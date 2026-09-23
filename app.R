library(httr)
library(xml2)
library(tidyverse)
library(glue)
library(forcats)
library(openxlsx)
library(gt)
library(DT)
library(plotly)
library(ggplot2)
library(sf)
library(hrbrthemes)
library(bs4Dash)
library(gtExtras)
library(googlesheets4)
library(googledrive)
library(bslib)
library(shiny)
library(leaflet)
library(rmapshaper)
library(jsonlite)

# ===========================================================================
# CACHING MODEL (read this before editing anything below)
# ---------------------------------------------------------------------------
# Every donor / donation / patient table is read from Google Sheets exactly
# ONCE per running R process (below), then kept in a per-session reactiveVal
# ("cache"). All lookups used while typing/searching (Load Donor, Find Donor,
# Load Journal Entry, the Patient ID search box, duplicate-email/phone
# checks, ID generation) read from these caches instead of calling
# read_sheet() again, so they're instant instead of round-tripping to
# Google.
#
# The cache is only written back to on two occasions:
#   1. This app successfully creates or edits a record itself -> the new/
#      edited row is patched into the relevant cache in memory (no re-read).
#   2. The user clicks one of the explicit "Refresh" buttons -> that does a
#      real read_sheet() call and replaces the cache, for when someone else
#      has changed the sheet from outside this app.
#
# Trade-off: if two people use this app AT THE SAME TIME, a session's cache
# can go briefly stale relative to edits made by the other session. Click
# "Refresh" before editing a record if you expect concurrent use, or before
# generating a new Donor ID / Journal ID after a burst of activity.
#
# Two latent bugs found while doing this refactor (see notes at their
# fix sites below):
#   - The donations-sheet header this app creates on first run named the
#     amount column "Amount", but the rest of the app already wrote/read a
#     column called "Donation amount". Depending on which name is actually
#     sitting in your live "Donations" tab's header row today, one or the
#     other was silently failing to save/load. The code below now writes
#     BOTH keys and reads whichever is present, so it's safe either way -
#     but it's worth opening the sheet and checking your header once.
#   - The journal "Reset Form" button only cleared the New Donation fields,
#     never the Find Donor box above it - fixed below (reset_journal_all).
# ===========================================================================

# ---------------------------------------------------------------------------
# AUTH
# ---------------------------------------------------------------------------
sa_path <- "service_account.json"

json <- Sys.getenv("GSHEETS_SERVICE_ACCOUNT_JSON")

if (nzchar(json)) {
  sa_path <- tempfile(fileext = ".json")
  writeLines(json, sa_path)
} else if (file.exists("service_account.json")) {
  sa_path <- "service_account.json"
} else {
  stop("No Google service-account credentials found.")
}
options(shiny.maxRequestSize = 30 * 1024^2)
gs4_auth(path = sa_path)
drive_auth(path = sa_path)

sheet_id         <- "1A1Ta-Zhz3FLk3cHXSAIaIr8SZAOKdk_kj0-2VLeH5MU"
drive_folder_id  <- "1k0N9K56Mh90q5DAI-BD2Q6lvc3UzzuyP"  # shared with the service account as Viewer
patient_sheet_id <- "1gAf-ZHo--M9baRjjQbKeW9B5jWXiHtkj8IXwU4gNxN4"
patient_sheet_gid <- 0

# ---------------------------------------------------------------------------
# PURE HELPERS (no input/output/session/reactives - safe at top level)
# ---------------------------------------------------------------------------
email_pattern <- "^[\\w.+-]+@[\\w-]+\\.[a-zA-Z]{2,}$"
phone_pattern <- "^\\d{10,11}$"
alpha_pattern <- "^[a-zA-Z ]+$"

is_blank <- function(x) is.null(x) || length(x) == 0 || !nzchar(x)

# Pulls a single value out of a one-row sheet tibble as a plain string,
# turning NULL/NA/missing columns into "" instead of erroring.
safe_val <- function(x) {
  if (is.null(x) || length(x) == 0) return("")
  x <- x[[1]]
  if (is.na(x)) "" else as.character(x)
}

# Like safe_val, but tries several candidate columns in order and returns
# the first non-blank one. Used where a column's name has been inconsistent
# across the sheet's history (see "Amount" vs "Donation amount" above).
safe_val_multi <- function(...) {
  for (v in list(...)) {
    s <- safe_val(v)
    if (nzchar(s)) return(s)
  }
  ""
}

col_letter <- function(n) {
  s <- ""
  while (n > 0) {
    rem <- (n - 1) %% 26
    s <- paste0(LETTERS[rem + 1], s)
    n <- (n - 1) %/% 26
  }
  s
}

sheet_row_range <- function(row_number, ncol) {
  paste0("A", row_number, ":", col_letter(ncol), row_number)
}

content_type_for <- function(fname) {
  ext <- tolower(tools::file_ext(fname))
  switch(ext,
         "png"  = "image/png",
         "jpg"  = "image/jpeg",
         "jpeg" = "image/jpeg",
         "application/octet-stream")
}

cleanup_tmp <- function(path) {
  if (!is.null(path) && file.exists(path)) unlink(path)
}

# Looks up an exact file name inside a Drive folder. Returns a one-row
# drive_resource (with $name, $id) if found, or NULL otherwise.
lookup_drive_image <- function(fname, folder_id) {
  fname <- trimws(fname)
  if (!nzchar(fname)) return(NULL)
  tryCatch({
    matches <- drive_ls(path = as_id(folder_id), pattern = fname)
    if (nrow(matches) == 0) return(NULL)
    exact <- matches[matches$name == fname, ]
    if (nrow(exact) == 0) return(NULL)
    exact[1, ]
  }, error = function(e) NULL)
}

download_preview <- function(file_row) {
  if (is.null(file_row)) return(NULL)
  ext <- tools::file_ext(file_row$name)
  tmp <- tempfile(fileext = if (nzchar(ext)) paste0(".", ext) else "")
  ok <- tryCatch({
    # verbose = FALSE just silences googledrive's own "File downloaded... /
    # Saved locally as..." console message. The temp file itself still has
    # to exist on disk - it's how imageOutput() shows the preview thumbnail
    # (Shiny can't render straight from a Drive file ID) - and it's already
    # deleted again by cleanup_tmp() as soon as the field changes, on
    # submit/reset, and on session end, so nothing lingers.
    drive_download(as_id(file_row$id), path = tmp, overwrite = TRUE, verbose = FALSE)
    TRUE
  }, error = function(e) FALSE)
  if (ok) tmp else NULL
}

# Lays a named list of field -> value out as a one-row tibble in exactly
# the column order given by `header`; any header column not present in
# `values` is written as "". Extra keys in `values` not present in header
# are simply ignored (this is what makes the dual Amount/Donation-amount
# keys below safe).
build_row_in_sheet_order <- function(values, header) {
  row <- lapply(header, function(col) {
    v <- values[[col]]
    if (is.null(v)) "" else as.character(v)
  })
  names(row) <- header
  tibble::as_tibble(row)
}

combine_remarks <- function(other_detail, remarks) {
  parts <- c(
    if (!is_blank(other_detail)) paste0("Detail: ", trimws(other_detail)) else NULL,
    if (!is_blank(remarks)) trimws(remarks) else NULL
  )
  paste(parts, collapse = " | ")
}

# Combines the matching column from two donor tables and returns the
# sorted, de-duplicated, non-blank values actually present today.
collect_choices <- function(personal_df, org_df, personal_col, org_col = personal_col) {
  vals <- character(0)
  if (!is.null(personal_df) && personal_col %in% names(personal_df)) vals <- c(vals, as.character(personal_df[[personal_col]]))
  if (!is.null(org_df) && org_col %in% names(org_df)) vals <- c(vals, as.character(org_df[[org_col]]))
  vals <- unique(trimws(vals))
  vals <- vals[!is.na(vals) & nzchar(vals)]
  sort(vals)
}

compute_choice_sets <- function(personal_df, org_df) {
  list(
    designation  = collect_choices(personal_df, org_df, "Designation", "Designation"),
    industry     = collect_choices(personal_df, org_df, "Industry Category", "Industry Category"),
    organisation = collect_choices(personal_df, org_df, "Organisation", "Organisation Name"),
    relationship = collect_choices(personal_df, org_df, "Pre-existing Relationship", "Pre-existing Relationship"),
    reference    = collect_choices(personal_df, org_df, "Reference", "Reference")
  )
}

get_sheet_name_by_gid <- function(ss, gid) {
  props <- tryCatch(googlesheets4::sheet_properties(ss), error = function(e) NULL)
  if (is.null(props)) return(NA_character_)
  nm <- props$name[props$id == gid]
  if (length(nm) == 0) NA_character_ else nm[1]
}

# Builds the choices list for the "Patient ID" selectize input: prefers the
# real "Patient ID" column, falls back to "Proposed Patient ID", and labels
# each option with the patient's name.
build_patient_choices <- function(df) {
  if (is.null(df) || nrow(df) == 0) return(character(0))
  id_col   <- if ("Patient ID" %in% names(df)) as.character(df$`Patient ID`) else rep(NA_character_, nrow(df))
  prop_col <- if ("Proposed Patient ID" %in% names(df)) as.character(df$`Proposed Patient ID`) else rep(NA_character_, nrow(df))
  name_col <- if ("Patient Name" %in% names(df)) as.character(df$`Patient Name`) else rep("", nrow(df))
  ids <- ifelse(!is.na(id_col) & nzchar(id_col), id_col, prop_col)
  keep <- !is.na(ids) & nzchar(ids)
  ids <- ids[keep]; names_ <- name_col[keep]
  labels <- ifelse(nzchar(names_), paste0(ids, " \u2014 ", names_), ids)
  stats::setNames(ids, labels)
}

# Finds a row by an ID column inside a cached data frame. Returns the row
# (as a one-row tibble) plus its 1-based position ($idx) within that data
# frame - which doubles as "row number minus 1" in the underlying sheet,
# since new rows are always appended at the bottom and edits are written
# back in place.
find_row_by_id <- function(df, id_col, id_val) {
  if (is.null(df) || nrow(df) == 0 || !(id_col %in% names(df))) return(NULL)
  idx <- which(df[[id_col]] == id_val)
  if (length(idx) == 0) return(NULL)
  list(row = df[idx[1], ], idx = idx[1])
}

donor_type_from_id <- function(donor_id) {
  prefix <- toupper(substr(donor_id, 1, 2))
  if (prefix == "PD") "personal" else if (prefix == "OD") "org" else NA_character_
}

# Generic {PREFIX}-{yymm}-{serial} ID generator against a cached data frame.
generate_id_from_df <- function(df, id_col, prefix) {
  if (is.null(df) || nrow(df) == 0 || !(id_col %in% names(df))) {
    serial <- 1
  } else {
    matching <- df[[id_col]][startsWith(df[[id_col]], prefix)]
    if (length(matching) == 0) {
      serial <- 1
    } else {
      nums <- suppressWarnings(as.integer(sub(prefix, "", matching, fixed = TRUE)))
      serial <- max(nums, na.rm = TRUE) + 1
    }
  }
  paste0(prefix, sprintf("%03d", serial))
}

# A DT table with CSV/Excel download buttons that export whatever the
# column filters (filter = "top") currently narrow the table down to,
# not the full underlying data - that's what `search = "applied"` below
# does (DataTables treats the per-column filter boxes as part of the same
# "search" the export buttons already know how to respect).
downloadable_datatable <- function(data, page_length = 10, filename_prefix = "export") {
  datatable(
    data, filter = "top", rownames = FALSE, extensions = "Buttons",
    options = list(
      pageLength = page_length, scrollX = TRUE, dom = "Blfrtip",
      buttons = list(
        list(extend = "csv", filename = filename_prefix,
             exportOptions = list(modifier = list(page = "all", search = "applied"))),
        list(extend = "excel", filename = filename_prefix,
             exportOptions = list(modifier = list(page = "all", search = "applied")))
      )
    )
  )
}

# Active / Expired / One-time status for a donations table.
donation_status <- function(data) {
  maturity <- if ("Maturity Date" %in% names(data)) suppressWarnings(as.Date(data$`Maturity Date`)) else rep(as.Date(NA), nrow(data))
  payment_type_col <- if ("Payment Type" %in% names(data)) data$`Payment Type` else rep("", nrow(data))
  ifelse(
    !is.na(maturity),
    ifelse(maturity >= Sys.Date(), "Active", "Expired — renewal required"),
    ifelse(payment_type_col == "One Time Payment", "One-time (complete)", "")
  )
}

validate_personal_donor <- function(name, email, phone, img_name_given, img_found) {
  errors <- c()
  if (is_blank(name) || !grepl(alpha_pattern, name, perl = TRUE)) errors <- c(errors, "Please enter a valid donor name.")
  has_email <- !is_blank(email); has_phone <- !is_blank(phone)
  if (!has_email && !has_phone) errors <- c(errors, "Please provide at least an email address or a phone number.")
  if (has_email && !grepl(email_pattern, email, perl = TRUE)) errors <- c(errors, "Please enter a valid email address.")
  if (has_phone && !grepl(phone_pattern, phone, perl = TRUE)) errors <- c(errors, "Please enter a valid phone number.")
  if (img_name_given && !img_found) errors <- c(errors, "Profile picture file name was not found in the Drive folder.")
  errors
}

validate_org_donor <- function(org_name, contact_name, phone, email, img_name_given, img_found) {
  errors <- c()
  if (is_blank(org_name)) errors <- c(errors, "Please enter the organisation name.")
  if (is_blank(contact_name) || !grepl(alpha_pattern, contact_name, perl = TRUE)) errors <- c(errors, "Please enter a valid contact name.")
  has_phone <- !is_blank(phone); has_email <- !is_blank(email)
  if (!has_phone && !has_email) errors <- c(errors, "Please provide at least an email address or a phone number.")
  if (has_phone && !grepl(phone_pattern, phone, perl = TRUE)) errors <- c(errors, "Please enter a valid phone number.")
  if (has_email && !grepl(email_pattern, email, perl = TRUE)) errors <- c(errors, "Please enter a valid email address.")
  if (img_name_given && !img_found) errors <- c(errors, "Organisation profile picture file name was not found in the Drive folder.")
  errors
}

# Validates a donation/journal entry and, if valid, returns the field
# values ready to be merged with Journal ID / Donor ID and written out.
# Shared by both the "New Donation" submit handler and the "Edit Journal"
# save handler, which previously duplicated ~150 lines of this each.
build_journal_entry <- function(beneficiary, amount, payment_type, start_date, maturity_date,
                                beds, patient_name, patient_phone, patient_id_input,
                                other_detail, remarks) {
  errors <- c()
  if (is_blank(beneficiary)) errors <- c(errors, "Please select a donation beneficiary.")
  if (is.null(amount) || is.na(amount) || amount <= 0) errors <- c(errors, "Please enter a valid donation amount.")
  if (is_blank(payment_type)) errors <- c(errors, "Please select a payment type.")
  
  is_fixed <- identical(payment_type, "Fixed Time Payment")
  if (is.null(start_date)) {
    errors <- c(errors, "Please provide a starting date.")
  } else if (is_fixed) {
    if (is.null(maturity_date)) {
      errors <- c(errors, "Please provide a maturing/closing date.")
    } else if (maturity_date <= start_date) {
      errors <- c(errors, "The maturing/closing date must be after the starting date.")
    }
  }
  
  patient_id_val <- ""; ext_name_val <- ""; ext_phone_val <- ""; bed_val <- ""
  
  if (identical(beneficiary, "Beds")) {
    if (is.null(beds) || length(beds) == 0) {
      errors <- c(errors, "Please select at least one bed.")
    } else {
      bed_val <- paste(beds, collapse = ", ")
    }
  } else if (identical(beneficiary, "External Patient")) {
    if (is_blank(patient_name) || !grepl(alpha_pattern, patient_name, perl = TRUE)) errors <- c(errors, "Please enter a valid patient name.")
    if (is_blank(patient_phone) || !grepl(phone_pattern, patient_phone, perl = TRUE)) errors <- c(errors, "Please enter a valid patient phone number.")
    ext_name_val <- patient_name; ext_phone_val <- patient_phone
  } else if (identical(beneficiary, "Patients")) {
    if (is_blank(patient_id_input)) {
      errors <- c(errors, "Please select the patient's ID.")
    } else {
      patient_id_val <- patient_id_input
    }
  }
  
  if (length(errors) > 0) return(list(errors = errors, values = NULL))
  
  maturity_val <- if (is_fixed && !is.null(maturity_date)) format(maturity_date, "%Y-%m-%d") else ""
  
  values <- list(
    `Donation Beneficiary`     = beneficiary,
    `Patient ID`               = patient_id_val,
    `External Patient Name`   = ext_name_val,
    `External Patient Number` = ext_phone_val,
    `Bed number`               = bed_val,
    # Written under both names - see the header-mismatch note near the top
    # of this file. build_row_in_sheet_order() only keeps whichever of
    # these actually matches a real column in your sheet.
    `Amount`                   = as.character(amount),
    `Donation amount`          = as.character(amount),
    `Payment Type`             = payment_type,
    `Starting Date`            = format(start_date, "%Y-%m-%d"),
    `Maturity Date`            = maturity_val,
    `Remarks`                  = combine_remarks(other_detail, remarks)
  )
  list(errors = character(0), values = values)
}

# ---------------------------------------------------------------------------
# DONATION / JOURNAL STATIC CHOICES
# ---------------------------------------------------------------------------
journal_sheet_name   <- "Donations"
beneficiary_choices  <- c("Beds", "Alok Katha", "Alok Boshoti", "Patients", "External Patient")
payment_type_choices <- c("One Time Payment", "Fixed Time Payment")
bed_choices          <- c(paste("Bed", 1:17), paste("Bed", 21:82))  # institution skips 18-20

# ---------------------------------------------------------------------------
# ENSURE THE DONATIONS SHEET EXISTS (must run BEFORE we read it into cache)
# ---------------------------------------------------------------------------
existing_sheet_names <- tryCatch(sheet_names(sheet_id), error = function(e) character(0))
if (!(journal_sheet_name %in% existing_sheet_names)) {
  journal_header_tbl <- tibble::tibble(
    `Journal ID` = character(), `Donor ID` = character(), `Donation Beneficiary` = character(),
    `Patient ID` = character(), `External Patient Name` = character(), `External Patient Number` = character(),
    `Bed number` = character(), `Donation amount` = character(), `Payment Type` = character(),
    `Starting Date` = character(), `Maturity Date` = character(), `Remarks` = character()
  )
  tryCatch(sheet_write(journal_header_tbl, ss = sheet_id, sheet = journal_sheet_name), error = function(e) NULL)
} else {
  existing_header <- tryCatch(names(read_sheet(sheet_id, sheet = journal_sheet_name, n_max = 0, col_types = "c")), error = function(e) NULL)
  if (!is.null(existing_header) && !("Payment Type" %in% existing_header)) {
    tryCatch(
      range_write(
        ss = sheet_id, data = tibble::tibble(`Payment Type` = "Payment Type"),
        sheet = journal_sheet_name, range = paste0(col_letter(length(existing_header) + 1), "1"),
        col_names = FALSE, reformat = FALSE
      ),
      error = function(e) NULL
    )
  }
}

# ---------------------------------------------------------------------------
# LOAD EVERYTHING ONCE (process start-up only - this is the whole point)
# ---------------------------------------------------------------------------
df_personal    <- read_sheet(sheet_id, 1, col_types = "c")
df_organisation <- read_sheet(sheet_id, 2, col_types = "c")
df_donations   <- tryCatch(read_sheet(sheet_id, sheet = journal_sheet_name, col_types = "c"), error = function(e) tibble::tibble())
journal_header <- names(df_donations)
if (length(journal_header) == 0) {
  journal_header <- c("Journal ID", "Donor ID", "Donation Beneficiary", "Patient ID",
                      "External Patient Name", "External Patient Number", "Bed number",
                      "Donation amount", "Payment Type", "Starting Date", "Maturity Date", "Remarks")
}

patient_sheet_name <- get_sheet_name_by_gid(patient_sheet_id, patient_sheet_gid)
df_patient <- if (!is.na(patient_sheet_name)) {
  tryCatch(read_sheet(patient_sheet_id, sheet = patient_sheet_name, col_types = "c"), error = function(e) tibble::tibble())
} else {
  tibble::tibble()
}
patient_choices <- build_patient_choices(df_patient)

initial_choice_sets <- compute_choice_sets(df_personal, df_organisation)
designation_choices  <- initial_choice_sets$designation
gender_choices       <- c("Male", "Female")
industry_choices     <- initial_choice_sets$industry
org_choices          <- initial_choice_sets$organisation
relationship_choices <- initial_choice_sets$relationship
reference_choices    <- initial_choice_sets$reference

# ===========================================================================
# UI
# ===========================================================================
ui <- fluidPage(
  tags$style(HTML("
  .bslib-sidebar-layout > .sidebar { position: sticky; top: 0; align-self: start; min-height: 90vh; overflow-y: auto; }
  .bslib-sidebar-resize-handle { display: none !important; }
  .bslib-sidebar-layout > .collapse-toggle { position: sticky; top: 10px; align-self: start; z-index: 999; }
  .leaflet-container { background: #ffffff !important; }
  .bslib-sidebar-layout > .sidebar .accordion-item { background-color: transparent !important; border-left: none !important; border-right: none !important; }
  .bslib-sidebar-layout > .sidebar .accordion-button { background-color: transparent !important; box-shadow: none !important; }
  .bslib-sidebar-layout > .sidebar .accordion-button:not(.collapsed) { background-color: transparent !important; box-shadow: none !important; }
  .bslib-sidebar-layout > .sidebar .accordion-body { background-color: transparent !important; }
  .bslib-sidebar-layout > .sidebar .accordion { --bs-accordion-bg: transparent; }
  .img-status-msg { font-size: 0.85rem; margin-top: 4px; }
  ")),
  
  page_navbar(
    title = "BANCAT",
    id    = "navbar",
    theme = bs_theme(
      preset    = "lumen",
      base_font = font_collection(font_google("Poppins", local = FALSE), "Roboto", "sans-serif")
    ),
    
    nav_panel(
      "Donor Registration",
      accordion(
        id = "registration", open = FALSE,
        accordion_panel(
          "Register a new donor", icon = icon("user-plus"),
          card(
            card_header("Registration Info"), height = "300px",
            layout_columns(
              col_widths = c(6, 6),
              dateInput(inputId = "donor_reg_date", label = h6("Donor Registration Date:"), value = Sys.Date()),
              selectInput("donor_type", h6("Select Donor Type"), list("Personal Donor" = "personal", "Organisation Donor" = "org"))
            ),
            layout_columns(
              col_widths = c(8, 4),
              div(h6("Donor ID:"), textOutput("donor_id_display")),
              div(class = "d-flex justify-content-end align-items-end",
                  actionButton("generate_donor_id_btn", "Generate Donor ID", icon = icon("id-badge"), class = "btn-outline-secondary btn-sm"))
            ),
            card_footer(
              div(class = "d-flex justify-content-end gap-2",
                  actionButton("submit_form", "Submit", icon = icon("paper-plane"), class = "btn-primary btn-sm"),
                  actionButton("reset_form", "Reset Form", icon = icon("rotate-left"), class = "btn-outline-secondary btn-sm"))
            )
          ),
          
          conditionalPanel(
            condition = "input.donor_type == 'personal'",
            card(
              card_header("Personal Donor Details"), height = "900px",
              layout_columns(
                col_widths = c(4, 4, 4),
                div(textInput("donor_name", h6("Donor name:")), textOutput("donor_name_msg")),
                selectizeInput("designation", h6("Designation"), choices = designation_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Enter Donor's Designation here", onInitialize = I('function(){this.setValue("");}'))),
                selectizeInput("gender", h6("Gender"), choices = gender_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "...", onInitialize = I('function(){this.setValue("");}'))),
                selectizeInput("industry_cat_per", h6("Industry Category"), choices = industry_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Enter Donor's Industry", onInitialize = I('function(){this.setValue("");}'))),
                selectizeInput("org_name", h6("Organisation"), choices = org_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Enter Donor's Organisation here", onInitialize = I('function(){this.setValue("");}'))),
                selectizeInput("pre-existing_per relationship", h6("Pre-existing Relationship"), choices = relationship_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "...", onInitialize = I('function(){this.setValue("");}'))),
                selectizeInput("reference_per", h6("Reference:"), choices = reference_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "...", onInitialize = I('function(){this.setValue("");}'))),
                div(textInput("email", h6("Email:")), textOutput("email_msg")),
                div(textInput("phone", h6("Mobile phone:")), textOutput("phone_msg")),
                div(
                  textInput("donor_img_name", h6("Profile picture file name (incl. extension):"), placeholder = "e.g. john_smith.jpg"),
                  helpText("Upload the photo into the shared Drive folder first, then type its exact file name here."),
                  div(class = "img-status-msg", textOutput("donor_img_status")),
                  imageOutput("donor_contents", height = "auto")
                )
              )
            )
          ),
          
          conditionalPanel(
            condition = "input.donor_type == 'org'",
            card(
              card_header("Organisation Donor Details"), height = "800px",
              layout_columns(
                col_widths = c(4, 4, 4),
                selectizeInput("org_donor_name", h6("Organisation Name"), choices = org_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Enter Organisation's name here", onInitialize = I('function(){this.setValue("");}'))),
                div(textInput("org_contact_name", h6("Contact Name: "))),
                div(textInput("org_contact_number", h6("Contact Number")), textOutput("org_phone_msg")),
                div(textInput("org_contact_email", h6("Email ID")), textOutput("org_email_msg")),
                selectizeInput("designation_org", h6("Designation"), choices = designation_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Enter Donor's Designation here", onInitialize = I('function(){this.setValue("");}'))),
                selectizeInput("industry_cat", h6("Industry Category"), choices = industry_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Enter Donor's Industry", onInitialize = I('function(){this.setValue("");}'))),
                selectizeInput("pre-existing_org relationship", h6("Pre-existing Relationship"), choices = relationship_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "", onInitialize = I('function(){this.setValue("");}'))),
                selectizeInput("reference_org", h6("Reference:"), choices = reference_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Enter Donor's Industry", onInitialize = I('function(){this.setValue("");}'))),
                div(
                  textInput("org_img_name", h6("Organisation profile picture file name (incl. extension):"), placeholder = "e.g. unilever_logo.png"),
                  helpText("Upload the photo into the shared Drive folder first, then type its exact file name here."),
                  div(class = "img-status-msg", textOutput("org_img_status")),
                  imageOutput("org_contents", height = "auto")
                )
              )
            )
          )
        ),
        
        accordion_panel(
          "View Donors", icon = icon("table"),
          card(
            card_header(div(class = "d-flex justify-content-between align-items-center",
                            input_switch("view_toggle", "Show Organisation Donors", value = FALSE),
                            actionButton("refresh_table_btn", "Refresh", icon = icon("rotate"), class = "btn-outline-secondary btn-sm"))),
            DTOutput("donor_table")
          )
        ),
        
        accordion_panel(
          "Edit Donor", icon = icon("user-pen"),
          card(
            card_header("Load Donor to Edit"),
            layout_columns(
              col_widths = c(8, 4),
              div(textInput("edit_donor_id", h6("Enter Donor ID:"), placeholder = "e.g. PD-2506-001 or OD-2506-001")),
              div(class = "d-flex justify-content-end align-items-end",
                  actionButton("load_donor_btn", "Load Donor", icon = icon("magnifying-glass"), class = "btn-outline-secondary btn-sm"))
            ),
            div(class = "img-status-msg", textOutput("edit_load_status"))
          ),
          
          conditionalPanel(
            condition = "output.edit_donor_loaded == 'personal'",
            card(
              card_header("Edit Personal Donor Details"), height = "900px",
              layout_columns(
                col_widths = c(4, 4, 4),
                dateInput(inputId = "edit_reg_date", label = h6("Registration Date:"), value = Sys.Date()),
                div(textInput("edit_donor_name", h6("Donor name:")), textOutput("edit_donor_name_msg")),
                selectizeInput("edit_designation", h6("Designation"), choices = designation_choices, selected = character(0), options = list(create = TRUE, placeholder = "Enter Donor's Designation here")),
                selectizeInput("edit_gender", h6("Gender"), choices = gender_choices, selected = character(0), options = list(create = TRUE, placeholder = "...")),
                selectizeInput("edit_industry_cat_per", h6("Industry Category"), choices = industry_choices, selected = character(0), options = list(create = TRUE, placeholder = "Enter Donor's Industry")),
                selectizeInput("edit_org_name", h6("Organisation"), choices = org_choices, selected = character(0), options = list(create = TRUE, placeholder = "Enter Donor's Organisation here")),
                selectizeInput("edit_pre_existing_per", h6("Pre-existing Relationship"), choices = relationship_choices, selected = character(0), options = list(create = TRUE, placeholder = "...")),
                selectizeInput("edit_reference_per", h6("Reference:"), choices = reference_choices, selected = character(0), options = list(create = TRUE, placeholder = "...")),
                div(textInput("edit_email", h6("Email:")), textOutput("edit_email_msg")),
                div(textInput("edit_phone", h6("Mobile phone:")), textOutput("edit_phone_msg")),
                div(
                  textInput("edit_donor_img_name", h6("Profile picture file name (incl. extension):"), placeholder = "e.g. john_smith.jpg"),
                  helpText("Leave as-is to keep the current photo, or type a different file name already uploaded to the shared Drive folder."),
                  div(class = "img-status-msg", textOutput("edit_donor_img_status")),
                  imageOutput("edit_donor_contents", height = "auto")
                )
              ),
              card_footer(div(class = "d-flex justify-content-end gap-2",
                              actionButton("save_personal_edit_btn", "Save Changes", icon = icon("floppy-disk"), class = "btn-primary btn-sm"),
                              actionButton("cancel_edit_btn", "Cancel", icon = icon("xmark"), class = "btn-outline-secondary btn-sm")))
            )
          ),
          
          conditionalPanel(
            condition = "output.edit_donor_loaded == 'org'",
            card(
              card_header("Edit Organisation Donor Details"), height = "800px",
              layout_columns(
                col_widths = c(4, 4, 4),
                dateInput(inputId = "edit_reg_date", label = h6("Registration Date:"), value = Sys.Date()),
                selectizeInput("edit_org_donor_name", h6("Organisation Name"), choices = org_choices, selected = character(0), options = list(create = TRUE, placeholder = "Enter Organisation's name here")),
                div(textInput("edit_org_contact_name", h6("Contact Name: "))),
                div(textInput("edit_org_contact_number", h6("Contact Number")), textOutput("edit_org_phone_msg")),
                div(textInput("edit_org_contact_email", h6("Email ID")), textOutput("edit_org_email_msg")),
                selectizeInput("edit_designation_org", h6("Designation"), choices = designation_choices, selected = character(0), options = list(create = TRUE, placeholder = "Enter Donor's Designation here")),
                selectizeInput("edit_industry_cat", h6("Industry Category"), choices = industry_choices, selected = character(0), options = list(create = TRUE, placeholder = "Enter Donor's Industry")),
                selectizeInput("edit_pre_existing_org", h6("Pre-existing Relationship"), choices = relationship_choices, selected = character(0), options = list(create = TRUE, placeholder = "")),
                selectizeInput("edit_reference_org", h6("Reference:"), choices = reference_choices, selected = character(0), options = list(create = TRUE, placeholder = "Enter Donor's Industry")),
                div(
                  textInput("edit_org_img_name", h6("Organisation profile picture file name (incl. extension):"), placeholder = "e.g. unilever_logo.png"),
                  helpText("Leave as-is to keep the current photo, or type a different file name already uploaded to the shared Drive folder."),
                  div(class = "img-status-msg", textOutput("edit_org_img_status")),
                  imageOutput("edit_org_contents", height = "auto")
                )
              ),
              card_footer(div(class = "d-flex justify-content-end gap-2",
                              actionButton("save_org_edit_btn", "Save Changes", icon = icon("floppy-disk"), class = "btn-primary btn-sm"),
                              actionButton("cancel_edit_btn2", "Cancel", icon = icon("xmark"), class = "btn-outline-secondary btn-sm")))
            )
          )
        )
      )
    ),
    
    nav_panel(
      "Journal",
      accordion(
        id = "journal_accordion", open = FALSE,
        accordion_panel(
          "Donation / Journal Entry", icon = icon("hand-holding-dollar"),
          card(
            card_header("Find Donor"),
            layout_columns(
              col_widths = c(8, 4),
              div(textInput("journal_donor_id", h6("Enter Donor ID:"), placeholder = "e.g. PD-2506-001 or OD-2506-001")),
              div(class = "d-flex justify-content-end align-items-end",
                  actionButton("journal_load_donor_btn", "Find Donor", icon = icon("magnifying-glass"), class = "btn-outline-secondary btn-sm"))
            ),
            div(class = "img-status-msg", textOutput("journal_donor_status"))
          ),
          
          conditionalPanel(
            condition = "output.journal_donor_loaded == 'yes'",
            card(
              card_header("New Donation"),
              layout_columns(
                col_widths = c(8, 4),
                div(h6("Journal ID:"), textOutput("journal_id_display")),
                div(class = "d-flex justify-content-end align-items-end",
                    actionButton("generate_journal_id_btn", "Generate Journal ID", icon = icon("id-badge"), class = "btn-outline-secondary btn-sm"))
              ),
              layout_columns(
                col_widths = c(4, 4, 4),
                selectizeInput("journal_beneficiary", h6("Donation Beneficiary"), choices = beneficiary_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Select or type a beneficiary", onInitialize = I('function(){this.setValue("");}'))),
                numericInput("journal_amount", h6("Donation Amount"), value = NA, min = 0),
                dateInput("journal_start_date", h6("Starting Date:"), value = Sys.Date())
              ),
              layout_columns(col_widths = c(4), radioButtons("journal_payment_type", h6("Payment Type"), choices = payment_type_choices, selected = "One Time Payment", inline = TRUE)),
              
              conditionalPanel(
                condition = "input.journal_beneficiary == 'Beds'",
                selectizeInput("journal_beds", h6("Select Bed(s) — a donation can cover more than one:"), choices = bed_choices, selected = character(0), multiple = TRUE,
                               options = list(create = TRUE, placeholder = "Select one or more beds"))
              ),
              conditionalPanel(
                condition = "input.journal_beneficiary == 'External Patient'",
                layout_columns(
                  col_widths = c(6, 6),
                  div(textInput("journal_patient_name", h6("Patient Name:")), textOutput("journal_patient_name_msg")),
                  div(textInput("journal_patient_phone", h6("Patient Phone Number:")), textOutput("journal_patient_phone_msg"))
                )
              ),
              conditionalPanel(
                condition = "input.journal_beneficiary=='Patients'",
                selectizeInput("journal_patient_id", h6("Patient ID:"), choices = NULL, selected = NULL,
                               options = list(placeholder = "Type a patient's name or ID to search…", maxOptions = 15)),
                div(class = "d-flex justify-content-between align-items-center",
                    div(class = "img-status-msg", textOutput("journal_patient_confirm")),
                    actionButton("refresh_patients_btn", "Refresh Patient List", icon = icon("rotate"), class = "btn-outline-secondary btn-sm"))
              ),
              conditionalPanel(
                condition = "input.journal_beneficiary == 'Alok Katha' || input.journal_beneficiary == 'Alok Boshoti' || input.journal_beneficiary == 'Patients'",
                textInput("journal_other_detail", h6("Additional Detail (optional):"), placeholder = "e.g. patient name / batch / notes")
              ),
              conditionalPanel(
                condition = "input.journal_payment_type == 'Fixed Time Payment'",
                layout_columns(col_widths = c(4), dateInput("journal_maturity_date", h6("Maturing / Closing Date:"), value = Sys.Date() %m+% months(1)))
              ),
              textAreaInput("journal_remarks", h6("Remarks (optional):"), rows = 2),
              card_footer(div(class = "d-flex justify-content-end gap-2",
                              actionButton("submit_journal_btn", "Submit Donation", icon = icon("paper-plane"), class = "btn-primary btn-sm"),
                              actionButton("reset_journal_btn", "Reset Form", icon = icon("rotate-left"), class = "btn-outline-secondary btn-sm")))
            ),
            
            card(
              card_header(div(class = "d-flex justify-content-between align-items-center",
                              span("Donation History for this Donor"),
                              actionButton("refresh_journal_btn", "Refresh", icon = icon("rotate"), class = "btn-outline-secondary btn-sm"))),
              DTOutput("journal_history_table")
            )
          )
        ),
        
        accordion_panel(
          "View Donations", icon = icon("table-list"),
          card(
            card_header(div(class = "d-flex justify-content-between align-items-center",
                            span("All Donations"),
                            actionButton("refresh_all_journal_btn", "Refresh", icon = icon("rotate"), class = "btn-outline-secondary btn-sm"))),
            DTOutput("all_journal_table")
          )
        ),
        
        accordion_panel(
          "Edit Journal", icon = icon("pen-to-square"),
          card(
            card_header("Load Journal Entry to Edit"),
            layout_columns(
              col_widths = c(8, 4),
              div(textInput("edit_journal_id", h6("Enter Journal ID:"), placeholder = "e.g. JN-2609-PD-2609-001-001")),
              div(class = "d-flex justify-content-end align-items-end",
                  actionButton("load_journal_btn", "Load Journal Entry", icon = icon("magnifying-glass"), class = "btn-outline-secondary btn-sm"))
            ),
            div(class = "img-status-msg", textOutput("edit_journal_load_status"))
          ),
          
          conditionalPanel(
            condition = "output.edit_journal_loaded == 'yes'",
            card(
              card_header("Edit Donation Details"), height = "700px",
              layout_columns(col_widths = c(6, 6),
                             div(h6("Donor ID:"), textOutput("edit_journal_donor_id_display")),
                             div(h6("Donor Name:"), textOutput("edit_journal_donor_name_display"))),
              layout_columns(
                col_widths = c(4, 4, 4),
                selectizeInput("edit_journal_beneficiary", h6("Donation Beneficiary"), choices = beneficiary_choices, selected = character(0),
                               options = list(create = TRUE, placeholder = "Select or type a beneficiary")),
                numericInput("edit_journal_amount", h6("Donation Amount"), value = NA, min = 0),
                dateInput("edit_journal_start_date", h6("Starting Date:"), value = Sys.Date())
              ),
              layout_columns(col_widths = c(4), radioButtons("edit_journal_payment_type", h6("Payment Type"), choices = payment_type_choices, selected = "One Time Payment", inline = TRUE)),
              
              conditionalPanel(
                condition = "input.edit_journal_beneficiary == 'Beds'",
                selectizeInput("edit_journal_beds", h6("Select Bed(s) — a donation can cover more than one:"), choices = bed_choices, selected = character(0), multiple = TRUE,
                               options = list(create = TRUE, placeholder = "Select one or more beds"))
              ),
              conditionalPanel(
                condition = "input.edit_journal_beneficiary == 'External Patient'",
                layout_columns(
                  col_widths = c(6, 6),
                  div(textInput("edit_journal_patient_name", h6("Patient Name:")), textOutput("edit_journal_patient_name_msg")),
                  div(textInput("edit_journal_patient_phone", h6("Patient Phone Number:")), textOutput("edit_journal_patient_phone_msg"))
                )
              ),
              conditionalPanel(
                condition = "input.edit_journal_beneficiary == 'Patients'",
                selectizeInput("edit_journal_patient_id", h6("Patient ID:"), choices = NULL, selected = NULL,
                               options = list(placeholder = "Type a patient's name or ID to search…", maxOptions = 15)),
                div(class = "d-flex justify-content-between align-items-center",
                    div(class = "img-status-msg", textOutput("edit_journal_patient_confirm")),
                    actionButton("edit_refresh_patients_btn", "Refresh Patient List", icon = icon("rotate"), class = "btn-outline-secondary btn-sm"))
              ),
              conditionalPanel(
                condition = "input.edit_journal_beneficiary == 'Alok Katha' || input.edit_journal_beneficiary == 'Alok Boshoti' || input.edit_journal_beneficiary == 'Patients'",
                textInput("edit_journal_other_detail", h6("Additional Detail (optional):"), placeholder = "e.g. patient name / batch / notes")
              ),
              conditionalPanel(
                condition = "input.edit_journal_payment_type == 'Fixed Time Payment'",
                layout_columns(col_widths = c(4), dateInput("edit_journal_maturity_date", h6("Maturing / Closing Date:"), value = Sys.Date() %m+% months(1)))
              ),
              textAreaInput("edit_journal_remarks", h6("Remarks (optional):"), rows = 2),
              card_footer(div(class = "d-flex justify-content-end gap-2",
                              actionButton("save_journal_edit_btn", "Save Changes", icon = icon("floppy-disk"), class = "btn-primary btn-sm"),
                              actionButton("cancel_journal_edit_btn", "Cancel", icon = icon("xmark"), class = "btn-outline-secondary btn-sm")))
            )
          )
        )
      )
    )
  )
)

# ===========================================================================
# SERVER
# ===========================================================================
server <- function(input, output, session) {
  
  # -- Caches (seeded once from the module-level reads above) --------------
  personal_data_rv <- reactiveVal(df_personal)
  org_data_rv       <- reactiveVal(df_organisation)
  journal_all_rv    <- reactiveVal(df_donations)
  patient_choices_rv <- reactiveVal(patient_choices)
  
  journal_with_status <- reactive({
    d <- journal_all_rv()
    if (nrow(d) > 0) d$Status <- donation_status(d)
    d
  })
  
  # -- Image preview state ---------------------------------------------------
  rv <- reactiveValues(
    donor_img_file = NULL, donor_img_tmp = NULL,
    org_img_file   = NULL, org_img_tmp   = NULL,
    edit_donor_img_file = NULL, edit_donor_img_tmp = NULL,
    edit_org_img_file   = NULL, edit_org_img_tmp   = NULL
  )
  
  edit_rv <- reactiveValues(donor_type = NULL, donor_id = NULL, idx = NULL)
  donor_id_rv <- reactiveVal(NULL)
  
  journal_rv <- reactiveValues(donor_id = NULL, donor_name = NULL)
  journal_id_rv <- reactiveVal(NULL)
  
  edit_journal_rv <- reactiveValues(journal_id = NULL, donor_id = NULL, donor_name = NULL, idx = NULL)
  
  # -- Session-scoped lookups against the caches (no network calls) --------
  find_donor_row <- function(donor_type, donor_id) {
    df <- if (donor_type == "personal") personal_data_rv() else org_data_rv()
    find_row_by_id(df, "Donor ID", donor_id)
  }
  
  generate_donor_id <- function(donor_type, reg_date) {
    yy <- format(reg_date, "%y"); mm <- format(reg_date, "%m")
    df <- if (donor_type == "personal") personal_data_rv() else org_data_rv()
    prefix <- paste0(if (donor_type == "personal") "PD" else "OD", "-", yy, mm, "-")
    generate_id_from_df(df, "Donor ID", prefix)
  }
  
  generate_journal_id <- function(reg_date, donor_id) {
    yy <- format(reg_date, "%y"); mm <- format(reg_date, "%m")
    generate_id_from_df(journal_all_rv(), "Journal ID", paste0("JN-", yy, mm, "-", donor_id, "-"))
  }
  
  check_duplicate <- function(email, phone, skip_donor_id = NULL) {
    errors <- c(); email_hit <- FALSE; phone_hit <- FALSE
    personal <- personal_data_rv(); org <- org_data_rv()
    if (!is.null(personal) && nrow(personal) > 0) {
      rows <- personal
      if (!is.null(skip_donor_id) && "Donor ID" %in% names(rows)) rows <- rows[rows$`Donor ID` != skip_donor_id, ]
      if (!is_blank(email) && "Email" %in% names(rows) && email %in% na.omit(rows$Email)) email_hit <- TRUE
      if (!is_blank(phone) && "Mobile Phone" %in% names(rows) && phone %in% na.omit(rows$`Mobile Phone`)) phone_hit <- TRUE
    }
    if (!is.null(org) && nrow(org) > 0) {
      rows <- org
      if (!is.null(skip_donor_id) && "Donor ID" %in% names(rows)) rows <- rows[rows$`Donor ID` != skip_donor_id, ]
      if (!is_blank(email) && "Email ID" %in% names(rows) && email %in% na.omit(rows$`Email ID`)) email_hit <- TRUE
      if (!is_blank(phone) && "Phone Number" %in% names(rows) && phone %in% na.omit(rows$`Phone Number`)) phone_hit <- TRUE
    }
    if (email_hit) errors <- c(errors, "This email address is already registered.")
    if (phone_hit) errors <- c(errors, "This phone number is already registered.")
    errors
  }
  
  # Pushes freshly computed choice sets (from the in-memory caches - no
  # network call) into every selectize input that offers them.
  choice_field_map <- list(
    designation  = c("designation", "designation_org", "edit_designation", "edit_designation_org"),
    industry     = c("industry_cat_per", "industry_cat", "edit_industry_cat_per", "edit_industry_cat"),
    organisation = c("org_name", "org_donor_name", "edit_org_name", "edit_org_donor_name"),
    relationship = c("pre-existing_per relationship", "pre-existing_org relationship", "edit_pre_existing_per", "edit_pre_existing_org"),
    reference    = c("reference_per", "reference_org", "edit_reference_per", "edit_reference_org")
  )
  sync_dynamic_choices <- function() {
    sets <- compute_choice_sets(personal_data_rv(), org_data_rv())
    for (key in names(choice_field_map)) {
      for (id in choice_field_map[[key]]) {
        updateSelectizeInput(session, id, choices = sets[[key]], selected = isolate(input[[id]]))
      }
    }
  }
  
  update_choice_field <- function(id, choices, value) {
    updateSelectizeInput(session, id, choices = union(choices, value), selected = value)
  }
  
  # -- Manual "Refresh" actions: the only places that re-hit the network ---
  resync_donor_caches <- function() {
    p <- tryCatch(read_sheet(sheet_id, sheet = 1, col_types = "c"), error = function(e) NULL)
    o <- tryCatch(read_sheet(sheet_id, sheet = 2, col_types = "c"), error = function(e) NULL)
    if (!is.null(p)) personal_data_rv(p)
    if (!is.null(o)) org_data_rv(o)
    if (is.null(p) || is.null(o)) showNotification("Could not refresh the donor table — showing the last loaded data.", type = "warning")
    sync_dynamic_choices()
  }
  
  resync_journal_cache <- function() {
    all_j <- tryCatch(read_sheet(sheet_id, sheet = journal_sheet_name, col_types = "c"), error = function(e) NULL)
    if (is.null(all_j)) { showNotification("Could not refresh the donations table.", type = "warning"); return() }
    journal_all_rv(all_j)
  }
  
  resync_patient_choices <- function() {
    if (is.na(patient_sheet_name)) {
      showNotification(paste0("Could not find the Patient sheet (looking for gid ", patient_sheet_gid, ")."), type = "warning")
      return()
    }
    new_df <- tryCatch(read_sheet(patient_sheet_id, sheet = patient_sheet_name, col_types = "c"), error = function(e) NULL)
    if (is.null(new_df)) { showNotification("Could not read the Patient sheet.", type = "warning"); return() }
    new_choices <- build_patient_choices(new_df)
    if (length(new_choices) == 0) showNotification("No patients found on the Patient sheet.", type = "warning")
    patient_choices_rv(new_choices)
    updateSelectizeInput(session, "journal_patient_id", choices = new_choices, selected = isolate(input$journal_patient_id), server = TRUE)
    updateSelectizeInput(session, "edit_journal_patient_id", choices = new_choices, selected = isolate(input$edit_journal_patient_id), server = TRUE)
  }
  
  observeEvent(input$refresh_table_btn, resync_donor_caches())
  observeEvent(input$refresh_journal_btn, resync_journal_cache())
  observeEvent(input$refresh_all_journal_btn, resync_journal_cache())
  observeEvent(input$refresh_patients_btn, resync_patient_choices())
  observeEvent(input$edit_refresh_patients_btn, resync_patient_choices())
  
  output$donor_table <- renderDT({
    data <- if (isTRUE(input$view_toggle)) org_data_rv() else personal_data_rv()
    req(data)
    downloadable_datatable(data, 10, if (isTRUE(input$view_toggle)) "organisation_donors" else "personal_donors")
  })
  
  output$journal_history_table <- renderDT({
    req(journal_rv$donor_id)
    data <- journal_with_status()
    data <- if ("Donor ID" %in% names(data)) data[data$`Donor ID` == journal_rv$donor_id, ] else data[0, ]
    downloadable_datatable(data, 5, paste0("donations_", journal_rv$donor_id))
  })
  
  output$all_journal_table <- renderDT({
    downloadable_datatable(journal_with_status(), 10, "all_donations")
  })
  
  # -- Validation message outputs (one factory instead of 14 copies) -------
  validator_msgs <- list(email = "Please enter a valid email address.", phone = "Please enter a valid phone number.", alpha = "Please enter a valid name.")
  validator_patterns <- list(email = email_pattern, phone = phone_pattern, alpha = alpha_pattern)
  register_validator <- function(output_id, input_id, kind) {
    output[[output_id]] <- renderText({
      val <- input[[input_id]]; req(val)
      if (!grepl(validator_patterns[[kind]], val, perl = TRUE)) validator_msgs[[kind]] else ""
    })
  }
  validator_specs <- list(
    c("email_msg", "email", "email"), c("phone_msg", "phone", "phone"), c("donor_name_msg", "donor_name", "alpha"),
    c("org_email_msg", "org_contact_email", "email"), c("org_phone_msg", "org_contact_number", "phone"),
    c("edit_email_msg", "edit_email", "email"), c("edit_phone_msg", "edit_phone", "phone"), c("edit_donor_name_msg", "edit_donor_name", "alpha"),
    c("edit_org_email_msg", "edit_org_contact_email", "email"), c("edit_org_phone_msg", "edit_org_contact_number", "phone"),
    c("journal_patient_name_msg", "journal_patient_name", "alpha"), c("journal_patient_phone_msg", "journal_patient_phone", "phone"),
    c("edit_journal_patient_name_msg", "edit_journal_patient_name", "alpha"), c("edit_journal_patient_phone_msg", "edit_journal_patient_phone", "phone")
  )
  for (spec in validator_specs) register_validator(spec[1], spec[2], spec[3])
  
  output$journal_patient_confirm <- renderText({
    pid <- input$journal_patient_id; if (is.null(pid) || !nzchar(pid)) return("")
    choices <- patient_choices_rv(); lbl <- names(choices)[match(pid, choices)]
    if (length(lbl) == 0 || is.na(lbl)) paste0("Selected patient ID: ", pid) else paste0("Confirmed patient: ", lbl)
  })
  output$edit_journal_patient_confirm <- renderText({
    pid <- input$edit_journal_patient_id; if (is.null(pid) || !nzchar(pid)) return("")
    choices <- patient_choices_rv(); lbl <- names(choices)[match(pid, choices)]
    if (length(lbl) == 0 || is.na(lbl)) paste0("Selected patient ID: ", pid) else paste0("Confirmed patient: ", lbl)
  })
  
  # -- Image lookup (one factory instead of 4 copies x 3 outputs each) -----
  image_fields <- list(
    donor      = list(input = "donor_img_name", file = "donor_img_file", tmp = "donor_img_tmp", status = "donor_img_status", img = "donor_contents"),
    org        = list(input = "org_img_name", file = "org_img_file", tmp = "org_img_tmp", status = "org_img_status", img = "org_contents"),
    edit_donor = list(input = "edit_donor_img_name", file = "edit_donor_img_file", tmp = "edit_donor_img_tmp", status = "edit_donor_img_status", img = "edit_donor_contents"),
    edit_org   = list(input = "edit_org_img_name", file = "edit_org_img_file", tmp = "edit_org_img_tmp", status = "edit_org_img_status", img = "edit_org_contents")
  )
  for (key in names(image_fields)) {
    local({
      spec <- image_fields[[key]]
      name_d <- debounce(reactive(input[[spec$input]]), 700)
      observeEvent(name_d(), {
        cleanup_tmp(rv[[spec$tmp]]); rv[[spec$tmp]] <- NULL; rv[[spec$file]] <- NULL
        fname <- name_d()
        if (is.null(fname) || !nzchar(trimws(fname))) return()
        match <- lookup_drive_image(fname, drive_folder_id)
        rv[[spec$file]] <- match
        if (!is.null(match)) rv[[spec$tmp]] <- download_preview(match)
      }, ignoreInit = TRUE)
      
      output[[spec$status]] <- renderText({
        fname <- input[[spec$input]]
        if (is.null(fname) || !nzchar(trimws(fname))) return("")
        if (is.null(rv[[spec$file]])) "Image not found in the folder — check the file name and try again." else "Image found."
      })
      
      output[[spec$img]] <- renderImage({
        req(rv[[spec$tmp]])
        list(src = rv[[spec$tmp]], contentType = content_type_for(rv[[spec$tmp]]), width = "100%")
      }, deleteFile = FALSE)
    })
  }
  
  # ---------------------------------------------------------------------
  # DONOR REGISTRATION
  # ---------------------------------------------------------------------
  reset_personal_donor_fields <- function() {
    updateTextInput(session, "donor_name", value = "")
    updateSelectizeInput(session, "designation", selected = character(0))
    updateSelectizeInput(session, "gender", selected = character(0))
    updateSelectizeInput(session, "org_name", selected = character(0))
    updateSelectizeInput(session, "industry_cat_per", selected = character(0))
    updateSelectizeInput(session, "pre-existing_per relationship", selected = character(0))
    updateSelectizeInput(session, "reference_per", selected = character(0))
    updateTextInput(session, "email", value = ""); updateTextInput(session, "phone", value = "")
    updateTextInput(session, "donor_img_name", value = "")
    cleanup_tmp(rv$donor_img_tmp); rv$donor_img_file <- NULL; rv$donor_img_tmp <- NULL
  }
  
  reset_org_donor_fields <- function() {
    updateSelectizeInput(session, "org_donor_name", selected = character(0))
    updateTextInput(session, "org_contact_name", value = ""); updateTextInput(session, "org_contact_number", value = "")
    updateSelectizeInput(session, "industry_cat", selected = character(0))
    updateSelectizeInput(session, "designation_org", selected = character(0))
    updateSelectizeInput(session, "pre-existing_org relationship", selected = character(0))
    updateSelectizeInput(session, "reference_org", selected = character(0))
    updateTextInput(session, "org_contact_email", value = ""); updateTextInput(session, "org_img_name", value = "")
    cleanup_tmp(rv$org_img_tmp); rv$org_img_file <- NULL; rv$org_img_tmp <- NULL
  }
  
  observeEvent(input$reset_form, {
    updateDateInput(session, "donor_reg_date", value = Sys.Date())
    updateSelectInput(session, "donor_type", selected = "personal")
    reset_personal_donor_fields(); reset_org_donor_fields()
    donor_id_rv(NULL)
  })
  
  observeEvent(input$generate_donor_id_btn, {
    req(input$donor_reg_date)
    donor_id_rv(generate_donor_id(input$donor_type, input$donor_reg_date))
  })
  output$donor_id_display <- renderText({ req(donor_id_rv()); donor_id_rv() })
  
  observeEvent(input$submit_form, {
    if (is.null(donor_id_rv())) { showNotification("Please click 'Generate Donor ID' first.", type = "error"); return() }
    donor_id <- donor_id_rv(); reg_date <- input$donor_reg_date
    
    if (input$donor_type == "personal") {
      errors <- validate_personal_donor(input$donor_name, input$email, input$phone, !is_blank(input$donor_img_name), !is.null(rv$donor_img_file))
      if (length(errors) == 0) errors <- check_duplicate(input$email, input$phone)
      if (length(errors) > 0) { showNotification(paste(errors, collapse = " "), type = "error"); return() }
      
      pic_name <- if (!is.null(rv$donor_img_file)) rv$donor_img_file$name else ""
      new_row <- tibble::tibble(
        `Donor ID` = donor_id, `Registration Date` = format(reg_date, "%Y-%m-%d"), `Donor Name` = input$donor_name,
        `Designation` = ifelse(is_blank(input$designation), "", input$designation),
        `Organisation` = ifelse(is_blank(input$org_name), "", input$org_name),
        `Pre-existing Relationship` = ifelse(is_blank(input$`pre-existing_per relationship`), "", input$`pre-existing_per relationship`),
        `Reference` = ifelse(is_blank(input$reference_per), "", input$reference_per),
        `Email` = ifelse(is_blank(input$email), "", input$email),
        `Mobile Phone` = ifelse(is_blank(input$phone), "", input$phone),
        `Profile Picture Name` = pic_name,
        `Industry Category` = ifelse(is_blank(input$industry_cat_per), "", input$industry_cat_per)
      )
      tryCatch({
        sheet_append(sheet_id, new_row, sheet = 1)
        personal_data_rv(dplyr::bind_rows(personal_data_rv(), new_row))
        sync_dynamic_choices()
        showNotification(paste("Personal donor submitted. Donor ID:", donor_id), type = "message")
        donor_id_rv(NULL); updateDateInput(session, "donor_reg_date", value = Sys.Date())
        reset_personal_donor_fields()
      }, error = function(e) showNotification(paste("Failed to write to sheet:", e$message), type = "error"))
      
    } else {
      errors <- validate_org_donor(input$org_donor_name, input$org_contact_name, input$org_contact_number, input$org_contact_email,
                                   !is_blank(input$org_img_name), !is.null(rv$org_img_file))
      if (length(errors) == 0) errors <- check_duplicate(input$org_contact_email, input$org_contact_number)
      if (length(errors) > 0) { showNotification(paste(errors, collapse = " "), type = "error"); return() }
      
      pic_name <- if (!is.null(rv$org_img_file)) rv$org_img_file$name else ""
      new_row <- tibble::tibble(
        `Donor ID` = donor_id, `Registration Date` = format(reg_date, "%Y-%m-%d"), `Organisation Name` = input$org_donor_name,
        `Contact Name` = input$org_contact_name,
        `Phone Number` = ifelse(is_blank(input$org_contact_number), "", input$org_contact_number),
        `Email ID` = ifelse(is_blank(input$org_contact_email), "", input$org_contact_email),
        `Designation` = ifelse(is_blank(input$designation_org), "", input$designation_org),
        `Industry Category` = ifelse(is_blank(input$industry_cat), "", input$industry_cat),
        `Pre-existing Relationship` = ifelse(is_blank(input$`pre-existing_org relationship`), "", input$`pre-existing_org relationship`),
        `Reference` = ifelse(is_blank(input$reference_org), "", input$reference_org),
        `Organisation profile pic` = pic_name
      )
      tryCatch({
        sheet_append(sheet_id, new_row, sheet = 2)
        org_data_rv(dplyr::bind_rows(org_data_rv(), new_row))
        sync_dynamic_choices()
        showNotification(paste("Organisation donor submitted. Donor ID:", donor_id), type = "message")
        donor_id_rv(NULL); updateDateInput(session, "donor_reg_date", value = Sys.Date())
        reset_org_donor_fields()
      }, error = function(e) showNotification(paste("Failed to write to sheet:", e$message), type = "error"))
    }
  })
  
  # ---------------------------------------------------------------------
  # EDIT DONOR
  # ---------------------------------------------------------------------
  output$edit_donor_loaded <- renderText({ req(edit_rv$donor_type); edit_rv$donor_type })
  outputOptions(output, "edit_donor_loaded", suspendWhenHidden = FALSE)
  
  output$edit_load_status <- renderText({
    if (is.null(edit_rv$donor_type)) return("")
    kind <- if (edit_rv$donor_type == "personal") "Personal Donor" else "Organisation Donor"
    paste0("Loaded ", edit_rv$donor_id, " (", kind, "). Edit any fields below and click Save Changes.")
  })
  
  clear_edit_form <- function() {
    edit_rv$donor_type <- NULL; edit_rv$donor_id <- NULL; edit_rv$idx <- NULL
    updateDateInput(session, "edit_reg_date", value = Sys.Date())
    updateTextInput(session, "edit_donor_name", value = "")
    updateSelectizeInput(session, "edit_designation", choices = designation_choices, selected = character(0))
    updateSelectizeInput(session, "edit_gender", choices = gender_choices, selected = character(0))
    updateSelectizeInput(session, "edit_industry_cat_per", choices = industry_choices, selected = character(0))
    updateSelectizeInput(session, "edit_org_name", choices = org_choices, selected = character(0))
    updateSelectizeInput(session, "edit_pre_existing_per", choices = relationship_choices, selected = character(0))
    updateSelectizeInput(session, "edit_reference_per", choices = reference_choices, selected = character(0))
    updateTextInput(session, "edit_email", value = ""); updateTextInput(session, "edit_phone", value = "")
    updateTextInput(session, "edit_donor_img_name", value = "")
    updateSelectizeInput(session, "edit_org_donor_name", choices = org_choices, selected = character(0))
    updateTextInput(session, "edit_org_contact_name", value = ""); updateTextInput(session, "edit_org_contact_number", value = "")
    updateTextInput(session, "edit_org_contact_email", value = "")
    updateSelectizeInput(session, "edit_designation_org", choices = designation_choices, selected = character(0))
    updateSelectizeInput(session, "edit_industry_cat", choices = industry_choices, selected = character(0))
    updateSelectizeInput(session, "edit_pre_existing_org", choices = relationship_choices, selected = character(0))
    updateSelectizeInput(session, "edit_reference_org", choices = reference_choices, selected = character(0))
    updateTextInput(session, "edit_org_img_name", value = "")
    cleanup_tmp(rv$edit_donor_img_tmp); cleanup_tmp(rv$edit_org_img_tmp)
    rv$edit_donor_img_file <- NULL; rv$edit_donor_img_tmp <- NULL; rv$edit_org_img_file <- NULL; rv$edit_org_img_tmp <- NULL
  }
  
  observeEvent(input$load_donor_btn, {
    donor_id <- trimws(input$edit_donor_id)
    if (!nzchar(donor_id)) { showNotification("Please enter a Donor ID.", type = "error"); return() }
    donor_type <- donor_type_from_id(donor_id)
    if (is.na(donor_type)) { showNotification("Donor ID should start with PD- (personal) or OD- (organisation).", type = "error"); return() }
    
    found <- find_donor_row(donor_type, donor_id)
    if (is.null(found)) {
      clear_edit_form(); updateTextInput(session, "edit_donor_id", value = donor_id)
      showNotification("Donor ID not found.", type = "error"); return()
    }
    
    r <- found$row; edit_rv$idx <- found$idx; edit_rv$donor_id <- donor_id; edit_rv$donor_type <- donor_type
    reg_date <- tryCatch(as.Date(safe_val(r$`Registration Date`)), error = function(e) NA)
    updateDateInput(session, "edit_reg_date", value = if (!is.na(reg_date)) reg_date else Sys.Date())
    
    if (donor_type == "personal") {
      updateTextInput(session, "edit_donor_name", value = safe_val(r$`Donor Name`))
      update_choice_field("edit_designation", designation_choices, safe_val(r$Designation))
      update_choice_field("edit_org_name", org_choices, safe_val(r$Organisation))
      update_choice_field("edit_industry_cat_per", industry_choices, safe_val(r$`Industry Category`))
      update_choice_field("edit_pre_existing_per", relationship_choices, safe_val(r$`Pre-existing Relationship`))
      update_choice_field("edit_reference_per", reference_choices, safe_val(r$Reference))
      updateTextInput(session, "edit_email", value = safe_val(r$Email))
      updateTextInput(session, "edit_phone", value = safe_val(r$`Mobile Phone`))
      updateTextInput(session, "edit_donor_img_name", value = safe_val(r$`Profile Picture Name`))
    } else {
      update_choice_field("edit_org_donor_name", org_choices, safe_val(r$`Organisation Name`))
      updateTextInput(session, "edit_org_contact_name", value = safe_val(r$`Contact Name`))
      updateTextInput(session, "edit_org_contact_number", value = safe_val(r$`Phone Number`))
      updateTextInput(session, "edit_org_contact_email", value = safe_val(r$`Email ID`))
      update_choice_field("edit_designation_org", designation_choices, safe_val(r$Designation))
      update_choice_field("edit_industry_cat", industry_choices, safe_val(r$`Industry Category`))
      update_choice_field("edit_pre_existing_org", relationship_choices, safe_val(r$`Pre-existing Relationship`))
      update_choice_field("edit_reference_org", reference_choices, safe_val(r$Reference))
      updateTextInput(session, "edit_org_img_name", value = safe_val(r$`Organisation profile pic`))
    }
    showNotification(paste("Loaded donor", donor_id, "for editing."), type = "message")
  })
  
  observeEvent(input$cancel_edit_btn, clear_edit_form())
  observeEvent(input$cancel_edit_btn2, clear_edit_form())
  
  observeEvent(input$save_personal_edit_btn, {
    req(edit_rv$donor_type == "personal", !is.null(edit_rv$idx), edit_rv$donor_id)
    donor_id <- edit_rv$donor_id
    errors <- validate_personal_donor(input$edit_donor_name, input$edit_email, input$edit_phone, !is_blank(input$edit_donor_img_name), !is.null(rv$edit_donor_img_file))
    if (length(errors) == 0) errors <- check_duplicate(input$edit_email, input$edit_phone, skip_donor_id = donor_id)
    if (length(errors) > 0) { showNotification(paste(errors, collapse = " "), type = "error"); return() }
    
    pic_name <- if (!is_blank(input$edit_donor_img_name) && !is.null(rv$edit_donor_img_file)) rv$edit_donor_img_file$name else ""
    new_row <- tibble::tibble(
      `Donor ID` = donor_id, `Registration Date` = format(input$edit_reg_date, "%Y-%m-%d"), `Donor Name` = input$edit_donor_name,
      `Designation` = ifelse(is_blank(input$edit_designation), "", input$edit_designation),
      `Organisation` = ifelse(is_blank(input$edit_org_name), "", input$edit_org_name),
      `Pre-existing Relationship` = ifelse(is_blank(input$edit_pre_existing_per), "", input$edit_pre_existing_per),
      `Reference` = ifelse(is_blank(input$edit_reference_per), "", input$edit_reference_per),
      `Email` = ifelse(is_blank(input$edit_email), "", input$edit_email),
      `Mobile Phone` = ifelse(is_blank(input$edit_phone), "", input$edit_phone),
      `Profile Picture Name` = pic_name,
      `Industry Category` = ifelse(is_blank(input$edit_industry_cat_per), "", input$edit_industry_cat_per)
    )
    tryCatch({
      range_write(ss = sheet_id, data = new_row, sheet = 1, range = sheet_row_range(edit_rv$idx + 1, ncol(new_row)), col_names = FALSE, reformat = FALSE)
      p <- personal_data_rv()
      for (col in names(new_row)) if (col %in% names(p)) p[[col]][edit_rv$idx] <- new_row[[col]][1]
      personal_data_rv(p); sync_dynamic_choices()
      showNotification(paste("Personal donor updated. Donor ID:", donor_id), type = "message")
      clear_edit_form(); updateTextInput(session, "edit_donor_id", value = "")
    }, error = function(e) showNotification(paste("Failed to update sheet:", e$message), type = "error"))
  })
  
  observeEvent(input$save_org_edit_btn, {
    req(edit_rv$donor_type == "org", !is.null(edit_rv$idx), edit_rv$donor_id)
    donor_id <- edit_rv$donor_id
    errors <- validate_org_donor(input$edit_org_donor_name, input$edit_org_contact_name, input$edit_org_contact_number, input$edit_org_contact_email,
                                 !is_blank(input$edit_org_img_name), !is.null(rv$edit_org_img_file))
    if (length(errors) == 0) errors <- check_duplicate(input$edit_org_contact_email, input$edit_org_contact_number, skip_donor_id = donor_id)
    if (length(errors) > 0) { showNotification(paste(errors, collapse = " "), type = "error"); return() }
    
    pic_name <- if (!is_blank(input$edit_org_img_name) && !is.null(rv$edit_org_img_file)) rv$edit_org_img_file$name else ""
    new_row <- tibble::tibble(
      `Donor ID` = donor_id, `Registration Date` = format(input$edit_reg_date, "%Y-%m-%d"), `Organisation Name` = input$edit_org_donor_name,
      `Contact Name` = input$edit_org_contact_name,
      `Phone Number` = ifelse(is_blank(input$edit_org_contact_number), "", input$edit_org_contact_number),
      `Email ID` = ifelse(is_blank(input$edit_org_contact_email), "", input$edit_org_contact_email),
      `Designation` = ifelse(is_blank(input$edit_designation_org), "", input$edit_designation_org),
      `Industry Category` = ifelse(is_blank(input$edit_industry_cat), "", input$edit_industry_cat),
      `Pre-existing Relationship` = ifelse(is_blank(input$edit_pre_existing_org), "", input$edit_pre_existing_org),
      `Reference` = ifelse(is_blank(input$edit_reference_org), "", input$edit_reference_org),
      `Organisation profile pic` = pic_name
    )
    tryCatch({
      range_write(ss = sheet_id, data = new_row, sheet = 2, range = sheet_row_range(edit_rv$idx + 1, ncol(new_row)), col_names = FALSE, reformat = FALSE)
      o <- org_data_rv()
      for (col in names(new_row)) if (col %in% names(o)) o[[col]][edit_rv$idx] <- new_row[[col]][1]
      org_data_rv(o); sync_dynamic_choices()
      showNotification(paste("Organisation donor updated. Donor ID:", donor_id), type = "message")
      clear_edit_form(); updateTextInput(session, "edit_donor_id", value = "")
    }, error = function(e) showNotification(paste("Failed to update sheet:", e$message), type = "error"))
  })
  
  # ---------------------------------------------------------------------
  # DONATION / JOURNAL ENTRY
  # ---------------------------------------------------------------------
  output$journal_donor_loaded <- renderText({ req(journal_rv$donor_id); "yes" })
  outputOptions(output, "journal_donor_loaded", suspendWhenHidden = FALSE)
  output$journal_donor_status <- renderText({
    if (is.null(journal_rv$donor_id)) return("")
    paste0("Donor: ", journal_rv$donor_name, " (", journal_rv$donor_id, ")")
  })
  
  reset_journal_entry_fields <- function() {
    updateSelectizeInput(session, "journal_beneficiary", choices = beneficiary_choices, selected = character(0))
    updateNumericInput(session, "journal_amount", value = NA)
    updateDateInput(session, "journal_start_date", value = Sys.Date())
    updateRadioButtons(session, "journal_payment_type", choices = payment_type_choices, selected = "One Time Payment")
    updateDateInput(session, "journal_maturity_date", value = Sys.Date() %m+% months(1))
    updateSelectizeInput(session, "journal_beds", choices = bed_choices, selected = character(0))
    updateSelectizeInput(session, "journal_patient_id", choices = patient_choices_rv(), selected = character(0), server = TRUE)
    updateTextInput(session, "journal_patient_name", value = ""); updateTextInput(session, "journal_patient_phone", value = "")
    updateTextInput(session, "journal_other_detail", value = ""); updateTextAreaInput(session, "journal_remarks", value = "")
    journal_id_rv(NULL)
  }
  
  # Fix: "Reset Form" previously left the "Find Donor" section (and the
  # per-donor history table) pointed at whatever donor was loaded, so the
  # New Donation panel never actually went back to its collapsed state.
  reset_journal_all <- function() {
    journal_rv$donor_id <- NULL; journal_rv$donor_name <- NULL
    updateTextInput(session, "journal_donor_id", value = "")
    reset_journal_entry_fields()
  }
  observeEvent(input$reset_journal_btn, reset_journal_all())
  
  observeEvent(input$journal_load_donor_btn, {
    donor_id <- trimws(input$journal_donor_id)
    if (!nzchar(donor_id)) { showNotification("Please enter a Donor ID.", type = "error"); return() }
    donor_type <- donor_type_from_id(donor_id)
    if (is.na(donor_type)) { showNotification("Donor ID should start with PD- (personal) or OD- (organisation).", type = "error"); return() }
    
    found <- find_donor_row(donor_type, donor_id)
    if (is.null(found)) {
      journal_rv$donor_id <- NULL; journal_rv$donor_name <- NULL
      showNotification("Donor ID not found.", type = "error"); return()
    }
    journal_rv$donor_id <- donor_id
    journal_rv$donor_name <- if (donor_type == "personal") safe_val(found$row$`Donor Name`) else safe_val(found$row$`Organisation Name`)
    reset_journal_entry_fields()
    showNotification(paste("Donor found:", journal_rv$donor_name), type = "message")
  })
  
  observeEvent(input$generate_journal_id_btn, {
    req(journal_rv$donor_id, input$journal_start_date)
    journal_id_rv(generate_journal_id(input$journal_start_date, journal_rv$donor_id))
  })
  output$journal_id_display <- renderText({ req(journal_id_rv()); journal_id_rv() })
  
  observeEvent(input$submit_journal_btn, {
    req(journal_rv$donor_id)
    if (is.null(journal_id_rv())) { showNotification("Please click 'Generate Journal ID' first.", type = "error"); return() }
    
    built <- build_journal_entry(
      beneficiary = input$journal_beneficiary, amount = input$journal_amount, payment_type = input$journal_payment_type,
      start_date = input$journal_start_date, maturity_date = input$journal_maturity_date, beds = input$journal_beds,
      patient_name = input$journal_patient_name, patient_phone = input$journal_patient_phone,
      patient_id_input = input$journal_patient_id, other_detail = input$journal_other_detail, remarks = input$journal_remarks
    )
    if (length(built$errors) > 0) { showNotification(paste(built$errors, collapse = " "), type = "error"); return() }
    
    values <- c(list(`Journal ID` = journal_id_rv(), `Donor ID` = journal_rv$donor_id), built$values)
    new_row <- build_row_in_sheet_order(values, journal_header)
    
    tryCatch({
      sheet_append(sheet_id, new_row, sheet = journal_sheet_name)
      journal_all_rv(dplyr::bind_rows(journal_all_rv(), new_row))
      showNotification(paste("Donation recorded. Journal ID:", journal_id_rv()), type = "message")
      reset_journal_entry_fields()
    }, error = function(e) showNotification(paste("Failed to write to sheet:", e$message), type = "error"))
  })
  
  # ---------------------------------------------------------------------
  # EDIT JOURNAL
  # ---------------------------------------------------------------------
  output$edit_journal_loaded <- renderText({ req(edit_journal_rv$journal_id); "yes" })
  outputOptions(output, "edit_journal_loaded", suspendWhenHidden = FALSE)
  output$edit_journal_load_status <- renderText({
    if (is.null(edit_journal_rv$journal_id)) return("")
    paste0("Loaded ", edit_journal_rv$journal_id, " (", edit_journal_rv$donor_name, ", ", edit_journal_rv$donor_id, "). Edit any fields below and click Save Changes.")
  })
  output$edit_journal_donor_id_display <- renderText({ req(edit_journal_rv$donor_id); edit_journal_rv$donor_id })
  output$edit_journal_donor_name_display <- renderText({ req(edit_journal_rv$donor_name); edit_journal_rv$donor_name })
  
  clear_journal_edit_form <- function() {
    edit_journal_rv$journal_id <- NULL; edit_journal_rv$donor_id <- NULL; edit_journal_rv$donor_name <- NULL; edit_journal_rv$idx <- NULL
    updateSelectizeInput(session, "edit_journal_beneficiary", choices = beneficiary_choices, selected = character(0))
    updateNumericInput(session, "edit_journal_amount", value = NA)
    updateDateInput(session, "edit_journal_start_date", value = Sys.Date())
    updateRadioButtons(session, "edit_journal_payment_type", choices = payment_type_choices, selected = "One Time Payment")
    updateDateInput(session, "edit_journal_maturity_date", value = Sys.Date() %m+% months(1))
    updateSelectizeInput(session, "edit_journal_beds", choices = bed_choices, selected = character(0))
    updateSelectizeInput(session, "edit_journal_patient_id", choices = patient_choices_rv(), selected = character(0), server = TRUE)
    updateTextInput(session, "edit_journal_patient_name", value = ""); updateTextInput(session, "edit_journal_patient_phone", value = "")
    updateTextInput(session, "edit_journal_other_detail", value = ""); updateTextAreaInput(session, "edit_journal_remarks", value = "")
  }
  
  observeEvent(input$load_journal_btn, {
    journal_id <- trimws(input$edit_journal_id)
    if (!nzchar(journal_id)) { showNotification("Please enter a Journal ID.", type = "error"); return() }
    
    found <- find_row_by_id(journal_all_rv(), "Journal ID", journal_id)
    if (is.null(found)) {
      clear_journal_edit_form(); updateTextInput(session, "edit_journal_id", value = journal_id)
      showNotification("Journal ID not found.", type = "error"); return()
    }
    
    r <- found$row
    edit_journal_rv$idx <- found$idx
    edit_journal_rv$journal_id <- journal_id
    edit_journal_rv$donor_id <- safe_val(r$`Donor ID`)
    
    donor_type <- donor_type_from_id(edit_journal_rv$donor_id)
    donor_found <- if (!is.na(donor_type)) find_donor_row(donor_type, edit_journal_rv$donor_id) else NULL
    edit_journal_rv$donor_name <- if (!is.null(donor_found)) {
      if (donor_type == "personal") safe_val(donor_found$row$`Donor Name`) else safe_val(donor_found$row$`Organisation Name`)
    } else ""
    
    beneficiary <- safe_val(r$`Donation Beneficiary`)
    update_choice_field("edit_journal_beneficiary", beneficiary_choices, beneficiary)
    # Read the amount under either historical column name - see the note
    # near the top of this file about the Amount / Donation amount mismatch.
    updateNumericInput(session, "edit_journal_amount", value = suppressWarnings(as.numeric(safe_val_multi(r$`Donation amount`, r$Amount))))
    
    start_date <- tryCatch(as.Date(safe_val(r$`Starting Date`)), error = function(e) NA)
    updateDateInput(session, "edit_journal_start_date", value = if (!is.na(start_date)) start_date else Sys.Date())
    
    maturity_str <- safe_val(r$`Maturity Date`)
    maturity_date <- tryCatch(as.Date(maturity_str), error = function(e) NA)
    updateDateInput(session, "edit_journal_maturity_date", value = if (!is.na(maturity_date)) maturity_date else Sys.Date() %m+% months(1))
    
    payment_type_val <- safe_val(r$`Payment Type`)
    if (!nzchar(payment_type_val)) payment_type_val <- if (nzchar(maturity_str)) "Fixed Time Payment" else "One Time Payment"
    updateRadioButtons(session, "edit_journal_payment_type", choices = payment_type_choices, selected = payment_type_val)
    
    updateTextAreaInput(session, "edit_journal_remarks", value = safe_val(r$Remarks))
    
    updateSelectizeInput(session, "edit_journal_beds", choices = bed_choices, selected = character(0))
    updateSelectizeInput(session, "edit_journal_patient_id", choices = patient_choices_rv(), selected = character(0), server = TRUE)
    updateTextInput(session, "edit_journal_patient_name", value = ""); updateTextInput(session, "edit_journal_patient_phone", value = "")
    updateTextInput(session, "edit_journal_other_detail", value = "")
    
    if (identical(beneficiary, "Beds")) {
      beds <- trimws(strsplit(safe_val(r$`Bed number`), ",")[[1]]); beds <- beds[nzchar(beds)]
      updateSelectizeInput(session, "edit_journal_beds", choices = union(bed_choices, beds), selected = beds)
    } else if (identical(beneficiary, "External Patient")) {
      updateTextInput(session, "edit_journal_patient_name", value = safe_val(r$`External Patient Name`))
      updateTextInput(session, "edit_journal_patient_phone", value = safe_val(r$`External Patient Number`))
    } else if (identical(beneficiary, "Patients")) {
      pid <- safe_val(r$`Patient ID`)
      choices_here <- patient_choices_rv()
      if (nzchar(pid) && !(pid %in% choices_here)) choices_here <- c(stats::setNames(pid, pid), choices_here)
      updateSelectizeInput(session, "edit_journal_patient_id", choices = choices_here, selected = pid, server = TRUE)
    }
    showNotification(paste("Loaded journal entry", journal_id, "for editing."), type = "message")
  })
  
  observeEvent(input$cancel_journal_edit_btn, clear_journal_edit_form())
  
  observeEvent(input$save_journal_edit_btn, {
    req(edit_journal_rv$journal_id, !is.null(edit_journal_rv$idx), edit_journal_rv$donor_id)
    
    built <- build_journal_entry(
      beneficiary = input$edit_journal_beneficiary, amount = input$edit_journal_amount, payment_type = input$edit_journal_payment_type,
      start_date = input$edit_journal_start_date, maturity_date = input$edit_journal_maturity_date, beds = input$edit_journal_beds,
      patient_name = input$edit_journal_patient_name, patient_phone = input$edit_journal_patient_phone,
      patient_id_input = input$edit_journal_patient_id, other_detail = input$edit_journal_other_detail, remarks = input$edit_journal_remarks
    )
    if (length(built$errors) > 0) { showNotification(paste(built$errors, collapse = " "), type = "error"); return() }
    
    journal_id <- edit_journal_rv$journal_id
    values <- c(list(`Journal ID` = journal_id, `Donor ID` = edit_journal_rv$donor_id), built$values)
    new_row <- build_row_in_sheet_order(values, journal_header)
    
    tryCatch({
      range_write(ss = sheet_id, data = new_row, sheet = journal_sheet_name, range = sheet_row_range(edit_journal_rv$idx + 1, ncol(new_row)), col_names = FALSE, reformat = FALSE)
      d <- journal_all_rv()
      for (col in names(new_row)) if (col %in% names(d)) d[[col]][edit_journal_rv$idx] <- new_row[[col]][1]
      journal_all_rv(d)
      showNotification(paste("Donation updated. Journal ID:", journal_id), type = "message")
      clear_journal_edit_form(); updateTextInput(session, "edit_journal_id", value = "")
    }, error = function(e) showNotification(paste("Failed to update sheet:", e$message), type = "error"))
  })
  
  # -- Clean up any leftover temp preview files if the session ends -------
  session$onSessionEnded(function() {
    cleanup_tmp(isolate(rv$donor_img_tmp)); cleanup_tmp(isolate(rv$org_img_tmp))
    cleanup_tmp(isolate(rv$edit_donor_img_tmp)); cleanup_tmp(isolate(rv$edit_org_img_tmp))
  })
}

shinyApp(ui = ui, server = server)