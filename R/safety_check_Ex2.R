# Safety Check Functions for Example 2: SEIR change-point attack rate
# This file contains all safety validation functions used in the vignette

#' Validate numeric parameters for safety
#' @param x Numeric value to check
#' @param name Parameter name for error messages
#' @param min_val Minimum allowed value (default: -Inf)
#' @param max_val Maximum allowed value (default: Inf)
#' @param allow_null Whether NULL values are allowed
#' @return TRUE if valid, FALSE otherwise
validate_numeric_param <- function(x, name, min_val = -Inf, max_val = Inf, allow_null = FALSE) {
  if (allow_null && is.null(x)) return(TRUE)
  if (is.null(x)) {
    warning(paste(name, "is NULL"))
    return(FALSE)
  }
  if (!is.numeric(x)) {
    warning(paste(name, "is not numeric"))
    return(FALSE)
  }
  if (length(x) != 1) {
    warning(paste(name, "has length", length(x), "but should be 1"))
    return(FALSE)
  }
  if (!is.finite(x)) {
    warning(paste(name, "is not finite"))
    return(FALSE)
  }
  if (x < min_val || x > max_val) {
    warning(paste(name, "=", x, "is outside bounds [", min_val, ",", max_val, "]"))
    return(FALSE)
  }
  TRUE
}

#' Validate vector parameters for safety
#' @param x Vector to check
#' @param name Parameter name for error messages
#' @param min_length Minimum allowed length
#' @param max_length Maximum allowed length
#' @param min_val Minimum allowed value for elements
#' @param max_val Maximum allowed value for elements
#' @param allow_null Whether NULL values are allowed
#' @return TRUE if valid, FALSE otherwise
validate_vector_param <- function(x, name, min_length = 1, max_length = Inf, 
                                min_val = -Inf, max_val = Inf, allow_null = FALSE) {
  if (allow_null && is.null(x)) return(TRUE)
  if (is.null(x)) {
    warning(paste(name, "is NULL"))
    return(FALSE)
  }
  if (!is.vector(x)) {
    warning(paste(name, "is not a vector"))
    return(FALSE)
  }
  if (length(x) < min_length || length(x) > max_length) {
    warning(paste(name, "has length", length(x), "but should be in [", min_length, ",", max_length, "]"))
    return(FALSE)
  }
  if (any(!is.finite(x))) {
    warning(paste(name, "contains non-finite values"))
    return(FALSE)
  }
  if (any(x < min_val) || any(x > max_val)) {
    warning(paste(name, "contains values outside bounds [", min_val, ",", max_val, "]"))
    return(FALSE)
  }
  TRUE
}

#' Validate matrix parameters for safety
#' @param x Matrix to check
#' @param name Parameter name for error messages
#' @param min_rows Minimum allowed number of rows
#' @param max_rows Maximum allowed number of rows
#' @param min_cols Minimum allowed number of columns
#' @param max_cols Maximum allowed number of columns
#' @param allow_null Whether NULL values are allowed
#' @return TRUE if valid, FALSE otherwise
validate_matrix_param <- function(x, name, min_rows = 1, max_rows = Inf,
                                min_cols = 1, max_cols = Inf, allow_null = FALSE) {
  if (allow_null && is.null(x)) return(TRUE)
  if (is.null(x)) {
    warning(paste(name, "is NULL"))
    return(FALSE)
  }
  if (!is.matrix(x)) {
    warning(paste(name, "is not a matrix"))
    return(FALSE)
  }
  if (nrow(x) < min_rows || nrow(x) > max_rows) {
    warning(paste(name, "has", nrow(x), "rows but should have [", min_rows, ",", max_rows, "]"))
    return(FALSE)
  }
  if (ncol(x) < min_cols || ncol(x) > max_cols) {
    warning(paste(name, "has", ncol(x), "columns but should have [", min_cols, ",", max_cols, "]"))
    return(FALSE)
  }
  if (any(!is.finite(x))) {
    warning(paste(name, "contains non-finite values"))
    return(FALSE)
  }
  TRUE
}

#' Validate datalist structure for safety
#' @param datalist Data list to check
#' @param required_names Required names in the datalist
#' @return TRUE if valid, FALSE otherwise
validate_datalist <- function(datalist, required_names = c("y", "T", "N", "gamma", "S0", "E0", "I0", "R0", "rho")) {
  if (is.null(datalist)) {
    warning("datalist is NULL")
    return(FALSE)
  }
  if (!is.list(datalist)) {
    warning("datalist is not a list")
    return(FALSE)
  }
  
  missing_names <- setdiff(required_names, names(datalist))
  if (length(missing_names) > 0) {
    warning("datalist missing required names:", paste(missing_names, collapse = ", "))
    return(FALSE)
  }
  
  TRUE
}

#' Validate SEIR model parameters for safety
#' @param T Time horizon
#' @param N Population size
#' @param beta_t Transmission rate vector
#' @param gamma Recovery rate
#' @param S0 Initial susceptible population
#' @param E0 Initial exposed population
#' @param I0 Initial infectious population
#' @param R0 Initial recovered population
#' @param rho Reporting rate
#' @return TRUE if valid, FALSE otherwise
validate_seir_params <- function(T, N, beta_t, gamma, S0, E0, I0, R0, rho = 1.0) {
  # Check individual parameters
  if (!validate_numeric_param(T, "T", min_val = 1)) return(FALSE)
  if (!validate_numeric_param(N, "N", min_val = 1)) return(FALSE)
  if (!validate_numeric_param(gamma, "gamma", min_val = 0.001, max_val = 1)) return(FALSE)
  if (!validate_numeric_param(S0, "S0", min_val = 0)) return(FALSE)
  if (!validate_numeric_param(E0, "E0", min_val = 0)) return(FALSE)
  if (!validate_numeric_param(I0, "I0", min_val = 0)) return(FALSE)
  if (!validate_numeric_param(R0, "R0", min_val = 0)) return(FALSE)
  if (!validate_numeric_param(rho, "rho", min_val = 0.001, max_val = 10)) return(FALSE)
  
  # Check beta_t vector
  if (!validate_vector_param(beta_t, "beta_t", min_length = T, max_length = T, min_val = 0.001, max_val = 10)) return(FALSE)
  
  # Check population consistency
  total_pop <- S0 + E0 + I0 + R0
  if (abs(total_pop - N) > 1e-6) {
    warning("Initial population sum (", total_pop, ") does not match N (", N, ")")
    return(FALSE)
  }
  
  TRUE
}

#' Validate jump matrix structure for safety
#' @param jump Jump matrix to check
#' @param T Time horizon
#' @param min_segments Minimum allowed segments
#' @param max_segments Maximum allowed segments
#' @return TRUE if valid, FALSE otherwise
validate_jump_matrix <- function(jump, T, min_segments = 1, max_segments = 20) {
  if (!validate_matrix_param(jump, "jump", min_rows = 2, max_rows = 2, 
                           min_cols = min_segments, max_cols = max_segments)) {
    return(FALSE)
  }
  
  # Extract beta and change-points
  beta_vec <- as.numeric(jump[1, ])
  cp_vec <- as.integer(round(jump[2, ]))
  
  # Check beta values
  if (!validate_vector_param(beta_vec, "beta values", min_val = 0.001, max_val = 20)) return(FALSE)
  
  # Check change-points
  if (!validate_vector_param(cp_vec, "change-points", min_val = 1, max_val = T)) return(FALSE)
  
  # Check ordering
  if (is.unsorted(cp_vec, strictly = TRUE)) {
    warning("Change-points are not strictly increasing")
    return(FALSE)
  }
  
  # Check last change-point equals T
  if (cp_vec[length(cp_vec)] != T) {
    warning("Last change-point (", cp_vec[length(cp_vec)], ") does not equal T (", T, ")")
    return(FALSE)
  }
  
  TRUE
}

#' Validate RJMCMC parameters for safety
#' @param params Parameter vector to check
#' @param expected_length Expected length of parameter vector
#' @param name Parameter name for error messages
#' @return TRUE if valid, FALSE otherwise
validate_rjmc_params <- function(params, expected_length = 1, name = "params") {
  if (is.null(params)) {
    warning(paste(name, "is NULL"))
    return(FALSE)
  }
  if (!is.vector(params)) {
    warning(paste(name, "is not a vector"))
    return(FALSE)
  }
  if (length(params) != expected_length) {
    warning(paste(name, "has length", length(params), "but should be", expected_length))
    return(FALSE)
  }
  if (any(!is.finite(params))) {
    warning(paste(name, "contains non-finite values"))
    return(FALSE)
  }
  TRUE
}

#' Safe default values for various parameters
#' @return List of safe default values
get_safe_defaults <- function() {
  list(
    beta_default = 0.1,
    T_default = 100,
    N_default = 10000,
    gamma_default = 1/6,
    S0_default = 9990,
    E0_default = 0,
    I0_default = 10,
    R0_default = 0,
    rho_default = 1.0
  )
}

#' Create safe default beta vector
#' @param T Time horizon
#' @return Safe default beta vector
create_safe_beta <- function(T) {
  defaults <- get_safe_defaults()
  rep(defaults$beta_default, max(1, T))
}

#' Create safe default SEIR result
#' @param T Time horizon
#' @return Safe default SEIR result list
create_safe_seir_result <- function(T) {
  list(
    S = rep(0, T),
    E = rep(0, T),
    I = rep(0, T),
    R = rep(0, T),
    incidence = rep(0, T)
  )
}

#' Create safe default jump matrix
#' @param T Time horizon
#' @return Safe default jump matrix
create_safe_jump <- function(T) {
  defaults <- get_safe_defaults()
  matrix(c(defaults$beta_default, T), nrow = 2, byrow = TRUE)
}

#' Comprehensive safety check for make_beta_t function
#' @param beta_vec Beta values vector
#' @param cp_vec Change-points vector
#' @param T Time horizon
#' @return TRUE if inputs are safe, FALSE otherwise
validate_make_beta_t_inputs <- function(beta_vec, cp_vec, T) {
  if (!validate_numeric_param(T, "T", min_val = 1)) return(FALSE)
  if (!validate_vector_param(beta_vec, "beta_vec", min_val = 0.001, max_val = 20)) return(FALSE)
  if (!validate_vector_param(cp_vec, "cp_vec", min_val = 1, max_val = T)) return(FALSE)
  
  # Check that we have the right number of change-points
  if (length(cp_vec) != length(beta_vec)) {
    warning("Length of beta_vec (", length(beta_vec), ") does not match length of cp_vec (", length(cp_vec), ")")
    return(FALSE)
  }
  
  TRUE
}

#' Comprehensive safety check for SEIR function inputs
#' @param T Time horizon
#' @param N Population size
#' @param beta_t Transmission rate vector
#' @param gamma Recovery rate
#' @param S0 Initial susceptible population
#' @param E0 Initial exposed population
#' @param I0 Initial infectious population
#' @param R0 Initial recovered population
#' @param rho Reporting rate
#' @return TRUE if inputs are safe, FALSE otherwise
validate_seir_inputs <- function(T, N, beta_t, gamma, S0, E0, I0, R0, rho = 1.0) {
  if (!validate_numeric_param(T, "T", min_val = 1)) return(FALSE)
  if (!validate_numeric_param(N, "N", min_val = 1)) return(FALSE)
  if (!validate_vector_param(beta_t, "beta_t", min_length = T, max_length = T, min_val = 0.001, max_val = 10)) return(FALSE)
  if (!validate_numeric_param(gamma, "gamma", min_val = 0.001, max_val = 1)) return(FALSE)
  if (!validate_numeric_param(S0, "S0", min_val = 0)) return(FALSE)
  if (!validate_numeric_param(E0, "E0", min_val = 0)) return(FALSE)
  if (!validate_numeric_param(I0, "I0", min_val = 0)) return(FALSE)
  if (!validate_numeric_param(R0, "R0", min_val = 0)) return(FALSE)
  if (!validate_numeric_param(rho, "rho", min_val = 0.001, max_val = 10)) return(FALSE)
  
  # Check population consistency
  total_pop <- S0 + E0 + I0 + R0
  if (abs(total_pop - N) > 1e-6) {
    warning("Initial population sum (", total_pop, ") does not match N (", N, ")")
    return(FALSE)
  }
  
  TRUE
}

#' Safe log calculation with bounds
#' @param x Numeric value
#' @param min_val Minimum allowed value
#' @return Safe log value
safe_log <- function(x, min_val = 1e-10) {
  if (is.null(x) || !is.finite(x)) return(log(min_val))
  if (x <= 0) return(log(min_val))
  log(max(x, min_val))
}

#' Safe sum calculation with bounds
#' @param x Numeric vector
#' @param min_val Minimum allowed value
#' @param max_val Maximum allowed value
#' @return Safe sum value
safe_sum <- function(x, min_val = -1e6, max_val = 1e6) {
  if (is.null(x) || !is.vector(x)) return(0)
  if (all(!is.finite(x))) return(0)
  result <- sum(x, na.rm = TRUE)
  if (!is.finite(result)) return(0)
  max(min_val, min(result, max_val))
}

#' Safe product calculation with bounds
#' @param x Numeric vector
#' @param min_val Minimum allowed value
#' @param max_val Maximum allowed value
#' @return Safe product value
safe_prod <- function(x, min_val = 1e-10, max_val = 1e10) {
  if (is.null(x) || !is.vector(x)) return(1)
  if (all(!is.finite(x))) return(1)
  if (any(x <= 0, na.rm = TRUE)) return(min_val)
  result <- prod(x, na.rm = TRUE)
  if (!is.finite(result)) return(1)
  max(min_val, min(result, max_val))
}
