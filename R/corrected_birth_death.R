# Corrected Birth and Death Functions for RJMCMC
# Based on thesis section 5.2.1.3 and 5.2.1.4

#' Corrected Birth Proposal Function
#' @param params RJMCMC parameters
#' @param jump Current jump matrix
#' @param i_idx Segment index to split
#' @param datalist Data list
#' @return New jump matrix or original if failed
sampleBirthProposal_corrected <- function(params, jump, i_idx, datalist) {
  cat("=== BIRTH PROPOSAL DEBUG ===\n")
  cat("Input i_idx:", i_idx, "\n")
  cat("Input jump dimensions:", nrow(jump), "x", ncol(jump), "\n")
  cat("Input beta:", paste(round(jump[1,], 4), collapse=", "), "\n")
  cat("Input cp:", paste(jump[2,], collapse=", "), "\n")
  
  # Use safety check functions
  if (!validate_rjmc_params(params, 1) || !validate_jump_matrix(jump, datalist$T)) {
    cat("Safety check failed\n")
    return(jump)
  }
  
  # Split segment i_idx at a random interior point; preserve weighted geometric mean
  T <- datalist$T
  beta <- as.numeric(jump[1, ])
  cp   <- as.integer(round(jump[2, ]))
  K    <- length(beta)
  
  # Safety checks
  cat("K =", K, "T =", T, "\n")
  if (K < 1 || any(!is.finite(beta)) || any(!is.finite(cp))) {
    cat("Safety check failed: K < 1 or non-finite values\n")
    return(jump)
  }
  if (any(beta <= 0)) {
    cat("Safety check failed: non-positive beta values\n")
    return(jump)
  }

  # Compute segment boundaries (thesis notation: sj-1, sj, sj+1)
  # For segment j, boundaries are (cp[j-1], cp[j]) where cp[0] = 0, cp[K] = T
  if (i_idx < 1 || i_idx > K) return(jump)
  
  # Get segment boundaries according to thesis
  s_left  <- if (i_idx == 1) 0 else cp[i_idx - 1]
  s_right <- if (i_idx <= K) cp[i_idx] else T
  cat("Segment boundaries: s_left =", s_left, "s_right =", s_right, "\n")
  
  # Check if segment is long enough to split
  if (s_right - s_left <= 1) {
    # If too short to split, pick a different index if possible
    long_idx <- which((cp - c(0, head(cp, -1))) > 1)
    if (length(long_idx) == 0) return(jump)
    i_idx <- sample(long_idx, 1)
    s_left  <- if (i_idx == 1) 0 else cp[i_idx - 1]
    s_right <- if (i_idx <= K) cp[i_idx] else T
  }

  # Draw random parameters for birth mapping (thesis eq. 5.51)
  s_star <- runif(1, s_left, s_right)  # u1 ~ Unif(sj, sj+1)
  u2 <- runif(1)                        # u2 ~ Unif(0,1)
  cat("Random parameters: s_star =", round(s_star, 2), "u2 =", round(u2, 4), "\n")
  
  # Preserve weighted geometric mean of heights (thesis eq. 5.47)
  w_minus <- s_star - s_left   # s* - sj
  w_plus <- s_right - s_star   # sj+1 - s*
  beta_parent <- beta[i_idx]
  
  # Safety check for beta_parent
  if (!is.finite(beta_parent) || beta_parent <= 0) return(jump)
  
  # New heights preserving weighted geometric mean (thesis eq. 5.51)
  ratio <- (1 - u2) / u2
  beta_L <- (ratio)^(-w_plus/(w_plus + w_minus)) * beta_parent
  beta_R <- (ratio)^(w_minus/(w_plus + w_minus)) * beta_parent
  cat("New heights: beta_L =", round(beta_L, 4), "beta_R =", round(beta_R, 4), "\n")
  
  # Ensure new heights are positive and finite
  beta_L <- max(0.01, min(beta_L, 1.0))
  beta_R <- max(0.01, min(beta_R, 1.0))
  
  # Safety check for new betas
  if (!is.finite(beta_L) || !is.finite(beta_R)) return(jump)
  if (beta_L <= 0 || beta_R <= 0) return(jump)

  # Create new vectors: K+1 segments need K+1 change-points
  beta_out <- numeric(K + 1)
  cp_out <- integer(K + 1)
  cat("Creating output vectors: beta_out length =", length(beta_out), "cp_out length =", length(cp_out), "\n")
  
  # Copy existing values - maintain order
  beta_out[1:i_idx] <- beta[1:i_idx]
  beta_out[i_idx + 1] <- beta_L
  if (i_idx < K) {
    beta_out[(i_idx + 2):(K + 1)] <- beta[(i_idx + 1):K]
  }
  
      # Copy change-points - handle special case when K=1
    if (K == 1) {
      # Special case: going from 1 to 2 segments
      # Original: cp = [T], we want: cp_out = [s_star, T]
      cp_out[1] <- s_star
      cp_out[2] <- T
    } else {
      # General case: K > 1
      # Copy existing change-points up to the split segment
      cp_out[1:i_idx] <- cp[1:i_idx]
      cp_out[i_idx + 1] <- s_star
      if (i_idx < K) {
        cp_out[(i_idx + 2):(K + 1)] <- cp[(i_idx + 1):K]
      }
      cp_out[K + 1] <- T  # Last change-point is always T
    }
  
  # Ensure change-points are ordered and in (0, T)
  cp_out <- sort(cp_out)
  cp_out[1] <- max(1, cp_out[1])  # First change-point >= 1
  cp_out[length(cp_out)] <- T      # Last change-point = T
  
  # Safety check for output vectors
  if (any(!is.finite(beta_out)) || any(!is.finite(cp_out))) return(jump)
  if (any(beta_out <= 0)) return(jump)
  if (any(cp_out < 1) || any(cp_out > T)) return(jump)
  if (is.unsorted(cp_out, strictly = TRUE)) return(jump)

  new_jump <- matrix(c(beta_out, cp_out), nrow = 2, byrow = TRUE)
  
  # Final safety check for new_jump matrix
  if (any(!is.finite(new_jump))) return(jump)
  if (ncol(new_jump) != K + 1) return(jump)
  
  # Verify dimensions match (thesis: k+1 segments need k+1 change-points)
  if (length(beta_out) != K + 1 || length(cp_out) != K + 1) {
    # cat("ERROR: Birth dimension mismatch - beta_out:", length(beta_out), "cp_out:", length(cp_out), "expected:", K + 1, "x", K + 1, "\n")
    return(jump)
  }
  
  # Store random parameters for Jacobian calculation (attach as attribute)
  attr(new_jump, "birth_params") <- list(
    i_idx = i_idx, s_star = s_star, u2 = u2, 
    beta_parent = beta_parent, w_minus = w_minus, w_plus = w_plus
  )
 
  new_jump
}

#' Corrected Death Proposal Function
#' @param params RJMCMC parameters
#' @param jump Current jump matrix
#' @param i_idx Segment index to merge
#' @param datalist Data list
#' @return New jump matrix or original if failed
sampleDeathProposal_corrected <- function(params, jump, i_idx, datalist) {
  # Use safety check functions
  if (!validate_rjmc_params(params, 1)) {
    return(jump)
  }
  
  # Merge segment i_idx with neighbor (prefer next; if last, merge with previous)
  T <- datalist$T
  beta <- as.numeric(jump[1, ])
  cp   <- as.integer(round(jump[2, ]))
  K    <- length(beta)
  if (K <= 1) return(jump)

  # Safety checks
  if (any(!is.finite(beta)) || any(!is.finite(cp))) return(jump)
  if (any(beta <= 0)) return(jump)  # betas must be positive

  i_idx <- max(1, min(i_idx, K))

  if (i_idx < K) {
    # merge i and i+1; drop cp[i_idx]
    # Calculate segment lengths correctly
    if (i_idx == 1) {
      len1 <- cp[i_idx]
    } else {
      len1 <- cp[i_idx] - cp[i_idx - 1]
    }
    len2 <- cp[i_idx + 1] - cp[i_idx]
    
    # Safety check for segment lengths
    if (len1 <= 0 || len2 <= 0) return(jump)
    
    # Weighted average of betas (thesis eq. 5.54)
    beta_merged <- (len1 * beta[i_idx] + len2 * beta[i_idx + 1]) / (len1 + len2)
    
    # Safety check for merged beta
    if (!is.finite(beta_merged)) return(jump)
    if (beta_merged <= 0) return(jump)
    
    # Create new vectors: K-1 segments need K-1 change-points
    beta_out <- numeric(K - 1)
    cp_out <- integer(K - 1)
    
    # Copy existing values
    beta_out[1:(i_idx - 1)] <- beta[1:(i_idx - 1)]
    beta_out[i_idx] <- beta_merged
    beta_out[(i_idx + 1):(K - 1)] <- beta[(i_idx + 2):K]
    
    # Copy change-points: drop cp[i_idx], keep others, ensure last is T
    cp_out[1:(i_idx - 1)] <- cp[1:(i_idx - 1)]
    cp_out[i_idx:(K - 2)] <- cp[(i_idx + 1):(K - 1)]
    cp_out[K - 1] <- T  # Last change-point is always T
    
  } else {
    # merge K with K-1; drop cp[K-1]
    if (K == 2) {
      # Special case: only 2 segments, merge them
      len1 <- cp[1]
      len2 <- T - cp[1]
      beta_merged <- (len1 * beta[1] + len2 * beta[2]) / (len1 + len2)
      
      # Safety check for merged beta
      if (!is.finite(beta_merged)) return(jump)
      if (beta_merged <= 0) return(jump)
      
      beta_out <- beta_merged
      cp_out   <- T
    } else {
      # K > 2, merge last two segments
      len1 <- cp[K-1] - cp[K-2]
      len2 <- T - cp[K-1]
      
      # Safety check for segment lengths
      if (len1 <= 0 || len2 <= 0) return(jump)
      
      beta_merged <- (len1 * beta[K-1] + len2 * beta[K]) / (len1 + len2)
      
      # Safety check for merged beta
      if (!is.finite(beta_merged)) return(jump)
      if (beta_merged <= 0) return(jump)
      
      # Create new vectors: K-1 segments need K-1 change-points
      beta_out <- numeric(K - 1)
      cp_out <- integer(K - 1)
      
      beta_out[1:(K-2)] <- beta[1:(K-2)]
      beta_out[K-1] <- beta_merged
      
      cp_out[1:(K-2)] <- cp[1:(K-2)]
      cp_out[K-1] <- T
    }
  }
  
  # Safety check for output
  if (any(!is.finite(beta_out)) || any(!is.finite(cp_out))) return(jump)
  if (any(beta_out <= 0)) return(jump)
  if (any(cp_out < 1) || any(cp_out > T)) return(jump)
  
  # Verify dimensions
  expected_beta_len <- if(K == 2) 1 else K - 1
  expected_cp_len <- if(K == 2) 1 else K - 1  # K-1 segments need K-1 change-points
  
  if (length(beta_out) != expected_beta_len || length(cp_out) != expected_cp_len) {
    # cat("ERROR: Death dimension mismatch - beta_out:", length(beta_out), "cp_out:", length(cp_out), "expected:", expected_beta_len, "x", expected_cp_len, "\n")
    return(jump)
  }
  
  new_jump <- matrix(c(beta_out, cp_out), nrow = 2, byrow = TRUE)
  
  # Store parameters for Jacobian calculation (attach as attribute)
  attr(new_jump, "death_params") <- list(
    i_idx = i_idx, beta_merged = beta_merged, K = K
  )
  
  # Final safety check
  if (any(!is.finite(new_jump))) return(jump)
  if (ncol(new_jump) != expected_beta_len) return(jump)

  cat("new_jump death: ", new_jump, "\n")
  cat("beta_out death: ", beta_out, "\n")
  cat("cp_out death: ", cp_out, "\n")
  cat("i_idx death: ", i_idx, "\n")
  cat("K death: ", K, "\n")

  new_jump
}

#' Validate change-points throughout the process
#' @param cp Change-point vector
#' @param T Total time
#' @param name Name for error messages
#' @return TRUE if valid, FALSE otherwise
validate_change_points <- function(cp, T, name = "change-points") {
  if (is.null(cp) || !is.vector(cp)) {
    cat("ERROR:", name, "is not a vector\n")
    return(FALSE)
  }
  
  if (length(cp) == 0) {
    cat("ERROR:", name, "has length 0\n")
    return(FALSE)
  }
  
  if (any(!is.finite(cp))) {
    cat("ERROR:", name, "contains non-finite values\n")
    return(FALSE)
  }
  
  if (any(cp < 1) || any(cp > T)) {
    cat("ERROR:", name, "contains values outside [1,", T, "]\n")
    return(FALSE)
  }
  
  if (is.unsorted(cp, strictly = TRUE)) {
    cat("ERROR:", name, "are not strictly increasing\n")
    return(FALSE)
  }
  
  if (cp[length(cp)] != T) {
    cat("ERROR: Last", name, "is not", T, "\n")
    return(FALSE)
  }
  
  TRUE
}

#' Validate segment heights throughout the process
#' @param beta Beta vector
#' @param name Name for error messages
#' @return TRUE if valid, FALSE otherwise
validate_segment_heights <- function(beta, name = "segment heights") {
  if (is.null(beta) || !is.vector(beta)) {
    cat("ERROR:", name, "is not a vector\n")
    return(FALSE)
  }
  
  if (length(beta) == 0) {
    cat("ERROR:", name, "has length 0\n")
    return(FALSE)
  }
  
  if (any(!is.finite(beta))) {
    cat("ERROR:", name, "contains non-finite values\n")
    return(FALSE)
  }
  
  if (any(beta <= 0)) {
    cat("ERROR:", name, "contains non-positive values\n")
    return(FALSE)
  }
  
  TRUE
}
