# Simple and Robust Birth/Death Functions for RJMCMC Change-Point Analysis
# Based on standard RJMCMC implementations for piecewise-constant functions

# Global variables to track move statistics
move_stats <- list(
  birth_attempts = 0,
  birth_successes = 0,
  death_attempts = 0,
  death_successes = 0,
  height_attempts = 0,
  height_successes = 0
)

#' Reset move statistics
resetMoveStats <- function() {
  move_stats <<- list(
    birth_attempts = 0,
    birth_successes = 0,
    death_attempts = 0,
    death_successes = 0,
    height_attempts = 0,
    height_successes = 0
  )
}

#' Report move statistics
reportMoveStats <- function() {
  cat("=== MOVE STATISTICS ===\n")
  cat("Birth moves:", move_stats$birth_successes, "/", move_stats$birth_attempts, 
      "(", round(100 * move_stats$birth_successes / max(1, move_stats$birth_attempts), 1), "%)\n")
  cat("Death moves:", move_stats$death_successes, "/", move_stats$death_attempts,
      "(", round(100 * move_stats$death_successes / max(1, move_stats$death_attempts), 1), "%)\n")
  cat("Height moves:", move_stats$height_successes, "/", move_stats$height_attempts,
      "(", round(100 * move_stats$height_successes / max(1, move_stats$height_attempts), 1), "%)\n")
  cat("=====================\n")
}

#' Simple Birth Proposal - Split a segment randomly
#' @param params RJMCMC parameters
#' @param jump Current jump matrix
#' @param i_idx Segment index to split
#' @param datalist Data list
#' @return New jump matrix or original if failed
simpleBirthProposal <- function(params, jump, i_idx, datalist) {
  #cat("=== SIMPLE BIRTH PROPOSAL ===\n")
  
  # Basic validation
  if (is.null(jump) || ncol(jump) < 1) {
    cat("Invalid jump matrix\n")
    return(jump)
  }
  
  T <- datalist$T
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(jump[2, ])
  K <- length(beta)
  
  #cat("Current state: K =", K, "T =", T, "\n")
  #cat("Current beta:", paste(round(beta, 4), collapse=", "), "\n")
 # cat("Current cp:", paste(cp, collapse=", "), "\n")
  
  # Visualize current segments for debugging
  visualizeSegments(jump, T)
  
  # Test which segments can be split
  testSegmentSplits(jump, T)
  
  # Safety checks
  if (K < 1 || any(!is.finite(beta)) || any(!is.finite(cp))) {
    cat("Safety check failed\n")
    return(jump)
  }
  
    # Choose segment to split (if i_idx is invalid, pick randomly)
  if (i_idx < 1 || i_idx > K) {
    i_idx <- sample(1:K, 1)
  }
 # cat("DEBUG: Selected segment", i_idx, "of", K, "segments\n")
 # cat("DEBUG: Available segments to split: 1 through", K, "\n")
  
    # Get segment boundaries - FIXED LOGIC
  if (i_idx == 1) {
    left_bound <- 1
  } else {
    left_bound <- cp[i_idx - 1] + 1
  }
  
  # The last segment goes from the last change-point to T
  if (i_idx == K) {
    right_bound <- T
  } else {
    right_bound <- cp[i_idx]
  }
  
  # Debug: show what we're actually splitting
 # cat("DEBUG: Splitting segment", i_idx, "from", left_bound, "to", right_bound, "\n")
#  cat("DEBUG: This segment contains days", left_bound, "through", right_bound, "\n")
  
  # cat("Segment boundaries:", left_bound, "to", right_bound, "\n")
  
  # Check if segment is long enough to split
 # cat("DEBUG: Segment width =", right_bound - left_bound + 1, "days\n")
  if (right_bound - left_bound < 5) {
  ##  cat("DEBUG: Segment too short to split (need at least 2 days)\n")
    return(jump)
  }
  
  # Improved split point selection: avoid clustering at boundaries
  # For the first segment, avoid splitting too close to the start
  if (i_idx == 1 && (right_bound - left_bound) > 10) {
    # First segment: avoid splitting in first 20% of the segment
    min_split <- left_bound + max(1, round(0.1 * (right_bound - left_bound)))
    split_point <- sample(min_split:(right_bound-1), 1)
  } else {
    # Other segments: random split within bounds, but avoid very short segments
    # Ensure the resulting segments are at least 5 days wide
    min_split <- left_bound + 4  # Left segment at least 5 days
    max_split <- right_bound - 5  # Right segment at least 5 days
    
    # Check if we can make a valid split
    if (min_split > max_split) {
      # cat("Segment too short to split meaningfully\n")
      return(jump)
    }
    
    split_point <- sample(min_split:max_split, 1)
  }
 #cat("Split point:", split_point, "\n")
  
  # Create new heights - simple approach: split the current height
  # Option 1: Random perturbation around current value
  current_beta <- beta[i_idx]
  new_beta1 <- current_beta * runif(1, 0.1, 10)
  new_beta2 <- current_beta * runif(1, 0.1, 10)
  
  # Ensure reasonable bounds
  new_beta1 <- max(0.01, min(new_beta1, 1.0))
  new_beta2 <- max(0.01, min(new_beta2, 1.0))
  
  #cat("New heights:", round(new_beta1, 4), "and", round(new_beta2, 4), "\n")
  
  # Create new vectors
  beta_out <- numeric(K + 1)
  cp_out <- integer(K + 1)
  
  # Copy existing values - FIXED LOGIC
  if (i_idx == K) {
    # Special case: splitting the last segment
    # Original: [cp[K-1], T] with height beta[K]
    # New: [cp[K-1], split_point] with height beta[K] AND [split_point, T] with height new_beta1
    
    # Copy all existing heights
    beta_out[1:K] <- beta[1:K]
    # Add the new height for the new segment
    beta_out[K + 1] <- new_beta1
    
   # cat("DEBUG: Split last segment at", split_point, "\n")
   # cat("DEBUG: Original: [", cp[K-1], ",", T, "] height =", beta[K], "\n")
   # cat("DEBUG: New segments: [", cp[K-1], ",", split_point, "] height =", beta[K], "AND [", split_point, ",", T, "] height =", new_beta1, "\n")
    
  } else {
    # General case: splitting non-last segment
    # Copy existing heights up to the split segment
    beta_out[1:i_idx] <- beta[1:i_idx]
    beta_out[i_idx + 1] <- new_beta1
    if (i_idx < K) {
      beta_out[(i_idx + 2):(K + 1)] <- beta[(i_idx + 1):K]
    }
  }
  
  # Copy change-points - FIXED LOGIC
  if (K == 1) {
    # Special case: going from 1 to 2 segments
    # Original: cp = [T], we want: cp_out = [split_point, T]
    cp_out[1] <- split_point
    cp_out[2] <- T
  } else if (i_idx == K) {
    # Special case: splitting the last segment
    # Copy all existing change-points
    cp_out[1:K] <- cp[1:K]
    # Add the new split point
    cp_out[K + 1] <- split_point
    # The last change-point is already T from the copy
  } else {
    # General case: splitting non-last segment
    # Copy existing change-points up to the split segment
    cp_out[1:i_idx] <- cp[1:i_idx]
    # Insert the new split point
    cp_out[i_idx + 1] <- split_point
    # Copy remaining change-points (shifted by 1 position)
    if (i_idx < K) {
      cp_out[(i_idx + 2):(K + 1)] <- cp[(i_idx + 1):K]
    }
    # Ensure the last change-point is T
    cp_out[K + 1] <- T
  }
  
  # Debug: show the copying process
  #cat("DEBUG: Original cp:", paste(cp, collapse=", "), "\n")
  #cat("DEBUG: i_idx =", i_idx, "split_point =", split_point, "\n")
  #cat("DEBUG: cp_out after copying:", paste(cp_out, collapse=", "), "\n")
  
  # Ensure ordering
  cp_out <- sort(cp_out)
  cp_out[1] <- max(1, cp_out[1])
  cp_out[length(cp_out)] <- T
  
 # cat("New cp:", paste(cp_out, collapse=", "), "\n")
 # cat("New beta:", paste(round(beta_out, 4), collapse=", "), "\n")
  
  # Create output matrix
  new_jump <- matrix(c(beta_out, cp_out), nrow = 2, byrow = TRUE)
  
  # Final validation
  if (ncol(new_jump) != K + 1) {
    cat("ERROR: Wrong output dimensions\n")
    return(jump)
  }
  
 # cat("Birth successful: K =", K, "->", K + 1, "\n")
 # cat("==================\n")
  
  new_jump
}

#' Simple Death Proposal - Merge adjacent segments
#' @param params RJMCMC parameters
#' @param jump Current jump matrix
#' @param i_idx Segment index to merge
#' @param datalist Data list
#' @return New jump matrix or original if failed
simpleDeathProposal <- function(params, jump, i_idx, datalist) {
 #cat("=== SIMPLE DEATH PROPOSAL ===\n")
  
  # Basic validation
  if (is.null(jump) || ncol(jump) <= 1) {
    cat("Cannot merge: only 1 segment\n")
    return(jump)
  }
  
  T <- datalist$T
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(jump[2, ])
  K <- length(beta)
  
  #cat("Current state: K =", K, "T =", T, "\n")
  #cat("Current beta:", paste(round(beta, 4), collapse=", "), "\n")
  #cat("Current cp:", paste(cp, collapse=", "), "\n")
  
  # Choose segments to merge
  if (i_idx < 1 || i_idx >= K) {
    i_idx <- sample(1:(K-1), 1)
  }
 #cat("Merging segments", i_idx, "and", i_idx + 1, "\n")
  
  # Calculate segment lengths for weighted average
  if (i_idx == 1) {
    len1 <- cp[1]
  } else {
    len1 <- cp[i_idx] - cp[i_idx - 1]
  }
  
  if (i_idx + 1 == K) {
    len2 <- T - cp[i_idx]
  } else {
    len2 <- cp[i_idx + 1] - cp[i_idx]
  }
  
  #cat("Segment lengths:", len1, "and", len2, "\n")
  
  # Weighted average of heights
  total_len <- len1 + len2
  merged_beta <- (len1 * beta[i_idx] + len2 * beta[i_idx + 1]) / total_len
  
  # Ensure reasonable bounds
  merged_beta <- max(0.01, min(merged_beta, 1.0))
  
  #cat("Merged height:", round(merged_beta, 4), "\n")
  
  # Create new vectors
  beta_out <- numeric(K - 1)
  cp_out <- integer(K - 1)
  
  # Copy existing values
  beta_out[1:(i_idx - 1)] <- beta[1:(i_idx - 1)]
  beta_out[i_idx] <- merged_beta
  if (i_idx + 1 < K) {
    beta_out[(i_idx + 1):(K - 1)] <- beta[(i_idx + 2):K]
  }
  
  # Copy change-points (drop the one between merged segments)
  cp_out[1:(i_idx - 1)] <- cp[1:(i_idx - 1)]
  if (i_idx + 1 < K) {
    cp_out[i_idx:(K - 2)] <- cp[(i_idx + 1):(K - 1)]
  }
  cp_out[K - 1] <- T
  
  #cat("New cp:", paste(cp_out, collapse=", "), "\n")
  #cat("New beta:", paste(round(beta_out, 4), collapse=", "), "\n")
  
  # Create output matrix
  new_jump <- matrix(c(beta_out, cp_out), nrow = 2, byrow = TRUE)
  
  # Final validation
  if (ncol(new_jump) != K - 1) {
    cat("ERROR: Wrong output dimensions\n")
    return(jump)
  }
  
 # cat("Death successful: K =", K, "->", K - 1, "\n")
 # cat("==================\n")
  
  new_jump
}

#' Simple Height Update - Random walk on existing heights
#' @param params RJMCMC parameters
#' @param jump Current jump matrix
#' @param i_idx Segment index to update
#' @param datalist Data list
#' @return New jump matrix or original if failed
simpleHeightUpdate <- function(params, jump, i_idx, datalist) {
  # cat("=== SIMPLE HEIGHT UPDATE ===\n")
  
  if (is.null(jump) || ncol(jump) < 1) {
    return(jump)
  }
  
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(jump[2, ])
  K <- length(beta)
  
  if (i_idx < 1 || i_idx > K) {
    i_idx <- sample(1:K, 1)
  }
  
  # cat("Updating height for segment", i_idx, "\n")
  # cat("Current height:", round(beta[i_idx], 4), "\n")
  
  # Simple random walk update
  current_beta <- beta[i_idx]
  step_size <- 0.01  # Small step size for stability
  new_beta <- current_beta + rnorm(1, 0, step_size)
  
  # Ensure reasonable bounds
  new_beta <- max(0.01, min(new_beta, 1.0))
  
  # cat("New height:", round(new_beta, 4), "\n")
  
  # Update the height
  beta[i_idx] <- new_beta
  
  # Return updated matrix
  rbind(beta, cp)
}

#' Simple Change-Point Update - Random walk on change-point positions
#' @param params RJMCMC parameters
#' @param jump Current jump matrix
#' @param i_idx Change-point index to update
#' @param datalist Data list
#' @return New jump matrix or original if failed
simpleChangePointUpdate <- function(params, jump, i_idx, datalist) {
  # cat("=== SIMPLE CHANGE-POINT UPDATE ===\n")
  
  if (is.null(jump) || ncol(jump) < 2) {
    return(jump)
  }
  
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(jump[2, ])
  K <- length(beta)
  
  if (i_idx < 1 || i_idx >= K) {
    i_idx <- sample(1:(K-1), 1)
  }
  
  # cat("Updating change-point", i_idx, "\n")
  # cat("Current position:", cp[i_idx], "\n")
  
  # Get bounds for this change-point
  left_bound <- if (i_idx == 1) 1 else cp[i_idx - 1] + 1
  right_bound <- if (i_idx + 1 == K) datalist$T else cp[i_idx + 1] - 1
  
  # cat("Bounds:", left_bound, "to", right_bound, "\n")
  
  # Simple random walk update
  step_size <- 2  # Integer step size
  new_pos <- cp[i_idx] + sample(-step_size:step_size, 1)
  
  # Ensure bounds
  new_pos <- max(left_bound, min(new_pos, right_bound))
  
  # cat("New position:", new_pos, "\n")
  
  # Update the change-point
  cp[i_idx] <- new_pos
  
  # Ensure ordering
  cp <- sort(cp)
  cp[1] <- max(1, cp[1])
  cp[length(cp)] <- datalist$T
  
  # Return updated matrix
  rbind(beta, cp)
}

#' Visualize current segments for debugging
#' @param jump Current jump matrix
#' @param T Total time
#' @return NULL (prints visualization)
visualizeSegments <- function(jump, T) {
  if (is.null(jump) || ncol(jump) < 1) {
   # cat("No segments to visualize\n")
    return(NULL)
  }
  
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(jump[2, ])
  K <- length(beta)
  
  # ===\n")
  #cat("K =", K, "segments\n")
  
  for (i in 1:K) {
    if (i == 1) {
      left <- 1
    } else {
      left <- cp[i-1] + 1
    }
    
    if (i == K) {
      right <- T
    } else {
      right <- cp[i]
    }
    
    width <- right - left + 1
 #   cat(sprintf("Segment %d: [%3d, %3d] width=%3d beta=%.4f\n", 
        #        i, left, right, width, beta[i]))
  }
 # cat("============================\n")
}

#' Validate jump matrix
#' @param jump Jump matrix
#' @param T Total time
#' @return TRUE if valid, FALSE otherwise
validateSimpleJump <- function(jump, T) {
  if (is.null(jump) || !is.matrix(jump) || nrow(jump) != 2) {
    # cat("Invalid jump matrix structure\n")
    return(FALSE)
  }
  
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(jump[2, ])
  
  if (length(beta) != length(cp)) {
    # cat("Dimension mismatch between beta and cp\n")
    return(FALSE)
  }
  
  if (any(!is.finite(beta))) {
    # cat("Non-finite beta values\n")
    return(FALSE)
  }
  
  if (any(beta <= 0)) {
    # cat("Non-positive beta values\n")
    return(FALSE)
  }
  
  if (any(!is.finite(cp))) {
    # cat("Non-finite change-point values\n")
    return(FALSE)
  }
  
  if (any(cp < 1) || any(cp > T)) {
    # cat("Change-points outside bounds [1,", T, "]\n")
    return(FALSE)
  }
  
  if (is.unsorted(cp, strictly = TRUE)) {
    # cat("Change-points not strictly ordered\n")
    return(FALSE)
  }
  
  if (cp[length(cp)] != T) {
    # cat("Last change-point is not T\n")
    return(FALSE)
  }
  
  TRUE
}

#' Check for problematic segments that might be causing stuck behavior
#' @param jump Current jump matrix
#' @param T Total time
#' @return List of problematic segments and suggestions
checkProblematicSegments <- function(jump, T) {
  if (is.null(jump) || ncol(jump) < 1) {
    return(list(has_problems = FALSE, issues = "No segments"))
  }
  
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(jump[2, ])
  K <- length(beta)
  
  issues <- list()
  has_problems <- FALSE
  
  for (i in 1:K) {
    if (i == 1) {
      left <- 1
    } else {
      left <- cp[i-1] + 1
    }
    
    if (i == K) {
      right <- T
    } else {
      right <- cp[i]
    }
    
    width <- right - left + 1
    
    # Check for very short segments
    if (width < 5) {
      issues[[length(issues) + 1]] <- paste0("Segment ", i, " too short: [", left, ", ", right, "] width=", width)
      has_problems <- TRUE
    }
    
    # Check for segments near the end
    if (right > T - 5 && width < 10) {
      issues[[length(issues) + 1]] <- paste0("Segment ", i, " too close to end: [", left, ", ", right, "]")
      has_problems <- TRUE
    }
    
    # Check for very small beta values
    if (beta[i] < 0.01) {
      issues[[length(issues) + 1]] <- paste0("Segment ", i, " has very small beta: ", round(beta[i], 6))
      has_problems <- TRUE
    }
  }
  
  if (has_problems) {
    cat("=== PROBLEMATIC SEGMENTS DETECTED ===\n")
    for (issue in issues) {
      cat("  ", issue, "\n")
    }
    cat("=====================================\n")
  }
  
  list(has_problems = has_problems, issues = issues)
}

#' Test which segments can be split (for debugging)
#' @param jump Current jump matrix
#' @param T Total time
#' @return List of splittable segments
testSegmentSplits <- function(jump, T) {
  if (is.null(jump) || ncol(jump) < 1) {
    return(list())
  }
  
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(jump[2, ])
  K <- length(beta)
  
 # cat("=== TESTING SEGMENT SPLITS ===\n")
 # cat("K =", K, "segments\n")
  
  splittable <- list()
  
  for (i in 1:K) {
    if (i == 1) {
      left <- 1
    } else {
      left <- cp[i-1] + 1
    }
    
    if (i == K) {
      right <- T
    } else {
      right <- cp[i]
    }
    
    width <- right - left + 1
    
  #  cat("Segment", i, ": [", left, ",", right, "] width =", width)
    
    if (width < 2) {
     # cat(" - TOO SHORT\n")
    } else if (width < 10) {
     # cat(" - SHORT (may cause issues)\n")
      splittable[[length(splittable) + 1]] <- i
    } else {
     # cat(" - GOOD\n")
      splittable[[length(splittable) + 1]] <- i
    }
  }
  
  #cat("Splittable segments:", paste(unlist(splittable), collapse=", "), "\n")
  #cat("==============================\n")
  
  splittable
}
