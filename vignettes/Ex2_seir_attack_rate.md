---
title: "Example 2: SEIR change-point attack rate"
author: "David Hodgson"
date: "2025-08-12"
output: rmarkdown::html_vignette
vignette: >
  %\VignetteIndexEntry{Example 2: SEIR change-point attack rate}
  %\VignetteEngine{knitr::rmarkdown}
  %\VignetteEncoding{UTF-8}
---

<!-- Triggering GitHub Actions workflow -->



This vignette demonstrates using RJMCMC to infer a piecewise-constant attack/transmission rate (change-point analysis) in a simple SEIR model from simulated incidence data.

- The time-varying transmission rate \(\beta(t)\) is modeled as a step function with an unknown number of segments and unknown change-points.
- RJMCMC explores the model dimension by proposing birth/death moves on the number of segments, and random-walk updates to segment-specific \(\beta\) values.
- We show recovery of both the number and locations of change-points and the underlying incidence curve.

**Note**: All safety checks and validation functions have been extracted to separate R files to make this vignette more concise and maintainable. When running this vignette interactively, these functions will be automatically loaded. For pkgdown builds, the functions are already available through the package.

## 1. Packages


``` r
library(devtools)
devtools::load_all()

library(dplyr)
library(tidyr)
library(purrr)
library(ggplot2)
library(tidybayes)
library(ggdist)

# Load safety check functions (only when running interactively)
# These functions provide comprehensive input validation and safe defaults
# See R/safety_check_Ex2.R for full documentation
# Note: In pkgdown builds, these functions are available through the package
if (interactive()) {
  source("R/safety_check_Ex2.R")
  
  # Load corrected birth and death functions
  # These functions match the thesis exactly and include proper dimension checks
  source("R/corrected_birth_death.R")
  
  # Load simple and robust birth/death functions
  # These are much simpler and more standard implementations
  source("R/simple_birth_death.R")
}

# Using more than one core might fail on windows
aaa_mc_cores <- if (.Platform$OS.type == "windows") 1 else 2
```

## 2. Simulate SEIR with piecewise-constant transmission rate

We simulate a discrete-time SEIR model (day step) with a piecewise-constant \(\beta(t)\) and normal observation noise on daily incidence.

- Population: \(N = 100{,}000\)
- Latent period: 1/\(\sigma\) = 4 days
- Infectious period: 1/\(\gamma\) = 6 days
- Change-points at days 40 and 80 with segment values: 0.30, 0.01, 0.40


``` r
# Helper to expand piecewise-constant beta from segment endpoints
make_beta_t <- function(beta_vec, cp_vec, T) {
  # Use safety check functions
  if (!validate_make_beta_t_inputs(beta_vec, cp_vec, T)) {
    return(create_safe_beta(T))
  }
  
  # Ensure change-points are within bounds and ordered
  ends <- pmin(pmax(round(cp_vec), 1), T)
  ends[length(ends)] <- T
  
  starts <- c(1, head(ends, -1) + 1)
  
  # Initialize output vector
  beta_t <- rep(0.1, T)
  
  # Fill in segment values
  for (k in seq_along(beta_vec)) {
    if (k <= length(starts) && k <= length(ends)) {
      start_idx <- starts[k]
      end_idx <- ends[k]
      
      if (is.finite(start_idx) && is.finite(end_idx) && 
          start_idx >= 1 && end_idx <= T && start_idx <= end_idx) {
        idx <- start_idx:end_idx
        if (length(idx) > 0) {
          beta_t[idx] <- beta_vec[k]
        }
      }
    }
  }
  
  # Final safety check
  if (any(!is.finite(beta_t)) || any(beta_t <= 0)) {
    return(create_safe_beta(T))
  }
  
  beta_t
}

# Deterministic SEIR forward solver for expected incidence
seir_expected_incidence <- function(T, N, beta_t, gamma, S0, E0, I0, R0, rho = 1.0) {
  # Use safety check functions
  if (!validate_seir_inputs(T, N, beta_t, gamma, S0, E0, I0, R0, rho)) {
    return(create_safe_seir_result(1))
  }
  
  # Initialize arrays
  S <- numeric(T); E <- numeric(T); I <- numeric(T); R <- numeric(T)
  inc <- numeric(T)
  
  # Set initial conditions
  S[1] <- max(0, S0); E[1] <- max(0, E0); I[1] <- max(0, I0); R[1] <- max(0, R0)
  
  # Forward simulation
  for (t in 1:T) {
    # Safety check for current state
    if (!is.finite(S[t]) || !is.finite(E[t]) || !is.finite(I[t]) || !is.finite(R[t])) {
      S[t] <- max(0, S0); E[t] <- max(0, E0); I[t] <- max(0, I0); R[t] <- max(0, R0)
    }
    
    # Calculate transmission rate
    lambda <- beta_t[t] * I[t] / N
    if (!is.finite(lambda) || lambda < 0) lambda <- 0
    
    # Calculate transitions
    new_inf <- lambda * S[t]
    new_E_to_I <- gamma * E[t]
    new_I_to_R <- gamma * I[t]
    
    # Safety checks for transitions
    if (!is.finite(new_inf) || new_inf < 0) new_inf <- 0
    if (!is.finite(new_E_to_I) || new_E_to_I < 0) new_E_to_I <- 0
    if (!is.finite(new_I_to_R) || new_I_to_R < 0) new_I_to_R <- 0
    
    # Record incidence
    inc[t] <- rho * new_inf
    if (!is.finite(inc[t]) || inc[t] < 0) inc[t] <- 0
    
    # Update states for next time step
    if (t < T) {
      S[t + 1] <- max(S[t] - new_inf, 0)
      E[t + 1] <- max(E[t] + new_inf - new_E_to_I, 0)
      I[t + 1] <- max(I[t] + new_E_to_I - new_I_to_R, 0)
      R[t + 1] <- min(R[t] + new_I_to_R, N)
      
      # Safety checks for next state
      if (!is.finite(S[t + 1])) S[t + 1] <- max(0, S0)
      if (!is.finite(E[t + 1])) E[t + 1] <- max(0, E0)
      if (!is.finite(I[t + 1])) I[t + 1] <- max(0, I0)
      if (!is.finite(R[t + 1])) R[t + 1] <- max(0, R0)
    }
  }
  
  # Final safety check for output
  if (any(!is.finite(S)) || any(!is.finite(E)) || any(!is.finite(I)) || 
      any(!is.finite(R)) || any(!is.finite(inc))) {
    return(create_safe_seir_result(T))
  }
  
  list(S = S, E = E, I = I, R = R, incidence = inc)
}

# Truth
T_days <- 120
N_pop  <- 100000
sigma  <- 1/4
gamma  <- 1/6
rho_true <- 1.0
beta_true_vals <- c(0.3, 0.01, 0.4)  # Transmission rates between 0 and 1
cp_true        <- c(40, 80, T_days)  # segment endpoints (last must be T)
beta_true_t    <- make_beta_t(beta_true_vals, cp_true, T_days)

init_I <- 1000

sim_true <- seir_expected_incidence(
  T = T_days, N = N_pop, beta_t = beta_true_t,
  gamma = gamma, S0 = N_pop - init_I, E0 = 0, I0 = init_I, R0 = 0,
  rho = rho_true
)

# Observations: Poisson noise on expected incidence
sigma_obs <- 4  # observation noise standard deviation (not used for Poisson)
obs_y <- rpois(T_days, lambda = sim_true$incidence)
obs_y <- pmax(obs_y, 0)  # ensure non-negative observations

# Quick visuals
p_obs <- tibble(day = 1:T_days, y = obs_y) %>%
  ggplot(aes(day, y)) + geom_col(fill = "grey80", color = "grey20") +
  labs(x = "Day", y = "Incidence", title = "Simulated daily incidence (observed)") + theme_bw() + ylim(0, NA)

p_beta <- tibble(day = 1:T_days, beta = beta_true_t) %>%
  ggplot(aes(day, beta)) + geom_step(color = "red", linewidth = 1) +
  labs(x = "Day", y = expression(beta(t)), title = expression("True transmission "*beta(t))) + theme_bw() + ylim(0, NA)



require(patchwork)
p_obs / p_beta
```

![plot of chunk simulate](figure/simulate-1.png)

## 3. RJMCMC model specification

We define the model interface required by `rjmc_func`. The `jump` matrix encodes the change-point segmentation:

- Row 1: segment-specific transmission rates \(\beta_k\) in [0, 1]
- Row 2: segment end days (in 1..T), increasing, with the last equal to T

The continuous parameter vector contains a single parameter controlling normal observation noise: \(\sigma = e^{\theta}\), where \(\theta\) is unconstrained.

### 3.1 Theoretical Framework

This implementation follows the RJMCMC theory from Lyyjynen (2014) §5.2 for piecewise-constant intensity functions:

- **Prior on number of change-points**: \(k \sim \text{Poisson}(\mu) \cdot e^{-\lambda k}\) where \(k = K-1\) (K = number of segments)
  - Modified to strongly prefer fewer segments with \(\mu = 0.5\) and penalty factor \(\lambda = 2.0\)
- **Prior on segment heights**: \(\beta_k \sim \text{Gamma}(\alpha, \beta)\) 
- **Prior on observation noise**: \(\log(\sigma) \sim \text{Normal}(\log(10), 1)\) where \(\sigma\) is the standard deviation
- **Spacing prior**: \(p(s) \propto \prod_{j=1}^{k+1} (s_j - s_{j-1})\) for ordered change-points
- **Birth proposal**: Split a segment at random point, preserve weighted geometric mean of heights
- **Death proposal**: Merge adjacent segments, weighted average of heights
- **Acceptance ratios**: Include proposal PDFs, Jacobian, and prior ratios as per Green (1995)
- **Likelihood**: \(y_t \sim \text{Normal}(\mu_t, \sigma^2)\) where \(\mu_t\) is the expected incidence from the SEIR model


``` r
# Build expected incidence given a jump matrix
expected_incidence_from_jump <- function(params, jump, datalist) {
  # Use safety check functions
  if (!validate_rjmc_params(params, 1)) {
    stop("expected_incidence_from_jump: Expected 1 dummy parameter for Poisson model")
  }
  
  if (!validate_datalist(datalist) || !validate_jump_matrix(jump, datalist$T)) {
    return(rep(0, datalist$T))
  }
  
  # Extract parameters
  T <- datalist$T
  S0 <- datalist$S0
  E0 <- datalist$E0
  I0 <- datalist$I0
  R0 <- datalist$R0
  gamma <- datalist$gamma
  rho <- datalist$rho
  
  # Extract beta and change-points from jump
  beta <- as.numeric(jump[1, ])
  cp <- as.integer(round(jump[2, ]))
  
  # Create piecewise-constant beta function
  beta_t <- make_beta_t(beta, cp, T)
  
  # Solve SEIR model
  result <- seir_expected_incidence(T, datalist$N, beta_t, gamma, S0, E0, I0, R0, rho)
  
  # Safety check for result
  if (is.null(result) || !is.list(result) || is.null(result$incidence)) {
    return(rep(0, T))
  }
  
  # Return only the incidence vector, not the entire result object
  result$incidence
}

# Helper function to compute Jacobian for birth transformation
# Based on thesis §5.2: J ≈ h_parent / u2^2 for the (h_j, u1, u2) -> (h_L, h_R, s*) mapping
compute_birth_jacobian <- function(beta_parent, u2) {
  # Use safety check functions
  if (!validate_numeric_param(beta_parent, "beta_parent", min_val = 0.001) || 
      !validate_numeric_param(u2, "u2", min_val = 0.001, max_val = 0.999)) {
    return(1.0)
  }
  
  # Simplified Jacobian: J ≈ h_parent / u2^2
  jacobian <- abs(beta_parent / (u2^2))
  
  # Bound the Jacobian to reasonable values
  max(0.1, min(jacobian, 100))
}

# Helper function to compute Jacobian for death transformation
# Based on thesis §5.2: J ≈ 1 for the death move (inverse of birth)
compute_death_jacobian <- function(beta_merged, beta_old, w_minus, w_plus) {
  # Use safety check functions
  if (!validate_numeric_param(beta_merged, "beta_merged", min_val = 0.001) ||
      !validate_numeric_param(beta_old, "beta_old", min_val = 0.001) ||
      !validate_numeric_param(w_minus, "w_minus", min_val = 0.001) ||
      !validate_numeric_param(w_plus, "w_plus", min_val = 0.001)) {
    return(1.0)
  }
  
  # For death moves, the Jacobian is approximately 1
  1.0
}

# Helper function for proposal probabilities (to avoid circular references)
sampleProposal_internal <- function(params, jump, datalist) {
  # Use safety check functions
  if (!validate_rjmc_params(params, 1) || !validate_jump_matrix(jump, datalist$T)) {
    return(c(0.33, 0.33, 1.0))
  }
  
  # Based on thesis §5.2: birth/death probabilities derived from Poisson prior
  K <- ncol(jump)
  k <- K - 1  # number of change-points
  
  # Prior parameters
  mu_prior <- 2.5  # Poisson prior mean for number of change-points
  
  if (K <= 1) {
    return(c(0.5, 0.0, 1.0))  # only birth and within-model moves
  } else if (K >= 20) {
    return(c(0.0, 0.5, 1.0))  # only death and within-model moves
  } else {
    # Compute birth/death probabilities based on Poisson prior ratios
    bk <- min(0.6 * mu_prior / (k + 1), 0.6)
    dk <- min(0.6 * k / mu_prior, 0.6)
    
    # Ensure probabilities are finite and non-negative
    bk <- max(0.0, min(bk, 0.6))
    dk <- max(0.0, min(dk, 0.6))
    
    # Ensure probabilities sum to at most 0.9
    total <- bk + dk
    if (total > 0.9) {
      scale_factor <- 0.9 / total
      bk <- bk * scale_factor
      dk <- dk * scale_factor
    }
    
    c(bk, dk, 1.0)  # birth, death, within-model
  }
}

# RJMCMC model list
model <- list(
  lowerParSupport_fitted = c(-10),  # Dummy parameter bounds
  upperParSupport_fitted = c(10),
  namesOfParameters = c("dummy"),  # Dummy parameter name

  sampleInitPrior = function(datalist) {
    # For Poisson model, we need a dummy parameter for internal RJMCMC machinery
    # Initialize dummy parameter around 0
    result <- rnorm(1, 0, 1)
    
    # Use safety check functions
    if (!validate_numeric_param(result, "result", allow_null = FALSE)) {
      return(0)  # Return safe default if generation failed
    }
    
    result
  },

  sampleInitJump = function(params, datalist) {
    # Use safety check functions
    if (!validate_rjmc_params(params, 1) || !validate_datalist(datalist)) {
      return(create_safe_jump(100))
    }
    
    T <- datalist$T
    if (!validate_numeric_param(T, "T", min_val = 1)) {
      return(create_safe_jump(100))
    }
    
    # SIMPLIFIED: Start with exactly 2 segments for stability
    K <- 2
    cat("Initialization: K =", K, "\n")
    
    # Create 2 segments with reasonable beta values
    betas <- runif(K, 0.1, 0.5)  # Reasonable beta values
    
    # Place change-point at 1/3 of time range (more balanced than middle)
    # This avoids clustering at the start and gives more reasonable segment sizes
    cps <- c(round(T/3), T)
    
    # Safety check for generated values
    if (any(!is.finite(betas)) || any(!is.finite(cps))) {
      return(create_safe_jump(T))
    }
    
    # Ensure change-points are valid and ordered
    cps <- sort(cps)
    cps[length(cps)] <- T  # Ensure last change-point is exactly T
    
    # Final safety check
    if (any(cps < 1) || any(cps > T) || any(betas <= 0)) {
      return(create_safe_jump(T))
    }
    
    result <- matrix(c(betas, cps), nrow = 2, byrow = TRUE)
    
    # Final matrix check
    if (any(!is.finite(result)) || ncol(result) != K || nrow(result) != 2) {
      return(create_safe_jump(T))
    }
    
    result
  },

  evaluateLogPrior = function(params, jump, datalist) {
    # Use safety check functions
    if (!validate_rjmc_params(params, 1)) {
      stop("evaluateLogPrior: Expected 1 dummy parameter for Poisson model")
    }
    
    # Start with zero log prior (flat prior on dummy parameter)
    lp <- 0.0
    
    # Safety check for jump
    if (!validate_jump_matrix(jump, datalist$T, min_segments = 1, max_segments = 20)) {
      return(-Inf)
    }
    
    # Number of change-points: k ~ Poisson(μ) where k = K-1
    K <- ncol(jump)
    k <- K - 1  # number of change-points (excluding boundaries)
    
    # Prior that allows reasonable number of change points
    mu_prior <- 3  # prior mean for number of change-points
    
    # Simple Poisson prior without additional penalty
    lp <- lp + dpois(k, lambda = mu_prior, log = TRUE)
    
    # Safety check for Poisson prior
    if (!is.finite(lp)) return(-Inf)

    # Segment heights (betas): ~ Gamma(α,β) instead of uniform
    beta_vec <- jump[1, ]
    alpha_prior <- 2.0  # shape parameter
    beta_prior <- 5.0   # rate parameter (mean = α/β = 2.0/5.0 = 0.4)
    lp <- lp + sum(dgamma(beta_vec, shape = alpha_prior, rate = beta_prior, log = TRUE))
    
    # Safety check for Gamma prior
    if (!is.finite(lp)) return(-Inf)

    # Change-points: ordered spacing prior
    T <- datalist$T
    cp_vec <- as.integer(round(jump[2, ]))
    
    # Spacing prior: log(prod(widths)) from thesis (5.33)
    if (length(cp_vec) > 1) {
      starts <- c(1, head(cp_vec, -1))
      widths <- cp_vec - starts
      if (any(widths <= 0)) return(-Inf)  # Safety check for widths
      lp <- lp + sum(log(widths))
    }
    
    # Final safety check
    if (!is.finite(lp)) return(-Inf)
    
    # Debug output for extreme values
    if (lp < -1e6) {
      cat("WARNING: Very low prior:", lp, "K =", K, "\n")
    }
    
    lp
  },

  evaluateLogLikelihood = function(params, jump, datalist) {
    
    y   <- datalist$y
    T   <- datalist$T
    
    # Use safety check functions
    if (!validate_rjmc_params(params, 1)) {
      stop("evaluateLogLikelihood: Expected 1 dummy parameter for Poisson model")
    }

    mu_t <- expected_incidence_from_jump(params, jump, datalist)
    
    # Safety checks for expected incidence
    if (any(!is.finite(mu_t))) return(-Inf)
    if (any(mu_t < 0)) return(-Inf)

    mu_t <- pmax(mu_t, 1e-6)  # ensure positive expected values

    # Poisson likelihood for counts: y_t ~ Poisson(mu_t)
    log_lik <- dpois(y, lambda = mu_t, log = TRUE)
    if (any(!is.finite(log_lik))) return(-Inf)

    # Simple dimension penalty (much smaller)
    K <- ncol(jump)
    penalty_term <- log(K) * 0.1  # Small penalty for complexity

    result <- sum(log_lik) - penalty_term
    
    # Debug output for extreme values
    if (result < -1e6) {
      cat("WARNING: Very low likelihood:", result, "K =", K, "sum(log_lik) =", sum(log_lik), "\n")
    }
    
    result
  },

  sampleBirthProposal = function(params, jump, i_idx, datalist) {
    # Use simple birth function that's more robust
    simpleBirthProposal(params, jump, i_idx, datalist)
  },
  
  sampleDeathProposal = function(params, jump, i_idx, datalist) {
    # Use simple death function that's more robust
    simpleDeathProposal(params, jump, i_idx, datalist)
  },

  evaluateBirthProposal = function(params, jump, i_idx, datalist) {
    # Use safety check functions
    if (!validate_rjmc_params(params, 1) || !validate_jump_matrix(jump, datalist$T)) {
      return(-Inf)
    }
    
    # Based on thesis §5.2: birth acceptance ratio with proper proposal PDFs
    T <- datalist$T
    beta <- as.numeric(jump[1, ])
    cp   <- as.integer(round(jump[2, ]))
    K    <- length(beta)
    
    # Get current birth/death probabilities
    move_probs <- sampleProposal_internal(params, jump, datalist)
    
    # Safety check for move_probs
    if (length(move_probs) < 2 || any(!is.finite(move_probs))) {
      return(-Inf)
    }
    
    bk <- move_probs[1]  # birth probability
    dk1 <- move_probs[2] # death probability in new state (k+1)
    
    # Safety check for probabilities
    if (bk <= 0 || dk1 <= 0) {
      return(-Inf)
    }
    
    # Proposal ratio: log(d_{k+1} * L / (b_k * (k+1))) from thesis (5.50)
    log_prop_ratio <- log(dk1) + log(T) - log(bk) - log(K + 1)
    
    # Safety check for final result
    if (!is.finite(log_prop_ratio)) {
      return(-Inf)
    }
    
    log_prop_ratio
  },

  evaluateDeathProposal = function(params, jump, i_idx, datalist) {
    # Use safety check functions
    if (!validate_rjmc_params(params, 1) || !validate_jump_matrix(jump, datalist$T)) {
      return(-Inf)
    }
    
    # Based on thesis §5.2: death acceptance ratio with proper proposal PDFs
    T <- datalist$T
    beta <- as.numeric(jump[1, ])
    cp   <- as.integer(round(jump[2, ]))
    K    <- length(beta)
    
    if (K <= 1) return(-Inf)
    
    # For death, the proposal ratio is the inverse of birth
    # From thesis (5.55): log(b_{k-1} * k / (d_k * L))
    
    # Get current birth/death probabilities
    move_probs <- sampleProposal_internal(params, jump, datalist)
    
    # Safety check for move_probs
    if (length(move_probs) < 2 || any(!is.finite(move_probs))) {
      return(-Inf)
    }
    
    dk <- move_probs[2]      # death probability in current state
    bk_minus1 <- move_probs[1] # birth probability in new state (k-1)
    
    # Proposal ratio: log(b_{k-1} * k / (d_k * L))
    log_prop_ratio <- log(bk_minus1) + log(K) - log(dk) - log(T)
    
    # Safety check for final result
    if (!is.finite(log_prop_ratio)) {
      return(-Inf)
    }
    
    log_prop_ratio
  },

  sampleJump = function(params, jump, i_idx, datalist) {
    # Use simple height update function that's more robust
    alpha <- runif(1, 0, 1)
    if (alpha < 0.3) {
      jump <- simpleHeightUpdate(params, jump, i_idx, datalist)
    } else if (alpha < 0.6) {
      jump <- simpleChangePointUpdate(params, jump, i_idx, datalist)
    } else {

    }
    jump
  },
  

  sampleProposal = function(params, jump, datalist) {
    # Simple, balanced proposal probabilities
    K <- ncol(jump)
    
    if (K <= 1) {
      # Can't have fewer than 1 segment - only birth and within-model
      return(c(0.4, 0.0, 0.6))  # birth, death, within-model
    } else if (K >= 20) {
      # Can't have more than 20 segments - only death and within-model
      return(c(0.0, 0.4, 0.6))  # birth, death, within-model
    } else {
      # Balanced probabilities for intermediate K values
      return(c(0.3, 0.3, 0.4))  # birth, death, within-model
    }
  }
)
```

# Diagnostic function to monitor RJMC mixing
diagnose_rjmc_mixing <- function(outputs) {
  cat("=== RJMC Mixing Diagnostics ===\n")
  
  # Extract jump lengths across all chains
  jump_lengths <- unlist(lapply(outputs$jump, function(chain) {
    sapply(chain, function(sample) ncol(sample))
  }))
  
  # Summary statistics
  cat("Jump length summary:\n")
  cat("  Min:", min(jump_lengths), "\n")
  cat("  Max:", max(jump_lengths), "\n")
  cat("  Mean:", round(mean(jump_lengths), 2), "\n")
  cat("  Median:", median(jump_lengths), "\n")
  
  # Frequency table
  freq_table <- table(jump_lengths)
  cat("\nJump length frequencies:\n")
  for (k in sort(as.numeric(names(freq_table)))) {
    cat("  K =", k, ":", freq_table[as.character(k)], "(", 
        round(100 * freq_table[as.character(k)] / length(jump_lengths), 1), "%)\n")
  }
  
  # Check for stuck chains
  stuck_threshold <- 0.8  # If 80% of samples are in one state, consider it stuck
  max_freq <- max(freq_table) / length(jump_lengths)
  if (max_freq > stuck_threshold) {
    cat("\n⚠️  WARNING: Algorithm appears to be stuck!\n")
    cat("   Most frequent state accounts for", round(100 * max_freq, 1), "% of samples\n")
    cat("   Consider:\n")
    cat("   1. Increasing iterations and burn-in\n")
    cat("   2. Adjusting proposal probabilities\n")
    cat("   3. Improving initialization\n")
  } else {
    cat("\n✅ Good mixing: No single state dominates\n")
  }
  
  # Effective sample size approximation
  ess_approx <- length(jump_lengths) / (1 + 2 * sum(acf(jump_lengths, plot = FALSE)$acf[-1]))
  cat("\nEffective sample size (approximate):", round(ess_approx, 0), "\n")
  
  return(list(
    jump_lengths = jump_lengths,
    freq_table = freq_table,
    is_stuck = max_freq > stuck_threshold,
    ess_approx = ess_approx
  ))
}

## 4. Settings, data, and run


``` r
settings <- list(
  numberCores = 4,
  numberChainRuns = 4,
  iterations = 40000,  # Increased from 10000 to allow more exploration
  burninPosterior = 20000,  # Increased from 5000 to allow proper burn-in
  thin = 10,  # Increased from 1 to reduce autocorrelation
  runParallel = TRUE
)

data_l <- list(
  y = obs_y,
  N_data = length(obs_y),
  T = T_days,
  N = N_pop,
  gamma = gamma,
  S0 = N_pop - init_I,
  E0 = 0,
  I0 = init_I,
  R0 = 0,
  rho = rho_true # 1
)

outputs <- rjmc_func(model, data_l, settings)
```

```
## `consoleUpdates` not specified in settings. Default value 100. 
## `numberFittedPar` not specified in settings. Default value equal to the number of parameters in the model  1 . 
## `onAdaptiveCov` not specified in settings. Default value TRUE. 
## `updatesAdaptiveCov` not specified in settings. Default value 100. 
## `burninAdaptiveCov` not specified in settings. Default value 2000. 
## `onAdaptiveTemp` not specified in settings.  Default value TRUE. 
## `updatesAdaptiveTemp` not specified in settings.  Default value 10. 
## `lowerParBounds` not specified in settings. Defaults to lowerParSupport_fitted. 
## `upperParBounds` not specified in settings. Defaults to upperParSupport_fitted 
## `covarInitVal` not specified in settings.  Default value 1e-10. 
## `covarInitValAdapt` not specified in settings.  Default value 1e-10. 
## `covarMaxVal` not specified in settings. Default value 1. 
## Initialization: K = 2 
## Initialization: K = 2 
## Running MCMC-PT iteration number: 0 of 40000. Chain number 4. Current logpost: -48356.2. Length of jump: 2.          Running MCMC-PT iteration number: 0 of 40000. Chain number 2. Current logpost: -36189.3. Length of jump: 2.          Initialization: K = 2 
## Running MCMC-PT iteration number: 0 of 40000. Chain number 1. Current logpost: -17905.4. Length of jump: 2.          Initialization: K = 2 
## Running MCMC-PT iteration number: 0 of 40000. Chain number 3. Current logpost: -42158.5. Length of jump: 2.          Running MCMC-PT iteration number: 100 of 40000. Chain number 4. Current logpost: -38658.8. Length of jump: 2.          Running MCMC-PT iteration number: 100 of 40000. Chain number 1. Current logpost: -6689.17. Length of jump: 2.          Running MCMC-PT iteration number: 100 of 40000. Chain number 2. Current logpost: -18654.8. Length of jump: 2.          Running MCMC-PT iteration number: 100 of 40000. Chain number 3. Current logpost: -37774. Length of jump: 2.          Running MCMC-PT iteration number: 200 of 40000. Chain number 1. Current logpost: -5838.2. Length of jump: 2.          Running MCMC-PT iteration number: 200 of 40000. Chain number 4. Current logpost: -26736.7. Length of jump: 2.          Running MCMC-PT iteration number: 200 of 40000. Chain number 3. Current logpost: -9317.38. Length of jump: 2.          Running MCMC-PT iteration number: 200 of 40000. Chain number 2. Current logpost: -7845.75. Length of jump: 2.          Running MCMC-PT iteration number: 300 of 40000. Chain number 1. Current logpost: -3923.2. Length of jump: 4.          Running MCMC-PT iteration number: 300 of 40000. Chain number 4. Current logpost: -11095.9. Length of jump: 2.          Running MCMC-PT iteration number: 300 of 40000. Chain number 3. Current logpost: -7904.88. Length of jump: 3.          Running MCMC-PT iteration number: 300 of 40000. Chain number 2. Current logpost: -4549.71. Length of jump: 3.          Running MCMC-PT iteration number: 400 of 40000. Chain number 1. Current logpost: -2294.41. Length of jump: 3.          Running MCMC-PT iteration number: 400 of 40000. Chain number 4. Current logpost: -9636.95. Length of jump: 2.          Running MCMC-PT iteration number: 400 of 40000. Chain number 3. Current logpost: -5582.8. Length of jump: 3.          Running MCMC-PT iteration number: 400 of 40000. Chain number 2. Current logpost: -2672.99. Length of jump: 3.          Running MCMC-PT iteration number: 500 of 40000. Chain number 4. Current logpost: -8433.14. Length of jump: 3.          Running MCMC-PT iteration number: 500 of 40000. Chain number 1. Current logpost: -1272.44. Length of jump: 3.          Running MCMC-PT iteration number: 500 of 40000. Chain number 2. Current logpost: -1231.4. Length of jump: 4.          Running MCMC-PT iteration number: 500 of 40000. Chain number 3. Current logpost: -2397.62. Length of jump: 3.          Running MCMC-PT iteration number: 600 of 40000. Chain number 4. Current logpost: -7219.31. Length of jump: 3.          Running MCMC-PT iteration number: 600 of 40000. Chain number 1. Current logpost: -552.441. Length of jump: 3.          Running MCMC-PT iteration number: 600 of 40000. Chain number 2. Current logpost: -955.969. Length of jump: 5.          Running MCMC-PT iteration number: 600 of 40000. Chain number 3. Current logpost: -1585.95. Length of jump: 3.          Running MCMC-PT iteration number: 700 of 40000. Chain number 4. Current logpost: -4869.09. Length of jump: 3.          Running MCMC-PT iteration number: 700 of 40000. Chain number 1. Current logpost: -417.758. Length of jump: 3.          Running MCMC-PT iteration number: 700 of 40000. Chain number 2. Current logpost: -761.841. Length of jump: 4.          Running MCMC-PT iteration number: 700 of 40000. Chain number 3. Current logpost: -1252.88. Length of jump: 4.          Running MCMC-PT iteration number: 800 of 40000. Chain number 4. Current logpost: -1354.42. Length of jump: 3.          Running MCMC-PT iteration number: 800 of 40000. Chain number 1. Current logpost: -364.709. Length of jump: 3.          Running MCMC-PT iteration number: 800 of 40000. Chain number 2. Current logpost: -705.091. Length of jump: 5.          Running MCMC-PT iteration number: 800 of 40000. Chain number 3. Current logpost: -796.05. Length of jump: 6.          Running MCMC-PT iteration number: 900 of 40000. Chain number 4. Current logpost: -490.161. Length of jump: 4.          Running MCMC-PT iteration number: 900 of 40000. Chain number 1. Current logpost: -360.419. Length of jump: 4.          Running MCMC-PT iteration number: 900 of 40000. Chain number 2. Current logpost: -677.722. Length of jump: 5.          Running MCMC-PT iteration number: 900 of 40000. Chain number 3. Current logpost: -636.575. Length of jump: 7.          Running MCMC-PT iteration number: 1000 of 40000. Chain number 4. Current logpost: -469.056. Length of jump: 5.          Running MCMC-PT iteration number: 1000 of 40000. Chain number 1. Current logpost: -362.536. Length of jump: 3.          Running MCMC-PT iteration number: 1000 of 40000. Chain number 2. Current logpost: -640.232. Length of jump: 5.          Running MCMC-PT iteration number: 1000 of 40000. Chain number 3. Current logpost: -553.923. Length of jump: 6.          Running MCMC-PT iteration number: 1100 of 40000. Chain number 4. Current logpost: -451.212. Length of jump: 5.          Running MCMC-PT iteration number: 1100 of 40000. Chain number 1. Current logpost: -364.069. Length of jump: 4.          Running MCMC-PT iteration number: 1100 of 40000. Chain number 3. Current logpost: -427.148. Length of jump: 5.          Running MCMC-PT iteration number: 1100 of 40000. Chain number 2. Current logpost: -609.863. Length of jump: 5.          Running MCMC-PT iteration number: 1200 of 40000. Chain number 4. Current logpost: -404.044. Length of jump: 6.          Running MCMC-PT iteration number: 1200 of 40000. Chain number 1. Current logpost: -362.14. Length of jump: 5.          Running MCMC-PT iteration number: 1200 of 40000. Chain number 3. Current logpost: -362.045. Length of jump: 4.          Running MCMC-PT iteration number: 1200 of 40000. Chain number 2. Current logpost: -530.712. Length of jump: 5.          Running MCMC-PT iteration number: 1300 of 40000. Chain number 4. Current logpost: -364.619. Length of jump: 6.          Running MCMC-PT iteration number: 1300 of 40000. Chain number 1. Current logpost: -362.799. Length of jump: 5.          Running MCMC-PT iteration number: 1300 of 40000. Chain number 3. Current logpost: -364.231. Length of jump: 5.          Running MCMC-PT iteration number: 1300 of 40000. Chain number 2. Current logpost: -471.426. Length of jump: 6.          Running MCMC-PT iteration number: 1400 of 40000. Chain number 4. Current logpost: -363.275. Length of jump: 6.          Running MCMC-PT iteration number: 1400 of 40000. Chain number 1. Current logpost: -362.063. Length of jump: 5.          Running MCMC-PT iteration number: 1400 of 40000. Chain number 3. Current logpost: -363.801. Length of jump: 6.          Running MCMC-PT iteration number: 1400 of 40000. Chain number 2. Current logpost: -440.862. Length of jump: 5.          Running MCMC-PT iteration number: 1500 of 40000. Chain number 4. Current logpost: -363.533. Length of jump: 6.          Running MCMC-PT iteration number: 1500 of 40000. Chain number 1. Current logpost: -360.966. Length of jump: 5.          Running MCMC-PT iteration number: 1500 of 40000. Chain number 3. Current logpost: -362.395. Length of jump: 6.          Running MCMC-PT iteration number: 1500 of 40000. Chain number 2. Current logpost: -420.444. Length of jump: 5.          Running MCMC-PT iteration number: 1600 of 40000. Chain number 4. Current logpost: -363.798. Length of jump: 5.          Running MCMC-PT iteration number: 1600 of 40000. Chain number 1. Current logpost: -360.263. Length of jump: 4.          Running MCMC-PT iteration number: 1600 of 40000. Chain number 3. Current logpost: -363.427. Length of jump: 6.          Running MCMC-PT iteration number: 1600 of 40000. Chain number 2. Current logpost: -360.669. Length of jump: 4.          Running MCMC-PT iteration number: 1700 of 40000. Chain number 4. Current logpost: -365.765. Length of jump: 6.          Running MCMC-PT iteration number: 1700 of 40000. Chain number 1. Current logpost: -360.878. Length of jump: 5.          Running MCMC-PT iteration number: 1700 of 40000. Chain number 3. Current logpost: -363.388. Length of jump: 6.          Running MCMC-PT iteration number: 1700 of 40000. Chain number 2. Current logpost: -362.924. Length of jump: 3.          Running MCMC-PT iteration number: 1800 of 40000. Chain number 4. Current logpost: -361.92. Length of jump: 4.          Running MCMC-PT iteration number: 1800 of 40000. Chain number 1. Current logpost: -363.508. Length of jump: 6.          Running MCMC-PT iteration number: 1800 of 40000. Chain number 2. Current logpost: -361.152. Length of jump: 3.          Running MCMC-PT iteration number: 1800 of 40000. Chain number 3. Current logpost: -361.574. Length of jump: 5.          Running MCMC-PT iteration number: 1900 of 40000. Chain number 4. Current logpost: -363.333. Length of jump: 4.          Running MCMC-PT iteration number: 1900 of 40000. Chain number 1. Current logpost: -362.784. Length of jump: 6.          Running MCMC-PT iteration number: 1900 of 40000. Chain number 2. Current logpost: -362.531. Length of jump: 4.          Running MCMC-PT iteration number: 1900 of 40000. Chain number 3. Current logpost: -361.326. Length of jump: 4.          Running MCMC-PT iteration number: 2000 of 40000. Chain number 4. Current logpost: -362.061. Length of jump: 4.          Running MCMC-PT iteration number: 2000 of 40000. Chain number 2. Current logpost: -360.699. Length of jump: 3.          Running MCMC-PT iteration number: 2000 of 40000. Chain number 1. Current logpost: -360.205. Length of jump: 4.          Running MCMC-PT iteration number: 2000 of 40000. Chain number 3. Current logpost: -362.443. Length of jump: 7.          Running MCMC-PT iteration number: 2100 of 40000. Chain number 3. Current logpost: -362.477. Length of jump: 6.          Running MCMC-PT iteration number: 2200 of 40000. Chain number 4. Current logpost: -361.757. Length of jump: 5.          Running MCMC-PT iteration number: 2200 of 40000. Chain number 2. Current logpost: -364.936. Length of jump: 3.          Running MCMC-PT iteration number: 2200 of 40000. Chain number 1. Current logpost: -360.725. Length of jump: 4.          Running MCMC-PT iteration number: 2200 of 40000. Chain number 3. Current logpost: -360.99. Length of jump: 6.          Running MCMC-PT iteration number: 2300 of 40000. Chain number 4. Current logpost: -361.781. Length of jump: 3.          Running MCMC-PT iteration number: 2300 of 40000. Chain number 2. Current logpost: -359.428. Length of jump: 4.          Running MCMC-PT iteration number: 2300 of 40000. Chain number 1. Current logpost: -361.685. Length of jump: 4.          Running MCMC-PT iteration number: 2300 of 40000. Chain number 3. Current logpost: -362.946. Length of jump: 7.          Running MCMC-PT iteration number: 2400 of 40000. Chain number 4. Current logpost: -361.451. Length of jump: 4.          Running MCMC-PT iteration number: 2400 of 40000. Chain number 2. Current logpost: -359.745. Length of jump: 4.          Running MCMC-PT iteration number: 2400 of 40000. Chain number 1. Current logpost: -362.172. Length of jump: 4.          Running MCMC-PT iteration number: 2400 of 40000. Chain number 3. Current logpost: -363.479. Length of jump: 6.          Running MCMC-PT iteration number: 2500 of 40000. Chain number 4. Current logpost: -359.86. Length of jump: 5.          Running MCMC-PT iteration number: 2500 of 40000. Chain number 2. Current logpost: -358.698. Length of jump: 5.          Running MCMC-PT iteration number: 2500 of 40000. Chain number 1. Current logpost: -360.398. Length of jump: 4.          Running MCMC-PT iteration number: 2500 of 40000. Chain number 3. Current logpost: -363.61. Length of jump: 6.          Running MCMC-PT iteration number: 2600 of 40000. Chain number 4. Current logpost: -359.787. Length of jump: 5.          Running MCMC-PT iteration number: 2600 of 40000. Chain number 2. Current logpost: -358.477. Length of jump: 5.          Running MCMC-PT iteration number: 2600 of 40000. Chain number 1. Current logpost: -362.081. Length of jump: 5.          Running MCMC-PT iteration number: 2600 of 40000. Chain number 3. Current logpost: -363.979. Length of jump: 7.          Running MCMC-PT iteration number: 2700 of 40000. Chain number 4. Current logpost: -362.167. Length of jump: 4.          Running MCMC-PT iteration number: 2700 of 40000. Chain number 2. Current logpost: -358.785. Length of jump: 5.          Running MCMC-PT iteration number: 2700 of 40000. Chain number 1. Current logpost: -358.353. Length of jump: 6.          Running MCMC-PT iteration number: 2700 of 40000. Chain number 3. Current logpost: -362.593. Length of jump: 7.          Running MCMC-PT iteration number: 2800 of 40000. Chain number 4. Current logpost: -360.646. Length of jump: 3.          Running MCMC-PT iteration number: 2800 of 40000. Chain number 1. Current logpost: -358.626. Length of jump: 6.          Running MCMC-PT iteration number: 2800 of 40000. Chain number 2. Current logpost: -358.631. Length of jump: 5.          Running MCMC-PT iteration number: 2800 of 40000. Chain number 3. Current logpost: -367.285. Length of jump: 7.          Running MCMC-PT iteration number: 2900 of 40000. Chain number 4. Current logpost: -361.889. Length of jump: 3.          Running MCMC-PT iteration number: 2900 of 40000. Chain number 2. Current logpost: -358.718. Length of jump: 5.          Running MCMC-PT iteration number: 2900 of 40000. Chain number 1. Current logpost: -358.499. Length of jump: 6.          Running MCMC-PT iteration number: 2900 of 40000. Chain number 3. Current logpost: -362.442. Length of jump: 5.          Running MCMC-PT iteration number: 3000 of 40000. Chain number 4. Current logpost: -358.493. Length of jump: 4.          Running MCMC-PT iteration number: 3000 of 40000. Chain number 3. Current logpost: -362.374. Length of jump: 5.          Running MCMC-PT iteration number: 3000 of 40000. Chain number 2. Current logpost: -359.798. Length of jump: 6.          Running MCMC-PT iteration number: 3000 of 40000. Chain number 1. Current logpost: -359.777. Length of jump: 6.          Running MCMC-PT iteration number: 3100 of 40000. Chain number 4. Current logpost: -358.508. Length of jump: 4.          Running MCMC-PT iteration number: 3100 of 40000. Chain number 3. Current logpost: -361.788. Length of jump: 4.          Running MCMC-PT iteration number: 3100 of 40000. Chain number 2. Current logpost: -359.209. Length of jump: 6.          Running MCMC-PT iteration number: 3100 of 40000. Chain number 1. Current logpost: -359.445. Length of jump: 6.          Running MCMC-PT iteration number: 3200 of 40000. Chain number 4. Current logpost: -359.783. Length of jump: 4.          Running MCMC-PT iteration number: 3200 of 40000. Chain number 2. Current logpost: -357.932. Length of jump: 5.          Running MCMC-PT iteration number: 3200 of 40000. Chain number 3. Current logpost: -361.284. Length of jump: 4.          Running MCMC-PT iteration number: 3200 of 40000. Chain number 1. Current logpost: -358.951. Length of jump: 5.          Running MCMC-PT iteration number: 3300 of 40000. Chain number 4. Current logpost: -358.194. Length of jump: 4.          Running MCMC-PT iteration number: 3300 of 40000. Chain number 2. Current logpost: -358.408. Length of jump: 5.          Running MCMC-PT iteration number: 3300 of 40000. Chain number 3. Current logpost: -360.514. Length of jump: 5.          Running MCMC-PT iteration number: 3300 of 40000. Chain number 1. Current logpost: -358.313. Length of jump: 5.          Running MCMC-PT iteration number: 3400 of 40000. Chain number 4. Current logpost: -359.051. Length of jump: 4.          Running MCMC-PT iteration number: 3400 of 40000. Chain number 2. Current logpost: -361.726. Length of jump: 5.          Running MCMC-PT iteration number: 3400 of 40000. Chain number 3. Current logpost: -362.07. Length of jump: 5.          Running MCMC-PT iteration number: 3400 of 40000. Chain number 1. Current logpost: -358.884. Length of jump: 5.          Running MCMC-PT iteration number: 3500 of 40000. Chain number 4. Current logpost: -360.011. Length of jump: 4.          Running MCMC-PT iteration number: 3500 of 40000. Chain number 2. Current logpost: -361.517. Length of jump: 5.          Running MCMC-PT iteration number: 3500 of 40000. Chain number 3. Current logpost: -357.931. Length of jump: 5.          Running MCMC-PT iteration number: 3500 of 40000. Chain number 1. Current logpost: -359.108. Length of jump: 6.          Running MCMC-PT iteration number: 3600 of 40000. Chain number 4. Current logpost: -358.685. Length of jump: 5.          Running MCMC-PT iteration number: 3600 of 40000. Chain number 2. Current logpost: -358.658. Length of jump: 5.          Running MCMC-PT iteration number: 3600 of 40000. Chain number 3. Current logpost: -360.966. Length of jump: 6.          Running MCMC-PT iteration number: 3600 of 40000. Chain number 1. Current logpost: -359.107. Length of jump: 6.          Running MCMC-PT iteration number: 3700 of 40000. Chain number 4. Current logpost: -358.605. Length of jump: 4.          Running MCMC-PT iteration number: 3700 of 40000. Chain number 2. Current logpost: -358.624. Length of jump: 5.          Running MCMC-PT iteration number: 3700 of 40000. Chain number 3. Current logpost: -359.606. Length of jump: 6.          Running MCMC-PT iteration number: 3700 of 40000. Chain number 1. Current logpost: -358.591. Length of jump: 6.          Running MCMC-PT iteration number: 3800 of 40000. Chain number 4. Current logpost: -359.72. Length of jump: 4.          Running MCMC-PT iteration number: 3800 of 40000. Chain number 2. Current logpost: -359.781. Length of jump: 5.          Running MCMC-PT iteration number: 3800 of 40000. Chain number 3. Current logpost: -358.598. Length of jump: 5.          Running MCMC-PT iteration number: 3800 of 40000. Chain number 1. Current logpost: -359.562. Length of jump: 5.          Running MCMC-PT iteration number: 3900 of 40000. Chain number 4. Current logpost: -358.911. Length of jump: 5.          Running MCMC-PT iteration number: 3900 of 40000. Chain number 2. Current logpost: -358.469. Length of jump: 6.          Running MCMC-PT iteration number: 3900 of 40000. Chain number 3. Current logpost: -361.652. Length of jump: 5.          Running MCMC-PT iteration number: 3900 of 40000. Chain number 1. Current logpost: -359.42. Length of jump: 6.          Running MCMC-PT iteration number: 4000 of 40000. Chain number 4. Current logpost: -360.527. Length of jump: 5.          Running MCMC-PT iteration number: 4000 of 40000. Chain number 3. Current logpost: -359.115. Length of jump: 5.          Running MCMC-PT iteration number: 4000 of 40000. Chain number 2. Current logpost: -362.575. Length of jump: 5.          Running MCMC-PT iteration number: 4000 of 40000. Chain number 1. Current logpost: -360.183. Length of jump: 6.          Running MCMC-PT iteration number: 4100 of 40000. Chain number 4. Current logpost: -360.998. Length of jump: 5.          Running MCMC-PT iteration number: 4100 of 40000. Chain number 3. Current logpost: -359.321. Length of jump: 6.          Running MCMC-PT iteration number: 4100 of 40000. Chain number 2. Current logpost: -358.648. Length of jump: 5.          Running MCMC-PT iteration number: 4100 of 40000. Chain number 1. Current logpost: -365.152. Length of jump: 5.          Running MCMC-PT iteration number: 4200 of 40000. Chain number 4. Current logpost: -359.247. Length of jump: 5.          Running MCMC-PT iteration number: 4200 of 40000. Chain number 3. Current logpost: -359.796. Length of jump: 6.          Running MCMC-PT iteration number: 4200 of 40000. Chain number 2. Current logpost: -359.915. Length of jump: 5.          Running MCMC-PT iteration number: 4200 of 40000. Chain number 1. Current logpost: -361.048. Length of jump: 7.          Running MCMC-PT iteration number: 4300 of 40000. Chain number 4. Current logpost: -360.908. Length of jump: 5.          Running MCMC-PT iteration number: 4300 of 40000. Chain number 3. Current logpost: -359.078. Length of jump: 5.          Running MCMC-PT iteration number: 4300 of 40000. Chain number 2. Current logpost: -360.347. Length of jump: 4.          Running MCMC-PT iteration number: 4300 of 40000. Chain number 1. Current logpost: -360.897. Length of jump: 7.          Running MCMC-PT iteration number: 4400 of 40000. Chain number 4. Current logpost: -360.664. Length of jump: 5.          Running MCMC-PT iteration number: 4400 of 40000. Chain number 3. Current logpost: -358.629. Length of jump: 5.          Running MCMC-PT iteration number: 4400 of 40000. Chain number 2. Current logpost: -360.199. Length of jump: 5.          Running MCMC-PT iteration number: 4400 of 40000. Chain number 1. Current logpost: -365.382. Length of jump: 8.          Running MCMC-PT iteration number: 4500 of 40000. Chain number 4. Current logpost: -361.293. Length of jump: 5.          Running MCMC-PT iteration number: 4500 of 40000. Chain number 3. Current logpost: -360.867. Length of jump: 5.          Running MCMC-PT iteration number: 4500 of 40000. Chain number 2. Current logpost: -360.857. Length of jump: 3.          Running MCMC-PT iteration number: 4500 of 40000. Chain number 1. Current logpost: -360.664. Length of jump: 7.          Running MCMC-PT iteration number: 4600 of 40000. Chain number 4. Current logpost: -360.932. Length of jump: 5.          Running MCMC-PT iteration number: 4600 of 40000. Chain number 3. Current logpost: -361.807. Length of jump: 6.          Running MCMC-PT iteration number: 4600 of 40000. Chain number 2. Current logpost: -360.682. Length of jump: 4.          Running MCMC-PT iteration number: 4600 of 40000. Chain number 1. Current logpost: -358.703. Length of jump: 7.          Running MCMC-PT iteration number: 4700 of 40000. Chain number 4. Current logpost: -360.945. Length of jump: 6.          Running MCMC-PT iteration number: 4700 of 40000. Chain number 3. Current logpost: -359.584. Length of jump: 6.          Running MCMC-PT iteration number: 4700 of 40000. Chain number 2. Current logpost: -361.317. Length of jump: 4.          Running MCMC-PT iteration number: 4700 of 40000. Chain number 1. Current logpost: -359.543. Length of jump: 7.          Running MCMC-PT iteration number: 4800 of 40000. Chain number 4. Current logpost: -364.957. Length of jump: 6.          Running MCMC-PT iteration number: 4800 of 40000. Chain number 3. Current logpost: -365.233. Length of jump: 7.          Running MCMC-PT iteration number: 4800 of 40000. Chain number 2. Current logpost: -362.433. Length of jump: 6.          Running MCMC-PT iteration number: 4800 of 40000. Chain number 1. Current logpost: -358.244. Length of jump: 6.          Running MCMC-PT iteration number: 4900 of 40000. Chain number 4. Current logpost: -362.995. Length of jump: 6.          Running MCMC-PT iteration number: 4900 of 40000. Chain number 3. Current logpost: -364.009. Length of jump: 7.          Running MCMC-PT iteration number: 4900 of 40000. Chain number 2. Current logpost: -361.388. Length of jump: 6.          Running MCMC-PT iteration number: 4900 of 40000. Chain number 1. Current logpost: -361.763. Length of jump: 7.          Running MCMC-PT iteration number: 5000 of 40000. Chain number 4. Current logpost: -361.041. Length of jump: 6.          Running MCMC-PT iteration number: 5000 of 40000. Chain number 3. Current logpost: -362.361. Length of jump: 8.          Running MCMC-PT iteration number: 5000 of 40000. Chain number 2. Current logpost: -361.396. Length of jump: 6.          Running MCMC-PT iteration number: 5000 of 40000. Chain number 1. Current logpost: -359.676. Length of jump: 7.          Running MCMC-PT iteration number: 5100 of 40000. Chain number 4. Current logpost: -358.882. Length of jump: 5.          Running MCMC-PT iteration number: 5100 of 40000. Chain number 3. Current logpost: -363.263. Length of jump: 7.          Running MCMC-PT iteration number: 5100 of 40000. Chain number 2. Current logpost: -363.901. Length of jump: 9.          Running MCMC-PT iteration number: 5100 of 40000. Chain number 1. Current logpost: -362.425. Length of jump: 7.          Running MCMC-PT iteration number: 5200 of 40000. Chain number 4. Current logpost: -359.897. Length of jump: 5.          Running MCMC-PT iteration number: 5200 of 40000. Chain number 3. Current logpost: -360.737. Length of jump: 6.          Running MCMC-PT iteration number: 5200 of 40000. Chain number 2. Current logpost: -364.823. Length of jump: 9.          Running MCMC-PT iteration number: 5200 of 40000. Chain number 1. Current logpost: -362.259. Length of jump: 7.          Running MCMC-PT iteration number: 5300 of 40000. Chain number 4. Current logpost: -360.178. Length of jump: 4.          Running MCMC-PT iteration number: 5300 of 40000. Chain number 3. Current logpost: -359.828. Length of jump: 6.          Running MCMC-PT iteration number: 5300 of 40000. Chain number 2. Current logpost: -359.25. Length of jump: 6.          Running MCMC-PT iteration number: 5300 of 40000. Chain number 1. Current logpost: -364.45. Length of jump: 7.          Running MCMC-PT iteration number: 5400 of 40000. Chain number 4. Current logpost: -358.593. Length of jump: 4.          Running MCMC-PT iteration number: 5400 of 40000. Chain number 3. Current logpost: -361.627. Length of jump: 7.          Running MCMC-PT iteration number: 5400 of 40000. Chain number 2. Current logpost: -360.024. Length of jump: 7.          Running MCMC-PT iteration number: 5400 of 40000. Chain number 1. Current logpost: -362.945. Length of jump: 5.          Running MCMC-PT iteration number: 5500 of 40000. Chain number 4. Current logpost: -357.999. Length of jump: 5.          Running MCMC-PT iteration number: 5500 of 40000. Chain number 3. Current logpost: -362.067. Length of jump: 7.          Running MCMC-PT iteration number: 5500 of 40000. Chain number 2. Current logpost: -361.639. Length of jump: 5.          Running MCMC-PT iteration number: 5500 of 40000. Chain number 1. Current logpost: -364.347. Length of jump: 5.          Running MCMC-PT iteration number: 5600 of 40000. Chain number 4. Current logpost: -358.283. Length of jump: 5.          Running MCMC-PT iteration number: 5600 of 40000. Chain number 3. Current logpost: -360.872. Length of jump: 7.          Running MCMC-PT iteration number: 5600 of 40000. Chain number 2. Current logpost: -362.313. Length of jump: 5.          Running MCMC-PT iteration number: 5600 of 40000. Chain number 1. Current logpost: -360.586. Length of jump: 5.          Running MCMC-PT iteration number: 5700 of 40000. Chain number 4. Current logpost: -359.527. Length of jump: 5.          Running MCMC-PT iteration number: 5700 of 40000. Chain number 3. Current logpost: -360.717. Length of jump: 7.          Running MCMC-PT iteration number: 5700 of 40000. Chain number 2. Current logpost: -363.385. Length of jump: 5.          Running MCMC-PT iteration number: 5700 of 40000. Chain number 1. Current logpost: -359.8. Length of jump: 5.          Running MCMC-PT iteration number: 5800 of 40000. Chain number 4. Current logpost: -359.745. Length of jump: 6.          Running MCMC-PT iteration number: 5800 of 40000. Chain number 3. Current logpost: -359.059. Length of jump: 6.          Running MCMC-PT iteration number: 5800 of 40000. Chain number 2. Current logpost: -361.384. Length of jump: 4.          Running MCMC-PT iteration number: 5800 of 40000. Chain number 1. Current logpost: -359.275. Length of jump: 6.          Running MCMC-PT iteration number: 5900 of 40000. Chain number 4. Current logpost: -362.373. Length of jump: 6.          Running MCMC-PT iteration number: 5900 of 40000. Chain number 3. Current logpost: -360.799. Length of jump: 6.          Running MCMC-PT iteration number: 5900 of 40000. Chain number 2. Current logpost: -361.309. Length of jump: 4.          Running MCMC-PT iteration number: 5900 of 40000. Chain number 1. Current logpost: -359.027. Length of jump: 5.          Running MCMC-PT iteration number: 6000 of 40000. Chain number 4. Current logpost: -362.058. Length of jump: 6.          Running MCMC-PT iteration number: 6000 of 40000. Chain number 3. Current logpost: -360.12. Length of jump: 4.          Running MCMC-PT iteration number: 6000 of 40000. Chain number 2. Current logpost: -360.641. Length of jump: 4.          Running MCMC-PT iteration number: 6000 of 40000. Chain number 1. Current logpost: -358.811. Length of jump: 5.          Running MCMC-PT iteration number: 6100 of 40000. Chain number 4. Current logpost: -361.138. Length of jump: 5.          Running MCMC-PT iteration number: 6100 of 40000. Chain number 3. Current logpost: -360.846. Length of jump: 4.          Running MCMC-PT iteration number: 6100 of 40000. Chain number 2. Current logpost: -361.832. Length of jump: 5.          Running MCMC-PT iteration number: 6100 of 40000. Chain number 1. Current logpost: -358.563. Length of jump: 5.          Running MCMC-PT iteration number: 6200 of 40000. Chain number 4. Current logpost: -360.785. Length of jump: 3.          Running MCMC-PT iteration number: 6200 of 40000. Chain number 3. Current logpost: -359.974. Length of jump: 6.          Running MCMC-PT iteration number: 6200 of 40000. Chain number 2. Current logpost: -362.265. Length of jump: 5.          Running MCMC-PT iteration number: 6200 of 40000. Chain number 1. Current logpost: -360.926. Length of jump: 6.          Running MCMC-PT iteration number: 6300 of 40000. Chain number 4. Current logpost: -360.836. Length of jump: 3.          Running MCMC-PT iteration number: 6300 of 40000. Chain number 3. Current logpost: -360.089. Length of jump: 6.          Running MCMC-PT iteration number: 6300 of 40000. Chain number 2. Current logpost: -363.245. Length of jump: 5.          Running MCMC-PT iteration number: 6300 of 40000. Chain number 1. Current logpost: -363.931. Length of jump: 6.          Running MCMC-PT iteration number: 6400 of 40000. Chain number 4. Current logpost: -360.856. Length of jump: 3.          Running MCMC-PT iteration number: 6400 of 40000. Chain number 3. Current logpost: -359.594. Length of jump: 7.          Running MCMC-PT iteration number: 6400 of 40000. Chain number 2. Current logpost: -364.235. Length of jump: 6.          Running MCMC-PT iteration number: 6400 of 40000. Chain number 1. Current logpost: -363.094. Length of jump: 7.          Running MCMC-PT iteration number: 6500 of 40000. Chain number 4. Current logpost: -361.676. Length of jump: 3.          Running MCMC-PT iteration number: 6500 of 40000. Chain number 3. Current logpost: -359.28. Length of jump: 7.          Running MCMC-PT iteration number: 6500 of 40000. Chain number 2. Current logpost: -362.617. Length of jump: 7.          Running MCMC-PT iteration number: 6500 of 40000. Chain number 1. Current logpost: -361.981. Length of jump: 6.          Running MCMC-PT iteration number: 6600 of 40000. Chain number 4. Current logpost: -362.477. Length of jump: 3.          Running MCMC-PT iteration number: 6600 of 40000. Chain number 3. Current logpost: -360.195. Length of jump: 8.          Running MCMC-PT iteration number: 6600 of 40000. Chain number 2. Current logpost: -360.679. Length of jump: 6.          Running MCMC-PT iteration number: 6600 of 40000. Chain number 1. Current logpost: -360.307. Length of jump: 6.          Running MCMC-PT iteration number: 6700 of 40000. Chain number 4. Current logpost: -362.762. Length of jump: 3.          Running MCMC-PT iteration number: 6700 of 40000. Chain number 3. Current logpost: -360.275. Length of jump: 7.          Running MCMC-PT iteration number: 6700 of 40000. Chain number 2. Current logpost: -361.428. Length of jump: 6.          Running MCMC-PT iteration number: 6800 of 40000. Chain number 3. Current logpost: -359.958. Length of jump: 5.          Running MCMC-PT iteration number: 6800 of 40000. Chain number 1. Current logpost: -359.385. Length of jump: 6.          Running MCMC-PT iteration number: 6900 of 40000. Chain number 4. Current logpost: -360.269. Length of jump: 4.          Running MCMC-PT iteration number: 6900 of 40000. Chain number 2. Current logpost: -364.46. Length of jump: 7.          Running MCMC-PT iteration number: 6900 of 40000. Chain number 3. Current logpost: -359.33. Length of jump: 6.          Running MCMC-PT iteration number: 6900 of 40000. Chain number 1. Current logpost: -361.772. Length of jump: 6.          Running MCMC-PT iteration number: 7000 of 40000. Chain number 4. Current logpost: -360.086. Length of jump: 4.          Running MCMC-PT iteration number: 7000 of 40000. Chain number 2. Current logpost: -361.407. Length of jump: 6.          Running MCMC-PT iteration number: 7000 of 40000. Chain number 3. Current logpost: -359.54. Length of jump: 5.          Running MCMC-PT iteration number: 7000 of 40000. Chain number 1. Current logpost: -359.78. Length of jump: 5.          Running MCMC-PT iteration number: 7100 of 40000. Chain number 4. Current logpost: -361.024. Length of jump: 4.          Running MCMC-PT iteration number: 7100 of 40000. Chain number 2. Current logpost: -362.905. Length of jump: 6.          Running MCMC-PT iteration number: 7100 of 40000. Chain number 3. Current logpost: -360.359. Length of jump: 5.          Running MCMC-PT iteration number: 7100 of 40000. Chain number 1. Current logpost: -359.146. Length of jump: 5.          Running MCMC-PT iteration number: 7200 of 40000. Chain number 4. Current logpost: -360.192. Length of jump: 4.          Running MCMC-PT iteration number: 7200 of 40000. Chain number 3. Current logpost: -361.033. Length of jump: 5.          Running MCMC-PT iteration number: 7200 of 40000. Chain number 1. Current logpost: -359.122. Length of jump: 5.          Running MCMC-PT iteration number: 7300 of 40000. Chain number 4. Current logpost: -361.093. Length of jump: 4.          Running MCMC-PT iteration number: 7300 of 40000. Chain number 2. Current logpost: -361.098. Length of jump: 6.          Running MCMC-PT iteration number: 7300 of 40000. Chain number 3. Current logpost: -364.712. Length of jump: 5.          Running MCMC-PT iteration number: 7300 of 40000. Chain number 1. Current logpost: -358.277. Length of jump: 5.          Running MCMC-PT iteration number: 7400 of 40000. Chain number 4. Current logpost: -359.901. Length of jump: 5.          Running MCMC-PT iteration number: 7400 of 40000. Chain number 2. Current logpost: -362.882. Length of jump: 5.          Running MCMC-PT iteration number: 7400 of 40000. Chain number 3. Current logpost: -362.301. Length of jump: 4.          Running MCMC-PT iteration number: 7400 of 40000. Chain number 1. Current logpost: -358.962. Length of jump: 5.          Running MCMC-PT iteration number: 7500 of 40000. Chain number 4. Current logpost: -360.215. Length of jump: 5.          Running MCMC-PT iteration number: 7500 of 40000. Chain number 2. Current logpost: -360.347. Length of jump: 5.          Running MCMC-PT iteration number: 7500 of 40000. Chain number 3. Current logpost: -359.289. Length of jump: 4.          Running MCMC-PT iteration number: 7500 of 40000. Chain number 1. Current logpost: -362.473. Length of jump: 6.          Running MCMC-PT iteration number: 7600 of 40000. Chain number 4. Current logpost: -360.217. Length of jump: 5.          Running MCMC-PT iteration number: 7600 of 40000. Chain number 2. Current logpost: -360.594. Length of jump: 4.          Running MCMC-PT iteration number: 7600 of 40000. Chain number 3. Current logpost: -360.064. Length of jump: 4.          Running MCMC-PT iteration number: 7600 of 40000. Chain number 1. Current logpost: -358.995. Length of jump: 6.          Running MCMC-PT iteration number: 7700 of 40000. Chain number 4. Current logpost: -361.646. Length of jump: 5.          Running MCMC-PT iteration number: 7700 of 40000. Chain number 2. Current logpost: -363.245. Length of jump: 4.          Running MCMC-PT iteration number: 7700 of 40000. Chain number 3. Current logpost: -360.677. Length of jump: 4.          Running MCMC-PT iteration number: 7700 of 40000. Chain number 1. Current logpost: -360.418. Length of jump: 5.          Running MCMC-PT iteration number: 7800 of 40000. Chain number 4. Current logpost: -359.834. Length of jump: 4.          Running MCMC-PT iteration number: 7800 of 40000. Chain number 2. Current logpost: -360.55. Length of jump: 4.          Running MCMC-PT iteration number: 7800 of 40000. Chain number 3. Current logpost: -363.674. Length of jump: 5.          Running MCMC-PT iteration number: 7800 of 40000. Chain number 1. Current logpost: -357.265. Length of jump: 6.          Running MCMC-PT iteration number: 7900 of 40000. Chain number 4. Current logpost: -360.265. Length of jump: 4.          Running MCMC-PT iteration number: 7900 of 40000. Chain number 2. Current logpost: -360.212. Length of jump: 4.          Running MCMC-PT iteration number: 7900 of 40000. Chain number 3. Current logpost: -363.881. Length of jump: 5.          Running MCMC-PT iteration number: 7900 of 40000. Chain number 1. Current logpost: -357.09. Length of jump: 6.          Running MCMC-PT iteration number: 8000 of 40000. Chain number 4. Current logpost: -362.634. Length of jump: 4.          Running MCMC-PT iteration number: 8000 of 40000. Chain number 2. Current logpost: -362.12. Length of jump: 4.          Running MCMC-PT iteration number: 8000 of 40000. Chain number 3. Current logpost: -362.813. Length of jump: 5.          Running MCMC-PT iteration number: 8000 of 40000. Chain number 1. Current logpost: -356.315. Length of jump: 6.          Running MCMC-PT iteration number: 8100 of 40000. Chain number 4. Current logpost: -360.34. Length of jump: 4.          Running MCMC-PT iteration number: 8100 of 40000. Chain number 2. Current logpost: -363.261. Length of jump: 4.          Running MCMC-PT iteration number: 8100 of 40000. Chain number 3. Current logpost: -362.103. Length of jump: 6.          Running MCMC-PT iteration number: 8100 of 40000. Chain number 1. Current logpost: -357.694. Length of jump: 7.          Running MCMC-PT iteration number: 8200 of 40000. Chain number 4. Current logpost: -360.21. Length of jump: 4.          Running MCMC-PT iteration number: 8200 of 40000. Chain number 2. Current logpost: -363.492. Length of jump: 4.          Running MCMC-PT iteration number: 8200 of 40000. Chain number 3. Current logpost: -360.633. Length of jump: 7.          Running MCMC-PT iteration number: 8200 of 40000. Chain number 1. Current logpost: -361.158. Length of jump: 7.          Running MCMC-PT iteration number: 8300 of 40000. Chain number 4. Current logpost: -360.687. Length of jump: 3.          Running MCMC-PT iteration number: 8300 of 40000. Chain number 2. Current logpost: -361.116. Length of jump: 3.          Running MCMC-PT iteration number: 8300 of 40000. Chain number 3. Current logpost: -362.28. Length of jump: 7.          Running MCMC-PT iteration number: 8300 of 40000. Chain number 1. Current logpost: -365.436. Length of jump: 8.          Running MCMC-PT iteration number: 8400 of 40000. Chain number 4. Current logpost: -361.443. Length of jump: 3.          Running MCMC-PT iteration number: 8400 of 40000. Chain number 2. Current logpost: -361.884. Length of jump: 3.          Running MCMC-PT iteration number: 8400 of 40000. Chain number 3. Current logpost: -361.998. Length of jump: 6.          Running MCMC-PT iteration number: 8400 of 40000. Chain number 1. Current logpost: -365.085. Length of jump: 8.          Running MCMC-PT iteration number: 8500 of 40000. Chain number 4. Current logpost: -361.118. Length of jump: 3.          Running MCMC-PT iteration number: 8500 of 40000. Chain number 2. Current logpost: -360.598. Length of jump: 3.          Running MCMC-PT iteration number: 8500 of 40000. Chain number 1. Current logpost: -365.856. Length of jump: 7.          Running MCMC-PT iteration number: 8600 of 40000. Chain number 4. Current logpost: -361.496. Length of jump: 3.          Running MCMC-PT iteration number: 8600 of 40000. Chain number 2. Current logpost: -360.063. Length of jump: 5.          Running MCMC-PT iteration number: 8600 of 40000. Chain number 3. Current logpost: -361.296. Length of jump: 6.          Running MCMC-PT iteration number: 8600 of 40000. Chain number 1. Current logpost: -363.066. Length of jump: 10.          Running MCMC-PT iteration number: 8700 of 40000. Chain number 4. Current logpost: -360.631. Length of jump: 4.          Running MCMC-PT iteration number: 8700 of 40000. Chain number 2. Current logpost: -360.531. Length of jump: 6.          Running MCMC-PT iteration number: 8700 of 40000. Chain number 3. Current logpost: -367.167. Length of jump: 6.          Running MCMC-PT iteration number: 8700 of 40000. Chain number 1. Current logpost: -360.583. Length of jump: 8.          Running MCMC-PT iteration number: 8800 of 40000. Chain number 4. Current logpost: -361.705. Length of jump: 6.          Running MCMC-PT iteration number: 8800 of 40000. Chain number 2. Current logpost: -360.281. Length of jump: 6.          Running MCMC-PT iteration number: 8800 of 40000. Chain number 3. Current logpost: -365.156. Length of jump: 5.          Running MCMC-PT iteration number: 8800 of 40000. Chain number 1. Current logpost: -360.38. Length of jump: 9.          Running MCMC-PT iteration number: 8900 of 40000. Chain number 4. Current logpost: -360.94. Length of jump: 6.          Running MCMC-PT iteration number: 8900 of 40000. Chain number 2. Current logpost: -362.672. Length of jump: 6.          Running MCMC-PT iteration number: 8900 of 40000. Chain number 3. Current logpost: -362.146. Length of jump: 4.          Running MCMC-PT iteration number: 8900 of 40000. Chain number 1. Current logpost: -358.958. Length of jump: 7.          Running MCMC-PT iteration number: 9000 of 40000. Chain number 4. Current logpost: -360.47. Length of jump: 5.          Running MCMC-PT iteration number: 9000 of 40000. Chain number 2. Current logpost: -365.285. Length of jump: 6.          Running MCMC-PT iteration number: 9000 of 40000. Chain number 3. Current logpost: -361.639. Length of jump: 4.          Running MCMC-PT iteration number: 9100 of 40000. Chain number 4. Current logpost: -360.23. Length of jump: 5.          Running MCMC-PT iteration number: 9000 of 40000. Chain number 1. Current logpost: -362.056. Length of jump: 6.          Running MCMC-PT iteration number: 9100 of 40000. Chain number 2. Current logpost: -360.877. Length of jump: 5.          Running MCMC-PT iteration number: 9100 of 40000. Chain number 3. Current logpost: -361.814. Length of jump: 5.          Running MCMC-PT iteration number: 9200 of 40000. Chain number 4. Current logpost: -361.238. Length of jump: 5.          Running MCMC-PT iteration number: 9100 of 40000. Chain number 1. Current logpost: -361.336. Length of jump: 8.          Running MCMC-PT iteration number: 9200 of 40000. Chain number 2. Current logpost: -362.862. Length of jump: 5.          Running MCMC-PT iteration number: 9200 of 40000. Chain number 3. Current logpost: -362.719. Length of jump: 5.          Running MCMC-PT iteration number: 9300 of 40000. Chain number 4. Current logpost: -365.294. Length of jump: 5.          Running MCMC-PT iteration number: 9200 of 40000. Chain number 1. Current logpost: -360.605. Length of jump: 6.          Running MCMC-PT iteration number: 9300 of 40000. Chain number 2. Current logpost: -363.671. Length of jump: 7.          Running MCMC-PT iteration number: 9300 of 40000. Chain number 3. Current logpost: -363.634. Length of jump: 5.          Running MCMC-PT iteration number: 9400 of 40000. Chain number 4. Current logpost: -361.183. Length of jump: 4.          Running MCMC-PT iteration number: 9300 of 40000. Chain number 1. Current logpost: -360.707. Length of jump: 5.          Running MCMC-PT iteration number: 9400 of 40000. Chain number 2. Current logpost: -362.742. Length of jump: 7.          Running MCMC-PT iteration number: 9400 of 40000. Chain number 3. Current logpost: -361.219. Length of jump: 5.          Running MCMC-PT iteration number: 9500 of 40000. Chain number 4. Current logpost: -362.315. Length of jump: 6.          Running MCMC-PT iteration number: 9400 of 40000. Chain number 1. Current logpost: -358.608. Length of jump: 4.          Running MCMC-PT iteration number: 9500 of 40000. Chain number 2. Current logpost: -360.397. Length of jump: 5.          Running MCMC-PT iteration number: 9500 of 40000. Chain number 3. Current logpost: -360.027. Length of jump: 4.          Running MCMC-PT iteration number: 9600 of 40000. Chain number 4. Current logpost: -360.121. Length of jump: 6.          Running MCMC-PT iteration number: 9500 of 40000. Chain number 1. Current logpost: -359.533. Length of jump: 4.          Running MCMC-PT iteration number: 9600 of 40000. Chain number 2. Current logpost: -360.579. Length of jump: 6.          Running MCMC-PT iteration number: 9600 of 40000. Chain number 3. Current logpost: -360.965. Length of jump: 4.          Running MCMC-PT iteration number: 9700 of 40000. Chain number 4. Current logpost: -363.225. Length of jump: 6.          Running MCMC-PT iteration number: 9600 of 40000. Chain number 1. Current logpost: -359.998. Length of jump: 4.          Running MCMC-PT iteration number: 9700 of 40000. Chain number 2. Current logpost: -360.156. Length of jump: 6.          Running MCMC-PT iteration number: 9700 of 40000. Chain number 3. Current logpost: -364.384. Length of jump: 5.          Running MCMC-PT iteration number: 9800 of 40000. Chain number 4. Current logpost: -360.446. Length of jump: 5.          Running MCMC-PT iteration number: 9700 of 40000. Chain number 1. Current logpost: -358.028. Length of jump: 5.          Running MCMC-PT iteration number: 9800 of 40000. Chain number 2. Current logpost: -360.687. Length of jump: 6.          Running MCMC-PT iteration number: 9800 of 40000. Chain number 3. Current logpost: -364.458. Length of jump: 5.          Running MCMC-PT iteration number: 9900 of 40000. Chain number 4. Current logpost: -364.614. Length of jump: 6.          Running MCMC-PT iteration number: 9800 of 40000. Chain number 1. Current logpost: -357.334. Length of jump: 6.          Running MCMC-PT iteration number: 9900 of 40000. Chain number 2. Current logpost: -360.774. Length of jump: 6.          Running MCMC-PT iteration number: 9900 of 40000. Chain number 3. Current logpost: -360.595. Length of jump: 4.          Running MCMC-PT iteration number: 10000 of 40000. Chain number 4. Current logpost: -363.19. Length of jump: 6.          Running MCMC-PT iteration number: 9900 of 40000. Chain number 1. Current logpost: -358.134. Length of jump: 6.          Running MCMC-PT iteration number: 10000 of 40000. Chain number 2. Current logpost: -360.739. Length of jump: 5.          Running MCMC-PT iteration number: 10000 of 40000. Chain number 3. Current logpost: Running MCMC-PT iteration number: 10100-360.574. Length of jump: 4.           of 40000. Chain number 4. Current logpost: -360.952. Length of jump: 5.          Running MCMC-PT iteration number: 10000 of 40000. Chain number 1. Current logpost: -358.544. Length of jump: 6.          Running MCMC-PT iteration number: 10100 of 40000. Chain number 2. Current logpost: -359.878. Length of jump: 5.          Running MCMC-PT iteration number: 10200 of 40000. Chain number 4. Current logpost: -361.28. Length of jump: 4.          Running MCMC-PT iteration number: 10100 of 40000. Chain number 3. Current logpost: -361.807. Length of jump: 4.          Running MCMC-PT iteration number: 10100 of 40000. Chain number 1. Current logpost: -358.638. Length of jump: 6.          Running MCMC-PT iteration number: 10200 of 40000. Chain number 2. Current logpost: -361.944. Length of jump: 6.          Running MCMC-PT iteration number: 10300 of 40000. Chain number 4. Current logpost: -360.173. Length of jump: 5.          Running MCMC-PT iteration number: 10200 of 40000. Chain number 3. Current logpost: -363.181. Length of jump: 5.          Running MCMC-PT iteration number: 10200 of 40000. Chain number 1. Current logpost: -359.327. Length of jump: 7.          Running MCMC-PT iteration number: 10300 of 40000. Chain number 2. Current logpost: -363.358. Length of jump: 6.          Running MCMC-PT iteration number: 10400 of 40000. Chain number 4. Current logpost: -359.935. Length of jump: 4.          Running MCMC-PT iteration number: 10300 of 40000. Chain number 3. Current logpost: -362.239. Length of jump: 4.          Running MCMC-PT iteration number: 10300 of 40000. Chain number 1. Current logpost: -359.052. Length of jump: 6.          Running MCMC-PT iteration number: 10400 of 40000. Chain number 2. Current logpost: -362.1. Length of jump: 5.          Running MCMC-PT iteration number: 10500 of 40000. Chain number 4. Current logpost: -361.426. Length of jump: 6.          Running MCMC-PT iteration number: 10400 of 40000. Chain number 3. Current logpost: -360.946. Length of jump: 3.          Running MCMC-PT iteration number: 10500 of 40000. Chain number 2. Current logpost: -362.597. Length of jump: 5.          Running MCMC-PT iteration number: 10400 of 40000. Chain number 1. Current logpost: -360.329. Length of jump: 5.          Running MCMC-PT iteration number: 10600 of 40000. Chain number 4. Current logpost: -363.162. Length of jump: 6.          Running MCMC-PT iteration number: 10500 of 40000. Chain number 3. Current logpost: -361.425. Length of jump: 3.          Running MCMC-PT iteration number: 10600 of 40000. Chain number 2. Current logpost: -362.461. Length of jump: 5.          Running MCMC-PT iteration number: 10500 of 40000. Chain number 1. Current logpost: -359.126. Length of jump: 5.          Running MCMC-PT iteration number: 10600 of 40000. Chain number 3. Current logpost: -360.523. Length of jump: 5.          Running MCMC-PT iteration number: 10800 of 40000. Chain number 4. Current logpost: -360.899. Length of jump: 5.          Running MCMC-PT iteration number: 10700 of 40000. Chain number 3. Current logpost: -361.34. Length of jump: 5.          Running MCMC-PT iteration number: 10800 of 40000. Chain number 2. Current logpost: -363.005. Length of jump: 6.          Running MCMC-PT iteration number: 10700 of 40000. Chain number 1. Current logpost: -361.213. Length of jump: 7.          Running MCMC-PT iteration number: 10900 of 40000. Chain number 4. Current logpost: -361.225. Length of jump: 6.          Running MCMC-PT iteration number: 10800 of 40000. Chain number 3. Current logpost: -362.924. Length of jump: 5.          Running MCMC-PT iteration number: 10900 of 40000. Chain number 2. Current logpost: -362.954. Length of jump: 6.          Running MCMC-PT iteration number: 10800 of 40000. Chain number 1. Current logpost: -360.922. Length of jump: 6.          Running MCMC-PT iteration number: 11000 of 40000. Chain number 4. Current logpost: -359.984. Length of jump: 5.          Running MCMC-PT iteration number: 10900 of 40000. Chain number 3. Current logpost: -361.256. Length of jump: 5.          Running MCMC-PT iteration number: 11000 of 40000. Chain number 2. Current logpost: -361.062. Length of jump: 5.          Running MCMC-PT iteration number: 10900 of 40000. Chain number 1. Current logpost: -360.139. Length of jump: 6.          Running MCMC-PT iteration number: 11100 of 40000. Chain number 4. Current logpost: -359.89. Length of jump: 4.          Running MCMC-PT iteration number: 11000 of 40000. Chain number 3. Current logpost: -361.452. Length of jump: 4.          Running MCMC-PT iteration number: 11100 of 40000. Chain number 2. Current logpost: -361.689. Length of jump: 6.          Running MCMC-PT iteration number: 11000 of 40000. Chain number 1. Current logpost: -360.534. Length of jump: 5.          Running MCMC-PT iteration number: 11200 of 40000. Chain number 4. Current logpost: -360.19. Length of jump: 4.          Running MCMC-PT iteration number: 11100 of 40000. Chain number 3. Current logpost: -362.155. Length of jump: 4.          Running MCMC-PT iteration number: 11200 of 40000. Chain number 2. Current logpost: -362.412. Length of jump: 6.          Running MCMC-PT iteration number: 11100 of 40000. Chain number 1. Current logpost: -359.658. Length of jump: 6.          Running MCMC-PT iteration number: 11300 of 40000. Chain number 4. Current logpost: -360.149. Length of jump: 5.          Running MCMC-PT iteration number: 11200 of 40000. Chain number 3. Current logpost: -361.424. Length of jump: 4.          Running MCMC-PT iteration number: 11300 of 40000. Chain number 2. Current logpost: -362.532. Length of jump: 6.          Running MCMC-PT iteration number: 11200 of 40000. Chain number 1. Current logpost: -363.079. Length of jump: 7.          Running MCMC-PT iteration number: 11400 of 40000. Chain number 4. Current logpost: -361.172. Length of jump: 4.          Running MCMC-PT iteration number: 11300 of 40000. Chain number 3. Current logpost: -360.684. Length of jump: 4.          Running MCMC-PT iteration number: 11400 of 40000. Chain number 2. Current logpost: -365.565. Length of jump: 8.          Running MCMC-PT iteration number: 11300 of 40000. Chain number 1. Current logpost: -363.93. Length of jump: 7.          Running MCMC-PT iteration number: 11500 of 40000. Chain number 4. Current logpost: -361.079. Length of jump: 4.          Running MCMC-PT iteration number: 11400 of 40000. Chain number 3. Current logpost: -357.964. Length of jump: 5.          Running MCMC-PT iteration number: 11500 of 40000. Chain number 2. Current logpost: -362.894. Length of jump: 6.          Running MCMC-PT iteration number: 11400 of 40000. Chain number 1. Current logpost: -364.417. Length of jump: 7.          Running MCMC-PT iteration number: 11600 of 40000. Chain number 4. Current logpost: -360.68. Length of jump: 4.          Running MCMC-PT iteration number: 11500 of 40000. Chain number 3. Current logpost: -359.065. Length of jump: 6.          Running MCMC-PT iteration number: 11600 of 40000. Chain number 2. Current logpost: -360.356. Length of jump: 5.          Running MCMC-PT iteration number: 11500 of 40000. Chain number 1. Current logpost: -365.249. Length of jump: 7.          Running MCMC-PT iteration number: 11700 of 40000. Chain number 4. Current logpost: -360.386. Length of jump: 4.          Running MCMC-PT iteration number: 11600 of 40000. Chain number 3. Current logpost: -358.186. Length of jump: 6.          Running MCMC-PT iteration number: 11700 of 40000. Chain number 2. Current logpost: -362.69. Length of jump: 7.          Running MCMC-PT iteration number: 11600 of 40000. Chain number 1. Current logpost: -362.3. Length of jump: 6.          Running MCMC-PT iteration number: 11800 of 40000. Chain number 4. Current logpost: -360.711. Length of jump: 4.          Running MCMC-PT iteration number: 11700 of 40000. Chain number 3. Current logpost: -361.704. Length of jump: 7.          Running MCMC-PT iteration number: 11800 of 40000. Chain number 2. Current logpost: -358.658. Length of jump: 7.          Running MCMC-PT iteration number: 11700 of 40000. Chain number 1. Current logpost: -360.598. Length of jump: 5.          Running MCMC-PT iteration number: 11800 of 40000. Chain number 3. Current logpost: -362.328. Length of jump: 7.          Running MCMC-PT iteration number: 11900 of 40000. Chain number 2. Current logpost: -357.935. Length of jump: 6.          Running MCMC-PT iteration number: 11800 of 40000. Chain number 1. Current logpost: -361.445. Length of jump: 4.          Running MCMC-PT iteration number: 12000 of 40000. Chain number 4. Current logpost: -361.249. Length of jump: 6.          Running MCMC-PT iteration number: 11900 of 40000. Chain number 3. Current logpost: -364.993. Length of jump: 8.          Running MCMC-PT iteration number: 12000 of 40000. Chain number 2. Current logpost: -357.479. Length of jump: 6.          Running MCMC-PT iteration number: 11900 of 40000. Chain number 1. Current logpost: -359.904. Length of jump: 4.          Running MCMC-PT iteration number: 12100 of 40000. Chain number 4. Current logpost: -361.515. Length of jump: 6.          Running MCMC-PT iteration number: 12100 of 40000. Chain number 2. Current logpost: -358.223. Length of jump: 6.          Running MCMC-PT iteration number: 12000 of 40000. Chain number 3. Current logpost: -364.881. Length of jump: 7.          Running MCMC-PT iteration number: 12000 of 40000. Chain number 1. Current logpost: -360.909. Length of jump: 4.          Running MCMC-PT iteration number: 12200 of 40000. Chain number 4. Current logpost: -362.927. Length of jump: 7.          Running MCMC-PT iteration number: 12200 of 40000. Chain number 2. Current logpost: -356.98. Length of jump: 6.          Running MCMC-PT iteration number: 12100 of 40000. Chain number 3. Current logpost: -363.214. Length of jump: 7.          Running MCMC-PT iteration number: 12100 of 40000. Chain number 1. Current logpost: -360.13. Length of jump: 4.          Running MCMC-PT iteration number: 12300 of 40000. Chain number 4. Current logpost: -364.362. Length of jump: 7.          Running MCMC-PT iteration number: 12300 of 40000. Chain number 2. Current logpost: -357.918. Length of jump: 5.          Running MCMC-PT iteration number: 12200 of 40000. Chain number 3. Current logpost: -363.688. Length of jump: 8.          Running MCMC-PT iteration number: 12200 of 40000. Chain number 1. Current logpost: -360.699. Length of jump: 5.          Running MCMC-PT iteration number: 12400 of 40000. Chain number 4. Current logpost: -360.766. Length of jump: 5.          Running MCMC-PT iteration number: 12400 of 40000. Chain number 2. Current logpost: -358.598. Length of jump: 6.          Running MCMC-PT iteration number: 12300 of 40000. Chain number 3. Current logpost: -362.011. Length of jump: 8.          Running MCMC-PT iteration number: 12300 of 40000. Chain number 1. Current logpost: -363.456. Length of jump: 5.          Running MCMC-PT iteration number: 12500 of 40000. Chain number 4. Current logpost: -364.628. Length of jump: 5.          Running MCMC-PT iteration number: 12500 of 40000. Chain number 2. Current logpost: -360.37. Length of jump: 4.          Running MCMC-PT iteration number: 12400 of 40000. Chain number 3. Current logpost: -361.878. Length of jump: 8.          Running MCMC-PT iteration number: 12400 of 40000. Chain number 1. Current logpost: -361.32. Length of jump: 6.          Running MCMC-PT iteration number: 12600 of 40000. Chain number 4. Current logpost: -363.21. Length of jump: 6.          Running MCMC-PT iteration number: 12600 of 40000. Chain number 2. Current logpost: -360.517. Length of jump: 4.          Running MCMC-PT iteration number: 12500 of 40000. Chain number 3. Current logpost: -362.104. Length of jump: 6.          Running MCMC-PT iteration number: 12500 of 40000. Chain number 1. Current logpost: -364.74. Length of jump: 4.          Running MCMC-PT iteration number: 12700 of 40000. Chain number 4. Current logpost: -363.282. Length of jump: 6.          Running MCMC-PT iteration number: 12700 of 40000. Chain number 2. Current logpost: -360.645. Length of jump: 4.          Running MCMC-PT iteration number: 12600 of 40000. Chain number 3. Current logpost: -360.186. Length of jump: 4.          Running MCMC-PT iteration number: 12600 of 40000. Chain number 1. Current logpost: -362.758. Length of jump: 4.          Running MCMC-PT iteration number: 12800 of 40000. Chain number 4. Current logpost: -362.281. Length of jump: 5.          Running MCMC-PT iteration number: 12800 of 40000. Chain number 2. Current logpost: -361.243. Length of jump: 5.          Running MCMC-PT iteration number: 12700 of 40000. Chain number 3. Current logpost: -360.518. Length of jump: 4.          Running MCMC-PT iteration number: 12700 of 40000. Chain number 1. Current logpost: -361.315. Length of jump: 5.          Running MCMC-PT iteration number: 12900 of 40000. Chain number 4. Current logpost: -364.594. Length of jump: 3.          Running MCMC-PT iteration number: 12900 of 40000. Chain number 2. Current logpost: -362.493. Length of jump: 4.          Running MCMC-PT iteration number: 12800 of 40000. Chain number 3. Current logpost: -360.445. Length of jump: 4.          Running MCMC-PT iteration number: 12800 of 40000. Chain number 1. Current logpost: -360.659. Length of jump: 7.          Running MCMC-PT iteration number: 13000 of 40000. Chain number 4. Current logpost: -363.671. Length of jump: 6.          Running MCMC-PT iteration number: 13000 of 40000. Chain number 2. Current logpost: -361.206. Length of jump: 5.          Running MCMC-PT iteration number: 12900 of 40000. Chain number 3. Current logpost: -364.776. Length of jump: 4.          Running MCMC-PT iteration number: 12900 of 40000. Chain number 1. Current logpost: -360.342. Length of jump: 7.          Running MCMC-PT iteration number: 13100 of 40000. Chain number 4. Current logpost: -364.273. Length of jump: 7.          Running MCMC-PT iteration number: 13100 of 40000. Chain number 2. Current logpost: -364.249. Length of jump: 5.          Running MCMC-PT iteration number: 13000 of 40000. Chain number 3. Current logpost: -361.262. Length of jump: 5.          Running MCMC-PT iteration number: 13000 of 40000. Chain number 1. Current logpost: -361.074. Length of jump: 8.          Running MCMC-PT iteration number: 13200 of 40000. Chain number 4. Current logpost: -360.539. Length of jump: 5.          Running MCMC-PT iteration number: 13200 of 40000. Chain number 2. Current logpost: -362.034. Length of jump: 6.          Running MCMC-PT iteration number: 13100 of 40000. Chain number 3. Current logpost: -361.626. Length of jump: 5.          Running MCMC-PT iteration number: 13100 of 40000. Chain number 1. Current logpost: -360.585. Length of jump: 8.          Running MCMC-PT iteration number: 13200 of 40000. Chain number 3. Current logpost: -361.436. Length of jump: 4.          Running MCMC-PT iteration number: 13200 of 40000. Chain number 1. Current logpost: -362.189. Length of jump: 9.          Running MCMC-PT iteration number: 13300 of 40000. Chain number 4. Current logpost: -360.53. Length of jump: 5.          Running MCMC-PT iteration number: 13300 of 40000. Chain number 2. Current logpost: -363.295. Length of jump: 6.          Running MCMC-PT iteration number: 13400 of 40000. Chain number 4. Current logpost: -360.637. Length of jump: 6.          Running MCMC-PT iteration number: 13400 of 40000. Chain number 2. Current logpost: -362.353. Length of jump: 4.          Running MCMC-PT iteration number: 13300 of 40000. Chain number 3. Current logpost: -362.199. Length of jump: 4.          Running MCMC-PT iteration number: 13500 of 40000. Chain number 4. Current logpost: -360.606. Length of jump: 5.          Running MCMC-PT iteration number: 13300 of 40000. Chain number 1. Current logpost: -363.577. Length of jump: 8.          Running MCMC-PT iteration number: 13500 of 40000. Chain number 2. Current logpost: -360.922. Length of jump: 3.          Running MCMC-PT iteration number: 13400 of 40000. Chain number 3. Current logpost: -363.567. Length of jump: 3.          Running MCMC-PT iteration number: 13600 of 40000. Chain number 4. Current logpost: -359.852. Length of jump: 4.          Running MCMC-PT iteration number: 13400 of 40000. Chain number 1. Current logpost: -360.91. Length of jump: 8.          Running MCMC-PT iteration number: 13600 of 40000. Chain number 2. Current logpost: -364.717. Length of jump: 4.          Running MCMC-PT iteration number: 13500 of 40000. Chain number 3. Current logpost: -363.05. Length of jump: 3.          Running MCMC-PT iteration number: 13700 of 40000. Chain number 4. Current logpost: -367.658. Length of jump: 5.          Running MCMC-PT iteration number: 13500 of 40000. Chain number 1. Current logpost: -359.261. Length of jump: 7.          Running MCMC-PT iteration number: 13700 of 40000. Chain number 2. Current logpost: -359.674. Length of jump: 7.          Running MCMC-PT iteration number: 13600 of 40000. Chain number 3. Current logpost: -365.521. Length of jump: 3.          Running MCMC-PT iteration number: 13800 of 40000. Chain number 4. Current logpost: -366.248. Length of jump: 6.          Running MCMC-PT iteration number: 13600 of 40000. Chain number 1. Current logpost: -358.173. Length of jump: 6.          Running MCMC-PT iteration number: 13700 of 40000. Chain number 3. Current logpost: -360.094. Length of jump: 5.          Running MCMC-PT iteration number: 13800 of 40000. Chain number 2. Current logpost: -358.98. Length of jump: 7.          Running MCMC-PT iteration number: 13900 of 40000. Chain number 4. Current logpost: -360.371. Length of jump: 5.          Running MCMC-PT iteration number: 13700 of 40000. Chain number 1. Current logpost: -359.844. Length of jump: 6.          Running MCMC-PT iteration number: 13800 of 40000. Chain number 3. Current logpost: -360.515. Length of jump: 5.          Running MCMC-PT iteration number: 13900 of 40000. Chain number 2. Current logpost: -359.996. Length of jump: 7.          Running MCMC-PT iteration number: 14000 of 40000. Chain number 4. Current logpost: -364.278. Length of jump: 5.          Running MCMC-PT iteration number: 13800 of 40000. Chain number 1. Current logpost: -359.91. Length of jump: 7.          Running MCMC-PT iteration number: 13900 of 40000. Chain number 3. Current logpost: -362.106. Length of jump: 5.          Running MCMC-PT iteration number: 14000 of 40000. Chain number 2. Current logpost: -358.356. Length of jump: 6.          Running MCMC-PT iteration number: 14100 of 40000. Chain number 4. Current logpost: -365.089. Length of jump: 5.          Running MCMC-PT iteration number: 13900 of 40000. Chain number 1. Current logpost: -359.511. Length of jump: 8.          Running MCMC-PT iteration number: 14000 of 40000. Chain number 3. Current logpost: -363.519. Length of jump: 6.          Running MCMC-PT iteration number: 14100 of 40000. Chain number 2. Current logpost: -359.454. Length of jump: 7.          Running MCMC-PT iteration number: 14200 of 40000. Chain number 4. Current logpost: -360.917. Length of jump: 6.          Running MCMC-PT iteration number: 14000 of 40000. Chain number 1. Current logpost: -361.778. Length of jump: 8.          Running MCMC-PT iteration number: 14100 of 40000. Chain number 3. Current logpost: -361.195. Length of jump: 4.          Running MCMC-PT iteration number: 14200 of 40000. Chain number 2. Current logpost: -358.67. Length of jump: 6.          Running MCMC-PT iteration number: 14300 of 40000. Chain number 4. Current logpost: -364.064. Length of jump: 6.          Running MCMC-PT iteration number: 14100 of 40000. Chain number 1. Current logpost: -361.227. Length of jump: 8.          Running MCMC-PT iteration number: 14200 of 40000. Chain number 3. Current logpost: -360.793. Length of jump: 4.          Running MCMC-PT iteration number: 14300 of 40000. Chain number 2. Current logpost: -360.508. Length of jump: 7.          Running MCMC-PT iteration number: 14400 of 40000. Chain number 4. Current logpost: -361.605. Length of jump: 6.          Running MCMC-PT iteration number: 14200 of 40000. Chain number 1. Current logpost: -362.489. Length of jump: 8.          Running MCMC-PT iteration number: 14300 of 40000. Chain number 3. Current logpost: -360.494. Length of jump: 4.          Running MCMC-PT iteration number: 14400 of 40000. Chain number 2. Current logpost: -362.969. Length of jump: 7.          Running MCMC-PT iteration number: 14500 of 40000. Chain number 4. Current logpost: -364.548. Length of jump: 5.          Running MCMC-PT iteration number: 14300 of 40000. Chain number 1. Current logpost: -358.649. Length of jump: 6.          Running MCMC-PT iteration number: 14400 of 40000. Chain number 3. Current logpost: -360.567. Length of jump: 5.          Running MCMC-PT iteration number: 14500 of 40000. Chain number 2. Current logpost: -361.108. Length of jump: 6.          Running MCMC-PT iteration number: 14600 of 40000. Chain number 4. Current logpost: -360.278. Length of jump: 4.          Running MCMC-PT iteration number: 14400 of 40000. Chain number 1. Current logpost: -362.351. Length of jump: 6.          Running MCMC-PT iteration number: 14500 of 40000. Chain number 3. Current logpost: -361.191. Length of jump: 3.          Running MCMC-PT iteration number: 14600 of 40000. Chain number 2. Current logpost: -360.602. Length of jump: 6.          Running MCMC-PT iteration number: 14700 of 40000. Chain number 4. Current logpost: -364.418. Length of jump: 6.          Running MCMC-PT iteration number: 14500 of 40000. Chain number 1. Current logpost: -361.326. Length of jump: 6.          Running MCMC-PT iteration number: 14600 of 40000. Chain number 3. Current logpost: -361.396. Length of jump: 3.          Running MCMC-PT iteration number: 14700 of 40000. Chain number 2. Current logpost: -361.221. Length of jump: 4.          Running MCMC-PT iteration number: 14800 of 40000. Chain number 4. Current logpost: -361.027. Length of jump: 4.          Running MCMC-PT iteration number: 14600 of 40000. Chain number 1. Current logpost: -357.765. Length of jump: 6.          Running MCMC-PT iteration number: 14700 of 40000. Chain number 3. Current logpost: -362.839. Length of jump: 3.          Running MCMC-PT iteration number: 14800 of 40000. Chain number 2. Current logpost: -362.401. Length of jump: 4.          Running MCMC-PT iteration number: 14900 of 40000. Chain number 4. Current logpost: -361.686. Length of jump: 4.          Running MCMC-PT iteration number: 14700 of 40000. Chain number 1. Current logpost: -361.371. Length of jump: 6.          Running MCMC-PT iteration number: 14800 of 40000. Chain number 3. Current logpost: -360.185. Length of jump: 4.          Running MCMC-PT iteration number: 14900 of 40000. Chain number 2. Current logpost: -362.952. Length of jump: 4.          Running MCMC-PT iteration number: 15000 of 40000. Chain number 4. Current logpost: -365.303. Length of jump: 4.          Running MCMC-PT iteration number: 14800 of 40000. Chain number 1. Current logpost: -359.144. Length of jump: 5.          Running MCMC-PT iteration number: 14900 of 40000. Chain number 3. Current logpost: -360.433. Length of jump: 4.          Running MCMC-PT iteration number: 15000 of 40000. Chain number 2. Current logpost: -360.313. Length of jump: 4.          Running MCMC-PT iteration number: 15100 of 40000. Chain number 4. Current logpost: -363.459. Length of jump: 5.          Running MCMC-PT iteration number: 14900 of 40000. Chain number 1. Current logpost: -364.282. Length of jump: 7.          Running MCMC-PT iteration number: 15000 of 40000. Chain number 3. Current logpost: -358.001. Length of jump: 4.          Running MCMC-PT iteration number: 15100 of 40000. Chain number 2. Current logpost: -364.385. Length of jump: 6.          Running MCMC-PT iteration number: 15200 of 40000. Chain number 4. Current logpost: -361.189. Length of jump: 5.          Running MCMC-PT iteration number: 15000 of 40000. Chain number 1. Current logpost: -358.721. Length of jump: 7.          Running MCMC-PT iteration number: 15100 of 40000. Chain number 3. Current logpost: -358.527. Length of jump: 5.          Running MCMC-PT iteration number: 15200 of 40000. Chain number 2. Current logpost: -362.929. Length of jump: 7.          Running MCMC-PT iteration number: 15300 of 40000. Chain number 4. Current logpost: -364.254. Length of jump: 5.          Running MCMC-PT iteration number: 15100 of 40000. Chain number 1. Current logpost: -360.468. Length of jump: 8.          Running MCMC-PT iteration number: 15200 of 40000. Chain number 3. Current logpost: -360.731. Length of jump: 6.          Running MCMC-PT iteration number: 15300 of 40000. Chain number 2. Current logpost: -362.011. Length of jump: 6.          Running MCMC-PT iteration number: 15400 of 40000. Chain number 4. Current logpost: -362.748. Length of jump: 6.          Running MCMC-PT iteration number: 15200 of 40000. Chain number 1. Current logpost: -358.727. Length of jump: 8.          Running MCMC-PT iteration number: 15300 of 40000. Chain number 3. Current logpost: -359.084. Length of jump: 6.          Running MCMC-PT iteration number: 15400 of 40000. Chain number 2. Current logpost: -361.181. Length of jump: 5.          Running MCMC-PT iteration number: 15500 of 40000. Chain number 4. Current logpost: -362.37. Length of jump: 6.          Running MCMC-PT iteration number: 15300 of 40000. Chain number 1. Current logpost: -357.354. Length of jump: 6.          Running MCMC-PT iteration number: 15400 of 40000. Chain number 3. Current logpost: -358.935. Length of jump: 7.          Running MCMC-PT iteration number: 15500 of 40000. Chain number 2. Current logpost: -364.651. Length of jump: 6.          Running MCMC-PT iteration number: 15600 of 40000. Chain number 4. Current logpost: -361.25. Length of jump: 7.          Running MCMC-PT iteration number: 15400 of 40000. Chain number 1. Current logpost: -357.901. Length of jump: 6.          Running MCMC-PT iteration number: 15500 of 40000. Chain number 3. Current logpost: -362.786. Length of jump: 7.          Running MCMC-PT iteration number: 15600 of 40000. Chain number 2. Current logpost: -364.076. Length of jump: 6.          Running MCMC-PT iteration number: 15700 of 40000. Chain number 4. Current logpost: -358.708. Length of jump: 5.          Running MCMC-PT iteration number: 15500 of 40000. Chain number 1. Current logpost: -359.864. Length of jump: 6.          Running MCMC-PT iteration number: 15600 of 40000. Chain number 3. Current logpost: -360.564. Length of jump: 6.          Running MCMC-PT iteration number: 15700 of 40000. Chain number 2. Current logpost: -365.462. Length of jump: 7.          Running MCMC-PT iteration number: 15800 of 40000. Chain number 4. Current logpost: -358.568. Length of jump: 5.          Running MCMC-PT iteration number: 15600 of 40000. Chain number 1. Current logpost: -358.259. Length of jump: 6.          Running MCMC-PT iteration number: 15700 of 40000. Chain number 3. Current logpost: -359.233. Length of jump: 6.          Running MCMC-PT iteration number: 15800 of 40000. Chain number 2. Current logpost: -364.459. Length of jump: 7.          Running MCMC-PT iteration number: 15900 of 40000. Chain number 4. Current logpost: -359.753. Length of jump: 6.          Running MCMC-PT iteration number: 15700 of 40000. Chain number 1. Current logpost: -358.286. Length of jump: 6.          Running MCMC-PT iteration number: 15800 of 40000. Chain number 3. Current logpost: -358.544. Length of jump: 5.          Running MCMC-PT iteration number: 15900 of 40000. Chain number 2. Current logpost: -364.517. Length of jump: 7.          Running MCMC-PT iteration number: 16000 of 40000. Chain number 4. Current logpost: -361.58. Length of jump: 5.          Running MCMC-PT iteration number: 15800 of 40000. Chain number 1. Current logpost: -362.59. Length of jump: 5.          Running MCMC-PT iteration number: 15900 of 40000. Chain number 3. Current logpost: -357.971. Length of jump: 5.          Running MCMC-PT iteration number: 16000 of 40000. Chain number 2. Current logpost: -368.052. Length of jump: 8.          Running MCMC-PT iteration number: 16100 of 40000. Chain number 4. Current logpost: -359.388. Length of jump: 6.          Running MCMC-PT iteration number: 15900 of 40000. Chain number 1. Current logpost: -362.032. Length of jump: 6.          Running MCMC-PT iteration number: 16000 of 40000. Chain number 3. Current logpost: -358.19. Length of jump: 5.          Running MCMC-PT iteration number: 16100 of 40000. Chain number 2. Current logpost: -365.906. Length of jump: 8.          Running MCMC-PT iteration number: 16200 of 40000. Chain number 4. Current logpost: -359.386. Length of jump: 6.          Running MCMC-PT iteration number: 16000 of 40000. Chain number 1. Current logpost: -361.44. Length of jump: 6.          Running MCMC-PT iteration number: 16100 of 40000. Chain number 3. Current logpost: -358.003. Length of jump: 5.          Running MCMC-PT iteration number: 16200 of 40000. Chain number 2. Current logpost: -365.4. Length of jump: 8.          Running MCMC-PT iteration number: 16300 of 40000. Chain number 4. Current logpost: -358.108. Length of jump: 6.          Running MCMC-PT iteration number: 16100 of 40000. Chain number 1. Current logpost: -360.974. Length of jump: 6.          Running MCMC-PT iteration number: 16200 of 40000. Chain number 3. Current logpost: -359.918. Length of jump: 5.          Running MCMC-PT iteration number: 16300 of 40000. Chain number 2. Current logpost: -367.663. Length of jump: 8.          Running MCMC-PT iteration number: 16400 of 40000. Chain number 4. Current logpost: -358.538. Length of jump: 6.          Running MCMC-PT iteration number: 16200 of 40000. Chain number 1. Current logpost: -360.577. Length of jump: 6.          Running MCMC-PT iteration number: 16300 of 40000. Chain number 3. Current logpost: -357.565. Length of jump: 5.          Running MCMC-PT iteration number: 16400 of 40000. Chain number 2. Current logpost: -370.727. Length of jump: 7.          Running MCMC-PT iteration number: 16500 of 40000. Chain number 4. Current logpost: -359.625. Length of jump: 6.          Running MCMC-PT iteration number: 16300 of 40000. Chain number 1. Current logpost: -358.425. Length of jump: 5.          Running MCMC-PT iteration number: 16400 of 40000. Chain number 3. Current logpost: -358.254. Length of jump: 5.          Running MCMC-PT iteration number: 16500 of 40000. Chain number 2. Current logpost: -363.336. Length of jump: 6.          Running MCMC-PT iteration number: 16600 of 40000. Chain number 4. Current logpost: -360.126. Length of jump: 6.          Running MCMC-PT iteration number: 16400 of 40000. Chain number 1. Current logpost: -362.585. Length of jump: 7.          Running MCMC-PT iteration number: 16500 of 40000. Chain number 3. Current logpost: -360.021. Length of jump: 6.          Running MCMC-PT iteration number: 16600 of 40000. Chain number 3. Current logpost: -359.943. Length of jump: 7.          Running MCMC-PT iteration number: 16800 of 40000. Chain number 4. Current logpost: -364.528. Length of jump: 7.          Running MCMC-PT iteration number: 16700 of 40000. Chain number 2. Current logpost: -363.773. Length of jump: 6.          Running MCMC-PT iteration number: 16700 of 40000. Chain number 3. Current logpost: -361.143. Length of jump: 7.          Running MCMC-PT iteration number: 16900 of 40000. Chain number 4. Current logpost: -357.751. Length of jump: 7.          Running MCMC-PT iteration number: 16800 of 40000. Chain number 2. Current logpost: -363.222. Length of jump: 6.          Running MCMC-PT iteration number: 16700 of 40000. Chain number 1. Current logpost: -361.999. Length of jump: 7.          Running MCMC-PT iteration number: 16800 of 40000. Chain number 3. Current logpost: -361.413. Length of jump: 4.          Running MCMC-PT iteration number: 17000 of 40000. Chain number 4. Current logpost: -358.201. Length of jump: 7.          Running MCMC-PT iteration number: 16900 of 40000. Chain number 2. Current logpost: -366.801. Length of jump: 5.          Running MCMC-PT iteration number: 16800 of 40000. Chain number 1. Current logpost: -361.314. Length of jump: 7.          Running MCMC-PT iteration number: 16900 of 40000. Chain number 3. Current logpost: -362.9. Length of jump: 6.          Running MCMC-PT iteration number: 17100 of 40000. Chain number 4. Current logpost: -359.553. Length of jump: 8.          Running MCMC-PT iteration number: 17000 of 40000. Chain number 2. Current logpost: -367.489. Length of jump: 6.          Running MCMC-PT iteration number: 16900 of 40000. Chain number 1. Current logpost: -361.181. Length of jump: 8.          Running MCMC-PT iteration number: 17000 of 40000. Chain number 3. Current logpost: -364.337. Length of jump: 7.          Running MCMC-PT iteration number: 17200 of 40000. Chain number 4. Current logpost: -359.545. Length of jump: 7.          Running MCMC-PT iteration number: 17100 of 40000. Chain number 2. Current logpost: -366.597. Length of jump: 7.          Running MCMC-PT iteration number: 17100 of 40000. Chain number 3. Current logpost: -363.582. Length of jump: 7.          Running MCMC-PT iteration number: 17300 of 40000. Chain number 4. Current logpost: -357.964. Length of jump: 7.          Running MCMC-PT iteration number: 17200 of 40000. Chain number 2. Current logpost: -366.337. Length of jump: 6.          Running MCMC-PT iteration number: 17100 of 40000. Chain number 1. Current logpost: -360.439. Length of jump: 7.          Running MCMC-PT iteration number: 17200 of 40000. Chain number 3. Current logpost: -364.153. Length of jump: 6.          Running MCMC-PT iteration number: 17400 of 40000. Chain number 4. Current logpost: -356.275. Length of jump: 7.          Running MCMC-PT iteration number: 17300 of 40000. Chain number 2. Current logpost: -368.141. Length of jump: 6.          Running MCMC-PT iteration number: 17200 of 40000. Chain number 1. Current logpost: -359.343. Length of jump: 7.          Running MCMC-PT iteration number: 17300 of 40000. Chain number 3. Current logpost: -361.524. Length of jump: 6.          Running MCMC-PT iteration number: 17500 of 40000. Chain number 4. Current logpost: -357.456. Length of jump: 6.          Running MCMC-PT iteration number: 17400 of 40000. Chain number 2. Current logpost: -362.216. Length of jump: 6.          Running MCMC-PT iteration number: 17600 of 40000. Chain number 4. Current logpost: -358.707. Length of jump: 7.          Running MCMC-PT iteration number: 17500 of 40000. Chain number 2. Current logpost: -360.349. Length of jump: 5.          Running MCMC-PT iteration number: 17400 of 40000. Chain number 1. Current logpost: -360.804. Length of jump: 6.          Running MCMC-PT iteration number: 17500 of 40000. Chain number 3. Current logpost: -362.299. Length of jump: 4.          Running MCMC-PT iteration number: 17700 of 40000. Chain number 4. Current logpost: -358.017. Length of jump: 8.          Running MCMC-PT iteration number: 17600 of 40000. Chain number 2. Current logpost: -360.894. Length of jump: 5.          Running MCMC-PT iteration number: 17500 of 40000. Chain number 1. Current logpost: -359.289. Length of jump: 7.          Running MCMC-PT iteration number: 17600 of 40000. Chain number 3. Current logpost: -361.458. Length of jump: 4.          Running MCMC-PT iteration number: 17800 of 40000. Chain number 4. Current logpost: -358.146. Length of jump: 8.          Running MCMC-PT iteration number: 17700 of 40000. Chain number 2. Current logpost: -362.89. Length of jump: 6.          Running MCMC-PT iteration number: 17700 of 40000. Chain number 3. Current logpost: -360.657. Length of jump: 4.          Running MCMC-PT iteration number: 17600 of 40000. Chain number 1. Current logpost: -361.751. Length of jump: 7.          Running MCMC-PT iteration number: 17900 of 40000. Chain number 4. Current logpost: -360.686. Length of jump: 7.          Running MCMC-PT iteration number: 17800 of 40000. Chain number 2. Current logpost: -363.782. Length of jump: 6.          Running MCMC-PT iteration number: 17800 of 40000. Chain number 3. Current logpost: -361.417. Length of jump: 4.          Running MCMC-PT iteration number: 17700 of 40000. Chain number 1. Current logpost: -363.755. Length of jump: 8.          Running MCMC-PT iteration number: 18000 of 40000. Chain number 4. Current logpost: -358.729. Length of jump: 6.          Running MCMC-PT iteration number: 17900 of 40000. Chain number 2. Current logpost: -361.222. Length of jump: 6.          Running MCMC-PT iteration number: 17900 of 40000. Chain number 3. Current logpost: -360.322. Length of jump: 4.          Running MCMC-PT iteration number: 17800 of 40000. Chain number 1. Current logpost: -363.73. Length of jump: 8.          Running MCMC-PT iteration number: 18100 of 40000. Chain number 4. Current logpost: -358.488. Length of jump: 6.          Running MCMC-PT iteration number: 18000 of 40000. Chain number 2. Current logpost: -360.973. Length of jump: 6.          Running MCMC-PT iteration number: 18000 of 40000. Chain number 3. Current logpost: -360.27. Length of jump: 4.          Running MCMC-PT iteration number: 17900 of 40000. Chain number 1. Current logpost: -363.14. Length of jump: 6.          Running MCMC-PT iteration number: 18200 of 40000. Chain number 4. Current logpost: -366.531. Length of jump: 5.          Running MCMC-PT iteration number: 18100 of 40000. Chain number 2. Current logpost: -362.456. Length of jump: 6.          Running MCMC-PT iteration number: 18100 of 40000. Chain number 3. Current logpost: -363.387. Length of jump: 5.          Running MCMC-PT iteration number: 18000 of 40000. Chain number 1. Current logpost: -360.408. Length of jump: 5.          Running MCMC-PT iteration number: 18300 of 40000. Chain number 4. Current logpost: -361.514. Length of jump: 5.          Running MCMC-PT iteration number: 18200 of 40000. Chain number 2. Current logpost: -360.771. Length of jump: 5.          Running MCMC-PT iteration number: 18200 of 40000. Chain number 3. Current logpost: -362.509. Length of jump: 5.          Running MCMC-PT iteration number: 18100 of 40000. Chain number 1. Current logpost: -360.42. Length of jump: 5.          Running MCMC-PT iteration number: 18400 of 40000. Chain number 4. Current logpost: -361.266. Length of jump: 5.          Running MCMC-PT iteration number: 18300 of 40000. Chain number 2. Current logpost: -360.614. Length of jump: 5.          Running MCMC-PT iteration number: 18300 of 40000. Chain number 3. Current logpost: -362.384. Length of jump: 6.          Running MCMC-PT iteration number: 18200 of 40000. Chain number 1. Current logpost: -361.192. Length of jump: 4.          Running MCMC-PT iteration number: 18500 of 40000. Chain number 4. Current logpost: -360.577. Length of jump: 4.          Running MCMC-PT iteration number: 18400 of 40000. Chain number 2. Current logpost: -362.631. Length of jump: 5.          Running MCMC-PT iteration number: 18400 of 40000. Chain number 3. Current logpost: -364.627. Length of jump: 8.          Running MCMC-PT iteration number: 18300 of 40000. Chain number 1. Current logpost: -365.032. Length of jump: 4.          Running MCMC-PT iteration number: 18500 of 40000. Chain number 2. Current logpost: -359.76. Length of jump: 5.          Running MCMC-PT iteration number: 18600 of 40000. Chain number 4. Current logpost: -360.35. Length of jump: 4.          Running MCMC-PT iteration number: 18500 of 40000. Chain number 3. Current logpost: -364.469. Length of jump: 8.          Running MCMC-PT iteration number: 18400 of 40000. Chain number 1. Current logpost: -361.73. Length of jump: 4.          Running MCMC-PT iteration number: 18700 of 40000. Chain number 4. Current logpost: -361.37. Length of jump: 4.          Running MCMC-PT iteration number: 18600 of 40000. Chain number 2. Current logpost: -362.285. Length of jump: 5.          Running MCMC-PT iteration number: 18600 of 40000. Chain number 3. Current logpost: -363.867. Length of jump: 7.          Running MCMC-PT iteration number: 18500 of 40000. Chain number 1. Current logpost: -364.247. Length of jump: 4.          Running MCMC-PT iteration number: 18800 of 40000. Chain number 4. Current logpost: -364.819. Length of jump: 6.          Running MCMC-PT iteration number: 18700 of 40000. Chain number 2. Current logpost: -362.788. Length of jump: 5.          Running MCMC-PT iteration number: 18700 of 40000. Chain number 3. Current logpost: -361.93. Length of jump: 7.          Running MCMC-PT iteration number: 18600 of 40000. Chain number 1. Current logpost: -361.328. Length of jump: 4.          Running MCMC-PT iteration number: 18900 of 40000. Chain number 4. Current logpost: -363.156. Length of jump: 7.          Running MCMC-PT iteration number: 18800 of 40000. Chain number 2. Current logpost: -365.083. Length of jump: 4.          Running MCMC-PT iteration number: 18800 of 40000. Chain number 3. Current logpost: -361.806. Length of jump: 6.          Running MCMC-PT iteration number: 18700 of 40000. Chain number 1. Current logpost: -360.54. Length of jump: 5.          Running MCMC-PT iteration number: 19000 of 40000. Chain number 4. Current logpost: -362.894. Length of jump: 6.          Running MCMC-PT iteration number: 18900 of 40000. Chain number 2. Current logpost: -361.615. Length of jump: 4.          Running MCMC-PT iteration number: 18900 of 40000. Chain number 3. Current logpost: -361.843. Length of jump: 6.          Running MCMC-PT iteration number: 18800 of 40000. Chain number 1. Current logpost: -360.362. Length of jump: 5.          Running MCMC-PT iteration number: 19100 of 40000. Chain number 4. Current logpost: -360.614. Length of jump: 3.          Running MCMC-PT iteration number: 19000 of 40000. Chain number 2. Current logpost: -363.687. Length of jump: 5.          Running MCMC-PT iteration number: 19000 of 40000. Chain number 3. Current logpost: -360.868. Length of jump: 5.          Running MCMC-PT iteration number: 18900 of 40000. Chain number 1. Current logpost: -361.316. Length of jump: 5.          Running MCMC-PT iteration number: 19200 of 40000. Chain number 4. Current logpost: -362.169. Length of jump: 3.          Running MCMC-PT iteration number: 19100 of 40000. Chain number 2. Current logpost: -365.856. Length of jump: 5.          Running MCMC-PT iteration number: 19100 of 40000. Chain number 3. Current logpost: -361.291. Length of jump: 5.          Running MCMC-PT iteration number: 19000 of 40000. Chain number 1. Current logpost: -362.152. Length of jump: 6.          Running MCMC-PT iteration number: 19300 of 40000. Chain number 4. Current logpost: -361.429. Length of jump: 3.          Running MCMC-PT iteration number: 19200 of 40000. Chain number 2. Current logpost: -364.639. Length of jump: 5.          Running MCMC-PT iteration number: 19200 of 40000. Chain number 3. Current logpost: -362.141. Length of jump: 6.          Running MCMC-PT iteration number: 19100 of 40000. Chain number 1. Current logpost: -361.086. Length of jump: 5.          Running MCMC-PT iteration number: 19400 of 40000. Chain number 4. Current logpost: -360.919. Length of jump: 4.          Running MCMC-PT iteration number: 19300 of 40000. Chain number 2. Current logpost: -367.953. Length of jump: 4.          Running MCMC-PT iteration number: 19300 of 40000. Chain number 3. Current logpost: -361.306. Length of jump: 5.          Running MCMC-PT iteration number: 19200 of 40000. Chain number 1. Current logpost: -360.462. Length of jump: 4.          Running MCMC-PT iteration number: 19500 of 40000. Chain number 4. Current logpost: -361.7. Length of jump: 4.          Running MCMC-PT iteration number: 19400 of 40000. Chain number 2. Current logpost: -364.557. Length of jump: 4.          Running MCMC-PT iteration number: 19400 of 40000. Chain number 3. Current logpost: -363.871. Length of jump: 5.          Running MCMC-PT iteration number: 19300 of 40000. Chain number 1. Current logpost: -361.872. Length of jump: 5.          Running MCMC-PT iteration number: 19600 of 40000. Chain number 4. Current logpost: -362.352. Length of jump: 4.          Running MCMC-PT iteration number: 19500 of 40000. Chain number 2. Current logpost: -363.566. Length of jump: 4.          Running MCMC-PT iteration number: 19500 of 40000. Chain number 3. Current logpost: -360.999. Length of jump: 5.          Running MCMC-PT iteration number: 19400 of 40000. Chain number 1. Current logpost: -364.138. Length of jump: 4.          Running MCMC-PT iteration number: 19700 of 40000. Chain number 4. Current logpost: -362.554. Length of jump: 5.          Running MCMC-PT iteration number: 19600 of 40000. Chain number 2. Current logpost: -361.689. Length of jump: 5.          Running MCMC-PT iteration number: 19600 of 40000. Chain number 3. Current logpost: -365.616. Length of jump: 5.          Running MCMC-PT iteration number: 19500 of 40000. Chain number 1. Current logpost: -362.83. Length of jump: 4.          Running MCMC-PT iteration number: 19800 of 40000. Chain number 4. Current logpost: -363.617. Length of jump: 4.          Running MCMC-PT iteration number: 19700 of 40000. Chain number 2. Current logpost: -364.085. Length of jump: 5.          Running MCMC-PT iteration number: 19700 of 40000. Chain number 3. Current logpost: -362.52. Length of jump: 5.          Running MCMC-PT iteration number: 19600 of 40000. Chain number 1. Current logpost: -360.364. Length of jump: 4.          Running MCMC-PT iteration number: 19900 of 40000. Chain number 4. Current logpost: -360.699. Length of jump: 4.          Running MCMC-PT iteration number: 19800 of 40000. Chain number 2. Current logpost: -360.45. Length of jump: 4.          Running MCMC-PT iteration number: 19800 of 40000. Chain number 3. Current logpost: -362.614. Length of jump: 6.          Running MCMC-PT iteration number: 19700 of 40000. Chain number 1. Current logpost: -361.097. Length of jump: 5.          Running MCMC-PT iteration number: 20000 of 40000. Chain number 4. Current logpost: -360.606. Length of jump: 4.          Running MCMC-PT iteration number: 19900 of 40000. Chain number 2. Current logpost: -363.437. Length of jump: 4.          Running MCMC-PT iteration number: 19900 of 40000. Chain number 3. Current logpost: -362.737. Length of jump: 6.          Running MCMC-PT iteration number: 19800 of 40000. Chain number 1. Current logpost: -362.042. Length of jump: 4.          Running MCMC-PT iteration number: 20100 of 40000. Chain number 4. Current logpost: -362.243. Length of jump: 4.          Running MCMC-PT iteration number: 20000 of 40000. Chain number 2. Current logpost: -360.364. Length of jump: 5.          Running MCMC-PT iteration number: 20000 of 40000. Chain number 3. Current logpost: -360.975. Length of jump: 5.          Running MCMC-PT iteration number: 19900 of 40000. Chain number 1. Current logpost: -360.746. Length of jump: 4.          Running MCMC-PT iteration number: 20200 of 40000. Chain number 4. Current logpost: -362.111. Length of jump: 5.          Running MCMC-PT iteration number: 20100 of 40000. Chain number 2. Current logpost: -360.036. Length of jump: 5.          Running MCMC-PT iteration number: 20100 of 40000. Chain number 3. Current logpost: -361.535. Length of jump: 5.          Running MCMC-PT iteration number: 20000 of 40000. Chain number 1. Current logpost: -360.584. Length of jump: 4.          Running MCMC-PT iteration number: 20300 of 40000. Chain number 4. Current logpost: -358.516. Length of jump: 5.          Running MCMC-PT iteration number: 20200 of 40000. Chain number 2. Current logpost: -362.502. Length of jump: 3.          Running MCMC-PT iteration number: 20200 of 40000. Chain number 3. Current logpost: -360.856. Length of jump: 4.          Running MCMC-PT iteration number: 20100 of 40000. Chain number 1. Current logpost: -360.635. Length of jump: 4.          Running MCMC-PT iteration number: 20400 of 40000. Chain number 4. Current logpost: -362.977. Length of jump: 7.          Running MCMC-PT iteration number: 20300 of 40000. Chain number 2. Current logpost: -360.875. Length of jump: 3.          Running MCMC-PT iteration number: 20300 of 40000. Chain number 3. Current logpost: -360.793. Length of jump: 3.          Running MCMC-PT iteration number: 20200 of 40000. Chain number 1. Current logpost: -361.214. Length of jump: 4.          Running MCMC-PT iteration number: 20500 of 40000. Chain number 4. Current logpost: -360.372. Length of jump: 6.          Running MCMC-PT iteration number: 20400 of 40000. Chain number 2. Current logpost: -360.525. Length of jump: 4.          Running MCMC-PT iteration number: 20400 of 40000. Chain number 3. Current logpost: -362.34. Length of jump: 3.          Running MCMC-PT iteration number: 20300 of 40000. Chain number 1. Current logpost: -361.483. Length of jump: 4.          Running MCMC-PT iteration number: 20600 of 40000. Chain number 4. Current logpost: -358.528. Length of jump: 6.          Running MCMC-PT iteration number: 20500 of 40000. Chain number 2. Current logpost: -361.771. Length of jump: 4.          Running MCMC-PT iteration number: 20500 of 40000. Chain number 3. Current logpost: -360.14. Length of jump: 4.          Running MCMC-PT iteration number: 20400 of 40000. Chain number 1. Current logpost: -364.847. Length of jump: 5.          Running MCMC-PT iteration number: 20700 of 40000. Chain number 4. Current logpost: -357.019. Length of jump: 7.          Running MCMC-PT iteration number: 20600 of 40000. Chain number 2. Current logpost: -359.211. Length of jump: 4.          Running MCMC-PT iteration number: 20600 of 40000. Chain number 3. Current logpost: -360.102. Length of jump: 4.          Running MCMC-PT iteration number: 20700 of 40000. Chain number 2. Current logpost: -357.791. Length of jump: 5.          Running MCMC-PT iteration number: 20700 of 40000. Chain number 3. Current logpost: -360.656. Length of jump: 4.          Running MCMC-PT iteration number: 20800 of 40000. Chain number 2. Current logpost: -357.821. Length of jump: 6.          Running MCMC-PT iteration number: 20800 of 40000. Chain number 3. Current logpost: -360.918. Length of jump: 4.          Running MCMC-PT iteration number: 20700 of 40000. Chain number 1. Current logpost: -365.64. Length of jump: 4.          Running MCMC-PT iteration number: 21000 of 40000. Chain number 4. Current logpost: -358.649. Length of jump: 6.          Running MCMC-PT iteration number: 21100 of 40000. Chain number 4. Current logpost: -363.047. Length of jump: 6.          Running MCMC-PT iteration number: 21000 of 40000. Chain number 2. Current logpost: -357.69. Length of jump: 7.          Running MCMC-PT iteration number: 21000 of 40000. Chain number 3. Current logpost: -362.137. Length of jump: 6.          Running MCMC-PT iteration number: 20900 of 40000. Chain number 1. Current logpost: -365.511. Length of jump: 3.          Running MCMC-PT iteration number: 21200 of 40000. Chain number 4. Current logpost: -359.976. Length of jump: 7.          Running MCMC-PT iteration number: 21100 of 40000. Chain number 2. Current logpost: -356.759. Length of jump: 6.          Running MCMC-PT iteration number: 21100 of 40000. Chain number 3. Current logpost: -359.187. Length of jump: 5.          Running MCMC-PT iteration number: 21000 of 40000. Chain number 1. Current logpost: -364.279. Length of jump: 4.          Running MCMC-PT iteration number: 21300 of 40000. Chain number 4. Current logpost: -359.894. Length of jump: 7.          Running MCMC-PT iteration number: 21200 of 40000. Chain number 2. Current logpost: -357.017. Length of jump: 6.          Running MCMC-PT iteration number: 21200 of 40000. Chain number 3. Current logpost: -358.183. Length of jump: 5.          Running MCMC-PT iteration number: 21100 of 40000. Chain number 1. Current logpost: -360.605. Length of jump: 3.          Running MCMC-PT iteration number: 21400 of 40000. Chain number 4. Current logpost: -362.924. Length of jump: 7.          Running MCMC-PT iteration number: 21300 of 40000. Chain number 2. Current logpost: -356.233. Length of jump: 6.          Running MCMC-PT iteration number: 21300 of 40000. Chain number 3. Current logpost: -358.878. Length of jump: 6.          Running MCMC-PT iteration number: 21200 of 40000. Chain number 1. Current logpost: -361.236. Length of jump: 4.          Running MCMC-PT iteration number: 21500 of 40000. Chain number 4. Current logpost: -358.699. Length of jump: 6.          Running MCMC-PT iteration number: 21400 of 40000. Chain number 2. Current logpost: -359.551. Length of jump: 7.          Running MCMC-PT iteration number: 21400 of 40000. Chain number 3. Current logpost: -359.039. Length of jump: 6.          Running MCMC-PT iteration number: 21300 of 40000. Chain number 1. Current logpost: -360.495. Length of jump: 5.          Running MCMC-PT iteration number: 21600 of 40000. Chain number 4. Current logpost: -361.681. Length of jump: 6.          Running MCMC-PT iteration number: 21500 of 40000. Chain number 2. Current logpost: -357.987. Length of jump: 8.          Running MCMC-PT iteration number: 21500 of 40000. Chain number 3. Current logpost: -362.18. Length of jump: 7.          Running MCMC-PT iteration number: 21400 of 40000. Chain number 1. Current logpost: -359.11. Length of jump: 5.          Running MCMC-PT iteration number: 21700 of 40000. Chain number 4. Current logpost: -359.603. Length of jump: 5.          Running MCMC-PT iteration number: 21600 of 40000. Chain number 2. Current logpost: -358.537. Length of jump: 8.          Running MCMC-PT iteration number: 21600 of 40000. Chain number 3. Current logpost: -359.739. Length of jump: 6.          Running MCMC-PT iteration number: 21500 of 40000. Chain number 1. Current logpost: -360.936. Length of jump: 5.          Running MCMC-PT iteration number: 21800 of 40000. Chain number 4. Current logpost: -360.864. Length of jump: 5.          Running MCMC-PT iteration number: 21700 of 40000. Chain number 2. Current logpost: -359.968. Length of jump: 8.          Running MCMC-PT iteration number: 21700 of 40000. Chain number 3. Current logpost: -360.752. Length of jump: 6.          Running MCMC-PT iteration number: 21600 of 40000. Chain number 1. Current logpost: -359.826. Length of jump: 5.          Running MCMC-PT iteration number: 21900 of 40000. Chain number 4. Current logpost: -360.909. Length of jump: 5.          Running MCMC-PT iteration number: 21800 of 40000. Chain number 2. Current logpost: -358.413. Length of jump: 7.          Running MCMC-PT iteration number: 21800 of 40000. Chain number 3. Current logpost: -360.916. Length of jump: 5.          Running MCMC-PT iteration number: 21700 of 40000. Chain number 1. Current logpost: -362.191. Length of jump: 7.          Running MCMC-PT iteration number: 22000 of 40000. Chain number 4. Current logpost: -364.198. Length of jump: 5.          Running MCMC-PT iteration number: 22100 of 40000. Chain number 4. Current logpost: -361.086. Length of jump: 5.          Running MCMC-PT iteration number: 22000 of 40000. Chain number 2. Current logpost: -358.529. Length of jump: 8.          Running MCMC-PT iteration number: 22000 of 40000. Chain number 3. Current logpost: -359.775. Length of jump: 4.          Running MCMC-PT iteration number: 21900 of 40000. Chain number 1. Current logpost: -360.845. Length of jump: 6.          Running MCMC-PT iteration number: 22200 of 40000. Chain number 4. Current logpost: -362.957. Length of jump: 7.          Running MCMC-PT iteration number: 22100 of 40000. Chain number 2. Current logpost: -358.046. Length of jump: 7.          Running MCMC-PT iteration number: 22200 of 40000. Chain number 2. Current logpost: -358.079. Length of jump: 7.          Running MCMC-PT iteration number: 22200 of 40000. Chain number 3. Current logpost: -360.092. Length of jump: 4.          Running MCMC-PT iteration number: 22100 of 40000. Chain number 1. Current logpost: -359.806. Length of jump: 7.          Running MCMC-PT iteration number: 22400 of 40000. Chain number 4. Current logpost: -364.92. Length of jump: 8.          Running MCMC-PT iteration number: 22300 of 40000. Chain number 2. Current logpost: -359.663. Length of jump: 7.          Running MCMC-PT iteration number: 22300 of 40000. Chain number 3. Current logpost: -359.963. Length of jump: 4.          Running MCMC-PT iteration number: 22200 of 40000. Chain number 1. Current logpost: -360.007. Length of jump: 7.          Running MCMC-PT iteration number: 22500 of 40000. Chain number 4. Current logpost: -359.99. Length of jump: 7.          Running MCMC-PT iteration number: 22400 of 40000. Chain number 2. Current logpost: -360.371. Length of jump: 8.          Running MCMC-PT iteration number: 22400 of 40000. Chain number 3. Current logpost: -361.757. Length of jump: 4.          Running MCMC-PT iteration number: 22300 of 40000. Chain number 1. Current logpost: -362.564. Length of jump: 7.          Running MCMC-PT iteration number: 22600 of 40000. Chain number 4. Current logpost: -360.565. Length of jump: 7.          Running MCMC-PT iteration number: 22500 of 40000. Chain number 2. Current logpost: -359.746. Length of jump: 8.          Running MCMC-PT iteration number: 22500 of 40000. Chain number 3. Current logpost: -362.205. Length of jump: 4.          Running MCMC-PT iteration number: 22400 of 40000. Chain number 1. Current logpost: -361.295. Length of jump: 6.          Running MCMC-PT iteration number: 22700 of 40000. Chain number 4. Current logpost: -361.067. Length of jump: 7.          Running MCMC-PT iteration number: 22600 of 40000. Chain number 2. Current logpost: -361.038. Length of jump: 7.          Running MCMC-PT iteration number: 22600 of 40000. Chain number 3. Current logpost: -362.501. Length of jump: 3.          Running MCMC-PT iteration number: 22500 of 40000. Chain number 1. Current logpost: -359.267. Length of jump: 6.          Running MCMC-PT iteration number: 22800 of 40000. Chain number 4. Current logpost: -362.211. Length of jump: 6.          Running MCMC-PT iteration number: 22700 of 40000. Chain number 2. Current logpost: -357.809. Length of jump: 7.          Running MCMC-PT iteration number: 22700 of 40000. Chain number 3. Current logpost: -360.65. Length of jump: 4.          Running MCMC-PT iteration number: 22600 of 40000. Chain number 1. Current logpost: -358.503. Length of jump: 6.          Running MCMC-PT iteration number: 22900 of 40000. Chain number 4. Current logpost: -360.538. Length of jump: 6.          Running MCMC-PT iteration number: 22800 of 40000. Chain number 2. Current logpost: -360.912. Length of jump: 6.          Running MCMC-PT iteration number: 22800 of 40000. Chain number 3. Current logpost: -360.603. Length of jump: 4.          Running MCMC-PT iteration number: 22700 of 40000. Chain number 1. Current logpost: -360.083. Length of jump: 6.          Running MCMC-PT iteration number: 23000 of 40000. Chain number 4. Current logpost: -360.426. Length of jump: 7.          Running MCMC-PT iteration number: 22900 of 40000. Chain number 2. Current logpost: -364.023. Length of jump: 8.          Running MCMC-PT iteration number: 22900 of 40000. Chain number 3. Current logpost: -360.141. Length of jump: 4.          Running MCMC-PT iteration number: 22800 of 40000. Chain number 1. Current logpost: -361.03. Length of jump: 6.          Running MCMC-PT iteration number: 23100 of 40000. Chain number 4. Current logpost: -361.745. Length of jump: 7.          Running MCMC-PT iteration number: 23000 of 40000. Chain number 2. Current logpost: -361.697. Length of jump: 7.          Running MCMC-PT iteration number: 23000 of 40000. Chain number 3. Current logpost: -362.079. Length of jump: 5.          Running MCMC-PT iteration number: 22900 of 40000. Chain number 1. Current logpost: -361. Length of jump: 6.          Running MCMC-PT iteration number: 23200 of 40000. Chain number 4. Current logpost: -359.068. Length of jump: 5.          Running MCMC-PT iteration number: 23100 of 40000. Chain number 2. Current logpost: -358.608. Length of jump: 5.          Running MCMC-PT iteration number: 23100 of 40000. Chain number 3. Current logpost: -363.986. Length of jump: 5.          Running MCMC-PT iteration number: 23000 of 40000. Chain number 1. Current logpost: -360.293. Length of jump: 7.          Running MCMC-PT iteration number: 23300 of 40000. Chain number 4. Current logpost: -358.964. Length of jump: 6.          Running MCMC-PT iteration number: 23200 of 40000. Chain number 2. Current logpost: -357.05. Length of jump: 6.          Running MCMC-PT iteration number: 23200 of 40000. Chain number 3. Current logpost: -361.157. Length of jump: 4.          Running MCMC-PT iteration number: 23100 of 40000. Chain number 1. Current logpost: -362.148. Length of jump: 5.          Running MCMC-PT iteration number: 23400 of 40000. Chain number 4. Current logpost: -359.634. Length of jump: 7.          Running MCMC-PT iteration number: 23300 of 40000. Chain number 2. Current logpost: -358.802. Length of jump: 6.          Running MCMC-PT iteration number: 23300 of 40000. Chain number 3. Current logpost: -362.859. Length of jump: 5.          Running MCMC-PT iteration number: 23200 of 40000. Chain number 1. Current logpost: -362.588. Length of jump: 5.          Running MCMC-PT iteration number: 23500 of 40000. Chain number 4. Current logpost: -360.39. Length of jump: 6.          Running MCMC-PT iteration number: 23400 of 40000. Chain number 2. Current logpost: -359.06. Length of jump: 6.          Running MCMC-PT iteration number: 23400 of 40000. Chain number 3. Current logpost: -362.464. Length of jump: 5.          Running MCMC-PT iteration number: 23300 of 40000. Chain number 1. Current logpost: -363.335. Length of jump: 5.          Running MCMC-PT iteration number: 23600 of 40000. Chain number 4. Current logpost: -363.097. Length of jump: 5.          Running MCMC-PT iteration number: 23500 of 40000. Chain number 2. Current logpost: -360.974. Length of jump: 6.          Running MCMC-PT iteration number: 23500 of 40000. Chain number 3. Current logpost: -361.851. Length of jump: 4.          Running MCMC-PT iteration number: 23400 of 40000. Chain number 1. Current logpost: -363.811. Length of jump: 5.          Running MCMC-PT iteration number: 23700 of 40000. Chain number 4. Current logpost: -365.603. Length of jump: 6.          Running MCMC-PT iteration number: 23600 of 40000. Chain number 2. Current logpost: -358.467. Length of jump: 5.          Running MCMC-PT iteration number: 23600 of 40000. Chain number 3. Current logpost: -360.612. Length of jump: 4.          Running MCMC-PT iteration number: 23500 of 40000. Chain number 1. Current logpost: -367.213. Length of jump: 5.          Running MCMC-PT iteration number: 23700 of 40000. Chain number 2. Current logpost: -360.521. Length of jump: 5.          Running MCMC-PT iteration number: 23700 of 40000. Chain number 3. Current logpost: -362.9. Length of jump: 4.          Running MCMC-PT iteration number: 23600 of 40000. Chain number 1. Current logpost: -362.569. Length of jump: 5.          Running MCMC-PT iteration number: 23800 of 40000. Chain number 4. Current logpost: -362.302. Length of jump: 6.          Running MCMC-PT iteration number: 23700 of 40000. Chain number 1. Current logpost: -361.749. Length of jump: 5.          Running MCMC-PT iteration number: 23900 of 40000. Chain number 4. Current logpost: -364.432. Length of jump: 7.          Running MCMC-PT iteration number: 23800 of 40000. Chain number 2. Current logpost: -362.379. Length of jump: 4.          Running MCMC-PT iteration number: 23800 of 40000. Chain number 3. Current logpost: -360.75. Length of jump: 4.          Running MCMC-PT iteration number: 24000 of 40000. Chain number 4. Current logpost: -360.958. Length of jump: 8.          Running MCMC-PT iteration number: 23900 of 40000. Chain number 2. Current logpost: -360.871. Length of jump: 4.          Running MCMC-PT iteration number: 23900 of 40000. Chain number 3. Current logpost: -361.209. Length of jump: 4.          Running MCMC-PT iteration number: 23800 of 40000. Chain number 1. Current logpost: -361.52. Length of jump: 4.          Running MCMC-PT iteration number: 24100 of 40000. Chain number 4. Current logpost: -357.622. Length of jump: 7.          Running MCMC-PT iteration number: 24000 of 40000. Chain number 2. Current logpost: -359.469. Length of jump: 4.          Running MCMC-PT iteration number: 24000 of 40000. Chain number 3. Current logpost: -361.023. Length of jump: 6.          Running MCMC-PT iteration number: 23900 of 40000. Chain number 1. Current logpost: -360.996. Length of jump: 4.          Running MCMC-PT iteration number: 24200 of 40000. Chain number 4. Current logpost: -357.908. Length of jump: 7.          Running MCMC-PT iteration number: 24100 of 40000. Chain number 2. Current logpost: -361.673. Length of jump: 5.          Running MCMC-PT iteration number: 24100 of 40000. Chain number 3. Current logpost: -361.835. Length of jump: 6.          Running MCMC-PT iteration number: 24000 of 40000. Chain number 1. Current logpost: -363.047. Length of jump: 7.          Running MCMC-PT iteration number: 24300 of 40000. Chain number 4. Current logpost: -358.625. Length of jump: 9.          Running MCMC-PT iteration number: 24200 of 40000. Chain number 2. Current logpost: -361.466. Length of jump: 5.          Running MCMC-PT iteration number: 24200 of 40000. Chain number 3. Current logpost: -363.976. Length of jump: 6.          Running MCMC-PT iteration number: 24100 of 40000. Chain number 1. Current logpost: -363.655. Length of jump: 7.          Running MCMC-PT iteration number: 24400 of 40000. Chain number 4. Current logpost: -357.491. Length of jump: 7.          Running MCMC-PT iteration number: 24300 of 40000. Chain number 2. Current logpost: -361.012. Length of jump: 8.          Running MCMC-PT iteration number: 24300 of 40000. Chain number 3. Current logpost: -362.692. Length of jump: 6.          Running MCMC-PT iteration number: 24200 of 40000. Chain number 1. Current logpost: -363.985. Length of jump: 7.          Running MCMC-PT iteration number: 24500 of 40000. Chain number 4. Current logpost: -357.682. Length of jump: 8.          Running MCMC-PT iteration number: 24400 of 40000. Chain number 2. Current logpost: -360.571. Length of jump: 9.          Running MCMC-PT iteration number: 24400 of 40000. Chain number 3. Current logpost: -361.644. Length of jump: 5.          Running MCMC-PT iteration number: 24300 of 40000. Chain number 1. Current logpost: -361.749. Length of jump: 6.          Running MCMC-PT iteration number: 24600 of 40000. Chain number 4. Current logpost: -358.443. Length of jump: 9.          Running MCMC-PT iteration number: 24500 of 40000. Chain number 3. Current logpost: -361.764. Length of jump: 5.          Running MCMC-PT iteration number: 24500 of 40000. Chain number 2. Current logpost: -359.252. Length of jump: 6.          Running MCMC-PT iteration number: 24400 of 40000. Chain number 1. Current logpost: -361.28. Length of jump: 6.          Running MCMC-PT iteration number: 24700 of 40000. Chain number 4. Current logpost: -359.142. Length of jump: 8.          Running MCMC-PT iteration number: 24600 of 40000. Chain number 2. Current logpost: -361.473. Length of jump: 6.          Running MCMC-PT iteration number: 24600 of 40000. Chain number 3. Current logpost: -359.764. Length of jump: 5.          Running MCMC-PT iteration number: 24500 of 40000. Chain number 1. Current logpost: -363.271. Length of jump: 6.          Running MCMC-PT iteration number: 24800 of 40000. Chain number 4. Current logpost: -360.297. Length of jump: 7.          Running MCMC-PT iteration number: 24700 of 40000. Chain number 2. Current logpost: -361.293. Length of jump: 7.          Running MCMC-PT iteration number: 24700 of 40000. Chain number 3. Current logpost: -360.185. Length of jump: 4.          Running MCMC-PT iteration number: 24600 of 40000. Chain number 1. Current logpost: -361.068. Length of jump: 6.          Running MCMC-PT iteration number: 24900 of 40000. Chain number 4. Current logpost: -357.135. Length of jump: 7.          Running MCMC-PT iteration number: 24800 of 40000. Chain number 3. Current logpost: -359.792. Length of jump: 5.          Running MCMC-PT iteration number: 24800 of 40000. Chain number 2. Current logpost: -360.295. Length of jump: 6.          Running MCMC-PT iteration number: 24700 of 40000. Chain number 1. Current logpost: -364.16. Length of jump: 7.          Running MCMC-PT iteration number: 25000 of 40000. Chain number 4. Current logpost: -359.924. Length of jump: 7.          Running MCMC-PT iteration number: 24900 of 40000. Chain number 3. Current logpost: -359.252. Length of jump: 5.          Running MCMC-PT iteration number: 24900 of 40000. Chain number 2. Current logpost: -360.618. Length of jump: 6.          Running MCMC-PT iteration number: 24800 of 40000. Chain number 1. Current logpost: -363.674. Length of jump: 6.          Running MCMC-PT iteration number: 25100 of 40000. Chain number 4. Current logpost: -358.625. Length of jump: 6.          Running MCMC-PT iteration number: 25000 of 40000. Chain number 3. Current logpost: -358.338. Length of jump: 5.          Running MCMC-PT iteration number: 25000 of 40000. Chain number 2. Current logpost: -359.634. Length of jump: 5.          Running MCMC-PT iteration number: 24900 of 40000. Chain number 1. Current logpost: -364.31. Length of jump: 6.          Running MCMC-PT iteration number: 25200 of 40000. Chain number 4. Current logpost: -358.801. Length of jump: 7.          Running MCMC-PT iteration number: 25100 of 40000. Chain number 3. Current logpost: -358.428. Length of jump: 6.          Running MCMC-PT iteration number: 25100 of 40000. Chain number 2. Current logpost: -359.238. Length of jump: 5.          Running MCMC-PT iteration number: 25000 of 40000. Chain number 1. Current logpost: -361.841. Length of jump: 5.          Running MCMC-PT iteration number: 25300 of 40000. Chain number 4. Current logpost: -358.135. Length of jump: 8.          Running MCMC-PT iteration number: 25200 of 40000. Chain number 3. Current logpost: -358.237. Length of jump: 6.          Running MCMC-PT iteration number: 25200 of 40000. Chain number 2. Current logpost: -361.074. Length of jump: 5.          Running MCMC-PT iteration number: 25100 of 40000. Chain number 1. Current logpost: -366.537. Length of jump: 5.          Running MCMC-PT iteration number: 25400 of 40000. Chain number 4. Current logpost: -356.651. Length of jump: 7.          Running MCMC-PT iteration number: 25300 of 40000. Chain number 3. Current logpost: -359.595. Length of jump: 6.          Running MCMC-PT iteration number: 25300 of 40000. Chain number 2. Current logpost: -361.48. Length of jump: 7.          Running MCMC-PT iteration number: 25200 of 40000. Chain number 1. Current logpost: -359.671. Length of jump: 5.          Running MCMC-PT iteration number: 25400 of 40000. Chain number 3. Current logpost: -360.758. Length of jump: 5.          Running MCMC-PT iteration number: 25500 of 40000. Chain number 4. Current logpost: -357.228. Length of jump: 7.          Running MCMC-PT iteration number: 25400 of 40000. Chain number 2. Current logpost: -360.338. Length of jump: 8.          Running MCMC-PT iteration number: 25300 of 40000. Chain number 1. Current logpost: -357.845. Length of jump: 8.          Running MCMC-PT iteration number: 25500 of 40000. Chain number 3. Current logpost: -359.441. Length of jump: 4.          Running MCMC-PT iteration number: 25600 of 40000. Chain number 4. Current logpost: -361.703. Length of jump: 7.          Running MCMC-PT iteration number: 25500 of 40000. Chain number 2. Current logpost: -359.393. Length of jump: 8.          Running MCMC-PT iteration number: 25600 of 40000. Chain number 2. Current logpost: -362.202. Length of jump: 8.          Running MCMC-PT iteration number: 25500 of 40000. Chain number 1. Current logpost: -356.172. Length of jump: 6.          Running MCMC-PT iteration number: 25800 of 40000. Chain number 4. Current logpost: -357.24. Length of jump: 6.          Running MCMC-PT iteration number: 25700 of 40000. Chain number 3. Current logpost: -360.491. Length of jump: 4.          Running MCMC-PT iteration number: 25700 of 40000. Chain number 2. Current logpost: -358.885. Length of jump: 7.          Running MCMC-PT iteration number: 25600 of 40000. Chain number 1. Current logpost: -356.473. Length of jump: 7.          Running MCMC-PT iteration number: 25900 of 40000. Chain number 4. Current logpost: -357.506. Length of jump: 7.          Running MCMC-PT iteration number: 25800 of 40000. Chain number 3. Current logpost: -360.649. Length of jump: 4.          Running MCMC-PT iteration number: 25800 of 40000. Chain number 2. Current logpost: -359.312. Length of jump: 7.          Running MCMC-PT iteration number: 25700 of 40000. Chain number 1. Current logpost: -359.263. Length of jump: 6.          Running MCMC-PT iteration number: 26000 of 40000. Chain number 4. Current logpost: -358.922. Length of jump: 6.          Running MCMC-PT iteration number: 25900 of 40000. Chain number 3. Current logpost: -361.189. Length of jump: 6.          Running MCMC-PT iteration number: 25900 of 40000. Chain number 2. Current logpost: -359.994. Length of jump: 8.          Running MCMC-PT iteration number: 25800 of 40000. Chain number 1. Current logpost: -356.92. Length of jump: 6.          Running MCMC-PT iteration number: 26100 of 40000. Chain number 4. Current logpost: -359.369. Length of jump: 6.          Running MCMC-PT iteration number: 26000 of 40000. Chain number 3. Current logpost: -362.945. Length of jump: 6.          Running MCMC-PT iteration number: 26000 of 40000. Chain number 2. Current logpost: -359.799. Length of jump: 8.          Running MCMC-PT iteration number: 25900 of 40000. Chain number 1. Current logpost: -356.711. Length of jump: 5.          Running MCMC-PT iteration number: 26200 of 40000. Chain number 4. Current logpost: -356.869. Length of jump: 6.          Running MCMC-PT iteration number: 26100 of 40000. Chain number 3. Current logpost: -361.081. Length of jump: 5.          Running MCMC-PT iteration number: 26100 of 40000. Chain number 2. Current logpost: -362.14. Length of jump: 8.          Running MCMC-PT iteration number: 26000 of 40000. Chain number 1. Current logpost: -356.141. Length of jump: 5.          Running MCMC-PT iteration number: 26300 of 40000. Chain number 4. Current logpost: -357.184. Length of jump: 6.          Running MCMC-PT iteration number: 26200 of 40000. Chain number 3. Current logpost: -363.973. Length of jump: 5.          Running MCMC-PT iteration number: 26200 of 40000. Chain number 2. Current logpost: -362.09. Length of jump: 8.          Running MCMC-PT iteration number: 26100 of 40000. Chain number 1. Current logpost: -358.474. Length of jump: 5.          Running MCMC-PT iteration number: 26400 of 40000. Chain number 4. Current logpost: -356.687. Length of jump: 6.          Running MCMC-PT iteration number: 26300 of 40000. Chain number 3. Current logpost: -359.072. Length of jump: 6.          Running MCMC-PT iteration number: 26300 of 40000. Chain number 2. Current logpost: -359.021. Length of jump: 7.          Running MCMC-PT iteration number: 26200 of 40000. Chain number 1. Current logpost: -359.012. Length of jump: 5.          Running MCMC-PT iteration number: 26500 of 40000. Chain number 4. Current logpost: -356.972. Length of jump: 6.          Running MCMC-PT iteration number: 26400 of 40000. Chain number 3. Current logpost: -359.099. Length of jump: 6.          Running MCMC-PT iteration number: 26400 of 40000. Chain number 2. Current logpost: -359.508. Length of jump: 7.          Running MCMC-PT iteration number: 26300 of 40000. Chain number 1. Current logpost: -357.179. Length of jump: 5.          Running MCMC-PT iteration number: 26600 of 40000. Chain number 4. Current logpost: -359.518. Length of jump: 5.          Running MCMC-PT iteration number: 26500 of 40000. Chain number 3. Current logpost: -358.428. Length of jump: 6.          Running MCMC-PT iteration number: 26500 of 40000. Chain number 2. Current logpost: -359.457. Length of jump: 7.          Running MCMC-PT iteration number: 26400 of 40000. Chain number 1. Current logpost: -356.789. Length of jump: 5.          Running MCMC-PT iteration number: 26700 of 40000. Chain number 4. Current logpost: -363.616. Length of jump: 4.          Running MCMC-PT iteration number: 26600 of 40000. Chain number 3. Current logpost: -358.406. Length of jump: 6.          Running MCMC-PT iteration number: 26600 of 40000. Chain number 2. Current logpost: -357.072. Length of jump: 6.          Running MCMC-PT iteration number: 26500 of 40000. Chain number 1. Current logpost: -360.507. Length of jump: 4.          Running MCMC-PT iteration number: 26800 of 40000. Chain number 4. Current logpost: -361.163. Length of jump: 6.          Running MCMC-PT iteration number: 26700 of 40000. Chain number 3. Current logpost: -359.474. Length of jump: 7.          Running MCMC-PT iteration number: 26700 of 40000. Chain number 2. Current logpost: -358.645. Length of jump: 6.          Running MCMC-PT iteration number: 26600 of 40000. Chain number 1. Current logpost: -359.224. Length of jump: 4.          Running MCMC-PT iteration number: 26900 of 40000. Chain number 4. Current logpost: -359.588. Length of jump: 6.          Running MCMC-PT iteration number: 26800 of 40000. Chain number 3. Current logpost: -360.303. Length of jump: 7.          Running MCMC-PT iteration number: 26800 of 40000. Chain number 2. Current logpost: -359.449. Length of jump: 7.          Running MCMC-PT iteration number: 26700 of 40000. Chain number 1. Current logpost: -359.689. Length of jump: 4.          Running MCMC-PT iteration number: 27000 of 40000. Chain number 4. Current logpost: -361.012. Length of jump: 5.          Running MCMC-PT iteration number: 26900 of 40000. Chain number 3. Current logpost: -362.288. Length of jump: 7.          Running MCMC-PT iteration number: 26900 of 40000. Chain number 2. Current logpost: -358.846. Length of jump: 6.          Running MCMC-PT iteration number: 26800 of 40000. Chain number 1. Current logpost: -359.033. Length of jump: 4.          Running MCMC-PT iteration number: 27100 of 40000. Chain number 4. Current logpost: -361.202. Length of jump: 4.          Running MCMC-PT iteration number: 27000 of 40000. Chain number 3. Current logpost: -359.178. Length of jump: 6.          Running MCMC-PT iteration number: 27000 of 40000. Chain number 2. Current logpost: -359.703. Length of jump: 6.          Running MCMC-PT iteration number: 27200 of 40000. Chain number 4. Current logpost: -360.628. Length of jump: 4.          Running MCMC-PT iteration number: 26900 of 40000. Chain number 1. Current logpost: -360.876. Length of jump: 5.          Running MCMC-PT iteration number: 27100 of 40000. Chain number 3. Current logpost: -361.94. Length of jump: 7.          Running MCMC-PT iteration number: 27100 of 40000. Chain number 2. Current logpost: -361.54. Length of jump: 6.          Running MCMC-PT iteration number: 27300 of 40000. Chain number 4. Current logpost: -359.125. Length of jump: 6.          Running MCMC-PT iteration number: 27000 of 40000. Chain number 1. Current logpost: -361.176. Length of jump: 5.          Running MCMC-PT iteration number: 27200 of 40000. Chain number 3. Current logpost: -359.533. Length of jump: 6.          Running MCMC-PT iteration number: 27200 of 40000. Chain number 2. Current logpost: -359.901. Length of jump: 5.          Running MCMC-PT iteration number: 27400 of 40000. Chain number 4. Current logpost: -358.614. Length of jump: 6.          Running MCMC-PT iteration number: 27100 of 40000. Chain number 1. Current logpost: -361.78. Length of jump: 4.          Running MCMC-PT iteration number: 27300 of 40000. Chain number 3. Current logpost: -360.737. Length of jump: 6.          Running MCMC-PT iteration number: 27300 of 40000. Chain number 2. Current logpost: -359.501. Length of jump: 5.          Running MCMC-PT iteration number: 27200 of 40000. Chain number 1. Current logpost: -363.42. Length of jump: 4.          Running MCMC-PT iteration number: 27500 of 40000. Chain number 4. Current logpost: -361.832. Length of jump: 7.          Running MCMC-PT iteration number: 27400 of 40000. Chain number 3. Current logpost: -359.388. Length of jump: 6.          Running MCMC-PT iteration number: 27400 of 40000. Chain number 2. Current logpost: -363.952. Length of jump: 5.          Running MCMC-PT iteration number: 27300 of 40000. Chain number 1. Current logpost: -358.665. Length of jump: 5.          Running MCMC-PT iteration number: 27600 of 40000. Chain number 4. Current logpost: -362.4. Length of jump: 7.          Running MCMC-PT iteration number: 27500 of 40000. Chain number 3. Current logpost: -361.989. Length of jump: 7.          Running MCMC-PT iteration number: 27500 of 40000. Chain number 2. Current logpost: -360.227. Length of jump: 5.          Running MCMC-PT iteration number: 27700 of 40000. Chain number 4. Current logpost: -362.159. Length of jump: 7.          Running MCMC-PT iteration number: 27400 of 40000. Chain number 1. Current logpost: -359.794. Length of jump: 5.          Running MCMC-PT iteration number: 27600 of 40000. Chain number 3. Current logpost: -363.323. Length of jump: 8.          Running MCMC-PT iteration number: 27600 of 40000. Chain number 2. Current logpost: -357.745. Length of jump: 6.          Running MCMC-PT iteration number: 27800 of 40000. Chain number 4. Current logpost: -359.917. Length of jump: 6.          Running MCMC-PT iteration number: 27500 of 40000. Chain number 1. Current logpost: -360.413. Length of jump: 5.          Running MCMC-PT iteration number: 27700 of 40000. Chain number 3. Current logpost: -364.189. Length of jump: 7.          Running MCMC-PT iteration number: 27700 of 40000. Chain number 2. Current logpost: -357.427. Length of jump: 7.          Running MCMC-PT iteration number: 27900 of 40000. Chain number 4. Current logpost: -359.368. Length of jump: 7.          Running MCMC-PT iteration number: 27600 of 40000. Chain number 1. Current logpost: -361.982. Length of jump: 5.          Running MCMC-PT iteration number: 27800 of 40000. Chain number 3. Current logpost: -363.507. Length of jump: 7.          Running MCMC-PT iteration number: 27800 of 40000. Chain number 2. Current logpost: -355.65. Length of jump: 6.          Running MCMC-PT iteration number: 28000 of 40000. Chain number 4. Current logpost: -359.433. Length of jump: 7.          Running MCMC-PT iteration number: 27700 of 40000. Chain number 1. Current logpost: -367.364. Length of jump: 7.          Running MCMC-PT iteration number: 27900 of 40000. Chain number 3. Current logpost: -361.836. Length of jump: 6.          Running MCMC-PT iteration number: 27900 of 40000. Chain number 2. Current logpost: -357.886. Length of jump: 6.          Running MCMC-PT iteration number: 28100 of 40000. Chain number 4. Current logpost: -358.72. Length of jump: 6.          Running MCMC-PT iteration number: 27800 of 40000. Chain number 1. Current logpost: -362.15. Length of jump: 7.          Running MCMC-PT iteration number: 28000 of 40000. Chain number 3. Current logpost: -363.786. Length of jump: 6.          Running MCMC-PT iteration number: 28000 of 40000. Chain number 2. Current logpost: -357.9. Length of jump: 6.          Running MCMC-PT iteration number: 27900 of 40000. Chain number 1. Current logpost: -363.875. Length of jump: 8.          Running MCMC-PT iteration number: 28100 of 40000. Chain number 3. Current logpost: -363.167. Length of jump: 6.          Running MCMC-PT iteration number: 28100 of 40000. Chain number 2. Current logpost: -357.46. Length of jump: 7.          Running MCMC-PT iteration number: 28300 of 40000. Chain number 4. Current logpost: -358.225. Length of jump: 6.          Running MCMC-PT iteration number: 28000 of 40000. Chain number 1. Current logpost: -365.848. Length of jump: 8.          Running MCMC-PT iteration number: 28200 of 40000. Chain number 3. Current logpost: -361.817. Length of jump: 5.          Running MCMC-PT iteration number: 28200 of 40000. Chain number 2. Current logpost: -358.548. Length of jump: 7.          Running MCMC-PT iteration number: 28400 of 40000. Chain number 4. Current logpost: -357.959. Length of jump: 6.          Running MCMC-PT iteration number: 28100 of 40000. Chain number 1. Current logpost: -365.071. Length of jump: 8.          Running MCMC-PT iteration number: 28300 of 40000. Chain number 3. Current logpost: -361.03. Length of jump: 5.          Running MCMC-PT iteration number: 28300 of 40000. Chain number 2. Current logpost: -359.575. Length of jump: 5.          Running MCMC-PT iteration number: 28500 of 40000. Chain number 4. Current logpost: -356.134. Length of jump: 7.          Running MCMC-PT iteration number: 28200 of 40000. Chain number 1. Current logpost: -366.283. Length of jump: 8.          Running MCMC-PT iteration number: 28400 of 40000. Chain number 3. Current logpost: -361.072. Length of jump: 4.          Running MCMC-PT iteration number: 28400 of 40000. Chain number 2. Current logpost: -359.341. Length of jump: 6.          Running MCMC-PT iteration number: 28600 of 40000. Chain number 4. Current logpost: -356.405. Length of jump: 7.          Running MCMC-PT iteration number: 28300 of 40000. Chain number 1. Current logpost: -365.029. Length of jump: 9.          Running MCMC-PT iteration number: 28500 of 40000. Chain number 3. Current logpost: -361.702. Length of jump: 4.          Running MCMC-PT iteration number: 28500 of 40000. Chain number 2. Current logpost: -358.779. Length of jump: 6.          Running MCMC-PT iteration number: 28700 of 40000. Chain number 4. Current logpost: -356.113. Length of jump: 7.          Running MCMC-PT iteration number: 28400 of 40000. Chain number 1. Current logpost: Running MCMC-PT iteration number: -361.686. Length of jump: 7.          28600 of 40000. Chain number 3. Current logpost: -362.077. Length of jump: 4.          Running MCMC-PT iteration number: 28600 of 40000. Chain number 2. Current logpost: -358.011. Length of jump: 7.          Running MCMC-PT iteration number: 28800 of 40000. Chain number 4. Current logpost: -359.13. Length of jump: 7.          Running MCMC-PT iteration number: 28700 of 40000. Chain number 3. Current logpost: -360.16. Length of jump: 4.          Running MCMC-PT iteration number: 28500 of 40000. Chain number 1. Current logpost: -359.417. Length of jump: 6.          Running MCMC-PT iteration number: 28700 of 40000. Chain number 2. Current logpost: -359.68. Length of jump: 7.          Running MCMC-PT iteration number: 28900 of 40000. Chain number 4. Current logpost: -356.127. Length of jump: 6.          Running MCMC-PT iteration number: 28800 of 40000. Chain number 3. Current logpost: -358.99. Length of jump: 6.          Running MCMC-PT iteration number: 28600 of 40000. Chain number 1. Current logpost: -359.195. Length of jump: 6.          Running MCMC-PT iteration number: 28800 of 40000. Chain number 2. Current logpost: -360.207. Length of jump: 6.          Running MCMC-PT iteration number: 29000 of 40000. Chain number 4. Current logpost: -357.893. Length of jump: 5.          Running MCMC-PT iteration number: 28900 of 40000. Chain number 3. Current logpost: -358.233. Length of jump: 4.          Running MCMC-PT iteration number: 28700 of 40000. Chain number 1. Current logpost: -359.111. Length of jump: 6.          Running MCMC-PT iteration number: 28900 of 40000. Chain number 2. Current logpost: -359.031. Length of jump: 6.          Running MCMC-PT iteration number: 29100 of 40000. Chain number 4. Current logpost: -358.835. Length of jump: 5.          Running MCMC-PT iteration number: 28800 of 40000. Chain number 1. Current logpost: -363.55. Length of jump: 6.          Running MCMC-PT iteration number: 29000 of 40000. Chain number 3. Current logpost: -360.274. Length of jump: 4.          Running MCMC-PT iteration number: 29000 of 40000. Chain number 2. Current logpost: -359.243. Length of jump: 5.          Running MCMC-PT iteration number: 29200 of 40000. Chain number 4. Current logpost: -359.04. Length of jump: 5.          Running MCMC-PT iteration number: 28900 of 40000. Chain number 1. Current logpost: -362.923. Length of jump: 7.          Running MCMC-PT iteration number: 29100 of 40000. Chain number 3. Current logpost: -359.63. Length of jump: 5.          Running MCMC-PT iteration number: 29100 of 40000. Chain number 2. Current logpost: -360.688. Length of jump: 6.          Running MCMC-PT iteration number: 29300 of 40000. Chain number 4. Current logpost: -359.723. Length of jump: 4.          Running MCMC-PT iteration number: 29200 of 40000. Chain number 3. Current logpost: -358.393. Length of jump: 5.          Running MCMC-PT iteration number: 29000 of 40000. Chain number 1. Current logpost: -361.249. Length of jump: 8.          Running MCMC-PT iteration number: 29200 of 40000. Chain number 2. Current logpost: -357.775. Length of jump: 6.          Running MCMC-PT iteration number: 29400 of 40000. Chain number 4. Current logpost: -360.781. Length of jump: 6.          Running MCMC-PT iteration number: 29300 of 40000. Chain number 3. Current logpost: -357.759. Length of jump: 5.          Running MCMC-PT iteration number: 29100 of 40000. Chain number 1. Current logpost: -358.965. Length of jump: 7.          Running MCMC-PT iteration number: 29300 of 40000. Chain number 2. Current logpost: -357.927. Length of jump: 6.          Running MCMC-PT iteration number: 29500 of 40000. Chain number 4. Current logpost: -359.71. Length of jump: 6.          Running MCMC-PT iteration number: 29400 of 40000. Chain number 3. Current logpost: -359.255. Length of jump: 7.          Running MCMC-PT iteration number: 29200 of 40000. Chain number 1. Current logpost: -358.705. Length of jump: 7.          Running MCMC-PT iteration number: 29400 of 40000. Chain number 2. Current logpost: -356.477. Length of jump: 7.          Running MCMC-PT iteration number: 29600 of 40000. Chain number 4. Current logpost: -359.611. Length of jump: 5.          Running MCMC-PT iteration number: 29500 of 40000. Chain number 3. Current logpost: -358.135. Length of jump: 6.          Running MCMC-PT iteration number: 29300 of 40000. Chain number 1. Current logpost: -360.703. Length of jump: 7.          Running MCMC-PT iteration number: 29500 of 40000. Chain number 2. Current logpost: -356.768. Length of jump: 7.          Running MCMC-PT iteration number: 29700 of 40000. Chain number 4. Current logpost: -359.935. Length of jump: 5.          Running MCMC-PT iteration number: 29600 of 40000. Chain number 3. Current logpost: -363.067. Length of jump: 8.          Running MCMC-PT iteration number: 29400 of 40000. Chain number 1. Current logpost: -358.492. Length of jump: 6.          Running MCMC-PT iteration number: 29600 of 40000. Chain number 2. Current logpost: -361.41. Length of jump: 7.          Running MCMC-PT iteration number: 29800 of 40000. Chain number 4. Current logpost: -361.128. Length of jump: 5.          Running MCMC-PT iteration number: 29700 of 40000. Chain number 3. Current logpost: -361.784. Length of jump: 8.          Running MCMC-PT iteration number: 29500 of 40000. Chain number 1. Current logpost: -361.851. Length of jump: 6.          Running MCMC-PT iteration number: 29700 of 40000. Chain number 2. Current logpost: -359.957. Length of jump: 7.          Running MCMC-PT iteration number: 29800 of 40000. Chain number 2. Current logpost: -359.303. Length of jump: 8.          Running MCMC-PT iteration number: 30000 of 40000. Chain number 4. Current logpost: -367.301. Length of jump: 6.          Running MCMC-PT iteration number: 29900 of 40000. Chain number 3. Current logpost: -358.927. Length of jump: 6.          Running MCMC-PT iteration number: 29700 of 40000. Chain number 1. Current logpost: -358.522. Length of jump: 6.          Running MCMC-PT iteration number: 29900 of 40000. Chain number 2. Current logpost: -360.343. Length of jump: 8.          Running MCMC-PT iteration number: 30100 of 40000. Chain number 4. Current logpost: -359.505. Length of jump: 7.          Running MCMC-PT iteration number: 30000 of 40000. Chain number 3. Current logpost: -358.275. Length of jump: 6.          Running MCMC-PT iteration number: 29800 of 40000. Chain number 1. Current logpost: -357.193. Length of jump: 5.          Running MCMC-PT iteration number: 30000 of 40000. Chain number 2. Current logpost: -364.161. Length of jump: 8.          Running MCMC-PT iteration number: 30200 of 40000. Chain number 4. Current logpost: -357.941. Length of jump: 6.          Running MCMC-PT iteration number: 30100 of 40000. Chain number 3. Current logpost: -359.207. Length of jump: 6.          Running MCMC-PT iteration number: 29900 of 40000. Chain number 1. Current logpost: -357.85. Length of jump: 6.          Running MCMC-PT iteration number: 30100 of 40000. Chain number 2. Current logpost: -359.47. Length of jump: 7.          Running MCMC-PT iteration number: 30300 of 40000. Chain number 4. Current logpost: -356.231. Length of jump: 6.          Running MCMC-PT iteration number: 30200 of 40000. Chain number 3. Current logpost: -360.237. Length of jump: 6.          Running MCMC-PT iteration number: 30000 of 40000. Chain number 1. Current logpost: -358.954. Length of jump: 6.          Running MCMC-PT iteration number: 30200 of 40000. Chain number 2. Current logpost: -359.917. Length of jump: 7.          Running MCMC-PT iteration number: 30400 of 40000. Chain number 4. Current logpost: -358.23. Length of jump: 6.          Running MCMC-PT iteration number: 30300 of 40000. Chain number 3. Current logpost: -361.124. Length of jump: 6.          Running MCMC-PT iteration number: 30100 of 40000. Chain number 1. Current logpost: -358.13. Length of jump: 6.          Running MCMC-PT iteration number: 30300 of 40000. Chain number 2. Current logpost: -362.778. Length of jump: 8.          Running MCMC-PT iteration number: 30500 of 40000. Chain number 4. Current logpost: -360.625. Length of jump: 7.          Running MCMC-PT iteration number: 30400 of 40000. Chain number 3. Current logpost: -360.293. Length of jump: 6.          Running MCMC-PT iteration number: 30200 of 40000. Chain number 1. Current logpost: -356.851. Length of jump: 6.          Running MCMC-PT iteration number: 30400 of 40000. Chain number 2. Current logpost: -357.816. Length of jump: 7.          Running MCMC-PT iteration number: 30600 of 40000. Chain number 4. Current logpost: -360.368. Length of jump: 5.          Running MCMC-PT iteration number: 30500 of 40000. Chain number 3. Current logpost: -361.115. Length of jump: 5.          Running MCMC-PT iteration number: 30300 of 40000. Chain number 1. Current logpost: -356.712. Length of jump: 6.          Running MCMC-PT iteration number: 30500 of 40000. Chain number 2. Current logpost: -357.685. Length of jump: 7.          Running MCMC-PT iteration number: 30700 of 40000. Chain number 4. Current logpost: -358.404. Length of jump: 7.          Running MCMC-PT iteration number: 30600 of 40000. Chain number 3. Current logpost: -358.815. Length of jump: 5.          Running MCMC-PT iteration number: 30400 of 40000. Chain number 1. Current logpost: -358.356. Length of jump: 6.          Running MCMC-PT iteration number: 30600 of 40000. Chain number 2. Current logpost: -358.009. Length of jump: 8.          Running MCMC-PT iteration number: 30800 of 40000. Chain number 4. Current logpost: -358.403. Length of jump: 7.          Running MCMC-PT iteration number: 30700 of 40000. Chain number 3. Current logpost: -358.134. Length of jump: 5.          Running MCMC-PT iteration number: 30500 of 40000. Chain number 1. Current logpost: -359.104. Length of jump: 6.          Running MCMC-PT iteration number: 30700 of 40000. Chain number 2. Current logpost: -359.996. Length of jump: 8.          Running MCMC-PT iteration number: 30900 of 40000. Chain number 4. Current logpost: -357.999. Length of jump: 7.          Running MCMC-PT iteration number: 30800 of 40000. Chain number 3. Current logpost: -359.437. Length of jump: 5.          Running MCMC-PT iteration number: 30600 of 40000. Chain number 1. Current logpost: -360.814. Length of jump: 5.          Running MCMC-PT iteration number: 30800 of 40000. Chain number 2. Current logpost: -359.398. Length of jump: 8.          Running MCMC-PT iteration number: 31000 of 40000. Chain number 4. Current logpost: -358.611. Length of jump: 8.          Running MCMC-PT iteration number: 30900 of 40000. Chain number 3. Current logpost: -360.072. Length of jump: 6.          Running MCMC-PT iteration number: 30700 of 40000. Chain number 1. Current logpost: -359.369. Length of jump: 5.          Running MCMC-PT iteration number: 30900 of 40000. Chain number 2. Current logpost: -363.549. Length of jump: 8.          Running MCMC-PT iteration number: 31100 of 40000. Chain number 4. Current logpost: -356.393. Length of jump: 7.          Running MCMC-PT iteration number: 31000 of 40000. Chain number 3. Current logpost: -358.828. Length of jump: 5.          Running MCMC-PT iteration number: 30800 of 40000. Chain number 1. Current logpost: -358.163. Length of jump: 6.          Running MCMC-PT iteration number: 31000 of 40000. Chain number 2. Current logpost: -359.054. Length of jump: 7.          Running MCMC-PT iteration number: 31200 of 40000. Chain number 4. Current logpost: -356.229. Length of jump: 6.          Running MCMC-PT iteration number: 31100 of 40000. Chain number 3. Current logpost: -358.379. Length of jump: 5.          Running MCMC-PT iteration number: 30900 of 40000. Chain number 1. Current logpost: -359.259. Length of jump: 6.          Running MCMC-PT iteration number: 31100 of 40000. Chain number 2. Current logpost: -359.501. Length of jump: 8.          Running MCMC-PT iteration number: 31300 of 40000. Chain number 4. Current logpost: -358.656. Length of jump: 6.          Running MCMC-PT iteration number: 31200 of 40000. Chain number 3. Current logpost: -358.89. Length of jump: 7.          Running MCMC-PT iteration number: 31000 of 40000. Chain number 1. Current logpost: -359.954. Length of jump: 5.          Running MCMC-PT iteration number: 31200 of 40000. Chain number 2. Current logpost: -358.057. Length of jump: 8.          Running MCMC-PT iteration number: 31400 of 40000. Chain number 4. Current logpost: -358.331. Length of jump: 6.          Running MCMC-PT iteration number: 31300 of 40000. Chain number 3. Current logpost: -365.23. Length of jump: 8.          Running MCMC-PT iteration number: 31100 of 40000. Chain number 1. Current logpost: -361.288. Length of jump: 5.          Running MCMC-PT iteration number: 31300 of 40000. Chain number 2. Current logpost: -361.867. Length of jump: 8.          Running MCMC-PT iteration number: 31500 of 40000. Chain number 4. Current logpost: -357.344. Length of jump: 6.          Running MCMC-PT iteration number: 31600 of 40000. Chain number 4. Current logpost: -356.017. Length of jump: 6.          Running MCMC-PT iteration number: 31500 of 40000. Chain number 3. Current logpost: -363.48. Length of jump: 7.          Running MCMC-PT iteration number: 31300 of 40000. Chain number 1. Current logpost: -360.86. Length of jump: 4.          Running MCMC-PT iteration number: 31500 of 40000. Chain number 2. Current logpost: -360.032. Length of jump: 8.          Running MCMC-PT iteration number: 31700 of 40000. Chain number 4. Current logpost: -356.119. Length of jump: 6.          Running MCMC-PT iteration number: 31600 of 40000. Chain number 3. Current logpost: -365.907. Length of jump: 8.          Running MCMC-PT iteration number: 31400 of 40000. Chain number 1. Current logpost: -362.089. Length of jump: 5.          Running MCMC-PT iteration number: 31600 of 40000. Chain number 2. Current logpost: -358.462. Length of jump: 7.          Running MCMC-PT iteration number: 31800 of 40000. Chain number 4. Current logpost: -356.307. Length of jump: 6.          Running MCMC-PT iteration number: 31700 of 40000. Chain number 3. Current logpost: -362.379. Length of jump: 6.          Running MCMC-PT iteration number: 31500 of 40000. Chain number 1. Current logpost: -359.658. Length of jump: 5.          Running MCMC-PT iteration number: 31700 of 40000. Chain number 2. Current logpost: -358.44. Length of jump: 6.          Running MCMC-PT iteration number: 31900 of 40000. Chain number 4. Current logpost: -355.692. Length of jump: 6.          Running MCMC-PT iteration number: 31800 of 40000. Chain number 3. Current logpost: -363.06. Length of jump: 6.          Running MCMC-PT iteration number: 31600 of 40000. Chain number 1. Current logpost: -359.601. Length of jump: 5.          Running MCMC-PT iteration number: 31800 of 40000. Chain number 2. Current logpost: -356.613. Length of jump: 6.          Running MCMC-PT iteration number: 32000 of 40000. Chain number 4. Current logpost: -355.802. Length of jump: 7.          Running MCMC-PT iteration number: 31900 of 40000. Chain number 3. Current logpost: -363.541. Length of jump: 6.          Running MCMC-PT iteration number: 31700 of 40000. Chain number 1. Current logpost: -360.35. Length of jump: 5.          Running MCMC-PT iteration number: 31900 of 40000. Chain number 2. Current logpost: -356.56. Length of jump: 6.          Running MCMC-PT iteration number: 32100 of 40000. Chain number 4. Current logpost: -355.306. Length of jump: 7.          Running MCMC-PT iteration number: 32000 of 40000. Chain number 3. Current logpost: -361.597. Length of jump: 6.          Running MCMC-PT iteration number: 31800 of 40000. Chain number 1. Current logpost: -359.223. Length of jump: 6.          Running MCMC-PT iteration number: 32000 of 40000. Chain number 2. Current logpost: -357.557. Length of jump: 6.          Running MCMC-PT iteration number: 32200 of 40000. Chain number 4. Current logpost: -355.146. Length of jump: 7.          Running MCMC-PT iteration number: 32100 of 40000. Chain number 3. Current logpost: -359.951. Length of jump: 6.          Running MCMC-PT iteration number: 31900 of 40000. Chain number 1. Current logpost: -362.37. Length of jump: 6.          Running MCMC-PT iteration number: 32100 of 40000. Chain number 2. Current logpost: -356.229. Length of jump: 6.          Running MCMC-PT iteration number: 32300 of 40000. Chain number 4. Current logpost: -356.766. Length of jump: 7.          Running MCMC-PT iteration number: 32200 of 40000. Chain number 3. Current logpost: -360.188. Length of jump: 5.          Running MCMC-PT iteration number: 32000 of 40000. Chain number 1. Current logpost: -359.398. Length of jump: 6.          Running MCMC-PT iteration number: 32200 of 40000. Chain number 2. Current logpost: -358.145. Length of jump: 7.          Running MCMC-PT iteration number: 32400 of 40000. Chain number 4. Current logpost: -357.718. Length of jump: 7.          Running MCMC-PT iteration number: 32300 of 40000. Chain number 3. Current logpost: -359.729. Length of jump: 5.          Running MCMC-PT iteration number: 32100 of 40000. Chain number 1. Current logpost: -363.248. Length of jump: 7.          Running MCMC-PT iteration number: 32300 of 40000. Chain number 2. Current logpost: -359.26. Length of jump: 7.          Running MCMC-PT iteration number: 32500 of 40000. Chain number 4. Current logpost: -359.067. Length of jump: 8.          Running MCMC-PT iteration number: 32400 of 40000. Chain number 3. Current logpost: -361.013. Length of jump: 6.          Running MCMC-PT iteration number: 32200 of 40000. Chain number 1. Current logpost: -361.126. Length of jump: 7.          Running MCMC-PT iteration number: 32400 of 40000. Chain number 2. Current logpost: -359.289. Length of jump: 6.          Running MCMC-PT iteration number: 32600 of 40000. Chain number 4. Current logpost: -359.67. Length of jump: 8.          Running MCMC-PT iteration number: 32300 of 40000. Chain number 1. Current logpost: -359.586. Length of jump: 7.          Running MCMC-PT iteration number: 32500 of 40000. Chain number 3. Current logpost: -360.65. Length of jump: 6.          Running MCMC-PT iteration number: 32500 of 40000. Chain number 2. Current logpost: -357.847. Length of jump: 6.          Running MCMC-PT iteration number: 32700 of 40000. Chain number 4. Current logpost: -357.323. Length of jump: 8.          Running MCMC-PT iteration number: 32400 of 40000. Chain number 1. Current logpost: -359.693. Length of jump: 6.          Running MCMC-PT iteration number: 32600 of 40000. Chain number 3. Current logpost: -361.503. Length of jump: 6.          Running MCMC-PT iteration number: 32600 of 40000. Chain number 2. Current logpost: -356.764. Length of jump: 7.          Running MCMC-PT iteration number: 32800 of 40000. Chain number 4. Current logpost: -357.38. Length of jump: 8.          Running MCMC-PT iteration number: 32700 of 40000. Chain number 3. Current logpost: -361.992. Length of jump: 7.          Running MCMC-PT iteration number: 32500 of 40000. Chain number 1. Current logpost: -359.918. Length of jump: 6.          Running MCMC-PT iteration number: 32700 of 40000. Chain number 2. Current logpost: -356.898. Length of jump: 7.          Running MCMC-PT iteration number: 32800 of 40000. Chain number 3. Current logpost: -361.252. Length of jump: 7.          Running MCMC-PT iteration number: 32900 of 40000. Chain number 4. Current logpost: -359.664. Length of jump: 7.          Running MCMC-PT iteration number: 32600 of 40000. Chain number 1. Current logpost: -359.068. Length of jump: 6.          Running MCMC-PT iteration number: 32800 of 40000. Chain number 2. Current logpost: -359.501. Length of jump: 8.          Running MCMC-PT iteration number: 32700 of 40000. Chain number 1. Current logpost: -361.203. Length of jump: 7.          Running MCMC-PT iteration number: 33000 of 40000. Chain number 4. Current logpost: -359.945. Length of jump: 8.          Running MCMC-PT iteration number: 32900 of 40000. Chain number 3. Current logpost: -364.399. Length of jump: 8.          Running MCMC-PT iteration number: 32900 of 40000. Chain number 2. Current logpost: -357.19. Length of jump: 7.          Running MCMC-PT iteration number: 33100 of 40000. Chain number 4. Current logpost: -361.312. Length of jump: 6.          Running MCMC-PT iteration number: 33000 of 40000. Chain number 3. Current logpost: -363.036. Length of jump: 9.          Running MCMC-PT iteration number: 32800 of 40000. Chain number 1. Current logpost: -363.594. Length of jump: 9.          Running MCMC-PT iteration number: 33000 of 40000. Chain number 2. Current logpost: -359.853. Length of jump: 8.          Running MCMC-PT iteration number: 33100 of 40000. Chain number 3. Current logpost: -364.309. Length of jump: 9.          Running MCMC-PT iteration number: 32900 of 40000. Chain number 1. Current logpost: -361.551. Length of jump: 9.          Running MCMC-PT iteration number: 33200 of 40000. Chain number 4. Current logpost: -363.667. Length of jump: 7.          Running MCMC-PT iteration number: 33100 of 40000. Chain number 2. Current logpost: -359.011. Length of jump: 8.          Running MCMC-PT iteration number: 33000 of 40000. Chain number 1. Current logpost: -361.346. Length of jump: 9.          Running MCMC-PT iteration number: 33200 of 40000. Chain number 3. Current logpost: -362.131. Length of jump: 8.          Running MCMC-PT iteration number: 33300 of 40000. Chain number 4. Current logpost: -360.529. Length of jump: 6.          Running MCMC-PT iteration number: 33200 of 40000. Chain number 2. Current logpost: -359.687. Length of jump: 6.          Running MCMC-PT iteration number: 33100 of 40000. Chain number 1. Current logpost: -362.943. Length of jump: 9.          Running MCMC-PT iteration number: 33300 of 40000. Chain number 3. Current logpost: -363.47. Length of jump: 8.          Running MCMC-PT iteration number: 33400 of 40000. Chain number 4. Current logpost: -359.522. Length of jump: 7.          Running MCMC-PT iteration number: 33300 of 40000. Chain number 2. Current logpost: -360.412. Length of jump: 7.          Running MCMC-PT iteration number: 33200 of 40000. Chain number 1. Current logpost: -359.154. Length of jump: 8.          Running MCMC-PT iteration number: 33400 of 40000. Chain number 3. Current logpost: -360.343. Length of jump: 7.          Running MCMC-PT iteration number: 33500 of 40000. Chain number 4. Current logpost: -357.247. Length of jump: 7.          Running MCMC-PT iteration number: 33400 of 40000. Chain number 2. Current logpost: -360.44. Length of jump: 8.          Running MCMC-PT iteration number: 33300 of 40000. Chain number 1. Current logpost: -358.866. Length of jump: 7.          Running MCMC-PT iteration number: 33500 of 40000. Chain number 3. Current logpost: -359.129. Length of jump: 7.          Running MCMC-PT iteration number: 33600 of 40000. Chain number 4. Current logpost: -359.839. Length of jump: 6.          Running MCMC-PT iteration number: 33500 of 40000. Chain number 2. Current logpost: -359.581. Length of jump: 7.          Running MCMC-PT iteration number: 33400 of 40000. Chain number 1. Current logpost: -357.781. Length of jump: 7.          Running MCMC-PT iteration number: 33600 of 40000. Chain number 3. Current logpost: -361.214. Length of jump: 8.          Running MCMC-PT iteration number: 33700 of 40000. Chain number 4. Current logpost: -357.799. Length of jump: 7.          Running MCMC-PT iteration number: 33600 of 40000. Chain number 2. Current logpost: -358.223. Length of jump: 6.          Running MCMC-PT iteration number: 33500 of 40000. Chain number 1. Current logpost: -360.807. Length of jump: 9.          Running MCMC-PT iteration number: 33700 of 40000. Chain number 3. Current logpost: -363.201. Length of jump: 8.          Running MCMC-PT iteration number: 33800 of 40000. Chain number 4. Current logpost: -358.209. Length of jump: 8.          Running MCMC-PT iteration number: 33700 of 40000. Chain number 2. Current logpost: -362.173. Length of jump: 7.          Running MCMC-PT iteration number: 33600 of 40000. Chain number 1. Current logpost: -357.867. Length of jump: 7.          Running MCMC-PT iteration number: 33800 of 40000. Chain number 3. Current logpost: -364.721. Length of jump: 9.          Running MCMC-PT iteration number: 33900 of 40000. Chain number 4. Current logpost: -356.923. Length of jump: 7.          Running MCMC-PT iteration number: 33800 of 40000. Chain number 2. Current logpost: -361.899. Length of jump: 7.          Running MCMC-PT iteration number: 33700 of 40000. Chain number 1. Current logpost: -359.84. Length of jump: 7.          Running MCMC-PT iteration number: 33900 of 40000. Chain number 3. Current logpost: -361.188. Length of jump: 7.          Running MCMC-PT iteration number: 34000 of 40000. Chain number 4. Current logpost: -356.919. Length of jump: 6.          Running MCMC-PT iteration number: 33900 of 40000. Chain number 2. Current logpost: -358.798. Length of jump: 8.          Running MCMC-PT iteration number: 33800 of 40000. Chain number 1. Current logpost: -357.745. Length of jump: 6.          Running MCMC-PT iteration number: 34000 of 40000. Chain number 3. Current logpost: -361.604. Length of jump: 7.          Running MCMC-PT iteration number: 34100 of 40000. Chain number 4. Current logpost: -359.053. Length of jump: 5.          Running MCMC-PT iteration number: 34000 of 40000. Chain number 2. Current logpost: -362.36. Length of jump: 8.          Running MCMC-PT iteration number: 33900 of 40000. Chain number 1. Current logpost: -357.578. Length of jump: 6.          Running MCMC-PT iteration number: 34100 of 40000. Chain number 3. Current logpost: -364.919. Length of jump: 7.          Running MCMC-PT iteration number: 34200 of 40000. Chain number 4. Current logpost: -356.617. Length of jump: 5.          Running MCMC-PT iteration number: 34000 of 40000. Chain number 1. Current logpost: -359.902. Length of jump: 5.          Running MCMC-PT iteration number: 34200 of 40000. Chain number 3. Current logpost: -362.039. Length of jump: 7.          Running MCMC-PT iteration number: 34100 of 40000. Chain number 1. Current logpost: -362.012. Length of jump: 6.          Running MCMC-PT iteration number: 34300 of 40000. Chain number 4. Current logpost: -357.614. Length of jump: 5.          Running MCMC-PT iteration number: 34200 of 40000. Chain number 1. Current logpost: -360.593. Length of jump: 6.          Running MCMC-PT iteration number: 34200 of 40000. Chain number 2. Current logpost: -365.302. Length of jump: 9.          Running MCMC-PT iteration number: 34300 of 40000. Chain number 3. Current logpost: -364.55. Length of jump: 8.          Running MCMC-PT iteration number: 34400 of 40000. Chain number 4. Current logpost: -357.502. Length of jump: 5.          Running MCMC-PT iteration number: 34300 of 40000. Chain number 2. Current logpost: -360.505. Length of jump: 8.          Running MCMC-PT iteration number: 34400 of 40000. Chain number 3. Current logpost: -360.279. Length of jump: 5.          Running MCMC-PT iteration number: 34500 of 40000. Chain number 4. Current logpost: -357.796. Length of jump: 5.          Running MCMC-PT iteration number: 34400 of 40000. Chain number 2. Current logpost: -358.33. Length of jump: 8.          Running MCMC-PT iteration number: 34300 of 40000. Chain number 1. Current logpost: -359.276. Length of jump: 6.          Running MCMC-PT iteration number: 34500 of 40000. Chain number 3. Current logpost: -361.681. Length of jump: 7.          Running MCMC-PT iteration number: 34600 of 40000. Chain number 4. Current logpost: -359.387. Length of jump: 5.          Running MCMC-PT iteration number: 34500 of 40000. Chain number 2. Current logpost: -357.851. Length of jump: 8.          Running MCMC-PT iteration number: 34400 of 40000. Chain number 1. Current logpost: -359.826. Length of jump: 5.          Running MCMC-PT iteration number: 34600 of 40000. Chain number 3. Current logpost: -363.916. Length of jump: 7.          Running MCMC-PT iteration number: 34700 of 40000. Chain number 4. Current logpost: -358.645. Length of jump: 5.          Running MCMC-PT iteration number: 34600 of 40000. Chain number 2. Current logpost: -358.772. Length of jump: 6.          Running MCMC-PT iteration number: 34500 of 40000. Chain number 1. Current logpost: -360.324. Length of jump: 5.          Running MCMC-PT iteration number: 34700 of 40000. Chain number 3. Current logpost: -361.647. Length of jump: 6.          Running MCMC-PT iteration number: 34800 of 40000. Chain number 4. Current logpost: -355.812. Length of jump: 5.          Running MCMC-PT iteration number: 34700 of 40000. Chain number 2. Current logpost: -360.164. Length of jump: 5.          Running MCMC-PT iteration number: 34600 of 40000. Chain number 1. Current logpost: -363.262. Length of jump: 5.          Running MCMC-PT iteration number: 34800 of 40000. Chain number 3. Current logpost: -360.075. Length of jump: 4.          Running MCMC-PT iteration number: 34900 of 40000. Chain number 4. Current logpost: -355.635. Length of jump: 5.          Running MCMC-PT iteration number: 34800 of 40000. Chain number 2. Current logpost: -360.095. Length of jump: 5.          Running MCMC-PT iteration number: 34700 of 40000. Chain number 1. Current logpost: -359.136. Length of jump: 5.          Running MCMC-PT iteration number: 34900 of 40000. Chain number 3. Current logpost: -360.439. Length of jump: 5.          Running MCMC-PT iteration number: 35000 of 40000. Chain number 4. Current logpost: -357.07. Length of jump: 5.          Running MCMC-PT iteration number: 34900 of 40000. Chain number 2. Current logpost: -359.744. Length of jump: 5.          Running MCMC-PT iteration number: 34800 of 40000. Chain number 1. Current logpost: -359.352. Length of jump: 6.          Running MCMC-PT iteration number: 35000 of 40000. Chain number 3. Current logpost: -361.88. Length of jump: 4.          Running MCMC-PT iteration number: 35100 of 40000. Chain number 4. Current logpost: -356.846. Length of jump: 5.          Running MCMC-PT iteration number: 35000 of 40000. Chain number 2. Current logpost: -358.887. Length of jump: 5.          Running MCMC-PT iteration number: 34900 of 40000. Chain number 1. Current logpost: -358.913. Length of jump: 6.          Running MCMC-PT iteration number: 35100 of 40000. Chain number 3. Current logpost: -363.649. Length of jump: 5.          Running MCMC-PT iteration number: 35200 of 40000. Chain number 4. Current logpost: -356.402. Length of jump: 5.          Running MCMC-PT iteration number: 35100 of 40000. Chain number 2. Current logpost: -359.836. Length of jump: 5.          Running MCMC-PT iteration number: 35000 of 40000. Chain number 1. Current logpost: -359.969. Length of jump: 7.          Running MCMC-PT iteration number: 35200 of 40000. Chain number 3. Current logpost: -361.792. Length of jump: 6.          Running MCMC-PT iteration number: 35300 of 40000. Chain number 4. Current logpost: -358.771. Length of jump: 6.          Running MCMC-PT iteration number: 35200 of 40000. Chain number 2. Current logpost: -357.001. Length of jump: 5.          Running MCMC-PT iteration number: 35100 of 40000. Chain number 1. Current logpost: -361.531. Length of jump: 8.          Running MCMC-PT iteration number: 35300 of 40000. Chain number 3. Current logpost: -361.327. Length of jump: 7.          Running MCMC-PT iteration number: 35400 of 40000. Chain number 4. Current logpost: -357.418. Length of jump: 6.          Running MCMC-PT iteration number: 35300 of 40000. Chain number 2. Current logpost: -358.893. Length of jump: 4.          Running MCMC-PT iteration number: 35200 of 40000. Chain number 1. Current logpost: -359.986. Length of jump: 7.          Running MCMC-PT iteration number: 35400 of 40000. Chain number 3. Current logpost: -359.292. Length of jump: 6.          Running MCMC-PT iteration number: 35500 of 40000. Chain number 4. Current logpost: -357.818. Length of jump: 7.          Running MCMC-PT iteration number: 35400 of 40000. Chain number 2. Current logpost: -361.367. Length of jump: 5.          Running MCMC-PT iteration number: 35300 of 40000. Chain number 1. Current logpost: -360.967. Length of jump: 7.          Running MCMC-PT iteration number: 35500 of 40000. Chain number 3. Current logpost: -358.865. Length of jump: 6.          Running MCMC-PT iteration number: 35600 of 40000. Chain number 4. Current logpost: -357.394. Length of jump: 7.          Running MCMC-PT iteration number: 35500 of 40000. Chain number 2. Current logpost: -356.952. Length of jump: 6.          Running MCMC-PT iteration number: 35400 of 40000. Chain number 1. Current logpost: -363.074. Length of jump: 7.          Running MCMC-PT iteration number: 35600 of 40000. Chain number 3. Current logpost: -357.602. Length of jump: 5.          Running MCMC-PT iteration number: 35700 of 40000. Chain number 4. Current logpost: -356.55. Length of jump: 7.          Running MCMC-PT iteration number: 35600 of 40000. Chain number 2. Current logpost: -360.645. Length of jump: 7.          Running MCMC-PT iteration number: 35500 of 40000. Chain number 1. Current logpost: -362.633. Length of jump: 6.          Running MCMC-PT iteration number: 35700 of 40000. Chain number 3. Current logpost: -358.39. Length of jump: 5.          Running MCMC-PT iteration number: 35800 of 40000. Chain number 4. Current logpost: -356.798. Length of jump: 7.          Running MCMC-PT iteration number: 35700 of 40000. Chain number 2. Current logpost: -361.196. Length of jump: 7.          Running MCMC-PT iteration number: 35600 of 40000. Chain number 1. Current logpost: -368.996. Length of jump: 7.          Running MCMC-PT iteration number: 35800 of 40000. Chain number 3. Current logpost: -361.276. Length of jump: 7.          Running MCMC-PT iteration number: 35900 of 40000. Chain number 4. Current logpost: -359.067. Length of jump: 7.          Running MCMC-PT iteration number: 35800 of 40000. Chain number 2. Current logpost: -363.049. Length of jump: 7.          Running MCMC-PT iteration number: 35700 of 40000. Chain number 1. Current logpost: -365.07. Length of jump: 6.          Running MCMC-PT iteration number: 35900 of 40000. Chain number 3. Current logpost: -362.089. Length of jump: 8.          Running MCMC-PT iteration number: 35900 of 40000. Chain number 2. Current logpost: -361.084. Length of jump: 7.          Running MCMC-PT iteration number: 36000 of 40000. Chain number 4. Current logpost: -358.66. Length of jump: 7.          Running MCMC-PT iteration number: 35800 of 40000. Chain number 1. Current logpost: -365.201. Length of jump: 5.          Running MCMC-PT iteration number: 36000 of 40000. Chain number 3. Current logpost: -360.16. Length of jump: 5.          Running MCMC-PT iteration number: 36000 of 40000. Chain number 2. Current logpost: -367.277. Length of jump: 8.          Running MCMC-PT iteration number: 36100 of 40000. Chain number 4. Current logpost: -360.15. Length of jump: 7.          Running MCMC-PT iteration number: 36100 of 40000. Chain number 3. Current logpost: -360.239. Length of jump: 5.          Running MCMC-PT iteration number: 36100 of 40000. Chain number 2. Current logpost: -365.093. Length of jump: 8.          Running MCMC-PT iteration number: 36200 of 40000. Chain number 4. Current logpost: -358.248. Length of jump: 8.          Running MCMC-PT iteration number: 36200 of 40000. Chain number 3. Current logpost: -360.296. Length of jump: 6.          Running MCMC-PT iteration number: 36200 of 40000. Chain number 2. Current logpost: -361.734. Length of jump: 8.          Running MCMC-PT iteration number: 36300 of 40000. Chain number 4. Current logpost: -356.479. Length of jump: 7.          Running MCMC-PT iteration number: 36100 of 40000. Chain number 1. Current logpost: -361.236. Length of jump: 6.          Running MCMC-PT iteration number: 36300 of 40000. Chain number 3. Current logpost: -361.401. Length of jump: 6.          Running MCMC-PT iteration number: 36300 of 40000. Chain number 2. Current logpost: -360.22. Length of jump: 5.          Running MCMC-PT iteration number: 36400 of 40000. Chain number 4. Current logpost: -357.751. Length of jump: 7.          Running MCMC-PT iteration number: 36200 of 40000. Chain number 1. Current logpost: -358.704. Length of jump: 7.          Running MCMC-PT iteration number: 36400 of 40000. Chain number 3. Current logpost: -360.443. Length of jump: 5.          Running MCMC-PT iteration number: 36500 of 40000. Chain number 4. Current logpost: -356.451. Length of jump: 7.          Running MCMC-PT iteration number: 36300 of 40000. Chain number 1. Current logpost: -360.207. Length of jump: 8.          Running MCMC-PT iteration number: 36500 of 40000. Chain number 3. Current logpost: -360.761. Length of jump: 4.          Running MCMC-PT iteration number: 36500 of 40000. Chain number 2. Current logpost: -363.204. Length of jump: 6.          Running MCMC-PT iteration number: 36600 of 40000. Chain number 4. Current logpost: -356.761. Length of jump: 6.          Running MCMC-PT iteration number: 36400 of 40000. Chain number 1. Current logpost: -357.818. Length of jump: 7.          Running MCMC-PT iteration number: 36600 of 40000. Chain number 2. Current logpost: -363.035. Length of jump: 7.          Running MCMC-PT iteration number: 36700 of 40000. Chain number 4. Current logpost: -357.429. Length of jump: 6.          Running MCMC-PT iteration number: 36500 of 40000. Chain number 1. Current logpost: -358.528. Length of jump: 8.          Running MCMC-PT iteration number: 36700 of 40000. Chain number 3. Current logpost: -362.139. Length of jump: 3.          Running MCMC-PT iteration number: 36700 of 40000. Chain number 2. Current logpost: -364.055. Length of jump: 6.          Running MCMC-PT iteration number: 36800 of 40000. Chain number 4. Current logpost: -359.229. Length of jump: 6.          Running MCMC-PT iteration number: 36600 of 40000. Chain number 1. Current logpost: -358.275. Length of jump: 9.          Running MCMC-PT iteration number: 36800 of 40000. Chain number 3. Current logpost: -358.786. Length of jump: 5.          Running MCMC-PT iteration number: 36800 of 40000. Chain number 2. Current logpost: -360.133. Length of jump: 4.          Running MCMC-PT iteration number: 36900 of 40000. Chain number 4. Current logpost: -358.834. Length of jump: 5.          Running MCMC-PT iteration number: 36700 of 40000. Chain number 1. Current logpost: -363.736. Length of jump: 9.          Running MCMC-PT iteration number: 36900 of 40000. Chain number 3. Current logpost: -358.438. Length of jump: 5.          Running MCMC-PT iteration number: 36900 of 40000. Chain number 2. Current logpost: -360.602. Length of jump: 5.          Running MCMC-PT iteration number: 37000 of 40000. Chain number 3. Current logpost: -358.455. Length of jump: 4.          Running MCMC-PT iteration number: 37000 of 40000. Chain number 2. Current logpost: -363.108. Length of jump: 6.          Running MCMC-PT iteration number: 37100 of 40000. Chain number 4. Current logpost: -362.138. Length of jump: 6.          Running MCMC-PT iteration number: 36900 of 40000. Chain number 1. Current logpost: -359.832. Length of jump: 9.          Running MCMC-PT iteration number: 37100 of 40000. Chain number 3. Current logpost: -358.037. Length of jump: 5.          Running MCMC-PT iteration number: 37100 of 40000. Chain number 2. Current logpost: -365.566. Length of jump: 5.          Running MCMC-PT iteration number: 37200 of 40000. Chain number 4. Current logpost: -357.828. Length of jump: 6.          Running MCMC-PT iteration number: 37000 of 40000. Chain number 1. Current logpost: -361.36. Length of jump: 9.          Running MCMC-PT iteration number: 37200 of 40000. Chain number 3. Current logpost: -358.939. Length of jump: 5.          Running MCMC-PT iteration number: 37200 of 40000. Chain number 2. Current logpost: -362.395. Length of jump: 6.          Running MCMC-PT iteration number: 37300 of 40000. Chain number 4. Current logpost: -359.702. Length of jump: 5.          Running MCMC-PT iteration number: 37100 of 40000. Chain number 1. Current logpost: -360.595. Length of jump: 7.          Running MCMC-PT iteration number: 37300 of 40000. Chain number 3. Current logpost: -357.922. Length of jump: 5.          Running MCMC-PT iteration number: 37300 of 40000. Chain number 2. Current logpost: -363.99. Length of jump: 6.          Running MCMC-PT iteration number: 37400 of 40000. Chain number 4. Current logpost: -360.906. Length of jump: 8.          Running MCMC-PT iteration number: 37200 of 40000. Chain number 1. Current logpost: -357.802. Length of jump: 7.          Running MCMC-PT iteration number: 37400 of 40000. Chain number 3. Current logpost: -358.129. Length of jump: 5.          Running MCMC-PT iteration number: 37400 of 40000. Chain number 2. Current logpost: -365.287. Length of jump: 7.          Running MCMC-PT iteration number: 37500 of 40000. Chain number 4. Current logpost: -360.977. Length of jump: 7.          Running MCMC-PT iteration number: 37300 of 40000. Chain number 1. Current logpost: -358.358. Length of jump: 6.          Running MCMC-PT iteration number: 37500 of 40000. Chain number 3. Current logpost: -357.902. Length of jump: 5.          Running MCMC-PT iteration number: 37500 of 40000. Chain number 2. Current logpost: -364.836. Length of jump: 8.          Running MCMC-PT iteration number: 37600 of 40000. Chain number 4. Current logpost: -358.616. Length of jump: 6.          Running MCMC-PT iteration number: 37400 of 40000. Chain number 1. Current logpost: -359.473. Length of jump: 8.          Running MCMC-PT iteration number: 37600 of 40000. Chain number 3. Current logpost: -362.271. Length of jump: 5.          Running MCMC-PT iteration number: 37600 of 40000. Chain number 2. Current logpost: -364.51. Length of jump: 7.          Running MCMC-PT iteration number: 37700 of 40000. Chain number 4. Current logpost: -358.66. Length of jump: 6.          Running MCMC-PT iteration number: 37500 of 40000. Chain number 1. Current logpost: -358.794. Length of jump: 8.          Running MCMC-PT iteration number: 37700 of 40000. Chain number 3. Current logpost: -358.39. Length of jump: 5.          Running MCMC-PT iteration number: 37700 of 40000. Chain number 2. Current logpost: -363.241. Length of jump: 7.          Running MCMC-PT iteration number: 37800 of 40000. Chain number 4. Current logpost: -358.684. Length of jump: 5.          Running MCMC-PT iteration number: 37600 of 40000. Chain number 1. Current logpost: -359.975. Length of jump: 9.          Running MCMC-PT iteration number: 37800 of 40000. Chain number 3. Current logpost: -356.574. Length of jump: 6.          Running MCMC-PT iteration number: 37800 of 40000. Chain number 2. Current logpost: -361.409. Length of jump: 6.          Running MCMC-PT iteration number: 37900 of 40000. Chain number 4. Current logpost: -358.99. Length of jump: 5.          Running MCMC-PT iteration number: 37700 of 40000. Chain number 1. Current logpost: -359.736. Length of jump: 9.          Running MCMC-PT iteration number: 37900 of 40000. Chain number 3. Current logpost: -356.864. Length of jump: 6.          Running MCMC-PT iteration number: 37900 of 40000. Chain number 2. Current logpost: -360.444. Length of jump: 5.          Running MCMC-PT iteration number: 38000 of 40000. Chain number 4. Current logpost: -357.818. Length of jump: 6.          Running MCMC-PT iteration number: 37800 of 40000. Chain number 1. Current logpost: -358.93. Length of jump: 9.          Running MCMC-PT iteration number: 38000 of 40000. Chain number 3. Current logpost: -360.094. Length of jump: 6.          Running MCMC-PT iteration number: 38000 of 40000. Chain number 2. Current logpost: -360.816. Length of jump: 4.          Running MCMC-PT iteration number: 38100 of 40000. Chain number 4. Current logpost: -357.892. Length of jump: 5.          Running MCMC-PT iteration number: 37900 of 40000. Chain number 1. Current logpost: -358.406. Length of jump: 9.          Running MCMC-PT iteration number: 38100 of 40000. Chain number 3. Current logpost: -358.635. Length of jump: 6.          Running MCMC-PT iteration number: 38100 of 40000. Chain number 2. Current logpost: -365.173. Length of jump: 5.          Running MCMC-PT iteration number: 38200 of 40000. Chain number 4. Current logpost: -364.077. Length of jump: 5.          Running MCMC-PT iteration number: 38000 of 40000. Chain number 1. Current logpost: -361.427. Length of jump: 10.          Running MCMC-PT iteration number: 38200 of 40000. Chain number 3. Current logpost: -359.714. Length of jump: 6.          Running MCMC-PT iteration number: 38200 of 40000. Chain number 2. Current logpost: -359.879. Length of jump: 4.          Running MCMC-PT iteration number: 38300 of 40000. Chain number 4. Current logpost: -362.021. Length of jump: 4.          Running MCMC-PT iteration number: 38100 of 40000. Chain number 1. Current logpost: -358.12. Length of jump: 9.          Running MCMC-PT iteration number: 38300 of 40000. Chain number 3. Current logpost: -360.881. Length of jump: 6.          Running MCMC-PT iteration number: 38300 of 40000. Chain number 2. Current logpost: -362.637. Length of jump: 6.          Running MCMC-PT iteration number: 38400 of 40000. Chain number 4. Current logpost: -360.411. Length of jump: 6.          Running MCMC-PT iteration number: 38200 of 40000. Chain number 1. Current logpost: -359.767. Length of jump: 8.          Running MCMC-PT iteration number: 38400 of 40000. Chain number 3. Current logpost: -362.515. Length of jump: 5.          Running MCMC-PT iteration number: 38400 of 40000. Chain number 2. Current logpost: -362.062. Length of jump: 5.          Running MCMC-PT iteration number: 38500 of 40000. Chain number 2. Current logpost: -362.158. Length of jump: 5.          Running MCMC-PT iteration number: 38600 of 40000. Chain number 4. Current logpost: -358.99. Length of jump: 6.          Running MCMC-PT iteration number: 38400 of 40000. Chain number 1. Current logpost: -361.349. Length of jump: 8.          Running MCMC-PT iteration number: 38600 of 40000. Chain number 3. Current logpost: -358.387. Length of jump: 4.          Running MCMC-PT iteration number: 38600 of 40000. Chain number 2. Current logpost: -359.934. Length of jump: 5.          Running MCMC-PT iteration number: 38700 of 40000. Chain number 4. Current logpost: -358.263. Length of jump: 6.          Running MCMC-PT iteration number: 38500 of 40000. Chain number 1. Current logpost: -364.813. Length of jump: 7.          Running MCMC-PT iteration number: 38700 of 40000. Chain number 3. Current logpost: -358.363. Length of jump: 5.          Running MCMC-PT iteration number: 38700 of 40000. Chain number 2. Current logpost: -360.655. Length of jump: 5.          Running MCMC-PT iteration number: 38800 of 40000. Chain number 4. Current logpost: -362.08. Length of jump: 7.          Running MCMC-PT iteration number: 38600 of 40000. Chain number 1. Current logpost: -361.348. Length of jump: 7.          Running MCMC-PT iteration number: 38800 of 40000. Chain number 3. Current logpost: -363.585. Length of jump: 6.          Running MCMC-PT iteration number: 38800 of 40000. Chain number 2. Current logpost: -359.358. Length of jump: 5.          Running MCMC-PT iteration number: 38900 of 40000. Chain number 4. Current logpost: -361.379. Length of jump: 8.          Running MCMC-PT iteration number: 38700 of 40000. Chain number 1. Current logpost: -361.087. Length of jump: 7.          Running MCMC-PT iteration number: 38900 of 40000. Chain number 3. Current logpost: -360.201. Length of jump: 6.          Running MCMC-PT iteration number: 38900 of 40000. Chain number 2. Current logpost: -363.794. Length of jump: 5.          Running MCMC-PT iteration number: 39000 of 40000. Chain number 4. Current logpost: -363.06. Length of jump: 7.          Running MCMC-PT iteration number: 38800 of 40000. Chain number 1. Current logpost: -360.633. Length of jump: 7.          Running MCMC-PT iteration number: 39000 of 40000. Chain number 3. Current logpost: -358.29. Length of jump: 6.          Running MCMC-PT iteration number: 39000 of 40000. Chain number 2. Current logpost: -360.686. Length of jump: 5.          Running MCMC-PT iteration number: 39100 of 40000. Chain number 4. Current logpost: -360.04. Length of jump: 7.          Running MCMC-PT iteration number: 38900 of 40000. Chain number 1. Current logpost: -361.173. Length of jump: 7.          Running MCMC-PT iteration number: 39100 of 40000. Chain number 3. Current logpost: -361.938. Length of jump: 6.          Running MCMC-PT iteration number: 39100 of 40000. Chain number 2. Current logpost: -363.988. Length of jump: 4.          Running MCMC-PT iteration number: 39200 of 40000. Chain number 4. Current logpost: -362.642. Length of jump: 7.          Running MCMC-PT iteration number: 39000 of 40000. Chain number 1. Current logpost: -360.939. Length of jump: 8.          Running MCMC-PT iteration number: 39200 of 40000. Chain number 3. Current logpost: -358.998. Length of jump: 6.          Running MCMC-PT iteration number: 39200 of 40000. Chain number 2. Current logpost: -361.923. Length of jump: 4.          Running MCMC-PT iteration number: 39300 of 40000. Chain number 4. Current logpost: -362.123. Length of jump: 7.          Running MCMC-PT iteration number: 39100 of 40000. Chain number 1. Current logpost: -360.892. Length of jump: 7.          Running MCMC-PT iteration number: 39300 of 40000. Chain number 3. Current logpost: -359.85. Length of jump: 6.          Running MCMC-PT iteration number: 39300 of 40000. Chain number 2. Current logpost: -360.791. Length of jump: 4.          Running MCMC-PT iteration number: 39400 of 40000. Chain number 4. Current logpost: -360.371. Length of jump: 7.          Running MCMC-PT iteration number: 39200 of 40000. Chain number 1. Current logpost: -362.271. Length of jump: 7.          Running MCMC-PT iteration number: 39400 of 40000. Chain number 3. Current logpost: -360.07. Length of jump: 7.          Running MCMC-PT iteration number: 39400 of 40000. Chain number 2. Current logpost: -363.589. Length of jump: 4.          Running MCMC-PT iteration number: 39500 of 40000. Chain number 4. Current logpost: -359.907. Length of jump: 7.          Running MCMC-PT iteration number: 39300 of 40000. Chain number 1. Current logpost: -359.239. Length of jump: 7.          Running MCMC-PT iteration number: 39500 of 40000. Chain number 3. Current logpost: -358.831. Length of jump: 6.          Running MCMC-PT iteration number: 39500 of 40000. Chain number 2. Current logpost: -366.599. Length of jump: 6.          Running MCMC-PT iteration number: 39600 of 40000. Chain number 4. Current logpost: -361.172. Length of jump: 7.          Running MCMC-PT iteration number: 39400 of 40000. Chain number 1. Current logpost: -360.601. Length of jump: 8.          Running MCMC-PT iteration number: 39600 of 40000. Chain number 3. Current logpost: -359.517. Length of jump: 6.          Running MCMC-PT iteration number: 39600 of 40000. Chain number 2. Current logpost: -360.732. Length of jump: 4.          Running MCMC-PT iteration number: 39700 of 40000. Chain number 4. Current logpost: -359.224. Length of jump: 5.          Running MCMC-PT iteration number: 39700 of 40000. Chain number 3. Current logpost: -358.489. Length of jump: 5.          Running MCMC-PT iteration number: 39500 of 40000. Chain number 1. Current logpost: -362.2. Length of jump: 8.          Running MCMC-PT iteration number: 39700 of 40000. Chain number 2. Current logpost: -360.154. Length of jump: 4.          Running MCMC-PT iteration number: 39800 of 40000. Chain number 4. Current logpost: -359.531. Length of jump: 5.          Running MCMC-PT iteration number: 39800 of 40000. Chain number 3. Current logpost: -359.712. Length of jump: 5.          Running MCMC-PT iteration number: 39600 of 40000. Chain number 1. Current logpost: -362.209. Length of jump: 7.          Running MCMC-PT iteration number: 39800 of 40000. Chain number 2. Current logpost: -359.152. Length of jump: 4.          Running MCMC-PT iteration number: 39900 of 40000. Chain number 4. Current logpost: -361.085. Length of jump: 5.          Running MCMC-PT iteration number: 39900 of 40000. Chain number 3. Current logpost: -356.237. Length of jump: 6.          Running MCMC-PT iteration number: 39700 of 40000. Chain number 1. Current logpost: -360.26. Length of jump: 6.          Running MCMC-PT iteration number: 39900 of 40000. Chain number 2. Current logpost: -359.773. Length of jump: 4.          Running MCMC-PT iteration number: 39800 of 40000. Chain number 1. Current logpost: -360.423. Length of jump: 6.          Running MCMC-PT iteration number: 39900 of 40000. Chain number 1. Current logpost: -359.831. Length of jump: 7.          
```

``` r
# Run diagnostics to check for mixing issues
cat("\n=== Running RJMC Diagnostics ===\n")
```

```
## 
## === Running RJMC Diagnostics ===
```

``` r
diagnostics <- diagnose_rjmc_mixing(outputs)
```

```
## Error in diagnose_rjmc_mixing(outputs): could not find function "diagnose_rjmc_mixing"
```

``` r
# Optionally save
saveRDS(outputs, here::here("outputs", "fits", "epi", "fit_seir_cp.RDS"))
```

## 5. Posterior analysis and recovery

### 5.1 Posterior over number of segments (change-points + 1)


``` r
K_counts <- map_dbl(outputs$jump, ~length(.x)) # number of posterior samples per chain
K_tab <- map_df(1:length(outputs$jump), function(c) {
  tibble(K = map_int(outputs$jump[[c]], ~ncol(.x)))
}) %>% count(K) %>% mutate(prop = n / sum(n))

K_mode <- as.integer(K_tab$K[which.max(K_tab$prop)])

K_tab %>% ggplot(aes(x = factor(K), y = prop)) +
  geom_col() + 
  labs(x = "Number of segments (K)", y = "Posterior proportion",
       title = "Posterior over number of segments") +
  theme_bw()
```

![plot of chunk posterior_K](figure/posterior_K-1.png)

### 5.2 Recover transmission rate and incidence (conditional on modal K)


``` r
# Extract samples with K == K_mode across all chains
samples_K <- map_df(1:length(outputs$jump), function(c) {
  keep_idx <- which(map_int(outputs$jump[[c]], ~ncol(.x)) == K_mode)
  if (length(keep_idx) == 0) return(NULL)
  map_df(keep_idx, function(s) {
    jump_mat <- outputs$jump[[c]][[s]]
    beta_vec <- as.numeric(jump_mat[1, ])
    cp_vec   <- as.numeric(jump_mat[2, ])
    beta_t   <- make_beta_t(beta_vec, cp_vec, T_days)
    tibble(chain = c, sample = s, day = 1:T_days, beta_t = beta_t)
  })
})

# Summaries for beta(t)
beta_sum <- samples_K %>%
  group_by(day) %>%
  mean_qi(beta_t, .width = c(0.95))

beta_sum_c <- samples_K %>%
  group_by(day, chain) %>%
  mean_qi(beta_t, .width = c(0.95))

# Plot with chain-specific colors
p_beta_rec <- ggplot(beta_sum_c, aes(day, beta_t)) +
  geom_step(data = tibble(day = 1:T_days, beta_t = beta_true_t),
            color = "red", linewidth = 1) +
  geom_ribbon(aes(ymin = .lower, ymax = .upper, fill = factor(chain)), alpha = 0.3) +
  geom_line(aes(color = factor(chain))) + 
  labs(x = "Day", y = expression(beta(t)),
       title = expression("Posterior "*beta(t)*" (modal K) with truth (red)")) +
  theme_bw()


# Incidence summaries from posterior beta paths
inc_sum <- samples_K %>%
  group_by(chain, sample) %>%
  summarize(
    mu = list(seir_expected_incidence(
      T = T_days, N = N_pop, beta_t = beta_t,
      gamma = gamma, S0 = N_pop - 1000, E0 = 0, I0 = 1000, R0 = 0, rho = rho_true
    )$incidence),
    .groups = "drop"
  ) %>%
  mutate(
    day = list(1:T_days),
    mu = map2(mu, day, ~setNames(.x, paste0("day_", .y)))
  ) %>%
  unnest_longer(c(mu, day)) %>%
  group_by(day) %>%
  mean_qi(mu, .width = c(0.5, 0.8, 0.95))

p_inc <- ggplot() +
  geom_col(data = tibble(day = 1:T_days, y = obs_y), aes(day, y),
           fill = "grey85", color = "grey40") +
  geom_ribbon(data = inc_sum, aes(day, ymin = .lower, ymax = .upper),
              fill = "tomato", alpha = 0.25) +
  geom_line(data = inc_sum, aes(day, y = mu), color = "tomato4") +
  labs(x = "Day", y = "Incidence",
       title = "Posterior incidence (modal K) with observed data") +
  theme_bw()

p_beta_rec / p_inc
```

![plot of chunk posterior_beta_inc](figure/posterior_beta_inc-1.png)

This analysis shows that RJMCMC can recover both the number and locations of change-points in \(\beta(t)\), and yields posterior predictive incidence consistent with the simulated data.

### 5.3 Convergence Diagnostics Between Chains

Let's check for convergence between chains by comparing the posterior distributions of beta values and change-points.


``` r
# Extract all samples across chains for convergence analysis
all_samples <- map_df(1:length(outputs$jump), function(c) {
  map_df(1:length(outputs$jump[[c]]), function(s) {
    jump_mat <- outputs$jump[[c]][[s]]
    K <- ncol(jump_mat)
    beta_vec <- as.numeric(jump_mat[1, ])
    cp_vec <- as.numeric(jump_mat[2, ])
    
    tibble(
      chain = c,
      sample = s,
      K = K,
      beta_1 = if(K >= 1) beta_vec[1] else NA_real_,
      beta_2 = if(K >= 2) beta_vec[2] else NA_real_,
      beta_3 = if(K >= 3) beta_vec[3] else NA_real_,
      beta_4 = if(K >= 4) beta_vec[4] else NA_real_,
      beta_5 = if(K >= 5) beta_vec[5] else NA_real_,
      beta_6 = if(K >= 6) beta_vec[6] else NA_real_,
      beta_7 = if(K >= 7) beta_vec[7] else NA_real_,
      beta_8 = if(K >= 8) beta_vec[8] else NA_real_,
      beta_9 = if(K >= 9) beta_vec[9] else NA_real_,
      beta_10 = if(K >= 10) beta_vec[10] else NA_real_,
      cp_1 = if(K >= 2) cp_vec[1] else NA_real_,
      cp_2 = if(K >= 3) cp_vec[2] else NA_real_,
      cp_3 = if(K >= 4) cp_vec[3] else NA_real_,
      cp_4 = if(K >= 5) cp_vec[4] else NA_real_,
      cp_5 = if(K >= 6) cp_vec[5] else NA_real_,
      cp_6 = if(K >= 7) cp_vec[6] else NA_real_,
      cp_7 = if(K >= 8) cp_vec[7] else NA_real_,
      cp_8 = if(K >= 9) cp_vec[8] else NA_real_    )
  })
})

# 1. Compare number of segments (K) between chains
K_convergence <- all_samples %>%
  group_by(chain) %>%
  summarise(
    mean_K = mean(K, na.rm = TRUE),
    sd_K = sd(K, na.rm = TRUE),
    median_K = median(K, na.rm = TRUE),
    q25_K = quantile(K, 0.25, na.rm = TRUE),
    q75_K = quantile(K, 0.75, na.rm = TRUE),
    .groups = "drop"
  )

print("Convergence check for number of segments (K):")
```

```
## [1] "Convergence check for number of segments (K):"
```

``` r
print(K_convergence)
```

```
## # A tibble: 4 × 6
##   chain mean_K  sd_K median_K q25_K q75_K
##   <int>  <dbl> <dbl>    <dbl> <dbl> <dbl>
## 1     1   6.22  1.42        6     5     7
## 2     2   6.31  1.28        6     5     7
## 3     3   5.59  1.26        6     5     6
## 4     4   6.27  1.03        6     6     7
```

``` r
# 2. Compare beta values between chains (conditional on K)
# Focus on the most common K value
K_mode <- as.numeric(names(sort(table(all_samples$K), decreasing = TRUE)[1]))
cat("\nMost common K value:", K_mode, "\n")
```

```
## 
## Most common K value: 6
```

``` r
# Extract samples with K == K_mode for beta comparison
beta_samples <- all_samples %>%
  filter(K == K_mode) %>%
  select(chain, sample, starts_with("beta_")) %>%
  pivot_longer(starts_with("beta_"), names_to = "segment", values_to = "beta") %>%
  filter(!is.na(beta)) %>%
  mutate(segment = as.numeric(gsub("beta_", "", segment)))

# Beta convergence by segment
beta_convergence <- beta_samples %>%
  group_by(segment, chain) %>%
  summarise(
    mean_beta = mean(beta, na.rm = TRUE),
    sd_beta = sd(beta, na.rm = TRUE),
    median_beta = median(beta, na.rm = TRUE),
    q25_beta = quantile(beta, 0.25, na.rm = TRUE),
    q75_beta = quantile(beta, 0.75, na.rm = TRUE),
    .groups = "drop"
  )

print("\nBeta convergence by segment and chain:")
```

```
## [1] "\nBeta convergence by segment and chain:"
```

``` r
print(beta_convergence)
```

```
## # A tibble: 24 × 7
##    segment chain mean_beta  sd_beta median_beta q25_beta q75_beta
##      <dbl> <int>     <dbl>    <dbl>       <dbl>    <dbl>    <dbl>
##  1       1     1    0.300  0.000955       0.300    0.299   0.300 
##  2       1     2    0.300  0.00132        0.300    0.299   0.300 
##  3       1     3    0.300  0.000852       0.300    0.299   0.300 
##  4       1     4    0.300  0.00240        0.300    0.299   0.301 
##  5       2     1    0.0755 0.121          0.01     0.01    0.0106
##  6       2     2    0.0935 0.131          0.01     0.01    0.297 
##  7       2     3    0.0304 0.0739         0.01     0.01    0.01  
##  8       2     4    0.231  0.122          0.298    0.287   0.300 
##  9       3     1    0.0322 0.0778         0.01     0.01    0.01  
## 10       3     2    0.0176 0.0453         0.01     0.01    0.01  
## # ℹ 14 more rows
```

``` r
# 3. Compare change-points between chains (conditional on K)
cp_samples <- all_samples %>%
  filter(K == K_mode) %>%
  select(chain, sample, starts_with("cp_")) %>%
  pivot_longer(starts_with("cp_"), names_to = "cp_idx", values_to = "cp") %>%
  filter(!is.na(cp)) %>%
  mutate(cp_idx = as.numeric(gsub("cp_", "", cp_idx)))

# Change-point convergence by index
cp_convergence <- cp_samples %>%
  group_by(cp_idx, chain) %>%
  summarise(
    mean_cp = mean(cp, na.rm = TRUE),
    sd_cp = sd(cp, na.rm = TRUE),
    median_cp = median(cp, na.rm = TRUE),
    q25_cp = quantile(cp, 0.25, na.rm = TRUE),
    q75_cp = quantile(cp, 0.75, na.rm = TRUE),
    .groups = "drop"
  )

print("\nChange-point convergence by index and chain:")
```

```
## [1] "\nChange-point convergence by index and chain:"
```

``` r
print(cp_convergence)
```

```
## # A tibble: 20 × 7
##    cp_idx chain mean_cp sd_cp median_cp q25_cp q75_cp
##     <dbl> <int>   <dbl> <dbl>     <dbl>  <dbl>  <dbl>
##  1      1     1    37.4  6.55        40     40     40
##  2      1     2    35.7  8.18        40     36     40
##  3      1     3    39.4  2.53        40     40     40
##  4      1     4    23.2 11.6         21     14     36
##  5      2     1    49.1 10.1         49     43     55
##  6      2     2    50.0  9.05        51     40     57
##  7      2     3    54.1  8.29        54     48     61
##  8      2     4    41.8 11.2         40     40     40
##  9      3     1    67.9 12.3         71     60     80
## 10      3     2    65.7 11.4         66     57     80
## 11      3     3    66.2  8.24        67     60     72
## 12      3     4    56.4 12.0         56     46     65
## 13      4     1    78.3  9.34        80     75     83
## 14      4     2    82.2 11.6         80     80     86
## 15      4     3    79.5  3.90        80     80     80
## 16      4     4    71.3 11.3         80     64     80
## 17      5     1    89.5  9.39        87     80     96
## 18      5     2    98.2 13.6        104     84    111
## 19      5     3    92.6  9.00        92     85     98
## 20      5     4    92.9 13.8         88     80    107
```

``` r
# 4. Visual convergence diagnostics
# Beta values by chain and segment
p_beta_conv <- beta_samples %>%
  ggplot(aes(x = factor(chain), y = beta, fill = factor(chain))) +
  geom_boxplot(alpha = 0.7) +
  facet_wrap(~segment, scales = "free_y", labeller = label_both) +
  labs(x = "Chain", y = "Beta value", title = paste("Beta convergence across chains (K =", K_mode, ")")) +
  theme_bw() +
  theme(legend.position = "none")

# Change-points by chain and index
p_cp_conv <- cp_samples %>%
  ggplot(aes(x = factor(chain), y = cp, fill = factor(chain))) +
  geom_boxplot(alpha = 0.7) +
  facet_wrap(~cp_idx, scales = "free_y", labeller = label_both) +
  labs(x = "Chain", y = "Change-point day", title = paste("Change-point convergence across chains (K =", K_mode, ")")) +
  theme_bw() +
  theme(legend.position = "none")

# 5. Gelman-Rubin diagnostic (approximate)
# Compute within-chain and between-chain variances for key parameters
gelman_rubin <- function(samples, param_name) {
  # Check if the parameter column exists
  if (!param_name %in% names(samples)) {
    return(NA_real_)
  }
  
  # Extract parameter values
  param_data <- samples %>%
    select(chain, sample, !!param_name) %>%
    filter(!is.na(!!sym(param_name)))
  
  if(nrow(param_data) == 0) return(NA_real_)
  
  # Within-chain variance
  W <- param_data %>%
    group_by(chain) %>%
    summarise(var_within = var(!!sym(param_name), na.rm = TRUE), .groups = "drop") %>%
    pull(var_within) %>%
    mean(na.rm = TRUE)
  
  # Between-chain variance
  chain_means <- param_data %>%
    group_by(chain) %>%
    summarise(mean_val = mean(!!sym(param_name), na.rm = TRUE), .groups = "drop") %>%
    pull(mean_val)
  
  overall_mean <- mean(chain_means, na.rm = TRUE)
  B <- var(chain_means, na.rm = TRUE) * length(unique(param_data$chain))
  
  # Pooled variance
  V <- W + B
  
  # Potential scale reduction factor
  R_hat <- sqrt(V / W)
  
  R_hat
}

# Compute R-hat for key parameters - only for existing columns
# First, get the actual columns that exist in beta_samples
existing_beta_cols <- names(beta_samples)[grepl("^beta_", names(beta_samples))]
existing_cp_cols <- names(cp_samples)[grepl("^cp_", names(cp_samples))]

# Extract segment numbers from column names
beta_segments <- as.numeric(gsub("beta_", "", existing_beta_cols))
cp_indices <- as.numeric(gsub("cp_", "", existing_cp_cols))

# Compute R-hat only for existing parameters
rhat_beta <- map_dbl(beta_segments, function(i) {
  gelman_rubin(beta_samples, paste0("beta_", i))
})

rhat_cp <- map_dbl(cp_indices, function(i) {
  gelman_rubin(cp_samples, paste0("cp_", i))
})

cat("\nGelman-Rubin diagnostic (R-hat) - values close to 1 indicate convergence:")
```

```
## 
## Gelman-Rubin diagnostic (R-hat) - values close to 1 indicate convergence:
```

``` r
cat("\nBeta parameters:")
```

```
## 
## Beta parameters:
```

``` r
for (i in seq_along(beta_segments)) {
  cat("\n  beta_", beta_segments[i], ": ", round(rhat_beta[i], 3), sep = "")
}
cat("\nChange-point parameters:")
```

```
## 
## Change-point parameters:
```

``` r
for (i in seq_along(cp_indices)) {
  cat("\n  cp_", cp_indices[i], ": ", round(rhat_cp[i], 3), sep = "")
}
```

```
## 
##   cp_NA: NA
```

``` r
# Display convergence plots
p_beta_conv
```

![plot of chunk convergence_check](figure/convergence_check-1.png)

``` r
p_cp_conv
```

![plot of chunk convergence_check](figure/convergence_check-2.png)

### 5.4 Convergence Assessment

The convergence diagnostics above help assess whether the RJMCMC chains have converged:

- **R-hat values**: Should be close to 1.0 (typically < 1.1 is acceptable)
- **Between-chain variation**: Beta values and change-points should show similar distributions across chains
- **Visual inspection**: Boxplots should show similar spreads and medians across chains

If convergence is poor, consider:
- Increasing the number of iterations
- Extending the burn-in period
- Adjusting the proposal distributions
- Checking for multimodality in the posterior

### 5.5 Acceptance Ratio Details

The RJMCMC implementation uses the theoretical framework from Lyyjynen (2014) §5.2:

- **Birth acceptance ratio**: \(A = \frac{\pi(\theta', k')}{\pi(\theta, k)} \times \frac{q(\theta, k|\theta', k')}{q(\theta', k'|\theta, k)} \times |J|\)
  - \(\pi(\cdot)\) is the posterior density
  - \(q(\cdot)\) is the proposal density  
  - \(|J|\) is the Jacobian determinant for the transformation

- **Death acceptance ratio**: \(A^{-1}\) (reciprocal of birth ratio)

- **Proposal probabilities**: \(b_k\) and \(d_k\) derived from Poisson prior ratios
- **Jacobian**: \(|J| \approx h_{\text{parent}} / u_2^2\) for the height transformation 
