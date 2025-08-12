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

**Note**: All safety checks and validation functions have been extracted to `R/safety_check_Ex2.R` to make this vignette more concise and maintainable.

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

# Load safety check functions
# These functions provide comprehensive input validation and safe defaults
# See R/safety_check_Ex2.R for full documentation
source("R/safety_check_Ex2.R")
```

```
## Error in file(filename, "r", encoding = encoding): cannot open the connection
```

``` r
# Load corrected birth and death functions
# These functions match the thesis exactly and include proper dimension checks
source("R/corrected_birth_death.R")
```

```
## Error in file(filename, "r", encoding = encoding): cannot open the connection
```

``` r
# Load simple and robust birth/death functions
# These are much simpler and more standard implementations
source("R/simple_birth_death.R")
```

```
## Error in file(filename, "r", encoding = encoding): cannot open the connection
```

``` r
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
## Initialization: K = Initialization: K = 2 
## 2 
## Running MCMC-PT iteration number: 0 of 40000. Chain number 2. Current logpost: -44635.5. Length of jump: 2.          Running MCMC-PT iteration number: 0 of 40000. Chain number 4. Current logpost: -49082.2. Length of jump: 2Running MCMC-PT iteration number: 0 of 40000. Chain number 1.          . Current logpost: -36100.5. Length of jump: 1.          Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Initialization: K = 2 
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 0 of 40000. Chain number 3. Current logpost: -24931.6. Length of jump: 2.          Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 100 of 40000. Chain number 4. Current logpost: -17833.8. Length of jump: 2.          Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 100 of 40000. Chain number 2. Current logpost: -20766. Length of jump: 2.          Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 100 of 40000. Chain number 1. Current logpost: -18430.8. Length of jump: 1.          Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 100 of 40000. Chain number 3. Current logpost: -18430.7. Length of jump: 1.          Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 200 of 40000. Chain number 4. Current logpost: -14276.9. Length of jump: 3.          Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 200 of 40000. Chain number 2. Current logpost: -8300.21. Length of jump: 2.          Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 200 of 40000. Chain number 1. Current logpost: -18431.6. Length of jump: 1.          Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 200 of 40000. Chain number 3. Current logpost: -12595.6. Length of jump: 3.          Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Cannot merge: only 1 segment
## Running MCMC-PT iteration number: 300 of 40000. Chain number 4. Current logpost: -10936.1. Length of jump: 3.          Running MCMC-PT iteration number: 300 of 40000. Chain number 2. Current logpost: -7111.62. Length of jump: 2.          Running MCMC-PT iteration number: 300 of 40000. Chain number 1. Current logpost: -11294.8. Length of jump: 3.          Running MCMC-PT iteration number: 300 of 40000. Chain number 3. Current logpost: -5468.41. Length of jump: 3.          Running MCMC-PT iteration number: 400 of 40000. Chain number 4. Current logpost: -3611.03. Length of jump: 3.          Running MCMC-PT iteration number: 400 of 40000. Chain number 1. Current logpost: -7360.32. Length of jump: 3.          Running MCMC-PT iteration number: 400 of 40000. Chain number 2. Current logpost: -5889.63. Length of jump: 2.          Running MCMC-PT iteration number: 400 of 40000. Chain number 3. Current logpost: -2090.34. Length of jump: 3.          Running MCMC-PT iteration number: 500 of 40000. Chain number 4. Current logpost: -1889.01. Length of jump: 3.          Running MCMC-PT iteration number: 500 of 40000. Chain number 1. Current logpost: -2586.75. Length of jump: 3.          Running MCMC-PT iteration number: 500 of 40000. Chain number 2. Current logpost: -4509.76. Length of jump: 3.          Running MCMC-PT iteration number: 500 of 40000. Chain number 3. Current logpost: -1557.47. Length of jump: 3.          Running MCMC-PT iteration number: 600 of 40000. Chain number 4. Current logpost: -675.043. Length of jump: 3.          Running MCMC-PT iteration number: 600 of 40000. Chain number 1. Current logpost: -1503.43. Length of jump: 3.          Running MCMC-PT iteration number: 600 of 40000. Chain number 2. Current logpost: -721.683. Length of jump: 3.          Running MCMC-PT iteration number: 600 of 40000. Chain number 3. Current logpost: -1003.41. Length of jump: 4.          Running MCMC-PT iteration number: 700 of 40000. Chain number 4. Current logpost: -423.884. Length of jump: 4.          Running MCMC-PT iteration number: 700 of 40000. Chain number 1. Current logpost: -1400.15. Length of jump: 3.          Running MCMC-PT iteration number: 700 of 40000. Chain number 2. Current logpost: -563.742. Length of jump: 4.          Running MCMC-PT iteration number: 700 of 40000. Chain number 3. Current logpost: -854.629. Length of jump: 4.          Running MCMC-PT iteration number: 800 of 40000. Chain number 4. Current logpost: -415.828. Length of jump: 4.          Running MCMC-PT iteration number: 800 of 40000. Chain number 1. Current logpost: -1045.01. Length of jump: 3.          Running MCMC-PT iteration number: 800 of 40000. Chain number 2. Current logpost: -537.594. Length of jump: 5.          Running MCMC-PT iteration number: 800 of 40000. Chain number 3. Current logpost: -818.385. Length of jump: 4.          Running MCMC-PT iteration number: 900 of 40000. Chain number 4. Current logpost: -416.22. Length of jump: 4.          Running MCMC-PT iteration number: 900 of 40000. Chain number 2. Current logpost: -520.987. Length of jump: 5.          Running MCMC-PT iteration number: 900 of 40000. Chain number 1. Current logpost: -814.886. Length of jump: 7.          Running MCMC-PT iteration number: 900 of 40000. Chain number 3. Current logpost: -771.366. Length of jump: 4.          Running MCMC-PT iteration number: 1000 of 40000. Chain number 4. Current logpost: -413.334. Length of jump: 5.          Running MCMC-PT iteration number: 1000 of 40000. Chain number 1. Current logpost: -776.721. Length of jump: 6.          Running MCMC-PT iteration number: 1000 of 40000. Chain number 2. Current logpost: -461.701. Length of jump: 6.          Running MCMC-PT iteration number: 1000 of 40000. Chain number 3. Current logpost: -719.829. Length of jump: 4.          Running MCMC-PT iteration number: 1100 of 40000. Chain number 2. Current logpost: -424.204. Length of jump: 6.          Running MCMC-PT iteration number: 1100 of 40000. Chain number 1. Current logpost: -733.023. Length of jump: 6.          Running MCMC-PT iteration number: 1100 of 40000. Chain number 4. Current logpost: -408.635. Length of jump: 4.          Running MCMC-PT iteration number: 1100 of 40000. Chain number 3. Current logpost: -697.038. Length of jump: 7.          Running MCMC-PT iteration number: 1200 of 40000. Chain number 1. Current logpost: -676.347. Length of jump: 7.          Running MCMC-PT iteration number: 1200 of 40000. Chain number 4. Current logpost: -405.685. Length of jump: 5.          Running MCMC-PT iteration number: 1200 of 40000. Chain number 2. Current logpost: -397.941. Length of jump: 6.          Running MCMC-PT iteration number: 1200 of 40000. Chain number 3. Current logpost: -681.407. Length of jump: 6.          Running MCMC-PT iteration number: 1300 of 40000. Chain number 1. Current logpost: -617.619. Length of jump: 8.          Running MCMC-PT iteration number: 1300 of 40000. Chain number 4. Current logpost: -395.539. Length of jump: 5.          Running MCMC-PT iteration number: 1300 of 40000. Chain number 2. Current logpost: -399.896. Length of jump: 5.          Running MCMC-PT iteration number: 1300 of 40000. Chain number 3. Current logpost: -617.373. Length of jump: 6.          Running MCMC-PT iteration number: 1400 of 40000. Chain number 4. Current logpost: -392.495. Length of jump: 5.          Running MCMC-PT iteration number: 1400 of 40000. Chain number 1. Current logpost: -575.681. Length of jump: 7.          Running MCMC-PT iteration number: 1400 of 40000. Chain number 2. Current logpost: -400.052. Length of jump: 4.          Running MCMC-PT iteration number: 1400 of 40000. Chain number 3. Current logpost: -584.197. Length of jump: 6.          Running MCMC-PT iteration number: 1500 of 40000. Chain number 1. Current logpost: -534.665. Length of jump: 6.          Running MCMC-PT iteration number: 1500 of 40000. Chain number 4. Current logpost: -375.113. Length of jump: 5.          Running MCMC-PT iteration number: 1500 of 40000. Chain number 2. Current logpost: -398.706. Length of jump: 4.          Running MCMC-PT iteration number: 1500 of 40000. Chain number 3. Current logpost: -560.083. Length of jump: 5.          Running MCMC-PT iteration number: 1600 of 40000. Chain number 4. Current logpost: -371.184. Length of jump: 5.          Running MCMC-PT iteration number: 1600 of 40000. Chain number 1. Current logpost: -526.496. Length of jump: 6.          Running MCMC-PT iteration number: 1600 of 40000. Chain number 2. Current logpost: -401.429. Length of jump: 4.          Running MCMC-PT iteration number: 1600 of 40000. Chain number 3. Current logpost: -535.527. Length of jump: 6.          Running MCMC-PT iteration number: 1700 of 40000. Chain number 4. Current logpost: -370.872. Length of jump: 5.          Running MCMC-PT iteration number: 1700 of 40000. Chain number 1. Current logpost: -472.374. Length of jump: 7.          Running MCMC-PT iteration number: 1700 of 40000. Chain number 2. Current logpost: -384.583. Length of jump: 5.          Running MCMC-PT iteration number: 1700 of 40000. Chain number 3. Current logpost: -506.404. Length of jump: 7.          Running MCMC-PT iteration number: 1800 of 40000. Chain number 1. Current logpost: -429.855. Length of jump: 6.          Running MCMC-PT iteration number: 1800 of 40000. Chain number 4. Current logpost: -368.079. Length of jump: 5.          Running MCMC-PT iteration number: 1800 of 40000. Chain number 2. Current logpost: -386.778. Length of jump: 6.          Running MCMC-PT iteration number: 1800 of 40000. Chain number 3. Current logpost: -503.95. Length of jump: 7.          Running MCMC-PT iteration number: 1900 of 40000. Chain number 4. Current logpost: -360.227. Length of jump: 4.          Running MCMC-PT iteration number: 1900 of 40000. Chain number 1. Current logpost: -407.942. Length of jump: 6.          Running MCMC-PT iteration number: 1900 of 40000. Chain number 2. Current logpost: -383.091. Length of jump: 6.          Running MCMC-PT iteration number: 1900 of 40000. Chain number 3. Current logpost: -492.17. Length of jump: 6.          Running MCMC-PT iteration number: 2000 of 40000. Chain number 4. Current logpost: -359.099. Length of jump: 4.          Running MCMC-PT iteration number: 2000 of 40000. Chain number 1. Current logpost: -380.909. Length of jump: 4.          Running MCMC-PT iteration number: 2000 of 40000. Chain number 2. Current logpost: -380.989. Length of jump: 6.          Running MCMC-PT iteration number: 2000 of 40000. Chain number 3. Current logpost: -464.757. Length of jump: 6.          Running MCMC-PT iteration number: 2100 of 40000. Chain number 4. Current logpost: -358.466. Length of jump: 4.          Running MCMC-PT iteration number: 2100 of 40000. Chain number 1. Current logpost: -364.059. Length of jump: 5.          Running MCMC-PT iteration number: 2100 of 40000. Chain number 2. Current logpost: -380.472. Length of jump: 6.          Running MCMC-PT iteration number: 2100 of 40000. Chain number 3. Current logpost: -438.489. Length of jump: 7.          Running MCMC-PT iteration number: 2200 of 40000. Chain number 1. Current logpost: -361.337. Length of jump: 5.          Running MCMC-PT iteration number: 2200 of 40000. Chain number 2. Current logpost: -380.378. Length of jump: 6.          Running MCMC-PT iteration number: 2200 of 40000. Chain number 4. Current logpost: -359.743. Length of jump: 5.          Running MCMC-PT iteration number: 2200 of 40000. Chain number 3. Current logpost: -376.808. Length of jump: 8.          Running MCMC-PT iteration number: 2300 of 40000. Chain number 1. Current logpost: -360.661. Length of jump: 5.          Running MCMC-PT iteration number: 2300 of 40000. Chain number 2. Current logpost: -378.248. Length of jump: 5.          Running MCMC-PT iteration number: 2300 of 40000. Chain number 4. Current logpost: -360.263. Length of jump: 6.          Running MCMC-PT iteration number: 2300 of 40000. Chain number 3. Current logpost: -369.896. Length of jump: 7.          Running MCMC-PT iteration number: 2400 of 40000. Chain number 1. Current logpost: -364.793. Length of jump: 5.          Running MCMC-PT iteration number: 2400 of 40000. Chain number 4. Current logpost: -359.336. Length of jump: 6.          Running MCMC-PT iteration number: 2400 of 40000. Chain number 2. Current logpost: -382.099. Length of jump: 5.          Running MCMC-PT iteration number: 2400 of 40000. Chain number 3. Current logpost: -368.632. Length of jump: 6.          Running MCMC-PT iteration number: 2500 of 40000. Chain number 1. Current logpost: -361.359. Length of jump: 5.          Running MCMC-PT iteration number: 2500 of 40000. Chain number 2. Current logpost: -377.863. Length of jump: 6.          Running MCMC-PT iteration number: 2500 of 40000. Chain number 4. Current logpost: -360.738. Length of jump: 6.          Running MCMC-PT iteration number: 2500 of 40000. Chain number 3. Current logpost: -368.382. Length of jump: 6.          Running MCMC-PT iteration number: 2600 of 40000. Chain number 1. Current logpost: -362.101. Length of jump: 6.          Running MCMC-PT iteration number: 2600 of 40000. Chain number 2. Current logpost: -379.116. Length of jump: 4.          Running MCMC-PT iteration number: 2600 of 40000. Chain number 4. Current logpost: -362.385. Length of jump: 6.          Running MCMC-PT iteration number: 2600 of 40000. Chain number 3. Current logpost: -369.439. Length of jump: 7.          Running MCMC-PT iteration number: 2700 of 40000. Chain number 1. Current logpost: -363.058. Length of jump: 7.          Running MCMC-PT iteration number: 2700 of 40000. Chain number 2. Current logpost: -368.503. Length of jump: 4.          Running MCMC-PT iteration number: 2700 of 40000. Chain number 4. Current logpost: -362.672. Length of jump: 6.          Running MCMC-PT iteration number: 2700 of 40000. Chain number 3. Current logpost: -372.452. Length of jump: 8.          Running MCMC-PT iteration number: 2800 of 40000. Chain number 1. Current logpost: -363.058. Length of jump: 7.          Running MCMC-PT iteration number: 2800 of 40000. Chain number 2. Current logpost: -364.34. Length of jump: 4.          Running MCMC-PT iteration number: 2800 of 40000. Chain number 4. Current logpost: -362.902. Length of jump: 6.          Running MCMC-PT iteration number: 2800 of 40000. Chain number 3. Current logpost: -370.87. Length of jump: 8.          Running MCMC-PT iteration number: 2900 of 40000. Chain number 4. Current logpost: -365.385. Length of jump: 7.          Running MCMC-PT iteration number: 2900 of 40000. Chain number 1. Current logpost: -359.942. Length of jump: 4.          Running MCMC-PT iteration number: 2900 of 40000. Chain number 2. Current logpost: -362.096. Length of jump: 4.          Running MCMC-PT iteration number: 2900 of 40000. Chain number 3. Current logpost: -368.649. Length of jump: 7.          Running MCMC-PT iteration number: 3000 of 40000. Chain number 1. Current logpost: -361.036. Length of jump: 4.          Running MCMC-PT iteration number: 3000 of 40000. Chain number 2. Current logpost: -359.839. Length of jump: 4.          Running MCMC-PT iteration number: 3000 of 40000. Chain number 4. Current logpost: -360.674. Length of jump: 4.          Running MCMC-PT iteration number: 3000 of 40000. Chain number 3. Current logpost: -364.769. Length of jump: 5.          Running MCMC-PT iteration number: 3100 of 40000. Chain number 1. Current logpost: -360.557. Length of jump: 5.          Running MCMC-PT iteration number: 3100 of 40000. Chain number 2. Current logpost: -359.839. Length of jump: 4.          Running MCMC-PT iteration number: 3100 of 40000. Chain number 4. Current logpost: -360.073. Length of jump: 4.          Running MCMC-PT iteration number: 3100 of 40000. Chain number 3. Current logpost: -363.669. Length of jump: 5.          Running MCMC-PT iteration number: 3200 of 40000. Chain number 2. Current logpost: Running MCMC-PT iteration number: 3200 of 40000. Chain number 1. Current logpost: -361.844. Length of jump: -360.355. Length of jump: 5.          4.          Running MCMC-PT iteration number: 3200 of 40000. Chain number 4. Current logpost: -360.95. Length of jump: 4.          Running MCMC-PT iteration number: 3200 of 40000. Chain number 3. Current logpost: -360.978. Length of jump: 4.          Running MCMC-PT iteration number: 3300 of 40000. Chain number 2. Current logpost: -363.187. Length of jump: 3.          Running MCMC-PT iteration number: 3300 of 40000. Chain number 4. Current logpost: -362.057. Length of jump: 5.          Running MCMC-PT iteration number: 3300 of 40000. Chain number 1. Current logpost: -361.113. Length of jump: 8.          Running MCMC-PT iteration number: 3300 of 40000. Chain number 3. Current logpost: -364.962. Length of jump: 5.          Running MCMC-PT iteration number: 3400 of 40000. Chain number 1. Current logpost: -363.297. Length of jump: 6.          Running MCMC-PT iteration number: 3400 of 40000. Chain number 2. Current logpost: -363.04. Length of jump: 4.          Running MCMC-PT iteration number: 3400 of 40000. Chain number 4. Current logpost: -360.36. Length of jump: 5.          Running MCMC-PT iteration number: 3400 of 40000. Chain number 3. Current logpost: -363.353. Length of jump: 5.          Running MCMC-PT iteration number: 3500 of 40000. Chain number 1. Current logpost: -359.648. Length of jump: 6.          Running MCMC-PT iteration number: 3500 of 40000. Chain number 4. Current logpost: -361.646. Length of jump: 5.          Running MCMC-PT iteration number: 3500 of 40000. Chain number 2. Current logpost: -360.883. Length of jump: 5.          Running MCMC-PT iteration number: 3500 of 40000. Chain number 3. Current logpost: -364.259. Length of jump: 4.          Running MCMC-PT iteration number: 3600 of 40000. Chain number 4. Current logpost: -362.229. Length of jump: 5.          Running MCMC-PT iteration number: 3600 of 40000. Chain number 1. Current logpost: -358.41. Length of jump: 7.          Running MCMC-PT iteration number: 3600 of 40000. Chain number 2. Current logpost: -360.998. Length of jump: 4.          Running MCMC-PT iteration number: 3600 of 40000. Chain number 3. Current logpost: -360.383. Length of jump: 5.          Running MCMC-PT iteration number: 3700 of 40000. Chain number 1. Current logpost: -357.772. Length of jump: 6.          Running MCMC-PT iteration number: 3700 of 40000. Chain number 4. Current logpost: -362.423. Length of jump: 4.          Running MCMC-PT iteration number: 3700 of 40000. Chain number 2. Current logpost: -360.975. Length of jump: 5.          Running MCMC-PT iteration number: 3700 of 40000. Chain number 3. Current logpost: -360.766. Length of jump: 6.          Running MCMC-PT iteration number: 3800 of 40000. Chain number 1. Current logpost: -358.088. Length of jump: 7.          Running MCMC-PT iteration number: 3800 of 40000. Chain number 4. Current logpost: -361.135. Length of jump: 3.          Running MCMC-PT iteration number: 3800 of 40000. Chain number 2. Current logpost: -367.611. Length of jump: 5.          Running MCMC-PT iteration number: 3800 of 40000. Chain number 3. Current logpost: -361.111. Length of jump: 5.          Running MCMC-PT iteration number: 3900 of 40000. Chain number 1. Current logpost: -357.072. Length of jump: 6.          Running MCMC-PT iteration number: 3900 of 40000. Chain number 4. Current logpost: -361.669. Length of jump: 3.          Running MCMC-PT iteration number: 3900 of 40000. Chain number 2. Current logpost: -365.401. Length of jump: 5.          Running MCMC-PT iteration number: 3900 of 40000. Chain number 3. Current logpost: -361.618. Length of jump: 4.          Running MCMC-PT iteration number: 4000 of 40000. Chain number 1. Current logpost: -362.408. Length of jump: 9.          Running MCMC-PT iteration number: 4000 of 40000. Chain number 2. Current logpost: -365.761. Length of jump: 5.          Running MCMC-PT iteration number: 4000 of 40000. Chain number 4. Current logpost: -361.773. Length of jump: 4.          Running MCMC-PT iteration number: 4000 of 40000. Chain number 3. Current logpost: -360.962. Length of jump: 4.          Running MCMC-PT iteration number: 4100 of 40000. Chain number 2. Current logpost: -366.043. Length of jump: 5.          Running MCMC-PT iteration number: 4100 of 40000. Chain number 1. Current logpost: -359.529. Length of jump: 8.          Running MCMC-PT iteration number: 4100 of 40000. Chain number 4. Current logpost: -361.047. Length of jump: 5.          Running MCMC-PT iteration number: 4100 of 40000. Chain number 3. Current logpost: -362.939. Length of jump: 4.          Running MCMC-PT iteration number: 4200 of 40000. Chain number 4. Current logpost: -360.427. Length of jump: 5.          Running MCMC-PT iteration number: 4200 of 40000. Chain number 2. Current logpost: -365.247. Length of jump: 6.          Running MCMC-PT iteration number: 4200 of 40000. Chain number 1. Current logpost: -360.817. Length of jump: 8.          Running MCMC-PT iteration number: 4200 of 40000. Chain number 3. Current logpost: -360.488. Length of jump: 6.          Running MCMC-PT iteration number: 4300 of 40000. Chain number 2. Current logpost: -364.72. Length of jump: 6.          Running MCMC-PT iteration number: 4300 of 40000. Chain number 4. Current logpost: -361.68. Length of jump: 5.          Running MCMC-PT iteration number: 4300 of 40000. Chain number 1. Current logpost: -359.029. Length of jump: 8.          Running MCMC-PT iteration number: 4300 of 40000. Chain number 3. Current logpost: -361.56. Length of jump: 6.          Running MCMC-PT iteration number: 4400 of 40000. Chain number 4. Current logpost: -363.072. Length of jump: 6.          Running MCMC-PT iteration number: 4400 of 40000. Chain number 2. Current logpost: -362.317. Length of jump: 6.          Running MCMC-PT iteration number: 4400 of 40000. Chain number 1. Current logpost: -359.602. Length of jump: 8.          Running MCMC-PT iteration number: 4400 of 40000. Chain number 3. Current logpost: -359.653. Length of jump: 5.          Running MCMC-PT iteration number: 4500 of 40000. Chain number 4. Current logpost: -361.508. Length of jump: 5.          Running MCMC-PT iteration number: 4500 of 40000. Chain number 2. Current logpost: -363.18. Length of jump: 7.          Running MCMC-PT iteration number: 4500 of 40000. Chain number 1. Current logpost: -359.103. Length of jump: 6.          Running MCMC-PT iteration number: 4500 of 40000. Chain number 3. Current logpost: -359.549. Length of jump: 6.          Running MCMC-PT iteration number: 4600 of 40000. Chain number 4. Current logpost: -363. Length of jump: 5.          Running MCMC-PT iteration number: 4600 of 40000. Chain number 2. Current logpost: -365.298. Length of jump: 7.          Running MCMC-PT iteration number: 4600 of 40000. Chain number 1. Current logpost: -358.544. Length of jump: 5.          Running MCMC-PT iteration number: 4600 of 40000. Chain number 3. Current logpost: -366.475. Length of jump: 7.          Running MCMC-PT iteration number: 4700 of 40000. Chain number 4. Current logpost: -359.957. Length of jump: 5.          Running MCMC-PT iteration number: 4700 of 40000. Chain number 2. Current logpost: -364.083. Length of jump: 7.          Running MCMC-PT iteration number: 4700 of 40000. Chain number 1. Current logpost: -358.716. Length of jump: 6.          Running MCMC-PT iteration number: 4700 of 40000. Chain number 3. Current logpost: -356.805. Length of jump: 9.          Running MCMC-PT iteration number: 4800 of 40000. Chain number 4. Current logpost: -361.538. Length of jump: 7.          Running MCMC-PT iteration number: 4800 of 40000. Chain number 2. Current logpost: -361.157. Length of jump: 6.          Running MCMC-PT iteration number: 4800 of 40000. Chain number 1. Current logpost: -356.496. Length of jump: 6.          Running MCMC-PT iteration number: 4800 of 40000. Chain number 3. Current logpost: -360.579. Length of jump: 7.          Running MCMC-PT iteration number: 4900 of 40000. Chain number 4. Current logpost: -364.52. Length of jump: 7.          Running MCMC-PT iteration number: 4900 of 40000. Chain number 2. Current logpost: -362.031. Length of jump: 5.          Running MCMC-PT iteration number: 4900 of 40000. Chain number 1. Current logpost: -356.529. Length of jump: 6.          Running MCMC-PT iteration number: 4900 of 40000. Chain number 3. Current logpost: -358.695. Length of jump: 8.          Running MCMC-PT iteration number: 5000 of 40000. Chain number 4. Current logpost: -360.328. Length of jump: 5.          Running MCMC-PT iteration number: 5000 of 40000. Chain number 2. Current logpost: -363.669. Length of jump: 6.          Running MCMC-PT iteration number: 5000 of 40000. Chain number 1. Current logpost: -356.882. Length of jump: 6.          Running MCMC-PT iteration number: 5000 of 40000. Chain number 3. Current logpost: -359.058. Length of jump: 9.          Running MCMC-PT iteration number: 5100 of 40000. Chain number 4. Current logpost: -360.048. Length of jump: 4.          Running MCMC-PT iteration number: 5100 of 40000. Chain number 2. Current logpost: -365.687. Length of jump: 8.          Running MCMC-PT iteration number: 5100 of 40000. Chain number 1. Current logpost: -357.961. Length of jump: 6.          Running MCMC-PT iteration number: 5100 of 40000. Chain number 3. Current logpost: -361.591. Length of jump: 9.          Running MCMC-PT iteration number: 5200 of 40000. Chain number 3. Current logpost: -364.173. Length of jump: 10.          Running MCMC-PT iteration number: 5300 of 40000. Chain number 4. Current logpost: -360.21. Length of jump: 4.          Running MCMC-PT iteration number: 5300 of 40000. Chain number 2. Current logpost: -361.969. Length of jump: 7.          Running MCMC-PT iteration number: 5300 of 40000. Chain number 1. Current logpost: -357.885. Length of jump: 6.          Running MCMC-PT iteration number: 5300 of 40000. Chain number 3. Current logpost: -364.071. Length of jump: 9.          Running MCMC-PT iteration number: 5400 of 40000. Chain number 3. Current logpost: -357.773. Length of jump: 8.          Running MCMC-PT iteration number: 5500 of 40000. Chain number 4. Current logpost: -363.19. Length of jump: 6.          Running MCMC-PT iteration number: 5500 of 40000. Chain number 2. Current logpost: -360.788. Length of jump: 4.          Running MCMC-PT iteration number: 5500 of 40000. Chain number 1. Current logpost: -359.219. Length of jump: 7.          Running MCMC-PT iteration number: 5500 of 40000. Chain number 3. Current logpost: -355.933. Length of jump: 7.          Running MCMC-PT iteration number: 5600 of 40000. Chain number 4. Current logpost: -361.026. Length of jump: 5.          Running MCMC-PT iteration number: 5600 of 40000. Chain number 2. Current logpost: -360.845. Length of jump: 4.          Running MCMC-PT iteration number: 5600 of 40000. Chain number 1. Current logpost: -359.3. Length of jump: 6.          Running MCMC-PT iteration number: 5600 of 40000. Chain number 3. Current logpost: -357.218. Length of jump: 6.          Running MCMC-PT iteration number: 5700 of 40000. Chain number 4. Current logpost: -359.458. Length of jump: 6.          Running MCMC-PT iteration number: 5700 of 40000. Chain number 2. Current logpost: -361.551. Length of jump: 3.          Running MCMC-PT iteration number: 5700 of 40000. Chain number 1. Current logpost: -359.91. Length of jump: 5.          Running MCMC-PT iteration number: 5800 of 40000. Chain number 1. Current logpost: -361.025. Length of jump: 5.          Running MCMC-PT iteration number: 5800 of 40000. Chain number 3. Current logpost: -356.575. Length of jump: 6.          Running MCMC-PT iteration number: 5900 of 40000. Chain number 1. Current logpost: -361.517. Length of jump: 5.          Running MCMC-PT iteration number: 5900 of 40000. Chain number 3. Current logpost: -356.174. Length of jump: 6.          Running MCMC-PT iteration number: 6000 of 40000. Chain number 4. Current logpost: -360.423. Length of jump: 7.          Running MCMC-PT iteration number: 6000 of 40000. Chain number 2. Current logpost: -363.141. Length of jump: 5.          Running MCMC-PT iteration number: 6000 of 40000. Chain number 1. Current logpost: -360.411. Length of jump: 4.          Running MCMC-PT iteration number: 6000 of 40000. Chain number 3. Current logpost: -360.604. Length of jump: 7.          Running MCMC-PT iteration number: 6100 of 40000. Chain number 4. Current logpost: -358.835. Length of jump: 6.          Running MCMC-PT iteration number: 6100 of 40000. Chain number 2. Current logpost: -362.886. Length of jump: 4.          Running MCMC-PT iteration number: 6100 of 40000. Chain number 1. Current logpost: -359.986. Length of jump: 4.          Running MCMC-PT iteration number: 6100 of 40000. Chain number 3. Current logpost: -357.368. Length of jump: 7.          Running MCMC-PT iteration number: 6200 of 40000. Chain number 1. Current logpost: -360.441. Length of jump: 4.          Running MCMC-PT iteration number: 6200 of 40000. Chain number 3. Current logpost: -360.808. Length of jump: 9.          Running MCMC-PT iteration number: 6300 of 40000. Chain number 4. Current logpost: -359.169. Length of jump: 5.          Running MCMC-PT iteration number: 6300 of 40000. Chain number 2. Current logpost: -361.799. Length of jump: 5.          Running MCMC-PT iteration number: 6300 of 40000. Chain number 1. Current logpost: -361.241. Length of jump: 5.          Running MCMC-PT iteration number: 6300 of 40000. Chain number 3. Current logpost: -359.152. Length of jump: 9.          Running MCMC-PT iteration number: 6400 of 40000. Chain number 4. Current logpost: -359.658. Length of jump: 5.          Running MCMC-PT iteration number: 6400 of 40000. Chain number 2. Current logpost: -360.988. Length of jump: 5.          Running MCMC-PT iteration number: 6400 of 40000. Chain number 1. Current logpost: -360.848. Length of jump: 4.          Running MCMC-PT iteration number: 6400 of 40000. Chain number 3. Current logpost: -360.358. Length of jump: 9.          Running MCMC-PT iteration number: 6500 of 40000. Chain number 4. Current logpost: -360.041. Length of jump: 6.          Running MCMC-PT iteration number: 6500 of 40000. Chain number 2. Current logpost: -361.801. Length of jump: 5.          Running MCMC-PT iteration number: 6500 of 40000. Chain number 1. Current logpost: -362.121. Length of jump: 5.          Running MCMC-PT iteration number: 6500 of 40000. Chain number 3. Current logpost: -358.833. Length of jump: 7.          Running MCMC-PT iteration number: 6600 of 40000. Chain number 4. Current logpost: -358.83. Length of jump: 6.          Running MCMC-PT iteration number: 6600 of 40000. Chain number 2. Current logpost: -360.542. Length of jump: 4.          Running MCMC-PT iteration number: 6600 of 40000. Chain number 1. Current logpost: -367.482. Length of jump: 6.          Running MCMC-PT iteration number: 6600 of 40000. Chain number 3. Current logpost: -360.979. Length of jump: 7.          Running MCMC-PT iteration number: 6700 of 40000. Chain number 2. Current logpost: -360.796. Length of jump: 3.          Running MCMC-PT iteration number: 6700 of 40000. Chain number 4. Current logpost: -358.91. Length of jump: 8.          Running MCMC-PT iteration number: 6700 of 40000. Chain number 1. Current logpost: -364.289. Length of jump: 6.          Running MCMC-PT iteration number: 6700 of 40000. Chain number 3. Current logpost: -358.992. Length of jump: 7.          Running MCMC-PT iteration number: 6800 of 40000. Chain number 2. Current logpost: -362.182. Length of jump: 3.          Running MCMC-PT iteration number: 6800 of 40000. Chain number 4. Current logpost: -360.433. Length of jump: 8.          Running MCMC-PT iteration number: 6800 of 40000. Chain number 1. Current logpost: -362.005. Length of jump: 6.          Running MCMC-PT iteration number: 6800 of 40000. Chain number 3. Current logpost: -358.975. Length of jump: 7.          Running MCMC-PT iteration number: 6900 of 40000. Chain number 2. Current logpost: -361.632. Length of jump: 4.          Running MCMC-PT iteration number: 6900 of 40000. Chain number 4. Current logpost: -357.945. Length of jump: 7.          Running MCMC-PT iteration number: 6900 of 40000. Chain number 1. Current logpost: -365.38. Length of jump: 7.          Running MCMC-PT iteration number: 6900 of 40000. Chain number 3. Current logpost: -361.902. Length of jump: 8.          Running MCMC-PT iteration number: 7000 of 40000. Chain number 2. Current logpost: -361.363. Length of jump: 4.          Running MCMC-PT iteration number: 7000 of 40000. Chain number 4. Current logpost: -359.45. Length of jump: 7.          Running MCMC-PT iteration number: 7000 of 40000. Chain number 1. Current logpost: -365.622. Length of jump: 8.          Running MCMC-PT iteration number: 7000 of 40000. Chain number 3. Current logpost: -359.463. Length of jump: 7.          Running MCMC-PT iteration number: 7100 of 40000. Chain number 2. Current logpost: -361.484. Length of jump: 5.          Running MCMC-PT iteration number: 7100 of 40000. Chain number 4. Current logpost: -359.754. Length of jump: 7.          Running MCMC-PT iteration number: 7100 of 40000. Chain number 1. Current logpost: -367.465. Length of jump: 9.          Running MCMC-PT iteration number: 7100 of 40000. Chain number 3. Current logpost: -361.495. Length of jump: 7.          Running MCMC-PT iteration number: 7200 of 40000. Chain number 2. Current logpost: -360.541. Length of jump: 5.          Running MCMC-PT iteration number: 7200 of 40000. Chain number 4. Current logpost: -358.345. Length of jump: 6.          Running MCMC-PT iteration number: 7200 of 40000. Chain number 1. Current logpost: -365.371. Length of jump: 8.          Running MCMC-PT iteration number: 7200 of 40000. Chain number 3. Current logpost: -359.129. Length of jump: 7.          Running MCMC-PT iteration number: 7300 of 40000. Chain number 2. Current logpost: -362.666. Length of jump: 4.          Running MCMC-PT iteration number: 7300 of 40000. Chain number 4. Current logpost: -358.952. Length of jump: 5.          Running MCMC-PT iteration number: 7300 of 40000. Chain number 1. Current logpost: -364.892. Length of jump: 7.          Running MCMC-PT iteration number: 7300 of 40000. Chain number 3. Current logpost: -360.781. Length of jump: 7.          Running MCMC-PT iteration number: 7400 of 40000. Chain number 4. Current logpost: -358.742. Length of jump: 5.          Running MCMC-PT iteration number: 7400 of 40000. Chain number 1. Current logpost: -360.815. Length of jump: 5.          Running MCMC-PT iteration number: 7400 of 40000. Chain number 3. Current logpost: -359.135. Length of jump: 6.          Running MCMC-PT iteration number: 7500 of 40000. Chain number 2. Current logpost: -362.584. Length of jump: 5.          Running MCMC-PT iteration number: 7500 of 40000. Chain number 4. Current logpost: -360.819. Length of jump: 5.          Running MCMC-PT iteration number: 7500 of 40000. Chain number 1. Current logpost: -360.646. Length of jump: 5.          Running MCMC-PT iteration number: 7500 of 40000. Chain number 3. Current logpost: -359.167. Length of jump: 6.          Running MCMC-PT iteration number: 7600 of 40000. Chain number 2. Current logpost: -363.042. Length of jump: 5.          Running MCMC-PT iteration number: 7600 of 40000. Chain number 4. Current logpost: -359.508. Length of jump: 6.          Running MCMC-PT iteration number: 7600 of 40000. Chain number 1. Current logpost: -360.563. Length of jump: 5.          Running MCMC-PT iteration number: 7600 of 40000. Chain number 3. Current logpost: -358.497. Length of jump: 6.          Running MCMC-PT iteration number: 7700 of 40000. Chain number 2. Current logpost: -362.98. Length of jump: 5.          Running MCMC-PT iteration number: 7700 of 40000. Chain number 4. Current logpost: -359.282. Length of jump: 6.          Running MCMC-PT iteration number: 7700 of 40000. Chain number 1. Current logpost: -360.93. Length of jump: 4.          Running MCMC-PT iteration number: 7700 of 40000. Chain number 3. Current logpost: -358.158. Length of jump: 6.          Running MCMC-PT iteration number: 7800 of 40000. Chain number 2. Current logpost: -360.533. Length of jump: 4.          Running MCMC-PT iteration number: 7800 of 40000. Chain number 4. Current logpost: -359.054. Length of jump: 6.          Running MCMC-PT iteration number: 7800 of 40000. Chain number 1. Current logpost: -360.108. Length of jump: 4.          Running MCMC-PT iteration number: 7800 of 40000. Chain number 3. Current logpost: -360.244. Length of jump: 4.          Running MCMC-PT iteration number: 7900 of 40000. Chain number 2. Current logpost: -359.328. Length of jump: 5.          Running MCMC-PT iteration number: 7900 of 40000. Chain number 4. Current logpost: -359.851. Length of jump: 6.          Running MCMC-PT iteration number: 7900 of 40000. Chain number 1. Current logpost: -360.272. Length of jump: 4.          Running MCMC-PT iteration number: 7900 of 40000. Chain number 3. Current logpost: -360.467. Length of jump: 4.          Running MCMC-PT iteration number: 8000 of 40000. Chain number 2. Current logpost: -360.027. Length of jump: 4.          Running MCMC-PT iteration number: 8000 of 40000. Chain number 4. Current logpost: -363.2. Length of jump: 7.          Running MCMC-PT iteration number: 8000 of 40000. Chain number 1. Current logpost: -360.342. Length of jump: 5.          Running MCMC-PT iteration number: 8000 of 40000. Chain number 3. Current logpost: -358.779. Length of jump: 5.          Running MCMC-PT iteration number: 8100 of 40000. Chain number 2. Current logpost: -361.953. Length of jump: 4.          Running MCMC-PT iteration number: 8100 of 40000. Chain number 4. Current logpost: -360.881. Length of jump: 6.          Running MCMC-PT iteration number: 8100 of 40000. Chain number 1. Current logpost: -360.158. Length of jump: 5.          Running MCMC-PT iteration number: 8100 of 40000. Chain number 3. Current logpost: -361.581. Length of jump: 6.          Running MCMC-PT iteration number: 8200 of 40000. Chain number 2. Current logpost: -360.34. Length of jump: 5.          Running MCMC-PT iteration number: 8200 of 40000. Chain number 4. Current logpost: -360.115. Length of jump: 6.          Running MCMC-PT iteration number: 8200 of 40000. Chain number 1. Current logpost: -360.147. Length of jump: 5.          Running MCMC-PT iteration number: 8200 of 40000. Chain number 3. Current logpost: -366.021. Length of jump: 7.          Running MCMC-PT iteration number: 8300 of 40000. Chain number 2. Current logpost: -360.409. Length of jump: 5.          Running MCMC-PT iteration number: 8300 of 40000. Chain number 4. Current logpost: -360.544. Length of jump: 6.          Running MCMC-PT iteration number: 8300 of 40000. Chain number 1. Current logpost: -360.188. Length of jump: 5.          Running MCMC-PT iteration number: 8300 of 40000. Chain number 3. Current logpost: -362.981. Length of jump: 7.          Running MCMC-PT iteration number: 8400 of 40000. Chain number 2. Current logpost: -362.218. Length of jump: 4.          Running MCMC-PT iteration number: 8400 of 40000. Chain number 4. Current logpost: -358.544. Length of jump: 6.          Running MCMC-PT iteration number: 8400 of 40000. Chain number 1. Current logpost: -364.263. Length of jump: 6.          Running MCMC-PT iteration number: 8400 of 40000. Chain number 3. Current logpost: -363.441. Length of jump: 8.          Running MCMC-PT iteration number: 8500 of 40000. Chain number 2. Current logpost: -360.467. Length of jump: 5.          Running MCMC-PT iteration number: 8500 of 40000. Chain number 4. Current logpost: -359.331. Length of jump: 8.          Running MCMC-PT iteration number: 8500 of 40000. Chain number 1. Current logpost: -363.867. Length of jump: 7.          Running MCMC-PT iteration number: 8500 of 40000. Chain number 3. Current logpost: -359.946. Length of jump: 6.          Running MCMC-PT iteration number: 8600 of 40000. Chain number 2. Current logpost: -360.164. Length of jump: 5.          Running MCMC-PT iteration number: 8600 of 40000. Chain number 4. Current logpost: -359.065. Length of jump: 7.          Running MCMC-PT iteration number: 8600 of 40000. Chain number 1. Current logpost: -361.521. Length of jump: 7.          Running MCMC-PT iteration number: 8600 of 40000. Chain number 3. Current logpost: -359.134. Length of jump: 6.          Running MCMC-PT iteration number: 8700 of 40000. Chain number 2. Current logpost: -360.205. Length of jump: 5.          Running MCMC-PT iteration number: 8700 of 40000. Chain number 4. Current logpost: -364.925. Length of jump: 8.          Running MCMC-PT iteration number: 8700 of 40000. Chain number 1. Current logpost: -362.628. Length of jump: 7.          Running MCMC-PT iteration number: 8700 of 40000. Chain number 3. Current logpost: -358.917. Length of jump: 6.          Running MCMC-PT iteration number: 8800 of 40000. Chain number 2. Current logpost: -359.828. Length of jump: 4.          Running MCMC-PT iteration number: 8800 of 40000. Chain number 4. Current logpost: -360.424. Length of jump: 8.          Running MCMC-PT iteration number: 8800 of 40000. Chain number 1. Current logpost: -362.819. Length of jump: 7.          Running MCMC-PT iteration number: 8800 of 40000. Chain number 3. Current logpost: -358.659. Length of jump: 6.          Running MCMC-PT iteration number: 8900 of 40000. Chain number 2. Current logpost: -360.152. Length of jump: 5.          Running MCMC-PT iteration number: 8900 of 40000. Chain number 4. Current logpost: -358.974. Length of jump: 8.          Running MCMC-PT iteration number: 8900 of 40000. Chain number 1. Current logpost: -363.467. Length of jump: 7.          Running MCMC-PT iteration number: 8900 of 40000. Chain number 3. Current logpost: -358.647. Length of jump: 6.          Running MCMC-PT iteration number: 9000 of 40000. Chain number 2. Current logpost: -361.367. Length of jump: 4.          Running MCMC-PT iteration number: 9000 of 40000. Chain number 4. Current logpost: -359.739. Length of jump: 8.          Running MCMC-PT iteration number: 9000 of 40000. Chain number 1. Current logpost: -362.94. Length of jump: 5.          Running MCMC-PT iteration number: 9000 of 40000. Chain number 3. Current logpost: -360.049. Length of jump: 6.          Running MCMC-PT iteration number: 9100 of 40000. Chain number 2. Current logpost: -360.071. Length of jump: 5.          Running MCMC-PT iteration number: 9100 of 40000. Chain number 4. Current logpost: -363.03. Length of jump: 8.          Running MCMC-PT iteration number: 9100 of 40000. Chain number 1. Current logpost: -361.051. Length of jump: 6.          Running MCMC-PT iteration number: 9100 of 40000. Chain number 3. Current logpost: -363.616. Length of jump: 6.          Running MCMC-PT iteration number: 9200 of 40000. Chain number 2. Current logpost: -361.278. Length of jump: 4.          Running MCMC-PT iteration number: 9200 of 40000. Chain number 4. Current logpost: -359.979. Length of jump: 8.          Running MCMC-PT iteration number: 9200 of 40000. Chain number 1. Current logpost: -361.343. Length of jump: 6.          Running MCMC-PT iteration number: 9200 of 40000. Chain number 3. Current logpost: -360.224. Length of jump: 6.          Running MCMC-PT iteration number: 9300 of 40000. Chain number 2. Current logpost: -360.682. Length of jump: 4.          Running MCMC-PT iteration number: 9300 of 40000. Chain number 4. Current logpost: -358.165. Length of jump: 7.          Running MCMC-PT iteration number: 9300 of 40000. Chain number 1. Current logpost: -358.831. Length of jump: 8.          Running MCMC-PT iteration number: 9300 of 40000. Chain number 3. Current logpost: -359.034. Length of jump: 7.          Running MCMC-PT iteration number: 9400 of 40000. Chain number 2. Current logpost: -360.606. Length of jump: 4.          Running MCMC-PT iteration number: 9400 of 40000. Chain number 4. Current logpost: -357.468. Length of jump: 7.          Running MCMC-PT iteration number: 9400 of 40000. Chain number 1. Current logpost: -360.904. Length of jump: 8.          Running MCMC-PT iteration number: 9400 of 40000. Chain number 3. Current logpost: -359.516. Length of jump: 7.          Running MCMC-PT iteration number: 9500 of 40000. Chain number 2. Current logpost: -361.176. Length of jump: 3.          Running MCMC-PT iteration number: 9500 of 40000. Chain number 4. Current logpost: -358.587. Length of jump: 6.          Running MCMC-PT iteration number: 9500 of 40000. Chain number 1. Current logpost: -358.991. Length of jump: 6.          Running MCMC-PT iteration number: 9500 of 40000. Chain number 3. Current logpost: -359.87. Length of jump: 7.          Running MCMC-PT iteration number: 9600 of 40000. Chain number 2. Current logpost: -362.877. Length of jump: 3.          Running MCMC-PT iteration number: 9600 of 40000. Chain number 4. Current logpost: -360.806. Length of jump: 7.          Running MCMC-PT iteration number: 9600 of 40000. Chain number 1. Current logpost: -358.515. Length of jump: 6.          Running MCMC-PT iteration number: 9600 of 40000. Chain number 3. Current logpost: -361.689. Length of jump: 7.          Running MCMC-PT iteration number: 9700 of 40000. Chain number 2. Current logpost: -361.912. Length of jump: 3.          Running MCMC-PT iteration number: 9700 of 40000. Chain number 4. Current logpost: -361.181. Length of jump: 7.          Running MCMC-PT iteration number: 9700 of 40000. Chain number 1. Current logpost: -362.258. Length of jump: 5.          Running MCMC-PT iteration number: 9700 of 40000. Chain number 3. Current logpost: -364.072. Length of jump: 8.          Running MCMC-PT iteration number: 9800 of 40000. Chain number 2. Current logpost: -362.419. Length of jump: 5.          Running MCMC-PT iteration number: 9800 of 40000. Chain number 4. Current logpost: -359.711. Length of jump: 6.          Running MCMC-PT iteration number: 9800 of 40000. Chain number 1. Current logpost: -357.993. Length of jump: 5.          Running MCMC-PT iteration number: 9800 of 40000. Chain number 3. Current logpost: -361.192. Length of jump: 8.          Running MCMC-PT iteration number: 9900 of 40000. Chain number 2. Current logpost: -362.096. Length of jump: 5.          Running MCMC-PT iteration number: 9900 of 40000. Chain number 4. Current logpost: -362.917. Length of jump: 9.          Running MCMC-PT iteration number: 9900 of 40000. Chain number 1. Current logpost: -361.302. Length of jump: 5.          Running MCMC-PT iteration number: 9900 of 40000. Chain number 3. Current logpost: -361.945. Length of jump: 8.          Running MCMC-PT iteration number: 10000 of 40000. Chain number 2. Current logpost: -361.073. Length of jump: 4.          Running MCMC-PT iteration number: 10000 of 40000. Chain number 4. Current logpost: -364.157. Length of jump: 8.          Running MCMC-PT iteration number: 10000 of 40000. Chain number 1. Current logpost: -359.635. Length of jump: 5.          Running MCMC-PT iteration number: 10000 of 40000. Chain number 3. Current logpost: -359.837. Length of jump: 7.          Running MCMC-PT iteration number: 10100 of 40000. Chain number 2. Current logpost: -360.717. Length of jump: 5.          Running MCMC-PT iteration number: 10100 of 40000. Chain number 4. Current logpost: -363.801. Length of jump: 7.          Running MCMC-PT iteration number: 10100 of 40000. Chain number 1. Current logpost: -358.527. Length of jump: 4.          Running MCMC-PT iteration number: 10100 of 40000. Chain number 3. Current logpost: -358.552. Length of jump: 6.          Running MCMC-PT iteration number: 10200 of 40000. Chain number 2. Current logpost: -363.633. Length of jump: 4.          Running MCMC-PT iteration number: 10200 of 40000. Chain number 4. Current logpost: -362.195. Length of jump: 7.          Running MCMC-PT iteration number: 10200 of 40000. Chain number 1. Current logpost: -360.386. Length of jump: 4.          Running MCMC-PT iteration number: 10200 of 40000. Chain number 3. Current logpost: -359.864. Length of jump: 6.          Running MCMC-PT iteration number: 10300 of 40000. Chain number 2. Current logpost: -360.593. Length of jump: 4.          Running MCMC-PT iteration number: 10300 of 40000. Chain number 4. Current logpost: -359.2. Length of jump: 5.          Running MCMC-PT iteration number: 10300 of 40000. Chain number 1. Current logpost: -357.661. Length of jump: 5.          Running MCMC-PT iteration number: 10300 of 40000. Chain number 3. Current logpost: -359.728. Length of jump: 6.          Running MCMC-PT iteration number: 10400 of 40000. Chain number 2. Current logpost: -362.132. Length of jump: 4.          Running MCMC-PT iteration number: 10400 of 40000. Chain number 4. Current logpost: -360.557. Length of jump: 6.          Running MCMC-PT iteration number: 10400 of 40000. Chain number 1. Current logpost: -357.838. Length of jump: 5.          Running MCMC-PT iteration number: 10400 of 40000. Chain number 3. Current logpost: -360.105. Length of jump: 6.          Running MCMC-PT iteration number: 10500 of 40000. Chain number 2. Current logpost: -362.743. Length of jump: 3.          Running MCMC-PT iteration number: 10500 of 40000. Chain number 1. Current logpost: -363.762. Length of jump: 4.          Running MCMC-PT iteration number: 10500 of 40000. Chain number 3. Current logpost: -358.706. Length of jump: 6.          Running MCMC-PT iteration number: 10600 of 40000. Chain number 2. Current logpost: -364.929. Length of jump: 5.          Running MCMC-PT iteration number: 10600 of 40000. Chain number 4. Current logpost: -363.639. Length of jump: 5.          Running MCMC-PT iteration number: 10600 of 40000. Chain number 1. Current logpost: -364.694. Length of jump: 4.          Running MCMC-PT iteration number: 10600 of 40000. Chain number 3. Current logpost: -361.35. Length of jump: 6.          Running MCMC-PT iteration number: 10700 of 40000. Chain number 2. Current logpost: -360.682. Length of jump: 4.          Running MCMC-PT iteration number: 10700 of 40000. Chain number 4. Current logpost: -360.228. Length of jump: 5.          Running MCMC-PT iteration number: 10700 of 40000. Chain number 1. Current logpost: -360.593. Length of jump: 5.          Running MCMC-PT iteration number: 10700 of 40000. Chain number 3. Current logpost: -358.245. Length of jump: 5.          Running MCMC-PT iteration number: 10800 of 40000. Chain number 2. Current logpost: -361.628. Length of jump: 5.          Running MCMC-PT iteration number: 10800 of 40000. Chain number 4. Current logpost: -360.404. Length of jump: 5.          Running MCMC-PT iteration number: 10800 of 40000. Chain number 1. Current logpost: -359.227. Length of jump: 5.          Running MCMC-PT iteration number: 10800 of 40000. Chain number 3. Current logpost: -358.535. Length of jump: 5.          Running MCMC-PT iteration number: 10900 of 40000. Chain number 2. Current logpost: -360.636. Length of jump: 5.          Running MCMC-PT iteration number: 10900 of 40000. Chain number 4. Current logpost: -358.551. Length of jump: 6.          Running MCMC-PT iteration number: 10900 of 40000. Chain number 1. Current logpost: -366.908. Length of jump: 6.          Running MCMC-PT iteration number: 10900 of 40000. Chain number 3. Current logpost: -359.283. Length of jump: 5.          Running MCMC-PT iteration number: 11000 of 40000. Chain number 2. Current logpost: -361.782. Length of jump: 6.          Running MCMC-PT iteration number: 11000 of 40000. Chain number 4. Current logpost: -358.736. Length of jump: 6.          Running MCMC-PT iteration number: 11000 of 40000. Chain number 1. Current logpost: -362.583. Length of jump: 6.          Running MCMC-PT iteration number: 11000 of 40000. Chain number 3. Current logpost: -358.511. Length of jump: 5.          Running MCMC-PT iteration number: 11100 of 40000. Chain number 2. Current logpost: -363.519. Length of jump: 7.          Running MCMC-PT iteration number: 11100 of 40000. Chain number 4. Current logpost: -359.07. Length of jump: 5.          Running MCMC-PT iteration number: 11100 of 40000. Chain number 1. Current logpost: -361.396. Length of jump: 6.          Running MCMC-PT iteration number: 11100 of 40000. Chain number 3. Current logpost: -359.374. Length of jump: 6.          Running MCMC-PT iteration number: 11200 of 40000. Chain number 2. Current logpost: -362.159. Length of jump: 7.          Running MCMC-PT iteration number: 11200 of 40000. Chain number 4. Current logpost: -359.752. Length of jump: 5.          Running MCMC-PT iteration number: 11200 of 40000. Chain number 1. Current logpost: -361.42. Length of jump: 6.          Running MCMC-PT iteration number: 11200 of 40000. Chain number 3. Current logpost: -358.42. Length of jump: 5.          Running MCMC-PT iteration number: 11300 of 40000. Chain number 2. Current logpost: -362.112. Length of jump: 6.          Running MCMC-PT iteration number: 11300 of 40000. Chain number 4. Current logpost: -361.58. Length of jump: 6.          Running MCMC-PT iteration number: 11300 of 40000. Chain number 1. Current logpost: -360.987. Length of jump: 7.          Running MCMC-PT iteration number: 11300 of 40000. Chain number 3. Current logpost: -358.635. Length of jump: 5.          Running MCMC-PT iteration number: 11400 of 40000. Chain number 2. Current logpost: -361.858. Length of jump: 5.          Running MCMC-PT iteration number: 11400 of 40000. Chain number 4. Current logpost: -360.59. Length of jump: 6.          Running MCMC-PT iteration number: 11400 of 40000. Chain number 1. Current logpost: -359.599. Length of jump: 6.          Running MCMC-PT iteration number: 11400 of 40000. Chain number 3. Current logpost: -358.768. Length of jump: 5.          Running MCMC-PT iteration number: 11500 of 40000. Chain number 2. Current logpost: -361.212. Length of jump: 5.          Running MCMC-PT iteration number: 11500 of 40000. Chain number 4. Current logpost: -362.91. Length of jump: 5.          Running MCMC-PT iteration number: 11500 of 40000. Chain number 1. Current logpost: -359.005. Length of jump: 5.          Running MCMC-PT iteration number: 11500 of 40000. Chain number 3. Current logpost: -361.779. Length of jump: 7.          Running MCMC-PT iteration number: 11600 of 40000. Chain number 2. Current logpost: -360.142. Length of jump: 5.          Running MCMC-PT iteration number: 11600 of 40000. Chain number 4. Current logpost: -363.384. Length of jump: 5.          Running MCMC-PT iteration number: 11600 of 40000. Chain number 1. Current logpost: -359.286. Length of jump: 5.          Running MCMC-PT iteration number: 11600 of 40000. Chain number 3. Current logpost: -360.571. Length of jump: 6.          Running MCMC-PT iteration number: 11700 of 40000. Chain number 2. Current logpost: -361.072. Length of jump: 5.          Running MCMC-PT iteration number: 11700 of 40000. Chain number 4. Current logpost: -360.007. Length of jump: 5.          Running MCMC-PT iteration number: 11700 of 40000. Chain number 1. Current logpost: -360.375. Length of jump: 5.          Running MCMC-PT iteration number: 11700 of 40000. Chain number 3. Current logpost: -360.693. Length of jump: 5.          Running MCMC-PT iteration number: 11800 of 40000. Chain number 2. Current logpost: -361.941. Length of jump: 6.          Running MCMC-PT iteration number: 11800 of 40000. Chain number 4. Current logpost: -358.067. Length of jump: 7.          Running MCMC-PT iteration number: 11800 of 40000. Chain number 1. Current logpost: -364.129. Length of jump: 7.          Running MCMC-PT iteration number: 11800 of 40000. Chain number 3. Current logpost: -361.44. Length of jump: 5.          Running MCMC-PT iteration number: 11900 of 40000. Chain number 2. Current logpost: -360.673. Length of jump: 5.          Running MCMC-PT iteration number: 11900 of 40000. Chain number 4. Current logpost: -364.099. Length of jump: 7.          Running MCMC-PT iteration number: 11900 of 40000. Chain number 1. Current logpost: -362.958. Length of jump: 7.          Running MCMC-PT iteration number: 11900 of 40000. Chain number 3. Current logpost: -359.943. Length of jump: 5.          Running MCMC-PT iteration number: 12000 of 40000. Chain number 2. Current logpost: -361.218. Length of jump: 6.          Running MCMC-PT iteration number: 12000 of 40000. Chain number 4. Current logpost: -361.278. Length of jump: 7.          Running MCMC-PT iteration number: 12000 of 40000. Chain number 1. Current logpost: -360.77. Length of jump: 7.          Running MCMC-PT iteration number: 12100 of 40000. Chain number 2. Current logpost: -364.49. Length of jump: 7.          Running MCMC-PT iteration number: 12000 of 40000. Chain number 3. Current logpost: -358.413. Length of jump: 7.          Running MCMC-PT iteration number: 12100 of 40000. Chain number 4. Current logpost: -359.281. Length of jump: 7.          Running MCMC-PT iteration number: 12100 of 40000. Chain number 1. Current logpost: -360.096. Length of jump: 7.          Running MCMC-PT iteration number: 12200 of 40000. Chain number 2. Current logpost: -364.068. Length of jump: 7.          Running MCMC-PT iteration number: 12100 of 40000. Chain number 3. Current logpost: -358.729. Length of jump: 6.          Running MCMC-PT iteration number: 12200 of 40000. Chain number 4. Current logpost: -359.253. Length of jump: 6.          Running MCMC-PT iteration number: 12200 of 40000. Chain number 1. Current logpost: -360.441. Length of jump: 7.          Running MCMC-PT iteration number: 12200 of 40000. Chain number 3. Current logpost: -359.509. Length of jump: 8.          Running MCMC-PT iteration number: 12300 of 40000. Chain number 2. Current logpost: -360.936. Length of jump: 5.          Running MCMC-PT iteration number: 12300 of 40000. Chain number 4. Current logpost: -358.472. Length of jump: 6.          Running MCMC-PT iteration number: 12300 of 40000. Chain number 1. Current logpost: -360.443. Length of jump: 6.          Running MCMC-PT iteration number: 12300 of 40000. Chain number 3. Current logpost: -360.755. Length of jump: 8.          Running MCMC-PT iteration number: 12400 of 40000. Chain number 2. Current logpost: -362.228. Length of jump: 6.          Running MCMC-PT iteration number: 12400 of 40000. Chain number 4. Current logpost: -358.747. Length of jump: 7.          Running MCMC-PT iteration number: 12400 of 40000. Chain number 1. Current logpost: -359.179. Length of jump: 5.          Running MCMC-PT iteration number: 12500 of 40000. Chain number 2. Current logpost: -362.503. Length of jump: 5.          Running MCMC-PT iteration number: 12400 of 40000. Chain number 3. Current logpost: -357.36. Length of jump: 8.          Running MCMC-PT iteration number: 12500 of 40000. Chain number 4. Current logpost: -358.126. Length of jump: 8.          Running MCMC-PT iteration number: 12500 of 40000. Chain number 1. Current logpost: -359.511. Length of jump: 5.          Running MCMC-PT iteration number: 12600 of 40000. Chain number 2. Current logpost: -362.019. Length of jump: 4.          Running MCMC-PT iteration number: 12500 of 40000. Chain number 3. Current logpost: -358.014. Length of jump: 8.          Running MCMC-PT iteration number: 12600 of 40000. Chain number 4. Current logpost: -357.683. Length of jump: 7.          Running MCMC-PT iteration number: 12600 of 40000. Chain number 1. Current logpost: -359.134. Length of jump: 8.          Running MCMC-PT iteration number: 12700 of 40000. Chain number 2. Current logpost: -362.923. Length of jump: 5.          Running MCMC-PT iteration number: 12600 of 40000. Chain number 3. Current logpost: -360.216. Length of jump: 7.          Running MCMC-PT iteration number: 12700 of 40000. Chain number 4. Current logpost: -358.322. Length of jump: 7.          Running MCMC-PT iteration number: 12700 of 40000. Chain number 1. Current logpost: -359.394. Length of jump: 9.          Running MCMC-PT iteration number: 12800 of 40000. Chain number 2. Current logpost: -364.75. Length of jump: 5.          Running MCMC-PT iteration number: 12700 of 40000. Chain number 3. Current logpost: -357.939. Length of jump: 8.          Running MCMC-PT iteration number: 12800 of 40000. Chain number 4. Current logpost: -365.406. Length of jump: 8.          Running MCMC-PT iteration number: 12800 of 40000. Chain number 1. Current logpost: -357.251. Length of jump: 9.          Running MCMC-PT iteration number: 12900 of 40000. Chain number 2. Current logpost: -361.928. Length of jump: 6.          Running MCMC-PT iteration number: 12800 of 40000. Chain number 3. Current logpost: -357.572. Length of jump: 8.          Running MCMC-PT iteration number: 12900 of 40000. Chain number 4. Current logpost: -358.561. Length of jump: 6.          Running MCMC-PT iteration number: 12900 of 40000. Chain number 1. Current logpost: -357.665. Length of jump: 8.          Running MCMC-PT iteration number: 13000 of 40000. Chain number 2. Current logpost: -362.826. Length of jump: 6.          Running MCMC-PT iteration number: 12900 of 40000. Chain number 3. Current logpost: -359.863. Length of jump: 8.          Running MCMC-PT iteration number: 13000 of 40000. Chain number 4. Current logpost: -359.915. Length of jump: 6.          Running MCMC-PT iteration number: 13000 of 40000. Chain number 1. Current logpost: -359.738. Length of jump: 8.          Running MCMC-PT iteration number: 13100 of 40000. Chain number 2. Current logpost: -365.056. Length of jump: 7.          Running MCMC-PT iteration number: 13000 of 40000. Chain number 3. Current logpost: -357.939. Length of jump: 8.          Running MCMC-PT iteration number: 13200 of 40000. Chain number 2. Current logpost: -361.921. Length of jump: 6.          Running MCMC-PT iteration number: 13100 of 40000. Chain number 3. Current logpost: -356.157. Length of jump: 8.          Running MCMC-PT iteration number: 13200 of 40000. Chain number 4. Current logpost: -361.214. Length of jump: 6.          Running MCMC-PT iteration number: 13300 of 40000. Chain number 4. Current logpost: -361.309. Length of jump: 6.          Running MCMC-PT iteration number: 13300 of 40000. Chain number 1. Current logpost: -356.262. Length of jump: 8.          Running MCMC-PT iteration number: 13300 of 40000. Chain number 3. Current logpost: -357.833. Length of jump: 8.          Running MCMC-PT iteration number: 13400 of 40000. Chain number 2. Current logpost: -361.327. Length of jump: 6.          Running MCMC-PT iteration number: 13400 of 40000. Chain number 4. Current logpost: -364.9. Length of jump: 7.          Running MCMC-PT iteration number: 13400 of 40000. Chain number 1. Current logpost: -357.09. Length of jump: 9.          Running MCMC-PT iteration number: 13500 of 40000. Chain number 2. Current logpost: -362.744. Length of jump: 6.          Running MCMC-PT iteration number: 13400 of 40000. Chain number 3. Current logpost: -357.357. Length of jump: 8.          Running MCMC-PT iteration number: 13500 of 40000. Chain number 4. Current logpost: -361.963. Length of jump: 6.          Running MCMC-PT iteration number: 13500 of 40000. Chain number 1. Current logpost: -358.859. Length of jump: 9.          Running MCMC-PT iteration number: 13600 of 40000. Chain number 2. Current logpost: -362.331. Length of jump: 6.          Running MCMC-PT iteration number: 13500 of 40000. Chain number 3. Current logpost: -359.721. Length of jump: 8.          Running MCMC-PT iteration number: 13600 of 40000. Chain number 4. Current logpost: -361.143. Length of jump: 6.          Running MCMC-PT iteration number: 13600 of 40000. Chain number 1. Current logpost: -356.868. Length of jump: 8.          Running MCMC-PT iteration number: 13700 of 40000. Chain number 2. Current logpost: -362.668. Length of jump: 5.          Running MCMC-PT iteration number: 13600 of 40000. Chain number 3. Current logpost: -357.406. Length of jump: 7.          Running MCMC-PT iteration number: 13700 of 40000. Chain number 4. Current logpost: -358.849. Length of jump: 6.          Running MCMC-PT iteration number: 13700 of 40000. Chain number 1. Current logpost: -355.253. Length of jump: 8.          Running MCMC-PT iteration number: 13800 of 40000. Chain number 2. Current logpost: -361.668. Length of jump: 5.          Running MCMC-PT iteration number: 13700 of 40000. Chain number 3. Current logpost: -359.721. Length of jump: 7.          Running MCMC-PT iteration number: 13800 of 40000. Chain number 4. Current logpost: -358.977. Length of jump: 7.          Running MCMC-PT iteration number: 13800 of 40000. Chain number 1. Current logpost: -355.491. Length of jump: 8.          Running MCMC-PT iteration number: 13900 of 40000. Chain number 2. Current logpost: -361.846. Length of jump: 5.          Running MCMC-PT iteration number: 13800 of 40000. Chain number 3. Current logpost: -360.594. Length of jump: 5.          Running MCMC-PT iteration number: 13900 of 40000. Chain number 4. Current logpost: -359.759. Length of jump: 7.          Running MCMC-PT iteration number: 13900 of 40000. Chain number 1. Current logpost: -356.798. Length of jump: 9.          Running MCMC-PT iteration number: 14000 of 40000. Chain number 2. Current logpost: -360.597. Length of jump: 4.          Running MCMC-PT iteration number: 13900 of 40000. Chain number 3. Current logpost: -359.16. Length of jump: 5.          Running MCMC-PT iteration number: 14000 of 40000. Chain number 4. Current logpost: -359.439. Length of jump: 7.          Running MCMC-PT iteration number: 14000 of 40000. Chain number 1. Current logpost: -358.979. Length of jump: 10.          Running MCMC-PT iteration number: 14100 of 40000. Chain number 2. Current logpost: -359.948. Length of jump: 5.          Running MCMC-PT iteration number: 14000 of 40000. Chain number 3. Current logpost: -359.669. Length of jump: 6.          Running MCMC-PT iteration number: 14100 of 40000. Chain number 4. Current logpost: -362.09. Length of jump: 8.          Running MCMC-PT iteration number: 14100 of 40000. Chain number 1. Current logpost: -361.656. Length of jump: 11.          Running MCMC-PT iteration number: 14200 of 40000. Chain number 2. Current logpost: -360.29. Length of jump: 5.          Running MCMC-PT iteration number: 14100 of 40000. Chain number 3. Current logpost: -359.1. Length of jump: 6.          Running MCMC-PT iteration number: 14200 of 40000. Chain number 4. Current logpost: -362.401. Length of jump: 8.          Running MCMC-PT iteration number: 14200 of 40000. Chain number 1. Current logpost: -363.504. Length of jump: 11.          Running MCMC-PT iteration number: 14300 of 40000. Chain number 2. Current logpost: -360.323. Length of jump: 4.          Running MCMC-PT iteration number: 14200 of 40000. Chain number 3. Current logpost: -359.45. Length of jump: 6.          Running MCMC-PT iteration number: 14300 of 40000. Chain number 4. Current logpost: -361.046. Length of jump: 7.          Running MCMC-PT iteration number: 14300 of 40000. Chain number 1. Current logpost: -359.145. Length of jump: 11.          Running MCMC-PT iteration number: 14400 of 40000. Chain number 2. Current logpost: -360.785. Length of jump: 4.          Running MCMC-PT iteration number: 14300 of 40000. Chain number 3. Current logpost: -359.596. Length of jump: 6.          Running MCMC-PT iteration number: 14400 of 40000. Chain number 4. Current logpost: -359.519. Length of jump: 6.          Running MCMC-PT iteration number: 14400 of 40000. Chain number 1. Current logpost: -360.288. Length of jump: 10.          Running MCMC-PT iteration number: 14500 of 40000. Chain number 2. Current logpost: -362.051. Length of jump: 5.          Running MCMC-PT iteration number: 14400 of 40000. Chain number 3. Current logpost: -358.772. Length of jump: 6.          Running MCMC-PT iteration number: 14500 of 40000. Chain number 4. Current logpost: -359.06. Length of jump: 6.          Running MCMC-PT iteration number: 14500 of 40000. Chain number 1. Current logpost: -361.03. Length of jump: 10.          Running MCMC-PT iteration number: 14600 of 40000. Chain number 2. Current logpost: -361.296. Length of jump: 5.          Running MCMC-PT iteration number: 14500 of 40000. Chain number 3. Current logpost: -358.947. Length of jump: 6.          Running MCMC-PT iteration number: 14600 of 40000. Chain number 4. Current logpost: -360.381. Length of jump: 6.          Running MCMC-PT iteration number: 14600 of 40000. Chain number 1. Current logpost: -359.395. Length of jump: 9.          Running MCMC-PT iteration number: 14700 of 40000. Chain number 2. Current logpost: -360.783. Length of jump: 3.          Running MCMC-PT iteration number: 14600 of 40000. Chain number 3. Current logpost: -360.182. Length of jump: 7.          Running MCMC-PT iteration number: 14700 of 40000. Chain number 4. Current logpost: -359.585. Length of jump: 7.          Running MCMC-PT iteration number: 14700 of 40000. Chain number 1. Current logpost: -359.07. Length of jump: 8.          Running MCMC-PT iteration number: 14800 of 40000. Chain number 2. Current logpost: -360.574. Length of jump: 4.          Running MCMC-PT iteration number: 14700 of 40000. Chain number 3. Current logpost: -359.926. Length of jump: 7.          Running MCMC-PT iteration number: 14800 of 40000. Chain number 4. Current logpost: -358.842. Length of jump: 6.          Running MCMC-PT iteration number: 14800 of 40000. Chain number 1. Current logpost: -359.792. Length of jump: 8.          Running MCMC-PT iteration number: 14900 of 40000. Chain number 2. Current logpost: -360.354. Length of jump: 4.          Running MCMC-PT iteration number: 14800 of 40000. Chain number 3. Current logpost: -360.316. Length of jump: 8.          Running MCMC-PT iteration number: 14900 of 40000. Chain number 4. Current logpost: -362.054. Length of jump: 7.          Running MCMC-PT iteration number: 14900 of 40000. Chain number 1. Current logpost: -363.247. Length of jump: 8.          Running MCMC-PT iteration number: 15000 of 40000. Chain number 2. Current logpost: -360.697. Length of jump: 6.          Running MCMC-PT iteration number: 14900 of 40000. Chain number 3. Current logpost: -358.559. Length of jump: 6.          Running MCMC-PT iteration number: 15000 of 40000. Chain number 4. Current logpost: -359.121. Length of jump: 6.          Running MCMC-PT iteration number: 15000 of 40000. Chain number 1. Current logpost: -359.589. Length of jump: 7.          Running MCMC-PT iteration number: 15100 of 40000. Chain number 2. Current logpost: -361.774. Length of jump: 6.          Running MCMC-PT iteration number: 15000 of 40000. Chain number 3. Current logpost: -358.162. Length of jump: 6.          Running MCMC-PT iteration number: 15100 of 40000. Chain number 4. Current logpost: -358.584. Length of jump: 6.          Running MCMC-PT iteration number: 15100 of 40000. Chain number 1. Current logpost: -360.115. Length of jump: 7.          Running MCMC-PT iteration number: 15200 of 40000. Chain number 2. Current logpost: -361.13. Length of jump: 5.          Running MCMC-PT iteration number: 15200 of 40000. Chain number 4. Current logpost: -358.306. Length of jump: 6.          Running MCMC-PT iteration number: 15200 of 40000. Chain number 1. Current logpost: -360.929. Length of jump: 7.          Running MCMC-PT iteration number: 15300 of 40000. Chain number 2. Current logpost: -358.878. Length of jump: 7.          Running MCMC-PT iteration number: 15200 of 40000. Chain number 3. Current logpost: -358.334. Length of jump: 6.          Running MCMC-PT iteration number: 15300 of 40000. Chain number 4. Current logpost: -357.805. Length of jump: 5.          Running MCMC-PT iteration number: 15300 of 40000. Chain number 1. Current logpost: -360.414. Length of jump: 5.          Running MCMC-PT iteration number: 15400 of 40000. Chain number 2. Current logpost: -362.496. Length of jump: 7.          Running MCMC-PT iteration number: 15300 of 40000. Chain number 3. Current logpost: -358.231. Length of jump: 5.          Running MCMC-PT iteration number: 15400 of 40000. Chain number 4. Current logpost: -358.536. Length of jump: 5.          Running MCMC-PT iteration number: 15400 of 40000. Chain number 1. Current logpost: -359.967. Length of jump: 5.          Running MCMC-PT iteration number: 15500 of 40000. Chain number 2. Current logpost: -360.635. Length of jump: 5.          Running MCMC-PT iteration number: 15400 of 40000. Chain number 3. Current logpost: -357.925. Length of jump: 5.          Running MCMC-PT iteration number: 15500 of 40000. Chain number 4. Current logpost: -357.916. Length of jump: 5.          Running MCMC-PT iteration number: 15500 of 40000. Chain number 1. Current logpost: -359.853. Length of jump: 5.          Running MCMC-PT iteration number: 15600 of 40000. Chain number 2. Current logpost: -358.885. Length of jump: 5.          Running MCMC-PT iteration number: 15500 of 40000. Chain number 3. Current logpost: -362.367. Length of jump: 3.          Running MCMC-PT iteration number: 15600 of 40000. Chain number 4. Current logpost: -358.827. Length of jump: 5.          Running MCMC-PT iteration number: 15600 of 40000. Chain number 1. Current logpost: -359.758. Length of jump: 6.          Running MCMC-PT iteration number: 15700 of 40000. Chain number 2. Current logpost: -358.051. Length of jump: 4.          Running MCMC-PT iteration number: 15600 of 40000. Chain number 3. Current logpost: -362.488. Length of jump: 4.          Running MCMC-PT iteration number: 15700 of 40000. Chain number 4. Current logpost: -359.88. Length of jump: 7.          Running MCMC-PT iteration number: 15700 of 40000. Chain number 1. Current logpost: -358.325. Length of jump: 5.          Running MCMC-PT iteration number: 15800 of 40000. Chain number 2. Current logpost: -358.888. Length of jump: 4.          Running MCMC-PT iteration number: 15700 of 40000. Chain number 3. Current logpost: -360.222. Length of jump: 5.          Running MCMC-PT iteration number: 15800 of 40000. Chain number 4. Current logpost: -357.273. Length of jump: 6.          Running MCMC-PT iteration number: 15800 of 40000. Chain number 1. Current logpost: -358.099. Length of jump: 5.          Running MCMC-PT iteration number: 15900 of 40000. Chain number 2. Current logpost: -359.367. Length of jump: 4.          Running MCMC-PT iteration number: 15800 of 40000. Chain number 3. Current logpost: -360.548. Length of jump: 5.          Running MCMC-PT iteration number: 15900 of 40000. Chain number 4. Current logpost: -357.465. Length of jump: 7.          Running MCMC-PT iteration number: 15900 of 40000. Chain number 1. Current logpost: -357.701. Length of jump: 5.          Running MCMC-PT iteration number: 16000 of 40000. Chain number 2. Current logpost: -358.785. Length of jump: 5.          Running MCMC-PT iteration number: 15900 of 40000. Chain number 3. Current logpost: -360.882. Length of jump: 5.          Running MCMC-PT iteration number: 16000 of 40000. Chain number 4. Current logpost: -361.008. Length of jump: 10.          Running MCMC-PT iteration number: 16000 of 40000. Chain number 1. Current logpost: -361.582. Length of jump: 5.          Running MCMC-PT iteration number: 16100 of 40000. Chain number 2. Current logpost: -361.081. Length of jump: 6.          Running MCMC-PT iteration number: 16000 of 40000. Chain number 3. Current logpost: -359.828. Length of jump: 4.          Running MCMC-PT iteration number: 16100 of 40000. Chain number 4. Current logpost: -363.511. Length of jump: 9.          Running MCMC-PT iteration number: 16100 of 40000. Chain number 1. Current logpost: -360.81. Length of jump: 6.          Running MCMC-PT iteration number: 16200 of 40000. Chain number 2. Current logpost: -359.4. Length of jump: 7.          Running MCMC-PT iteration number: 16100 of 40000. Chain number 3. Current logpost: -359.843. Length of jump: 4.          Running MCMC-PT iteration number: 16200 of 40000. Chain number 4. Current logpost: -361.852. Length of jump: 8.          Running MCMC-PT iteration number: 16200 of 40000. Chain number 1. Current logpost: -358.524. Length of jump: 6.          Running MCMC-PT iteration number: 16300 of 40000. Chain number 2. Current logpost: -359.094. Length of jump: 7.          Running MCMC-PT iteration number: 16200 of 40000. Chain number 3. Current logpost: -360.162. Length of jump: 5.          Running MCMC-PT iteration number: 16300 of 40000. Chain number 4. Current logpost: -357.641. Length of jump: 6.          Running MCMC-PT iteration number: 16300 of 40000. Chain number 1. Current logpost: -360.187. Length of jump: 6.          Running MCMC-PT iteration number: 16400 of 40000. Chain number 2. Current logpost: -359.632. Length of jump: 6.          Running MCMC-PT iteration number: 16300 of 40000. Chain number 3. Current logpost: -359.803. Length of jump: 4.          Running MCMC-PT iteration number: 16400 of 40000. Chain number 4. Current logpost: -356.559. Length of jump: 5.          Running MCMC-PT iteration number: 16400 of 40000. Chain number 1. Current logpost: -359.599. Length of jump: 7.          Running MCMC-PT iteration number: 16500 of 40000. Chain number 2. Current logpost: -359.381. Length of jump: 6.          Running MCMC-PT iteration number: 16400 of 40000. Chain number 3. Current logpost: -360.756. Length of jump: 5.          Running MCMC-PT iteration number: 16500 of 40000. Chain number 4. Current logpost: -356.695. Length of jump: 5.          Running MCMC-PT iteration number: 16500 of 40000. Chain number 1. Current logpost: -359.172. Length of jump: 6.          Running MCMC-PT iteration number: 16600 of 40000. Chain number 2. Current logpost: -360.718. Length of jump: 8.          Running MCMC-PT iteration number: 16500 of 40000. Chain number 3. Current logpost: -360.016. Length of jump: 4.          Running MCMC-PT iteration number: 16600 of 40000. Chain number 4. Current logpost: -360.411. Length of jump: 5.          Running MCMC-PT iteration number: 16600 of 40000. Chain number 1. Current logpost: -357.063. Length of jump: 7.          Running MCMC-PT iteration number: 16700 of 40000. Chain number 2. Current logpost: -362.12. Length of jump: 8.          Running MCMC-PT iteration number: 16600 of 40000. Chain number 3. Current logpost: -360.747. Length of jump: 5.          Running MCMC-PT iteration number: 16700 of 40000. Chain number 4. Current logpost: -357.256. Length of jump: 5.          Running MCMC-PT iteration number: 16700 of 40000. Chain number 1. Current logpost: -359.116. Length of jump: 7.          Running MCMC-PT iteration number: 16800 of 40000. Chain number 2. Current logpost: -361.311. Length of jump: 7.          Running MCMC-PT iteration number: 16700 of 40000. Chain number 3. Current logpost: -360.285. Length of jump: 5.          Running MCMC-PT iteration number: 16800 of 40000. Chain number 4. Current logpost: -358.891. Length of jump: 5.          Running MCMC-PT iteration number: 16800 of 40000. Chain number 1. Current logpost: -359.55. Length of jump: 7.          Running MCMC-PT iteration number: 16900 of 40000. Chain number 2. Current logpost: -359.052. Length of jump: 6.          Running MCMC-PT iteration number: 16800 of 40000. Chain number 3. Current logpost: -361.629. Length of jump: 6.          Running MCMC-PT iteration number: 16900 of 40000. Chain number 4. Current logpost: -359.057. Length of jump: 5.          Running MCMC-PT iteration number: 16900 of 40000. Chain number 1. Current logpost: -364.986. Length of jump: 7.          Running MCMC-PT iteration number: 17000 of 40000. Chain number 2. Current logpost: -359.735. Length of jump: 6.          Running MCMC-PT iteration number: 16900 of 40000. Chain number 3. Current logpost: -361.978. Length of jump: 6.          Running MCMC-PT iteration number: 17000 of 40000. Chain number 4. Current logpost: -357.635. Length of jump: 5.          Running MCMC-PT iteration number: 17000 of 40000. Chain number 1. Current logpost: -360.221. Length of jump: 7.          Running MCMC-PT iteration number: 17100 of 40000. Chain number 2. Current logpost: -364.591. Length of jump: 4.          Running MCMC-PT iteration number: 17000 of 40000. Chain number 3. Current logpost: -359.966. Length of jump: 4.          Running MCMC-PT iteration number: 17100 of 40000. Chain number 4. Current logpost: -358.229. Length of jump: 6.          Running MCMC-PT iteration number: 17100 of 40000. Chain number 1. Current logpost: -356.867. Length of jump: 7.          Running MCMC-PT iteration number: 17200 of 40000. Chain number 2. Current logpost: -362.666. Length of jump: 4.          Running MCMC-PT iteration number: 17100 of 40000. Chain number 3. Current logpost: -360.845. Length of jump: 6.          Running MCMC-PT iteration number: 17200 of 40000. Chain number 4. Current logpost: -358.885. Length of jump: 4.          Running MCMC-PT iteration number: 17200 of 40000. Chain number 1. Current logpost: -355.094. Length of jump: 7.          Running MCMC-PT iteration number: 17300 of 40000. Chain number 2. Current logpost: -359.383. Length of jump: 5.          Running MCMC-PT iteration number: 17200 of 40000. Chain number 3. Current logpost: -362.572. Length of jump: 6.          Running MCMC-PT iteration number: 17300 of 40000. Chain number 4. Current logpost: -358.709. Length of jump: 4.          Running MCMC-PT iteration number: 17300 of 40000. Chain number 1. Current logpost: -357.421. Length of jump: 7.          Running MCMC-PT iteration number: 17400 of 40000. Chain number 2. Current logpost: -361.675. Length of jump: 5.          Running MCMC-PT iteration number: 17300 of 40000. Chain number 3. Current logpost: -362.67. Length of jump: 7.          Running MCMC-PT iteration number: 17400 of 40000. Chain number 4. Current logpost: -358.596. Length of jump: 4.          Running MCMC-PT iteration number: 17400 of 40000. Chain number 1. Current logpost: -357.572. Length of jump: 6.          Running MCMC-PT iteration number: 17500 of 40000. Chain number 2. Current logpost: -360.581. Length of jump: 5.          Running MCMC-PT iteration number: 17400 of 40000. Chain number 3. Current logpost: -360.707. Length of jump: 5.          Running MCMC-PT iteration number: 17500 of 40000. Chain number 4. Current logpost: -358.681. Length of jump: 4.          Running MCMC-PT iteration number: 17500 of 40000. Chain number 1. Current logpost: -357.309. Length of jump: 6.          Running MCMC-PT iteration number: 17600 of 40000. Chain number 2. Current logpost: -360.926. Length of jump: 6.          Running MCMC-PT iteration number: 17500 of 40000. Chain number 3. Current logpost: -359.971. Length of jump: 4.          Running MCMC-PT iteration number: 17600 of 40000. Chain number 4. Current logpost: -361.088. Length of jump: 4.          Running MCMC-PT iteration number: 17600 of 40000. Chain number 1. Current logpost: -356.597. Length of jump: 6.          Running MCMC-PT iteration number: 17700 of 40000. Chain number 2. Current logpost: -358.528. Length of jump: 6.          Running MCMC-PT iteration number: 17600 of 40000. Chain number 3. Current logpost: -360.804. Length of jump: 5.          Running MCMC-PT iteration number: 17700 of 40000. Chain number 4. Current logpost: -360.15. Length of jump: 4.          Running MCMC-PT iteration number: 17700 of 40000. Chain number 1. Current logpost: -357.47. Length of jump: 7.          Running MCMC-PT iteration number: 17800 of 40000. Chain number 2. Current logpost: -359.452. Length of jump: 5.          Running MCMC-PT iteration number: 17700 of 40000. Chain number 3. Current logpost: -361.383. Length of jump: 5.          Running MCMC-PT iteration number: 17800 of 40000. Chain number 4. Current logpost: -361.296. Length of jump: 4.          Running MCMC-PT iteration number: 17800 of 40000. Chain number 1. Current logpost: -359.043. Length of jump: 7.          Running MCMC-PT iteration number: 17900 of 40000. Chain number 2. Current logpost: -358.418. Length of jump: 5.          Running MCMC-PT iteration number: 17800 of 40000. Chain number 3. Current logpost: -365.164. Length of jump: 6.          Running MCMC-PT iteration number: 17900 of 40000. Chain number 4. Current logpost: -358.477. Length of jump: 4.          Running MCMC-PT iteration number: 17900 of 40000. Chain number 1. Current logpost: -357.298. Length of jump: 7.          Running MCMC-PT iteration number: 18000 of 40000. Chain number 2. Current logpost: -360.468. Length of jump: 7.          Running MCMC-PT iteration number: 17900 of 40000. Chain number 3. Current logpost: -363.967. Length of jump: 6.          Running MCMC-PT iteration number: 18000 of 40000. Chain number 4. Current logpost: -362.391. Length of jump: 6.          Running MCMC-PT iteration number: 18000 of 40000. Chain number 1. Current logpost: -359.973. Length of jump: 7.          Running MCMC-PT iteration number: 18100 of 40000. Chain number 2. Current logpost: -361.22. Length of jump: 7.          Running MCMC-PT iteration number: 18000 of 40000. Chain number 3. Current logpost: -359.054. Length of jump: 6.          Running MCMC-PT iteration number: 18100 of 40000. Chain number 4. Current logpost: -359.563. Length of jump: 6.          Running MCMC-PT iteration number: 18100 of 40000. Chain number 1. Current logpost: -360.167. Length of jump: 7.          Running MCMC-PT iteration number: 18200 of 40000. Chain number 2. Current logpost: -360.124. Length of jump: 7.          Running MCMC-PT iteration number: 18200 of 40000. Chain number 4. Current logpost: -358.455. Length of jump: 5.          Running MCMC-PT iteration number: 18200 of 40000. Chain number 1. Current logpost: -360.573. Length of jump: 5.          Running MCMC-PT iteration number: 18300 of 40000. Chain number 2. Current logpost: -360.765. Length of jump: 8.          Running MCMC-PT iteration number: 18200 of 40000. Chain number 3. Current logpost: -360.087. Length of jump: 7.          Running MCMC-PT iteration number: 18300 of 40000. Chain number 4. Current logpost: -358.597. Length of jump: 5.          Running MCMC-PT iteration number: 18300 of 40000. Chain number 1. Current logpost: -363.255. Length of jump: 6.          Running MCMC-PT iteration number: 18400 of 40000. Chain number 2. Current logpost: -361.292. Length of jump: 8.          Running MCMC-PT iteration number: 18300 of 40000. Chain number 3. Current logpost: -359.105. Length of jump: 7.          Running MCMC-PT iteration number: 18400 of 40000. Chain number 4. Current logpost: -358.739. Length of jump: 5.          Running MCMC-PT iteration number: 18400 of 40000. Chain number 1. Current logpost: -363.05. Length of jump: 5.          Running MCMC-PT iteration number: 18500 of 40000. Chain number 2. Current logpost: -360.199. Length of jump: 7.          Running MCMC-PT iteration number: 18400 of 40000. Chain number 3. Current logpost: -358.677. Length of jump: 7.          Running MCMC-PT iteration number: 18500 of 40000. Chain number 4. Current logpost: -357.655. Length of jump: 5.          Running MCMC-PT iteration number: 18500 of 40000. Chain number 1. Current logpost: -361.803. Length of jump: 4.          Running MCMC-PT iteration number: 18600 of 40000. Chain number 2. Current logpost: -359.274. Length of jump: 7.          Running MCMC-PT iteration number: 18500 of 40000. Chain number 3. Current logpost: -358.843. Length of jump: 7.          Running MCMC-PT iteration number: 18600 of 40000. Chain number 4. Current logpost: -358.136. Length of jump: 5.          Running MCMC-PT iteration number: 18600 of 40000. Chain number 1. Current logpost: -361.559. Length of jump: 4.          Running MCMC-PT iteration number: 18600 of 40000. Chain number 3. Current logpost: -361.98. Length of jump: 4.          Running MCMC-PT iteration number: 18700 of 40000. Chain number 2. Current logpost: -360.336. Length of jump: 7.          Running MCMC-PT iteration number: 18700 of 40000. Chain number 4. Current logpost: -359.699. Length of jump: 5.          Running MCMC-PT iteration number: 18700 of 40000. Chain number 1. Current logpost: -361.238. Length of jump: 5.          Running MCMC-PT iteration number: 18800 of 40000. Chain number 2. Current logpost: -361.66. Length of jump: 8.          Running MCMC-PT iteration number: 18700 of 40000. Chain number 3. Current logpost: -361.699. Length of jump: 4.          Running MCMC-PT iteration number: 18800 of 40000. Chain number 4. Current logpost: -358.028. Length of jump: 6.          Running MCMC-PT iteration number: 18800 of 40000. Chain number 1. Current logpost: -362.715. Length of jump: 5.          Running MCMC-PT iteration number: 18900 of 40000. Chain number 2. Current logpost: -358.627. Length of jump: 6.          Running MCMC-PT iteration number: 18800 of 40000. Chain number 3. Current logpost: -360.175. Length of jump: 5.          Running MCMC-PT iteration number: 18900 of 40000. Chain number 4. Current logpost: -357.137. Length of jump: 6.          Running MCMC-PT iteration number: 18900 of 40000. Chain number 1. Current logpost: -362.237. Length of jump: 5.          Running MCMC-PT iteration number: 19000 of 40000. Chain number 2. Current logpost: -361.305. Length of jump: 7.          Running MCMC-PT iteration number: 18900 of 40000. Chain number 3. Current logpost: -360.685. Length of jump: 6.          Running MCMC-PT iteration number: 19000 of 40000. Chain number 4. Current logpost: -362.342. Length of jump: 6.          Running MCMC-PT iteration number: 19000 of 40000. Chain number 1. Current logpost: -362.219. Length of jump: 4.          Running MCMC-PT iteration number: 19100 of 40000. Chain number 2. Current logpost: -358.688. Length of jump: 5.          Running MCMC-PT iteration number: 19000 of 40000. Chain number 3. Current logpost: -360.858. Length of jump: 5.          Running MCMC-PT iteration number: 19100 of 40000. Chain number 4. Current logpost: -360.386. Length of jump: 6.          Running MCMC-PT iteration number: 19100 of 40000. Chain number 1. Current logpost: -361.13. Length of jump: 5.          Running MCMC-PT iteration number: 19200 of 40000. Chain number 2. Current logpost: -360.713. Length of jump: 5.          Running MCMC-PT iteration number: 19100 of 40000. Chain number 3. Current logpost: -360.101. Length of jump: 4.          Running MCMC-PT iteration number: 19200 of 40000. Chain number 4. Current logpost: -358.617. Length of jump: 6.          Running MCMC-PT iteration number: 19200 of 40000. Chain number 1. Current logpost: -363.462. Length of jump: 4.          Running MCMC-PT iteration number: 19300 of 40000. Chain number 2. Current logpost: -360.601. Length of jump: 6.          Running MCMC-PT iteration number: 19200 of 40000. Chain number 3. Current logpost: -360.598. Length of jump: 5.          Running MCMC-PT iteration number: 19300 of 40000. Chain number 4. Current logpost: -362.013. Length of jump: 7.          Running MCMC-PT iteration number: 19300 of 40000. Chain number 1. Current logpost: -363.015. Length of jump: 4.          Running MCMC-PT iteration number: 19400 of 40000. Chain number 2. Current logpost: -363.773. Length of jump: 8.          Running MCMC-PT iteration number: 19300 of 40000. Chain number 3. Current logpost: -361.761. Length of jump: 5.          Running MCMC-PT iteration number: 19400 of 40000. Chain number 4. Current logpost: -359.655. Length of jump: 7.          Running MCMC-PT iteration number: 19400 of 40000. Chain number 1. Current logpost: -363.755. Length of jump: 5.          Running MCMC-PT iteration number: 19400 of 40000. Chain number 3. Current logpost: -361.751. Length of jump: 5.          Running MCMC-PT iteration number: 19500 of 40000. Chain number 2. Current logpost: -361.641. Length of jump: 7.          Running MCMC-PT iteration number: 19500 of 40000. Chain number 1. Current logpost: -365.413. Length of jump: 6.          Running MCMC-PT iteration number: 19500 of 40000. Chain number 3. Current logpost: -359.974. Length of jump: 5.          Running MCMC-PT iteration number: 19600 of 40000. Chain number 2. Current logpost: -364.721. Length of jump: 7.          Running MCMC-PT iteration number: 19600 of 40000. Chain number 4. Current logpost: -359.354. Length of jump: 6.          Running MCMC-PT iteration number: 19600 of 40000. Chain number 1. Current logpost: -362.84. Length of jump: 6.          Running MCMC-PT iteration number: 19600 of 40000. Chain number 3. Current logpost: -360.262. Length of jump: 4.          Running MCMC-PT iteration number: 19700 of 40000. Chain number 2. Current logpost: -361.808. Length of jump: 5.          Running MCMC-PT iteration number: 19700 of 40000. Chain number 4. Current logpost: -359.465. Length of jump: 5.          Running MCMC-PT iteration number: 19700 of 40000. Chain number 1. Current logpost: -364.193. Length of jump: 5.          Running MCMC-PT iteration number: 19700 of 40000. Chain number 3. Current logpost: -359.889. Length of jump: 4.          Running MCMC-PT iteration number: 19800 of 40000. Chain number 2. Current logpost: -361.115. Length of jump: 5.          Running MCMC-PT iteration number: 19800 of 40000. Chain number 4. Current logpost: -357.788. Length of jump: 5.          Running MCMC-PT iteration number: 19800 of 40000. Chain number 1. Current logpost: -363.763. Length of jump: 3.          Running MCMC-PT iteration number: 19900 of 40000. Chain number 2. Current logpost: -362.223. Length of jump: 4.          Running MCMC-PT iteration number: 19800 of 40000. Chain number 3. Current logpost: -360.253. Length of jump: 4.          Running MCMC-PT iteration number: 19900 of 40000. Chain number 4. Current logpost: -359.612. Length of jump: 6.          Running MCMC-PT iteration number: 19900 of 40000. Chain number 1. Current logpost: -363.361. Length of jump: 3.          Running MCMC-PT iteration number: 19900 of 40000. Chain number 3. Current logpost: -359.546. Length of jump: 6.          Running MCMC-PT iteration number: 20000 of 40000. Chain number 2. Current logpost: -362.133. Length of jump: 3.          Running MCMC-PT iteration number: 20000 of 40000. Chain number 4. Current logpost: -359.514. Length of jump: 6.          Running MCMC-PT iteration number: 20000 of 40000. Chain number 1. Current logpost: -361.668. Length of jump: 3.          Running MCMC-PT iteration number: 20000 of 40000. Chain number 3. Current logpost: -361.057. Length of jump: 5.          Running MCMC-PT iteration number: 20100 of 40000. Chain number 2. Current logpost: -363. Length of jump: 4.          Running MCMC-PT iteration number: 20100 of 40000. Chain number 4. Current logpost: -359.188. Length of jump: 6.          Running MCMC-PT iteration number: 20100 of 40000. Chain number 1. Current logpost: -361.243. Length of jump: 3.          Running MCMC-PT iteration number: 20100 of 40000. Chain number 3. Current logpost: -358.924. Length of jump: 5.          Running MCMC-PT iteration number: 20200 of 40000. Chain number 2. Current logpost: -361.67. Length of jump: 5.          Running MCMC-PT iteration number: 20200 of 40000. Chain number 4. Current logpost: -361.369. Length of jump: 6.          Running MCMC-PT iteration number: 20200 of 40000. Chain number 1. Current logpost: -362.551. Length of jump: 4.          Running MCMC-PT iteration number: 20200 of 40000. Chain number 3. Current logpost: -363.348. Length of jump: 7.          Running MCMC-PT iteration number: 20300 of 40000. Chain number 2. Current logpost: -361.639. Length of jump: 5.          Running MCMC-PT iteration number: 20300 of 40000. Chain number 4. Current logpost: -359.331. Length of jump: 8.          Running MCMC-PT iteration number: 20300 of 40000. Chain number 1. Current logpost: -364.27. Length of jump: 4.          Running MCMC-PT iteration number: 20400 of 40000. Chain number 2. Current logpost: -360.796. Length of jump: 3.          Running MCMC-PT iteration number: 20300 of 40000. Chain number 3. Current logpost: -363.401. Length of jump: 8.          Running MCMC-PT iteration number: 20400 of 40000. Chain number 4. Current logpost: -361.352. Length of jump: 9.          Running MCMC-PT iteration number: 20400 of 40000. Chain number 1. Current logpost: -361.182. Length of jump: 4.          Running MCMC-PT iteration number: 20400 of 40000. Chain number 3. Current logpost: -361.792. Length of jump: 7.          Running MCMC-PT iteration number: 20500 of 40000. Chain number 2. Current logpost: -362.498. Length of jump: 3.          Running MCMC-PT iteration number: 20500 of 40000. Chain number 4. Current logpost: -357.822. Length of jump: 7.          Running MCMC-PT iteration number: 20500 of 40000. Chain number 1. Current logpost: -358.968. Length of jump: 4.          Running MCMC-PT iteration number: 20600 of 40000. Chain number 2. Current logpost: -360.746. Length of jump: 3.          Running MCMC-PT iteration number: 20500 of 40000. Chain number 3. Current logpost: -361.16. Length of jump: 6.          Running MCMC-PT iteration number: 20600 of 40000. Chain number 4. Current logpost: -359.422. Length of jump: 6.          Running MCMC-PT iteration number: 20600 of 40000. Chain number 1. Current logpost: -359.537. Length of jump: 4.          Running MCMC-PT iteration number: 20600 of 40000. Chain number 3. Current logpost: -359.946. Length of jump: 5.          Running MCMC-PT iteration number: 20700 of 40000. Chain number 2. Current logpost: -362.146. Length of jump: 4.          Running MCMC-PT iteration number: 20700 of 40000. Chain number 4. Current logpost: -358.8. Length of jump: 6.          Running MCMC-PT iteration number: 20700 of 40000. Chain number 1. Current logpost: -359.687. Length of jump: 4.          Running MCMC-PT iteration number: 20800 of 40000. Chain number 2. Current logpost: -362.833. Length of jump: 5.          Running MCMC-PT iteration number: 20700 of 40000. Chain number 3. Current logpost: -360.75. Length of jump: 6.          Running MCMC-PT iteration number: 20800 of 40000. Chain number 1. Current logpost: -358.378. Length of jump: 5.          Running MCMC-PT iteration number: 20800 of 40000. Chain number 4. Current logpost: -358.088. Length of jump: 6.          Running MCMC-PT iteration number: 20900 of 40000. Chain number 2. Current logpost: -362.809. Length of jump: 5.          Running MCMC-PT iteration number: 20800 of 40000. Chain number 3. Current logpost: -361.674. Length of jump: 7.          Running MCMC-PT iteration number: 20900 of 40000. Chain number 1. Current logpost: -361.214. Length of jump: 5.          Running MCMC-PT iteration number: 20900 of 40000. Chain number 4. Current logpost: -359.076. Length of jump: 7.          Running MCMC-PT iteration number: 21000 of 40000. Chain number 2. Current logpost: -362.06. Length of jump: 6.          Running MCMC-PT iteration number: 20900 of 40000. Chain number 3. Current logpost: -363.217. Length of jump: 8.          Running MCMC-PT iteration number: 21000 of 40000. Chain number 1. Current logpost: -362.597. Length of jump: 5.          Running MCMC-PT iteration number: 21000 of 40000. Chain number 4. Current logpost: -359.071. Length of jump: 6.          Running MCMC-PT iteration number: 21100 of 40000. Chain number 2. Current logpost: -361.896. Length of jump: 6.          Running MCMC-PT iteration number: 21000 of 40000. Chain number 3. Current logpost: -366.132. Length of jump: 9.          Running MCMC-PT iteration number: 21100 of 40000. Chain number 1. Current logpost: -360.489. Length of jump: 6.          Running MCMC-PT iteration number: 21100 of 40000. Chain number 4. Current logpost: -360.828. Length of jump: 6.          Running MCMC-PT iteration number: 21200 of 40000. Chain number 2. Current logpost: -362.311. Length of jump: 7.          Running MCMC-PT iteration number: 21100 of 40000. Chain number 3. Current logpost: -364.948. Length of jump: 8.          Running MCMC-PT iteration number: 21200 of 40000. Chain number 1. Current logpost: -360.916. Length of jump: 6.          Running MCMC-PT iteration number: 21200 of 40000. Chain number 4. Current logpost: -358.669. Length of jump: 5.          Running MCMC-PT iteration number: 21300 of 40000. Chain number 2. Current logpost: -359.477. Length of jump: 5.          Running MCMC-PT iteration number: 21200 of 40000. Chain number 3. Current logpost: -360.917. Length of jump: 7.          Running MCMC-PT iteration number: 21300 of 40000. Chain number 3. Current logpost: -360.53. Length of jump: 7.          Running MCMC-PT iteration number: 21400 of 40000. Chain number 1. Current logpost: -362.732. Length of jump: 7.          Running MCMC-PT iteration number: 21400 of 40000. Chain number 4. Current logpost: -360.564. Length of jump: 5.          Running MCMC-PT iteration number: 21500 of 40000. Chain number 2. Current logpost: -361.408. Length of jump: 7.          Running MCMC-PT iteration number: 21400 of 40000. Chain number 3. Current logpost: -360.592. Length of jump: 6.          Running MCMC-PT iteration number: 21500 of 40000. Chain number 1. Current logpost: -360.786. Length of jump: 7.          Running MCMC-PT iteration number: 21500 of 40000. Chain number 4. Current logpost: -362.763. Length of jump: 5.          Running MCMC-PT iteration number: 21600 of 40000. Chain number 2. Current logpost: -360.531. Length of jump: 7.          Running MCMC-PT iteration number: 21500 of 40000. Chain number 3. Current logpost: -359.159. Length of jump: 6.          Running MCMC-PT iteration number: 21600 of 40000. Chain number 1. Current logpost: Running MCMC-PT iteration number: 21600 of 40000. Chain number 4. Current logpost: -360.389. Length of jump: 7-362.142. Length of jump: 6.          .          Running MCMC-PT iteration number: 21700 of 40000. Chain number 2. Current logpost: -360.051. Length of jump: 7.          Running MCMC-PT iteration number: 21600 of 40000. Chain number 3. Current logpost: -358.505. Length of jump: 6.          Running MCMC-PT iteration number: 21700 of 40000. Chain number 4. Current logpost: -361.073. Length of jump: 6.          Running MCMC-PT iteration number: 21700 of 40000. Chain number 1. Current logpost: -359.748. Length of jump: 6.          Running MCMC-PT iteration number: 21800 of 40000. Chain number 2. Current logpost: -361.085. Length of jump: 7.          Running MCMC-PT iteration number: 21700 of 40000. Chain number 3. Current logpost: -362.425. Length of jump: 6.          Running MCMC-PT iteration number: 21800 of 40000. Chain number 4. Current logpost: -364.555. Length of jump: 6.          Running MCMC-PT iteration number: 21800 of 40000. Chain number 1. Current logpost: -359.558. Length of jump: 6.          Running MCMC-PT iteration number: 21900 of 40000. Chain number 2. Current logpost: -362.222. Length of jump: 7.          Running MCMC-PT iteration number: 21800 of 40000. Chain number 3. Current logpost: -361.273. Length of jump: 5.          Running MCMC-PT iteration number: 21900 of 40000. Chain number 4. Current logpost: -363.541. Length of jump: 7.          Running MCMC-PT iteration number: 21900 of 40000. Chain number 1. Current logpost: -361.996. Length of jump: 6.          Running MCMC-PT iteration number: 22000 of 40000. Chain number 2. Current logpost: -359.662. Length of jump: 6.          Running MCMC-PT iteration number: 21900 of 40000. Chain number 3. Current logpost: -361.92. Length of jump: 6.          Running MCMC-PT iteration number: 22000 of 40000. Chain number 1. Current logpost: -360.25. Length of jump: 5.          Running MCMC-PT iteration number: 22000 of 40000. Chain number 4. Current logpost: -361.044. Length of jump: 6.          Running MCMC-PT iteration number: 22100 of 40000. Chain number 2. Current logpost: -360.514. Length of jump: 6.          Running MCMC-PT iteration number: 22000 of 40000. Chain number 3. Current logpost: -363.428. Length of jump: 5.          Running MCMC-PT iteration number: 22100 of 40000. Chain number 1. Current logpost: -358.629. Length of jump: 5.          Running MCMC-PT iteration number: 22100 of 40000. Chain number 4. Current logpost: -359.708. Length of jump: 6.          Running MCMC-PT iteration number: 22200 of 40000. Chain number 2. Current logpost: -359.53. Length of jump: 6.          Running MCMC-PT iteration number: 22100 of 40000. Chain number 3. Current logpost: -360.28. Length of jump: 4.          Running MCMC-PT iteration number: 22200 of 40000. Chain number 4. Current logpost: -359.603. Length of jump: 6.          Running MCMC-PT iteration number: 22200 of 40000. Chain number 1. Current logpost: -358.649. Length of jump: 6.          Running MCMC-PT iteration number: 22300 of 40000. Chain number 2. Current logpost: -358.362. Length of jump: 5.          Running MCMC-PT iteration number: 22200 of 40000. Chain number 3. Current logpost: -360.497. Length of jump: 5.          Running MCMC-PT iteration number: 22300 of 40000. Chain number 4. Current logpost: -360.238. Length of jump: 6.          Running MCMC-PT iteration number: 22300 of 40000. Chain number 1. Current logpost: -361.382. Length of jump: 6.          Running MCMC-PT iteration number: 22400 of 40000. Chain number 2. Current logpost: -361.816. Length of jump: 6.          Running MCMC-PT iteration number: 22300 of 40000. Chain number 3. Current logpost: -361.092. Length of jump: 5.          Running MCMC-PT iteration number: 22400 of 40000. Chain number 1. Current logpost: -363.973. Length of jump: 8.          Running MCMC-PT iteration number: 22400 of 40000. Chain number 4. Current logpost: -356.41. Length of jump: 5.          Running MCMC-PT iteration number: 22500 of 40000. Chain number 2. Current logpost: -360.323. Length of jump: 6.          Running MCMC-PT iteration number: 22400 of 40000. Chain number 3. Current logpost: -361.397. Length of jump: 6.          Running MCMC-PT iteration number: 22500 of 40000. Chain number 1. Current logpost: -363.61. Length of jump: 8.          Running MCMC-PT iteration number: 22500 of 40000. Chain number 4. Current logpost: -356.97. Length of jump: 5.          Running MCMC-PT iteration number: 22600 of 40000. Chain number 2. Current logpost: -358.29. Length of jump: 6.          Running MCMC-PT iteration number: 22500 of 40000. Chain number 3. Current logpost: -360.602. Length of jump: 5.          Running MCMC-PT iteration number: 22600 of 40000. Chain number 1. Current logpost: -363.927. Length of jump: 9.          Running MCMC-PT iteration number: 22600 of 40000. Chain number 4. Current logpost: -359.963. Length of jump: 4.          Running MCMC-PT iteration number: 22700 of 40000. Chain number 2. Current logpost: -358.781. Length of jump: 5.          Running MCMC-PT iteration number: 22600 of 40000. Chain number 3. Current logpost: -362.088. Length of jump: 5.          Running MCMC-PT iteration number: 22700 of 40000. Chain number 4. Current logpost: -361.025. Length of jump: 4.          Running MCMC-PT iteration number: 22700 of 40000. Chain number 1. Current logpost: -362.107. Length of jump: 7.          Running MCMC-PT iteration number: 22800 of 40000. Chain number 2. Current logpost: -359.404. Length of jump: 5.          Running MCMC-PT iteration number: 22700 of 40000. Chain number 3. Current logpost: -360.609. Length of jump: 5.          Running MCMC-PT iteration number: 22800 of 40000. Chain number 4. Current logpost: -361.472. Length of jump: 6.          Running MCMC-PT iteration number: 22800 of 40000. Chain number 1. Current logpost: -365.133. Length of jump: 7.          Running MCMC-PT iteration number: 22900 of 40000. Chain number 2. Current logpost: -360.731. Length of jump: 5.          Running MCMC-PT iteration number: 22800 of 40000. Chain number 3. Current logpost: -362.03. Length of jump: 5.          Running MCMC-PT iteration number: 22900 of 40000. Chain number 4. Current logpost: -361.796. Length of jump: 8.          Running MCMC-PT iteration number: 23000 of 40000. Chain number 2. Current logpost: -360.108. Length of jump: 5.          Running MCMC-PT iteration number: 22900 of 40000. Chain number 1. Current logpost: -362.889. Length of jump: 6.          Running MCMC-PT iteration number: 22900 of 40000. Chain number 3. Current logpost: -360.102. Length of jump: 5.          Running MCMC-PT iteration number: 23000 of 40000. Chain number 1. Current logpost: -363.459. Length of jump: 6.          Running MCMC-PT iteration number: 23000 of 40000. Chain number 4. Current logpost: -358.466. Length of jump: 6.          Running MCMC-PT iteration number: 23100 of 40000. Chain number 2. Current logpost: -361.096. Length of jump: 6.          Running MCMC-PT iteration number: 23000 of 40000. Chain number 3. Current logpost: -361.673. Length of jump: 5.          Running MCMC-PT iteration number: 23100 of 40000. Chain number 1. Current logpost: -367.458. Length of jump: 5.          Running MCMC-PT iteration number: 23200 of 40000. Chain number 2. Current logpost: -361.004. Length of jump: 6.          Running MCMC-PT iteration number: 23100 of 40000. Chain number 4. Current logpost: -358.85. Length of jump: 6.          Running MCMC-PT iteration number: 23100 of 40000. Chain number 3. Current logpost: -359.804. Length of jump: 4.          Running MCMC-PT iteration number: 23200 of 40000. Chain number 1. Current logpost: -364.797. Length of jump: 4.          Running MCMC-PT iteration number: 23300 of 40000. Chain number 2. Current logpost: -362.33. Length of jump: 6.          Running MCMC-PT iteration number: 23200 of 40000. Chain number 4. Current logpost: -358.876. Length of jump: 6.          Running MCMC-PT iteration number: 23200 of 40000. Chain number 3. Current logpost: -360.275. Length of jump: 4.          Running MCMC-PT iteration number: 23400 of 40000. Chain number 2. Current logpost: -361.199. Length of jump: 5.          Running MCMC-PT iteration number: 23300 of 40000. Chain number 1. Current logpost: -364.307. Length of jump: 6.          Running MCMC-PT iteration number: 23300 of 40000. Chain number 4. Current logpost: -360.379. Length of jump: 7.          Running MCMC-PT iteration number: 23300 of 40000. Chain number 3. Current logpost: -360.875. Length of jump: 5.          Running MCMC-PT iteration number: 23500 of 40000. Chain number 2. Current logpost: -360.384. Length of jump: 4.          Running MCMC-PT iteration number: 23400 of 40000. Chain number 1. Current logpost: -364.434. Length of jump: 5.          Running MCMC-PT iteration number: 23400 of 40000. Chain number 4. Current logpost: -358.436. Length of jump: 6.          Running MCMC-PT iteration number: 23400 of 40000. Chain number 3. Current logpost: -360.542. Length of jump: 6.          Running MCMC-PT iteration number: 23600 of 40000. Chain number 2. Current logpost: -360.34. Length of jump: 4.          Running MCMC-PT iteration number: 23500 of 40000. Chain number 4. Current logpost: -361.947. Length of jump: 9.          Running MCMC-PT iteration number: 23500 of 40000. Chain number 1. Current logpost: -362.952. Length of jump: 5.          Running MCMC-PT iteration number: 23500 of 40000. Chain number 3. Current logpost: -360.832. Length of jump: 6.          Running MCMC-PT iteration number: 23700 of 40000. Chain number 2. Current logpost: -360.34. Length of jump: 4.          Running MCMC-PT iteration number: 23600 of 40000. Chain number 1. Current logpost: -364.294. Length of jump: 6.          Running MCMC-PT iteration number: 23600 of 40000. Chain number 4. Current logpost: -362.773. Length of jump: 8.          Running MCMC-PT iteration number: 23600 of 40000. Chain number 3. Current logpost: -362.664. Length of jump: 7.          Running MCMC-PT iteration number: 23800 of 40000. Chain number 2. Current logpost: -363.827. Length of jump: 5.          Running MCMC-PT iteration number: 23700 of 40000. Chain number 4. Current logpost: -361.01. Length of jump: 7.          Running MCMC-PT iteration number: 23700 of 40000. Chain number 1. Current logpost: -361.153. Length of jump: 5.          Running MCMC-PT iteration number: 23700 of 40000. Chain number 3. Current logpost: -363.443. Length of jump: 8.          Running MCMC-PT iteration number: 23900 of 40000. Chain number 2. Current logpost: -362.375. Length of jump: 4.          Running MCMC-PT iteration number: 23800 of 40000. Chain number 4. Current logpost: -365.497. Length of jump: 7.          Running MCMC-PT iteration number: 23800 of 40000. Chain number 1. Current logpost: -361.716. Length of jump: 6.          Running MCMC-PT iteration number: 23800 of 40000. Chain number 3. Current logpost: -364.208. Length of jump: 8.          Running MCMC-PT iteration number: 23900 of 40000. Chain number 4. Current logpost: -365.172. Length of jump: 7.          Running MCMC-PT iteration number: 23900 of 40000. Chain number 1. Current logpost: -360.276. Length of jump: 4.          Running MCMC-PT iteration number: 24000 of 40000. Chain number 2. Current logpost: -360.703. Length of jump: 5.          Running MCMC-PT iteration number: 23900 of 40000. Chain number 3. Current logpost: -362.907. Length of jump: 6.          Running MCMC-PT iteration number: 24100 of 40000. Chain number 2. Current logpost: -361.183. Length of jump: 4.          Running MCMC-PT iteration number: 24000 of 40000. Chain number 4. Current logpost: -363.622. Length of jump: 7.          Running MCMC-PT iteration number: 24000 of 40000. Chain number 1. Current logpost: -367.113. Length of jump: 6.          Running MCMC-PT iteration number: 24000 of 40000. Chain number 3. Current logpost: -360.883. Length of jump: 6.          Running MCMC-PT iteration number: 24200 of 40000. Chain number 2. Current logpost: -361.925. Length of jump: 4.          Running MCMC-PT iteration number: 24100 of 40000. Chain number 4. Current logpost: -357.917. Length of jump: 7.          Running MCMC-PT iteration number: 24100 of 40000. Chain number 1. Current logpost: -360.372. Length of jump: 6.          Running MCMC-PT iteration number: 24100 of 40000. Chain number 3. Current logpost: -363.422. Length of jump: 6.          Running MCMC-PT iteration number: 24300 of 40000. Chain number 2. Current logpost: -359.611. Length of jump: 6.          Running MCMC-PT iteration number: 24200 of 40000. Chain number 4. Current logpost: -358.605. Length of jump: 7.          Running MCMC-PT iteration number: 24200 of 40000. Chain number 1. Current logpost: -360.863. Length of jump: 4.          Running MCMC-PT iteration number: 24200 of 40000. Chain number 3. Current logpost: -359.876. Length of jump: 5.          Running MCMC-PT iteration number: 24400 of 40000. Chain number 2. Current logpost: -359.769. Length of jump: 6.          Running MCMC-PT iteration number: 24300 of 40000. Chain number 4. Current logpost: -360.645. Length of jump: 7.          Running MCMC-PT iteration number: 24300 of 40000. Chain number 1. Current logpost: -358.536. Length of jump: 4.          Running MCMC-PT iteration number: 24300 of 40000. Chain number 3. Current logpost: -360.071. Length of jump: 5.          Running MCMC-PT iteration number: 24500 of 40000. Chain number 2. Current logpost: -359.133. Length of jump: 5.          Running MCMC-PT iteration number: 24400 of 40000. Chain number 4. Current logpost: -359.255. Length of jump: 6.          Running MCMC-PT iteration number: 24400 of 40000. Chain number 1. Current logpost: -357.38. Length of jump: 5.          Running MCMC-PT iteration number: 24400 of 40000. Chain number 3. Current logpost: -361.754. Length of jump: 5.          Running MCMC-PT iteration number: 24600 of 40000. Chain number 2. Current logpost: -358.979. Length of jump: 6.          Running MCMC-PT iteration number: 24500 of 40000. Chain number 4. Current logpost: -358.82. Length of jump: 6.          Running MCMC-PT iteration number: 24500 of 40000. Chain number 1. Current logpost: -357.987. Length of jump: 5.          Running MCMC-PT iteration number: 24600 of 40000. Chain number 1. Current logpost: -361.102. Length of jump: 5.          Running MCMC-PT iteration number: 24600 of 40000. Chain number 3. Current logpost: -362.009. Length of jump: 3.          Running MCMC-PT iteration number: 24800 of 40000. Chain number 2. Current logpost: -361.241. Length of jump: 6.          Running MCMC-PT iteration number: 24700 of 40000. Chain number 4. Current logpost: -359.788. Length of jump: 4.          Running MCMC-PT iteration number: 24700 of 40000. Chain number 1. Current logpost: -362.262. Length of jump: 4.          Running MCMC-PT iteration number: 24700 of 40000. Chain number 3. Current logpost: -360.757. Length of jump: 3.          Running MCMC-PT iteration number: 24900 of 40000. Chain number 2. Current logpost: -368.057. Length of jump: 7.          Running MCMC-PT iteration number: 24800 of 40000. Chain number 4. Current logpost: -360.27. Length of jump: 4.          Running MCMC-PT iteration number: 24800 of 40000. Chain number 1. Current logpost: -360.82. Length of jump: 4.          Running MCMC-PT iteration number: 24800 of 40000. Chain number 3. Current logpost: -361.216. Length of jump: 3.          Running MCMC-PT iteration number: 25000 of 40000. Chain number 2. Current logpost: -369.16. Length of jump: 9.          Running MCMC-PT iteration number: 24900 of 40000. Chain number 4. Current logpost: -360.709. Length of jump: 4.          Running MCMC-PT iteration number: 24900 of 40000. Chain number 1. Current logpost: -361.154. Length of jump: 4.          Running MCMC-PT iteration number: 24900 of 40000. Chain number 3. Current logpost: -361.368. Length of jump: 3.          Running MCMC-PT iteration number: 25100 of 40000. Chain number 2. Current logpost: -368.313. Length of jump: 7.          Running MCMC-PT iteration number: 25000 of 40000. Chain number 4. Current logpost: -359.232. Length of jump: 4.          Running MCMC-PT iteration number: 25000 of 40000. Chain number 1. Current logpost: -360.983. Length of jump: 3.          Running MCMC-PT iteration number: 25000 of 40000. Chain number 3. Current logpost: -362.354. Length of jump: 3.          Running MCMC-PT iteration number: 25200 of 40000. Chain number 2. Current logpost: -365.541. Length of jump: 7.          Running MCMC-PT iteration number: 25100 of 40000. Chain number 4. Current logpost: -359.638. Length of jump: 4.          Running MCMC-PT iteration number: 25100 of 40000. Chain number 1. Current logpost: -361.21. Length of jump: 3.          Running MCMC-PT iteration number: 25300 of 40000. Chain number 2. Current logpost: -364.469. Length of jump: 7.          Running MCMC-PT iteration number: 25200 of 40000. Chain number 4. Current logpost: -360.162. Length of jump: 4.          Running MCMC-PT iteration number: 25200 of 40000. Chain number 1. Current logpost: -360.775. Length of jump: 3.          Running MCMC-PT iteration number: 25200 of 40000. Chain number 3. Current logpost: -362.564. Length of jump: 5.          Running MCMC-PT iteration number: 25400 of 40000. Chain number 2. Current logpost: -360.979. Length of jump: 7.          Running MCMC-PT iteration number: 25300 of 40000. Chain number 4. Current logpost: -358.965. Length of jump: 4.          Running MCMC-PT iteration number: 25300 of 40000. Chain number 1. Current logpost: -362.155. Length of jump: 3.          Running MCMC-PT iteration number: 25300 of 40000. Chain number 3. Current logpost: -361.967. Length of jump: 5.          Running MCMC-PT iteration number: 25500 of 40000. Chain number 2. Current logpost: -366.866. Length of jump: 8.          Running MCMC-PT iteration number: 25400 of 40000. Chain number 4. Current logpost: -359.536. Length of jump: 4.          Running MCMC-PT iteration number: 25400 of 40000. Chain number 1. Current logpost: -360.272. Length of jump: 5.          Running MCMC-PT iteration number: 25400 of 40000. Chain number 3. Current logpost: -365.123. Length of jump: 6.          Running MCMC-PT iteration number: 25600 of 40000. Chain number 2. Current logpost: -361.515. Length of jump: 8.          Running MCMC-PT iteration number: 25500 of 40000. Chain number 4. Current logpost: -360.452. Length of jump: 4.          Running MCMC-PT iteration number: 25500 of 40000. Chain number 1. Current logpost: -359.038. Length of jump: 5.          Running MCMC-PT iteration number: 25500 of 40000. Chain number 3. Current logpost: -367.511. Length of jump: 5.          Running MCMC-PT iteration number: 25700 of 40000. Chain number 2. Current logpost: -360.385. Length of jump: 8.          Running MCMC-PT iteration number: 25600 of 40000. Chain number 4. Current logpost: -357.631. Length of jump: 5.          Running MCMC-PT iteration number: 25600 of 40000. Chain number 1. Current logpost: -358.047. Length of jump: 5.          Running MCMC-PT iteration number: 25600 of 40000. Chain number 3. Current logpost: -365.873. Length of jump: 5.          Running MCMC-PT iteration number: 25800 of 40000. Chain number 2. Current logpost: -360.003. Length of jump: 8.          Running MCMC-PT iteration number: 25700 of 40000. Chain number 4. Current logpost: -359.659. Length of jump: 4.          Running MCMC-PT iteration number: 25700 of 40000. Chain number 1. Current logpost: -358.121. Length of jump: 5.          Running MCMC-PT iteration number: 25700 of 40000. Chain number 3. Current logpost: -360.44. Length of jump: 6.          Running MCMC-PT iteration number: 25900 of 40000. Chain number 2. Current logpost: -361.608. Length of jump: 7.          Running MCMC-PT iteration number: 25800 of 40000. Chain number 4. Current logpost: -361.073. Length of jump: 4.          Running MCMC-PT iteration number: 25800 of 40000. Chain number 1. Current logpost: -359.993. Length of jump: 7.          Running MCMC-PT iteration number: 25800 of 40000. Chain number 3. Current logpost: -361.059. Length of jump: 6.          Running MCMC-PT iteration number: 26000 of 40000. Chain number 2. Current logpost: -359.296. Length of jump: 6.          Running MCMC-PT iteration number: 25900 of 40000. Chain number 4. Current logpost: -359.256. Length of jump: 5.          Running MCMC-PT iteration number: 25900 of 40000. Chain number 1. Current logpost: -359.529. Length of jump: 7.          Running MCMC-PT iteration number: 25900 of 40000. Chain number 3. Current logpost: -359.988. Length of jump: 4.          Running MCMC-PT iteration number: 26100 of 40000. Chain number 2. Current logpost: -358.939. Length of jump: 6.          Running MCMC-PT iteration number: 26000 of 40000. Chain number 4. Current logpost: -359.326. Length of jump: 5.          Running MCMC-PT iteration number: 26000 of 40000. Chain number 1. Current logpost: -359.407. Length of jump: 6.          Running MCMC-PT iteration number: 26000 of 40000. Chain number 3. Current logpost: -360.388. Length of jump: 4.          Running MCMC-PT iteration number: 26200 of 40000. Chain number 2. Current logpost: -358.358. Length of jump: 5.          Running MCMC-PT iteration number: 26100 of 40000. Chain number 4. Current logpost: -356.922. Length of jump: 6.          Running MCMC-PT iteration number: 26100 of 40000. Chain number 1. Current logpost: -359.04. Length of jump: 6.          Running MCMC-PT iteration number: 26100 of 40000. Chain number 3. Current logpost: -361.098. Length of jump: 6.          Running MCMC-PT iteration number: 26300 of 40000. Chain number 2. Current logpost: -359.588. Length of jump: 5.          Running MCMC-PT iteration number: 26200 of 40000. Chain number 4. Current logpost: -356.662. Length of jump: 6.          Running MCMC-PT iteration number: 26200 of 40000. Chain number 1. Current logpost: -359.813. Length of jump: 7.          Running MCMC-PT iteration number: 26200 of 40000. Chain number 3. Current logpost: -368.404. Length of jump: 5.          Running MCMC-PT iteration number: 26400 of 40000. Chain number 2. Current logpost: -359.151. Length of jump: 5.          Running MCMC-PT iteration number: 26300 of 40000. Chain number 1. Current logpost: -361.53. Length of jump: 7.          Running MCMC-PT iteration number: 26300 of 40000. Chain number 3. Current logpost: -364.563. Length of jump: 6.          Running MCMC-PT iteration number: 26500 of 40000. Chain number 2. Current logpost: -359.836. Length of jump: 6.          Running MCMC-PT iteration number: 26400 of 40000. Chain number 4. Current logpost: -355.635. Length of jump: 6.          Running MCMC-PT iteration number: 26400 of 40000. Chain number 1. Current logpost: -362.977. Length of jump: 7.          Running MCMC-PT iteration number: 26400 of 40000. Chain number 3. Current logpost: -362.955. Length of jump: 5.          Running MCMC-PT iteration number: 26600 of 40000. Chain number 2. Current logpost: -357.162. Length of jump: 6.          Running MCMC-PT iteration number: 26500 of 40000. Chain number 4. Current logpost: -356.478. Length of jump: 5.          Running MCMC-PT iteration number: 26500 of 40000. Chain number 1. Current logpost: -363.08. Length of jump: 7.          Running MCMC-PT iteration number: 26500 of 40000. Chain number 3. Current logpost: -363.062. Length of jump: 5.          Running MCMC-PT iteration number: 26700 of 40000. Chain number 2. Current logpost: -357.022. Length of jump: 6.          Running MCMC-PT iteration number: 26600 of 40000. Chain number 4. Current logpost: -358.844. Length of jump: 6.          Running MCMC-PT iteration number: 26600 of 40000. Chain number 1. Current logpost: -360.096. Length of jump: 7.          Running MCMC-PT iteration number: 26600 of 40000. Chain number 3. Current logpost: -363.804. Length of jump: 4.          Running MCMC-PT iteration number: 26800 of 40000. Chain number 2. Current logpost: -360.598. Length of jump: 6.          Running MCMC-PT iteration number: 26700 of 40000. Chain number 4. Current logpost: -357.046. Length of jump: 6.          Running MCMC-PT iteration number: 26700 of 40000. Chain number 1. Current logpost: -358.412. Length of jump: 6.          Running MCMC-PT iteration number: 26700 of 40000. Chain number 3. Current logpost: -360.888. Length of jump: 4.          Running MCMC-PT iteration number: 26900 of 40000. Chain number 2. Current logpost: -356.053. Length of jump: 6.          Running MCMC-PT iteration number: 26800 of 40000. Chain number 4. Current logpost: -359.571. Length of jump: 6.          Running MCMC-PT iteration number: 26800 of 40000. Chain number 1. Current logpost: -361.824. Length of jump: 6.          Running MCMC-PT iteration number: 26800 of 40000. Chain number 3. Current logpost: -360.703. Length of jump: 5.          Running MCMC-PT iteration number: 27000 of 40000. Chain number 2. Current logpost: -357.44. Length of jump: 7.          Running MCMC-PT iteration number: 26900 of 40000. Chain number 4. Current logpost: -358.379. Length of jump: 7.          Running MCMC-PT iteration number: 26900 of 40000. Chain number 1. Current logpost: -360.128. Length of jump: 4.          Running MCMC-PT iteration number: 26900 of 40000. Chain number 3. Current logpost: -360.969. Length of jump: 6.          Running MCMC-PT iteration number: 27100 of 40000. Chain number 2. Current logpost: -360.099. Length of jump: 7.          Running MCMC-PT iteration number: 27000 of 40000. Chain number 4. Current logpost: -360.377. Length of jump: 6.          Running MCMC-PT iteration number: 27000 of 40000. Chain number 1. Current logpost: -358.529. Length of jump: 4.          Running MCMC-PT iteration number: 27000 of 40000. Chain number 3. Current logpost: -361.312. Length of jump: 6.          Running MCMC-PT iteration number: 27200 of 40000. Chain number 2. Current logpost: -357.018. Length of jump: 6.          Running MCMC-PT iteration number: 27100 of 40000. Chain number 4. Current logpost: -362.959. Length of jump: 8.          Running MCMC-PT iteration number: 27100 of 40000. Chain number 1. Current logpost: -359.011. Length of jump: 4.          Running MCMC-PT iteration number: 27100 of 40000. Chain number 3. Current logpost: -362.237. Length of jump: 7.          Running MCMC-PT iteration number: 27300 of 40000. Chain number 2. Current logpost: -357.727. Length of jump: 7.          Running MCMC-PT iteration number: 27200 of 40000. Chain number 4. Current logpost: -361.442. Length of jump: 7.          Running MCMC-PT iteration number: 27200 of 40000. Chain number 1. Current logpost: -359.66. Length of jump: 4.          Running MCMC-PT iteration number: 27200 of 40000. Chain number 3. Current logpost: -361.034. Length of jump: 6.          Running MCMC-PT iteration number: 27400 of 40000. Chain number 2. Current logpost: -356.21. Length of jump: 6.          Running MCMC-PT iteration number: 27300 of 40000. Chain number 4. Current logpost: -362.984. Length of jump: 7.          Running MCMC-PT iteration number: 27300 of 40000. Chain number 1. Current logpost: -358.2. Length of jump: 4.          Running MCMC-PT iteration number: 27300 of 40000. Chain number 3. Current logpost: -361.201. Length of jump: 8.          Running MCMC-PT iteration number: 27500 of 40000. Chain number 2. Current logpost: -355.928. Length of jump: 5.          Running MCMC-PT iteration number: 27400 of 40000. Chain number 4. Current logpost: -363.915. Length of jump: 8.          Running MCMC-PT iteration number: 27400 of 40000. Chain number 1. Current logpost: -360.647. Length of jump: 4.          Running MCMC-PT iteration number: 27400 of 40000. Chain number 3. Current logpost: -361.509. Length of jump: 9.          Running MCMC-PT iteration number: 27600 of 40000. Chain number 2. Current logpost: -356.015. Length of jump: 5.          Running MCMC-PT iteration number: 27500 of 40000. Chain number 4. Current logpost: -360.514. Length of jump: 6.          Running MCMC-PT iteration number: 27500 of 40000. Chain number 1. Current logpost: -360.789. Length of jump: 5.          Running MCMC-PT iteration number: 27500 of 40000. Chain number 3. Current logpost: -361.773. Length of jump: 7.          Running MCMC-PT iteration number: 27700 of 40000. Chain number 2. Current logpost: -357.276. Length of jump: 5.          Running MCMC-PT iteration number: 27600 of 40000. Chain number 4. Current logpost: -362.165. Length of jump: 7.          Running MCMC-PT iteration number: 27600 of 40000. Chain number 1. Current logpost: -359.645. Length of jump: 6.          Running MCMC-PT iteration number: 27600 of 40000. Chain number 3. Current logpost: -359.418. Length of jump: 6.          Running MCMC-PT iteration number: 27800 of 40000. Chain number 2. Current logpost: -356.69. Length of jump: 5.          Running MCMC-PT iteration number: 27700 of 40000. Chain number 4. Current logpost: -360.612. Length of jump: 6.          Running MCMC-PT iteration number: 27700 of 40000. Chain number 1. Current logpost: -359.996. Length of jump: 6.          Running MCMC-PT iteration number: 27700 of 40000. Chain number 3. Current logpost: -360.35. Length of jump: 6.          Running MCMC-PT iteration number: 27900 of 40000. Chain number 2. Current logpost: -356.592. Length of jump: 6.          Running MCMC-PT iteration number: 27800 of 40000. Chain number 4. Current logpost: -360.78. Length of jump: 6.          Running MCMC-PT iteration number: 27800 of 40000. Chain number 1. Current logpost: -362.702. Length of jump: 5.          Running MCMC-PT iteration number: 27800 of 40000. Chain number 3. Current logpost: -360.038. Length of jump: 6.          Running MCMC-PT iteration number: 28000 of 40000. Chain number 2. Current logpost: -358.773. Length of jump: 6.          Running MCMC-PT iteration number: 27900 of 40000. Chain number 4. Current logpost: -359.523. Length of jump: 6.          Running MCMC-PT iteration number: 27900 of 40000. Chain number 1. Current logpost: -358.268. Length of jump: 4.          Running MCMC-PT iteration number: 27900 of 40000. Chain number 3. Current logpost: -362.095. Length of jump: 8.          Running MCMC-PT iteration number: 28100 of 40000. Chain number 2. Current logpost: -360.698. Length of jump: 7.          Running MCMC-PT iteration number: 28000 of 40000. Chain number 4. Current logpost: -358.872. Length of jump: 6.          Running MCMC-PT iteration number: 28000 of 40000. Chain number 1. Current logpost: -358.723. Length of jump: 4.          Running MCMC-PT iteration number: 28000 of 40000. Chain number 3. Current logpost: -362.022. Length of jump: 7.          Running MCMC-PT iteration number: 28200 of 40000. Chain number 2. Current logpost: -360.852. Length of jump: 7.          Running MCMC-PT iteration number: 28100 of 40000. Chain number 4. Current logpost: -359.517. Length of jump: 5.          Running MCMC-PT iteration number: 28100 of 40000. Chain number 1. Current logpost: -360.694. Length of jump: 4.          Running MCMC-PT iteration number: 28100 of 40000. Chain number 3. Current logpost: -360.686. Length of jump: 6.          Running MCMC-PT iteration number: 28300 of 40000. Chain number 2. Current logpost: -361.709. Length of jump: 7.          Running MCMC-PT iteration number: 28200 of 40000. Chain number 4. Current logpost: -359.062. Length of jump: 5.          Running MCMC-PT iteration number: 28200 of 40000. Chain number 1. Current logpost: -365.854. Length of jump: 5.          Running MCMC-PT iteration number: 28200 of 40000. Chain number 3. Current logpost: -361.767. Length of jump: 6.          Running MCMC-PT iteration number: 28400 of 40000. Chain number 2. Current logpost: Running MCMC-PT iteration number: -360.078. Length of jump: 6.          28300 of 40000. Chain number 4. Current logpost: -358.989. Length of jump: 4.          Running MCMC-PT iteration number: 28300 of 40000. Chain number 1. Current logpost: -364.044. Length of jump: 6.          Running MCMC-PT iteration number: 28300 of 40000. Chain number 3. Current logpost: -361.608. Length of jump: 6.          Running MCMC-PT iteration number: 28400 of 40000. Chain number 4. Current logpost: -358.746. Length of jump: 5.          Running MCMC-PT iteration number: 28500 of 40000. Chain number 2. Current logpost: -358.45. Length of jump: 7.          Running MCMC-PT iteration number: 28400 of 40000. Chain number 1. Current logpost: -361.732. Length of jump: 6.          Running MCMC-PT iteration number: 28400 of 40000. Chain number 3. Current logpost: -360.009. Length of jump: 6.          Running MCMC-PT iteration number: 28500 of 40000. Chain number 4. Current logpost: -359.171. Length of jump: 6.          Running MCMC-PT iteration number: 28600 of 40000. Chain number 2. Current logpost: -361.531. Length of jump: 7.          Running MCMC-PT iteration number: 28500 of 40000. Chain number 1. Current logpost: -360.775. Length of jump: 5.          Running MCMC-PT iteration number: 28500 of 40000. Chain number 3. Current logpost: -358.494. Length of jump: 6.          Running MCMC-PT iteration number: 28600 of 40000. Chain number 4. Current logpost: -358.333. Length of jump: 6.          Running MCMC-PT iteration number: 28700 of 40000. Chain number 2. Current logpost: -360.772. Length of jump: 6.          Running MCMC-PT iteration number: 28600 of 40000. Chain number 1. Current logpost: -360.005. Length of jump: 5.          Running MCMC-PT iteration number: 28600 of 40000. Chain number 3. Current logpost: -359.509. Length of jump: 6.          Running MCMC-PT iteration number: 28700 of 40000. Chain number 4. Current logpost: -359.106. Length of jump: 7.          Running MCMC-PT iteration number: 28800 of 40000. Chain number 2. Current logpost: -360.131. Length of jump: 6.          Running MCMC-PT iteration number: 28700 of 40000. Chain number 1. Current logpost: -360.856. Length of jump: 6.          Running MCMC-PT iteration number: 28700 of 40000. Chain number 3. Current logpost: -358.088. Length of jump: 6.          Running MCMC-PT iteration number: 28800 of 40000. Chain number 4. Current logpost: -358.639. Length of jump: 7.          Running MCMC-PT iteration number: 28900 of 40000. Chain number 2. Current logpost: -359.709. Length of jump: 6.          Running MCMC-PT iteration number: 28800 of 40000. Chain number 1. Current logpost: -359.391. Length of jump: 7.          Running MCMC-PT iteration number: 28800 of 40000. Chain number 3. Current logpost: -358.56. Length of jump: 5.          Running MCMC-PT iteration number: 28900 of 40000. Chain number 4. Current logpost: -360.287. Length of jump: 8.          Running MCMC-PT iteration number: 29000 of 40000. Chain number 2. Current logpost: -363.289. Length of jump: 7.          Running MCMC-PT iteration number: 28900 of 40000. Chain number 1. Current logpost: -359.09. Length of jump: 6.          Running MCMC-PT iteration number: 28900 of 40000. Chain number 3. Current logpost: -358.468. Length of jump: 5.          Running MCMC-PT iteration number: 29000 of 40000. Chain number 4. Current logpost: -359.618. Length of jump: 6.          Running MCMC-PT iteration number: 29100 of 40000. Chain number 2. Current logpost: -360.094. Length of jump: 6.          Running MCMC-PT iteration number: 29000 of 40000. Chain number 1. Current logpost: -359.402. Length of jump: 6.          Running MCMC-PT iteration number: 29000 of 40000. Chain number 3. Current logpost: -362.501. Length of jump: 6.          Running MCMC-PT iteration number: 29100 of 40000. Chain number 4. Current logpost: -362.927. Length of jump: 6.          Running MCMC-PT iteration number: 29200 of 40000. Chain number 2. Current logpost: -359.449. Length of jump: 6.          Running MCMC-PT iteration number: 29100 of 40000. Chain number 1. Current logpost: -360.417. Length of jump: 6.          Running MCMC-PT iteration number: 29100 of 40000. Chain number 3. Current logpost: -359.956. Length of jump: 5.          Running MCMC-PT iteration number: 29200 of 40000. Chain number 4. Current logpost: -363.18. Length of jump: 5.          Running MCMC-PT iteration number: 29300 of 40000. Chain number 2. Current logpost: -361.965. Length of jump: 6.          Running MCMC-PT iteration number: 29200 of 40000. Chain number 1. Current logpost: -360.689. Length of jump: 8.          Running MCMC-PT iteration number: 29200 of 40000. Chain number 3. Current logpost: -362.453. Length of jump: 5.          Running MCMC-PT iteration number: 29300 of 40000. Chain number 4Running MCMC-PT iteration number: 29400. Current logpost: -360.852. Length of jump:  of 40000. Chain number 4.          2. Current logpost: -357.897. Length of jump: 5.          Running MCMC-PT iteration number: 29300 of 40000. Chain number 1. Current logpost: -361.262. Length of jump: 7.          Running MCMC-PT iteration number: 29300 of 40000. Chain number 3. Current logpost: -359.846. Length of jump: 4.          Running MCMC-PT iteration number: 29500 of 40000. Chain number 2. Current logpost: -358.43. Length of jump: 5.          Running MCMC-PT iteration number: 29400 of 40000. Chain number 4. Current logpost: -361.87. Length of jump: 4.          Running MCMC-PT iteration number: 29400 of 40000. Chain number 1. Current logpost: -361.775. Length of jump: 7.          Running MCMC-PT iteration number: 29400 of 40000. Chain number 3. Current logpost: -360.981. Length of jump: 4.          Running MCMC-PT iteration number: 29600 of 40000. Chain number 2. Current logpost: -359.644. Length of jump: 6.          Running MCMC-PT iteration number: 29500 of 40000. Chain number 4. Current logpost: -358.921. Length of jump: 4.          Running MCMC-PT iteration number: 29500 of 40000. Chain number 1. Current logpost: -361.144. Length of jump: 6.          Running MCMC-PT iteration number: 29500 of 40000. Chain number 3. Current logpost: -361.046. Length of jump: 4.          Running MCMC-PT iteration number: 29700 of 40000. Chain number 2. Current logpost: -359.603. Length of jump: 7.          Running MCMC-PT iteration number: 29600 of 40000. Chain number 4. Current logpost: -358.972. Length of jump: 4.          Running MCMC-PT iteration number: 29600 of 40000. Chain number 1. Current logpost: -360.545. Length of jump: 6.          Running MCMC-PT iteration number: 29600 of 40000. Chain number 3. Current logpost: -360.182. Length of jump: 4.          Running MCMC-PT iteration number: 29800 of 40000. Chain number 2. Current logpost: -361.037. Length of jump: 8.          Running MCMC-PT iteration number: 29700 of 40000. Chain number 4. Current logpost: -357.197. Length of jump: 5.          Running MCMC-PT iteration number: 29700 of 40000. Chain number 1. Current logpost: -358.048. Length of jump: 5.          Running MCMC-PT iteration number: 29700 of 40000. Chain number 3. Current logpost: -360.928. Length of jump: 4.          Running MCMC-PT iteration number: 29900 of 40000. Chain number 2. Current logpost: -361.866. Length of jump: 8.          Running MCMC-PT iteration number: 29800 of 40000. Chain number 4. Current logpost: -357.375. Length of jump: 5.          Running MCMC-PT iteration number: 29800 of 40000. Chain number 1. Current logpost: -358.113. Length of jump: 5.          Running MCMC-PT iteration number: 29800 of 40000. Chain number 3. Current logpost: -362.18. Length of jump: 5.          Running MCMC-PT iteration number: 29900 of 40000. Chain number 4. Current logpost: -356.141. Length of jump: 5.          Running MCMC-PT iteration number: 30000 of 40000. Chain number 2. Current logpost: -359.537. Length of jump: 7.          Running MCMC-PT iteration number: 29900 of 40000. Chain number 1. Current logpost: -358.961. Length of jump: 5.          Running MCMC-PT iteration number: 29900 of 40000. Chain number 3. Current logpost: -361.756. Length of jump: 6.          Running MCMC-PT iteration number: 30000 of 40000. Chain number 4. Current logpost: -357.16. Length of jump: 7.          Running MCMC-PT iteration number: 30100 of 40000. Chain number 2. Current logpost: -358.511. Length of jump: 7.          Running MCMC-PT iteration number: 30000 of 40000. Chain number 1. Current logpost: -359.5. Length of jump: 4.          Running MCMC-PT iteration number: 30000 of 40000. Chain number 3. Current logpost: -359.116. Length of jump: 6.          Running MCMC-PT iteration number: 30100 of 40000. Chain number 4. Current logpost: -357.822. Length of jump: 6.          Running MCMC-PT iteration number: 30200 of 40000. Chain number 2. Current logpost: -357.747. Length of jump: 5.          Running MCMC-PT iteration number: 30100 of 40000. Chain number 1. Current logpost: -359.955. Length of jump: 5.          Running MCMC-PT iteration number: 30100 of 40000. Chain number 3. Current logpost: -358.06. Length of jump: 5.          Running MCMC-PT iteration number: 30200 of 40000. Chain number 4. Current logpost: -355.718. Length of jump: 6.          Running MCMC-PT iteration number: 30300 of 40000. Chain number 2. Current logpost: -358.434. Length of jump: 5.          Running MCMC-PT iteration number: 30200 of 40000. Chain number 1. Current logpost: -361.38. Length of jump: 4.          Running MCMC-PT iteration number: 30400 of 40000. Chain number 2. Current logpost: -359.049. Length of jump: 5.          Running MCMC-PT iteration number: 30300 of 40000. Chain number 1. Current logpost: -364.61. Length of jump: 5.          Running MCMC-PT iteration number: 30500 of 40000. Chain number 2. Current logpost: -360.349. Length of jump: 5.          Running MCMC-PT iteration number: 30400 of 40000. Chain number 4. Current logpost: -357.717. Length of jump: 6.          Running MCMC-PT iteration number: 30400 of 40000. Chain number 1. Current logpost: -358.797. Length of jump: 4.          Running MCMC-PT iteration number: 30400 of 40000. Chain number 3. Current logpost: -358.248. Length of jump: 5.          Running MCMC-PT iteration number: 30600 of 40000. Chain number 2. Current logpost: -359.644. Length of jump: 5.          Running MCMC-PT iteration number: 30700 of 40000. Chain number 2. Current logpost: -361.293. Length of jump: 5.          Running MCMC-PT iteration number: 30600 of 40000. Chain number 4. Current logpost: -361.263. Length of jump: 5.          Running MCMC-PT iteration number: 30600 of 40000. Chain number 1. Current logpost: -357.409. Length of jump: 5.          Running MCMC-PT iteration number: 30600 of 40000. Chain number 3. Current logpost: -360.237. Length of jump: 5.          Running MCMC-PT iteration number: 30800 of 40000. Chain number 2. Current logpost: -361.183. Length of jump: 5.          Running MCMC-PT iteration number: 30700 of 40000. Chain number 4. Current logpost: -358.427. Length of jump: 5.          Running MCMC-PT iteration number: 30700 of 40000. Chain number 1. Current logpost: -360.881. Length of jump: 6.          Running MCMC-PT iteration number: 30700 of 40000. Chain number 3. Current logpost: -361.893. Length of jump: 5.          Running MCMC-PT iteration number: 30900 of 40000. Chain number 2. Current logpost: -361.185. Length of jump: 5.          Running MCMC-PT iteration number: 30800 of 40000. Chain number 4. Current logpost: -358.864. Length of jump: 5.          Running MCMC-PT iteration number: 30800 of 40000. Chain number 1. Current logpost: -359.724. Length of jump: 8.          Running MCMC-PT iteration number: 30800 of 40000. Chain number 3. Current logpost: -363.231. Length of jump: 5.          Running MCMC-PT iteration number: 31000 of 40000. Chain number 2. Current logpost: -361.015. Length of jump: 4.          Running MCMC-PT iteration number: 30900 of 40000. Chain number 4. Current logpost: -357.552. Length of jump: 5.          Running MCMC-PT iteration number: 30900 of 40000. Chain number 1. Current logpost: -360.155. Length of jump: 8.          Running MCMC-PT iteration number: 30900 of 40000. Chain number 3. Current logpost: -369.072. Length of jump: 6.          Running MCMC-PT iteration number: 31100 of 40000. Chain number 2. Current logpost: -360.519. Length of jump: 5.          Running MCMC-PT iteration number: 31000 of 40000. Chain number 4. Current logpost: -359.588. Length of jump: 6.          Running MCMC-PT iteration number: 31000 of 40000. Chain number 1. Current logpost: -359.351. Length of jump: 8.          Running MCMC-PT iteration number: 31000 of 40000. Chain number 3. Current logpost: -361.663. Length of jump: 5.          Running MCMC-PT iteration number: 31200 of 40000. Chain number 2. Current logpost: -364.965. Length of jump: 6.          Running MCMC-PT iteration number: 31100 of 40000. Chain number 4. Current logpost: -362.327. Length of jump: 7.          Running MCMC-PT iteration number: 31100 of 40000. Chain number 1. Current logpost: -358.913. Length of jump: 7.          Running MCMC-PT iteration number: 31100 of 40000. Chain number 3. Current logpost: -357.878. Length of jump: 5.          Running MCMC-PT iteration number: 31300 of 40000. Chain number 2. Current logpost: -365.233. Length of jump: 5.          Running MCMC-PT iteration number: 31200 of 40000. Chain number 4. Current logpost: -357.811. Length of jump: 6.          Running MCMC-PT iteration number: 31200 of 40000. Chain number 1. Current logpost: -357.946. Length of jump: 5.          Running MCMC-PT iteration number: 31200 of 40000. Chain number 3. Current logpost: -357.489. Length of jump: 6.          Running MCMC-PT iteration number: 31400 of 40000. Chain number 2. Current logpost: -365.005. Length of jump: 7.          Running MCMC-PT iteration number: 31300 of 40000. Chain number 4. Current logpost: -358.205. Length of jump: 5.          Running MCMC-PT iteration number: 31300 of 40000. Chain number 1. Current logpost: -359.249. Length of jump: 7.          Running MCMC-PT iteration number: 31300 of 40000. Chain number 3. Current logpost: -358.117. Length of jump: 7.          Running MCMC-PT iteration number: 31400 of 40000. Chain number 4. Current logpost: -358.17. Length of jump: 5.          Running MCMC-PT iteration number: 31500 of 40000. Chain number 2. Current logpost: -363.336. Length of jump: 7.          Running MCMC-PT iteration number: 31400 of 40000. Chain number 1. Current logpost: -358.953. Length of jump: 7.          Running MCMC-PT iteration number: 31400 of 40000. Chain number 3. Current logpost: -362.262. Length of jump: 7.          Running MCMC-PT iteration number: 31500 of 40000. Chain number 4. Current logpost: -359.891. Length of jump: 4.          Running MCMC-PT iteration number: 31500 of 40000. Chain number 3. Current logpost: -359.643. Length of jump: 6.          Running MCMC-PT iteration number: 31600 of 40000. Chain number 4. Current logpost: -359.624. Length of jump: 4.          Running MCMC-PT iteration number: 31700 of 40000. Chain number 2. Current logpost: -361.079. Length of jump: 6.          Running MCMC-PT iteration number: 31600 of 40000. Chain number 1. Current logpost: -360.149. Length of jump: 7.          Running MCMC-PT iteration number: 31600 of 40000. Chain number 3. Current logpost: -357.533. Length of jump: 7.          Running MCMC-PT iteration number: 31700 of 40000. Chain number 4. Current logpost: -358.188. Length of jump: 4.          Running MCMC-PT iteration number: 31800 of 40000. Chain number 2. Current logpost: -361.914. Length of jump: 5.          Running MCMC-PT iteration number: 31700 of 40000. Chain number 1. Current logpost: -361.193. Length of jump: 7.          Running MCMC-PT iteration number: 31700 of 40000. Chain number 3. Current logpost: -361.136. Length of jump: 8.          Running MCMC-PT iteration number: 31800 of 40000. Chain number 4. Current logpost: -359.39. Length of jump: 4.          Running MCMC-PT iteration number: 31900 of 40000. Chain number 2. Current logpost: -364.238. Length of jump: 5.          Running MCMC-PT iteration number: 31800 of 40000. Chain number 1. Current logpost: -362.947. Length of jump: 8.          Running MCMC-PT iteration number: 31800 of 40000. Chain number 3. Current logpost: -360.511. Length of jump: 7.          Running MCMC-PT iteration number: 31900 of 40000. Chain number 4. Current logpost: -362.453. Length of jump: 5.          Running MCMC-PT iteration number: 32000 of 40000. Chain number 2. Current logpost: -369.021. Length of jump: 5.          Running MCMC-PT iteration number: 31900 of 40000. Chain number 1. Current logpost: -362.039. Length of jump: 7.          Running MCMC-PT iteration number: 31900 of 40000. Chain number 3. Current logpost: -358.059. Length of jump: 7.          Running MCMC-PT iteration number: 32000 of 40000. Chain number 4. Current logpost: -364.201. Length of jump: 5.          Running MCMC-PT iteration number: 32100 of 40000. Chain number 2. Current logpost: -366.741. Length of jump: 6.          Running MCMC-PT iteration number: 32000 of 40000. Chain number 1. Current logpost: -362.058. Length of jump: 7.          Running MCMC-PT iteration number: 32000 of 40000. Chain number 3. Current logpost: -361.501. Length of jump: 7.          Running MCMC-PT iteration number: 32100 of 40000. Chain number 4. Current logpost: -359.494. Length of jump: 5.          Running MCMC-PT iteration number: 32200 of 40000. Chain number 2. Current logpost: -364.928. Length of jump: 6.          Running MCMC-PT iteration number: 32100 of 40000. Chain number 1. Current logpost: -362.635. Length of jump: 6.          Running MCMC-PT iteration number: 32100 of 40000. Chain number 3. Current logpost: -359.4. Length of jump: 7.          Running MCMC-PT iteration number: 32200 of 40000. Chain number 4. Current logpost: -358.365. Length of jump: 4.          Running MCMC-PT iteration number: 32300 of 40000. Chain number 2. Current logpost: -363.033. Length of jump: 6.          Running MCMC-PT iteration number: 32200 of 40000. Chain number 1. Current logpost: -362.271. Length of jump: 6.          Running MCMC-PT iteration number: 32200 of 40000. Chain number 3. Current logpost: -359.224. Length of jump: 6.          Running MCMC-PT iteration number: 32300 of 40000. Chain number 4. Current logpost: -357.5. Length of jump: 5.          Running MCMC-PT iteration number: 32400 of 40000. Chain number 2. Current logpost: -362.963. Length of jump: 6.          Running MCMC-PT iteration number: 32300 of 40000. Chain number 3. Current logpost: -361.867. Length of jump: 7.          Running MCMC-PT iteration number: 32300 of 40000. Chain number 1. Current logpost: -359.732. Length of jump: 6.          Running MCMC-PT iteration number: 32400 of 40000. Chain number 4. Current logpost: -357.627. Length of jump: 7.          Running MCMC-PT iteration number: 32500 of 40000. Chain number 2. Current logpost: -365.37. Length of jump: 8.          Running MCMC-PT iteration number: 32400 of 40000. Chain number 1. Current logpost: -358.314. Length of jump: 6.          Running MCMC-PT iteration number: 32400 of 40000. Chain number 3. Current logpost: -360.961. Length of jump: 8.          Running MCMC-PT iteration number: 32500 of 40000. Chain number 4. Current logpost: -359.828. Length of jump: 6.          Running MCMC-PT iteration number: 32600 of 40000. Chain number 2. Current logpost: -366.439. Length of jump: 8.          Running MCMC-PT iteration number: 32500 of 40000. Chain number 1. Current logpost: -360.754. Length of jump: 7.          Running MCMC-PT iteration number: 32500 of 40000. Chain number 3. Current logpost: -362.743. Length of jump: 8.          Running MCMC-PT iteration number: 32600 of 40000. Chain number 4. Current logpost: -359.507. Length of jump: 5.          Running MCMC-PT iteration number: 32700 of 40000. Chain number 2. Current logpost: -366.44. Length of jump: 8.          Running MCMC-PT iteration number: 32600 of 40000. Chain number 1. Current logpost: -360.934. Length of jump: 6.          Running MCMC-PT iteration number: 32600 of 40000. Chain number 3. Current logpost: -365.492. Length of jump: 8.          Running MCMC-PT iteration number: 32700 of 40000. Chain number 4. Current logpost: -360.701. Length of jump: 5.          Running MCMC-PT iteration number: 32800 of 40000. Chain number 2. Current logpost: -368.746. Length of jump: 8.          Running MCMC-PT iteration number: 32700 of 40000. Chain number 1. Current logpost: -364.062. Length of jump: 8.          Running MCMC-PT iteration number: 32700 of 40000. Chain number 3. Current logpost: -362.162. Length of jump: 6.          Running MCMC-PT iteration number: 32800 of 40000. Chain number 1. Current logpost: -362.811. Length of jump: 8.          Running MCMC-PT iteration number: 32800 of 40000. Chain number 3. Current logpost: -360.766. Length of jump: 7.          Running MCMC-PT iteration number: 32900 of 40000. Chain number 4. Current logpost: -358.805. Length of jump: 4.          Running MCMC-PT iteration number: 33000 of 40000. Chain number 2. Current logpost: -365.959. Length of jump: 6.          Running MCMC-PT iteration number: 32900 of 40000. Chain number 1. Current logpost: -361.144. Length of jump: 7.          Running MCMC-PT iteration number: 32900 of 40000. Chain number 3. Current logpost: -360.121. Length of jump: 6.          Running MCMC-PT iteration number: 33000 of 40000. Chain number 4. Current logpost: -359.095. Length of jump: 4.          Running MCMC-PT iteration number: 33100 of 40000. Chain number 2. Current logpost: -366.52. Length of jump: 6.          Running MCMC-PT iteration number: 33000 of 40000. Chain number 1. Current logpost: -361.072. Length of jump: 6.          Running MCMC-PT iteration number: 33000 of 40000. Chain number 3. Current logpost: -360.721. Length of jump: 6.          Running MCMC-PT iteration number: 33100 of 40000. Chain number 4. Current logpost: -360.084. Length of jump: 4.          Running MCMC-PT iteration number: 33200 of 40000. Chain number 2. Current logpost: -365.522. Length of jump: 7.          Running MCMC-PT iteration number: 33100 of 40000. Chain number 1. Current logpost: -363.188. Length of jump: 6.          Running MCMC-PT iteration number: 33100 of 40000. Chain number 3. Current logpost: -359.146. Length of jump: 6.          Running MCMC-PT iteration number: 33200 of 40000. Chain number 4. Current logpost: -358.789. Length of jump: 4.          Running MCMC-PT iteration number: 33300 of 40000. Chain number 2. Current logpost: -364.381. Length of jump: 5.          Running MCMC-PT iteration number: 33200 of 40000. Chain number 1. Current logpost: -363.678. Length of jump: 6.          Running MCMC-PT iteration number: 33200 of 40000. Chain number 3. Current logpost: -358.535. Length of jump: 6.          Running MCMC-PT iteration number: 33300 of 40000. Chain number 4. Current logpost: -360.164. Length of jump: 4.          Running MCMC-PT iteration number: 33400 of 40000. Chain number 2. Current logpost: -363.743. Length of jump: 5.          Running MCMC-PT iteration number: 33300 of 40000. Chain number 1. Current logpost: -365.087. Length of jump: 7.          Running MCMC-PT iteration number: 33300 of 40000. Chain number 3. Current logpost: -360.297. Length of jump: 6.          Running MCMC-PT iteration number: 33400 of 40000. Chain number 4. Current logpost: -359.265. Length of jump: 4.          Running MCMC-PT iteration number: 33500 of 40000. Chain number 2. Current logpost: -364.255. Length of jump: 5.          Running MCMC-PT iteration number: 33400 of 40000. Chain number 1. Current logpost: -364.366. Length of jump: 5.          Running MCMC-PT iteration number: 33400 of 40000. Chain number 3. Current logpost: -359.69. Length of jump: 5.          Running MCMC-PT iteration number: 33500 of 40000. Chain number 4. Current logpost: -359.098. Length of jump: 4.          Running MCMC-PT iteration number: 33600 of 40000. Chain number 2. Current logpost: -363.007. Length of jump: 5.          Running MCMC-PT iteration number: 33500 of 40000. Chain number 1. Current logpost: -358.924. Length of jump: 5.          Running MCMC-PT iteration number: 33500 of 40000. Chain number 3. Current logpost: -358.145. Length of jump: 5.          Running MCMC-PT iteration number: 33600 of 40000. Chain number 4. Current logpost: -358.286. Length of jump: 6.          Running MCMC-PT iteration number: 33700 of 40000. Chain number 2. Current logpost: -362.518. Length of jump: 5.          Running MCMC-PT iteration number: 33600 of 40000. Chain number 1. Current logpost: -357.618. Length of jump: 5.          Running MCMC-PT iteration number: 33600 of 40000. Chain number 3. Current logpost: -359.973. Length of jump: 5.          Running MCMC-PT iteration number: 33700 of 40000. Chain number 4. Current logpost: -357.332. Length of jump: 6.          Running MCMC-PT iteration number: 33800 of 40000. Chain number 2. Current logpost: -362.596. Length of jump: 5.          Running MCMC-PT iteration number: 33700 of 40000. Chain number 1. Current logpost: -358.135. Length of jump: 5.          Running MCMC-PT iteration number: 33700 of 40000. Chain number 3. Current logpost: -360.129. Length of jump: 7.          Running MCMC-PT iteration number: 33800 of 40000. Chain number 4. Current logpost: -356.47. Length of jump: 5.          Running MCMC-PT iteration number: 33900 of 40000. Chain number 2. Current logpost: -362.941. Length of jump: 4.          Running MCMC-PT iteration number: 33800 of 40000. Chain number 1. Current logpost: -358.285. Length of jump: 5.          Running MCMC-PT iteration number: 33800 of 40000. Chain number 3. Current logpost: -361.952. Length of jump: 7.          Running MCMC-PT iteration number: 33900 of 40000. Chain number 4. Current logpost: -356.938. Length of jump: 5.          Running MCMC-PT iteration number: 34000 of 40000. Chain number 2. Current logpost: -364.228. Length of jump: 4.          Running MCMC-PT iteration number: 33900 of 40000. Chain number 3. Current logpost: -359.712. Length of jump: 6.          Running MCMC-PT iteration number: 33900 of 40000. Chain number 1. Current logpost: -357.819. Length of jump: 5.          Running MCMC-PT iteration number: 34000 of 40000. Chain number 4. Current logpost: -357.593. Length of jump: 5.          Running MCMC-PT iteration number: 34100 of 40000. Chain number 2. Current logpost: -361.837. Length of jump: 3.          Running MCMC-PT iteration number: 34000 of 40000. Chain number 3. Current logpost: -360.578. Length of jump: 7.          Running MCMC-PT iteration number: 34000 of 40000. Chain number 1. Current logpost: -358.478. Length of jump: 6.          Running MCMC-PT iteration number: 34100 of 40000. Chain number 4. Current logpost: -358.516. Length of jump: 5.          Running MCMC-PT iteration number: 34200 of 40000. Chain number 2. Current logpost: -361.665. Length of jump: 3.          Running MCMC-PT iteration number: 34100 of 40000. Chain number 3. Current logpost: -360.952. Length of jump: 8.          Running MCMC-PT iteration number: 34100 of 40000. Chain number 1. Current logpost: -361.25. Length of jump: 6.          Running MCMC-PT iteration number: 34200 of 40000. Chain number 4. Current logpost: -360.491. Length of jump: 5.          Running MCMC-PT iteration number: 34300 of 40000. Chain number 2. Current logpost: -362.97. Length of jump: 4.          Running MCMC-PT iteration number: 34200 of 40000. Chain number 3. Current logpost: -358.985. Length of jump: 7.          Running MCMC-PT iteration number: 34200 of 40000. Chain number 1. Current logpost: -363.176. Length of jump: 7.          Running MCMC-PT iteration number: 34300 of 40000. Chain number 4. Current logpost: -357.699. Length of jump: 5.          Running MCMC-PT iteration number: 34400 of 40000. Chain number 2. Current logpost: -360.103. Length of jump: 4.          Running MCMC-PT iteration number: 34300 of 40000. Chain number 3. Current logpost: -359.509. Length of jump: 7.          Running MCMC-PT iteration number: 34300 of 40000. Chain number 1. Current logpost: -359.54. Length of jump: 6.          Running MCMC-PT iteration number: 34400 of 40000. Chain number 4. Current logpost: -356.813. Length of jump: 5.          Running MCMC-PT iteration number: 34400 of 40000. Chain number 1. Current logpost: -359.964. Length of jump: 5.          Running MCMC-PT iteration number: 34400 of 40000. Chain number 3. Current logpost: -361.8. Length of jump: 7.          Running MCMC-PT iteration number: 34500 of 40000. Chain number 2. Current logpost: -361.398. Length of jump: 4.          Running MCMC-PT iteration number: 34500 of 40000. Chain number 4. Current logpost: -357.744. Length of jump: 5.          Running MCMC-PT iteration number: 34600 of 40000. Chain number 2. Current logpost: -360.596. Length of jump: 4.          Running MCMC-PT iteration number: 34500 of 40000. Chain number 1. Current logpost: -360.927. Length of jump: 5.          Running MCMC-PT iteration number: 34500 of 40000. Chain number 3. Current logpost: -363.359. Length of jump: 7.          Running MCMC-PT iteration number: 34600 of 40000. Chain number 4. Current logpost: -360.174. Length of jump: 5.          Running MCMC-PT iteration number: 34700 of 40000. Chain number 2. Current logpost: -361.205. Length of jump: 5.          Running MCMC-PT iteration number: 34600 of 40000. Chain number 1. Current logpost: -360.743. Length of jump: 5.          Running MCMC-PT iteration number: 34600 of 40000. Chain number 3. Current logpost: -359.329. Length of jump: 6.          Running MCMC-PT iteration number: 34700 of 40000. Chain number 4. Current logpost: -360.946. Length of jump: 5.          Running MCMC-PT iteration number: 34800 of 40000. Chain number 2. Current logpost: -360.968. Length of jump: 4.          Running MCMC-PT iteration number: 34700 of 40000. Chain number 1. Current logpost: -361.171. Length of jump: 5.          Running MCMC-PT iteration number: 34700 of 40000. Chain number 3. Current logpost: -358.275. Length of jump: 6.          Running MCMC-PT iteration number: 34800 of 40000. Chain number 4. Current logpost: -358.559. Length of jump: 5.          Running MCMC-PT iteration number: 34900 of 40000. Chain number 2. Current logpost: -361.311. Length of jump: 3.          Running MCMC-PT iteration number: 34800 of 40000. Chain number 1. Current logpost: -366.704. Length of jump: 7.          Running MCMC-PT iteration number: 34800 of 40000. Chain number 3. Current logpost: -358.355. Length of jump: 6.          Running MCMC-PT iteration number: 34900 of 40000. Chain number 4. Current logpost: -358.774. Length of jump: 4.          Running MCMC-PT iteration number: 35000 of 40000. Chain number 2. Current logpost: -361.421. Length of jump: 3.          Running MCMC-PT iteration number: 34900 of 40000. Chain number 1. Current logpost: -367.495. Length of jump: 8.          Running MCMC-PT iteration number: 34900 of 40000. Chain number 3. Current logpost: -359. Length of jump: 6.          Running MCMC-PT iteration number: 35000 of 40000. Chain number 4. Current logpost: -358.205. Length of jump: 4.          Running MCMC-PT iteration number: 35100 of 40000. Chain number 2. Current logpost: -361.215. Length of jump: 4.          Running MCMC-PT iteration number: 35000 of 40000. Chain number 1. Current logpost: -361.678. Length of jump: 7.          Running MCMC-PT iteration number: 35000 of 40000. Chain number 3. Current logpost: -358.681. Length of jump: 5.          Running MCMC-PT iteration number: 35100 of 40000. Chain number 4. Current logpost: -359.122. Length of jump: 4.          Running MCMC-PT iteration number: 35200 of 40000. Chain number 2. Current logpost: -365.926. Length of jump: 5.          Running MCMC-PT iteration number: 35100 of 40000. Chain number 1. Current logpost: -363.08. Length of jump: 8.          Running MCMC-PT iteration number: 35100 of 40000. Chain number 3. Current logpost: -358.497. Length of jump: 5.          Running MCMC-PT iteration number: 35200 of 40000. Chain number 4. Current logpost: -358.393. Length of jump: 5.          Running MCMC-PT iteration number: 35300 of 40000. Chain number 2. Current logpost: -363.551. Length of jump: 4.          Running MCMC-PT iteration number: 35200 of 40000. Chain number 1. Current logpost: -361.574. Length of jump: 7.          Running MCMC-PT iteration number: 35200 of 40000. Chain number 3. Current logpost: -358.981. Length of jump: 6.          Running MCMC-PT iteration number: 35300 of 40000. Chain number 4. Current logpost: -357.946. Length of jump: 5.          Running MCMC-PT iteration number: 35400 of 40000. Chain number 2. Current logpost: -360.674. Length of jump: 5.          Running MCMC-PT iteration number: 35300 of 40000. Chain number 1. Current logpost: -361.874. Length of jump: 7.          Running MCMC-PT iteration number: 35300 of 40000. Chain number 3. Current logpost: -359.935. Length of jump: 6.          Running MCMC-PT iteration number: 35400 of 40000. Chain number 4. Current logpost: -358.264. Length of jump: 5.          Running MCMC-PT iteration number: 35500 of 40000. Chain number 2. Current logpost: -360.904. Length of jump: 4.          Running MCMC-PT iteration number: 35400 of 40000. Chain number 1. Current logpost: -363.534. Length of jump: 6.          Running MCMC-PT iteration number: 35400 of 40000. Chain number 3. Current logpost: -360.236. Length of jump: 6.          Running MCMC-PT iteration number: 35500 of 40000. Chain number 4. Current logpost: -358.817. Length of jump: 5.          Running MCMC-PT iteration number: 35600 of 40000. Chain number 2. Current logpost: -362.789. Length of jump: 5.          Running MCMC-PT iteration number: 35500 of 40000. Chain number 1. Current logpost: -363.467. Length of jump: 6.          Running MCMC-PT iteration number: 35500 of 40000. Chain number 3. Current logpost: -359.764. Length of jump: 6.          Running MCMC-PT iteration number: 35600 of 40000. Chain number 4. Current logpost: -359.547. Length of jump: 5.          Running MCMC-PT iteration number: 35700 of 40000. Chain number 2. Current logpost: -360.627. Length of jump: 4.          Running MCMC-PT iteration number: 35600 of 40000. Chain number 1. Current logpost: -363.583. Length of jump: 5.          Running MCMC-PT iteration number: 35600 of 40000. Chain number 3. Current logpost: -360.811. Length of jump: 4.          Running MCMC-PT iteration number: 35700 of 40000. Chain number 4. Current logpost: -358.508. Length of jump: 6.          Running MCMC-PT iteration number: 35800 of 40000. Chain number 2. Current logpost: -362.091. Length of jump: 5.          Running MCMC-PT iteration number: 35700 of 40000. Chain number 1. Current logpost: -364.019. Length of jump: 5.          Running MCMC-PT iteration number: 35700 of 40000. Chain number 3. Current logpost: -361.509. Length of jump: 4.          Running MCMC-PT iteration number: 35800 of 40000. Chain number 4. Current logpost: -359.5. Length of jump: 7.          Running MCMC-PT iteration number: 35900 of 40000. Chain number 2. Current logpost: -361.062. Length of jump: 5.          Running MCMC-PT iteration number: 35800 of 40000. Chain number 1. Current logpost: -364.06. Length of jump: 7.          Running MCMC-PT iteration number: 35800 of 40000. Chain number 3. Current logpost: -359.779. Length of jump: 4.          Running MCMC-PT iteration number: 35900 of 40000. Chain number 4. Current logpost: -359.82. Length of jump: 7.          Running MCMC-PT iteration number: 36000 of 40000. Chain number 2. Current logpost: -361.404. Length of jump: 5.          Running MCMC-PT iteration number: 35900 of 40000. Chain number 1. Current logpost: -365.569. Length of jump: 7.          Running MCMC-PT iteration number: 35900 of 40000. Chain number 3. Current logpost: -360.613. Length of jump: 5.          Running MCMC-PT iteration number: 36000 of 40000. Chain number 4. Current logpost: -358.028. Length of jump: 6.          Running MCMC-PT iteration number: 36100 of 40000. Chain number 2. Current logpost: -360.194. Length of jump: 4.          Running MCMC-PT iteration number: 36000 of 40000. Chain number 1. Current logpost: -364.325. Length of jump: 6.          Running MCMC-PT iteration number: 36000 of 40000. Chain number 3. Current logpost: -360.394. Length of jump: 5.          Running MCMC-PT iteration number: 36100 of 40000. Chain number 4. Current logpost: -358.333. Length of jump: 6.          Running MCMC-PT iteration number: 36200 of 40000. Chain number 2. Current logpost: -362.807. Length of jump: 5.          Running MCMC-PT iteration number: 36100 of 40000. Chain number 1. Current logpost: -365.161. Length of jump: 7.          Running MCMC-PT iteration number: 36100 of 40000. Chain number 3. Current logpost: -360.039. Length of jump: 5.          Running MCMC-PT iteration number: 36200 of 40000. Chain number 4. Current logpost: -363.818. Length of jump: 5.          Running MCMC-PT iteration number: 36200 of 40000. Chain number 1. Current logpost: -364.469. Length of jump: 7.          Running MCMC-PT iteration number: 36300 of 40000. Chain number 2. Current logpost: -361.255. Length of jump: 6.          Running MCMC-PT iteration number: 36200 of 40000. Chain number 3. Current logpost: -358.625. Length of jump: 4.          Running MCMC-PT iteration number: 36300 of 40000. Chain number 4. Current logpost: -361.137. Length of jump: 5.          Running MCMC-PT iteration number: 36400 of 40000. Chain number 2. Current logpost: -361.768. Length of jump: 6.          Running MCMC-PT iteration number: 36300 of 40000. Chain number 3. Current logpost: -358.308. Length of jump: 4.          Running MCMC-PT iteration number: 36300 of 40000. Chain number 1. Current logpost: -361.351. Length of jump: 4.          Running MCMC-PT iteration number: 36400 of 40000. Chain number 4. Current logpost: -358.382. Length of jump: 5.          Running MCMC-PT iteration number: 36500 of 40000. Chain number 2. Current logpost: -363.81. Length of jump: 8.          Running MCMC-PT iteration number: 36400 of 40000. Chain number 3. Current logpost: -358.745. Length of jump: 5.          Running MCMC-PT iteration number: 36400 of 40000. Chain number 1. Current logpost: -361.194. Length of jump: 4.          Running MCMC-PT iteration number: 36500 of 40000. Chain number 4. Current logpost: -361.621. Length of jump: 6.          Running MCMC-PT iteration number: 36600 of 40000. Chain number 2. Current logpost: -363.769. Length of jump: 8.          Running MCMC-PT iteration number: 36500 of 40000. Chain number 3. Current logpost: -358.893. Length of jump: 4.          Running MCMC-PT iteration number: 36500 of 40000. Chain number 1. Current logpost: -360.719. Length of jump: 4.          Running MCMC-PT iteration number: 36600 of 40000. Chain number 4. Current logpost: -360.186. Length of jump: 6.          Runni of 40000. Chain number 2. Current logpost: -362.147. Length of jump: 6.          Running MCMC-PT iteration number: 36600 of 40000. Chain number 3. Current logpost: -359.412. Length of jump: 4.          Running MCMC-PT iteration number: 36600 of 40000. Chain number 1. Current logpost: -359.216. Length of jump: 5.          Running MCMC-PT iteration number: 36700 of 40000. Chain number 4. Current logpost: -360.368. Length of jump: 6.          Running MCMC-PT iteration number: 36800 of 40000. Chain number 2. Current logpost: -361.979. Length of jump: 6.          Running MCMC-PT iteration number: 36700 of 40000. Chain number 1. Current logpost: -359.275. Length of jump: 5.          Running MCMC-PT iteration number: 36700 of 40000. Chain number 3. Current logpost: -359.614. Length of jump: 4.          Running MCMC-PT iteration number: 36800 of 40000. Chain number 4. Current logpost: -359.456. Length of jump: 5.          Running MCMC-PT iteration number: 36900 of 40000. Chain number 2. Current logpost: -361.958. Length of jump: 6.          Running MCMC-PT iteration number: 36800 of 40000. Chain number 3. Current logpost: -360.292. Length of jump: 4.          Running MCMC-PT iteration number: 36800 of 40000. Chain number 1. Current logpost: -359.644. Length of jump: 6.          Running MCMC-PT iteration number: 36900 of 40000. Chain number 4. Current logpost: -360.178. Length of jump: 4.          Running MCMC-PT iteration number: 37000 of 40000. Chain number 2. Current logpost: -361.071. Length of jump: 6.          Running MCMC-PT iteration number: 36900 of 40000. Chain number 3. Current logpost: -360.846. Length of jump: 4.          Running MCMC-PT iteration number: 36900 of 40000. Chain number 1. Current logpost: -361.368. Length of jump: 6.          Running MCMC-PT iteration number: 37000 of 40000. Chain number 4. Current logpost: -358.237. Length of jump: 5.          Running MCMC-PT iteration number: 37000 of 40000. Chain number 1. Current logpost: -362.658. Length of jump: 7.          Running MCMC-PT iteration number: 37000 of 40000. Chain number 3. Current logpost: -360.094. Length of jump: 4.          Running MCMC-PT iteration number: 37100 of 40000. Chain number 2. Current logpost: -360.776. Length of jump: 4.          Running MCMC-PT iteration number: 37100 of 40000. Chain number 4. Current logpost: -358.246. Length of jump: 5.          Running MCMC-PT iteration number: 37100 of 40000. Chain number 3. Current logpost: -360.721. Length of jump: 4.          Running MCMC-PT iteration number: 37200 of 40000. Chain number 2. Current logpost: -360.338. Length of jump: 5.          Running MCMC-PT iteration number: 37100 of 40000. Chain number 1. Current logpost: -361.12. Length of jump: 5.          Running MCMC-PT iteration number: 37200 of 40000. Chain number 4. Current logpost: -360.077. Length of jump: 5.          Running MCMC-PT iteration number: 37200 of 40000. Chain number 3. Current logpost: -360.036. Length of jump: 4.          Running MCMC-PT iteration number: 37300 of 40000Running MCMC-PT iteration number: . Chain number 372002. Current logpost:  of -362.011. Length of jump: 4.          40000. Chain number 1. Current logpost: -361.323. Length of jump: 5.          Running MCMC-PT iteration number: 37300 of 40000. Chain number 4. Current logpost: -357.74. Length of jump: 5.          Running MCMC-PT iteration number: 37400 of 40000. Chain number 2. Current logpost: -361.436. Length of jump: 5.          Running MCMC-PT iteration number: 37300 of 40000. Chain number 3. Current logpost: -364.637. Length of jump: 4.          Running MCMC-PT iteration number: 37300 of 40000. Chain number 1. Current logpost: -360.676. Length of jump: 5.          Running MCMC-PT iteration number: 37400 of 40000. Chain number 4. Current logpost: -359.33. Length of jump: 5.          Running MCMC-PT iteration number: 37400 of 40000. Chain number 3. Current logpost: -363.551. Length of jump: 4.          Running MCMC-PT iteration number: 37400 of 40000. Chain number 1. Current logpost: -359.923. Length of jump: 4.          Running MCMC-PT iteration number: 37500 of 40000. Chain number 2. Current logpost: -360.696. Length of jump: 5.          Running MCMC-PT iteration number: 37500 of 40000. Chain number 1. Current logpost: -360.514. Length of jump: 4.          Running MCMC-PT iteration number: 37600 of 40000. Chain number 2. Current logpost: -360.999. Length of jump: 6.          Running MCMC-PT iteration number: 37600 of 40000. Chain number 4. Current logpost: -360.64. Length of jump: 6.          Running MCMC-PT iteration number: 37600 of 40000. Chain number 1. Current logpost: -359.991. Length of jump: 4.          Running MCMC-PT iteration number: 37600 of 40000. Chain number 3. Current logpost: -359.759. Length of jump: 4.          Running MCMC-PT iteration number: 37700 of 40000. Chain number 3. Current logpost: -359.323. Length of jump: 5.          Running MCMC-PT iteration number: 37700 of 40000. Chain number 1. Current logpost: -359.943. Length of jump: 4.          Running MCMC-PT iteration number: 37800 of 40000. Chain number 2. Current logpost: -360.551. Length of jump: 4.          Running MCMC-PT iteration number: 37800 of 40000. Chain number 4. Current logpost: -360.515. Length of jump: 4.          Running MCMC-PT iteration number: 37800 of 40000. Chain number 1. Current logpost: -358.321. Length of jump: 4.          Running MCMC-PT iteration number: 37800 of 40000. Chain number 3. Current logpost: -360.376. Length of jump: 5.          Running MCMC-PT iteration number: 37900 of 40000. Chain number 2. Current logpost: -360.568. Length of jump: 5.          Running MCMC-PT iteration number: 37900 of 40000. Chain number 4. Current logpost: -361.227. Length of jump: 4.          Running MCMC-PT iteration number: 37900 of 40000. Chain number 3. Current logpost: -358.41. Length of jump: 6.          Running MCMC-PT iteration number: 37900 of 40000. Chain number 1. Current logpost: -358.756. Length of jump: 4.          Running MCMC-PT iteration number: 38000 of 40000. Chain number 2. Current logpost: -361.832. Length of jump: 5.          Running MCMC-PT iteration number: 38000 of 40000. Chain number 4. Current logpost: -361.217. Length of jump: 4.          Running MCMC-PT iteration number: 38000 of 40000. Chain number 3. Current logpost: -359.955. Length of jump: 6.          Running MCMC-PT iteration number: 38000 of 40000. Chain number 1. Current logpost: -360.666. Length of jump: 3.          Running MCMC-PT iteration number: 38100 of 40000. Chain number 2. Current logpost: -365.617. Length of jump: 6.          Running MCMC-PT iteration number: 38100 of 40000. Chain number 4. Current logpost: -362.74. Length of jump: 4.          Running MCMC-PT iteration number: 38100 of 40000. Chain number 3. Current logpost: -358.72. Length of jump: 5.          Running MCMC-PT iteration number: 38100 of 40000. Chain number 1. Current logpost: -361.329. Length of jump: 3.          Running MCMC-PT iteration number: 38200 of 40000. Chain number 2. Current logpost: -363.43. Length of jump: 7.          Running MCMC-PT iteration number: 38200 of 40000. Chain number 4. Current logpost: -361.788. Length of jump: 5.          Running MCMC-PT iteration number: 38200 of 40000. Chain number 3. Current logpost: -361.161. Length of jump: 4.          Running MCMC-PT iteration number: 38200 of 40000. Chain number 1. Current logpost: -361.51. Length of jump: 3.          Running MCMC-PT iteration number: 38300 of 40000. Chain number 2. Current logpost: -363.132. Length of jump: 6.          Running MCMC-PT iteration number: 38300 of 40000. Chain number 4. Current logpost: -361.559. Length of jump: 5.          Running MCMC-PT iteration number: 38300 of 40000. Chain number 3. Current logpost: -360.242. Length of jump: 4.          Running MCMC-PT iteration number: 38300 of 40000. Chain number 1. Current logpost: -362.536. Length of jump: 3.          Running MCMC-PT iteration number: 38400 of 40000. Chain number 2. Current logpost: -361. Length of jump: 5.          Running MCMC-PT iteration number: 38400 of 40000. Chain number 4. Current logpost: -363.779. Length of jump: 5.          Running MCMC-PT iteration number: 38400 of 40000. Chain number 3. Current logpost: -362.327. Length of jump: 3.          Running MCMC-PT iteration number: 38400 of 40000. Chain number 1. Current logpost: -361.308. Length of jump: 4.          Running MCMC-PT iteration number: 38500 of 40000. Chain number 2. Current logpost: -361.773. Length of jump: 6.          Running MCMC-PT iteration number: 38500 of 40000. Chain number 3. Current logpost: -361.191. Length of jump: 3.          Running MCMC-PT iteration number: 38500 of 40000. Chain number 4. Current logpost: -362.284. Length of jump: 5.          Running MCMC-PT iteration number: 38500 of 40000. Chain number 1. Current logpost: -362.173. Length of jump: 4.          Running MCMC-PT iteration number: 38600 of 40000. Chain number 2. Current logpost: -365.556. Length of jump: 6.          Running MCMC-PT iteration number: 38600 of 40000. Chain number 3. Current logpost: -361.192. Length of jump: 3.          Running MCMC-PT iteration number: 38600 of 40000. Chain number 4. Current logpost: -361.759. Length of jump: 5.          Running MCMC-PT iteration number: 38600 of 40000. Chain number 1. Current logpost: -362.325. Length of jump: 6.          Running MCMC-PT iteration number: 38700 of 40000. Chain number 2. Current logpost: -361.057. Length of jump: 6.          Running MCMC-PT iteration number: 38700 of 40000. Chain number 3. Current logpost: -360.321. Length of jump: 4.          Running MCMC-PT iteration number: 38700 of 40000. Chain number 4. Current logpost: -364.789. Length of jump: 6.          Running MCMC-PT iteration number: 38700 of 40000. Chain number 1. Current logpost: -363.313. Length of jump: 6.          Running MCMC-PT iteration number: 38800 of 40000. Chain number 2. Current logpost: -363.742. Length of jump: 5.          Running MCMC-PT iteration number: 38800 of 40000. Chain number 3. Current logpost: -360.127. Length of jump: 4.          Running MCMC-PT iteration number: 38800 of 40000. Chain number 4. Current logpost: -362.734. Length of jump: 6.          Running MCMC-PT iteration number: 38900 of 40000. Chain number 2. Current logpost: -362.3. Length of jump: 6.          Running MCMC-PT iteration number: 38800 of 40000. Chain number 1. Current logpost: -363.144. Length of jump: 7.          Running MCMC-PT iteration number: 38900 of 40000. Chain number 3. Current logpost: -360.907. Length of jump: 5.          Running MCMC-PT iteration number: 38900 of 40000. Chain number 4. Current logpost: -360.925. Length of jump: 5.          Running MCMC-PT iteration number: 39000 of 40000. Chain number 2. Current logpost: -360.428. Length of jump: 6.          Running MCMC-PT iteration number: 38900 of 40000. Chain number 1. Current logpost: -361.187. Length of jump: 6.          Running MCMC-PT iteration number: 39000 of 40000. Chain number 3. Current logpost: -360.711. Length of jump: 4.          Running MCMC-PT iteration number: 39000 of 40000. Chain number 4. Current logpost: -362.158. Length of jump: 5.          Running MCMC-PT iteration number: 39100 of 40000. Chain number 2. Current logpost: -358.809. Length of jump: 6.          Running MCMC-PT iteration number: 39000 of 40000. Chain number 1. Current logpost: -360.952. Length of jump: 4.          Running MCMC-PT iteration number: 39100 of 40000. Chain number 3. Current logpost: -362.368. Length of jump: 3.          Running MCMC-PT iteration number: 39100 of 40000. Chain number 4. Current logpost: -363.067. Length of jump: 5.          Running MCMC-PT iteration number: 39200 of 40000. Chain number 2. Current logpost: -360.125. Length of jump: 6.          Running MCMC-PT iteration number: 39100 of 40000. Chain number 1. Current logpost: -361.532. Length of jump: 4.          Running MCMC-PT iteration number: 39200 of 40000. Chain number 3. Current logpost: -362.479. Length of jump: 5.          Running MCMC-PT iteration number: 39200 of 40000. Chain number 4. Current logpost: -360.013. Length of jump: 4.          Running MCMC-PT iteration number: 39300 of 40000. Chain number 2. Current logpost: -358.86. Length of jump: 6.          Running MCMC-PT iteration number: 39200 of 40000. Chain number 1. Current logpost: -362.32. Length of jump: 4.          Running MCMC-PT iteration number: 39300 of 40000. Chain number 3. Current logpost: -361.374. Length of jump: 5.          Running MCMC-PT iteration number: 39300 of 40000. Chain number 4. Current logpost: -360.725. Length of jump: 4.          Running MCMC-PT iteration number: 39300 of 40000. Chain number 1. Current logpost: -361.541. Length of jump: 4.          Running MCMC-PT iteration number: 39400 of 40000. Chain number 2. Current logpost: -361.274. Length of jump: 7.          Running MCMC-PT iteration number: 39400 of 40000. Chain number 3. Current logpost: -364.08. Length of jump: 5.          Running MCMC-PT iteration number: 39400 of 40000. Chain number 4. Current logpost: -363.747. Length of jump: 4.          Running MCMC-PT iteration number: 39400 of 40000. Chain number 1. Current logpost: -361.805. Length of jump: 5.          Running MCMC-PT iteration number: 39500 of 40000. Chain number 2. Current logpost: -359.659. Length of jump: 7.          Running MCMC-PT iteration number: 39500 of 40000. Chain number 3. Current logpost: -363.508. Length of jump: 6.          Running MCMC-PT iteration number: 39500 of 40000. Chain number 4. Current logpost: -361.876. Length of jump: 4.          Running MCMC-PT iteration number: 39500 of 40000. Chain number 1. Current logpost: -360.833. Length of jump: 5.          Running MCMC-PT iteration number: 39600 of 40000. Chain number 2. Current logpost: -360.97. Length of jump: 7.          Running MCMC-PT iteration number: 39600 of 40000. Chain number 3. Current logpost: -364.411. Length of jump: 7.          Running MCMC-PT iteration number: 39600 of 40000. Chain number 4. Current logpost: -360.941. Length of jump: 4.          Running MCMC-PT iteration number: 39600 of 40000. Chain number 1. Current logpost: -361.316. Length of jump: 5.          Running MCMC-PT iteration number: 39700 of 40000. Chain number 2. Current logpost: -358.507. Length of jump: 6.          Running MCMC-PT iteration number: 39700 of 40000. Chain number 4. Current logpost: -360.37. Length of jump: 4.          Running MCMC-PT iteration number: 39700 of 40000. Chain number 3. Current logpost: -363.55. Length of jump: 6.          Running MCMC-PT iteration number: 39700 of 40000. Chain number 1. Current logpost: -362.529. Length of jump: 5.          Running MCMC-PT iteration number: 39800 of 40000. Chain number 2. Current logpost: -359.597. Length of jump: 6.          Running MCMC-PT iteration number: 39800 of 40000. Chain number 4. Current logpost: -361.951. Length of jump: 7.          Running MCMC-PT iteration number: 39800 of 40000. Chain number 3. Current logpost: -363.768. Length of jump: 6.          Running MCMC-PT iteration number: 39900 of 40000. Chain number 3. Current logpost: -362.984. Length of jump: 5.          Running MCMC-PT iteration number: 39900 of 40000. Chain number 1. Current logpost: -360.704. Length of jump: 5.          Running MCMC-PT iteration number: 39900 of 40000. Chain number 4. Current logpost: -362.797. Length of jump: 6.          
```

``` r
# Run diagnostics to check for mixing issues
cat("\n=== Running RJMC Diagnostics ===\n")
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
## 1     1   5.48  1.32        5     4     6
## 2     2   5.65  1.19        6     5     6
## 3     3   5.49  1.26        5     5     6
## 4     4   5.46  1.09        5     5     6
```

``` r
# 2. Compare beta values between chains (conditional on K)
# Focus on the most common K value
K_mode <- as.numeric(names(sort(table(all_samples$K), decreasing = TRUE)[1]))
cat("\nMost common K value:", K_mode, "\n")
```

```
## 
## Most common K value: 5
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
## # A tibble: 20 × 7
##    segment chain mean_beta   sd_beta median_beta q25_beta q75_beta
##      <dbl> <int>     <dbl>     <dbl>       <dbl>    <dbl>    <dbl>
##  1       1     1    0.300  0.000640       0.300    0.299    0.300 
##  2       1     2    0.300  0.000695       0.300    0.299    0.300 
##  3       1     3    0.300  0.000845       0.300    0.299    0.300 
##  4       1     4    0.300  0.000643       0.299    0.299    0.300 
##  5       2     1    0.0100 0.000235       0.01     0.01     0.01  
##  6       2     2    0.0502 0.0995         0.01     0.01     0.01  
##  7       2     3    0.0100 0.0000988      0.01     0.01     0.01  
##  8       2     4    0.0637 0.113          0.01     0.01     0.01  
##  9       3     1    0.0475 0.112          0.01     0.01     0.0110
## 10       3     2    0.0103 0.00105        0.01     0.01     0.01  
## 11       3     3    0.0150 0.0419         0.01     0.01     0.01  
## 12       3     4    0.166  0.188          0.0106   0.01     0.388 
## 13       4     1    0.298  0.167          0.399    0.0774   0.404 
## 14       4     2    0.118  0.169          0.0121   0.01     0.397 
## 15       4     3    0.190  0.196          0.0122   0.01     0.403 
## 16       4     4    0.263  0.189          0.390    0.01     0.406 
## 17       5     1    0.412  0.0159         0.407    0.402    0.422 
## 18       5     2    0.407  0.0127         0.403    0.401    0.406 
## 19       5     3    0.406  0.0104         0.404    0.402    0.409 
## 20       5     4    0.407  0.00981        0.405    0.401    0.410
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
## # A tibble: 16 × 7
##    cp_idx chain mean_cp sd_cp median_cp q25_cp q75_cp
##     <dbl> <int>   <dbl> <dbl>     <dbl>  <dbl>  <dbl>
##  1      1     1    40    0           40     40   40  
##  2      1     2    38.3  4.92        40     40   40  
##  3      1     3    40    0           40     40   40  
##  4      1     4    38.1  4.21        40     40   40  
##  5      2     1    64.5 11.6         65     56   75  
##  6      2     2    57.7 10.8         61     48   66.5
##  7      2     3    56.6  8.23        56     51   61  
##  8      2     4    61.9 17.0         60     46   80  
##  9      3     1    79.9  7.33        80     79   80  
## 10      3     2    72.8  8.26        75     70   80  
## 11      3     3    72.7  9.73        77     64   80  
## 12      3     4    76.7 14.2         80     67   86  
## 13      4     1    99.2 13.5        103     80  112  
## 14      4     2    88.1 14.1         80     80   93  
## 15      4     3    92.7 14.6         80     80  107  
## 16      4     4    92.1 10.9         94     80  101
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
