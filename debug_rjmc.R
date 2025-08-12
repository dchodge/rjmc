#!/usr/bin/env Rscript
# Debug script for RJMC mixing issues
# Run this to diagnose why the algorithm gets stuck

library(devtools)
devtools::load_all()

# Load the vignette data and model
source("vignettes/Ex2_seir_attack_rate.Rmd")

# Test the proposal probabilities for different K values
cat("=== Testing Proposal Probabilities ===\n")
for (K in 1:10) {
  # Create a dummy jump matrix
  dummy_jump <- matrix(runif(2*K), nrow = 2, ncol = K)
  probs <- model$sampleProposal(c(0), dummy_jump, data_l)
  cat(sprintf("K = %d: birth = %.3f, death = %.3f, within = %.3f\n", 
              K, probs[1], probs[2], probs[3]))
}

# Test initialization multiple times
cat("\n=== Testing Initialization ===\n")
for (i in 1:5) {
  init_jump <- model$sampleInitJump(c(0), data_l)
  cat(sprintf("Init %d: K = %d, segments = %d\n", 
              i, ncol(init_jump), ncol(init_jump)))
}

# Test birth/death proposals
cat("\n=== Testing Birth/Death Proposals ===\n")
test_jump <- matrix(c(0.3, 0.2, 50, 100), nrow = 2, byrow = TRUE)
cat("Original jump:\n")
print(test_jump)

# Test birth proposal
birth_result <- model$sampleBirthProposal(c(0), test_jump, 1, data_l)
cat("Birth proposal result:\n")
print(birth_result)

# Test death proposal  
death_result <- model$sampleDeathProposal(c(0), test_jump, 1, data_l)
cat("Death proposal result:\n")
print(death_result)

# Test likelihood evaluation
cat("\n=== Testing Likelihood Evaluation ===\n")
log_lik <- model$evaluateLogLikelihood(c(0), test_jump, data_l)
cat("Log likelihood:", log_lik, "\n")

# Test prior evaluation
log_prior <- model$evaluateLogPrior(c(0), test_jump, data_l)
cat("Log prior:", log_prior, "\n")

cat("\n=== Debug Complete ===\n")
cat("If everything looks good above, the issue might be in the RJMC algorithm itself.\n")
cat("Try running with the improved settings in the vignette.\n") 