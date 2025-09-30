## Reversible Jump Markov Chain Monte Carlo (RJMC)

![RJMC Logo](rjmc_logo.png)

[![Project Status: Active – The project has reached a stable, usable state and is being actively developed.](https://www.repostatus.org/badges/latest/active.svg)](https://www.repostatus.org/#active)
[![R-CMD-check](https://github.com/seroanalytics/serojump/actions/workflows/R-CMD-check.yaml/badge.svg)](https://github.com/seroanalytics/serojump/actions/workflows/R-CMD-check.yaml)

# rjmc: Reversible Jump Markov Chain Monte Carlo for Model Selection

**`rjmc`** is an R package designed to perform Bayesian inference using the **Reversible Jump Markov Chain Monte Carlo (RJMCMC)** algorithm. This method facilitates efficient exploration of **variable-dimension parameter spaces**, making it especially suitable for tasks such as model selection and problems where the number of parameters can change. This implementation is inspired by the seminal work of [Peter J. Green (1995)](https://people.maths.bris.ac.uk/~mapjg/papers/RJMCMCBka.pdf).

## Features

* Implements a **Metropolis-Hastings-like algorithm** that supports jumps between models with different dimensions.
* Flexible framework for **user-defined model spaces**, likelihoods, and priors.
* Effective at exploring high-dimensional posterior distributions with a variable number of parameters.
* Enables **Bayesian model selection and averaging** through a rigorous probabilistic framework.

## Why Use Reversible Jump MCMC?

Standard MCMC techniques are limited to fixed-dimensional parameter spaces, which restricts their application to problems where the number of parameters is known and constant. RJMCMC overcomes this limitation by allowing jumps between models with different dimensions, enabling:

* Bayesian model selection (e.g., choosing between competing hypotheses).
* Joint inference over models and their parameters.
* Exploration of hierarchical or nested model structures.

By combining the strengths of MCMC with the flexibility of dynamic model spaces, RJMCMC is a powerful tool for tackling complex Bayesian inference problems.

## Installation

To install the `rjmc` package, follow these steps:

### Step 1: Install R

Make sure you have R installed on your system. You can download R from [https://cran.r-project.org/](https://cran.r-project.org/).

### Step 2: Install `rjmc` from GitHub

You can install the development version of `rjmc` from GitHub using the `devtools` package. If you don't already have `devtools` installed, you can install it with:

```{r}

install.packages("devtools") 
devtools::install_github("dchodge/rjmc")

```

### Step 3: Load `rjmc` into Your R Session

After installation, you can load the `rjmc` package into your R session with:

```{r}

library(rjmc)

```

## Getting Started

We provide examples of how to implement this package for various models in the vignettes:

- Example 1: How to fit a mixture distribution where the number of mixtures is unknownhttps://cran.r-project.org/
- Example 2: How to fit a SEIR epidemiological model with unknown change points

For an interactive demonstration of mixture model fitting, try our [**RJMC Widget**](https://dchodge.github.io/rjmc-widget-mixture/) which allows you to upload your own data and explore the RJMCMC algorithm in real-time.

Refer to the background documentation or vignettes in the package for step-by-step tutorials.

## Contributing

We welcome contributions and suggestions! If you'd like to contribute to the `rjmcmc` package or report issues, please feel free to:

- Submit a pull request on GitHub.
- Open an issue on the repository.

For questions or feedback, contact the package maintainer:

**David Hodgson**
Email: [david.hodgson@charite.de](mailto:david.hodgson@charite.de)

---

## Project Status

This package is actively maintained and in a stable, usable state. New features and improvements are continually being developed.
