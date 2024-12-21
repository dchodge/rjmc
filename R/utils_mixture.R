#' Get Lengths of Jump Matrix Columns Across Chains
#'
#' This function calculates the number of columns (lengths) in the `jump` matrix
#' for each chain within the `outputs` object and compiles the results into a data frame. 
#' It also creates a sorted frequency table of the unique lengths in descending order.
#'
#' @param outputs List. A list containing the `jump` matrices for all chains. 
#'                Typically, this is the output from an RJMCMC process.
#' @param n_chain Integer. The number of chains to process.
#' @return A named vector representing the sorted frequency table of column lengths
#'         across all chains.
#'
#' @details
#' The function iterates through each chain in the range `1:n_chain`. For each chain, 
#' it calculates the number of columns in each `jump` matrix stored in `outputs$jump`. 
#' These lengths are compiled into a data frame with two columns:
#' - `chain`: The chain index.
#' - `length_n`: The number of columns in the `jump` matrix for that chain.
#'
#' Finally, it creates a frequency table of the `length_n` values and sorts it 
#' in descending order, allowing the user to see the most common lengths of `jump` matrices.
#'
#' @export
get_lengths <- function(outputs, n_chain) {
  length_df <- map_df(1:n_chain,
    function(c) {
      n_length <- vector()
      for (i in 1:length(outputs$jump[[c]])) {
          n_length[i] <- outputs$jump[[c]][[i]] %>% ncol
      }
      data.frame(
        chain = c,
        length_n = n_length
      )
    }
  )
  tables_length <- sort(table(length_df$length_n), decreasing = TRUE)
}

#' Extract and Process Clean Posterior Samples from RJMCMC Outputs
#'
#' This function filters and processes posterior samples from RJMCMC outputs
#' based on a specified mixture size. It generates clean posterior summaries 
#' and the trajectory of the posterior distribution.
#'
#' @param outputs List. The RJMCMC outputs, containing `jump` matrices for all chains.
#' @param mix_size Integer. The desired mixture size (number of components) to filter the posterior samples.
#' @param n_chain Integer. The number of chains in the RJMCMC output.
#' @return A list containing two components:
#' \itemize{
#'   \item \code{summary_post}: A data frame summarizing the posterior samples with columns:
#'         \code{p} (mixing proportions), \code{mu} (means), \code{sigma} (standard deviations),
#'         \code{order} (ranked means), \code{sample} (sample index), and \code{chain} (chain index).
#'   \item \code{post_traj_sum}: A data frame summarizing the posterior trajectory, including mean
#'         and uncertainty intervals (\code{mean_qi}).
#' }
#'
#' @details
#' The function filters `jump` matrices for samples matching the specified \code{mix_size} (number of components).
#' It constructs a clean summary of posterior parameters and calculates the posterior trajectory
#' using a sequence of x-values (e.g., for visualization of the mixture distribution).
#'
#' Steps:
#' 1. **Filter Samples**:
#'    - Selects `jump` matrices with \code{mix_size} columns.
#'    - Extracts parameters: mixing proportions (\code{p}), means (\code{mu}), and standard deviations (\code{sigma}).
#' 2. **Generate Posterior Trajectory**:
#'    - Uses the filtered posterior parameters to calculate the PDF of the mixture distribution over a range of x-values.
#'    - Aggregates the trajectories across samples using \code{mean_qi()} to summarize uncertainty.
#'
#' @export
get_clean_posterior <- function(outputs, mix_size, n_chain) {
  s <<- 1
  summary_post <- map_df(1:n_chain,
    function(c) {
      list_outputs_mode <- list()
      j <- 1
      for (i in 1:length(outputs$jump[[c]])) {
          if ((outputs$jump[[c]][[i]] %>% ncol) == mix_size) {
              sample_i <- (outputs$jump[[c]][[i]])
              order_second_row <- rank(sample_i[2, ])
              list_outputs_mode[[j]] <- data.frame(
                  p = sample_i[1, ],
                  mu = sample_i[2, ],
                  sigma = sample_i[3, ],
                  order = order_second_row,
                  sample = s,
                  chain = c
              )
              s <<- s + 1
              j <- j + 1
          }
      }
      list_outputs_mode %>% bind_rows()
    }
  )

  n_length <- (summary_post %>% nrow) / as.numeric(mix_size)


  post_traj <- map_df(1:n_length,
    function(si) { 
      summary_post_s <- summary_post %>% filter(sample == si)
      # Define parameters for the normal distributions
      means <- summary_post_s[, 2] %>% as.vector %>% unlist #%>% .[[1]]
      sds <- summary_post_s[, 3] %>% as.vector  %>% unlist#%>% .[[1]]
      weights <- summary_post_s[, 1] %>% as.vector %>% unlist #%>% .[[1]]

      # Create a sequence of x values#
      x_values <- seq(0, 18, 0.1)
      # Calculate the PDF of the mixture distribution
      
      data.frame(
        x = x_values,
        y_post = sapply(x_values, function(x) {
          sum(weights * dnorm(x, mean = means, sd = sds))
        })
      )
    }
  )

  post_traj_sum <- post_traj %>% group_by(x) %>% mean_qi

  post_process <- list(
    summary_post = summary_post,
    post_traj_sum = post_traj_sum
  )
}


get_posterior_component_size <- function(mix_size, tables_length, post_process, data_l) {
    p1 <- ggplot() + geom_histogram(aes(data_l$obs, y = ..density..), color = "black", fill = "lightgray") + theme_bw() + 
    xlim(0, 17) 
  plot_info <- ggplot_build(p1)
  plot_info$layout$panel_ranges[[1]]$y.range

  point_y <- - 0.1 * diff(plot_info$layout$panel_scales_y[[1]]$range$range) + plot_info$layout$panel_scales_y[[1]]$range$range[1]
  point_y_lim <- - 0.15 * diff(plot_info$layout$panel_scales_y[[1]]$range$range) + plot_info$layout$panel_scales_y[[1]]$range$range[1]

  prop <- tables_length / sum(tables_length)
  plotl <- prop[mix_size]

  p1_anot <- p1 +  stat_slabinterval(data = post_process$summary_post, 
      aes(x = mu, y = point_y, group = as.character(order)), 
        fill = "orange", color = "darkorange", side = "bottomright") + 
      geom_ribbon(data = post_process$post_traj_sum, aes(x = x, ymin = .lower, ymax = .upper), fill = "red", alpha = 0.5) +
      geom_line(data = post_process$post_traj_sum, aes(x = x, y = y_post), color = "red", alpha = 0.9) + 
      labs(x = "Time (days)", y = "Number of cases", 
        title = paste0("Posterior distribution for ", mix_size, " mixture components (", round(plotl * 100, 0), "% of posterior)")) + ylim(point_y_lim, NA)
}