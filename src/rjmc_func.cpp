
#include <RcppCommon.h>
#include <Rcpp.h>
#include <RcppEigen.h>
#include <Eigen/Core>

#include "./headers/mvn.hpp"
#include "./headers/rjmc.hpp"

// [[Rcpp::depends(RcppEigen)]]

// [[Rcpp::depends(BH)]]

// [[Rcpp::export]]
List run_rjmc(Rcpp::List model, Rcpp::RObject dataList, Rcpp::List settings, bool update_ind, Rcpp::List RJMCpar, int i)
{

  rjmc_full::RJMC_FULL_D RJMC_FULL;

  List output_full;
  MatrixXd output;
  List jump;
  // Priors 
  rjmc_full::init_sampleInitPrior(&RJMC_FULL, model["sampleInitPrior"]);
  rjmc_full::init_sampleInitJump(&RJMC_FULL, model["sampleInitJump"]);
  rjmc_full::init_evaluateLogPrior(&RJMC_FULL, model["evaluateLogPrior"]);
  rjmc_full::init_evaluateLogLikelihood(&RJMC_FULL, model["evaluateLogLikelihood"]);
  rjmc_full::init_sampleBirthProposal(&RJMC_FULL, model["sampleBirthProposal"]);
  rjmc_full::init_sampleDeathProposal(&RJMC_FULL, model["sampleDeathProposal"]);
  rjmc_full::init_evaluateBirthProposal(&RJMC_FULL, model["evaluateBirthProposal"]);
  rjmc_full::init_evaluateDeathProposal(&RJMC_FULL, model["evaluateDeathProposal"]);
  rjmc_full::init_sampleJump(&RJMC_FULL, model["sampleJump"]);
  rjmc_full::init_sampleProposal(&RJMC_FULL, model["sampleProposal"]);

  if (update_ind) {
    RJMC_FULL.updateClass(settings, dataList, RJMCpar);
  } else {  
    RJMC_FULL.initialiseClass(settings, dataList, i);
  }

  output_full = RJMC_FULL.runRJMCC();

  RJMCpar = RJMC_FULL.saveRJMCpar();
  output = output_full[0];
  jump = output_full[1];


  return Rcpp::List::create(_["output"] = output, _["jump"] = jump, _["RJMCpar"] = RJMCpar);

}
