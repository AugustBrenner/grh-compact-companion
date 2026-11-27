import Main
import Readable.Step0_StepanovWarmup
import Readable.Step1_ProductFormulaAndPinch
import Readable.Step2_BehrendSphere
import Readable.Step3_AnalyticEndgame
import Readable.Step4_MainProof

-- 5 root theorems from Main.lean
#print axioms riemannHypothesis
#print axioms riemannZeta_eq_zero_re
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
#print axioms LFunction_eq_zero_re_of_isPrimitive

-- 15 public walkthrough theorems from src/Readable/
#print axioms Readable.StepanovWarmup.stepanov_S_plus_bound
#print axioms Readable.StepanovWarmup.stepanov_warmup
#print axioms Readable.ProductFormulaAndPinch.rational_product_formula_log
#print axioms Readable.ProductFormulaAndPinch.product_formula_for_heights
#print axioms Readable.ProductFormulaAndPinch.greedy_covering_from_spread
#print axioms Readable.ProductFormulaAndPinch.twisted_lattice_volume_pinch
#print axioms Readable.BehrendSphere.behrend_three_term_free
#print axioms Readable.AnalyticEndgame.cauchy_moment_window
#print axioms Readable.AnalyticEndgame.one_sided_zero_free_criterion
#print axioms Readable.MainProof.theorem_C_integral_forms_long
#print axioms Readable.MainProof.star_inequality
#print axioms Readable.MainProof.eventually_one_sided_prime_bound
#print axioms Readable.MainProof.grh_half_plane
#print axioms Readable.MainProof.grh_critical_line
#print axioms Readable.MainProof.rh_critical_line
