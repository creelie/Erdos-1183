import Erdos1183

/-! Axiom audit: every main theorem should depend only on
`propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`). -/

-- the two conjectures, in the form stated on erdosproblems.com
#print Erdos1183.FirstConjecture
#print Erdos1183.SecondConjecture
#print axioms Erdos1183.erdos_1183
#print axioms Erdos1183.first_conjecture
#print axioms Erdos1183.second_conjecture
-- explicit forms
#print axioms Erdos1183.bigF_lower_explicit
#print axioms Erdos1183.lower_const_le
#print axioms Erdos1183.pow_le_bigF
#print axioms Erdos1183.rpow_loglog_le_bigF
#print axioms Erdos1183.first_conjecture_explicit
#print axioms Erdos1183.bigF_le_loglog
#print axioms Erdos1183.bigF_le_loglog_real
#print axioms Erdos1183.omega_le_of_pow_le
-- supporting results
#print axioms Erdos1183.box_ineq
#print axioms Erdos1183.card_mono_boxes
#print axioms Erdos1183.exists_good_pattern
#print axioms Erdos1183.card_le_bigF
#print axioms Erdos1183.pow_le_mul_bigF
#print axioms Erdos1183.first_conjecture_nat
#print axioms Erdos1183.bigF_superpolynomial
#print axioms Erdos1183.bigF_subexponential
#print axioms Erdos1183.bigF_lt_two_pow
#print axioms Erdos1183.le_bigF_iff
#print axioms Erdos1183.bigF_le_iff
#print axioms Erdos1183.bigF_le_sum_choose
#print axioms Erdos1183.bigF_le_explicit
#print axioms Erdos1183.half_le_smallF
#print axioms Erdos1183.smallF_le_bigF
