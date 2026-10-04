import OEISOpen.A219692.Summation
import OEISOpen.A219692.Uniqueness
import OEISOpen.A219692.Recurrence
import OEISOpen.A219692.OriginalBracket
import OEISOpen.A219692.Coefficient
import OEISOpen.A219692.BinomialTransform
import OEISOpen.A219692.CoefficientRepresentation
import OEISOpen.A219692.Trinomial
import OEISOpen.A219692.Bridge
import OEISOpen.A219692.LaurentCentral
import OEISOpen.A219692.Specialization
import OEISOpen.A219692.Main

/-! Explicit theorem and axiom audit. The original-sum recurrence still requires Bridge. -/

#check OEISOpen.A219692.original_residual_two
#check OEISOpen.A219692.original_recurrence_from_two_false
#check OEISOpen.A219692.local_certificate_of_crossed_shifts
#check OEISOpen.A219692.positive_recurrence_of_local_certificate
#check OEISOpen.A219692.positive_recurrence
#check OEISOpen.A219692.normalized_recurrence_of_bridge
#check OEISOpen.A219692.normalized_recurrence_of_specialized_transform
#check OEISOpen.A219692.normalized_recurrence
#check OEISOpen.A219692.original_tail_recurrence
#check OEISOpen.A219692.original_residual_from_two
#print axioms OEISOpen.A219692.original_residual_two
#print axioms OEISOpen.A219692.original_term_three_one
#print axioms OEISOpen.A219692.original_recurrence_from_two_false
#print axioms OEISOpen.A219692.normalized_residual_two
#print axioms OEISOpen.A219692.tail_recurrence_of_normalized
#print axioms OEISOpen.A219692.v_eq_sum_S
#print axioms OEISOpen.A219692.v_eq_extended_sum
#print axioms OEISOpen.A219692.G_zero
#print axioms OEISOpen.A219692.G_at_upper_endpoint
#print axioms OEISOpen.A219692.first_denominator_ne_zero
#print axioms OEISOpen.A219692.second_denominator_ne_zero
#print axioms OEISOpen.A219692.cleared_telescoping_certificate
#print axioms OEISOpen.A219692.rational_telescoping_certificate
#print axioms OEISOpen.A219692.local_certificate_of_crossed_shifts
#print axioms OEISOpen.A219692.sum_G_differences
#print axioms OEISOpen.A219692.positive_recurrence_of_local_certificate
#print axioms OEISOpen.A219692.recurrence_unique
#print axioms OEISOpen.A219692.original_bracket_crossed
#print axioms OEISOpen.A219692.shift1_succ
#print axioms OEISOpen.A219692.shift1
#print axioms OEISOpen.A219692.shift2
#print axioms OEISOpen.A219692.shiftJ
#print axioms OEISOpen.A219692.local_telescoping
#print axioms OEISOpen.A219692.positive_recurrence
#print axioms OEISOpen.A219692.normalized_eq_positive_of_bridge
#print axioms OEISOpen.A219692.normalized_recurrence_of_bridge
#print axioms OEISOpen.A219692.original_tail_recurrence_of_bridge
#print axioms OEISOpen.A219692.coefficient_substitution
#print axioms OEISOpen.A219692.p_two
#print axioms OEISOpen.A219692.q_two
#print axioms OEISOpen.A219692.bridge_binomial_product
#print axioms OEISOpen.A219692.p1_summand_rearrangement
#print axioms OEISOpen.A219692.trinomial_coefficient_closed
#print axioms OEISOpen.A219692.exponentRotation_injective
#print axioms OEISOpen.A219692.constant_coefficient_rotation
#print axioms OEISOpen.A219692.original_coefficient_representation
#print axioms OEISOpen.A219692.trinomial_coefficient_expanded
#print axioms OEISOpen.A219692.p1
#print axioms OEISOpen.A219692.bridgePolynomial_coeff
#print axioms OEISOpen.A219692.bridge_of_specialized_transform
#print axioms OEISOpen.A219692.normalized_recurrence_of_specialized_transform
#print axioms OEISOpen.A219692.quadratic_middle_coeff
#print axioms OEISOpen.A219692.shifted_toLaurent_coeff
#print axioms OEISOpen.A219692.laurent_ct_trinomial
#print axioms OEISOpen.A219692.laurent_ct_central
#print axioms OEISOpen.A219692.laurent_ct_antisymmetric_even
#print axioms OEISOpen.A219692.specialization_term
#print axioms OEISOpen.A219692.convolution_eq_binomial_sum
#print axioms OEISOpen.A219692.specialized_transform_sum
#print axioms OEISOpen.A219692.p1_range_central
#print axioms OEISOpen.A219692.central_binomial_transform
#print axioms OEISOpen.A219692.specialized_transform
#print axioms OEISOpen.A219692.original_eq_positive
#print axioms OEISOpen.A219692.normalized_eq_positive
#print axioms OEISOpen.A219692.normalized_recurrence
#print axioms OEISOpen.A219692.original_tail_recurrence
#print axioms OEISOpen.A219692.original_residual_from_two

