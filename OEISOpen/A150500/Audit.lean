import OEISOpen.A150500.Paths
import OEISOpen.A150500.Hypergeometric
import OEISOpen.A150500.LocalizedCertificate
import OEISOpen.A150500.SeriesPullback
import OEISOpen.A150500.Recurrence
import OEISOpen.A150500.Main

/-! Audit of the complete original-path proof and its kernel-checked components.

Intermediate interfaces deliberately retain their assumptions:
* target_of_generating_function requires
    1 + 4*X*A = gauge * centralSquareSeries.subst rho;
* recurrence_of_target_explicit requires targetOperator A = 1 - 5*X.

The finite-sum recurrence aSum_recurrence is unconditional. The intermediate
original_recurrence_of_count_formula explicitly assumes CountFormula, but the
independent finite combinatorial proof count_formula closes that assumption.
The final a150500_recurrence has only n : Nat and the required 4 <= n hypothesis.
All names below are qualified: the path-coordinate function X and the power-series
variable PowerSeries.X coexist without changing their respective definitions. -/

#print axioms OEISOpen.A150500.y_sub_x_eq_pauses
#print axioms OEISOpen.A150500.legal_iff_projectedLegal
#print axioms OEISOpen.A150500.legal_erasePauses_iff
#print axioms OEISOpen.A150500.movingPathCount_eq_square
#print axioms OEISOpen.A150500.pathCount_zero
#print axioms OEISOpen.A150500.pathCount_one
#print axioms OEISOpen.A150500.pathCount_two
#print axioms OEISOpen.A150500.pathCount_three
#print axioms OEISOpen.A150500.central_square_recurrence
#print axioms OEISOpen.A150500.centralSquareSeries_differential_equation
#print axioms OEISOpen.A150500.pullback_second
#print axioms OEISOpen.A150500.pullback_first
#print axioms OEISOpen.A150500.pullback_zero
#print axioms OEISOpen.A150500.pullback_constant
#print axioms OEISOpen.A150500.localized_combined
#print axioms OEISOpen.A150500.shiftedOperator_bridge
#print axioms OEISOpen.A150500.shifted_gauge_subst_operator
#print axioms OEISOpen.A150500.target_of_generating_function
#print axioms OEISOpen.A150500.coeff_targetOperator_shifted
#print axioms OEISOpen.A150500.recurrence_of_target_shifted
#print axioms OEISOpen.A150500.recurrence_of_target_explicit
#print axioms OEISOpen.A150500.r3_recurrence_iff_r4_of_values
#print axioms OEISOpen.A150500.aSumSeries_bridge
#print axioms OEISOpen.A150500.aSum_recurrence
#print axioms OEISOpen.A150500.original_recurrence_of_count_formula
#print axioms OEISOpen.A150500.original_initial_values
#print axioms OEISOpen.A150500.meanderCount_eq_choose
#print axioms OEISOpen.A150500.movingPathCount_eq_choose_square
#print axioms OEISOpen.A150500.sum_subsets_by_card
#print axioms OEISOpen.A150500.insertionEquiv
#print axioms OEISOpen.A150500.pathCount_eq_sum_moving
#print axioms OEISOpen.A150500.pathCount_eq_aSum
#print axioms OEISOpen.A150500.count_formula
#print axioms OEISOpen.A150500.walk_generating_function
#print axioms OEISOpen.A150500.original_recurrence
#print axioms OEISOpen.A150500.a150500_recurrence

-- Print the types as well, so the remaining hypotheses are visible in the log.
#check OEISOpen.A150500.target_of_generating_function
#check OEISOpen.A150500.recurrence_of_target_explicit
#check OEISOpen.A150500.r3_recurrence_iff_r4_of_values
#check OEISOpen.A150500.original_recurrence_of_count_formula

-- The full printed final declaration exposes its exact domain and all five terms.
#print OEISOpen.A150500.a150500_recurrence
