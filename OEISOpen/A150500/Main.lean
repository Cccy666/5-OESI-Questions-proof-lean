import OEISOpen.A150500.Paths
import OEISOpen.A150500.SeriesPullback
import OEISOpen.A150500.SumRecurrence
import OEISOpen.A150500.Counting

/-! Exact original-path target and its complete proof.
The original path count is never replaced by a recursively defined sequence.
The intermediate implications expose the proof structure; count_formula closes
the original combinatorial bridge before the final recurrence is deduced.
-/
namespace OEISOpen.A150500

noncomputable def walkSeries : Series := PowerSeries.mk fun n => (pathCount n : ℚ)

@[simp] theorem coeff_walkSeries (n : ℕ) :
    PowerSeries.coeff n walkSeries = (pathCount n : ℚ) := PowerSeries.coeff_mk _ _

/-- The original target, with all polynomial subtractions in Z. -/
def OriginalRecurrence : Prop := ∀ n : ℕ, 4 ≤ n →
  ((n:ℤ)+1)^2*(pathCount n:ℤ) - (9*(n:ℤ)+4)*(pathCount (n-1):ℤ) +
    (-22*(n:ℤ)^2+27*(n:ℤ)+15)*(pathCount (n-2):ℤ) -
    3*((n:ℤ)-2)*(8*(n:ℤ)-31)*(pathCount (n-3):ℤ) +
    45*((n:ℤ)-2)*((n:ℤ)-3)*(pathCount (n-4):ℤ) = 0

/-- The counting-to-series bridge, proved below from finite cardinalities. -/
def WalkGeneratingFunction : Prop :=
  1+4*PowerSeries.X*walkSeries = gauge*centralSquareSeries.subst rho

/-- The counting identity, stated with the auxiliary sum in Q. -/
def CountFormula : Prop := ∀ n : ℕ, (pathCount n : ℚ) = aSum n

theorem walkSeries_eq_aSumSeries (h : CountFormula) : walkSeries = aSumSeries := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_walkSeries, aSumSeries, PowerSeries.coeff_mk]
  exact h n

theorem generating_function_of_count_formula (h : CountFormula) : WalkGeneratingFunction := by
  unfold WalkGeneratingFunction
  rw [walkSeries_eq_aSumSeries h]
  simpa only [gauge, rho, geom, geometricSeries_eq_inverse] using aSumSeries_bridge

theorem original_recurrence_of_generating_function
    (h : WalkGeneratingFunction) : OriginalRecurrence := by
  intro n hn
  have he := recurrence_of_target_explicit walkSeries
    (target_of_generating_function walkSeries h) n hn
  simp only [coeff_walkSeries] at he
  exact_mod_cast he

theorem original_recurrence_of_count_formula (h : CountFormula) : OriginalRecurrence :=
  original_recurrence_of_generating_function (generating_function_of_count_formula h)

theorem original_initial_values :
    pathCount 0 = 1 ∧ pathCount 1 = 2 ∧ pathCount 2 = 7 ∧ pathCount 3 = 25 :=
  ⟨pathCount_zero, pathCount_one, pathCount_two, pathCount_three⟩

theorem count_formula : CountFormula := pathCount_eq_aSum

theorem walk_generating_function : WalkGeneratingFunction :=
  generating_function_of_count_formula count_formula

theorem original_recurrence : OriginalRecurrence :=
  original_recurrence_of_count_formula count_formula

/-- The A150500 fourth-order recurrence for the original prefix-constrained
three-dimensional walks, with integer polynomial arithmetic and the exact n>=4
domain. There is no auxiliary hypothesis in this final theorem. -/
theorem a150500_recurrence (n : ℕ) (hn : 4 ≤ n) :
  ((n:ℤ)+1)^2*(pathCount n:ℤ) - (9*(n:ℤ)+4)*(pathCount (n-1):ℤ) +
    (-22*(n:ℤ)^2+27*(n:ℤ)+15)*(pathCount (n-2):ℤ) -
    3*((n:ℤ)-2)*(8*(n:ℤ)-31)*(pathCount (n-3):ℤ) +
    45*((n:ℤ)-2)*((n:ℤ)-3)*(pathCount (n-4):ℤ) = 0 :=
  original_recurrence n hn

end OEISOpen.A150500
