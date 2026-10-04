import OEISOpen.A150500.Certificates
import Mathlib.RingTheory.PowerSeries.Derivative

/-! The non-Laurent operator transformation in rational formal power series.
No inverse of X is used. -/
namespace OEISOpen.A150500
open PowerSeries

abbrev Series := PowerSeries ℚ
noncomputable abbrev D : Series → Series := PowerSeries.derivative ℚ

noncomputable def targetOperator (A : Series) : Series :=
  alpha X * X^2 * D (D A) + delta X * X * D A + gamma X * A

noncomputable def shiftedOperator (Q : Series) : Series :=
  alpha X * X^2 * D (D Q) + (delta X - 2*alpha X)*X*D Q +
    (alpha X - beta X + gamma X)*Q

theorem shiftedOperator_one : shiftedOperator 1 = (-4:Series)*X+20*X^2 := by
  simp [shiftedOperator, D, alpha, beta, gamma]
  ring

theorem shiftedOperator_X_mul (A : Series) :
    shiftedOperator (X*A) = X*targetOperator A := by
  simp [shiftedOperator, targetOperator, D, Derivation.leibniz, alpha, beta, gamma, delta]
  ring

theorem shiftedOperator_bridge (A : Series) :
    shiftedOperator (1+4*X*A) = 4*X*(targetOperator A-(1-5*X)) := by
  have h4 : PowerSeries.derivative ℚ (4:Series) = 0 :=
    Derivation.map_natCast _ 4
  simp [shiftedOperator, targetOperator, D, Derivation.leibniz, h4,
    alpha, beta, gamma, delta]
  ring

theorem target_of_shifted (A : Series)
    (h : shiftedOperator (1+4*X*A) = 0) : targetOperator A = 1-5*X := by
  rw [shiftedOperator_bridge] at h
  have hx : (X : Series) ≠ 0 := X_ne_zero
  have hfour : (4 : Series) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff : Series →+* ℚ) h
    change (4:ℚ) = 0 at hc
    norm_num at hc
  have hz : targetOperator A-(1-5*X) = 0 :=
    (mul_eq_zero.mp h).resolve_left (mul_ne_zero hfour hx)
  exact sub_eq_zero.mp hz

end OEISOpen.A150500
