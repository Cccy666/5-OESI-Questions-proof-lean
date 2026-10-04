import OEISOpen.A150500.Pullback
import OEISOpen.A150500.LocalizedCertificate
import OEISOpen.A150500.Hypergeometric
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OEISOpen.A150500
open PowerSeries

noncomputable def geom : Series := (1-X)⁻¹
noncomputable def rho : Series := X^2*geom^2
noncomputable def gauge : Series := (1+3*X)*geom
noncomputable def multiplier : Series := 4*X^2*(1+3*X)^2*geom^2
noncomputable def hypergeomOperator (F : Series) : Series :=
  X*(1-16*X)*D (D F)+(1-32*X)*D F-4*F

theorem geom_unit : (1-X)*geom = (1:Series) := by
  apply PowerSeries.mul_inv_cancel
  simp

theorem deriv_geom : D geom = geom^2 := by
  simp [D, geom]

private theorem d2 : D (2:Series) = 0 := Derivation.map_natCast _ 2
private theorem d3 : D (3:Series) = 0 := Derivation.map_natCast _ 3

theorem deriv_gauge : D gauge = 3*geom+(1+3*X)*geom^2 := by
  simp [gauge, D, Derivation.leibniz, show PowerSeries.derivative ℚ (3:Series)=0 from d3,
    show PowerSeries.derivative ℚ geom=geom^2 from deriv_geom]
  ring

theorem deriv2_gauge : D (D gauge) = 6*geom^2+2*(1+3*X)*geom^3 := by
  rw [deriv_gauge]
  simp [D, Derivation.leibniz,
    show PowerSeries.derivative ℚ (3:Series)=0 from d3,
    show PowerSeries.derivative ℚ geom=geom^2 from deriv_geom]
  ring

theorem deriv_rho : D rho = 2*X*geom^2+2*X^2*geom^3 := by
  simp [rho, D, Derivation.leibniz,
    show PowerSeries.derivative ℚ geom=geom^2 from deriv_geom]
  ring

theorem deriv2_rho : D (D rho) = 2*geom^2+8*X*geom^3+6*X^2*geom^4 := by
  rw [deriv_rho]
  simp [D, Derivation.leibniz,
    show PowerSeries.derivative ℚ (2:Series)=0 from d2,
    show PowerSeries.derivative ℚ geom=geom^2 from deriv_geom]
  ring

theorem rho_hasSubst : HasSubst rho := by
  apply HasSubst.of_constantCoeff_zero'
  simp [rho]

theorem derivative_subst_rho (F : Series) :
    D (F.subst rho) = (D F).subst rho * D rho :=
  PowerSeries.derivative_subst rho_hasSubst

theorem derivative2_subst_rho (F : Series) :
    D (D (F.subst rho)) =
      (D (D F)).subst rho*(D rho)^2 + (D F).subst rho*D (D rho) := by
  rw [derivative_subst_rho]
  simp only [D, Derivation.leibniz, smul_eq_mul]
  rw [PowerSeries.derivative_subst rho_hasSubst]
  ring

theorem shifted_gauge_subst (F : Series) :
    shiftedOperator (gauge*F.subst rho) =
      multiplier * (rho*(1-16*rho)*(D (D F)).subst rho +
        (1-32*rho)*(D F).subst rho-4*F.subst rho) := by
  have hp : D (gauge*F.subst rho) =
      D gauge*F.subst rho+gauge*D (F.subst rho) := by
    simp only [D, Derivation.leibniz, smul_eq_mul]
    ring
  have hpp : D (D (gauge*F.subst rho)) = D (D gauge)*F.subst rho +
      2*D gauge*D (F.subst rho)+gauge*D (D (F.subst rho)) := by
    rw [hp]
    simp only [D, map_add, Derivation.leibniz, smul_eq_mul]
    ring
  unfold shiftedOperator
  rw [hpp, hp, derivative2_subst_rho, derivative_subst_rho,
    deriv2_gauge, deriv_gauge, deriv2_rho, deriv_rho]
  have hc := localized_combined (X:Series) geom (F.subst rho)
    ((D F).subst rho) ((D (D F)).subst rho) geom_unit
  convert hc using 1 <;>
    simp only [multiplier, rho, gauge, shiftDelta, shiftGamma, delta, alpha, beta, gamma] <;> ring

theorem subst_hypergeomOperator (F : Series) :
    (hypergeomOperator F).subst rho =
      rho*(1-16*rho)*(D (D F)).subst rho +
        (1-32*rho)*(D F).subst rho-4*F.subst rho := by
  let φ : Series →ₐ[ℚ] Series := substAlgHom rho_hasSubst
  have heq (P : Series) : P.subst rho = φ P :=
    (congrFun (coe_substAlgHom rho_hasSubst) P).symm
  have hx : φ PowerSeries.X = rho := substAlgHom_X rho_hasSubst
  simp only [heq, hypergeomOperator, map_add, map_sub, map_mul, map_one, map_ofNat, hx]

theorem shifted_gauge_subst_operator (F : Series) :
    shiftedOperator (gauge*F.subst rho) =
      multiplier*(hypergeomOperator F).subst rho := by
  rw [shifted_gauge_subst, subst_hypergeomOperator]

theorem hypergeom_centralSquare : hypergeomOperator centralSquareSeries = 0 := by
  have h := centralSquareSeries_differential_equation
  norm_num only [map_ofNat] at h
  exact h

/-- A real formal-series implication. The remaining counting bridge is explicit
in hA; this theorem does not assert that an arbitrary series is a walk series. -/
theorem target_of_generating_function (A : Series)
    (hA : 1+4*X*A = gauge*centralSquareSeries.subst rho) :
    targetOperator A = 1-5*X := by
  apply target_of_shifted
  rw [hA, shifted_gauge_subst_operator, hypergeom_centralSquare]
  have hz : (0:Series).subst rho = 0 := by
    simpa only [coe_substAlgHom] using (map_zero (substAlgHom (R:=ℚ) rho_hasSubst))
  rw [hz, mul_zero]

end OEISOpen.A150500
