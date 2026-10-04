import OEISOpen.A150500.Certificates

/-! A certificate in a commutative ring with a specified inverse of 1-t.
The witness may be (1-X)⁻¹ in power series. There is no inverse of t.
The displayed multipliers certify ideal membership; `linear_combination`
reduces every assertion to a ring identity checked by Lean. -/
namespace OEISOpen.A150500
variable {R : Type*} [CommRing R]

def shiftDelta (t : R) : R := 1-9*t-39*t^2+21*t^3+90*t^4
def shiftGamma (t : R) : R := -4*t+20*t^2

theorem localized_second (t w : R) (h : (1-t)*w = 1) :
    alpha t*t^2*((1+3*t)*w)*(2*t*w^2+2*t^2*w^3)^2 =
    (4*t^2*(1+3*t)^2*w^2)*(t^2*w^2)*(1-16*(t^2*w^2)) := by
  unfold alpha
  linear_combination
    (-4*t^4*w^4*(3*t+1)^2 *
      (15*t^4*w^2+2*t^3*w^2+15*t^3*w-t^2*w^2-13*t^2*w-2*t*w-1))*h

theorem localized_first (t w : R) (h : (1-t)*w = 1) :
    alpha t*t^2*(2*(3*w+(1+3*t)*w^2)*(2*t*w^2+2*t^2*w^3) +
      ((1+3*t)*w)*(2*w^2+8*t*w^3+6*t^2*w^4)) +
      shiftDelta t*t*((1+3*t)*w)*(2*t*w^2+2*t^2*w^3) =
    (4*t^2*(1+3*t)^2*w^2)*(1-32*(t^2*w^2)) := by
  unfold alpha shiftDelta
  linear_combination
    (-2*t^2*w^2*(3*t+1)^2 *
      (75*t^4*w^2+10*t^3*w^2+75*t^3*w-5*t^2*w^2-52*t^2*w-7*t*w-2))*h

theorem localized_zero (t w : R) (h : (1-t)*w = 1) :
    alpha t*t^2*(6*w^2+2*(1+3*t)*w^3) +
      shiftDelta t*t*(3*w+(1+3*t)*w^2) + shiftGamma t*((1+3*t)*w) =
    -4*(4*t^2*(1+3*t)^2*w^2) := by
  unfold alpha shiftDelta shiftGamma
  linear_combination
    (-t*w*(3*t+1)^2*(30*t^3*w+4*t^2*w+30*t^2-2*t*w-13*t-1))*h

theorem localized_combined (t w f f1 f2 : R) (h : (1-t)*w = 1) :
    alpha t*t^2 * ((6*w^2+2*(1+3*t)*w^3)*f +
      2*(3*w+(1+3*t)*w^2)*f1*(2*t*w^2+2*t^2*w^3) +
      ((1+3*t)*w)*(f2*(2*t*w^2+2*t^2*w^3)^2 +
        f1*(2*w^2+8*t*w^3+6*t^2*w^4))) +
    shiftDelta t*t*((3*w+(1+3*t)*w^2)*f +
      ((1+3*t)*w)*f1*(2*t*w^2+2*t^2*w^3)) +
    shiftGamma t*((1+3*t)*w*f) =
    (4*t^2*(1+3*t)^2*w^2)*
      ((t^2*w^2)*(1-16*(t^2*w^2))*f2+(1-32*(t^2*w^2))*f1-4*f) := by
  linear_combination f2*localized_second t w h + f1*localized_first t w h +
    f*localized_zero t w h

end OEISOpen.A150500
