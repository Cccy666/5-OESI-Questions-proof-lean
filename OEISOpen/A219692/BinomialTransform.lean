import OEISOpen.A219692.Definitions
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
Reusable exact nodes for the still unfinished formal Bridge proof.
These are general identities, not numerical instances. This module does not
assert P1, P, B1, or Bridge; their remaining obligations are listed in
`formal/bridge_obligations.md`.
-/
namespace OEISOpen.A219692

/-- The final binomial rearrangement in Bridge, on its exact support. -/
theorem bridge_binomial_product (n k : ℕ) (hk : 3*k ≤ n) :
    (n-k).choose k * (n-2*k).choose (n-3*k) =
      (n-k).choose (2*k) * (2*k).choose k := by
  rw [show n-3*k = (n-2*k)-k by omega, Nat.choose_symm (by omega : k ≤ n-2*k)]
  have h := (Nat.choose_mul (n := n-k) (k := 2*k) (s := k) (by omega)).symm
  simpa only [show n-k-k = n-2*k by omega, show 2*k-k = k by omega] using h

/-- The P1 summand is a trinomial coefficient after removing choose(n,k). -/
theorem p1_summand_rearrangement (n k ell : ℕ) (hk : k ≤ ell) (hell : 2*ell ≤ n) :
    n.choose (2*ell) * (2*ell).choose ell * ell.choose k =
      n.choose k * (n-k).choose (ell-k) * (n-ell).choose (n-2*ell) := by
  have h1 := Nat.choose_mul (n := n) (k := 2*ell) (s := ell) (by omega)
  have h2 := Nat.choose_mul (n := n) (k := ell) (s := k) hk
  have hs : (n-ell).choose (n-2*ell) = (n-ell).choose ell := by
    simpa only [show n-ell-ell = n-2*ell by omega] using
      (Nat.choose_symm (n := n-ell) (k := ell) (by omega))
  rw [show 2*ell-ell = ell by omega] at h1
  rw [h1, hs]
  calc
    _ = (n.choose ell * ell.choose k) * (n-ell).choose ell := by ring
    _ = _ := by rw [h2]

/-- The closed coefficient evaluation used in the trinomial proof of P1. -/
theorem trinomial_coefficient_closed (n k : ℕ) (hk : 2*k ≤ n) :
    ((1 + 2*Polynomial.X + Polynomial.X^2 : Polynomial ℚ)^(n-k)).coeff (n-2*k) =
      ((2*n-2*k).choose n : ℚ) := by
  have h : (1 + 2*Polynomial.X + Polynomial.X^2 : Polynomial ℚ) =
      (1+Polynomial.X)^2 := by ring
  rw [h, ← pow_mul, Polynomial.coeff_one_add_X_pow]
  have he : 2*(n-k) = 2*n-2*k := by omega
  rw [he]
  have hs : (2*n-2*k).choose (n-2*k) = (2*n-2*k).choose n := by
    have hh := Nat.choose_symm (n := 2*n-2*k) (k := n) (by omega)
    simpa only [show 2*n-2*k-n = n-2*k by omega] using hh
  rw [hs]

/-- Exponent map for x=p*q, y=p/q. It is injective, and need not be surjective. -/
def exponentRotation : (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun a := (a.1+a.2, a.1-a.2)
  map_zero' := by simp
  map_add' a b := by ext <;> simp <;> ring

theorem exponentRotation_injective : Function.Injective exponentRotation := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp [exponentRotation] at h1 h2
  apply Prod.ext <;> omega

/-- Constant coefficient is unchanged by the Laurent exponent substitution. -/
theorem constant_coefficient_rotation {R : Type*} [Semiring R]
    (f : AddMonoidAlgebra R (ℤ × ℤ)) :
    (AddMonoidAlgebra.mapDomain exponentRotation f).coeff (0,0) = f.coeff (0,0) := by
  change Finsupp.mapDomain exponentRotation f.coeff (exponentRotation (0,0)) = _
  exact Finsupp.mapDomain_apply exponentRotation_injective f.coeff (0,0)

end OEISOpen.A219692
