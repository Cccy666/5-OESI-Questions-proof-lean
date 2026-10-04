import OEISOpen.A219692.LaurentCentral

/-! Assembly of the general binomial transformation using finite Laurent polynomials. -/
namespace OEISOpen.A219692

open Finset LaurentPolynomial

noncomputable section

def laurentCT {R : Type*} [CommRing R] (f : LaurentPolynomial R) : R := f.coeff 0

@[simp] theorem laurentCT_add {R : Type*} [CommRing R] (f g : LaurentPolynomial R) :
    laurentCT (f+g) = laurentCT f + laurentCT g := by simp [laurentCT]

@[simp] theorem laurentCT_sum {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (f : ι → LaurentPolynomial R) :
    laurentCT (∑ i ∈ s, f i) = ∑ i ∈ s, laurentCT (f i) := by simp [laurentCT]

@[simp] theorem laurentCT_C {R : Type*} [CommRing R] (a : R) :
    laurentCT (C a) = a := by simp [laurentCT]

@[simp] theorem laurentCT_C_mul {R : Type*} [CommRing R] (a : R) (f : LaurentPolynomial R) :
    laurentCT (C a*f) = a*laurentCT f := by
  exact AddMonoidAlgebra.coeff_single_zero_mul f a 0

@[simp] theorem laurentCT_mul_C {R : Type*} [CommRing R] (f : LaurentPolynomial R) (a : R) :
    laurentCT (f*C a) = laurentCT f*a := by
  exact AddMonoidAlgebra.coeff_mul_single_zero f a 0

@[simp] theorem laurentCT_mul_natCast {R : Type*} [CommRing R]
    (f : LaurentPolynomial R) (a : ℕ) :
    laurentCT (f*(a : LaurentPolynomial R)) = laurentCT f*(a : R) := by
  rw [show (a : LaurentPolynomial R) = C (a : R) by simp, laurentCT_mul_C]

def centralKernel {R : Type*} [CommRing R] : LaurentPolynomial R := 2+T 1+T (-1)

@[simp] theorem laurentCT_centralKernel_pow {R : Type*} [CommRing R] (n : ℕ) :
    laurentCT ((centralKernel : LaurentPolynomial R)^n) = ((2*n).choose n : R) :=
  laurent_ct_central n

def separatedKernel {R : Type*} [CommRing R] (A B : R) :
    LaurentPolynomial (LaurentPolynomial R) :=
  C (C A)*centralKernel + C (C B*centralKernel)

theorem separatedKernel_ct {R : Type*} [CommRing R] (n : ℕ) (A B : R) :
    laurentCT (laurentCT ((separatedKernel A B)^n)) =
      ∑ j ∈ range (n+1),
        (n.choose j : R) * ((2*j).choose j : R) *
          ((2*(n-j)).choose (n-j) : R) * A^(n-j) * B^j := by
  rw [separatedKernel, add_comm, add_pow, laurentCT_sum, laurentCT_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hn :
      (C (C B*centralKernel) : LaurentPolynomial (LaurentPolynomial R))^j *
          (C (C A)*centralKernel)^(n-j) * (n.choose j : LaurentPolynomial (LaurentPolynomial R)) =
      C (C ((n.choose j : R)*A^(n-j)*B^j)*(centralKernel : LaurentPolynomial R)^j) *
        (centralKernel : LaurentPolynomial (LaurentPolynomial R))^(n-j) := by
    simp only [map_mul, map_pow, map_natCast, mul_pow]
    ring
  rw [hn, laurentCT_C_mul, laurentCT_centralKernel_pow, laurentCT_mul_natCast,
    laurentCT_C_mul, laurentCT_centralKernel_pow]
  ring

def flatKernel {R : Type*} [CommRing R] (A B : R) : AddMonoidAlgebra R (ℤ × ℤ) :=
  AddMonoidAlgebra.single (0,0) (2*(A+B)) +
    AddMonoidAlgebra.single (1,0) A + AddMonoidAlgebra.single (-1,0) A +
    AddMonoidAlgebra.single (0,1) B + AddMonoidAlgebra.single (0,-1) B

def rotatedKernel {R : Type*} [CommRing R] (A B : R) :
    LaurentPolynomial (LaurentPolynomial R) :=
  C (C (2*(A+B))) +
    C (C A*T 1+C B*T (-1))*T 1 +
    C (C A*T (-1)+C B*T 1)*T (-1)

theorem ct_curry {R : Type*} [CommRing R] (f : AddMonoidAlgebra R (ℤ × ℤ)) :
    laurentCT (laurentCT (AddMonoidAlgebra.curryRingEquiv f)) = f.coeff (0,0) := by
  rfl

theorem curry_flatKernel {R : Type*} [CommRing R] (A B : R) :
    AddMonoidAlgebra.curryRingEquiv (flatKernel A B) = separatedKernel A B := by
  simp only [flatKernel, map_add, AddMonoidAlgebra.curryRingEquiv_single]
  simp only [separatedKernel, centralKernel, mul_add, add_mul, map_add, map_mul, map_ofNat]
  simp only [C, T, AddMonoidAlgebra.single_mul_single]
  have hC2 : C (C (2 : R)) = (2 : LaurentPolynomial (LaurentPolynomial R)) := by
    rw [show (2 : R) = 1+1 by ring, map_add, map_one, map_add, map_one]
    ring
  simp [hC2] <;> ring

theorem curry_rotatedKernel {R : Type*} [CommRing R] (A B : R) :
    AddMonoidAlgebra.curryRingEquiv
      (AddMonoidAlgebra.mapDomainRingHom R exponentRotation (flatKernel A B)) = rotatedKernel A B := by
  simp only [flatKernel, map_add, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.curryRingEquiv_single]
  simp only [exponentRotation, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  norm_num
  simp only [rotatedKernel, map_add, C, T, AddMonoidAlgebra.single_mul_single]
  simp <;> ring

theorem rotatedKernel_ct_eq_separated {R : Type*} [CommRing R] (n : ℕ) (A B : R) :
    laurentCT (laurentCT ((rotatedKernel A B)^n)) =
      laurentCT (laurentCT ((separatedKernel A B)^n)) := by
  have hL : (rotatedKernel A B)^n = AddMonoidAlgebra.curryRingEquiv
      (AddMonoidAlgebra.mapDomainRingHom R exponentRotation ((flatKernel A B)^n)) := by
    rw [map_pow, map_pow, curry_rotatedKernel]
  have hR : (separatedKernel A B)^n =
      AddMonoidAlgebra.curryRingEquiv ((flatKernel A B)^n) := by
    rw [map_pow, curry_flatKernel]
  rw [hL, hR, ct_curry, ct_curry]
  exact constant_coefficient_rotation ((flatKernel A B)^n)

theorem mixed_laurent_product {R : Type*} [CommRing R] (A B : R) :
    (C A*T 1+C B*T (-1) : LaurentPolynomial R) * (C A*T (-1)+C B*T 1) =
      C ((A+B)^2) + C (A*B)*(T 1-T (-1))^2 := by
  have hunit : (T 1*T (-1) : LaurentPolynomial R) = 1 := by
    rw [← T_add]
    norm_num
  simp only [map_pow, map_add, map_mul]
  linear_combination (C A+C B)^2*hunit

end

end OEISOpen.A219692
