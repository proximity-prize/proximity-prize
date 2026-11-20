import Mathlib.Algebra.MvPolynomial.CommRing
import ProximityPrize.SubmissionLower.Koala6844VirtualHighWitness
import Mathlib.Algebra.Polynomial.Taylor



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial

variable {K E : Type*} [Field K] [Field E]

theorem eval₂_ne_zero_of_coprime_root (a d : Polynomial K) (cop : IsCoprime a d)
    (embed : K →+* E) (ζ : E) (root : d.eval₂ embed ζ = 0) :
    a.eval₂ embed ζ ≠ 0 := by
  obtain ⟨u,v,bezout⟩ := cop
  intro hz
  have h : (u*a + v*d).eval₂ embed ζ = 1 := by rw [bezout, eval₂_one]
  simp only [eval₂_add, eval₂_mul, root, hz, mul_zero, add_zero] at h
  exact zero_ne_one h

theorem coeff_virtualEquation (A : Fin 2 → Polynomial K) (B : Polynomial K)
    (z : Fin 3) (n : ℕ) :
    (virtualEquation A B z).coeff n =
      (MvPolynomial.C ((A 0).coeff n) +
        MvPolynomial.X z * MvPolynomial.C ((A 1).coeff n)) * MvPolynomial.X 0 -
        MvPolynomial.X z * MvPolynomial.C (B.coeff n) := by
  have lift_coeff (p : Polynomial K) : (liftPolynomial p).coeff n = MvPolynomial.C (p.coeff n) := by
    change (p.map MvPolynomial.C).coeff n = _
    exact Polynomial.coeff_map _ _
  simp only [virtualEquation, coordinatePolynomial, coeff_sub, coeff_mul_C,
    coeff_add, coeff_C_mul, lift_coeff]

theorem degreeOf_virtualEquation_coeff_le (A : Fin 2 → Polynomial K) (B : Polynomial K)
    (z : Fin 3) (hz : z ≠ 0) (n : ℕ) (i : Fin 3) :
    ((virtualEquation A B z).coeff n).degreeOf i ≤ if i = 0 ∨ i = z then 1 else 0 := by
  classical
  rw [coeff_virtualEquation]
  let a0 := MvPolynomial.C ((A 0).coeff n) (σ := Fin 3)
  let a1 := MvPolynomial.C ((A 1).coeff n) (σ := Fin 3)
  let b := MvPolynomial.C (B.coeff n) (σ := Fin 3)
  have hseed : (MvPolynomial.X z * a1).degreeOf i ≤ if i = z then 1 else 0 := by
    simpa only [a1, MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X, add_zero] using
      MvPolynomial.degreeOf_mul_le i (MvPolynomial.X z) a1
  have hm : (a0 + MvPolynomial.X z * a1).degreeOf i ≤ if i = z then 1 else 0 := by
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    apply max_le
    · simp [a0]
    · exact hseed
  have hval : ((a0 + MvPolynomial.X z * a1) * MvPolynomial.X 0).degreeOf i ≤
      (if i = z then 1 else 0) + (if i = 0 then 1 else 0) := by
    apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
    exact Nat.add_le_add hm (by simp [MvPolynomial.degreeOf_X])
  have hs : (MvPolynomial.X z * b).degreeOf i ≤ if i = z then 1 else 0 := by
    simpa only [b, MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X, add_zero] using
      MvPolynomial.degreeOf_mul_le i (MvPolynomial.X z) b
  change (((a0 + MvPolynomial.X z * a1) * MvPolynomial.X 0) -
    MvPolynomial.X z * b).degreeOf i ≤ _
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  apply max_le
  · refine hval.trans ?_
    by_cases h0 : i = 0
    · subst i
      simp [Ne.symm hz]
    · by_cases h1 : i = z
      · subst i
        simp [hz]
      · simp [h0, h1]
  · by_cases h1 : i = z
    · exact hs.trans (by simp [h1])
    · exact hs.trans (by simp [h1])

theorem virtualEquation_coeff_zero_ne
    (A : Fin 2 → Polynomial K) (B : Polynomial K) (z : Fin 3) (hz : z ≠ 0)
    (hA : (A 0).coeff 0 ≠ 0) :
    (virtualEquation A B z).coeff 0 ≠ 0 := by
  intro hzero
  rw [coeff_virtualEquation] at hzero
  let u : Fin 3 → K := fun i => if i = 0 then 1 else 0
  have he := congrArg (MvPolynomial.eval u) hzero
  simp [u, hz] at he
  exact hA he

theorem taylor_virtualEquation (x : K)
    (A : Fin 2 → Polynomial K) (B : Polynomial K) (z : Fin 3) :
    Polynomial.taylor (MvPolynomial.C x) (virtualEquation A B z) =
      virtualEquation (fun j => Polynomial.taylor x (A j)) (Polynomial.taylor x B) z := by
  have h (P : Polynomial K) :
      Polynomial.taylor (MvPolynomial.C x) (liftPolynomial P) =
        liftPolynomial (Polynomial.taylor x P) := by
    rw [Polynomial.taylor_apply, Polynomial.taylor_apply]
    simp [liftPolynomial, Polynomial.map_comp]
  simp only [virtualEquation, map_sub, map_add, Polynomial.taylor_mul, h,
    coordinatePolynomial, Polynomial.taylor_C]

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
