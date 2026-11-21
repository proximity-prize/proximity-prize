import ProximityPrize.SubmissionLower.Fast063

set_option Elab.async false
set_option maxHeartbeats 650000

namespace Shared50OrderDivision

noncomputable section

open K1_13_6_1_2 (VanishesTo hassePartial multiOrder taylorHom taylor_coeff)
open K1_13_6_1_2_2 (vanishesTo_of_hasse)
open scoped Polynomial BigOperators

private def gradedLine {n : ℕ} {B : Type*} [CommRing B] :
    MvPolynomial (Fin n) B →+* (MvPolynomial (Fin n) B)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)

private theorem gradedLine_monomial {n : ℕ} {B : Type*} [CommRing B]
    (a : Fin n →₀ ℕ) (b : B) :
    gradedLine (MvPolynomial.monomial a b) =
      Polynomial.monomial (multiOrder a) (MvPolynomial.monomial a b) := by
  classical
  rw [gradedLine, MvPolynomial.eval₂Hom_monomial]
  change Polynomial.C (MvPolynomial.C b) *
    (∏ i ∈ a.support, (Polynomial.C (MvPolynomial.X i) * Polynomial.X) ^ a i) = _
  simp_rw [mul_pow, ← map_pow Polynomial.C]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
    MvPolynomial.prod_X_pow_eq_monomial, ← mul_assoc, ← map_mul,
    MvPolynomial.C_mul_monomial, mul_one]
  exact Polynomial.C_mul_X_pow_eq_monomial

private theorem gradedLine_coeff {n : ℕ} {B : Type*} [CommRing B]
    (F : MvPolynomial (Fin n) B) (j : ℕ) (a : Fin n →₀ ℕ) :
    ((gradedLine F).coeff j).coeff a = if multiOrder a = j then F.coeff a else 0 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum F, map_sum, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
  simp only [gradedLine_monomial, Polynomial.coeff_monomial]
  by_cases ha : a ∈ F.support
  · rw [Finset.sum_eq_single_of_mem a ha]
    · split_ifs <;> simp
    · intro b _ hb
      split_ifs <;> simp [MvPolynomial.coeff_monomial, hb]
  · rw [MvPolynomial.notMem_support_iff.mp ha, ite_self]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : b ≠ a := fun he => ha (he ▸ hb)
    split_ifs <;> simp [MvPolynomial.coeff_monomial, hne]

variable {n : ℕ} {K : Type*} [Field K]

local notation "Jet" => MvPolynomial (Fin n) K
private abbrev Direction (P : Ideal (Jet)) := MvPolynomial (Fin n) (Jet ⧸ P)

/-- Expand at the residue-field point with independent symbolic directions.
The coefficient of T^d records every Hasse coefficient of total order d. -/
@[irreducible] private def expansion (P : Ideal (Jet)) : Jet →+* (Direction P)[X] :=
  gradedLine.comp ((MvPolynomial.map (Ideal.Quotient.mk P)).comp taylorHom)

private theorem expansion_coeff (P : Ideal (Jet)) (F : Jet) (j : ℕ)
    (a : Fin n →₀ ℕ) : ((expansion P F).coeff j).coeff a =
      if multiOrder a = j then Ideal.Quotient.mk P (hassePartial a F) else 0 := by
  unfold expansion
  rw [RingHom.comp_apply, RingHom.comp_apply, gradedLine_coeff, MvPolynomial.coeff_map, taylor_coeff]

private theorem hasse_zero (F : Jet) : hassePartial 0 F = F := by
  unfold hassePartial
  simp only [tsub_zero, Finsupp.zero_apply, Nat.choose_zero_right, Nat.cast_one,
    Finset.prod_const_one, mul_one]
  exact (MvPolynomial.as_sum F).symm

private theorem multiOrder_zero_iff (a : Fin n →₀ ℕ) : multiOrder a = 0 ↔ a = 0 := by
  rw [multiOrder, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  constructor
  · intro h
    ext i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h i (Finset.mem_univ i)
  · rintro rfl
    simp

private theorem constant_expansion (P : Ideal (Jet)) (F : Jet) :
    (expansion P F).coeff 0 = MvPolynomial.C (Ideal.Quotient.mk P F) := by
  classical
  ext a
  simp only [expansion_coeff, multiOrder_zero_iff]
  by_cases h : a = 0
  · simp [h, hasse_zero]
  · simp [h, Ne.symm h, MvPolynomial.coeff_C]

private theorem X_pow_dvd_of_mem_pow (P : Ideal (Jet)) {F : Jet} {d : ℕ}
    (hF : F ∈ P^d) : (Polynomial.X : (Direction P)[X])^d ∣ expansion P F := by
  let T : (Direction P)[X] := Polynomial.X
  have hp : P.map (expansion P) ≤ Ideal.span {T} := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    change expansion P f ∈ Ideal.span {T}
    apply Ideal.mem_span_singleton.mpr
    apply Polynomial.X_dvd_iff.mpr
    rw [constant_expansion, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  have h := Ideal.mem_map_of_mem (expansion P) hF
  rw [Ideal.map_pow] at h
  have hh := Ideal.pow_right_mono hp d h
  rw [Ideal.span_singleton_pow] at hh
  exact Ideal.mem_span_singleton.mp hh

private theorem le_trailing_iff_dvd {B : Type*} [CommRing B] {u : B[X]} (hu : u ≠ 0) (r : ℕ) :
    Polynomial.X ^ r ∣ u ↔ r ≤ u.natTrailingDegree := by
  rw [Polynomial.X_pow_dvd_iff]
  constructor
  · intro h
    by_contra! hbad
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hu (h _ hbad)
  · exact fun h i hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hi.trans_le h)

private theorem X_pow_cancel_of_const_ne_zero {B : Type*} [CommRing B] [IsDomain B]
    {u v : B[X]} {r : ℕ} (hu : u.coeff 0 ≠ 0) (h : Polynomial.X^r ∣ u*v) :
    Polynomial.X^r ∣ v := by
  by_cases hv : v = 0
  · rw [hv]; exact dvd_zero _
  have hu0 : u ≠ 0 := fun he => hu (he ▸ Polynomial.coeff_zero _)
  have ht : u.natTrailingDegree = 0 :=
    Nat.eq_zero_of_le_zero (Polynomial.natTrailingDegree_le_of_ne_zero hu)
  have hb := (le_trailing_iff_dvd (mul_ne_zero hu0 hv) r).mp h
  rw [Polynomial.natTrailingDegree_mul hu0 hv, ht, zero_add] at hb
  exact (le_trailing_iff_dvd hv _).mpr hb

private theorem clear_local_denominator {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime]
    {F : A} {r : ℕ} (h : VanishesTo P F r) : ∃ q ∉ P, q*F ∈ P^r := by
  let L := Localization.AtPrime P
  change algebraMap A L F ∈ IsLocalRing.maximalIdeal L ^ r at h
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P L, ← Ideal.map_pow,
    IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl L] at h
  exact h

private theorem X_pow_dvd_of_vanishesTo (P : Ideal Jet) [P.IsPrime]
    {F : Jet} {r : ℕ} (h : VanishesTo P F r) :
    (Polynomial.X : (Direction P)[X])^r ∣ expansion P F := by

  obtain ⟨q,hq,hqF⟩ := clear_local_denominator P h

  let E := expansion P
  have hdiv : (Polynomial.X : (Direction P)[X])^r ∣ E q * E F := by
    rw [← E.map_mul]
    exact X_pow_dvd_of_mem_pow P hqF

  have hc : (E q).coeff 0 ≠ 0 := by
    change (expansion P q).coeff 0 ≠ 0
    rw [constant_expansion, map_ne_zero_iff _ (MvPolynomial.C_injective _ _)]
    exact fun hz => hq (Ideal.Quotient.eq_zero_iff_mem.mp hz)

  exact @X_pow_cancel_of_const_ne_zero (Direction P) inferInstance inferInstance _ _ r hc hdiv

private theorem vanishesTo_of_X_pow_dvd [PerfectField K]
    (P : Ideal (Jet)) [P.IsPrime] {F : Jet} {r : ℕ}
    (h : (Polynomial.X : (Direction P)[X])^r ∣ expansion P F) : VanishesTo P F r := by
  apply vanishesTo_of_hasse F P r
  intro a ha
  have hz := (Polynomial.X_pow_dvd_iff.mp h) (multiOrder a) ha
  have hc := congrArg (fun f : Direction P => f.coeff a) hz
  rw [expansion_coeff, ite_eq_left rfl] at hc
  change Ideal.Quotient.mk P (hassePartial a F) = 0 at hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp hc

private theorem trailing_pow {B : Type*} [CommRing B] [IsDomain B] {u : B[X]} (hu : u ≠ 0) (k : ℕ) :
    (u^k).natTrailingDegree = k*u.natTrailingDegree := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero _ hu) hu, ih, Nat.succ_mul]

private theorem X_pow_dvd_of_pow_mul {B : Type*} [CommRing B] [IsDomain B]
    {u v : B[X]} {s k r : ℕ} (hu : ¬ Polynomial.X^(s+1) ∣ u)
    (h : Polynomial.X^r ∣ u^k*v) : Polynomial.X^(r-s*k) ∣ v := by
  by_cases hv : v = 0
  · rw [hv]; exact dvd_zero _
  have hu0 : u ≠ 0 := by
    intro hzero
    exact hu (hzero.symm ▸ dvd_zero _)
  have horder : u.natTrailingDegree ≤ s := by
    by_contra! hbad
    exact hu ((le_trailing_iff_dvd hu0 _).mpr hbad)
  have hb := (le_trailing_iff_dvd (mul_ne_zero (pow_ne_zero k hu0) hv) r).mp h
  rw [Polynomial.natTrailingDegree_mul (pow_ne_zero k hu0) hv, trailing_pow hu0 k] at hb
  have hbound := hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left k horder) _)
  apply (le_trailing_iff_dvd hv _).mpr
  rw [Nat.mul_comm s k]
  omega

/-- Dividing out an anchor power costs at most its exponent times the prescribed
upper bound on the anchor order. This applies to any prime of the jet ring. -/
theorem vanishesTo_of_pow_mul [PerfectField K] (P : Ideal Jet) [P.IsPrime]
    {f G : Jet} {s k r : ℕ} (hf : ¬ VanishesTo P f (s+1))
    (h : VanishesTo P (f^k*G) r) : VanishesTo P G (r-s*k) := by
  apply vanishesTo_of_X_pow_dvd P
  have hdiv := X_pow_dvd_of_vanishesTo P h
  rw [map_mul, map_pow] at hdiv
  exact @X_pow_dvd_of_pow_mul (Direction P) inferInstance inferInstance
    (expansion P f) (expansion P G) s k r
    (fun hm => hf (vanishesTo_of_X_pow_dvd P hm)) hdiv


/-- Divide an anchor power when the original contact is given by Hasse coefficients. -/
theorem vanishesTo_of_pow_mul_hasse [PerfectField K] (P : Ideal Jet) [P.IsPrime]
    {f G : Jet} {s k r : ℕ} (hf : ¬ VanishesTo P f (s+1))
    (h : ∀ a : Fin n →₀ ℕ, multiOrder a < r → hassePartial a (f^k*G) ∈ P) :
    VanishesTo P G (r-s*k) :=
  vanishesTo_of_pow_mul P hf (vanishesTo_of_hasse _ P r h)

end

#print axioms vanishesTo_of_pow_mul_hasse
#print axioms vanishesTo_of_pow_mul
end Shared50OrderDivision
