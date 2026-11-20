/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.Koala6844NormalizationNorm
import Mathlib.Tactic

namespace ProximityPrize.SubmissionLower.FixedWordGenerator
open Polynomial

noncomputable section
variable {K : Type*} [Field K] (σ : K ≃+* K) (a b : K[X])

/-- A homogeneous equation for coefficientwise conjugation of a polynomial. -/
def Solution (P : K[X]) : Prop := a * P.map σ.toRingHom = b * P

private theorem fixed_ratio (ha : a ≠ 0) {T P : K[X]} (hT : Solution σ a b T)
    (hP : Solution σ a b P) (hn : T ≠ 0) :
    σ (P.leadingCoeff / T.leadingCoeff) = P.leadingCoeff / T.leadingCoeff := by
  have hb : (b.map σ.symm.toRingHom).map σ.toRingHom = b := by
    ext i
    simp
  apply Koala6844Normalization.leadingCoeff_ratio_fixed σ.toRingHom (d0 := b.map σ.symm.toRingHom) ha hn
  · rw [hb]; exact hP
  · rw [hb]; exact hT

private theorem multiple_fixed (ha : a ≠ 0) {T : K[X]} (hn : T ≠ 0)
    (ht : Solution σ a b T)
    (minimal : ∀ P : K[X], P ≠ 0 → Solution σ a b P → T.natDegree ≤ P.natDegree)
    (P : K[X]) (hp : Solution σ a b P) :
    ∃ S : K[X], S.map σ.toRingHom = S ∧ P = T*S := by
  classical
  induction n : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hP : P = 0
    · exact ⟨0, by simp, by simp [hP]⟩
    have hle := minimal P hP hp
    let k := P.leadingCoeff / T.leadingCoeff
    have hk : k ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hP) (leadingCoeff_ne_zero.mpr hn)
    let M : K[X] := C k * X^(P.natDegree - T.natDegree)
    have hkfix : σ.toRingHom k = k := fixed_ratio σ a b ha ht hp hn
    have hM : M.map σ.toRingHom = M := by
      simp only [M, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, hkfix]
    have hnM : M ≠ 0 := mul_ne_zero (C_ne_zero.mpr hk) (pow_ne_zero _ X_ne_zero)
    have hTM : T*M ≠ 0 := mul_ne_zero hn hnM
    have hd : (T*M).natDegree = P.natDegree := by
      rw [natDegree_mul hn hnM]
      simp [M, natDegree_C_mul hk]
      omega
    have hlead : (T*M).leadingCoeff = P.leadingCoeff := by
      simp [M, k, leadingCoeff_mul]
      field_simp [leadingCoeff_ne_zero.mpr hn]
    have hdeg : (P-T*M).degree < P.degree :=
      degree_sub_lt_left (by rw [degree_eq_natDegree hP,degree_eq_natDegree hTM,hd]) hP hlead.symm
    have hdiff : Solution σ a b (P-T*M) := by
      unfold Solution at hp ht ⊢
      rw [Polynomial.map_sub, Polynomial.map_mul, hM, mul_sub, mul_sub, hp, ← mul_assoc, ht]
      ring
    by_cases hzero : P-T*M = 0
    · exact ⟨M,hM,sub_eq_zero.mp hzero⟩
    obtain ⟨S,hS,hprod⟩ := ih (P-T*M).natDegree (by rw [← n]; exact natDegree_lt_natDegree hzero hdeg)
      (P-T*M) hdiff rfl
    refine ⟨S+M, by rw [Polynomial.map_add, hS, hM], ?_⟩
    rw [mul_add, ← hprod]
    ring

/-- The solutions form a principal module over the fixed polynomial ring.
Its generator has no zero at a fixed field element. -/
theorem exists_generator (ha : a ≠ 0) (exists_solution : ∃ P : K[X], P ≠ 0 ∧ Solution σ a b P) :
    ∃ T : K[X], T ≠ 0 ∧ Solution σ a b T ∧
      (∀ x : K, σ x = x → T.eval x ≠ 0) ∧
      (∀ P : K[X], Solution σ a b P → ∃ S : K[X], S.map σ.toRingHom = S ∧ P = T*S) := by
  classical
  let pred (n : ℕ) := ∃ P : K[X], P ≠ 0 ∧ Solution σ a b P ∧ P.natDegree = n
  have hex : ∃ n, pred n := by
    obtain ⟨P,hn,hP⟩ := exists_solution
    exact ⟨P.natDegree,P,hn,hP,rfl⟩
  obtain ⟨T,hn,hT,hmin⟩ := Nat.find_spec hex
  have minimal (P : K[X]) (hP : P ≠ 0) (hs : Solution σ a b P) : T.natDegree ≤ P.natDegree :=
    hmin.trans_le (Nat.find_min' hex ⟨P,hP,hs,rfl⟩)
  refine ⟨T,hn,hT,?_,multiple_fixed σ a b ha hn hT minimal⟩
  intro x hx hroot
  let L : K[X] := X - C x
  have hL : L ≠ 0 := X_sub_C_ne_zero x
  have hfixed : L.map σ.toRingHom = L := by simp [L,hx]
  obtain ⟨U,hU⟩ := (dvd_iff_isRoot.mpr hroot : L ∣ T)
  have hUn : U ≠ 0 := fun h => hn (by simp [hU,h])
  have hs : Solution σ a b U := by
    unfold Solution at hT ⊢
    rw [hU,Polynomial.map_mul,hfixed] at hT
    apply mul_left_cancel₀ hL
    calc
      _ = a * (L * U.map σ.toRingHom) := by ring
      _ = b * (L * U) := hT
      _ = _ := by ring
  have hm := minimal U hUn hs
  rw [hU,natDegree_mul hL hUn] at hm
  simp [L] at hm

#print axioms exists_generator
end
end ProximityPrize.SubmissionLower.FixedWordGenerator
