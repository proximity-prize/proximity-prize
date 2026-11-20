import ProximityPrize.SubmissionLower.LowerGeometry

open scoped BigOperators

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

section CommonDenominator

variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S] [Algebra K R]

def ClearedForm (a b : R) (q : ℕ) (P : R) : Prop :=
  ∃ coeff : Fin (q+1) → R, P = ∑ j, a^(q-j.val)*b^j.val*coeff j

private theorem eigenpower (D : Derivation K R R) (a scalar : R)
    (ha : D a = a*scalar) (n : ℕ) : D (a^n) = a^n*((n : R)*scalar) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ,Derivation.leibniz,smul_eq_mul,ih,ha,Nat.cast_succ]
    ring

theorem ClearedForm.derivation (D : Derivation K R R) (a b scalar : R)
    (ha : D a = a*scalar) (hb : D b = b*scalar)
    (q : ℕ) {P : R} (hp : ClearedForm a b q P) :
    ClearedForm a b q (D P) := by
  obtain ⟨coeff, rfl⟩ := hp
  refine ⟨fun j => D (coeff j) + (((q-j.val : ℕ) : R)+(j.val : R))*scalar*coeff j,?_⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Derivation.leibniz,smul_eq_mul,eigenpower D a scalar ha,eigenpower D b scalar hb]
  ring

theorem ClearedForm.iterate (D : Derivation K R R) (a b scalar : R)
    (ha : D a = a*scalar) (hb : D b = b*scalar)
    (q n : ℕ) {P : R} (hp : ClearedForm a b q P) :
    ClearedForm a b q ((D : R → R)^[n] P) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact ClearedForm.derivation D a b scalar ha hb q ih

theorem ClearedForm.specialization_dvd (evaluation : R →+* S) (a b : R) (v : S)
    (he : evaluation b = evaluation a*v) (q : ℕ) {P : R}
    (hp : ClearedForm a b q P) : evaluation a^q ∣ evaluation P := by
  obtain ⟨coeff,rfl⟩ := hp
  refine ⟨∑ j : Fin (q+1), v^j.val*evaluation (coeff j),?_⟩
  rw [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul,map_pow,he,mul_pow]
  have hj : j.val ≤ q := by have h := j.isLt; omega
  have hpow : evaluation a^(q-j.val)*evaluation a^j.val = evaluation a^q := by
    rw [← pow_add,Nat.sub_add_cancel hj]
  calc
    _ = (evaluation a^(q-j.val)*evaluation a^j.val)*v^j.val*evaluation (coeff j) := by ring
    _ = _ := by rw [hpow]; ring

end CommonDenominator

theorem cleared_polynomial_eq_zero {K I : Type*} [Field K]
    (nodes : I ↪ K) (support : Finset I) (m q : ℕ) (P a : Polynomial K)
    (hdiv : a^q ∣ P)
    (hd : P.natDegree < m*support.card+q*a.natDegree)
    (havoid : ∀ i ∈ support, a.eval (nodes i) ≠ 0)
    (hroot : ∀ i ∈ support, (Polynomial.X-Polynomial.C (nodes i))^m ∣ P) :
    P = 0 := by
  classical
  by_contra hn
  obtain ⟨Q,rfl⟩ := hdiv
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hn
  have hmult : ∀ i ∈ support, m ≤ Q.rootMultiplicity (nodes i) := by
    intro i hi
    have hp := (Polynomial.le_rootMultiplicity_iff hn).mpr (hroot i hi)
    have hzero : (a^q).rootMultiplicity (nodes i) = 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero_iff]
      intro hr
      exact False.elim (pow_ne_zero q (havoid i hi) (by
        simpa only [Polynomial.IsRoot,Polynomial.eval_pow] using hr))
    rwa [Polynomial.rootMultiplicity_mul hn,hzero,Nat.zero_add] at hp
  have hcount := BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
    Q nodes support m hmult
  rw [Polynomial.natDegree_mul (left_ne_zero_of_mul hn) hQ,Polynomial.natDegree_pow] at hd
  omega

end ProximityPrize.SubmissionLower.Koala6844Receipts
