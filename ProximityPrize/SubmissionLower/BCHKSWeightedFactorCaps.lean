import ProximityPrize.SubmissionLower.BCHKSFactorPigeon

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace WeightedFactorCaps

variable {A : Type*} [CommSemiring A]

/-- Maximum of `deg_X(coeff_Y j) + k*j`; the tie-breaker used in the
multiplication proof is the largest outer index attaining this maximum. -/
noncomputable def weightedSupportDegree (p : Polynomial (Polynomial A)) (k : Nat) : Nat :=
  p.support.sup fun j => (p.coeff j).natDegree + k * j

theorem coeffWeight_le_of_ne (p : Polynomial (Polynomial A)) (k j : Nat)
    (hj : p.coeff j ≠ 0) :
    (p.coeff j).natDegree + k * j ≤ weightedSupportDegree p k := by
  classical
  unfold weightedSupportDegree
  exact Finset.le_sup (f := fun i => (p.coeff i).natDegree + k * i)
    (Polynomial.mem_support_iff.mpr hj)

theorem weightedSupportDegree_mul_le [IsDomain A]
    (p q : Polynomial (Polynomial A)) (k : Nat) (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedSupportDegree (p * q) k ≤
      weightedSupportDegree p k + weightedSupportDegree q k := by
  classical
  change (p * q).support.sup
    (fun n => ((p * q).coeff n).natDegree + k * n) ≤ _
  apply Finset.sup_le
  intro n hn
  have hnle : n ≤ p.natDegree + q.natDegree := by
    have h := Polynomial.le_natDegree_of_mem_supp (p := p * q) n hn
    rw [Polynomial.natDegree_mul hp hq] at h
    exact h
  have hpdeg : (p.coeff p.natDegree).natDegree + k * p.natDegree ≤
      weightedSupportDegree p k :=
    coeffWeight_le_of_ne p k p.natDegree (by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hqdeg : (q.coeff q.natDegree).natDegree + k * q.natDegree ≤
      weightedSupportDegree q k :=
    coeffWeight_le_of_ne q k q.natDegree (by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hkn : k * n ≤ weightedSupportDegree p k + weightedSupportDegree q k := by
    calc
      k * n ≤ k * (p.natDegree + q.natDegree) := Nat.mul_le_mul_left k hnle
      _ = k * p.natDegree + k * q.natDegree := Nat.mul_add _ _ _
      _ ≤ weightedSupportDegree p k + weightedSupportDegree q k := by
        apply Nat.add_le_add
        · exact (Nat.le_add_left _ _).trans hpdeg
        · exact (Nat.le_add_left _ _).trans hqdeg
  rw [Polynomial.coeff_mul]
  have hsum := Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.antidiagonal n)
    (f := fun ij : Nat × Nat => p.coeff ij.1 * q.coeff ij.2)
    (n := weightedSupportDegree p k + weightedSupportDegree q k - k * n)
  have hterm : ∀ ij ∈ Finset.antidiagonal n,
      (p.coeff ij.1 * q.coeff ij.2).natDegree ≤
        weightedSupportDegree p k + weightedSupportDegree q k - k * n := by
    intro ij hij
    by_cases hpij : p.coeff ij.1 = 0
    · simp [hpij]
    by_cases hqij : q.coeff ij.2 = 0
    · simp [hqij]
    have hsumidx : ij.1 + ij.2 = n := by simpa [Finset.mem_antidiagonal] using hij
    have hpw := coeffWeight_le_of_ne p k ij.1 hpij
    have hqw := coeffWeight_le_of_ne q k ij.2 hqij
    have hm := Polynomial.natDegree_mul_le (p := p.coeff ij.1) (q := q.coeff ij.2)
    have hkidx : k * ij.1 + k * ij.2 = k * n := by
      rw [← Nat.mul_add, hsumidx]
    omega
  have hdeg := hsum hterm
  omega

/-- Largest outer index among the terms attaining maximum weight. -/
theorem exists_max_index_weighted (p : Polynomial (Polynomial A)) (k : Nat)
    (hp : p ≠ 0) :
    ∃ m ∈ p.support,
      (p.coeff m).natDegree + k * m = weightedSupportDegree p k ∧
      ∀ n, m < n →
        (p.coeff n).natDegree + k * n < weightedSupportDegree p k ∨ p.coeff n = 0 := by
  classical
  let s : Finset Nat := p.support.filter fun n =>
    (p.coeff n).natDegree + k * n = weightedSupportDegree p k
  have hs : s.Nonempty := by
    have hsupp : p.support.Nonempty := (Polynomial.support_nonempty).2 hp
    obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup (s := p.support) hsupp
      (fun n => (p.coeff n).natDegree + k * n)
    refine ⟨m, ?_⟩
    simp [s, hm, weightedSupportDegree, hsup.symm]
  let mm := s.max' hs
  have hmm : mm ∈ s := Finset.max'_mem s hs
  refine ⟨mm, (Finset.mem_filter.mp hmm).1, (Finset.mem_filter.mp hmm).2, ?_⟩
  intro n hmn
  by_cases hn0 : p.coeff n = 0
  · exact Or.inr hn0
  left
  have hnmem : n ∈ p.support := Polynomial.mem_support_iff.mpr hn0
  have hnle := coeffWeight_le_of_ne p k n hn0
  apply lt_of_le_of_ne hnle
  intro heq
  have hnS : n ∈ s := by simp [s, hnmem, heq]
  have hnlemax : n ≤ mm := Finset.le_max' s n hnS
  exact (Nat.not_le_of_lt hmn) hnlemax

theorem weightedSupportDegree_mul_ge [IsDomain A]
    (p q : Polynomial (Polynomial A)) (k : Nat) (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedSupportDegree p k + weightedSupportDegree q k ≤
      weightedSupportDegree (p * q) k := by
  classical
  rcases exists_max_index_weighted p k hp with ⟨mp, hmp, hmpdeg, hmpmax⟩
  rcases exists_max_index_weighted q k hq with ⟨mq, hmq, hmqdeg, hmqmax⟩
  let N := mp + mq
  let deg := (p.coeff mp).natDegree + (q.coeff mq).natDegree
  let term : Nat × Nat → Polynomial A := fun ij => p.coeff ij.1 * q.coeff ij.2
  have hmx : (mp, mq) ∈ Finset.antidiagonal N := by simp [N, Finset.mem_antidiagonal]
  have hp0 : p.coeff mp ≠ 0 := Polynomial.mem_support_iff.mp hmp
  have hq0 : q.coeff mq ≠ 0 := Polynomial.mem_support_iff.mp hmq
  have hterm_mx : (term (mp, mq)).natDegree = deg := by
    simpa [term, deg] using Polynomial.natDegree_mul hp0 hq0
  have hleaderWeight : deg + k * N =
      weightedSupportDegree p k + weightedSupportDegree q k := by
    dsimp [deg, N]
    rw [Nat.mul_add]
    omega
  have hterm_other : ∀ y ∈ Finset.antidiagonal N, y ≠ (mp, mq) →
      (term y).natDegree < deg ∨ term y = 0 := by
    intro y hy hyne
    rcases y with ⟨i, j⟩
    have hij : i + j = mp + mq := by
      simpa [N, Finset.mem_antidiagonal] using hy
    have hlt : mp < i ∨ mq < j := by
      by_contra hn
      push Not at hn
      have hi : i ≤ mp := hn.1
      have hj : j ≤ mq := hn.2
      have : i = mp ∧ j = mq := by omega
      exact hyne (Prod.ext this.1 this.2)
    rcases hlt with hi | hj
    · rcases hmpmax i hi with hiw | hi0
      · by_cases qj0 : q.coeff j = 0
        · right; simp [term, qj0]
        · left
          have hnat := Polynomial.natDegree_mul_le (p := p.coeff i) (q := q.coeff j)
          have hqle := coeffWeight_le_of_ne q k j qj0
          have hkidx : k * i + k * j = k * N := by
            rw [← Nat.mul_add, hij]
          dsimp [term] at hnat ⊢
          omega
      · right; simp [term, hi0]
    · rcases hmqmax j hj with hjw | hj0
      · by_cases pi0 : p.coeff i = 0
        · right; simp [term, pi0]
        · left
          have hnat := Polynomial.natDegree_mul_le (p := p.coeff i) (q := q.coeff j)
          have hple := coeffWeight_le_of_ne p k i pi0
          have hkidx : k * i + k * j = k * N := by
            rw [← Nat.mul_add, hij]
          dsimp [term] at hnat ⊢
          omega
      · right; simp [term, hj0]
  have hsum : (∑ y ∈ Finset.antidiagonal N, term y).natDegree = deg :=
    Polynomial.Bivariate.natDegree_sum_eq_of_unique
      (mx := (mp, mq)) hmx hterm_mx hterm_other
  have hcoeff : ((p * q).coeff N).natDegree = deg := by
    rw [Polynomial.coeff_mul]
    exact hsum
  have hsum0 : (∑ y ∈ Finset.antidiagonal N, term y) ≠ 0 := by
    by_cases hd : deg = 0
    · have heq : (∑ y ∈ Finset.antidiagonal N, term y) = term (mp, mq) := by
        apply Finset.sum_eq_single_of_mem (mp, mq) hmx
        intro y hy hyne
        rcases hterm_other y hy hyne with hlt | hz
        · omega
        · exact hz
      rw [heq]
      exact mul_ne_zero hp0 hq0
    · intro hz
      rw [hz] at hsum
      simp at hsum
      exact hd hsum.symm
  have hprodcoeff : (p * q).coeff N ≠ 0 := by
    rw [Polynomial.coeff_mul]
    exact hsum0
  have hle := coeffWeight_le_of_ne (p * q) k N hprodcoeff
  rw [hcoeff] at hle
  omega

theorem weightedSupportDegree_mul [IsDomain A]
    (p q : Polynomial (Polynomial A)) (k : Nat) (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedSupportDegree (p * q) k =
      weightedSupportDegree p k + weightedSupportDegree q k :=
  le_antisymm (weightedSupportDegree_mul_le p q k hp hq)
    (weightedSupportDegree_mul_ge p q k hp hq)

end WeightedFactorCaps


namespace WeightedFactorCaps

variable {A : Type*} [CommSemiring A]

theorem weightedSupportDegree_lt_of_coeff_cap
    (p : Polynomial (Polynomial A)) (k B : Nat) (hp : p ≠ 0)
    (hcap : ∀ j a, (p.coeff j).coeff a ≠ 0 → a + k * j < B) :
    weightedSupportDegree p k < B := by
  classical
  have hB : 0 < B := by
    obtain ⟨j, hj⟩ := (Polynomial.support_nonempty.mpr hp)
    have hc : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hlc : (p.coeff j).coeff (p.coeff j).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hc
    exact lt_of_le_of_lt (Nat.zero_le _) (hcap j _ hlc)
  rw [weightedSupportDegree, Finset.sup_lt_iff hB]
  intro j hj
  have hc : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hlc : (p.coeff j).coeff (p.coeff j).natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hc
  exact hcap j _ hlc

theorem coeff_cap_of_dvd
    [IsDomain A]
    (Q R : Polynomial (Polynomial A)) (k B : Nat)
    (hQ : Q ≠ 0) (hRQ : R ∣ Q)
    (hcap : ∀ j a, (Q.coeff j).coeff a ≠ 0 → a + k * j < B) :
    ∀ j a, (R.coeff j).coeff a ≠ 0 → a + k * j < B := by
  obtain ⟨C, rfl⟩ := hRQ
  have hnz : R ≠ 0 ∧ C ≠ 0 := mul_ne_zero_iff.mp hQ
  have hmul := weightedSupportDegree_mul R C k hnz.1 hnz.2
  have hRle : weightedSupportDegree R k ≤ weightedSupportDegree (R * C) k := by
    rw [hmul]
    exact Nat.le_add_right _ _
  have hQlt := weightedSupportDegree_lt_of_coeff_cap (R * C) k B hQ hcap
  intro j a ha
  have hc : R.coeff j ≠ 0 := fun hz => ha (by simp [hz])
  have hale : a ≤ (R.coeff j).natDegree := Polynomial.le_natDegree_of_ne_zero ha
  have hw := coeffWeight_le_of_ne R k j hc
  omega


end WeightedFactorCaps

namespace WeightedFactorCaps
variable {F : Type*} [Field F]

/-- Sharp `(X + kY)` support-cap inheritance by a trivariate normalized factor. -/
theorem normalizedFactor_weightedX_cap
    [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F))) (k B : Nat)
    (hQ : Q ≠ 0)
    (hR : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 → a + k * j < B) :
    ∀ j a, ((R.coeff j).coeff a) ≠ 0 → a + k * j < B :=
  coeff_cap_of_dvd Q R k B hQ
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hR) hcap

end WeightedFactorCaps
end ProximityPrize.SubmissionLower
