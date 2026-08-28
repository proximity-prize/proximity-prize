import ProximityPrize.SubmissionLower.BCHKSFactorPigeon

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace YZFactorCap

variable {F : Type*} [CommSemiring F]

lemma natDegree_sum_le_of_forall {α : Type*} (s : Finset α)
    (f : α → Polynomial F) (n : ℕ) (h : ∀ a ∈ s, (f a).natDegree ≤ n) :
    (∑ a ∈ s, f a).natDegree ≤ n := by
  letI := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (h a (by simp)) (ih (fun b hb => h b (by simp [hb]))))

theorem degreeX_sum_le_of_forall {α : Type*} (s : Finset α)
    (f : α → Polynomial (Polynomial F)) (n : ℕ) (h : ∀ a ∈ s, Polynomial.Bivariate.degreeX (f a) ≤ n) :
    Polynomial.Bivariate.degreeX (∑ a ∈ s, f a) ≤ n := by
  classical
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  have heq : (∑ a ∈ s, f a).coeff i = ∑ a ∈ s, (f a).coeff i := by simp
  rw [heq]
  exact natDegree_sum_le_of_forall _ _ _ (fun a ha =>
    (Polynomial.Bivariate.coeff_natDegree_le_degreeX (f a) i).trans (h a ha))

theorem degreeX_sum_eq_of_unique {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → Polynomial (Polynomial F)} {deg : ℕ} (mx : α) (hmx : mx ∈ s)
    (hfmx : f mx ≠ 0) (hdeg : Polynomial.Bivariate.degreeX (f mx) = deg)
    (hother : ∀ y ∈ s, y ≠ mx →
      Polynomial.Bivariate.degreeX (f y) < deg ∨ f y = 0) :
    Polynomial.Bivariate.degreeX (∑ y ∈ s, f y) = deg := by
  have hle := degreeX_sum_le_of_forall s f deg (by
    intro y hy
    by_cases h : y = mx
    · subst y; exact hdeg.le
    · rcases hother y hy h with hlt | hz
      · exact hlt.le
      · rw [hz]
        exact Nat.zero_le _)
  obtain ⟨r, hr, hrdeg, -⟩ := Polynomial.Bivariate.exists_max_index_degreeX (f mx) hfmx
  have hcoeff : ((∑ y ∈ s, f y).coeff r).natDegree = deg := by
    have heq : (∑ y ∈ s, f y).coeff r = ∑ y ∈ s, (f y).coeff r := by simp
    rw [heq]
    apply Polynomial.Bivariate.natDegree_sum_eq_of_unique mx hmx
    · exact hrdeg.trans hdeg
    · intro y hy hne
      rcases hother y hy hne with hlt | hz
      · left
        exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX (f y) r).trans_lt hlt
      · right; simp [hz]
  apply le_antisymm hle
    ((by rw [← hcoeff]; exact Polynomial.Bivariate.coeff_natDegree_le_degreeX _ r))

/-- Maximum of `deg_X(coeff_Y j) + k*j`; the tie-breaker used in the
multiplication proof is the largest outer index attaining this maximum. -/
noncomputable def yzSupportDegree (p : Polynomial (Polynomial (Polynomial F))) (k : Nat) : Nat :=
  p.support.sup fun j => Polynomial.Bivariate.degreeX (p.coeff j) + k * j

theorem coeffWeight_le_of_ne (p : Polynomial (Polynomial (Polynomial F))) (k j : Nat)
    (hj : p.coeff j ≠ 0) :
    Polynomial.Bivariate.degreeX (p.coeff j) + k * j ≤ yzSupportDegree p k := by
  classical
  unfold yzSupportDegree
  exact Finset.le_sup (f := fun i => Polynomial.Bivariate.degreeX (p.coeff i) + k * i)
    (Polynomial.mem_support_iff.mpr hj)

theorem yzSupportDegree_mul_le [IsDomain F]
    (p q : Polynomial (Polynomial (Polynomial F))) (k : Nat) (hp : p ≠ 0) (hq : q ≠ 0) :
    yzSupportDegree (p * q) k ≤
      yzSupportDegree p k + yzSupportDegree q k := by
  classical
  change (p * q).support.sup
    (fun n => Polynomial.Bivariate.degreeX ((p * q).coeff n) + k * n) ≤ _
  apply Finset.sup_le
  intro n hn
  have hnle : n ≤ p.natDegree + q.natDegree := by
    have h := Polynomial.le_natDegree_of_mem_supp (p := p * q) n hn
    rw [Polynomial.natDegree_mul hp hq] at h
    exact h
  have hpdeg : Polynomial.Bivariate.degreeX (p.coeff p.natDegree) + k * p.natDegree ≤
      yzSupportDegree p k :=
    coeffWeight_le_of_ne p k p.natDegree (by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hqdeg : Polynomial.Bivariate.degreeX (q.coeff q.natDegree) + k * q.natDegree ≤
      yzSupportDegree q k :=
    coeffWeight_le_of_ne q k q.natDegree (by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hkn : k * n ≤ yzSupportDegree p k + yzSupportDegree q k := by
    calc
      k * n ≤ k * (p.natDegree + q.natDegree) := Nat.mul_le_mul_left k hnle
      _ = k * p.natDegree + k * q.natDegree := Nat.mul_add _ _ _
      _ ≤ yzSupportDegree p k + yzSupportDegree q k := by
        apply Nat.add_le_add
        · exact (Nat.le_add_left _ _).trans hpdeg
        · exact (Nat.le_add_left _ _).trans hqdeg
  rw [Polynomial.coeff_mul]
  have hsum := degreeX_sum_le_of_forall
    (s := Finset.antidiagonal n)
    (f := fun ij : Nat × Nat => p.coeff ij.1 * q.coeff ij.2)
    (n := yzSupportDegree p k + yzSupportDegree q k - k * n)
  have hterm : ∀ ij ∈ Finset.antidiagonal n,
      Polynomial.Bivariate.degreeX (p.coeff ij.1 * q.coeff ij.2) ≤
        yzSupportDegree p k + yzSupportDegree q k - k * n := by
    intro ij hij
    by_cases hpij : p.coeff ij.1 = 0
    · rw [hpij, zero_mul]
      change 0 ≤ _
      omega
    by_cases hqij : q.coeff ij.2 = 0
    · rw [hqij, mul_zero]
      change 0 ≤ _
      omega
    have hsumidx : ij.1 + ij.2 = n := by simpa [Finset.mem_antidiagonal] using hij
    have hpw := coeffWeight_le_of_ne p k ij.1 hpij
    have hqw := coeffWeight_le_of_ne q k ij.2 hqij
    have hm := Polynomial.Bivariate.degreeX_mul_le (p.coeff ij.1) (q.coeff ij.2)
    have hkidx : k * ij.1 + k * ij.2 = k * n := by
      rw [← Nat.mul_add, hsumidx]
    omega
  have hdeg := hsum hterm
  omega

/-- Largest outer index among the terms attaining maximum weight. -/
theorem exists_max_index_yz (p : Polynomial (Polynomial (Polynomial F))) (k : Nat)
    (hp : p ≠ 0) :
    ∃ m ∈ p.support,
      Polynomial.Bivariate.degreeX (p.coeff m) + k * m = yzSupportDegree p k ∧
      ∀ n, m < n →
        Polynomial.Bivariate.degreeX (p.coeff n) + k * n < yzSupportDegree p k ∨ p.coeff n = 0 := by
  classical
  let s : Finset Nat := p.support.filter fun n =>
    Polynomial.Bivariate.degreeX (p.coeff n) + k * n = yzSupportDegree p k
  have hs : s.Nonempty := by
    have hsupp : p.support.Nonempty := (Polynomial.support_nonempty).2 hp
    obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup (s := p.support) hsupp
      (fun n => Polynomial.Bivariate.degreeX (p.coeff n) + k * n)
    refine ⟨m, ?_⟩
    simp [s, hm, yzSupportDegree, hsup.symm]
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

theorem yzSupportDegree_mul_ge [IsDomain F]
    (p q : Polynomial (Polynomial (Polynomial F))) (k : Nat) (hp : p ≠ 0) (hq : q ≠ 0) :
    yzSupportDegree p k + yzSupportDegree q k ≤
      yzSupportDegree (p * q) k := by
  classical
  rcases exists_max_index_yz p k hp with ⟨mp, hmp, hmpdeg, hmpmax⟩
  rcases exists_max_index_yz q k hq with ⟨mq, hmq, hmqdeg, hmqmax⟩
  let N := mp + mq
  let deg := Polynomial.Bivariate.degreeX (p.coeff mp) + Polynomial.Bivariate.degreeX (q.coeff mq)
  let term : Nat × Nat → Polynomial (Polynomial F) := fun ij => p.coeff ij.1 * q.coeff ij.2
  have hmx : (mp, mq) ∈ Finset.antidiagonal N := by simp [N, Finset.mem_antidiagonal]
  have hp0 : p.coeff mp ≠ 0 := Polynomial.mem_support_iff.mp hmp
  have hq0 : q.coeff mq ≠ 0 := Polynomial.mem_support_iff.mp hmq
  have hterm_mx : Polynomial.Bivariate.degreeX (term (mp, mq)) = deg := by
    simpa [term, deg] using Polynomial.Bivariate.degreeX_mul _ _ hp0 hq0
  have hleaderWeight : deg + k * N =
      yzSupportDegree p k + yzSupportDegree q k := by
    dsimp [deg, N]
    rw [Nat.mul_add]
    omega
  have hterm_other : ∀ y ∈ Finset.antidiagonal N, y ≠ (mp, mq) →
      Polynomial.Bivariate.degreeX (term y) < deg ∨ term y = 0 := by
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
          have hnat := Polynomial.Bivariate.degreeX_mul_le (p.coeff i) (q.coeff j)
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
          have hnat := Polynomial.Bivariate.degreeX_mul_le (p.coeff i) (q.coeff j)
          have hple := coeffWeight_le_of_ne p k i pi0
          have hkidx : k * i + k * j = k * N := by
            rw [← Nat.mul_add, hij]
          dsimp [term] at hnat ⊢
          omega
      · right; simp [term, hj0]
  have hsum : Polynomial.Bivariate.degreeX (∑ y ∈ Finset.antidiagonal N, term y) = deg :=
    degreeX_sum_eq_of_unique
      (mx := (mp, mq)) hmx (mul_ne_zero hp0 hq0) hterm_mx hterm_other
  have hcoeff : Polynomial.Bivariate.degreeX ((p * q).coeff N) = deg := by
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
      have : Polynomial.Bivariate.degreeX (0 : Polynomial (Polynomial F)) = 0 := rfl
      rw [this] at hsum
      exact hd hsum.symm
  have hprodcoeff : (p * q).coeff N ≠ 0 := by
    rw [Polynomial.coeff_mul]
    exact hsum0
  have hle := coeffWeight_le_of_ne (p * q) k N hprodcoeff
  rw [hcoeff] at hle
  omega

theorem yzSupportDegree_mul [IsDomain F]
    (p q : Polynomial (Polynomial (Polynomial F))) (k : Nat) (hp : p ≠ 0) (hq : q ≠ 0) :
    yzSupportDegree (p * q) k =
      yzSupportDegree p k + yzSupportDegree q k :=
  le_antisymm (yzSupportDegree_mul_le p q k hp hq)
    (yzSupportDegree_mul_ge p q k hp hq)

end YZFactorCap


namespace YZFactorCap
variable {F : Type*} [CommSemiring F]
theorem coeffDegreeX_cap_of_dvd [IsDomain F]
    (Q R : Polynomial (Polynomial (Polynomial F))) (k B : Nat)
    (hQ : Q ≠ 0) (hRQ : R ∣ Q)
    (hcap : ∀ j, Q.coeff j ≠ 0 → Polynomial.Bivariate.degreeX (Q.coeff j) + k*j < B) :
    ∀ j, R.coeff j ≠ 0 → Polynomial.Bivariate.degreeX (R.coeff j) + k*j < B := by
  obtain ⟨C, rfl⟩ := hRQ
  have hnz := mul_ne_zero_iff.mp hQ
  have hm := yzSupportDegree_mul R C k hnz.1 hnz.2
  intro j hj
  have hr := coeffWeight_le_of_ne R k j hj
  have hq : yzSupportDegree (R*C) k < B := by
    unfold yzSupportDegree
    rw [Finset.sup_lt_iff]
    · intro i hi; exact hcap i (Polynomial.mem_support_iff.mp hi)
    · obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hQ
      exact Nat.zero_lt_of_lt (hcap i (Polynomial.mem_support_iff.mp hi))
  rw [hm] at hq
  omega

theorem coefficient_cap_of_dvd [IsDomain F]
    (Q R : Polynomial (Polynomial (Polynomial F))) (k B : Nat)
    (hQ : Q ≠ 0) (hRQ : R ∣ Q)
    (hcap : ∀ j, Q.coeff j ≠ 0 → Polynomial.Bivariate.degreeX (Q.coeff j) + k*j < B) :
    ∀ j a, ((R.coeff j).coeff a) ≠ 0 → ((R.coeff j).coeff a).natDegree + k*j < B := by
  intro j a ha
  have hj : R.coeff j ≠ 0 := fun h => ha (by simp [h])
  have hc := coeffDegreeX_cap_of_dvd Q R k B hQ hRQ hcap j hj
  have hd := Polynomial.Bivariate.coeff_natDegree_le_degreeX (R.coeff j) a
  omega

/-- Sharp `Z+Y` cap inheritance for a normalized factor. -/
theorem normalizedFactor_YZ_cap
    {F : Type*} [Field F] [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F))) (B : Nat)
    (hQ : Q ≠ 0)
    (hR : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hcap : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < B) :
    ∀ j a, (R.coeff j).coeff a ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < B := by
  have hraw := coefficient_cap_of_dvd Q R 1 B hQ
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hR) (by
      intro j hj
      obtain ⟨a, ha, hadeg, _⟩ :=
        Polynomial.Bivariate.exists_max_index_degreeX (Q.coeff j) hj
      have hca : (Q.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
      simpa [hadeg] using hcap j a hca)
  simpa using hraw

end YZFactorCap
end ProximityPrize.SubmissionLower
