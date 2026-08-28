import ProximityPrize.SubmissionLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionLower.BCHKSParameters

namespace ProximityPrize.SubmissionLower

/-- Summing a tailored per-factor obstruction of size `(2d-1) DZ` costs at
most `2 DZ DY`; it is not charged the global bad budget once per factor. -/
theorem sum_staged_R_capacities_le
    {ρ : Type*} [DecidableEq ρ] (Rs : Finset ρ)
    (d bad : ρ → Nat) (A e DZ DY : Nat)
    (hdpos : ∀ r ∈ Rs, 0 < d r)
    (hdsq : (∑ r ∈ Rs, d r ^ 2) ≤ DY ^ 2)
    (hdsum : (∑ r ∈ Rs, d r) ≤ DY)
    (hbad : ∀ r ∈ Rs, bad r ≤ 2 * d r * DZ) :
    (∑ r ∈ Rs, (A * d r ^ 2 + e * d r + bad r)) ≤
      A * DY ^ 2 + e * DY + 2 * DZ * DY := by
  have hbad' : ∀ r ∈ Rs, bad r ≤ 2 * DZ * d r := by
    intro r hr
    calc
      bad r ≤ 2 * d r * DZ := hbad r hr
      _ = 2 * DZ * d r := by ring
  calc
    (∑ r ∈ Rs, (A * d r ^ 2 + e * d r + bad r)) ≤
        ∑ r ∈ Rs, (A * d r ^ 2 + e * d r + 2 * DZ * d r) := by
      exact Finset.sum_le_sum fun r hr => Nat.add_le_add_left (hbad' r hr) _
    _ = A * (∑ r ∈ Rs, d r ^ 2) +
          e * (∑ r ∈ Rs, d r) + 2 * DZ * (∑ r ∈ Rs, d r) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ A * DY ^ 2 + e * DY + 2 * DZ * DY := by
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left A hdsq) (Nat.mul_le_mul_left e hdsum))
        (Nat.mul_le_mul_left (2 * DZ) hdsum)

/-- Variant retaining an externally proved square-sum cap instead of
weakening it to the square of the total degree. -/
theorem sum_staged_R_capacities_le_of_sq_cap
    {ρ : Type*} [DecidableEq ρ] (Rs : Finset ρ)
    (d bad : ρ → Nat) (A e DZ DY SQ : Nat)
    (hdsq : (∑ r ∈ Rs, d r ^ 2) ≤ SQ)
    (hdsum : (∑ r ∈ Rs, d r) ≤ DY)
    (hbad : ∀ r ∈ Rs, bad r ≤ 2 * d r * DZ) :
    (∑ r ∈ Rs, (A * d r ^ 2 + e * d r + bad r)) ≤
      A * SQ + e * DY + 2 * DZ * DY := by
  have hbad' : ∀ r ∈ Rs, bad r ≤ 2 * DZ * d r := by
    intro r hr
    calc
      bad r ≤ 2 * d r * DZ := hbad r hr
      _ = 2 * DZ * d r := by ring
  calc
    (∑ r ∈ Rs, (A * d r ^ 2 + e * d r + bad r)) ≤
        ∑ r ∈ Rs, (A * d r ^ 2 + e * d r + 2 * DZ * d r) := by
      exact Finset.sum_le_sum fun r hr => Nat.add_le_add_left (hbad' r hr) _
    _ = A * (∑ r ∈ Rs, d r ^ 2) +
          e * (∑ r ∈ Rs, d r) + 2 * DZ * (∑ r ∈ Rs, d r) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ A * SQ + e * DY + 2 * DZ * DY := by
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left A hdsq) (Nat.mul_le_mul_left e hdsum))
        (Nat.mul_le_mul_left (2 * DZ) hdsum)

/-- The staged accounting, including one initial `Q`-bad-Z deletion and all
tailored selected-factor obstruction budgets, fits the BCHKS numerator. -/
theorem bchks_staged_capacity_budget :
    632176 * 519142 * 851 ^ 2 +
      (bchksErrors + 1) * 851 +
      2 * 519143 * 851 + 519143 < bchksNumerator := by
  norm_num [bchksErrors, bchksNumerator]

/-- Convenient consequence for a source set after deleting the one-time
`Q`-bad set. -/
theorem bchks_staged_card_after_Qbad
    {α : Type*} [DecidableEq α] (S QBad : Finset α)
    (hS : bchksNumerator < S.card) (hQBad : (S ∩ QBad).card ≤ 519143) :
    632176 * 519142 * 851 ^ 2 +
      (bchksErrors + 1) * 851 + 2 * 519143 * 851 < (S \ QBad).card := by
  rw [Finset.card_sdiff]
  apply Nat.lt_sub_of_add_lt
  have hb := bchks_staged_capacity_budget
  have hi : (QBad ∩ S).card ≤ 519143 := by simpa [Finset.inter_comm] using hQBad
  exact (Nat.add_le_add_left hi _).trans_lt (hb.trans hS)



/-- Outside the one-time bad set, the full interpolation polynomial has a
nonzero `Z`-specialization. -/
theorem triSpecializeZ_ne_zero_outside_bad
    {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial (Polynomial F))) (S : Finset F)
    {z : F} (hz : z ∈ S \ badZSpecializations Q S) :
    triSpecializeZ Q z ≠ 0 := by
  intro hzero
  exact (Finset.mem_sdiff.mp hz).2 (by
    simp [badZSpecializations, (Finset.mem_sdiff.mp hz).1, hzero])

/-- Choose any nonzero coefficient satisfying the interpolation `Z` cap; its
roots account for the initial deletion exactly once. -/
theorem bchks_staged_after_badZSpecializations
    {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial (Polynomial F))) (S : Finset F)
    (j a : Nat) (hc : (Q.coeff j).coeff a ≠ 0)
    (hdeg : ((Q.coeff j).coeff a).natDegree < 519143)
    (hS : bchksNumerator < S.card) :
    632176 * 519142 * 851 ^ 2 +
      (bchksErrors + 1) * 851 + 2 * 519143 * 851 <
        (S \ badZSpecializations Q S).card := by
  apply bchks_staged_card_after_Qbad S (badZSpecializations Q S) hS
  have hb := badZSpecializations_card_le_519142 Q S j a hc hdeg
  exact (Finset.card_le_card Finset.inter_subset_right).trans (hb.trans (by omega))



/-- Direct normalized-factor instantiation of the staged capacity sum. -/
theorem positive_normalizedFactors_staged_cap_le
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (bad : Polynomial (Polynomial (Polynomial F)) → Nat)
    (A e DZ DY : Nat) (hQdeg : Q.natDegree ≤ DY)
    (hbad : ∀ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun R => 0 < R.natDegree),
      bad R ≤ 2 * R.natDegree * DZ) :
    (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun R => 0 < R.natDegree),
      (A * R.natDegree ^ 2 + e * R.natDegree + bad R)) ≤
      A * DY ^ 2 + e * DY + 2 * DZ * DY := by
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    fun R => 0 < R.natDegree
  have hsum : (∑ R ∈ Rs, R.natDegree) ≤ DY := by
    calc
      (∑ R ∈ Rs, R.natDegree) ≤
          ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset, R.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ DY := hQdeg
  have hsq : (∑ R ∈ Rs, R.natDegree ^ 2) ≤ DY ^ 2 := by
    have hpoint : ∀ R ∈ Rs, R.natDegree ^ 2 ≤
        R.natDegree * (∑ R ∈ Rs, R.natDegree) := by
      intro R hR
      have hle : R.natDegree ≤ ∑ x ∈ Rs, x.natDegree := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hR
      simpa [pow_two] using Nat.mul_le_mul_left R.natDegree hle
    calc
      (∑ R ∈ Rs, R.natDegree ^ 2) ≤
          ∑ R ∈ Rs, R.natDegree * (∑ R ∈ Rs, R.natDegree) :=
        Finset.sum_le_sum hpoint
      _ = (∑ R ∈ Rs, R.natDegree) ^ 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ DY ^ 2 := Nat.pow_le_pow_left hsum 2
  apply sum_staged_R_capacities_le Rs Polynomial.natDegree bad A e DZ DY
  · intro R hR
    exact (Finset.mem_filter.mp hR).2
  · exact hsq
  · exact hsum
  · intro R hR
    exact hbad R (by simpa [Rs] using hR)

/-- Mixed staged accounting.  Degree-one outer factors use the separate
linear cost `L`; every higher-degree factor uses `C * d`.  The comparison
`L ≤ C * DY` makes both branches charge at most `C * DY * d`, so the
global sum remains quadratic in the interpolation `Y` cap. -/
theorem positive_normalizedFactors_mixed_cap_le
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (bad : Polynomial (Polynomial (Polynomial F)) → Nat)
    (L C e DZ DY : Nat) (hQdeg : Q.natDegree ≤ DY)
    (hlinear : L ≤ C * DY)
    (hbad : ∀ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun R => 0 < R.natDegree),
      bad R ≤ 2 * R.natDegree * DZ) :
    (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun R => 0 < R.natDegree),
      ((if R.natDegree = 1 then L else C * R.natDegree) * R.natDegree +
        e * R.natDegree + bad R)) ≤
      C * DY ^ 2 + e * DY + 2 * DZ * DY := by
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    fun R => 0 < R.natDegree
  have hsum : (∑ R ∈ Rs, R.natDegree) ≤ DY := by
    calc
      (∑ R ∈ Rs, R.natDegree) ≤
          ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
            R.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ DY := hQdeg
  have hterm : ∀ R ∈ Rs,
      (if R.natDegree = 1 then L else C * R.natDegree) * R.natDegree +
          e * R.natDegree + bad R ≤
        C * DY * R.natDegree + e * R.natDegree + 2 * DZ * R.natDegree := by
    intro R hR
    have hRle : R.natDegree ≤ DY := by
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hR).trans hsum
    have hpair :
        (if R.natDegree = 1 then L else C * R.natDegree) * R.natDegree ≤
          C * DY * R.natDegree := by
      by_cases hOne : R.natDegree = 1
      · simp [hOne, hlinear]
      · rw [if_neg hOne]
        exact Nat.mul_le_mul_right R.natDegree (Nat.mul_le_mul_left C hRle)
    have hbadR : bad R ≤ 2 * DZ * R.natDegree := by
      calc
        bad R ≤ 2 * R.natDegree * DZ := hbad R (by simpa [Rs] using hR)
        _ = 2 * DZ * R.natDegree := by ring
    exact Nat.add_le_add (Nat.add_le_add hpair (le_refl _)) hbadR
  calc
    (∑ R ∈ Rs,
      ((if R.natDegree = 1 then L else C * R.natDegree) * R.natDegree +
        e * R.natDegree + bad R)) ≤
        ∑ R ∈ Rs,
          (C * DY * R.natDegree + e * R.natDegree + 2 * DZ * R.natDegree) :=
      Finset.sum_le_sum hterm
    _ = C * DY * (∑ R ∈ Rs, R.natDegree) +
          e * (∑ R ∈ Rs, R.natDegree) +
          2 * DZ * (∑ R ∈ Rs, R.natDegree) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ C * DY * DY + e * DY + 2 * DZ * DY := by
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left (C * DY) hsum)
          (Nat.mul_le_mul_left e hsum))
        (Nat.mul_le_mul_left (2 * DZ) hsum)
    _ = C * DY ^ 2 + e * DY + 2 * DZ * DY := by ring

/-- If every first-stage factor has degree at most `M`, the quadratic
capacity sum costs only `M * DY`. This isolates the genuinely hard case to
the presence of a factor whose degree exceeds `M`. -/
theorem sum_staged_R_capacities_le_of_degree_cap
    {ρ : Type*} [DecidableEq ρ] (Rs : Finset ρ)
    (d bad : ρ → Nat) (A e DZ DY M : Nat)
    (hdpos : ∀ r ∈ Rs, 0 < d r)
    (hdmax : ∀ r ∈ Rs, d r ≤ M)
    (hdsum : (∑ r ∈ Rs, d r) ≤ DY)
    (hbad : ∀ r ∈ Rs, bad r ≤ 2 * d r * DZ) :
    (∑ r ∈ Rs, (A * d r ^ 2 + e * d r + bad r)) ≤
      A * (M * DY) + e * DY + 2 * DZ * DY := by
  have hdsq : (∑ r ∈ Rs, d r ^ 2) ≤ M * DY := by
    calc
      (∑ r ∈ Rs, d r ^ 2) ≤ ∑ r ∈ Rs, M * d r := by
        apply Finset.sum_le_sum
        intro r hr
        simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_right (d r) (hdmax r hr)
      _ = M * (∑ r ∈ Rs, d r) := by rw [Finset.mul_sum]
      _ ≤ M * DY := Nat.mul_le_mul_left M hdsum
  have hbad' : ∀ r ∈ Rs, bad r ≤ 2 * DZ * d r := by
    intro r hr
    calc
      bad r ≤ 2 * d r * DZ := hbad r hr
      _ = 2 * DZ * d r := by ring
  calc
    (∑ r ∈ Rs, (A * d r ^ 2 + e * d r + bad r)) ≤
        ∑ r ∈ Rs, (A * d r ^ 2 + e * d r + 2 * DZ * d r) := by
      exact Finset.sum_le_sum fun r hr => Nat.add_le_add_left (hbad' r hr) _
    _ = A * (∑ r ∈ Rs, d r ^ 2) +
          e * (∑ r ∈ Rs, d r) + 2 * DZ * (∑ r ∈ Rs, d r) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ A * (M * DY) + e * DY + 2 * DZ * DY := by
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left A hdsq) (Nat.mul_le_mul_left e hdsum))
        (Nat.mul_le_mul_left (2 * DZ) hdsum)

/-- Normalized-factor specialization of the degree-capped staged capacity
bound. -/
theorem positive_normalizedFactors_staged_cap_le_of_degree_cap
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (bad : Polynomial (Polynomial (Polynomial F)) → Nat)
    (A e DZ DY M : Nat) (hQdeg : Q.natDegree ≤ DY)
    (hmax : ∀ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun R => 0 < R.natDegree), R.natDegree ≤ M)
    (hbad : ∀ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun R => 0 < R.natDegree), bad R ≤ 2 * R.natDegree * DZ) :
    (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun R => 0 < R.natDegree),
      (A * R.natDegree ^ 2 + e * R.natDegree + bad R)) ≤
      A * (M * DY) + e * DY + 2 * DZ * DY := by
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    fun R => 0 < R.natDegree
  have hsum : (∑ R ∈ Rs, R.natDegree) ≤ DY := by
    calc
      (∑ R ∈ Rs, R.natDegree) ≤
          ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
            R.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ DY := hQdeg
  apply sum_staged_R_capacities_le_of_degree_cap Rs Polynomial.natDegree bad
    A e DZ DY M
  · intro R hR
    exact (Finset.mem_filter.mp hR).2
  · intro R hR
    exact hmax R (by simpa [Rs] using hR)
  · exact hsum
  · intro R hR
    exact hbad R (by simpa [Rs] using hR)

end ProximityPrize.SubmissionLower
