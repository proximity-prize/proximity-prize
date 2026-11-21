import ProximityPrize.SubmissionLower.Fast069

/- The punctured-domain support transport is adapted from Dadon's PR 627, Fast067.
The agreement count, pruning cutoff and both Johnson certificates are for 69.25. -/
namespace Row6921
noncomputable section
open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark K1 CoreDefinitions Code
open ReedSolomon.HiddenDerivative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
local instance : NeZero (131072 : ℕ) := ⟨by decide⟩
abbrev ShortenedCap (n cap : ℕ) : Prop :=
  ∀ (d : Finset I), d.card ≤ n → ∀ u v (Γ : Finset K),
    (∀ γ ∈ Γ, K1_2.Pruning.BadOn node u v 131072 180130 d γ) → Γ.card ≤ cap

private def rolling (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => rolling f n + f n

private theorem rolling_eq (f : ℕ → ℕ) (n : ℕ) :
    rolling f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [rolling]
  | succ n ih => rw [rolling, sum_range_succ, ih]

private theorem shortened_from_weighted (N cap m B H : ℕ)
    (hB : B ≤ 2 * 131071 + 1)
    (hcert : ∀ n ≤ N, IsJohnsonWeightedCertificate n 131071 180130 m B
      (johnsonWeightedHeight n 131071 180130 m B))
    (hheight : ∀ n ≤ N, johnsonWeightedHeight n 131071 180130 m B ≤ H)
    (hprice : ⌊johnsonWeightedRefinedExceptionCount N 131071 180130 B H⌋ ≤ (cap : ℤ)) :
    ShortenedCap N cap := by
  classical
  letI : DecidableEq K := Classical.decEq K
  intro D hD u v Γ hΓ
  by_cases hA : 180130 ≤ D.card
  swap
  · have hzero : Γ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨S, hSD, hAS, _, _⟩ := hΓ γ hγ
      exact hA (hAS.trans (card_le_card hSD))
    simp [hzero]
  let e : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (α := D) (by simp)).symm
  let x : Fin D.card ↪ K :=
    ⟨fun j => node (e j).val, fun i j h => e.injective (Subtype.ext (IRSProfile.domain.injective h))⟩
  let u' (j : Fin D.card) := u (e j).val
  let v' (j : Fin D.card) := v (e j).val
  obtain ⟨exceptions, hcard, hexact⟩ := ReedSolomon.exists_weightedJohnson_line_exactCorrelatedPair
    x u' v' (hcert D.card hD) (by decide) (by decide) hA hB
  have hsub : Γ ⊆ exceptions := by
    intro γ hγ
    by_contra hnormal
    obtain ⟨S, hSD, hAS, ⟨P, hP, hval⟩, hnonjoint⟩ := hΓ γ hγ
    let f : S ↪ Fin D.card :=
      ⟨fun i => e.symm ⟨i.val, hSD i.property⟩,
        fun i j hh => Subtype.ext (congrArg (fun z : D => z.val) (e.symm.injective hh))⟩
    have hf (i : S) : (e (f i)).val = i.val := by simp [f]
    let hits := ReedSolomon.polynomialAgreementSet x (fun j => u' j + γ * v' j) P
    have hhits (i : S) : f i ∈ hits := by
      have h := hval i.val i.property
      simpa only [hits, ReedSolomon.polynomialAgreementSet, mem_filter, mem_univ, true_and,
        x, Function.Embedding.coeFn_mk, u', v', hf] using h
    have hinj : S.attach.map f ⊆ hits := by
      intro j hj
      obtain ⟨i, _, rfl⟩ := mem_map.mp hj
      exact hhits i
    have hA' : 180130 ≤ hits.card := hAS.trans (by simpa using card_le_card hinj)
    obtain ⟨pair, h0, h1, _, hsets⟩ := hexact γ hnormal P hP (by simpa only [hits] using hA')
    change hits = ReedSolomon.commonPolynomialAgreementSet x u' v' pair.1 pair.2 at hsets
    have hboth (i : S) : pair.1.eval (node i.val) = u i.val ∧
        pair.2.eval (node i.val) = v i.val := by
      have hi := hhits i
      rw [hsets] at hi
      simpa only [ReedSolomon.commonPolynomialAgreementSet, mem_filter, mem_univ, true_and,
        x, Function.Embedding.coeFn_mk, u', v', hf] using hi
    exact hnonjoint ⟨⟨pair.1, h0, fun i hi => (hboth ⟨i, hi⟩).1⟩,
      ⟨pair.2, h1, fun i hi => (hboth ⟨i, hi⟩).2⟩⟩
  have hmono : johnsonWeightedRefinedExceptionCount D.card 131071 180130 B
      (johnsonWeightedHeight D.card 131071 180130 m B) ≤
      johnsonWeightedRefinedExceptionCount N 131071 180130 B H := by
    let h := johnsonWeightedHeight D.card 131071 180130 m B
    have hh : h ≤ H := hheight D.card hD
    have hN : D.card - 131071 ≤ N - 131071 := Nat.sub_le_sub_right hD _
    have hN' : D.card - 131071 - 1 ≤ N - 131071 - 1 := Nat.sub_le_sub_right hN _
    have hslots : h + B + (2 * 131071 - 1) * h * (2 * B - 1) ≤
        H + B + (2 * 131071 - 1) * H * (2 * B - 1) :=
      Nat.add_le_add (Nat.add_le_add_right hh B)
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hh))
    unfold johnsonWeightedRefinedExceptionCount
    change (((2 * B - 1) * h : ℕ) : ℚ) + _ + _ ≤ (((2 * B - 1) * H : ℕ) : ℚ) + _ + _
    apply add_le_add
    · apply add_le_add
      · exact_mod_cast Nat.mul_le_mul_left (2 * B - 1) hh
      · apply mul_le_mul
        · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hN) (Nat.cast_nonneg _)
        · exact Nat.cast_le.mpr hslots
        · exact Nat.cast_nonneg _
        · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact_mod_cast Nat.mul_le_mul_right B hN'
  have hΓq : (Γ.card : ℚ) ≤
      johnsonWeightedRefinedExceptionCount N 131071 180130 B H :=
    (show (Γ.card : ℚ) ≤ exceptions.card by exact_mod_cast card_le_card hsub).trans
      (hcard.trans hmono)
  have hΓz := (Int.le_floor.mpr (by exact_mod_cast hΓq)).trans hprice
  exact_mod_cast hΓz


private theorem moments247107 :
    johnsonWeightedN 131071 180130 151 207 = 2835826552 ∧
    johnsonWeightedW 131071 180130 151 207 = 195218953800 ∧
    johnsonWeightedR 151 207 = 11476 ∧ johnsonWeightedT 151 207 = 573800 := by
  unfold johnsonWeightedN johnsonWeightedW johnsonWeightedR johnsonWeightedT johnsonWeightedU
  simp only [← rolling_eq]
  decide +kernel

theorem puncture_247107 : ShortenedCap 247039 16956296894856 := by
  apply shortened_from_weighted 247039 16956296894856 151 207 66256 (by decide)
  · intro n hn
    refine ⟨by decide, by decide, by decide, ?_, rfl⟩
    rw [moments247107.1, moments247107.2.2.1]
    omega
  · intro n hn
    unfold johnsonWeightedHeight johnsonWeightedHeightInt johnsonWeightedMoment johnsonWeightedSlope
    rw [moments247107.1, moments247107.2.1, moments247107.2.2.1, moments247107.2.2.2]
    change (max (207 : ℤ) ((195218953800 - (n : ℤ) * 573800) /
      (2835826552 - (n : ℤ) * 11476))).toNat ≤ 66256
    have hn' : (n : ℤ) ≤ 247039 := by exact_mod_cast hn
    have hden : 0 < (2835826552 : ℤ) - n * 11476 := by omega
    have hquot : (195218953800 - (n : ℤ) * 573800) / (2835826552 - n * 11476) < 66257 :=
      (Int.ediv_lt_iff_lt_mul hden).mpr (by omega)
    omega
  · norm_num [johnsonWeightedRefinedExceptionCount]

private theorem moments247716 :
    johnsonWeightedN 131071 180130 899 1235 = 100116651990 ∧
    johnsonWeightedW 131071 180130 899 1235 = 41197671935290 ∧
    johnsonWeightedR 899 1235 = 404550 ∧ johnsonWeightedT 899 1235 = 121095300 := by
  unfold johnsonWeightedN johnsonWeightedW johnsonWeightedR johnsonWeightedT johnsonWeightedU
  simp only [← rolling_eq]
  decide +kernel

theorem puncture_247716 : ShortenedCap 247465 3680066762208196 := by
  apply shortened_from_weighted 247465 3680066762208196 899 1235 2396553 (by decide)
  · intro n hn
    refine ⟨by decide, by decide, by decide, ?_, rfl⟩
    rw [moments247716.1, moments247716.2.2.1]
    omega
  · intro n hn
    unfold johnsonWeightedHeight johnsonWeightedHeightInt johnsonWeightedMoment johnsonWeightedSlope
    rw [moments247716.1, moments247716.2.1, moments247716.2.2.1, moments247716.2.2.2]
    change (max (1235 : ℤ) ((41197671935290 - (n : ℤ) * 121095300) /
      (100116651990 - (n : ℤ) * 404550))).toNat ≤ 2396553
    have hn' : (n : ℤ) ≤ 247465 := by exact_mod_cast hn
    have hden : 0 < (100116651990 : ℤ) - n * 404550 := by omega
    have hquot : (41197671935290 - (n : ℤ) * 121095300) / (100116651990 - n * 404550) < 2396554 :=
      (Int.ediv_lt_iff_lt_mul hden).mpr (by omega)
    omega
  · norm_num [johnsonWeightedRefinedExceptionCount]

abbrev block (u : Words) := stacked p node (u 0) (u 1) 49058 82014
abbrev nullity (u : Words) := GenericLayer.genericNullity (block u)
abbrev firstRank (u : Words) := GenericLayer.genericRank (hankel node (u 0) (u 1) 49058 82014)
def radius : ℝ := (claimedRadius 335932963 1073741824 : ℝ)
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius

theorem count_nullity_le_six (u : Words) (hfirst : firstRank u = 49058)
    (hr : nullity u ≤ 6) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ 177952993749663315 := by
  obtain ⟨W⟩ := K1_2.Pruning.witnessFamily_of_MCA IRSProfile.domain u 131072 180130
    (by omega) radius (by
      intro T hT
      norm_num [IRSProfile.card_index,radius,claimedRadius] at hT
      by_contra! h
      have he : (T.card : ℝ) ≤ 180129 := by exact_mod_cast (show T.card ≤ 180129 by omega)
      linarith) Γ hΓ
  have hcore : K1_2.Pruning.PuncturedCap node 131072 180130 66900 16956296894856 :=
    puncture_247107
  let φ := algebraMap K[X] Frac
  have h := K1_2.Pruning.stacked_pruning_count_of_card p φ (IsFractionRing.injective K[X] Frac)
    node IRSProfile.domain.injective Native.native_domain_fixed (u 0) (u 1)
    262144 131072 180130 49058 66900 16956296894856 IRSProfile.card_index
    (by decide) (by decide) hfirst hcore Γ W
  let R := GenericLayer.genericRank (block u)
  have hsum : R + nullity u = 82015 := by
    simpa [R, nullity, block] using GenericLayer.rank_add_nullity (block u)
  change (Γ.card : ℚ) ≤ K1_2.Pruning.bound (49058+p*(R-49058)) 16956296894856
    (1+(180130 : ℚ)/(66900+1)) (82015-R) at h
  have hn : 82015-R = nullity u := by omega
  have hg : R-49058 = 32957-nullity u := by omega
  rw [hn,hg] at h
  generalize nullity u = r at h hr
  have bound : K1_2.Pruning.bound (49058+p*(32957-r)) 16956296894856
      (1+(180130 : ℚ)/(66900+1)) r < 177952993749663316 := by
    interval_cases r <;> norm_num [K1_2.Pruning.bound, K1.p, Native.p]
  have hfinal : Γ.card < 177952993749663316 := by exact_mod_cast lt_of_le_of_lt h bound
  omega

end
end Row6921
