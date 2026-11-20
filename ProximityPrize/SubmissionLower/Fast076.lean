import ProximityPrize.SubmissionLower.Fast000
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast003
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast011
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast050
import ProximityPrize.SubmissionLower.Fast054
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast061
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast066
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast065
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2_4Split
import ProximityPrize.SubmissionLower.Fast062
import ProximityPrize.SubmissionLower.Pack_K1_14_3Split
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast035
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2Split
import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Aux3
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_7Proof
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.Fast064
import ProximityPrize.SubmissionLower.Fast067
import ProximityPrize.SubmissionLower.Fast044
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Split
import ProximityPrize.SubmissionLower.Fast069
set_option Elab.async false

section PackSource_K1_2Counting
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K1_2
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K1

local instance : NeZero (131072 : ℕ) := ⟨by decide⟩

/-- The donor's exact-support pruning argument, instantiated on the
benchmark's stacked matrix and the small shortened-domain core. -/
theorem count_le_six (core : ShortenedCap 247465 42657721657869)
    (u : Words) (hfirst : firstRank u = 49193) (hr : nullity u ≤ 6)
    (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 173643196181962951 := by
  obtain ⟨W⟩ := Pruning.witnessFamily_of_MCA IRSProfile.domain u 131072 180265 (by omega)
    Native.radius (by
      intro T hT
      norm_num [IRSProfile.card_index, Native.radius, claimedRadius] at hT ⊢
      exact hT) Γ hΓ
  have hpunct : Pruning.PuncturedCap node 131072 180265 67200 Pruning.coreK := by
    exact core
  let φ := algebraMap K[X] Frac
  have hp := Pruning.stacked_pruning_count_of_card p φ (IsFractionRing.injective K[X] Frac)
    node IRSProfile.domain.injective Native.native_domain_fixed (u 0) (u 1)
    262144 131072 180265 49193 67200 Pruning.coreK IRSProfile.card_index
    (by omega) (by omega) hfirst hpunct Γ W
  change (Γ.card : ℚ) ≤ Pruning.bound (49193 + p * (stackRank u - 49193))
    Pruning.coreK (1 + (180265 : ℚ) / ((67200 : ℚ) + 1)) (81880 - stackRank u) at hp
  rw [actual_stackRank] at hp
  have hr' : 81880 - (81880 - nullity u) = nullity u := by omega
  have hδ : 81880 - nullity u - 49193 = 32687 - nullity u := by omega
  rw [hr', hδ] at hp
  apply Pruning.production_count_le (nullity u) Γ.card hr
  have hC : (1 + (180265 : ℚ) / (67200 + 1)) = Pruning.productionC := by
    norm_num [Pruning.productionC]
  rw [hC] at hp
  exact hp

theorem rank_book (u : Words) (hfirst : firstRank u = 49193) (Γ : Finset K) :
    (abnormalSlopes u Γ).card ≤ rankReserve (nullity u) := by
  classical
  have hb := Strata.two_block_rank_exception_count p node (u 0) (u 1) 49193 81879
    (nullity u) (actual_stackRank u) hfirst (abnormalSlopes u Γ) (by
      intro γ hγ
      rw [← actual_stackRank u]
      exact (Finset.mem_filter.mp hγ).2)
  have he : 81879 + 1 - nullity u - 49193 = 32687 - nullity u := by omega
  rw [he] at hb
  exact hb

theorem padding_le_eight (r : ℕ) : padding r ≤ 8 := by
  unfold padding
  split_ifs <;> omega

theorem fixedLimit_le (r : ℕ) : fixedLimit r ≤ 14678 := by
  unfold fixedLimit
  split_ifs <;> omega

theorem planePrice_nonneg (A a b C : ℕ) : 0 ≤ planePrice A a b C := by
  dsimp only [planePrice]
  split_ifs
  · unfold oldPlanePrice
    positivity
  · apply le_min
    · unfold oldPlanePrice
      positivity
    · apply le_trans _ (le_max_left _ _)
      unfold oldPlanePrice
      positivity

/-- Apply one child count per deletion union and keep the rational child
price through the finite incidence inequality. -/
theorem padded_count {u : Words} {D : Finset I} {Γ : Finset K} {r g : ℕ}
    (F : PaddedFamily u D Γ r g) (hr : 7 ≤ r) (hr16 : r ≤ 16) (hg : g ≤ fixedLimit r)
    (hchild : ∀ J ∈ D.powersetCard (deletionSize r),
      ((childSlopes F J).card : ℚ) ≤ nativePlanePrice r g) :
    (Γ.card : ℚ) ≤ incidenceRatio r g * nativePlanePrice r g := by
  classical
  have hg' := hg.trans (fixedLimit_le r)
  have hj := padding_le_eight r
  let q := nativePlanePrice r g
  let n := q.num.toNat
  let d := q.den
  have hd : (0 : ℚ) < d := by exact_mod_cast Rat.den_pos q
  have hn : (n : ℚ) = (q.num : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg]
    exact Rat.num_nonneg.mpr (planePrice_nonneg _ _ _ _)
  have hq : (n : ℚ) / d = q := by rw [hn, Rat.num_div_den]
  have hfit : r - 1 + padding r ≤ 81879 - g := by omega
  have hden : 0 < (incidenceDenominator r g : ℚ) := by
    unfold incidenceDenominator
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hfit)
      (Nat.choose_pos (by omega : padding r ≤ 180265 - 1))
  have hcount := Mixed.shared_mixed_rational_count node (u 0) (u 1)
    IRSProfile.domain.injective D Γ 131072 180265 (81879 - g) (r - 1) (padding r) n d
    (fun γ => goodSet u D γ (F.decoder γ)) (fun γ => errorSet u D γ (F.decoder γ)) F.slack
    (by omega) hfit (by omega)
    (by
      intro γ hγ
      rcases F.witness γ hγ with ⟨hs, hS, hE, hbad⟩
      have hsub : goodSet u D γ (F.decoder γ) ⊆ D := by
        intro i hi
        exact (mem_filter.mp hi).1
      exact ⟨hs, hS, hE, Finset.sdiff_disjoint, union_subset sdiff_subset hsub, hbad⟩)
    (by
      intro J hJ
      have hh := hchild J hJ
      change ((childSlopes F J).card : ℚ) ≤ q at hh
      rw [← hq] at hh
      have hmul := (le_div_iff₀ hd).mp hh
      have hc : (childSlopes F J).card * d ≤ n := by exact_mod_cast hmul
      have hsame : childSlopes F J = Γ.filter (fun γ =>
          J ∈ Mixed.mixedDeletions node (u 0) (u 1) 131072
            (r - 1 - F.slack γ + padding r) (F.slack γ + padding r)
            (errorSet u D γ (F.decoder γ)) (goodSet u D γ (F.decoder γ))) := by
        ext γ
        simp only [childSlopes, mem_filter]
        unfold mixedChoices Mixed.mixedDeletions Mixed.goodDeletions JointOn Mixed.JointOn
        rfl
      rw [hsame, mul_comm] at hc
      exact hc)
  change d * incidenceDenominator r g * Γ.card ≤ D.card.choose (deletionSize r) * n at hcount
  rw [F.domain_card] at hcount
  have hcountQ : (d : ℚ) * incidenceDenominator r g * Γ.card ≤
      ((262144 - g).choose (deletionSize r) : ℚ) * n := by exact_mod_cast hcount
  change (Γ.card : ℚ) ≤ incidenceRatio r g * q
  rw [← hq, incidenceRatio, div_mul_div_comm]
  apply (le_div_iff₀ (mul_pos hden hd)).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hcountQ

end
end K1_2
end PackSource_K1_2Counting

section PackSource_K1_2Arithmetic
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K1_2

private theorem new_price_mono (β : ℚ) (A a x y : ℕ)
    (hβ : 0 ≤ β) (ha : 0 < a) (hxy : x ≤ y) :
    newPlanePrice β A a x ≤ newPlanePrice β A a y := by
  have hx : (0 : ℚ) ≤ x := by positivity
  have hy : (0 : ℚ) ≤ y := by positivity
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hxy' : (x : ℚ) ≤ y := by exact_mod_cast hxy
  have hfrac : (x : ℚ) / (a + x) ≤ y / (a + y) := by
    apply (div_le_div_iff₀ (by linarith : (0 : ℚ) < a + x)
      (by linarith : (0 : ℚ) < a + y)).mpr
    nlinarith
  have hsquare : (x : ℚ)^2 / (a + x) ≤ (y : ℚ)^2 / (a + y) := by
    calc
      (x : ℚ)^2 / (a + x) = x * (x / (a + x)) := by ring
      _ ≤ y * (y / (a + y)) := mul_le_mul hxy' hfrac (by positivity) hy
      _ = (y : ℚ)^2 / (a + y) := by ring
  calc
    newPlanePrice β A a x = 2 * β * ((x : ℚ)^2 / (a + x) * (A + a + x)) := by
      unfold newPlanePrice
      ring
    _ ≤ 2 * β * ((y : ℚ)^2 / (a + y) * (A + a + y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hsquare (by linarith) (by positivity) (by positivity)
    _ = newPlanePrice β A a y := by unfold newPlanePrice; ring

private def newNativePrice (r g : ℕ) : ℚ :=
  let a := childRows r
  let A := 131072 + a
  newPlanePrice (curveBeta A a (cutoff r)) A a (reducedHeight r g)

private theorem new_native_mono (r lo g : ℕ) (hl : lo ≤ g) :
    newNativePrice r g ≤ newNativePrice r lo := by
  have hj := padding_le_eight r
  dsimp only [newNativePrice]
  apply new_price_mono
  · unfold curveBeta
    positivity
  · unfold childRows
    omega
  · unfold reducedHeight
    omega

private theorem threshold_check (r : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16) :
    let a := childRows r
    let A := 131072 + a
    let q := planeThreshold A a (cutoff r)
    q < reducedHeight r (fixedLimit r) ∧
      oldPlanePrice A a q ≤ newNativePrice r (fixedLimit r) := by
  interval_cases r <;> decide +kernel

private theorem plane_le_new (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) : nativePlanePrice r g ≤ newNativePrice r g := by
  have h := threshold_check r hr hr16
  dsimp only at h
  have hH : reducedHeight r (fixedLimit r) ≤ reducedHeight r g := by
    unfold reducedHeight
    omega
  have hq := h.1.trans_le hH
  dsimp only [nativePlanePrice, planePrice]
  rw [ite_eq_right (not_le.mpr hq)]
  change min _ (max _ (newNativePrice r g)) ≤ newNativePrice r g
  apply min_le_of_right_le
  exact max_le (h.2.trans (new_native_mono r g _ hg)) le_rfl

private theorem reserve_le (r lo g : ℕ) (hr : 7 ≤ r) (hl : lo ≤ g) :
    extraReserve r g ≤ extraReserve r lo := by
  have hH : reducedHeight r g ≤ reducedHeight r lo := by unfold reducedHeight; omega
  have hd : 49193 - reducedHeight r lo ≤ 49193 - reducedHeight r g := by omega
  have hdpos : 0 < 49193 - reducedHeight r lo := by unfold reducedHeight; omega
  have hz :
      (2130706433 * 49193 + reducedHeight r g) / (49193 - reducedHeight r g) ≤
      (2130706433 * 49193 + reducedHeight r lo) / (49193 - reducedHeight r lo) :=
    (Nat.div_le_div_right (Nat.add_le_add_left hH _)).trans (Nat.div_le_div_left hd hdpos)
  have hn : 49193 / (49193 - reducedHeight r g) ≤ 49193 / (49193 - reducedHeight r lo) :=
    Nat.div_le_div_left hd hdpos
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hH) hz)
    (Nat.mul_le_mul_right (2130706433 + 1) hn)

-- The descending factorial evaluates using recursion on the small
-- lower argument of the binomial coefficient.
private def fastChoose (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

private theorem fastChoose_eq (n k : ℕ) : fastChoose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

private def intervalRatio (r lo hi : ℕ) : ℚ :=
  (fastChoose (262144 - lo) (deletionSize r) : ℚ) /
    (fastChoose (81879 - hi) (r - 1 + padding r) * fastChoose (180265 - 1) (padding r) : ℕ)

private theorem ratio_le_interval (r g lo hi : ℕ) (hr16 : r ≤ 16)
    (hl : lo ≤ g) (hh : g ≤ hi) (hhi : hi ≤ fixedLimit r) :
    incidenceRatio r g ≤ intervalRatio r lo hi := by
  have hj := padding_le_eight r
  have hhi' := hhi.trans (fixedLimit_le r)
  have htop := Nat.choose_le_choose (deletionSize r) (show 262144 - g ≤ 262144 - lo by omega)
  have hbot : incidenceDenominator r hi ≤ incidenceDenominator r g := by
    unfold incidenceDenominator
    exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (by omega))
  have hpos : 0 < incidenceDenominator r hi := by
    unfold incidenceDenominator
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hpos' : (0 : ℚ) < incidenceDenominator r hi := by exact_mod_cast hpos
  simp only [intervalRatio, fastChoose_eq, incidenceRatio]
  change ((262144 - g).choose (deletionSize r) : ℚ) / incidenceDenominator r g ≤
    ((262144 - lo).choose (deletionSize r) : ℚ) / incidenceDenominator r hi
  exact div_le_div₀ (by positivity) (by exact_mod_cast htop) hpos' (by exact_mod_cast hbot)

private def intervalBound (r lo hi : ℕ) : ℚ :=
  ((rankReserve r + extraReserve r lo : ℕ) : ℚ) +
    intervalRatio r lo hi * newNativePrice r lo

private theorem native_le_interval (r g lo hi : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hl : lo ≤ g) (hh : g ≤ hi) (hhi : hi ≤ fixedLimit r) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g ≤ intervalBound r lo hi := by
  unfold intervalBound
  apply add_le_add
  · exact_mod_cast Nat.add_le_add_left (reserve_le r lo g hr hl) (rankReserve r)
  · exact mul_le_mul (ratio_le_interval r g lo hi hr16 hl hh hhi)
      ((plane_le_new r g hr hr16 (hh.trans hhi)).trans (new_native_mono r lo g hl))
      (planePrice_nonneg _ _ _ _) (by unfold intervalRatio; positivity)

private def endpoints (r : ℕ) : List ℕ :=
  if r ≤ 13 then [14678]
  else if r = 14 then [7339, 14678]
  else if r = 15 then [7339, 11009, 14678]
  else [3606, 7213, 9017, 10820, 11722, 12624, 13075, 13526, 13752, 13977, 14090,
    14202, 14259, 14315, 14343, 14371, 14385, 14399, 14406, 14413, 14417, 14420,
    14422, 14424, 14425, 14426, 14427]

private def certified (r : ℕ) : ℕ → List ℕ → Bool
  | lo, [] => decide (fixedLimit r < lo)
  | lo, hi :: rest =>
    decide (lo ≤ hi ∧ hi ≤ fixedLimit r ∧ intervalBound r lo hi ≤ 181966665710181665) &&
      certified r (hi + 1) rest

private theorem covers (r lo g : ℕ) (cuts : List ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hl : lo ≤ g) (hg : g ≤ fixedLimit r) (hcert : certified r lo cuts = true) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g ≤ 181966665710181665 := by
  induction cuts generalizing lo with
  | nil =>
    have he : fixedLimit r < lo := of_decide_eq_true hcert
    omega
  | cons hi rest ih =>
    obtain ⟨hcurrent, hrest⟩ := Bool.and_eq_true_iff.mp hcert
    obtain ⟨_, hhi, hbound⟩ :
        lo ≤ hi ∧ hi ≤ fixedLimit r ∧ intervalBound r lo hi ≤ 181966665710181665 :=
      of_decide_eq_true hcurrent
    by_cases hh : g ≤ hi
    · exact (native_le_interval r g lo hi hr hr16 hl hh hhi).trans hbound
    · exact ih (hi + 1) (by omega) hrest

private theorem endpoints_checked (r : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16) :
    certified r 0 (endpoints r) = true := by
  interval_cases r <;> decide +kernel

theorem arithmetic_bound (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16) (hg : g ≤ fixedLimit r) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g ≤ 181966665710181665 :=
  covers r 0 g (endpoints r) hr hr16 (Nat.zero_le g) hg (endpoints_checked r hr hr16)

end K1_2
end PackSource_K1_2Arithmetic

section PackSource_K1_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K1_2
noncomputable section

open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark
open K1

/-- The primitive wide left pair has the shifted-minor seed-height bound. -/
def c1 : Prop :=
  ∀ (u : Words), MiddleGuard u → ∀ (T : TwoActive u) (R : Relation T),
    ∀ i, (R.coefficients i).natDegree ≤ 6347474207

/-- Once the original rank drops have been removed, only the reduced
resultant and normalization reserves are used to prepare the marked family. -/
def c2 : Prop :=
  ∀ (u : Words), MiddleGuard u → ∀ (T : TwoActive u) (R : Relation T),
    ¬ MovingGCD R → ¬ InvalidLeft R → NormalSaturation R →
    ∀ Γ : Finset K, Γ.Nonempty → BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
      let r := nullity u
      let g := (fixedNodes R).card
      let D := Finset.univ \ fixedNodes R
      g ≤ fixedLimit r →
        ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ extraReserve r g ∧
          ∃ _ : PaddedFamily u D (Γ \ book) r g,
          ∃ Q : ReducedRelation u D (reducedHeight r g),
            ∀ γ ∈ Γ \ book, RegularAt Q γ

/-- At a fixed deletion union there is one exact child plane across the
physical error sizes. The marked decoder is unchanged by puncturing. -/
def c3 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (r g : ℕ),
    7 ≤ r → r ≤ 16 → g ≤ fixedLimit r →
    ∀ (F : PaddedFamily u D Γ r g) (Q : ReducedRelation u D (reducedHeight r g)),
      (∀ γ ∈ Γ, RegularAt Q γ) →
      ∀ J ∈ D.powersetCard (deletionSize r), (childSlopes F J).Nonempty →
        RegularPlane u (D \ J) (childRows r) (childErrors r g)
          (childSlopes F J) F.decoder

/-- The carried primitive-box consumer for one regular punctured input. -/
def c4 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a b C : ℕ),
    1 ≤ b → b ≤ a → 1 ≤ C → C ≤ a →
    RegularPlane u D a (a + b) Γ P →
      (Γ.card : ℚ) ≤ planePrice (131072 + a) a b C

private theorem main_height_guards (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) :
    1 ≤ reducedHeight r g ∧ reducedHeight r g ≤ childRows r ∧
      1 ≤ cutoff r ∧ cutoff r ≤ childRows r := by
  have hpad := padding_le_eight r
  have hsmall := hg.trans (fixedLimit_le r)
  unfold reducedHeight childRows cutoff
  split_ifs <;> omega

private theorem normal_count_large_g (hcore : ShortenedCap 247716 185328514776456)
    (u : Words) (T : TwoActive u) (R : Relation T) (hsat : NormalSaturation R)
    (Γ : Finset K) (hΓ : BadFamily u Γ) (hn : ∀ γ ∈ Γ, Normal u γ)
    (hg : fixedLimit (nullity u) < (fixedNodes R).card) :
    Γ.card ≤ 185328514776456 := by
  classical
  refine hcore (Finset.univ \ fixedNodes R) ?_ (u 0) (u 1) Γ ?_
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index]
    unfold fixedLimit at hg
    split_ifs at hg <;> omega
  · intro γ hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
    have sat := hsat γ (hn γ hγ) M
    refine ⟨M.support, ?_, M.agreement, ⟨M.decoder, M.degree, M.hits⟩, M.nonjoint⟩
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi' => sat.fixed_errors i hi' (M.hits i hi)⟩

private theorem add_rank_book (u : Words) (Γ : Finset K) (hfirst : firstRank u = 49193)
    (b : ℕ) (hb : (normalSlopes u Γ).card ≤ b) :
    Γ.card ≤ rankReserve (nullity u) + b := by
  classical
  have hr := rank_book u hfirst Γ
  have hsplit := Finset.card_filter_add_card_filter_not (s := Γ) (p := Normal u)
  change (normalSlopes u Γ).card + (abnormalSlopes u Γ).card = Γ.card at hsplit
  omega

private theorem middle_count (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (u : Words) (hm : MiddleGuard u)
    (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 181966665710181665 := by
  classical
  let r := nullity u
  have hr : 7 ≤ r := hm.1
  have hr16 : r ≤ 16 := hm.2.1
  have hfirst := hm.2.2.1
  have hrank : rankReserve r ≤ 69631486279633 := by
    unfold rankReserve
    have hh : 32687 - r ≤ 32680 := by omega
    have hmul := Nat.mul_le_mul_left 2130706433 hh
    omega
  obtain ⟨T⟩ := two_active_of_positive u (by omega) hm.2.2.2.1 hm.2.2.2.2.1
  let R : Relation T := Strata.native_lemmaT_of_two_active_level u r
    T.a T.b T.c hr T.ab T.active T.inactive T.top T.degreeSum T.nullitySum T.level
  have hH : T.height < 49193 := by
    have := T.degreeSum
    have := T.nullitySum
    have := T.top
    unfold TwoActive.height
    omega
  have hsat := saturation_of_height u T R hH
  let N := normalSlopes u Γ
  have hN : BadFamily u N := normal_badFamily hΓ
  have hn : ∀ γ ∈ N, Normal u γ := normal_on_normalSlopes
  by_cases hnon : N.Nonempty
  swap
  · have hnempty := Finset.not_nonempty_iff_eq_empty.mp hnon
    have hh := add_rank_book u Γ hfirst 0 (by change N.card ≤ 0; simp [hnempty])
    change Γ.card ≤ rankReserve r + 0 at hh
    omega
  by_cases hmov : MovingGCD R
  · have hcount := K1_6.normal_growth_count R (h1 u hm T R) hmov hsat N hN hn
    have hh := add_rank_book u Γ hfirst _ hcount
    change Γ.card ≤ rankReserve r + 1663952278519808 at hh
    omega
  have hinv : ¬ InvalidLeft R := by
    obtain ⟨γ, hγ⟩ := hnon
    obtain ⟨M⟩ := bad_mark u N hN γ hγ
    exact (hsat γ (hn γ hγ) M).valid
  let g := (fixedNodes R).card
  by_cases hg : g ≤ fixedLimit r
  · obtain ⟨book, hbook, hfee, F, Q, hreg⟩ := h2 u hm T R hmov hinv hsat N hnon hN hn hg
    obtain ⟨hb, hba, hc, hca⟩ := main_height_guards r g hr hr16 hg
    have hp := padded_count F hr hr16 hg (by
      intro J hJ
      by_cases hJE : (childSlopes F J).Nonempty
      · have hplane := h3 u _ _ r g hr hr16 hg F Q hreg J hJ hJE
        exact h4 u _ _ F.decoder (childRows r) (reducedHeight r g) (cutoff r) hb hba hc hca hplane
      · rw [Finset.not_nonempty_iff_eq_empty.mp hJE, Finset.card_empty, Nat.cast_zero]
        exact planePrice_nonneg _ _ _ _)
    have hsolid := Finset.card_sdiff_add_card_eq_card hbook
    have hsplit : Γ.card ≤ rankReserve r + ((N \ book).card + book.card) := by
      rw [hsolid]
      exact add_rank_book u Γ hfirst _ le_rfl
    have hsplit' : (Γ.card : ℚ) ≤ (rankReserve r : ℚ) + ((N \ book).card : ℚ) + book.card := by
      exact_mod_cast (by simpa only [Nat.add_assoc] using hsplit)
    have hfee' : (book.card : ℚ) ≤ extraReserve r g := by exact_mod_cast hfee
    have hprice := arithmetic_bound r g hr hr16 hg
    push_cast at hprice
    have hfinal : (Γ.card : ℚ) ≤ 181966665710181665 := by linarith
    exact_mod_cast hfinal
  · have hc := normal_count_large_g shortened_large u T R hsat N hN hn (Nat.lt_of_not_ge hg)
    have hh := add_rank_book u Γ hfirst _ hc
    change Γ.card ≤ rankReserve r + 185328514776456 at hh
    omega

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : K1.c2 := by
  intro u Γ hu hΓ
  by_cases hd : firstRank u < 49193
  · exact (K1_3.proof u Γ hd hΓ).trans (by decide)
  have hfirst : firstRank u = 49193 := by have := firstRank_le u; omega
  by_cases hlow : nullity u ≤ 6
  · exact (count_le_six shortened_small u hfirst hlow Γ hΓ).trans (by decide)
  by_cases ht : TypeAtMostOne u
  · exact (Native.native_type_one_MCA_count u ht Γ hΓ).trans (by decide)
  by_cases hp : HomogeneousPrincipal u
  · exact (K1_4.proof u Γ hp hΓ).trans (by decide)
  by_cases hk : ConstantKernel u
  · exact (K1_5.proof u Γ hk hΓ).trans (by decide)
  exact middle_count h1 h2 h3 h4 u
    ⟨by omega, hu, hfirst, ht, hp, hk⟩ Γ hΓ

end
end K1_2
end PackSource_K1_2Split

section PackSource_K1_2_3Marks
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K1_2_3
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2

theorem child_parameters (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) :
    reducedHeight r g ≤ childRows r ∧
      0 < childErrors r g ∧ childErrors r g + 1 < p ∧
      262144 - g - deletionSize r = 131072 + childRows r + childErrors r g := by
  have hp := padding_le_eight r
  have hg' := hg.trans (fixedLimit_le r)
  change _ ∧ _ ∧ childErrors r g + 1 < 2130706433 ∧ _
  simp only [childErrors, childRows, reducedHeight, deletionSize]
  omega

theorem child_mark {u : Words} {D : Finset I} {Γ : Finset K} {r g : ℕ}
    (F : PaddedFamily u D Γ r g) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) {J : Finset I} {γ : K} (hγ : γ ∈ childSlopes F J) :
    γ ∈ Γ ∧ (F.decoder γ).degree < 131072 ∧
      (errorSet u (D \ J) γ (F.decoder γ)).card = childErrors r g ∧
      ¬ JointOn u (goodSet u (D \ J) γ (F.decoder γ)) := by
  classical
  obtain ⟨hΓ, hJ⟩ := Finset.mem_filter.mp hγ
  obtain ⟨hslack, _, herrors, _⟩ := F.witness γ hΓ
  let S := goodSet u D γ (F.decoder γ)
  let E := errorSet u D γ (F.decoder γ)
  change J ∈ mixedChoices u (r - 1 - F.slack γ + padding r) (F.slack γ + padding r) E S at hJ
  obtain ⟨⟨B, C⟩, hmem, rfl⟩ := Finset.mem_image.mp hJ
  obtain ⟨hB, hC⟩ := Finset.mem_product.mp hmem
  obtain ⟨hBE, hBc⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨hCS, _⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1
  have hbad := (Finset.mem_filter.mp hC).2
  have hgood : goodSet u (D \ (B ∪ C)) γ (F.decoder γ) = S \ C := by
    ext i
    have hBnot (h : i ∈ B) : i ∉ S := (Finset.mem_sdiff.mp (hBE h)).2
    simp only [S, goodSet, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union] at hBnot ⊢
    tauto
  have herr : errorSet u (D \ (B ∪ C)) γ (F.decoder γ) = E \ B := by
    ext i
    have hCs (h : i ∈ C) : i ∈ S := hCS h
    simp only [E, errorSet, S, goodSet, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_union] at hCs ⊢
    tauto
  refine ⟨hΓ, F.degree γ hΓ, ?_, hgood.symm ▸ hbad⟩
  rw [herr, Finset.card_sdiff_of_subset hBE]
  change E.card = _ at herrors
  rw [herrors, hBc]
  have hp := padding_le_eight r
  have hg' := hg.trans (fixedLimit_le r)
  unfold childErrors childRows reducedHeight
  omega

theorem plane_at_slope (u : Words) (D : Finset I) (a R : ℕ) (γ : K) :
    (planeMatrix u D a R).map (onGraph γ) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        (fun i : D => node i.val) (fun i : D => u 0 i.val + γ * u 1 i.val) a R := by
  apply Matrix.ext
  intro ⟨b, l⟩ j
  let x : D → K := fun i => node i.val
  have hs := Principal.syndrome_linear x (fun i : D => u 0 i.val)
    (fun i : D => u 1 i.val) 1 γ (l.val + j.val)
  simp only [one_mul] at hs
  let A := syndrome x (fun i : D => u 0 i.val) (l.val + j.val)
  let B := syndrome x (fun i : D => u 1 i.val) (l.val + j.val)
  have hpow : frobenius K p (A + γ * B) = A ^ p + γ ^ p * B ^ p := by
    simp only [map_add, map_mul, frobenius_def]
  fin_cases b
  · change (onGraph γ) (Polynomial.C (R := K[X]) (Polynomial.C (R := K) A + Polynomial.X (R := K) * Polynomial.C (R := K) B)) =
      syndrome x (fun i : D => u 0 i.val + γ * u 1 i.val) (l.val + j.val)
    simpa only [onGraph, coe_eval₂RingHom, eval₂_C, coe_evalRingHom, eval_add,
      eval_mul, eval_C, eval_X, A, B] using hs.symm
  · change (onGraph γ) (Polynomial.C (R := K[X]) (Polynomial.C (R := K) (A ^ p)) + Polynomial.X (R := K[X]) * Polynomial.C (R := K[X]) (Polynomial.C (R := K) (B ^ p))) =
      frobenius K p (syndrome x (fun i : D => u 0 i.val + γ * u 1 i.val) (l.val + j.val))
    rw [hs]
    change (onGraph γ) (Polynomial.C (R := K[X]) (Polynomial.C (R := K) (A ^ p)) + Polynomial.X (R := K[X]) * Polynomial.C (R := K[X]) (Polynomial.C (R := K) (B ^ p))) =
      frobenius K p (A + γ * B)
    rw [hpow]
    simp only [onGraph, coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
      coe_evalRingHom, eval_C]


private theorem eval_atSlope (P : Bivar) (a γ : K) :
    (atSlope P γ).eval a = (P.eval (C a)).eval γ := by
  simpa only [atSlope, Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (C a) (p := P))

private theorem specialize_relation {u : Words} {D D' : Finset I} {H : ℕ}
    (Q : ReducedRelation u D H) (hsub : D' ⊆ D) (γ : K) :
    Strata.TwistedRelation (frobenius K p) (fun i : D' => node i.val)
      (fun i : D' => u 0 i.val + γ * u 1 i.val) 131072 H
      (atSlope Q.U γ) (atSlope Q.V γ) (atSlope Q.output γ) := by
  refine ⟨natDegree_map_le.trans (le_max_left _ _ |>.trans_eq Q.height),
    natDegree_map_le.trans (le_max_right _ _ |>.trans_eq Q.height),
    degree_map_le.trans_lt Q.output_degree, ?_⟩
  intro i
  have hn := Q.nodes i.val (by simp [hsub i.property])
  have he := congrArg (evalRingHom γ) hn
  simpa only [map_add, map_mul, coe_evalRingHom, eval_C, eval_X, eval_pow,
    ← eval_atSlope, frobenius_def, add_pow_expChar, mul_pow] using he

theorem evaluated_rank {u : Words} {D D' : Finset I} {H a : ℕ}
    (Q : ReducedRelation u D H) (hsub : D' ⊆ D) (hH : H ≤ a) (hR : 0 < a + H)
    (hD : D'.card = 131072 + a + (a + H))
    (γ : K) (hregular : RegularAt Q γ) (P : K[X]) (hP : P.degree < 131072)
    (hE : (errorSet u D' γ P).card = a + H) :
    ((planeMatrix u D' a (a + H)).map (onGraph γ)).rank = a + H := by
  classical
  let x : D' → K := fun i => node i.val
  let w : D' → K := fun i => u 0 i.val + γ * u 1 i.val
  let S := (goodSet u D' γ P).subtype (· ∈ D')
  let E := (errorSet u D' γ P).subtype (· ∈ D')
  have hgood (i : D') : i ∈ S ↔ P.eval (x i) = w i := by
    simp [S, goodSet, x, w, Finset.mem_subtype, i.property]
  have herr (i : D') : i ∈ E ↔ P.eval (x i) ≠ w i := by
    simp [E, errorSet, goodSet, x, w, Finset.mem_subtype, i.property]
  have hEc : E.card = a + H := by
    have hmap : E.map (Function.Embedding.subtype (· ∈ D')) = errorSet u D' γ P :=
      Finset.subtype_map_of_mem (fun i hi => (Finset.mem_sdiff.mp hi).1)
    rw [← Finset.card_map (f := Function.Embedding.subtype (· ∈ D')), hmap, hE]
  have hSize : Fintype.card D' = 131072 + a + (a + H) := by
    rw [Fintype.card_coe, hD]
  have hSc : 131072 + H ≤ S.card := by
    have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset D')) (p := fun i => P.eval (x i) = w i)
    have hS' : S = Finset.univ.filter (fun i => P.eval (x i) = w i) := by
      ext i
      simp [hgood]
    have hE' : E = Finset.univ.filter (fun i => P.eval (x i) ≠ w i) := by
      ext i
      simp [herr]
    rw [← hS', ← hE', Finset.card_univ, hSize, hEc] at hcard
    omega
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have hfix (i : D') : frobenius K p (x i) = x i := Native.native_domain_fixed i.val
  have hfix₂ (b : Fin 2) (i : D') : Strata.twoConjugations (frobenius K p) b (x i) = x i := by
    fin_cases b <;> simp [Strata.twoConjugations, hfix]
  have hnot (i : D') (hi : i ∉ E) : w i = P.eval (x i) :=
    (not_ne_iff.mp (fun hn => hi ((herr i).mpr hn))).symm
  rw [plane_at_slope, Strata.conjugateHankel_error_rank _ x w hx hfix₂
    P 131072 a (a + H) hP hSize.ge E (by omega) hnot, Strata.conjugateErrors_two]
  let e (i : E) := w i.val - P.eval (x i.val)
  let y (i : E) := x i.val
  let U := atSlope Q.U γ
  let V := atSlope Q.V γ
  have hrel (i : E) : U.eval (y i) * e i + V.eval (y i) * frobenius K p (e i) = 0 :=
    Strata.decoder_error_identity (frobenius K p) x w hx hfix 131072 H U V _
      (specialize_relation Q hsub γ) S hSc P hP (fun i hi => (hgood i).mp hi) i.val
  have hne (i : E) : e i ≠ 0 := sub_ne_zero.mpr ((herr i.val).mp i.property).symm
  have hunits (i : E) : U.eval (y i) ≠ 0 ∧ V.eval (y i) ≠ 0 :=
    Strata.coprime_relation_units _ U V (y i) (e i) hregular.1 (hne i) (hrel i)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [hEc]; exact hR)
  have hU : U ≠ 0 := fun hz => (hunits ⟨i, hi⟩).1 (by rw [hz, eval_zero])
  have hV : V ≠ 0 := fun hz => (hunits ⟨i, hi⟩).2 (by rw [hz, eval_zero])
  have heq := Strata.error_two_rank_no_common (frobenius K p) y e
    (hx.comp Subtype.val_injective) U V H a hU hV hregular.2 hregular.1 hH hne
    (fun i => (hunits i).2) hrel
  simpa only [Fintype.card_coe, hEc, min_self] using heq

end
end K1_2_3
end PackSource_K1_2_3Marks

section PackSource_K1_2_4Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace K1_2_4

noncomputable section

open Polynomial Finset FrobeniusLocator
open K1 K1_2

/-- Remove the global fixed roots and recompute the simultaneous box, with
the same decoder marks and agreement. A constant box stops the family. -/
def c1 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a b : ℕ),
    1 ≤ b → b ≤ a → RegularPlane u D a (a+b) Γ P →
    Γ = ∅ ∨ ∃ (F : Finset I) (L : Bivar[X]), F ⊆ D ∧ F.card < b ∧
      (∀ γ ∈ Γ, F ⊆ errorSet u D γ (P γ)) ∧
      RegularPlane u (D \ F) a (a+(b-F.card)) Γ P ∧
      BoxedLocator u (D \ F) a (b-F.card) Γ P L

/-- On a mixed-coordinate curve, construct the two proper cofactor
representatives at each nonfixed grid root after removing curve-fixed errors. -/
def c2 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a b : ℕ),
    1 ≤ b → b ≤ a → RegularPlane u D a (a+b) Γ P →
    ∀ (L : Bivar[X]), BoxedLocator u D a b Γ P L →
    ∀ (Q : Bivar), Irreducible Q → 0 < seedDegree Q → 0 < Q.natDegree →
      Γ.Nonempty → (∀ γ ∈ Γ, onGraph γ Q = 0) →
      let d := a+b-(curveFixed D L Q).card
      0 < d → ∀ i ∈ D \ curveFixed D L Q,
        Nonempty (OppositeCuts u D Γ P Q a d i)

/-- The ordinary unique-decoding cap on an arbitrary punctured input with
agreement 131072+a and exact error count d strictly below a. -/
def c3 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a d : ℕ),
    d < a → D.card = 131072+a+d →
    (∀ γ ∈ Γ, (P γ).degree < 131072 ∧ (errorSet u D γ (P γ)).card = d ∧
      ¬ JointOn u (goodSet u D γ (P γ))) →
    Γ.card ≤ d + (131072+a+d)/(a-d+1)
private theorem restrict_plane {u D a b Γ P} (h : RegularPlane u D a (a+b) Γ P)
    (Q : Bivar) : RegularPlane u D a (a+b) (onCurve Γ Q) P :=
  ⟨h.domain_card, h.generic_rank, fun γ hγ => h.mark γ (Finset.mem_filter.mp hγ).1⟩

private theorem restrict_locator {u D a b Γ P L} (h : BoxedLocator u D a b Γ P L)
    (Q : Bivar) : BoxedLocator u D a b (onCurve Γ Q) P L :=
  ⟨h.degree, h.kernel, h.box, h.noFixed, fun γ hγ => h.fiber γ (Finset.mem_filter.mp hγ).1⟩

private theorem curveFixed_subset (D : Finset I) (L : Bivar[X]) (Q : Bivar) :
    curveFixed D L Q ⊆ D :=
  fun _ hi => (mem_curveFixed.mp hi).1

private theorem curveFixed_errors {u D a b Γ P L}
    (h : BoxedLocator u D a b Γ P L) {γ : K} (hγ : γ ∈ Γ)
    {Q : Bivar} (hQ : onGraph γ Q = 0) :
    curveFixed D L Q ⊆ errorSet u D γ (P γ) := by
  intro i hi
  obtain ⟨T, hT⟩ := (mem_curveFixed.mp hi).2
  apply (root_iff_error h hγ i).mp
  rw [hT, map_mul, hQ, zero_mul]

private theorem marks_after_puncture (u : Words) (D F : Finset I)
    (γ : K) (P : K[X]) (hF : F ⊆ errorSet u D γ P) :
    goodSet u (D \ F) γ P = goodSet u D γ P ∧
    errorSet u (D \ F) γ P = errorSet u D γ P \ F := by
  have hgood : goodSet u (D \ F) γ P = goodSet u D γ P := by
    ext i
    constructor
    · intro hi
      obtain ⟨hiD, hv⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hiD).1, hv⟩
    · intro hi
      obtain ⟨hiD, hv⟩ := Finset.mem_filter.mp hi
      have hin : i ∉ F := fun hiF => (Finset.mem_sdiff.mp (hF hiF)).2 hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hiD, hin⟩, hv⟩
  refine ⟨hgood, ?_⟩
  unfold errorSet
  rw [hgood]
  ext i
  simp only [Finset.mem_sdiff]
  tauto

/-- The two card identities use the same fixed set on both sides of the
incidence count. Every permitted puncture preserves the full good set. -/
private theorem punctured_curve_data {u D a b Γ P L}
    (hreg : RegularPlane u D a (a+b) Γ P) (h : BoxedLocator u D a b Γ P L)
    (Q : Bivar) (hΓ : Γ.Nonempty) (hQ : ∀ γ ∈ Γ, onGraph γ Q = 0) :
    let F := curveFixed D L Q
    let d := a+b-F.card
    (D \ F).card = 131072+a+d ∧
      ∀ γ ∈ Γ, (P γ).degree < 131072 ∧ (errorSet u (D \ F) γ (P γ)).card = d ∧
        ¬ JointOn u (goodSet u (D \ F) γ (P γ)) := by
  dsimp only
  obtain ⟨γ, hγ⟩ := hΓ
  have hle := Finset.card_le_card (curveFixed_errors h hγ (hQ γ hγ))
  rw [(hreg.mark γ hγ).2.1] at hle
  constructor
  · rw [Finset.card_sdiff_of_subset (curveFixed_subset D L Q), hreg.domain_card]
    omega
  · intro η hη
    have hsub := curveFixed_errors h hη (hQ η hη)
    obtain ⟨hg, he⟩ := marks_after_puncture u D (curveFixed D L Q) η (P η) hsub
    obtain ⟨hdegree, hcard, hbad, _⟩ := hreg.mark η hη
    rw [hg, he, Finset.card_sdiff_of_subset hsub, hcard]
    exact ⟨hdegree, rfl, hbad⟩

private theorem curve_root_incidence {u D a b Γ P L}
    (hreg : RegularPlane u D a (a+b) Γ P) (h : BoxedLocator u D a b Γ P L)
    (Q : Bivar) (hQ : ∀ γ ∈ Γ, onGraph γ Q = 0) (f : ℚ)
    (hcap : ∀ i ∈ D \ curveFixed D L Q,
      ((Γ.filter (fun γ => i ∈ errorSet u D γ (P γ))).card : ℚ) ≤ f) :
    ((a+b-(curveFixed D L Q).card : ℕ) : ℚ) * Γ.card ≤
      (D \ curveFixed D L Q).card * f := by
  let rel := fun i γ => i ∈ errorSet u D γ (P γ)
  apply rational_incidence _ _ rel _ f _ ?_
  · intro γ hγ
    have hsub := curveFixed_errors h hγ (hQ γ hγ)
    rw [← (hreg.mark γ hγ).2.1, ← Finset.card_sdiff_of_subset hsub]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hiE, hiF⟩ := Finset.mem_sdiff.mp hi
    exact (@Finset.mem_filter I (fun j => rel j γ)
      (fun j => Classical.propDecidable (rel j γ)) _ i).mpr
      ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hiE).1, hiF⟩, hiE⟩
  · intro i hi
    convert hcap i hi using 3
    ext γ
    simp only [Finset.mem_filter, rel]

private theorem old_curve (hcuts : c2) (hcore : c3) {u D a b Γ P L}
    (hb : 1 ≤ b) (hba : b ≤ a) (hreg : RegularPlane u D a (a+b) Γ P)
    (h : BoxedLocator u D a b Γ P L) (Q : Bivar) (hQ : Irreducible Q)
    (hzeros : ∀ γ ∈ Γ, onGraph γ Q = 0) :
    (Γ.card : ℚ) ≤ D.card / 2 * (seedDegree Q + Q.natDegree : ℕ) := by
  have hM : (131072 : ℚ) + a + (a+b) = D.card := by exact_mod_cast hreg.domain_card.symm
  have hweight : (1 : ℚ) ≤ D.card / 2 := by
    have ha : (0 : ℚ) ≤ a := by positivity
    have hbq : (0 : ℚ) ≤ b := by positivity
    linarith
  by_cases hcoord : seedDegree Q = 0 ∨ Q.natDegree = 0
  · have hc : (Γ.card : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) := by
      exact_mod_cast coordinate_intersection Q hQ.ne_zero hcoord Γ hzeros
    exact hc.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hweight (show (0 : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) by positivity))
  have hS : 0 < seedDegree Q := Nat.pos_of_ne_zero (fun hz => hcoord (Or.inl hz))
  have hT : 0 < Q.natDegree := Nat.pos_of_ne_zero (fun hz => hcoord (Or.inr hz))
  by_cases hne : Γ.Nonempty
  swap
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity
  let d := a+b-(curveFixed D L Q).card
  let E := D \ curveFixed D L Q
  by_cases hd : d = 0
  · obtain ⟨hcard, hmark⟩ := punctured_curve_data hreg h Q hne hzeros
    change E.card = 131072+a+d at hcard
    have hc := hcore u E Γ P a d (by omega) hcard hmark
    rw [hd] at hc
    have hc' : Γ.card ≤ 131072+a := by
      simpa using hc.trans (by simpa using Nat.div_le_self (131072+a) (a+1))
    have hcq : (Γ.card : ℚ) ≤ 131072+a := by exact_mod_cast hc'
    have hDN : (131072 : ℚ) + a ≤ D.card := by
      rw [← hM]
      exact le_add_of_nonneg_right (by positivity)
    have hperim : (2 : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) := by
      exact_mod_cast (show 2 ≤ seedDegree Q + Q.natDegree by omega)
    calc
      _ ≤ (D.card : ℚ) := hcq.trans hDN
      _ = (D.card : ℚ) / 2 * 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hperim (by positivity)
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hinc := curve_root_incidence hreg h Q hzeros
    ((d : ℚ)/2 * (seedDegree Q + Q.natDegree : ℕ)) (by
      intro i hi
      obtain ⟨cut⟩ := hcuts u D Γ P a b hb hba hreg L h Q hQ hS hT
        hne hzeros (Nat.pos_of_ne_zero hd) i hi
      let G := Γ.filter (fun γ => i ∈ errorSet u D γ (P γ))
      have hf : (G.card : ℚ) ≤ (Q.natDegree : ℚ) * (min a d : ℕ) + seedDegree Q * (d-a : ℕ) := by
        exact_mod_cast proper_intersection Q cut.first hQ hT.ne' cut.first_proper
          _ _ cut.first_box G (fun γ hγ =>
            ⟨hzeros γ (Finset.mem_filter.mp hγ).1,
              (cut.zeros γ (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hγ).2).1⟩)
      have hs : (G.card : ℚ) ≤ (Q.natDegree : ℚ) * (d-a : ℕ) + seedDegree Q * (min a d : ℕ) := by
        exact_mod_cast proper_intersection Q cut.second hQ hT.ne' cut.second_proper
          _ _ cut.second_box G (fun γ hγ =>
            ⟨hzeros γ (Finset.mem_filter.mp hγ).1,
              (cut.zeros γ (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hγ).2).2⟩)
      have hadd : (min a d : ℕ) + ((d-a : ℕ) : ℚ) = (d : ℚ) := by
        exact_mod_cast (show min a d + (d-a) = d by omega)
      change (G.card : ℚ) ≤ _
      have heq := congrArg (fun x : ℚ => x * (seedDegree Q + Q.natDegree : ℕ)) hadd
      simp only [Nat.cast_add] at heq ⊢
      linarith only [hf, hs, heq])
  change (d : ℚ)*Γ.card ≤ E.card*((d : ℚ)/2*(seedDegree Q + Q.natDegree : ℕ)) at hinc
  have hE : (E.card : ℚ) ≤ D.card := by
    exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : E ⊆ D))
  apply (mul_le_mul_iff_left₀ hdq).mp
  calc
    (Γ.card : ℚ)*d = (d : ℚ)*Γ.card := mul_comm _ _
    _ ≤ E.card*((d : ℚ)/2*(seedDegree Q + Q.natDegree : ℕ)) := hinc
    _ ≤ D.card*((d : ℚ)/2*(seedDegree Q + Q.natDegree : ℕ)) :=
      mul_le_mul_of_nonneg_right hE (by positivity)
    _ = _ := by ring

private theorem beta_at_least_one (A a C : ℕ) : 1 ≤ curveBeta A a C := by
  unfold curveBeta
  have hn : 0 ≤ (A : ℚ)/(a-C+1 : ℕ) := by positivity
  linarith

private theorem carried_curve (hcore : c3) {u D a b Γ P L}
    (hb : 1 ≤ b) (C : ℕ) (hC : 1 ≤ C) (hCa : C ≤ a)
    (hreg : RegularPlane u D a (a+b) Γ P) (h : BoxedLocator u D a b Γ P L)
    (hprice : ((ordinaryCore (131072+a) a C : ℕ) : ℚ) ≤
      2 * curveBeta (131072+a) a C * b)
    (Q : Bivar) (hQ : Irreducible Q) (hzeros : ∀ γ ∈ Γ, onGraph γ Q = 0) :
    (Γ.card : ℚ) ≤ curveBeta (131072+a) a C * b * (seedDegree Q + Q.natDegree : ℕ) := by
  let A := 131072+a
  let β := curveBeta A a C
  have hβ : 1 ≤ β := beta_at_least_one A a C
  have hbq : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hw : (1 : ℚ) ≤ β*b := by nlinarith
  change (Γ.card : ℚ) ≤ β*b*(seedDegree Q + Q.natDegree : ℕ)
  by_cases hcoord : seedDegree Q = 0 ∨ Q.natDegree = 0
  · have hc : (Γ.card : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) := by
      exact_mod_cast coordinate_intersection Q hQ.ne_zero hcoord Γ hzeros
    exact hc.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hw (show (0 : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) by positivity))
  have hS : 0 < seedDegree Q := Nat.pos_of_ne_zero (fun hz => hcoord (Or.inl hz))
  have hT : 0 < Q.natDegree := Nat.pos_of_ne_zero (fun hz => hcoord (Or.inr hz))
  by_cases hne : Γ.Nonempty
  swap
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by linarith) (by positivity)
  let F := curveFixed D L Q
  let d := a+b-F.card
  let E := D \ F
  obtain ⟨hcard, hmark⟩ := punctured_curve_data hreg h Q hne hzeros
  change E.card = A+d at hcard
  by_cases hsmall : d ≤ a-C
  · have hc := hcore u E Γ P a d (by omega) hcard hmark
    have hnum : (A+d)/(a-d+1) ≤ (A+(a-C))/(a-d+1) := Nat.div_le_div_right (by omega)
    have hden : (A+(a-C))/(a-d+1) ≤ (A+(a-C))/(C+1) := Nat.div_le_div_left (by omega) (by omega)
    have hc' : Γ.card ≤ ordinaryCore A a C := by
      unfold ordinaryCore
      change Γ.card ≤ (a-C)+(A+(a-C))/(C+1)
      change Γ.card ≤ d+(A+d)/(a-d+1) at hc
      omega
    have hcq : (Γ.card : ℚ) ≤ ordinaryCore A a C := by exact_mod_cast hc'
    have hperim : (2 : ℚ) ≤ (seedDegree Q + Q.natDegree : ℕ) := by
      exact_mod_cast (show 2 ≤ seedDegree Q + Q.natDegree by omega)
    calc
      _ ≤ 2*β*b := hcq.trans hprice
      _ = β*b*2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hperim (by linarith)
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hinc := curve_root_incidence hreg h Q hzeros
    ((b : ℚ)*(seedDegree Q + Q.natDegree : ℕ)) (by
      intro i hi
      let G := Γ.filter (fun γ => i ∈ errorSet u D γ (P γ))
      have hp : ¬ Q ∣ nodeEquation L i := by
        intro hdiv
        obtain ⟨hiD, hiF⟩ := Finset.mem_sdiff.mp hi
        exact hiF (mem_curveFixed.mpr ⟨hiD, hdiv⟩)
      have hh := proper_intersection Q (nodeEquation L i) hQ hT.ne' hp
        b b (nodeEquation_box L b b h.box i) G (by
          intro γ hγ
          obtain ⟨hγΓ, hγerr⟩ := Finset.mem_filter.mp hγ
          exact ⟨hzeros γ hγΓ, (root_iff_error h hγΓ i).mpr hγerr⟩)
      have hh' : G.card ≤ b*(seedDegree Q + Q.natDegree) := hh.trans_eq (by ring)
      exact_mod_cast hh')
  change (d : ℚ)*Γ.card ≤ E.card*((b : ℚ)*(seedDegree Q + Q.natDegree : ℕ)) at hinc
  have hcardq : (E.card : ℚ) = A+d := by exact_mod_cast hcard
  rw [hcardq] at hinc
  have hlo : ((a-C+1 : ℕ) : ℚ) ≤ d := by exact_mod_cast (show a-C+1 ≤ d by omega)
  have hratio : ((A : ℚ)+d)/d ≤ β := by
    calc
      _ = 1 + (A : ℚ)/d := by field_simp; ring
      _ ≤ β := by
        unfold β curveBeta
        gcongr
  calc
    (Γ.card : ℚ) ≤ ((A+d)*((b : ℚ)*(seedDegree Q + Q.natDegree : ℕ)))/d :=
      (le_div_iff₀ hdq).mpr (by rwa [mul_comm (Γ.card : ℚ)])
    _ = ((A+d)/d)*b*(seedDegree Q + Q.natDegree : ℕ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hratio (by positivity)) (by positivity)

private theorem price_fraction_mono (a x y : ℚ) (ha : 0 < a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x/(a+x) ≤ y/(a+y) := by
  apply (div_le_div_iff₀ (by linarith : 0 < a+x) (by linarith : 0 < a+y)).mpr
  nlinarith

private theorem old_price_mono (A a x y : ℕ) (ha : 0 < a) (hxy : x ≤ y) :
    oldPlanePrice A a x ≤ oldPlanePrice A a y := by
  have hxyq : (x : ℚ) ≤ y := by exact_mod_cast hxy
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hf := price_fraction_mono a x y haq (by positivity) hxyq
  have hs : ((A : ℚ)+a+x)^2 ≤ (A+a+y)^2 := by gcongr
  unfold oldPlanePrice
  calc
    _ = ((A : ℚ)+a+x)^2*(x/(a+x)) := by ring
    _ ≤ ((A : ℚ)+a+y)^2*(y/(a+y)) := mul_le_mul hs hf (by positivity) (by positivity)
    _ = _ := by ring

private theorem new_price_mono (β : ℚ) (A a x y : ℕ)
    (hβ : 0 ≤ β) (ha : 0 < a) (hxy : x ≤ y) :
    newPlanePrice β A a x ≤ newPlanePrice β A a y := by
  have hxyq : (x : ℚ) ≤ y := by exact_mod_cast hxy
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hf := price_fraction_mono a x y haq (by positivity) hxyq
  have hpx : (x : ℚ)*(A+a+x) ≤ (y : ℚ)*(A+a+y) := by gcongr
  unfold newPlanePrice
  calc
    _ = 2*β*(x/(a+x)*((x : ℚ)*(A+a+x))) := by ring
    _ ≤ 2*β*(y/(a+y)*((y : ℚ)*(A+a+y))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul hf hpx (by positivity) (by positivity)) (by positivity)
    _ = _ := by ring

private theorem core_below_threshold (A a C z : ℕ)
    (hz : planeThreshold A a C < z) :
    (ordinaryCore A a C : ℚ) ≤ 2*curveBeta A a C*z := by
  let x := (ordinaryCore A a C : ℚ)/(2*curveBeta A a C)
  have hceil : ⌈x⌉ ≤ (z : ℤ) := by
    by_contra hn
    change (⌈x⌉ : ℤ).toNat - 1 < z at hz
    omega
  have hdiv : x ≤ (z : ℚ) := by simpa only [Int.cast_natCast] using (Int.ceil_le.mp hceil)
  have hβ : 1 ≤ curveBeta A a C := beta_at_least_one A a C
  have hm := (div_le_iff₀ (show (0 : ℚ) < 2*curveBeta A a C by linarith)).mp hdiv
  simpa only [mul_comm (z : ℚ)] using hm

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_2.c4 := by
  intro u D Γ P a b C hb hba hC hCa hreg
  obtain he | ⟨F, L, _, hf, _, hplane, hloc⟩ := h1 u D Γ P a b hb hba hreg
  · rw [he, Finset.card_empty, Nat.cast_zero]
    exact K1_2.planePrice_nonneg _ _ _ _
  let z := b-F.card
  let A := 131072+a
  let β := curveBeta A a C
  let q := planeThreshold A a C
  have hz : 1 ≤ z := by omega
  have hzb : z ≤ b := Nat.sub_le _ _
  have hza := hzb.trans hba
  have ha : 0 < a := by omega
  have hpos : (0 : ℚ) < a+z := by
    exact_mod_cast (show 0 < a+z by omega)
  have hdom : ((D \ F).card : ℚ) = A+a+z := by
    exact_mod_cast (show (D \ F).card = A+a+z by have he := hplane.domain_card; dsimp [A, z]; omega)
  have hold : (Γ.card : ℚ) ≤ oldPlanePrice A a z := by
    have hinc := plane_incidence hloc (fun γ hγ => (hplane.mark γ hγ).2.1)
      (((D \ F).card : ℚ)/2) (by positivity) (by
        intro Q hQ
        exact old_curve h2 h3 hz hza (restrict_plane hplane Q) (restrict_locator hloc Q) Q hQ
          (fun γ hγ => (Finset.mem_filter.mp hγ).2))
    change (a+z : ℚ)*Γ.card ≤ ((D \ F).card : ℚ)*(2*(((D \ F).card : ℚ)/2)*z) at hinc
    rw [hdom] at hinc
    apply (le_div_iff₀ hpos).mpr
    calc
      (Γ.card : ℚ)*(a+z) = (a+z)*Γ.card := by ring
      _ ≤ _ := hinc
      _ = _ := by ring
  have hbase := hold.trans (old_price_mono A a z b ha hzb)
  change (Γ.card : ℚ) ≤ if b ≤ q then oldPlanePrice A a b else
    min (oldPlanePrice A a b) (max (oldPlanePrice A a q) (newPlanePrice β A a b))
  split_ifs
  · exact hbase
  apply le_min hbase
  by_cases hzq : z ≤ q
  · exact (hold.trans (old_price_mono A a z q ha hzq)).trans (le_max_left _ _)
  have hK := core_below_threshold A a C z (Nat.lt_of_not_ge hzq)
  have hβ : 0 ≤ β := (by norm_num : (0 : ℚ) ≤ 1).trans (beta_at_least_one A a C)
  have hinc := plane_incidence hloc (fun γ hγ => (hplane.mark γ hγ).2.1)
    (β*z) (by positivity) (by
      intro Q hQ
      exact carried_curve h3 hz C hC hCa (restrict_plane hplane Q) (restrict_locator hloc Q)
        hK Q hQ (fun γ hγ => (Finset.mem_filter.mp hγ).2))
  change (a+z : ℚ)*Γ.card ≤ ((D \ F).card : ℚ)*(2*(β*z)*z) at hinc
  rw [hdom] at hinc
  have hnew : (Γ.card : ℚ) ≤ newPlanePrice β A a z := by
    apply (le_div_iff₀ hpos).mpr
    calc
      (Γ.card : ℚ)*(a+z) = (a+z)*Γ.card := by ring
      _ ≤ _ := hinc
      _ = _ := by ring
  exact (hnew.trans (new_price_mono β A a z b hβ ha hzb)).trans (le_max_right _ _)

end

end K1_2_4
end PackSource_K1_2_4Split

section PackSource_K1_2_4_1Ranks
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K1_2_4_1

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2 K1_2_4

/-- Removing only errors preserves every agreement and restricts the error set. -/
theorem puncture_marks {u : Words} {D F : Finset I} {γ : K} {P : K[X]}
    (hF : F ⊆ errorSet u D γ P) :
    goodSet u (D \ F) γ P = goodSet u D γ P ∧
    errorSet u (D \ F) γ P = errorSet u D γ P \ F := by
  have hg : goodSet u (D \ F) γ P = goodSet u D γ P := by
    ext i
    have hnot (hi : i ∈ F) : i ∉ goodSet u D γ P := (Finset.mem_sdiff.mp (hF hi)).2
    simp only [goodSet, Finset.mem_filter, Finset.mem_sdiff] at hnot ⊢
    tauto
  refine ⟨hg, ?_⟩
  unfold errorSet
  rw [hg]
  ext i
  simp only [Finset.mem_sdiff]
  tauto

private def errorColumns (u : Words) (E : Finset I) (a : ℕ) (γ : K) (P : K[X]) :
    Matrix (Fin 2 × Fin a) E K :=
  Strata.conjugateErrors (Strata.twoConjugations (frobenius K p))
    (fun i : E => node i.val) (fun i : E => u 0 i.val + γ * u 1 i.val - P.eval (node i.val)) a

private theorem plane_rank_error_columns (u : Words) (D : Finset I) (a d : ℕ)
    (γ : K) (P : K[X]) (hD : D.card = 131072+a+d) (hP : P.degree < 131072)
    (hE : (errorSet u D γ P).card = d) :
    ((planeMatrix u D a d).map (onGraph γ)).rank = (errorColumns u (errorSet u D γ P) a γ P).rank := by
  classical
  let x : D → K := fun i => node i.val
  let w : D → K := fun i => u 0 i.val + γ * u 1 i.val
  let E := errorSet u D γ P
  let S := E.subtype (· ∈ D)
  have hsub : E ⊆ D := Finset.sdiff_subset
  let e : E ≃ S :=
    { toFun := fun i => ⟨⟨i.val, hsub i.property⟩, Finset.mem_subtype.mpr i.property⟩
      invFun := fun i => ⟨i.val.val, Finset.mem_subtype.mp i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : S.card = d := by
    rw [← Fintype.card_coe, ← Fintype.card_congr e, Fintype.card_coe, hE]
  have hsize : 131072+a+d ≤ Fintype.card D := by rw [Fintype.card_coe, hD]
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have hf (i : D) : frobenius K p (x i) = x i := Native.native_domain_fixed i.val
  have hfixed (b : Fin 2) (i : D) : Strata.twoConjugations (frobenius K p) b (x i) = x i := by
    fin_cases b <;> simp [Strata.twoConjugations, hf]
  have hagree (i : D) (hi : i ∉ S) : w i = P.eval (x i) := by
    by_contra hn
    exact hi (Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr ⟨i.property, by
      simp only [goodSet, Finset.mem_filter, i.property, true_and]
      exact Ne.symm hn⟩))
  rw [K1_2_3.plane_at_slope, Strata.conjugateHankel_error_rank _ x w hx hfixed
    P 131072 a d hP hsize S (by omega) hagree]
  exact (Matrix.rank_submatrix _ (Equiv.refl _) e).symm

/-- The same marked decoder at a shorter domain gives the restriction of
the original full-column-rank weighted error matrix, with weights stripped. -/
theorem puncture_point_rank {u : Words} {D F : Finset I} {a R : ℕ} {γ : K} {P : K[X]}
    (hD : D.card = 131072+a+R) (hP : P.degree < 131072)
    (hE : (errorSet u D γ P).card = R) (hR : ((planeMatrix u D a R).map (onGraph γ)).rank = R)
    (hF : F ⊆ errorSet u D γ P) :
    ((planeMatrix u (D \ F) a (R-F.card)).map (onGraph γ)).rank = R-F.card := by
  classical
  let E := errorSet u D γ P
  let E' := errorSet u (D \ F) γ P
  have heq : E' = E \ F := (puncture_marks hF).2
  have hE' : E'.card = R-F.card := by rw [heq, Finset.card_sdiff_of_subset hF, hE]
  have hDF : (D \ F).card = 131072+a+(R-F.card) := by
    have hle := Finset.card_le_card hF
    rw [hE] at hle
    rw [Finset.card_sdiff_of_subset (hF.trans Finset.sdiff_subset), hD]
    omega
  rw [plane_rank_error_columns u (D \ F) a (R-F.card) γ P hDF hP hE', ← hE', ← Fintype.card_coe]
  have hfull : (errorColumns u E a γ P).rank = Fintype.card E := by
    rw [← plane_rank_error_columns u D a R γ P hD hP hE, hR, Fintype.card_coe, hE]
  have hli : LinearIndependent K (errorColumns u E a γ P).col := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    unfold Set.finrank
    rw [← Matrix.rank_eq_finrank_span_cols, hfull]
  have hEE : E' ⊆ E := by rw [heq]; exact Finset.sdiff_subset
  let e : E' → E := fun i => ⟨i.val, hEE i.property⟩
  have he : Function.Injective e := fun _ _ h => Subtype.ext (congrArg (fun i : E => i.val) h)
  have hli' : LinearIndependent K (errorColumns u E' a γ P).col := hli.comp e he
  rw [Matrix.rank_eq_finrank_span_cols]
  exact finrank_span_eq_card hli'

end

end K1_2_4_1
end PackSource_K1_2_4_1Ranks

section PackSource_K1_2_2Marks
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K1_2_2
noncomputable section

open K1 K1_2 Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark

private theorem twoBlock_atSlope (u : Words) (γ : K) :
    ((twoBlock u).map (evalRingHom γ)) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        node (fun i => u 0 i + γ * u 1 i) 49193 81879 := by
  rw [twoBlock, Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]

/-- The rank of a normal stack is a lower bound on the number of actual
nonzero errors of every degree-bounded decoder of that slope. -/
theorem rank_le_errors {u : Words} {γ : K} (M : BadMark u γ)
    (hγ : Normal u γ) (E : Finset I)
    (hagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    stackRank u ≤ E.card := by
  have hfix : ∀ b i, Strata.twoConjugations (frobenius K p) b (node i) = node i := by
    intro b i
    fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]
  have h := Strata.conjugateHankel_factorization
    (Strata.twoConjugations (frobenius K p)) node (fun i => u 0 i + γ * u 1 i)
    IRSProfile.domain.injective hfix M.decoder 131072 49193 81879 M.degree
    (by rw [IRSProfile.card_index]) E hagree
  change ((twoBlock u).map (evalRingHom γ)).rank = stackRank u at hγ
  rw [← hγ, twoBlock_atSlope, h]
  refine (Matrix.rank_mul_le_right _ _).trans ?_
  simpa only [Fintype.card_coe] using
    Matrix.rank_le_card_height (Strata.nodeVandermonde (fun i : E => node i.val) 81879)

theorem domain_card (S : Finset I) :
    (Finset.univ \ S).card = 262144 - S.card := by
  classical
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index]

private theorem mark_counts {u : Words} {γ : K} (M : BadMark u γ)
    (hγ : Normal u γ) {S : Finset I}
    (hfixed : ∀ i ∈ S, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i) :
    let D := Finset.univ \ S
    let G := goodSet u D γ M.decoder
    let s := G.card - 180265
    s ≤ nullity u - 1 ∧ G.card = 180265 + s ∧
      (errorSet u D γ M.decoder).card = 81879 - S.card - s ∧ ¬ JointOn u G := by
  classical
  dsimp only
  let D := Finset.univ \ S
  let G := goodSet u D γ M.decoder
  let E := Finset.univ \ G
  have hsupport : M.support ⊆ G := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => hfixed i hs (M.hits i hi)⟩, M.hits i hi⟩
  have hlow := M.agreement.trans (Finset.card_le_card hsupport)
  have hGD : G ⊆ D := Finset.filter_subset _ _
  have hGle := Finset.card_le_card hGD
  have hD : D.card = 262144 - S.card := domain_card S
  have hE : E.card = 262144 - G.card := domain_card G
  have hEg : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    intro i hi
    by_contra hne
    apply hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hG =>
      hne (Finset.mem_filter.mp hG).2.symm⟩
  have hrank := rank_le_errors M hγ E hEg
  have hrankBound : stackRank u + nullity u = 81880 := by
    simpa only [stackRank, nullity, Fintype.card_fin] using
      GenericLayer.rank_add_nullity (twoBlock u)
  have herror : (errorSet u D γ M.decoder).card = D.card - G.card :=
    Finset.card_sdiff_of_subset hGD
  change G.card - 180265 ≤ nullity u - 1 ∧ G.card = 180265 + (G.card - 180265) ∧
    (errorSet u D γ M.decoder).card = 81879 - S.card - (G.card - 180265) ∧ ¬ JointOn u G
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro hjoint
  apply M.nonjoint
  obtain ⟨⟨P, hP, hPval⟩, ⟨Q, hQ, hQval⟩⟩ := hjoint
  exact ⟨⟨P, hP, fun i hi => hPval i (hsupport hi)⟩,
    ⟨Q, hQ, fun i hi => hQval i (hsupport hi)⟩⟩

/-- A single choice of a genuine decoder across the selected slopes,
with its full agreement set and unchanged nonjointness witness. -/
theorem paddedFamily {u : Words} {T : TwoActive u} {R : Relation T}
    (hsat : NormalSaturation R) (Γ : Finset K) (hbad : BadFamily u Γ)
    (hn : ∀ γ ∈ Γ, Normal u γ) :
    Nonempty (PaddedFamily u (Finset.univ \ fixedNodes R) Γ
      (nullity u) (fixedNodes R).card) := by
  classical
  let D := Finset.univ \ fixedNodes R
  let M (γ : K) (hγ : γ ∈ Γ) : BadMark u γ :=
    Classical.choice (bad_mark u Γ hbad γ hγ)
  let P (γ : K) : K[X] := if hγ : γ ∈ Γ then (M γ hγ).decoder else 0
  refine ⟨⟨P, fun γ => (goodSet u D γ (P γ)).card - 180265, domain_card _, ?_, ?_⟩⟩
  · intro γ hγ
    simpa only [P, dite_eq_left hγ] using (M γ hγ).degree
  · intro γ hγ
    have h := mark_counts (M γ hγ) (hn γ hγ) (hsat γ (hn γ hγ) (M γ hγ)).fixed_errors
    simpa only [P, dite_eq_left hγ, D] using h

end
end K1_2_2
end PackSource_K1_2_2Marks

section PackSource_K1_2_4_1Deflation
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K1_2_4_1

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2 K1_2_4

theorem eval_planeConstant (γ : K) (x : K) : onGraph γ (planeConstant x) = x := by
  rw [K1_2_4.evalGraph]
  simp [planeConstant]

theorem root_iff_error {u : Words} {D : Finset I} {Γ : Finset K} {P : K → K[X]}
    {a d : ℕ} {L : Bivar[X]} (hL : MarkedLocator u D a d Γ P L)
    {γ : K} (hγ : γ ∈ Γ) (i : I) :
    onGraph γ (nodeEquation L i) = 0 ↔ i ∈ errorSet u D γ (P γ) := by
  obtain ⟨c, hc, hf⟩ := hL.fiber γ hγ
  rw [nodeEquation, ← Polynomial.eval_map_apply, eval_planeConstant, hf, Polynomial.eval_smul,
    smul_eq_mul, mul_eq_zero, or_iff_right hc]
  exact Principal.locator_eval_zero_iff node IRSProfile.domain.injective _ i

theorem locator_nonzero {u : Words} {D : Finset I} {Γ : Finset K} {P : K → K[X]}
    {a d : ℕ} {L : Bivar[X]} (hL : MarkedLocator u D a d Γ P L) (hΓ : Γ.Nonempty) : L ≠ 0 := by
  obtain ⟨γ, hγ⟩ := hΓ
  obtain ⟨c, hc, hf⟩ := hL.fiber γ hγ
  intro hz
  rw [hz, Polynomial.map_zero] at hf
  exact (smul_ne_zero hc (locator_monic node _).ne_zero) hf.symm

/-- Divisibility holds over the polynomial coefficient ring. At a different
node the removed linear factor evaluates to a nonzero constant. -/
theorem fixedFactor_dvd (F : Finset I) (L : Bivar[X])
    (h : ∀ i ∈ F, nodeEquation L i = 0) : fixedFactor F ∣ L := by
  classical
  induction F using Finset.induction_on generalizing L with
  | empty => simp [fixedFactor, locator]
  | insert i F hi ih =>
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr (h i (Finset.mem_insert_self i F))
    have hroot (j : I) (hj : j ∈ F) : nodeEquation Q j = 0 := by
      have he := h j (Finset.mem_insert_of_mem hj)
      rw [nodeEquation, hQ, eval_mul, eval_sub, eval_X, eval_C] at he
      apply (mul_eq_zero.mp he).resolve_left
      exact sub_ne_zero.mpr (fun heq => hi ((IRSProfile.domain.injective
        (planeConstant.injective heq)) ▸ hj))
    obtain ⟨V, hV⟩ := ih Q hroot
    refine ⟨V, ?_⟩
    have hfac : fixedFactor (insert i F) =
        (Polynomial.X (R := Bivar) - C (planeConstant (node i))) * fixedFactor F := by
      simp only [fixedFactor, locator, Finset.prod_insert hi, Polynomial.map_mul,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hQ, hV, hfac, mul_assoc]

theorem fixedFactor_monic (F : Finset I) : (fixedFactor F).Monic :=
  (locator_monic node F).map _

theorem fixedFactor_natDegree (F : Finset I) : (fixedFactor F).natDegree = F.card := by
  rw [fixedFactor, (locator_monic node F).natDegree_map, locator_natDegree]

private abbrev FunctionField := FractionRing Bivar

private def planeEmbedding : Bivar →+* FunctionField := algebraMap Bivar FunctionField

private theorem planeEmbedding_injective : Function.Injective planeEmbedding :=
  IsFractionRing.injective Bivar FunctionField

private theorem map_locator_kernel {row : Type*} {d : ℕ}
    (M : Matrix row (Fin (d+1)) Bivar) {L : Bivar[X]}
    (h : M.mulVec (fun j => L.coeff j.val) = 0) :
    (M.map planeEmbedding).mulVec (fun j => (L.map planeEmbedding).coeff j.val) = 0 := by
  funext i
  simpa only [coeff_map, Function.comp_def, h, Pi.zero_apply, map_zero] using
    (planeEmbedding.map_mulVec M (fun j => L.coeff j.val) i).symm

private theorem map_locator_vector_ne_zero {d : ℕ} {L : Bivar[X]} (hL : L ≠ 0)
    (hd : L.natDegree ≤ d) : (fun j : Fin (d+1) => (L.map planeEmbedding).coeff j.val) ≠ 0 := by
  intro hz
  have h := congrFun hz ⟨L.natDegree, Nat.lt_succ_of_le hd⟩
  apply leadingCoeff_ne_zero.mpr hL
  apply planeEmbedding_injective
  simpa only [leadingCoeff, coeff_map, map_zero, Pi.zero_apply] using h

theorem generic_rank_le_of_locator {row : Type*} {d : ℕ} (M : Matrix row (Fin (d+1)) Bivar)
    {L : Bivar[X]} (hL : L ≠ 0) (hd : L.natDegree ≤ d)
    (hker : M.mulVec (fun j => L.coeff j.val) = 0) :
    (M.map (algebraMap Bivar (FractionRing Bivar))).rank ≤ d := by
  let N := M.map planeEmbedding
  have h := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  change N.rank + _ = d+1 at h
  have hpos : 0 < Module.finrank FunctionField (LinearMap.ker N.mulVecLin) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hbot := Submodule.finrank_eq_zero.mp hz
    have hv : (fun j => (L.map planeEmbedding).coeff j.val) ∈ LinearMap.ker N.mulVecLin :=
      map_locator_kernel M hker
    rw [hbot, Submodule.mem_bot] at hv
    exact map_locator_vector_ne_zero hL hd hv
  change N.rank ≤ d
  omega

/-- At generic rank d, a recomputed kernel polynomial has the same grid
zeros as the shortened polynomial locator. -/
theorem repack_node_nonzero {row : Type*} {d : ℕ} (M : Matrix row (Fin (d+1)) Bivar)
    (hr : (M.map (algebraMap Bivar (FractionRing Bivar))).rank = d)
    {L Q : Bivar[X]} (hL : L ≠ 0) (hQ : Q ≠ 0) (hLd : L.natDegree ≤ d) (hQd : Q.natDegree ≤ d)
    (hLker : M.mulVec (fun j => L.coeff j.val) = 0) (hQker : M.mulVec (fun j => Q.coeff j.val) = 0)
    (i : I) (hi : nodeEquation Q i ≠ 0) : nodeEquation L i ≠ 0 := by
  let N := M.map planeEmbedding
  have hn : N.rank+1 = Fintype.card (Fin (d+1)) := by rw [Fintype.card_fin]; exact congrArg (· + 1) hr
  obtain ⟨c, hc⟩ := GenericRank.kernel_line_of_finrank N (GenericRank.nullity_one_of_rank N hn)
    _ (map_locator_vector_ne_zero hQ hQd) (map_locator_kernel M hQker) _ (map_locator_kernel M hLker)
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hc
    exact map_locator_vector_ne_zero hL hLd hc
  have he : L.map planeEmbedding = c • Q.map planeEmbedding := by
    apply Polynomial.ext
    intro j
    by_cases hj : j < d+1
    · simpa only [coeff_smul, Pi.smul_apply] using congrFun hc ⟨j, hj⟩
    · rw [coeff_smul, coeff_map, coeff_map, coeff_eq_zero_of_natDegree_lt (show L.natDegree < j by omega),
        coeff_eq_zero_of_natDegree_lt (show Q.natDegree < j by omega), map_zero, smul_zero]
  intro hz
  have heval := congrArg (fun V : FunctionField[X] => V.eval (planeEmbedding (planeConstant (node i)))) he
  rw [Polynomial.eval_map_apply, Polynomial.eval_smul, Polynomial.eval_map_apply] at heval
  change planeEmbedding (nodeEquation L i) = c * planeEmbedding (nodeEquation Q i) at heval
  rw [hz, map_zero] at heval
  exact hi (planeEmbedding_injective ((mul_eq_zero.mp heval.symm).resolve_left hc0 |>.trans (map_zero _).symm))

end

end K1_2_4_1
end PackSource_K1_2_4_1Deflation

section PackSource_K1_2_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K1_2_2
noncomputable section

open K1 K1_2 K1_6 Polynomial Matrix FrobeniusLocator

/-- A genuine normal witness supplies the shortened stack's rank lower
bound after deletion of the fixed error columns. -/
def c1 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (A : Reduction u T R)
    (γ : K), BadMark u γ → Normal u γ →
      49193 + A.height ≤ GenericLayer.genericRank (shortenedStack R)

/-- The shortened relation supplies all its bounded shifts as left
dependencies of the shortened stack. -/
def c2 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (A : Reduction u T R),
    (shifts (pair A) 49193 (49193 - A.height)).transpose * shortenedStack R = 0

private theorem shifted_pair_height
    (F : Type) [Field F] (L H w q : ℕ) (P : Fin 2 → F[X][X])
    (M : Matrix (Fin 2 × Fin L) (Fin w) F[X])
    (hq : 1 ≤ q) (hHL : H < L)
    (hP : ∀ b, (P b).natDegree ≤ H)
    (hprim : PrimitiveVector.IsPrimitive (pairCoordinates P H))
    (hrank : L + H ≤ GenericLayer.genericRank M)
    (hshift : (shifts P L (L - H)).transpose * M = 0)
    (hentry : ∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else q) :
    ∀ b j, ((P b).coeff j).natDegree ≤ (q * L + H) / (L - H) := by
  classical
  intro b j
  let s := L - H
  have hs : 0 < s := by dsimp [s]; omega
  have hsum : H + s = L := by dsimp [s]; omega
  let W := shifts P L s
  let φ : F[X] →+* GenericLayer.GenericField F := algebraMap _ _
  obtain ⟨hminors, ζ, hζ, rows, hrows⟩ := K1_6_1.proof F H L s P hsum hs hP hprim
  obtain ⟨I, hI⟩ := PrimitiveVector.exists_eval_ne_zero (maximalMinors W) hminors 0
  have hI' : (W.submatrix I id).det ≠ 0 := fun hz => hI (by simp [maximalMinors, hz])
  have hdet : ((W.map φ).submatrix I id).det ≠ 0 := by
    have h := φ.map_det (W.submatrix I id)
    change φ ((W.submatrix I id).det) = ((W.map φ).submatrix I id).det at h
    rw [← h]
    exact fun hz => hI' ((IsFractionRing.injective F[X] (GenericLayer.GenericField F))
      (hz.trans (map_zero φ).symm))
  have hW : s ≤ (W.map φ).rank := by
    have h := Matrix.rank_submatrix_le (W.map φ) I id
    rwa [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h
  have hmap : (W.map φ).transpose * M.map φ = 0 := by
    have h := congrArg (fun N : Matrix (Fin s) (Fin w) F[X] => N.map φ) hshift
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_zero _ (map_zero φ)] at h
    exact h
  have hu := Matrix.rank_add_rank_le_card_of_mul_eq_zero hmap
  rw [Matrix.rank_transpose, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hu
  change (W.map φ).rank + GenericLayer.genericRank M ≤ 2 * L at hu
  have hR : GenericLayer.genericRank M + s = 2 * L := by omega
  have hb := K1_6_2.proof F L w s q M W hq hR hshift hentry hminors rows
  rw [hrows] at hb
  have hledger : L * (q + 1) - s = q * L + H := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm L q]
    omega
  rw [hledger] at hb
  exact (hζ b j).trans ((Nat.le_div_iff_mul_le hs).mpr (by simpa only [Nat.mul_comm] using hb))

theorem of_children (h1 : c1) (h2 : c2) : K1_2.c2 := by
  classical
  intro u hm T R hmov hinv hsat Γ hnon hbad hn
  dsimp only
  intro hg
  obtain ⟨γ, hγ⟩ := hnon
  obtain ⟨M⟩ := bad_mark u Γ hbad γ hγ
  have hSat := hsat γ (hn γ hγ) M
  have hU : leftU R ≠ 0 := by
    intro hz
    exact hSat.U_ne (by rw [atSlope, hz, Polynomial.map_zero])
  obtain ⟨A⟩ := K1_8.puncture R hsat ⟨γ, hn γ hγ, ⟨M⟩⟩
    (K1_8.fixed_gcd R hU hmov hinv)
  let D := Finset.univ \ fixedNodes R
  let H := reducedHeight (nullity u) (fixedNodes R).card
  have hheight : A.height = H := by
    have h := A.height_eq
    have := T.degreeSum
    have := T.nullitySum
    have := T.top
    unfold TwoActive.height at h
    dsimp [H, reducedHeight]
    omega
  have hpos : 0 < H := by
    have hg' := hg.trans (fixedLimit_le (nullity u))
    have hr := hm.2.1
    dsimp [H, reducedHeight]
    omega
  have hlt : A.height < 49193 := by
    have hr := hm.1
    rw [hheight]
    dsimp [H, reducedHeight]
    omega
  have hnodes : relationOn u (Finset.univ \ D) A.U A.V A.output := by
    intro i hi
    have hi' : i ∉ fixedNodes R := by
      intro hs
      exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hD => (Finset.mem_sdiff.mp hD).2 hs⟩)
    simpa only [Polynomial.C_1, one_mul] using K1_8.reduced_scaled_relation A (1 : K[X]) i hi'
  let Q : ReducedRelation u D H :=
    ⟨A.U, A.V, A.output, Or.inl A.U_ne, A.max_degree.trans hheight,
      hheight ▸ A.output_degree, hnodes⟩
  have hrank := h1 u T R A γ M (hn γ hγ)
  have hshift := h2 u T R A
  have hentry (i : Fin 2 × Fin 49193) (j : Fin (81879 - (fixedNodes R).card + 1)) :
      (shortenedStack R i j).natDegree ≤ if i.1 = 0 then 1 else p :=
    stacked_entry_natDegree p (fun i : D => node i.val) (fun i => u 0 i.val)
      (fun i => u 1 i.val) 49193 (81879 - (fixedNodes R).card) i j
  have hp : 1 ≤ p := by decide
  have hz := shifted_pair_height K 49193 A.height _ p (pair A) (shortenedStack R) hp hlt (pair_degree A)
    (pair_primitive A) hrank hshift hentry
  rw [hheight] at hz
  let ζ := (p * 49193 + H) / (49193 - H)
  have hζU (i : ℕ) : (Q.U.coeff i).natDegree ≤ ζ := hz 0 i
  have hζV (i : ℕ) : (Q.V.coeff i).natDegree ≤ ζ := hz 1 i
  obtain ⟨book, hbsub, hbcard, hreg⟩ :=
    resultant_book Q hpos A.U_ne A.V_ne A.coprime hζU hζV Γ
  obtain ⟨F⟩ := paddedFamily hsat (Γ \ book)
    (fun z hz => hbad z (Finset.mem_sdiff.mp hz).1)
    (fun z hz => hn z (Finset.mem_sdiff.mp hz).1)
  refine ⟨book, hbsub, ?_, F, Q, hreg⟩
  exact hbcard.trans (Nat.le_add_right _ _)

end
end K1_2_2
end PackSource_K1_2_2Split

section PackSource_K1_2_4_1Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K1_2_4_1

noncomputable section

open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2 K1_2_4

/-- Opposite cofactor choices bound both seed degrees, with a nonzero
primitive specialization at every selected exact-rank point. -/
def c1 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (P : K → K[X]) (a d : ℕ),
    0 < d → d ≤ a+a → Γ.Nonempty → RegularPlane u D a d Γ P →
    ∃ L : Bivar[X], MarkedLocator u D a d Γ P L ∧
      ∀ j, SeedBox (L.coeff j) (d-a) (d-a)

/-- Transport the literal independent-parameter Hankel kernel equation
through division by the locator of a set of deleted grid nodes. -/
def c2 : Prop :=
  ∀ (u : Words) (D F : Finset I) (a d : ℕ), F ⊆ D →
    ∀ Q : Bivar[X], Q.natDegree ≤ d →
      (planeMatrix u D a (F.card+d)).mulVec (fun j => (fixedFactor F * Q).coeff j.val) = 0 →
      (planeMatrix u (D \ F) a d).mulVec (fun j => Q.coeff j.val) = 0

private theorem constant_node_specialization {V : Bivar} (hV : SeedBox V 0 0) (γ : K) :
    onGraph γ V = 0 → V = 0 := by
  have hT : V.natDegree = 0 := Nat.eq_zero_of_le_zero hV.2
  have hS : (V.coeff 0).natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((coeff_natDegree_le_seedDegree V 0).trans hV.1)
  have hC : V = planeConstant ((V.coeff 0).coeff 0) :=
    (eq_C_of_natDegree_eq_zero hT).trans (congrArg Polynomial.C (eq_C_of_natDegree_eq_zero hS))
  intro hz
  rw [hC, eval_planeConstant] at hz
  rw [hC, hz, map_zero]

/-- With zero remaining errors the degree-zero kernel kills both formal
ordinary syndrome coefficients, giving separate decoders on the full puncture. -/
private theorem joint_of_zero_error_kernel (u : Words) (D : Finset I) (a : ℕ)
    (hD : D.card = 131072+a) (Q : Bivar[X]) (hQ : Q ≠ 0) (hQd : Q.natDegree ≤ 0)
    (hker : (planeMatrix u D a 0).mulVec (fun j => Q.coeff j.val) = 0) : JointOn u D := by
  classical
  let x : D → K := fun i => node i.val
  have hq : Q.coeff 0 ≠ 0 := by
    simpa only [Nat.eq_zero_of_le_zero hQd, leadingCoeff] using leadingCoeff_ne_zero.mpr hQ
  have hsz : Fintype.card D = 131072+a := by rw [Fintype.card_coe, hD]
  have hs (j : ℕ) (hj : j < a) :
      syndrome x (fun i => u 0 i.val) j = 0 ∧ syndrome x (fun i => u 1 i.val) j = 0 := by
    have hrow : (∑ t : Fin 1, planeMatrix u D a 0 (0, ⟨j, hj⟩) t * Q.coeff t.val) = 0 :=
      congrFun hker ((0 : Fin 2), (⟨j, hj⟩ : Fin a))
    rw [Fin.sum_univ_one, Fin.val_zero] at hrow
    have hz := (mul_eq_zero.mp hrow).resolve_right hq
    have hi : Polynomial.C (syndrome x (fun i => u 0 i.val) j) +
        Polynomial.X * Polynomial.C (syndrome x (fun i => u 1 i.val) j) = 0 := by
      apply Polynomial.C_injective (R := K[X])
      simpa [planeMatrix, x] using hz
    constructor
    · simpa only [coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, coeff_zero] using
        congrArg (fun V : K[X] => V.coeff 0) hi
    · simpa [coeff_add, coeff_X_mul] using congrArg (fun V : K[X] => V.coeff 1) hi
  have extend (b : Fin 2) (hb : ∀ j < a, syndrome x (fun i => u b i.val) j = 0) :
      ExtendsOn node (u b) 131072 D := by
    obtain ⟨A, hA, hfit⟩ := Principal.extendsOn_of_syndrome_zero x
      (IRSProfile.domain.injective.comp Subtype.val_injective) (fun i => u b i.val) 131072
      (by omega) (fun j hj => hb j (by omega))
    exact ⟨A, hA, fun i hi => hfit ⟨i, hi⟩ (Finset.mem_univ _)⟩
  exact ⟨extend 0 (fun j hj => (hs j hj).1), extend 1 (fun j hj => (hs j hj).2)⟩

theorem of_children (hbox : c1) (hcontract : c2) : K1_2_4.c1 := by
  classical
  intro u D Γ P a b hb hba hreg
  by_cases hΓ : Γ.Nonempty
  swap
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hΓ)
  have hΓ' := hΓ
  obtain ⟨γ₀, hγ₀⟩ := hΓ'
  obtain ⟨L, hL, _⟩ := hbox u D Γ P a (a+b) (by omega) (by omega) hΓ hreg
  let F := D.filter (fun i => nodeEquation L i = 0)
  let d := a+b-F.card
  have hF : F ⊆ D := Finset.filter_subset _ _
  have hsub (γ : K) (hγ : γ ∈ Γ) : F ⊆ errorSet u D γ (P γ) := by
    intro i hi
    apply (K1_2_4_1.root_iff_error hL hγ i).mp
    rw [(Finset.mem_filter.mp hi).2, map_zero]
  have hfmax : F.card ≤ a+b := (Finset.card_le_card (hsub γ₀ hγ₀)).trans_eq (hreg.mark γ₀ hγ₀).2.1
  have hadd : F.card+d = a+b := by omega
  obtain ⟨Q, hQ⟩ := fixedFactor_dvd F L (fun i hi => (Finset.mem_filter.mp hi).2)
  have hQ0 : Q ≠ 0 := by
    intro hz
    exact locator_nonzero hL hΓ (by rw [hQ, hz, mul_zero])
  have hQd : Q.natDegree ≤ d := by
    have he := natDegree_mul (fixedFactor_monic F).ne_zero hQ0
    rw [← hQ, fixedFactor_natDegree] at he
    have hd := hL.degree
    omega
  have hQker : (planeMatrix u (D \ F) a d).mulVec (fun j => Q.coeff j.val) = 0 := by
    apply hcontract u D F a d hF Q hQd
    rw [hadd, ← hQ]
    exact hL.kernel
  have hno (i : I) (hi : i ∈ D \ F) : nodeEquation Q i ≠ 0 := by
    intro hz
    change Q.eval (planeConstant (node i)) = 0 at hz
    have he : nodeEquation L i = 0 := by rw [nodeEquation, hQ, eval_mul, hz, mul_zero]
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, he⟩)
  have hD : (D \ F).card = 131072+a+d := by
    rw [Finset.card_sdiff_of_subset hF, hreg.domain_card]
    omega
  have hshort_mark (γ : K) (hγ : γ ∈ Γ) : (P γ).degree < 131072 ∧
      (errorSet u (D \ F) γ (P γ)).card = d ∧ ¬ JointOn u (goodSet u (D \ F) γ (P γ)) ∧
      ((planeMatrix u (D \ F) a d).map (onGraph γ)).rank = d := by
    obtain ⟨hP, hE, hbad, hr⟩ := hreg.mark γ hγ
    obtain ⟨hg, he⟩ := puncture_marks (hsub γ hγ)
    refine ⟨hP, ?_, hg.symm ▸ hbad, puncture_point_rank hreg.domain_card hP hE hr (hsub γ hγ)⟩
    rw [he, Finset.card_sdiff_of_subset (hsub γ hγ), hE]
  by_cases hd : d = 0
  · exfalso
    obtain ⟨_, hE, hbad, _⟩ := hshort_mark γ₀ hγ₀
    have hg : goodSet u (D \ F) γ₀ (P γ₀) = D \ F := by
      apply le_antisymm (Finset.filter_subset _ _)
      intro i hi
      by_contra hn
      have he : i ∈ errorSet u (D \ F) γ₀ (P γ₀) := Finset.mem_sdiff.mpr ⟨hi, hn⟩
      rw [hd, Finset.card_eq_zero] at hE
      exact Finset.notMem_empty i (hE ▸ he)
    apply hbad
    rw [hg]
    have hQker0 : (planeMatrix u (D \ F) a 0).mulVec (fun j => Q.coeff j.val) = 0 :=
      Eq.mp (congrArg (fun n => (planeMatrix u (D \ F) a n).mulVec (fun j => Q.coeff j.val) = 0) hd) hQker
    exact joint_of_zero_error_kernel u (D \ F) a (by simpa only [hd, add_zero] using hD)
      Q hQ0 (by simpa only [hd] using hQd) hQker0
  have hgen : ((planeMatrix u (D \ F) a d).map (algebraMap Bivar (FractionRing Bivar))).rank = d := by
    apply le_antisymm (generic_rank_le_of_locator _ hQ0 hQd hQker)
    calc
      d = ((planeMatrix u (D \ F) a d).map (onGraph γ₀)).rank := (hshort_mark γ₀ hγ₀).2.2.2.symm
      _ ≤ _ := K1_2_3.rank_ge_specialization _ (onGraph γ₀) _ (IsFractionRing.injective Bivar _)
  have hshort : RegularPlane u (D \ F) a d Γ P := ⟨hD, hgen, hshort_mark⟩
  obtain ⟨L', hL', hbox'⟩ := hbox u (D \ F) Γ P a d (by omega) (by omega) hΓ hshort
  have hno' (i : I) (hi : i ∈ D \ F) : nodeEquation L' i ≠ 0 :=
    repack_node_nonzero _ hgen (locator_nonzero hL' hΓ) hQ0 hL'.degree hQd hL'.kernel hQker i (hno i hi)
  have hda : a < d := by
    by_contra hn
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [(hshort_mark γ₀ hγ₀).2.1]; omega)
    have hzero := (K1_2_4_1.root_iff_error hL' hγ₀ i).mpr hi
    have hz : d-a = 0 := by omega
    apply hno' i (Finset.mem_sdiff.mp hi).1
    exact constant_node_specialization (by simpa only [hz] using nodeEquation_box L' _ _ hbox' i) γ₀ hzero
  have hfb : F.card < b := by omega
  have heq : d = a+(b-F.card) := by omega
  have hbeq : d-a = b-F.card := by omega
  exact Or.inr ⟨F, L', hF, hfb, hsub, heq ▸ hshort,
    ⟨heq ▸ hL'.degree, heq ▸ hL'.kernel, fun j => hbeq ▸ hbox' j, hno', hL'.fiber⟩⟩

end

end K1_2_4_1
end PackSource_K1_2_4_1Split

section PackSource_K1_2_4_1_1Fiber
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace K1_2_4_1_1

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2

/-- At exact error weight and rank, the leading columns retain the whole rank,
and each block has an independent prefix of the required length. -/
theorem fiber_data {u : Words} {D : Finset I} {a d : ℕ} {γ : K} {P : K[X]}
    (hD : D.card = 131072+a+d) (hP : P.degree < 131072)
    (hE : (errorSet u D γ P).card = d)
    (hrank : ((planeMatrix u D a d).map (onGraph γ)).rank = d) :
    let M := (planeMatrix u D a d).map (onGraph γ)
    let A := M.submatrix id Fin.castSucc
    A.rank = d ∧
      (∀ b : Fin 2, LinearIndependent K (fun j : Fin (min a d) =>
        A.row (b, j.castLE (min_le_left _ _)))) ∧
      M.mulVec (fun j => (locator node (errorSet u D γ P)).coeff j.val) = 0 := by
  classical
  dsimp only
  let M := (planeMatrix u D a d).map (onGraph γ)
  let x : D → K := fun i => node i.val
  let w : D → K := fun i => u 0 i.val + γ * u 1 i.val
  let σ := Strata.twoConjugations (frobenius K p)
  let E := (errorSet u D γ P).subtype (· ∈ D)
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have herr (i : D) : i ∈ E ↔ P.eval (x i) ≠ w i := by
    simp [E, errorSet, goodSet, x, w, Finset.mem_subtype, i.property]
  have hagree (i : D) (hi : i ∉ E) : w i = P.eval (x i) := by
    by_contra hn
    exact hi ((herr i).mpr (Ne.symm hn))
  have hEc : Fintype.card E = d := by
    have heq : E.map (Function.Embedding.subtype (· ∈ D)) = errorSet u D γ P :=
      Finset.subtype_map_of_mem (fun i hi => (Finset.mem_sdiff.mp hi).1)
    rw [Fintype.card_coe, ← Finset.card_map (f := Function.Embedding.subtype (· ∈ D)), heq, hE]
  have hfix (b : Fin 2) (i : D) : σ b (x i) = x i := by
    fin_cases b
    · rfl
    · exact Native.native_domain_fixed i.val
  let W (b : Fin 2) (i : E) := weight x i.val * σ b (w i.val - P.eval (x i.val))
  let H : Matrix (Fin 2 × Fin a) E K := fun j i => W j.1 i * x i.val ^ j.2.val
  let V := Strata.nodeVandermonde (fun i : E => x i.val) d
  have hfactor : M = H * V := by
    change (planeMatrix u D a d).map (onGraph γ) = _
    rw [K1_2_3.plane_at_slope]
    exact Strata.conjugateHankel_factorization σ x w hx hfix P 131072 a d hP
      (by rw [Fintype.card_coe, hD]) E hagree
  let e : Fin d ≃ E := (Fintype.equivFinOfCardEq hEc).symm
  let y : Fin d → K := fun i => x (e i).val
  have hy : Function.Injective y := hx.comp (Subtype.val_injective.comp e.injective)
  let C := H.submatrix id e
  have hC : C.rank = d := by
    have hlo := Matrix.rank_mul_le_left H V
    rw [← hfactor, show M.rank = d from hrank] at hlo
    have hhi := H.rank_le_card_width
    rw [hEc] at hhi
    rw [show C.rank = H.rank from Matrix.rank_submatrix H (Equiv.refl _) e]
    exact le_antisymm hhi hlo
  have hlead : M.submatrix id Fin.castSucc = C * Matrix.vandermonde y := by
    rw [hfactor]
    exact Matrix.submatrix_mul H V id e Fin.castSucc e.bijective
  have hdet := Matrix.det_vandermonde_ne_zero_iff.mpr hy
  refine ⟨?_, ?_, ?_⟩
  · rw [show ((planeMatrix u D a d).map (onGraph γ)).submatrix id Fin.castSucc =
        M.submatrix id Fin.castSucc from rfl, hlead, Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdet, hC]
  · intro b
    let m := min a d
    let r : Fin m → Fin 2 × Fin a := fun j => (b, j.castLE (min_le_left _ _))
    let c : Fin m ↪ Fin d := Fin.castLEEmb (min_le_right _ _)
    have hW (i : Fin d) : W b (e i) ≠ 0 := by
      apply mul_ne_zero (Strata.weight_ne_zero x hx _)
      intro hz
      have he := (σ b).injective (hz.trans (map_zero _).symm)
      exact ((herr (e i).val).mp (e i).property) (sub_eq_zero.mp he).symm
    have hsquare : C.submatrix r c =
        (Matrix.vandermonde (y ∘ c)).transpose * Matrix.diagonal (fun i => W b (e (c i))) := by
      apply Matrix.ext
      intro j k
      simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.transpose_apply,
        Matrix.vandermonde_apply, Function.comp_apply, C, H, r, y]
      exact mul_comm _ _
    have hsq : (C.submatrix r c).det ≠ 0 := by
      rw [hsquare, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
      exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (hy.comp c.injective))
        (Finset.prod_ne_zero_iff.mpr fun i _ => hW (c i))
    have hprefix : (C.submatrix r id).rank = m := by
      have hlo := Matrix.rank_submatrix_le (C.submatrix r id) id c
      change (C.submatrix r c).rank ≤ _ at hlo
      rw [Matrix.rank_of_det_ne_zero hsq, Fintype.card_fin] at hlo
      exact le_antisymm (by simpa using (C.submatrix r id).rank_le_card_height) hlo
    change LinearIndependent K ((M.submatrix id Fin.castSucc).submatrix r id).row
    have hsub : (C * Matrix.vandermonde y).submatrix r id =
        C.submatrix r id * Matrix.vandermonde y := rfl
    rw [hlead, hsub]
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row,
      Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdet, hprefix, Fintype.card_fin]
  · let T := locator node (errorSet u D γ P)
    have hTd : T.natDegree ≤ d := by
      change (locator node _).natDegree ≤ d
      rw [locator_natDegree, hE]
    have hv : V.mulVec (fun j => T.coeff j.val) = 0 := by
      funext i
      change (∑ j : Fin (d+1), x i.val ^ j.val * T.coeff j.val) = 0
      have hz : T.eval (x i.val) = 0 :=
        locator_eval_zero node (errorSet u D γ P) i.val.val (Finset.mem_subtype.mp i.property)
      rw [← hz, ← sum_coeff_eval T d hTd]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    change M.mulVec (fun j => T.coeff j.val) = 0
    rw [hfactor, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

end

end K1_2_4_1_1
end PackSource_K1_2_4_1_1Fiber

section PackSource_K1_2_4_3Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

namespace K1_2_4_3

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K1 K1_2

/-- Once common errors have been punctured, each node contributes only
the roots of its nonzero locator evaluation polynomial. -/
private theorem moving_count {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (x u v : ι → F) (hx : Function.Injective x) (k a r : ℕ)
    (hr : 0 < r) (hra : r < a) (hn : k + a + r = Fintype.card ι)
    (Γ : Finset F) (P : F → F[X]) (E : F → Finset ι) (hlarge : r + 1 < Γ.card)
    (hP : ∀ γ ∈ Γ, (P γ).degree < k)
    (hE : ∀ γ ∈ Γ, (E γ).card = r)
    (hout : ∀ γ ∈ Γ, ∀ i, i ∉ E γ → u i + γ * v i = (P γ).eval (x i))
    (hin : ∀ γ ∈ Γ, ∀ i ∈ E γ, u i + γ * v i ≠ (P γ).eval (x i))
    (hmoving : ∀ i, ∃ γ ∈ Γ, i ∉ E γ) :
    Γ.card ≤ Fintype.card ι / (a - r + 1) := by
  classical
  let s := a - r + 1
  let M := hankel x u v a r
  let φ := algebraMap F[X] (GenericLayer.GenericField F)
  have hφ := IsFractionRing.injective F[X] (GenericLayer.GenericField F)
  have heval (γ : F) (hγ : γ ∈ Γ) : (M.map (evalRingHom γ)).rank = r := by
    rw [K1_3.evaluated_hankel_rank x u v hx γ (P γ) k a r (hP γ hγ) hn.le (E γ)
      (by rw [hE γ hγ]; omega) (hout γ hγ) (hin γ hγ), hE γ hγ, min_eq_left hra.le]
  have hentry (i : Fin a) (j : Fin (r + 1)) : (M i j).natDegree ≤ 1 :=
    hankel_entry_natDegree x u v a r i j
  have hupper : (M.map φ).rank ≤ r := by
    by_contra! hnrank
    have hwidth := Matrix.rank_le_card_width (M.map φ)
    rw [Fintype.card_fin] at hwidth
    have hfull : (M.map φ).rank = r + 1 := by omega
    obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M (r + 1) hfull
    have hdeg : (NormalFiber.pivot B).det.natDegree ≤ r + 1 := by
      simpa using NormalFiber.minor_degree_le φ M (r + 1) B (fun _ => 1) hentry
    have hcard : Γ.card ≤ (NormalFiber.pivot B).det.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro γ hγ
      apply (Polynomial.mem_roots B.minor_ne).mpr
      by_contra hnonzero
      have hnormal := NormalFiber.rank_specializes φ hφ M (r + 1) B γ hnonzero
      have hactual := heval γ hγ
      omega
    omega
  let seq (j : ℕ) := Polynomial.C (syndrome x u j) + Polynomial.X * Polynomial.C (syndrome x v j)
  let A := Matrix.of (fun (i j : Fin r) => seq (i.val + j.val))
  have hpivotEval (γ : F) (hγ : γ ∈ Γ) : (A.map (evalRingHom γ)).det ≠ 0 := by
    have heq : A.map (evalRingHom γ) =
        Matrix.of (fun (i j : Fin r) => syndrome x (fun i => u i + γ * v i) (i.val + j.val)) := by
      ext i j
      exact congrFun (congrFun (K1_3.evaluated_hankel x u v γ r r) i) (Fin.castSucc j)
    rw [heq]
    exact K1_3.moment_det_ne_zero x _ hx (P γ) k r (hP γ hγ) (by omega)
      (E γ) (hE γ hγ) (hout γ hγ) (hin γ hγ)
  obtain ⟨γ₀, hγ₀⟩ : Γ.Nonempty := Finset.card_pos.mp (by omega)
  have hpivot : A.det ≠ 0 := by
    intro hz
    apply hpivotEval γ₀ hγ₀
    rw [← RingHom.mapMatrix_apply, ← (evalRingHom γ₀).map_det, hz, map_zero]
  have hAφ : (A.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← φ.map_det]
    exact fun hz => hpivot (hφ (hz.trans (map_zero φ).symm))
  let rows (i : Fin r) : Fin a := ⟨i.val, i.isLt.trans hra⟩
  have hlower := Matrix.rank_submatrix_le (M.map φ) rows Fin.castSucc
  change (A.map φ).rank ≤ (M.map φ).rank at hlower
  rw [Matrix.rank_of_det_ne_zero hAφ, Fintype.card_fin] at hlower
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M r (le_antisymm hupper hlower)
  obtain ⟨q, hprim, hker, _, _⟩ := GenericCofactor.exists_primitive_line B hφ (by simp)
    (fun _ => 1) hentry
  obtain ⟨H, hH, hsharp⟩ := sharp_hankel_height seq r s (by omega)
    (fun j => by dsimp [seq]; compute_degree) q hprim
    (fun i hi => congrFun hker ⟨i, by dsimp [s] at hi; omega⟩) hpivot
  let Q (i : ι) : F[X] := ∑ j : Fin (r + 1), Polynomial.C (x i ^ j.val) * q j
  have hQdeg (i : ι) : (Q i).natDegree ≤ H :=
    Polynomial.natDegree_sum_le_of_forall_le _ _
      (fun j _ => (Polynomial.natDegree_C_mul_le _ _).trans (hH j))
  have hQroots (γ : F) (hγ : γ ∈ Γ) (i : ι) : (Q i).eval γ = 0 ↔ i ∈ E γ := by
    let L := locator x (E γ)
    have hLd : L.natDegree = r := (locator_natDegree _ _).trans (hE γ hγ)
    have hLtop : L.coeff r = 1 := hLd ▸ (locator_monic x (E γ)).coeff_natDegree
    have hL0 : (fun j : Fin (r + 1) => L.coeff j.val) ≠ 0 := by
      intro hz
      have hh : L.coeff r = 0 := congrFun hz (Fin.last r)
      exact one_ne_zero (hLtop.symm.trans hh)
    have hLker : (M.map (evalRingHom γ)).mulVec (fun j => L.coeff j.val) = 0 := by
      apply hankel_annihilates x hx u v γ k a r hn.le (P γ) L (hP γ hγ) hLd.le
      intro j
      by_cases hj : j ∈ E γ
      · simp [L, locator_eval_zero x (E γ) j hj]
      · rw [hout γ hγ j hj]
    have hqker : (M.map (evalRingHom γ)).mulVec (fun j => (q j).eval γ) = 0 := by
      funext i
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
        map_sum, map_mul, map_zero, Pi.zero_apply] using
        congrArg (evalRingHom γ) (congrFun hker i)
    have hnull := GenericRank.nullity_one_of_rank (M.map (evalRingHom γ))
      (by rw [heval γ hγ, Fintype.card_fin])
    obtain ⟨c, hc⟩ := GenericRank.kernel_line_of_finrank _ hnull _ hL0 hLker _ hqker
    have hcne : c ≠ 0 := by
      intro hz
      exact PrimitiveVector.eval_ne_zero q hprim γ (by simp [hc, hz])
    have hQeval : (Q i).eval γ = c * L.eval (x i) := by
      rw [← sum_coeff_eval L r hLd.le, Finset.mul_sum]
      simp only [Q, eval_finsetSum, eval_mul, eval_C]
      apply Finset.sum_congr rfl
      intro j _
      rw [congrFun hc j]
      change x i ^ j.val * (c * L.coeff j.val) = c * (L.coeff j.val * x i ^ j.val)
      ring
    rw [hQeval, mul_eq_zero, or_iff_right hcne]
    exact Principal.locator_eval_zero_iff x hx _ i
  have hfiber (i : ι) : (Γ.filter (fun γ => i ∈ E γ)).card ≤ H := by
    obtain ⟨γ, hγ, hi⟩ := hmoving i
    have hne : Q i ≠ 0 := fun hz => hi ((hQroots γ hγ i).mp (by simp [hz]))
    apply (Polynomial.card_le_degree_of_subset_roots ?_).trans (hQdeg i)
    intro ζ hζ
    exact (Polynomial.mem_roots hne).mpr ((hQroots ζ (Finset.mem_filter.mp hζ).1 i).mpr
      (Finset.mem_filter.mp hζ).2)
  have hinc := K1_2.Pruning.root_incidence Γ Finset.univ ∅ E r
    (fun γ _ => Finset.subset_univ (E γ)) hE
  simp only [Finset.card_empty, Nat.sub_zero, Finset.sdiff_empty] at hinc
  have hdouble : r * Γ.card ≤ Fintype.card ι * H := hinc.trans (by
    calc
      _ ≤ ∑ _i : ι, H := Finset.sum_le_sum (fun i _ => hfiber i)
      _ = _ := by simp)
  apply (Nat.le_div_iff_mul_le (by omega : 0 < s)).mpr
  apply Nat.le_of_mul_le_mul_right _ hr
  calc
    (Γ.card * s) * r = (r * Γ.card) * s := by ac_rfl
    _ ≤ (Fintype.card ι * H) * s := Nat.mul_le_mul_right _ hdouble
    _ = Fintype.card ι * (s * H) := by ac_rfl
    _ ≤ Fintype.card ι * r := Nat.mul_le_mul_left _ hsharp

theorem proof : K1_2_4.c3 := by
  classical
  intro u D Γ P a d hda hD hmark
  have hfloor : 1 ≤ (131072 + a + d) / (a - d + 1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  by_cases hs : Γ.card ≤ d + 1
  · omega
  have hlarge : d + 1 < Γ.card := by omega
  obtain ⟨γ₀, hγ₀⟩ : Γ.Nonempty := Finset.card_pos.mp (by omega)
  let F := D.filter (fun i => ∀ γ ∈ Γ, i ∈ errorSet u D γ (P γ))
  let B := D \ F
  let r := d - F.card
  have hF (γ : K) (hγ : γ ∈ Γ) : F ⊆ errorSet u D γ (P γ) :=
    fun _ hi => (Finset.mem_filter.mp hi).2 γ hγ
  have hFD : F ⊆ D := Finset.filter_subset _ _
  have hFle : F.card ≤ d := (Finset.card_le_card (hF γ₀ hγ₀)).trans (hmark γ₀ hγ₀).2.1.le
  have hB : B.card = 131072 + a + r := by
    rw [Finset.card_sdiff_of_subset hFD, hD]
    dsimp [r]
    omega
  have hgood (γ : K) (hγ : γ ∈ Γ) (i : I) :
      i ∈ goodSet u D γ (P γ) → i ∈ B := by
    intro hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hi).1, fun hf =>
      (Finset.mem_sdiff.mp (hF γ hγ hf)).2 hi⟩
  let x (i : B) : K := node i.val
  let E (γ : K) : Finset B := Finset.univ.filter (fun i => i.val ∈ errorSet u D γ (P γ))
  have hE (γ : K) (hγ : γ ∈ Γ) : (E γ).card = r := by
    let f : B ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
    have heq : (E γ).map f = errorSet u D γ (P γ) \ F := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hj).2, (Finset.mem_sdiff.mp j.property).2⟩
      · intro hi
        obtain ⟨he, hf⟩ := Finset.mem_sdiff.mp hi
        let j : B := ⟨i, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp he).1, hf⟩⟩
        exact Finset.mem_map.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
    rw [← Finset.card_map f, heq, Finset.card_sdiff_of_subset (hF γ hγ), (hmark γ hγ).2.1]
  have hout (γ : K) (i : B) (hi : i ∉ E γ) :
      u 0 i.val + γ * u 1 i.val = (P γ).eval (x i) := by
    apply Eq.symm
    have hnot : i.val ∉ errorSet u D γ (P γ) :=
      fun he => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    have hiD := (Finset.mem_sdiff.mp i.property).1
    by_contra hn
    apply hnot
    exact Finset.mem_sdiff.mpr ⟨hiD, fun hg => hn (Finset.mem_filter.mp hg).2⟩
  by_cases hr : 0 < r
  · have hc := moving_count x (fun i => u 0 i.val) (fun i => u 1 i.val)
      (ProximityPrize.Benchmark.IRSProfile.domain.injective.comp Subtype.val_injective)
      131072 a r hr (by dsimp [r]; omega) (by simpa using hB.symm) Γ P E
      (by dsimp [r]; omega) (fun γ hg => (hmark γ hg).1) hE (fun γ _ => hout γ) ?_ ?_
    · have hn : Fintype.card B ≤ 131072 + a + d := by rw [Fintype.card_coe, hB]; dsimp [r]; omega
      have hrd : r ≤ d := Nat.sub_le _ _
      have hdiv : (131072 + a + d) / (a - r + 1) ≤ (131072 + a + d) / (a - d + 1) :=
        Nat.div_le_div_left (by omega) (by omega)
      exact (hc.trans ((Nat.div_le_div_right hn).trans hdiv)).trans (Nat.le_add_left _ _)
    · intro γ _ i hi he
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).2).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp i.property).1, he.symm⟩)
    · intro i
      by_contra! hi
      apply (Finset.mem_sdiff.mp i.property).2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp i.property).1,
        fun γ hg => (Finset.mem_filter.mp (hi γ hg)).2⟩
  · have hsmall := K1_3.fixed_error_count node (u 0) (u 1) 131072 Γ (Finset.univ \ B) P
      (fun γ => goodSet u D γ (P γ)) (fun γ hg => (hmark γ hg).1) ?_ ?_
      (fun γ hg => (hmark γ hg).2.2)
    · omega
    · intro γ hg i hi
      have hmem : i ∈ B := by simpa using hi
      have he : E γ = ∅ := Finset.card_eq_zero.mp (by rw [hE γ hg]; omega)
      exact hout γ ⟨i, hmem⟩ (by simp [he])
    · intro γ hg i hi h
      exact (Finset.mem_sdiff.mp h).2 (hgood γ hg i hi)

end

end K1_2_4_3
end PackSource_K1_2_4_3Proof

section PackSource_K1_2_4_2Contraction
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K1_2_4_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2 K1_2_4

/-- Coefficients of multiplication by a fixed polynomial on bounded inputs. -/
def convolution {F : Type*} [CommRing F] (Δ : F[X]) (R d : ℕ) :
    Matrix (Fin (R + 1)) (Fin (d + 1)) F :=
  fun j k => (Δ * Polynomial.X ^ k.val).coeff j.val

theorem convolution_map {F E : Type*} [CommRing F] [CommRing E]
    (φ : F →+* E) (Δ : F[X]) (R d : ℕ) :
    (convolution Δ R d).map φ = convolution (Δ.map φ) R d := by
  ext j k
  change φ ((Δ * Polynomial.X ^ k.val).coeff j.val) = _
  rw [← Polynomial.coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  rfl

theorem convolution_action {F : Type*} [CommRing F] (Δ T : F[X]) (R d : ℕ)
    (hT : T.natDegree ≤ d) :
    (convolution Δ R d).mulVec (fun j => T.coeff j.val) =
      fun j => (Δ * T).coeff j.val := by
  have hsum : T = ∑ k : Fin (d + 1), Polynomial.C (T.coeff k.val) *
      (Polynomial.X (R := F)) ^ k.val := by
    rw [Fin.sum_univ_eq_sum_range (fun n => Polynomial.C (T.coeff n) *
      (Polynomial.X (R := F)) ^ n)]
    exact T.as_sum_range_C_mul_X_pow' (by omega)
  funext j
  have heq : Δ * T = ∑ k : Fin (d + 1), Polynomial.C (T.coeff k.val) *
      (Δ * Polynomial.X ^ k.val) := by
    calc
      Δ * T = Δ * (∑ k : Fin (d + 1), Polynomial.C (T.coeff k.val) *
          (Polynomial.X (R := F)) ^ k.val) :=
        congrArg (Δ * ·) hsum
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [heq, finsetSum_coeff]
  simp only [Matrix.mulVec, dotProduct, convolution, coeff_C_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def contracted (u : Words) (D F : Finset I) (a R d : ℕ) :
    Matrix (Fin 2 × Fin a) (Fin (d + 1)) Bivar :=
  planeMatrix u D a R * (convolution (locator node F) R d).map planeConstant

theorem eval_nodeEquation {E : Type*} [Field E] (φ : Bivar →+* E)
    (L : Bivar[X]) (i : I) :
    φ (nodeEquation L i) = (L.map φ).eval (φ (planeConstant (node i))) := by
  rw [nodeEquation, Polynomial.eval_map_apply]

theorem graph_constant (γ c : K) : onGraph γ (planeConstant c) = c := by
  rw [K1_2_4.evalGraph]
  simp [planeConstant]

/-- The fixed-node equations divide the locator after any specialization
that kills them. Multiplication by that divisor contracts the matrix. -/
theorem contracted_kernel {E : Type} [Field E] (φ : Bivar →+* E)
    {u : Words} {D F : Finset I} {a R d : ℕ} {L : Bivar[X]}
    (hsize : R = d + F.card) (hL : L.natDegree ≤ R)
    (hker : (planeMatrix u D a R).mulVec (fun j => L.coeff j.val) = 0)
    (hF : ∀ i ∈ F, φ (nodeEquation L i) = 0) (hL0 : L.map φ ≠ 0) :
    ∃ T : E[X], T ≠ 0 ∧ T.natDegree ≤ d ∧
      L.map φ = locator (φ ∘ planeConstant ∘ node) F * T ∧
      ((contracted u D F a R d).map φ).mulVec (fun j => T.coeff j.val) = 0 := by
  classical
  let x := φ ∘ planeConstant ∘ node
  have hx : Function.Injective x :=
    (φ.comp planeConstant).injective.comp IRSProfile.domain.injective
  have hdiv : locator x F ∣ L.map φ :=
    Strata.locator_dvd_of_eval_zero x hx F _ (fun i hi =>
      (eval_nodeEquation φ L i).symm.trans (hF i hi))
  obtain ⟨T, hfactor⟩ := hdiv
  have hT0 : T ≠ 0 := fun hz => hL0 (by rw [hfactor, hz, mul_zero])
  have hdegree := (Polynomial.natDegree_map_le (f := φ) (p := L)).trans hL
  rw [hfactor, Polynomial.natDegree_mul (locator_monic x F).ne_zero hT0,
    locator_natDegree] at hdegree
  have hTd : T.natDegree ≤ d := by omega
  refine ⟨T, hT0, hTd, hfactor, ?_⟩
  have hmap : ((planeMatrix u D a R).map φ).mulVec
      (fun j => (L.map φ).coeff j.val) = 0 := by
    funext j
    have hj := congrArg φ (congrFun hker j)
    simpa only [RingHom.map_mulVec, Function.comp_def, Pi.zero_apply, map_zero,
      coeff_map] using hj
  have hc :
      ((convolution (locator node F) R d).map planeConstant).map φ =
        convolution (locator x F) R d := by
    change ((convolution (locator node F) R d).map (φ.comp planeConstant)) = _
    rw [convolution_map, locator_map]
    rfl
  rw [contracted, Matrix.map_mul, hc, ← Matrix.mulVec_mulVec, convolution_action _ _ _ _ hTd,
    ← hfactor]
  exact hmap

theorem coeff_vec_ne_zero {E : Type*} [Field E] (T : E[X]) (d : ℕ)
    (hTd : T.natDegree ≤ d) (hT0 : T ≠ 0) :
    (fun j : Fin (d + 1) => T.coeff j.val) ≠ 0 := by
  intro h
  have hz := congrFun h (⟨T.natDegree, by omega⟩ : Fin (d + 1))
  exact hT0 (Polynomial.leadingCoeff_eq_zero.mp hz)

instance curveDomain (Q : Bivar) [Fact (Prime Q)] : IsDomain (AdjoinRoot Q) :=
  AdjoinRoot.isDomain_of_prime Fact.out

abbrev CurveField (Q : Bivar) [Fact (Prime Q)] := FractionRing (AdjoinRoot Q)

def curveMap (Q : Bivar) [Fact (Prime Q)] : Bivar →+* CurveField Q :=
  (algebraMap (AdjoinRoot Q) (CurveField Q)).comp (AdjoinRoot.mk Q)

theorem curveMap_zero_iff (Q V : Bivar) [Fact (Prime Q)] : curveMap Q V = 0 ↔ Q ∣ V := by
  change algebraMap (AdjoinRoot Q) (CurveField Q) (AdjoinRoot.mk Q V) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (AdjoinRoot Q) (CurveField Q)),
    AdjoinRoot.mk_eq_zero]

end

end K1_2_4_2
end PackSource_K1_2_4_2Contraction

section PackSource_K1_2_2_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace K1_2_2_2

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2_2 K1_6
open scoped BigOperators

private theorem map_syndrome {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (f : F →+* E) (x w : ι → F) (j : ℕ) :
    f (syndrome x w j) = syndrome (fun i => f (x i)) (fun i => f (w i)) j := by
  simp only [syndrome, weight, map_sum, map_mul, map_pow, map_inv₀, map_prod, map_sub]

private def NodeIdentity {F ι : Type} [Field F] (q : ℕ) (y u v : ι → F)
    (U V out : F[X][X]) : Prop :=
  ∀ i, U.eval (C (y i)) * (C (u i) + Polynomial.X * C (v i)) +
    V.eval (C (y i)) * (C (u i ^ q) + Polynomial.X ^ q * C (v i ^ q)) =
      out.eval (C (y i))

/-- The all-node identity, multiplied by each bounded shift, has an output
whose dual moments vanish on the same domain as the stack. -/
private theorem shifts_annihilate {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (q : ℕ) [ExpChar F q]
    (y u v : ι → F) (hy : Function.Injective y) (hfix : ∀ i, y i ^ q = y i)
    (φ : F[X] →+* E) (hφ : Function.Injective φ)
    (k h L t s : ℕ) (hL : h + s = L + 1)
    (hsize : k + (L + 1) + t ≤ Fintype.card ι)
    (P : Fin 2 → F[X][X]) (out : F[X][X])
    (hP : ∀ b, (P b).natDegree ≤ h)
    (hout : out.degree < (k + h : ℕ))
    (hnodes : NodeIdentity q y u v (P 0) (P 1) out) :
    (shifts P (L + 1) s).transpose * stacked q y u v (L + 1) t = 0 := by
  classical
  let f : F →+* E := φ.comp Polynomial.C
  let x : ι → E := fun i => f (y i)
  let z : E := φ Polynomial.X
  let w (b : Fin 2) (i : ι) : E :=
    if b = 0 then f (u i) + z * f (v i) else f (u i ^ q) + z ^ q * f (v i ^ q)
  have hmoment (b : Fin 2) (l : Fin (L + 1)) (j : Fin (t + 1)) :
      φ (stacked q y u v (L + 1) t (b, l) j) = syndrome x (w b) (l.val + j.val) := by
    by_cases hb : b = 0
    · simp only [stacked, hankel, hb, ite_true, map_add, map_mul]
      change f (syndrome y u _) + z * f (syndrome y v _) = _
      rw [map_syndrome, map_syndrome]
      simpa only [w, hb, ite_true, one_mul] using
        (Principal.syndrome_linear x (fun i => f (u i)) (fun i => f (v i)) 1 z _).symm
    · simp only [stacked, hb, ite_false]
      rw [φ.map_add, φ.map_mul, φ.map_pow Polynomial.X]
      change f (syndrome y u _ ^ q) + z ^ q * f (syndrome y v _ ^ q) = _
      rw [← syndrome_frobenius q y hfix, ← syndrome_frobenius q y hfix,
        map_syndrome, map_syndrome]
      simpa only [w, hb, ite_false, one_mul] using
        (Principal.syndrome_linear x (fun i => f (u i ^ q))
          (fun i => f (v i ^ q)) 1 (z ^ q) _).symm
  have hnode (i : ι) :
      ((P 0).map φ).eval (x i) * w 0 i + ((P 1).map φ).eval (x i) * w 1 i =
        (out.map φ).eval (x i) := by
    simpa only [x, f, RingHom.comp_apply, z, w, ite_true, one_ne_zero, ite_false,
      map_add, map_mul, map_pow, eval_map_apply] using congrArg φ (hnodes i)
  apply Matrix.ext
  intro d j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, shifts]
  apply hφ
  let B (b : Fin 2) : E[X] := (P b).map φ * Polynomial.X ^ d.val
  have hd : h + d.val ≤ L := by have := d.isLt; omega
  have hB (b : Fin 2) : (B b).natDegree ≤ L :=
    natDegree_mul_le.trans (by
      rw [natDegree_X_pow]
      exact (Nat.add_le_add_right (natDegree_map_le.trans (hP b)) _).trans hd)
  have hshift (i : ι) :
      (B 0).eval (x i) * w 0 i + (B 1).eval (x i) * w 1 i =
        ((out.map φ) * Polynomial.X ^ d.val).eval (x i) := by
    simp only [B, eval_mul, eval_pow, eval_X]
    rw [← hnode i]
    ring
  have hdeg : ((out.map φ) * Polynomial.X ^ d.val).degree < ((k + L : ℕ) : WithBot ℕ) := by
    have hmul := Strata.degree_mul_lt_add (Polynomial.X ^ d.val : E[X])
      (out.map φ) d.val (k + h) (by simp) (degree_map_le.trans_lt hout)
    rw [mul_comm] at hmul
    apply hmul.trans_le
    exact_mod_cast (show k + h + d.val ≤ k + L by omega)
  rw [map_sum, map_zero, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [map_mul, hmoment, ← coeff_map, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X]
  change (∑ l : Fin (L + 1), (B 0).coeff l.val * syndrome x (w 0) (l.val + j.val)) +
    (∑ l : Fin (L + 1), (B 1).coeff l.val * syndrome x (w 1) (l.val + j.val)) = 0
  rw [← Strata.syndrome_polynomial_multiple x (w 0) (B 0) L j.val (hB 0),
    ← Strata.syndrome_polynomial_multiple x (w 1) (B 1) L j.val (hB 1)]
  have hlin := Principal.syndrome_linear x
    (fun i => (B 0).eval (x i) * w 0 i) (fun i => (B 1).eval (x i) * w 1 i) 1 1 j.val
  simp only [one_mul] at hlin
  rw [← hlin]
  simp_rw [hshift]
  apply Strata.syndrome_eval_zero x (f.injective.comp hy) _ (k + L) _ hdeg
  have := j.isLt
  omega

private def fieldPower {F : Type} [Field F] (x : F) (n : ℕ) : F := x ^ n

/-- The benchmark's concrete exponentiation agrees with the field power
used by the generic syndrome lemmas. -/
private theorem native_field_power (x : K) (n : ℕ) : fieldPower x n = x ^ n := by
  rw [CompPoly.Extension.Ext.pow_def]
  have hzero : fieldPower x 0 = 1 := pow_zero x
  have hsucc (m : ℕ) : fieldPower x (m + 1) = fieldPower x m * x := pow_succ x m
  induction n with
  | zero => rw [hzero, npowBinRec_zero]
  | succ n ih => rw [hsucc, npowBinRec_succ, ih]

private theorem restricted_nodes (q : ℕ) {u : Words} {S : Finset I} (U V out : Bivar)
    (hnodes : K1_8.relationOnAt q u S (C 1 * U) (C 1 * V) (C 1 * out)) :
    NodeIdentity q (fun i : (Finset.univ \ S : Finset I) => node i.val)
      (fun i => u 0 i.val) (fun i => u 1 i.val) U V out := by
  intro i
  have hi : i.val ∉ S := (Finset.mem_sdiff.mp i.property).2
  change U.eval (C (node i.val)) * (C (u 0 i.val) + Polynomial.X * C (u 1 i.val)) +
    V.eval (C (node i.val)) *
      (C (fieldPower (u 0 i.val) q) + Polynomial.X ^ q * C (fieldPower (u 1 i.val) q)) =
    out.eval (C (node i.val))
  rw [native_field_power, native_field_power]
  have h := hnodes i.val hi
  simpa only [Polynomial.C_1, one_mul] using h

private theorem native_relation : relationOn = K1_8.relationOnAt p := rfl

theorem proof : K1_2_2.c2 := by
  classical
  intro u T R A
  let D := Finset.univ \ fixedNodes R
  have hheight : T.height ≤ 49193 := by
    unfold TwoActive.height
    have := T.inactive
    omega
  have hL : A.height + (49193 - A.height) = 49192 + 1 := by
    have := A.height_eq
    omega
  have hsize : 131072 + (49192 + 1) + (81879 - (fixedNodes R).card) ≤ Fintype.card D := by
    rw [Fintype.card_coe, domain_card]
    have := A.height_eq
    omega
  refine shifts_annihilate (F := K) (E := Frac) (ι := D) p
    (fun i => node i.val) (fun i => u 0 i.val) (fun i => u 1 i.val)
    (IRSProfile.domain.injective.comp Subtype.val_injective)
    (fun i => Native.native_domain_fixed i.val)
    (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
    131072 A.height 49192 _ _ hL hsize (pair A) A.output (pair_degree A) A.output_degree ?_
  apply restricted_nodes p (u := u) (S := fixedNodes R) A.U A.V A.output
  rw [← native_relation]
  exact K1_8.reduced_scaled_relation A (1 : K[X])

end

end K1_2_2_2
end PackSource_K1_2_2_2Proof

section PackSource_K1_2_4_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace K1_2_4_1_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2 K1_2_4 K1_2_4_1
open scoped BigOperators

/-- The dual weight written on a finite set of grid indices. -/
private def gridWeight (D : Finset I) (i : I) : K :=
  (∏ j ∈ D.erase i, (node i - node j))⁻¹

private theorem weight_on_grid (D : Finset I) (i : D) :
    weight (fun j : D => node j.val) i = gridWeight D i.val := by
  classical
  let e : D ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hu : (univ : Finset D).map e = D := by
    ext j
    constructor
    · intro hj
      obtain ⟨k, _, hk⟩ := mem_map.mp hj
      exact hk ▸ k.property
    · intro hj
      exact mem_map.mpr ⟨⟨j, hj⟩, mem_univ _, rfl⟩
  have he : ((univ : Finset D).erase i).map e = D.erase i.val := by
    rw [Finset.map_erase, hu]
    rfl
  unfold weight gridWeight
  exact congrArg (fun x : K => x⁻¹)
    ((Finset.prod_map _ e (fun j => node i.val - node j)).symm.trans
      (congrArg (fun S : Finset I => ∏ j ∈ S, (node i.val - node j)) he))

private theorem eval_locator_at_node (F : Finset I) (i : I) :
    (locator node F).eval (node i) = ∏ j ∈ F, (node i - node j) := by
  simp only [locator, eval_prod, eval_sub, eval_X, eval_C]

/-- Recompute the surviving weight by cancelling the nonzero deleted factors. -/
private theorem gridWeight_puncture {D F : Finset I} (hF : F ⊆ D)
    {i : I} (hi : i ∈ D \ F) :
    gridWeight (D \ F) i = gridWeight D i * (locator node F).eval (node i) := by
  have hiF := (mem_sdiff.mp hi).2
  have hs : F ⊆ D.erase i := fun j hj =>
    mem_erase.mpr ⟨fun h => hiF (h ▸ hj), hF hj⟩
  have hprod : (∏ j ∈ D.erase i, (node i - node j)) =
      (∏ j ∈ F, (node i - node j)) * ∏ j ∈ (D \ F).erase i, (node i - node j) := by
    rw [mul_comm, ← erase_sdiff_comm]
    exact (Finset.prod_sdiff hs).symm
  have hnz : (∏ j ∈ F, (node i - node j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj hz =>
      hiF ((IRSProfile.domain.injective (sub_eq_zero.mp hz)).symm ▸ hj))
  simp only [gridWeight, eval_locator_at_node, hprod, _root_.mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hnz, mul_one]

private theorem syndrome_as_sum (D : Finset I) (w : I → K) (n : ℕ) :
    syndrome (fun i : D => node i.val) (fun i => w i.val) n =
      ∑ i ∈ D, gridWeight D i * w i * node i ^ n := by
  unfold syndrome
  simp_rw [weight_on_grid]
  exact Finset.sum_coe_sort D (fun i => gridWeight D i * w i * node i ^ n)

private def rowSeed (b : Fin 2) : Bivar :=
  if b = 0 then Polynomial.C (Polynomial.X (R := K)) else Polynomial.X

private def rowStream (u : Words) (b v : Fin 2) (i : I) : K :=
  if b = 0 then u v i else u v i ^ p

private def rowWord (u : Words) (b : Fin 2) (i : I) : Bivar :=
  planeConstant (rowStream u b 0 i) + rowSeed b * planeConstant (rowStream u b 1 i)

private theorem plane_entry_syndromes (u : Words) (D : Finset I) (a t : ℕ)
    (i : Fin 2 × Fin a) (j : Fin (t + 1)) :
    planeMatrix u D a t i j =
      planeConstant (syndrome (fun z : D => node z.val)
        (fun z => rowStream u i.1 0 z.val) (i.2.val + j.val)) +
      rowSeed i.1 * planeConstant (syndrome (fun z : D => node z.val)
        (fun z => rowStream u i.1 1 z.val) (i.2.val + j.val)) := by
  by_cases h : i.1 = 0
  · simp only [planeMatrix, rowStream, rowSeed, h, ite_true, planeConstant,
      RingHom.comp_apply, map_add, map_mul]
  · simp only [planeMatrix, rowStream, rowSeed, h, ite_false, planeConstant,
      RingHom.comp_apply, syndrome_frobenius p (fun z : D => node z.val)
        (fun z => Native.native_domain_fixed z.val)]

private theorem plane_entry_sum (u : Words) (D : Finset I) (a t : ℕ)
    (i : Fin 2 × Fin a) (j : Fin (t + 1)) :
    planeMatrix u D a t i j =
      ∑ z ∈ D, planeConstant (gridWeight D z) * rowWord u i.1 z *
        planeConstant (node z) ^ (i.2.val + j.val) := by
  rw [plane_entry_syndromes, syndrome_as_sum, syndrome_as_sum]
  simp only [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib, map_mul, map_pow]
  apply Finset.sum_congr rfl
  intro z _
  unfold rowWord
  ring

/-- A row acting on polynomial coefficients is a weighted sum of node evaluations. -/
private theorem plane_row_eval (u : Words) (D : Finset I) (a t : ℕ)
    (L : Bivar[X]) (hL : L.natDegree ≤ t) (i : Fin 2 × Fin a) :
    ((planeMatrix u D a t).mulVec (fun j => L.coeff j.val)) i =
      ∑ z ∈ D, planeConstant (gridWeight D z) * rowWord u i.1 z *
        planeConstant (node z) ^ i.2.val * L.eval (planeConstant (node z)) := by
  simp only [Matrix.mulVec, dotProduct, plane_entry_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have he : (∑ j : Fin (t + 1), L.coeff j.val * planeConstant (node z) ^ j.val) =
      L.eval (planeConstant (node z)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => L.coeff j * planeConstant (node z) ^ j)]
    exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hL) _).symm
  rw [← he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

private theorem fixedFactor_eval (F : Finset I) (i : I) :
    (fixedFactor F).eval (planeConstant (node i)) =
      planeConstant ((locator node F).eval (node i)) := by
  rw [fixedFactor, Polynomial.eval_map_apply]

theorem proof : K1_2_4_1.c2 := by
  intro u D F a d hF Q hQ hker
  have hL : (fixedFactor F * Q).natDegree ≤ F.card + d := by
    exact natDegree_mul_le.trans
      (by rw [fixedFactor_natDegree]; exact Nat.add_le_add_left hQ F.card)
  funext i
  have hrow := congrFun hker i
  rw [plane_row_eval u D a _ _ hL, Pi.zero_apply] at hrow
  rw [plane_row_eval u (D \ F) a _ _ hQ, Pi.zero_apply, ← hrow]
  calc
    _ = ∑ z ∈ D \ F, planeConstant (gridWeight D z) * rowWord u i.1 z *
        planeConstant (node z) ^ i.2.val *
          (fixedFactor F * Q).eval (planeConstant (node z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [gridWeight_puncture hF hz, map_mul, Polynomial.eval_mul, fixedFactor_eval]
      ring
    _ = _ := by
      apply Finset.sum_subset Finset.sdiff_subset
      intro z hz hn
      have hzF : z ∈ F := by
        by_contra h
        exact hn (mem_sdiff.mpr ⟨hz, h⟩)
      rw [Polynomial.eval_mul, fixedFactor_eval, locator_eval_zero node F z hzF,
        map_zero, zero_mul, mul_zero]

end

end K1_2_4_1_2
end PackSource_K1_2_4_1_2Proof

section PackSource_K1_2_4_2Cofactors
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K1_2_4_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K1 K1_2 K1_2_4

/-- Complete the independent rows in the preferred block to a pivot. -/
theorem select_rows {a d : ℕ} (M : Matrix (Fin 2 × Fin a) (Fin d) K)
    (hM : M.rank = d) (b : Fin 2)
    (hprefix : LinearIndependent K (fun j : Fin (min a d) =>
      M.row (b, j.castLE (min_le_left _ _)))) :
    ∃ rows : Fin d → Fin 2 × Fin a, (M.submatrix rows id).det ≠ 0 ∧
      (Finset.univ.filter (fun j => (rows j).1 = b)).card = min a d := by
  classical
  let f : Fin (min a d) ↪ Fin 2 × Fin a :=
    ⟨fun j => (b, j.castLE (min_le_left _ _)), fun i j h =>
      Fin.ext (congrArg (fun k : Fin 2 × Fin a => k.2.val) h)⟩
  let S := Set.range f
  have hS : LinearIndepOn K M.row S := (linearIndepOn_range_iff f.injective M.row).mpr hprefix
  let T := hS.extend (Set.subset_univ S)
  have hST := hS.subset_extend (Set.subset_univ S)
  have hli : LinearIndependent K (fun i : T => M.row i.val) :=
    (hS.linearIndepOn_extend (Set.subset_univ S)).linearIndependent_restrict
  have hspace : Submodule.span K (Set.range (fun i : T => M.row i.val)) =
      Submodule.span K (Set.range M.row) := by
    have heq : Set.range (fun i : T => M.row i.val) = M.row '' T := by
      ext v
      exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.property, hi⟩,
        fun ⟨i, hi, hv⟩ => ⟨⟨i, hi⟩, hv⟩⟩
    rw [heq, hS.span_image_extend_eq_span_image (Set.subset_univ S), Set.image_univ]
  have hcard : Fintype.card T = d := by
    rw [← finrank_span_eq_card hli, hspace, ← Matrix.rank_eq_finrank_span_row, hM]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let rows : Fin d → Fin 2 × Fin a := Subtype.val ∘ e
  have hinj : Function.Injective rows := Subtype.val_injective.comp e.injective
  have hpiv : LinearIndependent K (M.submatrix rows id).row := hli.comp e e.injective
  refine ⟨rows, ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hpiv)).ne_zero, ?_⟩
  let B := Finset.univ.filter (fun j => (rows j).1 = b)
  let intoB (j : Fin (min a d)) : B :=
    ⟨e.symm ⟨f j, hST (Set.mem_range_self j)⟩, by simp [B, rows, f]⟩
  have hlo := Fintype.card_le_of_injective intoB (by
    intro i j hij
    apply f.injective
    have he := e.symm.injective (congrArg Subtype.val hij)
    exact congrArg Subtype.val he)
  have hhi := Fintype.card_le_of_injective (fun i : B => (rows i.val).2) (by
    intro i j hij
    apply Subtype.ext
    apply hinj
    exact Prod.ext ((Finset.mem_filter.mp i.property).2.trans
      (Finset.mem_filter.mp j.property).2.symm) hij)
  simp only [Fintype.card_fin, Fintype.card_coe] at hlo hhi
  have hB := Finset.card_le_card (Finset.filter_subset (fun j => (rows j).1 = b) Finset.univ)
  rw [Finset.card_univ, Fintype.card_fin] at hB
  exact le_antisymm (le_min hhi hB) hlo

private theorem affine_degree {F : Type*} [CommRing F] [Nontrivial F] (v w : F) :
    (Polynomial.C v + Polynomial.X * Polynomial.C w).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_C_add]
  exact Polynomial.natDegree_mul_le.trans (by simp)

private theorem matrix_box (u : Words) (D : Finset I) (a R : ℕ) (r : Fin 2 × Fin a)
    (j : Fin (R + 1)) :
    SeedBox (planeMatrix u D a R r j) (if r.1 = 0 then 1 else 0)
      (if r.1 = 0 then 0 else 1) := by
  unfold planeMatrix SeedBox seedDegree
  dsimp only
  split_ifs
  · constructor
    · rw [Polynomial.Bivariate.swap_C, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
      exact affine_degree _ _
    · exact (Polynomial.natDegree_C _).le
  · constructor
    · rw [map_add, map_mul, Polynomial.Bivariate.swap_C_C, Polynomial.Bivariate.swap_C_C,
        Polynomial.Bivariate.swap_Y, ← Polynomial.C_mul, ← Polynomial.C_add]
      exact (Polynomial.natDegree_C _).le
    · exact affine_degree _ _

/-- The appended node-evaluation row turns a pivot into a polynomial cut. -/
def cutMatrix {a d : ℕ} (N : Matrix (Fin 2 × Fin a) (Fin (d + 1)) Bivar)
    (rows : Fin d → Fin 2 × Fin a) (i : I) : Matrix (Fin (d + 1)) (Fin (d + 1)) Bivar :=
  fun j k => Fin.lastCases (planeConstant (node i ^ k.val)) (fun r => N (rows r) k) j

private theorem det_natDegree_le_row {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι A[X]) (v : ι → ℕ) (hP : ∀ j k, (P j k).natDegree ≤ v j) :
    P.det.natDegree ≤ ∑ j, v j := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def]
  exact (Polynomial.natDegree_smul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans
    (Finset.sum_le_sum fun k _ => hP k (σ k)))

theorem cut_box (u : Words) (D F : Finset I) (a R d : ℕ)
    (rows : Fin d → Fin 2 × Fin a) (i : I) :
    SeedBox (cutMatrix (contracted u D F a R d) rows i).det
      (Finset.univ.filter (fun j => (rows j).1 = 0)).card
      (Finset.univ.filter (fun j => (rows j).1 ≠ 0)).card := by
  let M := cutMatrix (contracted u D F a R d) rows i
  let s : Fin (d + 1) → ℕ := Fin.lastCases 0 (fun j => if (rows j).1 = 0 then 1 else 0)
  let t : Fin (d + 1) → ℕ := Fin.lastCases 0 (fun j => if (rows j).1 ≠ 0 then 1 else 0)
  have hbox (j k : Fin (d + 1)) : SeedBox (M j k) (s j) (t j) := by
    refine Fin.lastCases ?_ (fun r => ?_) j
    · simp [M, cutMatrix, s, t, SeedBox, seedDegree, planeConstant,
        Polynomial.Bivariate.swap_C_C]
    · simp only [M, cutMatrix, s, t, Fin.lastCases_castSucc, contracted, Matrix.mul_apply]
      apply box_sum
      intro l _
      have h := box_mul_constant _ (convolution (locator node F) R d l k) _ _
        (matrix_box u D a R (rows r) l)
      simpa only [planeConstant, Matrix.map_apply, RingHom.comp_apply, ite_not] using h
  have hs : (∑ j, s j) = (Finset.univ.filter (fun j => (rows j).1 = 0)).card := by
    simp only [s, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, add_zero,
      Finset.sum_boole, Nat.cast_id]
  have ht : (∑ j, t j) = (Finset.univ.filter (fun j => (rows j).1 ≠ 0)).card := by
    simp only [t, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, add_zero,
      Finset.sum_boole, Nat.cast_id]
  constructor
  · change seedDegree M.det ≤ _
    rw [seedDegree, AlgEquiv.map_det, ← hs]
    exact det_natDegree_le_row (A := K[X]) (M.map (Polynomial.Bivariate.swap (R := K))) s
      (fun j k => (hbox j k).1)
  · change M.det.natDegree ≤ _
    rw [← ht]
    exact det_natDegree_le_row (A := K[X]) M t (fun j k => (hbox j k).2)

theorem cut_action {E : Type} [Field E] (φ : Bivar →+* E)
    {a d : ℕ} {N : Matrix (Fin 2 × Fin a) (Fin (d + 1)) Bivar}
    (rows : Fin d → Fin 2 × Fin a) (i : I) {T : E[X]}
    (hTd : T.natDegree ≤ d) (hker : (N.map φ).mulVec (fun j => T.coeff j.val) = 0) :
    ((cutMatrix N rows i).map φ).mulVec (fun j => T.coeff j.val) =
      Fin.lastCases (T.eval (φ (planeConstant (node i)))) (fun _ => 0) := by
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · rw [Fin.lastCases_last, ← sum_coeff_eval T d hTd (φ (planeConstant (node i)))]
    change (∑ k : Fin (d + 1), φ (cutMatrix N rows i (Fin.last d) k) *
      T.coeff k.val) = _
    apply Finset.sum_congr rfl
    intro k _
    simp only [cutMatrix, Fin.lastCases_last, map_pow]
    exact mul_comm _ _
  · simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, cutMatrix,
      Fin.lastCases_castSucc, Pi.zero_apply] using congrFun hker (rows l)

/-- A pivot over the curve field and a nonzero node evaluation imply
that the augmented determinant is nonzero there. -/
theorem cut_ne_zero {E : Type} [Field E] (φ : Bivar →+* E)
    {a d : ℕ} {N : Matrix (Fin 2 × Fin a) (Fin (d + 1)) Bivar}
    (rows : Fin d → Fin 2 × Fin a) (i : I)
    (hpivot : ((N.map φ).submatrix rows Fin.castSucc).det ≠ 0)
    {T : E[X]} (hTd : T.natDegree ≤ d)
    (hker : (N.map φ).mulVec (fun j => T.coeff j.val) = 0)
    (hnode : T.eval (φ (planeConstant (node i))) ≠ 0) :
    φ (cutMatrix N rows i).det ≠ 0 := by
  classical
  let A := (cutMatrix N rows i).map φ
  let v : Fin (d + 1) → E := fun j => T.coeff j.val
  let B := A.updateCol (Fin.last d) (A.mulVec v)
  have hdet : B.det = v (Fin.last d) * A.det := by
    have hcol : (fun k => ∑ j, v j • A k j) = A.mulVec v := by
      funext k
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    change (A.updateCol (Fin.last d) (A.mulVec v)).det = _
    rw [← hcol]
    exact Matrix.det_updateCol_sum A (Fin.last d) v
  have hAv : A.mulVec v = Fin.lastCases (T.eval (φ (planeConstant (node i)))) (fun _ => 0) :=
    cut_action φ rows i hTd hker
  have hminor : B.submatrix (Fin.last d).succAbove (Fin.last d).succAbove =
      (N.map φ).submatrix rows Fin.castSucc := by
    ext j k
    simp [B, A, cutMatrix]
  have htop (j : Fin d) : B j.castSucc (Fin.last d) = 0 := by
    simp only [B, Matrix.updateCol_self, hAv, Fin.lastCases_castSucc]
  have hbottom : B (Fin.last d) (Fin.last d) = T.eval (φ (planeConstant (node i))) := by
    simp only [B, Matrix.updateCol_self, hAv, Fin.lastCases_last]
  have hB : B.det ≠ 0 := by
    rw [Matrix.det_succ_column B (Fin.last d), Fin.sum_univ_castSucc]
    simp only [htop, hbottom, hminor, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hnode)
      hpivot
  rw [φ.map_det]
  change A.det ≠ 0
  exact fun hz => hB (by rw [hdet, hz, mul_zero])

end

end K1_2_4_2
end PackSource_K1_2_4_2Cofactors

section PackSource_K1_2_4_2Anchor
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace K1_2_4_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2 K1_2_4

private theorem evaluate_convolution {A ι : Type} [Field A] (x : ι → A)
    (Δ : A[X]) (R d : ℕ) (i : ι) (j : Fin (d + 1))
    (hdeg : (Δ * Polynomial.X ^ j.val).natDegree ≤ R) :
    (Strata.nodeVandermonde x R * convolution Δ R d) i j =
      Δ.eval (x i) * x i ^ j.val := by
  let T := Δ * (Polynomial.X (R := A)) ^ j.val
  calc
    _ = ∑ k : Fin (R + 1), T.coeff k.val * x i ^ k.val := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = T.eval (x i) := sum_coeff_eval T R hdeg (x i)
    _ = _ := by simp only [T, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- The shorter leading columns factor through the surviving actual
errors, with weights multiplied by the fixed-node divisor. -/
theorem anchor_ranks {u : Words} {D F : Finset I} {a R d : ℕ}
    {γ : K} {P : K[X]} (hsize : R = d + F.card)
    (hD : D.card = 131072 + a + R) (hP : P.degree < 131072)
    (hE : (errorSet u D γ P).card = R) (hF : F ⊆ errorSet u D γ P)
    (hrank : ((planeMatrix u D a R).map (onGraph γ)).rank = R) :
    let M := ((contracted u D F a R d).map (onGraph γ)).submatrix id Fin.castSucc
    M.rank = d ∧ ∀ b : Fin 2,
      LinearIndependent K (fun j : Fin (min a d) => M.row (b, j.castLE (min_le_left _ _))) := by
  classical
  dsimp only
  let x : D → K := fun i => node i.val
  let w : D → K := fun i => u 0 i.val + γ * u 1 i.val
  let σ := Strata.twoConjugations (frobenius K p)
  let E := (errorSet u D γ P).subtype (· ∈ D)
  let S := (Finset.univ : Finset E).filter (fun i => i.val.val ∉ F)
  let Δ := locator node F
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have herr (i : D) : i ∈ E ↔ P.eval (x i) ≠ w i := by
    simp [E, errorSet, goodSet, x, w, Finset.mem_subtype, i.property]
  have hnos (i : D) (hi : i ∉ E) : w i = P.eval (x i) :=
    ((not_ne_iff.mp fun hn => hi ((herr i).mpr hn)) : P.eval (x i) = w i).symm
  have hEc : E.card = R := by
    have heq : E.map (Function.Embedding.subtype (· ∈ D)) = errorSet u D γ P :=
      Finset.subtype_map_of_mem (fun i hi => (Finset.mem_sdiff.mp hi).1)
    rw [← Finset.card_map (f := Function.Embedding.subtype (· ∈ D)), heq, hE]
  let eS : S ≃ (errorSet u D γ P \ F : Finset I) := {
    toFun := fun i => ⟨i.val.val.val, Finset.mem_sdiff.mpr
      ⟨(Finset.mem_subtype.mp i.val.property), (Finset.mem_filter.mp i.property).2⟩⟩
    invFun := fun i =>
      let h := Finset.mem_sdiff.mp i.property
      ⟨⟨⟨i.val, (Finset.mem_sdiff.mp h.1).1⟩, Finset.mem_subtype.mpr h.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hSc : Fintype.card S = d := by
    rw [Fintype.card_congr eS, Fintype.card_coe, Finset.card_sdiff_of_subset hF, hE]
    omega
  let e := (Fintype.equivFinOfCardEq hSc).symm
  let ι : Fin d ↪ E := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
  let y : Fin d → K := x ∘ Subtype.val ∘ ι
  have hy : Function.Injective y := hx.comp (Subtype.val_injective.comp ι.injective)
  have hfix (b : Fin 2) (i : D) : σ b (x i) = x i := by
    fin_cases b
    · rfl
    · exact Native.native_domain_fixed i.val
  let W (b : Fin 2) (i : E) := weight x i.val * σ b (w i.val - P.eval (x i.val))
  let H : Matrix (Fin 2 × Fin a) E K := fun j i => W j.1 i * x i.val ^ j.2.val
  let V := Strata.nodeVandermonde (fun i : E => x i.val) R
  have hfactor : (planeMatrix u D a R).map (onGraph γ) = H * V := by
    rw [K1_2_3.plane_at_slope]
    exact Strata.conjugateHankel_factorization σ x w hx hfix P 131072 a R hP
      (by rw [Fintype.card_coe, hD]) E hnos
  have hH : H.rank = Fintype.card E := by
    have hh := Matrix.rank_mul_le_left H V
    rw [← hfactor, hrank] at hh
    rw [Fintype.card_coe, hEc]
    exact le_antisymm (by simpa only [Fintype.card_coe, hEc] using H.rank_le_card_width) hh
  let C : Matrix (Fin 2 × Fin a) (Fin d) K :=
    fun j i => H j (ι i) * Δ.eval (y i)
  have hΔ (i : Fin d) : Δ.eval (y i) ≠ 0 := fun hz =>
    (Finset.mem_filter.mp (e i).property).2
      ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective F _).mp hz)
  have hC : C.rank = d := by
    have hi : LinearIndependent K H.col := by
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols, hH]
    have hc := (hi.comp ι ι.injective).units_smul (fun i => Units.mk0 (Δ.eval (y i)) (hΔ i))
    have hcol : LinearIndependent K C.col := by
      have heq : C.col = (fun i : Fin d =>
          Units.mk0 (Δ.eval (y i)) (hΔ i) • (H.col ∘ ι) i) := by
        funext i j
        simp only [Matrix.col, C, Function.comp_def, Units.smul_def, Units.val_mk0,
          Pi.smul_apply, smul_eq_mul]
        exact mul_comm _ _
      rw [heq]
      exact hc
    simpa only [← Matrix.rank_eq_finrank_span_cols, Fintype.card_fin, Set.finrank]
      using (linearIndependent_iff_card_eq_finrank_span.mp hcol).symm
  have hconst : (onGraph γ).comp planeConstant = RingHom.id K :=
    RingHom.ext (graph_constant γ)
  have hconv : ((convolution Δ R d).map planeConstant).map (onGraph γ) = convolution Δ R d := by
    change (convolution Δ R d).map ((onGraph γ).comp planeConstant) = _
    rw [hconst]
    rfl
  have hV (i : E) (j : Fin (d + 1)) :
      (V * convolution Δ R d) i j = Δ.eval (x i.val) * x i.val ^ j.val := by
    have hdeg : (Δ * Polynomial.X ^ j.val).natDegree ≤ R := by
      have hh := Polynomial.natDegree_mul_le (p := Δ) (q := (Polynomial.X (R := K)) ^ j.val)
      rw [Polynomial.natDegree_X_pow, show Δ.natDegree = F.card from locator_natDegree _ _] at hh
      have := j.isLt
      omega
    exact evaluate_convolution (fun i : E => x i.val) Δ R d i j hdeg
  have hshort :
      ((contracted u D F a R d).map (onGraph γ)).submatrix id Fin.castSucc =
        C * Matrix.vandermonde y := by
    rw [contracted, Matrix.map_mul, hfactor, hconv, Matrix.mul_assoc]
    apply Matrix.ext
    intro j k
    change (∑ l : E, H j l * (V * convolution Δ R d) l k.castSucc) =
      ∑ l : Fin d, C j l * (Matrix.vandermonde y) l k
    simp only [hV, Fin.val_castSucc, Matrix.vandermonde_apply, C]
    let g (i : E) := H j i * (Δ.eval (x i.val) * x i.val ^ k.val)
    calc
      (∑ i : E, g i) = ∑ i ∈ S, g i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        have hiF : i.val.val ∈ F := by simpa [S] using hi
        simp [g, x, Δ, locator_eval_zero node F i.val.val hiF]
      _ = ∑ i : S, g i.val := (Finset.sum_coe_sort S g).symm
      _ = ∑ i : Fin d, g (e i).val := (Equiv.sum_comp e (fun i : S => g i.val)).symm
      _ = _ := Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)
  have hdet := Matrix.det_vandermonde_ne_zero_iff.mpr hy
  rw [hshort]
  refine ⟨(Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdet).trans hC, ?_⟩
  intro b
  let m := min a d
  let r : Fin m → Fin 2 × Fin a := fun j => (b, j.castLE (min_le_left _ _))
  let c : Fin m ↪ Fin d := Fin.castLEEmb (min_le_right _ _)
  have hW (i : Fin d) : W b (ι i) ≠ 0 := by
    apply mul_ne_zero (Strata.weight_ne_zero x hx _)
    intro hz
    have he := (σ b).injective (hz.trans (map_zero _).symm)
    exact ((herr (ι i).val).mp (ι i).property) (sub_eq_zero.mp he).symm
  have hsquare : C.submatrix r c =
      (Matrix.vandermonde (y ∘ c)).transpose *
        Matrix.diagonal (fun i => W b (ι (c i)) * Δ.eval (y (c i))) := by
    apply Matrix.ext
    intro j k
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.transpose_apply,
      Matrix.vandermonde_apply, Function.comp_apply, C, H, r, Fin.val_castLE, y]
    ring
  have hsq : (C.submatrix r c).det ≠ 0 := by
    rw [hsquare, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (hy.comp c.injective))
      (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (hW (c i)) (hΔ (c i)))
  have hprefix : (C.submatrix r id).rank = m := by
    have hlo := Matrix.rank_submatrix_le (C.submatrix r id) id c
    change (C.submatrix r c).rank ≤ _ at hlo
    rw [Matrix.rank_of_det_ne_zero hsq, Fintype.card_fin] at hlo
    exact le_antisymm (by simpa using (C.submatrix r id).rank_le_card_height) hlo
  have hsub : (C * Matrix.vandermonde y).submatrix r id =
      C.submatrix r id * Matrix.vandermonde y := by
    apply Matrix.ext
    intro i j
    rfl
  change LinearIndependent K ((C * Matrix.vandermonde y).submatrix r id).row
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, hsub,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdet, hprefix, Fintype.card_fin]

end

end K1_2_4_2
end PackSource_K1_2_4_2Anchor

section PackSource_K1_2_4_1_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace K1_2_4_1_1

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open K1 K1_2 K1_2_4 K1_2_4_1

private theorem map_kernel {R S row col : Type*} [CommRing R] [CommRing S] [Fintype col]
    (φ : R →+* S) (M : Matrix row col R) (v : col → R) (hv : M.mulVec v = 0) :
    (M.map φ).mulVec (fun j => φ (v j)) = 0 := by
  funext i
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul, map_sum, map_zero,
    Pi.zero_apply] using congrArg φ (congrFun hv i)

/-- A primitive generator divides every integral vector on its rational line.
The gcd argument applies over the plane even when its coordinates have a
common zero in codimension two. -/
private theorem polynomial_multiple {R col : Type*} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] [Fintype col] (Q V : col → R) (k : col) (hQ : Q k ≠ 0)
    (hprim : Finset.univ.gcd Q = 1) (hcross : ∀ j, V j * Q k = V k * Q j) :
    ∃ g, ∀ j, V j = g * Q j := by
  classical
  have hd : Q k ∣ Finset.univ.gcd (fun j => V k * Q j) := Finset.dvd_gcd fun j _ => by
    rw [← hcross j]
    exact dvd_mul_left _ _
  have h := hd.trans (Finset.gcd_mul_left' Finset.univ Q (V k)).dvd
  rw [hprim, mul_one] at h
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun j => mul_right_cancel₀ hQ ?_⟩
  rw [hcross j, hg]
  ring

theorem proof : K1_2_4_1.c1 := by
  classical
  let : NormalizedGCDMonoid Bivar := UniqueFactorizationMonoid.toNormalizedGCDMonoid Bivar
  intro u D Γ P a d _ _ hΓ hreg
  let M := planeMatrix u D a d
  let V (rows : Fin d → Fin 2 × Fin a) := cofactor (M.submatrix rows id)
  let k := Fin.last d
  let φ := algebraMap Bivar (FractionRing Bivar)
  have hφ : Function.Injective φ := IsFractionRing.injective Bivar _
  have hfne {x : Bivar} (h : x ≠ 0) : φ x ≠ 0 :=
    fun hz => h (hφ (hz.trans (map_zero φ).symm))
  have hdata (γ : K) (hγ : γ ∈ Γ) :=
    fiber_data hreg.domain_card (hreg.mark γ hγ).1 (hreg.mark γ hγ).2.1
      (hreg.mark γ hγ).2.2.2
  have hrows (γ : K) (hγ : γ ∈ Γ) (b : Fin 2) :
      ∃ rows : Fin d → Fin 2 × Fin a, onGraph γ (V rows k) ≠ 0 ∧
        (Finset.univ.filter (fun i => (rows i).1 = b)).card = min a d := by
    obtain ⟨rows, hp, hb⟩ := select_rows _ (hdata γ hγ).1 b ((hdata γ hγ).2.1 b)
    refine ⟨rows, ?_, hb⟩
    change onGraph γ (cofactor (M.submatrix rows id) (Fin.last d)) ≠ 0
    rw [cofactor_map, cofactor_last]
    exact hp
  have hnonzero (rows : Fin d → Fin 2 × Fin a) (γ : K) (h : onGraph γ (V rows k) ≠ 0) :
      V rows k ≠ 0 := fun hz => h ((congrArg (onGraph γ) hz).trans (map_zero _))
  have hVker (rows : Fin d → Fin 2 × Fin a) (h : V rows k ≠ 0) : M.mulVec (V rows) = 0 :=
    cofactor_kernel φ hφ M rows hreg.generic_rank (hfne h)
  obtain ⟨γ₀, hγ₀⟩ := hΓ
  obtain ⟨r₀, hp₀, hc₀⟩ := hrows γ₀ hγ₀ 0
  obtain ⟨r₁, hp₁, hc₁⟩ := hrows γ₀ hγ₀ 1
  let g := Finset.univ.gcd (V r₀)
  have hg : g ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨k, Finset.mem_univ _, hnonzero r₀ γ₀ hp₀⟩
  obtain ⟨Q, hQ, hprim⟩ := Finset.extract_gcd (V r₀) (Finset.univ_nonempty (α := Fin (d+1)))
  have hQ' (j : Fin (d+1)) : V r₀ j = g * Q j := hQ j (Finset.mem_univ _)
  have hQk : Q k ≠ 0 := by
    intro hz
    exact hnonzero r₀ γ₀ hp₀ (by rw [hQ', hz, mul_zero])
  have hQker : M.mulVec Q = 0 := by
    have hv := hVker r₀ (hnonzero r₀ γ₀ hp₀)
    funext i
    change (∑ j, M i j * Q j) = 0
    have hi : (∑ j, M i j * V r₀ j) = 0 := congrFun hv i
    have he : (∑ j, M i j * V r₀ j) = g * ∑ j, M i j * Q j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hQ']
      ac_rfl
    exact (mul_eq_zero.mp (he.symm.trans hi)).resolve_left hg
  have hmult (rows : Fin d → Fin 2 × Fin a) (hn : V rows k ≠ 0) :
      ∃ t : Bivar, ∀ j, V rows j = t * Q j := by
    apply polynomial_multiple Q (V rows) k hQk hprim
    have hnull := GenericRank.nullity_one_of_rank (M.map φ) (by
      rw [show (M.map φ).rank = d from hreg.generic_rank, Fintype.card_fin])
    have hnz : (fun j => φ (Q j)) ≠ 0 := by
      intro hz
      exact hfne hQk (congrFun hz k)
    obtain ⟨c, hc⟩ := GenericRank.kernel_line_of_finrank _ hnull _ hnz
      (map_kernel φ M Q hQker) _ (map_kernel φ M _ (hVker rows hn))
    intro j
    apply hφ
    simp only [map_mul]
    rw [congrFun hc j, congrFun hc k]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨t, ht⟩ := hmult r₁ (hnonzero r₁ γ₀ hp₁)
  have ht0 : t ≠ 0 := by
    intro hz
    exact hnonzero r₁ γ₀ hp₁ (by rw [ht, hz, zero_mul])
  have hcount (rows : Fin d → Fin 2 × Fin a) :
      (Finset.univ.filter (fun j => (rows j).1 = 0)).card +
        (Finset.univ.filter (fun j => (rows j).1 ≠ 0)).card = d := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun j => (rows j).1 = 0)
  have hb₀ : (Finset.univ.filter (fun j => (r₀ j).1 ≠ 0)).card = d-a := by
    have h := hcount r₀
    omega
  have hb₁ : (Finset.univ.filter (fun j => (r₁ j).1 = 0)).card = d-a := by
    have he (j : Fin d) : (r₁ j).1 ≠ 0 ↔ (r₁ j).1 = 1 := by omega
    have h := hcount r₁
    simp only [he, hc₁] at h
    omega
  have hbox (j : Fin (d+1)) : SeedBox (Q j) (d-a) (d-a) := by
    by_cases hz : Q j = 0
    · simp [hz, SeedBox, seedDegree]
    have h₀ := box_of_dvd (by rw [hQ']; exact mul_ne_zero hg hz)
      (show Q j ∣ V r₀ j by rw [hQ']; exact dvd_mul_left _ _)
      (cofactor_box u D a d r₀ j)
    have h₁ := box_of_dvd (by rw [ht]; exact mul_ne_zero ht0 hz)
      (show Q j ∣ V r₁ j by rw [ht]; exact dvd_mul_left _ _)
      (cofactor_box u D a d r₁ j)
    exact ⟨hb₁ ▸ h₁.1, hb₀ ▸ h₀.2⟩
  let L := Principal.assemble Q
  have hLd : L.natDegree ≤ d := Principal.assemble_natDegree_le Q
  refine ⟨L, ⟨hLd, ?_, ?_⟩, ?_⟩
  · simpa only [L, Principal.assemble_coeff] using hQker
  · intro γ hγ
    obtain ⟨rows, hp, _⟩ := hrows γ hγ 0
    obtain ⟨s, hs⟩ := hmult rows (hnonzero rows γ hp)
    have hpoint : onGraph γ (Q k) ≠ 0 := by
      intro hz
      exact hp (by rw [hs, map_mul, hz, mul_zero])
    let T := locator node (errorSet u D γ (P γ))
    let v (j : Fin (d+1)) := T.coeff j.val
    have hTd : T.natDegree = d := (locator_natDegree _ _).trans (hreg.mark γ hγ).2.1
    have hvk : v k = 1 := by
      change T.coeff d = 1
      rw [← hTd]
      exact locator_monic _ _
    have hv0 : v ≠ 0 := fun hz => one_ne_zero (hvk.symm.trans (congrFun hz k))
    have hnull := GenericRank.nullity_one_of_rank (M.map (onGraph γ)) (by
      rw [show (M.map (onGraph γ)).rank = d from (hreg.mark γ hγ).2.2.2, Fintype.card_fin])
    obtain ⟨c, hc⟩ := GenericRank.kernel_line_of_finrank _ hnull v hv0
      (hdata γ hγ).2.2 _ (map_kernel (onGraph γ) M Q hQker)
    refine ⟨c, fun hz => hpoint (by simpa [hz] using congrFun hc k), ?_⟩
    apply Polynomial.ext
    intro j
    rw [coeff_map, coeff_smul]
    by_cases hj : j < d+1
    · exact (congrArg (onGraph γ) (Principal.assemble_coeff Q ⟨j, hj⟩)).trans
        (congrFun hc ⟨j, hj⟩)
    · rw [coeff_eq_zero_of_natDegree_lt (hLd.trans_lt (by omega)), map_zero,
        coeff_eq_zero_of_natDegree_lt (hTd.trans_lt (by omega)), smul_zero]
  · intro j
    by_cases hj : j < d+1
    · exact (Principal.assemble_coeff Q ⟨j, hj⟩).symm ▸ hbox ⟨j, hj⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hLd.trans_lt (by omega))]
      simp [SeedBox, seedDegree]

end

end K1_2_4_1_1
end PackSource_K1_2_4_1_1Proof

section PackSource_K1_2_2_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace K1_2_2_1

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark K1

private theorem stacked_at_slope {ι : Type} [Fintype ι] [DecidableEq ι]
    (x a b : ι → K) (L t : ℕ) (γ : K) :
    (stacked p x a b L t).map (evalRingHom γ) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        x (fun i => a i + γ * b i) L t := by
  rw [Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]

private theorem node_fixed (b : Fin 2) (i : I) :
    Strata.twoConjugations (frobenius K p) b (node i) = node i := by
  fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]

private theorem rank_le_retained_rank_add_deleted {row ι : Type}
    [Fintype row] [Fintype ι] [DecidableEq ι]
    (M : Matrix row ι K) (C : Finset ι) :
    M.rank ≤ (M.submatrix id (Subtype.val : {i // i ∉ C} → ι)).rank + C.card := by
  have h := Strata.subspace_projection_bound (Strata.forgetCoordinates (F := K) C)
    (Submodule.span K (Set.range M.row))
  rw [Strata.rowspace_forget, Strata.forgetCoordinates_nullity,
    ← Matrix.rank_eq_finrank_span_row, ← Matrix.rank_eq_finrank_span_row] at h
  exact h

/-- Switch between the surviving-domain error set and the surviving subset
of the original error set before applying the coordinate projection bound. -/
private theorem rank_le_punctured_rank_add_deleted {row ι : Type}
    [Fintype row] [DecidableEq ι] (D E S : Finset ι)
    (hD : ∀ i, i ∈ D ↔ i ∉ S) (hS : S ⊆ E) (M : Matrix row E K) :
    M.rank ≤ (M.submatrix id (fun i : ↥(E.subtype (fun j => j ∈ D)) =>
      (⟨i.val.val, Finset.mem_subtype.mp i.property⟩ : E))).rank + S.card := by
  let C : Finset E := S.subtype (fun i : ι => i ∈ E)
  have hC (i : E) : i ∈ C ↔ i.val ∈ S := Finset.mem_subtype
  have hCcard : C.card = S.card := by
    change (S.subtype (fun i : ι => i ∈ E)).card = S.card
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun i hi => hS hi)]
  let e : ↥(E.subtype (fun j => j ∈ D)) ≃ {i : E // i ∉ C} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      let j : E := ⟨i.val.val, Finset.mem_subtype.mp i.property⟩
      exact ⟨j, fun hj => (hD i.val.val).1 i.val.property ((hC j).1 hj)⟩
    · intro j
      have hj : j.val.val ∉ S := fun hs => j.property ((hC j.val).2 hs)
      let i : D := ⟨j.val.val, (hD j.val.val).2 hj⟩
      exact ⟨i, Finset.mem_subtype.mpr j.val.property⟩
    · intro i
      rfl
    · intro j
      rfl
  let M₀ := M.submatrix id (Subtype.val : {i : E // i ∉ C} → E)
  change M.rank ≤ (M₀.submatrix (Equiv.refl row) e).rank + S.card
  rw [Matrix.rank_submatrix, ← hCcard]
  exact rank_le_retained_rank_add_deleted M C

theorem proof : K1_2_2.c1 := by
  classical
  intro u T R A γ M hn
  let S := fixedNodes R
  let D := Finset.univ \ S
  let w (i : I) := u 0 i + γ * u 1 i
  let G := Finset.univ.filter (fun i : I => w i = M.decoder.eval (node i))
  let E := Finset.univ \ G
  let E' : Finset D := E.subtype (fun i : I => i ∈ D)
  have hE (i : I) : i ∈ E ↔ w i ≠ M.decoder.eval (node i) := by
    simp [E, G]
  have hS : S ⊆ E := fun i hi => (hE i).2 (A.deleted_error γ hn M i hi).symm
  have hG : 180265 ≤ G.card := M.agreement.trans (Finset.card_le_card (by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (M.hits i hi).symm⟩))
  have hEcard : E.card ≤ 81879 := by
    have hg := K1_2_2.domain_card G
    change E.card = 262144 - G.card at hg
    omega
  have hDcard : Fintype.card D = 262144 - S.card := by
    rw [Fintype.card_coe]
    exact K1_2_2.domain_card S
  have hDsize : 131072 + 49193 + (81879 - S.card) ≤ Fintype.card D := by
    have hs := Finset.card_le_card hS
    omega
  have hE'card : E'.card ≤ 81879 - S.card := by
    have hfilter : E.filter (fun i : I => i ∈ D) = E \ S := by
      ext i
      simp [D]
    change (E.subtype (fun i : I => i ∈ D)).card ≤ _
    rw [Finset.card_subtype, hfilter, Finset.card_sdiff_of_subset hS]
    exact Nat.sub_le_sub_right hEcard _
  have hagree (i : I) (hi : i ∉ E) : w i = M.decoder.eval (node i) :=
    not_not.mp (fun hne => hi ((hE i).2 hne))
  have hagree' (i : D) (hi : i ∉ E') : w i.val = M.decoder.eval (node i.val) :=
    hagree i.val (fun he => hi (Finset.mem_subtype.mpr he))
  let σ := Strata.twoConjugations (frobenius K p)
  let x (i : D) := node i.val
  let B := Strata.conjugateErrors σ (fun i : E => node i.val)
    (fun i : E => w i.val - M.decoder.eval (node i.val)) 49193
  let B' := Strata.conjugateErrors σ (fun i : E' => x i.val)
    (fun i : E' => w i.val.val - M.decoder.eval (x i.val)) 49193
  -- Both Vandermonde factors have full row rank; the weights on each domain
  -- are removed by the existing rank factorization.
  have hfull : ((twoBlock u).map (evalRingHom γ)).rank = B.rank := by
    rw [twoBlock, stacked_at_slope]
    exact Strata.conjugateHankel_error_rank σ node w IRSProfile.domain.injective
      node_fixed M.decoder 131072 49193 81879 M.degree
      (by rw [IRSProfile.card_index]) E (by omega) hagree
  have hshort : ((K1_2_2.shortenedStack R).map (evalRingHom γ)).rank = B'.rank := by
    change ((stacked p x (fun i : D => u 0 i.val) (fun i : D => u 1 i.val)
      49193 (81879 - S.card)).map (evalRingHom γ)).rank = B'.rank
    rw [stacked_at_slope]
    exact Strata.conjugateHankel_error_rank σ x (fun i : D => w i.val)
      (IRSProfile.domain.injective.comp Subtype.val_injective)
      (fun b i => node_fixed b i.val) M.decoder 131072 49193 (81879 - S.card)
      M.degree hDsize E' (by omega) hagree'
  have hD (i : I) : i ∈ D ↔ i ∉ S := by simp [D]
  have hrank : B.rank ≤ B'.rank + S.card :=
    rank_le_punctured_rank_add_deleted D E S hD hS B
  have hnormal : ((twoBlock u).map (evalRingHom γ)).rank = 49193 + T.height := by
    change ((twoBlock u).map (evalRingHom γ)).rank = stackRank u at hn
    rw [hn, actual_stackRank]
    have := T.degreeSum
    have := T.nullitySum
    have := T.top
    unfold TwoActive.height
    omega
  have hspecial := K1_2_3.rank_ge_specialization (K1_2_2.shortenedStack R)
    (evalRingHom γ) (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
  change ((K1_2_2.shortenedStack R).map (evalRingHom γ)).rank ≤
    GenericLayer.genericRank (K1_2_2.shortenedStack R) at hspecial
  rw [hshort] at hspecial
  rw [← hfull, hnormal] at hrank
  have hheight := A.height_eq
  change A.height + S.card = T.height at hheight
  omega

end

end K1_2_2_1
end PackSource_K1_2_2_1Proof

section PackSource_K1_2_4_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K1_2_4_2

noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark
open K1 K1_2 K1_2_4

theorem proof : K1_2_4.c2 := by
  classical
  intro u D Γ P a b _ _ hreg L hL Q hQ _ _ hΓ hQΓ
  let F := curveFixed D L Q
  let R := a + b
  let d := R - F.card
  change 0 < d → ∀ i ∈ D \ F, Nonempty (OppositeCuts u D Γ P Q a d i)
  intro _ i hi
  have hiF : i ∉ F := (Finset.mem_sdiff.mp hi).2
  have hF (γ : K) (hγ : γ ∈ Γ) : F ⊆ errorSet u D γ (P γ) := by
    intro j hj
    obtain ⟨V, hV⟩ := (mem_curveFixed.mp hj).2
    apply (root_iff_error hL hγ j).mp
    rw [hV, map_mul, hQΓ γ hγ, zero_mul]
  obtain ⟨γ₀, hγ₀⟩ := hΓ
  obtain ⟨hP, hE, _, hR⟩ := hreg.mark γ₀ hγ₀
  have hcard := Finset.card_le_card (hF γ₀ hγ₀)
  rw [hE] at hcard
  have hsize : R = d + F.card := by dsimp [d, R]; omega
  let N := contracted u D F a R d
  have ha := anchor_ranks hsize hreg.domain_card hP hE (hF γ₀ hγ₀) hR
  letI : Fact (Prime Q) := ⟨hQ.prime⟩
  let φ := curveMap Q
  have hnot : φ (nodeEquation L i) ≠ 0 := by
    intro hz
    exact hiF (mem_curveFixed.mpr ⟨(Finset.mem_sdiff.mp hi).1,
      (curveMap_zero_iff Q _).mp hz⟩)
  have hLφ : L.map φ ≠ 0 := fun hz => hnot (by rw [eval_nodeEquation, hz, eval_zero])
  obtain ⟨T, _, hTd, hLT, hNT⟩ := contracted_kernel φ hsize hL.degree hL.kernel
    (fun j hj => (curveMap_zero_iff Q _).mpr (mem_curveFixed.mp hj).2) hLφ
  have hTi : T.eval (φ (planeConstant (node i))) ≠ 0 := by
    intro hz
    exact hnot (by rw [eval_nodeEquation, hLT, eval_mul, hz, mul_zero])
  have selected_cut (rows : Fin d → Fin 2 × Fin a) (γ : K) (hγ : γ ∈ Γ)
      (hγi : i ∈ errorSet u D γ (P γ)) :
      onGraph γ (cutMatrix N rows i).det = 0 := by
    obtain ⟨c, hc, hLc⟩ := hL.fiber γ hγ
    have hLγ : L.map (onGraph γ) ≠ 0 := by
      rw [hLc]
      exact smul_ne_zero hc (locator_monic node _).ne_zero
    obtain ⟨U, hU, hUd, hLU, hNU⟩ := contracted_kernel (onGraph γ) hsize hL.degree hL.kernel
      (fun j hj => (root_iff_error hL hγ j).mpr (hF γ hγ hj)) hLγ
    have hz := (root_iff_error hL hγ i).mpr hγi
    simp only [eval_nodeEquation, hLU, eval_mul, Function.comp_def, graph_constant] at hz
    have hUi := (mul_eq_zero.mp hz).resolve_left (fun he =>
      hiF ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective F i).mp he))
    rw [(onGraph γ).map_det]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨_, coeff_vec_ne_zero U d hUd hU, ?_⟩
    change ((cutMatrix N rows i).map (onGraph γ)).mulVec (fun j => U.coeff j.val) = 0
    rw [cut_action (onGraph γ) (N := N) rows i hUd hNU, graph_constant, hUi]
    funext j
    exact Fin.lastCases (by simp) (fun l => by simp) j
  have makeCut (o : Fin 2) :
      ∃ V : Bivar,
        SeedBox V (if o = 0 then min a d else d - a) (if o = 0 then d - a else min a d) ∧
        (¬ Q ∣ V) ∧ ∀ γ ∈ Γ, i ∈ errorSet u D γ (P γ) → onGraph γ V = 0 := by
    obtain ⟨rows, hdet, hcount⟩ := select_rows _ ha.1 o (ha.2 o)
    let B := N.submatrix rows Fin.castSucc
    have hB : onGraph γ₀ B.det ≠ 0 := by
      rw [(onGraph γ₀).map_det]
      exact hdet
    have hBφ : ((N.map φ).submatrix rows Fin.castSucc).det ≠ 0 := by
      change (φ.mapMatrix B).det ≠ 0
      rw [← φ.map_det B]
      intro hz
      obtain ⟨W, hW⟩ := (curveMap_zero_iff Q B.det).mp hz
      exact hB (by rw [hW, map_mul, hQΓ γ₀ hγ₀, zero_mul])
    refine ⟨(cutMatrix N rows i).det, ?_, ?_, selected_cut rows⟩
    · let A₀ := Finset.univ.filter (fun j => (rows j).1 = 0)
      let A₁ := Finset.univ.filter (fun j => (rows j).1 ≠ 0)
      have hb : SeedBox (cutMatrix N rows i).det A₀.card A₁.card :=
        cut_box u D F a R d rows i
      have htotal : A₀.card + A₁.card = d := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          (Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin d))) (p := fun j => (rows j).1 = 0))
      have hsum : min a d + (d - a) = d := by omega
      by_cases ho : o = 0
      · have hcount₀ : A₀.card = min a d := by simpa only [ho] using hcount
        rw [hcount₀] at htotal
        have hcount₁ := Nat.add_left_cancel (htotal.trans hsum.symm)
        simpa [ho, hcount₀, hcount₁] using hb
      · have hval : o.val ≠ 0 := fun h => ho (Fin.ext h)
        have h₁ : o = 1 := Fin.ext (by have := o.isLt; omega)
        have heq (k : Fin 2) : (k = 1) ↔ (k ≠ 0) := by
          fin_cases k <;> simp
        have hfilter : A₁ = Finset.univ.filter (fun j => (rows j).1 = o) := by
          apply Finset.ext
          intro j
          simp only [A₁, Finset.mem_filter, Finset.mem_univ, true_and, h₁, heq]
        have hcount₁ : A₁.card = min a d := by rw [hfilter, hcount]
        rw [hcount₁] at htotal
        have hcount₀ := Nat.add_right_cancel (htotal.trans ((Nat.add_comm _ _).trans hsum).symm)
        simpa [ho, hcount₀, hcount₁] using hb
    · exact fun hz => (cut_ne_zero φ (N := N) rows i hBφ hTd hNT hTi)
        ((curveMap_zero_iff Q _).mpr hz)
  obtain ⟨V, hVb, hVp, hVz⟩ := makeCut 0
  obtain ⟨W, hWb, hWp, hWz⟩ := makeCut 1
  exact ⟨⟨V, W, by simpa using hVb, by simpa using hWb, hVp, hWp,
    fun γ hγ hγi => ⟨hVz γ hγ hγi, hWz γ hγ hγi⟩⟩⟩

end

end K1_2_4_2
end PackSource_K1_2_4_2Proof

section PackSource_K1_2_3Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace K1_2_3

open Finset Matrix FrobeniusLocator K1 K1_2

theorem proof : K1_2.c3 := by
  intro u D Γ r g hr hr16 hg F Q hreg J hJ hnon
  obtain ⟨hH, hR, hRp, hsize⟩ := child_parameters r g hr hr16 hg
  obtain ⟨hsub, hJc⟩ := Finset.mem_powersetCard.mp hJ
  have hD : (D \ J).card = 131072 + childRows r + childErrors r g := by
    rw [Finset.card_sdiff_of_subset hsub, F.domain_card, hJc, hsize]
  have hmark := fun γ hγ => child_mark F hr hr16 hg (γ := γ) (J := J) hγ
  have hrank (γ : K) (hγ : γ ∈ childSlopes F J) :=
    evaluated_rank Q (Finset.sdiff_subset : D \ J ⊆ D) hH hR hD γ
      (hreg γ (hmark γ hγ).1) (F.decoder γ) (hmark γ hγ).2.1 (hmark γ hγ).2.2.1
  refine ⟨hD, le_antisymm ?_ ?_, ?_⟩
  · exact plane_rank_le u (D \ J) (childRows r) (childErrors r g) hRp
      (formal_graph_rank_le Q Finset.sdiff_subset hH hD)
  · obtain ⟨γ, hγ⟩ := hnon
    exact (hrank γ hγ).ge.trans
      (rank_ge_specialization _ (onGraph γ) _ (IsFractionRing.injective Bivar (FractionRing Bivar)))
  · intro γ hγ
    obtain ⟨_, hdegree, hE, hbad⟩ := hmark γ hγ
    exact ⟨hdegree, hE, hbad, hrank γ hγ⟩

end K1_2_3
end PackSource_K1_2_3Proof

section PackSource_K1_14_3_2RSplit
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace K1_14_3_2R

noncomputable section

open K1 K1_14 K1_14_3 K1_14_3_2 K1_14_3_2_3 Polynomial
open private mass_le from ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Split
open private raw positions t y v scalar par free from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private eval_y eval_v eval_seed baseMap from ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Aux3

private theorem chart_eq (s : Slice) : sectionChart s = planeMap s := by
  apply jetHom_ext
  · intro a
    rw [show scalar a = C (C (MvPolynomial.C a)) by rfl, eval_seed]
    simp [sectionChart, raw, baseMap]
    exact (IsScalarTower.algebraMap_apply FX (MvPolynomial (Fin 4) FX) SectionField a).symm
  · intro i
    rw [show t i = C (C (MvPolynomial.X i)) by rfl, eval_seed]
    cases s <;> fin_cases i <;>
      simp [sectionChart, raw, positions, par, free, seedCoordinates, parameter]
  · rw [show y = C (Polynomial.X (R := Seeds)) by rfl, eval_y]
    cases s <;> simp [sectionChart, raw, positions, par, free, ordinateCoordinate, parameter]
  · rw [show v = Polynomial.X (R := Equation) by rfl, eval_v]
    cases s <;> simp [sectionChart, raw, positions, par, free, derivativeCoordinate, parameter]

theorem prime_transport : K1_14_3_2_3.c1 := by
  intro s q
  have h := localized_prime s q
  rw [chart_eq s] at h
  exact h

theorem proper_transport : K1_14_3_2_3.c2 := by
  intro s ht P Q hp
  let : UniqueFactorizationMonoid SectionField := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid Plane := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  obtain ⟨hP, hQ, h⟩ := coprime_of_transport (planeMap s) ht hp
  exact ⟨hP, hQ, h⟩

theorem residual_sections : K1_14_3_2.c3 :=
  K1_14_3_2_3.of_children prime_transport proper_transport

theorem graph_sections : GraphSections := by
  intro P Q b u hp hc hd qs hq
  have hbound (s : Slice) (n : ℕ)
      (H : Module.Finite SectionField (PlaneQuotient (planeMap s P) (planeMap s Q)) ∧
        Module.finrank SectionField (PlaneQuotient (planeMap s P) (planeMap s Q)) ≤ n) :
      mass qs s ≤ (n : ℚ) :=
    (mass_le s P Q qs hq (prime_transport s) H.1).trans (Nat.cast_le.mpr H.2)
  have proper (s : Slice) := proper_transport s (prime_transport s) P Q hp
  constructor
  · simpa using hbound .seed _ (capped_bound _ _ b 0 63 1 (by decide) (by decide)
      (proper .seed) (planeMap_caps .seed P _ hc) (planeMap_caps .seed Q _ hd))
  · simpa using hbound .ordinate _ (box_bound _ _ u 0 812 1 (by decide) (by decide)
      (proper .ordinate) (planeMap_caps .ordinate P _ hc) (planeMap_caps .ordinate Q _ hd))
  · simpa [Nat.cast_add, Nat.cast_mul, mul_comm] using hbound .mixed _
      (box_bound _ _ u b 812 63 (by decide) (by decide)
        (proper .mixed) (planeMap_caps .mixed P _ hc) (planeMap_caps .mixed Q _ hd))
  · simpa [Nat.cast_mul, mul_comm] using hbound .jets _ (total_bound _ _ u 812 (by decide)
      (proper .jets) (planeMap_caps .jets P _ hc) (planeMap_caps .jets Q _ hd))

theorem of_children (seedImages : K1_14_3_2.c5) (jetImages : K1_14_3_2.c6) : K1_14_3.c2 :=
  assemble K1_14_3_2_1.proof residual_sections graph_sections seedImages jetImages K1_14_3_2_7.proof

end
end K1_14_3_2R
end PackSource_K1_14_3_2RSplit

section PackSource_K1_10_1Scalar
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace K1_10_1
noncomputable section

open MvPolynomial K1_11

private def scalarVariables : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  Equiv.ofBijective ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1] (by decide)

variable {F : Type*} [Field F]

def groupSeeds : MvPolynomial (Fin 4) F ≃+* MvPolynomial (Fin 2) (MvPolynomial (Fin 2) F) :=
  (renameEquiv F scalarVariables).toRingEquiv.trans (sumRingEquiv F (Fin 2) (Fin 2))

private def joinExponents (e f : Fin 2 →₀ ℕ) : Fin 4 →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, f)).mapDomain scalarVariables.symm

private theorem joinExponents_apply (e f : Fin 2 →₀ ℕ) :
    joinExponents e f 0 = e 0 ∧ joinExponents e f 1 = e 1 ∧
      joinExponents e f 2 = f 0 ∧ joinExponents e f 3 = f 1 := by
  simp [joinExponents, scalarVariables]

private theorem grouped_coeff (Q : MvPolynomial (Fin 4) F) (e f : Fin 2 →₀ ℕ) :
    ((groupSeeds Q).coeff e).coeff f = Q.coeff (joinExponents e f) := by
  classical
  let g := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, f)
  have hg : (joinExponents e f).mapDomain scalarVariables = g := by
    have he : (scalarVariables : Fin 4 → Fin 2 ⊕ Fin 2) ∘ scalarVariables.symm = id :=
      funext scalarVariables.apply_symm_apply
    rw [joinExponents, ← Finsupp.mapDomain_comp, he, Finsupp.mapDomain_id]
  rw [← coeff_rename_mapDomain scalarVariables scalarVariables.injective, hg]
  change ((sumRingEquiv F (Fin 2) (Fin 2) (rename scalarVariables Q)).coeff e).coeff f =
    (rename scalarVariables Q).coeff g
  generalize rename scalarVariables Q = P
  induction P using MvPolynomial.induction_on' with
  | add P R hp hr => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hr]
  | monomial a b =>
    change ((AddMonoidAlgebra.curryRingEquiv
        (AddMonoidAlgebra.mapDomainRingEquiv F Finsupp.sumFinsuppAddEquivProdFinsupp
          (AddMonoidAlgebra.single a b))).coeff e).coeff f = _
    rw [AddMonoidAlgebra.mapDomainRingEquiv_single]
    generalize hpair : Finsupp.sumFinsuppAddEquivProdFinsupp a = pair
    rcases pair with ⟨i,j⟩
    rw [AddMonoidAlgebra.curryRingEquiv_single]
    change ((monomial i (monomial j b)).coeff e).coeff f = (monomial a b).coeff g
    have ha : a = g ↔ i = e ∧ j = f := by
      rw [← Finsupp.sumFinsuppAddEquivProdFinsupp.injective.eq_iff, hpair,
        show Finsupp.sumFinsuppAddEquivProdFinsupp g = (e, f) from AddEquiv.apply_symm_apply _ _, Prod.mk.injEq]
    by_cases hi : i = e <;> by_cases hj : j = f <;> simp [coeff_monomial, ha, hi, hj]

private theorem group_eval (Q : MvPolynomial (Fin 4) F) (P : Polynomial F) (s t : F) :
    aeval ![Polynomial.X, P] ((groupSeeds Q).map (eval ![s,t])) =
      aeval (scalarImages P s t) Q := by
  let lhs := (aeval ![Polynomial.X, P]).toRingHom.comp
    ((map (eval ![s,t])).comp (groupSeeds (F:=F)).toRingHom)
  have heq : lhs = (aeval (scalarImages P s t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, groupSeeds]
    · intro i
      fin_cases i <;> simp [lhs, groupSeeds, scalarVariables, scalarImages]
  exact RingHom.congr_fun heq Q

def toScalarSource (Q : MvPolynomial (Fin 4) K1.K) (hn : Q ≠ 0)
    (hy : Q.weightedTotalDegree scalarWeightY ≤ 5)
    (hs : Q.weightedTotalDegree scalarWeightYS ≤ 26)
    (ht : Q.weightedTotalDegree scalarWeightT ≤ 21)
    (htot : Q.weightedTotalDegree scalarWeightTotal ≤ 37) : K1_10.ScalarSource := by
  have bounds (e f : Fin 2 →₀ ℕ) (hf : f ∈ ((groupSeeds Q).coeff e).support) :
      e 1 ≤ 5 ∧ f 0 ≤ 26 ∧ f 1 ≤ 21 ∧ e 1 + (f 0 + f 1) ≤ 37 := by
    have he : joinExponents e f ∈ Q.support := by
      rw [MvPolynomial.mem_support_iff, ← grouped_coeff]
      exact MvPolynomial.mem_support_iff.mp hf
    have ⟨h0,h1,h2,h3⟩ := joinExponents_apply e f
    have hy' := (le_weightedTotalDegree scalarWeightY he).trans hy
    have hs' := (le_weightedTotalDegree scalarWeightYS he).trans hs
    have ht' := (le_weightedTotalDegree scalarWeightT he).trans ht
    have htot' := (le_weightedTotalDegree scalarWeightTotal he).trans htot
    simp [scalarWeightY, scalarWeightYS, scalarWeightT, scalarWeightTotal,
      Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ,
      h0,h1,h2,h3, smul_eq_mul] at hy' hs' ht' htot'
    omega
  refine ⟨groupSeeds Q, (map_ne_zero_iff (groupSeeds (F:=K1.K)).toRingHom
    (groupSeeds (F:=K1.K)).injective).mpr hn, ?_, ?_, ?_, ?_⟩
  · rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro e he
    obtain ⟨f,hf⟩ := support_nonempty.mpr (MvPolynomial.mem_support_iff.mp he)
    exact (bounds e f hf).1
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf => (bounds e f hf).2.1)
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf => (bounds e f hf).2.2.1)
  · intro e he
    have hcoeff := MvPolynomial.mem_support_iff.mp he
    obtain ⟨f,hf⟩ := support_nonempty.mpr hcoeff
    have he' := (bounds e f hf).2.2.2
    have hb : ((groupSeeds Q).coeff e).totalDegree ≤ 37 - e 1 := by
      apply Finset.sup_le
      intro g hg
      have hh := (bounds e g hg).2.2.2
      simp [Finsupp.sum_fintype, Fin.sum_univ_succ]
      omega
    omega

theorem toScalarSource_atDecoder (Q : MvPolynomial (Fin 4) K1.K) (hn) (hy) (hs) (ht) (htot)
    (γ : K1.K) (P : Polynomial K1.K) :
    (toScalarSource Q hn hy hs ht htot).atDecoder γ P =
      aeval (scalarImages P γ (γ ^ K1.p)) Q := group_eval Q P γ (γ ^ K1.p)

end
end K1_10_1
end PackSource_K1_10_1Scalar

section PackSource_K1_10_1Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K1_10_1
noncomputable section

open K1 K1_10 K1_11 MvPolynomial

/-- Exact degrees of the plane relation in the source filtrations. -/
def c1 : Prop :=
  ∀ u deleted h U V (W : Plane u deleted h U V),
    ∀ j, (planeRelation U V W.output).weightedTotalDegree (sourceWeights 131071 j) =
      relationBounds h j

/-- The relation starts in contact order one at each retained node. -/
def c2 : Prop :=
  ∀ u deleted h U V (W : Plane u deleted h U V), ∀ i ∉ deleted,
    (contactLift contactWeight (shiftAt u i (planeRelation U V W.output))).natTrailingDegree = 1

/-- Primitivity in the variable being eliminated. -/
def c3 : Prop :=
  ∀ u deleted h U V (W : Plane u deleted h U V),
    (Polynomial.C (denominator V) * Polynomial.X - Polynomial.C (numerator U W.output)).IsPrimitive

private theorem eval_liftOrdinary (Q P : Polynomial K) (s t : K) :
    aeval (scalarImages P s t) (liftOrdinary Q) = Q := by
  let φ : MvPolynomial (Fin 4) K →+* Polynomial K := (aeval (scalarImages P s t)).toRingHom
  have hh : φ.comp liftOrdinary = RingHom.id (Polynomial K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [φ, liftOrdinary]
    · simp [φ, liftOrdinary, scalarImages]
  exact RingHom.congr_fun hh Q

private theorem eval_denominator (V : Fin 2 → Polynomial K) (P : Polynomial K) (s t : K) :
    aeval (scalarImages P s t) (denominator V) = V 0 + Polynomial.C s * V 1 := by
  simp only [denominator, pencil, map_add, map_mul, aeval_X, eval_liftOrdinary]
  rfl

private theorem denominator_ne {V : Fin 2 → Polynomial K} (hV : ∃ j, V j ≠ 0) :
    denominator V ≠ 0 := by
  intro hz
  have h (s : K) := eval_denominator V 0 s 0
  simp only [hz, map_zero] at h
  have h0 : V 0 = 0 := by simpa using (h 0).symm
  have h1 : V 1 = 0 := by simpa [h0] using (h 1).symm
  obtain ⟨j,hj⟩ := hV
  fin_cases j
  · exact hj h0
  · exact hj h1

private theorem relation_eval (U V : Fin 2 → Polynomial K) (O : Fin 2 → Fin 2 → Polynomial K)
    (Q Q' : Polynomial K) (s t : K) :
    aeval (decoderImages Q Q' s t) (planeRelation U V O) =
      (V 0 + Polynomial.C s * V 1) * Q' -
      ((O 0 0 + Polynomial.C s * O 1 0) + Polynomial.C t * (O 0 1 + Polynomial.C s * O 1 1) -
        (U 0 + Polynomial.C t * U 1) * Q) := by
  rw [decoderImages, ← polynomialView_eval, planeRelation_view]
  simp [eval_denominator, numerator, pencil, eval_liftOrdinary]
  rfl

private theorem relation_at_decoder {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (P : Puncture deleted)
    (hdeg : (planeRelation U V W.output).weightedTotalDegree (sourceWeights 131071 0) ≤ 131071 + h)
    (hh : h ≤ 32670) (Q Q' : Polynomial K) (hq : Q.natDegree ≤ 131071)
    (hq' : Q'.natDegree ≤ 131071) (s t : K) (S : Finset (Fin P.N)) (hS : 180265 ≤ S.card)
    (hc : correctOn u P Q Q' s t S) :
    aeval (decoderImages Q Q' s t) (planeRelation U V W.output) = 0 := by
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 1
  · intro j hj
    rw [pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, relation_eval]
    have hi : P.index j ∉ deleted := (P.retained _).mp ⟨j, rfl⟩
    have hcj := hc j hj
    change Q.eval (node (P.index j)) = u 0 (P.index j) + s * u 1 (P.index j) ∧
      Q'.eval (node (P.index j)) = u 0 (P.index j) ^ p + t * u 1 (P.index j) ^ p at hcj
    simp only [Puncture.nodes, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, hcj.1, hcj.2]
    linear_combination W.nodes _ hi 0 0 + s * W.nodes _ hi 1 0 +
      t * W.nodes _ hi 0 1 + (s*t) * W.nodes _ hi 1 1
  · have hd := decoder_eval_degree 131071 (131071+h) _ hdeg Q Q' hq hq' s t
    omega

private theorem coeff_bounds (L : MvPolynomial (Fin 5) K) (a b : MvPolynomial (Fin 4) K)
    (d : ℕ) (hL : L ∈ filtered (sourceWeights 131071) (sourceBounds d 1 1 1))
    (hview : polynomialView L = Polynomial.C b * Polynomial.X - Polynomial.C a)
    (hb : b ≠ 0) :
    a.weightedTotalDegree scalarWeightY ≤ 1 ∧ b.weightedTotalDegree scalarWeightY ≤ 0 ∧
    a.weightedTotalDegree scalarWeightYS ≤ 1 ∧ b.weightedTotalDegree scalarWeightYS ≤ 1 ∧
    a.weightedTotalDegree scalarWeightT ≤ 1 ∧ b.weightedTotalDegree scalarWeightT ≤ 0 := by
  have hz : (polynomialView L).coeff 0 = -a := by
    rw [hview]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X]
  have hone : (polynomialView L).coeff 1 = b := by
    rw [hview]
    simp [Polynomial.coeff_sub, Polynomial.coeff_C]
  obtain ⟨hy, hs, ht⟩ := polynomialView_source_coefficients d 131071 1 1 1 L hL
  have hs1 := hs 1 (by decide) (hone ▸ hb)
  have hy1 := hy 1 (by decide) (hone ▸ hb)
  have ht1 := ht 1 (by decide) (hone ▸ hb)
  rw [hone] at hs1 hy1 ht1
  have ha (v : Fin 4 → ℕ) : (-a).weightedTotalDegree v = a.weightedTotalDegree v := by
    simp [weightedTotalDegree]
  have ha0 : a.weightedTotalDegree scalarWeightY ≤ 1 ∧
      a.weightedTotalDegree scalarWeightYS ≤ 1 ∧ a.weightedTotalDegree scalarWeightT ≤ 1 := by
    by_cases ha' : a = 0
    · simp [ha', weightedTotalDegree]
    · have h0 : (polynomialView L).coeff 0 ≠ 0 := hz ▸ neg_ne_zero.mpr ha'
      have hy0 := hy 0 (by decide) h0
      have hs0 := hs 0 (by decide) h0
      have ht0 := ht 0 (by decide) h0
      simp only [hz, ha, Nat.add_zero] at hy0 hs0 ht0
      exact ⟨hy0, hs0, ht0⟩
  exact ⟨ha0.1, by omega, ha0.2.1, hs1, ha0.2.2, by omega⟩

private theorem total_bound (Q : MvPolynomial (Fin 4) K)
    (hs : Q.weightedTotalDegree scalarWeightYS ≤ 21)
    (ht : Q.weightedTotalDegree scalarWeightT ≤ 16) :
    Q.weightedTotalDegree scalarWeightTotal ≤ 37 := by
  apply Finset.sup_le
  intro e he
  have hS := (le_weightedTotalDegree scalarWeightYS he).trans hs
  have hT := (le_weightedTotalDegree scalarWeightT he).trans ht
  simp [scalarWeightYS, scalarWeightT, scalarWeightTotal, Finsupp.weight_apply,
    Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul] at hS hT ⊢
  omega

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_10.c1 := by
  intro u deleted h U V W _ hh hs
  let P := nativePuncture deleted
  let L := planeRelation U V W.output
  let a := numerator U W.output
  let b := denominator V
  have hb : b ≠ 0 := denominator_ne W.V_ne
  have hview : polynomialView L = Polynomial.C b * Polynomial.X - Polynomial.C a :=
    planeRelation_view U V W.output
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j :=
    h1 u deleted h U V W
  have hl : L ≠ 0 := by
    intro hz
    have hpos := hdeg 1
    simp [hz, relationBounds, weightedTotalDegree] at hpos
  let C : Contacts P.N L :=
    ⟨P.nodes, fun i => u 0 (P.index i), fun i => u 1 (P.index i),
      fun i => u 0 (P.index i) ^ p, fun i => u 1 (P.index i) ^ p,
      fun i => h2 u deleted h U V W (P.index i) ((P.retained _).mp ⟨i, rfl⟩)⟩
  have hN : P.N = 262144 - deleted.card := by have := P.size; omega
  obtain ⟨G, hnot, hcontacts⟩ := quotientSource C hdeg hl (by omega) (hN ▸ hs)
  let Q := scalarEliminant 5 G.val a b
  have hne : Q ≠ 0 := scalarEliminant_ne_zero 721059 131071 5 16 16
    G.val L G.property hnot a b hb hview (h3 u deleted h U V W)
  have hLsource : L ∈ filtered (sourceWeights 131071) (sourceBounds (131071+h) 1 1 1) := by
    apply (mem_filtered _ _ _).mpr
    intro j
    rw [hdeg j]
    rfl
  obtain ⟨haY, hbY, haS, hbS, haT, hbT⟩ := coeff_bounds L a b _ hLsource hview hb
  obtain ⟨hY,hS,hT⟩ := polynomialView_source_coefficients 721059 131071 5 16 16 G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 :=
    clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val) a b
      (by simpa using hY) haY hbY (by decide)
  have hs' : Q.weightedTotalDegree scalarWeightYS ≤ 21 :=
    clearedEval_weight_bound scalarWeightYS 5 16 0 1 1 (polynomialView G.val) a b
      (by simpa using hS) haS hbS (by decide)
  have ht' : Q.weightedTotalDegree scalarWeightT ≤ 16 :=
    clearedEval_weight_bound scalarWeightT 5 16 1 1 0 (polynomialView G.val) a b
      (by simpa using hT) haT hbT (by decide)
  refine ⟨toScalarSource Q hne hy (hs'.trans (by decide)) (ht'.trans (by decide))
    (total_bound Q hs' ht'), ?_⟩
  intro γ M hdis
  rw [toScalarSource_atDecoder]
  let S := indexedSupport P M.support
  have hS' : 180265 ≤ S.card := by
    rw [indexedSupport_card P M.support
      (fun i hi hid => Finset.disjoint_left.mp hdis hi hid)]
    exact M.agreement
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 := Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hrel := relation_at_decoder W P (le_of_eq (hdeg 0)) (by omega)
    _ _ hd hd' γ (γ ^ p) S hS' hcorrect
  apply scalarEliminant_annihilates 721059 131071 5 16 16
    G.val L G.property a b hview M.decoder (M.decoder.map twist) γ (γ ^ p) hrel
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hcontacts i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ γ (γ ^ p) _ _ G.val L R.val
      (hcorrect i hi).1 (hcorrect i hi).2 hrel hR
  · have hdG := decoder_eval_degree 131071 721059 G.val
      ((mem_filtered _ _ _).mp G.property 0) _ _ hd hd' γ (γ ^ p)
    omega

end
end K1_10_1
end PackSource_K1_10_1Split

section PackSource_K1_10_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace K1_10_1_2

noncomputable section

open K1 K1_10 K1_10_1 K1_11 K1_11_2 MvPolynomial

private abbrev PlanePoly := MvPolynomial (Fin 5) K

private def ordinary : Polynomial K →+* PlanePoly :=
  Polynomial.eval₂RingHom C (MvPolynomial.X 0)

private def planePencil (A : Fin 2 → Polynomial K) (z : PlanePoly) : PlanePoly :=
  ordinary (A 0) + z * ordinary (A 1)

private def planeOutput (O : Fin 2 → Fin 2 → Polynomial K) : PlanePoly :=
  planePencil (fun j => O j 0) (MvPolynomial.X 3) +
    MvPolynomial.X 4 * planePencil (fun j => O j 1) (MvPolynomial.X 3)

private theorem view_ordinary (Q : Polynomial K) :
    polynomialView (ordinary Q) = Polynomial.C (liftOrdinary Q) := by
  have hh : (polynomialView (F := K)).toRingHom.comp ordinary =
      Polynomial.C.comp liftOrdinary := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [ordinary, liftOrdinary, polynomialView, finSuccEquiv_apply]
    · simp [ordinary, liftOrdinary, polynomialView_X]
  exact RingHom.congr_fun hh Q

private theorem relation_eq (U V : Fin 2 → Polynomial K)
    (O : Fin 2 → Fin 2 → Polynomial K) :
    planeRelation U V O =
      planePencil U (MvPolynomial.X 4) * MvPolynomial.X 1 +
      planePencil V (MvPolynomial.X 3) * MvPolynomial.X 2 - planeOutput O := by
  apply polynomialView.injective
  simp only [planeRelation_view, planePencil, planeOutput, map_sub, map_add, map_mul,
    view_ordinary, polynomialView_X]
  change _ = (Polynomial.C (liftOrdinary (U 0)) +
      Polynomial.C (MvPolynomial.X 3) * Polynomial.C (liftOrdinary (U 1))) * Polynomial.C (MvPolynomial.X 1) +
      (Polynomial.C (liftOrdinary (V 0)) +
      Polynomial.C (MvPolynomial.X 2) * Polynomial.C (liftOrdinary (V 1))) * Polynomial.X -
      ((Polynomial.C (liftOrdinary (O 0 0)) +
      Polynomial.C (MvPolynomial.X 2) * Polynomial.C (liftOrdinary (O 1 0))) +
      Polynomial.C (MvPolynomial.X 3) * (Polynomial.C (liftOrdinary (O 0 1)) +
      Polynomial.C (MvPolynomial.X 2) * Polynomial.C (liftOrdinary (O 1 1))))
  simp only [denominator, numerator, pencil, map_sub, map_add, map_mul]
  ring

private theorem omits_add {P Q : PlanePoly} (hp : OmitsMessages P) (hq : OmitsMessages Q) :
    OmitsMessages (P + Q) := by
  constructor
  · exact Nat.eq_zero_of_le_zero (by simpa only [hp.1, hq.1, max_self] using degreeOf_add_le 1 P Q)
  · exact Nat.eq_zero_of_le_zero (by simpa only [hp.2, hq.2, max_self] using degreeOf_add_le 2 P Q)

private theorem omits_mul {P Q : PlanePoly} (hp : OmitsMessages P) (hq : OmitsMessages Q) :
    OmitsMessages (P * Q) := by
  constructor
  · exact Nat.eq_zero_of_le_zero (by simpa only [hp.1, hq.1, Nat.add_zero] using degreeOf_mul_le 1 P Q)
  · exact Nat.eq_zero_of_le_zero (by simpa only [hp.2, hq.2, Nat.add_zero] using degreeOf_mul_le 2 P Q)

private theorem omits_ordinary (Q : Polynomial K) : OmitsMessages (ordinary Q) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq =>
    rw [map_add]
    exact omits_add hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    simp only [ordinary, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
    apply omits_mul
    · exact ⟨degreeOf_C _ _, degreeOf_C _ _⟩
    · exact ⟨degreeOf_X_pow_of_ne _ (by decide), degreeOf_X_pow_of_ne _ (by decide)⟩

private theorem omits_pencil (A : Fin 2 → Polynomial K) {z : PlanePoly}
    (hz : OmitsMessages z) : OmitsMessages (planePencil A z) :=
  omits_add (omits_ordinary _) (omits_mul hz (omits_ordinary _))

private theorem omits_seed (j : Fin 5) (h1 : (1 : Fin 5) ≠ j) (h2 : (2 : Fin 5) ≠ j) :
    OmitsMessages (MvPolynomial.X j : PlanePoly) :=
  ⟨degreeOf_X_of_ne h1, degreeOf_X_of_ne h2⟩

private theorem node_ordinary (x a b c d : K) (Q : Polynomial K) :
    nodeWordMap x a b c d (ordinary Q) = C (Q.eval x) := by
  have hh : (nodeWordMap x a b c d).toRingHom.comp ordinary =
      C.comp (Polynomial.evalRingHom x) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [ordinary, nodeWordMap]
    · simp [ordinary, nodeWordMap, nodeWordImages]
  exact RingHom.congr_fun hh Q

private theorem node_pencil (x a b c d : K) (A : Fin 2 → Polynomial K)
    (j : Fin 5) (hj : j = 3 ∨ j = 4) :
    nodeWordMap x a b c d (planePencil A (MvPolynomial.X j)) =
      C ((A 0).eval x) + MvPolynomial.X j * C ((A 1).eval x) := by
  simp only [planePencil, map_add, map_mul, node_ordinary]
  rcases hj with rfl | rfl <;> simp [nodeWordMap, nodeWordImages]

private theorem node_relation {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (i : I) (hi : i ∉ deleted) :
    nodeWordMap (node i) (u 0 i) (u 1 i) (u 0 i ^ p) (u 1 i ^ p)
      (planePencil U (MvPolynomial.X 4) * MvPolynomial.X 1 +
        planePencil V (MvPolynomial.X 3) * MvPolynomial.X 2 - planeOutput W.output) = 0 := by
  simp only [planeOutput, map_add, map_mul, map_sub, node_pencil _ _ _ _ _ _ _ (Or.inl rfl),
    node_pencil _ _ _ _ _ _ _ (Or.inr rfl)]
  simp only [nodeWordMap, aeval_X, nodeWordImages, Matrix.cons_val]
  have hnode (j l : Fin 2) :
      C ((U l).eval (node i)) * C (u j i) + C ((V j).eval (node i)) * C (u l i ^ p) =
        (C ((W.output j l).eval (node i)) : PlanePoly) := by
    simpa only [map_add, map_mul] using congrArg (C : K →+* PlanePoly) (W.nodes i hi j l)
  linear_combination hnode 0 0 + MvPolynomial.X 3 * hnode 1 0 + MvPolynomial.X 4 * hnode 0 1 +
    (MvPolynomial.X 3 * MvPolynomial.X 4) * hnode 1 1

private theorem affine_coefficients_zero (j : Fin 5) (a b : K)
    (hz : C a + MvPolynomial.X j * C b = (0 : PlanePoly)) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    simpa using congrArg (MvPolynomial.eval (fun _ : Fin 5 => (0 : K))) hz
  have hb : b = 0 := by
    simpa [ha] using congrArg (MvPolynomial.eval (fun _ : Fin 5 => (1 : K))) hz
  exact ⟨ha, hb⟩

private theorem node_pencils_ne {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (i : I) :
    nodeWordMap (node i) (u 0 i) (u 1 i) (u 0 i ^ p) (u 1 i ^ p)
      (planePencil U (MvPolynomial.X 4)) ≠ 0 ∨
    nodeWordMap (node i) (u 0 i) (u 1 i) (u 0 i ^ p) (u 1 i ^ p)
      (planePencil V (MvPolynomial.X 3)) ≠ 0 := by
  by_contra! hz
  rw [node_pencil _ _ _ _ _ _ _ (Or.inr rfl), node_pencil _ _ _ _ _ _ _ (Or.inl rfl)] at hz
  have hu := affine_coefficients_zero _ _ _ hz.1
  have hv := affine_coefficients_zero _ _ _ hz.2
  apply Polynomial.not_isUnit_X_sub_C (node i)
  apply W.primitive
  · intro l
    apply Polynomial.dvd_iff_isRoot.mpr
    fin_cases l
    · exact hu.1
    · exact hu.2
  · intro j
    apply Polynomial.dvd_iff_isRoot.mpr
    fin_cases j
    · exact hv.1
    · exact hv.2

theorem proof : K1_10_1.c2 := by
  intro u deleted h U V W i hi
  rw [shiftAt, relation_eq]
  have hs := omits_seed 3 (by decide) (by decide)
  have ht := omits_seed 4 (by decide) (by decide)
  apply linear_relation_node_contact_one _ _ _ _ _
    _ _ _ (omits_pencil U ht) (omits_pencil V hs)
    (omits_add (omits_pencil _ hs) (omits_mul ht (omits_pencil _ hs)))
  · rw [contactConstant_shift]
    simpa only [planeOutput] using node_relation W i hi
  · simpa only [contactConstant_shift] using node_pencils_ne W i

end

end K1_10_1_2
end PackSource_K1_10_1_2Proof

section PackSource_K1_10_1_3Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_10_1_3

noncomputable section

open K1 K1_10 K1_10_1 MvPolynomial

private abbrev R := MvPolynomial (Fin 4) K

private theorem lift_degree_zero (Q : Polynomial K) {i : Fin 4} (hi : i ≠ 0) :
    (liftOrdinary Q).degreeOf i = 0 := by
  induction Q using Polynomial.induction_on' with
  | monomial n a =>
    change (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (Polynomial.monomial n a)).degreeOf i = 0
    rw [Polynomial.eval₂_monomial]
    exact Nat.eq_zero_of_le_zero ((degreeOf_mul_le i _ _).trans_eq (by
      rw [degreeOf_C, degreeOf_X_pow_of_ne n hi, Nat.zero_add]))
  | add P Q hP hQ =>
    rw [map_add]
    exact Nat.eq_zero_of_le_zero ((degreeOf_add_le i _ _).trans_eq (by simp [hP, hQ]))

private theorem pencil_degree_zero (A : Fin 2 → Polynomial K) {i j : Fin 4}
    (hi : i ≠ 0) (hij : i ≠ j) : (pencil A (MvPolynomial.X j)).degreeOf i = 0 := by
  have hm := degreeOf_mul_le i (MvPolynomial.X j : R) (liftOrdinary (A 1))
  rw [degreeOf_X_of_ne hij, lift_degree_zero _ hi, Nat.zero_add] at hm
  exact Nat.eq_zero_of_le_zero ((degreeOf_add_le i _ _).trans_eq (by
    rw [lift_degree_zero _ hi, Nat.eq_zero_of_le_zero hm, max_self]))

private theorem eval_lift (v : Fin 4 → Polynomial K) (hv : v 0 = Polynomial.X)
    (Q : Polynomial K) : aeval v (liftOrdinary Q) = Q := by
  have hh : (aeval v).toRingHom.comp liftOrdinary = RingHom.id (Polynomial K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [liftOrdinary]
    · simp [liftOrdinary, hv]
  exact RingHom.congr_fun hh Q

/-- Holding X fixed and setting the pencil variable first to zero and then to one
recovers both ordinary coefficients by subtraction. -/
private theorem dvd_pencil_coeffs (d : R) (f : Polynomial K)
    (heval : ∀ v : Fin 4 → Polynomial K, v 0 = Polynomial.X → aeval v d = f)
    (A : Fin 2 → Polynomial K) {i : Fin 4} (hi : i ≠ 0)
    (hd : d ∣ pencil A (MvPolynomial.X i)) : ∀ j, f ∣ A j := by
  have hval (z : Polynomial K) : f ∣ A 0 + z * A 1 := by
    let v := Function.update (K1_11.scalarImages (F := K) 0 0 0) i z
    have hv : v 0 = Polynomial.X := by
      simp only [v, Function.update_of_ne (Ne.symm hi)]
      rfl
    have hvi : v i = z := Function.update_self _ _ _
    have h := (aeval v).toRingHom.map_dvd hd
    change aeval v d ∣ aeval v (pencil A (MvPolynomial.X i)) at h
    simpa only [heval v hv, pencil, map_add, map_mul, aeval_X, eval_lift v hv, hvi] using h
  have h0 : f ∣ A 0 := by simpa using hval 0
  have h1 : f ∣ A 1 := by simpa using dvd_sub (hval 1) h0
  intro j
  fin_cases j
  · exact h0
  · exact h1

private theorem pencil_ne (A : Fin 2 → Polynomial K) (hA : ∃ j, A j ≠ 0)
    {i : Fin 4} (hi : i ≠ 0) : pencil A (MvPolynomial.X i) ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := hA
  apply hj
  have hd : (0 : R) ∣ pencil A (MvPolynomial.X i) := zero_dvd_iff.mpr h
  exact zero_dvd_iff.mp (dvd_pencil_coeffs 0 0 (by simp) A hi hd j)

private theorem divisor_degree_zero {d P : R} (hd : d ∣ P) (hP : P ≠ 0)
    {i : Fin 4} (hi : P.degreeOf i = 0) : d.degreeOf i = 0 := by
  obtain ⟨q, rfl⟩ := hd
  have he : (d * q).degreeOf i = d.degreeOf i + q.degreeOf i :=
    degreeOf_mul_eq (left_ne_zero_of_mul hP) (right_ne_zero_of_mul hP)
  omega

private theorem deriv_zero_of_degree_zero {d : R} {i : Fin 4}
    (h : d.degreeOf i = 0) : pderiv i d = 0 :=
  pderiv_eq_zero_of_notMem_vars (fun hi => (mem_vars_iff_degreeOf_ne_zero.mp hi) h)

private theorem lift_of_degree_zero (d : R) (h : ∀ i ≠ 0, d.degreeOf i = 0) :
    ∃ f : Polynomial K, liftOrdinary f = d := by
  let v := K1_11.scalarImages (F := K) 0 0 0
  refine ⟨aeval v d, ?_⟩
  change (liftOrdinary.comp (aeval v).toRingHom) d = (RingHom.id R) d
  apply hom_congr_vars
  · ext a
    simp [liftOrdinary]
  · intro i hi _
    have h0 : i = 0 := by
      by_contra hn
      exact (mem_vars_iff_degreeOf_ne_zero.mp hi) (h i hn)
    subst i
    simp [liftOrdinary, v, K1_11.scalarImages]
  · rfl

theorem proof : K1_10_1.c3 := by
  intro u deleted h U V W
  apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro d hd
  have hc := (Polynomial.C_dvd_iff_dvd_coeff d _).mp hd
  have hdV : d ∣ denominator V := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] using hc 1
  have hdN : d ∣ numerator U W.output := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] using hc 0
  have hV : denominator V ≠ 0 := pencil_ne V W.V_ne (by decide)
  have hy : d.degreeOf 1 = 0 :=
    divisor_degree_zero hdV hV (pencil_degree_zero V (by decide) (by decide))
  have ht : d.degreeOf 3 = 0 :=
    divisor_degree_zero hdV hV (pencil_degree_zero V (by decide) (by decide))
  -- The derivative extracts the coefficient of Y₀. The common divisor
  -- survives this operation because it is independent of Y₀.
  have hderiv (A : Fin 2 → Polynomial K) (i : Fin 4) (hi : (1 : Fin 4) ≠ i) :
      pderiv 1 (pencil A (MvPolynomial.X i)) = 0 :=
    deriv_zero_of_degree_zero (pencil_degree_zero A (by decide) hi)
  have hdU : d ∣ pencil U (MvPolynomial.X 3) := by
    obtain ⟨q, hq⟩ := hdN
    have he : -(pencil U (MvPolynomial.X 3)) = d * pderiv 1 q := by
      simpa [numerator, pderiv_mul, hderiv _ 2 (by decide), hderiv _ 3 (by decide),
        pderiv_X_of_ne (by decide : (3 : Fin 4) ≠ 1),
        deriv_zero_of_degree_zero hy] using congrArg (pderiv (R := K) (1 : Fin 4)) hq
    exact ⟨-pderiv 1 q, by rw [mul_neg, ← he, neg_neg]⟩
  have hU : pencil U (MvPolynomial.X 3) ≠ 0 := pencil_ne U W.U_ne (by decide)
  have hs : d.degreeOf 2 = 0 :=
    divisor_degree_zero hdU hU (pencil_degree_zero U (by decide) (by decide))
  obtain ⟨f, hf⟩ := lift_of_degree_zero d (by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact hy
    · exact hs
    · exact ht)
  have heval (v : Fin 4 → Polynomial K) (hv : v 0 = Polynomial.X) :
      aeval v d = f := by rw [← hf, eval_lift v hv]
  rw [← hf]
  exact (W.primitive f
    (dvd_pencil_coeffs d f heval U (by decide) hdU)
    (dvd_pencil_coeffs d f heval V (by decide) hdV)).map liftOrdinary

end

end K1_10_1_3
end PackSource_K1_10_1_3Proof

section PackSource_K1_13_7_6_2Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6_2
noncomputable section

open K1_13_7 K1_13_7_6
open scoped BigOperators

/-- The three equations at an isolated point are locally a parameter sequence. -/
def c1 : Prop :=
  ∀ (f g h : Lower) (y : LowerPoint) (q : PrimeSpectrum Lower),
    q.asIdeal = pointIdeal y →
    q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes →
    f ≠ 0 ∧ RegularCut q (Ideal.span {f, g}) h ∧
      ∀ r ∈ precedingPrimes (Ideal.span {f, g}) q, RegularCut r (Ideal.span {f}) g

/-- The length of one regular cut is the cut length on each surviving
minimal prime, weighted by the generic length of the prefix there. -/
def c2 : Prop :=
  ∀ (J : Ideal Lower) (t : Lower) (q : PrimeSpectrum Lower),
    q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes →
    RegularCut q J t →
    (localColength q (J ⊔ Ideal.span {t})).toNat =
      ∑ p ∈ precedingPrimes J q,
        (localColength p J).toNat * (localColength q (cutIdeal p t)).toNat

private theorem span_pair (f g : Lower) :
    Ideal.span ({f, g} : Set Lower) = Ideal.span {f} ⊔ Ideal.span {g} := by
  rw [← Ideal.span_union]
  congr 1

private theorem span_triple (f g h : Lower) :
    Ideal.span ({f, g, h} : Set Lower) = Ideal.span {f, g} ⊔ Ideal.span {h} := by
  rw [← Ideal.span_union]
  congr 1
  ext t
  simp [or_left_comm, or_comm]

private theorem cut_of_preceding {J : Ideal Lower} {t : Lower}
    {q p : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hreg : RegularCut q J t) (hp : p ∈ precedingPrimes J q) :
    t ∉ p.asIdeal ∧ q.asIdeal ∈ (cutIdeal p t).minimalPrimes := by
  obtain ⟨hpJ, hpq⟩ := (mem_precedingPrimes J q p).mp hp
  let A := Localization.AtPrime q.asIdeal
  let a : Lower →+* A := algebraMap Lower A
  have hdisj : Disjoint (q.asIdeal.primeCompl : Set Lower) (p.asIdeal : Set Lower) :=
    Set.disjoint_left.mpr (fun _ hx hxp => hx (hpq hxp))
  have hcomap : (p.asIdeal.map a).under Lower = p.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A p.isPrime hdisj
  have hmin : p.asIdeal.map a ∈ (J.map a).minimalPrimes := by
    change p.asIdeal.map a ∈ (J.map (algebraMap Lower A)).minimalPrimes
    rw [IsLocalization.minimalPrimes_map q.asIdeal.primeCompl A, Set.mem_preimage, hcomap]
    exact hpJ
  change IsSMulRegular (A ⧸ J.map a) (a t) at hreg
  have hmin' : p.asIdeal.map a ∈ (Module.annihilator A (A ⧸ J.map a)).minimalPrimes := by
    rwa [Ideal.annihilator_quotient]
  refine ⟨fun ht => (hreg.notMem_of_mem_minimalPrimes hmin') (Ideal.mem_map_of_mem a ht), ?_⟩
  have htq : Ideal.span {t} ≤ q.asIdeal := le_sup_right.trans hq.le
  refine ⟨⟨q.isPrime, sup_le hpq htq⟩, ?_⟩
  intro s hs hsq
  exact hq.2 ⟨hs.1, sup_le (hpJ.le.trans (le_sup_left.trans hs.2))
    (le_sup_right.trans hs.2)⟩ hsq

private theorem pointPrime_injective : Function.Injective K1_13_7_4.pointPrime := by
  intro y z hyz
  have heq : pointIdeal y = pointIdeal z := congrArg PrimeSpectrum.asIdeal hyz
  funext i
  have hm : MvPolynomial.X i - MvPolynomial.C (y i) ∈ pointIdeal y := by
    simp [pointIdeal, RingHom.mem_ker]
  rw [heq] at hm
  have hz : z i - y i = 0 := by
    simpa [pointIdeal, RingHom.mem_ker] using hm
  exact (sub_eq_zero.mp hz).symm

/-- The length of a proper incidence, with zero for pairs with no proper cut. -/
private def step (p : PrimeSpectrum Lower) (t : Lower) (q : PrimeSpectrum Lower) : ℚ := by
  classical
  exact if t ∉ p.asIdeal ∧ q.asIdeal ∈ (cutIdeal p t).minimalPrimes
    then (localColength q (cutIdeal p t)).toNat else 0

private theorem step_nonneg (p : PrimeSpectrum Lower) (t : Lower) (q : PrimeSpectrum Lower) :
    0 ≤ step p t q := by
  unfold step
  split <;> positivity

private theorem step_bound (D : PrimeSpectrum Lower → ℚ) (hD : ∀ p, 0 ≤ D p)
    (p : PrimeSpectrum Lower) (t : Lower)
    (hpay : t ∉ p.asIdeal → ∀ qs : Finset (PrimeSpectrum Lower),
      (∀ q ∈ qs, q.asIdeal ∈ (cutIdeal p t).minimalPrimes) →
      (∀ q ∈ qs, localColength q (cutIdeal p t) < ⊤) →
      cutCost D p t qs ≤ D p)
    (qs : Finset (PrimeSpectrum Lower)) :
    ∑ q ∈ qs, step p t q * D q ≤ D p := by
  classical
  by_cases ht : t ∈ p.asIdeal
  · simpa [step, ht] using hD p
  let qs' := qs.filter (fun q => q.asIdeal ∈ (cutIdeal p t).minimalPrimes)
  have hmin : ∀ q ∈ qs', q.asIdeal ∈ (cutIdeal p t).minimalPrimes :=
    fun q hq => (Finset.mem_filter.mp hq).2
  simpa [qs', cutCost, Finset.sum_filter, step, ht, ite_mul] using
    hpay ht qs' hmin (fun q hq => K1_13_7_4.localColength_lt_top (hmin q hq))

private theorem step_formula (hassoc : c2)
    {J : Ideal Lower} {t : Lower} {q : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hreg : RegularCut q J t) :
    ((localColength q (J ⊔ Ideal.span {t})).toNat : ℚ) =
      ∑ p ∈ precedingPrimes J q, (localColength p J).toNat * step p t q := by
  classical
  rw [hassoc J t q hq hreg]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  simp [step, cut_of_preceding hq hreg hp]

/-- A marked local length is bounded by the sum of the chain weights ending there. -/
private theorem point_chain_bound (hregular : c1) (hassoc : c2)
    (f g h : Lower) (y : LowerPoint) (q : PrimeSpectrum Lower)
    (hy : q.asIdeal = pointIdeal y) (hq : q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes) :
    ((localColength q (Ideal.span {f, g, h})).toNat : ℚ) ≤
      ∑ r ∈ minPrimes (Ideal.span {f, g}),
        (∑ p ∈ minPrimes (Ideal.span {f}), step zeroPrime f p * step p g r) * step r h q := by
  classical
  obtain ⟨hf, hreg, hregs⟩ := hregular f g h y q hy hq
  have hzero : cutIdeal zeroPrime f = Ideal.span {f} := by simp [cutIdeal, zeroPrime]
  have hf' : f ∉ zeroPrime.asIdeal := by simpa [zeroPrime, Ideal.mem_bot] using hf
  rw [span_triple f g h] at hq ⊢
  rw [step_formula hassoc hq hreg]
  calc
    _ ≤ ∑ r ∈ precedingPrimes (Ideal.span {f, g}) q,
        (∑ p ∈ minPrimes (Ideal.span {f}), step zeroPrime f p * step p g r) * step r h q := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right _ (step_nonneg r h q)
      have hrmin := ((mem_precedingPrimes _ _ _).mp hr).1
      rw [span_pair f g] at hrmin ⊢
      rw [step_formula hassoc hrmin (hregs r hr)]
      have hstart (p : PrimeSpectrum Lower) (hp : p ∈ precedingPrimes (Ideal.span {f}) r) :
          ((localColength p (Ideal.span {f})).toNat : ℚ) = step zeroPrime f p := by
        have hpmin := ((mem_precedingPrimes _ _ _).mp hp).1
        simp [step, hf', hzero, hpmin]
      trans ∑ p ∈ precedingPrimes (Ideal.span {f}) r, step zeroPrime f p * step p g r
      · exact le_of_eq (Finset.sum_congr rfl fun p hp => by rw [hstart p hp])
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (mem_minPrimes _ _).mpr ((mem_precedingPrimes _ _ _).mp hp).1
      · intro p _ _
        exact mul_nonneg (step_nonneg zeroPrime f p) (step_nonneg p g r)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact (mem_minPrimes _ _).mpr ((mem_precedingPrimes _ _ _).mp hr).1
      · intro r _ _
        exact mul_nonneg (Finset.sum_nonneg fun p _ =>
          mul_nonneg (step_nonneg zeroPrime f p) (step_nonneg p g r)) (step_nonneg r h q)

theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_6.c2 := by
  classical
  intro f g h D hD hpoint hpay points w hmarks
  let ps := minPrimes (Ideal.span {f})
  let rs := minPrimes (Ideal.span {f, g})
  let qs := points.image K1_13_7_4.pointPrime
  have hcard : qs.card = points.card := Finset.card_image_of_injective _ pointPrime_injective
  have hq (q : PrimeSpectrum Lower) (hq : q ∈ qs) :
      (w : ℚ) ≤ ∑ r ∈ rs, (∑ p ∈ ps, step zeroPrime f p * step p g r) * (step r h q * D q) := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨q, hp, hm, hw, hfin⟩ := hmarks y hy
    have heq : q = K1_13_7_4.pointPrime y := PrimeSpectrum.ext_iff.mpr hp
    subst q
    refine le_trans ?_ (le_trans (point_chain_bound h1 h2 f g h y _ hp hm) ?_)
    · exact_mod_cast (by simpa only [ENat.toNat_natCast] using
        ENat.toNat_le_toNat hw hfin.ne : w ≤ (localColength
          (K1_13_7_4.pointPrime y) (Ideal.span {f, g, h})).toNat)
    · exact Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right (step_nonneg r h _) (hpoint y _ hp))
          (Finset.sum_nonneg fun p _ =>
            mul_nonneg (step_nonneg zeroPrime f p) (step_nonneg p g r))
  have budget (p : PrimeSpectrum Lower) (t : Lower)
      (ht : t ∈ ({f, g, h} : Set Lower)) (s : Finset (PrimeSpectrum Lower)) :
      ∑ q ∈ s, step p t q * D q ≤ D p :=
    step_bound D hD p t (hpay t ht p) s
  calc
    (points.card : ℚ) * w = ∑ _ ∈ qs, (w : ℚ) := by simp [hcard]
    _ ≤ ∑ q ∈ qs, ∑ r ∈ rs, (∑ p ∈ ps, step zeroPrime f p * step p g r) *
        (step r h q * D q) := Finset.sum_le_sum hq
    _ = ∑ r ∈ rs, (∑ p ∈ ps, step zeroPrime f p * step p g r) *
        (∑ q ∈ qs, step r h q * D q) := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ rs, (∑ p ∈ ps, step zeroPrime f p * step p g r) * D r := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left (budget r h (by simp) qs)
        (Finset.sum_nonneg fun p _ =>
          mul_nonneg (step_nonneg zeroPrime f p) (step_nonneg p g r))
    _ = ∑ p ∈ ps, step zeroPrime f p * (∑ r ∈ rs, step p g r * D r) := by
      simp_rw [Finset.sum_mul, mul_assoc, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ ps, step zeroPrime f p * D p := by
      exact Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (budget p g (by simp) rs) (step_nonneg zeroPrime f p)
    _ ≤ D zeroPrime := budget zeroPrime f (by simp) ps

end
end K1_13_7_6_2
end PackSource_K1_13_7_6_2Split

section PackSource_K1_13_7_6_2_1Coordinates
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6_2_1
noncomputable section

open K1_13_7 MvPolynomial

/-- A translated coordinate vanishing at the marked point. -/
def coordinate (y : LowerPoint) (i : Fin 3) : Lower := MvPolynomial.X i - C (y i)

private def prefixIdeal (y : LowerPoint) (n : ℕ) : Ideal Lower :=
  Ideal.span (coordinate y '' {i | i.val < n})

private def specialize (y : LowerPoint) (n : ℕ) : Lower →+* Lower :=
  eval₂Hom C (fun i => if i.val < n then C (y i) else MvPolynomial.X i)

private theorem ker_specialize (y : LowerPoint) (n : ℕ) :
    RingHom.ker (specialize y n) = prefixIdeal y n := by
  let I := prefixIdeal y n
  have hmk : (Ideal.Quotient.mk I).comp (specialize y n) = Ideal.Quotient.mk I := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [specialize]
    · intro i
      simp only [RingHom.comp_apply, specialize, eval₂Hom_X']
      split_ifs with hi
      · have hm : coordinate y i ∈ I := Ideal.subset_span ⟨i, hi, rfl⟩
        have he := (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr hm
        rw [coordinate, map_sub, sub_eq_zero] at he
        exact he.symm
      · rfl
  apply le_antisymm
  · intro f hf
    apply (Ideal.Quotient.eq_zero_iff_mem (I := I)).mp
    have he := DFunLike.congr_fun hmk f
    change Ideal.Quotient.mk I (specialize y n f) = Ideal.Quotient.mk I f at he
    rw [RingHom.mem_ker.mp hf, map_zero] at he
    exact he.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i.val < n := hi
    simp [RingHom.mem_ker, coordinate, specialize, hi']

private instance prefixIdeal_prime (y : LowerPoint) (n : ℕ) :
    (prefixIdeal y n).IsPrime := by
  rw [← ker_specialize]
  exact RingHom.ker_isPrime _

private theorem coordinate_ne_zero (y : LowerPoint) (i : Fin 3) :
    coordinate y i ≠ 0 := by
  intro he
  have he' := congrArg (MvPolynomial.eval (fun _ => y i + 1)) he
  simp [coordinate] at he'

private theorem coordinate_notMem (y : LowerPoint) (i : Fin 3) {n : ℕ}
    (hi : n ≤ i.val) : coordinate y i ∉ prefixIdeal y n := by
  rw [← ker_specialize, RingHom.mem_ker]
  simpa [specialize, coordinate, not_lt.mpr hi] using coordinate_ne_zero y i

private theorem prefixIdeal_succ (y : LowerPoint) (i : Fin 3) :
    prefixIdeal y (i.val + 1) = Ideal.span {coordinate y i} ⊔ prefixIdeal y i.val := by
  rw [prefixIdeal, prefixIdeal, ← Ideal.span_insert]
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    change j.val < i.val + 1 at hj
    by_cases hji : j = i
    · exact Or.inl (congrArg (coordinate y) hji)
    · have hv : j.val ≠ i.val := fun he => hji (Fin.ext he)
      exact Or.inr ⟨j, (show j.val < i.val by omega), rfl⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨i, Nat.lt_succ_self _, rfl⟩
    · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩

private theorem prefixIdeal_lt_succ (y : LowerPoint) (i : Fin 3) :
    prefixIdeal y i.val < prefixIdeal y (i.val + 1) := by
  rw [prefixIdeal_succ]
  refine lt_of_le_of_ne le_sup_right ?_
  intro he
  apply coordinate_notMem y i le_rfl
  rw [he]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

private theorem prefixIdeal_three (y : LowerPoint) :
    prefixIdeal y 3 = pointIdeal y := by
  have he : specialize y 3 = C.comp (eval y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [specialize]
    · intro i
      simp [specialize]
  rw [← ker_specialize, he, pointIdeal]
  ext p
  simp [RingHom.mem_ker]

/-- The translated coordinate ideals form a chain of length three. -/
theorem point_height_lower (y : LowerPoint) : 3 ≤ (pointIdeal y).height := by
  have h0 := Ideal.height_add_one_le_of_lt_of_isPrime (prefixIdeal_lt_succ y 0)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (prefixIdeal_lt_succ y 1)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (prefixIdeal_lt_succ y 2)
  change (prefixIdeal y 0).height + 1 ≤ (prefixIdeal y 1).height at h0
  change (prefixIdeal y 1).height + 1 ≤ (prefixIdeal y 2).height at h1
  change (prefixIdeal y 2).height + 1 ≤ (prefixIdeal y 3).height at h2
  rw [← prefixIdeal_three]
  calc
    (3 : ℕ∞) = ((0 : ℕ∞) + 1) + 1 + 1 := by norm_num
    _ ≤ (prefixIdeal y 1).height + 1 + 1 :=
      add_le_add (add_le_add ((add_le_add (zero_le : 0 ≤ (prefixIdeal y 0).height) le_rfl).trans h0) le_rfl) le_rfl
    _ ≤ (prefixIdeal y 2).height + 1 := add_le_add h1 le_rfl
    _ ≤ (prefixIdeal y 3).height := h2

/-- Each localized coordinate ideal is prime and avoids the next coordinate. -/
private theorem localized_prefix (y : LowerPoint) (q : PrimeSpectrum Lower)
    (hy : q.asIdeal = pointIdeal y) (i : Fin 3) :
    let A := Localization.AtPrime q.asIdeal
    let a := algebraMap Lower A
    let I := (prefixIdeal y i.val).map a
    I.IsPrime ∧ a (coordinate y i) ∉ I := by
  dsimp only
  let A := Localization.AtPrime q.asIdeal
  let a := algebraMap Lower A
  let J := prefixIdeal y i.val
  have hle : J ≤ q.asIdeal := by
    rw [hy, ← prefixIdeal_three]
    apply Ideal.span_mono
    rintro _ ⟨j, _, rfl⟩
    exact ⟨j, j.isLt, rfl⟩
  have hd : Disjoint (q.asIdeal.primeCompl : Set Lower) (J : Set Lower) :=
    Set.disjoint_left.mpr (fun _ hx hz => hx (hle hz))
  refine ⟨IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl A J
    (prefixIdeal_prime y i.val) hd, ?_⟩
  have he := IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A
    (prefixIdeal_prime y i.val) hd
  change coordinate y i ∉ (J.map a).under Lower
  rw [he]
  exact coordinate_notMem y i le_rfl

/-- The three coordinates are regular in succession at the marked point. -/
theorem localized_coordinates (y : LowerPoint) (q : PrimeSpectrum Lower)
    (hy : q.asIdeal = pointIdeal y) :
    let A := Localization.AtPrime q.asIdeal
    let a := algebraMap Lower A
    let u := a (coordinate y 0)
    let v := a (coordinate y 1)
    let w := a (coordinate y 2)
    u ≠ 0 ∧ (Ideal.span {u}).IsPrime ∧ v ∉ Ideal.span {u} ∧
      (Ideal.span {u, v}).IsPrime ∧ w ∉ Ideal.span {u, v} := by
  dsimp only
  have h0 : prefixIdeal y 0 = ⊥ := by simp [prefixIdeal]
  have h1 : prefixIdeal y 1 = Ideal.span {coordinate y 0} := by
    have h := prefixIdeal_succ y 0
    change prefixIdeal y 1 = _ ⊔ prefixIdeal y 0 at h
    simpa [h0] using h
  have h2 : prefixIdeal y 2 = Ideal.span {coordinate y 0, coordinate y 1} := by
    have h := prefixIdeal_succ y 1
    change prefixIdeal y 2 = _ ⊔ prefixIdeal y 1 at h
    rw [h, h1, Ideal.span_insert, sup_comm]
  have hp1 := localized_prefix y q hy 1
  have hp2 := localized_prefix y q hy 2
  dsimp only at hp1 hp2
  change ((prefixIdeal y 1).map _).IsPrime ∧ _ ∉ (prefixIdeal y 1).map _ at hp1
  change ((prefixIdeal y 2).map _).IsPrime ∧ _ ∉ (prefixIdeal y 2).map _ at hp2
  rw [h1, Ideal.map_span, Set.image_singleton] at hp1
  rw [h2, Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at hp2
  refine ⟨?_, hp1.1, hp1.2, hp2.1, hp2.2⟩
  simpa only [map_zero] using (IsLocalization.injective (Localization.AtPrime q.asIdeal)
    q.asIdeal.primeCompl_le_nonZeroDivisors).ne (coordinate_ne_zero y 0)

end
end K1_13_7_6_2_1
end PackSource_K1_13_7_6_2_1Coordinates

section PackSource_K1_13_7_6_2_2Prime
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6_2_2

noncomputable section

open K1_13_7 K1_13_7_6 K1_13_7_6_2
open scoped Classical

private theorem cut_minimal {J : Ideal Lower} {t : Lower} {q p : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hJp : J ≤ p.asIdeal) (hpq : p.asIdeal ≤ q.asIdeal) :
    q.asIdeal ∈ (cutIdeal p t).minimalPrimes := by
  have htq : Ideal.span {t} ≤ q.asIdeal := le_sup_right.trans hq.le
  refine ⟨⟨q.isPrime, sup_le hpq htq⟩, ?_⟩
  intro s hs hsq
  exact hq.2 ⟨hs.1, sup_le (hJp.trans (le_sup_left.trans hs.2))
    (le_sup_right.trans hs.2)⟩ hsq

/-- In the quotient by a prime, the principal ideal theorem leaves no
prime strictly between zero and a minimal prime of the principal cut. -/
private theorem eq_of_prime_between {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P I Q : Ideal R} {t : R} (hP : P.IsPrime) (hI : I.IsPrime)
    (hQ : Q ∈ (P ⊔ Ideal.span {t}).minimalPrimes) (hPI : P ≤ I) (hIQ : I ≤ Q)
    (hne : I ≠ Q) : I = P := by
  let f : R →+* R ⧸ P := Ideal.Quotient.mk P
  have := hQ.isPrime
  have hPQ := hPI.trans hIQ
  have hh : (Q.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have : (Q.map f).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have hi : (I.map f).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPI
  have hlt : I.map f < Q.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hIQ) fun he => hne ?_
    calc
      I = (I.map f).comap f := (Ideal.comap_map_mk hPI).symm
      _ = (Q.map f).comap f := congrArg (Ideal.comap f) he
      _ = Q := Ideal.comap_map_mk hPQ
  have hz := (Ideal.height_le_iff (n := 1)).mp hh (I.map f) hi hlt
  have hbot := Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp hz)
  calc
    I = (I.map f).comap f := (Ideal.comap_map_mk hPI).symm
    _ = RingHom.ker f := by rw [hbot, RingHom.ker_eq_comap_bot]
    _ = P := Ideal.mk_ker

private theorem prime_below_cut {J : Ideal Lower} {t : Lower} {q r : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hJr : J ≤ r.asIdeal) (hrq : r.asIdeal ≤ q.asIdeal) :
    r = q ∨ r ∈ precedingPrimes J q := by
  by_cases h : r = q
  · exact Or.inl h
  right
  obtain ⟨P, hP, hPr⟩ := Ideal.exists_minimalPrimes_le hJr
  let p : PrimeSpectrum Lower := ⟨P, hP.isPrime⟩
  have hpq : q.asIdeal ∈ (P ⊔ Ideal.span {t}).minimalPrimes :=
    cut_minimal (p := p) hq hP.le (hPr.trans hrq)
  have he : r.asIdeal = P := eq_of_prime_between hP.isPrime r.isPrime hpq hPr hrq
    (fun he => h (PrimeSpectrum.ext_iff.mpr he))
  exact (mem_precedingPrimes J q r).mpr ⟨he.symm ▸ hP, hrq⟩

private theorem cut_regular_on_prime {J : Ideal Lower} {t : Lower}
    {q p : PrimeSpectrum Lower} (hreg : RegularCut q J t)
    (hp : p ∈ precedingPrimes J q) :
    IsSMulRegular (At q ⧸ p.asIdeal.map (algebraMap Lower (At q))) (algebraMap Lower (At q) t) := by
  obtain ⟨hpJ, hpq⟩ := (mem_precedingPrimes J q p).mp hp
  let A := At q
  let a := algebraMap Lower A
  let Q := p.asIdeal.map a
  have hdisj : Disjoint (q.asIdeal.primeCompl : Set Lower) (p.asIdeal : Set Lower) :=
    Set.disjoint_left.mpr (fun _ hx hxp => hx (hpq hxp))
  let : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl A p.asIdeal p.isPrime hdisj
  have hcomap : Q.under Lower = p.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A p.isPrime hdisj
  have hmin : Q ∈ (J.map a).minimalPrimes := by
    change Q ∈ (J.map (algebraMap Lower A)).minimalPrimes
    rw [IsLocalization.minimalPrimes_map q.asIdeal.primeCompl A, Set.mem_preimage, hcomap]
    exact hpJ
  change IsSMulRegular (A ⧸ J.map a) (a t) at hreg
  have hmin' : Q ∈ (Module.annihilator A (A ⧸ J.map a)).minimalPrimes := by
    rwa [Ideal.annihilator_quotient]
  have ha : Ideal.Quotient.mk Q (a t) ≠ 0 :=
    fun he => (hreg.notMem_of_mem_minimalPrimes hmin') (Ideal.Quotient.eq_zero_iff_mem.mp he)
  change IsSMulRegular (A ⧸ Q) (a t)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  exact (mul_eq_zero.mp (show Ideal.Quotient.mk Q (a t) * x = 0 from hx)).resolve_left ha

theorem locLength_at_preceding {J : Ideal Lower} {q p r : PrimeSpectrum Lower}
    (hp : p ∈ precedingPrimes J q) (hr : J ≤ r.asIdeal) :
    locLength p (Lower ⧸ r.asIdeal) = if r = p then 1 else 0 := by
  classical
  by_cases he : r = p
  · subst r
    simpa using locLength_prime_self p
  rw [ite_eq_right he]
  apply locLength_prime_away
  intro hrp
  have hm := ((mem_precedingPrimes J q p).mp hp).1
  have hle : p.asIdeal ≤ r.asIdeal := hm.2 ⟨r.isPrime, hr⟩ hrp
  exact he (PrimeSpectrum.ext_iff.mpr (hrp.antisymm hle))

theorem cut_prime_factor {J : Ideal Lower} {t : Lower} {q r : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hreg : RegularCut q J t) (hr : J ≤ r.asIdeal) :
    CutFinite (algebraMap Lower (At q) t) (Loc q (Lower ⧸ r.asIdeal)) ∧
      cutEuler (algebraMap Lower (At q) t) (Loc q (Lower ⧸ r.asIdeal)) =
        if r ∈ precedingPrimes J q then ((localColength q (cutIdeal r t)).toNat : ℤ) else 0 := by
  classical
  by_cases hp : r ∈ precedingPrimes J q
  · rw [ite_eq_left hp]
    exact cut_regular q r.asIdeal t (cut_regular_on_prime hreg hp)
      (K1_13_7_4.localColength_lt_top (cut_minimal (p := r) hq hr ((mem_precedingPrimes J q r).mp hp).2))
  rw [ite_eq_right hp]
  apply cut_of_finite_length
  change locLength q (Lower ⧸ r.asIdeal) < ⊤
  by_cases hrq : r.asIdeal ≤ q.asIdeal
  · rcases prime_below_cut hq hr hrq with h | h
    · subst r
      simp [locLength_prime_self]
    · exact (hp h).elim
  · simp [locLength_prime_away hrq]

end
end K1_13_7_6_2_2
end PackSource_K1_13_7_6_2_2Prime

section PackSource_K1_13_7_6_2_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6_2_1
noncomputable section

open K1_13_7 K1_13_7_6_2

local instance : GCDMonoid Lower := UniqueFactorizationMonoid.toGCDMonoid Lower

private theorem not_minimal_pair {q : Ideal Lower} (hq : 3 ≤ q.height) (a b : Lower) :
    q ∉ (Ideal.span {a, b}).minimalPrimes := by
  intro hp
  have hn : ({a, b} : Set Lower).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  have hle : q.height ≤ 2 :=
    (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hp).trans (by exact_mod_cast hn)
  exact (by norm_num : ¬ (3 : ℕ∞) ≤ 2) (hq.trans hle)

private theorem gcd_avoids {f g h : Lower} {q : PrimeSpectrum Lower}
    (hh : 3 ≤ q.asIdeal.height) (hq : q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes) :
    gcd f g ∉ q.asIdeal := by
  intro hd
  apply not_minimal_pair hh (gcd f g) h
  have ht : h ∈ q.asIdeal := hq.le (Ideal.subset_span (by simp))
  refine ⟨⟨q.isPrime, Ideal.span_le.mpr ?_⟩, ?_⟩
  · simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hd, ht⟩
  intro p hp hpq
  have hdp : gcd f g ∈ p := hp.2 (Ideal.subset_span (by simp))
  have hhp : h ∈ p := hp.2 (Ideal.subset_span (by simp))
  have hfp : f ∈ p := by
    obtain ⟨k, hk⟩ := gcd_dvd_left f g
    rw [hk]
    exact p.mul_mem_right _ hdp
  have hgp : g ∈ p := by
    obtain ⟨k, hk⟩ := gcd_dvd_right f g
    rw [hk]
    exact p.mul_mem_right _ hdp
  apply hq.2 ⟨hp.1, Ideal.span_le.mpr ?_⟩ hpq
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hfp, hgp, hhp⟩

/-- A global gcd outside a prime becomes a unit there, so the second cut is regular. -/
private theorem regular_pair (p : PrimeSpectrum Lower) {f g : Lower}
    (hd : gcd f g ∉ p.asIdeal) : RegularCut p (Ideal.span {f}) g := by
  let A := Localization.AtPrime p.asIdeal
  let a := algebraMap Lower A
  let J : Ideal Lower := Ideal.span {f}
  change IsSMulRegular (A ⧸ J.map a) (a g)
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (J.map a) (a g)).mpr
  intro z hz
  change a g * z ∈ J.map a at hz
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl z
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff] at hz
  obtain ⟨t, ht, htx⟩ := hz
  rw [← mul_left_comm g t x, Ideal.mem_span_singleton] at htx
  have hdx : t * (gcd f g * x) ∈ J := by
    change t * (gcd f g * x) ∈ Ideal.span {f}
    rw [mul_left_comm t, Ideal.mem_span_singleton]
    exact dvd_gcd_mul_of_dvd_mul htx
  have hmem : a (gcd f g) * IsLocalization.mk' A x s ∈ J.map a := by
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨t, ht, hdx⟩
  exact ((J.map a).unit_mul_mem_iff_mem
    (IsLocalization.map_units A (⟨gcd f g, hd⟩ : p.asIdeal.primeCompl))).mp hmem

/-- The two-generator syzygy for a regular pair. -/
private theorem pair_syzygy {A : Type*} [CommRing A] [IsDomain A]
    {f g : A} (hf : f ≠ 0) (hg : IsSMulRegular (A ⧸ Ideal.span {f}) g)
    {a b : A} (hab : f * a + g * b = 0) :
    ∃ c : A, a = g * c ∧ b = -(f * c) := by
  have hm : g * b ∈ Ideal.span {f} := by
    have he : g * b = f * (-a) := by linear_combination hab
    rw [he]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right f (-a))
  have hb : f ∣ b := Ideal.mem_span_singleton.mp
    (mem_of_isSMulRegular_quotient_of_smul_mem hg hm)
  obtain ⟨k, hk⟩ := hb
  refine ⟨-k, mul_left_cancel₀ hf ?_, by rw [hk]; ring⟩
  linear_combination hab - g * hk

/-- A regular pair quotient has no nonzero class killed by these three coordinates. -/
private theorem no_coordinate_socle {A : Type*} [CommRing A] [IsDomain A]
    {u v w f g z : A} (hu : u ≠ 0)
    (hU : (Ideal.span ({u} : Set A)).IsPrime) (hv : v ∉ Ideal.span {u})
    (hUV : (Ideal.span ({u, v} : Set A)).IsPrime) (hw : w ∉ Ideal.span {u, v})
    (hf : f ≠ 0) (hg : IsSMulRegular (A ⧸ Ideal.span {f}) g)
    (hz0 : u * z ∈ Ideal.span {f, g}) (hz1 : v * z ∈ Ideal.span {f, g})
    (hz2 : w * z ∈ Ideal.span {f, g}) :
    z ∈ Ideal.span {f, g} := by
  obtain ⟨a0, b0, h0⟩ := Ideal.mem_span_pair.mp hz0
  obtain ⟨a1, b1, h1⟩ := Ideal.mem_span_pair.mp hz1
  obtain ⟨a2, b2, h2⟩ := Ideal.mem_span_pair.mp hz2
  obtain ⟨c01, ha01, hb01⟩ := pair_syzygy hf hg
    (a := u * a1 - v * a0) (b := u * b1 - v * b0) (by
      linear_combination u * h1 - v * h0)
  obtain ⟨c02, _, hb02⟩ := pair_syzygy hf hg
    (a := u * a2 - w * a0) (b := u * b2 - w * b0) (by
      linear_combination u * h2 - w * h0)
  obtain ⟨c12, _, hb12⟩ := pair_syzygy hf hg
    (a := v * a2 - w * a1) (b := v * b2 - w * b1) (by
      linear_combination v * h2 - w * h1)
  -- Alternating the three syzygies forces the first coefficient into (u,v).
  have hc : u * c12 - v * c02 + w * c01 = 0 := by
    apply mul_left_cancel₀ hf
    linear_combination u * hb12 - v * hb02 + w * hb01
  have hwc : w * c01 ∈ Ideal.span {u, v} :=
    Ideal.mem_span_pair.mpr ⟨-c12, c02, by linear_combination -hc⟩
  have hc' := (hUV.mem_or_mem hwc).resolve_left hw
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hc'
  have div_first {x y : A} (he : u * y = v * x) : u ∣ x := by
    have hm : v * x ∈ Ideal.span {u} := he ▸
      Ideal.mem_span_singleton.mpr (dvd_mul_right u y)
    exact Ideal.mem_span_singleton.mp ((hU.mem_or_mem hm).resolve_left hv)
  -- Subtract a pair syzygy from the coefficients of u*z to make them divisible by u.
  obtain ⟨a, ha⟩ := div_first (x := a0 + g * d) (y := a1 - g * c)
    (by linear_combination ha01 - g * hcd)
  obtain ⟨b, hb⟩ := div_first (x := b0 - f * d) (y := b1 + f * c)
    (by linear_combination hb01 + f * hcd)
  refine Ideal.mem_span_pair.mpr ⟨a, b, mul_left_cancel₀ hu ?_⟩
  linear_combination h0 - f * ha - g * hb

private theorem regular_third {f g h : Lower} {y : LowerPoint} {q : PrimeSpectrum Lower}
    (hy : q.asIdeal = pointIdeal y) (hf : f ≠ 0)
    (hg : RegularCut q (Ideal.span {f}) g)
    (hq : q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes) :
    RegularCut q (Ideal.span {f, g}) h := by
  let A := Localization.AtPrime q.asIdeal
  let a := algebraMap Lower A
  let F := a f
  let G := a g
  let H := a h
  let J : Ideal A := Ideal.span {F, G}
  have hMapPair : (Ideal.span ({f, g} : Set Lower)).map a = J := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change IsSMulRegular (A ⧸ (Ideal.span {f, g}).map a) H
  rw [hMapPair]
  change IsSMulRegular (A ⧸ (Ideal.span {f}).map a) G at hg
  rw [Ideal.map_span, Set.image_singleton] at hg
  have hF : F ≠ 0 := by
    simpa only [map_zero] using
      (IsLocalization.injective A q.asIdeal.primeCompl_le_nonZeroDivisors).ne hf
  have hrad : (Ideal.span ({F, G, H} : Set A)).radical = IsLocalRing.maximalIdeal A := by
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal A] using
      (IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := A) q.asIdeal
        (Ideal.span {f, g, h}) hq)
  by_contra hn
  have hmem : H ∈ ⋃ p ∈ associatedPrimes A (A ⧸ J), (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hn
  obtain ⟨p, hp, hH⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨hpPrime, x, hx⟩ := isAssociatedPrime_iff.mp hp
  have hJ : J ≤ p := by
    rw [← Ideal.annihilator_quotient (I := J)]
    intro t ht
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact Module.mem_annihilator.mp ht x
  have hmp : IsLocalRing.maximalIdeal A ≤ p := by
    rw [← hrad, ← hpPrime.radical]
    apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hJ (Ideal.subset_span (by simp)), hJ (Ideal.subset_span (by simp)), hH⟩
  have hxne : x ≠ 0 := by
    intro he
    exact hpPrime.ne_top' (by simp [hx, he, Submodule.colon_singleton_zero])
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hz (i : Fin 3) : a (coordinate y i) * z ∈ J := by
    have hm : a (coordinate y i) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal A]
      apply Ideal.mem_map_of_mem
      rw [hy]
      simp [coordinate, pointIdeal, RingHom.mem_ker]
    have hp' := hmp hm
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot] at hp'
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    exact hp'
  obtain ⟨hu, hU, hv, hUV, hw⟩ := localized_coordinates y q hy
  exact hxne (Ideal.Quotient.eq_zero_iff_mem.mpr
    (no_coordinate_socle hu hU hv hUV hw hF hg (hz 0) (hz 1) (hz 2)))

/-- At an isolated geometric point all three cuts are locally regular in order. -/
theorem proof : K1_13_7_6_2.c1 := by
  intro f g h y q hy hq
  have hh : 3 ≤ q.asIdeal.height := hy.symm ▸ point_height_lower y
  have hf : f ≠ 0 := by
    intro he
    subst f
    exact not_minimal_pair hh g h (by simpa only [Ideal.span_insert_zero] using hq)
  have hd := gcd_avoids hh hq
  refine ⟨hf, regular_third hy hf (regular_pair q hd) hq, ?_⟩
  intro r hr
  have hrq := ((mem_precedingPrimes _ _ _).mp hr).2
  exact regular_pair r (fun hm => hd (hrq hm))

end
end K1_13_7_6_2_1
end PackSource_K1_13_7_6_2_1Proof

section PackSource_K1_13_7_6_2_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6_2_2

noncomputable section

open K1_13_7 K1_13_7_6 K1_13_7_6_2
open scoped BigOperators

private def cutWeight (q : PrimeSpectrum Lower) (t : Lower) (p : PrimeSpectrum Lower) : ℤ :=
  (localColength q (cutIdeal p t)).toNat

/-- Compute the Euler characteristic by prime-filtration induction. The lengths at
the surviving minimal primes count the occurrences of their cyclic factors. -/
private theorem module_formula {J : Ideal Lower} {t : Lower} {q : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hreg : RegularCut q J t)
    (M : Type) [AddCommGroup M] [Module Lower M] [Module.Finite Lower M]
    (hJ : J ≤ Module.annihilator Lower M) :
    CutFinite (algebraMap Lower (At q) t) (Loc q M) ∧
      (∀ p ∈ precedingPrimes J q, locLength p M < ⊤) ∧
      cutEuler (algebraMap Lower (At q) t) (Loc q M) =
        ∑ p ∈ precedingPrimes J q, (locLength p M).toNat * cutWeight q t p := by
  classical
  let u := algebraMap Lower (At q) t
  revert hJ
  induction (inferInstance : Module.Finite Lower M) using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime Lower with
  | subsingleton N =>
    intro _
    have h (p : PrimeSpectrum Lower) : locLength p N = 0 := Module.length_eq_zero
    have hz := cut_of_finite_length u (show locLength q N < ⊤ by simp [h])
    refine ⟨hz.1, fun p _ => by simp [h], ?_⟩
    simpa [h] using hz.2
  | quotient N r e =>
    intro hJ
    rw [e.annihilator_eq, Ideal.annihilator_quotient] at hJ
    let E (p : PrimeSpectrum Lower) : Loc p N ≃ₗ[At p] Loc p (Lower ⧸ r.asIdeal) :=
      IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (Lower ⧸ r.asIdeal)) (At p) e
    have hw (p : PrimeSpectrum Lower) (hp : p ∈ precedingPrimes J q) :
        locLength p N = if r = p then 1 else 0 :=
      (E p).length_eq.trans (locLength_at_preceding hp hJ)
    have hc := cut_prime_factor hq hreg hJ
    have he := cut_congr u (E q)
    refine ⟨he.1.mpr hc.1, fun p hp => by rw [hw p hp]; split <;> simp, ?_⟩
    rw [he.2, hc.2]
    by_cases hr : r ∈ precedingPrimes J q
    · rw [ite_eq_left hr, Finset.sum_eq_single r]
      · simp [hw r hr, cutWeight]
      · intro p hp hpr
        simp [hw p hp, Ne.symm hpr]
      · exact fun h => (h hr).elim
    · rw [ite_eq_right hr, Finset.sum_eq_zero]
      intro p hp
      have hne : r ≠ p := fun h => hr (h ▸ hp)
      simp [hw p hp, hne]
  | exact N₁ N₂ N₃ f g hf hg hfg ih₁ ih₃ =>
    intro hJ
    have h₁ := ih₁ (hJ.trans (f.annihilator_le_of_injective hf))
    have h₃ := ih₃ (hJ.trans (g.annihilator_le_of_surjective hg))
    have hex (p : PrimeSpectrum Lower) :
        Function.Exact (LocalizedModule.map p.asIdeal.primeCompl f)
          (LocalizedModule.map p.asIdeal.primeCompl g) :=
      LocalizedModule.map_exact p.asIdeal.primeCompl f g hfg
    have hl (p : PrimeSpectrum Lower) : locLength p N₂ = locLength p N₁ + locLength p N₃ :=
      Module.length_eq_add_of_exact _ _
        (LocalizedModule.map_injective p.asIdeal.primeCompl f hf)
        (LocalizedModule.map_surjective p.asIdeal.primeCompl g hg) (hex p)
    have hc := cut_add u _ _ (LocalizedModule.map_injective q.asIdeal.primeCompl f hf)
      (LocalizedModule.map_surjective q.asIdeal.primeCompl g hg) (hex q) h₁.1 h₃.1
    refine ⟨hc.1, fun p hp => (hl p).symm ▸ ENat.add_lt_top.mpr ⟨h₁.2.1 p hp, h₃.2.1 p hp⟩, ?_⟩
    rw [hc.2, h₁.2.2, h₃.2.2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hl p, ENat.toNat_add (h₁.2.1 p hp).ne (h₃.2.1 p hp).ne, Nat.cast_add, add_mul]

theorem proof : K1_13_7_6_2.c2 := by
  intro J t q hq hreg
  have hm := module_formula hq hreg (Lower ⧸ J)
    (show J ≤ Module.annihilator Lower (Lower ⧸ J) by rw [Ideal.annihilator_quotient])
  have hc := cut_regular q J t hreg (K1_13_7_4.localColength_lt_top hq)
  have h := hm.2.2
  rw [hc.2] at h
  simp only [locLength_quotient, cutWeight] at h
  exact_mod_cast h

end
end K1_13_7_6_2_2
end PackSource_K1_13_7_6_2_2Proof

section PackSource_K1_14_2_3_2Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_2_3_2

open K1_14_2 K1_14_2_3

/-- The generic seed-line slices retain the inclusions of the contracted
coordinate rings. A nonzero generic slice of the prime jet ring is a domain. -/
def c1 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime → Nontrivial (JetSeedSection I) →
    IsDomain (JetSeedSection I) ∧
      ∃ (f : PlaneSeedSection (seedImage I) →ₐ[SeedField] RootSeedSection (rootImage I))
        (j : RootSeedSection (rootImage I) →ₐ[SeedField] JetSeedSection I),
        Function.Injective f ∧ Function.Injective j

/-- A generic Y slice preserves the injection from the contracted ring. -/
def c2 : Prop :=
  ∀ I : Ideal Ambient,
    ∃ j : RootYSection (rootImage I) →ₐ[SeedField] JetYSection I, Function.Injective j

theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_3.c2 :=
  assemble h1 plane_degree h2

end K1_14_2_3_2
end PackSource_K1_14_2_3_2Split

section PackSource_K1_14_2_3_2_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_3_2_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_3 K1_14_2_3_1
open scoped Polynomial

local instance (n : ℕ) (I : Ideal (Raw n)) : CommRing (CoordinateRing I)[X] :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)

/-- Every section element is a polynomial in the free slope and the original
coordinates, divided by a nonzero coefficient from the parameter ring. -/
private theorem clear_denominator {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    (x : Slice I i j) :
    ∃ (q : (CoordinateRing I)[X]) (d : SeedField), d ≠ 0 ∧
      x * algebraMap SeedField (Slice I i j) d = slopeToSlice I i j q := by
  let : Algebra (MvPolynomial (Fin n) Seeds) (Over n) := MvPolynomial.algebraMvPolynomial
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨g, m⟩, hgm⟩ := IsLocalization.surj
    (M := (nonZeroDivisors Seeds).map (MvPolynomial.C (σ := Fin n))) f
  obtain ⟨d, hd, hdm⟩ := m.property
  let lift : MvPolynomial (Fin n) Seeds →+* (CoordinateRing I)[X] :=
    MvPolynomial.eval₂Hom (parameterMap I i j) (fun k => Polynomial.C (coord I k))
  have hcomp : (slopeToSlice I i j).comp lift =
      (Ideal.Quotient.mk (sectionIdeal I i j)).comp
        (MvPolynomial.map (algebraMap Seeds SeedField)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, lift, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact RingHom.congr_fun (parameter_commutes I i j) a
    · intro k
      simp [lift, slopeToSlice, toSlice, RingHom.comp_apply]
  refine ⟨lift g, algebraMap Seeds SeedField d, ?_, ?_⟩
  · exact fun h => mem_nonZeroDivisors_iff_ne_zero.mp hd
      (IsFractionRing.injective Seeds SeedField (h.trans (map_zero _).symm))
  · have hgm' : f * MvPolynomial.C (algebraMap Seeds SeedField d) =
        MvPolynomial.map (algebraMap Seeds SeedField) g := by
      simpa only [MvPolynomial.algebraMap_def, ← hdm, MvPolynomial.map_C] using hgm
    calc
      _ = Ideal.Quotient.mk (sectionIdeal I i j)
          (f * MvPolynomial.C (algebraMap Seeds SeedField d)) := (map_mul _ _ _).symm
      _ = _ := (congrArg (Ideal.Quotient.mk (sectionIdeal I i j)) hgm').trans
        (RingHom.congr_fun hcomp g).symm

private theorem cancel_denominator {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    {x : Slice I i j} {d : SeedField} (hd : d ≠ 0)
    (h : x * algebraMap SeedField (Slice I i j) d = 0) : x = 0 :=
  ((isUnit_iff_ne_zero.mpr hd).map (algebraMap SeedField (Slice I i j))).mul_right_cancel
    (h.trans (zero_mul _).symm)

/-- Clear denominators before using the domain property of the unsliced
coordinate ring with a free slope. -/
private theorem slice_isDomain {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] : IsDomain (Slice I i j) := by
  let : NoZeroDivisors (Slice I i j) := by
    constructor
    intro x y hxy
    obtain ⟨q, d, hd, hq⟩ := clear_denominator I i j x
    obtain ⟨r, e, he, hr⟩ := clear_denominator I i j y
    let d' : Slice I i j := algebraMap SeedField (Slice I i j) d
    let e' : Slice I i j := algebraMap SeedField (Slice I i j) e
    have hqr : slopeToSlice I i j (q * r) = 0 := calc
      _ = slopeToSlice I i j q * slopeToSlice I i j r := map_mul _ q r
      _ = (x * d') * (y * e') := congrArg₂ (· * ·) hq.symm hr.symm
      _ = (x * y) * (d' * e') := mul_mul_mul_comm x d' y e'
      _ = 0 := by rw [hxy, zero_mul]
    have hz : q * r = 0 := slope_injective I i j (hqr.trans (map_zero _).symm)
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (cancel_denominator I i j hd (by simpa only [h, map_zero] using hq))
    · exact Or.inr (cancel_denominator I i j he (by simpa only [h, map_zero] using hr))
  exact NoZeroDivisors.to_isDomain _

private abbrev extendCoeffs (n : ℕ) : Raw n →+* Over n :=
  MvPolynomial.map (algebraMap FX SeedField)

private abbrev contraction {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m)) :
    Ideal (Raw n) :=
  I.comap (MvPolynomial.rename e).toRingHom

private theorem rename_coeffs {n m : ℕ} (e : Fin n → Fin m) :
    ((MvPolynomial.rename e : Over n →ₐ[SeedField] Over m).toRingHom).comp
        (extendCoeffs n) =
      (extendCoeffs m).comp (MvPolynomial.rename e : Raw n →ₐ[FX] Raw m).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply]
  · intro k
    simp [RingHom.comp_apply]

private theorem sectionIdeal_le {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m))
    (i j : Fin n) :
    sectionIdeal (contraction e I) i j ≤
      (sectionIdeal I (e i) (e j)).comap (MvPolynomial.rename e : Over n →ₐ[SeedField] Over m) := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
  · intro p hp
    change (((MvPolynomial.rename e : Over n →ₐ[SeedField] Over m).toRingHom).comp
      (extendCoeffs n)) p ∈ sectionIdeal I (e i) (e j)
    rw [rename_coeffs]
    exact (show I.map (extendCoeffs m) ≤ sectionIdeal I (e i) (e j) from le_sup_left)
      (Ideal.mem_map_of_mem (extendCoeffs m) hp)
  · intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change MvPolynomial.rename e (seedLine i j) ∈ sectionIdeal I (e i) (e j)
    have h : MvPolynomial.rename e (seedLine i j) = seedLine (e i) (e j) := by
      simp [seedLine]
    rw [h]
    exact (show Ideal.span {seedLine (e i) (e j)} ≤ sectionIdeal I (e i) (e j) from le_sup_right)
      (Ideal.mem_span_singleton_self _)

private def sliceRename {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m))
    (i j : Fin n) : Slice (contraction e I) i j →ₐ[SeedField] Slice I (e i) (e j) :=
  Ideal.quotientMapₐ (sectionIdeal I (e i) (e j)) (MvPolynomial.rename e) (sectionIdeal_le e I i j)

private def quotientRename {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m)) :
    CoordinateRing (contraction e I) →+* CoordinateRing I :=
  Ideal.quotientMap I (MvPolynomial.rename e).toRingHom le_rfl

private theorem slice_slope_commutes {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m))
    (i j : Fin n) :
    (sliceRename e I i j).toRingHom.comp (slopeToSlice (contraction e I) i j) =
      (slopeToSlice I (e i) (e j)).comp (Polynomial.mapRingHom (quotientRename e I)) := by
  apply Polynomial.ringHom_ext
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, slopeToSlice,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C,
      toSlice, quotientRename, Ideal.quotientMap_mk, sliceRename, Ideal.quotient_map_mkₐ,
      Ideal.Quotient.mkₐ_eq_mk]
    exact congrArg (Ideal.Quotient.mk (sectionIdeal I (e i) (e j)))
      (RingHom.congr_fun (rename_coeffs e) a)
  · simp [slopeToSlice, RingHom.comp_apply]

/-- Contraction gives an injection of coordinate rings, and clearing
denominators reduces injectivity on the generic sections to this injection. -/
private theorem sliceRename_injective {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m))
    (i j : Fin n) [I.IsPrime] [Nontrivial (Slice I (e i) (e j))] :
    Function.Injective (sliceRename e I i j) := by
  apply (injective_iff_map_eq_zero (sliceRename e I i j)).mpr
  intro x hx
  obtain ⟨q, d, hd, hq⟩ := clear_denominator (contraction e I) i j x
  have hq' : sliceRename e I i j (slopeToSlice (contraction e I) i j q) = 0 := by
    rw [← hq, map_mul, hx, zero_mul]
  have hs : slopeToSlice I (e i) (e j) (Polynomial.map (quotientRename e I) q) = 0 :=
    (RingHom.congr_fun (slice_slope_commutes e I i j) q).symm.trans hq'
  have hq0 : q = 0 := (Polynomial.map_eq_zero_iff
      (show Function.Injective (quotientRename e I) from Ideal.quotientMap_injective)).mp
    ((injective_iff_map_eq_zero _).mp (slope_injective I (e i) (e j)) _ hs)
  exact cancel_denominator (contraction e I) i j hd (by simpa only [hq0, map_zero] using hq)

theorem proof : K1_14_2_3_2.c1 := by
  intro I hI hJet
  let e : Fin 2 → Fin 3 := Fin.castLE (by decide)
  let t : Fin 3 → Fin 4 := Fin.castLE (by decide)
  let j : K1_14_2.RootSeedSection (rootImage I) →ₐ[SeedField] JetSeedSection I :=
    sliceRename t I 0 1
  have hj : Function.Injective j := @sliceRename_injective 3 4 t I 0 1 hI hJet
  have hRootPrime : (rootImage I).IsPrime := hI.comap rootIncl
  have hRoot : Nontrivial (RootSeedSection (rootImage I)) := by
    let : Nontrivial (JetSeedSection I) := hJet
    exact j.toRingHom.domain_nontrivial
  let f : K1_14_2_3_2.PlaneSeedSection (seedImage I) →ₐ[SeedField] RootSeedSection (rootImage I) :=
    sliceRename e (rootImage I) 0 1
  exact ⟨@slice_isDomain 4 I 0 1 hI hJet, f, j,
    @sliceRename_injective 2 3 e (rootImage I) 0 1 hRootPrime hRoot, hj⟩

end

end K1_14_2_3_2_1
end PackSource_K1_14_2_3_2_1Proof

section PackSource_K1_14_2_3_2_2Integral
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000

namespace K1_14_2_3_2_2

noncomputable section

open K1_14 K1_14_2

abbrev Raw (n : ℕ) := MvPolynomial (Fin n) FX
abbrev Integral (n : ℕ) := MvPolynomial (Fin n) Seeds
abbrev Over (n : ℕ) := MvPolynomial (Fin n) SeedField

local instance (n : ℕ) (I : Ideal (Raw n)) : CommRing (Polynomial (CoordinateRing I)) :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)

abbrev rawToIntegral (n : ℕ) : Raw n →+* Integral n :=
  MvPolynomial.map MvPolynomial.C

abbrev relation {n : ℕ} (i : Fin n) : Integral n :=
  MvPolynomial.X i - MvPolynomial.C (MvPolynomial.X (1 : Fin 2))

abbrev integralIdeal {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) : Ideal (Integral n) :=
  I.map (rawToIntegral n) ⊔ Ideal.span {relation i}

abbrev integralQuot {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :=
  Integral n ⧸ integralIdeal I i

abbrev coord {n : ℕ} (I : Ideal (Raw n)) (k : Fin n) : CoordinateRing I :=
  Ideal.Quotient.mk I (MvPolynomial.X k)

/-- The first parameter is free. The second is identified with the sliced coordinate. -/
def parameter {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    Seeds →+* Polynomial (CoordinateRing I) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap FX (CoordinateRing I)))
    ![Polynomial.X, Polynomial.C (coord I i)]

def eliminate {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    Integral n →+* Polynomial (CoordinateRing I) :=
  MvPolynomial.eval₂Hom (parameter I i) (fun k => Polynomial.C (coord I k))

private theorem eliminate_raw {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    (eliminate I i).comp (rawToIntegral n) = Polynomial.C.comp (Ideal.Quotient.mk I) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [eliminate, parameter]
    rfl
  · intro k
    simp [eliminate]

private def rawQuotToIntegralQuot {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    CoordinateRing I →+* integralQuot I i :=
  Ideal.quotientMap (integralIdeal I i) (rawToIntegral n)
    (Ideal.map_le_iff_le_comap.mp le_sup_left)

private def restore {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    Polynomial (CoordinateRing I) →+* integralQuot I i :=
  Polynomial.eval₂RingHom (rawQuotToIntegralQuot I i)
    (Ideal.Quotient.mk (integralIdeal I i) (MvPolynomial.C (MvPolynomial.X (0 : Fin 2))))

private theorem integral_relation_eq {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    Ideal.Quotient.mk (integralIdeal I i) (MvPolynomial.X i) =
      Ideal.Quotient.mk (integralIdeal I i) (MvPolynomial.C (MvPolynomial.X (1 : Fin 2))) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (show Ideal.span {relation i} ≤ integralIdeal I i from le_sup_right)
    (Ideal.mem_span_singleton_self _)

private theorem restore_eliminate {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    (restore I i).comp (eliminate I i) = Ideal.Quotient.mk (integralIdeal I i) := by
  apply MvPolynomial.ringHom_ext
  · intro s
    have h : (restore I i).comp (parameter I i) =
        (Ideal.Quotient.mk (integralIdeal I i)).comp MvPolynomial.C := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [parameter, restore, rawQuotToIntegralQuot, MvPolynomial.algebraMap_eq]
      · intro k
        fin_cases k
        · simp [parameter, restore]
        · simpa [parameter, restore, rawQuotToIntegralQuot] using integral_relation_eq I i
    simpa [eliminate] using RingHom.congr_fun h s
  · intro k
    simp [eliminate, restore, rawQuotToIntegralQuot]

/-- Eliminating the second parameter leaves a polynomial ring over the raw quotient. -/
theorem mem_integralIdeal_iff {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) (f : Integral n) :
    f ∈ integralIdeal I i ↔ eliminate I i f = 0 := by
  constructor
  · change f ∈ integralIdeal I i → f ∈ RingHom.ker (eliminate I i)
    apply (show integralIdeal I i ≤ RingHom.ker (eliminate I i) from ?_)
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      change ((eliminate I i).comp (rawToIntegral n)) p = 0
      rw [eliminate_raw]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    · rintro p (rfl : p = relation i)
      simp [eliminate, parameter, RingHom.mem_ker]
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← restore_eliminate I i]
    simp [h]

end
end K1_14_2_3_2_2
end PackSource_K1_14_2_3_2_2Integral

section PackSource_K1_14_2_3_2_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000

namespace K1_14_2_3_2_2

noncomputable section

open K1_14 K1_14_2 K1_14_2_3
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance (n : ℕ) (I : Ideal (Raw n)) : CommRing (Polynomial (CoordinateRing I)) :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)

private abbrev keep : Fin 3 → Fin 4 := Fin.castLE (by decide : 3 ≤ 4)

private abbrev incl (R : Type) [CommRing R] :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 4) R :=
  MvPolynomial.rename keep

private abbrev extendCoeffs (n : ℕ) : Raw n →+* Over n :=
  MvPolynomial.map (algebraMap FX SeedField)

private abbrev localize (n : ℕ) : Integral n →+* Over n :=
  algebraMap (Integral n) (Over n)

private abbrev denominators (n : ℕ) : Submonoid (Integral n) :=
  (nonZeroDivisors Seeds).map MvPolynomial.C

private abbrev sectionIdeal {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) : Ideal (Over n) :=
  I.map (extendCoeffs n) ⊔ Ideal.span {ySection i}

private theorem map_integralIdeal {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    (integralIdeal I i).map (localize n) = sectionIdeal I i := by
  rw [integralIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  have h : (localize n).comp (rawToIntegral n) = extendCoeffs n := by
    have hbase : (algebraMap Seeds SeedField).comp (MvPolynomial.C : FX →+* Seeds) =
        algebraMap FX SeedField :=
      (IsScalarTower.algebraMap_eq FX Seeds SeedField).symm
    apply RingHom.ext
    intro f
    change MvPolynomial.map (algebraMap Seeds SeedField) (MvPolynomial.map MvPolynomial.C f) =
      MvPolynomial.map (algebraMap FX SeedField) f
    rw [MvPolynomial.map_map, hbase]
  rw [h]
  have hr : localize n (relation i) = ySection i := by
    change MvPolynomial.map (algebraMap Seeds SeedField) (relation i) = ySection i
    simp only [relation, ySection, map_sub, MvPolynomial.map_X, MvPolynomial.map_C, generic]
  rw [hr]

private def rawToJet (I : Ideal Ambient) : CoordinateRing (rootImage I) →+* CoordinateRing I :=
  Ideal.quotientMap I rootIncl le_rfl

private theorem rawToJet_injective (I : Ideal Ambient) : Function.Injective (rawToJet I) :=
  Ideal.quotientMap_injective

private theorem rawToJet_coord (I : Ideal Ambient) (k : Fin 3) :
    rawToJet I (coord (rootImage I) k) = coord I (keep k) := by
  simp [rawToJet, rootIncl]

private theorem eliminate_incl (I : Ideal Ambient) :
    (eliminate I 2).comp (incl Seeds).toRingHom =
      (Polynomial.mapRingHom (rawToJet I)).comp (eliminate (rootImage I) 2) := by
  have hp : (Polynomial.mapRingHom (rawToJet I)).comp (parameter (rootImage I) 2) =
      parameter I 2 := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [parameter, rawToJet, rootIncl, MvPolynomial.algebraMap_eq]
      rfl
    · intro k
      fin_cases k
      · simp [parameter]
      · simpa [parameter, show keep (2 : Fin 3) = (2 : Fin 4) from rfl] using
          congrArg Polynomial.C (rawToJet_coord I 2)
  apply MvPolynomial.ringHom_ext
  · intro s
    simpa [eliminate] using (RingHom.congr_fun hp s).symm
  · intro k
    simpa [eliminate] using (congrArg Polynomial.C (rawToJet_coord I k)).symm

private theorem integral_mem_of_incl (I : Ideal Ambient) (f : Integral 3)
    (hf : incl Seeds f ∈ integralIdeal I 2) : f ∈ integralIdeal (rootImage I) 2 := by
  rw [mem_integralIdeal_iff] at hf ⊢
  have h := RingHom.congr_fun (eliminate_incl I) f
  exact (Polynomial.map_eq_zero_iff (rawToJet_injective I)).mp (h.symm.trans hf)

private theorem localize_incl (f : Integral 3) :
    incl SeedField (localize 3 f) = localize 4 (incl Seeds f) :=
  (MvPolynomial.map_rename (algebraMap Seeds SeedField) keep f).symm

private theorem section_le (I : Ideal Ambient) :
    sectionIdeal (rootImage I) 2 ≤ (sectionIdeal I 2).comap (incl SeedField).toRingHom := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
  · intro p hp
    change incl SeedField (extendCoeffs 3 p) ∈ sectionIdeal I 2
    rw [← MvPolynomial.map_rename]
    exact (show I.map (extendCoeffs 4) ≤ sectionIdeal I 2 from le_sup_left)
      (Ideal.mem_map_of_mem (extendCoeffs 4) hp)
  · rintro q (rfl : q = ySection (2 : Fin 3))
    change incl SeedField (ySection (2 : Fin 3)) ∈ sectionIdeal I 2
    have hy : incl SeedField (ySection (2 : Fin 3)) = ySection (2 : Fin 4) := by
      simp [ySection, show keep (2 : Fin 3) = (2 : Fin 4) from rfl]
    rw [hy]
    exact (show Ideal.span {ySection (2 : Fin 4)} ≤ sectionIdeal I 2 from le_sup_right)
      (Ideal.mem_span_singleton_self _)

private theorem localized_mem_of_incl (I : Ideal Ambient) (f : Integral 3)
    (hf : localize 4 (incl Seeds f) ∈ sectionIdeal I 2) :
    localize 3 f ∈ sectionIdeal (rootImage I) 2 := by
  rw [← map_integralIdeal] at hf ⊢
  obtain ⟨_, ⟨d, hd, rfl⟩, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (denominators 4)
      (Over 4) (integralIdeal I 2) (incl Seeds f)).mp hf
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (denominators 3)]
  refine ⟨MvPolynomial.C d, Submonoid.mem_map_of_mem _ hd, ?_⟩
  apply integral_mem_of_incl I
  simpa only [map_mul, MvPolynomial.rename_C] using hmem

/-- Clear the denominators of a representative in the field-coefficient section.
The integral inclusion reflects the resulting ideal membership. -/
private theorem section_mem_of_incl (I : Ideal Ambient) (f : Over 3)
    (hf : incl SeedField f ∈ sectionIdeal I 2) :
    f ∈ sectionIdeal (rootImage I) 2 := by
  obtain ⟨⟨g, m⟩, hm⟩ := IsLocalization.surj
    (M := denominators 3) f
  obtain ⟨d, hd, hdm⟩ := m.property
  have heq : f * MvPolynomial.C (algebraMap Seeds SeedField d) = localize 3 g := by
    simpa only [← hdm, MvPolynomial.algebraMap_def, MvPolynomial.map_C] using hm
  have hg : localize 4 (incl Seeds g) ∈ sectionIdeal I 2 := by
    rw [← localize_incl, ← heq, map_mul]
    exact Ideal.mul_mem_right _ _ hf
  have hu : IsUnit (MvPolynomial.C (σ := Fin 3) (algebraMap Seeds SeedField d)) :=
    (IsLocalization.map_units SeedField (⟨d, hd⟩ : nonZeroDivisors Seeds)).map MvPolynomial.C
  apply (Ideal.mul_unit_mem_iff_mem _ hu).mp
  rw [heq]
  exact localized_mem_of_incl I g hg

private def toJet (I : Ideal Ambient) : RootYSection (rootImage I) →ₐ[SeedField] JetYSection I :=
  Ideal.quotientMapₐ (sectionIdeal I 2) (incl SeedField) (section_le I)

theorem proof : K1_14_2_3_2.c2 := by
  intro I
  refine ⟨toJet I, (injective_iff_map_eq_zero _).mpr ?_⟩
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply section_mem_of_incl I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [toJet, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk] using hx

end
end K1_14_2_3_2_2
end PackSource_K1_14_2_3_2_2Proof

section PackSource_K1_14_3_2_4Split
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace K1_14_3_2_4

noncomputable section

open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
open scoped BigOperators

/-- A proper pair has finite generic sections, and distinct height-two
components have disjoint generic sections. -/
def c1 : Prop :=
  ∀ (P Q : Jet), ProperPair P Q →
    ∀ s : Slice, Module.Finite SectionField (PairSection P Q s) ∧
      ∀ q r : Surface, q ≠ r → q.asIdeal.height = 2 → r.asIdeal.height = 2 →
        IsCoprime (sliceIdeal s q.asIdeal) (sliceIdeal s r.asIdeal)

/-- Affine substitutions preserve the degree caps in the two remaining coordinates. -/
def c2 : Prop :=
  ∀ (P : Jet) (d : Shape), RowCaps P d →
    BidegreeLE (sectionRow .mixed P) d.U d.B ∧
      (sectionRow .jets P).totalDegree ≤ d.U

/-- Affine product-line Bézout for two equations with the same bidegree caps. -/
def c3 : Prop :=
  ∀ (F G : Plane) (u b : ℕ), Module.Finite SectionField (PlaneSection F G) →
    BidegreeLE F u b → BidegreeLE G u b →
    Module.finrank SectionField (PlaneSection F G) ≤ 2 * u * b

private theorem total_le_pair (h : c1) {P Q : Jet} (hp : ProperPair P Q)
    {qs : Finset Surface} (hc : ComponentsOn P Q qs) (s : Slice) :
    totalSectionDegree qs s ≤ Module.finrank SectionField (PairSection P Q s) := by
  classical
  let I (i : {q // q ∈ qs}) : Ideal SectionJet := sliceIdeal s i.1.asIdeal
  let J : Ideal SectionJet := sliceIdeal s (Ideal.span {P, Q})
  have hle (i : {q // q ∈ qs}) : J ≤ I i := by
    apply sup_le_sup_right
    apply Ideal.map_mono
    apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨_, hP, hQ⟩ := hc i.1 i.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hP
    · exact hQ
  have hcop : Pairwise (Function.onFun IsCoprime I) := by
    intro i j hij
    exact (h P Q hp s).2 i.1 j.1 (fun he => hij (Subtype.ext he))
      (hc i.1 i.2).1 (hc j.1 j.2).1
  let : Module.Finite SectionField (SectionJet ⧸ J) := (h P Q hp s).1
  let finiteComponent (i : {q // q ∈ qs}) : Module.Finite SectionField (SectionJet ⧸ I i) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ SectionField (hle i)).toLinearMap
      (Ideal.Quotient.factor_surjective (hle i))
  let freeComponent (i : {q // q ∈ qs}) : Module.Free SectionField (SectionJet ⧸ I i) :=
    Module.Free.of_divisionRing (K := SectionField) (V := SectionJet ⧸ I i)
  let l := LinearMap.pi fun i => (Ideal.Quotient.factorₐ SectionField (hle i)).toLinearMap
  have hl : Function.Surjective l := by
    intro z
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop z
    exact ⟨Ideal.Quotient.mk J r, funext hr⟩
  calc
    totalSectionDegree qs s = ∑ i : {q // q ∈ qs},
        Module.finrank SectionField (SectionJet ⧸ I i) := by
      change (∑ q ∈ qs, sectionDegree q s) = ∑ q : ↥qs, sectionDegree q.1 s
      exact (Finset.sum_coe_sort qs (fun q => sectionDegree q s)).symm
    _ = Module.finrank SectionField (∀ i : {q // q ∈ qs}, SectionJet ⧸ I i) :=
      (Module.finrank_pi_fintype (R := SectionField)).symm
    _ ≤ _ := LinearMap.finrank_le_finrank_of_surjective (f := l) hl

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) :
    K1_14_3_2.c4 := by
  intro f g a _ _ _ ha hp qs hc
  let P : Jet := C f
  let Q := ordinaryCutter g
  let seedCap := f.natDegree
  let ordinateCap := ordinarySeedDegree f
  have hfin (s : Slice) : Module.Finite SectionField
      (PlaneSection (sectionRow s P) (sectionRow s Q)) :=
    haveI : Module.Finite SectionField (PairSection P Q s) := (h1 P Q hp s).1
    Module.Finite.of_surjective (pairSectionEquiv P Q s).toLinearEquiv.toLinearMap
      (pairSectionEquiv P Q s).surjective
  have htransfer (s : Slice) (N : ℕ) (hs :
      Module.finrank SectionField (PlaneSection (sectionRow s P) (sectionRow s Q)) ≤ N) :
      mass qs s ≤ (N : ℚ) := by
    have h := (total_le_pair h1 hp hc s).trans_eq (pairSectionEquiv P Q s).toLinearEquiv.finrank_eq
    have hcast : (totalSectionDegree qs s : ℚ) ≤ (N : ℚ) := by exact_mod_cast (h.trans hs)
    simpa [totalSectionDegree, mass] using hcast
  obtain ⟨hP, hQ⟩ := ordinaryRowCaps ha
  obtain ⟨hmP, hjP⟩ := h2 P _ hP
  obtain ⟨hmQ, hjQ⟩ := h2 Q _ hQ
  refine ⟨htransfer .seed seedCap ?_, htransfer .ordinate ordinateCap ?_, ?_, ?_⟩
  · rw [seed_length_zero f g (hfin .seed)]
    exact Nat.zero_le _
  · rw [ordinate_length_zero f g (hfin .ordinate)]
    exact Nat.zero_le _
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      htransfer .mixed (2 * ordinateCap * seedCap)
        (h3 _ _ ordinateCap seedCap (hfin .mixed) hmP hmQ)
  · simpa only [Nat.cast_pow] using
      htransfer .jets (ordinateCap ^ 2) (planeBezout _ _ ordinateCap (hfin .jets) hjP hjQ)

end

end K1_14_3_2_4
end PackSource_K1_14_3_2_4Split

section PackSource_K1_14_3_2_4_1Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000

namespace K1_14_3_2_4_1

noncomputable section

open K1_14 K1_14_3 K1_14_3_2 K1_14_3_2_4

private theorem plane_dimension : ringKrullDim Plane = 2 := by
  simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]

private theorem plane_height_le (p : Ideal Plane) [p.IsPrime] : p.height ≤ 2 := by
  have h := Ideal.height_le_ringKrullDim_of_isPrime (I := p)
  rw [plane_dimension] at h
  exact WithBot.coe_le_coe.mp h

private theorem properPair_height {P Q : Jet} (h : ProperPair P Q)
    (I : Ideal Jet) [I.IsPrime] (hP : P ∈ I) (hQ : Q ∈ I) : 2 ≤ I.height := by
  have hne : I ≠ ⊥ := fun e => h.left_ne (by simpa [e] using hP)
  obtain ⟨D, hD, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hne
  let J : Ideal Jet := Ideal.span {D}
  have : J.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hJ₀ : J ≠ ⊥ := fun e => hp.ne_zero (Ideal.span_singleton_eq_bot.mp e)
  have hJ₁ : 1 ≤ J.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hJ₀)
  have hJI : J < I := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr hD) ?_
    intro e
    exact h.no_common D hp.irreducible
      (Ideal.mem_span_singleton.mp (e ▸ hP : P ∈ J))
      (Ideal.mem_span_singleton.mp (e ▸ hQ : Q ∈ J))
  calc
    2 = 1 + 1 := by decide
    _ ≤ J.height + 1 := add_le_add hJ₁ le_rfl
    _ ≤ I.height := Ideal.height_add_one_le_of_lt_of_isPrime hJI

private theorem pair_finite {P Q : Jet} (h : ProperPair P Q) (s : Slice) :
    Module.Finite SectionField (PairSection P Q s) := by
  let J : Ideal Plane := Ideal.span {sectionRow s P, sectionRow s Q}
  have : FiniteRingKrullDim Plane :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr (by rw [plane_dimension]; exact ⟨by decide, by decide⟩)
  have hdim : Ring.KrullDimLE 0 (Plane ⧸ J) := by
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    intro p hp
    have : p.IsPrime := hp.isPrime
    let I := p.comap ((sectionEval s).toRingHom.comp sectionMap)
    have : I.IsPrime := Ideal.comap_isPrime _ _
    have hP : P ∈ I := by
      change sectionRow s P ∈ p
      exact hp.le (Ideal.subset_span (by simp))
    have hQ : Q ∈ I := by
      change sectionRow s Q ∈ p
      exact hp.le (Ideal.subset_span (by simp))
    have htwo : 2 ≤ p.height := (properPair_height h I hP hQ).trans (section_height_ge s p)
    apply Ideal.isMaximal_of_height_eq_ringKrullDim
    rw [plane_dimension]
    exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) (le_antisymm (plane_height_le p) htwo)
  have : IsArtinianRing SectionField := DivisionRing.instIsArtinianRing
  have : Algebra.FiniteType SectionField (Plane ⧸ J) := Algebra.FiniteType.quotient SectionField J
  have : Module.Finite SectionField (Plane ⧸ J) :=
    (Module.finite_iff_krullDimLE_zero SectionField (Plane ⧸ J)).mpr hdim
  exact Module.Finite.of_surjective (pairSectionEquiv P Q s).symm.toLinearEquiv.toLinearMap
    (pairSectionEquiv P Q s).symm.surjective

private theorem distinct_components_disjoint (s : Slice) (q r : Surface)
    (hne : q ≠ r) (hq : q.asIdeal.height = 2) (hr : r.asIdeal.height = 2) :
    IsCoprime (sliceIdeal s q.asIdeal) (sliceIdeal s r.asIdeal) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  let e := (sectionEval s).toRingHom
  have he : Function.Surjective e := sectionEval_surjective s
  have hker : RingHom.ker e ≤ M := (sectionEval_ker s).symm ▸
    (le_sup_right.trans (le_sup_left.trans hle) :
      Ideal.span (sectionEquations s) ≤ M)
  have : M.IsPrime := hM.isPrime
  let p := M.map e
  have : p.IsPrime := Ideal.map_isPrime_of_surjective he hker
  have hback : p.comap e = M := by
    dsimp [p]
    rw [Ideal.comap_map_of_surjective e he, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  let I := p.comap (e.comp sectionMap)
  have : I.IsPrime := Ideal.comap_isPrime _ _
  have hI : I.height ≤ 2 := (section_height_ge s p).trans (plane_height_le p)
  have hqM : q.asIdeal ≤ I := by
    change q.asIdeal ≤ p.comap (e.comp sectionMap)
    rw [← Ideal.comap_comap, hback, ← Ideal.map_le_iff_le_comap]
    exact le_sup_left.trans (le_sup_left.trans hle)
  have hrM : r.asIdeal ≤ I := by
    change r.asIdeal ≤ p.comap (e.comp sectionMap)
    rw [← Ideal.comap_comap, hback, ← Ideal.map_le_iff_le_comap]
    exact le_sup_left.trans (le_sup_right.trans hle)
  have eq_of_height_two (t : Surface) (ht : t.asIdeal.height = 2) (hle : t.asIdeal ≤ I) :
      t.asIdeal = I := by
    refine (lt_or_eq_of_le hle).resolve_left ?_
    intro hlt
    have hthree := (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hI
    rw [ht] at hthree
    exact (by decide : ¬ ((2 : ℕ∞) + 1 ≤ 2)) hthree
  exact hne (PrimeSpectrum.ext ((eq_of_height_two q hq hqM).trans
    (eq_of_height_two r hr hrM).symm))

theorem proof : K1_14_3_2_4.c1 := by
  intro P Q hp s
  exact ⟨pair_finite hp s, distinct_components_disjoint s⟩

end

end K1_14_3_2_4_1
end PackSource_K1_14_3_2_4_1Proof

section PackSource_K1_14_3R_2_4Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

namespace K1_14_3R_2_4

noncomputable section

open K1_14 K1_14_3 K1_14_3_2 K1_14_3R_2

/-- The two branches impose the same pair and the same slice equations. -/
private theorem section_length (P Q : Jet) (k : Slice) :
    Module.finrank SectionField (SectionJet ⧸ slicedIdeal (pairIdeal P Q) k) =
      K1_14_3_4.pairSectionDegree P Q k := by
  unfold slicedIdeal pairIdeal K1_14_3_4.pairSectionDegree
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

private theorem of_section_bounds (hbezout : K1_14_3_4.c5) : K1_14_3R_2.c4 := by
  intro P Q s t k hpair hsj htj hs ht
  constructor
  · exact (K1_14_3_2_4_1.proof P Q hpair (countedSlice k)).1
  · rw [section_length]
    obtain ⟨ha, hc, hd⟩ := hbezout s t P Q hpair hs ht hsj htj
    fin_cases k
    · change K1_14_3_4.pairSectionDegree P Q .seed ≤
        s.B * t.J + t.B * s.J - s.J * t.J
      have hsub : s.J * t.J ≤ s.B * t.J + t.B * s.J :=
        (Nat.mul_le_mul_right t.J hsj).trans (Nat.le_add_right _ _)
      apply (Nat.cast_le (α := ℚ)).mp
      simpa only [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_mul, K1_14_3_4.residualSeed] using ha
    · change K1_14_3_4.pairSectionDegree P Q .ordinate ≤ s.U * t.J + t.U * s.J
      unfold K1_14_3_4.residualOrdinate at hc
      exact_mod_cast hc
    · change K1_14_3_4.pairSectionDegree P Q .mixed ≤ s.U * t.B + t.U * s.B
      unfold K1_14_3_4.residualMixed at hd
      exact_mod_cast hd

end

/-- The generic sections are finite and satisfy the three scheme-length budgets. -/
theorem proof : K1_14_3R_2.c4 :=
  of_section_bounds (K1_14_3_4_5.of_children K1_14_3_4_5_1.proof K1_14_3_4_5_2.proof)

end K1_14_3R_2_4
end PackSource_K1_14_3R_2_4Proof

section PackSource_K1_14_2_2RSplit
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000

namespace K1_14_2_2R

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped Classical
open private selectPair cut_shape_valid equationFor equation_caps from ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split

private theorem passing_mass (h3 : K1_14_2_2.c3)
    (gcds : K1_14_2_2_4.c1) (cancel : K1_14_2_2_4.c3)
    (lengths : K1_14_2_2_4.c4) (sections : K1_14_2_2_4.c5)
    {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ} {rows : Banks}
    (hsrc : JetSource M F rows) (hlo : 2601 ≤ M.overhead) (hhi : M.overhead ≤ 3554)
    (i : Fin 10) (hi : 0 < i.val) (B : RowPair M.overhead rows i) (A : FixedPair B)
    (S : Finset (Ideal Ambient)) (hgeom : ∀ I ∈ S, Active I)
    (hcap : Fits S (budget (i.val-1))) :
    let R := S.filter (retainPair A)
    (i.val ≤ 4 → Fits R (exitBudget i)) ∧ Fits (R.filter dual) (budget i.val) := by
  apply retained_mass gcds cancel lengths sections _ _ i B A _ hi (fits_mono (Finset.filter_subset _ _) hcap)
  intro I hI
  obtain ⟨hm, hg⟩ := Finset.mem_filter.mp hI
  have hI' := hgeom I hm
  have hcontact (s : Shape) (hs : s ∈ stagePair i) (hv : bankVanishes rows s I)
      (P : Jet) (hp : P ∈ rows s (bufferedAt M.overhead (stageAt i).reserve s)) :
      orderOn I P ((stageAt i).reserve+1) := by
    have hs' := pair_scheduled hhi i hs
    have hres : (stageAt i).reserve < p := by fin_cases i <;> decide
    have hfit := buffered_fits hhi i hs
    have hsum : bufferedAt M.overhead (stageAt i).reserve s +
        2 * M.overhead.toNat * (stageAt i).reserve ≤ fullCutoff s := by
      change fullCutoff s - 2*M.overhead.toNat*(stageAt i).reserve + _ ≤ fullCutoff s
      omega
    exact h3 _ rows s I (by omega) hI'
      (hsrc.nested s hs' s hs' rfl rfl rfl le_rfl)
      (hsrc.shift s hs') hv _ _ P hres hsum hp
  exact ⟨hI', hg, hcontact _ (by simp [stagePair]) hg.1.1 _ B.cheap_mem,
    hcontact _ (by simp [stagePair]) hg.1.2.1 _ B.layered_mem⟩

private def stay {w rows} {pairs : ∀ i : Fin 10, RowPair w rows i}
    (parts : ∀ i : Fin 10, FixedPair (pairs i)) (n : ℕ) (I : Ideal Ambient) : Prop :=
  if hn : n < 10 then retainPair (parts ⟨n, hn⟩) I ∧ (n = 4 → dual I)
  else bankVanishes rows full I

private theorem after_four {w rows} {pairs : ∀ i : Fin 10, RowPair w rows i}
    (parts : ∀ i : Fin 10, FixedPair (pairs i)) (start : Finset (Ideal Ambient)) :
    ∀ n, 4 ≤ n → ∀ I ∈ timeline start (stay parts) n, dual I := by
  intro n hn I hI
  have h4 := timeline_antitone start (stay parts) hn hI
  change I ∈ (timeline start (stay parts) 3).filter (stay parts 4) at h4
  have hp := (Finset.mem_filter.mp h4).2
  simp only [stay, dite_eq_left (by decide : (4 : ℕ) < 10)] at hp
  exact hp.2 trivial

theorem of_children (h2 : K1_14_2_2.c2) (h3 : K1_14_2_2.c3)
    (gcds : K1_14_2_2_4.c1) (cancel : K1_14_2_2_4.c3)
    (lengths : K1_14_2_2_4.c4) (sections : K1_14_2_2_4.c5)
    (h5 : K1_14_2_2.c5) (h7 : K1_14_2_2.c7) : K1_14_2.c2 := by
  classical
  intro u del M Γ F hlo hhi rows hsrc hbuf
  let pairs (i : Fin 10) : RowPair M.overhead rows i :=
    Classical.choice (selectPair hhi hsrc hbuf i)
  let parts (i : Fin 10) : FixedPair (pairs i) :=
    ⟨Classical.choice (K1_14_2_2_1.proof _ _ (pairs i).cheap_ne (pairs i).cheap_caps),
     Classical.choice (K1_14_2_2_1.proof _ _ (pairs i).layered_ne (pairs i).layered_caps)⟩
  obtain ⟨initial⟩ := h2 u del M Γ F rows (pairs 0) (parts 0) (by
    intro γ hγ
    exact ⟨hsrc.necessary _ (pair_scheduled hhi 0 (by simp [stagePair]))
        _ (buffer_lt 0 (by simp [stagePair]) _) _ (pairs 0).cheap_mem γ hγ,
      hsrc.necessary _ (pair_scheduled hhi 0 (by simp [stagePair]))
        _ (buffer_lt 0 (by simp [stagePair]) _) _ (pairs 0).layered_mem γ hγ⟩)
  let S := timeline initial.parents (stay parts)
  have hsub (n : ℕ) : S (n+1) ⊆ S n := timeline_succ _ _ _
  have hactive (n : ℕ) : ∀ I ∈ S n, Active I :=
    fun I hI => initial.geometric I (timeline_antitone _ _ (Nat.zero_le n) hI)
  have hdual (n : ℕ) (hn : 4 ≤ n) : ∀ I ∈ S n, dual I :=
    after_four parts initial.parents n hn
  have hcap (n : ℕ) (hn : n < 10) : Fits (S n) (budget n) := by
    induction n with
    | zero => exact initial.initial_mass
    | succ n ih =>
      let i : Fin 10 := ⟨n+1, hn⟩
      let R := (S n).filter (retainPair (parts i))
      have hb := passing_mass h3 gcds cancel lengths sections hsrc hlo hhi i (by simp [i]) (pairs i) (parts i)
        (S n) (hactive n) (ih (by omega))
      have hs (I) (hI : I ∈ S (n+1)) : I ∈ R := by
        change I ∈ (S n).filter (stay parts (n+1)) at hI
        obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hI
        have hp' : retainPair (parts i) I ∧ (n+1 = 4 → dual I) := by
          simpa only [stay, dite_eq_left hn, i] using hp
        exact Finset.mem_filter.mpr ⟨hm, hp'.1⟩
      by_cases hfour : 4 ≤ n+1
      · apply fits_mono (T := R.filter dual) _ hb.2
        exact fun I hI => Finset.mem_filter.mpr ⟨hs I hI, hdual _ hfour I hI⟩
      · have hh := hb.1 (by dsimp [i]; omega)
        have he : exitBudget i = budget (n+1) := by
          simp [exitBudget, i, show n+1 ≠ 4 by omega]
        rw [he] at hh
        exact fits_mono hs hh
  let exitPool := (S 3).filter (retainPair (parts 4))
  let rankOne := exitPool.filter (fun I => ¬ dual I)
  have hexit : Fits exitPool (exitBudget 4) :=
    (passing_mass h3 gcds cancel lengths sections hsrc hlo hhi 4 (by decide) (pairs 4) (parts 4)
      (S 3) (hactive 3) (hcap 3 (by decide))).1 (by decide)
  have hrank := fits_mono (Finset.filter_subset (fun I => ¬ dual I) exitPool) hexit
  obtain ⟨rank, hrankCaps, hrankOn⟩ := h5 rankOne
    (fun I hI => ⟨hactive 3 I ((Finset.mem_filter.mp ((Finset.mem_filter.mp hI).1)).1),
      (Finset.mem_filter.mp hI).2⟩) (hrank 1) (hrank 2)
  let equation := equationFor parts rank
  let removed (n : ℕ) :=
    (S n \ S (n+1)).filter (fun I => ¬ stagePass pairs (n+1) I)
  have hstep (n : ℕ) (hn : n < 10) : ∃ C : CutCover,
      (∀ fee, C.cost fee ≤ dot (weight (cutShape (n+1)) fee) (mass (removed n))) ∧
      ∀ γ ∈ Γ, (∃ I ∈ removed n, OnParent M F I γ) → C.covers M F γ := by
    apply combineCuts (removed n) (cutShape (n+1))
    intro I hI
    obtain ⟨hsd, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨P, hP, hproper, hzero⟩ :=
      failed_stage hhi hsrc pairs (n+1) I hf
    obtain ⟨C, hcost, hcover⟩ :=
      h7 u del M Γ F (cutShape (n+1)) I P (cut_shape_valid _)
        (hactive n I (Finset.mem_sdiff.mp hsd).1) hP hproper
    exact ⟨C, hcost, fun γ hγ hmark => hcover γ hγ hmark (hzero γ hγ hmark)⟩
  let stepCuts (n : ℕ) : CutCover := if hn : n < 10 then Classical.choose (hstep n hn) else emptyCut
  have hstepCuts (n : ℕ) (hn : n < 10) :
      (∀ fee, (stepCuts n).cost fee ≤ dot (price fee (n+1)) (mass (removed n))) ∧
      ∀ γ ∈ Γ, (∃ I ∈ removed n, OnParent M F I γ) → (stepCuts n).covers M F γ := by
    simpa only [stepCuts, dite_eq_left hn, price, Nat.succ_ne_zero, ite_false] using
      Classical.choose_spec (hstep n hn)
  let cuts := joinCuts (Finset.range 10) stepCuts
  have hcutCap (fee : Fin 3) : cuts.cost fee ≤ feeCap fee := by
    calc
      _ ≤ ∑ n ∈ Finset.range 10, (stepCuts n).cost fee := joinCuts_cost _ _ _
      _ ≤ ∑ n ∈ Finset.range 10, dot (price fee (n+1)) (mass (S n \ S (n+1))) := by
        apply Finset.sum_le_sum
        intro n hn
        exact ((hstepCuts n (Finset.mem_range.mp hn)).1 fee).trans
          (dot_mono _ _ _ (mass_mono (Finset.filter_subset _ _)))
      _ ≤ ledger fee 10 :=
        (Nat.le_add_right _ _).trans (loss_ledger S fee le_rfl (fun i _ => hsub i) hcap)
      _ ≤ _ := ledger_cap fee
  have hfollow (γ : K) (hγ : γ ∈ Γ) (I : Ideal Ambient)
      (hI : I ∈ initial.parents) (hmark : OnParent M F I γ) (n : ℕ) (hn : n ≤ 10) :
      I ∈ S n ∨ (∃ t, fixedAt (equation t) (F.scalar γ) = 0) ∨ cuts.covers M F γ := by
    induction n with
    | zero => exact Or.inl hI
    | succ n ih =>
      rcases ih (by omega) with hm | hp
      · by_cases hout : I ∈ S (n+1)
        · exact Or.inl hout
        right
        have hfail : ¬ stay parts (n+1) I :=
          fun h => hout (Finset.mem_filter.mpr ⟨hm, h⟩)
        by_cases ht : stagePass pairs (n+1) I
        · by_cases hi : n+1 < 10
          · let i : Fin 10 := ⟨n+1, hi⟩
            have htest : pairPass (pairs i) I := by
              simpa only [stagePass, dite_eq_left hi, i] using ht
            by_cases hcheap : fixedOn (parts i).cheap.equation I
            · exact Or.inl ⟨cheapTag i, fixed_on_mark hmark hcheap⟩
            by_cases hlayer : fixedOn (parts i).layered.equation I
            · exact Or.inl ⟨layeredTag i, fixed_on_mark hmark hlayer⟩
            have hgood : retainPair (parts i) I := ⟨htest, hcheap, hlayer⟩
            have hbad : ¬ (n+1 = 4 → dual I) := by
              intro h
              exact hfail (by simpa only [stay, dite_eq_left hi, i] using And.intro hgood h)
            have he : n+1 = 4 := by
              by_contra hne
              exact hbad (fun h => (hne h).elim)
            have hd : ¬ dual I := fun hd => hbad (fun _ => hd)
            have hnj : n = 3 := by omega
            subst n
            have hp : I ∈ rankOne :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm, hgood⟩, hd⟩
            exact Or.inl ⟨rankTag, fixed_on_mark hmark (hrankOn I hp)⟩
          · exact (hfail (by simpa only [stagePass, stay, dite_eq_right hi] using ht)).elim
        · have hrem : I ∈ removed n :=
            Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hm, hout⟩, ht⟩
          exact Or.inr (joinCuts_covers (Finset.mem_range.mpr (by omega))
            ((hstepCuts n (by omega)).2 γ hγ ⟨I, hrem, hmark⟩))
      · exact Or.inr hp
  have hterminal (I : Ideal Ambient) (hI : I ∈ S 10) : bankVanishes rows full I := by
    change I ∈ (S 9).filter (stay parts 10) at hI
    simpa only [stay, dite_eq_right (by decide : ¬ (10 : ℕ) < 10)] using (Finset.mem_filter.mp hI).2
  let parents : RetainedParents rows :=
    ⟨S 10, fun I hI => (hactive 10 I hI).prime,
      fun I hI => (hactive 10 I hI).seed_finite, fun I hI => (hactive 10 I hI).seed_size,
      fun I hI => (hactive 10 I hI).jet_finite,
      fun I hI => ⟨hdual 10 (by decide) I hI, (hactive 10 I hI).jet_lt⟩, hterminal⟩
  let kept := Γ.filter (fun γ => ∃ I ∈ parents.ideals, OnParent M F I γ)
  let lost := Γ.filter (fun γ => ∃ I ∈ cuts.curves, OnParent M F I γ)
  let fixedGroups (k : ℕ × ℕ) :=
    Γ.filter (fun γ => ∃ t, tagKey t = k ∧ fixedAt (equation t) (F.scalar γ) = 0)
  have hfixed (t : FixedTag) (γ : K) (hγ : γ ∈ Γ)
      (hzero : fixedAt (equation t) (F.scalar γ) = 0) :
      ∃ k ∈ fixedKeys, γ ∈ fixedGroups k :=
    ⟨tagKey t, tagKey_mem t, Finset.mem_filter.mpr ⟨hγ, t, rfl, hzero⟩⟩
  refine ⟨{
    direct := initial.direct ∪ cuts.direct
    lost := lost
    kept := kept
    fixedGroups := fixedGroups
    parents := parents
    direct_card := ?_
    fixed_eq := ?_
    lost_subset := Finset.filter_subset _ _
    loss_cover := ?_
    kept_subset := Finset.filter_subset _ _
    kept_cover := fun γ hγ => (Finset.mem_filter.mp hγ).2
    cover := ?_
  }⟩
  · exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add initial.direct_card (hcutCap 2)).trans direct_cap)
  · intro k hk
    obtain ⟨t, rfl⟩ := tagKey_exists hk
    obtain ⟨hne, hj, hb⟩ := equation_caps parts hrankCaps t
    refine ⟨Finset.filter_subset _ _, equation t, hne, hj, hb, ?_⟩
    intro γ hγ
    obtain ⟨t', he, hz⟩ := (Finset.mem_filter.mp hγ).2
    simpa only [tagKey_injective he] using hz
  · exact ⟨cuts.curves, cuts.geometric, hcutCap 0, hcutCap 1,
      fun γ hγ => (Finset.mem_filter.mp hγ).2⟩
  · intro γ hγ
    rcases initial.cover γ hγ with hd | hc | hl | ⟨I, hI, hm⟩
    · exact Or.inl (Finset.mem_union_left _ hd)
    · exact Or.inr (Or.inl (hfixed (cheapTag 0) γ hγ hc))
    · exact Or.inr (Or.inl (hfixed (layeredTag 0) γ hγ hl))
    · rcases hfollow γ hγ I hI hm 10 le_rfl with hk | ⟨t, hf⟩ | hd | ⟨J, hJ, hJm⟩
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hγ, I, hk, hm⟩)))
      · exact Or.inr (Or.inl (hfixed t γ hγ hf))
      · exact Or.inl (Finset.mem_union_right _ hd)
      · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hγ, J, hJ, hJm⟩)))

end
end K1_14_2_2R
end PackSource_K1_14_2_2RSplit

section PackSource_K1_13_4_2_3_1Proof
set_option autoImplicit true
namespace K1_13_4_2_3_1

open K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3
open scoped Polynomial

set_option backward.isDefEq.respectTransparency false
noncomputable section

private theorem slot_grade (a : Shape) (q : ℕ) (s : Slot a q) :
    grade (exponent a q s) = q := by
  have h₂ := s.1.isLt
  have h₁ := s.2.isLt
  simp only [Nat.lt_succ_iff, le_min_iff] at h₂ h₁
  simp [grade, exponent]
  omega

private theorem slot_of_exp (a : Shape) (q : ℕ) (e : Exp) (h : grade e = q)
    (hw : weight e ≤ a.j) (ht : e 2 ≤ a.t) : ∃ s : Slot a q, exponent a q s = e := by
  unfold grade at h
  unfold weight at hw
  let e₂ : Fin (min q (min a.t (a.j / 2)) + 1) := ⟨e 2, by
    apply Nat.lt_succ_of_le
    simp only [le_min_iff]
    omega⟩
  let e₁ : Fin (min (q - e₂.val) (a.j - 2 * e₂.val) + 1) := ⟨e 1, by
    apply Nat.lt_succ_of_le
    simp only [le_min_iff, e₂]
    omega⟩
  refine ⟨⟨e₂, e₁⟩, ?_⟩
  ext i
  fin_cases i <;> simp [exponent, e₂, e₁]
  omega

private theorem exponent_injective (a : Shape) (q : ℕ) :
    Function.Injective (exponent a q) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hi := DFunLike.congr_fun h 2
  have hj := DFunLike.congr_fun h 1
  simp [exponent] at hi hj
  have he : i = i' := Fin.ext hi
  subst i'
  exact congrArg (Sigma.mk i) (Fin.ext hj)

private def testEquiv (a : Shape) (q : ℕ) :
    Test a q ≃ (Fin (a.b + a.j - q) × Slot a q) := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin, gradeCount]
  rw [Fin.sum_univ_eq_sum_range (fun e : ℕ => min (q - e) (a.j - 2 * e) + 1)]

private abbrev part {R : Type*} [CommRing R] (q : ℕ) :
    K1_13_4_2_3_1.Jets R →ₗ[R] K1_13_4_2_3_1.Jets R :=
  MvPolynomial.homogeneousComponent q

private theorem coeff_part {R : Type*} [CommRing R] (q : ℕ) (G : K1_13_4_2_3_1.Jets R) (e : Exp) :
    (part q G).coeff e = if grade e = q then G.coeff e else 0 := by
  rw [MvPolynomial.coeff_homogeneousComponent, Finsupp.degree_eq_sum, Fin.sum_univ_three]
  simp [grade, Nat.add_assoc]

private theorem part_canonical {R : Type*} [CommRing R] (t : R) (q : ℕ) (G : K1_13_4_2_3_1.Jets R) :
    part q (canonical t G) = canonical t (part q G) := by
  classical
  induction G using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial d r =>
      have hmono (P : K1_13_4_2_3_1.Jets R) (hP : ∀ e ∈ P.support, grade e = grade d) :
          part q P = if grade d = q then P else 0 := by
        apply MvPolynomial.ext
        intro e
        rw [coeff_part]
        by_cases he : e ∈ P.support
        · rw [hP e he]
          split <;> simp_all
        · split_ifs <;> simp [MvPolynomial.notMem_support_iff.mp he]
      have hd (e : Exp) (he : e ∈ (MvPolynomial.monomial d r).support) : grade e = grade d :=
        congrArg grade (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he))
      rw [hmono _ hd, hmono]
      · split <;> simp
      · intro e he
        obtain ⟨f, hf, h, _⟩ := canonical_support _ _ he
        exact h.trans (hd _ hf)

private theorem part_cap {a : Shape} {R : Type*} [CommRing R] {q : ℕ} {G : K1_13_4_2_3_1.Jets R}
    (hG : ∀ e ∈ G.support, admissible a e) {e : Exp} (he : e ∈ (part q G).support) :
    grade e = q ∧ weight e ≤ a.j ∧ e 2 ≤ a.t := by
  rw [MvPolynomial.mem_support_iff, coeff_part] at he
  split at he
  next h => exact ⟨h, (hG _ (MvPolynomial.mem_support_iff.mpr he)).2⟩
  next => contradiction

private def term {R : Type*} [CommRing R] (a : Shape) (q : ℕ) (c : JetCoeff a q) : K1_13_4_2_3_1.Jets R[X] :=
  MvPolynomial.monomial (exponent a q c.2) (Polynomial.X ^ c.1.val)

private def trunc {R : Type*} [CommRing R] (a : Shape) (q : ℕ) (G : K1_13_4_2_3_1.Jets R[X]) : K1_13_4_2_3_1.Jets R[X] :=
  ∑ c : JetCoeff a q, MvPolynomial.C (Polynomial.C ((G.coeff (exponent a q c.2)).coeff c.1.val)) *
    term a q c

private theorem coeff_trunc {R : Type*} [CommRing R] {a : Shape} {q : ℕ} (G : K1_13_4_2_3_1.Jets R[X])
    (e : Exp) (n : ℕ) (hn : n < a.b + a.j)
    (hG : G.coeff e ≠ 0 → ∃ s : Slot a q, exponent a q s = e) :
    ((trunc a q G).coeff e).coeff n = (G.coeff e).coeff n := by
  classical
  simp only [trunc, term, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  by_cases he : ∃ s : Slot a q, exponent a q s = e
  · obtain ⟨s, rfl⟩ := he
    rw [Finset.sum_eq_single (⟨⟨n, hn⟩, s⟩ : JetCoeff a q)]
    · simp
    · rintro ⟨k, f⟩ _ hne
      by_cases hf : f = s
      · subst f
        have hk : n ≠ k.val := by
          intro h
          exact hne (Prod.ext (Fin.ext h.symm) rfl)
        simp [Polynomial.coeff_X_pow, hk]
      · have hne' := (exponent_injective a q).ne hf
        simp [hne']
    · simp
  · have hz : G.coeff e = 0 := by
      by_contra h
      exact he (hG h)
    rw [hz, Polynomial.coeff_zero]
    apply Finset.sum_eq_zero
    intro c _
    have hne : exponent a q c.2 ≠ e := fun h => he ⟨c.2, h⟩
    simp [hne]

private theorem probe_trunc {R : Type*} [CommRing R] {a : Shape} {q : ℕ} (G : K1_13_4_2_3_1.Jets R[X])
    (hG : ∀ e ∈ G.support, grade e = q ∧ weight e ≤ a.j ∧ e 2 ≤ a.t)
    (e : Exp) (i : Fin (a.b + a.j - q)) :
    probe q e i.val G = probe q e i.val (trunc a q G) := by
  have hcoeff (f : Exp) (n : ℕ) (hn : n < a.b + a.j) :
      ((trunc a q G).coeff f).coeff n = (G.coeff f).coeff n := by
    apply coeff_trunc _ _ _ hn
    intro hf
    obtain ⟨hg, hw, ht⟩ := hG f (MvPolynomial.mem_support_iff.mpr hf)
    exact slot_of_exp a q f hg hw ht
  have hdiv : MvPolynomial.C ((Polynomial.X : R[X]) ^ (a.b + a.j)) ∣ G - trunc a q G := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro f
    rw [Polynomial.X_pow_dvd_iff]
    intro n hn
    simp [hcoeff f n hn]
  have himg := map_dvd (canonical (Polynomial.X : R[X])) hdiv
  rw [canonical_C, map_sub, MvPolynomial.C_dvd_iff_dvd_coeff] at himg
  unfold probe
  split
  · exact (hcoeff e _ (by have := i.isLt; omega)).symm
  · have h := (Polynomial.X_pow_dvd_iff.mp (himg e)) (q + i.val)
      (by have := i.isLt; omega)
    simpa [sub_eq_zero] using h

private theorem probe_sum {R : Type*} [CommRing R] {a : Shape} {q : ℕ}
    (G : K1_13_4_2_3_1.Jets R[X]) (e : Exp) (i : ℕ) :
    probe q e i (trunc a q G) = ∑ c : JetCoeff a q,
      ((G.coeff (exponent a q c.2)).coeff c.1.val) * probe q e i (term a q c) := by
  by_cases h : i < weight e <;>
    simp [probe, h, trunc, map_sum, map_mul, MvPolynomial.coeff_C_mul,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]

private theorem probe_term_map (a : Shape) (q : ℕ) (c : JetCoeff a q) (e : Exp) (i : ℕ) :
    probe (R := GenericSeed) q e i (term a q c) =
      algebraMap Geom GenericSeed (probe q e i (term a q c)) := by
  let f := Polynomial.mapRingHom (algebraMap Geom GenericSeed)
  have hterm : MvPolynomial.map f (term a q c) = term a q c := by simp [term, f]
  have himg : MvPolynomial.map f (canonical Polynomial.X (term a q c)) =
      canonical Polynomial.X (term a q c) := by
    rw [map_canonical, hterm]
    simp [f]
  by_cases h : i < weight e
  · simp only [probe, ite_eq_left h]
    rw [← hterm, MvPolynomial.coeff_map]
    simp [f, Polynomial.coeff_map]
  · simp only [probe, ite_eq_right h]
    rw [← himg, MvPolynomial.coeff_map]
    simp [f, Polynomial.coeff_map]

theorem proof : K1_13_4_2_3.c1 := by
  classical
  intro a α
  let L := a.b + a.j
  let F := MvPolynomial.mapEquiv (Fin 3)
    (Polynomial.taylorEquiv (algebraMap Geom GenericSeed α)).toRingEquiv
  have hF (G : RawRow) (e : Exp) :
      (F G).coeff e = (G.coeff e).taylor (algebraMap Geom GenericSeed α) := by
    exact MvPolynomial.coeff_map
      (Polynomial.taylorEquiv (algebraMap Geom GenericSeed α)).toRingEquiv.toRingHom G e
  have hX : (Polynomial.taylorEquiv (algebraMap Geom GenericSeed α)) (localPole α) =
      Polynomial.X := by
    change Polynomial.taylor (algebraMap Geom GenericSeed α) (localPole α) = _
    simp [localPole]
  refine ⟨fun q i c =>
    let es := testEquiv a q.val i
    probe q.val (exponent a q.val es.2) es.1.val (term a q.val c), ?_⟩
  intro G hG
  have hcap (e : Exp) (he : e ∈ (F G).support) : admissible a e := by
    apply hG e
    rw [MvPolynomial.mem_support_iff, hF] at he
    exact MvPolynomial.mem_support_iff.mpr (fun h => he (by simp [h]))
  have htranslated (H : RawRow) : F (canonical (localPole α) H) =
      canonical Polynomial.X (F H) := by
    simpa [F, hX] using map_canonical
      (Polynomial.taylorEquiv (algebraMap Geom GenericSeed α)).toRingEquiv.toRingHom
      (localPole α) H
  rw [← map_dvd_iff F, map_pow, htranslated]
  have hpow : F (MvPolynomial.C (localPole α)) = MvPolynomial.C (Polynomial.X : GenericSeed[X]) := by
    simpa [F] using congrArg (MvPolynomial.C (σ := Fin 3)) hX
  rw [hpow, ← map_pow]
  have hgrade (q : Fin (a.b + 1)) (e : Exp) (he : e ∈ (part q.val (F G)).support) :
      grade e = q.val ∧ q.val + weight e ≤ L := by
    obtain ⟨hg, hw, _⟩ := part_cap hcap he
    exact ⟨hg, Nat.add_le_add (Nat.le_of_lt_succ q.isLt) hw⟩
  have hprobes (q : Fin (a.b + 1)) :
      MvPolynomial.C ((Polynomial.X : GenericSeed[X]) ^ L) ∣
          part q.val (canonical Polynomial.X (F G)) ↔
        ∀ i : Test a q.val,
          probe q.val (exponent a q.val (testEquiv a q.val i).2)
            (testEquiv a q.val i).1.val (part q.val (F G)) = 0 := by
    rw [part_canonical, grade_probe_iff _ _ _ (hgrade q) (by have := q.isLt; omega)]
    constructor
    · intro h i
      exact h _ _ (testEquiv a q.val i).1.isLt
    · intro h e i hi
      let P := part q.val (F G)
      by_cases he : ∃ s : Slot a q.val, exponent a q.val s = e
      · obtain ⟨s, rfl⟩ := he
        simpa using h ((testEquiv a q.val).symm (⟨i, hi⟩, s))
      · have hP : P.coeff e = 0 := by
          apply MvPolynomial.notMem_support_iff.mp
          intro hm
          obtain ⟨hg, hw, ht⟩ := part_cap hcap hm
          exact he (slot_of_exp a q.val e hg hw ht)
        have hA : (canonical Polynomial.X P).coeff e = 0 := by
          apply MvPolynomial.notMem_support_iff.mp
          intro hm
          obtain ⟨d, hd, hg, hw, ht⟩ := canonical_support _ _ hm
          obtain ⟨hg', hw', ht'⟩ := part_cap hcap hd
          exact he (slot_of_exp a q.val e (hg.trans hg') (hw.trans hw') (ht.trans ht'))
        change probe q.val e i P = 0
        simp [probe, hP, hA]
  have hdot (q : Fin (a.b + 1)) (i : Test a q.val) :
      probe q.val (exponent a q.val (testEquiv a q.val i).2)
        (testEquiv a q.val i).1.val (part q.val (F G)) =
          dot a α q.val (fun c => probe q.val (exponent a q.val (testEquiv a q.val i).2)
            (testEquiv a q.val i).1.val (term a q.val c)) G := by
    rw [probe_trunc _ (fun _ he => part_cap hcap he), probe_sum, dot]
    apply Finset.sum_congr rfl
    intro c _
    rw [probe_term_map, coeff_part, slot_grade a q.val c.2, ite_eq_left rfl, hF, localCoeff, mul_comm]
  have hparts :
      MvPolynomial.C ((Polynomial.X : GenericSeed[X]) ^ L) ∣ canonical Polynomial.X (F G) ↔
        ∀ q : Fin (a.b + 1), MvPolynomial.C ((Polynomial.X : GenericSeed[X]) ^ L) ∣
          part q.val (canonical Polynomial.X (F G)) := by
    simp only [MvPolynomial.C_dvd_iff_dvd_coeff, coeff_part]
    constructor
    · intro h q e
      split
      · exact h e
      · exact dvd_zero _
    · intro h e
      by_cases he : e ∈ (canonical Polynomial.X (F G)).support
      · obtain ⟨d, hd, hg, _⟩ := canonical_support _ _ he
        have hb : grade e ≤ a.b := hg.le.trans (hcap d hd).1
        simpa using h ⟨grade e, Nat.lt_succ_of_le hb⟩ e
      · rw [MvPolynomial.notMem_support_iff.mp he]
        exact dvd_zero _
  rw [hparts]
  simp_rw [hprobes, hdot]

end

end K1_13_4_2_3_1
end PackSource_K1_13_4_2_3_1Proof

section PackSource_K1_13_4_2_4_2Proof
set_option autoImplicit true
namespace K1_13_4_2_4_2

noncomputable section

set_option maxHeartbeats 600000

open K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_4 Polynomial
open scoped Polynomial BigOperators

private abbrev PolynomialRow := MvPolynomial (Fin 3) ShiftSeed[X]

private def constSeed : Geom →+* ShiftSeed :=
  Polynomial.C.comp (Polynomial.C : Geom →+* Geom[X])

private def fibreSeed (ε : Geom) : ShiftSeed →+* GenericSeed :=
  (algebraMap Geom[X] GenericSeed).comp (specializeShift ε)

private def fibre (ε : Geom) : PolynomialRow →+* RawRow :=
  MvPolynomial.map (Polynomial.mapRingHom (fibreSeed ε))

@[simp] private theorem fibreSeed_const (ε c : Geom) :
    fibreSeed ε (constSeed c) = algebraMap Geom GenericSeed c := by
  rw [IsScalarTower.algebraMap_apply Geom Geom[X] GenericSeed]
  simp [fibreSeed, constSeed, specializeShift]

@[simp] private theorem fibreSeed_comp (ε : Geom) :
    (fibreSeed ε).comp constSeed = algebraMap Geom GenericSeed :=
  RingHom.ext (fibreSeed_const ε)

private def formalBlock (H : Geom[X]) : ShiftSeed[X] :=
  H.map constSeed + Polynomial.C (Polynomial.C Polynomial.X)

private theorem formalBlock_monic {H : Geom[X]} (hm : H.Monic) (hp : 0 < H.natDegree) :
    (formalBlock H).Monic := by
  apply (hm.map constSeed).add_of_left
  exact degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp (by
    rwa [hm.natDegree_map]))

@[simp] private theorem formalBlock_fibre (H : Geom[X]) (ε : Geom) :
    (formalBlock H).map (fibreSeed ε) = liftX (shiftedBlock H ε) := by
  have h : fibreSeed ε (Polynomial.C Polynomial.X) =
      algebraMap Geom GenericSeed ε := by
    rw [IsScalarTower.algebraMap_apply Geom Geom[X] GenericSeed]
    simp [fibreSeed, specializeShift]
  simp [formalBlock, liftX, shiftedBlock, Polynomial.map_map, h]

private def rawConst {A : Type*} [CommRing A] (a : A) : MvPolynomial (Fin 3) A[X] :=
  MvPolynomial.C (Polynomial.C a)

@[simp] private theorem fibre_rawConst (ε : Geom) (a : ShiftSeed) :
    fibre ε (rawConst a) = rawConst (fibreSeed ε a) := by
  simp [fibre, rawConst]

private def homogeneousJet {A : Type*} [CommRing A] (B : A[X]) (i : Fin 3) :
    MvPolynomial (Fin 3) A[X] :=
  ∑ j : Fin 3, if j.val ≤ i.val then
    MvPolynomial.C (hasseDeriv (i.val - j.val) B) * MvPolynomial.X j
  else 0

@[simp] private theorem fibre_homogeneousJet (ε : Geom) (B : ShiftSeed[X]) (i : Fin 3) :
    fibre ε (homogeneousJet B i) = homogeneousJet (B.map (fibreSeed ε)) i := by
  simp [fibre, homogeneousJet, apply_ite, ← hasseDeriv_map]

private def restoreHom (H : Geom[X]) (R : GenericSeed[X]) : PhysicalRow →+* RawRow :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap Geom GenericSeed)))
    (fun i : SeedVar => i.elim
      (rawConst (algebraMap Geom[X] GenericSeed Polynomial.X))
      (fun j => MvPolynomial.C (hasseDeriv j.val R) + homogeneousJet (liftX H) j))

private theorem restoreHom_apply (H : Geom[X]) (R : GenericSeed[X]) (F : PhysicalRow) :
    restoreHom H R F = restoreWith H R F := rfl

private theorem fibreSeed_ne_zero (ε : Geom) {D : ShiftSeed} (hD : specializeShift ε D ≠ 0) :
    fibreSeed ε D ≠ 0 := by
  intro hz
  exact hD ((IsFractionRing.injective Geom[X] GenericSeed)
    (hz.trans (map_zero (algebraMap Geom[X] GenericSeed)).symm))

private theorem residue_hasse (N : ShiftSeed[X]) (D : ShiftSeed) (ε : Geom) (i : ℕ) :
    hasseDeriv i (residueAtShift N D ε) =
      Polynomial.C ((fibreSeed ε D)⁻¹) * (hasseDeriv i N).map (fibreSeed ε) := by
  simp only [residueAtShift, genericResidue, Polynomial.map_map, fibreSeed, RingHom.comp_apply,
    ← Polynomial.smul_eq_C_mul, map_smul, hasseDeriv_map]

private theorem rawConst_mul_C_inv {d : GenericSeed} (hd : d ≠ 0) (p : GenericSeed[X]) :
    rawConst d * (MvPolynomial.C (Polynomial.C d⁻¹ * p) : RawRow) = MvPolynomial.C p := by
  have hc : Polynomial.C d * (Polynomial.C d⁻¹ * p) = p := by
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hd, Polynomial.C_1, one_mul]
  calc
    _ = (MvPolynomial.C (Polynomial.C d * (Polynomial.C d⁻¹ * p)) : RawRow) :=
      (MvPolynomial.C_mul (σ := Fin 3)).symm
    _ = _ := congrArg (MvPolynomial.C : GenericSeed[X] →+* RawRow) hc

/-- A variable of the physical row has a polynomial numerator over the shift ring. -/
private theorem clear_variable (H : Geom[X]) (N : ShiftSeed[X]) (D : ShiftSeed) (i : SeedVar) :
    ∃ (r : ℕ) (P : PolynomialRow), ∀ ε, specializeShift ε D ≠ 0 →
      fibre ε P = (rawConst (fibreSeed ε D)) ^ r *
        restoreHom (shiftedBlock H ε) (residueAtShift N D ε) (MvPolynomial.X i) := by
  cases i with
  | none =>
    refine ⟨0, rawConst Polynomial.X, fun ε _ => ?_⟩
    simp [restoreHom, fibreSeed, specializeShift]
  | some i =>
    refine ⟨1, MvPolynomial.C (hasseDeriv i.val N) +
      rawConst D * homogeneousJet (formalBlock H) i, fun ε hD => ?_⟩
    simp only [map_add, map_mul, fibre_rawConst, fibre_homogeneousJet,
      formalBlock_fibre, pow_one, restoreHom, MvPolynomial.eval₂Hom_X', Option.elim_some,
      residue_hasse, mul_add]
    congr 1
    simpa only [fibre, MvPolynomial.map_C, Polynomial.coe_mapRingHom, MvPolynomial.C_mul] using
      (rawConst_mul_C_inv (fibreSeed_ne_zero ε hD)
        ((hasseDeriv i.val N).map (fibreSeed ε))).symm

/-- Clear a power of one denominator throughout a row by induction on its monomials. -/
private theorem clear_row (H : Geom[X]) (N : ShiftSeed[X]) (D : ShiftSeed) (F : PhysicalRow) :
    ∃ (r : ℕ) (P : PolynomialRow), ∀ ε, specializeShift ε D ≠ 0 →
      fibre ε P = (rawConst (fibreSeed ε D)) ^ r *
        restoreHom (shiftedBlock H ε) (residueAtShift N D ε) F := by
  induction F using MvPolynomial.induction_on with
  | C p =>
    refine ⟨0, MvPolynomial.C (p.map constSeed), fun ε _ => ?_⟩
    simp [fibre, restoreHom, Polynomial.map_map]
  | add p q hp hq =>
    obtain ⟨r, P, hP⟩ := hp
    obtain ⟨s, Q, hQ⟩ := hq
    refine ⟨r + s, rawConst D ^ s * P + rawConst D ^ r * Q, fun ε hD => ?_⟩
    simp only [map_add, map_mul, map_pow, fibre_rawConst, hP ε hD, hQ ε hD, pow_add, mul_add]
    rw [← mul_assoc, ← mul_assoc, mul_comm (rawConst (fibreSeed ε D) ^ s)
      (rawConst (fibreSeed ε D) ^ r)]
  | mul_X p i hp =>
    obtain ⟨r, P, hP⟩ := hp
    obtain ⟨s, Q, hQ⟩ := clear_variable H N D i
    refine ⟨r + s, P * Q, fun ε hD => ?_⟩
    simp only [map_mul, hP ε hD, hQ ε hD, pow_add]
    exact mul_mul_mul_comm _ _ _ _

private theorem clear_columns (H : Geom[X]) (N : ShiftSeed[X]) (D : ShiftSeed)
    {m : ℕ} (F : Fin m → PhysicalRow) :
    ∃ (r : ℕ) (P : Fin m → PolynomialRow), ∀ ε, specializeShift ε D ≠ 0 → ∀ j,
      fibre ε (P j) = (rawConst (fibreSeed ε D)) ^ r *
        restoreHom (shiftedBlock H ε) (residueAtShift N D ε) (F j) := by
  classical
  choose r P hP using fun j => clear_row H N D (F j)
  let b := Finset.univ.sup r
  refine ⟨b, fun j => rawConst D ^ (b - r j) * P j, fun ε hD j => ?_⟩
  have hj : r j ≤ b := Finset.le_sup (Finset.mem_univ j)
  rw [map_mul, map_pow, fibre_rawConst, hP j ε hD, ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel hj]

private def combine {m : ℕ} (P : Fin m → PolynomialRow) (v : Fin m → Geom) : PolynomialRow :=
  ∑ j, rawConst (constSeed (v j)) * P j

private theorem restoreHom_smul (H : Geom[X]) (R : GenericSeed[X]) (a : Geom)
    (F : PhysicalRow) :
    restoreHom H R (a • F) = rawConst (algebraMap Geom GenericSeed a) * restoreHom H R F := by
  have hs : a • F = MvPolynomial.C (Polynomial.C a) * F := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply Geom Geom[X] PhysicalRow,
      MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq]
  rw [hs, map_mul]
  simp only [restoreHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_C, rawConst]

private theorem fibre_combine {H : Geom[X]} {N : ShiftSeed[X]} {D : ShiftSeed}
    {ε : Geom} {m r : ℕ} (P : Fin m → PolynomialRow) (F : Fin m → PhysicalRow)
    (hP : ∀ j, fibre ε (P j) = rawConst (fibreSeed ε D) ^ r *
      restoreHom (shiftedBlock H ε) (residueAtShift N D ε) (F j)) (v : Fin m → Geom) :
    fibre ε (combine P v) = rawConst (fibreSeed ε D) ^ r *
      restoreHom (shiftedBlock H ε) (residueAtShift N D ε) (∑ j, v j • F j) := by
  rw [combine, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, fibre_rawConst, fibreSeed_const, hP j, restoreHom_smul]
  exact mul_left_comm _ _ _

/-- A raw-jet monomial followed by the abscissa and seed exponents. -/
private abbrev Coordinate := (Fin 3 →₀ ℕ) × ℕ × ℕ

private def entry (B : ShiftSeed[X]) (P : PolynomialRow) (u : Coordinate) : Geom[X] :=
  (((P.coeff u.1) %ₘ B).coeff u.2.1).coeff u.2.2

private def coordinates (B : ShiftSeed[X]) (P : PolynomialRow) : Finset Coordinate := by
  classical
  exact P.support.biUnion fun a =>
    ((P.coeff a) %ₘ B).support.biUnion fun i =>
      (((P.coeff a) %ₘ B).coeff i).support.image fun j => (a, i, j)

private theorem mem_coordinates {B : ShiftSeed[X]} {P : PolynomialRow} {u : Coordinate}
    (he : entry B P u ≠ 0) : u ∈ coordinates B P := by
  classical
  obtain ⟨a, i, j⟩ := u
  have hi : ((P.coeff a) %ₘ B).coeff i ≠ 0 := by
    intro h
    exact he (by simp [entry, h])
  have ha : P.coeff a ≠ 0 := by
    intro h
    exact hi (by simp [h])
  exact Finset.mem_biUnion.mpr ⟨a, MvPolynomial.mem_support_iff.mpr ha,
    Finset.mem_biUnion.mpr ⟨i, Polynomial.mem_support_iff.mpr hi,
      Finset.mem_image.mpr ⟨j, Polynomial.mem_support_iff.mpr he, rfl⟩⟩⟩

private theorem entry_combine {m : ℕ} (B : ShiftSeed[X]) (P : Fin m → PolynomialRow)
    (v : Fin m → Geom) (u : Coordinate) :
    entry B (combine P v) u = ∑ j, Polynomial.C (v j) * entry B (P j) u := by
  have h :
      (∑ j, Polynomial.C (constSeed (v j)) * (P j).coeff u.1) %ₘ B =
      ∑ j, Polynomial.C (constSeed (v j)) * ((P j).coeff u.1 %ₘ B) := by
    simp only [← Polynomial.smul_eq_C_mul, ← modByMonicHom_apply, map_sum, map_smul]
  simp only [entry, combine, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, rawConst, h]
  simp only [
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, constSeed, RingHom.comp_apply]

private theorem fibre_dvd_iff_entries (B : ShiftSeed[X]) (hB : B.Monic) (P : PolynomialRow)
    (ε : Geom) :
    MvPolynomial.C (B.map (fibreSeed ε)) ∣ fibre ε P ↔
      ∀ u, evalRingHom ε (entry B P u) = 0 := by
  rw [MvPolynomial.C_dvd_iff_dvd_coeff]
  have hcoeff (a : Fin 3 →₀ ℕ) :
      B.map (fibreSeed ε) ∣ (fibre ε P).coeff a ↔
        ∀ i j, evalRingHom ε (entry B P (a, i, j)) = 0 := by
    rw [← modByMonic_eq_zero_iff_dvd (hB.map (fibreSeed ε))]
    simp only [fibre, MvPolynomial.coeff_map, Polynomial.coe_mapRingHom, ← map_modByMonic _ hB,
      Polynomial.ext_iff, coeff_map, coeff_zero, fibreSeed, RingHom.comp_apply,
      map_eq_zero_iff _ (IsFractionRing.injective Geom[X] GenericSeed), specializeShift]
    rfl
  exact ⟨fun h u => (hcoeff u.1).mp (h u.1) u.2.1 u.2.2,
    fun h a => (hcoeff a).mpr (fun i j => h (a, i, j))⟩

/-- The finite coefficient family of the full monic remainders gives the matrix. -/
theorem proof : K1_13_4_2_4.c2 := by
  classical
  intro H hm hp N D n m F
  obtain ⟨r, P, hP⟩ := clear_columns H N D F
  let B := formalBlock H ^ n
  have hB : B.Monic := (formalBlock_monic hm hp).pow n
  let T := Finset.univ.biUnion fun j : Fin m => coordinates B (P j)
  let e := T.equivFin.symm
  let M : Matrix (Fin T.card) (Fin m) Geom[X] := fun i j => entry B (P j) (e i)
  refine ⟨T.card, M, fun ε hD v => ?_⟩
  have htest (i : Fin T.card) :
      ((M.map (evalRingHom ε)).mulVecLin v) i = evalRingHom ε (entry B (combine P v) (e i)) := by
    change (∑ j, evalRingHom ε (entry B (P j) (e i)) * v j) = _
    rw [entry_combine, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    change _ = (Polynomial.C (v j)).eval ε * _
    rw [eval_C, mul_comm]
  have hmatrix : (M.map (evalRingHom ε)).mulVecLin v = 0 ↔
      ∀ u, evalRingHom ε (entry B (combine P v) u) = 0 := by
    constructor
    · intro hz u
      by_cases hu : u ∈ T
      · let i := T.equivFin ⟨u, hu⟩
        have hi := congrFun hz i
        rw [htest] at hi
        simpa [i, e] using hi
      · have hcol (j : Fin m) : entry B (P j) u = 0 :=
          not_ne_iff.mp fun h => hu (Finset.mem_biUnion.mpr
            ⟨j, Finset.mem_univ _, mem_coordinates h⟩)
        simp [entry_combine, hcol]
    · intro hz
      funext i
      exact (htest i).trans (hz (e i))
  have hunit : IsUnit (rawConst (fibreSeed ε D) ^ r) :=
    (((isUnit_iff_ne_zero.mpr (fibreSeed_ne_zero ε hD)).map
      (Polynomial.C : GenericSeed →+* GenericSeed[X])).map
      (MvPolynomial.C : GenericSeed[X] →+* RawRow)).pow r
  rw [hmatrix, ← fibre_dvd_iff_entries B hB, fibre_combine P F (hP ε hD),
    hunit.dvd_mul_left]
  simp only [B, Polynomial.map_pow, formalBlock_fibre, map_pow, restoreHom_apply]

end
end K1_13_4_2_4_2
end PackSource_K1_13_4_2_4_2Proof

section PackSource_K1_13_4_2_2_1Proof
set_option autoImplicit true
namespace K1_13_4_2_2_1

noncomputable section

open K1_13 K1_13_4_2_2 Finset MvPolynomial
open scoped BigOperators

/-- The coordinates of a pair are `(c,b)`, with index `b+2*c`. -/
private def weighted (u : ℕ) : Finset (ℕ × ℕ) :=
  ((range (u + 1)).product (range (u + 1))).filter fun p => p.2 + 2 * p.1 ≤ u

private theorem mem_weighted (u : ℕ) (p : ℕ × ℕ) :
    p ∈ weighted u ↔ p.2 + 2 * p.1 ≤ u := by
  simp only [weighted, product_eq_sprod, mem_filter, mem_product, mem_range]
  omega

/-- Write `j=b+c`. The part `j ≤ u-u/2` lies on or above the rectangle's
diagonal. Reflect the other part to fill the cells below the diagonal. -/
private theorem card_weighted (u : ℕ) :
    ((weighted u).card : ℤ) = ((u : ℤ) + 2) ^ 2 / 4 := by
  let m := u / 2
  let n := u - m
  have hmn : m ≤ n ∧ n ≤ m + 1 ∧ u = m + n := by
    dsimp [m, n]
    omega
  have hc : (weighted u).card = (m + 1) * (n + 1) := by
    rw [← card_range (m + 1), ← card_range (n + 1), ← card_product]
    apply card_nbij'
      (fun p => if p.1 + p.2 ≤ n then (p.1, p.1 + p.2) else (u + 1 - (p.1 + p.2), p.1))
      (fun p => if p.1 ≤ p.2 then (p.1, p.2 - p.1) else (p.2, u + 1 - p.1 - p.2))
    · rintro ⟨c, b⟩ h
      simp only [mem_coe, mem_weighted] at h
      simp only [mem_coe, mem_product, mem_range]
      split <;> dsimp <;> omega
    · rintro ⟨x, y⟩ h
      simp only [mem_coe, mem_product, mem_range] at h
      simp only [mem_coe, mem_weighted]
      split <;> dsimp <;> omega
    · rintro ⟨c, b⟩ h
      simp only [mem_coe, mem_weighted] at h
      by_cases hcb : c + b ≤ n
      · have hcc : c ≤ c + b := by omega
        simp [hcb, hcc]
      · have hcc : ¬ u + 1 - (c + b) ≤ c := by omega
        simp [hcb, hcc]
        omega
    · rintro ⟨x, y⟩ h
      simp only [mem_coe, mem_product, mem_range] at h
      by_cases hxy : x ≤ y
      · simp [hxy]
        omega
      · have hxy' : ¬ y + (u + 1 - x - y) ≤ n := by omega
        simp [hxy, hxy']
        omega
  simp only [hc, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hu : (u : ℤ) = (m : ℤ) + n := by omega
  have hn : (n : ℤ) - m = 0 ∨ (n : ℤ) - m = 1 := by omega
  have hsq : ((n : ℤ) - m) ^ 2 = 0 ∨ ((n : ℤ) - m) ^ 2 = 1 := by
    rcases hn with hn | hn <;> simp [hn]
  have hsq' : ((u : ℤ) + 2) ^ 2 =
      4 * ((m + 1 : ℤ) * (n + 1)) + ((n : ℤ) - m) ^ 2 := by
    rw [hu]
    ring
  omega

private def triangle (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (range n).sigma fun i => range (i + 1)

private theorem mem_triangle (n : ℕ) (p : Σ _ : ℕ, ℕ) :
    p ∈ triangle n ↔ p.1 < n ∧ p.2 ≤ p.1 := by
  simp [triangle]

private theorem card_triangle (n : ℕ) :
    ((triangle n).card : ℤ) = triangular n := by
  simp only [triangle, card_sigma, card_range, Nat.cast_sum, Nat.cast_add, Nat.cast_one]
  have h : ∀ k : ℕ, 2 * (∑ i ∈ range k, ((i : ℤ) + 1)) = (k : ℤ) * (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, Nat.cast_succ, mul_add, ih]; ring
  unfold triangular
  have hn := h n
  omega

/-- In the excluded part, `j=b+c>d`. Use the coordinates `(u-j,c)`.
The bound `u ≤ 2*d` ensures that the inverse has nonnegative `b`. -/
private theorem card_excluded (d u : ℕ) (hu : u ≤ 2 * d) :
    ((weighted u).filter fun p => ¬ p.1 + p.2 ≤ d).card = (triangle (u - d)).card := by
  apply card_nbij'
    (fun p => ⟨u - (p.1 + p.2), p.1⟩)
    (fun p => (p.2, u - p.1 - p.2))
  · rintro ⟨c, b⟩ h
    simp only [mem_coe, mem_filter, mem_weighted] at h
    simp only [mem_coe, mem_triangle]
    omega
  · rintro ⟨i, c⟩ h
    simp only [mem_coe, mem_triangle] at h
    simp only [mem_coe, mem_filter, mem_weighted]
    omega
  · rintro ⟨c, b⟩ h
    simp only [mem_coe, mem_filter, mem_weighted] at h
    change (c, u - (u - (c + b)) - c) = (c, b)
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨i, c⟩ h
    simp only [mem_coe, mem_triangle] at h
    have hi : u - (c + (u - i - c)) = i := by omega
    change (⟨u - (c + (u - i - c)), c⟩ : Σ _ : ℕ, ℕ) = ⟨i, c⟩
    rw [hi]

private def prefixPairs (d : ℕ) (w : ℤ) : Finset (ℕ × ℕ) :=
  if w < 0 then ∅ else
    (weighted (min w (2 * (d : ℤ))).toNat).filter fun p => p.1 + p.2 ≤ d

private theorem mem_prefix (d : ℕ) (w : ℤ) (p : ℕ × ℕ) :
    p ∈ prefixPairs d w ↔ p.1 + p.2 ≤ d ∧ (p.2 : ℤ) + 2 * p.1 ≤ w := by
  unfold prefixPairs
  split
  · simp only [notMem_empty, false_iff]
    omega
  · rw [mem_filter, mem_weighted]
    omega

private theorem card_prefix (d : ℕ) (w : ℤ) :
    ((prefixPairs d w).card : ℤ) = cumulative d w := by
  by_cases hw : w < 0
  · simp [prefixPairs, cumulative, hw]
  let u := (min w (2 * (d : ℤ))).toNat
  have hu : (u : ℤ) = min w (2 * (d : ℤ)) := by dsimp [u]; omega
  have hud : u ≤ 2 * d := by omega
  have hd : ((u - d : ℕ) : ℤ) = max 0 ((u : ℤ) - d) := by omega
  have h := card_filter_add_card_filter_not (s := weighted u) (fun p => p.1 + p.2 ≤ d)
  rw [card_excluded d u hud] at h
  have h' := congrArg (fun n : ℕ => (n : ℤ)) h
  simp only [Nat.cast_add, card_triangle, card_weighted, hd] at h'
  simp only [prefixPairs, cumulative, ite_eq_right hw]
  change (((weighted u).filter fun p => p.1 + p.2 ≤ d).card : ℤ) =
    (min w (2 * (d : ℤ)) + 2) ^ 2 / 4 - triangular (max 0 (min w (2 * (d : ℤ)) - d))
  rw [← hu]
  omega

private def window (d : ℕ) (g : ℤ) : Finset (ℕ × ℕ) :=
  prefixPairs d 2300 \ prefixPairs d (min 2300 (-g - 1))

private theorem mem_window (d : ℕ) (g : ℤ) (p : ℕ × ℕ) :
    p ∈ window d g ↔
      p.1 + p.2 ≤ d ∧ -g ≤ (p.2 : ℤ) + 2 * p.1 ∧ p.2 + 2 * p.1 ≤ 2300 := by
  simp only [window, mem_sdiff, mem_prefix]
  omega

private theorem card_window (q : ℕ) (g : ℤ) :
    ((window (residualDegree q) g).card : ℤ) = columnCount q g := by
  have hs : prefixPairs (residualDegree q) (min 2300 (-g - 1)) ⊆ prefixPairs (residualDegree q) 2300 := by
    intro p hp
    rw [mem_prefix] at hp ⊢
    omega
  have hc := card_sdiff_add_card_eq_card hs
  have h := congrArg (fun n : ℕ => (n : ℤ)) hc
  simp only [Nat.cast_add] at h
  change ((window (residualDegree q) g).card : ℤ) +
    ((prefixPairs (residualDegree q) (min 2300 (-g - 1))).card : ℤ) =
    ((prefixPairs (residualDegree q) 2300).card : ℤ) at h
  rw [card_prefix, card_prefix] at h
  exact eq_sub_of_add_eq h

private def exponent (d : ℕ) (p : ℕ × ℕ) : PlaneExp :=
  Finsupp.equivFunOnFinite.symm ![d - (p.1 + p.2), p.2, p.1]

private theorem exponent_injective (d : ℕ) : Function.Injective (exponent d) := by
  intro p r h
  apply Prod.ext
  · simpa [exponent] using congrArg (fun e : PlaneExp => e 2) h
  · simpa [exponent] using congrArg (fun e : PlaneExp => e 1) h

private theorem plane_grade (e : PlaneExp) :
    e.weight (fun _ => 1) = e 0 + e 1 + e 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul, add_assoc]

private theorem plane_index (e : PlaneExp) :
    e.weight Fin.val = e 1 + 2 * e 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul, Nat.mul_comm]

private theorem columns_eq (q : ℕ) (g : ℤ) :
    (↑((window (residualDegree q) g).image (exponent (residualDegree q))) : Set PlaneExp) =
      planeExponents q g := by
  ext e
  simp only [mem_coe, mem_image, mem_window]
  change _ ↔ e.weight (fun _ => 1) = residualDegree q ∧
    -g ≤ (e.weight Fin.val : ℤ) ∧ e.weight Fin.val ≤ 2300 ∧ e 2 ≤ 1150
  rw [plane_grade, plane_index]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp [exponent]
    omega
  · intro he
    refine ⟨(e 2, e 1), ?_, ?_⟩
    · dsimp
      omega
    · ext j
      fin_cases j <;> simp [exponent]
      omega

/-- The source dimension equals the difference of the two cumulative counts. -/
private theorem source_count (q : ℕ) (g : ℤ) :
    (Module.finrank Geom (PlaneSource q g) : ℤ) = columnCount q g := by
  unfold PlaneSource
  rw [← columns_eq q g, finrank_restrictSupport_finset,
    card_image_of_injective _ (exponent_injective _), card_window]

theorem proof : K1_13_4_2_2.c1 := by
  intro q _ k _
  exact (source_count q (offset k)).le

end

end K1_13_4_2_2_1
end PackSource_K1_13_4_2_2_1Proof

section PackSource_K1_13_6_2_3_2_6Proof
set_option autoImplicit true
namespace K1_13_6_2_3_2_6

noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial

private theorem component_mul {ι σ : Type}
    {w : σ → ι → ℕ} {s : ι → ℕ} {L : MvPolynomial σ GeoField}
    (hL : IsWeightedHomogeneous w L s) (f : MvPolynomial σ GeoField) (a : ι → ℕ) :
    weightedHomogeneousComponent w (a + s) (L * f) =
      L * weightedHomogeneousComponent w a f := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul, Finset.ite_sum_zero]
  apply Finset.sum_congr rfl
  rintro ⟨u, v⟩ huv
  rw [coeff_weightedHomogeneousComponent]
  by_cases hu : L.coeff u = 0
  · simp [hu]
  · have hw : Finsupp.weight w e = a + s ↔ Finsupp.weight w v = a := by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp huv, map_add, hL hu, add_comm s, add_right_cancel_iff]
    simp only [hw]
    split <;> simp_all

private theorem component_mul_eq_zero {ι σ : Type}
    {w : σ → ι → ℕ} {s : ι → ℕ} {L : MvPolynomial σ GeoField}
    (hL : IsWeightedHomogeneous w L s) (f : MvPolynomial σ GeoField) (b : ι → ℕ)
    (hb : ¬ ∃ a, b = a + s) :
    weightedHomogeneousComponent w b (L * f) = 0 := by
  classical
  apply weightedHomogeneousComponent_eq_zero'
  intro e he hdeg
  rw [MvPolynomial.mem_support_iff, coeff_mul] at he
  obtain ⟨⟨u, v⟩, huv, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hu : L.coeff u ≠ 0 := fun h => hc (by simp [h])
  apply hb
  refine ⟨Finsupp.weight w v, ?_⟩
  rw [← hdeg, ← Finset.HasAntidiagonal.mem_antidiagonal.mp huv, map_add, hL hu, add_comm]

private theorem graded_cut {ι σ : Type} [Fintype ι] [DecidableEq ι]
    (slot : σ → ι) {I : Ideal (MvPolynomial σ GeoField)} {L : MvPolynomial σ GeoField}
    {s : ι → ℕ} (hI : Graded slot I) (hL : IsWeightedHomogeneous (step ∘ slot) L s) :
    Graded slot (I ⊔ Ideal.span {L}) := by
  intro f hf b
  rw [sup_comm, Ideal.mem_span_singleton_sup] at hf
  obtain ⟨g, j, hj, rfl⟩ := hf
  rw [map_add, mul_comm g L]
  apply Ideal.add_mem _
  · by_cases hb : ∃ a, b = a + s
    · obtain ⟨a, rfl⟩ := hb
      rw [component_mul hL]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨_, rfl⟩)
    · rw [component_mul_eq_zero hL g b hb]
      exact Ideal.zero_mem _
  · exact Ideal.mem_sup_left (hI j hj b)

private theorem finite_piece {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (a : ι → ℕ) :
    Module.Finite GeoField (weightedHomogeneousSubmodule GeoField (step ∘ slot) a) := by
  classical
  let _ := Fintype.ofFinite σ
  have hd (e : σ →₀ ℕ) : e.degree = ∑ i, Finsupp.weight (step ∘ slot) e i := by
    simp only [Finsupp.degree_eq_sum, Finsupp.weight_eq_sum, Finset.sum_apply,
      Function.comp_apply, Pi.smul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp [step, Pi.single_apply, mul_ite]
  have := ((Finsupp.finite_of_degree_le (∑ i, a i)).subset
    (show {e | Finsupp.weight (step ∘ slot) e = a} ⊆ _ from
      fun e he => le_of_eq ((hd e).trans (congrArg _ he)))).to_subtype
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.of_basis (basisRestrictSupport GeoField _)

/-- On each degree piece, multiplication identifies the colon quotient with the kernel
of the projection onto the principal cut quotient. -/
private theorem hilbert_cut {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (I K : Ideal (MvPolynomial σ GeoField)) (L : MvPolynomial σ GeoField)
    (a s : ι → ℕ) (hI : Graded slot I) (hL : IsWeightedHomogeneous (step ∘ slot) L s)
    (hcolon : ∀ f, L * f ∈ I ↔ f ∈ K) :
    hilbert slot (I ⊔ Ideal.span {L}) (a + s) + hilbert slot K a = hilbert slot I (a + s) := by
  classical
  let w := step ∘ slot
  let S := weightedHomogeneousSubmodule GeoField w a
  let T := weightedHomogeneousSubmodule GeoField w (a + s)
  let B := I ⊔ Ideal.span {L}
  have hIB : I ≤ B := le_sup_left
  let V (J : Ideal (MvPolynomial σ GeoField)) :=
    T.map (Ideal.Quotient.mkₐ GeoField J).toLinearMap
  let src := (Ideal.Quotient.mkₐ GeoField K).toLinearMap.domRestrict S
  let multiply := (Ideal.Quotient.mkₐ GeoField I).toLinearMap.comp (LinearMap.mulLeft GeoField L)
  let mul : S →ₗ[GeoField] V I :=
    (multiply.domRestrict S).codRestrict (V I) (fun g => by
      have hg : IsWeightedHomogeneous w (g : MvPolynomial σ GeoField) a := g.2
      have hprod := hL.mul hg
      rw [add_comm s a] at hprod
      exact Submodule.mem_map.mpr ⟨L * g, hprod, rfl⟩)
  let proj : V I →ₗ[GeoField] V B :=
    ((Ideal.Quotient.factorₐ GeoField hIB).toLinearMap.domRestrict (V I)).codRestrict (V B)
      (fun x => by
        obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
        exact Submodule.mem_map.mpr ⟨f, hf, by
          change Ideal.Quotient.mk B f = Ideal.Quotient.factor hIB x.val
          rw [← hfx]
          rfl⟩)
  have hsurj : Function.Surjective proj := by
    intro x
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
    exact ⟨⟨Ideal.Quotient.mk I f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩⟩, Subtype.ext hfx⟩
  have hker : LinearMap.ker mul = LinearMap.ker src := by
    ext g
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hg
      have hz : Ideal.Quotient.mk I (L * (g : MvPolynomial σ GeoField)) = 0 :=
        congrArg Subtype.val hg
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hcolon _).mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    · intro hg
      exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr ((hcolon _).mpr
        (Ideal.Quotient.eq_zero_iff_mem.mp hg)))
  have hrange : LinearMap.range mul = LinearMap.ker proj := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change Ideal.Quotient.mk B (L * (g : MvPolynomial σ GeoField)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨_, rfl⟩))
    · intro hx
      obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
      have hx0 : Ideal.Quotient.factor hIB x.val = 0 :=
        congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      rw [← hfx] at hx0
      have hfB : f ∈ B := Ideal.Quotient.eq_zero_iff_mem.mp hx0
      change f ∈ I ⊔ Ideal.span {L} at hfB
      rw [sup_comm, Ideal.mem_span_singleton_sup] at hfB
      obtain ⟨g, j, hj, hgj⟩ := hfB
      let g' := weightedHomogeneousComponent w a g
      have he := congrArg (weightedHomogeneousComponent w (a + s)) hgj
      rw [map_add, mul_comm g L, component_mul hL, weightedHomogeneousComponent_eq_self hf] at he
      change L * g' + weightedHomogeneousComponent w (a + s) j = f at he
      refine ⟨⟨g', weightedHomogeneousComponent_mem w g a⟩, Subtype.ext ?_⟩
      change Ideal.Quotient.mk I (L * g') = x.val
      change Ideal.Quotient.mk I f = x.val at hfx
      rw [← hfx, ← he, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (hI j hj (a + s)), add_zero]
  let _ : Module.Finite GeoField S := finite_piece slot a
  let _ : Module.Finite GeoField T := finite_piece slot (a + s)
  let _ : Module.Finite GeoField (V I) := Module.Finite.map _ _
  have hm := mul.finrank_range_add_finrank_ker
  have hk := src.finrank_range_add_finrank_ker
  rw [hrange, hker] at hm
  have hdim : Module.finrank GeoField (LinearMap.ker proj) =
      Module.finrank GeoField (LinearMap.range src) := by omega
  have hp := proj.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hdim] at hp
  dsimp only [src] at hp
  rw [LinearMap.range_domRestrict] at hp
  unfold hilbert
  exact_mod_cast hp

theorem proof : K1_13_6_2_3_2.c6 := by
  classical
  intro ι _ _ shapes i J D hD hreg
  dsimp only
  intro hI hI₂
  obtain ⟨L, hL, heL⟩ := exists_lift shapes i D (box_support hD)
  obtain ⟨M, hM, heM⟩ := exists_lift shapes i (D ^ 2) (box_sq_support hD)
  have hle : cut J (D ^ 2) ≤ cut J D := by
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨D, pow_two D⟩)
  have : Finite (CapVar shapes) := inferInstance
  refine ⟨capIdeal shapes J ⊔ Ideal.span {M}, capIdeal shapes (cut J (D ^ 2)) ⊔ Ideal.span {L},
    graded_cut _ hI hM, graded_cut _ hI₂ hL, ?_, ?_, ?_, ?_⟩
  · exact sup_le (capIdeal_mono shapes le_sup_left)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (lift_mem heM (Ideal.mem_sup_right
        (Ideal.mem_span_singleton_self _)))))
  · exact sup_le (capIdeal_mono shapes hle)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (lift_mem heL (Ideal.mem_sup_right
        (Ideal.mem_span_singleton_self _)))))
  · intro a
    exact hilbert_cut _ _ _ M a _ hI hM
      (lift_mul_mem_iff heM (square_mul_mem_iff J D hreg))
  · intro a
    exact hilbert_cut _ _ _ L a _ hI₂ hL
      (lift_mul_mem_iff heL (cut_square_mul_mem_iff J D hreg))

end
end K1_13_6_2_3_2_6
end PackSource_K1_13_6_2_3_2_6Proof

section PackSource_K1_14_2_1_1View
set_option autoImplicit true
set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace K1_14_2_1_1

noncomputable section

open K1_14 K1_14_2 Polynomial

abbrev OtherSeed := MvPolynomial (Fin 1) FX
abbrev Fixed := Polynomial (Polynomial OtherSeed)

private def seedPerm (i : Fin 2) : Fin 2 ≃ Fin 2 := Equiv.swap i 0

private theorem seedPerm_active (i : Fin 2) : seedPerm i i = 0 :=
  Equiv.swap_apply_left i 0

private def seedView (i : Fin 2) : Seeds ≃ₐ[FX] Polynomial OtherSeed :=
  (MvPolynomial.renameEquiv FX (seedPerm i)).trans (MvPolynomial.finSuccEquiv FX 1)

private theorem seedView_degree (i : Fin 2) (f : Seeds) :
    (seedView i f).natDegree = f.degreeOf i := by
  change (MvPolynomial.finSuccEquiv FX 1 (MvPolynomial.rename (seedPerm i) f)).natDegree = _
  rw [MvPolynomial.natDegree_finSuccEquiv, ← seedPerm_active i]
  exact MvPolynomial.degreeOf_rename_of_injective (seedPerm i).injective i

private theorem seedView_C (i : Fin 2) (a : FX) :
    seedView i (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  change MvPolynomial.finSuccEquiv FX 1 (MvPolynomial.rename (seedPerm i) (MvPolynomial.C a)) = _
  rw [MvPolynomial.rename_C, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
  rfl

private theorem seedView_X (i j : Fin 2) :
    seedView i (MvPolynomial.X j) =
      if j = i then Polynomial.X else Polynomial.C (MvPolynomial.X 0) := by
  change MvPolynomial.finSuccEquiv FX 1 (MvPolynomial.rename (seedPerm i) (MvPolynomial.X j)) = _
  rw [MvPolynomial.rename_X]
  by_cases h : j = i
  · subst j
    rw [ite_eq_left rfl, seedPerm_active, MvPolynomial.finSuccEquiv_X_zero]
  · have hj : seedPerm i j ≠ 0 := by
      intro hz
      exact h ((seedPerm i).injective (hz.trans (seedPerm_active i).symm))
    have h1 : seedPerm i j = (0 : Fin 1).succ := by
      apply Fin.ext
      have hjv : (seedPerm i j).val ≠ 0 := fun hz => hj (Fin.ext hz)
      have hb := (seedPerm i j).isLt
      change (seedPerm i j).val = 1
      omega
    rw [ite_eq_right h, h1, MvPolynomial.finSuccEquiv_X_succ]

/-- Translating the chosen seed at fixed remaining seed is ordinary Taylor translation. -/
private theorem seedView_translate (i : Fin 2) (f : Seeds) :
    (translateSeed i f).map (seedView i).toRingHom =
      taylor (Polynomial.X : Polynomial OtherSeed) ((seedView i f).map Polynomial.C) := by
  let lhs := (mapRingHom (seedView i).toRingHom).comp (translateSeed i)
  let rhs := (taylorAlgHom (Polynomial.X : Polynomial OtherSeed)).toRingHom.comp
    ((mapRingHom (Polynomial.C : OtherSeed →+* Polynomial OtherSeed)).comp
      (seedView i).toRingHom)
  suffices h : lhs = rhs from RingHom.congr_fun h f
  apply MvPolynomial.ringHom_ext
  · intro a
    change (translateSeed i (MvPolynomial.C a)).map (seedView i).toRingHom =
      taylor _ ((seedView i (MvPolynomial.C a)).map Polynomial.C)
    simp [translateSeed, seedView_C]
  · intro j
    change (translateSeed i (MvPolynomial.X j)).map (seedView i).toRingHom =
      taylor _ ((seedView i (MvPolynomial.X j)).map Polynomial.C)
    by_cases h : j = i
    · simp [translateSeed, seedView_X, h, add_comm]
    · simp [translateSeed, seedView_X, h]

private theorem seedView_coeff_translate (i : Fin 2) (r : ℕ) (f : Seeds) :
    seedView i ((translateSeed i f).coeff r) = hasseDeriv r (seedView i f) := by
  calc
    _ = ((translateSeed i f).map (seedView i).toRingHom).coeff r := (coeff_map _ _).symm
    _ = _ := by rw [seedView_translate, taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]

private theorem swapped_coeff {A : Type*} [CommSemiring A]
    (F : Polynomial (Polynomial A)) (i j : ℕ) :
    ((Bivariate.swap F).coeff i).coeff j = (F.coeff j).coeff i := by
  induction F using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial m c =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]

/-- Move the active seed outside the value and derivative variables. -/
def view (i : Fin 2) : Jet ≃+* Polynomial Fixed :=
  let inner := ((Polynomial.mapEquiv (seedView i).toRingEquiv).trans
    (Bivariate.swap (R := OtherSeed)).toRingEquiv)
  (Polynomial.mapEquiv inner).trans (Bivariate.swap (R := Polynomial OtherSeed)).toRingEquiv

private theorem view_coeff (i : Fin 2) (F : Jet) (n j k : ℕ) :
    (((view i F).coeff n).coeff j).coeff k = (seedView i ((F.coeff j).coeff k)).coeff n := by
  let inner := ((Polynomial.mapEquiv (seedView i).toRingEquiv).trans
    (Bivariate.swap (R := OtherSeed)).toRingEquiv)
  change (((Bivariate.swap (F.map inner.toRingHom)).coeff n).coeff j).coeff k = _
  rw [swapped_coeff, coeff_map]
  change ((Bivariate.swap ((F.coeff j).map (seedView i).toRingHom)).coeff n).coeff k = _
  rw [swapped_coeff, coeff_map]
  rfl

private theorem coeff_sum_monomial_map {A B : Type*} [Semiring A] [Semiring B]
    (F : Polynomial A) (f : A → B) (h0 : f 0 = 0) (n : ℕ) :
    (F.sum fun k c => monomial k (f c)).coeff n = f (F.coeff n) := by
  classical
  rw [coeff_sum, Polynomial.sum, Finset.sum_eq_single n]
  · simp
  · intro k _ hkn
    simp [coeff_monomial, hkn]
  · intro hn
    rw [notMem_support_iff.mp hn, h0, monomial_zero_right, coeff_zero]

private theorem seedHasse_coeff (i : Fin 2) (r : ℕ) (F : Jet) (j k : ℕ) :
    ((seedHasse i r F).coeff j).coeff k = (translateSeed i ((F.coeff j).coeff k)).coeff r := by
  unfold seedHasse
  rw [coeff_sum_monomial_map, coeff_sum_monomial_map]
  · simp
  · simp

theorem view_seedHasse (i : Fin 2) (r : ℕ) (F : Jet) :
    view i (seedHasse i r F) = hasseDeriv r (view i F) := by
  ext n j k : 3
  rw [view_coeff, seedHasse_coeff, seedView_coeff_translate, hasseDeriv_coeff]
  simp only [hasseDeriv_coeff, coeff_natCast_mul, view_coeff]

theorem view_degree_le (i : Fin 2) (F : Jet) (U : ℕ)
    (hbound : ∀ j k, ((F.coeff j).coeff k).totalDegree ≤ U) :
    (view i F).natDegree ≤ U := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext j k : 2
  rw [view_coeff]
  simp only [Polynomial.coeff_zero]
  apply coeff_eq_zero_of_natDegree_lt
  rw [seedView_degree]
  exact ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hbound j k)).trans_lt hn

theorem exists_view_degree_pos (F : Jet) (hf : UsesSeed F) :
    ∃ i : Fin 2, 0 < (view i F).natDegree := by
  obtain ⟨j, k, h⟩ := hf
  obtain ⟨d, hd, hp⟩ := Finset.lt_sup_iff.mp h
  obtain ⟨i, hi⟩ : ∃ i, 0 < d i := by
    by_contra! hzero
    have hz : d = 0 := Finsupp.ext fun i => Nat.eq_zero_of_le_zero (hzero i)
    simp [hz] at hp
  have hseed : 0 < (seedView i ((F.coeff j).coeff k)).natDegree := by
    rw [seedView_degree]
    exact hi.trans_le (MvPolynomial.monomial_le_degreeOf i hd)
  refine ⟨i, hseed.trans_le (le_natDegree_of_ne_zero ?_)⟩
  intro hz
  have hc := view_coeff i F (seedView i ((F.coeff j).coeff k)).natDegree j k
  rw [hz, Polynomial.coeff_zero, Polynomial.coeff_zero] at hc
  have hn : seedView i ((F.coeff j).coeff k) ≠ 0 := by
    intro hn
    simp [hn] at hseed
  exact (leadingCoeff_ne_zero.mpr hn) hc.symm

end
end K1_14_2_1_1
end PackSource_K1_14_2_1_1View

section PackSource_K1_14_2_1_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace K1_14_2_1_1

noncomputable section

open K1 K1_14 Polynomial

/-- In the quotient by a prime g, the translate of g has first nonzero
coefficient at order one. The coefficient at order a of the translate
of g^a * s therefore detects whether g divides s. -/
private theorem dvd_pow_of_dvd_hasse {A : Type*} [CommRing A] {g f : Polynomial A}
    (hg : Prime g) (hd : ¬ g ∣ g.derivative) (e : ℕ)
    (hall : ∀ r < e, g ∣ hasseDeriv r f) : g ^ e ∣ f := by
  let I : Ideal (Polynomial A) := Ideal.span ({g} : Set (Polynomial A))
  let : I.IsPrime := (Ideal.span_singleton_prime hg.ne_zero).mpr hg
  let q := Ideal.Quotient.mk I
  have hq (s : Polynomial A) : q s = 0 ↔ g ∣ s :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  let shift : Polynomial A →+* Polynomial (Polynomial A ⧸ I) :=
    (taylorAlgHom (q Polynomial.X)).toRingHom.comp (mapRingHom (q.comp Polynomial.C))
  have hcoeff (s : Polynomial A) (r : ℕ) :
      (shift s).coeff r = q (hasseDeriv r s) := by
    change (taylor (q Polynomial.X) (s.map (q.comp Polynomial.C))).coeff r = _
    rw [taylor_coeff, hasseDeriv_map, eval_map, ← Polynomial.hom_eval₂, eval₂_C_X]
  have hzero (s : Polynomial A) : (shift s).coeff 0 = q s := by
    rw [hcoeff, hasseDeriv_zero']
  have hone : (shift g).coeff 1 ≠ 0 := by
    rw [hcoeff, hasseDeriv_one']
    exact mt (hq _).mp hd
  obtain ⟨T, hT⟩ : (Polynomial.X : Polynomial (Polynomial A ⧸ I)) ∣ shift g := by
    rw [Polynomial.X_dvd_iff, hzero]
    exact (hq g).mpr (dvd_refl g)
  have hT0 : T.coeff 0 ≠ 0 := by
    rw [hT, Polynomial.coeff_X_mul T 0] at hone
    exact hone
  have horder (a : ℕ) (s : Polynomial A) :
      (shift (g ^ a * s)).coeff a = T.coeff 0 ^ a * (shift s).coeff 0 := by
    rw [map_mul, map_pow, hT, mul_pow]
    have hprod : (Polynomial.X ^ a * T ^ a) * shift s =
        (T ^ a * shift s) * Polynomial.X ^ a := by ac_rfl
    rw [hprod]
    calc
      _ = (T ^ a * shift s).coeff 0 := by
        simpa only [Nat.zero_add] using Polynomial.coeff_mul_X_pow (T ^ a * shift s) a 0
      _ = _ := by
        change constantCoeff (T ^ a * shift s) = constantCoeff T ^ a * constantCoeff (shift s)
        rw [map_mul, map_pow]
  induction e with
  | zero => simp
  | succ a ih =>
    obtain ⟨s, hs⟩ := ih (fun r hr => hall r (Nat.lt_succ_of_lt hr))
    have hz := (hq _).mpr (hall a (Nat.lt_succ_self a))
    rw [hs, ← hcoeff, horder, hzero] at hz
    have hdiv := (hq s).mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hT0))
    obtain ⟨t, ht⟩ := hdiv
    exact ⟨t, by rw [hs, ht, pow_succ, mul_assoc]⟩

private theorem derivative_not_dvd {A : Type*} [CommRing A] [IsDomain A] {q : ℕ} [CharP A q]
    (g : Polynomial A) (hpos : 0 < g.natDegree) (hsmall : g.natDegree < q) :
    ¬ g ∣ g.derivative := by
  have hc : (g.natDegree : A) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hsmall) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff A q _).mp hz))
  have hlead : g.leadingCoeff ≠ 0 := by
    apply leadingCoeff_ne_zero.mpr
    intro hz
    simp [hz] at hpos
  have hcoeff : g.derivative.coeff (g.natDegree - 1) ≠ 0 := by
    rw [coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    exact mul_ne_zero hlead hc
  have hn : g.derivative ≠ 0 := by
    intro hz
    exact hcoeff (by simp [hz])
  intro hdiv
  exact (not_le_of_gt (natDegree_derivative_lt hpos.ne')) (natDegree_le_of_dvd hdiv hn)

theorem proof : K1_14_2_1.c1 := by
  intro G P R U e hG _ hmove hP hGP hsmall hcaps hhasse
  obtain ⟨i, hpos⟩ := exists_view_degree_pos G hmove
  have hbound : (view i G).natDegree < p :=
    ((natDegree_le_of_dvd ((map_dvd_iff (view i)).mpr hGP)
      ((view i).map_ne_zero_iff.mpr hP)).trans (view_degree_le i P U hcaps)).trans_lt hsmall
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  let : CharP OtherSeed p := charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 1) FX) p
  have hirr : Irreducible (view i G) := (MulEquiv.irreducible_iff (view i)).mpr hG
  have hprime : Prime (view i G) := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  apply (map_dvd_iff (view i)).mp
  rw [map_pow]
  apply dvd_pow_of_dvd_hasse hprime (derivative_not_dvd _ hpos hbound)
  intro r hr
  rw [← view_seedHasse]
  exact (map_dvd_iff (view i)).mpr (hhasse i r hr)

end
end K1_14_2_1_1
end PackSource_K1_14_2_1_1Proof

section PackSource_K1_13_5_4_2_4_2_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 12

namespace K1_13_5_4_2_4_2_1

noncomputable section

open K1_13_5_4 (GeometricX)
open K1_13_5_4_2_4 MvPolynomial Algebra
open scoped nonZeroDivisors

variable {A : Fin 4 → Finset Exponent}

private abbrev CoeffIndex (A : Fin 4 → Finset Exponent) := Σ i : Fin 4, ↥(A i)

private abbrev FreeCoeff (A : Fin 4 → Finset Exponent) :=
  {v : CoeffIndex A // v.2.val ≠ 0}

private abbrev Incidence (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (FreeCoeff A ⊕ Fin 4) GeometricX

private def pivot (hz : ∀ i, 0 ∈ A i) (i : Fin 4) : ↥(A i) := ⟨0, hz i⟩

private def otherTerm (i : Fin 4) (a : ↥(A i)) : Incidence A :=
  if h : a.val = 0 then 0 else
    MvPolynomial.X (Sum.inl ⟨⟨i, a⟩, h⟩) *
      a.val.prod (fun j n => MvPolynomial.X (Sum.inr j) ^ n)

private def otherTerms (A : Fin 4 → Finset Exponent) (i : Fin 4) : Incidence A :=
  ∑ a : ↥(A i), otherTerm i a

/-- The affine incidence coordinates consist of the nonconstant coefficients
and the four spatial variables. Each constant coefficient is solved for. -/
private def parameterMap (A : Fin 4 → Finset Exponent) :
    CoefficientRing A →ₐ[GeometricX] Incidence A :=
  aeval fun v => if h : v.2.val = 0 then -otherTerms A v.1 else MvPolynomial.X (Sum.inl ⟨v, h⟩)

private def quotientMk (A : Fin 4 → Finset Exponent) :
    MvPolynomial (Fin 4) (CoefficientField A) →+* GenericQuotient A :=
  Ideal.Quotient.mk _

private theorem quotientMk_C (r : CoefficientField A) :
    quotientMk A (C r) = algebraMap (CoefficientField A) (GenericQuotient A) r := by
  rw [← MvPolynomial.algebraMap_eq, quotientMk, Ideal.Quotient.mk_algebraMap]

private def quotientCoefficients (A : Fin 4 → Finset Exponent) :
    CoefficientRing A →+* GenericQuotient A :=
  (algebraMap (CoefficientField A) (GenericQuotient A)).comp
    (algebraMap (CoefficientRing A) (CoefficientField A))

private def projection (A : Fin 4 → Finset Exponent) : Incidence A →+* GenericQuotient A :=
  eval₂Hom ((quotientCoefficients A).comp (algebraMap GeometricX (CoefficientRing A)))
    (Sum.elim (fun v => quotientCoefficients A (MvPolynomial.X v.val))
      (fun j => quotientMk A (MvPolynomial.X j)))

private theorem projection_inr (i : Fin 4) :
    projection A (MvPolynomial.X (Sum.inr i)) = quotientMk A (MvPolynomial.X i) :=
  eval₂Hom_X' _ _ _

private theorem projection_term (i : Fin 4) (a : ↥(A i)) (ha : a.val ≠ 0) :
    projection A (otherTerm i a) =
      quotientMk A (monomial a.val
        (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩))) := by
  simp only [otherTerm, dite_eq_right ha, map_mul, map_finsuppProd, map_pow, projection_inr,
    monomial_eq]
  rw [show projection A (MvPolynomial.X (Sum.inl ⟨⟨i, a⟩, ha⟩)) =
    quotientCoefficients A (MvPolynomial.X ⟨i, a⟩) from eval₂Hom_X' _ _ _]
  rfl

private theorem projection_terms (hz : ∀ i, 0 ∈ A i) (i : Fin 4) :
    projection A (otherTerms A i) + quotientCoefficients A (MvPolynomial.X ⟨i, pivot hz i⟩) = 0 := by
  classical
  let p := pivot hz i
  have hzero : projection A (otherTerm i p) = 0 := by simp [p, pivot, otherTerm]
  have hterms : projection A (otherTerms A i) =
      ∑ a ∈ Finset.univ.erase p, quotientMk A (monomial a.val
        (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩))) := by
    rw [otherTerms, map_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ p), hzero, add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    exact projection_term i a (fun he => (Finset.mem_erase.mp ha).1 (Subtype.ext he))
  have hrelation : quotientMk A (genericEquation A i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [genericEquation, map_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ p),
    ← hterms] at hrelation
  simpa only [p, pivot, monomial_zero', quotientMk_C, quotientCoefficients,
    RingHom.comp_apply] using hrelation

private theorem parameter_square (hz : ∀ i, 0 ∈ A i) :
    (projection A).comp (parameterMap A).toRingHom = quotientCoefficients A := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change projection A (parameterMap A (C r)) = quotientCoefficients A (C r)
    rw [show parameterMap A (C r) = C r from (parameterMap A).commutes r]
    exact eval₂Hom_C _ _ _
  · rintro ⟨i, a⟩
    change projection A (parameterMap A (MvPolynomial.X ⟨i, a⟩)) =
      quotientCoefficients A (MvPolynomial.X ⟨i, a⟩)
    rw [parameterMap, aeval_X]
    by_cases ha : a.val = 0
    · have he : a = pivot hz i := Subtype.ext ha
      subst a
      rw [dite_eq_left (show (pivot hz i).val = 0 from rfl), map_neg]
      exact neg_eq_iff_add_eq_zero.mpr (projection_terms hz i)
    · rw [dite_eq_right ha]
      exact eval₂Hom_X' _ _ _

/-- Replacing each eliminated coefficient by its spatial coordinate preserves
the number of polynomial variables. -/
private def incidenceIndexEquiv (hz : ∀ i, 0 ∈ A i) : FreeCoeff A ⊕ Fin 4 ≃ CoeffIndex A := by
  classical
  let constants : Fin 4 ≃ {v : CoeffIndex A // ¬ v.2.val ≠ 0} :=
    { toFun := fun i => ⟨⟨i, pivot hz i⟩, by simp [pivot]⟩
      invFun := fun v => v.val.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨i, a⟩, ha⟩
        have he : a = pivot hz i := Subtype.ext (not_ne_iff.mp ha)
        subst a
        rfl }
  exact (Equiv.sumCongr (Equiv.refl _) constants).trans (Equiv.sumCompl _)

private theorem incidence_trdeg (hz : ∀ i, 0 ∈ A i) :
    trdeg GeometricX (Incidence A) = trdeg GeometricX (CoefficientRing A) := by
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] using
    Cardinal.mk_congr (incidenceIndexEquiv hz)

private theorem coefficient_trdeg_finite (A : Fin 4 → Finset Exponent) :
    trdeg GeometricX (CoefficientField A) < Cardinal.aleph0 := by
  let : Algebra.IsAlgebraic (CoefficientRing A) (CoefficientField A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (CoefficientRing A))
  rw [← trdeg_add_eq GeometricX (CoefficientRing A), trdeg_eq_zero (R := CoefficientRing A), add_zero,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id]
  exact Cardinal.mk_lt_aleph0

private theorem projection_surjective {D : Type} [CommRing D]
    (g : D →+* GenericQuotient A) (u : CoefficientField A →+* D)
    (hgu : g.comp u = algebraMap (CoefficientField A) (GenericQuotient A))
    (coord : Fin 4 → D) (hcoord : ∀ i, g (coord i) = quotientMk A (MvPolynomial.X i)) :
    Function.Surjective g := by
  let eval : MvPolynomial (Fin 4) (CoefficientField A) →+* D := eval₂Hom u coord
  have he : g.comp eval = quotientMk A := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, eval, eval₂Hom_C]
      exact (RingHom.congr_fun hgu r).trans (quotientMk_C r).symm
    · intro i
      simp only [RingHom.comp_apply, eval, eval₂Hom_X']
      exact hcoord i
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨eval p, RingHom.congr_fun he p⟩

/-- Localizing the incidence domain at the nonzero parameters preserves its
transcendence degree. Equality of the finite transcendence degrees over the
base field makes this localization integral over the parameter field. -/
private theorem finiteOfIncidence {k R B F Q : Type}
    [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [CommRing B] [IsDomain B] [Algebra k B]
    [Field F] [Algebra R F] [IsFractionRing R F] [Algebra k F] [IsScalarTower k R F]
    [CommRing Q] [Nontrivial Q] [Algebra F Q] [Algebra.FiniteType F Q]
    (j : R →ₐ[k] B) (p : B →+* Q)
    (hpj : p.comp j.toRingHom = (algebraMap F Q).comp (algebraMap R F))
    (hdeg : trdeg k B = trdeg k R) (hfinite : trdeg k F < Cardinal.aleph0)
    (surjective : ∀ (D : Type) [CommRing D] (u : F →+* D) (g : D →+* Q) (w : B →+* D),
      g.comp u = algebraMap F Q → g.comp w = p → Function.Surjective g) :
    Module.Finite F Q := by
  have hinj : Function.Injective (p.comp j.toRingHom) := by
    rw [hpj]
    exact (algebraMap F Q).injective.comp (IsFractionRing.injective R F)
  have hj : Function.Injective j := fun _ _ h => hinj (congrArg p h)
  let M := (nonZeroDivisors R).map j.toRingHom.toMonoidHom
  have hM : M ≤ nonZeroDivisors B :=
    map_le_nonZeroDivisors_of_injective j.toRingHom hj le_rfl
  let D := Localization M
  let : IsDomain D := IsLocalization.isDomain_localization hM
  let : FaithfulSMul B D :=
    (faithfulSMul_iff_algebraMap_injective B D).mpr (IsLocalization.injective D hM)
  let u : F →+* D :=
    IsLocalization.lift (M := nonZeroDivisors R) (g := (algebraMap B D).comp j.toRingHom)
      (fun x => IsLocalization.map_units D (⟨j x, ⟨x, x.2, rfl⟩⟩ : M))
  let : Algebra F D := u.toAlgebra
  let : IsScalarTower k F D := IsScalarTower.of_algebraMap_eq (by
    intro r
    rw [IsScalarTower.algebraMap_apply k B D, IsScalarTower.algebraMap_apply k R F]
    change algebraMap B D (algebraMap k B r) = u (algebraMap R F (algebraMap k R r))
    simp only [u, IsLocalization.lift_eq, RingHom.comp_apply]
    exact congrArg (algebraMap B D) (j.commutes r).symm)
  have hd : trdeg k D = trdeg k F := by
    let : Algebra.IsAlgebraic B D := IsLocalization.isAlgebraic D M
    let : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
    calc
      trdeg k D = trdeg k B := by
        rw [← trdeg_add_eq k B (A := D), trdeg_eq_zero (R := B), add_zero]
      _ = trdeg k R := hdeg
      _ = trdeg k F := by
        rw [← trdeg_add_eq k R (A := F), trdeg_eq_zero (R := R), add_zero]
  let : FaithfulSMul F D :=
    (faithfulSMul_iff_algebraMap_injective F D).mpr u.injective
  have hzero : trdeg F D = 0 := by
    have hle : trdeg F D ≤ 0 := by
      apply (Cardinal.add_le_add_iff_of_lt_aleph0 hfinite).mp
      calc
        trdeg F D + trdeg k F = trdeg k D :=
          (add_comm _ _).trans (trdeg_add_eq k F (A := D))
        _ ≤ 0 + trdeg k F := by rw [hd, zero_add]
    exact le_antisymm hle bot_le
  let : Algebra.IsIntegral F D :=
    Algebra.isAlgebraic_iff_isIntegral.mp (trdeg_eq_zero_iff.mp hzero)
  have hunits : ∀ x : M, IsUnit (p x) := by
    rintro ⟨_, x, hx, rfl⟩
    change IsUnit ((p.comp j.toRingHom) x)
    rw [hpj, RingHom.comp_apply]
    have hx' : algebraMap R F x ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R F).ne
        (mem_nonZeroDivisors_iff_ne_zero.mp hx)
    exact (isUnit_iff_ne_zero.mpr hx').map (algebraMap F Q)
  let g : D →+* Q := IsLocalization.lift hunits
  have hgu : g.comp u = algebraMap F Q := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, g, u, IsLocalization.lift_eq]
    exact RingHom.congr_fun hpj x
  let e : D →ₐ[F] Q := ⟨g, RingHom.congr_fun hgu⟩
  have hg := surjective D u g (algebraMap B D) hgu (IsLocalization.lift_comp hunits)
  let : Algebra.IsIntegral F Q := ⟨fun q => by
    obtain ⟨d, rfl⟩ := hg q
    exact (Algebra.IsIntegral.isIntegral d).map e⟩
  exact Algebra.IsIntegral.finite

private theorem finiteNontrivial (hz : ∀ i, 0 ∈ A i) [Nontrivial (GenericQuotient A)] :
    Module.Finite (CoefficientField A) (GenericQuotient A) := by
  apply finiteOfIncidence (parameterMap A) (projection A) (parameter_square hz)
    (incidence_trdeg hz) (coefficient_trdeg_finite A)
  intro D _ u g w hgu hgw
  refine projection_surjective g u hgu (fun i => w (MvPolynomial.X (Sum.inr i))) ?_
  intro i
  exact (RingHom.congr_fun hgw _).trans (projection_inr i)

theorem proof : K1_13_5_4_2_4_2.c1 := by
  intro A hz
  rcases subsingleton_or_nontrivial (GenericQuotient A) with hQ | hQ
  · let := hQ
    exact Module.Finite.of_surjective (Algebra.linearMap (CoefficientField A) (GenericQuotient A))
      (fun q => ⟨0, Subsingleton.elim _ q⟩)
  · let := hQ
    exact finiteNontrivial hz

end
end K1_13_5_4_2_4_2_1
end PackSource_K1_13_5_4_2_4_2_1Proof

section PackSource_K1_13_5_1View
set_option autoImplicit true
namespace K1_13_5_1

noncomputable section

open K1_13 K1_13_5 MvPolynomial
open scoped Polynomial BigOperators

/-- Present a row as a polynomial in the last jet over the lower jets. -/
def view {r : ℕ} : Row (r + 1) ≃ₐ[Geom[X]] Polynomial (Row r) :=
  (renameEquiv Geom[X] finSuccEquivLast).trans (optionEquivLeft Geom[X] (Fin r))

theorem view_degree {r : ℕ} (f : Row (r + 1)) :
    (view f).natDegree = f.degreeOf (Fin.last r) := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast f)).natDegree = _
  rw [natDegree_optionEquivLeft]
  simpa only [finSuccEquivLast_last] using
    degreeOf_rename_of_injective (p := f) finSuccEquivLast.injective (Fin.last r)

theorem view_derivative {r : ℕ} (f : Row (r + 1)) :
    view (pderiv (Fin.last r) f) = (view f).derivative := by
  change optionEquivLeft _ _ (rename finSuccEquivLast (pderiv (Fin.last r) f)) = _
  rw [← pderiv_rename finSuccEquivLast.injective, finSuccEquivLast_last,
    optionEquivLeft_pderiv_none]
  rfl

theorem view_eval {r : ℕ} (f : Row (r + 1)) (S : Geom[X]) :
    atJet f S = ((view f).map (eval (jet S))).eval (jet S (Fin.last r)) := by
  rw [atJet, view, AlgEquiv.trans_apply, renameEquiv_apply, ← optionEquivLeft_elim_eval,
    eval_rename]
  apply congrArg (fun v => eval v f)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [finSuccEquivLast_last]
  · simp [jet]

theorem view_coeff_weight {r : ℕ} (w : Fin (r + 1) → ℕ)
    (f : Row (r + 1)) (k : ℕ)
    (hk : k ≤ (view f).natDegree) :
    ((view f).coeff k).weightedTotalDegree (fun i => w i.castSucc) +
      w (Fin.last r) * k ≤ f.weightedTotalDegree w := by
  classical
  let w' : Option (Fin r) → ℕ := fun i => i.elim (w (Fin.last r)) (fun j => w j.castSucc)
  have hw : ∀ i : Fin (r + 1), w' (finSuccEquivLast i) = w i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [w', finSuccEquivLast_last]
  have hrename : (rename finSuccEquivLast f).weightedTotalDegree w' =
      f.weightedTotalDegree w := by
    rw [weightedTotalDegree, weightedTotalDegree, support_rename_of_injective
      finSuccEquivLast.injective, Finset.sup_image]
    congr 1
    funext u
    simp only [Function.comp_apply, Finsupp.weight_apply, smul_eq_mul]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  have hterm (k : ℕ) (m : Fin r →₀ ℕ) (hm : m ∈ ((view f).coeff k).support) :
      m.weight (fun i => w i.castSucc) + w (Fin.last r) * k ≤ f.weightedTotalDegree w := by
    have hs := (mem_support_coeff_optionEquivLeft _).mp hm
    have hle := le_weightedTotalDegree w' hs
    change _ ≤ (rename finSuccEquivLast f).weightedTotalDegree w' at hle
    rw [hrename, Finsupp.weight_optionElim] at hle
    simpa only [w', Nat.add_comm, Nat.mul_comm] using hle
  have hcoeff (j : ℕ) (hj : (view f).coeff j ≠ 0) :
      ((view f).coeff j).weightedTotalDegree (fun i => w i.castSucc) +
        w (Fin.last r) * j ≤ f.weightedTotalDegree w := by
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup
      _ (support_nonempty.mpr hj) (fun m => m.weight (fun i : Fin r => w i.castSucc))
    rw [weightedTotalDegree, hmax]
    exact hterm j m hm
  by_cases hzero : (view f).coeff k = 0
  · rw [hzero, weightedTotalDegree_zero, bot_eq_zero, zero_add]
    by_cases hf : view f = 0
    · simp_all
    have h := hcoeff _ (Polynomial.leadingCoeff_ne_zero.mpr hf)
    exact (Nat.mul_le_mul_left _ hk).trans ((Nat.le_add_left _ _).trans h)
  · exact hcoeff k hzero

/-- Lower-order factors keep their constant coefficient, and other factors use
the derivative resultant at the original declared degrees. -/
def elimination {r : ℕ} (f : Row (r + 1)) : Row r :=
  let F := view f
  let c := F.natDegree
  if c = 0 then F.coeff 0 else F.resultant F.derivative c (c - 1)

theorem elimination_eval {r : ℕ} (f : Row (r + 1)) (S : Geom[X])
    (hf : atJet f S = 0) :
    atJet (elimination f) S = 0 ∨
      (0 < (view f).natDegree ∧ RegularAt (Fin.last r) f S) := by
  by_cases hdeg : (view f).natDegree = 0
  · left
    rw [view_eval, Polynomial.eq_C_of_natDegree_eq_zero hdeg, Polynomial.map_C,
      Polynomial.eval_C] at hf
    simpa [elimination, hdeg, atJet] using hf
  · by_cases hder : atJet (pderiv (Fin.last r) f) S = 0
    · left
      rw [view_eval, view_derivative] at hder
      rw [view_eval] at hf
      simpa only [elimination, ite_eq_right hdeg, atJet] using
        Polynomial.map_resultant_eq_zero_of_common_root (eval (jet S))
          (view f) (view f).derivative le_rfl (Polynomial.natDegree_derivative_le _)
          (Or.inl hdeg) (jet S (Fin.last r)) hf hder
    · exact Or.inr ⟨Nat.pos_of_ne_zero hdeg, hf, hder⟩

theorem elimination_ne_zero {r : ℕ} {f : Row (r + 1)} (hf : Irreducible f)
    (hc : (view f).natDegree < K1.p) : elimination f ≠ 0 := by
  let F := view f
  let c := F.natDegree
  have hi : Irreducible F := (MulEquiv.irreducible_iff view.toMulEquiv).mpr hf
  change (if c = 0 then F.coeff 0 else F.resultant F.derivative c (c - 1)) ≠ 0
  by_cases h : c = 0
  · have hnz := Polynomial.leadingCoeff_ne_zero.mpr hi.ne_zero
    change F.coeff c ≠ 0 at hnz
    rw [h] at hnz
    simpa only [ite_eq_left h] using hnz
  · have : CharP Geom K1.p :=
      charP_of_injective_ringHom (RingHom.injective embed) K1.p
    have hcast : (c : Geom) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hc) (Nat.le_of_dvd (Nat.pos_of_ne_zero h)
        ((CharP.cast_eq_zero_iff Geom K1.p c).mp hz))
    have hc' : (c : Row r) ≠ 0 := by
      let ι : Geom →+* Row r := MvPolynomial.C.comp Polynomial.C
      have hinj : Function.Injective ι :=
        (MvPolynomial.C_injective _ _).comp Polynomial.C_injective
      simpa only [map_natCast, map_zero] using (hinj.ne hcast :
        ι (c : Geom) ≠ ι 0)
    have hder : F.derivative ≠ 0 := by
      intro hz
      have hindex : c - 1 + 1 = c := by omega
      have hz' := congrArg (fun p : Polynomial (Row r) => p.coeff (c - 1)) hz
      rw [Polynomial.coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one, hindex,
        Polynomial.coeff_zero] at hz'
      exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hi.ne_zero) hc') hz'
    simpa only [ite_eq_right h] using
      Polynomial.resultant_derivative_ne_zero_of_irreducible F hi hder

end

end K1_13_5_1
end PackSource_K1_13_5_1View

section PackSource_K1_13_5_1Degree
set_option autoImplicit true
namespace K1_13_5_1

noncomputable section

open K1_13 MvPolynomial
open scoped Polynomial BigOperators

/-- A Sylvester term has one coefficient per column. Its eliminated-variable
exponents sum to m*n, so that many copies of its weight can be subtracted. -/
private theorem resultant_weight {r : ℕ} (w : Fin r → ℕ) (a : ℕ)
    (P Q : Polynomial (Row r)) (m n B D : ℕ)
    (hP : ∀ i ≤ m, (P.coeff i).weightedTotalDegree w + a * i ≤ B)
    (hQ : ∀ i ≤ n, (Q.coeff i).weightedTotalDegree w + a * i ≤ D) :
    (P.resultant Q m n).weightedTotalDegree w + a * (m * n) ≤ n * B + m * D := by
  classical
  let M := Polynomial.sylvester P Q m n
  let W : Fin (m + n) → ℕ :=
    Fin.addCases (fun j : Fin m => D + a * j.val) (fun j : Fin n => B + a * j.val)
  have hentry (σ : Equiv.Perm (Fin (m + n))) (i : Fin (m + n))
      (hne : M (σ i) i ≠ 0) :
      (M (σ i) i).weightedTotalDegree w + a * (σ i).val ≤ W i := by
    cases i using Fin.addCases with
    | left j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hj : j.val ≤ (σ (j.castAdd n)).val := h.1
        have hh := hQ ((σ (j.castAdd n)).val - j.val) (by have := h.2; omega)
        simp only [W, Fin.addCases_left]
        have hid : a * ((σ (j.castAdd n)).val - j.val) + a * j.val =
            a * (σ (j.castAdd n)).val := by rw [← Nat.mul_add, Nat.sub_add_cancel hj]
        omega
      · exact absurd rfl hne
    | right j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hj : j.val ≤ (σ (j.natAdd m)).val := h.1
        have hh := hP ((σ (j.natAdd m)).val - j.val) (by have := h.2; omega)
        simp only [W, Fin.addCases_right]
        have hid : a * ((σ (j.natAdd m)).val - j.val) + a * j.val =
            a * (σ (j.natAdd m)).val := by rw [← Nat.mul_add, Nat.sub_add_cancel hj]
        omega
      · exact absurd rfl hne
  let S := (∑ j : Fin m, a * j.val) + ∑ j : Fin n, a * j.val
  have hW : ∑ i, W i = m * D + n * B + S := by
    simp only [W, S, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hsum : ∑ i : Fin (m + n), a * i.val = a * (m * n) + S := by
    simp only [S, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, Nat.mul_add,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hbase : a * (m * n) ≤ n * B := by
    rw [show a * (m * n) = n * (a * m) by ring]
    exact Nat.mul_le_mul_left n ((Nat.le_add_left _ _).trans (hP m le_rfl))
  have hterm (σ : Equiv.Perm (Fin (m + n))) :
      (∏ i, M (σ i) i).weightedTotalDegree w ≤ n * B + m * D - a * (m * n) := by
    by_cases hz : ∃ i, M (σ i) i = 0
    · obtain ⟨i, hi⟩ := hz
      have hp : (∏ j, M (σ j) j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hp, weightedTotalDegree_zero]
      exact Nat.zero_le _
    · simp only [not_exists] at hz
      rw [weightedTotalDegree_prod _ _ _ (fun i _ => hz i)]
      have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hentry σ i (hz i))
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i => a * i.val), hW, hsum] at h
      omega
  have hdet : M.det.weightedTotalDegree w ≤ n * B + m * D - a * (m * n) := by
    rw [Matrix.det_apply]
    refine AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]
      exact hterm σ
    · have hsign : Equiv.Perm.sign σ • (∏ i, M (σ i) i) = -(∏ i, M (σ i) i) := by
        simp [hs]
      rw [hsign, AddMonoidAlgebra.supDegree_neg]
      exact hterm σ
  change M.det.weightedTotalDegree w + a * (m * n) ≤ _
  omega

private theorem coeff_derivative_weight {r : ℕ} (w : Fin r → ℕ) (P : Polynomial (Row r))
    (i : ℕ) :
    (P.derivative.coeff i).weightedTotalDegree w ≤ (P.coeff (i + 1)).weightedTotalDegree w := by
  rw [Polynomial.coeff_derivative, ← Nat.cast_succ, ← map_natCast (MvPolynomial.C : Geom[X] →+* Row r)]
  exact (weightedTotalDegree_mul_le _ _ _).trans (by rw [weightedTotalDegree_C, Nat.add_zero])

/-- For a positive-order factor the Sylvester weight discount is a*c^2,
including the contribution of differentiating the top jet. -/
theorem elimination_weight_positive {r : ℕ} (w : Fin (r + 1) → ℕ)
    (f : Row (r + 1)) (hc : 0 < (view f).natDegree) :
    let c := (view f).natDegree
    (elimination f).weightedTotalDegree (fun i => w i.castSucc) +
      w (Fin.last r) * c ^ 2 ≤ (2 * c - 1) * f.weightedTotalDegree w := by
  let A := view f
  let a := w (Fin.last r)
  let v : Fin r → ℕ := fun i => w i.castSucc
  let B := f.weightedTotalDegree w
  change 0 < A.natDegree at hc
  obtain ⟨k, hk⟩ : ∃ k, A.natDegree = k + 1 :=
    ⟨A.natDegree - 1, by omega⟩
  have hA : ∀ i ≤ k + 1, (A.coeff i).weightedTotalDegree v + a * i ≤ B :=
    fun i hi => view_coeff_weight w f i (by rwa [hk])
  have hab : a ≤ B := by
    have htop := hA (k + 1) le_rfl
    rw [Nat.mul_add, Nat.mul_one] at htop
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  have hD : ∀ i ≤ k, (A.derivative.coeff i).weightedTotalDegree v + a * i ≤ d := by
    intro i hi
    have h := hA (i + 1) (by omega)
    rw [Nat.mul_add, Nat.mul_one, hd] at h
    have h' := coeff_derivative_weight v A i
    omega
  have h := resultant_weight v a A A.derivative (k + 1) k B d hA hD
  have hEq : elimination f = A.resultant A.derivative (k + 1) k := by
    change (if A.natDegree = 0 then A.coeff 0
      else A.resultant A.derivative A.natDegree (A.natDegree - 1)) = _
    simp [hk]
  have hR : (2 * (k + 1) - 1) * B = k * B + (k + 1) * d + (k + 1) * a := by
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, hd]
    ring
  have hL : a * (k + 1) ^ 2 = a * ((k + 1) * k) + (k + 1) * a := by ring
  change (elimination f).weightedTotalDegree v + a * A.natDegree ^ 2 ≤ (2 * A.natDegree - 1) * B
  rw [hk, hEq, hL, hR]
  omega

theorem elimination_weight_zero {r : ℕ} (w : Fin (r + 1) → ℕ)
    (f : Row (r + 1)) (hc : (view f).natDegree = 0) :
    (elimination f).weightedTotalDegree (fun i => w i.castSucc) ≤ f.weightedTotalDegree w := by
  simpa [elimination, hc] using view_coeff_weight w f 0 (Nat.zero_le _)

end

end K1_13_5_1
end PackSource_K1_13_5_1Degree

section PackSource_K1_13_5_1Budget
set_option autoImplicit true
namespace K1_13_5_1

noncomputable section

open scoped BigOperators

/-- Increasing the common top degree from c to C allows an extra degree
discount (C-c)*t whenever its weighted cost per increment is at most 2*b. -/
private theorem increase_budget {a b c C t d : ℕ} (hc : 0 < c) (hC : c ≤ C)
    (ht : a * t ≤ 2 * b) (hd : d + a * c ^ 2 ≤ (2 * c - 1) * b) :
    d + a * c ^ 2 + a * ((C - c) * t) ≤ (2 * C - 1) * b := by
  have hincr := Nat.mul_le_mul_left (C - c) ht
  have he : 2 * C - 1 = (2 * c - 1) + 2 * (C - c) := by omega
  rw [he, Nat.add_mul]
  rw [show a * ((C - c) * t) = (C - c) * (a * t) by ring,
    show 2 * (C - c) * b = (C - c) * (2 * b) by ring]
  exact Nat.add_le_add hd hincr

/-- Charge the constant factors and the positive-degree resultants against
their common source budget and top-degree sum. -/
theorem aggregate {ι : Type*} (T : Finset ι) (b c d : ι → ℕ) (B a : ℕ)
    (hb : ∑ i ∈ T, b i ≤ B) (hc : ∑ i ∈ T, c i ≤ 24) (hB : a * 24 ≤ B)
    (hbase : ∀ i ∈ T, a * c i ≤ b i)
    (hzero : ∀ i ∈ T, c i = 0 → d i ≤ b i)
    (hpos : ∀ i ∈ T, 0 < c i → d i + a * (c i)^2 ≤ (2 * c i - 1) * b i) :
    ∑ i ∈ T, d i ≤ 47 * B - a * 24^2 := by
  let C := ∑ i ∈ T, c i
  have hci (i : ι) (hi : i ∈ T) : c i ≤ C := Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) hi
  by_cases hC : C = 0
  · have h := (Finset.sum_le_sum fun i hi => hzero i hi (by have := hci i hi; omega)).trans hb
    omega
  have hCpos := Nat.pos_of_ne_zero hC
  have hterm (i : ι) (hi : i ∈ T) : d i + a * (C * c i) ≤ (2 * C - 1) * b i := by
    by_cases hi₀ : c i = 0
    · rw [hi₀, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      exact (hzero i hi hi₀).trans (by
        simpa using Nat.mul_le_mul_right (b i) (show 1 ≤ 2 * C - 1 by omega))
    · have h := increase_budget (Nat.pos_of_ne_zero hi₀) (hci i hi)
        ((hbase i hi).trans (by omega : b i ≤ 2 * b i)) (hpos i hi (Nat.pos_of_ne_zero hi₀))
      have he : C = c i + (C - c i) := by have := hci i hi; omega
      have hweight : a * (C * c i) = a * (c i)^2 + a * ((C - c i) * c i) := by
        calc
          _ = a * ((c i + (C - c i)) * c i) := congrArg (fun n => a * (n * c i)) he
          _ = _ := by ring
      rw [hweight, ← Nat.add_assoc]
      exact h
  have hs : (∑ i ∈ T, (d i + a * (C * c i))) ≤ (2 * C - 1) * B :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ hb)
  have hjoint : (∑ i ∈ T, d i) + a * C ^ 2 ≤ (2 * C - 1) * B := by
    simp only [Finset.sum_add_distrib, ← Nat.mul_assoc, ← Finset.mul_sum] at hs
    change (∑ i ∈ T, d i) + (a * C) * C ≤ _ at hs
    rwa [Nat.mul_assoc, ← pow_two] at hs
  have ha : a * (24 + C) ≤ 2 * B := by
    calc
      _ ≤ a * (24 + 24) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hc 24)
      _ = 2 * (a * 24) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hB
  have hfinal := increase_budget hCpos hc ha hjoint
  have he : 24 = C + (24 - C) := by omega
  have hsq : a * C ^ 2 + a * ((24 - C) * (24 + C)) = a * 24 ^ 2 := by
    calc
      _ = a * C ^ 2 + a * ((24 - C) * ((C + (24 - C)) + C)) := by
        exact congrArg (fun n => a * C ^ 2 + a * ((24 - C) * (n + C))) he
      _ = a * (C + (24 - C)) ^ 2 := by ring
      _ = _ := by rw [← he]
  exact Nat.le_sub_of_add_le (by simpa only [Nat.add_assoc, hsq] using hfinal)

end

end K1_13_5_1
end PackSource_K1_13_5_1Budget

section PackSource_K1_13_5_1Proof
set_option autoImplicit true
namespace K1_13_5_1

noncomputable section

open K1_13 K1_13_5 MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators

theorem proof : K1_13_5.c1 := by
  classical
  intro g hg
  obtain ⟨hg₀, hgt, hgi, hgw⟩ := hg
  let _ : StrongNormalizationMonoid (Row 3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors g
  let T := A.toFinset
  let c (f : Row 3) := (view f).natDegree
  let P := T.filter fun f => 0 < c f
  let n := Fintype.card ↥P
  let e : Fin n ≃ ↥P := (Fintype.equivFin ↥P).symm
  let f : Fin n → Row 3 := fun i => (e i).val
  let q : Row 2 := ∏ a ∈ T, elimination a
  have hmem (a : Row 3) (ha : a ∈ T) : a ∈ A := Multiset.mem_toFinset.mp ha
  have hirr (a : Row 3) (ha : a ∈ T) : Irreducible a :=
    irreducible_of_normalized_factor a (hmem a ha)
  have hf (i : Fin n) : f i ∈ T ∧ 0 < c (f i) := Finset.mem_filter.mp (e i).property
  have hdvd : (∏ a ∈ T, a) ∣ g :=
    (Multiset.toFinset_prod_dvd_prod A).trans (prod_normalizedFactors hg₀).dvd
  have hsum (w : Fin 3 → ℕ) :
      (∑ a ∈ T, a.weightedTotalDegree w) ≤ g.weightedTotalDegree w :=
    sum_weightedTotalDegree_le_of_prod_dvd w T id hg₀ hdvd
  have htop (a : Row 3) : c a = a.degreeOf 2 := view_degree a
  have hc : ∑ a ∈ T, c a ≤ 24 := by
    have hbound : g.weightedTotalDegree (fun i => i.val) ≤ 48 :=
      (K1_13_1.indexDegree_eq g) ▸ hgi
    have h : 2 * (∑ a ∈ T, c a) ≤ 48 := calc
      _ = ∑ a ∈ T, (2 * c a) := Finset.mul_sum T c 2
      _ ≤ ∑ a ∈ T, a.weightedTotalDegree (fun i => i.val) := by
        apply Finset.sum_le_sum
        intro a _
        exact (Nat.le_add_left _ _).trans (view_coeff_weight (fun i => i.val) a (c a) le_rfl)
      _ ≤ _ := (hsum _).trans hbound
    omega
  have he₀ (a : Row 3) (ha : a ∈ T) : elimination a ≠ 0 := by
    have hca : c a ≤ 24 := (Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) ha).trans hc
    exact elimination_ne_zero (hirr a ha) (hca.trans_lt (by decide))
  have hq (w : Fin 3 → ℕ) (B : ℕ) (hb : g.weightedTotalDegree w ≤ B)
      (hB : w 2 * 24 ≤ B) :
      q.weightedTotalDegree (fun i => w i.castSucc) ≤ 47 * B - w 2 * 24 ^ 2 := by
    let v : Fin 2 → ℕ := fun i => w i.castSucc
    rw [show q = ∏ a ∈ T, elimination a from rfl, weightedTotalDegree_prod v T _ he₀]
    apply aggregate T (fun a => a.weightedTotalDegree w) c
      (fun a => (elimination a).weightedTotalDegree v) B (w 2) ((hsum w).trans hb) hc hB
    · intro a _
      exact (Nat.le_add_left _ _).trans (view_coeff_weight w a (c a) le_rfl)
    · intro a _ ha
      exact elimination_weight_zero w a ha
    · intro a _ ha
      exact elimination_weight_positive w a ha
  have hqtotal : q.totalDegree ≤ 5064 := by
    have h := hq (1 : Fin 3 → ℕ) 120 (by simpa only [weightedTotalDegree_one] using hgt) (by decide)
    change q.weightedTotalDegree (1 : Fin 2 → ℕ) ≤ 5064 at h
    simpa only [weightedTotalDegree_one] using h
  have hqindex : indexDegree q ≤ 1104 := by
    rw [K1_13_1.indexDegree_eq] at hgi ⊢
    exact hq (fun i => i.val) 48 hgi (by decide)
  have hsub (d : Row 3 → ℕ) : (∑ i, d (f i)) ≤ ∑ a ∈ T, d a := by
    calc
      _ = ∑ a : ↥P, d a.val := e.sum_comp _
      _ = ∑ a ∈ P, d a := Finset.sum_coe_sort P d
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine ⟨n, f, q, ⟨fun i => hirr _ (hf i).1, fun i => htop _ ▸ (hf i).2, ?_, ?_, ?_, ?_⟩,
    ⟨Finset.prod_ne_zero_iff.mpr he₀, hqtotal, hqindex⟩, ?_⟩
  · intro i
    let E := MvPolynomial.optionEquivRight Geom (Fin 3)
    have hdi := map_dvd E.symm (dvd_of_mem_normalizedFactors (hmem _ (hf i).1))
    have hgn : E.symm g ≠ 0 := fun hz => hg₀ (E.symm.injective (hz.trans (map_zero _).symm))
    exact (K1_13_1.trueWeight_iff _).mpr
      ((weightedTotalDegree_le_of_dvd _ hdi hgn).trans ((K1_13_1.trueWeight_iff _).mp hgw))
  · exact (hsub _).trans ((by simpa only [weightedTotalDegree_one] using hsum (1 : Fin 3 → ℕ) :
      (∑ a ∈ T, a.totalDegree) ≤ g.totalDegree).trans hgt)
  · exact (hsub _).trans ((by simpa only [← K1_13_1.indexDegree_eq] using hsum (fun i => i.val) :
      (∑ a ∈ T, indexDegree a) ≤ indexDegree g).trans hgi)
  · simpa only [htop] using (hsub c).trans hc
  · intro S hS
    have hz := map_dvd (eval (jet S)) (prod_normalizedFactors hg₀).symm.dvd
    change atJet g S ∣ eval (jet S) A.prod at hz
    rw [hS, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨a, ha, hzero⟩ := hz
    have haT : a ∈ T := Multiset.mem_toFinset.mpr ha
    rcases elimination_eval a S hzero with h | ⟨hp, hr⟩
    · left
      change eval (jet S) (∏ a ∈ T, elimination a) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero haT h
    · right
      let j : ↥P := ⟨a, Finset.mem_filter.mpr ⟨haT, hp⟩⟩
      refine ⟨e.symm j, ?_⟩
      change RegularAt 2 ((e (e.symm j)).val) S
      rw [Equiv.apply_symm_apply]
      exact hr

end

end K1_13_5_1
end PackSource_K1_13_5_1Proof

section PackSource_K1_13_5_4_1_2Proof
set_option autoImplicit true
namespace K1_13_5_4_1_2

noncomputable section

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_1
open K1_13_6 (coefficientDerivative partialFlow)
open MvPolynomial
open scoped Polynomial

private theorem coefficientDerivative_coeff (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = Polynomial.derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

private theorem row_coeff_add (P Q : Row 4) (m : Fin 4 →₀ ℕ) :
    (P + Q).coeff m = P.coeff m + Q.coeff m :=
  map_add (MvPolynomial.coeffAddMonoidHom m) P Q

private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P + Q) = coefficientDerivative P + coefficientDerivative Q := by
  apply MvPolynomial.ext
  intro m
  simp only [coefficientDerivative_coeff, row_coeff_add, Polynomial.derivative_add]

private theorem coefficientDerivative_mul (P Q : Row 4) :
    coefficientDerivative (P * Q) = P * coefficientDerivative Q + coefficientDerivative P * Q := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [coefficientDerivative_coeff, row_coeff_add, MvPolynomial.coeff_mul,
    Polynomial.derivative_sum, Polynomial.derivative_mul, Finset.sum_add_distrib]
  exact add_comm _ _

private theorem partialFlow_add (P Q : Row 4) :
    partialFlow (P + Q) = partialFlow P + partialFlow Q := by
  simp only [partialFlow, coefficientDerivative_add, map_add, mul_add, Finset.sum_add_distrib]
  ring

private theorem partialFlow_mul (P Q : Row 4) :
    partialFlow (P * Q) = P * partialFlow Q + partialFlow P * Q := by
  let weight (i : Fin 3) : Row 4 :=
    MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) * MvPolynomial.X i.succ
  have hsum :
      (∑ i : Fin 3, weight i * pderiv i.castSucc (P * Q)) =
        P * (∑ i : Fin 3, weight i * pderiv i.castSucc Q) +
        (∑ i : Fin 3, weight i * pderiv i.castSucc P) * Q := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pderiv_mul]
    ring
  change coefficientDerivative (P * Q) + (∑ i : Fin 3, weight i * pderiv i.castSucc (P * Q)) =
    P * (coefficientDerivative Q + (∑ i : Fin 3, weight i * pderiv i.castSucc Q)) +
      (coefficientDerivative P + (∑ i : Fin 3, weight i * pderiv i.castSucc P)) * Q
  rw [coefficientDerivative_mul, hsum]
  ring

/-- The lifted tangent operator multiplied by the separant. -/
private def scaledFlow (f : Row 3) : Row 4 →+ Row 4 where
  toFun b := liftSep f * partialFlow b + thirdVelocityNumerator f * pderiv 3 b
  map_zero' := by simp [partialFlow, coefficientDerivative]
  map_add' P Q := by rw [partialFlow_add, map_add]; ring

private theorem scaledFlow_apply (f : Row 3) (b : Row 4) :
    scaledFlow f b = liftSep f * partialFlow b + thirdVelocityNumerator f * pderiv 3 b := rfl

private theorem scaledFlow_mul (f : Row 3) (P Q : Row 4) :
    scaledFlow f (P * Q) = P * scaledFlow f Q + scaledFlow f P * Q := by
  simp only [scaledFlow_apply, partialFlow_mul, pderiv_mul]
  ring

private theorem scaledFlow_one (f : Row 3) : scaledFlow f 1 = 0 := by
  have h := scaledFlow_mul f 1 1
  simp only [one_mul, mul_one] at h
  exact add_left_cancel (show scaledFlow f 1 + scaledFlow f 1 = scaledFlow f 1 + 0 by
    rw [add_zero]; exact h.symm)

private theorem scaledFlow_natCast (f : Row 3) (n : ℕ) : scaledFlow f (n : Row 4) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, map_add, ih, scaledFlow_one, add_zero]

private theorem scaledFlow_pow (f : Row 3) (b : Row 4) (k : ℕ) :
    scaledFlow f (b ^ (k + 1)) = (↑(k + 1) : Row 4) * b ^ k * scaledFlow f b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ b (k + 1), scaledFlow_mul, ih, pow_succ b k]
    simp only [Nat.cast_succ]
    ring

private def thirdConstant : Geom[X] := Polynomial.C ((3 : Geom)⁻¹)

private theorem three_mul_thirdConstant : (3 : Geom[X]) * thirdConstant = 1 := by
  have h : (3 : Geom) ≠ 0 := geomCast_ne_zero (a := 3) (by decide) (by decide)
  change (Polynomial.C (3 : Geom)) * Polynomial.C ((3 : Geom)⁻¹) = 1
  rw [← map_mul, mul_inv_cancel₀ h, map_one]

private theorem scaledFlow_graph (f : Row 3) : scaledFlow f (graphRaw f) = 0 := by
  have h := congrArg (MvPolynomial.C : Geom[X] →+* Row 4) three_mul_thirdConstant
  simp only [map_mul, map_ofNat, map_one] at h
  have hvelocity : 3 * thirdVelocityNumerator f = -partialFlow (graphRaw f) := by
    rw [thirdVelocityNumerator, Polynomial.C_neg]
    change 3 * (MvPolynomial.C (-thirdConstant) * partialFlow (graphRaw f)) = _
    rw [map_neg]
    calc
      _ = -(3 * MvPolynomial.C thirdConstant) * partialFlow (graphRaw f) := by ring
      _ = _ := by rw [h]; ring
  change liftSep f * partialFlow (graphRaw f) +
    thirdVelocityNumerator f * K1_13_6.separant (graphRaw f) = 0
  rw [graph_separant]
  calc
    _ = liftSep f * partialFlow (graphRaw f) + (3 * thirdVelocityNumerator f) * liftSep f := by ring
    _ = 0 := by rw [hvelocity]; ring

private abbrev rawGraphIdeal (f : Row 3) : Ideal (Row 4) := Ideal.span {graphRaw f}

private abbrev classOf (f : Row 3) := Ideal.Quotient.mk (rawGraphIdeal f)

private theorem scaledFlow_congr (f : Row 3) {P Q : Row 4} (h : classOf f P = classOf f Q) :
    classOf f (scaledFlow f P) = classOf f (scaledFlow f Q) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h)
  apply Ideal.Quotient.eq.mpr
  rw [← map_sub, ← hb, scaledFlow_mul, scaledFlow_graph, mul_zero, zero_add]
  exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩

private theorem scaledFlow_lift (f b : Row 3) :
    classOf f (scaledFlow f (liftRaw b)) = classOf f (liftRaw (tangentNumerator f b)) := by
  apply Ideal.Quotient.eq.mpr
  rw [scaledFlow_apply, pderiv_last_lift, mul_zero, add_zero, partialFlow_lift]
  refine Ideal.mem_span_singleton'.mpr ⟨liftRaw (pderiv 2 b), ?_⟩
  simp only [graphRaw, tangentNumerator, liftSep, separant, map_sub, map_mul]
  ring

private theorem scaledFlow_sep (f : Row 3) :
    scaledFlow f (liftSep f) = liftSep f * partialFlow (liftSep f) := by
  rw [scaledFlow_apply, pderiv_last_lift, mul_zero, add_zero]

private theorem scaledFlow_scaled (f : Row 3) (k : ℕ) (b : Row 4) :
    scaledFlow f (3 * liftSep f ^ (k + 1) * b) =
      3 * liftSep f ^ (k + 1) * scaledFlow f b +
        3 * (↑(k + 1) : Row 4) * liftSep f ^ (k + 1) * partialFlow (liftSep f) * b := by
  have h3 : scaledFlow f 3 = 0 := scaledFlow_natCast f 3
  rw [scaledFlow_mul, scaledFlow_mul f 3, h3, zero_mul, add_zero, scaledFlow_pow, scaledFlow_sep,
    pow_succ (liftSep f) k]
  ring

/-- The two recurrences give the same cleared numerator modulo the graph equation. -/
private theorem rawComparison (f : Row 3) (k : ℕ) :
    classOf f (3 * liftSep f ^ (k + 1) * thirdNumerator f k) =
      classOf f (liftRaw (compatibilityNumerator f k)) := by
  induction k with
  | zero =>
    apply Ideal.Quotient.eq.mpr
    refine Ideal.mem_span_singleton'.mpr ⟨1, ?_⟩
    simp only [one_mul, thirdNumerator, compatibilityNumerator, zero_add, pow_one, map_neg, graphRaw]
    ring
  | succ k ih =>
    let s := liftSep f
    let b := thirdNumerator f k
    let A := compatibilityNumerator f k
    let q := classOf f
    have h : q (3 * s ^ (k + 1) * b) = q (liftRaw A) := ih
    have hD := (scaledFlow_congr f h).trans (scaledFlow_lift f A)
    have hs := scaledFlow_lift f (separant f)
    change q (scaledFlow f (3 * s ^ (k + 1) * b)) = q (liftRaw (tangentNumerator f A)) at hD
    change q (scaledFlow f s) = q (liftRaw (tangentNumerator f (separant f))) at hs
    calc
      q (3 * s ^ (k + 1 + 1) * liftedStep f k b) =
          q (s * scaledFlow f (3 * s ^ (k + 1) * b) -
            (↑(2 * k + 1) : Row 4) * (3 * s ^ (k + 1) * b) * scaledFlow f s) := by
        congr 1
        rw [liftedStep, scaledFlow_scaled, scaledFlow_sep, scaledFlow_apply, pow_succ s (k + 1)]
        push_cast
        ring
      _ = q (liftRaw (compatibilityNumerator f (k + 1))) := by
        rw [map_sub q, map_mul q, map_mul q, map_mul q, hD, h, hs]
        simp only [compatibilityNumerator, map_sub, map_mul, map_natCast]
        rfl

private theorem genericRow_mem_graphIdeal (f : Row 3) {P : Row 4} (h : P ∈ rawGraphIdeal f) :
    genericRow P ∈ graphIdeal f := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h
  rw [← hb, genericRow, map_mul]
  change genericRow b * genericRow (graphRaw f) ∈ graphIdeal f
  rw [generic_graph]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

private theorem represents (f : Row 3) (k : ℕ) :
    RepresentsOnGraph f (compatibilityNumerator f k) (genericRow (thirdNumerator f k)) := by
  have h := genericRow_mem_graphIdeal f (Ideal.Quotient.eq.mp (rawComparison f k))
  change MvPolynomial.map genericCoeff (_ - _) ∈ graphIdeal f at h
  rw [map_sub, map_mul, map_mul, map_pow, map_ofNat] at h
  change 3 * genericRow (liftSep f) ^ (k + 1) * genericRow (thirdNumerator f k) -
    genericRow (liftRaw (compatibilityNumerator f k)) ∈ graphIdeal f at h
  rw [generic_lift, generic_lift] at h
  let c := genericCoeff thirdConstant
  have h3 : 3 * c = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg genericCoeff three_mul_thirdConstant
  have hc : c ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h3
    exact zero_ne_one h3
  have hC : (3 : GeoRow 4) * MvPolynomial.C c = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (MvPolynomial.C : GeometricX →+* GeoRow 4) h3
  refine ⟨0, k + 1, c, hc, ?_⟩
  simp only [pow_zero, one_mul]
  convert Ideal.mul_mem_left (graphIdeal f) (MvPolynomial.C c) h using 1
  rw [mul_sub, ← mul_assoc (MvPolynomial.C c), ← mul_assoc (MvPolynomial.C c), mul_comm (MvPolynomial.C c) 3,
    hC, one_mul]

theorem proof : K1_13_5_4_1.c2 := by
  intro f _ _
  exact ⟨represents f (taylorLength - 3), represents f (taylorLength - 2)⟩

end

end K1_13_5_4_1_2
end PackSource_K1_13_5_4_1_2Proof

section PackSource_K1_13_4_4_2Proof
set_option autoImplicit true
namespace K1_13_4_4_2

noncomputable section

open K1 K1_13 K1_13_4 K1_13_4_4
open scoped Polynomial BigOperators

/-- Translate one coordinate by a formal increment, keeping the coefficients
and all other coordinates fixed. -/
private def line {R : Type*} [CommSemiring R] (i : SeedVar) :
    SeedRow R →+* (SeedRow R)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun j =>
    Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0

private theorem line_C {R : Type*} [CommSemiring R] (i : SeedVar) (r : R) :
    line i (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  simp [line]

private theorem line_X {R : Type*} [CommSemiring R] (i j : SeedVar) :
    line i (MvPolynomial.X j : SeedRow R) =
      Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0 := by
  simp [line]

private theorem line_mul_X {R : Type*} [CommSemiring R] (i j : SeedVar) (F : SeedRow R) :
    line i (F * MvPolynomial.X j) =
      (if j = i then line i F * Polynomial.X else 0) +
        Polynomial.C (MvPolynomial.X j) * line i F := by
  rw [map_mul, line_X]
  by_cases h : j = i <;> simp [h, mul_add, mul_comm, add_comm]

private theorem line_zero {R : Type*} [CommSemiring R] (i : SeedVar) (F : SeedRow R) :
    (line i F).coeff 0 = F := by
  let ev := (Polynomial.constantCoeff (R := SeedRow R)).comp (line i)
  change ev F = (RingHom.id _) F
  have he : ev = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ev, line_C]
    · intro j
      by_cases h : j = i <;> simp [ev, line_X, h]
  rw [he]

private theorem line_one {R : Type*} [CommSemiring R] (i : SeedVar) (F : SeedRow R) :
    (line i F).coeff 1 = MvPolynomial.pderiv i F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [line_C]
  | add P Q hp hq => simp [hp, hq]
  | mul_X P j hp =>
    rw [line_mul_X, Polynomial.coeff_add, Polynomial.coeff_C_mul, hp, MvPolynomial.pderiv_mul]
    by_cases h : j = i
    · subst j
      simp only [ite_true, MvPolynomial.pderiv_X_self, mul_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, Polynomial.coeff_mul_X, line_zero, mul_comm]
      exact add_comm _ _
    · simp [h, MvPolynomial.pderiv_X_of_ne h, mul_comm]

private theorem line_coeff {R : Type*} [CommSemiring R] (i : SeedVar) (F : SeedRow R) (n : ℕ) :
    (line i F).coeff n = K1_13_4_3.hasse (Finsupp.single i n) F := by
  classical
  induction F using MvPolynomial.induction_on generalizing n with
  | C c =>
    cases n <;> simp [line_C, K1_13_4_3.partial_C, Finsupp.single_eq_zero]
  | add P Q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp, hq, K1_13_4_3.hasse,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | mul_X P j hp =>
    rw [line_mul_X, Polynomial.coeff_add, Polynomial.coeff_C_mul, hp, K1_13_4_3.partial_mul_X]
    by_cases h : j = i
    · subst j
      cases n with
      | zero => simp [mul_comm]
      | succ n =>
        have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
        simp only [ite_true, Polynomial.coeff_mul_X, hp, Finsupp.mem_support_iff,
          Finsupp.single_eq_same, ← Finsupp.single_tsub, Nat.succ_sub_one]
        rw [ite_eq_left hn, mul_comm (MvPolynomial.X i)]
    · simp [h, Finsupp.single_eq_of_ne h, mul_comm]

private theorem line_toGeneric (i : SeedVar) (F : PhysicalRow) (n : ℕ) :
    (line i (toGeneric F)).coeff n = toGeneric (mixedHasse (Finsupp.single i n) F) := by
  let g : PhysicalRow →+* GenericRow := MvPolynomial.map inclX
  let l := (line i).comp g
  let r := (Polynomial.mapRingHom g).comp (line i)
  have he : l = r := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [l, r, g, line_C, Polynomial.coe_mapRingHom]
    · intro j
      by_cases h : j = i <;> simp [l, r, g, line_X, h, Polynomial.coe_mapRingHom]
  have h : line i (toGeneric F) = (line i F).map g := DFunLike.congr_fun he F
  rw [h, Polynomial.coeff_map, line_coeff, K1_13_4_3.partial_eq_mixedHasse]
  rfl

/-- A positive coordinate degree below the characteristic gives a proper
first partial. Its leading coefficient in that coordinate survives, and its
degree drops. -/
private theorem transverse {f : GenericRow} {i : SeedVar}
    (hpos : 0 < f.degreeOf i) (hsmall : f.degreeOf i < K1.p) :
    ¬ f ∣ (line i f).coeff 1 := by
  classical
  rw [line_one]
  have hdeg : (MvPolynomial.pderiv i f).degreeOf i ≤ f.degreeOf i - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    have hd := MvPolynomial.le_degreeOf_of_mem_support i (MvPolynomial.mem_support_iff.mpr
      (left_ne_zero_of_mul hm))
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hd
    omega
  have hnz : MvPolynomial.pderiv i f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m i) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    have hup : 0 < u i := hsup.trans_le htop
    have hult := (MvPolynomial.le_degreeOf_of_mem_support i hu).trans_lt hsmall
    let m := u - Finsupp.single i 1
    have hsum : m + Finsupp.single i 1 = u :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hup)
    have hm : (m i).succ = u i := by
      change m i + 1 = u i
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using
        congrArg (fun a : SeedVar →₀ ℕ => a i) hsum
    let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
    let _ : CharP GenericX K1.p := charP_of_injective_ringHom inclConst.injective K1.p
    have hcast : (↑(u i) : GenericX) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hup ((CharP.cast_eq_zero_iff GenericX K1.p _).mp hz))
    have hcoeff : (MvPolynomial.pderiv i f).coeff m ≠ 0 := by
      rw [MvPolynomial.coeff_pderiv, ← Nat.cast_succ, hm, hsum]
      exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hu) hcast
    intro hz
    exact hcoeff (by simp [hz])
  rintro ⟨g, hg⟩
  have hne : f ≠ 0 ∧ g ≠ 0 := by simpa [hg] using hnz
  rw [hg, MvPolynomial.degreeOf_mul_eq hne.1 hne.2] at hdeg
  omega

/-- Modulo the prime factor, the first surviving coefficient of a row of exact
factor exponent a is the a-th power of the linear coefficient times the cofactor. -/
private theorem exact_coeff {R : Type*} [CommRing R]
    (T : R →+* R[X]) (hzero : ∀ G, (T G).coeff 0 = G)
    {f P : R} {a : ℕ} (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (ha : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) :
    ¬ f ∣ (T P).coeff a := by
  obtain ⟨U, rfl⟩ := ha
  have hu : ¬ f ∣ U := by
    rintro ⟨V, rfl⟩
    exact hexact ⟨V, by rw [pow_succ, mul_assoc]⟩
  let J := Ideal.span ({f} : Set R)
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  let reduce := Ideal.Quotient.mk J
  let tr := (Polynomial.mapRingHom reduce).comp T
  have hz (G : R) : reduce G = 0 ↔ f ∣ G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hc (G : R) (n : ℕ) : (tr G).coeff n = reduce ((T G).coeff n) :=
    Polynomial.coeff_map _ _
  have hc₀ (G : R) : (tr G).coeff 0 = reduce G := by rw [hc, hzero]
  obtain ⟨V, hV⟩ := Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0 = 0 by rw [hc₀]; exact (hz _).mpr dvd_rfl)
  have hfirst : V.coeff 0 = reduce ((T f).coeff 1) := by
    rw [← hc, hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr : reduce ((T (f ^ a * U)).coeff a) = reduce ((T f).coeff 1) ^ a * reduce U := by
    rw [← hc, map_mul, map_pow, hV, mul_pow, mul_assoc]
    have he := Polynomial.coeff_X_pow_mul (V ^ a * tr U) a 0
    rw [zero_add] at he
    rw [he]
    change Polynomial.constantCoeff (V ^ a * tr U) = _
    rw [map_mul, map_pow]
    change (V.coeff 0) ^ a * (tr U).coeff 0 = _
    rw [hfirst, hc₀]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hz _).not.mpr hsep)) ((hz _).not.mpr hu))
    (hr.symm.trans ((hz _).mpr h))

private theorem pow_dvd_of_coeff {R : Type*} [CommRing R]
    (T : R →+* R[X]) (hzero : ∀ G, (T G).coeff 0 = G)
    {f P : R} (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (n : ℕ) (htest : ∀ a < n, f ∣ (T P).coeff a) : f ^ n ∣ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih fun a ha => htest a (Nat.lt_succ_of_lt ha)
    by_contra hexact
    exact exact_coeff T hzero hf hsep hn hexact (htest n (Nat.lt_succ_self n))

private theorem positive_jet_degree {f : GenericRow} (hf : 0 < jetTotal f) :
    ∃ j : Fin 3, 0 < f.degreeOf (some j) := by
  classical
  by_contra h
  apply (not_le_of_gt hf)
  rw [jetTotal, MvPolynomial.weightedTotalDegree]
  apply Finset.sup_le
  intro m hm
  apply le_of_eq
  rw [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro i _
  cases i with
  | none => simp
  | some j =>
    have hj₀ : f.degreeOf (some j) ≤ 0 :=
      Nat.le_of_not_gt fun hj => h ⟨j, hj⟩
    have hj := (MvPolynomial.le_degreeOf_of_mem_support (some j) hm).trans hj₀
    simp [Nat.eq_zero_of_le_zero hj]

private theorem choose_coordinate {moving : Bool} {A : Finset GenericRow}
    (hA : FactorsFor moving A) {F f : GenericRow} (hF : F ≠ 0) (hcap : Caps secondBox F)
    (hf : f ∈ A) (hd : f ∣ F) :
    ∃ i : SeedVar, (∀ n, mixedWeight (Finsupp.single i n) = n * reserveCost moving) ∧
      ¬ f ∣ (line i f).coeff 1 := by
  classical
  cases moving with
  | false =>
    obtain ⟨j, hj⟩ := positive_jet_degree (hA.jets f hf)
    have hjet : jetTotal f ≤ 6820 :=
      (MvPolynomial.weightedTotalDegree_le_of_dvd _ hd hF).trans hcap.1
    have hdeg : f.degreeOf (some j) ≤ jetTotal f :=
      MvPolynomial.degreeOf_le_weightedTotalDegree
        (fun i : SeedVar => i.elim 0 (fun _ => 1)) (some j) Nat.one_pos f
    refine ⟨some j, ?_, transverse hj (hdeg.trans_lt (hjet.trans_lt (by decide)))⟩
    intro n
    simp [mixedWeight, reserveCost, Finsupp.sum_single_index, mul_comm]
  | true =>
    have hs : 0 < seedDegree f := hA.seed f hf
    have hdeg : seedDegree f ≤ 70000 := by
      simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
        (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hd hF).trans
          (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hcap.2.2.2)
    refine ⟨none, ?_, transverse hs (hdeg.trans_lt (by decide))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]

theorem proof : K1_13_4_4.c2 := by
  classical
  intro moving A F t hA hcap ht htest
  by_cases hF : toGeneric F = 0
  · rw [hF]
    exact dvd_zero _
  unfold factorProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro f hf g hg hfg
    refine IsRelPrime.pow ((hA.irreducible f hf).isRelPrime_iff_not_dvd.mpr ?_)
    intro hd
    exact hA.different hf hg hfg ((hA.irreducible f hf).associated_of_dvd (hA.irreducible g hg) hd)
  · intro f hf
    have hdiv : f ∣ toGeneric F := by
      simpa [mixedWeight, mixedHasse_zero] using htest f hf 0 (by simpa [mixedWeight] using ht)
    obtain ⟨i, hi, hsep⟩ := choose_coordinate hA hF (toGeneric_caps hcap) hf hdiv
    apply pow_dvd_of_coeff (line i) (line_zero i)
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hA.irreducible f hf)) hsep
    intro a ha
    rw [line_toGeneric]
    apply htest f hf
    rw [hi]
    have ha' : a ≤ (secondCut - t) / reserveCost moving := by
      unfold layerPower at ha
      omega
    have hm := (Nat.mul_le_mul_right (reserveCost moving) ha').trans
      (Nat.div_mul_le_self (secondCut - t) (reserveCost moving))
    omega

end

end K1_13_4_4_2
end PackSource_K1_13_4_4_2Proof

section PackSource_K1_13_5_4_2_3_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_3_2

noncomputable section

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_3 MvPolynomial

/-- A prime above the cut that misses the inverted element extends to the open chart. -/
private theorem exists_open_prime {R : Type*} [CommRing R] {I P : Ideal R}
    [P.IsPrime] {s : R} (hIP : I ≤ P) (hs : s ∉ P) :
    ∃ q : Ideal (OpenRing I s), q.IsPrime ∧ q.comap (onOpen I s) = P := by
  let p := P.map (Ideal.Quotient.mk I)
  have hp : p.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hcomap : p.comap (Ideal.Quotient.mk I) = P := by
    change (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIP]
  let M := Submonoid.powers (Ideal.Quotient.mk I s)
  have hM : Disjoint (M : Set (R ⧸ I)) (p : Set (R ⧸ I)) := by
    have hle : M ≤ p.primeCompl := Submonoid.powers_le.mpr (by
      change s ∉ p.comap (Ideal.Quotient.mk I)
      rwa [hcomap])
    exact Set.disjoint_left.mpr fun _ ha hb => hle ha hb
  let q := p.map (algebraMap (R ⧸ I) (OpenRing I s))
  refine ⟨q, IsLocalization.isPrime_of_isPrime_disjoint M _ p hp hM, ?_⟩
  rw [onOpen, ← Ideal.comap_comap]
  change (q.under (R ⧸ I)).comap (Ideal.Quotient.mk I) = P
  rw [show q.under (R ⧸ I) = p from
    IsLocalization.under_map_of_isPrime_disjoint M _ hp hM, hcomap]

/-- Cutting and localizing at a prime on the open chart gives the same ring
as localizing the ambient ring at its contraction and imposing the cut there. -/
private def openAtPrimeEquivQuotient {R : Type*} [CommRing R] {I P : Ideal R}
    [P.IsPrime] {s : R} (q : Ideal (OpenRing I s)) [q.IsPrime]
    (hP : q.comap (onOpen I s) = P) :
    Localization.AtPrime q ≃+*
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  let p := q.comap (algebraMap (R ⧸ I) (OpenRing I s))
  letI : p.IsPrime := Ideal.comap_isPrime _ q
  have hp : p.comap (Ideal.Quotient.mk I) = P := hP
  let A := Localization.AtPrime P
  let C := A ⧸ I.map (algebraMap R A)
  have hmonoid : Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl = p.primeCompl := by
    change P.primeCompl.map (Ideal.Quotient.mk I) = p.primeCompl
    simpa only [hp] using
      p.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : IsLocalization p.primeCompl C := hmonoid ▸
    (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl) C)
  letI : IsLocalization p.primeCompl (Localization.AtPrime q) := by
    change IsLocalization.AtPrime (Localization.AtPrime q)
      (q.comap (algebraMap (R ⧸ I) (OpenRing I s)))
    infer_instance
  exact (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime q) C).toRingEquiv

/-- Colength is the length of the quotient ring as a module over itself,
and a ring equivalence identifies the two lattices of ideals. -/
private theorem colength_eq_of_quotient_equiv {A B : Type*} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B} (e : (A ⧸ I) ≃+* (B ⧸ J)) :
    Module.length A (A ⧸ I) = Module.length B (B ⧸ J) := by
  rw [Module.length_eq_of_surjective (R := A ⧸ I) Ideal.Quotient.mk_surjective,
    Module.length_eq_of_surjective (R := B ⧸ J) Ideal.Quotient.mk_surjective]
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm

theorem proof : K1_13_5_4_2_3.c2 := by
  intro f T e he P Q _ _ _ hQ _ hsQ hQP
  obtain ⟨q, hprime, hq⟩ := exists_open_prime hQ hsQ
  let : q.IsPrime := hprime
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime _ q
  have hp : p.comap (oldMap f) = P := by
    ext b
    change e (oldMap f b) ∈ q ↔ b ∈ P
    rw [he]
    change liftRow b ∈ q.comap (graphMap f T) ↔ b ∈ P
    rw [hq]
    change b ∈ Q.comap (rename Fin.castSucc).toRingHom ↔ b ∈ P
    rw [hQP]
  exact colength_eq_of_quotient_equiv
    ((openAtPrimeEquivQuotient p hp).symm.trans
      ((Localization.localRingEquiv p q e rfl).trans (openAtPrimeEquivQuotient q hq)))

end

end K1_13_5_4_2_3_2
end PackSource_K1_13_5_4_2_3_2Proof

section PackSource_K1_13_6_3_5_3_5Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_3_5

open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5_3 Polynomial
open scoped Polynomial WithZero

private theorem algebraic_over_parameter {k F : Type} [Field k] [Field F] [Algebra k F]
    (hF : CurveField k F) {x : F} (hx : Transcendental k x) (y : F) :
    IsAlgebraic (IntermediateField.adjoin k {x}) y := by
  obtain ⟨t, ht, hfinite⟩ := hF
  let := hfinite
  have halg (z : F) : IsAlgebraic (Algebra.adjoin k {t}) z :=
    IntermediateField.isAlgebraic_adjoin_iff.mp
      (Algebra.IsAlgebraic.isAlgebraic (R := IntermediateField.adjoin k {t}) z)
  have ht' : IsAlgebraic (Algebra.adjoin k {x}) t := by
    simpa using IsAlgebraic.adjoin_singleton ht hx (halg x)
  rw [IntermediateField.isAlgebraic_adjoin_iff]
  apply IsAlgebraic.adjoin_of_forall_isAlgebraic (s := {t}) (t := {x}) _ (halg y)
  intro z hz
  have hzt : z = t := hz.1
  simpa only [hzt] using ht'

private theorem residue_zero_iff {F : Type} [Field F] (w : Valuation F ℤᵐ⁰)
    (x : w.valuationSubring) :
    IsLocalRing.residue w.valuationSubring x = 0 ↔ w (x : F) < 1 :=
  (IsLocalRing.residue_eq_zero_iff x).trans (w.mem_maximalIdeal_iff (a := x))

/-- A nontrivial place of the old curve has residue field equal to its constants. -/
private theorem residue_constant {k F : Type} [Field k] [IsAlgClosed k]
    [Field F] [Algebra k F] (hF : CurveField k F) (w : Valuation F ℤᵐ⁰)
    (hk : w.IsTrivialOn k) (hn : ∃ y : F, y ≠ 0 ∧ w y ≠ 1)
    (x : F) (hx : w x ≤ 1) :
    ∃ c : k, w (x - algebraMap k F c) < 1 := by
  let : w.IsTrivialOn k := hk
  let A := w.valuationSubring
  let ι : k →+* A := (algebraMap k F).codRestrict A
    (fun c => Valuation.IsTrivialOn.valuation_algebraMap_le_one w c)
  let ρ := IsLocalRing.residue A
  let : Algebra k (IsLocalRing.ResidueField A) := (ρ.comp ι).toAlgebra
  let u : A := ⟨x, hx⟩
  have hres : IsAlgebraic k (ρ u) := by
    by_contra htrans
    have hpoly (p : k[X]) (hp : p ≠ 0) : w (aeval x p) = 1 := by
      let z := p.eval₂ ι u
      have hz : (z : F) = aeval x p := Polynomial.hom_eval₂ p ι A.subtype u
      have hzres : ρ z ≠ 0 := by
        intro hzero
        apply htrans
        refine ⟨p, hp, ?_⟩
        change p.eval₂ (ρ.comp ι) (ρ u) = 0
        rw [← Polynomial.hom_eval₂ p ι ρ u]
        exact hzero
      rw [← hz]
      exact le_antisymm z.2 (le_of_not_gt fun hlt => hzres ((residue_zero_iff w z).2 hlt))
    have htr : Transcendental k x := by
      rintro ⟨p, hp, hzero⟩
      have he := hpoly p hp
      rw [hzero, map_zero] at he
      exact zero_ne_one he
    let B := IntermediateField.adjoin k {x}
    let : w.IsTrivialOn B := ⟨by
      intro b hb
      have hb' : (b : F) ≠ 0 := fun h => hb (Subtype.ext h)
      obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff k (b : F)).1 b.2
      have hp : p ≠ 0 := fun h => hb' (by simp [hpq, h])
      have hq : q ≠ 0 := fun h => hb' (by simp [hpq, h])
      change w (b : F) = 1
      rw [hpq, w.map_div, hpoly p hp, hpoly q hq, div_self one_ne_zero]⟩
    obtain ⟨y, hy, hvy⟩ := hn
    exact (Valuation.transcendental_of_ne_one B (v := w) y hy hvy)
      (algebraic_over_parameter hF htr y)
  let B := IntermediateField.adjoin k {ρ u}
  let : Algebra.IsAlgebraic k B :=
    IntermediateField.isAlgebraic_adjoin_simple (isAlgebraic_iff_isIntegral.mp hres)
  have hB := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic B
  have hu : ρ u ∈ (⊥ : IntermediateField k (IsLocalRing.ResidueField A)) :=
    hB ▸ IntermediateField.mem_adjoin_simple_self k (ρ u)
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hu
  refine ⟨c, (residue_zero_iff w (u - ι c)).1 ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr hc.symm

/-- Normalize by a largest coefficient and compare with its residue polynomial. -/
private theorem gauss_of_residue_constants {k F L : Type} [Field k] [Field F]
    [Algebra k F] [Field L] (j : F →+* L) (a : L) (v : Valuation L ℤᵐ⁰)
    (ha : v a = 1)
    (hres : ∀ x : F, v (j x) ≤ 1 → ∃ c : k, v (j (x - algebraMap k F c)) < 1)
    (hfresh : ∀ q : k[X], q ≠ 0 → v (q.eval₂ (j.comp (algebraMap k F)) a) = 1)
    (g : F[X]) :
    v (g.eval₂ j a) = g.support.sup (fun i => v (j (g.coeff i))) := by
  classical
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_mem_eq_sup g.support (nonempty_support_iff.mpr hg)
      (fun i => v (j (g.coeff i)))
  let b := g.coeff m
  have hb : b ≠ 0 := mem_support_iff.mp hm
  have hvb : 0 < v (j b) := v.pos_iff.mpr ((map_ne_zero j).2 hb)
  let d (i : ℕ) := g.coeff i / b
  have hd (i : ℕ) : v (j (d i)) ≤ 1 := by
    by_cases hi : i ∈ g.support
    · dsimp only [d]
      rw [map_div₀, v.map_div, div_le_one₀ hvb]
      change v (j (g.coeff i)) ≤ v (j (g.coeff m))
      rw [← hmax]
      exact Finset.le_sup (f := fun n => v (j (g.coeff n))) hi
    · simp [d, notMem_support_iff.mp hi]
  choose c hc using fun i => hres (d i) (hd i)
  have hcm : c m ≠ 0 := by
    intro hz
    have h := hc m
    simp [d, b, hb, hz] at h
  let q : k[X] := ∑ i ∈ g.support, monomial i (c i)
  have hqcoeff : q.coeff m = c m := by
    simp [q, finsetSum_coeff, coeff_monomial, hm]
  have hq : q ≠ 0 := fun h => hcm (by simpa [h] using hqcoeff.symm)
  let r := j.comp (algebraMap k F)
  let s := ∑ i ∈ g.support, j (d i) * a ^ i
  have hqeval : q.eval₂ r a = ∑ i ∈ g.support, r (c i) * a ^ i := by
    simp only [q, eval₂_finsetSum, eval₂_monomial]
  have hdiff : v (s - q.eval₂ r a) < 1 := by
    dsimp only [s]
    rw [hqeval, ← Finset.sum_sub_distrib]
    apply v.map_sum_lt one_ne_zero
    intro i _
    rw [← sub_mul, map_mul, map_pow, ha, one_pow, mul_one]
    change v (j (d i) - j (algebraMap k F (c i))) < 1
    rw [← map_sub]
    exact hc i
  have hqv := hfresh q hq
  have hdom : v (s - q.eval₂ r a) < v (q.eval₂ r a) := lt_of_lt_of_eq hdiff hqv.symm
  have hs : v s = 1 := (v.map_eq_of_sub_lt hdom).trans hqv
  have hscale : g.eval₂ j a = j b * s := by
    dsimp only [s]
    rw [eval₂_eq_sum, sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [d]
    rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hb]
  rw [hscale, map_mul, hs, mul_one]
  exact hmax.symm

theorem proof : K1_13_6_3_5_3.c5 := by
  intro R D v
  unfold FreshGauss
  by_cases h : ∀ x : D.Old, x ≠ 0 → v.value (D.includeOld x) = 1
  · exact Or.inl h
  right
  let w := v.value.comap D.includeOld
  have hk : w.IsTrivialOn Geom := ⟨by
    intro c hc
    change v.value ((D.includeOld.comp (algebraMap Geom D.Old)) c) = 1
    rw [D.constants]
    exact v.on_constants (geomConstants c) ((map_ne_zero geomConstants).2 hc)⟩
  have hn : ∃ y : D.Old, y ≠ 0 ∧ w y ≠ 1 := by
    obtain ⟨y, hy⟩ := not_forall.mp h
    exact ⟨y, (Classical.not_imp.mp hy).1, (Classical.not_imp.mp hy).2⟩
  have hfresh (q : Geom[X]) (hq : q ≠ 0) :
      v.value (q.eval₂ (D.includeOld.comp (algebraMap Geom D.Old)) D.center) = 1 := by
    have heval : q.eval₂ (D.includeOld.comp (algebraMap Geom D.Old)) D.center =
        algebraMap GeoField D.Fresh (genericCoeffs q) := by
      rw [D.constants, FreshCurve.center, ← Polynomial.hom_eval₂,
        geomConstants, genericArgument, ← Polynomial.hom_eval₂, eval₂_C_X]
    have hginj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp
        (IsFractionRing.injective Geom[X] GenericField)
    rw [heval]
    exact v.on_constants _ (map_ne_zero_iff genericCoeffs hginj |>.2 hq)
  have ha : v.value D.center = 1 := by
    simpa only [eval₂_X] using hfresh Polynomial.X Polynomial.X_ne_zero
  exact gauss_of_residue_constants D.includeOld D.center v.value ha
    (residue_constant D.oldCurve w hk hn) hfresh

end K1_13_6_3_5_3_5
end PackSource_K1_13_6_3_5_3_5Proof

section PackSource_K1_11_2_2AuxGraph
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace K1_11_2_2
noncomputable section

open MvPolynomial K1_11_2

variable {F : Type*} [Field F]

/-- Evaluate the X-coordinate while retaining the two formal parameters. -/
def parameterNode (x : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4]

theorem nodeWord_omits (x a b c d : F) (Q : MvPolynomial (Fin 5) F)
    (hQ : OmitsMessages Q) : nodeWordMap x a b c d Q = parameterNode x Q := by
  change eval₂ C (nodeWordImages x a b c d) Q = eval₂ C ![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4] Q
  apply eval₂_congr
  intro i e hi hc
  have ht := omitted_message_tag Q hQ e (mem_support_iff.mpr hc)
  have hin := Finsupp.mem_support_iff.mp hi
  fin_cases i <;> simp_all [nodeWordImages]

/-- Substitute the formal parameters by Z and Z^q after evaluating X. -/
def seedEval (q : ℕ) : MvPolynomial (Fin 5) F →ₐ[F] Polynomial F :=
  aeval ![0, 0, 0, Polynomial.X, Polynomial.X ^ q]

theorem eval_graph (q : ℕ) (x : F) (Q : MvPolynomial (Fin 5) F) :
    (graph q Q).eval (Polynomial.C x) = seedEval q (parameterNode x Q) := by
  have heq : (Polynomial.evalRingHom (Polynomial.C x)).comp (graph (F := F) q).toRingHom =
      (seedEval q).toRingHom.comp (parameterNode x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [graph, seedEval, parameterNode, Polynomial.algebraMap_apply]
    · intro i
      fin_cases i <;> simp [graph, seedEval, parameterNode]
  exact RingHom.congr_fun heq Q

end
end K1_11_2_2
end PackSource_K1_11_2_2AuxGraph

section PackSource_K1_14_3R_1Taylor
set_option autoImplicit true
namespace K1_14_3R_1

open K1_14_3 Polynomial

/-- Each summand in the Taylor expansion either vanishes or contains a
product of the two point generators of total exponent at least k. -/
theorem fibre_pow_of_hasse (F : FibreJet) (y v : SeedClosure) (k : ℕ)
    (h : ∀ a b : ℕ, a + b < k →
      (hasseDeriv a ((hasseDeriv b F).eval (C v))).eval y = 0) :
    F ∈ fibrePoint y v ^ k := by
  let I := fibrePoint y v
  let yDiff := Polynomial.X (R := SeedClosure) - C y
  let vDiff := Polynomial.X (R := Polynomial SeedClosure) - C (C v)
  have hY : C yDiff ∈ I := Ideal.subset_span (by simp [yDiff])
  have hV : vDiff ∈ I := Ideal.subset_span (by simp [vDiff])
  suffices hsum : (taylor (C v) F).sum (fun b B => C B * vDiff ^ b) ∈ I ^ k by
    simpa only [vDiff, sum_taylor_eq] using hsum
  unfold Polynomial.sum
  apply Ideal.sum_mem
  intro b _
  let B := (taylor (C v) F).coeff b
  change C B * vDiff ^ b ∈ I ^ k
  have hB : (taylor y B).sum (fun a c => C c * yDiff ^ a) = B :=
    sum_taylor_eq B y
  rw [← hB]
  unfold Polynomial.sum
  rw [map_sum, Finset.sum_mul]
  apply Ideal.sum_mem
  intro a _
  rw [map_mul, map_pow, mul_assoc]
  by_cases hab : a + b < k
  · have hc : (taylor y B).coeff a = 0 := by
      simpa only [B, taylor_coeff] using h a b hab
    simp [hc]
  · apply Ideal.mul_mem_left
    apply Ideal.pow_le_pow_right (le_of_not_gt hab)
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hY a) (Ideal.pow_mem_pow hV b)

end K1_14_3R_1
end PackSource_K1_14_3R_1Taylor
