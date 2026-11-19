/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from the frozen 68.32 submission of Bome2017, building on Lucieno
(PR 618) and BitWonka (PRs 581 and 582). KoalaBear 68.33 long branch, November 18. -/
/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,66 errors, right cap 167 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.Koala6831IntrinsicNativeFactors
import ProximityPrize.SubmissionLower.Koala6831IntrinsicSelectedComponents
import ProximityPrize.SubmissionLower.Koala6831BenchmarkRetention

namespace ProximityPrize.SubmissionLower.K6833FactorCount
open Koala6831Intrinsic

open MvPolynomial RCN081 RCN135 RCN136 RCN137
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false

def longFactorCharge_lp32 (y t z : ℕ) : ℕ :=
  ((46137520 + 81683) * 43777881 +
    (43778215 + 81683) * (51642172 - 5505004) + 1067484004616) * y +
  (5505046 * 43777881 + (43778215 + 81683) * 5505004) * t +
  (5505046 * 51642172 + (46137520 + 81683) * 5505004) * z

theorem longFactorCharge_eq_lp32 (y t z : ℕ) (hyt : y ≤ t) :
    longFactorCharge_lp32 y t z =
      5505046 * (51642172 * z + t * 43777881) +
      (46137520 + 81683) * (5505004 * z + y * 43777881) +
      (43778215 + 81683) * (5505004 * (t - y) + y * 51642172) + 1067484004616 * y := by
  unfold longFactorCharge_lp32
  rw [show t = (t - y) + y by omega]
  rw [Nat.add_sub_cancel]
  ring

theorem sum_longFactorCharge_le_lp32 {J : Type*} (S : Finset J) (y t z : J → ℕ)
    (ycap tcap zcap : ℕ) (hy : (∑ a ∈ S, y a) ≤ ycap) (ht : (∑ a ∈ S, t a) ≤ tcap)
    (hz : (∑ a ∈ S, z a) ≤ zcap) :
    (∑ a ∈ S, longFactorCharge_lp32 (y a) (t a) (z a)) ≤ longFactorCharge_lp32 ycap tcap zcap := by
  simp only [longFactorCharge_lp32, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hy) (Nat.mul_le_mul_left _ ht))
    (Nat.mul_le_mul_left _ hz)

theorem long_geometric_allowances_le_retained_lp32 :
    2130706433 * (2 * 22 + 2) * 365 + longFactorCharge_lp32 22 198 167
      ≤ 274584715711948448 := by
  decide +kernel

variable {K : Type} [Field K]

theorem long_native_caps_of_support_lp32 (F : Carrier K)
    (hcap : ∀ d ∈ F.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 198 ∧ d 3 ≤ 167 ∧
      d 0 + 131071 * d 1 < 4000000) :
    RCN234.wt ![0, 1, 0, 0] F ≤ 22 ∧ RCN234.wt ![0, 1, 1, 0] F ≤ 198 ∧
      RCN234.wt ![0, 0, 0, 1] F ≤ 167 ∧ RCN234.wt ![1, 131071, 0, 0] F < 4000000 := by
  have hle (v : Fin 4 → ℕ) (cap : ℕ)
      (h : ∀ d ∈ F.support, Finsupp.weight v d ≤ cap) : RCN234.wt v F ≤ cap :=
    (RCN081.weightedTotalDegree_le_iff v F cap).mpr h
  refine ⟨hle _ _ ?_, hle _ _ ?_, hle _ _ ?_, lt_of_le_of_lt (hle _ 3999999 ?_) (by decide)⟩
  · intro d hd
    simpa [weight_fin4] using (hcap d hd).1
  · intro d hd
    simpa [weight_fin4] using (hcap d hd).2.1
  · intro d hd
    simpa [weight_fin4] using (hcap d hd).2.2.1
  · intro d hd
    have h := (hcap d hd).2.2.2
    simpa [weight_fin4, Nat.mul_comm] using (Nat.le_of_lt_succ h)

theorem long_native_factor_caps_lp32 (Q F : Carrier K) (hQ : Q ≠ 0)
    (hF : F ∈ normalizedFactorSet Q)
    (hcap : ∀ d ∈ Q.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 198 ∧ d 3 ≤ 167 ∧
      d 0 + 131071 * d 1 < 4000000) :
    RCN234.wt ![0, 1, 0, 0] F ≤ 22 ∧ RCN234.wt ![0, 1, 1, 0] F ≤ 198 ∧
      RCN234.wt ![0, 0, 0, 1] F ≤ 167 ∧ RCN234.wt ![1, 131071, 0, 0] F < 4000000 := by
  obtain ⟨hy, ht, hz, hcode⟩ := long_native_caps_of_support_lp32 Q hcap
  exact ⟨(native_factor_weight_le _ Q F hQ hF).trans hy,
    (native_factor_weight_le _ Q F hQ hF).trans ht,
    (native_factor_weight_le _ Q F hQ hF).trans hz,
    (native_factor_weight_le _ Q F hQ hF).trans_lt hcode⟩

def longMiddleDegree_lp32 (G : MvPolynomial (Fin 3) (GenericField K)) : ℕ :=
  weightedTotalDegree ![1, 1, 0] G

private theorem surface_middle_degree_le_lp32 (F : Carrier K) :
    longMiddleDegree_lp32 (surfaceMap (polynomialEmbedding K) F) ≤
      weightedTotalDegree (Fin.cases 0 ![1, 1, 0]) F := by
  unfold longMiddleDegree_lp32 weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset (polynomialEmbedding K) F hd)
  have h := MvPolynomial.le_weightedTotalDegree (Fin.cases 0 ![1, 1, 0]) he
  rw [RCN372.weight_fin3]
  rw [weight_fin4] at h
  change e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ weightedTotalDegree (Fin.cases 0 ![1, 1, 0]) F
  change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ _ at h
  simpa only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] using h

theorem long_native_seed_support_lp32 (F : Carrier K)
    (ht : RCN234.wt ![0, 1, 1, 0] F ≤ 198) (hz : RCN234.wt ![0, 0, 0, 1] F ≤ 167) :
    ∀ d ∈ F.support, d 2 ≤ 198 ∧ d 3 ≤ 167 := by
  intro d hd
  have ht' := (MvPolynomial.le_weightedTotalDegree ![0, 1, 1, 0] hd).trans ht
  have hz' := (MvPolynomial.le_weightedTotalDegree ![0, 0, 0, 1] hd).trans hz
  rw [weight_fin4] at ht' hz'
  exact ⟨(Nat.le_add_left _ _).trans (by simpa using ht'), by simpa using hz'⟩

theorem long_geometric_factor_caps_lp32 (F : Carrier K) (hF : F ≠ 0)
    (G : MvPolynomial (Fin 3) (GenericField K)) (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hy : RCN234.wt ![0, 1, 0, 0] F ≤ 22) (ht : RCN234.wt ![0, 1, 1, 0] F ≤ 198)
    (hz : RCN234.wt ![0, 0, 0, 1] F ≤ 167) :
    G.degreeOf 0 ≤ 22 ∧ longMiddleDegree_lp32 G ≤ 198 ∧ G.degreeOf 2 ≤ 167 ∧
      G.degreeOf 0 ≤ longMiddleDegree_lp32 G ∧ ∀ d ∈ G.support, d 0 + d 1 ≤ longMiddleDegree_lp32 G := by
  let φ := polynomialEmbedding K
  have hsurface := surfaceMap_ne_zero φ (polynomialEmbedding_injective K) F hF
  have hy' : F.degreeOf 1 ≤ 22 := MvPolynomial.degreeOf_le_iff.mpr (fun d hd => by
    have h := (MvPolynomial.le_weightedTotalDegree ![0, 1, 0, 0] hd).trans hy
    rw [weight_fin4] at h
    simpa using h)
  have hz' : F.degreeOf 3 ≤ 167 :=
    MvPolynomial.degreeOf_le_iff.mpr (fun d hd => (long_native_seed_support_lp32 F ht hz d hd).2)
  have hmid (d : Fin 3 →₀ ℕ) (hd : d ∈ G.support) : d 0 + d 1 ≤ longMiddleDegree_lp32 G := by
    have h := MvPolynomial.le_weightedTotalDegree (![1, 1, 0] : Fin 3 → ℕ) hd
    rw [RCN372.weight_fin3] at h
    change d 0 * 1 + d 1 * 1 + d 2 * 0 ≤ longMiddleDegree_lp32 G at h
    simpa only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] using h
  have ht' : weightedTotalDegree (Fin.cases 0 ![1, 1, 0]) F ≤ 198 := by
    have heq : (Fin.cases 0 ![1, 1, 0] : Fin 4 → ℕ) = ![0, 1, 1, 0] := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact ht
  exact ⟨(coordinate_degree_le_of_dvd 0 G _ hdiv hsurface).trans
      ((surfaceMap_degreeOf_le φ F 0).trans hy'),
    (RCN071.weightedTotalDegree_le_of_dvd_fin3 ![1, 1, 0] G _ hdiv hsurface).trans
      ((surface_middle_degree_le_lp32 F).trans ht'),
    (coordinate_degree_le_of_dvd 2 G _ hdiv hsurface).trans
      ((surfaceMap_degreeOf_le φ F 2).trans hz'),
    MvPolynomial.degreeOf_le_iff.mpr (fun d hd => (Nat.le_add_right _ _).trans (hmid d hd)), hmid⟩

def longFactorSeeds_lp32 (F : Carrier K) (G : MvPolynomial (Fin 3) (GenericField K))
    (seeds : Finset K) (selected : K → Polynomial K) : Finset K :=
  seeds.filter fun g =>
    MvPolynomial.eval (selectedGraphPoint 2130706433 selected g) G = 0 ∧
    graphSpecialize (selected g) g (g ^ 2130706433) F = 0 ∧
    graphSpecialize (selected g) g (g ^ 2130706433) (implicitRegularity F) ≠ 0

private theorem geometric_long_charge_le_lp32 (F : Carrier K) (hF : F ≠ 0) :
    (∑ G ∈ surfaceFactors (polynomialEmbedding K) F,
      longFactorCharge_lp32 (G.degreeOf 0) (longMiddleDegree_lp32 G) (G.degreeOf 2)) ≤
      longFactorCharge_lp32 (F.degreeOf 1) (weightedTotalDegree (Fin.cases 0 ![1, 1, 0]) F) (F.degreeOf 3) := by
  let φ := polynomialEmbedding K
  let Q := surfaceMap φ F
  let S := surfaceFactors φ F
  have hQ : Q ≠ 0 := surfaceMap_ne_zero φ (polynomialEmbedding_injective K) F hF
  have hmid : (∑ G ∈ S, longMiddleDegree_lp32 G) ≤ weightedTotalDegree (Fin.cases 0 ![1, 1, 0]) F := by
    exact (RCN071.sum_weightedTotalDegree_le_of_prod_dvd_fin3 ![1, 1, 0] S id Q hQ
      (normalizedFactorSet_product_dvd Q hQ)).trans (surface_middle_degree_le_lp32 F)
  exact sum_longFactorCharge_le_lp32 S (fun G => G.degreeOf 0) longMiddleDegree_lp32 (fun G => G.degreeOf 2)
    _ _ _ (surfaceFactors_degree_budget φ (polynomialEmbedding_injective K) F hF 0) hmid
    (surfaceFactors_degree_budget φ (polynomialEmbedding_injective K) F hF 2)

theorem long_retained_seed_budget_of_factor_counts_lp32 [CharP K 2130706433]
    (Q : Carrier K) (hQ : Q ≠ 0)
    (hcap : ∀ d ∈ Q.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 198 ∧ d 3 ≤ 167)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hvanish : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ 2130706433) Q = 0)
    (hcount : ∀ F ∈ normalizedFactorSet Q, ∀ G ∈ surfaceFactors (polynomialEmbedding K) F,
      (longFactorSeeds_lp32 F G seeds selected).card ≤
        longFactorCharge_lp32 (G.degreeOf 0) (longMiddleDegree_lp32 G) (G.degreeOf 2)) :
    seeds.card ≤ 274584715711948448 := by
  classical
  let φ := polynomialEmbedding K
  let S := normalizedFactorSet Q
  let mid := (Fin.cases 0 ![1, 1, 0] : Fin 4 → ℕ)
  have hQY : Q.degreeOf 1 ≤ 22 :=
    MvPolynomial.degreeOf_le_iff.mpr (fun d hd => (hcap d hd).1)
  have hQT : weightedTotalDegree mid Q ≤ 198 := by
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 198
    simpa only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] using (hcap d hd).2.1
  have hQZ : Q.degreeOf 3 ≤ 167 :=
    MvPolynomial.degreeOf_le_iff.mpr (fun d hd => (hcap d hd).2.2)
  have htotal (d : Fin 4 →₀ ℕ) (hd : d ∈ Q.support) : d 1 ≤ 22 ∧ d 1 + d 2 + d 3 ≤ 365 := by
    have h := hcap d hd
    exact ⟨h.1, Nat.add_le_add h.2.1 h.2.2⟩
  obtain ⟨bad, hbad, hbadCount, hregular⟩ := native_regular_cover_after_singular_discard
    2130706433 Q hQ 22 365 (by decide) (by decide) (by decide) htotal seeds selected hvanish
  let onNative (F : Carrier K) := (surfaceFactors φ F).biUnion (fun G => longFactorSeeds_lp32 F G seeds selected)
  have hcover : seeds \ bad ⊆ S.biUnion onNative := by
    intro g hg
    obtain ⟨F, hF, hroot, hreg⟩ := hregular g hg
    have hi := (normalizedFactorSet_spec Q F hF).1
    have hsurface : MvPolynomial.eval (selectedGraphPoint 2130706433 selected g) (surfaceMap φ F) = 0 := by
      change MvPolynomial.eval (polynomialGraphSurfacePoint φ (selected g) g (g ^ 2130706433))
        (surfaceMap φ F) = 0
      rw [eval_polynomialGraphSurfacePoint, hroot, map_zero]
    obtain ⟨G, hG, hz⟩ := exists_surfaceFactor_zero φ (polynomialEmbedding_injective K) F hi.ne_zero _ hsurface
    exact Finset.mem_biUnion.mpr ⟨F, hF, Finset.mem_biUnion.mpr
      ⟨G, hG, Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hg).1, hz, hroot, hreg⟩⟩⟩
  have hnative (F : Carrier K) (hF : F ∈ S) :
      (onNative F).card ≤ longFactorCharge_lp32 (F.degreeOf 1) (weightedTotalDegree mid F) (F.degreeOf 3) := by
    calc
      _ ≤ ∑ G ∈ surfaceFactors φ F, (longFactorSeeds_lp32 F G seeds selected).card := Finset.card_biUnion_le
      _ ≤ ∑ G ∈ surfaceFactors φ F, longFactorCharge_lp32 (G.degreeOf 0) (longMiddleDegree_lp32 G) (G.degreeOf 2) :=
        Finset.sum_le_sum (hcount F hF)
      _ ≤ _ := geometric_long_charge_le_lp32 F (normalizedFactorSet_spec Q F hF).1.ne_zero
  have hgoodCount : (seeds \ bad).card ≤ longFactorCharge_lp32 22 198 167 := by
    calc
      _ ≤ (S.biUnion onNative).card := Finset.card_le_card hcover
      _ ≤ ∑ F ∈ S, (onNative F).card := Finset.card_biUnion_le
      _ ≤ ∑ F ∈ S, longFactorCharge_lp32 (F.degreeOf 1) (weightedTotalDegree mid F) (F.degreeOf 3) :=
        Finset.sum_le_sum hnative
      _ ≤ _ := sum_longFactorCharge_le_lp32 S (fun F => F.degreeOf 1) (weightedTotalDegree mid)
        (fun F => F.degreeOf 3) _ _ _
        ((normalizedFactorSet_degree_budget Q hQ 1).trans hQY)
        ((native_factor_weight_sum_le mid Q hQ).trans hQT)
        ((normalizedFactorSet_degree_budget Q hQ 3).trans hQZ)
  have hdecomp : (seeds \ bad).card + bad.card = seeds.card :=
    Finset.card_sdiff_add_card_eq_card hbad
  rw [← hdecomp, Nat.add_comm]
  exact (Nat.add_le_add hbadCount hgoodCount).trans long_geometric_allowances_le_retained_lp32

end

end ProximityPrize.SubmissionLower.K6833FactorCount

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
