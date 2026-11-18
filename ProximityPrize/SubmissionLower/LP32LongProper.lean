/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,066 errors, right cap 165 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.LP32ProperCount
import ProximityPrize.SubmissionLower.Koala6831IntrinsicWeightedAffine
import ProximityPrize.SubmissionLower.LP32WeightedLiteral

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped BigOperators
open MvPolynomial RCN002 RCN044 RCN135 RCN136 RCN234 RCN341

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option Elab.async false

variable {K : Type} [Field K] [CharP K 2130706433] {A : Type} [Fintype A]

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K

def longProperCurveCost_lp32 (gy gt gz : ℕ) : ℕ :=
  5505046 * (52166458 * gz + gt * 43253595) +
    46661810 * (5505004 * gz + gy * 43253595) +
    43253925 * (5505004 * (gt - gy) + gy * 52166458)

theorem long_proper_selected_count_lp32
    (F : Carrier K) (hp : Nat.Prime 2130706433) (hF : Irreducible F)
    (hY : wt ![0, 1, 0, 0] F ≤ 22)
    (hT : wt ![0, 1, 1, 0] F ≤ 200)
    (hZ : wt ![0, 0, 0, 1] F ≤ 165)
    (G : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hproper : ¬ G ∣ surfaceMap φ (tailNumerator F 131071))
    (gy gt gz : ℕ) (hyt : gy ≤ gt) (hy : gy ≤ 22) (ht : gt ≤ 200) (hz : gz ≤ 165)
    (hGy : G.degreeOf 0 ≤ gy) (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ gt)
    (hGz : G.degreeOf 2 ≤ gz)
    (component : A → LongTailRegularComponent_lp32 F 131071 G) (hinj : Function.Injective component)
    (hnonpersistent : ∀ i, ¬ ∀ j,
      surfaceMap φ (tailNumerator F (131071 + j)) ∈ (component i).1)
    (S : A → Finset (Fin 3 → Ω))
    (hpoint : ∀ i, ∀ v ∈ S i, (component i).1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hreg : ∀ i, ∀ v ∈ S i, MvPolynomial.aeval v (surfaceMap φ (implicitRegularity F)) ≠ 0)
    (hroot : ∀ i, ∀ v ∈ S i, ∀ j,
      MvPolynomial.aeval v (surfaceMap φ (tailNumerator F (131071 + j))) = 0) :
    (∑ i, (S i).card) ≤ longProperCurveCost_lp32 gy gt gz := by
  classical
  letI : CharP Ω 2130706433 := genericField_charP K 2130706433
  obtain ⟨hTy, hTt, hTz⟩ := long_first_tail_caps_lp32 F hY hT hZ
  let charts (i : A) := curveChartData_of_regularComponent F 131071 hF hdiv hproper (component i)
  have caps : LongLiteralSeedCaps_lp32 G (surfaceMap φ (tailNumerator F 131071)) :=
    ⟨hGy.trans hy, hTy, hGz.trans hz, hTz, fun d hd => (hGt d hd).trans ht, hTt⟩
  choose seed hseed using fun i =>
    exists_long_literal_seed_projection_lp32 F 131071 hdiv hG hproper caps (component i)
  let W (i : A) := literalRelevantPlaces (seed i)
  let μ (i : A) := curveTailOrder F 131071 (component i).1 (charts i)
  have hU := intrinsic_affine_weighted_pole_bound_all F 131071 2130706433 hp
    G hG hdiv hproper component hinj charts seed hseed W
    gt 52166458 gz 43253595 hGt hTt hGz hTz (hz.trans_lt (by decide)) (by decide)
  have hZ₀ := intrinsic_literal_weighted_pole_bound_lp32 F 131071 hp
    hdiv hG hproper caps component hinj charts W false gy gt gz hyt hGy hGt hGz
  have hZ₁ := intrinsic_literal_weighted_pole_bound_lp32 F 131071 hp
    hdiv hG hproper caps component hinj charts W true gy gt gz hyt hGy hGt hGz
  have hcount (i : A) :=
    proper_tail_curve_point_count_lp32 F 131071 2130706433 hp (component i).1
      (charts i) (seed i) (hnonpersistent i) 5505046 52166856 43253925 22 200 165
      (by decide) (by decide) (by decide) hY hT hZ (by decide) (by decide) (by decide)
      (S i) (hpoint i) (hreg i) (hroot i)
  have hZ₁' : (∑ i, (μ i : ℤ) * ∑ v ∈ W i,
      RCN187.poleOrder v.val (coordinate Ω (component i).1 2)) ≤
      ((5505004 * (gt - gy) + gy * 52166458 : ℕ) : ℤ) := by
    have he : 5505004 * gt + gy * 52166458 - 5505004 * gy =
        5505004 * (gt - gy) + gy * 52166458 := by
      rw [Nat.mul_sub]
      omega
    simpa [show longSeedOrder_lp32 true 0 = 2 by decide, he, μ, W] using hZ₁
  exact sum_point_counts_le_long_flag_poles_lp32 (K := K)
    (fun i => CoordinateField Ω (component i).1) W (fun i => coordinate Ω (component i).1)
    μ (fun i => (S i).card) 5505046 52166856 43253925 _ _ _
    (by decide) hcount hU
    (by simpa [show longSeedOrder_lp32 false 0 = 1 by decide] using hZ₀) hZ₁'

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
