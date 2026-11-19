/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from the frozen 68.32 submission of Bome2017, building on Lucieno
(PR 618) and BitWonka (PRs 581 and 582). KoalaBear 68.33 long branch, November 18. -/
/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,66 errors, right cap 167 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.Mid6833K6833SepLongProper
import ProximityPrize.SubmissionLower.Mid6833K6833SepLongPersistent
import ProximityPrize.SubmissionLower.Mid6833K6833SepLongBudget

namespace ProximityPrize.SubmissionLower.K6833FactorCount
open Koala6831Intrinsic

open scoped Classical BigOperators Polynomial
open MvPolynomial RCN002 RCN007 RCN135 RCN136 RCN234 RCN341 Koala6831OrdinaryIncidence

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option Elab.async false

variable {K I : Type} [Field K] [CharP K 2130706433]

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K
local notation "w" => 131071
local notation "p₀" => 2130706433

theorem long_proper_first_tail_factor_count_lp32
    (F : Carrier K) (hp : Nat.Prime p₀) (hF : Irreducible F)
    (hY : wt ![0, 1, 0, 0] F ≤ 22)
    (hT : wt ![0, 1, 1, 0] F ≤ 198)
    (hZ : wt ![0, 0, 0, 1] F ≤ 167)
    (G : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hproper : ¬ G ∣ surfaceMap φ (tailNumerator F w))
    (gy gt gz : ℕ) (hyt : gy ≤ gt) (hy : gy ≤ 22) (ht : gt ≤ 198) (hz : gz ≤ 167)
    (hGy : G.degreeOf 0 ≤ gy) (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ gt)
    (hGz : G.degreeOf 2 ≤ gz)
    (bound e : ℕ) (hw : w + 1 ≤ bound) (hchar : bound < p₀) (he : e ≤ 81095)
    (hweight : wt ![1, w, 0, 0] F < bound)
    (x : I ↪ K) (u₀ u₁ : I → K) (nodes : Finset I)
    (hAn : 181049 ≤ nodes.card) (haverage : nodeAverage nodes.card w 181049 ≤ 3)
    (allSeeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ allSeeds, (selected g).natDegree ≤ w)
    (hagreements : ∀ g ∈ allSeeds, 181049 ≤
      (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (RCN050.pencilSeeds allSeeds selected P₀ P₁).card ≤ e + 1) :
    (longFactorSeeds_lp32 F G allSeeds selected).card ≤ longFactorCharge_lp32 gy gt gz := by
  classical
  letI : CharP Ω p₀ := genericField_charP K p₀
  let C := FirstTailComponent F w G
  let persistent (c : C) : Prop := ∀ j, surfaceMap φ (tailNumerator F (w + j)) ∈ c.1
  let P := {c : C // persistent c}
  let N := {c : C // ¬ persistent c}
  letI : Fintype P := inferInstanceAs (Fintype {c : C // persistent c})
  letI : Fintype N := inferInstanceAs (Fintype {c : C // ¬ persistent c})
  let seeds := longFactorSeeds_lp32 F G allSeeds selected
  have hmem (g : K) (hg : g ∈ seeds) := Finset.mem_filter.mp hg
  have hsize (g : K) (hg : g ∈ seeds) := hdegree g (hmem g hg).1
  have hroot (g : K) (hg : g ∈ seeds) := (hmem g hg).2.2.1
  have hregular (g : K) (hg : g ∈ seeds) := (hmem g hg).2.2.2
  let points := selectedComponentPoints F w p₀ G seeds selected
  have hspec (c : C) := selectedComponentPoints_spec F w p₀ G seeds selected c hsize hroot hregular
  have hn : (∑ c : N, (points c.1).card) ≤ longProperCurveCost_lp32 gy gt gz :=
    long_proper_selected_count_lp32 F hp hF hY hT hZ G hG hdiv hproper gy gt gz hyt hy ht hz
      hGy hGt hGz (fun c : N => c.1) Subtype.val_injective (fun c => c.2)
      (fun c => points c.1) (fun c v hv => (hspec c.1 v hv).1)
      (fun c v hv => (hspec c.1 v hv).2.1) (fun c v hv => (hspec c.1 v hv).2.2)
  obtain ⟨hTy, hTt, hTz⟩ := long_first_tail_caps_lp32 F hY hT hZ
  have caps : LongLiteralSeedCaps_lp32 G (surfaceMap φ (tailNumerator F w)) :=
    ⟨hGy.trans hy, hTy, hGz.trans hz, hTz, fun d hd => (hGt d hd).trans ht, hTt⟩
  let charts (c : P) := curveChartData_of_regularComponent F w hF hdiv hproper c.1
  let base (c : P) := (exists_long_literal_seed_projection_lp32 F w hdiv hG hproper caps c.1).choose
  let deg₀ (c : P) := actualCoordinateDegree Ω c.1.1 1
  let deg₁ (c : P) := actualCoordinateDegree Ω c.1.1 2
  let μ (c : P) := curveTailOrder F w c.1.1 (charts c)
  have hμ (c : P) : 1 ≤ μ c := (curve_intrinsic_tail_dichotomy F w p₀ hp c.1.1 (charts c)).1
  have hU₀ := intrinsic_literal_weighted_degree_bound_lp32 F w hp hdiv hG hproper caps
    (fun c : P => c.1) Subtype.val_injective charts false gy gt gz hyt hGy hGt hGz
  have hU₁ := intrinsic_literal_weighted_degree_bound_lp32 F w hp hdiv hG hproper caps
    (fun c : P => c.1) Subtype.val_injective charts true gy gt gz hyt hGy hGt hGz
  have hsum₀ : (∑ c : P, deg₀ c) ≤ 5505004 * gz + gy * 43777881 := by
    calc
      _ ≤ ∑ c : P, μ c * deg₀ c := Finset.sum_le_sum fun c _ =>
        by simpa only [one_mul] using Nat.mul_le_mul_right (deg₀ c) (hμ c)
      _ ≤ _ := by simpa [μ, deg₀, show longSeedOrder_lp32 false 0 = 1 by decide] using hU₀
  have heq₁ : 5505004 * gt + gy * 51642172 - 5505004 * gy =
      5505004 * (gt - gy) + gy * 51642172 := by
    rw [Nat.mul_sub]
    omega
  have hsum₁ : (∑ c : P, deg₁ c) ≤ 5505004 * (gt - gy) + gy * 51642172 := by
    calc
      _ ≤ ∑ c : P, μ c * deg₁ c := Finset.sum_le_sum fun c _ =>
        by simpa only [one_mul] using Nat.mul_le_mul_right (deg₁ c) (hμ c)
      _ ≤ _ := by simpa [μ, deg₁, heq₁, show longSeedOrder_lp32 true 0 = 2 by decide] using hU₁
  have hP := long_persistent_selected_sum_le_of_degree_lp32 F G bound e hw hchar he hweight hT hZ
    (fun c : P => c.1) charts base (fun c => c.2) deg₀ deg₁
    (fun c => long_literal_seed_degrees_pos_lp32 F G hdiv hG hproper caps c.1)
    (fun c W => by
      simpa only [show longSeedOrder_lp32 false 0 = 1 by decide] using
        long_literal_pole_le_actual_degree_lp32 F G hdiv hG hproper caps c.1 false W)
    (fun c W => by
      simpa only [show longSeedOrder_lp32 true 0 = 2 by decide] using
        long_literal_pole_le_actual_degree_lp32 F G hdiv hG hproper caps c.1 true W)
    x u₀ u₁ nodes hAn haverage seeds allSeeds (fun g hg => (hmem g hg).1)
    selected hsize hroot hregular (fun g hg => hagreements g (hmem g hg).1) hpencil
  have hsplit : (∑ c : C, (points c).card) =
      (∑ c : P, (points c.1).card) + ∑ c : N, (points c.1).card := by
    calc
      _ = (∑ c ∈ Finset.univ.filter persistent, (points c).card) +
          ∑ c ∈ Finset.univ.filter (fun c => ¬ persistent c), (points c).card :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ persistent (fun c => (points c).card)).symm
      _ = _ := by
        apply congrArg₂ (· + ·)
        · simpa only [P, Finset.subtype_univ] using
            (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset C))
              (fun c => (points c).card) (p := persistent)).symm
        · simpa only [N, Finset.subtype_univ] using
            (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset C))
              (fun c => (points c).card) (p := fun c => ¬ persistent c)).symm
  have hcover := selected_card_le_sum_componentPoints F w p₀ G seeds selected hsize hroot hregular
    (fun g hg => (hmem g hg).2.1)
  change seeds.card ≤ _
  calc
    _ ≤ (∑ c : C, (points c).card) := hcover
    _ ≤ 81693 * ((5505004 * gz + gy * 43777881) +
        (5505004 * (gt - gy) + gy * 51642172)) + longProperCurveCost_lp32 gy gt gz := by
      rw [hsplit]
      exact Nat.add_le_add (hP.trans (Nat.mul_le_mul_left _ (Nat.add_le_add hsum₀ hsum₁))) hn
    _ ≤ longFactorCharge_lp32 gy gt gz := by
      rw [longFactorCharge_eq_lp32 gy gt gz hyt, longProperCurveCost_lp32]
      have h : 0 ≤ 1067484004626 * gy := Nat.zero_le _
      omega

end

end ProximityPrize.SubmissionLower.K6833FactorCount

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
