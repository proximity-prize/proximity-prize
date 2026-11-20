/- Joint projection accounting at 68.36, derived from the pinned 68.33 source. -/
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from the frozen 68.32 submission of Bome2017, building on Lucieno
(PR 618) and BitWonka (PRs 581 and 582). KoalaBear 68.33 long branch, November 18. -/
/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,66 errors, right cap 168 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.KB36JSepLongProper
import ProximityPrize.SubmissionLower.KB36JSepLongPersistent
import ProximityPrize.SubmissionLower.KB36JSepLongBudget

namespace ProximityPrize.SubmissionLower.KB36JFactorCount
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
    (hT : wt ![0, 1, 1, 0] F ≤ 197)
    (hZ : wt ![0, 0, 0, 1] F ≤ 168)
    (G : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hproper : ¬ G ∣ surfaceMap φ (tailNumerator F w))
    (gy gt gz : ℕ) (hyt : gy ≤ gt) (hy : gy ≤ 22) (ht : gt ≤ 197) (hz : gz ≤ 168)
    (hGy : G.degreeOf 0 ≤ gy) (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ gt)
    (hGz : G.degreeOf 2 ≤ gz)
    (bound e : ℕ) (hw : w + 1 ≤ bound) (hchar : bound < p₀) (he : e ≤ 81105)
    (hweight : wt ![1, w, 0, 0] F < bound)
    (x : I ↪ K) (u₀ u₁ : I → K) (nodes : Finset I)
    (hAn : 181039 ≤ nodes.card) (haverage : nodeAverage nodes.card w 181039 ≤ 3)
    (allSeeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ allSeeds, (selected g).natDegree ≤ w)
    (hagreements : ∀ g ∈ allSeeds, 181039 ≤
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
  have hn := long_proper_selected_joint F hp hF hY hT hZ G hG hdiv hproper gy gt gz hyt hy ht hz
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
  let chart (i : C) := curveChartData_of_regularComponent F w hF hdiv hproper i
  let mass (j : Fin 3) (i : C) := curveTailOrder F w i.1 (chart i) * actualCoordinateDegree Ω i.1 j
  have split (f : C → ℕ) : (∑ c : C, f c) = (∑ c : P, f c.1) + ∑ c : N, f c.1 := by
    calc
      _ = (∑ c ∈ Finset.univ.filter persistent, f c) +
          ∑ c ∈ Finset.univ.filter (fun c => ¬ persistent c), f c :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ persistent f).symm
      _ = _ := by
        apply congrArg₂ (· + ·)
        · simpa only [P, Finset.subtype_univ] using
            (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset C)) f (p := persistent)).symm
        · simpa only [N, Finset.subtype_univ] using
            (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset C)) f (p := fun c => ¬ persistent c)).symm
  have shared (j : Fin 3) : (∑ i : P, actualCoordinateDegree Ω i.1.1 j) +
      (∑ i : N, mass j i.1) ≤ ∑ i : C, mass j i := by
    rw [split]
    apply Nat.add_le_add_right
    apply Finset.sum_le_sum
    intro i _
    exact (Nat.one_mul _).symm.le.trans (Nat.mul_le_mul_right _ (hμ i))
  have all0 := intrinsic_literal_weighted_degree_bound_lp32 F w hp hdiv hG hproper caps
    (fun i : C => i) Function.injective_id chart false gy gt gz hyt hGy hGt hGz
  have all1 := intrinsic_literal_weighted_degree_bound_lp32 F w hp hdiv hG hproper caps
    (fun i : C => i) Function.injective_id chart true gy gt gz hyt hGy hGt hGz
  have hsum₀ : (∑ i : P, deg₀ i) + (∑ i : N, mass 1 i.1) ≤ 5505004 * gz + gy * 44040024 := by
    apply (shared 1).trans
    simpa [mass, show longSeedOrder_lp32 false 0 = 1 by decide] using all0
  have hsum₁ : (∑ i : P, deg₁ i) + (∑ i : N, mass 2 i.1) ≤ 5505004 * (gt-gy) + gy * 51380029 := by
    apply (shared 2).trans
    have he : 5505004 * gt + gy * 51380029 - 5505004 * gy = 5505004 * (gt - gy) + gy * 51380029 := by
      rw [Nat.mul_sub]
      omega
    simpa [mass, he, show longSeedOrder_lp32 true 0 = 2 by decide] using all1
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
  have hcover := selected_card_le_sum_componentPoints F w p₀ G seeds selected hsize hroot hregular
    (fun g hg => (hmem g hg).2.1)
  change (∑ i : N, (points i.1).card) ≤
      5505046 * (51380029 * gz + gt * 44040024) + 45875375 * (∑ i : N, mass 1 i.1) +
      44040360 * (∑ i : N, mass 2 i.1) at hn
  change (∑ i : P, (points i.1).card) ≤ 81700 * ((∑ i : P, deg₀ i) + ∑ i : P, deg₁ i) at hP
  change seeds.card ≤ _
  apply hcover.trans
  change (∑ i : C, (points i).card) ≤ longFactorCharge_lp32 gy gt gz
  rw [split, longFactorCharge_eq_lp32 gy gt gz hyt]
  omega

end

end ProximityPrize.SubmissionLower.KB36JFactorCount

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
