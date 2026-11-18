/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. The cumulative-direction identities build on the accepted 68.32 argument.
This version credits final factors retained through a whole group of adaptive passes. -/
import ProximityPrize.SubmissionLower.Mid6833GroupCore
namespace ProximityPrize.SubmissionLower.K6833Group
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN156 RCN238 RCN243 RCN263 RCN266 RCN275 RCN313 RCN319
open K6833FlowSources K6833FlowStages K6833FlowAdaptive K6833FlowPaid
open Koala6831Moving Koala6831MovingLedger Koala6831MovingPairIncidence
open LocatorBatchProductRoute (regularProduct regularProduct_ne_zero)
open LocatorFactorAggregate LocatorLowQuotient
open LocatorPhase6800Oracle (sumFlag sumFlag_all sumFlag_middle sumFlag_total)
noncomputable section
set_option maxRecDepth 30000
variable {K : Type} [Field K]
local instance mid6833Local_GroupCredit_15  : DecidableEq K := Classical.decEq _
private theorem direction_cumulative (P : ResidualSupportParameters) :
    (reducedAgreementDirection P).all = 2 * P.s - 2 ∧
      middle (reducedAgreementDirection P) = 2 * P.ys - 2 ∧
      total (reducedAgreementDirection P) = 2 * P.total - 2 := by
  have hs := P.one_le_s
  have hy := P.s_le_ys
  have ht := P.ys_le_total
  simp only [reducedAgreementDirection, middle, total, true_and]
  omega

private theorem direction_mono {f g : FlagDegree} (hf : 0 < f.all) (hg : 0 < g.all)
    (hfg : Below f g) :
    Below (reducedAgreementDirection (stageSupport f hf))
      (reducedAgreementDirection (stageSupport g hg)) := by
  obtain ⟨hr, hy, ht⟩ := hfg
  obtain ⟨hrf, hyf, htf⟩ := direction_cumulative (stageSupport f hf)
  obtain ⟨hrg, hyg, htg⟩ := direction_cumulative (stageSupport g hg)
  unfold Below
  rw [hrf, hrg, hyf, hyg, htf, htg]
  have hy' := max_le_max_left 2 hy
  have ht' := max_le_max_left 2 ht
  change _ ∧ (2 * max 2 (middle f) - 2 ≤ 2 * max 2 (middle g) - 2) ∧
    (2 * max 2 (total f) - 2 ≤ 2 * max 2 (total g) - 2)
  exact ⟨by simpa only [stageSupport] using Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 2,
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hy') 2,
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 ht') 2⟩

private theorem below_scaled_add {f g : FlagDegree} (hfg : Below f g)
    (k : ℕ) (p q : FlagDegree) : Below (k • f + p + q) (k • g + p + q) := by
  obtain ⟨hr, hy, ht⟩ := hfg
  simp only [Below, middle, total, add_all, add_yz, add_zOnly, nsmul_all, nsmul_yz, nsmul_zOnly]
  have hS := Nat.mul_le_mul_left k hr
  have hY := Nat.mul_le_mul_left k hy
  have hT := Nat.mul_le_mul_left k ht
  simp only [middle, total, Nat.mul_add] at hY hT
  omega

theorem stagePrice_mono {f g : FlagDegree} (hf : 0 < f.all) (hg : 0 < g.all)
    (hfg : Below f g) (s : Stage) (gain : ℕ) :
    stagePrice f hf s gain ≤ stagePrice g hg s gain := by
  unfold stagePrice
  apply Nat.div_le_div_right
  apply (mixed_mono_first hfg _ _).trans
  apply mixed_mono_third
  unfold stageScaledCut scaledPairFlag
  exact below_scaled_add (direction_mono hf hg hfg) _ _ _

private theorem flag_eq_of_cumulative {a b : FlagDegree}
    (hR : a.all = b.all) (hY : middle a = middle b) (hT : total a = total b) : a = b := by
  cases a with
  | mk za ya ra =>
    cases b with
    | mk zb yb rb =>
      simp only [middle, total] at hR hY hT
      have hy : ya = yb := by omega
      have hz : za = zb := by omega
      cases hR; cases hy; cases hz
      rfl

private theorem sumFlag_split {ι : Type} [DecidableEq ι] {A R : Finset ι} (hR : R ⊆ A)
    (flag : ι → FlagDegree) : sumFlag (A \ R) flag + sumFlag R flag = sumFlag A flag := by
  apply flag_eq_of_cumulative
  · simpa only [add_all, sumFlag_all] using Finset.sum_sdiff (f := fun i => (flag i).all) hR
  · have hmiddle (P Q : FlagDegree) : middle (P + Q) = middle P + middle Q := by
      simp only [middle, add_yz, add_all]
      omega
    simpa only [hmiddle, sumFlag_middle] using Finset.sum_sdiff (f := fun i => middle (flag i)) hR
  · have htotal (P Q : FlagDegree) : total (P + Q) = total P + total Q := by
      simp only [total, add_zOnly, add_yz, add_all]
      omega
    simpa only [htotal, sumFlag_total] using Finset.sum_sdiff (f := fun i => total (flag i)) hR


def credit (s : Stage) (f : FlagDegree) : ℕ :=
  if h : 0 < f.all then
    flagMixed (creditFlag f) (stagePartnerFlag s s.numbers.slopeCap)
      (stageScaledCut (creditFlag f) h) / agreementScale
  else 0

theorem bill [DecidableEq K] (s : Stage) (H : P4 K) (A U final : Finset (RegularIndex H))
    (sub : U⊆A) (last : final⊆U) (seeds : RegularIndex H→Finset K)
    (pos : 0<(aggregateFlag H A).all)
    (cnt : ∀ F∈A\U,(seeds F).card≤flagMixed (contactFlag F.1) (stagePartnerFlag s s.numbers.slopeCap)
      (stageScaledCut (aggregateFlag H A) pos) / agreementScale) :
    ((A\U).biUnion seeds).card + credit s (aggregateFlag H final) ≤
      stagePrice (aggregateFlag H A) pos s s.numbers.slopeCap := by
  classical
  let f := aggregateFlag H final
  let g := aggregateFlag H A
  let z := creditFlag f
  have zf : Below z f := by simp [z,creditFlag,Below,middle,total]
  have zU := transBelow zf (aggregateFlag_mono H last)
  have zg := transBelow zU (aggregateFlag_mono H sub)
  have split : sumFlag (A\U) (fun i=>contactFlag i.1) + aggregateFlag H U = g := by
    change sumFlag (A\U) (fun i=>contactFlag i.1) + contactFlag (regularProduct H U) = contactFlag (regularProduct H A)
    rw [contactFlag_regularProduct,contactFlag_regularProduct,sumFlag_split sub]
  have invoice := IntermediateCredit.full_credit (A\U) (fun i=>contactFlag i.1) seeds z (aggregateFlag H U) g
    (stagePartnerFlag s s.numbers.slopeCap) (stageScaledCut g pos) agreementScale_pos zU
    (by rw [split];exact ⟨le_rfl,le_rfl,le_rfl⟩) cnt
  have save : credit s (aggregateFlag H final)≤flagMixed z (stagePartnerFlag s s.numbers.slopeCap) (stageScaledCut g pos)/agreementScale := by
    unfold credit
    split
    next h =>
      apply Nat.div_le_div_right
      apply mixed_mono_third
      unfold stageScaledCut scaledPairFlag
      exact below_scaled_add (direction_mono (f:=z) (g:=g) h pos zg) _ _ _
    next => exact Nat.zero_le _
  exact (Nat.add_le_add_left save _).trans invoice
#print axioms bill
end
end ProximityPrize.SubmissionLower.K6833Group
