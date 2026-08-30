import ProximityPrize.SubmissionLower.LocatorFixedStage
import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorFactorAggregate
import ProximityPrize.SubmissionLower.O0
import ProximityPrize.SubmissionLower.FQ
namespace ProximityPrize.SubmissionLower.LocatorFixed
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286
open RCN081 RCN135 RCN095
open RCN238 RCN243
open RCN222 RCN266
open RCN221
open RCN268 RCN140
open RCN275 RCN130
open RCN156 RCN159
open RCN234 RCN137
open RCN198 RCN263
open LocatorFactorAggregate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K 2130706433 := by
 simpa [RCN223.prime] using
   RCN128.challenge_field_characteristic6600
def padA (p : FlagDegree) : ℕ := padT p - padY p
def padB (p : FlagDegree) : ℕ := padY p - padS p - 1
def padSlope (p : FlagDegree) : ℕ := padS p - 2
theorem pad_sums (p : FlagDegree) :
   padSlope p + 2 = padS p ∧
   padB p + padSlope p + 3 = padY p ∧
   padA p + padB p + padSlope p + 3 = padT p := by
 have hs : 2 ≤ padS p := le_max_right _ _
 have hy : padS p + 1 ≤ padY p := le_max_right _ _
 have ht : padY p ≤ padT p := le_max_right _ _
 dsimp [padA, padB, padSlope]
 omega
theorem padded_tail_eq (p : FlagDegree) (d : ℕ) :
   reducedResidualAgreementFlag (RCN198.support (padA p) (padB p) (padSlope p)) d =
     paddedTail p d := by
 have hc := pad_sums p
 have hs : 2 ≤ padS p := le_max_right _ _
 simp only [reducedResidualAgreementFlag, reducedAgreementDirection,
   RCN198.support, hc.1, hc.2.1, hc.2.2, paddedTail]
 have he : 2 * padS p - 2 = 2 * (padS p - 1) := by omega
 rw [he]
def hybridPaddedCost (p : FlagDegree) : ℕ :=
 LocatorFixedStage.hybridStageCost p (padA p) (padB p) (padSlope p)
private theorem rationalFlag_mono {p q : FlagDegree} (h : Below p q) :
   Below
     (LocatorFixedStage.rationalFlag (padA p) (padB p) (padSlope p))
     (LocatorFixedStage.rationalFlag (padA q) (padB q) (padSlope q)) := by
 have hp := pad_sums p
 have hq := pad_sums q
 have hm := padding_mono h
 unfold Below middle total
 simp only [LocatorFixedStage.rationalFlag]
 norm_num [LocatorFixedStage.w]
 omega
private theorem movingFiberFlag_mono {p q : FlagDegree} (h : Below p q) :
   Below
     (LocatorFixedStage.movingFiberFlag (padA p) (padB p) (padSlope p))
     (LocatorFixedStage.movingFiberFlag (padA q) (padB q) (padSlope q)) := by
 have hp := pad_sums p
 have hq := pad_sums q
 have hm := padding_mono h
 unfold Below middle total
 simp only [LocatorFixedStage.movingFiberFlag]
 omega
private theorem movingCutFlag_mono {p q : FlagDegree} (h : Below p q) :
   Below
     (LocatorFixedStage.movingCutFlag (padA p) (padB p) (padSlope p))
     (LocatorFixedStage.movingCutFlag (padA q) (padB q) (padSlope q)) := by
 have hp := pad_sums p
 have hq := pad_sums q
 have hm := padding_mono h
 unfold Below middle total
 simp only [LocatorFixedStage.movingCutFlag]
 norm_num [LocatorFixedStage.w]
 omega
theorem hybridPaddedCost_mono {p q : FlagDegree} (h : Below p q) :
   hybridPaddedCost p ≤ hybridPaddedCost q := by
 have hfirst : Below
     (LocatorFixedStage.firstTail (padA p) (padB p) (padSlope p))
     (LocatorFixedStage.firstTail (padA q) (padB q) (padSlope q)) := by
   simpa only [LocatorFixedStage.firstTail, LocatorFixedStage.w,
     Nat.reduceAdd, padded_tail_eq] using paddedTail_mono 131072 h
 have hrational := rationalFlag_mono h
 have hfiber := movingFiberFlag_mono h
 have hcut := movingCutFlag_mono h
 unfold hybridPaddedCost LocatorFixedStage.hybridStageCost
 exact Nat.add_le_add
   ((mixed_mono_first h _ _).trans
     (mixed_mono_tails q hfirst hrational))
   (Nat.mul_le_mul_left _
     ((mixed_mono_first h _ _).trans
       (mixed_mono_tails q hfiber hcut)))
private theorem hybrid_affine_10 (t : ℕ) (ht : 60 ≤ t) :
   hybridPaddedCost (cap t 60 10) + 5205596661568200 =
     159844470233702 * t := by
 have hsub : t - 60 + 60 = t := Nat.sub_add_cancel ht
 norm_num [hybridPaddedCost, padA, padB, padSlope, padT, padY, padS,
   cap, middle, total, LocatorFixedStage.hybridStageCost,
   LocatorFixedStage.firstTail, LocatorFixedStage.tail_support_formula,
   LocatorFixedStage.rationalFlag, LocatorFixedStage.movingFiberFlag,
   LocatorFixedStage.movingCutFlag, LocatorFixedStage.w, flagMixed]
 ring_nf
 omega
private theorem hybrid_affine_11 (t : ℕ) (ht : 60 ≤ t) :
   hybridPaddedCost (cap t 60 11) + 5745174421152956 =
     175152006438076 * t := by
 have hsub : t - 60 + 60 = t := Nat.sub_add_cancel ht
 norm_num [hybridPaddedCost, padA, padB, padSlope, padT, padY, padS,
   cap, middle, total, LocatorFixedStage.hybridStageCost,
   LocatorFixedStage.firstTail, LocatorFixedStage.tail_support_formula,
   LocatorFixedStage.rationalFlag, LocatorFixedStage.movingFiberFlag,
   LocatorFixedStage.movingCutFlag, LocatorFixedStage.w, flagMixed]
 ring_nf
 omega
private theorem hybrid_affine_12 (t : ℕ) (ht : 60 ≤ t) :
   hybridPaddedCost (cap t 60 12) + 6281350506346032 =
     190150299492102 * t := by
 have hsub : t - 60 + 60 = t := Nat.sub_add_cancel ht
 norm_num [hybridPaddedCost, padA, padB, padSlope, padT, padY, padS,
   cap, middle, total, LocatorFixedStage.hybridStageCost,
   LocatorFixedStage.firstTail, LocatorFixedStage.tail_support_formula,
   LocatorFixedStage.rationalFlag, LocatorFixedStage.movingFiberFlag,
   LocatorFixedStage.movingCutFlag, LocatorFixedStage.w, flagMixed]
 ring_nf
 omega
private theorem hybrid_affine_13 (t : ℕ) (ht : 56 ≤ t) :
   hybridPaddedCost (cap t 56 13) + 5920995872323560 =
     189445904539340 * t := by
 have hsub : t - 56 + 56 = t := Nat.sub_add_cancel ht
 norm_num [hybridPaddedCost, padA, padB, padSlope, padT, padY, padS,
   cap, middle, total, LocatorFixedStage.hybridStageCost,
   LocatorFixedStage.firstTail, LocatorFixedStage.tail_support_formula,
   LocatorFixedStage.rationalFlag, LocatorFixedStage.movingFiberFlag,
   LocatorFixedStage.movingCutFlag, LocatorFixedStage.w, flagMixed]
 ring_nf
 omega
def fixedRegularCap6742 : ℕ := 273049439447551806
private theorem hybrid_rate_of_affine {t c top alpha deficit : ℕ}
   (ht : t ≤ 1469) (hc : c + deficit = alpha * t)
   (hTop : top + deficit = alpha * 1469)
   (hbound : top ≤ fixedRegularCap6742) :
   1469 * c ≤ fixedRegularCap6742 * t := by
 have hscaled : 1469 * c + deficit * t ≤ top * t + deficit * t := by
   calc
     _ ≤ 1469 * c + deficit * 1469 :=
       Nat.add_le_add_left (Nat.mul_le_mul_left deficit ht) _
     _ = (c + deficit) * 1469 := by ring
     _ = (alpha * t) * 1469 := by rw [hc]
     _ = (alpha * 1469) * t := by ring
     _ = (top + deficit) * t := by rw [← hTop]
     _ = top * t + deficit * t := by ring
 exact (Nat.le_of_add_le_add_right hscaled).trans
   (Nat.mul_le_mul_right t hbound)
private theorem hybrid_large_rate_10 (t : ℕ) (hlo : 60 ≤ t) (hhi : t ≤ 1469) :
   1469 * hybridPaddedCost (cap t 60 10) ≤ fixedRegularCap6742 * t := by
 exact hybrid_rate_of_affine hhi (hybrid_affine_10 t hlo)
   (hybrid_affine_10 1469 (by decide)) (by decide)
private theorem hybrid_large_rate_11 (t : ℕ) (hlo : 60 ≤ t) (hhi : t ≤ 1469) :
   1469 * hybridPaddedCost (cap t 60 11) ≤ fixedRegularCap6742 * t := by
 exact hybrid_rate_of_affine hhi (hybrid_affine_11 t hlo)
   (hybrid_affine_11 1469 (by decide)) (by decide)
private theorem hybrid_large_rate_12 (t : ℕ) (hlo : 60 ≤ t) (hhi : t ≤ 1469) :
   1469 * hybridPaddedCost (cap t 60 12) ≤ fixedRegularCap6742 * t := by
 exact hybrid_rate_of_affine hhi (hybrid_affine_12 t hlo)
   (hybrid_affine_12 1469 (by decide)) (by decide)
private theorem hybrid_large_rate_13 (t : ℕ) (hlo : 56 ≤ t) (hhi : t ≤ 1469) :
   1469 * hybridPaddedCost (cap t 56 13) ≤ fixedRegularCap6742 * t := by
 exact hybrid_rate_of_affine hhi (hybrid_affine_13 t hlo)
   (hybrid_affine_13 1469 (by decide)) (by decide)
private theorem hybrid_small_rate (s t : ℕ) (hs : 10 ≤ s) (hs13 : s ≤ 13)
   (hst : s ≤ t) (ht : t ≤ 60) :
   1469 * hybridPaddedCost (cap (max t (s + 1)) (max t (s + 1)) s) ≤
     fixedRegularCap6742 * t := by
 interval_cases s <;> interval_cases t <;>
   norm_num [hybridPaddedCost, fixedRegularCap6742, padA, padB, padSlope,
     padT, padY, padS, cap, middle, total,
     LocatorFixedStage.hybridStageCost, LocatorFixedStage.firstTail,
     LocatorFixedStage.tail_support_formula, LocatorFixedStage.rationalFlag,
     LocatorFixedStage.movingFiberFlag, LocatorFixedStage.movingCutFlag,
     LocatorFixedStage.w, flagMixed] at *
theorem rate_bound_high_6742 (p : FlagDegree)
   (hs : 10 ≤ p.all) (hs13 : p.all ≤ 13)
   (hy : middle p ≤ 60) (ht : total p ≤ 1469)
   (h13 : p.all = 13 → middle p ≤ 56) :
   1469 * hybridPaddedCost p ≤ fixedRegularCap6742 * total p := by
 have hst : p.all ≤ total p := all_le_total p
 have hcases : p.all = 10 ∨ p.all = 11 ∨ p.all = 12 ∨ p.all = 13 := by omega
 rcases hcases with hs10 | hs11 | hs12 | hs13eq
 · by_cases hlarge : 60 ≤ total p
   · have hb := below_cap_of_bounds p (total p) 60 10 (by decide) hlarge
       (by omega) hy (le_refl _)
     exact (Nat.mul_le_mul_left 1469 (hybridPaddedCost_mono hb)).trans
       (hybrid_large_rate_10 (total p) hlarge ht)
   · let u := max (total p) 11
     have hb := below_cap_of_bounds p u u 10 (by simp [u]) (le_refl _)
       (by omega) (by dsimp [u]; exact (middle_le_total p).trans (le_max_left _ _))
       (by dsimp [u]; exact le_max_left _ _)
     have hc := Nat.mul_le_mul_left 1469 (hybridPaddedCost_mono hb)
     exact hc.trans (hybrid_small_rate 10 (total p) (by decide) (by decide)
       (by omega) (by omega))
 · by_cases hlarge : 60 ≤ total p
   · have hb := below_cap_of_bounds p (total p) 60 11 (by decide) hlarge
       (by omega) hy (le_refl _)
     exact (Nat.mul_le_mul_left 1469 (hybridPaddedCost_mono hb)).trans
       (hybrid_large_rate_11 (total p) hlarge ht)
   · let u := max (total p) 12
     have hb := below_cap_of_bounds p u u 11 (by simp [u]) (le_refl _)
       (by omega) (by dsimp [u]; exact (middle_le_total p).trans (le_max_left _ _))
       (by dsimp [u]; exact le_max_left _ _)
     exact (Nat.mul_le_mul_left 1469 (hybridPaddedCost_mono hb)).trans
       (hybrid_small_rate 11 (total p) (by decide) (by decide)
         (by omega) (by omega))
 · by_cases hlarge : 60 ≤ total p
   · have hb := below_cap_of_bounds p (total p) 60 12 (by decide) hlarge
       (by omega) hy (le_refl _)
     exact (Nat.mul_le_mul_left 1469 (hybridPaddedCost_mono hb)).trans
       (hybrid_large_rate_12 (total p) hlarge ht)
   · let u := max (total p) 13
     have hb := below_cap_of_bounds p u u 12 (by simp [u]) (le_refl _)
       (by omega) (by dsimp [u]; exact (middle_le_total p).trans (le_max_left _ _))
       (by dsimp [u]; exact le_max_left _ _)
     exact (Nat.mul_le_mul_left 1469 (hybridPaddedCost_mono hb)).trans
       (hybrid_small_rate 12 (total p) (by decide) (by decide)
         (by omega) (by omega))
 · have hy56 := h13 hs13eq
   by_cases hlarge : 56 ≤ total p
   · have hb := below_cap_of_bounds p (total p) 56 13 (by decide) hlarge
       (by omega) hy56 (le_refl _)
     exact (Nat.mul_le_mul_left 1469 (hybridPaddedCost_mono hb)).trans
       (hybrid_large_rate_13 (total p) hlarge ht)
   · let u := max (total p) 14
     have hb := below_cap_of_bounds p u u 13 (by simp [u]) (le_refl _)
       (by omega) (by dsimp [u]; exact (middle_le_total p).trans (le_max_left _ _))
       (by dsimp [u]; exact le_max_left _ _)
     exact (Nat.mul_le_mul_left 1469 (hybridPaddedCost_mono hb)).trans
       (hybrid_small_rate 13 (total p) (by decide) (by decide)
         (by omega) (by omega))
theorem own_support (F : P4) :
   ResidualSupportData
     (RCN198.support (padA (originalCumulativeFlag F))
       (padB (originalCumulativeFlag F)) (padSlope (originalCumulativeFlag F))) F := by
 have hc := originalCumulativeFlag_cumulative F
 have hp := pad_sums (originalCumulativeFlag F)
 refine ⟨?_, ?_, ?_⟩
 · change wt residualSWeights F ≤ padSlope (originalCumulativeFlag F) + 2
   rw [hp.1, ← hc.1]
   exact le_max_left _ _
 · change wt residualYSWeights F ≤
     padB (originalCumulativeFlag F) + padSlope (originalCumulativeFlag F) + 3
   rw [hp.2.1, ← hc.2.1]
   exact le_max_left _ _
 · change wt residualTotalWeights F ≤ padA (originalCumulativeFlag F) +
     padB (originalCumulativeFlag F) + padSlope (originalCumulativeFlag F) + 3
   rw [hp.2.2, ← hc.2.2]
   exact le_max_left _ _
theorem own_box (F : P4) (D w L s : ℕ)
   (hbox : F ∈ RCN174.globalCoefficientBox K D w L s) :
   F ∈ RCN174.globalCoefficientBox K D w
     (padA (originalCumulativeFlag F) + padB (originalCumulativeFlag F) +
       padSlope (originalCumulativeFlag F) + 3)
     (padSlope (originalCumulativeFlag F) + 2) := by
 have hs := (own_support F).s_weight
 have ht := (own_support F).total_weight
 intro d hd
 have hds := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hs
 have hdt := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans ht
 rw [weight_fin4] at hds hdt
 simp only [residualSWeights, residualTotalWeights, RCN198.support, Fin.isValue,
   Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
   Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] at hds hdt
 exact ⟨by omega, hds, (hbox hd).2.2⟩
def wholeSupport : ResidualSupportParameters :=
 ⟨13, 60, 1469, by decide, by decide, by decide, by decide⟩
theorem factor_support (Q : P4) (hQ : Q ≠ 0)
   (HQ : ResidualSupportData wholeSupport Q) (R : RegularIndex Q) :
   ResidualSupportData wholeSupport R.1 := by
 have hd := (RCN167.positiveRFactors_spec Q R.1 R.2).2.1
 exact ⟨(weightedTotalDegree_le_of_dvd residualSWeights R.1 Q hd hQ).trans HQ.s_weight,
   (weightedTotalDegree_le_of_dvd residualYSWeights R.1 Q hd hQ).trans HQ.ys_weight,
   (weightedTotalDegree_le_of_dvd residualTotalWeights R.1 Q hd hQ).trans HQ.total_weight⟩
theorem own_parameter_caps (p : FlagDegree)
   (hs : p.all ≤ 13) (hy : middle p ≤ 60) (ht : total p ≤ 1469) :
   padSlope p + 2 ≤ 13 ∧ padB p + padSlope p + 3 ≤ 60 ∧
     padA p + padB p + padSlope p + 3 ≤ 1469 := by
 have hp := pad_sums p
 have hps : padS p ≤ 13 := max_le hs (by decide)
 have hpy : padY p ≤ 60 := max_le hy (by omega)
 have hpt : padT p ≤ 1469 := max_le ht (by omega)
 rw [hp.1, hp.2.1, hp.2.2]
 exact ⟨hps, hpy, hpt⟩
def factorCost6742 (p : FlagDegree) : ℕ :=
 if p.all ≤ 9 then paddedCost 131072 131073 p else hybridPaddedCost p
theorem regular_factor_count
   (Q : P4) (hQ : Q ≠ 0)
   (hbox : Q ∈ RCN174.globalCoefficientBox K 8187885 131071 1469 13)
   (HQ : ResidualSupportData wholeSupport Q)
   (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
   (hagreement : ∀ gamma ∈ Gamma, 181953 ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hno : NoLargeSelectedPencil selected Gamma 131071 80191)
   (R : RegularIndex Q) :
   (regularSeeds Q selected Gamma R).card ≤
     factorCost6742 (regularCumulativeFlag Q R) := by
 letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
 let p := regularCumulativeFlag Q R
 let a := padA p
 let b := padB p
 let s := padSlope p
 have hRdata := directFactor_data Q R.1 hQ 8187885 131071 1469 13 hbox R.2
 have hRsmall : R.1.degreeOf (2 : Fin 4) < 2130706433 :=
   (degreeOf_R_le_of_mem_box _ _ _ _ _ hRdata.2.2).trans_lt (by decide)
 have hRbox := own_box R.1 8187885 131071 1469 13 hRdata.2.2
 have hRsupport := own_support R.1
 have hRwhole := factor_support Q hQ HQ R
 have hc := originalCumulativeFlag_cumulative R.1
 have hparam : s + 2 ≤ 13 ∧ b + s + 3 ≤ 60 ∧ a + b + s + 3 ≤ 1469 := by
   apply own_parameter_caps p
   · exact hRwhole.s_weight
   · simpa only [p, middle, regularCumulativeFlag, hc.2.1, wholeSupport] using
       hRwhole.ys_weight
   · simpa only [p, total, regularCumulativeFlag, hc.2.2, wholeSupport] using
       hRwhole.total_weight
 have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
     specialization K (selected gamma) gamma R.1 = 0 := by
   intro gamma hgamma
   exact (Finset.mem_filter.mp hgamma).2.1
 have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
   (regularSeeds Q selected Gamma R) hsolutions
 have hstage (g : GeometricFactor K R.1) :
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
       if p.all ≤ 9 then
         flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
           (paddedTail p 131073)
       else LocatorFixedStage.hybridStageCost (geometricCumulativeFlag K g) a b s := by
   let S0 := regularGeometricResidualStageOfSupport (RCN198.support a b s) Q selected Gamma
     (Finset.univ : Finset I) IRSProfile.domain u0 u1
     IRSProfile.domain.injective.injOn hdegree hno R
     hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
   let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
   have hsub : geometricSeeds K R.1 selected
       (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
     (geometricSeeds_subset K R.1 selected _ g).trans (regularSeeds_subset Q selected Gamma R)
   have hnodes : S.nodes.card = 181953 + 80191 := by
     change (Finset.univ : Finset I).card = _
     norm_num [I, IRSProfile.Index]
   have hag : ∀ gamma ∈ geometricSeeds K R.1 selected
       (regularSeeds Q selected Gamma R) g, 181953 ≤ (S.agreementFiber gamma).card := by
     intro gamma hgamma
     simpa [S, S0, ResidualStage.agreementFiber, ResidualStage.Agrees,
       reflagResidualStage, regularGeometricResidualStageOfSupport,
       geometricResidualStageOfSupport] using hagreement gamma (hsub hgamma)
   have hf := geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero hRsupport g
   by_cases hlow : p.all ≤ 9
   · have hcount := LocatorFixedStage.fixedStageBound a b s
       hparam.1 hparam.2.1 hparam.2.2 S hnodes hag hRbox hf
     simpa only [hlow, if_true, LocatorFixedStage.firstTail,
       LocatorFixedStage.secondTail, LocatorFixedStage.w, Nat.reduceAdd,
       geometricCumulativeFlag, a, b, s, padded_tail_eq] using hcount
   · have hpadS : padS p = p.all := max_eq_left (by omega)
     have hs8 : 8 ≤ s := by
       dsimp only [s, padSlope]
       rw [hpadS]
       omega
     have hcount := LocatorFixedStage.hybridStageBound a b s hs8
       hparam.1 hparam.2.1 hparam.2.2 S hnodes hag hRbox hf
     simpa only [hlow, if_false, geometricCumulativeFlag] using hcount
 calc
   (regularSeeds Q selected Gamma R).card ≤
       ∑ g : GeometricFactor K R.1,
         (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card := hcover
   _ ≤ ∑ g : GeometricFactor K R.1,
       (if p.all ≤ 9 then
         flagMixed (geometricCumulativeFlag K g) (paddedTail p 131072)
           (paddedTail p 131073)
       else LocatorFixedStage.hybridStageCost (geometricCumulativeFlag K g) a b s) :=
     Finset.sum_le_sum (fun g _ => hstage g)
   _ ≤ factorCost6742 p := by
     have hb := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
     by_cases hlow : p.all ≤ 9
     · simp only [hlow, if_true, factorCost6742]
       exact LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) p _ _
         hb.1 hb.2.1 hb.2.2
     · simp only [hlow, if_false, factorCost6742, hybridPaddedCost,
         LocatorFixedStage.hybridStageCost, Finset.sum_add_distrib,
         Finset.mul_sum]
       exact Nat.add_le_add
         (LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) p _ _
           hb.1 hb.2.1 hb.2.2)
         (by
           have hm := LocatorFactorAggregate.sum_mixed_le
             (geometricCumulativeFlag K) p
             (LocatorFixedStage.movingFiberFlag a b s)
             (LocatorFixedStage.movingCutFlag a b s)
             hb.1 hb.2.1 hb.2.2
           have hmul := Nat.mul_le_mul_left (LocatorFixedStage.w + 2) hm
           simpa only [Finset.mul_sum, a, b, s] using hmul)
theorem regular_sum_count
   (Q : P4) (hQ : Q ≠ 0)
   (hbox : Q ∈ RCN174.globalCoefficientBox K 8187885 131071 1469 13)
   (HQ : ResidualSupportData wholeSupport Q)
   (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
   (hagreement : ∀ gamma ∈ Gamma, 181953 ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hno : NoLargeSelectedPencil selected Gamma 131071 80191)
   (h13 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 13 →
     middle (regularCumulativeFlag Q R) ≤ 56) :
   (∑ R : RegularIndex Q, (regularSeeds Q selected Gamma R).card) ≤
     fixedRegularCap6742 := by
 have hb := regularCumulativeFlag_budgets Q hQ HQ
 have hsSum : (∑ R : RegularIndex Q, (regularCumulativeFlag Q R).all) ≤ 13 :=
   hb.1
 have hySum : (∑ R : RegularIndex Q, middle (regularCumulativeFlag Q R)) ≤ 60 :=
   hb.2.1
 have htSum : (∑ R : RegularIndex Q, total (regularCumulativeFlag Q R)) ≤ 1469 :=
   hb.2.2
 have hs (R : RegularIndex Q) : (regularCumulativeFlag Q R).all ≤ 13 :=
   (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ R)).trans hsSum
 have hy (R : RegularIndex Q) : middle (regularCumulativeFlag Q R) ≤ 60 :=
   (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ R)).trans hySum
 have ht (R : RegularIndex Q) : total (regularCumulativeFlag Q R) ≤ 1469 :=
   (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ R)).trans htSum
 have hrate (R : RegularIndex Q) :
     1469 * factorCost6742 (regularCumulativeFlag Q R) ≤
       fixedRegularCap6742 * total (regularCumulativeFlag Q R) := by
   by_cases hlow : (regularCumulativeFlag Q R).all ≤ 9
   · have hbase := LocatorFactorAggregate.rate_bound_low_6742
       (regularCumulativeFlag Q R) hlow (hy R) (ht R)
     rw [factorCost6742, if_pos hlow]
     exact hbase.trans (Nat.mul_le_mul_right _ (by decide))
   · rw [factorCost6742, if_neg hlow]
     exact rate_bound_high_6742 (regularCumulativeFlag Q R) (by omega)
       (hs R) (hy R) (ht R) (h13 R)
 have hscaled :
     1469 * (∑ R : RegularIndex Q, factorCost6742 (regularCumulativeFlag Q R)) ≤
       1469 * fixedRegularCap6742 := by
   calc
     _ = ∑ R : RegularIndex Q,
         1469 * factorCost6742 (regularCumulativeFlag Q R) := by
       rw [Finset.mul_sum]
     _ ≤ ∑ R : RegularIndex Q,
         fixedRegularCap6742 * total (regularCumulativeFlag Q R) :=
       Finset.sum_le_sum (fun R _ => hrate R)
     _ = fixedRegularCap6742 *
         (∑ R : RegularIndex Q, total (regularCumulativeFlag Q R)) := by
       rw [Finset.mul_sum]
     _ ≤ fixedRegularCap6742 * 1469 := Nat.mul_le_mul_left _ htSum
     _ = 1469 * fixedRegularCap6742 := by ring
 have hcost : (∑ R : RegularIndex Q,
     factorCost6742 (regularCumulativeFlag Q R)) ≤ fixedRegularCap6742 :=
   Nat.le_of_mul_le_mul_left hscaled (by decide)
 exact (Finset.sum_le_sum (fun R _ =>
   regular_factor_count Q hQ hbox HQ selected Gamma u0 u1
     hdegree hagreement hno R)).trans hcost
def profile : RCN276.Profile :=
 ⟨262144, 131071, 181953, 8187885, 1469, 13⟩
theorem fixed_count_le
   (Q : P4) (hQ : Q ≠ 0)
   (hbox : Q ∈ RCN174.globalCoefficientBox K 8187885 131071 1469 13)
   (HQ : ResidualSupportData wholeSupport Q)
   (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
   (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma Q = 0)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
   (hagreement : ∀ gamma ∈ Gamma, 181953 ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hno : NoLargeSelectedPencil selected Gamma 131071 80191)
   (h13 : ∀ R : RegularIndex Q, (regularCumulativeFlag Q R).all = 13 →
     middle (regularCumulativeFlag Q R) ≤ 56) :
   Gamma.card ≤ fixedRegularCap6742 + LocatorArithmetic.fixedSingular.countCap := by
 have hg := LocatorArithmetic.fixed_singular_gates
 have hcover := RCN239.card_le_regular_sum_add_singular
   profile Q hQ hbox hg.s_pos hg.s_small hg.w_pos hg.kD
   hg.algebraic_pos hg.algebraic_small selected Gamma hsolution
 have hreg := regular_sum_count Q hQ hbox HQ selected Gamma u0 u1
   hdegree hagreement hno h13
 have hsing := RCN292.TightParameters.singularSeeds_count_le_countCap
   LocatorArithmetic.fixedSingular Q hQ hbox
   hg.s_pos hg.s_small hg.w_pos hg.w_small hg.kD hg.algebraic_pos
   hg.implicit_small hg.algebraic_small hg.mixed_small hg.wa hg.an
   selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
   IRSProfile.domain.injective.injOn
   (by
     change (Finset.univ : Finset I).card = 262144
     rw [Finset.card_univ]
     change Fintype.card (Fin (2 ^ 18)) = 262144
     rw [Fintype.card_fin]
     decide) hdegree hagreement (by
       simpa only [LocatorArithmetic.fixedSingular,
         RCN318.TightParameters.errors, LocatorArithmetic.n,
         LocatorArithmetic.w, LocatorArithmetic.agreements,
         Nat.reduceSub] using hno)
 exact hcover.trans (Nat.add_le_add hreg hsing)
end
end ProximityPrize.SubmissionLower.LocatorFixed
