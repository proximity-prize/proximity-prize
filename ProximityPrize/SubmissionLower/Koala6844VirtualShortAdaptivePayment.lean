import ProximityPrize.SubmissionLower.MultipleAdaptive
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPhasePayment
import ProximityPrize.SubmissionLower.Koala6844VirtualShortFeeCaps
import ProximityPrize.SubmissionLower.Koala6844VirtualShortFeeInputs


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort
open scoped Classical
open Koala6844Normalization Koala6844Receipts Koala6844Terminal
open RCN081 RCN095 RCN130 RCN140 RCN156 RCN167 RCN234 RCN266
open LocatorBatchProductRoute LocatorFactorAggregate LocatorLowQuotient
open Koala6831MovingAdaptive (aggregateFlag aggregateFlag_mono aggregateFlag_pos)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4000

variable {K E I : Type} [Field K] [Field E] [CharP K prime] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {excess : ℕ}
variable {data : CenteredVirtualData x domain σ degree agreements 81186 excess}

private theorem below_trans {f g h : FlagDegree} (hfg : Below f g) (hgh : Below g h) : Below f h :=
  ⟨hfg.1.trans hgh.1,hfg.2.1.trans hgh.2.1,hfg.2.2.trans hgh.2.2⟩

omit [CharP K prime] [DecidableEq K] in
private theorem physical_cumulative (P : MvPolynomial (Fin 4) K) :
    (physicalFlag P).toFlagDegree = originalCumulativeFlag P := by
  change geometryFlag (physicalFlag P).increments = _
  rw [physicalFlag_increments,geometryFlag_increments]

omit [CharP K prime] [DecidableEq K] in
private theorem physical_fit_of_below (P : MvPolynomial (Fin 4) K) {f : Flag} (hf : f.ordered)
    (h : Below (originalCumulativeFlag P) f.toFlagDegree) :
    (physicalFlag P).cumulativeLE f := by
  rw [← physical_cumulative] at h
  obtain ⟨hr,hy,ht⟩ := h
  rw [Flag.toFlagDegree_middle _ (physicalFlag_ordered P),Flag.toFlagDegree_middle _ hf] at hy
  rw [Flag.toFlagDegree_total _ (physicalFlag_ordered P),Flag.toFlagDegree_total _ hf] at ht
  exact ⟨hr,hy,ht⟩

omit [CharP K prime] in
private theorem adaptive_family_paid
    (data : CenteredVirtualData x domain σ degree agreements 81186 excess)
    (embed : K →+* E) (germ : ActiveResultantGerm data embed)
    (σpow : ∀ g ∈ data.seeds, embed (σ g) = (embed g)^prime)
    (s : CenteredAdaptiveSource data prime)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (pass : CenteredAdaptivePass s poleWidth H A) (f g : Flag) (hg : g.ordered)
    (hprod : (physicalFlag (regularProduct H (A \ pass.residue))).cumulativeLE f)
    (hd : germDegreeT f g < prime)
    (hshape : (⟨s.B,s.U,s.L+s.q+s.B⟩ : Flag) = g) :
    (phaseSeeds H data.selected data.seeds (A \ pass.residue)).card ≤ germPrice f g := by
  apply MultipleAdaptive.charge embed germ σpow (fun _ : Unit => s) H (A \ pass.residue)
    f g hg hprod hd
  · intro _
    rw [← hshape]
    exact ⟨le_rfl,le_rfl,le_rfl⟩
  · intro F hF
    obtain ⟨Q,hbox,hzero,hrel⟩ := pass.partners F hF
    have hnonzero : Q ≠ 0 := by
      intro hz
      have hi := (positiveRFactors_spec H F.val F.property).1
      exact hi.not_isUnit (hrel (dvd_refl F.val) (hz ▸ dvd_zero _))
    exact ⟨(),Q,hrel,physicalFlag_le_of_nested Q hnonzero _ _ _ _ _ hbox,hzero⟩

omit [CharP K prime] in
theorem adaptive_fee_first
    (data : CenteredVirtualData x domain σ degree agreements 81186 excess)
    (hsize : domain.card ≤ nodes) (hpole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (embed : K →+* E) (germ : ActiveResultantGerm data embed)
    (σpow : ∀ g ∈ data.seeds, embed (σ g) = (embed g)^prime)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hfit : Below (aggregateFlag H A) afterRooms.toFlagDegree)
    (pass : CenteredAdaptivePass (firstCenteredAdaptiveSource data hsize hpole) poleWidth H A) :
    (phaseSeeds H data.selected data.seeds (A \ pass.residue)).card ≤ 524260341159050 := by
  have hrooms : afterRooms.ordered := ⟨by decide +kernel,by decide +kernel⟩
  have hp := physical_fit_of_below (regularProduct H (A \ pass.residue)) hrooms
    (below_trans (aggregateFlag_mono H Finset.sdiff_subset) hfit)
  obtain ⟨hg,hd,hpay⟩ := first_adaptive_germ_fee afterRooms
    (show afterRooms.cumulativeLE afterRooms from ⟨le_rfl,le_rfl,le_rfl⟩)
  exact (adaptive_family_paid data embed germ σpow _ H A pass afterRooms _ hg hp hd rfl).trans hpay

omit [CharP K prime] in
theorem adaptive_fee_second
    (data : CenteredVirtualData x domain σ degree agreements 81186 excess)
    (hsize : domain.card ≤ nodes) (hpole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (embed : K →+* E) (germ : ActiveResultantGerm data embed)
    (σpow : ∀ g ∈ data.seeds, embed (σ g) = (embed g)^prime)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hfit : Below (aggregateFlag H A) afterRooms.toFlagDegree)
    (first : CenteredAdaptivePass (firstCenteredAdaptiveSource data hsize hpole) poleWidth H A)
    (second : CenteredAdaptivePass (secondCenteredAdaptiveSource data hsize hpole) poleWidth H first.residue) :
    (phaseSeeds H data.selected data.seeds (first.residue \ second.residue)).card ≤ 5644446294717492 := by
  rcases first.stopped with empty | hfail
  · simp [phaseSeeds,empty]
  let P := regularProduct H first.residue
  let f := physicalFlag P
  have hord : f.ordered := physicalFlag_ordered P
  have hrooms : afterRooms.ordered := ⟨by decide +kernel,by decide +kernel⟩
  have hcap := physical_fit_of_below P hrooms
    (below_trans (aggregateFlag_mono H first.subset_incoming) hfit)
  by_cases empty : first.residue = ∅
  · simp [phaseSeeds,empty]
  have hpos := aggregateFlag_pos H (Finset.nonempty_iff_ne_empty.mpr empty)
  have hflag : f.toFlagDegree = aggregateFlag H first.residue := physical_cumulative P
  have hr : 1 ≤ f.r := by
    change 0 < f.toFlagDegree.all
    rw [hflag]
    exact hpos
  have hFail : ¬ geometricGate flowWidth (bandSourceNumbers firstAdaptiveFlag firstAdaptiveGap)
      f.toFlagDegree := by
    rw [hflag]
    simpa only [flowWidth,firstCenteredAdaptiveSource_numbers] using hfail
  obtain ⟨hg,hd,hpay⟩ := second_adaptive_germ_fee f hr hord hcap hFail
  have hb : Below (aggregateFlag H (first.residue \ second.residue)) f.toFlagDegree := by
    rw [hflag]
    exact aggregateFlag_mono H Finset.sdiff_subset
  have hprod := physical_fit_of_below (regularProduct H (first.residue \ second.residue)) hord hb
  exact (adaptive_family_paid data embed germ σpow _ H first.residue second f _ hg hprod hd rfl).trans hpay

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort

