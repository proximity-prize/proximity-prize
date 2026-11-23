import ProximityPrize.SubmissionLower.KoalaVariableSelect
import ProximityPrize.SubmissionLower.KoalaSplitRow

set_option Elab.async false
set_option maxRecDepth 18000

namespace KoalaSplitProof
noncomputable section
open P3 (K)
open K1_13 (Row shape)
open K1_13_6 (GenericField GeoJets)
open FadicGate (Entry varGateDim taperBox slopeBox)
open KoalaFarBridge (FeeBox rowCheck plainCheck)
open KoalaWeightedRate (Envelope)
open KoalaSplitRate (Pays)
open KoalaSplitRow (rate)
open Final50SharedPrice (Rate)
open Final50Price (Messages SmallFactor ActiveFits ProperCut layerNeed symbolCount)
open MvPolynomial
open scoped BigOperators Polynomial

structure Receipt (p : Envelope) (k U : ℕ) where
  terminal:ℕ
  plain:ℕ→FeeBox
  boxes:ℕ→List Entry
  depthPower:ℕ→List ℕ
  plainPower:ℕ→List ℕ
  endPower:List ℕ
  loss:ℕ
  size:0 < p.widthLow ∧ 0 < p.indexLow ∧ 0 < p.topLow
  hLoss:loss < layerNeed
  dimensions : ∀ N, ∑ i ∈ Finset.range N,
    max 0 ((symbolCount : ℤ) - varGateDim symbolCount p.widthLow p.widthHigh p.indexLow p.indexHigh
      p.topLow p.taperLow p.taperHigh terminal plain (fun r => (boxes r).length)
      (fun r a => (boxes r).getD a none) (i+1))≤(loss:ℤ)
  prices : ∀ r : ℕ, 0 < r → r < terminal →
    rowCheck (rate p k U) r (boxes r) (depthPower r) (plain r) (plainPower r) = true
  tail:plainCheck (rate p k U) terminal (4012,1650,550) endPower=true

private theorem cut {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (hact : ActiveFits f 172)
    {p:Envelope} {k U:ℕ} (d:Receipt p k U) (u:Rate) (hu:Pays p k U (shape f) u) :
    KoalaWeightedTally.Cut (Γ:=Γ) (s:=s) f u (KoalaWeightedCut.order f (u.split+1)):=by
  intro P hP hs
  obtain ⟨r, hr, v, hv, hsource, hcontact, hrow⟩ := KoalaVariableSelect.select hm P hP f hf.1.ne_zero
    p hu.1 hact d.terminal d.plain d.boxes d.loss d.dimensions d.hLoss
  by_cases ht:d.terminal≤r
  · have hV : v ∈ restrictSupport GenericField (slopeBox 4012 1650 550) := by
      exact restrictSupport_mono _ (by simpa only [one_mul] using (FadicGate.source_subset_slopeBox
        (σb:=4012) (σj:=1650) (σt:=550) (r:=1) (by decide))) hsource
    exact KoalaSplitRow.plain hf hu d.size _ d.endPower ht d.tail hv hV P hs hcontact
  · obtain hplain | ⟨a,B,J,T,c,h,ha,hbox,_,hEq,_,hproper,hC⟩ := hrow.resolve_left ht
    · have hd := (Bool.and_eq_true_iff.mp (d.prices r hr (lt_of_not_ge ht))).2
      have hsub : taperBox (min (d.plain r).1 4012) (min (d.plain r).2.1 1650) (d.plain r).2.2 131312 ⊆
          slopeBox (d.plain r).1 (d.plain r).2.1 (d.plain r).2.2:=by
        intro m hm
        change _ ∧ _ ∧ _
        exact ⟨hm.1.trans (min_le_left _ _),hm.2.1.trans (min_le_left _ _),hm.2.2.1⟩
      have hV:=restrictSupport_mono GenericField hsub hplain
      exact KoalaSplitRow.plain hf hu d.size _ (d.plainPower r) le_rfl hd hv hV P hs hcontact
    · have hd := (Bool.and_eq_true_iff.mp (d.prices r hr (lt_of_not_ge ht))).1
      exact KoalaSplitRow.adic hf hu (B,J,T) ((d.depthPower r).getD a 0)
        (KoalaFarBridge.depth_at _ hd ha hbox) hEq hproper
        (restrictSupport_mono _ (FadicGate.taperBox_subset_slopeBox _ _ _ _) hC) P hs hcontact

theorem count {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (hact : ActiveFits f 172)
    (hon : ∀ γ ∈ Γ,K1_13.OnFactor f (K1_13.extend (s γ))) (l:ℕ) (hl:0 < l) (hcut:ProperCut f Γ s l)
    {p:Envelope} {k U:ℕ} (d:Receipt p k U) (u:Rate) (hu:Pays p k U (shape f) u) :
    Γ.card≤Final50SharedPrice.price (shape f) l 172 u:=by
  obtain ⟨hfit,hk,hsplit,hk0,hU,hamount,hfitted,hweight⟩:=hu
  have hu:Pays p k U (shape f) u:=⟨hfit,hk,hsplit,hk0,hU,hamount,hfitted,hweight⟩
  apply KoalaWeightedTally.count hm f hf 172 hact hon l hl hcut u hk hfitted
    (KoalaWeightedCut.order f (u.split+1))
  · intro q hq hmem
    exact (KoalaWeightedCut.order_spec f _ (by omega) q hq hmem).2
  · exact cut hm f hf hact d u hu

#print axioms count
end
end KoalaSplitProof
