import ProximityPrize.SubmissionLower.R6961Low6961VariableSelect
import ProximityPrize.SubmissionLower.R6961Low6961WeightedRow
import ProximityPrize.SubmissionLower.FarCharge0
import ProximityPrize.SubmissionLower.FarCharge1

set_option Elab.async false
set_option maxRecDepth 18000

namespace Low6961WeightedProof
noncomputable section
open P3 (K)
open K1_13 (Row shape)
open K1_13_6 (GenericField GeoJets)
open FadicGate (Entry varGateDim taperBox slopeBox)
open KoalaFarBridge (FeeBox rowCheck plainCheck)
open Low6961WeightedRate (Envelope Pays first second)
open Low6961WeightedRow (rate)
open Low6961SharedPrice (Rate)
open Low6961Prices (Messages SmallFactor ActiveFits ProperCut layerNeed symbolCount)
open MvPolynomial
open scoped BigOperators Polynomial

structure Receipt (p : Envelope) where
  terminal : ℕ
  plain : ℕ → FeeBox
  boxes : ℕ → List Entry
  depthPower : ℕ → List ℕ
  plainPower : ℕ → List ℕ
  endPower : List ℕ
  loss : ℕ
  size : 0 < p.widthLow ∧ 0 < p.indexLow ∧ 0 < p.topLow
  hLoss : loss < layerNeed
  dimensions : ∀ N, ∑ i ∈ Finset.range N,
    max 0 ((symbolCount : ℤ) - varGateDim symbolCount p.widthLow p.widthHigh p.indexLow p.indexHigh
      p.topLow p.taperLow p.taperHigh terminal plain (fun r => (boxes r).length)
      (fun r a => (boxes r).getD a none) (i+1)) ≤ (loss : ℤ)
  prices : ∀ r, 0 < r → r < terminal → rowCheck (rate p) r (boxes r) (depthPower r) (plain r) (plainPower r) = true
  tail : plainCheck (rate p) terminal (4012,1650,550) endPower = true

private def firstReceipt : Receipt first :=
  ⟨FadicGate.Final54W0.terminal, FadicGate.Final54W0.plainT, FadicGate.Final54W0.boxes,
    KoalaFarBridge.FarCharge0.adicD, KoalaFarBridge.FarCharge0.plainD, KoalaFarBridge.FarCharge0.terminalD,
    20130931984877, by decide, by decide, FadicGate.Final54W0.loss,
    fun _ h h' => KoalaFarBridge.FarCharge0.fits h h', KoalaFarBridge.FarCharge0.tail⟩

private def secondReceipt : Receipt second :=
  ⟨FadicGate.Final54W1.terminal, FadicGate.Final54W1.plainT, FadicGate.Final54W1.boxes,
    KoalaFarBridge.FarCharge1.adicD, KoalaFarBridge.FarCharge1.plainD, KoalaFarBridge.FarCharge1.terminalD,
    21173162579821, by decide, by decide, FadicGate.Final54W1.loss,
    fun _ h h' => KoalaFarBridge.FarCharge1.fits h h', KoalaFarBridge.FarCharge1.tail⟩

private theorem cut {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (hact : ActiveFits f 165)
    {p : Envelope} (d : Receipt p) (u : Rate) (hu : Pays p (shape f) u) :
    Low6961WeightedTally.Cut (Γ := Γ) (s := s) f u (Low6961WeightedCut.order f (u.split+1)) := by
  intro P hP hs
  obtain ⟨r, hr, v, hv, hsource, hcontact, hrow⟩ := Low6961VariableSelect.select hm P hP f hf.1.ne_zero
    p hu.1 hact d.terminal d.plain d.boxes d.loss d.dimensions d.hLoss
  by_cases ht : d.terminal ≤ r
  · have hV : v ∈ restrictSupport GenericField (slopeBox 4012 1650 550) := by
      exact restrictSupport_mono _ (by simpa only [one_mul] using (FadicGate.source_subset_slopeBox
        (σb := 4012) (σj := 1650) (σt := 550) (r := 1) (by decide))) hsource
    exact Low6961WeightedRow.plain hf hu d.size _ d.endPower ht d.tail hv hV P hs hcontact
  · obtain hplain | ⟨a,B,J,T,c,h,ha,hbox,_,hEq,_,hproper,hC⟩ := hrow.resolve_left ht
    · have hd := (Bool.and_eq_true_iff.mp (d.prices r hr (lt_of_not_ge ht))).2
      have hsub : taperBox (min (d.plain r).1 4012) (min (d.plain r).2.1 1650) (d.plain r).2.2 131312 ⊆
          slopeBox (d.plain r).1 (d.plain r).2.1 (d.plain r).2.2 := by
        intro m hm
        change _ ∧ _ ∧ _
        exact ⟨hm.1.trans (min_le_left _ _), hm.2.1.trans (min_le_left _ _), hm.2.2.1⟩
      have hV := restrictSupport_mono GenericField hsub hplain
      exact Low6961WeightedRow.plain hf hu d.size _ (d.plainPower r) le_rfl hd hv hV P hs hcontact
    · have hd := (Bool.and_eq_true_iff.mp (d.prices r hr (lt_of_not_ge ht))).1
      exact Low6961WeightedRow.adic hf hu (B,J,T) ((d.depthPower r).getD a 0)
        (KoalaFarBridge.depth_at _ hd ha hbox) hEq hproper
        (restrictSupport_mono _ (FadicGate.taperBox_subset_slopeBox _ _ _ _) hC) P hs hcontact

theorem count {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (hact : ActiveFits f 165)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (l : ℕ) (hl : 0 < l) (hcut : ProperCut f Γ s l)
    (u : Rate) (hu : Low6961WeightedRate.Allowed (shape f) u) (hn : ¬ Low6961SharedPrice.RateFits (shape f) u) :
    Γ.card ≤ Low6961SharedPrice.price (shape f) l 165 u := by
  have h (p : Envelope) (d : Receipt p) (paid : Pays p (shape f) u) :
      Γ.card ≤ Low6961SharedPrice.price (shape f) l 165 u := by
    apply Low6961WeightedTally.count hm f hf 165 hact hon l hl hcut u paid.2.1 paid.2.2.2.2.1
      (Low6961WeightedCut.order f (u.split+1))
    · intro q hq hmem
      exact (Low6961WeightedCut.order_spec f _ (by omega) q hq hmem).2
    · exact cut hm f hf hact d u paid
  rcases hu.resolve_left hn with h0 | h1
  · exact h first firstReceipt h0
  · exact h second secondReceipt h1

#print axioms count
end
end Low6961WeightedProof
