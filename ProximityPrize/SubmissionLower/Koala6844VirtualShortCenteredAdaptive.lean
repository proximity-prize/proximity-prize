import ProximityPrize.SubmissionLower.Koala6844VirtualShortAdaptive
import ProximityPrize.SubmissionLower.Koala6844VirtualShortFlowPartner


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open RCN095 RCN130 RCN266 LocatorBatchProductRoute LocatorLowQuotient
open LocatorPhase6800Oracle (SourceNumbers)
open Koala6844Normalization
open Koala6844Receipts (geometricGate)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5800000
set_option maxRecDepth 50000

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]

theorem exists_centered_adaptive_partner {p : ℕ} [CharP K p]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w a errors excess)
    (D : ℕ → ℕ) (wQ δ m L B U q gap : ℕ)
    (hw : 0 < w) (ha : 0 < a) (hδ : 0 < δ) (hm : 0 < m) (hBp : B < p)
    (hUL : U ≤ L) (hqU : q ≤ U) (hcut : D 0 ≤ m*a) (hcaps : U ≤ (D 0+B-1)/w)
    (hWidth : data.d0.natDegree + affineDegree data.A0 ≤ δ)
    (hWQ : w+data.d0.natDegree ≤ affineDegree data.A0+wQ)
    (hLead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (hgap : gap ≤ Fintype.card (NormalizedIndex D w wQ L B 0 U q) -
      nodes.card * normalizedRankBudget D w m L B 0 U q)
    (H : MvPolynomial (Fin 4) K) (factors : Finset (RegularIndex H))
    (hFactors : factors.Nonempty) (hField : factors.card < ENat.card K)
    (hSlope : 0 < (originalCumulativeFlag (regularProduct H factors)).all)
    (hFuel : 0 < (⟨L+q,U,B,gap⟩ : SourceNumbers).fuel (originalCumulativeFlag (regularProduct H factors)))
    (hGate : geometricGate (2*δ) ⟨L+q,U,B,gap⟩ (originalCumulativeFlag (regularProduct H factors)))
    (hTrans : ∀ f ∈ factors, ¬ f.val ∣ (centeredFlow data).flow f.val) :
    ∃ remaining ⊂ factors, ∃ Q : MvPolynomial (Fin 4) K,
      Q ∈ nestedCoefficientBox K (m*a+q*affineDegree data.A0) w (L+q+B) U B ∧
      (∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g Q = 0) ∧
      ∀ f ∈ factors \ remaining, IsRelPrime f.val Q := by
  classical
  let T := {i // i ∈ nodes}
  let A := normalizedDenominator (data.A0 0) (data.A0 1)
  let N := normalizedNumerator data.d0 data.C1
  let aD := affineDegree data.A0
  let hX (i : T) := x i.val
  let u0 (i : T) := data.received 0 i.val
  let u1 (i : T) := data.received 1 i.val
  let v (i : T) := data.fixedWord i.val
  have hpLead (i : T) : (data.A0 1).eval (hX i) ≠ 0 := hLead i.val i.property
  have hNonempty : nodes.Nonempty := Finset.card_pos.mp
    ((ha.trans_le (data.agreements 0 data.zero_mem)).trans_le (Finset.card_filter_le _ _))
  have hAn : data.A0 1 ≠ 0 := by
    obtain ⟨i,hi⟩ := hNonempty
    intro hz
    exact hLead i hi (by rw [hz,Polynomial.eval_zero])
  have hi0 (i : T) : data.d0.eval (hX i)*u0 i = v i*(data.A0 0).eval (hX i) := by
    have hh := data.received_equation i.val i.property 0
    simpa [hX,u0,v] using hh
  have hi1 (i : T) : data.d0.eval (hX i)*u1 i+data.C1.eval (hX i) = v i*(data.A0 1).eval (hX i) := by
    have hh := data.received_equation i.val i.property 1
    simpa [hX,u1,v] using hh
  obtain ⟨remaining,hremaining,c,j,hj,hP,hbox,hclear,hfactor⟩ := exists_firstJet_adaptive_exit D
    w wQ m L B U q aD (m*a) (2*δ) hw hUL hqU hcut hcaps (data.A0 0) (data.A0 1) data.d0 data.C1
    hAn data.d0_ne (le_max_left _ _) (le_max_right _ _) (by omega) (by have := data.degree_C1; omega)
    hX u0 u1 v hi0 hi1 hpLead gap (by simpa [T] using hgap) H factors hFactors hField hSlope hFuel hGate
  let P := firstJetClearedLinear D w wQ L B U q A N c.val
  let Q := (((centeredFlow data).flow : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K)^[j] P)
  have hjB : j ≤ B := by
    exact (hj.trans (min_le_right _ _)).trans ((min_le_right _ _).trans (Nat.div_le_self _ _))
  have hpcontact (i : I) (hi : i ∈ nodes) :
      ContactOrderBridge.ContactAtLeast K (x i) (data.received 0 i) (data.received 1 i) m P :=
    firstJetKernel_contact D w wQ m L B U q hUL hqU (data.A0 0) (data.A0 1) data.d0 data.C1
      hX u0 u1 c ⟨i,hi⟩
  have hpclear : Koala6844Receipts.ClearedForm (centeredFlow data).A (centeredFlow data).numerator q P := by
    simpa only [A,N,toFirstJet_den_eq_centeredFlow,toFirstJet_num_eq_centeredFlow] using hclear
  obtain ⟨hQbox,hQzero⟩ := centered_flow_partner data δ m q j (L+q) U B hδ hm hw ha hWidth P hP hbox hpclear hpcontact
  refine ⟨remaining,hremaining,Q,?_,hQzero,?_⟩
  · intro e he
    obtain ⟨hTot,hMid,hSlope,hWeight⟩ := hQbox he
    exact ⟨hTot.trans (Nat.add_le_add_left hjB _),hMid,hSlope,hWeight⟩
  · intro f hf
    have hf' := Finset.mem_sdiff.mp hf
    have hex := hfactor f (by simpa only [Finset.mem_sdiff] using hf')
    obtain ⟨J,hPJ,hJ⟩ := hex
    have hfI := (RCN167.positiveRFactors_spec H f.val f.property).1
    change P = f.val^j*J at hPJ
    unfold Q
    rw [hPJ]
    exact Koala6844Moving.flow_partner_of_lt_characteristic (centeredFlow data) hfI hJ
      (hTrans f hf'.1) (hjB.trans_lt hBp)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
