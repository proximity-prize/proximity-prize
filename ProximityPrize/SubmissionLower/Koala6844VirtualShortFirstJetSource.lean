import ProximityPrize.SubmissionLower.Koala6844VirtualShortCenteredAdaptive


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Koala6844Normalization LocatorLowQuotient
open SecondJetSupport ContactOrderBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5400000

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]

theorem exists_centered_firstJet_source
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w a errors excess)
    (D : ℕ → ℕ) (wQ m L B U q : ℕ) (ha : 0 < a) (hw : 0 < w) (hm : 0 < m)
    (hUL : U ≤ L) (hqU : q ≤ U) (hcut : D 0 ≤ m*a) (hcaps : U ≤ (D 0+B-1)/w)
    (hWQ : w+data.d0.natDegree ≤ affineDegree data.A0+wQ)
    (hLead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (hgap : nodes.card * normalizedRankBudget D w m L B 0 U q <
      Fintype.card (NormalizedIndex D w wQ L B 0 U q)) :
    ∃ P : MvPolynomial (Fin 4) K, P ≠ 0 ∧
      P ∈ nestedCoefficientBox K (D 0+q*affineDegree data.A0) w (L+q) U B ∧
      Koala6844Receipts.ClearedForm (centeredFlow data).A (centeredFlow data).numerator q P ∧
      (∀ i ∈ nodes, ContactAtLeast K (x i) (data.received 0 i) (data.received 1 i) m P) ∧
      ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g P = 0 := by
  classical
  let T := {i // i ∈ nodes}
  let A := normalizedDenominator (data.A0 0) (data.A0 1)
  let N := normalizedNumerator data.d0 data.C1
  let x' (i : T) := x i.val
  let u0 (i : T) := data.received 0 i.val
  let u1 (i : T) := data.received 1 i.val
  let V := (jointContactMap D w wQ L B 0 U q m A N x' u0 u1).ker
  have hAn : data.A0 1 ≠ 0 := by
    have hNonempty : nodes.Nonempty := Finset.card_pos.mp
      ((ha.trans_le (data.agreements 0 data.zero_mem)).trans_le (Finset.card_filter_le _ _))
    obtain ⟨i,hi⟩ := hNonempty
    intro h
    exact hLead i hi (by rw [h,Polynomial.eval_zero])
  have hlocal (i : T) : Module.finrank K (normalizedContactMap D w wQ L B 0 U q m A N (x' i) (u0 i) (u1 i)).range ≤
      normalizedRankBudget D w m L B 0 U q := by
    have h0 := data.received_equation i.val i.property 0
    have h1 := data.received_equation i.val i.property 1
    norm_num at h0 h1
    obtain ⟨pole⟩ := exists_nodePoleData (x' i) (u0 i) (u1 i) (data.fixedWord i.val) m
      (data.A0 0) (data.A0 1) data.d0 data.C1 h0 h1 (hLead i.val i.property)
    exact normalized_local_rank_bound D w wQ L B 0 U q m (by omega) hUL hqU
      (fun h => (D h+B-1)/w) (fun h hh => by simpa [Nat.eq_zero_of_le_zero hh] using hcaps)
      A N (x' i) (u0 i) (u1 i) pole
  have hd : 0 < Module.finrank K V := by
    have hr := normalizedContactKernel_finrank D w wQ L B 0 U q m (normalizedRankBudget D w m L B 0 U q)
      A N x' u0 u1 hlocal
    change _ ≤ Module.finrank K V at hr
    rw [show Fintype.card T = nodes.card by simp [T]] at hr
    omega
  have hV : V ≠ ⊥ := by
    intro hh
    rw [hh] at hd
    simp at hd
  obtain ⟨c,hc,hn⟩ := (Submodule.ne_bot_iff _).mp hV
  let C : V := ⟨c,hc⟩
  let P := firstJetClearedLinear D w wQ L B U q A N c
  have hp : P ≠ 0 := by
    intro h
    apply hn
    apply firstJetClearedLinear_injective D w wQ L B U q hUL hqU (data.A0 0) (data.A0 1)
      data.d0 data.C1 hAn data.d0_ne
    simpa only [map_zero] using h
  have hbox : P ∈ nestedCoefficientBox K (D 0+q*affineDegree data.A0) w (L+q) U B :=
    firstJetClearedLinear_mem_nestedCoefficientBox D w wQ L B U q (affineDegree data.A0) (D 0)
      hUL hqU rfl.le (data.A0 0) (data.A0 1) data.d0 data.C1 (le_max_left _ _) (le_max_right _ _)
      (by omega) (by have := data.degree_C1; omega) c
  have hcontact (i : I) (hi : i ∈ nodes) : ContactAtLeast K (x i) (data.received 0 i) (data.received 1 i) m P :=
    firstJetKernel_contact D w wQ m L B U q hUL hqU (data.A0 0) (data.A0 1) data.d0 data.C1
      x' u0 u1 C ⟨i,hi⟩
  have hclear : Koala6844Receipts.ClearedForm (centeredFlow data).A (centeredFlow data).numerator q P := by
    simpa only [A,N,toFirstJet_den_eq_centeredFlow,toFirstJet_num_eq_centeredFlow] using
      firstJetClearedLinear_clearedForm D w wQ L B U q A N c
  have hbox' : P ∈ nestedCoefficientBox K (m*a+q*affineDegree data.A0-0*(2*(excess+1))) w (L+q) U B := by
    intro e he
    have hc := hbox he
    exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.trans_le (by omega)⟩
  exact ⟨P,hp,hbox,hclear,hcontact,
    (centered_flow_partner data (excess+1) m q 0 (L+q) U B (Nat.succ_pos _) hm hw ha
      (data.support_le.trans (Nat.le_succ _)) P hp hbox' hclear hcontact).2⟩

theorem exists_short_primary
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ 131071 180958 errors excess)
    (hWidth : data.d0.natDegree+affineDegree data.A0 ≤ 6679)
    (hLead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (hgap : nodes.card * normalizedRankBudget (fun _ => 601*180958) 131071 601 44841 185 0 829 744 <
      Fintype.card (NormalizedIndex (fun _ => 601*180958) 131071 (131071+6679) 44841 185 0 829 744)) :
    ∃ P : MvPolynomial (Fin 4) K, P ≠ 0 ∧
      P ∈ nestedCoefficientBox K (601*180958+744*6679) 131071 45585 829 185 ∧
      Koala6844Receipts.ClearedForm (centeredFlow data).A (centeredFlow data).numerator 744 P ∧
      (∀ i ∈ nodes, ContactAtLeast K (x i) (data.received 0 i) (data.received 1 i) 601 P) ∧
      ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g P = 0 := by
  have hWQ : 131071+data.d0.natDegree ≤ affineDegree data.A0 + (131071+6679) := by omega
  obtain ⟨P,hP,hbox,hclear,hcontact,hzero⟩ := exists_centered_firstJet_source data (fun _ => 601*180958)
    (131071+6679) 601 44841 185 829 744 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hWQ hLead hgap
  refine ⟨P,hP,?_,hclear,hcontact,hzero⟩
  intro e he
  have hc := hbox he
  exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.trans_le
    (Nat.add_le_add_left (Nat.mul_le_mul_left 744 (by omega)) _)⟩

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
