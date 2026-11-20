import ProximityPrize.SubmissionLower.Koala6844VirtualShortFlowVanish
import ProximityPrize.SubmissionLower.Koala6844NormalizationData
import ProximityPrize.SubmissionLower.Koala6831MovingContact
import ProximityPrize.SubmissionLower.Koala6831MovingSupports


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open ContactOrderBridge LocatorLowQuotient RCN081 RCN156 RCN234
open Koala6844Receipts (ClearedForm)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4100000

variable {K : Type*} [Field K]

private def legacyFlow (B : Koala6844Moving.FlowData K) : Koala6831Moving.FlowData K :=
  ⟨B.d0,B.a0,B.a1,B.c0,B.c1⟩

theorem iterate_flow_nested_box
    (B : Koala6844Moving.FlowData K) (P : MvPolynomial (Fin 4) K)
    (w δ j D L U r : ℕ) (hw : 0 < w) (hδ : 0 < δ)
    (hden : B.d0.natDegree+max B.a0.natDegree B.a1.natDegree ≤ δ)
    (hminor : (B.a1*B.c0-B.a0*B.c1).natDegree ≤ w+δ)
    (hP : P ≠ 0) (hbox : P ∈ nestedCoefficientBox K (D-j*(2*δ)) w L U r) :
    ((B.flow : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K)^[j] P) ∈
      nestedCoefficientBox K D w (L+j) U r := by
  let F := legacyFlow B
  let Q := ((B.flow : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K)^[j] P)
  obtain ⟨hT,hU,hR,hD⟩ := nested_mem_weights hbox hP
  have ht : wt residualTotalWeights Q ≤ L+j := by
    have h := F.flow_iterate_wt_le residualTotalWeights 1 j P F.flow_total_le
    change wt residualTotalWeights Q ≤ _ at h
    exact (by simpa only [Nat.mul_one] using h : wt residualTotalWeights Q ≤ wt residualTotalWeights P+j).trans
      (Nat.add_le_add_right hT _)
  have hu : wt residualYSWeights Q ≤ U := by
    have h := F.flow_iterate_wt_le residualYSWeights 0 j P (fun R => by simpa using F.flow_middle_le R)
    change wt residualYSWeights Q ≤ _ at h
    exact (by simpa using h : wt residualYSWeights Q ≤ wt residualYSWeights P).trans hU
  have hr : wt residualSWeights Q ≤ r := by
    have h := F.flow_iterate_wt_le residualSWeights 0 j P (fun R => by simpa using F.flow_slope_le R)
    change wt residualSWeights Q ≤ _ at h
    exact (by simpa using h : wt residualSWeights Q ≤ wt residualSWeights P).trans hR
  have hc : wt (contactWeights w) Q < D := by
    have h := F.flow_iterate_wt_le (contactWeights w) (2*δ) j P (fun R =>
      F.flow_contact_wt_le R w δ hw hδ hden hminor)
    change wt (contactWeights w) Q ≤ _ at h
    change wt (contactWeights w) P < D-j*(2*δ) at hD
    omega
  intro e he
  exact ⟨by simpa [weight_fin4,residualTotalWeights] using
      (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans ht,
    by simpa [weight_fin4,residualYSWeights] using
      (MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans hu,
    by simpa [weight_fin4,residualSWeights] using
      (MvPolynomial.le_weightedTotalDegree residualSWeights he).trans hr,
    by simpa [weight_fin4,contactWeights,Nat.mul_comm] using
      (MvPolynomial.le_weightedTotalDegree (contactWeights w) he).trans_lt hc⟩

theorem iterate_flow_contact (B : Koala6844Moving.FlowData K) (x u0 u1 v : K)
    (h0 : B.d0.eval x*u0+B.c0.eval x = B.a0.eval x*v)
    (h1 : B.d0.eval x*u1+B.c1.eval x = B.a1.eval x*v)
    (m j : ℕ) (P : MvPolynomial (Fin 4) K) (hc : ContactAtLeast K x u0 u1 m P) :
    ContactAtLeast K x u0 u1 m ((B.flow : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K)^[j] P) :=
  (legacyFlow B).contactAtLeast_iterate_flow x u0 u1 v h0 h1 j hc


private theorem specialize_liftX (f P : Polynomial K) (g : K) :
    RCN319.specialization K f g (Koala6844Moving.liftX P) = P := by
  have h : (RCN319.specialization K f g).comp
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) K)) =
      AlgHom.id K (Polynomial K) := by
    apply Polynomial.algHom_ext
    simp [RCN319.specialization]
  exact DFunLike.congr_fun h P

variable {I : Type*} [DecidableEq K] [DecidableEq I]

def centeredFlow {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : Koala6844Normalization.CenteredVirtualData x nodes σ w a errors excess) :
    Koala6844Moving.FlowData K := ⟨data.d0,data.A0 0,data.A0 1,0,data.C1⟩

theorem toFirstJet_den_eq_centeredFlow {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : Koala6844Normalization.CenteredVirtualData x nodes σ w a errors excess) :
    toFirstJet (normalizedDenominator (data.A0 0) (data.A0 1)) = (centeredFlow data).A :=
  toFirstJet_normalizedDenominator _ _

theorem toFirstJet_num_eq_centeredFlow {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : Koala6844Normalization.CenteredVirtualData x nodes σ w a errors excess) :
    toFirstJet (normalizedNumerator data.d0 data.C1) = (centeredFlow data).numerator := by
  rw [toFirstJet_normalizedNumerator]
  simp [centeredFlow,Koala6844Moving.FlowData.numerator,
    Koala6844Moving.FlowData.C,Koala6844Moving.affine,Koala6844Moving.liftX]

private theorem specialize_centered_den {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : Koala6844Normalization.CenteredVirtualData x nodes σ w a errors excess) (f : Polynomial K) (g : K) :
    RCN319.specialization K f g (centeredFlow data).A = Koala6844Normalization.specializeAffine data.A0 g := by
  have hx : RCN319.specialization K f g (MvPolynomial.X 3) = Polynomial.C g := by simp [RCN319.specialization]
  simp [centeredFlow,Koala6844Moving.FlowData.A,Koala6844Moving.affine,specialize_liftX,hx,
    Koala6844Normalization.specializeAffine]

private theorem specialize_centered_num {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : Koala6844Normalization.CenteredVirtualData x nodes σ w a errors excess) (f : Polynomial K) (g : K) :
    RCN319.specialization K f g (centeredFlow data).numerator = data.d0*f+Polynomial.C g*data.C1 := by
  have hy : RCN319.specialization K f g (MvPolynomial.X 1) = f := by simp [RCN319.specialization]
  have hz : RCN319.specialization K f g (MvPolynomial.X 3) = Polynomial.C g := by simp [RCN319.specialization]
  simp [centeredFlow,Koala6844Moving.FlowData.numerator,Koala6844Moving.FlowData.C,
    Koala6844Moving.affine,specialize_liftX,hy,hz]

theorem centered_flow_partner
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : Koala6844Normalization.CenteredVirtualData x nodes σ w a errors excess)
    (δ m q j L U R : ℕ) (hδ : 0 < δ) (hm : 0 < m) (hw : 0 < w) (ha : 0 < a)
    (hwidth : data.d0.natDegree+Koala6844Normalization.affineDegree data.A0 ≤ δ)
    (P : MvPolynomial (Fin 4) K) (hP : P ≠ 0)
    (hbox : P ∈ nestedCoefficientBox K
      (m*a+q*Koala6844Normalization.affineDegree data.A0-j*(2*δ)) w L U R)
    (hclear : ClearedForm (centeredFlow data).A (centeredFlow data).numerator q P)
    (hcontact : ∀ i ∈ nodes, ContactAtLeast K (x i) (data.received 0 i) (data.received 1 i) m P) :
    let Q := (((centeredFlow data).flow : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K)^[j] P)
    Q ∈ nestedCoefficientBox K (m*a+q*Koala6844Normalization.affineDegree data.A0) w (L+j) U R ∧
    (∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g Q = 0) := by
  classical
  let flow := centeredFlow data
  let Q := ((flow.flow : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K)^[j] P)
  have hminor : (flow.a1*flow.c0-flow.a0*flow.c1).natDegree ≤ w+δ := by
    change (data.A0 1*0-data.A0 0*data.C1).natDegree ≤ _
    rw [mul_zero,zero_sub,Polynomial.natDegree_neg]
    have hdeg := Polynomial.natDegree_mul_le_of_le (le_max_left (data.A0 0).natDegree (data.A0 1).natDegree) data.degree_C1
    change data.d0.natDegree+max (data.A0 0).natDegree (data.A0 1).natDegree ≤ δ at hwidth
    exact hdeg.trans (by omega)
  have hQbox : Q ∈ nestedCoefficientBox K (m*a+q*Koala6844Normalization.affineDegree data.A0) w (L+j) U R :=
    iterate_flow_nested_box flow P w δ j _ L U R hw hδ hwidth hminor hP hbox
  refine ⟨hQbox,?_⟩
  intro g hg
  let S := nodes.filter fun i => (data.selected g).eval (x i) = data.received 0 i+g*data.received 1 i
  refine specialization_vanish_of_cleared_contact Q flow.A flow.numerator w q m a
    (Koala6844Normalization.affineDegree data.A0) (L+j) U R ha hm hQbox
    (Koala6844Receipts.flow_iterate_clearedForm flow q j hclear)
    x (data.received 0) (data.received 1) S (data.agreements g hg)
    ?_ (data.selected g) (data.normalized g) g (data.selected_degree g hg) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i ∈ nodes := (Finset.mem_filter.mp hi).1
    have h₀ := data.received_equation i hi' 0
    have h₁ := data.received_equation i hi' 1
    norm_num [mul_comm] at h₀ h₁
    exact iterate_flow_contact flow (x i) (data.received 0 i) (data.received 1 i) (data.fixedWord i)
      (by simpa [flow,centeredFlow,mul_comm] using h₀) (by simpa [flow,centeredFlow,mul_comm] using h₁)
      m j P (hcontact i hi')
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · rw [specialize_centered_den]
    exact data.denominator_degree g hg
  · intro i hi
    rw [specialize_centered_den]
    exact data.denominator_on_domain g hg i (Finset.mem_filter.mp hi).1
  · rw [specialize_centered_num,specialize_centered_den]
    exact (data.equation0 g hg).symm

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
