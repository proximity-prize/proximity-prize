import ProximityPrize.SubmissionLower.Koala6844VirtualShortFlowPartner
import ProximityPrize.SubmissionLower.Koala6831MovingPartition


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical
open Koala6844Normalization ContactOrderBridge LocatorLowQuotient LocatorFactorAggregate
open LocatorBatchProductRoute RCN095 RCN130 RCN266
open Koala6831Moving (contactFlag room_residual_caps roomResidualFactors roomResidualFactors_subset mem_roomResidualFactors)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]

private theorem exists_exact_order {M : Type*} [Monoid M] (F P : M) (maxOrder : ℕ)
    (h : ¬ F^(maxOrder+1) ∣ P) : ∃ j ≤ maxOrder, ∃ Q, P = F^j*Q ∧ ¬ F ∣ Q := by
  induction maxOrder with
  | zero => exact ⟨0,le_rfl,P,by simp,by simpa using h⟩
  | succ k ih =>
    by_cases hh : F^(k+1) ∣ P
    · obtain ⟨Q,hQ⟩ := hh
      refine ⟨k+1,le_rfl,Q,hQ,?_⟩
      rintro ⟨R,hR⟩
      exact h ⟨R,by rw [hQ,hR,←mul_assoc,←pow_succ]⟩
    · obtain ⟨j,hj,Q,hQ,hn⟩ := ih hh
      exact ⟨j,hj.trans (Nat.le_succ _),Q,hQ,hn⟩

theorem centered_room_pass_of_source {p : ℕ} [CharP K p]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w a errors excess)
    (δ m q room order : ℕ) (hδ : 0 < δ) (hm : 0 < m) (hw : 0 < w) (ha : 0 < a)
    (hwidth : data.d0.natDegree+affineDegree data.A0 ≤ δ)
    (horder : order < p) (hroom : order*(2*δ) ≤ room) (hcut : room ≤ m*a)
    (P : MvPolynomial (Fin 4) K) (hP : P ≠ 0) (cap incoming : FlagDegree)
    (hbox : P ∈ nestedCoefficientBox K (m*a-room+q*affineDegree data.A0) w (total cap) (middle cap) cap.all)
    (hclear : Koala6844Receipts.ClearedForm (centeredFlow data).A (centeredFlow data).numerator q P)
    (hcontact : ∀ i ∈ nodes, ContactAtLeast K (x i) (data.received 0 i) (data.received 1 i) m P)
    (H : MvPolynomial (Fin 4) K) (factors : Finset (RegularIndex H))
    (hincoming : Below (contactFlag (regularProduct H factors)) incoming)
    (hTrans : ∀ F ∈ factors, ¬ F.val ∣ (centeredFlow data).flow F.val) :
    ∃ remaining ⊆ factors,
      (let actual := contactFlag (regularProduct H remaining)
       actual.all ≤ min incoming.all (cap.all/(order+1)) ∧
       middle actual ≤ min (middle incoming) (middle cap/(order+1)) ∧
       total actual ≤ min (total incoming) (total cap/(order+1))) ∧
      ∀ F ∈ factors, F ∉ remaining → ∃ Q : MvPolynomial (Fin 4) K,
        IsRelPrime F.val Q ∧ Q ∈ nestedCoefficientBox K (m*a+q*affineDegree data.A0) w
          (total cap+order) (middle cap) cap.all ∧
        ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g Q = 0 := by
  classical
  let source : Set (MvPolynomial (Fin 4) K) := {P}
  let retained := roomResidualFactors H factors source order
  refine ⟨retained,roomResidualFactors_subset H factors source order,?_,?_⟩
  · exact room_residual_caps H factors source order incoming cap hincoming (Set.mem_singleton P) hP hbox
  · intro F hF hn
    have hdiv : ¬F.val^(order+1) ∣ P := by
      intro hd
      apply hn
      apply (mem_roomResidualFactors H factors source order F).mpr
      exact ⟨hF,fun Q hQ => (Set.mem_singleton_iff.mp hQ).symm ▸ hd⟩
    obtain ⟨j,hj,J,hJ,hproper⟩ := exists_exact_order F.val P order hdiv
    have hbox' : P ∈ nestedCoefficientBox K (m*a+q*affineDegree data.A0-j*(2*δ)) w
        (total cap) (middle cap) cap.all := by
      intro e he
      obtain ⟨ht,hy,hr,hwgt⟩ := hbox he
      have hd := (Nat.mul_le_mul_right (2*δ) hj).trans hroom
      exact ⟨ht,hy,hr,hwgt.trans_le (by omega)⟩
    let Q := (((centeredFlow data).flow : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K)^[j] P)
    obtain ⟨hQbox,hQzero⟩ := centered_flow_partner data δ m q j (total cap) (middle cap) cap.all
      hδ hm hw ha hwidth P hP hbox' hclear hcontact
    have hFi := (RCN167.positiveRFactors_spec H F.val F.property).1
    refine ⟨Q,?_,?_,hQzero⟩
    · unfold Q
      rw [hJ]
      exact Koala6844Moving.flow_partner_of_lt_characteristic (centeredFlow data) hFi hproper (hTrans F hF)
        (hj.trans_lt horder)
    · intro e he
      obtain ⟨ht,hy,hr,hwgt⟩ := hQbox he
      exact ⟨ht.trans (Nat.add_le_add_left hj _),hy,hr,hwgt⟩

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
