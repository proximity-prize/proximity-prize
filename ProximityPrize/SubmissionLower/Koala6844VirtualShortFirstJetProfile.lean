import ProximityPrize.SubmissionLower.Koala6844VirtualShortFirstJetSource
import ProximityPrize.SubmissionLower.Koala6844ReceiptsFirstJetGap


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Koala6844Normalization Koala6844Receipts LocatorLowQuotient ContactOrderBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]

theorem firstJetProfileKernel_gap_le (profile : FirstJetShape) (room N : ℕ)
    (hN : N ≤ Koala6844Receipts.nodes) (hB : profile.s < degree)
    (hM : profile.m+profile.s ≤ (firstJetFlag profile room).y)
    (hL : (firstJetFlag profile room).y ≤ profile.L)
    (hq : profile.q ≤ (firstJetFlag profile room).y) :
    let D := fun _ : ℕ => firstJetCutoff profile room
    let U := (firstJetFlag profile room).y
    firstJetGap profile room ≤
      Fintype.card (NormalizedIndex D degree (degree+poleWidth) profile.L profile.s 0 U profile.q) -
        N*normalizedRankBudget D degree profile.m profile.L profile.s 0 U profile.q := by
  dsimp only
  rw [firstJetGap_exact profile room hB hM hL hq]
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right _ hN) _

theorem exists_checked_firstJet_profile
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ degree agreements errors excess)
    (hN : nodes.card ≤ Koala6844Receipts.nodes)
    (hWidth : data.d0.natDegree+affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (profile : FirstJetShape) (room : ℕ) (hB : profile.s < degree)
    (hM : profile.m+profile.s ≤ (firstJetFlag profile room).y)
    (hL : (firstJetFlag profile room).y ≤ profile.L)
    (hq : profile.q ≤ (firstJetFlag profile room).y) (hm : 0 < profile.m)
    (hgap : 0 < firstJetGap profile room) :
    ∃ P : MvPolynomial (Fin 4) K, P ≠ 0 ∧
      P ∈ nestedCoefficientBox K (firstJetCutoff profile room+profile.q*affineDegree data.A0) degree
        (profile.L+profile.q) (firstJetFlag profile room).y profile.s ∧
      ClearedForm (centeredFlow data).A (centeredFlow data).numerator profile.q P ∧
      (∀ i ∈ nodes, ContactAtLeast K (x i) (data.received 0 i) (data.received 1 i) profile.m P) ∧
      ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g P = 0 := by
  let D := fun _ : ℕ => firstJetCutoff profile room
  let U := (firstJetFlag profile room).y
  have hh := hgap.trans_le (firstJetProfileKernel_gap_le profile room nodes.card hN hB hM hL hq)
  have he : nodes.card*normalizedRankBudget D degree profile.m profile.L profile.s 0 U profile.q <
      Fintype.card (NormalizedIndex D degree (degree+poleWidth) profile.L profile.s 0 U profile.q) :=
    Nat.sub_pos_iff_lt.mp hh
  exact exists_centered_firstJet_source data D (degree+poleWidth) profile.m profile.L profile.s U profile.q
    (by decide) (by decide) hm hL hq (Nat.sub_le _ _) rfl.le (by omega) hLead he


theorem exists_checked_primary
    {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x domain σ degree agreements errors excess)
    (hN : domain.card ≤ Koala6844Receipts.nodes)
    (hWidth : data.d0.natDegree+affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (hGap : 0 < firstJetGap primaryShape 0) :
    ∃ P : MvPolynomial (Fin 4) K, P ≠ 0 ∧
      P ∈ nestedCoefficientBox K primaryWeight degree primaryFlag.t primaryFlag.y primaryFlag.r ∧
      ClearedForm (centeredFlow data).A (centeredFlow data).numerator primaryShape.q P ∧
      (∀ i ∈ domain, ContactAtLeast K (x i) (data.received 0 i) (data.received 1 i) primaryShape.m P) ∧
      ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g P = 0 := by
  have hh := hGap.trans_le (firstJetProfileKernel_gap_le primaryShape 0 domain.card hN
    (by decide) (by decide) (by decide) (by decide))
  exact exists_short_primary data hWidth hLead (Nat.sub_pos_iff_lt.mp hh)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
