import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import ProximityPrize.SubmissionLower.Koala6844VirtualShortRoom
import ProximityPrize.SubmissionLower.Koala6844VirtualShortFirstJetProfile
import ProximityPrize.SubmissionLower.Koala6844ReceiptsExactBand


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical
open Koala6844Normalization Koala6844Receipts LocatorLowQuotient LocatorFactorAggregate
open LocatorBatchProductRoute RCN095 RCN130 RCN266
open Koala6831Moving (contactFlag)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I] [CharP K prime]

def RoomPartners
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ degree agreements errors excess)
    (profile : FirstJetShape) (room : ℕ) (H : MvPolynomial (Fin 4) K)
    (incoming retained : Finset (RegularIndex H)) : Prop :=
  let f := roomPartnerFlag profile room
  ∀ F ∈ incoming, F ∉ retained → ∃ Q : MvPolynomial (Fin 4) K,
    IsRelPrime F.val Q ∧ Q ∈ nestedCoefficientBox K (profile.m*agreements+profile.q*affineDegree data.A0)
      degree f.t f.y f.r ∧ ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g Q = 0

private theorem flag_all (f : Flag) : f.toFlagDegree.all = f.r := rfl

theorem exists_checked_room_pass
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ degree agreements errors excess)
    (hN : nodes.card ≤ Koala6844Receipts.nodes)
    (hWidth : data.d0.natDegree+affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (profile : FirstJetShape) (room : ℕ) (hB : profile.s < degree)
    (hM : profile.m+profile.s ≤ (firstJetFlag profile room).y)
    (hL : (firstJetFlag profile room).y ≤ profile.L)
    (hq : profile.q ≤ (firstJetFlag profile room).y) (hm : 0 < profile.m)
    (hgap : 0 < firstJetGap profile room) (hRoomSize : room ≤ profile.m*agreements)
    (hOrder : room/flowWidth < prime)
    (H : MvPolynomial (Fin 4) K) (factors : Finset (RegularIndex H)) (bound : Flag)
    (hOrdered : bound.ordered)
    (hIncoming : Below (contactFlag (regularProduct H factors)) bound.toFlagDegree)
    (hTrans : ∀ F ∈ factors, ¬ F.val ∣ (centeredFlow data).flow F.val) :
    ∃ retained ⊆ factors,
      Below (contactFlag (regularProduct H retained)) (remainingAfterRoom bound profile room).toFlagDegree ∧
      RoomPartners data profile room H factors retained := by
  obtain ⟨P,hP,hbox,hclear,hcontact,_⟩ := exists_checked_firstJet_profile data hN hWidth hLead profile room
    hB hM hL hq hm hgap
  let f := firstJetFlag profile room
  have hf : f.ordered := ⟨by exact (Nat.le_add_left _ _).trans hM, hL.trans (Nat.le_add_right _ _)⟩
  have hbox' : P ∈ nestedCoefficientBox K (profile.m*agreements-room+profile.q*affineDegree data.A0)
      degree (total f.toFlagDegree) (middle f.toFlagDegree) f.toFlagDegree.all := by
    rw [Flag.toFlagDegree_total f hf,Flag.toFlagDegree_middle f hf]
    exact hbox
  have hroom : (room/flowWidth)*(2*poleWidth) ≤ room := Nat.div_mul_le_self room flowWidth
  obtain ⟨R,hR,hres,hparts⟩ := centered_room_pass_of_source data poleWidth profile.m profile.q room (room/flowWidth)
    (by decide) hm (by decide) (by decide) hWidth hOrder hroom hRoomSize P hP f.toFlagDegree
    bound.toFlagDegree hbox' hclear hcontact H factors hIncoming hTrans
  let out := remainingAfterRoom bound profile room
  have hout : out.ordered := by
    constructor
    · exact min_le_min hOrdered.1 (Nat.div_le_div_right hf.1)
    · exact min_le_min hOrdered.2 (Nat.div_le_div_right hf.2)
  refine ⟨R,hR,?_,?_⟩
  · show Below (contactFlag (regularProduct H R)) out.toFlagDegree
    unfold Below
    rw [Flag.toFlagDegree_middle out hout,Flag.toFlagDegree_total out hout]
    simpa only [out,remainingAfterRoom,f,Flag.toFlagDegree_middle _ hOrdered,Flag.toFlagDegree_total _ hOrdered,
      Flag.toFlagDegree_middle _ hf,Flag.toFlagDegree_total _ hf,flag_all] using hres
  · unfold RoomPartners
    simpa only [roomPartnerFlag,Flag.toFlagDegree_total f hf,Flag.toFlagDegree_middle f hf,flag_all] using hparts


theorem exists_two_checked_room_passes
    {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x domain σ degree agreements errors excess)
    (hN : domain.card ≤ Koala6844Receipts.nodes)
    (hWidth : data.d0.natDegree+affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (hGap₀ : 0 < firstJetGap firstRoomShape firstRoomCut)
    (hGap₁ : 0 < firstJetGap secondRoomShape secondRoomCut)
    (H : MvPolynomial (Fin 4) K) (factors : Finset (RegularIndex H))
    (hIncoming : Below (contactFlag (regularProduct H factors)) primaryFlag.toFlagDegree)
    (hTrans : ∀ F ∈ factors, ¬ F.val ∣ (centeredFlow data).flow F.val) :
    ∃ first ⊆ factors, ∃ last ⊆ first,
      Below (contactFlag (regularProduct H first)) firstResidualFlag.toFlagDegree ∧
      Below (contactFlag (regularProduct H last)) afterRooms.toFlagDegree ∧
      RoomPartners data firstRoomShape firstRoomCut H factors first ∧
      RoomPartners data secondRoomShape secondRoomCut H first last := by
  have hp : primaryFlag.ordered := by unfold Flag.ordered; decide +kernel
  have hf : firstResidualFlag.ordered := by unfold Flag.ordered; decide +kernel
  obtain ⟨first,hfsub,hfcap,hfPartner⟩ := exists_checked_room_pass data hN hWidth hLead firstRoomShape firstRoomCut
    (by decide) (by decide) (by decide) (by decide) (by decide) hGap₀ (by decide) (by decide)
    H factors primaryFlag hp hIncoming hTrans
  obtain ⟨last,hlsub,hlcap,hlPartner⟩ := exists_checked_room_pass data hN hWidth hLead secondRoomShape secondRoomCut
    (by decide) (by decide) (by decide) (by decide) (by decide) hGap₁ (by decide) (by decide)
    H first firstResidualFlag hf hfcap (fun F hF => hTrans F (hfsub hF))
  exact ⟨first,hfsub,last,hlsub,hfcap,hlcap,hfPartner,hlPartner⟩


theorem room_digit_gates : germDegreeT primaryFlag (roomPartnerFlag firstRoomShape firstRoomCut) < prime ∧
    germDegreeT firstResidualFlag (roomPartnerFlag secondRoomShape secondRoomCut) < prime := by decide +kernel

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
