import ProximityPrize.SubmissionLower.Koala6844VirtualShortRoomReceipts
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPhasePayment
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPhaseSeeds
import ProximityPrize.SubmissionLower.Koala6844ReceiptsArithmeticBundle01


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial Koala6844Receipts Koala6844Normalization Koala6844Terminal
open ContactOrderBridge LocatorLowQuotient LocatorFactorAggregate LocatorBatchProductRoute
open RCN095 RCN140 RCN156 RCN167 RCN234 RCN266
open Koala6831Moving (contactFlag)
open Koala6831MovingAdaptive (aggregateFlag)
open scoped Classical BigOperators

noncomputable section
set_option autoImplicit false

variable {K E I : Type} [Field K] [Field E] [DecidableEq K] [DecidableEq I] [CharP K prime]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {errors excess : ℕ}

private theorem below_removed_room_factors
    (H : MvPolynomial (Fin 4) K) (incoming retained : Finset (RegularIndex H))
    (flag : FlagDegree) (h : Below (contactFlag (regularProduct H incoming)) flag) :
    Below (contactFlag (regularProduct H (incoming \ retained))) flag := by
  classical
  have hdiv : regularProduct H (incoming \ retained) ∣ regularProduct H incoming :=
    Finset.prod_dvd_prod_of_subset (incoming \ retained) incoming (fun F : RegularIndex H => F.val) Finset.sdiff_subset
  have hp := Koala6831Moving.contactFlag_below_of_dvd (regularProduct_ne_zero H incoming) hdiv
  exact ⟨hp.1.trans h.1, hp.2.1.trans h.2.1, hp.2.2.trans h.2.2⟩

theorem card_fixed_room_paid_family
    (D : CenteredVirtualData x domain σ degree agreements errors excess)
    (embed : K →+* E) (germ : ActiveResultantGerm D embed)
    (σpow : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^prime)
    (profile : FirstJetShape) (room : ℕ) (H : MvPolynomial (Fin 4) K)
    (incoming retained : Finset (RegularIndex H)) (f : Flag)
    (hf : f.ordered) (hg : (roomPartnerFlag profile room).ordered)
    (hfit : Below (contactFlag (regularProduct H incoming)) f.toFlagDegree)
    (hDigit : germDegreeT f (roomPartnerFlag profile room) < prime)
    (partners : RoomPartners D profile room H incoming retained) :
    ((incoming \ retained).biUnion (regularSeeds H D.selected D.seeds)).card ≤
      germPrice f (roomPartnerFlag profile room) := by
  let right := roomPartnerFlag profile room
  have hfull := below_removed_room_factors H incoming retained f.toFlagDegree hfit
  have hall : f.toFlagDegree.all = f.r := rfl
  have hflags : (physicalFlag (regularProduct H (incoming \ retained))).cumulativeLE f := by
    simpa only [Below, Flag.cumulativeLE, physicalFlag, Koala6831Moving.contactFlag_all,
      Koala6831Moving.contactFlag_middle, Koala6831Moving.contactFlag_total,
      Flag.toFlagDegree_middle f hf, Flag.toFlagDegree_total f hf, hall] using hfull
  apply card_germ_paid_family D embed germ σpow H (incoming \ retained) f right hg hflags hDigit
  intro F hF
  obtain ⟨Q, hrel, hbox, hzero⟩ := partners F (Finset.mem_sdiff.mp hF).1 (Finset.mem_sdiff.mp hF).2
  have hirr := (positiveRFactors_spec H F.val F.property).1
  have hQ : Q ≠ 0 := fun e => (hirr.isRelPrime_iff_not_dvd.mp hrel) (e.symm ▸ dvd_zero _)
  exact ⟨Q,hrel,physicalFlag_le_of_nested Q hQ _ degree right.t right.y right.r hbox,hzero⟩


theorem fixed_room_fee_callbacks
    (D : CenteredVirtualData x domain σ degree agreements errors excess)
    (embed : K →+* E) (germ : ActiveResultantGerm D embed)
    (σpow : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^prime) :
    (∀ (H : MvPolynomial (Fin 4) K) (A R : Finset (RegularIndex H)), H ≠ 0 → R ⊆ A →
      Below (aggregateFlag H A) primaryFlag.toFlagDegree →
      RoomPartners D firstRoomShape firstRoomCut H A R →
      (phaseSeeds H D.selected D.seeds (A \ R)).card ≤ 1911243880121235) ∧
    (∀ (H : MvPolynomial (Fin 4) K) (A R : Finset (RegularIndex H)), H ≠ 0 → R ⊆ A →
      Below (aggregateFlag H A) firstResidualFlag.toFlagDegree →
      RoomPartners D secondRoomShape secondRoomCut H A R →
      (phaseSeeds H D.selected D.seeds (A \ R)).card ≤ 524153816993650) := by
  constructor
  · intro H A R _ _ hfit hpartners
    exact (card_fixed_room_paid_family D embed germ σpow firstRoomShape firstRoomCut H A R
      primaryFlag (by unfold Flag.ordered; decide +kernel) (by unfold Flag.ordered; decide +kernel)
      hfit room_digit_gates.1 hpartners).trans (by decide +kernel)
  · intro H A R _ _ hfit hpartners
    exact (card_fixed_room_paid_family D embed germ σpow secondRoomShape secondRoomCut H A R
      firstResidualFlag (by unfold Flag.ordered; decide +kernel) (by unfold Flag.ordered; decide +kernel)
      hfit room_digit_gates.2 hpartners).trans (by decide +kernel)



end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
