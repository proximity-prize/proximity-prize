import ProximityPrize.SubmissionLower.Koala6844VirtualShortPhaseSeeds
import ProximityPrize.SubmissionLower.Koala6844VirtualShortRoomReceipts
import ProximityPrize.SubmissionLower.Koala6844VirtualShortAdaptiveReceipts


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical
open RCN095 RCN140 RCN266 RCN286
open LocatorBatchProductRoute LocatorFactorAggregate LocatorLowQuotient
open Koala6831MovingAdaptive (aggregateFlag)
open Koala6844Receipts Koala6844Normalization Koala6844Terminal

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4200
set_option maxHeartbeats 2500000

variable {K I : Type} [Field K] [CharP K prime] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {excess : Nat}

structure ShortPhaseFees
    (data : CenteredVirtualData x domain σ degree agreements 81185 excess)
    (hsize : domain.card ≤ nodes)
    (hpole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth) : Prop where
  firstRoom : ∀ (H : MvPolynomial (Fin 4) K) (A R : Finset (RegularIndex H)), H ≠ 0 → R ⊆ A →
    Below (aggregateFlag H A) primaryFlag.toFlagDegree →
    RoomPartners data firstRoomShape firstRoomCut H A R →
    (phaseSeeds H data.selected data.seeds (A \ R)).card ≤ 1911243881988435
  secondRoom : ∀ (H : MvPolynomial (Fin 4) K) (A R : Finset (RegularIndex H)), H ≠ 0 → R ⊆ A →
    Below (aggregateFlag H A) firstResidualFlag.toFlagDegree →
    RoomPartners data secondRoomShape secondRoomCut H A R →
    (phaseSeeds H data.selected data.seeds (A \ R)).card ≤ 524153819097300
  firstAdaptive : ∀ (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H)),
    H ≠ 0 → Below (aggregateFlag H A) afterRooms.toFlagDegree →
    ∀ pass : CenteredAdaptivePass (firstCenteredAdaptiveSource data hsize hpole) poleWidth H A,
    (phaseSeeds H data.selected data.seeds (A \ pass.residue)).card ≤ 524260340386850
  secondAdaptive : ∀ (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H)),
    H ≠ 0 → Below (aggregateFlag H A) afterRooms.toFlagDegree →
    ∀ first : CenteredAdaptivePass (firstCenteredAdaptiveSource data hsize hpole) poleWidth H A,
    ∀ second : CenteredAdaptivePass (secondCenteredAdaptiveSource data hsize hpole) poleWidth H first.residue,
    (phaseSeeds H data.selected data.seeds (first.residue \ second.residue)).card ≤ 6777813845395257


end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
