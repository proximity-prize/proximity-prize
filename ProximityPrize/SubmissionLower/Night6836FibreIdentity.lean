/- Apache-2.0. Identify the two regular-witness predicates used on the
   same selected seed in the extended 68.36 packet and five-group proofs. -/
import ProximityPrize.SubmissionLower.Packet6833P01
import ProximityPrize.SubmissionLower.Koala6831MovingPaidStageCounts
namespace ProximityPrize.SubmissionLower.Raw6836
open scoped Classical
open RCN095 RCN130 RCN156 RCN234 RCN238 RCN266 Koala6831MovingPaid
noncomputable section
variable {K : Type} [Field K]

theorem packet_regular_seeds (H : MvPolynomial (Fin 4) K) (S : Finset K)
    (sel : K → Polynomial K) (F : RegularIndex H) :
    regularFiber H S sel F = RCN140.regularSeeds H sel S F := by
  ext g
  rw [mem_regularFiber, RCN140.regularSeeds, Finset.mem_filter]
  exact Iff.rfl

theorem packet_pencil {S : Finset K} {sel : K → Polynomial K} {d e : ℕ}
    (h : NoLargeSelectedPencil sel S d e) : RCN238.BL sel S d e := h
end
end ProximityPrize.SubmissionLower.Raw6836
#print axioms ProximityPrize.SubmissionLower.Raw6836.packet_regular_seeds
#print axioms ProximityPrize.SubmissionLower.Raw6836.packet_pencil
