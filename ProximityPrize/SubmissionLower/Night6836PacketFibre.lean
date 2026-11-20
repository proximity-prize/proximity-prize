/- Apache-2.0. The physical regular family of Bome2017's five-stage proof
   instantiates BitWonka's packet from PR 623. Keep the incidence proof's
   window parameters explicit so this bridge checks against the packet core. -/
import ProximityPrize.SubmissionLower.Packet6833P04
import ProximityPrize.SubmissionLower.Night6836FibreIdentity

namespace ProximityPrize.SubmissionLower.Night6836PacketFibre
open scoped Classical
open RCN095 RCN130 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN313
open Koala6831MovingPaid

set_option autoImplicit false
variable {K I : Type} [Field K] [Fintype I]

theorem window_fibre_le (x : I ↪ K) (primary : MvPolynomial (Fin 4) K)
    (D L s : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Γ : Finset K) (selected : K → Polynomial K) (u₀ u₁ : I → K)
    (hcard : Fintype.card I = 262144)
    (degree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ 131071)
    (agreement : ∀ γ ∈ Γ, 181039 ≤ ((Finset.univ : Finset I).filter
      (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (pencil : RCN238.NoLargeSelectedPencil selected Γ 131071 81105)
    (r y t low cap : ℕ)
    (hW : ∀ P : DU.Packet (x : I → K) t y r,
      low ≤ wt residualTotalWeights P.F → P.seeds.card ≤ cap)
    (hr5 : 5 ≤ r) (hrh : r ≤ 18) (hy : r+2 ≤ y) (hyh : y ≤ 76)
    (hyt : y ≤ t) (hth : t ≤ 9352)
    (F : RegularIndex primary) (box : F.1 ∈ globalCoefficientBox K D 131071 L s)
    (hr : wt residualSWeights F.1 ≤ r) (hyF : wt residualYSWeights F.1 ≤ y)
    (ht : wt residualTotalWeights F.1 ≤ t) (hlow : low ≤ wt residualTotalWeights F.1) :
    (regularFiber primary Γ selected F).card ≤ cap := by
  let P := CVL.factorPacket F D L s t y r hDlow hDchar box hr5 hrh hy hyh hyt hth
    hr hyF ht x u₀ u₁ hcard selected Γ degree agreement (Raw6836.packet_pencil pencil)
  rw [Raw6836.packet_regular_seeds]
  exact hW P hlow

#print axioms window_fibre_le
end ProximityPrize.SubmissionLower.Night6836PacketFibre
