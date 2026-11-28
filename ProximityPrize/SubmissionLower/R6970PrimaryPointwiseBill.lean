import ProximityPrize.SubmissionLower.R6970PrimaryRankBill
import ProximityPrize.SubmissionLower.Z6969Pack0427

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Research6970.Height2313.Lower6960.Prefix6969Main

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (ODECaps mass mass_mono)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (Mass massQ massQ_mono dotQ running weightedBill ODEGuard)
open _root_.Lower6960.Far6969RescueGeometry (Model Family word OnMark OnSurface)
open Research6970.Height2313.Lower6960.Prefix6969Rates (curveMarks mem_curveMarks)
open _root_.Lower6960 _root_.Research6969
open Research6966
open PrefixRows (Common)
open scoped Classical BigOperators

noncomputable section

def RankBill.Pointwise (s : Plan) (price : Pricing) (band : Band) (lossCap : ℕ) : Prop :=
  ∀ j b : ℕ, j ≤ s.initialCap 1 → b ≤ s.initialCap 2 → j ≤ b →
    RankBill.cellLoss s price band j j b b ≤ lossCap

private theorem CutBooks.pointwise_payment
    {s : Plan} {price : Pricing} {band : Band} {lossCap : ℕ}
    {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows s F Crt}
    (ini : Initial R) (C : CutBooks ini) (priced : price.Valid s band)
    (hi : M.overhead.toNat ≤ band.last)
    (pointwise : RankBill.Pointwise s price band lossCap) :
    C.paid.card + price.charge ini.final ≤ RankBill.fee s band lossCap := by
  have size (k : Fin 4) : mass ini.rankExit k ≤ s.initialCap k :=
    (mass_mono (subset_union_left : ini.rankExit ⊆ ini.rankExit ∪ ini.parents) k).trans (ini.fits k)
  have mix : mass ini.rankExit 1 ≤ mass ini.rankExit 2 :=
    _root_.Research6969.MixedSectionCredit.mass_le _ (fun I mem => (ini.rank_geom I mem).1)
  have fee := pointwise (mass ini.rankExit 1) (mass ini.rankExit 2) (size 1) (size 2) mix
  have loss := C.rank_cell_loss ini priced hi le_rfl le_rfl le_rfl le_rfl (size 2) fee
  exact C.paid_from_rank_loss ini hi loss

theorem main_prefix_rank_pointwise {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (sched : Plan) (valid : sched.Valid) (band : Band) (price : Pricing)
    (priced : price.Valid sched band)
    {first extra a low floor : ℕ} {outer : P1_7.Bank}
    (source : sched.Sources first band.last outer extra a low floor)
    {lossCap : ℕ}
    (bill : RankBill.Pointwise sched price band lossCap)
    (firstPos : 0 < first)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (known : Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (degree : a ≤ jetDegree G) (seed : low ≤ seedDegree G)
    (physical : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ (R : Rows sched F Crt) (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      R.out.exception = G ∧ C.paid.card + price.charge ini.final ≤ RankBill.fee sched band lossCap ∧
      (∀ k, massQ ini.final k ≤ sched.history sched.last k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ :=
  main_prefix_with_rank_payment F Crt sched valid band price source
    (fun _ ini C => C.pointwise_payment ini priced hi bill)
    firstPos lo hi noPole residues phys known degree seed physical

end
end Research6970.Height2313.Lower6960.Prefix6969Main
