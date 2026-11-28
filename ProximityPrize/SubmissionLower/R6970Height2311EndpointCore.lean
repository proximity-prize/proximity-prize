import ProximityPrize.SubmissionLower.R6970Height2313NearModel
import ProximityPrize.SubmissionLower.R6970Height2313PairState
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryClaimNear
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryClaimNearQuadratic19
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryClaimNearCubic41
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryClaimNearQuintic26

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1018
set_option autoImplicit true
namespace Research6969.HighPackets
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation L)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct nodeL)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface SeedField Parent ProjectedProduct)
open _root_.Lower6960.Far6969RescueGeometry (Model Family word)
open Research6966
open PadeNativeQuotient (Native)
open _root_.Research6969.TransitionPacket (Pair)
open Research6970.Height2313.Research6969.TransitionPacket.NormalCatalogue (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

theorem from_outcome (win:Goal) (reduce : Research6970.Height2313.Research6969.TransitionPacket.NormalCatalogue.Reducer) {u del} {M:Model u del} {Γ} (F:Family M Γ)
    {D:PoleData M.overhead.toNat} (Crt:CRTLift D) (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodes:∀j:I,(poleProduct D).eval (algebraMap K L (K1.node j))≠0)
    (res:∀z∈Γ,MarkResidues D (M.label z) (F.scalar z))
    (out:Research6970.Height2313.Lower6960.Prefix6969Early.Outcome F Crt):Γ.card≤274779381266040419:=by
  cases out with
  | ordinary P=>exact Research6970.Height2313.OrdinaryClaimNear.count F Crt P lo hi nodes res
  | quadratic19 P=>exact Research6970.Height2313.OrdinaryClaimNearQuadratic19.count F Crt P lo hi nodes res
  | cubicWide P=>exact Research6970.Height2313.OrdinaryClaimNearCubic41.count F Crt P lo hi nodes res
  | quinticMid P=>exact Research6970.Height2313.OrdinaryClaimNearQuintic26.count F Crt P lo hi nodes res
  | normal i H prime slope degree caps seedExact P md rd=>
    rcases reduce i P lo hi prime slope degree caps with complete|⟨f,G,project,hg,gp,gcap,control⟩
    · exact complete
    · obtain ⟨N⟩:=PadeNativeQuotient.exists_native gp
      obtain ⟨physical⟩:=HelperPhysicalModel.exists_model Crt (NativeWitnessBank.irreducible N gp)
        (by rw [NativeGraphMarks.slope_degree N gp];decide)
      exact win i ⟨u,del,M,Γ,F,D,Crt,lo,hi,nodes,res,H,prime,slope,degree,caps,seedExact,P,md,rd,
        f,project,hg,G,N,gp,gcap,control,physical,none⟩

end
end Research6969.HighPackets
end Z6969Source1018


section Z6969Source2541
set_option autoImplicit true
namespace Research6969.HighEndpoint
open _root_.Lower6960.Far6969RescueGeometry (Model Family)
open K1_14_1 (poleProduct nodeL)
open ProximityPrize.Benchmark
open Polynomial

/-- Everything outside the selected large-degree normal packets is
discharged on the concrete lower-track model. -/
theorem count (high:Research6970.Height2313.Research6969.HighPackets.Goal) (reduce : Research6970.Height2313.Research6969.TransitionPacket.NormalCatalogue.Reducer) {u del} (M:Model u del) {Γ}
    (F:Family M Γ) (lo:2308≤M.overhead) (hi:M.overhead≤2313):
    Γ.card≤274779381266040419 := by
  obtain ⟨D,⟨Crt⟩,safe,res⟩:=_root_.Lower6960.Far6969PoleChart.of_family M F
  obtain ⟨out⟩:=Research6970.Height2313.Lower6960.Prefix6969Early.route_using Research6970.Height2313.Lower6960.Prefix6969Early.choose F Crt (by omega) (by omega) safe res
  exact Research6970.Height2313.Research6969.HighPackets.from_outcome high reduce F Crt (by omega) (by omega) (fun i=>by
    change (poleProduct D).eval (nodeL i)≠0
    rw [poleProduct,eval_mul];exact mul_ne_zero (safe 0 i) (safe 1 i)) res out

end Research6969.HighEndpoint
end Z6969Source2541


end Research6970.Height2313
