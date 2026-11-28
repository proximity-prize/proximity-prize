import ProximityPrize.SubmissionLower.R6970Height2313Classification

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0779
set_option autoImplicit true
namespace Research6969.TransitionPacket
noncomputable section
open Finset Polynomial
open K1 (K I p)
open K1_14 (Jet Equation Seeds atX jetAt)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (Ambient toJet UsesSeed)
open K1_14_2_2 (Active RowCaps mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface ProjectedProduct Parent SeedField)
open _root_.Research6969.TransitionPacket (Pair)
open _root_.Lower6960.Far6969RescueGeometry (Model Family word OnSurface)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NonlinearMarkRows (evaluate)
open scoped Classical Differential
set_option maxRecDepth 10000
set_option maxHeartbeats 2300000

theorem reduce_singleton {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} {H:Jet} {m r} (P:Pair F Crt H m r)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2557) {d U limit:ℕ}
    (prime:Prime H) (slope:H.natDegree=1) (nonlin:2≤jetDegree H) (pos:0<U)
    (width:∀ j i,((H.coeff j).coeff i).totalDegree≤U)
    (dp:0<d) (phys:131071+M.overhead≤(d:ℤ)) (gap:d<179730) (tame:d<p)
    (mg:41*m.seedMass<p) (rg:41*r.seedMass<p)
    (table:∀ i j:Fin 22,i.val+j.val≤21→JointLedger.Pass m r (JointRouted.seedWeight d U)
      (JointRouted.ordWeight d (jetDegree H-1)) limit i.val j.val) :
    Γ.card≤limit ∨ ∃ (f:Equation) (G:Pade.Row SeedField),
      ProjectedProduct (P.main∪P.rescue) f ∧ 22≤f.natDegree ∧ G.primitive ∧
      G.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue))
        (TransitionClassification.content (TransitionClassification.band f.natDegree)) := by
  classical
  have geom (q) (hq:q∈P.main∪P.rescue):Parent q:=((mem_union.mp hq).elim (fun h=>(P.mainGeo q h).1) (fun h=>(P.rescueGeo q h).1))
  obtain ⟨f,union⟩:=JointProjection.exists_product _ geom
  by_cases low:f.natDegree≤21
  · left
    obtain ⟨G,N,gp,eq,deg⟩:=HelperGraph.of_prime prime slope
    apply JointClosure.small F hi P.paid P.main P.rescue (fun q h=>(P.mainGeo q h).1)
      (fun q h=>(P.rescueGeo q h).1) P.aSrc P.bSrc P.mainActive P.rescueActive
      P.mainOrigin P.rescueOrigin m r P.wm P.wr P.mainOrd P.mainSeed P.rescueOrd P.rescueSeed
      P.bill P.boundsM P.boundsR N gp (deg ▸ nonlin) pos dp phys gap tame (eq ▸ width) _ union low mg rg (deg ▸ table)
    intro z hz
    rcases P.cover z hz with paid|⟨_,main⟩|⟨root,regular,rescue⟩
    · exact Or.inl paid
    · exact Or.inr (Or.inl main)
    · refine Or.inr (Or.inr ⟨?_,?_,rescue⟩)
      · simpa only [den,rhs,eq] using Prefix6969Rescue.graph_law slope root
      · simpa only [den,eq,Prefix6969Rescue.regular,Prefix6969Rescue.denominator,
          NativeLostCurve.seed] using regular
  · right
    rcases union with proj|⟨_,rfl⟩
    · have live:(P.main∪P.rescue).Nonempty:=by
        by_contra empty
        have unit:=Research6966.NativeOrdinateMass.divides_of_member (D:=1) proj (fun q h=>False.elim (empty ⟨q,h⟩))
        have small:=natDegree_le_of_dvd unit (one_ne_zero: (1:Equation)≠0)
        simp only [natDegree_one] at small
        omega
      have pass q (hq:q∈P.main∪P.rescue):TerminalBanks.Pass Crt (word M) 179730 SpreadCatalogue.shape q:=
        (mem_union.mp hq).elim (fun h=>(P.mainGeo q h).2.1) (fun h=>(P.rescueGeo q h).2.1)
      obtain ⟨G,gp,degree,control⟩:=Research6970.Height2313.Classification.graph_above_twenty_one_from2313 Crt (word M) lo hi _ live geom pass proj (by omega)
      exact ⟨f,G,proj,by omega,gp,degree,control⟩
    · simp at low


end
end Research6969.TransitionPacket
end Z6969Source0779

end Research6970.Height2313
