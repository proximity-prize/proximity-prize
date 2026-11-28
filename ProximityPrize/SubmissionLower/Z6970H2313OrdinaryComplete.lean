import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryRouteCore

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.OrdinaryComplete
noncomputable section
open K1 (K I p)
open K1_14 (L)
open K1_14_1 (PoleData CRTLift poleProduct MarkResidues)
open K1_14_3 (SeedField)
open _root_.Lower6960
open Research6969
open Far6969RescueGeometry (Model Family)
open Research6966
open Finset Polynomial
open JointLedger (Book)
open Research6970.Height2313.OrdinaryRoute
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 13000

def upper (cap:ℕ) (b:Fin 8):ℕ:=![22,24,27,32,40,49,63,cap] b

theorem upper_band {e cap:ℕ} (room:e≤cap):e≤upper cap (TransitionClassification.band e):=by
  unfold TransitionClassification.band
  split_ifs <;>dsimp [upper] <;>omega

def Catalogue (first last:ℕ) (m:Book) (g:ℕ):Prop:=
  ∀(b:Fin 8) (a:ℕ),0<a→a≤TransitionClassification.maxGraph b→
    Tail first last m g (TransitionClassification.grade b) (upper g b) (TransitionClassification.content b) a 0

def GraphClassifier : Prop :=
  ∀ {h : ℕ} (lo : 2308 ≤ h) (hi : h ≤ 2313) {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (parents : Finset K1_14_3.Surface) (live : parents.Nonempty)
    (geo : ∀ q ∈ parents, K1_14_3.Parent q)
    (pass : ∀ q ∈ parents, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {f : K1_14.Equation} (proj : K1_14_3.ProjectedProduct parents f) (large : 22 ≤ f.natDegree),
    ∃ G : Pade.Row SeedField, G.primitive ∧
      G.graphDegree ≤ TransitionClassification.maxGraph (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets parents)
        (TransitionClassification.content (TransitionClassification.band f.natDegree))

theorem count {m:Book} {g:ℕ} (classify : GraphClassifier) (valid:Catalogue 2308 2313 m g)
    (small:OrdinaryPackets.prices m 21=true) (char:41*m.seedMass<p) 
    {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (P:Prefix6969Early.Packet F Crt m.fee m.ordinateCredit m.seedCredit g m.seedMass)
    (lo : 2308 ≤ M.overhead.toNat) (upper : M.overhead.toNat ≤ 2313)
    (noPole:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈Γ,MarkResidues D (M.label z) (F.scalar z)) : Γ.card≤OrdinaryCell.target := by
  have hi : M.overhead.toNat ≤ 2557 := by omega
  by_cases tiny : P.projected.natDegree ≤ 21
  · exact Research6969.Ordinary.small F hi P.paid P.project P.cover m P.bill P.seed_cap tiny
      (by decide) char (fun i => of_decide_eq_true (GradeTable.entry small i.isLt))
  have large : 22 ≤ P.projected.natDegree := by omega
  have project : K1_14_3.ProjectedProduct P.parents P.projected := by
    rcases P.project with actual | ⟨_,zero⟩
    · exact actual
    · rw [zero, natDegree_one] at large
      omega
  have nonempty:P.parents.Nonempty:=by
    by_contra empty
    have dvd:=NativeOrdinateMass.divides_of_member (D:=1) project (fun q h=>False.elim (empty ⟨q,h⟩))
    have zero:=natDegree_le_of_dvd dvd (one_ne_zero:(1:K1_14.Equation)≠0)
    simp only [natDegree_one] at zero;omega
  have classified :
      ∃ G : Pade.Row SeedField, G.primitive ∧
        G.graphDegree ≤ TransitionClassification.maxGraph (TransitionClassification.band P.projected.natDegree) ∧
        Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets P.parents)
          (TransitionClassification.content (TransitionClassification.band P.projected.natDegree)) := by
    exact classify lo upper Crt (Far6969RescueGeometry.word M) P.parents nonempty P.geo P.terminal project large
  obtain ⟨G,gp,cap,ctrl⟩ := classified
  let b:=TransitionClassification.band P.projected.natDegree
  obtain ⟨N⟩:=PadeNativeQuotient.exists_native gp
  obtain ⟨physical⟩:=HelperPhysicalModel.exists_model Crt (NativeWitnessBank.irreducible N gp)
    (by rw [NativeGraphMarks.slope_degree N gp];decide)
  let x:Context 2308 2313 m g:=⟨u,del,M,Γ,F,D,Crt,P,project,nonempty,G,N,gp,physical,
    TransitionClassification.content b,ctrl,le_rfl,by decide,lo,upper,noPole,res⟩
  have positive:0<G.graphDegree:=by
    unfold Pade.Row.graphDegree
    exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact valid b G.graphDegree positive cap x ⟨TransitionClassification.lower_bound large,upper_band P.degree_cap,
    rfl,rfl,Nat.zero_le _,by simp⟩

end
end Research6970.Height2313.OrdinaryComplete
