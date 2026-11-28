import ProximityPrize.SubmissionLower.R6970Height2313Rescue

set_option Elab.async false
set_option autoImplicit true

namespace Research6970.Height2313.Lower6960.Prefix6969Rescue
open _root_.Lower6960 _root_.Research6969
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_2 (UsesSeed toJet)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ)
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6966
open scoped Classical BigOperators

noncomputable section

theorem normal_prefix_direct {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    {plan : Plan} {x : NormalPrice}
    {first : ℕ} (S : plan.Sources first 2313) (cert : x.Valid plan)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (seed : plan.seedFloor ≤ seedDegree G)
    (physical : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0) :
    ∃ (R : Run F Crt G plan) (B : Book R) (Q : Finset Surface),
      B.final = R.terminal ∧
      (Invoice.paid B).card + Invoice.charge B x.credit ≤ x.fee ∧
      (∀ k, massQ B.final k ≤ plan.history (plan.count-1) k) ∧
      (∀ q∈Q, Parent q ∧ Prefix6969Wide.SurfacePass Crt (word M) q ∧
        G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal=J.comap toJet) ∧
      ∀ γ∈Γ, γ∈Invoice.paid B ∨
        (regular G (M.label γ) (F.scalar γ) ∧ ∃ q∈Q, OnSurface F q γ) := by
  obtain ⟨R⟩ := S.run F Crt lo hi noPole residues phys prime
    (le_of_eq (cert.slope_floor.trans slope.symm)) seeded caps degree seed physical
  have geomCaps : RowCaps G (graphShape 2 x.seed) := cert.graph_shape ▸ caps
  obtain ⟨event⟩ := Invoice.normal_event R (le_refl 2) cert.seed_pos prime slope geomCaps cert.char hi roots
    cert.tau_nonneg cert.tau_le_one cert.rank_small x.credit noPole residues cert.exact_fee cert.retained
  let B := event.book
  obtain ⟨surfaces, geom, marked⟩ := Invoice.Book.surfaces B
  refine ⟨R, B, surfaces, event.final, event.count, ?_, ?_, ?_⟩
  · intro k
    show massQ event.book.final k ≤ _
    rw [event.final]
    exact Invoice.Run.mass_terminal R k
  · intro q hq
    obtain ⟨parent, J, mem, origin⟩ := geom q hq
    obtain ⟨pass, inIdeal⟩ := Invoice.Book.terminal_parent B event.final mem origin
    exact ⟨parent, pass, inIdeal, J, mem, origin⟩
  · intro γ mem
    rcases Invoice.Book.paid_or_regular B mem (roots γ mem) with paid | ⟨reg, survivor⟩
    · exact Or.inl paid
    · exact Or.inr ⟨reg, marked γ mem survivor⟩

end
end Research6970.Height2313.Lower6960.Prefix6969Rescue
