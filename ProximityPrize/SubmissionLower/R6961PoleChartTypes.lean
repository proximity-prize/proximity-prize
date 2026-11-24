import ProximityPrize.SubmissionLower.R6960PrefixRows

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6961.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt liftPoly)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom)
open K1_14_3 (Surface)
open Lower6960.DifferentialContact (Native)

abbrev Model (u : P1.Words) (deleted : Finset I) := P1.ModelAt 33579 u deleted
abbrev Family {u deleted} (M : Model u deleted) (Γ : Finset K) := P1.FamilyAt 179818 M Γ

def word {u deleted} (M : Model u deleted) : I → L := fun i => algebraMap K L (M.word i)

def OnMark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (A : Ideal Ambient) (γ : K) : Prop := OnJet A (M.label γ) (F.scalar γ)

theorem label_injective {u deleted} (M : Model u deleted) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h

def OnSurface {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (q : Surface) (γ : K) : Prop :=
  ∀ P ∈ q.asIdeal, jetAt P (M.label γ) (F.scalar γ) = 0

/-- The selected row and every test used by its stage vanish at each actual model mark. -/
theorem contact_at_mark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {s : Shape} {W r : ℕ} {P : Jet} (inside : P ∈ evaluated Crt (word M) s W)
    (width : W + 2 * M.overhead.toNat * r < s.m * 179818)
    (γ : K) (hγ : γ ∈ Γ) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (r + 1) P := by
  let B := F.mark γ hγ
  have degree : (liftPoly (F.scalar γ)).natDegree ≤ 131071 + M.overhead.toNat := by
    rw [liftPoly, Polynomial.natDegree_map]
    rcases B.scalar_degree with hzero | hd
    · simp [hzero]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hd
      omega
  refine Lower6960.PrefixRows.contact_of_crt Crt (word M) s P inside width noPole
    (M.label γ) (F.scalar γ) (residues γ hγ) degree B.bad.support B.bad.agreement ?_
  intro i hit
  rw [word, liftPoly, nodeL, Polynomial.eval_map, Polynomial.eval₂_hom]
  exact congrArg (algebraMap K L) (B.scalar_hits i hit)

theorem zero_of_contact {z : K} {S : (Polynomial K)} {P : Jet} {r : ℕ}
    (contact : Native (RingHom.ker (jetMarkHom z S)) (r + 1) P) : jetAt P z S = 0 := by
  have test := contact [] (by simp)
  change toJet P ∈ RingHom.ker (jetMarkHom z S) at test
  rwa [RingHom.mem_ker, K1_14_2.eval_toJet] at test

end Lower6961.RescueGeometry
