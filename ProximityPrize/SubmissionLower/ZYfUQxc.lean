import ProximityPrize.SubmissionLower.Zf9KUOa
set_option Elab.async false
set_option autoImplicit true
namespace qe6nVeb
noncomputable section
open Polynomial
open P5 (K)


def c4 :Prop :=
  ∀ (z :K→Fin 2→cu.L) (T:Finset K),Set.InjOn z (T:Set K) →
    ∀ B:ℕ,0<B →
      (∀ q:SeedPlane,Irreducible q→(immersedMarks q z T).card≤B*q.totalDegree) →
      3*T.card≤10*B^2
private theorem injective_seeds (J:Input) :Function.Injective (dcQ J) := by
  intro γ η h
  have hz :=congrArg (fun w:Fin 2→cu.L=>w 0) h
  change algebraMap K cu.L (J.model.label γ) =
    algebraMap K cu.L (J.model.label η) at hz
  exact sub_left_inj.mp ((algebraMap K cu.L).injective hz)
end
end qe6nVeb
