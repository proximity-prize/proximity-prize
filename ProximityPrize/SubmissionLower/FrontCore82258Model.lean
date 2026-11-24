import ProximityPrize.SubmissionLower.HighCore82258Data
import ProximityPrize.SubmissionLower.UpperBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option backward.isDefEq.respectTransparency false

namespace FrontCore82258

noncomputable section

open Polynomial
open P1 (K I node twist p)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum seedEmbedding)
open K1_14_1 (PoleData MarkResidues nodeL)
open P1_7 (Reduced singularDegree singularFee)
open scoped BigOperators Polynomial

abbrev AnchorModel (u : P1.Words) (D : Finset I) := P1.ModelAt HighCore82258.heightCap u D
abbrev AnchoredFamily {u D} (M : AnchorModel u D) (Γ : Finset K) :=
  P1.FamilyAt HighCore82258.agreement M Γ

def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ

end
end FrontCore82258
