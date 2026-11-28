import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.NNRat.Floor
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import ProximityPrize.SubmissionLower.DdAD
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Finset→cy,Finset.range→lI,IsCoprime→aU,MvPolynomial.eval₂→mD,MvPolynomial.restrictSupport→lV,MvPolynomial.restrictSupport_finite→lJ,Polynomial.Bivariate.swap→nq,Polynomial.C→c9,Polynomial.X→lz
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace DdK1
noncomputable section
open Polynomial Matrix CoreDefinitions Code
open gR
open ProximityPrize.Benchmark
open scoped BigOperators
abbrev K:=Native.K
abbrev I:=Native.I
end
end DdK1
end
section
namespace aR
noncomputable section
open Polynomial DdK1
open scoped BigOperators
abbrev ao:=AlgebraicClosure K
abbrev embed:=algebraMap K ao
abbrev extend (S:(Polynomial K)) :=S.map embed
abbrev af (n:ℕ) :=MvPolynomial (Fin n) (Polynomial ao)
def jet (S:(Polynomial ao)) {n:ℕ} (i:Fin n) :(Polynomial ao) :=hasseDeriv i.val S
def cK {n:ℕ} (P:af n) (S:(Polynomial ao)) :(Polynomial ao) :=
 MvPolynomial.eval (jet S) P
def Z8 {n:ℕ} (P:af n) (S:(Polynomial ao)) :af n :=
 mD MvPolynomial.C (fun i=>MvPolynomial.X i+MvPolynomial.C (jet S i)) P
def wU {n:ℕ} (P:af n) (S:(Polynomial ao)) (d:ℕ) :Prop :=
 ∀ m∈(Z8 P S).support,d≤ m.sum (fun _ a=>a)
end
end aR
end
section
namespace aR
noncomputable section
open Polynomial DdK1
open scoped BigOperators
end
end aR
end
section
namespace xE
noncomputable section
open aR PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
end
end xE
end
section
namespace xE
noncomputable section
open DdK1 aR Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

end
end xE
end
