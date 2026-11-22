import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import ProximityPrize.SubmissionLower.Fast014
set_option Elab.async false
set_option autoImplicit true
section
namespace Sol1.C42
set_option maxRecDepth 10000
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ProximityPrize.Benchmark
universe u
variable {E : Type u} [Field E]
abbrev NativeK := IRSProfile.Field
local instance : DecidableEq NativeK := Classical.decEq NativeK
end
end Sol1.C42
end
section
namespace Sol1.C42
noncomputable section
set_option maxRecDepth 10000
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
local instance : DecidableEq NativeK := Classical.decEq NativeK
end
end Sol1.C42
end
section
namespace Astra7
universe u
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
theorem generic_source_support {R E κ : Type*} [CommSemiring R] [CommSemiring E] [Fintype κ]
    {d : ℕ} (psi : R →+* E) (cols : κ → SourceColumn d) (v : κ → R)
    (u : JetVariable d →₀ ℕ)
    (hu : u ∈ (MvPolynomial.map psi (SourceColumn.interpolant cols v)).support) :
    ∃ j : κ, u=(cols j).exponent := by
  classical
  have hs := MvPolynomial.support_map_subset psi (SourceColumn.interpolant cols v) hu
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
  exact ⟨j,by simpa [SourceColumn.interpolant] using MvPolynomial.support_monomial_subset hj⟩
end
end Astra7
end
section
namespace Astra7
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42 Sol1.C57
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F]
local instance : DecidableEq Sol1.C42.NativeK := Classical.decEq _
end
end Astra7
end
section
namespace Sol1.Reciprocal.Native
set_option maxRecDepth 10000
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
abbrev Base := KoalaBear.Field
abbrev K := IRSProfile.Field
abbrev Index := IRSProfile.Index
local instance : DecidableEq Base := Classical.decEq Base
local instance : DecidableEq K := Classical.decEq K
def nodes : Index ↪ Base where
  toFun i := IRSProfile.baseNttDomain.node i
  inj' := by
    intro i j h
    apply IRSProfile.domain.injective
    change CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i) =
      CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node j)
    exact congrArg CompPoly.Extension.Ext.ofBase h
def extendWord (w : Index → Base) : Base → Base :=
  Function.extend nodes w (fun _ ↦ 0)
@[simp] theorem extendWord_nodes (w : Index → Base) (i : Index) :
    extendWord w (nodes i) = w i := nodes.injective.extend_apply _ _ _
end
end Sol1.Reciprocal.Native
end
section
namespace Sol1.OneCount
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open Sol1.Reciprocal Sol1.FiniteRowProjection
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev scalarCode : ModuleCode I K K := ReedSolomon.code IRSProfile.domain 131072
local instance : DecidableEq K := Classical.decEq K
def extendScalarWord (w : I → K) : K → K :=
  Function.extend IRSProfile.domain w (fun _ ↦ 0)
@[simp] theorem extendScalarWord_domain (w : I → K) (i : I) :
    extendScalarWord w (IRSProfile.domain i) = w i :=
  IRSProfile.domain.injective.extend_apply _ _ _
end
end Sol1.OneCount
end
section
namespace Sol1.OneCount
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open Sol1.FiniteRowProjection
abbrev A16 := Fin 2 → Fin IRSProfile.interleaving → K
abbrev R16 := Fin 2 × Fin 8
def squaredCode : ModuleCode I K A16 := IRSProfile.code ^⋈ (Fin 2)
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq A16 := Classical.decEq A16
def flatten (f : I → A16) : I → R16 → K := fun i r ↦ f i r.1 r.2
theorem flatten_injective : Function.Injective flatten := by
  intro f g h
  funext i j r
  exact congrFun (congrFun h i) (j,r)
theorem flatten_agreement_le (f w : I → A16) :
    agreementCard f w ≤ agreementCard (flatten f) (flatten w) := by
  apply agreementCard_mono f w (flatten f) (flatten w)
  intro i he
  funext r
  exact congrFun (congrFun he r.1) r.2
theorem flatten_rows_mem (f : I → A16) (hf : f ∈ squaredCode) :
    ∀ r : R16, (fun i ↦ flatten f i r) ∈ scalarCode := by
  change ∀ j : Fin 2, ∀ r : Fin 8, (fun i ↦ f i j r) ∈ scalarCode at hf
  intro r
  exact hf r.1 r.2
end
end Sol1.OneCount
end
section
namespace Astra7.NativeBudget
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark Sol1.OneCount Sol1.FiniteRowProjection Sol1.C42
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq A16 := Classical.decEq A16
end
end Astra7.NativeBudget
end
section
namespace Astra7.NativeBudget
noncomputable section
open Code CoreDefinitions ToyProblem
open ProximityPrize.Benchmark Sol1.OneCount Sol1.C42
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance : DecidableEq K := Classical.decEq K
end
end Astra7.NativeBudget
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset CoreDefinitions Code
open ProximityPrize.Benchmark
local instance decidableScalarProtocol (P : Prop) : Decidable P := Classical.propDecidable P
end
end FrobeniusLocator.Native
end
