import ProximityPrize.SubmissionLower.BCHKSCoreTransformedUniversalTag6400
import ProximityPrize.SubmissionLower.BCHKSFullCoreOwnerBridge6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSFullCoreTransformedTagBridge6400

open Polynomial Polynomial.Bivariate
open BCHKSFullCoreLineArrangement6400
open BCHKSFullCoreOwnerBridge6400
open BCHKSCoreTransformedUniversalTag6400
open BCHKSTransformedUniversalTag6400

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
Concrete adapter from a full-order core quotient family to the normalized
factor-local transformed-tag package.  The ownership relation is defined to
be exactly: membership in the owner set together with the original
simple-root condition at the factor-specific selected center.  Thus no
global simple-slope hypothesis is hidden in this bridge.
-/

/-- A full core of codimension `s` at the benchmark root cap manufactures a
complete transformed-tag input.  The only center-selection cost is the
primitive obstruction degree plus the actual core-locator degree. -/
theorem exists_coreTransformedTagInput_of_fullCore
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (R : F[X][X][Y])
    (E S : Finset F) (P : F → F[X]) (U0 U1 : F → F)
    (s : Nat)
    (w : EffectivePrimitiveObstruction F R)
    (hcard : E.card + s = 131071)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ 131071)
    (hcoreMatch : ∀ z ∈ S, ∀ x ∈ E,
      Polynomial.eval x (P z) = U0 x + z * U1 x)
    (hroot : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcenterDegree :
      w.obstruction.natDegree + E.card < Fintype.card F) :
    ∃ D : CoreTransformedTagInput F,
      D.source = R ∧ D.originalRoot = P ∧
      D.rootDegreeCap = s ∧
      (∀ x z, D.owns x z ↔
        z ∈ S ∧ FiniteHensel.IsSimpleRootAt
          (triSpecializeZ R z) x ((P z).eval x)) := by
  classical
  obtain ⟨B0, B1, Q, hB0, hB1, _hB0eval, _hB1eval,
      hQdegree, hshape⟩ :=
    exists_bounded_coreQuotient_family E S P U0 U1 131071 s
      hcard hPdegree hcoreMatch
  let owns : F → F → Prop := fun x z =>
    z ∈ S ∧ FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R z) x ((P z).eval x)
  have hlocator0 : coreLocator E ≠ 0 :=
    (coreLocator_monic E).ne_zero
  have hcenterDegree' :
      w.obstruction.natDegree + (coreLocator E).natDegree <
        Fintype.card F := by
    simpa using hcenterDegree
  let D : CoreTransformedTagInput F := {
    source := R
    originalRoot := P
    quotientRoot := Q
    base0 := B0
    base1 := B1
    locator := coreLocator E
    rootDegreeCap := s
    owns := owns
    primitiveObstruction := w
    locator_ne_zero := hlocator0
    centerDegree_lt_card := hcenterDegree'
    quotient_degree_le := by
      intro x z hz
      exact hQdegree z hz.1
    quotient_shape := by
      intro x z hz
      exact hshape z hz.1
    original_exact_root := by
      intro x z hz
      exact hroot z hz.1
    original_simple_root := by
      intro x z hz
      exact hz.2
    base0_degree_le := hB0
    base1_degree_le := hB1
    locator_degree_add_cap := by
      simpa using hcard.le
  }
  refine ⟨D, rfl, rfl, rfl, ?_⟩
  intro x z
  rfl

/-- Selected-center form of the preceding bridge.  The resulting tag has
quotient roots of degree at most `s`, while keeping the source factor's
actual outer degree and both support caps. -/
theorem exists_transformedUniversalTag_of_fullCore
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (R : F[X][X][Y])
    (E S : Finset F) (P : F → F[X]) (U0 U1 : F → F)
    (s : Nat)
    (w : EffectivePrimitiveObstruction F R)
    (hcard : E.card + s = 131071)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ 131071)
    (hcoreMatch : ∀ z ∈ S, ∀ x ∈ E,
      Polynomial.eval x (P z) = U0 x + z * U1 x)
    (hroot : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcenterDegree :
      w.obstruction.natDegree + E.card < Fintype.card F) :
    ∃ D : CoreTransformedTagInput F,
      D.source = R ∧ D.originalRoot = P ∧
      D.rootDegreeCap = s ∧
      D.toTag.source = R ∧ D.toTag.rootDegreeCap = s ∧
      D.locator.eval D.center ≠ 0 ∧
      (triSpecializeX D.source D.center).IsPrimitive ∧
      (∀ z, D.toTag.owns z ↔
        z ∈ S ∧ FiniteHensel.IsSimpleRootAt
          (triSpecializeZ R z) D.center ((P z).eval D.center)) := by
  obtain ⟨D, hDR, hDP, hDs, howns⟩ :=
    exists_coreTransformedTagInput_of_fullCore
      R E S P U0 U1 s w hcard hPdegree hcoreMatch hroot hcenterDegree
  refine ⟨D, hDR, hDP, hDs, ?_, ?_, D.center_locator_ne_zero,
    D.center_primitive, ?_⟩
  · simpa using hDR
  · simpa using hDs
  · intro z
    rw [CoreTransformedTagInput.toTag_owns]
    simpa [hDR, hDP] using howns D.center z

end BCHKSFullCoreTransformedTagBridge6400
end ProximityPrize.SubmissionLower
