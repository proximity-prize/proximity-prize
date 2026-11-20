import Mathlib.RingTheory.GradedAlgebra.Radical
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast018
set_option Elab.async false

section PackSource_K1_13_6_1Defs
set_option autoImplicit true
namespace K1_13_6_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators

abbrev anchorBox (f : Row 4) : Shape := (shape f).chamber

def HasMark (Γ : Finset K) (s : K → K[X]) (surface : Ideal GeoJets) : Prop :=
  ∃ γ ∈ Γ, surface ≤ markIdeal (extend (s γ))

/-- Unscaled tangent iterates. On a regular chart the operator is the
tangent derivative times a unit, so its first nonzero residue is unchanged. -/
def tangentCut (g P : Row 4) (a : ℕ) : Row 4 :=
  (flowNumerator g)^[a] P

/-- The extra charge belongs to the proper anchor/derivative cycle
with this chart order, at this same surface prime. -/
def DerivativeWeight (f : Row 4) (surface : Ideal GeoJets) (r w : ℕ) : Prop :=
  let g := (separant^[r]) f
  ¬ f ∣ g ∧ InBox (shape g) (anchorBox f) ∧ 0 < w ∧
    ∃ hZ : (intersectionIdeal f g).IsMinimalPrime surface,
      cycleLength (intersectionIdeal f g) surface hZ.isPrime = (w : ℕ∞)

def SurfaceCut (f Q : Row 4) (surface : Ideal GeoJets) (P : Row 4) : Prop :=
  ∃ (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) (v w : ℕ),
    0 < v ∧ cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
    (w = 0 ∨ ∃ r, 0 < r ∧ r < (shape f).t ∧ DerivativeWeight f surface r w) ∧
    toGeneric P ∉ surface ∧
    InBox (shape P) (cutterBox.plus ((anchorBox f).scale (4*v + 2*w)))

structure CurveOnFactor (f : Row 4) (C : Ideal GeoJets) : Prop where
  prime : C.IsPrime
  dim : ringKrullDim (GeoJets ⧸ C) = 1
  contains : toGeneric f ∈ C

abbrev SectionIndex (a : Shape) := Fin 4 → Fin (a.b + 1)
abbrev SectionField (a : Shape) := FractionRing (MvPolynomial (SectionIndex a) GeoField)
abbrev SectionJets (a : Shape) := MvPolynomial (Fin 4) (SectionField a)

def boxMonomials (a : Shape) : Finset (SectionIndex a) :=
  Finset.univ.filter fun m =>
    (∑ i, (m i).val) ≤ a.b ∧
      (∑ i, i.val * (m i).val) ≤ a.j ∧ (m 3).val ≤ a.t

def genericSection (a : Shape) : SectionJets a :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial (SectionIndex a) GeoField)
      (SectionField a) (MvPolynomial.X m)) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val

/-- Length of the generic affine hyperplane section in the box's full
monomial system. The argument is scaled by six to use lattice polytopes. -/
def sectionDegree (C : Ideal GeoJets) (a : Shape) : ℕ :=
  let J := C.map (MvPolynomial.map (algebraMap GeoField (SectionField a))) ⊔
    Ideal.span {genericSection a}
  Module.finrank (SectionField a) (SectionJets a ⧸ J)

end
end K1_13_6_1
end PackSource_K1_13_6_1Defs
