import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import ProximityPrize.SubmissionLower.Fast035
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_3_2
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators Classical
def c1 : Prop :=
  ∀ P Q : Jet, P ≠ 0 → Q ≠ 0 →
    RowCaps P (cheapShape 0) → RowCaps Q (layeredShape 0) →
    NoMovingCommon P Q → Nonempty (PreparedPair P Q)
end
end K1_14_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
namespace K1_14_3_2_7
noncomputable section
open K1_14 K1_14_3
open scoped nonZeroDivisors
variable {B A : Type} [CommRing B] [CommRing A]
abbrev denominators (f : B →+* A) : Submonoid A :=
  (nonZeroDivisors B).map f.toMonoidHom
abbrev Localized (f : B →+* A) := Localization (M := A) (denominators f)
private def localBase (f : B →+* A) : FractionRing B →+* Localized f :=
  IsLocalization.lift (M := nonZeroDivisors B)
    (g := (algebraMap A (Localized f)).comp f)
    (fun b => IsLocalization.map_units (M := denominators f) (Localized f)
      ⟨f b, b, b.property, rfl⟩)
instance (f : B →+* A) : Algebra (FractionRing B) (Localized f) :=
  (localBase f).toAlgebra
@[simp] theorem local_base (f : B →+* A) (b : B) :
    algebraMap (FractionRing B) (Localized f) (algebraMap B (FractionRing B) b) =
      algebraMap A (Localized f) (f b) :=
  IsLocalization.lift_eq _ _
abbrev localizedPrime (f : B →+* A) (I : Ideal A) : Ideal (Localized f) :=
  I.map (algebraMap A (Localized f))
def GenericFibre (f : B →+* A) (I : Ideal A) := Localized f ⧸ localizedPrime f I
instance (f : B →+* A) (I : Ideal A) : CommRing (GenericFibre f I) :=
  inferInstanceAs (CommRing (Localized f ⧸ localizedPrime f I))
instance (f : B →+* A) (I : Ideal A) : Algebra (FractionRing B) (GenericFibre f I) :=
  inferInstanceAs (Algebra (FractionRing B) (Localized f ⧸ localizedPrime f I))
def toFibre (f : B →+* A) (I : Ideal A) : A →+* GenericFibre f I :=
  (Ideal.Quotient.mk _).comp (algebraMap A (Localized f))
@[simp] theorem fibre_base (f : B →+* A) (I : Ideal A) (b : B) :
    algebraMap (FractionRing B) (GenericFibre f I) (algebraMap B (FractionRing B) b) =
      toFibre f I (f b) := by
  change Ideal.Quotient.mk _ (algebraMap (FractionRing B) (Localized f)
    (algebraMap B (FractionRing B) b)) = _
  rw [local_base]
  rfl
variable [IsDomain B]
end
end K1_14_3_2_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 4000000
namespace K1_14_3_2_7
noncomputable section
open K1_14 K1_14_3 Polynomial
open scoped TensorProduct nonZeroDivisors
abbrev Four (R : Type) [CommRing R] := Polynomial (Polynomial (MvPolynomial (Fin 2) R))
def scalar {R : Type} [CommRing R] : R →+* Four R := C.comp (C.comp MvPolynomial.C)
def seedVar {R : Type} [CommRing R] (i : Fin 2) : Four R := C (C (MvPolynomial.X i))
def yVar {R : Type} [CommRing R] : Four R :=
  Polynomial.C (R := (Polynomial (MvPolynomial (Fin 2) R))) (Polynomial.X (R := MvPolynomial (Fin 2) R))
def vVar {R : Type} [CommRing R] : Four R :=
  Polynomial.X (R := (Polynomial (MvPolynomial (Fin 2) R)))
def evaluate {R T : Type} [CommRing R] [CommRing T] (a : R →+* T)
    (t : Fin 2 → T) (y v : T) : Four R →+* T :=
  eval₂RingHom (eval₂RingHom (MvPolynomial.eval₂Hom a t) y) v
@[simp] theorem evaluate_scalar {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) (c : R) :
    evaluate a t y v (scalar c) = a c := by simp [evaluate, scalar]
@[simp] theorem evaluate_seed {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) (i : Fin 2) :
    evaluate a t y v (seedVar i) = t i := by simp [evaluate, seedVar]
@[simp] theorem evaluate_y {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) :
    evaluate a t y v yVar = y := by simp [evaluate, yVar]
@[simp] theorem evaluate_v {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) :
    evaluate a t y v vVar = v := by simp [evaluate, vVar]
def extendScalars {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    Four R →+* Four G :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.map k))
@[simp] theorem extend_scalar {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) (c : R) :
    extendScalars k (scalar c) = scalar (k c) := by simp [extendScalars, scalar]
@[simp] theorem extend_seed {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) (i : Fin 2) :
    extendScalars k (seedVar i) = seedVar i := by simp [extendScalars, seedVar]
@[simp] theorem extend_y {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    extendScalars k yVar = yVar := by simp [extendScalars, yVar]
@[simp] theorem extend_v {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    extendScalars k vVar = vVar := by simp [extendScalars, vVar]
structure Projection (R G B : Type) [CommRing R] [Field G] [CommRing B] where
  intoJet : B →+* Four R
  intoSection : B →+* G
  injective : Function.Injective intoSection
  baseScalar : R →+* B
  baseVar : Fin 2 → B
  ext : ∀ {T : Type} [CommRing T] {f g : B →+* T},
    (∀ a, f (baseScalar a) = g (baseScalar a)) →
    (∀ i, f (baseVar i) = g (baseVar i)) → f = g
  scalar_jet : ∀ a, intoJet (baseScalar a) = scalar a
  coeffMap : R →+* G
  scalar_section : ∀ a, intoSection (baseScalar a) = coeffMap a
  cutSet : Set (Four G)
  cuts : cutSet = Set.range
    (fun i => extendScalars coeffMap (intoJet (baseVar i)) - scalar (intoSection (baseVar i)))
variable {R G B : Type} [CommRing R] [Field G] [CommRing B]
end
end K1_14_3_2_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2_5
noncomputable section
open K1_14 K1_14_3 Polynomial
def sectionParameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def seedLine : SectionSeeds :=
  MvPolynomial.X 0 + MvPolynomial.C (sectionParameter 0) * MvPolynomial.X 1 -
    MvPolynomial.C (sectionParameter 2)
end
end K1_14_3_2_5
end
section
set_option autoImplicit false
namespace K1_14_3_2_3
noncomputable section
open K1 K1_14 K1_14_3
abbrev Plane := MvPolynomial (Fin 2) SectionField
def parameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def seedCoordinates : Slice → Fin 2 → Plane
  | .seed => ![MvPolynomial.C (parameter 2), MvPolynomial.C (parameter 3)]
  | .ordinate | .mixed =>
    ![MvPolynomial.C (parameter 2) - MvPolynomial.C (parameter 0) * MvPolynomial.X 0,
      MvPolynomial.X 0]
  | .jets => MvPolynomial.X
def ordinateCoordinate : Slice → Plane
  | .seed => MvPolynomial.X 0
  | .ordinate => MvPolynomial.C (parameter 3)
  | .mixed => MvPolynomial.C (parameter 3) - MvPolynomial.C (parameter 1) * MvPolynomial.X 1
  | .jets => MvPolynomial.C (parameter 2)
def derivativeCoordinate : Slice → Plane
  | .jets => MvPolynomial.C (parameter 3)
  | _ => MvPolynomial.X 1
def sliceMap (s : Slice) : SectionJet →ₐ[SectionField] Plane :=
  Polynomial.aevalTower
    (Polynomial.aevalTower (MvPolynomial.aeval (seedCoordinates s)) (ordinateCoordinate s))
    (derivativeCoordinate s)
end
end K1_14_3_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000
namespace K1_14_3_2_3
noncomputable section
open K1_14_3 Polynomial
private abbrev t (i : Fin 2) : SectionJet := C (C (MvPolynomial.X i))
private abbrev y : SectionJet := C (Polynomial.X (R := SectionSeeds))
private abbrev v : SectionJet := Polynomial.X (R := Polynomial SectionSeeds)
private def free : Slice → Fin 2 → SectionJet
  | .seed => ![y, v]
  | .ordinate | .mixed => ![t 1, v]
  | .jets => ![t 0, t 1]
private abbrev CutQuotient (s : Slice) := SectionJet ⧸ Ideal.span (sectionEquations s)
private def cutMk (s : Slice) : SectionJet →ₐ[SectionField] CutQuotient s :=
  Ideal.Quotient.mkₐ _ _
private def restore (s : Slice) : Plane →ₐ[SectionField] CutQuotient s :=
  MvPolynomial.aeval (cutMk s ∘ free s)
@[simp] private theorem slice_t (s : Slice) (i : Fin 2) :
    sliceMap s (t i) = seedCoordinates s i := by
  simp [sliceMap]
@[simp] private theorem slice_y (s : Slice) :
    sliceMap s y = ordinateCoordinate s := by simp [sliceMap]
@[simp] private theorem slice_v (s : Slice) :
    sliceMap s v = derivativeCoordinate s := by simp [sliceMap]
@[simp] private theorem slice_scalar (s : Slice) (i : Fin 4) :
    sliceMap s (sectionScalar i) = MvPolynomial.C (parameter i) :=
  (sliceMap s).commutes (parameter i)
@[simp] private theorem restore_const (s : Slice) (i : Fin 4) :
    restore s (MvPolynomial.C (parameter i)) = cutMk s (sectionScalar i) :=
  (restore s).commutes (parameter i)
@[simp] private theorem restore_X (s : Slice) (i : Fin 2) :
    restore s (MvPolynomial.X i) = cutMk s (free s i) := by simp [restore]
end
end K1_14_3_2_3
end
