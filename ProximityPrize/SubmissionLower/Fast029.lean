import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Regular.Flat
import ProximityPrize.SubmissionLower.Fast017
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

set_option Elab.async false

-- merged module Pack_K1_13_6_1_4Geometry
section Merged_Pack_K1_13_6_1_4Geometry
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_6
noncomputable section
open Polynomial K1 K1_13
open scoped BigOperators
abbrev GenericField := FractionRing (Polynomial Geom)
abbrev GeoField := AlgebraicClosure GenericField
abbrev GeoJets := MvPolynomial (Fin 4) GeoField
def genericCoeffs : (Polynomial Geom) →+* GeoField :=
  (algebraMap GenericField GeoField).comp (algebraMap (Polynomial Geom) GenericField)
def toGeneric (P : Row 4) : GeoJets := MvPolynomial.map genericCoeffs P
def evalGeneric (S : (Polynomial Geom)) : GeoJets →+* GeoField :=
  MvPolynomial.eval (fun i => genericCoeffs (jet S i))
def markIdeal (S : (Polynomial Geom)) : Ideal GeoJets := RingHom.ker (evalGeneric S)
def intersectionIdeal (f Q : Row 4) : Ideal GeoJets :=
  Ideal.span {toGeneric f, toGeneric Q}
def divisorIdeal (surface : Ideal GeoJets) (E : Row 4) : Ideal GeoJets :=
  surface ⊔ Ideal.span {toGeneric E}
def cycleLength (J surface : Ideal GeoJets) (hp : surface.IsPrime) : ℕ∞ :=
  letI := hp
  let L := Localization.AtPrime surface
  Module.length L (L ⧸ J.map (algebraMap GeoJets L))
def separant (g : Row 4) : Row 4 := MvPolynomial.pderiv 3 g
def coefficientDerivative (P : Row 4) : Row 4 :=
  ∑ m ∈ P.support, MvPolynomial.monomial m (derivative (P.coeff m))
def partialFlow (P : Row 4) : Row 4 :=
  coefficientDerivative P +
  ∑ i : Fin 3, MvPolynomial.C (C ((i.val + 1 : ℕ) : Geom)) *
    MvPolynomial.X i.succ * MvPolynomial.pderiv i.castSucc P
def flowNumerator (g P : Row 4) : Row 4 :=
  separant g * partialFlow P - partialFlow g * separant P
def clearedStep (g : Row 4) (a : ℕ) (P : Row 4) : Row 4 :=
  separant g * flowNumerator g P - (a : Row 4) * flowNumerator g (separant g) * P
def jetNumerator (g : Row 4) : ℕ → Row 4
  | 0 => MvPolynomial.X 0
  | n+1 => clearedStep g (2*n) (jetNumerator g n)
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength+1)
def Invariant (g : Row 4) (surface : Ideal GeoJets) : Prop :=
  ∀ P : Row 4, toGeneric P ∈ surface → toGeneric (flowNumerator g P) ∈ surface
def CanonicalChart (f : Row 4) (surface : Ideal GeoJets) (r : ℕ) : Prop :=
  r < (shape f).t ∧ (∀ j ≤ r, toGeneric ((separant^[j]) f) ∈ surface) ∧
    toGeneric (separant ((separant^[r]) f)) ∉ surface
structure HighChart (f Q : Row 4) (l : ℕ) (S : (Polynomial Geom))
    (surface : Ideal GeoJets) (r : ℕ) : Prop where
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  point : surface ≤ markIdeal S
  chart : CanonicalChart f surface r
  regular : atJet (separant ((separant^[r]) f)) S ≠ 0
  invariant : Invariant ((separant^[r]) f) surface
def HighMark (f Q : Row 4) (l : ℕ) (S : (Polynomial Geom)) : Prop :=
  ∃ surface r, HighChart f Q l S surface r
def CurveSections (Γ : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    (Γ.filter fun γ => (s γ).eval x = a).card ≤ d
structure Pieces (Γ : Finset K) where
  n : ℕ
  piece : Fin n → Finset K
  subset : ∀ i, piece i ⊆ Γ
  degree : Fin n → ℕ
def Pieces.union {Γ : Finset K} (C : Pieces Γ) : Finset K := by
  classical exact Finset.univ.biUnion C.piece
def Pieces.total {Γ : Finset K} (C : Pieces Γ) : ℕ := ∑ i, C.degree i
def Pieces.curves {Γ : Finset K} (C : Pieces Γ) (s : K → (Polynomial K)) : Prop :=
  ∀ i, CurveSections (C.piece i) s (C.degree i)
def SurfaceSections (Γ : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    let H := Γ.filter fun γ => (s γ).eval x = a
    ∃ C : Pieces H, H ⊆ C.union ∧ C.curves s ∧ (∀ i, 0 < C.degree i) ∧ C.total ≤ d
def Pieces.surfaces {Γ : Finset K} (C : Pieces Γ) (s : K → (Polynomial K)) : Prop :=
  ∀ i, SurfaceSections (C.piece i) s (C.degree i)
end
end K1_13_6
end
section
namespace K1_13_6
noncomputable section
open Polynomial K1_13
open scoped BigOperators
@[simp] private theorem coeff_coefficientDerivative (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coefficientDerivative_C (p : (Polynomial Geom)) :
    coefficientDerivative (MvPolynomial.C p) = MvPolynomial.C (derivative p) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coefficientDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P+Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp
private theorem coefficientDerivative_mul_X (P : Row 4) (j : Fin 4) :
    coefficientDerivative (P * MvPolynomial.X j) = coefficientDerivative P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coefficientDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp
private theorem eval_chain (P : Row 4) (a : Fin 4 → (Polynomial Geom)) :
    derivative (MvPolynomial.eval a P) = MvPolynomial.eval a (coefficientDerivative P) +
      ∑ i, derivative (a i) * MvPolynomial.eval a (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [coefficientDerivative_C]
  | add P Q hP hQ =>
    simp only [map_add, coefficientDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    rw [map_mul, MvPolynomial.eval_X, derivative_mul, ih, coefficientDerivative_mul_X,
      map_mul, MvPolynomial.eval_X]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X,
      mul_add, Finset.sum_add_distrib]
    have left : (∑ i, derivative (a i) *
          (MvPolynomial.eval a (MvPolynomial.pderiv i P) * a j)) =
        (∑ i, derivative (a i) * MvPolynomial.eval a (MvPolynomial.pderiv i P)) * a j := by
      simp only [Finset.sum_mul, mul_assoc]
    have right : (∑ i, derivative (a i) *
          (MvPolynomial.eval a P * MvPolynomial.eval a (MvPolynomial.pderiv i (MvPolynomial.X j)))) =
        derivative (a j) * MvPolynomial.eval a P := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]
    rw [left, right]
    ring
private theorem derivative_hasse (S : (Polynomial Geom)) (k : ℕ) :
    derivative (hasseDeriv k S) = C ((k+1 : ℕ) : Geom) * hasseDeriv (k+1) S := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := Geom) 1 k) S
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul, C_eq_natCast, Nat.add_comm, add_mul] using h
private theorem eval_partialFlow (P : Row 4) (S : (Polynomial Geom)) :
    derivative (atJet P S) = atJet (partialFlow P) S +
      derivative (jet S (3 : Fin 4)) * atJet (separant P) S := by
  unfold atJet partialFlow separant
  rw [eval_chain, Fin.sum_univ_castSucc, map_add, map_sum]
  rw [← add_assoc]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [jet, derivative_hasse, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Fin.val_castSucc, Fin.val_succ]
theorem eval_flowNumerator (g P : Row 4) (S : (Polynomial Geom)) (hg : atJet g S = 0) :
    atJet (flowNumerator g P) S = atJet (separant g) S * derivative (atJet P S) := by
  have hz : atJet (partialFlow g) S +
      derivative (jet S (3 : Fin 4)) * atJet (separant g) S = 0 := by
    rw [← eval_partialFlow, hg, map_zero]
  unfold flowNumerator
  rw [eval_partialFlow]
  change (MvPolynomial.eval (jet S)) (_ - _) = _
  rw [map_sub, map_mul, map_mul]
  change atJet (separant g) S * atJet (partialFlow P) S -
      atJet (partialFlow g) S * atJet (separant P) S = _
  linear_combination -atJet (separant P) S * hz
private theorem cleared_product_rule (a : ℕ) (U V : (Polynomial Geom)) :
    U * (U * derivative (U^a * V)) - (a : (Polynomial Geom)) * (U * derivative U) * (U^a * V) =
      U^(a+2) * derivative V := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [derivative_mul, derivative_pow, Nat.succ_sub_one,
      pow_add U (a+1) 2, pow_succ' U a]
    simp only [C_eq_natCast]
    push_cast
    ring
theorem eval_jetNumerator (g : Row 4) (S : (Polynomial Geom)) (hg : atJet g S = 0) (n : ℕ) :
    atJet (jetNumerator g n) S =
      atJet (separant g) S ^ (2*n) * ((derivative (R := Geom))^[n]) S := by
  induction n with
  | zero =>
    simp [jetNumerator, atJet, jet]
  | succ n ih =>
    let e := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
    change e (clearedStep g (2*n) (jetNumerator g n)) = _
    unfold clearedStep
    rw [map_sub, map_mul, map_mul, map_mul, map_natCast]
    change atJet (separant g) S * atJet (flowNumerator g (jetNumerator g n)) S -
      (↑(2*n) : (Polynomial Geom)) * atJet (flowNumerator g (separant g)) S *
        atJet (jetNumerator g n) S = _
    rw [eval_flowNumerator _ _ _ hg, eval_flowNumerator _ _ _ hg, ih,
      cleared_product_rule,
      show 2*(n+1) = 2*n+2 by omega, Function.iterate_succ_apply']
end
end K1_13_6
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial K1_13 K1_13_6
abbrev TaylorIndex := Fin taylorLength
abbrev GeoPoint := Fin 4 → GeoField
def Chamber (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j
def GeoFits (g : GeoJets) (p : Shape) : Prop :=
  g.totalDegree ≤ p.b ∧ g.weightedTotalDegree Fin.val ≤ p.j ∧ g.degreeOf 3 ≤ p.t
structure TaylorChart where
  denom : GeoJets
  numerator : TaylorIndex → GeoJets
  initial : ∀ i : Fin 4,
    numerator (i.castLE (by decide : 4 ≤ taylorLength)) = MvPolynomial.X i * denom
def TaylorChart.Fits (C : TaylorChart) (h : Shape) : Prop :=
  GeoFits C.denom h ∧ ∀ i, GeoFits (C.numerator i) h
def TaylorChart.Recovers (C : TaylorChart) (S : (Polynomial Geom)) : Prop :=
  evalGeneric S C.denom ≠ 0 ∧
    ∀ i, evalGeneric S (C.numerator i) =
      evalGeneric S C.denom * genericCoeffs (hasseDeriv i.val S)
abbrev AffineForm := GeoField × (TaylorIndex → GeoField)
def TaylorChart.pullback (C : TaylorChart) (a : AffineForm) : GeoJets :=
  MvPolynomial.C a.1 * C.denom + ∑ i, MvPolynomial.C (a.2 i) * C.numerator i
def Isolated (f g u v : GeoJets) (y : GeoPoint) : Prop :=
  RingHom.ker (MvPolynomial.eval y) ∈ (Ideal.span ({f, g, u, v} : Set GeoJets)).minimalPrimes
def SliceBound (f g : GeoJets) (C : TaylorChart) (d : ℕ) : Prop :=
  ∀ a b : AffineForm, ∀ points : Finset GeoPoint,
    (∀ y ∈ points, Isolated f g (C.pullback a) (C.pullback b) y ∧
      MvPolynomial.eval y C.denom ≠ 0) → points.card ≤ d
end
end K1_13_7_1
end
section
namespace K1_13_6_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
abbrev anchorBox (f : Row 4) : Shape := (shape f).chamber
def HasMark (Γ : Finset K) (s : K → (Polynomial K)) (surface : Ideal GeoJets) : Prop :=
  ∃ γ ∈ Γ, surface ≤ markIdeal (extend (s γ))
def tangentCut (g P : Row 4) (a : ℕ) : Row 4 :=
  (flowNumerator g)^[a] P
def DerivativeWeight (f : Row 4) (surface : Ideal GeoJets) (r w : ℕ) : Prop :=
  let g := (separant^[r]) f
  ¬ f ∣ g ∧ InBox (shape g) (anchorBox f) ∧ 0 < w ∧
    ∃ hZ : (intersectionIdeal f g).IsMinimalPrime surface,
      cycleLength (intersectionIdeal f g) surface hZ.isPrime = (w : ℕ∞)
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
def sectionDegree (C : Ideal GeoJets) (a : Shape) : ℕ :=
  let J := C.map (MvPolynomial.map (algebraMap GeoField (SectionField a))) ⊔
    Ideal.span {genericSection a}
  Module.finrank (SectionField a) (SectionJets a ⧸ J)
end
end K1_13_6_1
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open RingTheory.Sequence
open scoped Pointwise
theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
theorem toGeneric_injective : Function.Injective toGeneric :=
  MvPolynomial.map_injective _ genericCoeffs_injective
private theorem mem_smul_top_iff_dvd {R : Type*} [CommRing R] (f x : R) :
    x ∈ f • (⊤ : Submodule R R) ↔ f ∣ x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, smul_eq_mul]
  exact exists_congr fun _ => eq_comm
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem proper_generic (f g : Row 4) (hf : Irreducible f) (hg : ¬ f ∣ g) :
    IsRelPrime (toGeneric f) (toGeneric g) := by
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hreg : IsWeaklyRegular (Row 4) [f, g] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
    refine ⟨mul_right_injective₀ hp.ne_zero, ?_⟩
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
    intro x hx
    exact (mem_smul_top_iff_dvd f x).mpr
      ((hp.dvd_mul.mp ((mem_smul_top_iff_dvd f (g * x)).mp hx)).resolve_left hg)
  let _ : Algebra (Polynomial Geom) GeoField := genericCoeffs.toAlgebra
  let _ : Module.IsTorsionFree (Polynomial Geom) GeoField :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr genericCoeffs_injective
  have hflat : Module.Flat (Row 4) GeoJets :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv (Polynomial Geom) (Row 4) GeoField GeoJets).symm.toLinearEquiv
  have h := hreg.of_flat (S := GeoJets)
  change IsWeaklyRegular GeoJets [toGeneric f, toGeneric g] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h
  rintro a ⟨b, hb⟩ ⟨c, hc⟩
  have hzero : toGeneric f ≠ 0 := fun hz => hp.ne_zero (toGeneric_injective (hz.trans (map_zero _).symm))
  have hprod : toGeneric g * b = toGeneric f * c := by rw [hc, hb]; ring
  have hdiv : toGeneric f ∣ b := (mem_smul_top_iff_dvd _ _).mp
    (mem_of_isSMulRegular_quotient_of_smul_mem h.2
      ((mem_smul_top_iff_dvd _ _).mpr ⟨c, hprod⟩))
  obtain ⟨q, hq⟩ := hdiv
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (hb ▸ hzero)
  have hu : a * q = 1 := mul_left_cancel₀ hb0 (by
    calc
      b * (a * q) = (a * b) * q := by ring
      _ = b := by rw [← hb, ← hq]
      _ = b * 1 := (mul_one _).symm)
  exact ⟨⟨a, q, hu, by rw [mul_comm, hu]⟩, rfl⟩
end
end K1_13_7_1
end
section
namespace K1_13_6_1_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators
def FullChamber (a : Shape) : Prop := Chamber a ∧ 0 < a.t
abbrev PairSectionIndex (a h : Shape) := SectionIndex a ⊕ SectionIndex h
abbrev PairSectionField (a h : Shape) :=
  FractionRing (MvPolynomial (PairSectionIndex a h) GeoField)
def sectionWith {σ : Type*} (a : Shape) (ι : SectionIndex a → σ) :
    MvPolynomial (Fin 4) (FractionRing (MvPolynomial σ GeoField)) :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial σ GeoField)
      (FractionRing (MvPolynomial σ GeoField)) (MvPolynomial.X (ι m))) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
def surfaceDegree (surface : Ideal GeoJets) (a h : Shape) : ℕ :=
  let F := PairSectionField a h
  let I := surface.map (MvPolynomial.map (algebraMap GeoField F)) ⊔
    Ideal.span {sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h),
      sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)}
  Module.finrank F (MvPolynomial (Fin 4) F ⧸ I)
abbrev pairIdeal (F G : GeoJets) : Ideal GeoJets := Ideal.span {F, G}
end
end K1_13_6_1_4
end
section
namespace K1_13_6_1_4
noncomputable section
open MvPolynomial K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
private theorem krullDim_of_polynomial_normalization {k R : Type*} [Field k]
    [CommRing R] [IsDomain R] {d : ℕ} [Algebra (MvPolynomial (Fin d) k) R]
    [FaithfulSMul (MvPolynomial (Fin d) k) R] [Module.Finite (MvPolynomial (Fin d) k) R] :
    ringKrullDim R = (d : WithBot ℕ∞) := by
  let B := MvPolynomial (Fin d) k
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [← hB]
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B R))
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (show x.asIdeal < y.asIdeal from hxy)
  · obtain ⟨b, hb, hd⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
    obtain ⟨z, hz⟩ :=
      Algebra.IsIntegral.comap_surjective B R (⟨b, hb⟩ : PrimeSpectrum B)
    have hz' : z.asIdeal.under B = b := congrArg PrimeSpectrum.asIdeal hz
    have hle := Ideal.height_under_le_height (R := B) z.asIdeal
    rw [hz'] at hle
    calc
      ringKrullDim B = (d : WithBot ℕ∞) := hB
      _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hd.trans hle)
      _ ≤ ringKrullDim R := Ideal.height_le_ringKrullDim_of_isPrime
private theorem krullDim_of_finite_hom {k R : Type*} [Field k] [CommRing R] [IsDomain R]
    {d : ℕ} (g : MvPolynomial (Fin d) k →+* R) (hg : Function.Injective g)
    (hgfin : g.Finite) : ringKrullDim R = (d : WithBot ℕ∞) := by
  let algebra := g.toAlgebra
  let := algebra
  let faithful : FaithfulSMul (MvPolynomial (Fin d) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let finite : Module.Finite (MvPolynomial (Fin d) k) R := hgfin
  exact @krullDim_of_polynomial_normalization k R _ _ _ d algebra faithful finite
theorem dim_eq_Hilbert {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    ringKrullDim (MvPolynomial σ k ⧸ I) =
      ((affineHilbertPolynomial I).natDegree : WithBot ℕ∞) := by
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hH := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgfin hg
  rw [Nat.card_fin] at hH
  rw [hH]
  exact krullDim_of_finite_hom g.toRingHom hg hgfin
theorem pair_dimension {F G : GeoJets} (hF : F ≠ 0) (hproper : IsRelPrime F G)
    {surface : Ideal GeoJets} (hZ : (pairIdeal F G).IsMinimalPrime surface) :
    ringKrullDim (GeoJets ⧸ surface) = 2 := by
  let := hZ.isPrime
  have hFZ : Ideal.span {F} ≤ surface :=
    le_trans (Ideal.span_mono (by simp)) hZ.le
  obtain ⟨D, hD, hDZ⟩ := Ideal.exists_minimalPrimes_le hFZ
  let := hD.isPrime
  have hD0 : D ≠ ⊥ := fun e =>
    hF (Ideal.mem_bot.mp (e ▸ hD.le (Ideal.subset_span (by simp))))
  have hDh : D.height = 1 :=
    le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ D hD)
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hD0))
  obtain ⟨a, ha, hap⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hD.isPrime hD0
  have heq := Ideal.eq_span_singleton_of_height_eq_one hDh ha hap
  have hGD : G ∉ D := by
    intro hG
    have hFa : a ∣ F := Ideal.mem_span_singleton.mp (heq ▸ hD.le (Ideal.subset_span (by simp)))
    have hGa : a ∣ G := Ideal.mem_span_singleton.mp (heq ▸ hG)
    exact hap.not_isUnit (hproper hFa hGa)
  have hpair : pairIdeal F G ≤ D ⊔ Ideal.span {G} := by
    rw [pairIdeal, Ideal.span_insert]
    exact sup_le (hD.le.trans le_sup_left) le_sup_right
  have hcut : (D ⊔ Ideal.span {G}).IsMinimalPrime surface :=
    ⟨⟨hZ.isPrime, sup_le hDZ ((Ideal.span_mono (by simp)).trans hZ.le)⟩,
      fun J hJ hJZ => hZ.2 ⟨hJ.1, hpair.trans hJ.2⟩ hJZ⟩
  have hDdeg := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
  have hZdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hGD hcut
  rw [Nat.card_fin] at hDdeg
  have hdeg : (affineHilbertPolynomial surface).natDegree = 2 := by omega
  simp [dim_eq_Hilbert surface, hdeg]
theorem curve_of_proper_cut {f P : Row 4} {surface C : Ideal GeoJets}
    (hZ : surface.IsPrime) (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (hf : toGeneric f ∈ surface) (hP : toGeneric P ∉ surface)
    (hC : (divisorIdeal surface P).IsMinimalPrime C) : CurveOnFactor f C := by
  let := hZ
  let := hC.isPrime
  have hZdeg : (affineHilbertPolynomial surface).natDegree = 2 := by
    have hd := (dim_eq_Hilbert surface).symm.trans hdim
    exact_mod_cast hd
  have hCdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hP hC
  have hd : (affineHilbertPolynomial C).natDegree = 1 := by omega
  have hle : surface ≤ C := (show surface ≤ divisorIdeal surface P from le_sup_left).trans hC.le
  exact ⟨hC.isPrime, by simp [dim_eq_Hilbert C, hd], hle hf⟩
end
end K1_13_6_1_4
end

end Merged_Pack_K1_13_6_1_4Geometry

-- merged module Fast023
section Merged_Fast023
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_14
noncomputable section
open K1 Polynomial
open scoped BigOperators
abbrev L := AlgebraicClosure K
abbrev FX := FractionRing (Polynomial L)
abbrev Seeds := MvPolynomial (Fin 2) FX
abbrev Equation := Polynomial Seeds
def liftPoly (g : (Polynomial K)) : (Polynomial L) := g.map (algebraMap K L)
def atX (g : (Polynomial K)) : FX := algebraMap (Polynomial L) FX (liftPoly g)
def seedEmbedding : K →+* FX :=
  (algebraMap (Polynomial L) FX).comp ((Polynomial.C : L →+* (Polynomial L)).comp (algebraMap K L))
def graphEval (z : K) : Seeds →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z) ^ p]
def atMark (f : Equation) (z : K) (S : (Polynomial K)) : FX :=
  f.eval₂ (graphEval z) (atX S)
abbrev Jet := Polynomial Equation
structure Shape where
  m : ℕ
  B : ℕ
  J : ℕ
  U : ℕ
  deriving DecidableEq
structure Band where
  endpoint : ℕ
  yBound : ℕ
  seedBound : ℕ
  multiplicity : ℕ
  jetBound : ℕ
  vBound : ℕ
  subbankSeeds : ℕ
def band (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554,5,144,836,1164,247,19371⟩
  else if w ≤ 8249 then ⟨8249,4,98,358,500,105,6798⟩
  else if w ≤ 23999 then ⟨23999,4,47,358,500,105,4860⟩
  else ⟨32680,4,36,358,500,105,3913⟩
def SeedBound (f : Equation) (b : ℕ) : Prop :=
  ∀ i, (f.coeff i).totalDegree ≤ b
def triangle (U : ℕ) : ℕ := (U + 1) * (U + 2) / 2
def slots (U spent : ℕ) : ℕ :=
  if spent ≤ U then triangle (U - spent) else 0
abbrev Banks := Shape → ℕ → Submodule FX Jet
def shapeSum (s : Shape) (g : ℕ → ℕ → ℕ) : ℕ :=
  ∑ q ∈ Finset.range (s.B+1), ∑ j ∈ Finset.range (min q s.J+1), g q j
def sourceDebit (h : ℕ) (s : Shape) : ℕ :=
  triangle s.U * 262144 * shapeSum s (fun q i => s.m + min q s.J - (q + 2*i)) +
    2*h*(s.U+1)*shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q))
def terminalShape (w : ℤ) : Shape :=
  let b := band w
  ⟨b.multiplicity, b.jetBound, b.vBound, b.subbankSeeds⟩
def scheduled (w : ℤ) : List Shape :=
  let sub := terminalShape w
  if w ≤ 3554 then
    [⟨59,82,18,1899⟩,⟨136,190,40,8441⟩,⟨66,92,21,2076⟩,⟨150,210,44,9356⟩,
     ⟨73,102,23,2261⟩,⟨164,229,48,10272⟩,⟨80,112,25,2455⟩,⟨178,249,52,11191⟩,
     ⟨94,131,30,2824⟩,⟨213,298,62,12959⟩,⟨115,160,36,3401⟩,⟨262,366,77,15611⟩,
     ⟨136,190,43,4204⟩,⟨325,454,96,19187⟩,⟨178,248,56,5332⟩,⟨409,572,121,24615⟩,
     ⟨241,336,78,7235⟩,⟨570,797,169,33523⟩,⟨325,453,104,9976⟩,⟨759,1061,224,46271⟩,
     ⟨836,1164,247,273617⟩, sub]
  else
    [⟨45,63,14,812⟩,⟨84,118,24,2907⟩,⟨57,80,18,1041⟩,⟨114,160,33,3775⟩,
     ⟨81,114,26,1383⟩,⟨144,203,42,5064⟩,⟨123,173,40,2173⟩,⟨231,325,67,8061⟩,
     ⟨358,500,105,66251⟩, sub]
def jetAt (P : Jet) (z : K) (S : (Polynomial K)) : FX :=
  P.eval₂ (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
def translateSeed (i : Fin 2) : Seeds →+* Polynomial Seeds :=
  MvPolynomial.eval₂Hom (C.comp MvPolynomial.C)
    (fun j => C (MvPolynomial.X j : Seeds) + if j = i then Polynomial.X (R := Seeds) else 0)
def seedHasse (i : Fin 2) (r : ℕ) (P : Jet) : Jet :=
  P.sum fun j g => monomial j (g.sum fun k c => monomial k ((translateSeed i c).coeff r))
structure JetSource {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) : Prop where
  nested : ∀ s ∈ scheduled M.overhead, ∀ s' ∈ scheduled M.overhead,
    s.m = s'.m → s.B = s'.B → s.J = s'.J → s.U ≤ s'.U →
    ∀ W W', W ≤ W' → rows s W ≤ rows s' W'
  necessary : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m*180265 → ∀ P ∈ rows s W,
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ j i,
    ((P.coeff j).coeff i) ≠ 0 →
      i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U
  leading : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree)*(131071-M.overhead.toNat) ≤ W + P.natDegree
  shift : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ i r,
    seedHasse i r P ∈ rows s (W + 2*M.overhead.toNat*r)
  floor_bound : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m*180265 →
    (∀ q ≤ s.B, ∀ j ≤ min q s.J, q*(131071-M.overhead.toNat) ≤ W+1+j) →
    triangle s.U * shapeSum s (fun q j => W+1+j - q*(131071-M.overhead.toNat)) ≤
      sourceDebit M.overhead.toNat s + ∑ t ∈ Finset.range (W+1), Module.finrank FX (rows s t)
end
end K1_14
end
section
namespace K1_14
noncomputable section
open K1 Polynomial
open scoped BigOperators
end
end K1_14
end
section
namespace K1_14
noncomputable section
open K1 Polynomial
theorem trim (P : (Polynomial L)) (h : ℕ) (hh : h ≤ P.natDegree) :
    ∃ H : (Polynomial L), H.Monic ∧ H.natDegree = h ∧ H ∣ P := by
  classical
  have hc : 0 < (P.roots.powersetCard h).card := by
    rw [Multiset.card_powersetCard, IsAlgClosed.card_roots_eq_natDegree]
    exact Nat.choose_pos hh
  obtain ⟨s, hs⟩ := Multiset.card_pos_iff_exists_mem.mp hc
  obtain ⟨hle, hsize⟩ := Multiset.mem_powersetCard.mp hs
  exact ⟨_, monic_multisetProd_X_sub_C s, (natDegree_multiset_prod_X_sub_C_eq_card s).trans hsize,
    (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)).trans P.prod_multiset_X_sub_C_dvd⟩
theorem twist_lift (P : (Polynomial K)) :
    liftPoly (P.map twist) = (liftPoly P).map (frobenius L p) := by
  simp only [liftPoly, Polynomial.map_map, twist, RingHom.frobenius_comm]
end
end K1_14
end

end Merged_Fast023

-- merged module Fast029
section Merged_Fast029
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_14_2
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
structure Stage where
  reserve : ℕ
  cheap : Shape
  layered : Shape
def stages : List Stage :=
  [⟨0, ⟨59,82,18,1899⟩, ⟨136,190,40,8441⟩⟩,
   ⟨1, ⟨66,92,21,2076⟩, ⟨150,210,44,9356⟩⟩,
   ⟨2, ⟨73,102,23,2261⟩, ⟨164,229,48,10272⟩⟩,
   ⟨3, ⟨80,112,25,2455⟩, ⟨178,249,52,11191⟩⟩,
   ⟨5, ⟨94,131,30,2824⟩, ⟨213,298,62,12959⟩⟩,
   ⟨8, ⟨115,160,36,3401⟩, ⟨262,366,77,15611⟩⟩,
   ⟨12, ⟨136,190,43,4204⟩, ⟨325,454,96,19187⟩⟩,
   ⟨18, ⟨178,248,56,5332⟩, ⟨409,572,121,24615⟩⟩,
   ⟨28, ⟨241,336,78,7235⟩, ⟨570,797,169,33523⟩⟩,
   ⟨42, ⟨325,453,104,9976⟩, ⟨759,1061,224,46271⟩⟩]
def full : Shape := ⟨836,1164,247,273617⟩
def shapes : List Shape := full :: stages.flatMap (fun s => [s.cheap, s.layered])
def bufferedAt (w : ℤ) (r : ℕ) (s : Shape) : ℕ :=
  s.m * 180265 - 1 - 2 * w.toNat * r
def UsesSeed (G : Jet) : Prop :=
  ∃ j i, 0 < ((G.coeff j).coeff i).totalDegree
abbrev ODE := Polynomial (Polynomial FX)
def fixedAt (G : ODE) (S : (Polynomial K)) : FX :=
  G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
def FixedEquation {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (T : Finset K) (B J : ℕ) : Prop :=
  ∃ G : ODE, G ≠ 0 ∧ G.natDegree ≤ J ∧
    (∀ j i, ((G.coeff j).coeff i) ≠ 0 → i+j ≤ B) ∧
    ∀ γ ∈ T, fixedAt G (F.scalar γ) = 0
def fixedKeys : List (ℕ × ℕ) := (507836, 93976) :: shapes.map (fun s => (s.B, s.J))
def endpointDegree : ℕ := 134625
def fixedPrice (B J : ℕ) : ℕ :=
  let d := endpointDegree
  let t := 2*d-3
  let a := 1+t*(B-1)
  let v := min a (t*(J-1)+d)
  let gap := 180265-d
  (81879*((B-J)*v+J*a)+gap-1)/gap+B^2
def fixedTotal : ℕ := (fixedKeys.map fun k => fixedPrice k.1 k.2).sum
def directPrice : ℕ :=
  5980 + ((p+1)*1052972+19635660) + (p+1)*(shapes.map Shape.U).sum + 310966947964
def lossSeedCap : ℕ := 220891211
def lossYCap : ℕ := 4783514411
def movingPrice : ℕ := 86954269798767161
abbrev Ambient := MvPolynomial (Fin 4) FX
abbrev RootAmbient := MvPolynomial (Fin 3) FX
def rootSeeds : Seeds →+* RootAmbient :=
  (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3))).toRingHom
def rootIncl : RootAmbient →+* Ambient :=
  (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4))).toRingHom
def toRoot : Equation →+* RootAmbient := eval₂RingHom rootSeeds (MvPolynomial.X 2)
def toJet : Jet →+* Ambient := eval₂RingHom (rootIncl.comp toRoot) (MvPolynomial.X 3)
def rootMarkHom (z : K) (S : (Polynomial K)) : RootAmbient →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z)^p, atX S]
def jetMarkHom (z : K) (S : (Polynomial K)) : Ambient →+* FX :=
  MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z)^p, atX S, atX S.derivative]
private theorem eval_root (a b y : FX) (f : Equation) :
    MvPolynomial.eval ![a,b,y] (toRoot f) = f.eval₂ (MvPolynomial.eval ![a,b]) y := by
  have hseed : (MvPolynomial.eval ![a,b,y]).comp rootSeeds = MvPolynomial.eval ![a,b] := by
    apply RingHom.ext
    intro g
    change MvPolynomial.eval ![a,b,y] (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3)) g) = _
    rw [MvPolynomial.eval_rename]
    have hvec : ![a,b,y] ∘ Fin.castLE (by decide : 2 ≤ 3) = ![a,b] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
  change MvPolynomial.eval ![a,b,y] (f.eval₂ rootSeeds (MvPolynomial.X 2)) = _
  rw [Polynomial.hom_eval₂, hseed, MvPolynomial.eval_X]
  rfl
private theorem eval_incl (a b y v : FX) (f : RootAmbient) :
    MvPolynomial.eval ![a,b,y,v] (rootIncl f) = MvPolynomial.eval ![a,b,y] f := by
  change MvPolynomial.eval ![a,b,y,v] (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4)) f) = _
  rw [MvPolynomial.eval_rename]
  have hvec : ![a,b,y,v] ∘ Fin.castLE (by decide : 3 ≤ 4) = ![a,b,y] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
theorem eval_rootIncl_toRoot (z : K) (S : (Polynomial K)) (f : Equation) :
    jetMarkHom z S (rootIncl (toRoot f)) = atMark f z S :=
  (eval_incl (seedEmbedding z) _ _ _ (toRoot f)).trans (eval_root (seedEmbedding z) _ _ f)
theorem eval_toJet (z : K) (S : (Polynomial K)) (P : Jet) :
    jetMarkHom z S (toJet P) = jetAt P z S := by
  have h : (jetMarkHom z S).comp (rootIncl.comp toRoot) =
      eval₂RingHom (graphEval z) (atX S) := by
    exact RingHom.ext (eval_rootIncl_toRoot z S)
  have hv : jetMarkHom z S (MvPolynomial.X 3) = atX S.derivative := by
    simp [jetMarkHom]
  change jetMarkHom z S (P.eval₂ (rootIncl.comp toRoot) (MvPolynomial.X 3)) = _
  rw [Polynomial.hom_eval₂, h, hv]
  rfl
def OnJet (I : Ideal Ambient) (z : K) (S : (Polynomial K)) : Prop :=
  I ≤ RingHom.ker (jetMarkHom z S)
def OnRoot (I : Ideal RootAmbient) (z : K) (S : (Polynomial K)) : Prop :=
  I ≤ RingHom.ker (rootMarkHom z S)
abbrev SeedField := FractionRing Seeds
def generic (i : Fin 2) : SeedField :=
  algebraMap Seeds SeedField (MvPolynomial.X i)
def seedLine {n : ℕ} (i j : Fin n) : MvPolynomial (Fin n) SeedField :=
  MvPolynomial.X i + MvPolynomial.C (generic 0) * MvPolynomial.X j -
    MvPolynomial.C (generic 1)
def ySection {n : ℕ} (i : Fin n) : MvPolynomial (Fin n) SeedField :=
  MvPolynomial.X i - MvPolynomial.C (generic 1)
abbrev CoordinateRing {R : Type} [CommRing R] (I : Ideal R) := R ⧸ I
abbrev JetSeedSection (I : Ideal Ambient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {seedLine 0 1})
abbrev JetYSection (I : Ideal Ambient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {ySection 2})
abbrev RootSeedSection (I : Ideal RootAmbient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {seedLine 0 1})
abbrev RootYSection (I : Ideal RootAmbient) :=
  CoordinateRing (I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {ySection 2})
def LossCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (T : Finset K) : Prop :=
  ∃ cs : Finset (Ideal Ambient),
    (∀ I ∈ cs, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 1 ∧
      Module.Finite SeedField (JetSeedSection I) ∧
      0 < Module.finrank SeedField (JetSeedSection I) ∧
      Module.Finite SeedField (JetYSection I)) ∧
    (∑ I ∈ cs, Module.finrank SeedField (JetSeedSection I)) ≤ lossSeedCap ∧
    (∑ I ∈ cs, Module.finrank SeedField (JetYSection I)) ≤ lossYCap ∧
    ∀ γ ∈ T, ∃ I ∈ cs, OnJet I (M.label γ) (F.scalar γ)
def SmallRootCurve (I : Ideal RootAmbient) (g H : ℕ) : Prop :=
  I.IsPrime ∧
    ∃ C₀ : MvPolynomial (Fin 2) L, Irreducible C₀ ∧
      I.comap rootSeeds =
        Ideal.span {(MvPolynomial.map
          ((algebraMap (Polynomial L) FX).comp (Polynomial.C : L →+* (Polynomial L))) C₀)} ∧
      Module.Finite SeedField (RootSeedSection I) ∧
      Module.finrank SeedField (RootSeedSection I) = C₀.totalDegree * g ∧
      Module.Finite SeedField (RootYSection I) ∧
      Module.finrank SeedField (RootYSection I) ≤ H
abbrev FibreRing := MvPolynomial (Fin 2) SeedField
def mapGenericSeed : Ambient →+* FibreRing :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
    ![MvPolynomial.C (generic 0), MvPolynomial.C (generic 1), MvPolynomial.X 0, MvPolynomial.X 1]
abbrev OverSeeds (I : Ideal Ambient) :=
  CoordinateRing (I.map mapGenericSeed)
def mapGenericJets : Ambient →+* FibreRing :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C (generic 0), MvPolynomial.C (generic 1)]
abbrev OverJets (I : Ideal Ambient) :=
  CoordinateRing (I.map mapGenericJets)
structure RetainedParents (rows : Banks) where
  ideals : Finset (Ideal Ambient)
  prime : ∀ I ∈ ideals, I.IsPrime
  seed_finite : ∀ I ∈ ideals, Module.Finite SeedField (OverSeeds I)
  seed_size : ∀ I ∈ ideals, 0 < Module.finrank SeedField (OverSeeds I) ∧
    Module.finrank SeedField (OverSeeds I) < p
  jet_finite : ∀ I ∈ ideals, Module.Finite SeedField (OverJets I)
  jet_size : ∀ I ∈ ideals, 0 < Module.finrank SeedField (OverJets I) ∧
    Module.finrank SeedField (OverJets I) < p
  terminal : ∀ I ∈ ideals, ∀ P ∈ rows full (full.m * 180265 - 1), toJet P ∈ I
structure Geometry {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) where
  direct : Finset K
  lost : Finset K
  kept : Finset K
  fixedGroups : (ℕ × ℕ) → Finset K
  parents : RetainedParents rows
  direct_card : direct.card ≤ directPrice
  fixed_eq : ∀ k ∈ fixedKeys, fixedGroups k ⊆ Γ ∧ FixedEquation F (fixedGroups k) k.1 k.2
  lost_subset : lost ⊆ Γ
  loss_cover : LossCover M F lost
  kept_subset : kept ⊆ Γ
  kept_cover : ∀ γ ∈ kept, ∃ I ∈ parents.ideals, OnJet I (M.label γ) (F.scalar γ)
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ (∃ k ∈ fixedKeys, γ ∈ fixedGroups k) ∨ γ ∈ lost ∨ γ ∈ kept
end
end K1_14_2
end
section
namespace K1_14_2
noncomputable section
open K1 K1_14 Polynomial
set_option maxRecDepth 12000 in
private theorem ledger (w : ℤ) (hw : w ≤ 3554) :
    directPrice + fixedTotal + movingPrice ≤ highPrefix w := by
  have he : highPrefix w = 132117856182247703 := by simp [highPrefix, hw]
  rw [he]
  decide +kernel
end
end K1_14_2
end
section
namespace K1_14_2_1
open K1_14 K1_14_2
def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * 180265 - 2 * h * r
def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)
def rawVolume (h r : ℕ) (s : Shape) : ℕ :=
  triangle s.U * shapeSum s (rawWidth h r s)
def movingCeiling (h : ℕ) (s : Shape) : ℕ :=
  triangle s.U * shapeSum s (fun _ j => 2 * h * j)
end K1_14_2_1
end
section
set_option maxSynthPendingDepth 8
namespace K1_14_2_1
noncomputable section
open K1_14 K1_14_2 Polynomial UniqueFactorizationMonoid
private def divisible (V : Submodule FX Jet) (G : Jet) : Submodule FX V where
  carrier := {Q | G ∣ (Q : Jet)}
  zero_mem' := dvd_zero G
  add_mem' := fun hP hQ => dvd_add hP hQ
  smul_mem' a := by
    rintro Q ⟨R, hR⟩
    exact ⟨a • R, by
      change a • (Q : Jet) = G * (a • R)
      rw [hR, mul_smul_comm]⟩
theorem exists_layered (P : Jet) (hP : P ≠ 0) (V : Submodule FX Jet)
    (hn : ∃ Q ∈ V, Q ≠ 0)
    (hproper : ∀ G : Jet, Irreducible G → G ∣ P → 0 < G.natDegree → UsesSeed G →
      ∃ Q ∈ V, ¬ G ∣ Q) :
    ∃ Q ∈ V, Q ≠ 0 ∧
      ∀ G : Jet, Irreducible G → G ∣ P → 0 < G.natDegree → UsesSeed G → ¬ G ∣ Q := by
  classical
  let : Infinite FX := Infinite.of_injective _ (IsFractionRing.injective (Polynomial L) FX)
  let I := {H : Jet // H ∈ factors P}
  let : Finite I := Set.finite_coe_iff.mpr (factors P).finite_toSet
  let tests : Option I → Submodule FX V := fun k =>
    match k with
    | none => ⊥
    | some H =>
      if ∃ G : Jet, Irreducible G ∧ G ∣ P ∧ 0 < G.natDegree ∧ UsesSeed G ∧
          Associated G H.val then divisible V H.val else ⊥
  have bot_proper : (⊥ : Submodule FX V) ≠ ⊤ := by
    obtain ⟨Q, hQ, hnQ⟩ := hn
    intro heq
    have hmem : (⟨Q, hQ⟩ : V) ∈ (⊥ : Submodule FX V) := heq ▸ Submodule.mem_top
    exact hnQ (congrArg Subtype.val ((Submodule.mem_bot FX).mp hmem))
  have ht : ∀ k, tests k ≠ ⊤ := by
    intro k
    cases k with
    | none => exact bot_proper
    | some H =>
      change (if _ then divisible V H.val else ⊥) ≠ ⊤
      split_ifs with h
      · obtain ⟨G, hi, hd, hv, hs, ha⟩ := h
        obtain ⟨Q, hQ, hnQ⟩ := hproper G hi hd hv hs
        intro heq
        have hmem : (⟨Q, hQ⟩ : V) ∈ divisible V H.val := heq ▸ Submodule.mem_top
        exact hnQ (ha.dvd.trans (show H.val ∣ Q from hmem))
      · exact bot_proper
  obtain ⟨Q, hQ⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (K := FX) (M := V) tests ht
  refine ⟨Q.val, Q.property, ?_, ?_⟩
  · intro hz
    exact hQ none ((Submodule.mem_bot FX).mpr (Subtype.ext hz))
  · intro G hi hd hv hs hdiv
    obtain ⟨H, hH, ha⟩ := exists_mem_factors_of_dvd hP hi hd
    let k : I := ⟨H, hH⟩
    apply hQ (some k)
    change Q ∈ (if _ then divisible V H else ⊥)
    rw [ite_eq_left ⟨G, hi, hd, hv, hs, ha⟩]
    exact ha.symm.dvd.trans hdiv
end
end K1_14_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
abbrev JetPlane := Polynomial (Polynomial FX)
abbrev Surface := PrimeSpectrum Jet
def fixedEmbedding : JetPlane →+* Jet :=
  Polynomial.mapRingHom (Polynomial.mapRingHom MvPolynomial.C)
def fixedAt (G : JetPlane) (S : (Polynomial K)) : FX :=
  G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
def JetCaps {R : Type*} [Semiring R] (G : Polynomial (Polynomial R)) (b j : ℕ) : Prop :=
  ∀ v y, (G.coeff v).coeff y ≠ 0 → y + v ≤ b ∧ v ≤ j
def RowCaps (G : Jet) (s : Shape) : Prop :=
  ∀ v y, (G.coeff v).coeff y ≠ 0 →
    y + v ≤ s.B ∧ v ≤ s.J ∧ ((G.coeff v).coeff y).totalDegree ≤ s.U
def cheapShape (i : Fin 4) : Shape :=
  ![⟨45,63,14,812⟩, ⟨57,80,18,1041⟩, ⟨81,114,26,1383⟩, ⟨123,173,40,2173⟩] i
def layeredShape (i : Fin 4) : Shape :=
  ![⟨84,118,24,2907⟩, ⟨114,160,33,3775⟩, ⟨144,203,42,5064⟩, ⟨231,325,67,8061⟩] i
def reserve (i : Fin 4) : ℕ := ![0,2,5,12] i
def fullShape : Shape := ⟨358,500,105,66251⟩
def reserveCutoff (h : ℕ) (s : Shape) (i : Fin 4) : ℕ :=
  s.m * 180265 - 1 - 2*h*reserve i
def contactPower (h : ℕ) (s : Shape) (W : ℕ) : ℕ :=
  1 + (s.m * 180265 - 1 - W) / (2*h)
def SeedShift (h : ℕ) (rows : Banks) (s : Shape) : Prop :=
  ∀ W, ∀ P ∈ rows s W, ∀ i r, seedHasse i r P ∈ rows s (W + 2*h*r)
def LeadingFilter (h : ℕ) (rows : Banks) (s : Shape) : Prop :=
  ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree) * (131071-h) ≤ W + P.natDegree
def NoMovingCommon (P Q : Jet) : Prop :=
  ∀ D : Jet, Irreducible D → D ∣ P → D ∣ Q → 0 < D.natDegree →
    D ∈ Set.range fixedEmbedding
structure BufferedPair (h : ℕ) (rows : Banks) (i : Fin 4) where
  cheap : Jet
  layered : Jet
  cheap_ne : cheap ≠ 0
  layered_ne : layered ≠ 0
  cheap_mem : cheap ∈ rows (cheapShape i) (reserveCutoff h (cheapShape i) i)
  layered_mem : layered ∈ rows (layeredShape i) (reserveCutoff h (layeredShape i) i)
  cheap_caps : RowCaps cheap (cheapShape i)
  layered_caps : RowCaps layered (layeredShape i)
  no_moving : NoMovingCommon cheap layered
abbrev SeedField := FractionRing Seeds
abbrev SeedClosure := AlgebraicClosure SeedField
abbrev JetField := FractionRing JetPlane
abbrev JetClosure := AlgebraicClosure JetField
abbrev FibreJet := Polynomial (Polynomial SeedClosure)
def seedGeneric : Seeds →+* SeedClosure :=
  (algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField)
def jetGeneric : JetPlane →+* JetClosure :=
  let first : JetPlane →+* JetField := algebraMap JetPlane JetField
  let second : JetField →+* JetClosure := algebraMap JetField JetClosure
  second.comp first
def seedFibreEval (y v : SeedClosure) : Jet →+* SeedClosure :=
  eval₂RingHom (eval₂RingHom seedGeneric y) v
def OnSeedFibre (q : Surface) (y v : SeedClosure) : Prop :=
  RingHom.ker (seedFibreEval y v) = q.asIdeal
structure Parent (q : Surface) : Prop where
  height_two : q.asIdeal.height = 2
  seed_side : ∃ y v, OnSeedFibre q y v ∧ IsSeparable SeedField y ∧ IsSeparable SeedField v
  jet_side : ∃ g : Jet →+* JetClosure,
    g.comp fixedEmbedding = jetGeneric ∧ RingHom.ker g = q.asIdeal ∧
      ∀ i : Fin 2, IsSeparable JetField (g (C (C (MvPolynomial.X i))))
def fibreRow (P : Jet) : FibreJet := P.map (Polynomial.mapRingHom seedGeneric)
def fibrePoint (y v : SeedClosure) : Ideal FibreJet :=
  Ideal.span {C (R := Polynomial SeedClosure) (Polynomial.X (R := SeedClosure) - C y),
    Polynomial.X (R := Polynomial SeedClosure) - C (C v)}
def OrderAt (q : Surface) (P : Jet) (m : ℕ) : Prop :=
  ∀ y v, OnSeedFibre q y v → fibreRow P ∈ fibrePoint y v ^ m
abbrev ClearedSeeds := MvPolynomial (Fin 2) (Polynomial L)
abbrev ClearedEquation := Polynomial ClearedSeeds
def liftEquation : ClearedEquation →+* Equation :=
  Polynomial.mapRingHom (MvPolynomial.map (algebraMap (Polynomial L) FX))
def clearedDx (g : ClearedEquation) : ClearedEquation :=
  g.sum fun j a => monomial j (∑ e ∈ MvPolynomial.support a, MvPolynomial.monomial e (AddMonoidAlgebra.coeff a e).derivative)
def ordinaryCutter (g : ClearedEquation) : Jet :=
  C (liftEquation (clearedDx g)) + X * C (liftEquation g.derivative)
def IsClearing (f : Equation) (g : ClearedEquation) (a : (Polynomial L)) : Prop :=
  a ≠ 0 ∧ liftEquation g = C (MvPolynomial.C (algebraMap (Polynomial L) FX a)) * f
def Compatible (P Q : Jet) (q : Surface) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    C f ∈ q.asIdeal → ∀ g a, IsClearing f g a → ordinaryCutter g ∈ q.asIdeal
inductive Slice where
  | seed | ordinate | mixed | jets
abbrev SectionField := FractionRing (MvPolynomial (Fin 4) FX)
abbrev SectionSeeds := MvPolynomial (Fin 2) SectionField
abbrev SectionJet := Polynomial (Polynomial SectionSeeds)
def sectionMap : Jet →+* SectionJet :=
  Polynomial.mapRingHom (Polynomial.mapRingHom
    (MvPolynomial.map (algebraMap FX SectionField)))
def sectionScalar (i : Fin 4) : SectionJet :=
  C (C (MvPolynomial.C (algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i))))
def sectionEquations (slice : Slice) : Set SectionJet :=
  let t₀ : SectionJet := C (C (MvPolynomial.X 0))
  let t₁ : SectionJet := C (C (MvPolynomial.X 1))
  let y : SectionJet := C (R := Polynomial SectionSeeds) (Polynomial.X (R := SectionSeeds))
  let v : SectionJet := Polynomial.X (R := Polynomial SectionSeeds)
  let seedLine := t₀ + sectionScalar 0 * t₁
  let jetLine := y + sectionScalar 1 * v
  let a := sectionScalar 2
  let b := sectionScalar 3
  match slice with
  | .seed => {t₀ - a, t₁ - b}
  | .ordinate => {seedLine - a, y - b}
  | .mixed => {seedLine - a, jetLine - b}
  | .jets => {y - a, v - b}
def sectionDegree (q : Surface) (slice : Slice) : ℕ :=
  let J := q.asIdeal.map sectionMap ⊔ Ideal.span (sectionEquations slice)
  Module.finrank SectionField (SectionJet ⧸ J)
def mass (qs : Finset Surface) (s : Slice) : ℚ :=
  ∑ q ∈ qs, (sectionDegree q s : ℚ)
structure MassCap (qs : Finset Surface) (a c z : ℚ) : Prop where
  seed : mass qs .seed ≤ a
  ordinate : mass qs .ordinate ≤ c
  mixed : mass qs .mixed ≤ z
structure SeedCover where
  curve : Seeds
  curve_ne : curve ≠ 0
  points : Finset (FX × FX)
def SeedCover.Covers (C : SeedCover) (z : K) : Prop :=
  graphEval z C.curve = 0 ∨ (seedEmbedding z, seedEmbedding z ^ p) ∈ C.points
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) where
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  masses : MassCap parents 2891 60998 381269
  jetMass : mass parents .jets ≤ 3019828
  seeds : SeedCover
  seedDegree : seeds.curve.totalDegree ≤ 381269 + 812 + 2907
  seedPoints : seeds.points.card ≤ 3019828
  ordinates : Finset FX
  ordinateCount : ordinates.card ≤ 2891
  lowJet : JetPlane
  fixedCheap : JetPlane
  fixedLayered : JetPlane
  lowJet_ne : lowJet ≠ 0
  fixedCheap_ne : fixedCheap ≠ 0
  fixedLayered_ne : fixedLayered ≠ 0
  lowJet_caps : JetCaps lowJet 381269 60998
  fixedCheap_caps : JetCaps fixedCheap 63 14
  fixedLayered_caps : JetCaps fixedLayered 118 24
  cover : ∀ γ ∈ Γ,
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    fixedAt lowJet (F.scalar γ) = 0 ∨ fixedAt fixedCheap (F.scalar γ) = 0 ∨
    fixedAt fixedLayered (F.scalar γ) = 0 ∨ ∃ q ∈ parents, MarkOn M F q γ
structure ProjectedProduct (qs : Finset Surface) (f : Equation) : Prop where
  positive : 0 < f.natDegree
  primitive : f.IsPrimitive
  separable : (f.map (algebraMap Seeds SeedField)).Separable
  vanishes : ∀ q ∈ qs, C f ∈ q.asIdeal
  divides_leading : ∀ (P : Jet) (k : ℕ), P ≠ 0 →
    (∀ q ∈ qs, OrderAt q P k) → f ^ (k - P.natDegree) ∣ P.leadingCoeff
end
end K1_14_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
def stageAt (i : Fin 10) : Stage :=
  stages.get ⟨i.val, by simp [stages]⟩
def RowCaps (P : Jet) (s : Shape) : Prop :=
  ∀ j i, (P.coeff j).coeff i ≠ 0 →
    i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U
def ODECaps (G : ODE) (B J : ℕ) : Prop :=
  G ≠ 0 ∧ G.natDegree ≤ J ∧ ∀ j i, (G.coeff j).coeff i ≠ 0 → i+j ≤ B
structure RowPair (w : ℤ) (rows : Banks) (i : Fin 10) where
  cheap : Jet
  layered : Jet
  cheap_ne : cheap ≠ 0
  layered_ne : layered ≠ 0
  cheap_mem : cheap ∈ rows (stageAt i).cheap (bufferedAt w (stageAt i).reserve (stageAt i).cheap)
  layered_mem : layered ∈ rows (stageAt i).layered (bufferedAt w (stageAt i).reserve (stageAt i).layered)
  cheap_caps : RowCaps cheap (stageAt i).cheap
  layered_caps : RowCaps layered (stageAt i).layered
  no_moving : ∀ G : Jet, Irreducible G → G ∣ cheap → 0 < G.natDegree →
    UsesSeed G → ¬ G ∣ layered
def fixedIncl : ODE →+* Jet := K1_14_3.fixedEmbedding
structure FixedPart (P : Jet) (s : Shape) where
  equation : ODE
  equation_caps : ODECaps equation s.B s.J
  residual : Jet
  factorization : P = fixedIncl equation * residual
  stripped : ∀ G : ODE, Irreducible (fixedIncl G) → ¬ fixedIncl G ∣ residual
structure FixedPair {w rows i} (B : RowPair w rows i) where
  cheap : FixedPart B.cheap (stageAt i).cheap
  layered : FixedPart B.layered (stageAt i).layered
def compatible (P Q : Jet) (I : Ideal Ambient) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    rootIncl (toRoot f) ∈ I →
    ∀ g a, K1_14_3.IsClearing f g a → toJet (K1_14_3.ordinaryCutter g) ∈ I
def fixedOn (G : ODE) (I : Ideal Ambient) : Prop :=
  toJet (fixedIncl G) ∈ I
abbrev SectionField := FractionRing (MvPolynomial (Fin 4) FX)
abbrev SectionAmbient := MvPolynomial (Fin 4) SectionField
def sliceParameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def sectionBase : Ambient →+* SectionAmbient := MvPolynomial.map (algebraMap FX SectionField)
def sectionSeedLine : SectionAmbient :=
  MvPolynomial.X 0 + MvPolynomial.C (sliceParameter 0) * MvPolynomial.X 1 -
    MvPolynomial.C (sliceParameter 2)
def sectionJetLine : SectionAmbient :=
  MvPolynomial.X 2 + MvPolynomial.C (sliceParameter 1) * MvPolynomial.X 3 -
    MvPolynomial.C (sliceParameter 3)
abbrev OverOrdinate (I : Ideal Ambient) :=
  CoordinateRing (I.map sectionBase ⊔ Ideal.span {sectionSeedLine, (MvPolynomial.X 2 -
    MvPolynomial.C (sliceParameter 3))})
abbrev OverMixed (I : Ideal Ambient) :=
  CoordinateRing (I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine})
def ordinateIncl : Polynomial FX →+* Ambient :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X 2)
def jetPlaneIncl : ODE →+* Ambient := toJet.comp fixedIncl
structure Active (I : Ideal Ambient) : Prop where
  prime : I.IsPrime
  dimension : ringKrullDim (CoordinateRing I) = 2
  seed_finite : Module.Finite SeedField (OverSeeds I)
  ordinate_finite : Module.Finite SectionField (OverOrdinate I)
  mixed_finite : Module.Finite SectionField (OverMixed I)
  jet_finite : Module.Finite SeedField (OverJets I)
  seed_size : 0 < Module.finrank SeedField (OverSeeds I) ∧
    Module.finrank SeedField (OverSeeds I) < p
  mixed_lt : Module.finrank SectionField (OverMixed I) < p
  jet_lt : Module.finrank SeedField (OverJets I) < p
  ordinate_dominant : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
def dual (I : Ideal Ambient) : Prop := 0 < Module.finrank SeedField (OverJets I)
def sectionDegree (I : Ideal Ambient) : Fin 4 → ℕ :=
  ![Module.finrank SeedField (OverSeeds I), Module.finrank SectionField (OverOrdinate I),
    Module.finrank SectionField (OverMixed I), Module.finrank SeedField (OverJets I)]
def mass (S : Finset (Ideal Ambient)) (k : Fin 4) : ℕ :=
  ∑ I ∈ S, sectionDegree I k
def Fits (S : Finset (Ideal Ambient)) (cap : Fin 4 → ℕ) : Prop :=
  ∀ k, mass S k ≤ cap k
def orderOn (I : Ideal Ambient) (P : Jet) (m : ℕ) : Prop :=
  let imageIdeal := if dual I then ⊥ else (I.comap jetPlaneIncl).map jetPlaneIncl
  ∃ a : Ambient, a ∉ I ∧ a * toJet P ∈ I^m ⊔ imageIdeal
def budget (n : ℕ) : Fin 4 → ℕ :=
  match n with
  | 0 => ![5980,227898,1052972,16029459]
  | 1 => ![3767,143910,648356,4855764]
  | 2 => ![3019,114928,521837,4855764]
  | 3 => ![2687,101858,521837,3052656]
  | 4 => ![422,15662,158698,1993744]
  | 5 => ![280,10171,103959,1285200]
  | 6 => ![225,8016,68569,995828]
  | 7 => ![170,6245,54168,776610]
  | 8 => ![145,5264,47174,606347]
  | _ => ![123,4633,40170,512888]
def weight (s : Shape) (fee : Fin 3) : Fin 4 → ℕ :=
  ![![s.U, s.B-s.J, s.J, 0],
    ![0, s.U, 0, s.J],
    ![0,0, s.U, s.B]] fee
def dot (weight values : Fin 4 → ℕ) : ℕ := ∑ k, weight k * values k
def initialPrice : ℕ := 5980 + ((p+1)*1052972+19635660) + (p+1)*(1899+8441)
def OnParent {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop :=
  OnJet I (M.label γ) (F.scalar γ)
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (cheapFixed layeredFixed : ODE) where
  parents : Finset (Ideal Ambient)
  geometric : ∀ I ∈ parents, Active I
  initial_mass : Fits parents (budget 0)
  direct : Finset K
  direct_card : direct.card ≤ initialPrice
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ fixedAt cheapFixed (F.scalar γ) = 0 ∨
    fixedAt layeredFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent M F I γ
def CurveGeometry (I : Ideal Ambient) : Prop :=
  I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 1 ∧
    Module.Finite SeedField (JetSeedSection I) ∧
    0 < Module.finrank SeedField (JetSeedSection I) ∧
    Module.Finite SeedField (JetYSection I)
structure CutCover where
  direct : Finset K
  curves : Finset (Ideal Ambient)
  geometric : ∀ I ∈ curves, CurveGeometry I
def curveSeedMass (C : Finset (Ideal Ambient)) : ℕ :=
  ∑ I ∈ C, Module.finrank SeedField (JetSeedSection I)
def curveYMass (C : Finset (Ideal Ambient)) : ℕ :=
  ∑ I ∈ C, Module.finrank SeedField (JetYSection I)
def CutCover.cost (C : CutCover) (fee : Fin 3) : ℕ :=
  ![curveSeedMass C.curves, curveYMass C.curves, C.direct.card] fee
end
end K1_14_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
theorem eval_fixed (z : K) (S : (Polynomial K)) (G : ODE) :
    jetMarkHom z S (toJet (fixedIncl G)) = fixedAt G S := by
  rw [eval_toJet]
  change (G.map (Polynomial.mapRingHom MvPolynomial.C)).eval₂
      (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative) =
    G.eval₂ (evalRingHom (atX S)) (atX S.derivative)
  rw [eval₂_map]
  have h : (eval₂RingHom (graphEval z) (atX S)).comp (Polynomial.mapRingHom MvPolynomial.C) =
      evalRingHom (atX S) := by
    apply RingHom.ext
    intro f
    change (f.map MvPolynomial.C).eval₂ (graphEval z) (atX S) = f.eval (atX S)
    rw [eval₂_map, ← eval₂_id]
    have hc : (graphEval z).comp MvPolynomial.C = RingHom.id FX := by
      ext c
      simp [graphEval]
    rw [hc]
  rw [h]
theorem mass_mono {S T : Finset (Ideal Ambient)} (h : S ⊆ T) (k : Fin 4) :
    mass S k ≤ mass T k :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)
theorem sum_union_le {α : Type*} (f : α → ℕ) (A B : Finset α) :
    (∑ a ∈ A ∪ B, f a) ≤ (∑ a ∈ A, f a) + ∑ a ∈ B, f a := by
  have h := Finset.sum_union_inter (f := f) (s₁ := A) (s₂ := B)
  omega
theorem sum_biUnion_le {α β : Type*} (A : Finset α) (B : α → Finset β) (f : β → ℕ) :
    (∑ x ∈ A.biUnion B, f x) ≤ ∑ i ∈ A, ∑ x ∈ B i, f x := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le f _ _).trans (Nat.add_le_add_left ih _)
def joinCuts {α : Type*} (A : Finset α) (B : α → CutCover) : CutCover where
  direct := A.biUnion (fun i => (B i).direct)
  curves := A.biUnion (fun i => (B i).curves)
  geometric := fun I hI => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hI
    exact (B i).geometric I hi
theorem joinCuts_cost {α : Type*} (A : Finset α) (B : α → CutCover) (fee : Fin 3) :
    (joinCuts A B).cost fee ≤ ∑ i ∈ A, (B i).cost fee := by
  fin_cases fee
  · exact sum_biUnion_le _ _ _
  · exact sum_biUnion_le _ _ _
  · exact Finset.card_biUnion_le
theorem sum_dot (A : Finset (Ideal Ambient)) (w : Fin 4 → ℕ) :
    (∑ I ∈ A, dot w (sectionDegree I)) = dot w (mass A) := by
  simp only [dot, mass, Finset.mul_sum]
  exact Finset.sum_comm
def emptyCut : CutCover :=
  ⟨∅, ∅, by simp⟩
theorem fits_mono {S T : Finset (Ideal Ambient)} {cap : Fin 4 → ℕ} (hs : S ⊆ T)
    (ht : Fits T cap) : Fits S cap :=
  fun k => (mass_mono hs k).trans (ht k)
end
end K1_14_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
def ordinarySeedDegree (f : Equation) : ℕ :=
  f.support.sup fun y => (f.coeff y).totalDegree
structure ProperPair (P Q : Jet) : Prop where
  left_ne : P ≠ 0
  right_ne : Q ≠ 0
  no_common : ∀ D : Jet, Irreducible D → D ∣ P → ¬ D ∣ Q
def markEval (z : K) (S : (Polynomial K)) : Jet →+* FX :=
  eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
def AtSurface (q : Surface) (z : K) (S : (Polynomial K)) : Prop :=
  q.asIdeal ≤ RingHom.ker (markEval z S)
structure PreparedPair (P Q : Jet) where
  seedContent : Seeds
  fixedCheap : JetPlane
  fixedLayered : JetPlane
  cheap : Jet
  layered : Jet
  ordinary : Finset Equation
  seedContent_ne : seedContent ≠ 0
  seedContent_degree : seedContent.totalDegree ≤ 812 + 2907
  fixedCheap_ne : fixedCheap ≠ 0
  fixedLayered_ne : fixedLayered ≠ 0
  fixedCheap_caps : JetCaps fixedCheap 63 14
  fixedLayered_caps : JetCaps fixedLayered 118 24
  cheap_caps : RowCaps cheap (cheapShape 0)
  layered_caps : RowCaps layered (layeredShape 0)
  proper : ProperPair cheap layered
  ordinary_factors : ∀ f ∈ ordinary, Irreducible f ∧ 0 < f.natDegree
  ordinary_seed : ∑ f ∈ ordinary, ordinarySeedDegree f ≤ 812
  ordinary_y : ∑ f ∈ ordinary, f.natDegree ≤ 63
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    graphEval z seedContent = 0 ∨ fixedAt fixedCheap S = 0 ∨ fixedAt fixedLayered S = 0 ∨
      (jetAt cheap z S = 0 ∧ jetAt layered z S = 0) ∨
      ∃ f ∈ ordinary, atMark f z S = 0
end
end K1_14_3_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators Classical
theorem seed_count {T : Finset K} {label : K → K} (hinj : Set.InjOn label (T : Set K))
    (C : SeedCover) (hdeg : C.curve.totalDegree < p)
    (hcover : ∀ γ ∈ T, C.Covers (label γ)) :
    T.card ≤ (p+1)*C.curve.totalDegree + C.points.card := by
  classical
  let zero := T.filter (fun γ => graphEval (label γ) C.curve = 0)
  let other := T.filter (fun γ => graphEval (label γ) C.curve ≠ 0)
  have inj : Set.InjOn (fun γ => seedEmbedding (label γ)) (T : Set K) :=
    fun _ ha _ hb h => hinj ha hb (seedEmbedding.injective h)
  have hzero : zero.card ≤ (p+1)*C.curve.totalDegree := by
    have hcard : (zero.image (fun γ => seedEmbedding (label γ))).card = zero.card :=
      Finset.card_image_iff.mpr (inj.mono (by exact Finset.filter_subset _ _))
    have hb := frobenius_coefficient_exception_count p
      C.curve.totalDegree C.curve.totalDegree (by decide) C.curve C.curve_ne
      (C.curve.degreeOf_le_totalDegree 0) hdeg (C.curve.degreeOf_le_totalDegree 1)
      (zero.image (fun γ => seedEmbedding (label γ))) (by
        intro x hx
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hγ).2)
    simpa only [hcard, Nat.add_mul, Nat.one_mul, Nat.add_comm (C.curve.totalDegree)] using hb
  have hother : other.card ≤ C.points.card := by
    apply Finset.card_le_card_of_injOn
      (fun γ => (seedEmbedding (label γ), seedEmbedding (label γ)^p))
    · intro γ hγ
      have hm := Finset.mem_filter.mp (show γ ∈ other from hγ)
      exact (hcover γ hm.1).resolve_left hm.2
    · intro x hx y hy h
      exact inj (Finset.mem_filter.mp (show x ∈ other from hx)).1
        (Finset.mem_filter.mp (show y ∈ other from hy)).1 (congrArg Prod.fst h)
  rw [← Finset.card_filter_add_card_filter_not (s := T)
    (p := fun γ => graphEval (label γ) C.curve = 0)]
  exact Nat.add_le_add hzero hother
theorem scalar_atX_injective : Function.Injective atX :=
  (IsFractionRing.injective (Polynomial L) FX).comp
    (Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective)
theorem label_injective {u del} (M : AnchorModel u del) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h
def joinCovers {ι : Type*} (I : Finset ι) (C : ι → SeedCover) : SeedCover := by
  classical
  exact ⟨∏ i ∈ I, (C i).curve,
    Finset.prod_ne_zero_iff.mpr (fun i _ => (C i).curve_ne),
    I.biUnion (fun i => (C i).points)⟩
theorem joinCovers_degree {ι : Type*} (I : Finset ι) (C : ι → SeedCover) :
    (joinCovers I C).curve.totalDegree ≤ ∑ i ∈ I, (C i).curve.totalDegree :=
  MvPolynomial.totalDegree_finsetProd I _
theorem joinCovers_points {ι : Type*} (I : Finset ι) (C : ι → SeedCover) :
    (joinCovers I C).points.card ≤ ∑ i ∈ I, (C i).points.card :=
  Finset.card_biUnion_le
theorem joinCovers_covers {ι : Type*} {I : Finset ι} {C : ι → SeedCover} {i : ι}
    (hi : i ∈ I) {z : K} (hz : (C i).Covers z) :
    (joinCovers I C).Covers z := by
  classical
  rcases hz with h | h
  · left
    change graphEval z (∏ j ∈ I, (C j).curve) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero hi h
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
end
end K1_14_3
end

end Merged_Fast029
