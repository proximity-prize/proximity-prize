import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_14_2_4
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
abbrev ParameterRing (n : ℕ) := MvPolynomial (Fin n) L
abbrev FamilyEquation (n : ℕ) := Polynomial (Polynomial (ParameterRing n))
abbrev SourceRing (n : ℕ) := MvPolynomial (Option (Fin n)) FX
def specialize {n : ℕ} (f : FamilyEquation n) (t : Fin n → L) :
    Polynomial (Polynomial L) :=
  f.map (Polynomial.mapRingHom (MvPolynomial.eval t))
def FamilyDegree {n : ℕ} (f : FamilyEquation n) (g : ℕ) : Prop :=
  f.natDegree ≤ g ∧ ∀ i j, ((f.coeff i).coeff j).totalDegree ≤ 1
def markedPoint {n : ℕ} (t : Fin n → L) (S : K[X]) : Option (Fin n) → FX
  | none => atX S
  | some j => algebraMap L FX (t j)
def taylorPower (d : ℕ) : ℕ := 2 * d - 1
def ordinateBound (d g : ℕ) : ℕ := 1 + taylorPower d * (g - 1)
abbrev SliceField (n : ℕ) := FractionRing (SourceRing n)
abbrev SliceAmbient (n : ℕ) := MvPolynomial (Option (Fin n)) (SliceField n)
def sliceVariable {n : ℕ} (i : Option (Fin n)) : SliceField n :=
  algebraMap (SourceRing n) (SliceField n) (MvPolynomial.X i)
def parameterCut (n : ℕ) : SliceAmbient n :=
  (∑ j : Fin n, MvPolynomial.C (sliceVariable (some j)) * MvPolynomial.X (some j)) -
    MvPolynomial.C (sliceVariable (n := n) none)
def ordinateCut (n : ℕ) : SliceAmbient n :=
  MvPolynomial.X none - MvPolynomial.C (sliceVariable (n := n) none)
abbrev SectionRing {n : ℕ} (J : Ideal (SourceRing n)) (q : SliceAmbient n) :=
  SliceAmbient n ⧸
    (J.map (MvPolynomial.map (algebraMap FX (SliceField n))) ⊔ Ideal.span {q})
structure SliceBounds {n : ℕ} (J : Ideal (SourceRing n)) (Dparam Dy : ℕ) : Prop where
  parameter_finite : Module.Finite (SliceField n) (SectionRing J (parameterCut n))
  parameter_length : Module.finrank (SliceField n) (SectionRing J (parameterCut n)) ≤ Dparam
  ordinate_finite : Module.Finite (SliceField n) (SectionRing J (ordinateCut n))
  ordinate_length : Module.finrank (SliceField n) (SectionRing J (ordinateCut n)) ≤ Dy
structure RegularChart (U : Finset K) (s : K → K[X]) (g H n : ℕ) where
  equation : FamilyEquation n
  equation_degree : FamilyDegree equation g
  parameter : K → Fin n → L
  source : Ideal (SourceRing n)
  source_prime : source.IsPrime
  source_dim : (MvPolynomial.affineHilbertPolynomial source).natDegree ≤ 1
  slices : SliceBounds source (g * H) H
  lies_on : ∀ γ ∈ U, markedPoint (parameter γ) (s γ) ∈ MvPolynomial.zeroLocus FX source
  root : ∀ γ ∈ U, (specialize equation (parameter γ)).eval (liftPoly (s γ)) = 0
  simple : ∀ γ ∈ U, (specialize equation (parameter γ)).derivative.eval (liftPoly (s γ)) ≠ 0
structure TaylorForms (n a b : ℕ) where
  denominator : SourceRing n
  numerator : K → SourceRing n
  denominator_bound : denominator ∈ MvPolynomial.restrictBidegree (Fin n) FX a b
  numerator_bound : ∀ x, numerator x ∈ MvPolynomial.restrictBidegree (Fin n) FX a b
def TaylorForms.Recovers {n a b : ℕ} (C : TaylorForms n a b)
    (t : Fin n → L) (S : K[X]) : Prop :=
  let ev := MvPolynomial.aeval (markedPoint t S)
  ev C.denominator ≠ 0 ∧
    ∀ x, ev (C.numerator x) = ev C.denominator * seedEmbedding (S.eval x)
abbrev LinearRing (n a b : ℕ) :=
  MvPolynomial (MvPolynomial.bidegreeExponents (Fin n) a b) FX
def linearIdeal {n : ℕ} (a b : ℕ) (J : Ideal (SourceRing n)) :
    Ideal (LinearRing n a b) :=
  J.comap (MvPolynomial.bidegreeMap (Fin n) FX a b)
end
end K1_14_2_4
end
section
namespace K1_14_2_4_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4
open scoped Polynomial BigOperators
abbrev ConstantSeeds := MvPolynomial (Fin 2) L
abbrev constantIdeal (C₀ : ConstantSeeds) : Ideal ConstantSeeds := Ideal.span {C₀}
instance (C₀ : ConstantSeeds) [h : Fact (Irreducible C₀)] : (constantIdeal C₀).IsPrime :=
  (Ideal.span_singleton_prime h.out.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp h.out)
abbrev ConstantSeedRing (C₀ : ConstantSeeds) := ConstantSeeds ⧸ constantIdeal C₀
abbrev ConstantSeedField (C₀ : ConstantSeeds) := FractionRing (ConstantSeedRing C₀)
abbrev ConstantSeedX (C₀ : ConstantSeeds) := FractionRing (ConstantSeedField C₀)[X]
def constToSeed (C₀ : ConstantSeeds) : L →+* ConstantSeedField C₀ :=
  (algebraMap (ConstantSeedRing C₀) (ConstantSeedField C₀)).comp
    ((Ideal.Quotient.mk (constantIdeal C₀)).comp MvPolynomial.C)
def seedCoordinate (C₀ : ConstantSeeds) (i : Fin 2) : ConstantSeedField C₀ :=
  algebraMap (ConstantSeedRing C₀) (ConstantSeedField C₀)
    (Ideal.Quotient.mk (constantIdeal C₀) (MvPolynomial.X i))
def insertX (C₀ : ConstantSeeds) : (ConstantSeedField C₀)[X] →+* ConstantSeedX C₀ :=
  algebraMap _ _
def insertConstant (C₀ : ConstantSeeds) : ConstantSeedField C₀ →+* ConstantSeedX C₀ :=
  (insertX C₀).comp Polynomial.C
def extendX (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] : FX →+* ConstantSeedX C₀ :=
  IsFractionRing.map (j := Polynomial.mapRingHom (constToSeed C₀))
    (Polynomial.map_injective (constToSeed C₀) (constToSeed C₀).injective)
def seedEquation (C₀ : ConstantSeeds) : Ideal Seeds :=
  Ideal.span {MvPolynomial.map ((algebraMap L[X] FX).comp (Polynomial.C : L →+* L[X])) C₀}
def genericRootMap (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    RootAmbient →+* (ConstantSeedX C₀)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (extendX C₀))
    ![Polynomial.C (insertConstant C₀ (seedCoordinate C₀ 0)),
      Polynomial.C (insertConstant C₀ (seedCoordinate C₀ 1)), Polynomial.X]
structure PrimitiveRoot (C₀ : ConstantSeeds) [Fact (Irreducible C₀)]
    (J : Ideal RootAmbient) (g : ℕ) where
  equation : ((ConstantSeedField C₀)[X])[X]
  primitive : equation.IsPrimitive
  degree : equation.natDegree = g
  irreducible : Irreducible (equation.map (insertX C₀))
  contraction : J = (Ideal.span {equation.map (insertX C₀)}).comap (genericRootMap C₀)
structure CoefficientChart {C₀ : ConstantSeeds} [Fact (Irreducible C₀)]
    {J : Ideal RootAmbient} {g : ℕ} (R : PrimitiveRoot C₀ J g) (n : ℕ) where
  coordinate : Fin n → ConstantSeedField C₀
  scale : (ConstantSeedField C₀)ˣ
  equation : FamilyEquation n
  degree : FamilyDegree equation g
  generic_eq : equation.map
      (Polynomial.mapRingHom (MvPolynomial.eval₂Hom (constToSeed C₀) coordinate)) =
    Polynomial.C (Polynomial.C (scale : ConstantSeedField C₀)) * R.equation
  coordinates_are_coefficients : ∀ i, ∃ j k,
    coordinate i = ((Polynomial.C (Polynomial.C (scale : ConstantSeedField C₀)) *
      R.equation).coeff j).coeff k
  normalized : ∃ ℓ : Fin n → L, (∑ i, constToSeed C₀ (ℓ i) * coordinate i) = 1
abbrev ChartBaseRing (n : ℕ) := MvPolynomial (Fin 2 ⊕ Fin n) FX
abbrev ParameterGeometry (n : ℕ) := MvPolynomial (Fin n) FX
def parameterInclusion (n : ℕ) : ParameterGeometry n →+* ChartBaseRing n :=
  (MvPolynomial.rename Sum.inr).toRingHom
def chartBaseMap {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    ChartBaseRing n →+* ConstantSeedX C₀ :=
  MvPolynomial.eval₂Hom (extendX C₀)
    (Sum.elim (insertConstant C₀ ∘ seedCoordinate C₀) (insertConstant C₀ ∘ A.coordinate))
def chartBase {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) : Ideal (ChartBaseRing n) :=
  RingHom.ker (chartBaseMap A)
def chartRootMap {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    SourceRing n →+* (ConstantSeedX C₀)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (extendX C₀))
    (fun i => i.elim Polynomial.X (Polynomial.C ∘ insertConstant C₀ ∘ A.coordinate))
def chartSource {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) : Ideal (SourceRing n) :=
  (Ideal.span {R.equation.map (insertX C₀)}).comap (chartRootMap A)
def baseMark {n : ℕ} (z : K) (t : Fin n → L) : Fin 2 ⊕ Fin n → FX :=
  Sum.elim ![seedEmbedding z, (seedEmbedding z) ^ p] (fun i => algebraMap L FX (t i))
def baseCut (n : ℕ) : MvPolynomial (Fin 2 ⊕ Fin n) (SliceField n) :=
  (∑ i : Fin n, MvPolynomial.C (sliceVariable (some i)) * MvPolynomial.X (Sum.inr i)) -
    MvPolynomial.C (sliceVariable (n := n) none)
abbrev BaseSection {n : ℕ} (B : Ideal (ChartBaseRing n)) :=
  MvPolynomial (Fin 2 ⊕ Fin n) (SliceField n) ⧸
    (B.map (MvPolynomial.map (algebraMap FX (SliceField n))) ⊔ Ideal.span {baseCut n})
structure BaseHeight {n : ℕ} (B : Ideal (ChartBaseRing n)) (H : ℕ) : Prop where
  dimension : (MvPolynomial.affineHilbertPolynomial B).natDegree ≤ 1
  finite : Module.Finite (SliceField n) (BaseSection B)
  length : Module.finrank (SliceField n) (BaseSection B) ≤ H
end
end K1_14_2_4_1
end
section
namespace K1_14_2_4_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4
open scoped Polynomial BigOperators
private def abscissa : FX := algebraMap L[X] FX Polynomial.X
private def coefficientsAtX (n : ℕ) : (ParameterRing n)[X] →+* ParameterGeometry n :=
  Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C abscissa)
def equationAtX {n : ℕ} (f : FamilyEquation n) : (ParameterGeometry n)[X] :=
  f.map (coefficientsAtX n)
def chartResultant {n : ℕ} (f : FamilyEquation n) (g : ℕ) : ParameterGeometry n :=
  (equationAtX f).resultant (equationAtX f).derivative g (g - 1)
private theorem coefficient_degree {n : ℕ} {f : FamilyEquation n} {g : ℕ}
    (hf : FamilyDegree f g) (j : ℕ) : ((equationAtX f).coeff j).totalDegree ≤ 1 := by
  rw [equationAtX, Polynomial.coeff_map, (f.coeff j).as_sum_range_C_mul_X_pow, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  rw [map_mul, map_pow]
  simp only [coefficientsAtX, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  rw [← map_pow MvPolynomial.C]
  have hm : (MvPolynomial.map (algebraMap L FX) ((f.coeff j).coeff i)).totalDegree ≤
      ((f.coeff j).coeff i).totalDegree := by
    unfold MvPolynomial.totalDegree
    exact Finset.sup_mono (MvPolynomial.support_map_subset (algebraMap L FX) ((f.coeff j).coeff i))
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    rw [MvPolynomial.totalDegree_C, add_zero]
    exact hm.trans (hf.2 j i))
theorem chartResultant_degree {n : ℕ} {f : FamilyEquation n} {g : ℕ}
    (hf : FamilyDegree f g) (hg : 0 < g) : (chartResultant f g).totalDegree ≤ taylorPower g := by
  classical
  let F := equationAtX f
  have hd (i : ℕ) : (F.derivative.coeff i).totalDegree ≤ 1 := by
    have hcast : ((i : ParameterGeometry n) + 1) = MvPolynomial.C ((i : FX) + 1) := by simp
    rw [Polynomial.coeff_derivative, hcast]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C, add_zero] using coefficient_degree hf (i + 1))
  let M := Polynomial.sylvester F F.derivative g (g - 1)
  have hentry (i j : Fin (g + (g - 1))) : (M i j).totalDegree ≤ 1 := by
    cases j using Fin.addCases with
    | left j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hd _
      · simp
    | right j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact coefficient_degree hf _
      · simp
  change M.det.totalDegree ≤ _
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  have hsign : ((Equiv.Perm.sign σ : ℤ) : ParameterGeometry n) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : FX) := by simp
  rw [hsign]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin (g + (g - 1)), 1 := Finset.sum_le_sum (fun i _ => hentry (σ i) i)
    _ = taylorPower g := by simp [taylorPower]; omega
private theorem embed_abscissa (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    extendX C₀ abscissa = insertX C₀ Polynomial.X := by
  unfold extendX abscissa IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertX]
private theorem embed_constant (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (a : L) :
    extendX C₀ (algebraMap L FX a) = insertConstant C₀ (constToSeed C₀ a) := by
  rw [IsScalarTower.algebraMap_apply L L[X] FX]
  unfold extendX IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertConstant, insertX]
private theorem chartEvaluation {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    ((chartBaseMap A).comp (parameterInclusion n)).comp (coefficientsAtX n) =
      (insertX C₀).comp
        (Polynomial.mapRingHom (MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate)) := by
  apply Polynomial.ringHom_ext
  · have hc : ((chartBaseMap A).comp (parameterInclusion n)).comp
        (MvPolynomial.map (algebraMap L FX)) =
        (insertConstant C₀).comp (MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [chartBaseMap, parameterInclusion, embed_constant]
      · intro i
        simp [chartBaseMap, parameterInclusion]
    intro a
    simpa only [RingHom.comp_apply, coefficientsAtX, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, insertConstant] using
      DFunLike.congr_fun hc a
  · simpa [coefficientsAtX, chartBaseMap, parameterInclusion] using embed_abscissa C₀
private theorem generic_separability {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g}
    (R : PrimitiveRoot C₀ J g) (hg : 0 < g) (h8 : g ≤ 8) :
    (R.equation.map (insertX C₀)).Separable := by
  let F := R.equation.map (insertX C₀)
  let : CharP (ConstantSeedX C₀) p :=
    charP_of_injective_ringHom ((extendX C₀).comp seedEmbedding).injective p
  have hdeg : F.natDegree = g :=
    (Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (ConstantSeedField C₀)[X] (ConstantSeedX C₀)) _).trans R.degree
  have hgc : (g : ConstantSeedX C₀) ≠ 0 := by
    intro hz
    have hp := (CharP.cast_eq_zero_iff (ConstantSeedX C₀) p g).mp hz
    exact (not_le_of_gt (h8.trans_lt (by decide : 8 < p))) (Nat.le_of_dvd hg hp)
  refine (Polynomial.separable_iff_derivative_ne_zero R.irreducible).mpr ?_
  intro hd
  have hz := congrArg (fun Q : (ConstantSeedX C₀)[X] => Q.coeff (g - 1)) hd
  have hsucc : g - 1 + 1 = g := Nat.sub_add_cancel hg
  have hcast : (↑(g - 1) + 1 : ConstantSeedX C₀) = (g : ConstantSeedX C₀) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : ConstantSeedX C₀)) hsucc
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, hcast, hsucc] at hz
  change F.coeff g * (g : ConstantSeedX C₀) = 0 at hz
  rw [show F.coeff g = F.leadingCoeff by rw [← hdeg, Polynomial.coeff_natDegree]] at hz
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr R.irreducible.ne_zero) hgc) hz
theorem chartResultant_proper {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) (hg : 0 < g) (h8 : g ≤ 8) :
    parameterInclusion n (chartResultant A.equation g) ∉ chartBase A := by
  let ev := (chartBaseMap A).comp (parameterInclusion n)
  let F := R.equation.map (insertX C₀)
  let a := insertConstant C₀ (A.scale : ConstantSeedField C₀)
  have ha : IsUnit (Polynomial.C a) :=
    (show IsUnit (A.scale : ConstantSeedField C₀) from A.scale.isUnit).map
      (Polynomial.C.comp (insertConstant C₀))
  have hFdeg : F.natDegree = g :=
    (Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (ConstantSeedField C₀)[X] (ConstantSeedX C₀)) _).trans R.degree
  have hG : (equationAtX A.equation).map ev = Polynomial.C a * F := by
    rw [equationAtX, Polynomial.map_map, chartEvaluation A, ← Polynomial.map_map,
      A.generic_eq, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hGdeg : (Polynomial.C a * F).natDegree = g :=
    (Polynomial.natDegree_C_mul (isUnit_iff_ne_zero.mp (Polynomial.isUnit_C.mp ha))).trans hFdeg
  have hsep := (generic_separability R hg h8).unit_mul ha
  have hres := Polynomial.resultant_derivative_ne_zero_of_separable _ hsep
  rw [hGdeg, ← hG, Polynomial.derivative_map, Polynomial.resultant_map_map] at hres
  exact fun h => hres (RingHom.mem_ker.mp h)
private def parameterEval {n : ℕ} (t : Fin n → L) : ParameterGeometry n →+* FX :=
  MvPolynomial.eval (algebraMap L FX ∘ t)
private theorem liftEvaluation {n : ℕ} (t : Fin n → L) :
    (parameterEval t).comp (coefficientsAtX n) =
      (algebraMap L[X] FX).comp (Polynomial.mapRingHom (MvPolynomial.eval t)) := by
  apply Polynomial.ringHom_ext
  · have hc : (parameterEval t).comp (MvPolynomial.map (algebraMap L FX)) =
        (algebraMap L FX).comp (MvPolynomial.eval t) := by
      apply MvPolynomial.ringHom_ext <;> simp [parameterEval]
    intro a
    simp only [RingHom.comp_apply, coefficientsAtX, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C]
    calc
      _ = algebraMap L FX (MvPolynomial.eval t a) := DFunLike.congr_fun hc a
      _ = _ := by rw [IsScalarTower.algebraMap_apply L L[X] FX]; rfl
  · simp [parameterEval, coefficientsAtX, abscissa]
theorem resultant_at_mark {n : ℕ} (f : FamilyEquation n) (g : ℕ) (z : K) (t : Fin n → L) :
    MvPolynomial.aeval (baseMark z t) (parameterInclusion n (chartResultant f g)) =
      parameterEval t (chartResultant f g) := by
  change MvPolynomial.eval (baseMark z t) (MvPolynomial.rename Sum.inr (chartResultant f g)) = _
  rw [MvPolynomial.eval_rename]
  rfl
theorem simple_of_resultant {n : ℕ} {f : FamilyEquation n} {g : ℕ}
    (hf : FamilyDegree f g) (hg : 0 < g) {z : K} {t : Fin n → L} {S : K[X]}
    (hr : (specialize f t).eval (liftPoly S) = 0)
    (hres : MvPolynomial.aeval (baseMark z t) (parameterInclusion n (chartResultant f g)) ≠ 0) :
    (specialize f t).derivative.eval (liftPoly S) ≠ 0 := by
  rw [resultant_at_mark] at hres
  have hmap : (equationAtX f).map (parameterEval t) =
      (specialize f t).map (algebraMap L[X] FX) := by
    rw [equationAtX, specialize, Polynomial.map_map, Polynomial.map_map, liftEvaluation]
  have hdeg : (equationAtX f).natDegree ≤ g := Polynomial.natDegree_map_le.trans hf.1
  have hroot : ((equationAtX f).map (parameterEval t)).eval (atX S) = 0 := by
    rw [hmap, atX, Polynomial.eval_map_apply, hr, map_zero]
  have hsimple := Polynomial.eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero
    (parameterEval t) (equationAtX f) hdeg hg hres _ hroot
  intro h
  apply hsimple
  rw [hmap, Polynomial.derivative_map, atX, Polynomial.eval_map_apply, h, map_zero]
end
end K1_14_2_4_1
end
section
set_option autoImplicit false
namespace K1_14_2_4_3
noncomputable section
open K1_14 K1_14_2_4 MvPolynomial
abbrev extendedIdeal {n : ℕ} (J : Ideal (SourceRing n)) : Ideal (SliceAmbient n) :=
  J.map (MvPolynomial.map (algebraMap FX (SliceField n)))
abbrev ExtendedRing {n : ℕ} (J : Ideal (SourceRing n)) :=
  SliceAmbient n ⧸ extendedIdeal J
abbrev box {n : ℕ} (J : Ideal (SourceRing n)) (u v : ℕ) :
    Submodule (SliceField n) (ExtendedRing J) :=
  quotientBidegreeLE (extendedIdeal J) u v
abbrev cutClass {n : ℕ} (J : Ideal (SourceRing n)) (q : SliceAmbient n) :
    ExtendedRing J :=
  Ideal.Quotient.mk (extendedIdeal J) q
def BoundaryRegular {n : ℕ} (J : Ideal (SourceRing n)) (q : SliceAmbient n)
    (du dv : ℕ) : Prop :=
  ∃ N : ℕ, ∀ u v : ℕ, N ≤ u → N ≤ v →
    (∀ x ∈ box J (u + 1) v, cutClass J q * x ∈ box J (u + du) (v + dv) → x ∈ box J u v) ∧
    (∀ x ∈ box J u (v + 1), cutClass J q * x ∈ box J (u + du) (v + dv) → x ∈ box J u v)
end
end K1_14_2_4_3
end
section
set_option autoImplicit false
namespace K1_14_2_4_3
noncomputable section
open K1_14 K1_14_2_4 MvPolynomial
open scoped TensorProduct
theorem finrank_box_le_extended {n : ℕ} (J : Ideal (SourceRing n)) (u v : ℕ) :
    Module.finrank FX (quotientBidegreeLE J u v) ≤
      Module.finrank (SliceField n) (box J u v) := by
  classical
  let E := SliceField n
  let R := SourceRing n
  let e₀ : E ⊗[FX] R ≃ₐ[E] SliceAmbient n :=
    MvPolynomial.algebraTensorAlgEquiv FX E
  let i : R →+* E ⊗[FX] R :=
    (Algebra.TensorProduct.includeRight (A := E) (R := FX)).toRingHom
  have hmap : e₀.toAlgHom.toRingHom.comp i = MvPolynomial.map (algebraMap FX E) := by
    apply RingHom.ext
    intro p
    change e₀ (1 ⊗ₜ[FX] p) = MvPolynomial.map (algebraMap FX E) p
    simpa only [e₀, one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul FX E 1 p
  let I := J.map i
  have hI : extendedIdeal J = I.map e₀.toAlgHom.toRingHom := by
    change extendedIdeal J = (J.map i).map e₀.toAlgHom.toRingHom
    rw [Ideal.map_map i e₀.toAlgHom.toRingHom, hmap]
  let e₁ : ((E ⊗[FX] R) ⧸ I) ≃ₐ[E] ExtendedRing J :=
    Ideal.quotientEquivAlg I (extendedIdeal J) e₀ hI
  let e : E ⊗[FX] (R ⧸ J) ≃ₐ[E] ExtendedRing J :=
    (Algebra.TensorProduct.tensorQuotientEquiv E R E J).trans e₁
  have he₁ (c : E) (p : R) :
      e₁ (Ideal.Quotient.mk I (c ⊗ₜ[FX] p)) =
        c • Ideal.Quotient.mk (extendedIdeal J) (MvPolynomial.map (algebraMap FX E) p) := by
    change Ideal.Quotient.mk (extendedIdeal J) (e₀ (c ⊗ₜ[FX] p)) = _
    rw [show e₀ (c ⊗ₜ[FX] p) = c • MvPolynomial.map (algebraMap FX E) p from
      MvPolynomial.algebraTensorAlgEquiv_tmul FX E c p]
    exact (Ideal.Quotient.mkₐ E (extendedIdeal J)).toLinearMap.map_smul c _
  let T := quotientBidegreeLE J u v
  let f : E ⊗[FX] T →ₗ[E] ExtendedRing J :=
    e.toLinearMap.comp (TensorProduct.AlgebraTensorModule.lTensor E E T.subtype)
  have hf : Function.Injective f := e.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := E) T.subtype Subtype.val_injective)
  have hbox (z : E ⊗[FX] T) : f z ∈ box J u v := by
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
        obtain ⟨p, hp, hp'⟩ := mem_quotientBidegreeLE.mp x.property
        have hm : MvPolynomial.map (algebraMap FX E) p ∈ restrictBidegree (Fin n) E u v :=
          mem_restrictBidegree.mpr fun m hm =>
            mem_restrictBidegree.mp hp m (MvPolynomial.support_map_subset _ _ hm)
        change e (c ⊗ₜ[FX] (x : R ⧸ J)) ∈ box J u v
        rw [← hp']
        change e₁ (Ideal.Quotient.mk I (c ⊗ₜ[FX] p)) ∈ box J u v
        rw [he₁ c p]
        exact (box J u v).smul_mem c (mem_quotientBidegreeLE.mpr ⟨_, hm, rfl⟩)
    | add x y hx hy =>
        rw [map_add]
        exact (box J u v).add_mem hx hy
  rw [← Module.finrank_baseChange (R := E) (S := FX) (M' := T)]
  exact LinearMap.finrank_le_finrank_of_injective
    (f := f.codRestrict (box J u v) hbox) (fun x y h => hf (congrArg Subtype.val h))
private theorem box_mono {n : ℕ} {J : Ideal (SourceRing n)} {x : ExtendedRing J}
    {u v u' v' : ℕ} (hu : u ≤ u') (hv : v ≤ v') (hx : x ∈ box J u v) :
    x ∈ box J u' v' := by
  obtain ⟨p, hp, rfl⟩ := mem_quotientBidegreeLE.mp hx
  exact mem_quotientBidegreeLE.mpr ⟨p, mem_restrictBidegree_mono hp hu hv, rfl⟩
theorem strict_of_boundaryRegular {n : ℕ} {J : Ideal (SourceRing n)} {q : SliceAmbient n}
    {du dv : ℕ} (h : BoundaryRegular J q du dv) :
    ∃ N : ℕ, ∀ u v : ℕ, N ≤ u → N ≤ v →
      ∀ x : ExtendedRing J, cutClass J q * x ∈ box J (u + du) (v + dv) → x ∈ box J u v := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro u v hu hv x hqx
  have shrink_u (s r : ℕ) (hx : x ∈ box J (u + r) (v + s)) :
      x ∈ box J u (v + s) := by
    induction r with
    | zero => exact hx
    | succ r ih =>
        apply ih
        apply (hN (u + r) (v + s) (by omega) (by omega)).1 x hx
        exact box_mono (by omega) (by omega) hqx
  have shrink_v (s : ℕ) (hx : x ∈ box J u (v + s)) : x ∈ box J u v := by
    induction s with
    | zero => exact hx
    | succ s ih =>
        apply ih
        apply (hN u (v + s) hu (by omega)).2 x hx
        exact box_mono le_rfl (by omega) hqx
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := extendedIdeal J) x
  let r := p.support.sup (fun m => m none)
  let s := p.support.sup (fun m => m.some.degree)
  have hpbox : p ∈ restrictBidegree (Fin n) (SliceField n) (u + r) (v + s) := by
    refine mem_restrictBidegree.mpr fun m hm => ⟨?_, ?_⟩
    · exact (Finset.le_sup (f := fun m => m none) hm).trans (Nat.le_add_left _ _)
    · exact (Finset.le_sup (f := fun m => m.some.degree) hm).trans (Nat.le_add_left _ _)
  exact shrink_v s (shrink_u s r (mem_quotientBidegreeLE.mpr ⟨p, hpbox, hp⟩))
theorem finrank_box_step {n : ℕ} (J : Ideal (SourceRing n)) (q : SliceAmbient n)
    (u v u' v' : ℕ) [Module.Finite (SliceField n) (SectionRing J q)]
    (h : ∀ x : ExtendedRing J, cutClass J q * x ∈ box J u' v' → x ∈ box J u v) :
    Module.finrank (SliceField n) (box J u' v') ≤
      Module.finrank (SliceField n) (box J u v) +
        Module.finrank (SliceField n) (SectionRing J q) := by
  let T := box J u' v'
  let π : T →ₗ[SliceField n] SectionRing J q :=
    (Ideal.Quotient.factorₐ (SliceField n)
      (le_sup_left : extendedIdeal J ≤ extendedIdeal J ⊔ Ideal.span {q})).toLinearMap.domRestrict T
  let ι : LinearMap.ker π →ₗ[SliceField n] ExtendedRing J :=
    T.subtype.comp (LinearMap.ker π).subtype
  let μ : box J u v →ₗ[SliceField n] ExtendedRing J :=
    (LinearMap.mulLeft (SliceField n) (cutClass J q)).domRestrict _
  have hk : LinearMap.range ι ≤ LinearMap.range μ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := extendedIdeal J) z.1.1
    have hz := LinearMap.mem_ker.mp z.2
    change Ideal.Quotient.factor (le_sup_left :
      extendedIdeal J ≤ extendedIdeal J ⊔ Ideal.span {q}) z.1.1 = 0 at hz
    rw [← hp] at hz
    have hm : p ∈ extendedIdeal J ⊔ Ideal.span {q} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hm
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ht
    have he : cutClass J q * cutClass J r = z.1.1 := by
      rw [← hp, ← hst, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hs, zero_add, map_mul]
    have hr : cutClass J r ∈ box J u v := h _ (he.symm ▸ z.1.2)
    exact ⟨⟨cutClass J r, hr⟩, he⟩
  have hi : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hker : Module.finrank (SliceField n) (LinearMap.ker π) ≤
      Module.finrank (SliceField n) (box J u v) :=
    (LinearMap.finrank_range_of_inj hi).symm.le.trans
      ((Submodule.finrank_mono hk).trans μ.finrank_range_le)
  have hrange := Submodule.finrank_le (LinearMap.range π)
  have hrank := π.finrank_range_add_finrank_ker
  change _ + _ = Module.finrank (SliceField n) (box J u' v') at hrank
  omega
end
end K1_14_2_4_3
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_1
noncomputable section
open K1_14 K1_14_2_4 MvPolynomial
abbrev HomVar (n : ℕ) := Option (Fin n) ⊕ Bool
abbrev HomRing (n : ℕ) (k : Type) [CommRing k] := MvPolynomial (HomVar n) k
def pad {n : ℕ} (side : Bool) : HomVar n := .inr side
def group {n : ℕ} : HomVar n → Bool
  | .inl none => false
  | .inl (some _) => true
  | .inr side => side
def unitDegree (side : Bool) : ℕ × ℕ := if side then (0, 1) else (1, 0)
def biWeight (n : ℕ) (i : HomVar n) : ℕ × ℕ := unitDegree (group i)
def paramWeight (n : ℕ) (i : HomVar n) : ℕ := (biWeight n i).2
def paramVar {n : ℕ} : Option (Fin n) → HomVar n
  | none => pad true
  | some j => .inl (some j)
abbrev Bihomogeneous {n : ℕ} {k : Type} [CommRing k]
    (p : HomRing n k) (d : ℕ × ℕ) : Prop :=
  p.IsWeightedHomogeneous (biWeight n) d
def dehom {n : ℕ} {k : Type} [CommRing k] :
    HomRing n k →ₐ[k] MvPolynomial (Option (Fin n)) k :=
  aeval (Sum.elim MvPolynomial.X fun _ => 1)
def dehomClass {n : ℕ} {k : Type} [CommRing k]
    (I : Ideal (MvPolynomial (Option (Fin n)) k)) :
    HomRing n k →ₐ[k] (MvPolynomial (Option (Fin n)) k ⧸ I) :=
  (Ideal.Quotient.mkₐ k I).comp dehom
def gradedEval {n : ℕ} {k : Type} [CommRing k]
    (I : Ideal (MvPolynomial (Option (Fin n)) k)) :
    HomRing n k →ₐ[k] MvPolynomial Bool (MvPolynomial (Option (Fin n)) k ⧸ I) :=
  aeval fun i => MvPolynomial.C (dehomClass I (MvPolynomial.X i)) * MvPolynomial.X (group i)
def homIdeal {n : ℕ} {k : Type} [CommRing k]
    (I : Ideal (MvPolynomial (Option (Fin n)) k)) : Ideal (HomRing n k) :=
  RingHom.ker (gradedEval I).toRingHom
def boundaryIdeal {n : ℕ} {k : Type} [CommRing k]
    (I : Ideal (MvPolynomial (Option (Fin n)) k)) (side : Bool) : Ideal (HomRing n k) :=
  homIdeal I ⊔ Ideal.span {MvPolynomial.X (pad side)}
def extendHomIdeal {n : ℕ} (I : Ideal (HomRing n FX)) : Ideal (HomRing n (SliceField n)) :=
  I.map (MvPolynomial.map (algebraMap FX (SliceField n)))
def homCut (n : ℕ) : HomRing n (SliceField n) :=
  (∑ j : Fin n, MvPolynomial.C (sliceVariable (some j)) * MvPolynomial.X (paramVar (some j))) -
    MvPolynomial.C (sliceVariable (n := n) none) * MvPolynomial.X (paramVar none)
def ParamGraded {n : ℕ} {k : Type} [CommRing k] (I : Ideal (HomRing n k)) : Prop :=
  ∀ p ∈ I, ∀ v : ℕ, weightedHomogeneousComponent (paramWeight n) v p ∈ I
end
end K1_14_2_4_3_1
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_1
noncomputable section
open K1_14 K1_14_2_4 K1_14_2_4_3 MvPolynomial
open scoped TensorProduct
set_option maxHeartbeats 600000 in
private theorem homIdeal_map {n : ℕ} {k E : Type} [Field k] [Field E]
    [Algebra k E] [Module.Flat k E]
    (J : Ideal (MvPolynomial (Option (Fin n)) k)) :
    homIdeal (J.map (MvPolynomial.map (algebraMap k E))) =
      (homIdeal J).map (MvPolynomial.map (algebraMap k E)) := by
  classical
  let R := MvPolynomial (Option (Fin n)) k
  let R' := MvPolynomial (Option (Fin n)) E
  let h : R →+* R' := MvPolynomial.map (algebraMap k E)
  let J' := J.map h
  let A := R ⧸ J
  let B := R' ⧸ J'
  let er : E ⊗[k] R ≃ₐ[E] R' := MvPolynomial.algebraTensorAlgEquiv k E
  let ir : R →+* E ⊗[k] R :=
    (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom
  have hir : er.toAlgHom.toRingHom.comp ir = h := by
    apply RingHom.ext
    intro p
    change er (1 ⊗ₜ[k] p) = h p
    simpa only [er, h, one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul k E 1 p
  have hI : J' = (J.map ir).map er.toAlgHom.toRingHom := by
    rw [Ideal.map_map, hir]
  let e₁ : ((E ⊗[k] R) ⧸ J.map ir) ≃ₐ[E] B :=
    Ideal.quotientEquivAlg (J.map ir) J' er hI
  let ec : E ⊗[k] A ≃ₐ[E] B :=
    (Algebra.TensorProduct.tensorQuotientEquiv E R E J).trans e₁
  have hec (p : R) :
      ec (1 ⊗ₜ[k] Ideal.Quotient.mk J p) = Ideal.Quotient.mk J' (h p) := by
    change Ideal.Quotient.mk J' (er (1 ⊗ₜ[k] p)) = _
    exact congrArg (Ideal.Quotient.mk J') (DFunLike.congr_fun hir p)
  let j : A →ₐ[k] B :=
    (ec.toAlgHom.restrictScalars k).comp (Algebra.TensorProduct.includeRight (A := E))
  let hₐ : HomRing n k →ₐ[k] HomRing n E :=
    MvPolynomial.mapAlgHom (Algebra.ofId k E)
  let f : HomRing n k →ₐ[k] MvPolynomial Bool A := gradedEval J
  let f' : HomRing n E →ₐ[E] MvPolynomial Bool B := gradedEval J'
  have hj : (MvPolynomial.mapAlgHom (σ := Bool) j).comp f =
      (f'.restrictScalars k).comp hₐ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i =>
        simp only [AlgHom.comp_apply, f, f', gradedEval, aeval_X, dehomClass, dehom,
          Sum.elim_inl, Ideal.Quotient.mkₐ_eq_mk, mapAlgHom_apply, hₐ, Algebra.toRingHom_ofId,
          MvPolynomial.map_X, map_mul, MvPolynomial.map_C, AlgHom.restrictScalars_apply]
        change MvPolynomial.C (ec (1 ⊗ₜ[k] Ideal.Quotient.mk J (MvPolynomial.X i))) * _ = _
        have hX : h (MvPolynomial.X i) = (MvPolynomial.X i : R') :=
          MvPolynomial.map_X (algebraMap k E) i
        rw [hec, hX]
    | inr side =>
        simp [f, f', gradedEval, dehomClass, dehom, hₐ, mapAlgHom_apply]
  let es : E ⊗[k] HomRing n k ≃ₐ[E] HomRing n E :=
    MvPolynomial.algebraTensorAlgEquiv k E
  have hes_tmul (a : E) (p : HomRing n k) :
      es (a ⊗ₜ[k] p) = a • hₐ p := by
    change MvPolynomial.algebraTensorAlgEquiv k E (a ⊗ₜ[k] p) =
      a • MvPolynomial.map (algebraMap k E) p
    exact MvPolynomial.algebraTensorAlgEquiv_tmul k E a p
  let et : E ⊗[k] MvPolynomial Bool A ≃ₐ[E] MvPolynomial Bool B :=
    MvPolynomial.rTensorAlgEquiv.trans (MvPolynomial.mapAlgEquiv Bool ec)
  have het (a : E) (p : MvPolynomial Bool A) :
      et (a ⊗ₜ[k] p) = a • MvPolynomial.map j.toRingHom p := by
    ext d
    simp only [et, AlgEquiv.trans_apply, mapAlgEquiv_apply, coeff_map,
      coeff_rTensorAlgEquiv_tmul, coeff_smul]
    change ec (a ⊗ₜ[k] p.coeff d) = a • ec (1 ⊗ₜ[k] p.coeff d)
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
  let tf := Algebra.TensorProduct.map (AlgHom.id k E) f
  have hcomp : f'.toRingHom.comp es.toAlgHom.toRingHom =
      et.toAlgHom.toRingHom.comp tf.toRingHom := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a p =>
        change f' (es (a ⊗ₜ[k] p)) = et (a ⊗ₜ[k] f p)
        rw [hes_tmul, map_smul, het]
        exact congrArg (a • ·) (DFunLike.congr_fun hj p).symm
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy]
  have hker : (homIdeal J').comap es.toAlgHom.toRingHom =
      (homIdeal J).map (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom := by
    rw [homIdeal, RingHom.comap_ker, hcomp]
    change RingHom.ker (et.toRingEquiv.toRingHom.comp tf.toRingHom) = _
    rw [RingHom.ker_equiv_comp]
    rw [← Submodule.restrictScalars_inj k]
    change LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor k E f.toLinearMap) = _
    have hk := Module.Flat.ker_lTensor_eq (R := k) k E
      (N := HomRing n k) (P := MvPolynomial Bool A) f.toLinearMap
    rw [hk]
    exact TensorProduct.AlgebraTensorModule.range_lTensor_idealMap (R := k) E k
      (RingHom.ker f.toRingHom)
  have hes : es.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := E) (R := k)).toRingHom = hₐ.toRingHom := by
    apply RingHom.ext
    intro p
    change es (1 ⊗ₜ[k] p) = hₐ p
    simpa only [one_smul] using hes_tmul 1 p
  calc
    homIdeal J' =
        ((homIdeal J').comap es.toAlgHom.toRingHom).map es.toAlgHom.toRingHom :=
      (Ideal.map_comap_of_surjective es.toAlgHom.toRingHom es.surjective _).symm
    _ = (homIdeal J).map hₐ.toRingHom := by
      rw [hker, Ideal.map_map, hes]
theorem homIdeal_extend {n : ℕ} (J : Ideal (SourceRing n)) :
    homIdeal (extendedIdeal J) = extendHomIdeal (homIdeal J) := by
  have : Module.Free FX (SliceField n) := Module.Free.of_divisionRing FX (SliceField n)
  have : Module.Flat FX (SliceField n) := Module.Flat.of_free
  exact homIdeal_map (k := FX) (E := SliceField n) J
end
end K1_14_2_4_3_1
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_1
noncomputable section
open MvPolynomial
private theorem weight_param {n : ℕ} (d : HomVar n →₀ ℕ) :
    Finsupp.weight (paramWeight n) d = ∑ i : Option (Fin n), d (paramVar i) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_sum_type, Fintype.sum_option,
    paramWeight, biWeight, unitDegree, group, paramVar, pad, Nat.add_comm]
private theorem bound_one_generator {n : ℕ} {k : Type} [Field k]
    (I : Ideal (HomRing n k)) (hI : ParamGraded I) (g : HomRing n k)
    (hg : ∀ i : Option (Fin n), ∃ e : ℕ, MvPolynomial.X (paramVar i) ^ e * g ∈ I) :
    ∃ B : ℕ, ∀ (v : ℕ) (a : HomRing n k), B ≤ v →
      weightedHomogeneousComponent (paramWeight n) v (a * g) ∈ I := by
  classical
  choose e he using hg
  refine ⟨(∑ i, e i) + weightedTotalDegree (paramWeight n) g + 1, ?_⟩
  intro v a hv
  induction a using MvPolynomial.induction_on' with
  | monomial d c =>
      by_cases hd : ∃ i, e i ≤ d (paramVar i)
      · obtain ⟨i, hi⟩ := hd
        have hsingle : Finsupp.single (paramVar i) (e i) ≤ d :=
          Finsupp.single_le_iff.mpr hi
        have hfactor : monomial d c =
            monomial (d - Finsupp.single (paramVar i) (e i)) c *
              MvPolynomial.X (paramVar i) ^ e i := by
          rw [← monomial_add_single, tsub_add_cancel_of_le hsingle]
        apply hI
        rw [hfactor, mul_assoc]
        exact I.mul_mem_left _ (he i)
      · by_cases hc : c = 0
        · simp [hc]
        have hw : Finsupp.weight (paramWeight n) d ≤ ∑ i, e i := by
          rw [weight_param]
          exact Finset.sum_le_sum fun i _ => Nat.le_of_lt (Nat.lt_of_not_ge (fun hi => hd ⟨i, hi⟩))
        have hdeg : weightedTotalDegree (paramWeight n) (monomial d c * g) < v := by
          apply (weightedTotalDegree_mul_le _ _ _).trans_lt
          rw [weightedTotalDegree_monomial _ _ _ hc]
          omega
        rw [weightedHomogeneousComponent_eq_zero v _ hdeg]
        exact I.zero_mem
  | add a b ha hb =>
      rw [add_mul, map_add]
      exact I.add_mem ha hb
theorem large_parameter_degree {n : ℕ} {k : Type} [Field k]
    (I : Ideal (HomRing n k)) (q : HomRing n k) (hI : ParamGraded I)
    (hlocal : ∀ p : HomRing n k, q * p ∈ I →
      ∀ i : Option (Fin n), ∃ e : ℕ, MvPolynomial.X (paramVar i) ^ e * p ∈ I) :
    ∃ N : ℕ, ∀ (v : ℕ) (p : HomRing n k), N ≤ v →
      p.IsWeightedHomogeneous (paramWeight n) v → q * p ∈ I → p ∈ I := by
  classical
  let T := I.colon (Ideal.span {q})
  obtain ⟨s, hs⟩ := T.fg_of_isNoetherianRing
  have hgen (g : s) :
      ∃ B : ℕ, ∀ (v : ℕ) (a : HomRing n k), B ≤ v →
        weightedHomogeneousComponent (paramWeight n) v (a * (g : HomRing n k)) ∈ I := by
    apply bound_one_generator I hI
    apply hlocal
    rw [mul_comm, ← Ideal.mem_colon_span_singleton]
    change (g : HomRing n k) ∈ T
    rw [← hs]
    exact Submodule.subset_span g.property
  choose B hB using hgen
  refine ⟨s.attach.sup B, ?_⟩
  intro v p hv hhom hqp
  have hp : p ∈ Submodule.span (HomRing n k) (s : Set (HomRing n k)) := by
    change p ∈ Ideal.span (s : Set (HomRing n k))
    rw [hs]
    apply Ideal.mem_colon_span_singleton.mpr
    simpa only [mul_comm] using hqp
  have H : ∀ a : HomRing n k, weightedHomogeneousComponent (paramWeight n) v (a * p) ∈ I := by
    refine Submodule.span_induction (p := fun y _ => ∀ a : HomRing n k,
      weightedHomogeneousComponent (paramWeight n) v (a * y) ∈ I) ?_ ?_ ?_ ?_ hp
    · intro g hg a
      let i : s := ⟨g, hg⟩
      exact hB i v a ((Finset.le_sup (f := B) (s.mem_attach i)).trans hv)
    · intro a
      simp
    · intro x y _ _ hx hy a
      rw [mul_add, map_add]
      exact I.add_mem (hx a) (hy a)
    · intro r x _ hx a
      simpa only [smul_eq_mul, mul_assoc] using hx (a * r)
  rw [← weightedHomogeneousComponent_eq_self hhom]
  simpa only [one_mul] using H 1
end
end K1_14_2_4_3_1
end
section
namespace K1_14_6
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
def taylorPower (d : ℕ) : ℕ := 2 * d - 1
def ordinateBound (d e : ℕ) : ℕ := 1 + taylorPower d * (e - 1)
def parameterBound (d b : ℕ) : ℕ := taylorPower d * b
def mixedDegree (d e b : ℕ) : ℕ :=
  e * (parameterBound d b)^2 + 2 * b * ordinateBound d e * parameterBound d b
abbrev Biform := MvPolynomial (Option (Fin 2)) FX
def rootPoint (z : K) (S : K[X]) : Option (Fin 2) → FX
  | none => atX S
  | some i => (![seedEmbedding z, (seedEmbedding z)^p] : Fin 2 → FX) i
structure TaylorChart (d e b : ℕ) where
  denominator : Biform
  numerator : K → Biform
  denominator_bound : denominator ∈
    MvPolynomial.restrictBidegree (Fin 2) FX (ordinateBound d e) (parameterBound d b)
  numerator_bound : ∀ x, numerator x ∈
    MvPolynomial.restrictBidegree (Fin 2) FX (ordinateBound d e) (parameterBound d b)
def TaylorChart.Recovers {d e b} (C : TaylorChart d e b) (z : K) (S : K[X]) : Prop :=
  let ev := MvPolynomial.eval (rootPoint z S)
  ev C.denominator ≠ 0 ∧
    ∀ x : K, ev (C.numerator x) = ev C.denominator * seedEmbedding (S.eval x)
abbrev ClosedField := AlgebraicClosure FX
abbrev ChartVariables (d e b : ℕ) :=
  ↥(MvPolynomial.bidegreeExponents (Fin 2) (ordinateBound d e) (parameterBound d b))
abbrev LinearRing (d e b : ℕ) := MvPolynomial (ChartVariables d e b) ClosedField
structure LinearCover (T : Finset K) (s : K → K[X]) (d e b : ℕ) where
  point : K → ChartVariables d e b → ClosedField
  injective : Set.InjOn point (T : Set K)
  cut : K → K → LinearRing d e b
  cut_degree : ∀ x a, (cut x a).totalDegree ≤ 1
  cut_eval : ∀ γ ∈ T, ∀ x a, MvPolynomial.aeval (point γ) (cut x a) = 0 ↔ (s γ).eval x = a
  components : Finset (Ideal (LinearRing d e b))
  is_prime : ∀ P ∈ components, P.IsPrime
  dimension : ∀ P ∈ components, (MvPolynomial.affineHilbertPolynomial P).natDegree = 2
  covers : ∀ γ ∈ T, ∃ P ∈ components, point γ ∈ MvPolynomial.zeroLocus ClosedField P
  component_count : components.card ≤ e
  degree_sum : ∑ P ∈ components, MvPolynomial.affineDegree P ≤ (mixedDegree d e b : ℚ)
structure FixedWord (w : I → K) (T : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ γ ∈ T, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ B : Finset I, 180265 ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
end
end K1_14_6
end
section
namespace K1_14_6
noncomputable section
open Polynomial Finset K1 ProximityPrize.Benchmark
open scoped BigOperators
private theorem occupancy {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (marks : Finset α) (nodes : Finset ι) (B : α → Finset ι) (x t cap : ℕ)
    (hB : ∀ a ∈ marks, B a ⊆ nodes ∧ (B a).card = x)
    (hpair : ∀ a ∈ marks, ∀ b ∈ marks, a ≠ b → (B a ∩ B b).card ≤ t)
    (hocc : ∀ i ∈ nodes, (marks.filter fun a => i ∈ B a).card ≤ cap) :
    (marks.card * x)^2 ≤ nodes.card * (marks.card * (x + (marks.card - 1)*t)) ∧
      marks.card * x ≤ nodes.card * cap := by
  classical
  let occ (i : ι) := (marks.filter fun a => i ∈ B a).card
  have section_eq (V : Finset ι) (hV : V ⊆ nodes) :
      (nodes.filter fun i => i ∈ V) = V := by
    ext i
    exact mem_filter.trans ⟨And.right, fun hi => ⟨hV hi, hi⟩⟩
  have first : ∑ i ∈ nodes, occ i = marks.card * x := by
    calc
      _ = ∑ a ∈ marks, (B a).card := by
        simp only [occ, card_filter]
        rw [sum_comm]
        refine sum_congr rfl fun a ha => ?_
        rw [sum_boole, Nat.cast_id, section_eq _ (hB a ha).1]
      _ = _ := by rw [sum_congr rfl (fun a ha => (hB a ha).2), sum_const, smul_eq_mul]
  have second : ∑ i ∈ nodes, occ i ^ 2 =
      ∑ a ∈ marks, ∑ b ∈ marks, (B a ∩ B b).card := by
    simp only [occ, sq, card_filter]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a ha => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    have identity (i : ι) :
        (if i ∈ B a then 1 else 0 : ℕ) * (if i ∈ B b then 1 else 0) =
          if i ∈ B a ∩ B b then 1 else 0 := by
      by_cases h₁ : i ∈ B a <;> by_cases h₂ : i ∈ B b <;> simp [h₁, h₂]
    simp_rw [identity]
    rw [sum_boole, Nat.cast_id, section_eq _ (inter_subset_left.trans (hB a ha).1)]
  have row (a : α) (ha : a ∈ marks) :
      ∑ b ∈ marks, (B a ∩ B b).card ≤ x + (marks.card - 1) * t := by
    rw [← add_sum_erase marks _ ha, inter_self, (hB a ha).2]
    refine Nat.add_le_add_left ?_ _
    calc
      _ ≤ ∑ b ∈ marks.erase a, t := sum_le_sum fun b hb =>
        hpair a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm
      _ = _ := by rw [sum_const, card_erase_of_mem ha, smul_eq_mul]
  have second_le : ∑ i ∈ nodes, occ i ^ 2 ≤ marks.card * (x + (marks.card - 1) * t) := by
    rw [second]
    exact (sum_le_sum row).trans_eq (by rw [sum_const, smul_eq_mul])
  have cs := sq_sum_le_card_mul_sum_sq (s := nodes) (f := occ)
  rw [first] at cs
  refine ⟨cs.trans (Nat.mul_le_mul_left _ second_le), ?_⟩
  rw [← first, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum hocc
private theorem incidence_arithmetic (m x gap cap : ℕ)
    (hm : 0 < m) (hg : 0 < gap) (hx : gap ≤ x)
    (hsecond : (m*x)^2 ≤ (x+81879) * (m * (x + (m-1)*(x-gap))))
    (hfirst : m*x ≤ (x+81879)*cap) :
    gap*m ≤ 81879*cap + gap := by
  have hcancel : m*x^2 ≤ (x+81879) * (x + (m-1)*(x-gap)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _ = (m*x)^2 := by ring
      _ ≤ _ := hsecond
      _ = _ := by ring
  have hM : ((m - 1 : ℕ) : ℤ) = (m : ℤ)-1 := Int.ofNat_sub (by omega)
  have hX : ((x - gap : ℕ) : ℤ) = (x : ℤ)-gap := Int.ofNat_sub hx
  have hcancelZ := Int.ofNat_le.mpr hcancel
  push_cast [hM, hX] at hcancelZ
  have hfirstZ := Int.ofNat_le.mpr hfirst
  push_cast at hfirstZ
  have secondZ : ((m : ℤ)*81879 - ((m : ℤ)-1)*gap)*x ≥
      ((m : ℤ)-1)*81879*gap := by
    nlinarith only [hcancelZ]
  have firstZ : ((m : ℤ)-(cap : ℤ))*x ≤ (cap : ℤ)*81879 := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ : (81879 : ℤ)*cap + gap < (gap : ℤ)*m := by exact_mod_cast h
  have hbad : (cap : ℤ)*81879 < ((m : ℤ)-1)*gap := by nlinarith only [hbadZ]
  have hxpos : 0 < (x : ℤ) := by omega
  have cmp : (m : ℤ)*81879 - ((m : ℤ)-1)*gap < ((m : ℤ)-(cap : ℤ))*81879 := by
    linarith only [hbad]
  have left := mul_lt_mul_of_pos_right cmp hxpos
  have right := mul_le_mul_of_nonneg_right firstZ (by norm_num : (0 : ℤ) ≤ 81879)
  have impossible := secondZ.trans_lt (left.trans_le (show
      ((m : ℤ)-(cap : ℤ))*81879*x ≤ (cap : ℤ)*81879*81879 from by
        convert right using 1
        ring))
  have bigger := mul_lt_mul_of_pos_right hbad (by norm_num : (0 : ℤ) < 81879)
  nlinarith only [impossible, bigger]
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < 180265) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (180265 - d) * T.card ≤ 81879 * cap + (180265 - d) := by
  classical
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (180265 - d) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ T, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ T) : 180265 ≤ (hits γ).card := by
    obtain ⟨B, hB, hval⟩ := h.hits γ hγ
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hval i hi⟩)
  have pair_count (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ d := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    change ((s a) - (s b)).eval (node i) = 0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ d :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := 180265 - common.card
  let t := d - common.card
  have ht : t = x - (180265 - d) := by dsimp [t, x]; omega
  have hx : 180265 - d ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + 81879 := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    dsimp [x]
    omega
  have exists_trim (γ : K) : ∃ B : Finset I, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic _ _ _ _ (by omega) (by omega) hx second first
end
end K1_14_6
end
section
namespace K1_14_2_4
noncomputable section
open K1 K1_14 K1_14_2 Polynomial MvPolynomial Finset
open scoped BigOperators
def c1 : Prop :=
  ∀ (T : Finset K) (z : K → K) (s : K → K[X]) (J : Ideal RootAmbient) (g H : ℕ),
    0 < g → g ≤ 8 → SmallRootCurve J g H → Set.InjOn z (T : Set K) →
    (∀ γ ∈ T, OnRoot J (z γ) (s γ)) →
    ∃ U ⊆ T, (T \ U).card ≤ taylorPower g * H ∧
      ∃ n : ℕ, Nonempty (RegularChart U s g H n)
def c2 : Prop :=
  ∀ (n d g : ℕ), 0 < d → d < p → 0 < g →
    ∀ f : FamilyEquation n, FamilyDegree f g →
    ∃ C : TaylorForms n (ordinateBound d g) (taylorPower d),
      ∀ (t : Fin n → L) (S : K[X]), S.natDegree ≤ d →
        (specialize f t).eval (liftPoly S) = 0 →
        (specialize f t).derivative.eval (liftPoly S) ≠ 0 → C.Recovers t S
def c3 : Prop :=
  ∀ (n a b Dparam Dy : ℕ), 0 < a → 0 < b →
    ∀ J : Ideal (SourceRing n), J.IsPrime →
      (affineHilbertPolynomial J).natDegree = 1 → SliceBounds J Dparam Dy →
      affineDegree (linearIdeal a b J) ≤ ((b * Dparam + a * Dy : ℕ) : ℚ)
private theorem proper_section_card {σ : Type} [Finite σ]
    {P : Ideal (MvPolynomial σ FX)} [P.IsPrime]
    (B : Finset K) (point : K → σ → FX) (hinj : Set.InjOn point (B : Set K))
    {q : MvPolynomial σ FX} (hq : q ∉ P) (hlinear : q.totalDegree ≤ 1)
    (hpoints : ∀ γ ∈ B, point γ ∈ zeroLocus FX (P ⊔ Ideal.span {q}))
    {D : ℕ} (hdim : (affineHilbertPolynomial P).natDegree ≤ 1)
    (hdeg : (affineHilbertPolynomial P).natDegree = 1 → affineDegree P ≤ (D : ℚ)) :
    B.card ≤ D := by
  classical
  let comps := (P ⊔ Ideal.span {q}).minimalPrimesFinset
  let slice (Q : Ideal (MvPolynomial σ FX)) := B.filter fun γ => point γ ∈ zeroLocus FX Q
  have cover (γ : K) (hγ : γ ∈ B) : ∃ Q ∈ comps, γ ∈ slice Q := by
    obtain ⟨Q, hQ, hγQ⟩ :=
      exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ (hpoints γ hγ) (by simp)
    exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  have dim (Q : Ideal (MvPolynomial σ FX)) (hQ : Q ∈ comps) :
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree :=
    principalCut_natDegree_affineHilbertPolynomial_add_one hq (Ideal.mem_minimalPrimesFinset.mp hQ)
  by_cases hcurve : (affineHilbertPolynomial P).natDegree = 1
  · have local_count (Q : Ideal (MvPolynomial σ FX)) (hQ : Q ∈ comps) :
        ((slice Q).card : ℚ) ≤ affineDegree Q := by
      obtain ⟨hfinite, hn⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := FX) Q
        (by have := dim Q hQ; omega)
      let im := (slice Q).image point
      have hsub : (im : Set _) ⊆ zeroLocus FX Q := by
        intro x hx
        obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp hγ).2
      have h := Set.ncard_le_ncard hsub hfinite
      rw [Set.ncard_coe_finset, card_image_of_injOn (hinj.mono (filter_subset _ _))] at h
      exact (Nat.cast_le.mpr h).trans hn
    have hsum : B.card ≤ ∑ Q ∈ comps, (slice Q).card :=
      (card_le_card fun γ hγ => mem_biUnion.mpr (cover γ hγ)).trans card_biUnion_le
    have hsumQ : (B.card : ℚ) ≤ ∑ Q ∈ comps, ((slice Q).card : ℚ) := by exact_mod_cast hsum
    have hbudget : (∑ Q ∈ comps, affineDegree Q) ≤ affineDegree P := by
      simpa only [comps, Nat.cast_one, one_mul] using
        principalCut_sum_affineDegree_minimalPrimes_le hq hlinear
    exact_mod_cast hsumQ.trans ((sum_le_sum local_count).trans (hbudget.trans (hdeg hcurve)))
  · have hB : B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨Q, hQ, _⟩ := cover γ hγ
      have := dim Q hQ
      omega
    simp [hB]
private theorem regular_count {n U s g H w} (A : RegularChart U s g H n)
    (hw : K1_14_6.FixedWord w U s endpointDegree)
    (C : TaylorForms n (ordinateBound endpointDegree g) (taylorPower endpointDegree))
    (hrec : ∀ γ ∈ U, C.Recovers (A.parameter γ) (s γ)) (hdegree : c3) :
    (U.card : ℚ) ≤
      (11697 / 6520 : ℚ) * ((taylorPower endpointDegree * (g * H) +
        ordinateBound endpointDegree g * H : ℕ) : ℚ) + 1 := by
  classical
  let a := ordinateBound endpointDegree g
  let b := taylorPower endpointDegree
  let D := b * (g * H) + a * H
  have ha : 0 < a := by simp [a, ordinateBound]
  have hb : 0 < b := by decide
  let P := linearIdeal a b A.source
  let M := bidegreeMap (Fin n) FX a b
  let v (γ : K) := markedPoint (A.parameter γ) (s γ)
  let point (γ : K) := monomialPoint (bidegreeExponents (Fin n) a b) (v γ)
  have hP : P.IsPrime := A.source_prime.comap M
  let _ : P.IsPrime := hP
  have hdim_eq : (affineHilbertPolynomial P).natDegree =
      (affineHilbertPolynomial A.source).natDegree :=
    natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb _
  have hdim := hdim_eq.trans_le A.source_dim
  have hdeg (h : (affineHilbertPolynomial P).natDegree = 1) : affineDegree P ≤ (D : ℚ) :=
    hdegree n a b (g * H) H ha hb A.source A.source_prime (hdim_eq.symm.trans h) A.slices
  have eval_linear (γ : K) (F : LinearRing n a b) :
      MvPolynomial.aeval (point γ) F = MvPolynomial.aeval (v γ) (M F) := by
    rw [show M = monomialMap FX (bidegreeExponents (Fin n) a b) from
      bidegreeMap_eq_monomialMap a b]
    exact aeval_monomialPoint _ _
  have hpoints (γ : K) (hγ : γ ∈ U) : point γ ∈ zeroLocus FX P := by
    intro F hF
    rw [eval_linear]
    exact A.lies_on γ hγ _ hF
  have hinj : Set.InjOn point (U : Set K) := by
    intro γ hγ η hη heq
    have hv := (monomialPoint_injective (fun i =>
      single_mem_bidegreeExponents ha hb i) : Function.Injective
      (monomialPoint (E := FX) (bidegreeExponents (Fin n) a b))) heq
    exact hw.distinct hγ hη (Polynomial.map_injective _ (algebraMap K L).injective
      (IsFractionRing.injective L[X] FX (congrFun hv none)))
  have hsection (i : I) (hmiss : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D := by
    let x := node i
    let y := w i
    let q := C.numerator x - MvPolynomial.C (seedEmbedding y) * C.denominator
    have hq : q ∈ restrictBidegree (Fin n) FX a b := by
      refine Submodule.sub_mem _ (C.numerator_bound x) ?_
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ C.denominator_bound
    let Q := bidegreeLift q hq
    have hcut (γ : K) (hγ : γ ∈ U) :
        MvPolynomial.aeval (point γ) Q = 0 ↔ (s γ).eval x = y := by
      have hr := hrec γ hγ
      change MvPolynomial.aeval (v γ) C.denominator ≠ 0 ∧
        (∀ x, MvPolynomial.aeval (v γ) (C.numerator x) =
          MvPolynomial.aeval (v γ) C.denominator * seedEmbedding ((s γ).eval x)) at hr
      rw [eval_linear, show M Q = q from bidegreeMap_bidegreeLift q hq]
      dsimp only [q]
      rw [map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, hr.2 x,
        sub_eq_zero, mul_comm (seedEmbedding y), mul_right_inj' hr.1]
      exact seedEmbedding.injective.eq_iff
    have hproper : Q ∉ P := by
      obtain ⟨γ, hγ, hγmiss⟩ := hmiss
      exact fun hQ => hγmiss ((hcut γ hγ).mp (hpoints γ hγ Q hQ))
    refine proper_section_card _ point (hinj.mono (filter_subset _ _)) hproper
      (totalDegree_bidegreeLift_le_one q hq) (fun γ hγ => ?_) hdim hdeg
    obtain ⟨hγU, hγhit⟩ := mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU, (hcut γ hγU).mpr hγhit⟩
  have hcount := K1_14_6.section_capacity hw (by decide) D hsection
  change 45640 * U.card ≤ 81879 * D + 45640 at hcount
  have hcountQ : (45640 : ℚ) * (U.card : ℚ) ≤ 81879 * (D : ℚ) + 45640 := by
    exact_mod_cast hcount
  change (U.card : ℚ) ≤ (11697 / 6520 : ℚ) * (D : ℚ) + 1
  linarith only [hcountQ]
set_option maxHeartbeats 800000 in
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_14_2.c4 := by
  intro u del M Γ F hM T hT J g H hg h8 hcurve hmarks
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨U, hU, hexc, n, ⟨A⟩⟩ :=
    h1 T M.label F.scalar J g H hg h8 hcurve hlabel hmarks
  have hw : K1_14_6.FixedWord M.word U F.scalar endpointDegree := by
    refine ⟨F.distinct.mono (hU.trans hT), ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT (hU hγ))).scalar_degree with hzero | hd
      · simp [hzero]
      · have hc : ((F.scalar γ).natDegree : ℤ) ≤ (endpointDegree : ℤ) := by
          change ((F.scalar γ).natDegree : ℤ) ≤ 134625
          omega
        exact_mod_cast hc
    · intro γ hγ
      let m := F.mark γ (hT (hU hγ))
      exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
  obtain ⟨C, hreconstruct⟩ :=
    h2 n endpointDegree g (by decide) (by decide) hg A.equation A.equation_degree
  have hregular := regular_count A hw C
    (fun γ hγ => hreconstruct _ _ (hw.degree γ hγ) (A.root γ hγ) (A.simple γ hγ)) h3
  let b := taylorPower endpointDegree
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hmixed : b * (g * H) + ordinateBound endpointDegree g * H =
      (b * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [ordinateBound, b]
    ring
  rw [hmixed] at hregular
  have hcast : (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
    unfold taylorPower
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hgQ : (1 : ℚ) ≤ (g : ℚ) := by exact_mod_cast hg
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ) + (U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ ((taylorPower g * H : ℕ) : ℚ) +
        ((11697 / 6520 : ℚ) * (((b * taylorPower g + 1) * H : ℕ) : ℚ) + 1) :=
      add_le_add (Nat.cast_le.mpr hexc) hregular
    _ ≤ ((taylorPower g * H : ℕ) : ℚ) +
        ((11697 / 6520 : ℚ) * (((b * taylorPower g + 1) * H : ℕ) : ℚ) + g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = rootPrice g H := by
      unfold rootPrice
      push_cast
      rw [hcast]
      dsimp only [b, taylorPower]
      ring
end
end K1_14_2_4
end
section
namespace K1_14_2_4_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4
open scoped Polynomial
def c1 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g : ℕ),
    J.IsPrime → J.comap rootSeeds = seedEquation C₀ →
    Module.Finite SeedField (RootSeedSection J) →
    Module.finrank SeedField (RootSeedSection J) = C₀.totalDegree * g → 0 < g →
    Nonempty (PrimitiveRoot C₀ J g)
def c2 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g : ℕ)
    (R : PrimitiveRoot C₀ J g) (T : Finset K) (z : K → K) (s : K → K[X]),
    (∀ γ ∈ T, OnRoot J (z γ) (s γ)) →
    ∃ (n : ℕ) (A : CoefficientChart R n) (t : K → Fin n → L),
      (∀ γ ∈ T, baseMark (z γ) (t γ) ∈ MvPolynomial.zeroLocus FX (chartBase A)) ∧
      (∀ γ ∈ T, markedPoint (t γ) (s γ) ∈ MvPolynomial.zeroLocus FX (chartSource A)) ∧
      (∀ γ ∈ T, (specialize A.equation (t γ)).eval (liftPoly (s γ)) = 0)
def c3 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g H n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n),
    0 < g → Module.Finite SeedField (RootYSection J) →
    Module.finrank SeedField (RootYSection J) ≤ H → BaseHeight (chartBase A) H
def c4 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g H n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n),
    BaseHeight (chartBase A) H → Module.Finite SeedField (RootYSection J) →
    Module.finrank SeedField (RootYSection J) ≤ H →
    (MvPolynomial.affineHilbertPolynomial (chartSource A)).natDegree ≤ 1 ∧
    SliceBounds (chartSource A) (g * H) H
def c5 : Prop :=
  ∀ (n H : ℕ) (B : Ideal (ChartBaseRing n)), B.IsPrime → BaseHeight B H →
    ∀ (q : ParameterGeometry n), parameterInclusion n q ∉ B →
    ∀ (V : Finset K) (pt : K → Fin 2 ⊕ Fin n → FX), Set.InjOn pt (V : Set K) →
      (∀ γ ∈ V, pt γ ∈ MvPolynomial.zeroLocus FX B ∧
        MvPolynomial.aeval (pt γ) (parameterInclusion n q) = 0) →
      V.card ≤ q.totalDegree * H
end
end K1_14_2_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace K1_14_2_4_1_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open scoped Polynomial
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g n : ℕ}
abbrev rootPolynomial (R : PrimitiveRoot C₀ J g) := R.equation.map (insertX C₀)
abbrev RootField (R : PrimitiveRoot C₀ J g) := AdjoinRoot (rootPolynomial R)
instance (R : PrimitiveRoot C₀ J g) : Fact (Irreducible (rootPolynomial R)) :=
  ⟨R.irreducible⟩
scoped instance seedXAlgebra (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    Algebra FX (ConstantSeedX C₀) := (extendX C₀).toAlgebra
abbrev BaseRing {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :=
  ChartBaseRing n ⧸ chartBase A
def baseEmbedding {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    BaseRing A →ₐ[FX] ConstantSeedX C₀ :=
  Ideal.kerLiftAlg {
    toRingHom := chartBaseMap A
    commutes' a := MvPolynomial.eval₂Hom_C _ _ a }
def originalEmbedding (R : PrimitiveRoot C₀ J g) :
    (RootAmbient ⧸ J) →ₐ[FX] RootField R :=
  Ideal.Quotient.liftₐ J
    { toRingHom := (AdjoinRoot.mk (rootPolynomial R)).comp (genericRootMap C₀)
      commutes' a := by
        change ((AdjoinRoot.mk (rootPolynomial R)).comp (genericRootMap C₀)) (MvPolynomial.C a) =
          algebraMap FX (RootField R) a
        rw [RingHom.comp_apply, genericRootMap, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply, AdjoinRoot.mk_C]
        exact DFunLike.congr_fun (AdjoinRoot.algebraMap_eq' FX (f := rootPolynomial R)).symm a }
    (fun f hf => by
      rw [R.contraction] at hf
      exact (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {rootPolynomial R})).mpr hf)
def imageEmbedding {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    (SourceRing n ⧸ chartSource A) →ₐ[FX] RootField R :=
  Ideal.Quotient.liftₐ (chartSource A)
    { toRingHom := (AdjoinRoot.mk (rootPolynomial R)).comp (chartRootMap A)
      commutes' a := by
        change ((AdjoinRoot.mk (rootPolynomial R)).comp (chartRootMap A)) (MvPolynomial.C a) =
          algebraMap FX (RootField R) a
        rw [RingHom.comp_apply, chartRootMap, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply, AdjoinRoot.mk_C]
        exact DFunLike.congr_fun (AdjoinRoot.algebraMap_eq' FX (f := rootPolynomial R)).symm a }
    (fun _ hf => (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {rootPolynomial R})).mpr hf)
open scoped TensorProduct
abbrev Other {ι : Type} (offset : ι) := {i : ι // i ≠ offset}
abbrev CutField (k ι : Type) [Field k] := FractionRing (MvPolynomial ι k)
def genericVariable {k ι : Type} [Field k] (i : ι) : CutField k ι :=
  algebraMap (MvPolynomial ι k) (CutField k ι) (MvPolynomial.X i)
def offsetMap {k ι A : Type} [Field k] [CommRing A] [Algebra k A]
    (offset : ι) (u : MvPolynomial (Other offset) A) :
    MvPolynomial ι k →+* MvPolynomial (Other offset) A := by
  classical
  exact MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap k A))
    (fun i => if hi : i = offset then u else MvPolynomial.X ⟨i, hi⟩)
abbrev offsetAlgebra {k ι A : Type} [Field k] [CommRing A] [Algebra k A]
    (offset : ι) (u : MvPolynomial (Other offset) A) :
    Algebra (MvPolynomial ι k) (MvPolynomial (Other offset) A) :=
  (offsetMap (k := k) offset u).toAlgebra
abbrev GenericFibre (k : Type) [Field k] {ι A : Type} [CommRing A] [Algebra k A]
    (offset : ι) (u : MvPolynomial (Other offset) A) :=
  letI := offsetAlgebra (k := k) offset u
  CutField k ι ⊗[MvPolynomial ι k] MvPolynomial (Other offset) A
def cutAtOffset {k ι σ : Type} [Field k] (offset : ι)
    (u : MvPolynomial (Other offset) (MvPolynomial σ k)) :
    MvPolynomial σ (CutField k ι) :=
  MvPolynomial.eval₂Hom (MvPolynomial.map (algebraMap k (CutField k ι)))
      (fun i => MvPolynomial.C (genericVariable i.val)) u -
    MvPolynomial.C (genericVariable offset)
abbrev PresentedSection {k ι σ : Type} [Field k] (offset : ι)
    (I : Ideal (MvPolynomial σ k)) (u : MvPolynomial (Other offset) (MvPolynomial σ k)) :=
  MvPolynomial σ (CutField k ι) ⧸
    (I.map (MvPolynomial.map (algebraMap k (CutField k ι))) ⊔ Ideal.span {cutAtOffset offset u})
def parameterForm {n : ℕ} {A : Type} [CommRing A] (x : Fin n → A) :
    MvPolynomial (Other (none : Option (Fin n))) A :=
  ∑ i, MvPolynomial.X ⟨some i, Option.some_ne_none i⟩ * MvPolynomial.C (x i)
def LengthBound (F M : Type) [Field F] [AddCommGroup M] [Module F M] (d : ℕ) : Prop :=
  Module.Finite F M ∧ Module.finrank F M ≤ d
end
end K1_14_2_4_1_4
end
section
set_option maxHeartbeats 800000
namespace K1_14_2_4_1_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open scoped Polynomial
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g n : ℕ}
theorem baseEmbedding_injective {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    Function.Injective (baseEmbedding A) :=
  Ideal.kerLiftAlg_injective _
theorem originalEmbedding_injective (R : PrimitiveRoot C₀ J g) :
    Function.Injective (originalEmbedding R) := by
  apply (injective_iff_map_eq_zero (originalEmbedding R)).mpr
  intro a ha
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  change AdjoinRoot.mk (rootPolynomial R) (genericRootMap C₀ f) = 0 at ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [R.contraction]
  exact (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {rootPolynomial R})).mp ha
theorem imageEmbedding_injective {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    Function.Injective (imageEmbedding A) := by
  apply (injective_iff_map_eq_zero (imageEmbedding A)).mpr
  intro a ha
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  change AdjoinRoot.mk (rootPolynomial R) (chartRootMap A f) = 0 at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {rootPolynomial R})).mp ha)
scoped instance baseDomain {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    IsDomain (BaseRing A) :=
  Function.Injective.isDomain _ (baseEmbedding_injective A)
theorem root_degree (R : PrimitiveRoot C₀ J g) :
    Module.finrank (ConstantSeedX C₀) (RootField R) = g := by
  change Module.finrank (ConstantSeedX C₀)
    ((ConstantSeedX C₀)[X] ⧸ Ideal.span {rootPolynomial R}) = g
  rw [finrank_quotient_span_eq_natDegree]
  exact (Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective (ConstantSeedField C₀)[X] (ConstantSeedX C₀)) R.equation).trans R.degree
scoped instance rootFinite (R : PrimitiveRoot C₀ J g) :
    Module.Finite (ConstantSeedX C₀) (RootField R) :=
  (AdjoinRoot.powerBasis R.irreducible.ne_zero).finite
private theorem mem_from_fractionRing {D F E : Type} [CommRing D] [IsDomain D]
    [Field F] [Field E] [Algebra D F] [IsFractionRing D F]
    (f : F →+* E) (S : Subfield E) (h : ∀ d, f (algebraMap D F d) ∈ S) (x : F) :
    f x ∈ S := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective D x
  rw [map_div₀]
  exact S.div_mem (h a) (h b)
private theorem extendX_C (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (a : L) :
    extendX C₀ (algebraMap L FX a) = insertConstant C₀ (constToSeed C₀ a) := by
  rw [IsScalarTower.algebraMap_apply L L[X] FX]
  unfold extendX IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertConstant, insertX]
private theorem extendX_X (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    extendX C₀ (algebraMap L[X] FX Polynomial.X) = insertX C₀ Polynomial.X := by
  unfold extendX IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertX]
private theorem mem_seedField {E : Type} [Field E] (f : ConstantSeedX C₀ →+* E)
    (S : Subfield E) (hfx : ∀ x, f (extendX C₀ x) ∈ S)
    (hseed : ∀ i, f (insertConstant C₀ (seedCoordinate C₀ i)) ∈ S)
    (x : ConstantSeedX C₀) : f x ∈ S := by
  refine mem_from_fractionRing (D := (ConstantSeedField C₀)[X]) f S (fun q => ?_) x
  change (f.comp (insertX C₀)) q ∈ S
  have hconst (a : ConstantSeedField C₀) : (f.comp (insertConstant C₀)) a ∈ S := by
    refine mem_from_fractionRing (D := ConstantSeedRing C₀) (f.comp (insertConstant C₀)) S (fun b => ?_) a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    let e := (f.comp (insertConstant C₀)).comp
      ((algebraMap (ConstantSeedRing C₀) (ConstantSeedField C₀)).comp
        (Ideal.Quotient.mk (constantIdeal C₀)))
    change e q ∈ S
    induction q using MvPolynomial.induction_on with
    | C a =>
      change f (insertConstant C₀ (constToSeed C₀ a)) ∈ S
      rw [← extendX_C]
      exact hfx _
    | add p q hp hq => exact (map_add e p q).symm ▸ S.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact S.mul_mem hp (hseed i)
  induction q using Polynomial.induction_on' with
  | add p q hp hq => exact (map_add (f.comp (insertX C₀)) p q).symm ▸ S.add_mem hp hq
  | monomial i a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    exact S.mul_mem (hconst a) (S.pow_mem (by
      change f (insertX C₀ Polynomial.X) ∈ S
      rw [← extendX_X]
      exact hfx _) _)
private def fractionExtension {D M : Type} [CommRing D] [IsDomain D] [Field M]
    (f : D →+* M) (hf : Function.Injective f) :
    let _ := f.toAlgebra
    FractionRing D →ₐ[D] M := by
  let _ : Algebra D M := f.toAlgebra
  exact { toRingHom := IsFractionRing.lift (g := f) hf
          commutes' := IsFractionRing.lift_algebraMap (K := FractionRing D) (g := f) hf }
private theorem fractionExtension_apply {D M : Type} [CommRing D] [IsDomain D] [Field M]
    (f : D →+* M) (hf : Function.Injective f) (x : D) :
    fractionExtension f hf (algebraMap D (FractionRing D) x) = f x :=
  IsFractionRing.lift_algebraMap (K := FractionRing D) (g := f) hf x
private theorem fractionRing_of_generators {D M : Type} [CommRing D] [IsDomain D] [Field M]
    (f : D →+* M) (hf : Function.Injective f)
    (h : ∀ S : Subfield M, (∀ x : D, f x ∈ S) → ∀ x : M, x ∈ S) :
    let _ := f.toAlgebra
    IsFractionRing D M := by
  let _ : Algebra D M := f.toAlgebra
  let φ : FractionRing D →ₐ[D] M := fractionExtension f hf
  have hφ : Function.Surjective φ := by
    intro z
    exact h φ.toRingHom.fieldRange
      (fun x => ⟨algebraMap D (FractionRing D) x, fractionExtension_apply f hf x⟩) z
  exact IsFractionRing.of_algEquiv (AlgEquiv.ofBijective φ ⟨φ.injective, hφ⟩)
private theorem tower_of_embedding {k A B : Type} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) :
    @IsScalarTower k A B inferInstance f.toRingHom.toAlgebra.toSMul inferInstance := by
  let _ : Algebra A B := f.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
abbrev baseAlgebra {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    Algebra (BaseRing A) (ConstantSeedX C₀) := (baseEmbedding A).toRingHom.toAlgebra
theorem baseTower {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    @IsScalarTower FX (BaseRing A) (ConstantSeedX C₀)
      (inferInstance : Algebra FX (BaseRing A)).toSMul (baseAlgebra A).toSMul
      (seedXAlgebra C₀).toSMul :=
  tower_of_embedding (k := FX) (A := BaseRing A) (B := ConstantSeedX C₀) (baseEmbedding A)
theorem baseEmbedding_mk {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n)
    (f : ChartBaseRing n) :
    baseEmbedding A (Ideal.Quotient.mk (chartBase A) f) = chartBaseMap A f := rfl
theorem baseFractionRing {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    let _ := baseAlgebra A
    IsFractionRing (BaseRing A) (ConstantSeedX C₀) := by
  let m : BaseRing A →+* ConstantSeedX C₀ := (baseEmbedding A).toRingHom
  have hm : Function.Injective m := baseEmbedding_injective A
  refine fractionRing_of_generators (D := BaseRing A) (M := ConstantSeedX C₀) m hm ?_
  intro S hS x
  have hmem (b : BaseRing A) : baseEmbedding A b ∈ S := hS b
  change (RingHom.id (ConstantSeedX C₀)) x ∈ S
  apply mem_seedField (C₀ := C₀) (RingHom.id _) S _ _ x
  · intro a
    simpa [baseEmbedding_mk, chartBaseMap] using
      hmem (Ideal.Quotient.mk (chartBase A) (MvPolynomial.C a))
  · intro i
    simpa [baseEmbedding_mk, chartBaseMap] using
      hmem (Ideal.Quotient.mk (chartBase A) (MvPolynomial.X (Sum.inl i)))
theorem originalDomain (R : PrimitiveRoot C₀ J g) : IsDomain (RootAmbient ⧸ J) :=
  Function.Injective.isDomain _ (originalEmbedding_injective R)
abbrev originalAlgebra (R : PrimitiveRoot C₀ J g) :
    Algebra (RootAmbient ⧸ J) (RootField R) := (originalEmbedding R).toRingHom.toAlgebra
theorem originalFractionRing (R : PrimitiveRoot C₀ J g) :
    let _ := originalAlgebra R
    IsFractionRing (RootAmbient ⧸ J) (RootField R) := by
  let B := RootAmbient ⧸ J
  let E := RootField R
  have : IsDomain B := originalDomain R
  let m : B →+* E := (originalEmbedding R).toRingHom
  have hm : Function.Injective m := originalEmbedding_injective R
  refine fractionRing_of_generators (D := B) (M := E) m hm ?_
  intro S hS z
  have hmem (x : B) : originalEmbedding R x ∈ S := hS x
  have hconstants (x : ConstantSeedX C₀) : AdjoinRoot.of (rootPolynomial R) x ∈ S := by
    apply mem_seedField (AdjoinRoot.of (rootPolynomial R)) S _ _ x
    · intro a
      simpa [originalEmbedding, genericRootMap] using
        hmem (Ideal.Quotient.mk J (MvPolynomial.C a))
    · intro i
      fin_cases i
      · simpa [originalEmbedding, genericRootMap] using
          hmem (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin 3)))
      · simpa [originalEmbedding, genericRootMap] using
          hmem (Ideal.Quotient.mk J (MvPolynomial.X (1 : Fin 3)))
  have hY : AdjoinRoot.mk (rootPolynomial R) Polynomial.X ∈ S := by
    simpa [originalEmbedding, genericRootMap] using
      hmem (Ideal.Quotient.mk J (MvPolynomial.X (2 : Fin 3)))
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  change AdjoinRoot.mk (rootPolynomial R) q ∈ S
  induction q using Polynomial.induction_on' with
  | add p q hp hq => exact (map_add (AdjoinRoot.mk (rootPolynomial R)) p q).symm ▸ S.add_mem hp hq
  | monomial i a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C]
    exact S.mul_mem (hconstants a) (S.pow_mem hY i)
private theorem trdeg_eq_of_finite_embedding {k A B : Type} [Field k] [CommRing A]
    [CommRing B] [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hi : Function.Injective f) (hf : f.Finite) :
    Algebra.trdeg k B = Algebra.trdeg k A := by
  let _ : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hi
  have : Module.Finite A B := hf
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  rw [← trdeg_add_eq k A (A := B), trdeg_eq_zero (R := A) (A := B), add_zero]
private theorem trdeg_eq_hilbert_degree {k σ : Type} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    Algebra.trdeg k (MvPolynomial σ k ⧸ I) =
      ((MvPolynomial.affineHilbertPolynomial I).natDegree : Cardinal) := by
  let B := MvPolynomial σ k ⧸ I
  obtain ⟨d, f, hfinj, hf⟩ := exists_finite_inj_algHom_of_fg k B
  rw [trdeg_eq_of_finite_embedding f hfinj hf,
    MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective f hf hfinj,
    Nat.card_fin]
  simp [MvPolynomial.trdeg_of_isDomain]
theorem image_dimension {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n)
    (hd : (MvPolynomial.affineHilbertPolynomial (chartBase A)).natDegree ≤ 1) :
    (MvPolynomial.affineHilbertPolynomial (chartSource A)).natDegree ≤ 1 := by
  let B := BaseRing A
  let F := ConstantSeedX C₀
  let E := RootField R
  have : (chartBase A).IsPrime := RingHom.ker_isPrime (chartBaseMap A)
  have : (chartSource A).IsPrime := (Ideal.Quotient.isDomain_iff_prime (chartSource A)).mp
    (Function.Injective.isDomain _ (imageEmbedding_injective A))
  let _ : Algebra B F := baseAlgebra A
  let _ : SMul B F := (baseAlgebra A).toSMul
  let _ : SMul FX B := (inferInstance : Algebra FX B).toSMul
  let _ : SMul FX F := (seedXAlgebra C₀).toSMul
  have : IsScalarTower FX B F := baseTower A
  have : IsFractionRing B F := baseFractionRing A
  have : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective B F).mpr (baseEmbedding_injective A)
  have : FaithfulSMul FX F := (faithfulSMul_iff_algebraMap_injective FX F).mpr (extendX C₀).injective
  have : Algebra.IsAlgebraic B F := IsLocalization.isAlgebraic F (nonZeroDivisors B)
  have : Module.Finite F E := rootFinite R
  have : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  have h : Algebra.trdeg FX (SourceRing n ⧸ chartSource A) ≤ Algebra.trdeg FX E :=
    trdeg_le_of_injective (imageEmbedding A) (imageEmbedding_injective A)
  rw [← trdeg_add_eq FX F (A := E), ← trdeg_add_eq FX B (A := F),
    trdeg_eq_zero (R := B) (A := F), trdeg_eq_zero (R := F) (A := E),
    add_zero, add_zero, trdeg_eq_hilbert_degree (chartSource A),
    show Algebra.trdeg FX B = Algebra.trdeg FX (ChartBaseRing n ⧸ chartBase A) from rfl,
    trdeg_eq_hilbert_degree (chartBase A)] at h
  have h' : (MvPolynomial.affineHilbertPolynomial (chartSource A)).natDegree ≤
      (MvPolynomial.affineHilbertPolynomial (chartBase A)).natDegree := by exact_mod_cast h
  exact h'.trans hd
end
end K1_14_2_4_1_4
end
section
namespace K1_14_2_4_1_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open scoped BigOperators Polynomial
def coefficientIdeal {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) : Ideal (ParameterRing n) :=
  RingHom.ker (MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate)
def seedDegree {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) : ℕ :=
  letI : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  let F := IntermediateField.adjoin L (Set.range A.coordinate)
  Module.finrank F (ConstantSeedField C₀)
abbrev extendedIdeal {k σ : Type*} [Field k] (E : Type*) [Field E] [Algebra k E]
    (I : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ E) :=
  I.map (MvPolynomial.map (algebraMap k E))
abbrev cutQuotient {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) :=
  MvPolynomial σ k ⧸ (I ⊔ Ideal.span {f})
def coefficientCut (n : ℕ) : MvPolynomial (Fin n) (SliceField n) :=
  (∑ i : Fin n, MvPolynomial.C (sliceVariable (some i)) * MvPolynomial.X i) -
    MvPolynomial.C (sliceVariable (n := n) none)
def ordinateForm {n : ℕ} (f : FamilyEquation n) : MvPolynomial (Fin n) SeedField :=
  (equationAtX f).eval₂ (MvPolynomial.map (algebraMap FX SeedField))
    (MvPolynomial.C (generic 1))
abbrev CoefficientSection {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :=
  cutQuotient (extendedIdeal (SliceField n) (coefficientIdeal A)) (coefficientCut n)
abbrev OrdinateSection {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :=
  cutQuotient (extendedIdeal SeedField (coefficientIdeal A)) (ordinateForm A.equation)
structure RegularLinearCut {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) : Prop where
  degree : f.totalDegree ≤ 1
  regular : IsLeftRegular (Ideal.Quotient.mk I f)
  boundary : ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
    ∀ x ∈ MvPolynomial.quotientDegreeLE I (d + 1),
      Ideal.Quotient.mk I f * x ∈ MvPolynomial.quotientDegreeLE I (d + 1) →
        x ∈ MvPolynomial.quotientDegreeLE I d
theorem coefficient_representation {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) (i : Fin n) :
    ∃ j k, (A.equation.coeff j).coeff k - MvPolynomial.X i ∈ coefficientIdeal A := by
  obtain ⟨j, k, hi⟩ := A.coordinates_are_coefficients i
  refine ⟨j, k, ?_⟩
  have h := congrArg (fun F : ((ConstantSeedField C₀)[X])[X] => (F.coeff j).coeff k)
    A.generic_eq
  simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom] at h
  change MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate
    ((A.equation.coeff j).coeff k - MvPolynomial.X i) = 0
  rw [map_sub, MvPolynomial.eval₂Hom_X']
  exact sub_eq_zero.mpr (h.trans hi.symm)
theorem coefficient_normalization {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    ∃ ℓ : Fin n → L,
      (∑ i, MvPolynomial.C (ℓ i) * MvPolynomial.X i) - 1 ∈ coefficientIdeal A := by
  obtain ⟨ℓ, hℓ⟩ := A.normalized
  refine ⟨ℓ, ?_⟩
  change MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate
    ((∑ i, MvPolynomial.C (ℓ i) * MvPolynomial.X i) - 1) = 0
  simp only [map_sub, map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    map_one, sub_eq_zero]
  exact hℓ
end
end K1_14_2_4_1_3
end
section
namespace K1_14_2_4_1_3
noncomputable section
open Algebra MvPolynomial K1_14 K1_14_2_4 K1_14_2_4_1
open scoped Polynomial
private theorem dim_of_field {k σ E : Type} [Field k] [Finite σ] [Field E] [Algebra k E]
    (f : MvPolynomial σ k →ₐ[k] E) (hE : trdeg k E ≤ 1) :
    (affineHilbertPolynomial (RingHom.ker f.toRingHom)).natDegree ≤ 1 := by
  let I := RingHom.ker f.toRingHom
  let : I.IsPrime := RingHom.ker_isPrime f.toRingHom
  let ι : (MvPolynomial σ k ⧸ I) →ₐ[k] E :=
    ⟨RingHom.kerLift f.toRingHom, fun r => f.commutes r⟩
  have hi : Function.Injective ι := RingHom.kerLift_injective f.toRingHom
  obtain ⟨d, u, hu, hfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have h := (trdeg_le_of_injective (ι.comp u) (hi.comp hu)).trans hE
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at h
  rw [natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective u hfin hu, Nat.card_fin]
  exact_mod_cast h
private theorem trdeg_fraction (k B : Type) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] : trdeg k (FractionRing B) = trdeg k B := by
  let : Algebra.IsAlgebraic B (FractionRing B) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing B)).mpr inferInstance
  rw [← trdeg_add_eq k B, trdeg_eq_zero (R := B), add_zero]
private theorem trdeg_of_normalization {k B : Type} [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] {d : ℕ} (u : MvPolynomial (Fin d) k →ₐ[k] B)
    (hu : Function.Injective u) (hfin : u.Finite) : trdeg k B = d := by
  let P := MvPolynomial (Fin d) k
  let : Algebra P B := u.toRingHom.toAlgebra
  let : IsScalarTower k P B := IsScalarTower.of_algHom u
  let : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective P B).mpr hu
  let : Module.Finite P B := hfin
  rw [← trdeg_add_eq k P, trdeg_eq_zero (R := P), add_zero,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin]
private theorem seed_trdeg (C₀ : ConstantSeeds) [hC : Fact (Irreducible C₀)] :
    trdeg L (ConstantSeedField C₀) ≤ 1 := by
  let B := ConstantSeedRing C₀
  obtain ⟨d, u, hu, hfin⟩ := exists_finite_inj_algHom_of_fg L B
  have hdim : (affineHilbertPolynomial (constantIdeal C₀)).natDegree ≤ 1 := by
    simpa using natDegree_affineHilbertPolynomial_le_of_mem (I := constantIdeal C₀)
      hC.out.ne_zero (Ideal.mem_span_singleton_self C₀)
  rw [natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective u hfin hu,
    Nat.card_fin] at hdim
  rw [trdeg_fraction L B, trdeg_of_normalization u hu hfin]
  exact_mod_cast hdim
private theorem extend_constant (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (a : L) :
    extendX C₀ (algebraMap L FX a) = algebraMap L (ConstantSeedX C₀) a := by
  rw [IsScalarTower.algebraMap_apply L L[X] FX]
  unfold extendX IsFractionRing.map
  rw [IsLocalization.map_eq]
  rw [IsScalarTower.algebraMap_apply L (ConstantSeedField C₀)[X] (ConstantSeedX C₀)]
  simp only [Polynomial.coe_mapRingHom, Polynomial.algebraMap_apply, Polynomial.map_C]
  rfl
private theorem graph_dim {k F E Q σ : Type} [Field k] [Field F] [Field E] [Field Q]
    [Finite σ] [Algebra k F] [Algebra k E] [Algebra k Q] [Algebra E Q]
    [IsScalarTower k E Q] (i : F →ₐ[k] Q) (f : MvPolynomial σ F →+* Q)
    (hf : ∀ a, f (MvPolynomial.C a) = i a)
    (hF : trdeg k F = 1) (hQ : trdeg E Q = 1) (hE : trdeg k E ≤ 1) :
    (affineHilbertPolynomial (RingHom.ker f)).natDegree ≤ 1 := by
  let : Algebra F Q := i.toRingHom.toAlgebra
  let : IsScalarTower k F Q := IsScalarTower.of_algHom i
  let φ : MvPolynomial σ F →ₐ[F] Q := ⟨f, hf⟩
  apply dim_of_field φ
  apply (Cardinal.add_le_add_iff_of_lt_aleph0 (γ := 1) (by simp)).mp
  calc
    trdeg F Q + 1 = trdeg k Q := by rw [add_comm, ← hF, trdeg_add_eq k F]
    _ = trdeg k E + 1 := by rw [← trdeg_add_eq k E, hQ]
    _ ≤ 1 + 1 := add_le_add_left hE 1
theorem chart_dimension {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    (affineHilbertPolynomial (chartBase A)).natDegree ≤ 1 ∧
      (affineHilbertPolynomial (coefficientIdeal A)).natDegree ≤ 1 := by
  let E := ConstantSeedField C₀
  let Q := ConstantSeedX C₀
  have hFX : trdeg L FX = 1 := (trdeg_fraction L L[X]).trans Polynomial.trdeg_of_isDomain
  have hX : trdeg E Q = 1 := (trdeg_fraction E E[X]).trans Polynomial.trdeg_of_isDomain
  let i : FX →ₐ[L] Q := ⟨extendX C₀, extend_constant C₀⟩
  let u : ParameterRing n →ₐ[L] E :=
    ⟨MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate, MvPolynomial.eval₂Hom_C _ _⟩
  exact ⟨graph_dim i (chartBaseMap A) (MvPolynomial.eval₂Hom_C _ _) hFX hX (seed_trdeg C₀),
    dim_of_field u (seed_trdeg C₀)⟩
end
end K1_14_2_4_1_3
end
section
namespace K1_14_2_4_1_3
noncomputable section
open MvPolynomial
variable {k σ : Type*} [Field k]
private theorem strict_mul {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (h : RegularLinearCut I f) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ x : MvPolynomial σ k ⧸ I,
      Ideal.Quotient.mk I f * x ∈ quotientDegreeLE I (d + 1) →
        x ∈ quotientDegreeLE I d := by
  obtain ⟨N, hN⟩ := h.boundary
  refine ⟨N, ?_⟩
  intro d hd x hfx
  have shrink : ∀ r, x ∈ quotientDegreeLE I (d + r) → x ∈ quotientDegreeLE I d := by
    intro r
    induction r with
    | zero => exact id
    | succ r ih =>
        intro hx
        apply ih
        exact hN (d + r) (by omega) x hx
          (quotientDegreeLE_mono I (by omega) hfx)
  obtain ⟨r, hr⟩ := exists_mem_quotientDegreeLE I x
  exact shrink r (quotientDegreeLE_mono I (by omega) hr)
variable [Finite σ]
private theorem hilbertFunction_cut {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (h : RegularLinearCut I f) {d : ℕ}
    (hs : ∀ x : MvPolynomial σ k ⧸ I,
      Ideal.Quotient.mk I f * x ∈ quotientDegreeLE I (d + 1) →
        x ∈ quotientDegreeLE I d) :
    affineHilbertFunction (I ⊔ Ideal.span {f}) (d + 1) + affineHilbertFunction I d =
      affineHilbertFunction I (d + 1) := by
  let J := I ⊔ Ideal.span {f}
  have hIJ : I ≤ J := le_sup_left
  let U := quotientDegreeLE I d
  let V := quotientDegreeLE I (d + 1)
  let W := quotientDegreeLE J (d + 1)
  let π : V →ₗ[k] W :=
    ((Ideal.Quotient.factorₐ k hIJ).toLinearMap.domRestrict V).codRestrict W (fun z => by
      obtain ⟨p, hp, hz⟩ := mem_quotientDegreeLE.mp z.property
      change Ideal.Quotient.factor hIJ z.val ∈ W
      rw [← hz, Ideal.Quotient.factor_mk]
      exact mk_mem_quotientDegreeLE hp)
  let μ : U →ₗ[k] V :=
    ((LinearMap.mulLeft k (Ideal.Quotient.mk I f)).domRestrict U).codRestrict V (fun x => by
      change Ideal.Quotient.mk I f * x.val ∈ V
      have hm := mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE (I := I) h.degree) x.property
      simpa only [V, Nat.add_comm 1 d] using hm)
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨p, hp, hz⟩ := mem_quotientDegreeLE.mp z.property
    exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hz⟩
  have hμ : Function.Injective μ := by
    intro x y hxy
    exact Subtype.ext (h.regular (congrArg (fun z : V => z.val) hxy))
  have hexact : LinearMap.range μ = LinearMap.ker π := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change Ideal.Quotient.factor hIJ (Ideal.Quotient.mk I f * x.val) = 0
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)), zero_mul]
    · intro hz
      obtain ⟨p, hp, hpz⟩ := mem_quotientDegreeLE.mp z.property
      have hz' := congrArg (fun w : W => w.val) (LinearMap.mem_ker.mp hz)
      change Ideal.Quotient.factor hIJ z.val = 0 at hz'
      rw [← hpz, Ideal.Quotient.factor_mk] at hz'
      have hm : p ∈ Ideal.span {f} ⊔ I := sup_comm I (Ideal.span {f}) ▸
        (Ideal.Quotient.eq_zero_iff_mem.mp hz' : p ∈ J)
      obtain ⟨a, b, hb, he⟩ := Ideal.mem_span_singleton_sup.mp hm
      have he' : Ideal.Quotient.mk I f * Ideal.Quotient.mk I a = z.val := by
        rw [← hpz, ← he, map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero,
          mul_comm]
      have ha : Ideal.Quotient.mk I a ∈ U := hs _ (he'.symm ▸ z.property)
      exact ⟨⟨Ideal.Quotient.mk I a, ha⟩, Subtype.ext he'⟩
  have hrank := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, ← hexact,
    LinearMap.finrank_range_of_inj hμ] at hrank
  exact hrank
theorem length_of_regularLinearCut {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hdim : (affineHilbertPolynomial I).natDegree ≤ 1) (h : RegularLinearCut I f) :
    Module.Finite k (cutQuotient I f) ∧
      (Module.finrank k (cutQuotient I f) : ℚ) = (affineHilbertPolynomial I).coeff 1 := by
  let J := I ⊔ Ideal.span {f}
  have hJdim : (affineHilbertPolynomial J).natDegree ≤
      (affineHilbertPolynomial I).natDegree - 1 :=
    (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le h.regular h.degree).1
  have hfinite : Module.Finite k (cutQuotient I f) :=
    (natDegree_affineHilbertPolynomial_eq_zero_iff (I := J)).mp (by omega)
  let : Module.Finite k (MvPolynomial σ k ⧸ J) := hfinite
  refine ⟨hfinite, ?_⟩
  obtain ⟨N, hN⟩ := strict_mul h
  obtain ⟨N₁, hN₁⟩ := exists_eval_affineHilbertPolynomial I
  obtain ⟨N₂, hN₂⟩ := exists_affineHilbertFunction_eq_finrank J
  let d := N + N₁ + N₂
  have hd : N ≤ d := by dsimp [d]; omega
  have hd₁ : N₁ ≤ d := by dsimp [d]; omega
  have hd₂ : N₂ ≤ d + 1 := by dsimp [d]; omega
  have hsum := hilbertFunction_cut h (hN d hd)
  rw [show I ⊔ Ideal.span {f} = J from rfl, hN₂ _ hd₂] at hsum
  have hsumQ : (Module.finrank k (cutQuotient I f) : ℚ) +
      (affineHilbertPolynomial I).eval (d : ℚ) =
      (affineHilbertPolynomial I).eval ((d + 1 : ℕ) : ℚ) := by
    rw [hN₁ d hd₁, hN₁ (d + 1) (by omega)]
    exact_mod_cast hsum
  have he (x : ℚ) : (affineHilbertPolynomial I).eval x =
      (affineHilbertPolynomial I).coeff 1 * x + (affineHilbertPolynomial I).coeff 0 := by
    nth_rw 1 [Polynomial.eq_X_add_C_of_natDegree_le_one hdim]
    simp
  simp only [he, Nat.cast_add, Nat.cast_one, mul_add, mul_one] at hsumQ
  linarith
end
end K1_14_2_4_1_3
end
section
namespace K1_14_2_4_1_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open scoped Polynomial
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g : ℕ}
abbrev rootEquation (R : PrimitiveRoot C₀ J g) := R.equation.map (insertX C₀)
instance (R : PrimitiveRoot C₀ J g) : Fact (Irreducible (rootEquation R)) := ⟨R.irreducible⟩
abbrev RootField (R : PrimitiveRoot C₀ J g) := AdjoinRoot (rootEquation R)
def generic (R : PrimitiveRoot C₀ J g) : RootAmbient →+* RootField R :=
  (AdjoinRoot.mk (rootEquation R)).comp (genericRootMap C₀)
def seedInRoot (R : PrimitiveRoot C₀ J g) : ConstantSeedField C₀ →+* RootField R :=
  (AdjoinRoot.of (rootEquation R)).comp (insertConstant C₀)
structure MarkLift (R : PrimitiveRoot C₀ J g) (z : K) (S : K[X]) where
  V : ValuationSubring (RootField R)
  ambient : RootAmbient →+* V
  generic_eq : V.toSubring.subtype.comp ambient = generic R
  marked_eq : (IsLocalRing.residue V).comp ambient =
    ((IsLocalRing.residue V).comp (ambient.comp MvPolynomial.C)).comp (rootMarkHom z S)
def MarkLift.fx {R : PrimitiveRoot C₀ J g} {z : K} {S : K[X]} (M : MarkLift R z S) :
    FX →+* M.V :=
  M.ambient.comp MvPolynomial.C
def MarkLift.constant {R : PrimitiveRoot C₀ J g} {z : K} {S : K[X]} (M : MarkLift R z S) :
    L →+* M.V :=
  M.fx.comp (algebraMap L FX)
def MarkLift.ConstantResidues {R : PrimitiveRoot C₀ J g} {z : K} {S : K[X]}
    (M : MarkLift R z S) : Prop :=
  ∀ (a : ConstantSeedField C₀) (ha : seedInRoot R a ∈ M.V),
    ∃ c : L, IsLocalRing.residue M.V ⟨seedInRoot R a, ha⟩ =
      IsLocalRing.residue M.V (M.constant c)
end
end K1_14_2_4_1_2
end
section
namespace K1_14_2_4_1_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open scoped TensorProduct
theorem lengthBound_of_injective {k U V : Type} [Field k] [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] (f : U →ₗ[k] V) (hf : Function.Injective f) {d : ℕ}
    (h : LengthBound k V d) : LengthBound k U d := by
  have := h.1
  exact ⟨FiniteDimensional.of_injective f hf, (f.finrank_le_finrank_of_injective hf).trans h.2⟩
theorem fibre_le_of_injective {k ι A B : Type} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (offset : ι) (u : MvPolynomial (Other offset) A)
    (f : A →ₐ[k] B) (hf : Function.Injective f) {d : ℕ}
    (h : LengthBound (CutField k ι) (GenericFibre k offset (MvPolynomial.map f.toRingHom u)) d) :
    LengthBound (CutField k ι) (GenericFibre k offset u) d := by
  classical
  let T := MvPolynomial ι k
  let F := CutField k ι
  let v := MvPolynomial.map f.toRingHom u
  let _ := offsetAlgebra (k := k) offset u
  let _ := offsetAlgebra (k := k) offset v
  have heq : (MvPolynomial.map f.toRingHom).comp (offsetMap (k := k) offset u) =
      offsetMap (k := k) offset v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [offsetMap, RingHom.comp_apply]
    · intro i
      by_cases hi : i = offset
      · simp [offsetMap, hi, v]
      · simp [offsetMap, hi]
  let f' : MvPolynomial (Other offset) A →ₐ[T] MvPolynomial (Other offset) B :=
    { toRingHom := MvPolynomial.map f.toRingHom
      commutes' a := DFunLike.congr_fun heq a }
  let fL := TensorProduct.AlgebraTensorModule.lTensor F F f'.toLinearMap
  have : Module.Flat T F := IsLocalization.flat F (nonZeroDivisors T)
  have hInj : Function.Injective fL :=
    Module.Flat.lTensor_preserves_injective_linearMap f'.toLinearMap (MvPolynomial.map_injective _ hf)
  exact lengthBound_of_injective fL hInj h
theorem cutAtOffset_parameterForm {k σ : Type} [Field k] {n : ℕ} (x : Fin n → σ) :
    cutAtOffset (none : Option (Fin n)) (parameterForm fun i => (MvPolynomial.X (x i) : MvPolynomial σ k)) =
      (∑ i : Fin n, MvPolynomial.C (genericVariable (k := k) (some i)) * MvPolynomial.X (x i)) -
        MvPolynomial.C (genericVariable (k := k) (none : Option (Fin n))) := by
  classical
  simp [cutAtOffset, parameterForm, map_sum, map_mul]
theorem cutAtOffset_ordinate {k ι σ : Type} [Field k] (offset : ι) (x : σ) :
    cutAtOffset offset (MvPolynomial.C (MvPolynomial.X x : MvPolynomial σ k)) =
      MvPolynomial.X x - MvPolynomial.C (genericVariable (k := k) offset) := by
  simp [cutAtOffset]
end
end K1_14_2_4_1_4
end
section
namespace K1_14_2_4_1_3_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_2
open scoped Polynomial
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g n : ℕ}
def rootBase (R : PrimitiveRoot C₀ J g) : FX →+* RootField R :=
  (AdjoinRoot.of (rootEquation R)).comp (extendX C₀)
def rootOrdinate (R : PrimitiveRoot C₀ J g) : RootField R :=
  AdjoinRoot.root (rootEquation R)
def coefficientRoot {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    letI : Algebra FX (RootField R) := (rootBase R).toAlgebra
    IntermediateField FX (RootField R) :=
  letI : Algebra FX (RootField R) := (rootBase R).toAlgebra
  IntermediateField.adjoin FX
    (Set.range (fun i => seedInRoot R (A.coordinate i)) ∪ {rootOrdinate R})
abbrev CoefficientRootField {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :=
  ↥(coefficientRoot A)
def coefficientRootInclusion {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    CoefficientRootField A →+* RootField R :=
  letI : Algebra FX (RootField R) := (rootBase R).toAlgebra
  (coefficientRoot A).val.toRingHom
def coefficientBase {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    FX →+* CoefficientRootField A :=
  letI : Algebra FX (RootField R) := (rootBase R).toAlgebra
  algebraMap FX (CoefficientRootField A)
def coefficientOrdinate {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) :
    CoefficientRootField A := by
  letI : Algebra FX (RootField R) := (rootBase R).toAlgebra
  exact ⟨rootOrdinate R, IntermediateField.subset_adjoin FX _
    (Set.mem_union_right _ (Set.mem_singleton _))⟩
abbrev SpareField (E : Type) [Field E] := FractionRing E[X]
def spareConstant (E : Type) [Field E] : E →+* SpareField E :=
  (algebraMap E[X] (SpareField E)).comp Polynomial.C
def spareVariable (E : Type) [Field E] : SpareField E :=
  algebraMap E[X] (SpareField E) Polynomial.X
def mapSpare {E F : Type} [Field E] [Field F] (i : E →+* F) :
    SpareField E →+* SpareField F :=
  IsFractionRing.map (j := Polynomial.mapRingHom i) (Polynomial.map_injective i i.injective)
@[simp] theorem mapSpare_constant {E F : Type} [Field E] [Field F] (i : E →+* F) (x : E) :
    mapSpare i (spareConstant E x) = spareConstant F (i x) := by
  unfold mapSpare spareConstant IsFractionRing.map
  simp only [RingHom.comp_apply, IsLocalization.map_eq, Polynomial.coe_mapRingHom,
    Polynomial.map_C]
@[simp] theorem mapSpare_variable {E F : Type} [Field E] [Field F] (i : E →+* F) :
    mapSpare i (spareVariable E) = spareVariable F := by
  unfold mapSpare spareVariable IsFractionRing.map
  simp only [IsLocalization.map_eq, Polynomial.coe_mapRingHom, Polynomial.map_X]
def IsOrdinateMap {E : Type} [Field E] (i : FX →+* E) (y : E)
    (b : SeedField →+* SpareField E) : Prop :=
  (∀ a, b (algebraMap FX SeedField a) = spareConstant E (i a)) ∧
  b (generic 1) = spareConstant E y ∧
  b (generic 0) = spareVariable E
def fieldDegree {E F : Type} [Field E] [Field F] (i : E →+* F) : ℕ :=
  letI : Algebra E F := i.toAlgebra
  Module.finrank E F
end
end K1_14_2_4_1_3_3
end
section
set_option autoImplicit false
namespace K1_14_2_4_1_5
noncomputable section
open K1_14 K1_14_2_4_1 MvPolynomial
open scoped TensorProduct
abbrev Base {n : ℕ} (B : Ideal (ChartBaseRing n)) := ChartBaseRing n ⧸ B
abbrev SlopeField (n : ℕ) := FractionRing (ParameterGeometry n)
abbrev ExtendedBase {n : ℕ} (B : Ideal (ChartBaseRing n)) :=
  SlopeField n ⊗[FX] Base B
scoped instance extendedBaseCommRing {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    CommRing (ExtendedBase B) :=
  Algebra.TensorProduct.instCommRing (R := FX) (A := SlopeField n) (B := Base B)
scoped instance extendedBaseCommSemiring {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    CommSemiring (ExtendedBase B) :=
  Algebra.TensorProduct.instCommSemiring (R := FX) (A := SlopeField n) (B := Base B)
def extendBase {n : ℕ} (B : Ideal (ChartBaseRing n)) : Base B →ₐ[FX] ExtendedBase B :=
  Algebra.TensorProduct.includeRight
def parameterEval {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    MvPolynomial (Fin n) (SlopeField n) →ₐ[SlopeField n] ExtendedBase B :=
  MvPolynomial.aeval (R := SlopeField n) (S₁ := ExtendedBase B)
    (fun i : Fin n => extendBase B (Ideal.Quotient.mk B (MvPolynomial.X (Sum.inr i))))
def parameterDegreeLE {n : ℕ} (B : Ideal (ChartBaseRing n)) (d : ℕ) :
    Submodule (SlopeField n) (ExtendedBase B) :=
  (restrictTotalDegree (Fin n) (SlopeField n) d).map (parameterEval B).toLinearMap
def genericLinear {n : ℕ} (B : Ideal (ChartBaseRing n)) : ExtendedBase B :=
  ∑ i : Fin n, (algebraMap (ParameterGeometry n) (SlopeField n) (MvPolynomial.X i)) •
    extendBase B (Ideal.Quotient.mk B (MvPolynomial.X (Sum.inr i)))
variable {F A : Type} [Field F] [CommRing A] [Algebra F A]
def powerSpan (a : A) (W : Submodule F A) : ℕ → Submodule F A
  | 0 => W
  | k + 1 => W ⊔ (powerSpan a W k).map (LinearMap.mulLeft F a)
instance (a : A) (W : Submodule F A) [Module.Finite F W] (k : ℕ) :
    Module.Finite F (powerSpan a W k) := by
  induction k with
  | zero => exact ‹Module.Finite F W›
  | succ k ih =>
    let := ih
    change Module.Finite F ↥(W ⊔ (powerSpan a W k).map (LinearMap.mulLeft F a))
    infer_instance
instance {n : ℕ} (B : Ideal (ChartBaseRing n)) (d : ℕ) :
    Module.Finite (SlopeField n) (parameterDegreeLE B d) := by
  unfold parameterDegreeLE
  infer_instance
end
end K1_14_2_4_1_5
end
section
set_option maxHeartbeats 2000000
namespace K1_14_2_4_1_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
def c1 : Prop :=
  ∀ (k ι σ : Type) [Field k] (offset : ι) (I : Ideal (MvPolynomial σ k))
    (u : MvPolynomial (Other offset) (MvPolynomial σ k)) (d : ℕ),
    LengthBound (CutField k ι) (PresentedSection offset I u) d ↔
    LengthBound (CutField k ι)
      (GenericFibre k offset (MvPolynomial.map (Ideal.Quotient.mk I) u)) d
def c2 : Prop :=
  ∀ (k ι A B E : Type) [Field k] [CommRing A] [IsDomain A] [Field B] [Field E]
    [Algebra k A] [Algebra k B] [Algebra k E] [Algebra B E] [Module.Finite B E]
    (base : A →ₐ[k] B) (cover : B →ₐ[k] E),
    (let _ := base.toRingHom.toAlgebra; IsFractionRing A B) →
    (∀ x, cover x = algebraMap B E x) →
    ∀ (offset : ι) (u : MvPolynomial (Other offset) A) (d : ℕ),
    LengthBound (CutField k ι) (GenericFibre k offset u) d →
    LengthBound (CutField k ι)
      (GenericFibre k offset (MvPolynomial.map (cover.toRingHom.comp base.toRingHom) u))
      (Module.finrank B E * d)
def c3 : Prop :=
  ∀ (k ι ι' A : Type) [Field k] [CommRing A] [Algebra k A]
    (offset : ι) (offset' : ι') (y : A) (d : ℕ),
    LengthBound (CutField k ι) (GenericFibre k offset (MvPolynomial.C y)) d →
    LengthBound (CutField k ι') (GenericFibre k offset' (MvPolynomial.C y)) d
private theorem section_length_congr {F σ : Type} [Field F] (I : Ideal (MvPolynomial σ F))
    {u v : MvPolynomial σ F} {d : ℕ} (e : u = v)
    (h : LengthBound F (MvPolynomial σ F ⧸ (I ⊔ Ideal.span {u})) d) :
    LengthBound F (MvPolynomial σ F ⧸ (I ⊔ Ideal.span {v})) d := by
  subst v
  exact h
private theorem fibre_length_congr {k ι A : Type} [Field k] [CommRing A] [Algebra k A]
    {offset : ι} {u v : MvPolynomial (Other offset) A} {d : ℕ} (e : u = v)
    (h : LengthBound (CutField k ι) (GenericFibre k offset u) d) :
    LengthBound (CutField k ι) (GenericFibre k offset v) d := by
  subst v
  exact h
private theorem lengthBound_mono {F M : Type} [Field F] [AddCommGroup M] [Module F M] {a b : ℕ}
    (h : LengthBound F M a) (hab : a ≤ b) : LengthBound F M b :=
  ⟨h.1, h.2.trans hab⟩
private theorem image_section_bound (h1 : c1) {k ι σ E : Type} [Field k] [CommRing E]
    [Algebra k E] (offset : ι) (I : Ideal (MvPolynomial σ k))
    (u : MvPolynomial (Other offset) (MvPolynomial σ k))
    (f : (MvPolynomial σ k ⧸ I) →ₐ[k] E) (hf : Function.Injective f)
    {v : MvPolynomial (Other offset) E} {d : ℕ}
    (heq : v = MvPolynomial.map f.toRingHom (MvPolynomial.map (Ideal.Quotient.mk I) u))
    (h : LengthBound (CutField k ι) (GenericFibre k offset v) d) :
    LengthBound (CutField k ι) (PresentedSection offset I u) d := by
  apply (h1 k ι σ offset I u d).mpr
  exact fibre_le_of_injective offset _ f hf (fibre_length_congr heq h)
private theorem parameter_extension_bound (h1 : c1) (h2 : c2) {k ι σ B E : Type}
    [Field k] [Field B] [Field E] [Algebra k B] [Algebra k E]
    [Algebra B E] [Module.Finite B E] (offset : ι) (I : Ideal (MvPolynomial σ k))
    [IsDomain (MvPolynomial σ k ⧸ I)] (base : (MvPolynomial σ k ⧸ I) →ₐ[k] B)
    (cover : B →ₐ[k] E) (hfrac : let _ := base.toRingHom.toAlgebra
      IsFractionRing (MvPolynomial σ k ⧸ I) B)
    (hcover : ∀ x, cover x = algebraMap B E x)
    (u : MvPolynomial (Other offset) (MvPolynomial σ k)) {d : ℕ}
    (h : LengthBound (CutField k ι) (PresentedSection offset I u) d) :
    LengthBound (CutField k ι)
      (GenericFibre k offset (MvPolynomial.map (cover.toRingHom.comp base.toRingHom)
        (MvPolynomial.map (Ideal.Quotient.mk I) u))) (Module.finrank B E * d) := by
  exact h2 k ι (MvPolynomial σ k ⧸ I) B E base cover hfrac hcover offset
    (MvPolynomial.map (Ideal.Quotient.mk I) u) d ((h1 k ι σ offset I u d).mp h)
private def baseParameterForm (n : ℕ) :
    MvPolynomial (Other (none : Option (Fin n))) (ChartBaseRing n) :=
  parameterForm fun i => MvPolynomial.X (Sum.inr i)
private theorem base_parameter_presented {n H : ℕ} (B : Ideal (ChartBaseRing n))
    (h : BaseHeight B H) :
    LengthBound (SliceField n) (PresentedSection (none : Option (Fin n)) B (baseParameterForm n)) H := by
  have hb : cutAtOffset (none : Option (Fin n)) (baseParameterForm n) = baseCut n :=
    cutAtOffset_parameterForm (k := FX) (n := n) Sum.inr
  have hs : LengthBound (SliceField n) (BaseSection B) H := ⟨h.finite, h.length⟩
  exact section_length_congr (F := SliceField n) (σ := Fin 2 ⊕ Fin n)
    (Ideal.map (MvPolynomial.map (algebraMap FX (SliceField n))) B) hb.symm hs
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g n : ℕ}
variable {R : PrimitiveRoot C₀ J g}
private theorem parameter_bound (h1 : c1) (h2 : c2) (A : CoefficientChart R n) {H : ℕ}
    (h : BaseHeight (chartBase A) H) :
    LengthBound (SliceField n) (SectionRing (chartSource A) (parameterCut n)) (g * H) := by
  classical
  let B := BaseRing A
  let F := ConstantSeedX C₀
  let E := RootField R
  have : IsDomain B := baseDomain A
  have : Module.Finite F E := rootFinite R
  let cover : F →ₐ[FX] E :=
    { toRingHom := AdjoinRoot.of (rootPolynomial R)
      commutes' a := (DFunLike.congr_fun (AdjoinRoot.algebraMap_eq' FX (f := rootPolynomial R)).symm a) }
  have hcover (a : F) : cover a = algebraMap F E a := rfl
  let offset : Option (Fin n) := none
  let ui : MvPolynomial (Other offset) (SourceRing n) :=
    parameterForm fun i => MvPolynomial.X (some i)
  let ubq : MvPolynomial (Other offset) B :=
    MvPolynomial.map (R := ChartBaseRing n) (S₁ := B)
      (Ideal.Quotient.mk (chartBase A)) (baseParameterForm n)
  let uiq : MvPolynomial (Other offset) (SourceRing n ⧸ chartSource A) :=
    MvPolynomial.map (R := SourceRing n) (S₁ := SourceRing n ⧸ chartSource A)
      (Ideal.Quotient.mk (chartSource A)) ui
  have hbase := base_parameter_presented (chartBase A) h
  have hE := parameter_extension_bound h1 h2 (k := FX) (ι := Option (Fin n))
    (σ := Fin 2 ⊕ Fin n) (B := F) (E := E) offset (chartBase A) (baseEmbedding A) cover
    (baseFractionRing A) hcover (baseParameterForm n) hbase
  have hmap : MvPolynomial.map (cover.toRingHom.comp (baseEmbedding A).toRingHom) ubq =
      MvPolynomial.map (imageEmbedding A).toRingHom uiq := by
    simp only [ubq, uiq, baseParameterForm, ui, parameterForm, map_sum, map_mul,
      MvPolynomial.map_X, MvPolynomial.map_C]
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg (fun a : E =>
      (MvPolynomial.X ⟨some i, Option.some_ne_none i⟩ : MvPolynomial (Other offset) E) *
        MvPolynomial.C a)
    change algebraMap F E (baseEmbedding A (Ideal.Quotient.mk (chartBase A) (MvPolynomial.X (Sum.inr i)))) =
      imageEmbedding A (Ideal.Quotient.mk (chartSource A) (MvPolynomial.X (some i)))
    simp [imageEmbedding, baseEmbedding_mk, chartRootMap, chartBaseMap]
    exact DFunLike.congr_fun (AdjoinRoot.algebraMap_eq (f := rootPolynomial R))
      (insertConstant C₀ (A.coordinate i))
  have hi := image_section_bound h1 offset (chartSource A) ui (imageEmbedding A)
    (imageEmbedding_injective A) hmap hE
  have hc : cutAtOffset offset ui = parameterCut n := cutAtOffset_parameterForm some
  exact section_length_congr _ hc (lengthBound_mono hi (Nat.mul_le_mul_right H (root_degree R).le))
private theorem ordinate_bound (h1 : c1) (h2 : c2) (h3 : c3) (A : CoefficientChart R n)
    {H : ℕ} (hf : Module.Finite SeedField (RootYSection J))
    (hd : Module.finrank SeedField (RootYSection J) ≤ H) :
    LengthBound (SliceField n) (SectionRing (chartSource A) (ordinateCut n)) H := by
  let B := RootAmbient ⧸ J
  let E := RootField R
  have : IsDomain B := originalDomain R
  let cover := AlgHom.id FX E
  have hcover (a : E) : cover a = algebraMap E E a := rfl
  let offset : Option (Fin n) := none
  let y : B := Ideal.Quotient.mk J (MvPolynomial.X (2 : Fin 3))
  let v : RootAmbient := MvPolynomial.X 2
  let w : SourceRing n := MvPolynomial.X none
  let wi : MvPolynomial (Other offset) (SourceRing n ⧸ chartSource A) :=
    MvPolynomial.map (R := SourceRing n) (S₁ := SourceRing n ⧸ chartSource A)
      (Ideal.Quotient.mk (chartSource A)) (MvPolynomial.C w)
  have hroot : LengthBound SeedField (PresentedSection (1 : Fin 2) J (MvPolynomial.C v)) H := by
    have hc : cutAtOffset (1 : Fin 2) (MvPolynomial.C v) = ySection (2 : Fin 3) :=
      cutAtOffset_ordinate 1 2
    have hs : LengthBound SeedField (RootYSection J) H := ⟨hf, hd⟩
    exact section_length_congr (Ideal.map (MvPolynomial.map (algebraMap FX SeedField)) J) hc.symm hs
  have hB : LengthBound SeedField (GenericFibre FX (1 : Fin 2) (MvPolynomial.C y)) H :=
    fibre_length_congr (MvPolynomial.map_C _ v)
      ((h1 FX (Fin 2) (Fin 3) 1 J (MvPolynomial.C v) H).mp hroot)
  have hB' := h3 FX (Fin 2) (Option (Fin n)) B 1 offset y H hB
  have hE := h2 FX (Option (Fin n)) B E E (originalEmbedding R) cover (originalFractionRing R)
    hcover offset (MvPolynomial.C y) H hB'
  have hy : (cover.toRingHom.comp (originalEmbedding R).toRingHom) y =
      (imageEmbedding A).toRingHom (Ideal.Quotient.mk (chartSource A) w) := by
    change originalEmbedding R y = imageEmbedding A (Ideal.Quotient.mk (chartSource A) w)
    simp [imageEmbedding, originalEmbedding, chartRootMap, genericRootMap, y, w]
  have heq : MvPolynomial.map (cover.toRingHom.comp (originalEmbedding R).toRingHom) (MvPolynomial.C y) =
      MvPolynomial.map (imageEmbedding A).toRingHom wi := by
    simp only [wi, MvPolynomial.map_C, hy]
  have hi := image_section_bound h1 offset (chartSource A) (MvPolynomial.C w) (imageEmbedding A)
    (imageEmbedding_injective A) heq hE
  have hc : cutAtOffset offset (MvPolynomial.C w) = ordinateCut n := cutAtOffset_ordinate offset none
  exact section_length_congr _ hc (lengthBound_mono hi (by rw [Module.finrank_self, one_mul]))
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_14_2_4_1.c4 := by
  intro C₀ hC₀ J g H n R A hbase hfinite hlength
  have hp := parameter_bound h1 h2 A hbase
  have hy := ordinate_bound h1 h2 h3 A hfinite hlength
  exact ⟨image_dimension A hbase.dimension, ⟨hp.1, hp.2, hy.1, hy.2⟩⟩
end
end K1_14_2_4_1_4
end
section
set_option autoImplicit false
namespace K1_14_2_4_1_5
noncomputable section
open K1 K1_14 K1_14_2_4_1 MvPolynomial
open scoped TensorProduct
private theorem interpolate {F A ι : Type} [Field F] [CommRing A] [Algebra F A]
    [Fintype ι] [DecidableEq ι] (f : ι → A →ₐ[F] F) (hf : Function.Injective f) :
    ∃ r : ι → A, ∀ i j, f j (r i) = if i = j then 1 else 0 := by
  classical
  have hsep (i j : ι) : ∃ x : A, f i x = 1 ∧ (i ≠ j → f j x = 0) := by
    by_cases h : i = j
    · exact ⟨1, map_one _, fun hn => (hn h).elim⟩
    · have hd : ∃ y : A, f i y ≠ f j y := by
        by_contra! hn
        exact h (hf (AlgHom.ext hn))
      obtain ⟨y, hy⟩ := hd
      let d := f i y - f j y
      have hd₀ : d ≠ 0 := sub_ne_zero.mpr hy
      refine ⟨algebraMap F A d⁻¹ * (y - algebraMap F A (f j y)), ?_, ?_⟩
      · simpa only [map_mul, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply] using
          inv_mul_cancel₀ hd₀
      · intro _
        simp
  choose s hs using hsep
  refine ⟨fun i => ∏ k ∈ Finset.univ.erase i, s i k, ?_⟩
  intro i j
  rw [map_prod]
  split_ifs with hij
  · subst j
    exact Finset.prod_eq_one fun k _ => (hs i k).1
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
      ((hs i j).2 hij)
private theorem independent_powers {F A ι : Type} [Field F] [CommRing A] [Algebra F A]
    [IsDomain A] [Fintype ι] [DecidableEq ι] (f : ι → A →ₐ[F] F) (r : ι → A)
    (hr : ∀ i j, f j (r i) = if i = j then 1 else 0)
    (a : A) (ha : a ≠ 0) (hf : ∀ i, f i a = 0) (k : ℕ) :
    LinearIndependent F (fun ij : Fin (k + 1) × ι => a ^ (ij.1 : ℕ) * r ij.2) := by
  induction k with
  | zero =>
    refine Fintype.linearIndependent_iff.mpr fun c hc ⟨i, j⟩ => ?_
    have hi : i = 0 := Fin.eq_zero _
    subst i
    have hh := congrArg (f j) hc
    simpa [Fintype.sum_prod_type, hr, eq_comm] using hh
  | succ k ih =>
    refine Fintype.linearIndependent_iff.mpr fun c hc ⟨i, j⟩ => ?_
    have hsplit :
        (∑ u : ι, c (0, u) • r u) +
            a * (∑ ij : Fin (k + 1) × ι, c (ij.1.succ, ij.2) • (a ^ (ij.1 : ℕ) * r ij.2)) = 0 := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_succ] at hc
      simpa only [Fintype.sum_prod_type, Fin.val_zero, Fin.val_succ, pow_zero, one_mul,
        pow_succ', Finset.mul_sum, mul_smul_comm, mul_assoc] using hc
    have hc₀ (u : ι) : c (0, u) = 0 := by
      have hh := congrArg (f u) hsplit
      simpa [hf, hr, eq_comm] using hh
    have htail : (∑ ij : Fin (k + 1) × ι,
        c (ij.1.succ, ij.2) • (a ^ (ij.1 : ℕ) * r ij.2)) = 0 := by
      have hz := hsplit
      simp only [hc₀, zero_smul, Finset.sum_const_zero, zero_add] at hz
      exact (mul_eq_zero.mp hz).resolve_left ha
    refine Fin.cases (hc₀ j) (fun i => ?_) i
    exact Fintype.linearIndependent_iff.mp ih (fun ij => c (ij.1.succ, ij.2)) htail (i, j)
theorem exists_independent_mark_powers {n : ℕ} (B : Ideal (ChartBaseRing n)) [B.IsPrime]
    (q : ParameterGeometry n) (hq : parameterInclusion n q ∉ B)
    (V : Finset K) (pt : K → Fin 2 ⊕ Fin n → FX) (hinj : Set.InjOn pt (V : Set K))
    (hpt : ∀ γ ∈ V, pt γ ∈ zeroLocus FX B ∧ aeval (pt γ) (parameterInclusion n q) = 0) :
    ∃ r : (↥V) → Base B, ∀ k,
      LinearIndependent (SlopeField n) (fun ij : Fin (k + 1) × (↥V) =>
        extendBase B ((Ideal.Quotient.mk B (parameterInclusion n q)) ^ (ij.1 : ℕ) * r ij.2)) := by
  classical
  let pts : (↥V) → zeroLocus FX B := fun i => ⟨pt i.1, (hpt i.1 i.2).1⟩
  let e := zeroLocusPointHom B ∘ pts
  have he : Function.Injective e := (zeroLocusPointHom_injective B).comp (fun i j h =>
    Subtype.ext (hinj i.2 j.2 (congrArg Subtype.val h)))
  obtain ⟨r, hr⟩ := interpolate e he
  refine ⟨r, fun k => ?_⟩
  let a := Ideal.Quotient.mk B (parameterInclusion n q)
  have ha : a ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hq
  have hz (i : (↥V)) : e i a = 0 := (hpt i.1 i.2).2
  exact Module.Flat.linearIndependent_one_tmul (S := SlopeField n)
    (independent_powers e r hr a ha hz k)
theorem parameterEval_map {n : ℕ} (B : Ideal (ChartBaseRing n)) (q : ParameterGeometry n) :
    parameterEval B (MvPolynomial.map (algebraMap FX (SlopeField n)) q) =
      extendBase B (Ideal.Quotient.mk B (parameterInclusion n q)) := by
  let f : ParameterGeometry n →+* ExtendedBase B :=
    (parameterEval B).toRingHom.comp (MvPolynomial.map (algebraMap FX (SlopeField n)))
  let g : ParameterGeometry n →+* ExtendedBase B :=
    (extendBase B).toRingHom.comp ((Ideal.Quotient.mk B).comp (parameterInclusion n))
  have h : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro x
      change parameterEval B (MvPolynomial.map (algebraMap FX (SlopeField n)) (MvPolynomial.C x)) =
        extendBase B (Ideal.Quotient.mk B (MvPolynomial.rename Sum.inr (MvPolynomial.C x)))
      rw [MvPolynomial.map_C, MvPolynomial.rename_C, parameterEval, MvPolynomial.aeval_C]
      change algebraMap (SlopeField n) (ExtendedBase B) (algebraMap FX (SlopeField n) x) =
        extendBase B (algebraMap FX (Base B) x)
      rw [AlgHom.commutes]
      rfl
    · intro i
      change parameterEval B (MvPolynomial.map (algebraMap FX (SlopeField n))
        (MvPolynomial.X i)) =
        extendBase B (Ideal.Quotient.mk B (MvPolynomial.rename Sum.inr (MvPolynomial.X i)))
      rw [MvPolynomial.map_X, MvPolynomial.rename_X, parameterEval, MvPolynomial.aeval_X]
  exact DFunLike.congr_fun h q
theorem parameterClass_mem {n d : ℕ} (B : Ideal (ChartBaseRing n)) (q : ParameterGeometry n)
    (h : q.totalDegree ≤ d) :
    extendBase B (Ideal.Quotient.mk B (parameterInclusion n q)) ∈ parameterDegreeLE B d := by
  refine ⟨MvPolynomial.map (algebraMap FX (SlopeField n)) q, ?_, parameterEval_map B q⟩
  exact (mem_restrictTotalDegree _ _ _).2 (le_trans (by
    rw [totalDegree_eq, totalDegree_eq]
    exact Finset.sup_mono (support_map_subset _ _)) h)
theorem map_powerSpan_le {F A : Type} [Field F] [CommRing A] [Algebra F A]
    (a b : A) {W U : Submodule F A} (h : W.map (LinearMap.mulLeft F b) ≤ U) (k : ℕ) :
    (powerSpan a W k).map (LinearMap.mulLeft F b) ≤ powerSpan a U k := by
  induction k with
  | zero => exact h
  | succ k ih =>
    change (W ⊔ (powerSpan a W k).map (LinearMap.mulLeft F a)).map (LinearMap.mulLeft F b) ≤
      U ⊔ (powerSpan a U k).map (LinearMap.mulLeft F a)
    rw [Submodule.map_sup, ← Submodule.map_comp]
    refine sup_le (h.trans le_sup_left) ?_
    rw [show (LinearMap.mulLeft F b).comp (LinearMap.mulLeft F a) =
        (LinearMap.mulLeft F a).comp (LinearMap.mulLeft F b) by
      ext y
      exact mul_left_comm b a y, Submodule.map_comp]
    exact (Submodule.map_mono ih).trans le_sup_right
end
end K1_14_2_4_1_5
end
section
namespace K1_14_2_4_1_3_3_3
noncomputable section
open K1_14_2_4_1_3_3
open scoped Polynomial RatFunc
attribute [local instance] Polynomial.algebra
theorem mapSpare_polynomial {E F : Type} [Field E] [Field F]
    (f : E →+* F) (p : E[X]) :
    mapSpare f (algebraMap E[X] (SpareField E) p) =
      algebraMap F[X] (SpareField F) (p.map f) :=
  by
    unfold mapSpare IsFractionRing.map
    rw [IsLocalization.map_eq]
    rfl
theorem mapSpare_comp {E F G : Type} [Field E] [Field F] [Field G]
    (f : E →+* F) (h : F →+* G) :
    (mapSpare h).comp (mapSpare f) = mapSpare (h.comp f) := by
  apply IsFractionRing.ringHom_ext (A := E[X])
  intro p
  simp only [RingHom.comp_apply, mapSpare_polynomial, Polynomial.map_map]
theorem degree_mapSpare {E F : Type} [Field E] [Field F] (f : E →+* F) :
    fieldDegree (mapSpare f) = fieldDegree f := by
  let : Algebra E F := f.toAlgebra
  let : Algebra (SpareField E) (SpareField F) := (mapSpare f).toAlgebra
  let e := FractionRing.algEquiv E[X] (RatFunc E)
  let e' := FractionRing.algEquiv F[X] (RatFunc F)
  have h : (algebraMap (RatFunc E) (RatFunc F)).comp e.toRingHom =
      e'.toRingHom.comp (mapSpare f) := by
    apply IsFractionRing.ringHom_ext (A := E[X])
    intro p
    simp only [RingHom.comp_apply, mapSpare_polynomial]
    change algebraMap (RatFunc E) (RatFunc F) (e (algebraMap E[X] (SpareField E) p)) =
      e' (algebraMap F[X] (SpareField F) (p.map f))
    rw [e.commutes, e'.commutes, ← IsScalarTower.algebraMap_apply E[X] (RatFunc E) (RatFunc F),
      IsScalarTower.algebraMap_apply E[X] F[X] (RatFunc F)]
    rfl
  calc
    fieldDegree (mapSpare f) = Module.finrank (RatFunc E) (RatFunc F) :=
      Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv e'.toRingEquiv h
    _ = Module.finrank E[X] F[X] := IsFractionRing.finrank_eq E[X] (RatFunc E) F[X] (RatFunc F)
    _ = fieldDegree f := congrArg Cardinal.toNat (rank_polynomial_polynomial E F)
theorem degree_algebraMap {E F : Type} [Field E] [Field F] [Algebra E F] :
    fieldDegree (algebraMap E F) = Module.finrank E F := by
  unfold fieldDegree
  rw [toAlgebra_algebraMap]
theorem degree_comp {E F G : Type} [Field E] [Field F] [Field G]
    (f : E →+* F) (h : F →+* G) :
    fieldDegree f * fieldDegree h = fieldDegree (h.comp f) := by
  let : Algebra E F := f.toAlgebra
  let : Algebra F G := h.toAlgebra
  let : Algebra E G := (h.comp f).toAlgebra
  let : IsScalarTower E F G :=
    IsScalarTower.of_algebraMap_eq (R := E) (S := F) (A := G) fun _ => rfl
  exact Module.finrank_mul_finrank E F G
end
end K1_14_2_4_1_3_3_3
end
section
namespace K1_14_2_4_1_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open scoped Polynomial BigOperators
set_option maxHeartbeats 800000
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g : ℕ}
variable (R : PrimitiveRoot C₀ J g)
def width : ℕ :=
  (Finset.univ.sup fun j : Fin (g + 1) => (R.equation.coeff j).natDegree) + 1
abbrev size := (g + 1) * width R
def coeff (i : Fin (size R)) : ConstantSeedField C₀ :=
  let jk := finProdFinEquiv.symm i
  (R.equation.coeff jk.1).coeff jk.2
private theorem coeff_natDegree_lt (j : Fin (g + 1)) :
    (R.equation.coeff j).natDegree < width R :=
  Nat.lt_succ_of_le (Finset.le_sup (f := fun i : Fin (g + 1) =>
    (R.equation.coeff i).natDegree) (Finset.mem_univ j))
theorem coeff_nonzero : ∃ i, coeff R i ≠ 0 := by
  have hR : R.equation ≠ 0 := by
    intro h
    exact R.irreducible.ne_zero (by simp [h])
  let j : Fin (g + 1) := ⟨R.equation.natDegree, by rw [R.degree]; omega⟩
  let k : Fin (width R) := ⟨(R.equation.coeff j).natDegree, coeff_natDegree_lt R j⟩
  refine ⟨finProdFinEquiv (j, k), ?_⟩
  simpa [coeff, j, k, Polynomial.coeff_natDegree] using
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hR)
private def tuplePolynomial {F : Type*} [Semiring F] {n : ℕ} (v : Fin n → F) : F[X] :=
  ∑ i : Fin n, Polynomial.monomial (i : ℕ) (v i)
private theorem tupleCoeff {F : Type*} [Semiring F] {n : ℕ} (v : Fin n → F) (k : ℕ) :
    (tuplePolynomial v).coeff k = if h : k < n then v ⟨k, h⟩ else 0 := by
  rw [tuplePolynomial, Polynomial.finsetSum_coeff]
  split_ifs with h
  · refine (Finset.sum_eq_single (⟨k, h⟩ : Fin n) ?_ (fun hn => (hn (Finset.mem_univ _)).elim)).trans ?_
    · intro b _ hb
      exact Polynomial.coeff_monomial_of_ne _ (fun he => hb (Fin.ext he.symm))
    · exact Polynomial.coeff_monomial_same _ _
  · exact Finset.sum_eq_zero (fun b _ =>
      Polynomial.coeff_monomial_of_ne _ (fun he => h (he.symm ▸ b.isLt)))
private theorem tupleCoeff_lt {F : Type*} [Semiring F] {n : ℕ} (v : Fin n → F)
    {k : ℕ} (h : k < n) : (tuplePolynomial v).coeff k = v ⟨k, h⟩ := by
  rw [tupleCoeff, dite_eq_left h]
private theorem tupleCoeff_ge {F : Type*} [Semiring F] {n : ℕ} (v : Fin n → F)
    {k : ℕ} (h : n ≤ k) : (tuplePolynomial v).coeff k = 0 := by
  rw [tupleCoeff, dite_eq_right (Nat.not_lt.mpr h)]
private def chartEquation : FamilyEquation (size R) :=
  tuplePolynomial (n := g + 1) fun j =>
    tuplePolynomial (n := width R) fun k => MvPolynomial.X (finProdFinEquiv (j, k))
private theorem chartEquation_degree : FamilyDegree (chartEquation R) g := by
  refine ⟨Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun _ h => tupleCoeff_ge _ h), ?_⟩
  intro j k
  unfold chartEquation
  by_cases hj : j < g + 1
  · rw [tupleCoeff_lt _ hj]
    by_cases hk : k < width R
    · simp [tupleCoeff_lt _ hk]
    · simp [tupleCoeff_ge _ (Nat.le_of_not_gt hk)]
  · simp [tupleCoeff_ge _ (Nat.le_of_not_gt hj)]
def chartDenominator (ℓ : Fin (size R) → L) : ConstantSeedField C₀ :=
  ∑ i, constToSeed C₀ (ℓ i) * coeff R i
def makeChart (ℓ : Fin (size R) → L) (h : chartDenominator R ℓ ≠ 0) :
    CoefficientChart R (size R) where
  coordinate i := coeff R i / chartDenominator R ℓ
  scale := Units.mk0 (chartDenominator R ℓ)⁻¹ (inv_ne_zero h)
  equation := chartEquation R
  degree := chartEquation_degree R
  generic_eq := by
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro k
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_C_mul,
      Units.val_mk0]
    by_cases hj : j < g + 1
    · let j' : Fin (g + 1) := ⟨j, hj⟩
      rw [chartEquation, tupleCoeff_lt _ hj]
      by_cases hk : k < width R
      · rw [tupleCoeff_lt _ hk]
        rw [MvPolynomial.eval₂Hom_X']
        simp only [coeff, Equiv.symm_apply_apply, div_eq_mul_inv]
        exact mul_comm _ _
      · rw [tupleCoeff_ge _ (Nat.le_of_not_gt hk),
          Polynomial.coeff_eq_zero_of_natDegree_lt
            ((coeff_natDegree_lt R j').trans_le (Nat.le_of_not_gt hk))]
        rw [map_zero, mul_zero]
    · have hr : R.equation.coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [R.degree]; omega)
      rw [chartEquation, tupleCoeff_ge _ (Nat.le_of_not_gt hj),
        Polynomial.coeff_zero, map_zero, hr, Polynomial.coeff_zero, mul_zero]
  coordinates_are_coefficients := by
    intro i
    let jk := (finProdFinEquiv (m := g + 1) (n := width R)).symm i
    refine ⟨jk.1, jk.2, ?_⟩
    simp only [coeff, jk, div_eq_mul_inv, Polynomial.coeff_C_mul, Units.val_mk0]
    exact mul_comm _ _
  normalized := by
    refine ⟨ℓ, ?_⟩
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    exact div_self h
private theorem exists_pivot {F : Type*} [Field F] (V : ValuationSubring F)
    {n : ℕ} (a : Fin n → F) (ha : ∃ i, a i ≠ 0) :
    ∃ j, a j ≠ 0 ∧ ∀ i, a i / a j ∈ V := by
  classical
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (a i))
    ⟨i, Finset.mem_univ _⟩
  have hpos := (Valuation.pos_iff V.valuation).2 hi
  have hjpos := hpos.trans_le (hj i (Finset.mem_univ i))
  have hjn : a j ≠ 0 := (Valuation.pos_iff V.valuation).1 hjpos
  refine ⟨j, hjn, fun i => (V.valuation_le_one_iff _).1 ?_⟩
  rw [map_div₀, div_le_iff₀ hjpos, one_mul]
  exact hj i (Finset.mem_univ i)
private theorem tupleEval {F : Type*} [CommSemiring F] {n : ℕ}
    (a : Fin n → F) (x : F) :
    (tuplePolynomial a).eval x = ∑ i : Fin n, x ^ (i : ℕ) * a i := by
  rw [tuplePolynomial, Polynomial.eval_finsetSum]
  simp [Polynomial.eval_monomial, mul_comm]
private theorem tuple_ne_zero {F : Type*} [Semiring F] {n : ℕ}
    (a : Fin n → F) (ha : ∃ i, a i ≠ 0) : tuplePolynomial a ≠ 0 := by
  obtain ⟨i, hi⟩ := ha
  intro h
  have hc := congrArg (fun p : F[X] => p.coeff i) h
  exact hi (by simpa only [tupleCoeff_lt _ i.isLt, Polynomial.coeff_zero]
    using hc)
private theorem linearForm {ι : Type*} [Finite ι] {n : ℕ}
    (a : Fin n → ConstantSeedField C₀) (ha : ∃ i, a i ≠ 0)
    (b : ι → Fin n → L) (hb : ∀ j, ∃ i, b j i ≠ 0) :
    ∃ ℓ : Fin n → L, (∑ i, constToSeed C₀ (ℓ i) * a i) ≠ 0 ∧
      ∀ j, (∑ i, ℓ i * b j i) ≠ 0 := by
  have hF : ∀ᶠ x : L in Filter.cofinite,
      (tuplePolynomial a).eval (constToSeed C₀ x) ≠ 0 := by
    have hf := ((Polynomial.finite_setOfPred_isRoot (tuple_ne_zero a ha)).preimage
      (constToSeed C₀).injective.injOn).compl_mem_cofinite
    exact Filter.Eventually.mono hf (fun _ h => by
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot] using h)
  have hL : ∀ᶠ x : L in Filter.cofinite, ∀ j,
      (tuplePolynomial (b j)).eval x ≠ 0 :=
    Filter.eventually_all.2 fun j => Polynomial.eventually_eval_ne_zero_cofinite
      (tuple_ne_zero (b j) (hb j))
  obtain ⟨x, hx, hy⟩ := (hF.and hL).exists
  refine ⟨fun i => x ^ (i : ℕ), ?_, ?_⟩
  · rw [tupleEval] at hx
    simpa only [map_pow] using hx
  · intro j
    rw [← tupleEval]
    exact hy j
theorem commonChart {ι : Type*} [Finite ι] (z : ι → K) (S : ι → K[X])
    (M : ∀ j, MarkLift R (z j) (S j)) (hM : ∀ j, (M j).ConstantResidues) :
    ∃ A : CoefficientChart R (size R),
      ∀ j i, seedInRoot R (A.coordinate i) ∈ (M j).V := by
  classical
  let a (i : Fin (size R)) := seedInRoot R (coeff R i)
  have ha : ∃ i, a i ≠ 0 := by
    obtain ⟨i, hi⟩ := coeff_nonzero R
    exact ⟨i, (map_ne_zero (seedInRoot R)).2 hi⟩
  choose pivot hp hv using fun j => exists_pivot (M j).V a ha
  let u (j : ι) (i : Fin (size R)) : (M j).V := ⟨a i / a (pivot j), hv j i⟩
  have hu (j : ι) (i : Fin (size R)) :
      ∃ k : L, IsLocalRing.residue (M j).V (u j i) =
        IsLocalRing.residue (M j).V ((M j).constant k) := by
    have he : seedInRoot R (coeff R i / coeff R (pivot j)) = a i / a (pivot j) := by
      simp [a]
    obtain ⟨k, hk⟩ := hM j (coeff R i / coeff R (pivot j)) (by rw [he]; exact hv j i)
    have hsub : u j i = ⟨seedInRoot R (coeff R i / coeff R (pivot j)),
        by rw [he]; exact hv j i⟩ := Subtype.ext he.symm
    exact ⟨k, hsub ▸ hk⟩
  choose b hb using hu
  have hb₀ (j : ι) : ∃ i, b j i ≠ 0 := by
    refine ⟨pivot j, ?_⟩
    have hu1 : u j (pivot j) = 1 := Subtype.ext (div_self (hp j))
    intro hzero
    simpa [hzero, hu1] using hb j (pivot j)
  obtain ⟨ℓ, hℓ, hℓb⟩ := linearForm (coeff R) (coeff_nonzero R) b hb₀
  refine ⟨makeChart R ℓ hℓ, ?_⟩
  intro j i
  let d : (M j).V := ∑ k, (M j).constant (ℓ k) * u j k
  have hd : IsUnit d := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    have he := (map_ne_zero ((IsLocalRing.residue (M j).V).comp (M j).constant)).2 (hℓb j)
    simpa [d, hb j, map_sum, map_mul, RingHom.comp_apply] using he
  have hconst (k : L) : ((M j).constant k : RootField R) =
      seedInRoot R (constToSeed C₀ k) := by
    change ((M j).V.toSubring.subtype.comp (M j).ambient)
      (MvPolynomial.C (algebraMap L FX k)) = _
    rw [(M j).generic_eq]
    simp only [generic, RingHom.comp_apply, genericRootMap, MvPolynomial.eval₂Hom_C,
      AdjoinRoot.mk_C]
    change AdjoinRoot.of (rootEquation R) (extendX C₀ (algebraMap L FX k)) = _
    unfold seedInRoot
    rw [RingHom.comp_apply]
    congr 1
    rw [IsScalarTower.algebraMap_apply L L[X] FX]
    unfold extendX IsFractionRing.map
    rw [IsLocalization.map_eq]
    simp [insertConstant, insertX]
  have hdval : (d : RootField R) = seedInRoot R (chartDenominator R ℓ) / a (pivot j) := by
    change (M j).V.toSubring.subtype d = _
    simp only [d, chartDenominator, map_sum, map_mul, Finset.sum_div, mul_div_assoc]
    exact Finset.sum_congr rfl (fun k _ => congrArg₂ (· * ·) (hconst (ℓ k)) rfl)
  have hdv := ((M j).V.valuation_eq_one_iff d).1 hd
  rw [hdval] at hdv
  have hcancel : seedInRoot R ((makeChart R ℓ hℓ).coordinate i) =
      (a i / a (pivot j)) / (seedInRoot R (chartDenominator R ℓ) / a (pivot j)) := by
    change seedInRoot R (coeff R i / chartDenominator R ℓ) = _
    rw [map_div₀]
    exact (div_div_div_cancel_right₀ (hp j) _ _).symm
  apply ((M j).V.valuation_le_one_iff _).1
  rw [hcancel, map_div₀, hdv, div_one]
  exact (M j).V.valuation_le_one (u j i)
end
end K1_14_2_4_1_2
end
section
namespace K1_14_2_4_1_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open scoped Polynomial
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g : ℕ}
variable {R : PrimitiveRoot C₀ J g}
private def abscissa : FX := algebraMap L[X] FX Polynomial.X
private theorem extend_abscissa : extendX C₀ abscissa = insertX C₀ Polynomial.X := by
  unfold extendX abscissa IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertX]
private theorem extend_constant (a : L) :
    extendX C₀ (algebraMap L FX a) = insertConstant C₀ (constToSeed C₀ a) := by
  rw [IsScalarTower.algebraMap_apply L L[X] FX]
  unfold extendX IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertConstant, insertX]
private def parameterMap (n : ℕ) : ParameterRing n →+* SourceRing n :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap L FX))
    (fun i => MvPolynomial.X (some i))
private def equationInSource {n : ℕ} (A : CoefficientChart R n) : SourceRing n :=
  A.equation.eval₂ (Polynomial.eval₂RingHom (parameterMap n) (MvPolynomial.C abscissa))
    (MvPolynomial.X none)
private theorem equation_mem_source {n : ℕ} (A : CoefficientChart R n) :
    equationInSource A ∈ chartSource A := by
  let F := ConstantSeedX C₀
  let e := MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate
  have hp : (chartRootMap A).comp (parameterMap n) =
      (Polynomial.C : F →+* F[X]).comp ((insertConstant C₀).comp e) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [parameterMap, chartRootMap, extend_constant, e]
    · intro i
      simp [parameterMap, chartRootMap, e]
  have hx : (chartRootMap A).comp (Polynomial.eval₂RingHom (parameterMap n)
      (MvPolynomial.C abscissa)) =
      (Polynomial.C : F →+* F[X]).comp ((insertX C₀).comp (Polynomial.mapRingHom e)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [insertConstant] using RingHom.congr_fun hp a
    · simp [chartRootMap, extend_abscissa]
  change chartRootMap A (equationInSource A) ∈ Ideal.span {rootEquation R}
  rw [equationInSource, Polynomial.hom_eval₂, hx]
  have hy : chartRootMap A (MvPolynomial.X none) = Polynomial.X := by simp [chartRootMap]
  rw [hy]
  change (A.equation.map ((insertX C₀).comp (Polynomial.mapRingHom e))) ∈ _
  rw [← Polynomial.map_map, A.generic_eq, Polynomial.map_mul, Polynomial.map_C]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
private theorem equation_eval_mark {n : ℕ} (A : CoefficientChart R n)
    (t : Fin n → L) (S : K[X]) :
    MvPolynomial.eval (markedPoint t S) (equationInSource A) =
      algebraMap L[X] FX ((specialize A.equation t).eval (liftPoly S)) := by
  let e := MvPolynomial.eval t
  have hp : (MvPolynomial.eval (markedPoint t S)).comp (parameterMap n) =
      (algebraMap L FX).comp e := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [parameterMap, e]
    · intro i
      simp [parameterMap, markedPoint, e]
  have hx : (MvPolynomial.eval (markedPoint t S)).comp
      (Polynomial.eval₂RingHom (parameterMap n) (MvPolynomial.C abscissa)) =
      (algebraMap L[X] FX).comp (Polynomial.mapRingHom e) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C]
      rw [← RingHom.comp_apply, hp, RingHom.comp_apply, IsScalarTower.algebraMap_apply L L[X] FX]
      rfl
    · simp [abscissa]
  rw [equationInSource, Polynomial.hom_eval₂, hx, MvPolynomial.eval_X, markedPoint, atX]
  rw [specialize, Polynomial.eval_map, Polynomial.hom_eval₂]
section Lift
variable {z : K} {S : K[X]} (M : MarkLift R z S)
local notation "res" => IsLocalRing.residue M.V
local notation "inc" => M.V.toSubring.subtype
private def seedLift (i : Fin 2) : M.V :=
  M.ambient (MvPolynomial.X (Fin.castLE (by decide : 2 ≤ 3) i))
private def ordinateLift : M.V := M.ambient (MvPolynomial.X 2)
private theorem generic_fx (x : FX) :
    inc (M.fx x) = AdjoinRoot.of (rootEquation R) (extendX C₀ x) := by
  change ((inc).comp M.ambient) (MvPolynomial.C x) = _
  rw [M.generic_eq]
  simp [generic, genericRootMap]
private theorem generic_seed (i : Fin 2) :
    inc (seedLift M i) = seedInRoot R (seedCoordinate C₀ i) := by
  change ((inc).comp M.ambient) (MvPolynomial.X (Fin.castLE (by decide : 2 ≤ 3) i)) = _
  rw [M.generic_eq]
  fin_cases i <;> simp [generic, genericRootMap, seedInRoot]
private theorem generic_y : inc (ordinateLift M) = AdjoinRoot.root (rootEquation R) := by
  change ((inc).comp M.ambient) (MvPolynomial.X 2) = _
  rw [M.generic_eq]
  simp [generic, genericRootMap]
private theorem seedVector (a b y : FX) (i : Fin 2) :
    (![a, b, y] : Fin 3 → FX) (Fin.castLE (by decide : 2 ≤ 3) i) = ![a, b] i := by
  fin_cases i <;> rfl
private theorem marked_seed (i : Fin 2) :
    res (seedLift M i) = ((res).comp M.fx)
      (![seedEmbedding z, (seedEmbedding z) ^ p] i) := by
  change ((res).comp M.ambient) (MvPolynomial.X (Fin.castLE (by decide : 2 ≤ 3) i)) = _
  rw [M.marked_eq]
  simp only [RingHom.comp_apply, rootMarkHom, MvPolynomial.eval_X]
  change res (M.fx (![seedEmbedding z, (seedEmbedding z) ^ p, atX S]
    (Fin.castLE (by decide : 2 ≤ 3) i))) =
    res (M.fx (![seedEmbedding z, (seedEmbedding z) ^ p] i))
  rw [seedVector]
private theorem marked_y : res (ordinateLift M) = ((res).comp M.fx) (atX S) := by
  change ((res).comp M.ambient) (MvPolynomial.X 2) = _
  rw [M.marked_eq]
  simp [rootMarkHom, MarkLift.fx]
private theorem eval_eq_zero {F E Q O σ : Type*} [Field F] [Field E]
    [CommRing Q] [CommRing O] (inj : O →+* Q) (hi : Function.Injective inj)
    (r : O →+* E) (k : F →+* E) (u : MvPolynomial σ F →+* O)
    (pt : σ → F) (he : r.comp u = k.comp (MvPolynomial.eval pt))
    (f : MvPolynomial σ F) (hf : (inj.comp u) f = 0) :
    MvPolynomial.eval pt f = 0 := by
  have hz : u f = 0 := hi (by simpa only [RingHom.comp_apply, map_zero] using hf)
  apply k.injective
  simpa only [RingHom.comp_apply, hz, map_zero] using (RingHom.congr_fun he f).symm
variable {n : ℕ} (A : CoefficientChart R n)
variable (q : Fin n → M.V) (t : Fin n → L)
private theorem baseMark_mem
    (hg : ∀ i, inc (q i) = seedInRoot R (A.coordinate i))
    (ht : ∀ i, res (q i) = res (M.constant (t i))) :
    baseMark z t ∈ MvPolynomial.zeroLocus FX (chartBase A) := by
  let ev := MvPolynomial.eval₂Hom M.fx (Sum.elim (seedLift M) q)
  have hgen : (inc).comp ev = (AdjoinRoot.of (rootEquation R)).comp (chartBaseMap A) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simpa [ev, chartBaseMap] using generic_fx M x
    · intro i
      cases i with
      | inl j => simpa [ev, chartBaseMap, seedInRoot] using generic_seed M j
      | inr j => simpa [ev, chartBaseMap, seedInRoot] using hg j
  have hmark : (res).comp ev = ((res).comp M.fx).comp (MvPolynomial.eval (baseMark z t)) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [ev]
    · intro i
      cases i with
      | inl j => simpa [ev, baseMark] using marked_seed M j
      | inr j => simpa [ev, MarkLift.constant, baseMark] using ht j
  apply MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mpr
  intro f hf
  change MvPolynomial.eval (baseMark z t) f = 0
  apply eval_eq_zero inc Subtype.val_injective res _ ev _ hmark
  rw [hgen, RingHom.comp_apply, show chartBaseMap A f = 0 from hf, map_zero]
private theorem sourceMark_mem
    (hg : ∀ i, inc (q i) = seedInRoot R (A.coordinate i))
    (ht : ∀ i, res (q i) = res (M.constant (t i))) :
    markedPoint t S ∈ MvPolynomial.zeroLocus FX (chartSource A) := by
  let ev := MvPolynomial.eval₂Hom M.fx (fun i : Option (Fin n) => i.elim (ordinateLift M) q)
  have hgen : (inc).comp ev = (AdjoinRoot.mk (rootEquation R)).comp (chartRootMap A) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simpa [ev, chartRootMap] using generic_fx M x
    · intro i
      cases i with
      | none => simpa [ev, chartRootMap] using generic_y M
      | some j => simpa [ev, chartRootMap, seedInRoot] using hg j
  have hmark : (res).comp ev = ((res).comp M.fx).comp (MvPolynomial.eval (markedPoint t S)) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [ev]
    · intro i
      cases i with
      | none => simpa [ev, markedPoint] using marked_y M
      | some j => simpa [ev, MarkLift.constant, markedPoint] using ht j
  apply MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mpr
  intro f hf
  change MvPolynomial.eval (markedPoint t S) f = 0
  apply eval_eq_zero inc Subtype.val_injective res _ ev _ hmark
  rw [hgen, RingHom.comp_apply]
  exact AdjoinRoot.mk_eq_zero.mpr (Ideal.mem_span_singleton.mp hf)
end Lift
theorem specializeChart {n : ℕ} (A : CoefficientChart R n)
    {z : K} {S : K[X]} (M : MarkLift R z S) (hM : M.ConstantResidues)
    (hreg : ∀ i, seedInRoot R (A.coordinate i) ∈ M.V) :
    ∃ t : Fin n → L,
      baseMark z t ∈ MvPolynomial.zeroLocus FX (chartBase A) ∧
      markedPoint t S ∈ MvPolynomial.zeroLocus FX (chartSource A) ∧
      (specialize A.equation t).eval (liftPoly S) = 0 := by
  classical
  let q (i : Fin n) : M.V := ⟨seedInRoot R (A.coordinate i), hreg i⟩
  choose t ht using fun i => hM (A.coordinate i) (hreg i)
  have hbase := baseMark_mem M A q t (fun _ => rfl) ht
  have hsource := sourceMark_mem M A q t (fun _ => rfl) ht
  refine ⟨t, hbase, hsource, ?_⟩
  apply IsFractionRing.injective L[X] FX
  rw [map_zero, ← equation_eval_mark A t S]
  have he := (MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mp hsource) (equation_mem_source A)
  exact he
end
end K1_14_2_4_1_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_1_5
noncomputable section
open K1 K1_14 K1_14_2_4_1 MvPolynomial
def c1 : Prop :=
  ∀ (n : ℕ) (B : Ideal (ChartBaseRing n)), B.IsPrime →
    (affineHilbertPolynomial B).natDegree ≤ 1 →
    ∃ D : ℕ, ∀ k : ℕ, parameterDegreeLE B (D + k) ≤
      powerSpan (F := SlopeField n) (genericLinear B) (parameterDegreeLE B D) k
def c2 : Prop :=
  ∀ (n H : ℕ) (B : Ideal (ChartBaseRing n)), B.IsPrime → BaseHeight B H →
    ∀ W : Submodule (SlopeField n) (ExtendedBase B), Module.Finite (SlopeField n) W →
    ∃ C : ℕ, ∀ k : ℕ,
      Module.finrank (SlopeField n) (powerSpan (F := SlopeField n) (genericLinear B) W k) ≤ C + k * H
set_option maxHeartbeats 1000000 in
theorem of_children (h₁ : c1) (h₂ : c2) : K1_14_2_4_1.c5 := by
  classical
  intro n H B hB hH q hq V pt hinj hpt
  let : B.IsPrime := hB
  obtain ⟨D, hD⟩ := h₁ n B hB hH.dimension
  obtain ⟨r, hr⟩ := exists_independent_mark_powers B q hq V pt hinj hpt
  let mulMark (j : ↥V) : ExtendedBase B →ₗ[SlopeField n] ExtendedBase B :=
    LinearMap.mulLeft (SlopeField n) (extendBase B (r j))
  let pieces (j : ↥V) : Submodule (SlopeField n) (ExtendedBase B) :=
    (parameterDegreeLE B D).map (mulMark j)
  let W := iSup pieces
  have piece_finite (j : ↥V) : Module.Finite (SlopeField n) (pieces j) := by
    dsimp only [pieces]
    infer_instance
  let : ∀ j, Module.Finite (SlopeField n) (pieces j) := piece_finite
  let : Module.Finite (SlopeField n) W := Submodule.finite_iSup pieces
  obtain ⟨C, hC⟩ := h₂ n H B hB hH W inferInstance
  have hcount (k : ℕ) : (k + 1) * V.card ≤ C + (k * q.totalDegree) * H := by
    let S := powerSpan (F := SlopeField n) (genericLinear B) W (k * q.totalDegree)
    let v (ij : Fin (k + 1) × (↥V)) :=
      extendBase B ((Ideal.Quotient.mk B (parameterInclusion n q)) ^ (ij.1 : ℕ) * r ij.2)
    have hmem (ij : Fin (k + 1) × (↥V)) : v ij ∈ S := by
      obtain ⟨i, j⟩ := ij
      have hdeg : (q ^ (i : ℕ)).totalDegree ≤ D + k * q.totalDegree :=
        ((totalDegree_pow q (i : ℕ)).trans
          (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ i.isLt))).trans (Nat.le_add_left _ _)
      have hp := hD (k * q.totalDegree) (parameterClass_mem B _ hdeg)
      have hj : pieces j ≤ W := le_iSup pieces j
      have hm : (powerSpan (F := SlopeField n) (genericLinear B) (parameterDegreeLE B D)
          (k * q.totalDegree)).map (mulMark j) ≤ S :=
        map_powerSpan_le (F := SlopeField n) (A := ExtendedBase B) (genericLinear B)
          (extendBase B (r j)) (W := parameterDegreeLE B D) (U := W) hj (k * q.totalDegree)
      apply hm
      refine Submodule.mem_map.mpr ⟨_, hp, ?_⟩
      simp only [mulMark, v, LinearMap.mulLeft_apply, map_mul, map_pow]
      exact mul_comm _ _
    let w : Fin (k + 1) × (↥V) → S := fun ij => ⟨v ij, hmem ij⟩
    have hw : LinearIndependent (SlopeField n) w :=
      LinearIndependent.of_comp S.subtype (hr k)
    have h := hw.fintype_card_le_finrank
    exact (by simpa [S, Fintype.card_prod] using h.trans (hC (k * q.totalDegree)))
  by_contra! hn
  have hbad := Nat.mul_le_mul_left (C + 1) (Nat.succ_le_of_lt hn)
  have ht := hbad.trans (hcount C)
  rw [Nat.mul_succ, Nat.mul_assoc, Nat.succ_mul C (q.totalDegree * H)] at ht
  omega
end
end K1_14_2_4_1_5
end
section
namespace K1_14_2_4_1_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4_1
open scoped Polynomial
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g : ℕ}
variable (R : PrimitiveRoot C₀ J g)
theorem ker_generic : RingHom.ker (generic R) = J := by
  refine Eq.trans ?_ R.contraction.symm
  ext f
  change AdjoinRoot.mk (rootEquation R) (genericRootMap C₀ f) = 0 ↔
    genericRootMap C₀ f ∈ Ideal.span {rootEquation R}
  rw [AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
private theorem liftEvaluation {A F E : Type*} [CommRing A] [Field F] [Field E]
    (j : A →+* F) (m : A →+* E) (s : E →+* A)
    (hm : RingHom.ker j ≤ RingHom.ker m) (hs : m.comp s = RingHom.id E) :
    ∃ (V : ValuationSubring F) (a : A →+* V),
      V.toSubring.subtype.comp a = j ∧
      (IsLocalRing.residue V).comp a = ((IsLocalRing.residue V).comp (a.comp s)).comp m := by
  let B := j.range
  let q : A →+* B := j.rangeRestrict
  let e : A ⧸ RingHom.ker j →+* E := Ideal.Quotient.lift _ m hm
  let mB : B →+* E := e.comp j.quotientKerEquivRange.symm.toRingHom
  have hq (f : A) : mB (q f) = m f := by
    change e (j.quotientKerEquivRange.symm (j.rangeRestrict f)) = _
    rw [RingHom.quotientKerEquivRange, RingEquiv.symm_trans_apply,
      RingHom.quotientKerEquivOfSurjective_symm_apply j.rangeRestrict_surjective,
      Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
    rfl
  obtain ⟨V, hBV, hnon⟩ := (RingHom.ker mB).image_subset_nonunits_valuationSubring
    (RingHom.ker_ne_top mB)
  let a : A →+* V := j.codRestrict V.toSubring (fun f => hBV ⟨f, rfl⟩)
  refine ⟨V, a, rfl, ?_⟩
  apply RingHom.ext
  intro f
  let b : A := f - s (m f)
  have hb : q b ∈ RingHom.ker mB := by
    change mB (q b) = 0
    rw [hq]
    simp only [b, map_sub, ← RingHom.comp_apply m s, hs, RingHom.id_apply, sub_self]
  have hv : a b ∈ IsLocalRing.maximalIdeal V :=
    V.coe_mem_nonunits_iff.mp (hnon ⟨q b, hb, rfl⟩)
  have hz := (IsLocalRing.residue_eq_zero_iff _).2 hv
  simpa only [b, map_sub, sub_eq_zero, RingHom.comp_apply] using hz
theorem exists_markLift {z : K} {S : K[X]} (hm : OnRoot J z S) :
    Nonempty (MarkLift R z S) := by
  have hk : RingHom.ker (generic R) ≤ RingHom.ker (rootMarkHom z S) :=
    (ker_generic R).symm ▸ hm
  have hc : (rootMarkHom z S).comp MvPolynomial.C = RingHom.id FX := by
    apply RingHom.ext
    intro x
    simp [rootMarkHom]
  obtain ⟨V, a, hgen, hmark⟩ :=
    liftEvaluation (generic R) (rootMarkHom z S) MvPolynomial.C hk hc
  exact ⟨⟨V, a, hgen, hmark⟩⟩
end
end K1_14_2_4_1_2
end
section
namespace K1_14_2_4_1_4_1
open K1_14_2_4_1_4
open scoped TensorProduct
noncomputable section
variable {k ι σ : Type} [Field k]
local notation "F" => CutField k ι
local notation "P" => MvPolynomial ι k
local notation "A" => MvPolynomial σ k
local notation "V" => MvPolynomial σ F
private abbrev extendCoeffs : A →+* V :=
  MvPolynomial.map (algebraMap k F)
private theorem map_cut (offset : ι) (u : MvPolynomial (Other offset) A)
    {D : Type} [CommRing D] [Algebra F D] (f : V →ₐ[F] D) :
    f (cutAtOffset offset u) =
      MvPolynomial.eval₂Hom (f.toRingHom.comp extendCoeffs)
        (fun i => algebraMap F D (genericVariable i.val)) u -
        algebraMap F D (genericVariable offset) := by
  rw [cutAtOffset, map_sub, MvPolynomial.algHom_C]
  change f.toRingHom (MvPolynomial.eval₂Hom extendCoeffs
    (fun i => MvPolynomial.C (genericVariable i.val)) u) - _ = _
  rw [MvPolynomial.map_eval₂Hom]
  have hX : (fun i : Other offset => f.toRingHom (MvPolynomial.C (genericVariable (k := k) i.val))) =
      (fun i => algebraMap F D (genericVariable i.val)) := funext fun i => f.commutes _
  rw [hX]
set_option maxHeartbeats 1000000 in
private def sectionEquiv (offset : ι) (I : Ideal A) (u : MvPolynomial (Other offset) A) :
    PresentedSection offset I u ≃ₐ[F]
      GenericFibre k offset (MvPolynomial.map (Ideal.Quotient.mk I) u) := by
  classical
  let v := MvPolynomial.map (Ideal.Quotient.mk I) u
  let B := MvPolynomial (Other offset) (A ⧸ I)
  letI := offsetAlgebra (k := k) offset v
  letI : Module P B := Algebra.toModule
  let T := GenericFibre k offset v
  let J := I.map extendCoeffs ⊔ Ideal.span {cutAtOffset offset u}
  let S := V ⧸ J
  let q : V →ₐ[F] S := Ideal.Quotient.mkₐ F J
  let r : B →ₐ[P] T := Algebra.TensorProduct.includeRight
  let j : A →+* T := r.toRingHom.comp (MvPolynomial.C.comp (Ideal.Quotient.mk I))
  let f : V →ₐ[F] T := MvPolynomial.aeval (fun s => j (MvPolynomial.X s))
  have offset_C (a : k) :
      offsetMap (k := k) offset v (MvPolynomial.C a) =
        MvPolynomial.C (Ideal.Quotient.mk I (MvPolynomial.C a)) := by
    rw [offsetMap, MvPolynomial.eval₂Hom_C]
    rfl
  have offset_X (i : Other offset) :
      offsetMap (k := k) offset v (MvPolynomial.X i.val) = MvPolynomial.X i := by
    rw [offsetMap, MvPolynomial.eval₂Hom_X', dite_eq_right i.property]
  have offset_self : offsetMap (k := k) offset v (MvPolynomial.X offset) = v := by
    rw [offsetMap, MvPolynomial.eval₂Hom_X', dite_eq_left rfl]
  have scalar_relation (p : P) :
      r (offsetMap (k := k) offset v p) = algebraMap F T (algebraMap P F p) :=
    r.commutes p
  have other_relation (i : Other offset) :
      r (MvPolynomial.X i) = algebraMap F T (genericVariable i.val) := by
    have h := scalar_relation (MvPolynomial.X i.val)
    rw [offset_X] at h
    exact h
  have offset_relation : r v = algebraMap F T (genericVariable offset) := by
    have h := scalar_relation (MvPolynomial.X offset)
    rw [offset_self] at h
    exact h
  have f_coeff : f.toRingHom.comp extendCoeffs = j := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change f (extendCoeffs (MvPolynomial.C a)) =
        r (MvPolynomial.C (Ideal.Quotient.mk I (MvPolynomial.C a)))
      rw [extendCoeffs, MvPolynomial.map_C, MvPolynomial.algHom_C]
      have h := scalar_relation (MvPolynomial.C a)
      rw [offset_C] at h
      exact h.symm
    · intro s
      change f (extendCoeffs (MvPolynomial.X s)) = j (MvPolynomial.X s)
      rw [extendCoeffs, MvPolynomial.map_X]
      exact MvPolynomial.aeval_X _ _
  have f_u : MvPolynomial.eval₂Hom j (fun i => algebraMap F T (genericVariable i.val)) u = r v := by
    dsimp only [v]
    rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
    change _ = r.toRingHom (MvPolynomial.eval₂Hom _ _ u)
    rw [MvPolynomial.map_eval₂Hom]
    change _ = MvPolynomial.eval₂Hom j (fun i => r (MvPolynomial.X i)) u
    simp_rw [other_relation]
  have f_cut : f (cutAtOffset offset u) = 0 := by
    rw [map_cut, f_coeff, f_u, offset_relation, sub_self]
  have f_kills : J ≤ RingHom.ker f.toRingHom := by
    apply sup_le
    · apply (Ideal.map_le_iff_le_comap).mpr
      intro a ha
      have h : f.toRingHom (extendCoeffs a) = j a := DFunLike.congr_fun f_coeff a
      change f.toRingHom (extendCoeffs a) = 0
      rw [h]
      have hz : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
      simp only [j, RingHom.comp_apply, hz, map_zero]
    · apply Ideal.span_le.mpr
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      exact RingHom.mem_ker.mpr f_cut
  let forward : S →ₐ[F] T := Ideal.Quotient.liftₐ J f fun a ha =>
    RingHom.mem_ker.mp (f_kills ha)
  have forward_mk (p : V) : forward (q p) = f p := rfl
  have q_kills (a : A) (ha : a ∈ I) : (q.toRingHom.comp extendCoeffs) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show I.map extendCoeffs ≤ J from le_sup_left) (Ideal.mem_map_of_mem _ ha))
  let j' : (A ⧸ I) →+* S := Ideal.Quotient.lift I (q.toRingHom.comp extendCoeffs) q_kills
  let g₀ : B →+* S := MvPolynomial.eval₂Hom j'
    (fun i => algebraMap F S (genericVariable i.val))
  have j'_mk (a : A) : j' (Ideal.Quotient.mk I a) = (q.toRingHom.comp extendCoeffs) a := rfl
  have g_C (a : A) : g₀ (MvPolynomial.C (Ideal.Quotient.mk I a)) = q (extendCoeffs a) :=
    (MvPolynomial.eval₂Hom_C _ _ _).trans (j'_mk a)
  have g_X (i : Other offset) :
      g₀ (MvPolynomial.X i) = algebraMap F S (genericVariable i.val) :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have g_offset : g₀ v = algebraMap F S (genericVariable offset) := by
    have h : q (cutAtOffset offset u) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show Ideal.span {cutAtOffset offset u} ≤ J from le_sup_right)
          (Ideal.subset_span (by simp)))
    have hq := map_cut (D := S) offset u q
    rw [hq, sub_eq_zero] at h
    have hj : j'.comp (Ideal.Quotient.mk I) = q.toRingHom.comp extendCoeffs :=
      RingHom.ext j'_mk
    change MvPolynomial.eval₂Hom j'
      (fun i : Other offset => algebraMap F S (genericVariable i.val))
      (MvPolynomial.map (Ideal.Quotient.mk I) u) = _
    rw [MvPolynomial.eval₂Hom_map_hom (S₂ := S), hj]
    exact h
  have g_scalar : g₀.comp (offsetMap (k := k) offset v) =
      (algebraMap F S).comp (algebraMap P F) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change g₀ (offsetMap (k := k) offset v (MvPolynomial.C a)) =
        algebraMap F S (algebraMap P F (MvPolynomial.C a))
      rw [offset_C, g_C, extendCoeffs, MvPolynomial.map_C, MvPolynomial.algHom_C]
      rfl
    · intro i
      change g₀ (offsetMap (k := k) offset v (MvPolynomial.X i)) =
        algebraMap F S (genericVariable i)
      by_cases hi : i = offset
      · subst i
        rw [offset_self]
        exact g_offset
      · rw [offset_X (⟨i, hi⟩ : Other offset)]
        exact g_X ⟨i, hi⟩
  let scalarMap : P →+* S := (algebraMap F S).comp (algebraMap P F)
  letI scalarAlgebra : Algebra P S := scalarMap.toAlgebra' fun c x => by
    exact mul_comm (scalarMap c) x
  letI : SMul P S := scalarAlgebra.toSMul
  letI : IsScalarTower P F S :=
    IsScalarTower.of_algebraMap_eq' (R := P) (S := F) (show algebraMap P S = scalarMap from rfl)
  let g : B →ₐ[P] S := ⟨g₀, DFunLike.congr_fun g_scalar⟩
  let back : T →ₐ[F] S := AlgHom.liftEquiv P F B S g
  have back_right (b : B) : back (r b) = g₀ b := by
    change (AlgHom.liftEquiv P F B S g) (1 ⊗ₜ[P] b) = g b
    simp only [AlgHom.liftEquiv_tmul, one_smul]
  refine AlgEquiv.ofAlgHom forward back ?_ ?_
  · apply AlgHom.coe_ringHom_injective
    apply Algebra.TensorProduct.ringHom_ext (R := P)
    · apply RingHom.ext
      intro a
      change forward (back (algebraMap F T a)) = algebraMap F T a
      rw [back.commutes, forward.commutes]
    · apply MvPolynomial.ringHom_ext
      · intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change forward (back (r (MvPolynomial.C (Ideal.Quotient.mk I a)))) =
          r (MvPolynomial.C (Ideal.Quotient.mk I a))
        rw [back_right, g_C, forward_mk]
        exact DFunLike.congr_fun f_coeff a
      · intro i
        change forward (back (r (MvPolynomial.X i))) = r (MvPolynomial.X i)
        rw [back_right, g_X, forward.commutes, other_relation]
  · apply Ideal.Quotient.algHom_ext F
    apply MvPolynomial.algHom_ext
    intro s
    change back (forward (q (MvPolynomial.X s))) = q (MvPolynomial.X s)
    rw [forward_mk]
    change back (MvPolynomial.aeval (fun s => j (MvPolynomial.X s)) (MvPolynomial.X s)) = _
    rw [MvPolynomial.aeval_X]
    change back (r (MvPolynomial.C (Ideal.Quotient.mk I (MvPolynomial.X s)))) = _
    rw [back_right, g_C, extendCoeffs, MvPolynomial.map_X]
theorem proof : K1_14_2_4_1_4.c1 := by
  intro k ι σ _ offset I u d
  let e := (sectionEquiv offset I u).toLinearEquiv
  simp only [LengthBound, Module.Finite.equiv_iff e, e.finrank_eq]
end
end K1_14_2_4_1_4_1
end
section
set_option autoImplicit false
namespace K1_14_2_4_3
noncomputable section
open K1_14 K1_14_2_4 MvPolynomial
open scoped Polynomial
def c1 : Prop :=
  ∀ (n : ℕ) (J : Ideal (SourceRing n)), J.IsPrime →
    (affineHilbertPolynomial J).natDegree = 1 →
    BoundaryRegular J (parameterCut n) 0 1
def c2 : Prop :=
  ∀ (n : ℕ) (J : Ideal (SourceRing n)), J.IsPrime →
    (affineHilbertPolynomial J).natDegree = 1 →
    BoundaryRegular J (ordinateCut n) 1 0
private theorem iterate_le (f : ℕ → ℕ) (d N m : ℕ)
    (h : ∀ i : ℕ, N ≤ i → f (i + 1) ≤ f i + d) :
    f (N + m) ≤ f N + m * d := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [← Nat.add_assoc, Nat.succ_mul]
      exact (h (N + m) (Nat.le_add_right _ _)).trans (by omega)
set_option maxHeartbeats 600000 in
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_4.c3 := by
  intro n a b Dparam Dy ha hb J hJ hdim hslice
  obtain ⟨N₁, h₁⟩ := strict_of_boundaryRegular (h1 n J hJ hdim)
  obtain ⟨N₂, h₂⟩ := strict_of_boundaryRegular (h2 n J hJ hdim)
  let N₀ := max N₁ N₂
  let F (u v : ℕ) := Module.finrank (SliceField n) (box J u v)
  let H (N : ℕ) := F (a * N) (b * N)
  let d := b * Dparam + a * Dy
  let _ : Module.Finite (SliceField n) (SectionRing J (parameterCut n)) := hslice.parameter_finite
  let _ : Module.Finite (SliceField n) (SectionRing J (ordinateCut n)) := hslice.ordinate_finite
  have hstep (N : ℕ) (hN : N₀ ≤ N) : H (N + 1) ≤ H N + d := by
    have hu : N₀ ≤ a * N := hN.trans (Nat.le_mul_of_pos_left N ha)
    have hv : N₀ ≤ b * N := hN.trans (Nat.le_mul_of_pos_left N hb)
    have hp (v : ℕ) (hv' : b * N ≤ v) : F (a * N) (v + 1) ≤ F (a * N) v + Dparam :=
      (finrank_box_step J (parameterCut n) (a * N) v (a * N) (v + 1)
        (h₁ _ _ ((le_max_left _ _).trans hu) ((le_max_left _ _).trans (hv.trans hv')))).trans
        (Nat.add_le_add_left hslice.parameter_length _)
    have hy (u : ℕ) (hu' : a * N ≤ u) :
        F (u + 1) (b * N + b) ≤ F u (b * N + b) + Dy :=
      (finrank_box_step J (ordinateCut n) u (b * N + b) (u + 1) (b * N + b)
        (h₂ _ _ ((le_max_right _ _).trans (hu.trans hu'))
          ((le_max_right _ _).trans (hv.trans (Nat.le_add_right _ _))))).trans
        (Nat.add_le_add_left hslice.ordinate_length _)
    have hp' := iterate_le (F (a * N)) Dparam (b * N) b hp
    have hy' := iterate_le (fun u => F u (b * N + b)) Dy (a * N) a hy
    dsimp only [H, d]
    rw [Nat.mul_succ, Nat.mul_succ]
    omega
  have hlin (N : ℕ) (hN : N₀ ≤ N) : H N ≤ H N₀ + N * d := by
    have h := iterate_le H d N₀ (N - N₀) hstep
    rw [Nat.add_sub_of_le hN] at h
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.sub_le _ _)) _)
  let R : ℚ[X] := Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (H N₀ : ℚ)
  have hR : R.natDegree ≤ 1 := Polynomial.natDegree_linear_le
  have hRcoeff : R.coeff 1 = (d : ℚ) := by
    simp [R]
  have hdim' : (affineHilbertPolynomial (linearIdeal a b J)).natDegree = 1 :=
    (natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb J).trans hdim
  have hdeg := affineDegree_le_of_eventually_affineHilbertFunction_le hdim' hR (by
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    have h := (affineHilbertFunction_comap_bidegreeMap_le J a b N).trans
      ((finrank_box_le_extended J (a * N) (b * N)).trans (hlin N hN))
    change affineHilbertFunction (linearIdeal a b J) N ≤ H N₀ + N * d at h
    calc
      _ ≤ (H N₀ : ℚ) + (N : ℚ) * (d : ℚ) := by exact_mod_cast h
      _ = R.eval (N : ℚ) := by
        simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        rw [add_comm (H N₀ : ℚ), mul_comm (N : ℚ)])
  simpa only [Nat.factorial_one, Nat.cast_one, one_mul, hRcoeff, d] using hdeg
end
end K1_14_2_4_3
end
section
namespace K1_14_2_4_1_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open scoped Polynomial
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
def c1 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)],
    letI : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
    ∃ i : Fin 2, IsTranscendenceBasis L (fun _ : Unit => seedCoordinate C₀ i)
def c2 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g : ℕ)
    (R : PrimitiveRoot C₀ J g) (z : K) (S : K[X]) (M : MarkLift R z S) (i : Fin 2),
    letI : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
    IsTranscendenceBasis L (fun _ : Unit => seedCoordinate C₀ i) →
    M.ConstantResidues
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_4_1.c2 := by
  classical
  intro C₀ _ J g R T z s hmark
  obtain ⟨i, hi⟩ := h1 C₀
  let I := ↥(T : Set K)
  let M (j : I) : MarkLift R (z j) (s j) :=
    Classical.choice (exists_markLift R (hmark j j.property))
  have hM (j : I) : (M j).ConstantResidues := h2 C₀ J g R (z j) (s j) (M j) i hi
  obtain ⟨A, hreg⟩ := commonChart R (z ∘ (Subtype.val : I → K)) (s ∘ Subtype.val) M hM
  choose t ht using fun j : I => specializeChart A (M j) (hM j) (hreg j)
  let p (γ : K) := if hγ : γ ∈ T then t ⟨γ, hγ⟩ else fun _ => 0
  refine ⟨size R, A, p, ?_, ?_, ?_⟩
  · intro γ hγ
    simpa only [p, dite_eq_left hγ] using (ht ⟨γ, hγ⟩).1
  · intro γ hγ
    simpa only [p, dite_eq_left hγ] using (ht ⟨γ, hγ⟩).2.1
  · intro γ hγ
    simpa only [p, dite_eq_left hγ] using (ht ⟨γ, hγ⟩).2.2
end
end K1_14_2_4_1_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_2
noncomputable section
open K1_14 K1_14_2_4 K1_14_2_4_3 MvPolynomial
abbrev Affine {k σ : Type*} [Field k] (J : Ideal (MvPolynomial (Option σ) k)) :=
  MvPolynomial (Option σ) k ⧸ J
abbrev filteredBox {k σ : Type*} [Field k] (J : Ideal (MvPolynomial (Option σ) k))
    (d : ℕ × ℕ) := quotientBidegreeLE J d.1 d.2
abbrev ordinate {k σ : Type*} [Field k] (J : Ideal (MvPolynomial (Option σ) k)) : Affine J :=
  Ideal.Quotient.mk J (MvPolynomial.X none)
variable {n : ℕ} (J : Ideal (SourceRing n))
abbrev CoeffPoly := MvPolynomial (Option (Fin n)) (Affine J)
def polynomialBox (d : ℕ × ℕ) : Submodule FX (CoeffPoly J) where
  carrier := {p | ∀ m, p.coeff m ∈ filteredBox J d}
  zero_mem' m := (filteredBox J d).zero_mem
  add_mem' hp hq m := (filteredBox J d).add_mem (hp m) (hq m)
  smul_mem' c p hp := by
    change ∀ m, (c • p).coeff m ∈ filteredBox J d
    intro m
    rw [MvPolynomial.coeff_smul]
    exact (filteredBox J d).smul_mem c (hp m)
def polynomialCut : CoeffPoly J := MvPolynomial.C (ordinate J) - MvPolynomial.X none
structure CoefficientTransport where
  toSlice : CoeffPoly J →ₐ[FX] ExtendedRing J
  injective_toSlice : Function.Injective toSlice
  cut_eq : toSlice (polynomialCut J) = cutClass J (ordinateCut n)
  map_box : ∀ (d : ℕ × ℕ) (p : CoeffPoly J),
    p ∈ polynomialBox J d → toSlice p ∈ box J d.1 d.2
  clear_boxes : ∀ (d e : ℕ × ℕ) (x t : ExtendedRing J),
    x ∈ box J d.1 d.2 → t ∈ box J e.1 e.2 →
      ∃ (s : SliceField n) (_ : s ≠ 0) (p q : CoeffPoly J),
        p ∈ polynomialBox J d ∧ q ∈ polynomialBox J e ∧
          toSlice p = s • x ∧ toSlice q = s • t
end
end K1_14_2_4_3_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace K1_14_2_4_3_2
noncomputable section
open MvPolynomial
variable {k σ : Type*} [Field k]
theorem box_one (J : Ideal (MvPolynomial (Option σ) k)) (d : ℕ × ℕ) :
    (1 : Affine J) ∈ filteredBox J d := by
  refine mem_quotientBidegreeLE.mpr ⟨1, ?_, map_one _⟩
  rw [mem_restrictBidegree]
  intro m hm
  obtain rfl : m = 0 := by simpa [support_one] using hm
  simp
private theorem box_mul {J : Ideal (MvPolynomial (Option σ) k)} {d e : ℕ × ℕ}
    {x y : Affine J} (hx : x ∈ filteredBox J d) (hy : y ∈ filteredBox J e) :
    x * y ∈ filteredBox J (d + e) := by
  obtain ⟨p, hp, rfl⟩ := mem_quotientBidegreeLE.mp hx
  obtain ⟨q, hq, rfl⟩ := mem_quotientBidegreeLE.mp hy
  exact mem_quotientBidegreeLE.mpr ⟨p * q, mul_mem_restrictBidegree hp hq, map_mul ..⟩
def rees (J : Ideal (MvPolynomial (Option σ) k)) :
    Subalgebra k (AddMonoidAlgebra (Affine J) (ℕ × ℕ)) where
  carrier := {p | ∀ d, p.coeff d ∈ filteredBox J d}
  zero_mem' d := (filteredBox J d).zero_mem
  add_mem' hx hy d := (filteredBox J d).add_mem (hx d) (hy d)
  one_mem' := by
    classical
    intro d
    change (AddMonoidAlgebra.single 0 1 : AddMonoidAlgebra (Affine J) (ℕ × ℕ)).coeff d ∈ _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · exact box_one J d
    · exact (filteredBox J d).zero_mem
  mul_mem' {p q} hp hq := by
    classical
    intro d
    simp only [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    refine (filteredBox J d).sum_mem fun i _ => (filteredBox J d).sum_mem fun j _ => ?_
    split
    · rename_i h
      rw [← h]
      exact box_mul (hp i) (hq j)
    · exact (filteredBox J d).zero_mem
  algebraMap_mem' c := by
    classical
    intro d
    change (AddMonoidAlgebra.single 0 (algebraMap k (Affine J) c)).coeff d ∈ _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · change Ideal.Quotient.mk J (MvPolynomial.C c) ∈ filteredBox J d
      refine mem_quotientBidegreeLE.mpr ⟨_, mem_restrictBidegree.mpr fun m hm => ?_, rfl⟩
      obtain rfl := Finset.mem_singleton.mp (support_C_subset hm)
      simp
    · exact (filteredBox J d).zero_mem
def piece {J : Ideal (MvPolynomial (Option σ) k)} (d : ℕ × ℕ)
    (x : Affine J) (hx : x ∈ filteredBox J d) : rees J :=
  ⟨AddMonoidAlgebra.single d x, by
    classical
    intro e
    change (AddMonoidAlgebra.single d x).coeff e ∈ filteredBox J e
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · rename_i h
      subst e
      exact hx
    · exact (filteredBox J e).zero_mem⟩
variable (J : Ideal (MvPolynomial (Option σ) k))
def U : rees J := piece (1, 0) 1 (box_one J _)
def V : rees J := piece (0, 1) 1 (box_one J _)
private def variableDegree : Option σ → ℕ × ℕ
  | none => (1, 0)
  | some _ => (0, 1)
private theorem box_X (i : Option σ) : Ideal.Quotient.mk J (MvPolynomial.X i) ∈
    filteredBox J (variableDegree i) := by
  refine mem_quotientBidegreeLE.mpr ⟨MvPolynomial.X i, ?_, rfl⟩
  rw [mem_restrictBidegree]
  intro m hm
  obtain rfl : m = Finsupp.single i 1 := by simpa only [support_X, Finset.mem_singleton] using hm
  cases i <;> simp [variableDegree, Finsupp.some_single_none, Finsupp.some_single_some]
def coordinate (i : Option σ) : rees J :=
  piece (variableDegree i) (Ideal.Quotient.mk J (MvPolynomial.X i)) (box_X J i)
abbrev yGen : rees J := coordinate J none
def degreeIdeal : Ideal (rees J) := Ideal.span {U J, yGen J}
@[simp] theorem val_piece {d : ℕ × ℕ} {x : Affine J} (hx : x ∈ filteredBox J d) :
    (rees J).val (piece d x hx) = AddMonoidAlgebra.single d x := rfl
private theorem val_coord (i : Option σ) : (rees J).val (coordinate J i) =
    AddMonoidAlgebra.single (variableDegree i) (Ideal.Quotient.mk J (MvPolynomial.X i)) := rfl
private theorem val_scalar (c : k) : (rees J).val (algebraMap k (rees J) c) =
    AddMonoidAlgebra.single 0 (Ideal.Quotient.mk J (MvPolynomial.C c)) := rfl
private theorem single_pow (d : ℕ × ℕ) (x : Affine J) (a : ℕ) :
    (AddMonoidAlgebra.single d x : AddMonoidAlgebra (Affine J) (ℕ × ℕ)) ^ a =
      AddMonoidAlgebra.single (a • d) (x ^ a) := by
  induction a with
  | zero => simp [AddMonoidAlgebra.one_def]
  | succ a ih => rw [pow_succ, ih, AddMonoidAlgebra.single_mul_single, succ_nsmul,
      pow_succ]
private theorem piece_monomial (u v : ℕ) (m : Option σ →₀ ℕ) (c : k)
    (hu : m none ≤ u) (hv : m.some.degree ≤ v) :
    ∃ (h : Ideal.Quotient.mk J (monomial m c) ∈ filteredBox J (u, v)),
      piece (u, v) (Ideal.Quotient.mk J (monomial m c)) h =
        (U J ^ (u - m none) * yGen J ^ m none) *
          (algebraMap k (rees J) c * V J ^ (v - m.some.degree) *
            m.some.prod (fun i a => coordinate J (some i) ^ a)) := by
  classical
  have hm : monomial m c ∈ restrictBidegree σ k u v := by
    exact mem_restrictBidegree.mpr fun e he => by
      obtain rfl := Finset.mem_singleton.mp (support_monomial_subset he)
      exact ⟨hu, hv⟩
  have hinj : Function.Injective (rees J).val := Subtype.val_injective
  refine ⟨mem_quotientBidegreeLE.mpr ⟨_, hm, rfl⟩, hinj ?_⟩
  simp only [Finsupp.prod, map_mul, map_pow, map_prod, val_scalar, U, V, yGen, val_coord,
    val_piece, variableDegree, single_pow, AddMonoidAlgebra.prod_single,
    AddMonoidAlgebra.single_mul_single, one_pow, Prod.smul_mk, nsmul_eq_mul, mul_one, mul_zero,
    one_mul]
  congr 1
  · have hv' : (∑ i ∈ m.some.support, m (some i)) ≤ v := by
      simpa [Finsupp.degree_apply] using hv
    ext <;> simp [Finsupp.degree_apply, Prod.fst_sum, Prod.snd_sum, Nat.sub_add_cancel hu,
      Nat.sub_add_cancel hv']
  · rw [monomial_eq, Finsupp.prod_option_index _ _ (by simp) (by intros; rw [pow_add]),
      map_mul, map_mul, map_pow, Finsupp.prod, map_prod]
    simp only [map_pow]
    ac_rfl
private theorem piece_sum_support (u v : ℕ) (p : MvPolynomial (Option σ) k)
    (hp : p ∈ restrictBidegree σ k u v) (m : p.support) :
    Ideal.Quotient.mk J (monomial m.val (p.coeff m.val)) ∈ filteredBox J (u, v) :=
  (piece_monomial J u v m.val _ (mem_restrictBidegree.mp hp _ m.property).1 (mem_restrictBidegree.mp hp _ m.property).2).choose
private theorem piece_sum (u v : ℕ) (p : MvPolynomial (Option σ) k)
    (hp : p ∈ restrictBidegree σ k u v) :
    piece (u, v) (Ideal.Quotient.mk J p) (mem_quotientBidegreeLE.mpr ⟨p, hp, rfl⟩) =
      ∑ m : p.support, piece (u, v) _ (piece_sum_support J u v p hp m) := by
  classical
  apply Subtype.ext
  change (rees J).val (piece (u, v) (Ideal.Quotient.mk J p) (mem_quotientBidegreeLE.mpr ⟨p, hp, rfl⟩)) =
    (rees J).val (∑ m : p.support, piece (u, v) _ (piece_sum_support J u v p hp m))
  rw [map_sum]
  change AddMonoidAlgebra.single (u, v) (Ideal.Quotient.mk J p) =
    ∑ m : p.support, AddMonoidAlgebra.single (u, v)
      (Ideal.Quotient.mk J (monomial m.val (p.coeff m.val)))
  rw [Finset.sum_coe_sort p.support (fun m => AddMonoidAlgebra.single (u, v)
    (Ideal.Quotient.mk J (monomial m (p.coeff m))))]
  simp only [← AddMonoidAlgebra.singleAddHom_apply, ← map_sum, support_sum_monomial_coeff]
theorem piece_mem_pow (u v : ℕ) {x : Affine J} (hx : x ∈ filteredBox J (u, v)) :
    piece (u, v) x hx ∈ degreeIdeal J ^ u := by
  classical
  obtain ⟨p, hp, rfl⟩ := mem_quotientBidegreeLE.mp hx
  rw [piece_sum J u v p hp]
  refine (degreeIdeal J ^ u).sum_mem fun m _ => ?_
  rw [(piece_monomial J u v m.val _ (mem_restrictBidegree.mp hp _ m.property).1 (mem_restrictBidegree.mp hp _ m.property).2).choose_spec]
  rw [mul_comm (U J ^ (u - m.val none) * yGen J ^ m.val none)]
  apply Ideal.mul_mem_left
  have hdeg : u - m.val none + m.val none = u := Nat.sub_add_cancel
    (mem_restrictBidegree.mp hp _ m.property).1
  have htwo : (degreeIdeal J).IsTwoSided := by
    constructor
    intro a b ha
    rw [mul_comm a b]
    exact (degreeIdeal J).mul_mem_left b ha
  have hpow : degreeIdeal J ^ (u - m.val none) * degreeIdeal J ^ m.val none =
      degreeIdeal J ^ u := (@Ideal.IsTwoSided.pow_add _ _ (degreeIdeal J) htwo _ _).symm.trans
        (congrArg (fun i : ℕ => degreeIdeal J ^ i) hdeg)
  rw [← hpow]
  apply Ideal.mul_mem_mul
  · exact Ideal.pow_mem_pow (Ideal.subset_span (by simp : U J ∈ {U J, yGen J})) _
  · exact Ideal.pow_mem_pow (Ideal.subset_span (by simp : yGen J ∈ {U J, yGen J})) _
theorem piece_mem_span_padding (e d : ℕ × ℕ) {x : Affine J}
    (hx : x ∈ filteredBox J (e + d)) :
    piece (e + d) x hx ∈ Ideal.span {piece e 1 (box_one J e)} ↔ x ∈ filteredBox J d := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
    rw [mul_comm r] at hr
    have hc := congrArg (fun z : rees J => ((rees J).val z).coeff (e + d)) hr
    have he : ((rees J).val r).coeff d = x := by
      simpa only [map_mul, val_piece, AddMonoidAlgebra.coeff_single_mul_add, one_mul,
        AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hc
    rw [← he]
    exact r.property d
  · intro h
    refine Ideal.mem_span_singleton'.mpr ⟨piece d x h, ?_⟩
    rw [mul_comm (piece d x h)]
    apply (show Function.Injective (rees J).val from Subtype.val_injective)
    simp only [map_mul, val_piece, AddMonoidAlgebra.single_mul_single, one_mul]
instance reesNoetherian [Finite σ] : IsNoetherianRing (rees J) := by
  classical
  let f : MvPolynomial (Bool ⊕ Option σ) k →ₐ[k] rees J :=
    aeval (Sum.elim (fun b => if b then U J else V J) (coordinate J))
  have hU : U J ∈ f.range := ⟨MvPolynomial.X (.inl true), by simp [f]⟩
  have hV : V J ∈ f.range := ⟨MvPolynomial.X (.inl false), by simp [f]⟩
  have hcoord (i : Option σ) : coordinate J i ∈ f.range := ⟨MvPolynomial.X (.inr i), by simp [f]⟩
  have hpiece (u v : ℕ) (x : Affine J) (hx : x ∈ filteredBox J (u, v)) :
      piece (u, v) x hx ∈ f.range := by
    obtain ⟨p, hp, rfl⟩ := mem_quotientBidegreeLE.mp hx
    rw [piece_sum J u v p hp]
    refine f.range.sum_mem fun m _ => ?_
    rw [(piece_monomial J u v m.val _ (mem_restrictBidegree.mp hp _ m.property).1 (mem_restrictBidegree.mp hp _ m.property).2).choose_spec]
    refine f.range.mul_mem (f.range.mul_mem (f.range.pow_mem hU _)
      (f.range.pow_mem (hcoord none) _)) (f.range.mul_mem
      (f.range.mul_mem (f.range.algebraMap_mem _) (f.range.pow_mem hV _)) ?_)
    change (∏ i ∈ m.val.some.support, coordinate J (some i) ^ m.val.some i) ∈ f.range
    exact f.range.prod_mem (f := fun i : σ => coordinate J (some i) ^ m.val.some i)
      (fun i _ => f.range.pow_mem (hcoord (some i)) _)
  apply isNoetherianRing_of_surjective _ _ f.toRingHom
  intro p
  change p ∈ f.range
  suffices p = ∑ d : p.val.coeff.support, piece d.val (p.val.coeff d.val) (p.property d.val) by
    rw [this]
    exact f.range.sum_mem fun d _ => hpiece d.val.1 d.val.2 _ _
  apply Subtype.ext
  change (rees J).val p = (rees J).val (∑ d : p.val.coeff.support,
    piece d.val (p.val.coeff d.val) (p.property d.val))
  rw [map_sum]
  change p.val = ∑ d : p.val.coeff.support, AddMonoidAlgebra.single d.val (p.val.coeff d.val)
  rw [Finset.sum_coe_sort p.val.coeff.support
    (fun d => AddMonoidAlgebra.single d (p.val.coeff d))]
  exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
end
end K1_14_2_4_3_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_1_5_2
open scoped Polynomial
noncomputable abbrev polynomialAction {F A : Type} [Field F] [CommRing A] [Algebra F A]
    (a : A) : Algebra F[X] A := (Polynomial.aeval (R := F) a).toRingHom.toAlgebra
end K1_14_2_4_1_5_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_4_1_5_2
noncomputable section
open K1_14 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_5
open scoped Polynomial TensorProduct
private def slopeInclusion (n : ℕ) : ParameterGeometry n →+* SourceRing n :=
  (MvPolynomial.rename some).toRingHom
private def slopeToSlice (n : ℕ) : SlopeField n →+* SliceField n :=
  IsFractionRing.lift (K := SlopeField n) (g := (algebraMap (SourceRing n) (SliceField n)).comp (slopeInclusion n))
    ((IsFractionRing.injective (SourceRing n) (SliceField n)).comp (MvPolynomial.rename_injective _ (Option.some_injective (Fin n))))
def offsetEval (n : ℕ) : (SlopeField n)[X] →+* SliceField n :=
  Polynomial.eval₂RingHom (slopeToSlice n) (sliceVariable (n := n) none)
abbrev offsetAlgebra (n : ℕ) : Algebra (SlopeField n)[X] (SliceField n) :=
  (offsetEval n).toAlgebra
attribute [local instance] offsetAlgebra
local instance (priority := 2000) offsetModule (n : ℕ) :
    Module (SlopeField n)[X] (SliceField n) :=
  @Algebra.toModule _ _ _ _ (offsetAlgebra n)
private def sourceToPolynomial (n : ℕ) : SourceRing n →+* (SlopeField n)[X] :=
  (Polynomial.mapRingHom (algebraMap (ParameterGeometry n) (SlopeField n))).comp
    (MvPolynomial.optionEquivLeft FX (Fin n)).toRingEquiv.toRingHom
private theorem sourceToPolynomial_injective (n : ℕ) :
    Function.Injective (sourceToPolynomial n) :=
  (Polynomial.map_injective _ (IsFractionRing.injective _ _)).comp
    (MvPolynomial.optionEquivLeft FX (Fin n)).injective
private theorem offset_source (n : ℕ) :
    (offsetEval n).comp (sourceToPolynomial n) = algebraMap (SourceRing n) (SliceField n) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [sourceToPolynomial, offsetEval, slopeToSlice, slopeInclusion,
      RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  · intro i
    cases i <;> simp [sourceToPolynomial, offsetEval, slopeToSlice, slopeInclusion,
      RingHom.comp_apply, IsFractionRing.lift_algebraMap, sliceVariable]
private def sliceToFraction (n : ℕ) : SliceField n →+* FractionRing (SlopeField n)[X] :=
  IsFractionRing.lift (K := SliceField n)
    (g := (algebraMap (SlopeField n)[X] (FractionRing (SlopeField n)[X])).comp
      (sourceToPolynomial n))
    ((IsFractionRing.injective (SlopeField n)[X] (FractionRing (SlopeField n)[X])).comp
      (sourceToPolynomial_injective n))
private theorem offset_injective (n : ℕ) : Function.Injective (offsetEval n) := by
  let m := algebraMap (SlopeField n)[X] (FractionRing (SlopeField n)[X])
  have he : (sliceToFraction n).comp (offsetEval n) = m := by
    apply Polynomial.ringHom_ext
    · have hc : (sliceToFraction n).comp (slopeToSlice n) = m.comp Polynomial.C := by
        apply IsFractionRing.ringHom_ext (A := ParameterGeometry n)
        intro c
        simp only [RingHom.comp_apply, slopeToSlice, IsFractionRing.lift_algebraMap,
          sliceToFraction]
        change m (sourceToPolynomial n (MvPolynomial.rename some c)) =
          m (Polynomial.C (algebraMap (ParameterGeometry n) (SlopeField n) c))
        have h : (MvPolynomial.optionEquivLeft FX (Fin n)) (MvPolynomial.rename some c) =
            Polynomial.C c := by
          have hcomp : (MvPolynomial.optionEquivLeft FX (Fin n)).toAlgHom.comp
              (MvPolynomial.rename some) = Polynomial.CAlgHom (R := FX) := by
            apply MvPolynomial.algHom_ext
            intro i
            simp
          exact DFunLike.congr_fun hcomp c
        change m (Polynomial.map (algebraMap (ParameterGeometry n) (SlopeField n))
          (MvPolynomial.optionEquivLeft FX (Fin n) (MvPolynomial.rename some c))) = _
        rw [h, Polynomial.map_C]
      intro c
      simpa [offsetEval, RingHom.comp_apply] using DFunLike.congr_fun hc c
    · simp only [RingHom.comp_apply, offsetEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        sliceVariable, sliceToFraction, IsFractionRing.lift_algebraMap]
      change m (Polynomial.map (algebraMap (ParameterGeometry n) (SlopeField n))
        (MvPolynomial.optionEquivLeft FX (Fin n) (MvPolynomial.X none))) = m Polynomial.X
      rw [MvPolynomial.optionEquivLeft_X_none, Polynomial.map_X]
  intro x y h
  have h' := congrArg (sliceToFraction n) h
  change ((sliceToFraction n).comp (offsetEval n)) x =
    ((sliceToFraction n).comp (offsetEval n)) y at h'
  rw [he] at h'
  exact IsFractionRing.injective (SlopeField n)[X] (FractionRing (SlopeField n)[X]) h'
private theorem fractionField_of_fractions {R E : Type} [CommRing R] [Field E]
    (f : R →+* E) (hf : Function.Injective f)
    (h : ∀ z : E, ∃ x y : R, z = f x / f y) :
    @IsFractionRing R _ E _ f.toAlgebra := by
  let : Algebra R E := f.toAlgebra
  let : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).mpr hf
  exact IsFractionRing.of_field R E h
theorem offset_isFractionRing (n : ℕ) :
    @IsFractionRing (SlopeField n)[X] _ (SliceField n) _ (offsetAlgebra n) := by
  apply fractionField_of_fractions (offsetEval n) (offset_injective n)
  intro x
  obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective (SourceRing n) x
  use sourceToPolynomial n r, sourceToPolynomial n s
  change _ = ((offsetEval n).comp (sourceToPolynomial n)) r /
    ((offsetEval n).comp (sourceToPolynomial n)) s
  rw [offset_source]
theorem offsetEval_X (n : ℕ) : offsetEval n Polynomial.X = sliceVariable (n := n) none :=
  Polynomial.eval₂_X _ _
private theorem slopeToSlice_some {n : ℕ} (i : Fin n) :
    slopeToSlice n (algebraMap (ParameterGeometry n) (SlopeField n) (MvPolynomial.X i)) =
      sliceVariable (some i) := by
  simp [slopeToSlice, slopeInclusion, IsFractionRing.lift_algebraMap, sliceVariable]
private theorem slopeToSlice_commutes (n : ℕ) (x : FX) :
    slopeToSlice n (algebraMap FX (SlopeField n) x) = algebraMap FX (SliceField n) x := by
  change slopeToSlice n (algebraMap (ParameterGeometry n) (SlopeField n) (MvPolynomial.C x)) =
    algebraMap (SourceRing n) (SliceField n) (MvPolynomial.C x)
  simp [slopeToSlice, slopeInclusion, IsFractionRing.lift_algebraMap]
local instance {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    Algebra (SlopeField n)[X] (ExtendedBase B) :=
  polynomialAction (genericLinear B)
local instance (priority := 2000) graphModule {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    Module (SlopeField n)[X] (ExtendedBase B) :=
  @Algebra.toModule _ _ _ _
    (show Algebra (SlopeField n)[X] (ExtendedBase B) from polynomialAction (genericLinear B))
abbrev LocalizedBase {n : ℕ} (B : Ideal (ChartBaseRing n)) :=
  SliceField n ⊗[(SlopeField n)[X]] ExtendedBase B
private abbrev coordInto {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    Base B →+* LocalizedBase B :=
  (Algebra.TensorProduct.includeRight (A := SliceField n)).toRingHom.comp
    (extendBase B).toRingHom
private theorem scalarInto {n : ℕ} (B : Ideal (ChartBaseRing n)) (c : SlopeField n) :
    (1 : SliceField n) ⊗ₜ[(SlopeField n)[X]] algebraMap (SlopeField n) (ExtendedBase B) c =
      algebraMap (SliceField n) (LocalizedBase B) (slopeToSlice n c) := by
  have h := Algebra.TensorProduct.tmul_one_eq_one_tmul
    (A := SliceField n) (B := ExtendedBase B) (Polynomial.C c)
  change offsetEval n (Polynomial.C c) ⊗ₜ[(SlopeField n)[X]] (1 : ExtendedBase B) =
    1 ⊗ₜ[(SlopeField n)[X]] Polynomial.aeval (genericLinear B) (Polynomial.C c) at h
  rw [offsetEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.aeval_C] at h
  exact h.symm
private abbrev sectionIdeal {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    Ideal (MvPolynomial (Fin 2 ⊕ Fin n) (SliceField n)) :=
  B.map (MvPolynomial.map (algebraMap FX (SliceField n))) ⊔ Ideal.span {baseCut n}
private def sectionEval {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    MvPolynomial (Fin 2 ⊕ Fin n) (SliceField n) →ₐ[SliceField n] LocalizedBase B :=
  MvPolynomial.aeval (fun i => coordInto B (Ideal.Quotient.mk B (MvPolynomial.X i)))
private theorem sectionEval_map {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    (sectionEval B).toRingHom.comp (MvPolynomial.map (algebraMap FX (SliceField n))) =
      (coordInto B).comp (Ideal.Quotient.mk B) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change sectionEval B (MvPolynomial.map (algebraMap FX (SliceField n)) (MvPolynomial.C c)) =
      coordInto B (Ideal.Quotient.mk B (MvPolynomial.C c))
    have hc : Ideal.Quotient.mk B (MvPolynomial.C c) = algebraMap FX (Base B) c := rfl
    rw [MvPolynomial.map_C, hc]
    change sectionEval B (MvPolynomial.C (algebraMap FX (SliceField n) c)) =
      (1 : SliceField n) ⊗ₜ[(SlopeField n)[X]] extendBase B (algebraMap FX (Base B) c)
    have hscalar : extendBase B (algebraMap FX (Base B) c) =
        algebraMap (SlopeField n) (ExtendedBase B) (algebraMap FX (SlopeField n) c) := by
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
        (A := SlopeField n) (B := Base B) c).symm
    rw [sectionEval, MvPolynomial.aeval_C, hscalar, scalarInto, slopeToSlice_commutes]
  · intro i
    change sectionEval B (MvPolynomial.map (algebraMap FX (SliceField n)) (MvPolynomial.X i)) =
      coordInto B (Ideal.Quotient.mk B (MvPolynomial.X i))
    rw [MvPolynomial.map_X]
    exact MvPolynomial.aeval_X _ _
private theorem sectionEval_cut {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    sectionEval B (baseCut n) = 0 := by
  let incl : ExtendedBase B →ₐ[(SlopeField n)[X]] LocalizedBase B :=
    Algebra.TensorProduct.includeRight
  have h₀ : incl (genericLinear B) =
      algebraMap (SliceField n) (LocalizedBase B) (sliceVariable (n := n) none) := by
    have h := Algebra.TensorProduct.tmul_one_eq_one_tmul
      (A := SliceField n) (B := ExtendedBase B) (Polynomial.X : (SlopeField n)[X])
    change (offsetEval n Polynomial.X) ⊗ₜ[(SlopeField n)[X]] (1 : ExtendedBase B) =
      1 ⊗ₜ[(SlopeField n)[X]] Polynomial.aeval (genericLinear B) Polynomial.X at h
    rw [offsetEval_X, Polynomial.aeval_X] at h
    exact h.symm
  have hi (i : Fin n) :
      incl (algebraMap (SlopeField n) (ExtendedBase B)
        (algebraMap (ParameterGeometry n) (SlopeField n) (MvPolynomial.X i))) =
      algebraMap (SliceField n) (LocalizedBase B) (sliceVariable (some i)) := by
    rw [← slopeToSlice_some i]
    exact scalarInto B _
  simp only [baseCut, sectionEval, map_sub, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  apply sub_eq_zero.mpr
  rw [← h₀]
  change _ = incl (∑ i : Fin n,
    (algebraMap (ParameterGeometry n) (SlopeField n) (MvPolynomial.X i)) •
      extendBase B (Ideal.Quotient.mk B (MvPolynomial.X (Sum.inr i))))
  rw [map_sum]
  simp only [Algebra.smul_def, map_mul, hi]
  rfl
def sectionToLocalized {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    BaseSection B →ₐ[SliceField n] LocalizedBase B :=
  Ideal.Quotient.liftₐ (sectionIdeal B) (sectionEval B) <| by
    change sectionIdeal B ≤ RingHom.ker (sectionEval B).toRingHom
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      change ((sectionEval B).toRingHom.comp (MvPolynomial.map
        (algebraMap FX (SliceField n)))) p = 0
      rw [sectionEval_map]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    · intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact sectionEval_cut B
theorem sectionToLocalized_surjective {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    Function.Surjective (sectionToLocalized B) := by
  let f := sectionToLocalized B
  let incl : ExtendedBase B →ₐ[(SlopeField n)[X]] LocalizedBase B :=
    Algebra.TensorProduct.includeRight
  have hcoord (b : Base B) : coordInto B b ∈ f.range := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨Ideal.Quotient.mk (sectionIdeal B)
      (MvPolynomial.map (algebraMap FX (SliceField n)) p), ?_⟩
    exact DFunLike.congr_fun (sectionEval_map B) p
  have hincl (x : ExtendedBase B) : incl x ∈ f.range := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact f.range.add_mem hx hy
    | tmul c b =>
      have h : (c ⊗ₜ[FX] b : ExtendedBase B) =
          algebraMap (SlopeField n) (ExtendedBase B) c * extendBase B b := by
        change _ = (c ⊗ₜ[FX] (1 : Base B)) * (1 ⊗ₜ[FX] b)
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h, map_mul]
      apply f.range.mul_mem _ (hcoord b)
      rw [show incl (algebraMap (SlopeField n) (ExtendedBase B) c) = _ from scalarInto B c]
      exact f.range.algebraMap_mem _
  intro z
  change z ∈ f.range
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => exact f.range.add_mem hx hy
  | tmul s x =>
    have h : (s ⊗ₜ[(SlopeField n)[X]] x : LocalizedBase B) =
        algebraMap (SliceField n) (LocalizedBase B) s * incl x := by
      change _ = (s ⊗ₜ[(SlopeField n)[X]] (1 : ExtendedBase B)) *
        (1 ⊗ₜ[(SlopeField n)[X]] x)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    exact f.range.mul_mem (f.range.algebraMap_mem _) (hincl x)
end
end K1_14_2_4_1_5_2
end
section
set_option autoImplicit false
namespace K1_14_6_1
noncomputable section
open K1 K1_14 K1_14_6
open scoped Polynomial
private abbrev Dual := TrivSqZeroExt FX FX
private abbrev incl := algebraMap L[X] FX
private def polyJet : L[X] →+* Dual where
  toFun g := (incl g, incl g.derivative)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' g h := by
    apply TrivSqZeroExt.ext
    · change incl (g + h) = incl g + incl h
      exact map_add _ _ _
    · change incl ((g + h).derivative) = incl g.derivative + incl h.derivative
      rw [map_add, map_add]
  map_mul' g h := by
    apply TrivSqZeroExt.ext
    · change incl (g * h) = incl g * incl h
      exact map_mul _ _ _
    · change incl ((g * h).derivative) =
        incl g * incl h.derivative + incl g.derivative * incl h
      rw [Polynomial.derivative_mul, map_add, map_mul, map_mul, add_comm]
private theorem polyJet_fst (g : L[X]) : (polyJet g).fst = incl g := rfl
private def rationalJet : FX →+* Dual :=
  IsLocalization.lift (M := nonZeroDivisors L[X]) (g := polyJet)
    (fun g => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
      (isUnit_iff_ne_zero.mpr (by
        rw [polyJet_fst]
        simpa only [map_zero] using (IsFractionRing.injective L[X] FX).ne (mem_nonZeroDivisors_iff_ne_zero.mp g.2))))
private theorem rationalJet_incl (g : L[X]) : rationalJet (incl g) = polyJet g := by
  exact IsLocalization.lift_eq _ _
private theorem rationalJet_fst (a : FX) : (rationalJet a).fst = a := by
  have h : (TrivSqZeroExt.fstHom FX FX FX).toRingHom.comp rationalJet = RingHom.id FX := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors L[X])
    apply RingHom.ext
    intro g
    exact congrArg TrivSqZeroExt.fst (rationalJet_incl g)
  exact RingHom.congr_fun h a
def Dx : FX →+ FX :=
  (TrivSqZeroExt.sndHom (R := FX) (M := FX)).toAddMonoidHom.comp rationalJet.toAddMonoidHom
theorem Dx_mul (a b : FX) : Dx (a * b) = a * Dx b + Dx a * b := by
  change (rationalJet (a * b)).snd = _
  rw [map_mul]
  change (rationalJet a).fst * Dx b + Dx a * (rationalJet b).fst = _
  rw [rationalJet_fst, rationalJet_fst]
theorem Dx_atX (g : K[X]) : Dx (atX g) = atX g.derivative := by
  change (rationalJet (incl (liftPoly g))).snd = _
  rw [rationalJet_incl]
  change incl (liftPoly g).derivative = incl (liftPoly g.derivative)
  rw [liftPoly, Polynomial.derivative_map, liftPoly]
private theorem Dx_seed (z : K) : Dx (seedEmbedding z) = 0 := by
  change (rationalJet (incl (Polynomial.C (algebraMap K L z)))).snd = _
  rw [rationalJet_incl]
  change incl (Polynomial.derivative (Polynomial.C (algebraMap K L z))) = _
  simp
theorem Dx_pow (a : FX) (n : ℕ) : Dx (a ^ n) = (n : FX) * a ^ (n - 1) * Dx a := by
  cases n with
  | zero =>
    change (rationalJet (a ^ 0)).snd = _
    simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ a (n + 1), Dx_mul, ih]
      push_cast
      simp only [pow_succ a n]
      ring
open MvPolynomial
def partialX : Biform →+ Biform :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom Dx).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
theorem coeff_partialX (P : Biform) (m : Option (Fin 2) →₀ ℕ) :
    (partialX P).coeff m = Dx (P.coeff m) := rfl
private theorem partialX_C (a : FX) : partialX (C a) = C (Dx a) := by
  ext m
  classical
  by_cases h : (0 : Option (Fin 2) →₀ ℕ) = m <;> simp [coeff_partialX, coeff_C, h]
private theorem partialX_mul_X (Q : Biform) (i : Option (Fin 2)) :
    partialX (Q * MvPolynomial.X i) = partialX Q * MvPolynomial.X i := by
  classical
  ext m
  simp only [coeff_partialX, coeff_mul_X']
  split <;> simp
theorem Dx_eval (z : K) (S : K[X]) (P : Biform) :
    Dx (eval (rootPoint z S) P) =
      eval (rootPoint z S) (partialX P) +
        atX S.derivative * eval (rootPoint z S) (pderiv none P) := by
  classical
  let ev := eval (rootPoint z S)
  change Dx (ev P) = ev (partialX P) + atX S.derivative * ev (pderiv none P)
  induction P using MvPolynomial.induction_on with
  | C a => simp [ev, partialX_C]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, mul_add]
    ring
  | mul_X P i hP =>
    have hi : Dx (rootPoint z S i) =
        atX S.derivative * ev (pderiv none (MvPolynomial.X i)) := by
      cases i with
      | none => simp [rootPoint, ev, Dx_atX]
      | some j =>
        fin_cases j <;> simp [rootPoint, ev, pderiv_X, Dx_seed, Dx_pow]
    simp only [map_mul, Dx_mul, hP, partialX_mul_X, pderiv_mul, map_add]
    rw [show ev (MvPolynomial.X i) = rootPoint z S i by simp [ev], hi]
    ring
end
end K1_14_6_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace K1_14_2_4_3_2
noncomputable section
private theorem polynomial_pencil_regular {R : Type*} [CommRing R] (a b : R) (p : Polynomial R)
    (h : IsUnit a ∨ IsUnit b)
    (hp : (Polynomial.C a - Polynomial.C b * Polynomial.X) * p = 0) : p = 0 := by
  rcases h with ha | hb
  · apply Polynomial.ext
    intro n
    simp only [Polynomial.coeff_zero]
    induction n with
    | zero =>
        have he := congrArg (fun f : Polynomial R => f.coeff 0) hp
        apply ha.mul_left_inj.mp
        simpa [sub_mul, mul_assoc, mul_comm a] using he
    | succ n ih =>
        have he := congrArg (fun f : Polynomial R => f.coeff (n + 1)) hp
        apply ha.mul_left_inj.mp
        simpa [sub_mul, mul_assoc, Polynomial.coeff_X_mul, ih, mul_comm a] using he
  · obtain ⟨b', hb'⟩ := hb.exists_right_inv
    have he : Polynomial.C a - Polynomial.C b * Polynomial.X =
        Polynomial.C (-b) * (Polynomial.X - Polynomial.C (b' * a)) := by
      rw [mul_sub, ← Polynomial.C_mul, neg_mul, ← mul_assoc, hb', one_mul, Polynomial.C_neg]
      simp [sub_eq_add_neg, add_comm]
    rw [he, mul_assoc] at hp
    exact (Polynomial.monic_X_sub_C (b' * a)).mul_right_eq_zero_iff.mp
      ((IsUnit.mul_right_eq_zero (hb.neg.map Polynomial.C)).mp hp)
private theorem pencil_killed_by_power {R σ : Type*} [CommRing R] (a b s : R)
    (hs : s = a ∨ s = b) (p : MvPolynomial (Option σ) R)
    (hp : (MvPolynomial.C a - MvPolynomial.C b * MvPolynomial.X none) * p = 0) :
    ∃ j : ℕ, (MvPolynomial.C s) ^ j * p = 0 := by
  let L := Localization.Away s
  let g := MvPolynomial.map (algebraMap R L) (σ := Option σ)
  let e := MvPolynomial.optionEquivLeft L σ
  have hu : IsUnit (algebraMap R L a) ∨ IsUnit (algebraMap R L b) := by
    rcases hs with rfl | rfl
    · exact Or.inl (IsLocalization.Away.algebraMap_isUnit _)
    · exact Or.inr (IsLocalization.Away.algebraMap_isUnit _)
  have hh : e (g p) = 0 := by
    apply polynomial_pencil_regular _ _ _ (hu.imp (fun h => h.map MvPolynomial.C)
      (fun h => h.map MvPolynomial.C))
    simpa [g, e] using congrArg (fun z => e (g z)) hp
  have hzero : g p = 0 := e.injective (hh.trans (map_zero e).symm)
  let _ : Algebra (MvPolynomial (Option σ) R) (MvPolynomial (Option σ) L) :=
    MvPolynomial.algebraMvPolynomial (R := R) (S := L)
  have hz : algebraMap (MvPolynomial (Option σ) R) (MvPolynomial (Option σ) L) p = 0 := hzero
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff
    ((Submonoid.powers s).map (MvPolynomial.C (σ := Option σ)))
    (MvPolynomial (Option σ) L) p).mp hz
  obtain ⟨r, hr, he⟩ := t.property
  obtain ⟨j, rfl⟩ := hr
  refine ⟨j, ?_⟩
  rw [← map_pow (MvPolynomial.C (σ := Option σ)), he]
  exact ht
private theorem radical_annihilator {R : Type*} [CommRing R] [IsNoetherianRing R]
    (T : Submodule R R) (s : R) (hs : ∀ t ∈ T, ∃ j : ℕ, s ^ j * t = 0) :
    s ∈ T.annihilator.radical := by
  let f : Module.End R R := LinearMap.mulLeft R s
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine Ideal.mem_radical_iff.mpr ⟨n, Submodule.mem_annihilator.mpr fun t ht => ?_⟩
  obtain ⟨j, hj⟩ := hs t ht
  have hm : t ∈ LinearMap.ker (f ^ (n + j)) := by
    simp [LinearMap.mem_ker, f, LinearMap.pow_mulLeft, pow_add, hj]
  have he : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + j)) :=
    hn (n + j) (Nat.le_add_right n j)
  rw [← he] at hm
  simpa [f, LinearMap.pow_mulLeft, smul_eq_mul] using hm
theorem high_pencil {R σ : Type*} [CommRing R] [IsNoetherianRing R] [Finite σ] (a b : R) :
    ∃ N : ℕ, ∀ p ∈ (Ideal.span {MvPolynomial.C a, MvPolynomial.C b} :
      Ideal (MvPolynomial (Option σ) R)) ^ N,
      (MvPolynomial.C a - MvPolynomial.C b * MvPolynomial.X none) * p = 0 → p = 0 := by
  let Q := MvPolynomial (Option σ) R
  let I : Ideal Q := Ideal.span {MvPolynomial.C a, MvPolynomial.C b}
  let q : Q := MvPolynomial.C a - MvPolynomial.C b * MvPolynomial.X none
  let T : Submodule Q Q := LinearMap.ker (LinearMap.mulLeft Q q)
  have hi : I ≤ T.annihilator.radical := by
    apply Ideal.span_le.mpr
    intro s hs
    rcases (show s = MvPolynomial.C a ∨ s = MvPolynomial.C b from by simpa using hs) with rfl | rfl
    · exact radical_annihilator T _ fun p hp => pencil_killed_by_power a b a (Or.inl rfl) p hp
    · exact radical_annihilator T _ fun p hp => pencil_killed_by_power a b b (Or.inr rfl) p hp
  obtain ⟨l, hl⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hi (IsNoetherian.noetherian I)
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul T
  refine ⟨k + l, fun p hp hqp => ?_⟩
  have hsmul : p ∈ I ^ (k + l) • (⊤ : Submodule Q Q) := by
    simpa [Ideal.smul_eq_mul] using hp
  have hmem : p ∈ I ^ (k + l) • (⊤ : Submodule Q Q) ⊓ T := ⟨hsmul, hqp⟩
  rw [hk _ (Nat.le_add_right k l), Nat.add_sub_cancel_left] at hmem
  have hs : I ^ l • (I ^ k • (⊤ : Submodule Q Q) ⊓ T) ≤ (⊥ : Submodule Q Q) :=
    Submodule.smul_le.mpr fun s hs x hx => (Submodule.mem_bot Q).mpr
      (Submodule.mem_annihilator.mp (hl hs) x hx.2)
  exact (Submodule.mem_bot Q).mp (hs hmem)
end
end K1_14_2_4_3_2
end
section
namespace K1_14_2_4_1_2_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4_1 K1_14_2_4_1_2
open scoped Polynomial
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
private theorem residue_isAlgebraic {k F E : Type} [Field k] [Field F] [Field E]
    [Algebra k F] (f : F →+* E) (V : ValuationSubring E) (c : k →+* V)
    (hc : ∀ b, (c b : E) = f (algebraMap k F b))
    {t d : F} (ht : IsTranscendenceBasis k (fun _ : Unit => t))
    (hd : d ≠ 0) (u : V) (hu : (u : E) = f d) (hu0 : IsLocalRing.residue V u = 0)
    (a : F) (x : V) (hx : (x : E) = f a) :
    letI : Algebra k (IsLocalRing.ResidueField V) :=
      ((IsLocalRing.residue V).comp c).toAlgebra
    IsAlgebraic k (IsLocalRing.residue V x) := by
  classical
  let res := IsLocalRing.residue V
  let _ : Algebra k (IsLocalRing.ResidueField V) := (res.comp c).toAlgebra
  by_contra htr
  have hres (q : k[X]) (hq : q ≠ 0) : res (q.eval₂ c x) ≠ 0 := by
    rw [Polynomial.hom_eval₂]
    exact fun h => hq ((transcendental_iff.mp htr) q h)
  have hinc : V.toSubring.subtype.comp c = f.comp (algebraMap k F) :=
    RingHom.ext hc
  have hval (q : k[X]) :
      V.toSubring.subtype (q.eval₂ c x) = f (Polynomial.aeval a q) := by
    rw [Polynomial.hom_eval₂, hinc, show V.toSubring.subtype x = f a from hx,
      Polynomial.aeval_def, Polynomial.hom_eval₂]
  have ha : Transcendental k a := transcendental_iff.mpr fun q hq => by
    by_contra hq0
    have he : q.eval₂ c x = 0 := by
      apply V.toSubring.subtype_injective
      rw [hval, hq, map_zero, map_zero]
    exact hres q hq0 (by rw [he, map_zero])
  have haBasis : IsTranscendenceBasis k (fun _ : Unit => a) :=
    ((algebraicIndependent_singleton_iff ()).mpr ha).isTranscendenceBasis_of_trdeg_le_of_finite
      ht.cardinalMk_eq_trdeg.ge
  let A := Algebra.adjoin k (Set.range (fun _ : Unit => a))
  have halg : Algebra.IsAlgebraic A F := haBasis.isAlgebraic
  have hrange : Set.range (fun _ : Unit => a) = {a} := by simp
  let v := V.valuation.comap f
  let _ : v.IsTrivialOn A := by
    constructor
    intro b hb
    have hmem : (b : F) ∈ Algebra.adjoin k ({a} : Set F) := by
      rw [← hrange]
      exact b.property
    obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval k a hmem
    have hq0 : q ≠ 0 := by
      intro h
      apply hb
      apply Subtype.ext
      simpa [h] using hq.symm
    have hunit := (IsLocalRing.residue_ne_zero_iff_isUnit (q.eval₂ c x)).mp (hres q hq0)
    change V.valuation (f (b : F)) = 1
    rw [← hq, ← hval]
    exact (V.valuation_eq_one_iff _).mp hunit
  have hdv : v d ≠ 1 := by
    intro h
    have he : V.valuation (u : E) = 1 := by
      rw [hu]
      exact h
    exact (IsLocalRing.residue_ne_zero_iff_isUnit u).mpr
      ((V.valuation_eq_one_iff u).mpr he) hu0
  exact (v.transcendental_of_ne_one _ d hd hdv) (halg.isAlgebraic d)
private theorem residue_eq_constant {k E : Type} [Field k] [IsAlgClosed k] [Field E]
    [Algebra k E] {x : E} (hx : IsAlgebraic k x) : ∃ b : k, x = algebraMap k E b := by
  let A := IntermediateField.adjoin k ({x} : Set E)
  let _ : Algebra.IsAlgebraic k A := IntermediateField.isAlgebraic_adjoin_simple hx.isIntegral
  have hA : A = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic A
  have hxA : x ∈ A := IntermediateField.subset_adjoin k _ (Set.mem_singleton x)
  rw [hA] at hxA
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.mp hxA
  exact ⟨b, hb.symm⟩
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g : ℕ}
variable {R : PrimitiveRoot C₀ J g} {z : K} {S : K[X]} (M : MarkLift R z S)
private theorem generic_constant (b : L) :
    (M.constant b : RootField R) = seedInRoot R (constToSeed C₀ b) := by
  change (M.V.toSubring.subtype.comp M.ambient) (MvPolynomial.C (algebraMap L FX b)) = _
  rw [M.generic_eq]
  simp only [K1_14_2_4_1_2.generic, RingHom.comp_apply, genericRootMap, MvPolynomial.eval₂Hom_C,
    AdjoinRoot.mk_C]
  change AdjoinRoot.of (rootEquation R) (extendX C₀ (algebraMap L FX b)) = _
  unfold seedInRoot
  rw [RingHom.comp_apply]
  congr 1
  rw [IsScalarTower.algebraMap_apply L L[X] FX]
  unfold extendX IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertConstant, insertX]
private def seedVariable (i : Fin 2) : RootAmbient :=
  MvPolynomial.X (Fin.castLE (by decide : 2 ≤ 3) i)
private theorem generic_coordinate (i : Fin 2) :
    (M.ambient (seedVariable i) : RootField R) = seedInRoot R (seedCoordinate C₀ i) := by
  change (M.V.toSubring.subtype.comp M.ambient) (seedVariable i) = _
  rw [M.generic_eq]
  fin_cases i <;> simp [seedVariable, K1_14_2_4_1_2.generic, genericRootMap, seedInRoot]
private def markedConstant (z : K) (i : Fin 2) : L :=
  ![algebraMap K L z, (algebraMap K L z) ^ p] i
private theorem seedEmbedding_eq (z : K) :
    seedEmbedding z = algebraMap L FX (algebraMap K L z) := by
  rw [IsScalarTower.algebraMap_apply L L[X] FX]
  rfl
private theorem markVector (a : L) (e : ℕ) (y : FX) (i : Fin 2) :
    (![algebraMap L FX a, (algebraMap L FX a) ^ e, y] : Fin 3 → FX)
      (Fin.castLE (by decide : 2 ≤ 3) i) = algebraMap L FX (![a, a ^ e] i) := by
  fin_cases i
  · rfl
  · exact (map_pow (algebraMap L FX) a e).symm
private theorem marked_coordinate (i : Fin 2) :
    IsLocalRing.residue M.V (M.ambient (seedVariable i)) =
      IsLocalRing.residue M.V (M.constant (markedConstant z i)) := by
  change ((IsLocalRing.residue M.V).comp M.ambient) (seedVariable i) = _
  rw [M.marked_eq]
  simp only [seedVariable, RingHom.comp_apply, rootMarkHom, MvPolynomial.eval_X]
  change IsLocalRing.residue M.V (M.fx (![seedEmbedding z, (seedEmbedding z) ^ p, atX S]
    (Fin.castLE (by decide : 2 ≤ 3) i))) =
    IsLocalRing.residue M.V (M.fx (algebraMap L FX (markedConstant z i)))
  rw [seedEmbedding_eq, markVector]
  rfl
theorem proof : K1_14_2_4_1_2.c2 := by
  intro C₀ _ J g R z S M i
  let _ : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  intro hi a ha
  let t := seedCoordinate C₀ i
  let b := markedConstant z i
  let d := t - algebraMap L (ConstantSeedField C₀) b
  have hd : d ≠ 0 := by
    have htr : Transcendental L t := hi.1.transcendental ()
    intro h
    refine htr ⟨Polynomial.X - Polynomial.C b, Polynomial.X_sub_C_ne_zero b, ?_⟩
    simpa using h
  let u : M.V := M.ambient (seedVariable i) - M.constant b
  have hu : (u : RootField R) = seedInRoot R d := by
    change (M.ambient (seedVariable i) : RootField R) - (M.constant b : RootField R) = _
    simp only [generic_coordinate, generic_constant, d, t, map_sub]
    rfl
  have hu0 : IsLocalRing.residue M.V u = 0 := by
    change IsLocalRing.residue M.V (M.ambient (seedVariable i) - M.constant b) = 0
    rw [map_sub, marked_coordinate, sub_self]
  let x : M.V := ⟨seedInRoot R a, ha⟩
  let _ : Algebra L (IsLocalRing.ResidueField M.V) :=
    ((IsLocalRing.residue M.V).comp M.constant).toAlgebra
  have hx := residue_isAlgebraic (seedInRoot R) M.V M.constant (generic_constant M)
    hi hd u hu hu0 a x rfl
  exact residue_eq_constant hx
end
end K1_14_2_4_1_2_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_2
noncomputable section
open K1_14_2_4 K1_14_2_4_3
def c1 : Prop :=
  ∀ (n : ℕ) (J : Ideal (SourceRing n)), J.IsPrime →
    (MvPolynomial.affineHilbertPolynomial J).natDegree = 1 → ∃ N : ℕ,
    ∀ u v : ℕ, N ≤ u → N ≤ v →
      (∀ p ∈ polynomialBox J (u + 1, v),
        polynomialCut J * p ∈ polynomialBox J (u + 1, v) → p ∈ polynomialBox J (u, v)) ∧
      (∀ p ∈ polynomialBox J (u, v + 1),
        polynomialCut J * p ∈ polynomialBox J (u + 1, v) → p ∈ polynomialBox J (u, v))
def c2 : Prop :=
  ∀ (n : ℕ) (J : Ideal (SourceRing n)), Nonempty (CoefficientTransport J)
private theorem transfer {n : ℕ} {J : Ideal (SourceRing n)} (T : CoefficientTransport J)
    (d e f : ℕ × ℕ)
    (h : ∀ p ∈ polynomialBox J d, polynomialCut J * p ∈ polynomialBox J e →
      p ∈ polynomialBox J f)
    (x : ExtendedRing J) (hx : x ∈ box J d.1 d.2)
    (hq : cutClass J (ordinateCut n) * x ∈ box J e.1 e.2) : x ∈ box J f.1 f.2 := by
  obtain ⟨s, hs, p, q, hp, hq', hpe, hqe⟩ := T.clear_boxes d e x _ hx hq
  have he : polynomialCut J * p = q := T.injective_toSlice (by
    rw [map_mul, T.cut_eq, hpe, hqe, mul_smul_comm])
  have hm := T.map_box f p (h p hp (he.symm ▸ hq'))
  rw [hpe] at hm
  simpa [smul_smul, hs] using (box J f.1 f.2).smul_mem s⁻¹ hm
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_4_3.c2 := by
  intro n J hJ hdim
  obtain ⟨T⟩ := h2 n J
  obtain ⟨N, hN⟩ := h1 n J hJ hdim
  refine ⟨N, fun u v hu hv => ⟨?_, ?_⟩⟩
  · exact transfer T (u + 1, v) (u + 1, v) (u, v) (hN u v hu hv).1
  · exact transfer T (u, v + 1) (u + 1, v) (u, v) (hN u v hu hv).2
end
end K1_14_2_4_3_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_1_5_2
noncomputable section
open K1_14_2_4_1_5
open scoped Polynomial TensorProduct
variable {F A : Type} [Field F] [CommRing A] [Algebra F A]
private def boundedProducts {ι : Type} (a : A) (w : ι → A) (d : ℕ) :
    Submodule F A :=
  Submodule.span F (Set.range fun ij : Fin d × ι => a ^ (ij.1 : ℕ) * w ij.2)
private instance {ι : Type} [Finite ι] (a : A) (w : ι → A) (d : ℕ) :
    Module.Finite F (boundedProducts (F := F) a w d) :=
  Module.Finite.span_of_finite F (Set.finite_range _)
private theorem eval_mem_bounded {ι : Type} (a : A) (w : ι → A)
    {d : ℕ} (i : ι) (p : F[X]) (hp : p.degree < d) :
    Polynomial.aeval a p * w i ∈ boundedProducts (F := F) a w d := by
  let L : Polynomial.degreeLT F d →ₗ[F] A :=
    (LinearMap.mulRight F (w i)).comp
      ((Polynomial.aeval a).toLinearMap.comp (Polynomial.degreeLT F d).subtype)
  let x : Polynomial.degreeLT F d := ⟨p, Polynomial.mem_degreeLT.mpr hp⟩
  change L x ∈ boundedProducts (F := F) a w d
  rw [← (Polynomial.degreeLT.basis F d).sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨⟨j, i⟩, ?_⟩
  simp [L]
private theorem powerSpan_le_bounded {ι : Type} (a : A) (w : ι → A)
    (W : Submodule F A) (hW : W = Submodule.span F (Set.range w)) (k : ℕ) :
    powerSpan a W k ≤ boundedProducts a w (k + 1) := by
  have hbase (d : ℕ) (hd : 0 < d) : W ≤ boundedProducts a w d := by
    rw [hW]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨⟨⟨0, hd⟩, i⟩, by simp⟩
  induction k with
  | zero => exact hbase 1 (by decide)
  | succ k ih =>
    change W ⊔ (powerSpan a W k).map (LinearMap.mulLeft F a) ≤ boundedProducts a w (k + 1 + 1)
    refine sup_le (hbase _ (by omega)) ((Submodule.map_mono ih).trans ?_)
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, i⟩, rfl⟩
    change a * (a ^ (j : ℕ) * w i) ∈ boundedProducts (F := F) a w (k + 1 + 1)
    rw [← mul_assoc, ← pow_succ']
    apply Submodule.subset_span
    exact ⟨⟨j.succ, i⟩, rfl⟩
private theorem growth_of_relations (a : A) (W : Submodule F A)
    {m r : ℕ} (w : Fin m → A) (v : Fin r → A)
    (hW : W = Submodule.span F (Set.range w))
    (b : F[X]) (hb : b ≠ 0) (q : Fin m → Fin r → F[X])
    (hrel : ∀ i, Polynomial.aeval a b * w i = ∑ j, Polynomial.aeval a (q i j) * v j) :
    ∃ C : ℕ, ∀ k : ℕ, Module.finrank F (powerSpan a W k) ≤ C + k * r := by
  classical
  let D := Finset.univ.sup (fun ij : Fin m × Fin r => (q ij.1 ij.2).natDegree)
  have hD (i : Fin m) (j : Fin r) : (q i j).natDegree ≤ D :=
    Finset.le_sup (s := Finset.univ) (f := fun ij : Fin m × Fin r => (q ij.1 ij.2).natDegree)
      (Finset.mem_univ (i, j))
  refine ⟨(b.natDegree + 1) * m + (D + 1) * r, fun k => ?_⟩
  let U := boundedProducts (F := F) a w (b.natDegree + 1)
  let V := boundedProducts (F := F) a v (k + D + 1)
  have hUV : boundedProducts a w (k + 1) ≤ U ⊔ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, i⟩, rfl⟩
    let p : F[X] := Polynomial.X ^ (l : ℕ)
    have hrem : (p % b).degree < b.natDegree + 1 :=
      (Polynomial.degree_mod_lt p hb).trans (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self _))
    have hl : (p / b).natDegree ≤ k := Polynomial.natDegree_le_of_degree_le
      ((Polynomial.degree_div_le p b).trans
        (Polynomial.degree_X_pow_le _ |>.trans (by exact_mod_cast Nat.le_of_lt_succ l.isLt)))
    have hquot (j : Fin r) : (p / b * q i j).degree < k + D + 1 := by
      have h := (Polynomial.natDegree_mul_le (p := p / b) (q := q i j)).trans
        (Nat.add_le_add hl (hD i j))
      exact (Polynomial.degree_le_of_natDegree_le h).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
    have hsplit : a ^ (l : ℕ) * w i =
        (∑ j, Polynomial.aeval a (p / b * q i j) * v j) +
          Polynomial.aeval a (p % b) * w i := by
      have h := congrArg (fun x : F[X] => Polynomial.aeval a x * w i)
        (EuclideanDomain.div_add_mod p b).symm
      change Polynomial.aeval a p * w i = _ at h
      rw [Polynomial.aeval_X_pow] at h
      simp only [map_add, map_mul, add_mul] at h ⊢
      rw [h, mul_comm (Polynomial.aeval a b) (Polynomial.aeval a (p / b)),
        mul_assoc, hrel i, Finset.mul_sum]
      simp only [mul_assoc]
    change a ^ (l : ℕ) * w i ∈ U ⊔ V
    rw [hsplit]
    exact (U ⊔ V).add_mem
      ((show V ≤ U ⊔ V from le_sup_right) (V.sum_mem fun j _ => eval_mem_bounded a v j _ (hquot j)))
      ((show U ≤ U ⊔ V from le_sup_left) (eval_mem_bounded a w i _ hrem))
  have bound (d e : ℕ) (u : Fin e → A) :
      Module.finrank F (boundedProducts (F := F) a u d) ≤ d * e := by
    let gen : Fin d × Fin e → A := fun ij => a ^ (ij.1 : ℕ) * u ij.2
    change (Set.range gen).finrank F ≤ d * e
    have hc : Fintype.card (Fin d × Fin e) = d * e := by simp [Fintype.card_prod]
    exact hc ▸ finrank_range_le_card (R := F) gen
  have h := (Submodule.finrank_mono ((powerSpan_le_bounded a w W hW k).trans hUV)).trans
    ((Submodule.finrank_add_le_finrank_add_finrank U V).trans (Nat.add_le_add (bound _ _ w) (bound _ _ v)))
  simpa only [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
theorem growth_of_localized (a : A) (W : Submodule F A) [Module.Finite F W]
    (E : Type) [Field E] [Algebra F[X] E] [IsFractionRing F[X] E]
    (hfinite : letI : Algebra F[X] A := polynomialAction a; Module.Finite E (E ⊗[F[X]] A)) :
    letI : Algebra F[X] A := polynomialAction a
    ∃ C : ℕ, ∀ k : ℕ, Module.finrank F (powerSpan a W k) ≤
      C + k * Module.finrank E (E ⊗[F[X]] A) := by
  classical
  let : Algebra F[X] A := polynomialAction a
  let : Module.Finite E (E ⊗[F[X]] A) := hfinite
  let R := F[X]
  let S := nonZeroDivisors R
  let T := E ⊗[R] A
  let f : A →ₗ[R] T := TensorProduct.mk R E A 1
  let : IsLocalizedModule S f := IsLocalization.tensorProduct_isLocalizedModule S E
  let bW := Module.finBasis F W
  let w := W.subtype ∘ bW
  have hW : W = Submodule.span F (Set.range w) := by
    rw [show Set.range w = W.subtype '' Set.range bW from Set.range_comp _ _,
      ← Submodule.map_span, bW.span_eq, Submodule.map_subtype_top]
  let bT := Module.finBasis E T
  obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples_of_finite S f bT
  choose v hv using hs
  let c (ij : Fin (Module.finrank F W) × Fin (Module.finrank E T)) :=
    bT.repr (f (w ij.1)) ij.2
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite S c
  choose g hg using hd
  have hlift (i : Fin (Module.finrank F W)) :
      f ((s.val * d.val) • w i) = f (∑ j, g (i,j) • v j) := by
    calc
      _ = s.val • (d.val • f (w i)) := by rw [map_smul, mul_smul]
      _ = s.val • (d.val • ∑ j, c (i,j) • bT j) := by rw [← bT.sum_repr (f (w i))]
      _ = ∑ j, g (i,j) • f (v j) := by
        rw [Finset.smul_sum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [← smul_assoc d.val (c (i,j)) (bT j), ← hg (i,j), algebraMap_smul E,
          smul_comm s.val (g (i,j)), ← hv j]
      _ = _ := by simp
  choose t ht using fun i => IsLocalizedModule.exists_of_eq (S := S) (f := f) (hlift i)
  let e := ∏ i, t i
  let b := e.val * (s.val * d.val)
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp
    (show b ∈ S from mul_mem e.property (mul_mem s.property d.property))
  refine growth_of_relations a W w v hW b hb (fun i j => e.val * g (i,j)) ?_
  intro i
  change b • w i = ∑ j, (e.val * g (i,j)) • v j
  have he (x : A) : e.val • x = (∏ j ∈ Finset.univ.erase i, t j).val • (t i).val • x := by
    rw [← mul_smul]
    congr 1
    exact congrArg Subtype.val (Finset.prod_erase_mul Finset.univ t (Finset.mem_univ i)).symm
  rw [show b = e.val * (s.val * d.val) from rfl, mul_smul]
  simp only [mul_smul, ← Finset.smul_sum]
  rw [he, he]
  exact congrArg _ (by simpa only [Submonoid.smul_def, mul_smul] using ht i)
end
end K1_14_2_4_1_5_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_2_2
noncomputable section
open K1_14 K1_14_2_4 K1_14_2_4_3 K1_14_2_4_3_2 MvPolynomial
open scoped BigOperators TensorProduct
variable {n : ℕ} (J : Ideal (SourceRing n))
private def baseChange : SliceField n ⊗[FX] Affine J ≃ₐ[SliceField n] ExtendedRing J := by
  let E := SliceField n
  let R := SourceRing n
  let e₀ : E ⊗[FX] R ≃ₐ[E] SliceAmbient n := MvPolynomial.algebraTensorAlgEquiv FX E
  let i : R →+* E ⊗[FX] R :=
    (Algebra.TensorProduct.includeRight (A := E) (R := FX)).toRingHom
  have hmap : e₀.toAlgHom.toRingHom.comp i = MvPolynomial.map (algebraMap FX E) := by
    apply RingHom.ext
    intro p
    change e₀ (1 ⊗ₜ[FX] p) = MvPolynomial.map (algebraMap FX E) p
    simpa only [e₀, one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul FX E 1 p
  have hI : extendedIdeal J = (J.map i).map e₀.toAlgHom.toRingHom := by
    rw [Ideal.map_map i e₀.toAlgHom.toRingHom, hmap]
  exact (Algebra.TensorProduct.tensorQuotientEquiv E R E J).trans
    (Ideal.quotientEquivAlg (J.map i) (extendedIdeal J) e₀ hI)
private theorem baseChange_tmul (c : SliceField n) (p : SourceRing n) :
    baseChange J (c ⊗ₜ[FX] Ideal.Quotient.mk J p) =
      c • cutClass J (MvPolynomial.map (algebraMap FX (SliceField n)) p) := by
  change cutClass J (MvPolynomial.algebraTensorAlgEquiv FX (SliceField n) (c ⊗ₜ[FX] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact (Ideal.Quotient.mkₐ (SliceField n) (extendedIdeal J)).toLinearMap.map_smul c _
private def toTensor : CoeffPoly J ≃ₐ[FX] SourceRing n ⊗[FX] Affine J := by
  let e : Affine J ⊗[FX] SourceRing n ≃ₐ[Affine J] CoeffPoly J :=
    MvPolynomial.algebraTensorAlgEquiv FX (Affine J)
  exact (e.symm.restrictScalars FX).trans
    (Algebra.TensorProduct.comm FX (Affine J) (SourceRing n))
private def extend : SourceRing n ⊗[FX] Affine J →ₐ[FX] SliceField n ⊗[FX] Affine J :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom FX (SourceRing n) (SliceField n))
    (AlgHom.id FX (Affine J))
private def toSlice : CoeffPoly J →ₐ[FX] ExtendedRing J :=
  ((baseChange J).toAlgHom.restrictScalars FX).comp ((extend J).comp (toTensor J).toAlgHom)
private theorem toSlice_injective : Function.Injective (toSlice J) := by
  have hext : Function.Injective (extend J) := by
    change Function.Injective (TensorProduct.map
      (IsScalarTower.toAlgHom FX (SourceRing n) (SliceField n)).toLinearMap
      (AlgHom.id FX (Affine J)).toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _
      (IsFractionRing.injective (SourceRing n) (SliceField n)) Function.injective_id
  exact (baseChange J).injective.comp (hext.comp (toTensor J).injective)
private theorem toSlice_term (p r : SourceRing n) :
    toSlice J (C (Ideal.Quotient.mk J p) * MvPolynomial.map (algebraMap FX (Affine J)) r) =
      algebraMap (SourceRing n) (SliceField n) r •
        cutClass J (MvPolynomial.map (algebraMap FX (SliceField n)) p) := by
  have hC (a : Affine J) : toTensor J (C a) = (1 : SourceRing n) ⊗ₜ[FX] a := by
    change Algebra.TensorProduct.comm FX (Affine J) (SourceRing n)
      ((MvPolynomial.algebraTensorAlgEquiv FX (Affine J)).symm (monomial 0 a)) = _
    rw [algebraTensorAlgEquiv_symm_monomial, Algebra.TensorProduct.comm_tmul,
      monomial_zero', C_1]
  have hr : toTensor J (MvPolynomial.map (algebraMap FX (Affine J)) r) =
      r ⊗ₜ[FX] (1 : Affine J) := by
    change Algebra.TensorProduct.comm FX (Affine J) (SourceRing n)
      ((MvPolynomial.algebraTensorAlgEquiv FX (Affine J)).symm
        (MvPolynomial.map (algebraMap FX (Affine J)) r)) = _
    simp only [algebraTensorAlgEquiv_symm_map, Algebra.TensorProduct.comm_tmul]
  change baseChange J (extend J (toTensor J
    (C (Ideal.Quotient.mk J p) * MvPolynomial.map (algebraMap FX (Affine J)) r))) = _
  rw [map_mul, hC, hr, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  change baseChange J (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom FX (SourceRing n) (SliceField n)) (AlgHom.id FX (Affine J))
    (r ⊗ₜ[FX] Ideal.Quotient.mk J p)) = _
  rw [Algebra.TensorProduct.map_tmul]
  exact baseChange_tmul J _ p
private theorem toSlice_cut : toSlice J (polynomialCut J) = cutClass J (ordinateCut n) := by
  have hy : toSlice J (C (ordinate J)) = cutClass J (MvPolynomial.X none) := by
    simpa only [map_one, mul_one, one_smul, map_X] using
      toSlice_term J (MvPolynomial.X none) 1
  have hb : toSlice J (MvPolynomial.X none) = cutClass J (C (sliceVariable (n := n) none)) := by
    change _ = algebraMap (SliceField n) (ExtendedRing J) (sliceVariable (n := n) none)
    rw [Algebra.algebraMap_eq_smul_one]
    simpa only [sliceVariable, map_one, C_1, one_mul, map_X] using
      toSlice_term J 1 (MvPolynomial.X none)
  rw [polynomialCut, map_sub, hy, hb, ordinateCut]
  exact (map_sub (Ideal.Quotient.mk (extendedIdeal J)) _ _).symm
private theorem toSlice_map_box (d : ℕ × ℕ) (p : CoeffPoly J)
    (hp : p ∈ polynomialBox J d) : toSlice J p ∈ box J d.1 d.2 := by
  classical
  have hp' (m : Option (Fin n) →₀ ℕ) : p.coeff m ∈ filteredBox J d := hp m
  have hexpand : toSlice J p =
      ∑ m ∈ p.support, toSlice J (monomial m (p.coeff m)) := by
    rw [← map_sum, ← as_sum]
  rw [hexpand]
  apply (box J d.1 d.2).sum_mem
  intro m _
  obtain ⟨f, hf, hf'⟩ := mem_quotientBidegreeLE.mp (hp' m)
  have hm : C (Ideal.Quotient.mk J f) *
      MvPolynomial.map (algebraMap FX (Affine J)) (monomial m 1) =
      monomial m (p.coeff m) := by
    rw [map_monomial, map_one, C_mul_monomial, mul_one, hf']
  rw [← hm, toSlice_term]
  apply (box J d.1 d.2).smul_mem
  exact mem_quotientBidegreeLE.mpr ⟨_, mem_restrictBidegree.mpr fun v hv =>
    mem_restrictBidegree.mp hf v (MvPolynomial.support_map_subset _ _ hv), rfl⟩
private theorem clearRepresentative (d : ℕ × ℕ) (P : SliceAmbient n)
    (hP : P ∈ restrictBidegree (Fin n) (SliceField n) d.1 d.2) (s : SliceField n)
    (hclear : ∀ m ∈ P.support, ∃ r : SourceRing n,
      algebraMap (SourceRing n) (SliceField n) r = s * P.coeff m) :
    ∃ p ∈ polynomialBox J d, toSlice J p = s • cutClass J P := by
  classical
  choose! r hr using hclear
  let term (m : Option (Fin n) →₀ ℕ) : CoeffPoly J :=
    C (Ideal.Quotient.mk J (monomial m 1)) * MvPolynomial.map (algebraMap FX (Affine J)) (r m)
  refine ⟨∑ m ∈ P.support, term m, (polynomialBox J d).sum_mem ?_, ?_⟩
  · intro m hm
    have hmon : monomial m (1 : FX) ∈ restrictBidegree (Fin n) FX d.1 d.2 :=
      mem_restrictBidegree.mpr fun v hv => by
        have hvm : v = m := Finset.mem_singleton.mp (support_monomial_subset hv)
        exact hvm ▸ mem_restrictBidegree.mp hP m hm
    have hclass : Ideal.Quotient.mk J (monomial m 1) ∈ filteredBox J d :=
      mem_quotientBidegreeLE.mpr ⟨_, hmon, rfl⟩
    intro v
    change (term m).coeff v ∈ filteredBox J d
    dsimp only [term]
    rw [coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def]
    exact (filteredBox J d).smul_mem ((r m).coeff v) hclass
  · rw [map_sum]
    calc
      (∑ m ∈ P.support, toSlice J (term m)) =
          ∑ m ∈ P.support, s • cutClass J (monomial m (P.coeff m)) := by
        apply Finset.sum_congr rfl
        intro m hm
        dsimp only [term]
        rw [toSlice_term, hr m hm, ← smul_smul]
        congr 1
        let π := (Ideal.Quotient.mkₐ (SliceField n) (extendedIdeal J)).toLinearMap
        change P.coeff m • π (MvPolynomial.map (algebraMap FX (SliceField n))
          (monomial m 1)) = π (monomial m (P.coeff m))
        rw [← π.map_smul, map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
      _ = s • cutClass J P := by
        rw [← Finset.smul_sum, ← map_sum, ← as_sum]
private theorem toSlice_clear_boxes (d e : ℕ × ℕ) (x t : ExtendedRing J)
    (hx : x ∈ box J d.1 d.2) (ht : t ∈ box J e.1 e.2) :
    ∃ (s : SliceField n) (_ : s ≠ 0) (p q : CoeffPoly J),
      p ∈ polynomialBox J d ∧ q ∈ polynomialBox J e ∧
        toSlice J p = s • x ∧ toSlice J q = s • t := by
  classical
  obtain ⟨P, hP, rfl⟩ := mem_quotientBidegreeLE.mp hx
  obtain ⟨Q, hQ, rfl⟩ := mem_quotientBidegreeLE.mp ht
  let coeffs := P.support.image P.coeff ∪ Q.support.image Q.coeff
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors (SourceRing n)) coeffs id
  let s := algebraMap (SourceRing n) (SliceField n) (b : SourceRing n)
  have hs : s ≠ 0 := by
    intro h
    apply mem_nonZeroDivisors_iff_ne_zero.mp b.property
    exact (IsFractionRing.injective (SourceRing n) (SliceField n)) (h.trans (map_zero _).symm)
  have hclear (c : SliceField n) (hc : c ∈ coeffs) :
      ∃ r : SourceRing n, algebraMap (SourceRing n) (SliceField n) r = s * c := by
    simpa only [s, IsLocalization.IsInteger, RingHom.mem_rangeS, id_eq, Algebra.smul_def]
      using hb c hc
  obtain ⟨p, hp, hpx⟩ := clearRepresentative J d P hP s fun m hm =>
    hclear _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm))
  obtain ⟨q, hq, hqt⟩ := clearRepresentative J e Q hQ s fun m hm =>
    hclear _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm))
  exact ⟨s, hs, p, q, hp, hq, hpx, hqt⟩
theorem proof : K1_14_2_4_3_2.c2 := by
  intro n J
  exact ⟨{
    toSlice := toSlice J
    injective_toSlice := toSlice_injective J
    cut_eq := toSlice_cut J
    map_box := toSlice_map_box J
    clear_boxes := toSlice_clear_boxes J
  }⟩
end
end K1_14_2_4_3_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 8
namespace K1_14_2_4_1_4_3
open K1_14_2_4_1_4
open scoped TensorProduct
noncomputable section
private abbrev ordinateAlgebra {k A : Type} [Field k] [CommRing A] [Algebra k A]
    (y : A) : Algebra (Polynomial k) A :=
  (Polynomial.aeval y : Polynomial k →ₐ[k] A).toRingHom.toAlgebra
private abbrev offsetPolynomial {k ι : Type} [Field k] (offset : ι) :
    Polynomial k →ₐ[k] MvPolynomial ι k :=
  Polynomial.aeval (MvPolynomial.X offset)
private abbrev offsetPolynomialAlgebra {k ι : Type} [Field k] (offset : ι) :
    Algebra (Polynomial k) (MvPolynomial ι k) :=
  (offsetPolynomial offset).toRingHom.toAlgebra
private theorem offsetMap_C {k ι A : Type} [Field k] [CommRing A] [Algebra k A]
    (offset : ι) (y : A) (a : k) :
    offsetMap offset (MvPolynomial.C y) (MvPolynomial.C a) =
      MvPolynomial.C (algebraMap k A a) := by
  classical
  simp [offsetMap]
private theorem offsetMap_offset {k ι A : Type} [Field k] [CommRing A] [Algebra k A]
    (offset : ι) (y : A) :
    offsetMap (k := k) offset (MvPolynomial.C y) (MvPolynomial.X offset) = MvPolynomial.C y := by
  classical
  simp [offsetMap]
private theorem offsetMap_other {k ι A : Type} [Field k] [CommRing A] [Algebra k A]
    (offset : ι) (y : A) (i : Other offset) :
    offsetMap (k := k) offset (MvPolynomial.C y) (MvPolynomial.X i.val) = MvPolynomial.X i := by
  classical
  simp [offsetMap, i.property]
private def polynomialFibreEquiv {k ι A : Type} [Field k] [CommRing A] [Algebra k A]
    (offset : ι) (y : A) :
    letI := offsetPolynomialAlgebra (k := k) offset
    letI := ordinateAlgebra (k := k) y
    letI := offsetAlgebra (k := k) offset (MvPolynomial.C y)
    MvPolynomial (Other offset) A ≃ₐ[MvPolynomial ι k] MvPolynomial ι k ⊗[Polynomial k] A := by
  classical
  let S := Polynomial k
  let T := MvPolynomial ι k
  let U := MvPolynomial (Other offset) A
  letI : Algebra S T := offsetPolynomialAlgebra offset
  letI : Algebra S A := ordinateAlgebra y
  letI : Algebra T U := offsetAlgebra offset (MvPolynomial.C y)
  let V := T ⊗[S] A
  letI : Algebra S U := Algebra.restrictScalars S T U
  let := IsScalarTower.of_algebraMap_eq (R := S) (S := T) (A := U) fun _ => rfl
  let right : A →ₐ[S] V := Algebra.TensorProduct.includeRight
  let left : T →ₐ[T] V := Algebra.TensorProduct.includeLeft
  let eval : U →+* V :=
    MvPolynomial.eval₂Hom right.toRingHom (fun i => left (MvPolynomial.X i.val))
  have balance (p : S) : right (Polynomial.aeval y p) = left (offsetPolynomial offset p) :=
    right.commutes p
  have forwardCommutes : eval.comp (offsetMap offset (MvPolynomial.C y)) = left.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change eval (offsetMap (k := k) offset (MvPolynomial.C y) (MvPolynomial.C a)) =
        left (MvPolynomial.C a)
      rw [offsetMap_C]
      calc
        eval (MvPolynomial.C (algebraMap k A a)) = right (algebraMap k A a) :=
          MvPolynomial.eval₂Hom_C _ _ _
        _ = left (MvPolynomial.C a) := by
          simpa only [Polynomial.aeval_C, MvPolynomial.algebraMap_eq] using balance (Polynomial.C a)
    · intro i
      by_cases hi : i = offset
      · subst i
        change eval (offsetMap (k := k) offset (MvPolynomial.C y) (MvPolynomial.X offset)) =
          left (MvPolynomial.X offset)
        rw [offsetMap_offset]
        calc
          eval (MvPolynomial.C y) = right y := MvPolynomial.eval₂Hom_C _ _ _
          _ = left (MvPolynomial.X offset) := by
            simpa only [Polynomial.aeval_X, offsetPolynomial] using balance Polynomial.X
      · change eval (offsetMap (k := k) offset (MvPolynomial.C y) (MvPolynomial.X i)) =
          left (MvPolynomial.X i)
        rw [offsetMap_other offset y ⟨i, hi⟩]
        exact MvPolynomial.eval₂Hom_X' _ _ _
  let forward : U →ₐ[T] V :=
    { toRingHom := eval
      commutes' a := DFunLike.congr_fun forwardCommutes a }
  have coordCommutes : MvPolynomial.C.comp (algebraMap S A) = algebraMap S U := by
    apply Polynomial.ringHom_ext
    · intro a
      change MvPolynomial.C (Polynomial.aeval y (Polynomial.C a)) =
        offsetMap offset (MvPolynomial.C y) (offsetPolynomial offset (Polynomial.C a))
      rw [Polynomial.aeval_C, offsetPolynomial, Polynomial.aeval_C, MvPolynomial.algebraMap_eq,
        offsetMap_C]
    · change MvPolynomial.C (Polynomial.aeval y Polynomial.X) =
        offsetMap offset (MvPolynomial.C y) (offsetPolynomial offset Polynomial.X)
      rw [Polynomial.aeval_X, offsetPolynomial, Polynomial.aeval_X, offsetMap_offset]
  let coord : A →ₐ[S] U :=
    { toRingHom := MvPolynomial.C
      commutes' p := DFunLike.congr_fun coordCommutes p }
  let backward : V →ₐ[T] U :=
    Algebra.TensorProduct.lift (Algebra.ofId T U) coord (fun _ _ => mul_comm _ _)
  have backward_left (p : T) : backward (p ⊗ₜ[S] (1 : A)) = algebraMap T U p :=
    (Algebra.TensorProduct.lift_tmul (Algebra.ofId T U) coord (fun _ _ => mul_comm _ _) p 1).trans
      (by rw [map_one, mul_one]; rfl)
  have backward_right (a : A) : backward ((1 : T) ⊗ₜ[S] a) = MvPolynomial.C a :=
    (Algebra.TensorProduct.lift_tmul (Algebra.ofId T U) coord (fun _ _ => mul_comm _ _) 1 a).trans
      (by rw [map_one, one_mul]; rfl)
  refine AlgEquiv.ofAlgHom forward backward ?_ ?_
  · apply AlgHom.coe_ringHom_injective
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro p
      change forward (backward (p ⊗ₜ[S] (1 : A))) = p ⊗ₜ[S] (1 : A)
      rw [backward_left]
      exact forward.commutes p
    · apply RingHom.ext
      intro a
      change forward (backward ((1 : T) ⊗ₜ[S] a)) = right a
      rw [backward_right]
      exact MvPolynomial.eval₂Hom_C _ _ _
  · apply AlgHom.coe_ringHom_injective
    apply MvPolynomial.ringHom_ext
    · intro a
      change backward (eval (MvPolynomial.C a)) = MvPolynomial.C a
      rw [show eval (MvPolynomial.C a) = right a from MvPolynomial.eval₂Hom_C _ _ _]
      exact backward_right a
    · intro i
      change backward (eval (MvPolynomial.X i)) = MvPolynomial.X i
      rw [show eval (MvPolynomial.X i) = left (MvPolynomial.X i.val) from
        MvPolynomial.eval₂Hom_X' _ _ _]
      change backward (algebraMap T V (MvPolynomial.X i.val)) = MvPolynomial.X i
      rw [AlgHom.commutes]
      exact offsetMap_other offset y i
private abbrev ordinateField (k : Type) [Field k] := FractionRing (Polynomial k)
private abbrev OrdinateFibre {k A : Type} [Field k] [CommRing A] [Algebra k A] (y : A) :=
  letI := ordinateAlgebra (k := k) y
  ordinateField k ⊗[Polynomial k] A
private def extendFibre {S T U A K F : Type}
    [CommRing S] [CommRing T] [CommRing U] [CommRing A] [Field K] [Field F]
    [Algebra S A] [Algebra S T] [Algebra T U] [Algebra T F] [Algebra S F]
    [Algebra S K] [Algebra K F] [IsScalarTower S T F] [IsScalarTower S K F]
    (e : U ≃ₐ[T] T ⊗[S] A) : (F ⊗[T] U) ≃ₗ[F] F ⊗[K] (K ⊗[S] A) :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e).trans
    ((Algebra.TensorProduct.cancelBaseChange S T F F A).trans
      (Algebra.TensorProduct.cancelBaseChange S K F F A).symm)).toLinearEquiv
private theorem lengthBound_extend {K F M N : Type} [Field K] [Field F] [Algebra K F]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module F N]
    (e : N ≃ₗ[F] F ⊗[K] M) (d : ℕ) : LengthBound F N d ↔ LengthBound K M d := by
  have hr := e.finrank_eq.trans (Module.finrank_baseChange (R := F) (S := K) (M' := M))
  constructor
  · intro h
    let : Module.Finite F N := h.1
    let : Module.Finite F (F ⊗[K] M) := Module.Finite.equiv e
    exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat F, hr.symm.trans_le h.2⟩
  · intro h
    let : Module.Finite K M := h.1
    exact ⟨Module.Finite.equiv e.symm, hr.trans_le h.2⟩
private abbrev offsetToCut {k ι : Type} [Field k] (offset : ι) :
    Polynomial k →+* CutField k ι :=
  (algebraMap (MvPolynomial ι k) (CutField k ι)).comp (offsetPolynomial offset).toRingHom
private theorem offsetToCut_injective {k ι : Type} [Field k] (offset : ι) :
    Function.Injective (offsetToCut (k := k) offset) :=
  (IsFractionRing.injective (MvPolynomial ι k) (CutField k ι)).comp
    (transcendental_iff_injective.mp (MvPolynomial.transcendental_X k offset))
private abbrev offsetFractionAlgebra {k ι : Type} [Field k] (offset : ι) :
    Algebra (ordinateField k) (CutField k ι) :=
  (IsFractionRing.lift (K := ordinateField k) (g := offsetToCut offset)
    (offsetToCut_injective offset)).toAlgebra
private theorem lengthBound_ordinate {k ι A : Type} [Field k] [CommRing A] [Algebra k A]
    (offset : ι) (y : A) (d : ℕ) :
    LengthBound (CutField k ι) (GenericFibre k offset (MvPolynomial.C y)) d ↔
      LengthBound (ordinateField k) (OrdinateFibre (k := k) y) d := by
  let S := Polynomial k
  let T := MvPolynomial ι k
  let F := CutField k ι
  let K := ordinateField k
  let U := MvPolynomial (Other offset) A
  let sT : Algebra S T := offsetPolynomialAlgebra offset
  let sA : Algebra S A := ordinateAlgebra y
  let tU : Algebra T U := offsetAlgebra offset (MvPolynomial.C y)
  let sF : Algebra S F := (offsetToCut offset).toAlgebra
  let kF : Algebra K F := offsetFractionAlgebra offset
  let towerSTF := @IsScalarTower.of_algebraMap_eq S T F _ _ _ sT inferInstance sF fun _ => rfl
  let towerSKF := @IsScalarTower.of_algebraMap_eq S K F _ _ _ inferInstance kF sF fun p =>
    (IsFractionRing.lift_algebraMap (K := K) (offsetToCut_injective (k := k) offset) p).symm
  let e := @extendFibre S T U A K F _ _ _ _ _ _ sA sT tU inferInstance sF
    inferInstance kF towerSTF towerSKF (polynomialFibreEquiv (k := k) offset y)
  exact @lengthBound_extend K F (OrdinateFibre (k := k) y) (GenericFibre k offset (MvPolynomial.C y))
    _ _ kF _ _ _ _ e d
theorem proof : K1_14_2_4_1_4.c3 := by
  intro k ι ι' A _ _ _ offset offset' y d h
  exact (lengthBound_ordinate (k := k) offset' y d).mpr
    ((lengthBound_ordinate (k := k) offset y d).mp h)
end
end K1_14_2_4_1_4_3
end
section
set_option autoImplicit false
namespace K1_14_6_1
noncomputable section
open K1 K1_14 K1_14_6 MvPolynomial
open scoped Polynomial BigOperators
local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))
local notation "Pdy" => pderiv (R := FX) (none : Option (Fin 2))
abbrev flatten (f : Equation) : Biform := (optionEquivLeft FX (Fin 2)).symm f
abbrev separant (f : Biform) : Biform := Pdy f
def tangent (f P : Biform) : Biform :=
  separant f * partialX P - partialX f * Pdy P
def cleared (f : Biform) : ℕ → Biform
  | 0 => -partialX f
  | n + 1 => separant f * tangent f (cleared f n) -
      C ((2*n+1 : ℕ) : FX) * tangent f (separant f) * cleared f n
abbrev markEval (z : K) (S : K[X]) : Biform →+* FX := eval (rootPoint z S)
theorem eval_flatten (z : K) (S : K[X]) (f : Equation) :
    markEval z S (flatten f) = atMark f z S := by
  change eval (rootPoint z S) (flatten f) = _
  rw [show rootPoint z S = fun i => i.elim (atX S) ![seedEmbedding z, (seedEmbedding z)^p] by
    funext i
    cases i <;> rfl]
  rw [optionEquivLeft_elim_eval, AlgEquiv.apply_symm_apply, Polynomial.eval_map]
  rfl
theorem eval_separant (z : K) (S : K[X]) (f : Equation) :
    markEval z S (separant (flatten f)) = atMark f.derivative z S := by
  have h : separant (flatten f) = flatten f.derivative := by
    apply (optionEquivLeft FX (Fin 2)).injective
    rw [optionEquivLeft_pderiv_none, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [h, eval_flatten]
private theorem eval_tangent (f P : Biform) (z : K) (S : K[X])
    (hf : markEval z S f = 0) :
    markEval z S (tangent f P) = markEval z S (separant f) * Dx (markEval z S P) := by
  have h := Dx_eval z S f
  change Dx (markEval z S f) = _ at h
  rw [hf, map_zero] at h
  rw [Dx_eval, tangent, map_sub, map_mul, map_mul]
  linear_combination -markEval z S (Pdy P) * (Eq.symm h)
private theorem cleared_product_rule (m : ℕ) (a v : FX) :
    a * (a * Dx (a^m * v)) - (m : FX) * (a * Dx a) * (a^m * v) =
      a^(m+2) * Dx v := by
  cases m with
  | zero => simp [pow_two, mul_assoc]
  | succ m =>
    rw [Dx_mul, Dx_pow, Nat.succ_sub_one, pow_add a (m+1) 2, pow_succ' a m]
    ring
abbrev derivativeAt (S : K[X]) (n : ℕ) : FX :=
  atX (((Polynomial.derivative (R := K))^[n]) S)
theorem eval_cleared (f : Biform) (z : K) (S : K[X])
    (hf : markEval z S f = 0) (n : ℕ) :
    markEval z S (cleared f n) = markEval z S (separant f) ^ (2*n+1) * derivativeAt S (n+1) := by
  induction n with
  | zero =>
    have h := Dx_eval z S f
    change Dx (markEval z S f) = _ at h
    rw [hf, map_zero] at h
    simp only [cleared, map_neg, Nat.mul_zero, Nat.zero_add, pow_one]
    change -markEval z S (partialX f) = markEval z S (separant f) * atX S.derivative
    linear_combination -(Eq.symm h)
  | succ n ih =>
    rw [cleared, map_sub, map_mul, map_mul, map_mul, eval_C, eval_tangent _ _ _ _ hf,
      eval_tangent _ _ _ _ hf, ih, cleared_product_rule,
      show 2*(n+1)+1 = 2*n+1+2 by omega, Dx_atX]
    congr 1
    exact congrArg atX (Function.iterate_succ_apply' _ _ _).symm
end
end K1_14_6_1
end
section
set_option autoImplicit false
namespace K1_14_2_4_2
noncomputable section
open K1 K1_14 K1_14_2_4 K1_14_6_1 MvPolynomial
open scoped Polynomial
variable {n : ℕ}
abbrev markEval (t : Fin n → L) (S : K[X]) : SourceRing n →+* FX :=
  MvPolynomial.eval (markedPoint t S)
abbrev ordinate : SourceRing n := MvPolynomial.X none
abbrev separant (P : SourceRing n) : SourceRing n := pderiv none P
private theorem Dx_constant (a : L) : Dx (algebraMap L FX a) = 0 := by
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  obtain ⟨b, rfl⟩ := IsAlgClosed.exists_pow_nat_eq a (n := p) (by decide)
  rw [map_pow, Dx_pow, CharP.cast_eq_zero FX p, zero_mul, zero_mul]
def partialX : SourceRing n →+ SourceRing n :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom Dx).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
theorem coeff_partialX (P : SourceRing n) (m : Option (Fin n) →₀ ℕ) :
    (partialX P).coeff m = Dx (P.coeff m) := rfl
private theorem partialX_C (a : FX) : partialX (C a : SourceRing n) = C (Dx a) := by
  classical
  ext m
  by_cases h : (0 : Option (Fin n) →₀ ℕ) = m <;> simp [coeff_partialX, coeff_C, h]
private theorem partialX_mul_X (Q : SourceRing n) (i : Option (Fin n)) :
    partialX (Q * MvPolynomial.X i) = partialX Q * MvPolynomial.X i := by
  classical
  ext m
  simp only [coeff_partialX, coeff_mul_X']
  split <;> simp
private theorem Dx_eval (t : Fin n → L) (S : K[X]) (P : SourceRing n) :
    Dx (markEval t S P) = markEval t S (partialX P) +
      atX S.derivative * markEval t S (separant P) := by
  classical
  let ev := markEval t S
  change Dx (ev P) = ev (partialX P) + atX S.derivative * ev (pderiv none P)
  induction P using MvPolynomial.induction_on with
  | C a => simp [ev, partialX_C]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, mul_add]
    ring
  | mul_X P i hP =>
    have hi : Dx (markedPoint t S i) =
        atX S.derivative * ev (pderiv none (MvPolynomial.X i)) := by
      cases i with
      | none => simp [markedPoint, ev, Dx_atX]
      | some j => simp [markedPoint, ev, pderiv_X, Dx_constant]
    simp only [map_mul, Dx_mul, hP, partialX_mul_X, pderiv_mul, map_add]
    rw [show ev (MvPolynomial.X i) = markedPoint t S i by simp [ev], hi]
    ring
def tangent (f P : SourceRing n) : SourceRing n :=
  separant f * partialX P - partialX f * separant P
def cleared (f : SourceRing n) : ℕ → SourceRing n
  | 0 => -partialX f
  | i + 1 => separant f * tangent f (cleared f i) -
      C ((2*i+1 : ℕ) : FX) * tangent f (separant f) * cleared f i
private theorem eval_tangent (f P : SourceRing n) (t : Fin n → L) (S : K[X])
    (hf : markEval t S f = 0) :
    markEval t S (tangent f P) = markEval t S (separant f) * Dx (markEval t S P) := by
  have h := Dx_eval t S f
  rw [hf, map_zero] at h
  rw [Dx_eval, tangent, map_sub, map_mul, map_mul]
  linear_combination -markEval t S (separant P) * (Eq.symm h)
private theorem cleared_product_rule (m : ℕ) (a v : FX) :
    a * (a * Dx (a^m * v)) - (m : FX) * (a * Dx a) * (a^m * v) =
      a^(m+2) * Dx v := by
  cases m with
  | zero => simp [pow_two, mul_assoc]
  | succ m =>
    rw [Dx_mul, Dx_pow, Nat.succ_sub_one, pow_add a (m+1) 2, pow_succ' a m]
    ring
theorem eval_cleared (f : SourceRing n) (t : Fin n → L) (S : K[X])
    (hf : markEval t S f = 0) (i : ℕ) :
    markEval t S (cleared f i) = markEval t S (separant f) ^ (2*i+1) * derivativeAt S (i+1) := by
  induction i with
  | zero =>
    have h := Dx_eval t S f
    rw [hf, map_zero] at h
    simp only [cleared, map_neg, Nat.mul_zero, Nat.zero_add, pow_one]
    change -markEval t S (partialX f) = markEval t S (separant f) * atX S.derivative
    linear_combination -(Eq.symm h)
  | succ i ih =>
    rw [cleared, map_sub, map_mul, map_mul, map_mul, eval_C, eval_tangent _ _ _ _ hf,
      eval_tangent _ _ _ _ hf, ih, cleared_product_rule,
      show 2*(i+1)+1 = 2*i+1+2 by omega, Dx_atX]
    congr 1
    exact congrArg atX (Function.iterate_succ_apply' _ _ _).symm
end
end K1_14_2_4_2
end
section
namespace K1_14_2_4_1_4_2
open K1_14_2_4_1_4
open scoped TensorProduct nonZeroDivisors
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
private theorem units_in_finite_tensor {T F P : Type} [CommRing T] [IsDomain T]
    [Field F] [Algebra T F] [IsFractionRing T F] [CommRing P] [IsDomain P] [Algebra T P]
    [Module.Finite F (F ⊗[T] P)] (p : P) (hp : p ≠ 0) :
    IsUnit (1 ⊗ₜ[T] p : F ⊗[T] P) := by
  let W := F ⊗[T] P
  let : Algebra P W := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid P T⁰
  let : IsLocalization M W := IsLocalization.tensorRight F T⁰
  change IsUnit (algebraMap P W p)
  by_cases hinj : Function.Injective (algebraMap T P)
  · have hreg : M ≤ P⁰ := by
      rintro _ ⟨t, ht, rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr
        ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero ht))
    let : IsDomain W := IsLocalization.isDomain_of_le_nonZeroDivisors W hreg
    have hp' : algebraMap P W p ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective W hreg)).2 hp
    exact isUnit_iff_exists_inv.mpr
      ((IsField.of_isDomain_of_finite F W).mul_inv_cancel hp')
  · rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨t, ht, hne⟩ := hinj
    have hzero : (0 : P) ∈ M := ⟨t, mem_nonZeroDivisors_iff_ne_zero.mpr hne, ht⟩
    let : Unique W := IsLocalization.uniqueOfZeroMem hzero
    rw [Subsingleton.elim (algebraMap P W p) 1]
    exact isUnit_one
private theorem tensor_localization_le {T F P Q : Type} [CommRing T] [IsDomain T]
    [Field F] [Algebra T F] [IsFractionRing T F] [CommRing P] [IsDomain P] [Algebra T P]
    [CommRing Q] [Algebra T Q] [Algebra P Q] [IsScalarTower T P Q]
    (N : Submonoid P) [IsLocalization N Q] (hN : N ≤ P⁰) {d : ℕ}
    (h : LengthBound F (F ⊗[T] P) d) : LengthBound F (F ⊗[T] Q) d := by
  let : Module.Finite F (F ⊗[T] P) := h.1
  let f : (F ⊗[T] P) →ₐ[F] (F ⊗[T] Q) :=
    Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom T P Q)
  have hf (a : F) (p : P) : f (a ⊗ₜ[T] p) = a ⊗ₜ[T] algebraMap P Q p := rfl
  have hright (q : Q) : (1 ⊗ₜ[T] q : F ⊗[T] Q) ∈ f.range := by
    obtain ⟨⟨p, m⟩, hpm⟩ := IsLocalization.surj N q
    change q * algebraMap P Q (m : P) = algebraMap P Q p at hpm
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp
      (units_in_finite_tensor (T := T) (F := F) (m : P) (nonZeroDivisors.ne_zero (hN m.2)))
    refine ⟨(1 ⊗ₜ[T] p) * v, ?_⟩
    calc
      f ((1 ⊗ₜ[T] p) * v) = (1 ⊗ₜ[T] algebraMap P Q p) * f v := by rw [map_mul, hf]
      _ = ((1 ⊗ₜ[T] q) * f (1 ⊗ₜ[T] (m : P))) * f v := by
        rw [hf, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hpm]
      _ = 1 ⊗ₜ[T] q := by rw [mul_assoc, ← map_mul, hv, map_one, mul_one]
  have hsurj : Function.Surjective f := by
    intro z
    change z ∈ f.range
    induction z using TensorProduct.inductionOn with
    | tmul a q =>
      rw [← one_mul q, ← mul_one a, ← Algebra.TensorProduct.tmul_mul_tmul]
      refine f.range.mul_mem ⟨a ⊗ₜ[T] 1, ?_⟩ (hright q)
      change f (a ⊗ₜ[T] 1) = a ⊗ₜ[T] 1
      rw [hf, map_one]
    | add a b ha hb => exact f.range.add_mem ha hb
  exact ⟨Module.Finite.of_surjective f.toLinearMap hsurj,
    (LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hsurj).trans h.2⟩
private theorem offset_map_natural {k ι A B : Type} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (offset : ι) (u : MvPolynomial (Other offset) A)
    (f : A →ₐ[k] B) :
    (MvPolynomial.map f.toRingHom).comp (offsetMap (k := k) offset u) =
      offsetMap (k := k) offset (MvPolynomial.map f.toRingHom u) := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [offsetMap, RingHom.comp_apply]
  · intro i
    by_cases hi : i = offset
    · simp [offsetMap, hi]
    · simp [offsetMap, hi]
private theorem fraction_bound {k ι A B : Type} [Field k] [CommRing A] [IsDomain A]
    [Field B] [Algebra k A] [Algebra k B] (base : A →ₐ[k] B)
    (hfrac : let _ := base.toRingHom.toAlgebra; IsFractionRing A B)
    (offset : ι) (u : MvPolynomial (Other offset) A) {d : ℕ}
    (h : LengthBound (CutField k ι) (GenericFibre k offset u) d) :
    LengthBound (CutField k ι) (GenericFibre k offset (MvPolynomial.map base.toRingHom u)) d := by
  let : Algebra A B := base.toRingHom.toAlgebra
  let : IsFractionRing A B := hfrac
  let T := MvPolynomial ι k
  let P := MvPolynomial (Other offset) A
  let Q := MvPolynomial (Other offset) B
  let : Algebra T P := offsetAlgebra (k := k) offset u
  let : Algebra T Q := offsetAlgebra (k := k) offset (MvPolynomial.map base.toRingHom u)
  let : Algebra P Q := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower T P Q := IsScalarTower.of_algebraMap_eq fun t =>
    (RingHom.congr_fun (offset_map_natural offset u base) t).symm
  let N : Submonoid P := A⁰.map MvPolynomial.C
  let : IsLocalization N Q := MvPolynomial.isLocalization A⁰ B
  have hN : N ≤ P⁰ := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (MvPolynomial.C_injective (Other offset) A)).2
        (nonZeroDivisors.ne_zero ha))
  exact tensor_localization_le N hN h
private theorem lengthBound_of_copies {F U W : Type} [Field F]
    [AddCommGroup U] [AddCommGroup W] [Module F U] [Module F W] {n d : ℕ}
    (e : W ≃ₗ[F] (Fin n → U)) (h : LengthBound F U d) : LengthBound F W (n * d) := by
  let : Module.Finite F U := h.1
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using
    Nat.mul_le_mul_left n h.2
private theorem extension_bound {k ι B E : Type} [Field k] [Field B] [Field E]
    [Algebra k B] [Algebra k E] [Algebra B E] [Module.Finite B E]
    (cover : B →ₐ[k] E) (hcover : ∀ b, cover b = algebraMap B E b)
    (offset : ι) (v : MvPolynomial (Other offset) B) {d : ℕ}
    (h : LengthBound (CutField k ι) (GenericFibre k offset v) d) :
    LengthBound (CutField k ι) (GenericFibre k offset (MvPolynomial.map cover.toRingHom v))
      (Module.finrank B E * d) := by
  let F := CutField k ι
  let T := MvPolynomial ι k
  let P := MvPolynomial (Other offset) B
  let Q := MvPolynomial (Other offset) E
  let : Algebra T P := offsetAlgebra (k := k) offset v
  let : Algebra T Q := offsetAlgebra (k := k) offset (MvPolynomial.map cover.toRingHom v)
  let : Algebra P Q := MvPolynomial.algebraMvPolynomial
  have hmap : cover.toRingHom = algebraMap B E := RingHom.ext hcover
  let : IsScalarTower T P Q := IsScalarTower.of_algebraMap_eq fun t => by
    have heq := RingHom.congr_fun (offset_map_natural (k := k) offset v cover) t
    change offsetMap (k := k) offset (MvPolynomial.map cover.toRingHom v) t =
      MvPolynomial.map (algebraMap B E) (offsetMap (k := k) offset v t)
    rw [← hmap]
    exact heq.symm
  let n := Module.finrank B E
  let e₀ : Q ≃ₗ[P] (Fin n → P) :=
    (Algebra.IsPushout.equiv B P E Q).symm.toLinearEquiv.trans
      (Algebra.TensorProduct.equivPiOfFiniteBasis P (Module.finBasis B E))
  let e : (F ⊗[T] Q) ≃ₗ[F] (Fin n → F ⊗[T] P) :=
    ((e₀.restrictScalars T).baseChange T F _ _).trans (TensorProduct.piRight T F F _)
  exact lengthBound_of_copies e h
theorem proof : K1_14_2_4_1_4.c2 := by
  intro k ι A B E _ _ _ _ _ _ _ _ _ _ base cover hfrac hcover offset u d h
  have hb := fraction_bound base hfrac offset u h
  have he := extension_bound cover hcover offset _ hb
  rwa [MvPolynomial.map_map] at he
end
end K1_14_2_4_1_4_2
end
section
namespace K1_14_2_4_1_2_1
noncomputable section
open K1_14 K1_14_2_4_1
open MvPolynomial
local instance seedAlgebra (C₀ : ConstantSeeds) : Algebra L (ConstantSeedField C₀) :=
  (constToSeed C₀).toAlgebra
variable (C₀ : ConstantSeeds)
private theorem seed_aeval (f : ConstantSeeds) :
    aeval (seedCoordinate C₀) f =
      algebraMap (ConstantSeedRing C₀) (ConstantSeedField C₀)
        (Ideal.Quotient.mk (constantIdeal C₀) f) := by
  let q : ConstantSeeds →ₐ[L] ConstantSeedField C₀ :=
    ⟨(algebraMap (ConstantSeedRing C₀) (ConstantSeedField C₀)).comp
      (Ideal.Quotient.mk (constantIdeal C₀)), fun _ => rfl⟩
  have hq : aeval (seedCoordinate C₀) = q :=
    MvPolynomial.algHom_ext fun i => aeval_X (seedCoordinate C₀) i
  exact DFunLike.congr_fun hq f
private theorem seed_aeval_eq_zero (f : ConstantSeeds) :
    aeval (seedCoordinate C₀) f = 0 ↔ C₀ ∣ f := by
  rw [seed_aeval]
  rw [map_eq_zero_iff _ (IsFractionRing.injective (ConstantSeedRing C₀) (ConstantSeedField C₀)),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
variable [hC : Fact (Irreducible C₀)]
private theorem independent_coordinate {i j : Fin 2} (hij : i ≠ j) (hj : j ∈ C₀.vars) :
    AlgebraicIndependent L (fun _ : Unit => seedCoordinate C₀ i) := by
  classical
  refine algebraicIndependent_iff.mpr fun f hf => ?_
  let r : Unit → Fin 2 := fun _ => i
  have hz : aeval (seedCoordinate C₀) (rename r f) = 0 := by
    rw [aeval_rename]
    exact hf
  obtain ⟨g, hg⟩ := (seed_aeval_eq_zero C₀ _).mp hz
  by_contra hf0
  have hr : rename r f ≠ 0 := by
    intro h
    apply hf0
    apply rename_injective r (Function.injective_of_subsingleton _)
    simpa only [map_zero] using h
  have hg0 : g ≠ 0 := by
    intro h
    exact hr (by simp [hg, h])
  have hd : (rename r f).degreeOf j = 0 := by
    by_contra hd
    obtain ⟨a, _, ha⟩ := mem_vars_rename r f (mem_vars_iff_degreeOf_ne_zero.mpr hd)
    exact hij ha
  rw [hg, degreeOf_mul_eq hC.out.ne_zero hg0] at hd
  exact (mem_vars_iff_degreeOf_ne_zero.mp hj) (Nat.eq_zero_of_add_eq_zero_right hd)
private theorem algebraic_of_coordinates
    (A : Subalgebra L (ConstantSeedField C₀))
    (h : ∀ i, IsAlgebraic A (seedCoordinate C₀ i)) :
    Algebra.IsAlgebraic A (ConstantSeedField C₀) := by
  have hle : Algebra.adjoin L (Set.range (seedCoordinate C₀)) ≤
      (Subalgebra.algebraicClosure A (ConstantSeedField C₀)).restrictScalars L := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    exact h i
  have him (a : ConstantSeedRing C₀) :
      IsAlgebraic A (algebraMap (ConstantSeedRing C₀) (ConstantSeedField C₀) a) := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective (I := constantIdeal C₀) a
    apply hle
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨f, seed_aeval C₀ f⟩
  refine ⟨fun x => ?_⟩
  obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective (ConstantSeedRing C₀) x
  rw [div_eq_mul_inv]
  exact (him r).mul (him s).inv
theorem proof : K1_14_2_4_1_2.c1 := by
  classical
  intro C₀ hC
  have hvars : C₀.vars.Nonempty := by
    by_contra h
    have hconst := vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    have hcoeff : C₀.coeff 0 ≠ 0 := by
      intro he
      exact hC.out.ne_zero (by simpa only [he, map_zero] using hconst)
    exact hC.out.not_isUnit (hconst ▸ (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C)
  obtain ⟨j, hj⟩ := hvars
  let i := j.succAbove (0 : Fin 1)
  have hcover (k : Fin 2) : k = i ∨ k = j := by
    by_cases hk : k = j
    · exact Or.inr hk
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
      exact Or.inl (congrArg j.succAbove (Subsingleton.elim l 0))
  let x : Unit → ConstantSeedField C₀ := fun _ => seedCoordinate C₀ i
  have hi : AlgebraicIndependent L x := independent_coordinate C₀ (j.succAbove_ne 0) hj
  refine ⟨i, hi.isTranscendenceBasis_iff_isAlgebraic.mpr ?_⟩
  let A := Algebra.adjoin L (Set.range x)
  change Algebra.IsAlgebraic A (ConstantSeedField C₀)
  have hjalg : IsAlgebraic A (seedCoordinate C₀ j) := by
    by_contra h
    have hind := (hi.option_iff_transcendental (seedCoordinate C₀ j)).mpr h
    let e : Fin 2 ≃ Option Unit :=
      (finSuccEquiv' j).trans (Equiv.optionCongr (Equiv.ofUnique (Fin 1) Unit))
    have hindices : (fun o : Option Unit => o.elim (seedCoordinate C₀ j) x) ∘ e =
        seedCoordinate C₀ := by
      funext k
      rcases hcover k with rfl | rfl
      · simp [e, i, x, finSuccEquiv'_succAbove]
      · simp [e, finSuccEquiv'_at]
    have hpair : AlgebraicIndependent L (seedCoordinate C₀) :=
      hindices ▸ hind.comp e e.injective
    exact hC.out.ne_zero (hpair.eq_zero_of_aeval_eq_zero C₀
      ((seed_aeval_eq_zero C₀ C₀).mpr (dvd_refl C₀)))
  apply algebraic_of_coordinates C₀ A
  intro k
  rcases hcover k with rfl | rfl
  · exact isAlgebraic_algebraMap (⟨seedCoordinate C₀ i, Algebra.subset_adjoin ⟨(), rfl⟩⟩ : A)
  · exact hjalg
end
end K1_14_2_4_1_2_1
end
section
namespace K1_14_6
noncomputable section
open Finset K1 MvPolynomial
open scoped BigOperators Polynomial
private theorem card_le_sum_cover {α β : Type*} (U : Finset α) (Ps : Finset β)
    (part : β → Finset α) (h : ∀ γ ∈ U, ∃ P ∈ Ps, γ ∈ part P) :
    U.card ≤ ∑ P ∈ Ps, (part P).card := by
  classical
  exact (card_le_card fun γ hγ => mem_biUnion.mpr (h γ hγ)).trans card_biUnion_le
private def LinearCover.slice {T s d e b} (C : LinearCover T s d e b)
    (U : Finset K) (P : Ideal (LinearRing d e b)) : Finset K := by
  classical
  exact U.filter fun γ => C.point γ ∈ zeroLocus ClosedField P
private def LinearCover.section {T s d e b} (C : LinearCover T s d e b)
    (P : Ideal (LinearRing d e b)) (x a : K) : Finset (Ideal (LinearRing d e b)) :=
  (P ⊔ Ideal.span {C.cut x a}).minimalPrimesFinset
private theorem LinearCover.cut_data {T s d e b} (C : LinearCover T s d e b) {U : Finset K}
    (hU : U ⊆ T) {P : Ideal (LinearRing d e b)} (hP : P.IsPrime)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P)
    {x a : K} (hmiss : ∃ γ ∈ U, (s γ).eval x ≠ a) :
    (let V := U.filter fun γ => (s γ).eval x = a
     V.card ≤ ∑ Q ∈ C.section P x a, (C.slice V Q).card) ∧
    (∀ Q ∈ C.section P x a, Q.IsPrime ∧
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree) ∧
    (∑ Q ∈ C.section P x a, affineDegree Q) ≤ affineDegree P := by
  classical
  let prime := hP
  have hproper : C.cut x a ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hp
    exact hv ((C.cut_eval γ (hU hγ) x a).mp (hpoints γ hγ _ hp))
  refine ⟨?_, ?_, ?_⟩
  · dsimp only
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨hγU, hv⟩ := mem_filter.mp hγ
    have hp : C.point γ ∈ zeroLocus ClosedField (P ⊔ Ideal.span {C.cut x a}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγU, (C.cut_eval γ (hU hγU) x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  · intro Q hQ
    have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
    exact ⟨hmin.isPrime, principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin⟩
  · simpa only [LinearCover.section, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (C.cut_degree x a)
private theorem LinearCover.zero_dim_count {T s d e b} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (P : Ideal (LinearRing d e b))
    (hP : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) : (U.card : ℚ) ≤ affineDegree P := by
  classical
  let image := U.image C.point
  have hc : image.card = U.card := card_image_of_injOn (C.injective.mono hU)
  have hsub : (image : Set _) ⊆ zeroLocus ClosedField P := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hx
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := ClosedField) P hP
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hc] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree
private theorem curve_degree_nat {k σ : Type*} [Field k] [Finite σ]
    (P : Ideal (MvPolynomial σ k)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 1) :
    ∃ δ : ℕ, 0 < δ ∧ affineDegree P = (δ : ℚ) := by
  let H := affineHilbertPolynomial P
  have hlin : H = Polynomial.C (H.coeff 0) + Polynomial.C (H.coeff 1) * Polynomial.X := by
    have hH : H.natDegree < 2 := by change (affineHilbertPolynomial P).natDegree < 2; omega
    simpa [Finset.sum_range_succ] using H.as_sum_range_C_mul_X_pow' hH
  have evalH (u : ℚ) : H.eval u = H.coeff 0 + H.coeff 1 * u := by
    conv_lhs => rw [hlin]
    simp
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial P
  let m := affineHilbertFunction P (N + 1)
  let n := affineHilbertFunction P N
  have hdiff : affineDegree P = (m : ℚ) - (n : ℚ) := by
    rw [affineDegree, hdim, Nat.factorial_one, Nat.cast_one, one_mul, Polynomial.leadingCoeff, hdim]
    dsimp only [m, n]
    rw [← hN (N+1) (by omega), ← hN N le_rfl]
    change H.coeff 1 = H.eval ((N+1 : ℕ) : ℚ) - H.eval (N : ℚ)
    rw [evalH, evalH, Nat.cast_add, Nat.cast_one]
    ring
  have hmn : n < m := by
    have hpos := affineDegree_pos hP.ne_top
    rw [hdiff] at hpos
    exact_mod_cast sub_pos.mp hpos
  exact ⟨m-n, Nat.sub_pos_of_lt hmn, hdiff.trans (Nat.cast_sub hmn.le).symm⟩
end
end K1_14_6
end
section
namespace K1_14_6_2
noncomputable section
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators
variable {F : Type*} [Field F]
abbrev SourcePolynomial (F : Type*) [Field F] := Polynomial (MvPolynomial (Fin 2) F)
def flatten : SourcePolynomial F ≃ₐ[F] MvPolynomial (Option (Fin 2)) F :=
  (optionEquivLeft F (Fin 2)).symm
theorem eval_flatten (f : SourcePolynomial F) (x : Option (Fin 2) → F) :
    MvPolynomial.eval x (flatten f) =
      f.eval₂ (MvPolynomial.eval (x ∘ some)) (x none) := by
  have hx : (fun i => Option.elim i (x none) (x ∘ some)) = x := by
    funext i
    cases i <;> rfl
  rw [Polynomial.eval₂_eq_eval_map]
  have h := optionEquivLeft_elim_eval F (Fin 2) (x ∘ some) (x none) (flatten f)
  rw [hx, show optionEquivLeft F (Fin 2) (flatten f) = f from
    (optionEquivLeft F (Fin 2)).apply_symm_apply f] at h
  exact h
private theorem flatten_bound (f : SourcePolynomial F) {e b : ℕ}
    (he : f.natDegree ≤ e) (hb : ∀ i, (f.coeff i).totalDegree ≤ b) :
    flatten f ∈ restrictBidegree (Fin 2) F e b := by
  rw [mem_restrictBidegree]
  intro m hm
  have hc : (f.coeff (m none)).coeff m.some ≠ 0 := by
    have hh := optionEquivLeft_coeff_some_coeff_none F (Fin 2) m (flatten f)
    rw [show optionEquivLeft F (Fin 2) (flatten f) = f from
      (optionEquivLeft F (Fin 2)).apply_symm_apply f] at hh
    rw [hh]
    exact MvPolynomial.mem_support_iff.mp hm
  exact ⟨(Polynomial.le_natDegree_of_ne_zero fun h => hc (by simp [h])).trans he,
    (le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)).trans (hb _)⟩
private theorem factor_span_minimal {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {f g : R}
    (hf : f ≠ 0) (hg : g ∈ factors f) :
    Ideal.span {g} ∈ (Ideal.span {f}).minimalPrimes := by
  have hp := prime_of_factor g hg
  refine ⟨⟨Ideal.isPrime_span_singleton_of_prime hp, (Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.mem_span_singleton.mpr (dvd_of_mem_factors hg))⟩, ?_⟩
  intro Q hQ hle
  have hfQ : f ∈ Q := hQ.2 (Ideal.subset_span (Set.mem_singleton f))
  have hprod : (factors f).prod ∈ Q :=
    ((Ideal.span_singleton_le_iff_mem _).mpr hfQ)
      (Ideal.mem_span_singleton.mpr (factors_prod hf).dvd')
  obtain ⟨q, hq, hqQ⟩ := (hQ.1.multiset_prod_mem_iff_exists_mem _).mp hprod
  have hdiv : g ∣ q := Ideal.mem_span_singleton.mp (hle hqQ)
  have hassoc := hp.associated_of_dvd (prime_of_factor q hq) hdiv
  rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc]
  exact (Ideal.span_singleton_le_iff_mem _).mpr hqQ
private theorem comap_span_flatten (f : SourcePolynomial F) :
    (Ideal.span {f}).comap (optionEquivLeft F (Fin 2)).toRingHom =
      Ideal.span {flatten f} := by
  ext g
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  change f ∣ optionEquivLeft F (Fin 2) g ↔ flatten f ∣ g
  constructor
  · intro h
    simpa only [AlgEquiv.symm_apply_apply, flatten] using
      map_dvd (optionEquivLeft F (Fin 2)).symm h
  · intro h
    simpa only [AlgEquiv.apply_symm_apply, flatten] using
      map_dvd (optionEquivLeft F (Fin 2)) h
private theorem positiveDegrees_card_le {R : Type*} [Semiring R]
    (fs : Multiset R[X]) :
    (fs.filter (fun g => 0 < g.natDegree)).card ≤ (fs.map Polynomial.natDegree).sum := by
  induction fs using Multiset.induction_on with
  | empty => simp
  | cons g fs ih =>
    by_cases hg : 0 < g.natDegree <;> simp [hg] <;> omega
private theorem positiveFactors_card_le [DecidableEq (SourcePolynomial F)]
    (f : SourcePolynomial F) (hf : f ≠ 0) :
    ((factors f).filter fun g => 0 < g.natDegree).toFinset.card ≤ f.natDegree := by
  obtain ⟨u, hu⟩ := factors_prod hf
  have hnz : (0 : SourcePolynomial F) ∉ factors f :=
    fun hz => (prime_of_factor 0 hz).ne_zero rfl
  have hdeg : ((factors f).prod).natDegree = f.natDegree := calc
    _ = ((factors f).prod * (u : SourcePolynomial F)).natDegree := by
      rw [Polynomial.natDegree_mul (Multiset.prod_ne_zero hnz) (Units.ne_zero u),
        Polynomial.natDegree_coe_units, add_zero]
    _ = _ := congrArg Polynomial.natDegree hu
  exact (Multiset.toFinset_card_le _).trans <| (positiveDegrees_card_le _).trans_eq <|
    (Polynomial.natDegree_multiset_prod _ hnz).symm.trans hdeg
private theorem positive_factor_at_root {R E : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field E]
    (f : R[X]) (hf : f ≠ 0) (ev : R →+* E) (v : E)
    (hroot : f.eval₂ ev v = 0) (hreg : f.derivative.eval₂ ev v ≠ 0) :
    ∃ g ∈ factors f, 0 < g.natDegree ∧ g.eval₂ ev v = 0 := by
  let ev' := Polynomial.eval₂RingHom ev v
  obtain ⟨u, hu⟩ := factors_prod hf
  change ev' f = 0 at hroot
  rw [← hu, map_mul, mul_eq_zero] at hroot
  have hz := hroot.resolve_right (Units.ne_zero (Units.map ev'.toMonoidHom u))
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at hz
  obtain ⟨g, hg, hgz⟩ := Multiset.mem_map.mp hz
  change g.eval₂ ev v = 0 at hgz
  refine ⟨g, hg, Nat.pos_of_ne_zero ?_, hgz⟩
  intro hd
  obtain ⟨q, hq⟩ := dvd_of_mem_factors hg
  have hder : g.derivative = 0 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.derivative_C]
  exact hreg (by rw [hq, Polynomial.derivative_mul]; simp [hder, hgz])
theorem regularComponents {a c e b : ℕ} (ha : 0 < a) (hc : 0 < c)
    (f : SourcePolynomial F) (hf : f ≠ 0) (he : f.natDegree ≤ e)
    (hb : ∀ i, (f.coeff i).totalDegree ≤ b) :
    ∃ Q : Finset (Ideal (MvPolynomial (bidegreeExponents (Fin 2) a c) F)),
      (∀ P ∈ Q, P.IsPrime ∧ (affineHilbertPolynomial P).natDegree = 2) ∧
      Q.card ≤ e ∧
      (∑ P ∈ Q, affineDegree P) ≤ (e * c ^ 2 + 2 * b * a * c : ℕ) ∧
      ∀ x : Option (Fin 2) → F, f.eval₂ (MvPolynomial.eval (x ∘ some)) (x none) = 0 →
        f.derivative.eval₂ (MvPolynomial.eval (x ∘ some)) (x none) ≠ 0 →
        ∃ P ∈ Q, monomialPoint (bidegreeExponents (Fin 2) a c) x ∈ zeroLocus F P := by
  classical
  let phi := bidegreeMap (Fin 2) F a c
  let fs := ((factors f).filter (fun g => 0 < g.natDegree)).toFinset
  let component := fun g : SourcePolynomial F => (Ideal.span {flatten g}).comap phi
  let Q := fs.image component
  have hminimal {g : SourcePolynomial F} (hg : g ∈ fs) :
      component g ∈ ((Ideal.span {flatten f}).comap phi).minimalPrimes := by
    have hfac := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hg)).1
    have h := Ideal.minimalPrimes_comap_of_surjective
      (f := (optionEquivLeft F (Fin 2)).toRingHom)
      (optionEquivLeft F (Fin 2)).surjective (factor_span_minimal hf hfac)
    rw [comap_span_flatten, comap_span_flatten] at h
    exact Ideal.minimalPrimes_comap_of_surjective (bidegreeMap_surjective ha hc) h
  refine ⟨Q, ?_, Finset.card_image_le.trans ((positiveFactors_card_le f hf).trans he), ?_, ?_⟩
  · intro P hP
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hP
    have hp := (hminimal hg).isPrime
    have hg0 := (prime_of_factor g
      (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hg)).1).ne_zero
    have hflat : flatten g ≠ 0 := by
      simpa only [map_zero] using (flatten : SourcePolynomial F ≃ₐ[F] _).injective.ne hg0
    have hproper : Ideal.span {flatten g} ≠ ⊤ := by
      intro ht
      exact hp.ne_top (by simp [component, ht])
    exact ⟨hp, by
      simpa [component, phi, Nat.card_eq_fintype_card] using
        natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton ha hc hflat hproper⟩
  · have hsub : Q ⊆ ((Ideal.span {flatten f}).comap phi).minimalPrimesFinset := by
      intro P hP
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hP
      exact Ideal.mem_minimalPrimesFinset.mpr (hminimal hg)
    have hflat : flatten f ≠ 0 := by
      simpa only [map_zero] using (flatten : SourcePolynomial F ≃ₐ[F] _).injective.ne hf
    have hbound := affineDegree_comap_bidegreeMap_span_singleton_le ha hc hflat
      (flatten_bound f he hb)
    have hsum := sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le ha hc
      (flatten f)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)).trans
      (hsum.trans (by simpa [phi, Nat.card_eq_fintype_card] using hbound))
  · intro x hroot hreg
    obtain ⟨g, hg, hd, hz⟩ := positive_factor_at_root f hf _ _ hroot hreg
    refine ⟨component g, Finset.mem_image.mpr
      ⟨g, Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hg, hd⟩), rfl⟩, ?_⟩
    change monomialPoint _ x ∈ zeroLocus F ((Ideal.span {flatten g}).comap phi)
    rw [show phi = monomialMap F (bidegreeExponents (Fin 2) a c) from
      bidegreeMap_eq_monomialMap a c,
      monomialPoint_mem_zeroLocus_comap_iff (fun i => single_mem_bidegreeExponents ha hc i),
      mem_zeroLocus_iff_le_ker_aeval, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    change MvPolynomial.eval x (flatten g) = 0
    rwa [eval_flatten]
end
end K1_14_6_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace K1_14_2_4_3_2_1
noncomputable section
open K1_14 K1_14_2_4 K1_14_2_4_3_2 MvPolynomial
variable {n : ℕ} (J : Ideal (SourceRing n))
local instance : CommRing (rees J) :=
  Subalgebra.toCommRing (R := FX) (A := AddMonoidAlgebra (Affine J) (ℕ × ℕ)) (rees J)
private theorem piece_eq_zero (d : ℕ × ℕ) {x : Affine J} (hx : x ∈ filteredBox J d)
    (h : x = 0) : piece d x hx = 0 := by
  subst x
  apply Subtype.ext
  change AddMonoidAlgebra.single d 0 = 0
  exact AddMonoidAlgebra.single_zero _
private def liftBox (d : ℕ × ℕ) (p : CoeffPoly J) (hp : p ∈ polynomialBox J d) :
    MvPolynomial (Option (Fin n)) (rees J) :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset p.support
    (fun m => piece d (p.coeff m) (hp m)) fun m hm => by
      by_contra h
      have hz := MvPolynomial.notMem_support_iff.mp h
      exact hm (piece_eq_zero J d (hp m) hz))
private theorem coeff_liftBox (d : ℕ × ℕ) (p : CoeffPoly J) (hp : p ∈ polynomialBox J d)
    (m : Option (Fin n) →₀ ℕ) :
    (liftBox J d p hp).coeff m = piece d (p.coeff m) (hp m) := rfl
private def homogeneousCut : MvPolynomial (Option (Fin n)) (rees J) :=
  C (yGen J) - C (U J) * MvPolynomial.X none
private theorem val_coeff_cut_mul_lift (d : ℕ × ℕ) (p : CoeffPoly J)
    (hp : p ∈ polynomialBox J d) (m : Option (Fin n) →₀ ℕ) :
    (rees J).val ((homogeneousCut J * liftBox J d p hp).coeff m) =
      AddMonoidAlgebra.single ((1, 0) + d) ((polynomialCut J * p).coeff m) := by
  classical
  have hy : (rees J).val (yGen J) = AddMonoidAlgebra.single (1, 0) (ordinate J) := rfl
  have hu : (rees J).val (U J) = AddMonoidAlgebra.single (1, 0) 1 := rfl
  have hc : polynomialCut J * p = C (ordinate J) * p - MvPolynomial.X none * p := by
    unfold polynomialCut
    exact sub_mul (C (ordinate J)) (MvPolynomial.X none) p
  rw [homogeneousCut, sub_mul, mul_assoc, hc]
  simp only [coeff_sub, coeff_C_mul, coeff_X_mul', coeff_liftBox, map_sub, map_mul, val_piece, hy, hu]
  split_ifs <;> simp only [val_piece, map_zero, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_sub, one_mul, mul_zero, sub_zero]
private theorem map_lift_mem_pow {R : Type*} [CommRing R] (q : rees J →+* R)
    (d : ℕ × ℕ) (N : ℕ) (hN : N ≤ d.1) (p : CoeffPoly J)
    (hp : p ∈ polynomialBox J d) :
    MvPolynomial.map q (liftBox J d p hp) ∈
      (Ideal.span {C (q (yGen J)), C (q (U J))} :
        Ideal (MvPolynomial (Option (Fin n)) R)) ^ N := by
  classical
  let f : rees J →+* MvPolynomial (Option (Fin n)) R := C.comp q
  have hI : (degreeIdeal J).map f =
      (Ideal.span {C (q (yGen J)), C (q (U J))} :
        Ideal (MvPolynomial (Option (Fin n)) R)) := by
    rw [degreeIdeal, Ideal.map_span, Set.image_pair, Set.pair_comm]
    rfl
  rw [← hI, ← Ideal.map_pow f (degreeIdeal J) N,
    ← support_sum_monomial_coeff (MvPolynomial.map q (liftBox J d p hp))]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [coeff_map, coeff_liftBox, monomial_eq, mul_comm]
  apply Ideal.mul_mem_left
  exact Ideal.mem_map_of_mem f
    (Ideal.pow_le_pow_right hN (piece_mem_pow J d.1 d.2 (hp m)))
private theorem eventual_lower_box (e : ℕ × ℕ) :
    ∃ N : ℕ, ∀ d : ℕ × ℕ, N ≤ (e + d).1 →
      ∀ p ∈ polynomialBox J (e + d),
        polynomialCut J * p ∈ polynomialBox J ((1, 0) + d) →
        p ∈ polynomialBox J d := by
  classical
  let a : rees J := piece e 1 (box_one J e)
  let I : Ideal (rees J) := Ideal.span {a}
  let q := Ideal.Quotient.mk I
  obtain ⟨N, hN⟩ := high_pencil (σ := Fin n) (q (yGen J)) (q (U J))
  refine ⟨N, fun d hd p hp hpq => ?_⟩
  let r := liftBox J (e + d) p hp
  have hkill : MvPolynomial.map q (homogeneousCut J * r) = 0 := by
    apply MvPolynomial.eq_zero_iff.mpr
    intro m
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    have hm : (homogeneousCut J * r).coeff m =
        a * piece ((1, 0) + d) ((polynomialCut J * p).coeff m) (hpq m) := by
      apply Subtype.ext
      change (rees J).val ((homogeneousCut J * r).coeff m) =
        (rees J).val (a * piece ((1, 0) + d) ((polynomialCut J * p).coeff m) (hpq m))
      rw [val_coeff_cut_mul_lift, map_mul, show (rees J).val a = AddMonoidAlgebra.single e 1
        from rfl, val_piece, AddMonoidAlgebra.single_mul_single, one_mul, add_left_comm e]
    rw [hm, mul_comm]
    exact I.mul_mem_left _ (Ideal.subset_span (Set.mem_singleton a))
  have hz := hN (MvPolynomial.map q r) (map_lift_mem_pow J q _ N hd p hp) (by
    simpa only [homogeneousCut, map_mul, map_sub, map_C, map_X] using hkill)
  intro m
  have hm := MvPolynomial.eq_zero_iff.mp hz m
  rw [coeff_map] at hm
  exact (piece_mem_span_padding J e d (hp m)).mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [r, coeff_liftBox] using hm))
theorem proof : K1_14_2_4_3_2.c1 := by
  intro n J _ _
  obtain ⟨Nu, hu⟩ := eventual_lower_box J (1, 0)
  obtain ⟨Nv, hv⟩ := eventual_lower_box J (0, 1)
  refine ⟨max Nu Nv, fun u v hN _ => ⟨?_, ?_⟩⟩
  · have hdeg : Nu ≤ ((1, 0) + (u, v) : ℕ × ℕ).1 := by
      have h := (le_max_left Nu Nv).trans hN
      change Nu ≤ 1 + u
      omega
    simpa only [Prod.mk_add_mk, Nat.zero_add, Nat.add_comm 1 u] using hu (u, v) hdeg
  · have hdeg : Nv ≤ ((0, 1) + (u, v) : ℕ × ℕ).1 := by
      simpa only [Prod.mk_add_mk, Nat.zero_add] using (le_max_right Nu Nv).trans hN
    simpa only [Prod.mk_add_mk, Nat.zero_add, Nat.add_comm 1 u, Nat.add_comm 1 v] using
      hv (u, v) hdeg
end
end K1_14_2_4_3_2_1
end
section
set_option autoImplicit false
namespace K1_14_2_4_2
noncomputable section
open K1 K1_14 K1_14_2_4 MvPolynomial
open scoped Polynomial BigOperators
variable {n : ℕ}
private abbrev incl := algebraMap L[X] FX
abbrev center : FX := incl Polynomial.X
private def atCenter (n : ℕ) : Polynomial (ParameterRing n) →+* MvPolynomial (Fin n) FX :=
  Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX)) (C center)
abbrev flatten (f : FamilyEquation n) : SourceRing n :=
  (optionEquivLeft FX (Fin n)).symm (f.map (atCenter n))
private theorem eval_atCenter (t : Fin n → L) :
    (MvPolynomial.eval (fun j => algebraMap L FX (t j))).comp (atCenter n) =
      incl.comp (Polynomial.mapRingHom (MvPolynomial.eval t)) := by
  apply Polynomial.ringHom_ext
  · intro q
    change MvPolynomial.eval (fun j => algebraMap L FX (t j))
      ((Polynomial.C q).eval₂ (MvPolynomial.map (algebraMap L FX)) (C center)) =
        incl ((Polynomial.C q).map (MvPolynomial.eval t))
    rw [Polynomial.eval₂_C, Polynomial.map_C, MvPolynomial.eval_map]
    exact (MvPolynomial.eval₂_comp (algebraMap L FX) t q).symm.trans
      (IsScalarTower.algebraMap_apply L L[X] FX _)
  · change MvPolynomial.eval (fun j => algebraMap L FX (t j))
      (Polynomial.X.eval₂ (MvPolynomial.map (algebraMap L FX)) (C center)) =
        incl (Polynomial.X.map (MvPolynomial.eval t))
    rw [Polynomial.eval₂_X, eval_C, Polynomial.map_X]
theorem eval_flatten (t : Fin n → L) (S : K[X]) (f : FamilyEquation n) :
    markEval t S (flatten f) = incl ((specialize f t).eval (liftPoly S)) := by
  change MvPolynomial.eval (markedPoint t S) (flatten f) = _
  rw [show markedPoint t S = fun i => i.elim (atX S) (fun j => algebraMap L FX (t j)) by
    funext i
    cases i <;> rfl]
  rw [optionEquivLeft_elim_eval, AlgEquiv.apply_symm_apply, Polynomial.eval_map,
    Polynomial.eval₂_map, eval_atCenter, specialize, Polynomial.eval_map, Polynomial.hom_eval₂]
  rfl
theorem eval_separant (t : Fin n → L) (S : K[X]) (f : FamilyEquation n) :
    markEval t S (separant (flatten f)) =
      incl ((specialize f t).derivative.eval (liftPoly S)) := by
  have h : separant (flatten f) = flatten f.derivative := by
    apply (optionEquivLeft FX (Fin n)).injective
    rw [optionEquivLeft_pderiv_none, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
      Polynomial.derivative_map]
  rw [h, eval_flatten, specialize, specialize, Polynomial.derivative_map]
abbrev box (n a b : ℕ) := restrictBidegree (Fin n) FX a b
private theorem atCenter_degree (P : Polynomial (ParameterRing n))
    (hP : ∀ j, (P.coeff j).totalDegree ≤ 1) : (atCenter n P).totalDegree ≤ 1 := by
  change (P.eval₂ (MvPolynomial.map (algebraMap L FX)) (C center)).totalDegree ≤ 1
  rw [Polynomial.eval₂_eq_sum_range]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [← map_pow (C : FX →+* MvPolynomial (Fin n) FX), totalDegree_C, add_zero]
  refine le_trans ?_ (hP j)
  exact Finset.sup_mono (support_map_subset (algebraMap L FX) (P.coeff j))
theorem flatten_bound {f : FamilyEquation n} {g : ℕ} (hf : FamilyDegree f g) :
    flatten f ∈ box n g 1 := by
  rw [mem_restrictBidegree]
  intro m hm
  have hc : m.some ∈ ((f.map (atCenter n)).coeff (m none)).support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    have h := optionEquivLeft_coeff_coeff FX (flatten f) (m none) m.some
    simp only [AlgEquiv.apply_symm_apply, Finsupp.optionElim_some] at h
    exact h.trans_ne hm
  have hc' : (f.map (atCenter n)).coeff (m none) ≠ 0 := by
    intro h
    simp [h] at hc
  refine ⟨(Polynomial.le_natDegree_of_ne_zero hc').trans (Polynomial.natDegree_map_le.trans hf.1),
    (le_totalDegree hc).trans ?_⟩
  rw [Polynomial.coeff_map]
  exact atCenter_degree _ (hf.2 (m none))
private theorem partialX_bound {P : SourceRing n} {a b : ℕ}
    (hP : P ∈ box n a b) : partialX P ∈ box n a b := by
  rw [mem_restrictBidegree] at hP ⊢
  intro m hm
  apply hP m
  contrapose! hm
  rw [notMem_support_iff] at hm ⊢
  rw [coeff_partialX, hm, map_zero]
theorem separant_bound {P : SourceRing n} {a b : ℕ}
    (hP : P ∈ box n a b) : separant P ∈ box n (a-1) b := by
  rw [mem_restrictBidegree_iff_weightedTotalDegree_le] at hP ⊢
  exact ⟨(weightedTotalDegree_pderiv_le_sub _ _ _).trans (Nat.sub_le_sub_right hP.1 1),
    (weightedTotalDegree_pderiv_le _ _ _).trans hP.2⟩
private theorem tangent_bound {f P : SourceRing n} {g b a c : ℕ}
    (hf : f ∈ box n g b) (hP : P ∈ box n a c) (hg : 0 < g) :
    tangent f P ∈ box n (a+(g-1)) (c+b) := by
  have h1 := mul_mem_restrictBidegree (separant_bound hf) (partialX_bound hP)
  unfold tangent
  apply (box _ _ _).sub_mem
  · simpa only [Nat.add_comm] using h1
  · by_cases ha : a = 0
    · have hzero : P.degreeOf none = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply degreeOf_le_iff.mpr
        intro m hm
        simpa only [ha] using ((mem_restrictBidegree.mp hP) m hm).1
      rw [show separant P = 0 from pderiv_eq_zero_of_degreeOf_eq_zero hzero, mul_zero]
      exact (box _ _ _).zero_mem
    · have h2 := mul_mem_restrictBidegree (partialX_bound hf) (separant_bound hP)
      rwa [show g+(a-1) = a+(g-1) by omega, Nat.add_comm b c] at h2
theorem cleared_bound {f : SourceRing n} {g b : ℕ} (hg : 0 < g)
    (hf : f ∈ box n g b) (i : ℕ) :
    cleared f i ∈ box n (1+(2*i+1)*(g-1)) ((2*i+1)*b) := by
  induction i with
  | zero =>
    have h := (box _ _ _).neg_mem (partialX_bound hf)
    simpa only [cleared, Nat.mul_zero, Nat.zero_add, Nat.one_mul, show 1+(g-1) = g by omega]
      using h
  | succ i ih =>
    have ha := separant_bound hf
    have h1 := mul_mem_restrictBidegree ha (tangent_bound hf ih hg)
    have h2 := mul_mem_restrictBidegree (tangent_bound hf ha hg) ih
    have h2' := (box _ _ _).smul_mem (((2*i+1 : ℕ) : FX)) h2
    rw [cleared]
    apply (box _ _ _).sub_mem
    · convert h1 using 2 <;> ring
    · rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul]
      convert h2' using 2 <;> ring
theorem box_pow {P : SourceRing n} {a b : ℕ} (hP : P ∈ box n a b) (i : ℕ) :
    P ^ i ∈ box n (i*a) (i*b) := by
  induction i with
  | zero =>
    simp only [pow_zero, Nat.zero_mul, mem_restrictBidegree]
    simp [support_one]
  | succ i ih =>
    simpa only [pow_succ, Nat.succ_mul] using mul_mem_restrictBidegree ih hP
theorem ordinate_mem : ordinate (n := n) ∈ box n 1 0 := by
  classical
  rw [mem_restrictBidegree, MvPolynomial.support_X]
  intro m hm
  rw [Finset.mem_singleton] at hm
  subst m
  simp
end
end K1_14_2_4_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_1
noncomputable section
open K1_14 K1_14_2_4 K1_14_2_4_3 MvPolynomial
def c1 : Prop :=
  ∀ (n : ℕ) (k : Type) [Field k] (I : Ideal (MvPolynomial (Option (Fin n)) k)),
    (∀ (u v : ℕ) (x : MvPolynomial (Option (Fin n)) k ⧸ I),
      x ∈ quotientBidegreeLE I u v ↔
        ∃ p : HomRing n k, Bihomogeneous p (u, v) ∧ dehomClass I p = x) ∧
    (∀ (side : Bool), ParamGraded (boundaryIdeal I side) ∧
      ∀ (u v : ℕ) (p : HomRing n k),
        Bihomogeneous p ((u, v) + unitDegree side) →
          (p ∈ boundaryIdeal I side ↔ dehomClass I p ∈ quotientBidegreeLE I u v))
def c2 : Prop :=
  ∀ (n : ℕ) (I : Ideal (HomRing n FX))
    (p : HomRing n (SliceField n)), homCut n * p ∈ extendHomIdeal I →
    ∀ i : Option (Fin n), ∃ e : ℕ, MvPolynomial.X (paramVar i) ^ e * p ∈ extendHomIdeal I
private theorem dehom_homCut (n : ℕ) : dehom (homCut n) = parameterCut n := by
  simp [homCut, parameterCut, dehom, paramVar, pad]
private theorem bihomogeneous_homCut (n : ℕ) : Bihomogeneous (homCut n) (0, 1) := by
  unfold homCut
  apply IsWeightedHomogeneous.sub
  · apply IsWeightedHomogeneous.sum
    intro j _
    exact (isWeightedHomogeneous_X (SliceField n) (biWeight n) (paramVar (some j))).C_mul _
  · exact (isWeightedHomogeneous_X (SliceField n) (biWeight n) (paramVar none)).C_mul _
private theorem param_of_bihomogeneous {n : ℕ} {k : Type} [Field k]
    {p : HomRing n k} {a b : ℕ} (hp : Bihomogeneous p (a, b)) :
    p.IsWeightedHomogeneous (paramWeight n) b := by
  intro d hd
  have hweight : Finsupp.weight (paramWeight n) d = (Finsupp.weight (biWeight n) d).2 := by
    simp only [Finsupp.weight_apply, Finsupp.sum, Prod.snd_sum, Prod.smul_snd, paramWeight]
  exact hweight.trans (congrArg Prod.snd (hp hd))
private theorem boundary_extend {n : ℕ} (J : Ideal (SourceRing n)) (side : Bool) :
    boundaryIdeal (extendedIdeal J) side = extendHomIdeal (boundaryIdeal J side) := by
  simp only [boundaryIdeal, extendHomIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    MvPolynomial.map_X, homIdeal_extend J]
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_4_3.c1 := by
  intro n J _ _
  obtain ⟨hlift, hboundary⟩ := h1 n (SliceField n) (extendedIdeal J)
  have hlarge (side : Bool) :
      ∃ N : ℕ, ∀ (v : ℕ) (p : HomRing n (SliceField n)), N ≤ v →
        p.IsWeightedHomogeneous (paramWeight n) v →
        homCut n * p ∈ boundaryIdeal (extendedIdeal J) side →
        p ∈ boundaryIdeal (extendedIdeal J) side := by
    apply large_parameter_degree _ (homCut n) (hboundary side).1
    intro p hp i
    rw [boundary_extend J side] at hp ⊢
    exact h2 n (boundaryIdeal J side) p hp i
  obtain ⟨Nu, hNu⟩ := hlarge false
  obtain ⟨Nv, hNv⟩ := hlarge true
  have step (side : Bool) (u v : ℕ) (x : ExtendedRing J)
      (hx : x ∈ box J ((u, v) + unitDegree side).1 ((u, v) + unitDegree side).2)
      (hqx : cutClass J (parameterCut n) * x ∈ box J u (v + 1))
      (hreg : ∀ (p : HomRing n (SliceField n)),
        p.IsWeightedHomogeneous (paramWeight n) ((u, v) + unitDegree side).2 →
        homCut n * p ∈ boundaryIdeal (extendedIdeal J) side →
        p ∈ boundaryIdeal (extendedIdeal J) side) :
      x ∈ box J u v := by
    obtain ⟨p, hp, he⟩ := (hlift _ _ _).mp hx
    have hprod : Bihomogeneous (homCut n * p) ((u, v + 1) + unitDegree side) := by
      have ht := (bihomogeneous_homCut n).mul hp
      convert ht using 1
      cases side <;> simp [unitDegree, Nat.add_comm, Nat.add_left_comm]
    have hq : dehomClass (extendedIdeal J) (homCut n) = cutClass J (parameterCut n) := by
      change Ideal.Quotient.mk (extendedIdeal J) (dehom (homCut n)) = _
      rw [dehom_homCut]
    have hmem : homCut n * p ∈ boundaryIdeal (extendedIdeal J) side := by
      apply ((hboundary side).2 u (v + 1) _ hprod).mpr
      simpa only [map_mul, hq, he] using hqx
    rw [← he]
    exact ((hboundary side).2 u v p hp).mp (hreg p (param_of_bihomogeneous hp) hmem)
  refine ⟨max Nu Nv, ?_⟩
  intro u v _ hv
  have hu' : Nu ≤ v := (le_max_left _ _).trans hv
  have hv' : Nv ≤ v + 1 := (le_max_right _ _).trans (hv.trans (Nat.le_succ _))
  constructor
  · intro x hx hqx
    exact step false u v x hx hqx (fun p => hNu v p hu')
  · intro x hx hqx
    exact step true u v x hx hqx (fun p => hNv (v + 1) p hv')
end
end K1_14_2_4_3_1
end
section
set_option autoImplicit false
namespace K1_14_6_1
noncomputable section
open K1_14 K1_14_6 MvPolynomial
local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))
abbrev box (a b : ℕ) := restrictBidegree (Fin 2) FX a b
private theorem flatten_bound {f : Equation} {e b : ℕ}
    (he : f.natDegree ≤ e) (hb : SeedBound f b) : flatten f ∈ box e b := by
  rw [mem_restrictBidegree]
  intro m hm
  have hc : m.some ∈ (f.coeff (m none)).support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    have h := optionEquivLeft_coeff_coeff FX (flatten f) (m none) m.some
    simp only [AlgEquiv.apply_symm_apply, Finsupp.optionElim_some] at h
    exact h.trans_ne hm
  have hc' : f.coeff (m none) ≠ 0 := by
    intro h
    simp [h] at hc
  exact ⟨(Polynomial.le_natDegree_of_ne_zero hc').trans he,
    (le_totalDegree hc).trans (hb (m none))⟩
private theorem partialX_bound {P : Biform} {a b : ℕ}
    (hP : P ∈ box a b) : partialX P ∈ box a b := by
  rw [mem_restrictBidegree] at hP ⊢
  intro m hm
  apply hP m
  contrapose! hm
  rw [notMem_support_iff] at hm ⊢
  rw [coeff_partialX, hm, map_zero]
private theorem separant_bound' {P : Biform} {a b : ℕ}
    (hP : P ∈ box a b) : separant P ∈ box (a-1) b := by
  rw [mem_restrictBidegree_iff_weightedTotalDegree_le] at hP ⊢
  exact ⟨(weightedTotalDegree_pderiv_le_sub _ _ _).trans (Nat.sub_le_sub_right hP.1 1),
    (weightedTotalDegree_pderiv_le _ _ _).trans hP.2⟩
theorem separant_bound {f : Equation} {e b : ℕ}
    (he : f.natDegree ≤ e) (hb : SeedBound f b) :
    separant (flatten f) ∈ box (e-1) b :=
  separant_bound' (flatten_bound he hb)
private theorem tangent_bound {f P : Biform} {e b a c : ℕ}
    (hf : f ∈ box e b) (hP : P ∈ box a c) (he : 0 < e) :
    tangent f P ∈ box (a+(e-1)) (c+b) := by
  have h1 := mul_mem_restrictBidegree (separant_bound' hf) (partialX_bound hP)
  unfold tangent
  apply (box _ _).sub_mem
  · simpa only [Nat.add_comm] using h1
  · by_cases ha : a = 0
    · have hzero : P.degreeOf none = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply degreeOf_le_iff.mpr
        intro m hm
        simpa only [ha] using ((mem_restrictBidegree.mp hP) m hm).1
      rw [show pderiv none P = 0 from pderiv_eq_zero_of_degreeOf_eq_zero hzero, mul_zero]
      exact (box _ _).zero_mem
    · have h2 := mul_mem_restrictBidegree (partialX_bound hf) (separant_bound' hP)
      rwa [show e+(a-1) = a+(e-1) by omega, Nat.add_comm b c] at h2
theorem cleared_bound {f : Equation} {e b : ℕ} (he : 0 < e)
    (hfe : f.natDegree ≤ e) (hb : SeedBound f b) (n : ℕ) :
    cleared (flatten f) n ∈ box (1+(2*n+1)*(e-1)) ((2*n+1)*b) := by
  have hf := flatten_bound hfe hb
  induction n with
  | zero =>
    have h := (box _ _).neg_mem (partialX_bound hf)
    simpa only [cleared, Nat.mul_zero, Nat.zero_add, Nat.one_mul, show 1+(e-1) = e by omega]
      using h
  | succ n ih =>
    have ha := separant_bound' hf
    have h1 := mul_mem_restrictBidegree ha (tangent_bound hf ih he)
    have h2 := mul_mem_restrictBidegree (tangent_bound hf ha he) ih
    have h2' := (box _ _).smul_mem (((2*n+1 : ℕ) : FX)) h2
    rw [cleared]
    apply (box _ _).sub_mem
    · convert h1 using 2 <;> ring
    · rw [mul_assoc]
      rw [← MvPolynomial.smul_eq_C_mul]
      convert h2' using 2 <;> ring
theorem box_pow {P : Biform} {a b : ℕ} (hP : P ∈ box a b) (n : ℕ) :
    P ^ n ∈ box (n*a) (n*b) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.zero_mul, mem_restrictBidegree]
    simp [support_one]
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using mul_mem_restrictBidegree ih hP
theorem ordinate_mem : Y ∈ box 1 0 := by
  classical
  rw [mem_restrictBidegree, MvPolynomial.support_X]
  intro m hm
  rw [Finset.mem_singleton] at hm
  subst m
  simp
end
end K1_14_6_1
end
section
namespace K1_14_6
noncomputable section
open K1 K1_14 Polynomial
def c1 : Prop :=
  ∀ d e b : ℕ, 0 < d → d < p → ∀ f : Equation,
    0 < f.natDegree → f.natDegree ≤ e → SeedBound f b →
    ∃ C : TaylorChart d e b, ∀ (z : K) (S : K[X]), S.natDegree ≤ d →
      atMark f z S = 0 → atMark f.derivative z S ≠ 0 → C.Recovers z S
def c2 : Prop :=
  ∀ d e b : ℕ, 0 < d → 0 < b → ∀ f : Equation,
    0 < f.natDegree → f.natDegree ≤ e → f.IsPrimitive →
    (f.map (algebraMap Seeds (FractionRing Seeds))).Separable → SeedBound f b →
    ∀ (T : Finset K) (z : K → K) (s : K → K[X]), Set.InjOn z (T : Set K) →
      (∀ γ ∈ T, atMark f (z γ) (s γ) = 0 ∧ atMark f.derivative (z γ) (s γ) ≠ 0) →
      ∀ C : TaylorChart d e b, (∀ γ ∈ T, C.Recovers (z γ) (s γ)) →
        Nonempty (LinearCover T s d e b)
end
end K1_14_6
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_1_2
noncomputable section
open K1_14 K1_14_2_4 K1_14_2_4_3_1 MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
private theorem linear_torsion {R : Type*} [CommRing R] (a b : R) (q : Polynomial R)
    (h : (Polynomial.C a * Polynomial.X + Polynomial.C b) * q = 0) :
    ∃ e : ℕ, Polynomial.C a ^ e * q = 0 := by
  let S := Localization.Away a
  let M : Submonoid (Polynomial R) := (Submonoid.powers a).map Polynomial.C
  let : IsLocalization M (Polynomial S) := Polynomial.isLocalization _ _
  let f := algebraMap (Polynomial R) (Polynomial S)
  have hz : f q = 0 := by
    change Polynomial.map (algebraMap R S) q = 0
    rcases subsingleton_or_nontrivial S with hS | hS
    · let := hS
      exact Subsingleton.elim _ _
    · let := hS
      have hu : IsUnit (algebraMap R S a) :=
        IsLocalization.map_units S (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)
      have hu' : IsUnit
          (Polynomial.C (algebraMap R S a) * Polynomial.X +
            Polynomial.C (algebraMap R S b)).leadingCoeff := by
        rwa [Polynomial.leadingCoeff_linear hu.ne_zero]
      apply (Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff hu').mp
      have hm := congrArg f h
      change Polynomial.map (algebraMap R S) _ = Polynomial.map (algebraMap R S) 0 at hm
      simpa only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_zero] using hm
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M (Polynomial S) q).mp hz
  have hmem := m.property
  change (m : Polynomial R) ∈ (Submonoid.powers a).map Polynomial.C at hmem
  rw [Submonoid.map_powers] at hmem
  obtain ⟨e, he⟩ := hmem
  change Polynomial.C a ^ e = (m : Polynomial R) at he
  exact ⟨e, by simpa only [he] using hm⟩
private theorem generic_torsion {R σ : Type*} [CommRing R] [Fintype σ]
    (a : σ → R) (q : MvPolynomial σ R)
    (h : (∑ j, C (a j) * MvPolynomial.X j) * q = 0) (i : σ) :
    ∃ e : ℕ, C (a i) ^ e * q = 0 := by
  classical
  let E := (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans
    (optionEquivLeft R {j : σ // j ≠ i})
  have hC (r : R) : E (C r) = Polynomial.C (C r) := by
    simp [E, renameEquiv_apply]
  have hi : E (MvPolynomial.X i) = Polynomial.X := by
    simp [E, renameEquiv_apply]
  let s : Finset σ := Finset.univ.erase i
  let b : MvPolynomial {j : σ // j ≠ i} R :=
    ∑ j ∈ s.attach, C (a j.val) * MvPolynomial.X ⟨j.val, (Finset.mem_erase.mp j.property).1⟩
  have hb : E (∑ j ∈ s, C (a j) * MvPolynomial.X j) = Polynomial.C b := by
    rw [← Finset.sum_attach s]
    simp only [b, map_sum, map_mul, hC]
    apply Finset.sum_congr rfl
    intro j _
    rw [show E (MvPolynomial.X (j : σ)) = Polynomial.C (MvPolynomial.X ⟨j.val,
      (Finset.mem_erase.mp j.property).1⟩) by
      simp [E, renameEquiv_apply,
        Equiv.optionSubtypeNe_symm_of_ne (Finset.mem_erase.mp j.property).1]]
  have hg : E (∑ j, C (a j) * MvPolynomial.X j) =
      Polynomial.C (C (a i)) * Polynomial.X + Polynomial.C b := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), map_add, map_mul, hi, hC, hb, add_comm]
  have hz : (Polynomial.C (C (a i)) * Polynomial.X + Polynomial.C b) * E q = 0 := by
    simpa only [map_mul, map_zero, hg] using congrArg E h
  obtain ⟨e, he⟩ := linear_torsion (C (a i)) b (E q) hz
  refine ⟨e, E.injective ?_⟩
  simpa only [map_mul, map_pow, map_zero, hC] using he
private def signedCoordinate (n : ℕ) : Option (Fin n) → HomRing n FX
  | none => -MvPolynomial.X (paramVar none)
  | some i => MvPolynomial.X (paramVar (some i))
theorem proof : K1_14_2_4_3_1.c2 := by
  classical
  intro n I p hp i
  let A := HomRing n FX
  let R := SourceRing n
  let B := HomRing n R
  let L := HomRing n (SliceField n)
  let M : Submonoid B := (nonZeroDivisors R).map C
  let : IsLocalization M L := MvPolynomial.isLocalization _ _
  let j : A →+* B := MvPolynomial.map (C : FX →+* R)
  let J : Ideal B := I.map j
  let g : B := ∑ k, j (signedCoordinate n k) * C (MvPolynomial.X k : R)
  let E := (commAlgEquiv FX (HomVar n) (Option (Fin n))).toRingHom
  have hE : E.comp j = C := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change commAlgEquiv FX (HomVar n) (Option (Fin n)) (MvPolynomial.map C (C r)) = C (C r)
      rw [map_C, commAlgEquiv_C, map_C]
    · intro k
      change commAlgEquiv FX (HomVar n) (Option (Fin n)) (MvPolynomial.map C (MvPolynomial.X k)) =
        C (MvPolynomial.X k)
      rw [map_X, commAlgEquiv_X]
  let Q : B →+* MvPolynomial (Option (Fin n)) (A ⧸ I) :=
    (MvPolynomial.map (Ideal.Quotient.mk I)).comp E
  have hQ : RingHom.ker Q = J := by
    change (RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I))).comap E = J
    rw [MvPolynomial.ker_map, Ideal.mk_ker, ← hE, ← Ideal.map_map]
    exact Ideal.comap_map_of_bijective E (commAlgEquiv FX (HomVar n) (Option (Fin n))).bijective
  have hQj (x : A) : Q (j x) = C (Ideal.Quotient.mk I x) := by
    have hx := RingHom.congr_fun hE x
    change E (j x) = C x at hx
    simp [Q, hx]
  have hQX (k : Option (Fin n)) : Q (C (MvPolynomial.X k : R)) = MvPolynomial.X k := by
    change MvPolynomial.map (Ideal.Quotient.mk I)
      (commAlgEquiv FX (HomVar n) (Option (Fin n)) (C (MvPolynomial.X k))) = MvPolynomial.X k
    rw [commAlgEquiv_C_X, map_X]
  have hQg : Q g = ∑ k, C (Ideal.Quotient.mk I (signedCoordinate n k)) * MvPolynomial.X k := by
    simp only [g, map_sum, map_mul, hQj, hQX]
  have hj : (algebraMap B L).comp j = MvPolynomial.map (algebraMap FX (SliceField n)) := by
    apply RingHom.ext
    intro x
    change MvPolynomial.map (algebraMap R (SliceField n)) (MvPolynomial.map C x) = _
    rw [MvPolynomial.map_map] <;> rfl
  have hJ : J.map (algebraMap B L) = extendHomIdeal I := by
    change (I.map j).map (algebraMap B L) = extendHomIdeal I
    rw [Ideal.map_map, hj, extendHomIdeal]
  have hg : algebraMap B L g = homCut n := by
    have hj' (x : A) : algebraMap B L (j x) = MvPolynomial.map (algebraMap FX (SliceField n)) x :=
      RingHom.congr_fun hj x
    have hCX (k : Option (Fin n)) :
        algebraMap B L (C (MvPolynomial.X k : R)) = C (sliceVariable k) := by
      change MvPolynomial.map (algebraMap R (SliceField n)) (C (MvPolynomial.X k)) = _
      rw [map_C] <;> rfl
    have hterm (k : Option (Fin n)) :
        algebraMap B L (j (signedCoordinate n k) * C (MvPolynomial.X k : R)) =
          C (sliceVariable k) * MvPolynomial.map (algebraMap FX (SliceField n))
            (signedCoordinate n k) := by
      rw [map_mul, hj', hCX, mul_comm]
    calc
      algebraMap B L g = ∑ k, C (sliceVariable k) *
          MvPolynomial.map (algebraMap FX (SliceField n)) (signedCoordinate n k) := by
        simp only [g, map_sum, hterm]
      _ = homCut n := by
        rw [Fintype.sum_option]
        simp only [signedCoordinate, map_X, map_neg, homCut, sub_eq_add_neg]
        rw [add_comm]
        exact congrArg (fun z : L =>
          (∑ k : Fin n, C (sliceVariable (some k)) * MvPolynomial.X (paramVar (some k))) + z)
          (mul_neg (C (sliceVariable (n := n) none) : L) (MvPolynomial.X (paramVar none)))
  obtain ⟨q, s, rfl⟩ := IsLocalization.exists_mk'_eq M p
  rw [← hg, ← hJ, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_mem_map_algebraMap_iff] at hp
  obtain ⟨d, hd, hmem⟩ := hp
  have hz : Q g * Q (d * q) = 0 := by
    rw [← map_mul, ← RingHom.mem_ker, hQ, ← mul_left_comm]
    exact hmem
  rw [hQg] at hz
  obtain ⟨e, he⟩ := generic_torsion (fun k => Ideal.Quotient.mk I (signedCoordinate n k))
    (Q (d * q)) hz i
  have ht : d * (j (signedCoordinate n i) ^ e * q) ∈ J := by
    rw [← hQ, RingHom.mem_ker, mul_left_comm, map_mul, map_pow, hQj]
    exact he
  have hpow : algebraMap B L (j (signedCoordinate n i)) ^ e * IsLocalization.mk' L q s ∈
      extendHomIdeal I := by
    rw [← hJ, ← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨d, hd, ht⟩
  refine ⟨e, ?_⟩
  have hji : algebraMap B L (j (signedCoordinate n i)) =
      MvPolynomial.map (algebraMap FX (SliceField n)) (signedCoordinate n i) :=
    RingHom.congr_fun hj _
  rw [hji] at hpow
  cases i with
  | some k => simpa [signedCoordinate] using hpow
  | none =>
    simp only [signedCoordinate, map_neg, map_X, ← neg_one_mul (MvPolynomial.X (paramVar none) : L),
      mul_pow, mul_assoc] at hpow
    exact ((extendHomIdeal I).unit_mul_mem_iff_mem (isUnit_one.neg.pow e)).mp hpow
end
end K1_14_2_4_3_1_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_3_1_1
noncomputable section
open K1_14_2_4_3_1 MvPolynomial
private def tag : (ℕ × ℕ) →+ (Bool →₀ ℕ) where
  toFun d := Finsupp.single false d.1 + Finsupp.single true d.2
  map_zero' := by simp
  map_add' d e := by
    ext i
    cases i <;> simp
@[simp] private theorem tag_false (d : ℕ × ℕ) : tag d false = d.1 := by
  simp [tag]
@[simp] private theorem tag_true (d : ℕ × ℕ) : tag d true = d.2 := by
  simp [tag]
private theorem tag_injective : Function.Injective tag := by
  intro d e h
  exact Prod.ext (by simpa using DFunLike.congr_fun h false)
    (by simpa using DFunLike.congr_fun h true)
private theorem tag_unit (side : Bool) : tag (unitDegree side) = Finsupp.single side 1 := by
  ext i
  cases side <;> cases i <;> simp [unitDegree]
private theorem tag_recover (m : Bool →₀ ℕ) : tag (m false, m true) = m := by
  ext i
  cases i <;> simp
variable {n : ℕ} {k : Type} [Field k]
private theorem weight_sumElim (e : Option (Fin n) →₀ ℕ) (t : Bool →₀ ℕ) :
    Finsupp.weight (biWeight n) (e.sumElim t) = (e none + t false, e.some.degree + t true) := by
  apply Prod.ext
  · simp [Finsupp.weight_eq_sum, Prod.fst_sum, Fintype.sum_sum_type,
      Fintype.sum_option, Fintype.univ_bool, biWeight, group, unitDegree]
  · simp [Finsupp.weight_eq_sum, Prod.snd_sum, Fintype.sum_sum_type,
      Fintype.sum_option, Fintype.univ_bool, biWeight, group, unitDegree, Finsupp.degree_eq_sum,
      Finsupp.some_apply]
private theorem dehom_monomial_sumElim (e : Option (Fin n) →₀ ℕ) (t : Bool →₀ ℕ) (c : k) :
    dehom (monomial (e.sumElim t) c) = monomial e c := by
  rw [dehom, aeval_monomial, Finsupp.prod_sumElim, algebraMap_eq, monomial_eq]
  simp [Finsupp.prod]
private theorem dehom_mem_box {p : HomRing n k} {u v : ℕ}
    (h : Bihomogeneous p (u, v)) :
    dehom p ∈ restrictBidegree (Fin n) k u v := by
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hw := h (mem_support_iff.mp hd)
  rw [← Finsupp.comapDomain_sumElim_comapDomain d, weight_sumElim] at hw
  rw [← Finsupp.comapDomain_sumElim_comapDomain d, dehom_monomial_sumElim]
  apply mem_restrictBidegree.mpr
  intro m hm
  have he := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst m
  have hu := congrArg Prod.fst hw
  have hv := congrArg Prod.snd hw
  exact ⟨(Nat.le_add_right _ _).trans_eq hu, (Nat.le_add_right _ _).trans_eq hv⟩
private theorem homogeneous_lift (p : MvPolynomial (Option (Fin n)) k) (u v : ℕ)
    (h : p ∈ restrictBidegree (Fin n) k u v) :
    ∃ q : HomRing n k, Bihomogeneous q (u, v) ∧ dehom q = p := by
  classical
  let lift (e : Option (Fin n) →₀ ℕ) : HomRing n k :=
    monomial (e.sumElim (tag (u - e none, v - e.some.degree))) (p.coeff e)
  refine ⟨∑ e ∈ p.support, lift e, ?_, ?_⟩
  · apply IsWeightedHomogeneous.sum
    intro e he
    obtain ⟨hu, hv⟩ := mem_restrictBidegree.mp h e he
    apply isWeightedHomogeneous_monomial
    rw [weight_sumElim, tag_false, tag_true, Nat.add_sub_of_le hu, Nat.add_sub_of_le hv]
  · rw [map_sum]
    conv_rhs => rw [p.as_sum]
    exact Finset.sum_congr rfl fun e _ => dehom_monomial_sumElim _ _ _
variable (I : Ideal (MvPolynomial (Option (Fin n)) k))
private theorem lift_iff (u v : ℕ) (x : MvPolynomial (Option (Fin n)) k ⧸ I) :
    x ∈ quotientBidegreeLE I u v ↔
      ∃ p : HomRing n k, Bihomogeneous p (u, v) ∧ dehomClass I p = x := by
  rw [mem_quotientBidegreeLE]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨q, hq, he⟩ := homogeneous_lift p u v hp
    exact ⟨q, hq, by simp [dehomClass, he]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨dehom p, dehom_mem_box hp, rfl⟩
@[simp] private theorem dehomClass_pad (side : Bool) :
    dehomClass I (MvPolynomial.X (pad side)) = 1 := by
  simp [dehomClass, dehom, pad]
private theorem gradedEval_X (i : HomVar n) :
    gradedEval I (MvPolynomial.X i) = C (dehomClass I (MvPolynomial.X i)) * MvPolynomial.X (group i) := by
  simp [gradedEval]
@[simp] private theorem gradedEval_pad (side : Bool) :
    gradedEval I (MvPolynomial.X (pad side)) = MvPolynomial.X side := by
  rw [gradedEval_X, dehomClass_pad, map_one, one_mul]
  rfl
private theorem gradedEval_monomial (d : HomVar n →₀ ℕ) (c : k) :
    gradedEval I (monomial d c) =
      monomial (tag (Finsupp.weight (biWeight n) d)) (dehomClass I (monomial d c)) := by
  classical
  induction d using Finsupp.induction with
  | zero =>
      simp only [map_zero, monomial_zero']
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
        IsScalarTower.algebraMap_apply k (MvPolynomial (Option (Fin n)) k ⧸ I),
        MvPolynomial.algebraMap_eq]
  | single_add i e d _ _ ih =>
      rw [add_comm (Finsupp.single i e) d]
      simp only [monomial_add_single, map_mul, map_pow, map_add, Finsupp.weight_single, ih]
      rw [gradedEval_X, C_mul_X_eq_monomial, monomial_pow, monomial_mul_monomial,
        map_nsmul tag, show biWeight n i = unitDegree (group i) from rfl, tag_unit]
private theorem gradedEval_bihomogeneous {d : ℕ × ℕ} {p : HomRing n k}
    (hp : Bihomogeneous p d) :
    gradedEval I p = monomial (tag d) (dehomClass I p) := by
  conv_lhs => rw [p.as_sum, map_sum]
  conv_rhs => rw [p.as_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun e he => by
    rw [gradedEval_monomial, hp (mem_support_iff.mp he)]
private theorem component_monomial {D : Type} [AddCommMonoid D] [DecidableEq D]
    (w : HomVar n → D) (s : D) (d : HomVar n →₀ ℕ) (c : k) :
    weightedHomogeneousComponent w s (monomial d c) =
      if Finsupp.weight w d = s then monomial d c else 0 := by
  classical
  ext e
  by_cases h : d = e
  · subst e
    by_cases hw : Finsupp.weight w d = s <;>
      simp [coeff_weightedHomogeneousComponent, hw]
  · by_cases hw : Finsupp.weight w d = s <;>
      simp [coeff_weightedHomogeneousComponent, h, hw]
private theorem coeff_gradedEval_component {D : Type} [AddCommMonoid D] [DecidableEq D]
    (w : HomVar n → D) (f : ℕ × ℕ → D)
    (hf : ∀ d : HomVar n →₀ ℕ, Finsupp.weight w d = f (Finsupp.weight (biWeight n) d))
    (s : D) (p : HomRing n k) (b : ℕ × ℕ) :
    (gradedEval I (weightedHomogeneousComponent w s p)).coeff (tag b) =
      if f b = s then (gradedEval I p).coeff (tag b) else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [component_monomial, hf]
      by_cases h : Finsupp.weight (biWeight n) d = b
      · rw [h]
        split <;> simp [gradedEval_monomial, *]
      · have ht : tag (Finsupp.weight (biWeight n) d) ≠ tag b := fun ht =>
          h (tag_injective ht)
        split <;> simp [gradedEval_monomial, ht]
  | add a b ha hb =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb]
      split <;> simp
private theorem homIdeal_paramGraded : ParamGraded (homIdeal I) := by
  intro p hp v
  change gradedEval I p = 0 at hp
  change gradedEval I (weightedHomogeneousComponent (paramWeight n) v p) = 0
  have hw (d : HomVar n →₀ ℕ) :
      Finsupp.weight (paramWeight n) d = (Finsupp.weight (biWeight n) d).2 := by
    simp only [Finsupp.weight_apply, Finsupp.sum, Prod.snd_sum, Prod.smul_snd, paramWeight]
  ext m
  rw [← tag_recover m, coeff_gradedEval_component I (paramWeight n) Prod.snd hw, hp]
  simp
private theorem span_pad_component (side : Bool) (a : HomRing n k) (v : ℕ) :
    weightedHomogeneousComponent (paramWeight n) v (a * MvPolynomial.X (pad side)) ∈
      Ideal.span ({MvPolynomial.X (pad side)} : Set (HomRing n k)) := by
  classical
  induction a using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [show monomial d c * MvPolynomial.X (pad side) =
          monomial (d + Finsupp.single (pad side) 1) c by rw [monomial_add_single, pow_one],
        component_monomial]
      split
      · rw [monomial_add_single, pow_one]
        exact Ideal.mem_span_singleton'.mpr ⟨monomial d c, rfl⟩
      · exact (Ideal.span _).zero_mem
  | add a b ha hb =>
      rw [add_mul, map_add]
      exact (Ideal.span _).add_mem ha hb
private theorem boundary_paramGraded (side : Bool) : ParamGraded (boundaryIdeal I side) := by
  intro p hp v
  rw [boundaryIdeal, sup_comm, Ideal.mem_span_singleton_sup] at hp
  obtain ⟨a, b, hb, rfl⟩ := hp
  rw [map_add]
  exact (boundaryIdeal I side).add_mem (Ideal.mem_sup_right (span_pad_component side a v))
    (Ideal.mem_sup_left (homIdeal_paramGraded I b hb v))
private theorem boundary_iff (side : Bool) (u v : ℕ) (p : HomRing n k)
    (hp : Bihomogeneous p ((u, v) + unitDegree side)) :
    p ∈ boundaryIdeal I side ↔ dehomClass I p ∈ quotientBidegreeLE I u v := by
  classical
  rw [lift_iff, boundaryIdeal, sup_comm, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨a, b, hb, he⟩
    change gradedEval I b = 0 at hb
    have heval : gradedEval I a * MvPolynomial.X side = gradedEval I p := by
      simpa only [map_add, map_mul, gradedEval_pad, hb, add_zero] using congrArg (gradedEval I) he
    let q := weightedHomogeneousComponent (biWeight n) (u, v) a
    have hq : Bihomogeneous q (u, v) :=
      weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hc : (gradedEval I a).coeff (tag (u, v)) = dehomClass I p := by
      have h := congrArg (fun f : MvPolynomial Bool (MvPolynomial (Option (Fin n)) k ⧸ I) =>
        f.coeff (tag ((u, v) + unitDegree side))) heval
      rw [gradedEval_bihomogeneous I hp] at h
      simpa only [map_add, tag_unit, coeff_mul_X, coeff_monomial, ite_true] using h
    refine ⟨q, hq, ?_⟩
    have h := coeff_gradedEval_component I (biWeight n) id (fun _ => rfl) (u, v) a (u, v)
    simp only [id_eq, ite_true] at h
    change (gradedEval I q).coeff (tag (u, v)) = _ at h
    simpa only [gradedEval_bihomogeneous I hq, coeff_monomial, ite_true, hc] using h
  · rintro ⟨q, hq, he⟩
    have hmul : Bihomogeneous (q * MvPolynomial.X (pad side)) ((u, v) + unitDegree side) :=
      hq.mul (isWeightedHomogeneous_X k (biWeight n) (pad side))
    refine ⟨q, p - q * MvPolynomial.X (pad side), ?_, by ring⟩
    change gradedEval I (p - q * MvPolynomial.X (pad side)) = 0
    rw [map_sub, gradedEval_bihomogeneous I hp, gradedEval_bihomogeneous I hmul]
    simp [he]
theorem proof : K1_14_2_4_3_1.c1 := by
  intro n k _ I
  exact ⟨lift_iff I, fun side => ⟨boundary_paramGraded I side, boundary_iff I side⟩⟩
end
end K1_14_2_4_3_1_1
end
section
namespace K1_14_6_2
noncomputable section
open K1 K1_14 K1_14_6 MvPolynomial
open scoped Polynomial
private abbrev ι : FX →+* ClosedField := algebraMap FX ClosedField
private def closedPoint (z : K) (S : K[X]) : Option (Fin 2) → ClosedField :=
  ι ∘ rootPoint z S
private theorem eval_extend {σ : Type*} (x : σ → FX) (P : MvPolynomial σ FX) :
    MvPolynomial.eval (ι ∘ x) (MvPolynomial.map ι P) = ι (MvPolynomial.eval x P) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_comp]
private def extendEquation (f : Equation) : SourcePolynomial ClosedField :=
  f.map (MvPolynomial.map ι)
private theorem extendEquation_eval (f : Equation) (z : K) (S : K[X]) :
    (extendEquation f).eval₂ (MvPolynomial.eval (closedPoint z S ∘ some))
      (closedPoint z S none) = ι (atMark f z S) := by
  change (f.map (MvPolynomial.map ι)).eval₂ _ (ι (atX S)) = _
  rw [Polynomial.eval₂_map, atMark, Polynomial.hom_eval₂]
  congr 1
  apply RingHom.ext
  intro g
  exact eval_extend (rootPoint z S ∘ some) g
private theorem extend_mem {P : Biform} {a c : ℕ}
    (hP : P ∈ restrictBidegree (Fin 2) FX a c) :
    MvPolynomial.map ι P ∈ restrictBidegree (Fin 2) ClosedField a c := by
  rw [mem_restrictBidegree] at hP ⊢
  intro m hm
  exact hP m (support_map_subset _ _ hm)
private theorem eval_valueCut {d e b : ℕ} (C : TaylorChart d e b)
    {z : K} {S : K[X]} (h : C.Recovers z S) (x a : K) :
    MvPolynomial.eval (closedPoint z S)
      (MvPolynomial.map ι (C.numerator x - seedEmbedding a • C.denominator)) = 0 ↔
      S.eval x = a := by
  obtain ⟨hD, hN⟩ := h
  rw [closedPoint, eval_extend, map_sub, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.eval_C, hN x]
  rw [← map_zero ι, ι.injective.eq_iff, sub_eq_zero, mul_comm (seedEmbedding a),
    mul_right_inj' hD]
  exact seedEmbedding.injective.eq_iff
theorem proof : K1_14_6.c2 := by
  classical
  intro d e b hd hb f hf0 hfe _hprimitive _hseparable hfseed T z s hz hroots C hC
  let a := ordinateBound d e
  let c := parameterBound d b
  have ha : 0 < a := by simp [a, ordinateBound]
  have hc : 0 < c := by
    change 0 < taylorPower d * b
    exact Nat.mul_pos (by unfold taylorPower; omega) hb
  let F := extendEquation f
  have hnat : F.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (MvPolynomial.map_injective _ ι.injective) f
  have hF : F ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by rw [hnat]; exact hf0)
  have hcoeff : ∀ j, (F.coeff j).totalDegree ≤ b := by
    intro j
    change ((f.map (MvPolynomial.map ι)).coeff j).totalDegree ≤ b
    rw [Polynomial.coeff_map]
    exact (Finset.sup_mono (support_map_subset _ _)).trans (hfseed j)
  obtain ⟨components, hdim, hcount, hsum, hcover⟩ :=
    regularComponents ha hc F hF (hnat.trans_le hfe) hcoeff
  let pt := fun γ => monomialPoint (bidegreeExponents (Fin 2) a c) (closedPoint (z γ) (s γ))
  let sectionPoly := fun x y => MvPolynomial.map ι (C.numerator x - seedEmbedding y • C.denominator)
  have hsection (x y : K) : sectionPoly x y ∈ restrictBidegree (Fin 2) ClosedField a c :=
    extend_mem (Submodule.sub_mem _ (C.numerator_bound x)
      (Submodule.smul_mem _ _ C.denominator_bound))
  let cut := fun x y => bidegreeLift (sectionPoly x y) (hsection x y)
  refine ⟨⟨pt, ?_, cut, fun x y => totalDegree_bidegreeLift_le_one _ _, ?_,
    components, fun P hP => (hdim P hP).1, fun P hP => (hdim P hP).2, ?_, hcount, ?_⟩⟩
  · intro γ hγ η hη hpt
    have hcoords : closedPoint (z γ) (s γ) = closedPoint (z η) (s η) :=
      monomialPoint_injective (fun i => single_mem_bidegreeExponents ha hc i) hpt
    have hfirst := congrFun hcoords (some (0 : Fin 2))
    change ι (seedEmbedding (z γ)) = ι (seedEmbedding (z η)) at hfirst
    exact hz hγ hη (seedEmbedding.injective (ι.injective hfirst))
  · intro γ hγ x y
    change aeval (monomialPoint _ (closedPoint (z γ) (s γ))) (bidegreeLift _ _) = 0 ↔ _
    rw [aeval_monomialPoint, ← bidegreeMap_eq_monomialMap, bidegreeMap_bidegreeLift]
    exact eval_valueCut C (hC γ hγ) x y
  · intro γ hγ
    apply hcover (closedPoint (z γ) (s γ))
    · rw [show F = extendEquation f from rfl, extendEquation_eval, (hroots γ hγ).1, map_zero]
    · rw [show F.derivative = extendEquation f.derivative from Polynomial.derivative_map _ _,
        extendEquation_eval]
      simpa only [map_zero] using ι.injective.ne (hroots γ hγ).2
  · exact hsum
end
end K1_14_6_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_1_5_2
open K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_5
open scoped Polynomial
theorem proof : K1_14_2_4_1_5.c2 := by
  intro n H B _ hH W hW
  let : Algebra (SlopeField n)[X] (ExtendedBase B) := polynomialAction (genericLinear B)
  let : Algebra (SlopeField n)[X] (SliceField n) := offsetAlgebra n
  let := offset_isFractionRing n
  let := hH.finite
  let := hW
  let f := (sectionToLocalized B).toLinearMap
  have hf : Function.Surjective f := sectionToLocalized_surjective B
  have hfinite : Module.Finite (SliceField n) (LocalizedBase B) := Module.Finite.of_surjective f hf
  have hlen : Module.finrank (SliceField n) (LocalizedBase B) ≤ H :=
    (LinearMap.finrank_le_finrank_of_surjective hf).trans hH.length
  obtain ⟨C, hC⟩ := growth_of_localized (genericLinear B) W (SliceField n) hfinite
  exact ⟨C, fun k => (hC k).trans (Nat.add_le_add_left (Nat.mul_le_mul_left k hlen) C)⟩
end K1_14_2_4_1_5_2
end
section
namespace K1_13_5_5
noncomputable section
open K1_13 MvPolynomial
open scoped BigOperators Polynomial
abbrev CoeffIndex := Fin taylorLength
abbrev CoeffRing := MvPolynomial CoeffIndex Geom
abbrev FreshField := FractionRing Geom[X]
abbrev FreshCoeffRing := MvPolynomial CoeffIndex FreshField
abbrev FreshJetRing := MvPolynomial (Fin 3) FreshField
def coeffPoint (P : Geom[X]) : CoeffIndex → Geom := fun a => P.coeff a.val
def jetForm {F : Type*} [Field F] (x : F) (j : ℕ) : MvPolynomial CoeffIndex F :=
  ∑ a : CoeffIndex, C ((a.val.choose j : F) * x ^ (a.val - j)) * MvPolynomial.X a
def freshCenter : FreshField := algebraMap Geom[X] FreshField Polynomial.X
def freshRow (f : Row 3) : FreshJetRing :=
  MvPolynomial.map (algebraMap Geom[X] FreshField) f
def freshIdeal (P : Ideal CoeffRing) : Ideal FreshCoeffRing :=
  P.map (MvPolynomial.map (algebraMap Geom FreshField))
def freshProjection : FreshJetRing →ₐ[FreshField] FreshCoeffRing :=
  MvPolynomial.aeval fun j => jetForm freshCenter j.val
structure FreshChart (P : Ideal CoeffRing) (g d : FreshJetRing) : Prop where
  prime : P.IsPrime
  equation_ne : g ≠ 0
  image : (freshIdeal P).comap freshProjection = Ideal.span {g}
  regular_open : d ∉ Ideal.span {g}
  recover : ∀ a : CoeffIndex, ∃ (v : FreshJetRing) (m : ℕ),
    freshProjection d ^ m * MvPolynomial.X a - freshProjection v ∈ freshIdeal P
end
end K1_13_5_5
end
section
set_option autoImplicit false
namespace K1_14_2_3
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
def rootImage (I : Ideal Ambient) : Ideal RootAmbient := I.comap rootIncl
def seedImage (I : Ideal Ambient) : Ideal Seeds := (rootImage I).comap rootSeeds
def constantCoefficients : L →+* FX :=
  (algebraMap L[X] FX).comp (Polynomial.C : L →+* L[X])
def DefinedOverConstants (P : Ideal Seeds) : Prop :=
  ∃ C : MvPolynomial (Fin 2) L, Irreducible C ∧
    P = Ideal.span {MvPolynomial.map constantCoefficients C}
def SeedSlice (I : Ideal Ambient) : Prop :=
  I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 1 ∧
  Module.Finite SeedField (JetSeedSection I) ∧
  0 < Module.finrank SeedField (JetSeedSection I)
def seedLength (I : Ideal Ambient) : ℕ := Module.finrank SeedField (JetSeedSection I)
def yLength (I : Ideal Ambient) : ℕ := Module.finrank SeedField (JetYSection I)
end
end K1_14_2_3
end
