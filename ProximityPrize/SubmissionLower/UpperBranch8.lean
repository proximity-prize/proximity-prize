import Mathlib.Algebra.Order.Sub.Prod
import ProximityPrize.SubmissionLower.LowerBase
import ProximityPrize.SubmissionLower.UpperBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_8
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P1 (K I node agreement)
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8
noncomputable section
open Polynomial Finset
open P1 (K I Words AnchorModel AnchoredFamily p node agreement blockLength)
open P1_7 (Reduced AdjacentChart regularRoot degreeAt quotientOrder singularDegree)
open K1_14 (L FX Seeds Equation SeedBound liftPoly atMark seedEmbedding)
open K1_14_4 (seedDegree)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten cleared separant markEval)
open scoped BigOperators
structure Input where
  words : Words
  deleted : Finset I
  model : AnchorModel words deleted
  labels : Finset K
  family : AnchoredFamily model labels
  shift_out : model.shift ∉ labels
  block : (Polynomial L)
  chart : AdjacentChart model family block
  marks : Finset K
  marks_sub : marks ⊆ labels
  f : Equation
  regular : ∀ γ ∈ marks, regularRoot f (model.label γ) (family.scalar γ)
  reduced : Reduced f
  sheets : 3 ≤ f.natDegree
  seed_pos : 0 < seedDegree f
  v : ℕ
  seed_bound : SeedBound f v
  lo : ℕ
  hi : ℕ
  lower : lo ≤ model.overhead.toNat
  upper : model.overhead.toNat ≤ hi
  positive : 0 < model.overhead.toNat
  quotient_pos : 0 < quotientOrder model.overhead.toNat
  agreement_gap : degreeAt hi < agreement
  factorial_guard : degreeAt hi + 1 < p
  separant_guard : singularDegree f.natDegree v < p
  flat_guard : f.natDegree * degreeAt hi + v < p
abbrev Input.w (J : Input) : ℕ := J.model.overhead.toNat
abbrev Input.ell (J : Input) : ℕ := quotientOrder J.w
abbrev Input.e (J : Input) : ℕ := J.f.natDegree
def Input.secondBlock (J : Input) : (Polynomial L) := J.block.map (frobenius L p)
def Input.blockProduct (J : Input) : (Polynomial L) := J.block * J.secondBlock
abbrev SeedConstants := MvPolynomial (Fin 2) L
def residueData (_J : Input) (i : Fin 2) (g : (Polynomial K)) : (Polynomial SeedConstants) :=
  ((liftPoly g).map (if i = 0 then RingHom.id L else frobenius L p)).map MvPolynomial.C
def blockAt (J : Input) (i : Fin 2) : (Polynomial L) :=
  if i = 0 then J.block else J.secondBlock
def residueDenominator (J : Input) (i : Fin 2) : (Polynomial SeedConstants) :=
  residueData J i (J.model.factor * J.model.A₀) +
    C (MvPolynomial.X i) * residueData J i (J.model.factor * J.model.A₁)
def evalSeedConstants (z : K) : SeedConstants →+* L :=
  MvPolynomial.eval ![algebraMap K L z, (algebraMap K L z)^p]
structure ResidueLift (J : Input) where
  denominator : SeedConstants
  numerator : (Polynomial SeedConstants)
  denominator_ne : denominator ≠ 0
  denominator_degree : denominator.totalDegree ≤ 2 * J.w
  numerator_degree : ∀ j, (numerator.coeff j).totalDegree ≤ 2 * J.w
  numerator_width : numerator.natDegree < 2 * J.w
  congruences : ∀ i : Fin 2, (blockAt J i).map MvPolynomial.C ∣
    residueDenominator J i * numerator +
      C (MvPolynomial.X i * denominator) * residueData J i J.model.Q
  unit_at_marks : ∀ γ ∈ J.labels, evalSeedConstants (J.model.label γ) denominator ≠ 0
def constantAbscissa : L →+* FX :=
  (algebraMap (Polynomial L) FX).comp Polynomial.C
def liftSeeds : SeedConstants →+* Seeds := MvPolynomial.map constantAbscissa
def seedBiform : SeedConstants →+* Biform :=
  (MvPolynomial.rename (R := FX) (some : Fin 2 → Option (Fin 2))).toRingHom.comp liftSeeds
def center : FX := algebraMap (Polynomial L) FX Polynomial.X
def liftTaylor (P : (Polynomial SeedConstants)) (i : ℕ) : Biform :=
  (Polynomial.taylor (MvPolynomial.C center) (P.map seedBiform)).coeff i
def inverseBlockCoeff (J : Input) (i : ℕ) : FX :=
  (i.factorial : FX)⁻¹ *
    (Dx^[i]) ((algebraMap (Polynomial L) FX J.blockProduct)⁻¹)
def ordinateTaylorNum (f : Equation) (r : ℕ) : ℕ → Biform
  | 0 => separant (flatten f) ^ (2*r-1) * MvPolynomial.X none
  | i + 1 => MvPolynomial.C (((i+1).factorial : FX)⁻¹) *
      (separant (flatten f) ^ ((2*r-1)-(2*i+1)) * cleared (flatten f) i)
def quotientNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  ∑ i ∈ range (r+1), MvPolynomial.C (inverseBlockCoeff J (r-i)) *
    (seedBiform B.denominator * ordinateTaylorNum J.f r i -
      separant (flatten J.f) ^ (2*r-1) * liftTaylor B.numerator i)
def quotientDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  seedBiform B.denominator * separant (flatten J.f) ^ (2*r-1)
def cutoff (J : Input) (B : ResidueLift J) : Equation :=
  MvPolynomial.optionEquivLeft FX (Fin 2) (quotientNumerator J B (J.ell+1))
abbrev SeedField := FractionRing Seeds
def generic (q : Equation) : (Polynomial SeedField) := q.map (algebraMap Seeds SeedField)
def rootOn (J : Input) (q : Equation) (γ : K) : Prop :=
  atMark q (J.model.label γ) (J.family.scalar γ) = 0
structure Factors (J : Input) (B : ResidueLift J) where
  proper : Equation
  count : ℕ
  flat : Fin count → Equation
  product : J.f = proper * ∏ j, flat j
  cutoff_at_marks : ∀ γ ∈ J.marks, rootOn J (cutoff J B) γ
  proper_coprime : IsCoprime (generic proper) (generic (cutoff J B))
  flat_reduced : ∀ j, Reduced (flat j)
  flat_irred : ∀ j, Irreducible (generic (flat j))
  flat_cutoff : ∀ j, generic (flat j) ∣ generic (cutoff J B)
  sheets : count ≤ J.e
  degree_each : ∀ j, (flat j).natDegree ≤ J.e
  seed_sum : ∑ j, seedDegree (flat j) ≤ J.v
structure ProperCurve (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime : Ideal Equation
  isPrime : prime.IsPrime
  onProper : D.proper ∈ prime
  onCutoff : cutoff J B ∈ prime
  marks : Finset K
  sub : marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker
    (eval₂RingHom (K1_14.graphEval (J.model.label γ)) (K1_14.atX (J.family.scalar γ)))
  persistent : Finset I
  hits : ∀ γ ∈ marks, ∀ x ∈ persistent, (J.family.scalar γ).eval (node x) = J.model.word x
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
  positive_seed : 0 < seed
  sections : ∀ x ∉ persistent,
    let r := J.ell - persistent.card
    (marks.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x).card ≤
      (1 + (J.e-3)*r)*fiber + r*tangent + (r*J.v + 2*J.w)*seed
def cutVelocity (J : Input) : ℕ := quotientOrder J.lo + 1
def cutOrdinate (J : Input) : ℕ := 1 + cutVelocity J * (J.e-1)
def cutSeed (J : Input) : ℕ := cutVelocity J * J.v + 2*J.hi
structure ProperCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count : ℕ
  curves : Fin count → ProperCurve J B D
  covers : ∀ γ ∈ J.marks, rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).fiber ≤ J.v*cutSeed J + J.v^2*cutVelocity J
  tangent : ∑ j, (curves j).tangent ≤ 2*J.e*J.v*cutSeed J + J.v^2*cutOrdinate J
  seed : ∑ j, (curves j).seed ≤
    J.e*cutSeed J + J.v*((2*J.e-2)*cutVelocity J + cutOrdinate J)
abbrev SeedClosure := AlgebraicClosure SeedField
def intoSeedClosure : Seeds →+* SeedClosure :=
  (algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField)
def genericPoint (y : SeedClosure) : Biform →+* SeedClosure :=
  (eval₂RingHom intoSeedClosure y).comp (MvPolynomial.optionEquivLeft FX (Fin 2)).toRingHom
def liftConstantSeeds : SeedConstants →+* SeedClosure :=
  intoSeedClosure.comp liftSeeds
def reconstructed (J : Input) (B : ResidueLift J) (y : SeedClosure) : (Polynomial SeedClosure) :=
  let ζ := intoSeedClosure (MvPolynomial.C center)
  let ev := genericPoint y
  C ((liftConstantSeeds B.denominator)⁻¹) * B.numerator.map liftConstantSeeds +
    J.blockProduct.map (liftConstantSeeds.comp MvPolynomial.C) *
      ∑ j ∈ range (J.ell+1),
        C (ev (quotientNumerator J B j) / ev (quotientDenominator J B j)) *
          (Polynomial.X - C ζ)^j
def genericRoots (q : Equation) : Finset SeedClosure := by
  classical
  exact (q.map intoSeedClosure).roots.toFinset
structure DifferentialProduct (J : Input) (B : ResidueLift J) (q : Equation) where
  numerator : Polynomial (Polynomial Seeds)
  denominator : Seeds
  denominator_ne : denominator ≠ 0
  leading : numerator.coeff q.natDegree = C denominator
  abscissa_width : ∀ j, (numerator.coeff j).natDegree ≤ q.natDegree * degreeAt J.hi
  numerator_constant : ∀ i j m, Dx (((numerator.coeff i).coeff j).coeff m) = 0
  denominator_constant : ∀ m, Dx (denominator.coeff m) = 0
  identity :
    numerator.map (Polynomial.mapRingHom intoSeedClosure) =
      C (C (intoSeedClosure denominator)) *
        ∏ y ∈ genericRoots q,
          (Polynomial.X - C (reconstructed J B y))
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8
noncomputable section
open P1 (agreement blockLength)
open P1_7 (degreeAt quotientOrder     ceilRatio )
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8_3
noncomputable section
open P1 (K I node)
open P1_7_8 (Input ResidueLift Factors)
open K1_14 (FX Equation Seeds atX graphEval seedEmbedding)
open K1_14_6_1 (Dx partialX flatten)
open Polynomial (eval₂RingHom)
abbrev JetRing := Polynomial Equation
instance jetCommRing : CommRing JetRing := @AddMonoidAlgebra.commRing Equation ℕ inferInstance _
abbrev Degree := ℕ × ℕ × ℕ
def nefDegree (h t s : ℕ) : Degree := (h + 2*t, t, s)
abbrev CoxVar := Fin 2 ⊕ (Fin 2 ⊕ Fin 3)
abbrev Cox := MvPolynomial CoxVar FX
def coxWeight : CoxVar → Degree
  | .inl _ => (1, 0, 0)
  | .inr (.inl i) => (2*i.val, 1, 0)
  | .inr (.inr _) => (0, 0, 1)
def ordinate : JetRing := Polynomial.C Polynomial.X
def seedVar (i : Fin 2) : JetRing :=
  Polynomial.C (Polynomial.C (MvPolynomial.X i))
def affineCoord : CoxVar → JetRing
  | .inl i => if i = 0 then 1 else ordinate
  | .inr (.inl i) => if i = 0 then 1 else Polynomial.X
  | .inr (.inr i) => if hi : i.val < 2 then seedVar ⟨i.val, hi⟩ else 1
def dehom : Cox →ₐ[FX] JetRing := MvPolynomial.aeval affineCoord
structure RelativeSection (Q : Ideal JetRing) (d : Degree) where
  order : ℕ
  finiteChart : Cox
  inverseChart : Cox
  finite_degree :
    finiteChart.IsWeightedHomogeneous coxWeight (d + order • (1, 0, 0))
  inverse_degree :
    inverseChart.IsWeightedHomogeneous coxWeight (d + order • (1, 0, 0))
  glue : ordinate ^ order * dehom finiteChart - dehom inverseChart ∈ Q
def RelativeSection.affine {Q : Ideal JetRing} {d : Degree}
    (S : RelativeSection Q d) : JetRing :=
  dehom S.finiteChart
def gradedPiece (Q : Ideal JetRing) (d : Degree) : Submodule FX (JetRing ⧸ Q) :=
  (MvPolynomial.weightedHomogeneousSubmodule FX coxWeight d).map
    (((Ideal.Quotient.mkₐ FX Q).comp dehom).toLinearMap)
structure CurveProbe (Q : Ideal JetRing) where
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
  offset : ℤ
  threshold : ℕ
  hilbert : ∀ h t s, threshold ≤ h → threshold ≤ t → threshold ≤ s →
    (Module.finrank FX (gradedPiece Q (nefDegree h t s)) : ℤ) =
      (h*fiber + t*tangent + s*seed : ℕ) + offset
def markRoot (J : Input) (γ : K) : Equation →+* FX :=
  eval₂RingHom (graphEval (J.model.label γ)) (atX (J.family.scalar γ))
def markPoint (J : Input) (γ : K) : JetRing →ₐ[FX] FX where
  toRingHom := eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ)))
  commutes' a := by
    change (eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ))))
      (Polynomial.C (Polynomial.C (MvPolynomial.C a))) = a
    simp [markRoot, graphEval]
def tangentEquation (f : Equation) : JetRing :=
  Polynomial.C (MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten f))) +
    Polynomial.X * Polynomial.C f.derivative
def rootIdeal {J : Input} {B : ResidueLift J} (D : Factors J B) : Ideal JetRing :=
  Ideal.span {Polynomial.C D.proper}
def residueInJet {J : Input} (B : ResidueLift J) : JetRing :=
  Polynomial.C (Polynomial.C (P1_7_8.liftSeeds B.denominator))
def openFactor (J : Input) (B : ResidueLift J) : JetRing :=
  residueInJet B * Polynomial.C J.f.derivative
def saturate (Q : Ideal JetRing) (g : JetRing) : Ideal JetRing where
  carrier := {f | ∃ n : ℕ, g^n * f ∈ Q}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f h ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m+n, ?_⟩
    rw [mul_add, pow_add]
    have hf : g^m * g^n * f = g^n * (g^m * f) := by ring
    have hh : g^m * g^n * h = g^m * (g^n * h) := by ring
    rw [hf, hh]
    exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
  smul_mem' := by
    rintro a f ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change g^n * (a * f) ∈ Q
    rw [show g^n * (a*f) = a * (g^n*f) by ring]
    exact Q.mul_mem_left _ hn
def graphIdeal (J : Input) (B : ResidueLift J) (D : Factors J B) : Ideal JetRing :=
  saturate (Ideal.span {Polynomial.C D.proper, tangentEquation J.f}) (openFactor J B)
structure TangentSection (J : Input) {B : ResidueLift J} (D : Factors J B) where
  section_ : RelativeSection (rootIdeal D) (J.e, 1, J.v)
  affine_eq : section_.affine = tangentEquation J.f
def jetDegree (J : Input) (r : ℕ) : Degree :=
  nefDegree (1 + (J.e-3)*r) r (r*J.v + 2*J.w)
def jetDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  residueInJet B * Polynomial.C J.f.derivative ^ (r-1)
def oldDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (P1_7_8.quotientDenominator J B r))
def oldNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (P1_7_8.quotientNumerator J B r))
structure TaylorSections (J : Input) (B : ResidueLift J) (D : Factors J B) (r : ℕ) where
  denominator : RelativeSection (graphIdeal J B D) (jetDegree J r)
  numerator : Fin (r+1) → RelativeSection (graphIdeal J B D) (jetDegree J r)
  den_eq : denominator.affine = jetDenominator J B r
  agrees : ∀ j : Fin (r+1),
    oldDenominator J B j.val * (numerator j).affine -
      oldNumerator J B j.val * denominator.affine ∈ graphIdeal J B D
structure CurveMarks (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime : Ideal JetRing
  isPrime : prime.IsPrime
  onGraph : graphIdeal J B D ≤ prime
  onCutoff : Polynomial.C (P1_7_8.cutoff J B) ∈ prime
  regular : openFactor J B ∉ prime
  marks : Finset K
  sub : marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker (markPoint J γ).toRingHom
structure CurveSlice (J : Input) (B : ResidueLift J) (D : Factors J B)
    extends CurveMarks J B D where
  probe : CurveProbe prime
  positive_seed : 0 < probe.seed
open scoped BigOperators
structure MixedCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count : ℕ
  curves : Fin count → CurveSlice J B D
  covers : ∀ γ ∈ J.marks, P1_7_8.rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).probe.fiber ≤
    J.v*P1_7_8.cutSeed J + J.v^2*P1_7_8.cutVelocity J
  tangent : ∑ j, (curves j).probe.tangent ≤
    2*J.e*J.v*P1_7_8.cutSeed J + J.v^2*P1_7_8.cutOrdinate J
  seed : ∑ j, (curves j).probe.seed ≤
    J.e*P1_7_8.cutSeed J + J.v*((2*J.e-2)*P1_7_8.cutVelocity J + P1_7_8.cutOrdinate J)
structure NodeSections {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C : CurveMarks J B D) where
  persistent : Finset I
  hits : ∀ γ ∈ C.marks, ∀ x ∈ persistent,
    (J.family.scalar γ).eval (node x) = J.model.word x
  cuts : ∀ x ∉ persistent,
    ∃ S : RelativeSection C.prime (jetDegree J (J.ell - persistent.card)),
      S.affine ∉ C.prime ∧
      ∀ γ ∈ C.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
        markPoint J γ S.affine = 0
end
end P1_7_8_3
end
