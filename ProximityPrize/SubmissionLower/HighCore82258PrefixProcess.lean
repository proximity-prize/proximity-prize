import ProximityPrize.SubmissionLower.HighCore82258PrefixHelpers
import Mathlib.Algebra.Order.Sub.Prod
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.UpperBranch3
import ProximityPrize.SubmissionLower.GoldBranch4
import ProximityPrize.SubmissionLower.HighCore82258ScheduleData

-- merged module HighCore82258UpperGeometry
section Merged_HighCore82258UpperGeometry
set_option Elab.async false
set_option autoImplicit true
section
namespace HighCore82258Upper
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P1 (K I node )
open HighCore82258 (agreement)
open K1_14_6 (occupancy)
structure FixedWord (w : I → K) (T : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ γ ∈ T, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
open P0_10 (incidence_arithmetic)
end
end HighCore82258Upper
end
section
set_option autoImplicit false
namespace HighCore82258Upper
noncomputable section
open Polynomial Finset
open P1 (K I Words p node  blockLength)
open HighCore82258 (agreement)
open FrontCore82258 (AnchorModel AnchoredFamily AdjacentChart)
open P1_7 (Reduced regularRoot degreeAt quotientOrder singularDegree)
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
end HighCore82258Upper
end
section
set_option autoImplicit false
namespace HighCore82258Upper
noncomputable section
open P1 ( blockLength)
open HighCore82258 (agreement)
open P1_7 (degreeAt quotientOrder     ceilRatio )
end
end HighCore82258Upper
end
section
set_option autoImplicit false
namespace HighCore82258Upper
noncomputable section
open Polynomial Finset
open P1 (K I  blockLength node p)
open HighCore82258 (agreement)
open P1_7 (degreeAt     )
open K1_14 (Equation Seeds graphEval)
open K1_14_4 (seedDegree)
open scoped BigOperators
theorem fixed_word (J : Input) {U : Finset K} (hU : U ⊆ J.marks) :
    FixedWord J.model.word U J.family.scalar (degreeAt J.hi) := by
  have hsub := hU.trans J.marks_sub
  refine ⟨J.family.distinct.mono hsub, ?_, ?_⟩
  · intro γ hγ
    rcases (J.family.mark γ (hsub hγ)).scalar_degree with hz | hd
    · simp [hz]
    · have hh := J.upper
      change ((J.family.scalar γ).natDegree : ℤ) ≤ 131072 - 1 + J.model.overhead at hd
      change (J.family.scalar γ).natDegree ≤ 131071 + J.hi
      omega
  · intro γ hγ
    let mark := J.family.mark γ (hsub hγ)
    exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
end
end HighCore82258Upper
end
section
set_option autoImplicit false
namespace HighCore82258Upper
noncomputable section
open P1_7 (degreeAt quotientOrder   )
open scoped BigOperators
end
end HighCore82258Upper
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3
noncomputable section
open P1 (K I node)
open HighCore82258Upper (Input ResidueLift Factors)
open K1_14 (FX Equation Seeds atX graphEval seedEmbedding)
open K1_14_6_1 (Dx partialX flatten)
open Polynomial (eval₂RingHom)
abbrev JetRing := Polynomial Equation
instance jetCommRing : CommRing JetRing := @AddMonoidAlgebra.commRing Equation ℕ inferInstance _
abbrev Degree := ℕ × ℕ × ℕ
def nefDegree (h t s : ℕ) : Degree := (h + 2*t, t, s)
abbrev CoxVar := Fin 2 ⊕ (Fin 2 ⊕ Fin 3)
abbrev Cox := MvPolynomial CoxVar FX
def h₀ : CoxVar := .inl 0
def h₁ : CoxVar := .inl 1
def v₀ : CoxVar := .inr (.inl 0)
def v₁ : CoxVar := .inr (.inl 1)
def tᵢ (i : Fin 3) : CoxVar := .inr (.inr i)
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
  Polynomial.C (Polynomial.C (HighCore82258Upper.liftSeeds B.denominator))
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
    (MvPolynomial.optionEquivLeft FX (Fin 2) (HighCore82258Upper.quotientDenominator J B r))
def oldNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (HighCore82258Upper.quotientNumerator J B r))
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
  onCutoff : Polynomial.C (HighCore82258Upper.cutoff J B) ∈ prime
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
  covers : ∀ γ ∈ J.marks, HighCore82258Upper.rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).probe.fiber ≤
    J.v*HighCore82258Upper.cutSeed J + J.v^2*HighCore82258Upper.cutVelocity J
  tangent : ∑ j, (curves j).probe.tangent ≤
    2*J.e*J.v*HighCore82258Upper.cutSeed J + J.v^2*HighCore82258Upper.cutOrdinate J
  seed : ∑ j, (curves j).probe.seed ≤
    J.e*HighCore82258Upper.cutSeed J + J.v*((2*J.e-2)*HighCore82258Upper.cutVelocity J + HighCore82258Upper.cutOrdinate J)
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
end HighCore82258Upper_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3
noncomputable section
open HighCore82258Upper (Input ResidueLift Factors)
open K1_14 (FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten partialX separant  )
open MvPolynomial
open scoped BigOperators
local notation "cx" => MvPolynomial.X
local notation "unwrap" => MvPolynomial.optionEquivLeft FX (Fin 2)
def rootInJet : Biform →ₐ[FX] JetRing :=
  (Polynomial.CAlgHom : Equation →ₐ[FX] JetRing).comp (unwrap).toAlgHom
end
end HighCore82258Upper_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3
noncomputable section
open K1_14 (FX)
open P1 (K)
open MvPolynomial
open scoped BigOperators
theorem weight_coordinates (m : CoxVar →₀ ℕ) :
    Finsupp.weight coxWeight m =
      (m h₀ + m h₁ + 2 * m v₁, m v₀ + m v₁, m (tᵢ 0) + m (tᵢ 1) + m (tᵢ 2)) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_three]
  simp [coxWeight, h₀, h₁, v₀, v₁, tᵢ, Prod.mk_add_mk, Prod.smul_mk,
    Nat.mul_comm, Nat.add_assoc]
private theorem cox_piece_finite (d : Degree) :
    Module.Finite FX (weightedHomogeneousSubmodule FX coxWeight d) := by
  have hle : weightedHomogeneousSubmodule FX coxWeight d ≤
      restrictTotalDegree CoxVar FX (d.1 + d.2.1 + d.2.2) := by
    intro p hp
    apply (mem_restrictTotalDegree _ _ _).mpr
    apply Finset.sup_le
    intro m hm
    have h := hp (mem_support_iff.mp hm)
    rw [weight_coordinates] at h
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_three]
    change m h₀ + m h₁ + (m v₀ + m v₁ + (m (tᵢ 0) + m (tᵢ 1) + m (tᵢ 2))) ≤ _
    rw [← h]
    change _ ≤ (m h₀ + m h₁ + 2*m v₁) + (m v₀ + m v₁) +
      (m (tᵢ 0) + m (tᵢ 1) + m (tᵢ 2))
    omega
  exact Submodule.finiteDimensional_of_le hle
instance gradedPiece_finite (Q : Ideal JetRing) (d : Degree) :
    Module.Finite FX (gradedPiece Q d) := by
  have := cox_piece_finite d
  unfold gradedPiece
  infer_instance
end
end HighCore82258Upper_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3
noncomputable section
open P1 (K I node)
open HighCore82258Upper (Input ResidueLift Factors)
open K1_14 (FX Equation Seeds seedEmbedding)
open MvPolynomial (optionEquivLeft)
open Polynomial (eval₂RingHom)
end
end HighCore82258Upper_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1
noncomputable section
open HighCore82258Upper (Input)
open HighCore82258Upper_3 (JetRing Degree Cox coxWeight dehom ordinate jetDegree RelativeSection)
open K1_14 (FX Equation)
open K1_14_6_1 (flatten partialX)
abbrev velocity : JetRing := Polynomial.X
def coefficientDerivative (f : Equation) : Equation :=
  MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten f))
def jetCoeffDerivative (δ : Equation → Equation) (P : JetRing) : JetRing :=
  P.sum fun k q => Polynomial.monomial k (δ q)
abbrev jetSeparant (f : Equation) : JetRing := Polynomial.C f.derivative
def secondAlongVelocity (f : Equation) : JetRing :=
  Polynomial.C (coefficientDerivative (coefficientDerivative f)) +
    2 * velocity * Polynomial.C (coefficientDerivative f.derivative) +
    velocity ^ 2 * Polynomial.C f.derivative.derivative
def velocityNumerator (f : Equation) : ℕ → JetRing
  | 0 => velocity
  | k+1 =>
    let N := velocityNumerator f k
    jetSeparant f * (jetCoeffDerivative coefficientDerivative N +
      velocity * jetCoeffDerivative Polynomial.derivative N) -
    secondAlongVelocity f * N.derivative -
    (k : JetRing) *
      (Polynomial.C (coefficientDerivative f.derivative) +
        velocity * Polynomial.C f.derivative.derivative) * N
end
end HighCore82258Upper_3_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1
noncomputable section
open HighCore82258Upper_3 (JetRing Degree Cox coxWeight dehom ordinate
  RelativeSection h₀ h₁ v₀ tᵢ affineCoord)
open K1_14 (FX)
open MvPolynomial (IsWeightedHomogeneous isWeightedHomogeneous_zero
  isWeightedHomogeneous_X)
open scoped BigOperators
local notation "H" => ((1,0,0) : Degree)
local notation "cx" => MvPolynomial.X
end
end HighCore82258Upper_3_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1
noncomputable section
open HighCore82258Upper (Input ResidueLift Factors SeedConstants seedBiform liftTaylor)
open HighCore82258Upper_3 (JetRing Degree Cox coxWeight dehom ordinate rootInJet graphIdeal
    jetDegree residueInJet)
open K1_14 (FX Equation Seeds SeedBound)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant  )
open MvPolynomial (mem_restrictBidegree optionEquivLeft)
open scoped BigOperators
theorem embed_separant (f : Equation) :
    rootInJet (separant (flatten f)) = jetSeparant f := by
  simp only [separant, rootInJet, AlgHom.coe_comp, Function.comp_apply,
    AlgEquiv.coe_toAlgHom, MvPolynomial.optionEquivLeft_pderiv_none,
    AlgEquiv.apply_symm_apply]
  rfl
end
end HighCore82258Upper_3_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1
noncomputable section
open K1_14 (FX Seeds Equation SeedBound)
open K1_14_6_1 (flatten partialX )
open HighCore82258Upper (Input)
open HighCore82258Upper_3 (JetRing Cox Degree coxWeight dehom v₀ v₁ affineCoord
  rootInJet )
open MvPolynomial (mem_restrictBidegree isWeightedHomogeneous_X)
open scoped BigOperators
end
end HighCore82258Upper_3_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1
noncomputable section
open HighCore82258Upper (Input ResidueLift Factors liftTaylor inverseBlockCoeff ordinateTaylorNum)
open HighCore82258Upper_3 (JetRing Degree rootInJet ordinate graphIdeal jetDegree jetDenominator
  oldNumerator oldDenominator residueInJet TaylorSections RelativeSection)
open K1_14 (FX)
open K1_14_6_1 (flatten separant cleared)
open Finset (range)
open scoped BigOperators
end
end HighCore82258Upper_3_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1_2
noncomputable section
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3 (JetRing ordinate graphIdeal openFactor)
open HighCore82258Upper_3_1 (velocity jetSeparant coefficientDerivative jetCoeffDerivative
  secondAlongVelocity)
open K1_14 (Equation Seeds)
open Polynomial (eval₂RingHom)
abbrev Graph (J : Input) (B : ResidueLift J) (D : Factors J B) :=
  JetRing ⧸ graphIdeal J B D
def overlapFactor (J : Input) (B : ResidueLift J) (D : Factors J B) : Graph J B D :=
  Ideal.Quotient.mk _ (ordinate * openFactor J B)
abbrev Overlap (J : Input) (B : ResidueLift J) (D : Factors J B) :=
  Localization.Away (overlapFactor J B D)
def finite (J : Input) (B : ResidueLift J) (D : Factors J B) : JetRing →+* Overlap J B D :=
  (algebraMap (Graph J B D) (Overlap J B D)).comp (Ideal.Quotient.mk _)
def reciprocal (J : Input) (B : ResidueLift J) (D : Factors J B) : Overlap J B D :=
  finite J B D (openFactor J B) * IsLocalization.Away.invSelf (overlapFactor J B D)
def seedMap {R : Type*} [CommRing R] (φ : JetRing →+* R) : Seeds →+* R :=
  (φ.comp Polynomial.C).comp Polynomial.C
def inverseEval {R : Type*} [CommRing R] (φ : JetRing →+* R) (z : R) : JetRing →+* R :=
  eval₂RingHom (eval₂RingHom (seedMap φ) z) (-(φ velocity * z^2))
abbrev inverse (J : Input) (B : ResidueLift J) (D : Factors J B) :
    JetRing →+* Overlap J B D :=
  inverseEval (finite J B D) (reciprocal J B D)
def sepAlong (f : Equation) : JetRing :=
  Polynomial.C (coefficientDerivative f.derivative) +
    velocity * Polynomial.C f.derivative.derivative
def clearedAction (f : Equation) (N : JetRing) : JetRing :=
  jetSeparant f * (jetCoeffDerivative coefficientDerivative N +
    velocity * jetCoeffDerivative Polynomial.derivative N) -
  secondAlongVelocity f * N.derivative
abbrev ChartDerivation (R : Type*) [CommRing R] := Derivation ℤ R R
structure ChartFlow {R : Type*} [CommRing R] (f : Equation) (ev : JetRing →+* R)
    (δ : ChartDerivation R) : Prop where
  root : δ (ev ordinate) = ev velocity
  sep : δ (ev (jetSeparant f)) = ev (sepAlong f)
  action : ∀ N, ev (jetSeparant f) * δ (ev N) = ev (clearedAction f N)
end
end HighCore82258Upper_3_1_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1_2
noncomputable section
open HighCore82258Upper_3 (JetRing Degree Cox coxWeight dehom ordinate v₀ v₁ h₁ affineCoord
  rootInJet  graphIdeal openFactor)
open HighCore82258Upper_3_1 (velocity )
open HighCore82258Upper (Input ResidueLift Factors)
open K1_14 (FX Equation SeedBound)
open K1_14_6_1 (flatten)
open scoped BigOperators
end
end HighCore82258Upper_3_1_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1_2
noncomputable section
open HighCore82258Upper_3 (JetRing ordinate)
open HighCore82258Upper_3_1 (velocity jetSeparant coefficientDerivative jetCoeffDerivative
  velocityNumerator secondAlongVelocity)
open K1_14 (Equation SeedBound)
end
end HighCore82258Upper_3_1_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1_2
noncomputable section
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3 (JetRing ordinate dehom)
open HighCore82258Upper_3_1 (jetSeparant   velocityNumerator)
open K1_14 (FX)
end
end HighCore82258Upper_3_1_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_1_1
noncomputable section
open K1_14 (FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx Dx_mul coeff_partialX flatten partialX separant tangent cleared)
open HighCore82258Upper_3 (JetRing rootInJet tangentEquation graphIdeal )
open HighCore82258Upper_3_1 (jetSeparant coefficientDerivative jetCoeffDerivative velocity
  secondAlongVelocity velocityNumerator embed_separant)
local notation "unwrap" => MvPolynomial.optionEquivLeft FX (Fin 2)
theorem dx_nat (n : ℕ) : Dx (n : FX) = 0 := by
  have h : Dx 1 = 0 := by
    have h₁ := Dx_mul 1 1
    simp only [mul_one, one_mul] at h₁
    exact add_left_cancel (h₁.symm.trans (add_zero _).symm)
  rw [← nsmul_one, map_nsmul, h, nsmul_zero]
private theorem partial_mul (p q : Biform) :
    partialX (p * q) = p * partialX q + partialX p * q := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [coeff_partialX, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_mul, map_sum, Dx_mul, Finset.sum_add_distrib]
theorem coeffDiff_mul (p q : Equation) :
    coefficientDerivative (p * q) =
      p * coefficientDerivative q + coefficientDerivative p * q := by
  unfold coefficientDerivative
  rw [show flatten (p * q) = flatten p * flatten q from map_mul _ _ _,
    partial_mul, map_add, map_mul, map_mul]
  simp only [AlgEquiv.apply_symm_apply]
private theorem coeffDiff_zero : coefficientDerivative 0 = 0 := by
  simp [coefficientDerivative]
theorem coeffDiff_add (p q : Equation) :
    coefficientDerivative (p + q) = coefficientDerivative p + coefficientDerivative q := by
  simp only [coefficientDerivative, map_add]
theorem coeff_coeffDiff (p : Equation) (i : ℕ) (m : Fin 2 →₀ ℕ) :
    ((coefficientDerivative p).coeff i).coeff m = Dx ((p.coeff i).coeff m) := by
  rw [coefficientDerivative, MvPolynomial.optionEquivLeft_coeff_coeff, coeff_partialX,
    ← MvPolynomial.optionEquivLeft_coeff_coeff FX, AlgEquiv.apply_symm_apply]
theorem coeffDiff_one : coefficientDerivative 1 = 0 := by
  classical
  have h : Dx 1 = 0 := by simpa only [Nat.cast_one] using dx_nat 1
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  by_cases hi : i = 0 <;> by_cases hm : (0 : Fin 2 →₀ ℕ) = m <;>
    simp [coeff_coeffDiff, Polynomial.coeff_one, MvPolynomial.coeff_one, hi, hm, h]
theorem coeffDiff_derivative (p : Equation) :
    coefficientDerivative p.derivative = (coefficientDerivative p).derivative := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  have h (q : Seeds) : (q * ((i : Seeds)+1)).coeff m = (↑(i+1 : ℕ) : FX) * q.coeff m := by
    rw [show (i : Seeds)+1 = (↑(i+1 : ℕ) : Seeds) from (Nat.cast_succ i).symm,
      ← map_natCast (MvPolynomial.C : FX →+* Seeds), mul_comm, MvPolynomial.coeff_C_mul]
  simp only [coeff_coeffDiff, Polynomial.coeff_derivative, h, Dx_mul, dx_nat, zero_mul, add_zero]
theorem coeff_lift {d : Equation → Equation} (h0 : d 0 = 0) (p : JetRing) (i : ℕ) :
    (jetCoeffDerivative d p).coeff i = d (p.coeff i) := by
  rw [jetCoeffDerivative, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · exact Polynomial.coeff_monomial_same _ _
  · exact fun j _ hj => Polynomial.coeff_monomial_of_ne _ hj.symm
  · intro hi
    rw [Polynomial.notMem_support_iff.mp hi, h0, Polynomial.monomial_zero_right,
      Polynomial.coeff_zero]
private theorem lift_zero {d : Equation → Equation} (h0 : d 0 = 0) :
    jetCoeffDerivative d 0 = 0 := by
  ext i
  simp only [coeff_lift h0, Polynomial.coeff_zero, h0]
private theorem lift_add {d : Equation → Equation} (h0 : d 0 = 0)
    (hadd : ∀ a b, d (a + b) = d a + d b) (p q : JetRing) :
    jetCoeffDerivative d (p + q) = jetCoeffDerivative d p + jetCoeffDerivative d q := by
  ext i
  simp only [coeff_lift h0, Polynomial.coeff_add, hadd]
private theorem lift_mul {d : Equation → Equation} (h0 : d 0 = 0)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = a * d b + d a * b) (p q : JetRing) :
    jetCoeffDerivative d (p * q) = p * jetCoeffDerivative d q + jetCoeffDerivative d p * q := by
  let D : Equation →+ Equation := ⟨⟨d, h0⟩, hadd⟩
  have hs {α : Type} (s : Finset α) (g : α → Equation) :
      d (∑ a ∈ s, g a) = ∑ a ∈ s, d (g a) := map_sum D g s
  ext i
  simp only [coeff_lift h0, Polynomial.coeff_add, Polynomial.coeff_mul, hs, hmul,
    Finset.sum_add_distrib]
private theorem lift_C {d : Equation → Equation} (h0 : d 0 = 0) (q : Equation) :
    jetCoeffDerivative d (Polynomial.C q) = Polynomial.C (d q) := by
  ext i
  cases i <;> simp [coeff_lift h0, h0]
private theorem lift_X {d : Equation → Equation} (h0 : d 0 = 0) (h1 : d 1 = 0) :
    jetCoeffDerivative d velocity = 0 := by
  ext i
  by_cases hi : 1 = i <;> simp [velocity, coeff_lift h0, Polynomial.coeff_X, hi, h0, h1]
private def slope (f : Equation) : JetRing :=
  Polynomial.C (coefficientDerivative f.derivative) + velocity * Polynomial.C f.derivative.derivative
def flow (f : Equation) : JetRing →+ JetRing where
  toFun p :=
    jetSeparant f * (jetCoeffDerivative coefficientDerivative p +
      velocity * jetCoeffDerivative Polynomial.derivative p) -
    secondAlongVelocity f * p.derivative
  map_zero' := by
    simp [lift_zero coeffDiff_zero, lift_zero Polynomial.derivative_zero]
  map_add' p q := by
    simp only [lift_add coeffDiff_zero coeffDiff_add,
      lift_add Polynomial.derivative_zero (fun a b : Equation => map_add Polynomial.derivative a b),
      map_add]
    ring
theorem flow_mul (f : Equation) (p q : JetRing) :
    flow f (p * q) = p * flow f q + flow f p * q := by
  simp only [flow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Polynomial.derivative_mul,
    lift_mul coeffDiff_zero coeffDiff_add coeffDiff_mul,
    lift_mul Polynomial.derivative_zero (fun a b : Equation => map_add Polynomial.derivative a b)
      (fun a b => Polynomial.derivative_mul.trans (add_comm _ _))]
  ring
theorem flow_C (f q : Equation) :
    flow f (Polynomial.C q) =
      jetSeparant f * (Polynomial.C (coefficientDerivative q) + velocity * Polynomial.C q.derivative) := by
  simp [flow, lift_C coeffDiff_zero, lift_C Polynomial.derivative_zero]
theorem flow_X (f : Equation) : flow f velocity = -secondAlongVelocity f := by
  change jetSeparant f * (jetCoeffDerivative coefficientDerivative Polynomial.X +
    velocity * jetCoeffDerivative Polynomial.derivative Polynomial.X) -
    secondAlongVelocity f * Polynomial.derivative Polynomial.X = _
  rw [lift_X coeffDiff_zero coeffDiff_one, lift_X Polynomial.derivative_zero
    Polynomial.derivative_one, Polynomial.derivative_X]
  ring
theorem flow_tangentEquation (f : Equation) : flow f (tangentEquation f) = 0 := by
  change flow f (Polynomial.C (coefficientDerivative f) + velocity * jetSeparant f) = 0
  rw [map_add, flow_mul, flow_X, flow_C, flow_C, ← coeffDiff_derivative]
  unfold secondAlongVelocity
  ring
theorem flow_sep (f : Equation) :
    flow f (jetSeparant f) = jetSeparant f * slope f :=
  flow_C f f.derivative
private theorem flow_sep_pow (f : Equation) (k : ℕ) :
    flow f (jetSeparant f ^ k) = (k : JetRing) * jetSeparant f ^ k * slope f := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, zero_mul, ← Polynomial.C_1, flow_C,
      coeffDiff_one, Polynomial.derivative_one]
    simp
  | succ k ih =>
    rw [pow_succ, flow_mul, flow_sep, ih, Nat.cast_succ]
    ring
def tangentIdeal (f : Equation) : Ideal JetRing := Ideal.span {tangentEquation f}
private abbrev image (f : Equation) := Ideal.Quotient.mk (tangentIdeal f)
private theorem flow_congr (f : Equation) {p q : JetRing}
    (h : image f p = image f q) : image f (flow f p) = image f (flow f q) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h)
  apply Ideal.Quotient.eq.mpr
  rw [← map_sub, ← ha, flow_mul, flow_tangentEquation, mul_zero, zero_add]
  exact Ideal.mem_span_singleton'.mpr ⟨flow f a, rfl⟩
private theorem tangent_zero (f : Equation) : image f (tangentEquation f) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
private theorem rootInJet_apply (p : Biform) : rootInJet p = Polynomial.C (unwrap p) := rfl
private theorem tangent_image (f : Equation) (p : Biform) :
    image f (rootInJet (tangent (flatten f) p)) = image f (flow f (rootInJet p)) := by
  have hx (q : Biform) : rootInJet (partialX q) =
      Polynomial.C (coefficientDerivative (unwrap q)) := by
    simp only [rootInJet_apply, coefficientDerivative, AlgEquiv.symm_apply_apply]
  have hy : rootInJet (MvPolynomial.pderiv none p) = Polynomial.C (unwrap p).derivative := by
    rw [rootInJet_apply, MvPolynomial.optionEquivLeft_pderiv_none]
  have ht : rootInJet (tangent (flatten f) p) =
      flow f (rootInJet p) - tangentEquation f * rootInJet (MvPolynomial.pderiv none p) := by
    rw [tangent, map_sub, map_mul, map_mul, embed_separant, hx, hx, hy,
      AlgEquiv.apply_symm_apply, rootInJet_apply, flow_C]
    change _ = _ - (Polynomial.C (coefficientDerivative f) + velocity * jetSeparant f) * _
    ring
  rw [ht, map_sub, map_mul, tangent_zero, zero_mul, sub_zero]
private abbrev oldNum (f : Equation) (k : ℕ) : JetRing :=
  rootInJet (cleared (flatten f) k)
private theorem old_next (f : Equation) (k : ℕ) :
    image f (oldNum f (k+1)) =
      image f (jetSeparant f) * image f (flow f (oldNum f k)) -
      (↑(2*k+1 : ℕ) : JetRing ⧸ tangentIdeal f) *
        image f (jetSeparant f * slope f) * image f (oldNum f k) := by
  simp only [oldNum, cleared, map_sub, map_mul, embed_separant, tangent_image]
  rw [flow_sep, map_mul]
  have h : rootInJet (MvPolynomial.C (↑(2*k+1 : ℕ) : FX)) = (↑(2*k+1 : ℕ) : JetRing) :=
    (rootInJet.commutes _).trans (map_natCast (algebraMap FX JetRing) _)
  rw [h, map_natCast]
private theorem velocity_next (f : Equation) (k : ℕ) :
    velocityNumerator f (k+1) =
      flow f (velocityNumerator f k) - (k : JetRing) * slope f * velocityNumerator f k := rfl
set_option maxHeartbeats 800000 in
theorem comparison (f : Equation) (k : ℕ) :
    image f (jetSeparant f ^ (k+1) * velocityNumerator f k) = image f (oldNum f k) := by
  induction k with
  | zero =>
    rw [show velocityNumerator f 0 = velocity from rfl,
      show oldNum f 0 = rootInJet (-partialX (flatten f)) from rfl,
      map_neg, rootInJet_apply, pow_one, mul_comm, map_mul, map_neg]
    have ht := tangent_zero f
    change image f (Polynomial.C (coefficientDerivative f) + velocity * jetSeparant f) = 0 at ht
    rw [map_add, map_mul] at ht
    exact eq_neg_of_add_eq_zero_right ht
  | succ k ih =>
    have hd := flow_congr f ih
    simp only [flow_mul, flow_sep_pow, map_add, map_mul, map_natCast, map_pow] at hd
    simp only [map_mul, map_pow] at ih
    rw [old_next, ← hd, ← ih]
    simp only [velocity_next, map_sub, map_mul, map_pow, map_natCast, Nat.cast_add,
      Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    rw [pow_succ _ (k+1)]
    ring
end
end HighCore82258Upper_3_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HighCore82258Upper_1
noncomputable section
open Polynomial Module
open K1_14 (L)
open HighCore82258Upper (SeedConstants)
open K1_14_1_1 (quotientBasis mulMatrix mulMatrix_entry mulMatrix_specialize mulMatrix_det_ne_zero)
abbrev liftConstants (g : (Polynomial L)) : (Polynomial SeedConstants) := g.map MvPolynomial.C
private lemma eval_constants (z : Fin 2 → L) (g : (Polynomial L)) :
    (liftConstants g).map (MvPolynomial.eval z) = g := by
  have h : (MvPolynomial.eval z).comp MvPolynomial.C = RingHom.id L :=
    RingHom.ext fun c => MvPolynomial.eval_C c
  rw [map_map, h, map_id]
structure BlockContribution (h : ℕ) (b e A B Q : (Polynomial L)) (i : Fin 2) where
  den : SeedConstants
  num : (Polynomial SeedConstants)
  den_ne : den ≠ 0
  den_degree : den.totalDegree ≤ h
  num_degree : ∀ j, (num.coeff j).totalDegree ≤ h
  width : num.natDegree < 2 * h
  other_dvd : liftConstants e ∣ num
  congruence : liftConstants b ∣
    (liftConstants A + C (MvPolynomial.X i) * liftConstants B) * num +
      C (den * MvPolynomial.X i) * liftConstants Q
  regular : ∀ z : Fin 2 → L, IsCoprime (A + C (z i) * B) b →
    MvPolynomial.eval z den ≠ 0
end
end HighCore82258Upper_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HighCore82258Upper_1
noncomputable section
open Polynomial
open P1 (K p)
open K1_14 (L liftPoly)
open HighCore82258Upper (Input SeedConstants blockAt residueData residueDenominator)
end
end HighCore82258Upper_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_2
noncomputable section
open Polynomial
open P1 (K p)
open P1_7 (degreeAt quotientOrder)
open HighCore82258Upper
open K1_14 (L FX liftPoly)
end
end HighCore82258Upper_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_2
noncomputable section
open Polynomial Finset
open P1 (K p)
open P1_7 (degreeAt quotientOrder)
open HighCore82258Upper
open K1_14 (L FX atX liftPoly seedEmbedding)
open K1_14_6 (Biform rootPoint)
open K1_14_6_1 (Dx Dx_mul derivativeAt flatten separant cleared markEval)
open scoped BigOperators
open K1_14_6_1 (rationalJet rationalJet_incl)
end
end HighCore82258Upper_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_2
noncomputable section
open Polynomial Finset UniqueFactorizationMonoid
open K1_14 (Seeds Equation)
open K1_14_4 (seedDegree seedDegree_mul seedDegree_le_iff)
open HighCore82258Upper
open scoped BigOperators
end
end HighCore82258Upper_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_2
end HighCore82258Upper_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2
noncomputable section
open K1_14 (FX)
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3
abbrev HilbertPoly := MvPolynomial (Fin 3) ℚ
structure Budget where
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
end
end HighCore82258Upper_3_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2
noncomputable section
open K1_14 (FX Seeds Equation atX atMark graphEval seedEmbedding)
open P1 (K)
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3
open K1_14_4 (seedDegree seedDegree_le_iff seedDegree_mul)
open K1_14_6_1 (flatten partialX markEval Dx Dx_eval Dx_atX eval_flatten )
open MvPolynomial (optionEquivLeft)
open Polynomial (eval₂RingHom)
end
end HighCore82258Upper_3_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82258Upper_3
open MvPolynomial
open scoped BigOperators
end
end HighCore82258Upper_3_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2
noncomputable section
open HighCore82258Upper_3
open scoped BigOperators
end
end HighCore82258Upper_3_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3
end
end HighCore82258Upper_3_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_1
noncomputable section
open K1_14 (L FX Seeds Equation)
open K1_14_6_1 (partialX flatten)
open HighCore82258Upper (Input ResidueLift Factors SeedField generic liftSeeds constantAbscissa)
open HighCore82258Upper_3
open Polynomial
end
end HighCore82258Upper_3_2_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_2
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3
open scoped Polynomial
end
end HighCore82258Upper_3_2_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_3
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82258Upper_3 HighCore82258Upper_3_2 MvPolynomial
open scoped BigOperators
private def kept : CoxVar → Prop
  | .inl i => i ≠ 0
  | .inr (.inl i) => i ≠ 0
  | .inr (.inr i) => i.val < 2
private def surviving (m : CoxVar →₀ ℕ) : CoxVar →₀ ℕ := by
  classical
  exact m.filter kept
end
end HighCore82258Upper_3_2_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_5
noncomputable section
open HighCore82258Upper_3_2 MvPolynomial
open scoped BigOperators
end
end HighCore82258Upper_3_2_5
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_6
noncomputable section
open K1_14 (FX)
open HighCore82258Upper_3 HighCore82258Upper_3_2 MvPolynomial
open scoped BigOperators
end
end HighCore82258Upper_3_2_6
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_3
noncomputable section
open P1 (I node)
open HighCore82258Upper
open HighCore82258Upper_3
open K1_14 (FX L seedEmbedding)
open scoped BigOperators
end
end HighCore82258Upper_3_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_3
noncomputable section
open HighCore82258Upper_3
open MvPolynomial (IsWeightedHomogeneous)
end
end HighCore82258Upper_3_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_3
noncomputable section
open P1 (I)
open HighCore82258Upper
open HighCore82258Upper_3
open K1_14 (FX Equation SeedBound)
open K1_14_6_1 (  flatten separant )
open MvPolynomial
end
end HighCore82258Upper_3_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_3
noncomputable section
open P1 (K I node)
open HighCore82258Upper
open HighCore82258Upper_3
open K1_14 (FX seedEmbedding)
open scoped BigOperators
end
end HighCore82258Upper_3_3
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5
noncomputable section
open Polynomial
open P1 (K)
open K1_14 (FX Seeds Equation atX graphEval seedEmbedding)
open HighCore82258Upper (Input ResidueLift SeedClosure intoSeedClosure center reconstructed genericRoots rootOn)
def embedFX : FX →+* SeedClosure := intoSeedClosure.comp MvPolynomial.C
def evalRoot (y : SeedClosure) : Equation →+* SeedClosure := eval₂RingHom intoSeedClosure y
def evalMark (J : Input) (γ : K) : Equation →+* FX :=
  eval₂RingHom (graphEval (J.model.label γ)) (atX (J.family.scalar γ))
structure RegularValues (J : Input) (B : ResidueLift J) (q : Equation) where
  denominator : Equation
  numerator : K → Equation
  generic_value : ∀ y ∈ genericRoots q, ∀ x : K,
    evalRoot y (numerator x) = evalRoot y denominator *
      (reconstructed J B y).eval (embedFX (seedEmbedding x))
  marked_value : ∀ γ ∈ J.marks, rootOn J q γ →
    evalMark J γ denominator ≠ 0 ∧ ∀ x : K,
      evalMark J γ (numerator x) = evalMark J γ denominator *
        seedEmbedding ((J.family.scalar γ).eval x)
structure BoundedProduct (J : Input) (B : ResidueLift J) (q : Equation) where
  numerator : Polynomial (Polynomial Seeds)
  degree : ∀ i j, ((numerator.coeff i).coeff j).totalDegree ≤ K1_14_4.seedDegree q
  identity : numerator.map (Polynomial.mapRingHom intoSeedClosure) =
    C (C (intoSeedClosure q.leadingCoeff)) *
      ∏ y ∈ genericRoots q, (Polynomial.X - C (reconstructed J B y))
end
end HighCore82258Upper_5
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5
noncomputable section
open Polynomial
open P1 (K I node)
open K1_14 (FX Seeds Equation seedEmbedding graphEval)
open P1_7 (Reduced)
open HighCore82258Upper (Input ResidueLift SeedField SeedClosure intoSeedClosure reconstructed genericRoots
  generic rootOn )
end
end HighCore82258Upper_5
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5
noncomputable section
open Polynomial
open K1_14 (L FX Seeds Equation)
open K1_14_6 (Biform)
open P1_7 (Reduced)
open HighCore82258Upper (Input ResidueLift SeedConstants SeedClosure intoSeedClosure center reconstructed
  genericRoots generic liftConstantSeeds seedBiform liftSeeds constantAbscissa liftTaylor
  inverseBlockCoeff ordinateTaylorNum quotientNumerator quotientDenominator DifferentialProduct)
end
end HighCore82258Upper_5
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5
noncomputable section
open Polynomial
open P1 (K p)
open K1_14 (FX L Seeds atX liftPoly seedEmbedding)
open K1_14_6_1 (Dx Dx_atX Dx_mul Dx_pow)
open HighCore82258Upper (center)
end
end HighCore82258Upper_5
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5
noncomputable section
open Polynomial
open K1_14 (Seeds Equation)
open K1_14_4 (seedDegree seedDegree_le_iff)
open P1_7 (Reduced degreeAt)
open HighCore82258Upper (Input ResidueLift Factors DifferentialProduct SeedClosure intoSeedClosure center)
end
end HighCore82258Upper_5
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5_1
noncomputable section
open Polynomial Finset
open P1 (K)
open K1_14 (L FX Equation seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (separant flatten)
open HighCore82258Upper (Input ResidueLift center constantAbscissa SeedConstants seedBiform
  quotientNumerator quotientDenominator)
end
end HighCore82258Upper_5_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5_1
noncomputable section
open Polynomial Finset
open P1 (K p)
open K1_14 (L FX atX liftPoly seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open HighCore82258Upper (Input ResidueLift center constantAbscissa SeedConstants seedBiform
  evalSeedConstants liftTaylor inverseBlockCoeff quotientNumerator)
end
end HighCore82258Upper_5_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_3_1
noncomputable section
open Polynomial
open P1 (K p node)
open K1_14 (L FX Equation atMark atX liftPoly seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten separant markEval)
open HighCore82258Upper HighCore82258Upper_3 HighCore82258Upper_3_3
open scoped BigOperators
end
end HighCore82258Upper_3_3_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_3_2
noncomputable section
open P1 (K I node)
open HighCore82258Upper (Input center constantAbscissa)
open HighCore82258Upper_3_3
open K1_14 (L FX seedEmbedding)
open ProximityPrize.Benchmark
open scoped BigOperators
end
end HighCore82258Upper_3_3_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4
noncomputable section
open Polynomial Finset
open HighCore82258Upper
open K1_14 (L FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx)
abbrev seedMap : Seeds →+* SeedField := algebraMap Seeds SeedField
def splitting (q : Equation) : IntermediateField SeedField SeedClosure :=
  IntermediateField.adjoin SeedField ((generic q).rootSet SeedClosure)
abbrev SplitField (q : Equation) := ↥(splitting q)
def geomRoots (q : Equation) : Finset (SplitField q) := by
  classical
  exact ((generic q).map (algebraMap SeedField (SplitField q))).roots.toFinset
def coeffDx : Seeds →+ Seeds :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom Dx).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
abbrev splitMap (q : Equation) : Seeds →+* SplitField q :=
  (algebraMap SeedField (SplitField q)).comp seedMap
def origin {F : Type} [Field F] (ι : Seeds →+* F) : F :=
  ι (MvPolynomial.C center)
structure DifferentialData (q : Equation) where
  base : Derivation ℤ SeedField SeedField
  split : Derivation ℤ (SplitField q) (SplitField q)
  extends_seed : ∀ s : Seeds, base (seedMap s) = seedMap (coeffDx s)
  extends_base : ∀ a : SeedField,
    split (algebraMap SeedField (SplitField q) a) =
      algebraMap SeedField (SplitField q) (base a)
  center_one : split (origin (splitMap q)) = 1
  frozen : ∀ s : SeedConstants, split (splitMap q (liftSeeds s)) = 0
end
end HighCore82258Upper_4
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4
noncomputable section
open Polynomial Finset
open HighCore82258Upper
open K1_14 (Seeds Equation)
def coeffDeriv {F : Type} [CommRing F] (δ : Derivation ℤ F F) :
    Derivation ℤ (Polynomial F) (Polynomial F) :=
  letI : Differential F := ⟨δ⟩
  Differential.mapCoeffs
@[simp] theorem coeff_coeffDeriv {F : Type} [CommRing F] (δ : Derivation ℤ F F)
    (P : (Polynomial F)) (i : ℕ) : (coeffDeriv δ P).coeff i = δ (P.coeff i) := rfl
@[simp] theorem coeffDeriv_C {F : Type} [CommRing F] (δ : Derivation ℤ F F)
    (x : F) : coeffDeriv δ (C x) = C (δ x) := by
  let : Differential F := ⟨δ⟩
  exact Differential.mapCoeffs_C x
@[simp] theorem coeffDeriv_X {F : Type} [CommRing F] (δ : Derivation ℤ F F) :
    coeffDeriv δ (Polynomial.X : (Polynomial F)) = 0 := by
  let : Differential F := ⟨δ⟩
  exact Differential.mapCoeffs_X (A := F)
end
end HighCore82258Upper_4
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4
noncomputable section
open Polynomial Finset
open HighCore82258Upper
open K1_14 (Seeds Equation)
instance splittingField (q : Equation) : (generic q).IsSplittingField SeedField (SplitField q) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
end
end HighCore82258Upper_4
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4
noncomputable section
open Polynomial
open HighCore82258Upper
open K1_14 (Seeds Equation seedEmbedding)
open K1_14_6_1 (Dx)
end
end HighCore82258Upper_4
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4
noncomputable section
open Polynomial
open HighCore82258Upper
open K1_14 (Equation)
end
end HighCore82258Upper_4
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4_1
noncomputable section
open Polynomial
open K1_14 (L FX Seeds Equation)
open K1_14_6_1 (Dx Dx_mul)
open HighCore82258Upper (SeedConstants SeedField center constantAbscissa liftSeeds generic)
open HighCore82258Upper_4 (SplitField coeffDx  seedMap)
open K1_14_6_1 (rationalJet rationalJet_incl)
open K1_13_6_3_1_2 (lift_derivation)
end
end HighCore82258Upper_4_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4_2
noncomputable section
open Polynomial Finset HighCore82258Upper HighCore82258Upper_4
open K1_14 (FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten separant partialX cleared tangent)
open K1_14_6_1 (partialX_C partialX_mul_X)
end
end HighCore82258Upper_4_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4_2
noncomputable section
open Polynomial Finset HighCore82258Upper HighCore82258Upper_4
open K1_14 (L FX Equation)
open K1_14_6_1 (Dx)
def divided {F : Type} [Field F] (δ : Derivation ℤ F F) (a : F) (i : ℕ) : F :=
  (i.factorial : F)⁻¹ * (δ^[i]) a
end
end HighCore82258Upper_4_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_4_2
noncomputable section
open Polynomial Finset HighCore82258Upper HighCore82258Upper_4
open K1_14 (L FX)
open K1_14_6_1 (flatten separant)
end
end HighCore82258Upper_4_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5_1
noncomputable section
open Polynomial
open P1 (K)
open K1_14 (L FX Equation seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open HighCore82258Upper (Input ResidueLift Factors SeedField SeedClosure intoSeedClosure center
  constantAbscissa liftSeeds seedBiform liftConstantSeeds genericPoint genericRoots reconstructed)
open HighCore82258Upper_5 (evalRoot evalMark embedFX)
end
end HighCore82258Upper_5_1
end
section
set_option autoImplicit false
namespace HighCore82258Upper_5_2
noncomputable section
open Polynomial
open K1_14 (FX Seeds atX liftPoly seedEmbedding)
open K1_14_6_1 (Dx Dx_mul Dx_atX)
open P1 (K p)
open HighCore82258Upper (center)
open HighCore82258Upper_4 (coeffDx )
end
end HighCore82258Upper_5_2
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_4
noncomputable section
open K1_14 (FX)
open HighCore82258Upper_3
open MvPolynomial
open scoped BigOperators
abbrev Exponent := CoxVar →₀ ℕ
structure Block where
  base : Exponent
  free : Finset CoxVar
end
end HighCore82258Upper_3_2_4
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_4
noncomputable section
open K1_14 (FX)
open HighCore82258Upper_3
open HighCore82258Upper_3_2
open MvPolynomial
open HighCore82258Upper_3 (cox_piece_finite)
end
end HighCore82258Upper_3_2_4
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_4
noncomputable section
open HighCore82258Upper_3
open scoped BigOperators
end
end HighCore82258Upper_3_2_4
end
section
set_option autoImplicit false
namespace HighCore82258Upper_3_2_4
open K1_14 (FX)
open HighCore82258Upper_3 HighCore82258Upper_3_2
open MvPolynomial
end HighCore82258Upper_3_2_4
end

end Merged_HighCore82258UpperGeometry

-- merged module HighCore82258UpperCertificates
section Merged_HighCore82258UpperCertificates

namespace HighCore82258GeometryGoals
end HighCore82258GeometryGoals

set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_1
noncomputable section
open K1_14 (Equation)
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3 (JetRing ordinate openFactor graphIdeal tangentEquation 
  )
open HighCore82258Upper_3_1 (velocity jetSeparant coefficientDerivative)
open HighCore82258Upper_3_1_2
open Polynomial (C)
open TrivSqZeroExt
open scoped BigOperators Ring
open HighCore82258Upper_3_1_1 (flow flow_mul flow_C flow_sep flow_tangentEquation coeffDiff_one coeff_coeffDiff dx_nat)
end
end HighCore82258GeometryCert_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_1
noncomputable section
open K1_14 (Equation Seeds)
open HighCore82258Upper_3 (JetRing ordinate)
open HighCore82258Upper_3_1 (velocity jetSeparant coefficientDerivative secondAlongVelocity)
open HighCore82258Upper_3_1_2
open Polynomial (C eval₂RingHom)
open HighCore82258Upper_3_1_1 (flow flow_mul flow_C flow_X coeffDiff_add coeffDiff_mul coeff_coeffDiff coeffDiff_derivative)
end
end HighCore82258GeometryCert_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2
end HighCore82258GeometryCert_2
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_1
noncomputable section
open K1_14 (FX)
open HighCore82258Upper_3 HighCore82258Upper_3_2_4 MvPolynomial
open scoped BigOperators MonomialOrder
end
end HighCore82258GeometryCert_2_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_2
noncomputable section
open HighCore82258Upper_3 HighCore82258Upper_3_2_4
def rootFree (B : Block) : Finset (Fin 2) :=
  Finset.univ.filter fun i => Sum.inl i ∈ B.free
def seedFree (B : Block) : Finset (Fin 3) :=
  Finset.univ.filter fun i => tᵢ i ∈ B.free
def rv {R : Type} [Semiring R] (r : ℕ) (a b : Prop) [Decidable a] [Decidable b]
    (T H HT HT₂ : R) : R :=
  if r = 0 then 0
  else if a then
    if b then T * (if r = 1 then 1 else HT)
    else if r = 1 then 1 else HT₂
  else if b then if r = 1 then 1 else H
  else 0
def seeds {R : Type} [Semiring R] (r : ℕ) (S S₂ Q : R) : R :=
  if r = 1 then 1 else if r = 2 then S else if r = 3 then Q * S * S₂ else 0
private def velocities (B : Block) (b : ℕ) : Finset ℕ :=
  if v₀ ∈ B.free then (if v₁ ∈ B.free then Finset.range (b+1) else {b})
  else if v₁ ∈ B.free then {0} else ∅
private theorem mem_velocities (B : Block) {b j : ℕ} (hb : 0 < b) :
    j ∈ velocities B b ↔ j ≤ b ∧ (v₀ ∉ B.free → j = 0) ∧
      (v₁ ∉ B.free → b-j = 0) := by
  by_cases h₀' : v₀ ∈ B.free <;> by_cases h₁' : v₁ ∈ B.free <;>
    simp [velocities, h₀', h₁'] <;> omega
private theorem mem_comp {n d : ℕ} {F : Finset (Fin n)} {f : Fin n →₀ ℕ} :
    f ∈ F.finsuppAntidiag d ↔ (∑ i, f i) = d ∧ ∀ i ∉ F, f i = 0 := by
  rw [Finset.mem_finsuppAntidiag', Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun h i hi => Finsupp.notMem_support_iff.mp (fun hm => hi (h hm))
  · intro h i hi
    by_contra hf
    exact (Finsupp.mem_support_iff.mp hi) (h i hf)
private def project {n : ℕ} (m : Exponent) (f : Fin n → CoxVar) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (f i))
private def pack (r : Fin 2 →₀ ℕ) (j b : ℕ) (z : Fin 3 →₀ ℕ) : Exponent :=
  Finsupp.equivFunOnFinite.symm (Sum.elim r (Sum.elim ![j,b-j] z))
private abbrev Increments (B : Block) (d : Degree) :=
  {m : Exponent // (∀ i ∉ B.free, m i = 0) ∧ Finsupp.weight coxWeight m = d}
private def enum (B : Block) (a b c : ℕ) (hb : 0 < b) :
    Increments B (nefDegree a b c) ≃
      (Σ j : velocities B b, (rootFree B).finsuppAntidiag (a+2*j.val)) ×
        (seedFree B).finsuppAntidiag c where
  toFun m := by
    have hz := m.prop.1
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have ha := congrArg Prod.fst hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    have hc := congrArg (fun d : Degree => d.2.2) hw
    change m.val h₀ + m.val h₁ + 2*m.val v₁ = a+2*b at ha
    change m.val v₀ + m.val v₁ = b at hv
    change m.val (tᵢ 0) + m.val (tᵢ 1) + m.val (tᵢ 2) = c at hc
    refine ⟨⟨⟨m.val v₀, (mem_velocities B hb).mpr ⟨by omega, hz _, ?_⟩⟩,
      ⟨project m.val Sum.inl, mem_comp.mpr ⟨?_, ?_⟩⟩⟩,
      ⟨project m.val tᵢ, mem_comp.mpr ⟨?_, ?_⟩⟩⟩
    · intro h
      have := hz v₁ h
      omega
    · rw [Fin.sum_univ_two]
      change m.val h₀ + m.val h₁ = a+2*m.val v₀
      omega
    · exact fun i hi => hz (Sum.inl i) (by simpa [rootFree] using hi)
    · rw [Fin.sum_univ_three]
      exact hc
    · exact fun i hi => hz (tᵢ i) (by simpa [seedFree] using hi)
  invFun p := by
    rcases p with ⟨⟨j, r⟩, z⟩
    have hj := ((mem_velocities B hb).mp j.prop).1
    have hj₀ := ((mem_velocities B hb).mp j.prop).2.1
    have hj₁ := ((mem_velocities B hb).mp j.prop).2.2
    have hr := (mem_comp.mp r.prop).1
    have hrz := (mem_comp.mp r.prop).2
    have hs := (mem_comp.mp z.prop).1
    have hsz := (mem_comp.mp z.prop).2
    rw [Fin.sum_univ_two] at hr
    rw [Fin.sum_univ_three] at hs
    refine ⟨pack r.val j.val b z.val, ?_, ?_⟩
    · intro i hi
      rcases i with i | (i | i)
      · exact hrz i (by simpa [rootFree] using hi)
      · fin_cases i
        · exact hj₀ hi
        · exact hj₁ hi
      · apply hsz i
        intro hz
        unfold seedFree at hz
        exact hi (Finset.mem_filter.mp hz).2
    · rw [weight_coordinates]
      change (r.val 0 + r.val 1 + 2*(b-j.val), j.val+(b-j.val),
        z.val 0+z.val 1+z.val 2) = (a+2*b,b,c)
      rw [hr, hs]
      congr 1
      · omega
      · congr 1
        omega
  left_inv m := by
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    change m.val v₀ + m.val v₁ = b at hv
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rcases i with i | (i | i)
    · rfl
    · fin_cases i
      · rfl
      · change b-m.val v₀ = m.val v₁
        omega
    · rfl
  right_inv p := by
    rcases p with ⟨⟨j,r⟩,z⟩
    apply Prod.ext
    · exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Subtype.ext (Finsupp.ext fun _ => rfl)))
    · exact Subtype.ext (Finsupp.ext fun _ => rfl)
end
end HighCore82258GeometryCert_2_2
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_2
noncomputable section
open HighCore82258Upper_3 HighCore82258Upper_3_2 HighCore82258Upper_3_2_4 MvPolynomial
private def affine (i j : Fin 3) (r b : ℚ) : HilbertPoly :=
  MvPolynomial.X i + C r * MvPolynomial.X j + C b
private def baseDegree (B : Block) : Degree := Finsupp.weight coxWeight B.base
private def profile (B : Block) : HilbertPoly :=
  let (u,v,w) := baseDegree B
  rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
    (affine 1 1 0 (1-v)) (affine 0 0 0 (1+2*v-u))
    (affine 0 1 1 (1+v-u)) (affine 0 1 2 (1-u)) *
  seeds (seedFree B).card
    (affine 2 2 0 (1-w)) (affine 2 2 0 (2-w)) (C (1/2))
end
end HighCore82258GeometryCert_2_2
end

end Merged_HighCore82258UpperCertificates

-- merged module HighCore82258Regular
section Merged_HighCore82258Regular

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
set_option autoImplicit false
namespace HighCore82258_5
noncomputable section
open HighCore82258 (agreement blockLength)
open HighCore82258 (degreeAt  gap    )
open HighCore82258Upper (Input cutSeed cutVelocity cutOrdinate   )
end
end HighCore82258_5
end
section
namespace HighCore82258_5
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open HighCore82258 (K I node agreement)
open HighCore82258 (FixedWord)
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
end
end HighCore82258_5
end
section
set_option autoImplicit false
namespace HighCore82258_5
noncomputable section
open Polynomial Finset
open HighCore82258 (K I agreement blockLength node p)
open HighCore82258 (FixedWord degreeAt gap    )
open K1_14 (Equation graphEval)
open K1_14_4 (seedDegree)
open HighCore82258Upper (Input ResidueLift Factors ProperCurve ProperCover 
     
  )
open scoped BigOperators
end
end HighCore82258_5
end
section
set_option autoImplicit false
namespace HighCore82258_5
open HighCore82258 (p agreement start finish)
open HighCore82258 (degreeAt    
  FixedWord)
open HighCore82258Upper (Input)
end HighCore82258_5
end

namespace HighCore82258


end HighCore82258

end Merged_HighCore82258Regular

-- merged module HighCore82258PrefixProcess
section Merged_HighCore82258PrefixProcess

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

open HighCore82258 (start finish)
set_option maxHeartbeats 3200000

section
namespace HighCore82258_3
noncomputable section
open Polynomial
open HighCore82258 (K p agreement blockLength AnchorModel AnchoredFamily)
open HighCore82258 (Stage stages terminal fullCutoff degreeAt gap fees curveUnit)
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
def BankPass (rows : Banks) (s : Shape) (I : Ideal Ambient) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), K1_14_2.toJet P ∈ I
def PairPass {h rows s} (pair : HighCore82258.BufferedPair h rows s) (I : Ideal Ambient) : Prop :=
  BankPass rows s.free.shape I ∧ BankPass rows s.moving.shape I ∧
    K1_14_2_2R.chainCompatible pair.free pair.moving I
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (b : HighCore82258.Band) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  mass_bound : Fits parents (initialCap b)
  seed : K1_14_3.SeedCover
  seed_le : seed.curve.totalDegree ≤ initialCap b 2
  seed_points : seed.points.card ≤ initialE b
  ordinates : Finset FX
  ordinate_le : ordinates.card ≤ initialCap b 0
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, seed.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    graphEval (M.label γ) content = 0 ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ
end
end HighCore82258_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace HighCore82258_3
noncomputable section
open Polynomial
open HighCore82258 (AnchorModel AnchoredFamily K p agreement)
open HighCore82258 (Stage Listed Source  stages fullCutoff buffered )
open K1_14 (Shape Banks Jet Equation jetAt seedHasse seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField
  JetSeedSection JetYSection ODE)
open K1_14_2_2 (Active dual orderOn FixedPart ODECaps fixedOn RowCaps CutCover
  sectionDegree weight dot joinCuts joinCuts_cost sum_dot emptyCut mass)
open K1_14_2_2_3
open K1_14_2_2_7
open K1_14_2_2_3 (specialize_shiftedWord shift_word)
open scoped BigOperators Classical
abbrev StageIndex (b : HighCore82258.Band) := Fin (stages b).length
def pairAt {b h rows} (pairs : HighCore82258.Pairs b h rows) (i : StageIndex b) :
    HighCore82258.BufferedPair h rows (stageAt b i) :=
  pairs _ (stage_mem i.isLt)
structure FixedRows {b h rows} (pairs : HighCore82258.Pairs b h rows) (i : StageIndex b) where
  free : FixedPart (pairAt pairs i).free (stageAt b i).free.shape
  moving : FixedPart (pairAt pairs i).moving (stageAt b i).moving.shape
theorem envelope_caps {s : Stage} {P : Jet}
    (hb : s.free.shape.J ≤ s.free.shape.B) (hc : s.moving.shape.J ≤ s.moving.shape.B)
    (hP : RowCaps P s.free.shape ∨ RowCaps P s.moving.shape) : RowCaps P (envelope s) := by
  have ha : s.free.shape.B ≤ (envelope s).B :=
    (Nat.sub_add_cancel hb).symm.trans_le
      (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  have hd : s.moving.shape.B ≤ (envelope s).B :=
    (Nat.sub_add_cancel hc).symm.trans_le
      (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  intro j i h
  rcases hP with hp | hp
  · obtain ⟨hg, hj, hu⟩ := hp j i h
    exact ⟨hg.trans ha, hj.trans (le_max_left _ _), hu.trans (le_max_left _ _)⟩
  · obtain ⟨hg, hj, hu⟩ := hp j i h
    exact ⟨hg.trans hd, hj.trans (le_max_right _ _), hu.trans (le_max_right _ _)⟩
end
end HighCore82258_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1000000
namespace HighCore82258_3
noncomputable section
open HighCore82258 (AnchorModel AnchoredFamily)
open HighCore82258 (stages terminal Source )
open P1_7_4 (massQ_mono)
open K1_14 (Banks)
open K1_14_2 (Ambient)
open K1_14_2_2 (Active Fits dual fixedOn mass)
open scoped Classical
def nextIndex {b : HighCore82258.Band} (i : ℕ) (hi : i < laterCount b) : StageIndex b :=
  ⟨i+1, by change i+1 < (HighCore82258.stages b).length; unfold laterCount at hi; omega⟩
structure Process {b h rows} (pairs : HighCore82258.Pairs b h rows) where
  sched : ScheduleOK b
  parents : Finset (Ideal Ambient)
  fixed : ∀ i : StageIndex b, FixedRows pairs i
  geometry : ∀ I ∈ parents, Active I ∧ I.height = 2
  init_mass : Fits parents (initialCap b)
def Process.Clean {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs)
    (I : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixed i).free.equation I ∧ ¬ fixedOn (R.fixed i).moving.equation I
def PassedThrough {b h rows} (pairs : HighCore82258.Pairs b h rows) (i : ℕ) (I : Ideal Ambient) : Prop :=
  ∀ j : StageIndex b, 0 < j.val → j.val ≤ i → PairPass (pairAt pairs j) I
def Process.tested {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  R.parents.filter fun I => R.Clean I ∧ PassedThrough pairs i I
def Process.kept {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  (R.tested i).filter fun I => stopIndex b ≤ i → dual I
def Process.rankExit {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.tested (stopIndex b)).filter fun I => ¬ dual I
def Process.final {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.kept (laterCount b)).filter (BankPass rows (terminal b).shape)
def Process.live {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if i ≤ laterCount b then R.kept i else R.final
def Process.lost {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if hi : i < laterCount b then
    (R.kept i).filter fun I => ¬ PairPass (pairAt pairs (nextIndex i hi)) I
  else
    (R.kept i).filter fun I => ¬ BankPass rows (terminal b).shape I
theorem Process.kept_sub {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.kept i ⊆ R.tested i :=
  Finset.filter_subset _ _
theorem Process.retains {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs)
    {I : Ideal Ambient} (hI : I ∈ R.parents) (hc : R.Clean I)
    (hrank : I ∉ R.rankExit) (hlost : ∀ i ≤ laterCount b, I ∉ R.lost i) :
    I ∈ R.final := by
  have keep : ∀ i ≤ laterCount b, I ∈ R.kept i := by
    intro i hi
    induction i with
    | zero =>
      have ht : I ∈ R.tested 0 :=
        Finset.mem_filter.mpr ⟨hI, hc, fun j hp hj => (Nat.not_lt_of_ge hj hp).elim⟩
      refine Finset.mem_filter.mpr ⟨ht, ?_⟩
      intro hs
      by_contra hd
      exact hrank (Finset.mem_filter.mpr ⟨by simpa [Nat.eq_zero_of_le_zero hs] using ht, hd⟩)
    | succ i ih =>
      have ht : i < laterCount b := hi
      have hprev := ih (Nat.le_of_lt ht)
      have hp : PairPass (pairAt pairs (nextIndex i ht)) I := by
        by_contra hfail
        apply hlost i ht.le
        simpa only [Process.lost, dite_eq_left ht] using Finset.mem_filter.mpr ⟨hprev, hfail⟩
      have htest : I ∈ R.tested (i+1) := by
        refine Finset.mem_filter.mpr ⟨hI, hc, ?_⟩
        intro j hj hji
        rcases hji.lt_or_eq with hj' | he
        · exact (Finset.mem_filter.mp (R.kept_sub i hprev)).2.2 j hj (Nat.le_of_lt_succ hj')
        · rw [show j = nextIndex i ht from Fin.ext he]
          exact hp
      refine Finset.mem_filter.mpr ⟨htest, ?_⟩
      intro hs
      by_cases hh : stopIndex b ≤ i
      · exact (Finset.mem_filter.mp hprev).2 hh
      · have he : stopIndex b = i+1 := by omega
        by_contra hd
        exact hrank (Finset.mem_filter.mpr ⟨by simpa [he] using htest, hd⟩)
  have hk := keep (laterCount b) le_rfl
  refine Finset.mem_filter.mpr ⟨hk, ?_⟩
  by_contra hf
  apply hlost (laterCount b) le_rfl
  simpa only [Process.lost, dite_eq_right (Nat.lt_irrefl _)] using Finset.mem_filter.mpr ⟨hk, hf⟩
end
end HighCore82258_3
end

end Merged_HighCore82258PrefixProcess
