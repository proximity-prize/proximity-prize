import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdA2
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdBG
import ProximityPrize.SubmissionLower.DdZ3EWiUc
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_ReedSolomon_MutualCorrelatedAgreement_Johnson_Agreement
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Finset_PairwiseIntersection
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_LinearAlgebra_FiniteDimensional
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_RingTheory_MvPolynomial_StandardMonomials
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Coeff
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_NoZeroDivisors
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Basis
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Degree_IsMonicOfDegree
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_TrivSqZeroExt_Ideal
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_BoxIntegral_UnitPartition
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Measure
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Visible
import ProximityPrize.SubmissionLower.LibraryMathlib_Combinatorics_Pigeonhole
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Finsupp_Interval
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Set_Card_Arithmetic
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Sym_NatCard
import ProximityPrize.SubmissionLower.LibraryMathlib_GroupTheory_CosetCover
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_FreeModule_Norm
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_TensorProduct_Free
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_FunctionField
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_RatFunc_Ostrowski
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_DedekindDomain_Factorization
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Finiteness_Descent
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Flat_Equalizer
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_GradedAlgebra_Radical
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Ideal_IsPrincipalPowQuotient
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Localization_NormTrace
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_OrderOfVanishing_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_PowerSeries_Inverse
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RamificationInertia_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Regular_Flat
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Surjective
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Unramified
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Spectrum_Prime_Homeomorph
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_Discrete_RankOne
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_LocalSubring
import ProximityPrize.SubmissionLower.LibraryMathlib_Topology_Algebra_MvPolynomial
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_DdB4
set_option Elab.async false




























































set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit true
section
namespace aZw
noncomputable section
open Polynomial

open scoped BigOperators
end
end aZw
end
section
namespace aZw
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark

theorem azg (errors m x gap cap:ℕ)
    (hm:0< m) (hg:0<gap) (hx :gap≤x) (he :0<errors)
    (hsecond: (m*x)^2≤(x+errors)*(m*(x+(m-1)*(x-gap))))
    (hfirst:m*x≤(x+errors)*cap) :
    gap*m≤errors*cap+gap:= by
  have hcancel:m*x^2≤(x+errors)*(x+(m-1)*(x-gap)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _=(m*x)^2 := by ring
      _≤_:=hsecond
      _ = _:= by ring
  have hM: ((m - 1 :ℕ) :ℤ)=(m:ℤ)-1 :=Int.ofNat_sub (by omega)
  have hX: ((x - gap:ℕ) :ℤ)=(x :ℤ)-gap:=Int.ofNat_sub hx
  have hcancelZ:=Int.ofNat_le.mpr hcancel
  push_cast [hM,hX] at hcancelZ
  have hfirstZ:=Int.ofNat_le.mpr hfirst
  push_cast at hfirstZ
  have secondZ: ((m:ℤ)*errors-((m:ℤ)-1)*gap)*x ≥
      ((m:ℤ)-1)*errors*gap:= by
    nlinarith only [hcancelZ]
  have firstZ: ((m:ℤ)-(cap:ℤ))*x≤(cap:ℤ)*errors := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ: (errors :ℤ)*cap+gap<(gap:ℤ)*m:= by exact_mod_cast h
  have hbad: (cap:ℤ)*errors<((m:ℤ)-1)*gap:= by nlinarith only [hbadZ]
  have hxpos :0<(x :ℤ) := by omega
  have cmp: (m:ℤ)*errors-((m:ℤ)-1)*gap<((m:ℤ)-(cap:ℤ))*errors := by
    linarith only [hbad]
  have left:=mul_lt_mul_of_pos_right cmp hxpos
  have right:=mul_le_mul_of_nonneg_right firstZ (Int.natCast_nonneg errors)
  have impossible :=secondZ.trans_lt (left.trans_le (show
      ((m:ℤ)-(cap:ℤ))*errors*x≤(cap:ℤ)*errors*errors from by
        convert right using 1
        ring))
  have bigger :=mul_lt_mul_of_pos_right hbad (Int.ofNat_lt.mpr he)
  nlinarith only [impossible,bigger]
end
end aZw
end
section
set_option backward.isDefEq.respectTransparency false
namespace atp
noncomputable section

open Polynomial
open scoped Polynomial
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open Polynomial
open scoped Polynomial BigOperators
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open DdK1 (I)
open Polynomial
open scoped Polynomial BigOperators
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open DdK1 (I)
open Polynomial
open scoped Polynomial BigOperators
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace dnG
noncomputable section
open cu Polynomial
open scoped BigOperators Polynomial
end
end dnG
end
section
namespace bjU

open Finset
open scoped BigOperators
end bjU
end
section
namespace bjU

open Finset
open scoped BigOperators
end bjU
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace dnk
noncomputable section
open cu
end
end dnk
end

end Merged6967_DdB4

section Merged6967_Fast048
set_option Elab.async false


























set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_5
noncomputable section
open K1 K1_13 Polynomial
open scoped BigOperators
def RegularAt {r : ℕ} (top : Fin r) (f : Row r) (S : (Polynomial Geom)) : Prop :=
  atJet f S = 0 ∧ atJet (MvPolynomial.pderiv top f) S ≠ 0
structure FirstRow (q : Row 2) : Prop where
  ne_zero : q ≠ 0
  total : q.totalDegree ≤ 5064
  index : indexDegree q ≤ 1104
structure FirstFactors {n : ℕ} (f : Fin n → Row 2) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 1
  total : (∑ i, (f i).totalDegree) ≤ 5064
  index : (∑ i, indexDegree (f i)) ≤ 1104
structure SecondFactors {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  weight : ∀ i, TrueWeightLE (f i) (90 * 180265 - 1)
  total : (∑ i, (f i).totalDegree) ≤ 120
  index : (∑ i, indexDegree (f i)) ≤ 48
  top : (∑ i, (f i).degreeOf 2) ≤ 24
def coeffDerivative {r : ℕ} (f : Row r) : Row r :=
  ∑ m ∈ f.support, MvPolynomial.monomial m (f.coeff m).derivative
def separant (f : Row 3) : Row 3 := MvPolynomial.pderiv 2 f
def lowerTangent (b : Row 3) : Row 3 :=
  coeffDerivative b + MvPolynomial.X 1 * MvPolynomial.pderiv 0 b +
    2 * MvPolynomial.X 2 * MvPolynomial.pderiv 1 b
def tangentNumerator (f b : Row 3) : Row 3 :=
  separant f * lowerTangent b - lowerTangent f * MvPolynomial.pderiv 2 b
def compatibilityNumerator (f : Row 3) : ℕ → Row 3
  | 0 => -lowerTangent f
  | j + 1 =>
    let b := compatibilityNumerator f j
    separant f * tangentNumerator f b - (2 * j + 1 : ℕ) * b * tangentNumerator f (separant f)
def Whole (f : Row 3) : Prop :=
  f ∣ compatibilityNumerator f (taylorLength - 3)
def NodeCapacity (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop := by
  classical
  exact ∃ persistent : Finset I,
    (∀ i ∈ persistent, ∀ γ ∈ Γ, (s γ).eval (node i) = w i) ∧
    ∀ i, i ∉ persistent → (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d
structure NodeFamily (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) where
  n : ℕ
  part : Fin n → Finset K
  cap : Fin n → ℕ
  sub : ∀ i, part i ⊆ Γ
  localCapacity : ∀ i, NodeCapacity w (part i) s (cap i)
def NodeFamily.labels {w Γ s} (F : NodeFamily w Γ s) : Finset K := by
  classical
  exact Finset.univ.biUnion F.part
def NodeFamily.totalCap {w Γ s} (F : NodeFamily w Γ s) : ℕ := ∑ i, F.cap i
abbrev lowBox : Shape := ⟨120,48,24⟩
def liftedBox (L : ℕ) : Shape :=
  let j := 2 + (L - 4) * (lowBox.j + 2)
  ⟨1 + (L - 4) * lowBox.b, j, min (1 + (L - 4) * (lowBox.t + 2)) (j / 2)⟩
abbrev graphBox : Shape := ⟨120,49,24⟩
def volumeTerm (p q r : Shape) : ℕ := p.t * (q.j - q.t) * (2 * r.b - r.j)
def mixed3 (p q r : Shape) : ℕ :=
  (volumeTerm p q r + volumeTerm p r q + volumeTerm q p r +
    volumeTerm q r p + volumeTerm r p q + volumeTerm r q p) / 2
def mixedBudget : ℕ :=
  let a := liftedBox (taylorLength + 1)
  let b := liftedBox (taylorLength + 2)
  mixed3 lowBox a b + (taylorLength - 1) * mixed3 lowBox graphBox b +
    taylorLength * mixed3 lowBox graphBox a
def invariantBudget : ℕ :=
  lowBox.b * (1 + (2 * (taylorLength + 1) - 7) * (lowBox.b - 1))
structure ProperCover (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget
  fresh : invariant.totalCap ≤ invariantBudget
  components : multiple.n + invariant.n ≤ 2 * invariantBudget
end
end K1_13_5
end
section
namespace K1_13_5_4
noncomputable section
open K1 K1_13 K1_13_5 Polynomial
open scoped BigOperators
abbrev RationalX := FractionRing (Polynomial Geom)
abbrev GeometricX := AlgebraicClosure RationalX
abbrev GeoRow (n : ℕ) := MvPolynomial (Fin n) GeometricX
abbrev Coefficients := Fin taylorLength → GeometricX
abbrev CoefficientIdeal := Ideal (GeoRow taylorLength)
abbrev CurveIndex (n : ℕ) := Fin n × Ideal (GeoRow 3)
def genericCoeff : (Polynomial Geom) →+* GeometricX :=
  (algebraMap RationalX GeometricX).comp (algebraMap (Polynomial Geom) RationalX)
def genericRow {n : ℕ} (P : Row n) : GeoRow n := MvPolynomial.map genericCoeff P
def jetPoint {n : ℕ} (S : (Polynomial Geom)) : Fin n → GeometricX :=
  fun j => genericCoeff (jet S j)
def coefficientPoint (S : (Polynomial Geom)) : Coefficients :=
  fun j => algebraMap Geom GeometricX (S.coeff j)
def coefficientPolynomial (a : Coefficients) : (Polynomial GeometricX) :=
  ∑ j : Fin taylorLength, Polynomial.monomial j.val (a j)
def oldCut (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 3)
def oldNext (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 2)
def oldCutIdeal (f : Row 3) : Ideal (GeoRow 3) :=
  Ideal.span {genericRow f, genericRow (oldCut f)}
def properComponents {n : ℕ} (f : Fin n → Row 3) : Finset (CurveIndex n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Whole (f i) then ∅ else
      ((oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i)))).image
        (fun P => (i, P))
def regularLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ MvPolynomial.zeroLocus GeometricX P ∧
    MvPolynomial.eval y (genericRow (separant f)) ≠ 0}
def componentLength (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ∞ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let A := Localization.AtPrime P
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A))
  else 0
def nextCutLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ regularLocus f P ∧ MvPolynomial.eval y (genericRow (oldNext f)) = 0}
def liftRow (P : GeoRow 3) : GeoRow 4 := MvPolynomial.rename Fin.castSucc P
def graph (f : Row 3) : GeoRow 4 :=
  liftRow (genericRow (lowerTangent f)) + 3 * MvPolynomial.X 3 * liftRow (genericRow (separant f))
def graphIdeal (f : Row 3) : Ideal (GeoRow 4) :=
  Ideal.span {liftRow (genericRow f), graph f}
def graphPoint (f : Row 3) (y : Fin 3 → GeometricX) : Fin 4 → GeometricX :=
  Fin.snoc y (-MvPolynomial.eval y (genericRow (lowerTangent f)) /
    (3 * MvPolynomial.eval y (genericRow (separant f))))
def InLiftedBox (P : GeoRow 4) (box : Shape) (height : ℕ) : Prop :=
  ∀ a ∈ P.support, a 0 + a 1 + a 2 ≤ box.b ∧
    a 1 + 2 * a 2 ≤ box.j ∧ a 2 ≤ box.t ∧ a 3 ≤ height
def RepresentsOnGraph (f old : Row 3) (P : GeoRow 4) : Prop :=
  ∃ (a b : ℕ) (c : GeometricX), c ≠ 0 ∧
    let sep := liftRow (genericRow (separant f))
    sep ^ a * (sep ^ b * P - MvPolynomial.C c * liftRow (genericRow old)) ∈ graphIdeal f
def reconstruct (f : Row 3) (numerator : Fin taylorLength → GeoRow 4)
    (y : Fin 3 → GeometricX) : Coefficients :=
  fun i => MvPolynomial.eval (graphPoint f y) (numerator i) /
    MvPolynomial.eval y (genericRow (separant f)) ^ (taylorLength - 4)
structure LiftedChart (f : Row 3) where
  cut : GeoRow 4
  next : GeoRow 4
  numerator : Fin taylorLength → GeoRow 4
  graph_box : InLiftedBox (graph f) graphBox 1
  cut_box : InLiftedBox cut (liftedBox (taylorLength + 1)) (taylorLength - 1)
  next_box : InLiftedBox next (liftedBox (taylorLength + 2)) taylorLength
  coefficient_box : ∀ i, InLiftedBox (numerator i) (liftedBox taylorLength) (taylorLength - 2)
  cut_represents : RepresentsOnGraph f (oldCut f) cut
  next_represents : RepresentsOnGraph f (oldNext f) next
  ordinary_bound : (oldCut f).totalDegree ≤
    1 + (2 * (taylorLength + 1) - 7) * (f.totalDegree - 1)
  actual : ∀ S : (Polynomial Geom), S.natDegree ≤ 133671 → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S
structure MixedSections {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart (f i)) where
  length : CurveIndex n → ℕ
  degree : CurveIndex n → ℕ
  length_eq : ∀ a ∈ properComponents f, (length a : ℕ∞) = componentLength (f a.1) a.2
  length_pos : ∀ a ∈ properComponents f, 0 < length a
  total : (∑ a ∈ properComponents f, length a * degree a) ≤ mixedBudget
  points : ∀ a ∈ properComponents f, genericRow (oldNext (f a.1)) ∉ a.2 →
    (nextCutLocus (f a.1) a.2).Finite ∧ (nextCutLocus (f a.1) a.2).ncard ≤ degree a
  curves : ∀ a ∈ properComponents f, 2 ≤ length a →
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      0 < degree a ∧ MvPolynomial.affineDegree Q ≤ (degree a : ℚ) ∧
      ∀ y ∈ regularLocus (f a.1) a.2,
        reconstruct (f a.1) (T a.1).numerator y ∈ MvPolynomial.zeroLocus GeometricX Q
def extendedAtJet (P : Row 3) (S : (Polynomial GeometricX)) : (Polynomial GeometricX) :=
  MvPolynomial.eval (fun j => hasseDeriv j.val S)
    (MvPolynomial.map (Polynomial.mapRingHom (algebraMap Geom GeometricX)) P)
structure ActualSolutionCurve (f : Row 3) (Q : CoefficientIdeal) : Prop where
  prime : Q.IsPrime
  dimension : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1
  solves : ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet f (coefficientPolynomial a) = 0
  regular : ∃ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet (separant f) (coefficientPolynomial a) ≠ 0
end
end K1_13_5_4
end
section
namespace K1_13_5_4
noncomputable section
open K1 K1_13 K1_13_5 Polynomial
open scoped BigOperators
theorem genericCoeff_injective : Function.Injective genericCoeff :=
  (algebraMap RationalX GeometricX).injective.comp (IsFractionRing.injective (Polynomial Geom) RationalX)
theorem eval_genericRow_at_point {n : ℕ} (P : Row n) (S : (Polynomial Geom)) :
    MvPolynomial.eval (jetPoint S) (genericRow P) = genericCoeff (atJet P S) := by
  unfold genericRow atJet jetPoint
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp _ _ _).symm
theorem jetPoint_injOn (s : K → (Polynomial K)) (Γ : Finset K)
    (hs : Set.InjOn s (Γ : Set K)) :
    Set.InjOn (fun γ => jetPoint (n := 3) (extend (s γ))) (Γ : Set K) := by
  intro γ hγ δ hδ heq
  apply hs hγ hδ
  apply Polynomial.map_injective embed embed.injective
  have h := genericCoeff_injective (congrFun heq (0 : Fin 3))
  simpa [jet, jetPoint] using h
end
end K1_13_5_4
end
section
namespace K1_13_5_4
noncomputable section
open K1 K1_13 K1_13_5 Polynomial
open scoped BigOperators
def c4 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∀ i, (oldCut (f i)).totalDegree ≤
      1 + (2 * (taylorLength + 1) - 7) * ((f i).totalDegree - 1)) →
    ∀ C : Finset CoefficientIdeal,
      (∀ Q ∈ C, ∃ i, ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q) →
      ∃ d : CoefficientIdeal → ℕ,
        (∀ Q ∈ C, 0 < d Q ∧ MvPolynomial.affineDegree Q ≤ (d Q : ℚ)) ∧
          (∑ Q ∈ C, d Q) ≤ invariantBudget
private theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {i : Fin n}
    {P : Ideal (GeoRow 3)} : (i, P) ∈ properComponents f ↔
    ¬ Whole (f i) ∧ P ∈ (oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i))) := by
  classical
  simp only [properComponents, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hw : Whole (f k)
    · simp [hw] at hk
    · simp only [hw, ite_false] at hk
      obtain ⟨P', hP', he⟩ := Finset.mem_image.mp hk
      cases he
      exact ⟨hw, hP'⟩
  · rintro ⟨hw, hP⟩
    exact ⟨i, by simpa only [hw, ite_false] using Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩
private theorem exists_properComponent {n : ℕ} {f : Fin n → Row 3}
    (T : ∀ i, LiftedChart (f i)) {i : Fin n} {S : (Polynomial Geom)}
    (hS : S.natDegree ≤ 133671) (hr : RegularAt 2 (f i) S) (hw : ¬ Whole (f i)) :
    ∃ P, (i, P) ∈ properComponents f ∧ jetPoint S ∈ regularLocus (f i) P := by
  have hzero : jetPoint S ∈ MvPolynomial.zeroLocus GeometricX (oldCutIdeal (f i)) := by
    apply MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mpr
    apply Ideal.span_le.mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    change g ∈ RingHom.ker (MvPolynomial.aeval (jetPoint S))
    rw [RingHom.mem_ker]
    change MvPolynomial.eval (jetPoint S) g = 0
    rcases hg with rfl | rfl
    · rw [eval_genericRow_at_point, hr.1, map_zero]
    · rw [eval_genericRow_at_point, (T i).actual S hS hr |>.1, map_zero]
  have hsep : MvPolynomial.eval (jetPoint S) (genericRow (separant (f i))) ≠ 0 := by
    rw [eval_genericRow_at_point]
    exact fun h => hr.2 ((map_eq_zero_iff genericCoeff genericCoeff_injective).mp h)
  obtain ⟨P, hP, hy⟩ := MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus
    (oldCutIdeal (f i)) (genericRow (separant (f i))) (jetPoint S) hzero hsep
  exact ⟨P, mem_properComponents.mpr ⟨hw, hP⟩, ⟨hy, hsep⟩⟩
end
end K1_13_5_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open scoped BigOperators Pointwise
abbrev JetPoint := Fin 4 → GeometricX
def factorCurves (f : Row 3) : Finset (Ideal (GeoRow 3)) := by
  classical
  exact if Whole f then ∅ else
    (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))
def graphLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set JetPoint :=
  graphPoint f '' regularLocus f P
def graphCurve (f : Row 3) (P : Ideal (GeoRow 3)) : Ideal (GeoRow 4) :=
  vanishingIdeal GeometricX (graphLocus f P)
def boxExponents (s : Shape) (h : ℕ) : Set (Fin 4 →₀ ℕ) :=
  {a | a 0 + a 1 + a 2 ≤ s.b ∧ a 1 + 2 * a 2 ≤ s.j ∧ a 2 ≤ s.t ∧ a 3 ≤ h}
instance boxExponentsFinite (s : Shape) (h : ℕ) : Finite (boxExponents s h) :=
  ((Finsupp.finite_of_degree_le (s.b + h)).subset (by
    intro a ha
    change a.degree ≤ s.b + h
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
    exact (Nat.add_le_add ha.1 ha.2.2.2))).to_subtype
abbrev lastBox := liftedBox (taylorLength + 2)
abbrev lastExponents := boxExponents lastBox taylorLength
abbrev lastMap := monomialMap GeometricX lastExponents
def sectionIdeal (f : Row 3) (P : Ideal (GeoRow 3)) :
    Ideal (MvPolynomial lastExponents GeometricX) :=
  (graphCurve f P).comap lastMap
def sectionDegree (f : Row 3) (P : Ideal (GeoRow 3)) : ℚ :=
  affineDegree (sectionIdeal f P)
structure GenericSection (f : Row 3) where
  polynomial : GeoRow 4
  support : InLiftedBox polynomial lastBox taylorLength
  points : Ideal (GeoRow 3) → Finset JetPoint
  card_eq : ∀ P ∈ factorCurves f, ((points P).card : ℚ) = sectionDegree f P
  proper : ∀ P ∈ factorCurves f, polynomial ∉ graphCurve f P
  roots : ∀ P ∈ factorCurves f, ∀ y ∈ points P,
    y ∈ graphLocus f P ∧ eval y polynomial = 0
  off_other_curves : ∀ P ∈ factorCurves f, ∀ P' ∈ factorCurves f, P ≠ P' →
    ∀ y ∈ points P, y ∉ graphLocus f P'
def fourCutIdeal (F G E L : GeoRow 4) : Ideal (GeoRow 4) :=
  Ideal.span {F, G, E, L}
abbrev pointIdeal (y : JetPoint) : Ideal (GeoRow 4) :=
  vanishingIdeal GeometricX {y}
def pointLength (J : Ideal (GeoRow 4)) (y : JetPoint) : ℕ∞ :=
  let A := Localization.AtPrime (pointIdeal y)
  Module.length A (A ⧸ J.map (algebraMap (GeoRow 4) A))
abbrev ExponentSpace := Fin 4 → ℝ
def capBody (s : Shape) (h : ℕ) : Set ExponentSpace :=
  {x | (∀ j, 0 ≤ x j) ∧ x 0 + x 1 + x 2 ≤ s.b ∧
    x 1 + 2 * x 2 ≤ s.j ∧ x 2 ≤ s.t ∧ x 3 ≤ h}
def downBody (F : GeoRow 4) : Set ExponentSpace :=
  convexHull ℝ {x | ∃ a ∈ F.support, ∀ j, 0 ≤ x j ∧ x j ≤ a j}
def mixedVolume4 (B : Fin 4 → Set ExponentSpace) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
    (-1 : ℝ) ^ (4 - S.card) * (MeasureTheory.volume (∑ i ∈ S, B i)).toReal
end
end K1_13_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open scoped BigOperators
theorem localLength_lt_top {R : Type} [CommRing R] [IsNoetherianRing R]
    {P J : Ideal R} [P.IsPrime] (hP : P ∈ J.minimalPrimes) :
    let A := Localization.AtPrime P
    Module.length A (A ⧸ J.map (algebraMap R A)) < ⊤ := by
  let A := Localization.AtPrime P
  let L := J.map (algebraMap R A)
  change Module.length A (A ⧸ L) < ⊤
  have hmin : IsLocalRing.maximalIdeal A ∈ L.minimalPrimes := by
    rw [show L = J.map (algebraMap R A) from rfl,
      IsLocalization.minimalPrimes_map P.primeCompl A, Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A P]
    exact hP
  have : IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,
        isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := L))⟩))
theorem graphPoint_injective (f : Row 3) : Function.Injective (graphPoint f) := by
  intro y z h
  funext i
  simpa only [graphPoint, Fin.snoc_castSucc] using congrFun h i.castSucc
@[simp] theorem eval_liftRow_graphPoint (f : Row 3) (x : Fin 3 → GeometricX) (P : GeoRow 3) :
    eval (graphPoint f x) (liftRow P) = eval x P := by
  rw [liftRow, eval_rename]
  have h : graphPoint f x ∘ Fin.castSucc = x := Fin.snoc_comp_castSucc
  rw [h]
theorem three_ne_zero : (3 : GeometricX) ≠ 0 := by
  let : CharP Geom K1.p := charP_of_injective_ringHom K1_13.embed.injective K1.p
  let : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  let : CharP GeometricX K1.p :=
    charP_of_injective_ringHom genericCoeff_injective K1.p
  exact fun h => (by decide : ¬ K1.p ∣ 3)
    ((CharP.cast_eq_zero_iff GeometricX K1.p 3).mp h)
theorem eval_graph_graphPoint {f : Row 3} {x : Fin 3 → GeometricX}
    (hx : eval x (genericRow (separant f)) ≠ 0) :
    eval (graphPoint f x) (graph f) = 0 := by
  have hs : (3 : GeometricX) * eval x (genericRow (separant f)) ≠ 0 :=
    mul_ne_zero three_ne_zero hx
  have hz : graphPoint f x 3 = -eval x (genericRow (lowerTangent f)) /
      (3 * eval x (genericRow (separant f))) := by
    exact Fin.snoc_last _ _
  rw [graph, map_add, map_mul, map_mul, map_ofNat, eval_X,
    eval_liftRow_graphPoint, eval_liftRow_graphPoint, hz]
  let u := eval x (genericRow (lowerTangent f))
  let s := eval x (genericRow (separant f))
  change u + 3 * (-u / (3 * s)) * s = 0
  calc
    _ = u + (-u / (3 * s)) * (3 * s) := by ring
    _ = 0 := by rw [div_mul_cancel₀ _ hs, add_neg_cancel]
theorem eval_represents_iff {f old : Row 3} {B : GeoRow 4}
    (hB : RepresentsOnGraph f old B) {x : Fin 3 → GeometricX}
    (hf : eval x (genericRow f) = 0) (hx : eval x (genericRow (separant f)) ≠ 0) :
    eval (graphPoint f x) B = 0 ↔ eval x (genericRow old) = 0 := by
  have ht : graphIdeal f ≤ RingHom.ker (eval (graphPoint f x)) := by
    apply Ideal.span_le.mpr
    intro q hq
    change q ∈ RingHom.ker (eval (graphPoint f x))
    rw [RingHom.mem_ker]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · simpa only [eval_liftRow_graphPoint] using hf
    · exact eval_graph_graphPoint hx
  obtain ⟨a, b, c, hc, hm⟩ := hB
  have he := RingHom.mem_ker.mp (ht hm)
  simp only [map_mul, map_pow, map_sub, eval_C, eval_liftRow_graphPoint] at he
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero a hx))
  constructor
  · intro h
    rw [h, mul_zero] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left hc
  · intro h
    rw [h, mul_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero b hx)
end
end K1_13_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
open scoped Pointwise
abbrev Exponent := Fin 4 →₀ ℕ
def Downward (A : Finset Exponent) : Prop :=
  ∀ ⦃a b : Exponent⦄, a ∈ A → b ≤ a → b ∈ A
def exponentVector : Exponent →+ ExponentSpace where
  toFun a i := (a i : ℝ)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp [Finsupp.add_apply]
def latticeBody (A : Set Exponent) : Set ExponentSpace :=
  convexHull ℝ (exponentVector '' A)
def downSupport (F : GeoRow 4) : Finset Exponent :=
  F.support.biUnion fun a => Finset.Icc 0 a
def capSupport (s : Shape) (h : ℕ) : Finset Exponent :=
  (Set.toFinite (boxExponents s h)).toFinset
def cutIdeal (f : Fin 4 → GeoRow 4) : Ideal (GeoRow 4) :=
  Ideal.span (Set.range f)
abbrev CoefficientRing (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (Σ i : Fin 4, ↥(A i)) GeometricX
abbrev CoefficientField (A : Fin 4 → Finset Exponent) :=
  FractionRing (CoefficientRing A)
def genericEquation (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    MvPolynomial (Fin 4) (CoefficientField A) :=
  ∑ a : ↥(A i), monomial a.1
    (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩))
abbrev GenericQuotient (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (Fin 4) (CoefficientField A) ⧸ Ideal.span (Set.range (genericEquation A))
def exponentCount (A : Fin 4 → Finset Exponent) (d : Fin 4 → ℕ) : ℕ :=
  (∑ i : Fin 4, d i • (↑(A i) : Set Exponent)).ncard
def corner (q n : ℕ) (S : Finset (Fin 4)) : Fin 4 → ℕ :=
  fun i => q + if i ∈ S then n else 0
end
end K1_13_5_4_2_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4
noncomputable section
open K1_13 K1_13_5_4 K1_13_5_4_2 MvPolynomial
theorem mem_downSupport {F : GeoRow 4} {a : Exponent} :
    a ∈ downSupport F ↔ ∃ b ∈ F.support, a ≤ b := by
  classical
  simp [downSupport, Finset.mem_Icc, show (0 : Exponent) ≤ a from fun _ => Nat.zero_le _]
theorem mem_capSupport {s : Shape} {h : ℕ} {a : Exponent} :
    a ∈ capSupport s h ↔ a ∈ boxExponents s h :=
  Set.Finite.mem_toFinset _
theorem latticeBody_downSupport (F : GeoRow 4) :
    latticeBody (downSupport F) = downBody F := by
  unfold latticeBody downBody
  apply Set.Subset.antisymm
  · apply convexHull_mono
    rintro x ⟨e, he, rfl⟩
    obtain ⟨a, ha, hea⟩ := mem_downSupport.mp he
    exact ⟨a, ha, fun i => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hea i)⟩⟩
  · refine convexHull_min ?_ (convex_convexHull _ _)
    rintro x ⟨a, ha, hx⟩
    let corners : Set ExponentSpace :=
      Set.univ.pi fun i => ({0, (a i : ℝ)} : Set ℝ)
    have hxc : x ∈ convexHull ℝ corners := by
      apply mem_convexHull_pi
      intro i _
      rw [convexHull_pair, segment_eq_Icc (Nat.cast_nonneg (a i))]
      exact hx i
    apply convexHull_mono (t := exponentVector '' (↑(downSupport F) : Set Exponent)) ?_ hxc
    intro y hy
    change ∀ i ∈ (Set.univ : Set (Fin 4)), y i ∈ ({0, (a i : ℝ)} : Set ℝ) at hy
    have hv (i : Fin 4) : ∃ b : ℕ, (b : ℝ) = y i ∧ b ≤ a i := by
      have hi := hy i (Set.mem_univ i)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with hi | hi
      · exact ⟨0, by simpa using hi.symm, Nat.zero_le _⟩
      · exact ⟨a i, hi.symm, le_rfl⟩
    choose v hv using hv
    let e : Exponent := Finsupp.equivFunOnFinite.symm v
    have hev : ∀ i, e i = v i := fun i =>
      congrFun (Finsupp.equivFunOnFinite.apply_symm_apply v) i
    refine ⟨e, mem_downSupport.mpr ⟨a, ha, fun i => (hev i).trans_le (hv i).2⟩, ?_⟩
    funext i
    change (e i : ℝ) = y i
    rw [hev i, (hv i).1]
private def capParameter (s : Shape) (h : ℕ) (u : Fin 4 → ℝ) : ExponentSpace :=
  let z := u 2 * s.t
  let y := u 1 * ((s.j : ℝ) - 2 * z)
  ![u 0 * ((s.b : ℝ) - y - z), y, z, u 3 * h]
private theorem capParameter_update (s : Shape) (h : ℕ) (u : Fin 4 → ℝ) (i : Fin 4) :
    capParameter s h u = (1 - u i) • capParameter s h (Function.update u i 0) +
      u i • capParameter s h (Function.update u i 1) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [capParameter, Pi.add_apply, smul_eq_mul, Function.update] <;> ring
private theorem cap_corner_mem (s : Shape) (h : ℕ) (hs : s.j ≤ s.b)
    (ht : 2 * s.t ≤ s.j) (u : Fin 4 → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) :
    capParameter s h u ∈ latticeBody (capSupport s h) := by
  have hbinary (i : Fin 4) : ∃ v : ℕ, (v : ℝ) = u i ∧ v ≤ 1 := by
    rcases hu i with hi | hi
    · exact ⟨0, by simpa using hi.symm, Nat.zero_le 1⟩
    · exact ⟨1, by simpa using hi.symm, le_rfl⟩
  choose v hv using hbinary
  let z := v 2 * s.t
  let y := v 1 * (s.j - 2 * z)
  have hz : z ≤ s.t := by
    simpa [z] using Nat.mul_le_mul_right s.t (hv 2).2
  have hzs : 2 * z ≤ s.j := (Nat.mul_le_mul_left 2 hz).trans ht
  have hy : y ≤ s.j - 2 * z := by
    simpa [y] using Nat.mul_le_mul_right (s.j - 2 * z) (hv 1).2
  have hyz : y + 2 * z ≤ s.j := by omega
  have hys : y ≤ s.b := by omega
  have hzys : z ≤ s.b - y := by omega
  let exponents : Fin 4 → ℕ := ![v 0 * (s.b - y - z), y, z, v 3 * h]
  let e : Exponent := Finsupp.equivFunOnFinite.symm exponents
  have he (i : Fin 4) : e i = exponents i :=
    congrFun (Finsupp.equivFunOnFinite.apply_symm_apply exponents) i
  have hsupp : e ∈ capSupport s h := by
    apply mem_capSupport.mpr
    have hc₀ : v 0 * (s.b - y - z) ≤ s.b - y - z := by
      simpa using Nat.mul_le_mul_right (s.b - y - z) (hv 0).2
    have hc₃ : v 3 * h ≤ h := by simpa using Nat.mul_le_mul_right h (hv 3).2
    change e 0 + e 1 + e 2 ≤ s.b ∧ e 1 + 2 * e 2 ≤ s.j ∧ e 2 ≤ s.t ∧ e 3 ≤ h
    rw [he 0, he 1, he 2, he 3]
    change v 0 * (s.b - y - z) + y + z ≤ s.b ∧ y + 2 * z ≤ s.j ∧ z ≤ s.t ∧ v 3 * h ≤ h
    exact ⟨by omega, hyz, hz, hc₃⟩
  apply subset_convexHull ℝ _
  refine ⟨e, hsupp, ?_⟩
  have hz' : (z : ℝ) = u 2 * s.t := by
    simp only [z, Nat.cast_mul, (hv 2).1]
  have hy' : (y : ℝ) = u 1 * ((s.j : ℝ) - 2 * (u 2 * s.t)) := by
    simp only [y, Nat.cast_mul, Nat.cast_sub hzs, Nat.cast_ofNat, (hv 1).1]
    rw [hz']
  funext i
  change (e i : ℝ) = capParameter s h u i
  rw [he]
  fin_cases i
  · change (↑(v 0 * (s.b - y - z)) : ℝ) =
      u 0 * ((s.b : ℝ) - u 1 * ((s.j : ℝ) - 2 * (u 2 * s.t)) - u 2 * s.t)
    rw [Nat.cast_mul, Nat.cast_sub hzys, Nat.cast_sub hys, (hv 0).1, hy', hz']
  · exact hy'
  · exact hz'
  · change (↑(v 3 * h) : ℝ) = u 3 * h
    rw [Nat.cast_mul, (hv 3).1]
private theorem cap_cube_mem (s : Shape) (h : ℕ) (hs : s.j ≤ s.b)
    (ht : 2 * s.t ≤ s.j) (S : Finset (Fin 4)) (u : Fin 4 → ℝ)
    (hside : ∀ i ∈ S, 0 ≤ u i ∧ u i ≤ 1)
    (hcorner : ∀ i ∉ S, u i = 0 ∨ u i = 1) :
    capParameter s h u ∈ latticeBody (capSupport s h) := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty =>
      exact cap_corner_mem s h hs ht u (fun i => hcorner i (by simp))
  | insert i S hi ih =>
      have updated (b : ℝ) (hb : b = 0 ∨ b = 1) :
          capParameter s h (Function.update u i b) ∈ latticeBody (capSupport s h) := by
        apply ih
        · intro j hj
          have hji : j ≠ i := fun e => hi (e ▸ hj)
          simpa [Function.update_of_ne hji] using hside j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji : j = i
          · subst j
            simpa using hb
          · rw [Function.update_of_ne hji]
            exact hcorner j (by simp [hji, hj])
      have hui := hside i (Finset.mem_insert_self i S)
      rw [capParameter_update s h u i]
      exact convex_convexHull ℝ _ (updated 0 (Or.inl rfl)) (updated 1 (Or.inr rfl))
        (sub_nonneg.mpr hui.2) hui.1 (sub_add_cancel 1 (u i))
private theorem exists_scale {x d : ℝ} (hx : 0 ≤ x) (hxd : x ≤ d) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ u * d = x := by
  by_cases hd : d = 0
  · exact ⟨0, le_rfl, zero_le_one, by linarith⟩
  · have hd' : 0 < d := lt_of_le_of_ne (hx.trans hxd) (Ne.symm hd)
    exact ⟨x / d, div_nonneg hx hd'.le, (div_le_one hd').mpr hxd, div_mul_cancel₀ x hd⟩
private theorem convex_capBody (s : Shape) (h : ℕ) : Convex ℝ (capBody s h) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx, hx₁, hx₂, hx₃, hx₄⟩ := hx
  obtain ⟨hy, hy₁, hy₂, hy₃, hy₄⟩ := hy
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)), ?_, ?_, ?_, ?_⟩
  · change a * x 0 + b * y 0 + (a * x 1 + b * y 1) + (a * x 2 + b * y 2) ≤ s.b
    nlinarith [mul_le_mul_of_nonneg_left hx₁ ha, mul_le_mul_of_nonneg_left hy₁ hb,
      congrArg (fun t : ℝ => t * s.b) hab]
  · change a * x 1 + b * y 1 + 2 * (a * x 2 + b * y 2) ≤ s.j
    nlinarith [mul_le_mul_of_nonneg_left hx₂ ha, mul_le_mul_of_nonneg_left hy₂ hb,
      congrArg (fun t : ℝ => t * s.j) hab]
  · change a * x 2 + b * y 2 ≤ s.t
    nlinarith [mul_le_mul_of_nonneg_left hx₃ ha, mul_le_mul_of_nonneg_left hy₃ hb,
      congrArg (fun t : ℝ => t * s.t) hab]
  · change a * x 3 + b * y 3 ≤ h
    nlinarith [mul_le_mul_of_nonneg_left hx₄ ha, mul_le_mul_of_nonneg_left hy₄ hb,
      congrArg (fun t : ℝ => t * h) hab]
theorem latticeBody_capSupport (s : Shape) (h : ℕ) (hs : s.j ≤ s.b)
    (ht : 2 * s.t ≤ s.j) : latticeBody (capSupport s h) = capBody s h := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_capBody s h)
    rintro x ⟨e, he, rfl⟩
    obtain ⟨he₁, he₂, he₃, he₄⟩ := mem_capSupport.mp he
    refine ⟨fun i => Nat.cast_nonneg _, ?_, ?_, Nat.cast_le.mpr he₃, Nat.cast_le.mpr he₄⟩
    · change (e 0 : ℝ) + e 1 + e 2 ≤ s.b
      exact_mod_cast he₁
    · change (e 1 : ℝ) + 2 * e 2 ≤ s.j
      exact_mod_cast he₂
  · intro x hx
    obtain ⟨hx, hx₁, hx₂, hx₃, hx₄⟩ := hx
    obtain ⟨u₀, hu₀, hv₀, h₀⟩ := exists_scale (hx 0) (show x 0 ≤ s.b - x 1 - x 2 by linarith)
    obtain ⟨u₁, hu₁, hv₁, h₁⟩ := exists_scale (hx 1) (show x 1 ≤ s.j - 2 * x 2 by linarith)
    obtain ⟨u₂, hu₂, hv₂, h₂⟩ := exists_scale (hx 2) hx₃
    obtain ⟨u₃, hu₃, hv₃, h₃⟩ := exists_scale (hx 3) hx₄
    let u : Fin 4 → ℝ := ![u₀, u₁, u₂, u₃]
    have hu : capParameter s h u = x := by
      funext i
      fin_cases i
      · change u₀ * ((s.b : ℝ) - u₁ * ((s.j : ℝ) - 2 * (u₂ * s.t)) - u₂ * s.t) = x 0
        rw [h₂, h₁, h₀]
      · change u₁ * ((s.j : ℝ) - 2 * (u₂ * s.t)) = x 1
        rw [h₂, h₁]
      · exact h₂
      · exact h₃
    rw [← hu]
    apply cap_cube_mem s h hs ht Finset.univ
    · intro i _
      fin_cases i
      · exact ⟨hu₀, hv₀⟩
      · exact ⟨hu₁, hv₁⟩
      · exact ⟨hu₂, hv₂⟩
      · exact ⟨hu₃, hv₃⟩
    · simp
end
end K1_13_5_4_2_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open scoped BigOperators Pointwise
private theorem affineDegree_point {k σ : Type} [Field k] [Finite σ] (x : σ → k) :
    affineDegree (vanishingIdeal k {x}) = 1 := by
  have hker : vanishingIdeal k {x} = RingHom.ker (aeval x : MvPolynomial σ k →ₐ[k] k) := by
    ext p
    rw [RingHom.mem_ker, mem_vanishingIdeal_singleton_iff]
  rw [hker]
  have hs : Function.Surjective (aeval x : MvPolynomial σ k →ₐ[k] k) :=
    fun b => ⟨C b, by simp⟩
  let e := Ideal.quotientKerAlgEquivOfSurjective hs
  let := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  rw [affineDegree_eq_finrank, e.toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one]
theorem ratio_image_degree {k σ τ : Type} [Field k] [Finite σ] [Finite τ]
    (A : Set (σ → k)) (I : Ideal (MvPolynomial σ k)) (hI : I = vanishingIdeal k A)
    (hprime : I.IsPrime) (hdim : (affineHilbertPolynomial I).natDegree = 1)
    (hone : 1 ≤ affineDegree I) (D : MvPolynomial σ k) (N : τ → MvPolynomial σ k)
    (hD : D.totalDegree ≤ 1) (hN : ∀ i, (N i).totalDegree ≤ 1)
    (hnonzero : ∀ x ∈ A, eval x D ≠ 0) :
    ∃ Q : Ideal (MvPolynomial τ k), Q.IsPrime ∧ (affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      affineDegree Q ≤ affineDegree I ∧
      ∀ x ∈ A, (fun i => eval x (N i) / eval x D) ∈ zeroLocus k Q := by
  have hA : A.Nonempty := by
    by_contra! h
    exact hprime.ne_top (by rw [hI, h, vanishingIdeal_empty])
  obtain ⟨x₀, hx₀⟩ := hA
  let e : MvPolynomial σ k →ₐ[k] (A → k) := AlgHom.pi fun x => aeval x.val
  have he : I = RingHom.ker e := by
    ext p
    rw [hI, mem_vanishingIdeal_iff, RingHom.mem_ker, _root_.funext_iff]
    exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
  clear hI
  subst I
  let I := RingHom.ker e
  let : I.IsPrime := hprime
  change (affineHilbertPolynomial I).natDegree = 1 at hdim
  change 1 ≤ affineDegree I at hone
  let R := MvPolynomial σ k ⧸ I
  let j : R →ₐ[k] (A → k) := Ideal.kerLiftAlg e
  have hj : Function.Injective j := Ideal.kerLiftAlg_injective e
  let dr : R := Ideal.Quotient.mk I D
  let d : A → k := e D
  have hjd : j dr = d := rfl
  have hd : IsUnit d := Pi.isUnit_iff.mpr fun x => isUnit_iff_ne_zero.mpr (hnonzero _ x.property)
  let y (i : τ) (x : A) : k := eval x.val (N i) / eval x.val D
  let φ : MvPolynomial τ k →ₐ[k] (A → k) := aeval y
  let Q := RingHom.ker φ
  have hφ (p : MvPolynomial τ k) (x : A) :
      φ p x = aeval (fun i => y i x) p := by
    let π := Pi.evalAlgHom k (fun _ : A => k) x
    have h : π.comp φ = aeval (fun i => y i x) := by
      apply algHom_ext
      intro i
      simp [φ, π]
    exact DFunLike.congr_fun h p
  have hy (i : τ) : d * y i = e (N i) := by
    ext x
    change eval x.val D * (eval x.val (N i) / eval x.val D) = eval x.val (N i)
    rw [mul_comm, div_mul_cancel₀ _ (hnonzero _ x.property)]
  let V (m : ℕ) : Submodule k (A → k) := (quotientDegreeLE I m).map j.toLinearMap
  let W (m : ℕ) : Submodule k (A → k) := (V m).comap (LinearMap.mulLeft k (d ^ m))
  have hW (m : ℕ) (z : A → k) :
      z ∈ W m ↔ ∃ r ∈ quotientDegreeLE I m, j r = d ^ m * z := by
    simp only [W, V, Submodule.mem_comap, Submodule.mem_map, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply]
    rfl
  have hdr_pow (n : ℕ) : dr ^ n ∈ quotientDegreeLE I n := by
    dsimp only [dr]
    rw [← map_pow]
    exact mk_mem_quotientDegreeLE ((totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left n hD))
  have hmono : Monotone W := by
    intro m n hmn z hz
    obtain ⟨r, hr, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨dr ^ (n - m) * r, ?_, ?_⟩
    · simpa only [Nat.sub_add_cancel hmn] using
        mul_mem_quotientDegreeLE (hdr_pow (n - m)) hr
    · rw [map_mul, map_pow, hjd, heq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
  have hmul (i : τ) (m : ℕ) (z : A → k) (hz : z ∈ W m) :
      y i * z ∈ W (m + 1) := by
    obtain ⟨r, hr, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨r * Ideal.Quotient.mk I (N i),
      mul_mem_quotientDegreeLE hr (mk_mem_quotientDegreeLE (hN i)), ?_⟩
    rw [map_mul, heq, Ideal.kerLiftAlg_mk, pow_succ, ← hy]
    ring
  have hclear (p : MvPolynomial τ k) (m : ℕ) (hp : p.totalDegree ≤ m) :
      ∃ r ∈ quotientDegreeLE I m, j r = d ^ m * φ p := by
    have hz : (1 : A → k) ∈ W 0 :=
      (hW _ _).mpr ⟨1, one_mem_quotientDegreeLE I _, by simp⟩
    have h := aeval_mem_of_forall_mul_mem y hmono hz hmul hp
    rw [one_mul] at h
    exact (hW _ _).mp h
  have hQ : Q.IsPrime := by
    apply Ideal.isPrime_iff.mpr
    constructor
    · intro htop
      have hz : φ 1 = 0 := RingHom.mem_ker.mp (show 1 ∈ Q from htop ▸ Submodule.mem_top)
      rw [map_one] at hz
      exact one_ne_zero (congrFun hz ⟨x₀, hx₀⟩)
    · intro p q hpq
      have hz := RingHom.mem_ker.mp hpq
      change φ (p * q) = 0 at hz
      rw [map_mul] at hz
      obtain ⟨r, _, hr⟩ := hclear p _ le_rfl
      obtain ⟨s, _, hs⟩ := hclear q _ le_rfl
      have hrs : r * s = 0 := hj (by
        rw [map_mul, hr, hs, map_zero]
        calc
          _ = (d ^ p.totalDegree * d ^ q.totalDegree) * (φ p * φ q) := by ring
          _ = 0 := by rw [hz, mul_zero])
      rcases mul_eq_zero.mp hrs with hr₀ | hs₀
      · left
        apply RingHom.mem_ker.mpr
        exact (hd.pow _).mul_left_cancel (by rw [← hr, hr₀, map_zero, mul_zero])
      · right
        apply RingHom.mem_ker.mpr
        exact (hd.pow _).mul_left_cancel (by rw [← hs, hs₀, map_zero, mul_zero])
  have hgrowth (m : ℕ) : affineHilbertFunction Q m ≤ affineHilbertFunction I m := by
    let ι := Ideal.kerLiftAlg φ
    have hm (a : quotientDegreeLE Q m) : d ^ m * ι a.1 ∈ V m := by
      obtain ⟨p, hp, hp'⟩ := mem_quotientDegreeLE.mp a.2
      obtain ⟨r, hr, heq⟩ := hclear p m hp
      refine Submodule.mem_map.mpr ⟨r, hr, ?_⟩
      rw [AlgHom.toLinearMap_apply, ← hp', Ideal.kerLiftAlg_mk, heq]
    let l : quotientDegreeLE Q m →ₗ[k] V m :=
      (((LinearMap.mulLeft k (d ^ m)).comp ι.toLinearMap).domRestrict
        (quotientDegreeLE Q m)).codRestrict (V m) hm
    have hl : Function.Injective l := by
      intro a b hab
      have h : d ^ m * ι a.1 = d ^ m * ι b.1 := congrArg Subtype.val hab
      exact Subtype.ext (Ideal.kerLiftAlg_injective φ ((hd.pow _).mul_left_cancel h))
    exact (LinearMap.finrank_le_finrank_of_injective hl).trans (Submodule.finrank_map_le _ _)
  have hle : ∀ᶠ m : ℕ in Filter.atTop,
      (affineHilbertPolynomial Q).eval (m : ℚ) ≤ (affineHilbertPolynomial I).eval (m : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial Q,
      eventually_eval_affineHilbertPolynomial I] with m hq hi
    rw [hq, hi]
    exact_mod_cast hgrowth m
  obtain ⟨hdegree, hcoeff⟩ := Polynomial.natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg Q) hle
  have hcover (x : A) : (fun i => y i x) ∈ zeroLocus k Q := by
    intro p hp
    rw [← hφ p x, RingHom.mem_ker.mp hp]
    rfl
  refine ⟨Q, hQ, hdegree.trans_eq hdim, ?_, fun x hx => hcover ⟨x, hx⟩⟩
  by_cases heq : (affineHilbertPolynomial Q).natDegree = (affineHilbertPolynomial I).natDegree
  · rw [affineDegree, affineDegree, heq]
    exact mul_le_mul_of_nonneg_left (hcoeff heq) (Nat.cast_nonneg _)
  · have hzero : (affineHilbertPolynomial Q).natDegree = 0 := by omega
    let := hQ
    let := natDegree_affineHilbertPolynomial_eq_zero_iff.mp hzero
    have hmax := Ideal.Quotient.maximal_of_isField Q (IsField.of_isDomain_of_finite k _)
    have hpoint : Q ≤ vanishingIdeal k {(fun i => y i ⟨x₀, hx₀⟩)} := by
      intro p hp
      exact (mem_vanishingIdeal_singleton_iff _ _).mpr (hcover ⟨x₀, hx₀⟩ p hp)
    have hprime' : (vanishingIdeal k {(fun i => y i ⟨x₀, hx₀⟩)}).IsPrime := inferInstance
    rw [hmax.eq_of_le hprime'.ne_top hpoint, affineDegree_point]
    exact hone
private theorem separator_box {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors f)
    (i : Fin n) : InLiftedBox (liftRow (genericRow (separant (f i)))) lowBox 0 := by
  classical
  intro a ha
  rw [liftRow, support_rename_of_injective (Fin.castSucc_injective 3)] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hs : b ∈ (separant (f i)).support := support_map_subset _ _ hb
  let m : Fin 3 →₀ ℕ := b + Finsupp.single 2 1
  have hm : m ∈ (f i).support := by
    rw [MvPolynomial.mem_support_iff, separant, coeff_pderiv] at hs
    exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs)
  have hb₀ : m.degree ≤ lowBox.b :=
    (le_totalDegree hm).trans ((Finset.single_le_sum (fun j _ => Nat.zero_le ((f j).totalDegree))
      (Finset.mem_univ i)).trans hf.total)
  have hj₀ : (m.sum fun j a => j.val * a) ≤ lowBox.j :=
    (Finset.le_sup hm).trans ((Finset.single_le_sum (fun j _ => Nat.zero_le (indexDegree (f j)))
      (Finset.mem_univ i)).trans hf.index)
  have ht₀ : m 2 ≤ lowBox.t :=
    (monomial_le_degreeOf 2 hm).trans ((Finset.single_le_sum
      (fun j _ => Nat.zero_le ((f j).degreeOf 2)) (Finset.mem_univ i)).trans hf.top)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hb₀
  rw [Finsupp.sum_fintype _ _ (fun j => mul_zero j.val), Fin.sum_univ_three] at hj₀
  have h0 : Finsupp.mapDomain Fin.castSucc b 0 = b 0 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 0
  have h1 : Finsupp.mapDomain Fin.castSucc b 1 = b 1 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 1
  have h2 : Finsupp.mapDomain Fin.castSucc b 2 = b 2 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 2
  have h3 : Finsupp.mapDomain Fin.castSucc b 3 = 0 :=
    Finsupp.mapDomain_of_notMem_range b _ (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)
  simp only [h0, h1, h2, h3, le_refl, and_true]
  simp [m, Finsupp.add_apply] at hb₀ hj₀ ht₀
  omega
theorem box_mono {B : GeoRow 4} {s t : Shape} {h k : ℕ}
    (hb : s.b ≤ t.b) (hj : s.j ≤ t.j) (ht : s.t ≤ t.t) (hh : h ≤ k)
    (hB : InLiftedBox B s h) : InLiftedBox B t k := by
  intro a ha
  obtain ⟨hb', hj', ht', hh'⟩ := hB a ha
  exact ⟨hb'.trans hb, hj'.trans hj, ht'.trans ht, hh'.trans hh⟩
end
end K1_13_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open scoped BigOperators
theorem lift_generic_ne_zero {f : Row 3} (hf : f ≠ 0) :
    liftRow (genericRow f) ≠ 0 := by
  have hg : genericRow f ≠ 0 := by
    simpa only [genericRow, map_zero] using (map_injective _ genericCoeff_injective).ne hf
  simpa only [liftRow, map_zero] using
    (rename_injective Fin.castSucc (Fin.castSucc_injective 3)).ne hg
end
end K1_13_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial Filter MeasureTheory
open scoped BigOperators Pointwise Topology
def c1 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent),
    (∀ i, 0 ∈ A i) → Module.Finite (CoefficientField A) (GenericQuotient A) →
    ∀ (f : Fin 4 → GeoRow 4), (∀ i, (f i).support ⊆ A i) →
    ∀ points : Finset JetPoint,
      (∀ y ∈ points, pointIdeal y ∈ (cutIdeal f).minimalPrimes) →
      (∑ y ∈ points, (pointLength (cutIdeal f) y).toNat) ≤
        Module.finrank (CoefficientField A) (GenericQuotient A)
def c2 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    (∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) →
    Module.Finite (CoefficientField A) (GenericQuotient A) ∧
      ∃ q : ℕ, ∀ n : ℕ,
        (Module.finrank (CoefficientField A) (GenericQuotient A) : ℝ) * (n : ℝ)^4 =
          ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
            (-1 : ℝ) ^ (4 - S.card) * (exponentCount A (corner q n S) : ℝ)
def c3 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) → (∀ i, Downward (A i)) →
    ∀ (q : ℕ) (S : Finset (Fin 4)),
      Tendsto (fun n : ℕ => (exponentCount A (corner q n S) : ℝ) / (n : ℝ)^4)
        atTop (𝓝 (volume (∑ i ∈ S, latticeBody (A i))).toReal)
theorem mixed_eq_generic (h2 : c2) (h3 : c3)
    (A : Fin 4 → Finset Exponent) (hzero : ∀ i, 0 ∈ A i)
    (hdown : ∀ i, Downward (A i))
    (hcoords : ∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) :
    Module.Finite (CoefficientField A) (GenericQuotient A) ∧
      (Module.finrank (CoefficientField A) (GenericQuotient A) : ℝ) =
        mixedVolume4 (fun i => latticeBody (A i)) := by
  obtain ⟨hfinite, q, hq⟩ := h2 A hzero hcoords
  refine ⟨hfinite, ?_⟩
  unfold mixedVolume4
  apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    (f := fun n : ℕ => ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * ((exponentCount A (corner q n S) : ℝ) / (n : ℝ)^4))
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ)^4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
    symm
    calc
      _ = (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
          (-1 : ℝ) ^ (4 - S.card) * (exponentCount A (corner q n S) : ℝ)) / (n : ℝ)^4 := by
        simp only [Finset.sum_div, mul_div_assoc]
      _ = _ := by rw [← hq n, mul_div_cancel_right₀ _ hn']
  · exact tendsto_finsetSum _ fun S _ => (h3 A hzero hdown q S).const_mul _
theorem downSupport_downward (F : GeoRow 4) : Downward (downSupport F) := by
  intro a b ha hab
  obtain ⟨e, he, hae⟩ := mem_downSupport.mp ha
  exact mem_downSupport.mpr ⟨e, he, hab.trans hae⟩
theorem capSupport_downward (s : Shape) (h : ℕ) : Downward (capSupport s h) := by
  intro a b ha hb
  have ha' := mem_capSupport.mp ha
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := ha'
  apply mem_capSupport.mpr
  exact ⟨(Nat.add_le_add (Nat.add_le_add (hb 0) (hb 1)) (hb 2)).trans hb₁,
    (Nat.add_le_add (hb 1) (Nat.mul_le_mul_left 2 (hb 2))).trans hb₂,
    (hb 2).trans hb₃, (hb 3).trans hb₄⟩
theorem zero_mem_capSupport (s : Shape) (h : ℕ) : (0 : Exponent) ∈ capSupport s h :=
  mem_capSupport.mpr (by simp [boxExponents])
end
end K1_13_5_4_2_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2
noncomputable section
open K1_13_5_4_2_4 MvPolynomial
open scoped Pointwise
abbrev Degree := Fin 4 → ℕ
abbrev Row (A : Fin 4 → Finset Exponent) := MvPolynomial (Fin 4) (CoefficientField A)
def exponentSet (A : Fin 4 → Finset Exponent) (d : Degree) : Set Exponent :=
  ∑ i : Fin 4, d i • (↑(A i) : Set Exponent)
def piece (A : Fin 4 → Finset Exponent) (d : Degree) : Submodule (CoefficientField A) (Row A) :=
  Submodule.span (CoefficientField A)
    (Set.range fun a : ↥(exponentSet A d) => monomial a.1 (1 : CoefficientField A))
def shift (d : Degree) (i : Fin 4) (n : ℕ) : Degree := d + Pi.single i n
def prefixIdeal (A : Fin 4 → Finset Exponent) (k : ℕ) : Ideal (Row A) :=
  Ideal.span (genericEquation A '' {i : Fin 4 | (i : ℕ) < k})
end
end K1_13_5_4_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2
noncomputable section
open K1_13_5_4_2_4 MvPolynomial
open scoped Pointwise
variable {A : Fin 4 → Finset Exponent}
private theorem finite_nsmul (s : Set Exponent) (hs : s.Finite) (n : ℕ) : (n • s).Finite := by
  induction n with
  | zero => simpa only [zero_nsmul] using (Set.finite_zero : (0 : Set Exponent).Finite)
  | succ n ih => rw [succ_nsmul]; exact ih.add hs
private theorem exponentSet_finite (A : Fin 4 → Finset Exponent) (d : Degree) :
    (exponentSet A d).Finite := by
  classical
  unfold exponentSet
  have h (s : Finset (Fin 4)) : (∑ i ∈ s, d i • (↑(A i) : Set Exponent)).Finite := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s nhi ih =>
      rw [Finset.sum_insert nhi]
      exact (finite_nsmul _ (A i).finite_toSet _).add ih
  exact h _
instance (d : Degree) : Module.Finite (CoefficientField A) (piece A d) := by
  classical
  let _ := (exponentSet_finite A d).fintype
  exact Module.Finite.span_of_finite _ (Set.finite_range _)
private theorem monomial_mem_piece {d : Degree} {a : Exponent} (ha : a ∈ exponentSet A d)
    (c : CoefficientField A) : monomial a c ∈ piece A d := by
  have h : monomial a (1 : CoefficientField A) ∈ piece A d :=
    Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  simpa only [smul_monomial, smul_eq_mul, mul_one] using (piece A d).smul_mem c h
private theorem exponentSet_add (A : Fin 4 → Finset Exponent) (d e : Degree) :
    exponentSet A (d + e) = exponentSet A d + exponentSet A e := by
  simp only [exponentSet, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]
private theorem exponentSet_single (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    exponentSet A (Pi.single i 1) = A i := by
  classical
  unfold exponentSet
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_nsmul]
  · simp
theorem equation_mul_mem_piece (i : Fin 4) {d : Degree} {p : Row A}
    (hp : p ∈ piece A d) : genericEquation A i * p ∈ piece A (shift d i 1) := by
  change p ∈ Submodule.span _ _ at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    rw [genericEquation, Finset.sum_mul]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [monomial_mul_monomial]
    apply monomial_mem_piece
    rw [shift, exponentSet_add, exponentSet_single]
    exact Set.mem_add.mpr ⟨a, a.2, b, b.2, add_comm _ _⟩
  | zero => simp
  | add p r _ _ hp hr => simpa only [mul_add] using (piece A _).add_mem hp hr
  | smul c p _ hp => simpa only [mul_smul_comm] using (piece A _).smul_mem c hp
private theorem zero_mem_exponentSet (hz : ∀ i, 0 ∈ A i) (d : Degree) :
    (0 : Exponent) ∈ exponentSet A d := by
  classical
  have hn (i : Fin 4) (n : ℕ) : (0 : Exponent) ∈ n • (↑(A i) : Set Exponent) := by
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul]; exact Set.mem_add.mpr ⟨0, ih, 0, hz i, zero_add _⟩
  have h (s : Finset (Fin 4)) : (0 : Exponent) ∈ ∑ i ∈ s, d i • (↑(A i) : Set Exponent) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s nhi ih =>
      rw [Finset.sum_insert nhi]
      exact Set.mem_add.mpr ⟨0, hn i _, 0, ih, zero_add _⟩
  exact h _
private theorem exponentSet_mono (hz : ∀ i, 0 ∈ A i) {d e : Degree} (h : d ≤ e) :
    exponentSet A d ⊆ exponentSet A e := by
  have he : e = d + (e - d) := by
    funext i
    exact (Nat.add_sub_of_le (h i)).symm
  intro a ha
  rw [he, exponentSet_add]
  exact Set.mem_add.mpr ⟨a, ha, 0, zero_mem_exponentSet hz _, add_zero _⟩
theorem piece_mono (hz : ∀ i, 0 ∈ A i) {d e : Degree} (h : d ≤ e) : piece A d ≤ piece A e := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact monomial_mem_piece (exponentSet_mono hz h a.2) _
private theorem monomial_eventually_mem
    (hz : ∀ i, 0 ∈ A i) (hv : ∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i)
    (a : Exponent) : ∃ n : ℕ, a ∈ exponentSet A (fun _ => n) := by
  classical
  have hadd {a b : Exponent} {m n : ℕ} (ha : a ∈ exponentSet A (fun _ => m))
      (hb : b ∈ exponentSet A (fun _ => n)) : a + b ∈ exponentSet A (fun _ => m + n) := by
    change _ ∈ exponentSet A ((fun _ => m) + (fun _ => n))
    rw [exponentSet_add]
    exact Set.mem_add.mpr ⟨a, ha, b, hb, rfl⟩
  have hvar (j : Fin 4) : Finsupp.single j 1 ∈ exponentSet A (fun _ => 1) := by
    obtain ⟨i, hi⟩ := hv j
    exact exponentSet_mono hz (show Pi.single i 1 ≤ fun _ => 1 by
      intro l; by_cases h : l = i <;> simp [h, Pi.single_eq_of_ne])
      (by rw [exponentSet_single]; exact Finset.mem_coe.mpr hi)
  have hsingle (j : Fin 4) (m : ℕ) : Finsupp.single j m ∈ exponentSet A (fun _ => m) := by
    induction m with
    | zero => simpa using zero_mem_exponentSet hz (fun _ => 0)
    | succ m ih =>
      rw [Finsupp.single_add]
      exact hadd ih (hvar j)
  have hsum (s : Finset (Fin 4)) :
      (∑ j ∈ s, Finsupp.single j (a j)) ∈ exponentSet A (fun _ => ∑ j ∈ s, a j) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using zero_mem_exponentSet hz (fun _ => 0)
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact hadd (hsingle j _) ih
  refine ⟨∑ j : Fin 4, a j, ?_⟩
  have ha : (∑ j : Fin 4, Finsupp.single j (a j)) = a := by
    ext j
    simp
  simpa only [ha] using hsum Finset.univ
theorem piece_exhaustive (hz : ∀ i, 0 ∈ A i)
    (hv : ∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) (p : Row A) :
    ∃ n : ℕ, p ∈ piece A (fun _ => n) := by
  classical
  choose n hn using monomial_eventually_mem hz hv
  refine ⟨p.support.sup n, ?_⟩
  have hsum : (∑ a ∈ p.support, monomial a (p.coeff a)) ∈ piece A (fun _ => p.support.sup n) := by
    refine Submodule.sum_mem _ fun a ha => monomial_mem_piece ?_ _
    exact exponentSet_mono hz (show (fun _ => n a) ≤ (fun _ => p.support.sup n : Degree) from
      fun _ => Finset.le_sup ha) (hn a)
  rwa [← p.as_sum] at hsum
theorem finrank_piece (A : Fin 4 → Finset Exponent) (d : Degree) :
    Module.finrank (CoefficientField A) (piece A d) = exponentCount A d := by
  classical
  let _ := (exponentSet_finite A d).fintype
  let m : ↥(exponentSet A d) → Row A := fun a => monomial a.1 1
  have h : LinearIndependent (CoefficientField A) m :=
    (basisMonomials (Fin 4) (CoefficientField A)).linearIndependent.comp
      (fun a : ↥(exponentSet A d) => a.1) Subtype.val_injective
  change Module.finrank (CoefficientField A) (Submodule.span _ (Set.range m)) = (exponentSet A d).ncard
  exact (finrank_span_eq_card h).trans (Set.fintypeCard_eq_ncard _)
end
end K1_13_5_4_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2
noncomputable section
private def shiftSet (d : Degree) (n : ℕ) (S : Finset (Fin 4)) : Degree :=
  fun i => d i + if i ∈ S then n else 0
private def boxDiff (F : Degree → ℝ) (J : Finset (Fin 4)) (d : Degree) (n : ℕ) : ℝ :=
  ∑ S ∈ J.powerset, (-1 : ℝ) ^ (J.card - S.card) * F (shiftSet d n S)
private theorem shift_le (d : Degree) (i : Fin 4) (t : ℕ) : d ≤ shift d i t :=
  fun _ => Nat.le_add_right _ _
private theorem shiftSet_le (d : Degree) (n : ℕ) (S : Finset (Fin 4)) : d ≤ shiftSet d n S :=
  fun _ => Nat.le_add_right _ _
private theorem shift_succ (d : Degree) (i : Fin 4) (t : ℕ) :
    shift d i (t + 1) = shift (shift d i t) i 1 := by
  funext j
  by_cases h : j = i <;> simp [shift, h, Pi.single_eq_of_ne, add_assoc]
private theorem shiftSet_insert {i : Fin 4} {S : Finset (Fin 4)} (hi : i ∉ S)
    (d : Degree) (n : ℕ) : shiftSet d n (insert i S) = shift (shiftSet d n S) i n := by
  funext j
  by_cases h : j = i <;> simp [shift, shiftSet, hi, h, Pi.single_eq_of_ne]
private theorem shift_comm_shiftSet (d : Degree) (i : Fin 4) (t n : ℕ) (S : Finset (Fin 4)) :
    shift (shiftSet d n S) i t = shiftSet (shift d i t) n S := by
  funext j
  simp only [shift, shiftSet, Pi.add_apply]
  ac_rfl
private theorem line_sum {F G : Degree → ℝ} {q : ℕ} {i : Fin 4}
    (h : ∀ d : Degree, (∀ j, q ≤ d j) → F (shift d i 1) - F d = G d)
    (d : Degree) (hd : ∀ j, q ≤ d j) (n : ℕ) :
    F (shift d i n) - F d = ∑ t ∈ Finset.range n, G (shift d i t) := by
  induction n with
  | zero => simp [shift]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, shift_succ,
      ← h (shift d i n) (fun j => (hd j).trans (shift_le d i n j))]
    ring
private theorem boxDiff_step {F G : Degree → ℝ} {q : ℕ} {i : Fin 4} {J : Finset (Fin 4)}
    (hi : i ∉ J) (h : ∀ d : Degree, (∀ j, q ≤ d j) → F (shift d i 1) - F d = G d)
    (d : Degree) (hd : ∀ j, q ≤ d j) (n : ℕ) :
    boxDiff F (insert i J) d n = ∑ t ∈ Finset.range n, boxDiff G J (shift d i t) n := by
  unfold boxDiff
  rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  have hiS : i ∉ S := fun hh => hi (hsub hh)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hiS,
    Nat.add_sub_add_right, show J.card + 1 - S.card = (J.card - S.card) + 1 by omega,
    pow_succ, shiftSet_insert hiS]
  have hs : (-1 : ℝ) ^ (J.card - S.card) * (-1) * F (shiftSet d n S) +
      (-1 : ℝ) ^ (J.card - S.card) * F (shift (shiftSet d n S) i n) =
      (-1 : ℝ) ^ (J.card - S.card) *
        (F (shift (shiftSet d n S) i n) - F (shiftSet d n S)) := by ring
  rw [hs, line_sum h _ (fun j => (hd j).trans (shiftSet_le d n S j)), Finset.mul_sum]
  simp only [shift_comm_shiftSet]
theorem fourfold_telescoping (H : ℕ → Degree → ℝ) (C : ℝ) (q : ℕ)
    (hstep : ∀ (i : Fin 4) (d : Degree), (∀ j, q ≤ d j) →
      H i.val (shift d i 1) - H i.val d = H (i.val + 1) (shift d i 1))
    (htop : ∀ d : Degree, (∀ j, q ≤ d j) → H 4 d = C) (n : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * H 0 (K1_13_5_4_2_4.corner q n S)) = C * (n : ℝ)^4 := by
  let tail (k : ℕ) : Finset (Fin 4) := Finset.univ.filter fun i => k ≤ i.val
  have htail (i : Fin 4) : tail i.val = insert i (tail (i.val + 1)) := by
    ext j
    simp only [tail, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases he : j = i
      · exact Or.inl he
      · exact Or.inr (by have hne := Fin.val_ne_of_ne he; omega)
    · rintro (rfl | h)
      · exact le_rfl
      · omega
  have hnot (i : Fin 4) : i ∉ tail (i.val + 1) := by simp [tail]
  have ht4 : tail 4 = ∅ := by ext i; simp [tail, not_le.mpr i.isLt]
  have ht0 : tail 0 = Finset.univ := by simp [tail]
  have hbox (k : ℕ) (hk : k ≤ 4) : ∀ d : Degree, (∀ j, q ≤ d j) →
      boxDiff (H k) (tail k) d n = C * (n : ℝ)^(4 - k) := by
    refine Nat.decreasingInduction' (m := k) (n := 4)
      (motive := fun l => ∀ d : Degree, (∀ j, q ≤ d j) →
        boxDiff (H l) (tail l) d n = C * (n : ℝ)^(4 - l)) ?_ hk ?_
    · intro l hl _ ih d hd
      let i : Fin 4 := ⟨l, hl⟩
      have hi : tail l = insert i (tail (l + 1)) := htail i
      rw [hi, boxDiff_step (hnot i) (hstep i) d hd]
      have he (t : ℕ) : boxDiff (fun e => H (l + 1) (shift e i 1))
          (tail (l + 1)) (shift d i t) n = C * (n : ℝ)^(4 - (l + 1)) := by
        unfold boxDiff
        simpa only [boxDiff, shift_comm_shiftSet] using
          ih (shift (shift d i t) i 1) (fun j =>
            ((hd j).trans (shift_le d i t j)).trans (shift_le (shift d i t) i 1 j))
      calc
        _ = ∑ _t ∈ Finset.range n, C * (n : ℝ)^(4 - (l + 1)) :=
          Finset.sum_congr rfl fun t _ => he t
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [show 4 - l = (4 - (l + 1)) + 1 by omega, pow_succ]
          ring
    · intro d hd
      have he : shiftSet d n ∅ = d := by funext j; simp [shiftSet]
      simpa [boxDiff, ht4, he] using htop d hd
  have h := hbox 0 (by decide) (fun _ => q) (fun _ => le_rfl)
  have hc (S : Finset (Fin 4)) : shiftSet (fun _ => q) n S = K1_13_5_4_2_4.corner q n S := rfl
  simpa [boxDiff, ht0, hc] using h
end
end K1_13_5_4_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
def TangentStable (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  ∀ b : Row 3, genericRow b ∈ P → genericRow (tangentNumerator f b) ∈ P
def pointEval (y : Fin 3 → GeometricX) : Row 3 →+* GeometricX :=
  (MvPolynomial.eval y).comp (MvPolynomial.map genericCoeff)
def centre {F : Type*} [Field F] (e : Row 3 →+* F) : F :=
  e (MvPolynomial.C Polynomial.X)
def centredJet {F : Type*} [Field F] (f : Row 3) (e : Row 3 →+* F) : ℕ → F
  | 0 => e (MvPolynomial.X 0)
  | 1 => e (MvPolynomial.X 1)
  | 2 => e (MvPolynomial.X 2)
  | k + 3 => 2 * e (compatibilityNumerator f k) /
      (((k + 3).factorial : F) * e (separant f) ^ (2 * k + 1))
def taylorAt {F : Type*} [Field F] (f : Row 3) (e : Row 3 →+* F) : (Polynomial F) :=
  Polynomial.taylor (-centre e)
    (∑ j : Fin taylorLength, Polynomial.monomial j.val (centredJet f e j.val))
def reconstructAt (f : Row 3) (y : Fin 3 → GeometricX) : Coefficients :=
  fun j => (taylorAt f (pointEval y)).coeff j.val
def coefficientImage (f : Row 3) (P : Ideal (GeoRow 3)) : Set Coefficients :=
  reconstructAt f '' regularLocus f P
def curveIdeal (f : Row 3) (P : Ideal (GeoRow 3)) : CoefficientIdeal :=
  MvPolynomial.vanishingIdeal GeometricX (coefficientImage f P)
def trajectory {A : Type*} [CommRing A] (k : Geom →+* A) (f : Row 3) (U : (Polynomial A)) :
    (Polynomial A) :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom k) (fun i => hasseDeriv i.val U) f
end
end K1_13_5_4_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
namespace K1_13_5_4_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
theorem coefficientPolynomial_reconstructAt (f : Row 3) (y : Fin 3 → GeometricX) :
    coefficientPolynomial (reconstructAt f y) = taylorAt f (pointEval y) := by
  have e0 : coefficientPolynomial (reconstructAt f y) =
      ∑ j : Fin taylorLength, Polynomial.monomial j.val (reconstructAt f y j) := rfl
  generalize hU : taylorAt f (pointEval y) = U
  have hdeg : U.natDegree ≤ taylorLength - 1 := by
    rw [← hU]
    dsimp [taylorAt]
    rw [Polynomial.natDegree_taylor]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt i.isLt)
  have e1 : ∀ j : Fin taylorLength, reconstructAt f y j = U.coeff j.val := fun j => by
    rw [← hU]; rfl
  rw [e0, Finset.sum_congr rfl (fun j _ => by rw [e1 j]),
    Fin.sum_univ_eq_sum_range (fun j => Polynomial.monomial j (U.coeff j))]
  exact (Polynomial.as_sum_range' U taylorLength (Nat.lt_succ_of_le hdeg)).symm
private theorem taylor_inverse_coefficient {A : Type*} [CommRing A] {L : ℕ}
    (x : A) (a : ℕ → A) (j : Fin L) :
    (hasseDeriv j.val (Polynomial.taylor (-x)
      (∑ l : Fin L, Polynomial.monomial l.val (a l.val)))).eval x = a j.val := by
  rw [← Polynomial.taylor_coeff, Polynomial.taylor_taylor, add_neg_cancel,
    Polynomial.taylor_zero, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply, Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
private theorem centredJet_initial (f : Row 3) (e : Row 3 →+* GeometricX) (i : Fin 3) :
    centredJet f e i.val = e (MvPolynomial.X i) := by
  fin_cases i <;> rfl
private theorem three_lt_length : 3 < taylorLength := by
  change 3 < 133672
  omega
theorem recover_initial (f : Row 3) (y : Fin 3 → GeometricX) (i : Fin 3) :
    (hasseDeriv i.val (taylorAt f (pointEval y))).eval (genericCoeff Polynomial.X) =
      y i := by
  have hx : centre (pointEval y) = genericCoeff Polynomial.X := by
    simp [centre, pointEval]
  let j : Fin taylorLength := ⟨i.val, i.isLt.trans three_lt_length⟩
  calc
    _ = (hasseDeriv j.val (taylorAt f (pointEval y))).eval (centre (pointEval y)) :=
      congrArg (fun x => (hasseDeriv i.val (taylorAt f (pointEval y))).eval x) hx.symm
    _ = centredJet f (pointEval y) j.val :=
      taylor_inverse_coefficient (centre (pointEval y)) (centredJet f (pointEval y)) j
    _ = pointEval y (MvPolynomial.X i) := centredJet_initial f (pointEval y) i
    _ = y i := by simp [pointEval]
theorem eval_abscissa :
    (Polynomial.evalRingHom (genericCoeff Polynomial.X)).comp
      (Polynomial.mapRingHom (algebraMap Geom GeometricX)) = genericCoeff := by
  apply Polynomial.ringHom_ext
  · intro a
    change ((Polynomial.C a).map (algebraMap Geom GeometricX)).eval
      (genericCoeff Polynomial.X) = genericCoeff (Polynomial.C a)
    rw [Polynomial.map_C, Polynomial.eval_C, ← Polynomial.algebraMap_eq]
    rfl
  · simp
theorem eval_trajectory_at_centre (f b : Row 3) (y : Fin 3 → GeometricX) :
    (extendedAtJet b (taylorAt f (pointEval y))).eval (genericCoeff Polynomial.X) =
      MvPolynomial.eval y (genericRow b) := by
  unfold extendedAtJet genericRow
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map]
  change (Polynomial.evalRingHom (genericCoeff Polynomial.X)) (MvPolynomial.eval₂ _ _ _) = _
  rw [MvPolynomial.hom_eval₂, eval_abscissa]
  simp only [Polynomial.coe_evalRingHom, recover_initial]
theorem regularLocus_nonempty (f : Row 3) (P : Ideal (GeoRow 3)) (hp : P.IsPrime)
    (hsep : genericRow (separant f) ∉ P) : (regularLocus f P).Nonempty := by
  classical
  let _ := hp
  by_contra hn
  apply hsep
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := GeometricX) P]
  intro y hy
  change MvPolynomial.eval y (genericRow (separant f)) = 0
  by_contra he
  exact hn ⟨y, hy, he⟩
private def universalTrajectory (f : Row 3) : (Polynomial (GeoRow taylorLength)) :=
  trajectory ((MvPolynomial.C : GeometricX →+* GeoRow taylorLength).comp
    (algebraMap Geom GeometricX)) f
    (∑ j : Fin taylorLength, Polynomial.monomial j.val (MvPolynomial.X j))
private theorem map_trajectory {A B : Type*} [CommRing A] [CommRing B]
    (h : A →+* B) (k : Geom →+* A) (f : Row 3) (U : (Polynomial A)) :
    (trajectory k f U).map h = trajectory (h.comp k) f (U.map h) := by
  unfold trajectory
  change (Polynomial.mapRingHom h) (MvPolynomial.eval₂ _ _ _) = _
  rw [MvPolynomial.hom_eval₂]
  simp only [Polynomial.coe_mapRingHom, Polynomial.hasseDeriv_map, Polynomial.mapRingHom_comp]
private theorem eval_universalTrajectory (f : Row 3) (a : Coefficients) :
    (universalTrajectory f).map (MvPolynomial.eval a) =
      extendedAtJet f (coefficientPolynomial a) := by
  unfold universalTrajectory
  rw [map_trajectory]
  have hk : (MvPolynomial.eval a).comp ((MvPolynomial.C :
      GeometricX →+* GeoRow taylorLength).comp (algebraMap Geom GeometricX)) =
      algebraMap Geom GeometricX := RingHom.ext fun z => by simp
  rw [hk]
  simp only [Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval_X]
  unfold trajectory extendedAtJet coefficientPolynomial
  rw [MvPolynomial.eval_map]
theorem solves_on_closure (f : Row 3) (P : Ideal (GeoRow 3))
    (h : ∀ y ∈ regularLocus f P, extendedAtJet f (taylorAt f (pointEval y)) = 0)
    (a : Coefficients) (ha : a ∈ MvPolynomial.zeroLocus GeometricX (curveIdeal f P)) :
    extendedAtJet f (coefficientPolynomial a) = 0 := by
  rw [← eval_universalTrajectory]
  ext m
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  apply ha
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  change MvPolynomial.eval (reconstructAt f y) ((universalTrajectory f).coeff m) = 0
  rw [← Polynomial.coeff_map, eval_universalTrajectory, coefficientPolynomial_reconstructAt,
    h y hy, Polynomial.coeff_zero]
end
end K1_13_5_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2
noncomputable section
open K1_13_5_4_2_4
def c1 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    Module.Finite (CoefficientField A) (GenericQuotient A)
def c2 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    ∀ (i : Fin 4) (p : Row A),
      genericEquation A i * p ∈ prefixIdeal A i.val → p ∈ prefixIdeal A i.val
def c3 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    (∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) →
    ∃ q : ℕ, ∀ (i : Fin 4) (d : Degree), (∀ j, q ≤ d j) →
      ∀ p ∈ piece A (shift d i 1), p ∈ prefixIdeal A (i.val + 1) →
        ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val
private def affineMk (A : Fin 4 → Finset Exponent) (k : ℕ) :
    Row A →ₐ[CoefficientField A] Row A ⧸ prefixIdeal A k :=
  Ideal.Quotient.mkₐ (CoefficientField A) (prefixIdeal A k)
private def quotPiece (A : Fin 4 → Finset Exponent) (k : ℕ) (d : Degree) :
    Submodule (CoefficientField A) (Row A ⧸ prefixIdeal A k) :=
  (piece A d).map (affineMk A k).toLinearMap
private instance (A : Fin 4 → Finset Exponent) (k : ℕ) (d : Degree) :
    Module.Finite (CoefficientField A) (quotPiece A k d) := by
  unfold quotPiece
  infer_instance
private def hilbert (A : Fin 4 → Finset Exponent) (k : ℕ) (d : Degree) : ℕ :=
  Module.finrank (CoefficientField A) (quotPiece A k d)
variable {A : Fin 4 → Finset Exponent}
private theorem affineMk_zero (k : ℕ) (p : Row A) :
    affineMk A k p = 0 ↔ p ∈ prefixIdeal A k := Ideal.Quotient.eq_zero_iff_mem
private theorem affineMk_eq (k : ℕ) (p r : Row A) :
    affineMk A k p = affineMk A k r ↔ p - r ∈ prefixIdeal A k := by
  rw [← affineMk_zero, map_sub, sub_eq_zero]
private theorem prefix_mono {k l : ℕ} (h : k ≤ l) : prefixIdeal A k ≤ prefixIdeal A l :=
  Ideal.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)
private theorem equation_mem_next (i : Fin 4) : genericEquation A i ∈ prefixIdeal A (i.val + 1) :=
  Ideal.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
private theorem hilbert_zero (A : Fin 4 → Finset Exponent) (d : Degree) :
    hilbert A 0 d = exponentCount A d := by
  have hbot : prefixIdeal A 0 = ⊥ := by simp [prefixIdeal]
  let f := ((affineMk A 0).toLinearMap.comp (piece A d).subtype)
  have hrange : LinearMap.range f = quotPiece A 0 d := by
    simp [f, quotPiece, LinearMap.range_comp]
  have hinj : Function.Injective f := by
    intro p r hpr
    apply Subtype.ext
    change affineMk A 0 (p : Row A) = affineMk A 0 (r : Row A) at hpr
    have hm := (affineMk_eq 0 (p : Row A) (r : Row A)).mp hpr
    rw [hbot, Ideal.mem_bot] at hm
    exact sub_eq_zero.mp hm
  unfold hilbert
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, finrank_piece]
private theorem prefix_four (A : Fin 4 → Finset Exponent) :
    prefixIdeal A 4 = Ideal.span (Set.range (genericEquation A)) := by
  have h : {i : Fin 4 | (i : ℕ) < 4} = Set.univ := Set.eq_univ_of_forall fun i => i.isLt
  rw [prefixIdeal, h, Set.image_univ]
private theorem hilbert_stable (hz : ∀ i, 0 ∈ A i)
    (hv : ∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i)
    (hf : Module.Finite (CoefficientField A) (GenericQuotient A)) :
    ∃ q : ℕ, ∀ d : Degree, (∀ j, q ≤ d j) →
      hilbert A 4 d = Module.finrank (CoefficientField A) (GenericQuotient A) := by
  let hfin : Module.Finite (CoefficientField A) (Row A ⧸ prefixIdeal A 4) := by
    rw [prefix_four]; exact hf
  let N : ℕ →o Submodule (CoefficientField A) (Row A ⧸ prefixIdeal A 4) :=
    ⟨fun n => quotPiece A 4 (fun _ => n),
      fun _ _ h => Submodule.map_mono (piece_mono hz fun _ => h)⟩
  have hsup : (⨆ n, N n) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective (CoefficientField A) (prefixIdeal A 4) x
    obtain ⟨n, hn⟩ := piece_exhaustive hz hv p
    exact le_iSup N n (Submodule.mem_map_of_mem hn)
  obtain ⟨q, hq⟩ := hfin.fg_top.stabilizes_of_iSup_eq N hsup
  refine ⟨q, fun d hd => ?_⟩
  have hqd : quotPiece A 4 d = ⊤ := top_unique (by
    rw [hq]
    exact Submodule.map_mono (piece_mono hz hd))
  unfold hilbert
  rw [hqd, finrank_top, prefix_four]
private theorem rank_step (i : Fin 4) (d : Degree)
    (hinj : ∀ p : Row A, genericEquation A i * p ∈ prefixIdeal A i.val → p ∈ prefixIdeal A i.val)
    (hlift : ∀ p ∈ piece A (shift d i 1), p ∈ prefixIdeal A (i.val + 1) →
      ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val) :
    hilbert A (i.val + 1) (shift d i 1) + hilbert A i.val d = hilbert A i.val (shift d i 1) := by
  let f := Ideal.Quotient.factorₐ (CoefficientField A)
    (prefix_mono (A := A) (Nat.le_succ i.val))
  have hf (p : Row A) : f (affineMk A i.val p) = affineMk A (i.val + 1) p := rfl
  let cut : quotPiece A i.val (shift d i 1) →ₗ[CoefficientField A]
      quotPiece A (i.val + 1) (shift d i 1) :=
    f.toLinearMap.restrict (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨p, hp, (hf p).symm⟩)
  let mul : quotPiece A i.val d →ₗ[CoefficientField A] quotPiece A i.val (shift d i 1) :=
    (LinearMap.mulLeft (CoefficientField A) (affineMk A i.val (genericEquation A i))).restrict (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, equation_mul_mem_piece i hp, map_mul (affineMk A i.val) _ _⟩)
  have hsurj : Function.Surjective cut := by
    intro y
    obtain ⟨p, hp, he⟩ := y.property
    exact ⟨⟨affineMk A i.val p, ⟨p, hp, rfl⟩⟩, Subtype.ext ((hf p).trans he)⟩
  have hmul : Function.Injective mul := by
    apply (LinearMap.ker_eq_bot (f := mul)).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨p, _, hp⟩ := x.property
    change affineMk A i.val p = (x : Row A ⧸ prefixIdeal A i.val) at hp
    have hz : affineMk A i.val (genericEquation A i * p) = 0 := by
      rw [map_mul]
      have h := congrArg Subtype.val hx
      change affineMk A i.val (genericEquation A i) * (x : Row A ⧸ prefixIdeal A i.val) = 0 at h
      rwa [hp]
    have hpI := hinj p ((affineMk_zero _ _).mp hz)
    exact Subtype.ext (hp.symm.trans ((affineMk_zero _ _).mpr hpI))
  have hk : LinearMap.range mul = LinearMap.ker cut := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change f (affineMk A i.val (genericEquation A i) * (x : Row A ⧸ prefixIdeal A i.val)) = 0
      rw [map_mul, hf, (affineMk_zero _ _).mpr (equation_mem_next i), zero_mul]
    · intro hy
      obtain ⟨p, hp, he⟩ := y.property
      change affineMk A i.val p = (y : Row A ⧸ prefixIdeal A i.val) at he
      have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hy)
      change f (y : Row A ⧸ prefixIdeal A i.val) = 0 at hz
      rw [← he, hf] at hz
      obtain ⟨r, hr, hrel⟩ := hlift p hp ((affineMk_zero _ _).mp hz)
      refine ⟨⟨affineMk A i.val r, ⟨r, hr, rfl⟩⟩, Subtype.ext ?_⟩
      change affineMk A i.val (genericEquation A i) * affineMk A i.val r = (y : Row A ⧸ prefixIdeal A i.val)
      rw [← he, ← map_mul]
      exact ((affineMk_eq _ _ _).mpr hrel).symm
  have hdim := LinearMap.finrank_range_add_finrank_ker cut
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hk,
    LinearMap.finrank_range_of_inj hmul] at hdim
  exact hdim
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_5_4_2_4.c2 := by
  intro A hz hv
  have hfinite := h1 A hz
  obtain ⟨q1, hq1⟩ := h3 A hz hv
  obtain ⟨q2, hq2⟩ := hilbert_stable hz hv hfinite
  refine ⟨hfinite, max q1 q2, fun n => ?_⟩
  let H (k : ℕ) (d : Degree) : ℝ := hilbert A k d
  have hstep (i : Fin 4) (d : Degree) (hd : ∀ j, max q1 q2 ≤ d j) :
      H i.val (shift d i 1) - H i.val d = H (i.val + 1) (shift d i 1) := by
    have hnat := rank_step i d (h2 A hz i) (hq1 i d fun j => (le_max_left _ _).trans (hd j))
    dsimp only [H]
    rw [sub_eq_iff_eq_add]
    exact_mod_cast hnat.symm
  have htop (d : Degree) (hd : ∀ j, max q1 q2 ≤ d j) :
      H 4 d = (Module.finrank (CoefficientField A) (GenericQuotient A) : ℝ) := by
    dsimp only [H]
    rw [hq2 d fun j => (le_max_right _ _).trans (hd j)]
  simpa only [H, hilbert_zero] using (fourfold_telescoping H _ _ hstep htop n).symm
end
end K1_13_5_4_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4
abbrev OpenRing {R : Type*} [CommRing R] (I : Ideal R) (s : R) :=
  Localization.Away (Ideal.Quotient.mk I s)
def onOpen {R : Type*} [CommRing R] (I : Ideal R) (s : R) : R →+* OpenRing I s :=
  (algebraMap (R ⧸ I) (OpenRing I s)).comp (Ideal.Quotient.mk I)
abbrev sep (f : Row 3) : GeoRow 3 := genericRow (separant f)
abbrev liftedSep (f : Row 3) : GeoRow 4 := liftRow (sep f)
def threeCut (f : Row 3) (T : LiftedChart f) : Ideal (GeoRow 4) :=
  graphIdeal f ⊔ Ideal.span {T.cut}
abbrev OldOpen (f : Row 3) := OpenRing (oldCutIdeal f) (sep f)
abbrev GraphOpen (f : Row 3) (T : LiftedChart f) := OpenRing (threeCut f T) (liftedSep f)
abbrev oldMap (f : Row 3) := onOpen (oldCutIdeal f) (sep f)
abbrev graphMap (f : Row 3) (T : LiftedChart f) := onOpen (threeCut f T) (liftedSep f)
end
end K1_13_5_4_2_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
namespace K1_13_5_4_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
@[simp] private theorem coeff_coeffDerivative (P : Row 3) (m : Fin 3 →₀ ℕ) :
    (coeffDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coeffDerivative_C (p : (Polynomial Geom)) :
    coeffDerivative (MvPolynomial.C p : Row 3) = MvPolynomial.C (derivative p) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
private theorem coeffDerivative_add (P Q : Row 3) :
    coeffDerivative (P + Q) = coeffDerivative P + coeffDerivative Q := by
  ext m
  simp
private theorem coeffDerivative_mul_X (P : Row 3) (j : Fin 3) :
    coeffDerivative (P * MvPolynomial.X j) = coeffDerivative P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coeffDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp
private theorem eval_chain (P : Row 3) (a : Fin 3 → (Polynomial Geom)) :
    derivative (MvPolynomial.eval a P) = MvPolynomial.eval a (coeffDerivative P) +
      ∑ i, derivative (a i) * MvPolynomial.eval a (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [coeffDerivative_C]
  | add P Q hP hQ =>
    simp only [map_add, coeffDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    rw [map_mul, MvPolynomial.eval_X, derivative_mul, ih, coeffDerivative_mul_X,
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
private theorem derivative_hasse_one (S : (Polynomial Geom)) :
    derivative (hasseDeriv 1 S) = 2 * hasseDeriv 2 S := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := Geom) 1 1) S
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul] using h
private theorem eval_lowerTangent (P : Row 3) (S : (Polynomial Geom)) :
    derivative (atJet P S) = atJet (lowerTangent P) S +
      derivative (jet S (2 : Fin 3)) * atJet (separant P) S := by
  unfold atJet lowerTangent separant
  rw [eval_chain, Fin.sum_univ_three]
  simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
  have h0 : derivative (jet S (0 : Fin 3)) = jet S (1 : Fin 3) := by
    simp [jet]
  have h1 : derivative (jet S (1 : Fin 3)) = 2 * jet S (2 : Fin 3) :=
    derivative_hasse_one S
  rw [h0, h1]
  ring
private theorem eval_tangentNumerator (f P : Row 3) (S : (Polynomial Geom)) (hf : atJet f S = 0) :
    atJet (tangentNumerator f P) S = atJet (separant f) S * derivative (atJet P S) := by
  have hz : atJet (lowerTangent f) S +
      derivative (jet S (2 : Fin 3)) * atJet (separant f) S = 0 := by
    rw [← eval_lowerTangent, hf, map_zero]
  unfold tangentNumerator
  rw [eval_lowerTangent]
  change (MvPolynomial.eval (jet S)) (_ - _) = _
  rw [map_sub, map_mul, map_mul]
  change atJet (separant f) S * atJet (lowerTangent P) S -
      atJet (lowerTangent f) S * atJet (separant P) S = _
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
theorem eval_compatibility (f : Row 3) (S : (Polynomial Geom)) (hf : atJet f S = 0) (k : ℕ) :
    atJet (compatibilityNumerator f k) S =
      atJet (separant f) S ^ (2 * k + 1) *
        ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)) := by
  induction k with
  | zero =>
    have hz : atJet (lowerTangent f) S +
        derivative (jet S (2 : Fin 3)) * atJet (separant f) S = 0 := by
      rw [← eval_lowerTangent, hf, map_zero]
    change MvPolynomial.eval (jet S) (-lowerTangent f) =
      atJet (separant f) S ^ (2 * 0 + 1) *
        ((derivative (R := Geom))^[0 + 1]) (jet S (2 : Fin 3))
    rw [map_neg]
    simp only [Nat.mul_zero, Nat.zero_add, pow_one, Function.iterate_one]
    change -atJet (lowerTangent f) S = _
    linear_combination -hz
  | succ k ih =>
    let e := MvPolynomial.eval (jet S : Fin 3 → (Polynomial Geom))
    change e (_ - _) = _
    rw [map_sub, map_mul, map_mul, map_mul, map_natCast]
    change atJet (separant f) S * atJet (tangentNumerator f (compatibilityNumerator f k)) S -
      (↑(2 * k + 1) : (Polynomial Geom)) * atJet (compatibilityNumerator f k) S *
        atJet (tangentNumerator f (separant f)) S = _
    rw [eval_tangentNumerator _ _ _ hf, eval_tangentNumerator _ _ _ hf, ih]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
      Function.iterate_succ_apply' (derivative (R := Geom)) (k + 1) (jet S (2 : Fin 3))]
    calc
      _ = atJet (separant f) S * (atJet (separant f) S *
          derivative (atJet (separant f) S ^ (2 * k + 1) *
            ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)))) -
          (↑(2 * k + 1) : (Polynomial Geom)) * (atJet (separant f) S * derivative (atJet (separant f) S)) *
            (atJet (separant f) S ^ (2 * k + 1) *
              ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3))) := by ring
      _ = _ := cleared_product_rule (2 * k + 1) (atJet (separant f) S)
        (((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)))
private theorem twice_iterate_derivative_top (k : ℕ) (S : (Polynomial Geom)) :
    2 * ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)) =
      ((derivative (R := Geom))^[k + 3]) S := by
  have hsecond : ((derivative (R := Geom))^[2]) S = 2 * jet S (2 : Fin 3) := by
    rw [Function.iterate_succ_apply' (derivative (R := Geom)) 1 S, Function.iterate_one]
    change derivative (derivative S) = 2 * hasseDeriv 2 S
    simpa only [hasseDeriv_one'] using derivative_hasse_one S
  rw [show k + 3 = (k + 1) + 2 by omega,
    Function.iterate_add_apply (derivative (R := Geom)) (k + 1) 2 S, hsecond]
  simpa only [Nat.cast_ofNat] using
    (Polynomial.iterate_derivative_natCast_mul (n := 2) (k := k + 1)
      (f := jet S (2 : Fin 3))).symm
private theorem factorial_ne_zero (j : ℕ) (hj : j < K1.p) :
    (j.factorial : GeometricX) ≠ 0 := by
  let g : K1.K →+* GeometricX := genericCoeff.comp (Polynomial.C.comp embed)
  intro hz
  have hK : (j.factorial : K1.K) = 0 :=
    g.injective (by simpa only [map_natCast, map_zero] using hz)
  have hp := CharP.char_is_prime_of_two_le K1.K K1.p (by decide)
  exact (not_le_of_gt hj) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K1.K K1.p _).mp hK))
private theorem centredJet_mark (f : Row 3) (S : (Polynomial Geom)) (hr : RegularAt 2 f S)
    (j : ℕ) (hj : j < taylorLength) :
    centredJet f (pointEval (jetPoint S)) j = genericCoeff (hasseDeriv j S) := by
  rcases j with _ | _ | _ | k
  · simp [centredJet, pointEval, jetPoint, jet]
  · simp [centredJet, pointEval, jetPoint, jet]
  · simp [centredJet, pointEval, jetPoint, jet]
  have he (b : Row 3) : pointEval (jetPoint S) b = genericCoeff (atJet b S) :=
    eval_genericRow_at_point b S
  have hsep : genericCoeff (atJet (separant f) S) ≠ 0 :=
    fun h => hr.2 (genericCoeff_injective (h.trans genericCoeff.map_zero.symm))
  have hchar : taylorLength < K1.p := by
    change 133672 < 2130706433
    omega
  have hfact : ((k + 3).factorial : GeometricX) ≠ 0 :=
    factorial_ne_zero _ (hj.trans hchar)
  change centredJet f (pointEval (jetPoint S)) (k + 3) = genericCoeff (hasseDeriv (k + 3) S)
  rw [centredJet, he, he, eval_compatibility _ _ hr.1, map_mul, map_pow]
  apply (div_eq_iff (mul_ne_zero hfact (pow_ne_zero _ hsep))).mpr
  rw [show 2 * (genericCoeff (atJet (separant f) S) ^ (2 * k + 1) *
      genericCoeff (((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)))) =
      genericCoeff (atJet (separant f) S) ^ (2 * k + 1) *
      genericCoeff (2 * ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3))) by
    rw [map_mul, map_ofNat]
    ring]
  have hscale : ((derivative (R := Geom))^[k + 3]) S =
      ((k + 3).factorial : (Polynomial Geom)) * hasseDeriv (k + 3) S := by
    rw [← Polynomial.factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul]
  rw [twice_iterate_derivative_top, hscale, map_mul, map_natCast]
  ring
theorem reconstructAt_mark (f : Row 3) (S : (Polynomial Geom)) (hS : S.natDegree ≤ 133671)
    (hr : RegularAt 2 f S) :
    reconstructAt f (jetPoint S) = coefficientPoint S := by
  let U := S.map (algebraMap Geom GeometricX)
  let x := genericCoeff Polynomial.X
  have hx : centre (pointEval (jetPoint S)) = x := by
    simp [centre, pointEval, x]
  have hdegree : (Polynomial.taylor x U).natDegree < taylorLength := by
    rw [Polynomial.natDegree_taylor, show U.natDegree = S.natDegree from
      Polynomial.natDegree_map_eq_of_injective (algebraMap Geom GeometricX).injective S]
    exact Nat.lt_succ_of_le hS
  have htaylor : (∑ j : Fin taylorLength,
      Polynomial.monomial j.val (centredJet f (pointEval (jetPoint S)) j.val)) =
      Polynomial.taylor x U := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      Polynomial.monomial j (centredJet f (pointEval (jetPoint S)) j))]
    conv_rhs => rw [Polynomial.as_sum_range' _ taylorLength hdegree]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [centredJet_mark f S hr j (Finset.mem_range.mp hj), Polynomial.taylor_coeff]
    congr 1
    dsimp [U, x]
    rw [Polynomial.hasseDeriv_map]
    exact (RingHom.congr_fun eval_abscissa (hasseDeriv j S)).symm
  have hU : taylorAt f (pointEval (jetPoint S)) = U := by
    rw [taylorAt, hx, htaylor, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
  funext j
  change (taylorAt f (pointEval (jetPoint S))).coeff j.val =
    algebraMap Geom GeometricX (S.coeff j.val)
  rw [hU, Polynomial.coeff_map]
end
end K1_13_5_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
theorem onOpen_kills {R : Type*} [CommRing R] {I : Ideal R} {s a : R} (ha : a ∈ I) :
    onOpen I s a = 0 := by
  rw [onOpen, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
theorem onOpen_isUnit {R : Type*} [CommRing R] (I : Ideal R) (s : R) :
    IsUnit (onOpen I s s) :=
  IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I s)
theorem onOpen_hom_ext {R A : Type*} [CommRing R] [CommRing A] {I : Ideal R} {s : R}
    {g h : OpenRing I s →+* A} (he : g.comp (onOpen I s) = h.comp (onOpen I s)) : g = h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk I s))
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact DFunLike.congr_fun he b
def openLift {R A : Type*} [CommRing R] [CommRing A] (I : Ideal R) (s : R)
    (b : R →+* A) (hI : I ≤ RingHom.ker b) (hs : IsUnit (b s)) : OpenRing I s →+* A :=
  let g := Ideal.Quotient.lift I b fun _ hx => RingHom.mem_ker.mp (hI hx)
  IsLocalization.Away.lift (g := g) (Ideal.Quotient.mk I s) hs
@[simp] theorem openLift_onOpen {R A : Type*} [CommRing R] [CommRing A] (I : Ideal R) (s : R)
    (b : R →+* A) (hI : I ≤ RingHom.ker b) (hs : IsUnit (b s)) (a : R) :
    openLift I s b hI hs (onOpen I s a) = b a :=
  IsLocalization.Away.lift_eq (g := Ideal.Quotient.lift I b
    fun _ hx => RingHom.mem_ker.mp (hI hx)) (Ideal.Quotient.mk I s) hs (Ideal.Quotient.mk I a)
private theorem three_ne_zero : (3 : GeometricX) ≠ 0 := by
  let : CharP Geom K1.p := charP_of_injective_ringHom K1_13.embed.injective K1.p
  let : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  let : CharP GeometricX K1.p :=
    charP_of_injective_ringHom genericCoeff_injective K1.p
  exact fun h => (by decide : ¬ K1.p ∣ 3)
    ((CharP.cast_eq_zero_iff GeometricX K1.p 3).mp h)
theorem three_isUnit {A : Type*} [CommRing A] (c : GeometricX →+* A) :
    IsUnit (3 : A) := by
  simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr three_ne_zero).map c
theorem graph_coord_unique {A : Type*} [CommRing A] (f : Row 3)
    (w : GeoRow 4 →+* A) (hu : IsUnit (w (liftedSep f))) (hG : w (graph f) = 0)
    {z : A} (hz : w (liftRow (genericRow (lowerTangent f))) + 3 * z * w (liftedSep f) = 0) :
    w (MvPolynomial.X 3) = z := by
  have hh := hG
  rw [graph, map_add, map_mul, map_mul, map_ofNat] at hh
  have he := add_left_cancel (hh.trans hz.symm)
  have hc (x : A) : 3 * x * w (liftedSep f) = (3 * w (liftedSep f)) * x := by ring
  rw [hc, hc] at he
  exact ((three_isUnit (w.comp C)).mul hu).mul_left_cancel he
theorem represents_vanish {A : Type*} [CommRing A] {f old : Row 3} {F : GeoRow 4}
    (hF : RepresentsOnGraph f old F) (w : GeoRow 4 →+* A)
    (hG : graphIdeal f ≤ RingHom.ker w) (hs : IsUnit (w (liftedSep f))) :
    w F = 0 ↔ w (liftRow (genericRow old)) = 0 := by
  obtain ⟨a, b, c, hc, hm⟩ := hF
  have he := RingHom.mem_ker.mp (hG hm)
  simp only [map_mul, map_sub, map_pow] at he
  have hz : w (liftedSep f) ^ b * w F = w (C c) * w (liftRow (genericRow old)) := by
    apply sub_eq_zero.mp
    apply (hs.pow a).mul_left_cancel
    simpa only [mul_zero] using he
  constructor
  · intro h
    have hu : IsUnit (w (C c)) := (isUnit_iff_ne_zero.mpr hc).map (w.comp C)
    apply hu.mul_left_cancel
    rw [mul_zero, ← hz, h, mul_zero]
  · intro h
    apply (hs.pow b).mul_left_cancel
    rw [mul_zero, hz, h, mul_zero]
private def newJet (f : Row 3) : OldOpen f :=
  -oldMap f (genericRow (lowerTangent f)) *
    ↑(((three_isUnit ((oldMap f).comp C)).mul (onOpen_isUnit (oldCutIdeal f) (sep f))).unit⁻¹)
private theorem newJet_eq (f : Row 3) :
    oldMap f (genericRow (lowerTangent f)) + 3 * newJet f * oldMap f (sep f) = 0 := by
  let a := oldMap f (genericRow (lowerTangent f))
  let s := oldMap f (sep f)
  let u := ((three_isUnit ((oldMap f).comp C)).mul (onOpen_isUnit (oldCutIdeal f) (sep f))).unit
  have hu : (u : OldOpen f) = 3 * s := IsUnit.unit_spec _
  change a + 3 * (-a * (↑u⁻¹ : OldOpen f)) * s = 0
  calc
    _ = a + -a * ((↑u⁻¹ : OldOpen f) * (u : OldOpen f)) := by rw [hu]; ring
    _ = 0 := by simp
private def substitute (f : Row 3) : GeoRow 4 →+* OldOpen f :=
  eval₂Hom ((oldMap f).comp C) (Fin.snoc (fun i => oldMap f (MvPolynomial.X i)) (newJet f))
@[simp] private theorem substitute_lift (f : Row 3) (p : GeoRow 3) :
    substitute f (liftRow p) = oldMap f p := by
  rw [substitute, liftRow, eval₂Hom_rename, Fin.snoc_comp_castSucc]
  have h : eval₂Hom ((oldMap f).comp C) (fun i : Fin 3 => oldMap f (MvPolynomial.X i)) = oldMap f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  rw [h]
private theorem substitute_last (f : Row 3) :
    substitute f (MvPolynomial.X (Fin.last 3)) = newJet f := by
  rw [substitute, eval₂Hom_X']
  exact Fin.snoc_last _ _
private theorem substitute_graph (f : Row 3) : substitute f (graph f) = 0 := by
  rw [graph, map_add, map_mul, map_mul, map_ofNat, substitute_lift, substitute_lift,
    show (3 : Fin 4) = Fin.last 3 from rfl, substitute_last]
  exact newJet_eq f
private theorem substitute_kills (f : Row 3) (T : LiftedChart f) :
    threeCut f T ≤ RingHom.ker (substitute f) := by
  have hG : graphIdeal f ≤ RingHom.ker (substitute f) := by
    rw [graphIdeal, Ideal.span_insert, sup_le_iff, Ideal.span_singleton_le_iff_mem,
      Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, RingHom.mem_ker]
    refine ⟨?_, substitute_graph f⟩
    rw [substitute_lift]
    exact onOpen_kills (Ideal.subset_span (by simp))
  have hs : IsUnit (substitute f (liftedSep f)) := by
    rw [substitute_lift]
    exact onOpen_isUnit _ _
  refine sup_le hG ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr ?_))
  apply (represents_vanish T.cut_represents _ hG hs).mpr
  rw [substitute_lift]
  exact onOpen_kills (Ideal.subset_span (by simp))
private def graphToOld (f : Row 3) (T : LiftedChart f) : GraphOpen f T →+* OldOpen f :=
  openLift _ _ (substitute f) (substitute_kills f T)
    (by rw [substitute_lift]; exact onOpen_isUnit _ _)
private theorem graphToOld_on (f : Row 3) (T : LiftedChart f) (b : GeoRow 4) :
    graphToOld f T (graphMap f T b) = substitute f b := by
  rw [graphToOld, openLift_onOpen]
private theorem oldToGraph_kills (f : Row 3) (T : LiftedChart f) :
    oldCutIdeal f ≤ RingHom.ker ((graphMap f T).comp (rename Fin.castSucc).toRingHom) := by
  let b := (graphMap f T).comp (rename Fin.castSucc).toRingHom
  have hG : graphIdeal f ≤ RingHom.ker (graphMap f T) := fun u hu =>
    RingHom.mem_ker.mpr (onOpen_kills (show u ∈ threeCut f T from Ideal.mem_sup_left hu))
  change oldCutIdeal f ≤ RingHom.ker b
  rw [oldCutIdeal, Ideal.span_insert, sup_le_iff]
  rw [Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_le_iff_mem]
  refine ⟨hG (show liftRow (genericRow f) ∈ graphIdeal f from
    Ideal.subset_span (by simp)), RingHom.mem_ker.mpr ?_⟩
  exact (represents_vanish T.cut_represents _ hG (onOpen_isUnit _ _)).mp
    (onOpen_kills (show T.cut ∈ threeCut f T from
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
private def oldToGraph (f : Row 3) (T : LiftedChart f) : OldOpen f →+* GraphOpen f T :=
  openLift _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f))
@[simp] private theorem oldToGraph_on (f : Row 3) (T : LiftedChart f) (a : GeoRow 3) :
    oldToGraph f T (oldMap f a) = graphMap f T (liftRow a) :=
  openLift_onOpen _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f)) a
def graphEquiv (f : Row 3) (T : LiftedChart f) : OldOpen f ≃+* GraphOpen f T := by
  refine RingEquiv.ofRingHom (oldToGraph f T) (graphToOld f T) ?_ ?_
  · apply onOpen_hom_ext
    have hcomp : (graphToOld f T).comp (graphMap f T) = substitute f :=
      RingHom.ext (graphToOld_on f T)
    rw [RingHom.comp_assoc, RingHom.id_comp, hcomp]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [substitute, liftRow]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hG : graphMap f T (graph f) = 0 :=
          onOpen_kills (Ideal.mem_sup_left (Ideal.subset_span (by simp)))
        have he := DFunLike.congr_arg (oldToGraph f T) (newJet_eq f)
        rw [map_add, map_mul, map_mul, map_ofNat, map_zero, oldToGraph_on, oldToGraph_on] at he
        have h := graph_coord_unique f (graphMap f T) (onOpen_isUnit _ _) hG he
        rw [RingHom.comp_apply, substitute_last]
        exact h.symm
      · simp [substitute, liftRow]
  · apply onOpen_hom_ext
    apply RingHom.ext
    intro a
    simp [graphToOld_on]
@[simp] theorem graphEquiv_on (f : Row 3) (T : LiftedChart f) (a : GeoRow 3) :
    graphEquiv f T (oldMap f a) = graphMap f T (liftRow a) :=
  oldToGraph_on f T a
end
end K1_13_5_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3
noncomputable section
open K1_13_5_4_2_4 K1_13_5_4_2_4_2 MvPolynomial
abbrev Slot (A : Fin 4 → Finset Exponent) := (i : Fin 4) × ↥(A i)
abbrev SlotRing (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (Slot A) (CoefficientField A)
def slotWeight (A : Fin 4 → Finset Exponent) (v : Slot A) : Degree :=
  Pi.single v.1 1
abbrev slotPiece (A : Fin 4 → Finset Exponent) (d : Degree) :=
  weightedHomogeneousSubmodule (CoefficientField A) (slotWeight A) d
def dehom (A : Fin 4 → Finset Exponent) : SlotRing A →ₐ[CoefficientField A] Row A :=
  aeval fun v => monomial v.2.val 1
def relationGenerators (A : Fin 4 → Finset Exponent) (k : ℕ) : Set (SlotRing A) :=
  {f | (∃ d, f ∈ slotPiece A d) ∧ dehom A f ∈ prefixIdeal A k}
def relationIdeal (A : Fin 4 → Finset Exponent) (k : ℕ) : Ideal (SlotRing A) :=
  Ideal.span (relationGenerators A k)
def homogeneousEquation (A : Fin 4 → Finset Exponent) (i : Fin 4) : SlotRing A :=
  ∑ a : ↥(A i), C (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩)) *
    MvPolynomial.X ⟨i, a⟩
def cutIdeal (A : Fin 4 → Finset Exponent) (k : ℕ) : Ideal (SlotRing A) :=
  relationIdeal A 0 ⊔ Ideal.span (homogeneousEquation A '' {i : Fin 4 | (i : ℕ) < k})
def chartProduct (A : Fin 4 → Finset Exponent) (b : (i : Fin 4) → ↥(A i)) :
    SlotRing A :=
  ∏ i : Fin 4, MvPolynomial.X (⟨i, b i⟩ : Slot A)
def constantChart (A : Fin 4 → Finset Exponent) (hz : ∀ i, 0 ∈ A i) : SlotRing A :=
  chartProduct A fun i => ⟨0, hz i⟩
open scoped Pointwise
private def affineWeight (A : Fin 4 → Finset Exponent) (v : Slot A) : Exponent :=
  v.2.val
private def exponentImage (A : Fin 4 → Finset Exponent) (d : Degree) : Set Exponent :=
  {a | ∃ e : Slot A →₀ ℕ,
    Finsupp.weight (slotWeight A) e = d ∧ Finsupp.weight (affineWeight A) e = a}
private theorem exponentSet_add (A : Fin 4 → Finset Exponent) (d e : Degree) :
    exponentSet A (d + e) = exponentSet A d + exponentSet A e := by
  simp only [exponentSet, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]
private theorem exponentSet_single (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    exponentSet A (Pi.single i 1) = A i := by
  classical
  unfold exponentSet
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_nsmul]
  · simp
private theorem sumset_eq_exponentImage (A : Fin 4 → Finset Exponent) (d : Degree) :
    exponentSet A d = exponentImage A d := by
  classical
  have hadd (d e : Degree) :
      exponentImage A d + exponentImage A e ⊆ exponentImage A (d + e) := by
    intro m hm
    obtain ⟨a, ⟨u, hu, rfl⟩, b, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_add.mp hm
    exact ⟨u + v, by rw [map_add, hu, hv], map_add _ _ _⟩
  have hzero : (0 : Exponent) ∈ exponentImage A 0 :=
    ⟨0, map_zero _, map_zero _⟩
  have hsingle (i : Fin 4) : (↑(A i) : Set Exponent) ⊆ exponentImage A (Pi.single i 1) := by
    intro a ha
    let v : Slot A := ⟨i, ⟨a, ha⟩⟩
    exact ⟨Finsupp.single v 1, by rw [Finsupp.weight_single, one_smul]; rfl,
      by rw [Finsupp.weight_single, one_smul]; rfl⟩
  have hscale (i : Fin 4) (n : ℕ) :
      n • (↑(A i) : Set Exponent) ⊆ exponentImage A (n • Pi.single i 1) := by
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      exact (Set.add_subset_add ih (hsingle i)).trans (hadd _ _)
  have hsum (s : Finset (Fin 4)) :
      (∑ i ∈ s, d i • (↑(A i) : Set Exponent)) ⊆
        exponentImage A (∑ i ∈ s, d i • Pi.single i 1) := by
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (Set.add_subset_add (hscale i _) ih).trans (hadd _ _)
  apply Set.Subset.antisymm
  · have hdeg : (∑ i : Fin 4, d i • Pi.single i (1 : ℕ)) = d := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    simpa only [exponentSet, hdeg] using hsum Finset.univ
  · clear hsum
    rintro _ ⟨e, rfl, rfl⟩
    induction e using Finsupp.induction_linear with
    | zero => simp [exponentSet]
    | add e f he hf =>
      rw [map_add, map_add, exponentSet_add]
      exact Set.mem_add.mpr ⟨_, he, _, hf, rfl⟩
    | single v n =>
      rw [Finsupp.weight_single, Finsupp.weight_single]
      have hv : affineWeight A v ∈ exponentSet A (slotWeight A v) := by
        rw [slotWeight, exponentSet_single]
        exact v.2.property
      induction n with
      | zero => simp [exponentSet]
      | succ n ih =>
        rw [succ_nsmul, succ_nsmul, exponentSet_add]
        exact Set.mem_add.mpr ⟨_, ih, _, hv, rfl⟩
private theorem dehom_monomial_one (A : Fin 4 → Finset Exponent) (e : Slot A →₀ ℕ) :
    dehom A (monomial e 1) = monomial (Finsupp.weight (affineWeight A) e) 1 := by
  induction e using Finsupp.induction_linear with
  | zero => simp [monomial_zero']
  | add e f he hf =>
    rw [← one_mul (1 : CoefficientField A), ← monomial_mul_monomial, map_mul, he, hf,
      monomial_mul_monomial, one_mul, map_add]
  | single v n =>
    rw [← X_pow_eq_monomial, map_pow, dehom, aeval_X]
    change (monomial (affineWeight A v) (1 : CoefficientField A)) ^ n = _
    rw [monomial_pow, one_pow, Finsupp.weight_single]
theorem map_slotPiece (A : Fin 4 → Finset Exponent) (d : Degree) :
    (slotPiece A d).map (dehom A).toLinearMap = piece A d := by
  have hS : slotPiece A d = restrictSupport (CoefficientField A)
      {e | Finsupp.weight (slotWeight A) e = d} :=
    weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
  rw [hS, restrictSupport_eq_span, Submodule.map_span, piece]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    rw [AlgHom.toLinearMap_apply, dehom_monomial_one]
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [sumset_eq_exponentImage]
    exact ⟨e, he, rfl⟩
  · rintro ⟨a, rfl⟩
    have ha : a.val ∈ exponentImage A d := by
      rw [← sumset_eq_exponentImage]
      exact a.property
    obtain ⟨e, he, hea⟩ := ha
    exact ⟨_, ⟨e, he, rfl⟩, by rw [AlgHom.toLinearMap_apply, dehom_monomial_one, hea]⟩
variable {A : Fin 4 → Finset Exponent}
theorem homogeneousEquation_mem (i : Fin 4) :
    homogeneousEquation A i ∈ slotPiece A (Pi.single i 1) := by
  classical
  apply Submodule.sum_mem
  intro a _
  have hC := isWeightedHomogeneous_C (slotWeight A)
    (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩))
  have hX := isWeightedHomogeneous_X (CoefficientField A) (slotWeight A) (⟨i, a⟩ : Slot A)
  simpa only [mem_weightedHomogeneousSubmodule, zero_add, slotWeight] using hC.mul hX
theorem dehom_equation (i : Fin 4) :
    dehom A (homogeneousEquation A i) = genericEquation A i := by
  classical
  simp only [homogeneousEquation, genericEquation, map_sum, map_mul, dehom, aeval_C,
    algebraMap_eq, aeval_X, C_mul_monomial, mul_one]
end
end K1_13_5_4_2_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
open RingTheory.Sequence
open scoped Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem quotient_regular_iff {R : Type*} [CommRing R] (a b : R) :
    IsSMulRegular (QuotSMulTop a R) b ↔
      IsLeftRegular (Ideal.Quotient.mk (Ideal.span {a}) b) := by
  let e : QuotSMulTop a R ≃ₗ[R] R ⧸ (Ideal.span {a} : Ideal R) :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
      change ((Ideal.span {a}).map (RingHom.id R) : Ideal R) = Ideal.span {a}
      rw [Ideal.map_id])
  exact e.isSMulRegular_congr b
theorem graph_dimension (f : Row 3) (P : Ideal (GeoRow 3)) [P.IsPrime]
    (hs : genericRow (separant f) ∉ P) :
    (graphCurve f P).IsPrime ∧
      (affineHilbertPolynomial (graphCurve f P)).natDegree =
        (affineHilbertPolynomial P).natDegree := by
  let s := genericRow (separant f)
  let v : GeoRow 3 := -genericRow (lowerTangent f) * C ((3 : GeometricX)⁻¹)
  let L := Localization.Away (Ideal.Quotient.mk P s)
  let J := awayPresentationIdeal P s
  have hsA : Ideal.Quotient.mk P s ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hs
  have hsreg : IsLeftRegular (Ideal.Quotient.mk P s) := fun _ _ h => mul_left_cancel₀ hsA h
  have : IsDomain L := IsLocalization.Away.isDomain L hsA
  have hJ : J.IsPrime := RingHom.ker_isPrime (awayPresentation P s)
  let coords : Fin 4 → MvPolynomial (Option (Fin 3)) GeometricX :=
    Fin.snoc (fun i => MvPolynomial.X (some i)) (rename some v * MvPolynomial.X none)
  let φ : GeoRow 4 →ₐ[GeometricX] MvPolynomial (Option (Fin 3)) GeometricX := aeval coords
  have hpoint (w : Option (Fin 3) → GeometricX) (hw : w ∈ zeroLocus GeometricX J) :
      (fun i => aeval w (coords i)) = graphPoint f (w ∘ some) := by
    have hrel := hw _ (X_none_mul_rename_some_sub_one_mem_awayPresentationIdeal P s)
    rw [map_sub, map_mul, aeval_X, aeval_rename, map_one, sub_eq_zero] at hrel
    have hinv : w none = (aeval (w ∘ some) s)⁻¹ := eq_inv_of_mul_eq_one_left hrel
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [coords, graphPoint, Fin.snoc_last, map_mul, aeval_rename, aeval_X, hinv, v,
        map_neg, aeval_C, Algebra.algebraMap_self_apply, aeval_eq_eval, div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    · simp [coords, graphPoint, Function.comp_def]
  have himage : (fun w : Option (Fin 3) → GeometricX => graphPoint f (w ∘ some)) ''
        zeroLocus GeometricX J = graphLocus f P := by
    change (graphPoint f ∘ (fun w : Option (Fin 3) → GeometricX => w ∘ some)) ''
      zeroLocus GeometricX J = graphPoint f '' regularLocus f P
    rw [Set.image_comp]
    have hopen := image_comp_some_zeroLocus_awayPresentationIdeal (K := GeometricX) P s
    simpa only [regularLocus, aeval_eq_eval] using congrArg (Set.image (graphPoint f)) hopen
  have hcomap : graphCurve f P = J.comap φ := by
    ext p
    change p ∈ vanishingIdeal GeometricX (graphLocus f P) ↔ φ p ∈ J
    have hjp : φ p ∈ J ↔ φ p ∈ vanishingIdeal GeometricX (zeroLocus GeometricX J) := by
      rw [IsPrime.vanishingIdeal_zeroLocus J]
    rw [← himage, hjp]
    simp only [mem_vanishingIdeal_iff, Set.forall_mem_image]
    refine forall₂_congr fun w hw => ?_
    change aeval (graphPoint f (w ∘ some)) p = 0 ↔ aeval w (aeval coords p) = 0
    rw [comp_aeval_apply, hpoint w hw]
  have hrename : φ.comp (rename Fin.castSucc) = rename some := by
    apply algHom_ext
    intro i
    simp [φ, coords]
  have hback : (graphCurve f P).comap (rename Fin.castSucc) = P := by
    rw [hcomap]
    change J.comap (φ.comp (rename Fin.castSucc)) = P
    rw [hrename]
    ext p
    change rename some p ∈ awayPresentationIdeal P s ↔ p ∈ P
    rw [mem_awayPresentationIdeal, awayPresentation_rename_some,
      map_eq_zero_iff _ (IsLocalization.Away.algebraMap_injective_of_isLeftRegular hsreg),
      Ideal.Quotient.eq_zero_iff_mem]
  have hupper : (affineHilbertPolynomial (J.comap φ)).natDegree ≤
      (affineHilbertPolynomial J).natDegree :=
    natDegree_affineHilbertPolynomial_le_of_injective (Ideal.quotientMapₐ J φ le_rfl)
      Ideal.quotientMap_injective
  have hlower : (affineHilbertPolynomial ((graphCurve f P).comap (rename Fin.castSucc))).natDegree ≤
      (affineHilbertPolynomial (graphCurve f P)).natDegree :=
    natDegree_affineHilbertPolynomial_le_of_injective
      (Ideal.quotientMapₐ (graphCurve f P) (rename Fin.castSucc) le_rfl)
      Ideal.quotientMap_injective
  rw [hback] at hlower
  rw [natDegree_affineHilbertPolynomial_awayPresentationIdeal hsreg, ← hcomap] at hupper
  refine ⟨?_, le_antisymm hupper hlower⟩
  rw [hcomap]
  exact hJ.comap φ
end
end K1_13_5_4_2_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5
open K1_13 K1_13_5_4_2
structure FirstBody (P : Set ExponentSpace) : Prop where
  polytope : ∃ v : Set ExponentSpace, v.Finite ∧ P = convexHull ℝ v
  zero_mem : 0 ∈ P
  zero_height : ∀ x ∈ P, x 3 = 0
def Chamber (s : Shape) : Prop := s.j ≤ s.b ∧ 2 * s.t ≤ s.j
end K1_13_5_4_2_5
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3
noncomputable section
open K1_13_5_4_2_4 K1_13_5_4_2_4_2 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent) (hz : ∀ i, 0 ∈ A i),
    (∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) →
    ∀ (i : Fin 4) (f : SlotRing A), f ∈ relationGenerators A (i.val + 1) →
      ∃ n : ℕ, constantChart A hz ^ n * f ∈ cutIdeal A (i.val + 1)
def c2 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent) (hz : ∀ i, 0 ∈ A i) (i : Fin 4)
    (b : (j : Fin 4) → ↥(A j)) (f : SlotRing A) (n : ℕ),
    constantChart A hz ^ n * f ∈ cutIdeal A (i.val + 1) →
      ∃ m : ℕ, chartProduct A b ^ m * f ∈ cutIdeal A (i.val + 1)
private theorem weight_apply (A : Fin 4 → Finset Exponent) (e : Slot A →₀ ℕ) (i : Fin 4) :
    Finsupp.weight (slotWeight A) e i = ∑ a : ↥(A i), e ⟨i, a⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp [slotWeight, Pi.smul_apply]
  · intro j _ hj
    simp [slotWeight, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj)]
  · simp
private theorem monomial_mul_mem (A : Fin 4 → Finset Exponent)
    (J : Ideal (SlotRing A)) (g : SlotRing A) (N : ℕ)
    (hkill : ∀ b : (i : Fin 4) → ↥(A i), chartProduct A b ^ N * g ∈ J)
    (e : Slot A →₀ ℕ) (c : CoefficientField A)
    (he : ∀ i, Fintype.card ↥(A i) * N < Finsupp.weight (slotWeight A) e i) :
    monomial e c * g ∈ J := by
  classical
  have hpick (i : Fin 4) : ∃ a : ↥(A i), N ≤ e ⟨i, a⟩ := by
    by_contra! h
    have hsum : (∑ a : ↥(A i), e ⟨i, a⟩) ≤ Fintype.card ↥(A i) * N := by
      calc
        _ ≤ ∑ _a : ↥(A i), N := Finset.sum_le_sum fun a _ => (h a).le
        _ = _ := by simp
    exact (not_le_of_gt (he i)) ((weight_apply A e i).trans_le hsum)
  choose b hb using hpick
  let v : Slot A →₀ ℕ := ∑ i : Fin 4, Finsupp.single ⟨i, b i⟩ N
  have hv : v ≤ e := by
    rintro ⟨i, a⟩
    rw [show v ⟨i, a⟩ = Finsupp.single (⟨i, b i⟩ : Slot A) N ⟨i, a⟩ by
      simp only [v, Finsupp.finsetSum_apply]
      apply Finset.sum_eq_single i
      · intro j _ hj
        apply Finsupp.single_eq_of_ne
        intro h
        exact hj (congrArg Sigma.fst h).symm
      · simp]
    by_cases ha : b i = a
    · subst a
      simpa using hb i
    · simp [Ne.symm ha]
  have hchart : chartProduct A b ^ N = monomial v (1 : CoefficientField A) := by
    unfold chartProduct
    rw [← Finset.prod_pow]
    simp only [MvPolynomial.X_pow_eq_monomial, v, monomial_sum_one]
  have hfac : monomial e c * g = monomial (e - v) c * (chartProduct A b ^ N * g) := by
    rw [hchart, ← mul_assoc, monomial_mul_monomial, mul_one, add_comm (e - v),
      add_tsub_cancel_of_le hv]
  rw [hfac]
  exact J.mul_mem_left _ (hkill b)
private theorem homogeneous_mul_mem (A : Fin 4 → Finset Exponent)
    (J : Ideal (SlotRing A)) (g : SlotRing A) (N : ℕ)
    (hkill : ∀ b : (i : Fin 4) → ↥(A i), chartProduct A b ^ N * g ∈ J)
    {f : SlotRing A} {d : Degree} (hf : f ∈ slotPiece A d)
    (hd : ∀ i, Fintype.card ↥(A i) * N < d i) :
    f * g ∈ J := by
  classical
  rw [f.as_sum, Finset.sum_mul]
  exact J.sum_mem fun e he => monomial_mul_mem A J g N hkill e _ (by
    have hdeg := hf (mem_support_iff.mp he)
    intro i
    simpa only [hdeg] using hd i)
private theorem component_mul (A : Fin 4 → Finset Exponent) {g : SlotRing A} {e : Degree}
    (hg : g ∈ slotPiece A e) (f : SlotRing A) (d : Degree) :
    weightedHomogeneousComponent (slotWeight A) (d + e) (f * g) =
      weightedHomogeneousComponent (slotWeight A) d f * g := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
    have ha := isWeightedHomogeneous_monomial (slotWeight A) a c rfl
    have hg' : g.IsWeightedHomogeneous (slotWeight A) e := hg
    simp only [weightedHomogeneousComponent_of_mem (ha.mul hg'),
      weightedHomogeneousComponent_of_mem ha, add_right_cancel_iff]
    split <;> simp_all
  | add p r hp hr => simp [add_mul, hp, hr]
private theorem high_degree_mem (A : Fin 4 → Finset Exponent) (k : ℕ) (J : Ideal (SlotRing A))
    (hlocal : ∀ g ∈ relationGenerators A k, ∀ b : (i : Fin 4) → ↥(A i),
      ∃ n : ℕ, chartProduct A b ^ n * g ∈ J) :
    ∃ q : ℕ, ∀ (d : Degree), (∀ i, q ≤ d i) →
      ∀ f ∈ slotPiece A d, f ∈ relationIdeal A k → f ∈ J := by
  classical
  obtain ⟨G, hG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (R := SlotRing A) (relationGenerators A k)).mp (IsNoetherian.noetherian _)
  have hspan' : relationIdeal A k = Ideal.span (↑G : Set (SlotRing A)) := hspan
  choose D hD using fun g : G => (hG g.property).1
  choose n hn using fun g : G => hlocal g (hG g.property)
  let N (g : G) := Finset.univ.sup (n g)
  have hN (g : G) (b : (i : Fin 4) → ↥(A i)) : chartProduct A b ^ N g * (g : SlotRing A) ∈ J := by
    have hle : n g b ≤ N g := Finset.le_sup (f := n g) (Finset.mem_univ b)
    have hpow : chartProduct A b ^ N g * (g : SlotRing A) =
        chartProduct A b ^ (N g - n g b) * (chartProduct A b ^ n g b * (g : SlotRing A)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [hpow]
    exact J.mul_mem_left _ (hn g b)
  let bound (g : G) (i : Fin 4) := D g i + Fintype.card ↥(A i) * N g + 1
  let q := Finset.univ.sup fun g : G => Finset.univ.sup (bound g)
  refine ⟨q, ?_⟩
  intro d hd f hf hrel
  rw [hspan'] at hrel
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.mp hrel
  have hsum := congrArg (weightedHomogeneousComponent (slotWeight A) d) hc
  rw [map_sum, weightedHomogeneousComponent_eq_self (show f.IsWeightedHomogeneous _ d from hf)]
    at hsum
  rw [← hsum]
  refine J.sum_mem fun g _ => ?_
  have hgd (i : Fin 4) : bound g i ≤ d i := by
    exact (Finset.le_sup (f := bound g) (Finset.mem_univ i)).trans
      ((Finset.le_sup (f := fun x : G => Finset.univ.sup (bound x)) (Finset.mem_univ g)).trans (hd i))
  have hdiff : ∀ i, Fintype.card ↥(A i) * N g < (d - D g) i := by
    intro i
    have hh := hgd i
    change D g i + Fintype.card ↥(A i) * N g + 1 ≤ d i at hh
    change _ < d i - D g i
    omega
  have heq : d - D g + D g = d := by
    funext i
    exact Nat.sub_add_cancel (by have hh := hgd i; dsimp [bound] at hh; omega)
  change weightedHomogeneousComponent (slotWeight A) d (c g * (g : SlotRing A)) ∈ J
  rw [← heq, component_mul A (hD g)]
  exact homogeneous_mul_mem A J g (N g) (hN g)
    (weightedHomogeneousComponent_mem _ _ _) hdiff
variable {A : Fin 4 → Finset Exponent}
private theorem relationIdeal_le (k : ℕ) :
    relationIdeal A k ≤ (prefixIdeal A k).comap (dehom A).toRingHom :=
  Ideal.span_le.mpr fun _ h => h.2
private theorem relationIdeal_homogeneous (k : ℕ) :
    (relationIdeal A k).IsHomogeneous (slotPiece A) :=
  Ideal.homogeneous_span _ _ fun _ h => h.1
private theorem prefix_mono {k l : ℕ} (h : k ≤ l) : prefixIdeal A k ≤ prefixIdeal A l :=
  Ideal.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)
private theorem relation_mono {k l : ℕ} (h : k ≤ l) : relationIdeal A k ≤ relationIdeal A l :=
  Ideal.span_mono fun _ hf => ⟨hf.1, prefix_mono h hf.2⟩
private def nextIdeal (A : Fin 4 → Finset Exponent) (i : Fin 4) : Ideal (SlotRing A) :=
  relationIdeal A i.val ⊔ Ideal.span {homogeneousEquation A i}
private theorem cutIdeal_le_next (i : Fin 4) : cutIdeal A (i.val + 1) ≤ nextIdeal A i := by
  apply sup_le ((relation_mono (Nat.zero_le i.val)).trans le_sup_left)
  apply Ideal.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  change j.val < i.val + 1 at hj
  by_cases hji : j = i
  · subst j
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
  · have hlt : j.val < i.val := by
      have hn : j.val ≠ i.val := fun he => hji (Fin.ext he)
      omega
    apply Submodule.mem_sup_left
    apply Ideal.subset_span
    exact ⟨⟨_, homogeneousEquation_mem j⟩, by
      rw [dehom_equation]
      exact Ideal.subset_span ⟨j, hlt, rfl⟩⟩
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2_4_2.c3 := by
  classical
  intro A hz hv
  have hlocal (i : Fin 4) (f : SlotRing A) (hf : f ∈ relationGenerators A (i.val + 1))
      (b : (j : Fin 4) → ↥(A j)) : ∃ n : ℕ, chartProduct A b ^ n * f ∈ nextIdeal A i := by
    obtain ⟨n, hn⟩ := h1 A hz hv i f hf
    obtain ⟨m, hm⟩ := h2 A hz i b f n hn
    exact ⟨m, cutIdeal_le_next i hm⟩
  choose q hq using fun i : Fin 4 => high_degree_mem A (i.val + 1) (nextIdeal A i) (hlocal i)
  refine ⟨Finset.univ.sup q, ?_⟩
  intro i d hd p hp hpI
  have hp' : p ∈ (slotPiece A (shift d i 1)).map (dehom A).toLinearMap := by
    rwa [map_slotPiece]
  obtain ⟨f, hf, hfp⟩ := hp'
  change dehom A f = p at hfp
  have hfI : f ∈ relationIdeal A (i.val + 1) :=
    Ideal.subset_span ⟨⟨_, hf⟩, hfp ▸ hpI⟩
  have hqd (j : Fin 4) : q i ≤ shift d i 1 j :=
    (Finset.le_sup (f := q) (Finset.mem_univ i)).trans
      ((hd j).trans (Nat.le_add_right _ _))
  have hJ := hq i _ hqd f hf hfI
  change f ∈ relationIdeal A i.val ⊔ Ideal.span {homogeneousEquation A i} at hJ
  rw [sup_comm] at hJ
  obtain ⟨m, g, hg, hsum⟩ := Ideal.mem_span_singleton_sup.mp hJ
  let r := weightedHomogeneousComponent (slotWeight A) d m
  let s := weightedHomogeneousComponent (slotWeight A) (shift d i 1) g
  have hs : s ∈ relationIdeal A i.val :=
    weightedHomogeneousComponent_mem_of_mem _ _ (relationIdeal_homogeneous i.val) hg _
  have hfg : r * homogeneousEquation A i + s = f := by
    have he := congrArg (weightedHomogeneousComponent (slotWeight A) (shift d i 1)) hsum
    rw [map_add, weightedHomogeneousComponent_eq_self (show f.IsWeightedHomogeneous _ _ from hf)]
      at he
    change weightedHomogeneousComponent (slotWeight A) (d + Pi.single i 1)
      (m * homogeneousEquation A i) + s = f at he
    rwa [component_mul A (homogeneousEquation_mem i)] at he
  have hsI : dehom A s ∈ prefixIdeal A i.val := relationIdeal_le i.val hs
  refine ⟨dehom A r, ?_, ?_⟩
  · rw [← map_slotPiece]
    exact ⟨r, weightedHomogeneousComponent_mem _ _ _, rfl⟩
  · have he := congrArg (dehom A) hfg
    rw [map_add, map_mul, dehom_equation, hfp] at he
    rw [← he, mul_comm (genericEquation A i), add_sub_cancel_left]
    exact hsI
end
end K1_13_5_4_2_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1
noncomputable section
open K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_4 MvPolynomial
abbrev Affine (L : Type) [CommRing L] := MvPolynomial (Fin 4) L
def equationsIdeal {L : Type} [CommRing L] (f : Fin 4 → Affine L) :
    Ideal (Affine L) :=
  Ideal.span (Set.range f)
abbrev Total (L : Type) [Field L] := Affine (Polynomial L)
abbrev ParameterField (L : Type) [Field L] := FractionRing (Polynomial L)
def reduce {L : Type} [Field L] : Total L →+* Affine L :=
  MvPolynomial.map (Polynomial.evalRingHom 0)
def toGeneric {L : Type} [Field L] : Total L →+* Affine (ParameterField L) :=
  MvPolynomial.map (algebraMap (Polynomial L) (ParameterField L))
abbrev GenericFiber {L : Type} [Field L] (g : Fin 4 → Total L) :=
  Affine (ParameterField L) ⧸ (equationsIdeal g).map toGeneric
def genericClass {L : Type} [Field L] (g : Fin 4 → Total L) :
    Total L →+* GenericFiber g :=
  (Ideal.Quotient.mk _).comp toGeneric
abbrev rationalIdeal {L : Type} [Field L] (y : Fin 4 → L) : Ideal (Affine L) :=
  vanishingIdeal L {y}
abbrev PointLocal {L : Type} [Field L] (y : Fin 4 → L) :=
  Localization.AtPrime (rationalIdeal y)
abbrev PointAlgebra {L : Type} [Field L] (I : Ideal (Affine L)) (y : Fin 4 → L) :=
  PointLocal y ⧸ I.map (algebraMap (Affine L) (PointLocal y))
def pointClass {L : Type} [Field L] (I : Ideal (Affine L)) (y : Fin 4 → L) :
    Affine L →ₐ[L] PointAlgebra I y :=
  (Ideal.Quotient.mkₐ L _).comp (IsScalarTower.toAlgHom L (Affine L) (PointLocal y))
abbrev totalPrime {L : Type} [Field L] (y : Fin 4 → L) : Ideal (Total L) :=
  (rationalIdeal y).comap reduce
instance totalPrime_isPrime {L : Type} [Field L] (y : Fin 4 → L) :
    (totalPrime y).IsPrime :=
  Ideal.IsPrime.comap reduce
abbrev TotalLocal {L : Type} [Field L] (y : Fin 4 → L) :=
  Localization.AtPrime (totalPrime y)
abbrev BranchAlgebra {L : Type} [Field L] (g : Fin 4 → Total L) (y : Fin 4 → L) :=
  TotalLocal y ⧸ (equationsIdeal g).map (algebraMap (Total L) (TotalLocal y))
def branchClass {L : Type} [Field L] (g : Fin 4 → Total L) (y : Fin 4 → L) :
    Total L →+* BranchAlgebra g y :=
  (Ideal.Quotient.mk _).comp (algebraMap (Total L) (TotalLocal y))
def branchParameter {L : Type} [Field L] (g : Fin 4 → Total L) (y : Fin 4 → L) :
    BranchAlgebra g y :=
  branchClass g y (MvPolynomial.C Polynomial.X)
def extendPoint (L : Type) [Field L] [Algebra GeometricX L] (y : JetPoint) : Fin 4 → L :=
  fun i => algebraMap GeometricX L (y i)
def extendIdeal (L : Type) [Field L] [Algebra GeometricX L]
    (I : Ideal (GeoRow 4)) : Ideal (Affine L) :=
  I.map (MvPolynomial.map (algebraMap GeometricX L))
end
end K1_13_5_4_2_4_1
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
def liftRaw : Row 3 →ₐ[(Polynomial Geom)] Row 4 := MvPolynomial.rename Fin.castSucc
abbrev liftSep (f : Row 3) : Row 4 := liftRaw (K1_13_5.separant f)
def graphRaw (f : Row 3) : Row 4 :=
  liftRaw (lowerTangent f) + 3 * MvPolynomial.X 3 * liftSep f
def thirdVelocityNumerator (f : Row 3) : Row 4 :=
  MvPolynomial.C (Polynomial.C (-(3 : Geom)⁻¹)) * K1_13_6.partialFlow (graphRaw f)
def liftedStep (f : Row 3) (a : ℕ) (b : Row 4) : Row 4 :=
  liftSep f * K1_13_6.partialFlow b + thirdVelocityNumerator f * MvPolynomial.pderiv 3 b -
    (a : Row 4) * K1_13_6.partialFlow (liftSep f) * b
def thirdNumerator (f : Row 3) : ℕ → Row 4
  | 0 => MvPolynomial.X 3
  | k + 1 => liftedStep f k (thirdNumerator f k)
def thirdScale : ℕ → Geom
  | 0 => 1
  | k + 1 => thirdScale k * ((k + 4 : ℕ) : Geom)⁻¹
def jetNumerator (f : Row 3) (j : ℕ) : Row 4 :=
  if h : j < 3 then
    MvPolynomial.X ⟨j, h.trans (by decide : 3 < 4)⟩
  else
    MvPolynomial.C (Polynomial.C (thirdScale (j - 3))) *
      thirdNumerator f (j - 3)
def padJet (f : Row 3) (d j : ℕ) : Row 4 :=
  liftSep f ^ (d - (j - 3)) * jetNumerator f j
def centre : GeometricX := genericCoeff Polynomial.X
end
end K1_13_5_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_5_4_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
def c3 : Prop :=
  ∀ (f : Row 3) (P : Ideal (GeoRow 3)),
    Irreducible f → 0 < f.degreeOf 2 → ¬ Whole f →
    P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f)) →
    (MvPolynomial.affineHilbertPolynomial P).natDegree = 1
def c4 : Prop :=
  ∀ (f : Row 3) (P : Ideal (GeoRow 3)),
    P.IsPrime → genericRow (separant f) ∉ P →
    (MvPolynomial.affineHilbertPolynomial P).natDegree = 1 →
    (curveIdeal f P).IsPrime ∧ (MvPolynomial.affineHilbertPolynomial (curveIdeal f P)).natDegree = 1
end
end K1_13_5_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
open scoped BigOperators Pointwise
theorem firstBody_zero : FirstBody (0 : Set ExponentSpace) := by
  refine ⟨⟨0, Set.finite_zero, convexHull_zero.symm⟩, by simp, ?_⟩
  intro x hx
  rw [Set.mem_zero] at hx
  simp [hx]
theorem FirstBody.add {P Q : Set ExponentSpace} (hP : FirstBody P) (hQ : FirstBody Q) :
    FirstBody (P + Q) := by
  obtain ⟨v, hv, hvP⟩ := hP.polytope
  obtain ⟨w, hw, hwQ⟩ := hQ.polytope
  refine ⟨⟨v + w, hv.add hw, by rw [hvP, hwQ, convexHull_add]⟩, ?_, ?_⟩
  · exact Set.mem_add.mpr ⟨0, hP.zero_mem, 0, hQ.zero_mem, zero_add 0⟩
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
    simp [Pi.add_apply, hP.zero_height y hy, hQ.zero_height z hz]
theorem capBody_convex (s : Shape) (h : ℕ) : Convex ℝ (capBody s h) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx, hxb, hxj, hxt, hxh⟩ := hx
  obtain ⟨hy, hyb, hyj, hyt, hyh⟩ := hy
  simp only [capBody, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)), ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hxb ha, mul_le_mul_of_nonneg_left hyb hb,
      congrArg (fun r : ℝ => r * (s.b : ℝ)) hab]
  · nlinarith [mul_le_mul_of_nonneg_left hxj ha, mul_le_mul_of_nonneg_left hyj hb,
      congrArg (fun r : ℝ => r * (s.j : ℝ)) hab]
  · nlinarith [mul_le_mul_of_nonneg_left hxt ha, mul_le_mul_of_nonneg_left hyt hb,
      congrArg (fun r : ℝ => r * (s.t : ℝ)) hab]
  · nlinarith [mul_le_mul_of_nonneg_left hxh ha, mul_le_mul_of_nonneg_left hyh hb,
      congrArg (fun r : ℝ => r * (h : ℝ)) hab]
private theorem downBody_polytope (F : GeoRow 4) :
    ∃ v : Set ExponentSpace, v.Finite ∧ downBody F = convexHull ℝ v := by
  let corners (a : ↥F.support) : Set ExponentSpace :=
    Set.univ.pi (fun j => ({0, (a.val j : ℝ)} : Set ℝ))
  let v := ⋃ a, corners a
  refine ⟨v, Set.finite_iUnion (fun a => Set.Finite.pi (fun j => by simp)), ?_⟩
  have hc (a : ↥F.support) : convexHull ℝ (corners a) =
      {x : ExponentSpace | ∀ j, 0 ≤ x j ∧ x j ≤ (a.val j : ℝ)} := by
    dsimp only [corners]
    rw [convexHull_pi]
    have hseg (j : Fin 4) : convexHull ℝ ({0, (a.val j : ℝ)} : Set ℝ) =
        Set.Icc 0 (a.val j : ℝ) := by
      rw [convexHull_pair, segment_eq_Icc (by positivity)]
    simp only [hseg, Set.pi_univ_Icc]
    ext x
    exact forall_and.symm
  unfold downBody
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull _ _)
    rintro x ⟨a, ha, hx⟩
    have hx' : x ∈ convexHull ℝ (corners ⟨a, ha⟩) := by rwa [hc]
    exact convexHull_mono (Set.subset_iUnion corners ⟨a, ha⟩) hx'
  · apply convexHull_mono
    intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    have hx' : x ∈ convexHull ℝ (corners a) := subset_convexHull ℝ _ ha
    rw [hc] at hx'
    exact ⟨a.val, a.property, hx'⟩
def rowShape (f : Row 3) : Shape := ⟨f.totalDegree, indexDegree f, f.degreeOf 2⟩
theorem row_support (f : Row 3) :
    InLiftedBox (liftRow (genericRow f)) (rowShape f) 0 := by
  classical
  intro a ha
  rw [liftRow, support_rename_of_injective (Fin.castSucc_injective 3)] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hb' : b ∈ f.support := support_map_subset _ _ hb
  have htotal : b.degree ≤ f.totalDegree := le_totalDegree hb'
  have hindex : b.sum (fun j a => j.val * a) ≤ indexDegree f :=
    Finset.le_sup (f := fun m => m.sum (fun j a => j.val * a)) hb'
  have htop := monomial_le_degreeOf 2 hb'
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at htotal
  rw [Finsupp.sum_fintype _ _ (fun j => mul_zero j.val), Fin.sum_univ_three] at hindex
  have h0 : Finsupp.mapDomain Fin.castSucc b 0 = b 0 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 0
  have h1 : Finsupp.mapDomain Fin.castSucc b 1 = b 1 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 1
  have h2 : Finsupp.mapDomain Fin.castSucc b 2 = b 2 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 2
  have h3 : Finsupp.mapDomain Fin.castSucc b 3 = 0 :=
    Finsupp.mapDomain_of_notMem_range b _ (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)
  simp only [h0, h1, h2, h3, rowShape, le_refl, and_true]
  exact ⟨htotal, by simpa using hindex, htop⟩
theorem downBody_subset {F : GeoRow 4} {s : Shape} {h : ℕ}
    (hs : InLiftedBox F s h) : downBody F ⊆ capBody s h := by
  apply convexHull_min _ (capBody_convex s h)
  rintro x ⟨a, ha, hx⟩
  obtain ⟨hb, hj, ht, hh⟩ := hs a ha
  have hb' : (a 0 : ℝ) + a 1 + a 2 ≤ s.b := by exact_mod_cast hb
  have hj' : (a 1 : ℝ) + 2 * a 2 ≤ s.j := by exact_mod_cast hj
  exact ⟨fun j => (hx j).1, by linarith [(hx 0).2, (hx 1).2, (hx 2).2],
    by linarith [(hx 1).2, (hx 2).2], (hx 2).2.trans (by exact_mod_cast ht),
    (hx 3).2.trans (by exact_mod_cast hh)⟩
theorem firstBody_row {f : Row 3} (hf : f ≠ 0) : FirstBody (downBody (liftRow (genericRow f))) := by
  have hg : genericRow f ≠ 0 := by
    simpa only [genericRow, map_zero] using (map_injective _ genericCoeff_injective).ne hf
  have hF : liftRow (genericRow f) ≠ 0 := by
    simpa only [liftRow, map_zero] using
      (rename_injective Fin.castSucc (Fin.castSucc_injective 3)).ne hg
  obtain ⟨a, ha⟩ := support_nonempty.mpr hF
  refine ⟨downBody_polytope _, subset_convexHull ℝ _ ⟨a, ha, fun _ => ⟨le_rfl, by positivity⟩⟩, ?_⟩
  intro x hx
  have hc := downBody_subset (row_support f) hx
  exact le_antisymm (by simpa using hc.2.2.2.2) (hc.1 3)
end
end K1_13_5_4_2_5
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5
noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 MeasureTheory
open scoped BigOperators Pointwise
private theorem split_cap {x A B : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : x ≤ A + B) : ∃ y, 0 ≤ y ∧ y ≤ A ∧ 0 ≤ x - y ∧ x - y ≤ B := by
  refine ⟨min x A, le_min hx hA, min_le_right _ _, sub_nonneg.mpr (min_le_left _ _), ?_⟩
  rcases le_total x A with hle | hle
  · simpa only [min_eq_left hle, sub_self] using hB
  · rw [min_eq_right hle]
    linarith
theorem capBody_zero : capBody ⟨0, 0, 0⟩ 0 = 0 := by
  ext x
  rw [Set.mem_zero]
  constructor
  · intro hx
    obtain ⟨hx, hb, _, _, hh⟩ := hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    norm_num at hb hh
    funext i
    change x i = 0
    fin_cases i
    · change x 0 = 0
      linarith
    · change x 1 = 0
      linarith
    · change x 2 = 0
      linarith
    · change x 3 = 0
      linarith
  · rintro rfl
    simp [capBody]
private theorem capBody_split {p q : Shape} (hp : Chamber p) (hq : Chamber q)
    {h k : ℕ} {x : ExponentSpace} (hx : x ∈ capBody (p.plus q) (h + k)) :
    x ∈ capBody p h + capBody q k := by
  obtain ⟨hx, hb, hj, ht, hh⟩ := hx
  simp only [Shape.plus, Nat.cast_add] at hb hj ht hh
  have hpj : (p.j : ℝ) ≤ p.b := by exact_mod_cast hp.1
  have hqj : (q.j : ℝ) ≤ q.b := by exact_mod_cast hq.1
  have hpt : 2 * (p.t : ℝ) ≤ p.j := by exact_mod_cast hp.2
  have hqt : 2 * (q.t : ℝ) ≤ q.j := by exact_mod_cast hq.2
  obtain ⟨z, hz, hzp, hz', hzq⟩ := split_cap (hx 2) (by positivity) (by positivity) ht
  obtain ⟨v, hv, hvp, hv', hvq⟩ := split_cap (hx 1)
    (show 0 ≤ (p.j : ℝ) - 2 * z by linarith)
    (show 0 ≤ (q.j : ℝ) - 2 * (x 2 - z) by linarith) (by linarith)
  obtain ⟨u, hu, hup, hu', huq⟩ := split_cap (hx 0)
    (show 0 ≤ (p.b : ℝ) - v - z by linarith)
    (show 0 ≤ (q.b : ℝ) - (x 1 - v) - (x 2 - z) by linarith) (by linarith)
  obtain ⟨w, hw, hwp, hw', hwq⟩ := split_cap (hx 3) (by positivity) (by positivity) hh
  let y : ExponentSpace := ![u, v, z, w]
  have hy : y ∈ capBody p h := by
    refine ⟨?_, ?_, ?_, hzp, hwp⟩
    · intro i
      fin_cases i <;> assumption
    · change u + v + z ≤ (p.b : ℝ)
      linarith
    · change v + 2 * z ≤ (p.j : ℝ)
      linarith
  have hy' : x - y ∈ capBody q k := by
    refine ⟨?_, ?_, ?_, hzq, hwq⟩
    · intro i
      fin_cases i <;> assumption
    · change (x 0 - u) + (x 1 - v) + (x 2 - z) ≤ (q.b : ℝ)
      linarith
    · change (x 1 - v) + 2 * (x 2 - z) ≤ (q.j : ℝ)
      linarith
  exact Set.mem_add.mpr ⟨y, hy, x - y, hy', by abel⟩
theorem capBody_add {p q : Shape} (hp : Chamber p) (hq : Chamber q) (h k : ℕ) :
    capBody (p.plus q) (h + k) = capBody p h + capBody q k := by
  apply Set.Subset.antisymm (fun _ hx => capBody_split hp hq hx)
  intro x hx
  obtain ⟨y, ⟨hy, hyb, hyj, hyt, hyh⟩, z, ⟨hz, hzb, hzj, hzt, hzh⟩, rfl⟩ := Set.mem_add.mp hx
  refine ⟨fun i => add_nonneg (hy i) (hz i), ?_, ?_, ?_, ?_⟩ <;>
    simp only [Pi.add_apply, Shape.plus, Nat.cast_add] <;> linarith
def sumShape {ι : Type} (S : Finset ι) (p : ι → Shape) : Shape :=
  ⟨∑ i ∈ S, (p i).b, ∑ i ∈ S, (p i).j, ∑ i ∈ S, (p i).t⟩
theorem sumChamber {ι : Type} (S : Finset ι) (p : ι → Shape)
    (hp : ∀ i, Chamber (p i)) : Chamber (sumShape S p) := by
  constructor
  · exact Finset.sum_le_sum (fun i _ => (hp i).1)
  · change 2 * (∑ i ∈ S, (p i).t) ≤ ∑ i ∈ S, (p i).j
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hp i).2)
theorem sum_capBody {ι : Type} (S : Finset ι) (p : ι → Shape)
    (h : ι → ℕ) (hp : ∀ i, Chamber (p i)) :
    (∑ i ∈ S, capBody (p i) (h i)) = capBody (sumShape S p) (∑ i ∈ S, h i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [sumShape, Finset.sum_empty, capBody_zero]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, ih, ← capBody_add (hp i) (sumChamber S p hp)]
    simp only [sumShape, Shape.plus, Finset.sum_insert hi]
end
end K1_13_5_4_2_5
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 Polynomial MvPolynomial
open K1_13_6 (coefficientDerivative partialFlow flowNumerator eval_flowNumerator)
private theorem coeff_coeffDerivative {r : ℕ} (P : Row r) (m : Fin r →₀ ℕ) :
    (coeffDerivative P).coeff m = (P.coeff m).derivative := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
private theorem coefficientDerivative_lift (P : Row 3) :
    coefficientDerivative (liftRaw P) = liftRaw (coeffDerivative P) := by
  apply MvPolynomial.ext
  intro m
  change (coeffDerivative (liftRaw P)).coeff m = _
  rw [coeff_coeffDerivative]
  change ((rename Fin.castSucc P).coeff m).derivative =
    (rename Fin.castSucc (coeffDerivative P)).coeff m
  by_cases h : ∃ u : Fin 3 →₀ ℕ, u.mapDomain Fin.castSucc = m
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain _ (Fin.castSucc_injective 3), coeff_rename_mapDomain _ (Fin.castSucc_injective 3),
      coeff_coeffDerivative]
  · rw [coeff_rename_eq_zero _ _ _ (fun u hu => (h ⟨u, hu⟩).elim),
      coeff_rename_eq_zero _ _ _ (fun u hu => (h ⟨u, hu⟩).elim), map_zero]
theorem pderiv_last_lift (P : Row 3) : pderiv 3 (liftRaw P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [liftRaw]
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | mul_X P i h =>
    have hi : i.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last i
    rw [map_mul, show liftRaw (MvPolynomial.X i) = MvPolynomial.X i.castSucc from rename_X _ _,
      pderiv_mul, h, pderiv_X_of_ne hi, zero_mul, mul_zero, zero_add]
theorem partialFlow_lift (P : Row 3) : partialFlow (liftRaw P) = graphRaw P := by
  unfold partialFlow graphRaw lowerTangent
  rw [coefficientDerivative_lift, Fin.sum_univ_three]
  have hs (i : Fin 3) : pderiv i.castSucc (liftRaw P) = liftRaw (pderiv i P) :=
    pderiv_rename (Fin.castSucc_injective 3) i P
  have hx (i : Fin 3) : liftRaw (MvPolynomial.X i) = MvPolynomial.X i.castSucc := rename_X _ _
  have hc (a : ℕ) : MvPolynomial.C (Polynomial.C (a : Geom)) = (a : Row 4) := by
    rw [Polynomial.C_eq_natCast, map_natCast]
  simp only [hs, hx, hc, map_add, map_mul, map_ofNat]
  change _ = liftRaw (coeffDerivative P) + MvPolynomial.X 1 * liftRaw (pderiv 0 P) +
      2 * MvPolynomial.X 2 * liftRaw (pderiv 1 P) + 3 * MvPolynomial.X 3 * liftRaw (pderiv 2 P)
  norm_num [Fin.val_succ, Fin.val_zero]
  ring
theorem graph_separant (f : Row 3) : K1_13_6.separant (graphRaw f) = 3 * liftSep f := by
  have h3 : pderiv 3 (3 : Row 4) = 0 := (pderiv (R := (Polynomial Geom)) (3 : Fin 4)).map_natCast 3
  simp [K1_13_6.separant, graphRaw, pderiv_last_lift, h3, mul_comm]
theorem geomCast_ne_zero {a : ℕ} (ha : 0 < a) (hp : a < K1.p) : (a : Geom) ≠ 0 := by
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  intro hz
  exact (not_le_of_gt hp) (Nat.le_of_dvd ha ((CharP.cast_eq_zero_iff Geom K1.p a).mp hz))
private theorem three_ne_zero : (3 : (Polynomial Geom)) ≠ 0 := by
  have h := geomCast_ne_zero (a := 3) (by decide) (by decide)
  exact Polynomial.C_ne_zero.mpr h
@[simp] theorem atJet_lift (P : Row 3) (S : (Polynomial Geom)) : atJet (liftRaw P) S = atJet P S :=
  eval_rename _ _ _
theorem derivative_atJet (P : Row 3) (S : (Polynomial Geom)) :
    derivative (atJet P S) = atJet (graphRaw P) S := by
  let g : Row 4 := MvPolynomial.X 3 - MvPolynomial.C (jet S (3 : Fin 4))
  have hg : atJet g S = 0 := by simp [atJet, g]
  have hsep : K1_13_6.separant g = 1 := by
    simp [K1_13_6.separant, g]
  have h := eval_flowNumerator g (liftRaw P) S hg
  unfold flowNumerator at h
  rw [hsep, show K1_13_6.separant (liftRaw P) = 0 from pderiv_last_lift P,
    mul_zero, sub_zero, one_mul, partialFlow_lift, atJet_lift,
    show atJet (1 : Row 4) S = 1 by exact map_one _, one_mul] at h
  exact h.symm
theorem graph_atJet_zero {f : Row 3} {S : (Polynomial Geom)} (h : atJet f S = 0) :
    atJet (graphRaw f) S = 0 := by
  rw [← derivative_atJet, h, map_zero]
private theorem three_mul_velocity (f : Row 3) :
    3 * thirdVelocityNumerator f = -partialFlow (graphRaw f) := by
  let c : Geom →+* Row 4 := (MvPolynomial.C : (Polynomial Geom) →+* Row 4).comp Polynomial.C
  have h : (3 : Geom) * -(3 : Geom)⁻¹ = -1 := by
    have hn : (3 : Geom) ≠ 0 := geomCast_ne_zero (a := 3) (by decide) (by decide)
    rw [mul_neg, mul_inv_cancel₀ hn]
  change c 3 * (c (-(3 : Geom)⁻¹) * _) = _
  rw [← mul_assoc, ← map_mul, h, map_neg, map_one]
  ring
private theorem atJet_liftedFlow (f : Row 3) (b : Row 4) (S : (Polynomial Geom))
    (hf : atJet f S = 0) :
    atJet (liftSep f * partialFlow b + thirdVelocityNumerator f * pderiv 3 b) S =
      atJet (liftSep f) S * derivative (atJet b S) := by
  have hpoly : flowNumerator (graphRaw f) b =
      3 * (liftSep f * partialFlow b + thirdVelocityNumerator f * pderiv 3 b) := by
    rw [flowNumerator, graph_separant, K1_13_6.separant, mul_add, ← mul_assoc, ← mul_assoc,
      three_mul_velocity]
    ring
  have h := eval_flowNumerator (graphRaw f) b S (graph_atJet_zero hf)
  rw [hpoly, graph_separant] at h
  let e := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
  change e (3 * _) = e (3 * _) * _ at h
  rw [map_mul, map_mul, map_ofNat, mul_assoc] at h
  exact mul_left_cancel₀ three_ne_zero h
private theorem atJet_partialFlow_sep (f : Row 3) (S : (Polynomial Geom)) :
    atJet (partialFlow (liftSep f)) S = derivative (atJet (liftSep f) S) := by
  rw [partialFlow_lift, ← derivative_atJet, atJet_lift]
private theorem clear_one_derivative (a : ℕ) (u v : (Polynomial Geom)) :
    u * derivative (u ^ a * v) - (a : (Polynomial Geom)) * derivative u * (u ^ a * v) =
      u ^ (a + 1) * derivative v := by
  cases a with
  | zero => simp
  | succ a =>
    rw [derivative_mul, derivative_pow, Nat.succ_sub_one, pow_succ u (a+1)]
    simp only [Polynomial.C_eq_natCast]
    push_cast
    rw [pow_succ u a]
    ring
theorem atJet_thirdNumerator (f : Row 3) (S : (Polynomial Geom)) (hf : atJet f S = 0) (k : ℕ) :
    atJet (thirdNumerator f k) S = atJet (liftSep f) S ^ k *
      ((derivative (R := Geom))^[k]) (jet S (3 : Fin 4)) := by
  induction k with
  | zero => simp [thirdNumerator, atJet]
  | succ k ih =>
    let e := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
    change e (liftedStep f k (thirdNumerator f k)) = _
    unfold liftedStep
    rw [map_sub, map_mul, map_mul, map_natCast]
    change atJet (liftSep f * partialFlow (thirdNumerator f k) +
        thirdVelocityNumerator f * pderiv 3 (thirdNumerator f k)) S -
        (k : (Polynomial Geom)) * atJet (partialFlow (liftSep f)) S * atJet (thirdNumerator f k) S = _
    rw [atJet_liftedFlow _ _ _ hf, atJet_partialFlow_sep, ih, clear_one_derivative,
      Function.iterate_succ_apply']
theorem derivative_hasse (S : (Polynomial Geom)) (k : ℕ) :
    derivative (hasseDeriv k S) = Polynomial.C ((k+1 : ℕ) : Geom) * hasseDeriv (k+1) S := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := Geom) 1 k) S
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul, Polynomial.C_eq_natCast, Nat.add_comm, add_mul] using h
end
end K1_13_5_4_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
section Branch
variable {L : Type} [Field L]
private def localReduce (y : Fin 4 → L) : TotalLocal y →+* PointLocal y :=
  Localization.localRingHom (totalPrime y) (rationalIdeal y) reduce rfl
private def branchReduce (g : Fin 4 → Total L) (y : Fin 4 → L) :
    BranchAlgebra g y →+* PointAlgebra (equationsIdeal fun i => reduce (g i)) y := by
  refine Ideal.quotientMap _ (localReduce y) ?_
  rw [Ideal.map_le_iff_le_comap, equationsIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change localReduce y (algebraMap (Total L) (TotalLocal y) (g i)) ∈
    (equationsIdeal fun i => reduce (g i)).map (algebraMap (Affine L) (PointLocal y))
  rw [localReduce, Localization.localRingHom_to_map]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))
private theorem branchReduce_class (g : Fin 4 → Total L) (y : Fin 4 → L) (p : Total L) :
    branchReduce g y (branchClass g y p) =
      pointClass (equationsIdeal fun i => reduce (g i)) y (reduce p) := by
  simp [branchReduce, branchClass, pointClass, localReduce]
private theorem clear_generic_ideal (g : Fin 4 → Total L) (p : Total L)
    (h : genericClass g p = 0) :
    ∃ d : Polynomial L, d ≠ 0 ∧ C d * p ∈ equationsIdeal g := by
  let : Algebra (Total L) (Affine (ParameterField L)) := MvPolynomial.algebraMvPolynomial
  let S := (Polynomial L)⁰.map (C (σ := Fin 4))
  have : IsLocalization S (Affine (ParameterField L)) :=
    MvPolynomial.isLocalization (Polynomial L)⁰ (ParameterField L)
  have hmem : algebraMap (Total L) (Affine (ParameterField L)) p ∈
      (equationsIdeal g).map (algebraMap (Total L) (Affine (ParameterField L))) :=
    Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨_, ⟨d, hd, rfl⟩, hp⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff S _ (equationsIdeal g) p).mp hmem
  exact ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, hp⟩
theorem relation_vanishes (g : Fin 4 → Total L) (y : Fin 4 → L)
    (hreg : IsSMulRegular (BranchAlgebra g y) (branchParameter g y))
    (p : Total L) (hp : genericClass g p = 0) :
    pointClass (equationsIdeal fun i => reduce (g i)) y (reduce p) = 0 := by
  obtain ⟨d, hd0, hd⟩ := clear_generic_ideal g p hp
  obtain ⟨q, hfactor, hq⟩ := d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd0 (0 : L)
  rw [Polynomial.C_0, sub_zero] at hfactor hq
  have hu : C q ∉ totalPrime y := by
    change reduce (C q) ∉ rationalIdeal y
    rw [mem_vanishingIdeal_singleton_iff]
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero] at hq
    simpa [reduce] using hq
  have hunit : IsUnit (branchClass g y (C q)) :=
    (IsLocalization.map_units (TotalLocal y) (⟨C q, hu⟩ : (totalPrime y).primeCompl)).map
      (Ideal.Quotient.mk _)
  have hz : branchClass g y (C d * p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hd)
  have hz' : branchParameter g y ^ d.rootMultiplicity 0 *
      (branchClass g y (C q) * branchClass g y p) = 0 := by
    rw [hfactor] at hz
    simpa only [map_mul, map_pow, mul_assoc, branchParameter] using hz
  have hz'' : branchClass g y (C q) * branchClass g y p = 0 :=
    (hreg.pow (d.rootMultiplicity 0)) (by simpa only [smul_eq_mul, mul_zero] using hz')
  have hp' : branchClass g y p = 0 :=
    hunit.mul_left_cancel (by simpa only [mul_zero] using hz'')
  rw [← branchReduce_class, hp', map_zero]
end Branch
section Rank
variable {L : Type} [Field L]
private theorem reduce_surjective : Function.Surjective (reduce (L := L)) := by
  apply MvPolynomial.map_surjective
  intro a
  exact ⟨Polynomial.C a, Polynomial.eval_C⟩
private theorem class_C (g : Fin 4 → Total L) (a : Polynomial L) :
    genericClass g (C a) =
      algebraMap (ParameterField L) (GenericFiber g)
        (algebraMap (Polynomial L) (ParameterField L) a) := by
  change Ideal.Quotient.mk _
    (MvPolynomial.map (algebraMap (Polynomial L) (ParameterField L)) (C a)) = _
  rw [map_C]
  rfl
theorem specialization_rank (g : Fin 4 → Total L)
    {D : Type} [AddCommGroup D] [Module L D]
    (s : Affine L →ₗ[L] D) (hs : Function.Surjective s)
    (hrel : ∀ p, genericClass g p = 0 → s (reduce p) = 0)
    [Module.Finite (ParameterField L) (GenericFiber g)] :
    Module.finrank L D ≤ Module.finrank (ParameterField L) (GenericFiber g) := by
  classical
  let n := Module.finrank L D
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := L) (M := D)
    (show n ≤ Module.finrank L D from le_rfl)
  choose p hp using fun i => (hs.comp reduce_surjective) (b i)
  let v (i : Fin n) := genericClass g (p i)
  let inc := algebraMap (Polynomial L) (ParameterField L)
  have hsum (a : Fin n → Polynomial L) :
      genericClass g (∑ i, C (a i) * p i) = ∑ i, inc (a i) • v i := by
    simp only [map_sum, map_mul, class_C]
    apply Finset.sum_congr rfl
    intro i _
    exact (Algebra.smul_def (inc (a i)) (v i)).symm
  have hconstant (a : Fin n → Polynomial L) (ha : (∑ i, inc (a i) • v i) = 0) (i : Fin n) :
      (a i).eval 0 = 0 := by
    have hz := hrel _ ((hsum a).trans ha)
    have hrow (j : Fin n) :
        s (reduce (C (a j) * p j)) = (a j).eval 0 • b j := by
      rw [map_mul]
      change s (MvPolynomial.map (Polynomial.evalRingHom 0) (C (a j)) * reduce (p j)) = _
      rw [map_C, MvPolynomial.C_mul', map_smul]
      rw [show s (reduce (p j)) = b j from hp j]
      rfl
    simp only [map_sum, hrow] at hz
    exact Fintype.linearIndependent_iff.mp hb _ hz i
  suffices hv : LinearIndependent (ParameterField L) v by
    simpa [n] using hv.fintype_card_le_finrank
  refine Fintype.linearIndependent_iff.mpr fun a ha j => ?_
  by_contra hj
  obtain ⟨den, hden⟩ := IsLocalization.exist_integer_multiples_of_finite (Polynomial L)⁰ a
  choose c hc using hden
  have hden0 : inc den ≠ 0 := by
    simpa only [inc, map_zero] using
      (IsFractionRing.injective (Polynomial L) (ParameterField L)).ne
        (mem_nonZeroDivisors_iff_ne_zero.mp den.prop)
  have hc' (i : Fin n) : inc (c i) = inc den * a i :=
    (hc i).trans (Algebra.smul_def (den : Polynomial L) (a i))
  have hcj : c j ≠ 0 := by
    intro hz
    exact (mul_ne_zero hden0 hj) (by rw [← hc', hz, map_zero])
  have hc0 : (∑ i, inc (c i) • v i) = 0 := by
    simp only [hc', mul_smul, ← Finset.smul_sum, ha, smul_zero]
  let P (d : ℕ) := ∃ a : Fin n → Polynomial L,
    a j ≠ 0 ∧ (a j).natDegree = d ∧ (∑ i, inc (a i) • v i) = 0
  have hP : ∃ d, P d := ⟨(c j).natDegree, c, hcj, rfl, hc0⟩
  obtain ⟨a, haj, hdeg, ha0⟩ := Nat.find_spec hP
  have hdiv (i : Fin n) : Polynomial.X ∣ a i := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hconstant a ha0 i
  choose a' ha' using hdiv
  have ha'j : a' j ≠ 0 := by
    intro hz
    exact haj (by rw [ha' j, hz, mul_zero])
  have hX : inc Polynomial.X ≠ 0 := by
    simpa only [inc, map_zero] using
      (IsFractionRing.injective (Polynomial L) (ParameterField L)).ne Polynomial.X_ne_zero
  have ha'0 : (∑ i, inc (a' i) • v i) = 0 := by
    have h : inc Polynomial.X • (∑ i, inc (a' i) • v i) = 0 := by
      simp only [Finset.smul_sum, ← mul_smul, ← inc.map_mul, ← ha', ha0]
    exact (smul_eq_zero.mp h).resolve_left hX
  have hmin := Nat.find_min' hP (show P (a' j).natDegree from ⟨a', ha'j, rfl, ha'0⟩)
  rw [ha' j, Polynomial.natDegree_X_mul ha'j] at hdeg
  omega
end Rank
section IsolatedPoints
open scoped Function
variable {L : Type} [Field L]
private theorem pointIdeal_injective : Function.Injective (rationalIdeal (L := L)) := by
  intro x y h
  funext j
  have hx : MvPolynomial.X j - C (x j) ∈ rationalIdeal x := by
    rw [mem_vanishingIdeal_singleton_iff]
    simp
  rw [h, mem_vanishingIdeal_singleton_iff] at hx
  simpa [sub_eq_zero, eq_comm] using hx
theorem pointClass_ker_contains_power (I : Ideal (Affine L)) (y : Fin 4 → L)
    (hy : rationalIdeal y ∈ I.minimalPrimes) :
    ∃ n : ℕ, rationalIdeal y ^ n ≤ RingHom.ker (pointClass I y).toRingHom := by
  let T := PointLocal y
  let J := I.map (algebraMap (Affine L) T)
  have hm : IsLocalRing.maximalIdeal T ∈ J.minimalPrimes := by
    rw [show J = I.map (algebraMap (Affine L) T) from rfl,
      IsLocalization.minimalPrimes_map (rationalIdeal y).primeCompl T, Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal T (rationalIdeal y)]
    exact hy
  have : IsArtinianRing (T ⧸ J) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J hm
  obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  refine ⟨n, fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hn ?_)⟩
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (rationalIdeal y) T, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hp
theorem pointClass_surjective (I : Ideal (Affine L)) (y : Fin 4 → L)
    (n : ℕ) (hn : rationalIdeal y ^ n ≤ RingHom.ker (pointClass I y).toRingHom) :
    Function.Surjective (pointClass I y) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (rationalIdeal y).primeCompl z
  have hcop : IsCoprime (rationalIdeal y) (Ideal.span {(s : Affine L)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have he := (inferInstance : (rationalIdeal y).IsMaximal).eq_of_le h le_sup_left
    have hle : Ideal.span {(s : Affine L)} ≤
        rationalIdeal y ⊔ Ideal.span {(s : Affine L)} := le_sup_right
    have hm := hle (Ideal.mem_span_singleton_self (s : Affine L))
    rw [← he] at hm
    exact s.prop hm
  obtain ⟨a, ha, b, hb, hab⟩ := (hcop.pow_left (m := n)).exists
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hb
  have hs : pointClass I y (s : Affine L) * pointClass I y w = 1 := by
    have hz : pointClass I y a = 0 := hn ha
    simpa only [map_add, map_mul, hz, zero_add, map_one] using congrArg (pointClass I y) hab
  have hr : pointClass I y r =
      Ideal.Quotient.mk _ (IsLocalization.mk' (PointLocal y) r s) *
        pointClass I y (s : Affine L) := by
    let mk := Ideal.Quotient.mk (I.map (algebraMap (Affine L) (PointLocal y)))
    change mk (algebraMap (Affine L) (PointLocal y) r) =
      mk (IsLocalization.mk' (PointLocal y) r s) *
        mk (algebraMap (Affine L) (PointLocal y) s)
    rw [← map_mul, IsLocalization.mk'_spec]
  refine ⟨r * w, ?_⟩
  rw [map_mul, hr, mul_assoc, hs, mul_one]
theorem points_surjective (I : Ideal (Affine L)) {ι : Type} [Fintype ι]
    (y : ι → Fin 4 → L) (hy : Function.Injective y)
    (hmin : ∀ i, rationalIdeal (y i) ∈ I.minimalPrimes) :
    Function.Surjective (AlgHom.pi fun i => pointClass I (y i)) := by
  classical
  choose n hn using fun i => pointClass_ker_contains_power I (y i) (hmin i)
  intro z
  choose r hr using fun i => pointClass_surjective I (y i) (n i) (hn i) (z i)
  have hcop : Pairwise (IsCoprime on fun i => rationalIdeal (y i) ^ n i) := by
    intro i j hij
    have hne : rationalIdeal (y i) ≠ rationalIdeal (y j) :=
      fun he => hij (hy (pointIdeal_injective he))
    exact (Ideal.isCoprime_of_isMaximal hne).pow_left.pow_right
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal hcop r
  refine ⟨p, funext fun i => ?_⟩
  change pointClass I (y i) p = z i
  rw [← hr i, ← sub_eq_zero, ← map_sub]
  exact hn i (hp i)
end IsolatedPoints
end
end K1_13_5_4_2_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace K1_13_5_4_3_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem flat_rowToGeo : Module.Flat (Row 3) (GeoRow 3) := by
  have : Module.Flat (Polynomial Geom) RationalX :=
    IsLocalization.flat RationalX (nonZeroDivisors (Polynomial Geom))
  have : Module.Flat (Polynomial Geom) GeometricX :=
    Module.Flat.trans (Polynomial Geom) RationalX GeometricX
  have h : Algebra.IsPushout (Polynomial Geom) (Row 3) GeometricX (GeoRow 3) := inferInstance
  exact Module.Flat.isBaseChange (Polynomial Geom) (Row 3) GeometricX (GeoRow 3) h.out
theorem rowToGeo_eq (b : Row 3) :
    algebraMap (Row 3) (GeoRow 3) b = genericRow b := by
  exact congrArg (fun g => MvPolynomial.map g b)
    (IsScalarTower.algebraMap_eq (Polynomial Geom) RationalX GeometricX)
@[simp] private theorem coeff_coeffDerivative (b : Row 3) (m : Fin 3 →₀ ℕ) :
    (coeffDerivative b).coeff m = derivative (b.coeff m) := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coeffDerivative_add (a b : Row 3) :
    coeffDerivative (a + b) = coeffDerivative a + coeffDerivative b := by
  ext m
  simp
private theorem coeffDerivative_mul (a b : Row 3) :
    coeffDerivative (a * b) = coeffDerivative a * b + a * coeffDerivative b := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffDerivative]
  change derivative ((a * b).coeff m) =
    (coeffDerivative a * b).coeff m + (a * coeffDerivative b).coeff m
  simp only [coeff_coeffDerivative, MvPolynomial.coeff_mul, map_sum, derivative_mul,
    Finset.sum_add_distrib]
theorem tangentNumerator_add (f a b : Row 3) :
    tangentNumerator f (a + b) = tangentNumerator f a + tangentNumerator f b := by
  simp only [tangentNumerator, lowerTangent, coeffDerivative_add, map_add]
  ring
theorem tangentNumerator_mul (f a b : Row 3) :
    tangentNumerator f (a * b) = tangentNumerator f a * b + a * tangentNumerator f b := by
  simp only [tangentNumerator, lowerTangent, coeffDerivative_mul, MvPolynomial.pderiv_mul]
  ring
theorem tangent_self (f : Row 3) : tangentNumerator f f = 0 := by
  unfold tangentNumerator separant
  exact sub_eq_zero.mpr (mul_comm _ _)
end
end K1_13_5_4_3_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3_2
noncomputable section
open K1_13_5_4_2_4_2 K1_13_5_4_2_4_2_3 MvPolynomial
abbrev Geo := K1_13_5_4.GeometricX
abbrev Supports := Fin 4 → Finset K1_13_5_4_2_4.Exponent
private abbrev degreeExponent : Degree ≃+ (Fin 4 →₀ ℕ) :=
  Finsupp.addEquivFunOnFinite.symm
private def affineExponent (A : Supports) : (Slot A →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
  Finsupp.weight fun v => v.2.val
private def taggedExponent (A : Supports) : (Slot A →₀ ℕ) →+ ((Fin 4 ⊕ Fin 4) →₀ ℕ) :=
  Finsupp.sumFinsuppAddEquivProdFinsupp.symm.toAddMonoidHom.comp
    ((degreeExponent.toAddMonoidHom.comp (Finsupp.weight (slotWeight A))).prod (affineExponent A))
private theorem taggedExponent_eq {A : Supports} {e f : Slot A →₀ ℕ} :
    taggedExponent A e = taggedExponent A f ↔
      Finsupp.weight (slotWeight A) e = Finsupp.weight (slotWeight A) f ∧
        affineExponent A e = affineExponent A f := by
  change Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_, _) =
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_, _) ↔ _
  rw [EquivLike.apply_eq_iff_eq, Prod.ext_iff]
  change (degreeExponent (Finsupp.weight (slotWeight A) e) =
    degreeExponent (Finsupp.weight (slotWeight A) f) ∧ _) ↔ _
  rw [EquivLike.apply_eq_iff_eq]
private def monomialHom {R σ τ : Type*} [CommRing R] (w : (σ →₀ ℕ) →+ (τ →₀ ℕ)) :
    MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  AddMonoidAlgebra.mapDomainAlgHom R R w
private theorem monomialHom_apply {R σ τ : Type*} [CommRing R]
    (w : (σ →₀ ℕ) →+ (τ →₀ ℕ)) (e : σ →₀ ℕ) (c : R) :
    monomialHom w (monomial e c) = monomial (w e) c := by
  change AddMonoidAlgebra.mapDomain w (AddMonoidAlgebra.single e c) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl
def binomialIdeal (A : Supports) (R : Type*) [CommRing R] : Ideal (MvPolynomial (Slot A) R) :=
  Ideal.span {p | ∃ e f : Slot A →₀ ℕ, taggedExponent A e = taggedExponent A f ∧
    p = monomial e 1 - monomial f 1}
theorem map_binomialIdeal {R S : Type*} [CommRing R] [CommRing S]
    (A : Supports) (g : R →+* S) :
    (binomialIdeal A R).map (MvPolynomial.map g) = binomialIdeal A S := by
  rw [binomialIdeal, Ideal.map_span, binomialIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨e, f, h, rfl⟩, rfl⟩
    exact ⟨e, f, h, by simp⟩
  · rintro ⟨e, f, h, rfl⟩
    exact ⟨_, ⟨e, f, h, rfl⟩, by simp⟩
private theorem lift_monomials {A : Supports} {R τ : Type*} [CommRing R]
    (s : Set (Slot A →₀ ℕ)) (w : (Slot A →₀ ℕ) → (τ →₀ ℕ))
    (h : ∀ e ∈ s, ∀ f ∈ s, w e = w f → taggedExponent A e = taggedExponent A f) :
    ∃ l : MvPolynomial τ R →ₗ[R] (MvPolynomial (Slot A) R ⧸ binomialIdeal A R),
      ∀ e ∈ s, l (monomial (w e) 1) = Ideal.Quotient.mk _ (monomial e 1) := by
  classical
  let J := binomialIdeal A R
  let g (a : τ →₀ ℕ) : MvPolynomial (Slot A) R ⧸ J :=
    if ha : ∃ e ∈ s, w e = a then Ideal.Quotient.mk J (monomial ha.choose 1) else 0
  refine ⟨(basisMonomials τ R).constr R g, fun e he => ?_⟩
  change (basisMonomials τ R).constr R g ((basisMonomials τ R) (w e)) = _
  rw [Module.Basis.constr_basis]
  let he' : ∃ f ∈ s, w f = w e := ⟨e, he, rfl⟩
  dsimp only [g]
  rw [dite_eq_left he', Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span ⟨_, _, h _ he'.choose_spec.1 e he he'.choose_spec.2, rfl⟩
private theorem tagged_ker (A : Supports) (R : Type*) [CommRing R] :
    RingHom.ker (monomialHom (R := R) (taggedExponent A)).toRingHom = binomialIdeal A R := by
  let J := binomialIdeal A R
  let φ := monomialHom (R := R) (taggedExponent A)
  obtain ⟨l, hl⟩ := lift_monomials (R := R) Set.univ (taggedExponent A)
    (fun _ _ _ _ h => h)
  have hfac : l.comp φ.toLinearMap = (Ideal.Quotient.mkₐ R J).toLinearMap := by
    apply (basisMonomials (Slot A) R).ext
    intro e
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [show φ (monomial e 1) = monomial (taggedExponent A e) 1 from monomialHom_apply _ _ _]
    exact hl e (Set.mem_univ _)
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := DFunLike.congr_fun hfac p
    change l (φ p) = Ideal.Quotient.mk J p at h
    change φ p = 0 at hp
    simpa [hp] using h.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, f, h, rfl⟩
    change monomialHom (R := R) (taggedExponent A) (monomial e 1 - monomial f 1) = 0
    rw [map_sub, monomialHom_apply, monomialHom_apply, h, sub_self]
private theorem dehom_eq_monomialHom (A : Supports) :
    dehom A = monomialHom (affineExponent A) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [dehom, aeval_X, MvPolynomial.X, monomialHom_apply, affineExponent, Finsupp.weight_single, one_smul]
theorem relationIdeal_zero (A : Supports) :
    relationIdeal A 0 = binomialIdeal A (K1_13_5_4_2_4.CoefficientField A) := by
  classical
  have hprefix : prefixIdeal A 0 = ⊥ := by simp [prefixIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨⟨d, hd⟩, hp⟩
    have hz : dehom A p = 0 := by simpa [hprefix] using hp
    let J := binomialIdeal A (K1_13_5_4_2_4.CoefficientField A)
    obtain ⟨l, hl⟩ := lift_monomials (R := K1_13_5_4_2_4.CoefficientField A)
      {e | Finsupp.weight (slotWeight A) e = d} (affineExponent A)
      (fun e he f hf h => taggedExponent_eq.mpr ⟨he.trans hf.symm, h⟩)
    let q := Ideal.Quotient.mkₐ (K1_13_5_4_2_4.CoefficientField A) J
    have hfac : l (dehom A p) = q p := by
      calc
        l (dehom A p) = l (dehom A (∑ e ∈ p.support, monomial e (p.coeff e))) :=
          congrArg (fun r => l (dehom A r)) p.as_sum
        _ = q (∑ e ∈ p.support, monomial e (p.coeff e)) := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro e he
          rw [show monomial e (p.coeff e) = p.coeff e • monomial e 1 by
            simp [smul_monomial]]
          simp only [map_smul, dehom_eq_monomialHom, monomialHom_apply,
            hl e (hd (mem_support_iff.mp he))]
          rfl
        _ = q p := (congrArg q p.as_sum).symm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [← hfac, hz, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, f, h, rfl⟩
    obtain ⟨hd, ha⟩ := taggedExponent_eq.mp h
    apply Ideal.subset_span
    refine ⟨⟨_, Submodule.sub_mem (slotPiece A (Finsupp.weight (slotWeight A) e)) ?_ ?_⟩, ?_⟩
    · exact isWeightedHomogeneous_monomial _ _ _ rfl
    · exact isWeightedHomogeneous_monomial _ _ _ hd.symm
    · rw [hprefix, Ideal.mem_bot, map_sub, dehom_eq_monomialHom,
        monomialHom_apply, monomialHom_apply, ha, sub_self]
abbrev MonomialRing (A : Supports) := MvPolynomial (Slot A) Geo ⧸ binomialIdeal A Geo
instance (A : Supports) : IsDomain (MonomialRing A) := by
  have : (binomialIdeal A Geo).IsPrime := by
    rw [← tagged_ker]
    exact RingHom.ker_isPrime _
  infer_instance
theorem monomialCoordinate_ne_zero {A : Supports} (v : Slot A) :
    Ideal.Quotient.mk (binomialIdeal A Geo) (MvPolynomial.X v) ≠ 0 := by
  intro h
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [← tagged_ker] at hm
  change monomialHom (R := Geo) (taggedExponent A) (MvPolynomial.X v) = 0 at hm
  rw [MvPolynomial.X, monomialHom_apply, monomial_eq_zero] at hm
  exact one_ne_zero hm
end
end K1_13_5_4_2_4_2_3_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2
noncomputable section
open MvPolynomial
open scoped BigOperators
variable {k σ : Type} [Field k] [Finite σ]
def linearForm (a : σ → k) : MvPolynomial σ k := by
  classical
  letI := Fintype.ofFinite σ
  exact ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i
def fiberIdeal (I : Ideal (MvPolynomial σ k)) (a : σ → k) (t : k) :
    Ideal (MvPolynomial σ k) :=
  I ⊔ Ideal.span {linearForm a - MvPolynomial.C t}
def projection (I : Ideal (MvPolynomial σ k)) (a : σ → k) :
    Polynomial k →ₐ[k] (MvPolynomial σ k ⧸ I) :=
  Polynomial.aeval (Ideal.Quotient.mk I (linearForm a))
def IsSeparating (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime) (a : σ → k) : Prop :=
  letI : I.IsPrime := hI
  let u : FractionRing (MvPolynomial σ k ⧸ I) :=
    algebraMap (MvPolynomial σ k ⧸ I) _ (Ideal.Quotient.mk I (linearForm a))
  Transcendental k u ∧
    Algebra.IsSeparable (IntermediateField.adjoin k ({u} : Set _))
      (FractionRing (MvPolynomial σ k ⧸ I))
end
end K1_13_5_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1
noncomputable section
open K1_13_5_4 K1_13_5_4_2_4 MvPolynomial
open scoped TensorProduct
private abbrev CoeffIndex (A : Fin 4 → Finset Exponent) := Σ i : Fin 4, ↥(A i)
private def center {A : Fin 4 → Finset Exponent} (f : Fin 4 → GeoRow 4)
    (a : CoeffIndex A) : GeometricX :=
  (f a.1).coeff a.2.1
private def coeffLine (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4)
    (a : CoeffIndex A) : Polynomial (CoefficientField A) :=
  Polynomial.C (algebraMap GeometricX (CoefficientField A) (center f a)) +
    Polynomial.X * Polynomial.C (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X a))
def deformation (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4)
    (i : Fin 4) : Total (CoefficientField A) :=
  ∑ a : ↥(A i), monomial a.1 (coeffLine A f ⟨i, a⟩)
private def coeffLineHom (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4) :
    CoefficientRing A →+* Polynomial (CoefficientField A) :=
  eval₂Hom (Polynomial.C.comp (algebraMap GeometricX (CoefficientField A))) (coeffLine A f)
private theorem coeffLineHom_injective (A : Fin 4 → Finset Exponent)
    (f : Fin 4 → GeoRow 4) : Function.Injective (coeffLineHom A f) := by
  let shift : CoefficientRing A →ₐ[GeometricX] CoefficientRing A :=
    aeval fun a => C (center f a) + MvPolynomial.X a
  let unshift : CoefficientRing A →ₐ[GeometricX] CoefficientRing A :=
    aeval fun a => MvPolynomial.X a - C (center f a)
  have hshift : unshift.comp shift = AlgHom.id GeometricX _ := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [shift, unshift, algebraMap_eq]
  have hleft : Function.LeftInverse unshift shift := fun p => AlgHom.congr_fun hshift p
  have heval : (Polynomial.evalRingHom 1).comp (coeffLineHom A f) =
      (algebraMap (CoefficientRing A) (CoefficientField A)).comp shift.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change Polynomial.eval 1 (coeffLineHom A f (C c)) =
        algebraMap (CoefficientRing A) (CoefficientField A) (shift (C c))
      rw [coeffLineHom, eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C, algHom_C]
      exact IsScalarTower.algebraMap_apply GeometricX (CoefficientRing A) (CoefficientField A) c
    · intro a
      change Polynomial.eval 1 (coeffLineHom A f (MvPolynomial.X a)) =
        algebraMap (CoefficientRing A) (CoefficientField A)
          (aeval (fun b => C (center f b) + MvPolynomial.X b) (MvPolynomial.X a))
      rw [coeffLineHom, MvPolynomial.eval₂Hom_X', aeval_X]
      simp only [coeffLine, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, one_mul, map_add]
      rw [IsScalarTower.algebraMap_apply GeometricX (CoefficientRing A) (CoefficientField A)]
      rfl
  intro p q hpq
  apply hleft.injective
  apply IsFractionRing.injective (CoefficientRing A) (CoefficientField A)
  exact (RingHom.congr_fun heval p).symm.trans
    ((congrArg (Polynomial.evalRingHom 1) hpq).trans (RingHom.congr_fun heval q))
private def genericCoeffMap (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4) :
    CoefficientField A →+* ParameterField (CoefficientField A) :=
  IsFractionRing.lift (g := (algebraMap (Polynomial (CoefficientField A))
      (ParameterField (CoefficientField A))).comp (coeffLineHom A f))
    ((IsFractionRing.injective (Polynomial (CoefficientField A)) (ParameterField (CoefficientField A))).comp
      (coeffLineHom_injective A f))
private theorem genericCoeffMap_coeff (A : Fin 4 → Finset Exponent)
    (f : Fin 4 → GeoRow 4) (a : CoeffIndex A) :
    genericCoeffMap A f (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X a)) =
      algebraMap (Polynomial (CoefficientField A)) (ParameterField (CoefficientField A))
        (coeffLine A f a) := by
  rw [genericCoeffMap, IsFractionRing.lift_algebraMap]
  simp [coeffLineHom]
theorem deformation_reduce (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4)
    (hs : ∀ i, (f i).support ⊆ A i) :
    equationsIdeal (fun i => reduce (deformation A f i)) = extendIdeal (CoefficientField A)
      (cutIdeal f) := by
  classical
  have hrow (i : Fin 4) : reduce (deformation A f i) =
      MvPolynomial.map (algebraMap GeometricX (CoefficientField A)) (f i) := by
    have hsum : (∑ a ∈ A i, monomial a ((f i).coeff a)) = f i := by
      rw [← Finset.sum_subset (hs i), ← MvPolynomial.as_sum]
      intro a _ ha
      rw [notMem_support_iff.mp ha, monomial_zero]
    conv_rhs => rw [← hsum]
    simp [reduce, deformation, coeffLine, center]
    exact Finset.sum_attach (A i)
      (fun a => monomial a (algebraMap GeometricX (CoefficientField A) ((f i).coeff a)))
  simp only [equationsIdeal, extendIdeal, cutIdeal, Ideal.map_span, ← Set.range_comp', hrow]
def baseQuotient {k L : Type} [Field k] [Field L] [Algebra k L]
    (I : Ideal (Affine k)) :
    L ⊗[k] (Affine k ⧸ I) ≃ₐ[L]
      Affine L ⧸ I.map (MvPolynomial.map (algebraMap k L)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) k L
  refine (Algebra.TensorProduct.tensorQuotientEquiv L (Affine k) L I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (MvPolynomial.map (algebraMap k L)) =
    (I.map (Algebra.TensorProduct.includeRight (A := L)).toRingHom).map
      e.toRingEquiv.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  change MvPolynomial.map (algebraMap k L) p = e (1 ⊗ₜ[k] p)
  simp [e]
private theorem finite_rank_map_ideal {k L : Type} [Field k] [Field L] [Algebra k L]
    (I : Ideal (Affine k)) [Module.Finite k (Affine k ⧸ I)] :
    Module.Finite L (Affine L ⧸ I.map (MvPolynomial.map (algebraMap k L))) ∧
    Module.finrank L (Affine L ⧸ I.map (MvPolynomial.map (algebraMap k L))) =
      Module.finrank k (Affine k ⧸ I) := by
  let e := (baseQuotient (L := L) I).toLinearEquiv
  exact ⟨Module.Finite.equiv e, e.finrank_eq.symm.trans Module.finrank_baseChange⟩
theorem deformation_generic (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4)
    (hf : Module.Finite (CoefficientField A) (GenericQuotient A)) :
    Module.Finite (ParameterField (CoefficientField A)) (GenericFiber (deformation A f)) ∧
    Module.finrank (ParameterField (CoefficientField A)) (GenericFiber (deformation A f)) =
      Module.finrank (CoefficientField A) (GenericQuotient A) := by
  let : Algebra (CoefficientField A) (ParameterField (CoefficientField A)) :=
    (genericCoeffMap A f).toAlgebra
  have hrow (i : Fin 4) :
      MvPolynomial.map (algebraMap (CoefficientField A) (ParameterField (CoefficientField A)))
          (genericEquation A i) = toGeneric (deformation A f i) := by
    change MvPolynomial.map (genericCoeffMap A f) (genericEquation A i) = _
    simp [genericEquation, toGeneric, deformation, genericCoeffMap_coeff]
  have hid :
      (Ideal.span (Set.range (genericEquation A))).map
          (MvPolynomial.map (algebraMap (CoefficientField A) (ParameterField (CoefficientField A)))) =
        (equationsIdeal (deformation A f)).map toGeneric := by
    simp only [equationsIdeal, Ideal.map_span, ← Set.range_comp', hrow]
  have := hf
  have hbase := finite_rank_map_ideal (L := ParameterField (CoefficientField A))
    (Ideal.span (Set.range (genericEquation A)))
  rw [hid] at hbase
  exact hbase
end
end K1_13_5_4_2_4_1
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
theorem genericCoeff_injective : Function.Injective genericCoeff :=
  (algebraMap RationalX GeometricX).injective.comp (IsFractionRing.injective _ _)
@[simp] theorem eval_genericRow {r : ℕ} (S : (Polynomial Geom)) (P : Row r) :
    MvPolynomial.eval (jetPoint S) (genericRow P) = genericCoeff (atJet P S) :=
  (MvPolynomial.map_eval genericCoeff (jet S) P).symm
theorem generic_lift (P : Row 3) : genericRow (liftRaw P) = liftRow (genericRow P) :=
  MvPolynomial.map_rename genericCoeff Fin.castSucc P
theorem generic_graph (f : Row 3) : genericRow (graphRaw f) = graph f := by
  unfold graphRaw graph
  change MvPolynomial.map genericCoeff (_ + _) = _
  rw [map_add, map_mul, map_mul, MvPolynomial.map_X, map_ofNat]
  exact congrArg₂ (· + 3 * MvPolynomial.X 3 * ·) (generic_lift _) (generic_lift _)
theorem genericCoeff_ne_zero {a : (Polynomial Geom)} (h : a ≠ 0) : genericCoeff a ≠ 0 := by
  intro ha
  exact h (genericCoeff_injective (ha.trans genericCoeff.map_zero.symm))
private theorem geometric_three_ne_zero : (3 : GeometricX) ≠ 0 := by
  have h := geomCast_ne_zero (a := 3) (by decide) (by decide)
  intro hz
  apply h
  apply (algebraMap Geom GeometricX).injective
  rw [map_natCast, map_zero]
  exact hz
theorem graphPoint_of_actual {f : Row 3} {S : (Polynomial Geom)} (hS : RegularAt 2 f S) :
    graphPoint f (jetPoint S) = jetPoint (n := 4) S := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hs : genericCoeff (atJet (separant f) S) ≠ 0 := genericCoeff_ne_zero hS.2
    have h := congrArg genericCoeff (graph_atJet_zero hS.1)
    change genericCoeff (MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom)) (_ + _)) = _ at h
    simp only [map_add, map_mul, map_ofNat, map_zero, MvPolynomial.eval_X,
      show ∀ p : Row 3, MvPolynomial.eval (jet S) (liftRaw p) = atJet p S from
        fun p => atJet_lift p S] at h
    unfold graphPoint
    rw [Fin.snoc_last, eval_genericRow, eval_genericRow,
      div_eq_iff (mul_ne_zero geometric_three_ne_zero hs)]
    change -genericCoeff (atJet (lowerTangent f) S) =
      genericCoeff (jet S (3 : Fin 4)) * (3 * genericCoeff (atJet (separant f) S))
    linear_combination -h
  · exact Fin.snoc_castSucc _ _ _
private theorem graphIdeal_eval_zero {f : Row 3} {S : (Polynomial Geom)} (hS : RegularAt 2 f S)
    {P : GeoRow 4} (hP : P ∈ graphIdeal f) :
    MvPolynomial.eval (jetPoint S) P = 0 := by
  let e := MvPolynomial.eval (jetPoint (n := 4) S)
  have hJ : graphIdeal f ≤ RingHom.ker e := by
    rw [graphIdeal, Ideal.span_le]
    intro p hp
    change e p = 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · simp [e, ← generic_lift, atJet_lift, hS.1]
    · simp [e, ← generic_graph, graph_atJet_zero hS.1]
  exact hJ hP
private theorem scaled_third (S : (Polynomial Geom)) (k : ℕ) (hk : k + 3 < K1.p) :
    Polynomial.C (thirdScale k) * ((derivative (R := Geom))^[k]) (jet S (3 : Fin 4)) =
      hasseDeriv (k+3) S := by
  induction k with
  | zero => simp [thirdScale, jet]
  | succ k ih =>
    have he := congrArg derivative (ih (by omega))
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_hasse] at he
    rw [thirdScale, map_mul, mul_comm (Polynomial.C (thirdScale k)), mul_assoc,
      Function.iterate_succ_apply', he, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ (geomCast_ne_zero (a := k+4) (by omega) (by omega)), map_one, one_mul]
private theorem atJet_jetNumerator (f : Row 3) (S : (Polynomial Geom)) (hf : atJet f S = 0)
    (j : ℕ) (hj : j < K1.p) :
    atJet (jetNumerator f j) S = atJet (liftSep f) S ^ (j-3) * hasseDeriv j S := by
  have hVar (i : Fin 4) : atJet (MvPolynomial.X i) S = hasseDeriv i.val S :=
    MvPolynomial.eval_X i
  unfold jetNumerator
  split_ifs with h
  · rw [hVar, show j - 3 = 0 by omega, pow_zero, one_mul]
  · let e := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
    change e (MvPolynomial.C _ * _) = _
    rw [map_mul, MvPolynomial.eval_C]
    change Polynomial.C _ * atJet (thirdNumerator f (j-3)) S = _
    rw [atJet_thirdNumerator _ _ hf, mul_left_comm, scaled_third S (j-3) (by omega),
      Nat.sub_add_cancel (by omega : 3 ≤ j)]
theorem atJet_padJet (f : Row 3) (S : (Polynomial Geom)) (hf : atJet f S = 0)
    (d j : ℕ) (hd : j - 3 ≤ d) (hj : j < K1.p) :
    atJet (padJet f d j) S = atJet (separant f) S ^ d * hasseDeriv j S := by
  let e := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
  change e (_ ^ _ * jetNumerator f j) = _
  rw [map_mul, map_pow]
  change atJet (liftSep f) S ^ _ * atJet (jetNumerator f j) S = _
  rw [atJet_jetNumerator f S hf j hj, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hd, atJet_lift]
private theorem taylor_coeff_generic (S : (Polynomial Geom)) (j : ℕ) :
    (taylor centre (S.map (algebraMap Geom GeometricX))).coeff j =
      genericCoeff (hasseDeriv j S) := by
  rw [taylor_coeff, hasseDeriv_map, Polynomial.eval_map]
  have he : Polynomial.eval₂RingHom (algebraMap Geom GeometricX) centre = genericCoeff := by
    apply Polynomial.ringHom_ext
    · intro a
      change (Polynomial.C a).eval₂ (algebraMap Geom GeometricX) centre = genericCoeff (Polynomial.C a)
      rw [eval₂_C]
      exact IsScalarTower.algebraMap_apply Geom (Polynomial Geom) GeometricX a
    · exact eval₂_X _ _
  exact RingHom.congr_fun he _
theorem taylor_coefficients_aux (S : (Polynomial Geom)) (m : ℕ) (hS : S.natDegree < m)
    (i : ℕ) :
    (∑ j : Fin m, ((Polynomial.X - Polynomial.C centre) ^ j.val).coeff i *
      genericCoeff (hasseDeriv j.val S)) = algebraMap Geom GeometricX (S.coeff i) := by
  let P := S.map (algebraMap Geom GeometricX)
  have hn : (taylor centre P).natDegree < m := by
    rw [natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt hS
  have Hd : (taylor centre P).degree < (m : WithBot ℕ) :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hn)
  have hsum : (∑ j : Fin m, Polynomial.C ((taylor centre P).coeff j.val) *
      (Polynomial.X - Polynomial.C centre) ^ j.val) = P := by
    exact (Polynomial.sum_fin
      (fun j (a : GeometricX) => Polynomial.C a * (Polynomial.X - Polynomial.C centre) ^ j)
      (fun _ => by rw [Polynomial.C_0, zero_mul]) Hd).trans (Polynomial.sum_taylor_eq P centre)
  calc
    _ = ∑ j : Fin m, (Polynomial.C ((taylor centre P).coeff j.val) *
        (Polynomial.X - Polynomial.C centre) ^ j.val).coeff i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [coeff_C_mul, taylor_coeff_generic, mul_comm]
    _ = P.coeff i := by rw [← finsetSum_coeff, hsum]
    _ = _ := Polynomial.coeff_map (algebraMap Geom GeometricX) i
theorem third_atJet_zero {f : Row 3} {S : (Polynomial Geom)} (hf : atJet f S = 0)
    (k : ℕ) (hk : S.natDegree - 3 < k) :
    atJet (thirdNumerator f k) S = 0 := by
  rw [atJet_thirdNumerator f S hf, iterate_derivative_eq_zero, mul_zero]
  exact (natDegree_hasseDeriv_le S 3).trans_lt hk
theorem actual_zero_of_represents {f old : Row 3} {P : GeoRow 4} {S : (Polynomial Geom)}
    (hS : RegularAt 2 f S) (hP : RepresentsOnGraph f old P)
    (hzero : MvPolynomial.eval (jetPoint S) P = 0) : atJet old S = 0 := by
  obtain ⟨a, b, c, hc, h⟩ := hP
  have he := graphIdeal_eval_zero hS h
  simp only [map_mul, map_pow, map_sub, hzero, mul_zero, MvPolynomial.eval_C,
    ← generic_lift, eval_genericRow, atJet_lift, zero_sub] at he
  have hs : genericCoeff (atJet (separant f) S) ≠ 0 :=
    genericCoeff_ne_zero hS.2
  have hq : genericCoeff (atJet old S) = 0 := by
    simpa [mul_eq_zero, pow_ne_zero _ hs, hc] using he
  exact genericCoeff_injective (by simpa only [map_zero] using hq)
end
end K1_13_5_4_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2
noncomputable section
open MvPolynomial
open scoped BigOperators Function
variable {k σ : Type} [Field k] [Finite σ]
theorem totalDegree_hyperplane_le_one (a : σ → k) (t : k) :
    (linearForm a - MvPolynomial.C t).totalDegree ≤ 1 := by
  classical
  apply (totalDegree_sub_C_le _ _).trans
  unfold linearForm
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add])
theorem zeroLocus_fiber_iff {I : Ideal (MvPolynomial σ k)} {a z : σ → k} {t : k} :
    z ∈ zeroLocus k (fiberIdeal I a t) ↔ z ∈ zeroLocus k I ∧ aeval z (linearForm a) = t := by
  rw [fiberIdeal, mem_zeroLocus_sup_span_singleton_iff, map_sub, aeval_C]
  exact and_congr_right fun _ => sub_eq_zero
theorem ncard_eq_affineDegree_of_radical [IsAlgClosed k] (J : Ideal (MvPolynomial σ k))
    (hJ : (affineHilbertPolynomial J).natDegree = 0) (hrad : J.IsRadical) :
    ((zeroLocus k J).ncard : ℚ) = affineDegree J := by
  classical
  let : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    natDegree_affineHilbertPolynomial_eq_zero_iff.mp hJ
  let zeros := zeroLocus k J
  have hZ : zeros.Finite := finite_zeroLocus_of_finite_quotient J
  let : Fintype zeros := hZ.fintype
  let e (x : zeros) : MvPolynomial σ k →ₐ[k] k := aeval x.val
  let M (x : zeros) := RingHom.ker (e x)
  have hpair : Pairwise (IsCoprime on M) := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, y.val i ≠ x.val i := by
      by_contra! he
      exact hxy (Subtype.ext (funext he).symm)
    let u : MvPolynomial σ k :=
      MvPolynomial.C ((y.val i - x.val i)⁻¹) * (MvPolynomial.X i - MvPolynomial.C (x.val i))
    have hx : e x u = 0 := by simp [e, u]
    have hy : e y u = 1 := by
      simp [e, u, inv_mul_cancel₀ (sub_ne_zero.mpr hi)]
    refine Ideal.isCoprime_iff_exists.mpr ⟨u, RingHom.mem_ker.mpr hx, 1 - u, ?_, by ring⟩
    exact RingHom.mem_ker.mpr (by rw [map_sub, map_one, hy, sub_self])
  let φ := AlgHom.pi e
  have hker : RingHom.ker φ = J := by
    calc
      _ = vanishingIdeal k zeros := by
        ext p
        rw [RingHom.mem_ker, mem_vanishingIdeal_iff]
        exact ⟨fun h x hx => congrFun h (⟨x, hx⟩ : zeros), fun h => funext fun x => h x.val x.property⟩
      _ = J := (vanishingIdeal_zeroLocus_eq_radical J).trans (Ideal.radical_eq_iff.mpr hrad)
  have hsurj : Function.Surjective φ := by
    intro d
    obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hpair
      (fun x => Ideal.Quotient.mk (M x) (MvPolynomial.C (d x)))
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨p, funext fun x => ?_⟩
    have hx := congrArg (Ideal.kerLiftAlg (e x)) (congrFun hq x)
    rw [Ideal.quotientInfToPiQuotient_mk', Ideal.kerLiftAlg_mk, Ideal.kerLiftAlg_mk] at hx
    simpa [φ, e] using hx
  let E := (Ideal.quotientEquivAlgOfEq k hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  rw [affineDegree_eq_finrank, E.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  exact_mod_cast (Nat.card_eq_fintype_card (α := zeros))
end
end K1_13_5_4_2_2
end
section
namespace K1_13_5_3
noncomputable section
open K1 K1_13 K1_13_5 Polynomial PolynomialDifferential
open scoped BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev CenterField := FractionRing (Polynomial Geom)
abbrev toCenter : (Polynomial Geom) →+* CenterField := algebraMap (Polynomial Geom) CenterField
abbrev constants : Geom →+* CenterField := toCenter.comp Polynomial.C
abbrev center : CenterField := toCenter Polynomial.X
def flatten (f : Row 2) : DifferentialPolynomial Geom 1 :=
  (MvPolynomial.optionEquivRight Geom (Fin 2)).symm f
def chart (f : Row 2) : DifferentialPolynomial CenterField 1 :=
  MvPolynomial.map constants (flatten f)
def plane (f : Row 2) : MvPolynomial (Fin 2) CenterField := MvPolynomial.map toCenter f
def marked (S : (Polynomial Geom)) : Fin 2 → CenterField :=
  polynomialJet center (S.map constants)
theorem toCenter_inj : Function.Injective toCenter := IsFractionRing.injective _ _
theorem eval_at_center (S : (Polynomial Geom)) : (S.map constants).eval center = toCenter S := by
  rw [Polynomial.eval_map]
  change eval₂RingHom constants center S = toCenter S
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [constants]
  · simp [center]
theorem marked_apply (S : (Polynomial Geom)) (i : Fin 2) :
    marked S i = toCenter (jet S i) := by
  change (hasseDeriv i.val (S.map constants)).eval center = _
  rw [Polynomial.hasseDeriv_map, eval_at_center]
  rfl
theorem marked_injective : Function.Injective marked := by
  intro S T heq
  have h := congrFun heq (0 : Fin 2)
  simpa only [marked_apply, jet, Fin.val_zero, Polynomial.hasseDeriv_zero',
    toCenter_inj.eq_iff] using h
theorem aeval_plane (f : Row 2) (S : (Polynomial Geom)) :
    MvPolynomial.aeval (marked S) (plane f) = toCenter (atJet f S) := by
  have hm : marked S = toCenter ∘ jet S := funext (marked_apply S)
  rw [plane, MvPolynomial.aeval_eq_eval, hm, atJet, ← MvPolynomial.map_eval]
theorem plane_ne_zero {f : Row 2} (hf : f ≠ 0) : plane f ≠ 0 :=
  fun h => hf ((MvPolynomial.map_injective _ toCenter_inj) (h.trans (map_zero _).symm))
theorem plane_prime {f : Row 2} (hf : Irreducible f) (hp : 0 < f.degreeOf 1) :
    (Ideal.span {plane f}).IsPrime := by
  let M := ((Polynomial Geom)⁰).map (MvPolynomial.C (σ := Fin 2))
  have hI : (Ideal.span {f}).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hdis : Disjoint (M : Set (Row 2)) (Ideal.span {f} : Ideal (Row 2)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hd
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hd
    have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hq' : q ≠ 0 := by
      intro h
      exact ha' (by simpa [h] using hq)
    have hh := congrArg (MvPolynomial.degreeOf (1 : Fin 2)) hq
    rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_mul_eq hf.ne_zero hq'] at hh
    omega
  have h := IsLocalization.isPrime_of_isPrime_disjoint M
    (MvPolynomial (Fin 2) CenterField) (Ideal.span {f}) hI hdis
  simpa only [plane, MvPolynomial.algebraMap_def, Ideal.map_span, Set.image_singleton] using h
theorem specialization_flatten (f : Row 2) (S : (Polynomial Geom)) :
    differentialSpecialization (flatten f) S = atJet f S := by
  let x : Option (Fin 2) → (Polynomial Geom) := fun
    | none => Polynomial.X
    | some i => jet S i
  have h := MvPolynomial.aeval_optionEquivRight_symm (R := Geom) x f
  have hx : x none = Polynomial.X := rfl
  have hj : (fun j => x (some j)) = jet S := rfl
  rw [hx, hj, Polynomial.aeval_X_left] at h
  rw [show (AlgHom.id Geom (Polynomial Geom)).toRingHom = RingHom.id ((Polynomial Geom)) from rfl,
    MvPolynomial.map_id, MvPolynomial.aeval_eq_eval] at h
  unfold flatten at *
  unfold atJet differentialSpecialization
  refine (AlgHom.congr_fun ?_ _).trans h
  apply MvPolynomial.algHom_ext
  intro v
  rw [differentialSpecializationHom, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  cases v <;> rfl
theorem chart_degree (f : Row 2) : jetTotalDegree (chart f) ≤ f.totalDegree := by
  apply (jetTotalDegree_map_le constants _).trans
  have hw : (jetDegreeWeight : Option (Fin 2) → ℕ) =
      fun v => v.elim 0 (fun _ => 1) := by
    funext v
    cases v <;> rfl
  rw [jetTotalDegree, hw, ← MvPolynomial.totalDegree_optionEquivRight]
  simp only [flatten, AlgEquiv.apply_symm_apply, le_refl]
theorem chart_top (f : Row 2) : (chart f).degreeOf (some 1) ≤ f.degreeOf 1 := by
  have h : (flatten f).degreeOf (some 1) = f.degreeOf 1 := by
    rw [← MvPolynomial.degreeOf_optionEquivRight]
    simp only [flatten, AlgEquiv.apply_symm_apply]
  rw [← h, MvPolynomial.degreeOf_def, MvPolynomial.degreeOf_def]
  exact Multiset.count_le_of_le _ MvPolynomial.degrees_map_le
theorem degreeOf_le_index (f : Row 2) : f.degreeOf 1 ≤ indexDegree f := by
  rw [MvPolynomial.degreeOf_eq_sup, indexDegree]
  exact Finset.sup_le fun m hm => by
    apply (Finset.le_sup (f := fun m : Fin 2 →₀ ℕ =>
      m.sum fun i a => i.val * a) hm).trans'
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
    simp
end
end K1_13_5_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
theorem graphCurve_comap {f : Row 3} {P : Ideal (GeoRow 3)} [P.IsPrime]
    (hsep : sep f ∉ P) : (graphCurve f P).comap (rename Fin.castSucc).toRingHom = P := by
  apply SetLike.ext
  intro a
  change liftRow a ∈ graphCurve f P ↔ a ∈ P
  constructor
  · intro ha
    have hh : sep f * a ∈ vanishingIdeal GeometricX (zeroLocus GeometricX P) := by
      intro x hx
      change eval x (sep f * a) = 0
      rw [map_mul]
      by_cases hs : eval x (sep f) = 0
      · rw [hs, zero_mul]
      · have he : eval (graphPoint f x) (liftRow a) = 0 := ha _ ⟨x, ⟨hx, hs⟩, rfl⟩
        rw [eval_liftRow_graphPoint] at he
        rw [he, mul_zero]
    rw [IsPrime.vanishingIdeal_zeroLocus] at hh
    exact (‹P.IsPrime›.mem_or_mem hh).resolve_left hsep
  · intro ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa only [aeval_eq_eval, eval_liftRow_graphPoint] using hx.1 a ha
theorem graphCurve_le_point {f : Row 3} {P : Ideal (GeoRow 3)} {y : JetPoint}
    (hy : y ∈ graphLocus f P) : graphCurve f P ≤ pointIdeal y :=
  vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hy)
theorem sep_notMem_point {f : Row 3} {P : Ideal (GeoRow 3)} {y : JetPoint}
    (hy : y ∈ graphLocus f P) : liftedSep f ∉ pointIdeal y := by
  obtain ⟨x, hx, rfl⟩ := hy
  intro hs
  apply hx.2
  rw [← eval_liftRow_graphPoint f x (sep f)]
  exact (mem_vanishingIdeal_singleton_iff _ _).mp hs
end
end K1_13_5_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 MeasureTheory
open scoped BigOperators Pointwise
def totalSupport (P : Set ExponentSpace) : ℝ :=
  sSup ((fun x : ExponentSpace => x 0 + x 1 + x 2) '' P)
def indexSupport (P : Set ExponentSpace) : ℝ :=
  sSup ((fun x : ExponentSpace => x 1 + 2 * x 2) '' P)
def topSupport (P : Set ExponentSpace) : ℝ :=
  sSup ((fun x : ExponentSpace => x 2) '' P)
def volumeQuotient (P C : Set ExponentSpace) (t : ℝ) : ℝ :=
  ((volume (t • P + C)).toReal - (volume C).toReal) / t
def capFirstVariation (s : Shape) (h : ℕ) (B J T : ℝ) : ℝ :=
  (h : ℝ) * ((s.t : ℝ) * ((s.j : ℝ) - s.t) * B +
    (s.t : ℝ) * ((s.b : ℝ) - s.j + (s.t : ℝ) / 2) * J +
    ((s.j : ℝ) - 2 * s.t) * ((s.b : ℝ) - (s.j : ℝ) / 2) * T)
end
end K1_13_5_4_2_5_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ (k σ : Type) [Field k] [IsAlgClosed k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)), I.IsPrime →
    (affineHilbertPolynomial I).natDegree = 1 →
    ∃ bad : Finset (Submodule k (σ → k)),
      (∀ B ∈ bad, B ≠ ⊤) ∧
      ∀ (a : σ → k), (∀ B ∈ bad, a ∉ B) →
        (projection I a).Finite ∧
        ∀ t : k, (affineHilbertPolynomial (fiberIdeal I a t)).natDegree = 0 ∧
          affineDegree (fiberIdeal I a t) = affineDegree I
def c2 : Prop :=
  ∀ (k σ : Type) [Field k] [IsAlgClosed k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime),
    (affineHilbertPolynomial I).natDegree = 1 →
    ∃ B : Submodule k (σ → k), B ≠ ⊤ ∧
      ∀ (a : σ → k), a ∉ B → IsSeparating I hI a
def c3 : Prop :=
  ∀ (k σ : Type) [Field k] [IsAlgClosed k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime)
    (a : σ → k), (projection I a).Finite → IsSeparating I hI a →
    ∃ bad : Finset k, ∀ t ∉ bad, (fiberIdeal I a t).IsRadical
end
end K1_13_5_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2
noncomputable section
open K1_13_5_4_2 MeasureTheory MvPolynomial
open scoped BigOperators Pointwise
def rest : Finset (Fin 4) := insert 1 (insert 2 (insert 3 ∅))
theorem univ_eq_insert : (Finset.univ : Finset (Fin 4)) = insert 0 rest := by decide
theorem zero_notMem_rest : (0 : Fin 4) ∉ rest := by decide
private theorem alternating_product (u v : Fin 4 → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * ∏ i, (if i ∈ S then u i else v i)) =
      ∏ i, (u i - v i) := by
  rw [univ_eq_insert]
  unfold rest
  simp only [
    Finset.sum_powerset_insert (a := (0 : Fin 4)) (s := insert 1 (insert 2 (insert 3 ∅))) (by decide),
    Finset.sum_powerset_insert (a := (1 : Fin 4)) (s := insert 2 (insert 3 ∅)) (by decide),
    Finset.sum_powerset_insert (a := (2 : Fin 4)) (s := insert 3 ∅) (by decide),
    Finset.sum_powerset_insert (a := (3 : Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem, Finset.mem_insert]
  ring
def weights (t : ℝ) (S : Finset (Fin 4)) (i : Fin 4) : ℝ :=
  if i ∈ S then (![t, 1, 1, 1] : Fin 4 → ℝ) i else 0
private theorem eval_as_sum (p : MvPolynomial (Fin 4) ℝ) (w : Fin 4 → ℝ) :
    p.eval w = ∑ d ∈ p.support, p.coeff d * ∏ i, (w i) ^ d i := by
  conv_lhs => rw [p.as_sum]
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [eval_monomial, Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (by simp)]
private theorem polar_eval (p : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * p.eval (weights t S)) =
      ∑ d ∈ p.support, p.coeff d * ∏ i, ((![t, 1, 1, 1] : Fin 4 → ℝ) i ^ d i - 0 ^ d i) := by
  simp_rw [eval_as_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  calc
    _ = ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
        p.coeff d * ((-1 : ℝ) ^ (4 - S.card) *
          ∏ i, (if i ∈ S then (![t, 1, 1, 1] : Fin 4 → ℝ) i ^ d i else 0 ^ d i)) := by
      apply Finset.sum_congr rfl
      intro S _
      have heq : (∏ i, weights t S i ^ d i) =
          ∏ i, (if i ∈ S then (![t, 1, 1, 1] : Fin 4 → ℝ) i ^ d i else 0 ^ d i) := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ S <;> simp [weights, hi]
      rw [heq]
      ring
    _ = _ := by
      rw [← Finset.mul_sum, alternating_product]
private theorem product_linear (d : Fin 4 →₀ ℕ) (hd : d.degree = 4) (t : ℝ) :
    (∏ i, ((![t, 1, 1, 1] : Fin 4 → ℝ) i ^ d i - 0 ^ d i)) =
      t * ∏ i, ((![1, 1, 1, 1] : Fin 4 → ℝ) i ^ d i - 0 ^ d i) := by
  by_cases hz : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]),
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
  · have hn (i : Fin 4) : 0 < d i := Nat.pos_of_ne_zero (fun hi => hz ⟨i, hi⟩)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hd
    have hones (i : Fin 4) : d i = 1 := by
      have h0 := hn 0
      have h1 := hn 1
      have h2 := hn 2
      have h3 := hn 3
      fin_cases i
      · change d 0 = 1
        omega
      · change d 1 = 1
        omega
      · change d 2 = 1
        omega
      · change d 3 = 1
        omega
    simp [hones, Fin.prod_univ_four]
theorem polar_linear (p : MvPolynomial (Fin 4) ℝ)
    (hp : p.IsHomogeneous 4) (t : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * p.eval (weights t S)) =
      t * ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
        (-1 : ℝ) ^ (4 - S.card) * p.eval (weights 1 S) := by
  rw [polar_eval, polar_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d.degree = 4 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hd)
  rw [product_linear d hd' t]
  ring
end
end K1_13_5_4_2_5_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3_2
noncomputable section
open K1_13_5_4_2_4_2_3 MvPolynomial
abbrev UniversalRing (A : Supports) := MvPolynomial (Slot A) (MonomialRing A)
def coordinate {A : Supports} (v : Slot A) : MonomialRing A :=
  Ideal.Quotient.mk (binomialIdeal A Geo) (MvPolynomial.X v)
def modelChart (A : Supports) (b : (j : Fin 4) → ↥(A j)) : MonomialRing A :=
  ∏ j : Fin 4, coordinate ⟨j, b j⟩
theorem modelChart_ne_zero (A : Supports) (b : (j : Fin 4) → ↥(A j)) :
    modelChart A b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => monomialCoordinate_ne_zero ⟨j, b j⟩
def modelEquation (A : Supports) (i : Fin 4) : UniversalRing A :=
  ∑ a : ↥(A i), C (coordinate ⟨i, a⟩) * MvPolynomial.X ⟨i, a⟩
def modelIdeal (A : Supports) (k : ℕ) : Ideal (UniversalRing A) :=
  Ideal.span (modelEquation A '' {i : Fin 4 | i.val < k})
private theorem substitution {L : Type*} [CommRing L] (A : Supports) (k : ℕ)
    (b : (j : Fin 4) → ↥(A j)) (z : Slot A → L) (w : Fin 4 → L)
    (hw : ∀ j, w j * z ⟨j, b j⟩ = 1) :
    ∃ E : MvPolynomial (Slot A) L →ₐ[L] MvPolynomial (Slot A) L,
      RingHom.ker E.toRingHom =
        Ideal.span ((fun j : Fin 4 => ∑ a : ↥(A j), C (z ⟨j, a⟩) * MvPolynomial.X ⟨j, a⟩) ''
          {j : Fin 4 | j.val < k}) := by
  classical
  let terms (j : Fin 4) (a : ↥(A j)) : MvPolynomial (Slot A) L :=
    C (z ⟨j, a⟩) * MvPolynomial.X ⟨j, a⟩
  let equation (j : Fin 4) := ∑ a, terms j a
  let rest (j : Fin 4) := ∑ a ∈ Finset.univ.erase (b j), terms j a
  let value (v : Slot A) : MvPolynomial (Slot A) L :=
    if v.1.val < k ∧ v.2 = b v.1 then - (C (w v.1) * rest v.1) else MvPolynomial.X v
  let E : MvPolynomial (Slot A) L →ₐ[L] MvPolynomial (Slot A) L := aeval value
  let J := Ideal.span (equation '' {j : Fin 4 | j.val < k})
  have hsum (j : Fin 4) : equation j = rest j + terms j (b j) :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ (b j))).symm
  have hrest (j : Fin 4) : E (rest j) = rest j := by
    simp only [rest, map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hne := (Finset.mem_erase.mp ha).1
    simp [terms, E, value, hne]
  have hpivot (j : Fin 4) (hj : j.val < k) :
      E (MvPolynomial.X ⟨j, b j⟩) = - (C (w j) * rest j) := by
    simp [E, value, hj]
  have hunit (j : Fin 4) : C (w j) * C (z ⟨j, b j⟩) = (1 : MvPolynomial (Slot A) L) := by
    rw [← map_mul, hw, map_one]
  refine ⟨E, show RingHom.ker E.toRingHom = J from le_antisymm ?_ ?_⟩
  · let q := Ideal.Quotient.mkₐ L J
    have hq : q.comp E = q := by
      apply MvPolynomial.algHom_ext
      rintro ⟨j, a⟩
      change q (E (MvPolynomial.X ⟨j, a⟩)) = q (MvPolynomial.X ⟨j, a⟩)
      by_cases h : j.val < k ∧ a = b j
      · obtain ⟨hj, rfl⟩ := h
        rw [hpivot j hj, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        rw [show - (C (w j) * rest j) - MvPolynomial.X ⟨j, b j⟩ =
          -(C (w j) * rest j + MvPolynomial.X ⟨j, b j⟩) by abel]
        apply J.neg_mem
        have he : equation j ∈ J := Ideal.subset_span ⟨j, hj, rfl⟩
        have hm := J.mul_mem_left (C (w j)) he
        simpa only [hsum j, terms, mul_add, ← mul_assoc, hunit j, one_mul] using hm
      · simp [E, value, h]
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    have hh := DFunLike.congr_fun hq p
    change q (E p) = q p at hh
    change E p = 0 at hp
    simpa only [hp, map_zero] using hh.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change E (equation j) = 0
    rw [hsum, map_add, hrest]
    simp only [terms, map_mul, hpivot j hj, mul_neg]
    rw [show E (C (z ⟨j, b j⟩)) = C (z ⟨j, b j⟩) by simp [E]]
    rw [← mul_assoc, mul_comm (C (z ⟨j, b j⟩)), hunit, one_mul, add_neg_cancel]
theorem model_saturate (A : Supports) (k : ℕ) (b : (j : Fin 4) → ↥(A j))
    {a : MonomialRing A} (ha : a ≠ 0) (u : UniversalRing A) (n : ℕ)
    (hu : C a ^ n * u ∈ modelIdeal A k) :
    ∃ m : ℕ, C (modelChart A b) ^ m * u ∈ modelIdeal A k := by
  classical
  let x := modelChart A b
  let L := Localization.Away x
  have hx : x ≠ 0 := modelChart_ne_zero A b
  let : IsDomain L := Localization.Away.isDomain hx
  let g := algebraMap (MonomialRing A) L
  let z (v : Slot A) := g (coordinate v)
  have hux : IsUnit (∏ j : Fin 4, z ⟨j, b j⟩) := by
    simp only [z, ← map_prod]
    change IsUnit (algebraMap (MonomialRing A) L x)
    exact IsLocalization.Away.algebraMap_isUnit (S := L) x
  have hz (j : Fin 4) : IsUnit (z ⟨j, b j⟩) :=
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => z ⟨i, b i⟩) (Finset.mem_univ j)) hux
  choose w hw using fun j => isUnit_iff_exists_inv.mp (hz j)
  obtain ⟨E, hE⟩ := substitution A k b z w (fun j => (mul_comm _ _).trans (hw j))
  let : Algebra (UniversalRing A) (MvPolynomial (Slot A) L) := MvPolynomial.algebraMvPolynomial
  let incl := algebraMap (UniversalRing A) (MvPolynomial (Slot A) L)
  let M := (Submonoid.powers x).map (C (σ := Slot A))
  have : IsLocalization M (MvPolynomial (Slot A) L) :=
    MvPolynomial.isLocalization (Submonoid.powers x) L
  have hincl : incl = MvPolynomial.map g := rfl
  have hJ : (modelIdeal A k).map incl = RingHom.ker E.toRingHom := by
    rw [hE, modelIdeal, Ideal.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    set_option synthInstance.maxHeartbeats 200000 in simp [hincl, modelEquation, z]
  have hmem := Ideal.mem_map_of_mem incl hu
  rw [hJ] at hmem
  change E (incl (C a ^ n * u)) = 0 at hmem
  have hga : g a ≠ 0 := by
    have hinj : Function.Injective g := IsLocalization.injective (S := L)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
    exact fun h => ha (hinj (h.trans (map_zero g).symm))
  have hEa : E (incl (C a)) = C (g a) := by simp [hincl]
  have heu : E (incl u) = 0 := by
    rw [map_mul, map_pow, map_mul, map_pow, hEa] at hmem
    exact (mul_eq_zero.mp hmem).resolve_left (pow_ne_zero _ (C_ne_zero.mpr hga))
  have hu' : incl u ∈ (modelIdeal A k).map incl := by rw [hJ]; exact heu
  obtain ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, hm⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M _ (modelIdeal A k) u).mp hu'
  exact ⟨m, by simpa only [map_pow] using hm⟩
end
end K1_13_5_4_2_4_2_3_2
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 MvPolynomial
open scoped Polynomial
private theorem partial_degree (P : Row 3) (i : Fin 3) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  simpa only [weightedTotalDegree_one, Pi.one_apply] using
    weightedTotalDegree_pderiv_le_sub (1 : Fin 3 → ℕ) i P
private theorem coeffDerivative_degree (P : Row 3) :
    (coeffDerivative P).totalDegree ≤ P.totalDegree := by
  unfold coeffDerivative
  exact totalDegree_finsetSum_le fun m hm =>
    (totalDegree_monomial_le _ _).trans (le_totalDegree hm)
private theorem nat_mul_degree (a : ℕ) (P : Row 3) :
    ((a : Row 3) * P).totalDegree ≤ P.totalDegree := by
  rw [← map_natCast (C : (Polynomial Geom) →+* Row 3) a]
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])
private theorem shift_degree (P : Row 3) (i j : Fin 3) :
    (MvPolynomial.X j * pderiv i P).totalDegree ≤ P.totalDegree := by
  by_cases h : P.totalDegree = 0
  · rw [totalDegree_eq_zero_iff_eq_C.mp h, pderiv_C, mul_zero, totalDegree_zero]
    exact Nat.zero_le _
  · have hp := partial_degree P i
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    omega
private theorem lowerTangent_degree (P : Row 3) :
    (lowerTangent P).totalDegree ≤ P.totalDegree := by
  unfold lowerTangent
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (coeffDerivative_degree P) (shift_degree P 0 1)))
    (by rw [mul_assoc]; exact (nat_mul_degree 2 _).trans (shift_degree P 1 2)))
private theorem tangent_degree (f P : Row 3) :
    (tangentNumerator f P).totalDegree ≤ P.totalDegree + (f.totalDegree - 1) := by
  unfold tangentNumerator
  apply (totalDegree_sub _ _).trans
  refine max_le ?_ ?_
  · have hs := partial_degree f 2
    have hl := lowerTangent_degree P
    apply (totalDegree_mul _ _).trans
    unfold separant
    omega
  · by_cases h : P.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C.mp h, pderiv_C, mul_zero, totalDegree_zero]
      exact Nat.zero_le _
    · have hl := lowerTangent_degree f
      have hp := partial_degree P 2
      apply (totalDegree_mul _ _).trans
      omega
theorem compatibility_degree (f : Row 3) (j : ℕ) :
    (compatibilityNumerator f j).totalDegree ≤ 1 + (2 * j + 1) * (f.totalDegree - 1) := by
  have hs : (separant f).totalDegree ≤ f.totalDegree - 1 := partial_degree f 2
  induction j with
  | zero =>
    rw [compatibilityNumerator, totalDegree_neg]
    have h := lowerTangent_degree f
    simp only [Nat.mul_zero, zero_add, one_mul]
    omega
  | succ j ih =>
    rw [compatibilityNumerator]
    let b := compatibilityNumerator f j
    change (separant f * tangentNumerator f b -
      ((2 * j + 1 : ℕ) : Row 3) * b * tangentNumerator f (separant f)).totalDegree ≤ _
    have h₁ := (totalDegree_mul (separant f) (tangentNumerator f b)).trans
      (Nat.add_le_add hs (tangent_degree f b))
    have h₂ := (totalDegree_mul (((2 * j + 1 : ℕ) : Row 3) * b)
      (tangentNumerator f (separant f))).trans
      (Nat.add_le_add (nat_mul_degree (2 * j + 1) b)
        ((tangent_degree f (separant f)).trans (Nat.add_le_add_right hs _)))
    have hstep := (totalDegree_sub _ _).trans (max_le h₁ (h₂.trans_eq (by omega)))
    change b.totalDegree ≤ _ at ih
    calc
      _ ≤ b.totalDegree + 2 * (f.totalDegree - 1) := by
        apply hstep.trans
        omega
      _ ≤ _ := by
        rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, Nat.add_mul]
        omega
end
end K1_13_5_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace K1_13_7_5_3_3_3
noncomputable section
open K1_13_5_4_2_4 MvPolynomial
abbrev Ground := K1_13_5_4.GeometricX
abbrev Coeff (A : Fin 4 → Finset Exponent) := Σ i : Fin 4, ↥(A i)
abbrev Universal (A : Fin 4 → Finset Exponent) := MvPolynomial (Fin 4) (CoefficientRing A)
def universalEquation (A : Fin 4 → Finset Exponent) (i : Fin 4) : Universal A :=
  ∑ a : ↥(A i), monomial a.1 (MvPolynomial.X ⟨i, a⟩)
def cutPrefix {R : Type*} [CommRing R] (f : Fin 4 → R) (k : ℕ) : Ideal R :=
  Ideal.span (f '' {i : Fin 4 | (i : ℕ) < k})
private def IsPivot {A : Fin 4 → Finset Exponent} (k : ℕ) (v : Coeff A) : Prop :=
  v.1.val < k ∧ v.2.val = 0
private abbrev Pivot (A : Fin 4 → Finset Exponent) (k : ℕ) := {v : Coeff A // IsPivot k v}
private abbrev Other (A : Fin 4 → Finset Exponent) (k : ℕ) := {v : Coeff A // ¬IsPivot k v}
private abbrev Rest (A : Fin 4 → Finset Exponent) (k : ℕ) :=
  MvPolynomial (Fin 4 ⊕ Other A k) Ground
private def regroupIndex (A : Fin 4 → Finset Exponent) (k : ℕ) :
    Fin 4 ⊕ Coeff A ≃ Pivot A k ⊕ (Fin 4 ⊕ Other A k) := by
  classical
  exact (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl (IsPivot k)).symm).trans
    ((Equiv.sumAssoc _ _ _).symm.trans
      ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _)))
private theorem regroupIndex_space (A : Fin 4 → Finset Exponent) (k : ℕ) (j : Fin 4) :
    regroupIndex A k (.inl j) = .inr (.inl j) := by
  simp [regroupIndex]
private theorem regroupIndex_pivot {A : Fin 4 → Finset Exponent} {k : ℕ} {v : Coeff A}
    (hv : IsPivot k v) : regroupIndex A k (.inr v) = .inl ⟨v, hv⟩ := by
  classical
  simp [regroupIndex, Equiv.sumCompl_symm_apply_of_pos hv]
private theorem regroupIndex_other {A : Fin 4 → Finset Exponent} {k : ℕ} {v : Coeff A}
    (hv : ¬IsPivot k v) : regroupIndex A k (.inr v) = .inr (.inr ⟨v, hv⟩) := by
  classical
  simp [regroupIndex, Equiv.sumCompl_symm_apply_of_neg hv]
private def regroup (A : Fin 4 → Finset Exponent) (k : ℕ) :
    Universal A ≃ₐ[Ground] MvPolynomial (Pivot A k) (Rest A k) :=
  (sumAlgEquiv Ground (Fin 4) (Coeff A)).symm.trans
    ((renameEquiv Ground (regroupIndex A k)).trans (sumAlgEquiv Ground _ _))
private theorem regroup_space (A : Fin 4 → Finset Exponent) (k : ℕ) (j : Fin 4) :
    regroup A k (MvPolynomial.X j) = C (MvPolynomial.X (.inl j)) := by
  simp [regroup, renameEquiv_apply, regroupIndex_space]
private theorem regroup_pivot {A : Fin 4 → Finset Exponent} {k : ℕ} {v : Coeff A}
    (hv : IsPivot k v) : regroup A k (C (MvPolynomial.X v)) = MvPolynomial.X ⟨v, hv⟩ := by
  simp [regroup, renameEquiv_apply, regroupIndex_pivot hv]
private theorem regroup_other {A : Fin 4 → Finset Exponent} {k : ℕ} {v : Coeff A}
    (hv : ¬IsPivot k v) : regroup A k (C (MvPolynomial.X v)) = C (MvPolynomial.X (.inr ⟨v, hv⟩)) := by
  simp [regroup, renameEquiv_apply, regroupIndex_other hv]
private def pivotIndex {A : Fin 4 → Finset Exponent} {k : ℕ}
    (hz : ∀ i, 0 ∈ A i) (i : Fin 4) (hi : i.val < k) : Pivot A k :=
  ⟨⟨i, ⟨0, hz i⟩⟩, hi, rfl⟩
private theorem pivotIndex_surjective {A : Fin 4 → Finset Exponent} {k : ℕ}
    (hz : ∀ i, 0 ∈ A i) :
    Function.Surjective (fun i : {i : Fin 4 // i.val < k} => pivotIndex hz i.val i.property) := by
  rintro ⟨⟨i, ⟨a, ha⟩⟩, hi, hzero⟩
  change a = 0 at hzero
  subst a
  exact ⟨⟨i, hi⟩, rfl⟩
private def remainingVariable {A : Fin 4 → Finset Exponent} (k : ℕ) (v : Coeff A) : Rest A k := by
  classical
  exact if h : IsPivot k v then 0 else MvPolynomial.X (.inr ⟨v, h⟩)
private def tail {A : Fin 4 → Finset Exponent} (k : ℕ)
    (hz : ∀ i, 0 ∈ A i) (i : Fin 4) : Rest A k :=
  ∑ a ∈ Finset.univ.erase (⟨0, hz i⟩ : ↥(A i)),
    remainingVariable k ⟨i, a⟩ * a.val.prod (fun j e => (MvPolynomial.X (.inl j) : Rest A k) ^ e)
private theorem regroup_equation {A : Fin 4 → Finset Exponent} {k : ℕ}
    (hz : ∀ i, 0 ∈ A i) (i : Fin 4) (hi : i.val < k) :
    regroup A k (universalEquation A i) = MvPolynomial.X (pivotIndex hz i hi) + C (tail k hz i) := by
  classical
  unfold universalEquation tail
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨0, hz i⟩ : ↥(A i))), map_add,
    monomial_zero', regroup_pivot (show IsPivot k (⟨i, ⟨0, hz i⟩⟩ : Coeff A) from ⟨hi, rfl⟩),
    add_comm, map_sum, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hn : ¬IsPivot k (⟨i, a⟩ : Coeff A) := by
    intro h
    exact (Finset.ne_of_mem_erase ha) (Subtype.ext h.2)
  simp only [monomial_eq, map_mul, regroup_other hn, remainingVariable, dite_eq_right hn]
  congr 1
  rw [Finsupp.prod, map_prod, Finsupp.prod, map_prod]
  simp [regroup_space]
private theorem evalSub_ker {B ι : Type*} [CommRing B] (s : ι → B) :
    RingHom.ker (aeval s : MvPolynomial ι B →ₐ[B] B).toRingHom =
      Ideal.span (Set.range fun i => MvPolynomial.X i - C (s i)) := by
  let I : Ideal (MvPolynomial ι B) := Ideal.span (Set.range fun i => MvPolynomial.X i - C (s i))
  change RingHom.ker (aeval s : MvPolynomial ι B →ₐ[B] B).toRingHom = I
  apply le_antisymm
  · intro f hf
    have h (p : MvPolynomial ι B) : p - C (aeval s p) ∈ I := by
      induction p using MvPolynomial.induction_on with
      | C b => simp
      | add p q hp hq =>
        simpa only [map_add, add_sub_add_comm] using I.add_mem hp hq
      | mul_X p i hp =>
        simp only [map_mul, aeval_X]
        have hi : MvPolynomial.X i - C (s i) ∈ I := Ideal.subset_span ⟨i, rfl⟩
        have he : p * MvPolynomial.X i - C (aeval s p * s i) =
            (p - C (aeval s p)) * MvPolynomial.X i + C (aeval s p) * (MvPolynomial.X i - C (s i)) := by
          rw [map_mul]
          ring
        rw [← map_mul, he]
        exact I.add_mem (I.mul_mem_right (MvPolynomial.X i) hp) (I.mul_mem_left _ hi)
    have hf' : aeval s f = 0 := hf
    simpa only [hf', map_zero, sub_zero] using h f
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
private def incidenceEquiv {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i) (k : ℕ) :
    (Universal A ⧸ cutPrefix (universalEquation A) k) ≃ₐ[Ground] Rest A k := by
  let e := regroup A k
  let s : Pivot A k → Rest A k := fun v => -tail k hz v.val.1
  have hker := evalSub_ker s
  have hmap : Ideal.map e.toRingHom (cutPrefix (universalEquation A) k) =
      RingHom.ker (aeval s : MvPolynomial (Pivot A k) (Rest A k) →ₐ[Rest A k] Rest A k).toRingHom := by
    rw [hker, cutPrefix, Ideal.map_span, Set.image_image]
    apply congrArg Ideal.span
    ext f
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨pivotIndex hz i hi, ?_⟩
      change MvPolynomial.X (pivotIndex hz i hi) - C (s (pivotIndex hz i hi)) =
        regroup A k (universalEquation A i)
      simpa only [s, pivotIndex, map_neg, sub_neg_eq_add] using (regroup_equation hz i hi).symm
    · rintro ⟨v, rfl⟩
      obtain ⟨⟨i, hi⟩, rfl⟩ := pivotIndex_surjective hz v
      refine ⟨i, hi, ?_⟩
      change regroup A k (universalEquation A i) =
        MvPolynomial.X (pivotIndex hz i hi) - C (s (pivotIndex hz i hi))
      simpa only [s, pivotIndex, map_neg, sub_neg_eq_add] using regroup_equation hz i hi
  let f : MvPolynomial (Pivot A k) (Rest A k) →ₐ[Ground] Rest A k :=
    (aeval s : MvPolynomial (Pivot A k) (Rest A k) →ₐ[Rest A k] Rest A k).restrictScalars Ground
  have hsurj : Function.Surjective f := fun b => ⟨C b, aeval_C s b⟩
  let q := Ideal.quotientEquivAlg (cutPrefix (universalEquation A) k) (RingHom.ker f.toRingHom) e hmap.symm
  exact q.trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
private theorem universalPrefix_prime {A : Fin 4 → Finset Exponent}
    (hz : ∀ i, 0 ∈ A i) (k : ℕ) : (cutPrefix (universalEquation A) k).IsPrime := by
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  let e := (incidenceEquiv hz k).toRingEquiv
  exact e.toMulEquiv.isDomain
private theorem universalEquation_not_mem {A : Fin 4 → Finset Exponent}
    (hz : ∀ i, 0 ∈ A i) (i : Fin 4) :
    universalEquation A i ∉ cutPrefix (universalEquation A) i.val := by
  classical
  let v : Coeff A → Ground := fun j => if j.1 = i then 1 else 0
  let ev := (eval v).comp (constantCoeff : Universal A →+* CoefficientRing A)
  have h (j : Fin 4) : ev (universalEquation A j) = v ⟨j, ⟨0, hz j⟩⟩ := by
    unfold universalEquation
    rw [map_sum, Finset.sum_eq_single (⟨0, hz j⟩ : ↥(A j))]
    · simp [ev, monomial_zero']
    · intro a _ ha
      have ha' : a.val ≠ 0 := fun ha' => ha (Subtype.ext ha')
      simp [ev, constantCoeff_monomial, ha']
    · simp
  have hle : cutPrefix (universalEquation A) i.val ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change j.val < i.val at hj
    have hji : j ≠ i := fun he => (ne_of_lt hj) (congrArg Fin.val he)
    change ev (universalEquation A j) = 0
    rw [h]
    simp [v, hji]
  intro hi
  have h0 : ev (universalEquation A i) = 0 := hle hi
  simp [h, v] at h0
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Affine (A : Fin 4 → Finset Exponent) := MvPolynomial (Fin 4) (CoefficientField A)
private abbrev Denoms (A : Fin 4 → Finset Exponent) :=
  (nonZeroDivisors (CoefficientRing A)).map (C (σ := Fin 4))
private theorem map_universalEquation (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    algebraMap (Universal A) (Affine A) (universalEquation A i) = genericEquation A i := by
  rw [MvPolynomial.algebraMap_def, universalEquation, genericEquation, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact MvPolynomial.map_monomial _ _ _
private theorem map_cutPrefix (A : Fin 4 → Finset Exponent) (k : ℕ) :
    Ideal.map (algebraMap (Universal A) (Affine A)) (cutPrefix (universalEquation A) k) =
      cutPrefix (genericEquation A) k := by
  simp only [cutPrefix, Ideal.map_span, Set.image_image, map_universalEquation]
theorem generic_prefix_regular {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i)
    (i : Fin 4) (p : Affine A) :
    genericEquation A i * p ∈ cutPrefix (genericEquation A) i.val →
      p ∈ cutPrefix (genericEquation A) i.val := by
  intro hp
  let J := cutPrefix (universalEquation A) i.val
  obtain ⟨q, s, rfl⟩ := IsLocalization.exists_mk'_eq (Denoms A) p
  rw [← map_cutPrefix] at hp ⊢
  change _ ∈ Ideal.map _ J at hp ⊢
  have hq : algebraMap (Universal A) (Affine A) (universalEquation A i * q) ∈
      Ideal.map (algebraMap (Universal A) (Affine A)) J := by
    rw [map_mul, map_universalEquation, ← IsLocalization.mk'_spec (Affine A) q s, ← mul_assoc]
    exact Ideal.mul_mem_right _ _ hp
  obtain ⟨d, hd, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Denoms A) _ J _).mp hq
  rw [mul_left_comm] at hmem
  have hprime := universalPrefix_prime hz i.val
  exact (IsLocalization.mk'_mem_map_algebraMap_iff (Denoms A) _ J q s).mpr
    ⟨d, hd, (hprime.mem_or_mem hmem).resolve_left (universalEquation_not_mem hz i)⟩
private theorem cutPrefix_four {R : Type*} [CommRing R] (f : Fin 4 → R) :
    cutPrefix f 4 = Ideal.span (Set.range f) := by
  rw [cutPrefix, show {i : Fin 4 | i.val < 4} = Set.univ from Set.eq_univ_of_forall Fin.isLt,
    Set.image_univ]
private def pivotEquiv {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i) :
    Fin 4 ≃ Pivot A 4 :=
  Equiv.ofBijective (fun i => pivotIndex hz i i.isLt) ⟨fun _ _ h => congrArg (fun x => x.val.1) h,
    fun v => by
      obtain ⟨⟨i, _⟩, rfl⟩ := pivotIndex_surjective hz v
      exact ⟨i, rfl⟩⟩
private theorem incidence_trdeg {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i) :
    Algebra.trdeg Ground (Universal A ⧸ cutPrefix (universalEquation A) 4) = Cardinal.mk (Coeff A) := by
  classical
  rw [(incidenceEquiv hz 4).trdeg_eq, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id]
  exact Cardinal.mk_congr ((Equiv.sumCongr (pivotEquiv hz) (Equiv.refl _)).trans
    (Equiv.sumCompl (IsPivot 4)))
private theorem fraction_trdeg (A : Fin 4 → Finset Exponent) :
    Algebra.trdeg Ground (CoefficientField A) = Cardinal.mk (Coeff A) := by
  let : Algebra.IsAlgebraic (CoefficientRing A) (CoefficientField A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (CoefficientRing A))
  rw [← trdeg_add_eq Ground (CoefficientRing A), trdeg_eq_zero (R := CoefficientRing A), add_zero,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id]
private theorem trdeg_localized_quotient {F U S : Type} [Field F] [CommRing U] [CommRing S]
    [Algebra F U] [Algebra U S] [Algebra F S] [IsScalarTower F U S]
    (M : Submonoid U) [IsLocalization M S] (J : Ideal U) (hprime : J.IsPrime)
    (hdis : Disjoint (M : Set U) (J : Set U)) :
    Algebra.trdeg F (S ⧸ Ideal.map (algebraMap U S) J) = Algebra.trdeg F (U ⧸ J) := by
  let B := U ⧸ J
  let I := Ideal.map (algebraMap U S) J
  let G := S ⧸ I
  let : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S J hprime hdis
  let : J.IsPrime := hprime
  let f : B →+* G := Ideal.quotientMap I (algebraMap U S) Ideal.le_comap_map
  have hf (u : U) : f (Ideal.Quotient.mk J u) = Ideal.Quotient.mk I (algebraMap U S u) := rfl
  have hfinj : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hf, hf, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, ← Ideal.mem_comap] at hab
    change a - b ∈ I.under U at hab
    rw [show I.under U = J from IsLocalization.under_map_of_isPrime_disjoint M S hprime hdis] at hab
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr hab
  let : Algebra B G := RingHom.toAlgebra (R := B) (S := G) f
  let : IsScalarTower F B G := IsScalarTower.of_algebraMap_eq fun a => by
    change Ideal.Quotient.mk I (algebraMap F S a) = f (Ideal.Quotient.mk J (algebraMap F U a))
    rw [hf, IsScalarTower.algebraMap_apply F U S]
  let : FaithfulSMul B G := (faithfulSMul_iff_algebraMap_injective B G).mpr hfinj
  let : Algebra.IsAlgebraic B G := ⟨fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨⟨q, s⟩, hs⟩ := IsLocalization.surj M p
    let a := Ideal.Quotient.mk J q
    let b := Ideal.Quotient.mk J s.val
    have hb : b ≠ 0 := fun hb => Set.disjoint_left.mp hdis s.property
      (Ideal.Quotient.eq_zero_iff_mem.mp hb)
    have hq : Ideal.Quotient.mk I p * f b = f a := by
      simp only [a, b, hf, ← map_mul, hs]
    refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, ?_, ?_⟩
    · intro h0
      have h := congrArg (fun P : Polynomial B => P.coeff 1) h0
      have hb1 : (Polynomial.C b * (Polynomial.X : Polynomial B)).coeff 1 = b := by
        rw [Polynomial.coeff_C_mul_X, ite_eq_left rfl]
      have ha1 : (Polynomial.C a).coeff 1 = 0 := by
        rw [Polynomial.coeff_C, ite_eq_right Nat.one_ne_zero]
      change (Polynomial.C b * Polynomial.X - Polynomial.C a).coeff 1 = (0 : Polynomial B).coeff 1 at h
      rw [Polynomial.coeff_sub, hb1, ha1, sub_zero, Polynomial.coeff_zero] at h
      exact hb h
    · let ev : Polynomial B →ₐ[B] G := Polynomial.aeval (Ideal.Quotient.mk I p)
      change ev (Polynomial.C b * Polynomial.X - Polynomial.C a) = 0
      have hC (c : B) : ev (Polynomial.C c) = f c := ev.commutes c
      have hX : ev Polynomial.X = Ideal.Quotient.mk I p := Polynomial.aeval_X _
      rw [map_sub, map_mul, hC, hC, hX, mul_comm, hq, sub_self]⟩
  change Algebra.trdeg F G = Algebra.trdeg F B
  rw [← trdeg_add_eq F B, trdeg_eq_zero (R := B), add_zero]
theorem generic_finite {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i) :
    Module.Finite (CoefficientField A) (GenericQuotient A) := by
  classical
  let J := cutPrefix (universalEquation A) 4
  let S := Affine A
  let U := Universal A
  let M := Denoms A
  let I := Ideal.span (Set.range (genericEquation A))
  let G := S ⧸ I
  have hI : Ideal.map (algebraMap U S) J = I := (map_cutPrefix A 4).trans (cutPrefix_four _)
  by_cases htop : I = ⊤
  · let : Subsingleton G := Ideal.Quotient.subsingleton_iff.mpr htop
    exact Module.Finite.of_finite (R := CoefficientField A) (M := G)
  have hprime : J.IsPrime := universalPrefix_prime hz 4
  have hdis : Disjoint (M : Set U) (J : Set U) := by
    apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint M S J).mp
    rwa [hI]
  let : I.IsPrime := hI ▸ IsLocalization.isPrime_of_isPrime_disjoint M S J hprime hdis
  let : IsScalarTower Ground U S := IsScalarTower.of_algebraMap_eq fun a => by
    change C (algebraMap Ground (CoefficientField A) a) = algebraMap U S (C (C a))
    rw [MvPolynomial.algebraMap_def, map_C]
    rfl
  have htrG : Algebra.trdeg Ground G = Cardinal.mk (Coeff A) := by
    have h := trdeg_localized_quotient (F := Ground) (S := S) M J hprime hdis
    rw [hI] at h
    exact h.trans (incidence_trdeg hz)
  have htr := trdeg_add_eq Ground (CoefficientField A) (A := G)
  rw [fraction_trdeg, htrG, Cardinal.add_eq_left_iff] at htr
  have hztr : Algebra.trdeg (CoefficientField A) G = 0 := by
    refine htr.resolve_left ?_
    intro h
    exact (Cardinal.mk_lt_aleph0 (α := Coeff A)).not_ge ((le_max_left _ _).trans h)
  let : Algebra.IsIntegral (CoefficientField A) G := ⟨fun x => isAlgebraic_iff_isIntegral.mp
    ((trdeg_eq_zero_iff.mp hztr).isAlgebraic x)⟩
  exact Algebra.IsIntegral.finite (R := CoefficientField A) (A := G)
end
end K1_13_7_5_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2_2
noncomputable section
open Algebra KaehlerDifferential MvPolynomial
open scoped BigOperators IntermediateField.algebraAdjoinAdjoin
private theorem trdeg_fractionRing_of_finite {k P A : Type} [Field k]
    [CommRing P] [IsDomain P] [CommRing A] [IsDomain A]
    [Algebra k P] [Algebra k A] {ι : Type} {v : ι → P}
    (hv : IsTranscendenceBasis k v) (g : P →ₐ[k] A)
    (hg : Function.Injective g) (hgfin : g.Finite) :
    trdeg k (FractionRing A) = Cardinal.mk ι := by
  let K := FractionRing A
  let _ : Algebra P A := g.toRingHom.toAlgebra
  have : IsScalarTower k P A := .of_algebraMap_eq fun a => (g.commutes a).symm
  have : IsScalarTower k P K := IsScalarTower.to₁₂₄ k P A K
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  have : Module.Finite P A := hgfin
  have : Algebra.IsAlgebraic P K := (IsFractionRing.isAlgebraic_iff' P A K).mp inferInstance
  exact (hv.algebraMap_comp (A := K)).cardinalMk_eq_trdeg.symm
private theorem curve_trdeg {k σ : Type} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (hd : (affineHilbertPolynomial I).natDegree = 1) :
    trdeg k (FractionRing (MvPolynomial σ k ⧸ I)) = 1 := by
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hd' : d = 1 := by
    simpa using (natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective
      g hgfin hg).symm.trans hd
  simpa [hd'] using trdeg_fractionRing_of_finite
    (IsTranscendenceBasis.mvPolynomial (Fin d) k) g hg hgfin
private theorem differential_finrank {k K : Type} [Field k] [Field K] [Algebra k K]
    [PerfectField k] [EssFiniteType k K] (ht : trdeg k K = 1) :
    Module.finrank K Ω[K⁄k] = 1 := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hcard : Fintype.card s = 1 := by
    have h := hs.cardinalMk_eq_trdeg.trans ht
    rw [Cardinal.mk_fintype] at h
    exact_mod_cast h
  let v : s → K := (↑)
  have hv : Set.range v = (s : Set K) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [← hv] at hsep
  let P := MvPolynomial s k
  let A := Algebra.adjoin k (Set.range v)
  let E := IntermediateField.adjoin k (Set.range v)
  let e : P ≃ₐ[k] A := hs.1.aevalEquiv
  let _ : Algebra P E := ((algebraMap A E).comp e.toRingHom).toAlgebra
  let _ : Algebra P K := ((algebraMap E K).comp (algebraMap P E)).toAlgebra
  have : IsScalarTower P E K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k P K := .of_algebraMap_eq fun a => by
    change algebraMap k K a = algebraMap E K (algebraMap A E (e (algebraMap k P a)))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply k A E,
      ← IsScalarTower.algebraMap_apply k E K]
  have : IsFractionRing P E := IsFractionRing.of_ringEquiv_left e.toRingEquiv fun _ => rfl
  have : Algebra.FormallyEtale P E := Algebra.FormallyEtale.of_isLocalization
    (nonZeroDivisors P)
  have : Algebra.IsSeparable E K := hsep
  have : Algebra.FormallyEtale E K := Algebra.FormallyEtale.of_isSeparable E K
  have : Algebra.FormallyEtale P K := Algebra.FormallyEtale.comp P E K
  let b := ((mvPolynomialBasis k s).baseChange K).map
    (tensorKaehlerEquivOfFormallyEtale k P K)
  exact (Module.finrank_eq_card_basis b).trans hcard
private theorem separates_over_intermediate {k E K : Type} [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K] [EssFiniteType E K]
    (z : E) (hd : Module.finrank K Ω[K⁄k] = 1)
    (hu : D k K (algebraMap E K z) ≠ 0) : Algebra.IsSeparable E K := by
  apply (Algebra.FormallyUnramified.iff_isSeparable (K := E) K).mp
  constructor
  let m := KaehlerDifferential.map k E K K
  have hm : m (D k K (algebraMap E K z)) = 0 := by
    simpa only [m, map_D, Algebra.algebraMap_self_apply] using (D E K).map_algebraMap z
  apply (subsingleton_iff_forall_eq 0).mpr
  intro y
  obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective k E K y
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_finrank_eq_one hd hu x
  change m (t • D k K (algebraMap E K z)) = 0
  rw [map_smul, hm, smul_zero]
private theorem separates_of_nonzero_differential {k K : Type} [Field k] [Field K]
    [IsAlgClosed k] [Algebra k K] [EssFiniteType k K] (u : K)
    (hd : Module.finrank K Ω[K⁄k] = 1) (hu : D k K u ≠ 0) :
    Transcendental k u ∧ Algebra.IsSeparable (IntermediateField.adjoin k {u}) K := by
  let E := IntermediateField.adjoin k ({u} : Set K)
  have humem : u ∈ E := IntermediateField.mem_adjoin_simple_self k u
  have htrans : Transcendental k u := by
    intro ha
    have : Algebra.IsAlgebraic k E :=
      IntermediateField.isAlgebraic_adjoin_simple (isAlgebraic_iff_isIntegral.mp ha)
    have hbot : E = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic E
    rw [hbot] at humem
    obtain ⟨t, ht⟩ := (IntermediateField.mem_bot.mp humem)
    exact hu (ht ▸ (D k K).map_algebraMap t)
  refine ⟨htrans, ?_⟩
  have : EssFiniteType E K := EssFiniteType.of_comp k E K
  exact separates_over_intermediate (⟨u, humem⟩ : E) hd hu
set_option maxHeartbeats 600000 in
theorem proof : K1_13_5_4_2_2.c2 := by
  classical
  intro k σ _ _ _ I hI hd
  have : I.IsPrime := hI
  let A := MvPolynomial σ k ⧸ I
  let K := FractionRing A
  let f : MvPolynomial σ k →ₐ[k] K :=
    (IsScalarTower.toAlgHom k A K).comp (Ideal.Quotient.mkₐ k I)
  have : EssFiniteType A K := EssFiniteType.of_isLocalization K (nonZeroDivisors A)
  have : EssFiniteType k K := EssFiniteType.comp k A K
  have hr : Module.finrank K Ω[K⁄k] = 1 := differential_finrank (curve_trdeg I hd)
  let _ : Fintype σ := Fintype.ofFinite σ
  let L : (σ → k) →ₗ[k] Ω[K⁄k] := {
    toFun := fun a => ∑ i, a i • D k K (f (MvPolynomial.X i))
    map_add' := by
      intro a b
      simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro t a
      simp [smul_smul, Finset.smul_sum] }
  refine ⟨L.ker, ?_, ?_⟩
  · intro htop
    have hX (i : σ) : D k K (f (MvPolynomial.X i)) = 0 := by
      have h : L (Pi.single i 1) = 0 := LinearMap.mem_ker.mp (htop.symm ▸ Submodule.mem_top)
      simpa [L, Pi.single_apply] using h
    have hp (p : MvPolynomial σ k) : D k K (f p) = 0 := by
      induction p using MvPolynomial.induction_on with
      | C t =>
        rw [← MvPolynomial.algebraMap_eq, f.commutes]
        exact (D k K).map_algebraMap t
      | add p q hp hq => simp only [map_add, hp, hq, add_zero]
      | mul_X p i hp => simp only [map_mul, Derivation.leibniz, hp, hX, smul_zero, add_zero]
    have hA (x : A) : D k K (algebraMap A K x) = 0 := by
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hp p
    have hK (x : K) : D k K x = 0 := by
      obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective A x
      simp [Derivation.leibniz_div, hA]
    have hle : (⊤ : Submodule K Ω[K⁄k]) ≤ ⊥ := by
      rw [← span_range_derivation k K, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      simpa using hK x
    have : Subsingleton Ω[K⁄k] := (subsingleton_iff_forall_eq 0).mpr fun x =>
      (Submodule.mem_bot K).mp (hle (Submodule.mem_top : x ∈ ⊤))
    exact Nat.zero_ne_one ((Module.finrank_zero_of_subsingleton (R := K) (M := Ω[K⁄k])).symm.trans hr)
  · intro a ha
    have hL : L a = D k K (f (K1_13_5_4_2_2.linearForm a)) := by
      change (∑ i, a i • D k K (f (MvPolynomial.X i))) =
        D k K (f (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i))
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← MvPolynomial.algebraMap_eq, ← Algebra.smul_def, map_smul, (D k K).map_smul]
    have hn : D k K (f (K1_13_5_4_2_2.linearForm a)) ≠ 0 := by
      rw [← hL]
      exact fun hz => ha (LinearMap.mem_ker.mpr hz)
    exact separates_of_nonzero_differential _ hr hn
end
end K1_13_5_4_2_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 K1_13_5_4_2_5 MeasureTheory Filter
open scoped BigOperators Pointwise Topology
theorem volume_zero_height {A : Set ExponentSpace} (hA : ∀ x ∈ A, x 3 = 0) :
    volume A = 0 := by
  let fibers (i : Fin 4) : Set ℝ := if i = 3 then {0} else Set.univ
  have hsub : A ⊆ Set.pi Set.univ fibers := by
    intro x hx
    refine Set.mem_pi.mpr (fun i _ => ?_)
    by_cases hi : i = 3
    · simpa [fibers, hi] using hA x hx
    · simp [fibers, hi]
  have hz : volume (Set.pi Set.univ fibers) = 0 := by
    rw [volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ (3 : Fin 4)) (by simp [fibers])
  exact le_antisymm ((measure_mono hsub).trans_eq hz) bot_le
end
end K1_13_5_4_2_5_2
end
section
namespace K1_14_2_5
noncomputable section
open K1_13 K1_13_5 MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
def firstView (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin 2) R ≃ₐ[R] (Polynomial (MvPolynomial (Fin 1) R)) :=
  (renameEquiv R finSuccEquivLast).trans (optionEquivLeft R (Fin 1))
private abbrev valueView : Row 1 ≃ₐ[(Polynomial Geom)] (Polynomial (Polynomial Geom)) :=
  uniqueAlgEquiv (Polynomial Geom) (Fin 1)
private theorem firstView_degree (f : Row 2) : (firstView (Polynomial Geom) f).natDegree = f.degreeOf 1 := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast f)).natDegree = f.degreeOf 1
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 1)
private theorem firstView_pderiv (f : Row 2) :
    firstView (Polynomial Geom) (pderiv 1 f) = (firstView (Polynomial Geom) f).derivative := by
  change optionEquivLeft _ _ (rename finSuccEquivLast (pderiv 1 f)) =
    (optionEquivLeft _ _ (rename finSuccEquivLast f)).derivative
  rw [← pderiv_rename finSuccEquivLast.injective,
    show finSuccEquivLast (1 : Fin 2) = none from finSuccEquivLast_last,
    optionEquivLeft_pderiv_none]
private theorem valueView_eval (g : Row 1) (S : (Polynomial Geom)) :
    (valueView g).eval S = MvPolynomial.eval (jet S) g := by
  have h := eval₂_uniqueAlgEquiv (f := g) (φ := RingHom.id (Polynomial Geom)) (a := jet S)
  have hzero : jet S (default : Fin 1) = S := by
    change Polynomial.hasseDeriv 0 S = S
    simp
  simpa only [Polynomial.eval₂_id, MvPolynomial.eval₂_id, hzero] using h
private theorem firstView_eval (f : Row 2) (S : (Polynomial Geom)) :
    ((firstView (Polynomial Geom) f).map (MvPolynomial.eval (jet S))).eval (jet S (1 : Fin 2)) =
      atJet f S := by
  rw [firstView, AlgEquiv.trans_apply, renameEquiv_apply, ← optionEquivLeft_elim_eval,
    eval_rename, atJet]
  apply congrArg (fun x : Fin 2 → (Polynomial Geom) => MvPolynomial.eval x f)
  funext i
  fin_cases i <;> rfl
private theorem valueView_degree_le (g : Row 1) : (valueView g).natDegree ≤ g.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [valueView, coeff_uniqueAlgEquiv]
  by_contra hn
  have h := le_totalDegree (mem_support_iff.mpr hn)
  change (Finsupp.single (default : Fin 1) k).degree ≤ g.totalDegree at h
  rw [Finsupp.degree_single] at h
  exact (not_le_of_gt hk) h
private theorem firstView_coeff_bound (f : Row 2) (k : ℕ) (hk : k ≤ f.totalDegree) :
    k + (valueView ((firstView (Polynomial Geom) f).coeff k)).natDegree ≤ f.totalDegree := by
  change k + (valueView ((optionEquivLeft _ _ (rename finSuccEquivLast f)).coeff k)).natDegree ≤ _
  have hdeg : (rename finSuccEquivLast f).totalDegree = f.totalDegree :=
    totalDegree_renameEquiv finSuccEquivLast f
  have hh := totalDegree_coeff_optionEquivLeft_add_le (Polynomial Geom) (Fin 1)
    (rename finSuccEquivLast f) k
    (by rw [hdeg]; exact hk)
  rw [hdeg] at hh
  exact (Nat.add_le_add_left (valueView_degree_le _) _).trans (by simpa [add_comm] using hh)
private def eliminant (f : Row 2) : (Polynomial (Polynomial Geom)) :=
  let A := firstView (Polynomial Geom) f
  if 0 < A.natDegree then
    valueView (A.resultant A.derivative A.natDegree (A.natDegree - 1))
  else valueView (A.coeff 0)
set_option maxHeartbeats 600000 in
private theorem eliminant_spec (f : Row 2) (hf : Irreducible f) {B : ℕ} (hB : 2 ≤ B)
    (hchar : B < K1.p) (hb : f.totalDegree ≤ B) :
    eliminant f ≠ 0 ∧ (eliminant f).natDegree ≤ f.totalDegree * (B - 1) ∧
      ∀ S : (Polynomial Geom), atJet f S = 0 → (eliminant f).eval S = 0 ∨
        (0 < f.degreeOf 1 ∧ RegularAt 1 f S) := by
  let A := firstView (Polynomial Geom) f
  let c := A.natDegree
  let b := f.totalDegree
  have hcb : c ≤ b := by
    change (firstView (Polynomial Geom) f).natDegree ≤ f.totalDegree
    exact (firstView_degree f).le.trans (f.degreeOf_le_totalDegree 1)
  have hAb : A ≠ 0 := (map_ne_zero_iff _ (firstView (Polynomial Geom)).injective).mpr hf.ne_zero
  by_cases hc : 0 < c
  · let R := A.resultant A.derivative c (c - 1)
    have hform : eliminant f = valueView R := ite_eq_left hc
    have hcast : (c : Row 1) ≠ 0 := by
      have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
      have : CharP (Polynomial Geom) K1.p :=
        charP_of_injective_ringHom (Polynomial.C_injective (R := Geom)) K1.p
      have : CharP (Row 1) K1.p :=
        charP_of_injective_ringHom (MvPolynomial.C_injective (σ := Fin 1) (R := (Polynomial Geom))) K1.p
      intro h
      have hp : K1.p ∣ c := (CharP.cast_eq_zero_iff (Row 1) K1.p c).mp h
      exact (not_le_of_gt (hcb.trans_lt (hb.trans_lt hchar)))
        (Nat.le_of_dvd hc hp)
    have hder : A.derivative ≠ 0 := by
      intro h
      have hz := congrArg (fun P : (Polynomial (Row 1)) => P.coeff (c - 1)) h
      rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hc, Polynomial.coeff_zero] at hz
      have hnat : (((c - 1 : ℕ) : Row 1) + 1) = (c : Row 1) := calc
        _ = ((c - 1 + 1 : ℕ) : Row 1) := by rw [Nat.cast_add, Nat.cast_one]
        _ = _ := congrArg (fun k : ℕ => (k : Row 1)) (Nat.sub_add_cancel hc)
      rw [hnat] at hz
      change A.leadingCoeff * (c : Row 1) = 0 at hz
      exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hAb) hcast) hz
    have hR : R ≠ 0 :=
      Polynomial.resultant_derivative_ne_zero_of_irreducible A (hf.map (firstView (Polynomial Geom))) hder
    have hdeg : (valueView R).natDegree + c ^ 2 ≤ (2 * c - 1) * b := by
      let B := A.map valueView.toRingHom
      have h := Polynomial.natDegree_resultant_derivative_padded_add_sq_le B c b (by
        intro k hk
        rw [Polynomial.coeff_map]
        exact firstView_coeff_bound f k (hk.trans hcb))
      dsimp only [B] at h
      rw [Polynomial.derivative_map, Polynomial.resultant_map_map] at h
      exact h
    have hbudget : (valueView R).natDegree ≤ b * (b - 1) := by
      have hbpos : 1 ≤ b := hc.trans_le hcb
      have hcpos : 1 ≤ 2 * c := by omega
      zify [hbpos, hcpos] at hdeg ⊢
      nlinarith [sq_nonneg ((b : ℤ) - (c : ℤ))]
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ valueView.injective).mpr hR, ?_, ?_⟩
    · rw [hform]
      exact hbudget.trans (Nat.mul_le_mul_left b (Nat.sub_le_sub_right hb 1))
    · intro S hS
      by_cases hS' : atJet (pderiv 1 f) S = 0
      · left
        rw [hform, valueView_eval]
        exact Polynomial.map_resultant_eq_zero_of_common_root (MvPolynomial.eval (jet S))
          A A.derivative le_rfl (Polynomial.natDegree_derivative_le A) (Or.inl hc.ne')
          (jet S (1 : Fin 2)) ((firstView_eval f S).trans hS) (by
            rw [show A.derivative = firstView (Polynomial Geom) (pderiv 1 f) from (firstView_pderiv f).symm]
            exact (firstView_eval _ S).trans hS')
      · exact Or.inr ⟨(firstView_degree f) ▸ hc, hS, hS'⟩
  · have hform : eliminant f = valueView (A.coeff 0) := ite_eq_right hc
    have hAc : A = Polynomial.C (A.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (Nat.eq_zero_of_not_pos hc).le
    have hA0 : A.coeff 0 ≠ 0 := fun h => hAb (by simpa [h] using hAc)
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ valueView.injective).mpr hA0, ?_, ?_⟩
    · rw [hform]
      have h := firstView_coeff_bound f 0 (Nat.zero_le _)
      exact (by simpa using h : (valueView (A.coeff 0)).natDegree ≤ b).trans
        (by simpa using Nat.mul_le_mul_left b (by omega : 1 ≤ B - 1))
    · intro S hS
      left
      have h := (firstView_eval f S).trans hS
      change (A.map _).eval _ = 0 at h
      conv at h => lhs; rw [hAc]
      rw [hform, valueView_eval]
      simpa only [Polynomial.map_C, Polynomial.eval_C] using h
theorem factor_cover (q : Row 2) {B J : ℕ} (hq : q ≠ 0) (hB : 2 ≤ B)
    (hchar : B < K1.p) (hb : q.totalDegree ≤ B) (hj : q.degreeOf 1 ≤ J) :
    ∃ (A : Finset (Row 2)) (u : (Polynomial (Polynomial Geom))),
      (∀ g ∈ A, Irreducible g ∧ 0 < g.degreeOf 1) ∧
      (∑ g ∈ A, g.totalDegree) ≤ B ∧ (∑ g ∈ A, g.degreeOf 1) ≤ J ∧
      u ≠ 0 ∧ u.natDegree ≤ B * (B - 1) ∧
      ∀ S : (Polynomial Geom), atJet q S = 0 → u.eval S = 0 ∨ ∃ g ∈ A, RegularAt 1 g S := by
  classical
  let _ : StrongNormalizationMonoid (Row 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M := normalizedFactors q
  let A := M.toFinset
  let T := A.filter fun g => 0 < g.degreeOf 1
  have hA : ∀ g ∈ A, Irreducible g := fun g hg =>
    irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
  have hdiv : (∏ g ∈ A, g) ∣ q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq).dvd
  have hcap : (∑ g ∈ A, g.totalDegree) ≤ B := by
    have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) A id hq hdiv
    simp only [id_eq, weightedTotalDegree_one] at h
    exact h.trans hb
  have hT : ∀ g ∈ T, Irreducible g ∧ 0 < g.degreeOf 1 := fun g hg =>
    ⟨hA g (Finset.mem_filter.mp hg).1, (Finset.mem_filter.mp hg).2⟩
  have hJ : (∑ g ∈ T, g.degreeOf 1) ≤ J := by
    obtain ⟨r, hr⟩ := (Finset.prod_dvd_prod_of_subset T A id
      (Finset.filter_subset _ _)).trans hdiv
    have hprod := Finset.prod_ne_zero_iff.mpr fun g hg => (hT g hg).1.ne_zero
    have hr0 : r ≠ 0 := fun hh => hq (by simp [hr, hh])
    simp only [id_eq] at hr
    have hb' := hj
    rw [hr, degreeOf_mul_eq hprod hr0, degreeOf_prod_eq T (fun g => g)
      (fun g hg => (hT g hg).1.ne_zero)] at hb'
    exact (Nat.le_add_right _ _).trans hb'
  have hspec (g : Row 2) (hg : g ∈ A) :=
    eliminant_spec g (hA g hg) hB hchar
      ((Finset.single_le_sum (fun x _ => Nat.zero_le x.totalDegree) hg).trans hcap)
  let u := ∏ g ∈ A, eliminant g
  refine ⟨T, u, hT, ?_, hJ, Finset.prod_ne_zero_iff.mpr (fun g hg => (hspec g hg).1), ?_, ?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun g _ _ => Nat.zero_le g.totalDegree)).trans hcap
  · calc
      u.natDegree ≤ ∑ g ∈ A, (eliminant g).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ g ∈ A, g.totalDegree * (B - 1) := Finset.sum_le_sum fun g hg => (hspec g hg).2.1
      _ ≤ B * (B - 1) := by rw [← Finset.sum_mul]; exact Nat.mul_le_mul_right _ hcap
  · intro S hS
    have hroot : MvPolynomial.eval (jet S) M.prod = 0 := by
      have hd := map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hq).symm.dvd
      change atJet q S ∣ _ at hd
      rwa [hS, zero_dvd_iff] at hd
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hroot
    obtain ⟨g, hgM, hgS⟩ := hroot
    have hgA : g ∈ A := Multiset.mem_toFinset.mpr hgM
    rcases (hspec g hgA).2.2 S hgS with hzero | ⟨hpos, hreg⟩
    · left
      change Polynomial.evalRingHom S u = 0
      rw [show u = ∏ g ∈ A, eliminant g from rfl, map_prod]
      exact Finset.prod_eq_zero_iff.mpr ⟨g, hgA, hzero⟩
    · exact Or.inr ⟨g, Finset.mem_filter.mpr ⟨hgA, hpos⟩, hreg⟩
end
end K1_14_2_5
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1
noncomputable section
open K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_4 MvPolynomial
def c1 : Prop :=
  ∀ (L : Type) [Field L] [Algebra GeometricX L]
    (I : Ideal (GeoRow 4)) (y : JetPoint), pointIdeal y ∈ I.minimalPrimes →
    rationalIdeal (extendPoint L y) ∈ (extendIdeal L I).minimalPrimes ∧
      Module.Finite L (PointAlgebra (extendIdeal L I) (extendPoint L y)) ∧
      Module.finrank L (PointAlgebra (extendIdeal L I) (extendPoint L y)) =
        (pointLength I y).toNat
def c2 : Prop :=
  ∀ (L : Type) [Field L] [Infinite L] (g : Fin 4 → Total L) (y : Fin 4 → L),
    rationalIdeal y ∈ (equationsIdeal fun i => reduce (g i)).minimalPrimes →
    IsSMulRegular (BranchAlgebra g y) (branchParameter g y)
private theorem branch_sum_bound {L : Type} [Field L] [Infinite L] (h : c2)
    (g : Fin 4 → Total L) {ι : Type} [Fintype ι] (y : ι → Fin 4 → L)
    (hy : Function.Injective y)
    (hmin : ∀ i, rationalIdeal (y i) ∈ (equationsIdeal fun j => reduce (g j)).minimalPrimes)
    (hlocal : ∀ i, Module.Finite L (PointAlgebra (equationsIdeal fun j => reduce (g j)) (y i)))
    [Module.Finite (ParameterField L) (GenericFiber g)] :
    (∑ i, Module.finrank L (PointAlgebra (equationsIdeal fun j => reduce (g j)) (y i))) ≤
      Module.finrank (ParameterField L) (GenericFiber g) := by
  let I := equationsIdeal (fun j => reduce (g j))
  let s := AlgHom.pi fun i => pointClass I (y i)
  have hs : Function.Surjective s := points_surjective I y hy hmin
  have hrel (p : Total L) (hp : genericClass g p = 0) : s (reduce p) = 0 := by
    funext i
    exact relation_vanishes g (y i) (h L g (y i) (hmin i)) p hp
  let pointModules : ∀ i : ι, Module L (PointAlgebra I (y i)) :=
    fun i => inferInstance
  let : Module L ((i : ι) → PointAlgebra I (y i)) := Pi.module ι _ L
  let : ∀ i : ι, Module.Free L (PointAlgebra I (y i)) := fun i => inferInstance
  let : ∀ i : ι, Module.Finite L (PointAlgebra I (y i)) := hlocal
  let s' : Affine L →ₗ[L] ((i : ι) → PointAlgebra I (y i)) := s.toLinearMap
  have hr : Module.finrank L ((i : ι) → PointAlgebra I (y i)) ≤
      Module.finrank (ParameterField L) (GenericFiber g) := by
    refine specialization_rank (L := L) (D := (i : ι) → PointAlgebra I (y i)) g s' ?_ ?_
    · exact hs
    · exact hrel
  rw [Module.finrank_pi_fintype] at hr
  exact hr
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2_4.c1 := by
  classical
  intro A _ hfinite f hsupport points hpoints
  let L := CoefficientField A
  have : Infinite L := Infinite.of_injective (algebraMap GeometricX L) (RingHom.injective _)
  let g := deformation A f
  let I := equationsIdeal (fun i => reduce (g i))
  let y : ↥points → Fin 4 → L := fun i => extendPoint L i.1
  have hI : I = extendIdeal L (cutIdeal f) := deformation_reduce A f hsupport
  have hlocal (i : ↥points) :
      rationalIdeal (y i) ∈ I.minimalPrimes ∧
        Module.Finite L (PointAlgebra I (y i)) ∧
        Module.finrank L (PointAlgebra I (y i)) =
          (pointLength (cutIdeal f) i.1).toNat := by
    rw [hI]
    exact h1 L (cutIdeal f) i.1 (hpoints i.1 i.2)
  have hy : Function.Injective y := by
    intro i j hij
    apply Subtype.ext
    funext a
    exact (RingHom.injective (algebraMap GeometricX L)) (congrFun hij a)
  obtain ⟨hfin, hrank⟩ := deformation_generic A f hfinite
  have := hfin
  have h := branch_sum_bound h2 g y hy (fun i => (hlocal i).1) (fun i => (hlocal i).2.1)
  rw [hrank] at h
  calc
    (∑ z ∈ points, (pointLength (cutIdeal f) z).toNat) =
        ∑ i : ↥points, Module.finrank L (PointAlgebra I (y i)) := by
      rw [← Finset.sum_attach points (fun z => (pointLength (cutIdeal f) z).toNat)]
      exact Finset.sum_congr rfl fun i _ => (hlocal i).2.2.symm
    _ ≤ _ := h
end
end K1_13_5_4_2_4_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_3_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial
def contracted (P : Ideal (GeoRow 3)) : Ideal (Row 3) :=
  P.comap (MvPolynomial.map genericCoeff)
abbrev LocalRows (f : Row 3) := Localization.Away (separant f)
def localRowsMap (f : Row 3) : Row 3 →+* LocalRows f := algebraMap _ _
def localContraction (f : Row 3) (P : Ideal (GeoRow 3)) : Ideal (LocalRows f) :=
  (contracted P).map (localRowsMap f)
def Chart (f : Row 3) (P : Ideal (GeoRow 3)) := LocalRows f ⧸ localContraction f P
instance chartCommRing (f : Row 3) (P : Ideal (GeoRow 3)) : CommRing (Chart f P) :=
  inferInstanceAs (CommRing (LocalRows f ⧸ localContraction f P))
def chartEval (f : Row 3) (P : Ideal (GeoRow 3)) : Row 3 →+* Chart f P :=
  show Row 3 →+* (LocalRows f ⧸ localContraction f P) from
    (Ideal.Quotient.mk (localContraction f P)).comp (localRowsMap f)
def invSep (f : Row 3) (P : Ideal (GeoRow 3)) : Chart f P :=
  Ideal.Quotient.mk (localContraction f P) (IsLocalization.Away.invSelf (separant f))
theorem sep_mul_inv (f : Row 3) (P : Ideal (GeoRow 3)) :
    chartEval f P (separant f) * invSep f P = 1 := by
  change Ideal.Quotient.mk (localContraction f P) (localRowsMap f (separant f)) *
    Ideal.Quotient.mk (localContraction f P) (IsLocalization.Away.invSelf (separant f)) = 1
  rw [← map_mul, show localRowsMap f (separant f) * IsLocalization.Away.invSelf (separant f) = 1
    from IsLocalization.Away.mul_invSelf (separant f), map_one]
theorem chart_zero (f : Row 3) (P : Ideal (GeoRow 3)) {b : Row 3}
    (hb : genericRow b ∈ P) : chartEval f P b = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hb)
private def liftRows {R : Type*} [CommRing R] {f : Row 3} (g : Row 3 →+* R)
    (hs : IsUnit (g (separant f))) : LocalRows f →+* R :=
  IsLocalization.Away.lift (separant f) hs
def chartLift {R : Type*} [CommRing R] {f : Row 3} {P : Ideal (GeoRow 3)}
    (g : Row 3 →+* R) (hg : ∀ b ∈ contracted P, g b = 0)
    (hs : IsUnit (g (separant f))) : Chart f P →+* R :=
  show (LocalRows f ⧸ localContraction f P) →+* R from
    Ideal.Quotient.lift (localContraction f P) (liftRows g hs) (by
      change (contracted P).map (localRowsMap f) ≤ RingHom.ker (liftRows g hs)
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      change liftRows g hs (localRowsMap f b) = 0
      exact (IsLocalization.Away.lift_eq (separant f) hs b).trans (hg b hb))
theorem chartLift_eval {R : Type*} [CommRing R] {f : Row 3} {P : Ideal (GeoRow 3)}
    (g : Row 3 →+* R) (hg : ∀ b ∈ contracted P, g b = 0)
    (hs : IsUnit (g (separant f))) (b : Row 3) :
    chartLift g hg hs (chartEval f P b) = g b :=
  IsLocalization.Away.lift_eq (separant f) hs b
def constants {A : Type*} [CommRing A] (e : Row 3 →+* A) : Geom →+* A :=
  e.comp (MvPolynomial.C.comp Polynomial.C)
def localJet (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ → Chart f P
  | 0 => chartEval f P (MvPolynomial.X 0)
  | 1 => chartEval f P (MvPolynomial.X 1)
  | 2 => chartEval f P (MvPolynomial.X 2)
  | k + 3 => 2 * chartEval f P (compatibilityNumerator f k) *
      constants (chartEval f P) (((k + 3).factorial : Geom)⁻¹) *
      invSep f P ^ (2 * k + 1)
def jetPolynomial {A : Type*} [Semiring A] (len : ℕ) (a : ℕ → A) : (Polynomial A) :=
  ∑ j : Fin len, Polynomial.monomial j.val (a j.val)
def centred (f : Row 3) (P : Ideal (GeoRow 3)) : (Polynomial (Chart f P)) :=
  jetPolynomial taylorLength (localJet f P)
def localTaylor (f : Row 3) (P : Ideal (GeoRow 3)) : (Polynomial (Chart f P)) :=
  Polynomial.taylor (-chartEval f P (MvPolynomial.C Polynomial.X)) (centred f P)
end
end K1_13_5_4_3_2
end
section
namespace K1_14_3_6
noncomputable section
open K1 K1_13 K1_14 K1_14_3 Polynomial
open K1_13_5_3
abbrev total := Bivariate.totalDegree (F := FX)
def atScalar (S : (Polynomial K)) : JetPlane →+* FX :=
  eval₂RingHom (evalRingHom (atX S)) (atX S.derivative)
def power (d : ℕ) : ℕ := 2 * d - 3
def totalCap (d b : ℕ) : ℕ := 1 + power d * (b - 1)
def topCap (d b j : ℕ) : ℕ := min (totalCap d b) (power d * (j - 1) + d)
structure AgreementChart (f : Row 2) (d b j : ℕ) where
  cut : K → K → MvPolynomial (Fin 2) CenterField
  total_bound : ∀ x y, (cut x y).totalDegree ≤ totalCap d b
  top_bound : ∀ x y, (cut x y).degreeOf 1 ≤ topCap d b j
  agrees : ∀ S : (Polynomial K), S.natDegree ≤ d → K1_13_5.RegularAt 1 f (extend S) → ∀ x y,
    MvPolynomial.aeval (marked (extend S)) (cut x y) = 0 ↔ S.eval x = y
end
end K1_14_3_6
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1_1
noncomputable section
open K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_4_1 MvPolynomial IsLocalRing
open scoped TensorProduct
private theorem rationalIdeal_span {k : Type} [Field k] (y : Fin 4 → k) :
    rationalIdeal y = Ideal.span (Set.range fun i => MvPolynomial.X i - C (y i)) := by
  let J : Ideal (Affine k) := Ideal.span (Set.range fun i => MvPolynomial.X i - C (y i))
  let q := Ideal.Quotient.mk J
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · have hcomp : q = q.comp (C.comp (eval y)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        have h : q (MvPolynomial.X i - C (y i)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
        simpa [q, map_sub, sub_eq_zero] using h
    intro p hp
    rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval] at hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [hcomp, RingHom.comp_apply, RingHom.comp_apply, hp, map_zero, map_zero]
  · rintro _ ⟨i, rfl⟩
    change MvPolynomial.X i - C (y i) ∈ vanishingIdeal k {y}
    rw [mem_vanishingIdeal_singleton_iff]
    simp
private theorem map_rationalIdeal {k L : Type} [Field k] [Field L] [Algebra k L]
    (y : Fin 4 → k) :
    (rationalIdeal y).map (MvPolynomial.map (algebraMap k L)) =
      rationalIdeal (algebraMap k L ∘ y) := by
  simp only [rationalIdeal_span, Ideal.map_span, ← Set.range_comp', Function.comp_apply,
    map_sub, map_X, map_C]
private theorem comap_rationalIdeal {k L : Type} [Field k] [Field L] [Algebra k L]
    (y : Fin 4 → k) :
    (rationalIdeal (algebraMap k L ∘ y)).comap (MvPolynomial.map (algebraMap k L)) =
      rationalIdeal y := by
  ext p
  rw [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, mem_vanishingIdeal_singleton_iff,
    aeval_eq_eval, aeval_eq_eval, ← MvPolynomial.map_eval, map_eq_zero_iff _ (RingHom.injective _)]
private theorem map_minimal {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {I p : Ideal R} {q : Ideal S}
    (hp : I.IsMinimalPrime p) (hq : q.IsPrime) (hm : p.map f = q) (hc : q.comap f = p) :
    (I.map f).IsMinimalPrime q := by
  refine ⟨⟨hq, hm ▸ Ideal.map_mono hp.le⟩, ?_⟩
  intro T hT hTq
  have := hT.1
  have hTp : T.comap f ≤ p := hc ▸ Ideal.comap_mono hTq
  have hpT : p ≤ T.comap f :=
    hp.2 ⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.mp hT.2⟩ hTp
  exact hm ▸ Ideal.map_le_iff_le_comap.mpr hpT
private theorem affine_flat {k L : Type} [Field k] [Field L] [Algebra k L] :
    let : Algebra (Affine k) (Affine L) := (MvPolynomial.map (algebraMap k L)).toAlgebra
    Module.Flat (Affine k) (Affine L) := by
  let : Algebra (Affine k) (Affine L) := (MvPolynomial.map (algebraMap k L)).toAlgebra
  let e := (Algebra.TensorProduct.comm k (Affine k) L).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) k L).toRingEquiv
  let e' : Affine k ⊗[k] L ≃ₐ[Affine k] Affine L :=
    { e with
      commutes' := fun p => by
        change MvPolynomial.algebraTensorAlgEquiv k L (1 ⊗ₜ[k] p) =
          MvPolynomial.map (algebraMap k L) p
        simp }
  exact Module.Flat.of_linearEquiv e'.symm.toLinearEquiv
private theorem residue_constants_surjective {L : Type} [Field L] (y : Fin 4 → L) :
    Function.Surjective (algebraMap L (ResidueField (PointLocal y))) := by
  let B := PointLocal y
  let p := rationalIdeal y
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal p B
  intro x
  change ∃ a : L, Ideal.Quotient.mk (maximalIdeal B) (algebraMap L B a) = x
  obtain ⟨z, rfl⟩ := e.surjective x
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  have he : Ideal.Quotient.mk p (C (eval y P)) = Ideal.Quotient.mk p P := by
    rw [Ideal.Quotient.eq, mem_vanishingIdeal_singleton_iff, aeval_eq_eval,
      map_sub, eval_C, sub_self]
  refine ⟨eval y P, ?_⟩
  rw [IsScalarTower.algebraMap_apply L (Affine L) B, MvPolynomial.algebraMap_eq]
  simpa only [e, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] using congrArg e he
private theorem length_over_constants {L : Type} [Field L]
    (I : Ideal (Affine L)) (y : Fin 4 → L) :
    Module.length L (PointAlgebra I y) = Module.length (PointLocal y) (PointAlgebra I y) := by
  let B := PointLocal y
  have : IsLocalHom (algebraMap L B) := ⟨fun a ha =>
    isUnit_iff_ne_zero.mpr (by intro h; subst a; simp at ha)⟩
  have hres : Function.Surjective (algebraMap (ResidueField L) (ResidueField B)) := by
    intro x
    obtain ⟨a, ha⟩ := residue_constants_surjective y x
    exact ⟨residue L a, ha⟩
  have hlen : Module.length (ResidueField L) (ResidueField B) = 1 := by
    rw [Module.length_eq_of_surjective hres, Module.length_eq_finrank]
    simp
  rw [IsLocalRing.length_restrictScalars L B (PointAlgebra I y), hlen, mul_one]
theorem proof : K1_13_5_4_2_4_1.c1 := by
  intro L _ _ I y hy
  let : Algebra (GeoRow 4) (Affine L) := (MvPolynomial.map (algebraMap GeometricX L)).toAlgebra
  let p := pointIdeal y
  let q := rationalIdeal (extendPoint L y)
  have hm : p.map (algebraMap (GeoRow 4) (Affine L)) = q := map_rationalIdeal y
  have hc : q.comap (algebraMap (GeoRow 4) (Affine L)) = p := comap_rationalIdeal y
  have hmin : q ∈ (extendIdeal L I).minimalPrimes :=
    map_minimal (algebraMap (GeoRow 4) (Affine L)) hy inferInstance hm hc
  have : q.LiesOver p := ⟨hc.symm⟩
  have : Module.Flat (GeoRow 4) (Affine L) := affine_flat
  let A := PointLocal y
  let B := PointLocal (extendPoint L y)
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver p q
  have : IsScalarTower (GeoRow 4) A B := inferInstance
  have : IsLocalHom (algebraMap A B) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  have hmap (J : Ideal (GeoRow 4)) :
      (J.map (algebraMap (GeoRow 4) A)).map (algebraMap A B) =
        (extendIdeal L J).map (algebraMap (Affine L) B) := by
    change _ = (J.map (algebraMap (GeoRow 4) (Affine L))).map (algebraMap (Affine L) B)
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), hmap]
    change (p.map (algebraMap (GeoRow 4) (Affine L))).map (algebraMap (Affine L) B) = _
    rw [hm, Localization.AtPrime.map_eq_maximalIdeal]
  let J := I.map (algebraMap (GeoRow 4) A)
  have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal B).1
  have hlen := IsLocalRing.length_baseChange A B (A ⧸ J)
  rw [hmax, Module.length_eq_one B (B ⧸ maximalIdeal B), mul_one] at hlen
  have hdim : Module.length L (PointAlgebra (extendIdeal L I) (extendPoint L y)) =
      pointLength I y := by
    rw [length_over_constants]
    change Module.length B (B ⧸ (extendIdeal L I).map (algebraMap (Affine L) B)) =
      Module.length A (A ⧸ J)
    rw [← hmap I]
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toLinearEquiv.length_eq.trans hlen
  have hfinite : pointLength I y < ⊤ := localLength_lt_top hy
  have : IsNoetherian L (PointAlgebra (extendIdeal L I) (extendPoint L y)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (Module.length_ne_top_iff.mp (hdim.trans_lt hfinite).ne)).1
  refine ⟨hmin, inferInstance, ?_⟩
  simpa only [Module.length_eq_finrank, ENat.toNat_natCast] using congrArg ENat.toNat hdim
end
end K1_13_5_4_2_4_1_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_5_4_3_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial
open scoped BigOperators
@[simp] private theorem coeff_coeffDerivative (b : Row 3) (m : Fin 3 →₀ ℕ) :
    (coeffDerivative b).coeff m = derivative (b.coeff m) := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coeffDerivative_C (g : (Polynomial Geom)) :
    coeffDerivative (MvPolynomial.C g : Row 3) = MvPolynomial.C (derivative g) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
@[simp] theorem coeffDerivative_X (i : Fin 3) :
    coeffDerivative (MvPolynomial.X i : Row 3) = 0 := by
  classical
  ext m
  simp only [coeff_coeffDerivative, MvPolynomial.coeff_X, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply]
  split_ifs <;> simp
private theorem tangent_C (f : Row 3) (g : (Polynomial Geom)) :
    tangentNumerator f (MvPolynomial.C g) = separant f * MvPolynomial.C g.derivative := by
  simp [tangentNumerator, lowerTangent, coeffDerivative_C]
variable {f : Row 3} {P : Ideal (GeoRow 3)}
private abbrev Dual (f : Row 3) (P : Ideal (GeoRow 3)) :=
  TrivSqZeroExt (Chart f P) (Chart f P)
private def rowJet (f : Row 3) (P : Ideal (GeoRow 3)) : Row 3 →+* Dual f P where
  toFun b := (chartEval f P b, invSep f P * chartEval f P (tangentNumerator f b))
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero _
    · rw [show (0 : Row 3) = MvPolynomial.C 0 by rw [map_zero], tangent_C]
      simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one _
    · rw [show (1 : Row 3) = MvPolynomial.C 1 by rw [map_one], tangent_C]
      simp
  map_add' b c := by
    apply TrivSqZeroExt.ext
    · exact map_add _ _ _
    · change _ * chartEval f P _ = _ * chartEval f P _ + _ * chartEval f P _
      rw [K1_13_5_4_3_1.tangentNumerator_add, map_add, mul_add]
  map_mul' b c := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change _ * chartEval f P _ =
        chartEval f P b * (_ * chartEval f P _) + (_ * chartEval f P _) * chartEval f P c
      rw [K1_13_5_4_3_1.tangentNumerator_mul, map_add, map_mul, map_mul]
      ring
private def chartJet (h : TangentStable f P) : Chart f P →+* Dual f P :=
  chartLift (rowJet f P) (fun b hb => by
    apply TrivSqZeroExt.ext
    · exact chart_zero f P hb
    · change invSep f P * chartEval f P (tangentNumerator f b) = 0
      rw [chart_zero f P (h b hb), mul_zero])
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.of_mul_eq_one _ (sep_mul_inv f P)))
private theorem chartJet_eval (h : TangentStable f P) (b : Row 3) :
    chartJet h (chartEval f P b) = rowJet f P b :=
  chartLift_eval _ _ _ b
private theorem chartJet_fst (h : TangentStable f P) (a : Chart f P) :
    (chartJet h a).fst = a := by
  let q := Ideal.Quotient.mk (localContraction f P)
  have he : (TrivSqZeroExt.fstHom (Chart f P) (Chart f P) (Chart f P)).toRingHom.comp
      ((chartJet h).comp q) = q := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (separant f))
    apply RingHom.ext
    intro b
    change (chartJet h (chartEval f P b)).fst = chartEval f P b
    rw [chartJet_eval]
    rfl
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact RingHom.congr_fun he b
def delta (h : TangentStable f P) : Chart f P →+ Chart f P :=
  (TrivSqZeroExt.sndHom (R := Chart f P) (M := Chart f P)).toAddMonoidHom.comp
    (chartJet h).toAddMonoidHom
theorem delta_mul (h : TangentStable f P) (a b : Chart f P) :
    delta h (a * b) = a * delta h b + delta h a * b := by
  change (chartJet h (a * b)).snd = _
  rw [map_mul]
  change (chartJet h a).fst * delta h b + delta h a * (chartJet h b).fst = _
  rw [chartJet_fst, chartJet_fst]
theorem delta_eval (h : TangentStable f P) (b : Row 3) :
    delta h (chartEval f P b) = invSep f P * chartEval f P (tangentNumerator f b) := by
  change (chartJet h (chartEval f P b)).snd = _
  rw [chartJet_eval]
  rfl
theorem delta_coeff (h : TangentStable f P) (b : (Polynomial Geom)) :
    delta h (chartEval f P (MvPolynomial.C b)) =
      chartEval f P (MvPolynomial.C b.derivative) := by
  rw [delta_eval, tangent_C, map_mul, ← mul_assoc, mul_comm (invSep f P),
    sep_mul_inv, one_mul]
end
end K1_13_5_4_3_2
end
section
namespace K1_6
noncomputable section
open Polynomial Matrix
def shifts {A : Type} [CommRing A] (P : Fin 2 → (Polynomial A)) (L s : ℕ) :
    Matrix (Fin 2 × Fin L) (Fin s) A :=
  fun i j => (P i.1 * Polynomial.X ^ j.val).coeff i.2.val
def pairCoordinates {F : Type} [Field F] (P : Fin 2 → (Polynomial (Polynomial F))) (h : ℕ) :
    Fin 2 × Fin (h + 1) → (Polynomial F) :=
  fun i => (P i.1).coeff i.2.val
def maximalMinors {A row : Type} [CommRing A] {s : ℕ}
    (W : Matrix row (Fin s) A) (rows : Fin s → row) : A :=
  (W.submatrix rows id).det
end
end K1_6
end

end Merged6967_Fast048

section Merged6967_Fast049
set_option Elab.async false































set_option Elab.async false

-- merged module FiltrationLift
section Merged_FiltrationLift
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_1
noncomputable section
open MvPolynomial
open scoped MonomialOrder BigOperators
variable {k σ : Type*} [Field k] [Finite σ]
theorem exists_degree_shift (I : Ideal (MvPolynomial σ k)) (g : MvPolynomial σ k) :
    ∃ C : ℕ, ∀ f ∈ I ⊔ Ideal.span {g}, ∃ q : MvPolynomial σ k,
      f - q * g ∈ I ∧ q.totalDegree ≤ f.totalDegree + C := by
  classical
  let := Fintype.ofFinite σ
  let : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  let : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  let J := I ⊔ Ideal.span {g}
  obtain ⟨E, hE⟩ := m.exists_finset_standardExponents_iff J
  have hex (e : E) : ∃ b ∈ J, b ≠ 0 ∧ m.degree b ≤ (e : σ →₀ ℕ) := by
    by_contra! h
    have hs : (e : σ →₀ ℕ) ∈ m.standardExponents J := fun b hb hn => h b hb hn
    exact (hE _).mp hs _ e.property le_rfl
  choose b hb hn he using hex
  let B : Set (MvPolynomial σ k) := Set.range b
  let : Fintype B := (Set.finite_range b).fintype
  have hB (x : B) : (x : MvPolynomial σ k) ∈ J ∧ (x : MvPolynomial σ k) ≠ 0 := by
    obtain ⟨e, h⟩ := x.property
    rw [← h]
    exact ⟨hb e, hn e⟩
  have hrep (x : B) : ∃ q : MvPolynomial σ k, (x : MvPolynomial σ k) - q * g ∈ I := by
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (hB x).1
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hj
    refine ⟨q, ?_⟩
    rw [← hij, mul_comm g q, add_sub_cancel_right]
    exact hi
  choose a ha using hrep
  refine ⟨Finset.univ.sup fun x : B => (a x).totalDegree, ?_⟩
  intro f hf
  obtain ⟨c, r, hfr, hc, hr⟩ :=
    m.div_set (B := B) (fun x hx => m.isUnit_leadingCoeff.mpr (hB ⟨x, hx⟩).2) f
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hfr
  have hsum : ∑ x ∈ c.support, c x • (x : MvPolynomial σ k) ∈ J :=
    J.sum_mem fun x _ => J.smul_mem (c x) (hB x).1
  have hrJ : r ∈ J := by
    convert J.sub_mem hf hsum using 1
    rw [hfr, add_comm, add_sub_cancel_right]
  have hr0 : r = 0 := by
    by_contra hr0
    have hstd : m.degree r ∈ m.standardExponents J := by
      apply (hE _).mpr
      intro e heE hle
      exact hr _ (m.degree_mem_support hr0) (b ⟨e, heE⟩) ⟨⟨e, heE⟩, rfl⟩
        ((he ⟨e, heE⟩).trans hle)
    exact hstd r hrJ hr0 le_rfl
  refine ⟨∑ x ∈ c.support, c x * a x, ?_, ?_⟩
  · rw [Finset.sum_mul, hfr, hr0, add_zero, ← Finset.sum_sub_distrib]
    exact I.sum_mem fun x _ => by
      simpa only [smul_eq_mul, mul_sub, mul_assoc] using I.mul_mem_left (c x) (ha x)
  · apply totalDegree_finsetSum_le
    intro x _
    have hcx : (c x).totalDegree ≤ f.totalDegree := by
      by_cases hx : c x = 0
      · simp [hx]
      have hx' := m.totalDegree_le_of_degree_le
        (fun _ _ h => degree_le_degree_of_degLex_le h) (hc x)
      rw [totalDegree_mul_of_isDomain (hB x).2 hx] at hx'
      omega
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add hcx (Finset.le_sup (f := fun y : B => (a y).totalDegree) (Finset.mem_univ x)))
end
end K1_13_6_2_3_3_1
end

end Merged_FiltrationLift

-- merged module Numeric5Defs
section Merged_Numeric5Defs
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_8
open CJ6 (VectorDots belowSucc belowZero block_rank_le rank_of_dots)
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l =>
  CJ6.Fast.vector b (buckets side q l) rfl rfl rfl (id (α := good side q l b) rfl)
end CJ6_8
end
section
namespace K1_13_2_3_5
open K1_13_2 K1_13_2_3
end K1_13_2_3_5
end

end Merged_Numeric5Defs

-- merged module Numeric5Certificate
section Merged_Numeric5Certificate
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_2_3_5
open K1_13_2 K1_13_2_3
open scoped BigOperators
structure Row where
  first : ℕ
  count : ℕ
  packed : ℕ
  deriving Inhabited
def unpack (packed : ℕ) : Powers :=
  ⟨packed % 512, packed / 512 % 512, packed / 262144 % 1024⟩
private def powersAt : ℕ → ℕ → Powers
  | 0, packed => unpack packed
  | k + 1, packed => powersAt k (packed / 268435456)
private def rowPowers (r : Row) (j : ℕ) : Powers :=
  powersAt (j - r.first) r.packed
private def assignment (start : ℕ) (rows : List Row) (i : BlockIndex) : Powers :=
  rowPowers (rows[i.1.val - start]?.getD default) i.2.val
end K1_13_2_3_5
end

end Merged_Numeric5Certificate

-- merged module Pack_K1_14_2_2Split
section Merged_Pack_K1_14_2_2Split
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
def c1 : Prop :=
  ∀ P s, P ≠ 0 → RowCaps P s → Nonempty (FixedPart P s)
end
end K1_14_2_2
end

end Merged_Pack_K1_14_2_2Split

-- merged module Pack_K1_14_2_2_4Split
section Merged_Pack_K1_14_2_2_4Split
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
def seedDegree (H : Equation) : ℕ :=
  H.support.sup fun j => (H.coeff j).totalDegree
def residualShape (s : Shape) (x z : ℕ) : Shape :=
  ⟨s.m, s.B - z, min s.J (s.B - z), s.U - x⟩
structure SharedGcd {w rows i} {B : RowPair w rows i} (A : FixedPair B) where
  ordinary : Equation
  cheapTail : Jet
  layeredTail : Jet
  ordinary_ne : ordinary ≠ 0
  cheap_ne : cheapTail ≠ 0
  layered_ne : layeredTail ≠ 0
  cheap_factor : B.cheap = fixedIncl A.cheap.equation * (C ordinary * cheapTail)
  layered_factor : B.layered = fixedIncl A.layered.equation * (C ordinary * layeredTail)
  relativelyPrime : IsRelPrime (toJet cheapTail) (toJet layeredTail)
  seed_le : seedDegree ordinary ≤ min (stageAt i).cheap.U (stageAt i).layered.U
  ordinate_le : ordinary.natDegree ≤ min (stageAt i).cheap.B (stageAt i).layered.B
  cheap_caps : RowCaps cheapTail
    (residualShape (stageAt i).cheap (seedDegree ordinary) ordinary.natDegree)
  layered_caps : RowCaps layeredTail
    (residualShape (stageAt i).layered (seedDegree ordinary) ordinary.natDegree)
def HighOn (H : Equation) (r : ℕ) (I : Ideal Ambient) : Prop :=
  ∃ f : Equation, Irreducible f ∧ 0 < f.natDegree ∧ f ^ r ∣ H ∧ toJet (C f) ∈ I
def highScale (r : ℕ) (k : Fin 4) : ℕ :=
  ![r, r, r ^ 2, r ^ 2] k
def highCap (x z : ℕ) (k : Fin 4) : ℕ :=
  ![z, x, 2 * x * z, x * x] k
def pairCap (s t : Shape) (k : Fin 4) : ℕ :=
  ![s.B * t.J + t.B * s.J - s.J * t.J, s.U * t.J + t.U * s.J,
    s.U * t.B + t.U * s.B, s.U * t.U] k
def localLength (P Q : Jet) (I : Ideal Ambient) (hp : I.IsPrime) : ℕ∞ :=
  letI : I.IsPrime := hp
  let R := Localization.AtPrime I
  letI : CommRing R := inferInstanceAs (CommRing (Localization.AtPrime I))
  let J : Ideal Ambient := Ideal.span {toJet P, toJet Q}
  let A : Ideal R := J.map (algebraMap Ambient R)
  Module.length R (R ⧸ (A : Submodule R R))
end
end K1_14_2_2_4
end
section
namespace K1_14_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
def residualScale (square : Bool) (k : Fin 4) (n : ℕ) : ℕ :=
  if square = true ∨ k = 3 then n ^ 2 else n
private def seedNumerator (s t : Shape) (d r z : ℕ) : ℕ :=
  d * z + r * pairCap (residualShape s 0 z) (residualShape t 0 z) 0
private def ordinateNumerator (s t : Shape) (d r x : ℕ) : ℕ :=
  d * x + r * ((s.U - x) * t.J + (t.U - x) * s.J)
private def mixedNumerator (s t : Shape) (d r x z : ℕ) : ℕ :=
  d * (2 * x * z) + r ^ 2 * ((s.U - x) * (t.B - z) + (t.U - x) * (s.B - z))
private def jetsNumerator (s t : Shape) (d r x : ℕ) : ℕ :=
  d * (x * x) + r ^ 2 * ((s.U - x) * (t.U - x))
private def checkNumerator (s t : Shape) (d r M : ℕ) (k : Fin 4) : Prop :=
  match k.val with
  | 0 => ∀ z : Fin (s.B + 1), seedNumerator s t d r z.val < M
  | 1 => ordinateNumerator s t d r 0 < M ∧ ordinateNumerator s t d r s.U < M
  | 2 => mixedNumerator s t d r 0 0 < M ∧ mixedNumerator s t d r 0 s.B < M ∧
      mixedNumerator s t d r s.U 0 < M ∧ mixedNumerator s t d r s.U s.B < M
  | _ => jetsNumerator s t d r 0 < M ∧ jetsNumerator s t d r s.U < M
private instance (s t : Shape) (d r M : ℕ) (k : Fin 4) :
    Decidable (checkNumerator s t d r M k) := by
  unfold checkNumerator
  split <;> infer_instance
private def certificate (i : Fin 10) (square : Bool) (cap : Fin 4 → ℕ)
    (k : Fin 4) (r : ℕ) : Prop :=
  let s := (stageAt i).cheap
  let t := (stageAt i).layered
  let m := (stageAt i).reserve + 1
  let d := residualScale square k (m + 1 - r)
  budget (i.val - 1) k ≤ cap k ∨
    (0 < r ∧ r ≤ m ∧ checkNumerator s t d r (highScale r k * d * (cap k + 1)) k)
private instance (i : Fin 10) (square : Bool) (cap : Fin 4 → ℕ)
    (k : Fin 4) (r : ℕ) : Decidable (certificate i square cap k r) := by
  unfold certificate
  infer_instance
end
end K1_14_2_2_4
end
section
set_option maxHeartbeats 1000000
namespace K1_14_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped Classical BigOperators
def c3 : Prop :=
  ∀ (H : Equation) (P : Jet) (I : Ideal Ambient) (m r : ℕ),
    H ≠ 0 → seedDegree H < p → H.natDegree < p →
    Active I → 0 < r → r ≤ m → ¬ HighOn H r I →
    orderOn I (C H * P) m → orderOn I P (m + 1 - r)
def c4 : Prop :=
  ∀ (P Q : Jet) (I : Ideal Ambient) (hI : Active I) (n : ℕ),
    0 < n → orderOn I P n → orderOn I Q n →
    ((if dual I then n ^ 2 else n : ℕ) : ℕ∞) ≤ localLength P Q I hI.prime
def c5 : Prop :=
  ∀ (P Q : Jet) (s t : Shape) (S : Finset (Ideal Ambient)) (k : Fin 4) (d : ℕ),
    P ≠ 0 → Q ≠ 0 → IsRelPrime (toJet P) (toJet Q) →
    s.J ≤ s.B → t.J ≤ t.B → RowCaps P s → RowCaps Q t → 0 < d →
    (∀ I ∈ S, ∃ hI : Active I,
      sectionDegree I k ≠ 0 → (d : ℕ∞) ≤ localLength P Q I hI.prime) →
    d * mass S k ≤ pairCap s t k
theorem cancel_fixed {I : Ideal Ambient} (hp : I.IsPrime) (G : ODE) (P : Jet)
    (m : ℕ) (hG : ¬ fixedOn G I) (ho : orderOn I (fixedIncl G * P) m) :
    orderOn I P m := by
  obtain ⟨a, ha, h⟩ := ho
  refine ⟨a * toJet (fixedIncl G), fun hn => (hp.mem_or_mem hn).elim ha hG, ?_⟩
  simpa only [map_mul, mul_assoc] using h
end
end K1_14_2_2_4
end

end Merged_Pack_K1_14_2_2_4Split

-- merged module Pack_K1_14_3_2_5_3Proof
section Merged_Pack_K1_14_3_2_5_3Proof
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 12
namespace K1_14_3_2_5_3
noncomputable section
open K1_14 K1_14_3 K1_14_3_2_5 Polynomial
open scoped nonZeroDivisors
end
end K1_14_3_2_5_3
end

end Merged_Pack_K1_14_3_2_5_3Proof

-- merged module Fast049
section Merged_Fast049
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_2_3_5
end K1_13_2_3_5
end
section
namespace K1_13_2_3_5
end K1_13_2_3_5
end
section
namespace K1_13_2_3_1
open K1_13_2
private def scaledDen (q r : ℤ) : ℤ :=
  2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem scaled_denominator (u : ℤ) (hu : 0 ≤ u) :
    2 * denominator u = scaledDen (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, not_lt.mpr hu, ite_false, scaledDen]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = _
  have h := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at h
  change _ = 2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
  linear_combination h + q * twice_half r + (57 + 6 * r) * twice_half q
private def prefixPolynomial (q r : ℤ) : ℤ :=
  984 * q + 3084 * q * (q - 1) + 1728 * q * (q - 1) * (q - 2) +
    216 * q * (q - 1) * (q - 2) * (q - 3) +
    24 * r + 4 * r * (r - 1) * (r + 1) +
    q * (528 * r + 84 * r * (r - 1) + 4 * r * (r - 1) * (r - 2)) +
    (684 * r + 36 * r * (r - 1)) * q * (q - 1) + 144 * r * q * (q - 1) * (q - 2)
def denPrefix (u : ℤ) : ℤ :=
  if u < 0 then 0 else prefixPolynomial (u / 6) (u % 6)
theorem denPrefix_of_nonpos (u : ℤ) (hu : u ≤ 0) : denPrefix u = 0 := by
  rcases lt_or_eq_of_le hu with h | rfl
  · simp [denPrefix, h]
  · decide
private theorem denPrefix_step (u : ℤ) :
    denPrefix (u + 1) - denPrefix u = 24 * denominator u := by
  by_cases h : u < 0
  · rw [denPrefix_of_nonpos _ (by omega), denPrefix_of_nonpos _ (by omega)]
    simp [denominator, h]
  have hd := scaled_denominator u (by omega)
  have hq : (u + 1) / 6 = u / 6 + (u % 6 + 1) / 6 := by omega
  have hr : (u + 1) % 6 = (u % 6 + 1) % 6 := by omega
  simp only [denPrefix, h, show ¬ u + 1 < 0 by omega, ite_false, hq, hr]
  have hlo : 0 ≤ u % 6 := by omega
  have hhi : u % 6 < 6 := by omega
  generalize u % 6 = r at hd hlo hhi ⊢
  interval_cases r <;> norm_num [prefixPolynomial, scaledDen] at hd ⊢ <;>
    linear_combination -12 * hd
theorem denPrefix_sum (a : ℤ) (n : ℕ) :
    24 * (∑ j ∈ Finset.range n, denominator (a + (j : ℤ))) =
      denPrefix (a + n) - denPrefix a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Nat.cast_succ, ← add_assoc, ← denPrefix_step]
    ring
end K1_13_2_3_1
end
section
namespace K1_13_2_3_1
open K1_13_2 K1_13_2_3
private theorem denominator_of_neg (u : ℤ) (h : u < 0) : denominator u = 0 := by
  simp [denominator, h]
private theorem cumulative_of_neg (d u : ℤ) (h : u < 0) : cumulative d u = 0 := by
  simp [cumulative, h]
private theorem cumulative_of_neg_degree (d u : ℤ) (h : d < 0) : cumulative d u = 0 := by
  simp [cumulative, h]
private theorem cumulative_eq_denominator (d u : ℤ) (h : u < d + 1) :
    cumulative d u = denominator u := by
  by_cases hu : u < 0
  · rw [cumulative_of_neg _ _ hu, denominator_of_neg _ hu]
  have hd : ¬ d < 0 := by omega
  simp (disch := omega) [cumulative, hu, hd, denominator_of_neg]
private theorem cumulative_nonneg (d : ℕ) (u : ℤ) : 0 ≤ cumulative (d : ℤ) u := by
  by_cases hu : u < 0
  · simp [cumulative_of_neg _ _ hu]
  have h := cumulative_mono d (show (-1 : ℤ) ≤ u by omega)
  rwa [cumulative_of_neg _ _ (by decide)] at h
private theorem denominator_nonneg (u : ℤ) : 0 ≤ denominator u := by
  by_cases hu : u < 0
  · simp [denominator_of_neg _ hu]
  have h := cumulative_nonneg u.toNat u
  rwa [Int.toNat_of_nonneg (by omega : 0 ≤ u), cumulative_eq_denominator _ _ (by omega)] at h
private theorem baseline_le_counts (i : BlockIndex) :
    baseline i ≤ (oldCount (initialFlag i)).toNat ∧
      baseline i ≤ (targetCount (initialFlag i)).toNat := by
  have hk : kernelLower (initialFlag i) = oldCount (initialFlag i) - targetCount (initialFlag i) := by
    simp [kernelLower, initialFlag]
  unfold baseline blockBound
  dsimp only
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · constructor <;> apply Int.toNat_le_toNat <;> apply (min_le_right _ _).trans
    · exact sub_le_self _ (le_max_left _ _)
    · have hm : kernelLower (initialFlag i) ≤ max 0 (max (kernelLower (initialFlag i))
          (kernelLower (residualFlag (initialFlag i) (fun _ => 0)))) :=
        (le_max_left _ _).trans (le_max_right _ _)
      omega
private def offsetBound (s x cut : ℕ) : ℤ :=
  let u := (x : ℤ) - (3000 - (s : ℤ))
  (if x < cut then cumulative (s : ℤ) x + denominator u else cumulative (s : ℤ) 1650) -
    cumulative (s : ℤ) u
private theorem oldCount_eq (s : Fin 4013) (j : Fin 4650) (hs : s.val < 1650)
    (x : ℕ) (hx : x + j.val + s.val = 4649) :
    oldCount (initialFlag (s, j)) =
      cumulative (s.val : ℤ) 1650 - cumulative (s.val : ℤ) ((x : ℤ) - (3000 - s.val)) := by
  have hc (u : ℤ) (hu : u ≤ 1650) : cappedCount (s.val : ℤ) u 550 = cumulative (s.val : ℤ) u := by
    simp (disch := omega) only [cappedCount, show ¬ (550 : ℤ) < 0 by decide, ite_false,
      cumulative_of_neg, sub_zero]
  simp only [oldCount, initialFlag, offset, min_eq_left (show (s.val : ℤ) ≤ 1650 by omega)]
  rw [show -((j.val : ℤ) - 1650) - 1 = (x : ℤ) - (3000 - s.val) by omega,
    min_eq_right (by omega : (x : ℤ) - (3000 - s.val) ≤ 1650), hc _ (by omega), hc _ (by omega)]
private theorem targetCount_eq (s : Fin 4013) (j : Fin 4650) (hs : s.val < 1650)
    (x : ℕ) (hx : x + j.val + s.val = 4649) (hx' : x < 1650) :
    targetCount (initialFlag (s, j)) = cumulative (s.val : ℤ) x +
      denominator ((x : ℤ) - (3000 - s.val)) -
      cumulative (s.val : ℤ) ((x : ℤ) - (3000 - s.val)) := by
  simp only [targetCount, initialFlag, offset, min_eq_left (show (s.val : ℤ) ≤ 1650 by omega)]
  rw [show 3000 - (s.val : ℤ) - ((j.val : ℤ) - 1650) - 1 = x by omega,
    show -((j.val : ℤ) - 1650) - 1 = (x : ℤ) - (3000 - s.val) by omega]
  rw [show (x : ℤ) - -((j.val : ℤ) - 1650) + s.val = 2999 by omega]
  norm_num only [Int.reduceLT, ite_false, Int.reduceDiv]
  by_cases h : s.val ≤ 749
  · rw [min_eq_left (show (s.val : ℤ) ≤ 749 by omega)]
    simp (disch := omega) only [cumulative_of_neg_degree, denominator_of_neg, sub_zero, add_zero]
  · rw [min_eq_right (show (749 : ℤ) ≤ s.val by omega)]
    rw [cumulative_of_neg ((s.val : ℤ) - (749 + 1)) ((x : ℤ) - 3 * (749 + 1)) (by omega),
      cumulative_eq_denominator ((s.val : ℤ) - (749 + 1)) ((x : ℤ) - (3000 - s.val)) (by omega),
      sub_zero]
    ring
private theorem offsetBound_nonneg (s x cut : ℕ) (hs : s < 1650) (hx : x < 4650 - s) :
    0 ≤ offsetBound s x cut := by
  unfold offsetBound
  dsimp only
  split
  · have hm := cumulative_mono s (show (x : ℤ) - (3000 - s) ≤ x by omega)
    have hd := denominator_nonneg ((x : ℤ) - (3000 - s))
    omega
  · exact sub_nonneg.mpr (cumulative_mono s (by omega))
private theorem baseline_le_offsetBound (s : Fin 4013) (j : Fin 4650) (hs : s.val < 1650)
    (cut x : ℕ) (hcut : cut ≤ 1650) (hx : x + j.val + s.val = 4649) :
    baseline (s, j) ≤ (offsetBound s.val x cut).toNat := by
  unfold offsetBound
  dsimp only
  split
  · rw [← targetCount_eq s j hs x hx (by omega)]
    exact (baseline_le_counts (s, j)).2
  · rw [← oldCount_eq s j hs x hx]
    exact (baseline_le_counts (s, j)).1
private theorem sum_cutoff {α : Type*} [AddCommMonoid α] (f : ℕ → α) {m n : ℕ} (h : m ≤ n) :
    (∑ j ∈ Finset.range n, if j < m then f j else 0) = ∑ j ∈ Finset.range m, f j := by
  calc
    _ = ∑ j ∈ Finset.range m, if j < m then f j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono h)
      intro j _ hj
      rw [Finset.mem_range] at hj
      rw [ite_eq_right hj]
    _ = _ := Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
private theorem sum_row (s : Fin 4013) (hs : s.val < 1650) (cut : ℕ) (hcut : cut ≤ 1650) :
    (∑ j : Fin 4650, baseline (s, j)) ≤
      ∑ x ∈ Finset.range (4650 - s.val), (offsetBound s.val x cut).toNat := by
  let n := 4650 - s.val
  calc
    _ ≤ ∑ j : Fin 4650, if j.val < n then (offsetBound s.val (n - 1 - j.val) cut).toNat else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j.val < n
      · rw [ite_eq_left hj]
        exact baseline_le_offsetBound s j hs cut _ hcut (by dsimp [n] at *; omega)
      · have ho : (initialFlag (s, j)).order ≤ 0 := by
          simp only [initialFlag, offset]
          dsimp [n] at hj
          omega
        simp [baseline, blockBound, ho, hj]
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if j < n then (offsetBound s.val (n - 1 - j) cut).toNat else 0)]
      rw [sum_cutoff _ (show n ≤ 4650 by dsimp [n]; omega)]
      exact Finset.sum_range_reflect (fun x : ℕ => (offsetBound s.val x cut).toNat) n
private def rowScaled (s cut : ℕ) : ℤ :=
  24 * (((4650 - s - cut : ℕ) : ℤ) * cumulative (s : ℤ) 1650 -
    ∑ x ∈ Finset.range (1650 - cut), cumulative (s : ℤ) ((cut + x : ℕ) : ℤ)) +
    denPrefix ((cut : ℤ) - (3000 - s))
private theorem sum_offsetBound (s cut : ℕ) (hs : s < 1650) (hcut : cut ≤ 1650) :
    24 * (∑ x ∈ Finset.range (4650 - s), offsetBound s x cut) = rowScaled s cut := by
  let n := 4650 - s
  let k : ℤ := 3000 - (s : ℤ)
  let C := cumulative (s : ℤ)
  let f := fun x : ℕ => C x + denominator ((x : ℤ) - k)
  have hChosen : (∑ x ∈ Finset.range n, if x < cut then f x else C 1650) =
      (∑ x ∈ Finset.range cut, f x) + ((n - cut : ℕ) : ℤ) * C 1650 := by
    conv_lhs => rw [show n = cut + (n - cut) by dsimp [n]; omega, Finset.sum_range_add]
    congr 1
    · exact Finset.sum_congr rfl fun _ hx => ite_eq_left (Finset.mem_range.mp hx)
    · simp (disch := omega) only [not_lt.mpr (Nat.le_add_right cut _), ite_false,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hLower : (∑ x ∈ Finset.range n, C ((x : ℤ) - k)) = ∑ x ∈ Finset.range 1650, C x := by
    rw [show n = (3000 - s) + 1650 by dsimp [n]; omega, Finset.sum_range_add]
    have hz : (∑ x ∈ Finset.range (3000 - s), C ((x : ℤ) - k)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hx' := Finset.mem_range.mp hx
      exact cumulative_of_neg _ _ (by dsimp [k]; omega)
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Nat.cast_add, Nat.cast_sub (show s ≤ 3000 by omega)]
    dsimp [k]
    ring
  have hSplit : (∑ x ∈ Finset.range 1650, C x) =
      (∑ x ∈ Finset.range cut, C x) +
        ∑ x ∈ Finset.range (1650 - cut), C ((cut + x : ℕ) : ℤ) := by
    rw [← Finset.sum_range_add, Nat.add_sub_of_le hcut]
  have hp : 24 * (∑ x ∈ Finset.range cut, denominator ((x : ℤ) - k)) = denPrefix ((cut : ℤ) - k) := by
    simp_rw [show ∀ x : ℕ, (x : ℤ) - k = -k + (x : ℤ) from fun x => by ring]
    rw [denPrefix_sum, denPrefix_of_nonpos (-k) (by dsimp [k]; omega), sub_zero]
  unfold rowScaled
  simp only [offsetBound, Finset.sum_sub_distrib]
  change 24 * ((∑ x ∈ Finset.range n, if x < cut then f x else C 1650) -
    ∑ x ∈ Finset.range n, C ((x : ℤ) - k)) =
      24 * (((n - cut : ℕ) : ℤ) * C 1650 -
        ∑ x ∈ Finset.range (1650 - cut), C ((cut + x : ℕ) : ℤ)) + denPrefix ((cut : ℤ) - k)
  rw [hChosen, hLower, hSplit]
  dsimp only [f]
  rw [Finset.sum_add_distrib]
  linear_combination hp
private def gradeCut (s : ℕ) : ℕ :=
  if s < 1549 then 1650 else if s < 1603 then 1649 else if s < 1641 then 1648 else 1647
private def grade (s : ℕ) : ℤ := rowScaled s (gradeCut s)
private theorem grade_bound (s : Fin 4013) (hs : s.val < 1650) :
    24 * ((∑ j : Fin 4650, baseline (s, j) : ℕ) : ℤ) ≤ grade s.val := by
  have hcut : gradeCut s.val ≤ 1650 := by
    unfold gradeCut
    split <;> (try split) <;> (try split) <;> omega
  calc
    _ ≤ 24 * ((∑ x ∈ Finset.range (4650 - s.val), (offsetBound s.val x (gradeCut s.val)).toNat : ℕ) : ℤ) := by
      apply mul_le_mul_of_nonneg_left _ (by decide)
      exact_mod_cast sum_row s hs _ hcut
    _ = 24 * (∑ x ∈ Finset.range (4650 - s.val), offsetBound s.val x (gradeCut s.val)) := by
      rw [Nat.cast_sum]
      congr 1
      exact Finset.sum_congr rfl fun x hx =>
        Int.toNat_of_nonneg (offsetBound_nonneg _ _ _ hs (Finset.mem_range.mp hx))
    _ = _ := sum_offsetBound _ _ hs hcut
private def total (start : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => total start n + grade (start + n)
private theorem total_eq (start n : ℕ) :
    total start n = ∑ j ∈ Finset.range n, grade (start + j) := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [total, Finset.sum_range_succ, ih]
private theorem k1231_total_append (s m n : ℕ) :
    total s (m + n) = total s m + total (s + m) n := by
  simp only [total_eq, Finset.sum_range_add, Nat.add_assoc]
private theorem k1231_total_join {s t m n k : ℕ} {a b c : ℤ}
    (ha : total s m = a) (hb : total t n = b)
    (ht : s + m = t) (hk : m + n = k) (hs : a + b = c) : total s k = c := by
  rw [← hk, k1231_total_append, ht, ha, hb, hs]
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private theorem k1231_grades_551 : total 551 16 = 27517850683872 := by
  decide +kernel
private theorem k1231_grades_567 : total 567 16 = 29734411311072 := by
  decide +kernel
private theorem k1231_grades_583 : total 583 16 = 32028905051616 := by
  decide +kernel
private theorem k1231_grades_599 : total 599 16 = 34385973281760 := by
  decide +kernel
private theorem k1231_grades_615 : total 615 16 = 36790609699296 := by
  decide +kernel
private theorem k1231_grades_631 : total 631 16 = 39228160323552 := by
  decide +kernel
private theorem k1231_grades_647 : total 647 16 = 41684323495392 := by
  decide +kernel
private theorem k1231_grades_663 : total 663 16 = 44145149877216 := by
  decide +kernel
private theorem k1231_grades_679 : total 679 16 = 46597042452960 := by
  decide +kernel
private theorem k1231_grades_695 : total 695 16 = 49026756528096 := by
  decide +kernel
private theorem k1231_grades_711 : total 711 16 = 51421399729632 := by
  decide +kernel
private theorem k1231_grades_727 : total 727 16 = 53768432006112 := by
  decide +kernel
private theorem k1231_grades_743 : total 743 16 = 56055665627616 := by
  decide +kernel
private theorem k1231_grades_759 : total 759 16 = 58271265185760 := by
  decide +kernel
private theorem k1231_grades_775 : total 775 16 = 60403747593696 := by
  decide +kernel
private theorem k1231_grades_791 : total 791 16 = 62441982086112 := by
  decide +kernel
private theorem k1231_grades_807 : total 807 16 = 64375190219232 := by
  decide +kernel
private theorem k1231_grades_823 : total 823 16 = 66193253109384 := by
  decide +kernel
private theorem k1231_grades_839 : total 839 16 = 67891598872128 := by
  decide +kernel
private theorem k1231_grades_855 : total 855 16 = 69472878502464 := by
  decide +kernel
private theorem k1231_grades_871 : total 871 16 = 70940659492416 := by
  decide +kernel
private theorem k1231_grades_887 : total 887 16 = 72298459159104 := by
  decide +kernel
private theorem k1231_grades_903 : total 903 16 = 73549744488000 := by
  decide +kernel
private theorem k1231_grades_919 : total 919 16 = 74697932132928 := by
  decide +kernel
private theorem k1231_grades_935 : total 935 16 = 75746388416064 := by
  decide +kernel
private theorem k1231_grades_951 : total 951 16 = 76698429327936 := by
  decide +kernel
private theorem k1231_grades_967 : total 967 16 = 77557320527424 := by
  decide +kernel
private theorem k1231_grades_983 : total 983 16 = 78326277341760 := by
  decide +kernel
private theorem k1231_grades_999 : total 999 16 = 79008464766528 := by
  decide +kernel
private theorem k1231_grades_1015 : total 1015 16 = 79606997465664 := by
  decide +kernel
private theorem k1231_grades_1031 : total 1031 16 = 80124939771456 := by
  decide +kernel
private theorem k1231_grades_1047 : total 1047 16 = 80565305684544 := by
  decide +kernel
private theorem k1231_grades_1063 : total 1063 16 = 80931058873920 := by
  decide +kernel
private theorem k1231_grades_1079 : total 1079 16 = 81225112676928 := by
  decide +kernel
private theorem k1231_grades_1095 : total 1095 16 = 81450330099264 := by
  decide +kernel
private theorem k1231_grades_1111 : total 1111 16 = 81609523814976 := by
  decide +kernel
private theorem k1231_grades_1127 : total 1127 16 = 81705456166464 := by
  decide +kernel
private theorem k1231_grades_1143 : total 1143 16 = 81740839164480 := by
  decide +kernel
private theorem k1231_grades_1159 : total 1159 16 = 81718334488128 := by
  decide +kernel
private theorem k1231_grades_1175 : total 1175 16 = 81640553484864 := by
  decide +kernel
private theorem k1231_grades_1191 : total 1191 16 = 81510057170496 := by
  decide +kernel
private theorem k1231_grades_1207 : total 1207 16 = 81329356229184 := by
  decide +kernel
private theorem k1231_grades_1223 : total 1223 16 = 81100911013440 := by
  decide +kernel
private theorem k1231_grades_1239 : total 1239 16 = 80827131544128 := by
  decide +kernel
private theorem k1231_grades_1255 : total 1255 16 = 80510377510464 := by
  decide +kernel
private theorem k1231_grades_1271 : total 1271 16 = 80152958270016 := by
  decide +kernel
private theorem k1231_grades_1287 : total 1287 16 = 79757132848704 := by
  decide +kernel
private theorem k1231_grades_1303 : total 1303 16 = 79325109940800 := by
  decide +kernel
private theorem k1231_grades_1319 : total 1319 16 = 78859047908928 := by
  decide +kernel
private theorem k1231_grades_1335 : total 1335 16 = 78361054784064 := by
  decide +kernel
private theorem k1231_grades_1351 : total 1351 16 = 77833188356040 := by
  decide +kernel
private theorem k1231_grades_1367 : total 1367 16 = 77277457488840 := by
  decide +kernel
private theorem k1231_grades_1383 : total 1383 16 = 76695824339568 := by
  decide +kernel
private theorem k1231_grades_1399 : total 1399 16 = 76090204918728 := by
  decide +kernel
private theorem k1231_grades_1415 : total 1415 16 = 75462469099464 := by
  decide +kernel
private theorem k1231_grades_1431 : total 1431 16 = 74814440617584 := by
  decide +kernel
private theorem k1231_grades_1447 : total 1447 16 = 74147897071560 := by
  decide +kernel
private theorem k1231_grades_1463 : total 1463 16 = 73464569922504 := by
  decide +kernel
private theorem k1231_grades_1479 : total 1479 16 = 72766144494192 := by
  decide +kernel
private theorem k1231_grades_1495 : total 1495 16 = 72054259973064 := by
  decide +kernel
private theorem k1231_grades_1511 : total 1511 16 = 71330509408200 := by
  decide +kernel
private theorem k1231_grades_1527 : total 1527 16 = 70596439711344 := by
  decide +kernel
private theorem k1231_grades_1543 : total 1543 16 = 69853547426688 := by
  decide +kernel
private theorem k1231_grades_1559 : total 1559 16 = 69103274454600 := by
  decide +kernel
private theorem k1231_grades_1575 : total 1575 16 = 68347041289800 := by
  decide +kernel
private theorem k1231_grades_1591 : total 1591 16 = 67586210218392 := by
  decide +kernel
private theorem k1231_grades_1607 : total 1607 16 = 66822074236464 := by
  decide +kernel
private theorem k1231_grades_1623 : total 1623 16 = 66055914261384 := by
  decide +kernel
private theorem k1231_grades_1639 : total 1639 11 = 44968541077224 := by
  decide +kernel
end
private theorem total_check : total 551 1099 = 4709579868565680 := by
  have h551_583 : total 551 32 = 57252261994944 :=
    k1231_total_join k1231_grades_551 k1231_grades_567 rfl rfl rfl
  have h583_615 : total 583 32 = 66414878333376 :=
    k1231_total_join k1231_grades_583 k1231_grades_599 rfl rfl rfl
  have h551_615 : total 551 64 = 0x70797ff83b80 :=
    k1231_total_join h551_583 h583_615 rfl rfl rfl
  have h615_647 : total 615 32 = 76018770022848 :=
    k1231_total_join k1231_grades_615 k1231_grades_631 rfl rfl rfl
  have h647_679 : total 647 32 = 85829473372608 :=
    k1231_total_join k1231_grades_647 k1231_grades_663 rfl rfl rfl
  have h615_679 : total 615 64 = 0x93333b0e1b80 :=
    k1231_total_join h615_647 h647_679 rfl rfl rfl
  have h551_679 : total 551 128 = 285515383723776 :=
    k1231_total_join h551_615 h615_679 rfl rfl rfl
  have h679_711 : total 679 32 = 95623798981056 :=
    k1231_total_join k1231_grades_679 k1231_grades_695 rfl rfl rfl
  have h711_743 : total 711 32 = 0x5fab6a8df9c0 :=
    k1231_total_join k1231_grades_711 k1231_grades_727 rfl rfl rfl
  have h679_743 : total 679 64 = 0xb6a3911ffb80 :=
    k1231_total_join h679_711 h711_743 rfl rfl rfl
  have h743_775 : total 743 32 = 0x67fad01971c0 :=
    k1231_total_join k1231_grades_743 k1231_grades_759 rfl rfl rfl
  have h791_823 : total 791 32 = 0x7356ec81b5c0 :=
    k1231_total_join k1231_grades_791 k1231_grades_807 rfl rfl rfl
  have h775_823 : total 775 48 = 0xaa46c46cd3a0 :=
    k1231_total_join k1231_grades_775 h791_823 rfl rfl rfl
  have h743_823 : total 743 80 = 301547850712416 :=
    k1231_total_join h743_775 h775_823 rfl rfl rfl
  have h679_823 : total 679 144 = 502361481429216 :=
    k1231_total_join h679_743 h743_823 rfl rfl rfl
  have h551_823 : total 551 272 = 787876865152992 :=
    k1231_total_join h551_679 h679_823 rfl rfl rfl
  have h823_855 : total 823 32 = 0x79f30ff8dcc8 :=
    k1231_total_join k1231_grades_823 k1231_grades_839 rfl rfl rfl
  have h855_887 : total 855 32 = 0x7fb4930dc880 :=
    k1231_total_join k1231_grades_855 k1231_grades_871 rfl rfl rfl
  have h823_887 : total 823 64 = 0xf9a7a306a548 :=
    k1231_total_join h823_855 h855_887 rfl rfl rfl
  have h887_919 : total 887 32 = 0x84a5ee5e9880 :=
    k1231_total_join k1231_grades_887 k1231_grades_903 rfl rfl rfl
  have h919_951 : total 919 32 = 0x88d40c48e880 :=
    k1231_total_join k1231_grades_919 k1231_grades_935 rfl rfl rfl
  have h887_951 : total 887 64 = 296292524196096 :=
    k1231_total_join h887_919 h919_951 rfl rfl rfl
  have h823_951 : total 823 128 = 570790914172488 :=
    k1231_total_join h823_887 h887_951 rfl rfl rfl
  have h951_983 : total 951 32 = 0x8c4b772cb880 :=
    k1231_total_join k1231_grades_951 k1231_grades_967 rfl rfl rfl
  have h983_1015 : total 983 32 = 0x8f18596a0880 :=
    k1231_total_join k1231_grades_983 k1231_grades_999 rfl rfl rfl
  have h951_1015 : total 951 64 = 311590491963648 :=
    k1231_total_join h951_983 h983_1015 rfl rfl rfl
  have h1015_1047 : total 1015 32 = 0x91467d60d880 :=
    k1231_total_join k1231_grades_1015 k1231_grades_1031 rfl rfl rfl
  have h1063_1095 : total 1063 32 = 0x937aed00e080 :=
    k1231_total_join k1231_grades_1063 k1231_grades_1079 rfl rfl rfl
  have h1047_1095 : total 1047 48 = 0xdcc0ff6e12c0 :=
    k1231_total_join k1231_grades_1047 h1063_1095 rfl rfl rfl
  have h1015_1095 : total 1015 80 = 402453414472512 :=
    k1231_total_join h1015_1047 h1047_1095 rfl rfl rfl
  have h951_1095 : total 951 144 = 714043906436160 :=
    k1231_total_join h951_1015 h1015_1095 rfl rfl rfl
  have h823_1095 : total 823 272 = 0x4908ceb13d288 :=
    k1231_total_join h823_951 h951_1095 rfl rfl rfl
  have h551_1095 : total 551 544 = 0x75d1ecbc06a68 :=
    k1231_total_join h551_823 h823_1095 rfl rfl rfl
  have h1095_1127 : total 1095 32 = 0x944d54ab7080 :=
    k1231_total_join k1231_grades_1095 k1231_grades_1111 rfl rfl rfl
  have h1127_1159 : total 1127 32 = 0x94a74e5f8080 :=
    k1231_total_join k1231_grades_1127 k1231_grades_1143 rfl rfl rfl
  have h1095_1159 : total 1095 64 = 326506149245184 :=
    k1231_total_join h1095_1127 h1127_1159 rfl rfl rfl
  have h1159_1191 : total 1159 32 = 0x9492f47d1080 :=
    k1231_total_join k1231_grades_1159 k1231_grades_1175 rfl rfl rfl
  have h1191_1223 : total 1191 32 = 0x941a01642080 :=
    k1231_total_join k1231_grades_1191 k1231_grades_1207 rfl rfl rfl
  have h1159_1223 : total 1159 64 = 326198301372672 :=
    k1231_total_join h1159_1191 h1191_1223 rfl rfl rfl
  have h1095_1223 : total 1095 128 = 652704450617856 :=
    k1231_total_join h1095_1159 h1159_1223 rfl rfl rfl
  have h1223_1255 : total 1223 32 = 0x9345cf74b080 :=
    k1231_total_join k1231_grades_1223 k1231_grades_1239 rfl rfl rfl
  have h1255_1287 : total 1255 32 = 0x921f590ec080 :=
    k1231_total_join k1231_grades_1255 k1231_grades_1271 rfl rfl rfl
  have h1223_1287 : total 1223 64 = 322591378338048 :=
    k1231_total_join h1223_1255 h1255_1287 rfl rfl rfl
  have h1287_1319 : total 1287 32 = 0x90af38925080 :=
    k1231_total_join k1231_grades_1287 k1231_grades_1303 rfl rfl rfl
  have h1335_1367 : total 1335 32 = 0x8e0ece60da08 :=
    k1231_total_join k1231_grades_1335 k1231_grades_1351 rfl rfl rfl
  have h1319_1367 : total 1319 48 = 0xd5c79bea9048 :=
    k1231_total_join k1231_grades_1319 h1335_1367 rfl rfl rfl
  have h1287_1367 : total 1287 80 = 394135533838536 :=
    k1231_total_join h1287_1319 h1319_1367 rfl rfl rfl
  have h1223_1367 : total 1223 144 = 716726912176584 :=
    k1231_total_join h1223_1287 h1287_1367 rfl rfl rfl
  have h1095_1367 : total 1095 272 = 0x4dd7d95ec73c8 :=
    k1231_total_join h1095_1223 h1223_1367 rfl rfl rfl
  have h1367_1399 : total 1367 32 = 0x8c09b2c4ae38 :=
    k1231_total_join k1231_grades_1367 k1231_grades_1383 rfl rfl rfl
  have h1399_1431 : total 1399 32 = 0x89d61b4cb390 :=
    k1231_total_join k1231_grades_1399 k1231_grades_1415 rfl rfl rfl
  have h1367_1431 : total 1367 64 = 305525955846600 :=
    k1231_total_join h1367_1399 h1399_1431 rfl rfl rfl
  have h1431_1463 : total 1431 32 = 0x877aff390e38 :=
    k1231_total_join k1231_grades_1431 k1231_grades_1447 rfl rfl rfl
  have h1479_1511 : total 1479 32 = 0x83b6a0c3b638 :=
    k1231_total_join k1231_grades_1479 k1231_grades_1495 rfl rfl rfl
  have h1463_1511 : total 1463 48 = 0xc6876e5bba00 :=
    k1231_total_join k1231_grades_1463 h1479_1511 rfl rfl rfl
  have h1431_1511 : total 1431 80 = 367247312078904 :=
    k1231_total_join h1431_1463 h1463_1511 rfl rfl rfl
  have h1367_1511 : total 1367 144 = 672773267925504 :=
    k1231_total_join h1367_1431 h1431_1511 rfl rfl rfl
  have h1511_1543 : total 1511 32 = 0x8114f162e638 :=
    k1231_total_join k1231_grades_1511 k1231_grades_1527 rfl rfl rfl
  have h1543_1575 : total 1543 32 = 0x7e616801e1c8 :=
    k1231_total_join k1231_grades_1543 k1231_grades_1559 rfl rfl rfl
  have h1511_1575 : total 1511 64 = 0xff765964c800 :=
    k1231_total_join h1511_1543 h1543_1575 rfl rfl rfl
  have h1575_1607 : total 1575 32 = 0x7ba16d2b57e0 :=
    k1231_total_join k1231_grades_1575 k1231_grades_1591 rfl rfl rfl
  have h1623_1650 : total 1623 27 = 0x64f9e538ca70 :=
    k1231_total_join k1231_grades_1623 k1231_grades_1639 rfl rfl rfl
  have h1607_1650 : total 1607 43 = 0xa1c01f3848a0 :=
    k1231_total_join k1231_grades_1607 h1623_1650 rfl rfl rfl
  have h1575_1650 : total 1575 75 = 313779781083264 :=
    k1231_total_join h1575_1607 h1607_1650 rfl rfl rfl
  have h1511_1650 : total 1511 139 = 594663552084096 :=
    k1231_total_join h1511_1575 h1575_1650 rfl rfl rfl
  have h1367_1650 : total 1367 283 = 0x480ba216e9280 :=
    k1231_total_join h1367_1511 h1511_1650 rfl rfl rfl
  have h1095_1650 : total 1095 555 = 0x95e37b75b0648 :=
    k1231_total_join h1095_1367 h1367_1650 rfl rfl rfl
  exact k1231_total_join h551_1095 h1095_1650 rfl rfl rfl
private theorem sum_grades :
    (∑ s ∈ Finset.range 4013, if 551 ≤ s ∧ s < 1650 then grade s else 0) = total 551 1099 := by
  simp_rw [show ∀ s : ℕ, (if 551 ≤ s ∧ s < 1650 then grade s else 0) =
    if s < 1650 then (if 551 ≤ s then grade s else 0) else 0 from fun s => by
      by_cases h : s < 1650 <;> simp [h]]
  rw [sum_cutoff _ (by decide : 1650 ≤ 4013), total_eq]
  rw [show (1650 : ℕ) = 551 + 1099 by decide, Finset.sum_range_add]
  have hz : (∑ x ∈ Finset.range 551, if 551 ≤ x then grade x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact ite_eq_right (not_le.mpr (Finset.mem_range.mp hx))
  rw [hz, zero_add]
  exact Finset.sum_congr rfl fun x _ => ite_eq_left (Nat.le_add_right 551 x)
theorem proof : K1_13_2_3.c1 := by
  have hb : 24 * ((baselineSum 551 1650 : ℕ) : ℤ) ≤
      ∑ s : Fin 4013, if 551 ≤ s.val ∧ s.val < 1650 then grade s.val else 0 := by
    unfold baselineSum baselineSumOn
    rw [← Finset.univ_product_univ, Finset.sum_product, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    by_cases h : 551 ≤ s.val ∧ s.val < 1650
    · simpa only [ite_eq_left h] using grade_bound s h.2
    · simp [h]
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => if 551 ≤ s ∧ s < 1650 then grade s else 0),
    sum_grades, total_check] at hb
  unfold K1_13_2_3.c1
  omega
end K1_13_2_3_1
end
section
namespace K1_13_2_3_3
open K1_13_2
open K1_13_2_3_1 (denPrefix denPrefix_of_nonpos denPrefix_sum)
private def twiceDenPoly (q r : ℤ) : ℤ :=
  12 * q^3 + (21 + 6 * r) * q^2 + (11 + 7 * r + r^2) * q + 2 + r + r^2
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem twice_denominator (u : ℤ) (hu : 0 ≤ u) :
    2 * denominator u = twiceDenPoly (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, ite_eq_right (not_lt.mpr hu)]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = twiceDenPoly q r
  have h := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at h
  unfold twiceDenPoly
  linear_combination h + q * twice_half r + (57 + 6 * r) * twice_half q
theorem prefix_offset_step (a j : ℤ) :
    denPrefix (a - j) - denPrefix (a - (j + 1)) = 24 * denominator (a - 1 - j) := by
  have h := (denPrefix_sum (a - 1 - j) 1).symm
  simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, Nat.cast_one] at h
  convert h using 1
  ring_nf
theorem denominator_of_neg (u : ℤ) (hu : u < 0) : denominator u = 0 := by
  simp only [denominator, ite_eq_left hu]
def smallCount (d u : ℤ) : ℤ :=
  denominator u - denominator (u - d - 1) - denominator (u - d - 2) -
    denominator (u - d - 3)
theorem cumulative_eq_small (d u : ℤ) (hd : 2 ≤ d) (hu : u ≤ 2 * d + 2) :
    cumulative d u = smallCount d u := by
  by_cases hn : u < 0
  · simp only [cumulative, hn, decide_true, Bool.or_true, ite_true, smallCount,
      denominator_of_neg u hn, denominator_of_neg (u - d - 1) (by omega),
      denominator_of_neg (u - d - 2) (by omega), denominator_of_neg (u - d - 3) (by omega),
      sub_zero]
  simp only [cumulative, smallCount, show ¬ d < 0 by omega, hn,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false, min_eq_left (by omega : u ≤ 3*d),
    show denominator (u - 2*d - 3) = 0 by simp [denominator, show u - 2*d - 3 < 0 by omega],
    show denominator (u - 2*d - 4) = 0 by simp [denominator, show u - 2*d - 4 < 0 by omega],
    show denominator (u - 2*d - 5) = 0 by simp [denominator, show u - 2*d - 5 < 0 by omega],
    show denominator (u - 3*d - 6) = 0 by simp [denominator, show u - 3*d - 6 < 0 by omega],
    add_zero, sub_zero]
theorem smallCount_eq_denominator (d u : ℤ) (h : u ≤ d) : smallCount d u = denominator u := by
  simp only [smallCount, denominator_of_neg (u - d - 1) (by omega),
    denominator_of_neg (u - d - 2) (by omega), denominator_of_neg (u - d - 3) (by omega), sub_zero]
def smallPrefix (d t : ℤ) : ℤ :=
  denPrefix t - denPrefix (t - (d + 1)) - denPrefix (t - (d + 2)) - denPrefix (t - (d + 3))
theorem smallPrefix_of_nonpos (d t : ℤ) (hd : 0 ≤ d) (ht : t ≤ 0) :
    smallPrefix d t = 0 := by
  unfold smallPrefix
  simp only [denPrefix_of_nonpos t ht, denPrefix_of_nonpos (t - (d + 1)) (by omega),
    denPrefix_of_nonpos (t - (d + 2)) (by omega), denPrefix_of_nonpos (t - (d + 3)) (by omega), sub_zero]
theorem smallPrefix_offset_step (d a j : ℤ) :
    smallPrefix d (a - j) - smallPrefix d (a - (j + 1)) = 24 * smallCount d (a - 1 - j) := by
  unfold smallPrefix smallCount
  have h (k : ℤ) :
      denPrefix (a - j - k) - denPrefix (a - (j + 1) - k) = 24 * denominator (a - 1 - j - k) := by
    convert prefix_offset_step (a - k) j using 1 <;> ring_nf
  rw [show a - 1 - j - d - 1 = a - 1 - j - (d + 1) by ring,
    show a - 1 - j - d - 2 = a - 1 - j - (d + 2) by ring,
    show a - 1 - j - d - 3 = a - 1 - j - (d + 3) by ring]
  linear_combination (norm := ring_nf) prefix_offset_step a j - h (d + 1) - h (d + 2) - h (d + 3)
theorem denominator_mono_to (u v : ℤ) (h : u ≤ v) (hv : v ≤ 1650) :
    denominator u ≤ denominator v := by
  have he (x : ℤ) (hx : x ≤ 1650) : cumulative 1650 x = denominator x :=
    (cumulative_eq_small _ _ (by decide) (by omega)).trans (smallCount_eq_denominator _ _ hx)
  rw [← he u (h.trans hv), ← he v hv]
  exact K1_13_2_3.cumulative_mono 1650 h
theorem denominator_quadruple (t : ℤ) (ht : 0 ≤ t) :
    4 * denominator t ≤ denominator (6 * (2 * (t / 6) + 1) + t % 6) := by
  let q := t / 6
  let r := t % 6
  have hq : 0 ≤ q := by dsimp [q]; omega
  have hr : 0 ≤ r := by dsimp [r]; omega
  have hr' : 0 ≤ 5 - r := by dsimp [r]; omega
  have h := twice_denominator t ht
  change 2 * denominator t = twiceDenPoly q r at h
  have hw := twice_denominator (6 * (2 * q + 1) + r) (by omega)
  rw [show (6 * (2 * q + 1) + r) / 6 = 2 * q + 1 by omega,
    show (6 * (2 * q + 1) + r) % 6 = r by omega] at hw
  have hp : twiceDenPoly (2 * q + 1) r - 4 * twiceDenPoly q r =
      48 * q^3 + 144 * q^2 + (134 + 2 * r * (5 - r)) * q + 38 + 2 * r * (5 - r) := by
    unfold twiceDenPoly
    ring
  have hn : 0 ≤ 48 * q^3 + 144 * q^2 + (134 + 2 * r * (5 - r)) * q + 38 + 2 * r * (5 - r) := by
    positivity
  change 4 * denominator t ≤ denominator (6 * (2 * q + 1) + r)
  omega
end K1_13_2_3_3
end
section
namespace K1_13_2_3_4
open K1_13_2 K1_13_2_3
def windowFlag (s j : ℕ) : Flag :=
  ⟨min s 1650, 1650 - (j : ℤ), 1650, 550, 4650 - (s : ℤ) - j⟩
def cubicFlag (F : Flag) (k : ℕ) : Flag :=
  ⟨F.degree - 3 * (k : ℤ), F.lower - 2 * k, F.upper - 3 * k, F.cap - k,
    F.order - 3 * k⟩
def cubicSavings (s j k : ℕ) : ℕ :=
  if k = 0 then 0 else
    let F := windowFlag s j
    let old := oldCount F
    let lower := max 0 (kernelLower F)
    (old - lower).toNat - (old - max lower (kernelLower (cubicFlag F k))).toNat
def entry (s q k : ℕ) : ℕ :=
  let j := 3000 + q - s
  if 993 ≤ j ∧ j ≤ 1581 then cubicSavings s j k else 0
def rowPower (code : ℕ) : ℕ → ℕ
  | 0 => code % 512
  | q + 1 => rowPower (code / 512) q
def rowSum (s q code : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => entry s q (code % 512) + rowSum s (q + 1) (code / 512) n
def rowsSum (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | row :: rows => rowSum s 0 row 71 + rowsSum (s + 1) rows
end K1_13_2_3_4
end
section
namespace K1_13_2_3_7
open K1_13_2 K1_13_2_3
def valuePower (s j : ℕ) : ℕ := 4650 - s - 4 * j
def witness (i : BlockIndex) : Powers := ⟨valuePower i.1.val i.2.val, 0, 0⟩
def fastDen (u : ℤ) : ℤ :=
  if u < 0 then 0 else u * (u * (2 * u + 21) + 66) / 72 + 1
def fastCum (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    if v ≤ d then fastDen v else
      let a := v - d
      let first := fastDen v - fastDen (a - 1) - fastDen (a - 2) -
        fastDen (a - 3)
      if v ≤ 2 * d + 2 then first else
        let b := v - 2 * d
        first + fastDen (b - 3) + fastDen (b - 4) + fastDen (b - 5)
def signedKernel (d j h : ℤ) : ℤ :=
  let low := 1649 - j
  let balance := h - (1650 - j) + d
  if balance < 0 then fastCum d 1650 - fastCum d low else
    let removed := min d (balance / 4) + 1
    fastCum d 1650 - fastCum d h + fastCum (d - removed) (h - 3 * removed) -
      fastCum (d - removed) low
def rangeSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rangeSum f n + f n
end K1_13_2_3_7
end
section
namespace K1_14_2_2_7
noncomputable section
open K1_14 K1_14_2 K1_14_2_2
open scoped Classical
def cutComponents (I : Ideal Ambient) (P : Jet) : Finset (Ideal Ambient) :=
  (I ⊔ Ideal.span {toJet P}).minimalPrimesFinset
def ConstantSeed (Q : Ideal Ambient) : Prop :=
  ∀ i : Fin 2, IsAlgebraic FX
    (Ideal.Quotient.mk Q (MvPolynomial.X (Fin.castLE (by decide : 2 ≤ 4) i)))
def movingComponents (I : Ideal Ambient) (P : Jet) : Finset (Ideal Ambient) :=
  (cutComponents I P).filter fun Q => ¬ ConstantSeed Q
def constantComponents (I : Ideal Ambient) (P : Jet) : Finset (Ideal Ambient) :=
  (cutComponents I P).filter ConstantSeed
end
end K1_14_2_2_7
end

end Merged_Fast049

end Merged6967_Fast049

section Merged6967_R6960Front6960ListCells0
set_option Elab.async false


set_option Elab.async false

-- merged module R6960Front6960ListBank
section Merged_R6960Front6960ListBank

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Front6960ListBank
open CJ1 (Block total total_eq_sum entryZ)
open CJ0 (Jet blockRows blockCols blockMatrix)
open scoped BigOperators
def source : CJ0.Source := ⟨57,78,24,10,CJ0.fullBox 78 24 10⟩
def rowLo (q u h : ℕ) := u + 2*q + h + 1 - 81
def rowHi (q u h : ℕ) := min (q + 1 - h) (u + 2*q + h + 1 - 24)
def rowLen (q u h : ℕ) := rowHi q u h - rowLo q u h
def colLo (u b : ℕ) := (25 - (u+b)) / 2
def colHi (q b : ℕ) := min 11 (min (q-b+1) ((24-b)/2+1))
def colLen (q u b : ℕ) := colHi q b - colLo u b
abbrev Row (q u : ℕ) := (h : Fin (q+1)) × Fin (rowLen q u h)
abbrev Col (q u : ℕ) := (b : Fin (min q 24 + 1)) × Fin (colLen q u b)
def rowAt (q u h i : ℕ) : CJ0.Jet :=
  let d := rowLo q u h + i
  ⟨q - (h+d), d, h⟩
def rowJet (q u : ℕ) (r : Row q u) : CJ0.Jet := rowAt q u r.1 r.2
def colAt (q u b i : ℕ) : CJ0.Jet :=
  let c := colLo u b + i
  ⟨c, b, q - (b+c)⟩
def colJet (q u : ℕ) (s : Col q u) : CJ0.Jet := colAt q u s.1 s.2
def packet (q u : ℕ) : Matrix (Row q u) (Col q u) (ZMod CJ0.p) :=
  fun r s => CJ0.blockEntry (rowJet q u r) (colJet q u s)
def rows (q u : ℕ) := total (rowLen q u) (q+1)
def cols (q u : ℕ) := total (colLen q u) (min q 24 + 1)
def nominal (q u : ℕ) := min (rows q u) (cols q u)
def outer (onRows : Bool) (q : ℕ) := if onRows then q+1 else min q 24+1
def fiber (onRows : Bool) (q u : ℕ) := if onRows then rowLen q u else colLen q u
abbrev Axis (onRows : Bool) (q u : ℕ) :=
  (i : Fin (outer onRows q)) × Fin (fiber onRows q u i)
def orientedEntry (onRows : Bool) (q u i k b t : ℕ) : ℤ :=
  if onRows then entryZ (rowAt q u b t) (colAt q u i k)
  else entryZ (rowAt q u i k) (colAt q u b t)
def dot (q u : ℕ) (z : Block) (j i k : ℕ) : ℤ :=
  total (fun b => total (fun t =>
    let w := z.coeff j b t
    if w = 0 then 0 else orientedEntry z.bank.onRows q u i k b t * (w : ℤ))
    (fiber z.bank.onRows q u b)) (outer z.bank.onRows q)
def Dots (q u : ℕ) (z : Block) : Prop :=
  ∀ j < z.free.length, ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
def VectorDots (q u : ℕ) (z : Block) (j : ℕ) : Prop :=
  ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
private theorem row_bounds (q u c d h : ℕ)
    (hr : (⟨c,d,h⟩ : Jet) ∈ blockRows 57 q ((u : ℤ)-24)) :
    h < q+1 ∧ rowLo q u h ≤ d ∧ d < rowHi q u h ∧ q-(h+d) = c := by
  simp only [blockRows, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_singleton, Jet.v, Jet.b, Jet.c, Jet.a, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hr
  unfold rowLo rowHi
  omega
private theorem col_bounds (q u c b a : ℕ)
    (hs : (⟨c,b,a⟩ : Jet) ∈ blockCols source q ((u : ℤ)-24)) :
    b < min q 24 + 1 ∧ colLo u b ≤ c ∧ c < colHi q b ∧ q-(b+c) = a := by
  change (⟨c,b,a⟩ : Jet) ∈ (CJ0.fullBox 78 24 10).filter _ at hs
  rw [Finset.mem_filter, CJ0.mem_fullBox (by decide) (by decide)] at hs
  simp only [Jet.q, Jet.v, Jet.a, Jet.b, Jet.c, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hs
  unfold colLo colHi
  omega
private def rowIndex (q u : ℕ) :
    ↥(blockRows 57 q ((u : ℤ)-24)) → Row q u
  | ⟨⟨c,d,h⟩, hr⟩ =>
    let H := row_bounds q u c d h hr
    ⟨⟨h,H.1⟩, ⟨d-rowLo q u h, by
      change d - rowLo q u h < rowHi q u h - rowLo q u h
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private def colIndex (q u : ℕ) :
    ↥(blockCols source q ((u : ℤ)-24)) → Col q u
  | ⟨⟨c,b,a⟩, hs⟩ =>
    let H := col_bounds q u c b a hs
    ⟨⟨b,H.1⟩, ⟨c-colLo u b, by
      change c - colLo u b < colHi q b - colLo u b
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private theorem rowJet_index (q u : ℕ) (r : ↥(blockRows 57 q ((u : ℤ)-24))) :
    rowJet q u (rowIndex q u r) = r.val := by
  rcases r with ⟨⟨c,d,h⟩,hr⟩
  obtain ⟨_, hlo, _, hc⟩ := row_bounds q u c d h hr
  change (⟨q-(h+(rowLo q u h+(d-rowLo q u h))),rowLo q u h+(d-rowLo q u h),h⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, hc]
private theorem colJet_index (q u : ℕ) (s : ↥(blockCols source q ((u : ℤ)-24))) :
    colJet q u (colIndex q u s) = s.val := by
  rcases s with ⟨⟨c,b,a⟩,hs⟩
  obtain ⟨_, hlo, _, ha⟩ := col_bounds q u c b a hs
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, ha]
theorem block_rank_le (q u : ℕ) :
    (blockMatrix source q ((u : ℤ)-24)).rank ≤ (packet q u).rank := by
  have he : blockMatrix source q ((u : ℤ)-24) =
      (packet q u).submatrix (rowIndex q u) (colIndex q u) := by
    ext r s
    change CJ0.blockEntry r.val s.val =
      CJ0.blockEntry (rowJet q u (rowIndex q u r)) (colJet q u (colIndex q u s))
    exact congrArg₂ CJ0.blockEntry (rowJet_index q u r).symm (colJet_index q u s).symm
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _
theorem card_row (q u : ℕ) : Fintype.card (Row q u) = rows q u := by
  simp only [Row, Fintype.card_sigma, Fintype.card_fin, rows, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
theorem card_col (q u : ℕ) : Fintype.card (Col q u) = cols q u := by
  simp only [Col, Fintype.card_sigma, Fintype.card_fin, cols, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
theorem rank_le_nominal (q u : ℕ) : (packet q u).rank ≤ nominal q u := by
  exact le_min ((packet q u).rank_le_card_height.trans_eq (card_row q u))
    ((packet q u).rank_le_card_width.trans_eq (card_col q u))
open CJ1 (fastChoose right_witness)
open scoped BigOperators
local instance : Fact (Nat.Prime CJ0.p) := ⟨KoalaBear.is_prime⟩
def Guard (q u : ℕ) (z : Block) : Prop :=
  total (fiber z.bank.onRows q u) (outer z.bank.onRows q) ≤ z.cap + z.free.length ∧
  (∀ j : Fin z.free.length,
    z.free[j].1 < outer z.bank.onRows q ∧
    z.free[j].2 < fiber z.bank.onRows q u z.free[j].1) ∧
  ∀ j k : Fin z.free.length, z.coeff k z.free[j].1 z.free[j].2 = if j = k then 1 else 0
instance (q u : ℕ) (z : Block) : Decidable (Guard q u z) := by
  unfold Guard
  infer_instance
private theorem entryZ_cast (r c : CJ0.Jet) : (entryZ r c : ZMod CJ0.p) = CJ0.blockEntry r c := by
  unfold entryZ CJ0.blockEntry
  split <;> simp [fastChoose, ← Nat.choose_eq_descFactorial_div_factorial, *]
private def oriented (side : Bool) (q u : ℕ) :
    Matrix (Axis (!side) q u) (Axis side q u) (ZMod CJ0.p) :=
  fun r c => (orientedEntry side q u r.1 r.2 c.1 c.2 : ZMod CJ0.p)
private theorem oriented_rank (side : Bool) (q u : ℕ) :
    (oriented side q u).rank = (packet q u).rank := by
  cases side
  · have he : oriented false q u = packet q u := by
      ext r c
      exact entryZ_cast _ _
    rw [he]
    rfl
  · have he : oriented true q u = (packet q u).transpose := by
      ext r c
      exact entryZ_cast _ _
    rw [he]
    exact Matrix.rank_transpose _
private def vectors (q u : ℕ) (z : Block) :
    Matrix (Axis z.bank.onRows q u) (Fin z.free.length) (ZMod CJ0.p) :=
  fun c j => (z.coeff j c.1 c.2 : ZMod CJ0.p)
private theorem sum_axis {α : Type*} [AddCommMonoid α] (side : Bool) (q u : ℕ) (f : ℕ → ℕ → α) :
    (∑ x : Axis side q u, f x.1 x.2) =
      total (fun i => total (f i) (fiber side q u i)) (outer side q) := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma, total_eq_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [total_eq_sum, ← Fin.sum_univ_eq_sum_range]
private theorem mul_eq_dot (q u : ℕ) (z : Block) (r : Axis (!z.bank.onRows) q u)
    (j : Fin z.free.length) :
    (oriented z.bank.onRows q u * vectors q u z) r j = (dot q u z j r.1 r.2 : ZMod CJ0.p) := by
  rw [Matrix.mul_apply, dot, ← sum_axis, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  change (orientedEntry z.bank.onRows q u r.1 r.2 c.1 c.2 : ZMod CJ0.p) * (z.coeff j c.1 c.2 : ZMod CJ0.p) = _
  by_cases hh : z.coeff j c.1 c.2 = 0 <;> simp [hh]
theorem rank_of_dots {q u : ℕ} {z : Block} (hg : Guard q u z) (hd : Dots q u z) :
    (packet q u).rank ≤ z.cap := by
  obtain ⟨hsize, hfree, hid⟩ := hg
  let f (j : Fin z.free.length) : Axis z.bank.onRows q u :=
    ⟨⟨z.free[j].1,(hfree j).1⟩, ⟨z.free[j].2,(hfree j).2⟩⟩
  have hm : oriented z.bank.onRows q u * vectors q u z = 0 := by
    ext r j
    rw [mul_eq_dot, Matrix.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero (hd j j.isLt r.1 r.1.isLt r.2 r.2.isLt)
  have hi : (vectors q u z).submatrix f id = 1 := by
    ext j k
    change (z.coeff k z.free[j].1 z.free[j].2 : ZMod CJ0.p) = _
    rw [hid]
    by_cases h : j = k <;> simp [Matrix.one_apply, h]
  have hr := right_witness (oriented z.bank.onRows q u) (vectors q u z) f hm hi
  have hc (side : Bool) :
      Fintype.card (Axis side q u) = total (fiber side q u) (outer side q) := by
    cases side
    · exact card_col q u
    · exact card_row q u
  rw [hc, oriented_rank] at hr
  exact Nat.le_of_add_le_add_right (hr.trans hsize)

namespace Fast
open CJ1 (Block total)
open CJ6.Packed
def point (row : Bool) (q u i k : ℕ) : CJ0.Jet := if row then rowAt q u i k else colAt q u i k
def inputs (q u : ℕ) (z : Block) (j : ℕ) : List Input :=
  axisList (outer z.bank.onRows q) (fiber z.bank.onRows q u)
    (fun i k => (point z.bank.onRows q u i k, z.coeff j i k))
def outputs (q u : ℕ) (z : Block) : List CJ0.Jet :=
  axisList (outer (!z.bank.onRows) q) (fiber (!z.bank.onRows) q u) (point (!z.bank.onRows) q u)
private theorem dot_eq (q u : ℕ) (z : Block) (j i k : ℕ) :
    dot q u z j i k = ((inputs q u z j).map (intTerm z.bank.onRows (point (!z.bank.onRows) q u i k))).sum := by
  rw [inputs, CJ6.Packed.sum_axis, dot]
  congr 1
  funext b
  congr 1
  funext t
  by_cases h : z.coeff j b t = 0
  · simp [h, intTerm]
  · cases hs : z.bank.onRows <;> simp [h, intTerm, point, orientedEntry]
theorem vector {q u : ℕ} {z : Block} {j : ℕ} (bands : List Band) (bs : List Bucket)
    (hi : (inputs q u z j).all (fun v => v.1.q == q) = true)
    (hc : (outputs q u z).all (covers z.bank.onRows q bands) = true)
    (hp : pack z.bank.onRows q (inputs q u z j) = bs)
    (hb : bands.all (checkBand z.bank.onRows bs) = true) : VectorDots q u z j := by
  intro i hᵢ k hₖ
  rw [dot_eq]
  subst bs
  apply int_sum_zero hi _ hb
  apply List.all_eq_true.mp hc
  exact mem_axis hᵢ hₖ

def vectorOK (q u : ℕ) (z : Block) (j : ℕ) (bands : List Band) : Bool :=
  let side := z.bank.onRows
  let xs := inputs q u z j
  xs.all (fun v => v.1.q == q) && (outputs q u z).all (covers side q bands) &&
    bands.all (checkBand side (pack side q xs))

theorem cell {q u : ℕ} {z : Block} (bands : List Band) (guard : Guard q u z)
    (cert : (List.range z.free.length).all (fun j => vectorOK q u z j bands) = true) :
    (CJ0.blockMatrix source q ((u : ℤ)-24)).rank ≤ z.cap := by
  apply (block_rank_le _ _).trans
  apply rank_of_dots guard
  intro j hj
  have h := List.all_eq_true.mp cert j (List.mem_range.mpr hj)
  simp only [vectorOK, Bool.and_eq_true] at h
  exact vector bands _ h.1.1 h.1.2 rfl h.2

def bands (xs : List (ℕ × ℕ × ℕ)) : List Band :=
  xs.map fun (a,lo,n) => (a, List.range' lo n)

end Fast
end Front6960ListBank

end Merged_R6960Front6960ListBank

-- merged module R6960Front6960ListCells0
section Merged_R6960Front6960ListCells0

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def allowance_0 (u : ℕ) : ℕ :=
  nominal 0 u

private theorem bound_0 (u : ℕ) :
    (CJ0.blockMatrix source 0 ((u : ℤ)-24)).rank ≤ allowance_0 u := by
  unfold allowance_0
  exact (block_rank_le 0 _).trans (rank_le_nominal 0 _)

theorem grade_0 : (∑ u ∈ Finset.range (81-0), (CJ0.blockMatrix source 0 ((u : ℤ)-24)).rank) ≤ 57 := by
  refine (Finset.sum_le_sum fun u _ => bound_0 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_0)]
  decide +kernel

private def allowance_1 (u : ℕ) : ℕ :=
  nominal 1 u

private theorem bound_1 (u : ℕ) :
    (CJ0.blockMatrix source 1 ((u : ℤ)-24)).rank ≤ allowance_1 u := by
  unfold allowance_1
  exact (block_rank_le 1 _).trans (rank_le_nominal 1 _)

theorem grade_1 : (∑ u ∈ Finset.range (81-1), (CJ0.blockMatrix source 1 ((u : ℤ)-24)).rank) ≤ 168 := by
  refine (Finset.sum_le_sum fun u _ => bound_1 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_1)]
  decide +kernel

private def allowance_2 (u : ℕ) : ℕ :=
  nominal 2 u

private theorem bound_2 (u : ℕ) :
    (CJ0.blockMatrix source 2 ((u : ℤ)-24)).rank ≤ allowance_2 u := by
  unfold allowance_2
  exact (block_rank_le 2 _).trans (rank_le_nominal 2 _)

theorem grade_2 : (∑ u ∈ Finset.range (81-2), (CJ0.blockMatrix source 2 ((u : ℤ)-24)).rank) ≤ 330 := by
  refine (Finset.sum_le_sum fun u _ => bound_2 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_2)]
  decide +kernel

private def allowance_3 (u : ℕ) : ℕ :=
  nominal 3 u

private theorem bound_3 (u : ℕ) :
    (CJ0.blockMatrix source 3 ((u : ℤ)-24)).rank ≤ allowance_3 u := by
  unfold allowance_3
  exact (block_rank_le 3 _).trans (rank_le_nominal 3 _)

theorem grade_3 : (∑ u ∈ Finset.range (81-3), (CJ0.blockMatrix source 3 ((u : ℤ)-24)).rank) ≤ 540 := by
  refine (Finset.sum_le_sum fun u _ => bound_3 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_3)]
  decide +kernel

private def allowance_4 (u : ℕ) : ℕ :=
  nominal 4 u

private theorem bound_4 (u : ℕ) :
    (CJ0.blockMatrix source 4 ((u : ℤ)-24)).rank ≤ allowance_4 u := by
  unfold allowance_4
  exact (block_rank_le 4 _).trans (rank_le_nominal 4 _)

theorem grade_4 : (∑ u ∈ Finset.range (81-4), (CJ0.blockMatrix source 4 ((u : ℤ)-24)).rank) ≤ 795 := by
  refine (Finset.sum_le_sum fun u _ => bound_4 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_4)]
  decide +kernel

private def allowance_5 (u : ℕ) : ℕ :=
  nominal 5 u

private theorem bound_5 (u : ℕ) :
    (CJ0.blockMatrix source 5 ((u : ℤ)-24)).rank ≤ allowance_5 u := by
  unfold allowance_5
  exact (block_rank_le 5 _).trans (rank_le_nominal 5 _)

theorem grade_5 : (∑ u ∈ Finset.range (81-5), (CJ0.blockMatrix source 5 ((u : ℤ)-24)).rank) ≤ 1092 := by
  refine (Finset.sum_le_sum fun u _ => bound_5 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_5)]
  decide +kernel

private def allowance_6 (u : ℕ) : ℕ :=
  nominal 6 u

private theorem bound_6 (u : ℕ) :
    (CJ0.blockMatrix source 6 ((u : ℤ)-24)).rank ≤ allowance_6 u := by
  unfold allowance_6
  exact (block_rank_le 6 _).trans (rank_le_nominal 6 _)

theorem grade_6 : (∑ u ∈ Finset.range (81-6), (CJ0.blockMatrix source 6 ((u : ℤ)-24)).rank) ≤ 1428 := by
  refine (Finset.sum_le_sum fun u _ => bound_6 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_6)]
  decide +kernel

private def allowance_7 (u : ℕ) : ℕ :=
  nominal 7 u

private theorem bound_7 (u : ℕ) :
    (CJ0.blockMatrix source 7 ((u : ℤ)-24)).rank ≤ allowance_7 u := by
  unfold allowance_7
  exact (block_rank_le 7 _).trans (rank_le_nominal 7 _)

theorem grade_7 : (∑ u ∈ Finset.range (81-7), (CJ0.blockMatrix source 7 ((u : ℤ)-24)).rank) ≤ 1800 := by
  refine (Finset.sum_le_sum fun u _ => bound_7 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_7)]
  decide +kernel

private def allowance_8 (u : ℕ) : ℕ :=
  nominal 8 u

private theorem bound_8 (u : ℕ) :
    (CJ0.blockMatrix source 8 ((u : ℤ)-24)).rank ≤ allowance_8 u := by
  unfold allowance_8
  exact (block_rank_le 8 _).trans (rank_le_nominal 8 _)

theorem grade_8 : (∑ u ∈ Finset.range (81-8), (CJ0.blockMatrix source 8 ((u : ℤ)-24)).rank) ≤ 2205 := by
  refine (Finset.sum_le_sum fun u _ => bound_8 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_8)]
  decide +kernel

private def allowance_9 (u : ℕ) : ℕ :=
  nominal 9 u

private theorem bound_9 (u : ℕ) :
    (CJ0.blockMatrix source 9 ((u : ℤ)-24)).rank ≤ allowance_9 u := by
  unfold allowance_9
  exact (block_rank_le 9 _).trans (rank_le_nominal 9 _)

theorem grade_9 : (∑ u ∈ Finset.range (81-9), (CJ0.blockMatrix source 9 ((u : ℤ)-24)).rank) ≤ 2640 := by
  refine (Finset.sum_le_sum fun u _ => bound_9 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_9)]
  decide +kernel

end Front6960ListBank

end Merged_R6960Front6960ListCells0

end Merged6967_R6960Front6960ListCells0
