import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.FrontBranch3
import ProximityPrize.SubmissionLower.UpperBranch3

set_option Elab.async false

-- merged module GoldBranch6N5
section Merged_GoldBranch6N5
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_5
noncomputable section
open P3 (K I)
open P3_6 (TrueWeightLE  taylorLength)
open K1_13 (Row indexDegree)
open K1_13_5 (NodeFamily lowBox liftedBox graphBox mixed3)
open scoped BigOperators Polynomial
def Whole (f : Row 3) : Prop :=
  f ∣ K1_13_5.compatibilityNumerator f (taylorLength - 3)
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
end P3_6_5
end
section
namespace P3_6_5_1
noncomputable section
open K1_13 (Geom Row Shape atJet)
open K1_13_5 (RegularAt compatibilityNumerator graphBox liftedBox separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericRow graph graphPoint
  InLiftedBox RepresentsOnGraph jetPoint regularLocus extendedAtJet)
open P3_6 (taylorLength physicalDegree)
open P3_6_5 (Whole mixedBudget)
open Polynomial
open scoped BigOperators
abbrev Coefficients := Fin taylorLength → GeometricX
abbrev CoefficientIdeal := Ideal (GeoRow taylorLength)
abbrev CurveIndex (n : ℕ) := Fin n × Ideal (GeoRow 3)
def coefficientPoint (S : (Polynomial Geom)) : Coefficients :=
  fun j => algebraMap Geom GeometricX (S.coeff j)
def oldCut (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 3)
def oldNext (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 2)
open K1_13_5_4_1 (compatibility_degree)
def oldCutIdeal (f : Row 3) : Ideal (GeoRow 3) :=
  Ideal.span {genericRow f, genericRow (oldCut f)}
def properComponents {n : ℕ} (f : Fin n → Row 3) : Finset (CurveIndex n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Whole (f i) then ∅ else
      ((oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i)))).image
        (fun P => (i, P))
def componentLength (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ∞ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let A := Localization.AtPrime P
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A))
  else 0
def nextCutLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ regularLocus f P ∧ MvPolynomial.eval y (genericRow (oldNext f)) = 0}
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
  actual : ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree → RegularAt 2 f S →
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
end
end P3_6_5_1
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace P3_6_5
noncomputable section
open P3 (I K node)
open K1_13_5 (NodeCapacity NodeFamily)
open Polynomial ProximityPrize.Benchmark
open scoped BigOperators
end
end P3_6_5
end
section
namespace P3_6_5_1
noncomputable section
open P3_6 (physicalDegree taylorLength)
open K1_13 (Geom Row atJet indexDegree)
open K1_13_5 (RegularAt separant graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow InLiftedBox RepresentsOnGraph graph genericCoeff genericRow jetPoint)
open K1_13_5_4_1 (liftRaw liftSep graphRaw thirdVelocityNumerator thirdNumerator
  padJet jetNumerator centre partialFlow_lift generic_graph eval_genericRow graphPoint_of_actual)
open K1_13_7_1 (weight_const_mul_le weight_X_le)
open MvPolynomial
open Polynomial (hasseDeriv)
open scoped BigOperators Polynomial
open K1_13_5_4_1_1 (mul_bound partialFlow_bound liftSep_eq liftedStep_bound generic_bound totalWeight indexWeight topWeight heightWeight lift_weight fits fits_lifted)
open K1_13_5_4_1_2 (represents)
open K1_13_5_4_1 (atJet_padJet taylor_coefficients_aux genericCoeff_ne_zero third_atJet_zero actual_zero_of_represents)
local notation "W" => weightedTotalDegree
end
end P3_6_5_1
end
section
namespace P3_6_5
noncomputable section
open P3 (K)
open P3_6 ( taylorLength )
open K1_13 (Row Geom embed extend atJet)
open K1_13_5 (FirstRow RegularAt NodeFamily mixed3 lowBox graphBox liftedBox)
open Polynomial
open scoped BigOperators
end
end P3_6_5
end
section
set_option autoImplicit false
namespace P3_6_5_1_1
noncomputable section
open K1_13 (Row)
open K1_13_5 (graphBox liftedBox separant)
open K1_13_5_4 (InLiftedBox GeoRow GeometricX genericRow)
open K1_13_5_4_2 (JetPoint ExponentSpace boxExponents graphLocus graphCurve capBody mixedVolume4)
open P3_6 (taylorLength)
open P3_6_5 (Whole)
open P3_6_5_1 (oldCutIdeal)
open MvPolynomial
def factorCurves (f : Row 3) : Finset (Ideal (GeoRow 3)) := by
  classical
  exact if Whole f then ∅ else
    (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))
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
end
end P3_6_5_1_1
end
section
set_option autoImplicit false
namespace P3_6_5_1_1
noncomputable section
open K1_13 (Row Geom Shape)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericCoeff_injective genericRow
  liftRow regularLocus graphPoint)
open K1_13_5_4_2 (boxExponents graphCurve eval_represents_iff)
open P3_6 (taylorLength)
open P3_6_5 (Whole)
open P3_6_5_1 (oldCut oldCutIdeal properComponents CurveIndex componentLength nextCutLocus
  oldNext LiftedChart)
open MvPolynomial RingTheory.Sequence
open scoped BigOperators Polynomial
open K1_13_5_4_2_1 (quotient_regular_iff graph_dimension)
open K1_13_5_4_2 (graphPoint_injective)
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end P3_6_5_1_1
end
section
set_option autoImplicit false
namespace P3_6_5_1_1_2
noncomputable section
open K1_13 (Row)
open K1_13_5 (lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow graph graphIdeal)
open P3_6_5_1 (LiftedChart oldCutIdeal)
open K1_13_5_4_2_3 (OpenRing onOpen onOpen_kills onOpen_isUnit onOpen_hom_ext
  openLift openLift_onOpen sep liftedSep)
open MvPolynomial
open K1_13_5_4_2_3 (three_isUnit graph_coord_unique represents_vanish)
def threeCut (f : Row 3) (T : LiftedChart f) : Ideal (GeoRow 4) :=
  graphIdeal f ⊔ Ideal.span {T.cut}
abbrev OldOpen (f : Row 3) := OpenRing (oldCutIdeal f) (sep f)
abbrev GraphOpen (f : Row 3) (T : LiftedChart f) := OpenRing (threeCut f T) (liftedSep f)
abbrev oldMap (f : Row 3) := onOpen (oldCutIdeal f) (sep f)
abbrev graphMap (f : Row 3) (T : LiftedChart f) := onOpen (threeCut f T) (liftedSep f)
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
end P3_6_5_1_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace P3_6_5_1_2
noncomputable section
open K1_13 (Row)
open K1_13_5 (compatibilityNumerator separant tangentNumerator)
open K1_13_5_4 (GeoRow genericRow genericCoeff genericCoeff_injective)
open K1_13_5_4_3 (TangentStable)
open K1_13_5_4_3_1 (tangentNumerator_add tangentNumerator_mul)
open P3_6 (taylorLength)
open P3_6_5 (Whole)
open P3_6_5_1 (oldCut oldNext oldCutIdeal componentLength )
open Polynomial
open K1_13_5_4_3_1 (flat_rowToGeo rowToGeo_eq tangent_self)
open K1_13_5_4_3_3 (generic_cut_regular)
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end P3_6_5_1_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P3_6_5_2
noncomputable section
open K1_13 (Geom)
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open P3_6 (physicalDegree)
open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_5_5_2_1 (monic_chart_aux)
open K1_13_5_5_2_1 (commonFactor_monic trimmedValue_monic trimmedValue_dvd)
open P0_9_5_2 (eval_divisions)
end
end P3_6_5_2
end

end Merged_GoldBranch6N5

-- merged module UpperBranch7
section Merged_UpperBranch7
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_7
noncomputable section
open Polynomial MvPolynomial
open P1 (I K node p)
open K1_14 (FX L seedEmbedding)
open K1_14_6 (Biform ClosedField rootPoint)
abbrev box (a b : ℕ) := restrictBidegree (Fin 2) FX a b
structure CRTChart (w : ℕ) where
  denominator : Biform
  numerator : (Polynomial Biform)
  degree_numerator : numerator.natDegree < 2 * w
  bound_denominator : denominator ∈ box 0 (2 * w)
  bound_numerator : ∀ j, numerator.coeff j ∈ box 0 (2 * w)
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open P1 (K I node agreement blockLength)
open K1_14 (FX)
open K1_14_6 (Biform ClosedField rootPoint)
open K1_14_6 (card_le_sum_cover)
open K1_14_6_2 (closedPoint eval_extend)
end
end P1_7_7
end
section
namespace P1_7_7
open P1 (HighBand agreement blockLength)
open P1_7 (degreeAt   quotientOrder   ceilRatio )
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
open P1 (K)
open P1_7 (regularRoot)
open K1_14 (Equation FX SeedBound atMark)
open K1_14_6 (ClosedField)
open K1_14_6_2 (closedPoint)
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open MvPolynomial
open K1_14_6 (ClosedField)
open scoped BigOperators
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open Polynomial MvPolynomial
open P1 (AnchorModel AnchoredFamily HighBand I K agreement node p)
open P1_7 (AdjacentChart GradeIndex  Reduced regularRoot grades )
open K1_14 (Equation FX L SeedBound seedEmbedding)
open scoped BigOperators
end
end P1_7_7
end
section
namespace P1_7_7_1
noncomputable section
open Polynomial Module K1_14_1
open K1_14 (L)
open scoped Polynomial BigOperators
open K1_14_1_1 (quotientBasis mulMatrix mulMatrix_entry mulMatrix_specialize mulMatrix_det_ne_zero eval_map_constants)
end
end P1_7_7_1
end
section
namespace P1_7_7_1
noncomputable section
open P1 (AnchorModel AnchoredFamily K p)
open P1_7 (AdjacentChart)
open K1_14 (L FX liftPoly seedEmbedding)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open K1_14_6 (Biform rootPoint)
open P1_7_7 (CRTChart box)
open MvPolynomial (mem_restrictBidegree mem_restrictBidegree_mono mul_mem_restrictBidegree)
open Polynomial
open scoped Polynomial BigOperators
end
end P1_7_7_1
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open Polynomial
open scoped BigOperators
end
end P1_7_7_2
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open P1 (K p)
open K1_14 (Equation FX SeedBound seedEmbedding atX liftPoly)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant     cleared
  markEval eval_cleared derivativeAt)
open P1_7_7 (box)
open MvPolynomial
open scoped Polynomial
local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))
end
end P1_7_7_2
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open P1 (I K node p)
open P1_7 (regularRoot)
open P1_7_7 (CRTChart box  )
open K1_14 (L FX seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant   markEval eval_flatten )
open Polynomial MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
end
end P1_7_7_2
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial
open scoped BigOperators
end
end P1_7_7_3
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial Filter
variable {k σ : Type*} [Field k]
end
end P1_7_7_3
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial
open scoped BigOperators
end
end P1_7_7_3
end

end Merged_UpperBranch7

-- merged module GoldBranch7
section Merged_GoldBranch7
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7
open P3 (HighBand)
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
def terminal : HighBand → Bank
  | .h2274 => ⟨⟨6600,9172,1952,211000⟩,0x1e372113d00000,0xae27f29bc6cc⟩
  | .h2294 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,946⟩,0xc4fd80000,22832869⟩
def stages : HighBand → List Stage
  | .h2274 =>
    [⟨0, ⟨⟨76,105,23,862⟩,0x345100000,3635193⟩, ⟨⟨359,499,105,11883⟩,0x14006680000,0x64b8343e⟩⟩,
     ⟨1, ⟨⟨80,111,24,1024⟩,0x3c7300000,4477423⟩, ⟨⟨356,495,104,14432⟩,0x137d3580000,0x616d5567⟩⟩,
     ⟨2, ⟨⟨90,125,27,1032⟩,0x558480000,7136131⟩, ⟨⟨391,543,114,15483⟩,0x19c04900000,0x8cc85625⟩⟩,
     ⟨3, ⟨⟨99,137,30,1063⟩,0x722180000,10343855⟩, ⟨⟨429,596,126,16288⟩,0x222a41c0000,0xcd26d8f5⟩⟩,
     ⟨4, ⟨⟨106,147,32,1146⟩,0x8b45c0000,13594640⟩, ⟨⟨483,671,142,16629⟩,0x30bbe980000,0x14954ceae⟩⟩,
     ⟨5, ⟨⟨115,159,35,1187⟩,0xb24d00000,18685854⟩, ⟨⟨521,724,153,17608⟩,0x3d118e80000,0x1bd78704c⟩⟩,
     ⟨6, ⟨⟨114,158,34,1481⟩,0xab2c00000,17916156⟩, ⟨⟨585,813,172,18018⟩,0x56714d40000,0x2c405b86b⟩⟩,
     ⟨10, ⟨⟨142,197,43,1768⟩,0x14bde80000,43318982⟩, ⟨⟨666,926,195,23938⟩,0x7f04c380000,0x4a1c95ad2⟩⟩,
     ⟨16, ⟨⟨195,270,60,1985⟩,0x35dfb80000,0x921d91e⟩, ⟨⟨869,1208,255,30502⟩,0x11a29c000000,0xd6957b128⟩⟩,
     ⟨18, ⟨⟨236,327,73,1859⟩,0x5f7bb40000,0x139cbdb4⟩, ⟨⟨1028,1429,302,30599⟩,0x1d31d5640000,0x1a41f86f48⟩⟩,
     ⟨24, ⟨⟨234,324,73,2988⟩,0x5daf840000,0x130a6f27⟩, ⟨⟨1267,1761,373,36637⟩,0x36b2a6f80000,0x3c9863ad3c⟩⟩,
     ⟨32, ⟨⟨261,362,81,5153⟩,0x813b280000,0x1d6fb003⟩, ⟨⟨1466,2038,431,46668⟩,0x54997c200000,0x6c7e6759da⟩⟩,
     ⟨36, ⟨⟨250,347,75,47631⟩,0x6ece680000,0x18392b4c⟩, ⟨⟨1215,1689,356,84012⟩,0x3011c0200000,0x33175ef1d6⟩⟩,
     ⟨54, ⟨⟨444,615,137,5303⟩,0x274cf340000,0xf2191e37⟩, ⟨⟨2194,3050,645,71333⟩,0x11b429fac0000,0x21f78372cbf⟩⟩,
     ⟨81, ⟨⟨680,942,212,6492⟩,0x8dc48280000,0x538e63a35⟩, ⟨⟨3385,4705,995,96391⟩,0x40f5ebab00000,0xc029d47a706⟩⟩,
     ⟨135, ⟨⟨998,1383,310,11820⟩,0x1bdf3ba00000,0x181eba870b⟩, ⟨⟨5282,7341,1556,154211⟩,0xf7195a1840000,0x4741ba66013a⟩⟩]
  | .h2294 =>
    [⟨0, ⟨⟨73,101,22,878⟩,0x2e5640000,3108650⟩, ⟨⟨352,489,103,10763⟩,0x12dda700000,0x5cfd94a5⟩⟩,
     ⟨1, ⟨⟨78,108,24,1006⟩,0x392740000,4103823⟩, ⟨⟨345,480,101,13083⟩,0x11c61f80000,0x564a51c0⟩⟩,
     ⟨2, ⟨⟨86,119,26,1061⟩,0x4b3780000,5931589⟩, ⟨⟨385,535,112,13830⟩,0x188bf840000,0x84679137⟩⟩,
     ⟨3, ⟨⟨94,130,29,1105⟩,0x633bc0000,8531244⟩, ⟨⟨411,572,120,15084⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
     ⟨4, ⟨⟨102,141,31,1166⟩,0x7cec00000,11621252⟩, ⟨⟨438,609,128,16326⟩,0x2436d340000,0xde912dc3⟩⟩,
     ⟨5, ⟨⟨108,150,33,1260⟩,0x948040000,14840297⟩, ⟨⟨522,726,153,15779⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
     ⟨6, ⟨⟨108,149,33,1589⟩,0x948040000,14526868⟩, ⟨⟨570,792,167,16543⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
     ⟨10, ⟨⟨142,197,43,1679⟩,0x14bde80000,43318982⟩, ⟨⟨696,968,204,20721⟩,0x910a3980000,0x5884788a7⟩⟩,
     ⟨16, ⟨⟨163,226,50,3079⟩,0x1f8a780000,75401397⟩, ⟨⟨851,1183,249,27859⟩,0x108708880000,0xc4f2a7606⟩⟩,
     ⟨18, ⟨⟨221,306,68,1918⟩,0x4e346c0000,0xf032b8c⟩, ⟨⟨952,1324,279,29044⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
     ⟨24, ⟨⟨212,294,65,3972⟩,0x44e9c40000,0xcc1a54f⟩, ⟨⟨1115,1550,329,35921⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
     ⟨32, ⟨⟨261,362,82,4794⟩,0x826c0c0000,0x1db6eefa⟩, ⟨⟨1463,2034,430,42399⟩,0x54106e900000,0x6b9d823520⟩⟩,
     ⟨36, ⟨⟨246,341,75,46786⟩,0x6ae4280000,0x16e7d3b2⟩, ⟨⟨1220,1696,357,67968⟩,0x309db61c0000,0x33e3754396⟩⟩,
     ⟨42, ⟨⟨279,386,85,43857⟩,0x9b80980000,0x25892b87⟩, ⟨⟨1240,1725,359,125646⟩,0x32a0cb700000,0x370899d961⟩⟩,
     ⟨54, ⟨⟨534,740,167,4011⟩,0x44f1df00000,0x1ff6e1863⟩, ⟨⟨2252,3131,661,63840⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
     ⟨81, ⟨⟨637,883,197,7007⟩,0x73e2ad80000,0x401d0f0c6⟩, ⟨⟨3474,4830,1019,88004⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8364⟩,0xcf60ca00000,0x8af950b98⟩, ⟨⟨4170,5798,1223,106403⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10486⟩,0x201c60040000,0x1cf53a5560⟩, ⟨⟨5487,7630,1607,140227⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 =>
    [⟨0, ⟨⟨11,15,3,125⟩,55574528,2194⟩, ⟨⟨20,28,4,256⟩,0xdc00000,17031⟩⟩,
     ⟨2, ⟨⟨21,29,6,151⟩,0x13cc0000,24733⟩, ⟨⟨38,53,9,375⟩,0x5d840000,211909⟩⟩,
     ⟨5, ⟨⟨34,47,10,230⟩,0x4f100000,156979⟩, ⟨⟨64,89,15,587⟩,0x1a3600000,1564938⟩⟩,
     ⟨10, ⟨⟨54,75,16,378⟩,0x12f140000,957077⟩, ⟨⟨101,141,24,985⟩,0x64f3c0000,9562298⟩⟩]
end P3_7
end
section
namespace P3_7
open P3 (HighBand agreement p blockLength)
abbrev degreeAt := P1_7.degreeAt
abbrev quotientOrder := P1_7.quotientOrder
def gap (hi : ℕ) := agreement - degreeAt hi
def scale (hi : ℕ) := agreement * gap hi
def muNum (hi : ℕ) := agreement * (blockLength - degreeAt hi)
def lambdaNum (hi : ℕ) := blockLength * gap hi
abbrev ceilRatio := P1_7.ceilRatio
abbrev singularDegree := P1_7.singularDegree
abbrev singularFee := P1_7.singularFee
def persistentFee (lo hi e v : ℕ) : ℕ :=
  let t := lambdaNum hi * quotientOrder lo
  let a := muNum hi + 2 * t * (e - 1)
  let b := 2 * hi * muNum hi + 2 * t * v
  ceilRatio (e * b^2 + 2 * v * a * b) ((scale hi)^2) + e
def properFee (lo hi e v : ℕ) : ℕ :=
  let bc := quotientOrder lo + 1
  let ac := 1 + bc * (e - 1)
  let cc := bc * v + 2 * hi
  let bn := lambdaNum hi * quotientOrder lo
  let an := muNum hi + bn * (e - 1)
  let cn := bn * v + 2 * hi * muNum hi
  ceilRatio (e * cc * cn +
    v * (cn * ((2*e-2)*bc + ac) + cc * ((2*e-2)*bn + an)) +
    v^2 * ((ac - 2*bc) * bn + an * bc)) (scale hi)
def flatFee (hi v : ℕ) : ℕ := ceilRatio (P3.t * (p+1) * v) (gap hi)
def tangentFee (lo hi e v : ℕ) : ℕ := properFee lo hi e v + flatFee hi v + e
def wholePrice (lo hi e v : ℕ) : ℕ :=
  if v = 0 then e else singularFee e v +
    if e ≤ 2 then persistentFee lo hi e v else tangentFee lo hi e v
structure GradeOK (lo hi fullU cap e : ℕ) (g : Grade) : Prop where
  sub : g.slots ≤ fullU
  separant : singularDegree e g.seedCap < p
  flat : e * degreeAt hi + g.seedCap < p
  fee : wholePrice lo hi e g.seedCap ≤ cap
theorem grade_of_literals {lo hi fullU cap e v U D m price : ℕ}
    (hU : U ≤ fullU) (hD : singularDegree e v = D) (hDp : D < p)
    (hm : e * degreeAt hi + v = m) (hmp : m < p)
    (hprice : wholePrice lo hi e v = price) (hle : price ≤ cap) :
    GradeOK lo hi fullU cap e ⟨v,U⟩ :=
  ⟨hU, hD.le.trans_lt hDp, hm.le.trans_lt hmp, hprice.le.trans hle⟩
end P3_7
end
section
namespace P3_7
open P3 (K HighBand)
abbrev PrefixFees := P1_7.PrefixFees
def fees : HighBand → PrefixFees
  | .h2274 => ⟨0xc904390c91470f, 0x17d3980110, 0x2ff61282b53d4, 0x509cd82b45d562, 0x198fe0fe4a37, 0x77b6ff61e2a14⟩
  | .h2294 => ⟨0xb8a9a55071628c, 0x19d622fd92, 0x2e2cc452ad45f, 0x4de68be1bd94f6, 0x241721d0f19c, 0x94c0f66257b34⟩
  | .h7773 => ⟨0x25f3ecf8e7b30, 15469025, 0xe395400f361, 0x766d97f5fb4, 0x28950a2d5, 0x7d0bf001f82⟩
structure PrefixBooks (b : HighBand) where
  loss : Finset K
  point : Finset K
  lowSeed : Finset K
  lowJet : Finset K
  fixedODE : Finset K
  content : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  lowSeed_le : lowSeed.card ≤ (fees b).lowSeed
  lowJet_le : lowJet.card ≤ (fees b).lowJet
  fixedODE_le : fixedODE.card ≤ (fees b).fixedODE
  content_le : content.card ≤ (fees b).content
noncomputable def PrefixBooks.union {b} (B : PrefixBooks b) : Finset K := by
  classical exact B.loss ∪ B.point ∪ B.lowSeed ∪ B.lowJet ∪ B.fixedODE ∪ B.content
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial
open P3 (HighBand AnchorModel AnchoredFamily K p node twist agreement)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_3 (Surface Parent)
open scoped BigOperators
def asP1Model {u del} (M : AnchorModel u del) : P1.AnchorModel u del :=
  { M with height_bound := M.height_bound.trans (by decide : P3.heightCap ≤ P1.heightCap) }
def fullCutoff (s : Shape) := s.m * agreement - 1
def buffered (h r : ℕ) (s : Shape) := fullCutoff s - 2*h*r
abbrev debit := P1_7.debit
structure BufferedPair (h : ℕ) (rows : Banks) (s : Stage) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows s.free.shape (buffered h s.reserve s.free.shape)
  moving_mem : moving ∈ rows s.moving.shape (buffered h s.reserve s.moving.shape)
  no_moving : K1_14_3.NoMovingCommon free moving
abbrev Pairs (b : HighBand) (h : ℕ) (rows : Banks) :=
  ∀ s ∈ stages b, BufferedPair h rows s
def BankPass (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {h rows s} (pair : BufferedPair h rows s) (q : Surface) : Prop :=
  BankPass rows s.free.shape q ∧ BankPass rows s.moving.shape q ∧
    K1_14_3R.compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
structure PrefixInventory (b : HighBand) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) {rows : Banks} (pairs : Pairs b M.overhead.toNat rows) where
  books : PrefixBooks b
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  stage_pass : ∀ q ∈ parents, ∀ s (hs : s ∈ stages b), 0 < s.reserve →
    PairPass (pairs s hs) q
  terminal_pass : ∀ q ∈ parents, BankPass rows (terminal b).shape q
  covers : ∀ γ ∈ Γ, γ ∈ books.union ∨ ∃ q ∈ parents, MarkOn M F q γ
def curveUnit (hi g : ℕ) : ℚ :=
  let d := degreeAt hi
  (2*(g : ℚ)-1) * (1 + 2*((P3.blockLength : ℚ)/agreement)*d) +
    ((P3.blockLength - d : ℕ) : ℚ) / gap hi
def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*agreement+j - q*(131071-h)
    let c := fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))
end
end P3_7
end
section
namespace P3_7
open P3 (HighBand agreement p)
local notation "r!" x "," y "," z => grade_of_literals (D := x) (m := y) (price := z)
  (by decide) rfl (by decide) rfl (by decide) rfl (by decide)
private theorem guard {lo hi m B top edge : ℕ}
    (hl : 0 < lo) (hh : hi ≤ 33249) (ht : m*agreement = top) (hp : 0 < top)
    (hc : top < p) (hw : B*(131071-lo) = edge) (he : edge ≤ top) :
    0 < lo ∧ hi ≤ 33249 ∧ 0 < m*agreement ∧ m*agreement < p ∧ B*(131071-lo) ≤ m*agreement :=
  ⟨hl, hh, ht.symm ▸ hp, ht.symm ▸ hc, hw.le.trans (he.trans ht.ge)⟩
local notation "g!" t "," w => guard (top := t) (edge := w) (by decide) (by decide) rfl
  (by decide) (by decide) rfl (by decide)
end P3_7
end
section
namespace P3_7
noncomputable section
open P3 (K I node p agreement blockLength AnchorModel AnchoredFamily)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open Finset Polynomial ProximityPrize.Benchmark
end
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial
open P3 (HighBand AnchorModel AnchoredFamily agreement p)
open K1_14 (Banks Jet Equation SeedBound)
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open K1_14_4 (seedDegree seedDegree_le_iff)
end
end P3_7
end

end Merged_GoldBranch7

-- merged module HighCore82258Data
section Merged_HighCore82258Data

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258

abbrev agreement : ℕ := 179886
abbrev heightCap : ℕ := 33443
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
abbrev debit := P1_7.debit

inductive Band where
  | h2367 | h2395 | h7773
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2367 => 2414
  | .h2395 => 2536
  | .h7773 => 7773
def finish : Band → ℕ
  | .h2367 => 2535
  | .h2395 => 7772
  | .h7773 => 33443
def terminal : Band → Bank
  | .h2367 => ⟨⟨4500,6256,1323,315000⟩,0x98969fb680000,0x2586075c1890⟩
  | .h2395 => ⟨⟨7550,10506,2218,180000⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,900⟩,0xc4fd80000,0x15c66e5⟩
def grades : Band → List Grade
  | .h2367 => []
  | .h2395 => [⟨338,172349⟩, ⟨333,173304⟩, ⟨327,179574⟩, ⟨322,177387⟩, ⟨317,175478⟩, ⟨311,176977⟩, ⟨305,177384⟩, ⟨299,176903⟩, ⟨292,178309⟩, ⟨285,178543⟩, ⟨277,179864⟩, ⟨269,179838⟩, ⟨261,178760⟩, ⟨251,179370⟩, ⟨240,179648⟩, ⟨228,179554⟩, ⟨214,179916⟩, ⟨199,179883⟩, ⟨183,179596⟩, ⟨165,179633⟩, ⟨145,179890⟩, ⟨124,179925⟩, ⟨102,179808⟩, ⟨78,179897⟩, ⟨53,179864⟩, ⟨26,180000⟩]
  | .h7773 => [⟨26,821⟩, ⟨25,771⟩, ⟨23,796⟩, ⟨20,855⟩, ⟨16,879⟩, ⟨10,900⟩, ⟨3,899⟩]
def stages : Band → List Stage
  | .h2367 => [⟨0,⟨⟨76,105,23,876⟩,0x345100000,0x3777f9⟩,⟨⟨437,608,128,16460⟩,0x2407b5c0000,0xdd657d32⟩⟩,
    ⟨1,⟨⟨83,115,25,972⟩,0x439080000,0x4ed4ac⟩,⟨⟨436,606,128,19573⟩,0x23d8b880000,0xdb115372⟩⟩,
    ⟨2,⟨⟨92,127,28,1030⟩,0x5c3600000,0x75b415⟩,⟨⟨508,706,149,20147⟩,0x389233c0000,0x19280bd7d⟩⟩,
    ⟨3,⟨⟨99,137,30,1121⟩,0x722180000,0x9dd5af⟩,⟨⟨492,686,144,24446⟩,0x33533580000,0x1656b0db4⟩⟩,
    ⟨4,⟨⟨107,148,33,1188⟩,0x917680000,0xd8f2fa⟩,⟨⟨525,731,154,26591⟩,0x3e6d7fc0000,0x1cdc7da38⟩⟩,
    ⟨5,⟨⟨116,161,35,1260⟩,0xb5c380000,0x128bb48⟩,⟨⟨642,892,188,24982⟩,0x71d1af40000,0x3fe068fa5⟩⟩,
    ⟨7,⟨⟨126,175,39,1507⟩,0xec9f00000,0x1a458a5⟩,⟨⟨685,952,201,29660⟩,0x8a677880000,0x52f0bdb9b⟩⟩,
    ⟨10,⟨⟨142,197,43,1969⟩,0x14bde80000,0x294fec6⟩,⟨⟨865,1202,254,33015⟩,0x1166fe340000,0xd28832ce8⟩⟩,
    ⟨16,⟨⟨171,237,50,3693⟩,0x2316e80000,0x53b7f45⟩,⟨⟨1014,1412,298,46747⟩,0x1c0729180000,0x1901657cf3⟩⟩,
    ⟨10,⟨⟨178,247,55,1414⟩,0x2932d00000,0x66c8fdf⟩,⟨⟨792,1101,233,35460⟩,0xd623cb40000,0x947787094⟩⟩,
    ⟨20,⟨⟨250,347,78,2205⟩,0x721cb80000,0x18f6d6a4⟩,⟨⟨1302,1815,383,49376⟩,0x3b50b1000000,0x442ac5ba92⟩⟩,
    ⟨32,⟨⟨261,362,81,6745⟩,0x813b280000,0x1d6fb003⟩,⟨⟨1459,2035,429,91138⟩,0x536744d80000,0x6b96ecc888⟩⟩,
    ⟨31,⟨⟨345,478,108,2963⟩,0x12b1e340000,0x59a98629⟩,⟨⟨1604,2235,472,73350⟩,0x6edb04b80000,0x9cb2a062f8⟩⟩,
    ⟨44,⟨⟨376,522,118,5271⟩,0x183833c0000,0x7f6275d9⟩,⟨⟨2253,3142,664,91136⟩,0x1334cd7ac0000,0x263b0eab16b⟩⟩,
    ⟨73,⟨⟨599,831,188,7362⟩,0x617b2300000,0x32de21d13⟩,⟨⟨3486,4863,1027,139347⟩,0x4711f2a780000,0xdb0e8041cee⟩⟩,
    ⟨76,⟨⟨498,692,155,26786⟩,0x37c11c80000,0x185234383⟩,⟨⟨2760,3850,812,234277⟩,0x233f7cff80000,0x5601e71ab3f⟩⟩,
    ⟨103,⟨⟨809,1126,252,10214⟩,0xee4ed940000,0xa99a27482⟩,⟨⟨4774,6667,1405,189434⟩,0xb6532fbfc0000,0x304357eb723c⟩⟩]
  | .h2395 => [⟨0,⟨⟨73,101,22,686⟩,0x2e5640000,0x2f6f2a⟩,⟨⟨352,489,103,9578⟩,0x12dda700000,0x5cfd94a5⟩⟩,
    ⟨1,⟨⟨78,108,24,786⟩,0x392740000,0x3e9e8f⟩,⟨⟨345,480,101,11294⟩,0x11c61f80000,0x564a51c0⟩⟩,
    ⟨2,⟨⟨86,119,26,855⟩,0x4b3780000,0x5a8245⟩,⟨⟨385,535,112,12199⟩,0x188bf840000,0x84679137⟩⟩,
    ⟨3,⟨⟨94,130,29,913⟩,0x633bc0000,0x822d2c⟩,⟨⟨411,572,120,13413⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
    ⟨4,⟨⟨102,141,31,983⟩,0x7cec00000,0xb15384⟩,⟨⟨438,609,128,14645⟩,0x2436d340000,0xde912dc3⟩⟩,
    ⟨5,⟨⟨108,150,33,1068⟩,0x948040000,0xe271e9⟩,⟨⟨522,726,153,14724⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
    ⟨6,⟨⟨108,149,33,1296⟩,0x948040000,0xdda994⟩,⟨⟨570,792,167,15613⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
    ⟨10,⟨⟨142,197,43,1481⟩,0x14bde80000,0x294fec6⟩,⟨⟨696,968,204,19837⟩,0x910a3980000,0x5884788a7⟩⟩,
    ⟨16,⟨⟨163,226,50,2605⟩,0x1f8a780000,0x47e88b5⟩,⟨⟨851,1183,249,26947⟩,0x108708880000,0xc4f2a7606⟩⟩,
    ⟨18,⟨⟨221,306,68,1813⟩,0x4e346c0000,0xf032b8c⟩,⟨⟨952,1324,279,28359⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
    ⟨24,⟨⟨212,294,65,3510⟩,0x44e9c40000,0xcc1a54f⟩,⟨⟨1115,1550,329,35496⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
    ⟨32,⟨⟨261,362,82,4355⟩,0x826c0c0000,0x1db6eefa⟩,⟨⟨1463,2034,430,42333⟩,0x54106e900000,0x6b9d823520⟩⟩,
    ⟨36,⟨⟨246,341,75,22227⟩,0x6ae4280000,0x16e7d3b2⟩,⟨⟨1220,1696,357,66559⟩,0x309db61c0000,0x33e3754396⟩⟩,
    ⟨42,⟨⟨279,386,85,24816⟩,0x9b80980000,0x25892b87⟩,⟨⟨1240,1725,359,118401⟩,0x32a0cb700000,0x370899d961⟩⟩,
    ⟨54,⟨⟨534,740,167,3960⟩,0x44f1df00000,0x1ff6e1863⟩,⟨⟨2252,3131,661,64497⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
    ⟨81,⟨⟨637,883,197,6921⟩,0x73e2ad80000,0x401d0f0c6⟩,⟨⟨3474,4830,1019,89437⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
    ⟨100,⟨⟨774,1072,239,8313⟩,0xcf60ca00000,0x8af950b98⟩,⟨⟨4170,5798,1223,108383⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
    ⟨135,⟨⟨1042,1443,329,10485⟩,0x201c60040000,0x1cf53a5560⟩,⟨⟨5487,7630,1607,143115⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 => [⟨0,⟨⟨11,15,3,134⟩,0x3500000,0x892⟩,⟨⟨20,28,4,277⟩,0xdc00000,0x4287⟩⟩,
    ⟨2,⟨⟨21,29,6,158⟩,0x13cc0000,0x609d⟩,⟨⟨38,53,9,400⟩,0x5d840000,0x33bc5⟩⟩,
    ⟨5,⟨⟨34,47,10,240⟩,0x4f100000,0x26533⟩,⟨⟨64,89,15,625⟩,0x1a3600000,0x17e10a⟩⟩,
    ⟨10,⟨⟨54,75,16,397⟩,0x12f140000,0xe9a95⟩,⟨⟨101,141,24,1052⟩,0x64f3c0000,0x91e8ba⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2367 => ⟨0x17995391305d9d6,0x266971f131,0x38b9c7c36389b,0x1cf1,0xfb231c85bab,0x219848008770⟩
  | .h2395 => ⟨0x972cf6daf77844,0x111c043902,0x26c37cc20d2f5,0x36aeb2322a567a,0x14c52d2e35e9,0x13e3e8005030⟩
  | .h7773 => ⟨0x288871cb28934,0x1104ece,0xf529d0114e8,0x89c424f27e8,0x16e313bf1,0xcbe5000336⟩
def retainedCap : Band → ℕ
  | .h2367 => 0x233b95fa21d83e5
  | .h2395 => 0x271956e092a65d7
  | .h7773 => 0x13aee2ace4cdc
def highBound : Band → ℕ
  | .h2367 => 0x3b10ba614948794
  | .h2395 => 0x3420609139fc6a6
  | .h7773 => 0x3dc317b12a0d6

def subbank (b : Band) (g : Grade) : Bank :=
  let t := terminal b
  { t with shape := { t.shape with U := g.slots } }

abbrev GradeIndex (b : Band) := Fin (grades b).length

def Listed (b : Band) (t : Bank) : Prop :=
  t = terminal b ∨ (∃ s ∈ stages b, t = s.free ∨ t = s.moving) ∨
    ∃ i : GradeIndex b, t = subbank b ((grades b).get i)

abbrev Test (b : Band) := Option (GradeIndex b)

def tested (b : Band) : Test b → Bank
  | none => terminal b
  | some i => subbank b ((grades b).get i)

def threshold (b : Band) : Test b → ℕ
  | none => (grades b).length + 1
  | some i => i.val + 1

def seedThreshold (b : Band) : Test b → ℕ
  | none => 0
  | some i => ((grades b).get i).seedCap + 1

def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*agreement+j - q*(131071-h)
    let c := fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))

def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * agreement - 2 * h * r

def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)


def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => rawWidth h r s q j - mode * (2 * h * j))


theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE + (fees b).content + retainedCap b + 1 = highBound b ∧
       highBound b ≤ 267872462194200158 := by
  cases b <;> decide +kernel

end HighCore82258

end Merged_HighCore82258Data

-- merged module FrontCore82258Model
section Merged_FrontCore82258Model

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option backward.isDefEq.respectTransparency false

namespace FrontCore82258

noncomputable section

open Polynomial
open P1 (K I node twist p)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum seedEmbedding)
open K1_14_1 (PoleData MarkResidues nodeL)
open P1_7 (Reduced singularDegree singularFee)
open scoped BigOperators Polynomial

abbrev AnchorModel (u : P1.Words) (D : Finset I) := P1.ModelAt HighCore82258.heightCap u D
abbrev AnchoredFamily {u D} (M : AnchorModel u D) (Γ : Finset K) :=
  P1.FamilyAt HighCore82258.agreement M Γ

def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ

end
end FrontCore82258

end Merged_FrontCore82258Model
