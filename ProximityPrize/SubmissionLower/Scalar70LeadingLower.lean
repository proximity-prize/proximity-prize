import ProximityPrize.SubmissionLower.Scalar70LeadingLowerBase
import ProximityPrize.SubmissionLower.Fast074

set_option Elab.async false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit true

section
namespace Scalar70LeadingLower_1
noncomputable section
variable {top : Fin 1}
open K1 (I K)
open Scalar70LeadingPrice (Messages taylorLength physicalDegree)
open Scalar70LeadingLower (ProperCover SecondFactors Whole mixedBudget invariantBudget)
open K1_13 (Row Geom atJet extend)
open K1_13_5 (RegularAt NodeFamily separant)
open K1_13_5_4 (GeometricX GeoRow genericRow genericCoeff genericCoeff_injective
  jetPoint regularLocus eval_genericRow_at_point jetPoint_injOn)
open Polynomial
open scoped BigOperators
private theorem exists_properComponent {n : ℕ} {f : Fin n → Row 3}
    (T : ∀ i, LiftedChart top (f i)) {i : Fin n} {S : Geom[X]}
    (hS : S.natDegree ≤ physicalDegree) (hr : RegularAt 2 (f i) S) (hw : ¬ Whole (f i)) :
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
end Scalar70LeadingLower_1
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5 (separant)
open Scalar70LeadingLower (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow GeometricX genericRow)
open K1_13_5_4_2 (JetPoint ExponentSpace boxExponents graphLocus graphCurve capBody mixedVolume4)
open Scalar70LeadingPrice (taylorLength)
open Scalar70LeadingLower (Whole)
open Scalar70LeadingLower_1 (oldCutIdeal)
open MvPolynomial
def factorCurves (f : Row 3) : Finset (Ideal (GeoRow 3)) := by
  classical
  exact if Whole f then ∅ else
    (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))
abbrev lastBox (top : Fin 1) := liftedBox top (taylorLength + 2)
abbrev lastExponents (top : Fin 1) := boxExponents (lastBox top) taylorLength
abbrev lastMap (top : Fin 1) := monomialMap GeometricX (lastExponents top)
def sectionIdeal (top : Fin 1) (f : Row 3) (P : Ideal (GeoRow 3)) :
    Ideal (MvPolynomial (lastExponents top) GeometricX) :=
  (graphCurve f P).comap (lastMap top)
def IsSectionCurve (top : Fin 1) (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  (sectionIdeal top f P).IsPrime ∧ (affineHilbertPolynomial (sectionIdeal top f P)).natDegree = 1
def sectionDegree (top : Fin 1) (f : Row 3) (P : Ideal (GeoRow 3)) : ℚ :=
  affineDegree (sectionIdeal top f P)
structure GenericSection (top : Fin 1) (f : Row 3) where
  polynomial : GeoRow 4
  support : InLiftedBox polynomial (lastBox top) taylorLength
  points : Ideal (GeoRow 3) → Finset JetPoint
  card_eq : ∀ P ∈ factorCurves f, ((points P).card : ℚ) = sectionDegree top f P
  proper : ∀ P ∈ factorCurves f, polynomial ∉ graphCurve f P
  roots : ∀ P ∈ factorCurves f, ∀ y ∈ points P,
    y ∈ graphLocus f P ∧ eval y polynomial = 0
  off_other_curves : ∀ P ∈ factorCurves f, ∀ P' ∈ factorCurves f, P ≠ P' →
    ∀ y ∈ points P, y ∉ graphLocus f P'
def lastMixedVolume (top : Fin 1) (first : Set ExponentSpace) : ℝ :=
  mixedVolume4 ![first, capBody (graphBox top) 1,
    capBody (liftedBox top (taylorLength + 1)) (taylorLength - 1),
    capBody (lastBox top) taylorLength]
end
end Scalar70LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Row Geom Shape)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericCoeff_injective genericRow
  liftRow regularLocus graphPoint)
open K1_13_5_4_2 (boxExponents graphCurve eval_represents_iff)
open Scalar70LeadingPrice (taylorLength)
open Scalar70LeadingLower (Whole)
open Scalar70LeadingLower_1 (oldCut oldCutIdeal properComponents CurveIndex componentLength nextCutLocus
  oldNext LiftedChart)
open MvPolynomial RingTheory.Sequence
open scoped BigOperators Polynomial
open private quotient_regular_iff graph_dimension from ProximityPrize.SubmissionLower.Fast048
open private graphPoint_injective from ProximityPrize.SubmissionLower.Fast048
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem mem_factorCurves {f : Row 3} {P : Ideal (GeoRow 3)} :
    P ∈ factorCurves f ↔ ¬ Whole f ∧
      P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f)) := by
  classical
  by_cases hf : Whole f <;> simp [factorCurves, hf]
theorem properComponents_eq {n : ℕ} (f : Fin n → Row 3) :
    properComponents f = Finset.univ.biUnion fun i =>
      (factorCurves (f i)).image (fun P => (i, P)) := by
  classical
  unfold properComponents
  congr 1
  funext i
  by_cases hf : Whole (f i) <;> simp [factorCurves, hf]
theorem componentLength_of_retained {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    0 < componentLength f P ∧ componentLength f P < ⊤ := by
  classical
  have hm := (Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2).1
  have hp : P.IsPrime := hm.isPrime
  rw [componentLength, dite_eq_left hp]
  let A := Localization.AtPrime P
  let L := (oldCutIdeal f).map (algebraMap (GeoRow 3) A)
  have hle : L ≤ IsLocalRing.maximalIdeal A := by
    apply Ideal.map_le_iff_le_comap.mpr
    change oldCutIdeal f ≤ (IsLocalRing.maximalIdeal A).under (GeoRow 3)
    rw [IsLocalization.AtPrime.under_maximalIdeal A P]
    exact hm.le
  have hL : L ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hle
  let : Nontrivial (A ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr hL
  exact ⟨Module.length_pos, K1_13_5_4_2.localLength_lt_top hm⟩
private theorem single_mem_box (s : Shape) (h : ℕ)
    (hb : 1 ≤ s.b) (hj : 2 ≤ s.j) (ht : 1 ≤ s.t) (hh : 1 ≤ h)
    (i : Fin 4) : Finsupp.single i 1 ∈ boxExponents s h := by
  change (Finsupp.single i 1) 0 + (Finsupp.single i 1) 1 + (Finsupp.single i 1) 2 ≤
    s.b ∧ (Finsupp.single i 1) 1 + 2 * (Finsupp.single i 1) 2 ≤ s.j ∧
    (Finsupp.single i 1) 2 ≤ s.t ∧ (Finsupp.single i 1) 3 ≤ h
  fin_cases i <;> norm_num [Finsupp.single_apply] <;> omega
theorem lastExponents_single (i : Fin 4) : Finsupp.single i 1 ∈ (lastExponents top) :=
  single_mem_box (lastBox top) taylorLength
    (show 1 ≤ (lastBox top).b by fin_cases top <;> decide) (show 2 ≤ (lastBox top).j by fin_cases top <;> decide)
    (show 1 ≤ (lastBox top).t by fin_cases top <;> decide) (show 1 ≤ 131072 by decide) i
private theorem cut_regular {f : Row 3} (hf : Irreducible f) (hw : ¬ Whole f) :
    IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span {genericRow f}) (genericRow (oldCut f))) := by
  let : Algebra Geom[X] GeometricX := genericCoeff.toAlgebra
  have : Module.IsTorsionFree (Geom[X]) GeometricX :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr genericCoeff_injective
  have : Module.Flat (Geom[X]) GeometricX := inferInstance
  have hbase : IsBaseChange (Row 3)
      (IsScalarTower.toAlgHom (Geom[X]) GeometricX (GeoRow 3)).toLinearMap :=
    Algebra.IsPushout.out
  have : Module.Flat (Row 3) (GeoRow 3) :=
    Module.Flat.isBaseChange (R := Geom[X]) (S := Row 3) (M := GeometricX)
      (N := GeoRow 3) hbase
  have : (Ideal.span {f} : Ideal (Row 3)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hc : oldCut f ∉ (Ideal.span {f} : Ideal (Row 3)) :=
    fun h => hw (Ideal.mem_span_singleton.mp h)
  have hseq : IsWeaklyRegular (Row 3) [f, oldCut f] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, quotient_regular_iff]
    exact ⟨fun _ _ h => mul_left_cancel₀ hf.ne_zero h,
      fun _ _ h => mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hc) h⟩
  have h := hseq.of_flat (S := GeoRow 3)
  change IsWeaklyRegular (GeoRow 3) [genericRow f, genericRow (oldCut f)] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, quotient_regular_iff] at h
  exact h.2
private theorem retained_dimension {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) :
    (affineHilbertPolynomial P).natDegree = 1 := by
  obtain ⟨hw, hret⟩ := mem_factorCurves.mp hP
  have hmin := (Ideal.mem_retainedMinimalPrimes.mp hret).1
  let := hmin.isPrime
  let H : Ideal (GeoRow 3) := Ideal.span {genericRow f}
  let g := genericRow (oldCut f)
  have heq : oldCutIdeal f = H ⊔ Ideal.span {g} := by
    rw [← Ideal.span_union]
    rfl
  have hHP : H ≤ P := le_sup_left.trans (heq ▸ hmin.le)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hHP
  let := hQ.isPrime
  have hgQ : g ∉ Q := by
    intro hg
    obtain ⟨a, ha, hga⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hQ hg
    have hga' : Ideal.Quotient.mk H g * Ideal.Quotient.mk H a = Ideal.Quotient.mk H g * 0 := by
      rw [← map_mul, mul_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hga
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mp (cut_regular hf hw hga'))
  have hP' : P ∈ (Q ⊔ Ideal.span {g}).minimalPrimes := by
    have hle : H ⊔ Ideal.span {g} ≤ Q ⊔ Ideal.span {g} := sup_le_sup_right hQ.le _
    refine ⟨⟨hmin.isPrime, sup_le hQP (le_sup_right.trans (heq ▸ hmin.le))⟩, ?_⟩
    intro J hJ hJP
    exact hmin.2 ⟨hJ.1, heq.trans_le (hle.trans hJ.2)⟩ hJP
  have hF : genericRow f ≠ 0 :=
    fun h => hf.ne_zero (map_injective _ genericCoeff_injective (h.trans (map_zero _).symm))
  have hdQ := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hQ
  have hdP := principalCut_natDegree_affineHilbertPolynomial_add_one hgQ hP'
  rw [Nat.card_fin] at hdQ
  omega
end
end Scalar70LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open Scalar70LeadingLower (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow)
open K1_13_5_4_2 (JetPoint fourCutIdeal pointIdeal pointLength downBody capBody)
open K1_13_5_4_2_4 (Exponent Downward cutIdeal downSupport capSupport mem_downSupport mem_capSupport
  latticeBody latticeBody_downSupport latticeBody_capSupport)
open Scalar70LeadingPrice (taylorLength)
open MvPolynomial
open scoped BigOperators Pointwise
open private mixed_eq_generic downSupport_downward capSupport_downward zero_mem_capSupport
  from ProximityPrize.SubmissionLower.Fast048
end
end Scalar70LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Row Shape indexDegree)
open K1_13_5 (separant)
open Scalar70LeadingLower (lowBox liftedBox mixedCoefficients)
open K1_13_5_4 (InLiftedBox GeometricX GeoRow genericRow liftRow graphPoint regularLocus)
open K1_13_5_4_2 (graphLocus JetPoint eval_liftRow_graphPoint)
open Scalar70LeadingPrice (taylorLength)
open Scalar70LeadingLower (SecondFactors)
open Scalar70LeadingLower_1 (LiftedChart reconstruct CoefficientIdeal)
open MvPolynomial
open scoped BigOperators Pointwise
open private ratio_image_degree box_mono from ProximityPrize.SubmissionLower.Fast048
end
end Scalar70LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5_4 (GeoRow genericRow liftRow graph)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal pointLength downBody
  localLength_lt_top)
open Scalar70LeadingLower (SecondFactors mixedBudget)
open Scalar70LeadingLower_1 (LiftedChart CurveIndex properComponents componentLength)
open MvPolynomial
open scoped BigOperators
open private lift_generic_ne_zero from ProximityPrize.SubmissionLower.Fast048
def c2 (top : Fin 1) : Prop :=
  ∀ (f : Row 3), Irreducible f → 0 < f.degreeOf 2 → ∀ (T : LiftedChart top f) (L : GeoRow 4),
    (∀ P ∈ factorCurves f, L ∉ graphCurve f P) →
    ∀ P ∈ factorCurves f, ∀ y ∈ graphLocus f P, eval y L = 0 →
      let J := fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L
      pointIdeal y ∈ J.minimalPrimes ∧ componentLength f P ≤ pointLength J y
end
end Scalar70LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1_1
noncomputable section
variable {top : Fin 1}
open K1_13_5_4 (GeoRow GeometricX InLiftedBox)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve)
open K1_13_5_4_2_2 (linearForm fiberIdeal totalDegree_hyperplane_le_one zeroLocus_fiber_iff
  ncard_eq_affineDegree_of_radical)
open Scalar70LeadingPrice (taylorLength)
open Scalar70LeadingLower_1_1 (factorCurves lastBox lastExponents lastMap sectionIdeal sectionDegree)
open MvPolynomial
open scoped Pointwise
end
end Scalar70LeadingLower_1_1_1
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5 (lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow graph graphIdeal)
open Scalar70LeadingLower_1 (LiftedChart oldCutIdeal)
open K1_13_5_4_2_3 (OpenRing onOpen onOpen_kills onOpen_isUnit onOpen_hom_ext
  openLift openLift_onOpen sep liftedSep)
open MvPolynomial
open private three_isUnit graph_coord_unique represents_vanish from ProximityPrize.SubmissionLower.Fast048
def threeCut (f : Row 3) (T : LiftedChart top f) : Ideal (GeoRow 4) :=
  graphIdeal f ⊔ Ideal.span {T.cut}
abbrev OldOpen (f : Row 3) := OpenRing (oldCutIdeal f) (sep f)
abbrev GraphOpen (f : Row 3) (T : LiftedChart top f) := OpenRing (threeCut f T) (liftedSep f)
abbrev oldMap (f : Row 3) := onOpen (oldCutIdeal f) (sep f)
abbrev graphMap (f : Row 3) (T : LiftedChart top f) := onOpen (threeCut f T) (liftedSep f)
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
private theorem substitute_kills (f : Row 3) (T : LiftedChart top f) :
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
private def graphToOld (f : Row 3) (T : LiftedChart top f) : GraphOpen f T →+* OldOpen f :=
  openLift _ _ (substitute f) (substitute_kills f T)
    (by rw [substitute_lift]; exact onOpen_isUnit _ _)
private theorem graphToOld_on (f : Row 3) (T : LiftedChart top f) (b : GeoRow 4) :
    graphToOld f T (graphMap f T b) = substitute f b := by
  rw [graphToOld, openLift_onOpen]
private theorem oldToGraph_kills (f : Row 3) (T : LiftedChart top f) :
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
private def oldToGraph (f : Row 3) (T : LiftedChart top f) : OldOpen f →+* GraphOpen f T :=
  openLift _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f))
@[simp] private theorem oldToGraph_on (f : Row 3) (T : LiftedChart top f) (a : GeoRow 3) :
    oldToGraph f T (oldMap f a) = graphMap f T (liftRow a) :=
  openLift_onOpen _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f)) a
def graphEquiv (f : Row 3) (T : LiftedChart top f) : OldOpen f ≃+* GraphOpen f T := by
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
@[simp] theorem graphEquiv_on (f : Row 3) (T : LiftedChart top f) (a : GeoRow 3) :
    graphEquiv f T (oldMap f a) = graphMap f T (liftRow a) :=
  oldToGraph_on f T a
end
end Scalar70LeadingLower_1_1_2
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5_4 (GeoRow GeometricX genericRow regularLocus liftRow graph graphIdeal graphPoint)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal
  eval_liftRow_graphPoint eval_graph_graphPoint eval_represents_iff)
open K1_13_5_4_2_3 (sep liftedSep openLift openLift_onOpen onOpen_kills
  length_atPrime_le_length_principalCut)
open Scalar70LeadingLower_1 (LiftedChart componentLength oldCutIdeal)
open Scalar70LeadingLower_1_1 (factorCurves mem_factorCurves)
open MvPolynomial
open private graph_dimension from ProximityPrize.SubmissionLower.Fast048
open private graphCurve_comap graphCurve_le_point sep_notMem_point from ProximityPrize.SubmissionLower.Fast048
open Scalar70LeadingLower_1_1 (retained_dimension)
open private mem_iff_vanishes_regular from ProximityPrize.SubmissionLower.Fast073
open private exists_open_prime openAtPrimeEquivQuotient colength_eq_of_quotient_equiv
  from ProximityPrize.SubmissionLower.Fast076
private theorem threeCut_le_graphCurve {f : Row 3} (T : LiftedChart top f)
    {P : Ideal (GeoRow 3)} (hP : oldCutIdeal f ≤ P) :
    threeCut f T ≤ graphCurve f P := by
  have hf (x : Fin 3 → GeometricX) (hx : x ∈ regularLocus f P) :
      eval x (genericRow f) = 0 :=
    hx.1 _ (hP (Ideal.subset_span (by simp)))
  apply sup_le
  · apply Ideal.span_le.mpr
    intro u hu y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · simpa only [aeval_eq_eval, eval_liftRow_graphPoint] using hf x hx
    · exact eval_graph_graphPoint hx.2
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (eval_represents_iff T.cut_represents (hf x hx) hx.2).mpr
      (hx.1 _ (hP (Ideal.subset_span (by simp))))
private theorem prime_of_chart {f : Row 3} (T : LiftedChart top f)
    (Q : Ideal (GeoRow 4)) [Q.IsPrime] (hcut : threeCut f T ≤ Q) (hsep : liftedSep f ∉ Q) :
    let P := Q.comap (rename Fin.castSucc).toRingHom
    oldCutIdeal f ≤ P ∧ graphCurve f P = Q := by
  let P := Q.comap (rename Fin.castSucc).toRingHom
  let : P.IsPrime := Ideal.comap_isPrime _ Q
  let F := FractionRing (GeoRow 4 ⧸ Q)
  let q : GeoRow 4 →+* F := (algebraMap (GeoRow 4 ⧸ Q) F).comp (Ideal.Quotient.mk Q)
  have hq (b : GeoRow 4) : q b = 0 ↔ b ∈ Q := by
    change algebraMap (GeoRow 4 ⧸ Q) F (Ideal.Quotient.mk Q b) = 0 ↔ b ∈ Q
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hsq : q (liftedSep f) ≠ 0 := fun h => hsep ((hq _).mp h)
  let qOpen := openLift (threeCut f T) (liftedSep f) q
    (fun b hb => RingHom.mem_ker.mpr ((hq b).mpr (hcut hb))) (isUnit_iff_ne_zero.mpr hsq)
  have hqOpen (b : GeoRow 4) : qOpen (graphMap f T b) = q b := openLift_onOpen _ _ _ _ _ b
  have hP : oldCutIdeal f ≤ P := by
    intro a ha
    change liftRow a ∈ Q
    apply (hq _).mp
    rw [← hqOpen, ← graphEquiv_on, onOpen_kills ha, map_zero, map_zero]
  refine ⟨hP, ?_⟩
  apply SetLike.ext
  intro b
  let e := graphEquiv f T
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (oldCutIdeal f) (sep f)) (e.symm (graphMap f T b))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  change e.symm (graphMap f T b) * oldMap f (sep f) ^ n = oldMap f a at hc
  have hab : graphMap f T b * graphMap f T (liftedSep f) ^ n = graphMap f T (liftRow a) := by
    simpa only [e, map_mul, map_pow, RingEquiv.apply_symm_apply, graphEquiv_on] using congrArg e hc
  have hfrac := congrArg qOpen hab
  simp only [map_mul, map_pow, hqOpen] at hfrac
  have hQmem : b ∈ Q ↔ a ∈ P := by
    change b ∈ Q ↔ liftRow a ∈ Q
    rw [← hq b, ← hq (liftRow a), ← hfrac, mul_eq_zero]
    simp only [pow_ne_zero n hsq, or_false]
  have hpoint (x : Fin 3 → GeometricX) (hx : x ∈ regularLocus f P) :
      eval (graphPoint f x) b * eval x (sep f) ^ n = eval x a := by
    have hs : eval (graphPoint f x) (liftedSep f) ≠ 0 := by
      rw [eval_liftRow_graphPoint]
      exact hx.2
    have hkill : threeCut f T ≤ RingHom.ker (eval (graphPoint f x)) := by
      intro g hg
      exact RingHom.mem_ker.mpr (threeCut_le_graphCurve T hP hg _ ⟨x, hx, rfl⟩)
    let w := openLift (threeCut f T) (liftedSep f) (eval (graphPoint f x)) hkill
      (isUnit_iff_ne_zero.mpr hs)
    have hw (g : GeoRow 4) : w (graphMap f T g) = eval (graphPoint f x) g :=
      openLift_onOpen _ _ _ _ _ g
    simpa only [map_mul, map_pow, hw, eval_liftRow_graphPoint] using congrArg w hab
  rw [hQmem, mem_iff_vanishes_regular (show sep f ∉ P from hsep)]
  constructor
  · intro hb x hx
    have hz : eval (graphPoint f x) b = 0 := hb _ ⟨x, hx, rfl⟩
    rw [← hpoint x hx, hz, zero_mul]
  · intro ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (mul_eq_zero.mp ((hpoint x hx).trans (ha x hx))).resolve_right (pow_ne_zero n hx.2)
private theorem chart_colength {f : Row 3} (T : LiftedChart top f)
    (P : Ideal (GeoRow 3)) (Q : Ideal (GeoRow 4)) [P.IsPrime] [Q.IsPrime]
    (hQ : threeCut f T ≤ Q) (hsQ : liftedSep f ∉ Q)
    (hQP : Q.comap (rename Fin.castSucc).toRingHom = P) :
    let A := Localization.AtPrime P
    let B := Localization.AtPrime Q
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A)) =
      Module.length B (B ⧸ (threeCut f T).map (algebraMap (GeoRow 4) B)) := by
  obtain ⟨q, hprime, hq⟩ := exists_open_prime hQ hsQ
  let : q.IsPrime := hprime
  let e := graphEquiv f T
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime _ q
  have hp : p.comap (oldMap f) = P := by
    ext b
    change graphEquiv f T (oldMap f b) ∈ q ↔ b ∈ P
    rw [graphEquiv_on]
    change liftRow b ∈ q.comap (graphMap f T) ↔ b ∈ P
    rw [hq]
    change b ∈ Q.comap (rename Fin.castSucc).toRingHom ↔ b ∈ P
    rw [hQP]
  exact colength_eq_of_quotient_equiv
    ((openAtPrimeEquivQuotient p hp).symm.trans
      ((Localization.localRingEquiv p q e rfl).trans (openAtPrimeEquivQuotient q hq)))
private theorem graph_is_curve {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) :
    (graphCurve f P).IsPrime ∧ (affineHilbertPolynomial (graphCurve f P)).natDegree = 1 := by
  obtain ⟨hm, hs⟩ := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let : P.IsPrime := hm.isPrime
  obtain ⟨hp, hdim⟩ := graph_dimension f P hs
  exact ⟨hp, hdim.trans (retained_dimension hf hP)⟩
private theorem point_isolated {f : Row 3} (hf : Irreducible f)
    (T : LiftedChart top f) {L : GeoRow 4} (hL : ∀ P ∈ factorCurves f, L ∉ graphCurve f P)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) {y : JetPoint}
    (hy : y ∈ graphLocus f P) (hLy : eval y L = 0) :
    pointIdeal y ∈ (threeCut f T ⊔ Ideal.span {L}).minimalPrimes := by
  let m := pointIdeal y
  have hmsep : liftedSep f ∉ m := sep_notMem_point hy
  obtain ⟨hProper, hRet⟩ := mem_factorCurves.mp hP
  have hBm : threeCut f T ≤ m :=
    (threeCut_le_graphCurve T (Ideal.mem_retainedMinimalPrimes.mp hRet).1.le).trans
      (graphCurve_le_point hy)
  have hmL : L ∈ m := (mem_vanishingIdeal_singleton_iff _ _).mpr hLy
  refine ⟨⟨inferInstance, sup_le hBm ((Ideal.span_singleton_le_iff_mem _).mpr hmL)⟩, ?_⟩
  intro Q hQ hQm
  let q := Q.comap (rename Fin.castSucc).toRingHom
  have hQsep : liftedSep f ∉ Q := fun h => hmsep (hQm h)
  let : Q.IsPrime := hQ.1
  let : q.IsPrime := hQ.1.comap _
  obtain ⟨hIq, hGQ⟩ := prime_of_chart T Q (le_sup_left.trans hQ.2) hQsep
  have hsq : sep f ∉ q := hQsep
  obtain ⟨P', hP', hP'q⟩ := Ideal.exists_mem_retainedMinimalPrimes_le (Q := q) hIq hsq
  have hP'f : P' ∈ factorCurves f := mem_factorCurves.mpr ⟨hProper, hP'⟩
  have hle : graphCurve f P' ≤ Q := by
    rw [← hGQ]
    exact vanishingIdeal_anti_mono
      (Set.image_mono fun _ hx => ⟨zeroLocus_anti_mono hP'q hx.1, hx.2⟩)
  obtain ⟨hp', hd⟩ := graph_is_curve hf hP'f
  have hLQ : Ideal.span {L} ≤ Q := le_sup_right.trans hQ.2
  have hcut := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp' (hL P' hP'f) le_rfl).1
  rw [hd, Nat.sub_self] at hcut
  have hdeg := (natDegree_affineHilbertPolynomial_le_of_le (sup_le hle hLQ)).trans hcut
  let : Module.Finite GeometricX (GeoRow 4 ⧸ Q) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero (Nat.eq_zero_of_le_zero hdeg)
  have hfield : IsField (GeoRow 4 ⧸ Q) :=
    isField_of_isIntegral_of_isField' (R := GeometricX) (Field.toIsField _)
  exact (Ideal.Quotient.maximal_of_isField Q hfield).eq_of_le
    (inferInstance : m.IsPrime).ne_top hQm |>.ge
theorem proof : Scalar70LeadingLower_1_1.c2 top := by
  intro f hf _ T L hL P hP y hy hLy
  have hJ : fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L =
      threeCut f T ⊔ Ideal.span {L} := by
    simp [fourCutIdeal, threeCut, graphIdeal, Ideal.span_insert, sup_assoc]
  dsimp only
  rw [hJ]
  refine ⟨point_isolated hf T hL hP hy hLy, ?_⟩
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let : P.IsPrime := hmin.isPrime
  let Q := graphCurve f P
  let : Q.IsPrime := (graph_is_curve hf hP).1
  have hQy : Q ≤ pointIdeal y := graphCurve_le_point hy
  have hLiftSep : liftedSep f ∉ Q := fun h => sep_notMem_point hy (hQy h)
  rw [componentLength, dite_eq_left hmin.isPrime]
  rw [chart_colength T P Q (threeCut_le_graphCurve T hmin.le) hLiftSep (graphCurve_comap hsep)]
  exact length_atPrime_le_length_principalCut hQy
    ((mem_vanishingIdeal_singleton_iff _ _).mpr hLy) (hL P hP)
end
end Scalar70LeadingLower_1_1_2
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Shape)
open Scalar70LeadingLower (lowBox liftedBox mixedCoefficients)
open K1_13_5_4_2 K1_13_5_4_2_5 K1_13_5_4_2_5_2
open MeasureTheory Set Filter
open scoped Topology Pointwise ENNReal BigOperators
open private K1_13_5_4_2_5_2_2.realCap shiftedCap shiftedCap_tendsto form form_apply form_fun
  bounds mem_realCap K1_13_5_4_2_5_2_2.support support_attains Pair nonparallel remaining slabMatrix slabRegion
  volume_slabRegion slabMatrix_invertible slabMap_apply
  from ProximityPrize.SubmissionLower.Fast070

private theorem mem_shifted {P : Set ExponentSpace} (h0 : 0 ∈ P)
    (hsub : P ⊆ capBody lowBox 0) {s : Shape} {h : ℕ} {t : ℝ} {x : ExponentSpace} :
    x ∈ shiftedCap P s h t ↔ x 3 ∈ Icc 0 (h : ℝ) ∧
      ∀ i, form i x ≤ bounds s i + t * K1_13_5_4_2_5_2_2.support P i := by
  rw [shiftedCap, mem_realCap]
  have hlow (i : Fin 6) (hi : 3 ≤ i.val) : K1_13_5_4_2_5_2_2.support P i = 0 := by
    have hzero : (0 : ℝ) ∈ form i '' P := ⟨0, h0, map_zero _⟩
    have hub : 0 ∈ upperBounds (form i '' P) := by
      rintro _ ⟨p, hp, rfl⟩
      have hn := (hsub hp).1
      fin_cases i <;> norm_num at hi
      all_goals simpa [form_apply] using hn _
    exact le_antisymm (csSup_le ⟨0, hzero⟩ hub) (le_csSup ⟨0, hub⟩ hzero)
  refine and_congr_right (fun _ => forall_congr' (fun i => ?_))
  fin_cases i
  · simp [bounds, K1_13_5_4_2_5_2_2.support, totalSupport, form_fun]
  · simp [bounds, K1_13_5_4_2_5_2_2.support, indexSupport, form_fun]
  · simp [bounds, K1_13_5_4_2_5_2_2.support, topSupport, form_fun]
  all_goals rw [hlow _ (by decide)]; simp [bounds]
private theorem form_bounded {P : Set ExponentSpace} (hsub : P ⊆ capBody lowBox 0)
    {x : ExponentSpace} (hx : x ∈ P) (i : Fin 6) : |form i x| ≤ 250 := by
  have hp := hsub hx
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have hb := hp.2.1
  change x 0 + x 1 + x 2 ≤ (lowBox.b : ℝ) at hb
  norm_num [lowBox] at hb
  rw [abs_le, form_apply]
  fin_cases i <;> simp <;> constructor <;> linarith
private theorem shiftedCap_error {P : Set ExponentSpace} (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0)
    (s : Shape) (h : ℕ) (htop : 0 < s.t) :
    ∃ K : ℝ, ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ),
      0 ≤ (volume (shiftedCap P s h t)).toReal - (volume (t • P + capBody s h)).toReal ∧
      (volume (shiftedCap P s h t)).toReal - (volume (t • P + capBody s h)).toReal ≤ K * t^2 := by
  have hc : IsCompact P := by
    obtain ⟨v, hv, rfl⟩ := hP.polytope
    exact hv.isCompact_convexHull ℝ
  choose pt hpt heq hmax using support_attains hc hP.zero_mem
  have hsup (i : Fin 6) : K1_13_5_4_2_5_2_2.support P i ≤ 250 :=
    (heq i).symm.trans_le ((le_abs_self _).trans (form_bounded hsub (hpt i) i))
  let R : ℝ := (s.b : ℝ) + (h : ℝ) + 250
  let coeff (p : Pair) : ℝ := |(slabMatrix p).det⁻¹| * 4 * R^2 * 250^2
  have hR : 0 ≤ R := by positivity
  refine ⟨∑ p, coeff p, ?_⟩
  have htop' : (0 : ℝ) < (s.t : ℝ) := by exact_mod_cast htop
  have hsmall : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), t < (s.t : ℝ) / 250 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (div_pos htop' (by norm_num : (0 : ℝ) < 250)))
  have hone : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0), hone, hsmall]
      with t ht ht1 hts
  have ht' : 0 < t := ht
  let e : ℝ := t * 250
  have he : 0 ≤ e := by positivity
  let S := shiftedCap P s h t
  let C := t • P + capBody s h
  let E := fun p : Pair => slabRegion (bounds s) R e p
  have hCS : C ⊆ S := by
    rintro x hx
    obtain ⟨w, hw, z, hz, rfl⟩ := mem_add.mp hx
    obtain ⟨y, hy, hwy⟩ := mem_smul_set.mp hw
    subst w
    have hz' := mem_realCap.mp (show z ∈ K1_13_5_4_2_5_2_2.realCap s.b s.j s.t h from hz)
    refine (mem_shifted hP.zero_mem hsub).mpr ⟨?_, fun i => ?_⟩
    · simpa [Pi.add_apply, Pi.smul_apply, hP.zero_height y hy] using hz'.1
    · rw [map_add, map_smul, smul_eq_mul]
      exact (add_le_add (mul_le_mul_of_nonneg_left (hmax i y hy) ht'.le) (hz'.2 i)).trans_eq
        (add_comm _ _)
  have hcube : S ⊆ Icc (0 : ExponentSpace) (fun _ => R) := by
    intro x hx
    obtain ⟨hn, hb, _, _, hh⟩ := (show x ∈ K1_13_5_4_2_5_2_2.realCap _ _ _ _ from hx)
    have htotal : totalSupport P = K1_13_5_4_2_5_2_2.support P 0 := by simp [totalSupport, K1_13_5_4_2_5_2_2.support, form_fun]
    have hbx : x 0 + x 1 + x 2 ≤ (s.b : ℝ) + t * 250 := by
      rw [htotal] at hb
      exact hb.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hsup 0) ht'.le) _)
    refine ⟨hn, fun i => ?_⟩
    have h0 := hn 0
    have h1 := hn 1
    have h2 := hn 2
    have hH : 0 ≤ (h : ℝ) := by positivity
    have hB : 0 ≤ (s.b : ℝ) := by positivity
    fin_cases i <;> dsimp [R] <;> linarith
  have hcover : S ⊆ C ∪ ⋃ p, E p := by
    intro x hx
    by_cases hxc : x ∈ C
    · exact Or.inl hxc
    have hb := (mem_shifted hP.zero_mem hsub).mp hx
    have hbase : x ∉ capBody s h := fun h =>
      hxc (mem_add.mpr ⟨0, ⟨0, hP.zero_mem, smul_zero _⟩, x, h, zero_add _⟩)
    have hviol : ¬ ∀ i, form i x ≤ bounds s i :=
      fun h => hbase (mem_realCap.mpr ⟨hb.1, h⟩)
    push Not at hviol
    obtain ⟨i, hi⟩ := hviol
    let y := x - t • pt i
    have hyh : y 3 ∈ Icc 0 (h : ℝ) := by
      simpa [y, Pi.sub_apply, Pi.smul_apply, hP.zero_height _ (hpt i)] using hb.1
    have hy : y ∉ capBody s h := fun h =>
      hxc (mem_add.mpr ⟨t • pt i, ⟨pt i, hpt i, rfl⟩, y, h, by dsimp [y]; abel⟩)
    have hother : ¬ ∀ j, form j y ≤ bounds s j :=
      fun h => hy (mem_realCap.mpr ⟨hyh, h⟩)
    push Not at hother
    obtain ⟨j, hj⟩ := hother
    have hshift (k : Fin 6) : form k y = form k x - t * form k (pt i) := by
      simp [y, smul_eq_mul]
    have hji : i ≠ j := by
      rintro rfl
      rw [hshift, heq] at hj
      linarith [hb.2 i]
    have hlo : bounds s j - e ≤ form j x := by
      have h := (abs_le.mp (form_bounded hsub (hpt i) j)).1
      rw [hshift] at hj
      dsimp [e]
      linarith [mul_le_mul_of_nonneg_left h ht'.le]
    have hhi (k : Fin 6) : form k x ≤ bounds s k + e :=
      (hb.2 k).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hsup k) ht'.le) _)
    have hpar : nonparallel (i, j) := by
      refine ⟨?_, hji, ?_⟩
      · have hn : ∀ k : Fin 4, 0 ≤ x k := (hcube hx).1
        fin_cases i <;> norm_num [bounds, form_apply] at hi ⊢
        · exact (not_lt_of_ge (hn 0)) hi
        · exact (not_lt_of_ge (hn 1)) hi
        · exact (not_lt_of_ge (hn 2)) hi
      · by_contra hn
        push Not at hn
        obtain ⟨rfl, rfl⟩ := hn
        simp [bounds, form_apply] at hi hlo
        linarith [show e < (s.t : ℝ) from (lt_div_iff₀ (by norm_num : (0 : ℝ) < 250)).mp hts]
    refine Or.inr (mem_iUnion.mpr ⟨(i,j), ?_⟩)
    change x ∈ slabRegion _ _ _ _
    simp only [slabRegion, hpar, ↓reduceIte, mem_preimage, slabMap_apply]
    have hxl := (hcube hx).1
    have hxu := (hcube hx).2
    constructor <;> intro k <;> fin_cases k
    · exact (sub_le_self _ he).trans hi.le
    · exact hlo
    · exact hxl (remaining (i, j))
    · exact hxl 3
    · exact hhi i
    · exact hhi j
    · exact hxu (remaining (i, j))
    · exact hxu 3
  have hevol : volume (⋃ p, E p) ≤ ENNReal.ofReal ((∑ p, coeff p) * t^2) := by
    calc
      _ ≤ ∑ p, volume (E p) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ p, ENNReal.ofReal (coeff p * t^2) := by
        apply Finset.sum_le_sum
        intro p _
        have h := volume_slabRegion (bounds s) hR he p
        convert h using 2
        dsimp [coeff, e]
        ring
      _ = _ := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  have hS : volume S ≠ ∞ := measure_ne_top_of_subset hcube isCompact_Icc.measure_ne_top
  have hC : volume C ≠ ∞ := measure_ne_top_of_subset hCS hS
  have hevol' : volume S ≤ volume C + ENNReal.ofReal ((∑ p, coeff p) * t^2) :=
    (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add_right hevol _))
  constructor
  · exact sub_nonneg.mpr (ENNReal.toReal_mono hS (measure_mono hCS))
  · have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hC, ENNReal.ofReal_ne_top⟩) hevol'
    rw [ENNReal.toReal_add hC ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h
    exact sub_le_iff_le_add'.mpr h
theorem volume_variation (P : Set ExponentSpace) (hP : FirstBody P)
    (hsub : P ⊆ capBody lowBox 0) (s : Shape) (h : ℕ)
    (hs : Chamber s) (hjb : s.j < s.b) (htop : 0 < s.t) :
    Tendsto (volumeQuotient P (capBody s h)) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (capFirstVariation s h (totalSupport P) (indexSupport P) (topSupport P))) := by
  obtain ⟨K, hK⟩ := shiftedCap_error hP hsub s h htop
  let f := fun t : ℝ =>
    ((volume (shiftedCap P s h t)).toReal - (volume (capBody s h)).toReal) / t
  have hupper := shiftedCap_tendsto P s h hs hjb htop
  have hzero : Tendsto (fun t : ℝ => K * t) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.const_mul K
  have hlower : Tendsto (fun t => f t - K * t) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (capFirstVariation s h (totalSupport P) (indexSupport P) (topSupport P))) := by
    simpa using hupper.sub hzero
  apply hlower.squeeze' hupper
  · filter_upwards [hK, eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht htpos
    have hpos : 0 < t := htpos
    have he := (div_le_iff₀ hpos).mpr (show _ ≤ K * t * t by
      simpa only [pow_two, mul_assoc] using ht.2)
    have hd : f t - volumeQuotient P (capBody s h) t =
        ((volume (shiftedCap P s h t)).toReal -
          (volume (t • P + capBody s h)).toReal) / t := by
      unfold f volumeQuotient
      rw [← sub_div]
      congr 1
      ring
    linarith
  · filter_upwards [hK, eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht htpos
    have hpos : 0 < t := htpos
    exact div_le_div_of_nonneg_right (by linarith [ht.1]) hpos.le
end
end Scalar70LeadingLower_1_1_3
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Shape)
open Scalar70LeadingLower (lowBox graphBox liftedBox mixedCoefficients)
open K1_13_5_4_2 (ExponentSpace capBody mixedVolume4)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation
  volumeQuotient rest univ_eq_insert zero_notMem_rest)
open K1_13_5_4_2_5_2_1 (cap_polytope closedOrthant)
open Scalar70LeadingPrice (taylorLength)
open Scalar70LeadingLower_1_1 (lastBox lastMixedVolume)
open MeasureTheory Filter MvPolynomial
open scoped BigOperators Pointwise Topology
open private K1_13_5_4_2_5.sumShape sumChamber sum_capBody capBody_zero from ProximityPrize.SubmissionLower.Fast048
open private labelHull_eq positivePolynomial from ProximityPrize.SubmissionLower.Fast071
open private weights polar_linear from ProximityPrize.SubmissionLower.Fast048
open private volume_zero_height from ProximityPrize.SubmissionLower.Fast048
end
end Scalar70LeadingLower_1_1_3
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Shape)
open Scalar70LeadingLower (lowBox liftedBox mixedCoefficients)
open K1_13_5_4_2 (ExponentSpace capBody)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation rest)
open Scalar70LeadingLower (mixedBudget)
open Scalar70LeadingLower_1_1 (lastMixedVolume)
open scoped BigOperators





end
end Scalar70LeadingLower_1_1_3
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Row indexDegree)
open Scalar70LeadingLower (lowBox liftedBox mixedCoefficients)
open K1_13_5_4 (genericRow liftRow)
open K1_13_5_4_2 (ExponentSpace downBody capBody)
open K1_13_5_4_2_5 (FirstBody firstBody_zero firstBody_row)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport)
open Scalar70LeadingLower (SecondFactors mixedBudget)
open Scalar70LeadingLower_1_1 (lastMixedVolume)
open MvPolynomial
open scoped BigOperators Pointwise
open private rowShape row_support downBody_subset from ProximityPrize.SubmissionLower.Fast048
end
end Scalar70LeadingLower_1_1_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Scalar70LeadingLower_1_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5 (compatibilityNumerator separant tangentNumerator)
open K1_13_5_4 (GeoRow genericRow genericCoeff genericCoeff_injective)
open K1_13_5_4_3 (TangentStable)
open K1_13_5_4_3_1 (tangentNumerator_add tangentNumerator_mul)
open Scalar70LeadingPrice (taylorLength)
open Scalar70LeadingLower (Whole)
open Scalar70LeadingLower_1 (oldCut oldNext oldCutIdeal componentLength SimpleInvariant)
open Polynomial
open private flat_rowToGeo rowToGeo_eq tangent_self from ProximityPrize.SubmissionLower.Fast048
open private generic_cut_regular from ProximityPrize.SubmissionLower.Fast074
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end Scalar70LeadingLower_1_2
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_3
noncomputable section
variable {top : Fin 1}
open K1_13_5_4 (GeometricX)
open MvPolynomial
open scoped BigOperators
open private restrictVariables restrict_rename padded_hilbert sum_monomial_eq_of_tail_zero
  from ProximityPrize.SubmissionLower.PortLow5
end
end Scalar70LeadingLower_1_3
end
section
set_option autoImplicit false
namespace Scalar70LeadingLower_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom Row embed)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX extendedAtJet)
open K1_13_5_4_4
open Scalar70LeadingPrice (taylorLength)
open Scalar70LeadingLower (Whole invariantBudget)
open Scalar70LeadingLower_1 (CoefficientIdeal ActualSolutionCurve coefficientPolynomial oldCut)
open MvPolynomial Finset
open scoped BigOperators Polynomial
open private flat_of_injective regular_cut_of_flat_map from ProximityPrize.SubmissionLower.Fast067
open private curve_minimal from ProximityPrize.SubmissionLower.Fast067
end
end Scalar70LeadingLower_1_3
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace Scalar70LeadingLower_2
noncomputable section
variable {top : Fin 1}
open K1 (K I node)
open Scalar70LeadingPrice (Messages)
open K1_13 (Geom embed extend taylorLength)
open K1_13_5 (NodeCapacity)
open K1_13_5_5 (CoeffRing CoeffIndex coeffPoint)
open Finset MvPolynomial
open scoped BigOperators Polynomial
open private valueCut valueCut_degree valueCut_eval nodeCapacity_of_sections
  curve_degree_nat from ProximityPrize.SubmissionLower.Fast064
end
end Scalar70LeadingLower_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Scalar70LeadingLower_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom embed Row atJet)
open K1_13_5 (RegularAt separant compatibilityNumerator)
open K1_13_5_5 K1_13_5_5_1
open Scalar70LeadingPrice (taylorLength physicalDegree TrueWeightLE anchorCutoff)
open Scalar70LeadingLower (Whole)
open scoped Polynomial
open private chart_trajectory from ProximityPrize.SubmissionLower.PortLow5
end
end Scalar70LeadingLower_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Scalar70LeadingLower_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom)
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open Scalar70LeadingPrice (physicalDegree)
open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open private monic_chart_aux from ProximityPrize.SubmissionLower.Fast064
open private commonFactor_monic trimmedValue_monic trimmedValue_dvd from ProximityPrize.SubmissionLower.Fast064
open private eval_divisions from ProximityPrize.SubmissionLower.PortLow5
end
end Scalar70LeadingLower_2
end
section
set_option maxHeartbeats 1000000
namespace Scalar70LeadingLower_2
noncomputable section
variable {top : Fin 1}
open K1 (K)
open Scalar70LeadingLower (Whole)
open K1_13 (Row Geom extend)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open K1_13_5_5 (freshRow FreshField)
open Finset MvPolynomial
open scoped BigOperators Polynomial
end
end Scalar70LeadingLower_2
end

namespace Scalar70LeadingLower
variable {top : Fin 1}

end Scalar70LeadingLower
