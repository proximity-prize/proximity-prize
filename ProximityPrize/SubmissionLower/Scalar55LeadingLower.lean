import ProximityPrize.SubmissionLower.Scalar55LeadingLowerBase
import ProximityPrize.SubmissionLower.Fast074

set_option Elab.async false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit true

section
namespace Scalar55LeadingLower_1
noncomputable section
variable {top : Fin 1}
open K1 (I K)
open Scalar55LeadingPrice (Messages taylorLength physicalDegree)
open Scalar55LeadingLower (ProperCover SecondFactors Whole mixedBudget invariantBudget)
open K1_13 (Row Geom atJet extend)
open K1_13_5 (RegularAt NodeFamily separant)
open K1_13_5_4 (GeometricX GeoRow genericRow genericCoeff genericCoeff_injective
  jetPoint regularLocus eval_genericRow_at_point jetPoint_injOn)
open Polynomial
open scoped BigOperators
def c2 (top : Fin 1) : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors top f → ∀ a ∈ properComponents f,
    SimpleInvariant (f a.1) a.2 →
    ∃ Q : CoefficientIdeal, ActualSolutionCurve (f a.1) Q ∧
      ∀ S : Geom[X], S.natDegree ≤ physicalDegree → jetPoint S ∈ regularLocus (f a.1) a.2 →
        coefficientPoint S ∈ MvPolynomial.zeroLocus GeometricX Q
def c3 (top : Fin 1) : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∀ i, (oldCut (f i)).totalDegree ≤
      1 + (2 * (taylorLength + 1) - 7) * ((f i).totalDegree - 1)) →
    ∀ C : Finset CoefficientIdeal,
      (∀ Q ∈ C, ∃ i, ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q) →
      ∃ d : CoefficientIdeal → ℕ,
        (∀ Q ∈ C, 0 < d Q ∧ MvPolynomial.affineDegree Q ≤ (d Q : ℚ)) ∧
          (∑ Q ∈ C, d Q) ≤ (invariantBudget top)
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
private def componentMarks {n : ℕ} (f : Fin n → Row 3)
    (Γ : Finset K) (s : K → K[X]) (a : CurveIndex n) : Finset K := by
  classical
  exact Γ.filter fun γ => jetPoint (extend (s γ)) ∈ regularLocus (f a.1) a.2
private theorem mem_componentMarks {n : ℕ} {f : Fin n → Row 3} {Γ : Finset K}
    {s : K → K[X]} {a : CurveIndex n} {γ : K} : γ ∈ componentMarks f Γ s a ↔
    γ ∈ Γ ∧ jetPoint (extend (s γ)) ∈ regularLocus (f a.1) a.2 := by
  classical
  exact Finset.mem_filter
private theorem regular_of_componentMark {n : ℕ} {f : Fin n → Row 3} {a : CurveIndex n}
    {S : Geom[X]} (ha : a ∈ properComponents f) (hS : jetPoint S ∈ regularLocus (f a.1) a.2) :
    RegularAt 2 (f a.1) S := by
  have hp := (Ideal.mem_retainedMinimalPrimes.mp (mem_properComponents.mp ha).2).1.le
  have hz : genericRow (f a.1) ∈ oldCutIdeal (f a.1) := Ideal.subset_span (by simp)
  have he : MvPolynomial.eval (jetPoint S) (genericRow (f a.1)) = 0 :=
    hS.1 _ (hp hz)
  have hsep := hS.2
  rw [eval_genericRow_at_point] at he hsep
  refine ⟨?_, fun h => hsep (by rw [show atJet (separant (f a.1)) S = 0 from h, map_zero])⟩
  exact (map_eq_zero_iff genericCoeff genericCoeff_injective).mp he
private theorem mixedComponent_card {w Γ s n f} (hm : Messages w Γ s)
    {T : ∀ i, LiftedChart top (f i)} (M : MixedSections top (n := n) f T)
    {a : CurveIndex n} (ha : a ∈ properComponents f) (hi : ¬ SimpleInvariant (f a.1) a.2) :
    (componentMarks f Γ s a).card ≤ M.length a * M.degree a := by
  classical
  have hsub : componentMarks f Γ s a ⊆ Γ := fun _ hg => (mem_componentMarks.mp hg).1
  have hdeg (γ : K) (hγ : γ ∈ Γ) : (extend (s γ)).natDegree ≤ physicalDegree := by
    simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
  by_cases hlen : M.length a = 1
  · have hsimp : componentLength (f a.1) a.2 = 1 := by rw [← M.length_eq a ha, hlen, Nat.cast_one]
    have hn : genericRow (oldNext (f a.1)) ∉ a.2 := fun hn => hi ⟨hsimp, hn⟩
    obtain ⟨hfinite, hcard⟩ := M.points a ha hn
    let pt := fun γ => jetPoint (n := 3) (extend (s γ))
    have hpts : ↑((componentMarks f Γ s a).image pt) ⊆ nextCutLocus (f a.1) a.2 := by
      intro y hy
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hmem, hy⟩ := mem_componentMarks.mp hγ
      have hreg := regular_of_componentMark ha hy
      exact ⟨hy, by rw [eval_genericRow_at_point, ((T a.1).actual _ (hdeg γ hmem) hreg).2.1, map_zero]⟩
    have hle := (Set.ncard_le_ncard hpts hfinite).trans hcard
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn ((jetPoint_injOn s Γ hm.distinct).mono hsub)] at hle
    simpa [hlen] using hle
  · have htwo : 2 ≤ M.length a := by have := M.length_pos a ha; omega
    obtain ⟨Q, hprime, hdim, hd, hdegree, hrec⟩ := M.curves a ha htwo
    have hm' := hm.mono hsub
    have hcap := nodeCapacity_of_coefficient_curve hm' Q hprime hdim hdegree (by
      intro γ hγ
      obtain ⟨hmem, hy⟩ := mem_componentMarks.mp hγ
      have hreg := regular_of_componentMark ha hy
      rw [← ((T a.1).actual _ (hdeg γ hmem) hreg).2.2]
      exact hrec _ hy)
    exact (curveCount_le_twice_degree hm' hd hcap).trans (Nat.mul_le_mul_right _ htwo)
private def coefficientFamily {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ)
    (hcut : ∀ Q ∈ C, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      MvPolynomial.affineDegree Q ≤ (d Q : ℚ)) : NodeFamily w Γ s := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  let part : Fin C.card → Finset K := fun i => Γ.filter fun γ =>
    coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX (e i).val
  have hs : ∀ i, part i ⊆ Γ := fun _ => Finset.filter_subset _ _
  refine ⟨C.card, part, fun i => d (e i).val, hs, ?_⟩
  intro i
  obtain ⟨hp, hdim, hd⟩ := hcut (e i).val (e i).property
  exact nodeCapacity_of_coefficient_curve (hm.mono (hs i)) (e i).val hp hdim hd
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
private theorem coefficientFamily_total {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ) (hcut) :
    (coefficientFamily hm C d hcut).totalCap = ∑ Q ∈ C, d Q := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  change (∑ i : Fin C.card, d (e i).val) = ∑ Q ∈ C, d Q
  rw [Equiv.sum_comp e (fun P : C => d P.val), Finset.sum_coe_sort]
private theorem mem_coefficientFamily {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ) (hcut) {γ : K} (hγ : γ ∈ Γ)
    {Q : CoefficientIdeal} (hQ : Q ∈ C)
    (hy : coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX Q) :
    γ ∈ (coefficientFamily hm C d hcut).labels := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  rw [NodeFamily.labels]
  let i := e.symm ⟨Q, hQ⟩
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, ?_⟩⟩
  change coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX (e i).val
  simpa [i] using hy
end
end Scalar55LeadingLower_1
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5 (separant)
open Scalar55LeadingLower (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow GeometricX genericRow)
open K1_13_5_4_2 (JetPoint ExponentSpace boxExponents graphLocus graphCurve capBody mixedVolume4)
open Scalar55LeadingPrice (taylorLength)
open Scalar55LeadingLower (Whole)
open Scalar55LeadingLower_1 (oldCutIdeal)
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
end Scalar55LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Row Geom Shape)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericCoeff_injective genericRow
  liftRow regularLocus graphPoint)
open K1_13_5_4_2 (boxExponents graphCurve eval_represents_iff)
open Scalar55LeadingPrice (taylorLength)
open Scalar55LeadingLower (Whole)
open Scalar55LeadingLower_1 (oldCut oldCutIdeal properComponents CurveIndex componentLength nextCutLocus
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
end Scalar55LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open Scalar55LeadingLower (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow)
open K1_13_5_4_2 (JetPoint fourCutIdeal pointIdeal pointLength downBody capBody)
open K1_13_5_4_2_4 (Exponent Downward cutIdeal downSupport capSupport mem_downSupport mem_capSupport
  latticeBody latticeBody_downSupport latticeBody_capSupport)
open Scalar55LeadingPrice (taylorLength)
open MvPolynomial
open scoped BigOperators Pointwise
open private mixed_eq_generic downSupport_downward capSupport_downward zero_mem_capSupport
  from ProximityPrize.SubmissionLower.Fast048
end
end Scalar55LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Row Shape indexDegree)
open K1_13_5 (separant)
open Scalar55LeadingLower (lowBox liftedBox mixedCoefficients)
open K1_13_5_4 (InLiftedBox GeometricX GeoRow genericRow liftRow graphPoint regularLocus)
open K1_13_5_4_2 (graphLocus JetPoint eval_liftRow_graphPoint)
open Scalar55LeadingPrice (taylorLength)
open Scalar55LeadingLower (SecondFactors)
open Scalar55LeadingLower_1 (LiftedChart reconstruct CoefficientIdeal)
open MvPolynomial
open scoped BigOperators Pointwise
open private ratio_image_degree box_mono from ProximityPrize.SubmissionLower.Fast048
end
end Scalar55LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5_4 (GeoRow genericRow liftRow graph)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal pointLength downBody
  localLength_lt_top)
open Scalar55LeadingLower (SecondFactors mixedBudget)
open Scalar55LeadingLower_1 (LiftedChart CurveIndex properComponents componentLength)
open MvPolynomial
open scoped BigOperators
open private lift_generic_ne_zero from ProximityPrize.SubmissionLower.Fast048
end
end Scalar55LeadingLower_1_1
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1_1
noncomputable section
variable {top : Fin 1}
open K1_13_5_4 (GeoRow GeometricX InLiftedBox)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve)
open K1_13_5_4_2_2 (linearForm fiberIdeal totalDegree_hyperplane_le_one zeroLocus_fiber_iff
  ncard_eq_affineDegree_of_radical)
open Scalar55LeadingPrice (taylorLength)
open Scalar55LeadingLower_1_1 (factorCurves lastBox lastExponents lastMap sectionIdeal sectionDegree)
open MvPolynomial
open scoped Pointwise
end
end Scalar55LeadingLower_1_1_1
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5 (lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow graph graphIdeal)
open Scalar55LeadingLower_1 (LiftedChart oldCutIdeal)
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
end Scalar55LeadingLower_1_1_2
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Shape)
open Scalar55LeadingLower (lowBox liftedBox mixedCoefficients)
open K1_13_5_4_2 K1_13_5_4_2_5 K1_13_5_4_2_5_2
open MeasureTheory Set Filter
open scoped Topology Pointwise ENNReal BigOperators
open private K1_13_5_4_2_5_2_2.realCap shiftedCap shiftedCap_tendsto form form_apply form_fun
  bounds mem_realCap K1_13_5_4_2_5_2_2.support support_attains Pair nonparallel remaining slabMatrix slabRegion
  volume_slabRegion slabMatrix_invertible slabMap_apply
  from ProximityPrize.SubmissionLower.Fast070

end
end Scalar55LeadingLower_1_1_3
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Shape)
open Scalar55LeadingLower (lowBox graphBox liftedBox mixedCoefficients)
open K1_13_5_4_2 (ExponentSpace capBody mixedVolume4)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation
  volumeQuotient rest univ_eq_insert zero_notMem_rest)
open K1_13_5_4_2_5_2_1 (cap_polytope closedOrthant)
open Scalar55LeadingPrice (taylorLength)
open Scalar55LeadingLower_1_1 (lastBox lastMixedVolume)
open MeasureTheory Filter MvPolynomial
open scoped BigOperators Pointwise Topology
open private K1_13_5_4_2_5.sumShape sumChamber sum_capBody capBody_zero from ProximityPrize.SubmissionLower.Fast048
open private labelHull_eq positivePolynomial from ProximityPrize.SubmissionLower.Fast071
open private weights polar_linear from ProximityPrize.SubmissionLower.Fast048
open private volume_zero_height from ProximityPrize.SubmissionLower.Fast048
end
end Scalar55LeadingLower_1_1_3
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Shape)
open Scalar55LeadingLower (lowBox liftedBox mixedCoefficients)
open K1_13_5_4_2 (ExponentSpace capBody)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation rest)
open Scalar55LeadingLower (mixedBudget)
open Scalar55LeadingLower_1_1 (lastMixedVolume)
open scoped BigOperators





end
end Scalar55LeadingLower_1_1_3
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Row indexDegree)
open Scalar55LeadingLower (lowBox liftedBox mixedCoefficients)
open K1_13_5_4 (genericRow liftRow)
open K1_13_5_4_2 (ExponentSpace downBody capBody)
open K1_13_5_4_2_5 (FirstBody firstBody_zero firstBody_row)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport)
open Scalar55LeadingLower (SecondFactors mixedBudget)
open Scalar55LeadingLower_1_1 (lastMixedVolume)
open MvPolynomial
open scoped BigOperators Pointwise
open private rowShape row_support downBody_subset from ProximityPrize.SubmissionLower.Fast048
end
end Scalar55LeadingLower_1_1_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Scalar55LeadingLower_1_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Row)
open K1_13_5 (compatibilityNumerator separant tangentNumerator)
open K1_13_5_4 (GeoRow genericRow genericCoeff genericCoeff_injective)
open K1_13_5_4_3 (TangentStable)
open K1_13_5_4_3_1 (tangentNumerator_add tangentNumerator_mul)
open Scalar55LeadingPrice (taylorLength)
open Scalar55LeadingLower (Whole)
open Scalar55LeadingLower_1 (oldCut oldNext oldCutIdeal componentLength SimpleInvariant)
open Polynomial
open private flat_rowToGeo rowToGeo_eq tangent_self from ProximityPrize.SubmissionLower.Fast048
open private generic_cut_regular from ProximityPrize.SubmissionLower.Fast074
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem map_eq_maximal_of_length_one (f : Row 3) (P : Ideal (GeoRow 3))
    [P.IsPrime] (h : componentLength f P = 1) :
    (oldCutIdeal f).map (algebraMap (GeoRow 3) (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  classical
  unfold componentLength at h
  rw [dite_eq_left ‹P.IsPrime›, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at h
  exact h
private theorem simple_saturation (f : Row 3) (P : Ideal (GeoRow 3))
    [P.IsPrime] (h : componentLength f P = 1) (x : Row 3) (hx : genericRow x ∈ P) :
    ∃ s : Row 3, genericRow s ∉ P ∧ s * x ∈ Ideal.span {f, oldCut f} := by
  let q := P.comap (algebraMap (Row 3) (GeoRow 3))
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : P.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime P
  let _ : Algebra A B := Localization.AtPrime.algebraOfLiesOver q P
  have : Module.Flat (Row 3) (GeoRow 3) := flat_rowToGeo
  have : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q P (algebraMap (Row 3) (GeoRow 3)) rfl)
    infer_instance
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let J : Ideal (Row 3) := Ideal.span {f, oldCut f}
  have hJ : J.map (algebraMap (Row 3) (GeoRow 3)) = oldCutIdeal f := by
    simp only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, rowToGeo_eq,
      oldCutIdeal]
  have hJB : (J.map (algebraMap (Row 3) A)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq (Row 3) A B,
      IsScalarTower.algebraMap_eq (Row 3) (GeoRow 3) B, ← Ideal.map_map, hJ]
    exact map_eq_maximal_of_length_one f P h
  have hxB : algebraMap A B (algebraMap (Row 3) A x) ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsScalarTower.algebraMap_apply (Row 3) A B,
      IsScalarTower.algebraMap_apply (Row 3) (GeoRow 3) B, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (by rwa [rowToGeo_eq])
  rw [← hJB] at hxB
  have hxA : algebraMap (Row 3) A x ∈ J.map (algebraMap (Row 3) A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J.map (algebraMap (Row 3) A))]
    exact hxB
  obtain ⟨s, hs, hsx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A J x).mp hxA
  refine ⟨s, ?_, hsx⟩
  change algebraMap (Row 3) (GeoRow 3) s ∉ P at hs
  rwa [rowToGeo_eq] at hs
private theorem numerator_succ (f : Row 3) (P : Ideal (GeoRow 3)) (j : ℕ)
    (hj : genericRow (compatibilityNumerator f j) ∈ P) :
    genericRow (compatibilityNumerator f (j + 1)) ∈ P ↔
      genericRow (separant f) * genericRow (tangentNumerator f (compatibilityNumerator f j)) ∈ P := by
  have hterm :
      genericRow (((2 * j + 1 : ℕ) : Row 3) * compatibilityNumerator f j *
        tangentNumerator f (separant f)) ∈ P := by
    simp only [genericRow, map_mul]
    exact P.mul_mem_right _ (P.mul_mem_left _ hj)
  change (MvPolynomial.map genericCoeff) (_ - _) ∈ P ↔ _
  unfold genericRow at hterm ⊢
  rw [map_sub, P.sub_mem_iff_left hterm, map_mul]
theorem tangent_stable {f : Row 3} {P : Ideal (GeoRow 3)} (hp : P.IsPrime)
    (hle : oldCutIdeal f ≤ P) (hsep : genericRow (separant f) ∉ P)
    (hInv : SimpleInvariant f P) : TangentStable f P := by
  let := hp
  have hf : genericRow f ∈ P := hle (Ideal.subset_span (by simp))
  have hc : genericRow (oldCut f) ∈ P := hle (Ideal.subset_span (by simp))
  have hprod := (numerator_succ f P (taylorLength - 3) hc).mp hInv.2
  have hcut := (hp.mem_or_mem hprod).resolve_left hsep
  have hgen : ∀ z ∈ (Ideal.span {f, oldCut f} : Ideal (Row 3)),
      genericRow (tangentNumerator f z) ∈ P := by
    intro z hz
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hz
    rw [tangentNumerator_add, tangentNumerator_mul, tangentNumerator_mul, tangent_self,
      mul_zero, add_zero]
    simp only [genericRow, map_add, map_mul]
    exact P.add_mem (P.mul_mem_left _ hf)
      (P.add_mem (P.mul_mem_left _ hc) (P.mul_mem_left _ hcut))
  intro x hx
  obtain ⟨s, hs, hsx⟩ := simple_saturation f P hInv.1 x hx
  have hd := hgen (s * x) hsx
  rw [tangentNumerator_mul] at hd
  simp only [genericRow, map_add, map_mul] at hd
  change genericRow (tangentNumerator f s) * genericRow x +
    genericRow s * genericRow (tangentNumerator f x) ∈ P at hd
  have hz := P.sub_mem hd (P.mul_mem_left (genericRow (tangentNumerator f s)) hx)
  rw [add_sub_cancel_left] at hz
  exact (hp.mem_or_mem hz).resolve_left hs
theorem numerator_mem {f : Row 3} {P : Ideal (GeoRow 3)} (h : TangentStable f P)
    (hc : genericRow (oldCut f) ∈ P) {j : ℕ} (hj : taylorLength - 3 ≤ j) :
    genericRow (compatibilityNumerator f j) ∈ P := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  clear hj
  induction i with
  | zero => exact hc
  | succ i hi =>
    exact (numerator_succ f P _ hi).mpr (P.mul_mem_left _ (h _ hi))
theorem component_dimension {f : Row 3} {P : Ideal (GeoRow 3)}
    (hf : Irreducible f) (hwhole : ¬ Whole f)
    (hP : P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))) :
    (MvPolynomial.affineHilbertPolynomial P).natDegree = 1 := by
  let F := genericRow f
  let G := genericRow (oldCut f)
  have hF : F ≠ 0 := by
    simpa only [F, genericRow, map_zero] using
      (MvPolynomial.map_injective _ genericCoeff_injective).ne hf.ne_zero
  have hregular := generic_cut_regular hf (show ¬ f ∣ oldCut f from hwhole)
  have hmin := (Ideal.mem_retainedMinimalPrimes.mp hP).1
  change P ∈ (Ideal.span {F, G}).minimalPrimes at hmin
  rw [Ideal.span_insert] at hmin
  have hp := hmin.isPrime
  obtain ⟨D, hD, hDP⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hmin.le)
  have hd := hD.isPrime
  have hFD : F ∈ D := hD.le (Ideal.mem_span_singleton_self F)
  have hDne : D ≠ ⊥ := fun h => hF (Ideal.mem_bot.mp (h ▸ hFD))
  have hDheight : D.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hD)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hDne))
  obtain ⟨a, ha⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hDheight).principal
  change D = Ideal.span {a} at ha
  have hGD : G ∉ D := by
    intro hG
    obtain ⟨b, hFb⟩ := Ideal.mem_span_singleton.mp (ha ▸ hFD)
    obtain ⟨c, hGc⟩ := Ideal.mem_span_singleton.mp (ha ▸ hG)
    have hb0 : b ≠ 0 := by
      intro hb
      exact hF (by simp [hFb, hb])
    have hdiv : F ∣ G * b := ⟨c, by rw [hGc, hFb, mul_right_comm]⟩
    obtain ⟨q, hq⟩ := hregular b hdiv
    have hb : b * (a * q) = b * 1 := by
      calc
        b * (a * q) = (a * b) * q := by rw [← mul_assoc, mul_comm b a]
        _ = b := by rw [← hFb, ← hq]
        _ = b * 1 := (mul_one _).symm
    have haUnit := IsUnit.of_mul_eq_one q (mul_left_cancel₀ hb0 hb)
    exact hd.ne_top (ha.trans (Ideal.span_singleton_eq_top.mpr haUnit))
  have hcut : P ∈ (D ⊔ Ideal.span {G}).minimalPrimes :=
    ⟨⟨hp, sup_le hDP (le_sup_right.trans hmin.le)⟩, fun J hJ hJP =>
      hmin.2 ⟨hJ.1, sup_le (hD.le.trans (le_sup_left.trans hJ.2))
        (le_sup_right.trans hJ.2)⟩ hJP⟩
  have hsurface :=
    MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
  rw [Nat.card_fin] at hsurface
  have hcurve := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hGD hcut
  omega
end
end Scalar55LeadingLower_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Scalar55LeadingLower_1_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Row Geom)
open K1_13_5 (separant)
open K1_13_5_4 (GeoRow GeometricX genericRow regularLocus extendedAtJet)
open K1_13_5_4_3 (TangentStable trajectory pointEval taylorAt)
open K1_13_5_4_3_2
open Scalar55LeadingPrice (physicalDegree taylorLength TrueWeightLE anchorCutoff)
open Scalar55LeadingLower_1 (oldCut oldCutIdeal)
open Polynomial
open private fresh_identity initial_residual from ProximityPrize.SubmissionLower.Fast073
open private specialize specialize_trajectory specialize_taylor from ProximityPrize.SubmissionLower.Fast073
private theorem trajectory_degree {A : Type*} [CommRing A] (k : Geom →+* A) (f : Row 3)
    (U : A[X]) (hU : U.natDegree ≤ physicalDegree) {D : ℕ} (hf : TrueWeightLE f D) :
    (trajectory k f U).natDegree ≤ D := by
  classical
  rw [trajectory, MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => (natDegree_mul_le).trans ?_
  apply le_trans _ (hf m hm)
  apply Nat.add_le_add natDegree_map_le
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le _ _).trans
    (Nat.sub_le_sub_right hU _)) |>.trans_eq (Nat.mul_comm _ _)
theorem stable_taylor {f : Row 3} {P : Ideal (GeoRow 3)}
    (hf : TrueWeightLE f anchorCutoff) (hc : oldCutIdeal f ≤ P)
    (h : TangentStable f P) {y : Fin 3 → GeometricX} (hy : y ∈ regularLocus f P) :
    (taylorAt f (pointEval y)).natDegree ≤ physicalDegree ∧
      extendedAtJet f (taylorAt f (pointEval y)) = 0 := by
  have hrow : genericRow f ∈ P := hc (Ideal.subset_span (by simp))
  have hcut : genericRow (oldCut f) ∈ P := hc (Ideal.subset_span (by simp))
  have hold : K1_13_5_4.oldCutIdeal f ≤ P := by
    apply Ideal.span_le.mpr
    intro b hb
    rcases (show b = genericRow f ∨ b = genericRow (K1_13_5_4.oldCut f) by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb) with rfl | rfl
    · exact hrow
    · exact numerator_mem h hcut (by change 131069 ≤ 133669; decide)
  have hU : (localTaylor f P).natDegree ≤ physicalDegree := by
    rw [localTaylor, natDegree_taylor, natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hsmall : 3 ≤ j := by
      change 131071 < j at hj
      omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hsmall
    rw [Nat.add_comm 3 n, centred, coeff_jetPolynomial]
    have hn : taylorLength - 3 ≤ n := by
      change 131071 < 3 + n at hj
      change 131069 ≤ n
      omega
    have hz : localJet f P (n + 3) = 0 := by
      rw [localJet, chart_zero f P (numerator_mem h hcut hn), mul_zero, zero_mul, zero_mul]
    split_ifs with hj'
    · exact hz
    · rfl
  refine ⟨by rw [← specialize_taylor hy]; exact natDegree_map_le.trans hU, ?_⟩
  have hOne : delta h (1 : Chart f P) = 0 := by
    simpa only [map_one] using delta_constants h (1 : Geom)
  have hShift : taylor (chartEval f P (MvPolynomial.C Polynomial.X)) (localTaylor f P) =
      centred f P := by
    rw [localTaylor, taylor_taylor, add_neg_cancel, taylor_zero]
  have hidentity := fresh_identity (delta h) hOne (delta_mul h) (constants (chartEval f P))
    (delta_constants h) _ (delta_centre h) f (localTaylor f P) (centred f P) hShift
    (centred_step h hold) (initial_residual hold)
    ((trajectory_degree _ _ _ hU hf).trans_lt (by change 9893179 < 0x7f000001; decide))
    (fun n hn hp => by
      rw [← map_natCast (constants (chartEval f P))]
      exact (natCast_geom_ne_zero hn hp).isUnit.map _)
  rw [← specialize_trajectory hy, hidentity, Polynomial.map_zero]
end
end Scalar55LeadingLower_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Scalar55LeadingLower_1_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom)
open K1_13_5 (RegularAt separant)
open K1_13_5_4 (GeoRow GeometricX extendedAtJet genericCoeff genericCoeff_injective
  genericRow jetPoint regularLocus eval_genericRow_at_point)
open K1_13_5_4_3 (coefficientImage coefficientPolynomial_reconstructAt curveIdeal
  eval_trajectory_at_centre pointEval reconstructAt reconstructAt_mark regularLocus_nonempty
  solves_on_closure taylorAt)
open K1_13_5_4_3_2 (jetPolynomial coeff_jetPolynomial)
open Scalar55LeadingPrice (physicalDegree taylorLength)
open Scalar55LeadingLower_1 (Coefficients coefficientPoint coefficientPolynomial oldCutIdeal mem_properComponents)
open Polynomial MvPolynomial
private theorem length_le : taylorLength ≤ K1_13.taylorLength := by
  change 131072 ≤ 133672
  decide
private def pad {m n : ℕ} (a : Fin m → GeometricX) (i : Fin n) : GeometricX :=
  if h : i.val < m then a ⟨i.val, h⟩ else 0
private def truncate {m n : ℕ} : GeoRow n →ₐ[GeometricX] GeoRow m :=
  aeval fun i => if h : i.val < m then MvPolynomial.X ⟨i.val, h⟩ else 0
private theorem truncate_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (truncate : GeoRow n →ₐ[GeometricX] GeoRow m) := by
  let r := rename (R := GeometricX) (Fin.castLE h)
  have he : truncate.comp r = AlgHom.id GeometricX (GeoRow m) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, rename_X, truncate, MvPolynomial.aeval_X, AlgHom.id_apply]
    exact dite_eq_left i.isLt
  exact fun p => ⟨r p, DFunLike.congr_fun he p⟩
private theorem eval_truncate {m n : ℕ} (a : Fin m → GeometricX) (p : GeoRow n) :
    MvPolynomial.eval a (truncate p) = MvPolynomial.eval (pad a) p := by
  change aeval a (truncate p) = aeval (pad a) p
  rw [truncate, comp_aeval_apply]
  apply congrArg (fun z : Fin n → GeometricX => aeval z p)
  funext i
  unfold pad
  split_ifs <;> simp only [MvPolynomial.aeval_X, map_zero]
private theorem pad_restrict {m n : ℕ} (h : m ≤ n) (a : Fin n → GeometricX)
    (hz : ∀ i : Fin n, m ≤ i.val → a i = 0) : pad (a ∘ Fin.castLE h) = a := by
  funext i
  unfold pad
  split_ifs with hi
  · exact congrArg a (Fin.ext rfl)
  · exact (hz i (Nat.le_of_not_lt hi)).symm
private theorem vanishingIdeal_restrict {m n : ℕ} (h : m ≤ n)
    (C : Set (Fin n → GeometricX)) (hz : ∀ a ∈ C, ∀ i : Fin n, m ≤ i.val → a i = 0) :
    vanishingIdeal GeometricX C =
      (vanishingIdeal GeometricX ((fun a => a ∘ Fin.castLE h) '' C)).comap
        (truncate : GeoRow n →ₐ[GeometricX] GeoRow m).toRingHom := by
  ext p
  constructor
  · intro hp a ha
    obtain ⟨b, hb, rfl⟩ := ha
    change MvPolynomial.eval (b ∘ Fin.castLE h) (truncate p) = 0
    rw [eval_truncate, pad_restrict h b (hz b hb)]
    exact hp b hb
  · intro hp b hb
    have ha := hp (b ∘ Fin.castLE h) ⟨b, hb, rfl⟩
    change MvPolynomial.eval (b ∘ Fin.castLE h) (truncate p) = 0 at ha
    rwa [eval_truncate, pad_restrict h b (hz b hb)] at ha
private theorem polynomial_pad {m n : ℕ} (h : m ≤ n) (a : Fin m → GeometricX) :
    (∑ i : Fin n, Polynomial.monomial i.val (pad a i)) =
      ∑ i : Fin m, Polynomial.monomial i.val (a i) := by
  let c : ℕ → GeometricX := fun j => if hj : j < m then a ⟨j, hj⟩ else 0
  change jetPolynomial n c = _
  have he : (∑ i : Fin m, Polynomial.monomial i.val (a i)) = jetPolynomial m c := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [c, dite_eq_left i.isLt, Fin.eta]
  rw [he]
  ext j
  simp only [coeff_jetPolynomial]
  by_cases hj : j < m
  · rw [ite_eq_left hj, ite_eq_left (hj.trans_le h)]
  · simp [c, hj]
theorem proof : Scalar55LeadingLower_1.c2 top := by
  intro n f hf a ha hs
  rcases a with ⟨i, P⟩
  obtain ⟨hw, hm⟩ := mem_properComponents.mp ha
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp hm
  have hp := hmin.isPrime
  have hle := hmin.le
  have hstable := tangent_stable hp hle hsep hs
  have hdim := component_dimension (hf.irreducible i) hw hm
  obtain ⟨hprime, hcurve⟩ :=
    K1_13_5_4_3_4.proof (f i) P hp hsep hdim
  have hTaylor := fun y hy => stable_taylor (hf.weight i) hle hstable (y := y) hy
  let C := coefficientImage (f i) P
  let Q := vanishingIdeal GeometricX ((fun b => b ∘ Fin.castLE length_le) '' C)
  have hz : ∀ b ∈ C, ∀ j : Fin K1_13.taylorLength, taylorLength ≤ j.val → b j = 0 := by
    rintro b ⟨y, hy, rfl⟩ j hj
    exact coeff_eq_zero_of_natDegree_lt ((hTaylor y hy).1.trans_lt (Nat.lt_of_succ_le hj))
  let T : GeoRow K1_13.taylorLength →ₐ[GeometricX] GeoRow taylorLength := truncate
  have hT : Function.Surjective T := truncate_surjective length_le
  have hQ : curveIdeal (f i) P = Q.comap T.toRingHom :=
    vanishingIdeal_restrict length_le C hz
  have hQprime : Q.IsPrime := by
    have hker : RingHom.ker T.toRingHom ≤ curveIdeal (f i) P := by
      rw [hQ]
      intro p hp'
      change T p = 0 at hp'
      change T p ∈ Q
      rw [hp']
      exact Q.zero_mem
    let := hprime
    have hmap := Ideal.map_isPrime_of_surjective (f := T.toRingHom) hT hker
    rwa [hQ, Ideal.map_comap_of_surjective T.toRingHom hT] at hmap
  have hQdim : (affineHilbertPolynomial Q).natDegree = 1 := by
    rw [hQ] at hcurve
    change (affineHilbertPolynomial (Q.comap T)).natDegree = 1 at hcurve
    rwa [natDegree_affineHilbertPolynomial_comap_of_surjective T hT Q] at hcurve
  have hmem (b : K1_13_5_4.Coefficients) (hb : b ∈ C) :
      b ∘ Fin.castLE length_le ∈ zeroLocus GeometricX Q :=
    zeroLocus_vanishingIdeal_le _ ⟨b, hb, rfl⟩
  have hpoly (b : Coefficients) :
      K1_13_5_4.coefficientPolynomial (pad b) = coefficientPolynomial b :=
    polynomial_pad length_le b
  refine ⟨Q, ⟨hQprime, hQdim, ?_, ?_⟩, ?_⟩
  · intro b hb
    have hpad : pad b ∈ zeroLocus GeometricX (curveIdeal (f i) P) := by
      intro p hp'
      change MvPolynomial.eval (pad b) p = 0
      rw [← eval_truncate]
      exact hb (T p) (by rw [hQ] at hp'; exact hp')
    rw [← hpoly b]
    exact solves_on_closure _ _ (fun y hy => (hTaylor y hy).2) _ hpad
  · obtain ⟨y, hy⟩ := regularLocus_nonempty (f i) P hp hsep
    let b := reconstructAt (f i) y
    have hb : b ∈ C := ⟨y, hy, rfl⟩
    refine ⟨b ∘ Fin.castLE length_le, hmem b hb, ?_⟩
    rw [← hpoly, pad_restrict length_le b (hz b hb), coefficientPolynomial_reconstructAt]
    intro hzero
    apply hy.2
    rw [← eval_trajectory_at_centre (f i), hzero, Polynomial.eval_zero]
  · intro S hS hy
    have hfP : genericRow (f i) ∈ P := hle (Ideal.subset_span (by simp))
    have he : MvPolynomial.eval (jetPoint S) (genericRow (f i)) = 0 := hy.1 _ hfP
    have hn : MvPolynomial.eval (jetPoint S) (genericRow (separant (f i))) ≠ 0 := hy.2
    rw [eval_genericRow_at_point] at he hn
    have hr : RegularAt 2 (f i) S :=
      ⟨genericCoeff_injective (he.trans genericCoeff.map_zero.symm),
        fun h => hn (by rw [show K1_13.atJet (separant (f i)) S = 0 from h, map_zero])⟩
    have hS' : S.natDegree ≤ 133671 := hS.trans (by change 131071 ≤ 133671; decide)
    have hres := hmem (reconstructAt (f i) (jetPoint S)) ⟨jetPoint S, hy, rfl⟩
    rw [reconstructAt_mark (f i) S hS' hr] at hres
    exact hres
end
end Scalar55LeadingLower_1_2
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_3
noncomputable section
variable {top : Fin 1}
open K1_13_5_4 (GeometricX)
open MvPolynomial
open scoped BigOperators
open private restrictVariables restrict_rename padded_hilbert sum_monomial_eq_of_tail_zero
  from ProximityPrize.SubmissionLower.PortLow5
theorem length_le : Scalar55LeadingPrice.taylorLength ≤ K1_13.taylorLength := by decide
private def dropCoefficients : K1_13_5_4.GeoRow K1_13.taylorLength →ₐ[GeometricX]
    K1_13_5_4.GeoRow Scalar55LeadingPrice.taylorLength :=
  MvPolynomial.aeval restrictVariables
def pad (Q : Scalar55LeadingLower_1.CoefficientIdeal) : K1_13_5_4.CoefficientIdeal :=
  Q.comap dropCoefficients
theorem pad_injective : Function.Injective pad :=
  Ideal.comap_injective_of_surjective dropCoefficients
    (fun p => ⟨rename (Fin.castLE length_le) p, restrict_rename length_le p⟩)
theorem pad_hilbert (Q : Scalar55LeadingLower_1.CoefficientIdeal) :
    affineHilbertPolynomial (pad Q) = affineHilbertPolynomial Q :=
  padded_hilbert length_le Q
theorem pad_degree (Q : Scalar55LeadingLower_1.CoefficientIdeal) :
    affineDegree (pad Q) = affineDegree Q := by
  unfold affineDegree
  rw [pad_hilbert]
theorem pad_points {Q : Scalar55LeadingLower_1.CoefficientIdeal} {b : K1_13_5_4.Coefficients}
    (hb : b ∈ zeroLocus GeometricX (pad Q)) :
    let a := b ∘ Fin.castLE length_le
    a ∈ zeroLocus GeometricX Q ∧
      K1_13_5_4.coefficientPolynomial b = Scalar55LeadingLower_1.coefficientPolynomial a := by
  dsimp only
  constructor
  · intro p hp
    have hv := hb (rename (Fin.castLE length_le) p)
      (show dropCoefficients (rename (Fin.castLE length_le) p) ∈ Q from
        (restrict_rename length_le p).symm ▸ hp)
    change eval b (rename (Fin.castLE length_le) p) = 0 at hv
    rwa [eval_rename] at hv
  · apply sum_monomial_eq_of_tail_zero length_le
    intro i hi
    have hx : MvPolynomial.X i ∈ pad Q := by
      change dropCoefficients (MvPolynomial.X i) ∈ Q
      simp [dropCoefficients, restrictVariables, Nat.not_lt.mpr hi]
    exact (eval_X (f := b) i).symm.trans (hb _ hx)
private def paddedPoint (a : Scalar55LeadingLower_1.Coefficients) : K1_13_5_4.Coefficients :=
  fun i => if hi : i.val < Scalar55LeadingPrice.taylorLength then a ⟨i.val, hi⟩ else 0
private theorem eval_paddedPoint (a : Scalar55LeadingLower_1.Coefficients) :
    MvPolynomial.aeval (paddedPoint a) =
      (MvPolynomial.aeval a).comp dropCoefficients := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i.val < Scalar55LeadingPrice.taylorLength <;>
    simp [dropCoefficients, restrictVariables, paddedPoint, hi]
theorem pad_actual {f : K1_13.Row 3} {Q : Scalar55LeadingLower_1.CoefficientIdeal}
    (h : Scalar55LeadingLower_1.ActualSolutionCurve f Q) : K1_13_5_4.ActualSolutionCurve f (pad Q) := by
  refine ⟨h.prime.comap dropCoefficients, ?_, ?_, ?_⟩
  · rw [pad_hilbert]
    exact h.dimension
  · intro b hb
    obtain ⟨ha, he⟩ := pad_points hb
    rw [he]
    exact h.solves _ ha
  · obtain ⟨a, ha, hs⟩ := h.regular
    have hb : paddedPoint a ∈ zeroLocus GeometricX (pad Q) := by
      intro p hp
      exact (DFunLike.congr_fun (eval_paddedPoint a) p).trans (ha _ hp)
    obtain ⟨_, he⟩ := pad_points hb
    exact ⟨paddedPoint a, hb, by
      have hrestrict : paddedPoint a ∘ Fin.castLE length_le = a := by
        funext i
        simp [paddedPoint, i.isLt]
      rw [he, hrestrict]
      exact hs⟩
end
end Scalar55LeadingLower_1_3
end
section
set_option autoImplicit false
namespace Scalar55LeadingLower_1_3
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom Row embed)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX extendedAtJet)
open K1_13_5_4_4
open Scalar55LeadingPrice (taylorLength)
open Scalar55LeadingLower (Whole invariantBudget)
open Scalar55LeadingLower_1 (CoefficientIdeal ActualSolutionCurve coefficientPolynomial oldCut)
open MvPolynomial Finset
open scoped BigOperators Polynomial
open private flat_of_injective regular_cut_of_flat_map from ProximityPrize.SubmissionLower.Fast067
open private curve_minimal from ProximityPrize.SubmissionLower.Fast067
private theorem donorCharts : K1_13_5_4_4.c1 :=
  K1_13_5_4_4_1.of_children K1_13_5_4_4_1_1.proof K1_13_5_4_4_1_2.proof
private def projectedIdeal (Q : CoefficientIdeal) : FreshJetIdeal := freshImage (pad Q)
private def retunedDivisor (f : Row 3) : FreshJetIdeal :=
  freshHypersurface f ⊔ Ideal.span {freshRow (oldCut f)}
private theorem compatibility_zero (f : Row 3) (S : GeometricX[X]) (k : ℕ)
    (hk : k + 3 ≤ K1_13.taylorLength) (hS : S.natDegree < k + 3)
    (hf : extendedAtJet f S = 0) : extendedAtJet (K1_13_5.compatibilityNumerator f k) S = 0 := by
  have h := K1_13_5_4_4_1_2.proof f S (hS.trans_le hk) hf k hk
  rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree S (k + 3) hS, mul_zero, mul_zero] at h
  have htwo : (2 : GeometricX[X]) ≠ 0 := by
    let g : K1.K →+* GeometricX[X] :=
      Polynomial.C.comp ((algebraMap Geom GeometricX).comp embed)
    have hne : (2 : K1.K) ≠ 0 := by decide
    exact fun hz => hne (g.injective (by simpa only [map_ofNat, map_zero] using hz))
  exact (mul_eq_zero.mp h).resolve_left htwo
private theorem cut_zero (f : Row 3) (S : GeometricX[X])
    (hS : S.natDegree < taylorLength) (hf : extendedAtJet f S = 0) :
    extendedAtJet (oldCut f) S = 0 := by
  have hk : taylorLength - 3 + 3 = taylorLength := rfl
  change extendedAtJet (K1_13_5.compatibilityNumerator f (taylorLength - 3)) S = 0
  exact compatibility_zero f S _ (hk.le.trans length_le) (hk.symm ▸ hS) hf
private theorem projected_on_divisor {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) : retunedDivisor f ≤ projectedIdeal Q := by
  have hold := pad_actual h
  have hrow : freshHypersurface f ≤ projectedIdeal Q :=
    le_sup_left.trans (((donorCharts f).1 (pad Q) hold).on_divisor)
  refine sup_le hrow ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  change freshProjection (freshRow (oldCut f)) ∈ extendIdeal (pad Q)
  rw [(K1_13_5_4_4_1_1.proof (pad Q) hold.prime).2]
  intro b hb
  obtain ⟨ha, he⟩ := pad_points hb
  have hdeg (a : Scalar55LeadingLower_1.Coefficients) : (coefficientPolynomial a).natDegree < taylorLength := by
    apply Nat.lt_succ_of_le
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt j.isLt)
  rw [K1_13_5_4_4_1.point_projected, K1_13_5_4_4_1.eval_row, he,
    cut_zero f _ (hdeg _) (h.solves _ ha), map_zero]
private theorem projected_comparison {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) :
    (projectedIdeal Q).IsPrime ∧ (affineHilbertPolynomial (projectedIdeal Q)).natDegree = 1 ∧
      affineDegree Q ≤ affineDegree (projectedIdeal Q) := by
  have hold := pad_actual h
  have hc := (donorCharts f).1 (pad Q) hold
  obtain ⟨hdim, hdeg⟩ := K1_13_5_4_4_2.proof (pad Q) hold.prime hold.dimension
    hc.extended_prime hc.birational
  exact ⟨hc.extended_prime.comap freshProjection, hdim, (pad_degree Q).symm.trans_le hdeg⟩
private theorem retunedCut_regular {f : Row 3} (hf : Irreducible f) (hw : ¬ Whole f) :
    IsLeftRegular (Ideal.Quotient.mk (freshHypersurface f) (freshRow (oldCut f))) := by
  let : (Ideal.span {f} : Ideal (Row 3)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hc : oldCut f ∉ (Ideal.span {f} : Ideal (Row 3)) :=
    fun h => hw (Ideal.mem_span_singleton.mp h)
  apply regular_cut_of_flat_map freshCoeff (flat_of_injective freshCoeff freshCoeff_injective)
  · exact fun _ _ h => mul_left_cancel₀ hf.ne_zero h
  · exact fun _ _ h => mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hc) h
private theorem factor_degree_sum (f : Row 3) (hf : Irreducible f) (hw : ¬ Whole f)
    (T : Finset FreshJetIdeal)
    (hT : ∀ Q ∈ T, Q.IsPrime ∧ retunedDivisor f ≤ Q ∧
      (affineHilbertPolynomial Q).natDegree = 1) :
    (∑ Q ∈ T, affineDegree Q) ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
  classical
  by_cases hEmpty : T = ∅
  · rw [hEmpty, sum_empty]
    positivity
  have hPproper : freshHypersurface f ≠ ⊤ := by
    obtain ⟨Q, hQ⟩ := nonempty_iff_ne_empty.mpr hEmpty
    exact ne_top_of_le_ne_top (hT Q hQ).1.ne_top
      (le_sup_left.trans (hT Q hQ).2.1)
  have hPdim : (affineHilbertPolynomial (freshHypersurface f)).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      (freshRow_ne_zero hf.ne_zero) hPproper
    rw [Nat.card_fin] at h
    change (affineHilbertPolynomial (freshHypersurface f)).natDegree + 1 = 3 at h
    omega
  have hcut := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (retunedCut_regular hf hw) (freshRow_degree_le (oldCut f))
  rw [hPdim] at hcut
  have hJdim : (affineHilbertPolynomial (retunedDivisor f)).natDegree ≤ 1 := hcut.1
  have hsub : T ⊆ (retunedDivisor f).minimalPrimesFinset := by
    intro Q hQ
    obtain ⟨hp, hle, hdim⟩ := hT Q hQ
    exact Ideal.mem_minimalPrimesFinset.mpr (curve_minimal hp hle hJdim hdim)
  have hdeg : affineDegree (freshHypersurface f) ≤ (f.totalDegree : ℚ) := by
    rw [freshHypersurface, affineDegree_span_singleton (freshRow_ne_zero hf.ne_zero)]
    exact_mod_cast freshRow_degree_le f
  calc
    (∑ Q ∈ T, affineDegree Q) = ∑ Q ∈ T, (affineHilbertPolynomial Q).coeff 1 := by
      apply sum_congr rfl
      intro Q hQ
      rw [affineDegree, (hT Q hQ).2.2, Polynomial.leadingCoeff, (hT Q hQ).2.2]
      simp
    _ ≤ ∑ Q ∈ (retunedDivisor f).minimalPrimesFinset, (affineHilbertPolynomial Q).coeff 1 := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro Q hQ _
      have hle := (Ideal.mem_minimalPrimesFinset.mp hQ).le
      exact Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
        ((natDegree_affineHilbertPolynomial_le_of_le hle).trans hJdim)
        (eventually_eval_affineHilbertPolynomial_nonneg Q)
    _ ≤ (affineHilbertPolynomial (retunedDivisor f)).coeff 1 :=
      sum_coeff_affineHilbertPolynomial_minimalPrimes_le _ hJdim
    _ ≤ ((oldCut f).totalDegree : ℚ) * affineDegree (freshHypersurface f) := by
      simpa [retunedDivisor, affineDegree, hPdim, mul_assoc] using hcut.2
    _ ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
      rw [Nat.cast_mul, mul_comm (f.totalDegree : ℚ)]
      exact mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _)
private theorem curve_family_bound (f : Row 3) (hf : Irreducible f) (hw : ¬ Whole f)
    (C : Finset CoefficientIdeal) (hC : ∀ Q ∈ C, ActualSolutionCurve f Q) :
    (∑ Q ∈ C, affineDegree Q) ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
  classical
  have hinj : Set.InjOn projectedIdeal (C : Set CoefficientIdeal) := by
    intro Q hQ R hR he
    exact pad_injective ((donorCharts f).2 (pad_actual (hC Q hQ)) (pad_actual (hC R hR)) he)
  calc
    (∑ Q ∈ C, affineDegree Q) ≤ ∑ Q ∈ C, affineDegree (projectedIdeal Q) :=
      sum_le_sum fun Q hQ => (projected_comparison (hC Q hQ)).2.2
    _ = ∑ P ∈ C.image projectedIdeal, affineDegree P := (sum_image hinj).symm
    _ ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
      apply factor_degree_sum f hf hw
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hP
      have hc := projected_comparison (hC Q hQ)
      exact ⟨hc.1, projected_on_divisor (hC Q hQ), hc.2.1⟩
private def cutterBound (b : ℕ) : ℕ :=
  1 + (2 * (taylorLength + 1) - 7) * (b - 1)
private theorem cutterBound_mono : Monotone cutterBound := by
  intro a b hab
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hab _)) _
theorem proof : Scalar55LeadingLower_1.c3 top := by
  classical
  intro n f hf hcut C hsource
  by_cases hEmpty : C = ∅
  · subst C
    exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨Q₀, hQ₀⟩ := nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨i₀, _⟩ := hsource Q₀ hQ₀
  let pick (Q : CoefficientIdeal) : Fin n :=
    if hQ : Q ∈ C then Classical.choose (hsource Q hQ) else i₀
  have hpick (Q : CoefficientIdeal) (hQ : Q ∈ C) :
      ¬ Whole (f (pick Q)) ∧ ActualSolutionCurve (f (pick Q)) Q := by
    simpa only [pick, dite_eq_left hQ] using Classical.choose_spec (hsource Q hQ)
  let part (i : Fin n) := C.filter fun Q => pick Q = i
  have hlocal (i : Fin n) : (∑ Q ∈ part i, affineDegree Q) ≤
      ((f i).totalDegree * (oldCut (f i)).totalDegree : ℕ) := by
    have hpart (Q : CoefficientIdeal) (hQ : Q ∈ part i) :
        ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q := by
      obtain ⟨hm, hi⟩ := mem_filter.mp hQ
      simpa only [hi] using hpick Q hm
    by_cases hw : Whole (f i)
    · have he : part i = ∅ := eq_empty_iff_forall_notMem.mpr fun Q hQ => (hpart Q hQ).1 hw
      rw [he, sum_empty]
      positivity
    exact curve_family_bound _ (hf.irreducible i) hw _ fun Q hQ => (hpart Q hQ).2
  have hnat : (∑ i : Fin n, (f i).totalDegree * (oldCut (f i)).totalDegree) ≤ (invariantBudget top) := by
    calc
      _ ≤ ∑ i : Fin n, (f i).totalDegree * cutterBound (Scalar55LeadingPrice.lowerWidth top) := by
        apply sum_le_sum
        intro i _
        have hi := (single_le_sum (f := fun j => (f j).totalDegree)
          (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hf.total
        exact Nat.mul_le_mul_left _ ((hcut i).trans (cutterBound_mono hi))
      _ = (∑ i : Fin n, (f i).totalDegree) * cutterBound (Scalar55LeadingPrice.lowerWidth top) := by rw [sum_mul]
      _ ≤ (invariantBudget top) := Nat.mul_le_mul_right _ hf.total
  have hsum : (∑ Q ∈ C, affineDegree Q) ≤ ((invariantBudget top) : ℚ) := by
    calc
      _ = ∑ i : Fin n, ∑ Q ∈ part i, affineDegree Q :=
        (sum_fiberwise_of_maps_to (t := (univ : Finset (Fin n)))
          (g := pick) (fun _ _ => mem_univ _) affineDegree).symm
      _ ≤ ∑ i : Fin n, (((f i).totalDegree * (oldCut (f i)).totalDegree : ℕ) : ℚ) :=
        sum_le_sum fun i _ => hlocal i
      _ ≤ ((invariantBudget top) : ℚ) := by exact_mod_cast hnat
  have hex (Q : CoefficientIdeal) : ∃ d : ℕ, Q ∈ C → 0 < d ∧ affineDegree Q = (d : ℚ) := by
    by_cases hQ : Q ∈ C
    · have h := (hpick Q hQ).2
      have hp := pad_actual h
      obtain ⟨d, hd, he⟩ := curve_degree_nat (pad Q) hp.prime hp.dimension
      exact ⟨d, fun _ => ⟨hd, (pad_degree Q).symm.trans he⟩⟩
    · exact ⟨0, fun h => False.elim (hQ h)⟩
  let d (Q : CoefficientIdeal) := Classical.choose (hex Q)
  have hd (Q : CoefficientIdeal) (hQ : Q ∈ C) : 0 < d Q ∧ affineDegree Q = (d Q : ℚ) :=
    Classical.choose_spec (hex Q) hQ
  refine ⟨d, fun Q hQ => ⟨(hd Q hQ).1, (hd Q hQ).2.le⟩, ?_⟩
  have hcast : (∑ Q ∈ C, (d Q : ℚ)) ≤ ((invariantBudget top) : ℚ) :=
    (sum_congr rfl fun Q hQ => (hd Q hQ).2.symm).trans_le hsum
  exact_mod_cast hcast
end
end Scalar55LeadingLower_1_3
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace Scalar55LeadingLower_2
noncomputable section
variable {top : Fin 1}
open K1 (K I node)
open Scalar55LeadingPrice (Messages)
open K1_13 (Geom embed extend taylorLength)
open K1_13_5 (NodeCapacity)
open K1_13_5_5 (CoeffRing CoeffIndex coeffPoint)
open Finset MvPolynomial
open scoped BigOperators Polynomial
open private valueCut valueCut_degree valueCut_eval nodeCapacity_of_sections
  curve_degree_nat from ProximityPrize.SubmissionLower.Fast064
private theorem coeffPoint_injOn {w Γ s} (h : Messages w Γ s) :
    Set.InjOn (fun γ => coeffPoint (extend (s γ))) (Γ : Set K) := by
  intro γ hγ η hη heq
  apply h.distinct hγ hη
  apply Polynomial.ext
  intro j
  by_cases hj : j < taylorLength
  · exact embed.injective (by simpa [coeffPoint] using congrFun heq ⟨j, hj⟩)
  · change ¬ j < 133672 at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := s γ) (by
          have hdeg : (s γ).natDegree ≤ 131071 := h.degree γ hγ
          omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (p := s η) (by
          have hdeg : (s η).natDegree ≤ 131071 := h.degree η hη
          omega)]
private theorem zeroDim_count {w Γ s} (h : Messages w Γ s) (P : Ideal CoeffRing)
    (hdim : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P) :
    (Γ.card : ℚ) ≤ affineDegree P := by
  classical
  let A := Γ.image (fun γ => coeffPoint (extend (s γ)))
  have hA : A.card = Γ.card := card_image_of_injOn (coeffPoint_injOn h)
  have hsub : (A : Set _) ⊆ zeroLocus Geom P := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := Geom) P hdim
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hA] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree
private theorem section_count {w Γ s} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P)
    (x a : K) (hmiss : ∃ γ ∈ Γ, (s γ).eval x ≠ a)
    {c : ℚ} (hc : 0 ≤ c)
    (bound : ∀ (V : Finset K), V ⊆ Γ → ∀ (Q : Ideal CoeffRing), Q.IsPrime →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, coeffPoint (extend (s γ)) ∈ zeroLocus Geom Q) →
      (V.card : ℚ) ≤ c * affineDegree Q) :
    ((Γ.filter fun γ => (s γ).eval x = a).card : ℚ) ≤ c * affineDegree P := by
  classical
  let prime := hP
  let cut := valueCut x a
  let Ps := (P ⊔ Ideal.span {cut}).minimalPrimesFinset
  let U := Γ.filter fun γ => (s γ).eval x = a
  let part (Q : Ideal CoeffRing) := U.filter fun γ => coeffPoint (extend (s γ)) ∈ zeroLocus Geom Q
  have hdegree (γ : K) (hγ : γ ∈ Γ) : (s γ).natDegree ≤ 133671 :=
    (h.degree γ hγ).trans (by decide : 131071 ≤ 133671)
  have hproper : cut ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hm
    exact hv ((valueCut_eval (hdegree γ hγ) x a).mp (hpoints γ hγ _ hm))
  have hcover : U ⊆ Ps.biUnion part := by
    intro γ hγ
    obtain ⟨hγΓ, hv⟩ := mem_filter.mp hγ
    have hp : coeffPoint (extend (s γ)) ∈ zeroLocus Geom (P ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ, (valueCut_eval (hdegree γ hγΓ) x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact mem_biUnion.mpr ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  have hsum : U.card ≤ ∑ Q ∈ Ps, (part Q).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hdeg : (∑ Q ∈ Ps, affineDegree Q) ≤ affineDegree P := by
    simpa only [Ps, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
  change (U.card : ℚ) ≤ c * affineDegree P
  calc
    _ ≤ ∑ Q ∈ Ps, ((part Q).card : ℚ) := by exact_mod_cast hsum
    _ ≤ ∑ Q ∈ Ps, c * affineDegree Q := by
      apply sum_le_sum
      intro Q hQ
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact bound _ ((filter_subset _ _).trans (filter_subset _ _)) Q hmin.isPrime
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => (mem_filter.mp hγ).2)
    _ ≤ c * affineDegree P := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hdeg hc
private theorem curve_count {w Γ s} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hdim : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P) :
    (Γ.card : ℚ) ≤ 2 * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hP hdim
  have hcap : NodeCapacity w Γ s δ := by
    apply nodeCapacity_of_sections
    intro i hi
    have hcount := section_count h hP hpoints (node i) (w i) hi (c := 1) zero_le_one
      (fun V hV Q _ hQ hp => by
        rw [one_mul]
        exact zeroDim_count (h.mono hV) Q (by omega) hp)
    rw [one_mul, hdeg] at hcount
    exact_mod_cast hcount
  have hcount := Scalar55LeadingLower.nodeCapacity_count h hcap
  have hi : Γ.card ≤ 2 * δ := by omega
  rw [hdeg]
  exact_mod_cast hi
theorem surface_nodeCapacity {w Γ s} {d : ℕ} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hdim : (affineHilbertPolynomial P).natDegree = 2)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P)
    (hd : 2 * affineDegree P ≤ (d : ℚ)) :
    NodeCapacity w Γ s d := by
  classical
  apply nodeCapacity_of_sections
  intro i hi
  have hcount := section_count h hP hpoints (node i) (w i) hi (c := 2) (by norm_num)
    (fun _ hV _ hQ hdimQ hp => curve_count (h.mono hV) hQ (by omega) hp)
  exact_mod_cast hcount.trans hd
end
end Scalar55LeadingLower_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Scalar55LeadingLower_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom embed Row atJet)
open K1_13_5 (RegularAt separant compatibilityNumerator)
open K1_13_5_5 K1_13_5_5_1
open Scalar55LeadingPrice (taylorLength physicalDegree TrueWeightLE anchorCutoff)
open Scalar55LeadingLower (Whole)
open scoped Polynomial
open private chart_trajectory from ProximityPrize.SubmissionLower.PortLow5
def LowSupport (P : Ideal CoeffRing) : Prop :=
  ∀ i : CoeffIndex, taylorLength ≤ i.val → MvPolynomial.X i ∈ P
private theorem degree_trajectory {F : Type} [Field F] (k : Geom →+* F) {U : F[X]}
    (hU : U.natDegree < taylorLength) (f : Row 3) (hf : TrueWeightLE f anchorCutoff) :
    (trajectory k U f).natDegree ≤ anchorCutoff := by
  classical
  unfold trajectory
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hprod : (∏ i ∈ m.support, Polynomial.hasseDeriv i.val U ^ m i).natDegree ≤
      m.sum (fun i e => (physicalDegree - i.val) * e) := by
    unfold Finsupp.sum
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    change ((Polynomial.hasseDeriv i.val U) ^ m i).natDegree ≤ (physicalDegree - i.val) * m i
    rw [Nat.mul_comm]
    exact Polynomial.natDegree_pow_le_of_le _ ((Polynomial.natDegree_hasseDeriv_le U i.val).trans
      (Nat.sub_le_sub_right (Nat.le_of_lt_succ hU) _))
  exact (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_map_le hprod).trans (hf m hm)
private theorem separant_regular_contracted (f : Row 3) (hf : Irreducible f) (hd : 0 < f.degreeOf 2)
    (hmax : f.degreeOf 2 ≤ 25) : freshRow (separant f) ∉ chartIdeal f := by
  change separant f ∉ (chartIdeal f).comap rowMap
  rw [chart_contract f hf hd]
  have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have : CharP Geom[X] K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hcast : (f.degreeOf 2 : Geom[X]) ≠ 0 := by
    intro h
    have hp := (CharP.cast_eq_zero_iff Geom[X] K1.p (f.degreeOf 2)).mp h
    exact (not_le_of_gt (hmax.trans_lt (by decide : 25 < K1.p))) (Nat.le_of_dvd hd hp)
  have hsep : separant f ≠ 0 := MvPolynomial.pderiv_ne_zero_of_natCast_ne_zero 2 f hcast
  intro hmem
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
  have hgn : g ≠ 0 := by
    intro he
    exact hsep (by simpa [he] using hg)
  have hdeg := MvPolynomial.degreeOf_pderiv_le_sub_one 2 f
  have h := congrArg (MvPolynomial.degreeOf (2 : Fin 3)) hg
  rw [MvPolynomial.degreeOf_mul_eq hf.ne_zero hgn] at h
  change (separant f).degreeOf 2 ≤ f.degreeOf 2 - 1 at hdeg
  omega
theorem chart_of_whole (f : Row 3) (hf : Irreducible f)
    (hd : 0 < f.degreeOf 2) (hmax : f.degreeOf 2 ≤ 25)
    (hw : TrueWeightLE f anchorCutoff) (hwhole : Whole f) :
    ∃ P : Ideal CoeffRing, FreshChart P (freshRow f) (freshRow (separant f)) ∧
      LowSupport P ∧ ∀ S : Geom[X], S.natDegree ≤ physicalDegree → RegularAt 2 f S →
        coeffPoint S ∈ MvPolynomial.zeroLocus Geom P := by
  let hp : (chartIdeal f).IsPrime := chart_prime f hf hd
  have hs := separant_regular_contracted f hf hd hmax
  have hweight (U : (ChartField f)[X]) (hU : U.natDegree < taylorLength) :
      (trajectory (chartConstants f) U f).natDegree < K1.p :=
    (degree_trajectory _ hU f hw).trans_lt (by decide : anchorCutoff < K1.p)
  obtain ⟨U, hsmall, hsol, hinit⟩ :=
    chart_trajectory f taylorLength (by decide) (by decide) hs hweight hwhole
  have length_le : taylorLength ≤ K1_13.taylorLength := by decide
  have hU := hsmall.trans_le length_le
  obtain ⟨m, v, hv⟩ := K1_13_5_5_1_1.proof f
  let k := chartConstants f
  let point : CoeffIndex → ChartField f := fun a => U.coeff a.val
  let P := RingHom.ker (coeffEval k point)
  have hbase := freshIdeal_eq_ker k point
  have himage := freshJetEval_ker f hf hd U hU hsol hinit
  have hD : onChart f (freshRow (separant f)) ≠ 0 :=
    fun h => hs ((onChart_eq_zero f _).mp h)
  have hUreg : trajectory k U (separant f) ≠ 0 := by
    intro hz
    have h := eval_trajectory k U (chartCenter f) (separant f)
    rw [hz, Polynomial.eval_zero, hinit, rowAt_chart] at h
    exact hD h.symm
  refine ⟨P, ⟨RingHom.ker_isPrime _, ?_, ?_, hs, ?_⟩, ?_, ?_⟩
  · exact fun h => hf.ne_zero (rowMap_injective (h.trans (map_zero _).symm))
  · change (freshIdeal P).comap freshProjection.toRingHom = chartIdeal f
    rw [hbase, RingHom.comap_ker]
    exact himage
  · intro a
    refine ⟨freshRow (v a), m, ?_⟩
    have hU' : (U.map (newConstants : ChartField f →+* NewField (ChartField f))).natDegree <
        K1_13.taylorLength := Polynomial.natDegree_map_le.trans_lt hU
    have hsol' : trajectory (newConstants.comp k) (U.map newConstants) f = 0 := by
      rw [← map_trajectory, hsol, Polynomial.map_zero]
    have hs' : rowAt (newConstants.comp k) newCenter
        (jetAt newCenter (U.map newConstants)) (separant f) ≠ 0 := by
      rw [newTrajectory_eval]
      exact fun h => hUreg ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
    have h := hv (NewField (ChartField f)) (newConstants.comp k) (U.map newConstants) newCenter
      hU' hsol' hs' a
    rw [newTrajectory_eval, newTrajectory_eval, Polynomial.coeff_map,
      ← freshJetEval_row k U hU, ← freshJetEval_row k U hU] at h
    exact fresh_recovered_mem k U a m _ _ h
  · intro a ha
    change coeffEval k point (MvPolynomial.X a) = 0
    rw [coeffEval, MvPolynomial.eval₂Hom_X']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hsmall.trans_le ha)
  · intro S hS hreg
    let e : FreshJetRing →+* ChartField f := onChart f
    let g : FreshJetRing →+* FreshField :=
      MvPolynomial.eval (jetAt freshCenter (S.map freshConstants))
    let b : Geom →+* FreshJetRing := MvPolynomial.C.comp freshConstants
    have hg (q : Row 3) : g (freshRow q) = algebraMap Geom[X] FreshField (atJet q S) := by
      rw [← actual_eval, actual_eval_fresh]
      rfl
    have hreg' : g (freshRow (separant f)) ≠ 0 := by
      rw [hg]
      exact fun h => hreg.2 ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
    have hker : RingHom.ker e ≤ RingHom.ker g := by
      rw [show RingHom.ker e = chartIdeal f by
        ext q
        exact onChart_eq_zero f q]
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker, hg, hreg.1, map_zero]
    have hS' : (S.map freshConstants).natDegree < K1_13.taylorLength :=
      Polynomial.natDegree_map_le.trans_lt ((Nat.lt_succ_of_le hS).trans_le length_le)
    have hsolS : trajectory freshConstants (S.map freshConstants) f = 0 := by
      simpa only [trajectory_actual, hreg.1, Polynomial.map_zero, RingHom.comp_id] using
        (map_trajectory (RingHom.id Geom) freshConstants S f).symm
    have hrecU (a : CoeffIndex) :
        e (freshRow (separant f)) ^ m * point a = e (freshRow (v a)) := by
      have hc := hv (ChartField f) k U (chartCenter f) hU hsol
        (by rwa [hinit, rowAt_chart]) a
      rwa [hinit, rowAt_chart] at hc
    have hrecS (a : CoeffIndex) :
        g (freshRow (separant f)) ^ m * freshConstants (S.coeff a.val) = g (freshRow (v a)) := by
      have hc := hv FreshField freshConstants (S.map freshConstants) freshCenter hS' hsolS
        (by rwa [actual_eval_fresh]) a
      rwa [actual_eval_fresh, Polynomial.coeff_map] at hc
    have hle := eval_kernel_le_of_cleared b e g hker (freshRow (separant f)) m
      (fun a => freshRow (v a)) hD hreg' point (freshConstants ∘ coeffPoint S) hrecU hrecS
    intro q hq
    have hz := hle hq
    change MvPolynomial.eval₂Hom (g.comp b) (freshConstants ∘ coeffPoint S) q = 0 at hz
    have hqmap : MvPolynomial.eval₂Hom (g.comp b) (freshConstants ∘ coeffPoint S) =
        freshConstants.comp (MvPolynomial.aeval (coeffPoint S)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [b, g]
      · intro a
        simp
    rw [hqmap] at hz
    exact freshConstants.injective (hz.trans (map_zero _).symm)
end
end Scalar55LeadingLower_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Scalar55LeadingLower_2
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom)
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open Scalar55LeadingPrice (physicalDegree)
open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open private monic_chart_aux from ProximityPrize.SubmissionLower.Fast064
open private commonFactor_monic trimmedValue_monic trimmedValue_dvd from ProximityPrize.SubmissionLower.Fast064
open private eval_divisions from ProximityPrize.SubmissionLower.PortLow5
private theorem supported_height (Q : Ideal CoeffRing) (L : Fin 2 → FreshJetRing)
    (hQ : Q.IsPrime) (hhom : Q.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom))
    (hdim : (affineHilbertPolynomial Q).natDegree = 2)
    (hL : FiniteJetPair L (jetImage (freshIdeal Q))) (hlow : LowSupport Q) :
    2 * affineDegree Q ≤
      (physicalDegree : ℚ) * (genericFiberDimension L (freshIdeal Q) : ℚ) := by
  have h1 := K1_13_5_5_2_1_1.of_children K1_13_5_5_2_1_1_1.proof
    K1_13_5_5_2_1_1_2.proof K1_13_5_5_2_1_1_3.proof
  have h2 := K1_13_5_5_2_1_2.proof
  have h3 := K1_13_5_5_2_1_3.proof
  have h4 := K1_13_5_5_2_1_4.of_children K1_13_5_5_2_1_4_1.proof K1_13_5_5_2_1_4_2.proof
  have h5 := K1_13_5_5_2_1_5.proof
  have h6 := K1_13_5_5_2_1_6.proof
  obtain ⟨i, hi, hchart, hmonic, hdegree⟩ := monic_chart_aux Q hQ hhom (by omega)
  have hid : i.val ≤ physicalDegree :=
    Nat.le_of_lt_succ (lt_of_not_ge (fun h => hi (hlow i h)))
  let : IsDomain (ChartRing Q i) := hchart
  obtain ⟨a, ha, ⟨s⟩⟩ := h2 (ChartRing Q i) (direction Q i) hmonic ((hdegree.trans hid).trans (by decide))
  obtain ⟨hdom, heval, hfinite, hcoeff⟩ := h1 Q i a hQ hhom hdim hi hchart ha
  let : IsDomain (FreshOpen Q i a) := hdom
  let : IsDomain (OpenRing Q i a) := IsLocalization.Away.isDomain _ ha
  change Factorization (openDirection Q i a) at s
  obtain ⟨q, hq0, hq, hqspan⟩ := h3 (OpenRing Q i a) (openDirection Q i a) s
  let e : (OpenRing Q i a)[X] →+* FreshOpen Q i a := freshEval (OpenRing Q i a)
  let x := e (openDirection Q i a)
  let b := e (commonFactor s)
  let d : Fin 3 → FreshOpen Q i a := fun j => e (q j)
  have hx : x ≠ 0 := by
    simpa only [e, x, openDirection, map_zero] using
      heval.ne (hmonic.map (algebraMap _ (OpenRing Q i a))).ne_zero
  have hb : b ≠ 0 := by
    simpa only [e, b, map_zero] using heval.ne (commonFactor_monic s).ne_zero
  have hd : d 0 ≠ 0 := by
    simpa only [d, hq0, e, map_zero] using heval.ne (trimmedValue_monic s).ne_zero
  have htrim : ∀ j, b * d j = e (Polynomial.hasseDeriv j.val (openDirection Q i a)) := by
    intro j
    exact (e.map_mul _ _).symm.trans (congrArg e (hq j))
  have hspan : Ideal.span (Set.range d) = ⊤ := by
    have hm := congrArg (Ideal.map e) hqspan
    rwa [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at hm
  let : Module.Finite FreshField (PrincipalQuot x) := hfinite
  have hdegree' : (openDirection Q i a).natDegree ≤ physicalDegree :=
    Polynomial.natDegree_map_le.trans (hdegree.trans hid)
  have hdiv := eval_divisions e s hdegree' (by decide)
  have hdeq : d 0 = e (trimmedValue s) := congrArg e hq0
  rw [← hdeq] at hdiv
  obtain ⟨hdfin, hlen⟩ := length_bound x (d 0) physicalDegree hx hd hdiv.1 hdiv.2
  rw [← hcoeff]
  have hlenQ : 2 * (Module.finrank FreshField (PrincipalQuot x) : ℚ) ≤
      (physicalDegree : ℚ) * (Module.finrank FreshField (PrincipalQuot (d 0)) : ℚ) := by
    exact_mod_cast hlen
  by_cases hu : IsUnit (d 0)
  · have hzero : Module.finrank FreshField (PrincipalQuot (d 0)) = 0 := by
      have : Subsingleton (PrincipalQuot (d 0)) :=
        Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
      exact Module.finrank_zero_of_subsingleton
    exact hlenQ.trans (by rw [hzero, Nat.cast_zero, mul_zero]; positivity)
  · obtain ⟨hk, hcomparison⟩ := h4 Q i a hQ hhom hdim hi hchart ha hdom b d hb htrim
    obtain ⟨hpairfin, hrank⟩ := hcomparison L hL
    have hL' : FiniteJetPair L (coneJetIdeal d) := hk ▸ hL
    obtain ⟨M, w, hM, hMw, hinj, hw⟩ := h5 _ d L hd hu hspan hL'
    obtain ⟨hwfin, hwRank⟩ := h6 _ d L M hL' hpairfin hM hinj
    rw [hMw] at hwfin hwRank hinj
    let : Module.Finite PairField (pairFiber (valuePairMap (d 0) w)) := hwfin
    let : Module.Finite FreshField (PrincipalQuot (d 0)) := hdfin
    have hbound := pin_bound (d 0) w hw hinj
    rw [hwRank, hrank] at hbound
    exact hlenQ.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hbound)
      (Nat.cast_nonneg physicalDegree))
theorem chart_degree (P : Ideal CoeffRing) (g d : FreshJetRing)
    (hchart : FreshChart P g d) (hlow : LowSupport P) :
    (affineHilbertPolynomial P).natDegree = 2 ∧
      2 * affineDegree P ≤ (physicalDegree : ℚ) * (g.totalDegree : ℚ) := by
  have hdim := K1_13_5_5_2.chart_dimension P g d hchart
  refine ⟨hdim, ?_⟩
  have h2 := K1_13_5_5_2_2.of_children K1_13_5_5_2_2_1.proof K1_13_5_5_2_2_2.proof
  have h3 := K1_13_5_5_2_3.of_children K1_13_5_5_2_3_1.proof
    K1_13_5_5_2_3_2.proof K1_13_5_5_2_3_3.proof
  obtain ⟨n, Q, hQ, hdeg, hfiber⟩ := h2 P hchart.prime hdim
  obtain ⟨L, hL, hfinite, hbudget⟩ := h3 P g d hchart
  have htail : LowSupport (infinityIdeal P) := by
    intro i hi
    change MvPolynomial.X i ∈ Ideal.span _
    apply Ideal.subset_span
    refine ⟨MvPolynomial.X i, hlow i hi, ?_⟩
    change homogeneousComponent (MvPolynomial.X (R := Geom) i).totalDegree
      (MvPolynomial.X i) = MvPolynomial.X i
    rw [totalDegree_X]
    exact homogeneousComponent_eq_self (isHomogeneous_X Geom i)
  have hcurve (i : Fin n) : 2 * affineDegree (Q i) ≤
      (physicalDegree : ℚ) * (genericFiberDimension L (freshIdeal (Q i)) : ℚ) := by
    obtain ⟨hi, hhom, hd⟩ := hQ i
    have hle : jetImage (freshIdeal (infinityIdeal P)) ≤ jetImage (freshIdeal (Q i)) :=
      Ideal.comap_mono (Ideal.map_mono hi.le)
    exact supported_height (Q i) L hi.isPrime hhom hd (hL.of_le hle)
      (fun j hj => hi.le (htail j hj))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcurve i)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [hdeg]
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg physicalDegree))
  exact_mod_cast (hfiber L hfinite).trans hbudget
end
end Scalar55LeadingLower_2
end
section
set_option maxHeartbeats 1000000
namespace Scalar55LeadingLower_2
noncomputable section
variable {top : Fin 1}
open K1 (K)
open Scalar55LeadingLower (Whole)
open K1_13 (Row Geom extend)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open K1_13_5_5 (freshRow FreshField)
open Finset MvPolynomial
open scoped BigOperators Polynomial
private theorem freshRow_degree_le (f : Row 3) : (freshRow f).totalDegree ≤ f.totalDegree := by
  unfold freshRow MvPolynomial.totalDegree
  exact Finset.sup_mono (support_map_subset (algebraMap Geom[X] FreshField) f)
theorem proof : Scalar55LeadingLower.c2 top := by
  classical
  intro w Γ s hm n f hf hcover
  let part (i : Fin n) := Γ.filter fun γ => RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  let cap (i : Fin n) := 131071 * (f i).totalDegree
  have hsub (i : Fin n) : part i ⊆ Γ := filter_subset _ _
  have hlocal (i : Fin n) : NodeCapacity w (part i) s (cap i) := by
    by_cases hi : Whole (f i)
    · have htop : (f i).degreeOf 2 ≤ 25 :=
        (single_le_sum (f := fun j => (f j).degreeOf 2) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
          (hf.coordinate.trans (by fin_cases top <;> decide))
      obtain ⟨P, hp, hsupport, hall⟩ := chart_of_whole _ (hf.irreducible i) (hf.positive i) htop (hf.weight i) hi
      obtain ⟨hdim, hdeg⟩ := chart_degree _ _ _ hp hsupport
      change 2 * affineDegree P ≤ (131071 : ℚ) * ((freshRow (f i)).totalDegree : ℚ) at hdeg
      apply surface_nodeCapacity (hm.mono (hsub i)) hp.prime hdim
      · intro γ hγ
        have hγΓ := hsub i hγ
        exact hall _ (Polynomial.natDegree_map_le.trans (hm.degree γ hγΓ))
          (mem_filter.mp hγ).2.1
      · have hle : ((freshRow (f i)).totalDegree : ℚ) ≤ ((f i).totalDegree : ℚ) :=
          Nat.cast_le.mpr (freshRow_degree_le (f i))
        simpa only [cap, Nat.cast_mul, Nat.cast_ofNat] using
          hdeg.trans (mul_le_mul_of_nonneg_left hle (by norm_num))
    · have hempty : part i = ∅ := by simp [part, hi]
      rw [hempty]
      exact ⟨∅, by simp, by simp⟩
  let C : NodeFamily w Γ s := ⟨n, part, cap, hsub, hlocal⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨i, hi, hwhole⟩ := hcover γ hγ
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hγ, hi, hwhole⟩⟩
  · change n ≤ Scalar55LeadingPrice.lowerWidth top
    calc
      n = ∑ _i : Fin n, 1 := by simp
      _ ≤ ∑ i, (f i).totalDegree := sum_le_sum fun i _ =>
        (hf.positive i).trans_le (degreeOf_le_totalDegree _ _)
      _ ≤ Scalar55LeadingPrice.lowerWidth top := hf.total
  · change (∑ i, 131071 * (f i).totalDegree) ≤ 131071 * Scalar55LeadingPrice.lowerWidth top
    rw [← mul_sum]
    exact Nat.mul_le_mul_left _ hf.total
end
end Scalar55LeadingLower_2
end

namespace Scalar55LeadingLower
variable {top : Fin 1}

end Scalar55LeadingLower
