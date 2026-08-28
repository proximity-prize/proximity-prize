import ProximityPrize.SubmissionLower.ContactSurfaceSparseSeedCount
import ProximityPrize.SubmissionLower.ContactSurfaceFactorJointSeedCap
import ProximityPrize.SubmissionLower.ContactRegularFactorGate
import ProximityPrize.SubmissionLower.ContactGeometricFactorCover

/-!
# Original regular seed count using the sparse whole-surface gate
-/

namespace ProximityPrize.SubmissionLower.ContactOriginalRegularSparseSeedCount

open scoped Classical BigOperators
open ContactAlignmentParameters ContactCountingCaps
open ContactGenericInitialPoint ContactGenericSurface ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate ContactFactorCaps
open ContactSurfaceSeedCount ContactSurfaceSparseSeedCount
open ContactSurfaceFactorJointSeedCap
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactPolynomialSolutions ContactInterpolation ContactTranslation
open ContactRefinedAgreementY

noncomputable section

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

def originalDegreeVector (F : MvPolynomial (Fin 4) K) : DegreeVector :=
  ⟨F.degreeOf 1, F.degreeOf 2, F.degreeOf 3⟩

theorem selectedPoint_eq_initialPoint (selected : K → Polynomial K) (γ : K) :
    selectedPoint (polynomialEmbedding K) selected γ =
      fun i : Fin 3 => initialPoint K (selected γ) γ i.succ := rfl

theorem selectedPoint_surface_evaluation
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K) (γ : K) :
    MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
      (surfaceMap (polynomialEmbedding K) F) =
        polynomialEmbedding K (specialization K (selected γ) γ F) := by
  rw [selectedPoint_eq_initialPoint]
  simpa only [canonical_geometricSurfaceMap] using
    eval_at_actual_generic_initial_point K (selected γ) γ F

theorem selectedPoint_regular_of_specialization
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K) (γ : K)
    (hregular : specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    MvPolynomial.eval₂Hom ((polynomialEmbedding K).comp Polynomial.C)
      (polynomialPoint ((polynomialEmbedding K).comp Polynomial.C)
        (selected γ) γ ((polynomialEmbedding K) Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 :=
  (initialPoint_regular_iff K F (selected γ) γ).mpr hregular

abbrev GeometricFactor (F : MvPolynomial (Fin 4) K) :=
  {g : MvPolynomial (Fin 3) (GenericField K) //
    g ∈ surfaceFactors (polynomialEmbedding K) F}

def geometricSeeds (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (g : GeometricFactor K F) : Finset K := by
  classical
  exact Γ.filter (fun γ =>
    MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ) g.1 = 0)

theorem geometricSeeds_subset
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (g : GeometricFactor K F) : geometricSeeds K F selected Γ g ⊆ Γ := by
  classical
  exact Finset.filter_subset _ _

theorem card_le_sum_geometricSeeds
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (selected : K → Polynomial K) (Γ : Finset K)
    (hsolutions : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0) :
    Γ.card ≤ ∑ g : GeometricFactor K F, (geometricSeeds K F selected Γ g).card := by
  classical
  have hcover : Γ ⊆ Finset.univ.biUnion (geometricSeeds K F selected Γ) := by
    intro γ hγ
    have hz : MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
        (surfaceMap (polynomialEmbedding K) F) = 0 := by
      rw [selectedPoint_surface_evaluation, hsolutions γ hγ, map_zero]
    obtain ⟨g, hg, hzg⟩ := exists_surfaceFactor_zero (polynomialEmbedding K)
      (polynomialEmbedding_injective K) F hF
      (selectedPoint (polynomialEmbedding K) selected γ) hz
    exact Finset.mem_biUnion.mpr ⟨⟨g, hg⟩, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hγ, hzg⟩⟩
  exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le

theorem geometricFactor_degree_le
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (g : GeometricFactor K F) (i : Fin 3) :
    g.1.degreeOf i ≤ F.degreeOf i.succ := by
  have hdiv := (surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).2
  exact (coordinate_degree_le_of_dvd i g.1 _ hdiv
    (surfaceMap_ne_zero (polynomialEmbedding K) (polynomialEmbedding_injective K) F hF)).trans
      (surfaceMap_degreeOf_le (polynomialEmbedding K) F i)

theorem geometricFactor_sum_degree_le
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (i : Fin 3) :
    (∑ g : GeometricFactor K F, g.1.degreeOf i) ≤ F.degreeOf i.succ := by
  classical
  have hb := surfaceFactors_degree_budget (polynomialEmbedding K)
    (polynomialEmbedding_injective K) F hF i
  rw [← Finset.sum_attach (surfaceFactors (polynomialEmbedding K) F)
    (fun g => g.degreeOf i)] at hb
  simpa only [Finset.attach_eq_univ] using hb

def sumVector {I : Type} [Fintype I] (v : I → DegreeVector) : DegreeVector :=
  ⟨∑ i, (v i).y, ∑ i, (v i).r, ∑ i, (v i).z⟩

def dot (a b : DegreeVector) : ℕ := a.y * b.y + a.r * b.r + a.z * b.z

def wholeCoefficients : DegreeVector :=
  ⟨wholeNumerator unitY, wholeNumerator unitR, wholeNumerator unitZ⟩

theorem whole_eq_dot (v : DegreeVector) :
    wholeNumerator v = dot v wholeCoefficients := by
  simp only [wholeNumerator, wholeCoefficients, dot, mixed, unitY, unitR, unitZ]
  ring

theorem dot_sum_left {I : Type} [Fintype I] (v : I → DegreeVector) (a : DegreeVector) :
    dot (sumVector v) a = ∑ i, dot (v i) a := by
  simp only [dot, sumVector, Finset.sum_add_distrib, Finset.sum_mul]

theorem whole_sum {I : Type} [Fintype I] (v : I → DegreeVector) :
    wholeNumerator (sumVector v) = ∑ i, wholeNumerator (v i) := by
  rw [whole_eq_dot, dot_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact (whole_eq_dot (v i)).symm

theorem dot_mono_left {a b : DegreeVector} (c : DegreeVector)
    (h : a.y ≤ b.y ∧ a.r ≤ b.r ∧ a.z ≤ b.z) :
    dot a c ≤ dot b c :=
  Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1)
      (Nat.mul_le_mul_right c.r h.2.1))
    (Nat.mul_le_mul_right c.z h.2.2)

theorem sum_wholeNumerator_geometricFactors_le
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (∑ g : GeometricFactor K F, wholeNumerator (degreeVector g.1)) ≤
      wholeNumerator (originalDegreeVector K F) := by
  classical
  rw [← whole_sum (fun g : GeometricFactor K F => degreeVector g.1)]
  rw [whole_eq_dot, whole_eq_dot]
  exact dot_mono_left _ ⟨geometricFactor_sum_degree_le K F hF 0,
    geometricFactor_sum_degree_le K F hF 1, geometricFactor_sum_degree_le K F hF 2⟩

theorem original_regular_seed_bound_sparse
    [CharP K prime]
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hRpos : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolutions : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ,
      specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagreement : ∀ γ ∈ Γ,
      agreements ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w errors) :
    Γ.card * gap ^ 2 ≤ wholeNumerator (originalDegreeVector K F) := by
  classical
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hc := degree_bounds_of_mem_box F weightedCap w seedTotalCap slopeCap
    (by norm_num [w]) hbox
  have hY : F.degreeOf 1 ≤ yCap := hc.1
  have hR : F.degreeOf 2 ≤ slopeCap := hc.2.1
  have hZ : F.degreeOf 3 ≤ seedTotalCap := hc.2.2
  have hHY : (ContactTaylorNumerators.polyH K F).degreeOf (1 : Fin 4) ≤ yCap - 1 :=
    polyH_Y_degree_le_of_mem_box F weightedCap w seedTotalCap slopeCap yCap
      hbox (by norm_num [w]) (by
        norm_num [weightedCap, ContactAlignmentParameters.multiplicity,
          agreements, w, yCap])
  have hseed : MvPolynomial.weightedTotalDegree seedWeights F ≤ seedTotalCap :=
    ((mem_globalCoefficientBox_iff F weightedCap w seedTotalCap slopeCap
      (by norm_num [weightedCap, ContactAlignmentParameters.multiplicity, agreements])).mp hbox).1
  have hsmall : F.degreeOf 2 < prime := hR.trans_lt (by norm_num [slopeCap, prime])
  have hcount (g : GeometricFactor K F) :
      (geometricSeeds K F selected Γ g).card * gap ^ 2 ≤ wholeNumerator (degreeVector g.1) := by
    obtain ⟨hgirred, hgdiv⟩ := surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
    have hgate := geometric_factor_regular_gate K (GenericField K) F hF prime hRpos hsmall
      g.1 hgirred (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
    have hHproper : ¬ g.1 ∣ surfaceMap (polynomialEmbedding K)
        (MvPolynomial.pderiv (2 : Fin 4) F) := by
      simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
    have hgcaps : HasCaps g.1 ContactProjectionParameters.surfaceVector := by
      intro i
      fin_cases i
      · exact (geometricFactor_degree_le K F hF.ne_zero g 0).trans hY
      · exact (geometricFactor_degree_le K F hF.ne_zero g 1).trans hR
      · exact (geometricFactor_degree_le K F hF.ne_zero g 2).trans hZ
    have hgjoint : ∀ d ∈ g.1.support, d 0 + d 2 ≤ seedTotalCap :=
      surface_factor_joint_seed_cap (polynomialEmbedding K) F g.1 seedTotalCap
        (polynomialEmbedding_injective K) hF.ne_zero hgdiv (fun d hd => (hbox hd).1)
    have hsub := geometricSeeds_subset K F selected Γ g
    exact whole_surface_seed_bound_fixed_sparse (polynomialEmbedding K) F g.1 hgirred hgdiv
      hgate.1 hHproper hgcaps hgjoint hseed hY hR hZ hHY selected
      (geometricSeeds K F selected Γ g) nodes x u₀ u₁ hinj hnodes
      (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => hsolutions γ (hsub hγ))
      (fun γ hγ => selectedPoint_regular_of_specialization K F selected γ
        (hregular γ (hsub hγ)))
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w errors hsub hnoPencil)
  calc
    Γ.card * gap ^ 2 ≤
        (∑ g : GeometricFactor K F, (geometricSeeds K F selected Γ g).card) * gap ^ 2 :=
      Nat.mul_le_mul_right _ (card_le_sum_geometricSeeds K F hF.ne_zero selected Γ hsolutions)
    _ = ∑ g : GeometricFactor K F, (geometricSeeds K F selected Γ g).card * gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F, wholeNumerator (degreeVector g.1) :=
      Finset.sum_le_sum (fun g _ => hcount g)
    _ ≤ wholeNumerator (originalDegreeVector K F) :=
      sum_wholeNumerator_geometricFactors_le K F hF.ne_zero

end

end ProximityPrize.SubmissionLower.ContactOriginalRegularSparseSeedCount

#print axioms ProximityPrize.SubmissionLower.ContactOriginalRegularSparseSeedCount.original_regular_seed_bound_sparse
