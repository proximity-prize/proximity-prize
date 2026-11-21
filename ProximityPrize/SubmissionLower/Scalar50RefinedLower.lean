import ProximityPrize.SubmissionLower.Scalar50RefinedLowerBase

set_option Elab.async false

section
set_option autoImplicit false
namespace ScalarRefined_1_1
noncomputable section
variable {top : Fin 3}
open K1_13 (Row)
open K1_13_5 (separant)
open ScalarRefined (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow GeometricX genericRow)
open K1_13_5_4_2 (JetPoint ExponentSpace boxExponents graphLocus graphCurve capBody mixedVolume4)
open ScalarRefined (taylorLength)
open ScalarRefined (Whole)
open ScalarRefined_1 (oldCutIdeal)
open MvPolynomial
def factorCurves (f : Row 3) : Finset (Ideal (GeoRow 3)) := by
  classical
  exact if Whole f then ∅ else
    (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))
abbrev lastBox (top : Fin 3) := liftedBox top (taylorLength + 2)
abbrev lastExponents (top : Fin 3) := boxExponents (lastBox top) taylorLength
abbrev lastMap (top : Fin 3) := monomialMap GeometricX (lastExponents top)
def sectionIdeal (top : Fin 3) (f : Row 3) (P : Ideal (GeoRow 3)) :
    Ideal (MvPolynomial (lastExponents top) GeometricX) :=
  (graphCurve f P).comap (lastMap top)
def IsSectionCurve (top : Fin 3) (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  (sectionIdeal top f P).IsPrime ∧ (affineHilbertPolynomial (sectionIdeal top f P)).natDegree = 1
def sectionDegree (top : Fin 3) (f : Row 3) (P : Ideal (GeoRow 3)) : ℚ :=
  affineDegree (sectionIdeal top f P)
structure GenericSection (top : Fin 3) (f : Row 3) where
  polynomial : GeoRow 4
  support : InLiftedBox polynomial (lastBox top) taylorLength
  points : Ideal (GeoRow 3) → Finset JetPoint
  card_eq : ∀ P ∈ factorCurves f, ((points P).card : ℚ) = sectionDegree top f P
  proper : ∀ P ∈ factorCurves f, polynomial ∉ graphCurve f P
  roots : ∀ P ∈ factorCurves f, ∀ y ∈ points P,
    y ∈ graphLocus f P ∧ eval y polynomial = 0
  off_other_curves : ∀ P ∈ factorCurves f, ∀ P' ∈ factorCurves f, P ≠ P' →
    ∀ y ∈ points P, y ∉ graphLocus f P'
def lastMixedVolume (top : Fin 3) (first : Set ExponentSpace) : ℝ :=
  mixedVolume4 ![first, capBody (graphBox top) 1,
    capBody (liftedBox top (taylorLength + 1)) (taylorLength - 1),
    capBody (lastBox top) taylorLength]
end
end ScalarRefined_1_1
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1
noncomputable section
variable {top : Fin 3}
open K1_13 (Row Geom Shape)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericCoeff_injective genericRow
  liftRow regularLocus graphPoint)
open K1_13_5_4_2 (boxExponents graphCurve eval_represents_iff)
open ScalarRefined (taylorLength)
open ScalarRefined (Whole)
open ScalarRefined_1 (oldCut oldCutIdeal properComponents CurveIndex componentLength nextCutLocus
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
      (factorCurves (f i)).image (fun P => (i, P)) := Scalar70LeadingLower_1_1.properComponents_eq f
theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {a : CurveIndex n} :
    a ∈ properComponents f ↔ a.2 ∈ factorCurves (f a.1) := by
  classical
  rcases a with ⟨i, P⟩
  rw [properComponents_eq]
  simp
theorem sum_properComponents {n : ℕ} (f : Fin n → Row 3) (v : CurveIndex n → ℕ) :
    (∑ a ∈ properComponents f, v a) =
      ∑ i, ∑ P ∈ factorCurves (f i), v (i, P) := by
  classical
  rw [properComponents_eq, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨Q, _, he⟩ := Finset.mem_image.mp hb
    exact hij (Prod.mk.inj he).1.symm
theorem componentLength_of_retained {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    0 < componentLength f P ∧ componentLength f P < ⊤ := Scalar70LeadingLower_1_1.componentLength_of_retained hP
theorem componentLength_toNat {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    ((componentLength f P).toNat : ℕ∞) = componentLength f P :=
  ENat.natCast_toNat (componentLength_of_retained hP).2.ne
theorem componentLength_toNat_pos {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) : 0 < (componentLength f P).toNat := by
  have h := (componentLength_of_retained hP).1
  rw [← componentLength_toNat hP] at h
  exact_mod_cast h
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
theorem section_curve {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) : IsSectionCurve top f P := by
  have hm := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let := hm.1.isPrime
  obtain ⟨hprime, hdim⟩ := graph_dimension f P hm.2
  refine ⟨hprime.comap (lastMap top), ?_⟩
  unfold sectionIdeal
  rw [natDegree_affineHilbertPolynomial_comap_of_surjective (lastMap top)
      (monomialMap_surjective lastExponents_single), hdim, retained_dimension hf hP]
private theorem eval_factor_of_regular {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) {x : Fin 3 → GeometricX} (hx : x ∈ regularLocus f P) :
    eval x (genericRow f) = 0 :=
  hx.1 _ ((Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2).1.le
    (Ideal.subset_span (by simp)))
private theorem next_notMem_graphCurve {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (T : LiftedChart top f) (hnext : genericRow (oldNext f) ∉ P) :
    T.next ∉ graphCurve f P := by
  intro hn
  have hm := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let := hm.1.isPrime
  have hvanish : genericRow (separant f) * genericRow (oldNext f) ∈
      vanishingIdeal GeometricX (zeroLocus GeometricX P) := by
    intro x hx
    change eval x (_ * _) = 0
    rw [map_mul]
    by_cases hs : eval x (genericRow (separant f)) = 0
    · rw [hs, zero_mul]
    · have hr : x ∈ regularLocus f P := ⟨hx, hs⟩
      have he : eval (graphPoint f x) T.next = 0 := hn _ ⟨x, hr, rfl⟩
      rw [(eval_represents_iff T.next_represents (eval_factor_of_regular hP hr) hs).mp he,
        mul_zero]
  rw [IsPrime.vanishingIdeal_zeroLocus P] at hvanish
  exact (hm.1.isPrime.mem_or_mem hvanish).elim hm.2 hnext
theorem points_le_sectionDegree {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hcurve : IsSectionCurve top f P) (T : LiftedChart top f)
    (hnext : genericRow (oldNext f) ∉ P) :
    (nextCutLocus f P).Finite ∧ ((nextCutLocus f P).ncard : ℚ) ≤ sectionDegree top f P := by
  let h : T.next ∈ restrictSupport GeometricX (lastExponents top) := T.next_box
  let l := monomialLift T.next h
  have hmap : (lastMap top) l = T.next := monomialMap_monomialLift _ _
  have hl : l ∉ sectionIdeal top f P := by
    intro hm
    change (lastMap top) l ∈ graphCurve f P at hm
    rw [hmap] at hm
    exact next_notMem_graphCurve hP T hnext hm
  let J := sectionIdeal top f P ⊔ Ideal.span {l}
  obtain ⟨hdim, hbound⟩ := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hcurve.1 hl (totalDegree_monomialLift_le_one _ _)
  change (affineHilbertPolynomial J).natDegree ≤ _ at hdim
  rw [hcurve.2] at hdim hbound
  have hzero : (affineHilbertPolynomial J).natDegree = 0 := Nat.eq_zero_of_le_zero hdim
  have hdeg : affineDegree J ≤ sectionDegree top f P := by
    rw [sectionDegree, affineDegree_of_natDegree_eq_zero hzero, affineDegree, hcurve.2]
    simpa [J] using hbound
  obtain ⟨hfinite, hcard⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) J hzero
  let m := fun x => monomialPoint (lastExponents top) (graphPoint f x)
  have hinj : Function.Injective m :=
    (monomialPoint_injective lastExponents_single).comp (graphPoint_injective f)
  have hsubset : m '' nextCutLocus f P ⊆ zeroLocus GeometricX J := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    apply sup_le
    · apply mem_zeroLocus_iff_le_ker_aeval.mp
      apply (monomialPoint_mem_zeroLocus_comap_iff lastExponents_single _ _).mpr
      exact zeroLocus_vanishingIdeal_le _ ⟨x, hx.1, rfl⟩
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker, aeval_monomialPoint, hmap]
      exact (eval_represents_iff T.next_represents
        (eval_factor_of_regular hP hx.1) hx.1.2).mpr hx.2
  refine ⟨(hfinite.subset hsubset).of_finite_image hinj.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective _ hinj]
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard hsubset hfinite)).trans (hcard.trans hdeg)
end
end ScalarRefined_1_1
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1
noncomputable section
variable {top : Fin 3}
open ScalarRefined (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow)
open K1_13_5_4_2 (JetPoint fourCutIdeal pointIdeal pointLength downBody capBody)
open K1_13_5_4_2_4 (Exponent Downward cutIdeal downSupport capSupport mem_downSupport mem_capSupport
  latticeBody latticeBody_downSupport latticeBody_capSupport)
open ScalarRefined (taylorLength)
open MvPolynomial
open scoped BigOperators Pointwise
open private mixed_eq_generic downSupport_downward capSupport_downward zero_mem_capSupport
  from ProximityPrize.SubmissionLower.Fast048
private theorem deformation_bound : K1_13_5_4_2_4.c1 :=
  K1_13_5_4_2_4_1.of_children K1_13_5_4_2_4_1_1.proof K1_13_5_4_2_4_1_2.proof
private theorem generic_degree : K1_13_5_4_2_4.c2 :=
  K1_13_5_4_2_4_2.of_children K1_13_5_4_2_4_2_1.proof K1_13_5_4_2_4_2_2.proof
    (K1_13_5_4_2_4_2_3.of_children K1_13_5_4_2_4_2_3_1.proof K1_13_5_4_2_4_2_3_2.proof)
theorem sparse_bound
    (F G E L : GeoRow 4) (hF : F ≠ 0) (hG : InLiftedBox G (graphBox top) 1)
    (hE : InLiftedBox E (liftedBox top (taylorLength + 1)) (taylorLength - 1))
    (hL : InLiftedBox L (lastBox top) taylorLength) (points : Finset JetPoint)
    (hpoints : ∀ y ∈ points, pointIdeal y ∈ (fourCutIdeal F G E L).minimalPrimes) :
    (↑(∑ y ∈ points, (pointLength (fourCutIdeal F G E L) y).toNat) : ℝ) ≤
      lastMixedVolume top (downBody F) := by
  classical
  let A : Fin 4 → Finset Exponent :=
    ![downSupport F, capSupport (graphBox top) 1,
      capSupport (liftedBox top (taylorLength + 1)) (taylorLength - 1),
      capSupport (lastBox top) taylorLength]
  let f : Fin 4 → GeoRow 4 := ![F, G, E, L]
  have hz : ∀ i, 0 ∈ A i := by
    intro i
    fin_cases i
    · obtain ⟨e, he⟩ := support_nonempty.mpr hF
      exact mem_downSupport.mpr ⟨e, he, fun _ => Nat.zero_le _⟩
    · exact zero_mem_capSupport _ _
    · exact zero_mem_capSupport _ _
    · exact zero_mem_capSupport _ _
  have hd : ∀ i, Downward (A i) := by
    intro i
    fin_cases i
    · exact downSupport_downward F
    · exact capSupport_downward _ _
    · exact capSupport_downward _ _
    · exact capSupport_downward _ _
  have hv (j : Fin 4) : ∃ i, Finsupp.single j 1 ∈ A i := by
    exact ⟨3, mem_capSupport.mpr (lastExponents_single j)⟩
  have hsup : ∀ i, (f i).support ⊆ A i := by
    intro i
    fin_cases i
    · exact fun a ha => mem_downSupport.mpr ⟨a, ha, le_rfl⟩
    · exact fun a ha => mem_capSupport.mpr (hG a ha)
    · exact fun a ha => mem_capSupport.mpr (hE a ha)
    · exact fun a ha => mem_capSupport.mpr (hL a ha)
  have hJ : cutIdeal f = fourCutIdeal F G E L := by
    unfold cutIdeal fourCutIdeal
    apply congrArg Ideal.span
    ext p
    simp [f, or_left_comm, or_comm]
  obtain ⟨hfinite, hmv⟩ := mixed_eq_generic generic_degree K1_13_5_4_2_4_3.proof A hz hd hv
  have hbound := deformation_bound A hz hfinite f hsup points (by simpa only [hJ] using hpoints)
  have hbodies : (fun i => latticeBody (A i)) =
      ![downBody F, capBody (graphBox top) 1,
        capBody (liftedBox top (taylorLength + 1)) (taylorLength - 1), capBody (lastBox top) taylorLength] := by
    funext i
    fin_cases i
    · exact latticeBody_downSupport F
    · exact latticeBody_capSupport _ _ (show (graphBox top).j ≤ (graphBox top).b by fin_cases top <;> decide) (show 2 * (graphBox top).t ≤ (graphBox top).j by fin_cases top <;> decide)
    · exact latticeBody_capSupport _ _ (show (liftedBox top (taylorLength + 1)).j ≤ (liftedBox top (taylorLength + 1)).b by fin_cases top <;> decide)
        (show 2 * (liftedBox top (taylorLength + 1)).t ≤ (liftedBox top (taylorLength + 1)).j by fin_cases top <;> decide)
    · exact latticeBody_capSupport _ _ (show (lastBox top).j ≤ (lastBox top).b by fin_cases top <;> decide)
        (show 2 * (lastBox top).t ≤ (lastBox top).j by fin_cases top <;> decide)
  simpa only [hJ, hmv, hbodies, lastMixedVolume] using (Nat.cast_le (α := ℝ)).mpr hbound
end
end ScalarRefined_1_1
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1
noncomputable section
variable {top : Fin 3}
open K1_13 (Row Shape indexDegree)
open K1_13_5 (separant)
open ScalarRefined (lowBox liftedBox mixedCoefficients)
open K1_13_5_4 (InLiftedBox GeometricX GeoRow genericRow liftRow graphPoint regularLocus)
open K1_13_5_4_2 (graphLocus JetPoint eval_liftRow_graphPoint)
open ScalarRefined (taylorLength)
open ScalarRefined (SecondFactors)
open ScalarRefined_1 (LiftedChart reconstruct CoefficientIdeal)
open MvPolynomial
open scoped BigOperators Pointwise
open private ratio_image_degree box_mono from ProximityPrize.SubmissionLower.Fast048
private theorem separator_box {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors top f)
    (i : Fin n) : InLiftedBox (liftRow (genericRow (separant (f i)))) (⟨(ScalarRefined.lowerWidth top - 1), (ScalarRefined.lowerIndex top - 2), (ScalarRefined.lowerTop top - 1)⟩ : K1_13.Shape) 0 := by
  classical
  intro a ha
  rw [liftRow, support_rename_of_injective (Fin.castSucc_injective 3)] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hs : b ∈ (separant (f i)).support := support_map_subset _ _ hb
  let m : Fin 3 →₀ ℕ := b + Finsupp.single 2 1
  have hm : m ∈ (f i).support := by
    rw [MvPolynomial.mem_support_iff, separant, coeff_pderiv] at hs
    exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs)
  have hb₀ : m.degree ≤ (⟨ScalarRefined.lowerWidth top, ScalarRefined.lowerIndex top, ScalarRefined.lowerTop top⟩ : K1_13.Shape).b :=
    (le_totalDegree hm).trans ((Finset.single_le_sum (fun j _ => Nat.zero_le ((f j).totalDegree))
      (Finset.mem_univ i)).trans hf.total)
  have hj₀ : (m.sum fun j a => j.val * a) ≤ (⟨ScalarRefined.lowerWidth top, ScalarRefined.lowerIndex top, ScalarRefined.lowerTop top⟩ : K1_13.Shape).j :=
    (Finset.le_sup hm).trans ((Finset.single_le_sum (fun j _ => Nat.zero_le (indexDegree (f j)))
      (Finset.mem_univ i)).trans hf.index)
  have ht₀ : m 2 ≤ (⟨ScalarRefined.lowerWidth top, ScalarRefined.lowerIndex top, ScalarRefined.lowerTop top⟩ : K1_13.Shape).t :=
    (monomial_le_degreeOf 2 hm).trans ((Finset.single_le_sum
      (fun j _ => Nat.zero_le ((f j).degreeOf 2)) (Finset.mem_univ i)).trans hf.coordinate)
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
private theorem pow_separator_box {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors top f)
    (i : Fin n) (r : ℕ) :
    InLiftedBox (liftRow (genericRow (separant (f i))) ^ r)
      ⟨(ScalarRefined.lowerWidth top - 1) * r, (ScalarRefined.lowerIndex top - 2) * r, (ScalarRefined.lowerTop top - 1) * r⟩ 0 := by
  classical
  induction r with
  | zero =>
      simp only [pow_zero, InLiftedBox, support_one, Finset.mem_singleton]
      rintro a rfl
      simp
  | succ r ih =>
      intro a ha
      rw [pow_succ] at ha
      obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ ha)
      have ⟨hb₀, hb₁, hb₂, hb₃⟩ := ih b hb
      have ⟨hc₀, hc₁, hc₂, hc₃⟩ := separator_box hf i c hc
      simp only [Finsupp.add_apply, Nat.mul_succ] at *
      exact ⟨by omega, by omega, by omega, by omega⟩
theorem coefficient_image_degree {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors top f)
    (i : Fin n) (P : Ideal (GeoRow 3)) (T : LiftedChart top (f i))
    (hcurve : IsSectionCurve top (f i) P) (hone : 1 ≤ sectionDegree top (f i) P) :
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      affineDegree Q ≤ sectionDegree top (f i) P ∧
      ∀ y ∈ regularLocus (f i) P, reconstruct (f i) T.numerator y ∈ zeroLocus GeometricX Q := by
  let A := monomialPoint (lastExponents top) '' graphLocus (f i) P
  have hA : sectionIdeal top (f i) P = vanishingIdeal GeometricX A := by
    ext p
    constructor
    · intro hp
      rintro _ ⟨z, hz, rfl⟩
      rw [aeval_monomialPoint]
      exact hp z hz
    · intro hp z hz
      have he := hp _ ⟨z, hz, rfl⟩
      rwa [aeval_monomialPoint] at he
  obtain ⟨D, hD_eq⟩ : ∃ D : GeoRow 4,
      D = liftRow (genericRow (separant (f i))) ^ (taylorLength - 4) := ⟨_, rfl⟩
  have hD : D ∈ restrictSupport GeometricX (lastExponents top) := by
    have hbox : InLiftedBox D
        ⟨(ScalarRefined.lowerWidth top - 1) * (taylorLength - 4), (ScalarRefined.lowerIndex top - 2) * (taylorLength - 4), (ScalarRefined.lowerTop top - 1) * (taylorLength - 4)⟩ 0 := by
      rw [hD_eq]
      exact pow_separator_box hf i (taylorLength - 4)
    change InLiftedBox D (lastBox top) taylorLength
    exact box_mono (show (ScalarRefined.lowerWidth top - 1) * (taylorLength - 4) ≤ (lastBox top).b by fin_cases top <;> decide)
      (show (ScalarRefined.lowerIndex top - 2) * (taylorLength - 4) ≤ (lastBox top).j by fin_cases top <;> decide) (show (ScalarRefined.lowerTop top - 1) * (taylorLength - 4) ≤ (lastBox top).t by fin_cases top <;> decide)
      (Nat.zero_le _) hbox
  have hN (j : Fin taylorLength) : T.numerator j ∈ restrictSupport GeometricX (lastExponents top) := by
    change InLiftedBox (T.numerator j) (lastBox top) taylorLength
    exact box_mono (show (liftedBox top taylorLength).b ≤ (lastBox top).b by fin_cases top <;> decide)
      (show (liftedBox top taylorLength).j ≤ (lastBox top).j by fin_cases top <;> decide) (show (liftedBox top taylorLength).t ≤ (lastBox top).t by fin_cases top <;> decide)
      (Nat.sub_le _ _) (T.coefficient_box j)
  let d := monomialLift D hD
  let ν (j : Fin taylorLength) := monomialLift (T.numerator j) (hN j)
  have hdeval (z : JetPoint) : eval (monomialPoint (lastExponents top) z) d = eval z D := by
    have hmap : (lastMap top) d = D := monomialMap_monomialLift D hD
    simpa only [aeval_eq_eval, hmap] using aeval_monomialPoint z d
  have hνeval (z : JetPoint) (j : Fin taylorLength) :
      eval (monomialPoint (lastExponents top) z) (ν j) = eval z (T.numerator j) := by
    have hmap : (lastMap top) (ν j) = T.numerator j := monomialMap_monomialLift _ _
    simpa only [aeval_eq_eval, hmap] using aeval_monomialPoint z (ν j)
  have hden (z) (hz : z ∈ A) : eval z d ≠ 0 := by
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    rw [hdeval, hD_eq, map_pow, eval_liftRow_graphPoint]
    exact pow_ne_zero _ hx.2
  obtain ⟨Q, hp, hd, hb, hz⟩ := ratio_image_degree A _ hA hcurve.1 hcurve.2 hone d ν
    (totalDegree_monomialLift_le_one _ _) (fun j => totalDegree_monomialLift_le_one _ _) hden
  refine ⟨Q, hp, hd, hb, fun x hx => ?_⟩
  have hz' := hz (monomialPoint (lastExponents top) (graphPoint (f i) x)) ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  unfold reconstruct
  simpa only [hνeval, hdeval, hD_eq, map_pow, eval_liftRow_graphPoint] using hz'
end
end ScalarRefined_1_1
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1
noncomputable section
variable {top : Fin 3}
open K1_13 (Row)
open K1_13_5_4 (GeoRow genericRow liftRow graph)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal pointLength downBody
  localLength_lt_top)
open ScalarRefined (SecondFactors mixedBudget)
open ScalarRefined_1 (LiftedChart CurveIndex properComponents componentLength)
open MvPolynomial
open scoped BigOperators
open private lift_generic_ne_zero from ProximityPrize.SubmissionLower.Fast048
def c1 (top : Fin 3) : Prop :=
  ∀ (f : Row 3), (∀ P ∈ factorCurves f, IsSectionCurve top f P) →
    Nonempty (GenericSection top f)
def c2 (top : Fin 3) : Prop :=
  ∀ (f : Row 3), Irreducible f → 0 < f.degreeOf 2 → ∀ (T : LiftedChart top f) (L : GeoRow 4),
    (∀ P ∈ factorCurves f, L ∉ graphCurve f P) →
    ∀ P ∈ factorCurves f, ∀ y ∈ graphLocus f P, eval y L = 0 →
      let J := fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L
      pointIdeal y ∈ J.minimalPrimes ∧ componentLength f P ≤ pointLength J y
def c3 (top : Fin 3) : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∑ i, lastMixedVolume top (downBody (liftRow (genericRow (f i))))) ≤ (mixedBudget top : ℝ)
private theorem section_cost (hlocal : c2 top) {f : Row 3}
    (hf : Irreducible f) (hpos : 0 < f.degreeOf 2) (T : LiftedChart top f) (S : GenericSection top f) :
    (↑(∑ P ∈ factorCurves f, (componentLength f P).toNat * (S.points P).card) : ℝ) ≤
      lastMixedVolume top (downBody (liftRow (genericRow f))) := by
  classical
  let J := fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut S.polynomial
  let points := (factorCurves f).biUnion S.points
  have hlocal' (P) (hP : P ∈ factorCurves f) (y) (hy : y ∈ S.points P) :
      pointIdeal y ∈ J.minimalPrimes ∧ componentLength f P ≤ pointLength J y :=
    hlocal f hf hpos T S.polynomial S.proper P hP y (S.roots P hP y hy).1
      (S.roots P hP y hy).2
  have hmin : ∀ y ∈ points, pointIdeal y ∈ J.minimalPrimes := by
    intro y hy
    obtain ⟨P, hP, hyP⟩ := Finset.mem_biUnion.mp hy
    exact (hlocal' P hP y hyP).1
  have hd : Set.PairwiseDisjoint (↑(factorCurves f)) S.points := by
    intro P hP P' hP' hne
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    exact S.off_other_curves P hP P' hP' hne y hy (S.roots P' hP' y hy').1
  have hcost : (∑ P ∈ factorCurves f, (componentLength f P).toNat * (S.points P).card) ≤
      ∑ y ∈ points, (pointLength J y).toNat := by
    change _ ≤ ∑ y ∈ (factorCurves f).biUnion S.points, (pointLength J y).toNat
    rw [Finset.sum_biUnion hd]
    apply Finset.sum_le_sum
    intro P hP
    calc
      _ = ∑ _ ∈ S.points P, (componentLength f P).toNat := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y hy
        exact ENat.toNat_le_toNat (hlocal' P hP y hy).2 (localLength_lt_top (hmin y
          (Finset.mem_biUnion.mpr ⟨P, hP, hy⟩))).ne
  exact (Nat.cast_le.mpr hcost).trans
    (sparse_bound _ _ _ _ (lift_generic_ne_zero hf.ne_zero) T.graph_box T.cut_box S.support points hmin)
theorem of_children (h1 : c1 top) (h2 : c2 top) (h3 : c3 top) :
    ∀ n (f : Fin n → Row 3), SecondFactors top f → ∀ T : ∀ i, LiftedChart top (f i),
      Nonempty (ScalarRefined_1.MixedSections top f T) := by
  classical
  intro n f hf T
  have hcurve (i : Fin n) (P) (hP : P ∈ factorCurves (f i)) : IsSectionCurve top (f i) P :=
    section_curve (hf.irreducible i) hP
  let S (i : Fin n) := Classical.choice (h1 (f i) (hcurve i))
  let e : CurveIndex n → ℕ := fun a => (componentLength (f a.1) a.2).toNat
  let d : CurveIndex n → ℕ := fun a => ((S a.1).points a.2).card
  have hdeg (a : CurveIndex n) (ha : a ∈ properComponents f) :
      (d a : ℚ) = sectionDegree top (f a.1) a.2 :=
    (S a.1).card_eq a.2 (mem_properComponents.mp ha)
  refine ⟨⟨e, d, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun _ ha => componentLength_toNat (mem_properComponents.mp ha)
  · exact fun _ ha => componentLength_toNat_pos (mem_properComponents.mp ha)
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [sum_properComponents, Nat.cast_sum]
    exact (Finset.sum_le_sum fun i _ =>
      section_cost h2 (hf.irreducible i) (hf.positive i) (T i) (S i)).trans (h3 n f hf)
  · intro a ha hn
    have hp := mem_properComponents.mp ha
    obtain ⟨hfin, hcard⟩ := points_le_sectionDegree hp (hcurve _ _ hp) (T a.1) hn
    exact ⟨hfin, Nat.cast_le.mp (hcard.trans_eq (hdeg a ha).symm)⟩
  · intro a ha _
    have hp := mem_properComponents.mp ha
    have hC := hcurve _ _ hp
    have hpos : 0 < d a := by
      have h : (0 : ℚ) < (d a : ℚ) := by
        rw [hdeg a ha]
        exact affineDegree_pos hC.1.ne_top
      exact_mod_cast h
    have hone : 1 ≤ sectionDegree top (f a.1) a.2 := by
      rw [← hdeg a ha]
      exact_mod_cast (Nat.succ_le_of_lt hpos)
    obtain ⟨Q, hprime, hdim, hb, hrec⟩ := coefficient_image_degree hf a.1 a.2 (T a.1) hC hone
    exact ⟨Q, hprime, hdim, hpos, hb.trans_eq (hdeg a ha).symm, hrec⟩
end
end ScalarRefined_1_1
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1_1
noncomputable section
variable {top : Fin 3}
open K1_13 (Row)
open K1_13_5 (separant lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow regularLocus graph graphPoint)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve eval_liftRow_graphPoint eval_graph_graphPoint)
open ScalarRefined_1 (oldCutIdeal)
open ScalarRefined_1_1 (factorCurves mem_factorCurves lastExponents lastExponents_single lastMap
  sectionIdeal IsSectionCurve)
open MvPolynomial
open private K1_13_5_4_2.three_ne_zero from ProximityPrize.SubmissionLower.Fast048
open private graphCurve_comap from ProximityPrize.SubmissionLower.Fast048
abbrev EmbeddedPoint (top : Fin 3) := (lastExponents top) → GeometricX
def jetOfEmbedded (top : Fin 3) (z : (EmbeddedPoint top)) : JetPoint :=
  fun i => z ⟨Finsupp.single i 1, lastExponents_single i⟩
private theorem jetOf_monomialPoint (y : JetPoint) :
    jetOfEmbedded top (monomialPoint (lastExponents top) y) = y :=
  funext fun i => monomialPoint_single y (lastExponents_single i)
theorem monomialPoint_jetOf {f : Row 3} {P : Ideal (GeoRow 3)} {z : (EmbeddedPoint top)}
    (hz : z ∈ zeroLocus GeometricX (sectionIdeal top f P)) :
    monomialPoint (lastExponents top) (jetOfEmbedded top z) = z := by
  obtain ⟨y, hy⟩ := exists_monomialPoint_eq_of_mem_zeroLocus_ker lastExponents_single
    (zeroLocus_anti_mono (show RingHom.ker (lastMap top) ≤ sectionIdeal top f P from
      fun q hq => show (lastMap top) q ∈ graphCurve f P from
        (RingHom.mem_ker.mp hq).symm ▸ (graphCurve f P).zero_mem) hz)
  rw [← hy, jetOf_monomialPoint]
private theorem jetOf_mem_closure {f : Row 3} {P : Ideal (GeoRow 3)} {z : (EmbeddedPoint top)}
    (hz : z ∈ zeroLocus GeometricX (sectionIdeal top f P)) :
    jetOfEmbedded top z ∈ zeroLocus GeometricX (graphCurve f P) := by
  apply (monomialPoint_mem_zeroLocus_comap_iff lastExponents_single _ _).mp
  rw [monomialPoint_jetOf hz]
  exact hz
private theorem retained {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    P ∈ (oldCutIdeal f).minimalPrimes ∧ genericRow (separant f) ∉ P :=
  Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
private theorem lift_mem_graphCurve_iff {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (g : GeoRow 3) :
    liftRow g ∈ graphCurve f P ↔ g ∈ P := by
  let : P.IsPrime := (retained hP).1.isPrime
  change g ∈ (graphCurve f P).comap (rename Fin.castSucc).toRingHom ↔ g ∈ P
  rw [graphCurve_comap (retained hP).2]
private theorem mem_graphLocus_of_mem_closure {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) {y : JetPoint}
    (hy : y ∈ zeroLocus GeometricX (graphCurve f P))
    (hs : eval y (liftRow (genericRow (separant f))) ≠ 0) :
    y ∈ graphLocus f P := by
  let x : Fin 3 → GeometricX := y ∘ Fin.castSucc
  have hs' : eval x (genericRow (separant f)) ≠ 0 := by
    simpa only [liftRow, eval_rename, x] using hs
  have hx : x ∈ regularLocus f P := by
    refine ⟨fun g hg => ?_, hs'⟩
    have h := hy (liftRow g) ((lift_mem_graphCurve_iff hP g).mpr hg)
    simpa only [aeval_eq_eval, liftRow, eval_rename, x] using h
  have hvan : graph f ∈ graphCurve f P := by
    rintro _ ⟨w, hw, rfl⟩
    exact eval_graph_graphPoint hw.2
  have h := hy (graph f) hvan
  simp only [aeval_eq_eval, graph, map_add, map_mul, map_ofNat, eval_X, liftRow,
    eval_rename] at h
  change eval x (genericRow (lowerTangent f)) +
    3 * y 3 * eval x (genericRow (separant f)) = 0 at h
  refine ⟨x, hx, ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j => Fin.snoc_castSucc _ _ j) i
  rw [graphPoint, Fin.snoc_last, div_eq_iff (mul_ne_zero K1_13_5_4_2.three_ne_zero hs')]
  change -eval x (genericRow (lowerTangent f)) =
    y 3 * (3 * eval x (genericRow (separant f)))
  linear_combination -h
private theorem finite_cut {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : IsSectionCurve top f P) {g : GeoRow 4} (hg : g ∉ graphCurve f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal top f P) ∧
      eval (jetOfEmbedded top z) g = 0}.Finite := by
  obtain ⟨G, hG⟩ := monomialMap_surjective lastExponents_single g
  have hnot : G ∉ sectionIdeal top f P := by
    change (lastMap top) G ∉ graphCurve f P
    rwa [hG]
  obtain ⟨hdim, _⟩ :=
    principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hP.1 hnot (b := G.totalDegree) le_rfl
  rw [hP.2] at hdim
  have hn := Nat.eq_zero_of_le_zero hdim
  refine ((finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) _ hn).1).subset ?_
  intro z hz
  apply mem_zeroLocus_sup_span_singleton_iff.mpr
  refine ⟨hz.1, ?_⟩
  rw [← monomialPoint_jetOf hz.1, aeval_monomialPoint, hG, aeval_eq_eval]
  exact hz.2
private theorem finite_boundary {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hC : IsSectionCurve top f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal top f P) ∧
      jetOfEmbedded top z ∉ graphLocus f P}.Finite := by
  have hsep : liftRow (genericRow (separant f)) ∉ graphCurve f P :=
    fun h => (retained hP).2 ((lift_mem_graphCurve_iff hP _).mp h)
  refine (finite_cut hC hsep).subset ?_
  intro z hz
  exact ⟨hz.1, not_ne_iff.mp fun hs =>
    hz.2 (mem_graphLocus_of_mem_closure hP (jetOf_mem_closure hz.1) hs)⟩
private theorem finite_overlap {f : Row 3} {P Q : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hQ : Q ∈ factorCurves f) (hne : P ≠ Q)
    (hC : IsSectionCurve top f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal top f P) ∧
      jetOfEmbedded top z ∈ graphLocus f Q}.Finite := by
  have h : ¬ Q ≤ P := Ideal.not_le_of_mem_minimalPrimes (retained hQ).1 (retained hP).1 hne.symm
  obtain ⟨g, hgQ, hgP⟩ : ∃ g, g ∈ Q ∧ g ∉ P := by
    by_contra! hbad
    exact h hbad
  refine (finite_cut hC (fun hg => hgP ((lift_mem_graphCurve_iff hP _).mp hg))).subset ?_
  intro z hz
  refine ⟨hz.1, ?_⟩
  obtain ⟨x, hx, he⟩ := hz.2
  rw [← he, eval_liftRow_graphPoint]
  exact hx.1 g hgQ
theorem exists_excluded_points {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hC : IsSectionCurve top f P) :
    ∃ B : Finset (EmbeddedPoint top),
      ∀ z ∈ zeroLocus GeometricX (sectionIdeal top f P), z ∉ B →
        jetOfEmbedded top z ∈ graphLocus f P ∧
        ∀ Q ∈ factorCurves f, P ≠ Q → jetOfEmbedded top z ∉ graphLocus f Q := by
  classical
  let boundary := (finite_boundary hP hC).toFinset
  let overlap (Q : (factorCurves f).erase P) :=
    (finite_overlap hP (Finset.mem_of_mem_erase Q.property)
      (Finset.ne_of_mem_erase Q.property).symm hC).toFinset
  refine ⟨boundary ∪ Finset.univ.biUnion overlap, ?_⟩
  intro z hz hB
  constructor
  · by_contra hn
    apply hB
    exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr ⟨hz, hn⟩)
  · intro Q hQ hne hmeet
    let q : (factorCurves f).erase P := ⟨Q, Finset.mem_erase.mpr ⟨hne.symm, hQ⟩⟩
    apply hB
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_univ _, (Set.Finite.mem_toFinset _).mpr ⟨hz, hmeet⟩⟩)
end
end ScalarRefined_1_1_1
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1_1
noncomputable section
variable {top : Fin 3}
open K1_13_5_4 (GeoRow GeometricX InLiftedBox)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve)
open K1_13_5_4_2_2 (linearForm fiberIdeal totalDegree_hyperplane_le_one zeroLocus_fiber_iff
  ncard_eq_affineDegree_of_radical)
open ScalarRefined (taylorLength)
open ScalarRefined_1_1 (factorCurves lastBox lastExponents lastMap sectionIdeal sectionDegree)
open MvPolynomial
open scoped Pointwise
private theorem hyperplane_support (a : (EmbeddedPoint top)) (t : GeometricX) :
    InLiftedBox ((lastMap top) (linearForm a - MvPolynomial.C t)) (lastBox top) taylorLength := by
  have hz : (0 : Fin 4 →₀ ℕ) ∈ (lastExponents top) := by
    change 0 + 0 + 0 ≤ (lastBox top).b ∧ 0 + 2 * 0 ≤ (lastBox top).j ∧ 0 ≤ (lastBox top).t ∧ 0 ≤ taylorLength
    simp
  have h := monomialMap_mem_restrictSupport_nsmul hz (totalDegree_hyperplane_le_one a t)
  rw [one_nsmul] at h
  exact h
theorem proof : ScalarRefined_1_1.c1 top := by
  classical
  intro f hC
  have h1 := K1_13_5_4_2_2_1.proof
  have h2 := K1_13_5_4_2_2_2.proof
  have h3 := K1_13_5_4_2_2_3.proof
  let I (P : factorCurves f) := sectionIdeal top f P.val
  obtain ⟨degreeBad, hdegreeBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h1 GeometricX (lastExponents top) (I P) (hC P.val P.property).1 (hC P.val P.property).2
  obtain ⟨separationBad, hseparationBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h2 GeometricX (lastExponents top) (I P) (hC P.val P.property).1 (hC P.val P.property).2
  let bad := Finset.univ.biUnion fun P => insert (separationBad P) (degreeBad P)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun V : bad => V.val) (by
      intro V
      obtain ⟨P, _, hV⟩ := Finset.mem_biUnion.mp V.property
      rcases Finset.mem_insert.mp hV with h | h
      · rw [h]
        exact (hseparationBad P).1
      · exact (hdegreeBad P).1 _ h)
  have havoid (P : factorCurves f) (V : Submodule GeometricX (EmbeddedPoint top))
      (hV : V ∈ insert (separationBad P) (degreeBad P)) : a ∉ V :=
    ha ⟨V, Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _, hV⟩⟩
  have hdegree (P : factorCurves f) :=
    (hdegreeBad P).2 a (fun V hV => havoid P V (Finset.mem_insert_of_mem hV))
  obtain ⟨valueBad, hvalueBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h3 GeometricX (lastExponents top) (I P) (hC P.val P.property).1 a (hdegree P).1
      ((hseparationBad P).2 a (havoid P _ (Finset.mem_insert_self _ _)))
  obtain ⟨pointsBad, hpointsBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    exists_excluded_points P.property (hC P.val P.property)
  let value (z : (EmbeddedPoint top)) := aeval z (linearForm a)
  let excludedValues := Finset.univ.biUnion fun P => valueBad P ∪ (pointsBad P).image value
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset excludedValues
  have hmiss (P : factorCurves f) : t ∉ valueBad P ∪ (pointsBad P).image value :=
    fun h => ht (Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _, h⟩)
  let L := linearForm a - MvPolynomial.C t
  let J (P : Ideal (GeoRow 3)) := fiberIdeal (sectionIdeal top f P) a t
  have hcut (P) (hP : P ∈ factorCurves f) :
      (affineHilbertPolynomial (J P)).natDegree = 0 ∧
        affineDegree (J P) = sectionDegree top f P :=
    (hdegree ⟨P, hP⟩).2 t
  have hproper (P) (hP : P ∈ factorCurves f) : (lastMap top) L ∉ graphCurve f P := by
    intro hmem
    have hL : L ∈ sectionIdeal top f P := hmem
    have heq : J P = sectionIdeal top f P :=
      sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hL)
    have hz := (hcut P hP).1
    rw [heq, (hC P hP).2] at hz
    omega
  have hfinite (P) (hP : P ∈ factorCurves f) : (zeroLocus GeometricX (J P)).Finite :=
    (finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) _ (hcut P hP).1).1
  let points (P : Ideal (GeoRow 3)) : Finset JetPoint :=
    if hP : P ∈ factorCurves f then (hfinite P hP).toFinset.image (jetOfEmbedded top) else ∅
  have hg (P) (hP : P ∈ factorCurves f) {z : (EmbeddedPoint top)}
      (hz : z ∈ zeroLocus GeometricX (J P)) :
      jetOfEmbedded top z ∈ graphLocus f P ∧
      (∀ Q ∈ factorCurves f, P ≠ Q → jetOfEmbedded top z ∉ graphLocus f Q) := by
    obtain ⟨hzC, hzt⟩ := zeroLocus_fiber_iff.mp hz
    apply hpointsBad ⟨P, hP⟩ z hzC
    intro hbad
    exact hmiss ⟨P, hP⟩ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨z, hbad, hzt⟩))
  have hpoint (P) (hP : P ∈ factorCurves f) (y) (hy : y ∈ points P) :
      ∃ z ∈ zeroLocus GeometricX (J P), jetOfEmbedded top z = y := by
    simp only [points, dite_eq_left hP] at hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨z, (Set.Finite.mem_toFinset _).mp hz, rfl⟩
  refine ⟨⟨(lastMap top) L, hyperplane_support a t, points, ?_, hproper, ?_, ?_⟩⟩
  · intro P hP
    have hrad := hvalueBad ⟨P, hP⟩ t (fun ht' => hmiss ⟨P, hP⟩ (Finset.mem_union_left _ ht'))
    have hinj : Set.InjOn (jetOfEmbedded top) (zeroLocus GeometricX (J P)) := by
      intro x hx y hy hxy
      rw [← monomialPoint_jetOf (zeroLocus_fiber_iff.mp hx).1,
        ← monomialPoint_jetOf (zeroLocus_fiber_iff.mp hy).1, hxy]
    simp only [points, dite_eq_left hP]
    rw [Finset.card_image_of_injOn (by simpa using hinj),
      ← Set.ncard_eq_toFinset_card _ (hfinite P hP)]
    exact (ncard_eq_affineDegree_of_radical (J P) (hcut P hP).1 hrad).trans (hcut P hP).2
  · intro P hP y hy
    obtain ⟨z, hz, rfl⟩ := hpoint P hP y hy
    have hzC := (zeroLocus_fiber_iff.mp hz).1
    refine ⟨(hg P hP hz).1, ?_⟩
    have hev := (mem_zeroLocus_sup_span_singleton_iff.mp hz).2
    rw [← monomialPoint_jetOf hzC, aeval_monomialPoint, aeval_eq_eval] at hev
    exact hev
  · intro P hP Q hQ hne y hy
    obtain ⟨z, hz, rfl⟩ := hpoint P hP y hy
    exact (hg P hP hz).2 Q hQ hne
end
end ScalarRefined_1_1_1
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1_3
noncomputable section
variable {top : Fin 3}
open K1_13 (Shape)
open Scalar70LeadingLower_1_1_3 (volume_variation)
open ScalarRefined (lowBox graphBox liftedBox mixedCoefficients)
open K1_13_5_4_2 (ExponentSpace capBody mixedVolume4)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation
  volumeQuotient rest univ_eq_insert zero_notMem_rest)
open K1_13_5_4_2_5_2_1 (cap_polytope closedOrthant)
open ScalarRefined (taylorLength)
open ScalarRefined_1_1 (lastBox lastMixedVolume)
open MeasureTheory Filter MvPolynomial
open scoped BigOperators Pointwise Topology
open private K1_13_5_4_2_5.sumShape sumChamber sum_capBody capBody_zero from ProximityPrize.SubmissionLower.Fast048
open private labelHull_eq positivePolynomial from ProximityPrize.SubmissionLower.Fast071
open private weights polar_linear from ProximityPrize.SubmissionLower.Fast048
open private volume_zero_height from ProximityPrize.SubmissionLower.Fast048
def boxShape (top : Fin 3) : Fin 4 → Shape := ![lowBox, (graphBox top), liftedBox top (taylorLength + 1), (lastBox top)]
def boxHeight : Fin 4 → ℕ := ![0, 1, taylorLength - 1, taylorLength]
abbrev baseShape (top : Fin 3) (S : Finset (Fin 4)) : Shape := K1_13_5_4_2_5.sumShape S (boxShape top)
def baseHeight (S : Finset (Fin 4)) : ℕ := ∑ i ∈ S, boxHeight i
private def base (top : Fin 3) (S : Finset (Fin 4)) : Set ExponentSpace :=
  capBody (baseShape top S) (baseHeight S)
private def slots (top : Fin 3) (P : Set ExponentSpace) : Fin 4 → Set ExponentSpace :=
  Function.update (fun i => capBody ((boxShape top) i) (boxHeight i)) 0 P
private theorem mixed_eq (P : Set ExponentSpace) : lastMixedVolume top P = mixedVolume4 (slots top P) := by
  unfold lastMixedVolume
  congr 1
  funext i
  fin_cases i <;> rfl
theorem box_chamber (i : Fin 4) : Chamber ((boxShape top) i) := by
  fin_cases top <;> fin_cases i <;> exact ⟨by decide, by decide⟩
theorem base_chamber (S : Finset (Fin 4)) : Chamber (baseShape top S) :=
  sumChamber S (boxShape top) box_chamber
private theorem slots_nonempty (P : Set ExponentSpace) (hP : FirstBody P)
    (i : Fin 4) : 0 ∈ slots top P i := by
  by_cases hi : i = 0
  · simpa [slots, hi] using hP.zero_mem
  · simp [slots, Function.update_of_ne hi, capBody]
private theorem volume_polynomial (P : Set ExponentSpace) (hP : FirstBody P) :
    ∃ p : MvPolynomial (Fin 4) ℝ, p.IsHomogeneous 4 ∧
      ∀ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) →
        p.eval w = (volume (∑ i, w i • slots top P i)).toReal := by
  classical
  have hslot (i : Fin 4) :
      ∃ v : Finset ExponentSpace, slots top P i = convexHull ℝ (v : Set ExponentSpace) := by
    by_cases hi : i = 0
    · subst i
      obtain ⟨s, hs, hr⟩ := hP.polytope
      exact ⟨hs.toFinset, by simpa [slots] using hr⟩
    · rw [slots, Function.update_of_ne hi]
      exact cap_polytope _ _ (box_chamber i)
  choose v hv using hslot
  obtain ⟨p, hp, he⟩ := positivePolynomial K1_13_5_4_2_5_2_1_1.proof
    K1_13_5_4_2_5_2_1_2.proof (slots top P) v hv
  refine ⟨p, hp, closedOrthant (slots top P) ?_ (slots_nonempty P hP) ?_ p he⟩
  · intro i
    rw [hv i]
    exact convex_convexHull _ _
  · intro w
    rw [← labelHull_eq (slots top P) v hv w]
    exact (Set.finite_range _).isCompact_convexHull ℝ
private theorem polar_slots (P : Set ExponentSpace) (hP : FirstBody P)
    (t : ℝ) (S : Finset (Fin 4)) :
    (∑ i, weights t S i • slots top P i) = ∑ i ∈ S, slots top (t • P) i := by
  calc
    _ = ∑ i ∈ S, (![t, 1, 1, 1] : Fin 4 → ℝ) i • slots top P i := by
      rw [← Finset.sum_subset (s₁ := S) (s₂ := Finset.univ) (Finset.subset_univ S)
        (f := fun i => weights t S i • slots top P i)]
      · exact Finset.sum_congr rfl (fun i hi => by simp [weights, hi])
      · intro i _ hi
        simp [weights, hi, Set.zero_smul_set (Set.nonempty_of_mem (slots_nonempty P hP i))]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      fin_cases i <;> simp [slots]
private theorem mixed_scale (P : Set ExponentSpace) (hP : FirstBody P) (t : ℝ) (ht : 0 ≤ t) :
    lastMixedVolume top (t • P) = t * lastMixedVolume top P := by
  obtain ⟨p, hp, heval⟩ := volume_polynomial P hP
  have hw (s : ℝ) (hs : 0 ≤ s) (S : Finset (Fin 4)) (i : Fin 4) :
      0 ≤ weights s S i := by
    unfold weights
    apply ite_nonneg _ (le_refl (0 : ℝ))
    fin_cases i
    · exact hs
    all_goals exact zero_le_one
  have hpol (s : ℝ) (hs : 0 ≤ s) (S : Finset (Fin 4)) :
      p.eval (weights s S) = (volume (∑ i ∈ S, slots top (s • P) i)).toReal := by
    rw [heval _ (hw s hs S), polar_slots P hP]
  simpa only [mixed_eq, mixedVolume4, hpol _ ht, hpol 1 zero_le_one, one_smul]
    using polar_linear p hp t
private theorem sum_slots (P : Set ExponentSpace) {S : Finset (Fin 4)} (h0 : 0 ∉ S) :
    (∑ i ∈ S, slots top P i) = base top S := by
  change _ = capBody (K1_13_5_4_2_5.sumShape S (boxShape top)) (∑ i ∈ S, boxHeight i)
  rw [← sum_capBody _ _ _ box_chamber]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ 0 := fun h => h0 (h ▸ hi)
  simp [slots, Function.update_of_ne hne]
private theorem mixed_increment (P : Set ExponentSpace) (t : ℝ) :
    lastMixedVolume top (t • P) =
      ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        ((volume (t • P + base top S)).toReal - (volume (base top S)).toReal) := by
  rw [mixed_eq, mixedVolume4, univ_eq_insert,
    Finset.sum_powerset_insert zero_notMem_rest, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  have h0 : (0 : Fin 4) ∉ S := fun h => zero_notMem_rest (hsub h)
  have hs : S.card ≤ 3 :=
    (Finset.card_le_card hsub).trans (show rest.card ≤ 3 by decide)
  rw [Finset.sum_insert h0, Finset.card_insert_of_notMem h0,
    sum_slots _ h0, show slots top (t • P) 0 = t • P by simp [slots]]
  have e₁ : 4 - S.card = (3 - S.card) + 1 := by omega
  have e₂ : 4 - (S.card + 1) = 3 - S.card := by omega
  rw [e₁, e₂, pow_succ]
  ring
private theorem empty_quotient (P : Set ExponentSpace) (hP : FirstBody P) (t : ℝ) :
    volumeQuotient P (base top ∅) t = 0 := by
  have hbase : base top ∅ = 0 := by simp [base, K1_13_5_4_2_5.sumShape, baseHeight, capBody_zero]
  have hPz : volume (t • P) = 0 := by
    apply volume_zero_height
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    simp [Pi.smul_apply, hP.zero_height y hy]
  rw [volumeQuotient, hbase, add_zero, hPz,
    show (0 : Set ExponentSpace) = {0} by rfl]
  simp
private theorem tendsto_quotient (P : Set ExponentSpace)
    (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) {S : Finset (Fin 4)} (hS : S ⊆ rest) :
    Tendsto (volumeQuotient P (base top S)) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (capFirstVariation (baseShape top S) (baseHeight S)
        (totalSupport P) (indexSupport P) (topSupport P))) := by
  by_cases he : S = ∅
  · subst S
    rw [show volumeQuotient P (base top ∅) = (fun _ : ℝ => 0) from funext (empty_quotient P hP)]
    simp [capFirstVariation, K1_13_5_4_2_5.sumShape, baseHeight]
  · have hn := Finset.nonempty_iff_ne_empty.mpr he
    apply volume_variation P hP hsub _ _ (base_chamber S)
    · exact Finset.sum_lt_sum_of_nonempty hn (fun i _ => by fin_cases top <;> fin_cases i <;> decide)
    · exact Finset.sum_pos (fun i _ => by fin_cases top <;> fin_cases i <;> decide) hn
theorem variation_eq (P : Set ExponentSpace) (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) :
    lastMixedVolume top P =
      ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        capFirstVariation (baseShape top S) (baseHeight S)
          (totalSupport P) (indexSupport P) (topSupport P) := by
  have hlim := tendsto_finsetSum rest.powerset (fun S hS =>
    (tendsto_quotient (top := top) P hP hsub (Finset.mem_powerset.mp hS)).const_mul
      ((-1 : ℝ) ^ (3 - S.card)))
  have heq : (fun _ : ℝ => lastMixedVolume top P) =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun t : ℝ => ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        volumeQuotient P (base top S) t) := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht
    have ht' : 0 < t := ht
    have hquot : lastMixedVolume top (t • P) / t = lastMixedVolume top P := by
      rw [mixed_scale P hP t ht'.le]
      exact mul_div_cancel_left₀ _ ht'.ne'
    calc
      lastMixedVolume top P = lastMixedVolume top (t • P) / t := hquot.symm
      _ = _ := by simp only [mixed_increment, Finset.sum_div, volumeQuotient, mul_div_assoc]
  exact tendsto_const_nhds_iff.mp (hlim.congr' heq.symm)
end
end ScalarRefined_1_1_3
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1_3
noncomputable section
variable {top : Fin 3}
open K1_13 (Shape)
open ScalarRefined (lowBox liftedBox mixedCoefficients)
open K1_13_5_4_2 (ExponentSpace capBody)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation rest)
open ScalarRefined (mixedBudget)
open ScalarRefined_1_1 (lastMixedVolume)
open scoped BigOperators

private def coefficients (s : Shape) (h : ℕ) : ℕ × ℕ × ℕ :=
  (2 * h * s.t * (s.j - s.t),
    h * s.t * (2 * (s.b - s.j) + s.t),
    h * (s.j - 2 * s.t) * (2 * s.b - s.j))
private theorem twice_variation (s : Shape) (h : ℕ) (hs : Chamber s) (B J T : ℝ) :
    2 * capFirstVariation s h B J T =
      (coefficients s h).1 * B + (coefficients s h).2.1 * J + (coefficients s h).2.2 * T := by
  have hB : s.j ≤ s.b := hs.1
  have hJ : 2 * s.t ≤ s.j := hs.2
  have ht : s.t ≤ s.j := by omega
  have hb : s.j ≤ 2 * s.b := by omega
  simp only [capFirstVariation, coefficients, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_sub hB, Nat.cast_sub hJ, Nat.cast_sub ht, Nat.cast_sub hb]
  ring
private def row (top : Fin 3) (S : Finset (Fin 4)) : ℕ × ℕ × ℕ :=
  coefficients (baseShape top S) (baseHeight S)
private theorem alternating_three (F : Finset (Fin 4) → ℝ) :
    (∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) * F S) =
      F (insert 1 (insert 2 (insert 3 ∅))) -
        F (insert 1 (insert 2 ∅)) - F (insert 1 (insert 3 ∅)) - F (insert 2 (insert 3 ∅)) +
        F (insert 1 ∅) + F (insert 2 ∅) + F (insert 3 ∅) - F ∅ := by
  unfold rest
  simp only [
    Finset.sum_powerset_insert (a := (1 : Fin 4)) (s := insert 2 (insert 3 ∅)) (by decide),
    Finset.sum_powerset_insert (a := (2 : Fin 4)) (s := insert 3 ∅) (by decide),
    Finset.sum_powerset_insert (a := (3 : Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem, Finset.mem_insert]
  ring
private theorem twice_row (S : Finset (Fin 4)) (B J T : ℝ) :
    2 * capFirstVariation (baseShape top S) (baseHeight S) B J T =
      (row top S).1 * B + (row top S).2.1 * J + (row top S).2.2 * T :=
  twice_variation _ _ (base_chamber S) _ _ _
private def alternate {A : Type*} [AddGroup A] (F : Finset (Fin 4) → A) : A :=
  F (insert 1 (insert 2 (insert 3 ∅))) -
    F (insert 1 (insert 2 ∅)) - F (insert 1 (insert 3 ∅)) - F (insert 2 (insert 3 ∅)) +
    F (insert 1 ∅) + F (insert 2 ∅) + F (insert 3 ∅) - F ∅

private def coordinate (x : ℕ × ℕ × ℕ) : Fin 3 → ℕ := ![x.1, x.2.1, x.2.2]

private theorem mixed_receipt (top : Fin 3) (i : Fin 3) :
    alternate (fun S => (coordinate (row top S) i : ℤ)) =
      2 * (coordinate (mixedCoefficients top) i : ℤ) := by
  fin_cases top <;> fin_cases i <;> decide

theorem mixed_formula (P : Set ExponentSpace) (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) :
    lastMixedVolume top P = (mixedCoefficients top).1 * totalSupport P +
      (mixedCoefficients top).2.1 * indexSupport P + (mixedCoefficients top).2.2 * topSupport P := by
  rw [variation_eq P hP hsub]
  apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
  generalize totalSupport P = B
  generalize indexSupport P = J
  generalize topSupport P = T
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (2 : ℝ), twice_row]
  rw [alternating_three]
  have hc (i : Fin 3) :
      alternate (fun S => (coordinate (row top S) i : ℝ)) =
        2 * (coordinate (mixedCoefficients top) i : ℝ) := by
    unfold alternate
    have h := mixed_receipt top i
    unfold alternate at h
    have hr := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at hr
    exact hr
  have hB := hc 0
  have hJ := hc 1
  have hT := hc 2
  change alternate (fun S => ((row top S).1 : ℝ)) = 2 * ((mixedCoefficients top).1 : ℝ) at hB
  change alternate (fun S => ((row top S).2.1 : ℝ)) = 2 * ((mixedCoefficients top).2.1 : ℝ) at hJ
  change alternate (fun S => ((row top S).2.2 : ℝ)) = 2 * ((mixedCoefficients top).2.2 : ℝ) at hT
  unfold alternate at hB hJ hT
  linear_combination B * hB + J * hJ + T * hT
theorem price_eq (top : Fin 3) :
    (mixedCoefficients top).1 * (ScalarRefined.lowerWidth top : ℝ) +
    (mixedCoefficients top).2.1 * (ScalarRefined.lowerIndex top : ℝ) +
    (mixedCoefficients top).2.2 * (ScalarRefined.lowerTop top : ℝ) =
      (mixedBudget top : ℝ) := by
  unfold mixedBudget
  rcases h : mixedCoefficients top with ⟨b, j, r⟩
  simp only [Nat.cast_add, Nat.cast_mul]

end
end ScalarRefined_1_1_3
end
section
set_option autoImplicit false
namespace ScalarRefined_1_1_3
noncomputable section
variable {top : Fin 3}
open K1_13 (Row indexDegree)
open ScalarRefined (lowBox liftedBox mixedCoefficients)
open K1_13_5_4 (genericRow liftRow)
open K1_13_5_4_2 (ExponentSpace downBody capBody)
open K1_13_5_4_2_5 (FirstBody firstBody_zero firstBody_row)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport)
open ScalarRefined (SecondFactors mixedBudget)
open ScalarRefined_1_1 (lastMixedVolume)
open MvPolynomial
open scoped BigOperators Pointwise
open private rowShape row_support downBody_subset from ProximityPrize.SubmissionLower.Fast048
private theorem sum_downBody_subset {n : ℕ} (f : Fin n → Row 3)
    (S : Finset (Fin n)) (a : K1_13.Shape)
    (ht : (∑ i, (f i).totalDegree) ≤ a.b)
    (hj : (∑ i, indexDegree (f i)) ≤ a.j)
    (htop : (∑ i, (f i).degreeOf 2) ≤ a.t) :
    (∑ i ∈ S, downBody (liftRow (genericRow (f i)))) ⊆ capBody a 0 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Set.mem_finsetSum S _ x).mp hx
  have hb (i : Fin n) (hi : i ∈ S) : y i ∈ capBody (rowShape (f i)) 0 :=
    downBody_subset (row_support (f i)) (hy hi)
  have cap (degree : Fin n → ℕ) (b : ℕ) (h : (∑ i, degree i) ≤ b) :
      (∑ i ∈ S, (degree i : ℝ)) ≤ b := by
    rw [← Nat.cast_sum, Nat.cast_le]
    exact (Finset.sum_le_sum_of_subset (Finset.subset_univ S)).trans h
  simp only [capBody, Set.mem_ofPred_eq, Finset.sum_apply]
  refine ⟨fun j => Finset.sum_nonneg (fun i hi => (hb i hi).1 j), ?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.1)).trans (cap _ _ ht)
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.2.1)).trans (cap _ _ hj)
  · exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.2.2.1)).trans (cap _ _ htop)
  · rw [Nat.cast_zero]
    exact Finset.sum_nonpos (fun i hi => by simpa using (hb i hi).2.2.2.2)
private theorem support_add {P Q : Set ExponentSpace} (hP : FirstBody P) (hQ : FirstBody Q)
    (L : ExponentSpace → ℝ) (hL : Continuous L) (ha : ∀ x y, L (x + y) = L x + L y) :
    sSup (L '' (P + Q)) = sSup (L '' P) + sSup (L '' Q) := by
  let ℓ := AddMonoidHom.mk' L ha
  change sSup (ℓ '' (P + Q)) = _
  have bounded {U : Set ExponentSpace} (hU : FirstBody U) : BddAbove (L '' U) := by
    obtain ⟨v, hv, rfl⟩ := hU.polytope
    exact (hv.isCompact_convexHull ℝ).bddAbove_image hL.continuousOn
  rw [Set.image_add ℓ]
  exact csSup_add ((Set.nonempty_of_mem hP.zero_mem).image L) (bounded hP)
    ((Set.nonempty_of_mem hQ.zero_mem).image L) (bounded hQ)
private theorem sum_mixed {ι : Type} (P : ι → Set ExponentSpace) (hP : ∀ i, FirstBody (P i))
    (hsub : ∀ S : Finset ι, (∑ i ∈ S, P i) ⊆ capBody lowBox 0) (S : Finset ι) :
    FirstBody (∑ i ∈ S, P i) ∧
      (∑ i ∈ S, lastMixedVolume top (P i)) = lastMixedVolume top (∑ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨firstBody_zero, ?_⟩
    have hz : (0 : Set ExponentSpace) ⊆ capBody lowBox 0 := by simpa using hsub ∅
    rw [mixed_formula _ firstBody_zero hz]
    simp [totalSupport, indexSupport, topSupport, show (0 : Set ExponentSpace) = {0} from rfl]
  | @insert i S hi ih =>
    let Q := ∑ j ∈ S, P j
    have hPi : P i ⊆ capBody lowBox 0 := by simpa using hsub {i}
    have hPQ : P i + Q ⊆ capBody lowBox 0 := by simpa only [Q, Finset.sum_insert hi] using hsub (insert i S)
    have hbody := (hP i).add ih.1
    simp only [Finset.sum_insert hi, ih.2]
    refine ⟨hbody, ?_⟩
    rw [mixed_formula (P i) (hP i) hPi, mixed_formula Q ih.1 (hsub S), mixed_formula _ hbody hPQ]
    have hB : totalSupport (P i + Q) = totalSupport (P i) + totalSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun x y => by simp only [Pi.add_apply]; ring)
    have hJ : indexSupport (P i + Q) = indexSupport (P i) + indexSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun x y => by simp only [Pi.add_apply]; ring)
    have hT : topSupport (P i + Q) = topSupport (P i) + topSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun _ _ => rfl)
    rw [hB, hJ, hT]
    ring
private theorem support_bound (P : Set ExponentSpace) (hP : FirstBody P)
    (L : ExponentSpace → ℝ) {x : ℝ} (hx : ∀ p ∈ P, L p ≤ x) :
    sSup (L '' P) ≤ x :=
  csSup_le ((Set.nonempty_of_mem hP.zero_mem).image L) (by rintro _ ⟨p, hp, rfl⟩; exact hx p hp)
theorem proof : ScalarRefined_1_1.c3 top := by
  intro n f hf
  let P (i : Fin n) := downBody (liftRow (genericRow (f i)))
  have hP (i : Fin n) : FirstBody (P i) := firstBody_row (hf.irreducible i).ne_zero
  have hB₀ : (∑ i, (f i).totalDegree) ≤ lowBox.b := hf.total.trans (by fin_cases top <;> decide)
  have hJ₀ : (∑ i, indexDegree (f i)) ≤ lowBox.j := hf.index.trans (by fin_cases top <;> decide)
  have hT₀ : (∑ i, (f i).degreeOf 2) ≤ lowBox.t := hf.coordinate.trans (by fin_cases top <;> decide)
  have hs (S : Finset (Fin n)) : (∑ i ∈ S, P i) ⊆ capBody lowBox 0 := sum_downBody_subset f S lowBox hB₀ hJ₀ hT₀
  obtain ⟨hbody, hsum⟩ := sum_mixed (top := top) P hP hs Finset.univ
  change (∑ i, lastMixedVolume top (P i)) ≤ (mixedBudget top : ℝ)
  rw [hsum, mixed_formula _ hbody (hs _), ← price_eq]
  let bounds : K1_13.Shape :=
    ⟨ScalarRefined.lowerWidth top, ScalarRefined.lowerIndex top, ScalarRefined.lowerTop top⟩
  have hsT : (∑ i, P i) ⊆ capBody bounds 0 :=
    sum_downBody_subset f _ bounds hf.total hf.index hf.coordinate
  have hB : totalSupport (∑ i, P i) ≤ (bounds.b : ℝ) :=
    support_bound _ hbody _ (fun _ hx => (hsT hx).2.1)
  have hJ : indexSupport (∑ i, P i) ≤ (bounds.j : ℝ) :=
    support_bound _ hbody _ (fun _ hx => (hsT hx).2.2.1)
  have hT : topSupport (∑ i, P i) ≤ (bounds.t : ℝ) :=
    support_bound _ hbody _ (fun _ hx => (hsT hx).2.2.2.1)
  dsimp only [bounds] at hB hJ hT
  gcongr
end
end ScalarRefined_1_1_3
end

section
namespace ScalarRefined_1_1_2
noncomputable section
open ScalarRefined (graphBox liftedBox taylorLength)
open ScalarRefined_1 (LiftedChart)
open K1_13 (Row)
open private box_mono from ProximityPrize.SubmissionLower.Fast048

/-- Use the existing local multiplicity result after enlarging the support bounds.
The underlying polynomials and all evaluation maps are identical. -/
private def relaxed {top : Fin 3} {f : Row 3} (T : LiftedChart top f) :
    Scalar70LeadingLower_1.LiftedChart 0 f where
  cut := T.cut
  next := T.next
  numerator := T.numerator
  graph_box := box_mono
    (show (graphBox top).b ≤ (Scalar70LeadingLower.graphBox 0).b by fin_cases top <;> decide)
    (show (graphBox top).j ≤ (Scalar70LeadingLower.graphBox 0).j by fin_cases top <;> decide)
    (show (graphBox top).t ≤ (Scalar70LeadingLower.graphBox 0).t by fin_cases top <;> decide)
    le_rfl T.graph_box
  cut_box := box_mono
    (show (liftedBox top (taylorLength+1)).b ≤ (Scalar70LeadingLower.liftedBox 0 (taylorLength+1)).b by fin_cases top <;> decide)
    (show (liftedBox top (taylorLength+1)).j ≤ (Scalar70LeadingLower.liftedBox 0 (taylorLength+1)).j by fin_cases top <;> decide)
    (show (liftedBox top (taylorLength+1)).t ≤ (Scalar70LeadingLower.liftedBox 0 (taylorLength+1)).t by fin_cases top <;> decide)
    le_rfl T.cut_box
  next_box := box_mono
    (show (liftedBox top (taylorLength+2)).b ≤ (Scalar70LeadingLower.liftedBox 0 (taylorLength+2)).b by fin_cases top <;> decide)
    (show (liftedBox top (taylorLength+2)).j ≤ (Scalar70LeadingLower.liftedBox 0 (taylorLength+2)).j by fin_cases top <;> decide)
    (show (liftedBox top (taylorLength+2)).t ≤ (Scalar70LeadingLower.liftedBox 0 (taylorLength+2)).t by fin_cases top <;> decide)
    le_rfl T.next_box
  coefficient_box i := box_mono
    (show (liftedBox top taylorLength).b ≤ (Scalar70LeadingLower.liftedBox 0 taylorLength).b by fin_cases top <;> decide)
    (show (liftedBox top taylorLength).j ≤ (Scalar70LeadingLower.liftedBox 0 taylorLength).j by fin_cases top <;> decide)
    (show (liftedBox top taylorLength).t ≤ (Scalar70LeadingLower.liftedBox 0 taylorLength).t by fin_cases top <;> decide)
    le_rfl (T.coefficient_box i)
  cut_represents := T.cut_represents
  next_represents := T.next_represents
  actual := T.actual

theorem proof {top : Fin 3} : ScalarRefined_1_1.c2 top := by
  intro f hf hpos T L hL P hP y hy hyL
  exact Scalar70LeadingLower_1_1_2.proof (top := 0) f hf hpos (relaxed T) L hL P hP y hy hyL
end
end ScalarRefined_1_1_2
end

namespace ScalarRefined
open ScalarRefined_1 (LiftedChart MixedSections lifted_chart)
open K1_13 (Row)

theorem mixed_sections (top : Fin 3) (n : ℕ) (f : Fin n → Row 3) (hf : SecondFactors top f)
    (T : ∀ i, LiftedChart top (f i)) : Nonempty (MixedSections top f T) :=
  ScalarRefined_1_1.of_children ScalarRefined_1_1_1.proof
    ScalarRefined_1_1_2.proof ScalarRefined_1_1_3.proof n f hf T

#print axioms mixed_sections
end ScalarRefined
