import ProximityPrize.SubmissionLower.Fast004
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast054
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast022
import ProximityPrize.SubmissionLower.Fast060
import ProximityPrize.SubmissionLower.Numeric5Certificate
import ProximityPrize.SubmissionLower.Fast049
import ProximityPrize.SubmissionLower.Fast061
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast066
import ProximityPrize.SubmissionLower.Fast019
import ProximityPrize.SubmissionLower.Fast020
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast065
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Fast032
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2_4Split
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast059
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.Fast064
import ProximityPrize.SubmissionLower.Fast067
set_option Elab.async false

section PackSource_K1_13_7_1_2Geometry
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2

noncomputable section

open K1_13 K1_13_6 K1_13_7_1 MvPolynomial
open scoped BigOperators

theorem project_chartPoint (C : TaylorChart) (y : GeoPoint)
    (hy : eval y C.denom ≠ 0) : project (chartPoint C y) = y := by
  funext i
  change eval y (C.numerator (initialIndex i)) / eval y C.denom = y i
  rw [show C.numerator (initialIndex i) = MvPolynomial.X i * C.denom from C.initial i,
    map_mul, eval_X, mul_div_cancel_right₀ _ hy]

private theorem eval_rename_initial (z : TaylorPoint) (q : GeoJets) :
    eval z (rename initialIndex q) = eval (project z) q :=
  eval_rename initialIndex z q

theorem eval_imageDenom (C : TaylorChart) (z : TaylorPoint) :
    eval z (imageDenom C) = eval (project z) C.denom :=
  eval_rename_initial z C.denom

theorem chartPoint_mem_image {C : TaylorChart} {P : Ideal GeoJets} {y : GeoPoint}
    (hy : y ∈ zeroLocus GeoField P) (hD : eval y C.denom ≠ 0) :
    chartPoint C y ∈ zeroLocus GeoField (imageIdeal C P) :=
  zeroLocus_vanishingIdeal_le _ ⟨y, ⟨hy, hD⟩, rfl⟩

theorem project_mem_source {C : TaylorChart} {P : Ideal GeoJets} {z : TaylorPoint}
    (hz : z ∈ zeroLocus GeoField (imageIdeal C P)) : project z ∈ zeroLocus GeoField P := by
  intro q hq
  have hmem : rename initialIndex q ∈ imageIdeal C P := by
    rintro _ ⟨y, ⟨hy, hD⟩, rfl⟩
    simpa only [aeval_eq_eval, eval_rename_initial, project_chartPoint C y hD] using hy q hq
  simpa only [aeval_eq_eval, eval_rename_initial] using hz _ hmem

theorem chartPoint_project {C : TaylorChart} {P : Ideal GeoJets} {z : TaylorPoint}
    (hz : z ∈ zeroLocus GeoField (imageIdeal C P)) (hD : eval z (imageDenom C) ≠ 0) :
    chartPoint C (project z) = z := by
  funext i
  let q := rename initialIndex (C.numerator i) - MvPolynomial.X i * imageDenom C
  have hmem : q ∈ imageIdeal C P := by
    rintro _ ⟨y, ⟨_, hy⟩, rfl⟩
    simp only [q, aeval_eq_eval, map_sub, map_mul, eval_rename_initial, eval_X,
      eval_imageDenom, project_chartPoint C y hy, sub_eq_zero, chartPoint]
    exact (div_mul_cancel₀ _ hy).symm
  apply (div_eq_iff (by rwa [← eval_imageDenom])).mpr
  simpa only [q, aeval_eq_eval, map_sub, map_mul, eval_rename_initial, eval_X,
    eval_imageDenom, sub_eq_zero] using hz _ hmem

theorem imageDenom_notMem {C : TaylorChart} {P : Ideal GeoJets}
    (hp : P.IsPrime) (hP : C.denom ∉ P) : imageDenom C ∉ imageIdeal C P := by
  let _ := hp
  intro hm
  apply hP
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := GeoField) P]
  intro y hy
  by_contra hD
  have hz := chartPoint_mem_image (C := C) hy (by simpa only [aeval_eq_eval] using hD)
  apply hD
  simpa only [aeval_eq_eval, eval_imageDenom, project_chartPoint C y
    (by simpa only [aeval_eq_eval] using hD)] using hz _ hm

theorem eval_formPolynomial (a : AffineForm) (z : TaylorPoint) :
    eval z (formPolynomial a) = a.1 + ∑ i, a.2 i * z i := by
  simp [formPolynomial]

theorem eval_pullback (C : TaylorChart) (a : AffineForm) (y : GeoPoint)
    (hy : eval y C.denom ≠ 0) :
    eval y (C.pullback a) = eval y C.denom * eval (chartPoint C y) (formPolynomial a) := by
  rw [eval_formPolynomial]
  simp only [TaylorChart.pullback, map_add, map_mul, eval_C, map_sum, mul_add, Finset.mul_sum]
  rw [mul_comm a.1]
  apply congrArg (fun t : GeoField => eval y C.denom * a.1 + t)
  apply Finset.sum_congr rfl
  intro i _
  rw [chartPoint, ← mul_assoc, mul_comm (eval y C.denom), mul_assoc,
    mul_div_cancel₀ _ hy]

/-- A point in a finite denominator-open slice is an isolated affine component. -/
theorem isolated_of_finite_open {I : Ideal GeoJets} {D : GeoJets} {S : Finset GeoPoint}
    (hS : ∀ x ∈ zeroLocus GeoField I, eval x D ≠ 0 → x ∈ S)
    {y : GeoPoint} (hy : y ∈ zeroLocus GeoField I) (hD : eval y D ≠ 0) :
    RingHom.ker (eval y) ∈ I.minimalPrimes := by
  classical
  obtain ⟨P, hP, hyP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus I D y hy hD
  obtain ⟨hmin, hDP⟩ := Ideal.mem_retainedMinimalPrimes.mp hP
  have hle : S.inf (fun x => vanishingIdeal GeoField {x}) ≤ P := by
    intro q hq
    have hm : D * q ∈ P := by
      let _ := hmin.isPrime
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := GeoField) P]
      intro x hx
      by_cases hDx : eval x D = 0
      · simp [aeval_eq_eval, hDx]
      · have hxs := hS x (zeroLocus_anti_mono hmin.le hx) hDx
        have hqx := (Finset.inf_le (f := fun x => vanishingIdeal GeoField {x}) hxs) hq
        rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval] at hqx
        simp [aeval_eq_eval, hqx]
    exact (hmin.isPrime.mem_or_mem hm).resolve_left hDP
  obtain ⟨x, _, hx⟩ := hmin.isPrime.inf_le'.mp hle
  have hmax : (vanishingIdeal GeoField {x}).IsMaximal := inferInstance
  have heq := hmax.eq_of_le hmin.isPrime.ne_top hx
  have hPy : P ≤ vanishingIdeal GeoField {y} := fun p hp =>
    (mem_vanishingIdeal_singleton_iff y p).mpr (hyP p hp)
  have hPy_eq := hmax.eq_of_le (Ideal.IsMaximal.ne_top inferInstance) (heq ▸ hPy)
  have hy_eq : vanishingIdeal GeoField {y} = P := hPy_eq.symm.trans heq
  have hk : RingHom.ker (eval y) = vanishingIdeal GeoField {y} := by
    ext p
    simp [aeval_eq_eval]
  rw [hk, hy_eq]
  exact hmin

end

end K1_13_7_1_2
end PackSource_K1_13_7_1_2Geometry

section PackSource_K1_13_7_1_2Sections
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2

noncomputable section

open K1 K1_13 K1_13_6 K1_13_7_1 MvPolynomial
open scoped Polynomial BigOperators

def actualJet (s : K → K[X]) (γ : K) : GeoPoint :=
  fun i => genericCoeffs (jet (extend (s γ)) i)

def markPoint (s : K → K[X]) (γ : K) : TaylorPoint :=
  fun i => genericCoeffs (Polynomial.hasseDeriv i.val (extend (s γ)))

theorem chartPoint_actual {C : TaylorChart} {s : K → K[X]} {γ : K}
    (h : C.Recovers (extend (s γ))) : chartPoint C (actualJet s γ) = markPoint s γ := by
  funext i
  change evalGeneric (extend (s γ)) (C.numerator i) / evalGeneric (extend (s γ)) C.denom =
    markPoint s γ i
  rw [h.2 i, mul_comm, mul_div_cancel_right₀ _ h.1]
  rfl

private theorem markPoint_injOn {Γ : Finset K} {s : K → K[X]}
    (h : Set.InjOn s (Γ : Set K)) : Set.InjOn (markPoint s) (Γ : Set K) := by
  intro a ha b hb heq
  have h₀ := congrFun heq (0 : TaylorIndex)
  have he : extend (s a) = extend (s b) := genericCoeffs_injective
    (by simpa only [markPoint, Fin.val_zero, Polynomial.hasseDeriv_zero'] using h₀)
  exact h ha hb (Polynomial.map_injective embed embed.injective he)

private def constants : Geom →+* GeoField := genericCoeffs.comp Polynomial.C
private def center : GeoField := genericCoeffs Polynomial.X

private def valueForm (x a : K) : AffineForm :=
  (-constants (embed a), fun i => (constants (embed x) - center) ^ i.val)

private theorem eval_at_center (p : Geom[X]) : (p.map constants).eval center = genericCoeffs p := by
  rw [Polynomial.eval_map]
  simpa only [constants, center, Polynomial.eval₂_C_X] using
    (Polynomial.hom_eval₂ p Polynomial.C genericCoeffs Polynomial.X).symm

private theorem value_eval {s : K → K[X]} {γ x a : K}
    (hd : (s γ).natDegree < taylorLength) :
    aeval (markPoint s γ) (formPolynomial (valueForm x a)) = 0 ↔ (s γ).eval x = a := by
  let p := (extend (s γ)).map constants
  have hdeg : (Polynomial.taylor center p).natDegree < taylorLength := by
    rw [Polynomial.natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt (Polynomial.natDegree_map_le.trans_lt hd)
  have hsum := Polynomial.eval_eq_sum_range' hdeg (constants (embed x) - center)
  rw [← Fin.sum_univ_eq_sum_range, Polynomial.taylor_eval_sub] at hsum
  simp_rw [p, Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_at_center,
    Polynomial.eval_map_apply] at hsum
  rw [aeval_eq_eval, eval_formPolynomial]
  change -constants (embed a) + (∑ i : TaylorIndex,
    (constants (embed x) - center) ^ i.val * markPoint s γ i) = 0 ↔ _
  simp_rw [mul_comm (_ ^ _), markPoint, Polynomial.hasseDeriv_map]
  rw [← hsum, add_comm, ← sub_eq_add_neg, sub_eq_zero, constants.injective.eq_iff,
    embed.injective.eq_iff]

private theorem form_degree (a : AffineForm) : (formPolynomial a).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  simp only [totalDegree_C, Nat.zero_le, Nat.max_eq_right]
  exact totalDegree_finsetSum_le (fun i _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add]))

private def allowance (A : TaylorIdeal) : ℕ := ⌊affineDegree A⌋₊

private theorem degree_at_point {A : TaylorIdeal} (hp : A.IsPrime)
    {z : TaylorPoint} (hz : z ∈ zeroLocus GeoField A) : 1 ≤ affineDegree A := by
  classical
  generalize hd : dimension A = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hn : n = 0
    · obtain ⟨hf, hdeg⟩ := finite_zeroLocus_and_ncard_le_affineDegree
        (K := GeoField) A (hd.trans hn)
      have hcard : 1 ≤ (zeroLocus GeoField A).ncard := by
        simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hz) hf
      exact (by exact_mod_cast hcard : (1 : ℚ) ≤ _).trans hdeg
    have hcut : ∃ i, MvPolynomial.X i - MvPolynomial.C (z i) ∉ A := by
      by_contra! hall
      let φ := Ideal.Quotient.mk A
      have hm : φ = φ.comp (MvPolynomial.C.comp (eval z)) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [φ]
        · intro i
          simp only [RingHom.comp_apply, eval_X]
          exact sub_eq_zero.mp (by
            rw [← map_sub]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
      have hsurj : Function.Surjective (algebraMap GeoField (TaylorRing ⧸ A)) := by
        intro q
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact ⟨eval z g, (RingHom.congr_fun hm g).symm⟩
      let _ : Module.Finite GeoField (TaylorRing ⧸ A) :=
        Module.Finite.of_surjective (Algebra.linearMap GeoField (TaylorRing ⧸ A)) hsurj
      exact hn (hd.symm.trans (by simp [dimension, affineHilbertPolynomial_eq_C_finrank]))
    obtain ⟨i, hi⟩ := hcut
    let cut : TaylorRing := MvPolynomial.X i - MvPolynomial.C (z i)
    have hdeg : cut.totalDegree ≤ 1 := (totalDegree_sub _ _).trans (by simp)
    have hzero : z ∈ zeroLocus GeoField (A ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz, by simp [cut]⟩
    obtain ⟨B, hB, hzB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      _ (1 : TaylorRing) _ hzero (by simp)
    let _ := hp
    have hm := (Ideal.mem_retainedMinimalPrimes.mp hB).1
    have hdim := principalCut_natDegree_affineHilbertPolynomial_add_one hi hm
    change dimension B + 1 = dimension A at hdim
    have hBdeg := ih (dimension B) (by omega) hm.isPrime hzB rfl
    have hsum := principalCut_sum_affineDegree_retainedMinimalPrimes_le (1 : TaylorRing) hi hdeg
    have hle := Finset.single_le_sum (f := affineDegree) (fun B _ => affineDegree_nonneg B) hB
    simpa only [Nat.cast_one, one_mul] using hBdeg.trans (hle.trans hsum)

private def marksOn (Γ : Finset K) (s : K → K[X]) (A : TaylorIdeal) : Finset K := by
  classical
  exact Γ.filter fun γ => markPoint s γ ∈ zeroLocus GeoField A

private theorem mem_marksOn {Γ : Finset K} {s : K → K[X]} {A : TaylorIdeal} {γ : K} :
    γ ∈ marksOn Γ s A ↔ γ ∈ Γ ∧ markPoint s γ ∈ zeroLocus GeoField A := by
  classical
  simp [marksOn]

private def piecesOf (Γ : Finset K) (s : K → K[X]) (T : Finset TaylorIdeal) : Pieces Γ :=
  ⟨T.card, fun i => marksOn Γ s (T.equivFin.symm i),
    fun _ _ h => (mem_marksOn.mp h).1, fun i => allowance (T.equivFin.symm i)⟩

private theorem cover_mem {Γ : Finset K} {s : K → K[X]} {T : Finset TaylorIdeal}
    {γ : K} (hγ : γ ∈ Γ) {A : TaylorIdeal} (hA : A ∈ T)
    (hmark : markPoint s γ ∈ zeroLocus GeoField A) : γ ∈ (piecesOf Γ s T).union := by
  classical
  refine Finset.mem_biUnion.mpr ⟨T.equivFin ⟨A, hA⟩, Finset.mem_univ _, ?_⟩
  simpa [piecesOf] using (mem_marksOn.mpr ⟨hγ, hmark⟩ : γ ∈ marksOn Γ s A)

private theorem piecesOf_budget (Γ : Finset K) (s : K → K[X]) (T : Finset TaylorIdeal) :
    ((piecesOf Γ s T).total : ℚ) ≤ ∑ A ∈ T, affineDegree A := by
  have htotal : (piecesOf Γ s T).total = ∑ A ∈ T, allowance A := by
    change ∑ i : Fin T.card, allowance (T.equivFin.symm i) = _
    calc
      _ = ∑ A : T, allowance A := Fintype.sum_equiv T.equivFin.symm _ _ (fun _ => rfl)
      _ = _ := Finset.sum_attach T allowance
  rw [htotal, Nat.cast_sum]
  exact Finset.sum_le_sum fun A _ => Nat.floor_le (affineDegree_nonneg A)

private theorem allowance_pos {Γ : Finset K} {s : K → K[X]} {A : TaylorIdeal}
    (hp : A.IsPrime) (h : (marksOn Γ s A).Nonempty) : 0 < allowance A := by
  obtain ⟨γ, hγ⟩ := h
  exact Nat.floor_pos.mpr (degree_at_point hp (mem_marksOn.mp hγ).2)

private theorem cut_proper {Γ : Finset K} {s : K → K[X]} {A : TaylorIdeal} {x a : K}
    (hd : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hz : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus GeoField A)
    (hmiss : ∃ γ ∈ Γ, (s γ).eval x ≠ a) : formPolynomial (valueForm x a) ∉ A := by
  obtain ⟨γ, hγ, hmiss⟩ := hmiss
  exact fun hm => hmiss ((value_eval (hd γ hγ)).mp (hz γ hγ _ hm))

private theorem curve_sections {Γ : Finset K} {s : K → K[X]} {A : TaylorIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 1)
    (hd : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hi : Set.InjOn (markPoint s) (Γ : Set K))
    (hz : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus GeoField A) :
    CurveSections Γ s (allowance A) := by
  classical
  intro x a hmiss
  let cut := formPolynomial (valueForm x a)
  let J := A ⊔ Ideal.span {cut}
  let H := Γ.filter fun γ => (s γ).eval x = a
  have hc := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp (cut_proper hd hz hmiss) (form_degree (valueForm x a))
  have hdimJ : dimension J = 0 := by
    have h := hc.1
    change dimension J ≤ dimension A - 1 at h
    omega
  have hdeg : affineDegree J ≤ affineDegree A := by
    simpa [affineDegree, hdim, hdimJ, J, cut, Polynomial.leadingCoeff] using hc.2
  obtain ⟨hfinite, hcard⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := GeoField) J hdimJ
  have hsub : (H.image (markPoint s) : Set _) ⊆ zeroLocus GeoField J := by
    intro z hzp
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hzp
    obtain ⟨hΓ, hv⟩ := Finset.mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz γ hΓ, (value_eval (hd γ hΓ)).mpr hv⟩
  have hcount := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn
    (hi.mono (Finset.filter_subset _ _))] at hcount
  exact Nat.le_floor ((Nat.cast_le.mpr hcount).trans (hcard.trans hdeg))

private theorem surface_sections {Γ : Finset K} {s : K → K[X]} {A : TaylorIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 2)
    (hd : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hi : Set.InjOn (markPoint s) (Γ : Set K))
    (hz : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus GeoField A) :
    SurfaceSections Γ s (allowance A) := by
  classical
  let _ := hp
  intro x a hmiss H
  let J := A ⊔ Ideal.span {formPolynomial (valueForm x a)}
  let T := J.minimalPrimesFinset.filter (fun B => (marksOn H s B).Nonempty)
  have hproper := cut_proper hd hz hmiss
  have hmin (B : TaylorIdeal) (hB : B ∈ T) : J.IsMinimalPrime B :=
    Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hB).1
  refine ⟨piecesOf H s T, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hΓ, hv⟩ := Finset.mem_filter.mp hγ
    have hzero : markPoint s γ ∈ zeroLocus GeoField J :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz γ hΓ, (value_eval (hd γ hΓ)).mpr hv⟩
    obtain ⟨B, hB, hzB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      J (1 : TaylorRing) _ hzero (by simp)
    exact cover_mem hγ (Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
      (Ideal.mem_retainedMinimalPrimes.mp hB).1, ⟨γ, mem_marksOn.mpr ⟨hγ, hzB⟩⟩⟩) hzB
  · intro i
    let B := T.equivFin.symm i
    have hm := hmin B B.property
    have hdimB := principalCut_natDegree_affineHilbertPolynomial_add_one hproper hm
    change dimension (B : TaylorIdeal) + 1 = dimension A at hdimB
    apply curve_sections hm.isPrime (by omega : dimension (B : TaylorIdeal) = 1)
    · exact fun γ hγ => hd γ (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1
    · exact hi.mono (fun _ hγ => (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1)
    · exact fun _ hγ => (mem_marksOn.mp hγ).2
  · intro i
    let B := T.equivFin.symm i
    exact allowance_pos (hmin B B.property).isPrime (Finset.mem_filter.mp B.property).2
  · apply Nat.le_floor
    have hsum := principalCut_sum_affineDegree_minimalPrimes_le hproper (form_degree (valueForm x a))
    exact (piecesOf_budget H s T).trans ((Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun B _ _ => affineDegree_nonneg B)).trans
      (by simpa only [Nat.cast_one, one_mul] using hsum))

/-- Proper value cuts of the separate surface images supply the marked pieces. -/
theorem pieces_of_surface_family {Γ : Finset K} {s : K → K[X]} (T : Finset TaylorIdeal) {d : ℕ}
    (hT : ∀ A ∈ T, A.IsPrime ∧ dimension A = 2)
    (hd : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength) (hi : Set.InjOn s (Γ : Set K))
    (hz : ∀ γ ∈ Γ, ∃ A ∈ T, markPoint s γ ∈ zeroLocus GeoField A)
    (hbudget : ∑ A ∈ T, affineDegree A ≤ d) :
    ∃ B : Pieces Γ, Γ ⊆ B.union ∧ B.surfaces s ∧ (∀ i, 0 < B.degree i) ∧ B.total ≤ d := by
  classical
  let U := T.filter (fun A => (marksOn Γ s A).Nonempty)
  refine ⟨piecesOf Γ s U, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨A, hA, hmark⟩ := hz γ hγ
    exact cover_mem hγ (Finset.mem_filter.mpr ⟨hA, ⟨γ, mem_marksOn.mpr ⟨hγ, hmark⟩⟩⟩) hmark
  · intro i
    let A := U.equivFin.symm i
    obtain ⟨hp, hdim⟩ := hT A (Finset.mem_filter.mp A.property).1
    have hsub : marksOn Γ s A ⊆ Γ := fun _ h => (mem_marksOn.mp h).1
    exact surface_sections hp hdim (fun γ hγ => hd γ (hsub hγ))
      ((markPoint_injOn hi).mono hsub) (fun _ hγ => (mem_marksOn.mp hγ).2)
  · intro i
    let A := U.equivFin.symm i
    obtain ⟨hA, hmark⟩ := Finset.mem_filter.mp A.property
    exact allowance_pos (hT A hA).1 hmark
  · exact Nat.cast_le.mp ((piecesOf_budget Γ s U).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun A _ _ => affineDegree_nonneg A)).trans hbudget))

end

end K1_13_7_1_2
end PackSource_K1_13_7_1_2Sections

section PackSource_K1_13_7_1_2Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2

noncomputable section

open K1 K1_13 K1_13_6 K1_13_7_1 MvPolynomial
open scoped BigOperators

/-- Each retained component of the proper pair gives a surface in Taylor space. -/
def c1 : Prop :=
  ∀ f g : GeoJets, f ≠ 0 → g ≠ 0 → IsRelPrime f g → ∀ C : TaylorChart,
    ∀ P ∈ retained f g C, (imageIdeal C P).IsPrime ∧ dimension (imageIdeal C P) = 2

/-- Two common general affine forms measure the sum of the degrees of the surfaces. -/
def c2 : Prop :=
  ∀ (T : Finset TaylorIdeal) (D : TaylorRing),
    (∀ A ∈ T, A.IsPrime ∧ dimension A = 2 ∧ D ∉ A) →
    ∃ (a b : AffineForm) (sectionPoints : Finset TaylorPoint),
      (∀ z, z ∈ sectionPoints ↔ (∃ A ∈ T, z ∈ zeroLocus GeoField A) ∧
        eval z (formPolynomial a) = 0 ∧ eval z (formPolynomial b) = 0) ∧
      (∀ z ∈ sectionPoints, eval z D ≠ 0) ∧
      (∑ A ∈ T, affineDegree A) ≤ (sectionPoints.card : ℚ)

private theorem mem_pair {y : GeoPoint} {f g : GeoJets} :
    y ∈ zeroLocus GeoField (pairIdeal f g) ↔ eval y f = 0 ∧ eval y g = 0 := by
  rw [pairIdeal, zeroLocus_span]
  simp [aeval_eq_eval]

private theorem mem_slice {y : GeoPoint} {f g u v : GeoJets} :
    y ∈ zeroLocus GeoField (Ideal.span ({f, g, u, v} : Set GeoJets)) ↔
      (eval y f = 0 ∧ eval y g = 0) ∧ eval y u = 0 ∧ eval y v = 0 := by
  rw [zeroLocus_span]
  simp [aeval_eq_eval, and_assoc]

theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_1.c2 := by
  classical
  intro f g hf hg hfg C d hbound Γ s hinj hmarks
  let T := (retained f g C).image (imageIdeal C)
  have hT : ∀ A ∈ T, A.IsPrime ∧ dimension A = 2 ∧ imageDenom C ∉ A := by
    intro A hA
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hmin, hden⟩ := Ideal.mem_retainedMinimalPrimes.mp hP
    obtain ⟨hp, hd⟩ := h1 f g hf hg hfg C P hP
    exact ⟨hp, hd, imageDenom_notMem hmin.isPrime hden⟩
  obtain ⟨a, b, sectionPoints, hZ, hDZ, hsum⟩ := h2 T (imageDenom C) hT
  let S := sectionPoints.image project
  let I := Ideal.span ({f, g, C.pullback a, C.pullback b} : Set GeoJets)
  have hfinite : ∀ y ∈ zeroLocus GeoField I, eval y C.denom ≠ 0 → y ∈ S := by
    intro y hy hDy
    obtain ⟨hpair, ha, hb⟩ := mem_slice.mp hy
    obtain ⟨P, hP, hyP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      (pairIdeal f g) C.denom y (mem_pair.mpr hpair) hDy
    rw [eval_pullback C a y hDy] at ha
    rw [eval_pullback C b y hDy] at hb
    have hz : chartPoint C y ∈ sectionPoints := (hZ _).mpr
      ⟨⟨imageIdeal C P, Finset.mem_image.mpr ⟨P, hP, rfl⟩, chartPoint_mem_image hyP hDy⟩,
        (mul_eq_zero.mp ha).resolve_left hDy, (mul_eq_zero.mp hb).resolve_left hDy⟩
    exact Finset.mem_image.mpr ⟨_, hz, project_chartPoint C y hDy⟩
  have hchart : ∀ z ∈ sectionPoints, chartPoint C (project z) = z := by
    intro z hz
    obtain ⟨A, hA, hzA⟩ := ((hZ z).mp hz).1
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hA
    exact chartPoint_project hzA (hDZ z hz)
  have hcard : S.card = sectionPoints.card := by
    apply Finset.card_image_of_injOn
    intro z hz w hw hwz
    rw [← hchart z hz, ← hchart w hw, hwz]
  have hSbound := hbound a b S (fun y hy => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hD : eval (project z) C.denom ≠ 0 := by
      rw [← eval_imageDenom]
      exact hDZ z hz
    obtain ⟨⟨A, hA, hzA⟩, ha, hb⟩ := (hZ z).mp hz
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hA
    have hpy := project_mem_source hzA
    have hpair := mem_pair.mp (zeroLocus_anti_mono (Ideal.mem_retainedMinimalPrimes.mp hP).1.le hpy)
    have hu : eval (project z) (C.pullback a) = 0 := by
      rw [eval_pullback C a _ hD, hchart z hz, ha, mul_zero]
    have hv : eval (project z) (C.pullback b) = 0 := by
      rw [eval_pullback C b _ hD, hchart z hz, hb, mul_zero]
    exact ⟨isolated_of_finite_open hfinite (mem_slice.mpr ⟨hpair, hu, hv⟩) hD, hD⟩)
  have hbudget : ∑ A ∈ T, affineDegree A ≤ (d : ℚ) := by
    exact hsum.trans (Nat.cast_le.mpr (hcard ▸ hSbound))
  apply pieces_of_surface_family T (fun A hA => ⟨(hT A hA).1, (hT A hA).2.1⟩) _ hinj _ hbudget
  · exact fun γ hγ => Nat.lt_succ_of_le (hmarks γ hγ).1
  · intro γ hγ
    obtain ⟨_, hF, hG, hC⟩ := hmarks γ hγ
    obtain ⟨P, hP, hpt⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      (pairIdeal f g) C.denom (actualJet s γ) (mem_pair.mpr ⟨hF, hG⟩) hC.1
    refine ⟨imageIdeal C P, Finset.mem_image.mpr ⟨P, hP, rfl⟩, ?_⟩
    rw [← chartPoint_actual hC]
    exact chartPoint_mem_image hpt hC.1

end

end K1_13_7_1_2
end PackSource_K1_13_7_1_2Split

section PackSource_K1_13_7_1_2_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_2

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 MvPolynomial
open scoped BigOperators

/-- Each of the two forms has an independent constant and an independent coefficient
for every Taylor coordinate. -/
abbrev SectionVariables := Bool × Option TaylorIndex
abbrev SectionParameter := SectionVariables → GeoField
abbrev SectionPolynomial := MvPolynomial SectionVariables GeoField

def sectionForm (p : SectionParameter) (j : Bool) : AffineForm :=
  (p (j, none), fun i => p (j, some i))

def cutIdeal (A : TaylorIdeal) (p : SectionParameter) : TaylorIdeal :=
  (A ⊔ Ideal.span {formPolynomial (sectionForm p false)}) ⊔
    Ideal.span {formPolynomial (sectionForm p true)}

/-- A condition on the pair holds wherever a nonzero parameter polynomial is nonzero. -/
def HoldsOnPrincipalOpen (condition : SectionParameter → Prop) : Prop :=
  ∃ f : SectionPolynomial, f ≠ 0 ∧ ∀ p, eval p f ≠ 0 → condition p

theorem mem_cutIdeal_zeroLocus {A : TaylorIdeal} {p : SectionParameter} {z : TaylorPoint} :
    z ∈ zeroLocus GeoField (cutIdeal A p) ↔ z ∈ zeroLocus GeoField A ∧
      eval z (formPolynomial (sectionForm p false)) = 0 ∧
      eval z (formPolynomial (sectionForm p true)) = 0 := by
  simp only [cutIdeal, mem_zeroLocus_sup_span_singleton_iff, aeval_eq_eval, and_assoc]

theorem HoldsOnPrincipalOpen.and {f g : SectionParameter → Prop}
    (hf : HoldsOnPrincipalOpen f) (hg : HoldsOnPrincipalOpen g) :
    HoldsOnPrincipalOpen (fun p => f p ∧ g p) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  refine ⟨F * G, mul_ne_zero hF hG, fun p hp => ?_⟩
  rw [map_mul] at hp
  exact ⟨hf p (left_ne_zero_of_mul hp), hg p (right_ne_zero_of_mul hp)⟩

theorem HoldsOnPrincipalOpen.finset_all {ι : Type*} (s : Finset ι)
    (condition : ι → SectionParameter → Prop)
    (h : ∀ i ∈ s, HoldsOnPrincipalOpen (condition i)) :
    HoldsOnPrincipalOpen (fun p => ∀ i ∈ s, condition i p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, one_ne_zero, by simp⟩
  | insert i s hi ih =>
    simpa only [Finset.forall_mem_insert] using
      (h i (Finset.mem_insert_self i s)).and (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem HoldsOnPrincipalOpen.exists_parameter {condition : SectionParameter → Prop}
    (h : HoldsOnPrincipalOpen condition) : ∃ p, condition p := by
  obtain ⟨f, hf, hc⟩ := h
  by_contra! hn
  apply hf
  apply MvPolynomial.funext
  intro p
  rw [map_zero]
  exact not_not.mp (mt (hc p) (hn p))

end

end K1_13_7_1_2_2
end PackSource_K1_13_7_1_2_2Defs

section PackSource_K1_13_7_1_2_2_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_2_1

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2 MvPolynomial

abbrev SectionField := FractionRing SectionPolynomial
abbrev UniversalRing := MvPolynomial TaylorIndex SectionPolynomial
abbrev GenericRing := MvPolynomial TaylorIndex SectionField

/-- Interpret a constant and a tuple of linear coefficients as an affine polynomial. -/
def affinePolynomial {k : Type} [CommRing k] (t : Option TaylorIndex → k) :
    MvPolynomial TaylorIndex k :=
  MvPolynomial.C (t none) + ∑ i : TaylorIndex, MvPolynomial.C (t (some i)) * MvPolynomial.X i

/-- The affine forms with independent coefficients over the parameter ring. -/
def universalForm (j : Bool) : UniversalRing :=
  affinePolynomial (fun i => MvPolynomial.X (j, i))

def genericCoordinate (j : Bool) (i : Option TaylorIndex) : SectionField :=
  algebraMap SectionPolynomial SectionField (MvPolynomial.X (j, i))

def genericForm (j : Bool) : GenericRing :=
  affinePolynomial (genericCoordinate j)

def genericBase (A : TaylorIdeal) : Ideal GenericRing :=
  A.map (MvPolynomial.map (algebraMap GeoField SectionField))

def genericFirstCut (A : TaylorIdeal) : Ideal GenericRing :=
  genericBase A ⊔ Ideal.span {genericForm false}

def universalCut (A : TaylorIdeal) : Ideal UniversalRing :=
  (A.map (MvPolynomial.map (C : GeoField →+* SectionPolynomial)) ⊔
    Ideal.span {universalForm false}) ⊔ Ideal.span {universalForm true}

def genericIdeal (J : Ideal UniversalRing) : Ideal GenericRing :=
  J.map (MvPolynomial.map (algebraMap SectionPolynomial SectionField))

def specializedIdeal (J : Ideal UniversalRing) (p : SectionParameter) : TaylorIdeal :=
  J.map (MvPolynomial.map (eval p))

/-- A cut acts injectively on the affine quotient and on successive degree
quotients in sufficiently high degrees. -/
def RegularLinearCut {k σ : Type} [Field k] (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) : Prop :=
  IsLeftRegular (Ideal.Quotient.mk I f) ∧
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ quotientDegreeLE I (n + 1),
      Ideal.Quotient.mk I f * x ∈ quotientDegreeLE I (n + 1) →
      x ∈ quotientDegreeLE I n

end

end K1_13_7_1_2_2_1
end PackSource_K1_13_7_1_2_2_1Defs

section PackSource_K1_13_7_1_2_2Avoidance
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace K1_13_7_1_2_2

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 MvPolynomial Algebra
open scoped BigOperators

private theorem trdeg_eq_of_finite_injective {k S R : Type} [Field k]
    [CommRing S] [IsDomain S] [CommRing R] [IsDomain R] [Algebra k S] [Algebra k R]
    (g : S →ₐ[k] R) (hg : Function.Injective g) (hfin : g.Finite) :
    trdeg k R = trdeg k S := by
  let algebra := g.toRingHom.toAlgebra
  let := algebra
  let : IsScalarTower k S R := .of_algebraMap_eq' g.comp_algebraMap.symm
  let : FaithfulSMul S R := (faithfulSMul_iff_algebraMap_injective S R).mpr hg
  let : Module.Finite S R := hfin
  let : Algebra.IsIntegral S R := Algebra.IsIntegral.of_finite S R
  rw [← trdeg_add_eq k S (A := R), trdeg_eq_zero (R := S) (A := R), add_zero]

/-- Noether normalization identifies the transcendence degree of an integral
coordinate algebra with the degree of its affine Hilbert polynomial. -/
private theorem trdeg_quotient {k σ : Type} [Field k] [Finite σ]
    {P : Ideal (MvPolynomial σ k)} [P.IsPrime] :
    trdeg k (MvPolynomial σ k ⧸ P) = ((affineHilbertPolynomial P).natDegree : Cardinal) := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ P)
  have hd : (affineHilbertPolynomial P).natDegree = d := by
    simpa only [Nat.card_fin] using
      natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfin hg
  rw [hd, trdeg_eq_of_finite_injective g hg hfin]
  simp [Cardinal.mk_fintype]

private theorem trdeg_adjoin_variables {k R ι : Type} [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] :
    trdeg k (MvPolynomial ι R) = trdeg k R + Cardinal.mk ι := by
  let : FaithfulSMul R (MvPolynomial ι R) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (C_injective ι R)
  rw [← trdeg_add_eq k R (A := MvPolynomial ι R), MvPolynomial.trdeg_of_isDomain,
    Cardinal.lift_id]

private abbrev LinearVariables := Bool × TaylorIndex

private abbrev IncidenceRing (P : TaylorIdeal) :=
  MvPolynomial LinearVariables (TaylorRing ⧸ P)

/-- After imposing both incidence equations, the constant coefficients are
determined by the point and the remaining coefficients. -/
private def incidenceCoordinates (P : TaylorIdeal) : SectionVariables → IncidenceRing P
  | (j, some i) => MvPolynomial.X (j, i)
  | (j, none) => -∑ i, MvPolynomial.X (j, i) * MvPolynomial.C (Ideal.Quotient.mk P (MvPolynomial.X i))

private theorem parameterMap_not_injective {k σ : Type} [Field k] [Fintype σ]
    {P : Ideal (MvPolynomial σ k)} [P.IsPrime]
    (hd : (affineHilbertPolynomial P).natDegree ≤ 1)
    (φ : MvPolynomial (Bool × Option σ) k →ₐ[k]
      MvPolynomial (Bool × σ) (MvPolynomial σ k ⧸ P)) :
    ¬ Function.Injective φ := by
  intro hinj
  have hle : trdeg k (MvPolynomial (Bool × Option σ) k) ≤
      trdeg k (MvPolynomial (Bool × σ) (MvPolynomial σ k ⧸ P)) :=
    trdeg_le_of_injective (R := k) (A := MvPolynomial (Bool × Option σ) k)
      (A' := MvPolynomial (Bool × σ) (MvPolynomial σ k ⧸ P)) φ hinj
  let n := Fintype.card σ
  let d := (affineHilbertPolynomial P).natDegree
  have hs : trdeg k (MvPolynomial (Bool × Option σ) k) = ((2 * (n + 1) : ℕ) : Cardinal) := by
    simp [Cardinal.mk_fintype, n, Fintype.card_prod]
  have ht : trdeg k (MvPolynomial (Bool × σ) (MvPolynomial σ k ⧸ P)) =
      ((d + 2 * n : ℕ) : Cardinal) := by
    rw [trdeg_adjoin_variables, trdeg_quotient]
    simp [Cardinal.mk_fintype, n, d, Fintype.card_prod, Nat.cast_add, Nat.cast_mul]
  have hcast : ((2 * (n + 1) : ℕ) : Cardinal) ≤ ((d + 2 * n : ℕ) : Cardinal) := by
    simpa only [hs, ht] using hle
  exact (by omega : ¬ 2 * (n + 1) ≤ d + 2 * n) (by exact_mod_cast hcast)

private theorem eval_incidenceCoordinates {P : TaylorIdeal} {p : SectionParameter}
    {z : TaylorPoint} (hz : z ∈ zeroLocus GeoField P)
    (hc : ∀ j, eval z (formPolynomial (sectionForm p j)) = 0) (f : SectionPolynomial) :
    eval₂Hom (zeroLocusPointHom P ⟨z, hz⟩).toRingHom (fun i : LinearVariables => p (i.1, some i.2))
      (aeval (R := GeoField) (incidenceCoordinates P) f) = eval p f := by
  let e := eval₂Hom (zeroLocusPointHom P ⟨z, hz⟩).toRingHom
    (fun i : LinearVariables => p (i.1, some i.2))
  have hcoord (i : TaylorIndex) :
      zeroLocusPointHom P ⟨z, hz⟩ (Ideal.Quotient.mk P (MvPolynomial.X i)) = z i := by
    change aeval z (MvPolynomial.X i) = z i
    exact aeval_X _ _
  have hcomp : e.comp (aeval (R := GeoField) (incidenceCoordinates P)).toRingHom = eval p := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change e (aeval (R := GeoField) (incidenceCoordinates P) (MvPolynomial.C a)) =
        eval p (MvPolynomial.C a)
      rw [aeval_C, MvPolynomial.algebraMap_apply, eval_C]
      exact (eval₂Hom_C _ _ _).trans ((zeroLocusPointHom P ⟨z, hz⟩).commutes a)
    · rintro ⟨j, i⟩
      change e (aeval (R := GeoField) (incidenceCoordinates P) (MvPolynomial.X (j, i))) =
        eval p (MvPolynomial.X (j, i))
      rw [aeval_X, eval_X]
      cases i with
      | none =>
        have hj := hc j
        rw [eval_formPolynomial] at hj
        change p (j, none) + (∑ i, p (j, some i) * z i) = 0 at hj
        have he : -(∑ i, p (j, some i) * z i) = p (j, none) :=
          (eq_neg_of_add_eq_zero_left hj).symm
        rw [incidenceCoordinates, map_neg, map_sum, ← he]
        refine congrArg (fun x : GeoField => -x) (Finset.sum_congr rfl ?_)
        intro i _
        rw [map_mul]
        simp only [e, eval₂Hom_X', eval₂Hom_C, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, hcoord]
      | some i => exact eval₂Hom_X' _ _ _
  exact RingHom.congr_fun hcomp f

private theorem avoids_prime {P : TaylorIdeal} (hP : P.IsPrime) (hd : dimension P ≤ 1) :
    HoldsOnPrincipalOpen (fun p => zeroLocus GeoField (cutIdeal P p) = ∅) := by
  let := hP
  let φ : SectionPolynomial →ₐ[GeoField] IncidenceRing P := aeval (incidenceCoordinates P)
  have hf : ¬ Function.Injective φ := parameterMap_not_injective hd φ
  rw [injective_iff_map_eq_zero] at hf
  push Not at hf
  obtain ⟨f, hf, hf0⟩ := hf
  refine ⟨f, hf0, fun p hp => Set.eq_empty_iff_forall_notMem.mpr fun z hz => hp ?_⟩
  obtain ⟨hz, h0, h1⟩ := mem_cutIdeal_zeroLocus.mp hz
  have hc : ∀ j, eval z (formPolynomial (sectionForm p j)) = 0 := by
    intro j
    cases j
    · exact h0
    · exact h1
  rw [← eval_incidenceCoordinates hz hc f]
  rw [show (aeval (R := GeoField) (incidenceCoordinates P)) f = 0 from hf, map_zero]

/-- A common general codimension-two affine section misses every point of
a prescribed locus of dimension at most one. -/
theorem avoids_lower_dimensional (J : TaylorIdeal) (hd : dimension J ≤ 1) :
    HoldsOnPrincipalOpen (fun p => zeroLocus GeoField (cutIdeal J p) = ∅) := by
  have hopen := HoldsOnPrincipalOpen.finset_all (J.retainedMinimalPrimes 1)
    (fun P p => zeroLocus GeoField (cutIdeal P p) = ∅) (fun P hP => by
      have hm := (Ideal.mem_retainedMinimalPrimes.mp hP).1
      exact avoids_prime hm.isPrime ((natDegree_affineHilbertPolynomial_le_of_le hm.le).trans hd))
  obtain ⟨f, hf, h⟩ := hopen
  refine ⟨f, hf, fun p hp => Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_⟩
  obtain ⟨hz, h0, h1⟩ := mem_cutIdeal_zeroLocus.mp hz
  obtain ⟨P, hP, hzP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J 1 z hz (by simp)
  exact Set.eq_empty_iff_forall_notMem.mp (h p hp P hP) z
    (mem_cutIdeal_zeroLocus.mpr ⟨hzP, h0, h1⟩)

end

end K1_13_7_1_2_2
end PackSource_K1_13_7_1_2_2Avoidance

section PackSource_K1_13_7_1_2_2_1Hilbert
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_2_1

noncomputable section

open MvPolynomial

variable {k σ : Type} [Field k]
variable {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}

private theorem strict_of_regular (h : RegularLinearCut I f) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : MvPolynomial σ k ⧸ I,
      Ideal.Quotient.mk I f * x ∈ quotientDegreeLE I (n + 1) →
      x ∈ quotientDegreeLE I n := by
  obtain ⟨_, N, hN⟩ := h
  refine ⟨N, fun n hn x hx => ?_⟩
  have shrink (r : ℕ) (hr : x ∈ quotientDegreeLE I (n + r)) :
      x ∈ quotientDegreeLE I n := by
    induction r with
    | zero => exact hr
    | succ r ih =>
      exact ih (hN (n + r) (by omega) x hr
        (quotientDegreeLE_mono I (by omega) hx))
  obtain ⟨m, hm⟩ := exists_mem_quotientDegreeLE I x
  exact shrink m (quotientDegreeLE_mono I (by omega) hm)

variable [Finite σ]

private theorem hilbertFunction_cut_step (hf : f.totalDegree ≤ 1)
    (hreg : IsLeftRegular (Ideal.Quotient.mk I f)) (n : ℕ)
    (hstrict : ∀ x : MvPolynomial σ k ⧸ I,
      Ideal.Quotient.mk I f * x ∈ quotientDegreeLE I (n + 1) →
        x ∈ quotientDegreeLE I n) :
    affineHilbertFunction (I ⊔ Ideal.span {f}) (n + 1) + affineHilbertFunction I n =
      affineHilbertFunction I (n + 1) := by
  let J := I ⊔ Ideal.span {f}
  let hIJ : I ≤ J := le_sup_left
  let U := quotientDegreeLE I n
  let V := quotientDegreeLE I (n + 1)
  let W := quotientDegreeLE J (n + 1)
  let q := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hq (x : V) : q x ∈ W := by
    obtain ⟨p, hp, he⟩ := mem_quotientDegreeLE.mp x.property
    rw [← he]
    exact mk_mem_quotientDegreeLE hp
  let cut : V →ₗ[k] W := (q.domRestrict V).codRestrict W hq
  have hsurj : Function.Surjective cut := by
    intro y
    obtain ⟨p, hp, he⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext he⟩
  let μ := (LinearMap.mulLeft k (Ideal.Quotient.mk I f)).domRestrict U
  have hμ (x : U) : μ x ∈ V := by
    change Ideal.Quotient.mk I f * (x : MvPolynomial σ k ⧸ I) ∈ quotientDegreeLE I (n + 1)
    have h := mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE (I := I) hf) x.property
    simpa only [Nat.add_comm 1 n] using h
  let m := μ.codRestrict V hμ
  have hfzero : q (Ideal.Quotient.mk I f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hm (x : U) : m x ∈ LinearMap.ker cut := by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change q (Ideal.Quotient.mk I f * x) = 0
    change Ideal.Quotient.factorₐ k hIJ (Ideal.Quotient.mk I f * x) = 0
    rw [map_mul]
    change q (Ideal.Quotient.mk I f) * q x = 0
    rw [hfzero, zero_mul]
  let e := m.codRestrict (LinearMap.ker cut) hm
  have he_inj : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (hreg (congrArg
      (fun z : LinearMap.ker cut => (z.1.1 : MvPolynomial σ k ⧸ I)) hxy))
  have he_surj : Function.Surjective e := by
    intro y
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := I) y.1.1
    have hy : q y.1.1 = 0 := congrArg
      (fun z : W => (z : MvPolynomial σ k ⧸ J)) (LinearMap.mem_ker.mp y.property)
    have hy' : Ideal.Quotient.mk J p = 0 := by
      rw [← hp] at hy
      exact hy
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hy')
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ht
    have hr : Ideal.Quotient.mk I f * Ideal.Quotient.mk I r = y.1.1 := by
      rw [← hp, ← hst, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hs, zero_add, map_mul]
    refine ⟨⟨Ideal.Quotient.mk I r, hstrict _ (hr.symm ▸ y.1.2)⟩, ?_⟩
    exact Subtype.ext (Subtype.ext hr)
  have hker := (LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩).finrank_eq
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hker] at hrank
  exact hrank

/-- Strict filtered exactness gives one backward difference of the affine
Hilbert polynomial. -/
theorem hilbertPolynomial_cut (hf : f.totalDegree ≤ 1) (h : RegularLinearCut I f) :
    affineHilbertPolynomial (I ⊔ Ideal.span {f}) =
      Polynomial.backwardDifference 1 (affineHilbertPolynomial I) := by
  obtain ⟨N, hN⟩ := strict_of_regular h
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial I
  symm
  refine eq_affineHilbertPolynomial_of_eval_eq (N₀ := max N M + 1) fun n hn => ?_
  have hn' : 1 ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub hn', Nat.cast_one]
  rw [Polynomial.eval_backwardDifference, ← hcast, hM n (by omega), hM (n - 1) (by omega)]
  apply sub_eq_iff_eq_add.mpr
  have hs := hilbertFunction_cut_step hf h.1 (n - 1) (hN _ (by omega))
  rw [Nat.sub_add_cancel hn'] at hs
  exact_mod_cast hs.symm

end

end K1_13_7_1_2_2_1
end PackSource_K1_13_7_1_2_2_1Hilbert

section PackSource_K1_13_7_1_2_2Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_2

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 MvPolynomial
open scoped BigOperators

/-- A general pair of affine hyperplanes preserves the degree as a scheme length. -/
def c1 : Prop :=
  ∀ A : TaylorIdeal, A.IsPrime → dimension A = 2 →
    HoldsOnPrincipalOpen (fun p =>
      dimension (cutIdeal A p) = 0 ∧ affineDegree A = affineDegree (cutIdeal A p))

/-- On an integral surface the general intersection scheme is reduced. -/
def c2 : Prop :=
  ∀ A : TaylorIdeal, A.IsPrime → dimension A = 2 →
    HoldsOnPrincipalOpen (fun p => (cutIdeal A p).IsRadical)

private theorem dimension_principal_cut_le_one {A : TaylorIdeal} {D : TaylorRing}
    (hA : A.IsPrime) (hd : dimension A = 2) (hD : D ∉ A) :
    dimension (A ⊔ Ideal.span {D}) ≤ 1 := by
  have hc := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hA hD (b := D.totalDegree) le_rfl).1
  change dimension (A ⊔ Ideal.span {D}) ≤ dimension A - 1 at hc
  rwa [hd] at hc

private theorem dimension_pair_overlap_le_one {A B : TaylorIdeal}
    (hA : A.IsPrime) (hB : B.IsPrime) (hdA : dimension A = 2) (hdB : dimension B = 2)
    (hne : A ≠ B) : dimension (A ⊔ B) ≤ 1 := by
  by_cases hAB : B ≤ A
  · obtain ⟨D, hDA, hDB⟩ : ∃ D ∈ A, D ∉ B :=
      Set.not_subset.mp (show ¬ A ≤ B from fun hBA => hne (le_antisymm hBA hAB))
    have hle : B ⊔ Ideal.span {D} ≤ A ⊔ B :=
      sup_le le_sup_right ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_left hDA))
    exact (natDegree_affineHilbertPolynomial_le_of_le hle).trans
      (dimension_principal_cut_le_one hB hdB hDB)
  · obtain ⟨D, hDB, hDA⟩ : ∃ D ∈ B, D ∉ A := Set.not_subset.mp hAB
    have hle : A ⊔ Ideal.span {D} ≤ A ⊔ B :=
      sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_right hDB))
    exact (natDegree_affineHilbertPolynomial_le_of_le hle).trans
      (dimension_principal_cut_le_one hA hdA hDA)

private theorem degree_le_card_of_radical {I : TaylorIdeal} (hI : I.IsRadical)
    (hd : dimension I = 0) {S : Finset TaylorPoint}
    (hS : (S : Set TaylorPoint) = zeroLocus GeoField I) :
    affineDegree I ≤ (S.card : ℚ) := by
  let : Module.Finite GeoField (TaylorRing ⧸ I) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hd
  have hfinite := finite_zeroLocus_of_finite_quotient (K := GeoField) I
  let : Fintype (zeroLocus GeoField I) := hfinite.fintype
  have hle := LinearMap.finrank_le_finrank_of_injective
    (zeroLocusEvaluation_injective (K := GeoField) I hI)
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] at hle
  change Module.finrank GeoField (TaylorRing ⧸ I) ≤ (zeroLocus GeoField I).ncard at hle
  rw [← hS, Set.ncard_coe_finset] at hle
  exact (affineDegree_eq_finrank I).trans_le (Nat.cast_le.mpr hle)

theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_1_2.c2 := by
  classical
  intro T D hT
  let good (A : TaylorIdeal) (p : SectionParameter) : Prop :=
    (dimension (cutIdeal A p) = 0 ∧ affineDegree A = affineDegree (cutIdeal A p)) ∧
      (cutIdeal A p).IsRadical ∧ zeroLocus GeoField (cutIdeal (A ⊔ Ideal.span {D}) p) = ∅
  have hgood : HoldsOnPrincipalOpen (fun p => ∀ A ∈ T, good A p) := by
    apply HoldsOnPrincipalOpen.finset_all
    intro A hA
    obtain ⟨hp, hd, hD⟩ := hT A hA
    exact (h1 A hp hd).and ((h2 A hp hd).and
      (avoids_lower_dimensional _ (dimension_principal_cut_le_one hp hd hD)))
  let pairs := (T ×ˢ T).filter fun AB => AB.1 ≠ AB.2
  let avoid (AB : TaylorIdeal × TaylorIdeal) (p : SectionParameter) : Prop :=
    zeroLocus GeoField (cutIdeal (AB.1 ⊔ AB.2) p) = ∅
  have havoid : HoldsOnPrincipalOpen (fun p => ∀ AB ∈ pairs, avoid AB p) := by
    apply HoldsOnPrincipalOpen.finset_all
    intro AB hAB
    obtain ⟨hAB, hne⟩ := Finset.mem_filter.mp hAB
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hAB
    exact avoids_lower_dimensional _ (dimension_pair_overlap_le_one (hT _ hA).1 (hT _ hB).1
      (hT _ hA).2.1 (hT _ hB).2.1 hne)
  obtain ⟨p, hp, hpair⟩ := (hgood.and havoid).exists_parameter
  let points (A : TaylorIdeal) : Finset TaylorPoint :=
    if hA : A ∈ T then
      ((finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero
        (cutIdeal A p)).2 (hp A hA).1.1).toFinset
    else ∅
  have hpoints (A : TaylorIdeal) (hA : A ∈ T) (z : TaylorPoint) :
      z ∈ points A ↔ z ∈ zeroLocus GeoField (cutIdeal A p) := by
    simp [points, hA]
  refine ⟨sectionForm p false, sectionForm p true, T.biUnion points, ?_, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨A, hA, hzA⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨hm, ha, hb⟩ := mem_cutIdeal_zeroLocus.mp ((hpoints A hA z).mp hzA)
      exact ⟨⟨A, hA, hm⟩, ha, hb⟩
    · rintro ⟨⟨A, hA, hm⟩, ha, hb⟩
      exact Finset.mem_biUnion.mpr
        ⟨A, hA, (hpoints A hA z).mpr (mem_cutIdeal_zeroLocus.mpr ⟨hm, ha, hb⟩)⟩
  · intro z hz hD
    obtain ⟨A, hA, hzA⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hm, ha, hb⟩ := mem_cutIdeal_zeroLocus.mp ((hpoints A hA z).mp hzA)
    have hzD : z ∈ zeroLocus GeoField (cutIdeal (A ⊔ Ideal.span {D}) p) :=
      mem_cutIdeal_zeroLocus.mpr
        ⟨mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hm, by rwa [aeval_eq_eval]⟩, ha, hb⟩
    simp [(hp A hA).2.2] at hzD
  · have hdisjoint : Set.PairwiseDisjoint (T : Set TaylorIdeal) points := by
      intro A hA B hB hne
      apply Finset.disjoint_left.mpr
      intro z hzA hzB
      have hAB : (A, B) ∈ pairs :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hA, hB⟩, hne⟩
      obtain ⟨hmA, ha, hb⟩ := mem_cutIdeal_zeroLocus.mp ((hpoints A hA z).mp hzA)
      have hmB := (mem_cutIdeal_zeroLocus.mp ((hpoints B hB z).mp hzB)).1
      have hzAB : z ∈ zeroLocus GeoField (cutIdeal (A ⊔ B) p) :=
        mem_cutIdeal_zeroLocus.mpr ⟨by rw [zeroLocus_sup]; exact ⟨hmA, hmB⟩, ha, hb⟩
      have hv : zeroLocus GeoField (cutIdeal (A ⊔ B) p) = ∅ := hpair (A, B) hAB
      simp [hv] at hzAB
    rw [Finset.card_biUnion hdisjoint, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro A hA
    rw [(hp A hA).1.2]
    exact degree_le_card_of_radical (hp A hA).2.1 (hp A hA).1.1
      (Set.ext fun z => hpoints A hA z)

end

end K1_13_7_1_2_2
end PackSource_K1_13_7_1_2_2Split

section PackSource_K1_13_7_1_2_2_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_2_2

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2 MvPolynomial

abbrev LinearVariables := Bool × TaylorIndex
abbrev SurfaceRing (A : TaylorIdeal) := TaylorRing ⧸ A
abbrev SurfaceField (A : TaylorIdeal) := FractionRing (SurfaceRing A)
abbrev IncidenceRing (A : TaylorIdeal) := MvPolynomial LinearVariables (SurfaceRing A)

def coordinate (A : TaylorIdeal) (i : TaylorIndex) : SurfaceRing A :=
  Ideal.Quotient.mk A (MvPolynomial.X i)

/-- The free affine coefficients on the incidence scheme are precisely the linear
parts. The two constant terms are determined by the point of the surface. -/
def incidenceCoordinates (A : TaylorIdeal) : SectionVariables → IncidenceRing A
  | (j, some i) => MvPolynomial.X (j, i)
  | (j, none) => -∑ i, MvPolynomial.X (j, i) * MvPolynomial.C (coordinate A i)

def parameterMap (A : TaylorIdeal) : SectionPolynomial →ₐ[GeoField] IncidenceRing A :=
  aeval (incidenceCoordinates A)

def genericParameterMap (A : TaylorIdeal) :
    SectionPolynomial →+* FractionRing (IncidenceRing A) :=
  (algebraMap (IncidenceRing A) (FractionRing (IncidenceRing A))).comp
    (parameterMap A).toRingHom

end

end K1_13_7_1_2_2_2
end PackSource_K1_13_7_1_2_2_2Defs

section PackSource_K1_13_7_1_2_2_1Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_2_1

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2 MvPolynomial

/-- One independent affine form gives a regular, eventually strict cut
after adjoining its coefficients to those of the defining ideal. -/
def c1 : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E],
    ∀ (t : Option TaylorIndex → E), AlgebraicIndependent k t →
      ∀ I : Ideal (MvPolynomial TaylorIndex k),
        RegularLinearCut (I.map (MvPolynomial.map (algebraMap k E))) (affinePolynomial t)

/-- A finite generic section algebra specializes with its dimension on some
principal open of the parameter space. -/
def c2 : Prop :=
  ∀ J : Ideal UniversalRing, Module.Finite SectionField (GenericRing ⧸ genericIdeal J) →
    HoldsOnPrincipalOpen (fun p =>
      Module.Finite GeoField (TaylorRing ⧸ specializedIdeal J p) ∧
      Module.finrank GeoField (TaylorRing ⧸ specializedIdeal J p) =
        Module.finrank SectionField (GenericRing ⧸ genericIdeal J))

private theorem mapCoefficients_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (MvPolynomial.map (σ := TaylorIndex) g).comp (MvPolynomial.map f) =
      MvPolynomial.map (g.comp f) := by
  apply RingHom.ext
  exact MvPolynomial.map_map f g

private theorem map_affinePolynomial {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Option TaylorIndex → R) :
    MvPolynomial.map f (affinePolynomial t) = affinePolynomial (f ∘ t) := by
  simp only [affinePolynomial, map_add, map_sum, map_mul, map_C, map_X, Function.comp_apply]

private theorem genericIdeal_universalCut (A : TaylorIdeal) :
    genericIdeal (universalCut A) = genericFirstCut A ⊔ Ideal.span {genericForm true} := by
  unfold genericIdeal universalCut genericFirstCut genericBase genericForm genericCoordinate
  rw [IsScalarTower.algebraMap_eq GeoField SectionPolynomial SectionField,
    MvPolynomial.algebraMap_eq]
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_map,
    mapCoefficients_comp, universalForm, map_affinePolynomial, Function.comp_def]

private theorem specializedIdeal_universalCut (A : TaylorIdeal) (p : SectionParameter) :
    specializedIdeal (universalCut A) p = cutIdeal A p := by
  have hcoeff : (eval p).comp (C : GeoField →+* SectionPolynomial) = RingHom.id GeoField :=
    RingHom.ext (fun x => eval_C (f := p) x)
  have hmap_id : MvPolynomial.map (σ := TaylorIndex) (RingHom.id GeoField) =
      RingHom.id TaylorRing := RingHom.ext MvPolynomial.map_id
  have hform (j : Bool) :
      MvPolynomial.map (eval p) (universalForm j) = formPolynomial (sectionForm p j) := by
    simp only [universalForm, affinePolynomial, formPolynomial, sectionForm, map_add, map_sum, map_mul,
      map_C, map_X, eval_X]
  unfold specializedIdeal universalCut cutIdeal
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_map,
    mapCoefficients_comp, hcoeff, hmap_id, Ideal.map_id, hform]

private theorem genericForm_degree (j : Bool) : (genericForm j).totalDegree ≤ 1 := by
  unfold genericForm affinePolynomial
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

/-- Keep the defining equations of the first section over the field generated
by its own coefficients so the second tuple is still independent. -/
private theorem genericRegularCuts (h : c1) (A : TaylorIdeal) :
    RegularLinearCut (genericBase A) (genericForm false) ∧
      RegularLinearCut (genericFirstCut A) (genericForm true) := by
  let t := genericCoordinate false
  let u := genericCoordinate true
  let L := IntermediateField.adjoin GeoField (Set.range t)
  let i : SectionPolynomial →ₐ[GeoField] SectionField :=
    IsScalarTower.toAlgHom GeoField SectionPolynomial SectionField
  have hall := (MvPolynomial.algebraicIndependent_X SectionVariables GeoField).map'
    (f := i) (IsFractionRing.injective SectionPolynomial SectionField)
  let e : Option TaylorIndex ⊕ Option TaylorIndex → SectionVariables :=
    Sum.elim (fun v => (true, v)) (fun v => (false, v))
  have he : Function.Injective e := by
    intro a b hab
    cases a <;> cases b <;> simp_all [e]
  have hind : AlgebraicIndependent GeoField (Sum.elim u t) := by
    have heval : Sum.elim u t = (i ∘ MvPolynomial.X) ∘ e := by
      funext a
      cases a <;> rfl
    rw [heval]
    exact hall.comp e he
  obtain ⟨ht, hu⟩ := AlgebraicIndependent.sumElim_iff.mp hind
  have hu' : AlgebraicIndependent L u :=
    IntermediateField.algebraicIndependent_adjoin_iff.mpr hu
  let tL : Option TaylorIndex → L :=
    fun v => ⟨t v, IntermediateField.subset_adjoin GeoField _ (Set.mem_range_self v)⟩
  let B : Ideal (MvPolynomial TaylorIndex L) :=
    A.map (MvPolynomial.map (algebraMap GeoField L)) ⊔ Ideal.span {affinePolynomial tL}
  have hB : B.map (MvPolynomial.map (algebraMap L SectionField)) = genericFirstCut A := by
    unfold B genericFirstCut genericBase genericForm
    simp only [Ideal.map_sup, Ideal.map_map, mapCoefficients_comp, Ideal.map_span,
      Set.image_singleton, map_affinePolynomial, ← IsScalarTower.algebraMap_eq]
    rfl
  have hsecond := h L SectionField u hu' B
  rw [hB] at hsecond
  exact ⟨h GeoField SectionField t ht A, hsecond⟩

theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_1_2_2.c1 := by
  intro A _ hd
  let P := affineHilbertPolynomial A
  let D := Polynomial.backwardDifference 1 P
  have hP : P.natDegree = 2 := hd
  have hD := Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (b := (1 : ℚ)) (P := P) one_ne_zero (by omega : 0 < P.natDegree)
  have hDd : D.natDegree = 1 := by simpa [D, hP] using hD.1
  have hDD := Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (b := (1 : ℚ)) (P := D) one_ne_zero (by omega : 0 < D.natDegree)
  have hbase : affineHilbertPolynomial (genericBase A) = P :=
    K1_13_5_5_2.hilbertPolynomial_map A
  obtain ⟨hreg₁, hreg₂⟩ := genericRegularCuts h1 A
  have hfirst : affineHilbertPolynomial (genericFirstCut A) = D := by
    rw [genericFirstCut, hilbertPolynomial_cut (genericForm_degree false) hreg₁, hbase]
  have hgeneric : affineHilbertPolynomial (genericIdeal (universalCut A)) =
      Polynomial.backwardDifference 1 D := by
    rw [genericIdeal_universalCut, hilbertPolynomial_cut (genericForm_degree true) hreg₂,
      hfirst]
  have hdgen : (affineHilbertPolynomial (genericIdeal (universalCut A))).natDegree = 0 := by
    rw [hgeneric, hDD.1, hDd]
  let : Module.Finite SectionField (GenericRing ⧸ genericIdeal (universalCut A)) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hdgen
  obtain ⟨g, hg, hopen⟩ := h2 (universalCut A) inferInstance
  refine ⟨g, hg, fun p hp => ?_⟩
  obtain ⟨hfin, hrank⟩ := hopen p hp
  let : Module.Finite GeoField (TaylorRing ⧸ specializedIdeal (universalCut A) p) := hfin
  have hfiber : affineHilbertPolynomial (specializedIdeal (universalCut A) p) =
      affineHilbertPolynomial (genericIdeal (universalCut A)) := by
    rw [affineHilbertPolynomial_eq_C_finrank, affineHilbertPolynomial_eq_C_finrank, hrank]
  rw [specializedIdeal_universalCut] at hfiber
  have hdim : dimension (cutIdeal A p) = 0 := by rw [dimension, hfiber, hdgen]
  refine ⟨hdim, ?_⟩
  unfold affineDegree
  rw [hP, hfiber, hgeneric, hDD.1, hDD.2, hDd, hD.2, hP]
  norm_num [Nat.factorial, P]

end

end K1_13_7_1_2_2_1
end PackSource_K1_13_7_1_2_2_1Split

section PackSource_K1_13_7_1_2_2_2Specialize
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_13_7_1_2_2_2

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2 MvPolynomial

private theorem le_cutIdeal (A : TaylorIdeal) (p : SectionParameter) :
    A ≤ cutIdeal A p :=
  le_sup_left.trans le_sup_left

private def sectionMap (A : TaylorIdeal) (p : SectionParameter) :
    IncidenceRing A →+* (TaylorRing ⧸ cutIdeal A p) :=
  eval₂Hom (Ideal.Quotient.factor (le_cutIdeal A p))
    (fun i : LinearVariables => algebraMap GeoField _ (p (i.1, some i.2)))

private theorem sectionMap_surjective (A : TaylorIdeal) (p : SectionParameter) :
    Function.Surjective (sectionMap A p) := by
  intro r
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨C (Ideal.Quotient.mk A a), eval₂Hom_C _ _ _⟩

private theorem cut_form_mem (A : TaylorIdeal) (p : SectionParameter) (j : Bool) :
    formPolynomial (sectionForm p j) ∈ cutIdeal A p := by
  cases j
  · exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
  · exact Ideal.mem_sup_right (Ideal.subset_span (by simp))

private theorem sectionMap_comp (A : TaylorIdeal) (p : SectionParameter) :
    (sectionMap A p).comp (parameterMap A).toRingHom =
      (algebraMap GeoField (TaylorRing ⧸ cutIdeal A p)).comp (eval p) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change sectionMap A p (parameterMap A (MvPolynomial.C a)) = algebraMap GeoField _ (eval p (MvPolynomial.C a))
    rw [parameterMap, aeval_C, MvPolynomial.algebraMap_apply, eval_C, sectionMap,
      eval₂Hom_C]
    rfl
  · rintro ⟨j, i⟩
    change sectionMap A p (parameterMap A (MvPolynomial.X (j, i))) = algebraMap GeoField _ (eval p (MvPolynomial.X (j, i)))
    rw [parameterMap, aeval_X, eval_X]
    cases i with
    | some i => exact eval₂Hom_X' _ _ _
    | none =>
      let I := cutIdeal A p
      have h := Ideal.Quotient.eq_zero_iff_mem.mpr (cut_form_mem A p j)
      rw [formPolynomial, map_add, map_sum] at h
      change algebraMap GeoField (TaylorRing ⧸ I) (p (j, none)) +
        (∑ i, Ideal.Quotient.mk I (MvPolynomial.C (p (j, some i)) * MvPolynomial.X i)) = 0 at h
      rw [incidenceCoordinates, map_neg, map_sum, eq_neg_of_add_eq_zero_left h]
      apply congrArg (fun y : TaylorRing ⧸ I => -y)
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_mul, sectionMap, eval₂Hom_X', eval₂Hom_C, coordinate,
        Ideal.Quotient.factor_mk]
      rfl

private theorem exists_unramified_open_of_fraction {P B : Type}
    [CommRing P] [CommRing B] [IsDomain B] [Algebra P B] [Algebra.FiniteType P B]
    (h : ((algebraMap B (FractionRing B)).comp (algebraMap P B)).FormallyUnramified) :
    ∃ d : B, d ≠ 0 ∧
      ((algebraMap B (Localization.Away d)).comp (algebraMap P B)).FormallyUnramified := by
  let F := FractionRing B
  let I : Ideal B := ⊥
  let L := Localization.AtPrime I
  have hFr : IsFractionRing B L := by
    change IsLocalization (nonZeroDivisors B) L
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let e : F ≃ₐ[B] L := IsLocalization.algEquiv (nonZeroDivisors B) F L
  let : Algebra.FormallyUnramified P F := by
    rw [← RingHom.formallyUnramified_algebraMap, IsScalarTower.algebraMap_eq P B F]
    exact h
  let : Algebra.IsUnramifiedAt P I :=
    Algebra.FormallyUnramified.of_equiv (e.restrictScalars P)
  obtain ⟨d, hd, hu⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := P) I
  refine ⟨d, (by simpa [I] using hd), ?_⟩
  rw [← IsScalarTower.algebraMap_eq P B (Localization.Away d),
    RingHom.formallyUnramified_algebraMap]
  exact hu

/-- The generic unramified locus contains a principal open of the incidence
scheme. The element cutting out the omitted locus is nonzero. -/
theorem exists_unramified_open (A : TaylorIdeal) (hA : A.IsPrime)
    (h : (genericParameterMap A).FormallyUnramified) :
    ∃ d : IncidenceRing A, d ≠ 0 ∧
      ((algebraMap (IncidenceRing A) (Localization.Away d)).comp
        (parameterMap A).toRingHom).FormallyUnramified := by
  let : A.IsPrime := hA
  let P := SectionPolynomial
  let B := IncidenceRing A
  let : Algebra P B := (parameterMap A).toRingHom.toAlgebra
  let : IsScalarTower GeoField P B :=
    IsScalarTower.of_algebraMap_eq (fun x => ((parameterMap A).commutes x).symm)
  let : Algebra.FiniteType GeoField B :=
    Algebra.FiniteType.trans (S := SurfaceRing A) inferInstance inferInstance
  let : Algebra.FiniteType P B :=
    Algebra.FiniteType.of_restrictScalars_finiteType GeoField P B
  exact exists_unramified_open_of_fraction (P := P) (B := B) h

/-- If the chosen unramified open contains the entire specialized section, its
coordinate ring is an unramified algebra of finite type over the field. -/
theorem radical_of_unramified_open (A : TaylorIdeal) (p : SectionParameter)
    {d : IncidenceRing A} {f : SectionPolynomial}
    (hu : ((algebraMap (IncidenceRing A) (Localization.Away d)).comp
      (parameterMap A).toRingHom).FormallyUnramified)
    (hf : parameterMap A f ∈ Ideal.span {d}) (hp : eval p f ≠ 0) :
    (cutIdeal A p).IsRadical := by
  let T := TaylorRing ⧸ cutIdeal A p
  let B := IncidenceRing A
  let g := sectionMap A p
  let S := Localization.Away d
  have hf' : g (parameterMap A f) = algebraMap GeoField T (eval p f) :=
    RingHom.congr_fun (sectionMap_comp A p) f
  have hd : IsUnit (g d) := by
    apply isUnit_of_dvd_unit ((map_dvd g) (Ideal.mem_span_singleton.mp hf))
    rw [hf']
    exact (isUnit_iff_ne_zero.mpr hp).map (algebraMap GeoField T)
  let g' : S →+* T := IsLocalization.Away.lift d hd
  have hg' : g'.comp (algebraMap B S) = g := IsLocalization.Away.lift_comp d hd
  have hs : Function.Surjective g' := by
    intro y
    obtain ⟨x, hx⟩ := sectionMap_surjective A p y
    exact ⟨algebraMap B S x, (RingHom.congr_fun hg' x).trans hx⟩
  have h := hu.comp (RingHom.FormallyUnramified.of_surjective (f := g') hs)
  rw [← RingHom.comp_assoc, hg', sectionMap_comp] at h
  let : Algebra.FormallyUnramified GeoField T :=
    RingHom.formallyUnramified_algebraMap.mp (RingHom.FormallyUnramified.of_comp h)
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr
    (Algebra.FormallyUnramified.isReduced_of_field GeoField T)

end

end K1_13_7_1_2_2_2
end PackSource_K1_13_7_1_2_2_2Specialize

section PackSource_K1_13_7_1_2_2_2Elimination
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_13_7_1_2_2_2

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2 MvPolynomial Algebra

private theorem trdeg_eq_of_finite_injective {k S R : Type} [Field k]
    [CommRing S] [IsDomain S] [CommRing R] [IsDomain R] [Algebra k S] [Algebra k R]
    (g : S →ₐ[k] R) (hg : Function.Injective g) (hfin : g.Finite) :
    trdeg k R = trdeg k S := by
  let : Algebra S R := g.toRingHom.toAlgebra
  let : IsScalarTower k S R := .of_algebraMap_eq (fun x => (g.commutes x).symm)
  let : FaithfulSMul S R := (faithfulSMul_iff_algebraMap_injective S R).mpr hg
  let : Module.Finite S R := hfin
  let : Algebra.IsIntegral S R := Algebra.IsIntegral.of_finite S R
  rw [← trdeg_add_eq k S (A := R), trdeg_eq_zero (R := S) (A := R), add_zero]

theorem surfaceRing_trdeg (A : TaylorIdeal) (hA : A.IsPrime) (hd : dimension A = 2) :
    trdeg GeoField (SurfaceRing A) = 2 := by
  let : A.IsPrime := hA
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg GeoField (SurfaceRing A)
  have hdim : dimension A = d := by
    simpa only [Nat.card_fin] using
      natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfin hg
  have hd' : d = 2 := hdim.symm.trans hd
  rw [trdeg_eq_of_finite_injective g hg hfin, hd']
  simp [Cardinal.mk_fintype]

theorem surfaceField_trdeg (A : TaylorIdeal) (hA : A.IsPrime) (hd : dimension A = 2) :
    trdeg GeoField (SurfaceField A) = 2 := by
  let : A.IsPrime := hA
  let : Algebra.IsAlgebraic (SurfaceRing A) (SurfaceField A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (SurfaceRing A))
  rw [← trdeg_add_eq GeoField (SurfaceRing A) (A := SurfaceField A),
    trdeg_eq_zero (R := SurfaceRing A) (A := SurfaceField A), add_zero,
    surfaceRing_trdeg A hA hd]

private theorem elimination_incidence_trdeg_of_variables (k R ι : Type) [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [Fintype ι] (hR : trdeg k R = 2) :
    trdeg k (MvPolynomial (Bool × ι) R) =
      ((2 * (Fintype.card ι + 1) : ℕ) : Cardinal) := by
  let : FaithfulSMul R (MvPolynomial (Bool × ι) R) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (C_injective _ _)
  rw [← trdeg_add_eq k R (A := MvPolynomial (Bool × ι) R),
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, hR]
  simp [Cardinal.mk_fintype, Fintype.card_prod, Nat.mul_add, Nat.cast_add, add_comm]

private theorem incidence_trdeg (A : TaylorIdeal) (hA : A.IsPrime) (hd : dimension A = 2) :
    trdeg GeoField (IncidenceRing A) =
      ((2 * (Fintype.card TaylorIndex + 1) : ℕ) : Cardinal) := by
  let : A.IsPrime := hA
  exact elimination_incidence_trdeg_of_variables GeoField (SurfaceRing A) TaylorIndex
    (surfaceRing_trdeg A hA hd)

private theorem elimination_parameter_trdeg_of_variables (k ι : Type) [Field k] [Fintype ι] :
    trdeg k (MvPolynomial (Bool × Option ι) k) =
      ((2 * (Fintype.card ι + 1) : ℕ) : Cardinal) := by
  simp [Cardinal.mk_fintype, Fintype.card_prod]

/-- For a dominant map here, the two dimension counts force transcendence
degree zero over the parameter ring. Nondominance is also allowed in the
elimination argument, since it already supplies a polynomial in the kernel. -/
private theorem incidence_isAlgebraic (A : TaylorIdeal) (hA : A.IsPrime) (hd : dimension A = 2)
    (hinj : Function.Injective (parameterMap A)) :
    letI := (parameterMap A).toRingHom.toAlgebra
    Algebra.IsAlgebraic SectionPolynomial (IncidenceRing A) := by
  let : A.IsPrime := hA
  let P := SectionPolynomial
  let B := IncidenceRing A
  let : Algebra P B := (parameterMap A).toRingHom.toAlgebra
  change Algebra.IsAlgebraic P B
  let : IsScalarTower GeoField P B :=
    .of_algebraMap_eq (fun x => ((parameterMap A).commutes x).symm)
  let : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective P B).mpr hinj
  let n := 2 * (Fintype.card TaylorIndex + 1)
  have hP : trdeg GeoField P = (n : Cardinal) :=
    elimination_parameter_trdeg_of_variables GeoField TaylorIndex
  have hadd := trdeg_add_eq GeoField P (A := B)
  rw [hP, incidence_trdeg A hA hd] at hadd
  change (n : Cardinal) + trdeg P B = (n : Cardinal) at hadd
  have hz : trdeg P B = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hadd with hc | he
    · exact (Cardinal.natCast_lt_aleph0.not_ge ((le_max_left _ _).trans hc)).elim
    · exact he
  exact (trdeg_eq_zero_iff (R := P) (A := B)).mp hz

private theorem exists_nonzero_mem_span_of_isAlgebraic {P B : Type} [CommRing P]
    [CommRing B] [IsDomain B] [Algebra P B] {d : B} (hd : d ≠ 0)
    (h : IsAlgebraic P d) : ∃ f : P, f ≠ 0 ∧ algebraMap P B f ∈ Ideal.span {d} := by
  obtain ⟨p, hp, hp0⟩ := h
  obtain ⟨q, hq, hn⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  rw [map_zero, sub_zero] at hq hn
  have hq0 : Polynomial.aeval d q = 0 := by
    rw [hq, map_mul, map_pow, Polynomial.aeval_X] at hp0
    exact (mul_eq_zero.mp hp0).resolve_left (pow_ne_zero _ hd)
  refine ⟨q.coeff 0, mt Polynomial.X_dvd_iff.mpr hn, Ideal.mem_span_singleton.mpr ?_⟩
  refine ⟨-Polynomial.aeval d q.divX, ?_⟩
  have hh := congrArg (Polynomial.aeval d) (Polynomial.X_mul_divX_add q)
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hq0] at hh
  rw [mul_neg]
  exact eq_neg_of_add_eq_zero_right hh

/-- Every nonzero principal equation on the incidence scheme has a nonzero
eliminant in the parameter ring. It can be chosen to lie in the principal
ideal after pullback, so nonvanishing makes the equation's value a unit. -/
theorem exists_parameter_multiple (A : TaylorIdeal) (hA : A.IsPrime) (hd : dimension A = 2)
    (d : IncidenceRing A) (hd0 : d ≠ 0) :
    ∃ f : SectionPolynomial, f ≠ 0 ∧ parameterMap A f ∈ Ideal.span {d} := by
  let : A.IsPrime := hA
  by_cases hinj : Function.Injective (parameterMap A)
  · let : Algebra SectionPolynomial (IncidenceRing A) := (parameterMap A).toRingHom.toAlgebra
    let := incidence_isAlgebraic A hA hd hinj
    exact exists_nonzero_mem_span_of_isAlgebraic hd0 (Algebra.IsAlgebraic.isAlgebraic d)
  · rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨f, hf, hf0⟩ := hinj
    exact ⟨f, hf0, hf.symm ▸ (Ideal.span {d}).zero_mem⟩

end

end K1_13_7_1_2_2_2
end PackSource_K1_13_7_1_2_2_2Elimination

section PackSource_K1_13_7_1_2_2_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace K1_13_7_1_2_2_1_2

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2 K1_13_7_1_2_2_1
open scoped TensorProduct

noncomputable section

private def quotientBaseChange (R S σ : Type) [CommRing R] [CommRing S] [Algebra R S]
    (J : Ideal (MvPolynomial σ R)) :
    S ⊗[R] (MvPolynomial σ R ⧸ J) ≃ₐ[S]
      MvPolynomial σ S ⧸ J.map (MvPolynomial.map (algebraMap R S)) := by
  let e : S ⊗[R] MvPolynomial σ R ≃ₐ[S] MvPolynomial σ S :=
    MvPolynomial.algebraTensorAlgEquiv R S
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom =
      MvPolynomial.map (σ := σ) (algebraMap R S) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[R] p) = _
    simpa only [e, one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul R S 1 p
  refine (Algebra.TensorProduct.tensorQuotientEquiv S (MvPolynomial σ R) S J).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change J.map (MvPolynomial.map (algebraMap R S)) =
    (J.map (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom).map e.toRingHom
  rw [Ideal.map_map, he]

/-- A spanning relation after module localization holds before localization after
multiplication by an element of the submonoid. -/
private theorem exists_smul_mem_span {R K M N ι : Type} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module K N] [IsScalarTower R K N] (S : Submonoid R) [IsLocalization S K]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (v : ι → M) (x : M)
    (hx : f x ∈ Submodule.span K (Set.range (f ∘ v))) :
    ∃ s : S, (s : R) • x ∈ Submodule.span R (Set.range v) := by
  obtain ⟨a, ha⟩ := multiple_mem_span_of_mem_localization_span S K _ _ hx
  rw [Set.range_comp, ← Submodule.map_span] at ha
  obtain ⟨z, hz, he⟩ := ha
  change f z = (a : R) • f x at he
  rw [← f.map_smul] at he
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists S f).mp he.symm
  refine ⟨t * a, ?_⟩
  change ((t : R) * (a : R)) • x ∈ _
  rw [mul_smul, show (t : R) • ((a : R) • x) = (t : R) • z from ht]
  exact (Submodule.span R (Set.range v)).smul_mem _ hz

/-- Lift a generic basis of a polynomial quotient on one principal open.
The relations to clear express the unit and each coordinate times each
basis element in the span of the lifted vectors. -/
private theorem exists_basis_away (R σ : Type) [CommRing R] [IsDomain R] [Fintype σ]
    (J : Ideal (MvPolynomial σ R)) (n : ℕ)
    (b : Module.Basis (Fin n) (FractionRing R)
      (FractionRing R ⊗[R] (MvPolynomial σ R ⧸ J))) :
    ∃ d : R, d ≠ 0 ∧
      Nonempty (Module.Basis (Fin n) (Localization.Away d)
        (Localization.Away d ⊗[R] (MvPolynomial σ R ⧸ J))) := by
  classical
  let K := FractionRing R
  let S := nonZeroDivisors R
  let B := MvPolynomial σ R ⧸ J
  change Module.Basis (Fin n) K (K ⊗[R] B) at b
  let f : B →ₐ[R] K ⊗[R] B := Algebra.TensorProduct.includeRight
  let : IsScalarTower R K (K ⊗[R] B) := TensorProduct.isScalarTower_left
  let : IsLocalizedModule S f.toLinearMap := by
    change IsLocalizedModule S (TensorProduct.mk R K B 1)
    infer_instance
  choose t ht using fun i => IsLocalizedModule.surj S f.toLinearMap (b i)
  let v : Fin n → B := fun i => (t i).1
  let b' := b.isUnitSMul (fun i => IsLocalization.map_units K (t i).2)
  have hv (i : Fin n) : b' i = f (v i) := by
    rw [Module.Basis.isUnitSMul_apply]
    exact (algebraMap_smul K ((t i).2 : R) (b i)).trans (ht i)
  have hrange : Set.range (f.toLinearMap ∘ v) = Set.range b' := by
    congr 1
    funext i
    exact (hv i).symm
  let x : σ → B := fun i => Ideal.Quotient.mk J (MvPolynomial.X i)
  let a : Unit ⊕ (σ × Fin n) → B :=
    Sum.elim (fun _ => 1) fun ij => v ij.2 * x ij.1
  have hclear (j : Unit ⊕ (σ × Fin n)) :
      ∃ s : S, (s : R) • a j ∈ Submodule.span R (Set.range v) := by
    apply exists_smul_mem_span (K := K) S f.toLinearMap
    rw [hrange, b'.span_eq]
    trivial
  choose s hs using hclear
  let d : R := ∏ j, (s j : R)
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun j _ => mem_nonZeroDivisors_iff_ne_zero.mp (s j).property)
  let L := Localization.Away d
  let D := L ⊗[R] B
  let : IsScalarTower R L D := TensorProduct.isScalarTower_left
  let g : B →ₐ[R] D := Algebra.TensorProduct.includeRight
  let P : Submodule L D := Submodule.span L (Set.range (g ∘ v))
  have hgen (z : B) (hz : z ∈ Submodule.span R (Set.range v)) : g z ∈ P := by
    have hP : Submodule.span R (Set.range v) ≤ (P.restrictScalars R).comap g.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    exact hP hz
  have ha (j : Unit ⊕ (σ × Fin n)) : g (a j) ∈ P := by
    have hunit : IsUnit (algebraMap R L (s j : R)) :=
      IsLocalization.Away.isUnit_of_dvd d
        (Finset.dvd_prod_of_mem (fun i => (s i : R)) (Finset.mem_univ j))
    apply (P.smul_mem_iff_of_isUnit hunit).mp
    simpa only [map_smul, algebraMap_smul L] using hgen _ (hs j)
  have hmul (i : σ) : P ≤ P.comap (LinearMap.mulRight L (g (x i))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change g (v j) * g (x i) ∈ P
    rw [← map_mul]
    exact ha (Sum.inr (i, j))
  have hone : (1 : D) ∈ P := by
    have h := ha (Sum.inl ())
    change (1 : D) ∈ P at h
    exact h
  have hall (z : B) : g z ∈ P := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C r =>
      change g (algebraMap R B r) ∈ P
      rw [g.commutes, IsScalarTower.algebraMap_apply R L D, Algebra.algebraMap_eq_smul_one]
      exact P.smul_mem _ hone
    | add p q hp hq =>
      rw [map_add, map_add]
      exact P.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul]
      exact hmul i hp
  have hspan : P = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨⟨y, u⟩, hu⟩ :=
      IsLocalizedModule.surj (Submonoid.powers d) (TensorProduct.mk R L B 1) z
    apply (P.smul_mem_iff_of_isUnit (IsLocalization.map_units L u)).mp
    change (u : R) • z = g y at hu
    rw [algebraMap_smul L, hu]
    exact hall y
  have hle : Submonoid.powers d ≤ S :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hd)
  let : Algebra L K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe L K _ _ hle
  let : IsScalarTower R L K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le L K _ _ hle
  let : IsScalarTower L K (K ⊗[R] B) := TensorProduct.isScalarTower_left
  have hinj : Function.Injective (algebraMap L K) := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers d) _).mpr
    intro r u
    rw [← IsScalarTower.algebraMap_apply R L K, ← IsScalarTower.algebraMap_apply R L K]
    rw [(IsLocalization.injective L hle).eq_iff, (IsFractionRing.injective R K).eq_iff]
  let gK : D →ₗ[L] K ⊗[R] B :=
    TensorProduct.AlgebraTensorModule.map (Algebra.linearMap L K) (LinearMap.id : B →ₗ[R] B)
  have hcomp : gK ∘ (g ∘ v) = b' := by
    funext i
    rw [hv i]
    change (algebraMap L K 1 ⊗ₜ[R] v i) = (1 ⊗ₜ[R] v i)
    rw [map_one]
  have hli : LinearIndependent L (g ∘ v) := by
    apply LinearIndependent.of_comp gK
    rw [hcomp]
    apply b'.linearIndependent.restrict_scalars
    simpa only [Algebra.smul_def, mul_one] using hinj
  exact ⟨d, hd, ⟨Module.Basis.mk hli hspan.ge⟩⟩

/-- A finite generic section quotient has constant dimension on a principal open. -/
theorem proof : K1_13_7_1_2_2_1.c2 := by
  intro J hfinite
  let R := SectionPolynomial
  let K := SectionField
  let B := UniversalRing ⧸ J
  let G := GenericRing ⧸ genericIdeal J
  let n := Module.finrank K G
  let : Module.Finite K G := hfinite
  let b := (Module.finBasis K G).map (quotientBaseChange R K TaylorIndex J).symm.toLinearEquiv
  obtain ⟨d, hd, ⟨b'⟩⟩ := exists_basis_away R TaylorIndex J n b
  refine ⟨d, hd, fun p hp => ?_⟩
  let L := Localization.Away d
  let E := GeoField
  let ev : R →+* E := MvPolynomial.eval p
  let : Algebra R E := ev.toAlgebra
  let hu : IsUnit (ev d) := isUnit_iff_ne_zero.mpr hp
  let g : L →+* E := IsLocalization.Away.lift d hu
  let : Algebra L E := g.toAlgebra
  let : IsScalarTower R L E :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp d hu).symm
  let e := (Algebra.TensorProduct.cancelBaseChange R L E E B).trans
    (quotientBaseChange R E TaylorIndex J)
  let basis : Module.Basis (Fin n) E (TaylorRing ⧸ specializedIdeal J p) :=
    (b'.baseChange E).map e.toLinearEquiv
  refine ⟨Module.Finite.of_basis basis, ?_⟩
  change Module.finrank E (TaylorRing ⧸ specializedIdeal J p) = n
  rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]

end

end K1_13_7_1_2_2_1_2
end PackSource_K1_13_7_1_2_2_1_2Proof

section PackSource_K1_13_7_1_2_2_1_1Algebra
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 650000

namespace K1_13_7_1_2_2_1_1

noncomputable section

open MvPolynomial
open scoped TensorProduct nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Any polynomial killed by a linear combination with indeterminate
coefficients is killed by a power of each separate coefficient. -/
private theorem polynomial_torsion {A ι : Type*} [CommRing A] [Fintype ι]
    (a : ι → A) (j : ι) (q : MvPolynomial ι A)
    (hq : (∑ i, C (a i) * MvPolynomial.X i) * q = 0) :
    ∃ n : ℕ, C (a j) ^ n * q = 0 := by
  classical
  let L := Localization.Away (a j)
  let f : MvPolynomial ι A →+* MvPolynomial ι L := MvPolynomial.map (algebraMap A L)
  let e := (renameEquiv L (Equiv.optionSubtypeNe j).symm).trans
    (optionEquivLeft L {i : ι // i ≠ j})
  let F : MvPolynomial ι A →+* Polynomial (MvPolynomial {i : ι // i ≠ j} L) :=
    e.toRingHom.comp f
  have hcoeff (i : ι) :
      (F (C (a i) * MvPolynomial.X i)).coeff 1 = if i = j then C (algebraMap A L (a i)) else 0 := by
    by_cases hij : i = j
    · subst i
      simp [F, f, e, Polynomial.C_mul_X_eq_monomial]
    · simp [F, f, e, Equiv.optionSubtypeNe_symm_of_ne hij, hij]
  have hcoef : (F (∑ i, C (a i) * MvPolynomial.X i)).coeff 1 = C (algebraMap A L (a j)) := by
    rw [map_sum, Polynomial.finsetSum_coeff]
    simp only [hcoeff]
    simp
  have hunit : IsUnit (C (algebraMap A L (a j)) : MvPolynomial {i : ι // i ≠ j} L) :=
    IsUnit.map C (IsLocalization.Away.algebraMap_isUnit (a j))
  have hreg : F (∑ i, C (a i) * MvPolynomial.X i) ∈ nonZeroDivisors _ :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 1 (by rw [hcoef]; exact hunit.mem_nonZeroDivisors)
  have hz : F q = 0 := (mem_nonZeroDivisors_iff_left.mp hreg) _ (by
    simpa only [map_mul, map_zero] using congrArg F hq)
  have hf : f q = 0 := e.injective (by simpa [F] using hz)
  have hloc : IsLocalization (Submonoid.powers (C (σ := ι) (a j))) (MvPolynomial ι L) := by
    rw [← Submonoid.map_powers]
    infer_instance
  have hmap : algebraMap (MvPolynomial ι A) (MvPolynomial ι L) q = 0 := hf
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (C (σ := ι) (a j)))
    (MvPolynomial ι L) q).mp hmap
  obtain ⟨n, hn⟩ := m.property
  exact ⟨n, by simpa only [hn] using hm⟩

private theorem flat_colon_le {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (I : Ideal R) (u v : R) (h : I.colon {u} ≤ I.colon {v}) :
    (I.map (algebraMap R S)).colon {algebraMap R S u} ≤
      (I.map (algebraMap R S)).colon {algebraMap R S v} := by
  let J := I.map (algebraMap R S)
  let e : S ⊗[R] (R ⧸ I) ≃ₐ[S] S ⧸ J :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
  let m (a : R) : (R ⧸ I) →ₗ[R] (R ⧸ I) :=
    LinearMap.mulLeft R (Ideal.Quotient.mk I a)
  have hker : LinearMap.ker (m u) ≤ LinearMap.ker (m v) := by
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa [m, LinearMap.mem_ker, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Submodule.mem_colon_singleton, smul_eq_mul, mul_comm _ p] using
      (h (show p ∈ I.colon {u} by
        simpa [m, LinearMap.mem_ker, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
          Submodule.mem_colon_singleton, smul_eq_mul, mul_comm _ p] using hx) :
        p ∈ I.colon {v})
  have hbase : LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S (m u)) ≤
      LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S (m v)) := by
    rw [Module.Flat.ker_lTensor_eq, Module.Flat.ker_lTensor_eq]
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨TensorProduct.AlgebraTensorModule.lTensor S S (Submodule.inclusion hker) z, ?_⟩
    induction z using TensorProduct.inductionOn <;>
      simp_all [TensorProduct.AlgebraTensorModule.lTensor_tmul]
  have he (a : R) (z : S ⊗[R] (R ⧸ I)) :
      e (TensorProduct.AlgebraTensorModule.lTensor S S (m a) z) =
        Ideal.Quotient.mk J (algebraMap R S a) * e z := by
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, m, LinearMap.mulLeft_apply,
        ← map_mul, e]
      change Ideal.Quotient.mk J ((a * p) • s) =
        Ideal.Quotient.mk J (algebraMap R S a) * Ideal.Quotient.mk J (p • s)
      rw [← map_mul]
      simp only [Algebra.smul_def, map_mul, mul_assoc]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
  intro p hp
  rw [Submodule.mem_colon_singleton, smul_eq_mul, ← Ideal.Quotient.eq_zero_iff_mem,
    map_mul] at hp ⊢
  let z := e.symm (Ideal.Quotient.mk J p)
  have hz : e z = Ideal.Quotient.mk J p := e.apply_symm_apply _
  have hu : z ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S (m u)) := by
    apply LinearMap.mem_ker.mpr
    apply e.injective
    rw [he, hz, map_zero]
    exact (mul_comm _ _).trans hp
  have hv := congrArg e (LinearMap.mem_ker.mp (hbase hu))
  rw [he, hz, map_zero, mul_comm] at hv
  exact hv

private theorem map_comp {R S T σ : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (MvPolynomial.map (σ := σ) g).comp (MvPolynomial.map f) = MvPolynomial.map (g.comp f) :=
  RingHom.ext (MvPolynomial.map_map f g)

private theorem generic_coefficients_flat {k E ι : Type} [Field k] [Field E]
    [Algebra k E] {t : ι → E} (ht : AlgebraicIndependent k t) :
    (aeval t : MvPolynomial ι k →ₐ[k] E).toRingHom.Flat := by
  let P := MvPolynomial ι k
  let F := FractionRing P
  let f : P →+* E := (aeval t).toRingHom
  have hf : Function.Injective f := ht
  let g : F →+* E := IsFractionRing.lift (K := F) hf
  have hg : g.comp (algebraMap P F) = f := by
    apply RingHom.ext
    intro x
    change g (algebraMap P F x) = f x
    exact IsFractionRing.lift_algebraMap (K := F) hf x
  change f.Flat
  rw [← hg]
  exact (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors P))).comp
    (RingHom.Flat.of_isField (Field.toIsField F) g)

private theorem colon_has_uniform_power {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (u v : R) (h : ∀ q, u * q ∈ I → ∃ n : ℕ, v ^ n * q ∈ I) :
    ∃ n : ℕ, I.colon {u} ≤ I.colon {v ^ n} := by
  classical
  let J := I.colon {u}
  obtain ⟨s, hs⟩ := J.fg_of_isNoetherianRing
  have hx (a : s) : u * a.1 ∈ I := by
    have hm : (a : R) ∈ J := hs ▸ Submodule.subset_span a.property
    simpa only [J, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm (a : R) u] using hm
  choose n hn using fun a : s => h a (hx a)
  refine ⟨s.attach.sup n, ?_⟩
  change J ≤ I.colon {v ^ s.attach.sup n}
  rw [← hs]
  apply Submodule.span_le.mpr
  intro a ha
  let b : s := ⟨a, ha⟩
  have hb : n b ≤ s.attach.sup n := Finset.le_sup (s.mem_attach b)
  apply Submodule.mem_colon_singleton.mpr
  rw [smul_eq_mul, mul_comm a, ← Nat.sub_add_cancel hb, pow_add, mul_assoc]
  exact I.mul_mem_left _ (hn b)

/-- A relation in the generic cut quotient is killed by a power of each
of the polynomials whose coefficients vary independently. -/
theorem generic_torsion {k E σ ι : Type} [Field k] [Field E] [Algebra k E]
    [Finite σ] [Fintype ι] [Finite ι] {t : ι → E} (ht : AlgebraicIndependent k t)
    (I : Ideal (MvPolynomial σ k)) (a : ι → MvPolynomial σ k)
    (j : ι) (q : MvPolynomial σ E)
    (hq : (∑ i, C (t i) * MvPolynomial.map (algebraMap k E) (a i)) * q ∈
      I.map (MvPolynomial.map (algebraMap k E))) :
    ∃ n : ℕ, (MvPolynomial.map (algebraMap k E) (a j)) ^ n * q ∈
      I.map (MvPolynomial.map (algebraMap k E)) := by
  let P := MvPolynomial ι k
  let R := MvPolynomial σ k
  let U := MvPolynomial σ P
  let i : R →+* U := MvPolynomial.map C
  let B := I.map i
  let u : U := ∑ l, C (MvPolynomial.X l) * i (a l)
  let F : U →+* MvPolynomial ι (R ⧸ I) :=
    (MvPolynomial.map (Ideal.Quotient.mk I)).comp (commAlgEquiv k σ ι).toRingHom
  have hi (p : R) : (commAlgEquiv k σ ι) (i p) = C p := by
    have h : (commAlgEquiv k σ ι).symm (C p) = i p := commAlgEquiv_C p
    rw [← h, AlgEquiv.apply_symm_apply]
  have hFi (p : R) : F (i p) = C (Ideal.Quotient.mk I p) := by
    change (MvPolynomial.map (Ideal.Quotient.mk I)) ((commAlgEquiv k σ ι) (i p)) = _
    rw [hi, map_C]
  have hFX (l : ι) : F (C (MvPolynomial.X l)) = MvPolynomial.X l := by
    change (MvPolynomial.map (Ideal.Quotient.mk I))
      ((commAlgEquiv k σ ι) (C (MvPolynomial.X l))) = _
    rw [commAlgEquiv_C_X, map_X]
  have hFu : F u = ∑ l, C (Ideal.Quotient.mk I (a l)) * MvPolynomial.X l := by
    simp only [u, map_sum, map_mul, hFi, hFX, mul_comm]
  have hF : RingHom.ker F = B := by
    let e := commAlgEquiv k σ ι
    rw [show F = (MvPolynomial.map (Ideal.Quotient.mk I)).comp e.toRingHom from rfl,
      ← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker]
    change (I.map C).comap e.toRingHom = I.map i
    have hC : C = e.toRingHom.comp i := RingHom.ext (fun p => (hi p).symm)
    rw [hC, ← Ideal.map_map]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  obtain ⟨n, hn⟩ := colon_has_uniform_power B u (i (a j)) (by
    intro p hp
    have hzero : F (u * p) = 0 := RingHom.mem_ker.mp (hF.symm ▸ hp)
    rw [map_mul, hFu] at hzero
    obtain ⟨n, hn⟩ := polynomial_torsion (fun l => Ideal.Quotient.mk I (a l)) j (F p) hzero
    refine ⟨n, hF ▸ RingHom.mem_ker.mpr ?_⟩
    simpa only [map_mul, map_pow, hFi] using hn)
  let ev : P →+* E := (aeval t).toRingHom
  let f : U →+* MvPolynomial σ E := MvPolynomial.map ev
  let : Algebra P E := ev.toAlgebra
  have hf : f.Flat := RingHom.Flat.isStableUnderBaseChange P E U (MvPolynomial σ E)
    (generic_coefficients_flat ht)
  let : Algebra U (MvPolynomial σ E) := f.toAlgebra
  have : Module.Flat U (MvPolynomial σ E) := hf
  have hev : ev.comp (C : k →+* P) = algebraMap k E :=
    RingHom.ext (fun x => aeval_C t x)
  have hfi : f.comp i = MvPolynomial.map (algebraMap k E) := by
    rw [show f = MvPolynomial.map ev from rfl, show i = MvPolynomial.map C from rfl,
      map_comp, hev]
  have hB : B.map f = I.map (MvPolynomial.map (algebraMap k E)) := by
    rw [show B = I.map i from rfl, Ideal.map_map, hfi]
  have hu : f u = ∑ l, C (t l) * MvPolynomial.map (algebraMap k E) (a l) := by
    simp only [u, map_sum, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show f (i (a l)) = (f.comp i) (a l) from rfl, hfi]
    change MvPolynomial.map ev (C (MvPolynomial.X l)) * _ = _
    rw [map_C, show ev (MvPolynomial.X l) = t l from aeval_X t l]
  have h := flat_colon_le (R := U) (S := MvPolynomial σ E) B u (i (a j) ^ n) hn
  change (B.map f).colon {f u} ≤ (B.map f).colon {f (i (a j) ^ n)} at h
  rw [hB, hu, map_pow, show f (i (a j)) = (f.comp i) (a j) from rfl, hfi] at h
  refine ⟨n, ?_⟩
  have hmem : q ∈ (I.map (MvPolynomial.map (algebraMap k E))).colon
      {∑ l, C (t l) * MvPolynomial.map (algebraMap k E) (a l)} := by
    apply Submodule.mem_colon_singleton.mpr
    rw [smul_eq_mul, mul_comm]
    exact hq
  simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm q] using h hmem

end

end K1_13_7_1_2_2_1_1
end PackSource_K1_13_7_1_2_2_1_1Algebra

section PackSource_K1_13_7_1_2_2_2Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_2_2

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2

/-- At the generic point of a surface, two ambient coordinate differentials
give a basis of the relative differentials over its function field. -/
def c1 : Prop :=
  ∀ A : TaylorIdeal, A.IsPrime → dimension A = 2 →
    ∃ (i : Fin 2 → TaylorIndex)
      (b : Module.Basis (Fin 2) (SurfaceField A) Ω[SurfaceField A⁄GeoField]),
      ∀ j, b j = KaehlerDifferential.D GeoField (SurfaceField A)
        (algebraMap (SurfaceRing A) (SurfaceField A) (coordinate A (i j)))

/-- On an integral surface with such a generic basis, independent rows of
linear coefficients give a generically unramified incidence projection. -/
def c2 : Prop :=
  ∀ (A : TaylorIdeal), A.IsPrime →
    ∀ (i : Fin 2 → TaylorIndex)
      (b : Module.Basis (Fin 2) (SurfaceField A) Ω[SurfaceField A⁄GeoField]),
      (∀ j, b j = KaehlerDifferential.D GeoField (SurfaceField A)
        (algebraMap (SurfaceRing A) (SurfaceField A) (coordinate A (i j)))) →
      (genericParameterMap A).FormallyUnramified

theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_1_2_2.c2 := by
  intro A hA hd
  obtain ⟨i, b, hb⟩ := h1 A hA hd
  obtain ⟨d, hd0, hu⟩ := exists_unramified_open A hA (h2 A hA i b hb)
  obtain ⟨f, hf0, hf⟩ := exists_parameter_multiple A hA hd d hd0
  exact ⟨f, hf0, fun p hp => radical_of_unramified_open A p hu hf hp⟩

end

end K1_13_7_1_2_2_2
end PackSource_K1_13_7_1_2_2_2Split

section PackSource_K1_13_7_1_2_2_2_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_2_2_1

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2_2
open KaehlerDifferential nonZeroDivisors

/-- Passage from the polynomial ring to the separating rational function
field and then to the full field preserves differentials by base change. -/
private def separatingDifferentialBasis {k E : Type} [Field k] [Field E] [Algebra k E]
    {ι : Type} {x : ι → E} (hx : AlgebraicIndependent k x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) E) :
    Module.Basis ι E Ω[E⁄k] := by
  let P := MvPolynomial ι k
  let T := IntermediateField.adjoin k (Set.range x)
  let e : FractionRing P ≃ₐ[k] T := hx.aevalEquivField
  let f : P →+* T := e.toRingHom.comp (algebraMap P (FractionRing P))
  letI : Algebra P T := f.toAlgebra
  letI : Algebra P E := ((algebraMap T E).comp f).toAlgebra
  letI : IsScalarTower P T E := .of_algebraMap_eq' rfl
  letI : IsScalarTower k P E := .of_algebraMap_eq fun a => by
    change algebraMap k E a = algebraMap T E (e (algebraMap P (FractionRing P) (algebraMap k P a)))
    rw [← IsScalarTower.algebraMap_apply k P (FractionRing P), e.commutes,
      ← IsScalarTower.algebraMap_apply k T E]
  let eP : FractionRing P ≃ₐ[P] T :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : IsFractionRing P T := IsFractionRing.of_algEquiv eP
  letI : Algebra.FormallyEtale P T := .of_isLocalization (nonZeroDivisors P)
  letI : Algebra.IsSeparable T E := hsep
  letI : Algebra.FormallyEtale T E := .of_isSeparable T E
  letI : Algebra.FormallyEtale P E := .comp P T E
  exact ((mvPolynomialBasis k ι).baseChange E).map (tensorKaehlerEquivOfFormallyEtale k P E)

/-- The differentials of the ambient variables span after quotienting and
passing to the fraction ring. -/
private theorem span_coordinates (A : TaylorIdeal) :
    Submodule.span (SurfaceField A) (Set.range (fun i : TaylorIndex =>
      D GeoField (SurfaceField A)
        (algebraMap (SurfaceRing A) (SurfaceField A) (coordinate A i)))) = ⊤ := by
  let R := SurfaceRing A
  let K := SurfaceField A
  let f : TaylorRing →ₐ[GeoField] K :=
    (IsScalarTower.toAlgHom GeoField R K).comp (Ideal.Quotient.mkₐ GeoField A)
  let v : TaylorIndex → Ω[K⁄GeoField] := fun i => D GeoField K (f (MvPolynomial.X i))
  let W := Submodule.span K (Set.range v)
  change W = ⊤
  have hpoly (p : TaylorRing) : D GeoField K (f p) ∈ W := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      change D GeoField K (f (algebraMap GeoField TaylorRing a)) ∈ W
      rw [f.commutes, Derivation.map_algebraMap]
      exact W.zero_mem
    | add p q hp hq =>
      rw [map_add, map_add]
      exact W.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, Derivation.leibniz]
      exact W.add_mem (W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)) (W.smul_mem _ hp)
  apply top_unique
  rw [← span_range_map_derivation_of_isLocalization GeoField R K (nonZeroDivisors R)]
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [Function.comp_apply, map_D]
  exact hpoly p

theorem proof : K1_13_7_1_2_2_2.c1 := by
  classical
  intro A hA hd
  let : A.IsPrime := hA
  let R := SurfaceRing A
  let K := SurfaceField A
  let : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  let : Algebra.EssFiniteType GeoField K := .comp GeoField R K
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField GeoField K
  have hsCard : Fintype.card s = 2 := by
    apply Nat.cast_injective (R := Cardinal)
    exact (Cardinal.mk_fintype s).symm.trans
      (hs.cardinalMk_eq_trdeg.trans (surfaceField_trdeg A hA hd))
  have hsep' : Algebra.IsSeparable
      (IntermediateField.adjoin GeoField (Set.range ((↑) : s → K))) K := by
    rw [show Set.range ((↑) : s → K) = (s : Set K) from Subtype.range_coe]
    exact hsep
  let bSep := separatingDifferentialBasis hs.1 hsep'
  let v : TaylorIndex → Ω[K⁄GeoField] := fun i =>
    D GeoField K (algebraMap R K (coordinate A i))
  obtain ⟨κ, a, _, ha, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K Ω[K⁄GeoField] :=
    Module.Basis.mk hli (ha.trans (span_coordinates A)).ge
  let e : κ ≃ Fin 2 := (b.indexEquiv bSep).trans (Fintype.equivFinOfCardEq hsCard)
  refine ⟨a ∘ e.symm, b.reindex e, fun j => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  rfl

end

end K1_13_7_1_2_2_2_1
end PackSource_K1_13_7_1_2_2_2_1Proof

section PackSource_K1_13_7_1_2_2_2_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_13_7_1_2_2_2_2

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 K1_13_7_1_2_2 K1_13_7_1_2_2_2
open MvPolynomial

/-- Evaluating each row at the covector for its selected coordinate sends
its two entries to the corresponding row of the identity. -/
private theorem polynomialDet_ne_zero {ι K : Type*} [Fintype ι] [Field K]
    (i : Fin 2 → ι) (q : ι → Fin 2 → K)
    (hq : ∀ s t, q (i s) t = if s = t then 1 else 0) :
    let entry : Bool → Fin 2 → MvPolynomial (Bool × ι) K :=
      fun r s => ∑ t, MvPolynomial.X (r, t) * C (q t s)
    entry false 0 * entry true 1 - entry false 1 * entry true 0 ≠ 0 := by
  classical
  intro entry
  let selected (r : Bool) : Fin 2 := if r then 1 else 0
  let value (v : Bool × ι) : K := if v.2 = i (selected v.1) then 1 else 0
  have heval (r : Bool) (s : Fin 2) : eval value (entry r s) = q (i (selected r)) s := by
    change eval value (∑ t, MvPolynomial.X (r, t) * C (q t s)) = _
    simp only [map_sum, map_mul, eval_X, eval_C]
    rw [Finset.sum_eq_single (i (selected r))]
    · simp [value]
    · intro t _ ht
      simp [value, ht]
    · simp
  intro hz
  have he := congrArg (eval value) hz
  simp [heval, hq, selected] at he

/-- Coefficient extension to the fraction field preserves the independence
of the polynomial variables in the incidence function field. -/
private theorem injective_generic_eval {ι R K L : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra (MvPolynomial ι R) L] [IsFractionRing (MvPolynomial ι R) L]
    [Algebra K L]
    (hcoef : ∀ r : R, algebraMap K L (algebraMap R K r) = algebraMap (MvPolynomial ι R) L (C r)) :
    Function.Injective (aeval (R := K) fun t : ι =>
      algebraMap (MvPolynomial ι R) L (MvPolynomial.X t)) := by
  let B := MvPolynomial ι R
  let B' := MvPolynomial ι K
  let L' := FractionRing B'
  let j : B →+* B' := MvPolynomial.map (algebraMap R K)
  let j_inj : Function.Injective j :=
    MvPolynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  let e : L →+* L' := IsFractionRing.map j_inj
  have he (p : B) : e (algebraMap B L p) = algebraMap B' L' (j p) :=
    IsLocalization.map_eq _ p
  have hK : e.comp (algebraMap K L) = (algebraMap B' L').comp C := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    change e (algebraMap K L (algebraMap R K r)) = algebraMap B' L' (C (algebraMap R K r))
    rw [hcoef, he]
    exact congrArg (algebraMap B' L') (MvPolynomial.map_C (σ := ι) (algebraMap R K) r)
  let f : B' →ₐ[K] L := aeval (fun t : ι => algebraMap B L (MvPolynomial.X t))
  have hf : e.comp f.toRingHom = algebraMap B' L' := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change e (f (C r)) = algebraMap B' L' (C r)
      rw [show f (C r) = algebraMap K L r from aeval_C _ _]
      exact RingHom.congr_fun hK r
    · intro t
      change e (f (MvPolynomial.X t)) = algebraMap B' L' (MvPolynomial.X t)
      rw [show f (MvPolynomial.X t) = algebraMap B L (MvPolynomial.X t) from aeval_X _ _, he]
      exact congrArg (algebraMap B' L') (MvPolynomial.map_X (σ := ι) (algebraMap R K) t)
  intro p q hpq
  apply IsFractionRing.injective B' L'
  rw [← hf]
  exact congrArg e hpq

private theorem solve_two_rows {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (a b c d : F) (x y : M) (hdet : a * d - b * c ≠ 0)
    (h₀ : a • x + b • y = 0) (h₁ : c • x + d • y = 0) : x = 0 ∧ y = 0 := by
  constructor <;> apply (smul_eq_zero_iff_right hdet).mp
  · calc
      (a * d - b * c) • x = d • (a • x + b • y) - b • (c • x + d • y) := by
        simp only [sub_smul, smul_add, smul_smul, mul_comm d a, mul_comm d b]
        abel
      _ = 0 := by rw [h₀, h₁, smul_zero, smul_zero, sub_zero]
  · calc
      (a * d - b * c) • y = a • (c • x + d • y) - c • (a • x + b • y) := by
        simp only [sub_smul, smul_add, smul_smul, mul_comm c a, mul_comm c b]
        abel
      _ = 0 := by rw [h₀, h₁, smul_zero, smul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
/-- The two generic incidence equations kill the images of the surface
basis, and the linear parameter variables kill the remaining generators. -/
private theorem incidence_projection_unramified {ι k R P K L : Type*} [Fintype ι]
    [CommRing k] [CommRing R] [IsDomain R] [CommRing P] [Algebra k R] [Algebra k P]
    [Field K] [Algebra R K] [IsFractionRing R K] [Algebra k K] [IsScalarTower k R K]
    [Field L] [Algebra (MvPolynomial (Bool × ι) R) L] [IsFractionRing (MvPolynomial (Bool × ι) R) L]
    (parameter : P →ₐ[k] MvPolynomial (Bool × ι) R) (coord : ι → R)
    (linear : Bool → ι → P) (constant : Bool → P)
    (hlinear : ∀ r t, parameter (linear r t) = MvPolynomial.X (r, t))
    (hconstant : ∀ r, parameter (constant r) = -∑ t, MvPolynomial.X (r, t) * C (coord t))
    (i : Fin 2 → ι) (b : Module.Basis (Fin 2) K Ω[K⁄k])
    (hb : ∀ s, b s = KaehlerDifferential.D k K (algebraMap R K (coord (i s)))) :
    ((algebraMap (MvPolynomial (Bool × ι) R) L).comp parameter.toRingHom).FormallyUnramified := by
  classical
  let B := MvPolynomial (Bool × ι) R
  let : Algebra P L := ((algebraMap B L).comp parameter.toRingHom).toAlgebra
  change Algebra.FormallyUnramified P L
  let coef : R →+* L := (algebraMap B L).comp C
  have hcoef_inj : Function.Injective coef :=
    (IsFractionRing.injective B L).comp (C_injective _ _)
  let : Algebra K L := (IsFractionRing.lift hcoef_inj : K →+* L).toAlgebra
  have hcoef (r : R) : algebraMap K L (algebraMap R K r) = algebraMap B L (C r) :=
    IsFractionRing.lift_algebraMap hcoef_inj r
  let baseToL : k →+* L := (algebraMap K L).comp (algebraMap k K)
  let : Algebra k L := baseToL.toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower k P L := .of_algebraMap_eq fun c => by
    change algebraMap K L (algebraMap k K c) = algebraMap B L (parameter (algebraMap k P c))
    calc
      _ = algebraMap K L (algebraMap R K (algebraMap k R c)) :=
        congrArg (algebraMap K L) (IsScalarTower.algebraMap_apply k R K c)
      _ = algebraMap B L (C (algebraMap k R c)) := hcoef _
      _ = _ := congrArg (algebraMap B L) (parameter.commutes c).symm
  let D := KaehlerDifferential.D P L
  let liftD := KaehlerDifferential.map k P K L
  have hnatural (r : R) :
      liftD (KaehlerDifferential.D k K (algebraMap R K r)) =
        D (algebraMap B L (C r)) :=
    (KaehlerDifferential.map_D k P K L _).trans (congrArg D (hcoef r))
  let z (t : ι) : K := algebraMap R K (coord t)
  let x (r : Bool) (t : ι) : L := algebraMap B L (MvPolynomial.X (r, t))
  let q (t : ι) (s : Fin 2) : K := b.repr (KaehlerDifferential.D k K (z t)) s
  let v (s : Fin 2) := liftD (b s)
  let entry (r : Bool) (s : Fin 2) : L := ∑ t, x r t * algebraMap K L (q t s)
  have hvar (r : Bool) (t : ι) : D (algebraMap B L (MvPolynomial.X (r, t))) = 0 := by
    have h := D.map_algebraMap (linear r t)
    change D (algebraMap B L (parameter (linear r t))) = 0 at h
    rwa [hlinear] at h
  have hconst (r : Bool) : ∑ t, x r t • D (algebraMap B L (C (coord t))) = 0 := by
    have h := D.map_algebraMap (constant r)
    change D (algebraMap B L (parameter (constant r))) = 0 at h
    simpa only [hconstant, map_neg, map_sum, map_mul, Derivation.leibniz, hvar,
      smul_zero, add_zero, neg_eq_zero] using h
  have hcoord (t : ι) :
      D (algebraMap B L (C (coord t))) = ∑ s, algebraMap K L (q t s) • v s := by
    calc
      _ = liftD (KaehlerDifferential.D k K (z t)) := (hnatural (coord t)).symm
      _ = liftD (∑ s, q t s • b s) := congrArg liftD (b.sum_repr _).symm
      _ = _ := by simp only [map_sum, map_smul, IsScalarTower.algebraMap_smul, v]
  have hrow (r : Bool) : ∑ s, entry r s • v s = 0 := by
    calc
      _ = ∑ s, ∑ t, (x r t * algebraMap K L (q t s)) • v s := by
        simp only [entry, Finset.sum_smul]
      _ = ∑ t, ∑ s, (x r t * algebraMap K L (q t s)) • v s := Finset.sum_comm
      _ = 0 := by
        simpa only [hcoord, Finset.smul_sum, smul_smul] using hconst r
  have hq (s t : Fin 2) : q (i s) t = if s = t then 1 else 0 := by
    change b.repr (KaehlerDifferential.D k K (z (i s))) t = _
    rw [← hb s, b.repr_self_apply]
  let f : MvPolynomial (Bool × ι) K →ₐ[K] L := aeval (fun t => x t.1 t.2)
  have hf : Function.Injective f := injective_generic_eval hcoef
  let polyEntry (r : Bool) (s : Fin 2) : MvPolynomial (Bool × ι) K :=
    ∑ t, MvPolynomial.X (r, t) * C (q t s)
  have hfEntry (r : Bool) (s : Fin 2) : f (polyEntry r s) = entry r s := by
    simp only [polyEntry, entry, f, map_sum, map_mul, aeval_X, aeval_C]
  have hdet : entry false 0 * entry true 1 - entry false 1 * entry true 0 ≠ 0 := by
    have h := polynomialDet_ne_zero i q hq
    change polyEntry false 0 * polyEntry true 1 - polyEntry false 1 * polyEntry true 0 ≠ 0 at h
    intro hz
    apply h
    apply hf
    simpa only [map_sub, map_mul, map_zero, hfEntry] using hz
  have hv := solve_two_rows (entry false 0) (entry false 1) (entry true 0) (entry true 1)
    (v 0) (v 1) hdet (by simpa only [Fin.sum_univ_two] using hrow false)
    (by simpa only [Fin.sum_univ_two] using hrow true)
  have hLift : liftD = 0 := by
    apply b.ext
    intro s
    change v s = 0
    fin_cases s
    · exact hv.1
    · exact hv.2
  have hC (r : R) : D (algebraMap B L (C r)) = 0 := by
    rw [← hnatural r, hLift, LinearMap.zero_apply]
  have hpoly (p : B) : D (algebraMap B L p) = 0 := by
    induction p using MvPolynomial.induction_on with
    | C r => exact hC r
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
    | mul_X p t hp =>
        obtain ⟨r, t⟩ := t
        simp only [map_mul, Derivation.leibniz, hp, hvar, smul_zero, add_zero]
  have hall (y : L) : D y = 0 := by
    obtain ⟨⟨p, d⟩, he⟩ := IsLocalization.surj (nonZeroDivisors B) y
    have hd : algebraMap B L (d : B) ≠ 0 :=
      fun hz => nonZeroDivisors.ne_zero d.2 ((IsFractionRing.to_map_eq_zero_iff (K := L)).mp hz)
    have h := congrArg D he
    simp only [Derivation.leibniz, hpoly, smul_zero, zero_add] at h
    exact (smul_eq_zero_iff_right hd).mp h
  refine ⟨(subsingleton_iff_forall_eq 0).mpr ?_⟩
  suffices h : (⊤ : Submodule L Ω[L⁄P]) ≤ ⊥ by
    exact fun y => h (show y ∈ (⊤ : Submodule L Ω[L⁄P]) from trivial)
  rw [← KaehlerDifferential.span_range_derivation P L, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  exact hall y

/-- The incidence projection for the contract has the two generic rows. -/
theorem proof : K1_13_7_1_2_2_2.c2 := by
  intro A hA i b hb
  let : A.IsPrime := hA
  exact incidence_projection_unramified
    (ι := TaylorIndex) (k := GeoField) (R := SurfaceRing A) (P := SectionPolynomial)
    (K := SurfaceField A) (L := FractionRing (K1_13_7_1_2_2_2.IncidenceRing A))
    (parameterMap A) (coordinate A)
    (fun r t => MvPolynomial.X (r, some t)) (fun r => MvPolynomial.X (r, none))
    (fun r t => aeval_X _ (r, some t)) (fun r => aeval_X _ (r, none)) i b hb

end

end K1_13_7_1_2_2_2_2
end PackSource_K1_13_7_1_2_2_2_2Proof

section PackSource_K1_13_7_1_2_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_2_1

noncomputable section

open K1_13_6 K1_13_7_1 K1_13_7_1_2 MvPolynomial

private theorem source_dimension {f g : GeoJets} (hf : f ≠ 0) (hrel : IsRelPrime f g)
    {P : Ideal GeoJets} (hP : P ∈ (pairIdeal f g).minimalPrimes) :
    (affineHilbertPolynomial P).natDegree = 2 := by
  rw [pairIdeal, Ideal.span_insert] at hP
  let := hP.isPrime
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {f} ≤ P from le_sup_left.trans hP.le)
  let := hQ.isPrime
  have hgQ : g ∉ Q := by
    intro hg
    obtain ⟨y, hy, hgy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hQ hg
    exact hy (Ideal.mem_span_singleton.mpr
      (hrel.dvd_of_dvd_mul_left (Ideal.mem_span_singleton.mp hgy)))
  have hcut : P ∈ (Q ⊔ Ideal.span {g}).minimalPrimes :=
    ⟨⟨hP.isPrime, sup_le hQP (le_sup_right.trans hP.le)⟩, fun J hJ hJP ↦
      hP.2 ⟨hJ.1, sup_le (hQ.le.trans (le_sup_left.trans hJ.2))
        (le_sup_right.trans hJ.2)⟩ hJP⟩
  have hQdim := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hf hQ
  rw [Nat.card_fin] at hQdim
  have hPdim := principalCut_natDegree_affineHilbertPolynomial_add_one hgQ hcut
  omega

private abbrev ChartOpen (C : TaylorChart) (P : Ideal GeoJets) :=
  Localization.Away (Ideal.Quotient.mk P C.denom)

private def localize (C : TaylorChart) (P : Ideal GeoJets) : GeoJets →ₐ[GeoField] ChartOpen C P :=
  (IsScalarTower.toAlgHom GeoField (GeoJets ⧸ P) (ChartOpen C P)).comp
    (Ideal.Quotient.mkₐ GeoField P)

private def invDenom (C : TaylorChart) (P : Ideal GeoJets) : ChartOpen C P :=
  IsLocalization.Away.invSelf (Ideal.Quotient.mk P C.denom)

private theorem localize_denom_mul_inv (C : TaylorChart) (P : Ideal GeoJets) :
    localize C P C.denom * invDenom C P = 1 :=
  IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk P C.denom)

private def chartMap (C : TaylorChart) (P : Ideal GeoJets) :
    TaylorRing →ₐ[GeoField] ChartOpen C P :=
  aeval fun i ↦ localize C P (C.numerator i) * invDenom C P

private theorem chartMap_rename (C : TaylorChart) (P : Ideal GeoJets) (q : GeoJets) :
    chartMap C P (rename initialIndex q) = localize C P q := by
  have h : (chartMap C P).comp (rename initialIndex) = localize C P := by
    apply MvPolynomial.algHom_ext
    intro i
    change chartMap C P (rename initialIndex (MvPolynomial.X i)) =
      localize C P (MvPolynomial.X i)
    rw [rename_X, chartMap, aeval_X,
      show C.numerator (initialIndex i) = MvPolynomial.X i * C.denom from C.initial i,
      map_mul, mul_assoc, localize_denom_mul_inv, mul_one]
  exact DFunLike.congr_fun h q

section Evaluation

variable {C : TaylorChart} {P : Ideal GeoJets} {y : GeoPoint}

private def pointEval (hy : y ∈ zeroLocus GeoField P) : (GeoJets ⧸ P) →ₐ[GeoField] GeoField :=
  Ideal.Quotient.liftₐ P (aeval y) fun q hq ↦ hy q hq

private def openEval (hy : y ∈ zeroLocus GeoField P) (hD : eval y C.denom ≠ 0) :
    ChartOpen C P →ₐ[GeoField] GeoField :=
  IsLocalization.Away.liftAlgHom (f := pointEval hy) (Ideal.Quotient.mk P C.denom)
    (isUnit_iff_ne_zero.mpr hD)

private theorem openEval_localize (hy : y ∈ zeroLocus GeoField P)
    (hD : eval y C.denom ≠ 0) (q : GeoJets) :
    openEval hy hD (localize C P q) = eval y q :=
  IsLocalization.Away.lift_eq (g := (pointEval hy).toRingHom)
    (Ideal.Quotient.mk P C.denom) (isUnit_iff_ne_zero.mpr hD) (Ideal.Quotient.mk P q)

private theorem openEval_chartMap (hy : y ∈ zeroLocus GeoField P)
    (hD : eval y C.denom ≠ 0) (q : TaylorRing) :
    openEval hy hD (chartMap C P q) = eval (chartPoint C y) q := by
  have hu := congrArg (openEval hy hD) (localize_denom_mul_inv C P)
  rw [map_mul, openEval_localize, map_one] at hu
  have hi : openEval hy hD (invDenom C P) = (eval y C.denom)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hD).mpr
    exact (mul_comm _ _).trans hu
  have h : (openEval hy hD).comp (chartMap C P) = aeval (chartPoint C y) := by
    apply MvPolynomial.algHom_ext
    intro i
    change openEval hy hD (chartMap C P (MvPolynomial.X i)) =
      aeval (chartPoint C y) (MvPolynomial.X i)
    rw [chartMap, aeval_X, map_mul, openEval_localize, hi, aeval_X, chartPoint, div_eq_mul_inv]
  exact DFunLike.congr_fun h q

end Evaluation

/-- The polynomials vanishing on the chart are exactly the relations in the source localization. -/
private theorem imageIdeal_eq_ker (C : TaylorChart) (P : Ideal GeoJets) [P.IsPrime]
    (hD : C.denom ∉ P) : imageIdeal C P = RingHom.ker (chartMap C P).toRingHom := by
  ext q
  change q ∈ imageIdeal C P ↔ chartMap C P q = 0
  constructor
  · intro hq
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk P C.denom) (chartMap C P q)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    change chartMap C P q * localize C P C.denom ^ n = localize C P p at ha
    have hp : p ∈ P := by
      have hmul : C.denom * p ∈ P := by
        rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := GeoField) P]
        intro y hy
        change eval y (C.denom * p) = 0
        by_cases hyD : eval y C.denom = 0
        · rw [map_mul, hyD, zero_mul]
        · have hz : eval (chartPoint C y) q = 0 :=
            hq _ ⟨y, ⟨hy, hyD⟩, rfl⟩
          have he := congrArg (openEval hy hyD) ha
          rw [map_mul, map_pow, openEval_chartMap, openEval_localize, openEval_localize,
            hz, zero_mul] at he
          rw [map_mul, ← he, mul_zero]
      exact (‹P.IsPrime›.mem_or_mem hmul).resolve_left hD
    have hp0 : localize C P p = 0 := by
      change algebraMap (GeoJets ⧸ P) (ChartOpen C P) (Ideal.Quotient.mk P p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    rw [hp0] at ha
    exact ((IsLocalization.Away.algebraMap_isUnit (S := ChartOpen C P)
      (Ideal.Quotient.mk P C.denom)).pow n).mul_right_cancel (ha.trans (zero_mul _).symm)
  · intro hq
    rintro _ ⟨y, ⟨hy, hyD⟩, rfl⟩
    change eval (chartPoint C y) q = 0
    rw [← openEval_chartMap hy hyD, hq, map_zero]

private theorem chart_dimension (C : TaylorChart) (P : Ideal GeoJets) [P.IsPrime]
    (hD : C.denom ∉ P) :
    (imageIdeal C P).IsPrime ∧ dimension (imageIdeal C P) = (affineHilbertPolynomial P).natDegree := by
  have hne : Ideal.Quotient.mk P C.denom ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  let : IsDomain (ChartOpen C P) := Localization.Away.isDomain hne
  have hreg : IsLeftRegular (Ideal.Quotient.mk P C.denom) := (IsRegular.of_ne_zero hne).1
  unfold dimension
  rw [imageIdeal_eq_ker C P hD]
  refine ⟨RingHom.ker_isPrime _, le_antisymm ?_ ?_⟩
  · let e := awayPresentationEquiv P C.denom
    exact (natDegree_affineHilbertPolynomial_le_of_injective
      (e.symm.toAlgHom.comp (Ideal.kerLiftAlg (chartMap C P)))
      (e.symm.injective.comp (Ideal.kerLiftAlg_injective (chartMap C P)))).trans
      (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le P C.denom)
  · exact natDegree_affineHilbertPolynomial_le_of_away_range P C.denom hreg (chartMap C P)
      (fun q ↦ ⟨rename initialIndex q, chartMap_rename C P q⟩) le_rfl

theorem proof : K1_13_7_1_2.c1 := by
  intro f g hf _ hfg C P hP
  obtain ⟨hmin, hD⟩ := Ideal.mem_retainedMinimalPrimes.mp hP
  let := hmin.isPrime
  obtain ⟨hprime, hdim⟩ := chart_dimension C P hD
  exact ⟨hprime, hdim.trans (source_dimension hf hfg hmin)⟩

end

end K1_13_7_1_2_1
end PackSource_K1_13_7_1_2_1Proof

section PackSource_K1_13_5_5_1Split
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_13_5_5_1

noncomputable section

open K1_13 K1_13_5 K1_13_5_5
open scoped Polynomial

/-- On each regular second-jet chart a common power of the separant clears
all coefficient formulas, uniformly in the field extension and centre. -/
def c1 : Prop :=
  ∀ f : Row 3, ∃ (m : ℕ) (v : CoeffIndex → Row 3),
    ∀ (F : Type) [Field F] (k : Geom →+* F) (U : F[X]) (x : F),
      U.natDegree < taylorLength → trajectory k U f = 0 →
      rowAt k x (jetAt x U) (separant f) ≠ 0 →
      ∀ a : CoeffIndex, rowAt k x (jetAt x U) (separant f) ^ m * U.coeff a.val =
        rowAt k x (jetAt x U) (v a)

/-- Descend the tangent derivative to the regular generic chart and use
the whole-factor numerator to kill its iterate at the Taylor cutoff. -/
def c2 : Prop :=
  ∀ (f : Row 3) (hp : (chartIdeal f).IsPrime),
    letI := hp
    freshRow (separant f) ∉ chartIdeal f → Whole f →
      Nonempty (Tangent (chartConstants f) (chartCenter f) (chartJets f))

/-- The characteristic-truncated Taylor expansion continues a bounded
trajectory to a genuinely independent polynomial argument. -/
def c3 : Prop :=
  ∀ (f : Row 3) (F : Type) [Field F] (k : Geom →+* F) (x : F) (y : Fin 3 → F),
    TrueWeightLE f (90 * 180246 - 1) → rowAt k x y f = 0 → Tangent k x y →
      ∃ U : F[X], U.natDegree < taylorLength ∧ trajectory k U f = 0 ∧ jetAt x U = y

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_5_5.c1 := by
  intro f hf hd hmax hw hwhole
  let hp : (chartIdeal f).IsPrime := chart_prime f hf hd
  have hs := separant_regular f hf hd hmax
  obtain ⟨δ⟩ := h2 f hp hs hwhole
  have hzero : rowAt (chartConstants f) (chartCenter f) (chartJets f) f = 0 := by
    rw [rowAt_chart]
    exact (onChart_eq_zero f _).mpr (Ideal.mem_span_singleton_self _)
  obtain ⟨U, hU, hsol, hinit⟩ :=
    h3 f (ChartField f) (chartConstants f) (chartCenter f) (chartJets f) hw hzero δ
  obtain ⟨m, v, hv⟩ := h1 f
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
  refine ⟨P, ⟨RingHom.ker_isPrime _, ?_, ?_, hs, ?_⟩, ?_⟩
  · exact fun h => hf.ne_zero (rowMap_injective (h.trans (map_zero _).symm))
  · change (freshIdeal P).comap freshProjection.toRingHom = chartIdeal f
    rw [hbase, RingHom.comap_ker]
    exact himage
  · intro a
    refine ⟨freshRow (v a), m, ?_⟩
    have hU' : (U.map (newConstants : ChartField f →+* NewField (ChartField f))).natDegree <
        taylorLength := Polynomial.natDegree_map_le.trans_lt hU
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
    have hS' : (S.map freshConstants).natDegree < taylorLength :=
      Polynomial.natDegree_map_le.trans_lt (Nat.lt_succ_of_le hS)
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

end K1_13_5_5_1
end PackSource_K1_13_5_5_1Split

section PackSource_K1_13_5_5_1_1Proof
set_option autoImplicit true
namespace K1_13_5_5_1_1

noncomputable section

open K1_13 K1_13_5 K1_13_5_5 K1_13_5_5_1 Polynomial
open scoped BigOperators

private abbrev exponent : ℕ := 2 * taylorLength

private def clearedJet (f : Row 3) : ℕ → Row 3
  | 0 => separant f ^ exponent * MvPolynomial.X 0
  | 1 => separant f ^ exponent * MvPolynomial.X 1
  | 2 => separant f ^ exponent * MvPolynomial.X 2
  | j + 3 =>
    let scale := 2 * (↑(j + 3).factorial : Geom)⁻¹
    separant f ^ (exponent - (2 * j + 1)) *
      (MvPolynomial.C (Polynomial.C scale) * compatibilityNumerator f j)

/-- Translate the cleared Taylor coefficients back to the ordinary monomial basis. -/
private def clearedPolynomial (f : Row 3) (length : ℕ) : (Row 3)[X] :=
  taylor (-MvPolynomial.C Polynomial.X)
    (∑ i : Fin length, monomial i.val (clearedJet f i.val))

section Evaluation

variable {F : Type*} [Field F]

private theorem eval_clearedJet (k : Geom →+* F) (U : F[X]) (x : F) (f : Row 3)
    (hf : trajectory k U f = 0) (n : ℕ) (hn : n < taylorLength) :
    rowAt k x (jetAt x U) (clearedJet f n) =
      rowAt k x (jetAt x U) (separant f) ^ exponent * (hasseDeriv n U).eval x := by
  let e := rowAt k x (jetAt x U)
  let s := e (separant f)
  change e (clearedJet f n) = s ^ exponent * (hasseDeriv n U).eval x
  have eX (i : Fin 3) : e (MvPolynomial.X i) = (hasseDeriv i.val U).eval x :=
    MvPolynomial.eval₂Hom_X' _ _ _
  rcases n with _ | _ | _ | j
  · rw [clearedJet, map_mul, map_pow, eX]
    rfl
  · rw [clearedJet, map_mul, map_pow, eX]
    rfl
  · rw [clearedJet, map_mul, map_pow, eX]
    rfl
  have hc : e (compatibilityNumerator f j) =
      s ^ (2 * j + 1) * ((derivative^[j + 1]) (hasseDeriv 2 U)).eval x := by
    simp only [s, e, ← eval_trajectory, eval_compatibility _ _ _ hf, eval_mul, eval_pow]
  have hscale : e (MvPolynomial.C (Polynomial.C (2 * (↑(j + 3).factorial : Geom)⁻¹))) =
      2 * (↑(j + 3).factorial : F)⁻¹ := by
    simp [e, rowAt, map_ofNat]
  have hfact : (↑(j + 3).factorial : F) ≠ 0 := by
    have hg := K1_13_7_1.factorial_cast_ne_zero
      (hn.trans (by decide : taylorLength < K1.p))
    simpa only [map_natCast] using (map_ne_zero_iff k k.injective).mpr hg
  have hderiv :
      2 * ((derivative^[j + 1]) (hasseDeriv 2 U)).eval x =
        (↑(j + 3).factorial : F) * (hasseDeriv (j + 3) U).eval x := by
    have ho : (derivative^[j + 3]) U =
        ((j + 3).factorial : F[X]) * hasseDeriv (j + 3) U := by
      rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul]
    simpa only [eval_mul, eval_ofNat, eval_natCast] using
      congrArg (Polynomial.eval x) ((twice_iterate_derivative_top U j).trans ho)
  have hp : exponent - (2 * j + 1) + (2 * j + 1) = exponent := by
    dsimp only [exponent] at *
    omega
  calc
    e (clearedJet f (j + 3)) =
        s ^ (exponent - (2 * j + 1)) * s ^ (2 * j + 1) *
          ((↑(j + 3).factorial : F)⁻¹ *
            (2 * ((derivative^[j + 1]) (hasseDeriv 2 U)).eval x)) := by
      rw [clearedJet, map_mul, map_pow, map_mul, hscale, hc]
      ring
    _ = _ := by
      rw [← pow_add, hp, hderiv, ← mul_assoc ((↑(j + 3).factorial : F)⁻¹),
        inv_mul_cancel₀ hfact, one_mul]

private theorem eval_clearedPolynomial (k : Geom →+* F) (U : F[X]) (x : F)
    (f : Row 3) (length : ℕ) (hL : length ≤ taylorLength)
    (hU : U.natDegree < length) (hf : trajectory k U f = 0) :
    (clearedPolynomial f length).map (rowAt k x (jetAt x U)) =
      Polynomial.C (rowAt k x (jetAt x U) (separant f) ^ exponent) * U := by
  let e := rowAt k x (jetAt x U)
  let s := e (separant f)
  change (clearedPolynomial f length).map e = Polynomial.C (s ^ exponent) * U
  have hx : e (MvPolynomial.C Polynomial.X) = x := by simp [e, rowAt]
  apply taylor_injective x
  rw [clearedPolynomial, Polynomial.map_taylor, map_neg, hx, taylor_taylor,
    add_neg_cancel, taylor_zero, Polynomial.map_sum, taylor_mul, taylor_C]
  simp only [map_monomial]
  have hdeg : (taylor x U).natDegree < length := by rwa [natDegree_taylor]
  conv_rhs =>
    rw [Polynomial.as_sum_range' (taylor x U) length hdeg, ← Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_clearedJet k U x f hf _ (i.isLt.trans_le hL), taylor_coeff, C_mul_monomial]

end Evaluation

theorem proof : K1_13_5_5_1.c1 := by
  intro f
  refine ⟨exponent, fun a => (clearedPolynomial f taylorLength).coeff a.val, ?_⟩
  intro F _ k U x hU hf _ a
  have h := congrArg (fun P : F[X] => P.coeff a.val)
    (eval_clearedPolynomial k U x f taylorLength le_rfl hU hf)
  simpa only [coeff_map, coeff_C_mul] using h.symm

end

end K1_13_5_5_1_1
end PackSource_K1_13_5_5_1_1Proof

section PackSource_K1_13_5_5_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace K1_13_5_5_1_2

noncomputable section

open K1_13 K1_13_5 K1_13_5_5 K1_13_5_5_1
open scoped Polynomial nonZeroDivisors

private abbrev Dual (B : Type*) := TrivSqZeroExt B B

private def dualPair {B : Type*} (a b : B) : Dual B := (a, b)

private abbrev fstHom (B : Type*) [CommRing B] : Dual B →+* B :=
  (TrivSqZeroExt.fstHom B B B).toRingHom

/-- A dual number over a field is invertible whenever its reduction is nonzero. -/
private def liftDual {A L B : Type*} [CommRing A] [IsDomain A] [Field L] [Field B]
    [Algebra A L] [IsFractionRing A L] (g : A →+* Dual B)
    (hg : Function.Injective ((fstHom B).comp g)) : L →+* Dual B :=
  IsLocalization.lift (M := A⁰) (g := g) fun d =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr (by
      change ((fstHom B).comp g) (d : A) ≠ 0
      intro h
      exact (mem_nonZeroDivisors_iff_ne_zero.mp d.2) (hg (h.trans (map_zero _).symm))))

private theorem liftDual_apply {A L B : Type*} [CommRing A] [IsDomain A] [Field L] [Field B]
    [Algebra A L] [IsFractionRing A L] (g : A →+* Dual B)
    (hg : Function.Injective ((fstHom B).comp g)) (a : A) :
    liftDual (L := L) g hg (algebraMap A L a) = g a :=
  IsLocalization.lift_eq _ _

private def polyJet {B : Type*} [CommRing B] (g : Geom[X] →+* B) : Geom[X] →+* Dual B where
  toFun p := (g p, g p.derivative)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · exact map_add g p q
    · change g (p + q).derivative = g p.derivative + g q.derivative
      rw [map_add, map_add]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · exact map_mul g p q
    · change g (p * q).derivative = g p * g q.derivative + g p.derivative * g q
      rw [Polynomial.derivative_mul, map_add, map_mul, map_mul, add_comm]

section Evaluation

variable {B : Type*} [Field B] (e : FreshJetRing →+* B)

private abbrev freshValue : FreshField →+* B := e.comp MvPolynomial.C
private abbrev coeffValue : Geom[X] →+* B :=
  (freshValue e).comp (algebraMap Geom[X] FreshField)
private abbrev evalRow : Row 3 →+* B := e.comp rowMap
private abbrev jetValue (i : Fin 3) : B := e (MvPolynomial.X i)

private def coeffJet : FreshField →+* Dual B :=
  liftDual (A := Geom[X]) (L := FreshField) (B := B) (polyJet (coeffValue e))
    ((freshValue e).injective.comp (IsFractionRing.injective Geom[X] FreshField))

private theorem coeffJet_apply (p : Geom[X]) :
    coeffJet e (algebraMap Geom[X] FreshField p) = polyJet (coeffValue e) p :=
  liftDual_apply _ _ _

private theorem coeffJet_fst (a : FreshField) : (coeffJet e a).fst = freshValue e a := by
  have h : (fstHom B).comp (coeffJet e) = freshValue e := by
    apply IsLocalization.ringHom_ext (Geom[X]⁰)
    apply RingHom.ext
    intro p
    exact congrArg TrivSqZeroExt.fst (coeffJet_apply e p)
  exact RingHom.congr_fun h a

private def freshJet (v : Fin 3 → B) : FreshJetRing →+* Dual B :=
  MvPolynomial.eval₂Hom (coeffJet e) (fun i => dualPair (jetValue e i) (v i))

private def rowJet (v : Fin 3 → B) : Row 3 →+* Dual B :=
  MvPolynomial.eval₂Hom (polyJet (coeffValue e)) (fun i => dualPair (jetValue e i) (v i))

private theorem freshJet_fst (v : Fin 3 → B) (b : FreshJetRing) :
    (freshJet e v b).fst = e b := by
  have h : (fstHom B).comp (freshJet e v) = e := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (freshJet e v (MvPolynomial.C a)).fst = _
      simpa only [freshJet, MvPolynomial.eval₂Hom_C, freshValue, RingHom.comp_apply]
        using coeffJet_fst e a
    · intro i
      change (freshJet e v (MvPolynomial.X i)).fst = _
      rw [freshJet, MvPolynomial.eval₂Hom_X']
      rfl
  exact RingHom.congr_fun h b

private theorem freshJet_rowMap (v : Fin 3 → B) (b : Row 3) :
    freshJet e v (rowMap b) = rowJet e v b := by
  have h : (freshJet e v).comp rowMap = rowJet e v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, rowMap, MvPolynomial.map_C, freshJet, rowJet,
        MvPolynomial.eval₂Hom_C] using coeffJet_apply e a
    · intro i
      simp [freshJet, rowJet, rowMap]
  exact RingHom.congr_fun h b

private theorem rowJet_fst (v : Fin 3 → B) (b : Row 3) :
    (rowJet e v b).fst = evalRow e b := by
  rw [← freshJet_rowMap, freshJet_fst]
  rfl

@[simp] private theorem coeff_coeffDerivative (b : Row 3) (m : Fin 3 →₀ ℕ) :
    (coeffDerivative b).coeff m = (b.coeff m).derivative := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]

private theorem coeffDerivative_C (p : Geom[X]) :
    coeffDerivative (MvPolynomial.C p : Row 3) = MvPolynomial.C p.derivative := by
  classical
  ext m
  by_cases h : 0 = m <;> simp [MvPolynomial.coeff_C, h]

private theorem coeffDerivative_add (b c : Row 3) :
    coeffDerivative (b + c) = coeffDerivative b + coeffDerivative c := by
  ext m
  simp

private theorem coeffDerivative_mul_X (b : Row 3) (i : Fin 3) :
    coeffDerivative (b * MvPolynomial.X i) = coeffDerivative b * MvPolynomial.X i := by
  classical
  ext m
  rw [coeff_coeffDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp

/-- The two components give evaluation and the directional chain rule, respectively. -/
private theorem rowJet_snd (v : Fin 3 → B) (b : Row 3) :
    (rowJet e v b).snd = evalRow e (coeffDerivative b) +
      ∑ i, v i * evalRow e (MvPolynomial.pderiv i b) := by
  classical
  let E := evalRow e
  let J := rowJet e v
  change (J b).snd = E (coeffDerivative b) + ∑ i, v i * E (MvPolynomial.pderiv i b)
  induction b using MvPolynomial.induction_on with
  | C a =>
    simp [J, E, rowJet, rowMap, coeffDerivative_C]
    rfl
  | add b c hb hc =>
    simp only [map_add, TrivSqZeroExt.snd_add, hb, hc, coeffDerivative_add, mul_add,
      Finset.sum_add_distrib]
    ring
  | mul_X b j hb =>
    have hJ : J (MvPolynomial.X j) = dualPair (jetValue e j) (v j) := by simp [J, rowJet]
    have hE : E (MvPolynomial.X j) = jetValue e j := by simp [E, rowMap]
    rw [map_mul, hJ, coeffDerivative_mul_X, map_mul, hE]
    change (J b).fst * v j + (J b).snd * jetValue e j = _
    rw [show (J b).fst = E b from rowJet_fst e v b]
    simp only [hb, MvPolynomial.pderiv_mul, map_add, map_mul, hE, mul_add,
      Finset.sum_add_distrib]
    have h₁ : (∑ i, v i * (E (MvPolynomial.pderiv i b) * jetValue e j)) =
        (∑ i, v i * E (MvPolynomial.pderiv i b)) * jetValue e j := by
      simp only [Finset.sum_mul, mul_assoc]
    have h₂ : (∑ i, v i * (E b * E (MvPolynomial.pderiv i (MvPolynomial.X j)))) =
        v j * E b := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]
    rw [h₁, h₂]
    ring

variable (f : Row 3)

private abbrev topVelocity : B := -evalRow e (lowerTangent f) / evalRow e (separant f)

private def velocity : Fin 3 → B := ![jetValue e 1, 2 * jetValue e 2, topVelocity e f]

private theorem rowJet_velocity (b : Row 3) :
    (rowJet e (velocity e f) b).snd = evalRow e (lowerTangent b) +
      topVelocity e f * evalRow e (separant b) := by
  rw [rowJet_snd, Fin.sum_univ_three]
  simp [lowerTangent, separant, velocity, evalRow, rowMap, map_ofNat, add_assoc]

private theorem mul_topVelocity (hs : evalRow e (separant f) ≠ 0) :
    evalRow e (separant f) * topVelocity e f = -evalRow e (lowerTangent f) := by
  rw [topVelocity, ← mul_div_assoc, mul_div_cancel_left₀ _ hs]

/-- The tangent equation kills both components of the defining row, so the
dual-number map descends to the prime quotient. -/
private def kernelJet (I : Ideal FreshJetRing) (hI : I = chartIdeal f)
    (hz : evalRow e f = 0) (hs : evalRow e (separant f) ≠ 0) :
    FreshJetRing ⧸ I →+* Dual B :=
  Ideal.Quotient.lift I (freshJet e (velocity e f)) (by
    intro b hb
    rw [hI] at hb
    have h : freshJet e (velocity e f) (freshRow f) = 0 := by
      apply TrivSqZeroExt.ext
      · rw [freshJet_fst, TrivSqZeroExt.fst_zero]
        exact hz
      · change (freshJet e (velocity e f) (rowMap f)).snd = 0
        rw [freshJet_rowMap, rowJet_velocity, mul_comm (topVelocity e f), mul_topVelocity e f hs,
          add_neg_cancel]
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hb
    rw [map_mul, h, zero_mul])

end Evaluation

section FractionField

variable {A B : Type*} [CommRing A] [IsDomain A] [Field B] [Algebra A B] [IsFractionRing A B]

private def fractionJet (q : A →+* Dual B)
    (hq : (fstHom B).comp q = algebraMap A B) : B →+* Dual B :=
  liftDual (L := B) q (by rw [hq]; exact IsFractionRing.injective A B)

private theorem fractionJet_apply (q : A →+* Dual B)
    (hq : (fstHom B).comp q = algebraMap A B) (a : A) :
    fractionJet q hq (algebraMap A B a) = q a :=
  liftDual_apply _ _ _

private theorem fractionJet_fst (q : A →+* Dual B)
    (hq : (fstHom B).comp q = algebraMap A B) (b : B) : (fractionJet q hq b).fst = b := by
  have h : (fstHom B).comp (fractionJet q hq) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (A⁰)
    apply RingHom.ext
    intro a
    change (fractionJet q hq (algebraMap A B a)).fst = _
    rw [fractionJet_apply]
    exact RingHom.congr_fun hq a
  exact RingHom.congr_fun h b

private def fractionDeriv (q : A →+* Dual B)
    (hq : (fstHom B).comp q = algebraMap A B) : Derivation ℕ B B :=
  Derivation.mk'
    ((TrivSqZeroExt.sndHom (R := B) (M := B)).toAddMonoidHom.comp
      (fractionJet q hq).toAddMonoidHom).toNatLinearMap (by
        intro a b
        change (fractionJet q hq (a * b)).snd =
          a * (fractionJet q hq b).snd + b * (fractionJet q hq a).snd
        rw [map_mul]
        change (fractionJet q hq a).fst * (fractionJet q hq b).snd +
          (fractionJet q hq a).snd * (fractionJet q hq b).fst = _
        rw [fractionJet_fst, fractionJet_fst, mul_comm (fractionJet q hq a).snd b])

private theorem fractionDeriv_apply (q : A →+* Dual B)
    (hq : (fstHom B).comp q = algebraMap A B) (a : A) :
    fractionDeriv q hq (algebraMap A B a) = (q a).snd := by
  change (fractionJet q hq (algebraMap A B a)).snd = _
  rw [fractionJet_apply]

end FractionField

section Descent

variable {A B : Type*} [CommRing A] [Field B] [Algebra A B]

private abbrev fractionMap (q : FreshJetRing →+* A) : FreshJetRing →+* B :=
  (algebraMap A B).comp q

private theorem evalRow_self (q : FreshJetRing →+* A) (f : Row 3)
    (hk : RingHom.ker q = chartIdeal f) : evalRow (fractionMap (B := B) q) f = 0 := by
  have hm : freshRow f ∈ RingHom.ker q := by
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  change algebraMap A B (q (freshRow f)) = 0
  rw [RingHom.mem_ker.mp hm, map_zero]

private def descendedJet (q : FreshJetRing →+* A) (f : Row 3)
    (hq : Function.Surjective q) (hk : RingHom.ker q = chartIdeal f)
    (hs : evalRow (fractionMap (B := B) q) (separant f) ≠ 0) : A →+* Dual B :=
  (kernelJet (fractionMap q) f (RingHom.ker q) hk (evalRow_self q f hk) hs).comp
    (q.quotientKerEquivOfSurjective hq).symm.toRingHom

private theorem descendedJet_apply (q : FreshJetRing →+* A) (f : Row 3)
    (hq : Function.Surjective q) (hk : RingHom.ker q = chartIdeal f)
    (hs : evalRow (fractionMap (B := B) q) (separant f) ≠ 0) (b : FreshJetRing) :
    descendedJet q f hq hk hs (q b) = freshJet (fractionMap q) (velocity (fractionMap q) f) b := by
  change kernelJet (fractionMap q) f _ hk (evalRow_self q f hk) hs
    ((q.quotientKerEquivOfSurjective hq).symm (q b)) = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

private theorem descendedJet_fst (q : FreshJetRing →+* A) (f : Row 3)
    (hq : Function.Surjective q) (hk : RingHom.ker q = chartIdeal f)
    (hs : evalRow (fractionMap (B := B) q) (separant f) ≠ 0) :
    (fstHom B).comp (descendedJet q f hq hk hs) = algebraMap A B := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := hq a
  change (descendedJet q f hq hk hs (q b)).fst = _
  rw [descendedJet_apply]
  exact freshJet_fst (fractionMap q) (velocity (fractionMap q) f) b

private theorem existsDerivation [IsDomain A] [IsFractionRing A B]
    (q : FreshJetRing →+* A) (f : Row 3)
    (hq : Function.Surjective q) (hk : RingHom.ker q = chartIdeal f)
    (hs : evalRow (fractionMap (B := B) q) (separant f) ≠ 0) :
    ∃ D : Derivation ℕ B B, ∀ b : FreshJetRing,
      D (fractionMap q b) = (freshJet (fractionMap q) (velocity (fractionMap q) f) b).snd := by
  refine ⟨fractionDeriv (descendedJet q f hq hk hs) (descendedJet_fst q f hq hk hs), ?_⟩
  intro b
  change fractionDeriv _ _ (algebraMap A B (q b)) = _
  rw [fractionDeriv_apply, descendedJet_apply]

end Descent

section Cutoff

variable {B : Type*} [Field B] (e : FreshJetRing →+* B) (f : Row 3) (D : Derivation ℕ B B)
variable (hD : ∀ b : FreshJetRing, D (e b) = (freshJet e (velocity e f) b).snd)

include hD in
private theorem deriv_poly (p : Geom[X]) :
    D (coeffValue e p) = coeffValue e p.derivative := by
  change D (e (MvPolynomial.C (algebraMap Geom[X] FreshField p))) = _
  rw [hD, freshJet, MvPolynomial.eval₂Hom_C, coeffJet_apply]
  rfl

include hD in
private theorem deriv_jet (i : Fin 3) : D (jetValue e i) = velocity e f i := by
  change D (e (MvPolynomial.X i)) = _
  rw [hD, freshJet, MvPolynomial.eval₂Hom_X']
  rfl

include hD in
private theorem deriv_evalRow (b : Row 3) :
    D (evalRow e b) = evalRow e (lowerTangent b) +
      topVelocity e f * evalRow e (separant b) := by
  change D (e (rowMap b)) = _
  rw [hD, freshJet_rowMap, rowJet_velocity]

variable (hs : evalRow e (separant f) ≠ 0)

include hD hs in
private theorem eval_tangentNumerator (b : Row 3) :
    evalRow e (tangentNumerator f b) = evalRow e (separant f) * D (evalRow e b) := by
  rw [deriv_evalRow e f D hD, mul_add, ← mul_assoc, mul_topVelocity e f hs]
  simp [tangentNumerator, separant, sub_eq_add_neg]

private theorem cleared_rule {F : Type*} [Field F] (δ : Derivation ℕ F F) (s z : F) (a : ℕ) :
    s * (s * δ (s ^ a * z)) - (a : F) * (s ^ a * z) * (s * δ s) =
      s ^ (a + 2) * δ z := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [δ.leibniz, δ.leibniz_pow, pow_add s (a + 1) 2, pow_succ' s a]
    simp only [Nat.succ_sub_one, smul_eq_mul, nsmul_eq_mul, pow_two]
    ring

include hD hs in
/-- At step n the numerator clears exactly the power 2n+1 from δ^(n+1)Y₂. -/
private theorem evalNumerator (n : ℕ) :
    evalRow e (compatibilityNumerator f n) = evalRow e (separant f) ^ (2 * n + 1) *
      ((D : B → B)^[n + 1]) (jetValue e 2) := by
  induction n with
  | zero =>
    change evalRow e (-lowerTangent f) = evalRow e (separant f) ^ 1 * D (jetValue e 2)
    rw [map_neg, pow_one, deriv_jet e f D hD]
    exact (mul_topVelocity e f hs).symm
  | succ n ih =>
    rw [compatibilityNumerator]
    simp only [map_sub, map_mul, map_natCast, eval_tangentNumerator e f D hD hs]
    rw [ih, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
      Function.iterate_succ_apply' _ (n + 1)]
    exact cleared_rule _ _ _ _

include hD in
private theorem iterate_value (n : ℕ) :
    ((D : B → B)^[n + 2]) (jetValue e 0) =
      2 * ((D : B → B)^[n]) (jetValue e 2) := by
  induction n with
  | zero =>
    change D (D (jetValue e 0)) = 2 * jetValue e 2
    rw [deriv_jet e f D hD, show velocity e f 0 = jetValue e 1 by rfl, deriv_jet e f D hD]
    rfl
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Function.iterate_succ_apply', ih,
      Function.iterate_succ_apply']
    simp only [two_mul, map_add]

include hD hs in
private theorem deriv_cutoff (hz : evalRow e f = 0) (hwhole : Whole f) :
    ((D : B → B)^[taylorLength]) (jetValue e 0) = 0 := by
  let n := taylorLength - 3
  have hnum : evalRow e (compatibilityNumerator f n) = 0 := by
    obtain ⟨q, hq⟩ := hwhole
    change compatibilityNumerator f n = f * q at hq
    rw [hq, map_mul, hz, zero_mul]
  rw [evalNumerator e f D hD hs] at hnum
  have h := (mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hs)
  rw [show taylorLength = (n + 1) + 2 by rfl, iterate_value e f D hD, h, mul_zero]

include hD hs in
private theorem chartTangent (hz : evalRow e f = 0) (hwhole : Whole f) :
    Nonempty (Tangent ((freshValue e).comp freshConstants)
      (e (MvPolynomial.C freshCenter)) (jetValue e)) := by
  exact ⟨{
    deriv := D.toLinearMap.toAddMonoidHom
    leibniz := fun a b => D.leibniz a b
    constants := fun a => by
      change D (coeffValue e (Polynomial.C a)) = 0
      rw [deriv_poly e f D hD, Polynomial.derivative_C, map_zero]
    center := by
      change D (coeffValue e Polynomial.X) = 1
      rw [deriv_poly e f D hD, Polynomial.derivative_X, map_one]
    value := deriv_jet e f D hD 0
    first := deriv_jet e f D hD 1
    cutoff := deriv_cutoff e f D hD hs hz hwhole }⟩

end Cutoff

private theorem tangentFromProjection {A B : Type*} [CommRing A] [IsDomain A]
    [Field B] [Algebra A B] [IsFractionRing A B] (q : FreshJetRing →+* A) (f : Row 3)
    (hq : Function.Surjective q) (hk : RingHom.ker q = chartIdeal f)
    (hs : evalRow (fractionMap (B := B) q) (separant f) ≠ 0) (hwhole : Whole f) :
    Nonempty (Tangent ((freshValue (fractionMap (B := B) q)).comp freshConstants)
      (fractionMap q (MvPolynomial.C freshCenter)) (jetValue (fractionMap q))) := by
  obtain ⟨D, hD⟩ := existsDerivation (B := B) q f hq hk hs
  exact chartTangent (fractionMap q) f D hD hs (evalRow_self q f hk) hwhole

theorem proof : K1_13_5_5_1.c2 := by
  intro f hp
  let : (chartIdeal f).IsPrime := hp
  change freshRow (separant f) ∉ chartIdeal f → Whole f →
    Nonempty (Tangent (chartConstants f) (chartCenter f) (chartJets f))
  intro hs hwhole
  let π : FreshJetRing →+* ChartRing f := Ideal.Quotient.mk (chartIdeal f)
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = chartIdeal f := Ideal.mk_ker
  have hregular : onChart f (freshRow (separant f)) ≠ 0 :=
    fun h => hs ((onChart_eq_zero f _).mp h)
  let qr : CommRing (ChartRing f) := Ideal.Quotient.commRing (chartIdeal f)
  let qd : IsDomain (ChartRing f) := Ideal.Quotient.isDomain (chartIdeal f)
  let kf : Field (ChartField f) := FractionRing.field (ChartRing f)
  let ka : Algebra (ChartRing f) (ChartField f) := inferInstance
  let kl : IsFractionRing (ChartRing f) (ChartField f) := inferInstance
  have h := @tangentFromProjection (ChartRing f) (ChartField f) qr qd kf ka kl π f
    hsurj hker hregular hwhole
  exact h

end

end K1_13_5_5_1_2
end PackSource_K1_13_5_5_1_2Proof

section PackSource_K1_13_5_5_1_3Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace K1_13_5_5_1_3

noncomputable section

open K1_13 K1_13_5_5_1 Polynomial
open scoped BigOperators Differential

variable {F : Type*} [Field F]

private abbrev differentialOfTangent {k : Geom →+* F} {x : F} {y : Fin 3 → F}
    (h : Tangent k x y) : Differential F :=
  ⟨Derivation.mk' h.deriv.toIntLinearMap (by
    intro a b
    change h.deriv (a * b) = a * h.deriv b + b * h.deriv a
    exact h.leibniz a b)⟩

private theorem factorial_ne_zero [CharP F K1.p] {n : ℕ} (hn : n < K1.p) :
    (n.factorial : F) ≠ 0 := by
  intro hz
  have hp := CharP.char_is_prime_of_two_le F K1.p (by decide)
  exact (not_le_of_gt hn) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff F K1.p _).mp hz))

private theorem iterate_zero_of_eq {D E : F → F} (hDE : D = E) (L : ℕ) (a : F)
    (hE : E^[L] a = 0) : D^[L] a = 0 := by
  simpa only [hDE] using hE

variable [Differential F]

private def normalizedJet (a : F) (n : ℕ) : F :=
  ((Differential.deriv : F → F)^[n]) a / n.factorial

private theorem normalizedJet_succ [CharP F K1.p] (a : F) (n : ℕ) (hn : n + 1 < K1.p) :
    (normalizedJet a n)′ = ((n : F) + 1) * normalizedJet a (n + 1) := by
  let D : Derivation ℤ F F := Differential.deriv
  have hd : D (normalizedJet a n) = (n.factorial : F)⁻¹ * D (((D : F → F)^[n]) a) :=
    D.leibniz_div_const _ (n.factorial : F) (D.map_natCast _)
  change D (normalizedJet a n) = _
  rw [hd, normalizedJet, Function.iterate_succ_apply',
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hfac : (n.factorial : F) ≠ 0 := factorial_ne_zero (by omega)
  have hs : (n : F) + 1 ≠ 0 := by
    intro hz
    apply factorial_ne_zero (F := F) hn
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, hz, zero_mul]
  field_simp [hfac, hs] <;> rfl

private def centered (L : ℕ) (a : F) : F[X] :=
  ∑ n ∈ Finset.range L, monomial n (normalizedJet a n)

private theorem coeff_centered (L : ℕ) (a : F) (n : ℕ) :
    (centered L a).coeff n = if n < L then normalizedJet a n else 0 := by
  classical
  simp only [centered, Polynomial.finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_range]

private theorem degree_centered {L : ℕ} (hL : 0 < L) (a : F) : (centered L a).natDegree < L := by
  apply lt_of_le_of_lt _ (show L - 1 < L by omega)
  apply natDegree_sum_le_of_forall_le
  intro n hn
  exact (natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt (Finset.mem_range.mp hn))

private theorem mapCoeffs_centered [CharP F K1.p] {L : ℕ} (hL : L < K1.p) (a : F)
    (hcut : ((Differential.deriv : F → F)^[L]) a = 0) :
    Differential.mapCoeffs (centered L a) = derivative (centered L a) := by
  ext n
  simp only [Differential.coeff_mapCoeffs, coeff_derivative, coeff_centered]
  by_cases hn : n + 1 < L
  · rw [ite_eq_left (show n < L by omega), ite_eq_left hn,
      normalizedJet_succ a n (hn.trans hL), mul_comm]
  · rw [ite_eq_right hn, zero_mul]
    by_cases h : n < L
    · have he : n + 1 = L := by omega
      have hz : normalizedJet a L = 0 := by rw [normalizedJet, hcut, zero_div]
      rw [ite_eq_left h, normalizedJet_succ a n (by rwa [he]), he, hz, mul_zero]
    · rw [ite_eq_right h, map_zero]

omit [Differential F] in
private theorem aeval_shift (x : F) (P : F[X]) :
    aeval (Polynomial.X - C x) P = taylor (-x) P := by
  rw [taylor_apply, C_neg, ← sub_eq_add_neg, Polynomial.aeval_def, Polynomial.comp,
    Polynomial.algebraMap_eq]

/-- Translation cancels the coefficient derivation against ordinary differentiation. -/
private theorem mapCoeffs_uncenter (x : F) (hx : x′ = 1) (P : F[X])
    (hP : Differential.mapCoeffs P = derivative P) :
    Differential.mapCoeffs (taylor (-x) P) = 0 := by
  let _ : Differential F[X] := ⟨Differential.mapCoeffs⟩
  let _ : DifferentialAlgebra F F[X] := ⟨by
    intro a
    change Differential.mapCoeffs (C a) = C a′
    exact Differential.mapCoeffs_C a⟩
  have hshift : (Polynomial.X - C x : F[X])′ = -1 := by
    change Differential.mapCoeffs (Polynomial.X - C x) = -1
    simp [hx]
  rw [← aeval_shift]
  change (aeval (Polynomial.X - C x) P)′ = 0
  rw [Differential.deriv_aeval_eq, hP, hshift, mul_neg_one, add_neg_cancel]

private theorem mapCoeffs_trajectory (k : Geom →+* F) (hk : ∀ a : Geom, (k a)′ = 0)
    {U : F[X]} (hU : Differential.mapCoeffs U = 0) (f : Row 3) :
    Differential.mapCoeffs (trajectory k U f) = 0 := by
  have hcoeff (n : ℕ) : (U.coeff n)′ = 0 := by
    simpa only [Differential.coeff_mapCoeffs, coeff_zero] using
      congrArg (fun P : F[X] => P.coeff n) hU
  have hj (i : Fin 3) : Differential.mapCoeffs (hasseDeriv i.val U) = 0 := by
    ext n
    simp [hasseDeriv_coeff, Derivation.leibniz, smul_eq_mul, hcoeff]
  induction f using MvPolynomial.induction_on with
  | C P =>
    change Differential.mapCoeffs (MvPolynomial.eval₂Hom (mapRingHom k) _ (MvPolynomial.C P)) = 0
    rw [MvPolynomial.eval₂Hom_C]
    ext n
    simp [hk]
  | add f g hf hg =>
    rw [map_add, map_add, hf, hg, add_zero]
  | mul_X f i hf =>
    have hXi : trajectory k U (MvPolynomial.X i) = hasseDeriv i.val U := by
      simp [trajectory]
    rw [map_mul, hXi, Derivation.leibniz, hf, hj]
    simp

omit [Differential F] in
private theorem degree_trajectory (k : Geom →+* F) {U : F[X]}
    (hU : U.natDegree < taylorLength) (f : Row 3) {d : ℕ} (hf : TrueWeightLE f d) :
    (trajectory k U f).natDegree ≤ d := by
  classical
  unfold trajectory
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hprod : (∏ i ∈ m.support, hasseDeriv i.val U ^ m i).natDegree ≤
      m.sum (fun i e => (133646 - i.val) * e) := by
    unfold Finsupp.sum
    apply (natDegree_prod_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    change ((hasseDeriv i.val U) ^ m i).natDegree ≤ (133646 - i.val) * m i
    rw [Nat.mul_comm]
    exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le U i.val).trans
      (Nat.sub_le_sub_right (Nat.le_of_lt_succ hU) _))
  exact (natDegree_mul_le_of_le natDegree_map_le hprod).trans (hf m hm)

/-- A root at a point with derivative one forces all ordinary polynomial
derivatives to vanish there when the coefficients are fixed. -/
private theorem eq_zero_of_constant_coeffs [CharP F K1.p]
    (x : F) (hx : x′ = 1) (P : F[X]) (hP : P.natDegree < K1.p)
    (hconst : Differential.mapCoeffs P = 0) (hroot : P.eval x = 0) : P = 0 := by
  suffices aux : ∀ n (Q : F[X]), Q.natDegree = n → Q.natDegree < K1.p →
      Differential.mapCoeffs Q = 0 → Q.eval x = 0 → Q = 0 by
    exact aux P.natDegree P rfl hP hconst hroot
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Q hdeg hchar hQ hzero
    by_cases hn : n = 0
    · rw [eq_C_of_natDegree_eq_zero (hdeg.trans hn), eval_C] at hzero
      rw [eq_C_of_natDegree_eq_zero (hdeg.trans hn), hzero, map_zero]
    have hlt : Q.derivative.natDegree < n := by
      rw [← hdeg]
      exact natDegree_derivative_lt (fun h => hn (hdeg.symm.trans h))
    have hnp : n < K1.p := hdeg ▸ hchar
    have hderiv : Q.derivative.eval x = 0 := by
      have he := Differential.deriv_aeval_eq x Q
      simpa only [coe_aeval_eq_eval, hQ, hzero, hx, map_zero, eval_zero, mul_one, zero_add,
        eq_comm] using he
    have hconstant : Differential.mapCoeffs Q.derivative = 0 := by
      have hc (i : ℕ) : (Q.coeff i)′ = 0 := by
        simpa only [Differential.coeff_mapCoeffs, coeff_zero] using
          congrArg (fun A : F[X] => A.coeff i) hQ
      ext i
      simp [coeff_derivative, Derivation.leibniz, smul_eq_mul, hc]
    have hz := ih _ hlt _ rfl (hlt.trans hnp) hconstant hderiv
    have hcast : (n : F) ≠ 0 := by
      intro h
      exact (not_le_of_gt hnp)
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((CharP.cast_eq_zero_iff F K1.p _).mp h))
    have htop := congrArg (fun A : F[X] => A.coeff (n - 1)) hz
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
    have hcast' : ((n - 1 : ℕ) : F) + 1 = (n : F) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun j : ℕ => (j : F)) hn'
    rw [coeff_derivative, hcast', hn', coeff_zero] at htop
    have hleading : Q.leadingCoeff = 0 := by
      rw [leadingCoeff, hdeg]
      exact (mul_eq_zero.mp htop).resolve_right hcast
    exact leadingCoeff_eq_zero.mp hleading

private theorem reconstruct [CharP F K1.p] {L : ℕ} (hL : 3 ≤ L) (hchar : L < K1.p)
    (x : F) (y : Fin 3 → F) (hx : x′ = 1) (hval : (y 0)′ = y 1)
    (hfirst : (y 1)′ = 2 * y 2) (hcut : ((Differential.deriv : F → F)^[L]) (y 0) = 0) :
    ∃ U : F[X], U.natDegree < L ∧ Differential.mapCoeffs U = 0 ∧ jetAt x U = y := by
  let U := taylor (-x) (centered L (y 0))
  have hU : U.natDegree < L := by
    rw [show U = taylor (-x) (centered L (y 0)) from rfl, natDegree_taylor]
    exact degree_centered (by omega) _
  have hc : Differential.mapCoeffs U = 0 :=
    mapCoeffs_uncenter x hx _ (mapCoeffs_centered hchar _ hcut)
  refine ⟨U, hU, hc, ?_⟩
  funext i
  have hi : i.val < L := i.isLt.trans_le hL
  rw [jetAt, ← taylor_coeff, show U = taylor (-x) (centered L (y 0)) from rfl,
    taylor_taylor, add_neg_cancel, taylor_zero, coeff_centered, ite_eq_left hi]
  fin_cases i
  · simp [normalizedJet]
  · simpa [normalizedJet] using hval
  · change normalizedJet (y 0) 2 = y 2
    rw [normalizedJet, Function.iterate_succ_apply', Function.iterate_one, hval, hfirst]
    have htwo : (2 : F) ≠ 0 := by
      have h2 := factorial_ne_zero (F := F) (n := 2) (by decide)
      norm_num at h2
      exact h2
    norm_num
    exact (div_eq_iff htwo).2 (mul_comm _ _)

theorem proof : K1_13_5_5_1.c3 := by
  intro f F _ k x y hweight hzero h
  let _ : CharP F K1.p := charP_of_injective_ringHom (k.comp embed).injective K1.p
  let _ : Differential F := differentialOfTangent h
  have hx : x′ = 1 := h.center
  have heq : (Differential.deriv : F → F) = (h.deriv : F → F) := rfl
  obtain ⟨U, hU, hc, hjet⟩ := reconstruct (L := taylorLength) (by decide) (by decide) x y
    hx h.value h.first (iterate_zero_of_eq heq taylorLength (y 0) h.cutoff)
  have hroot : (trajectory k U f).eval x = 0 :=
    (eval_trajectory k U x f).trans ((congrArg (fun z => rowAt k x z f) hjet).trans hzero)
  refine ⟨U, hU, ?_, hjet⟩
  apply eq_zero_of_constant_coeffs x hx _ ((degree_trajectory k hU f hweight).trans_lt
    (by decide : 90 * 180246 - 1 < K1.p)) (mapCoeffs_trajectory k h.constants hc f) hroot

end

end K1_13_5_5_1_3
end PackSource_K1_13_5_5_1_3Proof

section PackSource_K1_14_2_2_4_1Proof
set_option autoImplicit true
set_option maxHeartbeats 800000

namespace K1_14_2_2_4_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open scoped Classical

private abbrev Variables := Option (Option (Fin 2))
private abbrev Flat := MvPolynomial Variables FX

/-- Read the derivative and ordinate variables as the two polynomial layers. -/
private def unflatten : Flat ≃+* Jet :=
  (MvPolynomial.optionEquivLeft FX (Option (Fin 2))).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.optionEquivLeft FX (Fin 2)).toRingEquiv)

private theorem unflatten_apply (q : Flat) :
    unflatten q =
      (MvPolynomial.optionEquivLeft FX (Option (Fin 2)) q).map
        (MvPolynomial.optionEquivLeft FX (Fin 2)).toRingHom := rfl

private theorem flatten_coeff (P : Jet) (j i : ℕ) (d : Fin 2 →₀ ℕ) :
    (unflatten.symm P).coeff ((d.optionElim i).optionElim j) =
      ((P.coeff j).coeff i).coeff d := by
  have h := congrArg (fun Q : Jet => ((Q.coeff j).coeff i).coeff d)
    (unflatten.apply_symm_apply P)
  rw [unflatten_apply, coeff_map] at h
  change (((MvPolynomial.optionEquivLeft FX (Fin 2)
    ((MvPolynomial.optionEquivLeft FX (Option (Fin 2)) (unflatten.symm P)).coeff j)).coeff i).coeff d)
    = _ at h
  rw [MvPolynomial.optionEquivLeft_coeff_coeff, MvPolynomial.optionEquivLeft_coeff_coeff] at h
  exact h

private def ambientIndex : Fin 4 ≃ Variables :=
  finSuccEquivLast.trans (Equiv.optionCongr finSuccEquivLast)

private def ambientToJet : Ambient ≃+* Jet :=
  (MvPolynomial.renameEquiv FX ambientIndex).toRingEquiv.trans unflatten

private theorem toJet_equiv : toJet = ambientToJet.symm.toRingHom := by
  have h : toJet.comp ambientToJet.toRingHom = RingHom.id Ambient := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change toJet (unflatten (MvPolynomial.rename ambientIndex (MvPolynomial.C a))) = _
      simp [unflatten_apply, toJet, toRoot, rootIncl, rootSeeds]
    · intro k
      change toJet (unflatten (MvPolynomial.rename ambientIndex (MvPolynomial.X k))) = _
      have hseed (i : Fin 2) : ambientIndex i.castSucc.castSucc = some (some i) := by
        unfold ambientIndex
        rw [Equiv.trans_apply, finSuccEquivLast_castSucc]
        change some (finSuccEquivLast i.castSucc) = _
        rw [finSuccEquivLast_castSucc]
      have h0 : ambientIndex 0 = some (some 0) := hseed 0
      have h1 : ambientIndex 1 = some (some 1) := hseed 1
      have h2 : ambientIndex 2 = some none := by
        change ambientIndex (Fin.last 2).castSucc = _
        unfold ambientIndex
        rw [Equiv.trans_apply, finSuccEquivLast_castSucc]
        change some (finSuccEquivLast (Fin.last 2)) = _
        rw [finSuccEquivLast_last]
      have h3 : ambientIndex 3 = none := by
        change ambientIndex (Fin.last 3) = _
        unfold ambientIndex
        rw [Equiv.trans_apply, finSuccEquivLast_last]
        rfl
      fin_cases k <;>
        simp [unflatten_apply, h0, h1, h2, h3, toJet, toRoot, rootIncl, rootSeeds]
  apply RingHom.ext
  intro P
  have hp := DFunLike.congr_fun h (ambientToJet.symm P)
  change toJet (ambientToJet (ambientToJet.symm P)) = ambientToJet.symm P at hp
  rwa [RingEquiv.apply_symm_apply] at hp

private def jetWeight : Variables → ℕ := fun o => o.elim 1 (fun a => a.elim 1 fun _ => 0)
private def seedWeight : Variables → ℕ := fun o => o.elim 0 (fun a => a.elim 0 fun _ => 1)

private theorem jetWeight_apply (j i : ℕ) (d : Fin 2 →₀ ℕ) :
    ((d.optionElim i).optionElim j).weight jetWeight = i + j := by
  unfold jetWeight
  rw [Finsupp.weight_optionElim, Finsupp.weight_elim_one_zero,
    Finsupp.optionElim_apply_none, one_mul, Nat.add_comm]

private theorem seedWeight_apply (j i : ℕ) (d : Fin 2 →₀ ℕ) :
    ((d.optionElim i).optionElim j).weight seedWeight = d.degree := by
  unfold seedWeight
  rw [Finsupp.weight_optionElim, Finsupp.weight_optionElim,
    zero_mul, zero_add, zero_mul, zero_add, ← Finsupp.degree_eq_weight_one]

private def rowDegree (weight : Variables → ℕ) (P : Jet) : ℕ :=
  (unflatten.symm P).weightedTotalDegree weight

private theorem rowDegree_mul (weight : Variables → ℕ) {P Q : Jet}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    rowDegree weight (P * Q) = rowDegree weight P + rowDegree weight Q := by
  unfold rowDegree
  rw [map_mul, MvPolynomial.weightedTotalDegree_mul]
  · simpa using hP
  · simpa using hQ

private theorem rowDegree_le_iff (weight : Variables → ℕ) (P : Jet) (n : ℕ) :
    rowDegree weight P ≤ n ↔
      ∀ j i (d : Fin 2 →₀ ℕ), ((P.coeff j).coeff i).coeff d ≠ 0 →
        ((d.optionElim i).optionElim j).weight weight ≤ n := by
  rw [rowDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h j i d hd
    apply h
    exact MvPolynomial.mem_support_iff.mpr (by rwa [flatten_coeff])
  · intro h e he
    have heq : (e.some.some.optionElim (e.some none)).optionElim (e none) = e := by
      rw [Finsupp.optionElim_some, Finsupp.optionElim_some]
    rw [← heq]
    exact h _ _ _ (by rw [← flatten_coeff, heq]; exact MvPolynomial.mem_support_iff.mp he)

private theorem jetDegree_le_iff (P : Jet) (b : ℕ) :
    rowDegree jetWeight P ≤ b ↔
      ∀ j i, (P.coeff j).coeff i ≠ 0 → i + j ≤ b := by
  rw [rowDegree_le_iff]
  simp only [jetWeight_apply]
  constructor
  · intro h j i hji
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun hz => hji (MvPolynomial.support_eq_empty.mp hz))
    exact h j i d (MvPolynomial.mem_support_iff.mp hd)
  · intro h j i d hd
    exact h j i (fun hz => hd (by simp [hz]))

private theorem seedDegree_le_iff (P : Jet) (u : ℕ) :
    rowDegree seedWeight P ≤ u ↔ ∀ j i, ((P.coeff j).coeff i).totalDegree ≤ u := by
  rw [rowDegree_le_iff]
  simp only [seedWeight_apply, MvPolynomial.totalDegree, Finset.sup_le_iff,
    MvPolynomial.mem_support_iff]
  exact ⟨fun h j i d hd => h j i d hd, fun h j i d hd => h j i d hd⟩

private theorem ordinary_degrees {H : Equation} (hH : H ≠ 0) :
    H.natDegree ≤ rowDegree jetWeight (C H) ∧
      seedDegree H ≤ rowDegree seedWeight (C H) := by
  constructor
  · have htop : H.coeff H.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hH
    simpa using (jetDegree_le_iff _ _).mp le_rfl 0 H.natDegree (by simpa using htop)
  · apply Finset.sup_le
    intro i _
    simpa using (seedDegree_le_iff (C H) _).mp le_rfl 0 i

private theorem factor_caps {P D T : Jet} {H : Equation} {s : Shape}
    (hP : P ≠ 0) (hH : H ≠ 0) (hcap : RowCaps P s)
    (hf : P = D * (C H * T)) :
    seedDegree H ≤ s.U ∧ H.natDegree ≤ s.B ∧
      RowCaps T (residualShape s (seedDegree H) H.natDegree) := by
  have hprod : D * (C H * T) ≠ 0 := by rw [← hf]; exact hP
  have hD := left_ne_zero_of_mul hprod
  have hCT := right_ne_zero_of_mul hprod
  have hC := left_ne_zero_of_mul hCT
  have hT := right_ne_zero_of_mul hCT
  have hB : rowDegree jetWeight P ≤ s.B :=
    (jetDegree_le_iff _ _).mpr fun j i h => (hcap j i h).1
  have hU : rowDegree seedWeight P ≤ s.U := (seedDegree_le_iff _ _).mpr fun j i => by
    by_cases h : (P.coeff j).coeff i = 0
    · simp [h]
    · exact (hcap j i h).2.2
  have hJ : P.natDegree ≤ s.J := by
    have hp : P.coeff P.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hP
    obtain ⟨i, hi⟩ := support_nonempty.mpr hp
    exact (hcap _ i (mem_support_iff.mp hi)).2.1
  rw [hf, rowDegree_mul _ hD hCT, rowDegree_mul _ hC hT] at hB hU
  rw [hf, natDegree_mul hD hCT, natDegree_mul hC hT] at hJ
  obtain ⟨hOrd, hSeed⟩ := ordinary_degrees hH
  refine ⟨by omega, by omega, ?_⟩
  have hbT : rowDegree jetWeight T ≤ s.B - H.natDegree := by omega
  have huT : rowDegree seedWeight T ≤ s.U - seedDegree H := by omega
  intro j i hij
  have hb := (jetDegree_le_iff T _).mp hbT j i hij
  have hu := (seedDegree_le_iff T _).mp huT j i
  have hjT := le_natDegree_of_ne_zero (show T.coeff j ≠ 0 from fun hz => hij (by simp [hz]))
  exact ⟨hb, Nat.le_min.mpr ⟨by omega, by omega⟩, hu⟩

private theorem fixed_of_not_usesSeed (F : Jet) (h : ¬ UsesSeed F) :
    ∃ G : ODE, fixedIncl G = F := by
  refine ⟨F.map (mapRingHom MvPolynomial.constantCoeff), ?_⟩
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  simp only [fixedIncl, K1_14_3.fixedEmbedding, coe_mapRingHom, coeff_map]
  have hz : ((F.coeff j).coeff i).totalDegree = 0 :=
    Nat.eq_zero_of_not_pos (fun hi => h ⟨j, i, hi⟩)
  exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz).symm

private theorem natDegree_zero_of_factors (D : Jet)
    (h : ∀ G : Jet, Irreducible G → G ∣ D → G.natDegree = 0) : D.natDegree = 0 := by
  induction D using WfDvdMonoid.induction_on_irreducible with
  | zero => exact natDegree_zero
  | unit D hD => exact natDegree_eq_zero_of_isUnit hD
  | mul Q G hQ hG ih =>
    rw [natDegree_mul hG.ne_zero hQ, h G hG (dvd_mul_right _ _),
      ih (fun F hF hd => h F hF (dvd_mul_of_dvd_right hd G)), zero_add]

private theorem dvd_of_dvd_residual {P F : Jet} {s : Shape} (A : FixedPart P s)
    (h : F ∣ A.residual) : F ∣ P :=
  calc
    F ∣ fixedIncl A.equation * A.residual :=
      dvd_mul_of_dvd_right (α := Jet) h (fixedIncl A.equation)
    _ = P := A.factorization.symm

theorem proof : K1_14_2_2_4.c1 := by
  intro w rows i B A
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D := Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D := Equation)
  let gcdJet : GCDMonoid Jet := UniqueFactorizationMonoid.toGCDMonoid Jet
  let D : Jet := gcdJet.gcd A.cheap.residual A.layered.residual
  obtain ⟨P, Q, hP, hQ, hrel⟩ := @extract_gcd Jet _ gcdJet A.cheap.residual A.layered.residual
  change A.cheap.residual = D * P at hP
  change A.layered.residual = D * Q at hQ
  have hF : B.cheap = fixedIncl A.cheap.equation * (D * P) :=
    A.cheap.factorization.trans (congrArg (fixedIncl A.cheap.equation * ·) hP)
  have hG : B.layered = fixedIncl A.layered.equation * (D * Q) :=
    A.layered.factorization.trans (congrArg (fixedIncl A.layered.equation * ·) hQ)
  have hFne : fixedIncl A.cheap.equation * (D * P) ≠ 0 := by rw [← hF]; exact B.cheap_ne
  have hGne : fixedIncl A.layered.equation * (D * Q) ≠ 0 := by rw [← hG]; exact B.layered_ne
  have hDne := left_ne_zero_of_mul (right_ne_zero_of_mul hFne)
  have hPne := right_ne_zero_of_mul (right_ne_zero_of_mul hFne)
  have hQne := right_ne_zero_of_mul (right_ne_zero_of_mul hGne)
  have hDdeg : D.natDegree = 0 := by
    apply natDegree_zero_of_factors
    intro F hIrr hfd
    by_contra hpos
    have hd : 0 < F.natDegree := Nat.pos_of_ne_zero hpos
    have hcheap : F ∣ A.cheap.residual :=
      hfd.trans (gcdJet.gcd_dvd_left A.cheap.residual A.layered.residual)
    have hlayered : F ∣ A.layered.residual :=
      hfd.trans (gcdJet.gcd_dvd_right A.cheap.residual A.layered.residual)
    by_cases hseed : UsesSeed F
    · exact B.no_moving F hIrr (dvd_of_dvd_residual A.cheap hcheap) hd hseed
        (dvd_of_dvd_residual A.layered hlayered)
    · obtain ⟨G, rfl⟩ := fixed_of_not_usesSeed F hseed
      exact A.cheap.stripped G hIrr hcheap
  let H := D.coeff 0
  have hD : D = C H := eq_C_of_natDegree_eq_zero hDdeg
  have hH : H ≠ 0 := fun hz => hDne (by rw [hD, hz, map_zero])
  rw [hD] at hF hG
  obtain ⟨hFu, hFb, hPc⟩ := factor_caps B.cheap_ne hH B.cheap_caps hF
  obtain ⟨hGu, hGb, hQc⟩ := factor_caps B.layered_ne hH B.layered_caps hG
  have hprime : IsRelPrime (toJet P) (toJet Q) := by
    have hr := (@gcd_isUnit_iff_isRelPrime Jet _ gcdJet P Q).mp hrel
    rw [toJet_equiv]
    intro E hEP hEQ
    have h1 : ambientToJet E ∣ P := by
      simpa using map_dvd ambientToJet.toRingHom hEP
    have h2 : ambientToJet E ∣ Q := by
      simpa using map_dvd ambientToJet.toRingHom hEQ
    simpa using (hr h1 h2).map ambientToJet.symm.toRingHom
  exact ⟨⟨H, P, Q, hH, hPne, hQne, hF, hG, hprime, le_min hFu hGu,
    le_min hFb hGb, hPc, hQc⟩⟩

end
end K1_14_2_2_4_1
end PackSource_K1_14_2_2_4_1Proof

section PackSource_K1_14_2_2_7_3_3_1Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace K1_14_2_2_7_3_3_1

noncomputable section

open K1_13_6_3_5_3 (CurveField CurvePlace poleOrder)
open K1_13_6_3_5_3_3 (finite_of_transcendental poleOrder_eq_zero_iff)
open K1_14_2_2_7_3_3 (PoleProfile)
open K1_14_3R_3_1 (functionDegree jetPencilDegree pencilAlgebra toFunction)
open K1_14_3R_3_1_3 (GaussAt PlaceResidue exists_gauss_extension inverseChart
  pencilAlgebra_polynomial placeWeight weightedPoleDegree)
open scoped BigOperators Polynomial WithZero

/-- The inverse polynomial chart has finite normalization, including for inseparable maps. -/
def c1 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (x : F),
    Transcendental k x → Module.Finite (IntermediateField.adjoin k {x}) F →
      Module.Finite k[X] (inverseChart (k := k) x)

/-- The normalized fibre over zero computes the weighted pole degree. -/
def c2 : Prop := K1_14_3R_3_1_3.c2

/-- A Gauss extension preserves the residue degree over the extended constants. -/
def c3 : Prop := K1_14_3R_3_1_3.c4

/-- The places contributing to the pencil come from Gauss extension. -/
def c4 : Prop := K1_14_3R_3_1_3.c5

section Poles

variable {k F : Type} [Field k] [Field F] [Algebra k F]

private theorem pole_value_mono : Monotone (fun a : ℤᵐ⁰ => (WithZero.log a).toNat) := by
  intro a b hab
  by_cases ha : a = 0
  · simp [ha]
  · exact Int.toNat_le_toNat ((WithZero.log_le_log ha
      (ne_of_gt ((WithZero.pos_iff_ne_zero.mpr ha).trans_le hab))).mpr hab)

private theorem pole_add (p : CurvePlace k F) (a b : F) :
    poleOrder p.value (a + b) ≤ max (poleOrder p.value a) (poleOrder p.value b) :=
  (pole_value_mono (p.value.map_add a b)).trans pole_value_mono.map_max.le

private theorem pole_mul (p : CurvePlace k F) (a b : F) :
    poleOrder p.value (a * b) ≤ poleOrder p.value a + poleOrder p.value b := by
  unfold poleOrder
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  rw [map_mul, WithZero.log_mul (by simpa using ha) (by simpa using hb)]
  omega

private theorem pole_scalar (p : CurvePlace k F) (a : k) :
    poleOrder p.value (algebraMap k F a) = 0 := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [poleOrder]
  · simp [poleOrder, p.on_constants a ha]

private theorem pole_of_algebraic (p : CurvePlace k F) {x : F} (hx : IsAlgebraic k x) :
    poleOrder p.value x = 0 := by
  let : p.value.IsTrivialOn k := ⟨p.on_constants⟩
  obtain rfl | hx0 := eq_or_ne x 0
  · simp [poleOrder]
  · have hv : p.value x = 1 := by
      by_contra h
      exact (Valuation.transcendental_of_ne_one k x hx0 h) hx
    simp [poleOrder, hv]

private theorem poles_and_degree (h1 : c1) (h2 : c2) (hF : CurveField k F) (x : F) :
    (fun p : CurvePlace k F => poleOrder p.value x).HasFiniteSupport ∧
      (∀ p : CurvePlace k F, poleOrder p.value x ≠ 0 →
        FiniteDimensional k (PlaceResidue p)) ∧
      weightedPoleDegree (k := k) x = functionDegree k x := by
  by_cases hx : IsAlgebraic k x
  · have hp : ∀ p : CurvePlace k F, poleOrder p.value x = 0 :=
      fun p => pole_of_algebraic p hx
    refine ⟨?_, fun p h => (h (hp p)).elim, ?_⟩
    · simp [Function.HasFiniteSupport, Function.support, hp]
    · simp [weightedPoleDegree, functionDegree, hx, hp]
  · have hfinite := finite_of_transcendental hF hx
    exact h2 k F x hx hfinite (h1 k F x hx hfinite)

private theorem residue_finite (h1 : c1) (h2 : c2) (hF : CurveField k F) (p : CurvePlace k F) :
    FiniteDimensional k (PlaceResidue p) := by
  obtain ⟨a, ha⟩ := p.normalized (WithZero.exp 1)
  have h : poleOrder p.value a ≠ 0 := by simp [poleOrder, ha]
  exact (poles_and_degree h1 h2 hF a).2.1 p h

end Poles

section Pencil

variable {k F : Type} [Field k] [Field F] [Algebra k F]

local instance : Algebra (RatFunc k) (RatFunc F) := pencilAlgebra k (F := F)

private theorem gauss_constants {p : CurvePlace k F} {q : CurvePlace (RatFunc k) (RatFunc F)}
    (h : GaussAt p q) (x : F) : q.value (RatFunc.C x) = p.value x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · simpa [Polynomial.support_C hx] using h (Polynomial.C x)

private theorem place_ext {p q : CurvePlace k F} (h : p.value = q.value) : p = q := by
  cases p
  cases q
  cases h
  rfl

private theorem gauss_unique {p : CurvePlace k F} {q r : CurvePlace (RatFunc k) (RatFunc F)}
    (hq : GaussAt p q) (hr : GaussAt p r) : q = r := by
  apply place_ext
  apply Valuation.ext
  intro a
  induction a using RatFunc.induction_on with
  | _ P Q hQ => rw [q.value.map_div, r.value.map_div, hq P, hq Q, hr P, hr Q]

private def pencil (x y : F) : RatFunc F := RatFunc.C x + RatFunc.X * RatFunc.C y

private theorem gauss_pencil {p : CurvePlace k F} {q : CurvePlace (RatFunc k) (RatFunc F)}
    (h : GaussAt p q) (x y : F) :
    poleOrder q.value (pencil x y) = max (poleOrder p.value x) (poleOrder p.value y) := by
  let P : F[X] := Polynomial.C x + Polynomial.X * Polynomial.C y
  have hP : algebraMap F[X] (RatFunc F) P = pencil x y := by
    simp only [P, pencil, map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hc0 : P.coeff 0 = x := by simp [P]
  have hc1 : P.coeff 1 = y := by simp [P]
  have hrest (i : ℕ) (hi : 2 ≤ i) : P.coeff i = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    simp [P, add_comm]
  have hmax : P.support.sup (fun i => p.value (P.coeff i)) = max (p.value x) (p.value y) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      by_cases h0 : i = 0
      · simp [h0, hc0]
      by_cases h1 : i = 1
      · simp [h1, hc1]
      · simp [hrest i (by omega)]
    · have hcoeff (i : ℕ) : p.value (P.coeff i) ≤ P.support.sup (fun j => p.value (P.coeff j)) := by
        by_cases hi : P.coeff i = 0
        · simp [hi]
        · exact Finset.le_sup (f := fun j => p.value (P.coeff j))
            (Polynomial.mem_support_iff.mpr hi)
      exact max_le (hc0 ▸ hcoeff 0) (hc1 ▸ hcoeff 1)
  unfold poleOrder
  rw [← hP, h P, hmax, pole_value_mono.map_max]

private theorem pencil_pole_degree (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (hF : CurveField k F) (x y : F) :
    (∑ᶠ p : CurvePlace k F, placeWeight p * max (poleOrder p.value x) (poleOrder p.value y)) =
      jetPencilDegree k x y := by
  classical
  let lift (p : CurvePlace k F) := (exists_gauss_extension p).choose
  have hlift (p : CurvePlace k F) : GaussAt p (lift p) := (exists_gauss_extension p).choose_spec
  have hinj : Function.Injective lift := by
    intro p r he
    apply place_ext
    apply Valuation.ext
    intro a
    rw [← gauss_constants (hlift p), ← gauss_constants (hlift r), he]
  let g (q : CurvePlace (RatFunc k) (RatFunc F)) := placeWeight q * poleOrder q.value (pencil x y)
  have hsupp : Function.support g ⊆ Set.range lift := by
    intro q hq
    rcases h4 k F (residue_finite h1 h2 hF) q with htriv | ⟨p, hp⟩
    · have halg : algebraMap (RatFunc k) (RatFunc F) RatFunc.X = RatFunc.X := by
        simpa only [Polynomial.map_X, RatFunc.algebraMap_X] using
          (pencilAlgebra_polynomial (k := k) (F := F) Polynomial.X)
      have hX : q.value (RatFunc.X : RatFunc F) = 1 := by
        rw [← halg]
        exact q.on_constants _ RatFunc.X_ne_zero
      have hle : q.value (pencil x y) ≤ 1 := by
        unfold pencil
        apply (q.value.map_add _ _).trans
        rw [map_mul, hX, one_mul]
        exact max_le (htriv x) (htriv y)
      exact (hq (by simp [g, (poleOrder_eq_zero_iff _ _).2 hle])).elim
    · exact ⟨p, gauss_unique (hlift p) hp⟩
  have hsum : (∑ᶠ q, g q) = ∑ᶠ q ∈ Set.range lift, g q := by
    rw [← finsum_mem_support g]
    apply finsum_mem_inter_support_eq'
    intro q hq
    simp [hq, hsupp hq]
  calc
    _ = ∑ᶠ p, g (lift p) := by
      apply finsum_congr
      intro p
      simp only [g, gauss_pencil (hlift p), h3 k F p (residue_finite h1 h2 hF p) _ (hlift p)]
    _ = ∑ᶠ q ∈ Set.range lift, g q := (finsum_mem_range hinj).symm
    _ = weightedPoleDegree (k := RatFunc k) (pencil x y) := hsum.symm
    _ = jetPencilDegree k x y := (poles_and_degree h1 h2 (pencil_curve_field hF) _).2.2

end Pencil

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : K1_14_2_2_7_3_3.c1 := by
  classical
  intro k A _ _ _ _ hft hdim x y
  let F := FractionRing A
  have hF : CurveField k F := affine_curve_field hdim
  let order (p : CurvePlace k F) (a : A) := poleOrder p.value (toFunction a)
  have hdegree (a : A) := poles_and_degree h1 h2 hF (toFunction a)
  obtain ⟨T, hT⟩ := hft.out
  let E : Set (CurvePlace k F) := ⋃ a : ↥T, Function.support (fun p => order p a.1)
  have hE : E.Finite := Set.finite_iUnion fun a : ↥T => (hdegree a.1).1
  let S := hE.toFinset
  have hz (p : CurvePlace k F) (hp : p ∉ S) (a : A) : order p a = 0 := by
    have ha : a ∈ Algebra.adjoin k (↑T : Set A) := by rw [hT]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem b hb =>
      by_contra hne
      apply hp
      exact hE.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hne⟩)
    | algebraMap c =>
      simpa [order, toFunction, IsScalarTower.algebraMap_apply k A F] using
        pole_scalar (F := F) p c
    | add a b _ _ ha hb =>
      exact Nat.eq_zero_of_le_zero (by simpa [order, toFunction, ha, hb] using
        (pole_add p (toFunction a) (toFunction b)).trans (show
          max (order p a) (order p b) ≤ 0 by simp [ha, hb]))
    | mul a b _ _ ha hb =>
      exact Nat.eq_zero_of_le_zero (by simpa [order, toFunction, ha, hb] using
        (pole_mul p (toFunction a) (toFunction b)).trans (show
          order p a + order p b ≤ 0 by simp [ha, hb]))
  let e := S.equivFin.symm
  have hsum (g : CurvePlace k F → ℕ) (hg : ∀ p ∉ S, g p = 0) :
      (∑ i, g (e i)) = ∑ᶠ p, g p := by
    rw [e.sum_comp (fun p : S => g p), Finset.sum_coe_sort]
    exact (finsum_eq_finsetSum_of_support_subset _ (fun p hp => by
      by_contra h
      exact hp (hg p h))).symm
  refine ⟨{
    places := S.card
    order := fun i => order (e i)
    weight := fun i => placeWeight (e i : CurvePlace k F)
    scalar := fun i c => by
      simpa [order, toFunction, IsScalarTower.algebraMap_apply k A F] using
        pole_scalar (F := F) (e i) c
    add := fun i a b => by simpa [order, toFunction] using pole_add (e i : CurvePlace k F) (toFunction a) (toFunction b)
    mul := fun i a b => by simpa [order, toFunction] using pole_mul (e i : CurvePlace k F) (toFunction a) (toFunction b)
    degree_eq := fun a => (hsum (fun p => placeWeight p * order p a)
      (fun p hp => by simp [hz p hp a])).trans (hdegree a).2.2
    pencil_eq := ?_ }⟩
  exact (hsum (fun p => placeWeight p * max (order p x) (order p y))
    (fun p hp => by simp [hz p hp x, hz p hp y])).trans
      (pencil_pole_degree h1 h2 h3 h4 hF _ _)

end

end K1_14_2_2_7_3_3_1
end PackSource_K1_14_2_2_7_3_3_1Split

section PackSource_K1_14_2_2_7_3_3_1_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_2_2_7_3_3_1_1

open K1_14_3R_3_1_3 (chartAlgebra)
open K1_14_3R_3_1_3_1 (adjoin_inv finite_normalization fraction_chart fractionChartAlgebra
  polynomial_frobenius_lattices)
open scoped Polynomial

theorem proof : K1_14_2_2_7_3_3_1.c1 := by
  intro k F _ _ _ x hx hfinite
  have hxi : Transcendental k x⁻¹ := fun h => hx (IsAlgebraic.inv_iff.mp h)
  let K := IntermediateField.adjoin k ({x⁻¹} : Set F)
  let : Algebra k[X] F := chartAlgebra x⁻¹
  let : Algebra k[X] K := fractionChartAlgebra x⁻¹ hxi
  have : IsFractionRing k[X] K := (fraction_chart hxi).1
  have : IsScalarTower k[X] K F := (fraction_chart hxi).2
  have : Module.Finite K F := by
    change Module.Finite (IntermediateField.adjoin k ({x⁻¹} : Set F)) F
    rwa [adjoin_inv]
  exact finite_normalization k[X] K F (polynomial_frobenius_lattices k)

end K1_14_2_2_7_3_3_1_1
end PackSource_K1_14_2_2_7_3_3_1_1Proof

section PackSource_K1_14_2_2_7_3_3_1_3Proof
set_option autoImplicit true
namespace K1_14_2_2_7_3_3_1_3

/-- The Gauss extension preserves the residue degree. -/
theorem proof : K1_14_2_2_7_3_3_1.c3 :=
  K1_14_3R_3_1_3_4.proof

end K1_14_2_2_7_3_3_1_3
end PackSource_K1_14_2_2_7_3_3_1_3Proof

section PackSource_K1_13_5_4_4_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_4_1

noncomputable section

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_4
open scoped Polynomial

/-- Evaluate fresh coefficient polynomials at a point over the old constants. -/
def point (a : Coefficients) : FreshCoeffRing →+* FreshField :=
  MvPolynomial.eval fun j => algebraMap GeometricX FreshField (a j)

theorem point_X (a : Coefficients) (i : Fin taylorLength) :
    point a (MvPolynomial.X i) = algebraMap GeometricX FreshField (a i) :=
  MvPolynomial.eval_X i

theorem point_C (a : Coefficients) (c : FreshField) :
    point a (MvPolynomial.C c) = c :=
  MvPolynomial.eval_C c

/-- Cleared order-two jets evaluated along a polynomial solution, through
the first Hasse derivative above the message degree. -/
def CompatibilityIdentity (f : Row 3) (S : GeometricX[X]) : Prop :=
  ∀ k : ℕ, k + 3 ≤ taylorLength →
    2 * extendedAtJet (compatibilityNumerator f k) S =
      extendedAtJet (separant f) S ^ (2 * k + 1) *
        (((k + 3).factorial : GeometricX[X]) * Polynomial.hasseDeriv (k + 3) S)

end

end K1_13_5_4_4_1
end PackSource_K1_13_5_4_4_1Defs

section PackSource_K1_13_5_4_4_1Recovery
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace K1_13_5_4_4_1

noncomputable section

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_4 Polynomial
open scoped BigOperators

private abbrev incl : GeometricX[X] →+* FreshField := algebraMap _ _

theorem coefficientPolynomial_degree (a : Coefficients) :
    (coefficientPolynomial a).natDegree < taylorLength := by
  apply Nat.lt_succ_of_le
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt j.isLt)

private def pointPolynomial {n : ℕ} (a : Fin n → GeometricX) : GeometricX[X] :=
  ∑ j : Fin n, Polynomial.monomial j.val (a j)

private theorem pointPolynomial_coeff {n : ℕ} (a : Fin n → GeometricX) (i : Fin n) :
    (pointPolynomial a).coeff i.val = a i := by
  classical
  rw [pointPolynomial, finsetSum_coeff, Finset.sum_eq_single i]
  · exact coeff_monomial_same _ _
  · intro j _ h
    exact coeff_monomial_of_ne _ (fun e => h (Fin.ext e.symm))
  · simp

private theorem pointPolynomial_eq (a : Coefficients) :
    pointPolynomial (n := taylorLength) a = coefficientPolynomial a := rfl

def jetEval (a : Coefficients) : FreshJetRing →+* FreshField :=
  (point a).comp freshProjection.toRingHom

theorem point_projected (a : Coefficients) (b : FreshJetRing) :
    point a (freshProjection b) = jetEval a b := rfl

private theorem eval_jet (a : Coefficients) (i : Fin 3) :
    jetEval a (MvPolynomial.X i) = incl (hasseDeriv i.val (coefficientPolynomial a)) := by
  change point a (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]
  simp only [K1_13_5_5.jetForm, coefficientPolynomial, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_monomial, ← C_mul_X_pow_eq_monomial]
  simp only [map_mul, point_C, point_X, freshArgument, map_pow]
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply GeometricX GeometricX[X] FreshField]
  simp only [map_natCast]
  ac_rfl

private theorem eval_constant (a : Coefficients) (c : FreshField) :
    jetEval a (MvPolynomial.C c) = c := by
  change point a (MvPolynomial.aeval _ (MvPolynomial.C c)) = _
  rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, point_C]

theorem eval_row (a : Coefficients) (P : Row 3) :
    jetEval a (freshRow P) = incl (extendedAtJet P (coefficientPolynomial a)) := by
  unfold freshRow extendedAtJet
  rw [MvPolynomial.eval_map]
  change (jetEval a |>.comp (MvPolynomial.map freshCoeff)) P =
    (incl.comp (MvPolynomial.eval₂Hom (Polynomial.mapRingHom (algebraMap Geom GeometricX))
      (fun j : Fin 3 => hasseDeriv j.val (coefficientPolynomial a)))) P
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro p
    simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C,
      eval_constant, freshCoeff, Polynomial.coe_mapRingHom]
  · intro i
    simp only [RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', eval_jet]

private theorem factorial_ne_zero {n : ℕ} (h : n < K1.p) :
    (n.factorial : FreshField) ≠ 0 := by
  let g : K1.K →+* FreshField := (algebraMap Geom FreshField).comp embed
  intro hz
  have hK : (n.factorial : K1.K) = 0 :=
    g.injective (by simpa only [map_natCast, map_zero] using hz)
  have hp := CharP.char_is_prime_of_two_le K1.K K1.p (by decide)
  exact (not_le_of_gt h) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K1.K K1.p _).mp hK))

private abbrev exponent : ℕ := 2 * taylorLength

def sepRow (f : Row 3) : FreshJetRing := freshRow (separant f)

private def paddedJet (f : Row 3) : ℕ → FreshJetRing
  | 0 => sepRow f ^ exponent * MvPolynomial.X 0
  | 1 => sepRow f ^ exponent * MvPolynomial.X 1
  | 2 => sepRow f ^ exponent * MvPolynomial.X 2
  | k + 3 => MvPolynomial.C (2 / ((k + 3).factorial : FreshField)) *
      sepRow f ^ (exponent - (2 * k + 1)) * freshRow (compatibilityNumerator f k)

private theorem eval_paddedJet (f : Row 3) (a : Coefficients)
    (hrec : CompatibilityIdentity f (coefficientPolynomial a))
    (j : ℕ) (hj : j < taylorLength) :
    jetEval a (paddedJet f j) =
      jetEval a (sepRow f) ^ exponent * incl (hasseDeriv j (coefficientPolynomial a)) := by
  rcases j with _ | _ | _ | k
  · simp only [paddedJet, map_mul, map_pow, eval_jet]
    rfl
  · simp only [paddedJet, map_mul, map_pow, eval_jet]
    rfl
  · simp only [paddedJet, map_mul, map_pow, eval_jet]
    rfl
  let s := jetEval a (sepRow f)
  let y := incl (hasseDeriv (k + 3) (coefficientPolynomial a))
  let u := jetEval a (freshRow (compatibilityNumerator f k))
  let c : FreshField := (k + 3).factorial
  have he : 2 * u = s ^ (2 * k + 1) * (c * y) := by
    have h := congrArg incl (hrec k (Nat.le_of_lt hj))
    simpa only [map_mul, map_pow, map_ofNat, map_natCast, ← eval_row, u, s, y, c, sepRow] using h
  have hc : c ≠ 0 := factorial_ne_zero (hj.trans (by decide : taylorLength < K1.p))
  have hk : 2 * k + 1 ≤ exponent := by
    change 2 * k + 1 ≤ 2 * taylorLength
    omega
  simp only [paddedJet, map_mul, map_pow, eval_constant]
  change 2 / c * s ^ (exponent - (2 * k + 1)) * u = s ^ exponent * y
  rw [div_eq_mul_inv]
  calc
    _ = (s ^ (exponent - (2 * k + 1)) * c⁻¹) * (2 * u) := by ac_rfl
    _ = (s ^ (exponent - (2 * k + 1)) * s ^ (2 * k + 1)) * (c⁻¹ * c) * y := by
      rw [he]
      ac_rfl
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hk, inv_mul_cancel₀ hc, mul_one]

private theorem fresh_taylor_coeff (S : GeometricX[X]) (j : ℕ) :
    (taylor freshArgument (S.map (algebraMap GeometricX FreshField))).coeff j =
      incl (hasseDeriv j S) := by
  rw [taylor_coeff, hasseDeriv_map, Polynomial.eval_map]
  have h : Polynomial.eval₂RingHom (algebraMap GeometricX FreshField) freshArgument = incl := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact IsScalarTower.algebraMap_apply GeometricX GeometricX[X] FreshField a
    · exact Polynomial.eval₂_X _ _
  exact RingHom.congr_fun h _

private def weight (j i : ℕ) : FreshField :=
  ((Polynomial.X - Polynomial.C freshArgument) ^ j).coeff i

private theorem inverse_taylor_aux (S : GeometricX[X]) (m i : ℕ) (hS : S.natDegree < m) :
    (∑ j : Fin m, weight j.val i * incl (hasseDeriv j.val S)) =
      algebraMap GeometricX FreshField (S.coeff i) := by
  let P := S.map (algebraMap GeometricX FreshField)
  have hn : (taylor freshArgument P).natDegree < m := by
    rw [natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt hS
  have hsum : (∑ j : Fin m, Polynomial.C ((taylor freshArgument P).coeff j.val) *
      (Polynomial.X - Polynomial.C freshArgument) ^ j.val) = P :=
    (Polynomial.sum_fin (fun j (c : FreshField) =>
      Polynomial.C c * (Polynomial.X - Polynomial.C freshArgument) ^ j)
      (fun _ => by rw [Polynomial.C_0, zero_mul])
      (Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hn))).trans
      (Polynomial.sum_taylor_eq P freshArgument)
  calc
    _ = ∑ j : Fin m, (Polynomial.C ((taylor freshArgument P).coeff j.val) *
        (Polynomial.X - Polynomial.C freshArgument) ^ j.val).coeff i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [weight, coeff_C_mul, show (taylor freshArgument P).coeff j.val =
        incl (hasseDeriv j.val S) from fresh_taylor_coeff _ _, mul_comm]
    _ = P.coeff i := by rw [← finsetSum_coeff, hsum]
    _ = _ := Polynomial.coeff_map _ _

private theorem inverse_taylor (a : Coefficients) (i : Fin taylorLength) :
    (∑ j : Fin taylorLength, weight j.val i.val * incl (hasseDeriv j.val (coefficientPolynomial a))) =
      algebraMap GeometricX FreshField (a i) :=
  (inverse_taylor_aux _ taylorLength i.val (coefficientPolynomial_degree a)).trans
    (congrArg (algebraMap GeometricX FreshField)
      ((congrArg (fun p : GeometricX[X] => p.coeff i.val) (pointPolynomial_eq a).symm).trans
        (pointPolynomial_coeff (n := taylorLength) a i)))

def coefficientNumerator (f : Row 3) (i : Fin taylorLength) : FreshJetRing :=
  ∑ j : Fin taylorLength, MvPolynomial.C (weight j.val i.val) * paddedJet f j.val

private theorem point_recovery_expression (a : Coefficients) (i : Fin taylorLength)
    (b u : FreshJetRing) (n : ℕ) :
    point a (MvPolynomial.X i * freshProjection b ^ n - freshProjection u) =
      algebraMap GeometricX FreshField (a i) * jetEval a b ^ n - jetEval a u := by
  rw [map_sub, map_mul, point_X, map_pow, point_projected, point_projected]

/-- The same cleared coefficient formulas work at all polynomial solutions
of the fixed row, including points where its separant vanishes. -/
theorem recover_at_point (f : Row 3) (a : Coefficients) (i : Fin taylorLength)
    (hrec : CompatibilityIdentity f (coefficientPolynomial a)) :
    point a (MvPolynomial.X i * freshProjection (sepRow f) ^ (2 * taylorLength) -
      freshProjection (coefficientNumerator f i)) = 0 := by
  rw [point_recovery_expression, sub_eq_zero, coefficientNumerator, map_sum, ← inverse_taylor a i, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, eval_constant, eval_paddedJet f a hrec j.val j.isLt]
  exact (mul_assoc _ _ _).trans (congrArg (fun z => weight j.val i.val * z) (mul_comm _ _))

end

end K1_13_5_4_4_1
end PackSource_K1_13_5_4_4_1Recovery

section PackSource_K1_13_5_4_4_1Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace K1_13_5_4_4_1

noncomputable section

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_4
open scoped Polynomial

/-- Purely transcendental extension preserves prime ideals and detects
fresh ideal membership on the embedded old geometric points. -/
def c1 : Prop :=
  ∀ Q : CoefficientIdeal, Q.IsPrime →
    (extendIdeal Q).IsPrime ∧
      ∀ b : FreshCoeffRing, b ∈ extendIdeal Q ↔
        ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q, point a b = 0

/-- The order-two tangent recurrence computes the cleared jets of an
actual polynomial solution in the independent argument. -/
def c2 : Prop :=
  ∀ (f : Row 3) (S : GeometricX[X]), S.natDegree < taylorLength →
    extendedAtJet f S = 0 → CompatibilityIdentity f S

private theorem extend_contract (base : c1) {Q : CoefficientIdeal} (hQ : Q.IsPrime) :
    (extendIdeal Q).comap (MvPolynomial.map (algebraMap GeometricX FreshField)) = Q := by
  let _ := hQ
  ext p
  rw [Ideal.mem_comap, (base Q hQ).2]
  have h (a : Coefficients) :
      point a (MvPolynomial.map (algebraMap GeometricX FreshField) p) =
        algebraMap GeometricX FreshField (MvPolynomial.eval a p) :=
    (MvPolynomial.map_eval (algebraMap GeometricX FreshField) a p).symm
  simp only [h, map_eq_zero_iff _ (algebraMap GeometricX FreshField).injective]
  change p ∈ MvPolynomial.vanishingIdeal GeometricX (MvPolynomial.zeroLocus GeometricX Q) ↔ p ∈ Q
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]

private theorem eval_cut_zero (rec : c2) (f : Row 3) (S : GeometricX[X])
    (hS : S.natDegree < taylorLength) (hf : extendedAtJet f S = 0)
    (k : ℕ) (hk : k + 3 = taylorLength) :
    extendedAtJet (compatibilityNumerator f k) S = 0 := by
  have h := rec f S hS hf k hk.le
  have hd : S.natDegree < k + 3 := hk.symm ▸ hS
  rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree S (k + 3) hd, mul_zero, mul_zero] at h
  have htwo : (2 : GeometricX[X]) ≠ 0 := by
    let g : K1.K →+* GeometricX[X] :=
      Polynomial.C.comp ((algebraMap Geom GeometricX).comp embed)
    have hne : (2 : K1.K) ≠ 0 := by decide
    exact fun hz => hne (g.injective (by simpa only [map_ofNat, map_zero] using hz))
  exact (mul_eq_zero.mp h).resolve_left htwo

private theorem eval_oldCut_zero (rec : c2) (f : Row 3) (S : GeometricX[X])
    (hS : S.natDegree < taylorLength) (hf : extendedAtJet f S = 0) :
    extendedAtJet (oldCut f) S = 0 :=
  eval_cut_zero rec f S hS hf (taylorLength - 3) rfl

private theorem recover_coefficient (base : c1) (rec : c2) (f : Row 3) (i : Fin taylorLength)
    {Q : CoefficientIdeal} (h : ActualSolutionCurve f Q) :
    MvPolynomial.X i * freshProjection (sepRow f) ^ (2 * taylorLength) -
      freshProjection (coefficientNumerator f i) ∈ extendIdeal Q := by
  rw [(base Q h.prime).2]
  intro a ha
  exact recover_at_point f a i
    (rec f _ (coefficientPolynomial_degree a) (h.solves a ha))

private theorem fresh_on_divisor (base : c1) (rec : c2) {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) :
    freshDivisor f ≤ freshImage Q := by
  have vanishes (b : Row 3)
      (hb : ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
        extendedAtJet b (coefficientPolynomial a) = 0) : freshRow b ∈ freshImage Q := by
    change freshProjection (freshRow b) ∈ extendIdeal Q
    rw [(base Q h.prime).2]
    intro a ha
    rw [point_projected, eval_row, hb a ha, map_zero]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr (vanishes f h.solves))
    ((Ideal.span_singleton_le_iff_mem _).mpr
      (vanishes (oldCut f) fun a ha =>
        eval_oldCut_zero rec f _ (coefficientPolynomial_degree a) (h.solves a ha)))

private theorem fresh_regular (base : c1) {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) :
    sepRow f ∉ freshImage Q := by
  obtain ⟨a, ha, hs⟩ := h.regular
  intro hm
  have hz := ((base Q h.prime).2 (freshProjection (freshRow (separant f)))).mp hm a ha
  rw [point_projected, eval_row] at hz
  exact hs ((IsFractionRing.injective _ FreshField) (hz.trans (map_zero _).symm))

private theorem multiply_recovery {R : Type*} [CommRing R] (a b c d : R) :
    (a * b) * (c * d) = (a * c) * (b * d) :=
  mul_mul_mul_comm a b c d

/-- Clear a power of the same separant while lifting an arbitrary polynomial
in the coefficient coordinates. The lift only depends on the fixed row. -/
private theorem recover_polynomial (base : c1) (rec : c2) (f : Row 3) (p : FreshCoeffRing) :
    ∃ (u : FreshJetRing) (n : ℕ), ∀ Q : CoefficientIdeal, ActualSolutionCurve f Q →
      p * freshProjection (sepRow f) ^ n - freshProjection u ∈ extendIdeal Q := by
  let s := sepRow f
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨MvPolynomial.C c, 0, fun Q _ => ?_⟩
    simp [freshProjection]
  | add p q ihp ihq =>
    obtain ⟨u, n, hu⟩ := ihp
    obtain ⟨v, m, hv⟩ := ihq
    refine ⟨u * s ^ m + v * s ^ n, n + m, fun Q h => ?_⟩
    let π := Ideal.Quotient.mk (extendIdeal Q)
    have hU := Ideal.Quotient.eq_zero_iff_mem.mpr (hu Q h)
    have hV := Ideal.Quotient.eq_zero_iff_mem.mpr (hv Q h)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π ((p + q) * freshProjection s ^ (n + m) -
      freshProjection (u * s ^ m + v * s ^ n)) = 0
    simp only [map_sub, map_mul, map_add, map_pow, pow_add] at hU hV ⊢
    linear_combination π (freshProjection s) ^ m * hU + π (freshProjection s) ^ n * hV
  | mul_X p i ih =>
    obtain ⟨u, n, hu⟩ := ih
    refine ⟨u * coefficientNumerator f i, n + 2 * taylorLength, fun Q h => ?_⟩
    let π := Ideal.Quotient.mk (extendIdeal Q)
    have hU := Ideal.Quotient.eq_zero_iff_mem.mpr (hu Q h)
    have hV := Ideal.Quotient.eq_zero_iff_mem.mpr (recover_coefficient base rec f i h)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π ((p * MvPolynomial.X i) * freshProjection s ^ (n + 2 * taylorLength) -
      freshProjection (u * coefficientNumerator f i)) = 0
    simp only [map_sub, map_mul, map_pow, pow_add, sub_eq_zero] at hU hV ⊢
    calc
      _ = (π p * π (freshProjection s) ^ n) *
        (π (MvPolynomial.X i) * π (freshProjection s) ^ (2 * taylorLength)) :=
        multiply_recovery (π p) (π (MvPolynomial.X i))
          (π (freshProjection s) ^ n) (π (freshProjection s) ^ (2 * taylorLength))
      _ = _ := by rw [hU, hV]

private theorem membership_from_recovery (base : c1) {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) {p : FreshCoeffRing} {u : FreshJetRing} {n : ℕ}
    (heq : p * freshProjection (sepRow f) ^ n - freshProjection u ∈ extendIdeal Q) :
    p ∈ extendIdeal Q ↔ u ∈ freshImage Q := by
  have hp := (base Q h.prime).1
  have hs : freshProjection (sepRow f) ^ n ∉ extendIdeal Q :=
    fun hm => fresh_regular base h (hp.mem_of_pow_mem n hm)
  change p ∈ extendIdeal Q ↔ freshProjection u ∈ extendIdeal Q
  constructor
  · intro hm
    exact ((extendIdeal Q).sub_mem_iff_right (Ideal.mul_mem_right _ _ hm)).mp heq
  · intro hm
    exact (hp.mem_or_mem (((extendIdeal Q).sub_mem_iff_left hm).mp heq)).resolve_right hs

theorem of_children (base : c1) (rec : c2) : K1_13_5_4_4.c1 := by
  intro f
  constructor
  · intro Q h
    refine ⟨(base Q h.prime).1, fresh_on_divisor base rec h, fresh_regular base h, ?_⟩
    intro i
    refine ⟨coefficientNumerator f i, sepRow f ^ (2 * taylorLength), ?_, ?_⟩
    · intro hm
      exact fresh_regular base h (((base Q h.prime).1).comap freshProjection |>.mem_of_pow_mem _ hm)
    · rw [map_pow, mul_comm]
      exact recover_coefficient base rec f i h
  · intro A hA B hB hij
    change ActualSolutionCurve f A at hA
    change ActualSolutionCurve f B at hB
    have he : extendIdeal A = extendIdeal B := by
      ext p
      obtain ⟨u, n, h⟩ := recover_polynomial base rec f p
      rw [membership_from_recovery base hA (h A hA), membership_from_recovery base hB (h B hB), hij]
    rw [← extend_contract base hA.prime, ← extend_contract base hB.prime, he]

end

end K1_13_5_4_4_1
end PackSource_K1_13_5_4_4_1Split

section PackSource_K1_13_5_4_4_1_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_4_1_1

noncomputable section

open K1_13 K1_13_5_4 K1_13_5_4_4 K1_13_5_4_4_1
open scoped Polynomial nonZeroDivisors

private abbrev OldCoeffRing := GeoRow taylorLength
private abbrev PolynomialCoeffRing := MvPolynomial (Fin taylorLength) GeometricX[X]

attribute [local instance] MvPolynomial.algebraMvPolynomial

private abbrev denominators : Submonoid PolynomialCoeffRing :=
  (nonZeroDivisors GeometricX[X]).map MvPolynomial.C

/-- Move the fresh argument from the coefficient ring to the outside variable. -/
private def transpose : PolynomialCoeffRing ≃+* OldCoeffRing[X] :=
  ((MvPolynomial.optionEquivRight GeometricX (Fin taylorLength)).symm.trans
    (MvPolynomial.optionEquivLeft GeometricX (Fin taylorLength))).toRingEquiv

private theorem transpose_X (i : Fin taylorLength) :
    transpose (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i) := by
  change MvPolynomial.optionEquivLeft GeometricX (Fin taylorLength)
    ((MvPolynomial.optionEquivRight GeometricX (Fin taylorLength)).symm (MvPolynomial.X i)) = _
  rw [← MvPolynomial.optionEquivRight_X_some GeometricX,
    AlgEquiv.symm_apply_apply, MvPolynomial.optionEquivLeft_X_some]

private theorem transpose_C (d : GeometricX[X]) :
    transpose (MvPolynomial.C d) = d.map (MvPolynomial.C : GeometricX →+* OldCoeffRing) := by
  have he : transpose.toRingHom.comp MvPolynomial.C =
      Polynomial.mapRingHom (MvPolynomial.C : GeometricX →+* OldCoeffRing) := by
    apply Polynomial.ringHom_ext
    · intro c
      change transpose (MvPolynomial.C (Polynomial.C c)) = (Polynomial.C c).map MvPolynomial.C
      rw [Polynomial.map_C]
      change MvPolynomial.optionEquivLeft GeometricX (Fin taylorLength)
        ((MvPolynomial.optionEquivRight GeometricX (Fin taylorLength)).symm
          (MvPolynomial.C (Polynomial.C c))) = _
      rw [← MvPolynomial.optionEquivRight_C GeometricX,
        AlgEquiv.symm_apply_apply, MvPolynomial.optionEquivLeft_C]
    · change transpose (MvPolynomial.C Polynomial.X) = Polynomial.X.map MvPolynomial.C
      rw [Polynomial.map_X]
      change MvPolynomial.optionEquivLeft GeometricX (Fin taylorLength)
        ((MvPolynomial.optionEquivRight GeometricX (Fin taylorLength)).symm
          (MvPolynomial.C Polynomial.X)) = _
      rw [← MvPolynomial.optionEquivRight_X_none GeometricX,
        AlgEquiv.symm_apply_apply, MvPolynomial.optionEquivLeft_X_none]
  exact RingHom.congr_fun he d

private def includeOld : OldCoeffRing →+* PolynomialCoeffRing :=
  MvPolynomial.map Polynomial.C

private theorem transpose_includeOld : transpose.toRingHom.comp includeOld = Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change transpose (includeOld (MvPolynomial.C c)) = Polynomial.C (MvPolynomial.C c)
    rw [includeOld, MvPolynomial.map_C, transpose_C, Polynomial.map_C]
  · intro i
    change transpose (includeOld (MvPolynomial.X i)) = Polynomial.C (MvPolynomial.X i)
    rw [includeOld, MvPolynomial.map_X, transpose_X]

private def polynomialIdeal (Q : CoefficientIdeal) : Ideal PolynomialCoeffRing :=
  Q.map includeOld

private theorem polynomialIdeal_comap (Q : CoefficientIdeal) :
    polynomialIdeal Q = (Q.map Polynomial.C).comap transpose.toRingHom := by
  have hm : (polynomialIdeal Q).map transpose.toRingHom = Q.map Polynomial.C := by
    rw [polynomialIdeal, Ideal.map_map, transpose_includeOld]
  rw [← hm]
  exact (Ideal.comap_map_of_bijective transpose.toRingHom transpose.bijective).symm

private theorem mem_polynomialIdeal (Q : CoefficientIdeal) (p : PolynomialCoeffRing) :
    p ∈ polynomialIdeal Q ↔ ∀ n, (transpose p).coeff n ∈ Q := by
  rw [polynomialIdeal_comap, Ideal.mem_comap]
  change transpose p ∈ Q.map Polynomial.C ↔ _
  exact Ideal.mem_map_C_iff

private theorem denominators_disjoint (Q : CoefficientIdeal) (hQ : Q.IsPrime) :
    Disjoint (denominators : Set PolynomialCoeffRing) (polynomialIdeal Q : Set PolynomialCoeffRing) := by
  refine Set.disjoint_left.mpr ?_
  intro p hp hmem
  obtain ⟨d, hd, rfl⟩ := Submonoid.mem_map.mp hp
  apply nonZeroDivisors.ne_zero hd
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  have hn := (mem_polynomialIdeal Q _).mp hmem n
  rw [transpose_C, Polynomial.coeff_map] at hn
  by_contra hne
  exact hQ.ne_top (Q.eq_top_of_isUnit_mem hn ((isUnit_iff_ne_zero.mpr hne).map MvPolynomial.C))

private theorem extend_eq (Q : CoefficientIdeal) :
    extendIdeal Q = (polynomialIdeal Q).map (algebraMap PolynomialCoeffRing FreshCoeffRing) := by
  have h : (algebraMap GeometricX[X] FreshField).comp Polynomial.C =
      algebraMap GeometricX FreshField :=
    RingHom.ext fun c => (IsScalarTower.algebraMap_apply GeometricX GeometricX[X] FreshField c).symm
  rw [extendIdeal, polynomialIdeal, Ideal.map_map, MvPolynomial.algebraMap_def, includeOld]
  congr 1
  apply RingHom.ext
  intro p
  change MvPolynomial.map (algebraMap GeometricX FreshField) p =
    MvPolynomial.map _ (MvPolynomial.map Polynomial.C p)
  rw [MvPolynomial.map_map, h]

private theorem point_numerator (a : Coefficients) (p : PolynomialCoeffRing) :
    point a (algebraMap PolynomialCoeffRing FreshCoeffRing p) =
      algebraMap GeometricX[X] FreshField ((transpose p).map (MvPolynomial.eval a)) := by
  have he : (MvPolynomial.eval fun i => Polynomial.C (a i)) =
      (Polynomial.mapRingHom (MvPolynomial.eval a)).comp transpose.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro d
      change MvPolynomial.eval (fun i => Polynomial.C (a i)) (MvPolynomial.C d) =
        (transpose (MvPolynomial.C d)).map (MvPolynomial.eval a)
      rw [MvPolynomial.eval_C, transpose_C]
      ext n
      simp only [Polynomial.coeff_map, MvPolynomial.eval_C]
    · intro i
      change MvPolynomial.eval (fun j => Polynomial.C (a j)) (MvPolynomial.X i) =
        (transpose (MvPolynomial.X i)).map (MvPolynomial.eval a)
      rw [MvPolynomial.eval_X, transpose_X, Polynomial.map_C, MvPolynomial.eval_X]
  have hcoords : (fun i => algebraMap GeometricX FreshField (a i)) =
      (algebraMap GeometricX[X] FreshField) ∘ (fun i => Polynomial.C (a i)) :=
    funext fun i => IsScalarTower.algebraMap_apply GeometricX GeometricX[X] FreshField (a i)
  rw [MvPolynomial.algebraMap_def, point, hcoords, ← MvPolynomial.map_eval, he]
  rfl

/-- Clearing denominators leaves one old Nullstellensatz test per numerator coefficient. -/
private theorem numerator_iff (Q : CoefficientIdeal) [Q.IsPrime] (p : PolynomialCoeffRing) :
    p ∈ polynomialIdeal Q ↔
      ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
        point a (algebraMap PolynomialCoeffRing FreshCoeffRing p) = 0 := by
  rw [mem_polynomialIdeal]
  simp only [point_numerator, map_eq_zero_iff _ (IsFractionRing.injective GeometricX[X] FreshField),
    Polynomial.ext_iff, Polynomial.coeff_map, Polynomial.coeff_zero]
  have coeff_iff (n : ℕ) : (transpose p).coeff n ∈ Q ↔
      ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q, MvPolynomial.eval a ((transpose p).coeff n) = 0 := by
    change _ ↔ (transpose p).coeff n ∈
      MvPolynomial.vanishingIdeal GeometricX (MvPolynomial.zeroLocus GeometricX Q)
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  exact ⟨fun h a ha n => (coeff_iff n).mp (h n) a ha,
    fun h n => (coeff_iff n).mpr (fun a ha => h a ha n)⟩

private theorem fraction_zero_iff (a : Coefficients) (p : PolynomialCoeffRing) (s : denominators) :
    point a (IsLocalization.mk' FreshCoeffRing p s) = 0 ↔
      point a (algebraMap PolynomialCoeffRing FreshCoeffRing p) = 0 := by
  have he := congrArg (point a) (IsLocalization.mk'_spec FreshCoeffRing p s)
  rw [map_mul] at he
  have hu := (IsLocalization.map_units FreshCoeffRing s).map (point a)
  rw [← he, mul_eq_zero, or_iff_left hu.ne_zero]

theorem proof : K1_13_5_4_4_1.c1 := by
  intro Q hQ
  let _ := hQ
  have hp : (polynomialIdeal Q).IsPrime := by
    rw [polynomialIdeal_comap]
    exact ((Ideal.isPrime_map_C_iff_isPrime Q).mpr hQ).comap _
  have hd := denominators_disjoint Q hQ
  refine ⟨?_, ?_⟩
  · rw [extend_eq]
    exact IsLocalization.isPrime_of_isPrime_disjoint denominators FreshCoeffRing _ hp hd
  · intro b
    obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq denominators b
    have hmem : IsLocalization.mk' FreshCoeffRing p s ∈ extendIdeal Q ↔ p ∈ polynomialIdeal Q := by
      rw [extend_eq, IsLocalization.mk'_mem_iff]
      change p ∈ ((polynomialIdeal Q).map (algebraMap PolynomialCoeffRing FreshCoeffRing)).under
        PolynomialCoeffRing ↔ _
      rw [IsLocalization.under_map_of_isPrime_disjoint denominators FreshCoeffRing hp hd]
    rw [hmem, numerator_iff Q p]
    exact ⟨fun h a ha => (fraction_zero_iff a p s).mpr (h a ha),
      fun h a ha => (fraction_zero_iff a p s).mp (h a ha)⟩

end

end K1_13_5_4_4_1_1
end PackSource_K1_13_5_4_4_1_1Proof

section PackSource_K1_13_5_4_4_1_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_4_1_2

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_5_1 Polynomial
open scoped Polynomial

private theorem extendedAtJet_eq_trajectory (P : Row 3) (S : GeometricX[X]) :
    extendedAtJet P S = trajectory (algebraMap Geom GeometricX) S P := by
  rw [extendedAtJet, MvPolynomial.eval_map]
  rfl

/-- The cleared recurrence holds in the polynomial ring in the independent argument. -/
theorem proof : K1_13_5_4_4_1.c2 := by
  intro f S _ hf k _
  simp only [extendedAtJet_eq_trajectory] at hf ⊢
  rw [K1_13_5_5_1_1.eval_compatibility _ _ _ hf k,
    mul_left_comm (2 : GeometricX[X]), K1_13_5_5_1_1.twice_iterate_derivative_top,
    ← Polynomial.factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul]

end K1_13_5_4_4_1_2
end PackSource_K1_13_5_4_4_1_2Proof

section PackSource_K1_13_5_4_2_5_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1

noncomputable section

open K1_13 K1_13_5 K1_13_5_4_2 MeasureTheory
open scoped BigOperators Pointwise

abbrev OldSpace := Fin 3 → ℝ

/-- Delete the coordinate of the independent last interval. -/
def oldPart (x : ExponentSpace) : OldSpace := fun i => x i.castSucc

/-- The old-coordinate polytope of a native slot. -/
def oldCap (s : Shape) : Set OldSpace :=
  {x | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 ≤ s.b ∧ x 1 + 2 * x 2 ≤ s.j ∧ x 2 ≤ s.t}

def oldSlots : Fin 3 → Set OldSpace :=
  ![oldCap graphBox, oldCap (liftedBox (taylorLength + 1)), oldCap lastBox]

def pairSlots (P Q : Set ExponentSpace) (i j : Fin 3) : Fin 4 → Set OldSpace :=
  ![oldPart '' P, oldPart '' Q, oldSlots i, oldSlots j]

def weightedSum (base : Set OldSpace) (B : Fin 4 → Set OldSpace) (w : Fin 4 → ℝ) : Set OldSpace :=
  base + ∑ i, w i • B i

def corner (S : Finset (Fin 4)) (i : Fin 4) : ℝ := if i ∈ S then 1 else 0

/-- Approach each Boolean point through strictly positive weights. -/
def shiftedCorner (S : Finset (Fin 4)) (n : ℕ) (i : Fin 4) : ℝ :=
  corner S i + 1 / ((n : ℝ) + 1)

def oldVolume (A : Set OldSpace) : ℝ := (volume A).toReal

/-- Each vertex has a contribution from the fixed base and from each varying slot. -/
abbrev VertexChoices := Fin 4 → OldSpace × (Fin 4 → OldSpace)

def vertices (v : VertexChoices) (w : Fin 4 → ℝ) (k : Fin 4) : OldSpace :=
  (v k).1 + ∑ i, w i • (v k).2 i

def tetrahedron (x : Fin 4 → OldSpace) : Set OldSpace := convexHull ℝ (Set.range x)

def orientedDet (x : Fin 4 → OldSpace) : ℝ :=
  Matrix.det (Matrix.of (fun (r c : Fin 3) => x c.succ r - x 0 r))

/-- A common list of tetrahedra valid throughout the positive weight cone.
Their order gives positive signed volumes. -/
structure CommonTriangulation (base : Set OldSpace) (B : Fin 4 → Set OldSpace) (n : ℕ)
    (cells : Fin n → VertexChoices) : Prop where
  union_eq : ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) →
    weightedSum base B w = ⋃ k, tetrahedron (vertices (cells k) w)
  null_inter : ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) →
    Pairwise (fun k l =>
      volume (tetrahedron (vertices (cells k) w) ∩ tetrahedron (vertices (cells l) w)) = 0)
  oriented : ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) → ∀ k, 0 < orientedDet (vertices (cells k) w)

end
end K1_13_5_4_2_5_1
end PackSource_K1_13_5_4_2_5_1Defs

section PackSource_K1_13_5_4_2_5_1Slice
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1

noncomputable section

open K1_13 K1_13_5 K1_13_5_4_2 K1_13_5_4_2_5 MeasureTheory Set
open scoped BigOperators Pointwise

private abbrev splitLast : ExponentSpace ≃ᵐ ℝ × OldSpace :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last 3)

private theorem splitLast_apply (x : ExponentSpace) : splitLast x = (x 3, oldPart x) := by
  refine Prod.ext rfl ?_
  funext i
  change x ((Fin.last 3).succAbove i) = x i.castSucc
  rw [Fin.succAbove_last]

private def cylinder (A : Set OldSpace) (h : ℝ) : Set ExponentSpace :=
  splitLast ⁻¹' (Icc 0 h ×ˢ A)

private theorem first_cylinder {P : Set ExponentSpace} (hP : FirstBody P) :
    P = cylinder (oldPart '' P) 0 := by
  ext x
  simp only [cylinder, mem_preimage, splitLast_apply, mem_prod, mem_Icc, mem_image]
  constructor
  · intro hx
    exact ⟨by rw [hP.zero_height x hx]; exact ⟨le_rfl, le_rfl⟩, x, hx, rfl⟩
  · rintro ⟨⟨hx₀, hx₁⟩, y, hy, hyx⟩
    suffices y = x by rwa [← this]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (hP.zero_height y hy).trans (le_antisymm hx₁ hx₀).symm
    · exact congrFun hyx j

private theorem cap_cylinder (s : Shape) (h : ℕ) :
    capBody s h = cylinder (oldCap s) h := by
  ext x
  simp only [capBody, cylinder, mem_ofPred_eq, mem_preimage, splitLast_apply, mem_prod,
    mem_Icc, oldCap, Fin.forall_iff_castSucc (n := 3)]
  change ((0 ≤ x 3 ∧ ∀ i : Fin 3, 0 ≤ x i.castSucc) ∧
    x 0 + x 1 + x 2 ≤ (s.b : ℝ) ∧ x 1 + 2 * x 2 ≤ (s.j : ℝ) ∧
    x 2 ≤ (s.t : ℝ) ∧ x 3 ≤ (h : ℝ)) ↔ _
  tauto

private theorem cylinder_zero : cylinder 0 0 = 0 := by
  ext x
  simp only [cylinder, mem_preimage, splitLast_apply, mem_prod, Icc_self, mem_singleton_iff,
    mem_zero]
  constructor
  · rintro ⟨h, h'⟩
    funext i
    refine Fin.lastCases h (fun j => congrFun h' j) i
  · rintro rfl
    exact ⟨rfl, rfl⟩

private theorem cylinder_add {A B : Set OldSpace} {h k : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k) :
    cylinder A h + cylinder B k = cylinder (A + B) (h + k) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [cylinder, mem_preimage, splitLast_apply, mem_prod, mem_Icc] at ha hb ⊢
    exact ⟨⟨add_nonneg ha.1.1 hb.1.1, add_le_add ha.1.2 hb.1.2⟩,
      mem_add.mpr ⟨_, ha.2, _, hb.2, rfl⟩⟩
  · intro hx
    simp only [cylinder, mem_preimage, splitLast_apply, mem_prod, mem_Icc] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp hx.2
    let t := min h (x 3)
    have ht₀ : 0 ≤ t := le_min hh hx.1.1
    have ht₁ : t ≤ h := min_le_left _ _
    have hu₀ : 0 ≤ x 3 - t := sub_nonneg.mpr (min_le_right _ _)
    have hu₁ : x 3 - t ≤ k := by
      rcases le_total h (x 3) with he | he
      · dsimp only [t]
        rw [min_eq_left he]
        linarith [hx.1.2]
      · dsimp only [t]
        rw [min_eq_right he, sub_self]
        exact hk
    let y := splitLast.symm (t, a)
    let z := splitLast.symm (x 3 - t, b)
    have hy : splitLast y = (t, a) := splitLast.apply_symm_apply _
    have hz : splitLast z = (x 3 - t, b) := splitLast.apply_symm_apply _
    refine mem_add.mpr ⟨y, ?_, z, ?_, ?_⟩
    · show splitLast y ∈ Icc 0 h ×ˢ A
      rw [hy]
      exact ⟨⟨ht₀, ht₁⟩, ha⟩
    · show splitLast z ∈ Icc 0 k ×ˢ B
      rw [hz]
      exact ⟨⟨hu₀, hu₁⟩, hb⟩
    · apply splitLast.injective
      rw [splitLast_apply y] at hy
      rw [splitLast_apply z] at hz
      rw [splitLast_apply (y + z), splitLast_apply x]
      refine Prod.ext ?_ ?_
      · change y 3 + z 3 = x 3
        rw [(Prod.mk.inj hy).1, (Prod.mk.inj hz).1]
        ring
      · change oldPart y + oldPart z = oldPart x
        rw [(Prod.mk.inj hy).2, (Prod.mk.inj hz).2]
        exact hab

private theorem sum_cylinder {ι : Type} (S : Finset ι) (A : ι → Set OldSpace)
    (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) :
    (∑ i ∈ S, cylinder (A i) (h i)) = cylinder (∑ i ∈ S, A i) (∑ i ∈ S, h i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cylinder_zero]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, ih]
    exact cylinder_add (hh i) (Finset.sum_nonneg fun j _ => hh j)

private theorem cylinder_volume (A : Set OldSpace) {h : ℝ} (hh : 0 ≤ h) :
    (volume (cylinder A h)).toReal = h * oldVolume A := by
  have he : MeasurePreserving splitLast := volume_preserving_piFinSuccAbove _ _
  rw [cylinder, he.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod,
    ENNReal.toReal_mul, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hh]
  rfl

def mixedThree (D C A B : Set OldSpace) : ℝ :=
  oldVolume (D + C + A + B) - oldVolume (D + C + A) - oldVolume (D + C + B) -
    oldVolume (D + A + B) + oldVolume (D + C) + oldVolume (D + A) +
    oldVolume (D + B) - oldVolume D

/-- Expand the Boolean alternating sum once, leaving its summand abstract. -/
theorem alternating_four (f : Finset (Fin 4) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset, (-1 : ℝ) ^ (4 - S.card) * f S) =
      f {0, 1, 2, 3} - f {0, 1, 2} - f {0, 1, 3} - f {0, 2, 3} - f {1, 2, 3} +
      f {0, 1} + f {0, 2} + f {0, 3} + f {1, 2} + f {1, 3} + f {2, 3} -
      f {0} - f {1} - f {2} - f {3} + f ∅ := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  have hlast : ({3} : Finset (Fin 4)).powerset = {∅, {(3 : Fin 4)}} := by decide
  simp only [
    Finset.sum_powerset_insert (a := (0 : Fin 4)) (s := {1, 2, 3}) (by decide),
    Finset.sum_powerset_insert (a := (1 : Fin 4)) (s := {2, 3}) (by decide),
    Finset.sum_powerset_insert (a := (2 : Fin 4)) (s := {3}) (by decide),
    hlast, Finset.sum_insert (by decide : (∅ : Finset (Fin 4)) ∉ {{(3 : Fin 4)}}),
    Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem]
  ring

set_option maxHeartbeats 1200000 in
private theorem height_polarization (P A B C : Set OldSpace) (a b c : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset, (-1 : ℝ) ^ (4 - S.card) *
      ((∑ i ∈ S, (![0, a, b, c] : Fin 4 → ℝ) i) *
        oldVolume (∑ i ∈ S, (![P, A, B, C] : Fin 4 → Set OldSpace) i))) =
      a * mixedThree A P B C + b * mixedThree B P A C + c * mixedThree C P A B := by
  rw [alternating_four]
  simp [Finset.sum_insert, mixedThree]
  simp only [
    (add_assoc : ∀ x y z : Set OldSpace, x + y + z = x + (y + z)),
    (add_comm : ∀ x y : Set OldSpace, x + y = y + x)]
  ring

/-- Split the height factor into its three slot contributions before polarizing in old space. -/
theorem last_eq_three {P : Set ExponentSpace} (hP : FirstBody P) :
    lastMixedVolume P =
      mixedThree (oldSlots 0) (oldPart '' P) (oldSlots 1) (oldSlots 2) +
      ((taylorLength - 1 : ℕ) : ℝ) * mixedThree (oldSlots 1) (oldPart '' P) (oldSlots 0) (oldSlots 2) +
      (taylorLength : ℝ) * mixedThree (oldSlots 2) (oldPart '' P) (oldSlots 0) (oldSlots 1) := by
  let A : Fin 4 → Set OldSpace := ![oldPart '' P, oldSlots 0, oldSlots 1, oldSlots 2]
  let h : Fin 4 → ℝ := ![0, 1, ((taylorLength - 1 : ℕ) : ℝ), (taylorLength : ℝ)]
  have hh (i : Fin 4) : 0 ≤ h i := by
    fin_cases i <;> dsimp [h] <;> positivity
  have hs : ![P, capBody graphBox 1,
      capBody (liftedBox (taylorLength + 1)) (taylorLength - 1), capBody lastBox taylorLength] =
      (fun i => cylinder (A i) (h i)) := by
    funext i
    fin_cases i
    · exact first_cylinder hP
    · change capBody graphBox 1 = cylinder (oldCap graphBox) 1
      simpa only [Nat.cast_one] using cap_cylinder graphBox 1
    · exact cap_cylinder (liftedBox (taylorLength + 1)) (taylorLength - 1)
    · exact cap_cylinder lastBox taylorLength
  unfold lastMixedVolume mixedVolume4
  rw [hs]
  simp_rw [sum_cylinder _ _ _ hh, cylinder_volume _ (Finset.sum_nonneg fun i _ => hh i)]
  simpa only [one_mul, A, h] using
    height_polarization (oldPart '' P) (oldSlots 0) (oldSlots 1) (oldSlots 2)
      1 ((taylorLength - 1 : ℕ) : ℝ) (taylorLength : ℝ)

theorem oldPart_add (P Q : Set ExponentSpace) :
    oldPart '' (P + Q) = oldPart '' P + oldPart '' Q := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨p + q, ⟨p, hp, q, hq, rfl⟩, rfl⟩

end
end K1_13_5_4_2_5_1
end PackSource_K1_13_5_4_2_5_1Slice

section PackSource_K1_13_5_4_2_5_1Boundary
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1

noncomputable section

open K1_13 K1_13_5_4_2 K1_13_5_4_2_5 MeasureTheory Metric Filter Set
open scoped BigOperators Pointwise Topology

private def oldPartLinear : ExponentSpace →ₗ[ℝ] OldSpace where
  toFun := oldPart
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem oldCap_image (s : Shape) : oldPart '' capBody s 0 = oldCap s := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hb, hj, ht, _⟩, rfl⟩
    exact ⟨fun i => hy i.castSucc, hb, hj, ht⟩
  · rintro ⟨hx, hb, hj, ht⟩
    have hlast : (@Fin.snoc 3 (fun _ => ℝ) x 0) 3 = 0 :=
      @Fin.snoc_last 3 (fun _ => ℝ) 0 x
    refine ⟨Fin.snoc x 0, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
      · simpa only [Fin.snoc_castSucc] using hx j
    · exact hb
    · exact hj
    · exact ht
    · rw [hlast]
      positivity
    · funext j
      exact Fin.snoc_castSucc _ _ _

private theorem oldCap_convex (s : Shape) : Convex ℝ (oldCap s) := by
  rw [← oldCap_image]
  exact (capBody_convex s 0).linear_image oldPartLinear

private theorem oldCap_compact (s : Shape) : IsCompact (oldCap s) := by
  have h₁ : IsClosed {x : OldSpace | ∀ i, 0 ≤ x i} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h₂ : IsClosed {x : OldSpace | x 0 + x 1 + x 2 ≤ (s.b : ℝ)} :=
    isClosed_le (by fun_prop) continuous_const
  have h₃ : IsClosed {x : OldSpace | x 1 + 2 * x 2 ≤ (s.j : ℝ)} :=
    isClosed_le (by fun_prop) continuous_const
  have h₄ : IsClosed {x : OldSpace | x 2 ≤ (s.t : ℝ)} :=
    isClosed_le (continuous_apply 2) continuous_const
  refine (isCompact_Icc (a := (0 : OldSpace)) (b := fun _ => (s.b : ℝ))).of_isClosed_subset
    (h₁.inter (h₂.inter (h₃.inter h₄))) ?_
  rintro x ⟨hx, hb, _, _⟩
  refine ⟨hx, fun i => ?_⟩
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  fin_cases i
  · change x 0 ≤ (s.b : ℝ)
    linarith
  · change x 1 ≤ (s.b : ℝ)
    linarith
  · change x 2 ≤ (s.b : ℝ)
    linarith

private theorem oldPart_compact {P : Set ExponentSpace} (hP : FirstBody P) :
    IsCompact (oldPart '' P) := by
  obtain ⟨v, hv, rfl⟩ := hP.polytope
  have hc : IsCompact (convexHull ℝ v) := hv.isCompact_convexHull ℝ
  exact hc.image (continuous_pi fun _ => continuous_apply _)

private theorem oldPart_convex {P : Set ExponentSpace} (hP : FirstBody P) :
    Convex ℝ (oldPart '' P) := by
  obtain ⟨v, _, rfl⟩ := hP.polytope
  exact (convex_convexHull ℝ v).linear_image oldPartLinear

theorem oldSlots_compact (k : Fin 3) : IsCompact (oldSlots k) := by
  fin_cases k
  · exact oldCap_compact _
  · exact oldCap_compact _
  · exact oldCap_compact _

private theorem pairSlots_convex {P Q : Set ExponentSpace} (hP : FirstBody P)
    (hQ : FirstBody Q) (i j : Fin 3) (l : Fin 4) : Convex ℝ (pairSlots P Q i j l) := by
  have hs (k : Fin 3) : Convex ℝ (oldSlots k) := by
    fin_cases k
    · exact oldCap_convex _
    · exact oldCap_convex _
    · exact oldCap_convex _
  fin_cases l
  · exact oldPart_convex hP
  · exact oldPart_convex hQ
  · exact hs i
  · exact hs j

private theorem pairSlots_compact {P Q : Set ExponentSpace} (hP : FirstBody P)
    (hQ : FirstBody Q) (i j : Fin 3) (l : Fin 4) : IsCompact (pairSlots P Q i j l) := by
  fin_cases l
  · exact oldPart_compact hP
  · exact oldPart_compact hQ
  · exact oldSlots_compact i
  · exact oldSlots_compact j

theorem pairSlots_zero {P Q : Set ExponentSpace} (hP : FirstBody P)
    (hQ : FirstBody Q) (i j : Fin 3) (l : Fin 4) : 0 ∈ pairSlots P Q i j l := by
  have hs (k : Fin 3) : 0 ∈ oldSlots k := by
    fin_cases k <;> simp [oldSlots, oldCap]
  fin_cases l
  · exact ⟨0, hP.zero_mem, rfl⟩
  · exact ⟨0, hQ.zero_mem, rfl⟩
  · exact hs i
  · exact hs j

private theorem compact_sum (B : Fin 4 → Set OldSpace) (hB : ∀ i, IsCompact (B i))
    (S : Finset (Fin 4)) : IsCompact (∑ i ∈ S, B i) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact (isCompact_singleton (x := (0 : OldSpace)))
  | @insert i S hi ih => rw [Finset.sum_insert hi]; exact (hB i).add ih

private theorem zero_mem_sum (B : Fin 4 → Set OldSpace) (hB : ∀ i, 0 ∈ B i)
    (S : Finset (Fin 4)) : 0 ∈ (∑ i ∈ S, B i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact Set.mem_add.mpr ⟨0, hB i, 0, ih, zero_add 0⟩

private theorem corner_nonneg (S : Finset (Fin 4)) (i : Fin 4) : 0 ≤ corner S i := by
  unfold corner
  split <;> positivity

private theorem volume_perturbation {A B : Set OldSpace} (hA : IsCompact A) (hB : IsCompact B)
    (h₀ : 0 ∈ B) {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) (hδ₀ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => oldVolume (A + δ n • B)) atTop (𝓝 (oldVolume A)) := by
  obtain ⟨R, hR⟩ := hB.isBounded.exists_norm_le
  have hlow (n : ℕ) : A ⊆ A + δ n • B := by
    intro x hx
    exact Set.mem_add.mpr ⟨x, hx, 0, ⟨0, h₀, smul_zero _⟩, add_zero _⟩
  have hupp (n : ℕ) : A + δ n • B ⊆ cthickening (δ n * R) A := by
    rintro _ ⟨y, hy, _, ⟨z, hz, rfl⟩, rfl⟩
    apply mem_cthickening_of_dist_le _ y _ _ hy
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hδ n)]
    exact mul_le_mul_of_nonneg_left (hR z hz) (hδ n)
  have ht : Tendsto (fun n => volume (cthickening (δ n * R) A)) atTop (𝓝 (volume A)) :=
    (tendsto_measure_cthickening_of_isCompact hA).comp (by simpa using hδ₀.mul_const R)
  have hvol : Tendsto (fun n => volume (A + δ n • B)) atTop (𝓝 (volume A)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun n => measure_mono (hlow n)) (fun n => measure_mono (hupp n))
  exact (ENNReal.tendsto_toReal hA.measure_ne_top).comp hvol

/-- The limiting Boolean weights may annihilate any of the four varying slots. -/
theorem corner_limit {P Q : Set ExponentSpace} (hP : FirstBody P) (hQ : FirstBody Q)
    (k i j : Fin 3) (S : Finset (Fin 4)) :
    Tendsto (fun n => oldVolume (weightedSum (oldSlots k) (pairSlots P Q i j)
        (shiftedCorner S n))) atTop
      (𝓝 (oldVolume (weightedSum (oldSlots k) (pairSlots P Q i j) (corner S)))) := by
  let B := pairSlots P Q i j
  let A := weightedSum (oldSlots k) B (corner S)
  let T := ∑ l : Fin 4, B l
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 ≤ δ n := by dsimp [δ]; positivity
  have he (n : ℕ) : weightedSum (oldSlots k) B (shiftedCorner S n) = A + δ n • T := by
    simp only [weightedSum, A, T]
    have hw (l : Fin 4) :
        shiftedCorner S n l • B l = corner S l • B l + δ n • B l :=
      (pairSlots_convex hP hQ i j l).add_smul (corner_nonneg S l) (hδ n)
    simp only [hw, Finset.sum_add_distrib, Finset.smul_sum, add_assoc]
  change Tendsto (fun n => oldVolume (weightedSum (oldSlots k) B (shiftedCorner S n)))
    atTop (𝓝 (oldVolume A))
  simp only [he]
  exact volume_perturbation
    ((oldSlots_compact k).add (compact_sum _ (fun l => (pairSlots_compact hP hQ i j l).smul _) _))
    (compact_sum B (pairSlots_compact hP hQ i j) _) (zero_mem_sum B (pairSlots_zero hP hQ i j) _)
    hδ tendsto_one_div_add_atTop_nhds_zero_nat

end
end K1_13_5_4_2_5_1
end PackSource_K1_13_5_4_2_5_1Boundary

section PackSource_K1_13_5_4_2_5_1Polarization
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1

noncomputable section

open K1_13_5_4_2
open scoped BigOperators Pointwise

def difference (f : Finset (Fin 4) → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset, (-1 : ℝ) ^ (4 - S.card) * f S

theorem difference_sum {ι : Type} (T : Finset ι) (f : ι → Finset (Fin 4) → ℝ) :
    difference (fun S => ∑ i ∈ T, f i S) = ∑ i ∈ T, difference (f i) := by
  simp only [difference, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem difference_mul (a : ℝ) (f : Finset (Fin 4) → ℝ) :
    difference (fun S => a * f S) = a * difference f := by
  simp only [difference, Finset.mul_sum, mul_left_comm]

private theorem difference_missing (f : Finset (Fin 4) → ℝ) (i : Fin 4)
    (hf : ∀ S, f (insert i S) = f S) : difference f = 0 := by
  let T : Finset (Fin 4) := Finset.univ.erase i
  have hT : i ∉ T := Finset.notMem_erase _ _
  have hu : Finset.univ = insert i T := (Finset.insert_erase (Finset.mem_univ i)).symm
  have hcard : T.card = 3 := by simp [T]
  unfold difference
  rw [hu, Finset.sum_powerset_insert hT, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  have hni : i ∉ S := fun hi => hT (hsub hi)
  have hle : S.card ≤ 3 := (Finset.card_le_card hsub).trans_eq hcard
  have hpow : 4 - S.card = (4 - (S.card + 1)) + 1 := by omega
  rw [Finset.card_insert_of_notMem hni, hf, hpow, pow_succ]
  ring

private def affineCorner (S : Finset (Fin 4)) : Option (Fin 4) → ℝ
  | none => 1
  | some i => corner S i

private theorem difference_three_products (c : Fin 3 → Option (Fin 4) → ℝ) :
    difference (fun S => ∏ j, ∑ i, affineCorner S i * c j i) = 0 := by
  have hprod (S : Finset (Fin 4)) :
      (∏ j, ∑ i, affineCorner S i * c j i) =
        ∑ a : Fin 3 → Option (Fin 4), ∏ j, affineCorner S (a j) * c j (a j) := by
    simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [hprod, difference_sum]
  apply Finset.sum_eq_zero
  intro a _
  let indices (j : Fin 3) := (a j).getD 0
  have hcard : (Finset.univ.image indices).card ≤ 3 := Finset.card_image_le.trans (by decide)
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, i ∉ Finset.univ.image indices := by
    by_contra! h
    have he : Finset.univ.image indices = Finset.univ := Finset.eq_univ_of_forall h
    rw [he] at hcard
    exact (show ¬((Finset.univ : Finset (Fin 4)).card ≤ 3) by decide) hcard
  apply difference_missing _ i
  intro S
  apply Finset.prod_congr rfl
  intro j _
  cases hj : a j with
  | none => rfl
  | some k =>
    have hki : k ≠ i := by
      intro e
      apply hi
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simp [indices, hj, e]⟩
    simp [affineCorner, corner, hki]

/-- Each determinant term uses three affine factors, so four Boolean differences kill it. -/
theorem difference_det (v : VertexChoices) :
    difference (fun S => orientedDet (vertices v (corner S))) = 0 := by
  let coord (k : Fin 4) (r : Fin 3) : Option (Fin 4) → ℝ
    | none => (v k).1 r
    | some i => (v k).2 i r
  have hentry (S : Finset (Fin 4)) (r j : Fin 3) :
      vertices v (corner S) j.succ r - vertices v (corner S) 0 r =
        ∑ i, affineCorner S i * (coord j.succ r i - coord 0 r i) := by
    simp only [vertices, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_option, affineCorner, coord, one_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [orientedDet, Matrix.det_apply', Matrix.of_apply, hentry]
  rw [difference_sum]
  apply Finset.sum_eq_zero
  intro σ _
  rw [difference_mul, difference_three_products, mul_zero]

theorem weighted_corner (base : Set OldSpace) (B : Fin 4 → Set OldSpace) (hB : ∀ i, (B i).Nonempty)
    (S : Finset (Fin 4)) : weightedSum base B (corner S) = base + ∑ i ∈ S, B i := by
  unfold weightedSum
  congr 1
  calc
    _ = ∑ i : Fin 4, if i ∈ S then B i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [corner, hi, Set.zero_smul_set (hB i)]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem mixedThree_add_of_difference {P Q : Set ExponentSpace} {k i j : Fin 3}
    (hB : ∀ l, (pairSlots P Q i j l).Nonempty)
    (h : difference (fun S => oldVolume (weightedSum (oldSlots k) (pairSlots P Q i j) (corner S))) = 0) :
    mixedThree (oldSlots k) (oldPart '' P + oldPart '' Q) (oldSlots i) (oldSlots j) =
      mixedThree (oldSlots k) (oldPart '' P) (oldSlots i) (oldSlots j) +
        mixedThree (oldSlots k) (oldPart '' Q) (oldSlots i) (oldSlots j) := by
  simp only [weighted_corner _ _ hB, difference, alternating_four] at h
  simp [Finset.sum_insert, pairSlots] at h
  simp only [mixedThree]
  simp only [
    (add_assoc : ∀ x y z : Set OldSpace, x + y + z = x + (y + z)),
    (add_comm : ∀ x y : Set OldSpace, x + y = y + x),
    (add_left_comm : ∀ x y z : Set OldSpace, x + (y + z) = y + (x + z))] at h ⊢
  linear_combination h

end
end K1_13_5_4_2_5_1
end PackSource_K1_13_5_4_2_5_1Polarization

section PackSource_K1_13_5_4_2_5_1Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1

noncomputable section

open K1_13 K1_13_5_4_2 K1_13_5_4_2_5 MeasureTheory Filter
open scoped BigOperators Pointwise Topology

/-- Positive-weight old-coordinate sums have a common ordered tetrahedral triangulation. -/
def c1 : Prop :=
  ∀ P Q : Set ExponentSpace, FirstBody P → FirstBody Q →
    ∀ k i j : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      ∃ (n : ℕ) (cells : Fin n → VertexChoices),
        CommonTriangulation (oldSlots k) (pairSlots P Q i j) n cells

/-- Ordinary volume of a positively oriented tetrahedron in product Lebesgue measure. -/
def c2 : Prop :=
  ∀ x : Fin 4 → OldSpace, 0 < orientedDet x →
    oldVolume (tetrahedron x) = orientedDet x / 6

private theorem positive_volume_formula {base : Set OldSpace} {B : Fin 4 → Set OldSpace}
    {n : ℕ} {cells : Fin n → VertexChoices} (hc : CommonTriangulation base B n cells)
    (h2 : c2) {w : Fin 4 → ℝ} (hw : ∀ i, 0 < w i) :
    oldVolume (weightedSum base B w) = ∑ k, orientedDet (vertices (cells k) w) / 6 := by
  let T (k : Fin n) := tetrahedron (vertices (cells k) w)
  have hk (k : Fin n) : IsCompact (T k) := (Set.finite_range _).isCompact_convexHull ℝ
  have hvol := measureReal_biUnion_finset₀ (μ := (volume : Measure OldSpace))
    (s := Finset.univ) (f := T)
    (fun k _ l _ hkl => hc.null_inter w hw hkl)
    (fun k _ => (hk k).measurableSet.nullMeasurableSet)
    (fun k _ => (hk k).measure_ne_top)
  calc
    _ = ∑ k, oldVolume (T k) := by
      simpa only [hc.union_eq w hw, oldVolume, Measure.real_def, Finset.mem_univ, Set.iUnion_true]
        using hvol
    _ = _ := Finset.sum_congr rfl (fun k _ => h2 _ (hc.oriented w hw k))

private theorem corner_volume_formula {base : Set OldSpace} {B : Fin 4 → Set OldSpace}
    {n : ℕ} {cells : Fin n → VertexChoices} (hc : CommonTriangulation base B n cells)
    (h2 : c2) (S : Finset (Fin 4))
    (hlim : Tendsto (fun m => oldVolume (weightedSum base B (shiftedCorner S m))) atTop
      (𝓝 (oldVolume (weightedSum base B (corner S))))) :
    oldVolume (weightedSum base B (corner S)) =
      ∑ k, orientedDet (vertices (cells k) (corner S)) / 6 := by
  have hshift : Tendsto (shiftedCorner S) atTop (𝓝 (corner S)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [shiftedCorner, add_zero] using
      (tendsto_const_nhds (x := corner S i)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let f (w : Fin 4 → ℝ) := ∑ k, orientedDet (vertices (cells k) w) / 6
  have hf : Continuous f := by
    unfold f orientedDet vertices
    fun_prop
  have hpos (m : ℕ) (i : Fin 4) : 0 < shiftedCorner S m i := by
    unfold shiftedCorner corner
    split <;> positivity
  have he : ∀ m, oldVolume (weightedSum base B (shiftedCorner S m)) = f (shiftedCorner S m) :=
    fun m => positive_volume_formula hc h2 (hpos m)
  exact tendsto_nhds_unique hlim ((hf.continuousAt.tendsto.comp hshift).congr fun m => (he m).symm)

theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2_5.c1 := by
  intro P Q hP hQ
  have hadd (k i j : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
      mixedThree (oldSlots k) (oldPart '' P + oldPart '' Q) (oldSlots i) (oldSlots j) =
        mixedThree (oldSlots k) (oldPart '' P) (oldSlots i) (oldSlots j) +
          mixedThree (oldSlots k) (oldPart '' Q) (oldSlots i) (oldSlots j) := by
    obtain ⟨n, cells, hc⟩ := h1 P Q hP hQ k i j hij hki hkj
    apply mixedThree_add_of_difference (fun l => ⟨0, pairSlots_zero hP hQ i j l⟩)
    have h (S : Finset (Fin 4)) := corner_volume_formula hc h2 S
      (corner_limit hP hQ k i j S)
    simp only [h, div_eq_mul_inv, mul_comm _ ((6 : ℝ)⁻¹), difference_sum, difference_mul,
      difference_det, mul_zero, Finset.sum_const_zero]
  rw [last_eq_three (hP.add hQ), last_eq_three hP, last_eq_three hQ, oldPart_add P Q,
    hadd 0 1 2 (by decide) (by decide) (by decide),
    hadd 1 0 2 (by decide) (by decide) (by decide),
    hadd 2 0 1 (by decide) (by decide) (by decide)]
  ring

end
end K1_13_5_4_2_5_1
end PackSource_K1_13_5_4_2_5_1Split

section PackSource_K1_13_5_4_2_5_1_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1

open K1_13_5_4_2_5_1
open scoped BigOperators

noncomputable section

/-- The labels of the generating points maximizing a support functional. -/
def Maximizes {ι : Type} (x : ι → OldSpace) (ℓ : OldSpace →ₗ[ℝ] ℝ) (a : ι) : Prop :=
  ∀ b : ι, ℓ (x b) ≤ ℓ (x a)

/-- An exposed face is recorded by all its labels, including coincident generators. -/
def FaceLabels {ι : Type} (x : ι → OldSpace) (S : Finset ι) : Prop :=
  S.Nonempty ∧ ∃ ℓ : OldSpace →ₗ[ℝ] ℝ, ∀ a, a ∈ S ↔ Maximizes x ℓ a

/-- Average all labeled generators of a nonempty face. -/
def faceCenter {ι : Type} (x : ι → OldSpace) (S : Finset ι) : OldSpace :=
  (S.card : ℝ)⁻¹ • ∑ a ∈ S, x a

/-- Four strictly nested nonempty exposed faces, ending in the whole configuration. -/
def FaceFlag {ι : Type} [Fintype ι] (x : ι → OldSpace) :=
  {F : Fin 4 → Finset ι // StrictMono F ∧ (∀ i, FaceLabels x (F i)) ∧ F 3 = Finset.univ}

def flagVertices {ι : Type} [Fintype ι] {x : ι → OldSpace} (F : FaceFlag x) :
    Fin 4 → OldSpace :=
  fun i => faceCenter x (F.val i)

end

end K1_13_5_4_2_5_1_1
end PackSource_K1_13_5_4_2_5_1_1Defs

section PackSource_K1_13_5_4_2_5_1_1Labels
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1

open K1_13 K1_13_5 K1_13_5_4_2 K1_13_5_4_2_5 K1_13_5_4_2_5_1 Set
open scoped BigOperators Pointwise

noncomputable section

variable {ι : Type} {κ : Fin 4 → Type}

/-- A label independently picks one generator in each summand. -/
abbrev Labels (ι : Type) (κ : Fin 4 → Type) := ι × ((i : Fin 4) → κ i)

def labelPoint (p : ι → OldSpace) (q : (i : Fin 4) → κ i → OldSpace)
    (w : Fin 4 → ℝ) (a : Labels ι κ) : OldSpace :=
  p a.1 + ∑ i, w i • q i (a.2 i)

theorem labelHull (p : ι → OldSpace) (q : (i : Fin 4) → κ i → OldSpace)
    (w : Fin 4 → ℝ) :
    convexHull ℝ (range (labelPoint p q w)) =
      weightedSum (convexHull ℝ (range p)) (fun i => convexHull ℝ (range (q i))) w := by
  have hr : range (labelPoint p q w) = range p + ∑ i, w i • range (q i) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨p a.1, mem_range_self _, _, ?_, rfl⟩
      exact (Set.mem_fintype_sum _ _).2
        ⟨_, fun i => ⟨q i (a.2 i), mem_range_self _, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨b, rfl⟩, y, hy, rfl⟩
      obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).1 hy
      have hq (i : Fin 4) : ∃ a : κ i, w i • q i a = g i := by
        obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hg i
        exact ⟨a, ha⟩
      choose a ha using hq
      exact ⟨(b, a), by simp only [labelPoint, ha]⟩
  rw [hr, convexHull_add, convexHull_sum, weightedSum]
  simp only [convexHull_smul]

private theorem evalLabel (p : ι → OldSpace) (q : (i : Fin 4) → κ i → OldSpace)
    (w : Fin 4 → ℝ) (ℓ : OldSpace →ₗ[ℝ] ℝ) (a : Labels ι κ) :
    ℓ (labelPoint p q w a) = ℓ (p a.1) + ∑ i, w i * ℓ (q i (a.2 i)) := by
  simp only [labelPoint, map_add, map_sum, map_smul, smul_eq_mul]

private theorem maximizesLabel (p : ι → OldSpace) (q : (i : Fin 4) → κ i → OldSpace)
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) (ℓ : OldSpace →ₗ[ℝ] ℝ) (a : Labels ι κ) :
    Maximizes (labelPoint p q w) ℓ a ↔
      Maximizes p ℓ a.1 ∧ ∀ i, Maximizes (q i) ℓ (a.2 i) := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro b
      have hb := h (b, a.2)
      simp only [evalLabel, add_le_add_iff_right] at hb
      exact hb
    · intro i b
      have hb := h (a.1, Function.update a.2 i b)
      simp only [evalLabel, add_le_add_iff_left] at hb
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hb
      have he : (∑ j ∈ Finset.univ.erase i, w j * ℓ (q j (Function.update a.2 i b j))) =
          ∑ j ∈ Finset.univ.erase i, w j * ℓ (q j (a.2 j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [Function.update_self, he, add_le_add_iff_right] at hb
      exact le_of_mul_le_mul_left hb (hw i)
  · rintro ⟨hp, hq⟩ b
    simp only [evalLabel]
    exact add_le_add (hp b.1) (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hq i (b.2 i)) (hw i).le)

/-- Positive weights do not change the exposed-face label sets. -/
theorem faceLabels_iff (p : ι → OldSpace) (q : (i : Fin 4) → κ i → OldSpace)
    {v w : Fin 4 → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (S : Finset (Labels ι κ)) :
    FaceLabels (labelPoint p q v) S ↔ FaceLabels (labelPoint p q w) S := by
  simp only [FaceLabels, maximizesLabel p q v hv, maximizesLabel p q w hw]

/-- Transport a flag by retaining all four label sets. -/
def flagEquiv [Fintype (Labels ι κ)] (p : ι → OldSpace)
    (q : (i : Fin 4) → κ i → OldSpace)
    {v w : Fin 4 → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i) :
    FaceFlag (labelPoint p q v) ≃ FaceFlag (labelPoint p q w) where
  toFun F := ⟨F.val, F.property.1,
    fun i => (faceLabels_iff p q hv hw _).1 (F.property.2.1 i), F.property.2.2⟩
  invFun F := ⟨F.val, F.property.1,
    fun i => (faceLabels_iff p q hv hw _).2 (F.property.2.1 i), F.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Average the contributions separately to make the center affine in the weights. -/
def flagChoices [Fintype (Labels ι κ)] (p : ι → OldSpace)
    (q : (i : Fin 4) → κ i → OldSpace)
    {x : Labels ι κ → OldSpace} (F : FaceFlag x) : VertexChoices := fun j =>
  (faceCenter (fun a : Labels ι κ => p a.1) (F.val j),
    fun i => faceCenter (fun a : Labels ι κ => q i (a.2 i)) (F.val j))

theorem vertices_flagChoices [Fintype (Labels ι κ)] (p : ι → OldSpace)
    (q : (i : Fin 4) → κ i → OldSpace)
    {v w : Fin 4 → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (F : FaceFlag (labelPoint p q v)) :
    vertices (flagChoices p q F) w =
      flagVertices (flagEquiv p q hv hw F) := by
  funext j
  simp only [vertices, flagChoices, flagVertices, flagEquiv, faceCenter, labelPoint,
    Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  exact smul_comm _ _ _

end

end K1_13_5_4_2_5_1_1
end PackSource_K1_13_5_4_2_5_1_1Labels

section PackSource_K1_13_5_4_2_5_1_1Caps
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1

open K1_13 K1_13_5 K1_13_5_4_2 K1_13_5_4_2_4 K1_13_5_4_2_5 K1_13_5_4_2_5_1 Set
open scoped BigOperators Pointwise

noncomputable section

private def projectOld : ExponentSpace →ₗ[ℝ] OldSpace where
  toFun := oldPart
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem oldPart_capBody (s : Shape) : oldPart '' capBody s 0 = oldCap s := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hb, hj, ht, _⟩, rfl⟩
    exact ⟨fun i => hy i.castSucc, hb, hj, ht⟩
  · rintro ⟨hx, hb, hj, ht⟩
    have hlast : (@Fin.snoc 3 (fun _ => ℝ) x 0) 3 = 0 :=
      @Fin.snoc_last 3 (fun _ => ℝ) 0 x
    refine ⟨Fin.snoc x 0, ⟨?_, hb, hj, ht, ?_⟩, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
      · simpa only [Fin.snoc_castSucc] using hx j
    · rw [hlast]
      positivity
    · funext j
      exact Fin.snoc_castSucc _ _ _

private theorem oldCap_finiteHull (s : Shape) (hs : Chamber s) :
    ∃ (n : ℕ) (p : Fin n → OldSpace), oldCap s = convexHull ℝ (range p) := by
  let A := capSupport s 0
  let e := (Fintype.equivFin (↥A)).symm
  refine ⟨Fintype.card (↥A), fun i => oldPart (exponentVector (e i).val), ?_⟩
  have hr : range (fun i => oldPart (exponentVector (e i).val)) =
      oldPart '' (exponentVector '' (↑A : Set Exponent)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨(e i).val, (e i).property, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨e.symm ⟨a, ha⟩, ?_⟩
      change oldPart (exponentVector (e (e.symm ⟨a, ha⟩)).val) = _
      rw [Equiv.apply_symm_apply]
  rw [hr]
  change oldCap s = convexHull ℝ (projectOld '' (exponentVector '' (↑A : Set Exponent)))
  rw [← projectOld.image_convexHull, ← latticeBody, latticeBody_capSupport s 0 hs.1 hs.2]
  exact (oldPart_capBody s).symm

private theorem first_finiteHull {P : Set ExponentSpace} (hP : FirstBody P) :
    ∃ (n : ℕ) (p : Fin n → OldSpace), oldPart '' P = convexHull ℝ (range p) := by
  obtain ⟨v, hv, rfl⟩ := hP.polytope
  let _ := hv.fintype
  let e := (Fintype.equivFin (↥v)).symm
  refine ⟨Fintype.card (↥v), fun i => oldPart (e i).val, ?_⟩
  change projectOld '' convexHull ℝ v = _
  rw [projectOld.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨e.symm ⟨a, ha⟩, ?_⟩
    change projectOld (e (e.symm ⟨a, ha⟩)).val = _
    rw [Equiv.apply_symm_apply]
  · rintro ⟨i, rfl⟩
    exact ⟨(e i).val, (e i).property, rfl⟩

theorem oldSlots_finiteHull (k : Fin 3) :
    ∃ (n : ℕ) (p : Fin n → OldSpace), oldSlots k = convexHull ℝ (range p) := by
  fin_cases k <;> apply oldCap_finiteHull <;>
    norm_num [Chamber, liftedBox, taylorLength]

theorem pairSlots_finiteHull {P Q : Set ExponentSpace} (hP : FirstBody P) (hQ : FirstBody Q)
    (i j : Fin 3) (l : Fin 4) :
    ∃ (n : ℕ) (p : Fin n → OldSpace),
      pairSlots P Q i j l =
      convexHull ℝ (range p) := by
  fin_cases l
  · exact first_finiteHull hP
  · exact first_finiteHull hQ
  · exact oldSlots_finiteHull _
  · exact oldSlots_finiteHull _

private theorem oldCap_interior (s : Shape) (hb : 3 < s.b) (hj : 3 < s.j) (ht : 1 < s.t) :
    (interior (oldCap s)).Nonempty := by
  let U : Set OldSpace := {x | ∀ i, 0 < x i} ∩
    ({x | x 0 + x 1 + x 2 < (s.b : ℝ)} ∩
      ({x | x 1 + 2 * x 2 < (s.j : ℝ)} ∩ {x | x 2 < (s.t : ℝ)}))
  have ho : IsOpen U := by
    have hcoord : IsOpen {x : OldSpace | ∀ i, 0 < x i} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    exact hcoord.inter ((isOpen_lt (by fun_prop) continuous_const).inter
      ((isOpen_lt (by fun_prop) continuous_const).inter
        (isOpen_lt (continuous_apply 2) continuous_const)))
  have hU : U ⊆ oldCap s := fun _ h => ⟨fun i => (h.1 i).le,
    h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩
  have hm : (fun _ : Fin 3 => (1 : ℝ)) ∈ U := by
    change (∀ _ : Fin 3, (0 : ℝ) < 1) ∧
      (1 + 1 + 1 : ℝ) < s.b ∧ (1 + 2 * 1 : ℝ) < s.j ∧ (1 : ℝ) < s.t
    exact ⟨fun _ => zero_lt_one, by exact_mod_cast hb,
      by exact_mod_cast hj, by exact_mod_cast ht⟩
  exact ⟨_, interior_maximal hU ho hm⟩

theorem weightedSum_interior {P Q : Set ExponentSpace} (hP : FirstBody P) (hQ : FirstBody Q)
    (k i j : Fin 3) (w : Fin 4 → ℝ) :
    (interior (weightedSum (oldSlots k) (pairSlots P Q i j) w)).Nonempty := by
  have hbase : (interior (oldSlots k)).Nonempty := by
    fin_cases k <;> apply oldCap_interior <;> norm_num [liftedBox, taylorLength]
  refine hbase.mono (interior_mono fun x hx => ?_)
  refine Set.mem_add.mpr ⟨x, hx, 0, ?_, add_zero x⟩
  exact (Set.mem_fintype_sum _ _).2
    ⟨fun _ => 0, fun l => ⟨0, pairSlots_zero hP hQ i j l, smul_zero _⟩, by simp⟩

end

end K1_13_5_4_2_5_1_1
end PackSource_K1_13_5_4_2_5_1_1Caps

section PackSource_K1_13_5_4_2_5_1_1Nondegenerate
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1

open K1_13_5_4_2_5_1
open scoped BigOperators

noncomputable section

variable {ι : Type}

private theorem eval_center (x : ι → OldSpace) (S : Finset ι)
    (ℓ : OldSpace →ₗ[ℝ] ℝ) :
    ℓ (faceCenter x S) = (∑ b ∈ S, ℓ (x b)) / (S.card : ℝ) := by
  simp only [faceCenter, map_smul, map_sum, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem center_eq {x : ι → OldSpace} {S T : Finset ι} {a : ι}
    {ℓ : OldSpace →ₗ[ℝ] ℝ} (hℓ : ∀ b, b ∈ T ↔ Maximizes x ℓ b)
    (ha : a ∈ T) (hS : S.Nonempty) (hST : S ⊆ T) :
    ℓ (faceCenter x S) = ℓ (x a) := by
  have hp : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [eval_center, div_eq_iff hp.ne']
  calc
    _ = ∑ b ∈ S, ℓ (x a) := Finset.sum_congr rfl fun b hb =>
      le_antisymm ((hℓ a).1 ha b) ((hℓ b).1 (hST hb) a)
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

private theorem center_lt {x : ι → OldSpace} {S T : Finset ι} {a : ι}
    {ℓ : OldSpace →ₗ[ℝ] ℝ} (hℓ : ∀ b, b ∈ T ↔ Maximizes x ℓ b)
    (ha : a ∈ T) (hTS : T < S) :
    ℓ (faceCenter x S) < ℓ (x a) := by
  have hp : (0 : ℝ) < S.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨a, hTS.le ha⟩)
  obtain ⟨b, hbS, hbT⟩ := Finset.exists_of_ssubset hTS
  have hba : ℓ (x b) < ℓ (x a) := lt_of_le_of_ne ((hℓ a).1 ha b) fun he =>
    hbT ((hℓ b).2 fun c => he.symm ▸ (hℓ a).1 ha c)
  rw [eval_center, div_lt_iff₀ hp]
  calc
    _ < ∑ c ∈ S, ℓ (x a) := Finset.sum_lt_sum (fun c _ => (hℓ a).1 ha c)
      ⟨b, hbS, hba⟩
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

/-- Supporting functionals turn the edge matrix of a strict flag into a
triangular matrix with a nonzero diagonal. -/
theorem flag_det_ne_zero [Fintype ι] {x : ι → OldSpace} (F : FaceFlag x) :
    orientedDet (flagVertices F) ≠ 0 := by
  have h (i : Fin 3) : ∃ (a : ι) (ℓ : OldSpace →ₗ[ℝ] ℝ),
      a ∈ F.val i.castSucc ∧ ∀ b, b ∈ F.val i.castSucc ↔ Maximizes x ℓ b := by
    obtain ⟨⟨a, ha⟩, ℓ, hℓ⟩ := F.property.2.1 i.castSucc
    exact ⟨a, ℓ, ha, hℓ⟩
  choose a ℓ ha hℓ using h
  let d : Fin 3 → OldSpace := fun j => flagVertices F j.succ - flagVertices F 0
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => ℓ i (d j)
  have hbase (i : Fin 3) : ℓ i (flagVertices F 0) = ℓ i (x (a i)) :=
    center_eq (hℓ i) (ha i) (F.property.2.1 0).1 (F.property.1.monotone (Fin.zero_le _))
  have htri : M.IsUpperTriangular := by
    intro i j hij
    have hle : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      have hji : j.val < i.val := hij
      omega
    have he : ℓ i (flagVertices F j.succ) = ℓ i (x (a i)) :=
      center_eq (hℓ i) (ha i) (F.property.2.1 j.succ).1 (F.property.1.monotone hle)
    change ℓ i (flagVertices F j.succ - flagVertices F 0) = 0
    rw [map_sub, he, hbase, sub_self]
  have hdiag (i : Fin 3) : M i i ≠ 0 := by
    have hlt : ℓ i (flagVertices F i.succ) < ℓ i (x (a i)) :=
      center_lt (hℓ i) (ha i) (F.property.1 i.castSucc_lt_succ)
    change ℓ i (flagVertices F i.succ - flagVertices F 0) ≠ 0
    rw [map_sub, hbase]
    exact (sub_neg.mpr hlt).ne
  have hM : M.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)
  let L : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i k => ℓ i (Pi.single k 1)
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun k j => d j k
  have hprod : M = L * D := by
    ext i j
    change ℓ i (d j) = (L * D) i j
    calc
      _ = ℓ i (∑ k, (d j k) • Pi.single k 1) :=
        congrArg (ℓ i) (pi_eq_sum_univ' (d j))
      _ = _ := by
        simp only [Matrix.mul_apply, map_sum, map_smul, smul_eq_mul, L, D, Matrix.of_apply]
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  rw [hprod, Matrix.det_mul] at hM
  exact (mul_ne_zero_iff.mp hM).2

end

end K1_13_5_4_2_5_1_1
end PackSource_K1_13_5_4_2_5_1_1Nondegenerate

section PackSource_K1_13_5_4_2_5_1_1Orientation
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1

open K1_13_5_4_2_5_1 Set
open scoped BigOperators

noncomputable section

private def swapEdges (v : VertexChoices) : VertexChoices :=
  v ∘ Equiv.swap (1 : Fin 4) 2

private theorem range_swapEdges (v : VertexChoices) (w : Fin 4 → ℝ) :
    range (vertices (swapEdges v) w) = range (vertices v w) := by
  change range (vertices v w ∘ Equiv.swap (1 : Fin 4) 2) = _
  exact (Equiv.swap (1 : Fin 4) 2).surjective.range_comp _

private theorem orientedDet_swapEdges (v : VertexChoices) (w : Fin 4 → ℝ) :
    orientedDet (vertices (swapEdges v) w) = -orientedDet (vertices v w) := by
  have h (i : Fin 4) :
      vertices (swapEdges v) w i = vertices v w (Equiv.swap (1 : Fin 4) 2 i) := rfl
  simp only [orientedDet, Matrix.det_fin_three, Matrix.of_apply, h]
  have h0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have h1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have h2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have h3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  have e1 : (0 : Fin 3).succ = 1 := rfl
  have e2 : (1 : Fin 3).succ = 2 := rfl
  have e3 : (2 : Fin 3).succ = 3 := rfl
  simp only [h0, h1, h2, h3, e1, e2, e3]
  ring

private theorem positiveWeights_convex : Convex ℝ {w : Fin 4 → ℝ | ∀ i, 0 < w i} := by
  intro u hu v hv a b ha hb hab i
  have hu' : 0 < u i := hu i
  have hv' : 0 < v i := hv i
  change 0 < a * u i + b * v i
  rcases ha.eq_or_lt with rfl | ha'
  · have hb' : b = 1 := by linarith
    simpa [hb'] using hv'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hu') (mul_nonneg hb hv'.le)

private theorem det_pos_of_unit (v : VertexChoices)
    (hn : ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) → orientedDet (vertices v w) ≠ 0)
    (hunit : 0 < orientedDet (vertices v (fun _ => 1))) :
    ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) → 0 < orientedDet (vertices v w) := by
  intro w hw
  let f : (Fin 4 → ℝ) → ℝ := fun a => orientedDet (vertices v a)
  have hf : Continuous f := by unfold f orientedDet vertices; fun_prop
  by_contra! hle
  have hz : (0 : ℝ) ∈ Icc (f w) (f (fun _ => 1)) := ⟨hle, hunit.le⟩
  have hw' : w ∈ {a : Fin 4 → ℝ | ∀ i, 0 < a i} := hw
  have h1 : (fun _ : Fin 4 => (1 : ℝ)) ∈ {a : Fin 4 → ℝ | ∀ i, 0 < a i} :=
    fun _ => zero_lt_one
  obtain ⟨u, hu, he⟩ :=
    positiveWeights_convex.isPreconnected.intermediate_value hw' h1 hf.continuousOn hz
  exact hn u hu he

/-- A single reordering at unit weights fixes orientation on the positive cone. -/
theorem orient (v : VertexChoices)
    (hn : ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) → orientedDet (vertices v w) ≠ 0) :
    ∃ v' : VertexChoices, ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) →
      range (vertices v' w) = range (vertices v w) ∧ 0 < orientedDet (vertices v' w) := by
  have h1 := hn (fun _ => 1) (fun _ => zero_lt_one)
  rcases lt_or_gt_of_ne h1 with hneg | hpos
  · refine ⟨swapEdges v, fun w hw => ⟨range_swapEdges v w, ?_⟩⟩
    apply det_pos_of_unit (swapEdges v) _ _ w hw
    · intro u hu
      rw [orientedDet_swapEdges]
      exact neg_ne_zero.mpr (hn u hu)
    · rw [orientedDet_swapEdges]
      exact neg_pos.mpr hneg
  · exact ⟨v, fun w hw => ⟨rfl, det_pos_of_unit v hn hpos w hw⟩⟩

end

end K1_13_5_4_2_5_1_1
end PackSource_K1_13_5_4_2_5_1_1Orientation

section PackSource_K1_13_5_4_2_5_1_1_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1_1

open K1_13_5_4_2_5_1 K1_13_5_4_2_5_1_1 Set
open scoped BigOperators

noncomputable section

variable {ι : Type}

/-- The points labeled by a face. Multiple labels can designate the same point. -/
def facePoints (x : ι → OldSpace) (S : Finset ι) : Set OldSpace := x '' (S : Set ι)

def faceHull (x : ι → OldSpace) (S : Finset ι) : Set OldSpace :=
  convexHull ℝ (facePoints x S)

def faceDir (x : ι → OldSpace) (S : Finset ι) : Submodule ℝ OldSpace :=
  (affineSpan ℝ (facePoints x S)).direction

def faceDim (x : ι → OldSpace) (S : Finset ι) : ℕ :=
  Module.finrank ℝ (faceDir x S)

theorem label_mem_points (x : ι → OldSpace) {S : Finset ι} {a : ι} (ha : a ∈ S) :
    x a ∈ facePoints x S := ⟨a, ha, rfl⟩

theorem hull_mono (x : ι → OldSpace) {T S : Finset ι} (h : T ⊆ S) :
    faceHull x T ⊆ faceHull x S := convexHull_mono (image_mono h)

theorem center_mem_hull (x : ι → OldSpace) {S : Finset ι} (hS : S.Nonempty) :
    faceCenter x S ∈ faceHull x S := by
  have hp : 0 < ∑ _a ∈ S, (1 : ℝ) := by simpa using hS.card_pos
  simpa [faceHull, faceCenter, Finset.centerMass] using
    (S.centerMass_mem_convexHull (w := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) hp
      (fun a ha => label_mem_points x ha))

theorem dir_eq_span_sub (x : ι → OldSpace) {S : Finset ι} {a : ι} (ha : a ∈ S) :
    faceDir x S = Submodule.span ℝ ((fun b => x b - x a) '' (S : Set ι)) := by
  rw [faceDir, direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ (label_mem_points x ha)]
  exact congrArg (Submodule.span ℝ) (image_image _ _ _)

theorem label_sub_mem_dir (x : ι → OldSpace) {S : Finset ι} {a b : ι}
    (ha : a ∈ S) (hb : b ∈ S) : x b - x a ∈ faceDir x S := by
  rw [dir_eq_span_sub x ha]
  exact Submodule.subset_span ⟨b, hb, rfl⟩

theorem dir_le_ker {x : ι → OldSpace} {S : Finset ι} {a : ι} (ha : a ∈ S)
    {f : OldSpace →ₗ[ℝ] ℝ} (hf : ∀ i ∈ S, f (x i) = f (x a)) :
    faceDir x S ≤ LinearMap.ker f := by
  rw [dir_eq_span_sub x ha, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  change f (x i - x a) = 0
  rw [map_sub, hf i hi, sub_self]

/-- A support for an exposed face is strict on each of the other labels. -/
theorem expose_lt {x : ι → OldSpace} {T : Finset ι} {a b : ι}
    {f : OldSpace →ₗ[ℝ] ℝ} (hf : ∀ i, i ∈ T ↔ Maximizes x f i)
    (ha : a ∈ T) (hb : b ∉ T) : f (x b) < f (x a) :=
  ((hf a).1 ha b).lt_of_ne fun he => hb ((hf b).2 fun c => he.symm ▸ (hf a).1 ha c)

theorem faceDim_lt {x : ι → OldSpace} {T S : Finset ι}
    (hT : FaceLabels x T) (hTS : T < S) : faceDim x T < faceDim x S := by
  obtain ⟨⟨a, ha⟩, f, hf⟩ := hT
  obtain ⟨b, hbS, hbT⟩ := Finset.exists_of_ssubset hTS
  have hk : faceDir x T ≤ LinearMap.ker f :=
    dir_le_ker ha (fun i hi => le_antisymm ((hf a).1 ha i) ((hf i).1 hi a))
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_not_ge (AffineSubspace.direction_le (affineSpan_mono ℝ (image_mono hTS.le)))
    (fun h => ?_)
  have hm := hk (h (label_sub_mem_dir x (hTS.le ha) hbS))
  change f (x b - x a) = 0 at hm
  rw [map_sub, sub_eq_zero] at hm
  exact (expose_lt hf ha hbT).ne hm

/-- A relative support of an exposed face is a support in the original configuration
after adding a sufficiently large multiple of the functional exposing the parent. -/
theorem expose_relative [Fintype ι] {x : ι → OldSpace} {S T : Finset ι}
    (hS : FaceLabels x S) {a : ι} (ha : a ∈ S)
    (g : OldSpace →ₗ[ℝ] ℝ) (hg : ∀ b ∈ S, g (x b) ≤ g (x a))
    (hT : ∀ b, b ∈ T ↔ b ∈ S ∧ g (x b) = g (x a)) :
    FaceLabels x T := by
  obtain ⟨_, f, hf⟩ := hS
  let q (b : ι) := (g (x b) - g (x a)) / (f (x a) - f (x b))
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ q ⟨a, Finset.mem_univ a⟩
  let k : ℝ := q m + 1
  let u := k • f + g
  have hin (b : ι) (hb : b ∈ S) : f (x b) = f (x a) :=
    le_antisymm ((hf a).1 ha b) ((hf b).1 hb a)
  have hout (b : ι) (hb : b ∉ S) : u (x b) < u (x a) := by
    have hp := sub_pos.mpr (expose_lt hf ha hb)
    have hq : q b < k := (hm b (Finset.mem_univ b)).trans_lt (lt_add_one _)
    have hlt := (div_lt_iff₀ hp).1 hq
    change k * f (x b) + g (x b) < k * f (x a) + g (x a)
    linarith
  have hall (b : ι) : u (x b) ≤ u (x a) := by
    by_cases hb : b ∈ S
    · change k * f (x b) + g (x b) ≤ k * f (x a) + g (x a)
      rw [hin b hb]
      exact add_le_add_right (hg b hb) _
    · exact (hout b hb).le
  refine ⟨⟨a, (hT a).2 ⟨ha, rfl⟩⟩, u, fun b => ?_⟩
  constructor
  · intro hb j
    obtain ⟨hb, he⟩ := (hT b).1 hb
    have hu : u (x b) = u (x a) := by
      change k * f (x b) + g (x b) = k * f (x a) + g (x a)
      rw [hin b hb, he]
    exact hu.symm ▸ hall j
  · intro hb
    have hba := hb a
    have hs : b ∈ S := by
      by_contra hn
      exact (hout b hn).not_ge hba
    apply (hT b).2
    refine ⟨hs, ?_⟩
    have he := le_antisymm (hall b) hba
    change k * f (x b) + g (x b) = k * f (x a) + g (x a) at he
    rw [hin b hs] at he
    linarith

end

end K1_13_5_4_2_5_1_1_1
end PackSource_K1_13_5_4_2_5_1_1_1Defs

section PackSource_K1_13_5_4_2_5_1_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_2

noncomputable section

open K1_13_5_4_2_5_1 MeasureTheory Set
open scoped BigOperators

private def coordinateSimplex (n : ℕ) (L : ℝ) : Set (Fin n → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ L}

private theorem measurableSet_coordinateSimplex (n : ℕ) (L : ℝ) :
    MeasurableSet (coordinateSimplex n L) := by
  have horth : MeasurableSet {v : Fin n → ℝ | ∀ i, 0 ≤ v i} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  have hsum : Continuous (fun v : Fin n → ℝ => ∑ i, v i) :=
    continuous_finsetSum Finset.univ (fun i _ => continuous_apply i)
  exact horth.inter (measurableSet_le hsum.measurable measurable_const)

private theorem cons_mem_coordinateSimplex {n : ℕ} (L t : ℝ) (v : Fin n → ℝ) :
    Fin.cons t v ∈ coordinateSimplex (n + 1) L ↔
      t ∈ Icc 0 L ∧ v ∈ coordinateSimplex n (L - t) := by
  simp only [coordinateSimplex, mem_ofPred_eq, Fin.forall_fin_succ, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, mem_Icc]
  constructor
  · rintro ⟨⟨ht, hv⟩, hs⟩
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hv i)
    exact ⟨⟨ht, by linarith⟩, hv, by linarith⟩
  · rintro ⟨⟨ht, _⟩, hv, hs⟩
    exact ⟨⟨ht, hv⟩, by linarith⟩

/-- Slice at the first coordinate, leaving a simplex of budget `L - t`. -/
private theorem volume_coordinateSimplex (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    volume (coordinateSimplex n L) = ENNReal.ofReal (L ^ n / (n.factorial : ℝ)) := by
  induction n generalizing L with
  | zero =>
    have hall : coordinateSimplex 0 L = univ := by
      ext v
      simp [coordinateSimplex, hL]
    rw [hall, Measure.volume_pi_eq_dirac]
    simp
  | succ n ih =>
    let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
      MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0
    have he : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ => ℝ) 0
    have he_cons (t : ℝ) (v : Fin n → ℝ) : e.symm (t, v) = Fin.cons t v := by
      change Fin.insertNth (α := fun _ => ℝ) 0 t v = _
      exact Fin.insertNth_zero' t v
    let f (t : ℝ) : ℝ := (L - t) ^ n / (n.factorial : ℝ)
    have hvol : volume (coordinateSimplex (n + 1) L) =
        ∫⁻ t in Icc 0 L, ENNReal.ofReal (f t) := by
      have hm := (measurableSet_coordinateSimplex (n + 1) L).preimage e.symm.measurable
      rw [← (he.symm e).measure_preimage_equiv (coordinateSimplex (n + 1) L),
        Measure.volume_eq_prod, Measure.prod_apply hm, ← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Icc 0 L
      · have hsection : Prod.mk t ⁻¹' (e.symm ⁻¹' coordinateSimplex (n + 1) L) =
            coordinateSimplex n (L - t) := by
          ext v
          change e.symm (t, v) ∈ coordinateSimplex (n + 1) L ↔ _
          rw [he_cons, cons_mem_coordinateSimplex, and_iff_right ht]
        rw [hsection, ih (sub_nonneg.mpr ht.2), indicator_of_mem ht]
      · have hsection : Prod.mk t ⁻¹' (e.symm ⁻¹' coordinateSimplex (n + 1) L) = ∅ := by
          ext v
          change e.symm (t, v) ∈ coordinateSimplex (n + 1) L ↔ v ∈ ∅
          simp only [he_cons, cons_mem_coordinateSimplex, ht, false_and, mem_empty_iff_false]
        rw [hsection, measure_empty, indicator_of_notMem ht]
    have hf : Continuous f := by
      unfold f
      fun_prop
    have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc 0 L)] f :=
      (ae_restrict_mem measurableSet_Icc).mono (fun t ht =>
        div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (by positivity))
    rw [hvol, ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn_Icc hnonneg,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
    congr 1
    have hflip : (∫ t in (0 : ℝ)..L, f t) = ∫ t in (0 : ℝ)..L, t ^ n / (n.factorial : ℝ) := by
      simpa only [f, sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := L)
          (fun t : ℝ => t ^ n / (n.factorial : ℝ)) L)
    rw [hflip, intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n),
      sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, div_div]

private def edgeMatrix (x : Fin 4 → OldSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun r c => x c.succ r - x 0 r)

private theorem combination_eq_translate (x : Fin 4 → OldSpace) (w : Fin 4 → ℝ)
    (hw : ∑ i, w i = 1) :
    (∑ i, w i • x i) = x 0 + (edgeMatrix x).toLin' (fun j => w j.succ) := by
  have hzero : w 0 = 1 - ∑ j : Fin 3, w j.succ := by
    rw [Fin.sum_univ_succ] at hw
    linarith
  have hrow (r : Fin 3) :
      (edgeMatrix x).toLin' (fun j => w j.succ) r =
        ∑ j : Fin 3, w j.succ * (x j.succ r - x 0 r) := by
    rw [Matrix.toLin'_apply]
    change (∑ j : Fin 3, (x j.succ r - x 0 r) * w j.succ) = _
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [Fin.sum_univ_succ]
  ext r
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hrow]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero]
  ring

/-- The first barycentric coordinate is the slack in the standard simplex inequality. -/
private theorem tetrahedron_image (x : Fin 4 → OldSpace) :
    tetrahedron x = (x 0 + ·) '' ((edgeMatrix x).toLin' '' coordinateSimplex 3 1) := by
  classical
  rw [tetrahedron, convexHull_range_eq_exists_affineCombination]
  ext y
  simp only [mem_ofPred_eq, image_image, mem_image]
  constructor
  · rintro ⟨s, w, hn, hsum, hy⟩
    let W : Fin 4 → ℝ := (s : Set (Fin 4)).indicator w
    have hW : ∑ i, W i = 1 := by
      simpa only [W, Finset.sum_indicator_subset _ s.subset_univ] using hsum
    have hnW (i : Fin 4) : 0 ≤ W i := by
      by_cases hi : i ∈ s
      · simpa [W, hi] using hn i hi
      · simp [W, hi]
    refine ⟨fun i => W i.succ, ⟨fun i => hnW i.succ, ?_⟩, ?_⟩
    · rw [Fin.sum_univ_succ] at hW
      linarith [hnW 0]
    · rw [← combination_eq_translate x W hW,
        ← Finset.affineCombination_eq_linear_combination _ _ _ hW]
      simpa only [W, Finset.affineCombination_indicator_subset w x s.subset_univ] using hy
  · rintro ⟨v, hv, rfl⟩
    change (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1 at hv
    let w : Fin 4 → ℝ := Fin.cons (1 - ∑ i, v i) v
    have hsum : ∑ i, w i = 1 := by
      rw [Fin.sum_univ_succ]
      simp [w]
    refine ⟨Finset.univ, w, ?_, hsum, ?_⟩
    · intro i _
      exact Fin.cases (sub_nonneg.mpr hv.2) hv.1 i
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      exact combination_eq_translate x w hsum

/-- Ordinary volume is the positive edge determinant divided by six. -/
theorem proof : K1_13_5_4_2_5_1.c2 := by
  intro x hx
  rw [oldVolume, tetrahedron_image, image_add_left, measure_preimage_add,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin']
  change (ENNReal.ofReal |orientedDet x| * volume (coordinateSimplex 3 1)).toReal = _
  rw [abs_of_pos hx, volume_coordinateSimplex 3 zero_le_one, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hx.le, ENNReal.toReal_ofReal (by positivity)]
  norm_num [Nat.factorial, div_eq_mul_inv]

end
end K1_13_5_4_2_5_1_2
end PackSource_K1_13_5_4_2_5_1_2Proof

section PackSource_K1_13_5_4_2_5_1_1Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1

open K1_13_5_4_2_5_1 Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- Coverage by the tetrahedra of the exposed-face flags of one polytope. -/
def c1 : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → OldSpace),
    (interior (convexHull ℝ (range x))).Nonempty →
    convexHull ℝ (range x) = ⋃ F : FaceFlag x, tetrahedron (flagVertices F)

/-- Distinct exposed-face flags of one configuration have disjoint cell interiors. -/
def c2 : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → OldSpace),
    Pairwise (fun F G : FaceFlag x =>
      Disjoint (interior (tetrahedron (flagVertices F))) (interior (tetrahedron (flagVertices G))))

private theorem null_of_disjoint_interiors {A B : Set OldSpace} (hA : Convex ℝ A)
    (hB : Convex ℝ B) (h : Disjoint (interior A) (interior B)) : volume (A ∩ B) = 0 := by
  have hs : A ∩ B ⊆ frontier A ∪ frontier B := by
    intro x hx
    by_cases ha : x ∈ interior A
    · exact Or.inr ⟨subset_closure hx.2, fun hb => Set.disjoint_left.1 h ha hb⟩
    · exact Or.inl ⟨subset_closure hx.1, ha⟩
  exact measure_mono_null hs (measure_union_null (hA.addHaar_frontier _) (hB.addHaar_frontier _))

theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2_5_1.c1 := by
  classical
  intro P Q hP hQ k i j _ _ _
  obtain ⟨m, p, hp⟩ := oldSlots_finiteHull k
  have hq l := pairSlots_finiteHull hP hQ i j l
  choose d q hq using hq
  let unit : Fin 4 → ℝ := fun _ => 1
  have hunit : ∀ l, 0 < unit l := fun _ => zero_lt_one
  let flags : Type := FaceFlag (labelPoint p q unit)
  have hchoice (F : flags) := orient (flagChoices p q F) (fun w hw => by
    rw [vertices_flagChoices p q hunit hw]
    exact flag_det_ne_zero _)
  choose choice hchoice using hchoice
  let _ : Finite flags := by
    dsimp only [flags, FaceFlag]
    infer_instance
  let _ : Fintype flags := Fintype.ofFinite flags
  let e := Fintype.equivFin flags
  let cells : Fin (Fintype.card flags) → VertexChoices := fun a => choice (e.symm a)
  have hcell (w : Fin 4 → ℝ) (hw : ∀ l, 0 < w l) (a : Fin (Fintype.card flags)) :
      tetrahedron (vertices (cells a) w) =
        tetrahedron (flagVertices (flagEquiv p q hunit hw (e.symm a))) := by
    unfold tetrahedron
    change convexHull ℝ (range (vertices (choice (e.symm a)) w)) = _
    rw [(hchoice (e.symm a) w hw).1, vertices_flagChoices p q hunit hw]
  refine ⟨Fintype.card flags, cells, ⟨?_, ?_, ?_⟩⟩
  · intro w hw
    have hh : convexHull ℝ (range (labelPoint p q w)) =
        weightedSum (oldSlots k) (pairSlots P Q i j) w := by
      rw [labelHull, hp, funext hq]
    have hfull : (interior (convexHull ℝ (range (labelPoint p q w)))).Nonempty := by
      rw [hh]
      exact weightedSum_interior hP hQ k i j w
    rw [← hh, h1 _ _ hfull]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨F, hF⟩
      refine ⟨e ((flagEquiv p q hunit hw).symm F), ?_⟩
      rwa [hcell w hw, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · rintro ⟨a, ha⟩
      exact ⟨_, (hcell w hw a) ▸ ha⟩
  · intro w hw a b hab
    rw [hcell w hw a, hcell w hw b]
    refine null_of_disjoint_interiors (convex_convexHull ℝ _) (convex_convexHull ℝ _) ?_
    exact h2 _ _ ((flagEquiv p q hunit hw).injective.ne (e.symm.injective.ne hab))
  · intro w hw a
    exact (hchoice (e.symm a) w hw).2

end

end K1_13_5_4_2_5_1_1
end PackSource_K1_13_5_4_2_5_1_1Split

section PackSource_K1_13_5_4_2_5_1_1_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1_2

open K1_13_5_4_2_5_1 K1_13_5_4_2_5_1_1 Set
open scoped BigOperators

variable {ι : Type}

/-- The deficit from the support value at a face center vanishes exactly when
all of its labels belong to the exposed face. -/
private theorem center_deficit {x : ι → OldSpace} {S T : Finset ι}
    {ℓ : OldSpace →ₗ[ℝ] ℝ} {a : ι} (hℓ : ∀ b, b ∈ T ↔ Maximizes x ℓ b)
    (ha : a ∈ T) (hS : S.Nonempty) :
    0 ≤ ℓ (x a) - ℓ (faceCenter x S) ∧
      (ℓ (x a) - ℓ (faceCenter x S) = 0 ↔ S ⊆ T) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  let d (b : ι) : ℝ := ℓ (x a) - ℓ (x b)
  have hd (b : ι) : 0 ≤ d b := sub_nonneg.mpr ((hℓ a).mp ha b)
  have hd_zero (b : ι) : d b = 0 ↔ b ∈ T := by
    change ℓ (x a) - ℓ (x b) = 0 ↔ b ∈ T
    rw [sub_eq_zero, hℓ b]
    constructor
    · intro he c
      rw [← he]
      exact (hℓ a).mp ha c
    · intro hm
      exact le_antisymm (hm a) ((hℓ a).mp ha b)
  have hmean : ℓ (x a) - ℓ (faceCenter x S) = (∑ b ∈ S, d b) / (S.card : ℝ) := by
    simp only [faceCenter, map_smul, map_sum, smul_eq_mul, d, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard.ne']
  rw [hmean]
  refine ⟨div_nonneg (Finset.sum_nonneg fun b _ => hd b) hcard.le, ?_⟩
  simp only [div_eq_zero_iff, hcard.ne', or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hd b)]
  exact forall₂_congr (fun b _ => hd_zero b)

/-- Compare the contributions of the common last face. The exposing functional
for the penultimate face of the first chain has zero deficit on its whole
prefix. Every deficit of the second chain is nonnegative. -/
private theorem compare_top {x : ι → OldSpace} {n : ℕ}
    (F G : Fin (n + 2) → Finset ι) (w v : Fin (n + 2) → ℝ)
    (hF : StrictMono F) (hfacesF : ∀ i, FaceLabels x (F i))
    (hfacesG : ∀ i, FaceLabels x (G i)) (hv : ∀ i, 0 < v i)
    (htop : F (Fin.last (n + 1)) = G (Fin.last (n + 1)))
    (htotal : ∑ i, w i = ∑ i, v i)
    (hpoint : ∑ i, w i • faceCenter x (F i) = ∑ i, v i • faceCenter x (G i)) :
    v (Fin.last (n + 1)) ≤ w (Fin.last (n + 1)) ∧
      (w (Fin.last (n + 1)) = v (Fin.last (n + 1)) →
        G (Fin.last n).castSucc ⊆ F (Fin.last n).castSucc) := by
  let j : Fin (n + 1) := Fin.last n
  let k : Fin (n + 2) := Fin.last (n + 1)
  obtain ⟨⟨a, ha⟩, ℓ, hℓ⟩ := hfacesF j.castSucc
  let d (S : Finset ι) : ℝ := ℓ (x a) - ℓ (faceCenter x S)
  have hd (S : Finset ι) (hS : S.Nonempty) :
      0 ≤ d S ∧ (d S = 0 ↔ S ⊆ F j.castSucc) := center_deficit hℓ ha hS
  have hdF (i : Fin (n + 1)) : d (F i.castSucc) = 0 :=
    (hd _ (hfacesF _).1).2.mpr
      (hF.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i)))
  have hdtop : 0 < d (F k) := by
    refine lt_of_le_of_ne (hd _ (hfacesF k).1).1 (Ne.symm ?_)
    intro he
    exact (hF j.castSucc_lt_last).not_ge ((hd _ (hfacesF k).1).2.mp he)
  have hsum (u : Fin (n + 2) → ℝ) (H : Fin (n + 2) → Finset ι) :
      (∑ i, u i * d (H i)) = (∑ i, u i) * ℓ (x a) -
        ℓ (∑ i, u i • faceCenter x (H i)) := by
    simp only [d, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, map_sum, map_smul,
      smul_eq_mul]
  have hdiff : (∑ i, w i * d (F i)) = ∑ i, v i * d (G i) := by
    rw [hsum, hsum, htotal, hpoint]
  have hgap : w k * d (F k) =
      (∑ i : Fin (n + 1), v i.castSucc * d (G i.castSucc)) + v k * d (F k) := by
    rw [Fin.sum_univ_castSucc (fun i => w i * d (F i)),
      Fin.sum_univ_castSucc (fun i => v i * d (G i)), ← htop] at hdiff
    simpa only [hdF, mul_zero, Finset.sum_const_zero, zero_add] using hdiff
  have hterms (i : Fin (n + 1)) :
      0 ≤ v i.castSucc * d (G i.castSucc) :=
    mul_nonneg (hv _).le (hd _ (hfacesG _).1).1
  have hlower : 0 ≤ ∑ i : Fin (n + 1), v i.castSucc * d (G i.castSucc) :=
    Finset.sum_nonneg fun i _ => hterms i
  have hle : v k * d (F k) ≤ w k * d (F k) := by linarith only [hgap, hlower]
  refine ⟨le_of_mul_le_mul_right hle hdtop, ?_⟩
  intro he
  have hz : (∑ i : Fin (n + 1), v i.castSucc * d (G i.castSucc)) = 0 := by
    rw [he] at hgap
    linarith only [hgap]
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterms i)).mp hz j
    (Finset.mem_univ j)
  exact (hd _ (hfacesG _).1).2.mp ((mul_eq_zero.mp hj).resolve_left (hv _).ne')

/-- Equal positive combinations of face centers with equal total weight and a
common last face determine the same chain. Strip off that face after comparing
its coefficient and identifying the next face by mutual inclusion. -/
private theorem chain_eq {x : ι → OldSpace} (n : ℕ) :
    ∀ (F G : Fin (n + 1) → Finset ι) (w v : Fin (n + 1) → ℝ),
    StrictMono F → StrictMono G →
    (∀ i, FaceLabels x (F i)) → (∀ i, FaceLabels x (G i)) →
    (∀ i, 0 < w i) → (∀ i, 0 < v i) →
    F (Fin.last n) = G (Fin.last n) →
    (∑ i, w i = ∑ i, v i) →
    (∑ i, w i • faceCenter x (F i) = ∑ i, v i • faceCenter x (G i)) → F = G := by
  induction n with
  | zero =>
      intro F G w v _ _ _ _ _ _ htop _ _
      funext i
      have hi : i = Fin.last 0 := Fin.fin_one_eq_zero i
      rw [hi]
      exact htop
  | succ n ih =>
      intro F G w v hF hG hfacesF hfacesG hw hv htop htotal hpoint
      have hFG := compare_top F G w v hF hfacesF hfacesG hv htop htotal hpoint
      have hGF := compare_top G F v w hG hfacesG hfacesF hw htop.symm htotal.symm hpoint.symm
      have he : w (Fin.last (n + 1)) = v (Fin.last (n + 1)) := le_antisymm hGF.1 hFG.1
      have hnext : F (Fin.last n).castSucc = G (Fin.last n).castSucc :=
        Finset.Subset.antisymm (hGF.2 he.symm) (hFG.2 he)
      have ht :
          (∑ i : Fin (n + 1), w i.castSucc) = ∑ i : Fin (n + 1), v i.castSucc := by
        rw [Fin.sum_univ_castSucc w, Fin.sum_univ_castSucc v, he] at htotal
        exact add_right_cancel htotal
      have hp :
          (∑ i : Fin (n + 1), w i.castSucc • faceCenter x (F i.castSucc)) =
            ∑ i : Fin (n + 1), v i.castSucc • faceCenter x (G i.castSucc) := by
        rw [Fin.sum_univ_castSucc (fun i => w i • faceCenter x (F i)),
          Fin.sum_univ_castSucc (fun i => v i • faceCenter x (G i)), he, htop] at hpoint
        exact add_right_cancel hpoint
      have hprefix := ih (F ∘ Fin.castSucc) (G ∘ Fin.castSucc)
        (w ∘ Fin.castSucc) (v ∘ Fin.castSucc)
        (hF.comp Fin.strictMono_castSucc) (hG.comp Fin.strictMono_castSucc)
        (fun i => hfacesF i.castSucc) (fun i => hfacesG i.castSucc)
        (fun i => hw i.castSucc) (fun i => hv i.castSucc) hnext ht hp
      exact funext (Fin.lastCases htop (congrFun hprefix))

/-- The determinant from the parent supplies an affine basis, so an interior
point has strictly positive coordinates. -/
private theorem positive_weights [Fintype ι] {x : ι → OldSpace} (F : FaceFlag x)
    {y : OldSpace} (hy : y ∈ interior (tetrahedron (flagVertices F))) :
    ∃ w : Fin 4 → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • flagVertices F i = y) := by
  have hind : AffineIndependent ℝ (flagVertices F) := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0,
      ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 4))]
    exact Matrix.linearIndependent_cols_of_det_ne_zero (flag_det_ne_zero F)
  have hspan : affineSpan ℝ (range (flagVertices F)) = ⊤ :=
    hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simp [Module.finrank_fintype_fun_eq_card])
  let b : AffineBasis (Fin 4) ℝ OldSpace := ⟨flagVertices F, hind, hspan⟩
  change y ∈ interior (convexHull ℝ (range b)) at hy
  rw [b.interior_convexHull] at hy
  exact ⟨fun i => b.coord i y, hy, b.sum_coord_apply_eq_one y, b.linear_combination_coord_eq_self y⟩

/-- Distinct exposed-face flags have tetrahedra with disjoint interiors. -/
theorem proof : K1_13_5_4_2_5_1_1.c2 := by
  intro ι _ x F G hFG
  rw [Set.disjoint_left]
  intro y hyF hyG
  obtain ⟨w, hw, hwt, hwy⟩ := positive_weights F hyF
  obtain ⟨v, hv, hvt, hvy⟩ := positive_weights G hyG
  apply hFG
  apply Subtype.ext
  exact chain_eq 3 F.val G.val w v F.property.1 G.property.1
    F.property.2.1 G.property.2.1 hw hv (F.property.2.2.trans G.property.2.2.symm)
    (hwt.trans hvt.symm) (hwy.trans hvy.symm)

end K1_13_5_4_2_5_1_1_2
end PackSource_K1_13_5_4_2_5_1_1_2Proof

section PackSource_K1_13_5_4_2_5_1_1_1Cone
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1_1

open K1_13_5_4_2_5_1 K1_13_5_4_2_5_1_1 Set AffineMap
open scoped BigOperators Topology

noncomputable section

variable {ι : Type}

/-- A ray through two distinct points of a compact set has a last point in the set. -/
private theorem ray_endpoint {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {C : Set V} (hC : IsCompact C) {c z : V} (hz : z ∈ C) (hne : z ≠ c) :
    ∃ y ∈ C, y ∉ interior C ∧ z ∈ segment ℝ c y := by
  let l := lineMap c z (k := ℝ)
  have hl : Topology.IsClosedEmbedding l := by
    convert (Homeomorph.addRight c).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (𝕜 := ℝ) (sub_ne_zero.mpr hne)) using 1
    funext t
    exact lineMap_apply_module' c z t
  have h1 : (1 : ℝ) ∈ l ⁻¹' C := by simpa [l] using hz
  obtain ⟨t, ht⟩ := (hl.isCompact_preimage hC).exists_isGreatest ⟨1, h1⟩
  have ht1 : 1 ≤ t := ht.2 h1
  refine ⟨l t, ht.1, ?_, ?_⟩
  · intro hi
    obtain ⟨s, hst, hs⟩ :=
      (lineMap_continuous (p := c) (q := z)).tendsto t
        |>.eventually_mem (mem_interior_iff_mem_nhds.1 hi) |>.exists_gt
    exact hst.not_ge (ht.2 (show l s ∈ C from hs))
  · have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have h := lineMap_mem_segment ℝ c (l t) (t := t⁻¹) ⟨by positivity, (inv_le_one₀ ht0).2 ht1⟩
    simpa [l, inv_mul_cancel₀ ht0.ne'] using h

/-- The points attaining a linear upper bound on a finite hull lie in the hull of
the labels attaining that bound. -/
private theorem mem_hull_of_support_eq {x : ι → OldSpace} {S T : Finset ι}
    {y : OldSpace} (hy : y ∈ faceHull x S) (g : OldSpace →ₗ[ℝ] ℝ)
    (hmax : ∀ a ∈ S, g (x a) ≤ g y)
    (hT : ∀ a, a ∈ T ↔ a ∈ S ∧ g (x a) = g y) : y ∈ faceHull x T := by
  classical
  obtain ⟨κ, _, w, v, hw, h1, hv, hy'⟩ := mem_convexHull_iff_exists_fintype.1 hy
  have hle (i : κ) : g (v i) ≤ g y := by
    obtain ⟨a, ha, hva⟩ := hv i
    exact hva ▸ hmax a ha
  have hsum : ∑ i, w i * (g y - g (v i)) = 0 := by
    calc
      _ = (∑ i, w i) * g y - g (∑ i, w i • v i) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, map_sum, map_smul, smul_eq_mul]
      _ = 0 := by rw [h1, hy', one_mul, sub_self]
  let I := Finset.univ.filter fun i => w i ≠ 0
  have hI (i : κ) (hi : i ∈ I) : v i ∈ facePoints x T := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hw i) (sub_nonneg.2 (hle i)))).1 hsum i (Finset.mem_univ i)
    have he := (mul_eq_zero.1 hz).resolve_left (Finset.mem_filter.1 hi).2
    obtain ⟨a, ha, hva⟩ := hv i
    rw [← hva] at he
    exact ⟨a, (hT a).2 ⟨ha, (sub_eq_zero.1 he).symm⟩, hva⟩
  have hz (i : κ) (_ : i ∈ Finset.univ) (hi : i ∉ I) : w i = 0 := by
    by_contra hn
    exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, hn⟩)
  have hsw := Finset.sum_subset (Finset.filter_subset _ _) hz
  have hsv : ∑ i ∈ I, w i • v i = y :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun i hi hn => by rw [hz i hi hn, zero_smul])
      |>.trans hy'
  rw [← hsv]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw i) (hsw.trans h1)
    (fun i hi => subset_convexHull ℝ _ (hI i hi))

/-- Coning from the center of an exposed face reduces a noncentral point to a point
of a proper exposed subface. -/
theorem cone_descent [Fintype ι] {x : ι → OldSpace} {S : Finset ι}
    (hS : FaceLabels x S) {z : OldSpace} (hz : z ∈ faceHull x S)
    (hne : z ≠ faceCenter x S) :
    ∃ T, FaceLabels x T ∧ T < S ∧ ∃ y ∈ faceHull x T,
      z ∈ segment ℝ (faceCenter x S) y := by
  classical
  let H := faceHull x S
  have hcv : Convex ℝ H := convex_convexHull ℝ _
  let A := affineSpan ℝ H
  let c : A := ⟨faceCenter x S, subset_affineSpan ℝ H (center_mem_hull x hS.1)⟩
  let _ : Nonempty A := ⟨c⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ c
  let φ : A.direction →ᵃ[ℝ] OldSpace := A.subtype.comp e.toAffineEquiv.toAffineMap
  let C : Set A.direction := φ ⁻¹' H
  have hemb : Topology.IsClosedEmbedding φ :=
    A.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.comp
      e.toHomeomorph.isClosedEmbedding
  have hcompact : IsCompact C := hemb.isCompact_preimage
    ((S.finite_toSet.image x).isCompact_convexHull ℝ)
  have hcint : (interior C).Nonempty := by
    obtain ⟨q, hq⟩ := Set.Nonempty.intrinsicInterior hcv (⟨z, hz⟩ : H.Nonempty)
    obtain ⟨q', hq', _⟩ := mem_intrinsicInterior.1 hq
    refine ⟨e.symm q', ?_⟩
    change e.symm q' ∈ interior (e.toHomeomorph ⁻¹' ((↑) ⁻¹' H : Set A))
    rw [← e.toHomeomorph.preimage_interior]
    simpa using hq'
  let z' := e.symm ⟨z, subset_affineSpan ℝ H hz⟩
  have hzφ : φ z' = z := by simp [φ, z']
  have hφ (v : A.direction) : φ v = (v : OldSpace) + faceCenter x S := rfl
  have hφ0 : φ 0 = faceCenter x S := by simp [hφ]
  have hz' : z' ∈ C := by simpa only [C, mem_preimage, hzφ] using hz
  have hn' : z' ≠ 0 := fun he => hne (hzφ.symm.trans (he ▸ hφ0))
  obtain ⟨y', hy', hfront, hseg⟩ := ray_endpoint hcompact hz' hn'
  obtain ⟨f, hf, hsup⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point (hcv.affine_preimage φ) hfront hcint
  obtain ⟨g, hg⟩ := f.toLinearMap.exists_extend
  have hge (v : A.direction) : g (φ v) = f v + g (faceCenter x S) := by
    rw [hφ, map_add]
    exact congrArg (· + g (faceCenter x S)) (LinearMap.congr_fun hg v)
  let y := φ y'
  have hmax (a : ι) (ha : a ∈ S) : g (x a) ≤ g y := by
    have haH : x a ∈ H := subset_convexHull ℝ _ (label_mem_points x ha)
    let a' := e.symm ⟨x a, subset_affineSpan ℝ H haH⟩
    have haφ : φ a' = x a := by simp [φ, a']
    have haC : a' ∈ C := by simpa only [C, mem_preimage, haφ] using haH
    rw [← haφ, show y = φ y' from rfl, hge, hge]
    exact add_le_add_left (hsup a' haC) _
  let T := S.filter fun a => g (x a) = g y
  have hT (a : ι) : a ∈ T ↔ a ∈ S ∧ g (x a) = g y := Finset.mem_filter
  have hyT := mem_hull_of_support_eq hy' g hmax hT
  obtain ⟨_, a, ha, _⟩ := convexHull_nonempty_iff.1 ⟨y, hyT⟩
  have ha' := (hT a).1 ha
  have hface := expose_relative hS ha'.1 g (fun b hb => ha'.2.symm ▸ hmax b hb)
    (fun b => by rw [ha'.2]; exact hT b)
  have hTS : T < S := by
    refine lt_of_le_of_ne (Finset.filter_subset _ _) (fun he => hf ?_)
    have hker : A.direction ≤ LinearMap.ker g := by
      change (affineSpan ℝ (faceHull x S)).direction ≤ _
      rw [faceHull, affineSpan_convexHull]
      change faceDir x S ≤ _
      exact dir_le_ker ha'.1 (fun b hb => ((hT b).1 (he.symm ▸ hb)).2.trans ha'.2.symm)
    ext v
    exact (LinearMap.congr_fun hg v).symm.trans (hker v.2)
  refine ⟨T, hface, hTS, y, hyT, ?_⟩
  rw [← hφ0, ← hzφ, ← image_segment ℝ φ]
  exact ⟨z', hseg, rfl⟩

end

end K1_13_5_4_2_5_1_1_1
end PackSource_K1_13_5_4_2_5_1_1_1Cone

section PackSource_K1_13_5_4_2_5_1_1_1Refine
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1_1

open K1_13_5_4_2_5_1 K1_13_5_4_2_5_1_1 Set

noncomputable section

variable {ι : Type} [Fintype ι]

/-- If a proper face has codimension greater than one, tilt its support inside the
parent face up to the first new tie, leaving one chosen label strictly below it. -/
private theorem exists_intermediate {x : ι → OldSpace} {T S : Finset ι}
    (hT : FaceLabels x T) (hS : FaceLabels x S) (hTS : T < S)
    (hgap : faceDim x T + 1 < faceDim x S) :
    ∃ R, FaceLabels x R ∧ T < R ∧ R < S := by
  classical
  obtain ⟨⟨a, ha⟩, f, hf⟩ := hT
  obtain ⟨b, hbS, hbT⟩ := Finset.exists_of_ssubset hTS
  have hker : faceDir x T ≤ LinearMap.ker f :=
    dir_le_ker ha (fun i hi => le_antisymm ((hf a).1 ha i) ((hf i).1 hi a))
  have hb : x b - x a ∉ faceDir x T := by
    intro hm
    have he := hker hm
    change f (x b - x a) = 0 at he
    rw [map_sub, sub_eq_zero] at he
    exact (expose_lt hf ha hbT).ne he
  let W := faceDir x T ⊔ Submodule.span ℝ {x b - x a}
  have hrank : Module.finrank ℝ W = faceDim x T + 1 := by
    exact Submodule.finrank_sup_span_singleton hb
  have hn : ¬ faceDir x S ≤ W := by
    intro hl
    exact hgap.not_ge (hrank ▸ Submodule.finrank_mono hl)
  have haS := hTS.le ha
  obtain ⟨c, hcS, hcW⟩ : ∃ c ∈ S, x c - x a ∉ W := by
    by_contra! h
    apply hn
    rw [dir_eq_span_sub x haS, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact h i hi
  obtain ⟨g, hg, hgc⟩ := LinearMap.exists_extend_of_notMem
    (0 : W →ₗ[ℝ] ℝ) hcW (1 : ℝ)
  have hgW {v : OldSpace} (hv : v ∈ W) : g v = 0 := by
    simpa using LinearMap.congr_fun hg ⟨v, hv⟩
  let d (i : ι) := g (x i) - g (x a)
  have hd (i : ι) (hi : i ∈ T) : d i = 0 := by
    have hm : x i - x a ∈ W := (le_sup_left : faceDir x T ≤ W) (label_sub_mem_dir x ha hi)
    simpa [d, map_sub] using hgW hm
  have hdb : d b = 0 := by
    have hle : Submodule.span ℝ {x b - x a} ≤ W := le_sup_right
    simpa [d, map_sub] using hgW (hle (Submodule.subset_span (mem_singleton _)))
  have hdc : d c = 1 := by simpa [d, map_sub] using hgc
  let P := S.filter fun i => 0 < d i
  have hcP : c ∈ P := Finset.mem_filter.2 ⟨hcS, by simp [hdc]⟩
  let q (i : ι) := (f (x a) - f (x i)) / d i
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image P q ⟨c, hcP⟩
  let t := q j
  have hjp := (Finset.mem_filter.1 hj).2
  have hjT : j ∉ T := fun hjT => hjp.ne' (hd j hjT)
  have ht : 0 < t := div_pos (sub_pos.mpr (expose_lt hf ha hjT)) hjp
  let u := f + t • g
  have hu (i : ι) : u (x i) - u (x a) = f (x i) - f (x a) + t * d i := by
    change (f (x i) + t * g (x i)) - (f (x a) + t * g (x a)) = _
    dsimp only [d]
    ring
  have hle (i : ι) (hi : i ∈ S) : u (x i) ≤ u (x a) := by
    apply sub_nonpos.1
    rw [hu]
    by_cases hip : 0 < d i
    · have h := (le_div_iff₀ hip).1 (hmin i (Finset.mem_filter.2 ⟨hi, hip⟩))
      linarith
    · have h := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hip)
      linarith [(hf a).1 ha i]
  let R := S.filter fun i => u (x i) = u (x a)
  have hR : FaceLabels x R := expose_relative hS haS u hle (fun _ => Finset.mem_filter)
  have hTR : T ⊆ R := by
    intro i hi
    refine Finset.mem_filter.2 ⟨hTS.le hi, sub_eq_zero.1 ?_⟩
    rw [hu, hd i hi, mul_zero, add_zero, sub_eq_zero]
    exact le_antisymm ((hf a).1 ha i) ((hf i).1 hi a)
  have hjR : j ∈ R := by
    refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj).1, sub_eq_zero.1 ?_⟩
    rw [hu]
    have he : t * d j = f (x a) - f (x j) := div_mul_cancel₀ _ hjp.ne'
    linarith
  have hbR : b ∉ R := by
    intro h
    have he := sub_eq_zero.2 (Finset.mem_filter.1 h).2
    rw [hu, hdb, mul_zero, add_zero, sub_eq_zero] at he
    exact (expose_lt hf ha hbT).ne he
  exact ⟨R, hR, lt_of_le_of_ne hTR (fun he => hjT (he.symm ▸ hjR)),
    lt_of_le_of_ne (Finset.filter_subset _ _) (fun he => hbR (he.symm ▸ hbS))⟩

/-- A proper exposed subface is contained in a facet of its parent face. -/
theorem exists_facet {x : ι → OldSpace} {T S : Finset ι}
    (hT : FaceLabels x T) (hS : FaceLabels x S) (hTS : T < S) :
    ∃ R, FaceLabels x R ∧ T ⊆ R ∧ R < S ∧ faceDim x R + 1 = faceDim x S := by
  classical
  let P := Finset.univ.filter fun R : Finset ι => FaceLabels x R ∧ T ⊆ R ∧ R < S
  have hTP : T ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hT, le_rfl, hTS⟩
  obtain ⟨R, hRP, hmax⟩ := Finset.exists_max_image P Finset.card ⟨T, hTP⟩
  obtain ⟨hR, hTR, hRS⟩ := (Finset.mem_filter.1 hRP).2
  refine ⟨R, hR, hTR, hRS, ?_⟩
  have hlt := faceDim_lt hR hRS
  by_contra! hn
  obtain ⟨U, hU, hRU, hUS⟩ := exists_intermediate hR hS hRS (by omega)
  have hUP : U ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hU, hTR.trans hRU.le, hUS⟩
  exact (Finset.card_lt_card hRU).not_ge (hmax U hUP)

end

end K1_13_5_4_2_5_1_1_1
end PackSource_K1_13_5_4_2_5_1_1_1Refine

section PackSource_K1_13_5_4_2_5_1_1_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_1_1_1

open K1_13_5_4_2_5_1 K1_13_5_4_2_5_1_1 Set

noncomputable section

variable {ι : Type}

private theorem eq_center_of_dim_zero {x : ι → OldSpace} {S : Finset ι}
    (hS : S.Nonempty) (hd : faceDim x S = 0) {z : OldSpace} (hz : z ∈ faceHull x S) :
    z = faceCenter x S := by
  have hbot : faceDir x S = ⊥ := Submodule.finrank_eq_zero.1 hd
  have hm : z - faceCenter x S ∈ faceDir x S :=
    AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hz)
      (convexHull_subset_affineSpan _ (center_mem_hull x hS))
  rwa [hbot, Submodule.mem_bot, sub_eq_zero] at hm

private theorem cone_facet [Fintype ι] {x : ι → OldSpace} {S : Finset ι}
    (hS : FaceLabels x S) (hd : 0 < faceDim x S) {z : OldSpace} (hz : z ∈ faceHull x S) :
    ∃ R, FaceLabels x R ∧ R < S ∧ faceDim x R + 1 = faceDim x S ∧
      ∃ y ∈ faceHull x R, z ∈ segment ℝ (faceCenter x S) y := by
  have hstep : ∃ T, FaceLabels x T ∧ T < S ∧ ∃ y ∈ faceHull x T,
      z ∈ segment ℝ (faceCenter x S) y := by
    by_cases hn : z = faceCenter x S
    · obtain ⟨a, ha⟩ := hS.1
      obtain ⟨p, hp, hpne⟩ : ∃ p ∈ faceHull x S, p ≠ faceCenter x S := by
        by_contra! hc
        have hall (b : ι) (hb : b ∈ S) : x b = faceCenter x S :=
          hc _ (subset_convexHull ℝ _ (label_mem_points x hb))
        have hbot : faceDir x S ≤ ⊥ := by
          rw [dir_eq_span_sub x ha, Submodule.span_le]
          rintro _ ⟨b, hb, rfl⟩
          simp [hall b hb, hall a ha]
        have hd₀ : faceDim x S = 0 := Submodule.finrank_eq_zero.2 (le_antisymm hbot bot_le)
        omega
      obtain ⟨T, hT, hTS, y, hy, _⟩ := cone_descent hS hp hpne
      exact ⟨T, hT, hTS, y, hy, hn.symm ▸ left_mem_segment ℝ _ _⟩
    · exact cone_descent hS hz hn
  obtain ⟨T, hT, hTS, y, hy, hzy⟩ := hstep
  obtain ⟨R, hR, hTR, hRS, hr⟩ := exists_facet hT hS hTS
  exact ⟨R, hR, hRS, hr, y, hull_mono x hTR hy, hzy⟩

/-- Every point of the full-dimensional hull lies in a tetrahedron of face centers. -/
theorem proof : K1_13_5_4_2_5_1_1.c1 := by
  classical
  intro ι _ x hfull
  have hHull : faceHull x Finset.univ = convexHull ℝ (range x) := by
    simp [faceHull, facePoints, image_univ]
  obtain ⟨_, a, rfl⟩ := convexHull_nonempty_iff.1 (hfull.mono interior_subset)
  have htop : FaceLabels x Finset.univ :=
    ⟨⟨a, Finset.mem_univ _⟩, 0, by simp [Maximizes]⟩
  have hdim : faceDim x Finset.univ = 3 := by
    unfold faceDim faceDir facePoints
    rw [Finset.coe_univ, image_univ, affineSpan_eq_top_of_nonempty_interior hfull,
      AffineSubspace.direction_top, finrank_top]
    exact Module.finrank_fin_fun ℝ
  apply subset_antisymm
  · intro z hz
    rw [← hHull] at hz
    obtain ⟨S₂, h₂, h₂₃, hd₂, y₂, hy₂, hs₃⟩ := cone_facet htop (by omega) hz
    obtain ⟨S₁, h₁, h₁₂, hd₁, y₁, hy₁, hs₂⟩ := cone_facet h₂ (by omega) hy₂
    obtain ⟨S₀, h₀, h₀₁, hd₀, y₀, hy₀, hs₁⟩ := cone_facet h₁ (by omega) hy₁
    let L : Fin 4 → Finset ι := ![S₀, S₁, S₂, Finset.univ]
    have hm : StrictMono L := by
      apply Fin.strictMono_iff_lt_succ.2
      intro i
      fin_cases i
      exacts [h₀₁, h₁₂, h₂₃]
    have hL (i : Fin 4) : FaceLabels x (L i) := by
      fin_cases i
      exacts [h₀, h₁, h₂, htop]
    let F : FaceFlag x := ⟨L, hm, hL, rfl⟩
    have hc (i : Fin 4) : faceCenter x (L i) ∈ tetrahedron (flagVertices F) :=
      subset_convexHull ℝ _ (mem_range_self i)
    have cv : Convex ℝ (tetrahedron (flagVertices F)) := convex_convexHull ℝ _
    have hcy₀ : y₀ ∈ tetrahedron (flagVertices F) :=
      (eq_center_of_dim_zero h₀.1 (by omega) hy₀).symm ▸ hc 0
    have hcy₁ := cv.segment_subset (hc 1) hcy₀ hs₁
    have hcy₂ := cv.segment_subset (hc 2) hcy₁ hs₂
    exact mem_iUnion.2 ⟨F, cv.segment_subset (hc 3) hcy₂ hs₃⟩
  · intro z hz
    obtain ⟨F, hF⟩ := mem_iUnion.1 hz
    apply convexHull_min _ (convex_convexHull ℝ (range x)) hF
    rintro _ ⟨i, rfl⟩
    rw [← hHull]
    exact hull_mono x (Finset.subset_univ _) (center_mem_hull x (F.property.2.1 i).1)

end

end K1_13_5_4_2_5_1_1_1
end PackSource_K1_13_5_4_2_5_1_1_1Proof

section PackSource_K1_13_5_4_2_4_2_3_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_4_2_3_1

noncomputable section

open K1_13_5_4_2_4 K1_13_5_4_2_4_2 K1_13_5_4_2_4_2_3 MvPolynomial

variable {A : Fin 4 → Finset Exponent}

private theorem dehom_constantChart (hz : ∀ j, 0 ∈ A j) :
    dehom A (constantChart A hz) = 1 := by
  classical
  rw [constantChart, chartProduct, map_prod]
  apply Finset.prod_eq_one
  intro j _
  simp [dehom, monomial_zero']

private theorem constantChart_homogeneous (hz : ∀ j, 0 ∈ A j) :
    (constantChart A hz).IsWeightedHomogeneous (slotWeight A) (fun _ => 1) := by
  classical
  have hweight : (∑ j : Fin 4, (Pi.single j 1 : Degree)) = fun _ => 1 := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hweight, constantChart, chartProduct]
  exact IsWeightedHomogeneous.prod _ _ _ fun j _ =>
    isWeightedHomogeneous_X (CoefficientField A) (slotWeight A) (⟨j, ⟨0, hz j⟩⟩ : Slot A)

theorem proof : K1_13_5_4_2_4_2_3.c1 := by
  classical
  intro A hz hv i f hf
  obtain ⟨⟨d, hfd⟩, hfI⟩ := hf
  let s : Finset (Fin 4) := Finset.univ.filter fun j => j.val < i.val + 1
  have hs : (↑s : Set (Fin 4)) = {j | j.val < i.val + 1} := by
    ext j
    simp [s]
  have hfspan : dehom A f ∈ Submodule.span (Row A) (genericEquation A '' ↑s) := by
    rw [hs]
    exact hfI
  rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hfspan
  obtain ⟨c, hc⟩ := hfspan
  simp only [smul_eq_mul] at hc
  choose q hq using fun j => piece_exhaustive hz hv (c j)

  -- Pad all four degrees enough to lift each affine multiplier.
  let n := Finset.univ.sup q + 1
  let D : Degree := (fun _ => n) + d
  have hsingle (j l : Fin 4) : (Pi.single j 1 : Degree) l ≤ 1 := by
    by_cases h : l = j
    · simp [h]
    · simp [Pi.single_eq_of_ne h]
  have hpad (j : Fin 4) : (fun _ => q j) ≤ D - Pi.single j 1 := by
    intro l
    have hqj : q j ≤ Finset.univ.sup q := Finset.le_sup (Finset.mem_univ j)
    have hj := hsingle j l
    change q j ≤ Finset.univ.sup q + 1 + d l - (Pi.single j 1 : Degree) l
    omega
  have hdegree (j : Fin 4) : D - Pi.single j 1 + Pi.single j 1 = D := by
    funext l
    have hj := hsingle j l
    change D l - (Pi.single j 1 : Degree) l + (Pi.single j 1 : Degree) l = D l
    apply Nat.sub_add_cancel
    change (Pi.single j 1 : Degree) l ≤ Finset.univ.sup q + 1 + d l
    omega
  have hlift (j : Fin 4) : ∃ r ∈ slotPiece A (D - Pi.single j 1), dehom A r = c j := by
    have hm := piece_mono hz (hpad j) (hq j)
    rw [← map_slotPiece] at hm
    exact hm
  choose r hr hrd using hlift
  let g := ∑ j ∈ s, r j * homogeneousEquation A j
  have hgd : g ∈ slotPiece A D := by
    apply Submodule.sum_mem
    intro j _
    rw [← hdegree j]
    exact (show (r j).IsWeightedHomogeneous _ _ from hr j).mul
      (show (homogeneousEquation A j).IsWeightedHomogeneous _ _ from homogeneousEquation_mem j)
  have hg : dehom A g = dehom A f := by
    simpa only [g, map_sum, map_mul, hrd, dehom_equation] using hc
  have hgcut : g ∈ Ideal.span (homogeneousEquation A '' {j : Fin 4 | j.val < i.val + 1}) := by
    apply Ideal.sum_mem
    intro j hj
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩)

  -- The homogeneous remainder vanishes after dehomogenization.
  have hweight : n • (fun _ => 1 : Degree) = fun _ => n := by
    funext j
    simp [Pi.smul_apply]
  have hpower := (constantChart_homogeneous hz).pow n
  rw [hweight] at hpower
  have hprod : (constantChart A hz ^ n * f).IsWeightedHomogeneous (slotWeight A) D :=
    hpower.mul hfd
  have hrel : constantChart A hz ^ n * f - g ∈ relationIdeal A 0 := by
    apply Ideal.subset_span
    refine ⟨⟨D, hprod.sub hgd⟩, ?_⟩
    rw [map_sub, map_mul, map_pow, dehom_constantChart, one_pow, one_mul, hg, sub_self]
    exact (prefixIdeal A 0).zero_mem
  refine ⟨n, ?_⟩
  have hrem : constantChart A hz ^ n * f - g ∈ cutIdeal A (i.val + 1) :=
    Submodule.mem_sup_left hrel
  have hcut : g ∈ cutIdeal A (i.val + 1) :=
    Submodule.mem_sup_right hgcut
  simpa only [sub_add_cancel] using (cutIdeal A (i.val + 1)).add_mem hrem hcut

end

end K1_13_5_4_2_4_2_3_1
end PackSource_K1_13_5_4_2_4_2_3_1Proof

section PackSource_K1_13_7_2_3_1_3Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_13_7_2_3_1_3

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 MvPolynomial
open scoped BigOperators nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

private abbrev extendCurve (C : Ideal GeoJets) (a : Shape) : Ideal (SectionJets a) :=
  C.map (MvPolynomial.map (algebraMap GeoField (SectionField a)))

/-- The coefficient field is purely transcendental. Before localization the
coefficient of the variable indexed by the zero exponent is 1 on the curve. -/
private theorem generic_regular (C : Ideal GeoJets) (a : Shape) (hC : C.IsPrime) :
    (extendCurve C a).IsPrime ∧ genericSection a ∉ extendCurve C a := by
  classical
  let A := MvPolynomial (SectionIndex a) GeoField
  let R := MvPolynomial (SectionIndex a) GeoJets
  let T := MvPolynomial (Fin 4) A
  let S := SectionJets a
  let e : R ≃ₐ[GeoField] T := commAlgEquiv GeoField (SectionIndex a) (Fin 4)
  let I : Ideal R := C.map MvPolynomial.C
  let I' : Ideal T := I.map e.toRingHom
  let M : Submonoid T := (nonZeroDivisors A).map MvPolynomial.C
  have : IsLocalization M S := MvPolynomial.isLocalization (nonZeroDivisors A) (SectionField a)
  have := hC
  have hI : I.IsPrime := by
    rw [show I = RingHom.ker (MvPolynomial.map (σ := SectionIndex a) (Ideal.Quotient.mk C)) by
      rw [MvPolynomial.ker_map, Ideal.mk_ker]]
    exact RingHom.ker_isPrime _
  have hback : I'.comap e.toRingHom = I := Ideal.comap_map_of_bijective _ e.bijective
  have hI' : I'.IsPrime := by
    have := hI
    exact Ideal.map_isPrime_of_surjective (f := e.toRingHom) e.surjective
      (by rw [(RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective]; exact bot_le)
  have hdisj : Disjoint (M : Set T) (I' : Set T) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ hmem
    have hpre : e.symm (MvPolynomial.C s) ∈ I := by
      rw [← hback, Ideal.mem_comap]
      change e (e.symm (MvPolynomial.C s)) ∈ I'
      rw [AlgEquiv.apply_symm_apply]
      exact hmem
    change commAlgEquiv GeoField (Fin 4) (SectionIndex a) (MvPolynomial.C s) ∈ I at hpre
    rw [commAlgEquiv_C] at hpre
    obtain ⟨m, hm⟩ := support_nonempty.mpr (nonZeroDivisors.ne_zero hs)
    have hc := MvPolynomial.mem_map_C_iff.mp hpre m
    rw [MvPolynomial.coeff_map] at hc
    exact hC.ne_top (C.eq_top_of_isUnit_mem hc
      (IsUnit.map _ (isUnit_iff_ne_zero.mpr (mem_support_iff.mp hm))))
  have hJ : I'.map (algebraMap T S) = extendCurve C a := by
    simp only [I', I, extendCurve, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro p
    change algebraMap T S (e (MvPolynomial.C p)) = MvPolynomial.map _ p
    rw [commAlgEquiv_C, MvPolynomial.algebraMap_def, MvPolynomial.map_map]
    congr 1
  refine ⟨hJ ▸ IsLocalization.isPrime_of_isPrime_disjoint M S I' hI' hdisj, ?_⟩
  let G : R := ∑ m ∈ boxMonomials a,
    MvPolynomial.X m * MvPolynomial.C (∏ i : Fin 4, MvPolynomial.X i ^ (m i).val)
  have hG : algebraMap T S (e G) = genericSection a := by
    unfold G genericSection
    simp only [map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro m _
    dsimp only [e]
    rw [commAlgEquiv_X, commAlgEquiv_C]
    simp only [map_prod, map_pow, MvPolynomial.map_X]
    change (MvPolynomial.map (algebraMap A (SectionField a))) (MvPolynomial.C (MvPolynomial.X m)) *
      (∏ i : Fin 4, (MvPolynomial.map (algebraMap A (SectionField a)) (MvPolynomial.X i)) ^
        (m i).val) = _
    simp only [MvPolynomial.map_C, MvPolynomial.map_X, A]
  intro hmem
  have hG' : algebraMap T S (e G) ∈ I'.map (algebraMap T S) := by rwa [hJ, hG]
  have hG'' : e G ∈ I' := by
    rw [← IsLocalization.under_map_of_isPrime_disjoint M S hI' hdisj]
    exact hG'
  have hGI : G ∈ I := by
    rw [← hback]
    exact hG''
  have hzero : (0 : SectionIndex a) ∈ boxMonomials a := by simp [boxMonomials]
  have hone : G.coeff (Finsupp.single (0 : SectionIndex a) 1) = 1 := by
    have hterm (m : SectionIndex a) :
        (MvPolynomial.X m * MvPolynomial.C (∏ i : Fin 4, MvPolynomial.X i ^ (m i).val) : R).coeff
          (Finsupp.single (0 : SectionIndex a) 1) = if m = 0 then 1 else 0 := by
      rw [mul_comm, coeff_C_mul, coeff_X]
      by_cases hm : m = 0
      · subst m
        simp
      · have hs : Finsupp.single m 1 ≠ Finsupp.single (0 : SectionIndex a) (1 : ℕ) := by
          intro hs
          exact hm (Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0) hs)
        simp [hs, hm]
    calc
      G.coeff (Finsupp.single (0 : SectionIndex a) 1) =
          ∑ m ∈ boxMonomials a, if m = 0 then (1 : GeoJets) else 0 := by
        dsimp only [G]
        rw [MvPolynomial.coeff_sum]
        exact Finset.sum_congr rfl fun m _ => hterm m
      _ = 1 := by simp [hzero]
  exact hC.ne_top ((Ideal.eq_top_iff_one C).mpr (hone ▸ MvPolynomial.mem_map_C_iff.mp hGI _))

end

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_2_3 K1_13_6_2_3_1 MvPolynomial
open scoped BigOperators Pointwise TensorProduct

variable {k : Type*} [Field k]

/-- The image of the doubled cap's monomials in the coordinate algebra. -/
private def capSpace (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Submodule k (MvPolynomial (Fin 4) k ⧸ I) :=
  (restrictSupport k (capExponents p)).map (Ideal.Quotient.mkₐ k I).toLinearMap

instance (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) : Module.Finite k (capSpace I p) := by
  have : Module.Finite k (restrictSupport k (capExponents p)) :=
    Module.Finite.of_basis (basisRestrictSupport k _)
  exact Module.Finite.map _ _

private theorem capSpace_mono (I : Ideal (MvPolynomial (Fin 4) k)) {p q : Shape}
    (hb : p.b ≤ q.b) (hj : p.j ≤ q.j) (ht : p.t ≤ q.t) :
    capSpace I p ≤ capSpace I q := by
  apply Submodule.map_mono
  apply restrictSupport_mono
  intro e he
  rw [cap_coords] at he ⊢
  exact ⟨he.1.trans (by omega), he.2.1.trans (by omega), he.2.2.trans (by omega)⟩

private theorem capSpace_mul_mem {I : Ideal (MvPolynomial (Fin 4) k)} {p q : Shape}
    {f : MvPolynomial (Fin 4) k} (hf : f ∈ restrictSupport k (capExponents q))
    {x : MvPolynomial (Fin 4) k ⧸ I} (hx : x ∈ capSpace I p) :
    Ideal.Quotient.mk I f * x ∈ capSpace I (p.plus q) := by
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  refine ⟨f * g, ?_, map_mul (Ideal.Quotient.mk I) _ _⟩
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul f g he)
  have hu' := (cap_coords q u).mp (hf hu)
  have hv' := (cap_coords p v).mp (hg hv)
  simp only [cap_coords, Finsupp.add_apply, Shape.plus]
  omega

private theorem monomial_preimage {S : Set (Fin 4 →₀ ℕ)} {n : ℕ} {e : Fin 4 →₀ ℕ}
    (he : e ∈ n • S) :
    ∃ P : MvPolynomial S k, P.totalDegree ≤ n ∧ monomialMap k S P = monomial e 1 := by
  induction n generalizing e with
  | zero =>
    rw [zero_smul, Set.mem_zero] at he
    subst e
    exact ⟨1, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at he
    obtain ⟨u, hu, v, hv, rfl⟩ := he
    obtain ⟨P, hP, hmap⟩ := ih hu
    refine ⟨P * MvPolynomial.X ⟨v, hv⟩, ?_, ?_⟩
    · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
    · rw [map_mul, hmap, monomialMap_X, monomial_mul_monomial, mul_one]

private theorem cap_hilbertFunction (I : Ideal (MvPolynomial (Fin 4) k))
    (p : Shape) (hp : ChamberBox p) (n : ℕ) :
    affineHilbertFunction (I.comap (monomialMap k (capExponents p)).toRingHom) n =
      Module.finrank k (capSpace I (p.scale n)) := by
  classical
  let φ := monomialMap k (capExponents p)
  let J := I.comap φ.toRingHom
  let g := Ideal.quotientMapₐ I φ (le_rfl : J ≤ Ideal.comap φ.toRingHom I)
  have hg (P : MvPolynomial (capExponents p) k) :
      g (Ideal.Quotient.mk J P) = Ideal.Quotient.mk I (φ P) := rfl
  have hmap : (quotientDegreeLE J n).map g.toLinearMap = capSpace I (p.scale n) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hx
      refine ⟨φ P, ?_, hg P |>.symm⟩
      change φ P ∈ restrictSupport k (capExponents (p.scale n))
      rw [← nsmul_cap p hp n]
      exact monomialMap_mem_restrictSupport_nsmul (zero_mem_cap p) hP
    · rw [capSpace, restrictSupport_eq_span, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
      rw [← nsmul_cap p hp n] at he
      obtain ⟨P, hP, hφ⟩ := monomial_preimage (k := k) he
      exact ⟨Ideal.Quotient.mk J P, mk_mem_quotientDegreeLE hP, by simp [hg, φ, hφ]⟩
  have hinj : Function.Injective g.toLinearMap := Ideal.quotientMap_injective
  change Module.finrank k (quotientDegreeLE J n) = _
  rw [← hmap]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq

section ScalarExtension

variable {E : Type*} [Field E] [Algebra k E]

private def quotientTensor (I : Ideal (MvPolynomial (Fin 4) k)) :
    E ⊗[k] (MvPolynomial (Fin 4) k ⧸ I) ≃ₐ[E]
      MvPolynomial (Fin 4) E ⧸ I.map (MvPolynomial.map (algebraMap k E)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) k E
  let j : MvPolynomial (Fin 4) k →ₐ[k] E ⊗[k] MvPolynomial (Fin 4) k :=
    Algebra.TensorProduct.includeRight
  have hc : e.toRingHom.comp j.toRingHom = MvPolynomial.map (algebraMap k E) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = _
    simp [e]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k) E _ E I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  exact ((Ideal.map_map (I := I) j.toRingHom e.toRingHom).trans
    (congrArg (fun f => I.map f) hc)).symm

/-- Extending scalars preserves the dimension of the cap's quotient image. -/
private theorem finrank_capSpace_map (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Module.finrank E (capSpace (I.map (MvPolynomial.map (algebraMap k E))) p) =
      Module.finrank k (capSpace I p) := by
  let e := (quotientTensor (E := E) I).toLinearEquiv
  have h : ((capSpace I p).baseChange E).map e.toLinearMap =
      capSpace (I.map (MvPolynomial.map (algebraMap k E))) p := by
    simp only [capSpace, restrictSupport_eq_span, Submodule.map_span, Submodule.baseChange_span,
      Set.image_image]
    congr 1
    apply Set.image_congr
    intro m _
    change quotientTensor (E := E) I (1 ⊗ₜ[k] (Ideal.Quotient.mk I (monomial m 1))) =
      Ideal.Quotient.mk _ (monomial m 1)
    simp [quotientTensor, MvPolynomial.map_monomial]
  rw [← h, ← (Submodule.equivMapOfInjective e.toLinearMap e.injective _).finrank_eq,
    ← (Submodule.toBaseChange.toLinearEquiv E (capSpace I p)).finrank_eq, Module.finrank_baseChange]

end ScalarExtension

/-- All monomials of total degree at most n fit in the n-th baseline cap. -/
private theorem totalDegree_mem_baseline {f : MvPolynomial (Fin 4) k} {n : ℕ}
    (hf : f.totalDegree ≤ n) : f ∈ restrictSupport k (capExponents ((⟨3, 3, 1⟩ : Shape).scale n)) := by
  intro e he
  have h := (le_totalDegree he).trans hf
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_four] at h
  simp only [cap_coords, Shape.scale]
  omega

private theorem generic_support (h : Shape) :
    genericSection (h.scale 6) ∈
      restrictSupport (SectionField (h.scale 6)) (capExponents (h.scale 3)) := by
  classical
  apply Submodule.sum_mem
  intro m hm
  rw [MvPolynomial.prod_X_pow, C_mul_monomial]
  rw [monomial_mem_restrictSupport]
  left
  obtain ⟨hb, hj, ht⟩ := (Finset.mem_filter.mp hm).2
  simp only [cap_coords, Finsupp.indicator_of_mem (Finset.mem_univ _), Shape.scale]
  simp only [Fin.sum_univ_four, Shape.scale] at hb hj ht
  change 0 * (m 0).val + 1 * (m 1).val + 2 * (m 2).val + 3 * (m 3).val ≤ 6 * h.j at hj
  omega

end

noncomputable section

open K1_13 K1_13_6_2_3 MvPolynomial

private abbrev baseline : Shape := ⟨3, 3, 1⟩

/-- Once the baseline filtration surjects onto the section, increasing the
support by one copy of the cutter adds at least one section length. -/
private theorem rank_growth {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin 4) k)) (hI : I.IsPrime)
    (hdim : (affineHilbertPolynomial I).natDegree = 1)
    (g : MvPolynomial (Fin 4) k) (hg : g ∉ I)
    (q : Shape) (hsupport : g ∈ restrictSupport k (capExponents q)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      m * Module.finrank k (MvPolynomial (Fin 4) k ⧸ (I ⊔ Ideal.span {g})) +
        Module.finrank k (capSpace I (baseline.scale n)) ≤
      Module.finrank k (capSpace I ((baseline.scale n).plus (q.scale m))) := by
  have := hI
  let J := I ⊔ Ideal.span {g}
  have hJ : (affineHilbertPolynomial J).natDegree = 0 := by
    have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hI hg le_rfl).1
    change (affineHilbertPolynomial J).natDegree ≤ _ at h
    rw [hdim] at h
    omega
  have := (natDegree_affineHilbertPolynomial_eq_zero_iff (I := J)).mp hJ
  obtain ⟨N, hN⟩ := exists_quotientDegreeLE_eq_top J
  refine ⟨N, fun n hn m => ?_⟩
  let W := fun m => capSpace I ((baseline.scale n).plus (q.scale m))
  let c := Ideal.Quotient.mk I g
  have hc : c ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hg
  let cut := Ideal.Quotient.factorₐ k (le_sup_left : I ≤ J)
  have hstep (m : ℕ) : Module.finrank k (MvPolynomial (Fin 4) k ⧸ J) +
      Module.finrank k (W m) ≤ Module.finrank k (W (m + 1)) := by
    let π := cut.toLinearMap.domRestrict (W (m + 1))
    have hπ : Function.Surjective π := by
      intro x
      have hx : x ∈ quotientDegreeLE J n := by rw [hN n hn]; trivial
      obtain ⟨f, hf, rfl⟩ := mem_quotientDegreeLE.mp hx
      have hbase : Ideal.Quotient.mk I f ∈ capSpace I (baseline.scale n) :=
        ⟨f, totalDegree_mem_baseline hf, rfl⟩
      have hincl : capSpace I (baseline.scale n) ≤ W (m + 1) :=
        capSpace_mono I (Nat.le_add_right ..) (Nat.le_add_right ..) (Nat.le_add_right ..)
      exact ⟨⟨Ideal.Quotient.mk I f, hincl hbase⟩, rfl⟩
    have hshape : ((baseline.scale n).plus (q.scale m)).plus q =
        (baseline.scale n).plus (q.scale (m + 1)) := by
      cases q
      simp only [Shape.plus, Shape.scale, Nat.add_mul, one_mul, Nat.add_assoc]
    have hmul (x : W m) : c * (x : MvPolynomial (Fin 4) k ⧸ I) ∈ W (m + 1) := by
      rw [show W (m + 1) = capSpace I (((baseline.scale n).plus (q.scale m)).plus q) by
        rw [hshape]]
      exact capSpace_mul_mem hsupport x.property
    let μ := ((LinearMap.mulLeft k c).domRestrict (W m)).codRestrict (W (m + 1)) hmul
    have hμ : Function.Injective μ := fun x y hxy =>
      Subtype.ext (mul_left_cancel₀ hc (congrArg Subtype.val hxy))
    have hcut : cut c = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
    have hker : LinearMap.range μ ≤ LinearMap.ker π := by
      rintro _ ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      change cut (c * x.val) = 0
      rw [map_mul, hcut, zero_mul]
    have hrank := π.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hπ, finrank_top] at hrank
    change Module.finrank k (MvPolynomial (Fin 4) k ⧸ J) +
      Module.finrank k (LinearMap.ker π) = Module.finrank k (W (m + 1)) at hrank
    have hbound : Module.finrank k (W m) ≤ Module.finrank k (LinearMap.ker π) := (LinearMap.finrank_range_of_inj hμ).symm.trans_le
      (Submodule.finrank_mono hker)
    omega
  change m * Module.finrank k (MvPolynomial (Fin 4) k ⧸ J) +
    Module.finrank k (capSpace I (baseline.scale n)) ≤ Module.finrank k (W m)
  induction m with
  | zero =>
    have hzero : W 0 = capSpace I (baseline.scale n) := by
      dsimp only [W]
      congr 1
      simp only [Shape.plus, Shape.scale, Nat.zero_mul, Nat.add_zero]
    rw [hzero, Nat.zero_mul, Nat.zero_add]
  | succ m ih =>
    have hs := hstep m
    rw [Nat.succ_mul]
    omega

end

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_2_3 K1_13_6_2_3_1 K1_13_7_1 MvPolynomial Filter

private theorem cap_surjective (p : Shape) (hp : ChamberBox p) :
    Function.Surjective (monomialMap GeoField (capExponents p)) := by
  apply monomialMap_surjective
  intro i
  have ⟨hb, hj, ht⟩ := hp
  fin_cases i <;> norm_num [cap_coords, Finsupp.single_apply] <;> omega

private theorem linear_degree (a b : ℚ) :
    (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · calc
      (Polynomial.C a * Polynomial.X).natDegree ≤
          (Polynomial.C a).natDegree + (Polynomial.X : Polynomial ℚ).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 := by simp
  · simp

private theorem eval_linear {P : Polynomial ℚ} (h : P.natDegree ≤ 1) (x : ℚ) :
    P.eval x = P.coeff 1 * x + P.coeff 0 := by
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one h]
  simp

theorem proof : K1_13_7_2_3_1.c3 := by
  intro C h hC hdim hh _
  let a := h.scale 6
  let E := SectionField a
  let I := extendCurve C a
  let g := genericSection a
  let d := sectionDegree C a
  let p := baseline.plus h
  have hbase : ChamberBox baseline := ⟨by decide, by decide, by decide⟩
  have hp : ChamberBox p := by
    obtain ⟨hb, hj⟩ := hh
    change 3 + h.j ≤ 3 + h.b ∧ 3 * (1 + h.t) ≤ 3 + h.j ∧ 0 < 1 + h.t
    omega
  have hdI : (affineHilbertPolynomial I).natDegree = 1 := by
    change (affineHilbertPolynomial (C.map (MvPolynomial.map (algebraMap GeoField E)))).natDegree = 1
    rw [K1_13_5_5_2.hilbertPolynomial_map]
    exact hdim
  obtain ⟨hI, hg⟩ := generic_regular C a hC
  obtain ⟨N, hN⟩ := rank_growth I hI hdI g hg (h.scale 3) (generic_support h)
  let B := C.comap (monomialMap GeoField (capExponents baseline)).toRingHom
  let P := C.comap (monomialMap GeoField (capExponents p)).toRingHom
  obtain ⟨NB, hNB⟩ := exists_eval_affineHilbertPolynomial B
  obtain ⟨NP, hNP⟩ := exists_eval_affineHilbertPolynomial P
  have hdB : (affineHilbertPolynomial B).natDegree ≤ 1 :=
    (natDegree_affineHilbertPolynomial_comap_of_surjective _
      (cap_surjective baseline hbase) C).trans hdim |>.le
  have hdP : (affineHilbertPolynomial P).natDegree ≤ 1 :=
    (natDegree_affineHilbertPolynomial_comap_of_surjective _
      (cap_surjective p hp) C).trans hdim |>.le
  let basePoly := affineHilbertPolynomial B
  let sumPoly := affineHilbertPolynomial P
  let lower := Polynomial.C ((d : ℚ) + 3 * basePoly.coeff 1) * Polynomial.X + Polynomial.C (basePoly.coeff 0)
  let upper := Polynomial.C (3 * sumPoly.coeff 1) * Polynomial.X + Polynomial.C (sumPoly.coeff 0)
  have hgrowth : ∀ᶠ m : ℕ in atTop, lower.eval (m : ℚ) ≤ upper.eval (m : ℚ) := by
    filter_upwards [eventually_ge_atTop (N + NB + NP)] with m hm
    have hr := hN (3 * m) (by omega) m
    have hshape : (baseline.scale (3 * m)).plus ((h.scale 3).scale m) = p.scale (3 * m) := by
      cases h
      dsimp [p, Shape.plus, Shape.scale]
      congr 1 <;> ring
    change m * d + Module.finrank E (capSpace I (baseline.scale (3 * m))) ≤
      Module.finrank E (capSpace I ((baseline.scale (3 * m)).plus ((h.scale 3).scale m))) at hr
    rw [hshape] at hr
    change m * d +
        Module.finrank (SectionField a) (capSpace (extendCurve C a) (baseline.scale (3 * m))) ≤
      Module.finrank (SectionField a) (capSpace (extendCurve C a) (p.scale (3 * m))) at hr
    rw [finrank_capSpace_map (E := SectionField a) C (baseline.scale (3 * m)),
      finrank_capSpace_map (E := SectionField a) C (p.scale (3 * m)),
      ← cap_hilbertFunction C baseline hbase, ← cap_hilbertFunction C p hp] at hr
    change m * d + affineHilbertFunction B (3 * m) ≤ affineHilbertFunction P (3 * m) at hr
    have he : (m : ℚ) * d + basePoly.eval ((3 * m : ℕ) : ℚ) ≤ sumPoly.eval ((3 * m : ℕ) : ℚ) := by
      rw [hNB (3 * m) (by omega), hNP (3 * m) (by omega)]
      exact_mod_cast hr
    rw [eval_linear hdB, eval_linear hdP] at he
    push_cast at he
    simp [lower, upper]
    linarith
  have hslope := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (linear_degree _ _) (linear_degree _ _) hgrowth
  have hc : (d : ℚ) + 3 * basePoly.coeff 1 ≤ 3 * sumPoly.coeff 1 := by
    simpa [lower, upper, Polynomial.coeff_add, Polynomial.coeff_mul_X] using hslope
  change (d : ℚ) ≤ 6 * ((sumPoly.coeff 1 - basePoly.coeff 1) / (2 : ℚ) ^ 1)
  norm_num
  linarith

end

end K1_13_7_2_3_1_3
end PackSource_K1_13_7_2_3_1_3Proof

section PackSource_K1_11Annihilator
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace K1_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

private theorem scalar_total_weight_le (G : MvPolynomial (Fin 4) F) (a b : ℕ)
    (hA : G.weightedTotalDegree scalarWeightYS ≤ a)
    (hB : G.weightedTotalDegree scalarWeightT ≤ b) :
    G.weightedTotalDegree scalarWeightTotal ≤ a + b := by
  apply Finset.sup_le
  intro e he
  have ha := (le_weightedTotalDegree scalarWeightYS he).trans hA
  have hb := (le_weightedTotalDegree scalarWeightT he).trans hB
  simp [scalarWeightYS,scalarWeightT,scalarWeightTotal,Finsupp.weight_apply,
    Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul] at ha hb ⊢
  omega

open K1

private theorem bank_cancel (b : Bank) : 1 + (b.dT - 1) = b.dT := by cases b <;> rfl

theorem exists_annihilator {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {b : Bank} {H : ℕ} (C : ContactInput u P b H) (h : ℕ)
    (hmin : 24587 ≤ h) (hmax : h ≤ 32718) (hH : H + deleted.card = h)
    {Γ : Finset K} (F : Marks u deleted Γ) : Nonempty (Annihilator F b) := by
  obtain ⟨G, hG, hgAnn⟩ := exists_two_decoder_source C h hmin hmax hH
  let Q := scalarEliminant 5 G.val C.numerator C.denominator
  have hne : Q ≠ 0 := scalarEliminant_ne_zero 720983 131071 5 b.s b.t
    G.val C.L G.property hG C.numerator C.denominator C.denominator_ne C.linear C.primitive
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients 720983 131071 5 b.s b.t G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 := by
    simpa [Q, scalarEliminant] using
      clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val)
        C.numerator C.denominator (by simpa using hY) C.numerator_Y C.denominator_Y (by omega)
  have hs : Q.weightedTotalDegree scalarWeightYS ≤ b.a := by
    simpa [Q, scalarEliminant, Bank.a] using
      clearedEval_weight_bound scalarWeightYS 5 b.s 0 b.dS b.dS (polynomialView G.val)
        C.numerator C.denominator (by simpa using hS) C.numerator_S C.denominator_S (by omega)
  have ht : Q.weightedTotalDegree scalarWeightT ≤ b.b := by
    simpa [Q, scalarEliminant, Bank.b] using
      clearedEval_weight_bound scalarWeightT 5 b.t 1 b.dT (b.dT-1) (polynomialView G.val)
        C.numerator C.denominator (by simpa using hT) C.numerator_T C.denominator_T (bank_cancel b).ge
  refine ⟨⟨Q, hne, hy, hs, ht, scalar_total_weight_le Q b.a b.b hs ht, ?_⟩⟩
  intro γ hγ
  let M := F.mark γ hγ
  let S := indexedSupport P M.support
  have hS : 180246 ≤ S.card := by
    rw [indexedSupport_card P M.support (F.survives γ hγ)]
    exact M.agreement
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 :=
    Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hrel := relation_annihilates C (by omega) _ _ hd hd' γ (γ ^ p) S hS hcorrect
  exact scalarEliminant_annihilates 720983 131071 5 b.s b.t G.val C.L G.property
    C.numerator C.denominator C.linear _ _ γ (γ^p) hrel
    (hgAnn _ _ hd hd' γ (γ^p) S hS hcorrect)

end
end K1_11
end PackSource_K1_11Annihilator

section PackSource_K1_13_5_2Proof
set_option autoImplicit true
namespace K1_13_5_2

noncomputable section
open K1_13 K1_13_5 MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial

/-- Separate the first jet from the value, keeping the abscissa in the coefficient ring. -/
private def firstView : Row 2 ≃ₐ[Geom[X]] (Row 1)[X] :=
  (renameEquiv Geom[X] finSuccEquivLast).trans (optionEquivLeft Geom[X] (Fin 1))

private abbrev valueView : Row 1 ≃ₐ[Geom[X]] Geom[X][X] :=
  uniqueAlgEquiv Geom[X] (Fin 1)

private theorem firstView_degree (f : Row 2) : (firstView f).natDegree = f.degreeOf 1 := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast f)).natDegree = f.degreeOf 1
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 1)

private theorem firstView_pderiv (f : Row 2) :
    firstView (pderiv 1 f) = (firstView f).derivative := by
  change optionEquivLeft _ _ (rename finSuccEquivLast (pderiv 1 f)) =
    (optionEquivLeft _ _ (rename finSuccEquivLast f)).derivative
  rw [← pderiv_rename finSuccEquivLast.injective,
    show finSuccEquivLast (1 : Fin 2) = none from finSuccEquivLast_last,
    optionEquivLeft_pderiv_none]

private theorem valueView_eval (g : Row 1) (S : Geom[X]) :
    (valueView g).eval S = MvPolynomial.eval (jet S) g := by
  have h := eval₂_uniqueAlgEquiv (f := g) (φ := RingHom.id Geom[X]) (a := jet S)
  have hzero : jet S (default : Fin 1) = S := by
    change Polynomial.hasseDeriv 0 S = S
    simp
  simpa only [Polynomial.eval₂_id, MvPolynomial.eval₂_id, hzero] using h

private theorem firstView_eval (f : Row 2) (S : Geom[X]) :
    ((firstView f).map (MvPolynomial.eval (jet S))).eval (jet S (1 : Fin 2)) =
      atJet f S := by
  rw [firstView, AlgEquiv.trans_apply, renameEquiv_apply, ← optionEquivLeft_elim_eval,
    eval_rename, atJet]
  apply congrArg (fun x : Fin 2 → Geom[X] => MvPolynomial.eval x f)
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
    k + (valueView ((firstView f).coeff k)).natDegree ≤ f.totalDegree := by
  change k + (valueView ((optionEquivLeft _ _ (rename finSuccEquivLast f)).coeff k)).natDegree ≤ _
  have hdeg : (rename finSuccEquivLast f).totalDegree = f.totalDegree :=
    totalDegree_renameEquiv finSuccEquivLast f
  have hh := totalDegree_coeff_optionEquivLeft_add_le Geom[X] (Fin 1)
    (rename finSuccEquivLast f) k
    (by rw [hdeg]; exact hk)
  rw [hdeg] at hh
  exact (Nat.add_le_add_left (valueView_degree_le _) _).trans (by simpa [add_comm] using hh)

private def eliminant (f : Row 2) : Geom[X][X] :=
  let A := firstView f
  if 0 < A.natDegree then
    valueView (A.resultant A.derivative A.natDegree (A.natDegree - 1))
  else valueView (A.coeff 0)

set_option maxHeartbeats 600000 in
/-- Each factor contributes either its order-zero equation or its first-jet resultant. -/
private theorem eliminant_spec (f : Row 2) (hf : Irreducible f) (hb : f.totalDegree ≤ 5064) :
    eliminant f ≠ 0 ∧ (eliminant f).natDegree ≤ f.totalDegree * (5064 - 1) ∧
      ∀ S : Geom[X], atJet f S = 0 → (eliminant f).eval S = 0 ∨
        (0 < f.degreeOf 1 ∧ RegularAt 1 f S) := by
  let A := firstView f
  let c := A.natDegree
  let b := f.totalDegree
  have hcb : c ≤ b := by
    change (firstView f).natDegree ≤ f.totalDegree
    exact (firstView_degree f).le.trans (f.degreeOf_le_totalDegree 1)
  have hAb : A ≠ 0 := (map_ne_zero_iff _ firstView.injective).mpr hf.ne_zero
  by_cases hc : 0 < c
  · let R := A.resultant A.derivative c (c - 1)
    have hform : eliminant f = valueView R := ite_eq_left hc
    have hcast : (c : Row 1) ≠ 0 := by
      have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
      have : CharP Geom[X] K1.p :=
        charP_of_injective_ringHom (Polynomial.C_injective (R := Geom)) K1.p
      have : CharP (Row 1) K1.p :=
        charP_of_injective_ringHom (MvPolynomial.C_injective (σ := Fin 1) (R := Geom[X])) K1.p
      intro h
      have hp : K1.p ∣ c := (CharP.cast_eq_zero_iff (Row 1) K1.p c).mp h
      exact (not_le_of_gt (hcb.trans_lt (hb.trans_lt (by decide : 5064 < K1.p))))
        (Nat.le_of_dvd hc hp)
    have hder : A.derivative ≠ 0 := by
      intro h
      have hz := congrArg (fun P : (Row 1)[X] => P.coeff (c - 1)) h
      rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hc, Polynomial.coeff_zero] at hz
      have hnat : (((c - 1 : ℕ) : Row 1) + 1) = (c : Row 1) := calc
        _ = ((c - 1 + 1 : ℕ) : Row 1) := by rw [Nat.cast_add, Nat.cast_one]
        _ = _ := congrArg (fun k : ℕ => (k : Row 1)) (Nat.sub_add_cancel hc)
      rw [hnat] at hz
      change A.leadingCoeff * (c : Row 1) = 0 at hz
      exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hAb) hcast) hz
    have hR : R ≠ 0 :=
      Polynomial.resultant_derivative_ne_zero_of_irreducible A (hf.map firstView) hder
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
            rw [show A.derivative = firstView (pderiv 1 f) from (firstView_pderiv f).symm]
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
        (by simpa using Nat.mul_le_mul_left b (by decide : 1 ≤ 5064 - 1))
    · intro S hS
      left
      have h := (firstView_eval f S).trans hS
      change (A.map _).eval _ = 0 at h
      conv at h => lhs; rw [hAc]
      rw [hform, valueView_eval]
      simpa only [Polynomial.map_C, Polynomial.eval_C] using h

theorem proof : K1_13_5.c2 := by
  classical
  intro q hq
  let _ : StrongNormalizationMonoid (Row 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M := normalizedFactors q
  let A := M.toFinset
  let T := A.filter fun g => 0 < g.degreeOf 1
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 2 := fun i => (e i).val
  have hA : ∀ g ∈ A, Irreducible g := fun g hg =>
    irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
  have hdiv : (∏ g ∈ A, g) ∣ q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq.ne_zero).dvd
  have hcap : (∑ g ∈ A, g.totalDegree) ≤ 5064 := by
    have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) A id hq.ne_zero hdiv
    simp only [id_eq, weightedTotalDegree_one] at h
    exact h.trans hq.total
  have hfactor : ∀ i, f i ∈ A ∧ 0 < (f i).degreeOf 1 := fun i =>
    Finset.mem_filter.mp (e i).property
  have hfdiv : (∏ i, f i) ∣ q := by
    rw [show (∏ i, f i) = ∏ g : ↥T, id g.val from e.prod_comp Subtype.val,
      Finset.prod_coe_sort T id]
    exact (Finset.prod_dvd_prod_of_subset T A id (Finset.filter_subset _ _)).trans hdiv
  have hf : FirstFactors f := by
    refine ⟨fun i => hA _ (hfactor i).1, fun i => (hfactor i).2, ?_, ?_⟩
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) Finset.univ f hq.ne_zero hfdiv
      simp only [weightedTotalDegree_one] at h
      exact h.trans hq.total
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (fun i : Fin 2 => i.val)
        Finset.univ f hq.ne_zero hfdiv
      simp only [← K1_13_1.indexDegree_eq] at h
      exact h.trans hq.index
  have hspec (g : Row 2) (hg : g ∈ A) :=
    eliminant_spec g (hA g hg) ((Finset.single_le_sum (fun x _ => Nat.zero_le x.totalDegree) hg).trans hcap)
  let u := ∏ g ∈ A, eliminant g
  refine ⟨n, f, u, hf, Finset.prod_ne_zero_iff.mpr (fun g hg => (hspec g hg).1), ?_, ?_⟩
  · calc
      u.natDegree ≤ ∑ g ∈ A, (eliminant g).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ g ∈ A, g.totalDegree * (5064 - 1) := Finset.sum_le_sum fun g hg => (hspec g hg).2.1
      _ ≤ 5064 * (5064 - 1) := by rw [← Finset.sum_mul]; exact Nat.mul_le_mul_right _ hcap
  · intro S hS
    have hroot : MvPolynomial.eval (jet S) M.prod = 0 := by
      have hd := map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hq.ne_zero).symm.dvd
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
    · right
      let j := e.symm ⟨g, Finset.mem_filter.mpr ⟨hgA, hpos⟩⟩
      have hj : f j = g := congrArg Subtype.val (e.apply_symm_apply _)
      exact ⟨j, hj ▸ hreg⟩

end
end K1_13_5_2
end PackSource_K1_13_5_2Proof

section PackSource_K1_13_6_3_5_1Cycle
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_1

noncomputable section

open MvPolynomial K1_13_6_3 K1_13_6_3_5 K1_13_6_3_6

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type} [Field k]

private theorem mem_colon {I : Ideal (MvPolynomial σ k)} {g p : MvPolynomial σ k} :
    p ∈ I.colon {g} ↔ p * g ∈ I :=
  Submodule.mem_colon_singleton

private theorem colon_homogeneous {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {g : MvPolynomial σ k} {b : ℕ}
    (hg : g.IsHomogeneous b) :
    (I.colon {g}).IsHomogeneous (homogeneousSubmodule σ k) := by
  intro i p hp
  rw [decompose_apply]
  rw [mem_colon] at hp ⊢
  have h := homogeneousComponent_mem_of_mem hI hp (i + b)
  simpa only [component_mul hg, ite_eq_left (by omega : b ≤ i + b),
    show i + b - b = i by omega] using h

/-- A maximal annihilator among homogeneous elements of a nonzero graded
quotient is prime. -/
private theorem exists_homogeneous_prime_colon [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (hproper : I ≠ ⊤) :
    ∃ (g : MvPolynomial σ k) (b : ℕ), g.IsHomogeneous b ∧ g ∉ I ∧ (I.colon {g}).IsPrime := by
  let good (g : MvPolynomial σ k) := (∃ b, g.IsHomogeneous b) ∧ g ∉ I
  have he : ∃ g, good g := ⟨1, ⟨0, isHomogeneous_one σ k⟩, I.ne_top_iff_one.mp hproper⟩
  obtain ⟨g, hmax⟩ := exists_maximalFor_of_wellFoundedGT good (fun g => I.colon {g}) he
  obtain ⟨⟨b, hgb⟩, hg⟩ := hmax.prop
  refine ⟨g, b, hgb, hg, (colon_homogeneous hI hgb).isPrime_of_homogeneous_mem_or_mem ?_ ?_⟩
  · intro ht
    apply hg
    have h : (1 : MvPolynomial σ k) ∈ I.colon {g} := by rw [ht]; exact Submodule.mem_top
    simpa only [mem_colon, one_mul] using h
  · intro x y _ hy hxy
    by_cases h : y ∈ I.colon {g}
    · exact Or.inr h
    · left
      rw [mem_colon] at h
      obtain ⟨d, hyd⟩ := hy
      have hygood : good (y * g) := ⟨⟨d + b, (show y.IsHomogeneous d from hyd).mul hgb⟩, h⟩
      have hle : I.colon {g} ≤ I.colon {y * g} := by
        intro p hp
        rw [mem_colon, show p * (y * g) = y * (p * g) by ac_rfl]
        exact I.mul_mem_left _ (mem_colon.mp hp)
      apply hmax.2 hygood hle
      exact mem_colon.mpr (by simpa only [mul_assoc] using mem_colon.mp hxy)

private def localLength (J P : Ideal (MvPolynomial σ k)) (hp : P.IsPrime) : ℕ∞ :=
  letI := hp
  let L := Localization.AtPrime P
  Module.length L (L ⧸ J.map (algebraMap (MvPolynomial σ k) L))

private theorem colon_map_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (T : Submonoid R) [IsLocalization T S] (I : Ideal R) (g : R) :
    (I.colon {g}).map (algebraMap R S) = (I.map (algebraMap R S)).colon {algebraMap R S g} := by
  ext z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq T z
  rw [Submodule.mem_colon_singleton, smul_eq_mul,
    mul_comm _ (algebraMap R S g), IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc, mul_comm g]

private theorem length_cyclic (I P : Ideal (MvPolynomial σ k)) (hp : P.IsPrime)
    (g : MvPolynomial σ k) :
    localLength I P hp =
      localLength (I.colon {g}) P hp + localLength (I ⊔ Ideal.span {g}) P hp := by
  let _ : P.IsPrime := hp
  let L := Localization.AtPrime P
  let r := algebraMap (MvPolynomial σ k) L
  let J := I.map r
  let a := r g
  have h := Module.length_eq_add_of_exact (quotientMul J a)
    (Submodule.factor (le_sup_left : J ≤ J ⊔ Ideal.span {a}))
    (quotientMul_injective J a) (Submodule.factor_surjective le_sup_left)
    (quotientMul_exact J a)
  change Module.length L (L ⧸ I.map r) =
    Module.length L (L ⧸ (I.colon {g}).map r) +
      Module.length L (L ⧸ (I ⊔ Ideal.span {g}).map r)
  rw [colon_map_localization P.primeCompl, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact h

private theorem length_eq_zero_of_not_le {I P : Ideal (MvPolynomial σ k)} (hp : P.IsPrime)
    (h : ¬ I ≤ P) : localLength I P hp = 0 := by
  let _ : P.IsPrime := hp
  let L := Localization.AtPrime P
  have htop : I.map (algebraMap (MvPolynomial σ k) L) = ⊤ := by
    by_contra ht
    exact h (Set.disjoint_compl_left_iff_subset.mp
      ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl L I).mp ht))
  change Module.length L (L ⧸ I.map (algebraMap (MvPolynomial σ k) L)) = 0
  simp [htop, Module.length_eq_zero]

private theorem length_self (P : Ideal (MvPolynomial σ k)) (hp : P.IsPrime) :
    localLength P P hp = 1 := by
  let _ : P.IsPrime := hp
  let L := Localization.AtPrime P
  change Module.length L (L ⧸ P.map (algebraMap (MvPolynomial σ k) L)) = 1
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  have h : IsSimpleModule L (L ⧸ IsLocalRing.maximalIdeal L) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal L).1
  exact Module.length_eq_one _ _

private theorem dimension_lt_of_lt [Finite σ] {P Q : Ideal (MvPolynomial σ k)}
    (hP : P.IsPrime) (hlt : P < Q) (hd : dimension P = 2) : dimension Q < 2 := by
  obtain ⟨g, hgQ, hgP⟩ := SetLike.exists_of_lt hlt
  have hcut : P ⊔ Ideal.span {g} ≤ Q :=
    sup_le hlt.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgQ))
  have hb := (natDegree_affineHilbertPolynomial_le_of_le hcut).trans
    (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hP hgP (le_refl g.totalDegree)).1
  change dimension Q ≤ dimension P - 1 at hb
  omega

/-- The degree-two coefficient is additive along a graded prime filtration.
Localizing at a minimal prime counts exactly the factors with that annihilator. -/
theorem coefficient_cycle [Finite σ] (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ k)) (hd : dimension J ≤ 2)
    (hmin : ∀ P, J.IsMinimalPrime P → dimension P = 2) :
    (affineHilbertPolynomial J).coeff 2 =
      ∑ P ∈ J.minimalPrimesFinset,
        (boundaryWeight J P : ℚ) * (affineHilbertPolynomial P).coeff 2 := by
  classical
  let T := J.minimalPrimesFinset
  suffices aux : ∀ I : Ideal (MvPolynomial σ k), J ≤ I →
      I.IsHomogeneous (homogeneousSubmodule σ k) →
      (∀ P (hp : J.IsMinimalPrime P), localLength I P hp.isPrime ≠ ⊤) ∧
      (affineHilbertPolynomial I).coeff 2 =
        ∑ P ∈ T, (boundaryWeight I P : ℚ) * (affineHilbertPolynomial P).coeff 2 from
    (aux J le_rfl hJ).2
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α := Ideal (MvPolynomial σ k))) with
  | h I ih =>
    intro hJI hIhom
    by_cases hI : I = ⊤
    · subst I
      have hz (P : Ideal (MvPolynomial σ k)) (hp : P.IsPrime) : localLength ⊤ P hp = 0 :=
        length_eq_zero_of_not_le hp (by simpa using hp.ne_top)
      refine ⟨fun P hp => by simp [hz P hp.isPrime], ?_⟩
      simp only [affineHilbertPolynomial_top, Polynomial.coeff_zero]
      symm
      apply Finset.sum_eq_zero
      intro P hP
      have hp := (Ideal.mem_minimalPrimesFinset.mp hP).isPrime
      have he : (boundaryWeight ⊤ P : ℕ) = (localLength ⊤ P hp).toNat := by
        simp only [boundaryWeight, dite_eq_left hp, localLength]
      simp [he, hz P hp]
    obtain ⟨g, b, hgb, hg, hprime⟩ := exists_homogeneous_prime_colon I hIhom hI
    let A : Ideal (MvPolynomial σ k) := I.colon {g}
    let B : Ideal (MvPolynomial σ k) := I ⊔ Ideal.span {g}
    have hIA : I ≤ A := Ideal.le_colon
    have hIB : I < B := lt_of_le_not_ge le_sup_left
      (fun h => hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    have hspan : (Ideal.span {g}).IsHomogeneous (homogeneousSubmodule σ k) := by
      apply Ideal.homogeneous_span
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      exact ⟨b, hgb⟩
    obtain ⟨hfin, hbudget⟩ := ih B hIB (hJI.trans hIB.le) (hIhom.sup hspan)
    have hstep (P : Ideal (MvPolynomial σ k)) (hp : J.IsMinimalPrime P) :
        localLength I P hp.isPrime =
          localLength A P hp.isPrime + localLength B P hp.isPrime :=
      length_cyclic I P hp.isPrime g
    have hterm (P : Ideal (MvPolynomial σ k)) (hp : J.IsMinimalPrime P) :
        localLength A P hp.isPrime = if P = A then 1 else 0 := by
      split_ifs with h
      · subst P
        exact length_self A hp.isPrime
      · exact length_eq_zero_of_not_le hp.isPrime
          (fun hAP => h (le_antisymm (hp.2 ⟨hprime, hJI.trans hIA⟩ hAP) hAP))
    have hfinite (P : Ideal (MvPolynomial σ k)) (hp : J.IsMinimalPrime P) :
        localLength A P hp.isPrime ≠ ⊤ := by rw [hterm P hp]; split_ifs <;> simp
    have hweight (P : Ideal (MvPolynomial σ k)) (hP : P ∈ T) :
        (boundaryWeight I P : ℚ) = (boundaryWeight B P : ℚ) + (if P = A then 1 else 0) := by
      have hp := Ideal.mem_minimalPrimesFinset.mp hP
      have hw (L : Ideal (MvPolynomial σ k)) : boundaryWeight L P = (localLength L P hp.isPrime).toNat := by
        simp only [boundaryWeight, dite_eq_left hp.isPrime, localLength]
      rw [hw, hw, hstep P hp, ENat.toNat_add (hfinite P hp) (hfin P hp), hterm P hp, Nat.cast_add]
      split_ifs <;> simp [add_comm]
    have hdim := (natDegree_affineHilbertPolynomial_le_of_le hJI).trans hd
    refine ⟨fun P hp => by
      rw [hstep P hp]
      exact WithTop.add_ne_top.mpr ⟨hfinite P hp, hfin P hp⟩, ?_⟩
    have hA : (affineHilbertPolynomial A).coeff 2 =
        if A ∈ T then (affineHilbertPolynomial A).coeff 2 else 0 := by
      split_ifs with hAT
      · rfl
      · let _ : A.IsPrime := hprime
        obtain ⟨P, hp, hPA⟩ := Ideal.exists_minimalPrimes_le (hJI.trans hIA : J ≤ A)
        have hne : P ≠ A := fun he => hAT (Ideal.mem_minimalPrimesFinset.mpr (he ▸ hp))
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (dimension_lt_of_lt hp.isPrime (lt_of_le_of_ne hPA hne) (hmin P hp))
    calc
      _ = (affineHilbertPolynomial B).coeff 2 + (affineHilbertPolynomial A).coeff 2 :=
        (coeff_cyclic hIhom hgb hdim).symm
      _ = (∑ P ∈ T, (boundaryWeight B P : ℚ) * (affineHilbertPolynomial P).coeff 2) +
          (if A ∈ T then (affineHilbertPolynomial A).coeff 2 else 0) := congrArg₂ (· + ·) hbudget hA
      _ = _ := by
        rw [← Finset.sum_ite_eq' T A (fun P => (affineHilbertPolynomial P).coeff 2),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [hweight P hP, add_mul, ite_mul, one_mul, zero_mul]

theorem affineDegree_cycle [Finite σ] (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ k)) (hd : dimension J = 2)
    (hmin : ∀ P, J.IsMinimalPrime P → dimension P = 2) :
    affineDegree J =
      ∑ P ∈ J.minimalPrimesFinset, (boundaryWeight J P : ℚ) * affineDegree P := by
  classical
  have hdegree (P : Ideal (MvPolynomial σ k)) (hP : dimension P = 2) :
      affineDegree P = 2 * (affineHilbertPolynomial P).coeff 2 := by
    change (affineHilbertPolynomial P).natDegree = 2 at hP
    simp only [affineDegree, Polynomial.leadingCoeff, hP]
    norm_num
  rw [hdegree J hd, coefficient_cycle J hJ hd.le hmin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [hdegree P (hmin P (Ideal.mem_minimalPrimesFinset.mp hP))]
  ac_rfl

end

end K1_13_6_3_5_1
end PackSource_K1_13_6_3_5_1Cycle

section PackSource_K1_13_6_3_5_1Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_1

noncomputable section

open MvPolynomial K1_13_6_3 K1_13_6_3_5

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In the closure cone, each exact degree piece is the bounded-degree
piece of the affine chart. Taking a backward difference removes the sum. -/
def c1 : Prop :=
  ∀ (k σ : Type) [Field k] [Finite σ] (A : Ideal (MvPolynomial σ k)),
    Polynomial.backwardDifference 1 (affineHilbertPolynomial (closureIdeal A)) =
      affineHilbertPolynomial A

/-- The scheme cut by the affine coordinate is defined by the top parts
of all affine equations. Its pullback includes the zeroed coordinate. -/
def c2 : Prop :=
  ∀ (k σ : Type) [Field k] [Finite σ] (A : Ideal (MvPolynomial σ k)),
    (boundaryIdeal A).comap (atInfinity (k := k) (σ := σ)) =
      closureIdeal A ⊔ Ideal.span {MvPolynomial.X none}

theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_3_5.c1 := by
  classical
  intro k σ _ _ A hA hdim
  change (affineHilbertPolynomial A).natDegree = 2 at hdim
  let C := closureIdeal A
  let B := boundaryIdeal A
  let φ : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k := atInfinity
  let w : MvPolynomial (Option σ) k := MvPolynomial.X none
  let _ : C.IsPrime := closureIdeal_prime A hA
  have hw : w ∉ C := not_mem_closureIdeal A hA
  have hcut : B.comap φ = C ⊔ Ideal.span {w} := h2 k σ A
  have hdiff : Polynomial.backwardDifference 1 (affineHilbertPolynomial C) =
      affineHilbertPolynomial A := h1 k σ A
  have hle := Polynomial.natDegree_backwardDifference_le (1 : ℚ) (affineHilbertPolynomial C)
  rw [hdiff, hdim] at hle
  have hback := Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (P := affineHilbertPolynomial C) (one_ne_zero : (1 : ℚ) ≠ 0) (by omega)
  have hCdim : (affineHilbertPolynomial C).natDegree = 3 := by
    have h := hback.1
    rw [hdiff, hdim] at h
    omega
  have hcol : C.colon {w} = C := by
    refine le_antisymm ?_ Ideal.le_colon
    intro p hp
    exact (‹C.IsPrime›.mem_or_mem (Submodule.mem_colon_singleton.mp hp)).resolve_right hw
  have hBpoly : affineHilbertPolynomial B = affineHilbertPolynomial A := by
    have hx := hilbertPolynomial_cyclic (closureIdeal_homogeneous A) (isHomogeneous_X k none)
    change affineHilbertPolynomial (C ⊔ Ideal.span {w}) +
      Polynomial.taylor (-(1 : ℚ)) (affineHilbertPolynomial (C.colon {w})) =
      affineHilbertPolynomial C at hx
    rw [hcol, ← hcut, hilbertPolynomial_comap_atInfinity] at hx
    rw [← hdiff, Polynomial.backwardDifference]
    exact eq_sub_of_add_eq hx
  have hBhom := boundaryIdeal_homogeneous A
  have hmin (P) (hP : B.IsMinimalPrime P) : dimension P = 2 := by
    have hp := Ideal.minimalPrimes_comap_of_surjective
      (f := φ.toRingHom) (show Function.Surjective φ from atInfinity_surjective) hP
    change P.comap φ ∈ (B.comap φ).minimalPrimes at hp
    rw [hcut] at hp
    have hx := principalCut_natDegree_affineHilbertPolynomial_add_one hw hp
    have hPpoly : affineHilbertPolynomial (P.comap φ) = affineHilbertPolynomial P :=
      hilbertPolynomial_comap_atInfinity P
    rw [hPpoly, hCdim] at hx
    change (affineHilbertPolynomial P).natDegree = 2
    omega
  refine ⟨fun P hp => ⟨hmin P hp, minimalPrime_homogeneous hBhom hp⟩, ?_⟩
  have hBdim : dimension B = 2 := by
    change (affineHilbertPolynomial B).natDegree = 2
    rwa [hBpoly]
  have hdeg : affineDegree A = affineDegree B := by simp [affineDegree, hBpoly]
  exact hdeg.trans (affineDegree_cycle B hBhom hBdim hmin)

end

end K1_13_6_3_5_1
end PackSource_K1_13_6_3_5_1Split

section PackSource_K1_13_6_3_5_1_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_1_2

noncomputable section

open MvPolynomial K1_13_6_3_5 K1_13_6_3_5_1

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

private def atOne : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => i.elim 1 MvPolynomial.X

private theorem atOne_eq_eval (p : MvPolynomial (Option σ) k) :
    atOne p = (optionEquivLeft k σ p).eval 1 := by
  let e : Polynomial (MvPolynomial σ k) →ₐ[k] MvPolynomial σ k :=
    (Polynomial.aeval 1).restrictScalars k
  have h : (atOne (k := k) (σ := σ)) = e.comp (optionEquivLeft k σ).toAlgHom := by
    ext i
    cases i <;> simp [e, atOne, optionEquivLeft_X_none, optionEquivLeft_X_some]
  exact DFunLike.congr_fun h p

private theorem atOne_monomial (d : Option σ →₀ ℕ) (r : k) :
    atOne (monomial d r) = monomial d.some r := by
  rw [atOne_eq_eval, optionEquivLeft_monomial, Polynomial.eval_monomial, one_pow, mul_one]

private theorem atInfinity_monomial (d : Option σ →₀ ℕ) (r : k) :
    atInfinity (monomial d r) = if d none = 0 then monomial d.some r else 0 := by
  rw [atInfinity_eq_coeff_zero, optionEquivLeft_monomial, Polynomial.coeff_monomial]

private theorem degree_option (d : Option σ →₀ ℕ) :
    d.degree = d none + d.some.degree := by
  simp only [Finsupp.degree_apply]
  exact Finsupp.sum_option_index d (fun _ e => e) (fun _ => rfl) (fun _ _ _ => rfl)

/-- For a homogeneous equation, only the terms of unchanged degree survive
setting the affine coordinate to zero. -/
private theorem specialize_homogeneous {p : MvPolynomial (Option σ) k} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (atOne p).totalDegree ≤ n ∧ atInfinity p = homogeneousComponent n (atOne p) := by
  classical
  have hdeg (d : Option σ →₀ ℕ) (hd : d ∈ p.support) : d none + d.some.degree = n := by
    rw [← degree_option]
    exact (hp.degree_eq_sum_deg_support hd).symm
  have h₁ : atOne p = ∑ d ∈ p.support, monomial d.some (p.coeff d) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, atOne_monomial]
  have h₀ : atInfinity p =
      ∑ d ∈ p.support, if d none = 0 then monomial d.some (p.coeff d) else 0 := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, atInfinity_monomial]
  constructor
  · rw [h₁]
    apply totalDegree_finsetSum_le
    intro d hd
    exact (isHomogeneous_monomial (p.coeff d) (n := d.some.degree) rfl).totalDegree_le.trans
      (by have := hdeg d hd; omega)
  · rw [h₀, h₁, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl)]
    have he : d none = 0 ↔ n = d.some.degree := by
      have := hdeg d hd
      omega
    simp only [he]

private theorem mem_closure_iff_of_homogeneous (A : Ideal (MvPolynomial σ k))
    {p : MvPolynomial (Option σ) k} {n : ℕ} (hp : p.IsHomogeneous n) :
    p ∈ closureIdeal A ↔ atOne p ∈ A := by
  change closureMap A p = 0 ↔ _
  have hc (m : ℕ) : (closureMap A p).coeff m =
      Ideal.Quotient.mk A (atOne (if m = n then p else 0)) := by
    rw [coeff_closureMap, homogeneousComponent_of_mem hp]
    rfl
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [h] using (hc n).symm
  · intro h
    ext m
    rw [hc, Polynomial.coeff_zero]
    by_cases hm : m = n
    · simpa [hm] using Ideal.Quotient.eq_zero_iff_mem.mpr h
    · simp [hm]

private theorem exists_homogeneous_lift (f : MvPolynomial σ k) {n : ℕ} (hf : f.totalDegree ≤ n) :
    ∃ p : MvPolynomial (Option σ) k, p.IsHomogeneous n ∧ atOne p = f := by
  classical
  let term (d : σ →₀ ℕ) := monomial (d.optionElim (n - d.degree)) (f.coeff d)
  refine ⟨∑ d ∈ f.support, term d, IsHomogeneous.sum _ _ _ ?_, ?_⟩
  · intro d hd
    apply isHomogeneous_monomial
    have hle : d.degree ≤ n := (le_totalDegree hd).trans hf
    simp only [degree_option, Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
    exact Nat.sub_add_cancel hle
  · simp only [map_sum, term, atOne_monomial, Finsupp.some_optionElim]
    exact f.support_sum_monomial_coeff

private theorem map_closure (A : Ideal (MvPolynomial σ k)) :
    (closureIdeal A).map (atInfinity (k := k) (σ := σ)) = boundaryIdeal A := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change atInfinity p ∈ boundaryIdeal A
    rw [← sum_homogeneousComponent p, map_sum]
    apply Ideal.sum_mem
    intro n _
    have hC := homogeneousComponent_mem_of_mem (closureIdeal_homogeneous A) hp n
    have hhom := homogeneousComponent_isHomogeneous n p
    have ha := (mem_closure_iff_of_homogeneous A hhom).mp hC
    obtain ⟨hle, hs⟩ := specialize_homogeneous hhom
    rw [hs]
    rcases hle.eq_or_lt with he | hlt
    · exact Ideal.subset_span ⟨_, ha, by rw [he]⟩
    · rw [homogeneousComponent_eq_zero _ _ hlt]
      exact (boundaryIdeal A).zero_mem
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨p, hh, h₁⟩ := exists_homogeneous_lift f (n := f.totalDegree) le_rfl
    have hp := (mem_closure_iff_of_homogeneous A hh).mpr (h₁.symm ▸ hf)
    have hmap := Ideal.mem_map_of_mem (atInfinity (k := k) (σ := σ)) hp
    rwa [(specialize_homogeneous hh).2, h₁] at hmap

private theorem ker_atInfinity :
    RingHom.ker (atInfinity (k := k) (σ := σ)).toRingHom =
      Ideal.span {MvPolynomial.X none} := by
  ext p
  rw [Ideal.mem_span_singleton]
  change atInfinity p = 0 ↔ MvPolynomial.X none ∣ p
  rw [atInfinity_eq_coeff_zero, ← Polynomial.X_dvd_iff]
  simpa only [optionEquivLeft_X_none] using
    (map_dvd_iff (optionEquivLeft k σ) (a := MvPolynomial.X none) (b := p))

theorem proof : K1_13_6_3_5_1.c2 := by
  intro k σ _ _ A
  rw [← map_closure A, Ideal.comap_map_of_surjective' _ atInfinity_surjective]
  exact congrArg (fun I => closureIdeal A ⊔ I) ker_atInfinity

end

end K1_13_6_3_5_1_2
end PackSource_K1_13_6_3_5_1_2Proof

section PackSource_K1_13_6_3_5_1_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_1_1

noncomputable section

open MvPolynomial K1_13_6_3_5_1

variable {k σ : Type} [Field k]

/-- Dehomogenization at the affine coordinate one. -/
private def specialize : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => i.elim 1 MvPolynomial.X

private theorem specialize_rename (p : MvPolynomial σ k) :
    specialize (rename some p) = p := by
  have h : (specialize (k := k) (σ := σ)).comp (rename some) = AlgHom.id k _ := by
    ext i
    simp [specialize]
  exact DFunLike.congr_fun h p

private theorem totalDegree_specialize_le (p : MvPolynomial (Option σ) k) :
    (specialize p).totalDegree ≤ p.totalDegree := by
  let e := (Polynomial.aeval (R := MvPolynomial σ k) (1 : MvPolynomial σ k)).restrictScalars k
  have he : (specialize (k := k) (σ := σ)) = e.comp (optionEquivLeft k σ).toAlgHom := by
    ext i
    cases i <;> simp [e, specialize]
  rw [he]
  change (e (optionEquivLeft k σ p)).totalDegree ≤ p.totalDegree
  conv_lhs => rw [(optionEquivLeft k σ p).as_sum_support]
  rw [map_sum, ← mem_restrictTotalDegree]
  apply Submodule.sum_mem
  intro i _
  rw [mem_restrictTotalDegree]
  have h : e (Polynomial.monomial i ((optionEquivLeft k σ p).coeff i)) =
      (optionEquivLeft k σ p).coeff i := by
    change Polynomial.aeval (R := MvPolynomial σ k) (1 : MvPolynomial σ k)
      (Polynomial.monomial i _) = _
    rw [Polynomial.coe_aeval_eq_eval, Polynomial.eval_monomial, one_pow, mul_one]
  rw [h]
  exact totalDegree_coeff_optionEquivLeft_le k σ p i

/-- Pad each monomial with enough powers of the affine coordinate to give it degree `n`. -/
private theorem exists_homogeneous_lift {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.totalDegree ≤ n) :
    ∃ q : MvPolynomial (Option σ) k, q.IsHomogeneous n ∧ specialize q = p := by
  let h (d : σ →₀ ℕ) : MvPolynomial (Option σ) k :=
    rename some (monomial d (p.coeff d)) * MvPolynomial.X none ^ (n - d.degree)
  refine ⟨∑ d ∈ p.support, h d, ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro d hd
    have hd' : d.degree ≤ n := (le_totalDegree hd).trans hp
    have hh : (h d).IsHomogeneous (d.degree + (n - d.degree)) :=
      ((isHomogeneous_monomial (p.coeff d) rfl).rename_isHomogeneous (f := some)).mul
        (isHomogeneous_X_pow none (n - d.degree))
    simpa only [Nat.add_sub_of_le hd'] using hh
  · have hw : specialize (MvPolynomial.X none : MvPolynomial (Option σ) k) = 1 := by
      simp [specialize]
    rw [map_sum]
    calc
      _ = ∑ d ∈ p.support, monomial d (p.coeff d) := by simp [h, specialize_rename, hw]
      _ = p := p.as_sum.symm

private theorem totalDegree_sub_component_le {τ : Type} {p : MvPolynomial τ k} {n : ℕ}
    (hp : p.totalDegree ≤ n + 1) :
    (p - homogeneousComponent (n + 1) p).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro d hd
  change d.degree ≤ n
  rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hd
  have hne : d.degree ≠ n + 1 := by
    intro he
    simp [he] at hd
  simp only [ite_eq_right hne, sub_zero] at hd
  have hle : d.degree ≤ n + 1 :=
    (le_totalDegree (MvPolynomial.mem_support_iff.mpr hd)).trans hp
  exact Nat.le_of_lt_succ (lt_of_le_of_ne hle hne)

private def coneEmbedding (A : Ideal (MvPolynomial σ k)) :
    (MvPolynomial (Option σ) k ⧸ closureIdeal A) →ₐ[k] Polynomial (MvPolynomial σ k ⧸ A) :=
  Ideal.Quotient.liftₐ (closureIdeal A) (closureMap A)
    (fun _ hp => RingHom.mem_ker.mp hp)

private theorem coneEmbedding_mk (A : Ideal (MvPolynomial σ k))
    (p : MvPolynomial (Option σ) k) :
    coneEmbedding A (Ideal.Quotient.mk (closureIdeal A) p) = closureMap A p := rfl

/-- The coefficient of the top power of the cone parameter in a bounded-degree class. -/
private def topCoefficient (A : Ideal (MvPolynomial σ k)) (n : ℕ) :
    quotientDegreeLE (closureIdeal A) n →ₗ[k] quotientDegreeLE A n :=
  let f := ((Polynomial.lcoeff (MvPolynomial σ k ⧸ A) n).restrictScalars k).comp
    (coneEmbedding A).toLinearMap
  (f.domRestrict _).codRestrict _ fun x => by
    obtain ⟨p, _, hpx⟩ := mem_quotientDegreeLE.mp x.property
    change (coneEmbedding A x.val).coeff n ∈ quotientDegreeLE A n
    rw [← hpx, coneEmbedding_mk, coeff_closureMap]
    exact mk_mem_quotientDegreeLE (p := specialize (homogeneousComponent n p))
      ((totalDegree_specialize_le _).trans (homogeneousComponent_isHomogeneous n p).totalDegree_le)

private theorem topCoefficient_val (A : Ideal (MvPolynomial σ k)) (n : ℕ)
    (x : quotientDegreeLE (closureIdeal A) n) (p : MvPolynomial (Option σ) k)
    (hp : Ideal.Quotient.mk (closureIdeal A) p = x.val) :
    (topCoefficient A n x).val = Ideal.Quotient.mk A (specialize (homogeneousComponent n p)) := by
  change (coneEmbedding A x.val).coeff n = _
  rw [← hp, coneEmbedding_mk, coeff_closureMap]
  rfl

private theorem topCoefficient_surjective (A : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Function.Surjective (topCoefficient A n) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
  obtain ⟨q, hq, hqp⟩ := exists_homogeneous_lift hp
  refine ⟨⟨Ideal.Quotient.mk _ q, mk_mem_quotientDegreeLE hq.totalDegree_le⟩, Subtype.ext ?_⟩
  rw [topCoefficient_val A n _ q rfl, homogeneousComponent_eq_self hq, hqp, hpy]

/-- A cone class with zero top coefficient has a representative one degree lower. -/
private theorem ker_topCoefficient (A : Ideal (MvPolynomial σ k)) (n : ℕ) :
    LinearMap.ker (topCoefficient A (n + 1)) =
      (quotientDegreeLE (closureIdeal A) n).comap
        (quotientDegreeLE (closureIdeal A) (n + 1)).subtype := by
  ext x
  rw [LinearMap.mem_ker]
  change topCoefficient A (n + 1) x = 0 ↔ x.val ∈ quotientDegreeLE (closureIdeal A) n
  constructor
  · intro hz
    obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
    have hzero : Ideal.Quotient.mk A (specialize (homogeneousComponent (n + 1) p)) = 0 :=
      (topCoefficient_val A (n + 1) x p hpx).symm.trans (congrArg Subtype.val hz)
    have hm : homogeneousComponent (n + 1) p ∈ closureIdeal A := by
      change closureMap A (homogeneousComponent (n + 1) p) = 0
      ext i
      rw [Polynomial.coeff_zero, coeff_closureMap,
        homogeneousComponent_of_mem (homogeneousComponent_mem (n + 1) p)]
      by_cases hi : i = n + 1
      · rw [ite_eq_left hi]
        exact hzero
      · simp [hi]
    refine mem_quotientDegreeLE.mpr ⟨p - homogeneousComponent (n + 1) p,
      totalDegree_sub_component_le hp, ?_⟩
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hm, sub_zero, hpx]
  · intro hx
    obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp hx
    apply Subtype.ext
    rw [topCoefficient_val A (n + 1) x p hpx,
      homogeneousComponent_eq_zero _ _ (Nat.lt_succ_of_le hp)]
    simp

private theorem hilbertFunction_succ [Finite σ] (A : Ideal (MvPolynomial σ k)) (n : ℕ) :
    affineHilbertFunction A (n + 1) + affineHilbertFunction (closureIdeal A) n =
      affineHilbertFunction (closureIdeal A) (n + 1) := by
  have h := (topCoefficient A (n + 1)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (topCoefficient_surjective A (n + 1)), finrank_top,
    ker_topCoefficient,
    (Submodule.comapSubtypeEquivOfLe (quotientDegreeLE_mono (closureIdeal A)
      (Nat.le_succ n))).finrank_eq] at h
  exact h

theorem proof : K1_13_6_3_5_1.c1 := by
  intro k σ _ _ A
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial (closureIdeal A)
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := N + 1)
  intro m hm
  have h₁ : 1 ≤ m := by omega
  have h₂ : m - 1 + 1 = m := by omega
  rw [Polynomial.eval_backwardDifference, ← Nat.cast_one, ← Nat.cast_sub h₁,
    hN m (by omega), hN (m - 1) (by omega)]
  have h := hilbertFunction_succ A (m - 1)
  rw [h₂] at h
  exact sub_eq_iff_eq_add.mpr (by exact_mod_cast h.symm)

end

end K1_13_6_3_5_1_1
end PackSource_K1_13_6_3_5_1_1Proof

section PackSource_K1_13_2_3_5Proof
set_option autoImplicit true
namespace K1_13_2_3_5

set_option maxRecDepth 5000

private theorem lengthA : rowsA.length = 168 := rfl
private theorem lengthB : rowsB.length = 168 := rfl
private theorem lengthC : rowsC.length = 168 := rfl
private theorem lengthD : rowsD.length = 168 := rfl
private theorem lengthE : rowsE.length = 168 := rfl
private theorem lengthF : rowsF.length = 164 := rfl

private def allRows : List Row :=
  rowsA ++ (rowsB ++ (rowsC ++ (rowsD ++ (rowsE ++ rowsF))))

private theorem allRows_end : 2008 + allRows.length ≤ 4013 := by
  simp only [allRows, List.length_append, lengthA, lengthB, lengthC, lengthD, lengthE, lengthF,
    Nat.reduceAdd] <;> decide

private theorem exact_total : batchScore 2008 allRows = 159735926601 := by
  simp only [allRows, batchScore_append, lengthA, lengthB, lengthC, lengthD, lengthE,
    Nat.reduceAdd, checkedA, checkedB, checkedC, checkedD, checkedE, checkedF]

theorem proof : K1_13_2_3.c5 := by
  obtain ⟨p, hp⟩ := certificate 2008 allRows allRows_end
  rw [exact_total] at hp
  exact ⟨p, hp⟩

end K1_13_2_3_5
end PackSource_K1_13_2_3_5Proof

section PackSource_K1_13_5_4_2_5_2_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_2_1

noncomputable section
open K1_13_5_4_2 MeasureTheory
open scoped BigOperators

/-- A functional exposes a label set when every maximizing label is included. -/
def Exposes {α : Type} (v : α → ExponentSpace) (S : Finset α)
    (f : ExponentSpace →ₗ[ℝ] ℝ) : Prop :=
  ∀ a, a ∈ S ↔ ∀ b, f (v b) ≤ f (v a)

/-- The nonempty exposed face labels include the full face, exposed by zero. -/
def IsFaceLabels {α : Type} (v : α → ExponentSpace) (S : Finset α) : Prop :=
  S.Nonempty ∧ ∃ f : ExponentSpace →ₗ[ℝ] ℝ, Exposes v S f

/-- The strictly increasing flags with five nonempty exposed faces. -/
def flags {α : Type} [Fintype α] (v : α → ExponentSpace) :
    Finset (Fin 5 → Finset α) := by
  classical
  exact Finset.univ.filter (fun F => StrictMono F ∧ ∀ j, IsFaceLabels v (F j))

theorem mem_flags {α : Type} [Fintype α] (v : α → ExponentSpace)
    (F : Fin 5 → Finset α) :
    F ∈ flags v ↔ StrictMono F ∧ ∀ j, IsFaceLabels v (F j) := by
  classical
  simp [flags]

/-- An average over the labels of a face, with one positive weight per label. -/
def faceCenter {α : Type} (v : α → ExponentSpace) (S : Finset α) : ExponentSpace :=
  (S.card : ℝ)⁻¹ • ∑ a ∈ S, v a

/-- The simplex in the barycentric subdivision associated to a flag. -/
def flagSimplex {α : Type} (v : α → ExponentSpace) (F : Fin 5 → Finset α) :
    Set ExponentSpace :=
  convexHull ℝ (Set.range (fun j => faceCenter v (F j)))

end
end K1_13_5_4_2_5_2_1
end PackSource_K1_13_5_4_2_5_2_1Defs

section PackSource_K1_13_5_4_2_5_2_1Volume
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_2_1

noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 K1_13_5_4_2_5 MeasureTheory Filter
open scoped BigOperators Pointwise Topology

private def coordinateVertex : Fin 5 → ExponentSpace :=
  Fin.cons 0 (fun j => Pi.single j 1)

/-- The simplex spanned by zero and the four coordinate vectors. -/
def unitSimplex : Set ExponentSpace := convexHull ℝ (Set.range coordinateVertex)

/-- The columns are the edge vectors from vertex zero. -/
def edgeMatrix (x : Fin 5 → ExponentSpace) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => x j.succ i - x 0 i

private theorem simplexImage (x : Fin 5 → ExponentSpace) :
    convexHull ℝ (Set.range x) =
      (fun y : ExponentSpace => x 0 + y) ''
        ((edgeMatrix x).toLin' '' unitSimplex) := by
  let f : ExponentSpace →ᵃ[ℝ] ExponentSpace :=
    (AffineEquiv.constVAdd ℝ ExponentSpace (x 0)).toAffineMap.comp
      (edgeMatrix x).toLin'.toAffineMap
  have hf (j : Fin 5) : f (coordinateVertex j) = x j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · change x 0 + (edgeMatrix x).toLin' 0 = x 0
      rw [map_zero, add_zero]
    · change x 0 + (edgeMatrix x).toLin' (Pi.single j 1) = x j.succ
      rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
      ext i
      change x 0 i + (x j.succ i - x 0 i) = x j.succ i
      ring
  have hr : f '' Set.range coordinateVertex = Set.range x := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hf)
  rw [← hr, ← AffineMap.image_convexHull, Set.image_image]
  rfl

theorem simplex_volume (x : Fin 5 → ExponentSpace) :
    (volume (convexHull ℝ (Set.range x))).toReal =
      |(edgeMatrix x).det| * (volume unitSimplex).toReal := by
  have hshift (s : Set ExponentSpace) : volume ((fun y => x 0 + y) '' s) = volume s := by
    let e := MeasurableEquiv.addLeft (x 0)
    change volume (e '' s) = volume s
    rw [e.image_eq_preimage_symm]
    exact measure_preimage_add volume (-(x 0)) s
  rw [simplexImage, hshift, Measure.addHaar_image_linearMap, LinearMap.det_toLin',
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

private def cubeCorner (b : Fin 4 → Bool) : ExponentSpace :=
  fun i => if b i then 1 else 0

/-- An affine interpolation in each coordinate places the entire cube image
inside the convex hull of the images of its corners. -/
private theorem cube_image_mem_hull (f : ExponentSpace → ExponentSpace)
    (haff : ∀ (a : ExponentSpace) (i : Fin 4) (t : ℝ),
      f (Function.update a i t) =
        (1 - t) • f (Function.update a i 0) + t • f (Function.update a i 1))
    (a : ExponentSpace) (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) :
    f a ∈ convexHull ℝ (Set.range (f ∘ cubeCorner)) := by
  classical
  have aux : ∀ (S : Finset (Fin 4)) (a : ExponentSpace),
      (∀ i, a i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i ∉ S, a i = 0 ∨ a i = 1) →
      f a ∈ convexHull ℝ (Set.range (f ∘ cubeCorner)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro a _ ha'
      let b : Fin 4 → Bool := fun i => decide (a i = 1)
      have hb : cubeCorner b = a := by
        funext i
        rcases ha' i (by simp) with h | h <;> simp [cubeCorner, b, h]
      exact subset_convexHull ℝ _ ⟨b, congrArg f hb⟩
    | @insert i S hi ih =>
      intro a ha ha'
      have hup (t : ℝ) (ht : t = 0 ∨ t = 1) (ht' : t ∈ Set.Icc (0 : ℝ) 1) :
          f (Function.update a i t) ∈ convexHull ℝ (Set.range (f ∘ cubeCorner)) := by
        apply ih
        · intro j
          by_cases hj : j = i
          · subst j
            simpa only [Function.update_self] using ht'
          · simpa only [Function.update_of_ne hj] using ha j
        · intro j hj
          by_cases hji : j = i
          · subst j
            simpa only [Function.update_self] using ht
          · rw [Function.update_of_ne hji]
            exact ha' j (by simp [hji, hj])
      have he := haff a i (a i)
      rw [Function.update_eq_self] at he
      rw [he]
      exact (convex_convexHull ℝ _) (hup 0 (Or.inl rfl) (by simp))
        (hup 1 (Or.inr rfl) (by simp)) (sub_nonneg.mpr (ha i).2) (ha i).1 (by ring)
  exact aux Finset.univ a ha (by simp)

private def capPoint (s : Shape) (h : ℕ) (a : ExponentSpace) : ExponentSpace :=
  let z := a 2 * (s.t : ℝ)
  let y := a 1 * ((s.j : ℝ) - 2 * z)
  ![a 0 * ((s.b : ℝ) - y - z), y, z, a 3 * (h : ℝ)]

private theorem capPoint_affine (s : Shape) (h : ℕ) (a : ExponentSpace)
    (i : Fin 4) (t : ℝ) :
    capPoint s h (Function.update a i t) =
      (1 - t) • capPoint s h (Function.update a i 0) +
        t • capPoint s h (Function.update a i 1) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [capPoint, Function.update, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem capPoint_mem (s : Shape) (h : ℕ) (hc : Chamber s)
    (a : ExponentSpace) (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) :
    capPoint s h a ∈ capBody s h := by
  have hct : (2 : ℝ) * (s.t : ℝ) ≤ s.j := by exact_mod_cast hc.2
  have hcj : (s.j : ℝ) ≤ s.b := by exact_mod_cast hc.1
  let z := a 2 * (s.t : ℝ)
  have hz : 0 ≤ z := mul_nonneg (ha 2).1 (Nat.cast_nonneg _)
  have hzt : z ≤ s.t := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha 2).2 (Nat.cast_nonneg s.t : (0 : ℝ) ≤ s.t)
  let y := a 1 * ((s.j : ℝ) - 2 * z)
  have hj : 0 ≤ (s.j : ℝ) - 2 * z := by linarith
  have hy : 0 ≤ y := mul_nonneg (ha 1).1 hj
  have hyj : y ≤ (s.j : ℝ) - 2 * z := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha 1).2 hj
  have hb : 0 ≤ (s.b : ℝ) - y - z := by linarith
  have hxb : a 0 * ((s.b : ℝ) - y - z) ≤ (s.b : ℝ) - y - z := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha 0).2 hb
  refine ⟨?_, ?_, ?_, hzt, ?_⟩
  · intro j
    fin_cases j
    · exact mul_nonneg (ha 0).1 hb
    · exact hy
    · exact hz
    · exact mul_nonneg (ha 3).1 (Nat.cast_nonneg _)
  · change a 0 * ((s.b : ℝ) - y - z) + y + z ≤ s.b
    linarith
  · change y + 2 * z ≤ s.j
    linarith
  · change a 3 * (h : ℝ) ≤ h
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha 3).2 (Nat.cast_nonneg h : (0 : ℝ) ≤ h)

private theorem scale_to_interval {u b : ℝ} (hu : 0 ≤ u) (hb : u ≤ b) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, t * b = u := by
  rcases (hu.trans hb).eq_or_lt with he | hp
  · exact ⟨0, by simp, by linarith⟩
  · exact ⟨u / b, ⟨div_nonneg hu hp.le, (div_le_one hp).mpr hb⟩, div_mul_cancel₀ _ hp.ne'⟩

theorem cap_polytope (s : Shape) (h : ℕ) (hc : Chamber s) :
    ∃ v : Finset ExponentSpace, capBody s h = convexHull ℝ (v : Set ExponentSpace) := by
  classical
  let f := capPoint s h ∘ cubeCorner
  refine ⟨Finset.univ.image f, ?_⟩
  have hr : ((Finset.univ.image f : Finset ExponentSpace) : Set ExponentSpace) = Set.range f := by
    simp
  rw [hr]
  refine Set.Subset.antisymm ?_ (convexHull_min ?_ (capBody_convex s h))
  · intro x hx
    obtain ⟨hx, hb, hj, ht, hh⟩ := hx
    obtain ⟨a0, h0, ha0⟩ := scale_to_interval (hx 0)
      (show x 0 ≤ (s.b : ℝ) - x 1 - x 2 by linarith)
    obtain ⟨a1, h1, ha1⟩ := scale_to_interval (hx 1)
      (show x 1 ≤ (s.j : ℝ) - 2 * x 2 by linarith)
    obtain ⟨a2, h2, ha2⟩ := scale_to_interval (hx 2) ht
    obtain ⟨a3, h3, ha3⟩ := scale_to_interval (hx 3) hh
    let a : ExponentSpace := ![a0, a1, a2, a3]
    have ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1 := by
      intro i
      fin_cases i <;> assumption
    have he : capPoint s h a = x := by
      ext i
      fin_cases i <;> simp [capPoint, a, ha0, ha1, ha2, ha3]
    rw [← he]
    exact cube_image_mem_hull _ (capPoint_affine s h) _ ha
  · rintro _ ⟨b, rfl⟩
    apply capPoint_mem s h hc
    intro i
    cases hb : b i <;> simp [cubeCorner, hb]

/-- Extend a continuous formula from the positive orthant. Adding a small
amount of the total body changes each sum by at most a small thickening. -/
theorem closedOrthant (B : Fin 4 → Set ExponentSpace)
    (hconv : ∀ i, Convex ℝ (B i)) (hzero : ∀ i, 0 ∈ B i)
    (hcompact : ∀ w : Fin 4 → ℝ, IsCompact (∑ i, w i • B i))
    (p : MvPolynomial (Fin 4) ℝ)
    (hp : ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) →
      p.eval w = (volume (∑ i, w i • B i)).toReal)
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    p.eval w = (volume (∑ i, w i • B i)).toReal := by
  let K : Set ExponentSpace := ∑ i, w i • B i
  let L : Set ExponentSpace := ∑ i, B i
  change p.eval w = (volume K).toReal
  have hK : IsCompact K := hcompact w
  have hL : IsCompact L := by simpa [L] using hcompact (fun _ => 1)
  have hzL : 0 ∈ L := Set.mem_fintype_sum _ _ |>.mpr
    ⟨fun _ => 0, hzero, by simp⟩
  obtain ⟨R, hR⟩ := hL.isBounded.exists_norm_le
  let w' (t : ℝ) : Fin 4 → ℝ := fun i => w i + t
  have hadd (t : ℝ) (ht : 0 ≤ t) : (∑ i, w' t i • B i) = K + t • L := by
    rw [show K + t • L = (∑ i, w i • B i) + t • (∑ i, B i) from rfl,
      Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (hconv i).add_smul (hw i) ht)
  have hpos : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, 0 < t := self_mem_nhdsWithin
  have hp' (t : ℝ) (ht : 0 < t) :
      p.eval (w' t) = (volume (K + t • L)).toReal := by
    rw [hp _ (fun i => add_pos_of_nonneg_of_pos (hw i) ht), hadd t ht.le]
  have hw' : Tendsto w' (𝓝[Set.Ioi 0] 0) (𝓝 w) := by
    have hc : Continuous w' := by unfold w'; fun_prop
    have h0 : w' 0 = w := by simp [w']
    rw [← h0]
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hpLim := (p.continuous_eval.tendsto w).comp hw'
  have hr : Tendsto (fun t : ℝ => t * R) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    simpa using ((continuous_id.mul_const R).tendsto 0).mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0)
  have htLim := (ENNReal.tendsto_toReal hK.measure_lt_top.ne).comp
    ((tendsto_measure_cthickening_of_isCompact (μ := volume) hK).comp hr)
  apply le_antisymm
  · refine le_of_tendsto_of_tendsto hpLim htLim (hpos.mono fun t ht => ?_)
    change p.eval (w' t) ≤ (volume (Metric.cthickening (t * R) K)).toReal
    rw [hp' t ht]
    apply measureReal_mono _ (hK.isBounded.cthickening.measure_lt_top.ne)
    rintro _ ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩
    refine Metric.mem_cthickening_of_dist_le _ x _ _ hx ?_
    simpa [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le] using
      mul_le_mul_of_nonneg_left (hR y hy) ht.le
  · refine le_of_tendsto_of_tendsto tendsto_const_nhds hpLim (hpos.mono fun t ht => ?_)
    change (volume K).toReal ≤ p.eval (w' t)
    rw [hp' t ht]
    apply measureReal_mono _ (by rw [← hadd t ht.le]; exact (hcompact _).measure_lt_top.ne)
    intro x hx
    exact Set.mem_add.mpr ⟨x, hx, 0, ⟨0, hzL, smul_zero t⟩, add_zero x⟩

end
end K1_13_5_4_2_5_2_1
end PackSource_K1_13_5_4_2_5_2_1Volume

section PackSource_K1_13_5_4_2_5_2_1Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_5_2_1

noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 K1_13_5_4_2_5 K1_13_5_4_2_5_2
open MeasureTheory MvPolynomial
open scoped BigOperators Pointwise

/-- The full-dimensional flag simplices cover the hull up to a null set. -/
def c1 : Prop :=
  ∀ {α : Type} [Fintype α] (v : α → ExponentSpace),
    convexHull ℝ (Set.range v) =ᵐ[volume] ⋃ F ∈ flags v, flagSimplex v F

/-- Distinct flag simplices overlap only on null sets. -/
def c2 : Prop :=
  ∀ {α : Type} [Fintype α] (v : α → ExponentSpace),
    Set.Pairwise (↑(flags v) : Set (Fin 5 → Finset α))
      (fun F G => AEDisjoint volume (flagSimplex v F) (flagSimplex v G))

private theorem expose_eq {α : Type} {v : α → ExponentSpace} {S : Finset α}
    {f : ExponentSpace →ₗ[ℝ] ℝ} (hf : Exposes v S f)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) : f (v b) = f (v a) :=
  le_antisymm ((hf a).1 ha b) ((hf b).1 hb a)

private theorem expose_lt {α : Type} {v : α → ExponentSpace} {S : Finset α}
    {f : ExponentSpace →ₗ[ℝ] ℝ} (hf : Exposes v S f)
    {a b : α} (ha : a ∈ S) (hb : b ∉ S) : f (v b) < f (v a) := by
  refine lt_of_le_of_ne ((hf a).1 ha b) (fun he => hb ((hf b).2 (fun c => ?_)))
  rw [he]
  exact (hf a).1 ha c

theorem faceCenter_expose_eq {α : Type} {v : α → ExponentSpace} {S T : Finset α}
    {f : ExponentSpace →ₗ[ℝ] ℝ} (hf : Exposes v S f)
    {a : α} (ha : a ∈ S) (hT : T.Nonempty) (hsub : T ⊆ S) :
    f (faceCenter v T) = f (v a) := by
  have hc : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  simp only [faceCenter, map_smul, smul_eq_mul, map_sum]
  rw [Finset.sum_congr rfl (fun b hb => expose_eq hf ha (hsub hb)),
    Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem faceCenter_expose_lt {α : Type} {v : α → ExponentSpace} {S T : Finset α}
    {f : ExponentSpace →ₗ[ℝ] ℝ} (hf : Exposes v S f)
    {a : α} (ha : a ∈ S) (hsub : ¬ T ⊆ S) : f (faceCenter v T) < f (v a) := by
  obtain ⟨b, hb, hbs⟩ := Finset.not_subset.mp hsub
  have hc : (0 : ℝ) < T.card := by exact_mod_cast (Finset.card_pos.mpr ⟨b, hb⟩)
  have hlt : ∑ c ∈ T, f (v c) < ∑ _c ∈ T, f (v a) :=
    Finset.sum_lt_sum (fun c _ => (hf a).1 ha c) ⟨b, hb, expose_lt hf ha hbs⟩
  have he := mul_lt_mul_of_pos_left hlt (inv_pos.mpr hc)
  simpa only [faceCenter, map_smul, smul_eq_mul, map_sum, Finset.sum_const, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using he

/-- A supporting functional for the preceding face detects the last
nonzero coefficient of any proposed affine dependence. -/
theorem flag_affineIndependent {α : Type} [Fintype α] (v : α → ExponentSpace)
    (F : Fin 5 → Finset α) (hF : F ∈ flags v) :
    AffineIndependent ℝ (fun j => faceCenter v (F j)) := by
  classical
  obtain ⟨hmono, hface⟩ := (mem_flags v F).1 hF
  rw [affineIndependent_iff_of_fintype]
  intro w hw hz i
  by_contra hi
  let T := Finset.univ.filter (fun k : Fin 5 => w k ≠ 0)
  have hiT : i ∈ T := by simp [T, hi]
  let j := T.max' ⟨i, hiT⟩
  have hjT : j ∈ T := T.max'_mem _
  have hj : w j ≠ 0 := (Finset.mem_filter.mp hjT).2
  have hzero (k : Fin 5) (hk : j < k) : w k = 0 := by
    by_contra h
    exact (not_le_of_gt hk) (T.le_max' k (by simp [T, h]))
  have hjne : j ≠ 0 := by
    intro he
    have hsum : (∑ k, w k) = w j := by
      refine Finset.sum_eq_single j (fun k _ hk => hzero k ?_) (by simp)
      rw [he] at hk ⊢
      exact Fin.pos_iff_ne_zero.mpr hk
    exact hj (hsum ▸ hw)
  obtain ⟨p, hp⟩ := Fin.exists_succ_eq_of_ne_zero hjne
  have hpj : p.castSucc < j := hp ▸ p.castSucc_lt_succ
  obtain ⟨a, ha⟩ := (hface p.castSucc).1
  obtain ⟨f, hf⟩ := (hface p.castSucc).2
  have hl (k : Fin 5) (hk : k < j) : f (faceCenter v (F k)) = f (v a) := by
    apply faceCenter_expose_eq hf ha (hface k).1
    apply hmono.monotone
    rw [← hp] at hk
    exact Fin.le_castSucc_iff.mpr hk
  have hjlt : f (faceCenter v (F j)) < f (v a) :=
    faceCenter_expose_lt hf ha (not_le_of_gt (hmono hpj))
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hz
  have hv := congrArg f hz
  simp only [map_zero, map_sum, map_smul, smul_eq_mul] at hv
  have hsum : ∑ k, w k * (f (faceCenter v (F k)) - f (v a)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hv, hw, zero_mul, sub_zero]
  have he : (∑ k, w k * (f (faceCenter v (F k)) - f (v a))) =
      w j * (f (faceCenter v (F j)) - f (v a)) := by
    refine Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hl k hk, sub_self, mul_zero]
    · rw [hzero k hk, zero_mul]
  rw [he] at hsum
  exact (mul_ne_zero hj (ne_of_lt (sub_neg.mpr hjlt))) hsum

private abbrev Labels (v : Fin 4 → Finset ExponentSpace) := (i : Fin 4) → ↥(v i)

private def labelPoint (v : Fin 4 → Finset ExponentSpace) (w : Fin 4 → ℝ)
    (a : Labels v) : ExponentSpace :=
  ∑ i, w i • (a i : ExponentSpace)

private theorem labelHull_eq (B : Fin 4 → Set ExponentSpace)
    (v : Fin 4 → Finset ExponentSpace) (hv : ∀ i, B i = convexHull ℝ (v i : Set ExponentSpace))
    (w : Fin 4 → ℝ) :
    convexHull ℝ (Set.range (labelPoint v w)) = ∑ i, w i • B i := by
  have hr : Set.range (labelPoint v w) = ∑ i, w i • (v i : Set ExponentSpace) := by
    ext x
    rw [Set.mem_fintype_sum]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨fun i => w i • (a i : ExponentSpace), fun i => ⟨_, (a i).2, rfl⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      choose a ha he using hz
      exact ⟨fun i => ⟨a i, ha i⟩, Finset.sum_congr rfl (fun i _ => he i)⟩
  rw [hr, convexHull_sum]
  simp only [convexHull_smul, ← hv]

private theorem labelMax_iff (v : Fin 4 → Finset ExponentSpace) (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 < w i) (f : ExponentSpace →ₗ[ℝ] ℝ) (a : Labels v) :
    (∀ b, f (labelPoint v w b) ≤ f (labelPoint v w a)) ↔
      ∀ i (b : ↥(v i)), f (b : ExponentSpace) ≤ f (a i : ExponentSpace) := by
  simp only [labelPoint, map_sum, map_smul, smul_eq_mul]
  constructor
  · intro h i b
    by_contra! hi
    apply (not_lt_of_ge (h (Function.update a i b)))
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j = i
      · subst j
        rw [Function.update_self]
        exact mul_le_mul_of_nonneg_left hi.le (hw i).le
      · rw [Function.update_of_ne hj]
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [Function.update_self]
      exact mul_lt_mul_of_pos_left hi (hw i)
  · intro h b
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i (b i)) (hw i).le)

private theorem flags_eq (v : Fin 4 → Finset ExponentSpace) (u w : Fin 4 → ℝ)
    (hu : ∀ i, 0 < u i) (hw : ∀ i, 0 < w i) :
    flags (labelPoint v u) = flags (labelPoint v w) := by
  classical
  ext F
  simp only [flags, Finset.mem_filter, Finset.mem_univ, true_and, IsFaceLabels, Exposes,
    labelMax_iff v u hu, labelMax_iff v w hw]

private def centerCoeff (v : Fin 4 → Finset ExponentSpace) (F : Fin 5 → Finset (Labels v))
    (j : Fin 5) (k : Fin 4) : ExponentSpace :=
  faceCenter (fun a => (a k : ExponentSpace)) (F j)

private theorem center_eq (v : Fin 4 → Finset ExponentSpace) (w : Fin 4 → ℝ)
    (F : Fin 5 → Finset (Labels v)) (j : Fin 5) :
    faceCenter (labelPoint v w) (F j) = ∑ k, w k • centerCoeff v F j k := by
  simp only [faceCenter, labelPoint, centerCoeff]
  rw [Finset.sum_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.smul_sum, smul_comm]

private theorem edge_det_ne_zero (x : Fin 5 → ExponentSpace) (hx : AffineIndependent ℝ x) :
    (edgeMatrix x).det ≠ 0 := by
  intro hd
  obtain ⟨a, hne, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  apply hne
  let e := finSuccAboveEquiv (0 : Fin 5)
  have hli := (affineIndependent_iff_linearIndependent_vsub ℝ x 0).mp hx
  have hli' : LinearIndependent ℝ (fun j : Fin 4 => x j.succ - x 0) := by
    exact hli.comp e e.injective
  apply (linearIndependent_iff_injective_fintypeLinearCombination.mp hli')
  change (∑ j, a j • (x j.succ - x 0)) = ∑ j, (0 : ExponentSpace) j • (x j.succ - x 0)
  ext i
  have hi := congrFun ha i
  simpa [edgeMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.sub_apply, mul_comm] using hi

private def edgePolynomial (c : Fin 5 → Fin 4 → ExponentSpace) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) ℝ) :=
  fun i j => ∑ k, C (c j.succ k i - c 0 k i) * MvPolynomial.X k

private theorem edgePolynomial_hom (c : Fin 5 → Fin 4 → ExponentSpace) :
    (edgePolynomial c).det.IsHomogeneous 4 := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro σ _
  have hp : (∏ i, edgePolynomial c (σ i) i).IsHomogeneous (∑ _i : Fin 4, 1) :=
    IsHomogeneous.prod _ _ _ (fun i _ =>
      IsHomogeneous.sum _ _ _ (fun _ _ => isHomogeneous_C_mul_X _ _))
  have hp' : (∏ i, edgePolynomial c (σ i) i).IsHomogeneous 4 := by simpa using hp
  rw [← map_intCast (C : ℝ →+* MvPolynomial (Fin 4) ℝ)]
  exact hp'.C_mul _

private theorem edgePolynomial_eval (c : Fin 5 → Fin 4 → ExponentSpace) (w : Fin 4 → ℝ) :
    (edgePolynomial c).det.eval w = (edgeMatrix (fun j => ∑ k, w k • c j k)).det := by
  rw [(eval w).map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, edgePolynomial, map_sum, map_mul, eval_C, eval_X, edgeMatrix,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

private def orientation (q : MvPolynomial (Fin 4) ℝ) : ℝ :=
  if 0 ≤ q.eval (fun _ => 1) then 1 else -1

private theorem oriented_eval (q : MvPolynomial (Fin 4) ℝ)
    (hn : ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) → q.eval w ≠ 0)
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) :
    |q.eval w| = orientation q * q.eval w := by
  let U : Set (Fin 4 → ℝ) := Set.univ.pi (fun _ => Set.Ioi (0 : ℝ))
  have hU : Convex ℝ U := convex_pi (fun _ _ => convex_Ioi _)
  have h := hU.isPreconnected.image (fun a => q.eval a) q.continuous_eval.continuousOn
  have hz : 0 ∉ (fun a => q.eval a) '' U := by
    rintro ⟨a, ha, hq⟩
    exact hn a (by simpa [U] using ha) hq
  have hw' : q.eval w ∈ (fun a => q.eval a) '' U := ⟨w, by simpa [U] using hw, rfl⟩
  have he : q.eval (fun _ => 1) ∈ (fun a => q.eval a) '' U :=
    ⟨fun _ => 1, by simp [U], rfl⟩
  unfold orientation
  split_ifs with hs
  · have hg : 0 ≤ q.eval w := by
      by_contra! hc
      exact hz (h.Icc_subset hw' he ⟨hc.le, hs⟩)
    simp [abs_of_nonneg hg]
  · have hg : q.eval w ≤ 0 := by
      by_contra! hc
      exact hz (h.Icc_subset he hw' ⟨(lt_of_not_ge hs).le, hc.le⟩)
    simp [abs_of_nonpos hg]

private theorem hull_volume (h1 : c1) (h2 : c2) {α : Type} [Fintype α] (v : α → ExponentSpace) :
    (volume (convexHull ℝ (Set.range v))).toReal =
      ∑ F ∈ flags v, (volume (flagSimplex v F)).toReal := by
  have hF (F : Fin 5 → Finset α) : IsCompact (flagSimplex v F) :=
    (Set.finite_range _).isCompact_convexHull ℝ
  calc
    _ = (volume (⋃ F ∈ flags v, flagSimplex v F)).toReal :=
      congrArg ENNReal.toReal (measure_congr (h1 v))
    _ = _ := measureReal_biUnion_finset₀ (h2 v)
      (fun F _ => (hF F).measurableSet.nullMeasurableSet)
      (fun F _ => (hF F).measure_lt_top.ne)

private theorem positivePolynomial (h1 : c1) (h2 : c2)
    (B : Fin 4 → Set ExponentSpace) (v : Fin 4 → Finset ExponentSpace)
    (hv : ∀ i, B i = convexHull ℝ (v i : Set ExponentSpace)) :
    ∃ p : MvPolynomial (Fin 4) ℝ, p.IsHomogeneous 4 ∧
      ∀ w : Fin 4 → ℝ, (∀ i, 0 < w i) →
        p.eval w = (volume (∑ i, w i • B i)).toReal := by
  classical
  let fs := flags (labelPoint v (fun _ => 1))
  let q (F : Fin 5 → Finset (Labels v)) := (edgePolynomial (centerCoeff v F)).det
  let p := ∑ F ∈ fs, C ((volume unitSimplex).toReal * orientation (q F)) * q F
  have heval (F : Fin 5 → Finset (Labels v)) (w : Fin 4 → ℝ) :
      (q F).eval w = (edgeMatrix (fun j => faceCenter (labelPoint v w) (F j))).det := by
    dsimp only [q]
    rw [edgePolynomial_eval]
    simp_rw [center_eq v w F]
  have hflags (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) :
      flags (labelPoint v w) = fs := flags_eq v w _ hw (fun _ => zero_lt_one)
  have hn (F : Fin 5 → Finset (Labels v)) (hF : F ∈ fs)
      (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) : (q F).eval w ≠ 0 := by
    rw [heval]
    apply edge_det_ne_zero
    exact flag_affineIndependent (labelPoint v w) F (by rw [hflags w hw]; exact hF)
  refine ⟨p, IsHomogeneous.sum _ _ _ (fun F _ => (edgePolynomial_hom _).C_mul _), ?_⟩
  intro w hw
  rw [← labelHull_eq B v hv w, hull_volume h1 h2, hflags w hw]
  simp only [p, MvPolynomial.eval_sum, map_mul, eval_C]
  apply Finset.sum_congr rfl
  intro F hF
  rw [flagSimplex, simplex_volume, ← heval, oriented_eval (q F) (hn F hF) w hw]
  ring

theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2_5_2.c1 := by
  classical
  intro P hP _
  have hslot (i : Fin 4) :
      ∃ v : Finset ExponentSpace, slots P i = convexHull ℝ (v : Set ExponentSpace) := by
    by_cases hi : i = 0
    · subst i
      obtain ⟨s, hs, hr⟩ := hP.polytope
      exact ⟨hs.toFinset, by simpa [slots] using hr⟩
    · rw [slots, Function.update_of_ne hi]
      have hc : Chamber (slotShape i) := by
        fin_cases i <;> exact ⟨by decide, by decide⟩
      exact cap_polytope _ _ hc
  choose v hv using hslot
  obtain ⟨p, hp, he⟩ := positivePolynomial h1 h2 (slots P) v hv
  refine ⟨p, hp, closedOrthant (slots P) ?_ ?_ ?_ p he⟩
  · intro i
    rw [hv i]
    exact convex_convexHull _ _
  · intro i
    by_cases hi : i = 0
    · simpa [slots, hi] using hP.zero_mem
    · simp [slots, Function.update_of_ne hi, capBody]
  · intro w
    rw [← labelHull_eq (slots P) v hv w]
    exact (Set.finite_range _).isCompact_convexHull ℝ

end
end K1_13_5_4_2_5_2_1
end PackSource_K1_13_5_4_2_5_2_1Split

section PackSource_K1_14_3R_3_1_3_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace K1_14_3R_3_1_3_2

noncomputable section

open K1_13_6_3_5_3 (CurvePlace poleOrder)
open K1_14_3R_3_1 (functionDegree)
open K1_14_3R_3_1_3 (PlaceResidue chartAlgebra placeConstants placeWeight weightedPoleDegree)
open scoped BigOperators Polynomial

section Residues

variable {k F : Type} [Field k] [Field F] [Algebra k F]
variable [Algebra k[X] F] [IsScalarTower k k[X] F]
variable [IsDedekindDomain (Normalization k F)] [IsFractionRing (Normalization k F) F]
variable [Algebra k (Normalization k F)] [IsScalarTower k k[X] (Normalization k F)]

/-- The valuation ring of the adic place is the localization at its prime. -/
private def primeResidueEquiv (x : F) (hx : x ≠ 0) (hu : coordinate k F = x⁻¹)
    (P : OriginPrimes k F) [P.val.IsPrime] :
    P.val.ResidueField ≃ₐ[k] PlaceResidue (primePole x hx hu P).val := by
  let B := Normalization k F
  let p := (primePole x hx hu P).val
  let Q := primeAtOrigin (hu.symm ▸ inv_ne_zero hx) P
  let T := Q.valuationSubringAtPrime F
  have : IsLocalization P.val.primeCompl T := by
    change IsLocalization Q.asIdeal.primeCompl (Q.valuationSubringAtPrime F)
    infer_instance
  let loc : Localization.AtPrime P.val ≃ₐ[B] T :=
    IsLocalization.algEquiv P.val.primeCompl _ _
  have hT : T.toSubring = p.value.valuationSubring.toSubring :=
    congrArg ValuationSubring.toSubring (Q.valuationSubringAtPrime_eq_valuationSubring (K := F))
  let e : Localization.AtPrime P.val ≃+* p.value.valuationSubring :=
    loc.toRingEquiv.trans (RingEquiv.subringCongr hT)
  refine { IsLocalRing.ResidueField.mapEquiv e with commutes' := fun a => ?_ }
  change IsLocalRing.ResidueField.mapEquiv e
      (IsLocalRing.residue _ (algebraMap k (Localization.AtPrime P.val) a)) =
    IsLocalRing.residue _ (placeConstants p a)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  rw [IsScalarTower.algebraMap_apply k B (Localization.AtPrime P.val)]
  change (RingEquiv.subringCongr hT (loc (algebraMap B _ (algebraMap k B a)))).val = _
  rw [RingEquiv.coe_subringCongr_apply, loc.commutes]
  change algebraMap B F (algebraMap k B a) = algebraMap k F a
  rw [IsScalarTower.algebraMap_apply k k[X] B, ← IsScalarTower.algebraMap_apply k[X] B F,
    ← IsScalarTower.algebraMap_apply k k[X] F]

private theorem primePole_residue [Module.Finite k[X] (Normalization k F)]
    (x : F) (hx : x ≠ 0) (hu : coordinate k F = x⁻¹) (P : OriginPrimes k F) :
    FiniteDimensional k (PlaceResidue (primePole x hx hu P).val) ∧
      placeWeight (primePole x hx hu P).val = P.val.inertiaDeg k[X] := by
  let B := Normalization k F
  let p := origin k
  let Q := P.val
  let R := k[X] ⧸ p
  let S := B ⧸ Q
  have : Q.IsPrime := P.property.1
  have : Q.LiesOver p := P.property.2
  have : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q p
  let : Field R := Ideal.Quotient.field p
  let : Field S := Ideal.Quotient.field Q
  let e : S ≃ₐ[k] PlaceResidue (primePole x hx hu P).val :=
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom k S Q.ResidueField)
      Q.bijective_algebraMap_quotient_residueField).trans (primeResidueEquiv x hx hu P)
  have : Module.Finite k R := Module.Finite.of_surjective
    (originQuotient (k := k)).symm.toLinearMap (originQuotient (k := k)).symm.surjective
  have : Module.Finite k[X] S := Module.Finite.of_surjective
    (IsScalarTower.toAlgHom k[X] B S).toLinearMap (Ideal.Quotient.mk_surjective (I := Q))
  have : Module.Finite R S := Module.Finite.of_restrictScalars_finite k[X] R S
  have : Module.Finite k S := Module.Finite.trans R S
  refine ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, ?_⟩
  have hrank : Module.finrank k R = 1 :=
    (originQuotient (k := k)).toLinearEquiv.finrank_eq.trans (Module.finrank_self k)
  rw [placeWeight, ← e.toLinearEquiv.finrank_eq, Ideal.inertiaDeg_eq_of_isMaximal p Q,
    ← Module.finrank_mul_finrank k R S, hrank, one_mul]

end Residues

theorem proof : K1_14_3R_3_1_3.c2 := by
  classical
  intro k F _ _ _ x hx hfield hnorm
  let : Algebra k[X] F := chartAlgebra (k := k) x⁻¹
  have : IsScalarTower k k[X] F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap k F a = Polynomial.aeval x⁻¹ (Polynomial.C a)
    rw [Polynomial.aeval_C]
  have hu : coordinate k F = x⁻¹ := Polynomial.aeval_X _
  have htr : Transcendental k (coordinate k F) := by
    rw [hu]
    exact fun hi => hx (IsAlgebraic.inv_iff.mp hi)
  have : FiniteDimensional (chartField (k := k) (coordinate k F)) F := by
    rw [hu, chartField_inv]
    exact hfield
  let B := Normalization k F
  have : Module.Finite k[X] B := hnorm
  have : IsDedekindDomain B := normalization_dedekind htr
  have : IsFractionRing B F := normalization_fraction htr
  let : Algebra k B := Algebra.compHom B (algebraMap k k[X])
  have : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.IsTorsionFree k[X] B := normalization_torsionFree htr
  have : Module.Free k[X] B := inferInstance
  let e := Equiv.ofBijective (primePole x hx.ne_zero hu) (primePole_bijective x hx.ne_zero hu)
  have hres (P : OriginPrimes k F) :=
    primePole_residue x hx.ne_zero hu P
  have : Fintype (PolePlaces k F x) := Fintype.ofEquiv (OriginPrimes k F) e
  let f := fun v : CurvePlace k F => placeWeight v * poleOrder v.value x
  have hf : Finite (Function.support (fun v : CurvePlace k F => poleOrder v.value x)) := by
    change Finite (PolePlaces k F x)
    infer_instance
  refine ⟨Set.finite_coe_iff.mp hf, ?_, ?_⟩
  · intro v hv
    obtain ⟨P, hP⟩ := e.surjective ⟨v, hv⟩
    have hv' : (primePole x hx.ne_zero hu P).val = v := congrArg Subtype.val hP
    rw [← hv']
    exact (hres P).1
  change finsum f = functionDegree k x
  calc
    finsum f = ∑ᶠ v : PolePlaces k F x, f v.val := by
      rw [finsum_subtype_eq_finsum_cond, ← finsum_mem_univ f]
      apply finsum_mem_inter_support_eq'
      intro v hv
      exact iff_of_true (Set.mem_univ _) (fun h => hv (by simp [f, h]))
    _ = ∑ᶠ P : OriginPrimes k F, P.val.ramificationIdx k[X] * P.val.inertiaDeg k[X] := by
      symm
      apply finsum_eq_of_bijective e e.bijective
      intro P
      change _ = placeWeight (primePole x hx.ne_zero hu P).val *
        poleOrder (primePole x hx.ne_zero hu P).val.value x
      rw [(hres P).2, primePole_order, mul_comm]
    _ = Module.finrank k[X] B := by
      rw [finsum_eq_sum_of_fintype, Ideal.sum_ramification_inertia_eq_finrank]
    _ = functionDegree k x := by
      rw [normalization_rank htr, hu, chartField_inv, functionDegree, ite_eq_right hx]

end

end K1_14_3R_3_1_3_2
end PackSource_K1_14_3R_3_1_3_2Proof
