import ProximityPrize.SubmissionLower.Fast000
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast055
set_option Elab.async false

section PackSource_K1_13_5_5Capacity
set_option autoImplicit true
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

namespace K1_13_5_5

noncomputable section

open K1 K1_13 K1_13_5 Finset MvPolynomial
open scoped BigOperators Polynomial

private def valueCut (x a : K) : CoeffRing :=
  jetForm (embed x) 0 - C (embed a)

private theorem valueCut_degree (x a : K) : (valueCut x a).totalDegree ≤ 1 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply totalDegree_finsetSum_le
  intro j _
  simpa only [totalDegree_C, totalDegree_X, zero_add] using
    (totalDegree_mul (C ((j.val.choose 0 : Geom) * embed x ^ (j.val - 0))) (MvPolynomial.X j))

private theorem valueCut_eval {S : K[X]} (hS : S.natDegree ≤ 133634) (x a : K) :
    aeval (coeffPoint (extend S)) (valueCut x a) = 0 ↔ S.eval x = a := by
  have heval : S.eval x = ∑ j : CoeffIndex, S.coeff j.val * x ^ j.val := by
    have hlt : S.natDegree < taylorLength := Nat.lt_succ_of_le hS
    conv_lhs => rw [S.as_sum_range_C_mul_X_pow' hlt]
    rw [Fin.sum_univ_eq_sum_range (fun j => S.coeff j * x ^ j)]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hmap : embed (∑ j : CoeffIndex, S.coeff j.val * x ^ j.val) =
      ∑ j : CoeffIndex, embed x ^ j.val * embed (S.coeff j.val) := by
    rw [map_sum]
    exact sum_congr rfl fun _ _ => by rw [map_mul, map_pow, mul_comm]
  simp only [valueCut, jetForm, coeffPoint, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero,
    one_mul, map_sub, map_sum, map_mul, aeval_C, aeval_X, Polynomial.coeff_map, sub_eq_zero,
    Algebra.algebraMap_self_apply]
  rw [heval, ← hmap]
  exact embed.injective.eq_iff

private theorem coeffPoint_injOn {w Γ s} (h : Messages w Γ s) :
    Set.InjOn (fun γ => coeffPoint (extend (s γ))) (Γ : Set K) := by
  intro γ hγ η hη heq
  apply h.distinct hγ hη
  apply Polynomial.ext
  intro j
  by_cases hj : j < taylorLength
  · exact embed.injective (by simpa [coeffPoint] using congrFun heq ⟨j, hj⟩)
  · change ¬ j < 133635 at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := s γ) (by
          have := h.degree γ hγ
          omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (p := s η) (by
          have := h.degree η hη
          omega)]

private theorem nodeCapacity_of_sections {w Γ s d}
    (hcap : ∀ i : I, (∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) →
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d) :
    NodeCapacity w Γ s d := by
  classical
  let persistent := univ.filter fun i : I => ∀ γ ∈ Γ, (s γ).eval (node i) = w i
  refine ⟨persistent, ?_, ?_⟩
  · exact fun i hi => (mem_filter.mp hi).2
  · intro i hi
    apply hcap i
    by_contra! hall
    exact hi (mem_filter.mpr ⟨mem_univ _, hall⟩)

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

/-- The minimal primes of a proper node section cover its marked points.
The cut drops dimension by one and does not increase total degree. -/
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
  have hproper : cut ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hm
    exact hv ((valueCut_eval (h.degree γ hγ) x a).mp (hpoints γ hγ _ hm))
  have hcover : U ⊆ Ps.biUnion part := by
    intro γ hγ
    obtain ⟨hγΓ, hv⟩ := mem_filter.mp hγ
    have hp : coeffPoint (extend (s γ)) ∈ zeroLocus Geom (P ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ, (valueCut_eval (h.degree γ hγΓ) x a).mpr hv⟩
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

/-- A curve's affine degree is the difference of successive Hilbert-function
values, once the Hilbert function agrees with its polynomial. -/
private theorem curve_degree_nat (P : Ideal CoeffRing) (hP : P.IsPrime)
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
  have hcount := nodeCapacity_count h hcap
  have hi : Γ.card ≤ 2 * δ := by omega
  rw [hdeg]
  exact_mod_cast hi

/-- The fixed-word price for a proper node section of a coefficient surface. -/
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

end K1_13_5_5
end PackSource_K1_13_5_5Capacity

section PackSource_K1_13_5_5Split
set_option autoImplicit true
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

namespace K1_13_5_5

noncomputable section

open K1 K1_13 K1_13_5 Finset MvPolynomial
open scoped BigOperators Polynomial

/-- Integrate the whole regular chart into a family of actual polynomial solutions.
Its coefficient ideal is defined over the constant field. -/
def c1 : Prop :=
  ∀ f : Row 3, Irreducible f → 0 < f.degreeOf 2 → f.degreeOf 2 ≤ 24 →
    TrueWeightLE f (90 * 180236 - 1) → Whole f →
    ∃ P : Ideal CoeffRing, FreshChart P (freshRow f) (freshRow (separant f)) ∧
      ∀ S : Geom[X], S.natDegree ≤ 133634 → RegularAt 2 f S →
        coeffPoint S ∈ zeroLocus Geom P

/-- Compare the coefficient degree with the degree of the hypersurface in
the independent second-jet projection. -/
def c2 : Prop :=
  ∀ (P : Ideal CoeffRing) (g d : FreshJetRing), FreshChart P g d →
    (affineHilbertPolynomial P).natDegree = 2 ∧
      2 * affineDegree P ≤ (133634 : ℚ) * (g.totalDegree : ℚ)

private theorem freshRow_degree_le (f : Row 3) : (freshRow f).totalDegree ≤ f.totalDegree := by
  unfold freshRow MvPolynomial.totalDegree
  exact Finset.sup_mono (support_map_subset (algebraMap Geom[X] FreshField) f)

theorem of_children (h1 : c1) (h2 : c2) : K1_13_5.c5 := by
  classical
  intro w Γ s hm n f hf hcover
  let part (i : Fin n) := Γ.filter fun γ => RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  let cap (i : Fin n) := 133634 * (f i).totalDegree
  have hsub (i : Fin n) : part i ⊆ Γ := filter_subset _ _
  have hlocal (i : Fin n) : NodeCapacity w (part i) s (cap i) := by
    by_cases hi : Whole (f i)
    · have htop : (f i).degreeOf 2 ≤ 24 :=
        (single_le_sum (f := fun j => (f j).degreeOf 2) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
          hf.top
      obtain ⟨P, hp, hall⟩ := h1 _ (hf.irreducible i) (hf.positive i) htop (hf.weight i) hi
      obtain ⟨hdim, hdeg⟩ := h2 _ _ _ hp
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
  · change n ≤ 120
    calc
      n = ∑ _i : Fin n, 1 := by simp
      _ ≤ ∑ i, (f i).totalDegree := sum_le_sum fun i _ =>
        (hf.positive i).trans_le (degreeOf_le_totalDegree _ _)
      _ ≤ 120 := hf.total
  · change (∑ i, 133634 * (f i).totalDegree) ≤ 133634 * 120
    rw [← mul_sum]
    exact Nat.mul_le_mul_left _ hf.total

end

end K1_13_5_5
end PackSource_K1_13_5_5Split

section PackSource_K1_13_5_5_2Dimension
set_option autoImplicit true
namespace K1_13_5_5_2

noncomputable section

open K1_13 K1_13_5_5 MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section ScalarExtension

variable {F E σ : Type*} [Field F] [Field E] [Algebra F E]

private def quotientTensor (I : Ideal (MvPolynomial σ F)) :
    E ⊗[F] (MvPolynomial σ F ⧸ I) ≃ₐ[E]
      MvPolynomial σ E ⧸ I.map (MvPolynomial.map (algebraMap F E)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F E
  let ι : MvPolynomial σ F →ₐ[F] E ⊗[F] MvPolynomial σ F := Algebra.TensorProduct.includeRight
  have hcomp : e.toRingHom.comp ι.toRingHom = MvPolynomial.map (algebraMap F E) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[F] p) = _
    simp [e]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := F) E _ E I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  exact ((Ideal.map_map (I := I) ι.toRingHom e.toRingHom).trans
    (congrArg (fun f => I.map f) hcomp)).symm

private theorem quotientTensor_tmul_one (I : Ideal (MvPolynomial σ F)) (p : MvPolynomial σ F) :
    quotientTensor (E := E) I (1 ⊗ₜ[F] (Ideal.Quotient.mk I p)) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap F E) p) := by
  simp [quotientTensor]

/-- Extending the coefficient field preserves each piece of the total-degree filtration. -/
theorem hilbertFunction_map (I : Ideal (MvPolynomial σ F)) (n : ℕ) :
    affineHilbertFunction (I.map (MvPolynomial.map (algebraMap F E))) n =
      affineHilbertFunction I n := by
  let e := (quotientTensor (E := E) I).toLinearEquiv
  let V := quotientDegreeLE I n
  have h : (V.baseChange E).map e.toLinearMap =
      quotientDegreeLE (I.map (MvPolynomial.map (algebraMap F E))) n := by
    dsimp only [V, quotientDegreeLE, restrictTotalDegree]
    simp only [restrictSupport_eq_span, Submodule.map_span, Submodule.baseChange_span,
      Set.image_image]
    congr 1
    apply Set.image_congr
    intro m hm
    change quotientTensor (E := E) I (1 ⊗ₜ[F] (Ideal.Quotient.mk I (monomial m 1))) =
      Ideal.Quotient.mk _ (monomial m 1)
    rw [quotientTensor_tmul_one, MvPolynomial.map_monomial, map_one]
  rw [affineHilbertFunction, ← h,
    ← (Submodule.equivMapOfInjective e.toLinearMap e.injective (V.baseChange E)).finrank_eq,
    ← (Submodule.toBaseChange.toLinearEquiv E V).finrank_eq, Module.finrank_baseChange]
  rfl

theorem hilbertPolynomial_map [Finite σ] (I : Ideal (MvPolynomial σ F)) :
    affineHilbertPolynomial (I.map (MvPolynomial.map (algebraMap F E))) =
      affineHilbertPolynomial I := by
  obtain ⟨n, hn⟩ := exists_eval_affineHilbertPolynomial I
  symm
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := n)
  intro m hm
  rw [hilbertFunction_map]
  exact hn m hm

end ScalarExtension

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Adjoining and inverting polynomials in an independent variable preserves primality. -/
theorem freshIdeal_isPrime (P : Ideal CoeffRing) (hP : P.IsPrime) : (freshIdeal P).IsPrime := by
  let R := MvPolynomial CoeffIndex Geom[X]
  let e : R ≃ₐ[Geom] CoeffRing[X] :=
    (optionEquivRight Geom CoeffIndex).symm.trans (optionEquivLeft Geom CoeffIndex)
  let P' : Ideal R := P.map (MvPolynomial.map (Polynomial.C : Geom →+* Geom[X]))
  have heC : e.toRingHom.comp (MvPolynomial.map (Polynomial.C : Geom →+* Geom[X])) =
      (Polynomial.C : CoeffRing →+* CoeffRing[X]) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change e (MvPolynomial.map Polynomial.C (MvPolynomial.C a)) = _
      rw [MvPolynomial.map_C]
      change optionEquivLeft Geom CoeffIndex
        ((optionEquivRight Geom CoeffIndex).symm (MvPolynomial.C (Polynomial.C a))) = _
      rw [← optionEquivRight_C, AlgEquiv.symm_apply_apply, optionEquivLeft_C]
    · intro a
      change e (MvPolynomial.map Polynomial.C (MvPolynomial.X a)) = _
      rw [MvPolynomial.map_X]
      change optionEquivLeft Geom CoeffIndex
        ((optionEquivRight Geom CoeffIndex).symm (MvPolynomial.X a)) = _
      rw [← optionEquivRight_X_some, AlgEquiv.symm_apply_apply, optionEquivLeft_X_some]
  have heP : P'.map e.toRingHom = P.map (Polynomial.C : CoeffRing →+* CoeffRing[X]) := by
    rw [show P' = P.map _ from rfl, Ideal.map_map, heC]
  have hP' : P'.IsPrime := by
    have hmap := (Ideal.isPrime_map_C_iff_isPrime P).2 hP
    rw [← heP] at hmap
    have := hmap
    rw [← Ideal.comap_map_of_bijective (I := P') e.toRingHom e.bijective]
    exact Ideal.comap_isPrime e.toRingHom _
  let M : Submonoid R := (nonZeroDivisors Geom[X]).map (MvPolynomial.C (σ := CoeffIndex))
  have hdisj : Disjoint (M : Set R) (P' : Set R) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ hp
    have hmem := Ideal.mem_map_of_mem e.toRingHom hp
    rw [heP, Ideal.mem_map_C_iff] at hmem
    have heS : e.toRingHom (MvPolynomial.C s) =
        Polynomial.map (MvPolynomial.C : Geom →+* CoeffRing) s := by
      have he' : e.toRingHom.comp (MvPolynomial.C : Geom[X] →+* R) =
          Polynomial.mapRingHom (MvPolynomial.C : Geom →+* CoeffRing) := by
        apply Polynomial.ringHom_ext
        · intro a
          change e (MvPolynomial.C (Polynomial.C a)) = _
          change optionEquivLeft Geom CoeffIndex
            ((optionEquivRight Geom CoeffIndex).symm (MvPolynomial.C (Polynomial.C a))) = _
          rw [← optionEquivRight_C, AlgEquiv.symm_apply_apply, optionEquivLeft_C]
          simp
        · change e (MvPolynomial.C Polynomial.X) = _
          change optionEquivLeft Geom CoeffIndex
            ((optionEquivRight Geom CoeffIndex).symm (MvPolynomial.C Polynomial.X)) = _
          rw [← optionEquivRight_X_none, AlgEquiv.symm_apply_apply, optionEquivLeft_X_none]
          simp
      exact DFunLike.congr_fun he' s
    have hi : s.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (nonZeroDivisors.ne_zero hs)
    have hconst := hmem s.natDegree
    rw [heS, Polynomial.coeff_map] at hconst
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hconst (IsUnit.map _ (isUnit_iff_ne_zero.mpr hi)))
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint M FreshCoeffRing P' hP' hdisj
  have hext : P'.map (algebraMap R FreshCoeffRing) = freshIdeal P := by
    change (P.map _).map (MvPolynomial.map (algebraMap Geom[X] FreshField)) = _
    rw [Ideal.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      rfl
    · simp
  exact hext ▸ hprime

private theorem dimension_le_of_recovery {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]
    {I : Ideal (MvPolynomial σ F)} {J : Ideal (MvPolynomial τ F)}
    {s : MvPolynomial σ F} {t : MvPolynomial τ F}
    (φ : (MvPolynomial σ F ⧸ I) →ₐ[F] (MvPolynomial τ F ⧸ J))
    (ht : φ (Ideal.Quotient.mk I s) = Ideal.Quotient.mk J t)
    (hreg : IsLeftRegular (Ideal.Quotient.mk J t))
    (hrec : ∀ x, ∃ q m, φ q = φ (Ideal.Quotient.mk I s) ^ m * x) :
    (affineHilbertPolynomial J).natDegree ≤ (affineHilbertPolynomial I).natDegree := by
  let a := Ideal.Quotient.mk I s
  let A := Localization.Away a
  let B := Localization.Away (Ideal.Quotient.mk J t)
  have : IsLocalization.Away (φ a) B := by
    change IsLocalization.Away (φ (Ideal.Quotient.mk I s)) B
    rw [ht]
    infer_instance
  let ψ : A →ₐ[F] B := IsLocalization.Away.mapₐ (R := F) A B φ a
  have hψ : Function.Surjective ψ :=
    (IsLocalization.Away.map_surjective_iff A B φ.toRingHom a).2 hrec
  exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away hreg ψ hψ

/-- The recovered coordinates give a surjection on the two principal opens.
Together with injectivity on the quotients this identifies their Hilbert dimensions. -/
theorem chart_dimension (P : Ideal CoeffRing) (g d : FreshJetRing) (h : FreshChart P g d) :
    (affineHilbertPolynomial P).natDegree = 2 := by
  let J : Ideal FreshJetRing := Ideal.span {g}
  let A := FreshJetRing ⧸ J
  let B := FreshCoeffRing ⧸ freshIdeal P
  let φ : A →ₐ[FreshField] B := Ideal.quotientMapₐ _ freshProjection h.image.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' (H := h.image.ge) h.image.le
  let a : A := Ideal.Quotient.mk J d
  let b : B := φ a
  have hneq : Ideal.Quotient.mk (freshIdeal P) (freshProjection d) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun hd => h.regular_open (h.image ▸ hd)
  have := freshIdeal_isPrime P h.prime
  have hb : IsLeftRegular (Ideal.Quotient.mk (freshIdeal P) (freshProjection d)) :=
    (IsRegular.of_ne_zero hneq).1
  have hrecover (f : FreshCoeffRing) : ∃ q : A, ∃ m : ℕ,
      φ q = b ^ m * Ideal.Quotient.mk (freshIdeal P) f := by
    induction f using MvPolynomial.induction_on with
    | C c =>
      refine ⟨algebraMap FreshField A c, 0, ?_⟩
      simpa only [AlgHom.commutes, pow_zero, one_mul] using
        (show algebraMap FreshField B c = Ideal.Quotient.mk (freshIdeal P) (MvPolynomial.C c) from rfl)
    | add f r hf hr =>
      obtain ⟨u, m, hu⟩ := hf
      obtain ⟨v, n, hv⟩ := hr
      refine ⟨a ^ n * u + a ^ m * v, m + n, ?_⟩
      simp only [map_add, map_mul, map_pow, hu, hv, ← show b = φ a from rfl, pow_add]
      ring
    | mul_X f i hf =>
      obtain ⟨u, m, hu⟩ := hf
      obtain ⟨v, n, hv⟩ := h.recover i
      have hv' : φ (Ideal.Quotient.mk J v) =
          b ^ n * Ideal.Quotient.mk (freshIdeal P) (MvPolynomial.X i) := by
        have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hv
        simp only [map_sub, map_mul, map_pow, sub_eq_zero] at hz
        exact hz.symm
      refine ⟨u * Ideal.Quotient.mk J v, m + n, ?_⟩
      simp only [map_mul, hu, hv', pow_add]
      ring
  have hle := natDegree_affineHilbertPolynomial_le_of_injective φ hφ
  have hge : (affineHilbertPolynomial (freshIdeal P)).natDegree ≤ (affineHilbertPolynomial J).natDegree := by
    apply dimension_le_of_recovery (s := d) (t := freshProjection d) φ rfl hb
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hrecover f
  have hJ : (affineHilbertPolynomial J).natDegree = 2 := by
    have hproper : J ≠ ⊤ := by
      intro htop
      apply h.regular_open
      change d ∈ J
      simp [htop]
    have heq := natDegree_affineHilbertPolynomial_span_singleton_add_one h.equation_ne hproper
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at heq
    change (affineHilbertPolynomial J).natDegree + 1 = 3 at heq
    omega
  rw [← hilbertPolynomial_map (E := FreshField) P]
  exact (le_antisymm hge hle).trans hJ

end

end K1_13_5_5_2
end PackSource_K1_13_5_5_2Dimension

section PackSource_K1_14_2_4_1_3Split
set_option autoImplicit true
namespace K1_14_2_4_1_3

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 MvPolynomial

/-- The independent parameter and ordinate equations avoid the boundary of the
projective coefficient image. -/
def c1 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n),
    (affineHilbertPolynomial (coefficientIdeal A)).natDegree ≤ 1 →
    RegularLinearCut (extendedIdeal (SliceField n) (coefficientIdeal A)) (coefficientCut n) ∧
      RegularLinearCut (extendedIdeal SeedField (coefficientIdeal A)) (ordinateForm A.equation)

/-- Retaining the seed coordinates in a generic parameter section restores the
function-field degree over the coefficient image. -/
def c2 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n),
    Module.Finite (SliceField n) (CoefficientSection A) →
    Module.Finite (SliceField n) (BaseSection (chartBase A)) ∧
      Module.finrank (SliceField n) (BaseSection (chartBase A)) ≤
        seedDegree A * Module.finrank (SliceField n) (CoefficientSection A)

/-- Primitivity in X rules out ordinate length on a vertical component, so the
original root fibre pays the coefficient ordinate length with its seed degree. -/
def c3 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n),
    0 < g → Module.Finite SeedField (RootYSection J) →
    Module.Finite SeedField (OrdinateSection A) →
    seedDegree A * Module.finrank SeedField (OrdinateSection A) ≤
      Module.finrank SeedField (RootYSection J)

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_14_2_4_1.c3 := by
  intro C₀ _ J g H n R A hg hroot hH
  obtain ⟨hdBase, hdCoeff⟩ := chart_dimension A
  obtain ⟨hparam, hord⟩ := h1 C₀ J g n R A hdCoeff
  have hp : affineHilbertPolynomial (extendedIdeal (SliceField n) (coefficientIdeal A)) =
      affineHilbertPolynomial (coefficientIdeal A) :=
    K1_13_5_5_2.hilbertPolynomial_map _
  have hy : affineHilbertPolynomial (extendedIdeal SeedField (coefficientIdeal A)) =
      affineHilbertPolynomial (coefficientIdeal A) :=
    K1_13_5_5_2.hilbertPolynomial_map _
  have hpdim : (affineHilbertPolynomial (extendedIdeal (SliceField n) (coefficientIdeal A))).natDegree
      ≤ 1 := by rwa [hp]
  have hydim : (affineHilbertPolynomial (extendedIdeal SeedField (coefficientIdeal A))).natDegree
      ≤ 1 := by rwa [hy]
  obtain ⟨hpf, hplen⟩ := length_of_regularLinearCut hpdim hparam
  obtain ⟨hyf, hylen⟩ := length_of_regularLinearCut hydim hord
  have hlen : Module.finrank (SliceField n) (CoefficientSection A) =
      Module.finrank SeedField (OrdinateSection A) := by
    rw [hp] at hplen
    rw [hy] at hylen
    exact_mod_cast hplen.trans hylen.symm
  obtain ⟨hfin, hbudget⟩ := h2 C₀ J g n R A hpf
  refine ⟨hdBase, hfin, hbudget.trans ?_⟩
  rw [hlen]
  exact (h3 C₀ J g n R A hg hroot hyf).trans hH

end
end K1_14_2_4_1_3
end PackSource_K1_14_2_4_1_3Split

section PackSource_K1_14_2_4_1_3_2Defs
set_option autoImplicit true
set_option maxHeartbeats 600000

namespace K1_14_2_4_1_3_2

noncomputable section

section OffsetLocalization

set_option linter.unusedSectionVars false

open MvPolynomial
open scoped nonZeroDivisors

abbrev WeightRing (k : Type*) [CommRing k] (n : ℕ) :=
  MvPolynomial (Option (Fin n)) k

variable {k σ S : Type*} [CommRing k] {n : ℕ}
variable [CommRing S] [Algebra k S] [Algebra (WeightRing k n) S]
variable [IsScalarTower k (WeightRing k n) S] [IsFractionRing (WeightRing k n) S]

/-- The parameter ideal after substituting the weighted coordinate sum for the offset. -/
abbrev WeightedRing (I : Ideal (MvPolynomial σ k)) :=
  MvPolynomial (Fin n) (MvPolynomial σ k ⧸ I)

def weightedOffset (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    WeightedRing (n := n) I :=
  ∑ i, MvPolynomial.X i * C (Ideal.Quotient.mk I (MvPolynomial.X (j i)))

def substitute (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    WeightRing k n →+* WeightedRing (n := n) I :=
  eval₂Hom (C.comp ((Ideal.Quotient.mk I).comp C)) (fun i =>
    i.elim (weightedOffset I j) MvPolynomial.X)

abbrev substitutedDenominators (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    Submonoid (WeightedRing (n := n) I) :=
  (WeightRing k n)⁰ |>.map (substitute I j).toMonoidHom

abbrev LocalizedWeights (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :=
  Localization (M := WeightedRing (n := n) I) (substitutedDenominators I j)

instance localizedWeightsCommRing (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    CommRing (LocalizedWeights I j) :=
  @OreLocalization.instCommRing (WeightedRing (n := n) I) inferInstance
    (substitutedDenominators I j) inferInstance

private def locScalars (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    S →+* LocalizedWeights I j :=
  IsLocalization.lift (M := (WeightRing k n)⁰)
    (g := (algebraMap _ (LocalizedWeights I j)).comp (substitute I j))
    (fun y => IsLocalization.map_units (M := substitutedDenominators I j)
      (LocalizedWeights I j) ⟨substitute I j y, y, y.property, rfl⟩)

instance localizedWeightsAlgebra (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    Algebra S (LocalizedWeights I j) := (locScalars I j).toAlgebra

theorem localizedWeights_scalar (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ)
    (r : WeightRing k n) :
    algebraMap S (LocalizedWeights I j) (algebraMap (WeightRing k n) S r) =
      algebraMap (WeightedRing (n := n) I) (LocalizedWeights I j) (substitute I j r) :=
  IsLocalization.lift_eq _ _

abbrev weight (i : Option (Fin n)) : S :=
  algebraMap (WeightRing k n) S (MvPolynomial.X i)

def genericCut (j : Fin n → σ) : MvPolynomial σ S :=
  (∑ i, C (weight (k := k) (S := S) (some i)) * MvPolynomial.X (j i)) - C (weight (k := k) (S := S) (n := n) none)

abbrev cutIdeal (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    Ideal (MvPolynomial σ S) :=
  I.map (MvPolynomial.map (algebraMap k S)) ⊔ Ideal.span {genericCut (k := k) j}

abbrev GenericSection (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :=
  MvPolynomial σ S ⧸ cutIdeal (S := S) I j

private def coordToSection (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    (MvPolynomial σ k ⧸ I) →+* GenericSection (S := S) I j :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap k S)))
    (fun _p hp => Ideal.Quotient.eq_zero_iff_mem.mpr
      (show _ ∈ cutIdeal (S := S) I j from
        (le_sup_left : I.map _ ≤ cutIdeal (S := S) I j) (Ideal.mem_map_of_mem _ hp)))

private def weightsToSection (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    WeightedRing (n := n) I →+* GenericSection (S := S) I j :=
  eval₂Hom (coordToSection I j) (fun i => algebraMap S _ (weight (k := k) (some i)))

private theorem weightsToSection_compat (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    (weightsToSection (S := S) I j).comp (substitute I j) =
      (algebraMap S (GenericSection (S := S) I j)).comp (algebraMap (WeightRing k n) S) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, substitute, eval₂Hom_C, weightsToSection,
      coordToSection, Ideal.Quotient.lift_mk, MvPolynomial.map_C]
    change _ = algebraMap S (GenericSection (S := S) I j)
      (algebraMap (WeightRing k n) S (algebraMap k (WeightRing k n) a))
    rw [← IsScalarTower.algebraMap_apply k (WeightRing k n) S]
    rfl
  · intro i
    cases i with
    | some i => simp [substitute, weightsToSection]
    | none =>
      have hz : Ideal.Quotient.mk (cutIdeal (S := S) I j) (genericCut (k := k) j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ((le_sup_right : Ideal.span {genericCut (k := k) j} ≤ cutIdeal (S := S) I j)
          (Ideal.mem_span_singleton_self _))
      simp only [genericCut, map_sub, map_sum, map_mul, sub_eq_zero] at hz
      simp only [RingHom.comp_apply, substitute, eval₂Hom_X', Option.elim_none,
        weightedOffset, weightsToSection, map_sum, map_mul, eval₂Hom_C, coordToSection,
        Ideal.Quotient.lift_mk, MvPolynomial.map_X]
      exact hz

private def localizedToSection (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    LocalizedWeights I j →+* GenericSection (S := S) I j :=
  IsLocalization.lift (M := substitutedDenominators I j)
    (g := weightsToSection (S := S) I j) (by
      rintro ⟨_, r, hr, rfl⟩
      have h := DFunLike.congr_fun (weightsToSection_compat (S := S) I j) r
      change weightsToSection I j (substitute I j r) =
        algebraMap S _ (algebraMap (WeightRing k n) S r) at h
      change IsUnit (weightsToSection (S := S) I j (substitute I j r))
      rw [h]
      exact (IsLocalization.map_units S (⟨r, hr⟩ : (WeightRing k n)⁰)).map (algebraMap S _))

private theorem localizedToSection_scalar (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    (localizedToSection (S := S) I j).comp (algebraMap S (LocalizedWeights I j)) =
      algebraMap S (GenericSection (S := S) I j) := by
  apply IsLocalization.ringHom_ext (M := (WeightRing k n)⁰)
  apply RingHom.ext
  intro r
  have h := DFunLike.congr_fun (weightsToSection_compat (S := S) I j) r
  simpa [RingHom.comp_apply, localizedWeights_scalar, localizedToSection,
    IsLocalization.lift_eq] using h

private def polynomialToLocalized (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    MvPolynomial σ S →+* LocalizedWeights I j :=
  eval₂Hom (algebraMap S _) (fun i => algebraMap (WeightedRing (n := n) I) _
    (C (Ideal.Quotient.mk I (MvPolynomial.X i))))

private theorem polynomialToLocalized_coeff (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    (polynomialToLocalized (S := S) I j).comp (MvPolynomial.map (algebraMap k S)) =
      (algebraMap (WeightedRing (n := n) I) _).comp (C.comp (Ideal.Quotient.mk I)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, MvPolynomial.map_C, polynomialToLocalized, eval₂Hom_C]
    rw [IsScalarTower.algebraMap_apply k (WeightRing k n) S, localizedWeights_scalar]
    simp [substitute]
  · simp [polynomialToLocalized]

private def sectionToLocalized (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    GenericSection (S := S) I j →+* LocalizedWeights I j :=
  Ideal.Quotient.lift _ (polynomialToLocalized (S := S) I j) (by
    apply show cutIdeal (S := S) I j ≤ RingHom.ker (polynomialToLocalized (S := S) I j) from ?_
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro r hr
      change (polynomialToLocalized (S := S) I j).comp (MvPolynomial.map (algebraMap k S)) r = 0
      rw [polynomialToLocalized_coeff]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    · intro r hr
      obtain rfl := Set.mem_singleton_iff.mp hr
      change polynomialToLocalized (S := S) I j (genericCut (k := k) j) = 0
      rw [genericCut, map_sub, sub_eq_zero]
      rw [map_sum (polynomialToLocalized (S := S) I j)]
      simp only [map_mul]
      simp only [polynomialToLocalized, eval₂Hom_C, eval₂Hom_X', weight,
        localizedWeights_scalar, substitute, Option.elim_none, Option.elim_some,
        weightedOffset, map_sum, map_mul])

private theorem localized_left_inv (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    (sectionToLocalized (S := S) I j).comp (localizedToSection (S := S) I j) =
      RingHom.id (LocalizedWeights I j) := by
  apply IsLocalization.ringHom_ext (M := substitutedDenominators I j)
  simp only [RingHom.comp_assoc, localizedToSection, IsLocalization.lift_comp,
    RingHom.id_comp]
  apply MvPolynomial.ringHom_ext
  · intro r
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h := DFunLike.congr_fun (polynomialToLocalized_coeff (S := S) I j) p
    simp only [weightsToSection, coordToSection, RingHom.comp_apply,
      eval₂Hom_C, Ideal.Quotient.lift_mk]
    change polynomialToLocalized (S := S) I j (MvPolynomial.map (algebraMap k S) p) = _
    exact h
  · intro i
    simp only [RingHom.comp_apply, weightsToSection, eval₂Hom_X']
    change polynomialToLocalized (S := S) I j (C (weight (k := k) (some i))) =
      algebraMap (WeightedRing (n := n) I) _ (MvPolynomial.X i)
    simp [polynomialToLocalized, localizedWeights_scalar, substitute]

private theorem localized_right_inv (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    (localizedToSection (S := S) I j).comp (sectionToLocalized (S := S) I j) =
      RingHom.id (GenericSection (S := S) I j) := by
  apply RingHom.ext
  intro r
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h : (localizedToSection (S := S) I j).comp (polynomialToLocalized (S := S) I j) =
      Ideal.Quotient.mk (cutIdeal (S := S) I j) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change localizedToSection (S := S) I j (polynomialToLocalized I j (C a)) =
        algebraMap S (GenericSection (S := S) I j) a
      simpa only [polynomialToLocalized, eval₂Hom_C, RingHom.comp_apply] using
        DFunLike.congr_fun (localizedToSection_scalar (S := S) I j) a
    · intro i
      simp [polynomialToLocalized, localizedToSection, IsLocalization.lift_eq,
        weightsToSection, coordToSection]
  exact DFunLike.congr_fun h p

/-- Eliminating the free offset identifies the cut with localization at the
substituted nonzero parameter polynomials. This includes the zero ring. -/
def genericSectionEquiv (I : Ideal (MvPolynomial σ k)) (j : Fin n → σ) :
    GenericSection (S := S) I j ≃ₐ[S] LocalizedWeights I j where
  __ := RingEquiv.ofRingHom (sectionToLocalized (S := S) I j) (localizedToSection (S := S) I j)
    (localized_left_inv I j) (localized_right_inv I j)
  commutes' a := by
    change polynomialToLocalized (S := S) I j (C a) = _
    simp [polynomialToLocalized]

end OffsetLocalization

section RationalWeights

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open MvPolynomial
open scoped Polynomial nonZeroDivisors

abbrev RationalWeightRing (E : Type) [Field E] (n : ℕ) :=
  MvPolynomial (Fin n) (FractionRing E[X])

abbrev RationalWeightField (E : Type) [Field E] (n : ℕ) :=
  FractionRing (RationalWeightRing E n)

/-- Extend a constant-field embedding across the free abscissa. -/
def abscissaMap {E F : Type} [Field E] [Field F] (f : E →+* F) :
    FractionRing E[X] →+* FractionRing F[X] :=
  IsFractionRing.map (j := Polynomial.mapRingHom f) (Polynomial.map_injective f f.injective)

theorem abscissaMap_comp {E F G : Type} [Field E] [Field F] [Field G]
    (f : E →+* F) (g : F →+* G) :
    (abscissaMap g).comp (abscissaMap f) = abscissaMap (g.comp f) := by
  apply IsFractionRing.ringHom_ext (A := E[X])
  intro p
  simp [abscissaMap, IsFractionRing.map, IsLocalization.map_eq, Polynomial.map_map]

abbrev rationalConstant {E : Type} [Field E] (a : E) : FractionRing E[X] :=
  algebraMap E[X] (FractionRing E[X]) (Polynomial.C a)

/-- Evaluate the offset at the weighted sum while leaving the weights and X independent. -/
def parameterEval {E : Type} [Field E] {n : ℕ} (f : L →+* E) (a : Fin n → E) :
    SourceRing n →+* RationalWeightRing E n :=
  eval₂Hom (C.comp (abscissaMap f))
    (fun i => i.elim (∑ j, MvPolynomial.X j * C (rationalConstant (a j))) MvPolynomial.X)

theorem parameterEval_comp {E F : Type} [Field E] [Field F] {n : ℕ}
    (f : L →+* E) (g : E →+* F) (a : Fin n → E) :
    (MvPolynomial.map (abscissaMap g)).comp (parameterEval f a) =
      parameterEval (g.comp f) (g ∘ a) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, parameterEval, eval₂Hom_C, MvPolynomial.map_C]
    exact congrArg C (DFunLike.congr_fun (abscissaMap_comp f g) r)
  · intro i
    cases i with
    | some i => simp [parameterEval]
    | none =>
      simp only [RingHom.comp_apply, parameterEval, eval₂Hom_X', Option.elim_none,
        map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, abscissaMap,
        IsFractionRing.map, IsLocalization.map_eq, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Function.comp_apply]

abbrev CoefficientField {E : Type} [Field E] [Algebra L E] {n : ℕ} (a : Fin n → E) :=
  IntermediateField.adjoin L (Set.range a)

def coefficientTuple {E : Type} [Field E] [Algebra L E] {n : ℕ} (a : Fin n → E) :
    Fin n → CoefficientField a :=
  fun i => ⟨a i, IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩

abbrev coefficientParameter {E : Type} [Field E] [Algebra L E] {n : ℕ} (a : Fin n → E) :=
  parameterEval (algebraMap L (CoefficientField a)) (coefficientTuple a)

theorem coefficientParameter_injective {E : Type} [Field E] [Algebra L E] {n : ℕ}
    (a : Fin n → E) (h : Function.Injective (parameterEval (algebraMap L E) a)) :
    Function.Injective (coefficientParameter a) := by
  let F := CoefficientField a
  let g : F →+* E := F.val.toRingHom
  have he : (MvPolynomial.map (abscissaMap g)).comp (coefficientParameter a) =
      parameterEval (algebraMap L E) a := by
    rw [coefficientParameter, parameterEval_comp]
    rfl
  have hi : Function.Injective ((MvPolynomial.map (abscissaMap g)).comp (coefficientParameter a)) :=
    he.symm ▸ h
  intro x y hxy
  apply hi
  exact congrArg (MvPolynomial.map (abscissaMap g)) hxy

/-- The scalar structure on the rational function field of a dominant parameter cut. -/
abbrev sliceAlgebra {E : Type} [Field E] {n : ℕ} (f : SourceRing n →+* RationalWeightRing E n)
    (hf : Function.Injective f) : Algebra (SliceField n) (RationalWeightField E n) :=
  (IsFractionRing.map (j := f) hf).toAlgebra

theorem sliceAlgebra_apply {E : Type} [Field E] {n : ℕ} (f : SourceRing n →+* RationalWeightRing E n)
    (hf : Function.Injective f) (r : SourceRing n) :
    @algebraMap (SliceField n) (RationalWeightField E n) _ _ (sliceAlgebra f hf)
        (algebraMap (SourceRing n) (SliceField n) r) =
      algebraMap (RationalWeightRing E n) (RationalWeightField E n) (f r) :=
  IsLocalization.map_eq (M := (SourceRing n)⁰) (T := (RationalWeightRing E n)⁰)
    (g := f) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf) r

end RationalWeights

section SeedGraph

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
open MvPolynomial
open scoped nonZeroDivisors

variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
variable {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n)

private def graphWeights :
    WeightedRing (n := n) (chartBase A) →+* RationalWeightRing (ConstantSeedField C₀) n :=
  MvPolynomial.map (RingHom.kerLift (chartBaseMap A))

private theorem graphWeights_injective : Function.Injective (graphWeights A) :=
  MvPolynomial.map_injective _ (RingHom.kerLift_injective (chartBaseMap A))

private theorem graphWeights_X (i : Fin n) :
    graphWeights A (MvPolynomial.X i) = MvPolynomial.X i :=
  MvPolynomial.map_X _ _

private theorem graphWeights_C (p : ChartBaseRing n) :
    graphWeights A (C (Ideal.Quotient.mk (chartBase A) p)) = C (chartBaseMap A p) :=
  MvPolynomial.map_C _ _

private theorem graph_substitute :
    (graphWeights A).comp (substitute (chartBase A) Sum.inr) =
      parameterEval (constToSeed C₀) A.coordinate := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, substitute, parameterEval, eval₂Hom_C, graphWeights_C,
      chartBaseMap]
    rfl
  · intro i
    cases i with
    | some i =>
      simp only [RingHom.comp_apply, substitute, parameterEval, eval₂Hom_X', Option.elim_some,
        graphWeights_X]
    | none =>
      simp only [RingHom.comp_apply, substitute, parameterEval, eval₂Hom_X', Option.elim_none,
        weightedOffset]
      rw [map_sum (graphWeights A)]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, graphWeights_X, graphWeights_C]
      simp only [chartBaseMap, eval₂Hom_X', Sum.elim_inr, Function.comp_apply]
      rfl

private def graphEquiv :
    BaseSection (chartBase A) ≃ₐ[SliceField n] LocalizedWeights (chartBase A) Sum.inr :=
  genericSectionEquiv (k := FX) (S := SliceField n) (chartBase A) Sum.inr

/-- If the free offset has a relation over the parameter polynomial ring, its
nonzero relation becomes invertible and the graph cut is empty. -/
theorem graph_subsingleton (h : ¬ Function.Injective
    (parameterEval (constToSeed C₀) A.coordinate)) :
    Subsingleton (BaseSection (chartBase A)) := by
  classical
  have hker : ¬ ∀ p : SourceRing n,
      parameterEval (constToSeed C₀) A.coordinate p = 0 → p = 0 :=
    fun hk => h ((injective_iff_map_eq_zero _).mpr hk)
  obtain ⟨p, hp⟩ := not_forall.mp hker
  obtain ⟨hz, hp⟩ := not_imp.mp hp
  have hsub : substitute (chartBase A) Sum.inr p = 0 := by
    apply graphWeights_injective A
    rw [map_zero, ← RingHom.comp_apply, graph_substitute, hz]
  let d : substitutedDenominators (chartBase A) Sum.inr :=
    ⟨substitute (chartBase A) Sum.inr p, p, mem_nonZeroDivisors_iff_ne_zero.mpr hp, rfl⟩
  have hu := IsLocalization.map_units (M := substitutedDenominators (chartBase A) Sum.inr)
    (LocalizedWeights (chartBase A) Sum.inr) d
  change IsUnit (algebraMap _ _ (substitute (chartBase A) Sum.inr p)) at hu
  rw [hsub, map_zero] at hu
  let : Subsingleton (LocalizedWeights (chartBase A) Sum.inr) :=
    subsingleton_iff_zero_eq_one.mp (isUnit_zero_iff.mp hu)
  exact (graphEquiv A).injective.subsingleton

/-- On the dominant branch the localized graph embeds in the rational field
obtained from the seed function field by adjoining X and the weights. -/
theorem graph_embedding (h : Function.Injective
    (parameterEval (constToSeed C₀) A.coordinate)) :
    letI := sliceAlgebra (parameterEval (constToSeed C₀) A.coordinate) h
    ∃ f : BaseSection (chartBase A) →ₐ[SliceField n]
      RationalWeightField (ConstantSeedField C₀) n, Function.Injective f := by
  let := sliceAlgebra (parameterEval (constToSeed C₀) A.coordinate) h
  let B := WeightedRing (n := n) (chartBase A)
  let T := LocalizedWeights (chartBase A) Sum.inr
  let E := RationalWeightField (ConstantSeedField C₀) n
  let M := substitutedDenominators (chartBase A) Sum.inr
  let q : B →+* E := (algebraMap (RationalWeightRing (ConstantSeedField C₀) n) E).comp
    (graphWeights A)
  have hq : Function.Injective q := by
    intro x y hxy
    apply graphWeights_injective A
    exact IsFractionRing.injective (RationalWeightRing (ConstantSeedField C₀) n) E hxy
  have hu (p : M) : IsUnit (q p) := by
    obtain ⟨d, hd, hd'⟩ := p.property
    change substitute (chartBase A) Sum.inr d = (p : B) at hd'
    rw [← hd']
    change IsUnit ((algebraMap (RationalWeightRing (ConstantSeedField C₀) n) E)
      (graphWeights A (substitute (chartBase A) Sum.inr d)))
    have hs : graphWeights A (substitute (chartBase A) Sum.inr d) =
        parameterEval (constToSeed C₀) A.coordinate d :=
      DFunLike.congr_fun (graph_substitute A) d
    rw [hs]
    suffices hn : algebraMap (RationalWeightRing (ConstantSeedField C₀) n) E
        (parameterEval (constToSeed C₀) A.coordinate d) ≠ 0 from hn.isUnit
    intro hz
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hd)
    apply h
    apply IsFractionRing.injective (RationalWeightRing (ConstantSeedField C₀) n) E
    simpa only [map_zero] using hz
  let e : T →+* E := IsLocalization.lift hu
  have he : Function.Injective e := by
    apply (IsLocalization.lift_injective_iff hu).mpr
    intro x y
    exact ⟨fun hxy => by
      obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := M) hxy
      exact (hu d).mul_left_cancel (by rw [← map_mul, ← map_mul, hd]),
      fun hxy => congrArg (algebraMap B T) (hq hxy)⟩
  have hc : e.comp (algebraMap (SliceField n) T) = algebraMap (SliceField n) E := by
    apply IsLocalization.ringHom_ext (M := (SourceRing n)⁰)
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply]
    have hs := localizedWeights_scalar (S := SliceField n) (chartBase A) Sum.inr p
    rw [hs]
    have hl : e (algebraMap B T (substitute (chartBase A) Sum.inr p)) =
        q (substitute (chartBase A) Sum.inr p) :=
      IsLocalization.lift_eq hu _
    rw [hl, sliceAlgebra_apply]
    exact congrArg (algebraMap (RationalWeightRing (ConstantSeedField C₀) n) E)
      (DFunLike.congr_fun (graph_substitute A) p)
  let φ : T →ₐ[SliceField n] E := ⟨e, DFunLike.congr_fun hc⟩
  exact ⟨φ.comp (graphEquiv A).toAlgHom, he.comp (graphEquiv A).injective⟩

end SeedGraph

end

end K1_14_2_4_1_3_2
end PackSource_K1_14_2_4_1_3_2Defs

section PackSource_K1_14_2_4_1_3_2Split
set_option autoImplicit true
set_option maxHeartbeats 600000

namespace K1_14_2_4_1_3_2

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_3

/-- A finite coefficient section covers the function field of the coefficient image
with the independent abscissa and weights adjoined. -/
def c1 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n)
    (h : Function.Injective (parameterEval (constToSeed C₀) A.coordinate)),
    letI : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
    letI := sliceAlgebra (coefficientParameter A.coordinate)
      (coefficientParameter_injective A.coordinate h)
    Module.Finite (SliceField n) (CoefficientSection A) →
    ∃ f : CoefficientSection A →ₐ[SliceField n]
      RationalWeightField (CoefficientField A.coordinate) n, Function.Surjective f

/-- A dominant parameter map retains the finite seed mapping degree after adjoining
the same independent abscissa and weights to both function fields. -/
def c2 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n)
    (h : Function.Injective (parameterEval (constToSeed C₀) A.coordinate)),
    letI : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
    letI := sliceAlgebra (coefficientParameter A.coordinate)
      (coefficientParameter_injective A.coordinate h)
    letI := sliceAlgebra (parameterEval (constToSeed C₀) A.coordinate) h
    ∃ i : RationalWeightField (CoefficientField A.coordinate) n →ₐ[SliceField n]
        RationalWeightField (ConstantSeedField C₀) n,
      letI := i.toRingHom.toAlgebra
      Module.Finite (RationalWeightField (CoefficientField A.coordinate) n)
          (RationalWeightField (ConstantSeedField C₀) n) ∧
        Module.finrank (RationalWeightField (CoefficientField A.coordinate) n)
          (RationalWeightField (ConstantSeedField C₀) n) ≤ seedDegree A

private theorem transfer_rank {S B C F E : Type} [Field S] [CommRing B] [CommRing C]
    [Field F] [Field E] [Algebra S B] [Algebra S C] [aF : Algebra S F] [aE : Algebra S E]
    (hC : Module.Finite S C) (f : C →ₐ[S] F) (hf : Function.Surjective f)
    (j : B →ₐ[S] E) (hj : Function.Injective j) (i : F →ₐ[S] E) {d : ℕ}
    (hi : letI := i.toRingHom.toAlgebra
      Module.Finite F E ∧ Module.finrank F E ≤ d) :
    Module.Finite S B ∧ Module.finrank S B ≤ d * Module.finrank S C := by
  let := i.toRingHom.toAlgebra
  have : IsScalarTower S F E := IsScalarTower.of_algHom i
  have : Module.Finite S C := hC
  have : Module.Finite S F := Module.Finite.of_surjective f.toLinearMap hf
  have : Module.Finite F E := hi.1
  have : Module.Finite S E := Module.Finite.trans F E
  refine ⟨Module.Finite.of_injective j.toLinearMap hj, ?_⟩
  calc
    Module.finrank S B ≤ Module.finrank S E := j.toLinearMap.finrank_le_finrank_of_injective hj
    _ = Module.finrank S F * Module.finrank F E := (Module.finrank_mul_finrank S F E).symm
    _ ≤ d * Module.finrank S C := by
      rw [mul_comm (Module.finrank S F)]
      exact Nat.mul_le_mul hi.2 (f.toLinearMap.finrank_le_finrank_of_surjective hf)

theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_4_1_3.c2 := by
  intro C₀ _ J g n R A hfinite
  classical
  by_cases h : Function.Injective (parameterEval (constToSeed C₀) A.coordinate)
  · let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
    let coeffScalars := sliceAlgebra (coefficientParameter A.coordinate)
      (coefficientParameter_injective A.coordinate h)
    let seedScalars := sliceAlgebra (parameterEval (constToSeed C₀) A.coordinate) h
    obtain ⟨f, hf⟩ := h1 C₀ J g n R A h hfinite
    obtain ⟨i, hi⟩ := h2 C₀ J g n R A h
    obtain ⟨j, hj⟩ := graph_embedding A h
    exact transfer_rank (S := SliceField n) (B := BaseSection (chartBase A))
      (C := CoefficientSection A) (F := RationalWeightField (CoefficientField A.coordinate) n)
      (E := RationalWeightField (ConstantSeedField C₀) n)
      (aF := coeffScalars) (aE := seedScalars) hfinite f hf j hj i hi
  · have : Subsingleton (BaseSection (chartBase A)) := graph_subsingleton A h
    exact ⟨inferInstance, by simp [Module.finrank_zero_of_subsingleton]⟩

end

end K1_14_2_4_1_3_2
end PackSource_K1_14_2_4_1_3_2Split

section PackSource_K1_14_2_4_1_3_2_2Proof
set_option autoImplicit true
namespace K1_14_2_4_1_3_2_2

noncomputable section

open Algebra MvPolynomial K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1
  K1_14_2_4_1_3 K1_14_2_4_1_3_2
open scoped Polynomial BigOperators nonZeroDivisors

set_option maxHeartbeats 600000

private theorem trdeg_fraction (k B : Type) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] : trdeg k (FractionRing B) = trdeg k B := by
  let : Algebra.IsAlgebraic B (FractionRing B) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing B)).mpr inferInstance
  rw [← trdeg_add_eq k B, trdeg_eq_zero (R := B), add_zero]

private theorem trdeg_normalization {k B : Type} [Field k] [CommRing B] [IsDomain B]
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
  rw [trdeg_fraction L B, trdeg_normalization u hu hfin]
  exact_mod_cast hdim

private theorem abscissaMap_constant {F E : Type} [Field F] [Field E] (f : F →+* E)
    (a : F) : abscissaMap f (rationalConstant a) = rationalConstant (f a) := by
  simp [abscissaMap, IsFractionRing.map, IsLocalization.map_eq]

private theorem coefficient_trdeg {E : Type} [Field E] [Algebra L E] {n : ℕ}
    (a : Fin n → E) (h : Function.Injective (parameterEval (algebraMap L E) a)) :
    1 ≤ trdeg L (CoefficientField a) := by
  classical
  apply Cardinal.one_le_iff_ne_zero.mpr
  intro hz
  let : Algebra.IsAlgebraic L (CoefficientField a) := trdeg_eq_zero_iff.mp hz
  have he : CoefficientField a = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have ha (j : Fin n) : ∃ b : L, algebraMap L E b = a j := by
    have hm : a j ∈ CoefficientField a := IntermediateField.subset_adjoin _ _ (Set.mem_range_self j)
    rw [he, IntermediateField.mem_bot] at hm
    exact hm
  choose b hb using ha
  -- Constant coordinates would express the offset as a linear combination of the weights.
  have hrel : (MvPolynomial.X none : SourceRing n) =
      ∑ j : Fin n, MvPolynomial.X (some j) * C (rationalConstant (b j)) := by
    apply h
    simp only [parameterEval, eval₂Hom_X', Option.elim_none, map_sum, map_mul, Option.elim_some,
      eval₂Hom_C, RingHom.comp_apply, abscissaMap_constant, hb]
  have hbad := congrArg (MvPolynomial.eval (fun i : Option (Fin n) => i.elim (1 : FX) (fun _ => 0)))
    hrel
  simp at hbad

private theorem seed_finite (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] {n : ℕ}
    (a : Fin n → ConstantSeedField C₀)
    (h : Function.Injective (parameterEval (constToSeed C₀) a)) :
    letI : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
    Module.Finite (CoefficientField a) (ConstantSeedField C₀) := by
  let standardAlgebra : Algebra L (ConstantSeedField C₀) := inferInstance
  have hstandard : @Algebra.EssFiniteType L (ConstantSeedField C₀) _ _ standardAlgebra := by
    let : Algebra.EssFiniteType (ConstantSeedRing C₀) (ConstantSeedField C₀) :=
      Algebra.EssFiniteType.of_isLocalization _ (ConstantSeedRing C₀)⁰
    exact Algebra.EssFiniteType.comp L (ConstantSeedRing C₀) (ConstantSeedField C₀)
  have halgebra : standardAlgebra = (constToSeed C₀).toAlgebra :=
    Algebra.algebra_ext _ _ fun _ => rfl
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  let F := CoefficientField a
  let : FaithfulSMul L F :=
    (faithfulSMul_iff_algebraMap_injective L F).mpr (algebraMap L F).injective
  let : FaithfulSMul F (ConstantSeedField C₀) :=
    (faithfulSMul_iff_algebraMap_injective F _).mpr (algebraMap F (ConstantSeedField C₀)).injective
  have hF : 1 ≤ trdeg L F := coefficient_trdeg a h
  -- Transport this bound along the same algebra equality used for essential finite type.
  have hE : trdeg L (ConstantSeedField C₀) ≤ 1 :=
    Eq.mp (congrArg (fun alg : Algebra L (ConstantSeedField C₀) =>
      letI := alg
      trdeg L (ConstantSeedField C₀) ≤ 1) halgebra) (seed_trdeg C₀)
  have hsum : trdeg F (ConstantSeedField C₀) + 1 ≤ 0 + 1 := calc
    trdeg F (ConstantSeedField C₀) + 1 ≤ trdeg F (ConstantSeedField C₀) + trdeg L F :=
      add_le_add_right hF _
    _ = trdeg L (ConstantSeedField C₀) := by rw [add_comm, trdeg_add_eq L F]
    _ ≤ 0 + 1 := by simpa using hE
  let : Algebra.IsAlgebraic F (ConstantSeedField C₀) := trdeg_eq_zero_iff.mp
    (le_antisymm ((Cardinal.add_le_add_iff_of_lt_aleph0 Cardinal.one_lt_aleph0).mp hsum) bot_le)
  let E := ConstantSeedField C₀
  let : Algebra.EssFiniteType L E :=
    Eq.mp (congrArg (fun alg => @Algebra.EssFiniteType L (ConstantSeedField C₀) _ _ alg)
      halgebra) hstandard
  let : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp L F E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

section RationalExtension

attribute [local instance] Polynomial.algebra MvPolynomial.algebraMvPolynomial

-- Use the same fraction-ring algebras as Mathlib's rank preservation theorems.
private abbrev abscissaAlgebra {F E : Type} [Field F] [Field E] [Algebra F E] :
    Algebra (FractionRing F[X]) (FractionRing E[X]) :=
  FractionRing.liftAlgebra F[X] (FractionRing E[X])

attribute [local instance] abscissaAlgebra

private abbrev weightAlgebra {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} :
    Algebra (RationalWeightField F n) (RationalWeightField E n) :=
  FractionRing.liftAlgebra (RationalWeightRing F n) (RationalWeightField E n)

attribute [local instance] weightAlgebra

private theorem abscissa_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E] :
    algebraMap (FractionRing F[X]) (FractionRing E[X]) = abscissaMap (algebraMap F E) := by
  apply IsFractionRing.ringHom_ext (A := F[X])
  intro p
  change IsFractionRing.lift (FaithfulSMul.algebraMap_injective F[X] (FractionRing E[X]))
      (algebraMap F[X] (FractionRing F[X]) p) = _
  rw [IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply F[X] E[X] (FractionRing E[X])]
  simp [abscissaMap, IsFractionRing.map, IsLocalization.map_eq]

private def weightEmbedding {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}
    (p : SourceRing n →+* RationalWeightRing F n) (hp : Function.Injective p)
    (q : SourceRing n →+* RationalWeightRing E n) (hq : Function.Injective q)
    (h : (MvPolynomial.map (abscissaMap (algebraMap F E))).comp p = q) :
    letI := sliceAlgebra p hp
    letI := sliceAlgebra q hq
    RationalWeightField F n →ₐ[SliceField n] RationalWeightField E n := by
  let := sliceAlgebra p hp
  let := sliceAlgebra q hq
  let P := RationalWeightRing F n
  let Q := RationalWeightRing E n
  let F' := RationalWeightField F n
  let E' := RationalWeightField E n
  refine ⟨algebraMap F' E', ?_⟩
  suffices he : (algebraMap F' E').comp (algebraMap (SliceField n) F') =
      algebraMap (SliceField n) E' from RingHom.congr_fun he
  apply IsFractionRing.ringHom_ext (A := SourceRing n)
  intro r
  change algebraMap F' E' (algebraMap (SliceField n) F'
    (algebraMap (SourceRing n) (SliceField n) r)) = _
  rw [sliceAlgebra_apply, sliceAlgebra_apply]
  change IsFractionRing.lift (FaithfulSMul.algebraMap_injective P E')
      (algebraMap P F' (p r)) = _
  rw [IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply P Q E']
  rw [MvPolynomial.algebraMap_def, abscissa_algebraMap]
  exact congrArg (algebraMap Q E') (DFunLike.congr_fun h r)

private theorem weight_finite_rank {F E : Type} [Field F] [Field E] [Algebra F E]
    [Module.Finite F E] (n : ℕ) :
    Module.Finite (RationalWeightField F n) (RationalWeightField E n) ∧
      Module.finrank (RationalWeightField F n) (RationalWeightField E n) =
        Module.finrank F E := by
  have hrX : Module.rank (FractionRing F[X]) (FractionRing E[X]) = Module.rank F E :=
    Algebra.IsAlgebraic.rank_fractionRing_polynomial
  let : Module.Finite (FractionRing F[X]) (FractionRing E[X]) := by
    apply Module.rank_lt_aleph0_iff.mp
    rw [hrX]
    exact Module.rank_lt_aleph0_iff.mpr inferInstance
  have hrW : Module.rank (RationalWeightField F n) (RationalWeightField E n) =
      Module.rank F E := by
    rw [Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial (R := FractionRing F[X])
      (S := FractionRing E[X]) (Fin n), Cardinal.lift_id, hrX]
  refine ⟨Module.rank_lt_aleph0_iff.mp ?_, congrArg Cardinal.toNat hrW⟩
  rw [hrW]
  exact Module.rank_lt_aleph0_iff.mpr inferInstance

end RationalExtension

/-- The dominant parameter map retains the seed mapping degree over the generic cut. -/
theorem proof : K1_14_2_4_1_3_2.c2 := by
  intro C₀ _ J g n R A h
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  let F := CoefficientField A.coordinate
  let E := ConstantSeedField C₀
  let p := coefficientParameter A.coordinate
  let q := parameterEval (constToSeed C₀) A.coordinate
  have hp : Function.Injective p := coefficientParameter_injective A.coordinate h
  have he : (MvPolynomial.map (abscissaMap (algebraMap F E))).comp p = q := by
    change (MvPolynomial.map (abscissaMap (algebraMap F E))).comp
      (coefficientParameter A.coordinate) = q
    rw [coefficientParameter, parameterEval_comp]
    rfl
  let : Module.Finite F E := seed_finite C₀ A.coordinate h
  refine ⟨weightEmbedding p hp q h he, ?_⟩
  have hw := weight_finite_rank (F := F) (E := E) n
  exact ⟨hw.1, hw.2.le⟩

end

end K1_14_2_4_1_3_2_2
end PackSource_K1_14_2_4_1_3_2_2Proof

section PackSource_K1_14_2_4_1_3_3Aux1
set_option autoImplicit true
namespace K1_14_2_4_1_3_3

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_3 MvPolynomial
open scoped Polynomial

private theorem specialize_ordinate {n : ℕ} (P : FamilyEquation n) (t : Fin n → L) :
    MvPolynomial.eval (algebraMap L SeedField ∘ t) (ordinateForm P) =
      ((specialize P t).map (algebraMap L[X] FX)).eval₂
        (algebraMap FX SeedField) (generic 1) := by
  let e := MvPolynomial.eval (algebraMap L SeedField ∘ t)
  let m := MvPolynomial.map (algebraMap FX SeedField) (σ := Fin n)
  let v := e.comp m
  let ξ := algebraMap L[X] FX Polynomial.X
  let α := (algebraMap FX SeedField).comp (algebraMap L[X] FX)
  have hC : v.comp (MvPolynomial.map (algebraMap L FX)) =
      (algebraMap L SeedField).comp (MvPolynomial.eval t) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [v, e, m, RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval_C]
        using (IsScalarTower.algebraMap_apply L FX SeedField a).symm
    · intro i
      simp [v, e, m]
  have hX : v.comp (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
      (MvPolynomial.C ξ)) = α.comp (Polynomial.mapRingHom (MvPolynomial.eval t)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C]
      rw [show v (MvPolynomial.map (algebraMap L FX) a) =
        algebraMap L SeedField (MvPolynomial.eval t a) from RingHom.congr_fun hC a]
      change algebraMap L SeedField (MvPolynomial.eval t a) =
        algebraMap FX SeedField (algebraMap L[X] FX (algebraMap L L[X] (MvPolynomial.eval t a)))
      rw [← IsScalarTower.algebraMap_apply L L[X] FX, ← IsScalarTower.algebraMap_apply L FX SeedField]
    · simp [v, m, e, ξ, α]
  change e ((equationAtX P).eval₂ m (MvPolynomial.C (generic 1))) = _
  rw [Polynomial.hom_eval₂]
  rw [show e (MvPolynomial.C (generic 1)) = generic 1 by simp [e]]
  change (equationAtX P).eval₂ v (generic 1) = _
  unfold equationAtX specialize
  rw [Polynomial.eval₂_map]
  change P.eval₂ (v.comp (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
    (MvPolynomial.C ξ))) (generic 1) = _
  rw [hX, Polynomial.eval₂_map, Polynomial.eval₂_map]

private theorem generic_ordinate_injective :
    Function.Injective (Polynomial.eval₂RingHom (algebraMap FX SeedField) (generic 1)) := by
  let ι := (algebraMap Seeds SeedField).comp (Polynomial.toMvPolynomial (R := FX)
    (1 : Fin 2)).toRingHom
  have he : Polynomial.eval₂RingHom (algebraMap FX SeedField) (generic 1) = ι := by
    apply Polynomial.ringHom_ext
    · intro a
      change (Polynomial.C a).eval₂ (algebraMap FX SeedField) (generic 1) =
        algebraMap Seeds SeedField ((Polynomial.toMvPolynomial (1 : Fin 2)) (Polynomial.C a))
      rw [Polynomial.eval₂_C, Polynomial.toMvPolynomial_C]
      exact IsScalarTower.algebraMap_apply FX Seeds SeedField a
    · simp [ι, generic]
  rw [he]
  exact (IsFractionRing.injective Seeds SeedField).comp (Polynomial.toMvPolynomial_injective 1)

/-- The coefficient tuple has no ordinate section above a proper constant closed subset. -/
theorem ordinate_denominators {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n)
    (q : ParameterRing n) (hq : q ∉ coefficientIdeal A) :
    IsUnit (Ideal.Quotient.mk _
      (MvPolynomial.map (algebraMap L SeedField) q) : OrdinateSection A) := by
  classical
  let I := coefficientIdeal A
  let s := MvPolynomial.map (algebraMap L SeedField) (σ := Fin n)
  let π : MvPolynomial (Fin n) SeedField →+* OrdinateSection A := Ideal.Quotient.mk _
  change IsUnit (π (s q))
  by_contra hn
  obtain ⟨M, hM, hqM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)
  let : M.IsMaximal := hM
  let E := OrdinateSection A ⧸ M
  let ψ : MvPolynomial (Fin n) SeedField →+* E := (Ideal.Quotient.mk M).comp π
  let ρ : ParameterRing n →+* E := ψ.comp s
  let T := RingHom.ker ρ
  let : T.IsPrime := RingHom.ker_isPrime ρ
  have hIT : I ≤ T := by
    intro r hr
    apply RingHom.mem_ker.mpr
    change Ideal.Quotient.mk M (π (s r)) = 0
    rw [show π (s r) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ?_, map_zero]
    apply Ideal.mem_sup_left
    change MvPolynomial.map (algebraMap L SeedField) r ∈
      I.map (MvPolynomial.map (algebraMap L SeedField))
    exact Ideal.mem_map_of_mem _ hr
  have hle : I ⊔ Ideal.span {q} ≤ T :=
    sup_le hIT (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hqM))))
  have hI : I.IsPrime := RingHom.ker_isPrime _
  have hd := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hI hq (le_rfl : q.totalDegree ≤ q.totalDegree)).1
  have hdim : (affineHilbertPolynomial I).natDegree ≤ 1 := (chart_dimension A).2
  let : Module.Finite L (ParameterRing n ⧸ (I ⊔ Ideal.span {q})) :=
    natDegree_affineHilbertPolynomial_eq_zero_iff.mp (by omega)
  let B := ParameterRing n ⧸ T
  let : Module.Finite L B := Module.Finite.of_surjective
    (Ideal.Quotient.factorₐ L hle).toLinearMap (Ideal.Quotient.factor_surjective hle)
  choose t ht using fun i : Fin n =>
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := B)).2
      (Ideal.Quotient.mk T (MvPolynomial.X i))
  let β := ψ.comp MvPolynomial.C
  have hψ : ψ = β.comp (MvPolynomial.eval (algebraMap L SeedField ∘ t)) := by
    apply MvPolynomial.ringHom_ext
    · simp [β]
    · intro i
      simp only [β, RingHom.comp_apply, MvPolynomial.eval_X, Function.comp_apply]
      have hi : Ideal.Quotient.mk T (MvPolynomial.C (t i)) =
          Ideal.Quotient.mk T (MvPolynomial.X i) := ht i
      have he := congrArg (Ideal.Quotient.lift T ρ (fun _ hx => RingHom.mem_ker.mp hx)) hi
      simpa only [Ideal.Quotient.lift_mk, ρ, s, RingHom.comp_apply,
        MvPolynomial.map_C, MvPolynomial.map_X] using he.symm
  have htI (r : ParameterRing n) (hr : r ∈ I) : MvPolynomial.eval t r = 0 := by
    have hz : ψ (s r) = 0 := RingHom.mem_ker.mp (hIT hr)
    rw [hψ, RingHom.comp_apply, show s r = MvPolynomial.map (algebraMap L SeedField) r from rfl,
      MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp] at hz
    exact (β.injective.comp (algebraMap L SeedField).injective) (by simpa using hz)
  have hnonzero : specialize A.equation t ≠ 0 := by
    intro hzero
    have htzero : ∀ i, t i = 0 := by
      intro i
      obtain ⟨j, k, h⟩ := coefficient_representation A i
      have hp := congrArg (fun P : (L[X])[X] => (P.coeff j).coeff k) hzero
      simp only [specialize, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
        Polynomial.coeff_zero] at hp
      simpa [map_sub, hp] using htI _ h
    obtain ⟨ℓ, hℓ⟩ := coefficient_normalization A
    simpa [htzero] using htI _ hℓ
  have hcut : ψ (ordinateForm A.equation) = 0 := by
    change Ideal.Quotient.mk M (π (ordinateForm A.equation)) = 0
    rw [show π (ordinateForm A.equation) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)),
      map_zero]
  rw [hψ, RingHom.comp_apply] at hcut
  have hz := β.injective (hcut.trans (map_zero β).symm)
  rw [specialize_ordinate] at hz
  apply hnonzero
  have hi := Polynomial.map_injective (algebraMap L[X] FX) (IsFractionRing.injective L[X] FX)
  apply hi
  exact generic_ordinate_injective (by simpa using hz)

end
end K1_14_2_4_1_3_3
end PackSource_K1_14_2_4_1_3_3Aux1

section PackSource_K1_13_5_5_2Defs
set_option autoImplicit true
namespace K1_13_5_5_2

noncomputable section

open K1_13_5_5 MvPolynomial
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

/-- The leading total-degree forms define the affine cone of the section at infinity. -/
def infinityIdeal {σ F : Type*} [Field F] (P : Ideal (MvPolynomial σ F)) :
    Ideal (MvPolynomial σ F) :=
  Ideal.span ((fun f : MvPolynomial σ F => homogeneousComponent f.totalDegree f) '' (P : Set _))

/-- The image ideal of a coefficient cone under the three linear jet forms. -/
def jetImage (J : Ideal FreshCoeffRing) : Ideal FreshJetRing := J.comap freshProjection

abbrev PairRing := MvPolynomial (Fin 2) FreshField
abbrev PairField := FractionRing PairRing

/-- The two jet forms provide an affine projection of a cone to the plane. -/
def pairMap (L : Fin 2 → FreshJetRing) (J : Ideal FreshCoeffRing) :
    PairRing →ₐ[FreshField] (FreshCoeffRing ⧸ J) :=
  (Ideal.Quotient.mkₐ FreshField J).comp (freshProjection.comp (aeval L))

/-- The fiber of a cone over the generic point of that plane. -/
abbrev genericFiber (L : Fin 2 → FreshJetRing) (J : Ideal FreshCoeffRing) : Type :=
  letI : Module PairRing (FreshCoeffRing ⧸ J) :=
    Module.compHom (FreshCoeffRing ⧸ J)
      (show PairRing →+* (FreshCoeffRing ⧸ J) from (pairMap L J).toRingHom)
  PairField ⊗[PairRing] (FreshCoeffRing ⧸ J)

def genericFiberDimension (L : Fin 2 → FreshJetRing) (J : Ideal FreshCoeffRing) : ℕ :=
  Module.finrank PairField (genericFiber L J)

/-- The two forms are homogeneous linear and the corresponding jet quotient is finite
over the polynomial ring they define. -/
def jetPairMap (L : Fin 2 → FreshJetRing) (J : Ideal FreshJetRing) :
    PairRing →ₐ[FreshField] (FreshJetRing ⧸ J) :=
  (Ideal.Quotient.mkₐ FreshField J).comp (aeval L)

def FiniteJetPair (L : Fin 2 → FreshJetRing) (J : Ideal FreshJetRing) : Prop :=
  (∀ i, (L i).IsHomogeneous 1) ∧ @RingHom.Finite PairRing (FreshJetRing ⧸ J) _ _
    (jetPairMap L J).toRingHom

theorem FiniteJetPair.of_le {L : Fin 2 → FreshJetRing} {J J' : Ideal FreshJetRing}
    (h : FiniteJetPair L J) (hle : J ≤ J') : FiniteJetPair L J' := by
  refine ⟨h.1, ?_⟩
  have hcomp : jetPairMap L J' = (Ideal.Quotient.factorₐ FreshField hle).comp (jetPairMap L J) := by
    unfold jetPairMap
    ext i
    simp
  rw [hcomp]
  exact RingHom.Finite.comp
    (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)) h.2

end

end K1_13_5_5_2
end PackSource_K1_13_5_5_2Defs

section PackSource_K1_14_2_4_1_3_3Split
set_option autoImplicit true
namespace K1_14_2_4_1_3_3

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_2 K1_14_2_4_1_3

/-- After inverting the constant denominators, the nonempty coefficient fibre is
the coefficient root function field with the unused slice parameter adjoined. -/
def c1 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n),
    0 < g → Module.Finite SeedField (OrdinateSection A) → Nontrivial (OrdinateSection A) →
    (∀ q : ParameterRing n, q ∉ coefficientIdeal A →
      IsUnit (Ideal.Quotient.mk _
        (MvPolynomial.map (algebraMap L SeedField) q) : OrdinateSection A)) →
    ∃ e : OrdinateSection A ≃+* SpareField (CoefficientRootField A),
      IsOrdinateMap (coefficientBase A) (coefficientOrdinate A)
        (e.toRingHom.comp (algebraMap SeedField (OrdinateSection A)))

/-- The original ordinate fibre recovers the original root field whenever its
ordinate accepts the embedding of the independent slice parameters. -/
def c2 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g : ℕ)
    (R : PrimitiveRoot C₀ J g),
    Module.Finite SeedField (RootYSection J) →
    ∀ b : SeedField →+* SpareField (RootField R),
      IsOrdinateMap (rootBase R) (rootOrdinate R) b →
      ∃ e : RootYSection J ≃+* SpareField (RootField R),
        e.toRingHom.comp (algebraMap SeedField (RootYSection J)) = b

/-- The root degrees over the two seed function fields with X adjoined are
equal. Their relative degree is therefore the seed degree, also after adjoining
the unused slice parameter. -/
def c3 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient) (g n : ℕ)
    (R : PrimitiveRoot C₀ J g) (A : CoefficientChart R n),
    0 < g → fieldDegree (mapSpare (coefficientRootInclusion A)) = seedDegree A

private theorem section_tower {k U V D E : Type} [Field k] [Field U] [Field V]
    [CommRing D] [CommRing E] [Algebra k D] [Algebra k E]
    (e : D ≃+* U) (e' : E ≃+* V) (f : U →+* V)
    (h : e'.toRingHom.comp (algebraMap k E) =
      f.comp (e.toRingHom.comp (algebraMap k D))) :
    Module.finrank k D * fieldDegree f = Module.finrank k E := by
  let a : k →+* U := e.toRingHom.comp (algebraMap k D)
  let b : k →+* V := f.comp a
  let : Algebra k U := a.toAlgebra
  let : Algebra k V := b.toAlgebra
  let : Algebra U V := f.toAlgebra
  let : IsScalarTower k U V := IsScalarTower.of_algebraMap_eq (R := k) (S := U) (A := V)
    fun _ => rfl
  let eu : D ≃ₐ[k] U := { e with commutes' := fun _ => rfl }
  let ev : E ≃ₐ[k] V := { e' with commutes' := fun x => RingHom.congr_fun h x }
  change Module.finrank k D * Module.finrank U V = Module.finrank k E
  rw [eu.toLinearEquiv.finrank_eq, ev.toLinearEquiv.finrank_eq]
  exact Module.finrank_mul_finrank k U V

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) :
    K1_14_2_4_1_3.c3 := by
  classical
  intro C₀ _ J g n R A hg hroot hord
  by_cases hne : Nontrivial (OrdinateSection A)
  · obtain ⟨e, ha, hy, hs⟩ := h1 C₀ J g n R A hg hord hne (ordinate_denominators A)
    let U := SpareField (CoefficientRootField A)
    let V := SpareField (RootField R)
    let f : U →+* V := mapSpare (coefficientRootInclusion A)
    let a : SeedField →+* U := e.toRingHom.comp (algebraMap SeedField (OrdinateSection A))
    let b : SeedField →+* V := f.comp a
    have hb : IsOrdinateMap (rootBase R) (rootOrdinate R) b := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        change f (a (algebraMap FX SeedField x)) = _
        rw [show a (algebraMap FX SeedField x) = _ from ha x]
        exact mapSpare_constant _ _
      · change f (a (generic 1)) = _
        rw [show a (generic 1) = _ from hy]
        exact mapSpare_constant _ _
      · change f (a (generic 0)) = _
        rw [show a (generic 0) = _ from hs]
        exact mapSpare_variable _
    obtain ⟨e', he'⟩ := h2 C₀ J g R hroot b hb
    have hd : fieldDegree f = seedDegree A := h3 C₀ J g n R A hg
    apply le_of_eq
    rw [← hd, Nat.mul_comm]
    exact section_tower e e' f he'
  · let : Subsingleton (OrdinateSection A) := not_nontrivial_iff_subsingleton.mp hne
    rw [Module.finrank_eq_zero_of_subsingleton, Nat.mul_zero]
    exact Nat.zero_le _

end
end K1_14_2_4_1_3_3
end PackSource_K1_14_2_4_1_3_3Split

section PackSource_K1_13_5_5_2Split
set_option autoImplicit true
namespace K1_13_5_5_2

noncomputable section

open K1_13 K1_13_5_5 MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The second-jet height bound on a projective coefficient curve, expressed
as the degree of the affine cone over the generic point of a jet plane. -/
def c1 : Prop :=
  ∀ (Q : Ideal CoeffRing) (L : Fin 2 → FreshJetRing),
    Q.IsPrime → Q.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom) →
    (affineHilbertPolynomial Q).natDegree = 2 → FiniteJetPair L (jetImage (freshIdeal Q)) →
    2 * affineDegree Q ≤
      (133634 : ℚ) * (genericFiberDimension L (freshIdeal Q) : ℚ)

/-- The infinity cycle accounts for the coefficient degree. Repeated primes
in the list encode multiplicity, which also counts on the generic fiber. -/
def c2 : Prop :=
  ∀ (P : Ideal CoeffRing), P.IsPrime → (affineHilbertPolynomial P).natDegree = 2 →
    ∃ (n : ℕ) (Q : Fin n → Ideal CoeffRing),
      (∀ i, Q i ∈ (infinityIdeal P).minimalPrimes ∧
        (Q i).IsHomogeneous (homogeneousSubmodule CoeffIndex Geom) ∧
        (affineHilbertPolynomial (Q i)).natDegree = 2) ∧
      affineDegree P = ∑ i, affineDegree (Q i) ∧
      ∀ (L : Fin 2 → FreshJetRing), Module.Finite PairField
        (genericFiber L (freshIdeal (infinityIdeal P))) →
        (∑ i, genericFiberDimension L (freshIdeal (Q i))) ≤
          genericFiberDimension L (freshIdeal (infinityIdeal P))

/-- Specialization to the hyperplane at infinity cannot exceed the generic
degree over a jet plane, when the two affine coordinate rings are birational. -/
def c3 : Prop :=
  ∀ (P : Ideal CoeffRing) (g d : FreshJetRing), FreshChart P g d →
    ∃ L : Fin 2 → FreshJetRing,
      FiniteJetPair L (jetImage (freshIdeal (infinityIdeal P))) ∧
      Module.Finite PairField (genericFiber L (freshIdeal (infinityIdeal P))) ∧
      genericFiberDimension L (freshIdeal (infinityIdeal P)) ≤ g.totalDegree

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_5_5.c2 := by
  intro P g d hchart
  have hdim := chart_dimension P g d hchart
  refine ⟨hdim, ?_⟩
  obtain ⟨n, Q, hQ, hdeg, hfiber⟩ := h2 P hchart.prime hdim
  obtain ⟨L, hL, hfinite, hbudget⟩ := h3 P g d hchart
  have hcurve (i : Fin n) : 2 * affineDegree (Q i) ≤
      (133634 : ℚ) * (genericFiberDimension L (freshIdeal (Q i)) : ℚ) := by
    obtain ⟨hi, hhom, hd⟩ := hQ i
    have hle : jetImage (freshIdeal (infinityIdeal P)) ≤ jetImage (freshIdeal (Q i)) :=
      Ideal.comap_mono (Ideal.map_mono hi.le)
    exact h1 (Q i) L hi.isPrime hhom hd (hL.of_le hle)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcurve i)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [hdeg]
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  exact_mod_cast (hfiber L hfinite).trans hbudget

end

end K1_13_5_5_2
end PackSource_K1_13_5_5_2Split

section PackSource_K1_14_2_4_1_3_3_3Proof
set_option autoImplicit true
namespace K1_14_2_4_1_3_3_3

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_2 K1_14_2_4_1_3 K1_14_2_4_1_3_3
open scoped Polynomial

set_option autoImplicit false
set_option maxHeartbeats 600000

variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g n : ℕ}
variable {R : PrimitiveRoot C₀ J g}

private def seedImage (A : CoefficientChart R n) :
    letI : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
    IntermediateField L (ConstantSeedField C₀) :=
  letI : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  IntermediateField.adjoin L (Set.range A.coordinate)

private abbrev ImageSeeds (A : CoefficientChart R n) := ↥(seedImage A)

private def imageBase (A : CoefficientChart R n) : L →+* ImageSeeds A :=
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  algebraMap L (ImageSeeds A)

private def chartCoordinate (A : CoefficientChart R n) (i : Fin n) : ImageSeeds A := by
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  exact ⟨A.coordinate i, IntermediateField.subset_adjoin L _ ⟨i, rfl⟩⟩

private def seedMap (A : CoefficientChart R n) :
    SpareField (ImageSeeds A) →+* ConstantSeedX C₀ := by
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  exact mapSpare (seedImage A).val.toRingHom

private def chartEquation (A : CoefficientChart R n) : (SpareField (ImageSeeds A))[X] :=
  (A.equation.map (Polynomial.mapRingHom
    (MvPolynomial.eval₂Hom (imageBase A) (chartCoordinate A)))).map
      (algebraMap (ImageSeeds A)[X] (SpareField (ImageSeeds A)))

private theorem chartEquation_map (A : CoefficientChart R n) :
    (chartEquation A).map (seedMap A) =
      Polynomial.C (insertConstant C₀ (A.scale : ConstantSeedField C₀)) * rootEquation R := by
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  let u : ParameterRing n →+* ImageSeeds A :=
    MvPolynomial.eval₂Hom (imageBase A) (chartCoordinate A)
  let v : ParameterRing n →+* ConstantSeedField C₀ :=
    MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate
  have huv : (seedImage A).val.toRingHom.comp u = v := by
    dsimp only [u, v]
    rw [MvPolynomial.comp_eval₂Hom]
    rfl
  have hm : (seedMap A).comp ((algebraMap (ImageSeeds A)[X] (SpareField (ImageSeeds A))).comp
      (Polynomial.mapRingHom u)) = (insertX C₀).comp (Polynomial.mapRingHom v) := by
    apply RingHom.ext
    intro p
    change mapSpare (seedImage A).val.toRingHom (algebraMap _ _ (p.map u)) =
      insertX C₀ (p.map v)
    rw [mapSpare_polynomial, Polynomial.map_map, huv]
    rfl
  calc
    (chartEquation A).map (seedMap A) =
        (A.equation.map (Polynomial.mapRingHom v)).map (insertX C₀) := by
      change ((A.equation.map (Polynomial.mapRingHom u)).map
        (algebraMap _ _)).map (seedMap A) = _
      simp only [Polynomial.map_map, hm]
    _ = _ := by
      rw [show A.equation.map (Polynomial.mapRingHom v) = _ from A.generic_eq,
        Polynomial.map_mul, Polynomial.map_C]
      rfl

private theorem chartEquation_irreducible (A : CoefficientChart R n) :
    Irreducible (chartEquation A) := by
  let f := Polynomial.mapRingHom (seedMap A)
  let : IsLocalHom f :=
    ⟨fun p hp => Polynomial.isUnit_iff_degree_eq_zero.mpr <| by
      simpa only [f, Polynomial.coe_mapRingHom, Polynomial.degree_map] using
        (Polynomial.isUnit_iff_degree_eq_zero.mp hp)⟩
  apply Irreducible.of_map (f := f)
  change Irreducible ((chartEquation A).map (seedMap A))
  rw [chartEquation_map, irreducible_isUnit_mul]
  · exact R.irreducible
  · exact (A.scale.isUnit.map (insertConstant C₀)).map Polynomial.C

private theorem rootEquation_degree (R : PrimitiveRoot C₀ J g) :
    (rootEquation R).natDegree = g :=
  (Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _).trans R.degree

private theorem chartEquation_degree (A : CoefficientChart R n) :
    (chartEquation A).natDegree = g := by
  rw [← Polynomial.natDegree_map (p := chartEquation A) (seedMap A), chartEquation_map,
    Polynomial.natDegree_C_mul ((A.scale.isUnit.map (insertConstant C₀)).ne_zero),
    rootEquation_degree]

private def rootConstants (A : CoefficientChart R n) :
    SpareField (ImageSeeds A) →+* RootField R :=
  (AdjoinRoot.of (rootEquation R)).comp (seedMap A)

private theorem rootConstants_base (A : CoefficientChart R n) :
    (rootConstants A).comp (mapSpare (imageBase A)) = rootBase R := by
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  change (AdjoinRoot.of (rootEquation R)).comp
    ((mapSpare (seedImage A).val.toRingHom).comp (mapSpare (imageBase A))) = _
  rw [mapSpare_comp]
  rfl

private theorem polynomial_image_mem {E F : Type} [Field E] [Field F]
    (S : Subfield F) (f : E[X] →+* F) (hc : ∀ a, f (Polynomial.C a) ∈ S)
    (hx : f Polynomial.X ∈ S) (p : E[X]) : f p ∈ S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact (map_add f p q).symm ▸ S.add_mem hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    exact S.mul_mem (hc a) (S.pow_mem hx n)

private theorem rootConstants_mem (A : CoefficientChart R n) (x : SpareField (ImageSeeds A)) :
    rootConstants A x ∈ coefficientRoot A := by
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  let : Algebra FX (RootField R) := (rootBase R).toAlgebra
  let B := coefficientRoot A
  have hcoef : (seedImage A).toSubfield ≤ B.toSubfield.comap (seedInRoot R) := by
    change (IntermediateField.adjoin L (Set.range A.coordinate)).toSubfield ≤ _
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨i, rfl⟩)
    · change AdjoinRoot.of (rootEquation R) (spareConstant (ConstantSeedField C₀) (constToSeed C₀ a)) ∈ B
      have ha := B.algebraMap_mem (spareConstant L a)
      change rootBase R (spareConstant L a) ∈ B at ha
      change AdjoinRoot.of (rootEquation R) (mapSpare (constToSeed C₀) (spareConstant L a)) ∈ B at ha
      simpa only [mapSpare_constant] using ha
    · exact IntermediateField.subset_adjoin FX _
        (Set.mem_union_left _ ⟨i, rfl⟩)
  let j : (ImageSeeds A)[X] →+* RootField R :=
    (rootConstants A).comp (algebraMap _ _)
  have hp : ∀ p, j p ∈ B := by
    apply polynomial_image_mem B.toSubfield j
    · intro a
      change rootConstants A (spareConstant (ImageSeeds A) a) ∈ B
      change AdjoinRoot.of (rootEquation R)
        (mapSpare (seedImage A).val.toRingHom (spareConstant (ImageSeeds A) a)) ∈ B
      rw [mapSpare_constant]
      exact hcoef a.property
    · change rootConstants A (spareVariable (ImageSeeds A)) ∈ B
      have hx := B.algebraMap_mem (spareVariable L)
      change rootBase R (spareVariable L) ∈ B at hx
      have h := RingHom.congr_fun (rootConstants_base A) (spareVariable L)
      simp only [RingHom.comp_apply, mapSpare_variable] at h
      exact (congrArg (fun z : RootField R => z ∈ B) h).mpr hx
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (ImageSeeds A)[X] x
  rw [map_div₀]
  exact B.div_mem (hp p) (hp q)

/-- The coefficient root field is the simple extension of the coefficient seed
function field by the original ordinate. -/
private theorem coefficient_root_degree (A : CoefficientChart R n) :
    ∃ j : SpareField (ImageSeeds A) →+* CoefficientRootField A,
      (coefficientRootInclusion A).comp j = rootConstants A ∧ fieldDegree j = g := by
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  let : Algebra FX (RootField R) := (rootBase R).toAlgebra
  let B := coefficientRoot A
  let q := chartEquation A
  let : Fact (Irreducible q) := ⟨chartEquation_irreducible A⟩
  have hdvd : rootEquation R ∣ q.map (seedMap A) := by
    rw [show q.map (seedMap A) = _ from chartEquation_map A]
    exact dvd_mul_left _ _
  let f := AdjoinRoot.map (seedMap A) q (rootEquation R) hdvd
  have hconst (x : SpareField (ImageSeeds A)) : f (AdjoinRoot.of q x) = rootConstants A x :=
    AdjoinRoot.map_of _ _ _ _ _
  have hy : f (AdjoinRoot.root q) = rootOrdinate R := AdjoinRoot.map_root _ _ _ _
  have hf : ∀ w, f w ∈ B := by
    intro w
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective w
    exact polynomial_image_mem B.toSubfield (f.comp (AdjoinRoot.mk q))
      (fun a => by
        rw [RingHom.comp_apply, AdjoinRoot.mk_C, hconst, IntermediateField.mem_toSubfield]
        exact rootConstants_mem A a)
      (by
        rw [RingHom.comp_apply, AdjoinRoot.mk_X, hy, IntermediateField.mem_toSubfield]
        exact (coefficientOrdinate A).property) p
  have hrange : B.toSubfield ≤ f.fieldRange := by
    change (IntermediateField.adjoin FX
      (Set.range (fun i => seedInRoot R (A.coordinate i)) ∪ {rootOrdinate R})).toSubfield ≤ _
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨x, rfl⟩ | (⟨i, rfl⟩ | hx))
    · change rootBase R x ∈ f.fieldRange
      rw [← rootConstants_base A, RingHom.comp_apply, ← hconst]
      exact f.mem_fieldRange_self _
    · let x := spareConstant (ImageSeeds A) (chartCoordinate A i)
      refine ⟨AdjoinRoot.of q x, ?_⟩
      rw [hconst]
      change AdjoinRoot.of (rootEquation R) (mapSpare (seedImage A).val.toRingHom x) = _
      rw [show x = spareConstant (ImageSeeds A) (chartCoordinate A i) from rfl, mapSpare_constant]
      rfl
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨AdjoinRoot.root q, hy⟩
  let j := (rootConstants A).codRestrict B (rootConstants_mem A)
  refine ⟨j, rfl, ?_⟩
  let : Algebra (SpareField (ImageSeeds A)) (CoefficientRootField A) := j.toAlgebra
  let fB := f.codRestrict B hf
  let fA : AdjoinRoot q →ₐ[SpareField (ImageSeeds A)] CoefficientRootField A :=
    { fB with
      commutes' := fun x => Subtype.ext (hconst x) }
  let e := AlgEquiv.ofBijective fA ⟨fB.injective, fun z => by
    obtain ⟨w, hw⟩ := hrange z.property
    exact ⟨w, Subtype.ext hw⟩⟩
  change Module.finrank (SpareField (ImageSeeds A)) (CoefficientRootField A) = g
  rw [← e.toLinearEquiv.finrank_eq]
  exact finrank_quotient_span_eq_natDegree.trans (chartEquation_degree A)

theorem proof : K1_14_2_4_1_3_3.c3 := by
  intro C₀ _ J g n R A hg
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  have hseed : fieldDegree (seedMap A) = seedDegree A :=
    (degree_mapSpare (seedImage A).val.toRingHom).trans degree_algebraMap
  have hroot : fieldDegree (AdjoinRoot.of (rootEquation R)) = g := by
    rw [← AdjoinRoot.algebraMap_eq, degree_algebraMap]
    exact finrank_quotient_span_eq_natDegree.trans (rootEquation_degree R)
  obtain ⟨j, hj, hd⟩ := coefficient_root_degree A
  have hbig := degree_comp (seedMap A) (AdjoinRoot.of (rootEquation R))
  have hsmall := degree_comp j (coefficientRootInclusion A)
  rw [hroot, hseed] at hbig
  rw [hd, hj] at hsmall
  rw [degree_mapSpare]
  apply Nat.mul_left_cancel hg
  exact hsmall.trans (hbig.symm.trans (Nat.mul_comm _ _))

end
end K1_14_2_4_1_3_3_3
end PackSource_K1_14_2_4_1_3_3_3Proof

section PackSource_K1_13_5_5_2_1Defs
set_option autoImplicit true
namespace K1_13_5_5_2_1

noncomputable section

open K1_13 K1_13_5_5 K1_13_5_5_2
open scoped Polynomial TensorProduct

/-- Dehomogenize the coefficient cone by setting one coefficient equal to one. -/
abbrev CoefficientChart {k : Type} [Field k] {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) k)) (i : Fin n) :=
  MvPolynomial (Fin n) k ⧸ (Q ⊔ Ideal.span {MvPolynomial.X i - 1})

abbrev ChartRing (Q : Ideal CoeffRing) (i : CoeffIndex) := CoefficientChart Q i

/-- The polynomial with the actual dehomogenized coefficient coordinates. -/
def chartDirection {k : Type} [Field k] {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) k)) (i : Fin n) : (CoefficientChart Q i)[X] :=
  ∑ j : Fin n, Polynomial.monomial j.val (Ideal.Quotient.mk _ (MvPolynomial.X j))

abbrev direction (Q : Ideal CoeffRing) (i : CoeffIndex) : (ChartRing Q i)[X] :=
  chartDirection Q i

abbrev OpenRing (Q : Ideal CoeffRing) (i : CoeffIndex) (a : ChartRing Q i) :=
  Localization.Away a

abbrev FreshOpen (Q : Ideal CoeffRing) (i : CoeffIndex) (a : ChartRing Q i) :=
  FreshField ⊗[Geom] OpenRing Q i a

def openDirection (Q : Ideal CoeffRing) (i : CoeffIndex) (a : ChartRing Q i) :
    (OpenRing Q i a)[X] :=
  (direction Q i).map (algebraMap _ _)

/-- Evaluate at the fresh center after adjoining it to the constant field. -/
def freshEval (A : Type) [CommRing A] [Algebra Geom A] :
    A[X] →+* FreshField ⊗[Geom] A :=
  Polynomial.eval₂RingHom Algebra.TensorProduct.includeRight.toRingHom
    (algebraMap FreshField _ freshCenter)

/-- The quotient that measures the zero multiplicity of a regular function on an affine chart. -/
abbrev PrincipalQuot {A : Type} [CommRing A] (x : A) := A ⧸ Ideal.span {x}

/-- A monic factorization on a fixed open, with Bezout identities available over its ring. -/
structure Factorization {A : Type} [CommRing A] (f : A[X]) where
  n : ℕ
  factor : Fin n → A[X]
  multiplicity : Fin n → ℕ
  product_eq : f = ∏ i, factor i ^ multiplicity i
  monic : ∀ i, (factor i).Monic
  multiplicity_bounds : ∀ i, 0 < multiplicity i ∧ multiplicity i ≤ 133634
  pairwise_coprime : Pairwise (fun i j => IsCoprime (factor i) (factor j))
  derivative_coprime : ∀ i, IsCoprime (factor i) (factor i).derivative

def commonFactor {A : Type} [CommRing A] {f : A[X]} (s : Factorization f) : A[X] :=
  ∏ i, s.factor i ^ (s.multiplicity i - 2)

def trimmedValue {A : Type} [CommRing A] {f : A[X]} (s : Factorization f) : A[X] :=
  ∏ i, s.factor i ^ min (s.multiplicity i) 2

/-- A cone with normalized jet coordinates, with the common scaling removed. -/
def coneJetMap {A : Type} [CommRing A] [Algebra FreshField A] (d : Fin 3 → A) :
    FreshJetRing →ₐ[FreshField] A[X] :=
  MvPolynomial.aeval (fun j => Polynomial.C (d j) * Polynomial.X)

def coneJetIdeal {A : Type} [CommRing A] [Algebra FreshField A] (d : Fin 3 → A) :
    Ideal FreshJetRing :=
  RingHom.ker (coneJetMap d).toRingHom

def conePairMap {A : Type} [CommRing A] [Algebra FreshField A] (d : Fin 3 → A)
    (L : Fin 2 → FreshJetRing) : PairRing →ₐ[FreshField] A[X] :=
  (coneJetMap d).comp (MvPolynomial.aeval L)

/-- Substitute two degree-one forms in a polynomial ring with one scaling variable. -/
def polynomialPairMap (F : Type) [Field F] {A : Type} [CommRing A] [Algebra F A] (v w : A) :
    MvPolynomial (Fin 2) F →ₐ[F] A[X] :=
  MvPolynomial.aeval ![Polynomial.C v * Polynomial.X, Polynomial.C w * Polynomial.X]

/-- In a normalization containing the zeroth jet, use its reduced value first. -/
abbrev valuePairMap {A : Type} [CommRing A] [Algebra FreshField A] (v w : A) :
    PairRing →ₐ[FreshField] A[X] :=
  polynomialPairMap FreshField v w

/-- The same generic fiber construction as for the coefficient cone, for a specified map. -/
abbrev pairFiber {A : Type} [CommRing A] [Algebra FreshField A]
    (φ : PairRing →ₐ[FreshField] A) : Type :=
  letI : Module PairRing A := Module.compHom A φ.toRingHom
  PairField ⊗[PairRing] A

def pairRank {A : Type} [CommRing A] [Algebra FreshField A]
    (φ : PairRing →ₐ[FreshField] A) : ℕ :=
  Module.finrank PairField (pairFiber φ)

end

end K1_13_5_5_2_1
end PackSource_K1_13_5_5_2_1Defs

section PackSource_K1_13_5_5_2_1Chart
set_option autoImplicit true
namespace K1_13_5_5_2_1

noncomputable section

open K1_13 K1_13_5_5 MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 500000

private theorem eval₂_scale {k E σ : Type} [Field k] [CommRing E] (α : k →+* E)
    (v : σ → E) (u : E) {p : MvPolynomial σ k} {n : ℕ} (h : p.IsHomogeneous n) :
    eval₂Hom α (fun j => u * v j) p = u ^ n * eval₂Hom α v p := by
  classical
  have hp := (homogeneousComponent_eq_self h).symm.trans (homogeneousComponent_apply n p)
  rw [hp, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d.degree = n := (Finset.mem_filter.mp hd).2
  simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  change d.support.sum d = n at hdeg
  rw [hdeg]
  ac_rfl

private theorem chart_domain {k σ : Type} [Field k] (Q : Ideal (MvPolynomial σ k))
    (hQ : Q.IsPrime) (hhom : Q.IsHomogeneous (homogeneousSubmodule σ k)) (i : σ)
    (hi : MvPolynomial.X i ∉ Q) : IsDomain (MvPolynomial σ k ⧸ (Q ⊔ Ideal.span {MvPolynomial.X i - 1})) := by
  classical
  let R := MvPolynomial σ k ⧸ Q
  let : IsDomain R := (Ideal.Quotient.isDomain_iff_prime Q).2 hQ
  let E := FractionRing R
  let q : MvPolynomial σ k →+* E := (algebraMap R E).comp (Ideal.Quotient.mk Q)
  let α : k →+* E := q.comp C
  let z (j : σ) := q (MvPolynomial.X j)
  let u := z i
  have hu : u ≠ 0 := by
    intro h
    apply hi
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective R E
    change u = algebraMap R E 0
    rw [h, map_zero]
  let v (j : σ) := z j / u
  let ψ := eval₂Hom α v
  have hz : eval₂Hom α z = q := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [α]
    · simp [z]
  have hscale (p : MvPolynomial σ k) (n : ℕ) (hp : p.IsHomogeneous n) :
      q p = u ^ n * ψ p := by
    have hv : (fun j => u * v j) = z := by
      funext j
      exact mul_div_cancel₀ _ hu
    simpa only [ψ, hv, hz] using eval₂_scale α v u hp
  let I : Ideal (MvPolynomial σ k) := Q ⊔ Ideal.span {MvPolynomial.X i - 1}
  have hI : I = RingHom.ker ψ := by
    apply le_antisymm
    · refine sup_le (fun p hp => ?_) (Ideal.span_le.mpr ?_)
      · change ψ p = 0
        rw [← sum_homogeneousComponent p, map_sum]
        apply Finset.sum_eq_zero
        intro n _
        have hm : homogeneousComponent n p ∈ Q := homogeneousComponent_mem_of_mem hhom hp n
        have hq : q (homogeneousComponent n p) = 0 := by
          simp [q, Ideal.Quotient.eq_zero_iff_mem.mpr hm]
        rw [hscale _ _ (homogeneousComponent_isHomogeneous _ _)] at hq
        exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ hu)
      · intro p hp
        obtain rfl := Set.mem_singleton_iff.mp hp
        change ψ (MvPolynomial.X i - 1) = 0
        rw [map_sub, map_one, sub_eq_zero]
        simpa only [ψ, eval₂Hom_X', v] using div_self hu
    · intro p hp
      change ψ p = 0 at hp
      let m := p.totalDegree
      let H := ∑ n ∈ Finset.range (m + 1), MvPolynomial.X i ^ (m - n) * homogeneousComponent n p
      have hqH : q H = u ^ m * ψ p := by
        calc
          q H = ∑ n ∈ Finset.range (m + 1), u ^ (m - n) * q (homogeneousComponent n p) := by
            simp only [H, map_sum, map_mul, map_pow, u, z]
          _ = ∑ n ∈ Finset.range (m + 1), u ^ m * ψ (homogeneousComponent n p) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [hscale _ _ (homogeneousComponent_isHomogeneous _ _), ← mul_assoc, ← pow_add,
              Nat.sub_add_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]
          _ = u ^ m * ψ p := by
            rw [← Finset.mul_sum, ← map_sum, sum_homogeneousComponent]
      have hH : H ∈ Q := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        apply IsFractionRing.injective R E
        change q H = algebraMap R E 0
        rw [hqH, hp, mul_zero, map_zero]
      let π := Ideal.Quotient.mk I
      have hπ : π (MvPolynomial.X i) = 1 := sub_eq_zero.mp (by
        rw [← map_one π, ← map_sub]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          ((show Ideal.span {MvPolynomial.X i - 1} ≤ I from le_sup_right)
            (Ideal.mem_span_singleton_self (MvPolynomial.X i - 1))))
      have hπH : π H = π p := by
        calc
          π H = ∑ n ∈ Finset.range (m + 1), π (homogeneousComponent n p) := by
            simp only [H, map_sum, map_mul, map_pow, hπ, one_pow, one_mul]
          _ = π p := by rw [← map_sum, sum_homogeneousComponent]
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        (hπH ▸ Ideal.Quotient.eq_zero_iff_mem.mpr ((show Q ≤ I from le_sup_left) hH))
  exact (Ideal.Quotient.isDomain_iff_prime I).2 (hI.symm ▸ RingHom.ker_isPrime ψ)

/-- Setting a surviving coordinate of a homogeneous prime cone to one gives a domain. -/
theorem chartRing_isDomain (Q : Ideal CoeffRing) (hQ : Q.IsPrime)
    (hhom : Q.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom)) (i : CoeffIndex)
    (hi : MvPolynomial.X i ∉ Q) : IsDomain (ChartRing Q i) :=
  chart_domain Q hQ hhom i hi

private theorem exists_coordinate {k σ : Type} [Field k] [Finite σ]
    (Q : Ideal (MvPolynomial σ k)) (hdim : (affineHilbertPolynomial Q).natDegree ≠ 0) :
    ∃ i : σ, MvPolynomial.X i ∉ Q := by
  by_contra! hall
  let q := Ideal.Quotient.mk Q
  have hmaps : q = q.comp (C.comp (eval (0 : σ → k))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp only [RingHom.comp_apply, eval_X, Pi.zero_apply, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i)
  have hsurj : Function.Surjective (algebraMap k (MvPolynomial σ k ⧸ Q)) := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨eval (0 : σ → k) p, (DFunLike.congr_fun hmaps p).symm⟩
  let : Module.Finite k (MvPolynomial σ k ⧸ Q) :=
    Module.Finite.of_surjective (Algebra.linearMap k _) hsurj
  exact hdim (by rw [affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C])

private theorem monic_chart_aux {k : Type} [Field k] {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) k)) (hQ : Q.IsPrime)
    (hhom : Q.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    (hdim : (affineHilbertPolynomial Q).natDegree ≠ 0) :
    ∃ i : Fin n, MvPolynomial.X i ∉ Q ∧ IsDomain (CoefficientChart Q i) ∧
      (chartDirection Q i).Monic ∧ (chartDirection Q i).natDegree ≤ i.val := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => MvPolynomial.X i ∉ Q)
  obtain ⟨j, hj⟩ := exists_coordinate Q hdim
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s Fin.val ⟨j, by simp [s, hj]⟩
  have hiQ : MvPolynomial.X i ∉ Q := (Finset.mem_filter.mp hi).2
  let I : Ideal (MvPolynomial (Fin n) k) := Q ⊔ Ideal.span {MvPolynomial.X i - 1}
  let q := Ideal.Quotient.mk I
  let hdom := chart_domain Q hQ hhom i hiQ
  have : IsDomain (CoefficientChart Q i) := hdom
  have hqi : q (MvPolynomial.X i) = 1 := sub_eq_zero.mp (by
    rw [← map_one q, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {MvPolynomial.X i - 1} ≤ I from le_sup_right)
        (Ideal.mem_span_singleton_self (MvPolynomial.X i - 1))))
  have hcoeffi : (chartDirection Q i).coeff i.val = 1 := by
    rw [chartDirection, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
    · simpa only [Polynomial.coeff_monomial_same] using hqi
    · intro l _ hli
      simp [Polynomial.coeff_monomial, Fin.val_ne_of_ne hli]
    · simp
  have hle : (chartDirection Q i).natDegree ≤ i.val := by
    unfold chartDirection
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro l _
    by_cases hl : l.val ≤ i.val
    · exact Polynomial.natDegree_monomial_le _ |>.trans hl
    · have hlQ : MvPolynomial.X l ∈ Q := by
        by_contra h
        exact hl (hmax l (by simp [s, h]))
      have hqQl : q (MvPolynomial.X l) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ((show Q ≤ I from le_sup_left) hlQ)
      change (Polynomial.monomial l.val (q (MvPolynomial.X l))).natDegree ≤ i.val
      simp [hqQl]
  have hn : (chartDirection Q i).natDegree = i.val :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeffi]; exact one_ne_zero)
  exact ⟨i, hiQ, hdom, by rw [Polynomial.Monic, Polynomial.leadingCoeff, hn, hcoeffi], hle⟩

/-- The greatest surviving coordinate provides a monic polynomial direction. -/
theorem monic_chart (Q : Ideal CoeffRing) (hQ : Q.IsPrime)
    (hhom : Q.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom))
    (hdim : (affineHilbertPolynomial Q).natDegree = 2) :
    ∃ i : CoeffIndex, MvPolynomial.X i ∉ Q ∧ IsDomain (ChartRing Q i) ∧
      (direction Q i).Monic ∧ (direction Q i).natDegree ≤ 133634 := by
  obtain ⟨i, hi, hdom, hm, hd⟩ := monic_chart_aux Q hQ hhom (by rw [hdim]; decide)
  exact ⟨i, hi, hdom, hm, hd.trans (Nat.le_of_lt_succ i.isLt)⟩

end

end K1_13_5_5_2_1
end PackSource_K1_13_5_5_2_1Chart

section PackSource_K1_13_5_5_2_1Pin
set_option autoImplicit true
namespace K1_13_5_5_2_1

noncomputable section

open K1_13_5_5 K1_13_5_5_2
open scoped Polynomial TensorProduct nonZeroDivisors

set_option maxHeartbeats 1000000

private theorem reduce_polynomialPairMap {F A : Type} [Field F] [CommRing A] [Algebra F A]
    (v w : A) (p : MvPolynomial (Fin 2) F) :
    (polynomialPairMap F v w p).map (Ideal.Quotient.mk (Ideal.span {v})) =
      (((MvPolynomial.uniqueAlgEquiv F (Fin 1))
        ((MvPolynomial.finSuccEquiv F 1 p).coeff 0)).map
          (algebraMap F (PrincipalQuot v))).comp
        (Polynomial.C (Ideal.Quotient.mk (Ideal.span {v}) w) * Polynomial.X) := by
  let D := PrincipalQuot v
  let ρ : A →+* D := Ideal.Quotient.mk (Ideal.span {v})
  let E : MvPolynomial (Fin 1) F →+* D[X] :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap F D))
      (fun _ => Polynomial.C (ρ w) * Polynomial.X)
  have hv : ρ v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self v)
  have h :
      (Polynomial.mapRingHom ρ).comp (polynomialPairMap F v w).toRingHom =
        (E.comp Polynomial.constantCoeff).comp (MvPolynomial.finSuccEquiv F 1).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialPairMap, E, MvPolynomial.finSuccEquiv_apply, Polynomial.algebraMap_apply, ρ]
      rfl
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [polynomialPairMap, E, MvPolynomial.finSuccEquiv_X_zero, hv, ρ]
      · change (polynomialPairMap F v w (MvPolynomial.X j.succ)).map ρ =
          E ((MvPolynomial.finSuccEquiv F 1 (MvPolynomial.X j.succ)).coeff 0)
        rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.coeff_C_zero]
        fin_cases j
        simp [polynomialPairMap, E]
  have hp := DFunLike.congr_fun h p
  change _ = E ((MvPolynomial.finSuccEquiv F 1 p).coeff 0) at hp
  change ((Polynomial.mapRingHom ρ).comp (polynomialPairMap F v w).toRingHom) p = _
  rw [hp]
  change MvPolynomial.eval₂ _ (fun _ : Fin 1 => _) _ = _
  rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
  exact (Polynomial.eval₂_map _ _ _).symm

private theorem pin_bound_aux {F A : Type} [Field F] [CommRing A] [IsDomain A]
    [Algebra F A] (v w : A)
    (hw : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) w))
    (hinj : Function.Injective (polynomialPairMap F v w))
    [Module.Finite F (PrincipalQuot v)] :
    let P := MvPolynomial (Fin 2) F
    let K := FractionRing P
    letI : Module P A[X] := Module.compHom A[X] (polynomialPairMap F v w).toRingHom
    Module.Finite K (K ⊗[P] A[X]) →
      Module.finrank F (PrincipalQuot v) ≤ Module.finrank K (K ⊗[P] A[X]) := by
  classical
  intro P K hfin
  let D := PrincipalQuot v
  let φ := polynomialPairMap F v w
  let : Module P A[X] := Module.compHom A[X] φ.toRingHom
  let ρ : A →+* D := Ideal.Quotient.mk (Ideal.span {v})
  let view := MvPolynomial.finSuccEquiv F 1
  let read := MvPolynomial.uniqueAlgEquiv F (Fin 1)
  let B := Module.finBasis F D
  let r := Module.finrank F D
  choose lift hlift using fun i : Fin r => Ideal.Quotient.mk_surjective (B i)
  have hli : LinearIndependent P (fun i : Fin r => Polynomial.C (lift i)) := by
    rw [Fintype.linearIndependent_iff]
    intro p hp j
    change ∑ i, φ (p i) * Polynomial.C (lift i) = 0 at hp
    by_contra hpj
    have he : ∃ n : ℕ, ∃ i, (view (p i)).coeff n ≠ 0 := by
      by_contra! h
      apply hpj
      exact view.injective (Polynomial.ext (fun n => by simpa using h n j))
    let n := Nat.find he
    have hdiv (i) : Polynomial.X ^ n ∣ view (p i) :=
      Polynomial.X_pow_dvd_iff.mpr (fun k hk => by
        by_contra hc
        exact (Nat.find_min he hk) ⟨i, hc⟩)
    choose q hq using hdiv
    let a : Fin r → P := fun i => view.symm (q i)
    have hx : view.symm (Polynomial.X : (MvPolynomial (Fin 1) F)[X]) = MvPolynomial.X 0 :=
      view.symm_apply_eq.mpr (MvPolynomial.finSuccEquiv_X_zero.symm)
    have hpa (i) : p i = MvPolynomial.X 0 ^ n * a i := by
      have heq := congrArg (fun p => view.symm p) (hq i)
      change view.symm (view (p i)) = view.symm (Polynomial.X ^ n * q i) at heq
      rw [AlgEquiv.symm_apply_apply, map_mul, map_pow, hx] at heq
      exact heq
    have ha : ∑ i, φ (a i) * Polynomial.C (lift i) = 0 := by
      have hz : (φ (MvPolynomial.X 0) ^ n) ≠ 0 := by
        apply pow_ne_zero
        intro hx₀
        exact MvPolynomial.X_ne_zero 0 (hinj (hx₀.trans (map_zero φ).symm))
      rw [show (∑ i, φ (p i) * Polynomial.C (lift i)) =
          φ (MvPolynomial.X 0) ^ n * ∑ i, φ (a i) * Polynomial.C (lift i) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hpa i, map_mul, map_pow, mul_assoc]] at hp
      exact (mul_eq_zero.mp hp).resolve_left hz
    have hred := congrArg (Polynomial.mapRingHom ρ) ha
    have hb (i) : ρ (lift i) = B i := hlift i
    have hmap (i : Fin r) : ((polynomialPairMap F v w) (a i)).map ρ =
        ((read ((view (a i)).coeff 0)).map (algebraMap F D)).comp
          (Polynomial.C (ρ w) * Polynomial.X) :=
      reduce_polynomialPairMap v w (a i)
    simp only [φ, map_sum, map_mul, map_zero, Polynomial.coe_mapRingHom, Polynomial.map_C,
      hmap, hb] at hred
    have hc (k : ℕ) : ∀ i, (read ((view (a i)).coeff 0)).coeff k = 0 := by
      apply Fintype.linearIndependent_iff.mp B.linearIndependent
      have hcoeff := congrArg (fun f : D[X] => f.coeff k) hred
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Polynomial.comp_C_mul_X_coeff,
        Polynomial.coeff_map, Polynomial.coeff_zero] at hcoeff
      apply (hw.pow k).mul_right_inj.mp
      rw [mul_zero, Finset.mul_sum]
      convert hcoeff using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Algebra.smul_def]
      ring
    obtain ⟨i, hi⟩ := Nat.find_spec he
    apply hi
    have hcoef : (view (p i)).coeff n = (q i).coeff 0 := by
      rw [hq i]
      simpa using Polynomial.coeff_X_pow_mul (q i) n 0
    rw [hcoef]
    apply read.injective
    apply Polynomial.ext
    intro k
    simpa only [map_zero, Polynomial.coeff_zero, a, AlgEquiv.apply_symm_apply] using hc k i
  have hLI := hli.of_isLocalizedModule K (nonZeroDivisors P) (TensorProduct.mk P K A[X] 1)
  simpa only [Fintype.card_fin] using hLI.fintype_card_le_finrank

/-- Lifts of a basis of the pin fiber remain independent over the generic pair. -/
theorem pin_bound {A : Type} [CommRing A] [IsDomain A] [Algebra FreshField A] (v w : A)
    (hw : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) w))
    (hinj : Function.Injective (valuePairMap v w))
    [hfin : Module.Finite PairField (pairFiber (valuePairMap v w))]
    [Module.Finite FreshField (PrincipalQuot v)] :
    Module.finrank FreshField (PrincipalQuot v) ≤ pairRank (valuePairMap v w) :=
  pin_bound_aux (F := FreshField) v w hw hinj hfin

end

end K1_13_5_5_2_1
end PackSource_K1_13_5_5_2_1Pin

section PackSource_K1_13_5_5_2_1Lengths
set_option autoImplicit true
namespace K1_13_5_5_2_1

noncomputable section

open K1_13_5_5

set_option backward.isDefEq.respectTransparency false

private theorem finrank_quotient_pow {A : Type} [CommRing A] [IsDomain A]
    [Algebra FreshField A] (I : Ideal A) (hI : I.IsPrincipal) (hne : I ≠ ⊥)
    [Module.Finite FreshField (A ⧸ I)] (n : ℕ) :
    Module.Finite FreshField (A ⧸ I ^ n) ∧
      Module.finrank FreshField (A ⧸ I ^ n) = n * Module.finrank FreshField (A ⧸ I) := by
  have hrank : ∀ n : ℕ, Module.rank FreshField (A ⧸ I ^ n) =
      n • Module.rank FreshField (A ⧸ I) := by
    intro m
    induction m with
    | zero =>
      have : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      simp
    | succ m ih =>
      let J : Ideal A := I ^ (m + 1)
      let S := (I ^ m).map (Ideal.Quotient.mk J)
      have hJI : J ≤ I ^ m := Ideal.pow_le_pow_right (Nat.le_succ m)
      let e₁ : ((A ⧸ J) ⧸ S) ≃ₐ[FreshField] (A ⧸ I ^ m) :=
        DoubleQuot.quotQuotEquivQuotOfLEₐ FreshField hJI
      let e₂ : (A ⧸ I) ≃ₗ[FreshField] S :=
        ((Ideal.quotEquivPowQuotPowSucc hI hne m).trans
          (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I m)).restrictScalars FreshField
      have h := Submodule.rank_quotient_add_rank (S.restrictScalars FreshField)
      change Module.rank FreshField ((A ⧸ J) ⧸ S) + Module.rank FreshField S =
        Module.rank FreshField (A ⧸ I ^ (m + 1)) at h
      rw [e₁.toLinearEquiv.rank_eq, ← e₂.rank_eq, ih] at h
      simpa only [succ_nsmul] using h.symm
  refine ⟨Module.rank_lt_aleph0_iff.mp ?_, ?_⟩
  · rw [hrank, Cardinal.nsmul_lt_aleph0_iff]
    exact Or.inr (Module.rank_lt_aleph0 _ _)
  · simpa only [Module.finrank, nsmul_eq_mul, Cardinal.toNat_mul, Cardinal.toNat_natCast] using
      congrArg Cardinal.toNat (hrank n)

/-- A containment of powers compares principal zero-scheme lengths with multiplicity. -/
theorem length_bound {A : Type} [CommRing A] [IsDomain A] [Algebra FreshField A]
    (x y : A) (N : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : y ∣ x) (hpow : x ^ 2 ∣ y ^ N)
    [Module.Finite FreshField (PrincipalQuot x)] :
    Module.Finite FreshField (PrincipalQuot y) ∧
      2 * Module.finrank FreshField (PrincipalQuot x) ≤
        N * Module.finrank FreshField (PrincipalQuot y) := by
  let I : Ideal A := Ideal.span {x}
  let J : Ideal A := Ideal.span {y}
  have hIJ : I ≤ J := Ideal.span_singleton_le_span_singleton.mpr hxy
  let f := (Ideal.Quotient.factorₐ FreshField hIJ).toLinearMap
  have : Module.Finite FreshField (PrincipalQuot y) :=
    Module.Finite.of_surjective f (Ideal.Quotient.factor_surjective hIJ)
  refine ⟨inferInstance, ?_⟩
  obtain ⟨_, hxlen⟩ := finrank_quotient_pow I (by infer_instance)
    (by simpa only [I, ne_eq, Ideal.span_singleton_eq_bot] using hx) 2
  obtain ⟨hyfin, hylen⟩ := finrank_quotient_pow J (by infer_instance)
    (by simpa only [J, ne_eq, Ideal.span_singleton_eq_bot] using hy) N
  have hpowIJ : J ^ N ≤ I ^ 2 := by
    dsimp only [I, J]
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_le_span_singleton.mpr hpow
  let g := (Ideal.Quotient.factorₐ FreshField hpowIJ).toLinearMap
  have hle := LinearMap.finrank_le_finrank_of_surjective (f := g)
    (Ideal.Quotient.factor_surjective hpowIJ)
  rwa [hxlen, hylen] at hle

end

end K1_13_5_5_2_1
end PackSource_K1_13_5_5_2_1Lengths

section PackSource_K1_14_2_4_1_3_3_1Defs
set_option autoImplicit true
namespace K1_14_2_4_1_3_3_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_2 K1_14_2_4_1_3
open K1_14_2_4_1_3_3
open scoped Polynomial

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g n : ℕ}
  {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n)

def parameterEval : ParameterRing n →+* ConstantSeedField C₀ :=
  MvPolynomial.eval₂Hom (constToSeed C₀) A.coordinate

instance : (coefficientIdeal A).IsPrime := RingHom.ker_isPrime (parameterEval A)

abbrev CoeffRing := ParameterRing n ⧸ coefficientIdeal A
abbrev CoeffFrac := FractionRing (CoeffRing A)

def toCoeffFrac : ParameterRing n →+* CoeffFrac A :=
  (algebraMap (CoeffRing A) (CoeffFrac A)).comp (Ideal.Quotient.mk _)

private def quotientToSeed : CoeffRing A →+* ConstantSeedField C₀ :=
  RingHom.kerLift (parameterEval A)

def coeffToSeed : CoeffFrac A →+* ConstantSeedField C₀ :=
  IsFractionRing.lift (g := quotientToSeed A) (RingHom.kerLift_injective (parameterEval A))

@[simp] theorem coeffToSeed_toCoeffFrac (q : ParameterRing n) :
    coeffToSeed A (toCoeffFrac A q) = parameterEval A q :=
  IsFractionRing.lift_algebraMap (g := quotientToSeed A)
    (RingHom.kerLift_injective (parameterEval A)) _

def abscissa : FX := algebraMap L[X] FX Polynomial.X

theorem extend_abscissa : extendX C₀ abscissa = insertX C₀ Polynomial.X := by
  unfold extendX abscissa IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertX]

theorem extend_constant (a : L) :
    extendX C₀ (algebraMap L FX a) = insertConstant C₀ (constToSeed C₀ a) := by
  rw [IsScalarTower.algebraMap_apply L L[X] FX]
  unfold extendX IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp [insertConstant, insertX]

def coefficientCoordinate (i : Fin n) : CoefficientRootField A := by
  letI : Algebra FX (RootField R) := (rootBase R).toAlgebra
  exact ⟨seedInRoot R (A.coordinate i), IntermediateField.subset_adjoin FX _
    (Set.mem_union_left _ (Set.mem_range_self i))⟩

def parameterRoot : ParameterRing n →+* CoefficientRootField A :=
  MvPolynomial.eval₂Hom ((coefficientBase A).comp (algebraMap L FX)) (coefficientCoordinate A)

theorem parameterRoot_inclusion :
    (coefficientRootInclusion A).comp (parameterRoot A) =
      (seedInRoot R).comp (parameterEval A) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [parameterRoot, parameterEval, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change AdjoinRoot.of _ (extendX C₀ (algebraMap L FX a)) =
      AdjoinRoot.of _ (insertConstant C₀ (constToSeed C₀ a))
    rw [extend_constant]
  · intro i
    simp only [parameterRoot, parameterEval, MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    rfl

theorem parameterRoot_ker : RingHom.ker (parameterRoot A) = coefficientIdeal A := by
  ext q
  rw [RingHom.mem_ker]
  change parameterRoot A q = 0 ↔ parameterEval A q = 0
  rw [← (coefficientRootInclusion A).injective.eq_iff, map_zero,
    ← RingHom.comp_apply, parameterRoot_inclusion, RingHom.comp_apply,
    ← (seedInRoot R).injective.eq_iff, map_zero]

private def quotientToRoot : CoeffRing A →+* CoefficientRootField A :=
  Ideal.Quotient.lift _ (parameterRoot A)
    (fun _ h => RingHom.mem_ker.mp ((parameterRoot_ker A).symm ▸ h))

private theorem quotientToRoot_injective : Function.Injective (quotientToRoot A) := by
      intro a b h
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      apply Ideal.Quotient.eq.mpr
      rw [← parameterRoot_ker A, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact h

def coeffToRoot : CoeffFrac A →+* CoefficientRootField A :=
  IsFractionRing.lift (quotientToRoot_injective A)

@[simp] theorem coeffToRoot_toCoeffFrac (q : ParameterRing n) :
    coeffToRoot A (toCoeffFrac A q) = parameterRoot A q :=
  IsFractionRing.lift_algebraMap (g := quotientToRoot A) (quotientToRoot_injective A) _

theorem coeffToRoot_inclusion :
    (coefficientRootInclusion A).comp (coeffToRoot A) = (seedInRoot R).comp (coeffToSeed A) := by
  apply IsFractionRing.ringHom_ext (A := CoeffRing A)
  intro a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  change coefficientRootInclusion A (coeffToRoot A (toCoeffFrac A q)) =
    seedInRoot R (coeffToSeed A (toCoeffFrac A q))
  rw [coeffToRoot_toCoeffFrac, coeffToSeed_toCoeffFrac]
  exact RingHom.congr_fun (parameterRoot_inclusion A) q

abbrev EquationRing := ((CoeffFrac A)[X])[X]

def primitiveEquation : EquationRing A :=
  A.equation.map (Polynomial.mapRingHom (toCoeffFrac A))

def rawRoot : EquationRing A →+* CoefficientRootField A :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (coeffToRoot A) (coefficientBase A abscissa))
    (coefficientOrdinate A)

private theorem equation_map :
    (primitiveEquation A).map (Polynomial.mapRingHom (coeffToSeed A)) =
      Polynomial.C (Polynomial.C (A.scale : ConstantSeedField C₀)) * R.equation := by
  rw [primitiveEquation, Polynomial.map_map, Polynomial.mapRingHom_comp, ← A.generic_eq]
  congr 2
  exact RingHom.ext (coeffToSeed_toCoeffFrac A)

theorem equation_primitive : (primitiveEquation A).IsPrimitive := by
  let i := Polynomial.mapRingHom (coeffToSeed A)
  have hprim : ((primitiveEquation A).map i).IsPrimitive := by
    rw [show i = Polynomial.mapRingHom (coeffToSeed A) from rfl, equation_map]
    exact Polynomial.isPrimitive_of_dvd R.primitive
      (associated_unit_mul_left _ _ (A.scale.isUnit.map (Polynomial.C.comp Polynomial.C))).dvd
  refine Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr fun d hd => ?_
  have hm : IsUnit (i d) :=
    Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprim _ (by simpa using map_dvd (Polynomial.mapRingHom i) hd)
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hm ⊢
  simpa only [i, Polynomial.coe_mapRingHom, Polynomial.degree_map_eq_of_injective
    (coeffToSeed A).injective] using hm

private def coeffXToSeedX : FractionRing (CoeffFrac A)[X] →+* ConstantSeedX C₀ :=
  IsFractionRing.map (j := Polynomial.mapRingHom (coeffToSeed A))
    (Polynomial.map_injective _ (coeffToSeed A).injective)

private theorem coeffXToSeedX_apply (a : (CoeffFrac A)[X]) :
    coeffXToSeedX A (algebraMap _ (FractionRing (CoeffFrac A)[X]) a) =
      insertX C₀ (a.map (coeffToSeed A)) := by
  unfold coeffXToSeedX IsFractionRing.map
  rw [IsLocalization.map_eq]
  rfl

private abbrev genericEquation :=
  (primitiveEquation A).map (algebraMap (CoeffFrac A)[X] (FractionRing (CoeffFrac A)[X]))

private theorem genericEquation_map :
    (genericEquation A).map (coeffXToSeedX A) =
      Polynomial.C (insertConstant C₀ (A.scale : ConstantSeedField C₀)) * rootEquation R := by
  rw [Polynomial.map_map, show (coeffXToSeedX A).comp
    (algebraMap (CoeffFrac A)[X] (FractionRing (CoeffFrac A)[X])) =
      (insertX C₀).comp (Polynomial.mapRingHom (coeffToSeed A)) from
    RingHom.ext (coeffXToSeedX_apply A), ← Polynomial.map_map,
    equation_map, Polynomial.map_mul, Polynomial.map_C]
  rfl

private theorem rawRoot_inclusion :
    (coefficientRootInclusion A).comp (rawRoot A) =
      (AdjoinRoot.mk (rootEquation R)).comp
        (Polynomial.mapRingHom ((insertX C₀).comp (Polynomial.mapRingHom (coeffToSeed A)))) := by
  apply Polynomial.ringHom_ext
  · have h : (coefficientRootInclusion A).comp
        (Polynomial.eval₂RingHom (coeffToRoot A) (coefficientBase A abscissa)) =
      (AdjoinRoot.of (rootEquation R)).comp
        ((insertX C₀).comp (Polynomial.mapRingHom (coeffToSeed A))) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          Polynomial.coe_mapRingHom, Polynomial.map_C]
        exact RingHom.congr_fun (coeffToRoot_inclusion A) a
      · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
          Polynomial.coe_mapRingHom, Polynomial.map_X]
        exact congrArg (AdjoinRoot.of (rootEquation R)) (extend_abscissa (C₀ := C₀))
    intro a
    simpa only [rawRoot, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom, Polynomial.map_C, AdjoinRoot.of] using RingHom.congr_fun h a
  · simp only [rawRoot, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.coe_mapRingHom, Polynomial.map_X, AdjoinRoot.mk_X]
    rfl

/-- The coefficient equation generates the whole kernel, including before the abscissa
denominators are inverted. -/
theorem rawRoot_eq_zero (q : EquationRing A) :
    rawRoot A q = 0 ↔ primitiveEquation A ∣ q := by
  let k := algebraMap (CoeffFrac A)[X] (FractionRing (CoeffFrac A)[X])
  rw [← (coefficientRootInclusion A).injective.eq_iff, map_zero, ← RingHom.comp_apply,
    rawRoot_inclusion, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    ← show (q.map k).map (coeffXToSeedX A) =
      q.map ((insertX C₀).comp (Polynomial.mapRingHom (coeffToSeed A))) by
        rw [Polynomial.map_map]
        congr 1
        exact RingHom.ext (coeffXToSeedX_apply A)]
  rw [AdjoinRoot.mk_eq_zero]
  have ha : Associated ((genericEquation A).map (coeffXToSeedX A)) (rootEquation R) := by
    rw [genericEquation_map]
    exact associated_unit_mul_left _ _ (A.scale.isUnit.map (Polynomial.C.comp (insertConstant C₀)))
  rw [← ha.dvd_iff_dvd_left, Polynomial.map_dvd_map']
  exact (Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map
    (FractionRing (CoeffFrac A)[X]) (equation_primitive A)).symm

end
end K1_14_2_4_1_3_3_1
end PackSource_K1_14_2_4_1_3_3_1Defs

section PackSource_K1_13_5_5_2_1Split
set_option autoImplicit true
namespace K1_13_5_5_2_1

noncomputable section

open K1_13 K1_13_5_5 K1_13_5_5_2
open scoped Polynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- A fresh value cut gives the coefficient degree on every dense fixed open. -/
def c1 : Prop :=
  ∀ (Q : Ideal CoeffRing) (i : CoeffIndex) (a : ChartRing Q i),
    Q.IsPrime → Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule CoeffIndex Geom) →
    (MvPolynomial.affineHilbertPolynomial Q).natDegree = 2 →
    MvPolynomial.X i ∉ Q → IsDomain (ChartRing Q i) → a ≠ 0 →
    IsDomain (FreshOpen Q i a) ∧
    Function.Injective (freshEval (OpenRing Q i a)) ∧
    Module.Finite FreshField (PrincipalQuot (freshEval _ (openDirection Q i a))) ∧
    (Module.finrank FreshField
      (PrincipalQuot (freshEval _ (openDirection Q i a))) : ℚ) = MvPolynomial.affineDegree Q

/-- Factor over the function field, then clear the finitely many denominators in
the factors and the Bezout certificates before choosing the fresh center. -/
def c2 : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra Geom A] (f : A[X]),
    f.Monic → f.natDegree ≤ 133634 →
    ∃ (a : A), a ≠ 0 ∧ Nonempty (Factorization (f.map (algebraMap A (Localization.Away a))))

/-- Remove the common second-jet factor and keep the first two copies of every factor. -/
def c3 : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Geom A] (f : A[X]) (s : Factorization f),
    ∃ q : Fin 3 → A[X], q 0 = trimmedValue s ∧
      (∀ j, commonFactor s * q j = Polynomial.hasseDeriv j.val f) ∧
      Ideal.span (Set.range q) = ⊤

/-- The fresh open and the common rescaling preserve the jet kernel and generic rank. -/
def c4 : Prop :=
  ∀ (Q : Ideal CoeffRing) (i : CoeffIndex) (a : ChartRing Q i),
    Q.IsPrime → Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule CoeffIndex Geom) →
    (MvPolynomial.affineHilbertPolynomial Q).natDegree = 2 →
    MvPolynomial.X i ∉ Q → IsDomain (ChartRing Q i) → a ≠ 0 →
    IsDomain (FreshOpen Q i a) →
    ∀ (b : FreshOpen Q i a) (d : Fin 3 → FreshOpen Q i a), b ≠ 0 →
      (∀ j, b * d j = freshEval _ (Polynomial.hasseDeriv j.val (openDirection Q i a))) →
      jetImage (freshIdeal Q) = coneJetIdeal d ∧
      ∀ L, FiniteJetPair L (jetImage (freshIdeal Q)) →
        Module.Finite PairField (pairFiber (conePairMap d L)) ∧
        pairRank (conePairMap d L) = genericFiberDimension L (freshIdeal Q)

/-- Choose a finite linear projection with the zeroth jet as its first coordinate. -/
def c5 : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra FreshField A]
    (d : Fin 3 → A) (L : Fin 2 → FreshJetRing),
    d 0 ≠ 0 → ¬ IsUnit (d 0) → Ideal.span (Set.range d) = ⊤ →
    FiniteJetPair L (coneJetIdeal d) →
    ∃ (M : Fin 2 → FreshJetRing) (w : A), FiniteJetPair M (coneJetIdeal d) ∧
      conePairMap d M = valuePairMap (d 0) w ∧
      Function.Injective (conePairMap d M) ∧
      IsUnit (Ideal.Quotient.mk (Ideal.span {d 0}) w)

/-- Two finite linear normalizations of the same jet cone have the same generic rank. -/
def c6 : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra FreshField A]
    (d : Fin 3 → A) (L M : Fin 2 → FreshJetRing),
    FiniteJetPair L (coneJetIdeal d) → Module.Finite PairField (pairFiber (conePairMap d L)) →
    FiniteJetPair M (coneJetIdeal d) → Function.Injective (conePairMap d M) →
    Module.Finite PairField (pairFiber (conePairMap d M)) ∧
      pairRank (conePairMap d M) = pairRank (conePairMap d L)

private theorem commonFactor_monic {A : Type} [CommRing A] {f : A[X]}
    (s : Factorization f) : (commonFactor s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => (s.monic i).pow _)

private theorem trimmedValue_monic {A : Type} [CommRing A] {f : A[X]}
    (s : Factorization f) : (trimmedValue s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => (s.monic i).pow _)

private theorem trimmedValue_dvd {A : Type} [CommRing A] {f : A[X]}
    (s : Factorization f) : trimmedValue s ∣ f := by
  exact (Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow _ (min_le_left _ _))).trans
    (dvd_of_eq s.product_eq.symm)

private theorem full_square_dvd {A : Type} [CommRing A] {f : A[X]}
    (s : Factorization f) : f ^ 2 ∣ (trimmedValue s) ^ 133634 := by
  refine (dvd_of_eq (congrArg (fun g : A[X] => g ^ 2) s.product_eq)).trans ?_
  rw [trimmedValue, ← Finset.prod_pow, ← Finset.prod_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  rw [← pow_mul, ← pow_mul]
  apply pow_dvd_pow
  have hi := s.multiplicity_bounds i
  by_cases h : s.multiplicity i ≤ 2
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (by omega)]
    omega

private theorem eval_divisions {A B : Type} [CommRing A] [CommRing B]
    (e : A[X] →+* B) {f : A[X]} (s : Factorization f) :
    e (trimmedValue s) ∣ e f ∧ e f ^ 2 ∣ e (trimmedValue s) ^ 133634 := by
  exact ⟨map_dvd e (trimmedValue_dvd s),
    by simpa only [map_pow] using map_dvd e (full_square_dvd s)⟩

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) : K1_13_5_5_2.c1 := by
  intro Q L hQ hhom hdim hL
  obtain ⟨i, hi, hchart, hmonic, hdegree⟩ := monic_chart Q hQ hhom hdim
  let : IsDomain (ChartRing Q i) := hchart
  obtain ⟨a, ha, ⟨s⟩⟩ := h2 (ChartRing Q i) (direction Q i) hmonic hdegree
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
  have hdiv := eval_divisions e s
  have hdeq : d 0 = e (trimmedValue s) := congrArg e hq0
  rw [← hdeq] at hdiv
  obtain ⟨hdfin, hlen⟩ := length_bound x (d 0) 133634 hx hd hdiv.1 hdiv.2
  rw [← hcoeff]
  have hlenQ : 2 * (Module.finrank FreshField (PrincipalQuot x) : ℚ) ≤
      133634 * (Module.finrank FreshField (PrincipalQuot (d 0)) : ℚ) := by
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
    exact hlenQ.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hbound) (by norm_num))

end

end K1_13_5_5_2_1
end PackSource_K1_13_5_5_2_1Split

section PackSource_K1_13_6_3_5_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace K1_13_6_3_5_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 MvPolynomial
open scoped TensorProduct

variable {k E σ ι : Type*} [Field k] [Field E] [Algebra k E]

private abbrev scalarMap : MvPolynomial σ k →+* MvPolynomial σ E :=
  MvPolynomial.map (algebraMap k E)

private def quotientTensor (I : Ideal (MvPolynomial σ k)) :
    E ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[E] MvPolynomial σ E ⧸ I.map scalarMap := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  let ι' : MvPolynomial σ k →ₐ[k] E ⊗[k] MvPolynomial σ k :=
    Algebra.TensorProduct.includeRight
  have hcomp : e.toRingHom.comp ι'.toRingHom = scalarMap := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = _
    simp [e, scalarMap]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k) E _ E I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  exact ((Ideal.map_map (I := I) ι'.toRingHom e.toRingHom).trans
    (congrArg (fun f => I.map f) hcomp)).symm

private theorem quotientTensor_tmul (I : Ideal (MvPolynomial σ k))
    (a : E) (p : MvPolynomial σ k) :
    quotientTensor I (a ⊗ₜ[k] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (I.map scalarMap) (MvPolynomial.algebraTensorAlgEquiv k E (a ⊗ₜ[k] p)) := by
  simp only [quotientTensor, AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  rfl

/-- The polynomial multiplying the basis vector `b i` in a scalar extension. -/
private def piece [DecidableEq ι] (b : Module.Basis ι k E) (p : MvPolynomial σ E) (i : ι) :
    MvPolynomial σ k :=
  TensorProduct.equivFinsuppOfBasisLeft b ((MvPolynomial.algebraTensorAlgEquiv k E).symm p) i

private theorem coeff_piece [DecidableEq ι] (b : Module.Basis ι k E) (p : MvPolynomial σ E)
    (i : ι) (d : σ →₀ ℕ) : (piece b p i).coeff d = b.coord i (p.coeff d) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  obtain ⟨t, rfl⟩ := e.surjective p
  simp only [piece, show MvPolynomial.algebraTensorAlgEquiv k E = e from rfl,
    AlgEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul a q =>
    simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, e,
      algebraTensorAlgEquiv_tmul, coeff_smul, coeff_map]
    have hs : a • algebraMap k E (q.coeff d) = q.coeff d • a := by
      rw [smul_eq_mul, Algebra.smul_def, mul_comm]
    simp only [hs, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm]
  | add t u ht hu =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ht, hu]

private theorem mem_map_iff [DecidableEq ι] (b : Module.Basis ι k E)
    (I : Ideal (MvPolynomial σ k)) (p : MvPolynomial σ E) :
    p ∈ I.map scalarMap ↔ ∀ i, piece b p i ∈ I := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  let eI : E ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[E] _ := quotientTensor I
  let s := TensorProduct.equivFinsuppOfBasisLeft (N := MvPolynomial σ k ⧸ I) b
  obtain ⟨t, rfl⟩ := e.surjective p
  have hc (i : ι) :
      s (eI.symm (Ideal.Quotient.mk (I.map scalarMap) (e t))) i =
        Ideal.Quotient.mk I (TensorProduct.equivFinsuppOfBasisLeft b t i) := by
    induction t using TensorProduct.inductionOn with
    | tmul a q =>
      rw [← quotientTensor_tmul I a q]
      simp only [eI, AlgEquiv.symm_apply_apply, s,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact (map_smul (Ideal.Quotient.mkₐ k I) _ _).symm
    | add t u ht hu =>
      simp only [map_add, Finsupp.add_apply, ht, hu]
  simp only [piece, show MvPolynomial.algebraTensorAlgEquiv k E = e from rfl,
    AlgEquiv.symm_apply_apply, ← Ideal.Quotient.eq_zero_iff_mem, ← hc]
  constructor
  · intro h i
    simp [h]
  · intro h
    have hz : s (eI.symm (Ideal.Quotient.mk (I.map scalarMap) (e t))) = 0 :=
      Finsupp.ext h
    exact eI.symm.injective (s.injective (hz.trans (by simp)))

private theorem eval_piece [DecidableEq ι] (b : Module.Basis ι k E) (p : MvPolynomial σ E)
    (i : ι) (x : σ → k) :
    eval x (piece b p i) = b.coord i (eval ((algebraMap k E) ∘ x) p) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  obtain ⟨t, rfl⟩ := e.surjective p
  simp only [piece, show MvPolynomial.algebraTensorAlgEquiv k E = e from rfl,
    AlgEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul a q =>
    simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, e,
      algebraTensorAlgEquiv_tmul, ← aeval_eq_eval, map_smul]
    have he : eval ((algebraMap k E) ∘ x) (scalarMap q) = algebraMap k E (eval x q) := by
      simpa only [scalarMap, eval_map, RingHom.comp_id, eval₂_id] using
        (eval₂_comp_left (algebraMap k E) (RingHom.id k) x q).symm
    rw [show MvPolynomial.map (algebraMap k E) q = scalarMap q from rfl]
    simp only [aeval_eq_eval, he]
    have hs : a • algebraMap k E (eval x q) = eval x q • a := by
      rw [smul_eq_mul, Algebra.smul_def, mul_comm]
    simp only [hs, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm]
  | add t u ht hu =>
    simp only [map_add, Finsupp.add_apply, ht, hu]

private theorem component_mem_boundary (I : Ideal (MvPolynomial σ k)) {p : MvPolynomial σ k}
    (hp : p ∈ I) {n : ℕ} (hn : p.totalDegree ≤ n) :
    homogeneousComponent n p ∈ boundaryIdeal I := by
  rcases eq_or_lt_of_le hn with rfl | hlt
  · exact Ideal.subset_span ⟨p, hp, rfl⟩
  · rw [homogeneousComponent_eq_zero n p hlt]
    exact Ideal.zero_mem _

private theorem boundary_map (I : Ideal (MvPolynomial σ k)) :
    boundaryIdeal (I.map (scalarMap (E := E))) = (boundaryIdeal I).map scalarMap := by
  classical
  let b := Module.Basis.ofVectorSpace k E
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    apply (mem_map_iff b _ _).2
    intro i
    have hi := (mem_map_iff b I p).1 hp i
    have hn : (piece b p i).totalDegree ≤ p.totalDegree := by
      apply Finset.sup_mono
      intro d hd
      rw [MvPolynomial.mem_support_iff, coeff_piece] at hd
      exact MvPolynomial.mem_support_iff.mpr fun h => hd (by rw [h, map_zero])
    have he : piece b (homogeneousComponent p.totalDegree p) i =
        homogeneousComponent p.totalDegree (piece b p i) := by
      ext d
      by_cases hd : d.degree = p.totalDegree <;>
        simp [coeff_piece, coeff_homogeneousComponent, hd]
    rw [he]
    exact component_mem_boundary I hi hn
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    change scalarMap (homogeneousComponent p.totalDegree p) ∈ boundaryIdeal _
    have he : scalarMap (homogeneousComponent p.totalDegree p) =
        homogeneousComponent p.totalDegree (scalarMap (E := E) p) := by
      ext d
      by_cases hd : d.degree = p.totalDegree <;>
        simp only [scalarMap, coeff_map, coeff_homogeneousComponent, hd, ite_true, ite_false,
          map_zero]
    rw [he]
    exact component_mem_boundary _ (Ideal.mem_map_of_mem _ hp)
      (Finset.sup_mono (support_map_subset (algebraMap k E) p))

/-- Over an algebraically closed base field, the original points detect the
whole extended prime ideal. -/
private theorem mem_map_iff_vanishes [Finite σ] [IsAlgClosed k]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (p : MvPolynomial σ E) :
    p ∈ I.map scalarMap ↔
      ∀ x ∈ zeroLocus k I, eval ((algebraMap k E) ∘ x) p = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k E
  rw [mem_map_iff b]
  constructor
  · intro h x hx
    apply b.forall_coord_eq_zero_iff.mp
    intro i
    rw [← eval_piece]
    exact hx _ (h i)
  · intro h i
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := k) I]
    intro x hx
    change eval x (piece b p i) = 0
    rw [eval_piece, h x hx, map_zero]

/-- Prime ideals over the old algebraically closed field extend to prime ideals. -/
theorem isPrime_map [Finite σ] [IsAlgClosed k]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime) :
    (I.map (MvPolynomial.map (algebraMap k E))).IsPrime := by
  classical
  let b := Module.Basis.ofVectorSpace k E
  apply Ideal.isPrime_iff.mpr
  constructor
  · intro htop
    have hz := (mem_map_iff_vanishes I (1 : MvPolynomial σ E)).mp (by simp [htop])
    apply hI.ne_top
    apply I.eq_top_of_isUnit_mem _ isUnit_one
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := k) I]
    intro x hx
    exact (one_ne_zero ((eval _).map_one.symm.trans (hz x hx))).elim
  · intro p q hpq
    by_cases hp : p ∈ I.map (scalarMap (E := E))
    · exact Or.inl hp
    right
    apply (mem_map_iff b I q).mpr
    obtain ⟨i, hi⟩ := not_forall.mp fun h => hp ((mem_map_iff b I p).mpr h)
    intro j
    apply (hI.mem_or_mem ?_).resolve_left hi
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := k) I]
    intro x hx
    have hz := (mem_map_iff_vanishes I (p * q)).mp hpq x hx
    rw [map_mul] at hz
    change eval x (piece b p i * piece b q j) = 0
    rw [map_mul, eval_piece, eval_piece]
    rcases mul_eq_zero.mp hz with hz | hz <;> simp [hz]

theorem proof : K1_13_6_3_5.c2 := by
  intro A _
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  refine ⟨K1_13_5_5_2.hilbertPolynomial_map (E := GeoField) A, ?_⟩
  intro P hP
  have hb : boundaryIdeal (extendIdeal A) = (boundaryIdeal A).map
      (scalarMap (k := Geom) (E := GeoField)) := boundary_map A
  have hle : (boundaryIdeal A).map (scalarMap (k := Geom) (E := GeoField)) ≤ P :=
    hb ▸ hP.le
  let : (P.comap (scalarMap (k := Geom) (E := GeoField))).IsPrime :=
    hP.isPrime.comap _
  obtain ⟨R, hR, hRP⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hle)
  have hRP' : extendIdeal R ≤ P := Ideal.map_le_iff_le_comap.mpr hRP
  have hR' : (extendIdeal R).IsPrime := isPrime_map R hR.isPrime
  exact ⟨R, hR, le_antisymm hRP' (hP.2 ⟨hR', hb.trans_le (Ideal.map_mono hR.le)⟩ hRP')⟩

end

end K1_13_6_3_5_2
end PackSource_K1_13_6_3_5_2Proof

section PackSource_K1_13_5_5_2_1_4Defs
set_option autoImplicit true
namespace K1_13_5_5_2_1_4

noncomputable section

open K1_13 K1_13_5_5 K1_13_5_5_2_1
open scoped Polynomial

/-- The canonical map to the total fraction ring. -/
abbrev toFraction (R : Type) [CommRing R] : R →+* FractionRing R :=
  algebraMap R (FractionRing R)

/-- A dehomogenized coefficient, restricted to the fixed open and extended to the fresh field. -/
def chartCoeff (Q : Ideal CoeffRing) (i : CoeffIndex) (a : ChartRing Q i)
    (j : CoeffIndex) : FreshOpen Q i a :=
  Algebra.TensorProduct.includeRight (R := Geom)
    (algebraMap (ChartRing Q i) (OpenRing Q i a)
      (Ideal.Quotient.mk _ (MvPolynomial.X j)))

end

end K1_13_5_5_2_1_4
end PackSource_K1_13_5_5_2_1_4Defs

section PackSource_K1_13_5_5_2_1_4Split
set_option autoImplicit true
namespace K1_13_5_5_2_1_4

noncomputable section

open K1_13 K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open scoped Polynomial TensorProduct nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Recover the fresh coefficient cone birationally from the fixed chart and a free scale. -/
def c1 : Prop :=
  ∀ (Q : Ideal CoeffRing) (i : CoeffIndex) (a : ChartRing Q i),
    Q.IsPrime → Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule CoeffIndex Geom) →
    MvPolynomial.X i ∉ Q → IsDomain (ChartRing Q i) → a ≠ 0 →
    IsDomain (FreshOpen Q i a) →
    ∃ e : FractionRing (FreshCoeffRing ⧸ freshIdeal Q) ≃ₐ[FreshField]
        FractionRing ((FreshOpen Q i a)[X]),
      ∀ j : CoeffIndex,
        e (toFraction (FreshCoeffRing ⧸ freshIdeal Q)
          (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
        toFraction (FreshOpen Q i a)[X]
          (Polynomial.C (chartCoeff Q i a j) * Polynomial.X)

/-- Compatible fraction fields give the same rank over the generic pair on an affine surface. -/
def c2 : Prop :=
  ∀ (I : Ideal FreshCoeffRing) [IsDomain (FreshCoeffRing ⧸ I)]
    (A : Type) [CommRing A] [IsDomain A] [Algebra FreshField A]
    (φ : PairRing →ₐ[FreshField] (FreshCoeffRing ⧸ I)) (ψ : PairRing →ₐ[FreshField] A)
    (e : FractionRing (FreshCoeffRing ⧸ I) ≃ₐ[FreshField] FractionRing A),
    (MvPolynomial.affineHilbertPolynomial I).natDegree = 2 →
    (∀ p, e (toFraction (FreshCoeffRing ⧸ I) (φ p)) = toFraction A (ψ p)) →
    Module.Finite PairField (pairFiber ψ) ∧ pairRank ψ = pairRank (A := FreshCoeffRing ⧸ I) φ

private theorem scale_fraction {F A : Type} [Field F] [CommRing A] [IsDomain A]
    [Algebra F A] (b : A) (hb : b ≠ 0) :
    ∃ e : FractionRing A[X] ≃ₐ[F] FractionRing A[X], ∀ x : A,
      e (algebraMap A[X] _ (Polynomial.C x * Polynomial.X)) =
        algebraMap A[X] _ (Polynomial.C (b * x) * Polynomial.X) := by
  let E := FractionRing A[X]
  let j : A[X] →ₐ[A] E := IsScalarTower.toAlgHom A A[X] E
  let s : A[X] →ₐ[A] A[X] := Polynomial.aeval (Polynomial.C b * Polynomial.X)
  have hs : Function.Injective s := (injective_iff_map_eq_zero s).mpr (fun p hp =>
    (Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hb)).mp hp)
  have hinj : Function.Injective (j.comp s) := (IsFractionRing.injective A[X] E).comp hs
  let f : E →ₐ[A] E := IsFractionRing.liftAlgHom (g := j.comp s) hinj
  have hf (p : A[X]) : f (j p) = j (s p) := IsFractionRing.lift_algebraMap hinj p
  have hsC (x : A) : s (Polynomial.C x) = Polynomial.C x := Polynomial.aeval_C _ _
  have hsX : s Polynomial.X = Polynomial.C b * Polynomial.X := Polynomial.aeval_X _
  let g : A[X] →ₐ[A] E := Polynomial.aeval (j Polynomial.X / j (Polynomial.C b))
  have hg : f.comp g = j := by
    apply Polynomial.algHom_ext
    change f (g Polynomial.X) = j Polynomial.X
    rw [show g Polynomial.X = _ from Polynomial.aeval_X _, map_div₀, hf, hf, hsC, hsX, map_mul]
    apply mul_div_cancel_left₀
    intro hz
    apply (Polynomial.C_ne_zero.mpr hb : Polynomial.C b ≠ (0 : A[X]))
    apply IsFractionRing.injective A[X] E
    change j (Polynomial.C b) = j 0
    rw [hz, map_zero]
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective A[X] z
    refine ⟨g u / g v, ?_⟩
    rw [map_div₀]
    exact congrArg₂ (· / ·) (DFunLike.congr_fun hg u) (DFunLike.congr_fun hg v)
  let e := AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩
  refine ⟨e.restrictScalars F, fun x => ?_⟩
  change f (j (Polynomial.C x * Polynomial.X)) = j _
  rw [hf, map_mul, hsC, hsX, ← mul_assoc, ← Polynomial.C_mul, mul_comm x b]

private theorem eval_hasse_sum {ι A B F : Type} [Fintype ι] [CommRing A] [CommRing B]
    [CommRing F] (ρ : A →+* B) (γ : F →+* B) (x : F)
    (n : ι → ℕ) (v : ι → A) (j : ℕ) :
    Polynomial.eval₂RingHom ρ (γ x)
        (Polynomial.hasseDeriv j (∑ l, Polynomial.monomial (n l) (v l))) =
      ∑ l, γ ((n l).choose j * x ^ (n l - j)) * ρ (v l) := by
  simp only [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Polynomial.hasseDeriv_monomial]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, map_mul, map_natCast, map_pow]
  ac_rfl

private theorem eval_linear {ι F B : Type} [Fintype ι] [Field F] [CommRing B] [Algebra F B]
    (v : ι → B) (w : ι → F) :
    MvPolynomial.aeval (fun l => Polynomial.C (v l) * Polynomial.X)
      (∑ l, MvPolynomial.C (w l) * MvPolynomial.X l) =
    Polynomial.C (∑ l, algebraMap F B (w l) * v l) * Polynomial.X := by
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Polynomial.algebraMap_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ac_rfl

private theorem coeff_jet (Q : Ideal CoeffRing) (i : CoeffIndex) (a : ChartRing Q i)
    (j : Fin 3) :
    MvPolynomial.aeval (R := FreshField)
      (fun l => Polynomial.C (chartCoeff Q i a l) * Polynomial.X) (jetForm freshCenter j.val) =
    Polynomial.C (freshEval _ (Polynomial.hasseDeriv j.val (openDirection Q i a))) *
      Polynomial.X := by
  let v (l : CoeffIndex) : OpenRing Q i a :=
    algebraMap (ChartRing Q i) (OpenRing Q i a) (Ideal.Quotient.mk _ (MvPolynomial.X l))
  have hopen : openDirection Q i a = ∑ l : CoeffIndex, Polynomial.monomial l.val (v l) := by
    simp only [openDirection, direction, chartDirection, Polynomial.map_sum, Polynomial.map_monomial, v]
  have heval : freshEval _ (Polynomial.hasseDeriv j.val (openDirection Q i a)) =
      ∑ l : CoeffIndex, algebraMap FreshField (FreshOpen Q i a)
        (l.val.choose j.val * freshCenter ^ (l.val - j.val)) * chartCoeff Q i a l := by
    rw [hopen]
    exact eval_hasse_sum Algebra.TensorProduct.includeRight.toRingHom
      (algebraMap FreshField (FreshOpen Q i a)) freshCenter Fin.val v j.val
  rw [heval]
  exact eval_linear (chartCoeff Q i a) (fun l => l.val.choose j.val * freshCenter ^ (l.val - j.val))

theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_5_2_1.c4 := by
  intro Q i a hQ hhom hdim hi hchart ha hopen b d hb htrim
  let R := FreshCoeffRing ⧸ freshIdeal Q
  let B := FreshOpen Q i a
  let : IsDomain R := (Ideal.Quotient.isDomain_iff_prime _).mpr (freshIdeal_isPrime Q hQ)
  let : IsDomain B := hopen
  let jR : R →ₐ[FreshField] FractionRing R := IsScalarTower.toAlgHom FreshField R _
  let jB : B[X] →ₐ[FreshField] FractionRing B[X] := IsScalarTower.toAlgHom FreshField B[X] _
  obtain ⟨e, he⟩ := h1 Q i a hQ hhom hi hchart ha hopen
  obtain ⟨s, hs⟩ := scale_fraction (F := FreshField) b hb
  let q : FreshCoeffRing →ₐ[FreshField] FractionRing R :=
    jR.comp (Ideal.Quotient.mkₐ FreshField (freshIdeal Q))
  let t : FreshCoeffRing →ₐ[FreshField] B[X] :=
    MvPolynomial.aeval (fun j => Polynomial.C (chartCoeff Q i a j) * Polynomial.X)
  have heq : e.toAlgHom.comp q = jB.comp t := by
    apply MvPolynomial.algHom_ext
    intro j
    change e (jR (Ideal.Quotient.mk (freshIdeal Q) (MvPolynomial.X j))) =
      jB (t (MvPolynomial.X j))
    rw [show t (MvPolynomial.X j) = Polynomial.C (chartCoeff Q i a j) * Polynomial.X from
      MvPolynomial.aeval_X _ j]
    exact he j
  have hjet : (e.toAlgHom.comp q).comp freshProjection =
      s.toAlgHom.comp (jB.comp (coneJetMap d)) := by
    rw [heq]
    apply MvPolynomial.algHom_ext
    intro j
    change jB (t (freshProjection (MvPolynomial.X j))) =
      s (jB (coneJetMap d (MvPolynomial.X j)))
    simp only [freshProjection, coneJetMap, MvPolynomial.aeval_X]
    rw [show t (jetForm freshCenter j.val) = _ from coeff_jet Q i a j, ← htrim j]
    exact (hs (d j)).symm
  have hpoint (p : FreshJetRing) :
      e (jR (Ideal.Quotient.mk (freshIdeal Q) (freshProjection p))) =
        s (jB (coneJetMap d p)) := DFunLike.congr_fun hjet p
  have hinjR : Function.Injective jR := IsFractionRing.injective R _
  have hinjB : Function.Injective jB := IsFractionRing.injective B[X] _
  refine ⟨?_, ?_⟩
  · ext p
    change freshProjection p ∈ freshIdeal Q ↔ coneJetMap d p = 0
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hp
      apply s.injective.comp hinjB
      simp only [Function.comp_apply, map_zero, ← hpoint p, hp]
    · intro hp
      apply e.injective.comp hinjR
      simp only [Function.comp_apply, map_zero, hpoint p, hp]
  · intro L _
    have hdim' : (MvPolynomial.affineHilbertPolynomial (freshIdeal Q)).natDegree = 2 := by
      rw [freshIdeal, hilbertPolynomial_map, hdim]
    apply h2 (freshIdeal Q) B[X] (pairMap L (freshIdeal Q)) (conePairMap d L)
      (e.trans s.symm) hdim'
    intro p
    apply s.injective
    change s (s.symm (e (jR (Ideal.Quotient.mk (freshIdeal Q) (freshProjection
      (MvPolynomial.aeval L p)))))) = s (jB (coneJetMap d (MvPolynomial.aeval L p)))
    rw [AlgEquiv.apply_symm_apply, hpoint]

end

end K1_13_5_5_2_1_4
end PackSource_K1_13_5_5_2_1_4Split

section PackSource_K1_14_2_4_1_3_3_1Proof
set_option autoImplicit true
namespace K1_14_2_4_1_3_3_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_2 K1_14_2_4_1_3
open K1_14_2_4_1_3_3
open scoped Polynomial

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512

variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g n : ℕ}
  {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n)

private abbrev S := OrdinateSection A
private abbrev E := CoefficientRootField A
private abbrev T := SpareField (E A)
private abbrev Raw := (EquationRing A)[X]

local instance : CommSemiring (Raw A) :=
  @Polynomial.commSemiring (EquationRing A)
    (@Polynomial.commSemiring (CoeffFrac A)[X]
      (@Polynomial.commSemiring (CoeffFrac A) (inferInstance : Field (CoeffFrac A)).toCommRing.toCommSemiring))

private abbrev quotientMap : MvPolynomial (Fin n) SeedField →+* S A := Ideal.Quotient.mk _
private abbrev scalarMap : SeedField →+* S A := algebraMap SeedField (S A)
private abbrev sectionParameter : ParameterRing n →+* S A :=
  (quotientMap A).comp (MvPolynomial.map (algebraMap L SeedField))

private abbrev Denominators : Prop :=
  ∀ q : ParameterRing n, q ∉ coefficientIdeal A → IsUnit (sectionParameter A q)

private def parameterQuotient : CoeffRing A →+* S A :=
  Ideal.Quotient.lift _ (sectionParameter A) fun _ h =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ h))

private def coeffToSection (h : Denominators A) : CoeffFrac A →+* S A :=
  IsLocalization.lift (M := nonZeroDivisors (CoeffRing A)) (g := parameterQuotient A) fun d => by
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (d : CoeffRing A)
    rw [← hq]
    apply h
    exact fun hq' => (mem_nonZeroDivisors_iff_ne_zero.mp d.prop)
      (hq ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hq')

private theorem coeffToSection_apply (h : Denominators A) (q : ParameterRing n) :
    coeffToSection A h (toCoeffFrac A q) = sectionParameter A q :=
  IsLocalization.lift_eq (M := nonZeroDivisors (CoeffRing A)) _ _

private def sectionX := scalarMap A (algebraMap FX SeedField abscissa)

private def rawSection (h : Denominators A) : Raw A →+* S A :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (coeffToSection A h) (sectionX A))
      (scalarMap A (K1_14_2.generic 1))) (scalarMap A (K1_14_2.generic 0))

private def rawSpare : Raw A →+* T A :=
  (algebraMap (E A)[X] (T A)).comp (Polynomial.mapRingHom (rawRoot A))

private abbrev RawSeed := MvPolynomial (Fin 2) L[X]

attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance : Algebra RawSeed SeedField :=
  ((algebraMap Seeds SeedField).comp (algebraMap RawSeed Seeds)).toAlgebra

local instance : SMul RawSeed SeedField := (inferInstance : Algebra RawSeed SeedField).toSMul
local instance : SMul Seeds SeedField := (inferInstance : Algebra Seeds SeedField).toSMul

local instance : IsScalarTower RawSeed Seeds SeedField :=
  IsScalarTower.of_algebraMap_eq (R := RawSeed) (S := Seeds) (A := SeedField) fun _ => rfl

private instance rawSeedFraction : IsFractionRing RawSeed SeedField := by
  let M := (nonZeroDivisors L[X]).map (MvPolynomial.C (σ := Fin 2))
  let N := nonZeroDivisors Seeds
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    M N SeedField (fun _ h => h.mem_nonZeroDivisors)
  have he : N.comap (algebraMap RawSeed Seeds) = nonZeroDivisors RawSeed := by
    ext s
    change (algebraMap RawSeed Seeds s) ∈ nonZeroDivisors Seeds ↔ s ∈ nonZeroDivisors RawSeed
    simp only [MvPolynomial.algebraMap_def, mem_nonZeroDivisors_iff_ne_zero, not_iff_not]
    exact (MvPolynomial.map_injective _ (IsFractionRing.injective L[X] FX)).eq_iff' (map_zero _)
  rw [he] at h
  exact h

@[simp] private theorem rawSeed_C (p : L[X]) :
    algebraMap RawSeed SeedField (MvPolynomial.C p) =
      algebraMap FX SeedField (algebraMap L[X] FX p) := by
  rw [IsScalarTower.algebraMap_apply RawSeed Seeds SeedField, MvPolynomial.algebraMap_def,
    MvPolynomial.map_C]
  rfl

@[simp] private theorem rawSeed_X (i : Fin 2) :
    algebraMap RawSeed SeedField (MvPolynomial.X i) = K1_14_2.generic i := by
  rw [IsScalarTower.algebraMap_apply RawSeed Seeds SeedField, MvPolynomial.algebraMap_def,
    MvPolynomial.map_X]
  rfl

private def rawConstant : CoeffFrac A →+* Raw A :=
  Polynomial.C.comp (Polynomial.C.comp Polynomial.C)

private def rawSeedCoeff : L[X] →+* Raw A :=
  Polynomial.eval₂RingHom (R := L) (S := Raw A)
    ((rawConstant A).comp ((toCoeffFrac A).comp MvPolynomial.C))
    (Polynomial.C (Polynomial.C (Polynomial.X : (CoeffFrac A)[X])))

private def seedIntoRaw : RawSeed →+* Raw A :=
  MvPolynomial.eval₂Hom (σ := Fin 2) (R := L[X]) (S₁ := Raw A) (rawSeedCoeff A)
    ![Polynomial.X, Polynomial.C Polynomial.X]

private theorem sectionSeed (h : Denominators A) :
    (rawSection A h).comp (seedIntoRaw A) =
      (scalarMap A).comp (algebraMap RawSeed SeedField) := by
  apply MvPolynomial.ringHom_ext
  · have hc : (rawSection A h).comp (rawSeedCoeff A) =
        (scalarMap A).comp ((algebraMap FX SeedField).comp (algebraMap L[X] FX)) := by
      apply Polynomial.ringHom_ext
      · intro c
        simp only [rawSection, rawSeedCoeff, rawConstant, RingHom.comp_apply,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, coeffToSection_apply, MvPolynomial.map_C]
        change scalarMap A (algebraMap L SeedField c) =
          scalarMap A (algebraMap FX SeedField (algebraMap L[X] FX (algebraMap L L[X] c)))
        rw [← IsScalarTower.algebraMap_apply L L[X] FX, ← IsScalarTower.algebraMap_apply L FX SeedField]
      · simp [rawSection, rawSeedCoeff, sectionX, abscissa]
    intro p
    simpa only [RingHom.comp_apply, seedIntoRaw, MvPolynomial.eval₂Hom_C, rawSeed_C]
      using RingHom.congr_fun hc p
  · intro i
    fin_cases i <;> simp [seedIntoRaw, rawSection]

private theorem ordinate_eval {B : Type*} [CommRing B] (v : MvPolynomial (Fin n) SeedField →+* B)
    (p : FamilyEquation n) :
    v (ordinateForm p) =
      p.eval₂ (Polynomial.eval₂RingHom (v.comp (MvPolynomial.map (algebraMap L SeedField)))
        (v (MvPolynomial.C (algebraMap FX SeedField abscissa))))
        (v (MvPolynomial.C (K1_14_2.generic 1))) := by
  rw [ordinateForm, Polynomial.hom_eval₂, equationAtX, Polynomial.eval₂_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro q
    change v (MvPolynomial.map (algebraMap FX SeedField)
      (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C abscissa)
        (Polynomial.C q))) = _
    simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq L FX SeedField]
  · change v (MvPolynomial.map (algebraMap FX SeedField)
      (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C abscissa)
        Polynomial.X)) = _
    simp

private theorem primitive_eval {B : Type*} [CommRing B]
    (v : CoeffFrac A →+* B) (x y : B) :
    (primitiveEquation A).eval₂ (Polynomial.eval₂RingHom v x) y =
      A.equation.eval₂ (Polynomial.eval₂RingHom (v.comp (toCoeffFrac A)) x) y := by
  rw [primitiveEquation, Polynomial.eval₂_map]
  congr 1
  apply Polynomial.ringHom_ext <;> simp

private theorem rawSection_eq_zero (h : Denominators A) (q : Raw A)
    (hq : rawSpare A q = 0) : rawSection A h q = 0 := by
  let v := Polynomial.eval₂RingHom (coeffToSection A h) (sectionX A)
  let y := scalarMap A (K1_14_2.generic 1)
  have hp : (primitiveEquation A).eval₂ v y = 0 := by
    rw [primitive_eval]
    have hc : (coeffToSection A h).comp (toCoeffFrac A) = sectionParameter A :=
      RingHom.ext (coeffToSection_apply A h)
    rw [hc]
    exact (ordinate_eval (quotientMap A) A.equation).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hm : q.map (rawRoot A) = 0 :=
    IsFractionRing.injective (E A)[X] (T A) (hq.trans (map_zero _).symm)
  have hz : q.map (Polynomial.eval₂RingHom v y) = 0 := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    have hi := congrArg (fun p : (E A)[X] => p.coeff i) hm
    rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hi
    obtain ⟨r, hr⟩ := (rawRoot_eq_zero A _).mp hi
    simp only [hr, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, hp, zero_mul]
  change q.eval₂ (Polynomial.eval₂RingHom v y) _ = 0
  rw [Polynomial.eval₂_eq_eval_map, hz, Polynomial.eval_zero]

private def seedToTarget (h : Denominators A) (hne : Nontrivial (S A)) : SeedField →+* T A :=
  IsFractionRing.lift (g := (rawSpare A).comp (seedIntoRaw A)) (by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [RingHom.ker_eq_bot_iff_eq_zero]
    intro p hp
    have hz := rawSection_eq_zero A h (seedIntoRaw A p) hp
    rw [← RingHom.comp_apply, sectionSeed] at hz
    exact ((scalarMap A).injective.comp (IsFractionRing.injective RawSeed SeedField))
      (hz.trans (map_zero ((scalarMap A).comp (algebraMap RawSeed SeedField))).symm))

private theorem seedToTarget_apply (h : Denominators A) (hne : Nontrivial (S A)) (p : RawSeed) :
    seedToTarget A h hne (algebraMap RawSeed SeedField p) = rawSpare A (seedIntoRaw A p) :=
  IsFractionRing.lift_algebraMap (g := (rawSpare A).comp (seedIntoRaw A)) _ _

private theorem seedToTarget_ordinate (h : Denominators A) (hne : Nontrivial (S A)) :
    IsOrdinateMap (coefficientBase A) (coefficientOrdinate A) (seedToTarget A h hne) := by
  refine ⟨?_, ?_, ?_⟩
  · have hb : (seedToTarget A h hne).comp (algebraMap FX SeedField) =
        (spareConstant (E A)).comp (coefficientBase A) := by
      apply IsFractionRing.ringHom_ext (A := L[X])
      have hc : ((seedToTarget A h hne).comp (algebraMap RawSeed SeedField)).comp MvPolynomial.C =
          ((spareConstant (E A)).comp (coefficientBase A)).comp (algebraMap L[X] FX) := by
        apply Polynomial.ringHom_ext
        · intro c
          rw [RingHom.comp_apply, RingHom.comp_apply, seedToTarget_apply]
          simp only [seedIntoRaw, rawSeedCoeff, rawConstant, rawSpare, RingHom.comp_apply,
            MvPolynomial.eval₂Hom_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
            Polynomial.coe_mapRingHom, Polynomial.map_C, rawRoot, coeffToRoot_toCoeffFrac,
            parameterRoot]
          change spareConstant (E A) (coefficientBase A (algebraMap L FX c)) =
            spareConstant (E A) (coefficientBase A (algebraMap L[X] FX (algebraMap L L[X] c)))
          rw [← IsScalarTower.algebraMap_apply L L[X] FX]
        · rw [RingHom.comp_apply, RingHom.comp_apply, seedToTarget_apply]
          simp [seedIntoRaw, rawSeedCoeff, rawSpare, rawRoot, spareConstant, abscissa]
      intro p
      simpa only [RingHom.comp_apply, rawSeed_C] using RingHom.congr_fun hc p
    exact RingHom.congr_fun hb
  · rw [← rawSeed_X 1, seedToTarget_apply]
    simp [seedIntoRaw, rawSpare, rawRoot, spareConstant]
  · rw [← rawSeed_X 0, seedToTarget_apply]
    simp [seedIntoRaw, rawSpare, spareVariable]

private def evalTarget (h : Denominators A) (hne : Nontrivial (S A)) :
    MvPolynomial (Fin n) SeedField →+* T A :=
  MvPolynomial.eval₂Hom (seedToTarget A h hne) (spareConstant (E A) ∘ coefficientCoordinate A)

private theorem evalTarget_parameter (h : Denominators A) (hne : Nontrivial (S A)) :
    (evalTarget A h hne).comp (MvPolynomial.map (algebraMap L SeedField)) =
      (spareConstant (E A)).comp (parameterRoot A) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, MvPolynomial.map_C, evalTarget, MvPolynomial.eval₂Hom_C, parameterRoot]
    rw [IsScalarTower.algebraMap_apply L FX SeedField, (seedToTarget_ordinate A h hne).1]
  · intro i
    simp [evalTarget, parameterRoot]

private def sectionToTarget (h : Denominators A) (hne : Nontrivial (S A)) : S A →+* T A :=
  Ideal.Quotient.lift _ (evalTarget A h hne) (by
    apply (show _ ≤ RingHom.ker (evalTarget A h hne) from ?_)
    apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro p hp
      change ((evalTarget A h hne).comp (MvPolynomial.map (algebraMap L SeedField))) p = 0
      rw [evalTarget_parameter, RingHom.comp_apply,
        RingHom.mem_ker.mp (show p ∈ RingHom.ker (parameterRoot A) from (parameterRoot_ker A).symm ▸ hp),
        map_zero]
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟩
      change evalTarget A h hne (ordinateForm A.equation) = 0
      rw [ordinate_eval, evalTarget_parameter]
      simp only [evalTarget, MvPolynomial.eval₂Hom_C,
        (seedToTarget_ordinate A h hne).1, (seedToTarget_ordinate A h hne).2.1]
      have hv : (spareConstant (E A)).comp (parameterRoot A) =
          ((spareConstant (E A)).comp (coeffToRoot A)).comp (toCoeffFrac A) :=
        RingHom.ext fun p => by simp
      rw [hv, ← primitive_eval]
      have hr : rawRoot A (primitiveEquation A) = 0 := (rawRoot_eq_zero A _).mpr dvd_rfl
      have hx : Polynomial.eval₂RingHom ((spareConstant (E A)).comp (coeffToRoot A))
          (spareConstant (E A) (coefficientBase A abscissa)) =
          (spareConstant (E A)).comp (Polynomial.eval₂RingHom (coeffToRoot A) (coefficientBase A abscissa)) := by
        apply Polynomial.ringHom_ext <;> simp
      rw [hx, ← Polynomial.hom_eval₂]
      exact (spareConstant (E A)).map_zero' ▸ congrArg (spareConstant (E A)) hr)

private theorem sectionToTarget_scalar (h : Denominators A) (hne : Nontrivial (S A)) :
    (sectionToTarget A h hne).comp (scalarMap A) = seedToTarget A h hne := by
  ext p
  exact MvPolynomial.eval₂Hom_C _ _ _

private theorem sectionToTarget_raw (h : Denominators A) (hne : Nontrivial (S A)) :
    (sectionToTarget A h hne).comp (rawSection A h) = rawSpare A := by
  let e := sectionToTarget A h hne
  let b := seedToTarget A h hne
  have hs : ∀ p, e (scalarMap A p) = b p := RingHom.congr_fun (sectionToTarget_scalar A h hne)
  have ho := seedToTarget_ordinate A h hne
  have hc : e.comp (coeffToSection A h) = (spareConstant (E A)).comp (coeffToRoot A) := by
    apply IsFractionRing.ringHom_ext (A := CoeffRing A)
    intro a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    change e (coeffToSection A h (toCoeffFrac A q)) =
      spareConstant (E A) (coeffToRoot A (toCoeffFrac A q))
    rw [coeffToSection_apply, coeffToRoot_toCoeffFrac]
    exact RingHom.congr_fun (evalTarget_parameter A h hne) q
  have hx : e.comp (Polynomial.eval₂RingHom (coeffToSection A h) (sectionX A)) =
      (spareConstant (E A)).comp (Polynomial.eval₂RingHom (coeffToRoot A) (coefficientBase A abscissa)) := by
    apply Polynomial.ringHom_ext
    · simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using
        RingHom.congr_fun hc
    · simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sectionX, hs]
        using ho.1 abscissa
  have hy : e.comp (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (coeffToSection A h) (sectionX A))
      (scalarMap A (K1_14_2.generic 1))) = (spareConstant (E A)).comp (rawRoot A) := by
    apply Polynomial.ringHom_ext
    · simpa only [RingHom.comp_apply, rawRoot, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using
        RingHom.congr_fun hx
    · simp only [RingHom.comp_apply, rawRoot, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rw [hs]
      exact ho.2.1
  apply Polynomial.ringHom_ext
  · simpa only [RingHom.comp_apply, rawSection, rawSpare, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, spareConstant] using
      RingHom.congr_fun hy
  · simp only [RingHom.comp_apply, rawSection, rawSpare, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
    change e (scalarMap A (K1_14_2.generic 0)) = spareVariable (E A)
    rw [hs]
    exact ho.2.2

private theorem sectionToTarget_injective (h : Denominators A) (hne : Nontrivial (S A)) :
    Function.Injective (sectionToTarget A h hne) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro s hs
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
  let M := (nonZeroDivisors RawSeed).map (MvPolynomial.C (σ := Fin n))
  obtain ⟨⟨q, d⟩, hd⟩ := IsLocalization.surj M f
  obtain ⟨a, ha, had⟩ := d.prop
  have he : (quotientMap A).comp (algebraMap (MvPolynomial (Fin n) RawSeed) (MvPolynomial (Fin n) SeedField)) =
      (rawSection A h).comp (MvPolynomial.eval₂Hom (seedIntoRaw A)
        (Polynomial.C ∘ Polynomial.C ∘ Polynomial.C ∘ toCoeffFrac A ∘ MvPolynomial.X)) := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C,
        MvPolynomial.eval₂Hom_C]
      exact (RingHom.congr_fun (sectionSeed A h) p).symm
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X,
        MvPolynomial.eval₂Hom_X', Function.comp_apply, rawSection, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, coeffToSection_apply, sectionParameter]
  let r : Raw A := MvPolynomial.eval₂Hom (seedIntoRaw A)
    (Polynomial.C ∘ Polynomial.C ∘ Polynomial.C ∘ toCoeffFrac A ∘ MvPolynomial.X) q
  have hmul : quotientMap A f * scalarMap A (algebraMap RawSeed SeedField a) = rawSection A h r := by
    let m := algebraMap (MvPolynomial (Fin n) RawSeed) (MvPolynomial (Fin n) SeedField)
    calc
      _ = quotientMap A (f * m d) := by
        rw [map_mul, ← had, show m = MvPolynomial.map (algebraMap RawSeed SeedField) from rfl,
          MvPolynomial.map_C]
        rfl
      _ = ((quotientMap A).comp m) q := congrArg (quotientMap A) hd
      _ = _ := RingHom.congr_fun he q
  have hzero : rawSpare A r = 0 := by
    rw [← RingHom.congr_fun (sectionToTarget_raw A h hne) r, RingHom.comp_apply, ← hmul, map_mul]
    rw [show sectionToTarget A h hne (quotientMap A f) = 0 from hs, zero_mul]
  rw [rawSection_eq_zero A h r hzero] at hmul
  exact ((IsLocalization.map_units SeedField ⟨a, ha⟩).map (scalarMap A)).mul_left_eq_zero.mp hmul

private theorem sectionToTarget_surjective (h : Denominators A) (hne : Nontrivial (S A))
    (hf : Module.Finite SeedField (S A)) : Function.Surjective (sectionToTarget A h hne) := by
  let e := sectionToTarget A h hne
  let : IsDomain (S A) := (sectionToTarget_injective A h hne).isDomain e
  let : Field (S A) := (IsField.of_isDomain_of_finite SeedField (S A)).toField
  let U := e.fieldRange
  let : Algebra FX (RootField R) := (rootBase R).toAlgebra
  let V : IntermediateField FX (RootField R) :=
    { (U.comap (spareConstant (E A))).map (coefficientRootInclusion A) with
      algebraMap_mem' := fun x => ⟨coefficientBase A x,
        ⟨scalarMap A (algebraMap FX SeedField x), by
          rw [← (seedToTarget_ordinate A h hne).1 x]
          exact RingHom.congr_fun (sectionToTarget_scalar A h hne) _⟩, rfl⟩ }
  have hraw (q : EquationRing A) : spareConstant (E A) (rawRoot A q) ∈ U :=
    ⟨rawSection A h (Polynomial.C q), by
      simpa only [RingHom.comp_apply, rawSpare, Polynomial.coe_mapRingHom, Polynomial.map_C, spareConstant]
        using RingHom.congr_fun (sectionToTarget_raw A h hne) (Polynomial.C q)⟩
  have hV : coefficientRoot A ≤ V := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ (⟨i, rfl⟩ | hi)
    · refine ⟨coefficientCoordinate A i, ?_, rfl⟩
      simpa [rawRoot, parameterRoot] using
        hraw (Polynomial.C (Polynomial.C (toCoeffFrac A (MvPolynomial.X i))))
    · obtain rfl := Set.mem_singleton_iff.mp hi
      refine ⟨coefficientOrdinate A, ?_, rfl⟩
      simpa [rawRoot] using hraw Polynomial.X
  have hconst (a : E A) : spareConstant (E A) a ∈ U := by
    obtain ⟨v, hv, heq⟩ := hV a.property
    exact (coefficientRootInclusion A).injective heq ▸ hv
  have ht : spareVariable (E A) ∈ U :=
    ⟨scalarMap A (K1_14_2.generic 0), (RingHom.congr_fun (sectionToTarget_scalar A h hne) _).trans
      (seedToTarget_ordinate A h hne).2.2⟩
  intro z
  change z ∈ U
  have hpoly : Set.range (algebraMap (E A)[X] (T A)) ⊆ U := by
    rintro _ ⟨p, rfl⟩
    let v := Polynomial.eval₂RingHom ((spareConstant (E A)).codRestrict U.toSubring hconst)
      (⟨spareVariable (E A), ht⟩ : U.toSubring)
    have hv : U.toSubring.subtype.comp v = algebraMap (E A)[X] (T A) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [v, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        rfl
      · simp only [v, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        rfl
    exact (RingHom.congr_fun hv p) ▸ (v p).property
  have hall : (⊤ : Subfield (T A)) ≤ U := by
    rw [← IsFractionRing.closure_range_algebraMap (E A)[X] (T A)]
    exact Subfield.closure_le.mpr hpoly
  exact hall (Subfield.mem_top _)

theorem proof : K1_14_2_4_1_3_3.c1 := by
  intro C₀ _ J g n R A _ hfin hne hd
  let e := sectionToTarget A hd hne
  refine ⟨RingEquiv.ofBijective e
    ⟨sectionToTarget_injective A hd hne, sectionToTarget_surjective A hd hne hfin⟩, ?_⟩
  change IsOrdinateMap (coefficientBase A) (coefficientOrdinate A)
    ((sectionToTarget A hd hne).comp (scalarMap A))
  exact (sectionToTarget_scalar A hd hne).symm ▸ seedToTarget_ordinate A hd hne

end
end K1_14_2_4_1_3_3_1
end PackSource_K1_14_2_4_1_3_3_1Proof

section PackSource_K1_13_5_5_2_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_5_2_2

noncomputable section

open MvPolynomial

variable {k σ : Type*} [Field k]

/-- The annihilator of the class of `f` in the quotient by `I`. -/
def cyclicAnnihilator (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    Ideal (MvPolynomial σ k) :=
  I.colon (Ideal.span {f})

/-- The ideal obtained by adjoining the cyclic generator. -/
def cyclicCut (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    Ideal (MvPolynomial σ k) :=
  I ⊔ Ideal.span {f}

theorem mem_cyclicAnnihilator {I : Ideal (MvPolynomial σ k)} {f a : MvPolynomial σ k} :
    a ∈ cyclicAnnihilator I f ↔ a * f ∈ I :=
  Ideal.mem_colon_span_singleton

theorem le_cyclicAnnihilator (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    I ≤ cyclicAnnihilator I f :=
  fun _ ha ↦ mem_cyclicAnnihilator.mpr (I.mul_mem_right f ha)

theorem le_cyclicCut (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    I ≤ cyclicCut I f := le_sup_left

end

end K1_13_5_5_2_2
end PackSource_K1_13_5_5_2_2Defs

section PackSource_K1_13_5_5_2_2Filtration
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_5_2_2

open MvPolynomial
open K1_13_5_5_2

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem infinityIdeal_homogeneous (I : Ideal (MvPolynomial σ k)) :
    (infinityIdeal I).IsHomogeneous (homogeneousSubmodule σ k) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨f, _, rfl⟩
  exact ⟨f.totalDegree, homogeneousComponent_mem _ _⟩

theorem cyclicCut_homogeneous {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k} {d : ℕ}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (hf : f.IsHomogeneous d) :
    (cyclicCut I f).IsHomogeneous (homogeneousSubmodule σ k) := by
  apply hI.sup
  apply Ideal.homogeneous_span
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact ⟨d, hf⟩

theorem cyclicCut_lt {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hf : f ∉ I) : I < cyclicCut I f := by
  refine lt_of_le_not_ge (le_cyclicCut I f) (fun h ↦ hf (h ?_))
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)

theorem cyclicAnnihilator_homogeneous {I : Ideal (MvPolynomial σ k)}
    {f : MvPolynomial σ k} {d : ℕ}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (hf : f.IsHomogeneous d) :
    (cyclicAnnihilator I f).IsHomogeneous (homogeneousSubmodule σ k) := by
  intro i a ha
  rw [mem_cyclicAnnihilator] at ha ⊢
  have hm := hI (i + d) ha
  rwa [DirectSum.coe_decompose_mul_add_of_right_mem (homogeneousSubmodule σ k) hf] at hm

/-- A maximal annihilator of a nonzero homogeneous class is prime. Each step
from a proper homogeneous ideal thereby contributes a homogeneous prime factor. -/
theorem exists_homogeneous_prime_step [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (hproper : I ≠ ⊤) :
    ∃ (d : ℕ) (f : MvPolynomial σ k),
      f.IsHomogeneous d ∧ f ∉ I ∧ (cyclicAnnihilator I f).IsPrime := by
  classical
  let candidates : Set (Ideal (MvPolynomial σ k)) :=
    {Q | ∃ (d : ℕ) (f : MvPolynomial σ k),
      f.IsHomogeneous d ∧ f ∉ I ∧ Q = cyclicAnnihilator I f}
  have hone : (1 : MvPolynomial σ k) ∉ I :=
    fun h ↦ hproper (Ideal.eq_top_of_isUnit_mem I h isUnit_one)
  obtain ⟨_, ⟨d, f, hf, hfI, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherianRing (MvPolynomial σ k)) candidates
      ⟨cyclicAnnihilator I 1, 0, 1, isHomogeneous_one _ _, hone, rfl⟩
  refine ⟨d, f, hf, hfI, (cyclicAnnihilator_homogeneous hI hf).isPrime_of_homogeneous_mem_or_mem
    ?_ ?_⟩
  · intro htop
    apply hfI
    simpa using mem_cyclicAnnihilator.mp
      (show (1 : MvPolynomial σ k) ∈ cyclicAnnihilator I f by rw [htop]; trivial)
  · intro a b ha _ hab
    by_cases haI : a ∈ cyclicAnnihilator I f
    · exact Or.inl haI
    · apply Or.inr
      have hle : cyclicAnnihilator I f ≤ cyclicAnnihilator I (a * f) := by
        intro c hc
        apply mem_cyclicAnnihilator.mpr
        rw [mul_left_comm]
        exact I.mul_mem_left a (mem_cyclicAnnihilator.mp hc)
      obtain ⟨e, he⟩ := ha
      have hmem : cyclicAnnihilator I (a * f) ∈ candidates :=
        ⟨e + d, a * f, he.mul hf, mt mem_cyclicAnnihilator.mpr haI, rfl⟩
      rw [hle.eq_of_not_lt (hmax _ hmem)]
      exact mem_cyclicAnnihilator.mpr (by rw [← mul_assoc, mul_comm b a]; exact mem_cyclicAnnihilator.mp hab)

end K1_13_5_5_2_2
end PackSource_K1_13_5_5_2_2Filtration

section PackSource_K1_14_2_4_1_3_1Boundary
set_option autoImplicit true
namespace K1_14_2_4_1_3_1

noncomputable section

open MvPolynomial K1_13_6_3_4 K1_14_2_4_1_3

set_option maxHeartbeats 1000000

private theorem boundary_of_valueReduction {k σ : Type*} [Field k] [Finite σ]
    {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k} (hf : f.totalDegree ≤ 1)
    (hd : (affineHilbertPolynomial I).natDegree ≤ 1)
    (h : ValueReduction I (homogeneousComponent 1 f)) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ x ∈ quotientDegreeLE I (d + 1),
      Ideal.Quotient.mk I f * x ∈ quotientDegreeLE I (d + 1) → x ∈ quotientDegreeLE I d := by
  have hc : f - homogeneousComponent 1 f = MvPolynomial.C (f.coeff 0) := by
    classical
    ext m
    rw [coeff_sub, coeff_homogeneousComponent, coeff_C]
    by_cases hm : m = 0
    · subst m
      simp
    by_cases hn : m.degree = 1
    · simp [hn, Ne.symm hm]
    have hz : f.coeff m = 0 := coeff_eq_zero_of_totalDegree_lt
      (show f.totalDegree < m.degree from by
        have h0 : m.degree ≠ 0 := fun he => hm ((Finsupp.degree_eq_zero_iff m).mp he)
        omega)
    simp [hn, Ne.symm hm, hz]
  obtain ⟨N, hN⟩ := h
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial I
  refine ⟨max N M, fun d hdm x hx hfx => ?_⟩
  let U := quotientDegreeLE I d
  let V := quotientDegreeLE I (d + 1)
  let W := quotientDegreeLE I (d + 2)
  let U' := U.comap V.subtype
  let V' := V.comap W.subtype
  have hUV : U ≤ V := quotientDegreeLE_mono I (by omega)
  have hVW : V ≤ W := quotientDegreeLE_mono I (by omega)
  let μ : V →ₗ[k] W := ((LinearMap.mulLeft k (Ideal.Quotient.mk I f)).domRestrict V).codRestrict W
    (fun z => by
      change Ideal.Quotient.mk I f * z.val ∈ quotientDegreeLE I (d + 2)
      simpa only [Nat.add_comm 1, Nat.add_assoc] using
        (mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE (I := I) hf) z.property))
  let φ := V'.mkQ.comp μ
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨z, rfl⟩ := V'.mkQ_surjective q
    obtain ⟨a, ha, b, hb, he⟩ := hN (d + 1) (by omega) z.val z.property
    refine ⟨⟨b, hb⟩, ?_⟩
    change V'.mkQ (μ ⟨b, hb⟩) = V'.mkQ z
    apply (Submodule.Quotient.eq V').mpr
    change Ideal.Quotient.mk I f * b - z.val ∈ V
    rw [he, sub_add_eq_sub_sub, sub_right_comm, ← sub_mul, ← map_sub, hc]
    have hC : Ideal.Quotient.mk I (MvPolynomial.C (f.coeff 0)) ∈ quotientDegreeLE I 0 :=
      mk_mem_quotientDegreeLE (totalDegree_C _).le
    exact V.sub_mem (by simpa only [zero_add] using mul_mem_quotientDegreeLE hC hb) ha
  have hk : U' ≤ LinearMap.ker φ := by
    intro z hz
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by
      change Ideal.Quotient.mk I f * z.val ∈ quotientDegreeLE I (d + 1)
      simpa only [Nat.add_comm 1] using
        (mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE (I := I) hf) (show z.val ∈ U from hz)))
  have hnull := φ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hφ, finrank_top] at hnull
  have hquot := V'.finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hVW).finrank_eq] at hquot
  have hlinear : Module.finrank k W + Module.finrank k U = 2 * Module.finrank k V := by
    change affineHilbertFunction I (d + 2) + affineHilbertFunction I d =
      2 * affineHilbertFunction I (d + 1)
    have hP (z : ℚ) : (affineHilbertPolynomial I).eval z =
        (affineHilbertPolynomial I).coeff 1 * z + (affineHilbertPolynomial I).coeff 0 := by
      nth_rw 1 [Polynomial.eq_X_add_C_of_natDegree_le_one hd]
      simp
    have h (i : ℕ) : (affineHilbertFunction I (d + i) : ℚ) =
        (affineHilbertPolynomial I).coeff 1 * ((d : ℚ) + i) +
        (affineHilbertPolynomial I).coeff 0 := by
      rw [← hM (d + i) (by omega), hP, Nat.cast_add]
    have hr := h 0
    simp only [Nat.cast_zero, add_zero] at hr
    exact_mod_cast (show (affineHilbertFunction I (d + 2) : ℚ) + affineHilbertFunction I d =
      2 * affineHilbertFunction I (d + 1) by rw [h 2, hr, h 1]; push_cast; ring)
  have heq : U' = LinearMap.ker φ := Submodule.eq_of_le_of_finrank_eq hk (by
    rw [(Submodule.comapSubtypeEquivOfLe hUV).finrank_eq]
    omega)
  have hx' : (⟨x, hx⟩ : V) ∈ LinearMap.ker φ := LinearMap.mem_ker.mpr
    ((Submodule.Quotient.mk_eq_zero _).mpr hfx)
  rw [← heq] at hx'
  exact hx'

section Geometry

variable {k E F σ ι : Type*} [Field k] [Field E] [Field F]

private theorem map_component (a : k →+* E) (p : MvPolynomial σ k) (d : ℕ) :
    map a (homogeneousComponent d p) = homogeneousComponent d (map a p) := by
  ext m
  by_cases hm : m.degree = d <;>
    simp only [coeff_map, coeff_homogeneousComponent, hm, ite_true, ite_false, map_zero]

private theorem totalDegree_map_le (a : k →+* E) (p : MvPolynomial σ k) :
    (map a p).totalDegree ≤ p.totalDegree :=
  Finset.sup_mono (support_map_subset a p)

variable [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]

private theorem boundary_map_le (I : Ideal (MvPolynomial σ k)) :
    (boundaryIdeal I).map (map (algebraMap k E)) ≤ boundaryIdeal (extendedIdeal E I) := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨p, d, hp, hd, rfl⟩
  change map _ (homogeneousComponent d p) ∈ boundaryIdeal _
  rw [map_component]
  exact Ideal.subset_span ⟨map _ p, d, Ideal.mem_map_of_mem _ hp,
    (totalDegree_map_le _ _).trans hd, rfl⟩

private theorem eval_map_point (p : MvPolynomial σ k) (b : σ → F) :
    aeval b (map (algebraMap k E) p) = (aeval b p : F) := by
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq, ← aeval_def]

private theorem eval_scale [Fintype σ] {p : MvPolynomial σ k} {d : ℕ}
    (hp : p.IsHomogeneous d) (x : σ → F) (t : F) :
    (aeval (fun i => t * x i) p : F) = t ^ d * aeval x p := by
  classical
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have he : m.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  rw [show (∏ i : σ, (t * x i) ^ m i) = t ^ d * ∏ i : σ, x i ^ m i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, he]]
  ac_rfl

/-- A nonzero boundary point of a curve has a direction defined over the constant field. -/
private theorem normalize [Fintype σ] [LinearOrder σ] [WellFoundedGT σ] [IsAlgClosed k]
    (I : Ideal (MvPolynomial σ k)) (hd : (affineHilbertPolynomial I).natDegree = 1)
    {x : σ → F} (hx : x ∈ zeroLocus F (boundaryIdeal (extendedIdeal E I)))
    {i : σ} (hi : x i ≠ 0) :
    ∃ b : σ → k, b ∈ zeroLocus k (boundaryIdeal I) ∧ b i = 1 ∧
      (algebraMap k F ∘ b) = fun j => (x i)⁻¹ * x j := by
  let y : σ → F := fun j => (x i)⁻¹ * x j
  have hy : y i = 1 := inv_mul_cancel₀ hi
  have hx' : x ∈ zeroLocus F (boundaryIdeal I) := by
    intro p hp
    rw [← eval_map_point (E := E)]
    exact hx _ (boundary_map_le I (Ideal.mem_map_of_mem _ hp))
  have hyB : boundaryIdeal I ≤ RingHom.ker (aeval y).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, d, hp, hn, rfl⟩
    change (aeval y (homogeneousComponent d p) : F) = 0
    rw [eval_scale (homogeneousComponent_isHomogeneous ..), hx' _ (Ideal.subset_span
      ⟨p, d, hp, hn, rfl⟩), mul_zero]
  have hyC : y ∈ zeroLocus F (boundaryChart I i) := by
    change boundaryChart I i ≤ RingHom.ker (aeval y).toRingHom
    refine sup_le hyB (Ideal.span_le.mpr ?_)
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    change (aeval y (MvPolynomial.X i - 1 : MvPolynomial σ k) : F) = 0
    simp [hy]
  let J := boundaryChart I i
  let : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero
      (K1_13_5_4_4_2.boundaryChart_dimension I hd i)
  let e : (MvPolynomial σ k ⧸ J) →ₐ[k] F := Ideal.Quotient.liftₐ J (aeval y) hyC
  have hroot (j : σ) : IsIntegral k (y j) := by
    have h := (Algebra.IsIntegral.isIntegral (R := k)
      (Ideal.Quotient.mk J (MvPolynomial.X j))).map e
    change IsIntegral k ((aeval y) (MvPolynomial.X j : MvPolynomial σ k)) at h
    simpa only [aeval_X] using h
  have hconstant (j : σ) : ∃ b : k, algebraMap k F b = y j := by
    apply (hroot j).mem_range_algHom_of_minpoly_splits (K := k) _ (Algebra.ofId k F)
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using IsAlgClosed.splits (minpoly k (y j))
  choose b hb using hconstant
  have hb' : algebraMap k F ∘ b = y := funext hb
  refine ⟨b, ?_, (algebraMap k F).injective ((hb i).trans (hy.trans (map_one _).symm)), hb'⟩
  intro p hp
  apply (algebraMap k F).injective
  rw [map_zero]
  change (Algebra.ofId k F) (aeval b p) = 0
  rw [MvPolynomial.comp_aeval_apply, show (fun i => (Algebra.ofId k F) (b i)) = y from hb']
  exact hyB hp

private theorem point_of_prime [Fintype σ] [IsAlgClosed k]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime) :
    ∃ b : σ → k, b ∈ zeroLocus k I := by
  by_contra! h
  have hZ : zeroLocus k I = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
  let : I.IsPrime := hI
  have he := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := k) I
  rw [hZ] at he
  apply hI.ne_top
  rw [← he]
  exact top_unique fun p _ b hb => False.elim hb

/-- A linear combination with independent weights has no cancellation on constant points. -/
private theorem eval_combination [Fintype ι] (p : ι → MvPolynomial σ k) (w : ι → E)
    (hw : LinearIndependent k w) (b : σ → k)
    (h : (eval (algebraMap k E ∘ b))
      (∑ s, MvPolynomial.C (w s) * map (algebraMap k E) (p s)) = 0) :
    ∀ s, eval b (p s) = 0 := by
  apply (Fintype.linearIndependent_iff.mp hw) (fun s => eval b (p s))
  rw [map_sum] at h
  simpa only [map_mul, eval_C, eval_map, ← MvPolynomial.eval₂_comp,
    Algebra.smul_def, mul_comm] using h

/-- The same two tests apply to the parameter weights and to the ordinate monomials. -/
theorem regular_generic_cut [Fintype σ] [LinearOrder σ] [WellFoundedGT σ] [Fintype ι]
    [IsAlgClosed k] (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime)
    (p : ι → MvPolynomial σ k) (w : ι → E) (hw : LinearIndependent k w)
    (hp : ∀ s, (p s).totalDegree ≤ 1)
    (haff : ∀ b ∈ zeroLocus k I, ∃ s, eval b (p s) ≠ 0)
    (hinf : ∀ b ∈ zeroLocus k (boundaryIdeal I),
      (∀ s, eval b (homogeneousComponent 1 (p s)) = 0) → b = 0)
    (hd : (affineHilbertPolynomial I).natDegree ≤ 1) :
    RegularLinearCut (extendedIdeal E I)
      (∑ s, MvPolynomial.C (w s) * map (algebraMap k E) (p s)) := by
  let J := extendedIdeal E I
  let f : MvPolynomial σ E := ∑ s, MvPolynomial.C (w s) * map (algebraMap k E) (p s)
  have hf : f.totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro s _
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_map_le _ _).trans (hp s)
  have hJ : J.IsPrime := K1_13_6_3_5_2.isPrime_map I hI
  have hne : Ideal.Quotient.mk J f ≠ 0 := by
    obtain ⟨b, hb⟩ := point_of_prime I hI
    obtain ⟨s, hs⟩ := haff b hb
    have hb' : (algebraMap k E ∘ b) ∈ zeroLocus E J := by
      change J ≤ RingHom.ker (aeval (algebraMap k E ∘ b)).toRingHom
      apply Ideal.map_le_iff_le_comap.mpr
      intro q hq
      change (aeval _ (map (algebraMap k E) q) : E) = 0
      rw [eval_map_point]
      change (aeval (fun i => (Algebra.ofId k E) (b i)) q : E) = 0
      rw [← MvPolynomial.comp_aeval_apply b (Algebra.ofId k E), hb q hq, map_zero]
    intro hz
    apply hs
    exact eval_combination p w hw b (by
      rw [← aeval_eq_eval]
      exact hb' f (Ideal.Quotient.eq_zero_iff_mem.mp hz)) s
  refine ⟨hf, (IsRegular.of_ne_zero hne).1, ?_⟩
  have hdJ : affineHilbertPolynomial J = affineHilbertPolynomial I :=
    K1_13_5_5_2.hilbertPolynomial_map I
  by_cases hz : (affineHilbertPolynomial I).natDegree = 0
  · let : Module.Finite E (MvPolynomial σ E ⧸ J) :=
      moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero (hdJ.symm ▸ hz)
    obtain ⟨N, hN⟩ := exists_quotientDegreeLE_eq_top J
    exact ⟨N, fun d hd x _ _ => by rw [hN d hd]; trivial⟩
  have hdim : (affineHilbertPolynomial I).natDegree = 1 := by omega
  let l := homogeneousComponent 1 f
  have hreduce : ValueReduction J l := by
    apply K1_13_5_4_4_2.valueReduction_of_geometric (K := AlgebraicClosure E) _
      (homogeneousComponent_isHomogeneous ..)
    intro x hx hval
    funext i
    change x i = 0
    by_contra hi
    obtain ⟨b, hb, hbi, he⟩ := normalize I hdim hx hi
    have hcut : (aeval (algebraMap k (AlgebraicClosure E) ∘ b) l : AlgebraicClosure E) = 0 := by
      rw [he, eval_scale (homogeneousComponent_isHomogeneous ..), hval, mul_zero]
    have heval : eval (algebraMap k E ∘ b) l = 0 := by
      apply (algebraMap E (AlgebraicClosure E)).injective
      rw [map_zero, ← aeval_eq_eval]
      change (Algebra.ofId E (AlgebraicClosure E)) (aeval _ l) = 0
      rw [MvPolynomial.comp_aeval_apply]
      change (aeval (fun i => algebraMap E (AlgebraicClosure E) (algebraMap k E (b i))) l :
        AlgebraicClosure E) = 0
      simp_rw [← IsScalarTower.algebraMap_apply k E (AlgebraicClosure E)]
      exact hcut
    have hl : l = ∑ s, MvPolynomial.C (w s) *
        map (algebraMap k E) (homogeneousComponent 1 (p s)) := by
      simp only [l, f, map_sum, homogeneousComponent_C_mul, map_component]
    rw [hl] at heval
    have hb0 := hinf b hb (eval_combination _ w hw b heval)
    rw [hb0] at hbi
    exact zero_ne_one hbi
  exact boundary_of_valueReduction hf (hdJ ▸ hd) hreduce

end Geometry

end
end K1_14_2_4_1_3_1
end PackSource_K1_14_2_4_1_3_1Boundary

section PackSource_K1_13_5_5_2_2Initial
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_5_2_2

open MvPolynomial K1_13_5_5_2 K1_13_6_3_4

variable {k σ : Type*} [Field k]

/-- Allowing a degree bound above the actual degree only adds zero generators. -/
theorem infinityIdeal_eq_boundaryIdeal (I : Ideal (MvPolynomial σ k)) :
    infinityIdeal I = boundaryIdeal I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    exact Ideal.subset_span ⟨f, f.totalDegree, hf, le_rfl, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, n, hf, hn, rfl⟩
    rcases eq_or_lt_of_le hn with h | h
    · subst n
      exact Ideal.subset_span ⟨f, hf, rfl⟩
    · rw [homogeneousComponent_eq_zero _ _ h]
      exact Ideal.zero_mem _

/-- The top-form scheme has the same cumulative Hilbert polynomial. -/
theorem hilbertPolynomial_infinityIdeal [LinearOrder σ] [WellFoundedGT σ] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    affineHilbertPolynomial (infinityIdeal I) = affineHilbertPolynomial I :=
  (congrArg affineHilbertPolynomial (infinityIdeal_eq_boundaryIdeal I)).trans
    (K1_13_5_4_4_2.hilbertPolynomial_boundary I)

end K1_13_5_5_2_2
end PackSource_K1_13_5_5_2_2Initial

section PackSource_K1_13_5_5_2_2Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_5_2_2

noncomputable section

open K1_13 K1_13_5_5 K1_13_5_5_2 MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous cyclic subquotient adds its Hilbert polynomial with its grading shifted. -/
def c1 : Prop :=
  ∀ (I : Ideal CoeffRing) (f : CoeffRing) (d : ℕ),
    I.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom) →
    f.IsHomogeneous d → f ∉ I → (cyclicAnnihilator I f).IsPrime →
    affineHilbertPolynomial I =
      affineHilbertPolynomial (cyclicCut I f) +
        Polynomial.taylor (-(d : ℚ)) (affineHilbertPolynomial (cyclicAnnihilator I f))

/-- After the fresh extension and generic localization, dimensions add in the
same cyclic exact sequence. The quotient fiber stays finite. -/
def c2 : Prop :=
  ∀ (I : Ideal CoeffRing) (f : CoeffRing) (L : Fin 2 → FreshJetRing),
    Module.Finite PairField (genericFiber L (freshIdeal I)) →
    Module.Finite PairField (genericFiber L (freshIdeal (cyclicCut I f))) ∧
      genericFiberDimension L (freshIdeal I) =
        genericFiberDimension L (freshIdeal (cyclicCut I f)) +
        genericFiberDimension L (freshIdeal (cyclicAnnihilator I f))

private theorem affineDegree_eq_twice_coeff {I : Ideal CoeffRing}
    (h : (affineHilbertPolynomial I).natDegree = 2) :
    affineDegree I = 2 * (affineHilbertPolynomial I).coeff 2 := by
  norm_num [affineDegree, Polynomial.leadingCoeff, h]

/-- Iterate the cyclic exact sequences, keeping the degree-two factors
with their repetitions. -/
private theorem collect_top_factors (hHilbert : c1) (hFiber : c2) (I : Ideal CoeffRing) :
    I.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom) →
    (affineHilbertPolynomial I).natDegree ≤ 2 →
    ∃ (n : ℕ) (Q : Fin n → Ideal CoeffRing),
      (∀ i, I ≤ Q i ∧ (Q i).IsPrime ∧
        (Q i).IsHomogeneous (homogeneousSubmodule CoeffIndex Geom) ∧
        (affineHilbertPolynomial (Q i)).natDegree = 2) ∧
      (2 : ℚ) * (affineHilbertPolynomial I).coeff 2 = ∑ i, affineDegree (Q i) ∧
      ∀ (L : Fin 2 → FreshJetRing), Module.Finite PairField (genericFiber L (freshIdeal I)) →
        (∑ i, genericFiberDimension L (freshIdeal (Q i))) ≤
          genericFiberDimension L (freshIdeal I) := by
  classical
  have : WellFoundedGT (Ideal CoeffRing) :=
    isNoetherian_iff.mp (inferInstance : IsNoetherianRing CoeffRing)
  induction I using WellFoundedGT.induction with
  | ind I ih =>
    intro hI hdim
    by_cases htop : I = ⊤
    · subst I
      exact ⟨0, Fin.elim0, fun i ↦ i.elim0, by simp, fun L _ ↦ by simp⟩
    obtain ⟨d, f, hf, hfI, hprime⟩ := exists_homogeneous_prime_step hI htop
    let J := cyclicCut I f
    let R := cyclicAnnihilator I f
    have hIJ : I ≤ J := le_cyclicCut I f
    have hIR : I ≤ R := le_cyclicAnnihilator I f
    have hdimJ := (natDegree_affineHilbertPolynomial_le_of_le hIJ).trans hdim
    have hdimR := (natDegree_affineHilbertPolynomial_le_of_le hIR).trans hdim
    obtain ⟨n, Q, hQ, hcoeffJ, hboundJ⟩ :=
      ih J (cyclicCut_lt hfI) (cyclicCut_homogeneous hI hf) hdimJ
    have hcoeff : (affineHilbertPolynomial I).coeff 2 =
        (affineHilbertPolynomial J).coeff 2 + (affineHilbertPolynomial R).coeff 2 := by
      rw [hHilbert I f d hI hf hfI hprime, Polynomial.coeff_add, Polynomial.coeff_taylor_of_natDegree_le _ hdimR]
    by_cases he : (affineHilbertPolynomial R).natDegree = 2
    · refine ⟨n + 1, Fin.cons R Q, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa only [Fin.cons_zero] using And.intro hIR
            (And.intro hprime (And.intro (cyclicAnnihilator_homogeneous hI hf) he))
        · obtain ⟨hJQ, hq, hhom, hdegree⟩ := hQ j
          simpa only [Fin.cons_succ] using And.intro (hIJ.trans hJQ)
            (And.intro hq (And.intro hhom hdegree))
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [hcoeff, mul_add, hcoeffJ, affineDegree_eq_twice_coeff he]
        exact add_comm _ _
      · intro L hfinite
        obtain ⟨hfiniteJ, hdimEq⟩ := hFiber I f L hfinite
        rw [Fin.sum_univ_succ, Fin.cons_zero, hdimEq, add_comm
          (genericFiberDimension L (freshIdeal J))]
        simp only [Fin.cons_succ]
        exact Nat.add_le_add_left (hboundJ L hfiniteJ) _
    · refine ⟨n, Q, fun i ↦ ⟨hIJ.trans (hQ i).1, (hQ i).2⟩, ?_, ?_⟩
      · rw [hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hdimR he), add_zero]
        exact hcoeffJ
      · intro L hfinite
        obtain ⟨hfiniteJ, hdimEq⟩ := hFiber I f L hfinite
        rw [hdimEq]
        exact (hboundJ L hfiniteJ).trans (Nat.le_add_right _ _)

private theorem minimalPrime_of_dim (I Q : Ideal CoeffRing) (hIQ : I ≤ Q)
    (hQ : Q.IsPrime) (hdim : (affineHilbertPolynomial I).natDegree ≤ 2)
    (hQdim : (affineHilbertPolynomial Q).natDegree = 2) :
    Q ∈ I.minimalPrimes := by
  refine ⟨⟨hQ, hIQ⟩, ?_⟩
  intro R hR hRQ
  by_contra hQR
  obtain ⟨f, hfQ, hfR⟩ := Set.not_subset.mp
    (show ¬ (Q : Set CoeffRing) ⊆ (R : Set CoeffRing) from hQR)
  have hcut : R ⊔ Ideal.span {f} ≤ Q := sup_le hRQ (Q.span_singleton_le_iff_mem.mpr hfQ)
  have hQle := natDegree_affineHilbertPolynomial_le_of_le hcut
  have hdrop :=
    (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hR.1 hfR (b := f.totalDegree) le_rfl).1
  have hRdim := (natDegree_affineHilbertPolynomial_le_of_le hR.2).trans hdim
  omega

theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_5_2.c2 := by
  intro P _ hdim
  have hpoly := hilbertPolynomial_infinityIdeal P
  have hinf : (affineHilbertPolynomial (infinityIdeal P)).natDegree = 2 := by
    rw [hpoly, hdim]
  obtain ⟨n, Q, hQ, hcoeff, hfiber⟩ :=
    collect_top_factors h1 h2 (infinityIdeal P) (infinityIdeal_homogeneous P) hinf.le
  refine ⟨n, Q, ?_, ?_, hfiber⟩
  · intro i
    obtain ⟨hle, hprime, hhom, hd⟩ := hQ i
    exact ⟨minimalPrime_of_dim _ _ hle hprime hinf.le hd, hhom, hd⟩
  · rw [hpoly] at hcoeff
    exact (affineDegree_eq_twice_coeff hdim).trans hcoeff

end

end K1_13_5_5_2_2
end PackSource_K1_13_5_5_2_2Split

section PackSource_K1_13_5_5_2_1_4_1Proof
set_option autoImplicit true
namespace K1_13_5_5_2_1_4_1

noncomputable section

open MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1500000

private theorem eval_scale {k T σ : Type} [Field k] [CommRing T] [Algebra k T]
    (v : σ → T) (u : T) {p : MvPolynomial σ k} {n : ℕ} (hp : p.IsHomogeneous n) :
    aeval (fun j => u * v j) p = u ^ n * aeval v p := by
  classical
  have he := (homogeneousComponent_eq_self hp).symm.trans (homogeneousComponent_apply n p)
  simp only [aeval_eq_eval₂Hom]
  rw [he, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d.degree = n := (Finset.mem_filter.mp hd).2
  simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  change d.support.sum d = n at hdeg
  rw [hdeg]
  ac_rfl

/-- For a homogeneous relation, simultaneous scaling preserves its vanishing. -/
private theorem scaled_kills {k T σ : Type} [Field k] [CommRing T] [Algebra k T]
    {Q : Ideal (MvPolynomial σ k)} (hQ : Q.IsHomogeneous (homogeneousSubmodule σ k))
    (v : σ → T) (u : T) (h : ∀ p ∈ Q, aeval v p = 0) :
    ∀ p ∈ Q, aeval (fun j => u * v j) p = 0 := by
  intro p hp
  rw [← sum_homogeneousComponent p, map_sum]
  apply Finset.sum_eq_zero
  intro n _
  rw [eval_scale v u (homogeneousComponent_isHomogeneous _ _),
    h _ (homogeneousComponent_mem_of_mem hQ hp n), mul_zero]

private theorem scaled_extension_kills {k F T σ : Type} [Field k] [Field F] [CommRing T]
    [Algebra k F] [Algebra k T] [Algebra F T] [IsScalarTower k F T]
    {Q : Ideal (MvPolynomial σ k)} (hQ : Q.IsHomogeneous (homogeneousSubmodule σ k))
    (v : σ → T) (u : T) (h : ∀ p ∈ Q, aeval v p = 0) :
    ∀ p ∈ Q.map (MvPolynomial.map (algebraMap k F)),
      aeval (R := F) (fun j => u * v j) p = 0 := by
  let : IsScalarTower k F (MvPolynomial σ F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let t : MvPolynomial σ F →ₐ[F] T := aeval (fun j => u * v j)
  let m : MvPolynomial σ k →ₐ[k] MvPolynomial σ F :=
    MvPolynomial.mapAlgHom (Algebra.ofId k F)
  have ht : (t.restrictScalars k).comp m = aeval (fun j => u * v j) := by
    apply MvPolynomial.algHom_ext
    intro j
    change t (MvPolynomial.map (algebraMap k F) (MvPolynomial.X j)) =
      aeval (R := k) (fun l => u * v l) (MvPolynomial.X j)
    simp only [t, MvPolynomial.map_X, aeval_X]
  have hle : Q.map (MvPolynomial.map (algebraMap k F)) ≤ RingHom.ker t.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change ((t.restrictScalars k).comp m) p = 0
    rw [ht]
    exact scaled_kills hQ v u h p hp
  exact fun p hp => hle hp

private abbrev chart {k σ : Type} [Field k] (Q : Ideal (MvPolynomial σ k)) (i : σ) :=
  MvPolynomial σ k ⧸ (Q ⊔ Ideal.span {MvPolynomial.X i - 1})

private def openCoeff {k F σ : Type} [Field k] [Field F] [Algebra k F]
    (Q : Ideal (MvPolynomial σ k)) (i : σ) (a : chart Q i) (j : σ) :
    F ⊗[k] Localization.Away a :=
  Algebra.TensorProduct.includeRight (R := k)
    (algebraMap (chart Q i) (Localization.Away a) (Ideal.Quotient.mk _ (MvPolynomial.X j)))

private theorem recover {k F σ : Type} [Field k] [Field F] [Algebra k F]
    (Q : Ideal (MvPolynomial σ k)) (i : σ) (a : chart Q i)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ k))
    [IsDomain (chart Q i)] (ha : a ≠ 0)
    [IsDomain (F ⊗[k] Localization.Away a)]
    [IsDomain (MvPolynomial σ F ⧸ Q.map (MvPolynomial.map (algebraMap k F)))] :
    ∃ e : FractionRing (MvPolynomial σ F ⧸ Q.map (MvPolynomial.map (algebraMap k F))) ≃ₐ[F]
        FractionRing ((F ⊗[k] Localization.Away a)[X]),
      ∀ j : σ,
        e (K1_13_5_5_2_1_4.toFraction (MvPolynomial σ F ⧸ Q.map (MvPolynomial.map (algebraMap k F)))
          (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
        K1_13_5_5_2_1_4.toFraction ((F ⊗[k] Localization.Away a)[X])
          (Polynomial.C (openCoeff (F := F) Q i a j) * Polynomial.X) := by
  classical
  let I : Ideal (MvPolynomial σ k) := Q ⊔ Ideal.span {MvPolynomial.X i - 1}
  let J : Ideal (MvPolynomial σ F) := Q.map (MvPolynomial.map (algebraMap k F))
  let A := chart Q i
  let L := Localization.Away a
  let B := F ⊗[k] L
  let R := MvPolynomial σ F ⧸ J
  let E := FractionRing R
  let D := FractionRing B[X]
  let : IsDomain B := ‹IsDomain (F ⊗[k] Localization.Away a)›
  let : Field E := FractionRing.field (A := R)
  let : Field D := FractionRing.field (A := B[X])
  let : IsScalarTower k F (MvPolynomial σ F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k F B[X] := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k F D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let π : MvPolynomial σ k →ₐ[k] A := Ideal.Quotient.mkₐ k I
  let q : MvPolynomial σ F →ₐ[F] R := Ideal.Quotient.mkₐ F J
  let m : MvPolynomial σ k →ₐ[k] MvPolynomial σ F :=
    MvPolynomial.mapAlgHom (Algebra.ofId k F)
  let b₀ : A →ₐ[k] L := IsScalarTower.toAlgHom k A L
  let b₁ : L →ₐ[k] B := Algebra.TensorProduct.includeRight
  let b := b₁.comp b₀
  let jE : R →ₐ[F] E := IsScalarTower.toAlgHom F R E
  let jD : B[X] →ₐ[F] D := IsScalarTower.toAlgHom F B[X] D
  let Ck : B →ₐ[k] B[X] := Polynomial.CAlgHom
  let w (j : σ) : B[X] := Polynomial.C (b (π (MvPolynomial.X j)))
  let z (j : σ) : R := q (MvPolynomial.X j)
  have hπi : π (MvPolynomial.X i) = 1 := sub_eq_zero.mp (by
    rw [← map_one π, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {MvPolynomial.X i - 1} ≤ I from le_sup_right)
        (Ideal.mem_span_singleton_self (MvPolynomial.X i - 1))))
  have hw : aeval w = Ck.comp (b.comp π) := by
    apply MvPolynomial.algHom_ext
    intro j
    exact aeval_X _ _
  let t : MvPolynomial σ F →ₐ[F] B[X] := aeval (fun j => Polynomial.X * w j)
  have hwQ : ∀ p ∈ Q, aeval w p = 0 := by
    intro p hp
    have hπ : π p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((show Q ≤ I from le_sup_left) hp)
    rw [hw, AlgHom.comp_apply, AlgHom.comp_apply, hπ, map_zero, map_zero]
  have htJ : ∀ p ∈ J, t p = 0 :=
    scaled_extension_kills (F := F) (T := B[X]) hQ w Polynomial.X hwQ
  let φ : R →ₐ[F] B[X] := Ideal.Quotient.liftₐ J t htJ
  have hφ (j : σ) : φ (z j) = Polynomial.X * w j := aeval_X _ _
  have hφi : φ (z i) = Polynomial.X := by
    rw [hφ]
    simp [w, hπi]
  have hscaleD : jD Polynomial.X ≠ 0 := by
    intro h
    exact Polynomial.X_ne_zero ((IsFractionRing.injective B[X] D) (h.trans (map_zero jD).symm))
  have hz : jE (z i) ≠ 0 := by
    intro h
    have hzero : z i = 0 := (IsFractionRing.injective R E) (h.trans (map_zero jE).symm)
    exact Polynomial.X_ne_zero (hφi.symm.trans ((congrArg φ hzero).trans (map_zero φ)))
  -- First form the ratios with the scale coordinate inverted.
  let V := Localization.Away (z i)
  let : IsScalarTower k F V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ι : R →ₐ[F] V := IsScalarTower.toAlgHom F R V
  let s : V := IsLocalization.Away.invSelf (z i)
  have hs : ι (z i) * s = 1 := IsLocalization.Away.mul_invSelf (S := V) (z i)
  let v (j : σ) : V := s * ι (z j)
  have hv (j : σ) : ι (z i) * v j = ι (z j) := by
    change ι (z i) * (s * ι (z j)) = _
    rw [← mul_assoc, hs, one_mul]
  let pV : MvPolynomial σ k →ₐ[k] V := ((ι.comp q).restrictScalars k).comp m
  have hpV : aeval (fun j => ι (z j)) = pV := by
    apply MvPolynomial.algHom_ext
    intro j
    change aeval (R := k) (fun l => ι (z l)) (MvPolynomial.X j) =
      ι (q (MvPolynomial.map (algebraMap k F) (MvPolynomial.X j)))
    rw [aeval_X, MvPolynomial.map_X]
  have hpVQ : ∀ p ∈ Q, aeval (R := k) (fun j => ι (z j)) p = 0 := by
    intro p hp
    have hq : q (MvPolynomial.map (algebraMap k F) p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hp)
    rw [hpV]
    change ι (q (MvPolynomial.map (algebraMap k F) p)) = 0
    rw [hq, map_zero]
  have hvI : ∀ p ∈ I, aeval v p = 0 := by
    have hle : I ≤ RingHom.ker (aeval v : MvPolynomial σ k →ₐ[k] V).toRingHom := by
      refine sup_le (scaled_kills hQ (fun j => ι (z j)) s hpVQ) (Ideal.span_le.mpr ?_)
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change aeval (R := k) v (MvPolynomial.X i - 1) = 0
      rw [map_sub, aeval_X, map_one, sub_eq_zero]
      exact (mul_comm _ _).trans hs
    exact fun p hp => hle hp
  let α : A →ₐ[k] V := Ideal.Quotient.liftₐ I (aeval v) hvI
  have hα (j : σ) : α (π (MvPolynomial.X j)) = v j := aeval_X _ _
  have hunitE : IsUnit (jE (z i)) := isUnit_iff_ne_zero.mpr hz
  let ρ : V →ₐ[F] E := IsLocalization.Away.liftAlgHom (z i) (f := jE) hunitE
  have hρ (x : R) : ρ (ι x) = jE x :=
    IsLocalization.Away.lift_eq (S := V) (g := jE.toRingHom) (z i) hunitE x
  have hunitD : IsUnit ((jD.comp φ) (z i)) := isUnit_iff_ne_zero.mpr (by
    change jD (φ (z i)) ≠ 0
    rwa [hφi])
  let τ : V →ₐ[F] D := IsLocalization.Away.liftAlgHom (z i) (f := jD.comp φ) hunitD
  have hτ (x : R) : τ (ι x) = jD (φ x) :=
    IsLocalization.Away.lift_eq (S := V) (g := (jD.comp φ).toRingHom) (z i) hunitD x
  have hτv (j : σ) : τ (v j) = jD (w j) := by
    have ht1 : τ (ι (z i)) * τ (v j) = τ (ι (z j)) := by rw [← map_mul, hv]
    rw [hτ (z i), hτ (z j), hφi, hφ j, map_mul jD] at ht1
    exact mul_left_cancel₀ hscaleD ht1
  -- In the scaled chart, the ratios become the original chart coefficients.
  let Jk := jD.restrictScalars k
  have hτα : (τ.restrictScalars k).comp α = Jk.comp (Ck.comp b) := by
    apply Ideal.Quotient.algHom_ext k
    apply MvPolynomial.algHom_ext
    intro j
    change τ (α (π (MvPolynomial.X j))) = jD (w j)
    rw [hα, hτv]
  have hb₀ : Function.Injective b₀ :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hb₁ : Function.Injective b₁ :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k F).injective
  have hαa : α a ≠ 0 := by
    intro h
    have he := DFunLike.congr_fun hτα a
    change τ (α a) = jD (Polynomial.C (b₁ (b₀ a))) at he
    rw [h, map_zero] at he
    have hinj := (IsFractionRing.injective B[X] D).comp
      (Polynomial.C_injective.comp (hb₁.comp hb₀))
    apply ha
    apply hinj
    change jD (Polynomial.C (b₁ (b₀ a))) = jD (Polynomial.C (b₁ (b₀ 0)))
    rw [he.symm, map_zero, map_zero, map_zero, map_zero]
  have hinjρ : Function.Injective ρ := by
    apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers (z i))
      V ρ.toRingHom
    intro x hx
    change ρ (ι x) = 0 at hx
    rw [hρ] at hx
    have hx' : x = 0 := (IsFractionRing.injective R E) (hx.trans (map_zero jE).symm)
    change ι x = 0
    rw [hx', map_zero]
  let rA : A →ₐ[k] E := (ρ.restrictScalars k).comp α
  have hunitA : IsUnit (rA a) := isUnit_iff_ne_zero.mpr (by
    change ρ (α a) ≠ 0
    intro h
    exact hαa (hinjρ (h.trans (map_zero ρ).symm)))
  let gL : L →ₐ[k] E := IsLocalization.Away.liftAlgHom a (f := rA) hunitA
  let gB : B →ₐ[F] E := (AlgHom.liftEquiv k F L E) gL
  have hgB (x : L) : gB (b₁ x) = gL x := by
    change (AlgHom.liftEquiv k F L E gL) (1 ⊗ₜ[k] x) = _
    simp
  let g : B[X] →ₐ[F] E := Polynomial.aevalTower gB (jE (z i))
  have hgX : g Polynomial.X = jE (z i) := Polynomial.aevalTower_X _ _
  have hgC (x : B) : g (Polynomial.C x) = gB x := Polynomial.aevalTower_C _ _ _
  have hgchart (x : A) : gB (b x) = ρ (α x) := by
    change gB (b₁ (b₀ x)) = _
    rw [hgB]
    exact IsLocalization.Away.lift_eq (S := L) (g := rA.toRingHom) a hunitA x
  have hgφ : g.comp φ = jE := by
    apply Ideal.Quotient.algHom_ext F
    apply MvPolynomial.algHom_ext
    intro j
    change g (φ (z j)) = jE (z j)
    rw [hφ, map_mul, hgX]
    change jE (z i) * g (Polynomial.C (b (π (MvPolynomial.X j)))) = _
    rw [hgC, hgchart, hα, ← hρ, ← map_mul, hv, hρ]
  have hinj : Function.Injective (jD.comp φ) := by
    apply (IsFractionRing.injective B[X] D).comp
    intro x y h
    apply IsFractionRing.injective R E
    exact (DFunLike.congr_fun hgφ x).symm.trans
      ((congrArg g h).trans (DFunLike.congr_fun hgφ y))
  let f : E →ₐ[F] D := IsFractionRing.liftAlgHom (K := E) (L := D) (g := jD.comp φ) hinj
  have hf (x : R) : f (jE x) = jD (φ x) :=
    IsFractionRing.lift_algebraMap (K := E) (g := (jD.comp φ).toRingHom) hinj x
  have hfρ : f.comp ρ = τ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (z i))
    apply RingHom.ext
    intro x
    change f (ρ (ι x)) = τ (ι x)
    rw [hρ, hτ, hf]
  have hfgB : f.comp gB = jD.comp (Polynomial.CAlgHom : B →ₐ[F] B[X]) := by
    apply Algebra.TensorProduct.ext_ring (R := k)
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    apply RingHom.ext
    intro x
    change f (gB (b x)) = jD (Polynomial.C (b x))
    rw [hgchart]
    exact (DFunLike.congr_fun hfρ (α x)).trans (DFunLike.congr_fun hτα x)
  have hfg : f.comp g = jD := by
    apply Polynomial.algHom_ext'
    · apply AlgHom.ext
      intro x
      change f (g (Polynomial.C x)) = jD (Polynomial.C x)
      rw [hgC]
      exact DFunLike.congr_fun hfgB x
    · change f (g Polynomial.X) = jD Polynomial.X
      rw [hgX, hf, hφi]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective B[X] y
    refine ⟨g p / g q, ?_⟩
    rw [map_div₀]
    exact congrArg₂ (· / ·) (DFunLike.congr_fun hfg p) (DFunLike.congr_fun hfg q)
  let e := AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩
  refine ⟨e, fun j => ?_⟩
  change f (jE (z j)) = jD (w j * Polynomial.X)
  rw [hf, hφ]
  exact congrArg jD (mul_comm (Polynomial.X : B[X]) (w j))

open K1_13 K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1 K1_13_5_5_2_1_4

theorem proof : K1_13_5_5_2_1_4.c1 := by
  intro Q i a hQ hhom _ hchart ha hopen
  have hsource : IsDomain (FreshCoeffRing ⧸ freshIdeal Q) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr (freshIdeal_isPrime Q hQ)
  exact @recover Geom FreshField CoeffIndex _ _ _ Q i a hhom hchart ha hopen hsource

end

end K1_13_5_5_2_1_4_1
end PackSource_K1_13_5_5_2_1_4_1Proof

section PackSource_K1_13_5_5_2_1_1Defs
set_option autoImplicit true
namespace K1_13_5_5_2_1_1

open K1_13_5_5

noncomputable section

/-- The homogeneous value equation on the fresh coefficient cone. -/
def freshValue : FreshCoeffRing := jetForm freshCenter 0

/-- The value section before choosing an affine chart. -/
def valueIdeal (Q : Ideal CoeffRing) : Ideal FreshCoeffRing :=
  freshIdeal Q ⊔ Ideal.span {freshValue}

/-- The value section in the chart where coefficient `i` equals one. -/
def valueChartIdeal (Q : Ideal CoeffRing) (i : CoeffIndex) : Ideal FreshCoeffRing :=
  valueIdeal Q ⊔ Ideal.span {MvPolynomial.X i - 1}

end

end K1_13_5_5_2_1_1
end PackSource_K1_13_5_5_2_1_1Defs

section PackSource_K1_13_5_5_2_1_1Presentation
set_option autoImplicit true
namespace K1_13_5_5_2_1_1

open K1_13 K1_13_5_5 K1_13_5_5_2_1 MvPolynomial
open scoped Polynomial TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000

section ScalarExtension

variable {k F σ : Type*} [Field k] [Field F] [Algebra k F]

private def quotientTensor (I : Ideal (MvPolynomial σ k)) :
    F ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[F]
      MvPolynomial σ F ⧸ I.map (MvPolynomial.map (algebraMap k F)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k F
  let ι : MvPolynomial σ k →ₐ[k] F ⊗[k] MvPolynomial σ k := Algebra.TensorProduct.includeRight
  have he : e.toRingHom.comp ι.toRingHom = MvPolynomial.map (algebraMap k F) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = _
    simp [e]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k) F _ F I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  exact ((Ideal.map_map (I := I) ι.toRingHom e.toRingHom).trans
    (congrArg (fun f => I.map f) he)).symm

private theorem quotientTensor_tmul (I : Ideal (MvPolynomial σ k)) (c : F)
    (p : MvPolynomial σ k) :
    quotientTensor I (c ⊗ₜ[k] (Ideal.Quotient.mk I p)) =
      c • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap k F) p) := by
  simp only [quotientTensor, AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact (Ideal.Quotient.mkₐ F _).toLinearMap.map_smul c _

end ScalarExtension

abbrev FreshChartRing (Q : Ideal CoeffRing) (i : CoeffIndex) :=
  FreshField ⊗[Geom] ChartRing Q i

def chartValue (Q : Ideal CoeffRing) (i : CoeffIndex) : FreshChartRing Q i :=
  freshEval _ (direction Q i)

/-- The fresh chart receives the unnormalized coefficient coordinates with the
chosen chart coordinate set equal to one. -/
def chartProjection (Q : Ideal CoeffRing) (i : CoeffIndex) :
    FreshCoeffRing →ₐ[FreshField] FreshChartRing Q i :=
  MvPolynomial.aeval fun j : CoeffIndex =>
    (1 : FreshField) ⊗ₜ[Geom] (Ideal.Quotient.mk
      (Q ⊔ Ideal.span {MvPolynomial.X i - 1}) (MvPolynomial.X j) : ChartRing Q i)

private def tensorChartEquiv (Q : Ideal CoeffRing) (i : CoeffIndex) :
    FreshChartRing Q i ≃ₐ[FreshField]
      FreshCoeffRing ⧸ (freshIdeal Q ⊔ Ideal.span {MvPolynomial.X i - 1}) := by
  refine (quotientTensor (Q ⊔ Ideal.span {MvPolynomial.X i - 1})).trans ?_
  apply Ideal.quotientEquivAlgOfEq FreshField
  simp [freshIdeal, Ideal.map_sup, Ideal.map_span]

private theorem tensorChartEquiv_tmul (Q : Ideal CoeffRing) (i : CoeffIndex)
    (c : FreshField) (p : CoeffRing) :
    tensorChartEquiv Q i (c ⊗ₜ[Geom]
      (Ideal.Quotient.mk (Q ⊔ Ideal.span {MvPolynomial.X i - 1}) p)) =
      c • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap Geom FreshField) p) := by
  simp only [tensorChartEquiv, AlgEquiv.trans_apply, quotientTensor_tmul, map_smul,
    Ideal.quotientEquivAlgOfEq_mk]

private theorem tensorChartEquiv_projection (Q : Ideal CoeffRing) (i : CoeffIndex)
    (p : FreshCoeffRing) :
    tensorChartEquiv Q i (chartProjection Q i p) = Ideal.Quotient.mk _ p := by
  have he : (tensorChartEquiv Q i).toAlgHom.comp (chartProjection Q i) =
      Ideal.Quotient.mkₐ FreshField _ := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, chartProjection, aeval_X]
    change tensorChartEquiv Q i (1 ⊗ₜ[Geom] (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X j)
    rw [tensorChartEquiv_tmul Q i, one_smul, MvPolynomial.map_X]
  exact AlgHom.congr_fun he p

private theorem eval_direction_sum {k F A σ : Type} [Field k] [Field F] [CommRing A]
    [Algebra k F] [Algebra k A] [Fintype σ] (z : F) (d : σ → ℕ) (a : σ → A) :
    (Polynomial.eval₂RingHom Algebra.TensorProduct.includeRight.toRingHom
      (algebraMap F (F ⊗[k] A) z)) (∑ j, Polynomial.monomial (d j) (a j)) =
      MvPolynomial.aeval (fun j => (1 : F) ⊗ₜ[k] a j)
        (∑ j, MvPolynomial.C (z ^ d j) * MvPolynomial.X j) := by
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, map_mul, aeval_C, aeval_X, map_pow]
  exact mul_comm _ _

private theorem chartValue_projection (Q : Ideal CoeffRing) (i : CoeffIndex) :
    chartProjection Q i freshValue = chartValue Q i := by
  have h : freshValue =
      ∑ j : CoeffIndex, MvPolynomial.C (freshCenter ^ j.val) * MvPolynomial.X j := by
    simp only [freshValue, jetForm, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [h]
  exact (eval_direction_sum freshCenter Fin.val (fun j : CoeffIndex =>
    (Ideal.Quotient.mk (Q ⊔ Ideal.span {MvPolynomial.X i - 1}) (MvPolynomial.X j) :
      ChartRing Q i))).symm

theorem chartValue_eq (Q : Ideal CoeffRing) (i : CoeffIndex) :
    tensorChartEquiv Q i (chartValue Q i) = Ideal.Quotient.mk _ freshValue := by
  rw [← chartValue_projection, tensorChartEquiv_projection]

theorem freshValue_not_mem (Q : Ideal CoeffRing) (i : CoeffIndex)
    (hnonzero : chartValue Q i ≠ 0) : freshValue ∉ freshIdeal Q := by
  intro h
  apply hnonzero
  apply (tensorChartEquiv Q i).injective
  rw [chartValue_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_left h

private theorem chartClass_X_eq_one {k : Type} [Field k] {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) k)) (i : Fin n) :
    (Ideal.Quotient.mk _ (MvPolynomial.X i) : CoefficientChart Q i) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

private theorem chartDirection_coeff {k : Type} [Field k] {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) k)) (i : Fin n) :
    (chartDirection Q i).coeff i.val = 1 := by
  classical
  rw [chartDirection, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_monomial_same, chartClass_X_eq_one]
  · intro j _ hji
    simp [Polynomial.coeff_monomial, Fin.val_ne_of_ne hji]
  · simp

theorem direction_ne_zero (Q : Ideal CoeffRing) (i : CoeffIndex) [IsDomain (ChartRing Q i)] :
    direction Q i ≠ 0 := by
  intro h
  have hc := chartDirection_coeff Q i
  change chartDirection Q i = 0 at h
  rw [h, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc

section Principal

variable {F A B : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]

def principalQuotEquiv (e : A ≃ₐ[F] B) {x : A} {y : B} (h : e x = y) :
    PrincipalQuot x ≃ₐ[F] PrincipalQuot y :=
  Ideal.quotientEquivAlg _ _ e (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {y} = Ideal.span {e x}
    rw [h])

@[simp]
theorem principalQuotEquiv_mk (e : A ≃ₐ[F] B) {x : A} {y : B} (h : e x = y) (z : A) :
    principalQuotEquiv e h (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (e z) := rfl

private def principalDoubleQuotEquiv (I : Ideal A) (x : A) :
    PrincipalQuot (Ideal.Quotient.mk I x) ≃ₐ[F] A ⧸ (I ⊔ Ideal.span {x}) :=
  (Ideal.quotientEquivAlgOfEq F (show Ideal.span {Ideal.Quotient.mk I x} =
    (Ideal.span {x}).map (Ideal.Quotient.mkₐ F I) by
      rw [Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk])).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ F I (Ideal.span {x}))

@[simp]
private theorem principalDoubleQuotEquiv_mk (I : Ideal A) (x p : A) :
    principalDoubleQuotEquiv (F := F) I x (Ideal.Quotient.mk _ (Ideal.Quotient.mk I p)) =
      Ideal.Quotient.mk _ p := rfl

end Principal

/-- Before inverting the fixed denominator, the fresh value quotient is the
coefficient cone cut by the value and by the chart equation. -/
def valueChartEquiv (Q : Ideal CoeffRing) (i : CoeffIndex) :
    PrincipalQuot (chartValue Q i) ≃ₐ[FreshField] FreshCoeffRing ⧸ valueChartIdeal Q i :=
  (principalQuotEquiv (tensorChartEquiv Q i) (chartValue_eq Q i)).trans
    ((principalDoubleQuotEquiv _ freshValue).trans
      (Ideal.quotientEquivAlgOfEq FreshField (sup_right_comm _ _ _)))

theorem valueChartEquiv_mk (Q : Ideal CoeffRing) (i : CoeffIndex) (p : FreshCoeffRing) :
    valueChartEquiv Q i (Ideal.Quotient.mk _ (chartProjection Q i p)) =
      Ideal.Quotient.mk _ p := by
  simp only [valueChartEquiv, AlgEquiv.trans_apply, principalQuotEquiv_mk,
    tensorChartEquiv_projection, principalDoubleQuotEquiv_mk, Ideal.quotientEquivAlgOfEq_mk]

theorem chartProjection_map (Q : Ideal CoeffRing) (i : CoeffIndex) (p : CoeffRing) :
    chartProjection Q i (MvPolynomial.map (algebraMap Geom FreshField) p) =
      (1 : FreshField) ⊗ₜ[Geom] Ideal.Quotient.mk _ p := by
  apply (tensorChartEquiv Q i).injective
  rw [tensorChartEquiv_projection]
  rw [tensorChartEquiv_tmul, one_smul]

end

end K1_13_5_5_2_1_1
end PackSource_K1_13_5_5_2_1_1Presentation

section PackSource_K1_13_5_5_2_1_1Open
set_option autoImplicit true
namespace K1_13_5_5_2_1_1

open K1_13 K1_13_5_5 K1_13_5_5_2_1
open scoped Polynomial TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000

section Localization

variable {F A : Type} [CommRing F] [CommRing A] [Algebra F A]

/-- A localization does not change a principal quotient when the element being
inverted is already a unit there. -/
private def quotientAwayUnitEquiv (v b : A)
    (hb : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) b)) :
    PrincipalQuot (algebraMap A (Localization.Away b) v) ≃ₐ[F] PrincipalQuot v := by
  let S := Localization.Away b
  let D := PrincipalQuot v
  let J : Ideal S := Ideal.span {algebraMap A S v}
  let q : A →ₐ[F] D := Ideal.Quotient.mkₐ F _
  let π : S →ₐ[F] S ⧸ J := Ideal.Quotient.mkₐ F J
  let g : S →ₐ[F] D := IsLocalization.Away.liftAlgHom b (show IsUnit (q b) from hb)
  have hg (x : A) : g (algebraMap A S x) = q x :=
    IsLocalization.Away.lift_eq b (g := q.toRingHom) hb x
  have hv : q v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self v)
  have hπ : π (algebraMap A S v) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hJ : J ≤ RingHom.ker g.toRingHom :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ((hg v).trans hv))
  let forward : A →ₐ[F] S ⧸ J := π.comp (IsScalarTower.toAlgHom F A S)
  have hV : Ideal.span {v} ≤ RingHom.ker forward.toRingHom :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ)
  let f : S ⧸ J →ₐ[F] D := Ideal.Quotient.liftₐ J g (fun _ hx => hJ hx)
  let r : D →ₐ[F] S ⧸ J := Ideal.Quotient.liftₐ _ forward (fun _ hx => hV hx)
  have hf (x : S) : f (π x) = g x := rfl
  have hr (x : A) : r (q x) = π (algebraMap A S x) := rfl
  refine AlgEquiv.ofAlgHom f r ?_ ?_
  · apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change f (r (q x)) = q x
    rw [hr, hf, hg]
  · suffices h : r.comp g = π by
      apply AlgHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change r (f (π x)) = π x
      rw [hf]
      exact AlgHom.congr_fun h x
    apply IsLocalization.algHom_ext (Submonoid.powers b)
    ext x
    change r (g (algebraMap A S x)) = π (algebraMap A S x)
    rw [hg, hr]

end Localization

private theorem freshEval_map {A B : Type} [CommRing A] [CommRing B]
    [Algebra Geom A] [Algebra Geom B] (f : A →ₐ[Geom] B) (p : A[X]) :
    (Algebra.TensorProduct.map (AlgHom.id FreshField FreshField) f) (freshEval A p) =
      freshEval B (p.map f.toRingHom) := by
  have h : (Algebra.TensorProduct.map (AlgHom.id FreshField FreshField) f).toRingHom.comp
      (freshEval A) = (freshEval B).comp (Polynomial.mapRingHom f.toRingHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [freshEval, Polynomial.coe_eval₂RingHom, Algebra.TensorProduct.includeRight_apply]
    · simp [freshEval, Polynomial.coe_eval₂RingHom, Algebra.TensorProduct.algebraMap_apply]
  exact RingHom.congr_fun h p

private theorem tensorAwayMap {k F A : Type} [CommRing k] [CommRing F] [CommRing A]
    [Algebra k F] [Algebra k A] (a : A) (x : F ⊗[k] A) :
    IsLocalization.Away.tensorProductEquivTMulRight k F a (Localization.Away a)
      ((Algebra.TensorProduct.map (AlgHom.id F F)
        (IsScalarTower.toAlgHom k A (Localization.Away a))) x) =
      algebraMap (F ⊗[k] A) (Localization.Away ((1 : F) ⊗ₜ[k] a)) x := by
  induction x using TensorProduct.inductionOn with
  | tmul c z =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := k) (S := F) (A := A) a
      (Localization.Away a) c z
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The class of `b` is a unit in the quotient by the principal ideal of `v`. -/
def IsUnitModulo {A : Type} [CommRing A] (v b : A) : Prop :=
  IsUnit (Ideal.Quotient.mk (Ideal.span {v}) b)

/-- The value quotient on a fixed open agrees with the chart value quotient
if the denominator is a unit on the cut. -/
def valueOpenEquiv {A : Type} [CommRing A] [Algebra Geom A] (a : A) (p : A[X])
    (ha : IsUnitModulo (freshEval A p) ((1 : FreshField) ⊗ₜ[Geom] a)) :
    PrincipalQuot (freshEval (Localization.Away a) (p.map (algebraMap A _))) ≃ₐ[FreshField]
      PrincipalQuot (freshEval A p) := by
  let B := Localization.Away a
  let S := FreshField ⊗[Geom] A
  let b : S := (1 : FreshField) ⊗ₜ[Geom] a
  let T := Localization.Away b
  let e : FreshField ⊗[Geom] B ≃ₐ[FreshField] T :=
    IsLocalization.Away.tensorProductEquivTMulRight Geom FreshField a B
  let g := Algebra.TensorProduct.map (AlgHom.id FreshField FreshField) (IsScalarTower.toAlgHom Geom A B)
  have he (x : S) : e (g x) = algebraMap S T x := tensorAwayMap a x
  have hv : e (freshEval B (p.map (algebraMap A B))) = algebraMap S T (freshEval A p) := by
    have hf := freshEval_map (IsScalarTower.toAlgHom Geom A B) p
    change g (freshEval A p) = freshEval B (p.map (algebraMap A B)) at hf
    rw [← hf, he]
  exact (principalQuotEquiv e hv).trans (quotientAwayUnitEquiv _ b ha)

end

end K1_13_5_5_2_1_1
end PackSource_K1_13_5_5_2_1_1Open

section PackSource_K1_13_5_5_2_3Defs
set_option autoImplicit true
namespace K1_13_5_5_2_3

noncomputable section

open K1_13_5_5 K1_13_5_5_2 MvPolynomial

set_option backward.isDefEq.respectTransparency false

/-- The homogenizing variable maps to the polynomial variable. Each coefficient
coordinate maps to its affine class times that variable. -/
def closureEval {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial (Option σ) K →ₐ[K] Polynomial (MvPolynomial σ K ⧸ I) :=
  MvPolynomial.aeval (R := K) (S₁ := Polynomial (MvPolynomial σ K ⧸ I)) fun
    | none => Polynomial.X
    | some j => Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.X j)) * Polynomial.X

def closureIdeal {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial (Option σ) K) :=
  RingHom.ker (closureEval I).toRingHom

/-- The homogeneous coordinate ring of the projective closure. -/
abbrev Closure {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) :=
  MvPolynomial (Option σ) K ⧸ closureIdeal I

def closureW {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) : Closure I :=
  Ideal.Quotient.mk (closureIdeal I) (MvPolynomial.X none)

def closureLift {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) : Closure I :=
  Ideal.Quotient.mk (closureIdeal I) (rename some f)

/-- The plane parameters are homogeneous linear forms, and the polynomial variable
represents the common homogenizing coordinate. -/
def closurePairMap {σ : Type} (L : Fin 2 → MvPolynomial σ FreshField)
    (I : Ideal (MvPolynomial σ FreshField)) : Polynomial PairRing →+* Closure I :=
  Polynomial.eval₂RingHom (aeval fun i => closureLift I (L i)).toRingHom (closureW I)

/-- Rank over the plane parameters and the homogenizing coordinate. The cardinal
rank also distinguishes infinite rank from zero rank. -/
def closureRank {σ : Type} (L : Fin 2 → MvPolynomial σ FreshField)
    (I : Ideal (MvPolynomial σ FreshField)) : Cardinal :=
  letI : Module (Polynomial PairRing) (Closure I) :=
    Module.compHom (Closure I) (closurePairMap L I)
  Module.rank (Polynomial PairRing) (Closure I)

def topForm (g : FreshJetRing) : FreshJetRing :=
  homogeneousComponent g.totalDegree g

end

end K1_13_5_5_2_3
end PackSource_K1_13_5_5_2_3Defs

section PackSource_K1_13_5_5_2_1_1Fresh
set_option autoImplicit true
namespace K1_13_5_5_2_1_1

open K1_13 K1_13_5_5 K1_13_5_5_2_1
open scoped Polynomial TensorProduct nonZeroDivisors

noncomputable section

/-- Fresh evaluation in a domain is localization at the nonzero scalar polynomials. -/
theorem freshEval_domain_injective (A : Type) [CommRing A] [IsDomain A] [Algebra Geom A] :
    IsDomain (FreshField ⊗[Geom] A) ∧ Function.Injective (freshEval A) := by
  let P := Geom[X]
  let M := nonZeroDivisors P
  let R := A ⊗[Geom] P
  let ι : P →ₐ[Geom] R := Algebra.TensorProduct.includeRight
  let S := Localization (M.map ι)
  let e : A[X] ≃ₐ[A] R := polyEquivTensor' Geom A
  let : IsDomain R := e.symm.toRingEquiv.injective.isDomain _
  have hι : Function.Injective ι := by
    have he (p : P) : e.symm (ι p) = p.map (algebraMap Geom A) := by
      change (polyEquivTensor Geom A).symm ((1 : A) ⊗ₜ[Geom] p) = _
      rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
    intro p q hpq
    exact Polynomial.map_injective _ (algebraMap Geom A).injective
      ((he p).symm.trans ((congrArg e.symm hpq).trans (he q)))
  have hM : M.map ι ≤ nonZeroDivisors R := map_le_nonZeroDivisors_of_injective _ hι le_rfl
  let : IsDomain S := IsLocalization.isDomain_localization hM
  let E := IsLocalization.tensorProductEquivOfMapIncludeRight Geom A M FreshField S
  let E' := (Algebra.TensorProduct.comm Geom FreshField A).toRingEquiv.trans E.toRingEquiv
  have hmap : E'.toRingHom.comp (freshEval A) = (algebraMap R S).comp e.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, freshEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change E (a ⊗ₜ[Geom] (1 : FreshField)) = algebraMap R S (e (Polynomial.C a))
      rw [← map_one (algebraMap P FreshField),
        IsLocalization.tensorProductEquivOfMapIncludeRight_tmul]
      congr 1
      change a ⊗ₜ[Geom] (1 : P) = polyEquivTensor Geom A (Polynomial.C a)
      rw [polyEquivTensor_apply, Polynomial.eval₂_C]
      rfl
    · simp only [RingHom.comp_apply, freshEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      change E ((1 : A) ⊗ₜ[Geom] algebraMap P FreshField Polynomial.X) =
        algebraMap R S (e Polynomial.X)
      rw [IsLocalization.tensorProductEquivOfMapIncludeRight_tmul]
      congr 1
      change (1 : A) ⊗ₜ[Geom] (Polynomial.X : P) = polyEquivTensor Geom A Polynomial.X
      rw [polyEquivTensor_apply, Polynomial.eval₂_X]
  refine ⟨E'.injective.isDomain _, ?_⟩
  have hinj : Function.Injective (E'.toRingHom.comp (freshEval A)) := by
    rw [hmap]
    exact (IsLocalization.injective S hM).comp e.injective
  exact fun _ _ h => hinj (congrArg E' h)

end

end K1_13_5_5_2_1_1
end PackSource_K1_13_5_5_2_1_1Fresh

section PackSource_K1_13_5_5_2_3Split
set_option autoImplicit true
namespace K1_13_5_5_2_3

noncomputable section

open K1_13_5_5 K1_13_5_5_2 MvPolynomial
open scoped Polynomial TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-- Choose a direction off the top form, so the affine plane parameters give
the needed degree bound on the jet closure and a finite map at infinity. -/
def c1 : Prop :=
  ∀ g : FreshJetRing, 0 < g.totalDegree →
    ∃ L : Fin 2 → FreshJetRing,
      FiniteJetPair L (Ideal.span {topForm g}) ∧
      closureRank L (Ideal.span {g}) ≤ (g.totalDegree : Cardinal)

/-- Setting the homogenizing coordinate to zero gives the coefficient cone.
The top form of the jet equation vanishes on its scheme-theoretic jet image. -/
def c2 : Prop :=
  ∀ (P : Ideal CoeffRing) (g d : FreshJetRing), FreshChart P g d →
    topForm g ∈ jetImage (freshIdeal (infinityIdeal P)) ∧
    ∃ s : Closure (freshIdeal P) →ₐ[FreshField]
        (FreshCoeffRing ⧸ freshIdeal (infinityIdeal P)),
      Function.Surjective s ∧
      s (closureW (freshIdeal P)) = 0 ∧
      ∀ f : FreshCoeffRing,
        s (closureLift (freshIdeal P) f) =
          Ideal.Quotient.mk (freshIdeal (infinityIdeal P)) f

/-- The birational chart recovers the coefficient closure after inverting
a nonzero element of the jet closure. -/
def c3 : Prop :=
  ∀ (P : Ideal CoeffRing) (g d : FreshJetRing), FreshChart P g d →
    ∃ s : Closure (Ideal.span {g}) →ₐ[FreshField] Closure (freshIdeal P),
      s (closureW (Ideal.span {g})) = closureW (freshIdeal P) ∧
      (∀ f : FreshJetRing,
        s (closureLift (Ideal.span {g}) f) = closureLift (freshIdeal P) (freshProjection f)) ∧
      ∃ b : Closure (Ideal.span {g}), s b ≠ 0 ∧
        ∀ a : Closure (freshIdeal P), ∃ q : Closure (Ideal.span {g}), ∃ m : ℕ,
          s q = s b ^ m * a

private theorem closureW_ne_zero {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K))
    (hI : I.IsPrime) : closureW I ≠ 0 := by
  intro hw
  have hm := (Ideal.Quotient.eq_zero_iff_mem).mp hw
  have hz : closureEval I (MvPolynomial.X none) = 0 := hm
  simp [closureEval] at hz

private theorem specialization_compat {σ : Type}
    (L : Fin 2 → MvPolynomial σ FreshField) (I J : Ideal (MvPolynomial σ FreshField))
    (s : Closure I →ₐ[FreshField] (MvPolynomial σ FreshField ⧸ J))
    (hw : s (closureW I) = 0)
    (hc : ∀ f, s (closureLift I f) = Ideal.Quotient.mk J f) :
    s.toRingHom.comp (closurePairMap L I) =
      ((Ideal.Quotient.mkₐ FreshField J).comp (aeval L)).toRingHom.comp
        (Polynomial.evalRingHom 0) := by
  let α : PairRing →ₐ[FreshField] Closure I := aeval fun i => closureLift I (L i)
  let β : PairRing →ₐ[FreshField] (MvPolynomial σ FreshField ⧸ J) :=
    (Ideal.Quotient.mkₐ FreshField J).comp (aeval L)
  have hcomp : s.comp α = β := by
    ext i
    simpa [α, β] using hc (L i)
  have heval (r : PairRing) : s (α r) = β r := DFunLike.congr_fun hcomp r
  apply Polynomial.ringHom_ext
  · intro r
    simpa [closurePairMap, α, β] using heval r
  · simpa [closurePairMap] using hw

private theorem recovery_compat
    (L : Fin 2 → FreshJetRing) (I : Ideal FreshJetRing) (J : Ideal FreshCoeffRing)
    (s : Closure I →ₐ[FreshField] Closure J) (hw : s (closureW I) = closureW J)
    (hc : ∀ f : FreshJetRing, s (closureLift I f) = closureLift J (freshProjection f)) :
    s.toRingHom.comp (closurePairMap L I) =
      closurePairMap (fun i => freshProjection (L i)) J := by
  let α : PairRing →ₐ[FreshField] Closure I := aeval fun i => closureLift I (L i)
  let β : PairRing →ₐ[FreshField] Closure J := aeval fun i => closureLift J (freshProjection (L i))
  have hcomp : s.comp α = β := by
    ext i
    simpa [α, β] using hc (L i)
  apply Polynomial.ringHom_ext
  · intro r
    simpa [closurePairMap, α, β] using DFunLike.congr_fun hcomp r
  · simpa [closurePairMap] using hw

private theorem closure_rank_le_of_recovery {σ τ : Type}
    (L : Fin 2 → MvPolynomial σ FreshField) (L' : Fin 2 → MvPolynomial τ FreshField)
    (I : Ideal (MvPolynomial σ FreshField)) (J : Ideal (MvPolynomial τ FreshField))
    (hJ : (closureIdeal J).IsPrime) (t : Closure I →+* Closure J)
    (hcomp : t.comp (closurePairMap L I) = closurePairMap L' J)
    (b : Closure I) (hb : t b ≠ 0)
    (hrec : ∀ a : Closure J, ∃ q : Closure I, ∃ m : ℕ, t q = t b ^ m * a) (n : ℕ) :
    closureRank L I ≤ (n : Cardinal) → closureRank L' J ≤ (n : Cardinal) := by
  let : IsDomain (Closure J) := Ideal.Quotient.isDomain (closureIdeal J)
  unfold closureRank
  exact rank_le_of_recovery (R := Polynomial PairRing) (A := Closure I) (B := Closure J)
    (closurePairMap L I) (closurePairMap L' J) t hcomp b hb hrec n

private theorem generic_rank_bound (R K V : Type) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V]
    (n : ℕ) (hrank : Module.rank R V ≤ (n : Cardinal)) :
    Module.Finite K (K ⊗[R] V) ∧ Module.finrank K (K ⊗[R] V) ≤ n := by
  have hfiber : Module.rank K (K ⊗[R] V) ≤ (n : Cardinal) :=
    (TensorProduct.isBaseChange R V K).rank_eq.le.trans hrank
  refine ⟨Module.rank_lt_aleph0_iff.mp (hfiber.trans_lt Cardinal.natCast_lt_aleph0), ?_⟩
  simpa [Module.finrank] using Cardinal.toNat_le_toNat hfiber Cardinal.natCast_lt_aleph0

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_5_5_2.c3 := by
  intro P g d hchart
  have hpos : 0 < g.totalDegree := by
    by_contra! h
    have ha := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    have ha0 : g.coeff 0 ≠ 0 := fun e => hchart.equation_ne (by simpa [e] using ha)
    have hunit : IsUnit g := by
      rw [ha]
      exact (isUnit_iff_ne_zero.mpr ha0).map MvPolynomial.C
    exact hchart.regular_open (by simp [Ideal.span_singleton_eq_top.mpr hunit])
  obtain ⟨L, hL, hLrank⟩ := h1 g hpos
  obtain ⟨htop, s, hsurj, hw, hc⟩ := h2 P g d hchart
  refine ⟨L, hL.of_le ((Ideal.span_singleton_le_iff_mem _).mpr htop), ?_⟩
  let I := freshIdeal P
  let J := freshIdeal (infinityIdeal P)
  let L' : Fin 2 → FreshCoeffRing := fun i => freshProjection (L i)
  let : I.IsPrime := freshIdeal_isPrime P hchart.prime
  have hprime : (closureIdeal I).IsPrime := RingHom.ker_isPrime (closureEval I).toRingHom
  have hwne : closurePairMap L' I Polynomial.X ≠ 0 := by
    simpa [closurePairMap] using closureW_ne_zero I (inferInstance : I.IsPrime)
  have hs : s.toRingHom.comp (closurePairMap L' I) =
      (pairMap L J).toRingHom.comp (Polynomial.evalRingHom 0) := by
    have hpair : (Ideal.Quotient.mkₐ FreshField J).comp (aeval L') = pairMap L J := by
      ext i
      simp [L', pairMap]
    rw [← hpair]
    exact specialization_compat L' I J s hw hc
  obtain ⟨t, htw, htc, b, hb, hrec⟩ := h3 P g d hchart
  have hcomp : t.toRingHom.comp (closurePairMap L (Ideal.span {g})) =
      closurePairMap L' I := recovery_compat L _ I t htw htc
  have hr : closureRank L' I ≤ (g.totalDegree : Cardinal) :=
    closure_rank_le_of_recovery L L' (Ideal.span {g}) I hprime t.toRingHom
      hcomp b hb hrec g.totalDegree hLrank
  let B := FreshCoeffRing ⧸ J
  letI : Module PairRing B := Module.compHom B (pairMap L J).toRingHom
  have hbrank : Module.rank PairRing B ≤ (g.totalDegree : Cardinal) := by
    exact rank_le_of_specialization (R := PairRing) (A := Closure I) (B := B)
      (closurePairMap L' I) (pairMap L J).toRingHom s.toRingHom hwne hs hsurj g.totalDegree hr
  change Module.Finite PairField (PairField ⊗[PairRing] B) ∧
    Module.finrank PairField (PairField ⊗[PairRing] B) ≤ g.totalDegree
  exact generic_rank_bound PairRing PairField B g.totalDegree hbrank

end

end K1_13_5_5_2_3
end PackSource_K1_13_5_5_2_3Split

section PackSource_K1_13_5_5_2_1_1Split
set_option autoImplicit true
namespace K1_13_5_5_2_1_1

noncomputable section

open K1_13 K1_13_5_5 K1_13_5_5_2_1 MvPolynomial
open scoped Polynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The fresh value has no projective zero on a fixed homogeneous cone of dimension at most one. -/
def c1 : Prop :=
  ∀ (I : Ideal CoeffRing),
    I.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom) →
    (affineHilbertPolynomial I).natDegree ≤ 1 →
    ∀ j : CoeffIndex, MvPolynomial.X j ∈ (valueIdeal I).radical

/-- Multiplication by a regular linear form gives the first Hilbert difference. -/
def c2 : Prop :=
  ∀ {F σ : Type} [Field F] [Finite σ] (I : Ideal (MvPolynomial σ F)) (ℓ : MvPolynomial σ F),
    I.IsHomogeneous (homogeneousSubmodule σ F) →
    (affineHilbertPolynomial I).natDegree = 2 →
    ℓ.IsHomogeneous 1 → IsLeftRegular (Ideal.Quotient.mk I ℓ) →
    affineHilbertPolynomial (I ⊔ Ideal.span {ℓ}) =
      Polynomial.backwardDifference 1 (affineHilbertPolynomial I)

/-- A homogeneous curve cone with no points on the omitted hyperplane has
dehomogenized length equal to its eventual homogeneous Hilbert function. -/
def c3 : Prop :=
  ∀ {F σ : Type} [Field F] [Finite σ] (I : Ideal (MvPolynomial σ F)) (i : σ),
    I.IsHomogeneous (homogeneousSubmodule σ F) →
    (affineHilbertPolynomial I).natDegree = 1 →
    (∀ j : σ, MvPolynomial.X j ∈ (I ⊔ Ideal.span {MvPolynomial.X i}).radical) →
    affineHilbertPolynomial (I ⊔ Ideal.span {MvPolynomial.X i - 1}) =
      Polynomial.C (affineHilbertPolynomial I).leadingCoeff

private theorem sup_span_homogeneous {F σ : Type*} [Field F]
    {I : Ideal (MvPolynomial σ F)} {f : MvPolynomial σ F} {d : ℕ}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ F)) (hf : f.IsHomogeneous d) :
    (I ⊔ Ideal.span {f}).IsHomogeneous (homogeneousSubmodule σ F) := by
  apply hI.sup
  apply Ideal.homogeneous_span
  rintro _ ⟨⟩
  exact ⟨d, hf⟩

private theorem map_homogeneous {F E σ : Type*} [Field F] [Field E]
    {I : Ideal (MvPolynomial σ F)} (f : F →+* E)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ F)) :
    (I.map (MvPolynomial.map f)).IsHomogeneous (homogeneousSubmodule σ E) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ I).mp hI
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨_, ⟨q, _, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := q.property
  exact ⟨d, (show ((q : MvPolynomial σ F)).IsHomogeneous d from hd).map f⟩

private theorem linear_sum_homogeneous {F σ : Type} [Field F] [Fintype σ] (c : σ → F) :
    (∑ i : σ, MvPolynomial.C (c i) * MvPolynomial.X i).IsHomogeneous 1 :=
  (homogeneousSubmodule σ F 1).sum_mem fun i _ => isHomogeneous_C_mul_X _ i

private theorem freshValue_homogeneous : freshValue.IsHomogeneous 1 :=
  linear_sum_homogeneous (fun i : CoeffIndex =>
    (i.val.choose 0 : FreshField) * freshCenter ^ (i.val - 0))

private theorem fixed_cut_dimension {Q : Ideal CoeffRing} (hQ : Q.IsPrime)
    (hd : (affineHilbertPolynomial Q).natDegree = 2) {g : CoeffRing} (hg : g ∉ Q) :
    (affineHilbertPolynomial (Q ⊔ Ideal.span {g})).natDegree ≤ 1 := by
  simpa [hd] using
    (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime hQ hg
      (b := g.totalDegree) le_rfl).1

private theorem exists_homogeneous_lift (Q : Ideal CoeffRing) (i : CoeffIndex)
    (a : ChartRing Q i) :
    ∃ (g : CoeffRing) (d : ℕ), g.IsHomogeneous d ∧ Ideal.Quotient.mk _ g = a := by
  classical
  let J : Ideal CoeffRing := Q ⊔ Ideal.span {MvPolynomial.X i - 1}
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := J) a
  let d := p.totalDegree
  have hi : Ideal.Quotient.mk J (MvPolynomial.X i) = 1 := by
    apply sub_eq_zero.mp
    rw [← (Ideal.Quotient.mk J).map_one, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine ⟨∑ n ∈ Finset.range (d + 1), MvPolynomial.X i ^ (d - n) * homogeneousComponent n p,
    d, IsHomogeneous.sum _ _ _ ?_, ?_⟩
  · intro n hn
    have hnd : n ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    simpa only [Nat.sub_add_cancel hnd] using
      (isHomogeneous_X_pow (R := Geom) i (d - n)).mul
        (homogeneousComponent_isHomogeneous n p)
  · change Ideal.Quotient.mk J _ = a
    rw [map_sum]
    simp only [map_mul, map_pow, hi, one_pow, one_mul]
    rw [← map_sum, sum_homogeneousComponent, hp]

private theorem denominator_unit (h1 : c1) (Q : Ideal CoeffRing) (i : CoeffIndex)
    (a : ChartRing Q i) (hQ : Q.IsPrime)
    (hhom : Q.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom))
    (hd : (affineHilbertPolynomial Q).natDegree = 2) (ha : a ≠ 0) :
    IsUnitModulo (chartValue Q i) ((1 : FreshField) ⊗ₜ[Geom] a) := by
  obtain ⟨g, d, hghom, hg⟩ := exists_homogeneous_lift Q i a
  have hgQ : g ∉ Q := by
    intro h
    apply ha
    rw [← hg, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left h
  let J := valueChartIdeal Q i
  let p := MvPolynomial.map (algebraMap Geom FreshField) g
  let B : Ideal FreshCoeffRing := J ⊔ Ideal.span {p}
  have hle : valueIdeal (Q ⊔ Ideal.span {g}) ≤ B := by
    have h : freshIdeal (Q ⊔ Ideal.span {g}) = freshIdeal Q ⊔ Ideal.span {p} := by
      simp [freshIdeal, p, Ideal.map_sup, Ideal.map_span]
    rw [valueIdeal, h]
    apply sup_le (sup_le ?_ le_sup_right) ?_
    · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp
    (h1 (Q ⊔ Ideal.span {g}) (sup_span_homogeneous hhom hghom)
      (fixed_cut_dimension hQ hd hgQ) i)
  have hi : Ideal.Quotient.mk B (MvPolynomial.X i) = 1 := by
    apply sub_eq_zero.mp
    rw [← (Ideal.Quotient.mk B).map_one, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hzero : Ideal.Quotient.mk B (MvPolynomial.X i ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle hn)
  rw [map_pow, hi, one_pow] at hzero
  have htop : B = ⊤ := (Ideal.eq_top_iff_one B).mpr
    (Ideal.Quotient.eq_zero_iff_mem.mp ((Ideal.Quotient.mk B).map_one.trans hzero))
  have hspan : (Ideal.span {Ideal.Quotient.mk J p} : Ideal (FreshCoeffRing ⧸ J)) = ⊤ := by
    have hm := congrArg (fun H : Ideal FreshCoeffRing => H.map (Ideal.Quotient.mk J)) htop
    simpa [B, Ideal.map_sup, Ideal.map_span, Ideal.map_quotient_self, Ideal.map_top] using hm
  have hunit := (Ideal.span_singleton_eq_top (x := Ideal.Quotient.mk J p)).mp hspan
  have he := valueChartEquiv_mk Q i p
  rw [chartProjection_map, hg] at he
  have hu := IsUnit.map (valueChartEquiv Q i).symm.toRingHom hunit
  change IsUnit ((valueChartEquiv Q i).symm (Ideal.Quotient.mk J p)) at hu
  rwa [← he, AlgEquiv.symm_apply_apply] at hu

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_5_5_2_1.c1 := by
  intro Q i a hQ hhom hd hi hchart ha
  let : IsDomain (ChartRing Q i) := hchart
  let : IsDomain (OpenRing Q i a) := Localization.Away.isDomain ha
  obtain ⟨hfresh, heval⟩ := freshEval_domain_injective (OpenRing Q i a)
  refine ⟨hfresh, heval, ?_⟩
  have hvalue : freshValue ∉ freshIdeal Q := freshValue_not_mem Q i (by
    intro h
    apply direction_ne_zero Q i
    exact (freshEval_domain_injective (ChartRing Q i)).2 (h.trans (map_zero _).symm))
  have hp := K1_13_5_5_2.freshIdeal_isPrime Q hQ
  let : (freshIdeal Q).IsPrime := hp
  have hregular : IsLeftRegular (Ideal.Quotient.mk (freshIdeal Q) freshValue) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hvalue)
  have hh : (freshIdeal Q).IsHomogeneous (homogeneousSubmodule CoeffIndex FreshField) :=
    map_homogeneous (algebraMap Geom FreshField) hhom
  have hvalhom : (valueIdeal Q).IsHomogeneous (homogeneousSubmodule CoeffIndex FreshField) :=
    sup_span_homogeneous hh freshValue_homogeneous
  have hbase : affineHilbertPolynomial (freshIdeal Q) = affineHilbertPolynomial Q :=
    K1_13_5_5_2.hilbertPolynomial_map Q
  have hfreshdim : (affineHilbertPolynomial (freshIdeal Q)).natDegree = 2 := by
    rw [hbase, hd]
  have hpoly : affineHilbertPolynomial (valueIdeal Q) =
      Polynomial.backwardDifference 1 (affineHilbertPolynomial Q) := by
    change affineHilbertPolynomial (freshIdeal Q ⊔ Ideal.span {freshValue}) = _
    rw [h2 (freshIdeal Q) freshValue hh hfreshdim freshValue_homogeneous hregular, hbase]
  obtain ⟨hdegree, hlead⟩ := Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (b := (1 : ℚ)) one_ne_zero (P := affineHilbertPolynomial Q) (by omega)
  have hboundary : ∀ j : CoeffIndex,
      MvPolynomial.X j ∈ (valueIdeal Q ⊔ Ideal.span {MvPolynomial.X i}).radical := by
    have heq : valueIdeal (Q ⊔ Ideal.span {MvPolynomial.X i}) =
        valueIdeal Q ⊔ Ideal.span {MvPolynomial.X i} := by
      simp only [valueIdeal, freshIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
        MvPolynomial.map_X]
      exact sup_right_comm _ _ _
    rw [← heq]
    exact h1 _ (sup_span_homogeneous hhom (isHomogeneous_X Geom i)) (fixed_cut_dimension hQ hd hi)
  have hchartPoly : affineHilbertPolynomial (valueChartIdeal Q i) = Polynomial.C (affineDegree Q) := by
    rw [valueChartIdeal, h3 (valueIdeal Q) i hvalhom
      (by rw [hpoly, hdegree, hd]) hboundary, hpoly, hlead]
    norm_num [affineDegree, hd]
  let V := FreshCoeffRing ⧸ valueChartIdeal Q i
  let : Module.Finite FreshField V := moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero
    (by rw [hchartPoly, Polynomial.natDegree_C])
  have hfinrank : (Module.finrank FreshField V : ℚ) = affineDegree Q :=
    Polynomial.C_injective ((affineHilbertPolynomial_eq_C_finrank (valueChartIdeal Q i)).symm.trans hchartPoly)
  let e := (valueOpenEquiv a (direction Q i) (denominator_unit h1 Q i a hQ hhom hd ha)).trans
    (valueChartEquiv Q i)
  exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
    (congrArg (fun n : ℕ => (n : ℚ)) e.toLinearEquiv.finrank_eq).trans hfinrank⟩

end

end K1_13_5_5_2_1_1
end PackSource_K1_13_5_5_2_1_1Split

section PackSource_K1_14_2_4_1_3_1Proof
set_option autoImplicit true
namespace K1_14_2_4_1_3_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_3 K1_13_6_3_4 MvPolynomial
open scoped Polynomial

set_option maxHeartbeats 1000000

private theorem parameter_regular {n : ℕ} (I : Ideal (ParameterRing n)) (hI : I.IsPrime)
    (hd : (affineHilbertPolynomial I).natDegree ≤ 1) :
    RegularLinearCut (extendedIdeal (SliceField n) I) (coefficientCut n) := by
  let p : Option (Fin n) → ParameterRing n := fun i => i.elim (-1) MvPolynomial.X
  have hw : LinearIndependent L (sliceVariable (n := n)) := by
    have h := (MvPolynomial.linearIndependent_X (Option (Fin n)) FX).map'
      (IsScalarTower.toAlgHom FX (SourceRing n) (SliceField n)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective (SourceRing n) (SliceField n)))
    exact h.restrict_scalars' (R := L)
  have hp (s : Option (Fin n)) : (p s).totalDegree ≤ 1 := by
    cases s <;> simp [p]
  have h := regular_generic_cut I hI p _ hw hp
    (fun b _ => ⟨none, by simp [p]⟩)
    (fun b _ hb => funext fun i => by simpa [p, (homogeneousComponent_eq_self
      (isHomogeneous_X L i))] using hb (some i)) hd
  simpa [coefficientCut, Fintype.sum_option, p, sub_eq_add_neg, add_comm] using h

private theorem independent_powers {k E : Type*} [Field k] [Field E] [Algebra k E]
    {x : E} (h : Transcendental k x) :
    LinearIndependent k (fun j : ℕ => x ^ j) := by
  have h' := (Polynomial.basisMonomials k).linearIndependent.map'
    (Polynomial.aeval x).toLinearMap (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp h))
  simpa [Function.comp_def, ← Polynomial.C_mul_X_pow_eq_monomial] using h'

private def xValue : FX := algebraMap L[X] FX Polynomial.X

private def ordinateWeight {a b : ℕ} (s : Fin a × Fin b) : SeedField :=
  algebraMap FX SeedField (xValue ^ s.2.val) * generic 1 ^ s.1.val

private theorem ordinateWeight_independent (a b : ℕ) :
    LinearIndependent L (ordinateWeight (a := a) (b := b)) := by
  have hx : Transcendental L xValue :=
    (transcendental_algebraMap_iff (IsFractionRing.injective L[X] FX)).2
      (Polynomial.transcendental_X L)
  have hy : Transcendental FX (generic 1) :=
    (transcendental_algebraMap_iff (IsFractionRing.injective Seeds SeedField)).2
      (MvPolynomial.transcendental_X FX 1)
  have hX := (independent_powers hx).comp (fun i : Fin b => i.val) Fin.val_injective
  have hY := (independent_powers hy).comp (fun j : Fin a => j.val) Fin.val_injective
  apply Fintype.linearIndependent_iff.mpr
  intro c hc s
  have he : ∑ j : Fin a, (∑ i : Fin b, c (j, i) • xValue ^ i.val) • generic 1 ^ j.val = 0 := by
    rw [Fintype.sum_prod_type] at hc
    simpa only [ordinateWeight, Algebra.smul_def, map_sum, map_mul,
      IsScalarTower.algebraMap_apply L FX SeedField, Finset.sum_mul, mul_assoc] using hc
  exact (Fintype.linearIndependent_iff.mp hX) (fun i => c (s.1, i))
    ((Fintype.linearIndependent_iff.mp hY) _ he s.1) s.2

private def xBound {n : ℕ} (f : FamilyEquation n) : ℕ :=
  (Finset.range (f.natDegree + 1)).sup (fun j => (f.coeff j).natDegree) + 1

private theorem lt_xBound {n : ℕ} (f : FamilyEquation n) {j : ℕ} (hj : j < f.natDegree + 1) :
    (f.coeff j).natDegree < xBound f :=
  Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (f.coeff j).natDegree) (Finset.mem_range.mpr hj))

private def gridCoefficient {n : ℕ} (f : FamilyEquation n)
    (s : Fin (f.natDegree + 1) × Fin (xBound f)) : ParameterRing n :=
  (f.coeff s.1.val).coeff s.2.val

private theorem ordinateForm_sum {n : ℕ} (f : FamilyEquation n) :
    ordinateForm f = ∑ s : Fin (f.natDegree + 1) × Fin (xBound f),
      MvPolynomial.C (ordinateWeight s) * map (algebraMap L SeedField) (gridCoefficient f s) := by
  let χ : (ParameterRing n)[X] →+* ParameterGeometry n :=
    Polynomial.eval₂RingHom (map (algebraMap L FX)) (MvPolynomial.C xValue)
  let ψ : ParameterGeometry n →+* MvPolynomial (Fin n) SeedField :=
    map (algebraMap FX SeedField)
  let y : MvPolynomial (Fin n) SeedField := MvPolynomial.C (generic 1)
  have hC (q : ParameterRing n) : ψ (χ (Polynomial.C q)) = map (algebraMap L SeedField) q := by
    change (map (algebraMap FX SeedField))
      ((Polynomial.C q).eval₂ (map (algebraMap L FX)) (MvPolynomial.C xValue)) = _
    rw [Polynomial.eval₂_C, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hX : ψ (χ Polynomial.X) = MvPolynomial.C (algebraMap FX SeedField xValue) := by
    change (map (algebraMap FX SeedField))
      (Polynomial.X.eval₂ (map (algebraMap L FX)) (MvPolynomial.C xValue)) = _
    rw [Polynomial.eval₂_X, map_C]
  have hout :
      f = ∑ j : Fin (f.natDegree + 1), Polynomial.C (f.coeff j.val) * Polynomial.X ^ j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (f.coeff j) * Polynomial.X ^ j)]
    exact f.as_sum_range_C_mul_X_pow
  have hin (j : Fin (f.natDegree + 1)) :
      ψ (χ (f.coeff j.val)) =
        ∑ i : Fin (xBound f), MvPolynomial.C (algebraMap FX SeedField (xValue ^ i.val)) *
          map (algebraMap L SeedField) ((f.coeff j.val).coeff i.val) := by
    have hs : f.coeff j.val = ∑ i : Fin (xBound f),
        Polynomial.C ((f.coeff j.val).coeff i.val) * Polynomial.X ^ i.val := by
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        Polynomial.C ((f.coeff j.val).coeff i) * Polynomial.X ^ i)]
      exact (f.coeff j.val).as_sum_range_C_mul_X_pow' (lt_xBound f j.isLt)
    calc
      _ = ψ (χ (∑ i : Fin (xBound f),
          Polynomial.C ((f.coeff j.val).coeff i.val) * Polynomial.X ^ i.val)) :=
        congrArg (ψ ∘ χ) hs
      _ = _ := by
        simp only [map_sum, map_mul, map_pow, hC, hX]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
  change (f.map χ).eval₂ ψ y = _
  rw [Polynomial.eval₂_map]
  let ε := Polynomial.eval₂RingHom (ψ.comp χ) y
  change ε f = _
  rw [congrArg ε hout, map_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_pow]
  simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
    RingHom.comp_apply]
  rw [hin, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [y, ← map_pow MvPolynomial.C, gridCoefficient, ordinateWeight, map_mul]
  ac_rfl

private theorem chart_grid_representation {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) (i : Fin n) :
    MvPolynomial.X i ∈ coefficientIdeal A ∨
      ∃ s : Fin (A.equation.natDegree + 1) × Fin (xBound A.equation),
        gridCoefficient A.equation s - MvPolynomial.X i ∈ coefficientIdeal A := by
  obtain ⟨j, k, h⟩ := coefficient_representation A i
  by_cases hj : j < A.equation.natDegree + 1
  · by_cases hk : k < xBound A.equation
    · exact Or.inr ⟨(⟨j, hj⟩, ⟨k, hk⟩), h⟩
    · have hz : (A.equation.coeff j).coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (lt_xBound _ hj) (by omega))
      left
      simpa [hz] using h
  · have hz : A.equation.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    left
    simpa [hz] using h

private theorem chart_has_coefficient {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n)
    (b : Fin n → L) (hb : b ∈ zeroLocus L (coefficientIdeal A)) :
    ∃ s : Fin (A.equation.natDegree + 1) × Fin (xBound A.equation),
      eval b (gridCoefficient A.equation s) ≠ 0 := by
  by_contra! h
  have hb0 (i : Fin n) : b i = 0 := by
    rcases chart_grid_representation A i with hi | ⟨s, hs⟩
    · simpa [aeval_eq_eval] using hb _ hi
    · have he := hb _ hs
      simpa [aeval_eq_eval, h s] using he
  obtain ⟨ℓ, hℓ⟩ := coefficient_normalization A
  have hnorm := hb _ hℓ
  simp [aeval_eq_eval, hb0] at hnorm

private theorem chart_boundary_has_coefficient {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n)
    (b : Fin n → L) (hb : b ∈ zeroLocus L (boundaryIdeal (coefficientIdeal A)))
    (h : ∀ s, eval b (homogeneousComponent 1 (gridCoefficient A.equation s)) = 0) :
    b = 0 := by
  funext i
  rcases chart_grid_representation A i with hi | ⟨s, hs⟩
  · have hX : MvPolynomial.X i ∈ boundaryIdeal (coefficientIdeal A) :=
      Ideal.subset_span ⟨MvPolynomial.X i, 1, hi, (totalDegree_X i).le,
        (homogeneousComponent_eq_self (isHomogeneous_X L i)).symm⟩
    simpa [aeval_eq_eval] using hb _ hX
  · have hd : (gridCoefficient A.equation s - MvPolynomial.X i).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (A.degree.2 _ _) (totalDegree_X i).le)
    have he := hb _ (Ideal.subset_span ⟨_, 1, hs, hd, rfl⟩)
    simpa [aeval_eq_eval, homogeneousComponent_eq_self (isHomogeneous_X L i), h s] using he

theorem proof : K1_14_2_4_1_3.c1 := by
  intro C₀ _ J g n R A hd
  have hI : (coefficientIdeal A).IsPrime := RingHom.ker_isPrime _
  refine ⟨parameter_regular _ hI hd, ?_⟩
  rw [ordinateForm_sum]
  exact regular_generic_cut _ hI (gridCoefficient A.equation) _
    (ordinateWeight_independent _ _) (fun s => A.degree.2 s.1 s.2)
    (chart_has_coefficient A) (chart_boundary_has_coefficient A) hd

end
end K1_14_2_4_1_3_1
end PackSource_K1_14_2_4_1_3_1Proof

section PackSource_K1_14_2_4_1_3_2_1Proof
set_option autoImplicit true
set_option maxHeartbeats 600000

namespace K1_14_2_4_1_3_2_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_4 K1_14_2_4_1 K1_14_2_4_1_3 K1_14_2_4_1_3_2
open MvPolynomial
open scoped Polynomial

private theorem fraction_mem {P T : Type*} [CommRing P] [Field T]
    [Algebra P T] [IsFractionRing P T] (U : Subfield T)
    (h : ∀ p : P, algebraMap P T p ∈ U) (x : T) : x ∈ U := by
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective P x
  exact U.div_mem (h p) (h q)

theorem proof : K1_14_2_4_1_3_2.c1 := by
  intro C₀ _ J g n R A h
  let : Algebra L (ConstantSeedField C₀) := (constToSeed C₀).toAlgebra
  let := sliceAlgebra (coefficientParameter A.coordinate)
    (coefficientParameter_injective A.coordinate h)
  intro hfinite
  classical
  let S := SliceField n
  let F := CoefficientField A.coordinate
  let B := FractionRing F[X]
  let W := RationalWeightRing F n
  let T := RationalWeightField F n
  let a := coefficientTuple A.coordinate
  let k : W →+* T := algebraMap W T
  let b : B →+* T := k.comp MvPolynomial.C
  let c : F →+* T := b.comp ((algebraMap F[X] B).comp Polynomial.C)
  let ev : MvPolynomial (Fin n) S →ₐ[S] T := aeval (c ∘ a)
  have hFX (x : FX) :
      algebraMap S T (algebraMap FX S x) = b (abscissaMap (algebraMap L F) x) := by
    rw [IsScalarTower.algebraMap_apply FX (SourceRing n) S]
    rw [MvPolynomial.algebraMap_eq, sliceAlgebra_apply]
    exact congrArg k (eval₂Hom_C _ _ _)
  have hL (x : L) :
      algebraMap S T (algebraMap L S x) = c (algebraMap L F x) := by
    rw [IsScalarTower.algebraMap_apply L FX S, hFX]
    rw [IsScalarTower.algebraMap_apply L L[X] FX, Polynomial.algebraMap_eq]
    simp only [c, RingHom.comp_apply, abscissaMap, IsFractionRing.map,
      IsLocalization.map_eq, Polynomial.coe_mapRingHom, Polynomial.map_C]
    rfl
  have ev_coeff :
      ev.toRingHom.comp (MvPolynomial.map (algebraMap L S)) =
        c.comp (eval₂Hom (algebraMap L F) a) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.map_C, eval₂Hom_C]
      change aeval (R := S) (c ∘ a) (C (algebraMap L S x)) = _
      rw [aeval_C, hL]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, eval₂Hom_X']
      exact aeval_X (R := S) (c ∘ a) i
  have coeff_compat :
      F.val.toRingHom.comp (eval₂Hom (algebraMap L F) a) =
        eval₂Hom (constToSeed C₀) A.coordinate := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, eval₂Hom_C]
      rfl
    · intro i
      simp only [RingHom.comp_apply, eval₂Hom_X']
      rfl
  have hweight (i : Fin n) : algebraMap S T (sliceVariable (some i)) = k (MvPolynomial.X i) := by
    rw [sliceVariable, sliceAlgebra_apply]
    simp only [coefficientParameter, parameterEval, eval₂Hom_X', Option.elim_some]
    rfl
  have hoffset : algebraMap S T (sliceVariable (n := n) none) =
      ∑ i, k (MvPolynomial.X i) * c (a i) := by
    rw [sliceVariable, sliceAlgebra_apply]
    simp only [coefficientParameter, parameterEval, eval₂Hom_X', Option.elim_none,
      map_sum, map_mul]
    rfl
  have hcut :
      extendedIdeal S (coefficientIdeal A) ⊔ Ideal.span {coefficientCut n} ≤
        RingHom.ker ev.toRingHom := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      have hz : eval₂Hom (algebraMap L F) a p = 0 := by
        apply F.val.toRingHom.injective
        rw [map_zero, ← RingHom.comp_apply, coeff_compat]
        exact RingHom.mem_ker.mp hp
      change (ev.toRingHom.comp (MvPolynomial.map (algebraMap L S))) p = 0
      rw [ev_coeff, RingHom.comp_apply, hz, map_zero]
    · intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change ev (coefficientCut n) = 0
      rw [coefficientCut, map_sub, sub_eq_zero, map_sum]
      change _ = aeval (R := S) (c ∘ a) (C (sliceVariable (n := n) none))
      rw [aeval_C, hoffset]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      change aeval (R := S) (c ∘ a) (C (sliceVariable (some i))) *
        aeval (R := S) (c ∘ a) (MvPolynomial.X i) = _
      rw [aeval_C, aeval_X, hweight]
      rfl
  let f : CoefficientSection A →ₐ[S] T :=
    Ideal.Quotient.liftₐ _ ev (fun p hp => RingHom.mem_ker.mp (hcut hp))
  refine ⟨f, ?_⟩

  -- The image is a finite domain over the slice field, hence is closed under division.
  let : Module.Finite S f.range :=
    Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  let U := f.range.toIntermediateField' (IsField.of_isDomain_of_finite S f.range)
  have hcoord (i : Fin n) : c (a i) ∈ U := by
    refine (AlgHom.mem_range f).mpr ⟨Ideal.Quotient.mk _ (MvPolynomial.X i), ?_⟩
    change ev (MvPolynomial.X i) = _
    exact aeval_X (c ∘ a) i

  -- Pull back the image along the two constant embeddings to use field generation.
  let V : Subfield B := U.toSubfield.comap b
  let D : Subfield F := V.comap ((algebraMap F[X] B).comp Polynomial.C)
  let D' : IntermediateField L (ConstantSeedField C₀) :=
    (D.map F.val.toRingHom).toIntermediateField (fun x =>
      ⟨algebraMap L F x, by
        change c (algebraMap L F x) ∈ U
        rw [← hL]
        exact U.algebraMap_mem _, rfl⟩)
  have hF : F ≤ D' := IntermediateField.adjoin_le_iff.mpr (by
    rintro _ ⟨i, rfl⟩
    exact ⟨a i, hcoord i, rfl⟩)
  have hconst (x : F) : (algebraMap F[X] B) (Polynomial.C x) ∈ V := by
    obtain ⟨y, hy, hyx⟩ := hF x.property
    exact (F.val.toRingHom.injective hyx : y = x) ▸ hy
  have hx : algebraMap F[X] B Polynomial.X ∈ V := by
    change b (algebraMap F[X] B Polynomial.X) ∈ U
    have he := hFX (algebraMap L[X] FX Polynomial.X)
    simp only [abscissaMap, IsFractionRing.map, IsLocalization.map_eq,
      Polynomial.coe_mapRingHom, Polynomial.map_X] at he
    rw [← he]
    exact U.algebraMap_mem _
  have hB (x : B) : x ∈ V := by
    apply fraction_mem (P := F[X]) V _ x
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact V.add_mem hp hq
    | monomial m y =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact V.mul_mem (hconst y) (V.pow_mem hx m)
  intro x
  apply (AlgHom.mem_range f).mp
  change x ∈ U.toSubfield
  apply fraction_mem (P := W) U.toSubfield _ x
  intro p
  change k p ∈ U
  induction p using MvPolynomial.induction_on with
  | C y => exact hB y
  | add p q hp hq =>
    rw [map_add]
    exact U.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, ← hweight]
    exact U.mul_mem hp (U.algebraMap_mem _)

end

end K1_14_2_4_1_3_2_1
end PackSource_K1_14_2_4_1_3_2_1Proof

section PackSource_K1_13_5_5_2_3_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace K1_13_5_5_2_3_2

noncomputable section

open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_3 MvPolynomial
open scoped TensorProduct

section ScalarExtension

variable {k E σ ι : Type*} [Field k] [Field E] [Algebra k E]

private abbrev scalarMap : MvPolynomial σ k →+* MvPolynomial σ E :=
  MvPolynomial.map (algebraMap k E)

private def quotientTensor (I : Ideal (MvPolynomial σ k)) :
    E ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[E] MvPolynomial σ E ⧸ I.map scalarMap := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  let ι' : MvPolynomial σ k →ₐ[k] E ⊗[k] MvPolynomial σ k :=
    Algebra.TensorProduct.includeRight
  have hcomp : e.toRingHom.comp ι'.toRingHom = scalarMap := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = _
    simp [e, scalarMap]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k) E _ E I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  exact ((Ideal.map_map (I := I) ι'.toRingHom e.toRingHom).trans
    (congrArg (fun f => I.map f) hcomp)).symm

private theorem quotientTensor_tmul (I : Ideal (MvPolynomial σ k))
    (a : E) (p : MvPolynomial σ k) :
    quotientTensor I (a ⊗ₜ[k] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (I.map scalarMap) (MvPolynomial.algebraTensorAlgEquiv k E (a ⊗ₜ[k] p)) := by
  simp only [quotientTensor, AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  rfl

/-- Extract the polynomial in one field-basis coordinate. -/
private def piece [DecidableEq ι] (b : Module.Basis ι k E) (p : MvPolynomial σ E) (i : ι) :
    MvPolynomial σ k :=
  TensorProduct.equivFinsuppOfBasisLeft b ((MvPolynomial.algebraTensorAlgEquiv k E).symm p) i

private theorem coeff_piece [DecidableEq ι] (b : Module.Basis ι k E) (p : MvPolynomial σ E)
    (i : ι) (d : σ →₀ ℕ) : (piece b p i).coeff d = b.coord i (p.coeff d) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  obtain ⟨t, rfl⟩ := e.surjective p
  simp only [piece, show MvPolynomial.algebraTensorAlgEquiv k E = e from rfl,
    AlgEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul a q =>
    simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, e,
      algebraTensorAlgEquiv_tmul, coeff_smul, coeff_map]
    have hs : a • algebraMap k E (q.coeff d) = q.coeff d • a := by
      rw [smul_eq_mul, Algebra.smul_def, mul_comm]
    simp only [hs, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm]
  | add t u ht hu =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ht, hu]

private theorem mem_map_iff [DecidableEq ι] (b : Module.Basis ι k E)
    (I : Ideal (MvPolynomial σ k)) (p : MvPolynomial σ E) :
    p ∈ I.map scalarMap ↔ ∀ i, piece b p i ∈ I := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  let eI : E ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[E] _ := quotientTensor I
  let s := TensorProduct.equivFinsuppOfBasisLeft (N := MvPolynomial σ k ⧸ I) b
  obtain ⟨t, rfl⟩ := e.surjective p
  have hc (i : ι) :
      s (eI.symm (Ideal.Quotient.mk (I.map scalarMap) (e t))) i =
        Ideal.Quotient.mk I (TensorProduct.equivFinsuppOfBasisLeft b t i) := by
    induction t using TensorProduct.inductionOn with
    | tmul a q =>
      rw [← quotientTensor_tmul I a q]
      simp only [eI, AlgEquiv.symm_apply_apply, s,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact (map_smul (Ideal.Quotient.mkₐ k I) _ _).symm
    | add t u ht hu =>
      simp only [map_add, Finsupp.add_apply, ht, hu]
  simp only [piece, show MvPolynomial.algebraTensorAlgEquiv k E = e from rfl,
    AlgEquiv.symm_apply_apply, ← Ideal.Quotient.eq_zero_iff_mem, ← hc]
  constructor
  · intro h i
    simp [h]
  · intro h
    have hz : s (eI.symm (Ideal.Quotient.mk (I.map scalarMap) (e t))) = 0 :=
      Finsupp.ext h
    exact eI.symm.injective (s.injective (hz.trans (by simp)))

/-- The degree bound holds coordinatewise in a scalar extension. -/
private theorem component_mem_map_infinity (I : Ideal (MvPolynomial σ k)) {p : MvPolynomial σ E}
    (hp : p ∈ I.map scalarMap) {n : ℕ} (hn : p.totalDegree ≤ n) :
    homogeneousComponent n p ∈ (infinityIdeal I).map scalarMap := by
  classical
  let b := Module.Basis.ofVectorSpace k E
  apply (mem_map_iff b _ _).2
  intro i
  have hi := (mem_map_iff b I p).1 hp i
  have hdeg : (piece b p i).totalDegree ≤ p.totalDegree := by
    apply Finset.sup_mono
    intro d hd
    rw [MvPolynomial.mem_support_iff, coeff_piece] at hd
    exact MvPolynomial.mem_support_iff.mpr fun h => hd (by rw [h, map_zero])
  have he : piece b (homogeneousComponent n p) i = homogeneousComponent n (piece b p i) := by
    ext d
    by_cases hd : d.degree = n <;> simp [coeff_piece, coeff_homogeneousComponent, hd]
  rw [he]
  rcases eq_or_lt_of_le (hdeg.trans hn) with h | h
  · refine Ideal.subset_span ⟨piece b p i, hi, ?_⟩
    change homogeneousComponent (piece b p i).totalDegree (piece b p i) = _
    rw [h]
  · rw [homogeneousComponent_eq_zero n _ h]
    exact Ideal.zero_mem _

end ScalarExtension

section Specialization

variable {K σ : Type} [Field K]

private def atW (w : MvPolynomial σ K) :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => i.elim w MvPolynomial.X)

private theorem atW_monomial (w : MvPolynomial σ K) (d : Option σ →₀ ℕ) (r : K) :
    atW w (monomial d r) = w ^ (d none) * monomial d.some r := by
  rw [atW, aeval_monomial, algebraMap_eq, Finsupp.prod_option_index]
  · rw [monomial_eq (s := d.some) (a := r)]
    simp only [Option.elim_none, Option.elim_some]
    ac_rfl
  · simp
  · intros
    rw [pow_add]

/-- Homogeneous evaluation at one keeps only degrees up to the original degree.
Evaluation at zero keeps exactly the top-degree component of evaluation at one. -/
private theorem atW_homogeneous {q : MvPolynomial (Option σ) K} {n : ℕ}
    (hq : q.IsHomogeneous n) :
    (atW 1 q).totalDegree ≤ n ∧ atW 0 q = homogeneousComponent n (atW 1 q) := by
  change q.IsWeightedHomogeneous (fun _ => 1) n at hq
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq =>
    simp only [map_add]
    exact ⟨(totalDegree_add _ _).trans (max_le hp.1 hq.1), by rw [hp.2, hq.2]⟩
  | monomial d r hd =>
    rw [← Finsupp.degree_eq_weight_one] at hd
    have hdeg : d none + d.some.degree = n := by
      have hsplit : d.degree = d none + d.some.degree := by
        simp only [Finsupp.degree_apply]
        exact Finsupp.sum_option_index d (fun _ m => m) (by simp) (by intros; rfl)
      rwa [← hsplit]
    simp only [atW_monomial, one_pow, one_mul]
    have hle : d.some.degree ≤ n := by omega
    refine ⟨(totalDegree_monomial_le d.some r).trans hle, ?_⟩
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial (d := d.some) r rfl)]
    by_cases hz : d none = 0
    · have he : n = d.some.degree := by omega
      simp [hz, he]
    · have he : n ≠ d.some.degree := by omega
      simp [zero_pow hz, he]

private theorem eval_scaled {α B : Type} [CommRing B] [Algebra K B]
    (x : α → B) (t : B) {q : MvPolynomial α K} {n : ℕ} (hq : q.IsHomogeneous n) :
    aeval (fun i => t * x i) q = t ^ n * aeval x q := by
  change q.IsWeightedHomogeneous (fun _ => 1) n at hq
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add, mul_add, hp, hq]
  | monomial d r hd =>
    rw [← Finsupp.degree_eq_weight_one] at hd
    rw [← hd, aeval_monomial, aeval_monomial]
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finsupp.degree_apply]
    ac_rfl

private theorem closureEval_homogeneous (I : Ideal (MvPolynomial σ K))
    {q : MvPolynomial (Option σ) K} {n : ℕ} (hq : q.IsHomogeneous n) :
    closureEval I q = Polynomial.monomial n (Ideal.Quotient.mk I (atW 1 q)) := by
  let m : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K ⧸ I) :=
    Polynomial.CAlgHom.comp (Ideal.Quotient.mkₐ K I)
  let x : Option σ → Polynomial (MvPolynomial σ K ⧸ I) := fun i => m (i.elim 1 MvPolynomial.X)
  have hscaled : closureEval I = aeval (fun i => Polynomial.X * x i) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [closureEval, x, m]
  have hx : aeval x = m.comp (atW 1) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [aeval_X, AlgHom.comp_apply, x, atW]
  rw [hscaled, eval_scaled x Polynomial.X hq, hx, AlgHom.comp_apply]
  change Polynomial.X ^ n * Polynomial.C (Ideal.Quotient.mk I (atW 1 q)) = _
  exact (Polynomial.X_pow_mul_C (Ideal.Quotient.mk I (atW 1 q)) n).trans
    Polynomial.C_mul_X_pow_eq_monomial

private theorem closure_specialization (I J : Ideal (MvPolynomial σ K))
    (hcomponent : ∀ (f : MvPolynomial σ K) (n : ℕ), f ∈ I → f.totalDegree ≤ n →
      homogeneousComponent n f ∈ J) :
    ∃ s : Closure I →ₐ[K] (MvPolynomial σ K ⧸ J),
      Function.Surjective s ∧ s (closureW I) = 0 ∧
      ∀ f, s (closureLift I f) = Ideal.Quotient.mk J f := by
  let e := (Ideal.Quotient.mkₐ K J).comp (atW 0)
  have hker (q : MvPolynomial (Option σ) K) (hq : q ∈ closureIdeal I) : e q = 0 := by
    change closureEval I q = 0 at hq
    have h : closureEval I q =
        ∑ j ∈ Finset.range (q.totalDegree + 1),
          Polynomial.monomial j (Ideal.Quotient.mk I (atW 1 (homogeneousComponent j q))) := by
      conv_lhs => rw [← sum_homogeneousComponent q, map_sum]
      exact Finset.sum_congr rfl fun j _ =>
        closureEval_homogeneous I (homogeneousComponent_isHomogeneous j q)
    have hm (n : ℕ) (hn : n ∈ Finset.range (q.totalDegree + 1)) :
        atW 0 (homogeneousComponent n q) ∈ J := by
      have hcoeff := congrArg (fun p : Polynomial (MvPolynomial σ K ⧸ I) => p.coeff n) h.symm
      have hz : Ideal.Quotient.mk I (atW 1 (homogeneousComponent n q)) = 0 := by
        simpa only [hq, Polynomial.coeff_zero, Polynomial.finsetSum_coeff,
          Polynomial.coeff_monomial, Finset.sum_ite_eq', ite_eq_left hn] using hcoeff
      obtain ⟨hdeg, he⟩ := atW_homogeneous (homogeneousComponent_isHomogeneous n q)
      rw [he]
      exact hcomponent _ _ (Ideal.Quotient.eq_zero_iff_mem.mp hz) hdeg
    change Ideal.Quotient.mk J (atW 0 q) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← sum_homogeneousComponent q, map_sum]
    exact Ideal.sum_mem _ hm
  let s := Ideal.Quotient.liftₐ (closureIdeal I) e hker
  have hLift (f : MvPolynomial σ K) : s (closureLift I f) = Ideal.Quotient.mk J f := by
    have hid : (atW (0 : MvPolynomial σ K)).comp (rename some) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [atW]
    change Ideal.Quotient.mk J (atW 0 (rename some f)) = Ideal.Quotient.mk J f
    exact congrArg (Ideal.Quotient.mk J) (DFunLike.congr_fun hid f)
  refine ⟨s, ?_, ?_, hLift⟩
  · intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨closureLift I f, hLift f⟩
  · change Ideal.Quotient.mk J (atW 0 (MvPolynomial.X none)) = 0
    simp [atW]

end Specialization

private theorem linear_sum_homogeneous {k σ : Type} [Field k] [Fintype σ] (c : σ → k) :
    (∑ i : σ, C (c i) * MvPolynomial.X i).IsHomogeneous 1 :=
  (homogeneousSubmodule σ k 1).sum_mem fun i _ => isHomogeneous_C_mul_X _ i

private theorem projection_homogeneous {f : FreshJetRing} {n : ℕ} (hf : f.IsHomogeneous n) :
    (freshProjection f).IsHomogeneous n := by
  have h (j : Fin 3) : (jetForm freshCenter j.val).IsHomogeneous 1 := by
    exact linear_sum_homogeneous fun i : CoeffIndex =>
      (i.val.choose j.val : FreshField) * freshCenter ^ (i.val - j.val)
  simpa only [freshProjection, one_mul] using hf.aeval _ h

private theorem projection_top (g : FreshJetRing) :
    (freshProjection g).totalDegree ≤ g.totalDegree ∧
      homogeneousComponent g.totalDegree (freshProjection g) = freshProjection (topForm g) := by
  have hsum : freshProjection g = ∑ j ∈ Finset.range (g.totalDegree + 1),
      freshProjection (homogeneousComponent j g) := by
    conv_lhs => rw [← sum_homogeneousComponent g, map_sum]
  have hhom (j : ℕ) : (freshProjection (homogeneousComponent j g)).IsHomogeneous j :=
    projection_homogeneous (homogeneousComponent_isHomogeneous j g)
  constructor
  · rw [hsum]
    exact totalDegree_finsetSum_le fun j hj =>
      (hhom j).totalDegree_le.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  · rw [hsum, map_sum]
    simp only [homogeneousComponent_of_mem (hhom _), Finset.sum_ite_eq, Finset.mem_range,
      Nat.lt_succ_self, ite_true, topForm]

theorem proof : K1_13_5_5_2_3.c2 := by
  intro P g d h
  have hg : freshProjection g ∈ freshIdeal P := by
    change g ∈ (freshIdeal P).comap freshProjection
    rw [h.image]
    exact Ideal.subset_span (Set.mem_singleton g)
  obtain ⟨hdeg, htop⟩ := projection_top g
  have hc (f : FreshCoeffRing) (n : ℕ) (hf : f ∈ freshIdeal P) (hn : f.totalDegree ≤ n) :
      homogeneousComponent n f ∈ freshIdeal (infinityIdeal P) :=
    component_mem_map_infinity P hf hn
  refine ⟨?_, closure_specialization _ _ hc⟩
  change freshProjection (topForm g) ∈ freshIdeal (infinityIdeal P)
  rw [← htop]
  exact hc _ _ hg hdeg

end

end K1_13_5_5_2_3_2
end PackSource_K1_13_5_5_2_3_2Proof

section PackSource_K1_13_5_5_2_1_5Aux1
set_option autoImplicit true
namespace K1_13_5_5_2_1_5

noncomputable section

open MvPolynomial K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open scoped Polynomial

set_option maxHeartbeats 1000000

theorem homogeneous_aeval_mul {F B σ : Type} [Field F] [CommRing B] [Algebra F B]
    {p : MvPolynomial σ F} {n : ℕ} (hp : p.IsHomogeneous n) (x : σ → B) (s : B) :
    aeval (fun i => s * x i) p = s ^ n * aeval x p := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd := hp.degree_eq_sum_deg_support hm
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← hd]
  ac_rfl

/-- The cone substitution uses a free scaling variable in degree one. -/
def scaled {F B σ : Type} [Field F] [CommRing B] [Algebra F B] (d : σ → B) :
    MvPolynomial σ F →ₐ[F] B[X] :=
  aeval (fun i => Polynomial.C (d i) * Polynomial.X)

theorem scaled_homogeneous {F B σ : Type} [Field F] [CommRing B] [Algebra F B]
    (d : σ → B) {p : MvPolynomial σ F} {n : ℕ} (hp : p.IsHomogeneous n) :
    scaled d p = Polynomial.monomial n (aeval d p) := by
  let c : B →ₐ[F] B[X] := Polynomial.CAlgHom
  change aeval (fun i => c (d i) * Polynomial.X) p = _
  simp_rw [mul_comm (c _), homogeneous_aeval_mul hp]
  rw [← comp_aeval_apply d c p]
  change Polynomial.X ^ n * Polynomial.C (aeval d p) = _
  rw [Polynomial.X_pow_mul_C, Polynomial.C_mul_X_pow_eq_monomial]

private theorem scaled_coeff {F B σ : Type} [Field F] [CommRing B] [Algebra F B]
    (d : σ → B) (p : MvPolynomial σ F) (n : ℕ) :
    (scaled d p).coeff n = aeval d (homogeneousComponent n p) := by
  classical
  by_cases hn : n ≤ p.totalDegree
  · conv_lhs => rw [← sum_homogeneousComponent p]
    rw [map_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
    · rw [scaled_homogeneous d (homogeneousComponent_isHomogeneous _ _)]
      simp
    · intro b _ hb
      rw [scaled_homogeneous d (homogeneousComponent_isHomogeneous _ _)]
      simp [Polynomial.coeff_monomial, hb]
    · simp [Finset.mem_range, hn]
  · rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]
    conv_lhs => rw [← sum_homogeneousComponent p]
    rw [map_sum, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [scaled_homogeneous d (homogeneousComponent_isHomogeneous _ _)]
    have hbn : b ≠ n := by simp only [Finset.mem_range] at hb; omega
    simp [Polynomial.coeff_monomial, hbn]

/-- A relation can be divided by its full power of the fixed coordinate. Its homogeneous
component detected by any surviving coefficient still vanishes under the cone substitution. -/
theorem relation_on_value_plane {F B : Type} [Field F] [CommRing B] [IsDomain B]
    [Algebra F B] {m : ℕ} (d : Fin (m + 1) → B) (hd : d 0 ≠ 0)
    (h : ¬ Function.Injective (scaled (F := F) d)) :
    ∃ p : MvPolynomial (Fin (m + 1)) F, ∃ n : ℕ,
      p.IsHomogeneous n ∧ aeval d p = 0 ∧ (finSuccEquiv F m p).coeff 0 ≠ 0 := by
  classical
  rw [injective_iff_map_eq_zero] at h
  push Not at h
  obtain ⟨p, hp, hp0⟩ := h
  let e := finSuccEquiv F m
  let k := (e p).natTrailingDegree
  have hdv : Polynomial.X ^ k ∣ e p :=
    Polynomial.X_pow_dvd_iff.mpr fun j hj =>
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
  obtain ⟨r, hr⟩ := hdv
  let q := e.symm r
  have hqeq : p = MvPolynomial.X 0 ^ k * q := by
    apply e.injective
    simpa [e, q, finSuccEquiv_X_zero] using hr
  have hq : scaled d q = 0 := by
    rw [hqeq, map_mul, map_pow] at hp
    refine (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ ?_)
    simpa [scaled] using hd
  have hr0 : r.coeff 0 ≠ 0 := by
    have hcoeff : (e p).coeff k = r.coeff 0 := by
      rw [hr]
      simpa using Polynomial.coeff_X_pow_mul r k 0
    rw [← hcoeff, Polynomial.coeff_natTrailingDegree_ne_zero]
    simpa [map_eq_zero_iff _ e.injective] using hp0
  obtain ⟨a, ha⟩ := exists_coeff_ne_zero hr0
  have haq : ((finSuccEquiv F m q).coeff 0).coeff a ≠ 0 := by
    simpa [q, e] using ha
  rw [finSuccEquiv_coeff_coeff] at haq
  let n := (a.cons 0).degree
  refine ⟨homogeneousComponent n q, n, homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
  · simpa [scaled_coeff] using congrArg (fun f : B[X] => f.coeff n) hq
  · intro hz
    have hz' := congrArg (fun f : MvPolynomial (Fin m) F => f.coeff a) hz
    rw [finSuccEquiv_coeff_coeff, coeff_homogeneousComponent, ite_eq_left rfl] at hz'
    exact haq (by simpa using hz')

private theorem ideal_ne_bot_of_finite_pair {F : Type} [Field F]
    {I : Ideal (MvPolynomial (Fin 3) F)}
    (g : MvPolynomial (Fin 2) F →ₐ[F] MvPolynomial (Fin 3) F ⧸ I)
    (hg : g.Finite) : I ≠ ⊥ := by
  intro hbot
  let e := AlgEquiv.quotientBot F (MvPolynomial (Fin 2) F)
  have hdeg := natDegree_affineHilbertPolynomial_le_of_finite (g.comp e.toAlgHom)
    (RingHom.Finite.comp hg e.toRingEquiv.finite)
  rw [hbot, natDegree_affineHilbertPolynomial_bot, natDegree_affineHilbertPolynomial_bot,
    Nat.card_fin, Nat.card_fin] at hdeg
  omega

theorem cone_has_relation {A : Type} [CommRing A] [IsDomain A] [Algebra FreshField A]
    (d : Fin 3 → A) (L : Fin 2 → FreshJetRing) (hL : FiniteJetPair L (coneJetIdeal d)) :
    ¬ Function.Injective (scaled (F := FreshField) d) := by
  intro hinj
  apply ideal_ne_bot_of_finite_pair (jetPairMap L (coneJetIdeal d)) hL.2
  exact (RingHom.injective_iff_ker_eq_bot (coneJetMap d).toRingHom).mp hinj

/-- A homogeneous relation that survives on the value plane is nonzero in a direction
of the form `(0, t, 1)`, since the base field is infinite. -/
theorem choose_direction {F : Type} [Field F] [Infinite F]
    {p : MvPolynomial (Fin 3) F} {n : ℕ} (hp : p.IsHomogeneous n)
    (h0 : (finSuccEquiv F 2 p).coeff 0 ≠ 0) : ∃ t : F, eval ![0, t, 1] p ≠ 0 := by
  classical
  by_contra! ht
  apply h0
  let s : Fin 2 → Set F := ![Set.univ, {0}ᶜ]
  have hs : ∀ i, (s i).Infinite := by
    intro i
    fin_cases i
    · exact Set.infinite_univ
    · exact (Set.finite_singleton (0 : F)).infinite_compl
  apply MvPolynomial.funext_set s hs
  intro x hx
  have hx1 : x 1 ≠ 0 := by
    simpa [s] using hx (1 : Fin 2) (Set.mem_univ _)
  have he : (fun i => x 1 * (![0, x 0 / x 1, 1] : Fin 3 → F) i) = Fin.cons 0 x := by
    ext i
    fin_cases i
    · simp
    · change x 1 * (x 0 / x 1) = Fin.cons (α := fun _ => F) 0 x (0 : Fin 2).succ
      simp [div_eq_mul_inv, ← mul_assoc, mul_comm (x 1) (x 0), hx1]
    · change x 1 * 1 = Fin.cons (α := fun _ => F) 0 x (1 : Fin 2).succ
      rw [Fin.cons_succ, mul_one]
  have h := homogeneous_aeval_mul hp (![0, x 0 / x 1, 1] : Fin 3 → F) (x 1)
  rw [he, aeval_eq_eval, aeval_eq_eval, ht, mul_zero] at h
  rw [eval_eq_eval_mv_eval', ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h
  simpa using h

end

end K1_13_5_5_2_1_5
end PackSource_K1_13_5_5_2_1_5Aux1

section PackSource_K1_13_5_5_2_1_1_3Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_5_2_1_1_3

noncomputable section

open MvPolynomial
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type} [Field k]

private abbrev chart (I : Ideal (MvPolynomial σ k)) (i : σ) :
    Ideal (MvPolynomial σ k) :=
  I ⊔ Ideal.span {MvPolynomial.X i - 1}

/-- The image of one homogeneous piece in the coordinate quotient. -/
private def piece (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (homogeneousSubmodule σ k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

private theorem mem_piece {I : Ideal (MvPolynomial σ k)} {n : ℕ}
    {z : MvPolynomial σ k ⧸ I} :
    z ∈ piece I n ↔ ∃ p : MvPolynomial σ k, p.IsHomogeneous n ∧
      Ideal.Quotient.mk I p = z :=
  Submodule.mem_map

private instance [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.Finite k (piece I n) :=
  Module.Finite.of_fg ((homogeneousSubmodule_fg σ k n).map _)

private theorem piece_le_filtered (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    piece I n ≤ quotientDegreeLE I n := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := mem_piece.mp hz
  exact mk_mem_quotientDegreeLE hp.totalDegree_le

private theorem totalDegree_sub_component_le {p : MvPolynomial σ k} {n : ℕ}
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
  exact Nat.le_of_lt_succ (lt_of_le_of_ne
    ((le_totalDegree (MvPolynomial.mem_support_iff.mpr hd)).trans hp) hne)

/-- For a homogeneous ideal the filtration splits at each degree. -/
private theorem piece_finrank_succ [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (piece I (n + 1)) + affineHilbertFunction I n =
      affineHilbertFunction I (n + 1) := by
  have hsup : quotientDegreeLE I n ⊔ piece I (n + 1) = quotientDegreeLE I (n + 1) := by
    refine le_antisymm (sup_le (quotientDegreeLE_mono I (Nat.le_succ n))
      (piece_le_filtered I (n + 1))) ?_
    intro z hz
    obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hz
    refine Submodule.mem_sup.mpr ⟨_, mk_mem_quotientDegreeLE
      (totalDegree_sub_component_le hp), Ideal.Quotient.mk I (homogeneousComponent (n + 1) p),
      mem_piece.mpr ⟨_, homogeneousComponent_isHomogeneous (n + 1) p, rfl⟩, ?_⟩
    rw [← map_add, sub_add_cancel]
  have hinf : quotientDegreeLE I n ⊓ piece I (n + 1) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    obtain ⟨a, ha, haz⟩ := mem_quotientDegreeLE.mp hz.1
    obtain ⟨b, hb, hbz⟩ := mem_piece.mp hz.2
    have hba : b - a ∈ I := Ideal.Quotient.eq.mp (hbz.trans haz.symm)
    have hm := homogeneousComponent_mem_of_mem hI hba (n + 1)
    rw [map_sub, homogeneousComponent_eq_self hb,
      homogeneousComponent_eq_zero _ _ (Nat.lt_succ_of_le ha), sub_zero] at hm
    rw [← hbz, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have h := Submodule.finrank_sup_add_finrank_inf_eq (quotientDegreeLE I n) (piece I (n + 1))
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact (add_comm _ _).trans h.symm

private theorem component_mul_X (i : σ) (p : MvPolynomial σ k) (m : ℕ) :
    homogeneousComponent m (p * MvPolynomial.X i) =
      if 1 ≤ m then homogeneousComponent (m - 1) p * MvPolynomial.X i else 0 := by
  simpa only [← DirectSum.Decomposition.decompose'_eq, MvPolynomial.decomposition.decompose'_apply]
    using DirectSum.coe_decompose_mul_of_right_mem
      (homogeneousSubmodule σ k) m (a := p) (isHomogeneous_X k i)

private def mulPiece (I : Ideal (MvPolynomial σ k)) (i : σ) (n : ℕ) :
    piece I n →ₗ[k] piece I (n + 1) :=
  ((LinearMap.mulLeft k (Ideal.Quotient.mk I (MvPolynomial.X i))).domRestrict _).codRestrict _
    fun z => by
      obtain ⟨p, hp, hpz⟩ := mem_piece.mp z.property
      change Ideal.Quotient.mk I (MvPolynomial.X i) * z.val ∈ piece I (n + 1)
      rw [← hpz, ← map_mul, mul_comm]
      exact mem_piece.mpr ⟨_, hp.mul (isHomogeneous_X k i), rfl⟩

private theorem mulPiece_mk (I : Ideal (MvPolynomial σ k)) (i : σ) {n : ℕ}
    {p : MvPolynomial σ k} (hp : p.IsHomogeneous n) :
    (mulPiece I i n ⟨Ideal.Quotient.mk I p, mem_piece.mpr ⟨p, hp, rfl⟩⟩).val =
      Ideal.Quotient.mk I (p * MvPolynomial.X i) := by
  change Ideal.Quotient.mk I (MvPolynomial.X i) * Ideal.Quotient.mk I p = _
  rw [mul_comm, map_mul]

/-- The radical condition puts all forms of sufficiently high degree in the
ideal generated by the original ideal and the chart variable. -/
private theorem mulPiece_eventually_surjective [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (i : σ) (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (hrad : ∀ j : σ, MvPolynomial.X j ∈ (I ⊔ Ideal.span {MvPolynomial.X i}).radical) :
    ∃ N : ℕ, ∀ n ≥ N, Function.Surjective (mulPiece I i n) := by
  let J : Ideal (MvPolynomial σ k) := I ⊔ Ideal.span {MvPolynomial.X i}
  have hvars : idealOfVars σ k ≤ J.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hrad j
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hvars (idealOfVars_fg σ k)
  refine ⟨N, fun n hn z => ?_⟩
  obtain ⟨p, hp, hpz⟩ := mem_piece.mp z.property
  have hpJ : p ∈ J := hN ((mem_pow_idealOfVars_iff N p).mpr fun d hd => by
    have he : d.degree = n + 1 := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero hne)
    omega)
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hpJ
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have hc := congrArg (homogeneousComponent (n + 1)) he
  rw [map_add, component_mul_X, ite_eq_left (by omega), Nat.add_sub_cancel,
    homogeneousComponent_eq_self hp] at hc
  refine ⟨⟨_, mem_piece.mpr ⟨_, homogeneousComponent_isHomogeneous n q, rfl⟩⟩,
    Subtype.ext ?_⟩
  rw [mulPiece_mk I i (homogeneousComponent_isHomogeneous n q), ← hpz, ← hc, map_add,
    Ideal.Quotient.eq_zero_iff_mem.mpr (homogeneousComponent_mem_of_mem hI ha _), zero_add]

private theorem eventual_piece_finrank [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (hd : (affineHilbertPolynomial I).natDegree = 1) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Module.finrank k (piece I (n + 1)) : ℚ) = (affineHilbertPolynomial I).leadingCoeff := by
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial I
  refine ⟨N, fun n hn => ?_⟩
  let P := affineHilbertPolynomial I
  have hdeg : (Polynomial.backwardDifference 1 P).natDegree = 0 :=
    Nat.eq_zero_of_le_zero (by simpa [P, hd] using Polynomial.natDegree_backwardDifference_le 1 P)
  have hcoeff := Polynomial.coeff_backwardDifference_natDegree_sub_one (1 : ℚ) P
  change (Polynomial.backwardDifference 1 P).coeff (P.natDegree - 1) = _ at hcoeff
  have hP : P.natDegree = 1 := hd
  simp only [hP, Nat.sub_self, Nat.cast_one, mul_one, one_mul] at hcoeff
  have hback : Polynomial.backwardDifference 1 P = Polynomial.C P.leadingCoeff :=
    (Polynomial.eq_C_of_natDegree_eq_zero hdeg).trans (congrArg Polynomial.C hcoeff)
  have hev := congrArg (fun f : ℚ[X] => f.eval ((n + 1 : ℕ) : ℚ)) hback
  change (Polynomial.backwardDifference 1 P).eval ((n + 1 : ℕ) : ℚ) = _ at hev
  have hncast : ((n + 1 : ℕ) : ℚ) - 1 = (n : ℚ) := by simp
  rw [Polynomial.eval_backwardDifference, Polynomial.eval_C, hncast] at hev
  change (affineHilbertPolynomial I).eval ((n + 1 : ℕ) : ℚ) -
    (affineHilbertPolynomial I).eval (n : ℚ) = _ at hev
  rw [hN (n + 1) (hn.trans (Nat.le_succ n)), hN n hn] at hev
  have hs : (Module.finrank k (piece I (n + 1)) : ℚ) +
      (affineHilbertFunction I n : ℚ) = (affineHilbertFunction I (n + 1) : ℚ) := by
    exact_mod_cast piece_finrank_succ hI n
  linarith only [hs, hev]

/-- A homogeneous relation in the chart is already a cone relation in any degree
where multiplication by the chart variable is injective from then on. -/
private theorem homogeneous_chart_mem {I : Ideal (MvPolynomial σ k)} (i : σ)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {n : ℕ}
    (hcancel : ∀ m ≥ n, ∀ {q : MvPolynomial σ k}, q.IsHomogeneous m →
      q * MvPolynomial.X i ∈ I → q ∈ I)
    {p : MvPolynomial σ k} (hp : p.IsHomogeneous n) (hpJ : p ∈ chart I i) : p ∈ I := by
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hpJ
  obtain ⟨f, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  let t (m : ℕ) := homogeneousComponent m f
  have hrel (m : ℕ) : homogeneousComponent m p -
      ((if 1 ≤ m then t (m - 1) * MvPolynomial.X i else 0) - t m) ∈ I := by
    have hc := congrArg (homogeneousComponent m) he
    rw [map_add, mul_sub, mul_one, map_sub, component_mul_X] at hc
    dsimp only [t]
    rw [← hc, add_sub_cancel_right]
    exact homogeneousComponent_mem_of_mem hI ha m
  have hsucc (m : ℕ) : homogeneousComponent (m + 1) p -
      (t m * MvPolynomial.X i - t (m + 1)) ∈ I := by
    simpa only [ite_eq_left (show 1 ≤ m + 1 by omega), Nat.add_sub_cancel] using hrel (m + 1)
  have hhigh : t n ∈ I := by
    let M := max n (f.totalDegree + 1)
    refine Nat.decreasingInduction' (P := fun m => t m ∈ I) (n := M) (m := n)
      (fun m _ hm ih => ?_) (le_max_left _ _) ?_
    · have ht := hsucc m
      rw [homogeneousComponent_eq_zero _ _ (hp.totalDegree_le.trans_lt (by omega)),
        zero_sub, neg_mem_iff] at ht
      exact hcancel m hm (homogeneousComponent_isHomogeneous m f)
        ((Submodule.sub_mem_iff_left I ih).mp ht)
    · dsimp only [t]
      rw [homogeneousComponent_eq_zero _ _ (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))]
      exact I.zero_mem
  have hlow (m : ℕ) : m < n → t m ∈ I := by
    induction m with
    | zero =>
      intro hm
      have ht := hrel 0
      rw [homogeneousComponent_of_mem hp, ite_eq_right (by omega : 0 ≠ n),
        ite_eq_right (by omega : ¬ 1 ≤ 0)] at ht
      simpa only [zero_sub, neg_neg] using ht
    | succ m ih =>
      intro hm
      have ht := hsucc m
      rw [homogeneousComponent_of_mem hp, ite_eq_right (Nat.ne_of_lt hm), zero_sub, neg_mem_iff] at ht
      exact (Submodule.sub_mem_iff_right I (I.mul_mem_right _ (ih (Nat.lt_of_succ_lt hm)))).mp ht
  have ht := hrel n
  rw [homogeneousComponent_eq_self hp] at ht
  apply (Submodule.sub_mem_iff_left I ?_).mp ht
  apply I.sub_mem _ hhigh
  split_ifs with hn
  · exact I.mul_mem_right _ (hlow _ (by omega))
  · exact I.zero_mem

private theorem homogeneous_representative (I : Ideal (MvPolynomial σ k)) (i : σ)
    {n : ℕ} {p : MvPolynomial σ k} (hp : p.totalDegree ≤ n) :
    ∃ q : MvPolynomial σ k, q.IsHomogeneous n ∧
      Ideal.Quotient.mk (chart I i) q = Ideal.Quotient.mk (chart I i) p := by
  classical
  let J := chart I i
  have hi : Ideal.Quotient.mk J (MvPolynomial.X i) = 1 := by
    apply sub_eq_zero.mp
    rw [← (Ideal.Quotient.mk J).map_one, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine ⟨∑ d ∈ Finset.range (p.totalDegree + 1),
    MvPolynomial.X i ^ (n - d) * homogeneousComponent d p, IsHomogeneous.sum _ _ _ ?_, ?_⟩
  · intro d hd
    have hdn := (Nat.le_of_lt_succ (Finset.mem_range.mp hd)).trans hp
    simpa only [Nat.sub_add_cancel hdn] using
      (isHomogeneous_X_pow (R := k) i (n - d)).mul (homogeneousComponent_isHomogeneous d p)
  · change Ideal.Quotient.mk J _ = Ideal.Quotient.mk J p
    rw [map_sum]
    simp only [map_mul, map_pow, hi, one_pow, one_mul]
    rw [← map_sum, sum_homogeneousComponent]

private theorem chart_hilbertFunction [Finite σ] {I : Ideal (MvPolynomial σ k)} (i : σ)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {n : ℕ}
    (hcancel : ∀ m ≥ n, ∀ {q : MvPolynomial σ k}, q.IsHomogeneous m →
      q * MvPolynomial.X i ∈ I → q ∈ I) :
    affineHilbertFunction (chart I i) n = Module.finrank k (piece I n) := by
  let J := chart I i
  let q := Ideal.Quotient.factorₐ k (show I ≤ J from le_sup_left)
  let cut : piece I n →ₗ[k] quotientDegreeLE J n :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun z => by
      obtain ⟨p, hp, hpz⟩ := mem_piece.mp z.property
      change q z.val ∈ quotientDegreeLE J n
      rw [← hpz]
      exact mk_mem_quotientDegreeLE hp.totalDegree_le
  have hsurj : Function.Surjective cut := by
    intro z
    obtain ⟨p, hp, hpz⟩ := mem_quotientDegreeLE.mp z.property
    obtain ⟨r, hr, hrp⟩ := homogeneous_representative I i hp
    exact ⟨⟨Ideal.Quotient.mk I r, mem_piece.mpr ⟨r, hr, rfl⟩⟩, Subtype.ext (hrp.trans hpz)⟩
  have hinj : Function.Injective cut := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨p, hp, hpz⟩ := mem_piece.mp z.property
    have hm : q z.val = 0 := congrArg Subtype.val hz
    rw [← hpz] at hm
    have hpJ : p ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hm
    apply Subtype.ext
    change z.val = 0
    rw [← hpz, Ideal.Quotient.eq_zero_iff_mem]
    exact homogeneous_chart_mem i hI hcancel hp hpJ
  exact (LinearEquiv.ofBijective cut ⟨hinj, hsurj⟩).finrank_eq.symm

theorem proof : K1_13_5_5_2_1_1.c3 := by
  intro k σ _ _ I i hI hd hrad
  obtain ⟨N, hN⟩ := mulPiece_eventually_surjective i hI hrad
  obtain ⟨M, hM⟩ := eventual_piece_finrank hI hd
  have hcancel (m : ℕ) (hm : max N (M + 1) ≤ m) {p : MvPolynomial σ k}
      (hp : p.IsHomogeneous m) (hpX : p * MvPolynomial.X i ∈ I) : p ∈ I := by
    have hN' : N ≤ m := (le_max_left _ _).trans hm
    have hM' : M + 1 ≤ m := (le_max_right _ _).trans hm
    have he : m - 1 + 1 = m := by omega
    have hfin : Module.finrank k (piece I m) = Module.finrank k (piece I (m + 1)) := by
      have hh := hM (m - 1) (by omega)
      rw [he] at hh
      exact_mod_cast hh.trans (hM m (by omega)).symm
    have hi : Function.Injective (mulPiece I i m) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr (hN m hN')
    let z : piece I m := ⟨Ideal.Quotient.mk I p, mem_piece.mpr ⟨p, hp, rfl⟩⟩
    have hz : mulPiece I i m z = 0 := Subtype.ext (by
      change (mulPiece I i m z).val = 0
      rw [mulPiece_mk I i hp, Ideal.Quotient.eq_zero_iff_mem]
      exact hpX)
    have hz' : z = 0 := hi (hz.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hz')
  change affineHilbertPolynomial (chart I i) = Polynomial.C (affineHilbertPolynomial I).leadingCoeff
  symm
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := max N (M + 1))
  intro n hn
  rw [Polynomial.eval_C, chart_hilbertFunction i hI (fun m hm => hcancel m (hn.trans hm))]
  have hM' : M + 1 ≤ n := (le_max_right _ _).trans hn
  have hh := hM (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at hh
  exact hh.symm

end

end K1_13_5_5_2_1_1_3
end PackSource_K1_13_5_5_2_1_1_3Proof

section PackSource_K1_13_5_5_2_3_1Proof
set_option autoImplicit true
namespace K1_13_5_5_2_3_1

noncomputable section

open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_3 MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

private theorem monic_image {R A : Type} [CommRing R] [IsDomain R] [CommRing A]
    (ρ : R →+* A) (z : A) (p : Polynomial R) (hp : p.Monic) (hz : p.eval₂ ρ z = 0)
    (hs : Function.Surjective (Polynomial.eval₂RingHom ρ z)) :
    ρ.Finite ∧
      (letI : Module R A := Module.compHom A ρ
       Module.rank R A ≤ (p.natDegree : Cardinal)) := by
  let t := AdjoinRoot.lift ρ z hz
  have ht : t.comp (AdjoinRoot.of p) = ρ := AdjoinRoot.lift_comp_of hz
  have hts : Function.Surjective t := by
    intro a
    obtain ⟨q, hq⟩ := hs a
    exact ⟨AdjoinRoot.mk p q, (AdjoinRoot.lift_mk hz q).trans hq⟩
  constructor
  · have hfinite : (AdjoinRoot.of p).Finite :=
      RingHom.finite_algebraMap.mpr hp.finite_adjoinRoot
    rw [← ht]
    exact (RingHom.Finite.of_surjective t hts).comp hfinite
  · letI : Module R A := Module.compHom A ρ
    let u : AdjoinRoot p →ₗ[R] A :=
      { toFun := t
        map_add' := t.map_add
        map_smul' := fun r a => by
          rw [Algebra.smul_def]
          change t (AdjoinRoot.of p r * a) = ρ r * t a
          rw [map_mul]
          exact congrArg (· * t a) (DFunLike.congr_fun ht r) }
    refine (LinearMap.rank_le_of_surjective u hts).trans ?_
    rw [← (AdjoinRoot.powerBasis' hp).basis.mk_eq_rank'']
    simp

private theorem surjective_quotient {F D σ : Type} [CommRing F] [Semiring D]
    (I : Ideal (MvPolynomial σ F)) (s : D →+* (MvPolynomial σ F ⧸ I))
    (hc : ∀ c : F, ∃ t, s t = Ideal.Quotient.mk I (C c))
    (hx : ∀ i : σ, ∃ t, s t = Ideal.Quotient.mk I (MvPolynomial.X i)) : Function.Surjective s := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C c => exact hc c
  | add p q hp hq =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hq
      exact ⟨u + v, by rw [map_add, hu, hv, map_add]⟩
  | mul_X p i hp =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hx i
      exact ⟨u * v, by rw [map_mul, hu, hv, map_mul]⟩

private theorem eval₂_linear {R A : Type} [CommSemiring R] [CommSemiring A]
    (ρ : R →+* A) (z : A) (a b : R) :
    Polynomial.eval₂RingHom ρ z (Polynomial.C a + Polynomial.C b * Polynomial.X) =
      ρ a + ρ b * z := by
  change (Polynomial.C a + Polynomial.C b * Polynomial.X).eval₂ ρ z = _
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_C,
    Polynomial.eval₂_X]

private theorem choose_direction {F : Type} [Field F] [Infinite F]
    (g : MvPolynomial (Fin 3) F) (hg : 0 < g.totalDegree) :
    ∃ v : Fin 3 → F, v 0 ≠ 0 ∧ eval v (homogeneousComponent g.totalDegree g) ≠ 0 := by
  classical
  have hs : g.support.Nonempty := by
    rw [support_nonempty]
    rintro rfl
    simp at hg
  obtain ⟨d, hd, hdeg⟩ :=
    Finset.exists_mem_eq_sup g.support hs (fun d => d.degree)
  have htop : homogeneousComponent g.totalDegree g ≠ 0 := by
    intro h
    have hdeg' : d.degree = g.totalDegree := hdeg.symm
    have hcoeff : (homogeneousComponent g.totalDegree g).coeff d ≠ 0 := by
      simpa only [coeff_homogeneousComponent, ite_eq_left hdeg'] using mem_support_iff.mp hd
    exact hcoeff (by simp [h])
  -- The extra factor supplies a nonzero first coordinate for the change of variables.
  have hprod : MvPolynomial.X 0 * homogeneousComponent g.totalDegree g ≠ 0 :=
    mul_ne_zero (X_ne_zero _) htop
  have hex : ∃ v, eval v (MvPolynomial.X 0 * homogeneousComponent g.totalDegree g) ≠ 0 := by
    by_contra! h
    apply hprod
    apply MvPolynomial.funext
    intro v
    simpa only [map_zero] using h v
  obtain ⟨v, hv⟩ := hex
  rw [map_mul, eval_X] at hv
  exact ⟨v, left_ne_zero_of_mul hv, right_ne_zero_of_mul hv⟩

private def plane (v : Fin 3 → FreshField) (i : Fin 2) : FreshJetRing :=
  MvPolynomial.X i.succ - C (v i.succ * (v 0)⁻¹) * MvPolynomial.X 0

private def direction (v : Fin 3 → FreshField) : FreshJetRing :=
  C ((v 0)⁻¹) * MvPolynomial.X 0

private def offsets : Fin 3 → PairRing :=
  Fin.cons 0 MvPolynomial.X

private theorem coord (v : Fin 3 → FreshField) (hv : v 0 ≠ 0) (i : Fin 3) :
    MvPolynomial.X i = aeval (plane v) (offsets i) + C (v i) * direction v := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [offsets, Fin.cons_zero, map_zero, zero_add, direction, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hv, map_one, one_mul]
  · simp only [offsets, Fin.cons_succ, aeval_X, plane, direction, ← mul_assoc, ← map_mul]
    abel

private theorem coord_image {A : Type} [CommRing A] [Algebra FreshField A]
    (v : Fin 3 → FreshField) (hv : v 0 ≠ 0) (q : FreshJetRing →ₐ[FreshField] A)
    (i : Fin 3) :
    q (MvPolynomial.X i) =
      aeval (fun j => q (plane v j)) (offsets i) +
        algebraMap FreshField A (v i) * q (direction v) := by
  have h := congrArg q (coord v hv i)
  simpa only [map_add, map_mul, comp_aeval_apply, ← algebraMap_eq, AlgHom.commutes] using h

private theorem top_finite (g : FreshJetRing) (v : Fin 3 → FreshField) (h0 : v 0 ≠ 0)
    (hv : eval v (topForm g) ≠ 0) :
    FiniteJetPair (plane v) (Ideal.span {topForm g}) := by
  let J : Ideal FreshJetRing := Ideal.span {topForm g}
  let A := FreshJetRing ⧸ J
  let q : FreshJetRing →ₐ[FreshField] A := Ideal.Quotient.mkₐ FreshField J
  let β : PairRing →ₐ[FreshField] A := aeval fun j => q (plane v j)
  let ρ : PairRing →+* A := β.toRingHom
  let f := algebraMap FreshField PairRing
  let z := q (direction v)
  have hcomp : ρ.comp f = algebraMap FreshField A := β.comp_algebraMap
  have hcoord (i : Fin 3) : q (MvPolynomial.X i) = ρ (offsets i) + ρ (f (v i)) * z := by
    have hh := DFunLike.congr_fun hcomp (v i)
    change ρ (f (v i)) = algebraMap FreshField A (v i) at hh
    rw [hh]
    exact coord_image (A := A) v h0 q i
  let p := monicEquation f g v offsets 0
  have hp : p.Monic := (monicEquation_spec f g v offsets 0 hv).1
  have hz : p.eval₂ ρ z = 0 := by
    refine monicEquation_root f g v offsets 0 ρ z ?_
    simp only [← hcoord, hcomp, map_zero, homogeneousEval_zero]
    have heval : eval₂ (algebraMap FreshField A) (fun i => q (MvPolynomial.X i)) (topForm g) =
        q (topForm g) := by
      rw [← aeval_def]
      exact DFunLike.congr_fun (by ext i; simp : (aeval fun i => q (MvPolynomial.X i)) = q) _
    change eval₂ (algebraMap FreshField A) (fun i => q (MvPolynomial.X i)) (topForm g) = 0
    rw [heval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hsurj : Function.Surjective (Polynomial.eval₂RingHom ρ z) := by
    refine surjective_quotient (D := Polynomial PairRing) J (Polynomial.eval₂RingHom ρ z) ?_ ?_
    · intro c
      refine ⟨Polynomial.C (f c), ?_⟩
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact (DFunLike.congr_fun hcomp c).trans (q.commutes c |>.symm)
    · intro i
      refine ⟨Polynomial.C (offsets i) + Polynomial.C (f (v i)) * Polynomial.X, ?_⟩
      exact (eval₂_linear (R := PairRing) (A := A) ρ z _ _).trans (hcoord i).symm
  refine ⟨fun i => (isHomogeneous_X _ _).sub (isHomogeneous_C_mul_X _ _), ?_⟩
  have hβ : jetPairMap (plane v) J = β := by
    ext i
    exact (congrArg q (aeval_X (plane v) i)).trans
      (aeval_X (fun j => q (plane v j)) i).symm
  have heq : (jetPairMap (plane v) J).toRingHom = ρ :=
    congrArg (fun b : PairRing →ₐ[FreshField] A => b.toRingHom) hβ
  change @RingHom.Finite PairRing A _ _ (jetPairMap (plane v) J).toRingHom
  rw [heq]
  exact (monic_image (A := A) ρ z p hp hz hsurj).1

private theorem closure_rank (g : FreshJetRing) (v : Fin 3 → FreshField) (h0 : v 0 ≠ 0)
    (hv : eval v (topForm g) ≠ 0) :
    closureRank (plane v) (Ideal.span {g}) ≤ (g.totalDegree : Cardinal) := by
  let I : Ideal FreshJetRing := Ideal.span {g}
  let J := closureIdeal I
  let A := Closure I
  let q : FreshJetRing →ₐ[FreshField] A :=
    (Ideal.Quotient.mkₐ FreshField J).comp (rename some)
  let β : PairRing →ₐ[FreshField] A := aeval fun i => q (plane v i)
  let ρ : (Polynomial PairRing) →+* A := closurePairMap (plane v) I
  let f := algebraMap FreshField (Polynomial PairRing)
  let a := fun i => Polynomial.C (offsets i)
  let w : Polynomial PairRing := Polynomial.X
  let z := q (direction v)
  have hρC (r : PairRing) : ρ (Polynomial.C r) = β r :=
    Polynomial.eval₂_C _ _
  have hρw : ρ w = closureW I := Polynomial.eval₂_X _ _
  have hcomp : ρ.comp f = algebraMap FreshField A := by
    ext c
    change ρ (Polynomial.C (algebraMap FreshField PairRing c)) = _
    rw [hρC, AlgHom.commutes]
  have hcoord (i : Fin 3) : q (MvPolynomial.X i) = ρ (a i) + ρ (f (v i)) * z := by
    have hh := DFunLike.congr_fun hcomp (v i)
    change ρ (f (v i)) = algebraMap FreshField A (v i) at hh
    dsimp only [a]
    rw [hρC, hh]
    exact coord_image (A := A) v h0 q i
  have hqX (i : Fin 3) : q (MvPolynomial.X i) = Ideal.Quotient.mk J (MvPolynomial.X (some i)) := by
    change Ideal.Quotient.mk J (rename some (MvPolynomial.X i)) = _
    rw [rename_X]
  let p := monicEquation f g v a w
  obtain ⟨hp, hdeg⟩ := monicEquation_spec f g v a w hv
  have hz : p.eval₂ ρ z = 0 := by
    refine monicEquation_root f g v a w ρ z ?_
    simp only [hcomp, ← hcoord, hρw]
    letI : CommRing (FreshJetRing ⧸ I) := Ideal.Quotient.commRing I
    letI : CommRing (Polynomial (FreshJetRing ⧸ I)) := Polynomial.commRing
    let k := (closureEval I).toRingHom
    let eqn := homogeneousEval MvPolynomial.C g (fun i => MvPolynomial.X (some i))
      (MvPolynomial.X none)
    have heqn : Ideal.Quotient.mk J eqn =
        homogeneousEval (algebraMap FreshField A) g (fun i => q (MvPolynomial.X i)) (closureW I) := by
      have hx : (Ideal.Quotient.mk J ∘ fun i => MvPolynomial.X (some i)) =
          fun i => q (MvPolynomial.X i) := funext fun i => (hqX i).symm
      dsimp only [eqn]
      rw [map_homogeneousEval, hx]
      rfl
    rw [← heqn]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    -- In the affine quotient, evaluation of the homogenization multiplies g by w^deg(g).
    change k eqn = 0
    dsimp only [eqn]
    rw [map_homogeneousEval (R := MvPolynomial (Option (Fin 3)) FreshField)
      (S := Polynomial (FreshJetRing ⧸ I)) k]
    let m : FreshJetRing →+* (FreshJetRing ⧸ I) := Ideal.Quotient.mk I
    have hkcomp : k.comp MvPolynomial.C = Polynomial.C.comp (m.comp MvPolynomial.C) := by
      refine RingHom.ext fun c => ?_
      change (closureEval I) (C c) = Polynomial.C (m (C c))
      exact aeval_C _ c
    have hkx : (k ∘ fun i : Fin 3 => MvPolynomial.X (some i)) =
        fun i => Polynomial.C (m (MvPolynomial.X i)) * Polynomial.X := by
      funext i
      change (closureEval I) (MvPolynomial.X (some i)) = _
      exact aeval_X _ (some i)
    have hkw : k (MvPolynomial.X none) = Polynomial.X := aeval_X _ none
    simp only [hkcomp, hkx, hkw]
    rw [homogeneousEval_scaled (R := Polynomial (FreshJetRing ⧸ I))]
    have hm : eval₂ (Polynomial.C.comp (m.comp MvPolynomial.C))
        (fun i => Polynomial.C (m (MvPolynomial.X i))) g = Polynomial.C (m g) := by
      have he : eval₂Hom (Polynomial.C.comp (m.comp MvPolynomial.C))
          (fun i => Polynomial.C (m (MvPolynomial.X i))) = Polynomial.C.comp m := by
        apply MvPolynomial.ringHom_ext <;> simp
      exact DFunLike.congr_fun he g
    have hm0 : m g = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hm, hm0, map_zero, zero_mul]
  have hsurj : Function.Surjective (Polynomial.eval₂RingHom ρ z) := by
    refine surjective_quotient (D := Polynomial (Polynomial PairRing)) J
      (Polynomial.eval₂RingHom ρ z) ?_ ?_
    · intro c
      refine ⟨Polynomial.C (f c), ?_⟩
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact DFunLike.congr_fun hcomp c
    · intro i
      cases i with
      | none => exact ⟨Polynomial.C w, (Polynomial.eval₂_C _ _).trans hρw⟩
      | some i =>
          refine ⟨Polynomial.C (a i) + Polynomial.C (f (v i)) * Polynomial.X, ?_⟩
          rw [← hqX]
          exact (eval₂_linear (R := Polynomial PairRing) (A := A) ρ z _ _).trans (hcoord i).symm
  unfold closureRank
  rw [← hdeg]
  exact (monic_image (A := A) ρ z p hp hz hsurj).2

theorem proof : K1_13_5_5_2_3.c1 := by
  intro g hg
  letI : Infinite FreshField := Infinite.of_injective _
    (IsFractionRing.injective (Polynomial K1_13.Geom) FreshField)
  obtain ⟨v, h0, hv⟩ := choose_direction g hg
  exact ⟨plane v, top_finite g v h0 hv, closure_rank g v h0 hv⟩

end

end K1_13_5_5_2_3_1
end PackSource_K1_13_5_5_2_3_1Proof

section PackSource_K1_13_6_3_4_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_4_1

open K1_13 K1_13_6 K1_13_6_3 MvPolynomial

/-- The fresh constant extension is the scalar map in the existing
base-change theorem for the total-degree filtration. -/
theorem proof : K1_13_6_3_4.c1 := by
  intro A
  letI : Algebra Geom GeoField := geomConstants.toAlgebra
  change affineHilbertPolynomial (A.map (MvPolynomial.map (algebraMap Geom GeoField))) =
    affineHilbertPolynomial A
  exact K1_13_5_5_2.hilbertPolynomial_map (E := GeoField) A

end K1_13_6_3_4_1
end PackSource_K1_13_6_3_4_1Proof

section PackSource_K1_13_5_5_2_1_6Coordinates
set_option autoImplicit true
namespace K1_13_5_5_2_1_6

noncomputable section

open K1_13_5_5 K1_13_5_5_2_1 MvPolynomial
open scoped Polynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem sumSMulX_homogeneous {k σ : Type} [Field k] (u : σ →₀ k) :
    (sumSMulX u).IsHomogeneous 1 := by
  classical
  rw [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum]
  exact (homogeneousSubmodule σ k 1).sum_mem (fun i _ =>
    (homogeneousSubmodule σ k 1).smul_mem _ (isHomogeneous_X _ i))

private theorem sumSMulX_of_homogeneous {k σ : Type} [Field k]
    {p : MvPolynomial σ k} (hp : p.IsHomogeneous 1) :
    ∃ u : σ →₀ k, sumSMulX u = p := by
  classical
  let I := p.support
  have hx (v : σ →₀ ℕ) (h : v.degree = 1) : ∃ i : σ, Finsupp.single i 1 = v :=
    show v ∈ Set.range (fun i : σ => Finsupp.single i 1) from Finsupp.range_single_one ▸ h
  let u : σ →₀ k := ∑ v ∈ I, if h : v.degree = 1 then
      Finsupp.single ((hx v h).choose) (p.coeff v) else 0
  refine ⟨u, ?_⟩
  rw [show p = ∑ v ∈ I, monomial v (p.coeff v) from p.as_sum]
  simp only [u, map_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hd : v.degree = 1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hv)
  simp only [dite_eq_left hd, sumSMulX, Finsupp.linearCombination_single]
  rw [Algebra.smul_def, algebraMap_eq]
  change C (p.coeff v) * MvPolynomial.X _ = monomial v (p.coeff v)
  rw [C_mul_X_eq_monomial]
  exact congrArg (fun m => monomial m (p.coeff v)) (hx v hd).choose_spec

private theorem aeval_sumSMulX {k σ τ : Type} [Field k]
    (y : σ → MvPolynomial τ k) (u : σ →₀ k) :
    aeval y (sumSMulX u) = Finsupp.linearCombination k y u := by
  simp [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum]

private def linearSubstitution {k σ : Type} [Field k]
    (e : (σ →₀ k) ≃ₗ[k] (σ →₀ k)) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k := by
  let form (e : (σ →₀ k) ≃ₗ[k] (σ →₀ k)) (i : σ) := sumSMulX (e (Finsupp.single i 1))
  have hform (e : (σ →₀ k) ≃ₗ[k] (σ →₀ k)) (u : σ →₀ k) :
      aeval (form e) (sumSMulX u) = sumSMulX (e u) := by
    rw [aeval_sumSMulX]
    have hmap : Finsupp.linearCombination k (form e) = sumSMulX.comp e.toLinearMap := by
      apply (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).ext
      intro i
      simp [form, Finsupp.coe_basisSingleOne]
    rw [hmap]
    rfl
  have hcomp (e : (σ →₀ k) ≃ₗ[k] (σ →₀ k)) :
      (aeval (form e)).comp (aeval (form e.symm)) = AlgHom.id k (MvPolynomial σ k) := by
    apply algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
    change aeval (form e) (sumSMulX (e.symm (Finsupp.single i 1))) = MvPolynomial.X i
    rw [hform, LinearEquiv.apply_symm_apply]
    simp [sumSMulX]
  exact AlgEquiv.ofAlgHom (aeval (form e)) (aeval (form e.symm)) (hcomp e) (hcomp e.symm)

/-- Complete two independent linear forms by one more linear coordinate. -/
theorem exists_linearCoordinates {k : Type} [Field k] (L : Fin 2 → MvPolynomial (Fin 3) k)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hi : Function.Injective (aeval L : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 3) k)) :
    ∃ e : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k,
      (∀ i : Fin 2, e (MvPolynomial.X i.succ) = L i) ∧
      (∀ i, (e (MvPolynomial.X i)).IsHomogeneous 1) := by
  classical
  choose u hu using fun i => sumSMulX_of_homogeneous (hL i)
  have hli : LinearIndependent k u := by
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    intro a b hab
    have hh : aeval L (sumSMulX a) = aeval L (sumSMulX b) := by
      rw [aeval_sumSMulX, aeval_sumSMulX]
      have hcomp : Finsupp.linearCombination k L =
          sumSMulX.comp (Finsupp.linearCombination k u) := by
        apply (Finsupp.basisSingleOne : Module.Basis (Fin 2) k (Fin 2 →₀ k)).ext
        intro i
        simp [Finsupp.coe_basisSingleOne, hu]
      simp only [hcomp, LinearMap.comp_apply, hab]
    ext i
    simpa only [coeff_sumSMulX] using congrArg (fun p : MvPolynomial (Fin 2) k => p.coeff (Finsupp.single i 1)) (hi hh)
  let V := Fin 3 →₀ k
  let D : Module.Basis (Fin 3) k V := Finsupp.basisSingleOne
  have hdim : Module.finrank k V = 3 := by
    simpa using Module.finrank_eq_card_basis D
  have hproper : Submodule.span k (Set.range u) ≠ ⊤ := by
    intro h
    have hspan := finrank_span_eq_card hli
    rw [h, finrank_top, hdim, Fintype.card_fin] at hspan
    omega
  obtain ⟨v, hv⟩ : ∃ v : V, v ∉ Submodule.span k (Set.range u) := by
    by_contra! h
    exact hproper (eq_top_iff.mpr fun x _ => h x)
  let B := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_finCons.mpr ⟨hli, hv⟩)
    (show Fintype.card (Fin 3) = Module.finrank k V by simp [hdim])
  let e := D.equiv B (Equiv.refl _)
  refine ⟨linearSubstitution e, ?_, ?_⟩
  · intro i
    change (aeval (fun j => sumSMulX (e (Finsupp.single j 1)))) (MvPolynomial.X i.succ) = L i
    rw [aeval_X, show Finsupp.single i.succ 1 = D i.succ from rfl, Module.Basis.equiv_apply]
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank, hu]
  · intro i
    change (aeval (fun j => sumSMulX (e (Finsupp.single j 1))) (MvPolynomial.X i)).IsHomogeneous 1
    rw [aeval_X]
    exact sumSMulX_homogeneous _

theorem linearCoordinates_homogeneous {k : Type} [Field k]
    (e : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k)
    (he : ∀ i, (e (MvPolynomial.X i)).IsHomogeneous 1) {p : MvPolynomial (Fin 3) k} {n : ℕ}
    (hp : p.IsHomogeneous n) : (e p).IsHomogeneous n := by
  have h : aeval (fun i => e (MvPolynomial.X i)) = e.toAlgHom := by
    apply algHom_ext
    intro i
    simp
  rw [← show e.toAlgHom p = e p from rfl, ← h]
  simpa only [one_mul] using hp.aeval _ he

/-- Coefficient comparison with the scaling variable preserves the cone kernel. -/
theorem coneJetIdeal_component {A : Type} [CommRing A] [Algebra FreshField A]
    (d : Fin 3 → A) {p : FreshJetRing} (hp : p ∈ coneJetIdeal d) (n : ℕ) :
    homogeneousComponent n p ∈ coneJetIdeal d := by
  classical
  let c (v : Fin 3 →₀ ℕ) (r : FreshField) :=
    algebraMap FreshField A r * ∏ i ∈ v.support, d i ^ v i
  have hmono (v : Fin 3 →₀ ℕ) (r : FreshField) :
      coneJetMap d (monomial v r) = Polynomial.monomial v.degree (c v r) := by
    rw [coneJetMap, aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    simp_rw [← map_pow]
    rw [← map_prod, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul,
      Polynomial.C_mul_X_pow_eq_monomial]
    rfl
  have hparts : coneJetMap d (homogeneousComponent n p) =
      Polynomial.monomial n ((coneJetMap d p).coeff n) := by
    rw [show coneJetMap d p = ∑ v ∈ p.support, coneJetMap d (monomial v (p.coeff v)) by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]]
    rw [homogeneousComponent_apply, map_sum, Polynomial.finsetSum_coeff]
    simp only [hmono, Polynomial.coeff_monomial, ← Finset.sum_filter, map_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [(Finset.mem_filter.mp hv).2]
  change coneJetMap d p = 0 at hp
  change coneJetMap d (homogeneousComponent n p) = 0
  rw [hparts, hp, Polynomial.coeff_zero, Polynomial.monomial_zero_right]

end

end K1_13_5_5_2_1_6
end PackSource_K1_13_5_5_2_1_6Coordinates

section PackSource_K1_13_5_5_2_1_1_1Proof
set_option autoImplicit true
namespace K1_13_5_5_2_1_1_1

noncomputable section

open K1_13 K1_13_5_5 K1_13_5_5_2_1_1 K1_13_6_3_4 MvPolynomial
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

private theorem boundaryIdeal_eq {k σ : Type*} [Field k]
    {I : Ideal (MvPolynomial σ k)} (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) :
    boundaryIdeal I = I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, _, rfl⟩
    exact homogeneousComponent_mem_of_mem hI hp n
  · intro p hp
    rw [← sum_homogeneousComponent p]
    refine (boundaryIdeal I).sum_mem fun n _ => ?_
    have hn : homogeneousComponent n p ∈ I := homogeneousComponent_mem_of_mem hI hp n
    have hh := homogeneousComponent_isHomogeneous n p
    exact Ideal.subset_span ⟨_, n, hn, hh.totalDegree_le, (homogeneousComponent_eq_self hh).symm⟩

private theorem chart_degree_zero {k σ : Type*} [Field k] [Finite σ] [LinearOrder σ]
    [WellFoundedGT σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (hd : (affineHilbertPolynomial I).natDegree ≤ 1) (i : σ) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {MvPolynomial.X i - 1})).natDegree = 0 := by
  rcases Nat.eq_zero_or_pos (affineHilbertPolynomial I).natDegree with h | h
  · exact Nat.eq_zero_of_le_zero ((natDegree_affineHilbertPolynomial_le_of_le
      (le_sup_left : I ≤ I ⊔ Ideal.span {MvPolynomial.X i - 1})).trans_eq h)
  · have hone : (affineHilbertPolynomial I).natDegree = 1 := by omega
    simpa only [boundaryChart, boundaryIdeal_eq hI] using
      K1_13_5_4_4_2.boundaryChart_dimension I hone i

private theorem eval₂_scale {k L σ : Type*} [Field k] [Field L] [Fintype σ]
    (f : k →+* L) (x : σ → L) (t : L) {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) : eval₂ f (fun j => t * x j) p = t ^ n * eval₂ f x p := by
  classical
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  rw [show (∏ j : σ, (t * x j) ^ d j) = t ^ n * ∏ j : σ, x j ^ d j by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, hdeg]]
  ring

private theorem normalize_zero {k L σ : Type*} [Field k] [Field L] [Algebra k L] [Fintype σ]
    {I : Ideal (MvPolynomial σ k)} (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    {x : σ → L} (hx : x ∈ zeroLocus L I) {i : σ} (hi : x i ≠ 0) :
    (fun j => (x i)⁻¹ * x j) ∈ zeroLocus L (I ⊔ Ideal.span {MvPolynomial.X i - 1}) := by
  change I ⊔ Ideal.span {MvPolynomial.X i - 1} ≤ RingHom.ker (aeval _).toRingHom
  apply sup_le
  · intro p hp
    change eval₂ (algebraMap k L) (fun j => (x i)⁻¹ * x j) p = 0
    rw [← sum_homogeneousComponent p, eval₂_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [eval₂_scale _ x _ (homogeneousComponent_isHomogeneous n p)]
    have hz : eval₂ (algebraMap k L) x (homogeneousComponent n p) = 0 :=
      hx _ (homogeneousComponent_mem_of_mem hI hp n)
    rw [hz, mul_zero]
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    change eval₂ (algebraMap k L) (fun j => (x i)⁻¹ * x j) (MvPolynomial.X i - 1) = 0
    rw [eval₂_sub, eval₂_X, eval₂_one]
    exact sub_eq_zero.mpr (inv_mul_cancel₀ hi)

private theorem finite_chart_coordinates {k L σ : Type*} [Field k] [Field L] [Algebra k L]
    [IsAlgClosed k] [Finite σ] (J : Ideal (MvPolynomial σ k))
    (hJ : (affineHilbertPolynomial J).natDegree = 0)
    {x : σ → L} (hx : x ∈ zeroLocus L J) (j : σ) : ∃ c : k, algebraMap k L c = x j := by
  let : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
  let e : (MvPolynomial σ k ⧸ J) →ₐ[k] L := Ideal.Quotient.liftₐ J (aeval x) hx
  have h : IsIntegral k (x j) := by
    have hJX := (Algebra.IsIntegral.isIntegral (R := k) (Ideal.Quotient.mk J (MvPolynomial.X j))).map e
    change IsIntegral k (aeval x (MvPolynomial.X j)) at hJX
    simpa only [aeval_X] using hJX
  apply h.mem_range_algHom_of_minpoly_splits (K := k) _ (Algebra.ofId k L)
  simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
    IsAlgClosed.splits (minpoly k (x j))

private abbrev FreshClosure (k : Type*) [Field k] := AlgebraicClosure (FractionRing k[X])

private def freshEmbedding (k : Type*) [Field k] : k[X] →+* FreshClosure k :=
  (algebraMap (FractionRing k[X]) (FreshClosure k)).comp (algebraMap k[X] (FractionRing k[X]))

private def oldEmbedding (k : Type*) [Field k] : k →+* FreshClosure k :=
  (algebraMap (FractionRing k[X]) (FreshClosure k)).comp (algebraMap k (FractionRing k[X]))

private def genericValue (k : Type*) [Field k] (n : ℕ) :
    MvPolynomial (Fin n) (FractionRing k[X]) :=
  ∑ j : Fin n, C ((algebraMap k[X] (FractionRing k[X]) Polynomial.X) ^ j.val) * MvPolynomial.X j

private theorem eval_genericValue {k : Type*} [Field k] {n : ℕ} (a : Fin n → k) :
    aeval (oldEmbedding k ∘ a) (genericValue k n) =
      freshEmbedding k (∑ j : Fin n, Polynomial.monomial j.val (a j)) := by
  classical
  unfold genericValue
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul, aeval_C, aeval_X, Function.comp_apply, oldEmbedding, freshEmbedding,
    RingHom.comp_apply, map_pow]
  rw [← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply k k[X] (FractionRing k[X]), mul_comm]

private theorem genericValue_homogeneous (k : Type*) [Field k] (n : ℕ) :
    (genericValue k n).IsHomogeneous 1 :=
  (homogeneousSubmodule (Fin n) (FractionRing k[X]) 1).sum_mem fun j _ =>
    isHomogeneous_C_mul_X _ j

private theorem generic_no_zero {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    (hd : (affineHilbertPolynomial I).natDegree ≤ 1) (i : Fin n) :
    MvPolynomial.X i ∈
      (I.map (MvPolynomial.map (algebraMap k (FractionRing k[X]))) ⊔
        Ideal.span {genericValue k n}).radical := by
  classical
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := FreshClosure k)]
  apply mem_vanishingIdeal_iff.mpr
  intro x hx
  rw [aeval_X]
  by_contra hi
  let : Algebra k (FreshClosure k) := (oldEmbedding k).toAlgebra
  have hxI : x ∈ zeroLocus (FreshClosure k) I := by
    intro p hp
    have h := hx _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem
      (MvPolynomial.map (algebraMap k (FractionRing k[X]))) hp))
    rw [aeval_def, eval₂_map] at h
    exact h
  have hb := normalize_zero hI hxI hi
  choose a ha using fun j => finite_chart_coordinates _ (chart_degree_zero I hI hd i) hb j
  have he : oldEmbedding k ∘ a = fun j => (x i)⁻¹ * x j := funext ha
  have hai : a i ≠ 0 := by
    intro h
    have h' := ha i
    change oldEmbedding k (a i) = (x i)⁻¹ * x i at h'
    rw [h, map_zero, inv_mul_cancel₀ hi] at h'
    exact zero_ne_one h'
  have hv := hx (genericValue k n) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hv' : aeval (oldEmbedding k ∘ a) (genericValue k n) = 0 := by
    rw [he, aeval_def, eval₂_scale _ x _ (genericValue_homogeneous k n), ← aeval_def, hv, mul_zero]
  rw [eval_genericValue] at hv'
  have hinj : Function.Injective (freshEmbedding k) :=
    (algebraMap (FractionRing k[X]) (FreshClosure k)).injective.comp (IsFractionRing.injective _ _)
  have hp := hinj (hv'.trans (freshEmbedding k).map_zero.symm)
  have hc := congrArg (fun p : k[X] => p.coeff i.val) hp
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i] at hc
  · exact hai (by simpa only [Polynomial.coeff_monomial_same, Polynomial.coeff_zero] using hc)
  · intro j _ hj
    exact Polynomial.coeff_monomial_of_ne _ (fun h => hj (Fin.val_injective h.symm))
  · simp

/-- On a fixed cone of dimension at most one the independent value vanishes only at the origin. -/
theorem proof : K1_13_5_5_2_1_1.c1 := by
  intro I hI hd i
  simpa only [valueIdeal, freshIdeal, freshValue, jetForm, genericValue, freshCenter,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] using
    generic_no_zero I hI hd i

end

end K1_13_5_5_2_1_1_1
end PackSource_K1_13_5_5_2_1_1_1Proof

section PackSource_K1_13_6_3_5_3_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000

namespace K1_13_6_3_5_3_1

noncomputable section

open MvPolynomial K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5_3
open scoped Polynomial nonZeroDivisors

private theorem chart_baseChange {k E σ : Type} [Field k] [Field E] [Algebra k E]
    (R : Ideal (MvPolynomial σ k)) [R.IsPrime] [(scalarExtension (E := E) R).IsPrime]
    {a : σ} {z : E} (hz : Transcendental k z) (ha : MvPolynomial.X a ∉ R) :
    let H := scalarExtension (E := E) R
    ∃ inc : chartField R a →+* chartField H a,
      MvPolynomial.X a ∉ H ∧
      inc.comp (algebraMap k (chartField R a)) =
        (algebraMap E (chartField H a)).comp (algebraMap k E) ∧
      (∀ i, inc (chartPoint R a i) = chartPoint H a i) ∧
      Function.Injective (Polynomial.eval₂RingHom inc (algebraMap E (chartField H a) z)) := by
  let H := scalarExtension (E := E) R
  let j : ConeFrac R →+* ConeFrac H := IsFractionRing.map (coneRingInclude_injective R hz)
  have hjmk (p : MvPolynomial σ k) :
      j (algebraMap (ConeRing R) (ConeFrac R) (Ideal.Quotient.mk R p)) =
        algebraMap (ConeRing H) (ConeFrac H)
          (Ideal.Quotient.mk H (MvPolynomial.map (algebraMap k E) p)) :=
    IsLocalization.map_eq (M := (ConeRing R)⁰) (T := (ConeRing H)⁰) _ _
  have hj (i : σ) : j (conePoint R i) = conePoint H i := by
    simpa only [conePoint, MvPolynomial.map_X] using hjmk (MvPolynomial.X i)
  have ha' : MvPolynomial.X a ∉ H := by
    intro h
    have hzero : conePoint H a = 0 := by
      simp [conePoint, Ideal.Quotient.eq_zero_iff_mem.mpr h]
    exact conePoint_ne_zero ha (j.injective (by rw [hj, hzero, map_zero]))
  have hj' (i : σ) :
      j ((chartPoint R a i : chartField R a) : ConeFrac R) =
        (chartPoint H a i : ConeFrac H) := by rw [chartPoint_coe, chartPoint_coe, map_div₀, hj, hj]
  let Fresh := chartField H a
  let Old := chartField R a
  let jk : Old →ₐ[k] ConeFrac H :=
    { toRingHom := j.comp (chartField R a).val.toRingHom
      commutes' := by
        intro x
        change j (algebraMap k (ConeFrac R) x) = _
        change j (algebraMap (ConeRing R) (ConeFrac R) (Ideal.Quotient.mk _ (MvPolynomial.C x))) = _
        rw [hjmk, MvPolynomial.map_C]
        rfl }
  let L : IntermediateField k (ConeFrac H) := (chartField H a).restrictScalars k
  have hle : (⊤ : IntermediateField k Old) ≤ L.comap jk := by
    rw [← chart_generates R a]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    change jk (chartPoint R a i) ∈ L
    rw [show jk (chartPoint R a i) = (chartPoint H a i : ConeFrac H) from hj' i]
    exact (chartPoint H a i).property
  let inc : Old →+* Fresh := jk.toRingHom.codRestrict Fresh.toSubfield
    (fun x => hle (show x ∈ (⊤ : IntermediateField k Old) from trivial))
  have hinc (i : σ) : inc (chartPoint R a i) = chartPoint H a i :=
    Subtype.ext (hj' i)
  have hind : Function.Injective
      (Polynomial.eval₂RingHom inc (algebraMap E Fresh z)) := by
    have he : (chartField H a).val.toRingHom.comp
        (Polynomial.eval₂RingHom inc (algebraMap E Fresh z)) =
        (Polynomial.eval₂RingHom j (algebraMap E (ConeFrac H) z)).comp
          (Polynomial.mapRingHom (chartField R a).val.toRingHom) := by
      apply Polynomial.ringHom_ext
      · intro x
        simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          Polynomial.coe_mapRingHom, Polynomial.map_C]
        rfl
      · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
          Polynomial.coe_mapRingHom, Polynomial.map_X]
        rfl
    apply Function.Injective.of_comp (f := fun z : Fresh => (z : ConeFrac H))
    change Function.Injective ((chartField H a).val.toRingHom.comp
      (Polynomial.eval₂RingHom inc (algebraMap E Fresh z)))
    rw [he]
    exact (coneFrac_eval_injective R hz).comp
      (Polynomial.map_injective _ (chartField R a).val.injective)
  refine ⟨inc, ha', ?_, hinc, hind⟩
  apply RingHom.ext
  intro x
  exact Subtype.ext (jk.commutes x)

private theorem genericCoeffs_injective : Function.Injective K1_13_6.genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp
    (IsFractionRing.injective Geom[X] GenericField)

private theorem freshArgument_transcendental [Algebra Geom GeoField]
    (hc : algebraMap Geom GeoField = geomConstants) :
    Transcendental Geom genericArgument := by
  apply transcendental_iff_injective.mpr
  have h : (Polynomial.aeval genericArgument : Geom[X] →ₐ[Geom] GeoField).toRingHom =
      K1_13_6.genericCoeffs := by
    apply Polynomial.ringHom_ext
    · intro c
      change (Polynomial.aeval genericArgument : Geom[X] →ₐ[Geom] GeoField)
          (Polynomial.C c) = geomConstants c
      rw [Polynomial.aeval_C]
      exact RingHom.congr_fun hc c
    · change (Polynomial.aeval genericArgument : Geom[X] →ₐ[Geom] GeoField)
          Polynomial.X = genericArgument
      exact Polynomial.aeval_X _
  change Function.Injective (Polynomial.aeval genericArgument :
    Geom[X] →ₐ[Geom] GeoField).toRingHom
  rw [h]
  exact genericCoeffs_injective

private theorem monic_of_coefficients {n : ℕ} {L : Type} [Field L] [DecidableEq L]
    (u : Fin n → L) (a : Fin n) (ha : u a = 1)
    (hz : ∀ i, a < i → u i = 0) :
    (Polynomial.ofFn n u).Monic ∧ (Polynomial.ofFn n u).natDegree < n := by
  have hcoeff := Polynomial.ofFn_coeff_eq_val_of_lt u a.isLt
  have hle : (Polynomial.ofFn n u).natDegree ≤ a.val := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    by_cases h : m < n
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt u h]
      exact hz ⟨m, h⟩ hm
    · exact Polynomial.ofFn_coeff_eq_zero_of_ge u (by omega)
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one a.val hle (hcoeff.trans ha),
    hle.trans_lt a.isLt⟩

private theorem coefficientTuple_ofFn {n : ℕ} {F L : Type}
    [Field F] [Field L] [DecidableEq F] (j : F →+* L) (u : Fin n → F) :
    coefficientTuple (N := n) j (Polynomial.ofFn n u) = j ∘ u := by
  funext i
  exact congrArg j (Polynomial.ofFn_coeff_eq_val_of_lt u i.isLt)

set_option backward.isDefEq.respectTransparency false in
theorem proof : K1_13_6_3_5_3.c1 := by
  classical
  intro R hR hprime hhom hdim
  let : R.IsPrime := hR
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  let : (scalarExtension (E := GeoField) R).IsPrime := hprime
  have hz := freshArgument_transcendental rfl
  obtain ⟨a, ha, hlast⟩ := exists_anchor R hdim
  obtain ⟨inc, ha', hconstants, hinc, hind⟩ := chart_baseChange (E := GeoField) R hz ha
  let H := scalarExtension (E := GeoField) R
  let Old := chartField R a
  let Fresh := chartField H a
  let f : Old[X] := Polynomial.ofFn taylorLength (chartPoint R a)
  have hf := monic_of_coefficients (chartPoint R a) a (chartPoint_anchor ha) (by
    intro i hi
    apply Subtype.ext
    change conePoint R i / conePoint R a = 0
    simp [conePoint, Ideal.Quotient.eq_zero_iff_mem.mpr (hlast i hi)])
  have htuple : coefficientTuple (N := taylorLength) inc f = chartPoint H a :=
    (coefficientTuple_ofFn inc (chartPoint R a)).trans (funext hinc)
  have hhom' := homogeneous_map (algebraMap Geom GeoField) hhom
  have hd' : dimension H = 2 := by
    change (MvPolynomial.affineHilbertPolynomial (R.map (MvPolynomial.map
      (algebraMap Geom GeoField)))).natDegree = _
    rw [K1_13_5_5_2.hilbertPolynomial_map]
    exact hdim
  obtain ⟨hold, _⟩ := chart_curve R a hhom ha hdim
  obtain ⟨hfresh, hnonconstant⟩ := chart_curve H a hhom' ha' hd'
  have heq : H = coneIdeal GeoField (coefficientTuple (N := taylorLength) inc f) :=
    (coneIdeal_chart hhom' ha').symm.trans (congrArg (coneIdeal GeoField) htuple).symm
  have hgen : IntermediateField.adjoin GeoField
      (Set.range (coefficientTuple (N := taylorLength) inc f)) = ⊤ := by
    rw [htuple]
    exact chart_generates H a
  have hnon : ∃ i : Fin taylorLength, Transcendental GeoField (coefficientTuple inc f i) :=
    htuple.symm ▸ hnonconstant
  exact ⟨{
    Old := Old
    Fresh := Fresh
    oldCurve := hold
    freshCurve := hfresh
    includeOld := inc
    constants := hconstants
    independent := hind
    polynomial := f
    monic := hf.1
    degree_le := Nat.lt_succ_iff.mp hf.2
    equation := heq
    generates := hgen
    nonconstant := hnon }⟩

end

end K1_13_6_3_5_3_1
end PackSource_K1_13_6_3_5_3_1Proof

section PackSource_K1_13_5_5_2_1_6Fiber
set_option autoImplicit true
namespace K1_13_5_5_2_1_6

noncomputable section

open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1 MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors

set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

abbrev JetQuot {A : Type} [CommRing A] [Algebra FreshField A] (d : Fin 3 → A) :=
  FreshJetRing ⧸ coneJetIdeal d

abbrev jetInclusion {A : Type} [CommRing A] [Algebra FreshField A] (d : Fin 3 → A) :
    JetQuot d →ₐ[FreshField] A[X] :=
  Ideal.kerLiftAlg (coneJetMap d)

theorem jetInclusion_injective {A : Type} [CommRing A] [Algebra FreshField A]
    (d : Fin 3 → A) : Function.Injective (jetInclusion d) :=
  Ideal.kerLiftAlg_injective _

theorem conePairMap_eq_comp {A : Type} [CommRing A] [Algebra FreshField A]
    (d : Fin 3 → A) (L : Fin 2 → FreshJetRing) :
    conePairMap d L = (jetInclusion d).comp (jetPairMap L (coneJetIdeal d)) :=
  rfl

private theorem finite_pair_injective {k : Type} [Field k]
    {J : Ideal (MvPolynomial (Fin 3) k)}
    (g g' : MvPolynomial (Fin 2) k →ₐ[k] (MvPolynomial (Fin 3) k ⧸ J))
    (hg : g.Finite) (hg' : g'.Finite) (hi : Function.Injective g') :
    Function.Injective g := by
  let I : Ideal (MvPolynomial (Fin 2) k) := RingHom.ker g
  have hdim : (affineHilbertPolynomial J).natDegree = 2 := by
    simpa using natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g' hg' hi
  let q := Ideal.Quotient.mkₐ k I
  let j := Ideal.kerLiftAlg g
  have hj : j.comp q = g := rfl
  have hfin : j.Finite := AlgHom.Finite.of_comp_finite (f := q) (by rwa [hj])
  have hdim' := natDegree_affineHilbertPolynomial_eq_of_finite_of_injective j hfin
    (Ideal.kerLiftAlg_injective g)
  by_contra hn
  have hnb : I ≠ ⊥ := fun hb => hn ((RingHom.injective_iff_ker_eq_bot g.toRingHom).mpr hb)
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
  have hsmall := natDegree_affineHilbertPolynomial_le_of_mem hp0 hp
  change (affineHilbertPolynomial J).natDegree = (affineHilbertPolynomial I).natDegree at hdim'
  rw [← hdim', hdim] at hsmall
  simp at hsmall

/-- A finite map to a two-dimensional jet image is injective on the pair ring. -/
theorem jetPairMap_injective {J : Ideal FreshJetRing} {L M : Fin 2 → FreshJetRing}
    (hL : FiniteJetPair L J) (hM : FiniteJetPair M J)
    (hi : Function.Injective (jetPairMap M J)) :
    Function.Injective (jetPairMap L J) :=
  finite_pair_injective (jetPairMap L J) (jetPairMap M J) hL.2 hM.2 hi

/-- Generic tensor fibers compute the ring module finrank even before establishing finiteness. -/
theorem pairRank_eq_finrank {B : Type} [CommRing B] [Algebra FreshField B]
    (φ : PairRing →ₐ[FreshField] B) :
    letI : Algebra PairRing B := φ.toRingHom.toAlgebra
    pairRank φ = Module.finrank PairRing B := by
  letI : Algebra PairRing B := φ.toRingHom.toAlgebra
  let f := TensorProduct.mk PairRing PairField B 1
  exact (IsFractionRing.finrank_right_eq PairRing PairField (pairFiber φ)).trans
    (IsLocalizedModule.finrank_eq (nonZeroDivisors PairRing) f le_rfl)

theorem pairFiber_nontrivial {B : Type} [CommRing B] [IsDomain B] [Algebra FreshField B]
    (φ : PairRing →ₐ[FreshField] B) (hi : Function.Injective φ) :
    Nontrivial (pairFiber φ) := by
  letI : Algebra PairRing B := φ.toRingHom.toAlgebra
  let f := TensorProduct.mk PairRing PairField B 1
  refine (show Function.Injective f from ?_).nontrivial
  apply (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors PairRing) f).2
  intro c x y h
  change φ c * x = φ c * y at h
  have hc : φ c ≠ φ 0 := hi.ne (mem_nonZeroDivisors_iff_ne_zero.mp c.property)
  rw [map_zero] at hc
  exact mul_left_cancel₀ hc h

/-- The module rank for the scalar action specified by a ring homomorphism. -/
def mapFinrank {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) : ℕ :=
  @Module.finrank R S _ _ g.toAlgebra.toModule

private theorem mapFinrank_comp {R S T : Type}
    [CommRing R] [CommRing S] [CommRing T] [IsDomain T]
    (g : R →+* S) (f : S →+* T) (hf : Function.Injective f) :
    mapFinrank (f.comp g) = mapFinrank g * mapFinrank f := by
  letI : Algebra R S := g.toAlgebra
  letI : Algebra S T := f.toAlgebra
  letI : Algebra R T := (f.comp g).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).mpr hf
  exact (Module.finrank_mul_finrank' (R := R) (S := S) T).symm

theorem pairRank_comp {B C : Type}
    [CommRing B] [CommRing C] [IsDomain C] [Algebra FreshField B] [Algebra FreshField C]
    (g : PairRing →ₐ[FreshField] B) (f : B →ₐ[FreshField] C) (hf : Function.Injective f) :
    pairRank (f.comp g) = mapFinrank g.toRingHom * mapFinrank f.toRingHom := by
  exact (pairRank_eq_finrank (f.comp g)).trans
    (mapFinrank_comp g.toRingHom f.toRingHom hf)

end

end K1_13_5_5_2_1_6
end PackSource_K1_13_5_5_2_1_6Fiber

section PackSource_K1_13_5_5_2_3_3Proof
set_option autoImplicit true
namespace K1_13_5_5_2_3_3

noncomputable section

open K1_13_5_5 K1_13_5_5_2_3 MvPolynomial
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private def affineMap (P : Ideal CoeffRing) (g d : FreshJetRing) (h : FreshChart P g d) :
    (FreshJetRing ⧸ Ideal.span {g}) →ₐ[FreshField] (FreshCoeffRing ⧸ freshIdeal P) :=
  Ideal.quotientMapₐ _ freshProjection h.image.ge

private def liftProjection :
    MvPolynomial (Option (Fin 3)) FreshField →ₐ[FreshField]
      MvPolynomial (Option CoeffIndex) FreshField :=
  aeval fun
    | none => MvPolynomial.X none
    | some i => rename some (freshProjection (MvPolynomial.X i))

private theorem liftProjection_rename (f : FreshJetRing) :
    liftProjection (rename some f) = rename some (freshProjection f) := by
  have he : liftProjection.comp (rename some) = (rename some).comp freshProjection := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [liftProjection]
  exact DFunLike.congr_fun he f

private theorem scaled_linear_form {K σ : Type} [Field K] [Fintype σ]
    (J : Ideal (MvPolynomial σ K)) (c : σ → K) :
    closureEval J (rename some (∑ a, C (c a) * MvPolynomial.X a)) =
      Polynomial.C (Ideal.Quotient.mk J (∑ a, C (c a) * MvPolynomial.X a)) * Polynomial.X := by
  simp only [map_sum, map_mul, rename_C, rename_X, closureEval, aeval_X, aeval_C,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc]
  rfl

private theorem scaled_jet (J : Ideal FreshCoeffRing) (i : Fin 3) :
    closureEval J (rename some (freshProjection (MvPolynomial.X i))) =
      Polynomial.C (Ideal.Quotient.mk J (freshProjection (MvPolynomial.X i))) * Polynomial.X := by
  simp only [freshProjection, aeval_X, jetForm]
  exact scaled_linear_form J _

private theorem projection_commutes (P : Ideal CoeffRing) (g d : FreshJetRing)
    (h : FreshChart P g d) :
    (closureEval (freshIdeal P)).comp liftProjection =
      (Polynomial.mapAlgHom (affineMap P g d h)).comp (closureEval (Ideal.span {g})) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | none =>
    simp [liftProjection, closureEval]
  | some i =>
    simpa [liftProjection, closureEval, affineMap] using scaled_jet (freshIdeal P) i

private theorem closure_project_le (P : Ideal CoeffRing) (g d : FreshJetRing)
    (h : FreshChart P g d) :
    closureIdeal (Ideal.span {g}) ≤ (closureIdeal (freshIdeal P)).comap liftProjection := by
  intro f hf
  change closureEval (freshIdeal P) (liftProjection f) = 0
  have h0 : closureEval (Ideal.span {g}) f = 0 := hf
  have hc := DFunLike.congr_fun (projection_commutes P g d h) f
  change closureEval (freshIdeal P) (liftProjection f) =
    Polynomial.mapAlgHom (affineMap P g d h) (closureEval (Ideal.span {g}) f) at hc
  rw [hc, h0, map_zero]

private def chartMap (P : Ideal CoeffRing) (g d : FreshJetRing) (h : FreshChart P g d) :
    Closure (Ideal.span {g}) →ₐ[FreshField] Closure (freshIdeal P) :=
  Ideal.quotientMapₐ _ liftProjection (closure_project_le P g d h)

/-- Evaluate a closure class in the affine coordinate ring with a polynomial homogenizer. -/
private def closureEmbed {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) :
    Closure I →ₐ[K] Polynomial (MvPolynomial σ K ⧸ I) :=
  Ideal.kerLiftAlg (closureEval I)

private theorem closureEmbed_injective {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) :
    Function.Injective (closureEmbed I) :=
  Ideal.kerLiftAlg_injective _

private theorem embed_W {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) :
    closureEmbed I (closureW I) = Polynomial.monomial 1 1 := by
  change closureEval I (MvPolynomial.X none) = _
  simp only [closureEval, aeval_X, Polynomial.monomial_one_one_eq_X]

private theorem embed_var {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) (i : σ) :
    closureEmbed I (Ideal.Quotient.mk (closureIdeal I) (MvPolynomial.X (some i))) =
      Polynomial.monomial 1 (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
  change closureEval I (MvPolynomial.X (some i)) = _
  simp only [closureEval, aeval_X, Polynomial.C_mul_X_eq_monomial]

private theorem embed_chartMap (P : Ideal CoeffRing) (g d : FreshJetRing)
    (h : FreshChart P g d) (q : Closure (Ideal.span {g})) :
    closureEmbed (freshIdeal P) (chartMap P g d h q) =
      Polynomial.mapAlgHom (affineMap P g d h) (closureEmbed (Ideal.span {g}) q) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact DFunLike.congr_fun (projection_commutes P g d h) f

/-- An affine polynomial has a homogeneous lift after scaling by some power of w.
The degree can be padded to a common degree when taking a sum. -/
private theorem exists_homogeneous_lift {K σ : Type} [Field K]
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    ∃ (q : Closure I) (n : ℕ),
      closureEmbed I q = Polynomial.monomial n (Ideal.Quotient.mk I f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    refine ⟨algebraMap K (Closure I) c, 0, ?_⟩
    rw [AlgHom.commutes, Polynomial.monomial_zero_left, Polynomial.algebraMap_apply]
    rfl
  | add f v hf hv =>
    obtain ⟨p, m, hp⟩ := hf
    obtain ⟨q, n, hq⟩ := hv
    refine ⟨closureW I ^ n * p + closureW I ^ m * q, m + n, ?_⟩
    simp only [map_add, map_mul, map_pow, embed_W, hp, hq, Polynomial.monomial_pow,
      Polynomial.monomial_mul_monomial, one_mul, one_pow]
    rw [Nat.add_comm n m, ← map_add]
  | mul_X f i hf =>
    obtain ⟨p, m, hp⟩ := hf
    refine ⟨p * Ideal.Quotient.mk (closureIdeal I) (MvPolynomial.X (some i)), m + 1, ?_⟩
    simp only [map_mul, hp, embed_var, Polynomial.monomial_mul_monomial]

/-- Recovery with powers of a shared denominator extends from coordinates to the quotient. -/
private theorem recover_of_variables {K σ : Type} [Field K] {A : Type} [CommRing A]
    [Algebra K A] (J : Ideal (MvPolynomial σ K)) (s : A →ₐ[K] Closure J) (b : A)
    (hvars : ∀ i : Option σ, ∃ q : A, ∃ m : ℕ,
      s q = s b ^ m * Ideal.Quotient.mk (closureIdeal J) (MvPolynomial.X i)) :
    ∀ a : Closure J, ∃ q : A, ∃ m : ℕ, s q = s b ^ m * a := by
  intro a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction f using MvPolynomial.induction_on with
  | C c =>
    refine ⟨algebraMap K A c, 0, ?_⟩
    rw [AlgHom.commutes, pow_zero, one_mul]
    rfl
  | add f v hf hv =>
    obtain ⟨p, m, hp⟩ := hf
    obtain ⟨q, n, hq⟩ := hv
    refine ⟨b ^ n * p + b ^ m * q, m + n, ?_⟩
    simp only [map_add, map_mul, map_pow, hp, hq, pow_add]
    ring
  | mul_X f i hf =>
    obtain ⟨p, m, hp⟩ := hf
    obtain ⟨q, n, hq⟩ := hvars i
    refine ⟨p * q, m + n, ?_⟩
    simp only [map_mul, hp, hq, pow_add]
    ring

theorem proof : K1_13_5_5_2_3.c3 := by
  intro P g d h
  let I : Ideal FreshJetRing := Ideal.span {g}
  let J := freshIdeal P
  let s : Closure I →ₐ[FreshField] Closure J := chartMap P g d h
  have hW : s (closureW I) = closureW J := by
    change Ideal.Quotient.mk (closureIdeal J) (liftProjection (MvPolynomial.X none)) = _
    simp [liftProjection, closureW]
  refine ⟨s, hW, ?_, ?_⟩
  · intro f
    change Ideal.Quotient.mk (closureIdeal J) (liftProjection (rename some f)) = _
    exact congrArg (Ideal.Quotient.mk (closureIdeal J)) (liftProjection_rename f)
  obtain ⟨D, r, hDr⟩ := exists_homogeneous_lift I d
  let b := closureW I * D
  let δ := Ideal.Quotient.mk J (freshProjection d)
  have hδ : δ ≠ 0 := by
    rw [show δ = Ideal.Quotient.mk J (freshProjection d) from rfl, ne_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    intro hd
    apply h.regular_open
    rw [← h.image]
    exact hd
  have transfer (q : Closure I) (v : FreshJetRing) (n : ℕ)
      (hq : closureEmbed I q = Polynomial.monomial n (Ideal.Quotient.mk I v)) :
      closureEmbed J (s q) = Polynomial.monomial n (Ideal.Quotient.mk J (freshProjection v)) := by
    change closureEmbed J (chartMap P g d h q) = _
    rw [embed_chartMap, hq, Polynomial.mapAlgHom_monomial]
    rfl
  have hD : closureEmbed J (s D) = Polynomial.monomial r δ := transfer D d r hDr
  have hw : closureEmbed J (s (closureW I)) = Polynomial.monomial 1 1 := by
    rw [hW]
    exact embed_W J
  have hb : s b ≠ 0 := by
    intro hzero
    have hz := congrArg (closureEmbed J) hzero
    simp only [b, map_mul, hw, hD, Polynomial.monomial_mul_monomial, one_mul, map_zero] at hz
    exact hδ ((Polynomial.monomial_eq_zero_iff δ (1 + r)).mp hz)
  refine ⟨b, hb, recover_of_variables J s b ?_⟩
  intro i
  cases i with
  | none =>
    refine ⟨closureW I, 0, ?_⟩
    change s (closureW I) = s b ^ 0 * closureW J
    simpa only [pow_zero, one_mul] using hW
  | some i =>
    obtain ⟨v, m, hv⟩ := h.recover i
    obtain ⟨V, n, hVn⟩ := exists_homogeneous_lift I v
    have ha : Ideal.Quotient.mk J (freshProjection v) =
        δ ^ m * Ideal.Quotient.mk J (MvPolynomial.X i) := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hv
      simp only [map_sub, map_mul, map_pow, sub_eq_zero] at hz
      exact hz.symm
    have hV := (transfer V v n hVn).trans (congrArg (Polynomial.monomial n) ha)
    -- The extra n factors of b clear the homogenizing power used to lift v.
    refine ⟨closureW I ^ (m * (r + 1) + 1) * D ^ n * V, m + n, ?_⟩
    apply closureEmbed_injective J
    simp only [b, map_mul, map_pow, hw, hD, hV, embed_var,
      Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, one_mul, one_pow]
    apply congrArg₂ (fun k c => (Polynomial.monomial k c : Polynomial (FreshCoeffRing ⧸ J)))
    · ring
    · ring

end

end K1_13_5_5_2_3_3
end PackSource_K1_13_5_5_2_3_3Proof

section PackSource_K1_13_5_5_2_1_5Proof
set_option autoImplicit true
namespace K1_13_5_5_2_1_5

noncomputable section

open MvPolynomial K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open scoped Polynomial

set_option maxHeartbeats 1000000

private theorem mapped_eval {F B σ : Type} [Field F] [CommRing B] [Algebra F B]
    (x : σ → F) (p : MvPolynomial σ F) :
    aeval (fun i => algebraMap F B (x i)) p = algebraMap F B (eval x p) := by
  exact (comp_aeval_apply x (Algebra.ofId F B) p).symm

private theorem slope_unit {F A : Type} [Field F] [CommRing A] [Algebra F A]
    (d : Fin 3 → A) (hd : Ideal.span (Set.range d) = ⊤)
    (t : F) {p : MvPolynomial (Fin 3) F} {n : ℕ}
    (hp : p.IsHomogeneous n) (hrel : aeval d p = 0) (ht : eval ![0, t, 1] p ≠ 0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {d 0}) (d 1 - algebraMap F A t * d 2)) := by
  let D := A ⧸ Ideal.span {d 0}
  let ρ : A →ₐ[F] D := Ideal.Quotient.mkₐ F _
  let w : A := d 1 - algebraMap F A t * d 2
  change IsUnit (ρ w)
  by_contra hn
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal (Ideal.span {ρ w})
    (fun h => hn (Ideal.span_singleton_eq_top.mp h))
  let _ : N.IsMaximal := hN
  let E := D ⧸ N
  let π : A →ₐ[F] E := (Ideal.Quotient.mkₐ F N).comp ρ
  have h0 : π (d 0) = 0 := by
    have hρ : ρ (d 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp [π, hρ]
  have hw : π w = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_span_singleton_self _))
  have h1 : π (d 1) = algebraMap F E t * π (d 2) := by
    simpa [w, map_sub, map_mul, sub_eq_zero] using hw
  have hx : (fun i => π (d i)) =
      fun i => π (d 2) * algebraMap F E ((![0, t, 1] : Fin 3 → F) i) := by
    funext i
    fin_cases i <;> simp [h0, h1, mul_comm]
  have h := congrArg π hrel
  rw [comp_aeval_apply, map_zero, hx, homogeneous_aeval_mul hp, mapped_eval] at h
  have h2 : π (d 2) = 0 := by
    by_contra h2
    exact (mul_ne_zero (pow_ne_zero _ h2) ((map_ne_zero (algebraMap F E)).2 ht)) h
  have hle' : Ideal.span (Set.range d) ≤ RingHom.ker π.toRingHom :=
    Ideal.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      change π (d i) = 0
      fin_cases i <;> simp [h0, h1, h2])
  have hbad : π 1 = 0 := hle' (by rw [hd]; trivial)
  simp at hbad

private theorem eval_on_axis_ne_zero {F : Type} [Field F] [Infinite F]
    {p : MvPolynomial (Fin 2) F} {n : ℕ}
    (hp : p.IsHomogeneous n) (hrest : (finSuccEquiv F 1 p).coeff 0 ≠ 0) :
    eval ![0, 1] p ≠ 0 := by
  intro hzero
  apply hrest
  apply MvPolynomial.funext
  intro x
  have hvx : (fun i => x 0 * ((![0, 1] : Fin 2 → F) i)) = Fin.cons 0 x := by
    funext i
    fin_cases i
    · simp
    · change x 0 * 1 = Fin.cons (α := fun _ => F) 0 x (0 : Fin 1).succ
      rw [Fin.cons_succ, mul_one]
  have he := homogeneous_aeval_mul hp (![0, 1] : Fin 2 → F) (x 0)
  rw [hvx, aeval_eq_eval, aeval_eq_eval, hzero, mul_zero,
    eval_eq_eval_mv_eval', ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at he
  simpa using he

/-- The fixed coordinate and a unit on its zero slice admit no homogeneous relation. -/
private theorem pin_injective {F A : Type} [Field F] [Infinite F] [CommRing A] [IsDomain A]
    [Algebra F A] (v w : A) (hv : v ≠ 0) (hvu : ¬ IsUnit v)
    (hw : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) w)) :
    Function.Injective (polynomialPairMap F v w) := by
  classical
  by_contra h
  have heq : scaled (F := F) (![v, w] : Fin 2 → A) = polynomialPairMap F v w := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [scaled, polynomialPairMap]
  have h' : ¬ Function.Injective (scaled (F := F) (![v, w] : Fin 2 → A)) := by
    rwa [heq]
  obtain ⟨p, n, hp, hrel, hrest⟩ :=
    relation_on_value_plane (F := F) (m := 1) (![v, w] : Fin 2 → A) hv h'
  let D := A ⧸ Ideal.span {v}
  let _ : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr
    (fun h => hvu (Ideal.span_singleton_eq_top.mp h))
  let ρ : A →ₐ[F] D := Ideal.Quotient.mkₐ F _
  have hv' : ρ v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hmap : (fun i => ρ ((![v, w] : Fin 2 → A) i)) =
      fun i => ρ w * algebraMap F D ((![0, 1] : Fin 2 → F) i) := by
    funext i
    fin_cases i <;> simp [hv']
  have hr := congrArg ρ hrel
  rw [comp_aeval_apply, map_zero, hmap, homogeneous_aeval_mul hp, mapped_eval] at hr
  have hunit : IsUnit (ρ w) := hw
  exact ((map_ne_zero (algebraMap F D)).2 (eval_on_axis_ne_zero hp hrest))
    ((hunit.pow n).mul_left_cancel (hr.trans (mul_zero _).symm))

private def pairForms (t : FreshField) : Fin 2 → FreshJetRing :=
  ![MvPolynomial.X 0, MvPolynomial.X 1 - C t * MvPolynomial.X 2]

private theorem pairForms_homogeneous (t : FreshField) (i : Fin 2) :
    (pairForms t i).IsHomogeneous 1 := by
  fin_cases i
  · exact isHomogeneous_X FreshField 0
  · exact (isHomogeneous_X FreshField (1 : Fin 3)).sub
      ((isHomogeneous_C (Fin 3) t).mul (isHomogeneous_X FreshField 2))

/-- Express the old jet coordinates in the order (free variable, value, second form). -/
private def shear (t : FreshField) : Fin 3 → FreshJetRing :=
  ![MvPolynomial.X 1, MvPolynomial.X 2 + C t * MvPolynomial.X 0, MvPolynomial.X 0]

private theorem shear_homogeneous (t : FreshField) (i : Fin 3) :
    (shear t i).IsHomogeneous 1 := by
  fin_cases i
  · exact isHomogeneous_X FreshField 1
  · exact (isHomogeneous_X FreshField (2 : Fin 3)).add
      ((isHomogeneous_C (Fin 3) t).mul (isHomogeneous_X FreshField 0))
  · exact isHomogeneous_X FreshField 0

/-- The relation is a polynomial in the free coordinate with constant, nonzero leading
coefficient. The evaluation along the kernel line computes that coefficient. -/
private theorem unit_leading_coeff (t : FreshField) {p : FreshJetRing} {n : ℕ}
    (hp : p.IsHomogeneous n) (ht : eval ![0, t, 1] p ≠ 0) :
    IsUnit (finSuccEquiv FreshField 2 (aeval (shear t) p)).leadingCoeff := by
  let q : FreshJetRing := aeval (shear t) p
  let P := finSuccEquiv FreshField 2 q
  have hq : q.IsHomogeneous n := by
    simpa [q] using hp.aeval (shear t) (shear_homogeneous t)
  have hn : P.natDegree ≤ n := by
    rw [show P = finSuccEquiv FreshField 2 q from rfl, natDegree_finSuccEquiv]
    exact (degreeOf_le_totalDegree _ _).trans hq.totalDegree_le
  have heq : eval (Fin.cons 1 0) q = eval ![0, t, 1] p := by
    change (aeval (Fin.cons 1 0 : Fin 3 → FreshField)) (aeval (shear t) p) = _
    rw [comp_aeval_apply]
    let a : Fin 3 → FreshField := Fin.cons 1 0
    have h1 : a 1 = 0 := Fin.cons_succ (α := fun _ => FreshField) 1 (0 : Fin 2 → FreshField) 0
    have h2 : a 2 = 0 := Fin.cons_succ (α := fun _ => FreshField) 1 (0 : Fin 2 → FreshField) 1
    have h0 : a 0 = 1 := Fin.cons_zero (α := fun _ => FreshField) _ _
    have hx : (fun i => eval a (shear t i)) = ![0, t, 1] := by
      funext i
      fin_cases i <;> simp [shear, h0, h1, h2]
    change aeval (fun i => eval a (shear t i)) p = aeval ![0, t, 1] p
    rw [hx]
  have hz (i : ℕ) (hi : i ∈ Finset.range n) : constantCoeff (P.coeff i) = 0 := by
    have hil := Finset.mem_range.mp hi
    exact (hq.finSuccEquiv_coeff_isHomogeneous i (n - i) (by omega)).coeff_eq_zero (by simp; omega)
  have heval : constantCoeff (P.coeff n) = eval ![0, t, 1] p := by
    rw [← heq, eval_eq_eval_mv_eval', Polynomial.eval_one_map, eval_zero]
    change _ = constantCoeff (P.eval 1)
    rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < n + 1)]
    simp [Finset.sum_range_succ, Finset.sum_eq_zero hz]
  have htop : P.coeff n = C (eval ![0, t, 1] p) := by
    rw [← heval]
    have hhom := hq.finSuccEquiv_coeff_isHomogeneous n 0 (add_zero n)
    exact (homogeneousComponent_eq_self hhom).symm.trans (homogeneousComponent_zero _)
  have hdegree : P.natDegree = n := hn.antisymm <|
    Polynomial.le_natDegree_of_ne_zero (by rw [htop]; simpa using ht)
  change IsUnit P.leadingCoeff
  rw [Polynomial.leadingCoeff, hdegree, htop]
  exact ht.isUnit.map C

private theorem finite_of_monic_root {R S : Type} [CommRing R] [CommRing S]
    (g : R →+* S) (z : S) (Q : R[X]) (hm : Q.Monic) (hQ : Q.eval₂ g z = 0)
    (hE : ∀ y : S, ∃ x : R[X], x.eval₂ g z = y) : g.Finite := by
  let f := AdjoinRoot.lift g z hQ
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hE y
    exact ⟨AdjoinRoot.mk Q x, (AdjoinRoot.lift_mk hQ x).trans hx⟩
  rw [← AdjoinRoot.lift_comp_of hQ]
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective f hf)
    (RingHom.finite_algebraMap.mpr hm.finite_adjoinRoot)

private theorem finite_chosen_pair {A : Type} [CommRing A] [Algebra FreshField A]
    (d : Fin 3 → A) (t : FreshField) {p : FreshJetRing} {n : ℕ}
    (hp : p.IsHomogeneous n) (hrel : aeval d p = 0) (ht : eval ![0, t, 1] p ≠ 0) :
    FiniteJetPair (pairForms t) (coneJetIdeal d) := by
  refine ⟨pairForms_homogeneous t, ?_⟩
  let J := coneJetIdeal d
  let g := jetPairMap (pairForms t) J
  let z := Ideal.Quotient.mk J (MvPolynomial.X 2)
  let E : PairRing[X] →ₐ[FreshField] FreshJetRing ⧸ J :=
    Polynomial.eval₂AlgHom g z (fun a => by
      change g a * z = z * g a
      exact mul_comm (g a) z)
  let ψ : FreshJetRing →ₐ[FreshField] PairRing[X] :=
    (finSuccEquiv FreshField 2).toAlgHom.comp (aeval (shear t))
  have hEC (a : PairRing) : E (Polynomial.C a) = g a := Polynomial.eval₂_C _ _
  have hEX : E Polynomial.X = z := Polynomial.eval₂_X _ _
  have hψ (i : Fin 3) : ψ (MvPolynomial.X i) = finSuccEquiv FreshField 2 (shear t i) := by
    simp [ψ]
  have hg (i : Fin 2) : g (MvPolynomial.X i) = Ideal.Quotient.mk J (pairForms t i) := by
    simp [g, jetPairMap]
  have hX1 : finSuccEquiv FreshField 2 (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) :=
    finSuccEquiv_X_succ (j := 0)
  have hX2 : finSuccEquiv FreshField 2 (MvPolynomial.X 2) = Polynomial.C (MvPolynomial.X 1) :=
    finSuccEquiv_X_succ (j := 1)
  have hscalar : E (finSuccEquiv FreshField 2 (C t)) = Ideal.Quotient.mk J (C t) :=
    ((E.comp (finSuccEquiv FreshField 2).toAlgHom).commutes t).trans
      ((Ideal.Quotient.mkₐ FreshField J).commutes t).symm
  have hcomp : E.comp ψ = Ideal.Quotient.mkₐ FreshField J := by
    apply MvPolynomial.algHom_ext
    intro i
    change E (ψ (MvPolynomial.X i)) = Ideal.Quotient.mk J (MvPolynomial.X i)
    rw [hψ]
    fin_cases i
    · change E (finSuccEquiv FreshField 2 (MvPolynomial.X 1)) = _
      rw [hX1, hEC, hg]
      rfl
    · change E (finSuccEquiv FreshField 2 (MvPolynomial.X 2 + C t * MvPolynomial.X 0)) = _
      rw [map_add, map_mul, hX2, finSuccEquiv_X_zero, map_add, map_mul, hEC, hg, hEX, hscalar]
      change Ideal.Quotient.mk J (MvPolynomial.X 1 - C t * MvPolynomial.X 2) +
        Ideal.Quotient.mk J (C t) * Ideal.Quotient.mk J (MvPolynomial.X 2) = _
      rw [← map_mul, ← map_add, sub_add_cancel]
      rfl
    · change E (finSuccEquiv FreshField 2 (MvPolynomial.X 0)) = _
      rw [finSuccEquiv_X_zero, hEX]
      rfl
  have hE : Function.Surjective E := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨ψ x, (DFunLike.congr_fun hcomp x).trans hx⟩
  let P := ψ p
  have hP : E P = 0 := by
    change (E.comp ψ) p = 0
    rw [hcomp]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact show scaled d p = 0 from by
      rw [scaled_homogeneous d hp, hrel, Polynomial.monomial_zero_right]
  have hu : IsUnit P.leadingCoeff := unit_leading_coeff t hp ht
  let Q := (↑hu.unit⁻¹ : PairRing) • P
  have hm : Q.Monic := Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu
  have hQ : Q.eval₂ g.toRingHom z = 0 := by
    change E Q = 0
    rw [show Q = Polynomial.C (↑hu.unit⁻¹ : PairRing) * P by
      simp [Q, Polynomial.smul_eq_C_mul], map_mul, hP, mul_zero]
  refine @finite_of_monic_root PairRing (FreshJetRing ⧸ J) _ _ g.toRingHom z Q hm hQ ?_
  intro y
  obtain ⟨x, hx⟩ := hE y
  exact ⟨x, hx⟩

/-- Choose a finite linear normalization retaining the zeroth jet. -/
theorem proof : K1_13_5_5_2_1.c5 := by
  classical
  intro A _ _ _ d L hd hdu hspan hL
  let _ : Infinite FreshField :=
    Infinite.of_injective _ (IsFractionRing.injective (Polynomial K1_13.Geom) FreshField)
  obtain ⟨p, n, hp, hrel, hrest⟩ := relation_on_value_plane d hd (cone_has_relation d L hL)
  obtain ⟨t, ht⟩ := choose_direction hp hrest
  let w := d 1 - algebraMap FreshField A t * d 2
  have hw : IsUnit (Ideal.Quotient.mk (Ideal.span {d 0}) w) :=
    slope_unit d hspan t hp hrel ht
  have hmap : conePairMap d (pairForms t) = valuePairMap (d 0) w := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [conePairMap, coneJetMap, pairForms, polynomialPairMap]
    · simp [conePairMap, coneJetMap, pairForms, polynomialPairMap, w,
        Polynomial.algebraMap_apply, sub_mul, mul_assoc]
  exact ⟨pairForms t, w, finite_chosen_pair d t hp hrel ht, hmap,
    hmap.symm ▸ pin_injective (F := FreshField) (d 0) w hd hdu hw, hw⟩

end

end K1_13_5_5_2_1_5
end PackSource_K1_13_5_5_2_1_5Proof

section PackSource_K1_13_5_5_2_1_4_2Proof
set_option autoImplicit true
namespace K1_13_5_5_2_1_4_2

noncomputable section

open Algebra K1_13 K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1 K1_13_5_5_2_1_4
open scoped TensorProduct nonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem trdeg_fraction (k B : Type) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] : trdeg k (FractionRing B) = trdeg k B := by
  let : Algebra.IsAlgebraic B (FractionRing B) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing B)).mpr inferInstance
  rw [← trdeg_add_eq k B, trdeg_eq_zero (R := B), add_zero]

private theorem trdeg_of_normalization {k B : Type} [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] {n : ℕ} (u : MvPolynomial (Fin n) k →ₐ[k] B)
    (hu : Function.Injective u) (hfin : u.Finite) : trdeg k B = n := by
  let P := MvPolynomial (Fin n) k
  let : Algebra P B := u.toRingHom.toAlgebra
  let : IsScalarTower k P B := IsScalarTower.of_algHom u
  let : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective P B).mpr hu
  let : Module.Finite P B := hfin
  rw [← trdeg_add_eq k P (A := B), trdeg_eq_zero (R := P), add_zero,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin]

private theorem surface_trdeg {k σ : Type} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [IsDomain (MvPolynomial σ k ⧸ I)]
    (h : (MvPolynomial.affineHilbertPolynomial I).natDegree = 2) :
    trdeg k (FractionRing (MvPolynomial σ k ⧸ I)) = 2 := by
  obtain ⟨n, u, hu, hfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hn : n = 2 := by
    simpa only [MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective
      u hfin hu, Nat.card_fin] using h
  rw [trdeg_fraction, trdeg_of_normalization u hu hfin, hn]
  rfl

private theorem trdeg_pair (k : Type) [Field k] :
    trdeg k (FractionRing (MvPolynomial (Fin 2) k)) = 2 := by
  rw [trdeg_fraction]
  simp

/-- An algebraic fraction field over the localized base is already the generic fiber. -/
private def localizedEquiv {P K A E : Type} [CommRing P] [Field K] [CommRing A] [Field E]
    [Algebra P K] [IsFractionRing P K] [Algebra P A] [Algebra A E] [IsFractionRing A E]
    [Algebra K E] [Algebra.IsAlgebraic K E]
    (h : ∀ p, algebraMap K E (algebraMap P K p) = algebraMap A E (algebraMap P A p)) :
    K ⊗[P] A ≃ₗ[K] E := by
  letI : Algebra P E := ((algebraMap A E).comp (algebraMap P A)).toAlgebra
  letI : IsScalarTower P K E := IsScalarTower.of_algebraMap_eq fun p => (h p).symm
  let T := K ⊗[P] A
  let j : A →ₐ[P] E := ⟨algebraMap A E, fun _ => rfl⟩
  let f : T →ₐ[K] E := AlgHom.liftEquiv P K A E j
  letI : Algebra A T := Algebra.TensorProduct.rightAlgebra
  let S := Algebra.algebraMapSubmonoid A (nonZeroDivisors P)
  letI : IsLocalization S T := IsLocalization.tensorRight K (nonZeroDivisors P)
  have hf (a : A) : f (algebraMap A T a) = algebraMap A E a := by
    change (AlgHom.liftEquiv P K A E j) (1 ⊗ₜ[P] a) = _
    rw [AlgHom.liftEquiv_tmul, one_smul]
    rfl
  have hinj : Function.Injective f := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq S f.toRingHom).mpr
    intro x y
    constructor
    · exact congrArg f
    · intro hxy
      change f (algebraMap A T x) = f (algebraMap A T y) at hxy
      rw [hf, hf] at hxy
      exact congrArg (algebraMap A T) (IsFractionRing.injective A E hxy)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective A z
    change algebraMap A E u / algebraMap A E v ∈ f.range
    have hu : algebraMap A E u ∈ f.range := ⟨algebraMap A T u, hf u⟩
    have hv : algebraMap A E v ∈ f.range := ⟨algebraMap A T v, hf v⟩
    have hi : (algebraMap A E v)⁻¹ ∈ f.range :=
      f.range.inv_mem_of_algebraic (x := ⟨_, hv⟩) (Algebra.IsAlgebraic.isAlgebraic _)
    simpa only [div_eq_mul_inv] using f.range.mul_mem hu hi
  exact (AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).toLinearEquiv

private abbrev fiber {k P : Type} [CommRing k] [CommRing P] [Algebra k P]
    (K : Type) [Field K] [Algebra P K] {A : Type} [CommRing A] [Algebra k A]
    (φ : P →ₐ[k] A) : Type :=
  letI : Module P A := Module.compHom A φ.toRingHom
  K ⊗[P] A

private def fiberEquiv {k P K A : Type} [Field k] [CommRing P] [Field K] [Algebra k P]
    [Algebra P K] [IsFractionRing P K] [CommRing A] [IsDomain A] [Algebra k A]
    (φ : P →ₐ[k] A) [Algebra K (FractionRing A)] [Algebra.IsAlgebraic K (FractionRing A)]
    (h : ∀ p, algebraMap K (FractionRing A) (algebraMap P K p) = toFraction A (φ p)) :
    fiber K φ ≃ₗ[K] FractionRing A := by
  letI : Algebra P A := φ.toRingHom.toAlgebra
  exact localizedEquiv h

private theorem fiber_zero {k P K A : Type} [Field k] [CommRing P] [Field K] [Algebra k P]
    [Algebra P K] [IsFractionRing P K] [CommRing A] [Algebra k A]
    (φ : P →ₐ[k] A) {p : P} (hp : p ≠ 0) (hz : φ p = 0) :
    Module.Finite K (fiber K φ) ∧ Module.finrank K (fiber K φ) = 0 := by
  let : Module P A := Module.compHom A φ.toRingHom
  have hp' : algebraMap P K p ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective P K).ne hp
  have hzero (z : fiber K φ) : z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul x a =>
      have heq : p • (x / algebraMap P K p) = x := by
        rw [Algebra.smul_def, mul_comm, div_mul_cancel₀ _ hp']
      calc
        x ⊗ₜ[P] a = (p • (x / algebraMap P K p)) ⊗ₜ[P] a := by
          rw [heq]
        _ = (x / algebraMap P K p) ⊗ₜ[P] (p • a) :=
          TensorProduct.smul_tmul _ _ _
        _ = 0 := by
          change _ ⊗ₜ[P] (φ p * a) = _
          rw [hz, zero_mul, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, zero_add]
  let : Subsingleton (fiber K φ) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  exact ⟨inferInstance, Module.finrank_zero_of_subsingleton⟩

private theorem finiteExtension {k K E : Type} [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra.EssFiniteType k E] (i : K →ₐ[k] E)
    (hK : trdeg k K = 2) (hE : trdeg k E = 2) :
    letI : Algebra K E := i.toRingHom.toAlgebra
    Algebra.IsAlgebraic K E ∧ Module.Finite K E := by
  let : Algebra K E := i.toRingHom.toAlgebra
  let : IsScalarTower k K E := IsScalarTower.of_algHom i
  have h := trdeg_add_eq k K (A := E)
  rw [hK, hE, add_comm 2] at h
  have halg : Algebra.IsAlgebraic K E := by
    apply trdeg_eq_zero_iff.mp
    apply (Cardinal.add_right_inj_of_lt_aleph0 (γ := 2) (by simp)).mp
    rw [h, zero_add]
  let : Algebra.EssFiniteType K E := Algebra.EssFiniteType.of_comp k K E
  exact ⟨halg, Algebra.finite_of_essFiniteType_of_isAlgebraic⟩

/-- Extend the pair map to the generic point by taking fractions. -/
private def pairEmbedding {k P K A : Type} [Field k] [CommRing P] [Field K]
    [Algebra k P] [Algebra P K] [IsFractionRing P K] [Algebra k K] [IsScalarTower k P K]
    [CommRing A] [IsDomain A] [Algebra k A]
    {φ : P →ₐ[k] A} (hφ : Function.Injective φ) : K →ₐ[k] FractionRing A :=
  IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom k A (FractionRing A)).comp φ)
    ((IsFractionRing.injective A (FractionRing A)).comp hφ)

private theorem pairEmbedding_apply {k P K A : Type} [Field k] [CommRing P] [Field K]
    [Algebra k P] [Algebra P K] [IsFractionRing P K] [Algebra k K] [IsScalarTower k P K]
    [CommRing A] [IsDomain A] [Algebra k A] {φ : P →ₐ[k] A}
    (hφ : Function.Injective φ) (p : P) :
    pairEmbedding (K := K) hφ (algebraMap P K p) = toFraction A (φ p) := by
  unfold pairEmbedding
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

private theorem compareFibers {k P K B A : Type} [Field k] [CommRing P] [Field K]
    [Algebra k P] [Algebra P K] [IsFractionRing P K] [Algebra k K] [IsScalarTower k P K]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [CommRing A] [IsDomain A] [Algebra k A]
    (φ : P →ₐ[k] B) (ψ : P →ₐ[k] A) (e : FractionRing B ≃ₐ[k] FractionRing A)
    (hK : trdeg k K = 2) (hB : trdeg k (FractionRing B) = 2)
    (he : ∀ p, e (toFraction B (φ p)) = toFraction A (ψ p)) :
    Module.Finite K (fiber K ψ) ∧ Module.finrank K (fiber K ψ) = Module.finrank K (fiber K φ) := by
  by_cases hφ : Function.Injective φ
  · have hψ : Function.Injective ψ := by
      intro x y hxy
      apply hφ
      apply IsFractionRing.injective B (FractionRing B)
      apply e.injective
      rw [he x, he y, hxy]
    let : Algebra.EssFiniteType B (FractionRing B) :=
      Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors B)
    let : Algebra.EssFiniteType k (FractionRing B) :=
      Algebra.EssFiniteType.comp k B (FractionRing B)
    let i : K →ₐ[k] FractionRing B := pairEmbedding hφ
    let j : K →ₐ[k] FractionRing A := pairEmbedding hψ
    obtain ⟨halg, hfinite⟩ := finiteExtension i hK hB
    let : Algebra K (FractionRing B) := i.toRingHom.toAlgebra
    let : Algebra K (FractionRing A) := j.toRingHom.toAlgebra
    let : Algebra.IsAlgebraic K (FractionRing B) := halg
    let : Module.Finite K (FractionRing B) := hfinite
    have hi (p : P) : i (algebraMap P K p) = toFraction B (φ p) := pairEmbedding_apply hφ p
    have hj (p : P) : j (algebraMap P K p) = toFraction A (ψ p) := pairEmbedding_apply hψ p
    have he' : e.toRingHom.comp i.toRingHom = j.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := P)
      intro p
      change e (i (algebraMap P K p)) = j (algebraMap P K p)
      rw [hi, hj, he]
    let e' : FractionRing B ≃ₐ[K] FractionRing A :=
      AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun x => RingHom.congr_fun he' x
    let : Algebra.IsAlgebraic K (FractionRing A) := e'.isAlgebraic
    let l := fiberEquiv φ hi
    let r := fiberEquiv ψ hj
    let fiberComparison := (l.trans e'.toLinearEquiv).trans r.symm
    let : Module.Finite K (fiber K φ) := Module.Finite.equiv l.symm
    exact ⟨Module.Finite.equiv fiberComparison, fiberComparison.finrank_eq.symm⟩
  · obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hφ
    have hp : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hz : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz' : ψ (x - y) = 0 := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [← he (x - y), hz, map_zero, map_zero, map_zero]
    obtain ⟨_, hl⟩ := fiber_zero (K := K) φ hp hz
    obtain ⟨hr, hrank⟩ := fiber_zero (K := K) ψ hp hz'
    exact ⟨hr, hrank.trans hl.symm⟩

section Surface

variable {k σ : Type} [Field k] [Finite σ]

local notation "PairBase" => MvPolynomial (Fin 2) k
local notation "PairFrac" => FractionRing (MvPolynomial (Fin 2) k)

private theorem compareSurfaceFibers
    (I : Ideal (MvPolynomial σ k)) [IsDomain (MvPolynomial σ k ⧸ I)]
    (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    (φ : PairBase →ₐ[k] (MvPolynomial σ k ⧸ I)) (ψ : PairBase →ₐ[k] A)
    (e : FractionRing (MvPolynomial σ k ⧸ I) ≃ₐ[k] FractionRing A)
    (hdim : (MvPolynomial.affineHilbertPolynomial I).natDegree = 2)
    (he : ∀ p, e (toFraction (MvPolynomial σ k ⧸ I) (φ p)) = toFraction A (ψ p)) :
    Module.Finite PairFrac (fiber PairFrac ψ) ∧
      Module.finrank PairFrac (fiber PairFrac ψ) = Module.finrank PairFrac (fiber PairFrac φ) :=
  compareFibers (K := PairFrac) φ ψ e (trdeg_pair k) (surface_trdeg I hdim) he

end Surface

/-- The generic pair rank is preserved by a compatible birational change of coordinates. -/
theorem proof : K1_13_5_5_2_1_4.c2 :=
  compareSurfaceFibers (k := FreshField) (σ := CoeffIndex)

end
end K1_13_5_5_2_1_4_2
end PackSource_K1_13_5_5_2_1_4_2Proof

section PackSource_K1_13_5_5_2_1_3Proof
set_option autoImplicit true
namespace K1_13_5_5_2_1_3

noncomputable section

open K1_13 K1_13_5_5_2_1
open Polynomial
open scoped Polynomial

/-- The value and the first two ordinary derivatives, with their product rule. -/
@[ext] private structure Jet (R : Type) where
  value : R
  first : R
  second : R

private def jetMul {R : Type} [CommRing R] (x y : Jet R) : Jet R :=
  ⟨x.value * y.value,
    x.first * y.value + x.value * y.first,
    x.second * y.value + 2 * x.first * y.first + x.value * y.second⟩

private instance {R : Type} [CommRing R] : CommMonoid (Jet R) where
  one := ⟨1, 0, 0⟩
  mul := jetMul
  one_mul x := by
    change jetMul ⟨1, 0, 0⟩ x = x
    apply Jet.ext <;> simp [jetMul]
  mul_one x := by
    change jetMul x ⟨1, 0, 0⟩ = x
    apply Jet.ext <;> simp [jetMul]
  mul_assoc x y z := by
    change jetMul (jetMul x y) z = jetMul x (jetMul y z)
    apply Jet.ext <;> simp only [jetMul] <;> ring
  mul_comm x y := by
    change jetMul x y = jetMul y x
    apply Jet.ext <;> simp only [jetMul] <;> ring

private def rawJet {A : Type} [CommRing A] : A[X] →* Jet A[X] where
  toFun g := ⟨g, derivative g, derivative (derivative g)⟩
  map_one' := by
    change (⟨1, derivative 1, derivative (derivative 1)⟩ : Jet A[X]) = ⟨1, 0, 0⟩
    simp
  map_mul' g h := by
    apply Jet.ext
    · rfl
    · exact derivative_mul
    · change derivative (derivative (g * h)) =
        derivative (derivative g) * h + 2 * derivative g * derivative h +
          g * derivative (derivative h)
      simp only [derivative_mul, map_add]
      ring

private def scalarJet {R : Type} [CommRing R] : R →* Jet R where
  toFun a := ⟨a, 0, 0⟩
  map_one' := rfl
  map_mul' a b := by
    change ⟨a * b, 0, 0⟩ = jetMul ⟨a, 0, 0⟩ ⟨b, 0, 0⟩
    simp [jetMul]

private def valueHom {R : Type} [CommRing R] : Jet R →* R where
  toFun := Jet.value
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Remove the common power from the derivatives of one factor. -/
private def reducedPower {A : Type} [CommRing A] (g : A[X]) : ℕ → Jet A[X]
  | 0 => 1
  | 1 => rawJet g
  | k + 2 =>
    ⟨g ^ 2,
      C ((k + 2 : ℕ) : A) * g * derivative g,
      C ((k + 2 : ℕ) : A) * C ((k + 1 : ℕ) : A) * derivative g ^ 2 +
        C ((k + 2 : ℕ) : A) * g * derivative (derivative g)⟩

private theorem reducedPower_value {A : Type} [CommRing A] (g : A[X]) (m : ℕ) :
    (reducedPower g m).value = g ^ min m 2 := by
  match m with
  | 0 => exact (pow_zero g).symm
  | 1 => exact (pow_one g).symm
  | k + 2 =>
    change g ^ 2 = g ^ min (k + 2) 2
    rw [min_eq_right (by omega)]

private theorem rawJet_pow {A : Type} [CommRing A] (g : A[X]) (m : ℕ) :
    rawJet (g ^ m) = scalarJet (g ^ (m - 2)) * reducedPower g m := by
  match m with
  | 0 => simp [reducedPower]
  | 1 => simp [reducedPower]
  | k + 2 =>
    apply Jet.ext
    · change g ^ (k + 2) = g ^ k * g ^ 2
      exact pow_add g k 2
    · change derivative (g ^ (k + 2)) =
        0 * g ^ 2 + g ^ k * (C ((k + 2 : ℕ) : A) * g * derivative g)
      rw [zero_mul, zero_add, derivative_pow_succ, pow_succ g k]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_one, map_ofNat]
      ring
    · change derivative (derivative (g ^ (k + 2))) =
        0 * g ^ 2 + 2 * 0 * (C ((k + 2 : ℕ) : A) * g * derivative g) +
          g ^ k * (C ((k + 2 : ℕ) : A) * C ((k + 1 : ℕ) : A) * derivative g ^ 2 +
            C ((k + 2 : ℕ) : A) * g * derivative (derivative g))
      rw [derivative_pow_succ, derivative_mul, derivative_C_mul,
        derivative_pow_succ, pow_succ g k]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_one, map_ofNat]
      ring

private def reducedProduct {A : Type} [CommRing A] {f : A[X]}
    (s : Factorization f) : Jet A[X] :=
  ∏ i, reducedPower (s.factor i) (s.multiplicity i)

private theorem reducedProduct_value {A : Type} [CommRing A] {f : A[X]}
    (s : Factorization f) : (reducedProduct s).value = trimmedValue s := by
  change valueHom (∏ i, reducedPower (s.factor i) (s.multiplicity i)) = _
  rw [map_prod, trimmedValue]
  exact Finset.prod_congr rfl (fun i _ => reducedPower_value _ _)

private theorem rawJet_factorization {A : Type} [CommRing A] {f : A[X]}
    (s : Factorization f) :
    rawJet f = scalarJet (commonFactor s) * reducedProduct s := by
  calc
    rawJet f = ∏ i, rawJet (s.factor i ^ s.multiplicity i) :=
      (congrArg rawJet s.product_eq).trans (map_prod rawJet _ _)
    _ = ∏ i, scalarJet (s.factor i ^ (s.multiplicity i - 2)) *
        reducedPower (s.factor i) (s.multiplicity i) :=
      Finset.prod_congr rfl (fun i _ => rawJet_pow _ _)
    _ = _ := by rw [Finset.prod_mul_distrib, commonFactor, map_prod, reducedProduct]

private theorem geom_cast_ne_zero {n : ℕ} (hpos : 0 < n) (hsmall : n < K1.p) :
    (n : Geom) ≠ 0 := by
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  intro h
  exact (not_le_of_gt hsmall) (Nat.le_of_dvd hpos
    ((CharP.cast_eq_zero_iff Geom K1.p n).mp h))

private theorem isUnit_C_small {A : Type} [CommRing A] [Algebra Geom A]
    {n : ℕ} (hpos : 0 < n) (hsmall : n ≤ 133634) : IsUnit (C (n : A)) := by
  let ι : Geom →+* A[X] := C.comp (algebraMap Geom A)
  have hu := (isUnit_iff_ne_zero.mpr (geom_cast_ne_zero hpos
    (hsmall.trans_lt (by decide : 133634 < K1.p)))).map ι
  simpa only [ι, RingHom.comp_apply, map_natCast] using hu

private theorem not_mem_of_coprime {R : Type} [CommRing R] {P : Ideal R}
    (hP : P ≠ ⊤) {x y : R} (hx : x ∈ P) (hxy : IsCoprime x y) : y ∉ P := by
  intro hy
  obtain ⟨a, b, hab⟩ := hxy
  exact hP ((Ideal.eq_top_iff_one P).mpr (hab ▸ P.add_mem (P.mul_mem_left a hx)
    (P.mul_mem_left b hy)))

/-- A prime containing the reduced value misses one of the other reduced derivatives. -/
private theorem reducedProduct_escapes_prime {A : Type} [CommRing A] [Algebra Geom A]
    {f : A[X]} (s : Factorization f) (P : Ideal A[X]) [hP : P.IsPrime]
    (hv : (reducedProduct s).value ∈ P) :
    (reducedProduct s).first ∉ P ∨ (reducedProduct s).second ∉ P := by
  classical
  rw [reducedProduct_value, trimmedValue] at hv
  obtain ⟨i, hi, hiPow⟩ := Ideal.IsPrime.prod_mem_iff.mp hv
  have hgi := hP.mem_of_pow_mem _ hiPow
  let g := s.factor i
  let m := s.multiplicity i
  have hm : 0 < m ∧ m ≤ 133634 := s.multiplicity_bounds i
  have hd : derivative g ∉ P :=
    not_mem_of_coprime hP.ne_top' hgi (s.derivative_coprime i)
  let t := ∏ j ∈ Finset.univ.erase i, reducedPower (s.factor j) (s.multiplicity j)
  have ht : t.value ∉ P := by
    change valueHom (∏ j ∈ Finset.univ.erase i,
      reducedPower (s.factor j) (s.multiplicity j)) ∉ P
    rw [map_prod]
    intro h
    obtain ⟨j, hj, hjPow⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    change (reducedPower (s.factor j) (s.multiplicity j)).value ∈ P at hjPow
    rw [reducedPower_value] at hjPow
    exact (not_mem_of_coprime hP.ne_top' hgi
      (s.pairwise_coprime (Finset.ne_of_mem_erase hj).symm)) (hP.mem_of_pow_mem _ hjPow)
  have he : reducedProduct s = reducedPower g m * t :=
    (Finset.mul_prod_erase _ _ hi).symm
  have hg : g ∈ P := hgi
  by_cases hm1 : m = 1
  · left
    rw [he, hm1]
    change derivative g * t.value + g * t.first ∉ P
    intro h
    exact hP.mul_notMem hd ht (by simpa using P.sub_mem h (P.mul_mem_right t.first hg))
  · right
    have hm2 : m = (m - 2) + 2 := by omega
    let k := m - 2
    have hk : m = k + 2 := hm2
    have hu0 : C ((k + 2 : ℕ) : A) ∉ P :=
      P.notMem_of_isUnit (isUnit_C_small (by omega : 0 < k + 2) (by omega : k + 2 ≤ 133634))
    have hu1 : C ((k + 1 : ℕ) : A) ∉ P :=
      P.notMem_of_isUnit (isUnit_C_small (by omega : 0 < k + 1) (by omega : k + 1 ≤ 133634))
    rw [he, hk]
    let a : A[X] := C ((k + 2 : ℕ) : A)
    let b : A[X] := C ((k + 1 : ℕ) : A)
    change (a * b * derivative g ^ 2 + a * g * derivative (derivative g)) * t.value +
      2 * (a * g * derivative g) * t.first + g ^ 2 * t.second ∉ P
    intro h
    have h₁ : a * g * derivative (derivative g) * t.value ∈ P :=
      P.mul_mem_right _ (P.mul_mem_right _ (P.mul_mem_left _ hg))
    have h₂ : 2 * (a * g * derivative g) * t.first ∈ P :=
      P.mul_mem_right _ (P.mul_mem_left _ (P.mul_mem_right _ (P.mul_mem_left _ hg)))
    have h₃ : g ^ 2 * t.second ∈ P := P.mul_mem_right _ (P.pow_mem_of_mem hg 2 (by decide))
    rw [add_mul] at h
    have h' := P.sub_mem (P.sub_mem (P.sub_mem h h₃) h₂) h₁
    have hn : a * b * derivative g ^ 2 * t.value ∉ P :=
      hP.mul_notMem (hP.mul_notMem (hP.mul_notMem hu0 hu1)
        (fun h => hd (hP.mem_of_pow_mem 2 h))) ht
    exact hn (by simpa using h')

private def half (A : Type) [CommRing A] [Algebra Geom A] : A[X] :=
  C (algebraMap Geom A ((2 : Geom)⁻¹))

private theorem two_mul_half (A : Type) [CommRing A] [Algebra Geom A] :
    (2 : A[X]) * half A = 1 := by
  let ι : Geom →+* A[X] := C.comp (algebraMap Geom A)
  have htwo := geom_cast_ne_zero (n := 2) (by decide) (by decide)
  have hh : (2 : Geom) * (2 : Geom)⁻¹ = 1 := mul_inv_cancel₀ htwo
  change (2 : A[X]) * ι ((2 : Geom)⁻¹) = 1
  simpa only [map_mul, map_ofNat, map_one] using congrArg ι hh

private theorem two_hasse {A : Type} [CommRing A] (f : A[X]) :
    (2 : A[X]) * hasseDeriv 2 f = derivative (derivative f) := by
  simpa [Nat.factorial, nsmul_eq_mul, Function.iterate_succ_apply'] using
    congrFun (factorial_smul_hasseDeriv (R := A) 2) f

theorem proof : K1_13_5_5_2_1.c3 := by
  intro A _ _ f s
  let t := reducedProduct s
  let q : Fin 3 → A[X] := ![t.value, t.first, half A * t.second]
  have he := rawJet_factorization s
  have h0 : f = commonFactor s * t.value := congrArg Jet.value he
  have h1 : derivative f = commonFactor s * t.first := by
    have h := congrArg Jet.first he
    change derivative f = 0 * t.value + commonFactor s * t.first at h
    simpa only [zero_mul, zero_add] using h
  have h2 : derivative (derivative f) = commonFactor s * t.second := by
    have h := congrArg Jet.second he
    change derivative (derivative f) =
      0 * t.value + 2 * 0 * t.first + commonFactor s * t.second at h
    simpa only [mul_zero, zero_mul, zero_add] using h
  refine ⟨q, reducedProduct_value s, ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa [q] using h0.symm
    · simpa [q] using h1.symm
    · change commonFactor s * (half A * t.second) = hasseDeriv 2 f
      calc
        commonFactor s * (half A * t.second) =
            half A * (commonFactor s * t.second) := by ac_rfl
        _ = half A * derivative (derivative f) := by rw [h2]
        _ = _ := by rw [← two_hasse, ← mul_assoc, mul_comm (half A), two_mul_half, one_mul]
  · by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    let _ : P.IsPrime := hP.isPrime
    have hmem (j : Fin 3) : q j ∈ P := hle (Ideal.subset_span ⟨j, rfl⟩)
    have hsecond : t.second ∈ P := by
      have hh : half A * t.second ∈ P := hmem 2
      have hh' := P.mul_mem_left (2 : A[X]) hh
      rwa [← mul_assoc, two_mul_half, one_mul] at hh'
    exact (reducedProduct_escapes_prime s P (hmem 0)).elim
      (fun hfirst => hfirst (hmem 1)) (fun hn => hn hsecond)

end

end K1_13_5_5_2_1_3
end PackSource_K1_13_5_5_2_1_3Proof

section PackSource_K1_13_5_5_2_1_1_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_5_2_1_1_2

open MvPolynomial

/-- The cyclic Hilbert identity specializes to a backward difference when
regularity makes the colon ideal equal to the original ideal. -/
theorem proof : K1_13_5_5_2_1_1.c2 := by
  intro F σ _ _ I ℓ hI _ hℓ hregular
  have hcolon : I.colon {ℓ} = I := by
    refine le_antisymm ?_ Ideal.le_colon
    intro a ha
    have hmul : ℓ * a ∈ I := by
      rw [mul_comm]
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hregular
    change Ideal.Quotient.mk I ℓ * Ideal.Quotient.mk I a = Ideal.Quotient.mk I ℓ * 0
    rw [mul_zero, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmul
  have h := K1_13_6_3_5_1.hilbertPolynomial_cyclic hI hℓ
  rw [hcolon, Nat.cast_one] at h
  exact eq_sub_of_add_eq h

end K1_13_5_5_2_1_1_2
end PackSource_K1_13_5_5_2_1_1_2Proof

section PackSource_K1_13_1_1Translation
set_option autoImplicit true
namespace K1_13_1_1

open K1_13 K1_13_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 800000


private theorem exponent_le_of_mem_translation_monomial
    (x y : Geom) (u v : JetVariable 3 →₀ ℕ) (a : Geom)
    (hv : v ∈ (globalPointTranslation x y (monomial u a)).support) : v ≤ u := by
  intro j
  let w : JetVariable 3 → ℕ := Pi.single j 1
  have h : monomial u a ∈ restrictWeightAtMost w (u j) := by
    rw [monomial_mem_restrictWeightAtMost]
    exact Or.inl (by simp [w, Finsupp.weight_single_one_apply])
  have hh := globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _) x y h
  simpa only [w, Finsupp.weight_single_one_apply] using mem_restrictWeightAtMost.mp hh v hv

private theorem eligible_of_le {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : AnchorEligible u) : AnchorEligible v := by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hw (w : Fin 4 → ℕ) : v.some.weight w ≤ u.some.weight w := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right (w j) (h (some j))
  have ht : v.weight (differentialWeight 133634) ≤ u.weight (differentialWeight 133634) := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right (differentialWeight 133634 j) (h j)
  obtain ⟨hdeg, hi, hf, htail, hwgt⟩ := hu
  have hcap : 48 - (u.some.degree - 113 + 1) / 2 ≤ 48 - (v.some.degree - 113 + 1) / 2 := by
    omega
  refine ⟨hd.trans hdeg, (hw _).trans hi, (h _).trans hf, ?_, ht.trans hwgt⟩
  exact (add_le_add (add_le_add (h _) (h _)) (h _)).trans (htail.trans hcap)

theorem translate_mem_anchorSpace (x y : Geom) (Q : anchorSpace) :
    globalPointTranslation x y (Q : DifferentialPolynomial Geom 3) ∈ anchorSpace := by
  classical
  let f := globalPointTranslation (d := 3) x y
  change f (Q : DifferentialPolynomial Geom 3) ∈ anchorSpace
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  change globalPointTranslation x y (monomial u _) ∈
    restrictSupport Geom {v | AnchorEligible v}
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  exact eligible_of_le (exponent_le_of_mem_translation_monomial x y u v _ hv) (Q.property hu)

theorem rank_local_le_origin (x y : Geom) :
    Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
  have hpositive (j : JetVariable 3) : differentialWeight 133634 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133634 - j.val ≠ 0
      omega
  have : Module.Finite Geom anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let tr : anchorSpace →ₗ[Geom] anchorSpace :=
    ((globalPointTranslation x y).toLinearMap.domRestrict anchorSpace).codRestrict anchorSpace
      (translate_mem_anchorSpace x y)
  have h : anchorLocal x y = (anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 90 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 90 0 0 (globalPointTranslation x y Q)
    exact localConstraintAt_eq_zero_globalPointTranslation (d := 3) (m := 90) x y
      (Q : DifferentialPolynomial Geom 3)
  rw [h]
  exact LinearMap.finrank_range_comp_le_left (anchorLocal 0 0) tr

end

end K1_13_1_1
end PackSource_K1_13_1_1Translation

section PackSource_K1_14_2_3_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_2_3_2

noncomputable section

open K1_14 K1_14_2

/-- The image in the seed plane, cut by the same generic line as the root and
jet sections. -/
abbrev PlaneSeedSection (J : Ideal Seeds) :=
  CoordinateRing (J.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔
    Ideal.span {seedLine 0 1})

end

end K1_14_2_3_2
end PackSource_K1_14_2_3_2Defs
