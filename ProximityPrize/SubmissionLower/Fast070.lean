import ProximityPrize.SubmissionLower.Fast063
import ProximityPrize.SubmissionLower.Fast064
import ProximityPrize.SubmissionLower.Fast065
import ProximityPrize.SubmissionLower.Fast066
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_5_5_2_2_2
noncomputable section
open K1_13 K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_2 K1_13_7_6_1
open scoped TensorProduct nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
abbrev freshMap : CoeffRing →+* FreshCoeffRing :=
  MvPolynomial.map (algebraMap Geom FreshField)
private def quotientTensor (I : Ideal CoeffRing) :
    FreshField ⊗[Geom] (CoeffRing ⧸ I) ≃ₐ[FreshField] FreshCoeffRing ⧸ freshIdeal I := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := CoeffIndex) Geom FreshField
  let ι : CoeffRing →ₐ[Geom] FreshField ⊗[Geom] CoeffRing :=
    Algebra.TensorProduct.includeRight
  have hcomp : e.toRingHom.comp ι.toRingHom = freshMap := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[Geom] p) = _
    simp [e]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := Geom) FreshField _ FreshField I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  exact ((Ideal.map_map (I := I) ι.toRingHom e.toRingHom).trans
    (congrArg (fun f => I.map f) hcomp)).symm
theorem quotientTensor_one_tmul (I : Ideal CoeffRing) (p : CoeffRing) :
    quotientTensor I (1 ⊗ₜ[Geom] (Ideal.Quotient.mk I p)) =
      Ideal.Quotient.mk (freshIdeal I) (freshMap p) := by
  simp [quotientTensor]
theorem freshIdeal_cut (I : Ideal CoeffRing) (f : CoeffRing) :
    freshIdeal (cyclicCut I f) = cyclicCut (freshIdeal I) (freshMap f) := by
  simp [freshIdeal, cyclicCut, Ideal.map_sup, Ideal.map_span]
theorem freshIdeal_annihilator (I : Ideal CoeffRing) (f : CoeffRing) :
    freshIdeal (cyclicAnnihilator I f) = cyclicAnnihilator (freshIdeal I) (freshMap f) := by
  let A := cyclicAnnihilator I f
  have hA : ∀ x : CoeffRing, x * f ∈ I ↔ x ∈ A :=
    fun _ ↦ mem_cyclicAnnihilator.symm
  have hmul : freshIdeal A ≤ cyclicAnnihilator (freshIdeal I) (freshMap f) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change freshMap x ∈ cyclicAnnihilator (freshIdeal I) (freshMap f)
    rw [mem_cyclicAnnihilator, ← map_mul]
    exact Ideal.mem_map_of_mem freshMap ((hA x).mpr hx)
  let u : (FreshCoeffRing ⧸ freshIdeal A) →ₗ[FreshField] FreshCoeffRing ⧸ freshIdeal I :=
    ((freshIdeal A).restrictScalars FreshField).liftQ
      ((Ideal.Quotient.mkₐ FreshField (freshIdeal I)).toLinearMap ∘ₗ
        LinearMap.mulLeft FreshField (freshMap f)) (fun x hx ↦ by
          change Ideal.Quotient.mk (freshIdeal I) (freshMap f * x) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, mul_comm]
          exact mem_cyclicAnnihilator.mp (hmul hx))
  let v := factorMul (k := Geom) hA
  have hv : Function.Injective (v.baseChange FreshField) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap v (factorMul_injective hA)
  have hcompare (z : FreshField ⊗[Geom] (CoeffRing ⧸ A)) :
      u (quotientTensor A z) = quotientTensor I (v.baseChange FreshField z) := by
    induction z using TensorProduct.inductionOn with
    | tmul c q =>
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [show c ⊗ₜ[Geom] Ideal.Quotient.mk A p =
        c • (1 ⊗ₜ[Geom] Ideal.Quotient.mk A p) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      simp only [map_smul, quotientTensor_one_tmul, LinearMap.baseChange_tmul, v, factorMul_mk]
      congr 1
      change Ideal.Quotient.mk (freshIdeal I) (freshMap f * freshMap p) =
        Ideal.Quotient.mk (freshIdeal I) (freshMap (f * p))
      rw [map_mul freshMap]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hu : Function.Injective u := by
    intro x y hxy
    obtain ⟨z, rfl⟩ := (quotientTensor A).surjective x
    obtain ⟨w, rfl⟩ := (quotientTensor A).surjective y
    rw [hcompare, hcompare] at hxy
    exact congrArg (quotientTensor A) (hv ((quotientTensor I).injective hxy))
  refine le_antisymm hmul fun x hx ↦ ?_
  apply (Ideal.Quotient.eq_zero_iff_mem (I := freshIdeal A)).mp
  apply hu
  rw [map_zero]
  change Ideal.Quotient.mk (freshIdeal I) (freshMap f * x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, mul_comm]
  exact mem_cyclicAnnihilator.mp hx
set_option maxHeartbeats 1200000 in
theorem genericFiber_step (L : Fin 2 → FreshJetRing) (J : Ideal FreshCoeffRing)
    (a : FreshCoeffRing) (hfinite : Module.Finite PairField (genericFiber L J)) :
    Module.Finite PairField (genericFiber L (cyclicCut J a)) ∧
      genericFiberDimension L J =
        genericFiberDimension L (cyclicCut J a) +
          genericFiberDimension L (cyclicAnnihilator J a) := by
  let quotientModule (T : Ideal FreshCoeffRing) : Module PairRing (FreshCoeffRing ⧸ T) :=
    Module.compHom (FreshCoeffRing ⧸ T) (pairMap L T).toRingHom
  let Q := cyclicAnnihilator J a
  let T := cyclicCut J a
  have hA : ∀ x : FreshCoeffRing, x * a ∈ J ↔ x ∈ Q :=
    fun _ ↦ mem_cyclicAnnihilator.symm
  have hle : J ≤ T := le_cyclicCut J a
  let u : (FreshCoeffRing ⧸ Q) →ₗ[PairRing] FreshCoeffRing ⧸ J :=
    { (factorMul (k := FreshField) hA).toAddMonoidHom with
      map_smul' := fun r x ↦ by
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
        let b := freshProjection (MvPolynomial.aeval L r)
        change Ideal.Quotient.mk J (a * (b * p)) =
          Ideal.Quotient.mk J (b * (a * p))
        rw [mul_left_comm a b] }
  let v : (FreshCoeffRing ⧸ J) →ₗ[PairRing] FreshCoeffRing ⧸ T :=
    { (Ideal.Quotient.factor hle).toAddMonoidHom with
      map_smul' := fun r x ↦ by
        let b := freshProjection (MvPolynomial.aeval L r)
        change Ideal.Quotient.factor hle (Ideal.Quotient.mk J b * x) =
          Ideal.Quotient.mk T b * Ideal.Quotient.factor hle x
        rw [map_mul, Ideal.Quotient.factor_mk] }
  have hu : Function.Injective u := factorMul_injective (k := FreshField) hA
  have hv : Function.Surjective v := Ideal.Quotient.factor_surjective hle
  have huv : Function.Exact u v := factorMul_exact (k := FreshField) hA
  let : Module.Flat PairRing PairField :=
    IsLocalization.flat PairField (nonZeroDivisors PairRing)
  let u' := u.baseChange PairField
  let v' := v.baseChange PairField
  have hu' : Function.Injective u' := by
    dsimp only [u']
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap u hu
  have hv' : Function.Surjective v' := LinearMap.baseChange_surjective PairField hv
  have huv' : Function.Exact u' v' := by
    dsimp only [u', v']
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact PairField huv
  let : Module.Finite PairField (genericFiber L J) := hfinite
  let : Module.Finite PairField (genericFiber L Q) := Module.Finite.of_injective u' hu'
  let hT : Module.Finite PairField (genericFiber L T) := Module.Finite.of_surjective v' hv'
  refine ⟨hT, ?_⟩
  have h := Module.length_eq_add_of_exact u' v' hu' hv' huv'
  simpa only [Module.length_eq_finrank, ← ENat.natCast_add, ENat.natCast_inj, add_comm,
    genericFiberDimension] using h
theorem proof : K1_13_5_5_2_2.c2 := by
  intro I f L hfinite
  let P (J Q : Ideal FreshCoeffRing) : Prop :=
    Module.Finite PairField (genericFiber L J) ∧
      genericFiberDimension L (freshIdeal I) =
        genericFiberDimension L J + genericFiberDimension L Q
  change P (freshIdeal (cyclicCut I f)) (freshIdeal (cyclicAnnihilator I f))
  rw [freshIdeal_cut, freshIdeal_annihilator]
  exact genericFiber_step L (freshIdeal I) (freshMap f) hfinite
end
end K1_13_5_5_2_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_5_2_2_1
noncomputable section
open MvPolynomial K1_13_5_5_2_2
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]
theorem bounded_cyclic_rep {I : Ideal (MvPolynomial σ k)} {f p : MvPolynomial σ k}
    {d N : ℕ} (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (hf : f.IsHomogeneous d)
    (hdN : d ≤ N) (hp : p.totalDegree ≤ N) (hpJ : p ∈ cyclicCut I f) :
    ∃ q : MvPolynomial σ k, q.totalDegree ≤ N - d ∧
      Ideal.Quotient.mk I (f * q) = Ideal.Quotient.mk I p := by
  change p ∈ I ⊔ Ideal.span {f} at hpJ
  rw [sup_comm, Ideal.mem_span_singleton_sup] at hpJ
  obtain ⟨a, b, hb, heq⟩ := hpJ
  let q := ∑ i ∈ Finset.range (N - d + 1), homogeneousComponent i a
  have hq : q.totalDegree ≤ N - d := by
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi ↦ ?_)
    exact (homogeneousComponent_isHomogeneous i a).totalDegree_le.trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hq_component (e : ℕ) (he : e ≤ N - d) :
      homogeneousComponent e q = homogeneousComponent e a := by
    simp only [q, map_sum, homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous _ _)]
    rw [Finset.sum_eq_single_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_of_le he))]
    · rw [ite_eq_left rfl]
    · intro i _ hi
      exact ite_eq_right (Ne.symm hi)
  have hqf : (q * f).totalDegree ≤ N :=
    (totalDegree_mul _ _).trans (by have := hf.totalDegree_le; omega)
  have hdiff : p - q * f ∈ I := by
    apply (mem_iff_homogeneousComponent_mem hI _).mpr
    intro e
    rw [map_sub]
    by_cases he : e ≤ N
    · rw [← heq, map_add, K1_13_5_4_4_2.component_mul_homogeneous (p := a) hf,
        K1_13_5_4_4_2.component_mul_homogeneous (p := q) hf]
      have hb' := homogeneousComponent_mem_of_mem hI hb e
      by_cases hd : d ≤ e
      · simpa only [ite_eq_left hd, hq_component (e - d) (by omega), add_sub_cancel_left] using hb'
      · simpa only [ite_eq_right hd, zero_add, sub_zero] using hb'
    · rw [homogeneousComponent_eq_zero _ _ (by omega : p.totalDegree < e),
        homogeneousComponent_eq_zero _ _ (by omega : (q * f).totalDegree < e), sub_zero]
      exact I.zero_mem
  refine ⟨q, hq, ?_⟩
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
  rw [map_sub, sub_eq_zero] at h
  simpa only [mul_comm q f] using h.symm
theorem hilbertFunction_step_eq [Finite σ]
    {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k} {d N : ℕ}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (hf : f.IsHomogeneous d) (hdN : d ≤ N) :
    affineHilbertFunction I N =
      affineHilbertFunction (cyclicCut I f) N +
        affineHilbertFunction (cyclicAnnihilator I f) (N - d) := by
  let J := cyclicCut I f
  let Q := cyclicAnnihilator I f
  have hIJ : I ≤ J := le_cyclicCut I f
  have hann (x : MvPolynomial σ k) : x * f ∈ I ↔ x ∈ Q :=
    mem_cyclicAnnihilator.symm
  let π := ((Ideal.Quotient.factorₐ k hIJ).toLinearMap.domRestrict (quotientDegreeLE I N)).codRestrict
    (quotientDegreeLE J N) fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
      change Ideal.Quotient.factor hIJ x ∈ quotientDegreeLE J N
      rw [← hpx, Ideal.Quotient.factor_mk]
      exact mk_mem_quotientDegreeLE hp
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
  let μ := ((K1_13_7_6_1.factorMul (k := k) hann).domRestrict
    (quotientDegreeLE Q (N - d))).codRestrict (quotientDegreeLE I N) fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
      change K1_13_7_6_1.factorMul hann x ∈ quotientDegreeLE I N
      rw [← hpx, K1_13_7_6_1.factorMul_mk]
      exact mk_mem_quotientDegreeLE
        ((totalDegree_mul f p).trans (by have := hf.totalDegree_le; omega))
  have hker : ∀ x, μ x ∈ LinearMap.ker π := by
    intro x
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change Ideal.Quotient.factor hIJ (K1_13_7_6_1.factorMul (k := k) hann x) = 0
    exact (K1_13_7_6_1.factorMul_exact (k := k) hann _).mpr ⟨x, rfl⟩
  let μker := μ.codRestrict (LinearMap.ker π) hker
  have hμinj : Function.Injective μker := fun x y hxy ↦
    Subtype.ext (K1_13_7_6_1.factorMul_injective hann
      (congrArg (fun z ↦ (z.val.val : MvPolynomial σ k ⧸ I)) hxy))
  have hμsurj : Function.Surjective μker := by
    intro z
    obtain ⟨p, hp, hpz⟩ := mem_quotientDegreeLE.mp z.val.property
    have hpJ : p ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← Ideal.Quotient.factor_mk hIJ, hpz]
      exact congrArg (fun x : quotientDegreeLE J N ↦ x.val) (LinearMap.mem_ker.mp z.property)
    obtain ⟨q, hq, hqp⟩ := bounded_cyclic_rep hI hf hdN hp hpJ
    refine ⟨⟨Ideal.Quotient.mk Q q, mk_mem_quotientDegreeLE hq⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change K1_13_7_6_1.factorMul (k := k) hann (Ideal.Quotient.mk Q q) = z.val.val
    rw [K1_13_7_6_1.factorMul_mk, hqp, hpz]
  have hdim := (LinearEquiv.ofBijective μker ⟨hμinj, hμsurj⟩).finrank_eq
  have hrank := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, ← hdim] at hrank
  exact hrank.symm
theorem proof : K1_13_5_5_2_2.c1 := by
  intro I f d hI hf _ _
  obtain ⟨TJ, hTJ⟩ := exists_eval_affineHilbertPolynomial (cyclicCut I f)
  obtain ⟨TQ, hTQ⟩ := exists_eval_affineHilbertPolynomial (cyclicAnnihilator I f)
  symm
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := max TJ (TQ + d))
  intro N hN
  have hTQd := le_of_max_le_right hN
  have hdN : d ≤ N := by omega
  rw [Polynomial.eval_add, Polynomial.taylor_eval, ← sub_eq_add_neg, ← Nat.cast_sub hdN,
    hTJ N (le_of_max_le_left hN), hTQ (N - d) (by omega),
    hilbertFunction_step_eq hI hf hdN, Nat.cast_add]
end
end K1_13_5_5_2_2_1
end
section
set_option autoImplicit false
namespace K1_13_5_5_2_1_2
noncomputable section
open K1_13 K1_13_5_5_2_1
open scoped Polynomial
attribute [local instance] Polynomial.algebra in
theorem lift_polynomials {A : Type} [CommRing A] [IsDomain A]
    {I : Type} [Finite I] (g : I → (FractionRing A)[X]) :
    ∃ (a : A) (l : Localization.Away a →+* FractionRing A),
      a ≠ 0 ∧ Function.Injective l ∧
      l.comp (algebraMap A (Localization.Away a)) = algebraMap A (FractionRing A) ∧
      ∃ q : I → (Localization.Away a)[X], ∀ i, (q i).map l = g i := by
  classical
  let F := FractionRing A
  let M := nonZeroDivisors A
  let _ : IsLocalization (M.map (Polynomial.C : A →+* A[X])) F[X] :=
    Polynomial.isLocalization M F
  obtain ⟨⟨_, a, ha, rfl⟩, hclear⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (M.map (Polynomial.C : A →+* A[X])) g
  have ha0 := nonZeroDivisors.ne_zero ha
  let b : A →+* F := algebraMap A F
  have hb : Function.Injective b := IsFractionRing.injective A F
  have hunit : IsUnit (b a) := isUnit_iff_ne_zero.mpr (by
    simpa only [map_zero] using hb.ne ha0)
  let l : Localization.Away a →+* F := IsLocalization.Away.lift a hunit
  have hl : l.comp (algebraMap A (Localization.Away a)) = b :=
    IsLocalization.Away.lift_comp a hunit
  have hlinj : Function.Injective l := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers a) l]
    intro x y
    change algebraMap A (Localization.Away a) x = algebraMap A (Localization.Away a) y ↔
      (l.comp (algebraMap A (Localization.Away a))) x =
        (l.comp (algebraMap A (Localization.Away a))) y
    rw [hl, hb.eq_iff,
      (IsLocalization.injective (Localization.Away a)
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha0)).eq_iff]
  let z : Localization.Away a := IsLocalization.Away.invSelf a
  have hza : l z * b a = 1 := by
    have h := congrArg l (IsLocalization.Away.mul_invSelf (S := Localization.Away a) a)
    rw [map_mul, map_one] at h
    rwa [mul_comm, show l (algebraMap A (Localization.Away a) a) = b a from
      DFunLike.congr_fun hl a] at h
  refine ⟨a, l, ha0, hlinj, hl, ?_⟩
  have hpre (i : I) : ∃ q : (Localization.Away a)[X], q.map l = g i := by
    obtain ⟨r, hr⟩ := hclear i
    rw [Algebra.smul_def] at hr
    change r.map b = ((Polynomial.C a).map b) * g i at hr
    refine ⟨Polynomial.C z * r.map (algebraMap A (Localization.Away a)), ?_⟩
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hl, hr,
      Polynomial.map_C, ← mul_assoc, ← Polynomial.C_mul, hza, Polynomial.C_1, one_mul]
  choose q hq using hpre
  exact ⟨q, hq⟩
private theorem descend {A : Type} [CommRing A] [IsDomain A] {f : A[X]}
    (s : Factorization (f.map (algebraMap A (FractionRing A)))) :
    ∃ a : A, a ≠ 0 ∧
      Nonempty (Factorization (f.map (algebraMap A (Localization.Away a)))) := by
  classical
  let F := FractionRing A
  let I := Fin s.n
  let J := {ij : I × I // ij.1 ≠ ij.2} ⊕ I
  let left : J → I := Sum.elim (fun ij => ij.val.1) id
  let right : J → F[X] := Sum.elim (fun ij => s.factor ij.val.2)
    (fun i => (s.factor i).derivative)
  have hbez (j : J) : ∃ u v : F[X], u * s.factor (left j) + v * right j = 1 := by
    cases j with
    | inl ij => exact s.pairwise_coprime ij.property
    | inr i => exact s.derivative_coprime i
  choose u v huv using hbez
  let g : I ⊕ (J ⊕ J) → F[X] := Sum.elim s.factor (Sum.elim u v)
  obtain ⟨a, l, ha, hl, hcomp, lift, hlift⟩ := lift_polynomials g
  let q (i : I) := lift (Sum.inl i)
  let U (j : J) := lift (Sum.inr (Sum.inl j))
  let V (j : J) := lift (Sum.inr (Sum.inr j))
  have hq (i : I) : (q i).map l = s.factor i := hlift _
  have hU (j : J) : (U j).map l = u j := hlift _
  have hV (j : J) : (V j).map l = v j := hlift _
  refine ⟨a, ha, ⟨{
    n := s.n
    factor := q
    multiplicity := s.multiplicity
    product_eq := ?_
    monic := fun i => Polynomial.monic_of_injective hl (by rw [hq i]; exact s.monic i)
    multiplicity_bounds := s.multiplicity_bounds
    pairwise_coprime := ?_
    derivative_coprime := ?_ }⟩⟩
  · apply Polynomial.map_injective l hl
    rw [Polynomial.map_map, hcomp]
    simpa only [Polynomial.map_prod, Polynomial.map_pow, hq] using s.product_eq
  · intro i k hik
    let j : J := Sum.inl ⟨(i, k), hik⟩
    have hj : u j * s.factor i + v j * s.factor k = 1 := huv j
    refine ⟨U j, V j, Polynomial.map_injective l hl ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, hq, hU, hV] using hj
  · intro i
    let j : J := Sum.inr i
    have hj : u j * s.factor i + v j * (s.factor i).derivative = 1 := huv j
    refine ⟨U j, V j, Polynomial.map_injective l hl ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
      ← Polynomial.derivative_map, hq, hU, hV] using hj
theorem proof : K1_13_5_5_2_1.c2 := by
  intro A _ _ _ f hf hd
  let F := FractionRing A
  let b : A →+* F := algebraMap A F
  let geomToFrac := b.comp (algebraMap Geom A)
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  let _ : CharP F K1.p := charP_of_injective_ringHom geomToFrac.injective K1.p
  have hdeg : (f.map b).natDegree ≤ 133671 := Polynomial.natDegree_map_le.trans hd
  let s := K1_13_6_3_5_3.factorsOfMonic (p := K1.p) (hf.map b)
    (hdeg.trans_lt (by decide)) (by decide)
  apply descend (f := f)
  exact {
    n := s.count
    factor := s.factor
    multiplicity := s.multiplicity
    product_eq := s.product_eq
    monic := s.monic
    multiplicity_bounds := fun i => ⟨s.positive i, (s.le_degree i).trans hdeg⟩
    pairwise_coprime := fun _ _ hij => s.coprime _ _ hij
    derivative_coprime := s.separable }
end
end K1_13_5_5_2_1_2
end
section
namespace K1_13_5_5_2_1_6
noncomputable section
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1 MvPolynomial
open scoped Polynomial
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
theorem linearCoordinates_component {k : Type} [Field k]
    (e : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k)
    (he : ∀ i, (e (MvPolynomial.X i)).IsHomogeneous 1) (f : MvPolynomial (Fin 3) k) (n : ℕ) :
    homogeneousComponent n (e f) = e (homogeneousComponent n f) := by
  conv_lhs => rw [← sum_homogeneousComponent (φ := f), map_sum, map_sum]
  conv_rhs => rw [← sum_homogeneousComponent (φ := f), map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [homogeneousComponent_of_mem
    (linearCoordinates_homogeneous e he (homogeneousComponent_isHomogeneous i f)),
    homogeneousComponent_of_mem (homogeneousComponent_mem i f)]
  split_ifs <;> simp
private theorem jetEquation {k : Type} [Field k]
    (I : Ideal (MvPolynomial (Fin 3) k)) [I.IsPrime]
    (hI : ∀ {p}, p ∈ I → ∀ n, homogeneousComponent n p ∈ I)
    (L : Fin 2 → MvPolynomial (Fin 3) k) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hf : ((Ideal.Quotient.mkₐ k I).comp (aeval L)).Finite)
    (hi : Function.Injective ((Ideal.Quotient.mkₐ k I).comp (aeval L))) :
    ∃ p : MvPolynomial (Fin 3) k, p ≠ 0 ∧ I = Ideal.span {p} ∧
      p.totalDegree = mapFinrank (R := MvPolynomial (Fin 2) k) (S := MvPolynomial (Fin 3) k ⧸ I)
        ((Ideal.Quotient.mkₐ k I).comp (aeval L)).toRingHom := by
  classical
  let J := MvPolynomial (Fin 3) k
  let R := MvPolynomial (Fin 2) k
  let Q := J ⧸ I
  let mk : J →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  let g : R →ₐ[k] Q := mk.comp (aeval L)
  let a : Algebra R Q := g.toRingHom.toAlgebra
  letI : Algebra R Q := a
  letI : SMul R Q := a.toSMul
  letI : Module R Q := a.toModule
  haveI : Module.Finite R Q := hf
  haveI : FaithfulSMul R Q := (faithfulSMul_iff_algebraMap_injective R Q).mpr hi
  haveI : IsScalarTower k R Q :=
    IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  obtain ⟨e, heL, he⟩ := exists_linearCoordinates L hL (fun a b hab =>
    hi (congrArg mk hab))
  let F : J ≃ₐ[k] R[X] := finSuccEquiv k 2
  let z : Q := mk (e (MvPolynomial.X 0))
  let θ : R[X] →ₐ[R] Q := Polynomial.aeval z
  have hθ : (θ.restrictScalars k).comp F.toAlgHom = mk.comp e.toAlgHom := by
    apply algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change θ (finSuccEquiv k 2 (MvPolynomial.X 0)) = z
      rw [finSuccEquiv_X_zero]
      exact Polynomial.aeval_X z
    · change θ (finSuccEquiv k 2 (MvPolynomial.X j.succ)) = mk (e (MvPolynomial.X j.succ))
      rw [finSuccEquiv_X_succ, heL]
      change Polynomial.aeval z (Polynomial.C (MvPolynomial.X j)) = mk (L j)
      rw [Polynomial.aeval_C]
      change g (MvPolynomial.X j) = mk (L j)
      exact congrArg mk (MvPolynomial.aeval_X L j)
  have happly (p : J) : θ (F p) = mk (e p) := DFunLike.congr_fun hθ p
  have hmem (p : J) : θ (F p) = 0 ↔ e p ∈ I := by
    rw [happly]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective θ := by
    intro x
    have hmks : Function.Surjective mk := Ideal.Quotient.mk_surjective
    obtain ⟨y, hy⟩ := hmks x
    refine ⟨F (e.symm y), ?_⟩
    simpa only [happly, AlgEquiv.apply_symm_apply] using hy
  let P := minpoly R z
  have hInt : IsIntegral R z := IsIntegral.of_finite R z
  have hP : P.Monic := minpoly.monic hInt
  have hker : RingHom.ker θ.toRingHom = Ideal.span {P} := minpoly.ker_eval hInt
  let p := F.symm P
  have hp : p ≠ 0 := by
    intro h
    apply hP.ne_zero
    simpa only [p, AlgEquiv.apply_symm_apply, map_zero] using congrArg F h
  have hpI : e p ∈ I := (hmem p).mp (by
    simpa only [p, AlgEquiv.apply_symm_apply] using minpoly.aeval R z)
  have hgen : I = Ideal.span {e p} := by
    apply le_antisymm
    · intro f hf
      have hf' : θ (F (e.symm f)) = 0 := (hmem _).mpr (by simpa using hf)
      obtain ⟨t, ht⟩ := minpoly.isIntegrallyClosed_dvd hInt hf'
      refine Ideal.mem_span_singleton.mpr ⟨e (F.symm t), ?_⟩
      calc
        f = e (F.symm (F (e.symm f))) := by simp
        _ = e (F.symm (P * t)) := by rw [ht]
        _ = e p * e (F.symm t) := by simp only [p, map_mul]
    · exact (Ideal.span_singleton_le_iff_mem I).mpr hpI
  let n := P.natDegree
  let p' := homogeneousComponent n p
  have hp'I : e p' ∈ I := by
    rw [show e p' = homogeneousComponent n (e p) from (linearCoordinates_component e he p n).symm]
    exact hI hpI n
  have hlead : (F p').coeff n = 1 := by
    have hcoeff : (F p).coeff n = 1 := by
      simpa only [p, AlgEquiv.apply_symm_apply] using hP.coeff_natDegree
    ext a
    change ((finSuccEquiv k 2 p').coeff n).coeff a = (1 : R).coeff a
    rw [finSuccEquiv_coeff_coeff, show p' = homogeneousComponent n p from rfl,
      coeff_homogeneousComponent, ← finSuccEquiv_coeff_coeff, show
        finSuccEquiv k 2 p = F p from rfl, hcoeff]
    by_cases ha : a = 0
    · subst a
      simp [Finsupp.cons_zero_eq_single_zero]
    · simp [coeff_one, Ne.symm ha]
  have hdeg : (F p').natDegree ≤ n := by
    change (finSuccEquiv k 2 p').natDegree ≤ n
    rw [natDegree_finSuccEquiv]
    exact (degreeOf_le_totalDegree _ _).trans (homogeneousComponent_isHomogeneous n p).totalDegree_le
  have hP' : (F p').Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdeg hlead
  have hdvd : P ∣ F p' := minpoly.isIntegrallyClosed_dvd hInt ((hmem p').mpr hp'I)
  have hpp : p' = p := F.injective <| by
    rw [show F p = P from F.apply_symm_apply P]
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hP hP' hdvd hdeg
  have hhom : p.IsHomogeneous n := hpp ▸ homogeneousComponent_isHomogeneous n p
  have hep : e p ≠ 0 := by
    intro h
    apply hp
    apply e.injective
    rw [h, map_zero]
  have ht : (e p).totalDegree = n :=
    (linearCoordinates_homogeneous e he hhom).totalDegree hep
  let E : AdjoinRoot P ≃ₐ[R] Q :=
    (Ideal.quotientEquivAlgOfEq R hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have hr : mapFinrank (R := R) (S := Q) g.toRingHom = n :=
    E.symm.toLinearEquiv.finrank_eq.trans (AdjoinRoot.powerBasis' hP).finrank
  exact ⟨e p, hep, hgen, ht.trans hr.symm⟩
theorem pairRank_factor {A : Type} [CommRing A] [IsDomain A] [Algebra FreshField A]
    (d : Fin 3 → A) (L : Fin 2 → FreshJetRing) :
    pairRank (conePairMap d L) =
      mapFinrank (R := PairRing) (S := JetQuot d) (jetPairMap L (coneJetIdeal d)).toRingHom *
        mapFinrank (R := JetQuot d) (S := A[X]) (jetInclusion d).toRingHom := by
  let Q := JetQuot d
  let j : Q →ₐ[FreshField] A[X] := jetInclusion d
  let g : PairRing →ₐ[FreshField] Q := jetPairMap L (coneJetIdeal d)
  have hj : Function.Injective j := jetInclusion_injective d
  have hc := @pairRank_comp Q A[X]
    (inferInstanceAs (CommRing (JetQuot d))) (inferInstanceAs (CommRing A[X]))
    (inferInstanceAs (IsDomain A[X]))
    (inferInstanceAs (Algebra FreshField (JetQuot d))) (inferInstanceAs (Algebra FreshField A[X]))
    g j hj
  exact hc
theorem proof : K1_13_5_5_2_1.c6 := by
  intro A _ _ _ d L M hL hfin hM hi
  have hiM : Function.Injective (jetPairMap M (coneJetIdeal d)) :=
    fun p q hpq => hi (congrArg (jetInclusion d) hpq)
  have hiL := jetPairMap_injective hL hM hiM
  have hiL' : Function.Injective (conePairMap d L) := by
    rw [conePairMap_eq_comp]
    exact (jetInclusion_injective d).comp hiL
  haveI : (coneJetIdeal d).IsPrime := RingHom.ker_isPrime (coneJetMap d)
  obtain ⟨p, hp, hpI, hpR⟩ := jetEquation (coneJetIdeal d) (coneJetIdeal_component d)
    L hL.1 hL.2 hiL
  obtain ⟨q, hq, hqI, hqR⟩ := jetEquation (coneJetIdeal d) (coneJetIdeal_component d)
    M hM.1 hM.2 hiM
  have hassoc : Associated p q := Ideal.span_singleton_eq_span_singleton.mp (hpI.symm.trans hqI)
  obtain ⟨u, hu⟩ := hassoc
  have hdeg : q.totalDegree = p.totalDegree := by
    rw [← hu, totalDegree_mul_of_isDomain hp (Units.ne_zero u),
      (isUnit_iff_totalDegree_of_isReduced.mp u.isUnit).2, add_zero]
  have hrank : pairRank (conePairMap d M) = pairRank (conePairMap d L) := by
    rw [pairRank_factor, pairRank_factor]
    simp only [jetPairMap]
    rw [← hpR, ← hqR, hdeg]
  letI := hfin
  letI := pairFiber_nontrivial (conePairMap d L) hiL'
  have hpos : 0 < pairRank (conePairMap d M) := by
    rw [hrank]
    exact Module.finrank_pos
  exact ⟨FiniteDimensional.of_finrank_pos hpos, hrank⟩
end
end K1_13_5_5_2_1_6
end
section
namespace K1_13_1_1
open K1_13
open scoped BigOperators
noncomputable section
def c1 : Prop := PascalEntries
def c2 : Prop :=
  PascalEntries →
    ∀ (s : ℕ) (g : ℤ), s ≤ 120 → -48 ≤ g → g < 90 - (s : ℤ) →
      ∀ (b c : ℕ), b + c ≤ residualDegree s →
        Module.finrank Geom (LinearMap.range
          ((projectJet 2 c).comp ((projectJet 1 b).comp (blockMap s g)))) ≤
          lineBound (residualDegree s) (-g) (orderCutoff s g) b c
def c3 : Prop :=
  PascalEntries →
    ∀ (s : ℕ) (g : ℤ), s ≤ 120 → -48 ≤ g → g < 90 - (s : ℤ) →
      ∀ b ≤ residualDegree s,
        Module.finrank Geom (LinearMap.range ((projectJet 1 b).comp (blockMap s g))) ≤
          pairBound (residualDegree s) (-g) b
theorem rank_block_le_budget (h1 : c1) (h2 : c2) (h3 : c3) (s : ℕ) (g : ℤ)
    (hs : s ≤ 120) (hg : -48 ≤ g) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) ≤ blockBudget s g := by
  by_cases h : g < 90 - (s : ℤ)
  · have hP := rank_block_le_pascal s g h (h2 h1 s g hs hg h) (h3 h1 s g hs hg h)
    unfold blockBudget
    rw [ite_eq_left h]
    split
    · exact hP
    · exact le_min hP (rank_block_le_flag s g _)
  · rw [blockMap_eq_zero s g (le_of_not_gt h), LinearMap.range_zero, finrank_bot]
    exact Nat.zero_le _
theorem totalBudget_eq_sum :
    totalBudget = ∑ s : Fin 121, ∑ r : Fin 138, blockBudget s (offset r) := by
  rw [totalBudget, sumRange_eq_fin]
  apply Finset.sum_congr rfl
  intro s _
  rw [gradeBudget, sumRange_eq_fin]
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_1.c1 := by
  intro x y
  calc
    _ ≤ Module.finrank Geom (LinearMap.range (K1_13_1.anchorLocal 0 0)) :=
      rank_local_le_origin x y
    _ ≤ ∑ s : Fin 121, ∑ r : Fin 138,
        Module.finrank Geom (LinearMap.range (blockMap s (offset r))) := rank_origin_le_blocks
    _ ≤ ∑ s : Fin 121, ∑ r : Fin 138, blockBudget s (offset r) := by
      refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun r _ => ?_
      exact rank_block_le_budget h1 h2 h3 s (offset r) (Nat.le_of_lt_succ s.isLt)
        (by unfold offset; omega)
    _ = totalBudget := totalBudget_eq_sum.symm
    _ = 9199626 := totalBudget_eq
end
end K1_13_1_1
end
section
namespace K1_13_1_1_1
open K1_13 K1_13_1_1 MvPolynomial
open scoped BigOperators
noncomputable section
def visible (m : Fin 4 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![0, m 1, m 2, m 3]
@[simp] private theorem visible_apply (m : Fin 4 →₀ ℕ) (j : Fin 4) :
    visible m j = ![0, m 1, m 2, m 3] j := by simp [visible]
theorem monomial_four (m : Fin 4 →₀ ℕ) :
    (monomial m 1 : Form) = MvPolynomial.X 0 ^ m 0 * MvPolynomial.X 1 ^ m 1 *
      MvPolynomial.X 2 ^ m 2 * MvPolynomial.X 3 ^ m 3 := by
  rw [monic_monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
theorem backShift_monomial (m : Fin 4 →₀ ℕ) :
    backShift (monomial m 1) = valueForm ^ m 0 * monomial (visible m) 1 := by
  rw [monomial_four m, monomial_four (visible m)]
  simp [backShift_X_of_ne 1 (by decide), backShift_X_of_ne 2 (by decide),
    backShift_X_of_ne 3 (by decide), mul_assoc]
theorem coeff_valueForm_pow (d : Fin 4 →₀ ℕ) (n : ℕ) (h : d.degree = n) :
    (valueForm ^ n).coeff d = (d.multinomial : Geom) * (-1 : Geom) ^ d 2 := by
  have hv : valueForm =
      ∑ j : Fin 4, (![1, 1, -1, 1] : Fin 4 → Geom) j • MvPolynomial.X j := by
    simp [valueForm, Fin.sum_univ_four, sub_eq_add_neg, add_assoc]
  rw [hv, coeff_linearCombination_X_pow_of_fintype]
  change (if d.degree = n then _ else _) = _
  rw [ite_eq_left h, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
  simp
def factorialProduct (d : Fin 4 →₀ ℕ) : Geom :=
  ∏ j : Fin 4, ((d j).factorial : Geom)
theorem factorialProduct_ne_zero (d : Fin 4 →₀ ℕ) (h : d.degree ≤ 48) :
    factorialProduct d ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => factorial_cast_ne_zero ((Finsupp.le_degree j d).trans h)
theorem multinomial_factorials (d : Fin 4 →₀ ℕ) :
    (d.multinomial : Geom) * factorialProduct d = (d.degree.factorial : Geom) := by
  have h := congrArg (fun k : ℕ => (k : Geom)) (Nat.multinomial_spec Finset.univ d)
  rw [Nat.cast_mul, Nat.cast_prod, ← Finsupp.multinomial_eq_of_support_subset
    (Finset.subset_univ d.support), ← Finsupp.degree_eq_sum, mul_comm] at h
  exact h
theorem choose_factorials {n k : ℕ} (h : k ≤ n) :
    (n.choose k : Geom) * (k.factorial : Geom) * ((n - k).factorial : Geom) =
      (n.factorial : Geom) := by
  simpa only [Nat.cast_mul] using
    congrArg (fun a : ℕ => (a : Geom)) (Nat.choose_mul_factorial_mul_factorial h)
private theorem rescale (m e d : Fin 4 →₀ ℕ) (h : d + visible m = e)
    (hd : d.degree = m 0) (hm : m.degree ≤ 48) (he : e.degree ≤ 48) :
    (d.multinomial : Geom) * (-1 : Geom) ^ d 2 =
      pascalRowScale e * pascalColScale m *
        ((e 1).choose (m 1) : Geom) * ((e 2).choose (m 2) : Geom) *
          ((e 3).choose (m 3) : Geom) := by
  have coord (j : Fin 4) : d j + visible m j = e j :=
    congrArg (fun u : Fin 4 →₀ ℕ => u j) h
  have h0 : d 0 = e 0 := by simpa using coord 0
  have h1 : d 1 + m 1 = e 1 := by simpa using coord 1
  have h2 : d 2 + m 2 = e 2 := by simpa using coord 2
  have h3 : d 3 + m 3 = e 3 := by simpa using coord 3
  have fact {x y z : ℕ} (hx : z + y = x) :
      (x.factorial : Geom) = (x.choose y : Geom) * (y.factorial : Geom) *
        (z.factorial : Geom) := by
    have hc := choose_factorials (n := x) (k := y) (by omega)
    rw [show x - y = z by omega] at hc
    exact hc.symm
  have hsign : (-1 : Geom) ^ e 2 * (-1 : Geom) ^ m 2 = (-1 : Geom) ^ d 2 := by
    rw [← pow_add, ← h2, add_assoc, ← two_mul, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  have hmulti := multinomial_factorials d
  rw [hd] at hmulti
  change _ = (-1 : Geom) ^ e 2 / factorialProduct e *
    ((-1 : Geom) ^ m 2 * factorialProduct m) * _ * _ * _
  simp only [div_mul_eq_mul_div₀]
  apply (eq_div_iff (factorialProduct_ne_zero e he)).mpr
  have hsmall : d.degree ≤ 48 := by
    rw [hd]
    exact (Finsupp.le_degree 0 m).trans hm
  apply mul_right_cancel₀ (factorialProduct_ne_zero d hsmall)
  calc
    _ = (-1 : Geom) ^ d 2 *
        ((d.multinomial : Geom) * factorialProduct d) * factorialProduct e := by ac_rfl
    _ = (-1 : Geom) ^ d 2 * ((m 0).factorial : Geom) * factorialProduct e := by rw [hmulti]
    _ = _ := by
      rw [← hsign]
      simp only [factorialProduct, Fin.prod_univ_four]
      conv_lhs => rw [← h0, fact h1, fact h2, fact h3]
      ac_rfl
theorem proof : K1_13_1_1.c1 := by
  classical
  intro m e hdegree hm
  rw [backShift_monomial, coeff_mul_monomial']
  by_cases h : visible m ≤ e
  · rw [ite_eq_left h, mul_one]
    let d := e - visible m
    have hsum : d + visible m = e := tsub_add_cancel_of_le h
    have hd : d.degree = m 0 := by
      have ha : d.degree + (visible m).degree = e.degree := by rw [← map_add, hsum]
      rw [← hdegree, degree_formula m, degree_formula (visible m)] at ha
      simp at ha
      omega
    rw [coeff_valueForm_pow d _ hd]
    exact rescale m e d hsum hd hm (hdegree ▸ hm)
  · rw [ite_eq_right h]
    have hb : e 1 < m 1 ∨ e 2 < m 2 ∨ e 3 < m 3 := by
      by_contra! hn
      apply h
      intro j
      fin_cases j
      · simp
      · simpa using hn.1
      · simpa using hn.2.1
      · simpa using hn.2.2
    rcases hb with h1 | h2 | h3
    · simp [Nat.choose_eq_zero_of_lt h1]
    · simp [Nat.choose_eq_zero_of_lt h2]
    · simp [Nat.choose_eq_zero_of_lt h3]
end
end K1_13_1_1_1
end
section
namespace K1_13_1_1_2
open K1_13 K1_13_1_1 MvPolynomial
open scoped BigOperators
noncomputable section
private abbrev Exponent := Fin 4 →₀ ℕ
private abbrev Column (s : ℕ) (g : ℤ) :=
  {m : Exponent // BandExponent (residualDegree s) (-g) 48 10 m}
abbrev oldBasis (s : ℕ) (g : ℤ) :
    Module.Basis (Column s g) Geom (bandSpace (residualDegree s) (-g) 48 10) :=
  basisRestrictSupport Geom {m | BandExponent (residualDegree s) (-g) 48 10 m}
private abbrev lineMap (s : ℕ) (g : ℤ) (b c : ℕ) :=
  (projectJet 2 c).comp ((projectJet 1 b).comp (blockMap s g))
def colMin (g : ℤ) (b c : ℕ) : ℤ :=
  max 0 ((-g - b - 2 * (min c 24 : ℕ) + 2) / 3)
def colMax (s : ℕ) : ℤ := min (residualDegree s) 10
private def rowMin (s : ℕ) (g : ℤ) (b c : ℕ) : ℤ :=
  max (colMin g b c) (3 * (residualDegree s : ℤ) - 3 * b - 2 * c - orderCutoff s g + 1)
def rowMax (s b c : ℕ) : ℤ :=
  (residualDegree s : ℤ) - b - c
def lineRows (s : ℕ) (g : ℤ) (b c : ℕ) : Set Exponent :=
  {e | e.degree = residualDegree s ∧ e 1 = b ∧ e 2 = c ∧
    (e.weight targetOrder : ℤ) < orderCutoff s g ∧ colMin g b c ≤ (e 3 : ℤ)}
theorem lineRows_finite (s : ℕ) (g : ℤ) (b c : ℕ) :
    (lineRows s g b c).Finite :=
  (Finsupp.finite_of_degree_le (residualDegree s)).subset fun _ he => Nat.le_of_eq he.1
variable {s : ℕ} {g : ℤ} {b c : ℕ}
private theorem column_coeff (m : Column s g) (e : Exponent) :
    (lineMap s g b c (oldBasis s g m)).coeff e =
      if e 2 = c then
        if e 1 = b then
          if e.weight targetOrder < (orderCutoff s g).toNat then
            (backShift (monomial m.val 1)).coeff e
          else 0
        else 0
      else 0 := by
  change (filterSupport (fun x => x 2 = c) (filterSupport (fun x => x 1 = b)
    (weightedTruncation targetOrder (orderCutoff s g).toNat
      (backShift ↑(oldBasis s g m))))).coeff e = _
  have hmono : (oldBasis s g m : Form) = monomial m.val 1 :=
    coe_basisRestrictSupport_apply (R := Geom) _ m
  rw [coeff_filterSupport, coeff_filterSupport, coeff_weightedTruncation, hmono]
theorem column_data (m : Column s g) (e : Exponent)
    (hne : (lineMap s g b c (oldBasis s g m)).coeff e ≠ 0) :
    e.degree = residualDegree s ∧ e 1 = b ∧ e 2 = c ∧
      (e.weight targetOrder : ℤ) < orderCutoff s g := by
  rw [column_coeff] at hne
  split_ifs at hne with hc hb ho
  · have hm : m.val.weight (fun _ => (1 : ℕ)) = residualDegree s := by
      rw [← Finsupp.degree_eq_weight_one]
      exact m.property.1
    have hhom := backShift_homogeneous (isWeightedHomogeneous_monomial _ _ (1 : Geom) hm)
    have hd := hhom hne
    rw [← Finsupp.degree_eq_weight_one] at hd
    exact ⟨hd, hb, hc, by omega⟩
  all_goals contradiction
theorem pascal_coeff (hPascal : PascalEntries) (m : Column s g) (e : Exponent)
    (hd : e.degree = residualDegree s) (hb : e 1 = b) (hc : e 2 = c)
    (ho : (e.weight targetOrder : ℤ) < orderCutoff s g) :
    (lineMap s g b c (oldBasis s g m)).coeff e =
      pascalRowScale e * pascalColScale m.val * ((e 1).choose (m.val 1) : Geom) *
        ((e 2).choose (m.val 2) : Geom) * ((e 3).choose (m.val 3) : Geom) := by
  have hw : e.weight targetOrder < (orderCutoff s g).toNat := by omega
  rw [column_coeff, ite_eq_left hc, ite_eq_left hb, ite_eq_left hw]
  exact hPascal m.val e (m.property.1.trans hd.symm)
    (m.property.1.le.trans ((min_le_right _ _).trans (Nat.sub_le _ _)))
theorem col_lower_and_row (hPascal : PascalEntries) (m : Column s g) (e : Exponent)
    (hne : (lineMap s g b c (oldBasis s g m)).coeff e ≠ 0) :
    colMin g b c ≤ (m.val 3 : ℤ) ∧ e ∈ lineRows s g b c := by
  obtain ⟨hd, hb, hc, ho⟩ := column_data m e hne
  rw [pascal_coeff hPascal m e hd hb hc ho] at hne
  have h₁ : m.val 1 ≤ b := by
    by_contra! h
    simp [hb, Nat.choose_eq_zero_of_lt h] at hne
  have h₂ : m.val 2 ≤ c := by
    by_contra! h
    simp [hc, Nat.choose_eq_zero_of_lt h] at hne
  have h₃ : m.val 3 ≤ e 3 := by
    by_contra! h
    simp [Nat.choose_eq_zero_of_lt h] at hne
  have hlow := m.property.2.1
  have hhigh := m.property.2.2.1
  rw [jetIndex_formula] at hlow hhigh
  have hcap : m.val 2 ≤ min c 24 := by omega
  have hf : colMin g b c ≤ (m.val 3 : ℤ) := by
    unfold colMin
    omega
  exact ⟨hf, hd, hb, hc, ho, by omega⟩
def intervalIndex (lo hi : ℤ) (f : ℕ) (hl : lo ≤ (f : ℤ)) (hu : (f : ℤ) ≤ hi) :
    Fin (intervalSize lo hi) :=
  ⟨((f : ℤ) - lo).toNat, by unfold intervalSize; omega⟩
theorem intervalIndex_recover (lo hi : ℤ) (f : ℕ)
    (hl : lo ≤ (f : ℤ)) (hu : (f : ℤ) ≤ hi) :
    (lo + ((intervalIndex lo hi f hl hu).val : ℤ)).toNat = f := by
  change (lo + ((((f : ℤ) - lo).toNat : ℕ) : ℤ)).toNat = f
  omega
private theorem row_bounds (e : lineRows s g b c) :
    rowMin s g b c ≤ (e.val 3 : ℤ) ∧ (e.val 3 : ℤ) ≤ rowMax s b c := by
  obtain ⟨hd, hb, hc, ho, htop⟩ := e.property
  rw [degree_formula] at hd
  rw [targetOrder_formula] at ho
  refine ⟨max_le htop ?_, ?_⟩
  · omega
  · unfold rowMax
    omega
private def rowIndex (e : lineRows s g b c) :
    Fin (intervalSize (rowMin s g b c) (rowMax s b c)) :=
  intervalIndex _ _ (e.val 3) (row_bounds e).1 (row_bounds e).2
theorem rowIndex_injective :
    Function.Injective (rowIndex (s := s) (g := g) (b := b) (c := c)) := by
  intro e e' heq
  have hf : e.val 3 = e'.val 3 := by
    have hval := congrArg (fun i : Fin (intervalSize (rowMin s g b c) (rowMax s b c)) =>
      (rowMin s g b c + (i.val : ℤ)).toNat) heq
    simpa only [rowIndex, intervalIndex_recover] using hval
  obtain ⟨hd, hb, hc, _, _⟩ := e.property
  obtain ⟨hd', hb', hc', _, _⟩ := e'.property
  rw [degree_formula] at hd hd'
  apply Subtype.ext
  ext i
  fin_cases i
  · change e.val 0 = e'.val 0
    omega
  · exact hb.trans hb'.symm
  · exact hc.trans hc'.symm
  · exact hf
theorem range_le_of_basis {ι V : Type*} [AddCommGroup V] [Module Geom V]
    (B : Module.Basis ι Geom V) (φ : V →ₗ[Geom] Form) (S : Submodule Geom Form)
    (h : ∀ m, φ (B m) ∈ S) : LinearMap.range φ ≤ S := by
  rw [LinearMap.range_eq_map, ← B.span_eq, LinearMap.map_span_le]
  rintro _ ⟨m, rfl⟩
  exact h m
theorem rank_le_rows (hPascal : PascalEntries) (s : ℕ) (g : ℤ) (b c : ℕ) :
    Module.finrank Geom (LinearMap.range (lineMap s g b c)) ≤
      intervalSize (rowMin s g b c) (rowMax s b c) := by
  let : Fintype (lineRows s g b c) := (lineRows_finite s g b c).fintype
  let S := restrictSupport Geom (lineRows s g b c)
  let : Module.Finite Geom S := restrictSupport_finite (lineRows_finite s g b c)
  have hsub : LinearMap.range (lineMap s g b c) ≤ S := by
    apply range_le_of_basis (oldBasis s g)
    intro m
    apply (mem_restrictSupport_iff Geom).mpr
    intro e he
    exact (col_lower_and_row hPascal m e (mem_support_iff.mp he)).2
  calc
    _ ≤ Module.finrank Geom S := Submodule.finrank_mono hsub
    _ = Fintype.card (lineRows s g b c) :=
      Module.finrank_eq_card_basis (basisRestrictSupport Geom (lineRows s g b c))
    _ ≤ _ := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective _ (rowIndex_injective (s := s) (g := g) (b := b) (c := c))
def lineVector (s : ℕ) (g : ℤ) (b c : ℕ) [Fintype (lineRows s g b c)] (f : ℕ) :
    Form :=
  ∑ r : lineRows s g b c, monomial r.val (pascalRowScale r.val * ((r.val 3).choose f : Geom))
open scoped Classical in
theorem coeff_lineVector [Fintype (lineRows s g b c)] (f : ℕ) (e : Exponent) :
    (lineVector s g b c f).coeff e =
      if e ∈ lineRows s g b c then pascalRowScale e * ((e 3).choose f : Geom) else 0 := by
  classical
  simp only [lineVector, coeff_sum, coeff_monomial]
  by_cases he : e ∈ lineRows s g b c
  · let r : lineRows s g b c := ⟨e, he⟩
    rw [ite_eq_left he, Finset.sum_eq_single r]
    · simp [r]
    · intro r' _ hne
      have h : r'.val ≠ e := fun eq => hne (Subtype.ext eq)
      simp [h]
    · simp
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro r _
    have h : r.val ≠ e := fun eq => he (eq ▸ r.property)
    simp [h]
theorem column_eq_smul [Fintype (lineRows s g b c)] (hPascal : PascalEntries)
    (m : Column s g) :
    lineMap s g b c (oldBasis s g m) =
      (pascalColScale m.val * (b.choose (m.val 1) : Geom) * (c.choose (m.val 2) : Geom)) •
        lineVector s g b c (m.val 3) := by
  classical
  ext e
  rw [coeff_smul, coeff_lineVector]
  by_cases he : e ∈ lineRows s g b c
  · rw [ite_eq_left he]
    obtain ⟨hd, hb, hc, ho, _⟩ := he
    rw [pascal_coeff hPascal m e hd hb hc ho, hb, hc]
    rw [smul_eq_mul]
    ac_rfl
  · rw [ite_eq_right he, smul_zero]
    by_contra hne
    exact he (col_lower_and_row hPascal m e hne).2
theorem rank_le_columns (hPascal : PascalEntries) (s : ℕ) (g : ℤ) (b c : ℕ) :
    Module.finrank Geom (LinearMap.range (lineMap s g b c)) ≤
      intervalSize (colMin g b c) (colMax s) := by
  let : Fintype (lineRows s g b c) := (lineRows_finite s g b c).fintype
  let v : Fin (intervalSize (colMin g b c) (colMax s)) → Form := fun i =>
    lineVector s g b c ((colMin g b c + (i.val : ℤ)).toNat)
  let S := Submodule.span Geom (Set.range v)
  let : Module.Finite Geom S := Module.Finite.span_of_finite Geom (Set.finite_range v)
  have hsub : LinearMap.range (lineMap s g b c) ≤ S := by
    apply range_le_of_basis (oldBasis s g)
    intro m
    by_cases hlo : colMin g b c ≤ (m.val 3 : ℤ)
    · have hdeg := (Finsupp.le_degree 3 m.val).trans_eq m.property.1
      have htop := m.property.2.2.2
      have hhi : (m.val 3 : ℤ) ≤ colMax s := by unfold colMax; omega
      let i := intervalIndex (colMin g b c) (colMax s) (m.val 3) hlo hhi
      rw [column_eq_smul hPascal]
      apply S.smul_mem
      apply Submodule.subset_span
      exact ⟨i, congrArg (lineVector s g b c) (intervalIndex_recover _ _ _ hlo hhi)⟩
    · have hz : lineMap s g b c (oldBasis s g m) = 0 := by
        ext e
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        by_contra hne
        exact hlo (col_lower_and_row hPascal m e hne).1
      rw [hz]
      exact S.zero_mem
  refine (Submodule.finrank_mono hsub).trans ?_
  simpa only [S, Set.finrank, Fintype.card_fin] using finrank_range_le_card (R := Geom) v
theorem proof : K1_13_1_1.c2 := by
  intro hPascal s g _ _ _ b c _
  exact le_min (rank_le_columns hPascal s g b c) (rank_le_rows hPascal s g b c)
end
end K1_13_1_1_2
end
section
namespace K1_13_1_1_3
open K1_13 K1_13_1_1 MvPolynomial
noncomputable section
def pairLower (lo : ℤ) (b f : ℕ) : ℤ :=
  max 0 ((lo - b - 3 * f + 1) / 2)
def pairUpper (d f : ℕ) : ℤ :=
  min ((d : ℤ) - f) ((48 - 3 * f) / 2)
abbrev PairSlots (d : ℕ) (lo : ℤ) (b : ℕ) :=
  Σ f : Fin (min d 10 + 1), Fin (intervalSize (pairLower lo b f) (pairUpper d f))
def pairSecond {d : ℕ} {lo : ℤ} {b : ℕ} (p : PairSlots d lo b) : ℕ :=
  (pairLower lo b p.1).toNat + p.2.val
theorem card_pairSlots (d : ℕ) (lo : ℤ) (b : ℕ) :
    Fintype.card (PairSlots d lo b) = pairBound d lo b := by
  calc
    _ = ∑ f : Fin (min d 10 + 1), Fintype.card
        (Fin (intervalSize (pairLower lo b f) (pairUpper d f))) := Fintype.card_sigma
    _ = _ := by
      rw [pairBound, sumRange_eq_fin]
      exact Finset.sum_congr rfl fun f _ => Fintype.card_fin _
theorem exists_pairSlot {d : ℕ} {lo : ℤ} {b : ℕ} {m : Fin 4 →₀ ℕ}
    (hm : BandExponent d lo 48 10 m) (hb : m 1 ≤ b) :
    ∃ p : PairSlots d lo b, pairSecond p = m 2 ∧ p.1.val = m 3 := by
  obtain ⟨hdeg, hlo, hhi, htop⟩ := hm
  rw [degree_formula] at hdeg
  rw [jetIndex_formula] at hlo hhi
  have hf : m 3 < min d 10 + 1 := by omega
  let lower := pairLower lo b (m 3)
  let upper := pairUpper d (m 3)
  have hnonneg : 0 ≤ lower := le_max_left _ _
  have hlower : lower ≤ (m 2 : ℤ) := by
    dsimp only [lower, pairLower]
    omega
  have hupper : (m 2 : ℤ) ≤ upper := by
    dsimp only [upper, pairUpper]
    omega
  let offset := m 2 - lower.toNat
  have hfit : offset < intervalSize lower upper := by
    dsimp only [offset, intervalSize]
    omega
  refine ⟨⟨⟨m 3, hf⟩, ⟨offset, hfit⟩⟩, ?_, rfl⟩
  change lower.toNat + offset = m 2
  dsimp only [offset]
  omega
def sliceColumn (d b cutoff c f : ℕ) : Form := by
  classical
  refine AddMonoidAlgebra.ofCoeff (Finsupp.onFinset
    (Finsupp.finite_of_degree_le (σ := Fin 4) d).toFinset
    (fun e => if e.degree = d ∧ e 1 = b ∧ e.weight targetOrder < cutoff then
      pascalRowScale e * ((e 2).choose c : Geom) * ((e 3).choose f : Geom) else 0) ?_)
  intro e h
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  by_cases he : e.degree = d
  · exact he.le
  · simp [he] at h
theorem coeff_sliceColumn (d b cutoff c f : ℕ) (e : Fin 4 →₀ ℕ) :
    (sliceColumn d b cutoff c f).coeff e =
      if e.degree = d ∧ e 1 = b ∧ e.weight targetOrder < cutoff then
        pascalRowScale e * ((e 2).choose c : Geom) * ((e 3).choose f : Geom) else 0 := by
  rfl
private theorem project_monomial (hPascal : PascalEntries) {d : ℕ}
    (hd : d ≤ 48) (b cutoff : ℕ) (m : Fin 4 →₀ ℕ) (hm : m.degree = d) :
    projectJet 1 b (weightedTruncation targetOrder cutoff (backShift (monomial m 1))) =
      (pascalColScale m * (b.choose (m 1) : Geom)) • sliceColumn d b cutoff (m 2) (m 3) := by
  apply MvPolynomial.ext
  intro e
  change (filterSupport (fun t : Fin 4 →₀ ℕ => t 1 = b)
    (weightedTruncation targetOrder cutoff (backShift (monomial m 1)))).coeff e = _
  rw [coeff_filterSupport, coeff_weightedTruncation, coeff_smul, coeff_sliceColumn]
  by_cases he : e.degree = d
  · by_cases hb : e 1 = b
    · by_cases hcut : e.weight targetOrder < cutoff
      · rw [ite_eq_left hb, ite_eq_left hcut, ite_eq_left ⟨he, hb, hcut⟩,
          hPascal m e (hm.trans he.symm) (hm.trans_le hd), hb, smul_eq_mul]
        ac_rfl
      · simp [he, hb, hcut]
    · simp [hb]
  · have hhom : (monomial m (1 : Geom)).IsWeightedHomogeneous (fun _ => (1 : ℕ)) d := by
      apply isWeightedHomogeneous_monomial
      rwa [← Finsupp.degree_eq_weight_one]
    have hzero : (backShift (monomial m 1)).coeff e = 0 := by
      by_contra hne
      have hdeg := backShift_homogeneous hhom hne
      rw [← Finsupp.degree_eq_weight_one] at hdeg
      exact he hdeg
    simp [he, hzero]
theorem proof : K1_13_1_1.c3 := by
  classical
  intro hPascal s g _ _ _ b _
  let d := residualDegree s
  let cutoff := (orderCutoff s g).toNat
  let B := bandSpace d (-g) 48 10
  let φ : B →ₗ[Geom] Form := (projectJet 1 b).comp (blockMap s g)
  let basis : Module.Basis {m | BandExponent d (-g) 48 10 m} Geom B :=
    basisRestrictSupport Geom _
  let column (p : PairSlots d (-g) b) := sliceColumn d b cutoff (pairSecond p) p.1.val
  have hd : d ≤ 48 := (min_le_right _ _).trans (Nat.sub_le _ _)
  have hspan : LinearMap.range φ ≤ Submodule.span Geom (Set.range column) := by
    have htop : (⊤ : Submodule Geom B) = Submodule.span Geom (Set.range basis) :=
      basis.span_eq.symm
    rw [← Submodule.map_top, htop, Submodule.map_span_le]
    rintro _ ⟨m, rfl⟩
    change projectJet 1 b (weightedTruncation targetOrder cutoff
      (backShift (↑(basis m) : Form))) ∈ _
    rw [show (↑(basis m) : Form) = monomial m.val 1 from coe_basisRestrictSupport_apply _ _,
      project_monomial hPascal hd b cutoff m.val m.property.1]
    by_cases hb : m.val 1 ≤ b
    · obtain ⟨p, hp₂, hp₃⟩ := exists_pairSlot m.property hb
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨p, by simp only [column, hp₂, hp₃]⟩
    · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hb)]
  have : Module.Finite Geom (Submodule.span Geom (Set.range column)) :=
    Module.Finite.span_of_finite _ (Set.finite_range column)
  exact (Submodule.finrank_mono hspan).trans
    ((finrank_range_le_card (R := Geom) column).trans_eq (card_pairSlots d (-g) b))
end
end K1_13_1_1_3
end
section
namespace K1_13_7_5_3_3
noncomputable section
open K1_13 K1_13_7_5 K1_13_7_5_3 K1_13_7_4_2 MvPolynomial
open K1_13_5_4_2_4 hiding capSupport
open scoped BigOperators Pointwise
@[simp] theorem mem_doubledSupport {s : Shape} {a : Exponent} :
    a ∈ doubledSupport s ↔ Fits (s.scale 2) a :=
  Set.Finite.mem_toFinset _
theorem fits_supported {s : Shape} {f : Jets} (h : Supported s f) {a : Exponent}
    (ha : a ∈ f.support) : Fits s a := by
  obtain ⟨hb, hj, ht⟩ := h a ha
  rw [Finsupp.sum_fintype a (fun _ n => n) (fun _ => rfl)] at hb
  rw [Finsupp.sum_fintype a (fun i n => i.val * n) (fun _ => Nat.mul_zero _)] at hj
  exact ⟨hb, hj, ht⟩
theorem zero_mem_doubledSupport (s : Shape) : 0 ∈ doubledSupport s := by
  simp [Fits]
theorem single_mem_doubledSupport {s : Shape} (hc : K1_13_7_1.Chamber s)
    (ht : 0 < s.t) (j : Fin 4) : Finsupp.single j 1 ∈ doubledSupport s := by
  have hb : 3 ≤ s.b := by have := hc.1; have := hc.2; omega
  have hj : 3 ≤ s.j := by have := hc.2; omega
  have hj' : j.val ≤ 3 := by omega
  rw [mem_doubledSupport]
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finsupp.single_apply, Shape.scale] using (show 1 ≤ 2 * s.b by omega)
  · simpa [Finsupp.single_apply, Shape.scale, mul_ite] using
      (show j.val ≤ 2 * s.j by omega)
  · by_cases h : j = 3
    · subst j
      simpa [Shape.scale] using (show 1 ≤ 2 * s.t by omega)
    · simp [h, Shape.scale]
theorem sq_support_subset {s : Shape} {f : Jets} (h : Supported s f) :
    (f ^ 2).support ⊆ doubledSupport s := by
  classical
  intro e he
  rw [pow_two] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul f f he)
  obtain ⟨ha₀, ha₁, ha₃⟩ := fits_supported h ha
  obtain ⟨hb₀, hb₁, hb₃⟩ := fits_supported h hb
  rw [mem_doubledSupport]
  refine ⟨?_, ?_, ?_⟩
  · simpa [Shape.scale, Finsupp.add_apply, Finset.sum_add_distrib, two_mul] using
      Nat.add_le_add ha₀ hb₀
  · simpa [Shape.scale, Finsupp.add_apply, mul_add, Finset.sum_add_distrib, two_mul] using
      Nat.add_le_add ha₁ hb₁
  · simpa [Shape.scale, Finsupp.add_apply, two_mul] using Nat.add_le_add ha₃ hb₃
theorem cutIdeal_vec (F G L D : Jets) :
    K1_13_5_4_2_4.cutIdeal (![F, G, L, D] : Fin 4 → Jets) =
      K1_13_7_5_3.cutIdeal (Ideal.span {F, G, L}) D := by
  unfold K1_13_5_4_2_4.cutIdeal K1_13_7_5_3.cutIdeal
  rw [← Ideal.span_union]
  congr 1
  ext f
  simp [or_left_comm, or_comm]
theorem pointIdeal_eq (y : JetPoint) :
    K1_13_5_4_2.pointIdeal y = jetPointIdeal y := by
  ext f
  exact (mem_vanishingIdeal_singleton_iff y f).trans RingHom.mem_ker.symm
theorem pointLength_eq (J : Ideal Jets) (y : JetPoint) :
    K1_13_5_4_2.pointLength J y = liftLength (pointPrime y) J := by
  let r : PrimeSpectrum Jets := ⟨K1_13_5_4_2.pointIdeal y, inferInstance⟩
  change liftLength r J = liftLength (pointPrime y) J
  rw [show r = pointPrime y from PrimeSpectrum.ext (pointIdeal_eq y)]
theorem point_radical {J : Ideal Jets} {y : JetPoint}
    (h : jetPointIdeal y ∈ J.minimalPrimes) :
    (J.map (algebraMap Jets (PointLocal y))).radical =
      IsLocalRing.maximalIdeal (PointLocal y) := by
  rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (PointLocal y) (pointPrime y).asIdeal J h, Localization.AtPrime.map_eq_maximalIdeal]
theorem pointLength_ne_top {J : Ideal Jets} {y : JetPoint}
    (h : jetPointIdeal y ∈ J.minimalPrimes) :
    liftLength (pointPrime y) J ≠ ⊤ := by
  let R := PointLocal y
  let I := J.map (algebraMap Jets R)
  have hmin : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, point_radical h]
    exact ⟨⟨inferInstance, le_rfl⟩, fun _ hP _ => hP.2⟩
  let : IsArtinianRing (R ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  change Module.length R (R ⧸ I) ≠ ⊤
  rw [Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective (I := I))]
  exact Module.length_ne_top_iff.mpr ((isArtinianRing_iff_isFiniteLength (R ⧸ I)).mp inferInstance)
theorem squared_isolated {f : Fin 4 → Jets} {y : JetPoint}
    (h : jetPointIdeal y ∈ (K1_13_5_4_2_4.cutIdeal f).minimalPrimes) :
    jetPointIdeal y ∈ (K1_13_5_4_2_4.cutIdeal (fun i => f i ^ 2)).minimalPrimes := by
  simpa only [K1_13_5_4_2_4.cutIdeal, ← Ideal.radical_minimalPrimes
    (I := Ideal.span (Set.range fun i => f i ^ 2)),
    radical_span_powers f (fun _ => 2) (fun _ => by decide), Ideal.radical_minimalPrimes] using h
theorem squared_length {f : Fin 4 → Jets} {y : JetPoint}
    (h : jetPointIdeal y ∈ (K1_13_5_4_2_4.cutIdeal f).minimalPrimes)
    (hreg : ∀ (g : Fin 4 → PointLocal y),
      (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal (PointLocal y) →
      ∀ i x, g i * x ∈ remainingIdeal g i → x ∈ remainingIdeal g i) :
    liftLength (pointPrime y) (K1_13_5_4_2_4.cutIdeal (fun i => f i ^ 2)) =
      16 * liftLength (pointPrime y) (K1_13_5_4_2_4.cutIdeal f) := by
  let R := PointLocal y
  let a : Fin 4 → R := fun i => algebraMap Jets R (f i)
  have hmap (g : Fin 4 → Jets) :
      (K1_13_5_4_2_4.cutIdeal g).map (algebraMap Jets R) =
        Ideal.span (Set.range fun i => algebraMap Jets R (g i)) := by
    rw [K1_13_5_4_2_4.cutIdeal, Ideal.map_span, ← Set.range_comp]
    rfl
  have hrad : (Ideal.span (Set.range a)).radical = IsLocalRing.maximalIdeal R := by
    rw [← hmap f]
    exact point_radical h
  have hcancel (e : Fin 4 → ℕ) (he : ∀ j, 0 < e j) (i : Fin 4) (x : R)
      (hx : a i * x ∈ remainingIdeal (fun j => a j ^ e j) i) :
      x ∈ remainingIdeal (fun j => a j ^ e j) i := by
    let d (j : Fin 4) : ℕ := if j = i then 1 else e j
    let g (j : Fin 4) : R := a j ^ d j
    have hd (j : Fin 4) : 0 < d j := by by_cases hj : j = i <;> simp [d, hj, he j]
    have hg : (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal R :=
      (radical_span_powers a d hd).trans hrad
    have hgi : g i = a i := by simp [g, d]
    have hr : remainingIdeal g i = remainingIdeal (fun j => a j ^ e j) i := by
      unfold remainingIdeal
      congr 1
      exact Set.image_congr fun j hj => by
        have hji : j ≠ i := hj
        simp [g, d, hji]
    rw [← hr] at hx ⊢
    exact hreg g hg i x (by simpa only [hgi] using hx)
  have hp := power_colength a (fun _ => 2) (fun _ => by decide) hcancel
  change colength ((K1_13_5_4_2_4.cutIdeal (fun i => f i ^ 2)).map (algebraMap Jets R)) =
    16 * colength ((K1_13_5_4_2_4.cutIdeal f).map (algebraMap Jets R))
  rw [hmap, hmap]
  simpa only [map_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_ofNat, show 2 ^ 4 = (16 : ℕ) by decide] using hp
theorem last_not_mem_vars {s : Shape} {F : Jets} (ht : s.t = 0)
    (hF : Supported s F) : (3 : Fin 4) ∉ F.vars := by
  intro h
  obtain ⟨a, ha, hav⟩ := (mem_vars_iff_mem_support _).mp h
  exact (Finsupp.mem_support_iff.mp hav) (Nat.eq_zero_of_le_zero (ht ▸ (hF a ha).2.2))
theorem not_isolated_without_last {f : Fin 4 → Jets} {s : Fin 4 → Shape}
    (ht : ∀ i, (s i).t = 0) (hf : ∀ i, Supported (s i) (f i)) (y : JetPoint) :
    jetPointIdeal y ∉ (K1_13_5_4_2_4.cutIdeal f).minimalPrimes := by
  classical
  intro h
  let φ : Jets →+* Polynomial K1_13_5_4.GeometricX :=
    eval₂Hom Polynomial.C (fun j => if j = 3 then Polynomial.X else Polynomial.C (y j))
  have hφ : (Polynomial.evalRingHom (y 3)).comp φ = eval y := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [φ]
    · intro j
      by_cases hj : j = 3 <;> simp [φ, hj]
  have hle : RingHom.ker φ ≤ jetPointIdeal y := by
    intro z hz
    change eval y z = 0
    rw [← hφ, RingHom.comp_apply, RingHom.mem_ker.mp hz, map_zero]
  have hfφ : K1_13_5_4_2_4.cutIdeal f ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hz := RingHom.mem_ker.mp (h.le (Ideal.subset_span (Set.mem_range_self i)))
    change φ (f i) = 0
    have heq : φ (f i) = Polynomial.C (eval y (f i)) := by
      apply hom_congr_vars (f₂ := Polynomial.C.comp (eval y)) _ _ rfl
      · ext c
        simp [φ]
      · intro j hj _
        have hj' : j ≠ 3 := fun e => last_not_mem_vars (ht i) (hf i) (e ▸ hj)
        simp [φ, hj']
    rw [heq, hz, map_zero]
  have heq : RingHom.ker φ = jetPointIdeal y :=
    hle.antisymm (h.2 ⟨RingHom.ker_isPrime φ, hfφ⟩ hle)
  have hx : MvPolynomial.X (3 : Fin 4) - MvPolynomial.C (y 3) ∈ jetPointIdeal y := by
    change eval y (MvPolynomial.X 3 - MvPolynomial.C (y 3)) = 0
    simp
  rw [← heq] at hx
  have hn := RingHom.mem_ker.mp hx
  exact Polynomial.X_sub_C_ne_zero (y 3) (by simpa [φ, map_sub] using hn)
end
end K1_13_7_5_3_3
end
section
namespace K1_13_7_5_3_3
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_5_3
open K1_13_5_4_2_4 (exponentVector latticeBody)
open MeasureTheory
open scoped BigOperators Pointwise
theorem mem_body (s : Shape) (x : RealJets) :
    x ∈ capBody s ↔ (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 ≤ s.b ∧
      x 1 + 2 * x 2 + 3 * x 3 ≤ s.j ∧ x 3 ≤ s.t := by
  norm_num [capBody, Fin.sum_univ_four]
theorem convex_body (s : Shape) : Convex ℝ (capBody s) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx, hxb, hxj, hxt⟩ := (mem_body s x).mp hx
  obtain ⟨hy, hyb, hyj, hyt⟩ := (mem_body s y).mp hy
  apply (mem_body s _).mpr
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)), ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hxb ha, mul_le_mul_of_nonneg_left hyb hb,
      congrArg (fun t : ℝ => t * s.b) hab]
  · nlinarith [mul_le_mul_of_nonneg_left hxj ha, mul_le_mul_of_nonneg_left hyj hb,
      congrArg (fun t : ℝ => t * s.j) hab]
  · nlinarith [mul_le_mul_of_nonneg_left hxt ha, mul_le_mul_of_nonneg_left hyt hb,
      congrArg (fun t : ℝ => t * s.t) hab]
private def param (s : Shape) (u : Fin 4 → ℝ) : RealJets :=
  let z := u 3 * s.t
  let x₂ := u 2 * ((s.j : ℝ) - 3 * z)
  let x₁ := u 1 * (2 * ((s.j : ℝ) - 3 * z) - 2 * x₂)
  ![u 0 * (2 * (s.b : ℝ) - x₁ - x₂ - 2 * z), x₁, x₂, 2 * z]
theorem param_update (s : Shape) (u : Fin 4 → ℝ) (i : Fin 4) :
    param s u = (1 - u i) • param s (Function.update u i 0) +
      u i • param s (Function.update u i 1) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [param, Pi.add_apply, smul_eq_mul, Function.update] <;> ring
theorem corner_mem (s : Shape) (hs : Chamber s) (u : Fin 4 → ℝ)
    (hu : ∀ i, u i = 0 ∨ u i = 1) : param s u ∈ latticeBody (doubledSupport s) := by
  have hbinary (i : Fin 4) : ∃ v : ℕ, (v : ℝ) = u i ∧ v ≤ 1 := by
    rcases hu i with hi | hi
    · exact ⟨0, by simpa using hi.symm, zero_le_one⟩
    · exact ⟨1, by simpa using hi.symm, le_rfl⟩
  choose v hv using hbinary
  let z := v 3 * s.t
  let r := s.j - 3 * z
  let x₂ := v 2 * r
  let x₁ := v 1 * (2 * r - 2 * x₂)
  have hz : z ≤ s.t := by simpa [z] using Nat.mul_le_mul_right s.t (hv 3).2
  have hzr : 3 * z ≤ s.j := (Nat.mul_le_mul_left _ hz).trans hs.2
  have h₂ : x₂ ≤ r := by simpa [x₂] using Nat.mul_le_mul_right r (hv 2).2
  have h₂' : 2 * x₂ ≤ 2 * r := Nat.mul_le_mul_left _ h₂
  have h₁ : x₁ ≤ 2 * r - 2 * x₂ := by
    simpa [x₁] using Nat.mul_le_mul_right (2 * r - 2 * x₂) (hv 1).2
  have hindex : x₁ + 2 * x₂ + 3 * (2 * z) ≤ 2 * s.j := by dsimp only [r] at *; omega
  have hsum : x₁ + x₂ + 2 * z ≤ 2 * s.b := by have := hs.1; omega
  let x₀ := v 0 * (2 * s.b - (x₁ + x₂ + 2 * z))
  have h₀ : x₀ ≤ 2 * s.b - (x₁ + x₂ + 2 * z) := by
    simpa [x₀] using Nat.mul_le_mul_right (2 * s.b - (x₁ + x₂ + 2 * z)) (hv 0).2
  let w : Fin 4 → ℕ := ![x₀, x₁, x₂, 2 * z]
  let e : Exponent := Finsupp.equivFunOnFinite.symm w
  have he (i : Fin 4) : e i = w i :=
    congrFun (Finsupp.equivFunOnFinite.apply_symm_apply w) i
  apply subset_convexHull ℝ _
  refine ⟨e, mem_doubledSupport.mpr ?_, ?_⟩
  · simp only [Fits, Fin.sum_univ_four, he, w, Matrix.cons_val_zero,
      Shape.scale, Fin.val_zero, Nat.zero_mul, zero_add]
    change x₀ + x₁ + x₂ + 2 * z ≤ 2 * s.b ∧
      1 * x₁ + 2 * x₂ + 3 * (2 * z) ≤ 2 * s.j ∧ 2 * z ≤ 2 * s.t
    omega
  · have hz' : (z : ℝ) = u 3 * s.t := by simp only [z, Nat.cast_mul, (hv 3).1]
    have hr' : (r : ℝ) = s.j - 3 * (u 3 * s.t) := by
      simp only [r, Nat.cast_sub hzr, Nat.cast_mul, Nat.cast_ofNat, hz']
    have h₂' : (x₂ : ℝ) = u 2 * (s.j - 3 * (u 3 * s.t)) := by
      simp only [x₂, Nat.cast_mul, (hv 2).1, hr']
    have h₁' : (x₁ : ℝ) = u 1 * (2 * (s.j - 3 * (u 3 * s.t)) -
        2 * (u 2 * (s.j - 3 * (u 3 * s.t)))) := by
      have hsub : 2 * x₂ ≤ 2 * r := Nat.mul_le_mul_left _ h₂
      simp only [x₁, Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_ofNat, (hv 1).1, hr', h₂']
    funext i
    change (e i : ℝ) = param s u i
    rw [he]
    fin_cases i
    · change (x₀ : ℝ) = _
      simp only [x₀, Nat.cast_mul, Nat.cast_sub hsum, Nat.cast_ofNat, Nat.cast_add,
        (hv 0).1, h₁', h₂', hz']
      change _ = u 0 * (2 * (s.b : ℝ) - _ - _ - _)
      ring
    · exact h₁'
    · exact h₂'
    · change (↑(2 * z) : ℝ) = 2 * (u 3 * s.t)
      rw [Nat.cast_mul, Nat.cast_ofNat, hz']
theorem cube_mem (s : Shape) (hs : Chamber s) (T : Finset (Fin 4)) (u : Fin 4 → ℝ)
    (hside : ∀ i ∈ T, 0 ≤ u i ∧ u i ≤ 1)
    (hcorner : ∀ i ∉ T, u i = 0 ∨ u i = 1) :
    param s u ∈ latticeBody (doubledSupport s) := by
  classical
  induction T using Finset.induction_on generalizing u with
  | empty => exact corner_mem s hs u (fun i => hcorner i (by simp))
  | @insert i T hi ih =>
      have updated (b : ℝ) (hb : b = 0 ∨ b = 1) :
          param s (Function.update u i b) ∈ latticeBody (doubledSupport s) := by
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
      have hui := hside i (Finset.mem_insert_self i T)
      rw [param_update s u i]
      exact convex_convexHull ℝ _ (updated 0 (Or.inl rfl)) (updated 1 (Or.inr rfl))
        (sub_nonneg.mpr hui.2) hui.1 (sub_add_cancel 1 (u i))
private theorem exists_scale {x d : ℝ} (hx : 0 ≤ x) (hxd : x ≤ d) :
    ∃ u : ℝ, (0 ≤ u ∧ u ≤ 1) ∧ u * d = x := by
  by_cases hd : d = 0
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by linarith⟩
  · have hd' : 0 < d := lt_of_le_of_ne (hx.trans hxd) (Ne.symm hd)
    exact ⟨x / d, ⟨div_nonneg hx hd'.le, (div_le_one hd').mpr hxd⟩, div_mul_cancel₀ x hd⟩
theorem latticeBody_doubledSupport (s : Shape) (hs : Chamber s) :
    latticeBody (doubledSupport s) = capBody (s.scale 2) := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_body _)
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨hb, hj, ht⟩ := mem_doubledSupport.mp he
    refine (mem_body _ _).mpr ⟨fun _ => Nat.cast_nonneg _, ?_, ?_, ?_⟩
    · simp only [Fin.sum_univ_four] at hb
      change (e 0 : ℝ) + e 1 + e 2 + e 3 ≤ _
      exact_mod_cast hb
    · have hindex : e 1 + 2 * e 2 + 3 * e 3 ≤ (s.scale 2).j := by
        simpa [Fin.sum_univ_four] using hj
      change (e 1 : ℝ) + 2 * e 2 + 3 * e 3 ≤ _
      exact_mod_cast hindex
    · exact Nat.cast_le.mpr ht
  · intro x hx
    obtain ⟨hx, hb, hj, ht⟩ := (mem_body _ _).mp hx
    simp only [Shape.scale, Nat.cast_mul, Nat.cast_ofNat] at hb hj ht
    obtain ⟨u₃, hu₃, h₃⟩ := exists_scale (div_nonneg (hx 3) (by norm_num : (0 : ℝ) ≤ 2))
      (show x 3 / 2 ≤ s.t by linarith)
    obtain ⟨u₂, hu₂, h₂⟩ := exists_scale (hx 2)
      (show x 2 ≤ s.j - 3 * (u₃ * s.t) by linarith [hx 1])
    obtain ⟨u₁, hu₁, h₁⟩ := exists_scale (hx 1)
      (show x 1 ≤ 2 * (s.j - 3 * (u₃ * s.t)) - 2 * (u₂ * (s.j - 3 * (u₃ * s.t))) by
        rw [h₂]
        linarith)
    obtain ⟨u₀, hu₀, h₀⟩ := exists_scale (hx 0)
      (show x 0 ≤ 2 * (s.b : ℝ) - (u₁ * (2 * (s.j - 3 * (u₃ * s.t)) -
        2 * (u₂ * (s.j - 3 * (u₃ * s.t))))) - (u₂ * (s.j - 3 * (u₃ * s.t))) -
          2 * (u₃ * s.t) by
        rw [h₁, h₂, h₃]
        linarith)
    let u : Fin 4 → ℝ := ![u₀, u₁, u₂, u₃]
    have heq : param s u = x := by
      funext i
      fin_cases i
      · exact h₀
      · exact h₁
      · exact h₂
      · change 2 * (u₃ * s.t) = x 3
        linarith
    rw [← heq]
    apply cube_mem s hs Finset.univ
    · intro i _
      fin_cases i
      · exact hu₀
      · exact hu₁
      · exact hu₂
      · exact hu₃
    · simp
theorem capBody_double (s : Shape) : capBody (s.scale 2) = (2 : ℝ) • capBody s := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hb, hj, ht⟩ := (mem_body _ _).mp hx
    simp only [Shape.scale, Nat.cast_mul, Nat.cast_ofNat] at hb hj ht
    refine ⟨fun i => x i / 2, (mem_body _ _).mpr ?_, ?_⟩
    · exact ⟨fun i => div_nonneg (hx i) (by norm_num), by linarith, by linarith, by linarith⟩
    · funext i
      change 2 * (x i / 2) = x i
      ring
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu, hb, hj, ht⟩ := (mem_body _ _).mp hu
    apply (mem_body _ _).mpr
    simp only [Pi.smul_apply, smul_eq_mul, Shape.scale, Nat.cast_mul, Nat.cast_ofNat]
    exact ⟨fun i => mul_nonneg (by norm_num) (hu i), by linarith, by linarith, by linarith⟩
end
end K1_13_7_5_3_3
end
section
namespace K1_13_7_5_3_3
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_5_3
open K1_13_5_4_2_4 (latticeBody)
open MeasureTheory
open scoped BigOperators Pointwise
def subsetDifference (B : Fin 4 → Set RealJets) (I : Finset (Fin 4))
    (F : Set RealJets → ℝ) (x : Set RealJets) : ℝ :=
  ∑ T ∈ I.powerset, (-1 : ℝ) ^ (I.card - T.card) * F (x + ∑ j ∈ T, B j)
theorem subsetDifference_insert (B : Fin 4 → Set RealJets)
    {i : Fin 4} {I : Finset (Fin 4)} (hi : i ∉ I)
    (F : Set RealJets → ℝ) (x : Set RealJets) :
    subsetDifference B (insert i I) F x =
      subsetDifference B I (capDifference F (B i)) x := by
  classical
  unfold subsetDifference
  rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have hsub := Finset.mem_powerset.mp hT
  have hiT := fun h => hi (hsub h)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hiT,
    Finset.sum_insert hiT, show I.card + 1 - T.card = I.card - T.card + 1 by omega,
    show I.card + 1 - (T.card + 1) = I.card - T.card by omega,
    show x + (B i + ∑ j ∈ T, B j) = (x + ∑ j ∈ T, B j) + B i by ac_rfl,
    pow_succ, capDifference]
  ring
theorem mixedVolume4_caps (p q r s : Shape) :
    K1_13_5_4_2.mixedVolume4 ![capBody p, capBody q, capBody r, capBody s] =
      capMixed p q r s := by
  classical
  let B : Fin 4 → Set RealJets := ![capBody p, capBody q, capBody r, capBody s]
  have heq : K1_13_5_4_2.mixedVolume4 B = subsetDifference B Finset.univ capVolume 0 := by
    simp [K1_13_5_4_2.mixedVolume4, subsetDifference, capVolume]
  change K1_13_5_4_2.mixedVolume4 B = _
  rw [heq, show (Finset.univ : Finset (Fin 4)) = insert 0 (insert 1 (insert 2 (insert 3 ∅))) by decide]
  rw [subsetDifference_insert B (show (0 : Fin 4) ∉ insert 1 (insert 2 (insert 3 ∅)) by decide),
    subsetDifference_insert B (show (1 : Fin 4) ∉ insert 2 (insert 3 ∅) by decide),
    subsetDifference_insert B (show (2 : Fin 4) ∉ insert 3 ∅ by decide),
    subsetDifference_insert B (show (3 : Fin 4) ∉ (∅ : Finset (Fin 4)) by decide)]
  simp [subsetDifference, capMixed, B, Set.singleton_zero]
theorem double_add (s t : Set RealJets) :
    (2 : ℝ) • (s + t) = (2 : ℝ) • s + (2 : ℝ) • t := by
  ext x
  constructor
  · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    exact ⟨2 • u, ⟨u, hu, rfl⟩, 2 • v, ⟨v, hv, rfl⟩, (smul_add (2 : ℝ) u v).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u + v, ⟨u, hu, v, hv, rfl⟩, smul_add (2 : ℝ) u v⟩
theorem double_sum (B : Fin 4 → Set RealJets) (T : Finset (Fin 4)) :
    (∑ i ∈ T, (2 : ℝ) • B i) = (2 : ℝ) • (∑ i ∈ T, B i) := by
  induction T using Finset.induction_on with
  | empty => simp [← Set.singleton_zero]
  | @insert i T hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, double_add]
theorem mixedVolume4_double (B : Fin 4 → Set RealJets) :
    K1_13_5_4_2.mixedVolume4 (fun i => (2 : ℝ) • B i) =
      16 * K1_13_5_4_2.mixedVolume4 B := by
  unfold K1_13_5_4_2.mixedVolume4
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [double_sum, Measure.addHaar_smul_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 2),
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ENNReal.toReal_mul]
  norm_num
  ring
theorem mixedVolume4_supports {p q H : Shape} (hp : Chamber p)
    (hq : Chamber q) (hH : Chamber H) :
    K1_13_5_4_2.mixedVolume4 (fun i => latticeBody (supports p q H i)) =
      16 * capMixed p q q H := by
  let B : Fin 4 → Set RealJets := ![capBody p, capBody q, capBody q, capBody H]
  have he : (fun i => latticeBody (supports p q H i)) = fun i => (2 : ℝ) • B i := by
    funext i
    fin_cases i
    · exact (latticeBody_doubledSupport p hp).trans (capBody_double p)
    · exact (latticeBody_doubledSupport q hq).trans (capBody_double q)
    · exact (latticeBody_doubledSupport q hq).trans (capBody_double q)
    · exact (latticeBody_doubledSupport H hH).trans (capBody_double H)
  rw [he, mixedVolume4_double]
  exact congrArg (16 * ·) (mixedVolume4_caps p q q H)
theorem capMixed_zero_last {p q H : Shape} (hp : p.t = 0) (hq : q.t = 0) (hH : H.t = 0) :
    capMixed p q q H = 0 := by
  classical
  let B : Fin 4 → Set RealJets := ![capBody p, capBody q, capBody q, capBody H]
  let E : Set RealJets := {x | x 3 = 0}
  have hcap (s : Shape) (hs : s.t = 0) : capBody s ⊆ E := by
    intro x hx
    have ht := hx.2.2.2
    rw [hs, Nat.cast_zero] at ht
    exact le_antisymm ht (hx.1 3)
  have hB (i : Fin 4) : B i ⊆ E := by
    fin_cases i
    · exact hcap p hp
    · exact hcap q hq
    · exact hcap q hq
    · exact hcap H hH
  have hsum (T : Finset (Fin 4)) : (∑ i ∈ T, B i) ⊆ E := by
    induction T using Finset.induction_on with
    | empty => simp [E, ← Set.singleton_zero]
    | @insert i T hi ih =>
        rw [Finset.sum_insert hi]
        rintro _ ⟨u, hu, v, hv, rfl⟩
        change u 3 + v 3 = 0
        rw [show u 3 = 0 from hB i hu, show v 3 = 0 from ih hv, zero_add]
  have hE : volume E = 0 := by
    rw [volume_pi]
    exact Measure.pi_hyperplane (fun _ => volume) 3 0
  rw [← mixedVolume4_caps]
  change K1_13_5_4_2.mixedVolume4 B = _
  unfold K1_13_5_4_2.mixedVolume4
  apply Finset.sum_eq_zero
  intro T _
  rw [measure_mono_null (hsum T) hE, ENNReal.toReal_zero, mul_zero]
end
end K1_13_7_5_3_3
end
section
namespace K1_13_7_5_3_3
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_5 K1_13_7_5_3
open K1_13_7_4_2 (remainingIdeal)
open K1_13_5_4_2_4 (CoefficientField GenericQuotient corner exponentCount latticeBody)
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology
def c1 : Prop :=
  ∀ (y : JetPoint) (g : Fin 4 → PointLocal y),
    (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal (PointLocal y) →
    ∀ i x, g i * x ∈ remainingIdeal g i → x ∈ remainingIdeal g i
def c2 : Prop :=
  ∀ (p q H : Shape), Chamber p → Chamber q → Chamber H →
    let A := supports p q H
    Module.Finite (CoefficientField A) (GenericQuotient A) →
    ∀ (f : Fin 4 → Jets), (∀ i, (f i).support ⊆ A i) →
      ∀ points : Finset JetPoint,
        (∀ y ∈ points, K1_13_5_4_2.pointIdeal y ∈ (K1_13_5_4_2_4.cutIdeal f).minimalPrimes) →
        (∑ y ∈ points, (K1_13_5_4_2.pointLength (K1_13_5_4_2_4.cutIdeal f) y).toNat) ≤
          Module.finrank (CoefficientField A) (GenericQuotient A)
def c3 : Prop :=
  ∀ (p q H : Shape), Chamber p → Chamber q → Chamber H →
    (0 < p.t ∨ 0 < q.t ∨ 0 < H.t) →
    let A := supports p q H
    Module.Finite (CoefficientField A) (GenericQuotient A) ∧
      ∃ b : ℕ, ∀ n : ℕ,
        (Module.finrank (CoefficientField A) (GenericQuotient A) : ℝ) * (n : ℝ)^4 =
          ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
            (-1 : ℝ) ^ (4 - S.card) * (exponentCount A (corner b n S) : ℝ)
def c4 : Prop :=
  ∀ (p q H : Shape), Chamber p → Chamber q → Chamber H →
    ∀ (b : ℕ) (S : Finset (Fin 4)),
      let A := supports p q H
      Tendsto (fun n : ℕ => (exponentCount A (corner b n S) : ℝ) / (n : ℝ)^4)
        atTop (𝓝 (volume (∑ i ∈ S, latticeBody (A i))).toReal)
theorem generic_mixed (hdiag : c4) {p q H : Shape}
    (hp : Chamber p) (hq : Chamber q) (hH : Chamber H) (b : ℕ)
    (h : ∀ n : ℕ, (Module.finrank (CoefficientField (supports p q H))
        (GenericQuotient (supports p q H)) : ℝ) * (n : ℝ)^4 =
        ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
          (-1 : ℝ) ^ (4 - S.card) * (exponentCount (supports p q H) (corner b n S) : ℝ)) :
    (Module.finrank (CoefficientField (supports p q H)) (GenericQuotient (supports p q H)) : ℝ) =
      16 * capMixed p q q H := by
  rw [← mixedVolume4_supports hp hq hH]
  unfold K1_13_5_4_2.mixedVolume4
  apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    (f := fun n : ℕ => ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * ((exponentCount (supports p q H) (corner b n S) : ℝ) / (n : ℝ)^4))
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ)^4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
    symm
    calc
      _ = (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
          (-1 : ℝ) ^ (4 - S.card) * (exponentCount (supports p q H) (corner b n S) : ℝ)) /
            (n : ℝ)^4 := by simp only [Finset.sum_div, mul_div_assoc]
      _ = _ := by rw [← h n, mul_div_cancel_right₀ _ hn']
  · exact tendsto_finsetSum _ fun S _ => (hdiag p q H hp hq hH b S).const_mul _
theorem c3_of_hilbert (h : K1_13_5_4_2_4.c2) : c3 := by
  intro p q H hp hq hH htop
  apply h
  · intro i
    fin_cases i <;> exact zero_mem_doubledSupport _
  · intro j
    rcases htop with ht | ht | ht
    · exact ⟨0, single_mem_doubledSupport hp ht j⟩
    · exact ⟨1, single_mem_doubledSupport hq ht j⟩
    · exact ⟨3, single_mem_doubledSupport hH ht j⟩
theorem of_children (hregular : c1) (hspec : c2) (hhilb : c3) (hdiag : c4) :
    K1_13_7_5_3.c3 := by
  classical
  intro p q H hp hq hH F G L D hF hG hL hD m points hpoints
  let f : Fin 4 → Jets := ![F, G, L, D]
  let g : Fin 4 → Jets := fun i => f i ^ 2
  let J := K1_13_5_4_2_4.cutIdeal f
  let J' := K1_13_5_4_2_4.cutIdeal g
  have hpoints' (y : JetPoint) (hy : y ∈ points) : IsolatedLengthGE J m y := by
    simpa only [J, f, cutIdeal_vec] using hpoints y hy
  by_cases htop : 0 < p.t ∨ 0 < q.t ∨ 0 < H.t
  · have hsupp (i : Fin 4) : (g i).support ⊆ supports p q H i := by
      fin_cases i
      · exact sq_support_subset hF
      · exact sq_support_subset hG
      · exact sq_support_subset hL
      · exact sq_support_subset hD
    have hmin (y : JetPoint) (hy : y ∈ points) :
        jetPointIdeal y ∈ J'.minimalPrimes := squared_isolated (hpoints' y hy).1
    have hlen (y : JetPoint) (hy : y ∈ points) :
        16 * m ≤ (K1_13_5_4_2.pointLength J' y).toNat := by
      have hm : (↑(16 * m) : ℕ∞) ≤ liftLength (pointPrime y) J' := by
        rw [Nat.cast_mul, Nat.cast_ofNat, squared_length (hpoints' y hy).1 (hregular y)]
        exact mul_le_mul_of_nonneg_left (hpoints' y hy).2 zero_le
      rw [← pointLength_eq] at hm
      have hfin := pointLength_ne_top (hmin y hy)
      rw [← pointLength_eq] at hfin
      simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat hm hfin
    obtain ⟨hfinite, b, hb⟩ := hhilb p q H hp hq hH htop
    have hbnd := hspec p q H hp hq hH hfinite g hsupp points
      (fun y hy => by simpa only [pointIdeal_eq] using hmin y hy)
    have hn : 16 * m * points.card ≤
        Module.finrank (CoefficientField (supports p q H)) (GenericQuotient (supports p q H)) := by
      calc
        _ = ∑ _y ∈ points, 16 * m := by simp [Nat.mul_comm]
        _ ≤ _ := (Finset.sum_le_sum hlen).trans hbnd
    have hr := (Nat.cast_le (α := ℝ)).mpr hn
    rw [generic_mixed hdiag hp hq hH b hb] at hr
    push_cast at hr ⊢
    linarith
  · have hpt : p.t = 0 := by omega
    have hqt : q.t = 0 := by omega
    have hHt : H.t = 0 := by omega
    let s : Fin 4 → Shape := ![p, q, q, H]
    have hz (i : Fin 4) : (s i).t = 0 := by fin_cases i <;> assumption
    have hfit (i : Fin 4) : Supported (s i) (f i) := by fin_cases i <;> assumption
    have hempty : points = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun y hy =>
      not_isolated_without_last hz hfit y (hpoints' y hy).1
    simp [hempty, capMixed_zero_last hpt hqt hHt]
end
end K1_13_7_5_3_3
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_2
open K1_13_7_5 (Jets JetPoint)
open K1_13_5_4_2_4 (CoefficientField Exponent genericEquation)
open scoped Polynomial
noncomputable section
abbrev Affine (k : Type) [CommRing k] := MvPolynomial (Fin 4) k
abbrev Family (k : Type) [CommRing k] := Affine k[X]
def equationIdeal {R : Type} [CommRing R] (f : Fin 4 → Affine R) : Ideal (Affine R) :=
  Ideal.span (Set.range f)
def rationalIdeal {k : Type} [Field k] (y : Fin 4 → k) : Ideal (Affine k) :=
  RingHom.ker (MvPolynomial.eval y)
instance rationalIdeal_isPrime {k : Type} [Field k] (y : Fin 4 → k) :
    (rationalIdeal y).IsPrime := RingHom.ker_isPrime _
def localContraction {R : Type} [CommRing R] (I P : Ideal R) [P.IsPrime] : Ideal R :=
  let ι := algebraMap R (Localization.AtPrime P)
  (I.map ι).comap ι
def zeroFibre {k : Type} [CommRing k] : Family k →+* Affine k :=
  MvPolynomial.map (Polynomial.evalRingHom 0)
def liftedPoint {k : Type} [Field k] (y : Fin 4 → k) : Ideal (Family k) :=
  (rationalIdeal y).comap zeroFibre
instance liftedPoint_isPrime {k : Type} [Field k] (y : Fin 4 → k) :
    (liftedPoint y).IsPrime := Ideal.comap_isPrime _ _
def markedIdeal {k : Type} [Field k] (I : Ideal (Affine k)) (points : Finset (Fin 4 → k)) :
    Ideal (Affine k) :=
  ⨅ y : ↥points, localContraction I (rationalIdeal y.1)
abbrev GenericField (k : Type) [Field k] := FractionRing (Polynomial k)
def genericFibre {k : Type} [Field k] : Family k →+* Affine (GenericField k) :=
  MvPolynomial.map (algebraMap k[X] (GenericField k))
abbrev FamilyQuotient {k : Type} [Field k] (F : Fin 4 → Family k) :=
  Affine (GenericField k) ⧸ equationIdeal (fun i => genericFibre (F i))
def coefficientLine (A : Fin 4 → Finset Exponent) (f : Fin 4 → Jets) (i : Fin 4) :
    Family (CoefficientField A) :=
  MvPolynomial.C (1 - Polynomial.X) *
      MvPolynomial.map (Polynomial.C.comp (algebraMap _ (CoefficientField A))) (f i) +
    MvPolynomial.C Polynomial.X * MvPolynomial.map Polynomial.C (genericEquation A i)
end
end K1_13_7_5_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_2
open K1_13_7_5 (Jets)
open K1_13_5_4_2_4 (CoefficientRing CoefficientField Exponent genericEquation GenericQuotient)
open MvPolynomial
open scoped Polynomial TensorProduct
noncomputable section
def quotientBaseChange (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal (Affine R)) :
    S ⊗[R] (Affine R ⧸ I) ≃ₐ[S] Affine S ⧸ I.map (map (algebraMap R S)) := by
  let e : S ⊗[R] Affine R ≃ₐ[S] Affine S := algebraTensorAlgEquiv R S
  have hmap : e.toRingHom.comp (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom =
      map (σ := Fin 4) (algebraMap R S) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[R] p) = _
    simp [e]
  refine (Algebra.TensorProduct.tensorQuotientEquiv S (Affine R) S I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (map (algebraMap R S)) =
    (I.map (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom).map e.toRingHom
  rw [Ideal.map_map, hmap]
theorem equationIdeal_map {R S : Type} [CommRing R] [CommRing S]
    (g : R →+* S) (f : Fin 4 → Affine R) :
    (equationIdeal f).map (map g) = equationIdeal (fun i => map g (f i)) := by
  rw [equationIdeal, equationIdeal, Ideal.map_span, ← Set.range_comp]
  rfl
def coefficientHom (A : Fin 4 → Finset Exponent) (f : Fin 4 → Jets) :
    CoefficientRing A →+* (CoefficientField A)[X] :=
  eval₂Hom (Polynomial.C.comp (algebraMap _ (CoefficientField A))) fun s =>
    (1 - Polynomial.X) * Polynomial.C (algebraMap _ _ ((f s.1).coeff s.2.1)) +
      Polynomial.X * Polynomial.C (algebraMap (CoefficientRing A) _ (MvPolynomial.X s))
theorem eval_one_coefficientHom (A : Fin 4 → Finset Exponent) (f : Fin 4 → Jets) :
    (Polynomial.evalRingHom 1).comp (coefficientHom A f) =
      algebraMap (CoefficientRing A) (CoefficientField A) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [coefficientHom]
    rw [IsScalarTower.algebraMap_apply K1_13_5_4.GeometricX (CoefficientRing A),
      MvPolynomial.algebraMap_eq]
  · intro i
    simp [coefficientHom]
def lineFieldHom (A : Fin 4 → Finset Exponent) (f : Fin 4 → Jets) :
    CoefficientField A →+* GenericField (CoefficientField A) :=
  IsFractionRing.lift
    (g := (algebraMap (CoefficientField A)[X] _).comp (coefficientHom A f)) <| by
      intro x y h
      have h' := IsFractionRing.injective (CoefficientField A)[X]
        (GenericField (CoefficientField A)) h
      apply IsFractionRing.injective (CoefficientRing A) (CoefficientField A)
      rw [← eval_one_coefficientHom A f]
      exact congrArg (Polynomial.evalRingHom 1) h'
theorem coefficientLine_at_zero (A : Fin 4 → Finset Exponent) (f : Fin 4 → Jets)
    (i : Fin 4) :
    zeroFibre (coefficientLine A f i) = map (algebraMap _ (CoefficientField A)) (f i) := by
  have hC : (Polynomial.evalRingHom (0 : CoefficientField A)).comp Polynomial.C =
      RingHom.id _ := by
    ext a
    simp
  simp [zeroFibre, coefficientLine, map_map, ← RingHom.comp_assoc, hC]
theorem coefficientLine_at_generic (A : Fin 4 → Finset Exponent) (f : Fin 4 → Jets)
    (hs : ∀ i, (f i).support ⊆ A i) (i : Fin 4) :
    map (lineFieldHom A f) (genericEquation A i) = genericFibre (coefficientLine A f i) := by
  classical
  have hsum : f i = ∑ a : ↥(A i), monomial a.1 ((f i).coeff a.1) := by
    rw [Finset.sum_coe_sort (A i) (fun a => monomial a ((f i).coeff a))]
    exact (f i).as_sum.trans (Finset.sum_subset (hs i) fun a _ ha => by
      simp [notMem_support_iff.mp ha])
  have h :
      (∑ a : ↥(A i), monomial a.1
        (coefficientHom A f (MvPolynomial.X ⟨i, a⟩))) = coefficientLine A f i := by
    conv_rhs =>
      unfold coefficientLine
      rw [hsum, genericEquation]
    simp only [map_sum, map_monomial, Finset.mul_sum, ← Finset.sum_add_distrib,
      coefficientHom, eval₂Hom_X', RingHom.comp_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_add, C_mul_monomial, C_mul_monomial]
  unfold genericFibre
  rw [← h]
  simp only [genericEquation, map_sum, map_monomial]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  unfold lineFieldHom
  exact IsFractionRing.lift_algebraMap _ _
theorem baseChange_finrank (R S : Type) [Field R] [Field S] [Algebra R S]
    (J : Ideal (Affine R)) (h : Module.Finite R (Affine R ⧸ J)) :
    Module.Finite S (Affine S ⧸ J.map (map (algebraMap R S))) ∧
      Module.finrank S (Affine S ⧸ J.map (map (algebraMap R S))) =
        Module.finrank R (Affine R ⧸ J) := by
  let e := quotientBaseChange R S J
  let : Module.Finite R (Affine R ⧸ J) := h
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    e.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange⟩
theorem line_finrank (A : Fin 4 → Finset Exponent) (f : Fin 4 → Jets)
    (hs : ∀ i, (f i).support ⊆ A i)
    (hfinite : Module.Finite (CoefficientField A) (GenericQuotient A)) :
    Module.Finite (GenericField (CoefficientField A)) (FamilyQuotient (coefficientLine A f)) ∧
      Module.finrank (GenericField (CoefficientField A)) (FamilyQuotient (coefficientLine A f)) =
        Module.finrank (CoefficientField A) (GenericQuotient A) := by
  let K := CoefficientField A
  let L := GenericField K
  let : Algebra (CoefficientField A) (GenericField (CoefficientField A)) :=
    (lineFieldHom A f).toAlgebra
  let J := equationIdeal (genericEquation A)
  have hJ : J.map (map (algebraMap K L)) =
      equationIdeal (fun i => genericFibre (coefficientLine A f i)) := by
    rw [equationIdeal_map]
    congr 1
    funext i
    exact coefficientLine_at_generic A f hs i
  have hf := baseChange_finrank K L J hfinite
  rw [hJ] at hf
  exact hf
end
end K1_13_7_5_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_2
open K1_13_7 (GeometricX)
open K1_13_7_5 (Jets JetPoint)
open K1_13_7_5_3_3 (supports)
open K1_13_5_4_2 (pointIdeal pointLength)
open K1_13_5_4_2_4 (CoefficientField Exponent GenericQuotient cutIdeal)
open scoped Polynomial TensorProduct
noncomputable section
def c1 : Prop :=
  ∀ (k : Type) [Field k] [Algebra GeometricX k] (f : Fin 4 → Jets)
    (y : JetPoint), pointIdeal y ∈ (cutIdeal f).minimalPrimes →
    let P := rationalIdeal (fun i => algebraMap GeometricX k (y i))
    let I := equationIdeal (fun i => MvPolynomial.map (algebraMap GeometricX k) (f i))
    P ∈ I.minimalPrimes ∧
      Module.Finite k (Affine k ⧸ localContraction I P) ∧
      Module.finrank k (Affine k ⧸ localContraction I P) =
        (pointLength (cutIdeal f) y).toNat
def c2 : Prop :=
  ∀ (k : Type) [Field k] (F : Fin 4 → Family k) (y : Fin 4 → k),
    rationalIdeal y ∈ (equationIdeal (fun i => zeroFibre (F i))).minimalPrimes →
    ∀ r : Family k,
      MvPolynomial.C Polynomial.X * r ∈ localContraction (equationIdeal F) (liftedPoint y) →
      r ∈ localContraction (equationIdeal F) (liftedPoint y)
theorem zeroFibre_map_C {k : Type} [Field k] (v : Affine k) :
    zeroFibre (MvPolynomial.map Polynomial.C v) = v := by
  have h : (Polynomial.evalRingHom (0 : k)).comp Polynomial.C = RingHom.id k := by
    ext a
    simp
  simp [zeroFibre, MvPolynomial.map_map, h, MvPolynomial.map_id]
theorem zero_mem_local {k : Type} [Field k] (F : Fin 4 → Family k)
    (y : Fin 4 → k) {r : Family k}
    (h : r ∈ localContraction (equationIdeal F) (liftedPoint y)) :
    zeroFibre r ∈ localContraction (equationIdeal (fun i => zeroFibre (F i)))
      (rationalIdeal y) := by
  let P := liftedPoint y
  let Q := rationalIdeal y
  change algebraMap (Family k) (Localization.AtPrime P) r ∈
    (equationIdeal F).map (algebraMap (Family k) (Localization.AtPrime P)) at h
  change algebraMap (Affine k) (Localization.AtPrime Q) (zeroFibre r) ∈
    (equationIdeal (fun i => zeroFibre (F i))).map (algebraMap (Affine k) (Localization.AtPrime Q))
  obtain ⟨s, hs, hsr⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl
      (Localization.AtPrime P) (equationIdeal F) r).mp h
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl
    (Localization.AtPrime Q) _ _).mpr
  refine ⟨zeroFibre s, hs, ?_⟩
  change zeroFibre s * zeroFibre r ∈ equationIdeal (fun i => zeroFibre (F i))
  rw [← map_mul, ← show (equationIdeal F).map zeroFibre =
      equationIdeal (fun i => zeroFibre (F i)) from equationIdeal_map _ F]
  exact Ideal.mem_map_of_mem _ hsr
theorem marked_finrank_le (hreg : c2) (k : Type) [Field k]
    (F : Fin 4 → Family k) (points : Finset (Fin 4 → k))
    (hisol : ∀ y ∈ points, rationalIdeal y ∈ (equationIdeal (fun i => zeroFibre (F i))).minimalPrimes)
    (hmarked : Module.Finite k
      (Affine k ⧸ markedIdeal (equationIdeal (fun i => zeroFibre (F i))) points))
    (hfinite : Module.Finite (GenericField k) (FamilyQuotient F)) :
    Module.finrank k (Affine k ⧸ markedIdeal (equationIdeal (fun i => zeroFibre (F i))) points) ≤
      Module.finrank (GenericField k) (FamilyQuotient F) := by
  classical
  let L := GenericField k
  let J := equationIdeal F
  let B := Family k ⧸ J
  let I := markedIdeal (equationIdeal (fun i => zeroFibre (F i))) points
  let E := Affine k ⧸ I
  let N := Module.finrank k E
  let : Module.Finite k E := hmarked
  let b := Module.finBasis k E
  choose v hv using (fun i : Fin N => Ideal.Quotient.mk_surjective (b i))
  let u : Fin N → Family k := fun i => MvPolynomial.map Polynomial.C (v i)
  let rel : (Fin N → k[X]) → Family k := fun c =>
    ∑ i, MvPolynomial.C (c i) * u i
  have specialize (c : Fin N → k[X])
      (hc : ∀ y ∈ points, rel c ∈ localContraction J (liftedPoint y)) :
      ∀ i, (c i).coeff 0 = 0 := by
    have hmem : zeroFibre (rel c) ∈ I :=
      Ideal.mem_iInf.mpr fun y => zero_mem_local F y.1 (hc y.1 y.2)
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hterm (i : Fin N) :
        Ideal.Quotient.mk I (zeroFibre (MvPolynomial.C (c i) * u i)) =
          (c i).coeff 0 • b i := by
      have hC : zeroFibre (MvPolynomial.C (c i)) = MvPolynomial.C ((c i).coeff 0) := by
        simp [zeroFibre, Polynomial.coeff_zero_eq_eval_zero]
      have hu : zeroFibre (u i) = v i := zeroFibre_map_C (v i)
      rw [map_mul, hC, hu, map_mul, ← MvPolynomial.algebraMap_eq,
        Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def, hv]
    have hz' : ∑ i, (c i).coeff 0 • b i = 0 := by
      simpa only [rel, map_sum, ← map_mul, hterm] using hz
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ hz'
  have allCoeffs (n : ℕ) (c : Fin N → k[X])
      (hc : ∀ y ∈ points, rel c ∈ localContraction J (liftedPoint y)) :
      ∀ i, (c i).coeff n = 0 := by
    induction n generalizing c with
    | zero => exact specialize c hc
    | succ n ih =>
      have hdiv (i : Fin N) : Polynomial.X * (c i).divX = c i := by
        simpa [specialize c hc i] using Polynomial.X_mul_divX_add (c i)
      have hrel : MvPolynomial.C Polynomial.X * rel (fun i => (c i).divX) = rel c := by
        simp only [rel, Finset.mul_sum, ← mul_assoc, ← map_mul, hdiv]
      have hc' : ∀ y ∈ points, rel (fun i => (c i).divX) ∈
          localContraction J (liftedPoint y) := by
        intro y hy
        apply hreg k F y (hisol y hy)
        rw [hrel]
        exact hc y hy
      intro i
      simpa only [Polynomial.coeff_divX] using ih _ hc' i
  have hind : LinearIndependent k[X] (fun i => (Ideal.Quotient.mk J (u i) : B)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hj : rel c ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hm (i : Fin N) : Ideal.Quotient.mk J (MvPolynomial.C (c i) * u i) =
          c i • Ideal.Quotient.mk J (u i) := by
        rw [map_mul, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap,
          ← Algebra.smul_def]
      simpa only [rel, map_sum, hm] using hc
    have hl (y : Fin 4 → k) (_ : y ∈ points) :
        rel c ∈ localContraction J (liftedPoint y) := Ideal.mem_map_of_mem _ hj
    ext n
    rw [Polynomial.coeff_zero]
    exact allCoeffs n c hl i
  let lift : B →ₗ[k[X]] L ⊗[k[X]] B := TensorProduct.mk k[X] L B 1
  have hind' := hind.of_isLocalizedModule L (nonZeroDivisors (k[X])) lift
  have hJ : J.map (MvPolynomial.map (algebraMap k[X] L)) =
      equationIdeal (fun i => genericFibre (F i)) := equationIdeal_map _ F
  let e : L ⊗[k[X]] B ≃ₐ[L] FamilyQuotient F :=
    (quotientBaseChange (k[X]) L J).trans (Ideal.quotientEquivAlgOfEq L hJ)
  let : Module.Finite L (FamilyQuotient F) := hfinite
  let : Module.Finite L (L ⊗[k[X]] B) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have hn := hind'.fintype_card_le_finrank
  rw [e.toLinearEquiv.finrank_eq, Fintype.card_fin] at hn
  exact hn
theorem rationalIdeal_isMaximal {k : Type} [Field k] (y : Fin 4 → k) :
    (rationalIdeal y).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval y) fun a =>
    ⟨MvPolynomial.C a, MvPolynomial.eval_C a⟩
theorem rationalIdeal_injective {k : Type} [Field k] :
    Function.Injective (rationalIdeal (k := k)) := by
  intro y z h
  funext i
  have hm : MvPolynomial.X i - MvPolynomial.C (y i) ∈ rationalIdeal y := by
    simp [rationalIdeal, RingHom.mem_ker]
  rw [h] at hm
  exact (sub_eq_zero.mp (by simpa [rationalIdeal, RingHom.mem_ker] using hm)).symm
theorem localContraction_radical {k : Type} [Field k] (I : Ideal (Affine k))
    (y : Fin 4 → k) (hy : rationalIdeal y ∈ I.minimalPrimes) :
    (localContraction I (rationalIdeal y)).radical = rationalIdeal y := by
  let P := rationalIdeal y
  let S := Localization.AtPrime P
  let m := algebraMap (Affine k) S
  change ((I.map m).comap m).radical = P
  rw [← Ideal.comap_radical,
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes S P I hy,
    Localization.AtPrime.map_eq_maximalIdeal]
  exact Localization.AtPrime.under_maximalIdeal
theorem marked_finrank_eq_sum (k : Type) [Field k] (I : Ideal (Affine k))
    (points : Finset (Fin 4 → k))
    (hisol : ∀ y ∈ points, rationalIdeal y ∈ I.minimalPrimes)
    (hfinite : ∀ y ∈ points, Module.Finite k (Affine k ⧸ localContraction I (rationalIdeal y))) :
    Module.Finite k (Affine k ⧸ markedIdeal I points) ∧
      Module.finrank k (Affine k ⧸ markedIdeal I points) =
        ∑ y ∈ points, Module.finrank k (Affine k ⧸ localContraction I (rationalIdeal y)) := by
  classical
  let J (y : ↥points) := localContraction I (rationalIdeal y.1)
  have hcoprime : Pairwise (fun x y => IsCoprime (J x) (J y)) := by
    intro x y hxy
    rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.radical_eq_top, Ideal.radical_sup,
      localContraction_radical I x.1 (hisol x.1 x.2),
      localContraction_radical I y.1 (hisol y.1 y.2)]
    have hx := rationalIdeal_isMaximal x.1
    have hy := rationalIdeal_isMaximal y.1
    have hne : rationalIdeal x.1 ≠ rationalIdeal y.1 :=
      fun h => hxy (Subtype.ext (rationalIdeal_injective h))
    rw [hx.coprime_of_ne hy hne, Ideal.radical_top]
  let e : (Affine k ⧸ markedIdeal I points) ≃ₐ[k] (∀ y : ↥points, Affine k ⧸ J y) :=
    { Ideal.quotientInfRingEquivPiQuotient J hcoprime with
      commutes' := fun _ => rfl }
  let : ∀ y : ↥points, Module.Finite k (Affine k ⧸ J y) := fun y => hfinite y.1 y.2
  refine ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective, ?_⟩
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_coe_sort points
    (fun y => Module.finrank k (Affine k ⧸ localContraction I (rationalIdeal y)))
theorem coefficientLine_bound (hpoints : c1) (hreg : c2)
    (A : Fin 4 → Finset Exponent)
    (hfinite : Module.Finite (CoefficientField A) (GenericQuotient A))
    (f : Fin 4 → Jets) (hs : ∀ i, (f i).support ⊆ A i) (points : Finset JetPoint)
    (hisol : ∀ y ∈ points, pointIdeal y ∈ (cutIdeal f).minimalPrimes) :
    (∑ y ∈ points, (pointLength (cutIdeal f) y).toNat) ≤
      Module.finrank (CoefficientField A) (GenericQuotient A) := by
  classical
  let k := CoefficientField A
  let F := coefficientLine A f
  obtain ⟨hgen, hrank⟩ := line_finrank A f hs hfinite
  let mark (y : JetPoint) : Fin 4 → k := fun i => algebraMap GeometricX k (y i)
  let points' := points.image mark
  have hzero : (fun i => zeroFibre (F i)) =
      fun i => MvPolynomial.map (algebraMap GeometricX k) (f i) :=
    funext (coefficientLine_at_zero A f)
  let I := equationIdeal (fun i => zeroFibre (F i))
  let I₀ := equationIdeal (fun i => MvPolynomial.map (algebraMap GeometricX k) (f i))
  have hI : I = I₀ := congrArg equationIdeal hzero
  have hlocal (y : JetPoint) (hy : y ∈ points) :
      rationalIdeal (mark y) ∈ I.minimalPrimes ∧
      Module.Finite k (Affine k ⧸ localContraction I (rationalIdeal (mark y))) ∧
      Module.finrank k (Affine k ⧸ localContraction I (rationalIdeal (mark y))) =
        (pointLength (cutIdeal f) y).toNat := by
    rw [hI]
    exact hpoints k f y (hisol y hy)
  have hiso' (y : Fin 4 → k) (hy : y ∈ points') : rationalIdeal y ∈ I.minimalPrimes := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact (hlocal z hz).1
  have hfin' (y : Fin 4 → k) (hy : y ∈ points') :
      Module.Finite k (Affine k ⧸ localContraction I (rationalIdeal y)) := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact (hlocal z hz).2.1
  obtain ⟨hmarked, hlen⟩ := marked_finrank_eq_sum k I points' hiso' hfin'
  have hinj : Function.Injective mark := by
    intro y z h
    funext i
    exact (algebraMap GeometricX k).injective (congrFun h i)
  rw [show points' = points.image mark from rfl,
    Finset.sum_image (fun _ _ _ _ h => hinj h)] at hlen
  have hlength :
      (∑ y ∈ points, Module.finrank k (Affine k ⧸ localContraction I (rationalIdeal (mark y)))) =
        ∑ y ∈ points, (pointLength (cutIdeal f) y).toNat :=
    Finset.sum_congr rfl (fun y hy => (hlocal y hy).2.2)
  have hbound := marked_finrank_le hreg k F points' hiso' hmarked hgen
  rwa [hlen, hlength, hrank] at hbound
theorem of_children (hpoints : c1) (hreg : c2) : K1_13_7_5_3_3.c2 := by
  intro p q H _ _ _ A hfinite f hs points hisol
  exact coefficientLine_bound hpoints hreg A hfinite f hs points hisol
end
end K1_13_7_5_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_3
noncomputable section
open K1_13_5_4_2_4 K1_13_5_4_2_4_2
def c1 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    (∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) → ChartLifting A
def c2 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) → ChartLifting A →
    ∃ b : ℕ, ∀ (i : Fin 4) (d : Degree), (∀ j, b ≤ d j) →
      ∀ p ∈ piece A (shift d i 1), p ∈ prefixIdeal A (i.val + 1) →
        ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val
theorem of_children (hc : c1) (hg : c2) : K1_13_7_5_3_3.c3 := by
  apply K1_13_7_5_3_3.c3_of_hilbert
  apply K1_13_5_4_2_4_2.of_children
  · exact fun _ hzero => generic_finite hzero
  · exact fun _ hzero i p => generic_prefix_regular hzero i p
  · exact fun A hzero hcoords => hg A hzero (hc A hzero hcoords)
end
end K1_13_7_5_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_2_1
open K1_13_7_5_3_3_2 (Affine rationalIdeal localContraction)
open MvPolynomial
noncomputable section
variable {R : Type} [CommRing R]
theorem mem_localContraction (I P : Ideal R) [P.IsPrime] (x : R) :
    x ∈ localContraction I P ↔ ∃ u ∈ P.primeCompl, u * x ∈ I :=
  IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P) I x
theorem rational_isMaximal {k : Type} [Field k] (y : Fin 4 → k) :
    (rationalIdeal y).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (eval y) fun a => ⟨C a, eval_C a⟩
theorem contraction_radical (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
    (localContraction I P).radical = P := by
  let S := Localization.AtPrime P
  let m := algebraMap R S
  change ((I.map m).comap m).radical = P
  rw [← Ideal.comap_radical, IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes S P I hP,
    Localization.AtPrime.map_eq_maximalIdeal]
  exact Localization.AtPrime.under_maximalIdeal
theorem common_denominator (I P : Ideal R) [P.IsPrime]
    (J : Ideal R) (hfg : J.FG) (hJ : J ≤ localContraction I P) :
    ∃ u : P.primeCompl, Ideal.span { (u : R) } * J ≤ I := by
  induction J, hfg using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨u, hu, hux⟩ := (mem_localContraction I P x).mp (hJ (Ideal.subset_span (by simp)))
    refine ⟨⟨u, hu⟩, ?_⟩
    rwa [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
  | sup J₁ J₂ _ _ ih₁ ih₂ =>
    obtain ⟨u, hu⟩ := ih₁ (le_sup_left.trans hJ)
    obtain ⟨v, hv⟩ := ih₂ (le_sup_right.trans hJ)
    refine ⟨u * v, ?_⟩
    rw [Submonoid.coe_mul, ← Ideal.span_singleton_mul_span_singleton, Ideal.mul_sup]
    apply sup_le
    · rw [mul_comm (Ideal.span {(u : R)}) (Ideal.span {(v : R)}), mul_assoc]
      exact Ideal.mul_le_right.trans' (Ideal.mul_mono le_rfl hu)
    · rw [mul_assoc]
      exact Ideal.mul_le_right.trans' (Ideal.mul_mono le_rfl hv)
theorem unit_in_factor {P Q : Ideal R} [P.IsMaximal] {n : ℕ}
    (hn : P ^ n ≤ Q) {u : R} (hu : u ∉ P) :
    IsUnit (Ideal.Quotient.mk Q u) := by
  exact (Ideal.Quotient.isUnit_mk_pow_of_notMem (I := P) (n := n) hu).map (Ideal.Quotient.factor hn)
theorem eval_map_rational {k L : Type} [Field k] [Field L]
    (g : k →+* L) (y : Fin 4 → k) :
    (eval (fun i => g (y i))).comp (map g) = g.comp (eval y) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp
private theorem map_rationalIdeal {k L : Type} [Field k] [Field L]
    (g : k →+* L) (y : Fin 4 → k) :
    (rationalIdeal y).map (map g) = rationalIdeal (fun i => g (y i)) := by
  let Q := (rationalIdeal y).map (map g)
  let z : Fin 4 → L := fun i => g (y i)
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr ?_) ?_
  · intro p hp
    change (eval y) p = 0 at hp
    change eval z (map g p) = 0
    exact (DFunLike.congr_fun (eval_map_rational g y) p).trans (by simp [hp])
  · have h : Ideal.Quotient.mk Q =
        ((Ideal.Quotient.mk Q).comp C).comp (eval z) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        change Ideal.Quotient.mk Q (MvPolynomial.X i) = Ideal.Quotient.mk Q (C (eval z (MvPolynomial.X i)))
        rw [eval_X, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        have hi : MvPolynomial.X i - C (y i) ∈ rationalIdeal y := by
          change eval y (MvPolynomial.X i - C (y i)) = 0
          simp
        simpa [z] using Ideal.mem_map_of_mem (map g) hi
    intro p hp
    change eval z p = 0 at hp
    change p ∈ Q
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [DFunLike.congr_fun h p]
    simp [hp]
theorem contraction_baseChange {k L : Type} [Field k] [Field L]
    (g : k →+* L) (y : Fin 4 → k) (I : Ideal (Affine k))
    (hy : rationalIdeal y ∈ I.minimalPrimes) :
    let P := rationalIdeal (fun i => g (y i))
    P ∈ (I.map (map g)).minimalPrimes ∧
      localContraction (I.map (map g)) P = (localContraction I (rationalIdeal y)).map (map g) := by
  classical
  let p := rationalIdeal y
  let P := rationalIdeal (fun i => g (y i))
  let m : Affine k →+* Affine L := map g
  let J := I.map m
  let Q := localContraction I p
  let Q' := Q.map m
  let : P.IsMaximal := rational_isMaximal (fun i => g (y i))
  have hP : p.map m = P := map_rationalIdeal g y
  have hrad : Q.radical = p := contraction_radical I p hy
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p ^ n ≤ Q :=
    Ideal.exists_pow_le_of_le_radical_of_fg (le_of_eq hrad.symm) (IsNoetherian.noetherian _)
  have hpow : P ^ n ≤ Q' := by
    rw [← hP, ← Ideal.map_pow]
    exact Ideal.map_mono hn
  have hQ : Q' ≤ P := by
    rw [← hP]
    apply Ideal.map_mono
    exact hrad ▸ Ideal.le_radical
  have hJ : J ≤ Q' := Ideal.map_mono (fun _ hx => Ideal.mem_map_of_mem _ hx)
  obtain ⟨u, hu⟩ := common_denominator I p Q (IsNoetherian.noetherian _) le_rfl
  have huP : m (u : Affine k) ∈ P.primeCompl := by
    have hu0 : eval y (u : Affine k) ≠ 0 := u.prop
    change eval (fun i => g (y i)) (m (u : Affine k)) ≠ 0
    rw [show eval (fun i => g (y i)) (m (u : Affine k)) = g (eval y (u : Affine k)) from
      DFunLike.congr_fun (eval_map_rational g y) (u : Affine k)]
    exact fun h => hu0 (g.injective (h.trans (map_zero g).symm))
  have heq : localContraction J P = Q' := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨v, hv, hvx⟩ := (mem_localContraction J P x).mp hx
      have hzero : Ideal.Quotient.mk Q' v * Ideal.Quotient.mk Q' x = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        exact hJ hvx
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((unit_in_factor hpow hv).mul_left_cancel (hzero.trans (mul_zero _).symm))
    · intro x hx
      apply (mem_localContraction J P x).mpr
      refine ⟨m (u : Affine k), huP, ?_⟩
      have hu' := Ideal.map_mono (f := m) hu
      rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hu'
      exact hu' (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hx)
  refine ⟨⟨⟨inferInstance, hJ.trans hQ⟩, ?_⟩, heq⟩
  intro T hT hTP x hx
  apply hT.1.mem_of_pow_mem n
  apply (show Q' ≤ T from ?_) (hpow (Ideal.pow_mem_pow hx n))
  intro v hv
  have hv' : v ∈ localContraction J P := heq.symm ▸ hv
  obtain ⟨w, hw, hwv⟩ := (mem_localContraction J P v).mp hv'
  exact (hT.1.mem_or_mem (hT.2 hwv)).resolve_left (fun hwT => hw (hTP hwT))
end
end K1_13_7_5_3_3_2_1
end
section
namespace K1_13_7_5_3_3_2_2
open K1_13_7_5_3_3_2
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open scoped Pointwise Polynomial
private noncomputable abbrev parameter (k : Type) [CommRing k] : Family k :=
  MvPolynomial.C Polynomial.X
theorem zeroFibre_constantLift {k : Type} [Field k] (v : Affine k) :
    zeroFibre (MvPolynomial.map Polynomial.C v) = v :=
  MvPolynomial.map_leftInverse (fun _ : k => Polynomial.eval_C) v
theorem zeroFibre_surjective {k : Type} [Field k] :
    Function.Surjective (zeroFibre (k := k)) :=
  fun v => ⟨MvPolynomial.map Polynomial.C v, zeroFibre_constantLift v⟩
theorem ker_zeroFibre {k : Type} [Field k] :
    RingHom.ker (zeroFibre (k := k)) = Ideal.span {parameter k} := by
  classical
  apply le_antisymm
  · intro f hf
    have hz : zeroFibre f = 0 := hf
    have hx (m : Fin 4 →₀ ℕ) : Polynomial.X * (f.coeff m).divX = f.coeff m := by
      have he : (f.coeff m).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        have hh := congrArg (fun p : Affine k => p.coeff m) hz
        simpa only [zeroFibre, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero,
          Finsupp.zero_apply, Polynomial.coe_evalRingHom] using hh
      simpa only [he, Polynomial.C_0, add_zero] using Polynomial.X_mul_divX_add (f.coeff m)
    rw [Ideal.mem_span_singleton]
    refine ⟨∑ m ∈ f.support, MvPolynomial.monomial m (f.coeff m).divX, ?_⟩
    simp only [parameter, Finset.mul_sum, MvPolynomial.C_mul_monomial, hx,
      MvPolynomial.support_sum_monomial_coeff]
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp [parameter, zeroFibre]
private theorem variable_cancel {k : Type} [Field k] {s : Set (Fin 4)} {i : Fin 4}
    (hi : i ∉ s) (p : Affine k)
    (hp : MvPolynomial.X i * p ∈ span (MvPolynomial.X '' s)) :
    p ∈ span (MvPolynomial.X '' s) := by
  rw [mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hcoeff := coeff_X_mul m i p
  have hmem : Finsupp.single i 1 + m ∈ (MvPolynomial.X i * p).support :=
    mem_support_iff.mpr (hcoeff.trans_ne (mem_support_iff.mp hm))
  obtain ⟨j, hj, hne⟩ := hp _ hmem
  have hij : i ≠ j := fun e => hi (e.symm ▸ hj)
  exact ⟨j, hj, by simpa [Finsupp.add_apply, Finsupp.single_apply, hij] using hne⟩
private noncomputable abbrev coord (k : Type) [Field k] : Fin 4 → Affine k :=
  MvPolynomial.X
private theorem variables_weaklyRegular (k : Type) [Field k] :
    IsWeaklyRegular (Affine k) (List.ofFn (coord k)) := by
  classical
  refine ⟨?_⟩
  intro n hn
  have hn' : n < 4 := by simpa using hn
  let s : Set (Fin 4) := {j | j.val < n}
  have hprev : Ideal.ofList ((List.ofFn (coord k)).take n) •
      (⊤ : Submodule (Affine k) (Affine k)) = span (coord k '' s) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← Fin.ofFn_take_eq_take_ofFn hn'.le]
    apply congrArg (Ideal.span : Set (Affine k) → Ideal (Affine k))
    ext p
    change p ∈ List.ofFn (Fin.take n hn'.le (coord k)) ↔ p ∈ coord k '' s
    rw [List.mem_ofFn]
    exact ⟨fun ⟨j, hj⟩ => ⟨Fin.castLE hn'.le j, j.isLt, hj⟩,
      fun ⟨j, hj, he⟩ => ⟨⟨j.val, hj⟩, he⟩⟩
  rw [hprev]
  simpa only [List.getElem_ofFn] using
    (isSMulRegular_quotient_iff_mem_of_smul_mem (span (coord k '' s))
      (coord k ⟨n, hn'⟩)).mpr
      (variable_cancel (s := s) (i := ⟨n, hn'⟩) (Nat.lt_irrefl n))
private noncomputable def translation {k : Type} [Field k] (y : Fin 4 → k) :
    Affine k ≃ₐ[k] Affine k :=
  AlgEquiv.ofAlgHom (aeval (fun i => coord k i - C (y i)))
    (aeval (fun i => coord k i + C (y i)))
    (MvPolynomial.algHom_ext (fun i => by simp [coord]))
    (MvPolynomial.algHom_ext (fun i => by simp [coord]))
theorem translated_weaklyRegular {k : Type} [Field k] (y : Fin 4 → k) :
    IsWeaklyRegular (Affine k) (List.ofFn fun i => coord k i - C (y i)) := by
  let e := (translation y).toRingEquiv
  let rs := List.ofFn (coord k)
  have hcongr : List.Forall₂ (fun (r s : Affine k) => ∀ x : Affine k, e (r • x) = s • e x)
      rs (rs.map e) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => e.map_mul r x)
  have hwr := (e.toAddEquiv.isWeaklyRegular_congr hcongr).mp (variables_weaklyRegular k)
  simpa [rs, e, translation, coord, List.map_ofFn, Function.comp_def] using hwr
private theorem reference_sequence {k : Type} [Field k] (y : Fin 4 → k) :
    ∃ rs : List (Localization.AtPrime (liftedPoint y)), rs.length = 5 ∧
      (∀ a ∈ rs, a ∈ maximalIdeal (Localization.AtPrime (liftedPoint y))) ∧
      IsRegular (Localization.AtPrime (liftedPoint y)) rs := by
  let P := liftedPoint y
  let R := Localization.AtPrime P
  let ι := algebraMap (Family k) R
  let d : Fin 4 → Family k := fun i => MvPolynomial.map Polynomial.C (coord k i - C (y i))
  let rs := List.ofFn d
  let I : Ideal (Family k) := parameter k • (⊤ : Submodule (Family k) (Family k))
  have hI : I = RingHom.ker (zeroFibre (k := k)) := by
    change parameter k • (⊤ : Submodule (Family k) (Family k)) = _
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top, ker_zeroFibre]
  let e : Family k ⧸ I ≃+* Affine k :=
    (Ideal.quotEquivOfEq hI).trans
      (RingHom.quotientKerEquivOfSurjective zeroFibre_surjective)
  have he (x : Family k) : e (Ideal.Quotient.mk I x) = zeroFibre x := by
    change (RingHom.quotientKerEquivOfSurjective zeroFibre_surjective)
      (Ideal.quotEquivOfEq hI (Ideal.Quotient.mk I x)) = _
    rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hcongr : List.Forall₂ (fun (r : Family k) (s : Affine k) =>
      ∀ x : Family k ⧸ I, e (r • x) = s • e x) rs (rs.map zeroFibre) := by
    refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun a _ x => ?_)
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    change e (Ideal.Quotient.mk I (a * z)) = zeroFibre a * e (Ideal.Quotient.mk I z)
    rw [he, he, map_mul]
  have hzero : rs.map zeroFibre = List.ofFn (fun i => coord k i - C (y i)) := by
    simp only [rs, List.map_ofFn, Function.comp_def, d, zeroFibre_constantLift]
  have hreg : IsWeaklyRegular (Family k) (parameter k :: rs) := by
    rw [isWeaklyRegular_cons_iff]
    constructor
    · have ht : parameter k ≠ 0 := fun h => Polynomial.X_ne_zero
        (MvPolynomial.C_injective (Fin 4) k[X] (h.trans (map_zero MvPolynomial.C).symm))
      exact mul_right_injective₀ ht
    · change IsWeaklyRegular (Family k ⧸ I) rs
      apply (e.toAddEquiv.isWeaklyRegular_congr hcongr).mpr
      rw [hzero]
      exact translated_weaklyRegular y
  have hm (x : Family k) (hx : x ∈ parameter k :: rs) : x ∈ P := by
    rcases List.mem_cons.mp hx with rfl | hx
    · change MvPolynomial.eval y (zeroFibre (parameter k)) = 0
      simp [parameter, zeroFibre]
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      change MvPolynomial.eval y
        (zeroFibre (MvPolynomial.map Polynomial.C (coord k i - C (y i)))) = 0
      rw [zeroFibre_constantLift]
      simp [coord]
  refine ⟨(parameter k :: rs).map ι, by simp [rs], ?_,
    hreg.isRegular_of_isLocalization_of_mem R P hm⟩
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R P w).mpr (hm w hw)
theorem proof : K1_13_7_5_3_3_2.c2 := by
  classical
  intro k _ F y hmin r hr
  let P := liftedPoint y
  let R := Localization.AtPrime P
  let ι := algebraMap (Family k) R
  let J := equationIdeal F
  let front := List.ofFn fun i => ι (F i)
  let t := ι (parameter k)
  have hmap : J.map zeroFibre = equationIdeal (fun i => zeroFibre (F i)) :=
    equationIdeal_map _ F
  have hP : P ∈ (J ⊔ span {parameter k}).minimalPrimes := by
    have h := Ideal.minimalPrimes_comap_of_surjective zeroFibre_surjective (hmap.symm ▸ hmin)
    rw [Ideal.comap_map_of_surjective _ zeroFibre_surjective J,
      ← RingHom.ker_eq_comap_bot, ker_zeroFibre] at h
    exact h
  have hfront : Ideal.ofList front = J.map ι := by
    change Ideal.ofList front = (span (Set.range F)).map ι
    rw [Ideal.map_span, ← Set.range_comp]
    exact congrArg span (Set.ext (List.mem_ofFn' (fun i => ι (F i))))
  have hfull : Ideal.ofList (front ++ [t]) =
      (J ⊔ span {parameter k}).map ι := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton, hfront, Ideal.map_sup,
      Ideal.map_span, Set.image_singleton]
  have hrad : (Ideal.ofList (front ++ [t])).radical = maximalIdeal R := by
    rw [hfull, IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes R P _ hP]
    exact Localization.AtPrime.map_eq_maximalIdeal
  obtain ⟨rs, hlen, hm, hreg⟩ := reference_sequence y
  have hparams := weaklyRegular_of_parameters rs (front ++ [t])
    (by simpa [front] using hlen) hm hreg hrad
  have hlast := ((isWeaklyRegular_append_iff R front [t]).mp hparams).2
  have hc := (isWeaklyRegular_singleton_iff _ _).mp hlast
  rw [Ideal.smul_eq_mul, Ideal.mul_top, hfront] at hc
  change ι r ∈ J.map ι
  apply mem_of_isSMulRegular_quotient_of_smul_mem hc
  change t * ι r ∈ J.map ι
  rw [← map_mul]
  exact hr
end K1_13_7_5_3_3_2_2
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_4
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_5_3 K1_13_7_5_3_3
open K1_13_5_4_2_4 (corner exponentCount latticeBody)
open K1_13_6_1_4_2 (exponents)
open scoped BigOperators Pointwise
theorem mem_cap (p : Shape) (x : RealJets) :
    x ∈ capBody p ↔ (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 ≤ p.b ∧
      x 1 + 2 * x 2 + 3 * x 3 ≤ p.j ∧ x 3 ≤ p.t := by
  norm_num [capBody, Fin.sum_univ_four]
theorem mem_support (p : Shape) (e : Exponent) :
    e ∈ doubledSupport p ↔ (fun i => e i) ∈ exponents (p.scale 2) := by
  simp [K1_13_7_5_3_3.Fits, exponents, Fin.sum_univ_four]
private theorem support_zero : (↑(doubledSupport ⟨0, 0, 0⟩) : Set Exponent) = 0 := by
  ext e
  rw [Finset.mem_coe, mem_support]
  change (fun i => e i) ∈ exponents ⟨0, 0, 0⟩ ↔ _
  rw [K1_13_6_1_4_2.exponents_zero, Set.mem_singleton_iff, Set.mem_zero]
  exact ⟨fun h => Finsupp.ext (congrFun h), fun h => by subst e; rfl⟩
theorem support_plus {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    (↑(doubledSupport (p.plus q)) : Set Exponent) =
      (↑(doubledSupport p) : Set Exponent) + (↑(doubledSupport q) : Set Exponent) := by
  ext e
  rw [Finset.mem_coe, mem_support]
  rw [show (p.plus q).scale 2 = (p.scale 2).plus (q.scale 2) by
    cases p
    cases q
    simp [Shape.plus, Shape.scale, Nat.mul_add]]
  rw [K1_13_6_1_4_2.exponents_plus _ _
    (K1_13_6_1_4_2.chamber_scale hp 2) (K1_13_6_1_4_2.chamber_scale hq 2)
    (by simp [Shape.scale]) (by simp [Shape.scale]) (by simp [Shape.scale])]
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    refine ⟨Finsupp.equivFunOnFinite.symm u, (mem_support _ _).mpr hu,
      Finsupp.equivFunOnFinite.symm v, (mem_support _ _).mpr hv, ?_⟩
    ext i
    exact congrFun he i
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨fun i => u i, (mem_support _ _).mp hu, fun i => v i, (mem_support _ _).mp hv, rfl⟩
theorem support_scale {p : Shape} (hp : Chamber p) (n : ℕ) :
    (↑(doubledSupport (p.scale n)) : Set Exponent) = n • (↑(doubledSupport p) : Set Exponent) := by
  induction n with
  | zero => simpa [Shape.scale] using
      support_zero.trans (zero_smul ℕ (↑(doubledSupport p) : Set Exponent)).symm
  | succ n ih =>
      rw [show p.scale (n + 1) = (p.scale n).plus p by
        cases p
        simp [Shape.scale, Shape.plus, Nat.add_mul]]
      rw [support_plus (K1_13_6_1_4_2.chamber_scale hp n) hp, ih, succ_nsmul]
def shapeSum (S : Finset (Fin 4)) (B : Fin 4 → Shape) : Shape :=
  ⟨∑ i ∈ S, (B i).b, ∑ i ∈ S, (B i).j, ∑ i ∈ S, (B i).t⟩
theorem shapeSum_chamber {B : Fin 4 → Shape} (hB : ∀ i, Chamber (B i)) (S : Finset (Fin 4)) :
    Chamber (shapeSum S B) := by
  constructor
  · exact Finset.sum_le_sum fun i _ => (hB i).1
  · simp only [shapeSum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hB i).2
private theorem shapeSum_insert {S : Finset (Fin 4)} {i : Fin 4} (hi : i ∉ S)
    (B : Fin 4 → Shape) :
    shapeSum (insert i S) B = (B i).plus (shapeSum S B) := by
  simp [shapeSum, Shape.plus, Finset.sum_insert hi]
private theorem support_sum (B : Fin 4 → Shape) (hB : ∀ i, Chamber (B i)) (S : Finset (Fin 4)) :
    (∑ i ∈ S, (↑(doubledSupport (B i)) : Set Exponent)) =
      (↑(doubledSupport (shapeSum S B)) : Set Exponent) := by
  induction S using Finset.induction_on with
  | empty => simpa [shapeSum] using support_zero.symm
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, ih, shapeSum_insert hi,
        support_plus (hB i) (shapeSum_chamber hB S)]
theorem body_sum (B : Fin 4 → Shape) (hB : ∀ i, Chamber (B i)) (S : Finset (Fin 4)) :
    (∑ i ∈ S, latticeBody (doubledSupport (B i))) = capBody ((shapeSum S B).scale 2) := by
  induction S using Finset.induction_on with
  | empty => simpa [shapeSum, Shape.scale, ← Set.singleton_zero] using capBody_zero.symm
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, ih, latticeBody_doubledSupport _ (hB i), shapeSum_insert hi]
      rw [show ((B i).plus (shapeSum S B)).scale 2 =
          ((B i).scale 2).plus ((shapeSum S B).scale 2) by
        cases B i
        cases shapeSum S B
        simp [Shape.plus, Shape.scale, Nat.mul_add]]
      exact (capBody_plus _ _
        (K1_13_6_1_4_2.chamber_scale (hB i) 2)
        (K1_13_6_1_4_2.chamber_scale (shapeSum_chamber hB S) 2)).symm
theorem shapeSum_corner (B : Fin 4 → Shape) (b n : ℕ) (S : Finset (Fin 4)) :
    shapeSum Finset.univ (fun i => (B i).scale (corner b n S i)) =
      ((shapeSum S B).scale n).plus ((shapeSum Finset.univ B).scale b) := by
  classical
  have split_sum (f : Fin 4 → ℕ) :
      (∑ i, corner b n S i * f i) = n * (∑ i ∈ S, f i) + b * (∑ i, f i) := by
    simp only [corner, Nat.add_mul, ite_mul, Nat.zero_mul, Finset.sum_add_distrib, Finset.mul_sum]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, add_comm]
  unfold shapeSum Shape.scale Shape.plus
  rw [split_sum, split_sum, split_sum]
theorem exponentCount_corner (B : Fin 4 → Shape) (hB : ∀ i, Chamber (B i)) (b n : ℕ)
    (S : Finset (Fin 4)) :
    exponentCount (fun i => doubledSupport (B i)) (corner b n S) =
      (doubledSupport (((shapeSum S B).scale n).plus ((shapeSum Finset.univ B).scale b))).card := by
  unfold exponentCount
  simp_rw [← support_scale (hB _) _]
  rw [support_sum _ (fun i => K1_13_6_1_4_2.chamber_scale (hB i) _),
    shapeSum_corner, Set.ncard_coe_finset]
end
end K1_13_7_5_3_3_4
end
section
namespace K1_13_7_5_3_3_1
open K1_13_7 K1_13_7_5 K1_13_7_5_3
open K1_13_7_5_3_3 (PointLocal)
open K1_13_7_4_2 (remainingIdeal)
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open scoped Pointwise
private noncomputable abbrev coord : Fin 4 → Jets := MvPolynomial.X
private theorem variable_cancel {s : Set (Fin 4)} {i : Fin 4} (hi : i ∉ s)
    (p : Jets) (hp : coord i * p ∈ span (coord '' s)) : p ∈ span (coord '' s) := by
  rw [mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hcoeff := coeff_X_mul m i p
  have hmem : Finsupp.single i 1 + m ∈ (coord i * p).support :=
    mem_support_iff.mpr (hcoeff.trans_ne (mem_support_iff.mp hm))
  obtain ⟨j, hj, hne⟩ := hp _ hmem
  have hij : i ≠ j := fun e => hi (e.symm ▸ hj)
  exact ⟨j, hj, by simpa [Finsupp.add_apply, Finsupp.single_apply, hij] using hne⟩
private theorem variables_weaklyRegular : IsWeaklyRegular Jets (List.ofFn coord) := by
  classical
  refine ⟨?_⟩
  intro n hn
  have hn' : n < 4 := by simpa using hn
  let s : Set (Fin 4) := {j | j.val < n}
  have hprev : Ideal.ofList ((List.ofFn coord).take n) • (⊤ : Submodule Jets Jets) =
      span (coord '' s) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← Fin.ofFn_take_eq_take_ofFn hn'.le]
    apply congrArg (Ideal.span : Set Jets → Ideal Jets)
    ext p
    change p ∈ List.ofFn (Fin.take n hn'.le coord) ↔ p ∈ coord '' s
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.castLE hn'.le j, j.isLt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j.val, hj⟩, rfl⟩
  rw [hprev]
  simpa only [List.getElem_ofFn] using
    (isSMulRegular_quotient_iff_mem_of_smul_mem (span (coord '' s)) (coord ⟨n, hn'⟩)).mpr
      (variable_cancel (s := s) (i := ⟨n, hn'⟩) (Nat.lt_irrefl n))
private noncomputable def translation (y : JetPoint) : Jets ≃ₐ[GeometricX] Jets :=
  AlgEquiv.ofAlgHom (aeval (fun i => coord i - C (y i))) (aeval (fun i => coord i + C (y i)))
    (MvPolynomial.algHom_ext (fun i => by simp))
    (MvPolynomial.algHom_ext (fun i => by simp))
private theorem reference_sequence (y : JetPoint) :
    ∃ rs : List (PointLocal y), rs.length = 4 ∧
      (∀ a ∈ rs, a ∈ maximalIdeal (PointLocal y)) ∧ IsRegular (PointLocal y) rs := by
  let e := (translation y).toRingEquiv
  let rs := List.ofFn coord
  let p := (pointPrime y).asIdeal
  have hcongr : List.Forall₂ (fun (r s : Jets) => ∀ x : Jets, e (r • x) = s • e x)
      rs (rs.map e) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => e.map_mul r x)
  have hwr : IsWeaklyRegular Jets (rs.map e) :=
    (e.toAddEquiv.isWeaklyRegular_congr hcongr).mp variables_weaklyRegular
  have hm (x : Jets) (hx : x ∈ rs.map e) : x ∈ p := by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    change MvPolynomial.eval y (aeval (fun j => coord j - C (y j)) (coord i)) = 0
    simp [coord]
  refine ⟨(rs.map e).map (algebraMap Jets (PointLocal y)), by simp [rs], ?_,
    hwr.isRegular_of_isLocalization_of_mem (PointLocal y) p hm⟩
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (PointLocal y) p w).mpr (hm w hw)
theorem proof : K1_13_7_5_3_3.c1 := by
  classical
  intro y g hrad i x hx
  let R := PointLocal y
  let _ : Algebra GeometricX R :=
    ((algebraMap Jets R).comp (algebraMap GeometricX Jets)).toAlgebra
  let e := Equiv.swap (Fin.last 3) i
  have hei : e (Fin.last 3) = i := Equiv.swap_apply_left _ _
  let f : Fin 4 → R := g ∘ e
  let front : List R := List.ofFn fun j : Fin 3 => f j.castSucc
  have hfull : Ideal.ofList (List.ofFn f) = span (Set.range g) := by
    rw [← EquivLike.range_comp g e]
    exact congrArg span (Set.ext (List.mem_ofFn' f))
  have hfront : Ideal.ofList front = remainingIdeal g i := by
    unfold remainingIdeal
    apply congrArg (Ideal.span : Set R → Ideal R)
    ext z
    change z ∈ List.ofFn (fun j : Fin 3 => f j.castSucc) ↔ z ∈ g '' {j | j ≠ i}
    rw [List.mem_ofFn' (fun j : Fin 3 => f j.castSucc)]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j.castSucc, fun h => Fin.castSucc_ne_last j (e.injective (h.trans hei.symm)), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨l, rfl⟩ := e.surjective j
      rcases Fin.eq_castSucc_or_eq_last l with ⟨m, rfl⟩ | rfl
      · exact ⟨m, rfl⟩
      · exact (hj hei).elim
  obtain ⟨rs, hlen, hmem, hreg⟩ := reference_sequence y
  have hparams := weaklyRegular_of_parameters (k := GeometricX) rs (List.ofFn f)
    (by simpa using hlen) hmem hreg (hfull ▸ hrad)
  rw [List.ofFn_succ', List.concat_eq_append] at hparams
  have hlast := ((isWeaklyRegular_append_iff R front [f (Fin.last 3)]).mp hparams).2
  have hc := (isWeaklyRegular_singleton_iff _ _).mp hlast
  rw [Ideal.smul_eq_mul, Ideal.mul_top, hfront] at hc
  exact mem_of_isSMulRegular_quotient_of_smul_mem hc
    (by simpa only [f, Function.comp_apply, hei, smul_eq_mul] using hx)
end K1_13_7_5_3_3_1
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_2_1
open K1_13_7 (GeometricX)
open K1_13_7_5 (Jets JetPoint)
open K1_13_5_4_2 (pointIdeal pointLength)
open K1_13_5_4_2_4 (cutIdeal)
open K1_13_7_5_3_3_2 (Affine rationalIdeal equationIdeal localContraction quotientBaseChange)
open MvPolynomial IsLocalRing
open scoped TensorProduct
noncomputable section
def localFactorEquiv (k : Type) [Field k] (I : Ideal (Affine k))
    (y : Fin 4 → k) (hy : rationalIdeal y ∈ I.minimalPrimes) :
    let P := rationalIdeal y
    let S := Localization.AtPrime P
    (Affine k ⧸ localContraction I P) ≃ₐ[k] S ⧸ I.map (algebraMap (Affine k) S) := by
  let P := rationalIdeal y
  let S := Localization.AtPrime P
  let J := I.map (algebraMap (Affine k) S)
  let Q := localContraction I P
  let : P.IsMaximal := rational_isMaximal y
  let a := IsScalarTower.toAlgHom k (Affine k) S
  let φ : Affine k ⧸ Q →ₐ[k] S ⧸ J := Ideal.quotientMapₐ J a le_rfl
  refine AlgEquiv.ofBijective φ ⟨Ideal.quotientMap_injective, ?_⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, maximalIdeal S ^ n ≤ J := by
    apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Ideal.fg_of_isNoetherianRing _)
    rw [show J.radical = P.map (algebraMap (Affine k) S) from
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes S P I hy,
      Localization.AtPrime.map_eq_maximalIdeal]
  intro b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨x, hx⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdealPow P S n).surjective
    (Ideal.Quotient.mk (maximalIdeal S ^ n) b)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk] at hx
  exact ⟨Ideal.Quotient.mk Q x, congrArg (Ideal.Quotient.factor hn) hx⟩
theorem residue_length_one (k : Type) [Field k] (y : Fin 4 → k) :
    Module.length (ResidueField k) (ResidueField (Localization.AtPrime (rationalIdeal y))) = 1 := by
  let P := rationalIdeal y
  let S := Localization.AtPrime P
  let : P.IsMaximal := rational_isMaximal y
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal P S
  have hs : Function.Surjective (algebraMap k (ResidueField S)) := by
    intro z
    obtain ⟨a, ha⟩ := e.surjective z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hc : Ideal.Quotient.mk P (C (eval y a)) = Ideal.Quotient.mk P a := by
      apply Ideal.Quotient.eq.mpr
      change eval y (C (eval y a) - a) = 0
      simp
    refine ⟨eval y a, ?_⟩
    rw [← ha, ← hc, show e = IsLocalization.AtPrime.equivQuotMaximalIdeal P S from rfl,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
      IsScalarTower.algebraMap_apply k S (ResidueField S),
      IsScalarTower.algebraMap_apply k (Affine k) S, MvPolynomial.algebraMap_eq]
    rfl
  have hs' : Function.Surjective (algebraMap (ResidueField k) (ResidueField S)) := by
    intro z
    obtain ⟨a, ha⟩ := hs z
    exact ⟨residue k a, ha⟩
  rw [Module.length_eq_of_surjective hs', Module.length_eq_one]
theorem original_factor (I : Ideal Jets) (y : JetPoint) (hy : pointIdeal y ∈ I.minimalPrimes) :
    let Q := localContraction I (rationalIdeal y)
    Module.Finite GeometricX (Jets ⧸ Q) ∧
      Module.finrank GeometricX (Jets ⧸ Q) = (pointLength I y).toNat := by
  let k := GeometricX
  let P := rationalIdeal y
  let S := Localization.AtPrime P
  let J := I.map (algebraMap Jets S)
  let Q := localContraction I P
  have hP : pointIdeal y = P := K1_13_7_5_3_3.pointIdeal_eq y
  have hy' : P ∈ I.minimalPrimes := hP ▸ hy
  let e : (Jets ⧸ Q) ≃ₐ[k] S ⧸ J := localFactorEquiv k I y hy'
  have hpoint : pointLength I y = Module.length S (S ⧸ J) := by
    rw [K1_13_7_5_3_3.pointLength_eq]
    rfl
  have hlen : Module.length k (S ⧸ J) = pointLength I y := by
    rw [IsLocalRing.length_restrictScalars k S, residue_length_one k y, mul_one, hpoint]
  have hfin : Module.length k (S ⧸ J) ≠ ⊤ := by
    rw [hlen, K1_13_7_5_3_3.pointLength_eq]
    exact K1_13_7_5_3_3.pointLength_ne_top hy'
  let : IsNoetherian k (S ⧸ J) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hfin)).1
  let : Module.Finite k (S ⧸ J) := ⟨IsNoetherian.noetherian _⟩
  refine ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective, ?_⟩
  rw [e.toLinearEquiv.finrank_eq, ← hlen, Module.length_eq_finrank, ENat.toNat_natCast]
theorem proof : K1_13_7_5_3_3_2.c1 := by
  intro k _ _ f y hy
  let K := GeometricX
  let P := rationalIdeal y
  let Q := localContraction (cutIdeal f) P
  let m : Affine K →+* Affine k := map (algebraMap K k)
  have hP : pointIdeal y = P := K1_13_7_5_3_3.pointIdeal_eq y
  have hp : P ∈ (cutIdeal f).minimalPrimes := hP ▸ hy
  have hi : (cutIdeal f).map m = equationIdeal (fun i => m (f i)) :=
    K1_13_7_5_3_3_2.equationIdeal_map _ f
  obtain ⟨hmin, hQ⟩ := contraction_baseChange (algebraMap K k) y (cutIdeal f) hp
  change _ ∈ ((cutIdeal f).map m).minimalPrimes at hmin
  rw [hi] at hmin hQ
  obtain ⟨hfin, hlen⟩ := original_factor (cutIdeal f) y hy
  let : Module.Finite K (Affine K ⧸ Q) := hfin
  let e : k ⊗[K] (Affine K ⧸ Q) ≃ₐ[k] Affine k ⧸ Q.map m := quotientBaseChange K k Q
  refine ⟨hmin, ?_⟩
  rw [hQ]
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    e.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_baseChange.trans hlen)⟩
end
end K1_13_7_5_3_3_2_1
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_4
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_5_3 K1_13_7_5_3_3
open Filter MeasureTheory Set
open scoped BigOperators ENNReal Function Pointwise Topology
private def cell (e : Exponent) : Set RealJets :=
  Set.pi Set.univ fun i => Set.Ico (e i : ℝ) ((e i : ℝ) + 1)
private def cells (p : Shape) : Set RealJets :=
  ⋃ e ∈ doubledSupport p, cell e
theorem cell_disjoint : Pairwise (Disjoint on cell) := by
  intro e f hef
  refine Set.disjoint_left.mpr fun x hx hy => hef (Finsupp.ext fun i => ?_)
  exact (Nat.floor_eq_on_Ico (e i) _ (hx i (Set.mem_univ i))).symm.trans
    (Nat.floor_eq_on_Ico (f i) _ (hy i (Set.mem_univ i)))
private theorem volume_cells (p : Shape) : volume (cells p) = (doubledSupport p).card := by
  unfold cells
  rw [measure_biUnion_finset (fun _ _ _ _ h => cell_disjoint h)]
  · have hcell (e : Exponent) : volume (cell e) = 1 := by
      simp [cell, Real.volume_pi_Ico]
    simp [hcell]
  · intro e _
    exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
private theorem cap_subset_cells (p : Shape) : capBody (p.scale 2) ⊆ cells p := by
  intro x hx
  obtain ⟨hx₀, hxb, hxj, hxt⟩ := (mem_cap _ _).mp hx
  let e : Exponent := Finsupp.equivFunOnFinite.symm fun i => ⌊x i⌋₊
  have hle (i : Fin 4) : (e i : ℝ) ≤ x i := Nat.floor_le (hx₀ i)
  have hmem : e ∈ doubledSupport p := by
    apply (mem_support p e).mpr
    change e 0 + e 1 + e 2 + e 3 ≤ (p.scale 2).b ∧
      e 1 + 2 * e 2 + 3 * e 3 ≤ (p.scale 2).j ∧ e 3 ≤ (p.scale 2).t
    refine ⟨?_, ?_, ?_⟩
    · exact_mod_cast (show (e 0 : ℝ) + e 1 + e 2 + e 3 ≤ (p.scale 2).b by
        linarith [hle 0, hle 1, hle 2, hle 3])
    · exact_mod_cast (show (e 1 : ℝ) + 2 * e 2 + 3 * e 3 ≤ (p.scale 2).j by
        linarith [hle 1, hle 2, hle 3])
    · exact_mod_cast (hle 3).trans hxt
  exact Set.mem_iUnion₂.mpr ⟨e, hmem, fun i _ => ⟨hle i, Nat.lt_floor_add_one (x i)⟩⟩
private theorem cells_subset_cap (p : Shape) :
    cells p ⊆ capBody ((p.scale 2).plus ⟨6, 6, 1⟩) := by
  intro x hx
  obtain ⟨e, he, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨heb, hej, het⟩ :
      e 0 + e 1 + e 2 + e 3 ≤ (p.scale 2).b ∧
      e 1 + 2 * e 2 + 3 * e 3 ≤ (p.scale 2).j ∧ e 3 ≤ (p.scale 2).t :=
    (mem_support p e).mp he
  have hb : (e 0 : ℝ) + e 1 + e 2 + e 3 ≤ (p.scale 2).b := by exact_mod_cast heb
  have hj : (e 1 : ℝ) + 2 * e 2 + 3 * e 3 ≤ (p.scale 2).j := by exact_mod_cast hej
  have ht : (e 3 : ℝ) ≤ (p.scale 2).t := by exact_mod_cast het
  have h (i : Fin 4) : (e i : ℝ) ≤ x i ∧ x i < (e i : ℝ) + 1 := hx i (Set.mem_univ i)
  apply (mem_cap _ _).mpr
  refine ⟨fun i => (Nat.cast_nonneg _).trans (h i).1, ?_, ?_, ?_⟩ <;>
    simp only [Shape.plus, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] <;>
    linarith [(h 0).2, (h 1).2, (h 2).2, (h 3).2]
theorem cap_volume_ne_top (p : Shape) : volume (capBody p) ≠ ∞ := by
  have hsubset : capBody p ⊆ Set.Icc (0 : RealJets) (fun _ => (p.b : ℝ)) := by
    intro x hx
    refine ⟨hx.1, fun i => ?_⟩
    exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2.1
  refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
  rw [Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
theorem count_bounds (p : Shape) :
    (volume (capBody (p.scale 2))).toReal ≤ (doubledSupport p).card ∧
      ((doubledSupport p).card : ℝ) ≤
        (volume (capBody ((p.scale 2).plus ⟨6, 6, 1⟩))).toReal := by
  have hlo := measure_mono (μ := volume) (cap_subset_cells p)
  have hhi := measure_mono (μ := volume) (cells_subset_cap p)
  rw [volume_cells] at hlo hhi
  exact ⟨by simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo,
    by simpa using ENNReal.toReal_mono (cap_volume_ne_top _) hhi⟩
def volumePolynomial (b j t : ℝ) : ℝ :=
  (8*b*j^2*t - 24*b*j*t^2 + 24*b*t^3 - 4*j^3*t + 14*j^2*t^2 - 20*j*t^3 + 9*t^4) / 32
theorem cap_volume (p : Shape) (hp : Chamber p) :
    (volume (capBody p)).toReal = volumePolynomial p.b p.j p.t := by
  have h := K1_13_7_5_3_4.proof p hp
  change 32 * (volume (capBody p)).toReal = (volume32 p : ℝ) at h
  rw [show (volume (capBody p)).toReal = (volume32 p : ℝ) / 32 by linarith]
  unfold volume32 volumePolynomial
  push_cast
  rfl
theorem tendsto_volume (p u : Shape) (hp : Chamber p) (hu : Chamber u) :
    Tendsto (fun n : ℕ => (volume (capBody ((p.scale n).plus u))).toReal / (n : ℝ)^4)
      atTop (𝓝 (volume (capBody p)).toReal) := by
  let f (r : ℝ) :=
    volumePolynomial (p.b + u.b * r) (p.j + u.j * r) (p.t + u.t * r)
  have hf : Continuous f := by
    unfold f volumePolynomial
    fun_prop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  rw [cap_volume p hp, show volumePolynomial p.b p.j p.t = f 0 by simp [f]]
  refine ((hf.tendsto 0).comp hi).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  rw [cap_volume _ (K1_13_6_1_4_2.chamber_plus (K1_13_6_1_4_2.chamber_scale hp _) hu)]
  change f (n : ℝ)⁻¹ = _
  simp only [f, Shape.scale, Shape.plus, Nat.cast_add, Nat.cast_mul, volumePolynomial]
  field_simp
theorem tendsto_count (p u : Shape) (hp : Chamber p) (hu : Chamber u) :
    Tendsto (fun n : ℕ => ((doubledSupport ((p.scale n).plus u)).card : ℝ) / (n : ℝ)^4)
      atTop (𝓝 (volume (capBody (p.scale 2))).toReal) := by
  have hshape (n : ℕ) : ((p.scale n).plus u).scale 2 = ((p.scale 2).scale n).plus (u.scale 2) := by
    cases p
    cases u
    simp [Shape.scale, Shape.plus, Nat.mul_add, Nat.mul_left_comm]
  have hp₂ := K1_13_6_1_4_2.chamber_scale hp 2
  have hu₂ := K1_13_6_1_4_2.chamber_scale hu 2
  have hpadding : Chamber (⟨6, 6, 1⟩ : Shape) := by norm_num [Chamber]
  have hplus (a b c : Shape) : (a.plus b).plus c = a.plus (b.plus c) := by
    cases a
    cases b
    cases c
    simp [Shape.plus, Nat.add_assoc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_volume _ _ hp₂ hu₂)
    (tendsto_volume _ _ hp₂ (K1_13_6_1_4_2.chamber_plus hu₂ hpadding))
    (fun n => ?_) (fun n => ?_)
  · exact div_le_div_of_nonneg_right (by simpa only [hshape] using (count_bounds ((p.scale n).plus u)).1)
      (by positivity)
  · exact div_le_div_of_nonneg_right
      (by simpa only [hshape, hplus] using (count_bounds ((p.scale n).plus u)).2)
      (by positivity)
end
end K1_13_7_5_3_3_4
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_4
open K1_13 K1_13_7_1 K1_13_7_5_3_3
open K1_13_5_4_2_4 (corner exponentCount latticeBody)
open Filter MeasureTheory
open scoped BigOperators Pointwise Topology
theorem proof : K1_13_7_5_3_3.c4 := by
  intro p q H hp hq hH b S
  let B : Fin 4 → Shape := ![p, q, q, H]
  have hB (i : Fin 4) : Chamber (B i) := by
    fin_cases i <;> assumption
  have hA : supports p q H = fun i => doubledSupport (B i) := by
    funext i
    fin_cases i <;> rfl
  change Tendsto (fun n : ℕ => (exponentCount (supports p q H) (corner b n S) : ℝ) / (n : ℝ)^4)
    atTop (𝓝 (volume (∑ i ∈ S, latticeBody (supports p q H i))).toReal)
  simp_rw [hA, exponentCount_corner B hB b, body_sum B hB S]
  exact tendsto_count _ _ (shapeSum_chamber hB S)
    (K1_13_6_1_4_2.chamber_scale (shapeSum_chamber hB Finset.univ) b)
end K1_13_7_5_3_3_4
end
section
namespace K1_13_3
noncomputable section
open K1_13
open scoped BigOperators
private abbrev Exponent := Fin 4 →₀ ℕ
private def slots (b j : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (min b (j / 3) + 1)).biUnion (fun z =>
    (Finset.range (min (b - z) ((j - 3 * z) / 2) + 1)).biUnion (fun y =>
      (Finset.range (min (b - z - y) (j - 3 * z - 2 * y) + 1)).biUnion (fun x =>
        (Finset.range (b - z - y - x + 1)).image (fun v => (z, y, x, v)))))
private def slotExponent (q : ℕ × ℕ × ℕ × ℕ) : Exponent :=
  Finsupp.equivFunOnFinite.symm ![q.2.2.2, q.2.2.1, q.2.1, q.1]
private theorem slots_card (b j : ℕ) : (slots b j).card ≤ symbols b j := by
  unfold slots symbols
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun z _ => ?_)
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ => ?_)
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun x _ => ?_)
  exact Finset.card_image_le.trans_eq (Finset.card_range _)
theorem exponent_mem_slots (b j : ℕ) (m : Exponent)
    (hb : m.sum (fun _ a => a) ≤ b) (hj : m.sum (fun i a => i.val * a) ≤ j) :
    m ∈ (slots b j).image slotExponent := by
  classical
  have htotal : m 0 + m 1 + m 2 + m 3 ≤ b := by
    simp [Finsupp.sum_fintype, Fin.sum_univ_succ] at hb
    omega
  have hindex : m 1 + 2 * m 2 + 3 * m 3 ≤ j := by
    simp [Finsupp.sum_fintype, Fin.sum_univ_succ] at hj
    omega
  refine Finset.mem_image.mpr ⟨(m 3, m 2, m 1, m 0), ?_, ?_⟩
  · unfold slots
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    exact ⟨m 3, by omega, m 2, by omega, m 1, by omega, m 0, by omega, rfl⟩
  · ext i
    fin_cases i <;> simp [slotExponent]
theorem count_independent (b j r : ℕ) (e : Fin r → Symbol)
    (hli : LinearIndependent Geom e)
    (hcap : ∀ i, (e i).totalDegree ≤ b ∧ symbolIndex (e i) ≤ j) :
    r ≤ symbols b j := by
  classical
  let A := (slots b j).image slotExponent
  let V := MvPolynomial.restrictSupport Geom (↑A : Set Exponent)
  have hmem (i : Fin r) : e i ∈ V := by
    change (↑(e i).support : Set Exponent) ⊆ (↑A : Set Exponent)
    intro m hm
    have hb : m.sum (fun _ a => a) ≤ (e i).totalDegree := MvPolynomial.le_totalDegree hm
    have hj : m.sum (fun i a => i.val * a) ≤ symbolIndex (e i) :=
      Finset.le_sup (f := fun u : Exponent => u.sum (fun i a => i.val * a)) hm
    exact exponent_mem_slots b j m (hb.trans (hcap i).1) (hj.trans (hcap i).2)
  let : Module.Finite Geom V := MvPolynomial.restrictSupport_finite A.finite_toSet
  have hi : LinearIndependent Geom (fun i => (⟨e i, hmem i⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hli
  have hd : r ≤ Module.finrank Geom V := by simpa using hi.fintype_card_le_finrank
  rw [MvPolynomial.finrank_restrictSupport_finset] at hd
  exact hd.trans (Finset.card_image_le.trans (slots_card b j))
private theorem index_eq_weighted (P : Symbol) :
    symbolIndex P = MvPolynomial.weightedTotalDegree Fin.val P := by
  unfold symbolIndex MvPolynomial.weightedTotalDegree
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
private theorem weighted_pow (w : Fin 4 → ℕ) (P : Symbol) (hP : P ≠ 0) (a : ℕ) :
    MvPolynomial.weightedTotalDegree w (P ^ a) =
      a * MvPolynomial.weightedTotalDegree w P := by
  induction a with
  | zero => rw [pow_zero, zero_mul, ← MvPolynomial.C_1, MvPolynomial.weightedTotalDegree_C]
  | succ a ih =>
    rw [pow_succ, MvPolynomial.weightedTotalDegree_mul w _ _ (pow_ne_zero _ hP) hP,
      ih, Nat.succ_mul]
theorem cofactor_rank (n : ℕ) (F : Fin n → Symbol) (a : Fin n → ℕ) (hF : ∀ i, F i ≠ 0)
    (r : ℕ) (e : Fin r → Symbol) (hli : LinearIndependent Geom e)
    (hcap : ∀ i, (e i).totalDegree ≤ 4012 ∧ symbolIndex (e i) ≤ 1650 ∧
      (∏ j, F j ^ a j) ∣ e i) :
    r ≤ remaining (∑ j, a j * (F j).totalDegree) (∑ j, a j * symbolIndex (F j)) := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  let P := ∏ i, F i ^ a i
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hF i)
  let b := ∑ j, a j * (F j).totalDegree
  let j := ∑ i, a i * symbolIndex (F i)
  have hdeg (w : Fin 4 → ℕ) : MvPolynomial.weightedTotalDegree w P =
      ∑ i, a i * MvPolynomial.weightedTotalDegree w (F i) := by
    rw [MvPolynomial.weightedTotalDegree_prod w Finset.univ _ (fun i _ => pow_ne_zero _ (hF i))]
    exact Finset.sum_congr rfl fun i _ => weighted_pow w (F i) (hF i) (a i)
  have hb : P.totalDegree = b := by
    simpa only [MvPolynomial.weightedTotalDegree_one] using hdeg (1 : Fin 4 → ℕ)
  have hj : symbolIndex P = j := by
    simpa only [j, index_eq_weighted] using hdeg Fin.val
  choose Q hQ using fun i => (hcap i).2.2
  have hQ_ne (i : Fin r) : Q i ≠ 0 := by
    intro hz
    exact hli.ne_zero i (by rw [hQ i, hz, mul_zero])
  have hliQ : LinearIndependent Geom Q := by
    refine LinearIndependent.of_comp (LinearMap.mulLeft Geom P) ?_
    have heq : (LinearMap.mulLeft Geom P) ∘ Q = e := funext fun i => (hQ i).symm
    rwa [heq]
  have hbounds (i : Fin r) :
      b + (Q i).totalDegree ≤ 4012 ∧ j + symbolIndex (Q i) ≤ 1650 := by
    obtain ⟨ht, hi, _⟩ := hcap i
    have heq : e i = P * Q i := hQ i
    rw [heq, MvPolynomial.totalDegree_mul_of_isDomain hP (hQ_ne i), hb] at ht
    rw [heq, index_eq_weighted, MvPolynomial.weightedTotalDegree_mul _ _ _ hP (hQ_ne i),
      ← index_eq_weighted, ← index_eq_weighted, hj] at hi
    exact ⟨ht, hi⟩
  have h0 := hbounds ⟨0, Nat.pos_of_ne_zero hr⟩
  have hb0 : b ≤ 4012 := by omega
  have hj0 : j ≤ 1650 := by omega
  change r ≤ remaining b j
  simp only [remaining, hb0, hj0, and_self, ite_true]
  exact count_independent _ _ r Q hliQ fun i => by
    have h := hbounds i
    omega
end
end K1_13_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 8
namespace K1_14_3R_3_2_2
noncomputable section
open K1_14 K1_14_3 K1_14_3R_3_2 Polynomial
open K1_14_3_2_4 (sectionEval sectionEval_ker sectionEval_surjective seedValues
  ordinateValue derivativeValue)
open K1_14_3_2_7 (four_ext scalar seedVar yVar vVar)
private abbrev Plane := MvPolynomial (Fin 2) FurtherField
private def values (jets : Bool) : Coordinates → Plane :=
  if jets then fun i => i.elim (MvPolynomial.C (furtherParameter 1)) MvPolynomial.X
  else fun i => i.elim (MvPolynomial.X 1) fun j =>
    if j = 0 then MvPolynomial.C (furtherParameter 1) -
      MvPolynomial.C (furtherParameter 0) * MvPolynomial.X 0
    else MvPolynomial.X 0
end
end K1_14_3R_3_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_4_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
theorem cancel_principal {R : Type*} [CommRing R] {M : Ideal R} {f a : R} {n : ℕ}
    (hM : M = Ideal.span {f}) (hf : Function.Injective (fun x : R => f * x))
    (h : f * a ∈ M ^ (n + 1)) : a ∈ M ^ n := by
  rw [pow_succ', show M * M ^ n = Ideal.span {f} * M ^ n from congrArg (· * M ^ n) hM] at h
  obtain ⟨b, hb, he⟩ := Ideal.mem_span_singleton_mul.mp h
  exact (hf he) ▸ hb
theorem pow_le_factor_sup {R : Type*} [CommRing R] {M F T : Ideal R}
    (hM : M = F ⊔ T) (n : ℕ) : M ^ (n + 1) ≤ F * M ^ n ⊔ T ^ (n + 1) := by
  induction n with
  | zero => simpa using hM.le
  | succ n ih =>
    have hTM : T ≤ M := hM ▸ le_sup_right
    calc
      M ^ (n + 1 + 1) = (F ⊔ T) * M ^ (n + 1) := by rw [pow_succ', ← hM]
      _ = F * M ^ (n + 1) ⊔ T * M ^ (n + 1) := Ideal.sup_mul F T _
      _ ≤ F * M ^ (n + 1) ⊔ T * (F * M ^ n ⊔ T ^ (n + 1)) :=
        sup_le_sup_left (Ideal.mul_mono_right ih) _
      _ ≤ F * M ^ (n + 1) ⊔ T ^ (n + 1 + 1) := by
        rw [Ideal.mul_sup, ← mul_assoc T F, mul_comm T F, mul_assoc, ← pow_succ' T]
        apply sup_le le_sup_left (sup_le ?_ le_sup_right)
        rw [pow_succ' M]
        exact (Ideal.mul_mono_right (Ideal.mul_mono_left hTM)).trans le_sup_left
theorem cancel_pair {R : Type*} [CommRing R] [IsDomain R] {M : Ideal R}
    {f t a : R} {n : ℕ} (hf : Prime f) (hM : M = Ideal.span {f, t})
    (h : f * a ∈ M ^ (n + 1)) : a ∈ M ^ n := by
  let F : Ideal R := Ideal.span {f}
  let T : Ideal R := Ideal.span {t}
  have hs : M = F ⊔ T := hM.trans (Ideal.span_insert _ _)
  have hinj : Function.Injective (fun x : R => f * x) := fun _ _ h => mul_left_cancel₀ hf.ne_zero h
  by_cases ht : f ∣ t
  · have hTF : T ≤ F := Ideal.span_singleton_le_span_singleton.mpr ht
    exact cancel_principal (hs.trans (sup_eq_left.mpr hTF)) hinj h
  have hparts := pow_le_factor_sup hs n h
  obtain ⟨b, hb, c, hc, he⟩ := Submodule.mem_sup.mp hparts
  obtain ⟨x, hx, rfl⟩ := Ideal.mem_span_singleton_mul.mp hb
  change c ∈ (Ideal.span ({t} : Set R)) ^ (n + 1) at hc
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc
  obtain ⟨y, rfl⟩ := hc
  have hdiv : f ∣ t ^ (n + 1) * y := ⟨a - x, by
    rw [mul_sub, ← he, add_sub_cancel_left]⟩
  obtain ⟨z, rfl⟩ := (hf.dvd_or_dvd hdiv).resolve_left (fun hd => ht (hf.dvd_of_dvd_pow hd))
  have ha : x + t ^ (n + 1) * z = a := hinj (by
    change f * (x + t ^ (n + 1) * z) = f * a
    rw [mul_add, ← mul_left_comm (t ^ (n + 1)) f]
    exact he)
  have htM : t ∈ M := hM ▸ Ideal.subset_span (by simp)
  rw [← ha]
  exact (M ^ n).add_mem hx ((M ^ n).mul_mem_right _
    (Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow htM (n + 1))))
theorem order_dual_iff (I : Ideal Ambient) [I.IsPrime] (hd : dual I) (P : Jet) (n : ℕ) :
    orderOn I P n ↔ parentLocalMap I (toJet P) ∈ (I.map (parentLocalMap I)) ^ n := by
  simp only [orderOn, ite_eq_left hd, sup_bot_eq]
  rw [← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff I.primeCompl (ParentLocal I)]
  rfl
theorem order_rankOne_iff (I : Ideal Ambient) [I.IsPrime] (hd : ¬ dual I) (P : Jet) (n : ℕ) :
    orderOn I P n ↔ jetQuotientMap I (parentLocalMap I (toJet P)) ∈
      ((I.map (parentLocalMap I)).map (jetQuotientMap I)) ^ n := by
  simp only [orderOn, ite_eq_right hd]
  rw [← Ideal.map_pow (jetQuotientMap I) (I.map (parentLocalMap I)) n,
    Ideal.mem_quotient_iff_mem_sup, ← Ideal.map_pow, ← Ideal.map_sup,
    IsLocalization.algebraMap_mem_map_algebraMap_iff I.primeCompl (ParentLocal I)]
  rfl
theorem lower_order {I : Ideal Ambient} {P : Jet} {a b : ℕ} (hab : a ≤ b)
    (h : orderOn I P b) : orderOn I P a := by
  classical
  obtain ⟨s, hs, h⟩ := h
  let J : Ideal Ambient := if dual I then ⊥ else jetImageIdeal I
  have hle : I ^ b ⊔ J ≤ I ^ a ⊔ J := sup_le_sup_right (Ideal.pow_le_pow_right hab) J
  exact ⟨s, hs, hle h⟩
theorem cancel_unit {I : Ideal Ambient} (hp : I.IsPrime) {g : Equation} {P : Jet} {m : ℕ}
    (hg : ordinaryIncl g ∉ I) (h : orderOn I (C g * P) m) : orderOn I P m := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a * ordinaryIncl g, fun hz => (hp.mem_or_mem hz).elim ha hg, ?_⟩
  simpa only [map_mul, ordinaryIncl_apply, mul_assoc] using h
theorem cancel_power {I : Ideal Ambient} {f : Equation} {P : Jet} {m r e : ℕ}
    (cancel : ∀ Q n, orderOn I (C f * Q) (n + 1) → orderOn I Q n) (he : e < r)
    (hm : r ≤ m) (h : orderOn I (C (f ^ e) * P) m) : orderOn I P (m + 1 - r) := by
  let n := m + 1 - r
  have hne : n + e ≤ m := by omega
  have h' := lower_order hne h
  clear h hne he hm
  induction e with
  | zero => simpa using h'
  | succ e ih =>
    apply ih
    apply cancel
    simpa only [pow_succ', map_mul, mul_assoc, Nat.add_assoc, Nat.succ_eq_add_one] using h'
end
end K1_14_2_2_4_3
end
section
namespace K1_13_7_2_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_7_2
def stride (linear : Bool) : ℕ := if linear then 1 else 2
def step (linear : Bool) (g : Row 4) (a : ℕ) (P : Row 4) : Row 4 :=
  if linear then flowNumerator g P - (a : Row 4) * partialFlow (separant g) * P
  else clearedStep g a P
def raw (linear : Bool) (g : Row 4) : ℕ → Row 4
  | 0 => MvPolynomial.X 0
  | n + 1 => step linear g (stride linear * n) (raw linear g n)
private theorem raw_false (g : Row 4) (n : ℕ) : raw false g n = jetNumerator g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [raw, ih, step, Bool.false_eq_true, ↓reduceIte, stride, jetNumerator]
@[simp] private theorem coeff_coefficientDerivative (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coefficientDerivative_C (p : Geom[X]) :
    coefficientDerivative (MvPolynomial.C p) = MvPolynomial.C (derivative p) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coefficientDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P + Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp
private theorem coefficientDerivative_mul_X (P : Row 4) (j : Fin 4) :
    coefficientDerivative (P * MvPolynomial.X j) = coefficientDerivative P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coefficientDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp
private theorem coefficientDerivative_mul (P Q : Row 4) :
    coefficientDerivative (P * Q) = coefficientDerivative P * Q + P * coefficientDerivative Q := by
  classical
  ext m
  simp only [coeff_coefficientDerivative, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_mul, map_sum, derivative_mul, Finset.sum_add_distrib]
private theorem partialFlow_mul (P Q : Row 4) :
    partialFlow (P * Q) = partialFlow P * Q + P * partialFlow Q := by
  simp only [partialFlow, coefficientDerivative_mul, MvPolynomial.pderiv_mul,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  have h (i : Fin 3) :
      MvPolynomial.C (C ((i.val + 1 : ℕ) : Geom)) * MvPolynomial.X i.succ *
        (P * MvPolynomial.pderiv i.castSucc Q) =
      P * (MvPolynomial.C (C ((i.val + 1 : ℕ) : Geom)) * MvPolynomial.X i.succ *
        MvPolynomial.pderiv i.castSucc Q) := by ac_rfl
  simp only [← mul_assoc, ← Finset.sum_mul] at h ⊢
  simp only [h]
  ring
private theorem flow_mul (g P Q : Row 4) :
    flowNumerator g (P * Q) = flowNumerator g P * Q + P * flowNumerator g Q := by
  simp only [flowNumerator, partialFlow_mul, separant, MvPolynomial.pderiv_mul]
  ring
theorem linear_separant {g : Row 4} (hg : (shape g).t = 1) :
    separant (separant g) = 0 := by
  let w : Fin 4 → ℕ := Pi.single 3 1
  have hb := MvPolynomial.weightedTotalDegree_pderiv_le_sub w 3 g
  rw [show w 3 = 1 by decide] at hb
  simp only [w, MvPolynomial.weightedTotalDegree_piSingle] at hb
  change g.degreeOf 3 = 1 at hg
  have hd : (separant g).degreeOf 3 ≤ 0 := by
    simpa [separant, hg] using hb
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hm
  exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hm) (Nat.eq_zero_of_le_zero hd)
private theorem raw_true_compare (g : Row 4) (h : separant (separant g) = 0) (n : ℕ) :
    jetNumerator g n = separant g ^ n * raw true g n := by
  have hD : flowNumerator g (separant g) = separant g * partialFlow (separant g) := by
    simp [flowNumerator, h]
  have hOne : flowNumerator g 1 = 0 := by
    have hm := flow_mul g 1 1
    simp only [mul_one, one_mul] at hm
    linear_combination -hm
  have hp (a : ℕ) :
      flowNumerator g (separant g ^ a) = (a : Row 4) * separant g ^ a * partialFlow (separant g) := by
    induction a with
    | zero => simp [hOne]
    | succ a ih =>
      rw [pow_succ, flow_mul, ih, hD, Nat.cast_succ]
      ring
  induction n with
  | zero => simp [jetNumerator, raw]
  | succ n ih =>
    simp only [jetNumerator, raw, step, stride, ↓reduceIte, one_mul, ih, clearedStep,
      flow_mul, hp, hD, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
abbrev trajectoryHom {L : Type} [Field L] [Algebra Geom L] (S : L[X]) : Row 4 →+* L[X] :=
  MvPolynomial.eval₂Hom (Polynomial.mapRingHom (algebraMap Geom L))
    (fun i => hasseDeriv i.val S)
private theorem eval_chain {L : Type} [Field L] [Algebra Geom L]
    (P : Row 4) (a : Fin 4 → L[X]) :
    let E := MvPolynomial.eval₂Hom (Polynomial.mapRingHom (algebraMap Geom L)) a
    derivative (E P) = E (coefficientDerivative P) +
      ∑ i, derivative (a i) * E (MvPolynomial.pderiv i P) := by
  classical
  let E := MvPolynomial.eval₂Hom (Polynomial.mapRingHom (algebraMap Geom L)) a
  change derivative (E P) = E (coefficientDerivative P) + _
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [E, coefficientDerivative_C, derivative_map]
  | add P Q hP hQ =>
    simp only [map_add, coefficientDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    have hx : E (MvPolynomial.X j) = a j := MvPolynomial.eval₂_X _ _ _
    rw [map_mul, hx, derivative_mul, ih, coefficientDerivative_mul_X, map_mul, hx]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    have hleft : (∑ i, derivative (a i) *
          (E (MvPolynomial.pderiv i P) * E (MvPolynomial.X j))) =
        (∑ i, derivative (a i) * E (MvPolynomial.pderiv i P)) * a j := by
      simp only [hx, Finset.sum_mul, mul_assoc]
    have hright : (∑ i, derivative (a i) *
          (E P * E (MvPolynomial.pderiv i (MvPolynomial.X j)))) =
        derivative (a j) * E P := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]
    rw [hleft, hright]
    ring
private theorem derivative_hasse {L : Type} [Field L] (S : L[X]) (k : ℕ) :
    derivative (hasseDeriv k S) = C ((k + 1 : ℕ) : L) * hasseDeriv (k + 1) S := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := L) 1 k) S
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul, C_eq_natCast, Nat.add_comm, add_mul] using h
private theorem eval_partialFlow {L : Type} [Field L] [Algebra Geom L]
    (S : L[X]) (P : Row 4) :
    derivative (trajectoryHom S P) = trajectoryHom S (partialFlow P) +
      derivative (hasseDeriv 3 S) * trajectoryHom S (separant P) := by
  rw [eval_chain, Fin.sum_univ_castSucc, partialFlow, map_add, map_sum, ← add_assoc]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [trajectoryHom, derivative_hasse]
private theorem eval_flow {L : Type} [Field L] [Algebra Geom L] (S : L[X])
    (g P : Row 4) (hg : trajectoryHom S g = 0) :
    trajectoryHom S (flowNumerator g P) = trajectoryHom S (separant g) *
      derivative (trajectoryHom S P) := by
  have hz := (eval_partialFlow S g).symm
  rw [hg, map_zero] at hz
  rw [eval_partialFlow, flowNumerator, map_sub, map_mul, map_mul]
  linear_combination -trajectoryHom S (separant P) * hz
private theorem cleared_product_rule {L : Type} [Field L] (a : ℕ) (U V : L[X]) :
    U * derivative (U ^ a * V) - (a : L[X]) * derivative U * (U ^ a * V) =
      U ^ (a + 1) * derivative V := by
  cases a with
  | zero => simp
  | succ a =>
    rw [derivative_mul, derivative_pow, Nat.succ_sub_one, pow_succ U (a + 1), pow_succ' U a]
    simp only [C_eq_natCast]
    ring
theorem eval_raw {L : Type} [Field L] [Algebra Geom L] (linear : Bool)
    (g : Row 4) (hl : linear = true → separant (separant g) = 0)
    (S : L[X]) (hg : trajectoryHom S g = 0) (n : ℕ) :
    trajectoryHom S (raw linear g n) =
      trajectoryHom S (separant g) ^ (stride linear * n) * ((derivative (R := L))^[n]) S := by
  induction n with
  | zero => simp [raw]
  | succ n ih =>
    rw [raw, Nat.mul_succ, Function.iterate_succ_apply']
    let a := stride linear * n
    let U := trajectoryHom S (separant g)
    let V := ((derivative (R := L))^[n]) S
    let P := raw linear g n
    change trajectoryHom S (step linear g a P) = U ^ (a + stride linear) * derivative V
    have hP : trajectoryHom S P = U ^ a * V := ih
    have hflow := eval_flow S g P hg
    have hrule := cleared_product_rule a U V
    cases linear with
    | false =>
      simp only [step, Bool.false_eq_true, ↓reduceIte, clearedStep, map_sub, map_mul, map_natCast]
      rw [hflow, eval_flow S g (separant g) hg, hP]
      change U * (U * derivative (U ^ a * V)) - (a : L[X]) * (U * derivative U) * (U ^ a * V)
        = U ^ (a + 2) * derivative V
      rw [show a + 2 = (a + 1) + 1 by omega, pow_succ]
      linear_combination U * hrule
    | true =>
      have hA : trajectoryHom S (partialFlow (separant g)) = derivative U := by
        dsimp only [U]
        rw [eval_partialFlow, hl rfl, map_zero, mul_zero, add_zero]
      simp only [step, ↓reduceIte, map_sub, map_mul, map_natCast]
      rw [hflow, hA, hP]
      exact hrule
end
end K1_13_7_2_2
end
section
namespace K1_13_7_2_2
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_1
local notation "W" => MvPolynomial.weightedTotalDegree
def topLinear (g : Row 4) : Bool := decide ((shape g).t = 1)
def denominator (g : Row 4) (n : ℕ) : Row 4 :=
  separant g ^ (stride (topLinear g) * n)
def hasseNumerator (g : Row 4) {n : ℕ} (j : Fin n) : Row 4 :=
  MvPolynomial.C (Polynomial.C (↑j.val.factorial : Geom)⁻¹) *
    (separant g ^ (stride (topLinear g) * (n - j.val)) * raw (topLinear g) g j.val)
def backwardWeight (i j : ℕ) : Geom[X] :=
  (((Polynomial.X : Geom[X][X]) - Polynomial.C (Polynomial.X : Geom[X])) ^ j).coeff i
def numerator (g : Row 4) {n : ℕ} (i : Fin n) : Row 4 :=
  ∑ j : Fin n, MvPolynomial.C (backwardWeight i.val j.val) * hasseNumerator g j
private theorem pderiv_zero_of_weight_lt (w : Fin 4 → ℕ) (i : Fin 4) (P : Row 4)
    (h : W w P < w i) : pderiv i P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : P.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]
private theorem weight_coeff_deriv (w : Fin 4 → ℕ) (P : Row 4) :
    W w (coefficientDerivative P) ≤ W w P := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj
private theorem partialFlow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (P : Row 4) {d : ℕ} (hP : W w P ≤ d) : W w (partialFlow P) ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_coeff_deriv w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    by_cases h : w i.castSucc ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he := hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
    · rw [pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)), mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem flow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) :
    W w (flowNumerator g P) ≤ d + (B - w 3) + Δ := by
  have hsep := (weightedTotalDegree_pderiv_le_sub w 3 g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (partialFlow_bound w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h : w 3 ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w 3 P).trans (Nat.sub_le_sub_right hP (w 3))
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (partialFlow_bound w Δ hshift g hg) hp).trans (by omega))
    · rw [separant, pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        mul_zero, weightedTotalDegree_zero]
      exact Nat.zero_le _
theorem weight_nat_mul_le (w : Fin 4 → ℕ) (a : ℕ) (P : Row 4) :
    W w ((a : Row 4) * P) ≤ W w P := by
  rw [← map_natCast (MvPolynomial.C : Geom[X] →+* Row 4)]
  exact weight_const_mul_le w _ _
private theorem step_bound (linear : Bool) (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) (a : ℕ) :
    W w (step linear g a P) ≤ d + (stride linear * (B - w 3) + Δ) := by
  have hsep : W w (separant g) ≤ B - w 3 :=
    (weightedTotalDegree_pderiv_le_sub w 3 g).trans (Nat.sub_le_sub_right hg (w 3))
  cases linear
  · simp only [step, Bool.false_eq_true, ↓reduceIte, stride, clearedStep]
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sub_mem <;> apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    · exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add hsep (flow_bound w Δ hshift hB hg hP)).trans (by omega))
    · exact (weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add
        ((weight_nat_mul_le _ _ _).trans (flow_bound w Δ hshift hB hg hsep)) hP |>.trans (by omega))
  · simp only [step, stride, ↓reduceIte, one_mul]
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sub_mem <;> apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    · exact (flow_bound w Δ hshift hB hg hP).trans (by omega)
    · exact (weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add
        ((weight_nat_mul_le _ _ _).trans (partialFlow_bound w Δ hshift _ hsep)) hP |>.trans (by omega))
private theorem raw_bound (linear : Bool) (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) {g : Row 4} {B : ℕ}
    (hB : w 3 ≤ B) (hg : W w g ≤ B) (n : ℕ) :
    W w (raw linear g n) ≤ w 0 + n * (stride linear * (B - w 3) + Δ) := by
  induction n with
  | zero => simpa only [raw, zero_mul, add_zero] using weight_X_le (R := Geom[X]) w 0
  | succ n ih =>
    simpa only [raw, Nat.add_mul, one_mul, Nat.add_assoc] using
      step_bound linear w Δ hshift hB hg ih (stride linear * n)
private theorem sep_pow_bound (g : Row 4) (w : Fin 4 → ℕ) (a : ℕ) {B : ℕ} (hg : W w g ≤ B) :
    W w (separant g ^ a) ≤ a * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _
    ((weightedTotalDegree_pderiv_le_sub w 3 g).trans (Nat.sub_le_sub_right hg _)))
end
end K1_13_7_2_2
end
section
namespace K1_13_7_2_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_7_1 K1_13_7_2
private theorem topLinear_regular (g : Row 4) :
    topLinear g = true → separant (separant g) = 0 :=
  fun h => linear_separant (of_decide_eq_true h)
private theorem ordinary_eq_hasse {L : Type} [Field L] (S : L[X]) (n : ℕ) :
    derivative^[n] S = C (n.factorial : L) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, coeff_C_mul, hasseDeriv_coeff, Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
theorem eval_hasseNumerator {L : Type} [Field L] [Algebra Geom L]
    (g : Row 4) (S : L[X]) (hg : trajectoryHom S g = 0)
    {n : ℕ} (hn : n ≤ K1.p) (j : Fin n) :
    trajectoryHom S (hasseNumerator g j) =
      trajectoryHom S (denominator g n) * hasseDeriv j.val S := by
  let k := stride (topLinear g)
  let U := trajectoryHom S (separant g)
  let m := Polynomial.mapRingHom (algebraMap Geom L)
  let u : Geom := (j.val.factorial : Geom)
  have hu : u ≠ 0 := factorial_cast_ne_zero (j.isLt.trans_le hn)
  have hinv : m (C u⁻¹) * C (↑j.val.factorial : L) = 1 := by
    have h : C u⁻¹ * C u = (1 : Geom[X]) := by
      rw [← map_mul, inv_mul_cancel₀ hu, map_one]
    simpa only [m, u, map_mul, map_one, Polynomial.coe_mapRingHom, Polynomial.map_C, map_natCast]
      using congrArg m h
  simp only [hasseNumerator, denominator, map_mul, map_pow, MvPolynomial.eval₂Hom_C]
  rw [eval_raw _ _ (topLinear_regular g) S hg, ordinary_eq_hasse]
  change m (C u⁻¹) * (U ^ (k * (n - j.val)) *
    (U ^ (k * j.val) * (C (↑j.val.factorial : L) * hasseDeriv j.val S))) =
      U ^ (k * n) * hasseDeriv j.val S
  calc
    _ = (m (C u⁻¹) * C (↑j.val.factorial : L)) *
          ((U ^ (k * (n - j.val)) * U ^ (k * j.val)) * hasseDeriv j.val S) := by ring
    _ = _ := by
      rw [hinv, one_mul, ← pow_add, ← Nat.mul_add, Nat.sub_add_cancel j.isLt.le]
theorem map_backwardWeight {L : Type} [Field L] [Algebra Geom L] (i j : ℕ) :
    (backwardWeight i j).map (algebraMap Geom L) =
      (((Polynomial.X : L[X][X]) - C (Polynomial.X : L[X])) ^ j).coeff i := by
  let m := Polynomial.mapRingHom (algebraMap Geom L)
  change m ((((Polynomial.X : Geom[X][X]) - C (Polynomial.X : Geom[X])) ^ j).coeff i) = _
  rw [← Polynomial.coeff_map (f := m)]
  simp [m]
theorem eval_at_X {L : Type} [Field L] (P : L[X]) :
    (P.map (C : L →+* L[X])).eval (Polynomial.X : L[X]) = P := by rw [eval_map, eval₂_C_X]
private theorem inverse_taylor {L : Type} [Field L] (S : L[X])
    {n : ℕ} (hS : S.natDegree < n) (i : ℕ) :
    (∑ j : Fin n, (((Polynomial.X : L[X][X]) - C (Polynomial.X : L[X])) ^ j.val).coeff i *
      hasseDeriv j.val S) = C (S.coeff i) := by
  let Sh := S.map (C : L →+* L[X])
  have hd : (taylor (Polynomial.X : L[X]) Sh).natDegree < n := by
    rw [natDegree_taylor]
    exact natDegree_map_le.trans_lt hS
  have h := sum_taylor_eq Sh (Polynomial.X : L[X])
  rw [sum_over_range' _ (fun n => by simp) _ hd, ← Fin.sum_univ_eq_sum_range] at h
  have hc := congrArg (fun P : L[X][X] => P.coeff i) h
  simpa only [finsetSum_coeff, coeff_C_mul, taylor_coeff, hasseDeriv_map, eval_at_X, Sh,
    Polynomial.coeff_map, mul_comm] using hc
private theorem eval_numerator {L : Type} [Field L] [Algebra Geom L]
    (g : Row 4) (S : L[X]) (hg : trajectoryHom S g = 0)
    {n : ℕ} (hd : S.natDegree < n) (hn : n ≤ K1.p) (i : Fin n) :
    trajectoryHom S (numerator g i) = trajectoryHom S (denominator g n) * C (S.coeff i.val) := by
  simp only [numerator, map_sum, map_mul, MvPolynomial.eval₂Hom_C, eval_hasseNumerator _ _ hg hn,
    Polynomial.coe_mapRingHom, map_backwardWeight, Finset.mul_sum, ← inverse_taylor S hd]
  exact Finset.sum_congr rfl (fun j _ => by ring)
theorem eval_test_zero {L : Type} [Field L] [Algebra Geom L]
    (g : Row 4) (S : L[X]) (hg : trajectoryHom S g = 0) {n : ℕ} (hd : S.natDegree < n) :
    trajectoryHom S (raw (topLinear g) g n) = 0 := by
  rw [eval_raw _ _ (topLinear_regular g) S hg, iterate_derivative_eq_zero hd, mul_zero]
private theorem specializes {L : Type} [Field L] [Algebra Geom L]
    (g : Row 4) (S : L[X]) {n : ℕ} (hd : S.natDegree < n) (hn : n ≤ K1.p)
    (hs : evalTrajectory g S = 0) (hr : evalTrajectory (separant g) S ≠ 0) :
    evalTrajectory (denominator g n) S ≠ 0 ∧ evalTrajectory (raw (topLinear g) g n) S = 0 ∧
      ∀ i : Fin n, evalTrajectory (numerator g i) S =
        evalTrajectory (denominator g n) S * C (S.coeff i.val) := by
  have hD : trajectoryHom S (denominator g n) ≠ 0 := by
    rw [denominator, map_pow]
    exact pow_ne_zero _ hr
  exact ⟨hD, eval_test_zero g S hs hd, fun i => eval_numerator g S hs hd hn i⟩
end
end K1_13_7_2_2
end
section
namespace K1_14_2_5
noncomputable section
open K1 K1_13 K1_13_5
open K1_13_5_3 hiding exponent exponent_sufficient
open Polynomial PolynomialDifferential
open scoped BigOperators
abbrev length : ℕ := K1_14_2.endpointDegree + 1
abbrev power : ℕ := 2 * length - 5
def chartTotal (B : ℕ) : ℕ := 1 + power * (B - 1)
def chartTop (B J : ℕ) : ℕ := min (chartTotal B) (power * (J - 1) + (length - 1))
private theorem exponent_sufficient : TaylorExponentSufficient 1 length power :=
  taylorExponentSufficient_firstOrder_tight 134625
private theorem specialization_flatten (f : Row 2) (S : Geom[X]) :
    differentialSpecialization (flatten f) S = atJet f S := by
  let x : Option (Fin 2) → Geom[X] := fun
    | none => Polynomial.X
    | some i => jet S i
  have h := MvPolynomial.aeval_optionEquivRight_symm (R := Geom) x f
  have hx : x none = Polynomial.X := rfl
  have hj : (fun j => x (some j)) = jet S := rfl
  rw [hx, hj, Polynomial.aeval_X_left] at h
  rw [show (AlgHom.id Geom Geom[X]).toRingHom = RingHom.id (Geom[X]) from rfl,
    MvPolynomial.map_id, MvPolynomial.aeval_eq_eval] at h
  unfold flatten at *
  unfold atJet differentialSpecialization
  refine (AlgHom.congr_fun ?_ _).trans h
  apply MvPolynomial.algHom_ext
  intro v
  rw [differentialSpecializationHom, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  cases v <;> rfl
private theorem chart_cut_agreement {f : Row 2} {S : Geom[X]} (hS : RegularAt 1 f S)
    (hD : S.natDegree ≤ 134625) (x y : Geom) :
    MvPolynomial.aeval (marked S)
      (taylorAgreementEquation center (K1_13_5_3.chart f) length power (constants x) (constants y))
      = 0 ↔ S.eval x = y := by
  have hsol : differentialSpecialization (K1_13_5_3.chart f) (S.map constants) = 0 := by
    rw [K1_13_5_3.chart, ← map_differentialSpecialization, specialization_flatten, hS.1, Polynomial.map_zero]
  have hsf : differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) S ≠ 0 := by
    change differentialSpecialization
      (MvPolynomial.pderiv (some 1) ((MvPolynomial.optionEquivRight Geom (Fin 2)).symm f)) S ≠ 0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]
    exact (specialization_flatten (MvPolynomial.pderiv 1 f) S).substr hS.2
  have eval_at_center (P : Geom[X]) : (P.map constants).eval center = toCenter P := by
    have h := marked_apply P 0
    change (hasseDeriv 0 (P.map constants)).eval center = toCenter (hasseDeriv 0 P) at h
    simpa only [Polynomial.hasseDeriv_zero'] using h
  have hsep : jetEvaluation (PolynomialDifferential.separant (K1_13_5_3.chart f) (Fin.last 1))
      center (marked S) ≠ 0 := by
    change jetEvaluation (PolynomialDifferential.separant (K1_13_5_3.chart f) 1) center (marked S) ≠ 0
    rw [marked, ← eval_differentialSpecialization, K1_13_5_3.chart, ← map_separant,
      ← map_differentialSpecialization, eval_at_center]
    exact fun he => hsf (toCenter_inj (he.trans (map_zero _).symm))
  have hdeg : (S.map constants).degree < (length : WithBot ℕ) := by
    have hb : (S.map constants).natDegree ≤ 134625 := Polynomial.natDegree_map_le.trans hD
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hb)
  have hcharG : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have : CharP CenterField K1.p := charP_of_injective_ringHom constants.injective K1.p
  have hpiv : ∀ i : ℕ, 1 < i → i < length → (i.choose 1 : CenterField) ≠ 0 := by
    intro i hi ht
    rw [Nat.choose_one_right]
    intro hz
    have hp := Nat.le_of_dvd (by omega : 0 < i)
      ((CharP.cast_eq_zero_iff CenterField K1.p i).mp hz)
    change 2130706433 ≤ i at hp
    change i < 134626 at ht
    omega
  rw [taylorAgreementEquation_eq_zero_iff center (K1_13_5_3.chart f) exponent_sufficient (marked S)
      (by rwa [aeval_initialJetSeparant]) (constants x) (constants y)]
  rw [marked, rationalTaylorPolynomial_polynomialJet center (K1_13_5_3.chart f) (S.map constants)
    hsol hsep hdeg hpiv, Polynomial.eval_map_apply, constants.injective.eq_iff]
private def nodeCut (w : I → K) (f : Row 2) (i : I) : MvPolynomial (Fin 2) CenterField :=
  taylorAgreementEquation center (K1_13_5_3.chart f) length power
    (constants (embed (node i))) (constants (embed (w i)))
private theorem nodeCut_capped (w : I → K) (f : Row 2) {B J : ℕ}
    (hB : f.totalDegree ≤ B) (hJ : f.degreeOf 1 ≤ J) (hJpos : 0 < J) (i : I) :
    nodeCut w f i ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      (chartTotal B) (chartTop B J) := by
  have ht : (nodeCut w f i).totalDegree ≤ chartTotal B := by
    refine (totalDegree_taylorAgreementEquation_le center (K1_13_5_3.chart f)
      exponent_sufficient _ _).trans ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_left power
      (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1)) 1
  refine mem_capped _ ht (le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans ht) ?_)
  exact degreeOf_taylorAgreementEquation_firstOrder_le center (K1_13_5_3.chart f) J
    length power exponent_sufficient hJpos ((chart_top f).trans hJ) _ _
private theorem nodeCut_vanishes {w : I → K} {f : Row 2} {S : K[X]}
    (hreg : RegularAt 1 f (extend S)) (hD : S.natDegree ≤ 134625) (i : I) :
    MvPolynomial.aeval (marked (extend S)) (nodeCut w f i) = 0 ↔
      S.eval (node i) = w i := by
  rw [nodeCut, chart_cut_agreement hreg (Polynomial.natDegree_map_le.trans hD),
    Polynomial.eval_map_apply, embed.injective.eq_iff]
end
end K1_14_2_5
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1500000
namespace K1_14_3R_2_3
noncomputable section
open K1_14 K1_14_3 K1_14_3_2_3 K1_14_3_2_7
open MvPolynomial
open scoped nonZeroDivisors
private abbrev Parameters := MvPolynomial (Fin 4) FX
abbrev SlopedJet := MvPolynomial (Fin 2) Jet
private abbrev RawPlane := MvPolynomial (Fin 2) Parameters
private abbrev par (i : Fin 4) : RawPlane := C (MvPolynomial.X i)
private abbrev t (i : Fin 2) : SlopedJet := C (seedVar i)
private abbrev y : SlopedJet := C yVar
private abbrev v : SlopedJet := C vVar
private def rawSeeds : Slice → Fin 2 → RawPlane
  | .seed => ![par 2, par 3]
  | .ordinate | .mixed => ![par 2 - par 0 * MvPolynomial.X 0, MvPolynomial.X 0]
  | .jets => MvPolynomial.X
private def rawY : Slice → RawPlane
  | .seed => MvPolynomial.X 0
  | .ordinate => par 3
  | .mixed => par 3 - par 1 * MvPolynomial.X 1
  | .jets => par 2
private def rawV : Slice → RawPlane
  | .jets => par 3
  | _ => MvPolynomial.X 1
private def rawJet (s : Slice) : Jet →+* RawPlane :=
  evaluate (C.comp C) (rawSeeds s) (rawY s) (rawV s)
private def forward (s : Slice) : SlopedJet →+* RawPlane :=
  eval₂Hom (rawJet s) ![par 0, par 1]
def originalParameters : Slice → Fin 4 → SlopedJet
  | .seed => ![MvPolynomial.X 0, MvPolynomial.X 1, t 0, t 1]
  | .ordinate => ![MvPolynomial.X 0, MvPolynomial.X 1, t 0 + MvPolynomial.X 0 * t 1, y]
  | .mixed => ![MvPolynomial.X 0, MvPolynomial.X 1, t 0 + MvPolynomial.X 0 * t 1, y + MvPolynomial.X 1 * v]
  | .jets => ![MvPolynomial.X 0, MvPolynomial.X 1, y, v]
private def free : Slice → Fin 2 → SlopedJet
  | .seed => ![y, v]
  | .ordinate | .mixed => ![t 1, v]
  | .jets => ![t 0, t 1]
private def backward (s : Slice) : RawPlane →+* SlopedJet :=
  eval₂Hom (eval₂Hom (C.comp scalar) (originalParameters s)) (free s)
@[simp] private theorem forward_C (s : Slice) (a : Jet) :
    forward s (C a) = rawJet s a := by simp [forward]
@[simp] private theorem forward_X (s : Slice) (i : Fin 2) :
    forward s (MvPolynomial.X i) = (![par 0, par 1] : Fin 2 → RawPlane) i := by simp [forward]
@[simp] private theorem backward_scalar (s : Slice) (a : FX) :
    backward s (C (C a)) = C (scalar a) := by simp [backward]
@[simp] private theorem backward_par (s : Slice) (i : Fin 4) :
    backward s (par i) = originalParameters s i := by simp [backward]
@[simp] private theorem backward_X (s : Slice) (i : Fin 2) :
    backward s (MvPolynomial.X i) = free s i := by simp [backward]
abbrev rawAlgebra : Algebra RawPlane Plane := MvPolynomial.algebraMvPolynomial
local instance : Algebra RawPlane Plane := rawAlgebra
end
end K1_14_3R_2_3
end
section
namespace K1_13_5_4_1_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_1 MvPolynomial
open K1_13_6 (coefficientDerivative partialFlow)
open K1_13_7_1 (weight_le_of_support_subset weight_const_mul_le weight_X_le)
open scoped Polynomial
local notation "W" => weightedTotalDegree
private theorem mul_bound {R : Type*} [CommSemiring R] {w : Fin 4 → ℕ}
    {p q : MvPolynomial (Fin 4) R} {a b : ℕ} (hp : W w p ≤ a) (hq : W w q ≤ b) :
    W w (p * q) ≤ a + b :=
  (weightedTotalDegree_mul_le w p q).trans (Nat.add_le_add hp hq)
theorem derivative_zero_of_lt (w : Fin 4 → ℕ) (i : Fin 4) (p : Row 4)
    (h : W w p < w i) : pderiv i p = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : p.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]
theorem mul_pderiv_bound (w : Fin 4 → ℕ) (i : Fin 4) {p q : Row 4} {d delta : ℕ}
    (hp : W w p ≤ d) (hq : W w q ≤ w i + delta) :
    W w (q * pderiv i p) ≤ d + delta := by
  by_cases hi : w i ≤ d
  · have hd := (weightedTotalDegree_pderiv_le_sub w i p).trans
      (Nat.sub_le_sub_right hp (w i))
    exact (mul_bound hq hd).trans (by omega)
  · rw [derivative_zero_of_lt w i p (hp.trans_lt (Nat.lt_of_not_ge hi)), mul_zero,
      weightedTotalDegree_zero]
    exact Nat.zero_le _
theorem coefficientDerivative_bound (w : Fin 4 → ℕ) (p : Row 4) :
    W w (coefficientDerivative p) ≤ W w p := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj
private theorem partialFlow_bound (w : Fin 4 → ℕ) {delta d : ℕ}
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + delta)
    {p : Row 4} (hp : W w p ≤ d) :
    W w (partialFlow p) ≤ d + delta := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((coefficientDerivative_bound w p).trans (hp.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    exact (weight_const_mul_le w _ _).trans
      (mul_pderiv_bound w i.castSucc hp ((weight_X_le w i.succ).trans (hshift i)))
private theorem liftSep_eq (f : Row 3) : liftSep f = pderiv 2 (liftRaw f) :=
  (pderiv_rename (Fin.castSucc_injective 3) (2 : Fin 3) f).symm
private theorem liftedStep_bound (w : Fin 4 → ℕ) {delta step sep d : ℕ}
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + delta)
    {f : Row 3} {p : Row 4} (hp : W w p ≤ d) (hs : W w (liftSep f) ≤ sep)
    (hsep : sep + delta ≤ step) (hu : W w (thirdVelocityNumerator f) ≤ w 3 + step) (k : ℕ) :
    W w (liftedStep f k p) ≤ d + step := by
  unfold liftedStep
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((mul_bound hs (partialFlow_bound w hshift hp)).trans (by omega))
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        (mul_pderiv_bound w 3 hp hu)
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [← map_natCast (MvPolynomial.C : Geom[X] →+* Row 4), mul_assoc]
    exact ((weight_const_mul_le w _ _).trans
      (mul_bound (partialFlow_bound w hshift hs) hp)).trans (by omega)
private theorem generic_bound (w : Fin 4 → ℕ) (p : Row 4) :
    W w (genericRow p) ≤ W w p :=
  weight_le_of_support_subset w (support_map_subset genericCoeff p)
private abbrev totalWeight : Fin 4 → ℕ := ![1, 1, 1, 0]
private abbrev indexWeight : Fin 4 → ℕ := ![0, 1, 2, 0]
private abbrev topWeight : Fin 4 → ℕ := Pi.single 2 1
private abbrev heightWeight : Fin 4 → ℕ := Pi.single 3 1
private theorem lift_weight (w : Fin 4 → ℕ) (f : Row 3) :
    W w (liftRaw f) = W (w ∘ Fin.castSucc) f :=
  weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 3)
private theorem fits {p : GeoRow 4} {b j t h : ℕ}
    (hb : W totalWeight p ≤ b) (hj : W indexWeight p ≤ j)
    (ht : W topWeight p ≤ t) (hh : W heightWeight p ≤ h) :
    InLiftedBox p ⟨b, j, min t (j / 2)⟩ h := by
  intro a ha
  have hb' := (le_weightedTotalDegree totalWeight ha).trans hb
  have hj' := (le_weightedTotalDegree indexWeight ha).trans hj
  have ht' := (le_weightedTotalDegree topWeight ha).trans ht
  have hh' := (le_weightedTotalDegree heightWeight ha).trans hh
  rw [Finsupp.weight_single_one_apply] at ht' hh'
  simp [Finsupp.weight_eq_sum, smul_eq_mul, Fin.sum_univ_four] at hb' hj'
  have hj'' : a 1 + 2 * a 2 ≤ j := by omega
  exact ⟨hb', hj'', le_min ht' (by omega), hh'⟩
private theorem fits_lifted {p : GeoRow 4} (L : ℕ)
    (hb : W totalWeight p ≤ 1 + (L - 4) * 120)
    (hj : W indexWeight p ≤ 2 + (L - 4) * 50)
    (ht : W topWeight p ≤ 1 + (L - 4) * 26)
    (hh : W heightWeight p ≤ L - 2) :
    InLiftedBox p (liftedBox L) (L - 2) :=
  fits hb hj ht hh
end
end K1_13_5_4_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_11_2
noncomputable section
open K1_11 MvPolynomial Finset
variable {F : Type*} [Field F]
theorem multiply_message_tag (P : MvPolynomial (Fin 5) F) (hP : OmitsMessages P) :
    messageTag (P*MvPolynomial.X 1) 1 0 ∧ messageTag (P*MvPolynomial.X 2) 0 1 := by
  constructor
  all_goals
    intro e he
    rw [support_mul_X] at he
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    have hh := omitted_message_tag P hP f hf
    simpa [Finsupp.add_apply,Finsupp.single_apply] using hh
theorem supports_disjoint_of_tags (P Q : MvPolynomial (Fin 5) F) (a b c d : ℕ)
    (hP : messageTag P a b) (hQ : messageTag Q c d) (hne : (a,b)≠(c,d)) :
    Disjoint P.support Q.support := by
  apply disjoint_left.mpr
  intro e heP heQ
  have h1 := hP e heP
  have h2 := hQ e heQ
  exact hne (Prod.ext (by omega) (by omega))
theorem weighted_add_of_disjoint (v : Fin 5 → ℕ) (P Q : MvPolynomial (Fin 5) F)
    (h : Disjoint P.support Q.support) :
    (P+Q).weightedTotalDegree v=max (P.weightedTotalDegree v) (Q.weightedTotalDegree v) := by
  have hs : (P+Q).support=P.support∪Q.support := Finsupp.support_add_eq h
  simp only [weightedTotalDegree,hs,Finset.sup_union]
theorem linear_form_weight (v : Fin 5 → ℕ) (U V R : MvPolynomial (Fin 5) F)
    (hU : U≠0) (hV : V≠0) (hUm : OmitsMessages U) (hVm : OmitsMessages V)
    (hRm : OmitsMessages R) :
    (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R).weightedTotalDegree v=
      max (max (U.weightedTotalDegree v+v 1) (V.weightedTotalDegree v+v 2))
        (R.weightedTotalDegree v) := by
  have htU := (multiply_message_tag U hUm).1
  have htV := (multiply_message_tag V hVm).2
  have hd := supports_disjoint_of_tags _ _ 1 0 0 1 htU htV (by decide)
  have hsum : (U*MvPolynomial.X 1+V*MvPolynomial.X 2).support=(U*MvPolynomial.X 1).support∪(V*MvPolynomial.X 2).support :=
    Finsupp.support_add_eq hd
  have hdR : Disjoint (U*MvPolynomial.X 1+V*MvPolynomial.X 2).support (-R).support := by
    apply disjoint_left.mpr
    intro e he heR
    have hR : e∈R.support := by simpa using heR
    have hRtag := omitted_message_tag R hRm e hR
    rw [hsum] at he
    rcases mem_union.mp he with hu | hv
    · have hh := htU e hu
      omega
    · have hh := htV e hv
      omega
  rw [sub_eq_add_neg,weighted_add_of_disjoint _ _ _ hdR,
    weighted_add_of_disjoint _ _ _ hd,
    weightedTotalDegree_mul _ _ _ hU (X_ne_zero 1),
    weightedTotalDegree_mul _ _ _ hV (X_ne_zero 2)]
  have hx (i : Fin 5) : (MvPolynomial.X i : MvPolynomial (Fin 5) F).weightedTotalDegree v=v i := by
    rw [MvPolynomial.X, weightedTotalDegree_monomial _ _ _ one_ne_zero]
    simp [Finsupp.weight_single]
  rw [hx 1,hx 2]
  have hn : (-R).weightedTotalDegree v=R.weightedTotalDegree v := by simp [weightedTotalDegree]
  rw [hn]
theorem omitted_source_weights (w : ℕ) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) (q : Fin 4) :
    P.weightedTotalDegree (sourceWeights w q)=![P.degreeOf 0,0,P.degreeOf 3,P.degreeOf 4] q := by
  have ht := omitted_message_tag P hP
  fin_cases q
  · change P.weightedTotalDegree (sourceWeights w 0)=P.degreeOf 0
    rw [weightedTotalDegree,degreeOf_eq_sup]
    apply Finset.sup_congr rfl
    intro e he
    have hh := ht e he
    simp [sourceWeights,weight5,hh.1,hh.2]
  · change P.weightedTotalDegree (sourceWeights w 1)=0
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro e he
    have hh := ht e he
    simp [sourceWeights,weight5,hh.1,hh.2]
  · change P.weightedTotalDegree (sourceWeights w 2)=P.degreeOf 3
    rw [weightedTotalDegree,degreeOf_eq_sup]
    apply Finset.sup_congr rfl
    intro e he
    have hh := ht e he
    simp [sourceWeights,weight5,hh.1,hh.2]
  · change P.weightedTotalDegree (sourceWeights w 3)=P.degreeOf 4
    rw [weightedTotalDegree,degreeOf_eq_sup]
    apply Finset.sup_congr rfl
    intro e he
    have hh := ht e he
    simp [sourceWeights,weight5,hh.1,hh.2]
theorem equation_degrees (w H : ℕ) (U V W : MvPolynomial (Fin 5) F)
    (hU : U ≠ 0) (hV : V ≠ 0)
    (hUm : OmitsMessages U) (hVm : OmitsMessages V) (hWm : OmitsMessages W)
    (hH : max (U.degreeOf 0) (V.degreeOf 0) = H) (hWX : W.degreeOf 0 ≤ w + H)
    (hWS : W.degreeOf 3 ≤ sWeight U V) (hWT : W.degreeOf 4 ≤ tWeight U V) :
    ∀ j, (U * MvPolynomial.X 1 + V * MvPolynomial.X 2 - W).weightedTotalDegree
      (sourceWeights w j) = sourceBounds (w + H) 1 (sWeight U V) (tWeight U V) j := by
  intro j
  rw [linear_form_weight _ U V W hU hV hUm hVm hWm, omitted_source_weights w U hUm,
    omitted_source_weights w V hVm, omitted_source_weights w W hWm]
  fin_cases j
  · simp [sourceWeights, sourceBounds]
    omega
  · simp [sourceWeights, sourceBounds]
  · simp [sourceWeights, sourceBounds, sWeight] at hWS ⊢
    omega
  · simp [sourceWeights, sourceBounds, tWeight] at hWT ⊢
    omega
theorem polynomialView_constant (Q : MvPolynomial (Fin 5) F)
    (hQ : OmitsMessages Q) : polynomialView Q = Polynomial.C ((polynomialView Q).coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_le_zero
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hn
  obtain ⟨f, hf⟩ := support_nonempty.mpr hn
  obtain ⟨e, he, _, _, he2, _, _⟩ := polynomialView_coeff_support Q j f hf
  have he0 := (omitted_message_tag Q hQ e he).2
  omega
def equation (U V W : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 5) F :=
  U * MvPolynomial.X 1 + V * MvPolynomial.X 2 - W
def decoderNumerator (U W : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 4) F :=
  (polynomialView W).coeff 0 - (polynomialView U).coeff 0 * MvPolynomial.X 1
def decoderDenominator (V : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 4) F :=
  (polynomialView V).coeff 0
theorem equation_linear (U V W : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hW : OmitsMessages W) :
    polynomialView (equation U V W) =
      Polynomial.C (decoderDenominator V) * Polynomial.X -
        Polynomial.C (decoderNumerator U W) := by
  simp only [equation, map_sub, map_add, map_mul, polynomialView_X]
  rw [polynomialView_constant U hU, polynomialView_constant V hV, polynomialView_constant W hW]
  simp [decoderDenominator, decoderNumerator, map_sub, map_mul]
  ring
theorem decoderDenominator_ne (V : MvPolynomial (Fin 5) F)
    (hV : OmitsMessages V) (hn : V ≠ 0) : decoderDenominator V ≠ 0 := by
  intro h
  apply hn
  apply (polynomialView (F:=F)).injective
  have he : polynomialView V = Polynomial.C (decoderDenominator V) :=
    polynomialView_constant V hV
  rw [he, h, Polynomial.C_0]
  exact (map_zero (polynomialView (F:=F))).symm
theorem equation_primitive (U V W : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hW : OmitsMessages W)
    (hn : V ≠ 0) (hUV : IsRelPrime U V) :
    (Polynomial.C (decoderDenominator V) * Polynomial.X -
        Polynomial.C (decoderNumerator U W)).IsPrimitive := by
  apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro d hd
  have hc := (Polynomial.C_dvd_iff_dvd_coeff d _).mp hd
  have hdV : d ∣ decoderDenominator V := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] using hc 1
  have hdN : d ∣ decoderNumerator U W := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] using hc 0
  let e := (polynomialView (F:=F)).symm (Polynomial.C d)
  have heV : e ∣ V := by
    apply (map_dvd_iff (polynomialView (F:=F))).mp
    change polynomialView ((polynomialView (F:=F)).symm (Polynomial.C d)) ∣ polynomialView V
    rw [AlgEquiv.apply_symm_apply, polynomialView_constant V hV]
    exact map_dvd Polynomial.C hdV
  have heN : e ∣ W - U * MvPolynomial.X 1 := by
    apply (map_dvd_iff (polynomialView (F:=F))).mp
    change polynomialView ((polynomialView (F:=F)).symm (Polynomial.C d)) ∣
      polynomialView (W - U * MvPolynomial.X 1)
    rw [AlgEquiv.apply_symm_apply, map_sub, map_mul, polynomialView_X,
      polynomialView_constant W hW, polynomialView_constant U hU]
    change Polynomial.C d ∣ Polynomial.C ((polynomialView W).coeff 0) -
      Polynomial.C ((polynomialView U).coeff 0) * Polynomial.C (MvPolynomial.X 1)
    rw [← map_mul, ← map_sub]
    exact map_dvd Polynomial.C hdN
  obtain ⟨v, hv⟩ := heV
  have he : e ≠ 0 := by intro hz; apply hn; rw [hv, hz, zero_mul]
  have hv_ne : v ≠ 0 := by intro hz; apply hn; rw [hv, hz, mul_zero]
  have heomits : e.degreeOf 1 = 0 := by
    have hdeg := congrArg (degreeOf (1 : Fin 5)) hv
    rw [hV.1, degreeOf_mul_eq he hv_ne] at hdeg
    omega
  obtain ⟨q, hq⟩ := heN
  have hh : -U = e * pderiv 1 q := by
    simpa [map_sub, pderiv_mul, pderiv_zero_of_degree_zero _ _ hW.1,
      pderiv_zero_of_degree_zero _ _ hU.1,
      pderiv_zero_of_degree_zero _ _ heomits] using congrArg (pderiv (R:=F) (1 : Fin 5)) hq
  have heU : e ∣ U := by
    refine ⟨-pderiv 1 q, ?_⟩
    rw [mul_neg, ← hh, neg_neg]
  have hu := (hUV heU ⟨v, hv⟩).map (polynomialView (F:=F)).toRingHom
  change IsUnit (polynomialView e) at hu
  exact Polynomial.isUnit_C.mp (by simpa only [e, AlgEquiv.apply_symm_apply] using hu)
theorem decoder_bounds (w H s t : ℕ) (U V W : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hW : OmitsMessages W) (hVn : V ≠ 0)
    (hQ : equation U V W ∈ filtered (sourceWeights w) (sourceBounds (w + H) 1 s t)) :
    (decoderNumerator U W).weightedTotalDegree scalarWeightY ≤ 1 ∧
    (decoderDenominator V).weightedTotalDegree scalarWeightY ≤ 0 ∧
    (decoderNumerator U W).weightedTotalDegree scalarWeightYS ≤ s ∧
    (decoderDenominator V).weightedTotalDegree scalarWeightYS ≤ s ∧
    (decoderNumerator U W).weightedTotalDegree scalarWeightT ≤ t ∧
    (decoderDenominator V).weightedTotalDegree scalarWeightT ≤ t - 1 := by
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients (w + H) w 1 s t _ hQ
  have h0 : (polynomialView (equation U V W)).coeff 0 = -decoderNumerator U W := by
    rw [equation_linear U V W hU hV hW]
    simp [Polynomial.coeff_sub]
  have h1 : (polynomialView (equation U V W)).coeff 1 = decoderDenominator V := by
    rw [equation_linear U V W hU hV hW]
    simp [Polynomial.coeff_sub]
  have hV' : (polynomialView (equation U V W)).coeff 1 ≠ 0 := by
    rw [h1]
    exact decoderDenominator_ne V hV hVn
  have hy1 := hY 1 le_rfl hV'
  have hs1 := hS 1 le_rfl hV'
  have ht1 := hT 1 le_rfl hV'
  rw [h1] at hy1 hs1 ht1
  refine ⟨?_, by omega, ?_, hs1, ?_, by omega⟩
  all_goals
    by_cases hn : decoderNumerator U W = 0
    · simp [hn, weightedTotalDegree]
    · have hn' : (polynomialView (equation U V W)).coeff 0 ≠ 0 := by simpa [h0] using hn
      first
      | simpa [h0, weightedTotalDegree] using hY 0 (by decide) hn'
      | simpa [h0, weightedTotalDegree] using hS 0 (by decide) hn'
      | simpa [h0, weightedTotalDegree] using hT 0 (by decide) hn'
end
end K1_11_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_3_6 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem degree_slotWeight {σ : Type} (s : σ → Fin 5) (a : σ →₀ ℕ) :
    (Finsupp.weight (slotWeight s) a).degree = a.degree := by
  have h : Finsupp.degree.comp (Finsupp.weight (slotWeight s)) = Finsupp.degree := by
    ext j
    simp [Finsupp.weight_single, slotWeight, unitGrade]
  exact DFunLike.congr_fun h a
theorem piece_fg {σ : Type} [Finite σ] (s : σ → Fin 5) (t : Grade) :
    (piece s t).FG := by
  change (weightedHomogeneousSubmodule GeoField (slotWeight s) t).FG
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, ← Module.Finite.iff_fg]
  have hs : {a : σ →₀ ℕ | Finsupp.weight (slotWeight s) a = t}.Finite := by
    refine (Finsupp.finite_of_degree_eq t.degree).subset ?_
    intro a ha
    change Finsupp.weight (slotWeight s) a = t at ha
    change a.degree = t.degree
    exact (degree_slotWeight s a).symm.trans (congrArg Finsupp.degree ha)
  have := hs.to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport GeoField {a : σ →₀ ℕ | Finsupp.weight (slotWeight s) a = t})
abbrev quotientPiece {σ : Type} (s : σ → Fin 5) (J : Ideal (MvPolynomial σ GeoField))
    (t : Grade) :=
  (piece s t).map (Ideal.Quotient.mkₐ GeoField J).toLinearMap
instance {σ : Type} [Finite σ] (s : σ → Fin 5) (J : Ideal (MvPolynomial σ GeoField))
    (t : Grade) : Module.Finite GeoField (quotientPiece s J t) :=
  Module.Finite.iff_fg.mpr ((piece_fg s t).map _)
theorem homogeneous_cut_exact {σ : Type} [Finite σ] (s : σ → Fin 5)
    (J : Ideal (MvPolynomial σ GeoField)) (hJ : J.IsHomogeneous (piece s))
    (i : Fin 5) (g : MvPolynomial σ GeoField) (hg : g ∈ piece s (unitGrade i)) :
    (J ⊔ Ideal.span {g}).IsHomogeneous (piece s) ∧
      ∀ t : Grade, gradedHilbert s (J ⊔ Ideal.span {g}) (t + unitGrade i) +
        gradedHilbert s (J.colon {g}) t = gradedHilbert s J (t + unitGrade i) := by
  have hspan : (Ideal.span {g}).IsHomogeneous (piece s) :=
    Ideal.homogeneous_span _ _ (by
      intro x hx
      obtain rfl : x = g := hx
      exact ⟨unitGrade i, hg⟩)
  refine ⟨hJ.sup hspan, ?_⟩
  intro t
  let K := J ⊔ Ideal.span {g}
  let A := J.colon {g}
  let e := unitGrade i
  let q := Ideal.Quotient.factorₐ GeoField (show J ≤ K from le_sup_left)
  let cut : quotientPiece s J (t + e) →ₗ[GeoField] quotientPiece s K (t + e) :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y => by
      obtain ⟨b, hb, hby⟩ := y.property
      exact ⟨b, hb, by simpa [q] using congrArg q hby⟩
  have hsurj : Function.Surjective cut := by
    intro y
    obtain ⟨b, hb, hby⟩ := y.property
    exact ⟨⟨Ideal.Quotient.mk J b, ⟨b, hb, rfl⟩⟩, Subtype.ext (by simpa [cut, q] using hby)⟩
  let mu := (quotientMul J g).restrictScalars GeoField
  let emb : quotientPiece s A t →ₗ[GeoField] quotientPiece s J (t + e) :=
    (mu.domRestrict _).codRestrict _ fun y => by
      obtain ⟨b, hb, hby⟩ := y.property
      have hbg : b * g ∈ piece s (t + e) :=
        IsWeightedHomogeneous.mul hb hg
      refine ⟨b * g, hbg, ?_⟩
      change Ideal.Quotient.mk J (b * g) = mu y.val
      change Ideal.Quotient.mk A b = y.val at hby
      rw [← hby]
      exact (quotientMul_mk J g b).symm
  have hInj : Function.Injective emb := fun y z h =>
    Subtype.ext (quotientMul_injective J g (congrArg Subtype.val h))
  have hker : LinearMap.ker cut = LinearMap.range emb := by
    ext y
    obtain ⟨b, hb, hby⟩ := y.property
    have hy : y = ⟨Ideal.Quotient.mk J b, ⟨b, hb, rfl⟩⟩ := Subtype.ext hby.symm
    rw [hy, LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hz
      have hkb : b ∈ K := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa [cut, q] using congrArg Subtype.val hz
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hkb
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      let m := weightedHomogeneousComponent (slotWeight s) t d
      have hm : m ∈ piece s t := weightedHomogeneousComponent_mem _ _ _
      have ha' := weightedHomogeneousComponent_mem_of_mem _ _ hJ ha (t + e)
      have hb' : b.IsWeightedHomogeneous (slotWeight s) (t + e) := hb
      have hdecomp := congrArg (weightedHomogeneousComponent (slotWeight s) (t + e)) hac
      rw [map_add, component_mul_of_grade s hg, weightedHomogeneousComponent_eq_self hb'] at hdecomp
      refine ⟨⟨Ideal.Quotient.mk A m, ⟨m, hm, rfl⟩⟩, Subtype.ext ?_⟩
      change quotientMul J g (Ideal.Quotient.mk A m) = Ideal.Quotient.mk J b
      rw [quotientMul_mk, ← hdecomp, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha', zero_add]
    · rintro ⟨z, hz⟩
      obtain ⟨a, _, haz⟩ := z.property
      apply Subtype.ext
      change Ideal.Quotient.mk K b = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm : a * g ∈ K :=
        Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
      have he := congrArg Subtype.val hz
      change mu z.val = Ideal.Quotient.mk J b at he
      rw [← haz] at he
      change quotientMul J g (Ideal.Quotient.mk A a) = Ideal.Quotient.mk J b at he
      rw [quotientMul_mk, Ideal.Quotient.eq] at he
      have hsub : a * g - (a * g - b) ∈ K := K.sub_mem hm ((show J ≤ K from le_sup_left) he)
      rwa [sub_sub_cancel] at hsub
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, LinearMap.finrank_range_of_inj hInj] at hrank
  exact hrank
end
end K1_13_6_2_4_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace K1_11
noncomputable section
open MvPolynomial
open scoped BigOperators
private theorem ncard_inter_filter {A : Type*} (S : Finset A) (locus : Set A) [DecidablePred (· ∈ locus)] :
    ((S : Set A) ∩ locus).ncard = (S.filter (· ∈ locus)).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  rfl
private theorem one_le_degree_of_point {F σ : Type*} [Field F] [Finite σ]
    (J : Ideal (MvPolynomial σ F)) [J.IsPrime] (x : σ → F) (hx : x ∈ zeroLocus F J) :
    1 ≤ affineDegree J := by
  classical
  generalize hd : (affineHilbertPolynomial J).natDegree = d
  induction d using Nat.strong_induction_on generalizing J with
  | h d ih =>
    by_cases h0 : d = 0
    · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := F) J (hd.trans h0)
      have hxone : 1 ≤ (zeroLocus F J).ncard := by
        simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hx) hfin.1
      exact (by exact_mod_cast hxone : (1 : ℚ) ≤ _).trans hfin.2
    have hproper : ∃ i, MvPolynomial.X i - C (x i) ∉ J := by
      by_contra hn
      push Not at hn
      let φ := Ideal.Quotient.mk J
      have hmaps : φ = φ.comp (C.comp (MvPolynomial.eval x)) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [φ]
        · intro i
          simp only [RingHom.comp_apply, eval_X]
          exact sub_eq_zero.mp (by rw [← map_sub]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hn i))
      have hsurj : Function.Surjective (algebraMap F (MvPolynomial σ F ⧸ J)) := by
        intro q
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine ⟨MvPolynomial.eval x g, ?_⟩
        exact (RingHom.congr_fun hmaps g).symm
      letI : Module.Finite F (MvPolynomial σ F ⧸ J) :=
        Module.Finite.of_surjective (Algebra.linearMap F (MvPolynomial σ F ⧸ J)) hsurj
      exact h0 (by rw [← hd, affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C])
    obtain ⟨i, hi⟩ := hproper
    let f := MvPolynomial.X i - C (x i)
    have hxf : aeval x f = 0 := by simp [f]
    have hfdeg : f.totalDegree ≤ 1 := by
      exact (totalDegree_sub _ _).trans (by simp)
    have hxp : x ∈ zeroLocus F (J ⊔ Ideal.span {f}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx, hxf⟩
    obtain ⟨Q, hQ, hxQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      (J ⊔ Ideal.span {f}) (1 : MvPolynomial σ F) x hxp (by simp)
    have hQmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
    letI : Q.IsPrime := hQmin.isPrime
    have hd' := principalCut_natDegree_affineHilbertPolynomial_add_one hi hQmin
    have hone := ih _ (by omega) Q hxQ rfl
    have hsum := principalCut_sum_affineDegree_retainedMinimalPrimes_le
      (1 : MvPolynomial σ F) hi hfdeg
    have hQsum := Finset.single_le_sum (f := affineDegree)
      (fun A _ => affineDegree_nonneg A) hQ
    simpa only [Nat.cast_one, one_mul] using hone.trans (hQsum.trans hsum)
private theorem prime_count_with_terminal {F σ ι : Type*} [Field F] [Finite σ] [Fintype ι]
    (s : MvPolynomial σ F) (cuts : ι → MvPolynomial σ F) {A L M : ℕ}
    (hLA : L ≤ A) (hdeg : ∀ i, (cuts i).totalDegree ≤ M) {R : ℚ} (hR : 1 ≤ R)
    (hratio : ∀ m < L, (((Fintype.card ι - m) * M : ℕ) : ℚ) ≤ R * ((A - m : ℕ) : ℚ))
    (S : Finset (σ → F)) (hreg : ∀ x ∈ S, aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard)
    (hterminal : ∀ J : Ideal (MvPolynomial σ F), L ≤ {i | cuts i ∈ J}.ncard →
      (((S : Set (σ → F)) ∩ zeroLocus F J).ncard : ℚ) ≤ R)
    (P : Ideal (MvPolynomial σ F)) [P.IsPrime] (W : Finset (σ → F)) (hW : W ⊆ S)
    (hzero : ∀ x ∈ W, x ∈ zeroLocus F P) :
    (W.card : ℚ) ≤ affineDegree P * R ^ (affineHilbertPolynomial P).natDegree := by
  classical
  generalize hd : (affineHilbertPolynomial P).natDegree = d
  induction d using Nat.strong_induction_on generalizing P W with
  | h d ih =>
    rcases W.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simpa using mul_nonneg (affineDegree_nonneg P) (pow_nonneg (zero_le_one.trans hR) d)
    rcases d with _ | e
    · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := F) P hd
      have hcard := Set.ncard_le_ncard
        (fun x (hx : x ∈ (W : Set (σ → F))) => hzero x hx) hfin.1
      rw [Set.ncard_coe_finset] at hcard
      simpa using (by exact_mod_cast hcard : (W.card : ℚ) ≤ _).trans hfin.2
    let keep : Finset ι := Finset.univ.filter fun i => cuts i ∈ P
    have hkeep : keep.card = {i | cuts i ∈ P}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp [keep]
    by_cases hpers : L ≤ keep.card
    · have hc : W.card ≤ ((S : Set (σ → F)) ∩ zeroLocus F P).ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard (fun x hx => ⟨hW hx, hzero x hx⟩)
      have hdegP := one_le_degree_of_point P x₀ (hzero x₀ hx₀)
      calc
        (W.card : ℚ) ≤ (((S : Set (σ → F)) ∩ zeroLocus F P).ncard : ℚ) := by exact_mod_cast hc
        _ ≤ R := hterminal P (hkeep ▸ hpers)
        _ ≤ affineDegree P * R ^ (e+1) := by
          calc
            R = 1 * R ^ (1 : ℕ) := by ring
            _ ≤ affineDegree P * R ^ (e+1) :=
              mul_le_mul hdegP (pow_le_pow_right₀ hR (by omega)) (by positivity) (by linarith)
    let rel : (σ → F) → ι → Prop := fun x i => aeval x (cuts i) = 0
    let c : ℚ := ((A - keep.card : ℕ) : ℚ)
    have hc : 0 < c := by
      change (0 : ℚ) < ((A - keep.card : ℕ) : ℚ)
      exact_mod_cast (by omega : 0 < A - keep.card)
    have hlowNat : W.card * (A - keep.card) ≤ ∑ i ∈ keepᶜ, (W.bipartiteBelow rel i).card := by
      refine Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow rel keep fun x hx => ?_
      rw [← Set.ncard_coe_finset, Finset.coe_bipartiteAbove]
      simpa [rel] using hA x (hW hx)
    have hlow : (W.card : ℚ) * c ≤ ∑ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) := by
      change (W.card : ℚ) * ((A - keep.card : ℕ) : ℚ) ≤ _
      exact_mod_cast hlowNat
    have hcut : ∀ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) ≤ M * affineDegree P * R^e := by
      intro i hi
      have hiP : cuts i ∉ P := by simpa [keep] using hi
      rw [← Set.ncard_coe_finset, Finset.coe_bipartiteBelow]
      refine ncard_inter_cut_le_of_retained_le s hiP (hdeg i) W
        (fun x hx => ⟨hzero x hx, hreg x (hW hx)⟩) (by positivity) fun Q hQ => ?_
      have hQmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
      letI : Q.IsPrime := hQmin.isPrime
      have hQdim : (affineHilbertPolynomial Q).natDegree = e := by
        have := principalCut_natDegree_affineHilbertPolynomial_add_one hiP hQmin
        omega
      rw [ncard_inter_filter]
      exact ih e (by omega) Q _ (fun _ hx => hW (Finset.mem_filter.mp hx).1)
        (fun _ hx => (Finset.mem_filter.mp hx).2) hQdim
    have hupp : ∑ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) ≤
        ((Fintype.card ι - keep.card : ℕ) : ℚ) * (M * affineDegree P * R^e) := by
      refine (Finset.sum_le_card_nsmul _ _ _ hcut).trans_eq ?_
      rw [nsmul_eq_mul, Finset.card_compl]
    refine le_of_mul_le_mul_right (hlow.trans (hupp.trans ?_)) hc
    calc
      ((Fintype.card ι - keep.card : ℕ) : ℚ) * (M * affineDegree P * R^e) =
          (((Fintype.card ι - keep.card) * M : ℕ) : ℚ) * (affineDegree P * R^e) := by
        rw [Nat.cast_mul]
        ring
      _ ≤ (R * c) * (affineDegree P * R^e) :=
        mul_le_mul_of_nonneg_right (hratio keep.card (by omega))
          (mul_nonneg (affineDegree_nonneg P) (pow_nonneg (zero_le_one.trans hR) e))
      _ = (affineDegree P * R^(e+1)) * c := by rw [pow_succ]; ring
private theorem surface_count_with_terminal {F ι : Type*} [Field F] [Fintype ι]
    (g s : MvPolynomial (Fin 3) F) (hg : g ≠ 0) (cuts : ι → MvPolynomial (Fin 3) F)
    {A L M E : ℕ} (hLA : L ≤ A) (hgdeg : g.totalDegree ≤ E) (hdeg : ∀ i, (cuts i).totalDegree ≤ M)
    {R : ℚ} (hR : 1 ≤ R)
    (hratio : ∀ m < L, (((Fintype.card ι - m) * M : ℕ) : ℚ) ≤ R * ((A - m : ℕ) : ℚ))
    (S : Finset (Fin 3 → F)) (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard)
    (hterminal : ∀ J : Ideal (MvPolynomial (Fin 3) F), L ≤ {i | cuts i ∈ J}.ncard →
      (((S : Set (Fin 3 → F)) ∩ zeroLocus F J).ncard : ℚ) ≤ R) :
    (S.card : ℚ) ≤ E * R^2 := by
  classical
  let family := (Ideal.span {g}).retainedMinimalPrimes s
  have hmem (Q) (hQ : Q ∈ family) : g ∈ Q :=
    (Ideal.mem_retainedMinimalPrimes.mp hQ).1.le (Ideal.mem_span_singleton_self g)
  have hdim : ∀ Q ∈ family, (affineHilbertPolynomial Q).natDegree ≤ 2 := by
    intro Q hQ
    simpa [Nat.card_eq_fintype_card] using natDegree_affineHilbertPolynomial_le_of_mem hg (hmem Q hQ)
  have hsum : ∑ Q ∈ family, affineDegree Q ≤ (E : ℚ) := by
    letI : (⊥ : Ideal (MvPolynomial (Fin 3) F)).IsPrime := Ideal.isPrime_bot
    have hnot : g ∉ (⊥ : Ideal (MvPolynomial (Fin 3) F)) := by simpa using hg
    simpa only [family, bot_sup_eq, affineDegree_bot, mul_one] using
      principalCut_sum_affineDegree_retainedMinimalPrimes_le s hnot hgdeg
  refine card_le_mul_pow_of_forall_mem_zeroLocus family hdim hsum hR S (fun x hx => ?_) ?_
  · have hxg : x ∈ zeroLocus F (Ideal.span {g}) := mem_zeroLocus_iff_le_ker_aeval.mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hS x hx).1))
    exact exists_retainedMinimalPrime_of_mem_zeroLocus _ s x hxg (hS x hx).2
  · intro Q hQ
    letI : Q.IsPrime := (Ideal.mem_retainedMinimalPrimes.mp hQ).1.isPrime
    rw [ncard_inter_filter]
    exact prime_count_with_terminal s cuts hLA hdeg hR hratio S
      (fun x hx => (hS x hx).2) hA hterminal Q _
      (fun _ hx => (Finset.mem_filter.mp hx).1) (fun _ hx => (Finset.mem_filter.mp hx).2)
open K1
end
end K1_11
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 K1_13_5_4_2_5 K1_13_5_4_2_5_2
open MeasureTheory Set Filter
open scoped Topology Pointwise ENNReal
private def realCap (b j c h : ℝ) : Set ExponentSpace :=
  {x | (∀ k, 0 ≤ x k) ∧ x 0 + x 1 + x 2 ≤ b ∧
    x 1 + 2 * x 2 ≤ j ∧ x 2 ≤ c ∧ x 3 ≤ h}
private def shiftedCap (P : Set ExponentSpace) (s : Shape) (h : ℕ) (t : ℝ) :
    Set ExponentSpace :=
  realCap ((s.b : ℝ) + t * totalSupport P) ((s.j : ℝ) + t * indexSupport P)
    ((s.t : ℝ) + t * topSupport P) h
private theorem volume_slices {α β : Type} [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)]
    (e : β ≃ᵐ ℝ × α) (he : MeasurePreserving e) {C : Set β} (hC : MeasurableSet C)
    {d : ℝ} (hd : ∀ v ∈ C, (e v).1 ∈ Icc 0 d) :
    volume C = ∫⁻ t in Icc 0 d, volume ((fun v => e.symm (t, v)) ⁻¹' C) := by
  have hpre : MeasurableSet (e.symm ⁻¹' C) := hC.preimage e.symm.measurable
  rw [← (MeasurePreserving.symm e he).measure_preimage_equiv C, Measure.volume_eq_prod,
    Measure.prod_apply hpre, ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Icc 0 d
  · rw [indicator_of_mem ht]
    rfl
  · rw [indicator_of_notMem ht]
    have h : Prod.mk t ⁻¹' (e.symm ⁻¹' C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hv' := hd _ hv
      rw [e.apply_symm_apply] at hv'
      exact ht hv'
    rw [h, measure_empty]
private theorem lintegral_affine {a b d : ℝ} (hd : 0 ≤ d)
    (hn : ∀ x ∈ Icc 0 d, 0 ≤ a + b * x) :
    (∫⁻ x in Icc 0 d, ENNReal.ofReal (a + b * x)) = ENNReal.ofReal (d * a + b * d^2 / 2) := by
  have hi : IntegrableOn (fun x : ℝ => a + b * x) (Icc 0 d) :=
    (show Continuous (fun x : ℝ => a + b * x) by fun_prop).integrableOn_Icc
  have hnn : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc 0 d), 0 ≤ a + b * x :=
    (ae_restrict_mem measurableSet_Icc).mono hn
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd,
    intervalIntegral.integral_add
      (show IntervalIntegrable (fun _ : ℝ => a) volume 0 d from intervalIntegrable_const)
      ((show Continuous (fun x : ℝ => b * x) by fun_prop).intervalIntegrable 0 d),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, smul_eq_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  ring
private abbrev splitLast {n : ℕ} : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)
private theorem splitLast_symm {n : ℕ} (t : ℝ) (v : Fin n → ℝ) :
    splitLast.symm (t, v) = Fin.snoc v t := by
  change @Fin.insertNth n (fun _ => ℝ) (Fin.last n) t v = @Fin.snoc n (fun _ => ℝ) v t
  exact Fin.insertNth_last' t v
private def triangle (d e : ℝ) : Set (Fin 2 → ℝ) :=
  {x | x 1 ∈ Icc 0 e ∧ x 0 ∈ Icc 0 (d - x 1)}
private theorem volume_triangle {d e : ℝ} (he : 0 ≤ e) (hed : e ≤ d) :
    volume (triangle d e) = ENNReal.ofReal (e * d - e^2 / 2) := by
  let equiv : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.finTwoArrow (α := ℝ)).trans MeasurableEquiv.prodComm
  have hpres : MeasurePreserving equiv :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).comp
      (volume_preserving_finTwoArrow ℝ)
  have hm : MeasurableSet (triangle d e) := by
    have h0 : Measurable (fun x : Fin 2 → ℝ => x 0) := measurable_pi_apply 0
    have h1 : Measurable (fun x : Fin 2 → ℝ => x 1) := measurable_pi_apply 1
    exact (measurableSet_Icc.preimage h1).inter
      ((measurableSet_le measurable_const h0).inter (measurableSet_le h0 (by fun_prop)))
  rw [volume_slices equiv hpres hm (fun v hv => hv.1)]
  calc
    _ = ∫⁻ x in Icc 0 e, ENNReal.ofReal (d + (-1) * x) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hsec : (fun v : ℝ => equiv.symm (x, v)) ⁻¹' triangle d e = Icc 0 (d - x) := by
        ext y
        change (x ∈ Icc 0 e ∧ y ∈ Icc 0 (d - x)) ↔ _
        simp [hx]
      dsimp only
      rw [hsec, Real.volume_Icc]
      congr 1
      ring
    _ = _ := by
      rw [lintegral_affine he (fun x hx => by linarith [hx.2])]
      congr 1
      ring
private def oldCap (b j c : ℝ) : Set (Fin 3 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 ≤ b ∧ x 1 + 2 * x 2 ≤ j ∧ x 2 ≤ c}
private theorem measurableSet_oldCap (b j c : ℝ) : MeasurableSet (oldCap b j c) := by
  have horth : MeasurableSet {x : Fin 3 → ℝ | ∀ i, 0 ≤ x i} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  have hb : MeasurableSet {x : Fin 3 → ℝ | x 0 + x 1 + x 2 ≤ b} :=
    measurableSet_le (by fun_prop) measurable_const
  have hj : MeasurableSet {x : Fin 3 → ℝ | x 1 + 2 * x 2 ≤ j} :=
    measurableSet_le (by fun_prop) measurable_const
  have ht : MeasurableSet {x : Fin 3 → ℝ | x 2 ≤ c} :=
    measurableSet_le (measurable_pi_apply 2) measurable_const
  exact horth.inter (hb.inter (hj.inter ht))
private theorem volume_oldCap {b j c : ℝ} (hc : 0 ≤ c) (hbj : j ≤ b) (hjc : 2 * c ≤ j) :
    volume (oldCap b j c) = ENNReal.ofReal (c * (j - c) * (b - j / 2)) := by
  have hbound (v : Fin 3 → ℝ) (hv : v ∈ oldCap b j c) : (splitLast v).1 ∈ Icc 0 c :=
    ⟨hv.1 2, hv.2.2.2⟩
  rw [volume_slices splitLast (volume_preserving_piFinSuccAbove _ _) (measurableSet_oldCap b j c) hbound]
  calc
    _ = ∫⁻ z in Icc 0 c, ENNReal.ofReal (j * (b - j / 2) + (-2 * (b - j / 2)) * z) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro z hz
      have hsec : (fun v : Fin 2 → ℝ => splitLast.symm (z, v)) ⁻¹' oldCap b j c =
          triangle (b - z) (j - 2 * z) := by
        ext v
        have h0 : (@Fin.snoc 2 (fun _ => ℝ) v z) 0 = v 0 :=
          @Fin.snoc_castSucc 2 (fun _ => ℝ) z v 0
        have h1 : (@Fin.snoc 2 (fun _ => ℝ) v z) 1 = v 1 :=
          @Fin.snoc_castSucc 2 (fun _ => ℝ) z v 1
        have h2 : (@Fin.snoc 2 (fun _ => ℝ) v z) 2 = z :=
          @Fin.snoc_last 2 (fun _ => ℝ) z v
        simp only [mem_preimage, splitLast_symm, oldCap, triangle, mem_ofPred_eq, mem_Icc,
          Fin.forall_iff_castSucc (n := 2), Fin.snoc_last, Fin.snoc_castSucc, Fin.forall_fin_two,
          h0, h1, h2]
        change ((0 ≤ z ∧ 0 ≤ v 0 ∧ 0 ≤ v 1) ∧ v 0 + v 1 + z ≤ b ∧
          v 1 + 2 * z ≤ j ∧ z ≤ c) ↔ ((0 ≤ v 1 ∧ v 1 ≤ j - 2 * z) ∧
          0 ≤ v 0 ∧ v 0 ≤ b - z - v 1)
        constructor
        · rintro ⟨⟨_, hv0, hv1⟩, hb', hj', _⟩
          exact ⟨⟨hv1, by linarith⟩, hv0, by linarith⟩
        · rintro ⟨⟨hv1, hj'⟩, hv0, hb'⟩
          exact ⟨⟨hz.1, hv0, hv1⟩, by linarith, by linarith, hz.2⟩
      dsimp only
      rw [hsec, volume_triangle (by linarith [hz.2]) (by linarith [hz.1])]
      congr 1
      ring
    _ = _ := by
      rw [lintegral_affine hc (fun z hz => by
        have h1 : 0 ≤ j - 2 * z := by linarith [hz.2]
        have h2 : 0 ≤ b - j / 2 := by linarith
        nlinarith [mul_nonneg h1 h2])]
      congr 1
      ring
theorem realCap_volume {b j c h : ℝ} (hc : 0 ≤ c) (hbj : j ≤ b)
    (hjc : 2 * c ≤ j) (hh : 0 ≤ h) :
    (volume (realCap b j c h)).toReal = h * c * (j - c) * (b - j / 2) := by
  have hcap : realCap b j c h = {x | (fun i : Fin 3 => x i.castSucc) ∈ oldCap b j c ∧
      x 3 ∈ Icc 0 h} := by
    ext x
    simp only [realCap, oldCap, mem_ofPred_eq, mem_Icc, Fin.forall_iff_castSucc (n := 3)]
    change ((0 ≤ x 3 ∧ ∀ i : Fin 3, 0 ≤ x i.castSucc) ∧
      x 0 + x 1 + x 2 ≤ b ∧ x 1 + 2 * x 2 ≤ j ∧ x 2 ≤ c ∧ x 3 ≤ h) ↔
      ((∀ i : Fin 3, 0 ≤ x i.castSucc) ∧ x 0 + x 1 + x 2 ≤ b ∧
      x 1 + 2 * x 2 ≤ j ∧ x 2 ≤ c) ∧ 0 ≤ x 3 ∧ x 3 ≤ h
    tauto
  have hm : MeasurableSet (realCap b j c h) := by
    rw [hcap]
    exact ((measurableSet_oldCap _ _ _).preimage
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.castSucc))).inter
        (measurableSet_Icc.preimage (measurable_pi_apply 3))
  have hbound (v : ExponentSpace) (hv : v ∈ realCap b j c h) :
      (splitLast v).1 ∈ Icc 0 h := ⟨hv.1 3, hv.2.2.2.2⟩
  have hvol : volume (realCap b j c h) = volume (oldCap b j c) * ENNReal.ofReal h := by
    rw [volume_slices splitLast (volume_preserving_piFinSuccAbove _ _) hm hbound]
    calc
      _ = ∫⁻ _ in Icc 0 h, volume (oldCap b j c) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro z hz
        dsimp only
        congr 1
        ext v
        have h3 : (@Fin.snoc 3 (fun _ => ℝ) v z) 3 = z :=
          @Fin.snoc_last 3 (fun _ => ℝ) z v
        simp [hcap, splitLast_symm, h3, hz.1, hz.2]
      _ = _ := by rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  have hn : 0 ≤ c * (j - c) * (b - j / 2) :=
    mul_nonneg (mul_nonneg hc (by linarith)) (by linarith)
  rw [hvol, volume_oldCap hc hbj hjc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hh]
  ring
theorem realCap_clip (b j c h : ℝ) :
    realCap b j c h = realCap b j (min c (j / 2)) h := by
  ext x
  simp only [realCap, mem_ofPred_eq, le_min_iff]
  constructor
  · rintro ⟨hx, hb, hj, hc, hh⟩
    exact ⟨hx, hb, hj, ⟨hc, by linarith [hx 1]⟩, hh⟩
  · rintro ⟨hx, hb, hj, ⟨hc, _⟩, hh⟩
    exact ⟨hx, hb, hj, hc, hh⟩
private theorem shiftedCap_tendsto (P : Set ExponentSpace) (s : Shape) (h : ℕ)
    (hs : K1_13_5_4_2_5.Chamber s) (hjb : s.j < s.b) (htop : 0 < s.t) :
    Filter.Tendsto
      (fun t : ℝ => ((volume (shiftedCap P s h t)).toReal -
        (volume (capBody s h)).toReal) / t)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (K1_13_5_4_2_5_2.capFirstVariation s h
        (K1_13_5_4_2_5_2.totalSupport P) (K1_13_5_4_2_5_2.indexSupport P)
        (K1_13_5_4_2_5_2.topSupport P))) := by
  classical
  let b : ℝ := s.b
  let j : ℝ := s.j
  let c : ℝ := s.t
  let B : ℝ := totalSupport P
  let J : ℝ := indexSupport P
  let T : ℝ := topSupport P
  let U : ℝ := if 2 * c = j then min T (J / 2) else T
  have hc : 0 < c := by
    change (0 : ℝ) < (s.t : ℝ)
    exact_mod_cast htop
  have hj : j < b := by
    change (s.j : ℝ) < (s.b : ℝ)
    exact_mod_cast hjb
  have hcj : 2 * c ≤ j := by
    change 2 * (s.t : ℝ) ≤ (s.j : ℝ)
    exact_mod_cast hs.2
  have hline (a m : ℝ) : HasDerivAt (fun t : ℝ => a + t * m) m 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const m).const_add a
  have hpositive : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), 0 < c + t * U :=
    (Filter.Tendsto.eventually
      (show Filter.Tendsto (fun t : ℝ => c + t * U) (𝓝 0) (𝓝 c) by
        simpa [ContinuousAt] using (hline c U).continuousAt) (Ioi_mem_nhds hc)).filter_mono nhdsWithin_le_nhds
  have hchamber : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), j + t * J < b + t * B :=
    ((hline j J).continuousAt.eventually_lt (hline b B).continuousAt (by simpa using hj)).filter_mono
      nhdsWithin_le_nhds
  have heff : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ),
      min (c + t * T) ((j + t * J) / 2) = c + t * U := by
    by_cases heq : 2 * c = j
    · filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with t ht
      have ht' : 0 ≤ t := (show 0 < t from ht).le
      rw [show (j + t * J) / 2 = c + t * (J / 2) by rw [← heq]; ring]
      by_cases hTJ : T ≤ J / 2
      · rw [min_eq_left (add_le_add_right (mul_le_mul_of_nonneg_left hTJ ht') _)]
        simp [U, heq, min_eq_left hTJ]
      · have hJT := (lt_of_not_ge hTJ).le
        rw [min_eq_right (add_le_add_right (mul_le_mul_of_nonneg_left hJT ht') _)]
        simp [U, heq, min_eq_right hJT]
    · have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), c + t * T < (j + t * J) / 2 :=
        (hline c T).continuousAt.eventually_lt
          ((hline j J).div_const 2).continuousAt (by
            simp only [zero_mul, add_zero]
            linarith [lt_of_le_of_ne hcj heq])
      filter_upwards [hnear.filter_mono (nhdsWithin_le_nhds
        (s := Ioi (0 : ℝ)))] with t ht
      simp [U, heq, min_eq_left ht.le]
  let f := fun t : ℝ => (h : ℝ) * (c + t * U) *
    ((j + t * J) - (c + t * U)) * ((b + t * B) - (j + t * J) / 2)
  have hcoef : (j - 2 * c) * U = (j - 2 * c) * T := by
    by_cases heq : 2 * c = j
    · rw [show j - 2 * c = 0 by linarith, zero_mul, zero_mul]
    · simp [U, heq]
  have hf : HasDerivAt f ((h : ℝ) * (c * (j - c) * B +
      c * (b - j + c / 2) * J + (j - 2 * c) * (b - j / 2) * T)) 0 := by
    convert ((((hline c U).const_mul (h : ℝ)).mul
      ((hline j J).sub (hline c U))).mul
      ((hline b B).sub ((hline j J).div_const 2))) using 1
    simp only [Pi.mul_apply, Pi.sub_apply, zero_mul, add_zero]
    calc
      _ = (h : ℝ) * (c * (j - c) * B + c * (b - j + c / 2) * J +
          (b - j / 2) * ((j - 2 * c) * T)) := by ring
      _ = _ := by rw [← hcoef]; ring
  have hlim := hf.tendsto_slope_zero_right
  have hbase : (volume (capBody s h)).toReal = f 0 := by
    change (volume (realCap b j c h)).toReal = _
    rw [realCap_volume hc.le hj.le hcj (by positivity)]
    simp [f]
  apply hlim.congr'
  filter_upwards [hpositive, hchamber, heff] with t hp hb he
  have hclip : 2 * (c + t * U) ≤ j + t * J := by
    rw [← he]
    linarith [min_le_right (c + t * T) ((j + t * J) / 2)]
  change t⁻¹ • (f (0 + t) - f 0) =
    ((volume (realCap (b + t * B) (j + t * J) (c + t * T) h)).toReal -
      (volume (capBody s h)).toReal) / t
  rw [realCap_clip, he, realCap_volume hp.le hb.le hclip (by positivity), hbase,
    zero_add, smul_eq_mul, div_eq_mul_inv]
  exact mul_comm _ _
def normals : Matrix (Fin 6) (Fin 4) ℝ :=
  ![![1,1,1,0], ![0,1,2,0], ![0,0,1,0], ![-1,0,0,0], ![0,-1,0,0], ![0,0,-1,0]]
private def form (i : Fin 6) : ExponentSpace →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (Matrix.toLin' normals)
private theorem form_apply (i : Fin 6) (x : ExponentSpace) :
    form i x = (![x 0 + x 1 + x 2, x 1 + 2 * x 2, x 2, -x 0, -x 1, -x 2] :
      Fin 6 → ℝ) i := by
  change ((Matrix.toLin' normals) x) i = _
  rw [Matrix.toLin'_apply]
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four, normals]
private theorem form_fun (i : Fin 6) :
    (form i : ExponentSpace → ℝ) =
      (fun x => (![x 0 + x 1 + x 2, x 1 + 2 * x 2, x 2, -x 0, -x 1, -x 2] :
        Fin 6 → ℝ) i) :=
  funext (form_apply i)
private def bounds (s : Shape) : Fin 6 → ℝ := ![s.b, s.j, s.t, 0, 0, 0]
private theorem mem_realCap {b j c h : ℝ} {x : ExponentSpace} :
    x ∈ realCap b j c h ↔ x 3 ∈ Icc 0 h ∧
      ∀ i, form i x ≤ (![b, j, c, 0, 0, 0] : Fin 6 → ℝ) i := by
  simp [realCap, Fin.forall_fin_succ, form_apply]
  tauto
private def support (P : Set ExponentSpace) (i : Fin 6) : ℝ := sSup (form i '' P)
private theorem support_attains {P : Set ExponentSpace} (hc : IsCompact P)
    (h0 : 0 ∈ P) (i : Fin 6) :
    ∃ p ∈ P, form i p = support P i ∧ ∀ q ∈ P, form i q ≤ support P i := by
  obtain ⟨p, hp, hm⟩ := hc.exists_isMaxOn ⟨0, h0⟩ (form i).continuous_of_finiteDimensional.continuousOn
  have hle : ∀ q ∈ P, form i q ≤ form i p := fun q hq => hm hq
  have hsup : support P i = form i p := by
    refine le_antisymm (csSup_le ⟨form i p, mem_image_of_mem _ hp⟩ ?_) (le_csSup ?_ (mem_image_of_mem _ hp))
    · rintro _ ⟨q, hq, rfl⟩
      exact hle q hq
    · exact ⟨form i p, by rintro _ ⟨q, hq, rfl⟩; exact hle q hq⟩
  exact ⟨p, hp, hsup.symm, hsup ▸ hle⟩
private abbrev Pair := Fin 6 × Fin 6
private def nonparallel (p : Pair) : Prop :=
  p.1.val < 3 ∧ p.1 ≠ p.2 ∧ (p.1 ≠ 2 ∨ p.2 ≠ 5)
private instance (p : Pair) : Decidable (nonparallel p) := by
  unfold nonparallel
  infer_instance
private def remaining (p : Pair) : Fin 4 :=
  (![![0,2,1,2,2,1], ![2,0,0,2,0,0], ![1,0,0,1,0,0], 0, 0, 0] :
    Fin 6 → Fin 6 → Fin 4) p.1 p.2
private def slabMatrix (p : Pair) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![normals p.1, normals p.2, fun i => if i = remaining p then 1 else 0, ![0,0,0,1]]
theorem slabMatrix_det (p : Pair) :
    (slabMatrix p).det = ((slabMatrix p).submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last 3), Fin.sum_univ_four]
  have h0 : slabMatrix p (Fin.last 3) 0 = 0 := rfl
  have h1 : slabMatrix p (Fin.last 3) 1 = 0 := rfl
  have h2 : slabMatrix p (Fin.last 3) 2 = 0 := rfl
  have h3 : slabMatrix p (Fin.last 3) (Fin.last 3) = 1 := rfl
  simp only [h0, h1, h2, mul_zero, zero_mul, zero_add]
  change (-1 : ℝ)^6 * slabMatrix p (Fin.last 3) (Fin.last 3) *
      ((slabMatrix p).submatrix (Fin.last 3).succAbove (Fin.last 3).succAbove).det = _
  rw [h3, Fin.succAbove_last]
  norm_num
private theorem slabMatrix_invertible (p : Pair) (hp : nonparallel p) : (slabMatrix p).det ≠ 0 := by
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> norm_num [nonparallel] at hp
  all_goals
    rw [slabMatrix_det, Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply,
      show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl]
    norm_num [slabMatrix, normals, remaining]
private theorem slabMap_apply (p : Pair) (x : ExponentSpace) :
    Matrix.toLin' (slabMatrix p) x = ![form p.1 x, form p.2 x, x (remaining p), x 3] := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · rw [Matrix.toLin'_apply]
    change (∑ k, (if k = remaining p then 1 else (0 : ℝ)) * x k) = _
    simp [ite_mul]
  · rw [Matrix.toLin'_apply]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four, slabMatrix]
private def slabRegion (a : Fin 6 → ℝ) (R e : ℝ) (p : Pair) : Set ExponentSpace :=
  if nonparallel p then
    Matrix.toLin' (slabMatrix p) ⁻¹'
      Icc (![a p.1 - e, a p.2 - e, 0, 0] : ExponentSpace) ![a p.1 + e, a p.2 + e, R, R]
  else ∅
private theorem volume_slabRegion (a : Fin 6 → ℝ) {R e : ℝ} (hR : 0 ≤ R) (he : 0 ≤ e)
    (p : Pair) :
    volume (slabRegion a R e p) ≤ ENNReal.ofReal (|(slabMatrix p).det⁻¹| * 4 * R^2 * e^2) := by
  unfold slabRegion
  split_ifs with hp
  · rw [Measure.addHaar_preimage_linearMap volume (by rw [LinearMap.det_toLin']; exact slabMatrix_invertible p hp),
      LinearMap.det_toLin', Real.volume_Icc_pi, Fin.prod_univ_four]
    have hwidth (w : ℝ) : w + e - (w - e) = 2 * e := by ring
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hwidth, sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * e), ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * e * (2 * e)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * e * (2 * e) * R),
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    apply le_of_eq
    congr 1
    ring
  · simp
end
end K1_13_5_4_2_5_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3_2
noncomputable section
open K1_13_5_4_2_4_2_3 MvPolynomial
open K1_13_5_4_2_4 (CoefficientRing CoefficientField)
open scoped nonZeroDivisors
private abbrev IntegralSlots (A : Supports) := MvPolynomial (Slot A) (CoefficientRing A)
private def integralEquation (A : Supports) (i : Fin 4) : IntegralSlots A :=
  ∑ a : ↥(A i), C (MvPolynomial.X ⟨i, a⟩) * MvPolynomial.X ⟨i, a⟩
private def integralChart (A : Supports) (b : (j : Fin 4) → ↥(A j)) : IntegralSlots A :=
  ∏ j : Fin 4, MvPolynomial.X ⟨j, b j⟩
private def equationIdeal (A : Supports) (k : ℕ) : Ideal (IntegralSlots A) :=
  Ideal.span (integralEquation A '' {i : Fin 4 | i.val < k})
private def integralIdeal (A : Supports) (k : ℕ) : Ideal (IntegralSlots A) :=
  binomialIdeal A (CoefficientRing A) ⊔ equationIdeal A k
private abbrev swap (A : Supports) := commAlgEquiv Geo (Slot A) (Slot A)
private def toModel (A : Supports) : IntegralSlots A →+* UniversalRing A :=
  (MvPolynomial.map (Ideal.Quotient.mk (binomialIdeal A Geo))).comp (swap A).toRingHom
private theorem toModel_surjective (A : Supports) : Function.Surjective (toModel A) :=
  (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp (swap A).surjective
private theorem toModel_ker (A : Supports) :
    RingHom.ker (toModel A) = binomialIdeal A (CoefficientRing A) := by
  have hswap : (swap A).toRingHom.comp (MvPolynomial.map (C (σ := Slot A))) = C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [swap]
    · intro v
      simp [swap]
  have hker : RingHom.ker (swap A).toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot (swap A).toRingHom).mp (swap A).injective
  rw [toModel, ← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← hswap,
    ← Ideal.map_map, Ideal.comap_map_of_surjective (swap A).toRingHom (swap A).surjective,
    ← RingHom.ker_eq_comap_bot, hker,
    sup_bot_eq, map_binomialIdeal]
private theorem toModel_chart (A : Supports) (b : (j : Fin 4) → ↥(A j)) :
    toModel A (integralChart A b) = C (modelChart A b) := by
  simp [integralChart, toModel, modelChart, coordinate]
private theorem integralIdeal_eq (A : Supports) (k : ℕ) :
    integralIdeal A k = (modelIdeal A k).comap (toModel A) := by
  have hmap : (equationIdeal A k).map (toModel A) = modelIdeal A k := by
    rw [equationIdeal, modelIdeal, Ideal.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    simp [integralEquation, modelEquation, toModel, coordinate]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [← hmap, Ideal.comap_map_of_surjective _ (toModel_surjective A),
    ← RingHom.ker_eq_comap_bot, toModel_ker, integralIdeal, sup_comm]
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev extendCoefficients (A : Supports) := algebraMap (IntegralSlots A) (SlotRing A)
private theorem extend_chart (A : Supports) (b : (j : Fin 4) → ↥(A j)) :
    extendCoefficients A (integralChart A b) = chartProduct A b := by
  change MvPolynomial.map (algebraMap (CoefficientRing A) (CoefficientField A))
    (integralChart A b) = chartProduct A b
  simp only [integralChart, chartProduct, map_prod, map_X]
private theorem extend_ideal (A : Supports) (k : ℕ) :
    (integralIdeal A k).map (extendCoefficients A) = cutIdeal A k := by
  change (integralIdeal A k).map
    (MvPolynomial.map (algebraMap (CoefficientRing A) (CoefficientField A))) = cutIdeal A k
  rw [integralIdeal, Ideal.map_sup, map_binomialIdeal,
    ← relationIdeal_zero, cutIdeal, equationIdeal, Ideal.map_span, Set.image_image]
  congr 2
  apply Set.image_congr
  intro i _
  simp only [integralEquation, homogeneousEquation, map_sum, map_mul, map_C, map_X]
set_option maxHeartbeats 800000 in
theorem proof : K1_13_5_4_2_4_2_3.c2 := by
  classical
  intro A hz i b f n hf
  let k := i.val + 1
  let b₀ (j : Fin 4) : ↥(A j) := ⟨0, hz j⟩
  let I := integralIdeal A k
  let e := extendCoefficients A
  let M := (CoefficientRing A)⁰.map (C (σ := Slot A))
  have : IsLocalization M (SlotRing A) :=
    MvPolynomial.isLocalization (CoefficientRing A)⁰ (CoefficientField A)
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj M f
  change f * e s = e p at hs
  have hc : e (integralChart A b₀) = constantChart A hz := extend_chart A b₀
  have hp : e (integralChart A b₀ ^ n * p) ∈ I.map e := by
    rw [show I.map e = cutIdeal A k from extend_ideal A k, map_mul, map_pow, hc, ← hs,
      ← mul_assoc]
    exact (cutIdeal A k).mul_mem_right _ hf
  obtain ⟨d, hd, hpre⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M _ I _).mp hp
  have hpre' : integralChart A b₀ ^ n * (d * p) ∈ integralIdeal A k := by
    rw [mul_left_comm (integralChart A b₀ ^ n) d p]
    exact hpre
  have hmod : C (modelChart A b₀) ^ n * toModel A (d * p) ∈ modelIdeal A k := by
    rw [integralIdeal_eq] at hpre'
    change toModel A (integralChart A b₀ ^ n * (d * p)) ∈ modelIdeal A k at hpre'
    simpa only [map_mul, map_pow, toModel_chart] using hpre'
  obtain ⟨m, hm⟩ := model_saturate A k b (modelChart_ne_zero A b₀) (toModel A (d * p)) n hmod
  have hm' : integralChart A b ^ m * (d * p) ∈ I := by
    change _ ∈ integralIdeal A k
    rw [integralIdeal_eq]
    change toModel A (integralChart A b ^ m * (d * p)) ∈ modelIdeal A k
    simpa only [map_mul, map_pow, toModel_chart] using hm
  have hresult := Ideal.mem_map_of_mem e hm'
  rw [show I.map e = cutIdeal A k from extend_ideal A k, map_mul, map_pow, extend_chart,
    map_mul, ← hs] at hresult
  have hds : IsUnit (e d) := IsLocalization.map_units (SlotRing A) ⟨d, hd⟩
  have hss : IsUnit (e s) := IsLocalization.map_units (SlotRing A) s
  refine ⟨m, (Ideal.unit_mul_mem_iff_mem _ (hds.mul hss)).mp ?_⟩
  rw [mul_assoc (e d) (e s), mul_left_comm (e s) (chartProduct A b ^ m),
    mul_left_comm (e d) (chartProduct A b ^ m), mul_comm (e s) f]
  exact hresult
end
end K1_13_5_4_2_4_2_3_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_3
open K1_13_5_4_2 K1_13_5_4_2_4
open scoped Pointwise
noncomputable section
theorem sum_mem_nsmul {ι : Type*} (t : Finset ι) (D : Set Exponent)
    (k : ι → ℕ) (v : ι → Exponent) (h : ∀ i ∈ t, v i ∈ k i • D) :
    (∑ i ∈ t, v i) ∈ (∑ i ∈ t, k i) • D := by
  rw [← Finset.sum_nsmul_assoc]
  exact Set.finsetSum_mem_finsetSum t _ v h
theorem exists_padding {D : Set Exponent} (hD : D.Finite) (hzero : 0 ∈ D)
    (hunit : ∀ a ∈ D, ∀ j, 0 < a j → Finsupp.single j 1 ∈ D) :
    ∃ c : ℕ, ∀ (m : ℕ) (y : ExponentSpace), y ∈ latticeBody D →
      ∃ a ∈ (m + c) • D, ∀ j, (a j : ℝ) ≤ (m : ℝ) * y j ∧
        (m : ℝ) * y j < (a j : ℝ) + 1 := by
  classical
  let _ : Fintype D := hD.fintype
  let bound (j : Fin 4) : ℕ := ∑ a : D, a.val j
  refine ⟨∑ j, bound j, ?_⟩
  intro m y hy
  let v (a : D) : ExponentSpace := exponentVector a.val
  have himage : exponentVector '' D = Set.range v := by
    ext x
    exact ⟨fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩, fun ⟨a, h⟩ => ⟨a.val, a.property, h⟩⟩
  rw [latticeBody, himage, convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨t, w, hw, hsum, hy⟩ := hy
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hy
  let u (a : D) : ℝ := (m : ℝ) * w a
  let k (a : D) : ℕ := ⌊u a⌋₊
  have hu (a : D) (ha : a ∈ t) : 0 ≤ u a := mul_nonneg (Nat.cast_nonneg _) (hw a ha)
  have hk (a : D) (ha : a ∈ t) : (k a : ℝ) ≤ u a := Nat.floor_le (hu a ha)
  have hdegrees : (∑ a ∈ t, k a) ≤ m := by
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ a ∈ t, u a := Finset.sum_le_sum hk
      _ = (m : ℝ) := by simp [u, ← Finset.mul_sum, hsum]
  let r (j : Fin 4) : ℝ := ∑ a ∈ t, (u a - (k a : ℝ)) * (a.val j : ℝ)
  let l (j : Fin 4) : ℕ := ⌊r j⌋₊
  have hr (j : Fin 4) : 0 ≤ r j :=
    Finset.sum_nonneg fun a ha => mul_nonneg (sub_nonneg.mpr (hk a ha)) (Nat.cast_nonneg _)
  have hbound (j : Fin 4) : l j ≤ bound j := by
    apply Nat.floor_le_of_le
    calc
      r j ≤ ∑ a ∈ t, (a.val j : ℝ) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        exact mul_le_of_le_one_left (Nat.cast_nonneg _)
          (by have h := Nat.lt_floor_add_one (u a); change u a < (k a : ℝ) + 1 at h; linarith)
      _ ≤ (bound j : ℝ) := by
        rw [show (bound j : ℝ) = ∑ a : D, (a.val j : ℝ) by simp [bound, Nat.cast_sum]]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.cast_nonneg _)
  have haxes (j : Fin 4) (hj : l j ≠ 0) : Finsupp.single j 1 ∈ D := by
    by_contra h
    have hv (a : D) : a.val j = 0 :=
      Nat.eq_zero_of_not_pos (fun ha => h (hunit a.val a.property j ha))
    exact hj (by simp [l, r, hv])
  let b : Exponent := ∑ a ∈ t, k a • a.val
  let d : Exponent := ∑ j, l j • Finsupp.single j 1
  have hb : b ∈ (∑ a ∈ t, k a) • D :=
    sum_mem_nsmul t D k _ (fun a _ => Set.nsmul_mem_nsmul a.property)
  have hd : d ∈ (∑ j, l j) • D := by
    refine sum_mem_nsmul Finset.univ D l _ (fun j _ => ?_)
    by_cases hj : l j = 0
    · simp [hj]
    · exact Set.nsmul_mem_nsmul (haxes j hj)
  have hbd : b + d ∈ (m + ∑ j, bound j) • D := by
    apply Set.nsmul_subset_nsmul_right hzero (Nat.add_le_add hdegrees (Finset.sum_le_sum fun j _ => hbound j))
    rw [add_nsmul]
    exact Set.add_mem_add hb hd
  refine ⟨b + d, hbd, fun j => ?_⟩
  have hdj : d j = l j := by
    change (∑ i : Fin 4, l i • Finsupp.single i 1) j = l j
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have hbj : (b j : ℝ) = ∑ a ∈ t, (k a : ℝ) * (a.val j : ℝ) := by
    simp [b, Finsupp.finsetSum_apply, Finsupp.smul_apply, Nat.cast_sum]
  have hyj : (m : ℝ) * y j = ∑ a ∈ t, u a * (a.val j : ℝ) := by
    rw [← hy]
    simp [v, exponentVector, Finset.sum_apply, smul_eq_mul, u, Finset.mul_sum, mul_assoc]
  have hdecomp : (m : ℝ) * y j = (b j : ℝ) + r j := by
    rw [hyj, hbj]
    simp only [r, sub_mul, Finset.sum_sub_distrib]
    abel
  change ((b j + d j : ℕ) : ℝ) ≤ (m : ℝ) * y j ∧
    (m : ℝ) * y j < ((b j + d j : ℕ) : ℝ) + 1
  rw [Nat.cast_add, hdj, hdecomp]
  have hlo := Nat.floor_le (hr j)
  have hhi := Nat.lt_floor_add_one (r j)
  change (l j : ℝ) ≤ r j at hlo
  change r j < (l j : ℝ) + 1 at hhi
  constructor <;> linarith
end
end K1_13_5_4_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_3
open K1_13_5_4_2 K1_13_5_4_2_4 Filter MeasureTheory
open scoped ENNReal Pointwise Topology
noncomputable section
local instance : Dist ExponentSpace := (inferInstance : PseudoMetricSpace ExponentSpace).toDist
theorem finite_nsmul {D : Set Exponent} (hD : D.Finite) (n : ℕ) :
    (n • D).Finite := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [add_nsmul, one_nsmul]
    exact ih.add hD
def gridBox (n : ℕ) (a : Exponent) : Set ExponentSpace :=
  Set.univ.pi fun j => Set.Ico ((a j : ℝ) / n) (((a j : ℝ) + 1) / n)
def gridUnion (n : ℕ) (T : Set Exponent) : Set ExponentSpace :=
  ⋃ a ∈ T, gridBox n a
theorem mem_gridBox {n : ℕ} (hn : 0 < n) {a : Exponent} {x : ExponentSpace} :
    x ∈ gridBox n a ↔ ∀ j, (a j : ℝ) ≤ (n : ℝ) * x j ∧
      (n : ℝ) * x j < (a j : ℝ) + 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [gridBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
    div_le_iff₀ hn', lt_div_iff₀ hn']
  exact forall_congr' fun j => by rw [mul_comm (x j)]
theorem volume_gridUnion {n : ℕ} (hn : 0 < n) {T : Set Exponent}
    (hT : T.Finite) :
    (volume (gridUnion n T)).toReal = (T.ncard : ℝ) / (n : ℝ)^4 := by
  classical
  have hdisj : (↑hT.toFinset : Set Exponent).PairwiseDisjoint (gridBox n) := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun x ha hb => hab ?_
    ext j
    have ha' := (mem_gridBox hn).mp ha j
    have hb' := (mem_gridBox hn).mp hb j
    have hx : 0 ≤ (n : ℝ) * x j := (Nat.cast_nonneg _).trans ha'.1
    exact ((Nat.floor_eq_iff hx).mpr ha').symm.trans ((Nat.floor_eq_iff hx).mpr hb')
  have hbox (a : Exponent) : MeasurableSet (gridBox n a) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hvol (a : Exponent) :
      volume (gridBox n a) = (ENNReal.ofReal (1 / (n : ℝ)))^4 := by
    rw [gridBox, Real.volume_pi_Ico]
    have hlength (j : Fin 4) : ((a j : ℝ) + 1) / n - (a j : ℝ) / n = 1 / (n : ℝ) := by
      ring
    simp only [hlength, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hunion : gridUnion n T = ⋃ a ∈ hT.toFinset, gridBox n a := by
    ext x
    simp only [gridUnion, Set.mem_iUnion, Set.Finite.mem_toFinset]
  rw [hunion, measure_biUnion_finset hdisj (fun a _ => hbox a), Set.ncard_eq_toFinset_card T hT]
  simp only [hvol, Finset.sum_const]
  rw [ENNReal.toReal_nsmul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  rw [nsmul_eq_mul, one_div, inv_pow, div_eq_mul_inv]
theorem nsmul_latticeBody {D : Set Exponent} (hD : 0 ∈ D) (n : ℕ) :
    n • latticeBody D = (n : ℝ) • latticeBody D := by
  have h0 : (0 : ExponentSpace) ∈ latticeBody D :=
    subset_convexHull ℝ _ ⟨0, hD, map_zero exponentVector⟩
  induction n with
  | zero =>
    rw [zero_nsmul, Nat.cast_zero, Set.zero_smul_set ⟨0, h0⟩]
  | succ n ih =>
    rw [add_nsmul, one_nsmul, ih, Nat.cast_add, Nat.cast_one]
    have hconv : Convex ℝ (latticeBody D) := convex_convexHull ℝ _
    rw [hconv.add_smul (Nat.cast_nonneg n) zero_le_one, one_smul]
theorem gridUnion_subset_cthickening {B D : Set Exponent} {n : ℕ}
    (hn : 0 < n) (hD : 0 ∈ D) {R : ℝ} (hR : ∀ b ∈ B, ‖exponentVector b‖ ≤ R) :
    gridUnion n (B + n • D) ⊆ Metric.cthickening ((1 + R) / n) (latticeBody D) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  intro x hx
  obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨b, hb, d, hd, rfl⟩ := Set.mem_add.mp ha
  have hscaled : exponentVector d ∈ (n : ℝ) • latticeBody D := by
    rw [← nsmul_latticeBody hD n]
    apply Set.nsmul_subset_nsmul_left (subset_convexHull ℝ _)
    rw [← Set.image_nsmul exponentVector]
    exact ⟨d, hd, rfl⟩
  obtain ⟨y, hy, hyd⟩ := hscaled
  let z : ExponentSpace := (n : ℝ)⁻¹ • exponentVector (b + d)
  have hxy : dist x z ≤ 1 / (n : ℝ) := by
    rw [dist_pi_le_iff (by positivity)]
    intro j
    obtain ⟨hlo, hhi⟩ := (mem_gridBox hn).mp hx j
    change (↑((b + d) j) : ℝ) ≤ (n : ℝ) * x j at hlo
    change (n : ℝ) * x j < (↑((b + d) j) : ℝ) + 1 at hhi
    have hz : z j = (↑((b + d) j) : ℝ) / n := by
      change (n : ℝ)⁻¹ * (↑((b + d) j) : ℝ) = _
      rw [div_eq_mul_inv, mul_comm]
    rw [Real.dist_eq, hz, abs_le]
    have hlo' := (div_le_iff₀ hn').mpr (by simpa only [mul_comm] using hlo :
      (↑((b + d) j) : ℝ) ≤ x j * n)
    have hhi' : x j < ((↑((b + d) j) : ℝ) + 1) / n := (lt_div_iff₀ hn').mpr
      (by simpa only [mul_comm] using hhi)
    rw [add_div] at hhi'
    constructor <;> linarith
  have hzy : dist z y ≤ R / (n : ℝ) := by
    have heq : z = (n : ℝ)⁻¹ • exponentVector b + y := by
      dsimp [z]
      rw [map_add, smul_add, ← hyd, smul_smul, inv_mul_cancel₀ hn'.ne', one_smul]
    rw [dist_eq_norm, heq, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hn'.le), div_eq_mul_inv, mul_comm R]
    exact mul_le_mul_of_nonneg_left (hR b hb) (inv_nonneg.mpr hn'.le)
  apply Metric.mem_cthickening_of_dist_le x y _ _ hy
  calc
    dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
    _ ≤ 1 / (n : ℝ) + R / n := add_le_add hxy hzy
    _ = _ := (add_div _ _ _).symm
theorem tendsto_diagonal {B D : Set Exponent} (hB : B.Finite) (hD : D.Finite)
    (hB0 : 0 ∈ B) (hD0 : 0 ∈ D)
    (hunit : ∀ a ∈ D, ∀ j, 0 < a j → Finsupp.single j 1 ∈ D) :
    Tendsto (fun n : ℕ => ((B + n • D).ncard : ℝ) / (n : ℝ)^4)
      atTop (𝓝 (volume (latticeBody D)).toReal) := by
  let K := latticeBody D
  have hK : IsCompact K := (hD.image exponentVector).isCompact_convexHull ℝ
  have hKfin : volume K ≠ ∞ := hK.measure_lt_top.ne
  obtain ⟨c, hc⟩ := exists_padding hD hD0 hunit
  obtain ⟨R, _, hR⟩ := (hB.image exponentVector).isCompact.isBounded.exists_pos_norm_le
  have hupper : Tendsto (fun n : ℕ => (volume (Metric.cthickening ((1 + R) / n) K)).toReal)
      atTop (𝓝 (volume K).toReal) :=
    (ENNReal.continuousAt_toReal hKfin).tendsto.comp
      ((tendsto_measure_cthickening_of_isCompact hK).comp
        (tendsto_const_div_atTop_nhds_zero_nat (1 + R)))
  let scale (n : ℕ) : ℝ := ((n - c : ℕ) : ℝ) / n
  have hscale : Tendsto scale atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := hone.sub (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
    simp only [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (c + 1)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [scale, Nat.cast_sub (by omega : c ≤ n), sub_div, div_self hn']
  have hlower : Tendsto (fun n => (scale n)^4 * (volume K).toReal)
      atTop (𝓝 (volume K).toReal) := by
    simpa only [one_pow, one_mul] using (hscale.pow 4).mul tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (c + 1)] with n hn
    have hn' : 0 < n := by omega
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn'
    have hcover : scale n • K ⊆ gridUnion n (B + n • D) := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨a, ha, hcoord⟩ := hc (n - c) y hy
      rw [Nat.sub_add_cancel (by omega : c ≤ n)] at ha
      refine Set.mem_iUnion₂.mpr ⟨a, ?_, (mem_gridBox hn').mpr ?_⟩
      · simpa only [zero_add] using Set.add_mem_add hB0 ha
      · intro j
        have heq : (n : ℝ) * ((scale n • y) j) = ((n - c : ℕ) : ℝ) * y j := by
          change (n : ℝ) * ((((n - c : ℕ) : ℝ) / n) * y j) = _
          field_simp [hnR.ne']
        rw [heq]
        exact hcoord j
    have hvol : (volume (scale n • K)).toReal = (scale n)^4 * (volume K).toReal := by
      rw [Measure.addHaar_smul_of_nonneg volume (by positivity : 0 ≤ scale n),
        Module.finrank_pi, Fintype.card_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hbounded : Bornology.IsBounded (Metric.cthickening ((1 + R) / n) K) :=
      hK.isBounded.cthickening
    have hfinite : volume (gridUnion n (B + n • D)) ≠ ∞ :=
      measure_ne_top_of_subset
        (gridUnion_subset_cthickening hn' hD0 (fun b hb => hR _ ⟨b, hb, rfl⟩))
        hbounded.measure_lt_top.ne
    rw [← hvol, ← volume_gridUnion hn' (hB.add (finite_nsmul hD n))]
    exact ENNReal.toReal_mono hfinite (measure_mono hcover)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : 0 < n := by omega
    rw [← volume_gridUnion hn' (hB.add (finite_nsmul hD n))]
    have hbounded : Bornology.IsBounded (Metric.cthickening ((1 + R) / n) K) :=
      hK.isBounded.cthickening
    exact ENNReal.toReal_mono hbounded.measure_lt_top.ne (measure_mono
      (gridUnion_subset_cthickening hn' hD0 (fun b hb => hR _ ⟨b, hb, rfl⟩)))
end
end K1_13_5_4_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_3
open K1_13_5_4_2 K1_13_5_4_2_4
open scoped Pointwise
noncomputable section
theorem finite_sum (supports : Fin 4 → Set Exponent) (S : Finset (Fin 4))
    (h : ∀ i, (supports i).Finite) : (∑ i ∈ S, supports i).Finite := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i).add ih
theorem zero_mem_sum (supports : Fin 4 → Set Exponent) (S : Finset (Fin 4))
    (h : ∀ i, 0 ∈ supports i) : 0 ∈ ∑ i ∈ S, supports i := by
  simpa only [Finset.sum_const_zero] using
    Set.finsetSum_mem_finsetSum S supports (fun _ => 0) (fun i _ => h i)
theorem units_sum (supports : Fin 4 → Set Exponent) (S : Finset (Fin 4))
    (hzero : ∀ i, 0 ∈ supports i)
    (hunit : ∀ i, ∀ a ∈ supports i, ∀ j, 0 < a j → Finsupp.single j 1 ∈ supports i)
    (a : Exponent) (ha : a ∈ ∑ i ∈ S, supports i) (j : Fin 4) (hj : 0 < a j) :
    Finsupp.single j 1 ∈ ∑ i ∈ S, supports i := by
  classical
  induction S using Finset.induction_on generalizing a with
  | empty =>
    simp only [Finset.sum_empty, Set.mem_zero] at ha
    subst a
    simp at hj
  | insert i S hi ih =>
    rw [Finset.sum_insert hi] at ha ⊢
    obtain ⟨b, hb, d, hd, rfl⟩ := Set.mem_add.mp ha
    change 0 < b j + d j at hj
    by_cases hb' : 0 < b j
    · simpa only [add_zero] using Set.add_mem_add (hunit i b hb j hb') (zero_mem_sum supports S hzero)
    · simpa only [zero_add] using Set.add_mem_add (hzero i) (ih d hd (by omega))
theorem corner_sum (supports : Fin 4 → Set Exponent) (q n : ℕ) (S : Finset (Fin 4)) :
    (∑ i, corner q n S i • supports i) = (∑ i, q • supports i) + n • (∑ i ∈ S, supports i) := by
  classical
  simp only [corner, add_nsmul, Finset.sum_add_distrib]
  congr 1
  have h (i : Fin 4) : (if i ∈ S then n else 0) • supports i =
      if i ∈ S then n • supports i else 0 := by
    split_ifs <;> simp
  simp only [h, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_nsmul]
theorem proof : K1_13_5_4_2_4.c3 := by
  classical
  intro A hzero hdown q S
  let supports (i : Fin 4) : Set Exponent := A i
  let B := ∑ i : Fin 4, q • supports i
  let D := ∑ i ∈ S, supports i
  have hf (i : Fin 4) : (supports i).Finite := Finset.finite_toSet _
  have hz (i : Fin 4) : 0 ∈ supports i := hzero i
  have hunit (i : Fin 4) (a : Exponent) (ha : a ∈ supports i) (j : Fin 4) (hj : 0 < a j) :
      Finsupp.single j 1 ∈ supports i := by
    apply hdown i ha
    intro k
    by_cases h : j = k
    · subst k
      simpa using (Nat.succ_le_of_lt hj)
    · simp [h]
  have hB0 : 0 ∈ B := zero_mem_sum (fun i => q • supports i) Finset.univ
    (fun i => Set.zero_mem_nsmul (hz i))
  have hbodies : latticeBody D = ∑ i ∈ S, latticeBody (A i) := by
    simp only [D, supports, latticeBody, Set.image_finsetSum exponentVector, convexHull_sum]
  have hexponents (n : ℕ) : exponentCount A (corner q n S) = (B + n • D).ncard := by
    unfold exponentCount
    exact congrArg Set.ncard (corner_sum supports q n S)
  simp only [hexponents, ← hbodies]
  exact tendsto_diagonal (finite_sum _ _ (fun i => finite_nsmul (hf i) q))
    (finite_sum supports S hf) hB0 (zero_mem_sum supports S hz) (units_sum supports S hz hunit)
end
end K1_13_5_4_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2_3
open K1_13_5_4_2_2
open scoped nonZeroDivisors
theorem genericUnramified {k B : Type} [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] (x : B)
    (hx : Transcendental k (algebraMap B (FractionRing B) x))
    (hsep : Algebra.IsSeparable
      (IntermediateField.adjoin k ({algebraMap B (FractionRing B) x} : Set (FractionRing B)))
      (FractionRing B)) :
    letI : Algebra (Polynomial k) B := (Polynomial.aeval x).toRingHom.toAlgebra
    Algebra.IsUnramifiedAt (Polynomial k) (⊥ : Ideal B) := by
  let R := Polynomial k
  let L := FractionRing B
  let F := FractionRing R
  let u : L := algebraMap B L x
  let f : R →ₐ[k] L := Polynomial.aeval u
  have hf : Function.Injective f := transcendental_iff_injective.mp hx
  let g : F →ₐ[k] L := IsFractionRing.liftAlgHom hf
  have hg : g.fieldRange = IntermediateField.adjoin k ({u} : Set L) :=
    IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq hf
      (Algebra.adjoin_singleton_eq_range_aeval k u).symm
  let e : F ≃ₐ[k] g.fieldRange := AlgEquiv.ofInjectiveField g
  let : Algebra.IsSeparable g.fieldRange L := by rwa [hg]
  let : Algebra F L := g.toRingHom.toAlgebra
  let : Algebra.IsSeparable F L :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) (by
      ext y
      change g (e.symm y) = (y : L)
      exact congrArg Subtype.val (e.apply_symm_apply y))
  let : Algebra R L := f.toRingHom.toAlgebra
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun p => by
    change f p = g (algebraMap R F p)
    simp [g]
  let : Algebra.FormallyUnramified R F :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := F) R⁰
  let : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_isSeparable F L
  let : Algebra.FormallyUnramified R L := Algebra.FormallyUnramified.comp R F L
  let : Algebra R B := (Polynomial.aeval x).toRingHom.toAlgebra
  let : IsLocalization (⊥ : Ideal B).primeCompl L := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  let T := Localization.AtPrime (⊥ : Ideal B)
  let eB := IsLocalization.algEquiv (⊥ : Ideal B).primeCompl L T
  let eR : L ≃ₐ[R] T :=
    { eB.toRingEquiv with
      commutes' := fun p => by
        change eB (f p) = algebraMap R T p
        have hp : f p = algebraMap B L (algebraMap R B p) :=
          Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k B L) x p
        rw [hp, eB.commutes, IsScalarTower.algebraMap_apply R B T] }
  exact Algebra.FormallyUnramified.of_equiv eR
theorem radicalFiber {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.EssFiniteType R B] (b : B)
    [Algebra.FormallyUnramified R (Localization.Away b)]
    (p : Ideal R) [p.IsMaximal] {d : R} (hd : d ∉ p) (hb : b ∣ algebraMap R B d) :
    (p.map (algebraMap R B)).IsRadical := by
  let S := Localization.Away b
  let J := p.map (algebraMap R B)
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  have hd' : IsUnit (Ideal.Quotient.mk J (algebraMap R B d)) := by
    have hu : IsUnit (Ideal.Quotient.mk p d) :=
      isUnit_iff_ne_zero.mpr (fun h => hd ((Ideal.Quotient.eq_zero_iff_mem).mp h))
    exact hu.map (algebraMap (R ⧸ p) (B ⧸ J))
  have hunit : IsUnit (Ideal.Quotient.mk J b) :=
    isUnit_of_dvd_unit (map_dvd (Ideal.Quotient.mk J) hb) hd'
  let : Algebra.EssFiniteType B S := Algebra.EssFiniteType.of_isLocalization S (.powers b)
  let : Algebra.EssFiniteType R S := Algebra.EssFiniteType.comp R B S
  have hrad : (J.map (algebraMap B S)).IsRadical := by
    change ((p.map (algebraMap R B)).map (algebraMap B S)).IsRadical
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R B S]
    exact Algebra.FormallyUnramified.isRadical_map_isMaximal R S p
  intro z hz
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hz
  have hzn : algebraMap B S z ^ n ∈ J.map (algebraMap B S) := by
    rw [← map_pow]
    exact Ideal.mem_map_of_mem _ hn
  have hz' := hrad (Ideal.mem_radical_iff.mpr ⟨n, hzn⟩)
  obtain ⟨s, hs, hsz⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers b) S J z).mp hz'
  obtain ⟨m, rfl⟩ := hs
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow] at hsz
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((hunit.pow m).mul_right_eq_zero.mp hsz)
theorem proof : K1_13_5_4_2_2.c3 := by
  classical
  intro k σ _ _ _ I hI a hfin hsep
  let : I.IsPrime := hI
  let B := MvPolynomial σ k ⧸ I
  let x : B := Ideal.Quotient.mk I (linearForm a)
  let : Algebra (Polynomial k) B := (projection I a).toRingHom.toAlgebra
  let : Module.Finite (Polynomial k) B := hfin
  let : Algebra.IsUnramifiedAt (Polynomial k) (⊥ : Ideal B) :=
    genericUnramified x hsep.1 hsep.2
  obtain ⟨b, hb, hunram⟩ :=
    Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := Polynomial k) (⊥ : Ideal B)
  let : Algebra.FormallyUnramified (Polynomial k) (Localization.Away b) := hunram
  have hb₀ : b ≠ 0 := fun h => hb (by simp [h])
  obtain ⟨d, hd, hdiv⟩ := (IsIntegral.of_finite (R := Polynomial k) b).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hb₀)
  refine ⟨d.roots.toFinset, fun t ht => ?_⟩
  let p := RingHom.ker (Polynomial.evalRingHom t)
  have hp : p = Ideal.span {Polynomial.X - Polynomial.C t} := Polynomial.ker_evalRingHom t
  let : p.IsMaximal := RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom t)
    (fun c => ⟨Polynomial.C c, Polynomial.eval_C⟩)
  have hdp : d ∉ p := by
    intro h
    exact ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr (RingHom.mem_ker.mp h)))
  have hrad := radicalFiber b p hdp hdiv
  have hmap : p.map (algebraMap (Polynomial k) B) =
      (Ideal.span {linearForm a - MvPolynomial.C t}).map (Ideal.Quotient.mk I) := by
    have hgen : algebraMap (Polynomial k) B (Polynomial.X - Polynomial.C t) =
        Ideal.Quotient.mk I (linearForm a - MvPolynomial.C t) := by
      change (projection I a) (Polynomial.X - Polynomial.C t) = _
      simp only [K1_13_5_4_2_2.projection, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] <;> rfl
    rw [hp, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, hgen]
  rw [hmap] at hrad
  unfold fiberIdeal
  rw [← Ideal.comap_map_quotientMk I (Ideal.span {linearForm a - MvPolynomial.C t})]
  exact hrad.comap (Ideal.Quotient.mk I)
end K1_13_5_4_2_2_3
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_1_2
theorem proof : K1_13_7_5_3_1.c2 :=
  K1_13_7_5_3_1.reduced_of_shared K1_13_5_4_2_2_2.proof K1_13_5_4_2_2_3.proof
end K1_13_7_5_3_1_2
end
section
namespace K1_13_7_2_1
noncomputable section
open K1 K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_2 MvPolynomial UniqueFactorizationMonoid
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem genericCoeffs_flat : genericCoeffs.Flat := by
  exact (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat GenericField (nonZeroDivisors (Polynomial Geom)))).comp
    (RingHom.Flat.of_isField (Field.toIsField GenericField) (algebraMap GenericField GeoField))
theorem geometric_flat (n : ℕ) : (MvPolynomial.map (σ := Fin n) genericCoeffs).Flat := by
  let : Algebra (Polynomial Geom) GeoField := genericCoeffs.toAlgebra
  have hg : (algebraMap (Polynomial Geom) GeoField).Flat := genericCoeffs_flat
  exact RingHom.Flat.isStableUnderBaseChange (Polynomial Geom) GeoField (Row n)
    (MvPolynomial (Fin n) GeoField) hg
private theorem geometric_injective (n : ℕ) :
    Function.Injective (MvPolynomial.map (σ := Fin n) genericCoeffs) :=
  MvPolynomial.map_injective _ ((algebraMap GenericField GeoField).injective.comp
    (IsFractionRing.injective (Polynomial Geom) GenericField))
theorem comap_span_prime {n : ℕ} {r : MvPolynomial (Fin n) GeoField} (hr : Prime r)
    {x : Row n} (hx : x ≠ 0) (hxr : r ∣ MvPolynomial.map genericCoeffs x) :
    ∃ a : Row n, Prime a ∧
      (Ideal.span ({r} : Set (MvPolynomial (Fin n) GeoField))).comap
        (MvPolynomial.map genericCoeffs) = Ideal.span {a} := by
  let P : Ideal (MvPolynomial (Fin n) GeoField) := Ideal.span {r}
  have hP : P.IsPrime := (Ideal.span_singleton_prime hr.ne_zero).mpr hr
  let Q := P.comap (MvPolynomial.map (σ := Fin n) genericCoeffs)
  have hQ : Q.IsPrime := hP.comap _
  have hQn : Q ≠ ⊥ := fun h => hx (by
    have hm : x ∈ Q := Ideal.mem_span_singleton.mpr hxr
    simpa [h] using hm)
  have hPheight : P.height = 1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hr.ne_zero) hr.not_isUnit
  let : Algebra (Row n) (MvPolynomial (Fin n) GeoField) :=
    (MvPolynomial.map (σ := Fin n) genericCoeffs).toAlgebra
  let : Module.Flat (Row n) (MvPolynomial (Fin n) GeoField) := geometric_flat n
  let : P.LiesOver Q := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown Q P
  have hQle : Q.height ≤ 1 := by
    rw [← hPheight, h]
    exact le_self_add
  have hQheight : Q.height = 1 := by
    apply le_antisymm hQle
    rw [Order.one_le_iff_ne_zero]
    exact fun hzero => hQn (Ideal.height_eq_zero_iff_eq_bot.mp hzero)
  obtain ⟨a, haQ, ha⟩ := hQ.exists_mem_prime_of_ne_bot hQn
  exact ⟨a, ha, Ideal.eq_span_singleton_of_height_eq_one hQheight haQ ha⟩
private theorem liftLower_ne_zero {q : Row 3} (hq : q ≠ 0) : liftLower q ≠ 0 :=
  fun hz => hq (rename_injective _ (Fin.castSucc_injective 3) (by simpa [liftLower] using hz))
theorem clear_local_membership {J : Ideal (Row 4)} {surface : Ideal GeoJets}
    [surface.IsPrime] {P : Row 4}
    (hP : algebraMap GeoJets (Localization.AtPrime surface) (toGeneric P) ∈
      (J.map (MvPolynomial.map genericCoeffs)).map (algebraMap GeoJets (Localization.AtPrime surface))) :
    ∃ s : Row 4, toGeneric s ∉ surface ∧ s * P ∈ J := by
  let g : Row 4 →+* GeoJets := MvPolynomial.map genericCoeffs
  let Q := surface.comap g
  let : Q.IsPrime := (inferInstance : surface.IsPrime).comap g
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime surface
  let e : A →+* B := Localization.localRingHom Q surface g rfl
  let : Algebra A B := e.toAlgebra
  let : Module.Flat A B := (geometric_flat 4).localRingHom surface Q rfl
  let : IsLocalHom (algebraMap A B) := Localization.isLocalHom_localRingHom Q surface g rfl
  let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have he (x : Row 4) : e (algebraMap (Row 4) A x) = algebraMap GeoJets B (g x) :=
    Localization.localRingHom_to_map Q surface g rfl x
  have hJ : (J.map (algebraMap (Row 4) A)).map e = (J.map g).map (algebraMap GeoJets B) := by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (fun a => J.map a) (RingHom.ext he)
  have hx : algebraMap (Row 4) A P ∈ J.map (algebraMap (Row 4) A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J.map (algebraMap (Row 4) A))]
    change e (algebraMap (Row 4) A P) ∈ (J.map (algebraMap (Row 4) A)).map e
    rw [he, hJ]
    exact hP
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl A J P).mp hx
theorem lifted_height {f : Row 4} {q : Row 3} {surface : Ideal GeoJets}
    (hf : f ≠ 0) (hproper : IsRelPrime (toGeneric f) (toGeneric (liftLower q)))
    (h : LiftedSurface f q surface) : surface.height = 2 :=
  K1_13_6_1_2.pair_height (fun hz => hf (geometric_injective 4 (by simpa [toGeneric] using hz)))
    hproper h.minimal
end
end K1_13_7_2_1
end
section
namespace K1_13_7_2_1
noncomputable section
open K1 K1_13 K1_13_6 K1_13_7 K1_13_7_2 MvPolynomial
def c1 : Prop :=
  ∀ q : Row 3, Squarefree q → q.totalDegree < K1.p → Squarefree (genericRow q)
private theorem local_length_one {f : Row 4} {q : Row 3} {surface : Ideal GeoJets}
    (hp : surface.IsPrime) (h : LocalGenerators f q surface hp) :
    cycleLength (intersectionIdeal f (liftLower q)) surface hp = 1 := by
  let : surface.IsPrime := hp
  let A := Localization.AtPrime surface
  change (intersectionIdeal f (liftLower q)).map (algebraMap GeoJets A) =
    IsLocalRing.maximalIdeal A at h
  change Module.length A (A ⧸ (intersectionIdeal f (liftLower q)).map (algebraMap GeoJets A)) = 1
  rw [h, Module.length_eq_one_iff]
  exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
private theorem tangent_invariant {f : Row 4} {q : Row 3} {surface : Ideal GeoJets}
    (h : LiftedSurface f q surface) (hloc : LocalGenerators f q surface h.minimal.isPrime)
    (hqD : toGeneric (lowerFlow q) ∈ surface) : Invariant f surface := by
  let : surface.IsPrime := h.minimal.isPrime
  let A := Localization.AtPrime surface
  let g : Row 4 →+* GeoJets := MvPolynomial.map genericCoeffs
  let J : Ideal (Row 4) := Ideal.span {f, liftLower q}
  have hJ : J.map g = intersectionIdeal f (liftLower q) := by
    simp [J, Ideal.map_span, intersectionIdeal, toGeneric, g]
  have hf : g f ∈ surface := h.minimal.le (Ideal.subset_span (by simp [g, toGeneric]))
  have hq : g (liftLower q) ∈ surface := h.minimal.le (Ideal.subset_span (by simp [g, toGeneric]))
  have hqFlow : g (flowNumerator f (liftLower q)) ∈ surface := by
    simp only [flowNumerator, separant_liftLower, mul_zero, sub_zero]
    change g (separant f * lowerFlow q) ∈ surface
    rw [map_mul]
    exact surface.mul_mem_left _ hqD
  have hloc' : (J.map g).map (algebraMap GeoJets A) = IsLocalRing.maximalIdeal A :=
    (congrArg (fun I : Ideal GeoJets => I.map (algebraMap GeoJets A)) hJ).trans hloc
  intro P hP
  change g P ∈ surface at hP
  change g (flowNumerator f P) ∈ surface
  have hmem : algebraMap GeoJets A (g P) ∈ (J.map g).map (algebraMap GeoJets A) := by
    rw [hloc', IsLocalization.AtPrime.to_map_mem_maximal_iff A surface]
    exact hP
  obtain ⟨u, hu, huP⟩ := clear_local_membership hmem
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp huP
  have hd : g (flowNumerator f (u * P)) ∈ surface := by
    rw [← hab, flow_add, flow_mul, flow_mul, flow_self, mul_zero, zero_add]
    simp only [map_add, map_mul]
    exact surface.add_mem (surface.mul_mem_right _ hf) <|
      surface.add_mem (surface.mul_mem_left _ hqFlow) (surface.mul_mem_right _ hq)
  rw [flow_mul, map_add, map_mul, map_mul] at hd
  have hterm : g P * g (flowNumerator f u) ∈ surface := surface.mul_mem_right _ hP
  have hprod : g u * g (flowNumerator f P) ∈ surface := (surface.add_mem_iff_left hterm).mp hd
  exact (h.minimal.isPrime.mem_or_mem hprod).resolve_left hu
end
end K1_13_7_2_1
end
section
namespace K1_13_7_2_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_7 K1_13_7_2
open scoped Polynomial
private def top {R : Type*} [CommRing R] :
    MvPolynomial (Fin 4) R ≃ₐ[R] (MvPolynomial (Fin 3) R)[X] :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans (MvPolynomial.optionEquivLeft R (Fin 3))
@[simp] private theorem top_C {R : Type*} [CommRing R] (a : R) :
    top (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simp [top, MvPolynomial.optionEquivLeft_C]
@[simp] private theorem top_X_last {R : Type*} [CommRing R] :
    top (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) R) = Polynomial.X := by
  have h : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  simp [top, h, MvPolynomial.optionEquivLeft_X_none]
@[simp] private theorem top_X_lower {R : Type*} [CommRing R] (i : Fin 3) :
    top (MvPolynomial.X i.castSucc : MvPolynomial (Fin 4) R) =
      Polynomial.C (MvPolynomial.X i) := by
  simp [top, MvPolynomial.optionEquivLeft_X_some]
private theorem top_rename_lower {R : Type*} [CommRing R] (q : MvPolynomial (Fin 3) R) :
    top (MvPolynomial.rename Fin.castSucc q) = Polynomial.C q := by
  have h : (top (R := R)).toRingHom.comp (MvPolynomial.rename Fin.castSucc).toRingHom =
      Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  exact DFunLike.congr_fun h q
private theorem top_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPolynomial (Fin 4) R) :
    top (MvPolynomial.map φ f) = (top f).map (MvPolynomial.map φ) := by
  have h : (top (R := S)).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom (MvPolynomial.map φ)).comp (top (R := R)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp
  exact DFunLike.congr_fun h f
private theorem top_derivative {R : Type*} [CommRing R] (f : MvPolynomial (Fin 4) R) :
    top (MvPolynomial.pderiv 3 f) = (top f).derivative := by
  have hX (i : Fin 4) :
      top (MvPolynomial.pderiv 3 (MvPolynomial.X i : MvPolynomial (Fin 4) R)) =
        (top (MvPolynomial.X i : MvPolynomial (Fin 4) R)).derivative := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · have hne : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
      simp only [MvPolynomial.pderiv_X_of_ne hne, map_zero, top_X_lower, Polynomial.derivative_C]
  refine MvPolynomial.induction_on
    (motive := fun p => top (MvPolynomial.pderiv 3 p) = (top p).derivative)
    f ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro p i hp
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hp, hX, Polynomial.derivative_mul]
end
end K1_13_7_2_1_2
end
section
namespace K1_13_7_2_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_7 MvPolynomial
private theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp
    (IsFractionRing.injective (Polynomial Geom) GenericField)
theorem exists_partial_not_dvd {a : Row 3} (ha : a ≠ 0)
    (hvars : a.vars.Nonempty) (hsmall : a.totalDegree < K1.p) :
    ∃ i : Fin 3, ¬ a ∣ pderiv i a := by
  obtain ⟨i, hi⟩ := hvars
  have hpos := Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hi)
  have hlt := (degreeOf_le_totalDegree a i).trans_lt hsmall
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  let _ : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hcast : (a.degreeOf i : Polynomial Geom) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hlt)
      (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff (Polynomial Geom) K1.p _).mp hz))
  have hnonzero := pderiv_ne_zero_of_natCast_ne_zero i a hcast
  have hdeg := degreeOf_pderiv_le_sub_one i a
  refine ⟨i, ?_⟩
  rintro ⟨b, hb⟩
  have hb0 : b ≠ 0 := fun hz => hnonzero (by rw [hb, hz, mul_zero])
  rw [hb, degreeOf_mul_eq ha hb0] at hdeg
  omega
theorem proof : K1_13_7_2_1.c1 := by
  intro q hsq hsmall
  change Squarefree (MvPolynomial.map genericCoeffs q)
  have hq : q ≠ 0 := hsq.ne_zero
  have hgq : MvPolynomial.map genericCoeffs q ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective _ genericCoeffs_injective)).mpr hq
  apply (squarefree_iff_no_irreducibles hgq).mpr
  intro r hir hrr
  have hr := UniqueFactorizationMonoid.irreducible_iff_prime.mp hir
  have hrq : r ∣ MvPolynomial.map genericCoeffs q := (dvd_mul_right r r).trans hrr
  obtain ⟨a, ha, hcomap⟩ := K1_13_7_2_1.comap_span_prime hr hq hrq
  have hdvd (x : Row 3) : a ∣ x ↔ r ∣ MvPolynomial.map genericCoeffs x := by
    rw [← Ideal.mem_span_singleton, ← hcomap, Ideal.mem_comap, Ideal.mem_span_singleton]
  have haq := (hdvd q).mpr hrq
  have hva : a.vars.Nonempty := by
    by_contra! he
    have heq := vars_eq_empty_iff_eq_C.mp he
    have hc : a.coeff 0 ≠ 0 := fun hz => ha.ne_zero (by rw [heq, hz, map_zero])
    have hcnz : genericCoeffs (a.coeff 0) ≠ 0 := fun hz =>
      hc (genericCoeffs_injective (hz.trans genericCoeffs.map_zero.symm))
    have hu : IsUnit (MvPolynomial.map genericCoeffs a) := by
      rw [heq, MvPolynomial.map_C]
      exact (isUnit_iff_ne_zero.mpr hcnz).map C
    exact hr.not_isUnit (isUnit_of_dvd_unit ((hdvd a).mp dvd_rfl) hu)
  obtain ⟨i, hi⟩ := exists_partial_not_dvd ha.ne_zero hva
    ((totalDegree_le_of_dvd_of_isDomain haq hq).trans_lt hsmall)
  have hrderiv : r ∣ MvPolynomial.map genericCoeffs (pderiv i q) := by
    obtain ⟨w, hw⟩ := hrr
    rw [← pderiv_map, hw, mul_assoc, pderiv_mul]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_right r w) _) (dvd_mul_right r _)
  have haderiv := (hdvd (pderiv i q)).mpr hrderiv
  obtain ⟨b, hb⟩ := haq
  have hab : ¬ a ∣ b := by
    rintro ⟨c, hc⟩
    exact ha.not_isUnit (hsq a ⟨c, by rw [hb, hc, mul_assoc]⟩)
  rw [hb, pderiv_mul] at haderiv
  exact hi ((ha.dvd_or_dvd ((dvd_add_left (dvd_mul_right a _)).mp haderiv)).resolve_right hab)
end
end K1_13_7_2_1_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_3
noncomputable section
open K1 K1_11 MvPolynomial
section Field
variable {F : Type*} [Field F]
def swapXY : Fin 4 ≃ Fin 4 := Equiv.swap 0 1
def yView : MvPolynomial (Fin 4) F ≃ₐ[F]
    Polynomial (MvPolynomial (Fin 3) F) :=
  (renameEquiv F swapXY).trans (MvPolynomial.finSuccEquiv F 3)
theorem yView_X (i : Fin 4) :
    yView (MvPolynomial.X i : MvPolynomial (Fin 4) F) =
      ![Polynomial.C (MvPolynomial.X 0), Polynomial.X, Polynomial.C (MvPolynomial.X 1), Polynomial.C (MvPolynomial.X 2)] i := by
  change MvPolynomial.finSuccEquiv F 3 (rename swapXY (MvPolynomial.X i)) = _
  rw [rename_X]
  fin_cases i
  · change (MvPolynomial.finSuccEquiv F 3) (MvPolynomial.X (0 : Fin 3).succ) = _
    exact finSuccEquiv_X_succ
  · change (MvPolynomial.finSuccEquiv F 3) (MvPolynomial.X 0) = _
    exact finSuccEquiv_X_zero
  · change (MvPolynomial.finSuccEquiv F 3) (MvPolynomial.X (1 : Fin 3).succ) = _
    exact finSuccEquiv_X_succ
  · change (MvPolynomial.finSuccEquiv F 3) (MvPolynomial.X (2 : Fin 3).succ) = _
    exact finSuccEquiv_X_succ
private def seedValues (s t : F) : Fin 3 → Polynomial F :=
  ![Polynomial.X, Polynomial.C s, Polynomial.C t]
private def specializeY (G : MvPolynomial (Fin 4) F) (s t : F) :
    Polynomial (Polynomial F) :=
  (yView G).map (aeval (seedValues s t)).toRingHom
private theorem specializeY_eval (G : MvPolynomial (Fin 4) F) (D : Polynomial F) (s t : F) :
    (specializeY G s t).eval D = aeval (scalarImages D s t) G := by
  let ev : MvPolynomial (Fin 3) F →+* Polynomial F := (aeval (seedValues s t)).toRingHom
  have h : (Polynomial.evalRingHom D).comp ((Polynomial.mapRingHom ev).comp yView.toRingHom) =
      (aeval (scalarImages D s t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ev, yView, finSuccEquiv_apply]
    · intro i
      change (specializeY (MvPolynomial.X i) s t).eval D = _
      unfold specializeY
      rw [yView_X]
      fin_cases i <;> simp [seedValues, scalarImages]
  exact RingHom.congr_fun h G
private theorem specializeY_derivative (G : MvPolynomial (Fin 4) F) (s t : F) :
    specializeY (pderiv 1 G) s t = Polynomial.derivative (specializeY G s t) := by
  let f : MvPolynomial (Fin 4) F →+* Polynomial (Polynomial F) :=
    (Polynomial.mapRingHom (aeval (seedValues s t)).toRingHom).comp yView.toRingHom
  change f (pderiv 1 G) = Polynomial.derivative (f G)
  have hC (a : F) : f (C a) = Polynomial.C (Polynomial.C a) := by
    simp [f, yView, finSuccEquiv_apply]
  have hX (i : Fin 4) : f (MvPolynomial.X i) = ![Polynomial.C Polynomial.X, Polynomial.X,
      Polynomial.C (Polynomial.C s), Polynomial.C (Polynomial.C t)] i := by
    change (yView (MvPolynomial.X i)).map _ = _
    rw [yView_X]
    fin_cases i <;> simp [seedValues]
  induction G using MvPolynomial.induction_on with
  | C a => simp [hC]
  | add a b ha hb => simp [ha, hb]
  | mul_X a i ha =>
      simp only [pderiv_mul, map_add, map_mul, Polynomial.derivative_mul, ha, hX]
      fin_cases i <;> simp
private theorem specializeY_iterate (G : MvPolynomial (Fin 4) F) (s t : F) (j : ℕ) :
    specializeY (derivativeChart G j) s t =
      (fun H : Polynomial (Polynomial F) => Polynomial.derivative H)^[j] (specializeY G s t) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      unfold derivativeChart at *
      simp only [Function.iterate_succ_apply', specializeY_derivative, ih]
private theorem yView_degree (G : MvPolynomial (Fin 4) F) :
    (yView G).natDegree = G.weightedTotalDegree scalarWeightY := by
  change (MvPolynomial.finSuccEquiv F 3 (rename swapXY G)).natDegree = _
  rw [natDegree_finSuccEquiv, show (0 : Fin 4) = swapXY 1 by decide,
    degreeOf_rename_of_injective swapXY.injective, ← weightedTotalDegree_piSingle]
  congr 1
  funext i
  fin_cases i <;> decide
theorem coefficient_support (G : MvPolynomial (Fin 4) F) (i j : ℕ)
    (e : Fin 2 →₀ ℕ) (he : e ∈
      ((MvPolynomial.finSuccEquiv F 2 ((yView G).coeff j)).coeff i).support) :
    ∃ m ∈ G.support, m 2 = e 0 ∧ m 3 = e 1 := by
  rw [mem_support_coeff_finSuccEquiv] at he
  change e.cons i ∈ ((MvPolynomial.finSuccEquiv F 3 (rename swapXY G)).coeff j).support at he
  rw [mem_support_coeff_finSuccEquiv] at he
  obtain ⟨m, hm, hcoeff⟩ := coeff_rename_ne_zero swapXY G ((e.cons i).cons j)
    (mem_support_iff.mp he)
  refine ⟨m, mem_support_iff.mpr hcoeff, ?_, ?_⟩
  · have h := congrArg (fun z : Fin 4 →₀ ℕ => z (swapXY 2)) hm
    simp only [Finsupp.mapDomain_apply_of_injective swapXY.injective] at h
    rw [show swapXY 2 = (0 : Fin 2).succ.succ by decide] at h
    simpa only [Finsupp.cons_succ] using h
  · have h := congrArg (fun z : Fin 4 →₀ ℕ => z (swapXY 3)) hm
    simp only [Finsupp.mapDomain_apply_of_injective swapXY.injective] at h
    rw [show swapXY 3 = (1 : Fin 2).succ.succ by decide] at h
    simpa only [Finsupp.cons_succ] using h
theorem seedValues_map (H : MvPolynomial (Fin 3) F) (s t : F) :
    aeval (seedValues s t) H =
      (MvPolynomial.finSuccEquiv F 2 H).map (MvPolynomial.eval ![s,t]) := by
  change (aeval (seedValues s t)).toRingHom H =
    ((Polynomial.mapRingHom (MvPolynomial.eval ![s,t])).comp (MvPolynomial.finSuccEquiv F 2).toRingHom) H
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [seedValues, finSuccEquiv_X_zero]
    · change aeval (seedValues s t) (MvPolynomial.X j.succ) =
        ((MvPolynomial.finSuccEquiv F 2) (MvPolynomial.X j.succ)).map _
      rw [finSuccEquiv_X_succ]
      fin_cases j <;> simp [seedValues]
private theorem exceptions (G : MvPolynomial (Fin 4) F) (hG : G ≠ 0)
    (q a b : ℕ) (hq : 0 < q) (ha : a < q)
    (hS : G.weightedTotalDegree scalarWeightYS ≤ a)
    (hT : G.weightedTotalDegree scalarWeightT ≤ b) (Γ : Finset F) :
    ∃ exceptional : Finset F, exceptional.card ≤ a + q * b ∧
      ∀ γ ∈ Γ, γ ∉ exceptional → specializeY G γ (γ ^ q) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr
    (show yView G ≠ 0 from fun hz => hG (yView.injective (hz.trans (map_zero yView).symm)))
  have hn : MvPolynomial.finSuccEquiv F 2 ((yView G).coeff j) ≠ 0 := by
    intro hz
    apply Polynomial.mem_support_iff.mp hj
    exact (MvPolynomial.finSuccEquiv F 2).injective
      (hz.trans (map_zero (MvPolynomial.finSuccEquiv F 2)).symm)
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hn
  let c := (MvPolynomial.finSuccEquiv F 2 ((yView G).coeff j)).coeff i
  have hc : c ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hmono (e : Fin 2 →₀ ℕ) (he : e ∈ c.support) : e 0 ≤ a ∧ e 1 ≤ b := by
    obtain ⟨m, hm, h0, h1⟩ := coefficient_support G i j e he
    have hs := (Finset.le_sup (f := fun m => m.weight scalarWeightYS) hm).trans hS
    have ht := (Finset.le_sup (f := fun m => m.weight scalarWeightT) hm).trans hT
    simp [scalarWeightYS, scalarWeightT, Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_succ, smul_eq_mul] at hs ht
    omega
  have hca : c.degreeOf 0 ≤ a := by
    rw [degreeOf_eq_sup]
    exact Finset.sup_le fun e he => (hmono e he).1
  have hcb : c.degreeOf 1 ≤ b := by
    rw [degreeOf_eq_sup]
    exact Finset.sup_le fun e he => (hmono e he).2
  let E := Γ.filter fun γ => MvPolynomial.eval ![γ, γ ^ q] c = 0
  refine ⟨E, K1_10.frobenius_coefficient_exception_count q a b hq c hc hca ha hcb E
    (fun γ hγ => (Finset.mem_filter.mp hγ).2), ?_⟩
  intro γ hγ houtside hz
  apply houtside
  apply Finset.mem_filter.mpr
  refine ⟨hγ, ?_⟩
  have he := congrArg (fun R : Polynomial (Polynomial F) => (R.coeff j).coeff i) hz
  simpa [specializeY, seedValues_map, c] using he
end Field
end
end K1_11_3
end
section
set_option maxHeartbeats 350000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_4_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
open IsLocalRing
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev SeedChart := MvPolynomial (Fin 2) Seeds
private abbrev seedVariables : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  finSumFinEquiv.symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
private def seedChart : Ambient ≃+* SeedChart :=
  ((MvPolynomial.renameEquiv FX seedVariables).trans
    (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2))).toRingEquiv
private theorem seedMap :
    mapGenericSeed = (algebraMap SeedChart FibreRing).comp seedChart.toRingHom := by
  have hChart :
      (algebraMap SeedChart FibreRing).comp seedChart.toRingHom =
        MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
          (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (generic i)) ∘ seedVariables) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [seedChart]
      rfl
    · intro i
      rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Function.comp_apply]
      change algebraMap SeedChart FibreRing
        (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2)
          (MvPolynomial.renameEquiv FX seedVariables (MvPolynomial.X i))) = _
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, MvPolynomial.algebraMap_def]
      cases seedVariables i <;> simp [generic]
  rw [hChart]
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [mapGenericSeed, MvPolynomial.eval₂Hom_C]
  · intro i
    simp only [mapGenericSeed, MvPolynomial.eval₂Hom_X', Function.comp_apply]
    fin_cases i <;> rfl
theorem height_bivariate_maximal {F : Type*} [Field F]
    (J : Ideal (MvPolynomial (Fin 2) F)) [J.IsMaximal] : J.height = 2 := by
  let e := (MvPolynomial.finSuccEquiv F 1).toRingEquiv
  let P := J.map e.toRingHom
  let A := MvPolynomial (Fin 1) F
  have hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
  let q := P.comap (Polynomial.C : A →+* Polynomial A)
  have hq : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
  have hdim : q.height = 1 := by
    let e₁ := (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv
    let q' := q.map e₁.toRingHom
    have hq' : q'.IsMaximal := Ideal.map_isMaximal_of_equiv e₁
    exact (e₁.height_map q).symm.trans
      (IsPrincipalIdealRing.height_eq_one_of_isMaximal q' (Polynomial.not_isField F))
  have hqP : P.LiesOver q := ⟨rfl⟩
  calc
    J.height = P.height := (e.height_map J).symm
    _ = q.height + 1 := Polynomial.height_eq_height_add_one q P
    _ = 2 := by rw [hdim, one_add_one_eq_two]
theorem localized_height {A F : Type*} [CommRing A] [Field F]
    [Algebra A (MvPolynomial (Fin 2) F)] (S : Submonoid A)
    [IsLocalization S (MvPolynomial (Fin 2) F)]
    (P : Ideal A) [P.IsPrime]
    (hproper : P.map (algebraMap A (MvPolynomial (Fin 2) F)) ≠ ⊤)
    (hfin : Module.Finite F
      (MvPolynomial (Fin 2) F ⧸ P.map (algebraMap A (MvPolynomial (Fin 2) F)))) :
    P.height = 2 := by
  let B := MvPolynomial (Fin 2) F
  let Q := P.map (algebraMap A B)
  have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint S B P).mp hproper
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint S B P inferInstance hd
  let : Field (B ⧸ Q) := fieldOfFiniteDimensional F _
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField Q (Field.toIsField _)
  exact (IsLocalization.height_map_of_disjoint S P hd).symm.trans (height_bivariate_maximal Q)
theorem active_height {I : Ideal Ambient} (hI : Active I) : I.height = 2 := by
  let S : Submonoid SeedChart := (nonZeroDivisors Seeds).map MvPolynomial.C
  let P := I.map seedChart.toRingHom
  let J := I.map mapGenericSeed
  have hJ : J = P.map (algebraMap SeedChart FibreRing) := by
    rw [Ideal.map_map, ← seedMap]
  have hP : P.IsPrime := by
    change (I.map (seedChart : Ambient →+* SeedChart)).IsPrime
    rw [Ideal.map_comap_of_equiv seedChart]
    exact hI.prime.comap _
  have hproper : J ≠ ⊤ := by
    intro ht
    let : Subsingleton (FibreRing ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr ht
    exact hI.seed_size.1.ne' (Module.finrank_eq_zero_of_subsingleton SeedField (FibreRing ⧸ J))
  have hfin : Module.Finite SeedField (FibreRing ⧸ J) := hI.seed_finite
  have hproperP : P.map (algebraMap SeedChart FibreRing) ≠ ⊤ := by
    rw [← hJ]
    exact hproper
  have hfinP : Module.Finite SeedField (FibreRing ⧸ P.map (algebraMap SeedChart FibreRing)) := by
    rw [← hJ]
    exact hfin
  have hlocal : IsLocalization S FibreRing :=
    MvPolynomial.isLocalization (nonZeroDivisors Seeds) SeedField
  have hPheight : P.height = 2 := by
    exact localized_height (A := SeedChart) (F := SeedField) S P hproperP hfinP
  rw [← RingEquiv.height_map seedChart I]
  exact hPheight
theorem local_mem_of_order {I : Ideal Ambient} [I.IsPrime]
    {J : Ideal Ambient} {f : Ambient} {n : ℕ}
    (h : ∃ a : Ambient, a ∉ I ∧ a * f ∈ I ^ n ⊔ J) :
    algebraMap Ambient (Localization.AtPrime I) f ∈
      (maximalIdeal (Localization.AtPrime I)) ^ n ⊔
        J.map (algebraMap Ambient (Localization.AtPrime I)) := by
  let R := Localization.AtPrime I
  let φ := algebraMap Ambient R
  obtain ⟨a, ha, haf⟩ := h
  have hb := Ideal.mem_map_of_mem φ haf
  rw [Ideal.map_sup, Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, map_mul] at hb
  let B := (maximalIdeal R) ^ n ⊔ J.map φ
  have hu : IsUnit (φ a) := (IsLocalization.AtPrime.isUnit_to_map_iff R I a).mpr ha
  obtain ⟨u, hu⟩ := hu
  change φ a * φ f ∈ B at hb
  rw [← hu] at hb
  simpa [← mul_assoc] using B.mul_mem_left (↑u⁻¹ : R) hb
end
end K1_14_2_2_4_4
end
section
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_4_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4
open IsLocalRing
theorem proof : K1_14_2_2_4.c4 := by
  classical
  intro P Q I hI n hn hP hQ
  let : I.IsPrime := hI.prime
  let R := Localization.AtPrime I
  let : CommRing R := inferInstanceAs (CommRing (Localization.AtPrime I))
  let φ := algebraMap Ambient R
  have hdim : ringKrullDim R = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height I R, active_height hI]
    rfl
  change (↑(if dual I then n ^ 2 else n : ℕ) : ℕ∞) ≤
    Module.length R (R ⧸ ((Ideal.span {toJet P, toJet Q}).map φ : Submodule R R))
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  by_cases hD : dual I
  · rw [ite_eq_left hD]
    rw [orderOn, ite_eq_left hD] at hP hQ
    have hp := local_mem_of_order hP
    have hq := local_mem_of_order hQ
    have hbase : IsRegularRing FX := inferInstance
    have hambient : IsRegularRing Ambient := MvPolynomial.isRegularRing_of_isRegularRing FX
    have hregular : IsRegularLocalRing R :=
      IsRegularRing.isRegularLocalRing_localization (R := Ambient) I
    have hfactor : UniqueFactorizationMonoid Ambient :=
      MvPolynomial.uniqueFactorizationMonoid (Fin 4)
    have hlocalFactor : UniqueFactorizationMonoid R :=
      UniqueFactorizationMonoid.of_isLocalization I.primeCompl R
    have hdomain : IsDomain R := inferInstanceAs (IsDomain (Localization.AtPrime I))
    exact square_length_of_hilbert (maximalIdeal R) (regular_surface_hilbert (R := R) hdim)
      hn (by simpa only [Ideal.map_bot, sup_bot_eq] using hp)
      (by simpa only [Ideal.map_bot, sup_bot_eq] using hq)
  · rw [ite_eq_right hD]
    rw [orderOn, ite_eq_right hD] at hP hQ
    obtain ⟨G, _, hG⟩ := K1_14_2_2_5.jet_image_principal hI hD
    have hGI : jetPlaneIncl G ∈ I := by
      change G ∈ I.comap jetPlaneIncl
      rw [hG]
      exact Ideal.mem_span_singleton_self G
    have hX : φ (jetPlaneIncl G) ∈ maximalIdeal R :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff R I _).mpr hGI
    have hM : 1 < (maximalIdeal R).height := by
      have h := maximalIdeal_height_eq_ringKrullDim (R := R)
      rw [hdim] at h
      have he : (maximalIdeal R).height = 2 := WithBot.coe_injective h
      rw [he]
      decide
    have hp := local_mem_of_order hP
    have hq := local_mem_of_order hQ
    simp only [hG, Ideal.map_span, Set.image_singleton] at hp hq
    exact linear_length hX hM hp hq
end
end K1_14_2_2_4_4
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_2
noncomputable section
open MvPolynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
private theorem affine_image (Q : MvPolynomial (Fin 5) F)
    (j : Fin 5) (hj : j = 3 ∨ j = 4) (x : E) (v : Fin 5 → Polynomial E)
    (hv : v 0 = Polynomial.C x) (hl : Q.degreeOf j ≤ 1)
    (hzero : ∀ i : Fin 5, i ≠ 0 → i ≠ j → Q.degreeOf i = 0) :
    ∃ a b : E, aeval v Q = Polynomial.C a + Polynomial.C b * v j := by
  classical
  let c (e : Fin 5 →₀ ℕ) := algebraMap F E (Q.coeff e) * x ^ e 0
  let a (e : Fin 5 →₀ ℕ) := if e j = 0 then c e else 0
  let b (e : Fin 5 →₀ ℕ) := if e j = 0 then 0 else c e
  refine ⟨∑ e ∈ Q.support, a e, ∑ e ∈ Q.support, b e, ?_⟩
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hdz (i : Fin 5) (hi : i ≠ 0) (hij : i ≠ j) : e i = 0 :=
    Nat.eq_zero_of_le_zero ((le_degreeOf_of_mem_support i he).trans (hzero i hi hij).le)
  have hmono :
      aeval v (monomial e (Q.coeff e)) = Polynomial.C (c e) * v j ^ e j := by
    rw [aeval_monomial]
    rcases hj with rfl | rfl
    · simp [Finsupp.prod_fintype, Fin.prod_univ_succ, hv, c,
        hdz 1 (by decide) (by decide), hdz 2 (by decide) (by decide),
        hdz 4 (by decide) (by decide), Polynomial.algebraMap_apply, mul_assoc]
    · simp [Finsupp.prod_fintype, Fin.prod_univ_succ, hv, c,
        hdz 1 (by decide) (by decide), hdz 2 (by decide) (by decide),
        hdz 3 (by decide) (by decide), Polynomial.algebraMap_apply, mul_assoc]
  rw [hmono]
  have he' := (le_degreeOf_of_mem_support j he).trans hl
  by_cases h : e j = 0
  · simp [a, b, h]
  · have he1 : e j = 1 := by omega
    simp [a, b, he1]
private def transpose (f : Polynomial F →+* E) :
    Polynomial (Polynomial F) →+* Polynomial E :=
  (Polynomial.mapRingHom f).comp (Polynomial.Bivariate.swap (R:=F)).toRingHom
theorem transpose_graph (f : Polynomial F →ₐ[F] E) (q : ℕ)
    (Q : MvPolynomial (Fin 5) F) :
    transpose f.toRingHom (graph q Q) =
      aeval ![Polynomial.C (f Polynomial.X), 0, 0,
        Polynomial.X, (Polynomial.X (R:=E)) ^ q] Q := by
  have h : (transpose f.toRingHom).comp (graph (F:=F) q).toRingHom =
      (aeval ![Polynomial.C (f Polynomial.X), 0, 0,
        Polynomial.X, (Polynomial.X (R:=E)) ^ q]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [transpose, graph, Polynomial.algebraMap_apply, Polynomial.Bivariate.swap_C_C]
      exact f.commutes r
    · intro i
      fin_cases i <;> simp [transpose, graph, Polynomial.Bivariate.swap_X,
        Polynomial.Bivariate.swap_Y]
  exact RingHom.congr_fun h Q
private def columns (z U V : Polynomial E) : Fin 4 → Polynomial E :=
  ![U, Polynomial.X * U, V, z * V]
theorem dependent_of_affine (z U V g : Polynomial E)
    (a b c d : E) (hU : U ≠ 0) (hg : g ≠ 0)
    (hA : g * U = Polynomial.C a + Polynomial.C b * z)
    (hB : g * V = Polynomial.C c + Polynomial.C d * Polynomial.X) :
    ¬ LinearIndependent E (columns z U V) := by
  intro hi
  have hrel : (Polynomial.C c + Polynomial.C d * Polynomial.X) * U =
      (Polynomial.C a + Polynomial.C b * z) * V := by
    rw [← hB, ← hA]
    ring
  have hcomb : ∑ i : Fin 4, (![c, d, -a, -b] : Fin 4 → E) i • columns z U V i = 0 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, columns,
      Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, Polynomial.smul_eq_C_mul, map_neg]
    linear_combination hrel
  have hz := Fintype.linearIndependent_iff.mp hi _ hcomb
  have ha : a = 0 := by simpa using hz 2
  have hb : b = 0 := by simpa using hz 3
  exact mul_ne_zero hg hU (by simpa [ha, hb] using hA)
private theorem no_pair_one_one_of_graph (q : ℕ) (f : Polynomial F →ₐ[F] E)
    (hf : Function.Injective f) (g : Polynomial F)
    (U V : MvPolynomial (Fin 5) F) (U' V' : Polynomial (Polynomial F))
    (hg : g ≠ 0) (hu : U' ≠ 0) (hU : OmitsMessages U) (hV : OmitsMessages V)
    (hGU : graph q U = Polynomial.C g * U') (hGV : graph q V = Polynomial.C g * V')
    (hr : Module.finrank E (Submodule.span E (Set.range
      (columns (Polynomial.X ^ q) (transpose f.toRingHom U') (transpose f.toRingHom V')))) = 4)
    (hs : sWeight U V = 1) (ht : tWeight U V = 1) : False := by
  let ψ := transpose f.toRingHom
  let v : Fin 5 → Polynomial E :=
    ![Polynomial.C (f Polynomial.X), 0, 0, Polynomial.X, Polynomial.X ^ q]
  have htrans (Q : MvPolynomial (Fin 5) F) : ψ (graph q Q) = aeval v Q :=
    transpose_graph f q Q
  have hU3 : U.degreeOf 3 = 0 := by unfold sWeight at hs; omega
  have hV4 : V.degreeOf 4 = 0 := by unfold tWeight at ht; omega
  obtain ⟨hU1, hU2⟩ := hU
  obtain ⟨hV1, hV2⟩ := hV
  have haxisU : ∀ i : Fin 5, i ≠ 0 → i ≠ 4 → U.degreeOf i = 0 := by
    intro i hi hj
    fin_cases i <;> simp_all
  have haxisV : ∀ i : Fin 5, i ≠ 0 → i ≠ 3 → V.degreeOf i = 0 := by
    intro i hi hj
    fin_cases i <;> simp_all
  have hU4 : U.degreeOf 4 ≤ 1 := by
    unfold tWeight at ht
    omega
  have hV3 : V.degreeOf 3 ≤ 1 := by
    unfold sWeight at hs
    omega
  obtain ⟨a, b, hab⟩ := affine_image U 4 (Or.inr rfl) _ v rfl hU4 haxisU
  obtain ⟨c, d, hcd⟩ := affine_image V 3 (Or.inl rfl) _ v rfl hV3 haxisV
  have hv4 : v 4 = (Polynomial.X (R:=E)) ^ q := rfl
  have hv3 : v 3 = (Polynomial.X (R:=E)) := rfl
  rw [← htrans, hGU, map_mul, hv4] at hab
  rw [← htrans, hGV, map_mul, hv3] at hcd
  have hψ : Function.Injective ψ :=
    (Polynomial.map_injective f.toRingHom hf).comp (Polynomial.Bivariate.swap (R:=F)).injective
  have hu' : ψ U' ≠ 0 := by
    intro h
    exact hu (hψ (h.trans (map_zero ψ).symm))
  have hg' : ψ (Polynomial.C g) ≠ 0 := by
    intro h
    exact hg (Polynomial.C_eq_zero.mp (hψ (h.trans (map_zero ψ).symm)))
  have hi : LinearIndependent E (columns (Polynomial.X ^ q) (ψ U') (ψ V')) :=
    linearIndependent_iff_card_eq_finrank_span.mpr
      (by simpa only [Set.finrank, Fintype.card_fin] using hr.symm)
  exact dependent_of_affine (Polynomial.X ^ q) (ψ U') (ψ V') (ψ (Polynomial.C g))
    a b c d hu' hg' hab hcd hi
open K1 K1_11
private theorem native_column_rank (q : ℕ) (U V : Bivar) :
    K1_8.columnRankAt q U V =
      Module.finrank Frac (Submodule.span Frac (Set.range (columns (Polynomial.X ^ q)
        (extendSeed (Polynomial.Bivariate.swap U)) (extendSeed (Polynomial.Bivariate.swap V))))) := by
  have hcols : (fun j : Fin 4 => extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V
        else seed ^ q * V))) = columns (Polynomial.X ^ q)
          (extendSeed (Polynomial.Bivariate.swap U)) (extendSeed (Polynomial.Bivariate.swap V)) := by
    funext j
    fin_cases j <;> simp [columns, extendSeed, seed, Polynomial.Bivariate.swap_X]
  unfold K1_8.columnRankAt
  rw [hcols]
end
end K1_11_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_4
noncomputable section
open K1_13_6_3_5 K1_13_6_3_5_3
open scoped Polynomial RatFunc
attribute [local instance] Polynomial.algebra
private def scale {L : Type} [Field L] (b : L) (hb : b ≠ 0) :
    L[X] ≃ₐ[L] L[X] :=
  Polynomial.algEquivOfCompEqX (Polynomial.C b⁻¹ * Polynomial.X)
    (Polynomial.C b * Polynomial.X)
    (by simp [← Polynomial.C_mul, ← mul_assoc, hb])
    (by simp [← Polynomial.C_mul, ← mul_assoc, hb])
private theorem coneEval_div {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (b : L) (hb : b ≠ 0) :
    coneEval k (fun i => w i / b) = (scale b hb).toRingHom.comp (coneEval k w) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [coneEval, scale, Polynomial.algebraMap_eq]
  · intro i
    simp only [RingHom.comp_apply, coneEval, MvPolynomial.eval₂Hom_X']
    change Polynomial.C (w i / b) * Polynomial.X =
      Polynomial.aeval (Polynomial.C b⁻¹ * Polynomial.X) (Polynomial.C (w i) * Polynomial.X)
    rw [map_mul, Polynomial.aeval_C, Polynomial.algebraMap_eq, Polynomial.aeval_X, ← mul_assoc,
      ← Polynomial.C_mul, div_eq_mul_inv]
theorem ratioField_div {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (i : σ) (b : L) (hb : b ≠ 0) :
    ratioField k (fun l => w l / b) i = ratioField k w i := by
  have h : ratios (fun l => w l / b) i = ratios w i := by
    funext l
    exact div_div_div_cancel_right₀ hb (w l) (w i)
  simp only [ratioField, h]
private def coneRat {k L σ : Type} [Field k] [Field L] [Algebra k L] (w : σ → L) :
    MvPolynomial σ k →+* RatFunc L :=
  (algebraMap L[X] (RatFunc L)).comp (coneEval k w)
private theorem coneRat_C {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (c : k) :
    coneRat w (MvPolynomial.C c) = RatFunc.C (algebraMap k L c) := by
  simp [coneRat, coneEval]
private theorem coneRat_X {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (i : σ) :
    coneRat (k := k) w (MvPolynomial.X i) = RatFunc.C (w i) * RatFunc.X := by
  simp [coneRat, coneEval]
private theorem coneRat_ker_div {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (b : L) (hb : b ≠ 0) :
    RingHom.ker (coneRat (k := k) (fun i => w i / b)) = coneIdeal k w := by
  rw [coneRat, RingHom.ker_comp_of_injective _ (RatFunc.algebraMap_injective L),
    coneEval_div w b hb]
  exact RingHom.ker_comp_of_injective (coneEval k w)
    (f := (scale b hb).toRingHom) (scale b hb).injective
private def fractionEval {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P) :
    FractionRing (A ⧸ P) →+* K :=
  IsFractionRing.lift (RingHom.lift_injective_of_ker_le_ideal P
    (fun _ ha => RingHom.mem_ker.mp (h.symm ▸ ha)) h.le)
private theorem fractionEval_mk {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P) (a : A) :
    fractionEval P e h
      (algebraMap (A ⧸ P) (FractionRing (A ⧸ P)) (Ideal.Quotient.mk P a)) = e a := by
  rw [fractionEval, IsFractionRing.lift_algebraMap, Ideal.Quotient.lift_mk]
private theorem fractionEval_range_le {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P)
    (S : Subfield K) (he : ∀ a, e a ∈ S) :
    (fractionEval P e h).fieldRange ≤ S := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A ⧸ P) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [map_div₀, fractionEval_mk, fractionEval_mk]
  exact S.div_mem (he a) (he b)
theorem constants_mem {k L σ A : Type} [Field k] [Field L] [Algebra k L]
    [Field A] (w : σ → L) (i : σ) (f : A →+* RatFunc L)
    (he : ∀ p : MvPolynomial σ k, coneRat w p ∈ f.fieldRange)
    {a : L} (ha : a ∈ ratioField k w i) :
    RatFunc.C a ∈ f.fieldRange := by
  let S : IntermediateField k L :=
    (f.fieldRange.comap RatFunc.C).toIntermediateField (fun c => by
      change RatFunc.C (algebraMap k L c) ∈ f.fieldRange
      simpa only [coneRat_C] using he (MvPolynomial.C c))
  have hle : ratioField k w i ≤ S := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨j, rfl⟩
    change RatFunc.C (ratios w i j) ∈ f.fieldRange
    have hx (l : σ) : RatFunc.C (w l) * RatFunc.X ∈ f.fieldRange := by
      simpa only [coneRat_X] using he (MvPolynomial.X l)
    have hd := f.fieldRange.div_mem (hx j) (hx i)
    rwa [mul_div_mul_right _ _ RatFunc.X_ne_zero, ← map_div₀] at hd
  exact hle ha
private theorem ratFunc_mem {F K : Type} [Field F] [Field K]
    (g : RatFunc F →+* K) (S : Subfield K)
    (hC : ∀ a, g (RatFunc.C a) ∈ S) (hX : g RatFunc.X ∈ S) (z : RatFunc F) : g z ∈ S := by
  have hp (p : F[X]) : g (algebraMap F[X] (RatFunc F) p) ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add, map_add]
        exact S.add_mem hp hq
    | monomial n a =>
        rw [RatFunc.algebraMap_monomial, map_mul, map_pow]
        exact S.mul_mem (hC a) (S.pow_mem hX n)
  induction z using RatFunc.induction_on with
  | f p q hq =>
      rw [map_div₀]
      exact S.div_mem (hp p) (hp q)
private theorem ratFunc_map_poly {F L : Type} [Field F] [Field L] [Algebra F L]
    (p : F[X]) :
    algebraMap (RatFunc F) (RatFunc L) (algebraMap F[X] (RatFunc F) p) =
      algebraMap L[X] (RatFunc L) (p.map (algebraMap F L)) := by
  rw [← IsScalarTower.algebraMap_apply F[X] (RatFunc F) (RatFunc L),
    IsScalarTower.algebraMap_apply F[X] L[X] (RatFunc L)]
  rfl
private theorem ratFunc_map_C {F L : Type} [Field F] [Field L] [Algebra F L] (c : F) :
    algebraMap (RatFunc F) (RatFunc L) (RatFunc.C c) = RatFunc.C (algebraMap F L c) := by
  simpa only [RatFunc.algebraMap_C, Polynomial.map_C] using
    ratFunc_map_poly (L := L) (Polynomial.C c)
private theorem ratFunc_map_X {F L : Type} [Field F] [Field L] [Algebra F L] :
    algebraMap (RatFunc F) (RatFunc L) RatFunc.X = RatFunc.X := by
  simpa only [RatFunc.algebraMap_X, Polynomial.map_X] using
    ratFunc_map_poly (L := L) (Polynomial.X : F[X])
set_option maxHeartbeats 1000000 in
theorem proof : K1_13_6_3_5_3.c4 := by
  classical
  intro k L σ τ _ _ _ u i v j φ hi hj hgen hcomp
  let P := coneIdeal k u
  let Q := P.comap φ
  let _ : P.IsPrime := RingHom.ker_isPrime (coneEval k u)
  let _ : Q.IsPrime := Ideal.IsPrime.comap φ
  let U : σ → L := fun l => u l / v j
  let V : τ → L := fun l => v l / v j
  let E := ratioField k v j
  have hnorm : (coneRat (k := k) U).comp φ = coneRat (k := k) V := by
    change ((algebraMap L[X] (RatFunc L)).comp (coneEval k U)).comp φ =
      (algebraMap L[X] (RatFunc L)).comp (coneEval k V)
    rw [show coneEval k U = _ from coneEval_div u (v j) hj,
      show coneEval k V = _ from coneEval_div v (v j) hj,
      RingHom.comp_assoc, RingHom.comp_assoc, hcomp]
  have hP : RingHom.ker (coneRat (k := k) U) = P := coneRat_ker_div u (v j) hj
  have hQ : RingHom.ker (coneRat (k := k) V) = Q := by
    rw [← hnorm, ← RingHom.comap_ker, hP]
  let KU := FractionRing (MvPolynomial σ k ⧸ P)
  let KV := FractionRing (MvPolynomial τ k ⧸ Q)
  let fU : KU →+* RatFunc L := fractionEval P (coneRat U) hP
  let fV : KV →+* RatFunc L := fractionEval Q (coneRat V) hQ
  have hU (p : MvPolynomial σ k) : coneRat U p ∈ fU.fieldRange :=
    ⟨_, fractionEval_mk P (coneRat U) hP p⟩
  have hV (p : MvPolynomial τ k) : coneRat V p ∈ fV.fieldRange :=
    ⟨_, fractionEval_mk Q (coneRat V) hQ p⟩
  let f : KV →+* KU :=
    IsFractionRing.map (Ideal.quotientMap_injective (I := P) (f := φ))
  let _ : Algebra KV KU := f.toAlgebra
  have hsquare : fU.comp f = fV := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial τ k ⧸ Q)
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hf : f (algebraMap (MvPolynomial τ k ⧸ Q) KV (Ideal.Quotient.mk Q p)) =
        algebraMap (MvPolynomial σ k ⧸ P) KU (Ideal.Quotient.mk P (φ p)) := by
      change IsLocalization.map _ (Ideal.quotientMap P φ le_rfl) _ _ = _
      rw [IsLocalization.map_eq]
      rfl
    rw [RingHom.comp_apply, hf]
    exact (fractionEval_mk P (coneRat U) hP (φ p)).trans
      ((RingHom.congr_fun hnorm p).trans (fractionEval_mk Q (coneRat V) hQ p).symm)
  have hX : RatFunc.X ∈ fV.fieldRange := by
    simpa only [coneRat_X, V, div_self hj, map_one, one_mul] using hV (MvPolynomial.X j)
  have hXU : RatFunc.X ∈ fU.fieldRange := by
    obtain ⟨x, hx⟩ := hX
    exact ⟨f x, (RingHom.congr_fun hsquare x).trans hx⟩
  have hConstU (a : L) : RatFunc.C a ∈ fU.fieldRange :=
    constants_mem U i fU hU (by
      rw [show ratioField k U i = ratioField k u i from ratioField_div u i (v j) hj, hgen]
      exact IntermediateField.mem_top)
  have hsurjU : Function.Surjective fU := fun z =>
    ratFunc_mem (RingHom.id (RatFunc L)) fU.fieldRange hConstU hXU z
  let g := algebraMap (RatFunc E) (RatFunc L)
  have hg : g.fieldRange = fV.fieldRange := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ratFunc_mem g fV.fieldRange (fun c => ?_) ?_ z
      · rw [show g (RatFunc.C c) = RatFunc.C (c : L) from ratFunc_map_C c]
        exact constants_mem V j fV hV (by
          rw [show ratioField k V j = E from ratioField_div v j (v j) hj]
          exact c.property)
      · exact ratFunc_map_X (F := E) (L := L) ▸ hX
    · apply fractionEval_range_le
      intro p
      induction p using MvPolynomial.induction_on with
      | C c =>
          rw [coneRat_C]
          exact ⟨RatFunc.C (algebraMap k E c), ratFunc_map_C _⟩
      | add p q hp hq =>
          rw [map_add]
          exact g.fieldRange.add_mem hp hq
      | mul_X p l hp =>
          rw [map_mul, coneRat_X]
          refine g.fieldRange.mul_mem hp (g.fieldRange.mul_mem ?_ ⟨RatFunc.X, ratFunc_map_X⟩)
          have hl : V l ∈ E := IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
          exact ⟨RatFunc.C ⟨V l, hl⟩, ratFunc_map_C _⟩
  let eU := RingEquiv.ofBijective fU ⟨fU.injective, hsurjU⟩
  let eV := fV.rangeRestrictFieldEquiv.trans
    ((RingEquiv.subfieldCongr hg.symm).trans g.rangeRestrictFieldEquiv.symm)
  have hcomm : g.comp eV.toRingHom = eU.toRingHom.comp f := by
    ext1 x
    change g ((g.rangeRestrictFieldEquiv).symm _) = fU (f x)
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    exact (RingHom.congr_fun hsquare x).symm
  unfold residueDegree
  rw [dite_eq_left (show P.IsPrime from inferInstance)]
  change Module.finrank KV KU = Module.finrank E L
  calc
    _ = Module.finrank (RatFunc E) (RatFunc L) := Algebra.finrank_eq_of_equiv_equiv eV eU hcomm
    _ = Module.finrank E[X] L[X] := IsFractionRing.finrank_eq E[X] (RatFunc E) L[X] (RatFunc L)
    _ = Module.finrank E L := congrArg Cardinal.toNat (rank_polynomial_polynomial E L)
end
end K1_13_6_3_5_3_4
end
