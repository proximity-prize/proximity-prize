import ProximityPrize.SubmissionLower.MergedInfra6815_24
import ProximityPrize.SubmissionLower.MergedInfra6815_17
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingSourceVerticalFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators

variable {K : Type} [Field K]

theorem irreducible_of_C (p : Polynomial K)
    (hp : Irreducible (Polynomial.C p : Polynomial (Polynomial K))) : Irreducible p := by
  refine ⟨fun hu => hp.not_isUnit (hu.map Polynomial.C), ?_⟩
  intro a b hab
  have hh := hp.isUnit_or_isUnit (by rw [hab, map_mul])
  exact hh.imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp

theorem associated_minpoly (p : Polynomial K) (hp : Irreducible p)
    {E : Type} [Field E] [Algebra K E] (y : E) (hy : Polynomial.aeval y p=0) :
    Associated p (minpoly K y) := by
  have hi : IsIntegral K y := IsAlgebraic.isIntegral ⟨p,hp.ne_zero,hy⟩
  exact (minpoly.irreducible hi).associated_of_dvd hp (minpoly.dvd K y hy) |>.symm

theorem specialization_ne_zero (p : Polynomial K) (hp : Irreducible p)
    (Q : Polynomial (Polynomial K)) (hproper : ¬Polynomial.C p ∣ Q)
    {E : Type} [Field E] [Algebra K E] (y : E) (hy : Polynomial.aeval y p=0) :
    Q.map (Polynomial.eval₂RingHom (algebraMap K E) y)≠0 := by
  intro hz
  apply hproper
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro j
  have hj := congrArg (fun A : Polynomial E => A.coeff j) hz
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero,
    Polynomial.coe_eval₂RingHom] at hj
  exact (associated_minpoly p hp y hy).dvd.trans (minpoly.dvd K y hj)

theorem finite_of_vertical_roots
    (p : Polynomial K) (hp : Irreducible p) (Q : Polynomial (Polynomial K))
    (hproper : ¬Polynomial.C p ∣ Q)
    {E : Type} [Field E] [Algebra K E] (y r : E)
    (hy : Polynomial.aeval y p=0)
    (hQ : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K E) y) r Q=0)
    (hgen : IntermediateField.adjoin K ({y,r} : Set E)=⊤) :
    FiniteDimensional K E := by
  classical
  letI : DecidableEq K := Classical.decEq K
  have hyi : IsIntegral K y := IsAlgebraic.isIntegral ⟨p,hp.ne_zero,hy⟩
  let S : IntermediateField K E := IntermediateField.adjoin K {y}
  let yS : S := ⟨y,IntermediateField.mem_adjoin_simple_self K y⟩
  let g : Polynomial K →+* S := Polynomial.eval₂RingHom (algebraMap K S) yS
  have hcoeff : (algebraMap S E).comp g=
      Polynomial.eval₂RingHom (algebraMap K E) y := by
    apply Polynomial.ringHom_ext
    · intro c
      change algebraMap S E (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c))=
        Polynomial.eval₂ (algebraMap K E) y (Polynomial.C c)
      rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K S E c).symm
    · change algebraMap S E (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X)=
        Polynomial.eval₂ (algebraMap K E) y Polynomial.X
      simp only [Polynomial.eval₂_X]
      rfl
  have hQne : Q.map g≠0 := by
    intro hz
    have hh := congrArg (Polynomial.map (algebraMap S E)) hz
    rw [Polynomial.map_map,hcoeff,Polynomial.map_zero] at hh
    exact specialization_ne_zero p hp Q hproper y hy hh
  have hr : Polynomial.aeval r (Q.map g)=0 := by
    change Polynomial.eval₂ (algebraMap S E) r (Q.map g)=0
    rw [Polynomial.eval₂_map,hcoeff]
    exact hQ
  have hri : IsIntegral S r := IsAlgebraic.isIntegral ⟨Q.map g,hQne,hr⟩
  letI : FiniteDimensional K S := IntermediateField.adjoin.finiteDimensional hyi
  letI : Algebra.IsIntegral K S := Algebra.IsIntegral.of_finite K S
  exact RCN024.finiteDimensional_of_integral_generating_pair y r hyi
    (isIntegral_trans r hri) hgen

theorem sum_finrank_vertical
    {I : Type*} [Fintype I] (E : I → Type)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, FiniteDimensional K (E i)]
    (p : Polynomial K) (hp : Irreducible p) (Q : Polynomial (Polynomial K))
    (hproper : ¬Polynomial.C p ∣ Q) (y r : ∀ i, E i)
    (hgen : ∀ i, IntermediateField.adjoin K ({y i,r i} : Set (E i))=⊤)
    (hkernels : Function.Injective (fun i => RCN361.relationIdeal K (E i) (y i) (r i)))
    (hy : ∀ i, Polynomial.aeval (y i) p=0)
    (hQ : ∀ i, RCN361.planeEval K (E i) (y i) (r i) Q=0) :
    (∑ i, Module.finrank K (E i)) ≤ Q.natDegree*p.natDegree := by
  classical
  letI : DecidableEq K := Classical.decEq K
  have hspecial : ∀ f ∈ Finset.univ.image (fun i => minpoly K (y i)),
      Q.map (AdjoinRoot.mk f)≠0 := by
    intro f hf hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    apply hproper
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro j
    have hj := congrArg (fun A : Polynomial (AdjoinRoot (minpoly K (y i))) => A.coeff j) hz
    simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at hj
    exact (associated_minpoly p hp (y i) (hy i)).dvd.trans (AdjoinRoot.mk_eq_zero.mp hj)
  have hroot : ∀ i, RCN361.planeEval K (E i) (y i) (r i) (Polynomial.C p)=0 := by
    intro i
    rw [RCN365.planeEval_eq_eval₂,Polynomial.eval₂_C]
    exact hy i
  have hres : Polynomial.resultant Q (Polynomial.C p) Q.natDegree 0≠0 := by
    simpa only [Polynomial.resultant_C_right,pow_zero,one_mul] using pow_ne_zero Q.natDegree hp.ne_zero
  have hb := RCN025.sum_finrank_le_resultant_of_relationIdeal_injective
    E Q (Polynomial.C p) Q.natDegree 0 le_rfl (by simp) y r hgen hkernels
    hQ hroot hspecial hres
  simpa only [Polynomial.resultant_C_right,pow_zero,one_mul,Polynomial.natDegree_pow] using hb

theorem finite_sum_finrank_irreducible
    {I : Type*} [Fintype I] (E : I → Type)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (P Q : Polynomial (Polynomial K)) (hP : Irreducible P) (hproper : ¬P∣Q)
    (y r : ∀ i, E i)
    (hgen : ∀ i, IntermediateField.adjoin K ({y i,r i} : Set (E i))=⊤)
    (hkernels : Function.Injective (fun i => RCN361.relationIdeal K (E i) (y i) (r i)))
    (hProot : ∀ i, RCN361.planeEval K (E i) (y i) (r i) P=0)
    (hQroot : ∀ i, RCN361.planeEval K (E i) (y i) (r i) Q=0) :
    (∀ i, FiniteDimensional K (E i)) ∧
      (∑ i, Module.finrank K (E i)) ≤ (Polynomial.resultant P Q).natDegree := by
  classical
  letI : DecidableEq K := Classical.decEq K
  by_cases hzero : P.natDegree=0
  · have he := Polynomial.eq_C_of_natDegree_eq_zero hzero
    rw [he] at hP hproper hProot ⊢
    have hp := irreducible_of_C (P.coeff 0) hP
    have hy : ∀ i, Polynomial.aeval (y i) (P.coeff 0)=0 := by
      intro i
      have hh := hProot i
      rw [RCN365.planeEval_eq_eval₂,Polynomial.eval₂_C] at hh
      exact hh
    have hfinite : ∀ i, FiniteDimensional K (E i) := fun i =>
      finite_of_vertical_roots (P.coeff 0) hp Q hproper (y i) (r i) (hy i)
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hQroot i)) (hgen i)
    letI : ∀ i, FiniteDimensional K (E i) := hfinite
    refine ⟨hfinite,?_⟩
    have hh := sum_finrank_vertical E (P.coeff 0) hp Q hproper y r hgen hkernels hy hQroot
    simpa only [Polynomial.natDegree_C,Polynomial.resultant_C_left,zero_mul,pow_zero,
      one_mul,Polynomial.natDegree_pow] using hh
  · have hpositive := Nat.pos_of_ne_zero hzero
    have hfinite : ∀ i, FiniteDimensional K (E i) := fun i =>
      RCN024.finite_of_proper_plane_roots P Q hP hpositive hproper (y i) (r i)
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hProot i))
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hQroot i)) (hgen i)
    letI : ∀ i, FiniteDimensional K (E i) := hfinite
    exact ⟨hfinite,RCN124.sum_finrank_le_ordinary_resultant_without_separability
      E P Q hP hpositive hproper y r hgen hkernels hProot hQroot⟩

end
end ProximityPrize.SubmissionLower.MovingSourceVerticalFamily6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN371 RCN011 RCN009 RCN013 RCN008 RCN021 RCN022
open RCN095 RCN125 RCN093 RCN123 RCN121 RCN084 RCN137 RCN071

theorem finite_sum_finrank_projection
    (K : Type) [Field K] (order : Fin 3 ≃ Fin 3) {I : Type} [Fintype I]
    (E : I → Type) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (e : ∀ i, Original K →ₐ[K] E i)
    (ht : ∀ i, Transcendental K (e i (MvPolynomial.X (order 0))))
    (hgen : ∀ i,
      letI : Algebra (RatFunc K) (E i) :=
        (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
          (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))} : Set (E i))=⊤)
    (hkernels : Function.Injective (fun i => RingHom.ker (e i).toRingHom))
    (G H : Original K) (hG : Irreducible G)
    (hGroot : ∀ i, e i G=0) (hHroot : ∀ i, e i H=0) (hproper : ¬G∣H) :
    letI : ∀ i, Algebra (RatFunc K) (E i) := fun i =>
      (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
        (ht i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (E i)) ∧
      (∑ i, Module.finrank (RatFunc K) (E i)) ≤
        (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree := by
  classical
  letI : ∀ i, Algebra (RatFunc K) (E i) := fun i =>
    (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
      (ht i)).toRingHom.toAlgebra
  by_cases hI : Nonempty I
  · let i₀ : I := Classical.choice hI
    have hirr : Irreducible (planeMap K order G) :=
      planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
        G hG (hGroot i₀) (ht i₀)
    have hproperPlane : ¬planeMap K order G ∣ planeMap K order H := by
      intro hdiv
      exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
        G H hG (hGroot i₀) (ht i₀)).mp hdiv)
    have hGroots : ∀ i, RCN361.planeEval (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
        (planeMap K order G)=0 := by
      intro i
      change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order G)=0
      rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
      exact hGroot i
    have hHroots : ∀ i, RCN361.planeEval (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
        (planeMap K order H)=0 := by
      intro i
      change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order H)=0
      rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
      exact hHroot i
    have hrelation : Function.Injective (fun i => RCN361.relationIdeal (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))) := by
      intro i j hij
      apply hkernels
      change relationKernel K (E i) order (e i) (ht i)=
        relationKernel K (E j) order (e j) (ht j) at hij
      have hc := congrArg (Ideal.comap (planeMap K order)) hij
      simpa only [relationKernel_contract] using hc
    exact MovingSourceVerticalFamily6814.finite_sum_finrank_irreducible E
      (planeMap K order G) (planeMap K order H) hirr hproperPlane
      (fun i => e i (MvPolynomial.X (order 2)))
      (fun i => e i (MvPolynomial.X (order 1))) hgen hrelation hGroots hHroots
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    exact ⟨fun i => isEmptyElim i,by simp⟩

theorem all_factors_mixed_sum_le
    {K : Type} [Field K] (B : MvPolynomial (Fin 3) K) (hB : B≠0)
    (p q r : FlagDegree) (hsupport : RCN095.PolynomialInFlag p B) :
    (∑ g : ↥(normalizedFactorSet B), flagMixed (exactFlag g.1) q r) ≤ flagMixed p q r := by
  classical
  have hc := inFlag_weight_caps B p hsupport
  have hw (w : Fin 3 → ℕ) :
      (∑ g : ↥(normalizedFactorSet B), MvPolynomial.weightedTotalDegree w g.1) ≤
        MvPolynomial.weightedTotalDegree w B := by
    rw [Finset.sum_coe_sort]
    exact sum_weightedTotalDegree_le_of_prod_dvd_fin3 w (normalizedFactorSet B) id B hB
      (normalizedFactorSet_product_dvd B hB)
  apply sum_flagMixed_le_of_cumulative
  · simpa only [(exactFlag_cumulative _).1] using (hw flagSWeights).trans hc.1
  · calc
      _=∑ g : ↥(normalizedFactorSet B), MvPolynomial.weightedTotalDegree flagYSWeights g.1 :=
        Finset.sum_congr rfl (fun g _ => (exactFlag_cumulative g.1).2.1)
      _ ≤ _ := (hw flagYSWeights).trans hc.2.1
  · calc
      _=∑ g : ↥(normalizedFactorSet B), MvPolynomial.weightedTotalDegree flagTotalWeights g.1 :=
        Finset.sum_congr rfl (fun g _ => (exactFlag_cumulative g.1).2.2)
      _ ≤ _ := (hw flagTotalWeights).trans hc.2.2

inductive Axis | z | u | v

def Axis.order : Axis → (Fin 3 ≃ Fin 3)
  | .z => zOrder
  | .u => uOrder
  | .v => vOrder

def Axis.flag : Axis → FlagDegree
  | .z => unitZFlag
  | .u => unitYZFlag
  | .v => unitAllFlag

theorem flag_resultant_degree_le
    {K : Type} [Field K] (axis : Axis) (lam mu nu : K)
    (G H : MvPolynomial (Fin 3) K) (p q : FlagDegree)
    (hG : RCN095.PolynomialInFlag p G) (hH : RCN095.PolynomialInFlag q H) (hHne : H≠0) :
    (Polynomial.resultant (planeMap K axis.order (flagAlgHom lam mu nu G))
      (planeMap K axis.order (flagAlgHom lam mu nu H))).natDegree ≤ flagMixed p q axis.flag := by
  have hGs := (support_subset_flagSupport_iff _ _).mpr hG
  have hHs := (support_subset_flagSupport_iff _ _).mpr hH
  cases axis with
  | z => exact RCN112.flagPlaneResultant_z_degree_le p q lam mu nu hGs hHs hHne
  | u => exact RCN112.flagPlaneResultant_u_degree_le p q lam mu nu hGs hHs hHne
  | v => exact RCN112.flagPlaneResultant_v_degree_le p q lam mu nu hGs hHs hHne

end
end ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingSourceSharedFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN371 RCN011 RCN022 RCN095 RCN093 RCN123 RCN121 RCN084 RCN137
open RCN125 (flagAlgHom flag_irreducible_iff flag_dvd_iff)
open MovingSourceProjectionFamily6814

theorem finite_sum_finrank_coprime_flags
    (K : Type) [Field K] (axis : Axis) (lam mu nu : K) {I : Type} [Fintype I]
    (E : I → Type) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (e : ∀ i, Original K →ₐ[K] E i)
    (ht : ∀ i, Transcendental K (e i (MvPolynomial.X (axis.order 0))))
    (hgen : ∀ i,
      letI : Algebra (RatFunc K) (E i) :=
        (elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
          (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (axis.order 2)),e i (MvPolynomial.X (axis.order 1))} :
          Set (E i))=⊤)
    (hkernels : Function.Injective (fun i => RingHom.ker (e i).toRingHom))
    (B H : Original K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBroot : ∀ i, e i (flagAlgHom lam mu nu B)=0)
    (hHroot : ∀ i, e i (flagAlgHom lam mu nu H)=0)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    letI : ∀ i, Algebra (RatFunc K) (E i) := fun i =>
      (elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
        (ht i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (E i)) ∧
      (∑ i, Module.finrank (RatFunc K) (E i)) ≤ flagMixed p q axis.flag := by
  classical
  letI : ∀ i, Algebra (RatFunc K) (E i) := fun i =>
    (elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
      (ht i)).toRingHom.toAlgebra
  have hex : ∀ i, ∃ g : ↥(normalizedFactorSet B), e i (flagAlgHom lam mu nu g.1)=0 := by
    intro i
    obtain ⟨g,hg,hroot⟩ := exists_normalizedFactorSet_zero
      ((e i).toRingHom.comp (flagAlgHom lam mu nu).toRingHom) B hB (hBroot i)
    exact ⟨⟨g,hg⟩,hroot⟩
  choose owner howner using hex
  have hgroup (g : ↥(normalizedFactorSet B)) :
      (∀ i : {i // owner i=g}, FiniteDimensional (RatFunc K) (E i.1)) ∧
        (∑ i : {i // owner i=g}, Module.finrank (RatFunc K) (E i.1)) ≤
          flagMixed (exactFlag g.1) q axis.flag := by
    have hg := normalizedFactorSet_spec B g.1 g.2
    have hproper : ¬g.1∣H := fun hgH => hg.1.not_isUnit (hrel hg.2 hgH)
    have hker : Function.Injective
        (fun i : {i // owner i=g} => RingHom.ker (e i.1).toRingHom) := by
      intro i j hij
      exact Subtype.ext (hkernels hij)
    have hgroot : ∀ i : {i // owner i=g}, e i.1 (flagAlgHom lam mu nu g.1)=0 := by
      intro i
      have hh := howner i.1
      rw [i.2] at hh
      exact hh
    have hb := finite_sum_finrank_projection K axis.order
      (fun i : {i // owner i=g} => E i.1)
      (fun i => e i.1) (fun i => ht i.1) (fun i => hgen i.1) hker
      (flagAlgHom lam mu nu g.1) (flagAlgHom lam mu nu H)
      ((flag_irreducible_iff lam mu nu g.1).mpr hg.1)
      hgroot (fun i => hHroot i.1) (by simpa only [flag_dvd_iff] using hproper)
    exact ⟨hb.1,hb.2.trans (flag_resultant_degree_le axis lam mu nu g.1 H
      (exactFlag g.1) q (polynomialIn_exactFlag g.1) hq hH)⟩
  refine ⟨fun i => (hgroup (owner i)).1 ⟨i,rfl⟩,?_⟩
  calc
    (∑ i, Module.finrank (RatFunc K) (E i))=
        ∑ g : ↥(normalizedFactorSet B),
          ∑ i : {i // owner i=g}, Module.finrank (RatFunc K) (E i.1) :=
      (Fintype.sum_fiberwise owner (fun i => Module.finrank (RatFunc K) (E i))).symm
    _ ≤ ∑ g : ↥(normalizedFactorSet B), flagMixed (exactFlag g.1) q axis.flag :=
      Finset.sum_le_sum (fun g _ => (hgroup g).2)
    _ ≤ flagMixed p q axis.flag := all_factors_mixed_sum_le B hB p q axis.flag hp

end
end ProximityPrize.SubmissionLower.MovingSourceSharedFamily6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN011 RCN022 RCN116 RCN095 RCN093 RCN123 RCN121
open RCN125 (flagAlgHom zOrder uOrder vOrder)
open MovingSourceProjectionFamily6814 MovingSourceSharedFamily6814

private theorem embedding_congr
    {K E : Type} [Field K] [Field E] [Algebra K E]
    {x y : E} (hx : Transcendental K x) (hy : Transcendental K y) (h : x=y) :
    elementEmbedding K E x hx=elementEmbedding K E y hy := by
  subst y
  rfl

theorem flag_generators_axis
    (K : Type) [Field K] (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (axis : Axis) (lam mu nu : K)
    (ht : Transcendental K (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0)))) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc K)
      ({flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 2)),
        flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 1))} :
        Set (CoordinateField K P))=⊤ := by
  cases axis with
  | z =>
    have hz : Transcendental K (coordinate K P 2) := by
      simpa [Axis.order,zOrder,Equiv.swap_apply_def] using ht
    have he : elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.z.order 0))) ht=
        elementEmbedding K (CoordinateField K P) (coordinate K P 2) hz :=
      embedding_congr ht hz (by simp [Axis.order,zOrder])
    rw [he]
    simpa [Axis.order,zOrder,Equiv.swap_apply_def] using flag_generators_z K P lam mu nu hz
  | u =>
    have hu : Transcendental K (affineU K P lam) := by
      simpa [Axis.order,uOrder] using ht
    have he : elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.u.order 0))) ht=
        elementEmbedding K (CoordinateField K P) (affineU K P lam) hu :=
      embedding_congr ht hu (by simp [Axis.order,uOrder])
    rw [he]
    simpa [Axis.order,uOrder] using flag_generators_u K P lam mu nu hu
  | v =>
    have hv : Transcendental K (affineV K P mu nu) := by
      simpa [Axis.order,vOrder,Equiv.swap_apply_def] using ht
    have he : elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.v.order 0))) ht=
        elementEmbedding K (CoordinateField K P) (affineV K P mu nu) hv :=
      embedding_congr ht hv (by simp [Axis.order,vOrder])
    rw [he]
    simpa [Axis.order,vOrder,Equiv.swap_apply_def] using flag_generators_v K P lam mu nu hv

theorem finite_sum_prime_fields
    (K : Type) [Field K] (axis : Axis) (lam mu nu : K) {I : Type} [Fintype I]
    (P : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (P i).IsPrime]
    (hinj : Function.Injective P)
    (ht : ∀ i, Transcendental K
      (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))))
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ i, B∈P i) (hHmem : ∀ i, H∈P i)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) := fun i =>
      (elementEmbedding K (CoordinateField K (P i))
        (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))
          (ht i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ flagMixed p q axis.flag := by
  have hroot (A : MvPolynomial (Fin 3) K) (ha : ∀ i, A∈P i) :
      ∀ i, flagEvaluation K (P i) lam mu nu (flagAlgHom lam mu nu A)=0 := by
    intro i
    rw [flagEvaluation_flag]
    change A∈RingHom.ker (coordinateEvaluation K (P i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact ha i
  exact finite_sum_finrank_coprime_flags K axis lam mu nu
    (fun i => CoordinateField K (P i)) (fun i => flagEvaluation K (P i) lam mu nu)
    ht (fun i => flag_generators_axis K (P i) axis lam mu nu (ht i))
    (flagEvaluation_kernel_family_injective K P hinj lam mu nu)
    B H hB hH hrel (hroot B hBmem) (hroot H hHmem) p q hp hq

end
end ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourcePoleBudget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN022 RCN037 RCN042 RCN046 RCN093 RCN095 RCN114 RCN116 RCN237 RCN264 RCN341 RCN344
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814

theorem sum_coordinateOfGate_le
    (K : Type) [Field K] [IsAlgClosed K] (axis : Axis) (lam mu nu : K)
    {I : Type} [Fintype I]
    (P : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (P i).IsPrime]
    (hinj : Function.Injective P)
    (hgate : ∀ i, ∀ ht : Transcendental K
        (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))),
      (letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
        (elementEmbedding K (CoordinateField K (P i))
          (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) (CoordinateField K (P i))) ∧
      (letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
        (elementEmbedding K (CoordinateField K (P i))
          (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))))
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ i, B∈P i) (hHmem : ∀ i, H∈P i)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    (∑ i, coordinateDegree K (CoordinateField K (P i))
      (coordinateOfGate (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))
        (hgate i))) ≤ flagMixed p q axis.flag := by
  classical
  rw [sum_coordinateOfGate_degree_eq]
  exact (finite_sum_prime_fields K axis lam mu nu
    (fun i : {i // Transcendental K
      (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))} => P i.1)
    (fun i j hij => Subtype.ext (hinj hij)) (fun i => i.2)
    B H hB hH hrel (fun i => hBmem i.1) (fun i => hHmem i.1) p q hp hq).2

variable {K : Type} [Field K] [IsAlgClosed K]
    {G T R : MvPolynomial (Fin 3) K}

def projectionFamily_of_coprime_pair
    (base : ∀ C : RegularComponent K G T R, SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent K G T R, LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent K G T R, LiteralProjectionGate C 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (D : AdaptiveNestedProjectionData base hY hZ hderiv)
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ C : RegularComponent K G T R, B∈C.1)
    (hHmem : ∀ C : RegularComponent K G T R, H∈C.1)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    AdaptiveUnitProjectionFamily base p q := by
  classical
  let x (axis : Axis) (C : RegularComponent K G T R) :=
    flagEvaluation K C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0))
  have gate (axis : Axis) (C : RegularComponent K G T R)
      (ht : Transcendental K (x axis C)) :
      (letI : Algebra (RatFunc K) (CoordinateField K C.1) :=
        (elementEmbedding K (CoordinateField K C.1) (x axis C) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) (CoordinateField K C.1)) ∧
      (letI : Algebra (RatFunc K) (CoordinateField K C.1) :=
        (elementEmbedding K (CoordinateField K C.1) (x axis C) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1)) := by
    cases axis with
    | z =>
      have hz : Transcendental K (coordinate K C.1 2) := by
        simpa only [x,Axis.order,RCN125.zOrder,Equiv.swap_apply_left,flagEvaluation_X_two] using ht
      have he := elementEmbedding_congr ht hz (by
        simp only [x,Axis.order,RCN125.zOrder,Equiv.swap_apply_left,flagEvaluation_X_two])
      rw [he]
      exact hZ C hz
    | u =>
      have hu : Transcendental K (affineU K C.1 D.lam) := by
        simpa only [x,Axis.order,RCN125.uOrder,Equiv.refl_apply,flagEvaluation_X_zero] using ht
      have he := elementEmbedding_congr ht hu (by
        simp only [x,Axis.order,RCN125.uOrder,Equiv.refl_apply,flagEvaluation_X_zero])
      rw [he]
      exact D.uGate C hu
    | v =>
      have he := elementEmbedding_congr ht (D.allAffineTranscendental C) (by
        simp only [x,Axis.order,RCN125.vOrder,Equiv.swap_apply_left,flagEvaluation_X_one])
      rw [he]
      exact ⟨D.allFinite C,D.allSeparable C⟩
  let projection (axis : Axis) (C : RegularComponent K G T R) :=
    coordinateOfGate (x axis C) (gate axis C)
  have hsum (axis : Axis) :
      (∑ C : RegularComponent K G T R,
        coordinateDegree K (CoordinateField K C.1) (projection axis C)) ≤ flagMixed p q axis.flag :=
    sum_coordinateOfGate_le K axis D.lam D.mu (D.mu*D.lam)
      (fun C : RegularComponent K G T R => C.1)
      (fun _ _ h => Subtype.ext h) (gate axis) B H hB hH hrel hBmem hHmem p q hp hq
  have hz (C : RegularComponent K G T R) :
      coordinateValue K (CoordinateField K C.1) (projection .z C)=coordinate K C.1 2 := by
    simp only [projection,coordinateOfGate_value,x,Axis.order,RCN125.zOrder,
      Equiv.swap_apply_left,flagEvaluation_X_two]
  have hu (C : RegularComponent K G T R) :
      coordinateValue K (CoordinateField K C.1) (projection .u C)=affineU K C.1 D.lam := by
    simp only [projection,coordinateOfGate_value,x,Axis.order,RCN125.uOrder,
      Equiv.refl_apply,flagEvaluation_X_zero]
  have hv (C : RegularComponent K G T R) :
      coordinateValue K (CoordinateField K C.1) (projection .v C)=affineV K C.1 D.mu (D.mu*D.lam) := by
    simp only [projection,coordinateOfGate_value,x,Axis.order,RCN125.vOrder,
      Equiv.swap_apply_left,flagEvaluation_X_one]
  refine {
    zProjection := projection .z
    yzProjection := projection .u
    allProjection := projection .v
    zValue := hz
    allTranscendental := ?_
    zPole_eq := ?_
    yzPole_eq := ?_
    allPole_eq := ?_
    sum_zDegree_le := hsum .z
    sum_yzDegree_le := hsum .u
    sum_allDegree_le := hsum .v }
  · intro C
    rw [hv C]
    exact D.allAffineTranscendental C
  · intro C v
    rw [exponentSetPoleWeight_unitZ]
    change _=RCN187.poleOrder v.val _
    rw [hz C]
  · intro C v
    rw [exponentSetPoleWeight_unitYZ]
    change _=RCN187.poleOrder v.val _
    rw [hu C,←D.uValue C]
    exact (D.uPole C v).symm
  · intro C v
    rw [exponentSetPoleWeight_unitAll]
    change _=RCN187.poleOrder v.val _
    rw [hv C,←D.allValue C]
    exact (D.allPole C v).symm

end
end ProximityPrize.SubmissionLower.MovingSourcePoleBudget6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingSourceCarrierZeros6814 RCN234 RCN156

variable {K : Type} [Field K]

instance carrierSpanPrime (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (Fact.out : Irreducible F).prime

abbrev CarrierRing (F : MvPolynomial (Fin 4) K) :=
  MvPolynomial (Fin 4) K ⧸ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))

abbrev CarrierField (F : MvPolynomial (Fin 4) K) := FractionRing (CarrierRing F)

def carrierMap (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    MvPolynomial (Fin 4) K →+* CarrierField F :=
  (algebraMap (CarrierRing F) (CarrierField F)).comp (Ideal.Quotient.mk _)

theorem carrierMap_zero_iff (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (P : MvPolynomial (Fin 4) K) : carrierMap F P=0 ↔ F∣P := by
  change algebraMap (CarrierRing F) (CarrierField F) (Ideal.Quotient.mk _ P)=0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (CarrierRing F) (CarrierField F)),
    Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]

theorem carrierMap_self (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    carrierMap F F=0 := (carrierMap_zero_iff F F).mpr (dvd_refl F)

instance carrierField_charP (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (p : ℕ) [CharP K p] : CharP (CarrierField F) p :=
  charP_of_injective_ringHom ((carrierMap F).comp MvPolynomial.C).injective p

theorem carrier_H_nonzero (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    [CharP K 2130706433] (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    carrierMap F (2*RCN313.polyH K F)≠0 := by
  have hh : carrierMap F (RCN313.polyH K F)≠0 := by
    intro hz
    exact RCN267.equation_not_dvd_R_derivative F 2130706433 hpos hsmall
      ((carrierMap_zero_iff F _).mp hz)
  rw [map_mul,map_ofNat]
  apply mul_ne_zero _ hh
  exact (CharP.cast_eq_zero_iff (CarrierField F) 2130706433 2).not.mpr (by decide)

theorem carrier_polynomial_nonzero
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (P : WholeSpaceCube6814.Poly (K := K)) (hP : P≠0) (cap : ℕ)
    (hshape : ∀ e ∈ P.support, e 1+e 2+e 3+e 4≤cap)
    (hF : cap<wt residualTotalWeights F) : (asS P).map (carrierMap F)≠0 := by
  have hh := SecondJetTotalAvoidance.leading_not_dvd P hP F cap hshape hF
  have hl : carrierMap F (asS P).leadingCoeff≠0 := by
    exact fun hz => hh.2 ((carrierMap_zero_iff F _).mp hz)
  exact (SecondJetCoefficientAvoidance.map_degree_preserved (asS P) (carrierMap F) hl).1

end
end ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingSourceHybridCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
open scoped BigOperators
open RCN002 RCN037 RCN042 RCN046 RCN072 RCN084 RCN095 RCN136 RCN207 RCN237 RCN264 RCN341 RCN344
open SecondJetCoefficients SecondJetClearedHelper
open MovingFiberProjection6811 MovingFiberThreeSources6811 MovingFiberNativeBudget6811

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local notation "Poly3" => MvPolynomial (Fin 3) Ω

theorem old_z_bound_on_new_projections
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) (S : Source F)
    (carrier : Poly3) (p : FlagDegree)
    (hcarrier : carrier≠0) (hcarrierF : carrier∣surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all)<c)
    (h2 : (2 : Ω)≠0) (hfact : (S.k.factorial : Ω)≠0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (R : Poly3)
    (hH : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      surfaceMap phi (RCN313.polyH K F)∉C.1)
    (hL : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      S.leading phi∉C.1)
    (base : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      SeparableLiteralCoordinate C.1)
    (pNew qNew : FlagDegree) (unit : AdaptiveUnitProjectionFamily base pNew qNew) :
    S.d*(∑ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      coordinateDegree Ω (CoordinateField Ω C.1) (unit.zProjection C)) ≤
      flagMixed p unitZFlag S.flag := by
  classical
  let H := surfaceMap phi (RCN313.polyH K F)
  let M := movingEquation H (surfaceMap phi (RCN313.polyG K F)) Q A target
  let Family := RegularComponent Ω carrier M R
  let forget (C : Family) : RegularComponent Ω carrier M (H*S.leading phi) :=
    ⟨C.1,(mem_regularComponents Ω).mpr ⟨regularComponent_mem Ω carrier M R C,by
      intro hz
      exact ((inferInstance : C.1.IsPrime).mem_or_mem hz).elim (hH C) (hL C)⟩⟩
  have hinj : Function.Injective forget := by
    intro C D h
    exact Subtype.ext (congrArg (fun C0 : RegularComponent Ω carrier M (H*S.leading phi) => C0.1) h)
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : Algebra Ω Ext := ((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI : SMul (RatFunc Ω) Ext := (inferInstance : Algebra (RatFunc Ω) Ext).toSMul
  letI : SMul Ω Ext := (inferInstance : Algebra Ω Ext).toSMul
  letI : IsScalarTower Ω (RatFunc Ω) Ext := by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI : CharP Ext c := by infer_instance
  have h2e : (2 : Ext)≠0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfe : (S.k.factorial : Ext)≠0 := by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne hfact
  exact sum_coordinate_projection_degrees (E:=Ext) phi F carrier p unitZFlag hcarrier hcarrierF hflag
    linearZ linearZ_flag c (by omega) (by simpa [unitZFlag] using hunit)
    S.P S.B S.U S.T S.s S.k S.n0 S.hS S.hshape S.hBU S.hUT S.hdn S.hB S.hn S.hdiv
    h2e hfe Q A target hQ hA forget hinj unit.zProjection unit.zValue

end
end ProximityPrize.SubmissionLower.MovingSourceHybridCount6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN046 RCN095 RCN264 RCN341 RCN344

variable {K : Type} [Field K]
    {G M R : MvPolynomial (Fin 3) K}

def forgetExtra (L : MvPolynomial (Fin 3) K)
    (C : RegularComponent K G M (R*L)) : RegularComponent K G M R := by
  classical
  exact ⟨C.1,(mem_regularComponents K).mpr ⟨regularComponent_mem K G M (R*L) C,by
    intro hz
    exact regularComponent_H_not_mem K G M (R*L) C (C.1.mul_mem_right L hz)⟩⟩

theorem forgetExtra_injective (L : MvPolynomial (Fin 3) K) :
    Function.Injective (forgetExtra (G:=G) (M:=M) (R:=R) L) := by
  intro C D h
  exact Subtype.ext (congrArg (fun C0 : RegularComponent K G M R => C0.1) h)

theorem extra_not_mem (L : MvPolynomial (Fin 3) K)
    (C : RegularComponent K G M (R*L)) : L∉C.1 := by
  intro hz
  exact regularComponent_H_not_mem K G M (R*L) C (C.1.mul_mem_left R hz)

private theorem sum_pullback_le {I J : Type} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (v : J → ℕ) :
    (∑ i, v (f i))≤∑ j, v j := by
  classical
  letI : DecidableEq J := Classical.decEq J
  calc
    _ = ∑ j ∈ Finset.univ.image f, v j := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def restrict_projection_family [IsAlgClosed K]
    (base : ∀ C : RegularComponent K G M R, SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p q)
    (L : MvPolynomial (Fin 3) K) :
    AdaptiveUnitProjectionFamily (fun C => base (forgetExtra L C)) p q where
  zProjection := fun C => unit.zProjection (forgetExtra L C)
  yzProjection := fun C => unit.yzProjection (forgetExtra L C)
  allProjection := fun C => unit.allProjection (forgetExtra L C)
  zValue := fun C => unit.zValue (forgetExtra L C)
  allTranscendental := fun C => unit.allTranscendental (forgetExtra L C)
  zPole_eq := fun C v => unit.zPole_eq (forgetExtra L C) v
  yzPole_eq := fun C v => unit.yzPole_eq (forgetExtra L C) v
  allPole_eq := fun C v => unit.allPole_eq (forgetExtra L C) v
  sum_zDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.zProjection C))).trans unit.sum_zDegree_le
  sum_yzDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C))).trans unit.sum_yzDegree_le
  sum_allDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.allProjection C))).trans unit.sum_allDegree_le

open RCN084 RCN136 RCN207
open MovingFiberThreeSources6811 MovingSourceHybridCount6814

end
end ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.MovingSourceZCounts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  130*181255-SecondJetRelaxedDifferentiation.reserve 6 8 h*50186

end ProximityPrize.SubmissionLower.MovingSourceZCounts6814
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.MovingSourceZSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
open SecondJetRelaxedDifferentiation MovingSourceZCounts6814 MovingFiberThreeSources6811
open RCN234 RCN156

variable {K N : Type} [Field K] [Fintype N]

def Bounds (P : Poly (K:=K)) : Prop := ∀ e ∈ P.support,
  2*e 1+e 3≤53 ∧ e 1≤24 ∧ e 1+e 2+e 3≤177 ∧ e 1+e 2+e 3+e 4≤3429 ∧
    e 0+131071*e 2+131070*e 3+131069*e 1<cutoff (e 1)

def Interpolant (nodes : N ↪ K) (u0 u1 : N → K) (P : Poly (K:=K)) : Prop :=
  P≠0 ∧ Bounds P ∧ ∀ i, MvPolynomial.X 0^130 ∣ SecondJetDifferentiation.substitute (K:=K)
    (localize (nodes i) (u0 i) (u1 i) P)

theorem derivative_vanish (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K:=K)) (hP : Interpolant nodes u0 u1 P)
    (d : ℕ) (hd : d≤6) (f : Polynomial K) (hf : f.natDegree≤131071)
    (z : K) (S : Finset N) (hS : 181255≤S.card)
    (hvalues : ∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z) :
    specialize f z ((pderiv 1)^[d] P)=0 := by
  apply SecondJetRelaxedDifferentiation.derivative_vanish P 130 181255 131071 6 8 d
    (by omega) (by omega) (by omega) hd ?_ nodes u0 u1 hP.2.2 f hf z S hS hvalues
  intro e he
  have hh := (hP.2.1 e he).2.2.2.2
  dsimp [cutoff] at hh
  norm_num
  omega

theorem low_coefficient_vanish (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K:=K)) (hP : Interpolant nodes u0 u1 P)
    (d : ℕ) (hd : d<8) (hfact : (d.factorial : K)≠0)
    (f : Polynomial K) (hf : f.natDegree≤131071) (z : K) (S : Finset N)
    (hS : 181255≤S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z)
    (hh : ∀ j, d<j → coefficientSpecialize f z ((asS P).coeff j)=0) :
    coefficientSpecialize f z ((asS P).coeff d)=0 := by
  have hweight : ∀ e ∈ ((asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2<(130-d)*181255 := by
    intro e he
    have hb := (hP.2.1 _ (coefficient_support P d e he)).2.2.2.2
    obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [cutoff,reserve,if_pos hd] at hb
    omega
  have hdeg := MovingFiberLeadingCoefficient6811.coefficient_degree ((asS P).coeff d)
    f z 131071 ((130-d)*181255) hf (by omega) hweight
  have htop := MovingFiberLeadingCoefficient6811.specialize_top P f z d hh
  have hv : specialize f z ((pderiv 1)^[d] P)=0 := by
    refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (130-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (show d≤130 by omega)] using hP.2.2 i
    · rw [htop]
      exact ((Polynomial.natDegree_smul_le d.factorial _).trans_lt hdeg).trans_le
        (Nat.mul_le_mul_left (130-d) hS)
  rw [htop,nsmul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (by
    simpa only [map_natCast] using Polynomial.C_ne_zero.mpr hfact)

end
end ProximityPrize.SubmissionLower.MovingSourceZSupplier6814
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN022 RCN037 RCN046 RCN093 RCN095 RCN116 RCN264 RCN341
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814 MovingSourcePoleBudget6814

theorem separable_of_finrank_lt_char
    {K E : Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    (c : ℕ) [CharP K c] (h : Module.finrank K E<c) : Algebra.IsSeparable K E := by
  classical
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq E := Classical.decEq E
  refine ⟨fun x => ?_⟩
  exact (RCN364.integral_and_separable_of_small_annihilator c (minpoly K x) x
    (minpoly.ne_zero (IsIntegral.of_finite K x)) (minpoly.aeval K x)
    ((minpoly.natDegree_le x).trans_lt h)).2

theorem prime_projection_gate
    {K : Type} [Field K] (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (axis : Axis) (lam mu nu : K)
    (ht : Transcendental K (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))))
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : B∈P) (hHmem : H∈P)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H)
    (c : ℕ) [CharP K c] (hsmall : flagMixed p q axis.flag<c) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    (elementEmbedding K (CoordinateField K P)
      (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
  have hfamily := finite_sum_prime_fields K axis lam mu nu (fun _ : Unit => P)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => ht)
    B H hB hH hrel (fun _ => hBmem) (fun _ => hHmem) p q hp hq
  letI : FiniteDimensional (RatFunc K) (CoordinateField K P) := hfamily.1 ()
  have hdegree : Module.finrank (RatFunc K) (CoordinateField K P)≤flagMixed p q axis.flag := by
    simpa only [Fintype.sum_unique] using hfamily.2
  exact ⟨inferInstance,separable_of_finrank_lt_char c (hdegree.trans_lt hsmall)⟩

end
end ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.MovingSourceTargetField6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open RCN135

variable (K : Type) [Field K]

theorem coefficientEmbedding_eq_algebraMap :
    coefficientEmbedding K=algebraMap K (GenericField K) := by
  ext c
  change algebraMap (RationalBase K) (GenericField K)
    (algebraMap (Polynomial K) (RationalBase K) (algebraMap K (Polynomial K) c))=
      algebraMap K (GenericField K) c
  rw [←IsScalarTower.algebraMap_apply K (Polynomial K) (RationalBase K),
    ←IsScalarTower.algebraMap_apply K (RationalBase K) (GenericField K)]

def rationalEmbedding : RatFunc K →ₐ[K] GenericField K :=
  (IsScalarTower.toAlgHom K (RationalBase K) (GenericField K)).comp
    (RatFunc.toFractionRingAlgEquiv K K).toAlgHom

theorem rationalEmbedding_variable :
    rationalEmbedding K (RCN202.rationalVariable K)=initialCoordinate K := by
  change algebraMap (RationalBase K) (GenericField K)
    ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X).toFractionRing)=_
  rw [←RatFunc.ofFractionRing_algebraMap]
  rfl

abbrev targetAlgebra : Algebra (RatFunc K) (GenericField K) :=
  (rationalEmbedding K).toRingHom.toAlgebra

theorem target_tower :
    letI := targetAlgebra K
    IsScalarTower K (RatFunc K) (GenericField K) := by
  letI := targetAlgebra K
  exact IsScalarTower.of_algebraMap_eq fun c => ((rationalEmbedding K).commutes c).symm

theorem target_variable :
    letI := targetAlgebra K
    algebraMap (RatFunc K) (GenericField K) (RCN202.rationalVariable K)=initialCoordinate K :=
  rationalEmbedding_variable K

end
end ProximityPrize.SubmissionLower.MovingSourceTargetField6814
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
local instance : Algebra (RatFunc Omega) OmegaT := targetAlgebra Omega
local instance : IsScalarTower Omega (RatFunc Omega) OmegaT := target_tower Omega

def baseCarrier (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) F
def baseH (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) (polyH K F)
def baseG (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) (polyG K F)

def targetCut (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (Q A : MvPolynomial (Fin 3) Omega) : MvPolynomial (Fin 3) OmegaT :=
  eliminatedCut n (fun j => lift (coeff j)) (lift Q) (lift A) (initialCoordinate Omega)

theorem scalar_eq_lift (P : MvPolynomial (Fin 3) Omega) : scalarPolynomialMap Omega OmegaT P=lift P := by
  rw [scalarPolynomialMap,←coefficientEmbedding_eq_algebraMap Omega]

theorem targetCut_small_flag
    (F : MvPolynomial (Fin 4) K) (a b s n : ℕ) (center : FlagDegree)
    (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega) (flags : Fin (n+1) → FlagDegree)
    (hH : PolynomialInFlag ⟨a,b+1,s+1⟩ (baseH F))
    (hG : PolynomialInFlag ⟨a,b,s+3⟩ (baseG F))
    (hcoeff : ∀ j, PolynomialInFlag (flags j) (coeff j))
    (heq : ∀ j, flags j+(n-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree)=center+n • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree))
    (Q A : MvPolynomial (Fin 3) Omega)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (center+n • (⟨a,b+1,s+2⟩ : FlagDegree)) (targetCut n coeff Q A) := by
  have hh := (fiber_small_flags (E:=OmegaT) a b s n center (baseH F) (baseG F) Q A coeff flags
    hH hG hQ hA hcoeff heq).2
  simpa only [fiberCut,scalar_eq_lift,target_variable,targetCut] using hh

end
end ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
end MergedPart12
section MergedPart13
namespace ProximityPrize.SubmissionLower.MovingSourceNativeFactor6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper SecondJetCarrierDichotomy
open MovingFiberThreeSources6811 MovingSourceCarrierField6814

variable {K E : Type} [Field K] [Field E]

theorem asS_natDegree (P : SecondJetSupport.Poly (K:=K)) :
    (asS P).natDegree=P.degreeOf 1 := by
  change (MvPolynomial.finSuccEquiv K 4 (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) P)).natDegree=_
  rw [MvPolynomial.natDegree_finSuccEquiv]
  simpa only [Equiv.swap_apply_right] using
    (MvPolynomial.degreeOf_rename_of_injective (p:=P) (Equiv.swap (0 : Fin 5) 1).injective 1)

theorem source_of_root_multiplicity
    (J : SecondJetSupport.Poly (K:=K)) (F : MvPolynomial (Fin 4) K)
    (phi : MvPolynomial (Fin 4) K →+* E) (hker : ∀ P, phi P=0 ↔ F∣P)
    (hH : phi (2*RCN313.polyH K F)≠0)
    (m s B U T : ℕ) (hm : 0<m) (hs : J.degreeOf 1=s)
    (h2s : 2*s≤B) (hBU : B≤U) (hUT : U≤T)
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hroot : ((asS J).map phi).rootMultiplicity (ratio phi F)=m) :
    ∃ S : Source F, S.P=J ∧ S.d=m ∧
      S.flag=SecondJetRelaxedFlag.budgetFlag B U T m s := by
  have hne : (asS J).map phi≠0 := by
    intro hz
    rw [hz,Polynomial.rootMultiplicity_zero] at hroot
    omega
  have hpow : (Polynomial.X-Polynomial.C (ratio phi F))^m ∣ (asS J).map phi := by
    rw [←hroot]
    exact Polynomial.pow_rootMultiplicity_dvd _ _
  have hms : m≤s := by
    have hh := Polynomial.natDegree_le_of_dvd hpow hne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq ((asS_natDegree J).trans hs))
  have hS : ∀ e ∈ J.support, e 1≤s := MvPolynomial.degreeOf_le_iff.mp hs.le
  have hdiv (d : ℕ) (hd : d≤m-1) : F∣helper J F (s-d) d := by
    apply (hker _).mp
    rw [mapped_helper J F phi s d hS hH]
    have hz : ((Polynomial.derivative)^[d] ((asS J).map phi)).eval (ratio phi F)=0 :=
      Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot]; omega)
    rw [hz,mul_zero]
  let S : Source F := {
    P := J, B := B, U := U, T := T, s := s, k := m-1, n0 := s
    hS := hS
    hshape := hshape
    hBU := hBU
    hUT := hUT
    hdn := by omega
    hB := by omega
    hn := by rw [asS_natDegree,hs]
    hdiv := hdiv }
  have hd : S.d=m := by dsimp [S,Source.d]; omega
  exact ⟨S,rfl,hd,by simp only [Source.flag,hd]; rfl⟩

theorem canonical_source_of_root [CharP K 2130706433]
    (J : SecondJetSupport.Poly (K:=K)) (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (m s B U T : ℕ) (hm : 0<m) (hs : J.degreeOf 1=s)
    (h2s : 2*s≤B) (hBU : B≤U) (hUT : U≤T)
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m) :
    ∃ S : Source F, S.P=J ∧ S.d=m ∧ S.flag=SecondJetRelaxedFlag.budgetFlag B U T m s :=
  source_of_root_multiplicity J F (carrierMap F) (carrierMap_zero_iff F)
    (carrier_H_nonzero F hpos hsmall) m s B U T hm hs h2s hBU hUT hshape hroot

end
end ProximityPrize.SubmissionLower.MovingSourceNativeFactor6814
end MergedPart13
section MergedPart14
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerSplit6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN137 WholeSpaceCube6814
open SecondJetCoefficients UniqueCurvatureOwner6814

variable {K E : Type} [Field K] [Field E]
local notation "Poly" => MvPolynomial (Fin 5) K

def UniqueOwner (ev : Poly →+* E) (J P : Poly) : Prop :=
  ∀ D, Irreducible D → D∣P → ev D=0 → Associated D J

theorem unique_owner_remainder (ev : Poly →+* E) (P J : Poly)
    (hP : P≠0) (hJ : Irreducible J) (hu : UniqueOwner ev J P) :
    ∃ e Q, P=J^e*Q ∧ ev Q≠0 := by
  obtain ⟨e,Q,hnot,hEq⟩ := WfDvdMonoid.max_power_factor hP hJ
  have hQ : Q≠0 := by intro hz; apply hP; rw [hEq,hz,mul_zero]
  refine ⟨e,Q,hEq,?_⟩
  intro hz
  obtain ⟨D,hD,hDz⟩ := exists_normalizedFactorSet_zero ev Q hQ hz
  have hd := normalizedFactorSet_spec Q D hD
  have hDP : D∣P := hd.2.trans (by rw [hEq]; exact dvd_mul_left _ _)
  exact hnot (((hu D hd.1 hDP hDz).symm.dvd).trans hd.2)

theorem two_source_owner_split (ev : Poly →+* E) (P Q : Poly)
    (hP : P≠0) (hQ : Q≠0) (hz : ev P=0) :
    ∃ J, Irreducible J ∧ J∣P ∧ ev J=0 ∧
      ((UniqueOwner ev J P ∧ UniqueOwner ev J Q ∧
          (∃ e R, P=J^e*R ∧ ev R≠0) ∧ (∃ e R, Q=J^e*R ∧ ev R≠0)) ∨
        ∃ D, Irreducible D ∧ (D∣P ∨ D∣Q) ∧ ev D=0 ∧ IsRelPrime J D) := by
  classical
  obtain ⟨J,hJ,hJz⟩ := exists_normalizedFactorSet_zero ev P hP hz
  have hj := normalizedFactorSet_spec P J hJ
  refine ⟨J,hj.1,hj.2,hJz,?_⟩
  rcases Classical.em (∃ D, Irreducible D ∧ (D∣P ∨ D∣Q) ∧ ev D=0 ∧ ¬Associated D J) with hex | hex
  · right
    obtain ⟨D,hD,hd,hzD,hnot⟩ := hex
    refine ⟨D,hD,hd,hzD,hj.1.isRelPrime_iff_not_dvd.mpr ?_⟩
    intro hdiv
    exact hnot (hj.1.associated_of_dvd hD hdiv).symm
  · have hp : UniqueOwner ev J P := by
      intro D hD hd hzD
      by_contra hn
      exact hex ⟨D,hD,Or.inl hd,hzD,hn⟩
    have hq : UniqueOwner ev J Q := by
      intro D hD hd hzD
      by_contra hn
      exact hex ⟨D,hD,Or.inr hd,hzD,hn⟩
    exact Or.inl ⟨hp,hq,unique_owner_remainder ev P J hP hj.1 hp,
      unique_owner_remainder ev Q J hQ hj.1 hq⟩

def rootPolynomialMap (phi : MvPolynomial (Fin 4) K →+* E) : Poly →+* Polynomial E :=
  (Polynomial.mapRingHom phi).comp (asS (K:=K)).toRingHom

def rootEvaluation (phi : MvPolynomial (Fin 4) K →+* E) (z : E) : Poly →+* E :=
  (Polynomial.evalRingHom z).comp (rootPolynomialMap phi)

theorem unique_owner_charges
    (phi : MvPolynomial (Fin 4) K →+* E) (z : E) (P J : Poly)
    (hP : P≠0) (hJ : Irreducible J) (hu : UniqueOwner (rootEvaluation phi z) J P)
    (d m : ℕ) (hJne : rootPolynomialMap phi J≠0)
    (hroot : (rootPolynomialMap phi J).rootMultiplicity z=m)
    (hpower : (Polynomial.X-Polynomial.C z)^d ∣ rootPolynomialMap phi P) :
    ∃ e, d≤e*m ∧
      (∀ w : Fin 5 → ℕ, e*weightedTotalDegree w J≤weightedTotalDegree w P) ∧
      e*J.degreeOf 1≤P.degreeOf 1 := by
  obtain ⟨e,Q,hEq,hQroot⟩ := unique_owner_remainder (rootEvaluation phi z) P J hP hJ hu
  have hQ : Q≠0 := by intro hz; apply hQroot; rw [hz,map_zero]
  have hp := hpower
  rw [hEq,map_mul,map_pow] at hp
  have hm := unique_owner_order_le (rootPolynomialMap phi J) (rootPolynomialMap phi Q)
    z d e hJne hQroot hp
  rw [hroot] at hm
  refine ⟨e,hm,?_,?_⟩
  · intro w
    rw [hEq,weight_mul _ _ _ (pow_ne_zero _ hJ.ne_zero) hQ,weight_pow _ _ hJ.ne_zero]
    omega
  · rw [hEq,MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ hJ.ne_zero) hQ,
      MvPolynomial.degreeOf_pow_eq _ _ _ hJ.ne_zero]
    omega

end
end ProximityPrize.SubmissionLower.MovingSourceOwnerSplit6814
end MergedPart14
section MergedPart15
namespace ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN095 SecondJetRelaxedFlag

def copies3 (m : ℕ) : ℕ := (m+2)/m
def parentFlag : FlagDegree := ⟨3504,45,12⟩
def coefficientZ3 : ℕ := 4*131072*(131074*3504)+3*65539*(131073*3504)
def coefficientU3 : ℕ := 4*131072*(131074*45-131072)+3*65539*(131073*45)
def coefficientA3 : ℕ := 4*131072*(131074*11)+3*65539*(131073*12-1)

theorem copies3_le (m e : ℕ) (hm : 0<m) (h : 3≤e*m) : copies3 m≤e := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hm).mpr
  nlinarith

theorem copies3_pos (m : ℕ) (hm : 0<m) : 0<copies3 m := by
  change 0<(m+2)/m
  exact Nat.div_pos (by omega) hm

end ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
end MergedPart15
