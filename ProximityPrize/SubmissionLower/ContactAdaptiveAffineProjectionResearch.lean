import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactWeakSeparableSeparatorResearch
import ProximityPrize.SubmissionLower.ContactFlagExactSeparableProjection6543Research
namespace ProximityPrize.SubmissionLower.ContactAdaptiveAffineProjectionResearch
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential
open CoordinateBoxZeroCount
open SeparableShearKaehlerResearch SeparableShearTranscendenceResearch
  GlobalSeparableShearResearch
open ArbitraryRationalProjectionResearch
open ContactFlagExactSeparableProjection6543Research
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
theorem element_transcendental_finite_separable_of_differential_ne_zero
    (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
    (base:SeparableCoordinate K L) (t:L)
    (hdt:D K L t≠0):
    ∃ ht:Transcendental K t,
      (letI:Algebra (RatFunc K) L:=
          (elementEmbedding K L t ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) L)∧
      (letI:Algebra (RatFunc K) L:=
          (elementEmbedding K L t ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) L):=by
  have ht:Transcendental K t:=by
    show ¬ IsAlgebraic K t
    intro halg
    obtain ⟨c,hc⟩:=eq_algebraMap_of_isAlgebraic K L t halg
    apply hdt
    rw [←hc]
    exact (D K L).map_algebraMap c
  let embeddingT:=elementEmbedding K L t ht
  have hfiniteT:
      letI:Algebra (RatFunc K) L:=embeddingT.toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L:=
    finiteDimensional_elementEmbedding K L base.embedding base.finite t ht
  refine ⟨ht,hfiniteT,?_⟩
  have hcriterionBase:=
    isSeparable_iff_span_parameterDifferential K L base.embedding base.finite
  have hcriterionT:=
    isSeparable_iff_span_parameterDifferential K L embeddingT hfiniteT
  have hspanBase:Submodule.span L
      ({D K L (SeparableCoordinate.value K L base)}:Set Ω[L⁄K])=⊤:=by
    have h:=hcriterionBase.mp base.separable
    exact h
  apply hcriterionT.mpr
  have hparamT:parameterDifferential K L embeddingT=D K L t:=by
    unfold parameterDifferential embeddingT
    rw [elementEmbedding_variable]
  rw [hparamT]
  apply top_unique
  rw [←hspanBase]
  apply Submodule.span_le.mpr
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  have htmem:D K L t∈Submodule.span L
      ({D K L (SeparableCoordinate.value K L base)}:Set Ω[L⁄K]):=by
    rw [hspanBase]
    trivial
  obtain ⟨b,hb⟩:=Submodule.mem_span_singleton.mp htmem
  have hb0:b≠0:=by
    intro hzero
    apply hdt
    rw [←hb,hzero,zero_smul]
  apply Submodule.mem_span_singleton.mpr
  refine ⟨b⁻¹,?_⟩
  rw [←hb,smul_smul,inv_mul_cancel₀ hb0,one_smul]
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
variable {I:Type*} [Fintype I]
variable (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
variable (r z:∀ i,E i)
variable (W:∀ i,
  Finset (CoordinatePlaceClassification.NormalizedValuation K (E i)))
theorem exists_common_exact_finite_separable_affine_adaptive
    (base:∀ i,SeparableCoordinate K (E i))
    (hactive:∀ i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
    ∃ a:K,a≠0∧∀ i,
      ∃ ht:Transcendental K (r i+a • z i),
        (letI:Algebra (RatFunc K) (E i):=
            (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc K) (E i))∧
        (letI:Algebra (RatFunc K) (E i):=
            (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc K) (E i))∧
        (∀ v∈W i,v.val (r i+a • z i)=
          max (v.val (r i)) (v.val (z i))):=by
  let J:=I ⊕ Sigma fun i:I => {v//v∈W i}
  let Bad:J → K → Prop
    | Sum.inl i,a => D K (E i) (r i)+a • D K (E i) (z i)=0
    | Sum.inr iv,a => iv.2.1.val (r iv.1+a • z iv.1) <
        max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
  have hsingle:∀ j {a b},Bad j a → Bad j b → a=b:=by
    intro j a b ha hb
    rcases j with i | ⟨i,v⟩
    · by_cases hdz:D K (E i) (z i)=0
      · have hdr:D K (E i) (r i)≠0:=
          (hactive i).resolve_right (fun hn => hn hdz)
        change D K (E i) (r i)+a • D K (E i) (z i)=0 at ha
        exfalso
        apply hdr
        simpa only [hdz,smul_zero,add_zero] using ha
      · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
          hdz ha hb
    · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
  obtain ⟨a,ha0,havoid⟩:=
    exists_nonzero_avoiding_finite_subsingleton Bad hsingle
  refine ⟨a,ha0,fun i => ?_⟩
  have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
    exact havoid (Sum.inl i)
  have hD:D K (E i) (r i+a • z i)≠0:=by
    rw [map_add,(D K (E i)).map_smul]
    exact hdiff
  obtain ⟨ht,hfinite,hsep⟩:=
    element_transcendental_finite_separable_of_differential_ne_zero
      K (E i) (base i) (r i+a • z i) hD
  refine ⟨ht,hfinite,hsep,?_⟩
  intro v hv
  have hnotlt:=havoid (Sum.inr ⟨i,⟨v,hv⟩⟩)
  have hupper:=v.val.map_add (r i) (a • z i)
  have haz:v.val (a • z i)=v.val (z i):=by
    letI:v.val.IsTrivialOn K:=v.property.2
    rw [Algebra.smul_def,map_mul,
      Valuation.IsTrivialOn.eq_one a ha0,one_mul]
  rw [haz] at hupper
  exact le_antisymm hupper (le_of_not_gt hnotlt)
theorem exists_common_exact_finite_separable_affine_adaptive_avoiding_one
    (Extra:K → Prop)
    (hextra:∀ {a b},Extra a → Extra b → a=b)
    (base:∀ i,SeparableCoordinate K (E i))
    (hactive:∀ i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
    ∃ a:K,a≠0∧¬ Extra a∧∀ i,
      ∃ ht:Transcendental K (r i+a • z i),
        (letI:Algebra (RatFunc K) (E i):=
            (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc K) (E i))∧
        (letI:Algebra (RatFunc K) (E i):=
            (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc K) (E i))∧
        (∀ v∈W i,v.val (r i+a • z i)=
          max (v.val (r i)) (v.val (z i))):=by
  let J:=Unit ⊕ (I ⊕ Sigma fun i:I => {v//v∈W i})
  let Bad:J → K → Prop
    | Sum.inl _,a => Extra a
    | Sum.inr (Sum.inl i),a =>
        D K (E i) (r i)+a • D K (E i) (z i)=0
    | Sum.inr (Sum.inr iv),a => iv.2.1.val (r iv.1+a • z iv.1) <
        max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
  have hsingle:∀ j {a b},Bad j a → Bad j b → a=b:=by
    intro j a b ha hb
    rcases j with _ | i | ⟨i,v⟩
    · exact hextra ha hb
    · by_cases hdz:D K (E i) (z i)=0
      · have hdr:D K (E i) (r i)≠0:=
          (hactive i).resolve_right (fun hn => hn hdz)
        change D K (E i) (r i)+a • D K (E i) (z i)=0 at ha
        exfalso
        apply hdr
        simpa only [hdz,smul_zero,add_zero] using ha
      · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
          hdz ha hb
    · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
  obtain ⟨a,ha0,havoid⟩:=
    exists_nonzero_avoiding_finite_subsingleton Bad hsingle
  refine ⟨a,ha0,havoid (Sum.inl ()),fun i => ?_⟩
  have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
    exact havoid (Sum.inr (Sum.inl i))
  have hD:D K (E i) (r i+a • z i)≠0:=by
    rw [map_add,(D K (E i)).map_smul]
    exact hdiff
  obtain ⟨ht,hfinite,hsep⟩:=
    element_transcendental_finite_separable_of_differential_ne_zero
      K (E i) (base i) (r i+a • z i) hD
  refine ⟨ht,hfinite,hsep,?_⟩
  intro v hv
  have hnotlt:=havoid (Sum.inr (Sum.inr ⟨i,⟨v,hv⟩⟩))
  have hupper:=v.val.map_add (r i) (a • z i)
  have haz:v.val (a • z i)=v.val (z i):=by
    letI:v.val.IsTrivialOn K:=v.property.2
    rw [Algebra.smul_def,map_mul,
      Valuation.IsTrivialOn.eq_one a ha0,one_mul]
  rw [haz] at hupper
  exact le_antisymm hupper (le_of_not_gt hnotlt)
end FiniteFamily
end
end ProximityPrize.SubmissionLower.ContactAdaptiveAffineProjectionResearch
