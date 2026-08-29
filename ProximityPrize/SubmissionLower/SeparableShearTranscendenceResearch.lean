import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.SeparableShearKaehlerResearch

/-!
# Transcendence of a separating additive shear

This research module closes the logical gap which occurs before one may
construct the rational-function embedding at `R + Z`.  If the finite
projection at `R` is nonseparable and the finite projection at `Z` is
separable, then `R + Z` is transcendental over an algebraically closed base.

The proof is deliberately differential rather than circular: it uses only
the already-existing embeddings at `R` and `Z`.  Nonseparability forces
`dR = 0`, separability makes `dZ` span the one-dimensional differential
module, and an algebraic element over the algebraically closed base would be
a scalar and hence have zero differential.
-/

namespace ProximityPrize.SubmissionLower.SeparableShearTranscendenceResearch

open scoped Classical
open KaehlerDifferential
open SeparableShearKaehlerResearch

noncomputable section

set_option maxHeartbeats 2000000

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- An element algebraic over an algebraically closed base field is a base
scalar.  This generic form avoids depending on an actual-coordinate model. -/
theorem eq_algebraMap_of_isAlgebraic [IsAlgClosed K]
    (s : L) (hs : IsAlgebraic K s) :
    ∃ c : K, algebraMap K L c = s := by
  let S : IntermediateField K L := IntermediateField.adjoin K {s}
  letI : Algebra.IsAlgebraic K S :=
    IntermediateField.isAlgebraic_adjoin_simple hs.isIntegral
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := S)).2
      (⟨s, IntermediateField.mem_adjoin_simple_self K s⟩ : S)
  refine ⟨c, ?_⟩
  have hcast := congrArg (algebraMap S L) hc
  simpa only [IntermediateField.algebraMap_apply,
    IntermediateField.coe_algebraMap_apply] using hcast

/-- Before constructing an embedding at the shear, `R + Z` is already known
to be transcendental.  The hypotheses mention only the independently valid
embeddings at `R` and `Z`, so the statement is not circular. -/
theorem transcendental_add_of_not_isSeparable_isSeparable [IsAlgClosed K]
    (embeddingR embeddingZ : RatFunc K →ₐ[K] L)
    (hfiniteR :
      letI : Algebra (RatFunc K) L := embeddingR.toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hfiniteZ :
      letI : Algebra (RatFunc K) L := embeddingZ.toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hnotsepR :
      letI : Algebra (RatFunc K) L := embeddingR.toRingHom.toAlgebra
      ¬ Algebra.IsSeparable (RatFunc K) L)
    (hsepZ :
      letI : Algebra (RatFunc K) L := embeddingZ.toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) L) :
    Transcendental K
      (embeddingR (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) +
        embeddingZ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) := by
  let dR := parameterDifferential K L embeddingR
  let dZ := parameterDifferential K L embeddingZ
  have hcriterionR :=
    isSeparable_iff_span_parameterDifferential K L embeddingR hfiniteR
  have hcriterionZ :=
    isSeparable_iff_span_parameterDifferential K L embeddingZ hfiniteZ
  have hspanR_ne : Submodule.span L ({dR} : Set Ω[L⁄K]) ≠ ⊤ := by
    intro htop
    exact hnotsepR (hcriterionR.mpr htop)
  have hspanZ : Submodule.span L ({dZ} : Set Ω[L⁄K]) = ⊤ :=
    hcriterionZ.mp hsepZ
  have hdR : dR = 0 := by
    by_contra hdR0
    apply hspanR_ne
    apply top_unique
    rw [← hspanZ]
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    have hdR_mem : dR ∈ Submodule.span L ({dZ} : Set Ω[L⁄K]) := by
      rw [hspanZ]
      trivial
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hdR_mem
    have hb0 : b ≠ 0 := by
      intro hzero
      apply hdR0
      rw [← hb, hzero, zero_smul]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b⁻¹, ?_⟩
    rw [← hb, smul_smul, inv_mul_cancel₀ hb0, one_smul]
  have hdZ : dZ ≠ 0 := by
    intro hdZ
    apply hspanR_ne
    simpa only [hdR, hdZ] using hspanZ
  show ¬ IsAlgebraic K _
  intro halg
  obtain ⟨c, hc⟩ := eq_algebraMap_of_isAlgebraic K L _ halg
  apply hdZ
  have hD : D K L
      (embeddingR (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) +
        embeddingZ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) = 0 := by
    rw [← hc]
    exact (D K L).map_algebraMap c
  have hD' : parameterDifferential K L embeddingR +
      parameterDifferential K L embeddingZ = 0 := by
    change D K L
        (embeddingR (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) +
      D K L
        (embeddingZ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) = 0
    simpa only [map_add] using hD
  unfold dR at hdR
  unfold dZ
  rw [hdR, zero_add] at hD'
  exact hD'

end

end ProximityPrize.SubmissionLower.SeparableShearTranscendenceResearch
