import ProximityPrize.SubmissionLower.Koala6844VirtualHighCoefficientTransport
import ProximityPrize.SubmissionLower.Koala6844VirtualHighSurfaceSource
import ProximityPrize.SubmissionLower.Koala6844VirtualHighExceptions


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical
open Polynomial Koala6831Intrinsic Koala6844Normalization RCN132

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {K E I : Type} [Field K] [Field E]

def rationalSeedEmbedding (embed : K →+* E) : K →+* RationalCoefficients E :=
  ((algebraMap (Polynomial E) (RationalCoefficients E)).comp Polynomial.C).comp embed

theorem seedPoint_eq_mapped_graph (embed : K →+* E) (p : ℕ)
    (Q : K → Polynomial K) (g : K) :
    seedPoint (rationalSeedEmbedding embed) p (fun a => fractionValue ((Q a).map embed)) g =
      polynomialGraphSurfacePoint (algebraMap (Polynomial E) (RationalCoefficients E))
        ((Q g).map embed) (embed g) ((embed g)^p) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact (map_pow ((algebraMap (Polynomial E) (RationalCoefficients E)).comp Polynomial.C)
      (embed g) p).symm

theorem mem_surfaceSeeds_iff_graph (embed : K →+* E) (p : ℕ)
    (Q : K → Polynomial K) (A : Finset K) (F : Carrier E) (g : K) :
    g ∈ surfaceSeeds (rationalSeedEmbedding embed) p
        (fun a => fractionValue ((Q a).map embed)) A F ↔
      g ∈ A ∧ graphSpecialize ((Q g).map embed) (embed g) ((embed g)^p) F = 0 := by
  rw [surfaceSeeds, Finset.mem_filter, seedPoint_eq_mapped_graph, eval_rationalSurface_graph]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro h
    exact IsFractionRing.injective (Polynomial E) (RationalCoefficients E)
      (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

def regularSurfaceSeeds (embed : K →+* E) (p : ℕ) (Q : K → Polynomial K)
    (A : Finset K) (F : Carrier E) : Finset K :=
  surfaceSeeds (rationalSeedEmbedding embed) p (fun a => fractionValue ((Q a).map embed)) A F \
  surfaceSeeds (rationalSeedEmbedding embed) p (fun a => fractionValue ((Q a).map embed)) A
    (implicitRegularity F)

theorem mem_regularSurfaceSeeds_iff_graph (embed : K →+* E) (p : ℕ)
    (Q : K → Polynomial K) (A : Finset K) (F : Carrier E) (g : K) :
    g ∈ regularSurfaceSeeds embed p Q A F ↔
      g ∈ A ∧ graphSpecialize ((Q g).map embed) (embed g) ((embed g)^p) F = 0 ∧
      graphSpecialize ((Q g).map embed) (embed g) ((embed g)^p) (implicitRegularity F) ≠ 0 := by
  rw [regularSurfaceSeeds, Finset.mem_sdiff, mem_surfaceSeeds_iff_graph,
    mem_surfaceSeeds_iff_graph]
  tauto

theorem regularSurfaceSeeds_subset (embed : K →+* E) (p : ℕ)
    (Q : K → Polynomial K) (A : Finset K) (F : Carrier E) :
    regularSurfaceSeeds embed p Q A F ⊆ A :=
  fun g hg => ((mem_regularSurfaceSeeds_iff_graph embed p Q A F g).mp hg).1

variable [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

theorem mapped_regular_trimmed_graphs
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (p first : ℕ) (A : Finset K) (hA : A ⊆ D.seeds)
    (hσ : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^p)
    (F : Carrier E) (V W : Carrier K)
    (reduced : K → Polynomial K) (scale : K → K)
    (hdivisor : ∀ g ∈ D.seeds,
      graphSpecialize (D.normalized g) g (σ g) V = D.d0 * D.d1)
    (htrim : ∀ g ∈ D.seeds, graphSpecialize (D.normalized g) g (σ g) W =
      Polynomial.C (scale g) * graphSpecialize (D.normalized g) g (σ g) V * reduced g)
    (hdegree : ∀ g ∈ D.seeds, (reduced g).natDegree ≤ first) :
    let seeds := (regularSurfaceSeeds embed p D.normalized A F).image embed
    let selected := mappedPolynomialFamily embed D.normalized
    let trim := mappedPolynomialFamily embed reduced
    let scalars := mappedScalarFamily embed scale
    let V' := MvPolynomial.map embed V
    let W' := MvPolynomial.map embed W
    ∀ g ∈ seeds,
      graphSpecialize (selected g) g (g^p) F = 0 ∧
      graphSpecialize (selected g) g (g^p) (V' * implicitRegularity F) ≠ 0 ∧
      graphSpecialize (selected g) g (g^p) W' =
        Polynomial.C (scalars g) * graphSpecialize (selected g) g (g^p) V' * trim g ∧
      (trim g).natDegree ≤ first := by
  intro seeds selected trim scalars V' W' g hg
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨haA, root, regular⟩ := (mem_regularSurfaceSeeds_iff_graph embed p D.normalized A F a).mp ha
  have hseed := hA haA
  have selected_eq : selected (embed a) = (D.normalized a).map embed :=
    mappedPolynomialFamily_apply_map embed _ a
  have trim_eq : trim (embed a) = (reduced a).map embed :=
    mappedPolynomialFamily_apply_map embed _ a
  have scale_eq : scalars (embed a) = embed (scale a) :=
    mappedScalarFamily_apply_map embed _ a
  have hV : graphSpecialize (selected (embed a)) (embed a) ((embed a)^p) V' ≠ 0 := by
    rw [selected_eq, ← hσ a hseed]
    change graphSpecialize ((D.normalized a).map embed) (embed a) (embed (σ a))
      (MvPolynomial.map embed V) ≠ 0
    rw [graphSpecialize_map_coefficients, hdivisor a hseed]
    exact Polynomial.map_ne_zero (mul_ne_zero D.d0_ne D.d1_ne)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rwa [selected_eq]
  · rw [map_mul, mul_ne_zero_iff, selected_eq] at ⊢
    exact ⟨selected_eq ▸ hV, regular⟩
  · rw [selected_eq, trim_eq, scale_eq, ← hσ a hseed]
    change graphSpecialize ((D.normalized a).map embed) (embed a) (embed (σ a))
      (MvPolynomial.map embed W) = Polynomial.C (embed (scale a)) *
      graphSpecialize ((D.normalized a).map embed) (embed a) (embed (σ a))
        (MvPolynomial.map embed V) * (reduced a).map embed
    simp only [graphSpecialize_map_coefficients, htrim a hseed, Polynomial.map_mul,
      Polynomial.map_C]
  · rw [trim_eq, Polynomial.natDegree_map]
    exact hdegree a hseed

theorem mapped_graph_nonzero_of_original
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (p : ℕ) (A : Finset K) (hA : A ⊆ D.seeds)
    (hσ : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^p) (H : Carrier K)
    (hnonzero : ∀ g ∈ D.seeds, graphSpecialize (D.normalized g) g (σ g) H ≠ 0) :
    ∀ g ∈ A.image embed, graphSpecialize (mappedPolynomialFamily embed D.normalized g)
      g (g^p) (MvPolynomial.map embed H) ≠ 0 := by
  intro u hu
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hu
  rw [mappedPolynomialFamily_apply_map, ← hσ g (hA hg), graphSpecialize_map_coefficients]
  exact Polynomial.map_ne_zero (hnonzero g (hA hg))

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

