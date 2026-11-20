import ProximityPrize.SubmissionLower.Koala6844VirtualHighSelectedResidual
import ProximityPrize.SubmissionLower.Koala6844ActiveGerm


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical
open Polynomial Koala6831Intrinsic Koala6844Normalization RCN135 RCN136 RCN132

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1100000

variable {K E I : Type} [Field K] [Field E]

def mappedPolynomialFamily (embed : K →+* E) (Q : K → Polynomial K) :
    E → Polynomial E :=
  fun g => (Q (Function.invFun embed g)).map embed

def mappedScalarFamily (embed : K →+* E) (a : K → K) : E → E :=
  fun g => embed (a (Function.invFun embed g))

@[simp] theorem mappedPolynomialFamily_apply_map
    (embed : K →+* E) (Q : K → Polynomial K) (g : K) :
    mappedPolynomialFamily embed Q (embed g) = (Q g).map embed := by
  unfold mappedPolynomialFamily
  rw [Function.leftInverse_invFun embed.injective]

@[simp] theorem mappedScalarFamily_apply_map
    (embed : K →+* E) (a : K → K) (g : K) :
    mappedScalarFamily embed a (embed g) = embed (a g) := by
  unfold mappedScalarFamily
  rw [Function.leftInverse_invFun embed.injective]

def mappedNodes (embed : K →+* E) (x : I ↪ K) : I ↪ E :=
  ⟨embed ∘ x, embed.injective.comp x.injective⟩

theorem graphSpecialize_map_coefficients (embed : K →+* E) (Q : Polynomial K)
    (g h : K) (F : Carrier K) :
    graphSpecialize (Q.map embed) (embed g) (embed h) (MvPolynomial.map embed F) =
      (graphSpecialize Q g h F).map embed := by
  have commute : (graphSpecialize (Q.map embed) (embed g) (embed h)).comp
      (MvPolynomial.map embed) =
      (Polynomial.mapRingHom embed).comp (graphSpecialize Q g h) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [graphSpecialize]
    · intro i
      fin_cases i <;> simp [graphSpecialize, Matrix.cons_val_two, Matrix.cons_val_three]
  exact DFunLike.congr_fun commute F

theorem eval_rationalSurface_graph (Q : Polynomial E) (g h : E) (F : Carrier E) :
    MvPolynomial.eval (polynomialGraphSurfacePoint (algebraMap (Polynomial E) (RationalCoefficients E))
      Q g h) (rationalSurfaceMap E F) =
      algebraMap (Polynomial E) (RationalCoefficients E) (graphSpecialize Q g h F) :=
  eval_polynomialGraphSurfacePoint _ Q g h F

variable [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

private theorem mapped_normalized_degree
    (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (A : Finset K) (hs : A ⊆ data.seeds) :
    ∀ g ∈ A.image embed, (mappedPolynomialFamily embed data.normalized g).natDegree ≤
      w + data.d0.natDegree - affineDegree data.A0 := by
  intro t ht
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ht
  rw [mappedPolynomialFamily_apply_map, Polynomial.natDegree_map]
  exact data.normalized_degree g (hs hg)

private theorem mapped_normalized_injOn
    (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (A : Finset K) (hs : A ⊆ data.seeds) :
    Set.InjOn (mappedPolynomialFamily embed data.normalized) (↑(A.image embed) : Set E) := by
  intro u hu v hv eq
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hv
  rw [mappedPolynomialFamily_apply_map, mappedPolynomialFamily_apply_map] at eq
  exact congrArg embed (Koala6844ActiveGerm.normalized_injOn data (hs hg) (hs hh)
    (Polynomial.map_injective embed embed.injective eq))

private theorem mapped_normalized_agreements
    (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (A : Finset K) (hs : A ⊆ data.seeds) :
    ∀ g ∈ A.image embed, agreement ≤ (nodes.filter fun i =>
      (mappedPolynomialFamily embed data.normalized g).eval (mappedNodes embed x i) =
        embed (data.fixedWord i)).card := by
  intro t ht
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ht
  refine (data.normalized_agreements g (hs hg)).trans (Finset.card_le_card ?_)
  intro i hi
  obtain ⟨hin, he⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨hin, ?_⟩
  rw [mappedPolynomialFamily_apply_map]
  change ((data.normalized g).map embed).eval (embed (x i)) = embed (data.fixedWord i)
  rw [Polynomial.eval_map_apply, he]

theorem mapped_normalized_family
    (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (A : Finset K) (hs : A ⊆ data.seeds) :
    (A.image embed).card = A.card ∧
      (∀ g ∈ A.image embed, (mappedPolynomialFamily embed data.normalized g).natDegree ≤
        w + data.d0.natDegree - affineDegree data.A0) ∧
      Set.InjOn (mappedPolynomialFamily embed data.normalized) (↑(A.image embed) : Set E) ∧
      ∀ g ∈ A.image embed, agreement ≤ (nodes.filter fun i =>
        (mappedPolynomialFamily embed data.normalized g).eval (mappedNodes embed x i) =
          embed (data.fixedWord i)).card :=
  ⟨Finset.card_image_of_injective _ embed.injective,
    mapped_normalized_degree data embed A hs, mapped_normalized_injOn data embed A hs,
    mapped_normalized_agreements data embed A hs⟩

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

