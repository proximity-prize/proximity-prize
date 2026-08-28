import ProximityPrize.SubmissionLower.BCHKSReedSolomonCofactor6400
import ProximityPrize.SubmissionLower.BCHKSFrobeniusBivariatePencil6400

/-!
# Production instantiation of bivariate Frobenius separation

This module rewrites the concrete sparse Reed--Solomon low-stack kernel in
the two independent parameters required by
`BCHKSFrobeniusBivariatePencil6400`.  Many bad diagonal challenges then force
all independent source/target specializations to be singular.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- Extend one production error row from the NTT domain to the whole sextic
field. -/
noncomputable def score6400ErrorSource
    (e : IRSProfile.Index → IRSProfile.Field) :
    IRSProfile.Field → IRSProfile.Field :=
  Function.extend IRSProfile.domain e 0

@[simp]
theorem score6400ErrorSource_domain
    (e : IRSProfile.Index → IRSProfile.Field) (i : IRSProfile.Index) :
    score6400ErrorSource e (IRSProfile.domain i) = e i := by
  exact IRSProfile.domain.injective.extend_apply e 0 i

@[simp]
theorem koalaSexticFrobenius_apply (x : IRSProfile.Field) :
    koalaSexticFrobenius x = x ^ 2130706433 := by
  rw [koalaSexticFrobenius, frobeniusEquiv_def]

/-- On the sparse source image, the earlier affine extension is the affine
combination of the two separately extended rows. -/
theorem score6400AffineErrorSource_eq_affine_on_pairSupport
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field)
    (z x : IRSProfile.Field)
    (hx : x ∈ (pairSupport e₀ e₁).map IRSProfile.domain) :
    score6400AffineErrorSource e₀ e₁ z x =
      score6400ErrorSource e₀ x + z * score6400ErrorSource e₁ x := by
  obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
  subst x
  simp only [score6400AffineErrorSource_domain,
    score6400ErrorSource_domain]

/-- The concrete conjugate target is affine in the independent Frobenius
parameter, with the real diagonal specialization `w=z^p`. -/
theorem koalaSexticFrobenius_affineError_eq_on_pairSupport
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field)
    (z x : IRSProfile.Field)
    (hx : x ∈ (pairSupport e₀ e₁).map IRSProfile.domain) :
    koalaSexticFrobenius (score6400AffineErrorSource e₀ e₁ z x) =
      koalaSexticFrobenius (score6400ErrorSource e₀ x) +
        z ^ 2130706433 *
          koalaSexticFrobenius (score6400ErrorSource e₁ x) := by
  rw [score6400AffineErrorSource_eq_affine_on_pairSupport e₀ e₁ z x hx,
    map_add, map_mul]
  simp only [koalaSexticFrobenius_apply]

/-- One concrete sparse bad witness produces the diagonal low-stack kernel
in the exact bivariate-pencil normal form. -/
theorem score6400_lowStackKernel_frobenius_shape_of_sparse_mcaBad
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hbad : MCABad IRSProfile.baseCode e₀ e₁ 185364 z)
    (hnoncancel : z ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁))
    (hlarge : 54292 < (pairSupport e₀ e₁).card) :
    LinearMap.ker
      (lowStackRelationMap
        ((pairSupport e₀ e₁).map IRSProfile.domain)
        (fun x ↦ score6400ErrorSource e₀ x +
          z * score6400ErrorSource e₁ x)
        (fun x ↦ koalaSexticFrobenius (score6400ErrorSource e₀ x) +
          z ^ 2130706433 *
            koalaSexticFrobenius (score6400ErrorSource e₁ x))
        ((pairSupport e₀ e₁).card - 54292)) ≠ ⊥ := by
  let S := (pairSupport e₀ e₁).map IRSProfile.domain
  let h := (pairSupport e₀ e₁).card - 54292
  let source := score6400AffineErrorSource e₀ e₁ z
  let target : IRSProfile.Field → IRSProfile.Field := fun x ↦
    koalaSexticFrobenius (source x)
  have hconcrete : LinearMap.ker
      (lowStackRelationMap S source target h) ≠ ⊥ := by
    simpa only [S, h, source, target] using
      score6400_lowStackKernel_of_sparse_mcaBad
        e₀ e₁ z hsparse hbad hnoncancel hlarge
  have hmap : lowStackRelationMap S source target h =
      lowStackRelationMap S
        (fun x ↦ score6400ErrorSource e₀ x +
          z * score6400ErrorSource e₁ x)
        (fun x ↦ koalaSexticFrobenius (score6400ErrorSource e₀ x) +
          z ^ 2130706433 *
            koalaSexticFrobenius (score6400ErrorSource e₁ x)) h := by
    apply LinearMap.ext
    intro q
    funext x
    change q.1.1.eval x.1 *
          score6400AffineErrorSource e₀ e₁ z x.1 +
        q.2.1.eval x.1 *
          koalaSexticFrobenius
            (score6400AffineErrorSource e₀ e₁ z x.1) =
      q.1.1.eval x.1 *
          (score6400ErrorSource e₀ x.1 +
            z * score6400ErrorSource e₁ x.1) +
        q.2.1.eval x.1 *
          (koalaSexticFrobenius (score6400ErrorSource e₀ x.1) +
            z ^ 2130706433 *
              koalaSexticFrobenius (score6400ErrorSource e₁ x.1))
    rw [koalaSexticFrobenius_affineError_eq_on_pairSupport
        e₀ e₁ z x.1 (by simpa only [S] using x.2),
      score6400AffineErrorSource_eq_affine_on_pairSupport
        e₀ e₁ z x.1 (by simpa only [S] using x.2)]
  rw [hmap] at hconcrete
  simpa only [S, h] using hconcrete

/-- If more than the diagonal determinant degree many noncancelling sparse
bad slopes share the same error pair, every independent source/target
specialization has a nontrivial low-stack kernel. -/
theorem score6400_lowStackKernel_all_parameters_of_many_sparse_mcaBad
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hbad : ∀ z ∈ Gamma,
      MCABad IRSProfile.baseCode e₀ e₁ 185364 z)
    (hnoncancel : ∀ z ∈ Gamma,
      z ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁))
    (hlarge : 54292 < (pairSupport e₀ e₁).card)
    (hGamma :
      ((pairSupport e₀ e₁).card - 54292) +
          2130706433 * ((pairSupport e₀ e₁).card - 54292) <
        Gamma.card)
    (z w : IRSProfile.Field) :
    LinearMap.ker
      (lowStackRelationMap
        ((pairSupport e₀ e₁).map IRSProfile.domain)
        (fun x ↦ score6400ErrorSource e₀ x +
          z * score6400ErrorSource e₁ x)
        (fun x ↦ koalaSexticFrobenius (score6400ErrorSource e₀ x) +
          w * koalaSexticFrobenius (score6400ErrorSource e₁ x))
        ((pairSupport e₀ e₁).card - 54292)) ≠ ⊥ := by
  have hsupport : (pairSupport e₀ e₁).card ≤ 76780 := by
    change (pairSupport e₀ e₁).card ≤
      Fintype.card IRSProfile.Index - 185364 at hsparse
    norm_num [IRSProfile.Index] at hsparse
    exact hsparse
  have hhp : (pairSupport e₀ e₁).card - 54292 < 2130706433 := by
    omega
  apply lowStack_kernel_of_many_frobenius_kernels
    ((pairSupport e₀ e₁).map IRSProfile.domain) Gamma
    (score6400ErrorSource e₀) (score6400ErrorSource e₁)
    (fun x ↦ koalaSexticFrobenius (score6400ErrorSource e₀ x))
    (fun x ↦ koalaSexticFrobenius (score6400ErrorSource e₁ x))
    ((pairSupport e₀ e₁).card - 54292) 2130706433
  · norm_num
  · exact hhp
  · exact hGamma
  · intro y hy
    exact score6400_lowStackKernel_frobenius_shape_of_sparse_mcaBad
      e₀ e₁ y hsparse (hbad y hy) (hnoncancel y hy) hlarge

/-- Extend a field-valued function to the rational function field along the
coefficient embedding. -/
noncomputable def ratFuncPointwiseLift
    {F : Type} [Field F] (f : F → F) : RatFunc F → RatFunc F :=
  Function.extend (algebraMap F (RatFunc F))
    (fun x ↦ algebraMap F (RatFunc F) (f x)) 0

@[simp]
theorem ratFuncPointwiseLift_algebraMap
    {F : Type} [Field F] (f : F → F) (x : F) :
    ratFuncPointwiseLift f (algebraMap F (RatFunc F) x) =
      algebraMap F (RatFunc F) (f x) := by
  exact (algebraMap F (RatFunc F)).injective.extend_apply _ _ x

/-- Extend a generic affine target `target₀ + W*target₁` to the rational
function field. -/
noncomputable def ratFuncAffinePointwiseLift
    {F : Type} [Field F] (target₀ target₁ : F → F) :
    RatFunc F → RatFunc F :=
  Function.extend (algebraMap F (RatFunc F))
    (fun x ↦ algebraMap F (RatFunc F) (target₀ x) +
      (RatFunc.X : RatFunc F) *
        algebraMap F (RatFunc F) (target₁ x)) 0

@[simp]
theorem ratFuncAffinePointwiseLift_algebraMap
    {F : Type} [Field F] (target₀ target₁ : F → F) (x : F) :
    ratFuncAffinePointwiseLift target₀ target₁
        (algebraMap F (RatFunc F) x) =
      algebraMap F (RatFunc F) (target₀ x) +
        (RatFunc.X : RatFunc F) *
          algebraMap F (RatFunc F) (target₁ x) := by
  exact (algebraMap F (RatFunc F)).injective.extend_apply _ _ x

/-- The large diagonal family now produces the exact Frobenius amplitude
atom consumed by the checked cofactor/resultant finish. -/
noncomputable def score6400_frobeniusAmplitudeAtom_of_many_sparse_mcaBad
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hbad : ∀ z ∈ Gamma,
      MCABad IRSProfile.baseCode e₀ e₁ 185364 z)
    (hnoncancel : ∀ z ∈ Gamma,
      z ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁))
    (hlarge : 54292 < (pairSupport e₀ e₁).card)
    (hGamma :
      ((pairSupport e₀ e₁).card - 54292) +
          2130706433 * ((pairSupport e₀ e₁).card - 54292) <
        Gamma.card) :
    Σ z₀ : {z // z ∈ Gamma},
      FrobeniusAmplitudeAtom
        ((pairSupport e₀ e₁).map IRSProfile.domain)
        (score6400ErrorSource e₀) (score6400ErrorSource e₁)
        koalaSexticFrobenius z₀.1
        ((pairSupport e₀ e₁).card - 54292) := by
  classical
  let T := pairSupport e₀ e₁
  let S := T.map IRSProfile.domain
  let h := T.card - 54292
  let error₀ := score6400ErrorSource e₀
  let error₁ := score6400ErrorSource e₁
  let target₀ : IRSProfile.Field → IRSProfile.Field := fun x ↦
    koalaSexticFrobenius (error₀ x)
  let target₁ : IRSProfile.Field → IRSProfile.Field := fun x ↦
    koalaSexticFrobenius (error₁ x)
  have hGammaPos : 0 < Gamma.card := by omega
  let z₀ : IRSProfile.Field :=
    Classical.choose (Finset.card_pos.mp hGammaPos)
  have hz₀ : z₀ ∈ Gamma :=
    Classical.choose_spec (Finset.card_pos.mp hGammaPos)
  let source : IRSProfile.Field → IRSProfile.Field := fun x ↦
    error₀ x + z₀ * error₁ x
  have hsupport : T.card ≤ 76780 := by
    change T.card ≤ Fintype.card IRSProfile.Index - 185364 at hsparse
    norm_num [IRSProfile.Index] at hsparse
    exact hsparse
  have hlargeT : 54292 < T.card := by
    simpa only [T] using hlarge
  have hScardExact : S.card = T.card := by
    simp only [S, Finset.card_map]
  have hScard : h ≤ S.card := by
    rw [hScardExact]
    dsimp only [h]
    omega
  have hhcap : h ≤ 22488 := by
    dsimp only [h]
    omega
  have hdecomp : 54292 + h = T.card := by
    dsimp only [h]
    exact Nat.add_sub_of_le hlargeT.le
  have hstrict : 3 * h < S.card := by
    rw [hScardExact, ← hdecomp]
    omega
  have hTcard : h < Gamma.card := by
    have hhGamma : h + 2130706433 * h < Gamma.card := by
      simpa only [h, T] using hGamma
    exact (Nat.le_add_right h (2130706433 * h)).trans_lt hhGamma
  have hsource : ∀ x ∈ S, source x ≠ 0 := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
    subst x
    simp only [source, error₀, error₁, score6400ErrorSource_domain]
    exact affine_error_ne_zero_on_support_of_not_cancellation
      e₀ e₁ T (fun _ hi ↦ hi) z₀ (hnoncancel z₀ hz₀) i hi
  let genericSource := ratFuncPointwiseLift source
  let genericTarget := ratFuncAffinePointwiseLift target₀ target₁
  have hkernels : ∀ w ∈ Gamma,
      LinearMap.ker (lowStackRelationMap S source
        (fun x ↦ target₀ x + w * target₁ x) h) ≠ ⊥ := by
    intro w hw
    simpa only [S, T, source, error₀, error₁, target₀, target₁, h] using
      score6400_lowStackKernel_all_parameters_of_many_sparse_mcaBad
        e₀ e₁ Gamma hsparse hbad hnoncancel hlarge hGamma z₀ w
  let scroll := scrollAtom_of_many_affine_lowStack_kernels
    S Gamma source target₀ target₁ genericSource genericTarget h
    hTcard hScard hsource
    (fun x hx ↦ by simp only [genericSource,
      ratFuncPointwiseLift_algebraMap])
    (fun x hx ↦ by simp only [genericTarget,
      ratFuncAffinePointwiseLift_algebraMap])
    hstrict hkernels
  have hfixed : ∀ x ∈ S, koalaSexticFrobenius x = x := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
    rw [← hix]
    exact koalaSexticFrobenius_fixed_domain i
  let atom := frobeniusAmplitudeAtom_of_scroll
    S source target₀ target₁ error₀ error₁ koalaSexticFrobenius z₀ h
    scroll hScard hsource (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) hfixed
  exact ⟨⟨z₀, hz₀⟩, by
    simpa only [S, T, error₀, error₁, h] using atom⟩

end ProximityPrize.SubmissionLower
