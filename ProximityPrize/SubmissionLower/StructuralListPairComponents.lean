import ProximityPrize.SubmissionLower.StructuralListPairFiltration

set_option Elab.async false
set_option maxRecDepth 6000

namespace StructuralList

open CJ0 CJ0_4 MvPolynomial Finset
open scoped BigOperators

noncomputable section

/-- A finite family of pairwise incomparable prime ideals admits separate coordinates. -/
theorem primeSeparators {ι R : Type*} [Fintype ι] [CommRing R]
    (P : ι → Ideal R) (hp : ∀ i, (P i).IsPrime)
    (hincomp : ∀ i j, i ≠ j → ¬ P j ≤ P i) :
    ∃ g : ι → R, ∀ i, g i ∉ P i ∧ ∀ j, j ≠ i → g i ∈ P j := by
  classical
  have hchoose (i j : ι) (hij : j ≠ i) : ∃ q, q ∈ P j ∧ q ∉ P i := by
    by_contra! h
    exact hincomp i j hij.symm (fun _ hq => h _ hq)
  let q (i j : ι) := if hj : j ≠ i then (hchoose i j hj).choose else 1
  have hspec (i j : ι) (hj : j ≠ i) : q i j ∈ P j ∧ q i j ∉ P i := by
    simpa only [q, dite_eq_left hj] using (hchoose i j hj).choose_spec
  let g (i : ι) := ∏ j ∈ univ.erase i, q i j
  refine ⟨g, fun i => ⟨?_, ?_⟩⟩
  · let := hp i
    intro h
    obtain ⟨j, hj, hq⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact (hspec i j (mem_erase.mp hj).1).2 hq
  · intro j hj
    have hj' : j ∈ univ.erase i := mem_erase.mpr ⟨hj, mem_univ _⟩
    exact (P j).prod_mem hj' (hspec i j hj).1

/-- A family of independent coordinate values uses their sum of dimensions. -/
theorem sum_finrank_le_of_coordinates {𝕜 ι V : Type*} [Field 𝕜] [Fintype ι]
    [AddCommGroup V] [Module 𝕜 V] [Module.Finite 𝕜 V]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module 𝕜 (M i)]
    (W : ∀ i, Submodule 𝕜 (M i)) [∀ i, Module.Finite 𝕜 (W i)]
    (f : V →ₗ[𝕜] ∀ i, M i)
    (hs : ∀ (i) (y : W i), ∃ x : V, f x i = y.val ∧ ∀ j, j ≠ i → f x j = 0) :
    (∑ i, Module.finrank 𝕜 (W i)) ≤ Module.finrank 𝕜 V := by
  classical
  let incl : (∀ i, W i) →ₗ[𝕜] (∀ i, M i) :=
    LinearMap.pi fun i => (W i).subtype.comp (LinearMap.proj i)
  have hincl (y : ∀ i, W i) : incl y ∈ LinearMap.range f := by
    choose x hx hz using (fun i => hs i (y i))
    refine ⟨∑ i, x i, ?_⟩
    ext j
    change f (∑ i, x i) j = (y j).val
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
    · exact hx j
    · intro i _ hi
      exact hz i j hi.symm
    · intro hm
      exact (hm (mem_univ _)).elim
  let incl' := incl.codRestrict (LinearMap.range f) hincl
  have hi : Function.Injective incl' := by
    intro y z h
    funext i
    exact Subtype.ext (congrArg (fun x : LinearMap.range f => x.val i) h)
  rw [← Module.finrank_pi_fintype]
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans f.finrank_range_le


def componentBand (P : Ideal (InitialRing 2)) (a d e : ℕ) :
    Submodule Geo (InitialRing 2 ⧸ P) :=
  (bandSpace a d e).map (Ideal.Quotient.mkₐ Geo P).toLinearMap

instance (P : Ideal (InitialRing 2)) (a d e : ℕ) : Module.Finite Geo (componentBand P a d e) :=
  Module.Finite.map _ _

def cutQuotientTo (T : Chart 2) (Q : InitialRing 2) (P : Ideal (InitialRing 2))
    (hE : sourceIdeal T ≤ P) (hQ : Q ∈ P) :
    ((InitialRing 2 ⧸ sourceIdeal T) ⧸ cutIdeal T Q) →ₐ[Geo] (InitialRing 2 ⧸ P) := by
  let φ := Ideal.Quotient.liftₐ (sourceIdeal T) (Ideal.Quotient.mkₐ Geo P)
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hE hx))
  refine Ideal.Quotient.liftₐ (cutIdeal T Q) φ ?_
  intro x hx
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hφ : φ (Ideal.Quotient.mk (sourceIdeal T) Q) = Ideal.Quotient.mk P Q := by
    rfl
  rw [map_mul, hφ, Ideal.Quotient.eq_zero_iff_mem.mpr hQ, zero_mul]

theorem cutQuotientTo_apply (T : Chart 2) (Q : InitialRing 2) (P : Ideal (InitialRing 2))
    (hE : sourceIdeal T ≤ P) (hQ : Q ∈ P) (z : InitialRing 2) :
    cutQuotientTo T Q P hE hQ (Ideal.Quotient.mk (cutIdeal T Q) (Ideal.Quotient.mk (sourceIdeal T) z)) =
      Ideal.Quotient.mk P z := by
  rfl

/-- Source component bands fit jointly in the cut filtration after multiplying by separators. -/
theorem componentBands_le_cutBand {ι : Type*} [Fintype ι] (T : Chart 2) (Q : InitialRing 2)
    (P : ι → Ideal (InitialRing 2)) (hP : ∀ i, (P i).IsPrime)
    (hE : ∀ i, sourceIdeal T ≤ P i) (hQ : ∀ i, Q ∈ P i)
    (g : ι → InitialRing 2) (hg : ∀ i, g i ∉ P i ∧ ∀ j, j ≠ i → g i ∈ P j)
    (a d e : ℕ) (u v w : ι → ℕ)
    (hcap : ∀ i, u i + (g i).totalDegree ≤ a ∧ v i + (g i).weightedTotalDegree Fin.val ≤ d ∧
      w i + (g i).degreeOf (Fin.last 2) ≤ e) :
    (∑ i, Module.finrank Geo (componentBand (P i) (u i) (v i) (w i))) ≤
      Module.finrank Geo (cutBand T Q a d e) := by
  let μ (i : ι) := LinearMap.mulLeft Geo (Ideal.Quotient.mk (P i) (g i))
  let W (i : ι) := (componentBand (P i) (u i) (v i) (w i)).map (μ i)
  have hEq (i : ι) : Module.finrank Geo (componentBand (P i) (u i) (v i) (w i)) = Module.finrank Geo (W i) := by
    let := hP i
    let f := (μ i).domRestrict (componentBand (P i) (u i) (v i) (w i))
    have hμ : Function.Injective f := by
      intro x y h
      exact Subtype.ext (mul_left_cancel₀ (show Ideal.Quotient.mk (P i) (g i) ≠ 0 from
        mt Ideal.Quotient.eq_zero_iff_mem.mp (hg i).1) h)
    rw [show W i = LinearMap.range f from (LinearMap.range_domRestrict _ _).symm]
    exact LinearEquiv.finrank_eq (LinearEquiv.ofInjective f hμ)
  let f : cutBand T Q a d e →ₗ[Geo] ∀ i, InitialRing 2 ⧸ P i :=
    LinearMap.pi fun i => (cutQuotientTo T Q (P i) (hE i) (hQ i)).toLinearMap.domRestrict _
  have hcover (i : ι) (y : W i) : ∃ z : cutBand T Q a d e, f z i = y.val ∧ ∀ j, j ≠ i → f z j = 0 := by
    obtain ⟨x, hx, hxy⟩ := y.property
    obtain ⟨p, hp, hpx⟩ := hx
    have hgband : g i ∈ bandSpace (g i).totalDegree ((g i).weightedTotalDegree Fin.val)
        ((g i).degreeOf (Fin.last 2)) := mem_bandSpace.mpr ⟨le_rfl, le_rfl, le_rfl⟩
    have hband : g i * p ∈ bandSpace a d e := by
      obtain ⟨ha, hd, he⟩ := hcap i
      rw [mul_comm]
      exact bandSpace_mono ha hd he (mul_mem_bandSpace hp hgband)
    let z := Ideal.Quotient.mk (cutIdeal T Q) (Ideal.Quotient.mk (sourceIdeal T) (g i * p))
    have hz : z ∈ cutBand T Q a d e := ⟨_, ⟨_, hband, rfl⟩, rfl⟩
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · change cutQuotientTo T Q (P i) (hE i) (hQ i) z = y.val
      rw [cutQuotientTo_apply, map_mul]
      change Ideal.Quotient.mk (P i) p = x at hpx
      rw [hpx]
      exact hxy
    · intro j hj
      change cutQuotientTo T Q (P j) (hE j) (hQ j) z = 0
      rw [cutQuotientTo_apply, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr ((hg i).2 j hj), zero_mul]
  simp only [hEq]
  exact sum_finrank_le_of_coordinates W f hcover

end

end StructuralList
