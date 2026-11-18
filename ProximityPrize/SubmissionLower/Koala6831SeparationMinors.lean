import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace ProximityPrize.SubmissionLower.Koala6831Separation

open scoped BigOperators Matrix

variable {F ι : Type*} [Field F]

private theorem row_span_of_independent_columns {m : ℕ} (M : ι → Fin m → F)
    (h : LinearIndependent F (fun j i ↦ M i j)) :
    Submodule.span F (Set.range M) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨f, hne, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  let b := Pi.basisFun F (Fin m)
  let z (j : Fin m) : F := f (b j)
  have hrepr (v : Fin m → F) : (∑ j, z j * v j) = f v := by
    have he := congrArg f (b.sum_repr v)
    simpa [z, b, map_sum, map_smul, smul_eq_mul, mul_comm] using he
  have hsum : ∑ j, z j • (fun i ↦ M i j) = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [hrepr]
    exact hker (Submodule.subset_span ⟨i, rfl⟩)
  have hz (j : Fin m) := Fintype.linearIndependent_iff.mp h z hsum j
  apply hne
  apply LinearMap.ext
  intro v
  simp only [LinearMap.zero_apply, ← hrepr, hz, zero_mul, Finset.sum_const_zero]

theorem exists_nonzero_minor_of_independent_columns {m : ℕ}
    (cols : Fin m → ι → F) (h : LinearIndependent F cols) :
    ∃ keys : Fin m → ι, (Matrix.of fun i j ↦ cols j (keys i)).det ≠ 0 := by
  classical
  let row (i : ι) (j : Fin m) := cols j i
  have hspan := row_span_of_independent_columns row h
  obtain ⟨s, select, _, hs, hli⟩ := exists_linearIndependent' F row
  have : Finite s := hli.finite
  let _ : Fintype s := Fintype.ofFinite s
  let b : Module.Basis s F (Fin m → F) := Module.Basis.mk hli (by rw [hs, hspan])
  have hcard : Fintype.card (Fin m) = Fintype.card s :=
    (Module.finrank_eq_card_basis (Pi.basisFun F (Fin m))).symm.trans
      (Module.finrank_eq_card_basis b)
  let e := Fintype.equivOfCardEq hcard
  refine ⟨select ∘ e, ?_⟩
  let N : Matrix (Fin m) (Fin m) F := Matrix.of fun i j ↦ cols j (select (e i))
  have hN : LinearIndependent F N.row := hli.comp e e.injective
  exact (Matrix.isUnit_iff_isUnit_det N).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hN)
    |>.ne_zero

theorem exists_relation_of_singular_minors {m : ℕ}
    (cols : Fin m → ι → F)
    (h : ∀ keys : Fin m → ι, (Matrix.of fun i j ↦ cols j (keys i)).det = 0) :
    ∃ v : Fin m → F, v ≠ 0 ∧ ∑ j, v j • cols j = 0 := by
  classical
  have hnot : ¬ LinearIndependent F cols := fun hind ↦ by
    obtain ⟨keys, hk⟩ := exists_nonzero_minor_of_independent_columns cols hind
    exact hk (h keys)
  rw [Fintype.linearIndependent_iff] at hnot
  push Not at hnot
  obtain ⟨v, hv, i, hi⟩ := hnot
  exact ⟨v, fun he ↦ hi (by rw [he, Pi.zero_apply]), hv⟩

theorem mem_span_of_singular_augmented_minors {m : ℕ}
    (cols : Fin (m + 1) → ι → F) (rhs : ι → F) (slot : Fin (m + 1))
    (hind : LinearIndependent F (cols ∘ slot.succAbove))
    (h : ∀ keys : Fin (m + 1) → ι,
      ((Matrix.of fun i j ↦ cols j (keys i)).updateCol slot (fun i ↦ rhs (keys i))).det = 0) :
    rhs ∈ Submodule.span F (Set.range (cols ∘ slot.succAbove)) := by
  classical
  by_contra hout
  have hv := (hind.option hout).comp (finSuccEquiv' slot) (Equiv.injective _)
  obtain ⟨keys, hkeys⟩ := exists_nonzero_minor_of_independent_columns _ hv
  apply hkeys
  convert h keys using 2
  ext i j
  refine Fin.succAboveCases slot ?_ (fun k ↦ ?_) j
  · simp
  · simp [Fin.succAbove_ne]

end ProximityPrize.SubmissionLower.Koala6831Separation
