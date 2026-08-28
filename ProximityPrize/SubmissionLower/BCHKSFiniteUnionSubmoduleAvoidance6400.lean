import ProximityPrize.Benchmark.TargetLower

/-!
# Avoiding a finite union of proper subspaces

Over a finite field, at most `|K|` proper linear subspaces cannot cover a
nontrivial finite-dimensional vector space.  The proof counts nonzero vectors
in each subspace, retaining the shared zero instead of paying for it once per
subspace.  This endpoint is useful when one seed must avoid one linear kernel
at every point of the score-64 evaluation domain.
-/

open scoped BigOperators

namespace ProximityPrize.SubmissionLower
namespace BCHKSFiniteUnionSubmoduleAvoidance6400

set_option autoImplicit false

/-- At most `|K|` proper subspaces of a nontrivial finite `K`-space leave a
common point outside all of them. -/
theorem exists_outside_finite_union_submodules6400
    {α K M : Type} [Field K] [Fintype K] [AddCommGroup M] [Module K M]
    [Finite M] [Nontrivial M]
    (s : Finset α) (p : α → Submodule K M)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Fintype.card K) :
    ∃ x : M, ∀ i ∈ s, x ∉ p i := by
  classical
  letI := Fintype.ofFinite M
  letI : DecidableEq M := Classical.decEq M
  let q := Fintype.card K
  let d := Module.finrank K M
  let nz (i : α) := Finset.univ.filter fun x : M => x ∈ p i ∧ x ≠ 0
  let covered := insert (0 : M) (s.biUnion nz)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := Module.finrank_pos
  have hnz (i : α) (hi : i ∈ s) :
      (nz i).card ≤ q ^ (d - 1) - 1 := by
    let allp := Finset.univ.filter fun x : M => x ∈ p i
    have hzero : (0 : M) ∈ allp := by simp [allp]
    have hnz_eq : nz i = allp.erase 0 := by
      ext x
      simp [nz, allp, and_comm]
    rw [hnz_eq, Finset.card_erase_of_mem hzero]
    have hcard : allp.card = Fintype.card (p i) := by
      symm
      exact Fintype.card_ofFinset allp (by simp [allp])
    have hcardpow :
        Fintype.card (p i) = q ^ Module.finrank K (p i) := by
      simpa [q] using (Module.card_eq_pow_finrank (K := K) (V := p i))
    rw [hcard, hcardpow]
    exact Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq)
        (Nat.le_sub_one_of_lt (Submodule.finrank_lt (hp i hi)))) 1
  have hcovered : covered.card < Fintype.card M := by
    have hbi :
        (s.biUnion nz).card ≤ s.card * (q ^ (d - 1) - 1) := by
      calc
        (s.biUnion nz).card ≤ ∑ i ∈ s, (nz i).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ s, (q ^ (d - 1) - 1) :=
          Finset.sum_le_sum fun i hi => hnz i hi
        _ = s.card * (q ^ (d - 1) - 1) := by simp
    have hmul :
        s.card * (q ^ (d - 1) - 1) ≤ q * (q ^ (d - 1) - 1) :=
      Nat.mul_le_mul_right _ hs
    have hpow : q ^ d = q * q ^ (d - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hd]
      simp [pow_succ, Nat.mul_comm]
    have hcardM : Fintype.card M = q ^ d := by
      simpa [q, d] using (Module.card_eq_pow_finrank (K := K) (V := M))
    rw [hcardM, hpow]
    calc
      covered.card ≤ (s.biUnion nz).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ s.card * (q ^ (d - 1) - 1) + 1 :=
        Nat.add_le_add_right hbi 1
      _ ≤ q * (q ^ (d - 1) - 1) + 1 :=
        Nat.add_le_add_right hmul 1
      _ < q * q ^ (d - 1) := by
        have hpos : 0 < q ^ (d - 1) :=
          pow_pos (Nat.zero_lt_of_lt hq) _
        have hqmul : q ≤ q * q ^ (d - 1) := by
          simpa using Nat.mul_le_mul_left q hpos
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := covered) (t := Finset.univ) (by simpa using hcovered)
  refine ⟨x, fun i hi hxi => hx ?_⟩
  by_cases hx0 : x = 0
  · simp [covered, hx0]
  · simp only [covered, Finset.mem_insert]
    exact Or.inr
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp [nz, hxi, hx0]⟩)

/-- Kernel form of the same avoidance theorem. -/
theorem exists_simultaneously_nonzero_linear_maps6400
    {α K M N : Type} [Field K] [Fintype K]
    [AddCommGroup M] [Module K M] [Finite M] [Nontrivial M]
    [AddCommGroup N] [Module K N]
    (s : Finset α) (f : α → M →ₗ[K] N)
    (hf : ∀ i ∈ s, f i ≠ 0) (hs : s.card ≤ Fintype.card K) :
    ∃ x : M, ∀ i ∈ s, f i x ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := exists_outside_finite_union_submodules6400
    s (fun i => LinearMap.ker (f i)) (by
      intro i hi htop
      apply hf i hi
      apply LinearMap.ker_eq_top.mp
      exact htop) hs
  refine ⟨x, ?_⟩
  intro i hi hzero
  exact hx i hi (by simpa only [LinearMap.mem_ker] using hzero)

end BCHKSFiniteUnionSubmoduleAvoidance6400
end ProximityPrize.SubmissionLower
