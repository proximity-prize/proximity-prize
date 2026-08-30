import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BD
import ProximityPrize.SubmissionLower.RegularColonQuotientProjection
import ProximityPrize.SubmissionLower.ContactOrderBridge
/-
Uncompiled research companion. The two bare imports refer to the sibling
research drafts; rewrite them to the allowed SubmissionLower namespace
only if these files are eventually integrated in that flat archive.

This supplies the contact-to-LowTopRootDivisibility bridge for Y=0,1.
It uses explicit C1 Taylor blocks, not a dimension assumption.
-/
namespace ProximityPrize.SubmissionLower.RegularColonTopSlice
open scoped BigOperators
open RCN119 RCN100
open RCN122 RegularColonQuotientProjection
open ContactOrderBridge
noncomputable section
variable {K : Type*} [Field K]

def azExponent (j z : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 j + Finsupp.single 2 z

theorem coeff_localMonomial (j z b z' : ℕ) :
    MvPolynomial.coeff (azExponent j z) (localMonomial K b 0 z') =
      if b = j ∧ z' = z then 1 else 0 := by
  classical
  have he : (Finsupp.single (0 : Fin 3) b + Finsupp.single 1 0 +
      Finsupp.single 2 z' = azExponent j z) ↔ b = j ∧ z' = z := by
    constructor
    · intro h
      constructor
      · have hh := congrArg (fun d : Fin 3 →₀ ℕ => d 0) h
        simpa [azExponent] using hh
      · have hh := congrArg (fun d : Fin 3 →₀ ℕ => d 2) h
        simpa [azExponent] using hh
    · rintro ⟨rfl, rfl⟩
      simp [azExponent]
  simp only [localMonomial, MvPolynomial.coeff_monomial, he]

theorem coeff_one_seedAffine_mul_localMonomial (u₀ u₁ : K) (z z' : ℕ) :
    MvPolynomial.coeff (azExponent 1 z)
      (seedAffine K u₀ u₁ * localMonomial K 0 0 z') = 0 := by
  classical
  by_contra h
  have hb := coefficientBox_mul K (seedAffine_mem K u₀ u₁)
    (localMonomial_mem K 0 0 z')
  have hzero := (hb (MvPolynomial.mem_support_iff.mpr h)).1
  norm_num [azExponent] at hzero

theorem blockEntry_y_zero {D w L : ℕ} (x u₀ u₁ : K)
    (c : Index D w L) (hy : c.1.val = 0) (n : ℕ) :
    blockEntry K D w L 0 x u₀ u₁ c n =
      (((c.2.2.2.val.choose n : ℕ) : K) * x ^ (c.2.2.2.val - n)) •
        localMonomial K 0 0 c.2.2.1.val := by
  have hr : c.2.1.val = 0 := by have h := c.2.1.isLt; omega
  simp [blockEntry, hy, hr, Fin.sum_univ_succ]

theorem blockEntry_y_one {D w L : ℕ} (x u₀ u₁ : K)
    (c : Index D w L) (hy : c.1.val = 1) (n : ℕ) :
    blockEntry K D w L 0 x u₀ u₁ c (n + 1) =
      (((c.2.2.2.val.choose (n + 1) : ℕ) : K) *
          x ^ (c.2.2.2.val - (n + 1))) •
        (seedAffine K u₀ u₁ * localMonomial K 0 0 c.2.2.1.val) +
      (((c.2.2.2.val.choose n : ℕ) : K) * x ^ (c.2.2.2.val - n)) •
        localMonomial K 1 0 c.2.2.1.val := by
  have hr : c.2.1.val = 0 := by have h := c.2.1.isLt; omega
  simp [blockEntry, hy, hr, Fin.sum_univ_succ]

theorem top_blockEntry_coeff {D w L : ℕ} (x u₀ u₁ : K)
    (c : Index D w L) (j n z : ℕ) (hj : j ≤ 1) (hc : c.1.val ≤ j) :
    MvPolynomial.coeff (azExponent j z)
      (blockEntry K D w L 0 x u₀ u₁ c (n + j)) =
      if c.1.val = j ∧ c.2.2.1.val = z then
        ((c.2.2.2.val.choose n : ℕ) : K) * x ^ (c.2.2.2.val - n)
      else 0 := by
  have hjcases : j = 0 ∨ j = 1 := by omega
  rcases hjcases with rfl | rfl
  · have hy : c.1.val = 0 := by omega
    rw [Nat.add_zero, blockEntry_y_zero x u₀ u₁ c hy]
    by_cases hz : c.2.2.1.val = z <;>
      simp [MvPolynomial.coeff_smul, coeff_localMonomial, hy, hz, smul_eq_mul]
  · have hycases : c.1.val = 0 ∨ c.1.val = 1 := by omega
    rcases hycases with hy | hy
    · rw [blockEntry_y_zero x u₀ u₁ c hy]
      simp [MvPolynomial.coeff_smul, coeff_localMonomial, hy]
    · rw [blockEntry_y_one x u₀ u₁ c hy, MvPolynomial.coeff_add,
        MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
        coeff_one_seedAffine_mul_localMonomial, coeff_localMonomial]
      by_cases hz : c.2.2.1.val = z <;> simp [hy, hz]

theorem extractBlock_top_coeff {D w L : ℕ} (x u₀ u₁ : K)
    (a : Index D w L → K) (j n z : ℕ) (hj : j ≤ 1)
    (htop : ∀ c : Index D w L, j < c.1.val → a c = 0) :
    MvPolynomial.coeff (azExponent j z)
      ((extractBlock K D w L 0 x u₀ u₁ (n + j) a) : Poly K) =
      ∑ c : Index D w L,
        if c.1.val = j ∧ c.2.2.1.val = z then
          a c * (((c.2.2.2.val.choose n : ℕ) : K) * x ^ (c.2.2.2.val - n))
        else 0 := by
  classical
  have heq : ((extractBlock K D w L 0 x u₀ u₁ (n + j) a) : Poly K) =
      ∑ c : Index D w L, a c • blockEntry K D w L 0 x u₀ u₁ c (n + j) := by
    change (((∑ c : Index D w L,
      a c • boundedBlockEntry K D w L 0 x u₀ u₁ c (n + j)) :
        coefficientBox K (min (n + j) L) L 0) : Poly K) = _
    simp [boundedBlockEntry]
  rw [heq, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : j < c.1.val
  · simp [htop c hc]
  · have hc' : c.1.val ≤ j := by omega
    rw [MvPolynomial.coeff_smul, top_blockEntry_coeff x u₀ u₁ c j n z hj hc']
    by_cases h : c.1.val = j ∧ c.2.2.1.val = z <;> simp [h, smul_eq_mul]

theorem taylor_monomial_coeff (x b : K) (e n : ℕ) :
    (Polynomial.taylor x (Polynomial.monomial e b)).coeff n =
      b * (((e.choose n : ℕ) : K) * x ^ (e - n)) := by
  rw [Polynomial.taylor_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  ring

theorem taylor_xSlice_coeff {D w L : ℕ} (x : K)
    (a : Index D w L → K) (j n z : ℕ) :
    (Polynomial.taylor x (xSlice a j z)).coeff n =
      ∑ c : Index D w L,
        if c.1.val = j ∧ c.2.2.1.val = z then
          a c * (((c.2.2.2.val.choose n : ℕ) : K) * x ^ (c.2.2.2.val - n))
        else 0 := by
  classical
  rw [xSlice, map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hc
  · exact taylor_monomial_coeff x (a c) c.2.2.2.val n
  · simp

theorem topSlice_taylor_coeff_eq_block {D w L : ℕ} (x u₀ u₁ : K)
    (a : Index D w L → K) (j n z : ℕ) (hj : j ≤ 1)
    (htop : ∀ c : Index D w L, j < c.1.val → a c = 0) :
    (Polynomial.taylor x (xSlice a j z)).coeff n =
      MvPolynomial.coeff (azExponent j z)
        ((extractBlock K D w L 0 x u₀ u₁ (n + j) a) : Poly K) := by
  rw [taylor_xSlice_coeff, extractBlock_top_coeff x u₀ u₁ a j n z hj htop]

theorem topSlice_root_divisibility_of_blocks_zero {D w L : ℕ}
    (x u₀ u₁ : K) (a : Index D w L → K) (m j z : ℕ)
    (hj : j ≤ 1) (htop : ∀ c : Index D w L, j < c.1.val → a c = 0)
    (hblocks : ∀ r : ℕ, r < m →
      ((extractBlock K D w L 0 x u₀ u₁ r a) : Poly K) = 0) :
    (Polynomial.X - Polynomial.C x) ^ (m - j) ∣ xSlice a j z := by
  apply (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
    (xSlice a j z) x (m - j)).mpr
  intro n hn
  rw [topSlice_taylor_coeff_eq_block x u₀ u₁ a j n z hj htop,
    hblocks (n + j) (by omega), MvPolynomial.coeff_zero]

theorem topSlice_root_divisibility_of_contact {D w L : ℕ}
    (x u₀ u₁ : K) (a : Index D w L → K) (m j z : ℕ)
    (hj : j ≤ 1) (htop : ∀ c : Index D w L, j < c.1.val → a c = 0)
    (ha : ContactAtLeast K x u₀ u₁ m (reconstruct K D w L 0 a)) :
    (Polynomial.X - Polynomial.C x) ^ (m - j) ∣ xSlice a j z :=
  topSlice_root_divisibility_of_blocks_zero x u₀ u₁ a m j z hj htop
    (slopeFree_blocks_zero_of_contactAtLeast K D w L m x u₀ u₁ a ha)

theorem lowTopRootDivisibility_of_contact {D w L : ℕ}
    (V : Submodule K (Index D w L → K))
    (points : Finset K) (mu : K → ℕ) (u₀ u₁ : K → K)
    (hcontact : ∀ a : V, ∀ x ∈ points,
      ContactAtLeast K x (u₀ x) (u₁ x) (mu x) (reconstruct K D w L 0 a.1)) :
    LowTopRootDivisibility V points mu := by
  intro a j hj htop z x hx
  exact topSlice_root_divisibility_of_contact x (u₀ x) (u₁ x) a.1
    (mu x) j z hj htop (hcontact a x hx)

end
end ProximityPrize.SubmissionLower.RegularColonTopSlice
