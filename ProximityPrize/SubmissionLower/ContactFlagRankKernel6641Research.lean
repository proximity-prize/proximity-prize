import ProximityPrize.Benchmark.TargetLower

import ProximityPrize.SubmissionLower.LocalMathlib_Algebra_MvPolynomial_NoZeroDivisors

/-! .








 -/

namespace ProximityPrize.SubmissionLower.ContactFlagRankKernel6641Research

open scoped BigOperators Pointwise

noncomputable section

variable (K : Type*) [Field K]

abbrev Poly := MvPolynomial (Fin 3) K

def slopeDifference : Poly K := MvPolynomial.X 0 - MvPolynomial.X 1

private def plusVariables (i : Fin 3) : Poly K :=
  if i = 0 then MvPolynomial.X 0 + MvPolynomial.X 1 else MvPolynomial.X i

private def minusVariables (i : Fin 3) : Poly K :=
  if i = 0 then MvPolynomial.X 0 - MvPolynomial.X 1 else MvPolynomial.X i

def shiftPlus : Poly K →ₐ[K] Poly K := MvPolynomial.aeval (plusVariables K)

def shiftMinus : Poly K →ₐ[K] Poly K := MvPolynomial.aeval (minusVariables K)

theorem shiftMinus_comp_shiftPlus :
    (shiftMinus K).comp (shiftPlus K) = AlgHom.id K (Poly K) := by
  ext i
  fin_cases i <;> simp [shiftPlus, shiftMinus, plusVariables, minusVariables]

theorem shiftPlus_comp_shiftMinus :
    (shiftPlus K).comp (shiftMinus K) = AlgHom.id K (Poly K) := by
  ext i
  fin_cases i <;> simp [shiftPlus, shiftMinus, plusVariables, minusVariables]

@[simp] theorem shiftMinus_shiftPlus (f : Poly K) :
    shiftMinus K (shiftPlus K f) = f :=
  DFunLike.congr_fun (shiftMinus_comp_shiftPlus K) f

@[simp] theorem shiftPlus_shiftMinus (f : Poly K) :
    shiftPlus K (shiftMinus K f) = f :=
  DFunLike.congr_fun (shiftPlus_comp_shiftMinus K) f

@[simp] theorem shiftPlus_slopeDifference :
    shiftPlus K (slopeDifference K) = MvPolynomial.X 0 := by
  simp [slopeDifference, shiftPlus, plusVariables]

@[simp] theorem shiftMinus_X_zero :
    shiftMinus K (MvPolynomial.X 0) = slopeDifference K := by
  simp [shiftMinus, minusVariables, slopeDifference]

theorem slopeDifference_ne_zero : slopeDifference K ≠ 0 := by
  intro h
  have hh := congrArg (shiftPlus K) h
  simpa using hh

/-- . -/
def monomialRemainder (d : Fin 3 →₀ ℕ) : Poly K →ₗ[K] Poly K where
  toFun f := f.modMonomial d
  map_add' f g := by
    ext e
    by_cases he : d ≤ e
    · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
    · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
  map_smul' c f := by
    ext e
    by_cases he : d ≤ e
    · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
    · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]

/-- . -/
def contactJet (h : ℕ) : Poly K →ₗ[K] Poly K :=
  (monomialRemainder K (Finsupp.single 0 h)).comp (shiftPlus K).toLinearMap

theorem contactJet_apply (h : ℕ) (f : Poly K) :
    contactJet K h f = (shiftPlus K f).modMonomial (Finsupp.single 0 h) := rfl

/-- . -/
theorem contactJet_eq_zero_iff (h : ℕ) (f : Poly K) :
    contactJet K h f = 0 ↔ slopeDifference K ^ h ∣ f := by
  rw [contactJet_apply,
    ← MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero,
    ← MvPolynomial.X_pow_eq_monomial]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨shiftMinus K q, ?_⟩
    have hh := congrArg (shiftMinus K) hq
    simpa only [shiftMinus_shiftPlus, map_mul, map_pow, shiftMinus_X_zero] using hh
  · rintro ⟨q, rfl⟩
    exact ⟨shiftPlus K q, by simp⟩

theorem contactJet_mul_slopeDifference (h : ℕ) (q : Poly K) :
    contactJet K h (slopeDifference K ^ h * q) = 0 :=
  (contactJet_eq_zero_iff K h _).2 ⟨q, rfl⟩

/-- . -/
theorem contactJet_eq_zero_iff_coeff (h : ℕ) (f : Poly K) :
    contactJet K h f = 0 ↔
      ∀ d : Fin 3 →₀ ℕ, d 0 < h → MvPolynomial.coeff d (shiftPlus K f) = 0 := by
  constructor
  · intro hf d hd
    have hnot : ¬ Finsupp.single (0 : Fin 3) h ≤ d := by
      intro hle
      have hh := hle 0
      simp only [Finsupp.single_eq_same] at hh
      omega
    have hh := congrArg (MvPolynomial.coeff d) hf
    simpa [contactJet_apply, MvPolynomial.coeff_modMonomial_of_not_le _ hnot] using hh
  · intro hf
    ext d
    by_cases hle : Finsupp.single (0 : Fin 3) h ≤ d
    · simp [contactJet_apply, MvPolynomial.coeff_modMonomial_of_le _ hle]
    · have hd : d 0 < h := by
        by_contra hnot
        apply hle
        intro i
        by_cases hi : i = 0
        · subst i
          simp only [Finsupp.single_eq_same]
          omega
        · simp [Finsupp.single_eq_of_ne hi]
      simp [contactJet_apply, MvPolynomial.coeff_modMonomial_of_not_le _ hle, hf d hd]

def boxExponents (M L s : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {d | d 0 ≤ M ∧ d 0 + d 1 + d 2 ≤ L ∧ d 1 ≤ s}

/-- . -/
def coefficientBox (M L s : ℕ) : Submodule K (Poly K) :=
  MvPolynomial.restrictSupport K (boxExponents M L s)

theorem mem_coefficientBox_iff (M L s : ℕ) (f : Poly K) :
    f ∈ coefficientBox K M L s ↔
      ∀ d ∈ f.support, d 0 ≤ M ∧ d 0 + d 1 + d 2 ≤ L ∧ d 1 ≤ s := by
  rfl

theorem coefficientBox_mul
    {M L s M' L' s' : ℕ} {f g : Poly K}
    (hf : f ∈ coefficientBox K M L s)
    (hg : g ∈ coefficientBox K M' L' s') :
    f * g ∈ coefficientBox K (M + M') (L + L') (s + s') := by
  have hset : boxExponents M L s + boxExponents M' L' s' ⊆
      boxExponents (M + M') (L + L') (s + s') := by
    rintro _ ⟨d, hd, e, he, rfl⟩
    rcases hd with ⟨hd0, hdTotal, hd1⟩
    rcases he with ⟨he0, heTotal, he1⟩
    simp only [boxExponents, Set.mem_setOf_eq, Finsupp.add_apply]
    omega
  apply MvPolynomial.restrictSupport_mono (R := K) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hf hg

theorem slopeDifference_mem_coefficientBox :
    slopeDifference K ∈ coefficientBox K 1 1 1 := by
  apply (coefficientBox K 1 1 1).sub_mem
  · change MvPolynomial.monomial (Finsupp.single 0 1) (1 : K) ∈ _
    apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
    left
    simp [boxExponents]
  · change MvPolynomial.monomial (Finsupp.single 1 1) (1 : K) ∈ _
    apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
    left
    simp [boxExponents]

theorem slopeDifference_pow_mem_coefficientBox (h : ℕ) :
    slopeDifference K ^ h ∈ coefficientBox K h h h := by
  induction h with
  | zero =>
      simp only [pow_zero]
      change MvPolynomial.monomial 0 (1 : K) ∈ _
      apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
      left
      simp [boxExponents]
  | succ h ih =>
      simpa only [pow_succ] using coefficientBox_mul K ih (slopeDifference_mem_coefficientBox K)

theorem slopeDifference_mul_mem_coefficientBox
    {M L s h : ℕ} (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s)
    {q : Poly K} (hq : q ∈ coefficientBox K (M - h) (L - h) (s - h)) :
    slopeDifference K ^ h * q ∈ coefficientBox K M L s := by
  have hh := coefficientBox_mul K (slopeDifference_pow_mem_coefficientBox K h) hq
  simpa only [Nat.add_sub_of_le hM, Nat.add_sub_of_le hL, Nat.add_sub_of_le hs] using hh

private def exponentTriple (i j z : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 z

@[simp] private theorem exponentTriple_zero (i j z : ℕ) :
    exponentTriple i j z 0 = i := by simp [exponentTriple]

@[simp] private theorem exponentTriple_one (i j z : ℕ) :
    exponentTriple i j z 1 = j := by simp [exponentTriple]

@[simp] private theorem exponentTriple_two (i j z : ℕ) :
    exponentTriple i j z 2 = z := by simp [exponentTriple]

private theorem exponentTriple_eta (d : Fin 3 →₀ ℕ) :
    exponentTriple (d 0) (d 1) (d 2) = d := by
  ext i
  fin_cases i <;> simp

/-- .
 -/
private theorem finPair_heq_of_val_eq
    {n a b : ℕ} {i j : Fin n} {u : Fin a} {v : Fin b}
    (hab : a = b) (hij : i.val = j.val) (huv : u.val = v.val) :
    HEq (i, u) (j, v) := by
  subst b
  have hi : i = j := Fin.ext hij
  have hu : u = v := Fin.ext huv
  cases hi
  cases hu
  rfl

private theorem finSigma_heq_of_val_eq
    {n : ℕ} {a b : Fin n → ℕ}
    {i j : Fin n} {u : Fin (a i)} {v : Fin (b j)}
    (hab : a = b) (hij : i.val = j.val) (huv : u.val = v.val) :
    HEq (⟨i, u⟩ : (k : Fin n) × Fin (a k))
      (⟨j, v⟩ : (k : Fin n) × Fin (b k)) := by
  subst b
  have hi : i = j := Fin.ext hij
  subst j
  have hu : u = v := Fin.ext huv
  subst v
  rfl

abbrev BoxIndex (M L s : ℕ) :=
  (i : Fin (M + 1)) ×
    (j : Fin (s + 1)) × Fin (L + 1 - i.val - j.val)

def boxExponentsEquivIndex (M L s : ℕ) :
    boxExponents M L s ≃ BoxIndex M L s where
  toFun d :=
    ⟨⟨d.val 0, by
        rcases d.property with ⟨hM, hL, hs⟩
        omega⟩,
      ⟨⟨d.val 1, by
        rcases d.property with ⟨hM, hL, hs⟩
        omega⟩,
      ⟨d.val 2, by
        rcases d.property with ⟨hM, hL, hs⟩
        change d.val 2 < L + 1 - d.val 0 - d.val 1
        omega⟩⟩⟩
  invFun q :=
    ⟨exponentTriple q.1.val q.2.1.val q.2.2.val, by
      have hi := q.1.isLt
      have hj := q.2.1.isLt
      have hz := q.2.2.isLt
      simp only [boxExponents, Set.mem_setOf_eq, exponentTriple_zero,
        exponentTriple_one, exponentTriple_two]
      omega⟩
  left_inv d := Subtype.ext (exponentTriple_eta d.val)
  right_inv q := by
    rcases q with ⟨⟨i, hi⟩, ⟨⟨j, hj⟩, ⟨z, hz⟩⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      exact exponentTriple_zero i j z
    · dsimp only
      apply @finSigma_heq_of_val_eq (s + 1)
        (fun k ↦ L + 1 - (exponentTriple i j z) 0 - k.val)
        (fun k ↦ L + 1 - i - k.val) _ _ _ _
      · funext k
        simp only [exponentTriple_zero]
      · exact exponentTriple_one i j z
      · exact exponentTriple_two i j z

instance boxExponentsFintype (M L s : ℕ) : Fintype (boxExponents M L s) :=
  Fintype.ofEquiv (BoxIndex M L s) (boxExponentsEquivIndex M L s).symm

instance coefficientBoxFinite (M L s : ℕ) :
    Module.Finite K (coefficientBox K M L s) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boxExponents M L s))

theorem coefficientBox_finrank (M L s : ℕ) :
    Module.finrank K (coefficientBox K M L s) =
      ∑ i : Fin (M + 1),
        ∑ j : Fin (s + 1), (L + 1 - i.val - j.val) := by
  change Module.finrank K (MvPolynomial.restrictSupport K (boxExponents M L s)) = _
  rw [Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport K (boxExponents M L s))]
  rw [Fintype.card_congr (boxExponentsEquivIndex M L s)]
  simp [BoxIndex, Fintype.card_sigma]

theorem coefficientBox_finrank_of_le (M L s : ℕ) (hML : M ≤ L) :
    Module.finrank K (coefficientBox K M L s) =
      ∑ i : Fin (M + 1),
        ∑ j : Fin (s + 1), (L + 1 - i.val - j.val) := by
  exact coefficientBox_finrank K M L s

/-- . -/
def multiplyIntoBox {M L s h : ℕ} (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    coefficientBox K (M - h) (L - h) (s - h) →ₗ[K]
      coefficientBox K M L s where
  toFun q := ⟨slopeDifference K ^ h * q.val,
    slopeDifference_mul_mem_coefficientBox K hM hL hs q.property⟩
  map_add' q r := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' c q := by
    apply Subtype.ext
    simp [mul_smul_comm]

theorem multiplyIntoBox_injective
    {M L s h : ℕ} (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    Function.Injective (multiplyIntoBox K hM hL hs) := by
  intro q r heq
  apply Subtype.ext
  have hh : slopeDifference K ^ h * q.val = slopeDifference K ^ h * r.val :=
    congrArg Subtype.val heq
  exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh

/-- . -/
def blockJet (M L s h : ℕ) : coefficientBox K M L s →ₗ[K] Poly K :=
  (contactJet K h).comp (coefficientBox K M L s).subtype

def kernelEmbedding {M L s h : ℕ}
    (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    coefficientBox K (M - h) (L - h) (s - h) →ₗ[K]
      LinearMap.ker (blockJet K M L s h) :=
  LinearMap.codRestrict (LinearMap.ker (blockJet K M L s h))
    (multiplyIntoBox K hM hL hs) (fun q => by
      change contactJet K h (slopeDifference K ^ h * q.val) = 0
      exact contactJet_mul_slopeDifference K h q.val)

theorem kernelEmbedding_injective {M L s h : ℕ}
    (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    Function.Injective (kernelEmbedding K hM hL hs) := by
  intro q r heq
  apply multiplyIntoBox_injective K hM hL hs
  exact congrArg Subtype.val heq

/-- . -/
theorem blockJet_rank_add_quotient_finrank_le {M L s h : ℕ}
    (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    Module.finrank K (LinearMap.range (blockJet K M L s h)) +
        Module.finrank K (coefficientBox K (M - h) (L - h) (s - h)) ≤
      Module.finrank K (coefficientBox K M L s) := by
  have hker := LinearMap.finrank_le_finrank_of_injective
    (kernelEmbedding_injective K hM hL hs)
  have hsum := (blockJet K M L s h).finrank_range_add_finrank_ker
  omega

/-- .
 -/
theorem blockJet_rank_le_triangle_difference {M L s h : ℕ}
    (hML : M ≤ L) (hM : h ≤ M) (hs : h ≤ s) :
    Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
      (∑ i : Fin (M + 1),
          ∑ j : Fin (s + 1), (L + 1 - i.val - j.val)) -
        (∑ i : Fin (M - h + 1),
          ∑ j : Fin (s - h + 1), (L - h + 1 - i.val - j.val)) := by
  have hineq := blockJet_rank_add_quotient_finrank_le K hM (hM.trans hML) hs
  rw [coefficientBox_finrank_of_le K M L s hML,
    coefficientBox_finrank_of_le K (M - h) (L - h) (s - h)
      (Nat.sub_le_sub_right hML h)] at hineq
  omega

/-- .
 -/
theorem blockJet_rank_le_input (M L s h : ℕ) (hML : M ≤ L) :
    Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
      ∑ i : Fin (M + 1),
        ∑ j : Fin (s + 1), (L + 1 - i.val - j.val) := by
  have hsum := (blockJet K M L s h).finrank_range_add_finrank_ker
  rw [coefficientBox_finrank_of_le K M L s hML] at hsum
  omega

theorem coefficientBox_finrank_range (M L s : ℕ) (hML : M ≤ L) :
    Module.finrank K (coefficientBox K M L s) =
      ∑ i ∈ Finset.range (M + 1),
        ∑ j ∈ Finset.range (s + 1), (L + 1 - i - j) := by
  rw [coefficientBox_finrank_of_le K M L s hML]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_range]

def blockInputCount (M L s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (M + 1),
    ∑ j ∈ Finset.range (s + 1), (L + 1 - i - j)

/-- .
 -/
def blockKernelLowerBound (M L s h : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (M + 1 - h),
    ∑ j ∈ Finset.range (s + 1 - h), (L + 1 - h - i - j)

def contactRankBound (M L s h : ℕ) : ℕ :=
  blockInputCount M L s - blockKernelLowerBound M L s h

/-- .
 -/
theorem blockJet_rank_le_contactRankBound (M L s h : ℕ) (hML : M ≤ L) :
    Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
      contactRankBound M L s h := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ s
    · have hL : h ≤ L := hM.trans hML
      have hineq := blockJet_rank_add_quotient_finrank_le K hM hL hs
      rw [coefficientBox_finrank_range K M L s hML,
        coefficientBox_finrank_range K (M - h) (L - h) (s - h)
          (Nat.sub_le_sub_right hML h)] at hineq
      have hMeq : M - h + 1 = M + 1 - h := by omega
      have hLeq : L - h + 1 = L + 1 - h := by omega
      have hseq : s - h + 1 = s + 1 - h := by omega
      rw [hMeq, hLeq, hseq] at hineq
      unfold contactRankBound blockInputCount blockKernelLowerBound
      omega
    · have hzero : s + 1 - h = 0 := by omega
      have hinput := blockJet_rank_le_input K M L s h hML
      simpa [contactRankBound, blockKernelLowerBound, blockInputCount,
        hzero, Finset.sum_range] using hinput
  · have hzero : M + 1 - h = 0 := by omega
    have hinput := blockJet_rank_le_input K M L s h hML
    simpa [contactRankBound, blockKernelLowerBound, blockInputCount,
      hzero, Finset.sum_range] using hinput

def localRankBound (m L s : ℕ) : ℕ :=
  ∑ r ∈ Finset.range m,
    contactRankBound (min r L) L s (min (r + 1) (m - r))

/-- .

 -/
theorem sum_blockJet_ranks_le_localRankBound (m L s : ℕ) :
    (∑ r ∈ Finset.range m,
      Module.finrank K (LinearMap.range
        (blockJet K (min r L) L s (min (r + 1) (m - r))))) ≤
      localRankBound m L s := by
  apply Finset.sum_le_sum
  intro r hr
  exact blockJet_rank_le_contactRankBound K (min r L) L s
    (min (r + 1) (m - r)) (min_le_right r L)

end

end ProximityPrize.SubmissionLower.ContactFlagRankKernel6641Research
