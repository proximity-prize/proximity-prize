import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminant6400
import ProximityPrize.SubmissionLower.BCHKSDoubleCounting
import ProximityPrize.SubmissionLower.BCHKSLocatorSyndrome6400

/-!
# Root-pin extraction for the low-nullity locator branch

Every surviving locator is split over the fixed evaluation domain and has at
least `76771` distinct roots after the already-certified score-63.99 slopes
are removed.  Repeated incidence pigeonholing selects a common root while
retaining a controlled number of slopes.  Seven such pins are affordable;
the exact endpoint still beats the determinant degree after seven Frobenius
rows are replaced by evaluation rows.
-/

namespace ProximityPrize.SubmissionLower

set_option autoImplicit false

/-- One root-pin step.  If every row contains `t` points and already contains
the pinned set `P`, the residual incidence count supplies a new point outside
`P` which is shared by more than `B` rows. -/
theorem exists_new_common_pin
    {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    (T : Finset J) (R : J → Finset I) (P : Finset I)
    (n t B : ℕ) (hn : Fintype.card I = n)
    (htn : t ≤ n)
    (hP : ∀ z ∈ T, P ⊆ R z)
    (hRcard : ∀ z ∈ T, t ≤ (R z).card)
    (hcount : n * B < (t - P.card) * T.card) :
    ∃ i T', i ∉ P ∧ T' ⊆ T ∧ B < T'.card ∧
      (∀ z ∈ T', insert i P ⊆ R z) := by
  classical
  let A : J → Finset I := fun z => R z \ P
  have hrow : ∀ z ∈ T, n - (n - (t - P.card)) ≤ (A z).card := by
    intro z hz
    have hPz := hP z hz
    have hcard : (A z).card = (R z).card - P.card := by
      dsimp only [A]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hPz]
    have htn' : t - P.card ≤ n := (Nat.sub_le t P.card).trans htn
    rw [Nat.sub_sub_self htn']
    rw [hcard]
    exact Nat.sub_le_sub_right (hRcard z hz) P.card
  have hlarge := many_large_fibers T A n (n - (t - P.card)) 0 B hn hrow (by
    simpa [Nat.sub_sub_self ((Nat.sub_le t P.card).trans htn)] using hcount)
  let G : Finset I := Finset.univ.filter fun i : I =>
    B < (T.filter fun z => i ∈ A z).card
  have hGpos : 0 < G.card := by
    change 0 < (Finset.univ.filter fun i : I =>
      B < (T.filter fun z => i ∈ A z).card).card
    omega
  obtain ⟨i, hiG⟩ := Finset.card_pos.mp hGpos
  have hifiber : B < (T.filter fun z => i ∈ A z).card :=
    (Finset.mem_filter.mp hiG).2
  have hfiberPos : 0 < (T.filter fun z => i ∈ A z).card :=
    lt_of_le_of_lt (Nat.zero_le B) hifiber
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp hfiberPos
  have hiP : i ∉ P := (Finset.mem_sdiff.mp
    ((Finset.mem_filter.mp hz₀).2)).2
  let T' : Finset J := T.filter fun z => i ∈ R z
  have hfilter : (T.filter fun z => i ∈ A z) = T' := by
    ext z
    simp only [A, T', Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hzT, hiR, _⟩
      exact ⟨hzT, hiR⟩
    · rintro ⟨hzT, hiR⟩
      exact ⟨hzT, hiR, hiP⟩
  refine ⟨i, T', hiP, ?_, ?_, ?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp hz).1
  · rw [← hfilter]
    exact hifiber
  · intro z hzT'
    have hzT : z ∈ T := (Finset.mem_filter.mp hzT').1
    have hiR : i ∈ R z := (Finset.mem_filter.mp hzT').2
    intro x hx
    rw [Finset.mem_insert] at hx
    exact hx.elim (fun hxi => hxi ▸ hiR) (fun hxP => hP z hzT hxP)

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- A score-64 witness can be shrunk to exactly `185364` agreement
coordinates.  Its complementary locator consequently has exactly `76780`
distinct evaluation-domain roots, even when the original close polynomial
had fewer errors.  This justifies applying the root-pin argument to *all* bad
slopes rather than first pigeonholing an exact error count. -/
theorem exists_score6400_exact_split_locator_of_mcaBad
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z) :
    ∃ E : Finset IRSProfile.Index,
      ∃ locator : Fin (76780 + 1) → IRSProfile.Field,
        E.card = 76780 ∧ locator ≠ 0 ∧
        (∀ j, koalaSexticFrobenius (locator j) = locator j) ∧
        locator ∈ LinearMap.ker
          (rsSyndromeHankel IRSProfile.domain
            (fun i => f₀ i + z * f₁ i)
            locatorOrdinaryRows6400 76780).mulVecLin ∧
        ∀ i ∈ E, ∑ j : Fin (76780 + 1),
          locator j * IRSProfile.domain i ^ j.1 = 0 := by
  classical
  have hbadRS : MCABad
      (ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension)
      f₀ f₁ 185364 z := by
    simpa only [IRSProfile.baseCode] using hbad
  obtain ⟨A, P, hA, hPdegree, hPagree, _⟩ :=
    exists_rs_polynomial_data_of_mcaBad
      IRSProfile.domain IRSProfile.baseDimension 185364 f₀ f₁ z hbadRS
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hA
  let E : Finset IRSProfile.Index := Finset.univ \ A'
  have hEcard : E.card = 76780 := by
    dsimp only [E]
    rw [Finset.card_sdiff]
    norm_num [hA'card, IRSProfile.Index]
  have hPagree' : ∀ i ∈ A',
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro i hi
    exact hPagree i (hA'sub hi)
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  have hlocatorDegree :
      (rsAgreementLocator IRSProfile.domain A').natDegree = 76780 := by
    rw [rsAgreementLocator_natDegree]
    exact hEcard
  let locator := rsLocatorCoefficients IRSProfile.domain A' 76780
  have hlocatorNe : locator ≠ 0 :=
    rsLocatorCoefficients_ne_zero IRSProfile.domain A' 76780
      hlocatorDegree.le
  have hlocatorFixed : ∀ j,
      koalaSexticFrobenius (locator j) = locator j := by
    intro j
    simpa only [locator, rsLocatorCoefficients] using
      map_rsAgreementLocator_coeff IRSProfile.domain
        koalaSexticFrobenius koalaSexticFrobenius_fixed_domain A' j.1
  have hdegreeRoom :
      (Finset.univ \ A').card + P.natDegree + locatorOrdinaryRows6400 ≤
        Fintype.card IRSProfile.Index - 1 := by
    have hcompcard : (Finset.univ \ A').card = 76780 := by
      simpa only [E] using hEcard
    rw [hcompcard]
    norm_num [locatorOrdinaryRows6400, IRSProfile.Index]
    omega
  have hlocatorMem : locator ∈ LinearMap.ker
      (rsSyndromeHankel IRSProfile.domain
        (fun i => f₀ i + z * f₁ i)
        locatorOrdinaryRows6400 76780).mulVecLin :=
    rsLocatorCoefficients_mem_hankel_ker
      IRSProfile.domain A' (fun i => f₀ i + z * f₁ i) P hPagree'
      locatorOrdinaryRows6400 76780 hlocatorDegree.le hdegreeRoom
  refine ⟨E, locator, hEcard, hlocatorNe, hlocatorFixed,
    hlocatorMem, ?_⟩
  intro i hiE
  have hiA' : i ∉ A' := (Finset.mem_sdiff.mp hiE).2
  have hroot := rsAgreementLocator_eval_eq_zero_of_not_mem
    IRSProfile.domain A' hiA'
  calc
    (∑ j : Fin (76780 + 1),
        locator j * IRSProfile.domain i ^ j.1) =
        (rsAgreementLocator IRSProfile.domain A').eval
          (IRSProfile.domain i) := by
      rw [Polynomial.eval_eq_sum_range'
        (Nat.lt_succ_of_le hlocatorDegree.le)]
      rw [← Fin.sum_univ_eq_sum_range]
      rfl
    _ = 0 := hroot

/-! The exact seven recurrence thresholds.  Each theorem is deliberately
separate so that the staged combinatorial proof uses only linear arithmetic
and does not elaborate large rational expressions. -/

theorem score6400_root_pin_step0_numeric (s : ℕ)
    (hs : 274972148031419760 < s) :
    262144 * 80527827364044671 < 76771 * s := by omega

theorem score6400_root_pin_step1_numeric (s : ℕ)
    (hs : 80527827364044671 < s) :
    262144 * 23582921244574392 < 76770 * s := by omega

theorem score6400_root_pin_step2_numeric (s : ℕ)
    (hs : 23582921244574392 < s) :
    262144 * 6906270145510603 < 76769 * s := by omega

theorem score6400_root_pin_step3_numeric (s : ℕ)
    (hs : 6906270145510603 < s) :
    262144 * 2022478281137687 < 76768 * s := by omega

theorem score6400_root_pin_step4_numeric (s : ℕ)
    (hs : 2022478281137687 < s) :
    262144 * 592268334228885 < 76767 * s := by omega

theorem score6400_root_pin_step5_numeric (s : ℕ)
    (hs : 592268334228885 < s) :
    262144 * 173439296514185 < 76766 * s := by omega

theorem score6400_root_pin_step6_numeric (s : ℕ)
    (hs : 173439296514185 < s) :
    262144 * 50789137256284 < 76765 * s := by omega

/-- After seven root pins the surviving slope count still exceeds the
diagonal degree of the augmented locator determinant. -/
theorem score6400_seven_pin_degree_margin :
    54292 + 2130706433 * (22489 - 7) < 50789137256284 := by
  norm_num

/-- Seven successive applications of `exists_new_common_pin`, with the exact
score-64 thresholds.  The conclusion is independent of polynomials: any
family of `76771`-large subsets of a `262144`-point universe has the required
seven-point common core on a determinant-beating subfamily. -/
theorem exists_seven_common_pins_6400
    {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    (T : Finset J) (R : J → Finset I)
    (hn : Fintype.card I = 262144)
    (hT : 274972148031419760 < T.card)
    (hRcard : ∀ z ∈ T, 76771 ≤ (R z).card) :
    ∃ P : Finset I, ∃ T' : Finset J,
      P.card = 7 ∧ T' ⊆ T ∧ 50789137256284 < T'.card ∧
        ∀ z ∈ T', P ⊆ R z := by
  classical
  obtain ⟨i₀, T₁, hi₀, hT₁sub, hT₁card, hpin₁⟩ :=
    exists_new_common_pin T R ∅ 262144 76771 80527827364044671 hn
      (by norm_num) (by simp) hRcard (by
        simpa using score6400_root_pin_step0_numeric T.card hT)
  let P₁ : Finset I := insert i₀ ∅
  have hP₁card : P₁.card = 1 := by simp [P₁]
  obtain ⟨i₁, T₂, hi₁, hT₂sub, hT₂card, hpin₂⟩ :=
    exists_new_common_pin T₁ R P₁ 262144 76771 23582921244574392 hn
      (by norm_num)
      (by simpa [P₁] using hpin₁)
      (fun z hz => hRcard z (hT₁sub hz)) (by
        simpa [hP₁card] using
          score6400_root_pin_step1_numeric T₁.card hT₁card)
  let P₂ : Finset I := insert i₁ P₁
  have hP₂card : P₂.card = 2 := by simp [P₂, hi₁, hP₁card]
  obtain ⟨i₂, T₃, hi₂, hT₃sub, hT₃card, hpin₃⟩ :=
    exists_new_common_pin T₂ R P₂ 262144 76771 6906270145510603 hn
      (by norm_num)
      (by simpa [P₂] using hpin₂)
      (fun z hz => hRcard z (hT₁sub (hT₂sub hz))) (by
        simpa [hP₂card] using
          score6400_root_pin_step2_numeric T₂.card hT₂card)
  let P₃ : Finset I := insert i₂ P₂
  have hP₃card : P₃.card = 3 := by simp [P₃, hi₂, hP₂card]
  obtain ⟨i₃, T₄, hi₃, hT₄sub, hT₄card, hpin₄⟩ :=
    exists_new_common_pin T₃ R P₃ 262144 76771 2022478281137687 hn
      (by norm_num)
      (by simpa [P₃] using hpin₃)
      (fun z hz => hRcard z (hT₁sub (hT₂sub (hT₃sub hz)))) (by
        simpa [hP₃card] using
          score6400_root_pin_step3_numeric T₃.card hT₃card)
  let P₄ : Finset I := insert i₃ P₃
  have hP₄card : P₄.card = 4 := by simp [P₄, hi₃, hP₃card]
  obtain ⟨i₄, T₅, hi₄, hT₅sub, hT₅card, hpin₅⟩ :=
    exists_new_common_pin T₄ R P₄ 262144 76771 592268334228885 hn
      (by norm_num)
      (by simpa [P₄] using hpin₄)
      (fun z hz => hRcard z
        (hT₁sub (hT₂sub (hT₃sub (hT₄sub hz))))) (by
        simpa [hP₄card] using
          score6400_root_pin_step4_numeric T₄.card hT₄card)
  let P₅ : Finset I := insert i₄ P₄
  have hP₅card : P₅.card = 5 := by simp [P₅, hi₄, hP₄card]
  obtain ⟨i₅, T₆, hi₅, hT₆sub, hT₆card, hpin₆⟩ :=
    exists_new_common_pin T₅ R P₅ 262144 76771 173439296514185 hn
      (by norm_num)
      (by simpa [P₅] using hpin₅)
      (fun z hz => hRcard z
        (hT₁sub (hT₂sub (hT₃sub (hT₄sub (hT₅sub hz)))))) (by
        simpa [hP₅card] using
          score6400_root_pin_step5_numeric T₅.card hT₅card)
  let P₆ : Finset I := insert i₅ P₅
  have hP₆card : P₆.card = 6 := by simp [P₆, hi₅, hP₅card]
  obtain ⟨i₆, T₇, hi₆, hT₇sub, hT₇card, hpin₇⟩ :=
    exists_new_common_pin T₆ R P₆ 262144 76771 50789137256284 hn
      (by norm_num)
      (by simpa [P₆] using hpin₆)
      (fun z hz => hRcard z
        (hT₁sub (hT₂sub (hT₃sub (hT₄sub (hT₅sub (hT₆sub hz))))))) (by
        simpa [hP₆card] using
          score6400_root_pin_step6_numeric T₆.card hT₆card)
  let P₇ : Finset I := insert i₆ P₆
  have hP₇card : P₇.card = 7 := by simp [P₇, hi₆, hP₆card]
  refine ⟨P₇, T₇, hP₇card, ?_, hT₇card, ?_⟩
  · exact fun _ hz =>
      hT₁sub (hT₂sub (hT₃sub (hT₄sub (hT₅sub (hT₆sub (hT₇sub hz))))))
  · simpa [P₇] using hpin₇

end ProximityPrize.SubmissionLower
