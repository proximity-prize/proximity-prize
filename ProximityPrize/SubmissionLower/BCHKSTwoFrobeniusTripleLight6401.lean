import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusPrimitiveFrame6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusTripleLight6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusPrimitiveFrame6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
noncomputable def denominatorZeroCoordinates
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι) (z : F) : Finset ι := by
  classical
  exact B.filter fun i =>
    Polynomial.eval z (evalOuterAt (alpha i) D) = 0
noncomputable def lightChallenges
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (S : Finset F) (t : ℕ) : Finset F := by
  classical
  exact S.filter fun z => (denominatorZeroCoordinates D alpha B z).card ≤ t
noncomputable def heavyChallenges
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (S : Finset F) (t : ℕ) : Finset F := by
  classical
  exact S.filter fun z => t < (denominatorZeroCoordinates D alpha B z).card
theorem light_union_heavy
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (S : Finset F) (t : ℕ) :
    lightChallenges D alpha B S t ∪ heavyChallenges D alpha B S t = S := by
  classical
  ext z
  simp only [lightChallenges, heavyChallenges, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
  · intro hz
    by_cases hlight :
        (denominatorZeroCoordinates D alpha B z).card ≤ t
    · exact Or.inl ⟨hz, hlight⟩
    · exact Or.inr ⟨hz, by omega⟩
theorem light_disjoint_heavy
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (S : Finset F) (t : ℕ) :
    Disjoint (lightChallenges D alpha B S t)
      (heavyChallenges D alpha B S t) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzL hzH
  have hL := (Finset.mem_filter.mp hzL).2
  have hH := (Finset.mem_filter.mp hzH).2
  omega
theorem owner_eval_eq_affine_of_rational_identity
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D N : XOverZ F) (alpha u₀ u₁ : ι → F) (I : Finset ι)
    (z : F) (P : Polynomial F)
    (hbranch : specializeCoeffZ z D * P = -specializeCoeffZ z N)
    (i : ι) (hi : i ∈ rationalIdentityCoordinates D N alpha u₀ u₁ I)
    (hden : Polynomial.eval z (evalOuterAt (alpha i) D) ≠ 0) :
    Polynomial.eval (alpha i) P = u₀ i + z * u₁ i := by
  classical
  have howner := congrArg (Polynomial.eval (alpha i)) hbranch
  simp only [Polynomial.eval_mul, Polynomial.eval_neg] at howner
  have hDcomm := eval_specializeCoeffZ_comm z (alpha i) D
  have hNcomm := eval_specializeCoeffZ_comm z (alpha i) N
  have hi' := Finset.mem_filter.mp hi
  have hmismatch := congrArg (Polynomial.eval z) hi'.2
  simp only [Polynomial.eval_zero] at hmismatch
  unfold rationalCoordinateMismatch affineValuePolynomial at hmismatch
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hmismatch
  rw [hDcomm, hNcomm] at howner
  apply mul_left_cancel₀ hden
  exact howner.trans (eq_neg_of_add_eq_zero_left hmismatch).symm
theorem sum_denominatorZeroCoordinates_card_le
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (S : Finset F) (n degreeCap : ℕ)
    (hn : Fintype.card ι ≤ n)
    (hactive : ∀ i ∈ B, evalOuterAt (alpha i) D ≠ 0)
    (hdegree : ∀ i ∈ B,
      (evalOuterAt (alpha i) D).natDegree ≤ degreeCap) :
    (∑ z ∈ S, (denominatorZeroCoordinates D alpha B z).card) ≤
      n * degreeCap := by
  classical
  have hswap :
      (∑ z ∈ S, (denominatorZeroCoordinates D alpha B z).card) =
        ∑ i ∈ B,
          (S.filter fun z =>
            Polynomial.eval z (evalOuterAt (alpha i) D) = 0).card := by
    calc
      (∑ z ∈ S, (denominatorZeroCoordinates D alpha B z).card) =
          ∑ z ∈ S, ∑ i ∈ B,
            if Polynomial.eval z (evalOuterAt (alpha i) D) = 0
            then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        unfold denominatorZeroCoordinates
        convert (Finset.card_filter
          (fun i => Polynomial.eval z (evalOuterAt (alpha i) D) = 0) B) using 1
        congr 1
        ext i
        simp
      _ = ∑ i ∈ B, ∑ z ∈ S,
          if Polynomial.eval z (evalOuterAt (alpha i) D) = 0
          then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i ∈ B,
          (S.filter fun z =>
            Polynomial.eval z (evalOuterAt (alpha i) D) = 0).card := by
        apply Finset.sum_congr rfl
        intro i hi
        simp
  calc
    (∑ z ∈ S, (denominatorZeroCoordinates D alpha B z).card) =
        ∑ i ∈ B,
          (S.filter fun z =>
            Polynomial.eval z (evalOuterAt (alpha i) D) = 0).card := hswap
    _ ≤ ∑ _i ∈ B, degreeCap := by
      apply Finset.sum_le_sum
      intro i hi
      exact (card_filter_eval_eq_zero_le_natDegree S _ (hactive i hi)).trans
        (hdegree i hi)
    _ = B.card * degreeCap := by simp
    _ ≤ Fintype.card ι * degreeCap :=
      Nat.mul_le_mul_right degreeCap (Finset.card_le_univ B)
    _ ≤ n * degreeCap := Nat.mul_le_mul_right degreeCap hn
theorem heavyChallenges_card_mul_succ_le
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (S : Finset F) (t n degreeCap : ℕ)
    (hn : Fintype.card ι ≤ n)
    (hactive : ∀ i ∈ B, evalOuterAt (alpha i) D ≠ 0)
    (hdegree : ∀ i ∈ B,
      (evalOuterAt (alpha i) D).natDegree ≤ degreeCap) :
    (heavyChallenges D alpha B S t).card * (t + 1) ≤
      n * degreeCap := by
  classical
  have hlower :
      (heavyChallenges D alpha B S t).card * (t + 1) ≤
        ∑ z ∈ heavyChallenges D alpha B S t,
          (denominatorZeroCoordinates D alpha B z).card := by
    calc
      (heavyChallenges D alpha B S t).card * (t + 1) =
          ∑ _z ∈ heavyChallenges D alpha B S t, (t + 1) := by simp
      _ ≤ ∑ z ∈ heavyChallenges D alpha B S t,
          (denominatorZeroCoordinates D alpha B z).card := by
        apply Finset.sum_le_sum
        intro z hz
        have := (Finset.mem_filter.mp hz).2
        omega
  calc
    (heavyChallenges D alpha B S t).card * (t + 1) ≤
        ∑ z ∈ heavyChallenges D alpha B S t,
          (denominatorZeroCoordinates D alpha B z).card := hlower
    _ ≤ ∑ z ∈ S, (denominatorZeroCoordinates D alpha B z).card :=
      Finset.sum_le_sum_of_subset (fun z hz => (Finset.mem_filter.mp hz).1)
    _ ≤ n * degreeCap :=
      sum_denominatorZeroCoordinates_card_le
        D alpha B S n degreeCap hn hactive hdegree
theorem heavyChallenges_card_le
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (S : Finset F) (t n degreeCap : ℕ)
    (hn : Fintype.card ι ≤ n)
    (hactive : ∀ i ∈ B, evalOuterAt (alpha i) D ≠ 0)
    (hdegree : ∀ i ∈ B,
      (evalOuterAt (alpha i) D).natDegree ≤ degreeCap) :
    (heavyChallenges D alpha B S t).card ≤
      (n * degreeCap) / (t + 1) := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < t + 1)]
  exact heavyChallenges_card_mul_succ_le
    D alpha B S t n degreeCap hn hactive hdegree
noncomputable def tripleGoodCoordinates
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (z₀ z₁ z₂ : F) : Finset ι :=
  B \ ((denominatorZeroCoordinates D alpha B z₀ ∪
    denominatorZeroCoordinates D alpha B z₁) ∪
      denominatorZeroCoordinates D alpha B z₂)
theorem tripleGoodCoordinates_card_lower
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (z₀ z₁ z₂ : F) (t : ℕ)
    (h₀ : (denominatorZeroCoordinates D alpha B z₀).card ≤ t)
    (h₁ : (denominatorZeroCoordinates D alpha B z₁).card ≤ t)
    (h₂ : (denominatorZeroCoordinates D alpha B z₂).card ≤ t) :
    B.card - 3 * t ≤
      (tripleGoodCoordinates D alpha B z₀ z₁ z₂).card := by
  classical
  have hunion :
      (((denominatorZeroCoordinates D alpha B z₀ ∪
        denominatorZeroCoordinates D alpha B z₁) ∪
          denominatorZeroCoordinates D alpha B z₂)).card ≤ 3 * t := by
    calc
      _ ≤ (denominatorZeroCoordinates D alpha B z₀ ∪
              denominatorZeroCoordinates D alpha B z₁).card +
            (denominatorZeroCoordinates D alpha B z₂).card :=
        Finset.card_union_le _ _
      _ ≤ ((denominatorZeroCoordinates D alpha B z₀).card +
              (denominatorZeroCoordinates D alpha B z₁).card) +
            (denominatorZeroCoordinates D alpha B z₂).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 3 * t := by omega
  have hdiff := Finset.le_card_sdiff
    (((denominatorZeroCoordinates D alpha B z₀ ∪
      denominatorZeroCoordinates D alpha B z₁) ∪
        denominatorZeroCoordinates D alpha B z₂)) B
  simpa [tripleGoodCoordinates] using
    (show B.card - 3 * t ≤
        (B \ ((denominatorZeroCoordinates D alpha B z₀ ∪
          denominatorZeroCoordinates D alpha B z₁) ∪
            denominatorZeroCoordinates D alpha B z₂)).card by omega)
theorem denominator_eval_ne_zero_of_mem_tripleGood
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D : XOverZ F) (alpha : ι → F) (B : Finset ι)
    (z₀ z₁ z₂ : F) (i : ι)
    (hi : i ∈ tripleGoodCoordinates D alpha B z₀ z₁ z₂) :
    Polynomial.eval z₀ (evalOuterAt (alpha i) D) ≠ 0 ∧
      Polynomial.eval z₁ (evalOuterAt (alpha i) D) ≠ 0 ∧
      Polynomial.eval z₂ (evalOuterAt (alpha i) D) ≠ 0 := by
  classical
  have hi' := Finset.mem_sdiff.mp hi
  simp only [Finset.mem_union, not_or] at hi'
  constructor
  · intro hz
    exact hi'.2.1.1 (Finset.mem_filter.mpr ⟨hi'.1, hz⟩)
  · constructor
    · intro hz
      exact hi'.2.1.2 (Finset.mem_filter.mpr ⟨hi'.1, hz⟩)
    · intro hz
      exact hi'.2.2 (Finset.mem_filter.mpr ⟨hi'.1, hz⟩)
theorem exists_affine_family_on_lightChallenges
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (D N : XOverZ F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) (P : F → Polynomial F)
    (k t : ℕ)
    (hBcard : k + 3 * t <
      (rationalIdentityCoordinates D N alpha u₀ u₁ I).card)
    (hlight : 1 < (lightChallenges D alpha
      (rationalIdentityCoordinates D N alpha u₀ u₁ I) S t).card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hbranch : ∀ z ∈ S,
      specializeCoeffZ z D * P z = -specializeCoeffZ z N) :
    ∃ p₀ p₁ : Polynomial F,
      p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ lightChallenges D alpha
        (rationalIdentityCoordinates D N alpha u₀ u₁ I) S t,
        P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let B := rationalIdentityCoordinates D N alpha u₀ u₁ I
  let L := lightChallenges D alpha B S t
  obtain ⟨z₀, hz₀, z₁, hz₁, hzneq⟩ := Finset.one_lt_card.mp hlight
  have hz₀S : z₀ ∈ S := (Finset.mem_filter.mp hz₀).1
  have hz₁S : z₁ ∈ S := (Finset.mem_filter.mp hz₁).1
  have hz₀light : (denominatorZeroCoordinates D alpha B z₀).card ≤ t :=
    (Finset.mem_filter.mp hz₀).2
  have hz₁light : (denominatorZeroCoordinates D alpha B z₁).card ≤ t :=
    (Finset.mem_filter.mp hz₁).2
  have hsubne : z₁ - z₀ ≠ 0 := sub_ne_zero.mpr hzneq.symm
  let p₁ : Polynomial F :=
    Polynomial.C ((z₁ - z₀)⁻¹) * (P z₁ - P z₀)
  let p₀ : Polynomial F := P z₀ - Polynomial.C z₀ * p₁
  have hp₁degree : p₁.natDegree ≤ k := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_sub_le _ _).trans
        (max_le (hPdegree z₁ hz₁S) (hPdegree z₀ hz₀S)))
  have hp₀degree : p₀.natDegree ≤ k := by
    exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
      (hPdegree z₀ hz₀S)
      (Polynomial.natDegree_C_mul_le z₀ p₁ |>.trans hp₁degree)
  refine ⟨p₀, p₁, hp₀degree, hp₁degree, ?_⟩
  intro z hz
  have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
  have hzlight : (denominatorZeroCoordinates D alpha B z).card ≤ t :=
    (Finset.mem_filter.mp hz).2
  let E := tripleGoodCoordinates D alpha B z₀ z₁ z
  have hEcard : k < E.card := by
    have hlower := tripleGoodCoordinates_card_lower
      D alpha B z₀ z₁ z t hz₀light hz₁light hzlight
    have hBcard' : k + 3 * t < B.card := by simpa [B] using hBcard
    dsimp [E]
    omega
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z)
      (p₀ + Polynomial.C z * p₁)
      (f := fun i : {i // i ∈ E} => alpha i.1)
      (alpha.injective.comp Subtype.val_injective)
  · intro i
    have hiB : i.1 ∈ B := (Finset.mem_sdiff.mp i.2).1
    have hden := denominator_eval_ne_zero_of_mem_tripleGood
      D alpha B z₀ z₁ z i.1 i.2
    have howner₀ := owner_eval_eq_affine_of_rational_identity
      D N alpha u₀ u₁ I z₀ (P z₀) (hbranch z₀ hz₀S)
        i.1 (by simpa [B] using hiB) hden.1
    have howner₁ := owner_eval_eq_affine_of_rational_identity
      D N alpha u₀ u₁ I z₁ (P z₁) (hbranch z₁ hz₁S)
        i.1 (by simpa [B] using hiB) hden.2.1
    have howner := owner_eval_eq_affine_of_rational_identity
      D N alpha u₀ u₁ I z (P z) (hbranch z hzS)
        i.1 (by simpa [B] using hiB) hden.2.2
    have hp₁eval : Polynomial.eval (alpha i.1) p₁ = u₁ i.1 := by
      simp only [p₁, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, howner₁, howner₀]
      field_simp [hsubne]
      ring
    have hp₀eval : Polynomial.eval (alpha i.1) p₀ = u₀ i.1 := by
      simp only [p₀, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, howner₀, hp₁eval]
      ring
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      hp₀eval, hp₁eval, howner]
  · rw [Fintype.card_coe]
    apply max_lt
    · exact (hPdegree z hzS).trans_lt hEcard
    · exact ((Polynomial.natDegree_add_le _ _).trans <| max_le
        hp₀degree
        (Polynomial.natDegree_C_mul_le z p₁ |>.trans hp₁degree)).trans_lt
          hEcard
def tripleLightThreshold6401 : ℕ := 18074
def tripleLightLineCap6401 : ℕ := 76791
def tripleLightHeavyCap6401 : ℕ :=
  (n6401 * rankTwoDenomZCap6401) / (tripleLightThreshold6401 + 1)
def tripleLightTotalCap6401 : ℕ :=
  tripleLightHeavyCap6401 + tripleLightLineCap6401
theorem tripleLight_ledger_exact6401 :
    ownerDegreeCap6401 + 3 * tripleLightThreshold6401 = 185293 ∧
      tripleLightHeavyCap6401 = 900079745938841 ∧
      tripleLightTotalCap6401 = 900079746015632 ∧
      tripleLightTotalCap6401 <
        BCHKSFinalConditional6401.mcaNumerator6401 ∧
      BCHKSFinalConditional6401.mcaNumerator6401 -
          tripleLightTotalCap6401 = 274080648348333611 := by
  norm_num [tripleLightThreshold6401, tripleLightLineCap6401,
    tripleLightHeavyCap6401, tripleLightTotalCap6401,
    ownerDegreeCap6401, n6401, rankTwoDenomZCap6401,
    balancedDepth6401, balancedThreshold6401, moduleIndexSum6401,
    a1XSlots6401, q6401,
    BCHKSFinalConditional6401.mcaNumerator6401,
    BCHKSList6401.maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    BCHKSList6401.listBound6401]
theorem ownerFamily_card_le_tripleLightTotalCap6401
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (D N : XOverZ F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) (P : F → Polynomial F)
    (hcardι : Fintype.card ι ≤ n6401)
    (hlarge : 185295 ≤
      (rationalIdentityCoordinates D N alpha u₀ u₁ I).card)
    (hactive : ∀ i ∈ rationalIdentityCoordinates D N alpha u₀ u₁ I,
      evalOuterAt (alpha i) D ≠ 0)
    (hdegree : ∀ i ∈ rationalIdentityCoordinates D N alpha u₀ u₁ I,
      (evalOuterAt (alpha i) D).natDegree ≤ rankTwoDenomZCap6401)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hbranch : ∀ z ∈ S,
      specializeCoeffZ z D * P z = -specializeCoeffZ z N)
    (hlineCap :
      ∀ p₀ p₁ : Polynomial F,
        p₀.natDegree ≤ ownerDegreeCap6401 →
        p₁.natDegree ≤ ownerDegreeCap6401 →
        (∀ z ∈ lightChallenges D alpha
          (rationalIdentityCoordinates D N alpha u₀ u₁ I) S
            tripleLightThreshold6401,
          P z = p₀ + Polynomial.C z * p₁) →
        (lightChallenges D alpha
          (rationalIdentityCoordinates D N alpha u₀ u₁ I) S
            tripleLightThreshold6401).card ≤ tripleLightLineCap6401) :
    S.card ≤ tripleLightTotalCap6401 := by
  classical
  let B := rationalIdentityCoordinates D N alpha u₀ u₁ I
  let L := lightChallenges D alpha B S tripleLightThreshold6401
  let H := heavyChallenges D alpha B S tripleLightThreshold6401
  have hHcap : H.card ≤ tripleLightHeavyCap6401 := by
    apply heavyChallenges_card_le D alpha B S tripleLightThreshold6401
      n6401 rankTwoDenomZCap6401 hcardι
    · intro i hi
      exact hactive i (by simpa [B] using hi)
    · intro i hi
      exact hdegree i (by simpa [B] using hi)
  have hLcap : L.card ≤ tripleLightLineCap6401 := by
    by_cases hsmall : L.card ≤ 1
    · exact hsmall.trans (by norm_num [tripleLightLineCap6401])
    · have htwo : 1 < L.card := by omega
      obtain ⟨p₀, p₁, hp₀, hp₁, halign⟩ :=
        exists_affine_family_on_lightChallenges
          D N alpha u₀ u₁ I S P ownerDegreeCap6401
            tripleLightThreshold6401 (by
              norm_num [ownerDegreeCap6401, tripleLightThreshold6401] at hlarge ⊢
              omega) (by simpa [L, B] using htwo) hPdegree hbranch
      exact hlineCap p₀ p₁ hp₀ hp₁ (by simpa [L, B] using halign)
  have hpartition : L ∪ H = S := by
    simpa [L, H, B] using light_union_heavy D alpha B S tripleLightThreshold6401
  have hdisjoint : Disjoint L H := by
    simpa [L, H, B] using light_disjoint_heavy D alpha B S tripleLightThreshold6401
  have hcard : S.card = L.card + H.card := by
    rw [← hpartition, Finset.card_union_of_disjoint hdisjoint]
  rw [hcard, tripleLightTotalCap6401]
  calc
    L.card + H.card ≤ tripleLightLineCap6401 + tripleLightHeavyCap6401 :=
      Nat.add_le_add hLcap hHcap
    _ = tripleLightHeavyCap6401 + tripleLightLineCap6401 := Nat.add_comm _ _
end BCHKSTwoFrobeniusTripleLight6401
end ProximityPrize.SubmissionLower
