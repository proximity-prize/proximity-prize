import ProximityPrize.SubmissionLower.BCHKSReceivedTailCompressionShortRelation6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSReceivedTailCompressionSemantic6401
open Polynomial
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusTailKernelSufficiency6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSReceivedTailCompressionShortRelation6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
section Generic
variable {F I : Type*} [Field F] [Fintype I] [Nonempty I]
  [DecidableEq I]
abbrev TailPairVector6401 (F : Type*) :=
  Fin (22507 + 1) ⊕ Fin (22507 + 1) → F
def fourLaneBasePair6401 :
    FourLaneTailVector6401 F →ₗ[F] TailPairVector6401 F where
  toFun v
    | Sum.inl j => v 0 j
    | Sum.inr j => v 2 j
  map_add' _ _ := by
    funext j
    cases j <;> rfl
  map_smul' _ _ := by
    funext j
    cases j <;> rfl
def fourLaneDirectionPair6401 :
    FourLaneTailVector6401 F →ₗ[F] TailPairVector6401 F where
  toFun v
    | Sum.inl j => v 1 j
    | Sum.inr j => v 3 j
  map_add' _ _ := by
    funext j
    cases j <;> rfl
  map_smul' _ _ := by
    funext j
    cases j <;> rfl
noncomputable def receivedEndpointFourLaneMap6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F) (k : Nat) :
    FourLaneTailVector6401 F →ₗ[F]
      (Fin (Fintype.card I - (k + 22507 + 1)) → F) :=
  ((receivedTailMatrix6401 sigma alpha u₀ k 22507).mulVecLin.comp
      fourLaneBasePair6401) +
    ((receivedTailMatrix6401 sigma alpha u₁ k 22507).mulVecLin.comp
      fourLaneDirectionPair6401)
noncomputable def fourLaneBasePolynomials6401
    (v : FourLaneTailVector6401 F) : F[X] × F[X] :=
  tailPairPolynomial 22507 (fourLaneBasePair6401 v)
noncomputable def fourLaneDirectionPolynomials6401
    (v : FourLaneTailVector6401 F) : F[X] × F[X] :=
  tailPairPolynomial 22507 (fourLaneDirectionPair6401 v)
noncomputable def fourLaneReceivedRepresentative6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (v : FourLaneTailVector6401 F) : F[X] :=
  receivedPairInterpolant6401 sigma alpha u₀
      (fourLaneBasePolynomials6401 v).1
      (fourLaneBasePolynomials6401 v).2 +
    receivedPairInterpolant6401 sigma alpha u₁
      (fourLaneDirectionPolynomials6401 v).1
      (fourLaneDirectionPolynomials6401 v).2
theorem tailPairPolynomial_fst_coeff6401
    (v : TailPairVector6401 F) (j : Fin (22507 + 1)) :
    (tailPairPolynomial 22507 v).1.coeff j.1 = v (Sum.inl j) := by
  classical
  simp [tailPairPolynomial]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro b hbj
    rw [if_neg]
    intro heq
    exact hbj (Fin.ext heq.symm)
theorem tailPairPolynomial_snd_coeff6401
    (v : TailPairVector6401 F) (j : Fin (22507 + 1)) :
    (tailPairPolynomial 22507 v).2.coeff j.1 = v (Sum.inr j) := by
  classical
  simp [tailPairPolynomial]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro b hbj
    rw [if_neg]
    intro heq
    exact hbj (Fin.ext heq.symm)
theorem tailPairPolynomial_eq_zero_imp_vector_eq_zero6401
    (v : TailPairVector6401 F)
    (hfst : (tailPairPolynomial 22507 v).1 = 0)
    (hsnd : (tailPairPolynomial 22507 v).2 = 0) :
    v = 0 := by
  funext j
  cases j with
  | inl j =>
      have hcoeff := tailPairPolynomial_fst_coeff6401 v j
      rw [hfst] at hcoeff
      simpa using hcoeff.symm
  | inr j =>
      have hcoeff := tailPairPolynomial_snd_coeff6401 v j
      rw [hsnd] at hcoeff
      simpa using hcoeff.symm
theorem fourLanePolynomials_all_zero_imp_vector_eq_zero6401
    (v : FourLaneTailVector6401 F)
    (hA₀ : (fourLaneBasePolynomials6401 v).1 = 0)
    (hA₁ : (fourLaneDirectionPolynomials6401 v).1 = 0)
    (hB₀ : (fourLaneBasePolynomials6401 v).2 = 0)
    (hB₁ : (fourLaneDirectionPolynomials6401 v).2 = 0) :
    v = 0 := by
  have hbase : fourLaneBasePair6401 v = 0 :=
    tailPairPolynomial_eq_zero_imp_vector_eq_zero6401
      (fourLaneBasePair6401 v) hA₀ hB₀
  have hdirection : fourLaneDirectionPair6401 v = 0 :=
    tailPairPolynomial_eq_zero_imp_vector_eq_zero6401
      (fourLaneDirectionPair6401 v) hA₁ hB₁
  funext lane j
  fin_cases lane
  · exact congrFun hbase (Sum.inl j)
  · exact congrFun hdirection (Sum.inl j)
  · exact congrFun hbase (Sum.inr j)
  · exact congrFun hdirection (Sum.inr j)
private theorem tailPairPolynomial_fst_degree_le_11253
    (v : TailPairVector6401 F)
    (hhigh : ∀ j : Fin tailHighLaneSlots6401,
      v (Sum.inl ⟨tailShortLaneSlots6401 + j.1, by
        have hj := j.2
        norm_num [tailLaneWidth6401, tailShortLaneSlots6401,
          tailHighLaneSlots6401] at hj ⊢
        omega⟩) = 0) :
    (tailPairPolynomial 22507 v).1.natDegree ≤ 11253 := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hnwindow : n < tailLaneWidth6401
  · have hnlow : tailShortLaneSlots6401 ≤ n := by
      norm_num [tailShortLaneSlots6401] at hn ⊢
      omega
    let j : Fin tailHighLaneSlots6401 :=
      ⟨n - tailShortLaneSlots6401, by
        norm_num [tailLaneWidth6401, tailShortLaneSlots6401,
          tailHighLaneSlots6401] at hnwindow hnlow ⊢
        omega⟩
    have hj : tailShortLaneSlots6401 + j.1 = n := by
      dsimp [j]
      omega
    let jf : Fin (22507 + 1) := ⟨n, by
      norm_num [tailLaneWidth6401] at hnwindow ⊢
      omega⟩
    change (tailPairPolynomial 22507 v).1.coeff jf.1 = 0
    rw [tailPairPolynomial_fst_coeff6401]
    have hindex : jf =
        ⟨tailShortLaneSlots6401 + j.1, by
          have hj' := j.2
          norm_num [tailShortLaneSlots6401, tailHighLaneSlots6401,
            tailLaneWidth6401] at hj' ⊢
          omega⟩ := by
      apply Fin.ext
      exact hj.symm
    rw [hindex]
    exact hhigh j
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hdeg := tailPairPolynomial_fst_natDegree_le 22507 v
    norm_num [tailLaneWidth6401] at hnwindow
    omega
private theorem tailPairPolynomial_snd_degree_le_11253
    (v : TailPairVector6401 F)
    (hhigh : ∀ j : Fin tailHighLaneSlots6401,
      v (Sum.inr ⟨tailShortLaneSlots6401 + j.1, by
        have hj := j.2
        norm_num [tailLaneWidth6401, tailShortLaneSlots6401,
          tailHighLaneSlots6401] at hj ⊢
        omega⟩) = 0) :
    (tailPairPolynomial 22507 v).2.natDegree ≤ 11253 := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hnwindow : n < tailLaneWidth6401
  · have hnlow : tailShortLaneSlots6401 ≤ n := by
      norm_num [tailShortLaneSlots6401] at hn ⊢
      omega
    let j : Fin tailHighLaneSlots6401 :=
      ⟨n - tailShortLaneSlots6401, by
        norm_num [tailLaneWidth6401, tailShortLaneSlots6401,
          tailHighLaneSlots6401] at hnwindow hnlow ⊢
        omega⟩
    have hj : tailShortLaneSlots6401 + j.1 = n := by
      dsimp [j]
      omega
    let jf : Fin (22507 + 1) := ⟨n, by
      norm_num [tailLaneWidth6401] at hnwindow ⊢
      omega⟩
    change (tailPairPolynomial 22507 v).2.coeff jf.1 = 0
    rw [tailPairPolynomial_snd_coeff6401]
    have hindex : jf =
        ⟨tailShortLaneSlots6401 + j.1, by
          have hj' := j.2
          norm_num [tailShortLaneSlots6401, tailHighLaneSlots6401,
            tailLaneWidth6401] at hj' ⊢
          omega⟩ := by
      apply Fin.ext
      exact hj.symm
    rw [hindex]
    exact hhigh j
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hdeg := tailPairPolynomial_snd_natDegree_le 22507 v
    norm_num [tailLaneWidth6401] at hnwindow
    omega
theorem fourLanePolynomials_degree_le_11253_6401
    (v : FourLaneTailVector6401 F)
    (hhigh : ∀ lane (j : Fin tailHighLaneSlots6401),
      v lane ⟨tailShortLaneSlots6401 + j.1, by
        have hj := j.2
        norm_num [tailLaneWidth6401, tailShortLaneSlots6401,
          tailHighLaneSlots6401] at hj ⊢
        omega⟩ = 0) :
    (fourLaneBasePolynomials6401 v).1.natDegree ≤ 11253 ∧
      (fourLaneDirectionPolynomials6401 v).1.natDegree ≤ 11253 ∧
      (fourLaneBasePolynomials6401 v).2.natDegree ≤ 11253 ∧
      (fourLaneDirectionPolynomials6401 v).2.natDegree ≤ 11253 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply tailPairPolynomial_fst_degree_le_11253
      (fourLaneBasePair6401 v)
    intro j
    change v 0 _ = 0
    exact hhigh 0 j
  · apply tailPairPolynomial_fst_degree_le_11253
      (fourLaneDirectionPair6401 v)
    intro j
    change v 1 _ = 0
    exact hhigh 1 j
  · apply tailPairPolynomial_snd_degree_le_11253
      (fourLaneBasePair6401 v)
    intro j
    change v 2 _ = 0
    exact hhigh 2 j
  · apply tailPairPolynomial_snd_degree_le_11253
      (fourLaneDirectionPair6401 v)
    intro j
    change v 3 _ = 0
    exact hhigh 3 j
theorem fourLaneReceivedRepresentative_degree_le_of_map_eq_zero6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (k : Nat) (v : FourLaneTailVector6401 F)
    (hwindow : k + 22507 < Fintype.card I)
    (hzero : receivedEndpointFourLaneMap6401 sigma alpha u₀ u₁ k v = 0) :
    (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v).natDegree ≤
      k + 22507 := by
  classical
  let R := fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hncard : n < Fintype.card I
  · have hbase : k + 22507 + 1 ≤ n := by omega
    let r : Fin (Fintype.card I - (k + 22507 + 1)) :=
      ⟨n - (k + 22507 + 1), by omega⟩
    have hr := congrFun hzero r
    have hrval : k + 22507 + 1 + (n - (k + 22507 + 1)) = n := by
      omega
    have hbaseCoeff := receivedTailMatrix_mulVec_eq_coeff6401
      sigma alpha u₀ k 22507 (fourLaneBasePair6401 v) r
    have hdirCoeff := receivedTailMatrix_mulVec_eq_coeff6401
      sigma alpha u₁ k 22507 (fourLaneDirectionPair6401 v) r
    have hbaseCoeffN :
        (receivedPairInterpolant6401 sigma alpha u₀
          (fourLaneBasePolynomials6401 v).1
          (fourLaneBasePolynomials6401 v).2).coeff n =
            (receivedTailMatrix6401 sigma alpha u₀ k 22507).mulVec
              (fourLaneBasePair6401 v) r := by
      rw [← hrval]
      exact hbaseCoeff.symm
    have hdirCoeffN :
        (receivedPairInterpolant6401 sigma alpha u₁
          (fourLaneDirectionPolynomials6401 v).1
          (fourLaneDirectionPolynomials6401 v).2).coeff n =
            (receivedTailMatrix6401 sigma alpha u₁ k 22507).mulVec
              (fourLaneDirectionPair6401 v) r := by
      rw [← hrval]
      exact hdirCoeff.symm
    change R.coeff n = 0
    rw [show R.coeff n =
        (receivedPairInterpolant6401 sigma alpha u₀
          (fourLaneBasePolynomials6401 v).1
          (fourLaneBasePolynomials6401 v).2).coeff n +
        (receivedPairInterpolant6401 sigma alpha u₁
          (fourLaneDirectionPolynomials6401 v).1
          (fourLaneDirectionPolynomials6401 v).2).coeff n by
          simp [R, fourLaneReceivedRepresentative6401]]
    rw [hbaseCoeffN, hdirCoeffN]
    simpa [receivedEndpointFourLaneMap6401, Matrix.mulVecLin_apply]
      using hr
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hbaseDegree := receivedPairInterpolant_natDegree_lt_card6401
      sigma alpha u₀ (fourLaneBasePolynomials6401 v).1
        (fourLaneBasePolynomials6401 v).2
    have hdirDegree := receivedPairInterpolant_natDegree_lt_card6401
      sigma alpha u₁ (fourLaneDirectionPolynomials6401 v).1
        (fourLaneDirectionPolynomials6401 v).2
    have hRdegree : R.natDegree < Fintype.card I :=
      (Polynomial.natDegree_add_le _ _).trans_lt
        (max_lt hbaseDegree hdirDegree)
    exact hRdegree.trans_le (Nat.le_of_not_gt hncard)
theorem fourLaneReceivedRepresentative_eval6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (v : FourLaneTailVector6401 F) (i : I) :
    (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v).eval
        (alpha i) =
      (fourLaneBasePolynomials6401 v).1.eval (alpha i) * sigma (u₀ i) -
        (fourLaneBasePolynomials6401 v).2.eval (alpha i) * u₀ i +
      ((fourLaneDirectionPolynomials6401 v).1.eval (alpha i) *
          sigma (u₁ i) -
        (fourLaneDirectionPolynomials6401 v).2.eval (alpha i) * u₁ i) := by
  simp [fourLaneReceivedRepresentative6401,
    receivedPairInterpolant_eval6401]
def EndpointAlignment6401
    (sigma : F →+* F) (v : FourLaneTailVector6401 F) (z : F) : Prop :=
  (fourLaneDirectionPolynomials6401 v).1 =
      Polynomial.C (sigma z) * (fourLaneBasePolynomials6401 v).1 ∧
    (fourLaneDirectionPolynomials6401 v).2 =
      Polynomial.C z * (fourLaneBasePolynomials6401 v).2
theorem fourLaneReceivedRepresentative_eval_eq_alignedPair6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (v : FourLaneTailVector6401 F) (z : F)
    (halign : EndpointAlignment6401 sigma v z) (i : I) :
    (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v).eval
        (alpha i) =
      (fourLaneBasePolynomials6401 v).1.eval (alpha i) *
          sigma (u₀ i + z * u₁ i) -
        (fourLaneBasePolynomials6401 v).2.eval (alpha i) *
          (u₀ i + z * u₁ i) := by
  rw [fourLaneReceivedRepresentative_eval6401]
  rw [halign.1, halign.2]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, map_add, map_mul]
  ring
theorem failureRelation_of_alignedShortFourLane6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (v : FourLaneTailVector6401 F) (z : F) (P : F[X])
    (agreements : Finset I) (k d D : Nat)
    (halign : EndpointAlignment6401 sigma v z)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements,
      P.eval (alpha i) = u₀ i + z * u₁ i)
    (hPdegree : P.natDegree ≤ k)
    (hAdegree : (fourLaneBasePolynomials6401 v).1.natDegree ≤ d)
    (hBdegree : (fourLaneBasePolynomials6401 v).2.natDegree ≤ d)
    (hproductCap : k + d ≤ D)
    (hRdegree :
      (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v).natDegree ≤ D)
    (hroots : D < agreements.card) :
    TwoLaneFailureRelation sigma alpha
      (fun i ↦ u₀ i + z * u₁ i - P.eval (alpha i))
      (fourLaneBasePolynomials6401 v).1
      (fourLaneBasePolynomials6401 v).2 := by
  apply failureRelation_of_lowDegree_receivedRepresentative6401
    sigma alpha (fun i ↦ u₀ i + z * u₁ i) P
      (fourLaneBasePolynomials6401 v).1
      (fourLaneBasePolynomials6401 v).2
      (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v)
      agreements D hfixed hagree
      (fourLaneReceivedRepresentative_eval_eq_alignedPair6401
        sigma alpha u₀ u₁ v z halign)
      hRdegree
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply (max_le ?_ ?_).trans hproductCap
    · apply Polynomial.natDegree_mul_le.trans
      have hmap : (P.map sigma).natDegree ≤ k :=
        Polynomial.natDegree_map_le.trans hPdegree
      omega
    · apply Polynomial.natDegree_mul_le.trans
      omega
  · exact hroots
theorem endpointAlignment_challenge_unique6401
    (sigma : F →+* F) (v : FourLaneTailVector6401 F) (z w : F)
    (hbase : (fourLaneBasePolynomials6401 v).1 ≠ 0 ∨
      (fourLaneBasePolynomials6401 v).2 ≠ 0)
    (hz : EndpointAlignment6401 sigma v z)
    (hw : EndpointAlignment6401 sigma v w) :
    z = w := by
  rcases hbase with hA | hB
  · have hmul :
        Polynomial.C (sigma z) * (fourLaneBasePolynomials6401 v).1 =
          Polynomial.C (sigma w) * (fourLaneBasePolynomials6401 v).1 :=
      hz.1.symm.trans hw.1
    have hC : Polynomial.C (sigma z) = Polynomial.C (sigma w) :=
      mul_right_cancel₀ hA hmul
    exact sigma.injective (Polynomial.C_injective hC)
  · have hmul :
        Polynomial.C z * (fourLaneBasePolynomials6401 v).2 =
          Polynomial.C w * (fourLaneBasePolynomials6401 v).2 :=
      hz.2.symm.trans hw.2
    have hC : Polynomial.C z = Polynomial.C w :=
      mul_right_cancel₀ hB hmul
    exact Polynomial.C_injective hC
theorem endpointAlignment_base_ne_zero_of_vector_ne_zero6401
    (sigma : F →+* F) (v : FourLaneTailVector6401 F) (z : F)
    (hv : v ≠ 0) (hz : EndpointAlignment6401 sigma v z) :
    (fourLaneBasePolynomials6401 v).1 ≠ 0 ∨
      (fourLaneBasePolynomials6401 v).2 ≠ 0 := by
  by_contra hbase
  push Not at hbase
  have hA₁ : (fourLaneDirectionPolynomials6401 v).1 = 0 := by
    rw [hz.1, hbase.1, mul_zero]
  have hB₁ : (fourLaneDirectionPolynomials6401 v).2 = 0 := by
    rw [hz.2, hbase.2, mul_zero]
  exact hv (fourLanePolynomials_all_zero_imp_vector_eq_zero6401
    v hbase.1 hA₁ hbase.2 hB₁)
theorem nonzero_endpointAlignment_challenge_unique6401
    (sigma : F →+* F) (v : FourLaneTailVector6401 F) (z w : F)
    (hv : v ≠ 0)
    (hz : EndpointAlignment6401 sigma v z)
    (hw : EndpointAlignment6401 sigma v w) :
    z = w :=
  endpointAlignment_challenge_unique6401 sigma v z w
    (endpointAlignment_base_ne_zero_of_vector_ne_zero6401 sigma v z hv hz)
    hz hw
theorem exists_semantic_shortFourLaneRelation_of_compression6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (k : Nat) (hwindow : k + 22507 < Fintype.card I)
    (hcompression : Module.finrank F
      (LinearMap.range
        (receivedEndpointFourLaneMap6401 sigma alpha u₀ u₁ k)) ≤ 45015) :
    ∃ v : FourLaneTailVector6401 F,
      v ≠ 0 ∧
      (fourLaneBasePolynomials6401 v).1.natDegree ≤ 11253 ∧
      (fourLaneDirectionPolynomials6401 v).1.natDegree ≤ 11253 ∧
      (fourLaneBasePolynomials6401 v).2.natDegree ≤ 11253 ∧
      (fourLaneDirectionPolynomials6401 v).2.natDegree ≤ 11253 ∧
      (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v).natDegree ≤
        k + 22507 := by
  have hcap : Module.finrank F
      (LinearMap.range
        (receivedEndpointFourLaneMap6401 sigma alpha u₀ u₁ k)) ≤
      tailCompressionImageCap6401 := by
    simpa [tailCompressionImageCap6401, tailLaneWidth6401] using hcompression
  obtain ⟨v, hv, hmap, hhigh⟩ :=
    exists_short_fourLaneRelation_of_range_finrank_le6401
      (receivedEndpointFourLaneMap6401 sigma alpha u₀ u₁ k) hcap
  obtain ⟨hA₀, hA₁, hB₀, hB₁⟩ :=
    fourLanePolynomials_degree_le_11253_6401 v hhigh
  exact ⟨v, hv, hA₀, hA₁, hB₀, hB₁,
    fourLaneReceivedRepresentative_degree_le_of_map_eq_zero6401
      sigma alpha u₀ u₁ k v hwindow hmap⟩
end Generic
open BCHKSTwoFrobeniusModuleAudit6401
def compressedShortPairDegree6401 : Nat := 11253
def compressedTailRepresentativeDegree6401 : Nat :=
  ownerDegreeCap6401 + 22507
def compressedMessageProductDegree6401 : Nat :=
  ownerDegreeCap6401 + compressedShortPairDegree6401
def compressedDegreeGap6401 : Nat :=
  compressedTailRepresentativeDegree6401 -
    compressedMessageProductDegree6401
theorem compressionSemantic_absorptionProfile_exact6401 :
    ownerDegreeCap6401 = 131071 ∧
      compressedShortPairDegree6401 = 11253 ∧
      compressedMessageProductDegree6401 = 142324 ∧
      compressedTailRepresentativeDegree6401 = 153578 ∧
      compressedDegreeGap6401 = 11254 ∧
      compressedTailRepresentativeDegree6401 < a6401 ∧
      a6401 - compressedTailRepresentativeDegree6401 = 31776 ∧
      2 * a6401 - n6401 = 108564 ∧
      (compressedTailRepresentativeDegree6401 + 1) -
          (2 * a6401 - n6401) = tailCompressionImageCap6401 := by
  native_decide
end BCHKSReceivedTailCompressionSemantic6401
end ProximityPrize.SubmissionLower
