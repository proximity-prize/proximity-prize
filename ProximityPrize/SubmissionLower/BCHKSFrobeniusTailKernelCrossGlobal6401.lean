import ProximityPrize.SubmissionLower.BCHKSFrobeniusTailFixedMinor6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusFailurePairRankOne6401
import ProximityPrize.SubmissionLower.BCHKSQuadraticKernel6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusTailKernelCrossGlobal6401
open Polynomial
open BCHKSFrobeniusGraphInjectivity6401
open BCHKSFrobeniusFailurePairRankOne6401
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusKeyEquationFork6401
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
noncomputable def globalTailPairPolynomial6401
    {F : Type*} [Field F] (d : Nat)
    (V : Fin (d + 1) ⊕ Fin (d + 1) → F[X]) : F[X][X] × F[X][X] :=
  (∑ j : Fin (d + 1),
      Polynomial.C (V (Sum.inl j)) * Polynomial.X ^ (j : Nat),
    ∑ j : Fin (d + 1),
      Polynomial.C (V (Sum.inr j)) * Polynomial.X ^ (j : Nat))
theorem globalTailPairPolynomial_map6401
    {F : Type*} [Field F] (d : Nat)
    (V : Fin (d + 1) ⊕ Fin (d + 1) → F[X]) (z : F) :
    ((globalTailPairPolynomial6401 d V).1.map (Polynomial.evalRingHom z),
      (globalTailPairPolynomial6401 d V).2.map (Polynomial.evalRingHom z)) =
      tailPairPolynomial d (fun c ↦ Polynomial.eval z (V c)) := by
  apply Prod.ext
  · change (∑ j : Fin (d + 1),
        Polynomial.C (V (Sum.inl j)) * Polynomial.X ^ (j : Nat)).map
          (Polynomial.evalRingHom z) =
      ∑ j : Fin (d + 1),
        Polynomial.C (Polynomial.eval z (V (Sum.inl j))) *
          Polynomial.X ^ (j : Nat)
    ext n
    simp [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp_all
  · change (∑ j : Fin (d + 1),
        Polynomial.C (V (Sum.inr j)) * Polynomial.X ^ (j : Nat)).map
          (Polynomial.evalRingHom z) =
      ∑ j : Fin (d + 1),
        Polynomial.C (Polynomial.eval z (V (Sum.inr j))) *
          Polynomial.X ^ (j : Nat)
    ext n
    simp [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp_all
theorem globalTailPairPolynomial_coeffDegreeLE6401
    {F : Type*} [Field F] (d D : Nat)
    (V : Fin (d + 1) ⊕ Fin (d + 1) → F[X])
    (hV : ∀ c, (V c).natDegree ≤ D) :
    BivariateCoeffDegreeLE (globalTailPairPolynomial6401 d V).1 D ∧
      BivariateCoeffDegreeLE (globalTailPairPolynomial6401 d V).2 D := by
  constructor
  · change BivariateCoeffDegreeLE
      (∑ j : Fin (d + 1),
        Polynomial.C (V (Sum.inl j)) * Polynomial.X ^ (j : Nat)) D
    apply BivariateCoeffDegreeLE_sum
    intro j n
    simp only [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact hV (Sum.inl j)
    · simp
  · change BivariateCoeffDegreeLE
      (∑ j : Fin (d + 1),
        Polynomial.C (V (Sum.inr j)) * Polynomial.X ^ (j : Nat)) D
    apply BivariateCoeffDegreeLE_sum
    intro j n
    simp only [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact hV (Sum.inr j)
    · simp
noncomputable def globalTailPairCross6401
    {F : Type*} [Field F] (d : Nat)
    (V W : Fin (d + 1) ⊕ Fin (d + 1) → F[X]) : F[X][X] :=
  (globalTailPairPolynomial6401 d V).1 *
      (globalTailPairPolynomial6401 d W).2 -
    (globalTailPairPolynomial6401 d W).1 *
      (globalTailPairPolynomial6401 d V).2
theorem globalTailPairCross_coeffDegreeLE6401
    {F : Type*} [Field F] (d D : Nat)
    (V W : Fin (d + 1) ⊕ Fin (d + 1) → F[X])
    (hV : ∀ c, (V c).natDegree ≤ D)
    (hW : ∀ c, (W c).natDegree ≤ D) :
    BivariateCoeffDegreeLE (globalTailPairCross6401 d V W) (D + D) := by
  intro n
  unfold globalTailPairCross6401
  rw [Polynomial.coeff_sub]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (BivariateCoeffDegreeLE_mul
      (globalTailPairPolynomial_coeffDegreeLE6401 d D V hV).1
      (globalTailPairPolynomial_coeffDegreeLE6401 d D W hW).2) n
  · exact (BivariateCoeffDegreeLE_mul
      (globalTailPairPolynomial_coeffDegreeLE6401 d D W hW).1
      (globalTailPairPolynomial_coeffDegreeLE6401 d D V hV).2) n
theorem globalTailPairCross_map6401
    {F : Type*} [Field F] (d : Nat)
    (V W : Fin (d + 1) ⊕ Fin (d + 1) → F[X]) (z : F) :
    (globalTailPairCross6401 d V W).map (Polynomial.evalRingHom z) =
      failurePairCross
        (tailPairPolynomial d (fun c ↦ Polynomial.eval z (V c))).1
        (tailPairPolynomial d (fun c ↦ Polynomial.eval z (V c))).2
        (tailPairPolynomial d (fun c ↦ Polynomial.eval z (W c))).1
        (tailPairPolynomial d (fun c ↦ Polynomial.eval z (W c))).2 := by
  unfold globalTailPairCross6401 failurePairCross
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul]
  have hV := globalTailPairPolynomial_map6401 d V z
  have hW := globalTailPairPolynomial_map6401 d W z
  have hV₀ := congrArg Prod.fst hV
  have hV₁ := congrArg Prod.snd hV
  have hW₀ := congrArg Prod.fst hW
  have hW₁ := congrArg Prod.snd hW
  simp only at hV₀ hV₁ hW₀ hW₁
  rw [hV₀, hV₁, hW₀, hW₁]
theorem globalTailPairCross_eq_zero_of_specializations6401
    {F : Type*} [Field F] [DecidableEq F] (d D : Nat)
    (V W : Fin (d + 1) ⊕ Fin (d + 1) → F[X])
    (hV : ∀ c, (V c).natDegree ≤ D)
    (hW : ∀ c, (W c).natDegree ≤ D)
    (S : Finset F) (hmass : D + D < S.card)
    (hzero : ∀ z ∈ S,
      (globalTailPairCross6401 d V W).map
        (Polynomial.evalRingHom z) = 0) :
    globalTailPairCross6401 d V W = 0 := by
  by_contra hne
  have hcard :=
    BCHKSQuadraticKernel6400.specialization_zero_card_le_degreeX
      (globalTailPairCross6401 d V W) S hne
  have hfilter :
      (S.filter fun z ↦
        (globalTailPairCross6401 d V W).map
          (Polynomial.evalRingHom z) = 0) = S := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.1
    · intro hz
      exact ⟨hz, hzero z hz⟩
  rw [hfilter] at hcard
  have hdegree :
      Polynomial.Bivariate.degreeX (globalTailPairCross6401 d V W) ≤
        D + D := by
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro n hn
    exact globalTailPairCross_coeffDegreeLE6401 d D V W hV hW n
  omega
theorem globalTailPairCross_eq_zero_of_ownerFailureRelations6401
    {F : Type*} [Field F] [DecidableEq F] {t : Nat}
    (sigma : F →+* F) (d D : Nat)
    (V W : Fin (d + 1) ⊕ Fin (d + 1) → F[X])
    (hVdegree : ∀ c, (V c).natDegree ≤ D)
    (hWdegree : ∀ c, (W c).natDegree ≤ D)
    (S : Finset F) (hmass : D + D < S.card)
    (alpha : F → Fin t ↪ F) (E : F → Fin t → F)
    (hE : ∀ z ∈ S, ∀ i, E z i ≠ 0)
    (hVrel : ∀ z ∈ S,
      TwoLaneFailureRelation sigma (alpha z) (E z)
        (tailPairPolynomial d (fun c ↦ Polynomial.eval z (V c))).1
        (tailPairPolynomial d (fun c ↦ Polynomial.eval z (V c))).2)
    (hWrel : ∀ z ∈ S,
      TwoLaneFailureRelation sigma (alpha z) (E z)
        (tailPairPolynomial d (fun c ↦ Polynomial.eval z (W c))).1
        (tailPairPolynomial d (fun c ↦ Polynomial.eval z (W c))).2)
    (herrors : d + d < t) :
    globalTailPairCross6401 d V W = 0 := by
  apply globalTailPairCross_eq_zero_of_specializations6401
    d D V W hVdegree hWdegree S hmass
  intro z hz
  rw [globalTailPairCross_map6401]
  exact failurePairCross_eq_zero_of_two_mul_degree_lt_card
    sigma (alpha z) (E z)
      (tailPairPolynomial d (fun c ↦ Polynomial.eval z (V c))).1
      (tailPairPolynomial d (fun c ↦ Polynomial.eval z (V c))).2
      (tailPairPolynomial d (fun c ↦ Polynomial.eval z (W c))).1
      (tailPairPolynomial d (fun c ↦ Polynomial.eval z (W c))).2
      d (hE z hz)
      (tailPairPolynomial_fst_natDegree_le d _)
      (tailPairPolynomial_snd_natDegree_le d _)
      (tailPairPolynomial_fst_natDegree_le d _)
      (tailPairPolynomial_snd_natDegree_le d _)
      (hVrel z hz) (hWrel z hz) herrors
theorem receivedTail_fixedMinorCross_exceptionCap6401 :
    2 * ((2 * 22507 + 1) *
      BCHKSTwoFrobeniusModuleAudit6401.q6401) = 191827500162990 ∧
    191827500162990 < 80251881527475554 := by
  native_decide
end BCHKSFrobeniusTailKernelCrossGlobal6401
end ProximityPrize.SubmissionLower
