import ProximityPrize.SubmissionLower.BCHKSReceivedTailCompressionSemantic6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSReceivedTailCompressionTwoOwner6401
open Polynomial
open BCHKSSubfieldFrobenius6401
open BCHKSReceivedTailCompressionSemantic6401
open BCHKSReceivedTailCompressionShortRelation6401
open BCHKSTwoFrobeniusModuleAudit6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
section Generic
variable {F I : Type*} [Field F] [Fintype I] [Nonempty I]
  [DecidableEq I]
noncomputable def reconstructedBasePolynomial6401
    (r s : F) (Pᵣ Pₛ : F[X]) : F[X] :=
  Polynomial.C (s - r)⁻¹ *
    (Polynomial.C s * Pᵣ - Polynomial.C r * Pₛ)
noncomputable def reconstructedDirectionPolynomial6401
    (r s : F) (Pᵣ Pₛ : F[X]) : F[X] :=
  Polynomial.C (s - r)⁻¹ * (Pₛ - Pᵣ)
theorem reconstructedBasePolynomial_eval6401
    (r s x u₀ u₁ : F) (Pᵣ Pₛ : F[X]) (hrs : r ≠ s)
    (hPᵣ : Pᵣ.eval x = u₀ + r * u₁)
    (hPₛ : Pₛ.eval x = u₀ + s * u₁) :
    (reconstructedBasePolynomial6401 r s Pᵣ Pₛ).eval x = u₀ := by
  have hsr : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  simp only [reconstructedBasePolynomial6401, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, hPᵣ, hPₛ]
  field_simp [hsr]
  ring
theorem reconstructedDirectionPolynomial_eval6401
    (r s x u₀ u₁ : F) (Pᵣ Pₛ : F[X]) (hrs : r ≠ s)
    (hPᵣ : Pᵣ.eval x = u₀ + r * u₁)
    (hPₛ : Pₛ.eval x = u₀ + s * u₁) :
    (reconstructedDirectionPolynomial6401 r s Pᵣ Pₛ).eval x = u₁ := by
  have hsr : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  simp only [reconstructedDirectionPolynomial6401, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, hPᵣ, hPₛ]
  field_simp [hsr]
  ring
theorem reconstructedBasePolynomial_natDegree_le6401
    (r s : F) (Pᵣ Pₛ : F[X]) (k : Nat)
    (hPᵣ : Pᵣ.natDegree ≤ k) (hPₛ : Pₛ.natDegree ≤ k) :
    (reconstructedBasePolynomial6401 r s Pᵣ Pₛ).natDegree ≤ k := by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le
    ((Polynomial.natDegree_C_mul_le _ _).trans hPᵣ)
    ((Polynomial.natDegree_C_mul_le _ _).trans hPₛ)
theorem reconstructedDirectionPolynomial_natDegree_le6401
    (r s : F) (Pᵣ Pₛ : F[X]) (k : Nat)
    (hPᵣ : Pᵣ.natDegree ≤ k) (hPₛ : Pₛ.natDegree ≤ k) :
    (reconstructedDirectionPolynomial6401 r s Pᵣ Pₛ).natDegree ≤ k := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_sub_le _ _).trans (max_le hPₛ hPᵣ))
noncomputable def fourLaneTwoOwnerMessageProduct6401
    (sigma : F →+* F) (v : FourLaneTailVector6401 F)
    (r s : F) (Pᵣ Pₛ : F[X]) : F[X] :=
  let P₀ := reconstructedBasePolynomial6401 r s Pᵣ Pₛ
  let P₁ := reconstructedDirectionPolynomial6401 r s Pᵣ Pₛ
  (fourLaneBasePolynomials6401 v).1 * P₀.map sigma +
      (fourLaneDirectionPolynomials6401 v).1 * P₁.map sigma -
    ((fourLaneBasePolynomials6401 v).2 * P₀ +
      (fourLaneDirectionPolynomials6401 v).2 * P₁)
theorem fourLaneTwoOwnerMessageProduct_natDegree_le6401
    (sigma : F →+* F) (v : FourLaneTailVector6401 F)
    (r s : F) (Pᵣ Pₛ : F[X]) (k d : Nat)
    (hPᵣ : Pᵣ.natDegree ≤ k) (hPₛ : Pₛ.natDegree ≤ k)
    (hA₀ : (fourLaneBasePolynomials6401 v).1.natDegree ≤ d)
    (hA₁ : (fourLaneDirectionPolynomials6401 v).1.natDegree ≤ d)
    (hB₀ : (fourLaneBasePolynomials6401 v).2.natDegree ≤ d)
    (hB₁ : (fourLaneDirectionPolynomials6401 v).2.natDegree ≤ d) :
    (fourLaneTwoOwnerMessageProduct6401 sigma v r s Pᵣ Pₛ).natDegree
      ≤ k + d := by
  have hP₀ := reconstructedBasePolynomial_natDegree_le6401
    r s Pᵣ Pₛ k hPᵣ hPₛ
  have hP₁ := reconstructedDirectionPolynomial_natDegree_le6401
    r s Pᵣ Pₛ k hPᵣ hPₛ
  have hP₀map :
      ((reconstructedBasePolynomial6401 r s Pᵣ Pₛ).map sigma).natDegree
        ≤ k := Polynomial.natDegree_map_le.trans hP₀
  have hP₁map :
      ((reconstructedDirectionPolynomial6401 r s Pᵣ Pₛ).map sigma).natDegree
        ≤ k := Polynomial.natDegree_map_le.trans hP₁
  dsimp [fourLaneTwoOwnerMessageProduct6401]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le <;> apply Polynomial.natDegree_mul_le.trans <;> omega
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le <;> apply Polynomial.natDegree_mul_le.trans <;> omega
theorem fourLaneReceivedRepresentative_eval_eq_twoOwnerProduct6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (v : FourLaneTailVector6401 F) (r s : F) (Pᵣ Pₛ : F[X])
    (hrs : r ≠ s) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (i : I)
    (hPᵣ : Pᵣ.eval (alpha i) = u₀ i + r * u₁ i)
    (hPₛ : Pₛ.eval (alpha i) = u₀ i + s * u₁ i) :
    (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v).eval
        (alpha i) =
      (fourLaneTwoOwnerMessageProduct6401 sigma v r s Pᵣ Pₛ).eval
        (alpha i) := by
  let P₀ := reconstructedBasePolynomial6401 r s Pᵣ Pₛ
  let P₁ := reconstructedDirectionPolynomial6401 r s Pᵣ Pₛ
  have hP₀eval : P₀.eval (alpha i) = u₀ i := by
    exact reconstructedBasePolynomial_eval6401
      r s (alpha i) (u₀ i) (u₁ i) Pᵣ Pₛ hrs hPᵣ hPₛ
  have hP₁eval : P₁.eval (alpha i) = u₁ i := by
    exact reconstructedDirectionPolynomial_eval6401
      r s (alpha i) (u₀ i) (u₁ i) Pᵣ Pₛ hrs hPᵣ hPₛ
  rw [fourLaneReceivedRepresentative_eval6401]
  dsimp [fourLaneTwoOwnerMessageProduct6401, P₀, P₁]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul]
  rw [eval_map_eq_map_eval_of_fixed sigma
      (reconstructedBasePolynomial6401 r s Pᵣ Pₛ) (alpha i) (hfixed i),
    eval_map_eq_map_eval_of_fixed sigma
      (reconstructedDirectionPolynomial6401 r s Pᵣ Pₛ) (alpha i) (hfixed i),
    hP₀eval, hP₁eval]
  ring
theorem fourLaneReceivedRepresentative_eq_twoOwnerProduct6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (v : FourLaneTailVector6401 F) (r s : F) (Pᵣ Pₛ : F[X])
    (common : Finset I) (k d D : Nat)
    (hrs : r ≠ s) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hPᵣagree : ∀ i ∈ common,
      Pᵣ.eval (alpha i) = u₀ i + r * u₁ i)
    (hPₛagree : ∀ i ∈ common,
      Pₛ.eval (alpha i) = u₀ i + s * u₁ i)
    (hPᵣdegree : Pᵣ.natDegree ≤ k) (hPₛdegree : Pₛ.natDegree ≤ k)
    (hA₀ : (fourLaneBasePolynomials6401 v).1.natDegree ≤ d)
    (hA₁ : (fourLaneDirectionPolynomials6401 v).1.natDegree ≤ d)
    (hB₀ : (fourLaneBasePolynomials6401 v).2.natDegree ≤ d)
    (hB₁ : (fourLaneDirectionPolynomials6401 v).2.natDegree ≤ d)
    (hRdegree :
      (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v).natDegree ≤ D)
    (hproductCap : k + d ≤ D) (hroots : D < common.card) :
    fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v =
      fourLaneTwoOwnerMessageProduct6401 sigma v r s Pᵣ Pₛ := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    (fourLaneReceivedRepresentative6401 sigma alpha u₀ u₁ v)
    (fourLaneTwoOwnerMessageProduct6401 sigma v r s Pᵣ Pₛ)
    (common.map alpha)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact fourLaneReceivedRepresentative_eval_eq_twoOwnerProduct6401
      sigma alpha u₀ u₁ v r s Pᵣ Pₛ hrs hfixed i
        (hPᵣagree i hi) (hPₛagree i hi)
  · rw [Finset.card_map]
    apply (max_le hRdegree ?_).trans_lt hroots
    exact (fourLaneTwoOwnerMessageProduct_natDegree_le6401
      sigma v r s Pᵣ Pₛ k d hPᵣdegree hPₛdegree
        hA₀ hA₁ hB₀ hB₁).trans hproductCap
end Generic
end BCHKSReceivedTailCompressionTwoOwner6401
end ProximityPrize.SubmissionLower
