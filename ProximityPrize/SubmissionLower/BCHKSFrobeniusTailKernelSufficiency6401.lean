import ProximityPrize.SubmissionLower.BCHKSSubfieldFrobenius6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusKeyEquationFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusTailKernelSufficiency6401
open Polynomial
open BCHKSSubfieldFrobenius6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
section Generic
variable {F I : Type*} [Field F] [DecidableEq I]
theorem failureRelation_of_lowDegree_receivedRepresentative6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (u : I → F) (P A B R : F[X]) (agreements : Finset I) (D : Nat)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements, P.eval (alpha i) = u i)
    (hR : ∀ i, R.eval (alpha i) =
      A.eval (alpha i) * sigma (u i) - B.eval (alpha i) * u i)
    (hRdegree : R.natDegree ≤ D)
    (hAPdegree : (A * P.map sigma - B * P).natDegree ≤ D)
    (hroots : D < agreements.card) :
    TwoLaneFailureRelation sigma alpha
      (fun i ↦ u i - P.eval (alpha i)) A B := by
  have hpoly : R = A * P.map sigma - B * P := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
      R (A * P.map sigma - B * P) (agreements.map alpha)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      rw [hR i, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_mul,
        eval_map_eq_map_eval_of_fixed sigma P (alpha i) (hfixed i),
        hagree i hi]
    · rw [Finset.card_map]
      exact (max_le hRdegree hAPdegree).trans_lt hroots
  intro i
  have hi := congrArg (fun Q : F[X] ↦ Q.eval (alpha i)) hpoly
  rw [hR i, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_mul,
    eval_map_eq_map_eval_of_fixed sigma P (alpha i) (hfixed i)] at hi
  dsimp only
  rw [map_sub]
  linear_combination hi
theorem failureRelation_of_tailRepresentative_degreeBounds6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (u : I → F) (P A B R : F[X]) (agreements : Finset I)
    (k d : Nat)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements, P.eval (alpha i) = u i)
    (hR : ∀ i, R.eval (alpha i) =
      A.eval (alpha i) * sigma (u i) - B.eval (alpha i) * u i)
    (hPdegree : P.natDegree ≤ k)
    (hAdegree : A.natDegree ≤ d)
    (hBdegree : B.natDegree ≤ d)
    (hRdegree : R.natDegree ≤ k + d)
    (hroots : k + d < agreements.card) :
    TwoLaneFailureRelation sigma alpha
      (fun i ↦ u i - P.eval (alpha i)) A B := by
  apply failureRelation_of_lowDegree_receivedRepresentative6401
    sigma alpha u P A B R agreements (k + d)
    hfixed hagree hR hRdegree
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans <| by
        have hmap : (P.map sigma).natDegree ≤ k :=
          Polynomial.natDegree_map_le.trans hPdegree
        omega
    · exact Polynomial.natDegree_mul_le.trans (by omega)
  · exact hroots
end Generic
section InterpolatedTail
variable {F I : Type*} [Field F] [Fintype I] [Nonempty I] [DecidableEq I]
noncomputable def receivedPairInterpolant6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (A B : F[X]) : F[X] :=
  Lagrange.interpolate Finset.univ alpha fun i ↦
    A.eval (alpha i) * sigma (u i) - B.eval (alpha i) * u i
theorem receivedPairInterpolant_eval6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (A B : F[X]) (i : I) :
    (receivedPairInterpolant6401 sigma alpha u A B).eval (alpha i) =
      A.eval (alpha i) * sigma (u i) - B.eval (alpha i) * u i := by
  exact Lagrange.eval_interpolate_at_node _ alpha.injective.injOn
    (Finset.mem_univ i)
theorem receivedPairInterpolant_natDegree_lt_card6401
    (sigma : F →+* F) (alpha : I ↪ F) (u : I → F)
    (A B : F[X]) :
    (receivedPairInterpolant6401 sigma alpha u A B).natDegree <
      Fintype.card I := by
  let R := receivedPairInterpolant6401 sigma alpha u A B
  by_cases hR : R = 0
  · simpa [R, hR] using (Fintype.card_pos : 0 < Fintype.card I)
  · rw [Polynomial.natDegree_lt_iff_degree_lt hR]
    have hdegree := Lagrange.degree_interpolate_lt (s := Finset.univ)
      (fun i ↦ A.eval (alpha i) * sigma (u i) -
        B.eval (alpha i) * u i) alpha.injective.injOn
    rw [Finset.card_univ] at hdegree
    exact hdegree
theorem failureRelation_of_receivedPairInterpolant_degree6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (u : I → F) (P A B : F[X]) (agreements : Finset I)
    (k d : Nat)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements, P.eval (alpha i) = u i)
    (hPdegree : P.natDegree ≤ k)
    (hAdegree : A.natDegree ≤ d)
    (hBdegree : B.natDegree ≤ d)
    (htail : (receivedPairInterpolant6401 sigma alpha u A B).natDegree ≤
      k + d)
    (hroots : k + d < agreements.card) :
    TwoLaneFailureRelation sigma alpha
      (fun i ↦ u i - P.eval (alpha i)) A B := by
  exact failureRelation_of_tailRepresentative_degreeBounds6401
    sigma alpha u P A B
      (receivedPairInterpolant6401 sigma alpha u A B)
      agreements k d hfixed hagree
      (receivedPairInterpolant_eval6401 sigma alpha u A B)
      hPdegree hAdegree hBdegree htail hroots
theorem receivedPairInterpolant_eq_messageProduct6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (u : I → F) (P A B : F[X]) (k d : Nat)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hPdegree : P.natDegree ≤ k)
    (hAdegree : A.natDegree ≤ d)
    (hBdegree : B.natDegree ≤ d)
    (hwindow : k + d < Fintype.card I)
    (hfailure : TwoLaneFailureRelation sigma alpha
      (fun i ↦ u i - P.eval (alpha i)) A B) :
    receivedPairInterpolant6401 sigma alpha u A B =
      A * P.map sigma - B * P := by
  let R := receivedPairInterpolant6401 sigma alpha u A B
  let Q := A * P.map sigma - B * P
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    R Q ((Finset.univ : Finset I).map alpha)
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    rw [receivedPairInterpolant_eval6401,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
      eval_map_eq_map_eval_of_fixed sigma P (alpha i) (hfixed i)]
    have hf := hfailure i
    dsimp only at hf
    rw [map_sub] at hf
    linear_combination hf
  · rw [Finset.card_map, Finset.card_univ]
    apply max_lt
    · exact receivedPairInterpolant_natDegree_lt_card6401
        sigma alpha u A B
    · apply lt_of_le_of_lt _ hwindow
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact Polynomial.natDegree_mul_le.trans <| by
          have hmap : (P.map sigma).natDegree ≤ k :=
            Polynomial.natDegree_map_le.trans hPdegree
          omega
      · exact Polynomial.natDegree_mul_le.trans (by omega)
theorem receivedPairInterpolant_degree_iff_failureRelation6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (u : I → F) (P A B : F[X]) (agreements : Finset I)
    (k d : Nat)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ i ∈ agreements, P.eval (alpha i) = u i)
    (hPdegree : P.natDegree ≤ k)
    (hAdegree : A.natDegree ≤ d)
    (hBdegree : B.natDegree ≤ d)
    (hwindow : k + d < Fintype.card I)
    (hroots : k + d < agreements.card) :
    (receivedPairInterpolant6401 sigma alpha u A B).natDegree ≤ k + d ↔
      TwoLaneFailureRelation sigma alpha
        (fun i ↦ u i - P.eval (alpha i)) A B := by
  constructor
  · intro htail
    exact failureRelation_of_receivedPairInterpolant_degree6401
      sigma alpha u P A B agreements k d hfixed hagree
      hPdegree hAdegree hBdegree htail hroots
  · intro hfailure
    rw [receivedPairInterpolant_eq_messageProduct6401
      sigma alpha u P A B k d hfixed hPdegree hAdegree hBdegree
      hwindow hfailure]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans <| by
        have hmap : (P.map sigma).natDegree ≤ k :=
          Polynomial.natDegree_map_le.trans hPdegree
        omega
    · exact Polynomial.natDegree_mul_le.trans (by omega)
end InterpolatedTail
theorem benchmark_tailSufficiency_margin6401 :
    ownerDegreeCap6401 + 22507 < a6401 ∧
      a6401 - (ownerDegreeCap6401 + 22507) = 31776 := by
  native_decide
end BCHKSFrobeniusTailKernelSufficiency6401
end ProximityPrize.SubmissionLower
