import ProximityPrize.SubmissionLower.RankTotal82190
import ProximityPrize.SubmissionLower.AnchorDimension82190
import ProximityPrize.SubmissionLower.AnchorGeometry82190

set_option Elab.async false
set_option maxHeartbeats 1200000
namespace LowAnchor82190
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open AnchorSpace82190 AnchorGeometry82190
open scoped BigOperators
open private atJet_unflatten from ProximityPrize.SubmissionLower.Fast040

private instance : Profile where
  deg := fun s _ => Pascal82190.degree s
  le_grade := fun s _ => min_le_left _ _
  fits u hu := by
    have ht : u (some 1) + u (some 2) + u (some 3) ≤ u.some.degree := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
      simp only [Finsupp.some_apply]
      omega
    have hj := hu.2.1
    change u.some.weight jetIndex ≤ 48 at hj
    rw [jetIndex_formula] at hj
    simp only [Finsupp.some_apply] at hj
    apply le_min ht
    exact cap_of_grade (by omega) hu.2.2.2.1

theorem per_position (x y : Geom) :
    Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤ 9513882 :=
  (rank_at_point_le_origin x y).trans (rank_origin_le_sum.trans RankCharge82190.total_rank)

theorem margin :
    Module.finrank Geom anchorSpace - 262144 * 9513882 = 17195980 := by
  rw [anchor_finrank]

private theorem shape_bound (Q : anchorSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨120, 48, 12⟩ := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, AnchorEligible (m.optionElim i) := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i, hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.degree_apply, Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 12
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1

/-- One nonzero differential equation annihilates every message with this many agreements. -/
theorem exists_anchor (w : I → K) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨120,48,12⟩ ∧
      differentialWeightedDegree 133419 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) <
        90 * 179954 ∧
      ∀ (S : K[X]) (T : Finset I), S.natDegree ≤ 133419 → 179954 ≤ T.card →
        (∀ i ∈ T, S.eval (node i) = w i) → atJet P (extend S) = 0 := by
  let rows (i : I) := anchorLocal (embed (node i)) (embed (w i))
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (rows i))) ≤ 262144 * 9513882 := calc
    _ ≤ ∑ _ : I, (9513882 : ℕ) := Finset.sum_le_sum fun i _ => per_position _ _
    _ = _ := by simp
  have hroom : 262144 * 9513882 < Module.finrank Geom anchorSpace := by
    rw [anchor_finrank]
    decide
  obtain ⟨Q, hQ, hlocal⟩ := LinearMap.exists_ne_zero_of_sum_finrank_range_lt rows (hr.trans_lt hroom)
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  have hdeg : differentialWeightedDegree 133419 (Q : DifferentialPolynomial Geom 3) <
      90 * 179954 := by
    have hw : differentialWeightedDegree 133419 (Q : DifferentialPolynomial Geom 3) ≤
        90 * 179954 - 1 := by
      rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
      exact fun m hm => (Q.property hm).2.2.2.2
    exact lt_of_le_of_lt hw (by decide)
  refine ⟨P, hP, shape_bound Q, ?_, ?_⟩
  · simpa only [P, AlgEquiv.symm_apply_apply] using hdeg
  · intro S T hd hT hits
    rw [atJet_unflatten]
    have hS : (extend S).natDegree ≤ 133419 := Polynomial.natDegree_map_le.trans hd
    refine differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
      (fun i => embed (node i)) (fun i => embed (w i)) T hdeg
      (fun i _ => hlocal i) _ hS
      ((RingHom.injective embed).comp node.injective).injOn hT ?_
    intro i hi
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, hits i hi]

#print axioms exists_anchor
end
end LowAnchor82190
