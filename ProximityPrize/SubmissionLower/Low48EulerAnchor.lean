import ProximityPrize.SubmissionLower.Low48EulerColumns
import ProximityPrize.SubmissionLower.Low48AnchorLocal
import ProximityPrize.SubmissionLower.Low48Rank

set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Low48EulerAnchor
noncomputable section
open K1 (I K node)
open K1_13 (Geom embed extend Row shape InBox atJet)
open Low48AnchorSpace (anchorSpace anchorLocal)
open Low48EulerColumns (Differential Marker column column_mem column_degree columns_independent)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial
open private atJet_unflatten from ProximityPrize.SubmissionLower.Fast040

private def source : Submodule Geom Differential := Submodule.span Geom (Set.range column)

private theorem source_le : source ≤ anchorSpace :=
  Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact column_mem i)

private theorem marker_finite : Finite Marker := by
  apply Nat.finite_of_card_ne_zero
  rw [Low48EulerDimension.source_card]
  decide

private theorem source_finite : Module.Finite Geom source := by
  letI := marker_finite
  exact Module.Finite.span_of_finite Geom (Set.finite_range column)

theorem source_room : 262144 * 11098186 < Module.finrank Geom source := by
  letI := marker_finite
  letI := Fintype.ofFinite Marker
  letI := source_finite
  let gen (i : Marker) : source := ⟨column i,Submodule.subset_span (Set.mem_range_self i)⟩
  have hli : LinearIndependent Geom gen := columns_independent.of_comp source.subtype
  have hc : Fintype.card Marker = 2909327354270 := by
    rw [← Nat.card_eq_fintype_card]
    exact Low48EulerDimension.source_card
  exact (show 262144 * 11098186 < Fintype.card Marker by rw [hc]; decide).trans_le
    hli.fintype_card_le_finrank

private theorem specialized_degree (Q : source) (S : Geom[X])
    (hS : S.natDegree ≤ 133426) :
    (differentialSpecialization Q.val S).natDegree < 92 * 179915 := by
  let eval := (differentialSpecializationHom (d := 3) S).toLinearMap
  have hdegree (p : Differential) (hp : p ∈ source) : (eval p).natDegree < 92 * 179915 := by
    induction hp using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨i,rfl⟩ := hq
      exact column_degree i S hS
    | zero => rw [map_zero, Polynomial.natDegree_zero]; decide
    | add q r _ _ hq hr =>
      rw [map_add]
      exact (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hq hr)
    | smul c q _ hq =>
      rw [map_smul]
      exact (Polynomial.natDegree_smul_le _ _).trans_lt hq
  exact hdegree Q.val Q.property

/-- A nonzero equation for every polynomial with at least 179915 agreements. -/
theorem exists_anchor (w : I → K) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨123,50,13⟩ ∧
      differentialWeightedDegree 133426 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) <
        92 * 179915 + 50 ∧
      ∀ (S : K[X]) (T : Finset I), S.natDegree ≤ 133426 → 179915 ≤ T.card →
        (∀ i ∈ T, S.eval (node i) = w i) → atJet P (extend S) = 0 := by
  letI := source_finite
  have hpositive (j : JetVariable 3) : differentialWeight 133426 j ≠ 0 := by
    cases j with
    | none => decide
    | some j => have hj := j.isLt; change 133426 - j.val ≠ 0; omega
  have : Module.Finite Geom anchorSpace :=
    MvPolynomial.restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ h => h.2.2.2.2
  let incl : source →ₗ[Geom] anchorSpace := Submodule.inclusion source_le
  let rows (i : I) := (anchorLocal (embed (node i)) (embed (w i))).comp incl
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (rows i))) ≤ 262144 * 11098186 := calc
    _ ≤ ∑ _ : I, (11098186 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (LinearMap.finrank_range_comp_le_left _ _).trans
        (Low48AnchorLocal.per_position Low48Rank.origin_rank _ _)
    _ = _ := by simp
  obtain ⟨Q,hQ,hlocal⟩ := LinearMap.exists_ne_zero_of_sum_finrank_range_lt rows (hr.trans_lt source_room)
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q.val
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  have hcut : differentialWeightedDegree 133426 Q.val ≤ 92 * 179915 + 50 - 1 := by
    rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
    exact fun e he => ((incl Q).property he).2.2.2.2
  refine ⟨P,hP,Low48AnchorLocal.shape_bound (incl Q),?_,?_⟩
  · simpa only [P,AlgEquiv.symm_apply_apply] using hcut.trans_lt (by decide :
      92 * 179915 + 50 - 1 < 92 * 179915 + 50)
  · intro S T hd hT hits
    rw [atJet_unflatten]
    have hd' : (extend S).natDegree ≤ 133426 := Polynomial.natDegree_map_le.trans hd
    refine Low48EulerJets.contact_zero (m := 92) (fun i => embed (node i)) (fun i => embed (w i)) T
      (extend S) ?_ ?_ ((RingHom.injective embed).comp node.injective).injOn hT ?_
    · simpa only [P,AlgEquiv.symm_apply_apply] using specialized_degree Q (extend S) hd'
    · intro i _
      change (rows i) Q = 0
      exact hlocal i
    · intro i hi
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, hits i hi]

#print axioms exists_anchor

end
end Low48EulerAnchor
