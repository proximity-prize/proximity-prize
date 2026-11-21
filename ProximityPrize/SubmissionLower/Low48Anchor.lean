import ProximityPrize.SubmissionLower.Low48AnchorDimension

set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

namespace Low48Anchor
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Low48AnchorSpace Low48AnchorDimension
open scoped BigOperators
open private atJet_unflatten from ProximityPrize.SubmissionLower.Fast040
open private P0_9_1.truncateX P0_9_1.origin_truncateX from ProximityPrize.SubmissionLower.PortLowBase
open private exponent_le_of_mem_translation_monomial from ProximityPrize.SubmissionLower.Fast064

section
open MvPolynomial

private theorem centered {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : AnchorEligible u) (hx : v none < 90) :
    AnchorEligible v := by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hi : v.some.weight (fun i => i.val) ≤ u.some.weight (fun i => i.val) := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right j.val (h (some j))
  obtain ⟨hdeg,hidx,ht,htail,_⟩ := hu
  have hsum := add_le_add (add_le_add (h (some 1)) (h (some 2))) (h (some 3))
  refine ⟨hd.trans hdeg,hi.trans hidx,(h _).trans ht,hd.trans (htail.trans (gradeLimit_antitone hsum)),?_⟩
  have hw := Finsupp.weight_le_weight
    (w := fun j : Fin 4 => 133426 - j.val) (w' := fun _ => 133426)
    (fun j => Nat.sub_le _ _) v.some
  have he : v.some.weight (fun _ => 133426) = 133426 * v.some.degree := by
    simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
      Finset.mul_sum, Nat.mul_comm]
  rw [he] at hw
  have hweight : differentialWeight (d := 3) 133426 =
      fun j => j.elim 1 (fun i => 133426 - i.val) := by
    funext j
    cases j <;> rfl
  rw [← Finsupp.optionElim_some v, hweight, Finsupp.weight_optionElim, one_mul]
  calc
    _ ≤ 89 + 133426 * 121 :=
      Nat.add_le_add (Nat.le_of_lt_succ hx)
        (hw.trans (Nat.mul_le_mul_left _ (hd.trans hdeg)))
    _ ≤ _ := by decide
private theorem centered_in_space (x y : Geom) (Q : anchorSpace) :
    P0_9_1.truncateX (globalPointTranslation x y (Q : DifferentialPolynomial Geom 3)) ∈
      anchorSpace := by
  classical
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn := mem_support_iff.mp hv
  rw [P0_9_1.truncateX, coeff_filterSupport] at hn
  split at hn
  · exact centered
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (Q.property hu) (by assumption)
  · exact (hn rfl).elim
/-- Centering and truncating the ordinary variable bounds local rank for every physical weight. -/
theorem rank_at_point_le_origin (x y : Geom) :
    Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
  have hpositive (j : JetVariable 3) : differentialWeight 133426 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133426 - j.val ≠ 0
      omega
  have : Module.Finite Geom anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let f : anchorSpace →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (P0_9_1.truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict anchorSpace
  let tr : anchorSpace →ₗ[Geom] anchorSpace := f.codRestrict _ fun Q =>
    centered_in_space x y Q
  have he : anchorLocal x y = (anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 90 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 90 0 0 (P0_9_1.truncateX (globalPointTranslation x y Q))
    rw [P0_9_1.origin_truncateX,localConstraintAt_eq_zero_globalPointTranslation]
  rw [he]
  exact LinearMap.finrank_range_comp_le_left _ _

end

theorem per_position
    (hRank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 10053422)
    (x y : Geom) :
    Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤ 10053422 :=
  (rank_at_point_le_origin x y).trans hRank

theorem margin :
    Module.finrank Geom anchorSpace - 262144 * 10053422 = 108644306 := by
  rw [anchor_finrank]

private theorem shape_bound (Q : anchorSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨121, 49, 13⟩ := by
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
  · change P.degreeOf 3 ≤ 13
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1

/-- One nonzero differential equation annihilates every message with this many agreements. -/
theorem exists_anchor
    (hRank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 10053422) (w : I → K) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨121,49,13⟩ ∧
      differentialWeightedDegree 133426 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) <
        90 * 179935 ∧
      ∀ (S : K[X]) (T : Finset I), S.natDegree ≤ 133426 → 179935 ≤ T.card →
        (∀ i ∈ T, S.eval (node i) = w i) → atJet P (extend S) = 0 := by
  let rows (i : I) := anchorLocal (embed (node i)) (embed (w i))
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (rows i))) ≤ 262144 * 10053422 := calc
    _ ≤ ∑ _ : I, (10053422 : ℕ) := Finset.sum_le_sum fun i _ => per_position hRank _ _
    _ = _ := by simp
  have hroom : 262144 * 10053422 < Module.finrank Geom anchorSpace := by
    rw [anchor_finrank]
    decide
  obtain ⟨Q, hQ, hlocal⟩ := LinearMap.exists_ne_zero_of_sum_finrank_range_lt rows (hr.trans_lt hroom)
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  have hdeg : differentialWeightedDegree 133426 (Q : DifferentialPolynomial Geom 3) <
      90 * 179935 := by
    have hw : differentialWeightedDegree 133426 (Q : DifferentialPolynomial Geom 3) ≤
        90 * 179935 - 1 := by
      rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
      exact fun m hm => (Q.property hm).2.2.2.2
    exact lt_of_le_of_lt hw (by decide)
  refine ⟨P, hP, shape_bound Q, ?_, ?_⟩
  · simpa only [P, AlgEquiv.symm_apply_apply] using hdeg
  · intro S T hd hT hits
    rw [atJet_unflatten]
    have hS : (extend S).natDegree ≤ 133426 := Polynomial.natDegree_map_le.trans hd
    refine differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
      (fun i => embed (node i)) (fun i => embed (w i)) T hdeg
      (fun i _ => hlocal i) _ hS
      ((RingHom.injective embed).comp node.injective).injOn hT ?_
    intro i hi
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, hits i hi]

#print axioms rank_at_point_le_origin
#print axioms exists_anchor
end
end Low48Anchor
