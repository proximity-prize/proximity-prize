import ProximityPrize.SubmissionLower.R6961Low6961AnchorDimension

set_option Elab.async false
set_option maxHeartbeats 300000
set_option linter.style.haveILetI false
set_option maxRecDepth 10000

namespace Low6961Anchor
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Low6961AnchorColumns Low6961AnchorLocal
open scoped BigOperators
open K1_13_1 (atJet_unflatten)

private abbrev Slot := {u : Ex // ColumnEligible u}

private theorem independent_dp : LinearIndependent Geom (fun u : Slot => column u.val) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c he i hi
  by_contra hn
  let F := s.filter (fun i => c i ≠ 0)
  have hF : F.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩⟩
  obtain ⟨j, hj, hm⟩ := F.exists_max_image (fun u => jidx u.val) hF
  have hj' := Finset.mem_filter.mp hj
  have hcoeff := congrArg (fun p : DP => p.coeff j.val) he
  change (∑ i ∈ s, c i • column i.val).coeff j.val = (0 : DP).coeff j.val at hcoeff
  rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero,
    Finset.sum_eq_single_of_mem j hj'.1] at hcoeff
  · rw [MvPolynomial.coeff_smul, smul_eq_mul] at hcoeff
    exact (mul_ne_zero hj'.2 (column_coeff j.val)) hcoeff
  · intro k hk hkj
    rw [MvPolynomial.coeff_smul]
    by_cases hc : c k = 0
    · simp [hc]
    · have hne : j.val ≠ k.val := fun h => hkj (Subtype.ext h.symm)
      have hi := hm k (Finset.mem_filter.mpr ⟨hk,hc⟩)
      simp [column_lower k.val j.val hne hi]

private def source : Submodule Geom DP := Submodule.span Geom
    (Set.range fun u : Slot => column u.val)

private theorem source_le_wide : source ≤ wideSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u,rfl⟩
  exact column_wide u.property

private theorem dim_source : Module.finrank Geom source = 4342187385853 := by
  classical
  obtain ⟨e⟩ := Low6961AnchorDimension.eligible_card
  letI : Fintype Slot := Fintype.ofEquiv _ e.symm
  rw [source,finrank_span_eq_card independent_dp,Fintype.card_congr e,Fintype.card_fin]

private theorem source_eval (Q : source) (S : (Polynomial Geom)) (hs : S.natDegree ≤ 133397) :
    (differentialSpecialization (Q.val : DP) S).natDegree ≤ 99*179818-1 := by
  change (differentialSpecializationHom S Q.val).natDegree ≤ _
  let f := (differentialSpecializationHom (d := 3) S).toLinearMap
  change (f Q.val).natDegree ≤ _
  have hq : Q.val ∈ Submodule.span Geom (Set.range fun u : Slot => column u.val) := Q.property
  refine Submodule.span_induction (p := fun p _ => (f p).natDegree ≤ 99 * 179818 - 1) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨u,rfl⟩
    exact column_eval_degree S u.property hs
  · rw [map_zero]
    simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact (Polynomial.natDegree_add_le (f a) (f b)).trans (max_le ha hb)
  · intro a p _ hp
    rw [map_smul]
    exact (Polynomial.natDegree_smul_le _ _).trans hp

private def row (w : I → K) (i : I) : source →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 99 (embed (node i)) (embed (w i))).domRestrict _

private theorem row_rank (w : I → K) (i : I) :
    Module.finrank Geom (LinearMap.range (row w i)) ≤ 16564024 := by
  letI : Module.Finite Geom wideSpace := finiteWide
  let L := wideLocal (embed (node i)) (embed (w i))
  have hle : LinearMap.range (row w i) ≤ LinearMap.range L := by
    rintro _ ⟨Q,rfl⟩
    exact ⟨⟨Q.val,source_le_wide Q.property⟩,rfl⟩
  have hfin : Module.finrank Geom (LinearMap.range (row w i)) ≤
      Module.finrank Geom (LinearMap.range L) := Submodule.finrank_mono hle
  exact hfin.trans (per_position (embed (node i)) (embed (w i)))

private theorem exists_local (w : I → K) :
    ∃ Q : source, Q ≠ 0 ∧ ∀ i, row w i Q = 0 := by
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (row w i))) ≤ 262144 * 16564024 := calc
    _ ≤ ∑ _ : I, (16564024 : ℕ) := Finset.sum_le_sum fun i _ => row_rank w i
    _ = _ := by simp
  have hroom : 262144 * 16564024 < Module.finrank Geom source := by
    rw [dim_source]
    decide
  exact LinearMap.exists_ne_zero_of_sum_finrank_range_lt (row w) (hr.trans_lt hroom)

/-- The Euler anchor at the actual low endpoint, using the published local-rank witnesses. -/
theorem exists_anchor (w : I → K) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨132,55,14⟩ ∧ Low50Anchor.ActiveFits P 165 ∧
      differentialWeightedDegree 133397 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) ≤
        99 * 179818 - 1 + 55 ∧
      ∀ (S : (Polynomial K)) (T : Finset I), S.natDegree ≤ 133397 → 179818 ≤ T.card →
        (∀ i ∈ T, S.eval (node i) = w i) → atJet P (extend S) = 0 := by
  classical
  obtain ⟨Q,hQ,hloc⟩ := exists_local w
  let V : wideSpace := ⟨Q.val, source_le_wide Q.property⟩
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q.val
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  refine ⟨P,hP,shape_bound V,active_bound V,?_,?_⟩
  · simpa only [P,AlgEquiv.symm_apply_apply] using rawWeight V
  · intro S T hd hT hits
    rw [atJet_unflatten]
    have hS : (extend S).natDegree ≤ 133397 := Polynomial.natDegree_map_le.trans hd
    have hdeg := (source_eval Q (extend S) hS).trans_lt (by decide : 99*179818-1 < 99*179818)
    have heval (i : I) (hi : i ∈ T) : (extend S).eval (embed (node i)) = embed (w i) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, hits i hi]
    exact eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      (fun i => embed (node i)) T 99 179818
      ((RingHom.injective embed).comp node.injective).injOn hT
      (fun i hi => X_sub_C_pow_dvd_differentialSpecialization_of_contact
        Q.val (extend S) (embed (node i)) (embed (w i)) (heval i hi) (hloc i)) hdeg

/-- The actual low-band model and marks supply the same single anchor. -/
theorem anchor_of_family {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179818 M Γ)
    (hi : M.overhead ≤ 2326) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨132,55,14⟩ ∧ Low50Anchor.ActiveFits P 165 ∧
      differentialWeightedDegree 133397 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) ≤
        99*179818-1+55 ∧ ∀ γ∈Γ,atJet P (extend (F.scalar γ))=0 := by
  obtain ⟨P,nz,box,active,weight,zero⟩ := exists_anchor M.word
  refine ⟨P,nz,box,active,weight,?_⟩
  intro γ hγ
  let mark := F.mark γ hγ
  have degree : (F.scalar γ).natDegree ≤ 133397 := by
    rcases mark.scalar_degree with z | h
    · simp [z]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
      omega
  exact zero _ mark.bad.support degree mark.bad.agreement mark.scalar_hits

#print axioms exists_anchor
#print axioms anchor_of_family
end
end Low6961Anchor
