import ProximityPrize.SubmissionLower.AlignmentScalarListBridge

/-!
# Actual moment-curve separation and finite interleaved lists

Model label: gpt-5.

A nonzero coordinate-difference polynomial is constructed for each unequal
pair of r-row words. Its root set has at most r-1 elements. A union over
the actual two-element subsets gives the binomial pair bound, and hence
an actual moment-curve parameter separating the finite family.

The finite interleaved-list corollary uses the verified scalar bridge.
No separator, root-count estimate, or intermediate list bound is assumed.
No Code.Lambda or new ProtocolClaim is asserted; the 6400 candidate is
untouched.
-/

namespace ProximityPrize.SubmissionLower.AlignmentMomentCurveProjection

open scoped BigOperators

noncomputable section Proofs

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable {r : ℕ}

/-- The coefficients of an r-row value, in increasing moment-curve order. -/
def rowPolynomial (v : Fin r → F) : Polynomial F :=
  ∑ j : Fin r, Polynomial.monomial j.val (v j)

theorem rowPolynomial_coeff (v : Fin r → F) (j : Fin r) :
    (rowPolynomial v).coeff j.val = v j := by
  classical
  rw [rowPolynomial, Polynomial.finsetSum_coeff]
  calc
    (∑ k : Fin r, (Polynomial.monomial k.val (v k)).coeff j.val) =
        (Polynomial.monomial j.val (v j)).coeff j.val := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        have hval : k.val ≠ j.val := fun hh => hkj (Fin.ext hh)
        simp [Polynomial.coeff_monomial, hval, Ne.symm hval]
      · intro hnot
        exact (hnot (Finset.mem_univ j)).elim
    _ = v j := by simp [Polynomial.coeff_monomial]

theorem rowPolynomial_injective :
    Function.Injective (rowPolynomial : (Fin r → F) → Polynomial F) := by
  intro v u heq
  funext j
  have hc := congrArg (fun P : Polynomial F => P.coeff j.val) heq
  simpa only [rowPolynomial_coeff] using hc

theorem rowPolynomial_natDegree_le (v : Fin r → F) :
    (rowPolynomial v).natDegree ≤ r - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  have hterm := Polynomial.natDegree_monomial_le (v j) (m := j.val)
  have hj := j.isLt
  exact hterm.trans (by omega)

/-- The actual projection, not an existentially assumed linear functional. -/
def momentProjection (t : F) (v : ι → Fin r → F) : ι → F :=
  fun i => (rowPolynomial (v i)).eval t

theorem momentProjection_apply (t : F) (v : ι → Fin r → F) (i : ι) :
    momentProjection t v i = ∑ j : Fin r, t ^ j.val * v i j := by
  change (Polynomial.evalRingHom t)
      (∑ j : Fin r, Polynomial.monomial j.val (v i j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (Polynomial.monomial j.val (v i j)).eval t = t ^ j.val * v i j
  rw [Polynomial.eval_monomial, mul_comm]

/-- One explicit coordinate-difference polynomial controls every collision
of two unequal words under the actual moment projection. -/
theorem exists_nonzero_coordinate_difference
    (v u : ι → Fin r → F) (hne : v ≠ u) :
    ∃ P : Polynomial F, P ≠ 0 ∧ P.natDegree ≤ r - 1 ∧
      ∀ t : F, momentProjection t v = momentProjection t u → P.eval t = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : ι, v i ≠ u i := by
    by_contra hno
    push_neg at hno
    exact hne (funext hno)
  refine ⟨rowPolynomial (v i) - rowPolynomial (u i), ?_, ?_, ?_⟩
  · apply sub_ne_zero.mpr
    intro hh
    exact hi (rowPolynomial_injective hh)
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (rowPolynomial_natDegree_le _) (rowPolynomial_natDegree_le _))
  · intro t ht
    rw [Polynomial.eval_sub]
    exact sub_eq_zero.mpr (congrFun ht i)

/-- All parameters at which some unequal members of this finite pair collide. -/
def pairCollisionSeeds (pair : Finset (ι → Fin r → F)) : Finset F := by
  classical
  exact Finset.univ.filter (fun t => ∃ v ∈ pair, ∃ u ∈ pair,
    v ≠ u ∧ momentProjection t v = momentProjection t u)

theorem mem_pairCollisionSeeds_iff
    (pair : Finset (ι → Fin r → F)) (t : F) :
    t ∈ pairCollisionSeeds pair ↔ ∃ v ∈ pair, ∃ u ∈ pair,
      v ≠ u ∧ momentProjection t v = momentProjection t u := by
  classical
  simp only [pairCollisionSeeds, Finset.mem_filter, Finset.mem_univ, true_and]

theorem pairCollisionSeeds_card_le
    (pair : Finset (ι → Fin r → F)) (hpair : pair.card = 2) :
    (pairCollisionSeeds pair).card ≤ r - 1 := by
  classical
  letI : DecidableEq (ι → Fin r → F) := Classical.decEq (ι → Fin r → F)
  obtain ⟨v, u, hne, rfl⟩ := Finset.card_eq_two.mp hpair
  obtain ⟨P, hP, hdegree, heval⟩ := exists_nonzero_coordinate_difference v u hne
  have hcard : (pairCollisionSeeds ({v, u} : Finset (ι → Fin r → F))).card ≤
      P.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    apply (Polynomial.mem_roots hP).mpr
    apply heval t
    have ht' : t ∈ pairCollisionSeeds ({v, u} : Finset (ι → Fin r → F)) := ht
    obtain ⟨a, ha, b, hb, hab, habproj⟩ :=
      (mem_pairCollisionSeeds_iff ({v, u} : Finset (ι → Fin r → F)) t).mp ht'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact habproj
    · exact habproj.symm
    · exact (hab rfl).elim
  exact hcard.trans hdegree

def allCollisionSeeds (L : Finset (ι → Fin r → F)) : Finset F := by
  classical
  exact (L.powersetCard 2).biUnion pairCollisionSeeds

theorem allCollisionSeeds_card_le (L : Finset (ι → Fin r → F)) :
    (allCollisionSeeds L).card ≤ (r - 1) * L.card.choose 2 := by
  classical
  calc
    (allCollisionSeeds L).card ≤
        ∑ pair ∈ L.powersetCard 2, (pairCollisionSeeds pair).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _pair ∈ L.powersetCard 2, (r - 1) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact pairCollisionSeeds_card_le pair (Finset.mem_powersetCard.mp hpair).2
    _ = (L.powersetCard 2).card * (r - 1) := by simp
    _ = (r - 1) * L.card.choose 2 := by
      rw [Finset.card_powersetCard, Nat.mul_comm]

/-- A single actual field parameter separates every member of L.
The union bound counts unordered pairs exactly once. -/
theorem exists_separating_moment_parameter
    (L : Finset (ι → Fin r → F))
    (hfield : (r - 1) * L.card.choose 2 < Fintype.card F) :
    ∃ t : F, Set.InjOn (momentProjection (ι := ι) (r := r) t)
      (L : Set (ι → Fin r → F)) := by
  classical
  letI : DecidableEq (ι → Fin r → F) := Classical.decEq (ι → Fin r → F)
  have hsmall : (allCollisionSeeds L).card < Fintype.card F :=
    (allCollisionSeeds_card_le L).trans_lt hfield
  obtain ⟨t, ht⟩ : ∃ t : F, t ∉ allCollisionSeeds L := by
    by_contra hno
    have hsub : Finset.univ ⊆ allCollisionSeeds L := by
      intro t _
      by_contra ht
      exact hno ⟨t, ht⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ] at hc
    omega
  refine ⟨t, ?_⟩
  intro v hv u hu hproj
  change v ∈ L at hv
  change u ∈ L at hu
  by_contra hne
  apply ht
  apply Finset.mem_biUnion.mpr
  refine ⟨{v, u}, ?_, ?_⟩
  · apply Finset.mem_powersetCard.mpr
    constructor
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact hv
      · exact hu
    · simp [hne]
  · apply (mem_pairCollisionSeeds_iff ({v, u} : Finset (ι → Fin r → F)) t).mpr
    exact ⟨v, by simp, u, by simp, hne, hproj⟩

theorem momentProjection_mem_code
    (C : LinearCode ι F) (t : F) (v : ι → Fin r → F)
    (hrows : ∀ j : Fin r, (fun i => v i j) ∈ C) :
    momentProjection t v ∈ C := by
  classical
  have heq : momentProjection t v =
      ∑ j : Fin r, t ^ j.val • (fun i => v i j) := by
    funext i
    rw [momentProjection_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact C.sum_mem (fun j _ => C.smul_mem (t ^ j.val) (hrows j))

theorem momentProjection_preserves_agreements
    (t : F) (v u : ι → Fin r → F) :
    (Finset.univ.filter (fun i => v i = u i)) ⊆
      Finset.univ.filter (fun i => momentProjection t v i = momentProjection t u i) := by
  classical
  intro i hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
  have hv := (Finset.mem_filter.mp hi).2
  change (rowPolynomial (v i)).eval t = (rowPolynomial (u i)).eval t
  rw [hv]

/-- Actual finite interleaved-list bound, from strong scalar alignment.
Both field-size inequalities are explicit; no strong interleaved
alignment premise or assumed separating map is used. -/
theorem interleaved_finite_list_card_le
    (C : LinearCode ι F) (e w B : ℕ)
    (hzero : AlignmentScalarListBridge.ZeroCoordinateBound C w)
    (hgap : w < Fintype.card ι - e)
    (halign : AffineLineAlignmentBound C e B)
    (hfield : B < Fintype.card F)
    (hseparation : (r - 1) * (B + 1).choose 2 < Fintype.card F)
    (u : ι → Fin r → F) (L : Finset (ι → Fin r → F))
    (hrows : ∀ v ∈ L, ∀ j : Fin r, (fun i => v i j) ∈ C)
    (hclose : ∀ v ∈ L,
      Fintype.card ι - e ≤ (Finset.univ.filter (fun i => v i = u i)).card) :
    L.card ≤ B := by
  classical
  letI : DecidableEq (ι → Fin r → F) := Classical.decEq (ι → Fin r → F)
  letI : DecidableEq (ι → F) := Classical.decEq (ι → F)
  by_contra hnot
  obtain ⟨D, hDL, hDcard⟩ :=
    Finset.exists_subset_card_eq (show B + 1 ≤ L.card by omega)
  have hsepD : (r - 1) * D.card.choose 2 < Fintype.card F := by
    rw [hDcard]
    exact hseparation
  obtain ⟨t, ht⟩ := exists_separating_moment_parameter D hsepD
  let projected : Finset (ι → F) := D.image (momentProjection (ι := ι) (r := r) t)
  have hprojcard : projected.card = D.card := Finset.card_image_of_injOn ht
  have hcode : ∀ c ∈ projected, c ∈ C := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact momentProjection_mem_code C t v (hrows v (hDL hv))
  have hnear : ∀ c ∈ projected,
      Fintype.card ι - e ≤
        (Finset.univ.filter (fun i => c i = momentProjection t u i)).card := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact (hclose v (hDL hv)).trans
      (Finset.card_le_card (momentProjection_preserves_agreements t v u))
  have hbound := AlignmentScalarListBridge.finite_list_card_le C e w B
    hzero hgap halign hfield (momentProjection t u) projected hcode hnear
  rw [hprojcard, hDcard] at hbound
  omega

end Proofs

#print axioms rowPolynomial_coeff
#print axioms rowPolynomial_injective
#print axioms rowPolynomial_natDegree_le
#print axioms momentProjection_apply
#print axioms exists_nonzero_coordinate_difference
#print axioms pairCollisionSeeds_card_le
#print axioms allCollisionSeeds_card_le
#print axioms exists_separating_moment_parameter
#print axioms momentProjection_mem_code
#print axioms momentProjection_preserves_agreements
#print axioms interleaved_finite_list_card_le

end ProximityPrize.SubmissionLower.AlignmentMomentCurveProjection
