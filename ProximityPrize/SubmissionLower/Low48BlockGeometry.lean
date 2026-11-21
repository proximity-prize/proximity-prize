import ProximityPrize.SubmissionLower.Low48AnchorSpace
import ProximityPrize.SubmissionLower.Low48RankCore
import ProximityPrize.SubmissionLower.Fast063

/- Use the homogeneous-block decomposition in K1_13_1_1 with the
   homogenizing degree supplied by the anchor cap. -/
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace Low48BlockGeometry
noncomputable section
open K1_13 K1_13_1_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Low48AnchorSpace
open scoped BigOperators
open private liftJets liftJets_X lift_value liftImage liftPower liftVar lift_order lift_value_order
  project_monomial jet_index_formula value_hom source_monomial_expr form_monomial_expr merge merge_single
  from ProximityPrize.SubmissionLower.Fast063

private abbrev Local := LocalPolynomial Geom 3
private abbrev T : Local := MvPolynomial.X (localT 3)
private def offset (i : Fin 141) : ℤ := (i : ℕ) - (50 : ℤ)

private abbrev selectedBlock (s : ℕ) (g : ℤ) :=
  Low48RankCore.blockAt (cap s) s g

private def postprocess (s : ℕ) (g : ℤ) : Form →ₗ[Geom] Local :=
  (projectLowContact 141).comp
    ((LinearMap.mulLeft Geom (T ^ (g + 50).toNat *
      (liftJets valueForm) ^ (s - cap s))).comp liftJets.toLinearMap)
private theorem postprocess_truncate (s : ℕ) (g : ℤ) (hg : -50 ≤ g) {P : Form}
    (hP : P.IsWeightedHomogeneous (fun _ => (1 : ℕ)) (cap s)) :
    postprocess s g (weightedTruncation targetOrder (Low48RankCore.orderCutoff s g).toNat P) =
      postprocess s g P := by
  let d := cap s
  let cutoff := (Low48RankCore.orderCutoff s g).toNat
  let H := filterSupport (fun e : Fin 4 →₀ ℕ => ¬ e.weight targetOrder < cutoff) P
  have hsplit : weightedTruncation targetOrder cutoff P + H = P :=
    filterSupport_add_filterSupport_not _ _
  have hH : H ∈ restrictWeightedOrder (fun j => 1 + targetOrder j) (d + cutoff) := by
    refine mem_restrictWeightedOrder.mpr fun e he => ?_
    have hc := mem_support_iff.mp he
    change (filterSupport _ P).coeff e ≠ 0 at hc
    rw [coeff_filterSupport] at hc
    by_cases hl : e.weight targetOrder < cutoff
    · simp [hl] at hc
    · have hd := hP (d := e) (by simpa [hl] using hc)
      rw [← Finsupp.degree_eq_weight_one] at hd
      have hw : e.weight (fun j => 1 + targetOrder j) = e.degree + e.weight targetOrder := by
        rw [Finsupp.degree_eq_sum, Finsupp.weight_eq_sum, Finsupp.weight_eq_sum,
          ← Finset.sum_add_distrib]
        simp [Nat.mul_add]
      rw [hw, hd]
      exact Nat.add_le_add_left (Nat.le_of_not_lt hl) d
  have ht : (T ^ (g + 50).toNat) ∈
      restrictWeightedOrder (localContactWeight 3) ((g + 50).toNat * 1) :=
    pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ _ (localContactWeight_T 3).ge) _
  have hf := pow_mem_restrictWeightedOrder lift_value_order (s - d)
  have hh := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder ht hf)
    (bind₁_mem_restrictWeightedOrder lift_order hH)
  have hc : 141 ≤ ((g + 50).toNat * 1 + (s-d) * 1) + (d + cutoff) := by
    have hd : d ≤ s := cap_le_grade s
    dsimp [cutoff, Low48RankCore.orderCutoff]
    omega
  have hz : postprocess s g H = 0 :=
    (weightedTruncation_eq_zero_iff _ _ _).mpr (restrictWeightedOrder_anti _ hc hh)
  calc
    postprocess s g (weightedTruncation targetOrder cutoff P) =
        postprocess s g (weightedTruncation targetOrder cutoff P + H) := by rw [map_add, hz, add_zero]
    _ = postprocess s g P := by rw [hsplit]
private def trimmed (u : JetVariable 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  u.some - Finsupp.single 0 (u.some.degree - cap u.some.degree)
private theorem trimmed_other (u : JetVariable 3 →₀ ℕ) (j : Fin 4) (h : j ≠ 0) :
    trimmed u j = u (some j) := by
  simp [trimmed, Ne.symm h]
private theorem trimmed_id (u : JetVariable 3 →₀ ℕ) :
    (trimmed u).weight jetIndex = u.some.weight jetIndex := by
  rw [jet_index_formula, jet_index_formula]
  rw [trimmed_other u 1 (by decide), trimmed_other u 2 (by decide), trimmed_other u 3 (by decide)]
  simp
private theorem trimmed_value_and_degree (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) :
    trimmed u 0 + (u.some.degree - cap u.some.degree) = u (some 0) ∧
      (trimmed u).degree = cap u.some.degree := by
  have htotal : u.some.degree = u (some 0) + u (some 1) + u (some 2) + u (some 3) := by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have hj : u (some 1) + u (some 2) + u (some 3) ≤ 50 := by
    have hi := hu.2.1
    change u.some.weight jetIndex ≤ 50 at hi
    rw [jet_index_formula] at hi
    simp only [Finsupp.some_apply] at hi
    omega
  have hcap := cap_of_grade hj (by omega) hu.2.2.2.1
  have htrim : trimmed u 0 =
      u (some 0) - (u.some.degree - cap u.some.degree) := by
    simp [trimmed]
  have hnew : (trimmed u).degree =
      trimmed u 0 + u (some 1) + u (some 2) + u (some 3) := by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_four, trimmed_other u 1 (by decide),
      trimmed_other u 2 (by decide), trimmed_other u 3 (by decide)]
  have hle := cap_le_grade u.some.degree
  omega
private theorem trimmed_mem_band (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) :
    BandExponent (cap u.some.degree) (-((u none : ℤ) - u.some.weight jetIndex))
      50 13 (trimmed u) := by
  refine ⟨(trimmed_value_and_degree u hu).2, ?_, ?_, ?_⟩
  · rw [trimmed_id]
    omega
  · rw [trimmed_id]
    exact_mod_cast hu.2.1
  · rw [trimmed_other u 3 (by decide)]
    exact hu.2.2.1
private theorem backShift_hom (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) (a : Geom) :
    (backShift (monomial (trimmed u) a)).IsWeightedHomogeneous
      (fun _ => (1 : ℕ)) (cap u.some.degree) := by
  have h := isWeightedHomogeneous_monomial (fun _ : Fin 4 => (1 : ℕ)) (trimmed u) a
    (m := cap u.some.degree)
    (by rw [← Finsupp.degree_eq_weight_one, (trimmed_value_and_degree u hu).2])
  apply h.bind₁
  intro j
  split_ifs
  · exact value_hom
  · exact isWeightedHomogeneous_X _ _ _
private theorem shifted_substitution (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) (a : Geom) :
    T ^ 50 * unscaledLocalSubstitution 3 0 0 (monomial u a) =
      T ^ (((u none : ℤ) - u.some.weight jetIndex) + 50).toNat *
        (liftJets valueForm) ^ (u.some.degree - cap u.some.degree) *
        liftJets (backShift (monomial (trimmed u) a)) := by
  have hi := hu.2.1
  change u.some.weight jetIndex ≤ 50 at hi
  let r := (((u none : ℤ) - u.some.weight jetIndex) + 50).toNat
  have ht : r + u.some.weight jetIndex = u none + 50 := by dsimp [r]; omega
  rw [jet_index_formula] at ht
  simp only [Finsupp.some_apply] at ht
  have hv := (trimmed_value_and_degree u hu).1
  have h1 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 1)) =
      MvPolynomial.X (localY (0 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 0
  have h2 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 2)) =
      MvPolynomial.X (localY (1 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 1
  have h3 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 3)) =
      MvPolynomial.X (localY (2 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 2
  have b0 : backShift (MvPolynomial.X 0) = valueForm := by simp [backShift]
  have b (j : Fin 4) (hj : j ≠ 0) : backShift (MvPolynomial.X j) = MvPolynomial.X j := by
    simp [backShift, hj]
  rw [source_monomial_expr, form_monomial_expr]
  simp only [map_mul, map_pow, algHom_C, algebraMap_eq, unscaledLocalSubstitution_X, map_zero,
    zero_add, ← lift_value, h1, h2, h3, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide),
    trimmed_other u 1 (by decide), trimmed_other u 2 (by decide), trimmed_other u 3 (by decide),
    liftJets_X]
  have hpow : T ^ r * T ^ u (some 1) * (T ^ 2) ^ u (some 2) * (T ^ 3) ^ u (some 3) =
      T ^ (u none + 50) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ = T ^ (u none + 50) * MvPolynomial.C a * liftJets valueForm ^ u (some 0) *
        MvPolynomial.X (localY (0 : Fin 3)) ^ u (some 1) *
        MvPolynomial.X (localY (1 : Fin 3)) ^ u (some 2) *
        MvPolynomial.X (localY (2 : Fin 3)) ^ u (some 3) := by rw [pow_add]; ring
    _ = _ := by
      rw [← hpow, ← hv, pow_add]
      simp [liftImage, liftPower, liftVar, mul_pow]
      ring
private theorem shift_projection (P : Local) :
    T ^ 50 * projectLowContact 91 P = projectLowContact 141 (T ^ 50 * P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      have hmul : T ^ 50 * monomial e a = monomial (Finsupp.single (localT 3) 50 + e) a := by
        rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, one_mul]
      rw [project_monomial, hmul, project_monomial]
      have ho : localContactOrder 3 (Finsupp.single (localT 3) 50 + e) =
          50 + localContactOrder 3 e := by
        simp [localContactOrder, Finsupp.weight_single]
      have hlt : localContactOrder 3 (Finsupp.single (localT 3) 50 + e) < 141 ↔
          localContactOrder 3 e < 91 := by rw [ho]; omega
      by_cases he : localContactOrder 3 e < 91
      · simp [he, hlt.mpr he, hmul]
      · have hnot : ¬ localContactOrder 3 (Finsupp.single (localT 3) 50 + e) < 141 :=
          fun h => he (hlt.mp h)
        simp [he, hnot]
  | add P Q hP hQ => simp only [map_add, mul_add, hP, hQ]
private theorem shifted_constraint_monomial (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u)
    (a : Geom) :
    let s := u.some.degree
    let g := (u none : ℤ) - u.some.weight jetIndex
    T ^ 50 * localConstraintAt 91 0 0 (monomial u a) =
      postprocess s g (selectedBlock s g ⟨monomial (trimmed u) a,
        (monomial_mem_restrictSupport (R := Geom)).mpr (Or.inl (trimmed_mem_band u hu))⟩) := by
  dsimp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [shift_projection, shifted_substitution u hu]
  have hi := hu.2.1
  change u.some.weight jetIndex ≤ 50 at hi
  let s := u.some.degree
  let g : ℤ := (u none : ℤ) - u.some.weight jetIndex
  let P := backShift (monomial (trimmed u) a)
  change postprocess s g P = postprocess s g
    (weightedTruncation targetOrder (Low48RankCore.orderCutoff s g).toNat P)
  exact (postprocess_truncate s g (by dsimp [g]; omega) (backShift_hom u hu a)).symm
private theorem selected_zero (s : ℕ) (g : ℤ) (h : 91 - (s : ℤ) ≤ g) :
    selectedBlock s g = 0 := by
  apply LinearMap.ext
  intro q
  change weightedTruncation targetOrder (Low48RankCore.orderCutoff s g).toNat (backShift q) = 0
  have hcut : (Low48RankCore.orderCutoff s g).toNat = 0 := by unfold Low48RankCore.orderCutoff; omega
  rw [hcut, weightedTruncation_eq_zero_iff, restrictWeightedOrder_zero]
  trivial
private abbrev Block := Fin 123 × Fin 141
private abbrev Image (b : Block) := LinearMap.range (selectedBlock b.1 (offset b.2))
private def assemble : (∀ b : Block, Image b) →ₗ[Geom] Local :=
  merge (fun b => postprocess b.1 (offset b.2))
private theorem postprocess_mem_assemble (b : Block) (s : ℕ) (g : ℤ)
    (hs : (b.1 : ℕ) = s) (hg : offset b.2 = g)
    (q : bandSpace (cap s) (-g) 50 13) :
    postprocess s g (selectedBlock s g q) ∈ LinearMap.range assemble := by
  subst s
  subst g
  let v : Image b := ⟨selectedBlock b.1 (offset b.2) q, LinearMap.mem_range_self _ q⟩
  exact ⟨Pi.single b v, merge_single (fun j : Block => postprocess j.1 (offset j.2)) b v⟩
private theorem shifted_monomial_mem_assemble (u : JetVariable 3 →₀ ℕ)
    (hu : AnchorEligible u) (a : Geom) :
    T ^ 50 * localConstraintAt 91 0 0 (monomial u a) ∈ LinearMap.range assemble := by
  classical
  let s := u.some.degree
  let g : ℤ := (u none : ℤ) - u.some.weight jetIndex
  let q : bandSpace (cap s) (-g) 50 13 :=
    ⟨monomial (trimmed u) a, (monomial_mem_restrictSupport (R := Geom)).mpr (Or.inl (trimmed_mem_band u hu))⟩
  have hmono : T ^ 50 * localConstraintAt 91 0 0 (monomial u a) =
      postprocess s g (selectedBlock s g q) := shifted_constraint_monomial u hu a
  rw [hmono]
  by_cases hg : g < 91
  · have hJ := hu.2.1
    change u.some.weight jetIndex ≤ 50 at hJ
    have hs : s < 123 := by exact Nat.lt_succ_of_le hu.1
    have hr : (g + 50).toNat < 141 := by dsimp [g] at *; omega
    let b : Block := (⟨s, hs⟩, ⟨(g + 50).toNat, hr⟩)
    have ho : offset b.2 = g := by dsimp [b, offset, g]; omega
    exact postprocess_mem_assemble b s g rfl ho q
  · rw [selected_zero s g (by omega), LinearMap.zero_apply, map_zero]
    exact Submodule.zero_mem _
theorem origin_le_blocks :
    Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤
      ∑ s : Fin 123, ∑ r : Fin 141,
        Module.finrank Geom (LinearMap.range (Low48RankCore.blockAt (cap s) s ((r : ℕ) - (50 : ℤ)))) := by
  classical
  let shift := LinearMap.mulLeft Geom (T ^ 50)
  have hshift : Function.Injective shift :=
    fun _ _ h => mul_left_cancel₀ (pow_ne_zero _ (MvPolynomial.X_ne_zero _)) h
  let shifted := shift.comp (anchorLocal 0 0)
  have hdim : Module.finrank Geom (LinearMap.range shifted) =
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
    rw [LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective shift hshift _).finrank_eq.symm
  have hsub : LinearMap.range shifted ≤ LinearMap.range assemble := by
    rintro _ ⟨Q, rfl⟩
    change shift (localConstraintAt 91 0 0 (Q : DifferentialPolynomial Geom 3)) ∈ _
    rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
    exact Submodule.sum_mem _ fun u hu => shifted_monomial_mem_assemble u (Q.property hu) _
  have (b : Block) : Module.Finite Geom (Image b) := by
    have : Module.Finite Geom (bandSpace (cap b.1) (-offset b.2) 50 13) :=
      restrictSupport_finite ((Finsupp.finite_of_degree_le _).subset fun _ he =>
        Nat.le_of_eq he.1)
    infer_instance
  calc
    _ = Module.finrank Geom (LinearMap.range shifted) := hdim.symm
    _ ≤ Module.finrank Geom (LinearMap.range assemble) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank Geom (∀ b : Block, Image b) := LinearMap.finrank_range_le assemble
    _ = _ := by
      rw [Module.finrank_pi_fintype, Fintype.sum_prod_type]
      rfl

#print axioms origin_le_blocks

end
end Low48BlockGeometry
