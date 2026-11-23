import ProximityPrize.SubmissionLower.SmallAnchor6960Rank
import ProximityPrize.SubmissionLower.Low50Anchor

set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

namespace SmallAnchor6960Local
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open SmallAnchor6960Space (gradeLimit gradeLimit_antitone cap_of_grade cap_active AnchorEligible anchorLocal anchorSpace)
open scoped BigOperators
open private exponent_le_of_mem_translation_monomial from ProximityPrize.SubmissionLower.Fast064

abbrev WideEligible:=AnchorEligible
abbrev wideSpace:=anchorSpace
abbrev wideLocal:=anchorLocal

/-- Bounds on jet exponents shared by both local anchor spaces. -/
def ShapeEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 137 ∧ u.some.weight (fun i => i.val) ≤ 56 ∧ u (some 3) ≤ 14 ∧
    u.some.degree ≤ gradeLimit (u (some 1)+u (some 2)+u (some 3))

private theorem shapeEligible (Q : wideSpace) {u} (hu : u ∈ (Q : DifferentialPolynomial Geom 3).support) :
    ShapeEligible u := by
  obtain ⟨hdeg,hidx,ht,htail,_⟩ := Q.property hu
  exact ⟨hdeg,hidx,ht,htail⟩

section
open MvPolynomial

private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 102)
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu:102≤u none) :
    localConstraintAt 102 0 0 (monomial u a)=0:=by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3)=monomial u a:=by
    rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_mul_monomial,one_mul,Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 102 0 0 _).mpr
  intro e he
  rw [map_mul,map_pow,unscaledLocalSubstitution,bind₁_X_right]
  simp only [unscaledLocalImage,MvPolynomial.C_0,zero_add,MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none≤e (localT 3)→False
  omega
private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 102 0 0 (truncateX Q)=localConstraintAt 102 0 0 Q:=by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 102 then monomial u (Q.coeff u) else 0:=by
    ext v
    rw [truncateX,coeff_filterSupport]
    by_cases h:u=v
    · subst v
      by_cases hx:u none < 102 <;> simp [hx]
    · by_cases hx:u none < 102 <;> simp [hx,MvPolynomial.coeff_monomial,h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero,origin_monomial_zero _ _ (by omega)]

private theorem centered {u v : JetVariable 3 →₀ ℕ}
    (h:v≤u) (hu:ShapeEligible u) (hx:v none < 102) :
    AnchorEligible v:=by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum,Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hi : v.some.weight (fun i => i.val) ≤ u.some.weight (fun i => i.val) := by
    rw [Finsupp.weight_eq_sum,Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right j.val (h (some j))
  obtain ⟨hdeg,hidx,ht,htail⟩:=hu
  have hsum:=add_le_add (add_le_add (h (some 1)) (h (some 2))) (h (some 3))
  refine ⟨hd.trans hdeg,hi.trans hidx,(h _).trans ht,hd.trans (htail.trans (gradeLimit_antitone hsum)),?_⟩
  have hw := Finsupp.weight_le_weight
    (w:=fun j:Fin 4 => 133499 - j.val) (w' := fun _ => 133499)
    (fun j => Nat.sub_le _ _) v.some
  have he : v.some.weight (fun _ => 133499) = 133499 * v.some.degree := by
    simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
      Finset.mul_sum,Nat.mul_comm]
  rw [he] at hw
  have hweight : differentialWeight (d := 3) 133499 =
      fun j => j.elim 1 (fun i => 133499 - i.val):=by
    funext j
    cases j <;> rfl
  rw [← Finsupp.optionElim_some v,hweight,Finsupp.weight_optionElim,one_mul]
  calc
    _ ≤ 101 + 133499 * 137 :=
      Nat.add_le_add (Nat.le_of_lt_succ hx)
        (hw.trans (Nat.mul_le_mul_left _ (hd.trans hdeg)))
    _≤_:=by decide
private theorem centered_in_space (x y : Geom) (Q : DifferentialPolynomial Geom 3)
    (hQ : ∀ u ∈ Q.support, ShapeEligible u) :
    truncateX (globalPointTranslation x y Q) ∈
      anchorSpace:=by
  classical
  rw [Q.as_sum,map_sum,map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn:=mem_support_iff.mp hv
  rw [truncateX,coeff_filterSupport] at hn
  split at hn
  · exact centered
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (hQ u hu) (by assumption)
  · exact (hn rfl).elim
theorem finite_of_weight (S : Set (JetVariable 3 →₀ ℕ)) (D B : ℕ) (hD : 3 < D)
    (h : ∀ u ∈ S, u.weight (differentialWeight D) ≤ B) :
    Module.Finite Geom (MvPolynomial.restrictSupport Geom S) := by
  have positive (j : JetVariable 3) : differentialWeight D j ≠ 0 := by
    cases j with
    | none =>
      change (1 : ℕ) ≠ 0
      exact Nat.one_ne_zero
    | some j =>
      have hj := j.isLt
      change D - j.val ≠ 0
      omega
  exact MvPolynomial.restrictSupport_finite <|
    (Finsupp.finite_of_nat_weight_le _ positive _).subset (fun u hu => h u hu)

theorem finiteWide : Module.Finite Geom wideSpace :=
  finite_of_weight _ 133499 _ (by decide) (fun _ hu => hu.2.2.2.2)

/-- Translate to the old origin chart and discard powers of X at least 102.
The input weight bound is not needed after this truncation. -/
theorem rank_of_shape (U : Submodule Geom (DifferentialPolynomial Geom 3))
    (hU : ∀ Q : U, ∀ u ∈ (Q : DifferentialPolynomial Geom 3).support, ShapeEligible u)
    (x y : Geom) :
    Module.finrank Geom (LinearMap.range ((localConstraintAt 102 x y).domRestrict U)) ≤
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)):=by
  letI : Module.Finite Geom anchorSpace := finiteWide
  let f : U →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict U
  let tr : U →ₗ[Geom] anchorSpace := f.codRestrict _ fun Q =>
    centered_in_space x y Q (hU Q)
  have he : (localConstraintAt 102 x y).domRestrict U = (anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 102 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 102 0 0 (truncateX (globalPointTranslation x y Q))
    rw [origin_truncateX,localConstraintAt_eq_zero_globalPointTranslation]
  rw [he]
  exact LinearMap.finrank_range_comp_le_left _ _

theorem rank_at_point_le_origin (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) :=
  rank_of_shape _ (fun Q _ h => shapeEligible Q h) x y

end

theorem per_position (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y))≤18553227 :=
  (rank_at_point_le_origin x y).trans SmallAnchor6960Rank.origin_rank

theorem shape_of_support (Q : DifferentialPolynomial Geom 3)
    (hQ : ∀ u ∈ Q.support, ShapeEligible u) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨137,56,14⟩:=by
  classical
  let P:Row 4:=MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, ShapeEligible (m.optionElim i) := by
    obtain ⟨i,hi⟩:=Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i,hQ _ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i,hi⟩:=hm m h
    simpa only [Finsupp.some_optionElim,Finsupp.degree_apply,Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i,hi⟩:=hm m h
    simpa only [Finsupp.some_optionElim,Finsupp.weight_apply,smul_eq_mul,Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 14
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i,hi⟩:=hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1

theorem active_of_support (Q : DifferentialPolynomial Geom 3)
    (hQ : ∀ u ∈ Q.support, ShapeEligible u) :
    Low50Anchor.ActiveFits (MvPolynomial.optionEquivRight Geom (Fin 4) Q) 172:=by
  classical
  let P:Row 4:=MvPolynomial.optionEquivRight Geom (Fin 4) Q
  intro m hm
  obtain ⟨i,hi⟩:=Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hm)
  have h : ShapeEligible (m.optionElim i) := hQ _ (MvPolynomial.mem_support_iff.mpr (by
    rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff]))
  have hd:=h.1
  have hl:=h.2.2.2
  have hw:=h.2.1
  simp only [Finsupp.optionElim_apply_some] at hl
  rw [Finsupp.some_optionElim] at hd hw
  have hdeg : m.degree = m 0 + m 1 + m 2 + m 3 := by
    rw [Finsupp.degree_eq_sum,Fin.sum_univ_four]
  have hweight : m.weight (fun i : Fin 4 => i.val) = m 1 + 2 * m 2 + 3 * m 3 := by
    rw [Finsupp.weight_eq_sum,Fin.sum_univ_four]
    simp [Nat.mul_comm,Nat.add_assoc]
  change m.weight (fun i:Fin 4 => i.val)≤56 at hw
  rw [hweight] at hw
  have hc := cap_of_grade (s := m.degree) (t := m 1 + m 2 + m 3)
    (by omega) (by omega) (by simpa [Finsupp.some_optionElim] using hl)
  have hb:=cap_active _ hd
  omega

theorem shape_bound (Q : wideSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨137,56,14⟩ :=
  shape_of_support Q (fun _ h => shapeEligible Q h)

theorem active_bound (Q : wideSpace) :
    Low50Anchor.ActiveFits (MvPolynomial.optionEquivRight Geom (Fin 4) Q) 172 :=
  active_of_support Q (fun _ h => shapeEligible Q h)

theorem rawWeight (Q : wideSpace) :
    differentialWeightedDegree 133499 (Q : DifferentialPolynomial Geom 3) ≤
      102*179876 - 1+56:=by
  rw [differentialWeightedDegree,MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
  exact fun m hm => (Q.property hm).2.2.2.2

#print axioms per_position
#print axioms shape_bound
#print axioms active_bound

end
end SmallAnchor6960Local
