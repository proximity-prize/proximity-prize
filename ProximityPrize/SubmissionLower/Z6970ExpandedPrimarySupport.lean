import ProximityPrize.SubmissionLower.Z6970ExpandedColumns

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000

namespace ExpandedPrimary6970

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open MvPolynomial (mem_support_iff monomial)
open ExpandedColumns6970
open ExpandedTaper6970 (cap)
open scoped BigOperators

open P0_9_2 (weight_eq_sum map_independent_family pointContact high_monomial_vanishes)
open ExpandedColumns6970 (sumCount sumIndex sumDifferentiated sumGrade sumOld)

def primaryBox : Shape := ⟨4024, 1679, 500⟩

def TrueWeightLE {n : ℕ} (D : ℕ) (P : Row n) (T : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree + m.sum (fun i a => (D - i.val) * a) ≤ T

def JetsBounded (P : Row 4) : Prop := ∀ m ∈ P.support, m ∈ jetExponents

theorem row_bounds {A D : ℕ} (Q : Source A D) :
    InBox (shape (toRow Q.1)) primaryBox ∧
    TrueWeightLE D (toRow Q.1) (3000*A-1) ∧ JetsBounded (toRow Q.1) := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4024 ∧
      m.sum (fun i a => i.val * a) ≤ 1679 ∧ m 3 ≤ 500 ∧
      ((toRow Q.1).coeff m).natDegree + m.sum (fun i a => (D - i.val) * a) ≤ 3000*A-1 ∧
      m ∈ jetExponents := by
    let n := ((toRow Q.1).coeff m).natDegree
    have hc : (Q.1).coeff (m.optionElim n) ≠ 0 := by
      rw [← MvPolynomial.optionEquivRight_coeff_coeff]
      change ((toRow Q.1).coeff m).coeff n ≠ 0
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact mem_support_iff.mp hm
    have supportBound : ∀ e ∈ Q.1.support, Eligible A D e := Q.2
    obtain ⟨⟨hb, hj, ht, hcap⟩, hw⟩ := supportBound _ (mem_support_iff.mpr hc)
    have hmem : m ∈ jetExponents := by
      change m.weight K1_13_2_2.gradeWeight ≤ 4024 ∧ m.weight K1_13_2_2.oldWeight ≤ 1679 ∧
        m 3 ≤ 500 ∧ m 1+m 2+m 3 ≤ cap (m.weight K1_13_2_2.gradeWeight)
      rw [sumGrade, sumOld]
      rw [sumCount] at hb
      rw [sumIndex] at hj
      rw [sumDifferentiated, sumCount] at hcap
      have htop : m 3 ≤ 500 := by
        simpa only [sumTop, Finsupp.optionElim_apply_some] using ht
      simpa only [Finsupp.optionElim_apply_some] using And.intro hb (And.intro hj (And.intro htop hcap))
    have jb : jetDegreeWeight (d := 3) = (fun v => v.elim 0 (fun _ => 1)) := by
      funext v; cases v <;> rfl
    have ji : jetDerivativeWeight (d := 3) = (fun v => v.elim 0 (fun i => i.val)) := by
      funext v; cases v <;> rfl
    have jw : differentialWeight (d := 3) D =
        (fun v => v.elim 1 (fun i => D - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 500 at ht
    simp only [Finsupp.weight_optionElim, zero_mul, zero_add, one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _ => 1)] at hb
    rw [weight_eq_sum m (fun i => i.val)] at hj
    rw [weight_eq_sum m (fun i => D - i.val)] at hw
    exact ⟨by simpa only [one_mul] using hb, hj, ht, hw, hmem⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Finset.sup_le fun m hm => (h m hm).1
  · exact Finset.sup_le fun m hm => (h m hm).2.1
  · exact MvPolynomial.degreeOf_le_iff.mpr fun m hm => (h m hm).2.2.1
  · exact fun m hm => (h m hm).2.2.2.1
  · exact fun m hm => (h m hm).2.2.2.2

def nodeMap {A D : ℕ} (x y : Geom) : Source A D →ₗ[Geom] Local :=
  (localConstraintAt 3000 x y).domRestrict (Source A D)

def wordMap (A D : ℕ) (w : I → K) : Source A D →ₗ[Geom] (I → Local) :=
  LinearMap.pi fun i => nodeMap (embed (node i)) (embed (w i))

theorem contact_of_word_kernel {A D : ℕ} (w : I → K) (Q : Source A D) (hQ : wordMap A D w Q = 0) :
    Contact w (toRow Q.1) := by
  intro i S hS
  rw [K1_13_2.atJet_toRow]
  have hi : SatisfiesLocalConstraints (d := 3) 3000 (embed (node i)) (embed (w i)) Q.1 := congrFun hQ i
  have hd := pointContact (embed (node i)) (embed (w i)) Q.1 S hS hi
  with_reducible exact hd

theorem local_range_finite (x y : Geom) :
    Module.Finite Geom (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
      (ExpandedTaper6970.space cap))) := by
  have hsub :
      LinearMap.range ((localConstraintAt 3000 x y).domRestrict (ExpandedTaper6970.space cap)) ≤
        LinearMap.range ((localConstraintAt 3000 0 0).domRestrict ExpandedTaper6970.SourceSpace) := by
    rintro _ ⟨Q, rfl⟩
    let R := globalPointTranslation x y Q.1
    have hR : R ∈ ExpandedTaper6970.space cap := ExpandedTaper6970.translate ExpandedTaper6970.cap_antitone x y Q
    change localConstraintAt 3000 x y Q.1 ∈ _
    rw [localConstraintAt_eq_zero_globalPointTranslation]
    change localConstraintAt 3000 0 0 R ∈ _
    rw [congrArg (localConstraintAt 3000 0 0) R.as_sum, map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    by_cases hx : e none < 3000
    · obtain ⟨hg, hj, ht, _⟩ := hR he
      have hw := weight_le_add_mul_totalJetDegree 133671 e
      change e.weight (differentialWeight 133671) ≤ e none + 133671 * e.weight jetDegreeWeight at hw
      have hOld : ExpandedTaper6970.SourceEligible e := ⟨hg,hj,ht,by omega⟩
      have hMono : monomial e (R.coeff e) ∈ ExpandedTaper6970.SourceSpace :=
        (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hOld)
      exact ⟨⟨_, hMono⟩, rfl⟩
    · rw [high_monomial_vanishes _ _ (Nat.le_of_not_gt hx)]
      exact Submodule.zero_mem _
  exact Module.Finite.of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)









end
end ExpandedPrimary6970

