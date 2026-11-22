import ProximityPrize.SubmissionLower.PrimaryTaperColumnData
import ProximityPrize.SubmissionLower.GoldBranch6N8

set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace PrimaryTaper

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open MvPolynomial (mem_support_iff monomial)
open TaperColumns
open TaperBudget (cap)
open scoped BigOperators

open private weight_eq_sum map_independent_family pointContact high_monomial_vanishes
  from ProximityPrize.SubmissionLower.PortLowBase
open private sumCount sumIndex sumDifferentiated sumGrade sumOld from ProximityPrize.SubmissionLower.PrimaryTaperColumns

def primaryBox : Shape := ⟨4012, 1650, 550⟩

def TrueWeightLE {n : ℕ} (D : ℕ) (P : Row n) (T : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree + m.sum (fun i a => (D - i.val) * a) ≤ T

def JetsBounded (P : Row 4) : Prop := ∀ m ∈ P.support, m ∈ jetExponents

theorem row_bounds {A D : ℕ} (Q : Source A D) :
    InBox (shape (toRow Q.1)) primaryBox ∧
    TrueWeightLE D (toRow Q.1) (3000*A-1) ∧ JetsBounded (toRow Q.1) := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4012 ∧
      m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
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
      change m.weight K1_13_2_2.gradeWeight ≤ 4012 ∧ m.weight K1_13_2_2.oldWeight ≤ 1650 ∧
        m 1+m 2+m 3 ≤ cap (m.weight K1_13_2_2.gradeWeight)
      rw [sumGrade, sumOld]
      rw [sumCount] at hb
      rw [sumIndex] at hj
      rw [sumDifferentiated, sumCount] at hcap
      simpa only [Finsupp.optionElim_apply_some] using And.intro hb (And.intro hj hcap)
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
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 550 at ht
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

private theorem local_range_finite (x y : Geom) :
    Module.Finite Geom (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
      (TaperNormalize.space cap))) := by
  have hsub :
      LinearMap.range ((localConstraintAt 3000 x y).domRestrict (TaperNormalize.space cap)) ≤
        LinearMap.range (K1_13_2.nodeMap 0 0) := by
    rintro _ ⟨Q, rfl⟩
    let R := globalPointTranslation x y Q.1
    have hR : R ∈ TaperNormalize.space cap := TaperNormalize.translate TaperBudget.cap_antitone x y Q
    change localConstraintAt 3000 x y Q.1 ∈ _
    rw [localConstraintAt_eq_zero_globalPointTranslation]
    change localConstraintAt 3000 0 0 R ∈ _
    rw [congrArg (localConstraintAt 3000 0 0) R.as_sum, map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    by_cases hx : e none < 3000
    · obtain ⟨hg, hj, ht, _⟩ := hR he
      have hw := weight_le_add_mul_totalJetDegree 133671 e
      change e.weight (differentialWeight 133671) ≤ e none + 133671 * e.weight jetDegreeWeight at hw
      have hOld : K1_13_2.SourceEligible e := ⟨hg,hj,ht,by omega⟩
      have hMono : monomial e (R.coeff e) ∈ K1_13_2.SourceSpace :=
        (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hOld)
      exact ⟨⟨_, hMono⟩, rfl⟩
    · rw [high_monomial_vanishes _ _ (Nat.le_of_not_gt hx)]
      exact Submodule.zero_mem _
  exact Module.Finite.of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

abbrev LocalRankBound : Prop :=
  ∀ x y : Geom, Module.finrank Geom
    (LinearMap.range ((localConstraintAt 3000 x y).domRestrict (TaperNormalize.space cap))) ≤ 343903138965692

private theorem node_rank (hLoc : LocalRankBound) {A D : ℕ} (x y : Geom) :
    Module.finrank Geom (LinearMap.range (nodeMap (A:=A) (D:=D) x y)) ≤ 343903138965692 := by
  letI := local_range_finite x y
  apply (Submodule.finrank_mono ?_).trans (hLoc x y)
  rintro _ ⟨Q, rfl⟩
  exact ⟨⟨Q.1, fun e he => (Q.2 he).1⟩, rfl⟩

theorem word_rank_of_local (hLoc : LocalRankBound) (A D : ℕ) (hD : 3<D) (w : I → K) :
    Module.finrank Geom (LinearMap.range (wordMap A D w)) ≤ 262144 * 343903138965692 := by
  letI : Fact (3<D) := ⟨hD⟩
  let nmap (i : I) := nodeMap (A:=A) (D:=D) (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : Source A D →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap A D w = g.comp f := rfl
  rw [hw]
  calc
    _ ≤ Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, 343903138965692 := Finset.sum_le_sum fun i _ => node_rank hLoc _ _
    _ = _ := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]

def sourceRank (A D : ℕ) : ℕ := compactCount A D - 262144 * 343903138965692



theorem primary_family_of_local (hLoc : LocalRankBound) (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A)
    (w : I → K) {n : ℕ} (hn : n ≤ sourceRank A D) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE D (e i) (3000*A-1) ∧
        JetsBounded (e i) ∧ Contact w (e i) := by
  letI : Fact (3<D) := ⟨hD⟩
  let lift : LinearMap.ker (wordMap A D w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp ((Source A D).subtype.comp (LinearMap.ker (wordMap A D w)).subtype)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  have hdim := (wordMap A D w).finrank_range_add_finrank_ker
  have hcols := (finrank_source A D hD).trans (exact_columns A D hA hD hBudget)
  have hr := word_rank_of_local hLoc A D hD w
  have hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap A D w)) := by
    unfold sourceRank at hn
    omega
  let admissible (P : Row 4) :=
    InBox (shape P) primaryBox ∧ TrueWeightLE D P (3000*A-1) ∧ JetsBounded P ∧ Contact w P
  refine map_independent_family (V := LinearMap.ker (wordMap A D w)) (W := Row 4)
    (n := n) lift hinj admissible ?_ hker
  intro Q
  obtain ⟨hbox,hweight,hJets⟩ := row_bounds Q.1
  exact ⟨hbox,hweight,hJets,contact_of_word_kernel w Q.1 (LinearMap.mem_ker.mp Q.2)⟩


theorem symbol_rank {n : ℕ} (x : Geom) (e : Fin n → Row 4)
    (he : ∀ i, JetsBounded (e i))
    (hli : LinearIndependent Geom (fun i => K1_13_3.symbolAt x (e i))) :
    n ≤ 406807694511 := by
  let V := MvPolynomial.restrictSupport Geom jetExponents
  let v : Fin n → V := fun i =>
    ⟨K1_13_3.symbolAt x (e i), fun m hm => he i m (MvPolynomial.support_map_subset _ _ hm)⟩
  letI : Module.Finite Geom V := MvPolynomial.restrictSupport_finite jetExponents_finite
  have hv : LinearIndependent Geom v := LinearIndependent.of_comp V.subtype hli
  have hd : Module.finrank Geom V = jetColumns.card := by
    change Module.finrank Geom (MvPolynomial.restrictSupport Geom jetExponents) = _
    rw [← jetExponents_finite.coe_toFinset]
    exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) jetColumns
  have hn : jetColumns.card = 406807694511 := by
    exact_mod_cast jet_card_eq.trans sourceCount_eq
  simpa only [Fintype.card_fin, hd, hn] using hv.fintype_card_le_finrank

#print axioms primary_family_of_local
#print axioms symbol_rank
end
end PrimaryTaper
