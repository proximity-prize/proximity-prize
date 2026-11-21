import ProximityPrize.SubmissionLower.Low48EulerJets
import ProximityPrize.SubmissionLower.Low48EulerDimension

set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Low48EulerColumns
noncomputable section
open K1_13 (Geom)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Low48AnchorSpace (AnchorEligible SourceEligible anchorSpace)
open Low48EulerJets (scaledVar first second third)
open scoped BigOperators Pointwise Polynomial

abbrev Exponent := JetVariable 3 →₀ ℕ
abbrev Differential := DifferentialPolynomial Geom 3
abbrev Marker := {u : Exponent // SourceEligible u}

private def measure (w : Fin 4 → ℕ) : Exponent →+ ℕ := Finsupp.weight (fun i => i.elim 0 w)
private abbrev idx := measure Fin.val
private abbrev count := measure (fun _ => 1)
private abbrev diff := measure (fun i => if i = 0 then 0 else 1)
private abbrev top := measure (fun i => if i = 3 then 1 else 0)
private abbrev formal : Exponent →+ ℕ := Finsupp.weight (differentialWeight 133426)

private theorem measure_some (w : Fin 4 → ℕ) (e : Exponent) :
    measure w e = e.some.weight w := by
  unfold measure
  conv_lhs => rw [← Finsupp.optionElim_some e, Finsupp.weight_optionElim]
  simp

private theorem weight_coords (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]

private theorem index_coords (e : Exponent) :
    idx e = e (some 1) + 2 * e (some 2) + 3 * e (some 3) := by
  rw [measure_some, weight_coords]
  change e (some 0) * 0 + e (some 1) * 1 + e (some 2) * 2 + e (some 3) * 3 = _
  omega

private theorem count_coords (e : Exponent) : count e = e.some.degree := by
  rw [measure_some, Finsupp.degree_eq_weight_one]

private theorem diff_coords (e : Exponent) : diff e = e (some 1) + e (some 2) + e (some 3) := by
  rw [measure_some, weight_coords]
  simp [Finsupp.some_apply]

private theorem top_coords (e : Exponent) : top e = e (some 3) := by
  rw [measure_some, weight_coords]
  simp [Finsupp.some_apply]

private theorem formal_coords (e : Exponent) :
    formal e = e none + 133426 * e.some.degree - idx e := by
  have hf : differentialWeight (d := 3) 133426 =
      fun i => i.elim 1 (fun j => 133426 - j.val) := by
    funext i
    cases i <;> rfl
  change e.weight (differentialWeight 133426) = _
  conv_lhs => rw [hf, ← Finsupp.optionElim_some e, Finsupp.weight_optionElim, weight_coords]
  rw [index_coords, Finsupp.degree_eq_sum, Fin.sum_univ_four]
  simp only [one_mul, Finsupp.some_apply]
  change e none + (e (some 0) * 133426 + e (some 1) * 133425 +
    e (some 2) * 133424 + e (some 3) * 133423) = _
  omega

private structure Compatible (hi lo : Exponent) : Prop where
  jet_count : count lo = count hi
  differential : diff lo ≤ diff hi
  top_power : top lo ≤ top hi
  weight : formal lo = formal hi
  index : idx lo ≤ idx hi
  tie : idx lo = idx hi → lo = hi

private theorem Compatible.refl (e : Exponent) : Compatible e e :=
  ⟨rfl, le_rfl, le_rfl, rfl, le_rfl, fun _ => rfl⟩

private theorem Compatible.add {a b c d : Exponent} (h : Compatible a c) (k : Compatible b d) :
    Compatible (a+b) (c+d) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [map_add,map_add,h.jet_count,k.jet_count]
  · simpa only [map_add] using Nat.add_le_add h.differential k.differential
  · simpa only [map_add] using Nat.add_le_add h.top_power k.top_power
  · rw [map_add,map_add,h.weight,k.weight]
  · simpa only [map_add] using Nat.add_le_add h.index k.index
  · simp only [map_add]
    intro hsum
    rw [h.tie (by have := h.index; have := k.index; omega),
      k.tie (by have := h.index; have := k.index; omega)]

private def Leads (p : Differential) (e : Exponent) (c : Geom) : Prop :=
  p.coeff e = c ∧ ∀ v ∈ p.support, Compatible e v

private theorem leads_monomial (e : Exponent) (c : Geom) : Leads (monomial e c) e c := by
  refine ⟨by simp, ?_⟩
  intro v hv
  have he := Finset.mem_singleton.mp (support_monomial_subset hv)
  subst v
  exact Compatible.refl e

private theorem Leads.addSmaller {e v : Exponent} {p : Differential} {a : Geom}
    (h : Leads p e a) (hc : Compatible e v) (hlt : idx v < idx e) (c : Geom) :
    Leads (p+monomial v c) e a := by
  classical
  refine ⟨?_, ?_⟩
  · have hn : v ≠ e := fun he => hlt.ne (congrArg idx he)
    change coeffAddMonoidHom e (p + monomial v c) = a
    rw [map_add]
    change p.coeff e + (monomial v c).coeff e = a
    rw [h.1,coeff_monomial,if_neg hn,add_zero]
  · intro u hu
    rcases Finset.mem_union.mp (support_add hu) with hp | hq
    · exact h.2 u hp
    · have he := Finset.mem_singleton.mp (support_monomial_subset hq)
      rwa [he]

private theorem Leads.mul {p q : Differential} {e f : Exponent} {a b : Geom}
    (hp : Leads p e a) (hq : Leads q f b) : Leads (p*q) (e+f) (a*b) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [coeff_mul, Finset.sum_eq_single (e,f)]
    · rw [hp.1,hq.1]
    · intro v hv hne
      by_cases h1 : p.coeff v.1 = 0
      · simp [h1]
      by_cases h2 : q.coeff v.2 = 0
      · simp [h2]
      have hc := hp.2 v.1 (mem_support_iff.mpr h1)
      have hd := hq.2 v.2 (mem_support_iff.mpr h2)
      have he := congrArg idx (Finset.mem_antidiagonal.mp hv)
      simp only [map_add] at he
      exact (hne (Prod.ext (hc.tie (by have := hc.index; have := hd.index; omega))
        (hd.tie (by have := hc.index; have := hd.index; omega)))).elim
    · intro hn
      exact (hn (Finset.mem_antidiagonal.mpr rfl)).elim
  · intro v hv
    obtain ⟨u,hu,w,hw,rfl⟩ := Finset.mem_add.mp (support_mul p q hv)
    exact (hp.2 u hu).add (hq.2 w hw)

private theorem Leads.pow {p : Differential} {e : Exponent} {a : Geom}
    (h : Leads p e a) (n : ℕ) : Leads (p^n) (n • e) (a^n) := by
  induction n with
  | zero => simpa [← MvPolynomial.C_apply] using leads_monomial 0 (1 : Geom)
  | succ n ih => simpa only [pow_succ,succ_nsmul] using ih.mul h

private def jexp (i : Fin 4) : Exponent := Finsupp.single none i.val + Finsupp.single (some i) 1

private theorem jet_measure (w : Fin 4 → ℕ) (i : Fin 4) : measure w (jexp i) = w i := by
  simp [jexp,measure,Finsupp.weight_single]

private theorem jet_formal (i : Fin 4) : formal (jexp i) = 133426 := by
  simp only [jexp,map_add,Finsupp.weight_single,differentialWeight,smul_eq_mul,mul_one,one_mul]
  have hi := i.isLt
  change i.val + (133426 - i.val) = 133426
  omega

private theorem jet_refines (i j : Fin 4) (h : i.val < j.val) : Compatible (jexp j) (jexp i) := by
  refine ⟨by simp only [jet_measure],?_,?_,by simp only [jet_formal],?_,?_⟩
  · have hne : j ≠ 0 := by intro he; subst j; exact (Nat.not_lt_zero _) h
    simpa only [jet_measure, if_neg hne] using (show (if i = 0 then 0 else 1) ≤ 1 by split <;> decide)
  · have hne : i ≠ 3 := by intro he; subst i; have := j.isLt; omega
    simp only [jet_measure, if_neg hne, Nat.zero_le]
  · simpa only [jet_measure] using h.le
  · intro he
    simp only [jet_measure] at he
    exact (h.ne he).elim

private theorem jet_lower (i j : Fin 4) (h : i.val < j.val) : idx (jexp i) < idx (jexp j) := by
  simpa [measure, jexp, Finsupp.weight_single] using h

private theorem scaled_as_monomial (j : Fin 4) : (scaledVar j : Differential) = monomial (jexp j) 1 := by
  rw [scaledVar,MvPolynomial.X_pow_eq_monomial,MvPolynomial.X,monomial_mul_monomial,one_mul,jexp]

private theorem const_scaled (j : Fin 4) (a : Geom) : C a * scaledVar j = monomial (jexp j) a := by
  rw [scaled_as_monomial, C_mul_monomial, mul_one]

private theorem leadFirst : Leads (first 133426) (jexp 1) 1 := by
  rw [first, sub_eq_add_neg, const_scaled, scaled_as_monomial, ← map_neg]
  exact (leads_monomial _ _).addSmaller (jet_refines 0 1 (by decide)) (jet_lower 0 1 (by decide)) _

private theorem leadSecond : Leads (second 133426) (jexp 2) 2 := by
  rw [second, const_scaled, const_scaled, const_scaled, sub_eq_add_neg, ← map_neg]
  apply Leads.addSmaller _ (jet_refines 0 2 (by decide)) (jet_lower 0 2 (by decide))
  exact (leads_monomial _ _).addSmaller (jet_refines 1 2 (by decide)) (jet_lower 1 2 (by decide)) _

private theorem leadThird : Leads (third 133426) (jexp 3) 6 := by
  rw [third, const_scaled, const_scaled, const_scaled, const_scaled, sub_eq_add_neg, sub_eq_add_neg,
    ← map_neg, ← map_neg]
  apply Leads.addSmaller _ (jet_refines 0 3 (by decide)) (jet_lower 0 3 (by decide))
  apply Leads.addSmaller _ (jet_refines 1 3 (by decide)) (jet_lower 1 3 (by decide))
  exact (leads_monomial _ _).addSmaller (jet_refines 2 3 (by decide)) (jet_lower 2 3 (by decide)) _

private theorem high_has_abscissa (u : Marker) (h : ¬ formal u.val < 92 * 179915) :
    idx u.val ≤ u.val none := by
  have hb := u.property.1
  rw [formal_coords] at h
  omega

def column (u : Marker) : Differential :=
  if formal u.val < 92 * 179915 then monomial u.val 1 else
    Low48EulerJets.column 133426 (u.val none - idx u.val) (u.val (some 0))
      (u.val (some 1)) (u.val (some 2)) (u.val (some 3))

private def leadingCoefficient (u : Marker) : Geom :=
  if formal u.val < 92 * 179915 then 1 else (2 : Geom)^(u.val (some 2)) * (6 : Geom)^(u.val (some 3))

private theorem leading_exponent (u : Exponent) (h : idx u ≤ u none) :
    Finsupp.single none (u none-idx u) + u (some 0) • jexp 0 + u (some 1) • jexp 1 +
      u (some 2) • jexp 2 + u (some 3) • jexp 3 = u := by
  ext j
  cases j with
  | none =>
    simp [jexp, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]
    rw [index_coords] at h ⊢
    omega
  | some j => fin_cases j <;>
    simp [jexp, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]

private theorem column_leads (u : Marker) : Leads (column u) u.val (leadingCoefficient u) := by
  unfold column leadingCoefficient
  split_ifs with h
  · exact leads_monomial _ _
  · have hx := high_has_abscissa u h
    have hx0 (n : ℕ) : Leads (MvPolynomial.X none ^ n) (Finsupp.single none n) 1 := by
      rw [MvPolynomial.X_pow_eq_monomial]
      exact leads_monomial _ _
    have hy := leads_monomial (jexp 0) (1 : Geom)
    have hp := (((((hx0 (u.val none - idx u.val)).mul (hy.pow (u.val (some 0)))).mul
      (leadFirst.pow (u.val (some 1)))).mul (leadSecond.pow (u.val (some 2)))).mul
      (leadThird.pow (u.val (some 3))))
    rw [leading_exponent _ hx] at hp
    simpa [Low48EulerJets.column, scaled_as_monomial] using hp

private theorem leading_ne_zero (u : Marker) : leadingCoefficient u ≠ 0 := by
  have hn (n : ℕ) (hn : ¬ K1.p ∣ n) : (n : Geom) ≠ 0 :=
    fun h => hn ((CharP.cast_eq_zero_iff Geom K1.p n).mp h)
  have h₂ : (2 : Geom) ≠ 0 := hn 2 (by decide)
  have h₆ : (6 : Geom) ≠ 0 := hn 6 (by decide)
  unfold leadingCoefficient
  split_ifs
  · exact one_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ h₂) (pow_ne_zero _ h₆)

theorem column_mem (u : Marker) : column u ∈ anchorSpace := by
  apply (mem_restrictSupport_iff Geom).mpr
  intro e he
  have h := (column_leads u).2 e he
  obtain ⟨hb,hi,ht,hg,hw⟩ := u.property
  have hd : e.some.degree = u.val.some.degree := by simpa only [count_coords] using h.jet_count
  have hij : e.some.weight Fin.val ≤ u.val.some.weight Fin.val := by
    simpa only [measure_some] using h.index
  have htop := h.top_power
  rw [top_coords,top_coords] at htop
  have hdif := h.differential
  rw [diff_coords,diff_coords] at hdif
  have hfor := h.weight
  change e.weight (differentialWeight 133426) = u.val.weight (differentialWeight 133426) at hfor
  refine ⟨hd.le.trans hb,hij.trans hi,htop.trans ht,?_,?_⟩
  · rw [hd]
    exact hg.trans (Low48AnchorSpace.gradeLimit_antitone hdif)
  · rw [hfor]
    exact hw.trans (by omega)

theorem column_degree (u : Marker) (S : Geom[X]) (hS : S.natDegree ≤ 133426) :
    (differentialSpecialization (column u) S).natDegree < 92 * 179915 := by
  unfold column
  split_ifs with h
  · have hw : differentialWeightedDegree 133426 (monomial u.val (1 : Geom)) = formal u.val := by
      simp [differentialWeightedDegree, weightedTotalDegree_monomial, formal]
    exact (natDegree_differentialSpecialization_le _ S hS).trans_lt (hw.symm ▸ h)
  · have hd := Low48EulerJets.column_degree (by decide : 3 ≤ 133426) S hS
      (u.val none - idx u.val) (u.val (some 0)) (u.val (some 1)) (u.val (some 2)) (u.val (some 3))
    have hf := u.property.2.2.2.2
    change formal u.val ≤ 92*179915 + u.val.some.weight Fin.val - 1 at hf
    have hi : u.val.some.weight Fin.val = idx u.val := (measure_some _ _).symm
    rw [hi] at hf
    rw [formal_coords, Finsupp.degree_eq_sum, Fin.sum_univ_four] at hf
    simp only [Finsupp.some_apply] at hf
    have hindex := index_coords u.val
    have hx := high_has_abscissa u h
    exact hd.trans_lt (by omega)

theorem columns_independent : LinearIndependent Geom column := by
  classical
  rw [linearIndependent_iff']
  intro s g hz u hu
  by_contra hn
  let candidates := s.filter fun e => g e ≠ 0
  have hnon : candidates.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,hn⟩⟩
  obtain ⟨v,hv,hm⟩ := Finset.exists_max_image candidates (fun e => idx e.val) hnon
  obtain ⟨hvs,hvg⟩ := Finset.mem_filter.mp hv
  have hc := congrArg (coeffAddMonoidHom v.val) hz
  simp only [map_sum, map_zero] at hc
  rw [Finset.sum_eq_single v] at hc
  · have hl : (column v).coeff v.val = leadingCoefficient v := (column_leads v).1
    change g v * (column v).coeff v.val = 0 at hc
    rw [hl] at hc
    exact (mul_ne_zero hvg (leading_ne_zero v)) hc
  · intro e he hne
    by_cases hge : g e = 0
    · simp [hge]
    have hdeg := hm e (Finset.mem_filter.mpr ⟨he,hge⟩)
    have hzero : (column e).coeff v.val = 0 := by
      by_contra hnzero
      have hd := (column_leads e).2 v.val (mem_support_iff.mpr hnzero)
      exact hne (Subtype.ext (hd.tie (le_antisymm hd.index hdeg)).symm)
    change g e * (column e).coeff v.val = 0
    simp [hzero]
  · exact fun h => (h hvs).elim

#print axioms column_degree
#print axioms columns_independent

end
end Low48EulerColumns
