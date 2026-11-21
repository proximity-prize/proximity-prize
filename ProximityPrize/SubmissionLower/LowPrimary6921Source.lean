import ProximityPrize.SubmissionLower.LowPrice6921Geometry

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace LowPrimary6921

noncomputable section

open Polynomial K1 K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative Finset
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow atJet_toRow)
open scoped BigOperators Polynomial
open MvPolynomial (mem_support_iff)

abbrev degreeBound : ℕ := 133455
abbrev agreement : ℕ := 180071
abbrev terminal : ℕ := 3000 * agreement - 1
abbrev layerWidth : ℕ := 46619
abbrev sourceRank : ℕ := 1188934726272953919

def WeightLE {n : ℕ} (P : Row n) (T : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (degreeBound - i.val) * a) ≤ T

def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) ⟨4012, 1650, 550⟩ ∧ WeightLE (e i) terminal ∧ Contact w (e i)

def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight degreeBound) ≤ terminal

def sourceExponents : Set SourceExponent := { e | SourceEligible e }

theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) degreeBound)
    ?_ terminal).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < degreeBound) j).ne'

def sourceColumns : Finset SourceExponent := sourceExponents_finite.toFinset

def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents

instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite

/-- The exponent tuple in the order (Y₃,Y₂,Y₁,Y₀,X). -/
private abbrev Column := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

private def width (a b c f : ℕ) : ℕ :=
  540213000 + b + 2 * c + 3 * f - 133455 * (a + b + c + f)

private def tuples : Finset Column :=
  (range 551).sigma fun f =>
    (range ((1650 - 3 * f) / 2 + 1)).sigma fun c =>
      (range (1651 - 2 * c - 3 * f)).sigma fun b =>
        (range (4013 - b - c - f)).sigma fun a => range (width a b c f)

private def exponent : Column → SourceExponent
  | ⟨f, c, b, a, x⟩ => Finsupp.equivFunOnFinite.symm (fun v => v.elim x ![a, b, c, f])

private def coordinates (e : SourceExponent) : Column :=
  ⟨e (some 3), e (some 2), e (some 1), e (some 0), e none⟩

private theorem coordinates_exponent (t : Column) : coordinates (exponent t) = t := by
  rcases t with ⟨f, c, b, a, x⟩
  simp [coordinates, exponent]

private theorem exponent_coordinates (e : SourceExponent) : exponent (coordinates e) = e := by
  ext v
  cases v with
  | none => simp [coordinates, exponent]
  | some j => fin_cases j <;> simp [coordinates, exponent]

private theorem mem_columns (t : Column) :
    exponent t ∈ sourceColumns ↔ t ∈ tuples := by
  rcases t with ⟨f, c, b, a, x⟩
  change exponent ⟨f, c, b, a, x⟩ ∈ sourceExponents_finite.toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change SourceEligible (exponent ⟨f, c, b, a, x⟩) ↔ _
  simp only [tuples, mem_sigma, mem_range, SourceEligible, Finsupp.weight_eq_sum,
    Fintype.sum_option, Fin.sum_univ_succ, Fin.sum_univ_zero, smul_eq_mul,
    jetDegreeWeight_none, jetDegreeWeight_some, jetDerivativeWeight, differentialWeight,
    topWeight, Option.elim_none, Option.elim_some, exponent, Finsupp.coe_equivFunOnFinite_symm]
  simp [width, terminal, agreement, degreeBound]
  omega

private theorem card_columns : sourceColumns.card = tuples.card := by
  let e : Column ≃ SourceExponent :=
    ⟨exponent, coordinates, coordinates_exponent, exponent_coordinates⟩
  exact (Finset.card_equiv e (fun t => (mem_columns t).symm)).symm

private def widthInt (a b c f : ℤ) : ℤ :=
  540213000 + b + 2 * c + 3 * f - 133455 * (a + b + c + f)

private theorem cast_width (a b c f : ℕ) (h : a + b + c + f ≤ 4012) :
    (width a b c f : ℤ) = widthInt a b c f := by
  have hpos : 133455 * (a + b + c + f) ≤ 540213000 + b + 2 * c + 3 * f := by omega
  simp [width, widthInt, Nat.cast_sub hpos]

/-- Verify a polynomial prefix by its initial value and forward difference. -/
private theorem scaled_sum (k : ℤ) (g p : ℤ → ℤ)
    (base : p 0 = 0) (step : ∀ t, p (t + 1) = p t + k * g t) (n : ℕ) :
    k * (∑ i ∈ range n, g i) = p n := by
  induction n with
  | zero => simpa using base.symm
  | succ n ih => rw [sum_range_succ, Nat.cast_succ, mul_add, ih, step]

private def prefixA (b c f n : ℤ) : ℤ :=
  n * (2 * widthInt 0 b c f - 133455 * (n - 1))

private def doubleA (b c f : ℤ) : ℤ :=
  prefixA b c f (4013 - b - c - f)

/-- The doubled sum over the (Y₀)-exponent is quadratic in the (Y₁)-exponent. -/
private def prefixB (c f n : ℤ) : ℤ :=
  let p := 4013 - c - f
  let q := 2 * widthInt 0 0 c f - 133455 * (p - 1)
  let r := 2 - 133455
  6 * n * p * q + 3 * n * (n - 1) * (p * r - q) - n * (n - 1) * (2 * n - 1) * r

private def twelveB (c f : ℤ) : ℤ :=
  prefixB c f (1651 - 2 * c - 3 * f)

/-- Sum the cubic in the (Y₂)-exponent using its first four values.
The factor 24 clears the denominators in its Newton prefix polynomial. -/
private def prefixC (f n : ℤ) : ℤ :=
  let v₀ := twelveB 0 f
  let v₁ := twelveB 1 f
  let v₂ := twelveB 2 f
  let v₃ := twelveB 3 f
  24 * n * v₀ + 12 * n * (n - 1) * (v₁ - v₀) +
    4 * n * (n - 1) * (n - 2) * (v₂ - 2 * v₁ + v₀) +
    n * (n - 1) * (n - 2) * (n - 3) * (v₃ - 3 * v₂ + 3 * v₁ - v₀)

private def countA (b c f : ℕ) : ℤ :=
  ∑ a ∈ range (4013 - b - c - f), (width a b c f : ℤ)

private def countB (c f : ℕ) : ℤ :=
  ∑ b ∈ range (1651 - 2 * c - 3 * f), countA b c f

private def countC (f : ℕ) : ℤ :=
  ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), countB c f

private theorem card_tuples_int : (tuples.card : ℤ) = ∑ f ∈ range 551, countC f := by
  simp only [tuples, card_sigma, card_range, Nat.cast_sum, countC, countB, countA]

private theorem countA_closed (b c f : ℕ) (h : b + 2 * c + 3 * f ≤ 1650) :
    2 * countA b c f = doubleA b c f := by
  have hsum : countA b c f =
      ∑ a ∈ range (4013 - b - c - f), widthInt a b c f := by
    apply sum_congr rfl
    intro a ha
    rw [mem_range] at ha
    exact cast_width a b c f (by omega)
  rw [hsum, scaled_sum 2 (fun a => widthInt a b c f) (prefixA b c f)
    (by simp [prefixA]) (by intro t; unfold prefixA widthInt; ring)]
  have hn : ((4013 - b - c - f : ℕ) : ℤ) = 4013 - b - c - f := by omega
  rw [hn, doubleA]

private theorem countB_closed (c f : ℕ) (h : 2 * c + 3 * f ≤ 1650) :
    12 * countB c f = twelveB c f := by
  calc
    12 * countB c f =
        ∑ b ∈ range (1651 - 2 * c - 3 * f), 6 * (2 * countA b c f) := by
      simp only [countB, ← mul_assoc, ← mul_sum, show (6 : ℤ) * 2 = 12 by decide]
    _ = 6 * ∑ b ∈ range (1651 - 2 * c - 3 * f), doubleA b c f := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b hb
      rw [mem_range] at hb
      rw [countA_closed b c f (by omega)]
    _ = twelveB c f := by
      rw [scaled_sum 6 (fun b => doubleA b c f) (prefixB c f)
        (by simp [prefixB])
        (by intro t; unfold prefixB doubleA prefixA widthInt; ring)]
      have hn : ((1651 - 2 * c - 3 * f : ℕ) : ℤ) = 1651 - 2 * c - 3 * f := by omega
      rw [hn, twelveB]

private def closedC (f : ℕ) : ℤ :=
  prefixC f ((1650 - 3 * f) / 2 + 1 : ℕ)

private theorem countC_closed (f : ℕ) (hf : f < 551) :
    288 * countC f = closedC f := by
  calc
    288 * countC f =
        ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), 24 * (12 * countB c f) := by
      simp only [countC, ← mul_assoc, ← mul_sum, show (24 : ℤ) * 12 = 288 by decide]
    _ = 24 * ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), twelveB c f := by
      rw [mul_sum]
      apply sum_congr rfl
      intro c hc
      rw [mem_range] at hc
      rw [countB_closed c f (by omega)]
    _ = closedC f := by
      rw [scaled_sum 24 (fun c => twelveB c f) (prefixC f)
        (by simp [prefixC])
        (by intro t; unfold prefixC twelveB prefixB widthInt; ring)]
      rfl

/-- Evaluate the remaining one-dimensional sum of closed formulas. -/
private def evaluate (g : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => evaluate g n + g n

private theorem sum_eq_evaluate (g : ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ range n, g i) = evaluate g n := by
  induction n with
  | zero => simp [evaluate]
  | succ n ih => rw [sum_range_succ, ih, evaluate]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem evaluate_closedC : evaluate closedC 551 = 26323032581587275613920 := by
  rfl

theorem exact_source_columns : sourceColumns.card = 91399418686066929215 := by
  have h : 288 * (tuples.card : ℤ) = 26323032581587275613920 := by
    rw [card_tuples_int, mul_sum]
    calc
      _ = ∑ f ∈ range 551, closedC f :=
        sum_congr rfl fun f hf => countC_closed f (mem_range.mp hf)
      _ = _ := by rw [sum_eq_evaluate, evaluate_closedC]
  rw [card_columns]
  omega

private theorem weight_eq_sum (m : Fin 4 →₀ ℕ) (weight : Fin 4 → ℕ) :
    m.weight weight = m.sum (fun i a => weight i * a) := by
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]

/-- Extract the support test at the largest X exponent in a nonzero coefficient. -/
theorem row_bounds (Q : SourceSpace) :
    InBox (shape (toRow Q.1)) ⟨4012, 1650, 550⟩ ∧
    WeightLE (toRow Q.1) terminal := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4012 ∧
      m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
      ((toRow Q.1).coeff m).natDegree + m.sum (fun i a => (133455 - i.val) * a) ≤
        terminal := by
    let n := ((toRow Q.1).coeff m).natDegree
    have hc : (Q.1).coeff (m.optionElim n) ≠ 0 := by
      rw [← MvPolynomial.optionEquivRight_coeff_coeff]
      change ((toRow Q.1).coeff m).coeff n ≠ 0
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact mem_support_iff.mp hm
    have supportBound : ∀ e ∈ Q.1.support, SourceEligible e := Q.2
    obtain ⟨hb, hj, ht, hw⟩ := supportBound _ (mem_support_iff.mpr hc)
    have jb : jetDegreeWeight (d := 3) = (fun v => v.elim 0 (fun _ => 1)) := by
      funext v; cases v <;> rfl
    have ji : jetDerivativeWeight (d := 3) = (fun v => v.elim 0 (fun i => i.val)) := by
      funext v; cases v <;> rfl
    have jw : differentialWeight (d := 3) 133455 =
        (fun v => v.elim 1 (fun i => 133455 - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 550 at ht
    simp only [Finsupp.weight_optionElim, zero_mul, zero_add, one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _ => 1)] at hb
    rw [weight_eq_sum m (fun i => i.val)] at hj
    rw [weight_eq_sum m (fun i => 133455 - i.val)] at hw
    exact ⟨by simpa only [one_mul] using hb, hj, ht, hw⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.sup_le fun m hm => (h m hm).1
  · exact Finset.sup_le fun m hm => (h m hm).2.1
  · exact MvPolynomial.degreeOf_le_iff.mpr fun m hm => (h m hm).2.2.1
  · exact fun m hm => (h m hm).2.2.2

/-- Translate each independent coordinate weight and intersect the resulting bounds. -/
theorem translate_mem_source (x y : Geom) (Q : SourceSpace) :
    globalPointTranslation x y Q.1 ∈ SourceSpace := by
  have preserve (wt : JetVariable 3 → ℕ) (B : ℕ)
      (h : ∀ e ∈ Q.1.support, e.weight wt ≤ B) :
      ∀ e ∈ (globalPointTranslation x y Q.1).support, e.weight wt ≤ B :=
    MvPolynomial.mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x y (MvPolynomial.mem_restrictWeightAtMost.mpr h))
  have h : ∀ e ∈ Q.1.support, SourceEligible e :=
    Q.2
  exact fun e he =>
    ⟨preserve jetDegreeWeight 4012 (fun t ht => (h t ht).1) e he,
      preserve jetDerivativeWeight 1650 (fun t ht => (h t ht).2.1) e he,
      preserve topWeight 550 (fun t ht => (h t ht).2.2.1) e he,
      preserve (differentialWeight degreeBound) terminal
        (fun t ht => (h t ht).2.2.2) e he⟩

def nodeMap (x y : Geom) : SourceSpace →ₗ[Geom] Local :=
  (localConstraintAt 3000 x y).domRestrict SourceSpace

def wordMap (w : I → K) : SourceSpace →ₗ[Geom] (I → Local) :=
  LinearMap.pi fun i => nodeMap (embed (node i)) (embed (w i))

private theorem pointContact {m : ℕ} (x y : Geom) (Q : SourcePolynomial) (S : Geom[X])
    (hS : S.eval x = y) (hQ : SatisfiesLocalConstraints m x y Q) :
    (Polynomial.X - Polynomial.C x) ^ m ∣ differentialSpecialization Q S := by
  exact X_sub_C_pow_dvd_differentialSpecialization_of_contact Q S x y hS hQ

theorem contact_of_word_kernel (w : I → K) (Q : SourceSpace) (hQ : wordMap w Q = 0) :
    Contact w (toRow Q.1) := by
  intro i S hS
  rw [atJet_toRow]
  have hi : SatisfiesLocalConstraints (d := 3) 3000 (embed (node i)) (embed (w i)) Q.1 := by
    exact congrFun hQ i
  have hd := pointContact (embed (node i)) (embed (w i)) Q.1 S hS hi
  with_reducible exact hd

theorem finrank_source : Module.finrank Geom SourceSpace = sourceColumns.card := by
  have h : (↑sourceColumns : Set SourceExponent) = sourceExponents :=
    Set.Finite.coe_toFinset sourceExponents_finite
  rw [SourceSpace, ← h]
  exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) sourceColumns

private theorem high_monomial_vanishes (e : SourceExponent) (c : Geom) (he : 3000 ≤ e none) :
    localConstraintAt 3000 0 0 (MvPolynomial.monomial e c) = 0 := by
  change MvPolynomial.weightedTruncation (localContactWeight 3) 3000
    (MvPolynomial.bind₁ (unscaledLocalImage 3 0 0) (MvPolynomial.monomial e c)) = 0
  apply (MvPolynomial.weightedTruncation_eq_zero_iff _ _ _).mpr
  refine MvPolynomial.bind₁_mem_restrictWeightedOrder
    (w := fun v : JetVariable 3 => v.elim 1 (fun _ => 0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa only [unscaledLocalImage, map_zero, zero_add, Option.elim_none] using
        (MvPolynomial.X_mem_restrictWeightedOrder (R := Geom)
          (localContactWeight 3) (localT 3) (m := 1) (by rfl))
    | some j => simp
  · exact (MvPolynomial.monomial_mem_restrictWeightedOrder _ _ _ _).mpr
      (Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he))


/-- Any monomial whose origin contact can survive is already a published source column. -/
private theorem low_column_old {e : SourceExponent} (he : SourceEligible e) (hx : e none < 3000) :
    K1_13_2.SourceEligible e := by
  refine ⟨he.1, he.2.1, he.2.2.1, ?_⟩
  let w : JetVariable 3 → ℕ := fun v => v.elim 1 (fun _ => 133671)
  have hle : e.weight (differentialWeight 133671) ≤ e.weight w := by
    apply Finsupp.weight_le_weight
    intro v
    cases v <;> simp [w, differentialWeight]
  have hwt : e.weight w = e none + (e.weight jetDegreeWeight) * 133671 := by
    have heq : e.some.optionElim (e none) = e := by
      ext i
      cases i <;> simp
    conv_lhs => rw [← heq]
    dsimp only [w]
    rw [Finsupp.weight_optionElim]
    have hj : jetDegreeWeight (d := 3) = (fun v => v.elim 0 (fun _ => 1)) := by
      funext v
      cases v <;> rfl
    rw [hj, ← heq, Finsupp.weight_optionElim]
    simp only [Finsupp.some_optionElim, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul,
      Finset.sum_mul, one_mul, mul_one, zero_mul, zero_add]
  have hd := he.1
  rw [hwt] at hle
  omega

theorem origin_range_le_old :
    LinearMap.range (nodeMap 0 0) ≤ LinearMap.range (K1_13_2.nodeMap 0 0) := by
  intro L hL
  obtain ⟨Q, rfl⟩ := LinearMap.mem_range.mp hL
  let f := localConstraintAt (R := Geom) (d := 3) 3000 0 0
  change f Q.val ∈ _
  have heq := congrArg f Q.val.as_sum
  rw [map_sum] at heq
  rw [heq]
  apply Submodule.sum_mem
  intro e he
  by_cases hx : e none < 3000
  · have hm : MvPolynomial.monomial e (Q.val.coeff e) ∈ K1_13_2.SourceSpace := by
      unfold K1_13_2.SourceSpace
      apply (MvPolynomial.monomial_mem_restrictSupport Geom).mpr
      exact Or.inl (low_column_old (Q.property he) hx)
    exact LinearMap.mem_range.mpr ⟨⟨_, hm⟩, rfl⟩
  · rw [show f (MvPolynomial.monomial e (Q.val.coeff e)) = 0 from
        high_monomial_vanishes e _ (Nat.le_of_not_gt hx)]
    exact Submodule.zero_mem _

theorem node_range_le_old (x y : Geom) :
    LinearMap.range (nodeMap x y) ≤ LinearMap.range (K1_13_2.nodeMap 0 0) := by
  rintro _ ⟨Q, rfl⟩
  apply origin_range_le_old
  refine ⟨⟨globalPointTranslation x y Q.val, translate_mem_source x y Q⟩, ?_⟩
  exact (localConstraintAt_eq_zero_globalPointTranslation (m := 3000) x y Q.val).symm

/-- Sum the individual rank bounds by factoring through the product of the node ranges. -/
theorem word_rank_le (w : I → K) {b : ℕ}
    (h : Module.finrank Geom (LinearMap.range (K1_13_2.nodeMap 0 0)) ≤ b) :
    Module.finrank Geom (LinearMap.range (wordMap w)) ≤ 262144 * b := by
  let nmap (i : I) := nodeMap (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : SourceSpace →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap w = g.comp f := rfl
  rw [hw]
  calc
    Module.finrank Geom (LinearMap.range (g.comp f)) ≤
        Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, b := Finset.sum_le_sum fun i _ =>
      (Submodule.finrank_mono (node_range_le_old (embed (node i)) (embed (w i)))).trans h
    _ = 262144 * b := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]

private theorem map_independent_family {V W : Type*} [AddCommGroup V] [Module Geom V]
    [AddCommGroup W] [Module Geom W] {n : ℕ} (f : V →ₗ[Geom] W)
    (hf : Function.Injective f) (P : W → Prop) (hP : ∀ x, P (f x))
    (hn : n ≤ Module.finrank Geom V) :
    ∃ e : Fin n → W, LinearIndependent Geom e ∧ ∀ i, P (e i) := by
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank hn
  exact ⟨f ∘ e, he.map' f (LinearMap.ker_eq_bot_of_injective hf), fun i => hP (e i)⟩

private theorem family_of_kernel (w : I → K) {n : ℕ}
    (hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap w))) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) ⟨4012, 1650, 550⟩ ∧
        WeightLE (e i) terminal ∧ Contact w (e i) := by
  let liftRow : LinearMap.ker (wordMap w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp (SourceSpace.subtype.comp (LinearMap.ker (wordMap w)).subtype)
  have hinj : Function.Injective liftRow := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  let admissible (P : Row 4) := InBox (shape P) ⟨4012, 1650, 550⟩ ∧
    WeightLE P terminal ∧ Contact w P
  have hrows (Q : LinearMap.ker (wordMap w)) : admissible (liftRow Q) := by
    obtain ⟨hbox, hwt⟩ := row_bounds Q.1
    have hk : wordMap w Q.1 = 0 := (LinearMap.mem_ker (f := wordMap w)).mp Q.2
    have hcont := contact_of_word_kernel w Q.1 hk
    have happly : liftRow Q = toRow Q.1.1 := rfl
    rw [happly]
    exact ⟨hbox, hwt, hcont⟩
  have h := map_independent_family (V := LinearMap.ker (wordMap w)) (W := Row 4)
    (n := n) liftRow hinj admissible hrows hker
  simpa only [admissible] using h

theorem OldGeometry.K1_13_2_2_1 : K1_13_2_2.c1 := K1_13_2_2_1.proof
theorem OldGeometry.K1_13_2_2_2 : K1_13_2_2.c2 := K1_13_2_2_2.proof
theorem OldGeometry.K1_13_2_2_3 : K1_13_2_2.c3 := K1_13_2_2_3.proof
theorem OldGeometry.K1_13_2_2_4 : K1_13_2_2.c4 := K1_13_2_2_4.proof
theorem OldGeometry.K1_13_2_2_5 : K1_13_2_2.c5 := K1_13_2_2_5.proof
theorem OldGeometry.K1_13_2_2 : K1_13_2.c2 := K1_13_2_2.of_children OldGeometry.K1_13_2_2_1 OldGeometry.K1_13_2_2_2 OldGeometry.K1_13_2_2_3 OldGeometry.K1_13_2_2_4 OldGeometry.K1_13_2_2_5
theorem OldGeometry.K1_13_2_3_1 : K1_13_2_3.c1 := K1_13_2_3_1.proof
theorem OldGeometry.K1_13_2_3_2 : K1_13_2_3.c2 := K1_13_2_3_2.proof
theorem OldGeometry.K1_13_2_3_3 : K1_13_2_3.c3 := K1_13_2_3_3.proof
theorem OldGeometry.K1_13_2_3_4 : K1_13_2_3.c4 := K1_13_2_3_4.proof
theorem OldGeometry.K1_13_2_3_5 : K1_13_2_3.c5 := K1_13_2_3_5.proof
theorem OldGeometry.K1_13_2_3_6 : K1_13_2_3.c6 := K1_13_2_3_6.proof
theorem OldGeometry.K1_13_2_3_7 : K1_13_2_3.c7 := K1_13_2_3_7.proof
theorem OldGeometry.K1_13_2_3 : K1_13_2.c3 := K1_13_2_3.of_children OldGeometry.K1_13_2_3_1 OldGeometry.K1_13_2_3_2 OldGeometry.K1_13_2_3_3 OldGeometry.K1_13_2_3_4 OldGeometry.K1_13_2_3_5 OldGeometry.K1_13_2_3_6 OldGeometry.K1_13_2_3_7

theorem primary_rank (w : I → K) : PrimaryRank w := by
  obtain ⟨power, hpower⟩ := OldGeometry.K1_13_2_3
  have hlocal := (K1_13_2.origin_rank_le power OldGeometry.K1_13_2_2).trans hpower
  have hglobal := word_rank_le w hlocal
  have hsize : Module.finrank Geom SourceSpace = 91399418686066929215 :=
    finrank_source.trans exact_source_columns
  have hdim := (wordMap w).finrank_range_add_finrank_ker
  have hker : sourceRank ≤ Module.finrank Geom (LinearMap.ker (wordMap w)) := by
    simp only [sourceRank]
    omega
  exact family_of_kernel w hker

end
end LowPrimary6921
