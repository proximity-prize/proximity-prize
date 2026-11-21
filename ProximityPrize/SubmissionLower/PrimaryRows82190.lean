import ProximityPrize.SubmissionLower.Primary82170
import ProximityPrize.SubmissionLower.GoldBranch6N8

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

namespace PrimaryRows82190
noncomputable section
open K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open MvPolynomial (mem_support_iff)
open scoped BigOperators
open private weight_eq_sum map_independent_family from ProximityPrize.SubmissionLower.PortLowBase

def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (133419 - i.val) * a) ≤ D

def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133419) ≤ 3000 * 179954 - 1
def sourceExponents : Set SourceExponent := { e | SourceEligible e }
theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133419)
    ?_ (3000 * 179954 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133419) j).ne'
def sourceColumns : Finset SourceExponent := sourceExponents_finite.toFinset
def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents
instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite
theorem row_bounds (Q : SourceSpace) :
    InBox (shape (toRow Q.1)) ⟨4012, 1650, 550⟩ ∧
    TrueWeightLE (toRow Q.1) (3000 * 179954 - 1) := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4012 ∧
      m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
      ((toRow Q.1).coeff m).natDegree + m.sum (fun i a => (133419 - i.val) * a) ≤
        3000 * 179954 - 1 := by
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
    have jw : differentialWeight (d := 3) 133419 =
        (fun v => v.elim 1 (fun i => 133419 - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 550 at ht
    simp only [Finsupp.weight_optionElim, zero_mul, zero_add, one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _ => 1)] at hb
    rw [weight_eq_sum m (fun i => i.val)] at hj
    rw [weight_eq_sum m (fun i => 133419 - i.val)] at hw
    exact ⟨by simpa only [one_mul] using hb, hj, ht, hw⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.sup_le fun m hm => (h m hm).1
  · exact Finset.sup_le fun m hm => (h m hm).2.1
  · exact MvPolynomial.degreeOf_le_iff.mpr fun m hm => (h m hm).2.2.1
  · exact fun m hm => (h m hm).2.2.2
/-- The smaller cutoff and larger message degree give a subspace of the previous primary bank. -/
private theorem included : SourceSpace ≤ P3_6_2.SourceSpace := by
  intro Q hQ e he
  obtain ⟨hb, hj, ht, hw⟩ := hQ he
  refine ⟨hb, hj, ht, ?_⟩
  have mono : e.weight (differentialWeight 133344) ≤ e.weight (differentialWeight 133419) := by
    apply Finsupp.weight_le_weight
    intro j
    cases j with
    | none => rfl
    | some i => exact Nat.sub_le_sub_right (by decide : 133344 ≤ 133419) i.val
  exact mono.trans (hw.trans (by decide))

def wordMap (w : I → K) : SourceSpace →ₗ[Geom] (I → Local) :=
  (P3_6_2.wordMap w).comp (Submodule.inclusion included)

theorem word_rank (w : I → K) :
    Module.finrank Geom (LinearMap.range (wordMap w)) ≤ 262144 * 344122366652253 :=
  (LinearMap.finrank_range_comp_le_left _ _).trans (P3_6_2.word_rank_le w Primary82170.origin_rank)

theorem contact_of_word_kernel (w : I → K) (Q : SourceSpace) (hQ : wordMap w Q = 0) :
    Contact w (toRow Q.1) :=
  P3_6_2.contact_of_word_kernel w (Submodule.inclusion included Q) hQ

theorem finrank_source : Module.finrank Geom SourceSpace = sourceColumns.card := by
  have h : (↑sourceColumns : Set SourceExponent) = sourceExponents :=
    Set.Finite.coe_toFinset sourceExponents_finite
  rw [SourceSpace, ← h]
  exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) sourceColumns

open K1_13_2 (SourceExponent topWeight)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finset
open scoped BigOperators
open private Column P0_9_2.exponent coordinates coordinates_exponent P0_9_2.exponent_coordinates scaled_sum
  from ProximityPrize.SubmissionLower.PortLowBase
private def width (a b c f : ℕ) : ℕ :=
  539862000 + b + 2 * c + 3 * f - 133419 * (a + b + c + f)
private def tuples : Finset Column :=
  (range 551).sigma fun f =>
    (range ((1650 - 3 * f) / 2 + 1)).sigma fun c =>
      (range (1651 - 2 * c - 3 * f)).sigma fun b =>
        (range (4013 - b - c - f)).sigma fun a => range (width a b c f)
private theorem mem_columns (t : Column) :
    P0_9_2.exponent t ∈ sourceColumns ↔ t ∈ tuples := by
  rcases t with ⟨f, c, b, a, x⟩
  change P0_9_2.exponent ⟨f, c, b, a, x⟩ ∈ sourceExponents_finite.toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change SourceEligible (P0_9_2.exponent ⟨f, c, b, a, x⟩) ↔ _
  simp only [tuples, mem_sigma, mem_range, SourceEligible, Finsupp.weight_eq_sum,
    Fintype.sum_option, Fin.sum_univ_succ, Fin.sum_univ_zero, smul_eq_mul,
    jetDegreeWeight_none, jetDegreeWeight_some, jetDerivativeWeight, differentialWeight,
    topWeight, Option.elim_none, Option.elim_some, P0_9_2.exponent, Finsupp.coe_equivFunOnFinite_symm]
  simp [width]
  omega
private theorem card_columns : sourceColumns.card = tuples.card := by
  let e : Column ≃ SourceExponent :=
    ⟨P0_9_2.exponent, coordinates, coordinates_exponent, P0_9_2.exponent_coordinates⟩
  exact (Finset.card_equiv e (fun t => (mem_columns t).symm)).symm
private def widthInt (a b c f : ℤ) : ℤ :=
  539862000 + b + 2 * c + 3 * f - 133419 * (a + b + c + f)
private theorem cast_width (a b c f : ℕ) (h : a + b + c + f ≤ 4012) :
    (width a b c f : ℤ) = widthInt a b c f := by
  have hpos : 133419 * (a + b + c + f) ≤ 539862000 + b + 2 * c + 3 * f := by omega
  simp [width, widthInt, Nat.cast_sub hpos]
private def prefixA (b c f n : ℤ) : ℤ :=
  n * (2 * widthInt 0 b c f - 133419 * (n - 1))
private def doubleA (b c f : ℤ) : ℤ :=
  prefixA b c f (4013 - b - c - f)
private def prefixB (c f n : ℤ) : ℤ :=
  let p := 4013 - c - f
  let q := 2 * widthInt 0 0 c f - 133419 * (p - 1)
  let r := 2 - 133419
  6 * n * p * q + 3 * n * (n - 1) * (p * r - q) - n * (n - 1) * (2 * n - 1) * r
private def twelveB (c f : ℤ) : ℤ :=
  prefixB c f (1651 - 2 * c - 3 * f)
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
private theorem evaluate_closedC : evaluate closedC 551 = 26291754481793903517024 := by
  rfl

theorem exact_source_columns : sourceColumns.card = 91290814172895498323 := by
  have h : 288 * (tuples.card : ℤ) = 26291754481793903517024 := by
    rw [card_tuples_int, mul_sum]
    calc
      _ = ∑ f ∈ range 551, closedC f :=
        sum_congr rfl fun f hf => countC_closed f (mem_range.mp hf)
      _ = _ := by rw [sum_eq_evaluate, evaluate_closedC]
  rw [card_columns]
  omega

private theorem family_of_kernel (w : I → K) {n : ℕ}
    (hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap w))) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) ⟨4012,1650,550⟩ ∧
        TrueWeightLE (e i) (3000*179954-1) ∧ Contact w (e i) := by
  let liftRow : LinearMap.ker (wordMap w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp (SourceSpace.subtype.comp (LinearMap.ker (wordMap w)).subtype)
  have hinj : Function.Injective liftRow := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  let admissible (P : Row 4) := InBox (shape P) ⟨4012,1650,550⟩ ∧
    TrueWeightLE P (3000*179954-1) ∧ Contact w P
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
/-- Independent primary rows for every received word up through physical degree 133,393. -/
theorem primary_family (w : I → K) :
    ∃ e : Fin 1081200489207287891 → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) ⟨4012,1650,550⟩ ∧
        TrueWeightLE (e i) (3000*179954-1) ∧ Contact w (e i) := by
  apply family_of_kernel
  have hd := (wordMap w).finrank_range_add_finrank_ker
  have hc := finrank_source.trans exact_source_columns
  have hr := word_rank w
  omega

theorem quotient : 1081200489207287891 / (179954 - 133419 + 3) = 23232637612430 := by decide

#print axioms primary_family
end
end PrimaryRows82190
