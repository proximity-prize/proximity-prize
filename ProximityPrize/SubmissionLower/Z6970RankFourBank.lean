import ProximityPrize.SubmissionLower.HighCore82258Pairs

section RankFourBankData
set_option autoImplicit false
namespace P2_4At6970
noncomputable section
open P2 MvPolynomial
def WedgeBounds (h : ℕ) (U V : MvPolynomial (Fin 5) K) : Prop :=
  (L - h) * U.degreeOf 3 ≤ h ∧ (L - h) * U.degreeOf 4 ≤ L ∧
    (L - h) * V.degreeOf 3 ≤ L ∧ (L - h) * V.degreeOf 4 ≤ h
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  bounds : WedgeBounds T.height U V
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : K1_11_2.graph p U = Polynomial.C content * leftU R
  graphV : K1_11_2.graph p V = Polynomial.C content * leftV R
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ A.U
  V_dvd : V ∣ A.V
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  graphU : K1_11_2.graph p U = Polynomial.C A.content * D.U
  graphV : K1_11_2.graph p V = Polynomial.C A.content * D.V
abbrev Puncture := K1_11.Puncture
open K1_11 (sourceWeights scalarWeightY scalarWeightYS scalarWeightT
  contactLift contactWeight contactShift polynomialView scalarImages)
structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted
inductive Bank
  | w22 | w22Swapped | w12 | w21 | w13 | w23 | w31 | w32 | w33 | w33Swapped
def Bank.dS : Bank → ℕ
  | .w22 | .w22Swapped | .w21 | .w23 => 2
  | .w12 | .w13 => 1
  | .w31 | .w32 | .w33 | .w33Swapped => 3
def Bank.dT : Bank → ℕ
  | .w22 | .w22Swapped | .w12 | .w32 => 2
  | .w21 | .w31 => 1
  | .w13 | .w23 | .w33 | .w33Swapped => 3
def Bank.s : Bank → ℕ
  | .w12 => 16
  | .w13 => 8
  | .w21 => 11
  | .w22 => 11
  | .w22Swapped => 10
  | .w23 => 8
  | .w31 => 7
  | .w32 => 6
  | .w33 => 6
  | .w33Swapped => 8
def Bank.t : Bank → ℕ
  | .w12 => 11
  | .w13 => 7
  | .w21 => 16
  | .w22 => 10
  | .w22Swapped => 11
  | .w23 => 6
  | .w31 => 8
  | .w32 => 8
  | .w33 => 8
  | .w33Swapped => 6
def Bank.a (b : Bank) : ℕ := b.s + 5 * b.dS
def Bank.b (b : Bank) : ℕ := b.t + 5 * (b.dT - 1)
def Bank.E (b : Bank) : ℕ := b.a + b.b
def Bank.M (b : Bank) : ℕ := (2 * 131071 - 1) * (b.E - 1) + 1
def Bank.zeroFee (b : Bank) : ℕ := b.a + p * b.b
abbrev nodeCut := K1_11.nodeCut
def Bank.relationBounds (b : Bank) (H : ℕ) : Fin 4 → ℕ := ![131071 + H, 1, b.dS, b.dT]
structure ContactInput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (b : Bank) (H : ℕ) where
  L : MvPolynomial (Fin 5) K
  L_ne : L ≠ 0
  degrees : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j
  order_one : ∀ i : Fin P.N,
    (contactLift contactWeight
      (contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) L)).natTrailingDegree = 1
  numerator : MvPolynomial (Fin 4) K
  denominator : MvPolynomial (Fin 4) K
  denominator_ne : denominator ≠ 0
  linear : polynomialView L =
    Polynomial.C denominator * Polynomial.X - Polynomial.C numerator
  primitive : (Polynomial.C denominator * Polynomial.X - Polynomial.C numerator).IsPrimitive
  numerator_Y : numerator.weightedTotalDegree scalarWeightY ≤ 1
  denominator_Y : denominator.weightedTotalDegree scalarWeightY ≤ 0
  numerator_S : numerator.weightedTotalDegree scalarWeightYS ≤ b.dS
  denominator_S : denominator.weightedTotalDegree scalarWeightYS ≤ b.dS
  numerator_T : numerator.weightedTotalDegree scalarWeightT ≤ b.dT
  denominator_T : denominator.weightedTotalDegree scalarWeightT ≤ b.dT - 1
abbrev scalarWeightTotal := K1_11.scalarWeightTotal
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)
end
end P2_4At6970
end RankFourBankData
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace P2_4At6970
noncomputable section
open P2 MvPolynomial
open K1_11_3 (SimpleRoot derivativeChart exists_simple_derivative_at_root)
open K1_11_3 (exceptions specializeY yView_degree specializeY_eval specializeY_iterate specializeY_derivative)
open K1_11_3 (centerPoint atCenter atCenter_degree numerator numerator_degree denominator eval_atCenter pderiv_atCenter numerator_eval_degree denominator_degree reconstruct natDegree_le_of_degree_lt_succ derivativeChart_degree)
theorem assign {u : Words} {deleted : Finset I} {Γ : Finset K}
    {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, ∃ hsub : charts j ⊆ Γ, ∀ γ (hγ : γ ∈ charts j),
        SimpleRoot (derivativeChart A.Q j) (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
  classical
  obtain ⟨exceptional, hfee, hex⟩ := exceptions A.Q A.nonzero p b.a b.b (by decide)
    (by cases b <;> decide) A.degreeS A.degreeT Γ
  have hassign (γ : K) (hγ : γ ∈ Γ) (hn : γ ∉ exceptional) :
      ∃ j : Fin 5, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p) := by
    let f := specializeY A.Q γ (γ ^ p)
    have hdeg : f.natDegree ≤ 5 :=
      (Polynomial.natDegree_map_le).trans ((yView_degree A.Q).le.trans A.degreeY)
    have hroot : f.IsRoot (F.mark γ hγ).decoder :=
      (specializeY_eval A.Q _ γ (γ ^ p)).trans (A.vanishes γ hγ)
    obtain ⟨j, hj, hz, hnz⟩ := exists_simple_derivative_at_root p 5 f
      (hex γ hγ hn) hdeg (by decide) _ hroot
    refine ⟨⟨j,hj⟩, ?_, ?_⟩
    · rw [← specializeY_eval, specializeY_iterate]
      exact hz
    · rw [← specializeY_eval, specializeY_derivative, specializeY_iterate]
      exact hnz
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p)
  refine ⟨exceptional, charts, hfee, ?_, ?_⟩
  · intro γ hγ
    by_cases he : γ ∈ exceptional
    · exact Or.inl he
    · obtain ⟨j,hj⟩ := hassign γ hγ he
      exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  · intro j
    refine ⟨fun _ hγ => (Finset.mem_filter.mp hγ).1, ?_⟩
    intro γ hγ
    obtain ⟨_, h⟩ := (Finset.mem_filter.mp hγ).2
    exact h
private theorem build_chart
    {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank)
    (Λ : Finset K) (hsub : Λ ⊆ Γ) (hne : Λ.Nonempty)
    (G : MvPolynomial (Fin 4) K) (hG : G.weightedTotalDegree scalarWeightTotal ≤ b.E)
    (hroot : ∀ γ (hγ : γ ∈ Λ),
      SimpleRoot G (F.mark γ (hsub hγ)).decoder γ (γ ^ p)) :
    Nonempty (TaylorChart u P F b Λ) := by
  classical
  let point (γ : K) : Fin 3 → Frac := if h : γ ∈ Λ then
    centerPoint (F.mark γ (hsub h)).decoder γ (γ ^ p) else fun _ => 0
  have hpnt (γ : K) (hγ : γ ∈ Λ) :
      point γ = centerPoint (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
    simp [point, hγ]
  refine ⟨{
    subset := hsub
    equation := atCenter G
    equation_ne := ?_
    equation_degree := (atCenter_degree G).trans hG
    numerator := K1_11_3.numerator G 131071
    numerator_degree := numerator_degree _ _
    denominator := K1_11_3.denominator G 131071
    cut_degree := ?_
    point := point
    slope := fun γ hγ => by rw [hpnt γ hγ]; rfl
    on_equation := fun γ hγ => by rw [hpnt γ hγ, eval_atCenter, (hroot γ hγ).1, map_zero]
    regular := ?_
    reconstruction := ?_ }⟩
  · obtain ⟨γ, hγ⟩ := hne
    have hn := (hroot γ hγ).2
    intro hz
    apply hn
    apply (IsFractionRing.injective (Polynomial K) Frac)
    rw [map_zero, ← eval_atCenter, ← pderiv_atCenter, hz, map_zero, map_zero]
  · intro i
    unfold nodeCut
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact numerator_eval_degree K1_11_3_1.proof G 131071 b.E (by cases b <;> decide) hG _
    · apply (totalDegree_mul _ _).trans
      have ha : (C (σ := Fin 3) (algebraMap K Frac (u 0 (P.index i))) +
          MvPolynomial.X 1 * C (algebraMap K Frac (u 1 (P.index i)))).totalDegree ≤ 1 := by
        exact (totalDegree_add _ _).trans (max_le (by simp)
          ((totalDegree_mul _ _).trans (by simp)))
      exact Nat.add_le_add (denominator_degree G 131071 b.E hG) ha
  · intro γ hγ
    rw [hpnt γ hγ, K1_11_3.denominator, map_pow, eval_atCenter]
    exact pow_ne_zero _ (fun h => (hroot γ hγ).2
      ((IsFractionRing.injective (Polynomial K) Frac) (h.trans (map_zero _).symm)))
  · intro γ hγ
    rw [hpnt γ hγ]
    apply reconstruct K1_11_3_2.proof
    · exact natDegree_le_of_degree_lt_succ (F.mark γ (hsub hγ)).degree
    · exact (hroot γ hγ).1
    · intro n hn
      have pp := CharP.char_is_prime_of_two_le K p (by decide)
      intro hz
      have hn' := pp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K p _).mp hz)
      exact (not_lt_of_ge (hn'.trans hn)) (by decide)
theorem chart_cover {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, charts j = ∅ ∨ Nonempty (TaylorChart u P F b (charts j)) := by
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ := assign A
  refine ⟨exceptional, charts, hfee, hcover, fun j => ?_⟩
  rcases (charts j).eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  · obtain ⟨hsub, hroot⟩ := hcharts j
    exact Or.inr (build_chart P F b (charts j) hsub hn (derivativeChart A.Q j)
      ((derivativeChart_degree A.Q j).trans A.degreeTotal) hroot)
end
end P2_4At6970
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P2_4At6970
open P2 Finset
open K1_11 (V J)
open P0_7 (countRow gradeRow count grade contactRow V_affine rational_fee)
open P1_4 (dims_5_16_10 dims_4_15_8 jets_4_16_10 jets_3_15_8 dims_5_8_7 dims_4_7_4 jets_4_8_7 jets_3_7_4 dims_5_10_16 dims_4_8_15 jets_4_10_16 jets_3_8_15 dims_5_11_10 dims_4_9_8 jets_4_11_10 jets_3_9_8 dims_5_8_6 dims_4_6_3 jets_4_8_6 jets_3_6_3 dims_5_7_8 dims_4_4_7 jets_4_7_8 jets_3_4_7 dims_5_6_8 dims_4_3_6 jets_4_6_8 jets_3_3_6 dims_4_3_5 jets_3_3_5)
theorem dims_5_10_11 : count 5 10 11 = 2002 ∧ grade 5 10 11 = 6174 := by
  constructor
  · have r0 : countRow 5 10 11 0 = 627 := by decide
    have r1 : countRow 5 10 11 1 = 500 := by decide
    have r2 : countRow 5 10 11 2 = 378 := by decide
    have r3 : countRow 5 10 11 3 = 264 := by decide
    have r4 : countRow 5 10 11 4 = 161 := by decide
    have r5 : countRow 5 10 11 5 = 72 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 10 11 i) = 6174
    have r0 : gradeRow 5 10 11 0 = 1375 := by decide
    have r1 : gradeRow 5 10 11 1 = 1400 := by decide
    have r2 : gradeRow 5 10 11 2 = 1278 := by decide
    have r3 : gradeRow 5 10 11 3 = 1040 := by decide
    have r4 : gradeRow 5 10 11 4 = 721 := by decide
    have r5 : gradeRow 5 10 11 5 = 360 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
theorem jets_4_10_11 : J 4 10 11 = 2301 := by
  change (∑ i ∈ range 4, contactRow 4 10 11 i) = 2301
  have r0 : contactRow 4 10 11 0 = 1210 := by decide
  have r1 : contactRow 4 10 11 1 = 680 := by decide
  have r2 : contactRow 4 10 11 2 = 315 := by decide
  have r3 : contactRow 4 10 11 3 = 96 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
theorem dims_4_8_9 : count 4 8 9 = 985 ∧ grade 4 8 9 = 2419 := by
  constructor
  · have r0 : countRow 4 8 9 0 = 360 := by decide
    have r1 : countRow 4 8 9 1 = 272 := by decide
    have r2 : countRow 4 8 9 2 = 189 := by decide
    have r3 : countRow 4 8 9 3 = 114 := by decide
    have r4 : countRow 4 8 9 4 = 50 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 8 9 i) = 2419
    have r0 : gradeRow 4 8 9 0 = 630 := by decide
    have r1 : gradeRow 4 8 9 1 = 640 := by decide
    have r2 : gradeRow 4 8 9 2 = 553 := by decide
    have r3 : gradeRow 4 8 9 3 = 396 := by decide
    have r4 : gradeRow 4 8 9 4 = 200 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
theorem jets_3_8_9 : J 3 8 9 = 806 := by
  change (∑ i ∈ range 3, contactRow 3 8 9 i) = 806
  have r0 : contactRow 3 8 9 0 = 504 := by decide
  have r1 : contactRow 3 8 9 1 = 232 := by decide
  have r2 : contactRow 3 8 9 2 = 70 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
theorem dims_4_5_3 : count 4 5 3 = 175 ∧ grade 4 5 3 = 364 := by
  constructor
  · have r0 : countRow 4 5 3 0 = 60 := by decide
    have r1 : countRow 4 5 3 1 = 50 := by decide
    have r2 : countRow 4 5 3 2 = 36 := by decide
    have r3 : countRow 4 5 3 3 = 21 := by decide
    have r4 : countRow 4 5 3 4 = 8 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 5 3 i) = 364
    have r0 : gradeRow 4 5 3 0 = 60 := by decide
    have r1 : gradeRow 4 5 3 1 = 100 := by decide
    have r2 : gradeRow 4 5 3 2 = 100 := by decide
    have r3 : gradeRow 4 5 3 3 = 72 := by decide
    have r4 : gradeRow 4 5 3 4 = 32 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
theorem jets_3_5_3 : J 3 5 3 = 191 := by
  change (∑ i ∈ range 3, contactRow 3 5 3 i) = 191
  have r0 : contactRow 3 5 3 0 = 120 := by decide
  have r1 : contactRow 3 5 3 1 = 55 := by decide
  have r2 : contactRow 3 5 3 2 = 16 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
end P2_4At6970
end
section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace P2_4At6970
noncomputable section
open MvPolynomial
open P2 (heightCap)
open K1_11 (V J filtered filteredMul filteredMul_injective mem_filteredMul_range_iff
  sourceWeights sourceBounds source_filtered_finrank JetSpace jetSpace_finrank sourceToJet
  contactShift contactLift contactWeight contactShift_parameter_weights
  truncated_mul_mem_jet contact_product_not_high_order
  jetSpace_support_bound)
open K1_11 (exists_kernel_outside)
abbrev Multipliers (F : Type*) [Field F] (b : Bank) := JetSpace F 2 (b.s - b.dS) (b.t - b.dT)
variable {F : Type*} [Field F]
structure ContactData (N : ℕ) (L : MvPolynomial (Fin 5) F) (b : Bank) where
  x : Fin N → F
  first : Fin N → F
  firstSlope : Fin N → F
  second : Fin N → F
  secondSlope : Fin N → F
  nonzero : L ≠ 0
  degreeS : L.weightedTotalDegree (sourceWeights 1 2) ≤ b.dS
  degreeT : L.weightedTotalDegree (sourceWeights 1 3) ≤ b.dT
  order_one : ∀ i, (contactLift contactWeight
    (contactShift (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree = 1
variable {N : ℕ} {L : MvPolynomial (Fin 5) F} {b : Bank} {H : ℕ} (D : ContactData N L b)
def ContactData.shifted (i : Fin N) (Q : MvPolynomial (Fin 5) F) :=
  contactShift (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q
private theorem shifted_S (i : Fin N) :
    (D.shifted i L).weightedTotalDegree (sourceWeights 1 2) ≤ b.dS := by
  apply (contactShift_parameter_weights _ _ _ _ _ L).1.trans
  exact D.degreeS
private theorem shifted_T (i : Fin N) :
    (D.shifted i L).weightedTotalDegree (sourceWeights 1 3) ≤ b.dT := by
  apply (contactShift_parameter_weights _ _ _ _ _ L).2.trans
  exact D.degreeT
private theorem shifted_ne (i : Fin N) : D.shifted i L ≠ 0 := by
  intro hz
  have hh := D.order_one i
  change (contactLift contactWeight (D.shifted i L)).natTrailingDegree = 1 at hh
  simp [hz] at hh
private theorem bank_s (b : Bank) : b.s - b.dS + b.dS = b.s := by cases b <;> rfl
private theorem bank_t (b : Bank) : b.t - b.dT + b.dT = b.t := by cases b <;> rfl
def localMultiply (i : Fin N) : Multipliers F b →ₗ[F] JetSpace F 3 b.s b.t where
  toFun Q := ⟨weightedTruncation contactWeight 4 (D.shifted i L * Q.val), by
    simpa only [bank_s, bank_t] using
      truncated_mul_mem_jet 2 (b.s-b.dS) (b.t-b.dT) b.dS b.dT (D.shifted i L)
        (shifted_S D i) (shifted_T D i) Q⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp
private theorem localMultiply_injective (i : Fin N) :
    Function.Injective (localMultiply D i) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro Q hQ
  by_contra hn
  have hprod : weightedTruncation contactWeight 4 (D.shifted i L * Q.val) = 0 :=
    congrArg (fun x : JetSpace F 3 b.s b.t => x.val) hQ
  have hhigh := (weightedTruncation_eq_zero_iff _ _ _).mp hprod
  have hQn : Q.val ≠ 0 := fun hz => hn (Subtype.ext hz)
  exact contact_product_not_high_order contactWeight 4 (D.shifted i L) Q.val
    (D.order_one i) (shifted_ne D i) hQn (jetSpace_support_bound _ _ _ Q) hhigh
abbrev LocalSpace (i : Fin N) :=
  (JetSpace F 3 b.s b.t) ⧸ LinearMap.range (localMultiply D i)
theorem local_finrank (i : Fin N) :
    Module.finrank F (LocalSpace D i) = J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT) := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (localMultiply D i))
  rw [LinearMap.finrank_range_of_inj (localMultiply_injective D i), jetSpace_finrank,
    jetSpace_finrank] at hq
  change Module.finrank F (LocalSpace D i) + J 3 (b.s-b.dS) (b.t-b.dT) = J 4 b.s b.t at hq
  omega
end
end P2_4At6970
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace P2_4At6970
noncomputable section
open P2 FrobeniusLocator MvPolynomial
open K1_11 (V J contactLift contactWeight contactShift
  contactLift_X_pow_dvd_iff
  contactDecoderImages_vanish decoder_contact_composition decoder_eval_degree
  eq_zero_of_many_contacts decoder_contact_multiplicity decoderImages contactDecoderImages
  sourceWeights mem_filtered correctOn nodes_injective indexedSupport indexedSupport_card
  mem_indexedSupport scalarWeightY scalarWeightYS scalarWeightT scalarEliminant
  scalarEliminant_ne_zero polynomialView_source_coefficients clearedEval_weight_bound
  polynomialView scalarEliminant_annihilates)
open K1_11 (scalar_total_weight_le)
variable {u : Words} {deleted : Finset I} {P : Puncture deleted} {b : Bank} {H : ℕ}
    (D : ContactInput u P b H)
def ContactInput.shifted (_D : ContactInput u P b H) (i : Fin P.N) (Q : MvPolynomial (Fin 5) K) :=
  contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
    (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) Q
def asContactData : ContactData P.N D.L b where
  x := P.nodes
  first := fun i => u 0 (P.index i)
  firstSlope := fun i => u 1 (P.index i)
  second := fun i => u 0 (P.index i) ^ p
  secondSlope := fun i => u 1 (P.index i) ^ p
  nonzero := D.L_ne
  degreeS := le_of_eq (D.degrees 2)
  degreeT := le_of_eq (D.degrees 3)
  order_one := D.order_one
theorem contact_order_one_mem {σ : Type*} (v : σ → ℕ) (L : MvPolynomial σ K)
    (hL : (contactLift v L).natTrailingDegree = 1) : L ∈ restrictWeightedOrder v 1 := by
  apply (contactLift_X_pow_dvd_iff v 1 L).mp
  apply Polynomial.X_pow_dvd_iff.mpr
  intro d hd
  apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
  omega
theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree < (131072 : ℕ) from M.degree)
theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [Strata.eval_coefficient_map twist M.decoder _ (Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, P0.twist, frobenius_def]
theorem bank_cancel (b : Bank) : 1 + (b.dT - 1) = b.dT := by cases b <;> rfl
end
end P2_4At6970
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace P2_4At6970
noncomputable section
open P2 MvPolynomial
open scoped BigOperators
open K1_11 (indexedSupport mem_indexedSupport indexedSupport_card nodes_injective)
open K1_11 (ncard_inter_filter surface_count_with_terminal)
open K1_11 (seed_eq_of_mismatch)
variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
private theorem pencil_bad_count (hsub : Λ ⊆ Γ) (P₀ P₁ : Polynomial K)
    (h₀ : P₀.degree < (131072 : ℕ)) (h₁ : P₁.degree < (131072 : ℕ))
    (pencil : ∀ γ (hγ : γ ∈ Λ),
      (F.mark γ (hsub hγ)).decoder = P₀ + Polynomial.C γ * P₁) :
    Λ.card ≤ P.N := by
  classical
  have mismatch (γ : Λ) :
      ∃ i : Fin P.N,
        (P₀.eval (P.nodes i) ≠ u 0 (P.index i) ∨ P₁.eval (P.nodes i) ≠ u 1 (P.index i)) ∧
        P₀.eval (P.nodes i) + (γ : K) * P₁.eval (P.nodes i) =
          u 0 (P.index i) + (γ : K) * u 1 (P.index i) := by
    let M := F.mark γ (hsub γ.property)
    obtain ⟨idx, hi, hm⟩ :
        ∃ idx ∈ M.support, P₀.eval (node idx) ≠ u 0 idx ∨ P₁.eval (node idx) ≠ u 1 idx := by
      by_contra hn
      push Not at hn
      exact M.nonjoint ⟨⟨P₀, h₀, fun j hj => (hn j hj).1⟩, ⟨P₁, h₁, fun j hj => (hn j hj).2⟩⟩
    obtain ⟨i, rfl⟩ := (P.retained idx).mpr (F.survives γ (hsub γ.property) idx hi)
    refine ⟨i, hm, ?_⟩
    have hh := M.hits (P.index i) hi
    change (F.mark (γ : K) (hsub γ.property)).decoder.eval (P.nodes i) = _ at hh
    simpa only [pencil _ γ.property, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C] using hh
  let f : Λ → Fin P.N := fun γ => Classical.choose (mismatch γ)
  have hf : Function.Injective f := by
    intro γ δ he
    apply Subtype.ext
    obtain ⟨hm, hγ⟩ := Classical.choose_spec (mismatch γ)
    have hδ := (Classical.choose_spec (mismatch δ)).2
    change f γ = f δ at he
    change
      (P₀.eval (P.nodes (f γ)) ≠ u 0 (P.index (f γ)) ∨
        P₁.eval (P.nodes (f γ)) ≠ u 1 (P.index (f γ))) at hm
    change P₀.eval (P.nodes (f γ)) + (γ : K) * P₁.eval (P.nodes (f γ)) =
      u 0 (P.index (f γ)) + (γ : K) * u 1 (P.index (f γ)) at hγ
    change P₀.eval (P.nodes (f δ)) + (δ : K) * P₁.eval (P.nodes (f δ)) =
      u 0 (P.index (f δ)) + (δ : K) * u 1 (P.index (f δ)) at hδ
    rw [← he] at hδ
    exact seed_eq_of_mismatch (F := K) hγ hδ hm
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf
variable (chart : TaylorChart u P F b Λ)
theorem chart_cut_iff (γ : K) (hγ : γ ∈ Λ) (i : Fin P.N) :
    MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 ↔
      (F.mark γ (chart.subset hγ)).decoder.eval (P.nodes i) =
        u 0 (P.index i) + γ * u 1 (P.index i) := by
  let val := MvPolynomial.eval (chart.point γ)
  let x := algebraMap K Frac (P.nodes i)
  change val (nodeCut u P chart.numerator chart.denominator i) = 0 ↔ _
  have heval := Polynomial.eval_map_apply val (C x) (p := chart.numerator)
  unfold nodeCut
  change val (chart.numerator.eval (C x) - _) = 0 ↔ _
  rw [map_sub, ← heval]
  change (chart.numerator.map val).eval (val (C x)) - _ = 0 ↔ _
  rw [show val (C x) = x by simp [val], show chart.numerator.map val = _ from chart.reconstruction γ hγ]
  rw [Polynomial.eval_mul, Polynomial.eval_C, show x = algebraMap K Frac (P.nodes i) from rfl,
    Polynomial.eval_map_apply, map_mul, map_add, map_mul]
  simp only [val, eval_C, eval_X, chart.slope γ hγ]
  rw [← map_mul, ← map_add, sub_eq_zero]
  constructor
  · intro h
    exact (algebraMap K Frac).injective (mul_left_cancel₀ (chart.regular γ hγ) h)
  · intro h
    rw [h]
theorem chart_persistent (J : Ideal (MvPolynomial (Fin 3) Frac)) (W : Finset K) (hW : W ⊆ Λ)
    (hzero : ∀ γ ∈ W, chart.point γ ∈ zeroLocus Frac J)
    (hpersist : 131072 ≤ {i | nodeCut u P chart.numerator chart.denominator i ∈ J}.ncard) :
    W.card ≤ P.N := by
  classical
  let keep := Finset.univ.filter fun i => nodeCut u P chart.numerator chart.denominator i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersist.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P₀ := Lagrange.interpolate S P.nodes (fun i => u 0 (P.index i))
  let P₁ := Lagrange.interpolate S P.nodes (fun i => u 1 (P.index i))
  have hinj : Set.InjOn P.nodes (S : Set (Fin P.N)) := nodes_injective.injOn
  have hd₀ : P₀.degree < (131072 : ℕ) := by
    simpa only [P₀, hcard] using Lagrange.degree_interpolate_lt (fun i => u 0 (P.index i)) hinj
  have hd₁ : P₁.degree < (131072 : ℕ) := by
    simpa only [P₁, hcard] using Lagrange.degree_interpolate_lt (fun i => u 1 (P.index i)) hinj
  apply pencil_bad_count (P := P) (F := F) (fun _ hg => chart.subset (hW hg)) P₀ P₁ hd₀ hd₁
  intro γ hγ
  let M := F.mark γ (chart.subset (hW hγ))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (mark_degree M)))
  · rw [hcard]
    have hm : (Polynomial.C γ * P₁).degree ≤ P₁.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) P₁.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hd₀ (hm.trans_lt hd₁))
  · intro i hi
    have hcut : nodeCut u P chart.numerator chart.denominator i ∈ J := (Finset.mem_filter.mp (hS hi)).2
    have hz : MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 :=
      hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (chart_cut_iff chart γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])
end
end P2_4At6970
end
