import ProximityPrize.SubmissionLower.PortFrontB
import ProximityPrize.SubmissionLower.RungSplit
set_option autoImplicit true
section
namespace P1_3
noncomputable section
open P1 Polynomial
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : K[X] :=
  B.a * (B.β l).map twist
abbrev Plane := K1_10.Plane
abbrev Adjugate := K1_10.Adjugate
inductive Bank where
  | st
  | ts
def Bank.first : Bank → ℕ
  | .st => 20
  | .ts => 17
def Bank.second : Bank → ℕ
  | .st => 17
  | .ts => 20
abbrev sourceCutoff : ℕ := 4 * agreement - 1
def quotientSurplus (bank : Bank) (n h : ℕ) : Prop :=
  n * (K1_10.jetDim 4 bank.first bank.second -
      K1_10.jetDim 3 (bank.first - 1) (bank.second - 1)) <
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second -
      K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4
        (bank.first - 1) (bank.second - 1)
structure ScalarSource (bank : Bank) where
  poly : MvPolynomial (Fin 2) K1_10.SeedPoly
  nonzero : poly ≠ 0
  y_degree : poly.degreeOf 1 ≤ 5
  s_degree : ∀ e ∈ poly.support, (poly.coeff e).degreeOf 0 ≤ bank.first + 5
  t_degree : ∀ e ∈ poly.support, (poly.coeff e).degreeOf 1 ≤ bank.second
  total : ∀ e ∈ poly.support, e 1 + (poly.coeff e).totalDegree ≤ 42
def ScalarSource.atLabel {bank} (A : ScalarSource bank) (γ : K) : MvPolynomial (Fin 2) K :=
  A.poly.map (MvPolynomial.eval ![γ, γ ^ p])
def ScalarSource.atDecoder {bank} (A : ScalarSource bank) (γ : K) (P : K[X]) : K[X] :=
  MvPolynomial.aeval ![Polynomial.X, P] (A.atLabel γ)
abbrev cutDegree : ℕ := (2 * (k - 1) - 1) * (42 - 1) + 1
def incidenceRatio : ℚ :=
  (((blockLength - (k - 1)) * cutDegree : ℕ) : ℚ) / ((agreement - (k - 1) : ℕ) : ℚ)
def Bank.graphFee (bank : Bank) : ℕ := bank.first + 5 + p * bank.second
end
end P1_3
end
section
namespace P1_3
noncomputable section
open P1
open scoped BigOperators
open private sum_rows ceil_sq_div_eq from ProximityPrize.SubmissionLower.PortFrontB
theorem jet_st : K1_10.jetDim 4 20 17 = 6981 := by
  let rows : Fin 4 → ℕ := ![3570, 2080, 1007, 324]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 4, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 6981 := by decide
theorem jet_ts : K1_10.jetDim 4 17 20 = 6981 := by
  let rows : Fin 4 → ℕ := ![3600, 2074, 992, 315]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 4, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 6981 := by decide
theorem local_st : K1_10.jetDim 3 19 16 = 3216 := by
  let rows : Fin 3 → ℕ := ![1960, 950, 306]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 3, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 3216 := by decide
theorem local_ts : K1_10.jetDim 3 16 19 = 3216 := by
  let rows : Fin 3 → ℕ := ![1972, 944, 300]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 3, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 3216 := by decide
private theorem jet_quotient (bank : Bank) :
    K1_10.jetDim 4 bank.first bank.second -
      K1_10.jetDim 3 (bank.first - 1) (bank.second - 1) = 3765 := by
  cases bank
  · change K1_10.jetDim 4 20 17 - K1_10.jetDim 3 19 16 = 3765
    rw [jet_st, local_st]
  · change K1_10.jetDim 4 17 20 - K1_10.jetDim 3 16 19 = 3765
    rw [jet_ts, local_ts]
end
end P1_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace P1_3_1
noncomputable section
open MvPolynomial K1_11
open K1_10_1 (Contacts relationBounds)
open P1_3 (sourceCutoff)
open private exists_kernel_outside from ProximityPrize.SubmissionLower.PortFrontB
abbrev Source (F : Type*) [Field F] (bank : P1_3.Bank) :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds sourceCutoff 5 bank.first bank.second)
abbrev Multipliers (F : Type*) [Field F] (bank : P1_3.Bank) :=
  JetSpace F 2 (bank.first - 1) (bank.second - 1)
variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}
variable (bank : P1_3.Bank) (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)
theorem first_sub_add (b : P1_3.Bank) : b.first - 1 + 1 = b.first := by cases b <;> rfl
theorem second_sub_add (b : P1_3.Bank) : b.second - 1 + 1 = b.second := by cases b <;> rfl
private def localMultiply (i : Fin N) : Multipliers F bank →ₗ[F] JetSpace F 3 bank.first bank.second where
  toFun Q := ⟨weightedTruncation contactWeight 4 (C.shifted i L * Q.val), by
    simpa only [first_sub_add, second_sub_add] using
      truncated_mul_mem_jet 2 (bank.first - 1) (bank.second - 1) 1 1 (C.shifted i L)
        ((contactShift_parameter_weights _ _ _ _ _ L).1.trans (le_of_eq (hdeg 2)))
        ((contactShift_parameter_weights _ _ _ _ _ L).2.trans (le_of_eq (hdeg 3))) Q⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp
private abbrev LocalSpace (i : Fin N) :=
  (JetSpace F 3 bank.first bank.second) ⧸ LinearMap.range (localMultiply bank C hdeg i)
private theorem local_finrank (i : Fin N) :
    Module.finrank F (LocalSpace bank C hdeg i) =
      J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1) := by
  have hinj : Function.Injective (localMultiply bank C hdeg i) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro Q hQ
    by_contra hn
    have hprod : weightedTruncation contactWeight 4 (C.shifted i L * Q.val) = 0 :=
      congrArg (fun x : JetSpace F 3 bank.first bank.second => x.val) hQ
    have horder := C.order_one i
    change (contactLift contactWeight (C.shifted i L)).natTrailingDegree = 1 at horder
    have hL : C.shifted i L ≠ 0 := by
      intro hz
      simp [hz] at horder
    exact contact_product_not_high_order contactWeight 4 (C.shifted i L) Q.val
      horder hL (fun hz => hn (Subtype.ext hz)) (jetSpace_support_bound _ _ _ Q)
      ((weightedTruncation_eq_zero_iff _ _ _).mp hprod)
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (localMultiply bank C hdeg i))
  rw [LinearMap.finrank_range_of_inj hinj, jetSpace_finrank, jetSpace_finrank] at hq
  change Module.finrank F (LocalSpace bank C hdeg i) + J 3 (bank.first - 1) (bank.second - 1) =
    J 4 bank.first bank.second at hq
  omega
private def nodeMap (i : Fin N) : Source F bank →ₗ[F] LocalSpace bank C hdeg i :=
  (LinearMap.range (localMultiply bank C hdeg i)).mkQ.comp
    (sourceToJet sourceCutoff 131071 5 bank.first bank.second 3 (C.x i) (C.first i) (C.firstSlope i)
      (C.second i) (C.secondSlope i))
include hdeg in
theorem quotientSource (hL : L ≠ 0) (hh : h ≤ 33327) (hs : P1_3.quotientSurplus bank N h) :
    ∃ G : Source F bank, ¬ L ∣ G.val ∧ ∀ i, ∃ R : Multipliers F bank,
      C.shifted i G.val - C.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hfit : ∀ j, relationBounds h j ≤ sourceBounds sourceCutoff 5 bank.first bank.second j := by
    have hcapacity : 131071 + 33327 ≤ sourceCutoff := by decide
    intro j
    cases bank <;> fin_cases j <;> simp [relationBounds, sourceBounds, P1_3.Bank.first, P1_3.Bank.second] <;> omega
  have hshift : (fun j => sourceBounds sourceCutoff 5 bank.first bank.second j - relationBounds h j) =
      sourceBounds (sourceCutoff - 131071 - h) 4 (bank.first - 1) (bank.second - 1) := by
    funext j
    fin_cases j <;> simp [sourceBounds, relationBounds, Nat.sub_sub]
    omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds sourceCutoff 5 bank.first bank.second)
    (relationBounds h) L hL hdeg hfit
  have hmult : Module.finrank F (LinearMap.range mult) =
      V (sourceCutoff - 131071 - h) 131071 4 (bank.first - 1) (bank.second - 1) := by
    rw [LinearMap.finrank_range_of_inj (filteredMul_injective _ _ _ L hL hdeg hfit),
      hshift, source_filtered_finrank]
  let (i : Fin N) : Module.Free F (LocalSpace bank C hdeg i) := Module.Free.of_divisionRing F _
  let : Module F (∀ i : Fin N, LocalSpace bank C hdeg i) := Pi.module _ _ _
  have hlocal : Module.finrank F (∀ i : Fin N, LocalSpace bank C hdeg i) =
      N * (J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1)) := by
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank bank C hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace bank C hdeg i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F bank) := by
    rw [hlocal, hmult, source_filtered_finrank]
    change N * (J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1)) <
      V sourceCutoff 131071 5 bank.first bank.second -
        V (sourceCutoff - 131071 - h) 131071 4 (bank.first - 1) (bank.second - 1) at hs
    omega
  obtain ⟨G, hG, hnot⟩ := exists_kernel_outside (G := ∀ i : Fin N, LocalSpace bank C hdeg i)
    (LinearMap.pi (nodeMap bank C hdeg)) (LinearMap.range mult) hdim
  refine ⟨G, (mem_filteredMul_range_iff _ _ _ L hL hdeg hfit G).not.mp hnot, ?_⟩
  intro i
  have hi : nodeMap bank C hdeg i G = 0 := congrFun hG i
  obtain ⟨R, hR⟩ := (Submodule.Quotient.mk_eq_zero _).mp hi
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm
end
end P1_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace P1_3_1
noncomputable section
open MvPolynomial
open K1_11 (scalarWeightY scalarWeightYS scalarWeightT scalarWeightTotal scalarImages)
open K1_10_1 (groupSeeds)
open P1 (K p)
open P1_3 (Bank ScalarSource)
open private grouped_coeff joinExponents joinExponents_apply group_eval from ProximityPrize.SubmissionLower.Fast076
def toScalarSource {bank : Bank} (Q : MvPolynomial (Fin 4) K) (hn : Q ≠ 0)
    (hy : Q.weightedTotalDegree scalarWeightY ≤ 5)
    (hs : Q.weightedTotalDegree scalarWeightYS ≤ bank.first + 5)
    (ht : Q.weightedTotalDegree scalarWeightT ≤ bank.second)
    (htot : Q.weightedTotalDegree scalarWeightTotal ≤ 42) : ScalarSource bank := by
  have bounds (e f : Fin 2 →₀ ℕ) (hf : f ∈ ((groupSeeds Q).coeff e).support) :
      e 1 ≤ 5 ∧ f 0 ≤ bank.first + 5 ∧ f 1 ≤ bank.second ∧ e 1 + (f 0 + f 1) ≤ 42 := by
    have he : joinExponents e f ∈ Q.support := by
      rw [MvPolynomial.mem_support_iff, ← grouped_coeff]
      exact MvPolynomial.mem_support_iff.mp hf
    have ⟨h0, h1, h2, h3⟩ := joinExponents_apply e f
    have hy' := (le_weightedTotalDegree scalarWeightY he).trans hy
    have hs' := (le_weightedTotalDegree scalarWeightYS he).trans hs
    have ht' := (le_weightedTotalDegree scalarWeightT he).trans ht
    have htot' := (le_weightedTotalDegree scalarWeightTotal he).trans htot
    simp [scalarWeightY, scalarWeightYS, scalarWeightT, scalarWeightTotal,
      Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ,
      h0, h1, h2, h3, smul_eq_mul] at hy' hs' ht' htot'
    omega
  refine ⟨groupSeeds Q, (map_ne_zero_iff (groupSeeds (F := K)).toRingHom
    (groupSeeds (F := K)).injective).mpr hn, ?_, ?_, ?_, ?_⟩
  · rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro e he
    obtain ⟨f, hf⟩ := support_nonempty.mpr (MvPolynomial.mem_support_iff.mp he)
    exact (bounds e f hf).1
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf => (bounds e f hf).2.1)
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf => (bounds e f hf).2.2.1)
  · intro e he
    have hcoeff := MvPolynomial.mem_support_iff.mp he
    obtain ⟨f, hf⟩ := support_nonempty.mpr hcoeff
    have he' := (bounds e f hf).2.2.2
    have hb : ((groupSeeds Q).coeff e).totalDegree ≤ 42 - e 1 := by
      apply Finset.sup_le
      intro g hg
      have hh := (bounds e g hg).2.2.2
      simp [Finsupp.sum_fintype, Fin.sum_univ_succ]
      omega
    omega
theorem toScalarSource_atDecoder {bank : Bank} (Q : MvPolynomial (Fin 4) K) (hn)
    (hy : Q.weightedTotalDegree scalarWeightY ≤ 5)
    (hs : Q.weightedTotalDegree scalarWeightYS ≤ bank.first + 5)
    (ht) (htot) (γ : K) (P : Polynomial K) :
    (toScalarSource Q hn hy hs ht htot).atDecoder γ P =
      aeval (scalarImages P γ (γ ^ p)) Q := group_eval Q P γ (γ ^ p)
end
end P1_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_3_2
noncomputable section
open P1 MvPolynomial
open P1_3 (cutDegree)
open K1_10_2 (Row toGeneric)
open K1_10_2_2 (dx dy flow numerator)
open scoped Polynomial
open private dx_degree dy_degree from ProximityPrize.SubmissionLower.Fast069
open private clearPower separant taylorNumerator received nodeCut toGeneric_degree
  order_le_clearPower received_degree from ProximityPrize.SubmissionLower.Fast069
theorem separant_degree {g : Row} (h : g.totalDegree ≤ 42) : (dy g).totalDegree ≤ 41 := by
  have := dy_degree g
  omega
theorem flow_degree {g f : Row} {d : ℕ}
    (hg : g.totalDegree ≤ 42) (hf : f.totalDegree ≤ d) (hd : 0 < d) :
    (flow g f).totalDegree ≤ d + 41 := by
  have ha := separant_degree hg
  have hx := dx_degree g
  have hfx := dx_degree f
  have hfy := dy_degree f
  unfold flow
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    omega
  · apply (totalDegree_mul _ _).trans
    omega
private theorem numerator_degree {g : Row} (hg : g.totalDegree ≤ 42) (n : ℕ) :
    (numerator g n).totalDegree ≤ (2*n+1)*41+1 := by
  induction n with
  | zero =>
    simpa [numerator, totalDegree_neg] using (dx_degree g).trans hg
  | succ n ih =>
    have ha := separant_degree hg
    have hf := flow_degree hg ih (by omega)
    have hfa := flow_degree hg ha (by decide)
    rw [numerator]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      omega
    · apply (totalDegree_mul _ _).trans
      have hc := totalDegree_mul
        (MvPolynomial.C ((2*n+1 : ℕ) : K[X]) : Row) (flow g (dy g))
      rw [totalDegree_C, zero_add] at hc
      omega
theorem sep_pow_degree (g : Row) (hg : g.totalDegree ≤ 42) (a : ℕ) :
    (separant g ^ a).totalDegree ≤ a * 41 :=
  (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left a ((toGeneric_degree _).trans (separant_degree hg)))
theorem taylorNumerator_degree (g : Row) (hg : g.totalDegree ≤ 42) (x : K) :
    (taylorNumerator g x).totalDegree ≤ cutDegree := by
  unfold taylorNumerator
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    exact Nat.add_le_add_right (sep_pow_degree g hg clearPower) 1
  · apply totalDegree_finsetSum_le
    intro n hn
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, add_zero]
    apply (totalDegree_mul _ _).trans
    have h1 := sep_pow_degree g hg (clearPower - (2*n+1))
    have h2 := (toGeneric_degree (numerator g n)).trans (numerator_degree hg n)
    have h3 := Nat.sub_add_cancel (order_le_clearPower hn)
    change _ ≤ clearPower * 41 + 1
    omega
theorem nodeCut_degree (u : Words) (g : Row) (hg : g.totalDegree ≤ 42) (i : I) :
    (nodeCut u g i).totalDegree ≤ cutDegree := by
  unfold nodeCut
  apply (totalDegree_sub _ _).trans
  refine max_le (taylorNumerator_degree g hg _) ((totalDegree_mul _ _).trans ?_)
  exact Nat.add_le_add (sep_pow_degree g hg clearPower) (received_degree u i)
end
end P1_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace P1_3_2
noncomputable section
open P1 MvPolynomial
open P1_3 (ScalarSource incidenceRatio)
open K1_10_2 (Row RegularRoot derivativeOrder toGeneric atTrajectory point)
open scoped Polynomial
open private seedRow seedRow_degree regroup specialize specialize_regroup decoderView
  decoderView_injective decoderView_degree eval_decoderView exists_simple_derivative
  eval_specialize specialize_iterate specialize_pderiv from ProximityPrize.SubmissionLower.Fast069
open private nodeCut eval_nodeCut from ProximityPrize.SubmissionLower.Fast069
open private derivativeOrder_degree K1_10_2.eval_toGeneric from ProximityPrize.SubmissionLower.Fast069
theorem regroup_degree {bank : P1_3.Bank} (A : ScalarSource bank) : (regroup A.poly).totalDegree ≤ 42 := by
  classical
  have hsum : regroup A.poly =
      ∑ e ∈ A.poly.support, regroup (monomial e (A.poly.coeff e)) := by
    conv_lhs => rw [A.poly.as_sum]
    rw [map_sum]
  rw [hsum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [regroup, eval₂Hom_monomial, Finsupp.prod_pow, Fin.prod_univ_two]
  change (seedRow (A.poly.coeff e) *
    ((C (Polynomial.X : K[X]) : Row) ^ e 0 * (MvPolynomial.X (0 : Fin 3) : Row) ^ e 1)).totalDegree ≤ 42
  have hx : ((C (Polynomial.X : K[X]) : Row) ^ e 0).totalDegree = 0 := by
    rw [← map_pow, totalDegree_C]
  calc
    _ ≤ (seedRow (A.poly.coeff e)).totalDegree +
        (((C (Polynomial.X : K[X]) : Row) ^ e 0) * (MvPolynomial.X (0 : Fin 3) : Row) ^ e 1).totalDegree :=
      totalDegree_mul _ _
    _ ≤ (A.poly.coeff e).totalDegree + e 1 := by
      apply Nat.add_le_add (seedRow_degree _)
      exact (totalDegree_mul _ _).trans (by rw [hx, zero_add, totalDegree_X_pow])
    _ ≤ 42 := by simpa only [Nat.add_comm] using A.total e he
private theorem assign_charts {bank : P1_3.Bank} (A : ScalarSource bank) (Γ : Finset K)
    (P : ∀ γ ∈ Γ, K[X])
    (hF : ∀ γ (hγ : γ ∈ Γ), A.atLabel γ ≠ 0 ∧ A.atDecoder γ (P γ hγ) = 0) :
    ∃ g : Row, g.totalDegree ≤ 42 ∧
      ∀ γ (hγ : γ ∈ Γ), ∃ j : Fin 5, RegularRoot (derivativeOrder g j) γ (P γ hγ) := by
  let g := regroup A.poly
  refine ⟨g, regroup_degree A, ?_⟩
  intro γ hγ
  let Q := P γ hγ
  let specializeLabel := specialize (Polynomial.C γ) (Polynomial.C (γ ^ p))
  have hview : specializeLabel g = decoderView (A.atLabel γ) :=
    specialize_regroup A.poly γ (γ ^ p)
  have hne : specializeLabel g ≠ 0 := by
    rw [hview]
    intro hz
    exact (hF γ hγ).1 (decoderView_injective (hz.trans (map_zero _).symm))
  have hdegree : (specializeLabel g).natDegree ≤ 5 := by
    rw [hview]
    apply (decoderView_degree _).trans
    rw [degreeOf_eq_sup, Finset.sup_le_iff]
    intro e he
    exact (le_degreeOf_of_mem_support 1 (support_map_subset _ _ he)).trans A.y_degree
  have hroot : (specializeLabel g).IsRoot Q := by
    change (specializeLabel g).eval Q = 0
    rw [hview, eval_decoderView]
    exact (hF γ hγ).2
  obtain ⟨j, hj, hz, hsep⟩ :=
    exists_simple_derivative p 5 _ hne hdegree (by decide) Q hroot
  refine ⟨⟨j, hj⟩, ?_, ?_⟩
  · change MvPolynomial.eval ![Q, Polynomial.C γ, Polynomial.C (γ ^ p)]
      (derivativeOrder g ⟨j, hj⟩) = 0
    rw [← eval_specialize, derivativeOrder, specialize_iterate]
    exact hz
  · change MvPolynomial.eval ![Q, Polynomial.C γ, Polynomial.C (γ ^ p)]
      (pderiv 0 (derivativeOrder g ⟨j, hj⟩)) ≠ 0
    rw [← eval_specialize, specialize_pderiv, derivativeOrder, specialize_iterate]
    exact hsep
end
end P1_3_2
end
