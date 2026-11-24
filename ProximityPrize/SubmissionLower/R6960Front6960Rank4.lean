import ProximityPrize.SubmissionLower.HighCore82258Pairs
import ProximityPrize.SubmissionLower.R6960Front6960Rank2

-- merged module R6960Front6960Charts
section Merged_R6960Front6960Charts

set_option Elab.async false
set_option autoImplicit false

namespace Front6960_4
noncomputable section
open Front6960 MvPolynomial
open P2_4 (Bank Puncture nodeCut)
open K1_11 (scalarWeightY scalarWeightYS scalarWeightT scalarWeightTotal scalarImages)

structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted
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
end Front6960_4
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Front6960_4
noncomputable section
open Front6960 MvPolynomial
open P2_4 (Bank Puncture nodeCut)
open K1_11 (scalarWeightTotal)
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
end Front6960_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Front6960_4
noncomputable section
open Front6960 MvPolynomial
open P2_4 (Bank Puncture nodeCut)
open K1_11 (scalarWeightTotal)
open scoped BigOperators
open K1_11 (indexedSupport mem_indexedSupport indexedSupport_card nodes_injective)
open K1_11 (ncard_inter_filter surface_count_with_terminal)
open K1_11 (seed_eq_of_mismatch)
variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree < (131072 : ℕ) from M.degree)

theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    K1_11.correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [FrobeniusLocator.Strata.eval_coefficient_map twist M.decoder _
    (FrobeniusLocator.Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, P0.twist, frobenius_def]

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
end Front6960_4
end

end Merged_R6960Front6960Charts

-- merged module R6960Front6960Rank4
section Merged_R6960Front6960Rank4
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace Front6960_4
noncomputable section
open Front6960 MvPolynomial
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
abbrev weightedCutoff : ℕ := 4 * agreement - 1
def originalFloor : P2_4.Bank → ℕ
  | .w22 | .w22Swapped | .w12 | .w21 => 24373
  | _ => 32498
end
end Front6960_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace Front6960_4
noncomputable section
open Front6960 MvPolynomial
open P2_4 (Bank Puncture ContactInput)
open K1_11 (sourceWeights sourceBounds filtered mem_filtered)
open K1_11_2 (OmitsMessages sWeight tWeight graph PlaneOutput equation equation_degrees
  nodeWordMap decoder_bounds decoderNumerator decoderDenominator decoderDenominator_ne equation_linear
  equation_primitive linear_relation_contact_order_one)
open K1_11_2_2 (interpolant parameterNode nodeValue parameterNode_interpolant
  parameterNode_nodeValue degreeOf_interpolant_le degreeOf_nodeValue_le seedEval
  seedEval_nodeValue eval_graph nodeWord_combination nodeWord_omits)
open K1_11_2_1 (degreeOf_le_of_dvd)
open K1_11_2 (no_pair_one_one_of_graph native_column_rank)
open K1_8 (transfer_at)
private theorem reduced_bounds {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A) :
    WedgeBounds T.height B.U B.V := by
  have loc_ne : liftX (FrobeniusLocator.locator node (fixedNodes R)) ≠ 0 :=
    fun hz => (FrobeniusLocator.locator_monic node (fixedNodes R)).ne_zero
      ((Polynomial.map_injective _ Polynomial.C_injective) (hz.trans (Polynomial.map_zero _).symm))
  have hU : A.U ≠ 0 := by
    intro h
    have hg := A.graphU
    rw [h, map_zero, D.U_factor] at hg
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr A.content_ne) (mul_ne_zero loc_ne D.U_ne) hg.symm
  have hV : A.V ≠ 0 := by
    intro h
    have hg := A.graphV
    rw [h, map_zero, D.V_factor] at hg
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr A.content_ne) (mul_ne_zero loc_ne D.V_ne) hg.symm
  exact ⟨(Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hU B.U_dvd 3)).trans A.bounds.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hU B.U_dvd 4)).trans A.bounds.2.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hV B.V_dvd 3)).trans A.bounds.2.2.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hV B.V_dvd 4)).trans A.bounds.2.2.2⟩
private theorem degree_lt_of_product (s d m b : ℕ) (hd : s * d ≤ b) (hm : b < s * m) :
    d < m := by
  by_contra! h
  exact (not_lt_of_ge ((Nat.mul_le_mul_left s h).trans hd)) hm
private theorem reduced_boxes {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hH : T.height ≤ heightCap) :
    B.U.degreeOf 3 ≤ 2 ∧ B.U.degreeOf 4 ≤ 3 ∧
      B.V.degreeOf 3 ≤ 3 ∧ B.V.degreeOf 4 ≤ 2 := by
  obtain ⟨hUS, hUT, hVS, hVT⟩ := reduced_bounds B
  have hh : T.height ≤ 33579 := hH
  exact ⟨Nat.le_of_lt_succ (degree_lt_of_product _ _ 3 _ hUS (by change _ < (48746 - _) * 3; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 4 _ hUT (by change 48746 < (48746 - _) * 4; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 4 _ hVS (by change 48746 < (48746 - _) * 4; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 3 _ hVT (by change _ < (48746 - _) * 3; omega))⟩
private theorem no_pair_one_one {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hs : sWeight B.U B.V = 1) (ht : tWeight B.U B.V = 1) :
    False := by
  let f : Polynomial K →ₐ[K] Frac := IsScalarTower.toAlgHom K (Polynomial K) Frac
  have hf : Function.Injective f := IsFractionRing.injective (Polynomial K) Frac
  have hold : K1.columnRank D.U D.V = 4 := (P0_4.columnRank_eq D.U D.V).symm.trans hr
  have hr' : K1_8.columnRankAt K1.p D.U D.V = 4 := hold
  rw [native_column_rank] at hr'
  exact no_pair_one_one_of_graph p f hf A.content B.U B.V D.U D.V A.content_ne D.U_ne
    B.U_omits B.V_omits B.graphU B.graphV hr' hs ht
private theorem actual_bank {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hH : T.height ≤ heightCap) :
    ∃ bank : Bank, sWeight B.U B.V = bank.dS ∧ tWeight B.U B.V = bank.dT ∧
      originalFloor bank ≤ T.height := by
  obtain ⟨pUS, pUT, pVS, pVT⟩ := reduced_bounds B
  obtain ⟨bUS, bUT, bVS, bVT⟩ := reduced_boxes B hH
  have hlo : 24373 ≤ T.height := by
    by_contra! h
    have hs₁ : B.U.degreeOf 3 < 1 :=
      degree_lt_of_product _ _ 1 _ pUS (by change _ < (48746 - _) * 1; omega)
    have hs₂ : B.V.degreeOf 3 < 2 :=
      degree_lt_of_product _ _ 2 _ pVS (by change 48746 < (48746 - _) * 2; omega)
    have ht₁ : B.U.degreeOf 4 < 2 :=
      degree_lt_of_product _ _ 2 _ pUT (by change 48746 < (48746 - _) * 2; omega)
    have ht₂ : B.V.degreeOf 4 < 1 :=
      degree_lt_of_product _ _ 1 _ pVT (by change _ < (48746 - _) * 1; omega)
    exact no_pair_one_one B hr (by unfold sWeight; omega) (by unfold tWeight; omega)
  have hhi (hw : sWeight B.U B.V = 3 ∨ tWeight B.U B.V = 3) : 32498 ≤ T.height := by
    by_contra! h
    have hs₁ : B.U.degreeOf 3 < 2 :=
      degree_lt_of_product _ _ 2 _ pUS (by change _ < (48746 - _) * 2; omega)
    have hs₂ : B.V.degreeOf 3 < 3 :=
      degree_lt_of_product _ _ 3 _ pVS (by change 48746 < (48746 - _) * 3; omega)
    have ht₁ : B.U.degreeOf 4 < 3 :=
      degree_lt_of_product _ _ 3 _ pUT (by change 48746 < (48746 - _) * 3; omega)
    have ht₂ : B.V.degreeOf 4 < 2 :=
      degree_lt_of_product _ _ 2 _ pVT (by change _ < (48746 - _) * 2; omega)
    unfold sWeight tWeight at hw
    omega
  have hs : sWeight B.U B.V = 1 ∨ sWeight B.U B.V = 2 ∨ sWeight B.U B.V = 3 := by
    unfold sWeight
    omega
  have ht : tWeight B.U B.V = 1 ∨ tWeight B.U B.V = 2 ∨ tWeight B.U B.V = 3 := by
    unfold tWeight
    omega
  rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht
  · exact (no_pair_one_one B hr hs ht).elim
  · exact ⟨.w12, hs, ht, hlo⟩
  · exact ⟨.w13, hs, ht, hhi (Or.inr ht)⟩
  · exact ⟨.w21, hs, ht, hlo⟩
  · exact ⟨.w22Swapped, hs, ht, hlo⟩
  · exact ⟨.w23, hs, ht, hhi (Or.inr ht)⟩
  · exact ⟨.w31, hs, ht, hhi (Or.inl hs)⟩
  · exact ⟨.w32, hs, ht, hhi (Or.inl hs)⟩
  · exact ⟨.w33, hs, ht, hhi (Or.inl hs)⟩
private theorem reduced_scaled_relation {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (e : Polynomial K) :
    K1_8.relationOnAt p u (fixedNodes R) (Polynomial.C e * D.U)
      (Polynomial.C e * D.V) (Polynomial.C e * D.output) := by
  let G := liftX (FrobeniusLocator.locator node (fixedNodes R))
  have hG : ∀ i ∉ fixedNodes R, G.eval (Polynomial.C (node i)) ≠ 0 := by
    intro i hi
    rw [show G = K1.liftX _ from rfl, K1_8.eval_liftX, Polynomial.C_ne_zero]
    exact fun hz => hi ((FrobeniusLocator.Principal.locator_eval_zero_iff node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  exact @transfer_at u p 131072 T.height R (fixedNodes R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e
private theorem nodeValue_of_relation (q : ℕ) {u : Words} {deleted : Finset I}
    {P : Puncture deleted} {U V : MvPolynomial (Fin 5) K} {G : Bivar}
    (hrel : K1_8.relationOnAt q u deleted (graph q U) (graph q V) G) (i : Fin P.N) :
    seedEval q (nodeValue (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
      (u 0 (P.index i) ^ q) (u 1 (P.index i) ^ q) U V) = G.eval (Polynomial.C (P.nodes i)) := by
  have hkeep : P.index i ∉ deleted := (P.retained _).mp ⟨i, rfl⟩
  rw [seedEval_nodeValue]
  exact hrel (P.index i) hkeep
private theorem plane_output {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hH : T.height ≤ heightCap) (P : Puncture (fixedNodes R)) :
    Nonempty (PlaneOutput u P D.height B.U B.V) := by
  let x : Fin P.N → K := P.nodes
  let a (i : Fin P.N) : K := u 0 (P.index i)
  let b (i : Fin P.N) : K := u 1 (P.index i)
  let v (i : Fin P.N) := nodeValue (x i) (a i) (b i) (a i ^ p) (b i ^ p) B.U B.V
  let W := interpolant x v
  have hx : Function.Injective x :=
    ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective
  have hnodes (i : Fin P.N) : parameterNode (x i) W = v i :=
    parameterNode_interpolant x hx v (fun _ => parameterNode_nodeValue ..) i
  have hdeg (j : Fin 5) : W.degreeOf j ≤
      (P.N - 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 5) K).degreeOf j +
      (if j = 3 then sWeight B.U B.V else if j = 4 then tWeight B.U B.V else 0) :=
    degreeOf_interpolant_le x hx v j _ (fun i => degreeOf_nodeValue_le j
      (x i) (a i) (b i) (a i ^ p) (b i ^ p) B.U B.V)
  have hm : OmitsMessages W := ⟨Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 1),
    Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 2)⟩
  have hs : W.degreeOf 3 ≤ sWeight B.U B.V := by simpa [degreeOf_X] using hdeg 3
  have ht : W.degreeOf 4 ≤ tWeight B.U B.V := by simpa [degreeOf_X] using hdeg 4
  have hbound : 131072 + D.height ≤ P.N := by
    have hh : T.height ≤ 33579 := hH
    have hD := D.height_eq
    have hP := P.size
    omega
  have hsmall : W.degreeOf 3 < p := by
    obtain ⟨huS, _, hvS, _⟩ := reduced_boxes B hH
    unfold sWeight at hs
    change W.degreeOf 3 < 2130706433
    omega
  have hdegree := K1_11_2_1.graph_natDegree p (by decide) W hm hsmall
  have hWdeg : (graph p W).natDegree < P.N := by
    rw [hdegree]
    have hh : W.degreeOf 0 ≤ P.N - 1 := by simpa [degreeOf_X] using hdeg 0
    omega
  let G := Polynomial.C A.content * D.output
  have hDdeg : D.output.natDegree ≤ 131071 + D.height := by
    by_cases hz : D.output = 0
    · simp [hz]
    have hd := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr D.output_degree
    change D.output.natDegree < 131072 + D.height at hd
    omega
  have hGdeg : G.natDegree ≤ 131071 + D.height :=
    (Polynomial.natDegree_C_mul_le A.content D.output).trans hDdeg
  have hrel : K1_8.relationOnAt p u (fixedNodes R) (graph p B.U) (graph p B.V) G := by
    rw [B.graphU, B.graphV]
    exact reduced_scaled_relation D A.content
  have heval (i : Fin P.N) : (graph p W).eval (Polynomial.C (x i)) = G.eval (Polynomial.C (x i)) := by
    rw [eval_graph, hnodes]
    exact nodeValue_of_relation p (P := P) hrel i
  have hgraph : graph p W = G := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Polynomial.C_injective.comp hx) heval
    rw [Fintype.card_fin]
    exact max_lt hWdeg (by omega)
  have hheight : W.degreeOf 0 ≤ 131071 + D.height := by
    rw [← hdegree, hgraph]
    exact hGdeg
  refine ⟨⟨W, hm, hheight, hs, ht, ?_⟩⟩
  intro i
  change nodeWordMap (x i) (a i) (b i) (a i ^ p) (b i ^ p) (B.U * MvPolynomial.X 1 + B.V * MvPolynomial.X 2 - W) = 0
  rw [map_sub, nodeWord_combination _ _ _ _ _ _ _ B.U_omits B.V_omits,
    nodeWord_omits _ _ _ _ _ W hm, hnodes]
  exact sub_self _
theorem contact_input {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hH : T.height ≤ heightCap) (P : Puncture (fixedNodes R)) :
    ∃ b : Bank, originalFloor b ≤ T.height ∧ Nonempty (ContactInput u P b D.height) := by
  obtain ⟨W⟩ := plane_output B hH P
  obtain ⟨bank, hs, ht, hfloor⟩ := actual_bank B hr hH
  let L := equation B.U B.V W.W
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) =
      sourceBounds (131071 + D.height) 1 bank.dS bank.dT j := by
    simpa only [L, equation, hs, ht] using equation_degrees 131071 D.height B.U B.V W.W
      B.U_ne B.V_ne B.U_omits B.V_omits W.omits B.height W.height W.degreeS W.degreeT
  have hL : L ≠ 0 := by
    intro hz
    have he := hdeg 1
    simp [hz, sourceBounds, weightedTotalDegree] at he
  have hf : L ∈ filtered (sourceWeights 131071)
      (sourceBounds (131071 + D.height) 1 bank.dS bank.dT) :=
    (mem_filtered _ _ _).mpr fun j => (hdeg j).le
  obtain ⟨hy, hdy, hns, hds, hnt, hdt⟩ := decoder_bounds 131071 D.height bank.dS bank.dT
    B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne hf
  refine ⟨bank, hfloor, ⟨{
    L := L
    L_ne := hL
    degrees := hdeg
    order_one := ?_
    numerator := decoderNumerator B.U W.W
    denominator := decoderDenominator B.V
    denominator_ne := decoderDenominator_ne B.V B.V_omits B.V_ne
    linear := equation_linear B.U B.V W.W B.U_omits B.V_omits W.omits
    primitive := equation_primitive B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne B.relPrime
    numerator_Y := hy
    denominator_Y := hdy
    numerator_S := hns
    denominator_S := hds
    numerator_T := hnt
    denominator_T := hdt
  }⟩⟩
  intro i
  exact linear_relation_contact_order_one _ _ _ _ _ B.U B.V W.W B.relPrime
    B.U_omits B.V_omits W.omits (W.node i)
end
end Front6960_4
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace Front6960_4
open Front6960 Finset
open P2_4 (Bank)
open K1_11 (V J)
open P0_7 (countRow gradeRow count grade contactRow V_affine rational_fee)
open P1_4 (dims_5_16_10 dims_4_15_8 jets_4_16_10 jets_3_15_8 dims_5_8_7 dims_4_7_4 jets_4_8_7 jets_3_7_4 dims_5_10_16 dims_4_8_15 jets_4_10_16 jets_3_8_15 dims_5_11_10 dims_4_9_8 jets_4_11_10 jets_3_9_8 dims_5_8_6 dims_4_6_3 jets_4_8_6 jets_3_6_3 dims_5_7_8 dims_4_4_7 jets_4_7_8 jets_3_4_7 dims_5_6_8 dims_4_3_6 jets_4_6_8 jets_3_3_6 dims_4_3_5 jets_3_3_5)
open P2_4 (dims_5_10_11 jets_4_10_11 dims_4_8_9 jets_3_8_9 dims_4_5_3 jets_3_5_3)
private theorem surplus_of_stats (h H e N lo s t ds dt c g c' g' j : ℕ)
    (hlo : lo ≤ h) (hmax : h ≤ 33579) (hH : H + e = h) (hN : N + e = 262144)
    (hc : count 5 s t = c) (hg : grade 5 s t = g)
    (hc' : count 4 (s-ds) (t-dt) = c') (hg' : grade 4 (s-ds) (t-dt) = g')
    (hj : J 4 s t - J 3 (s-ds) (t-dt) = j) (hgain : c' ≤ j)
    (hmargin : 262144 * j + (588201 - lo) * c' + 131071 * g <
      719272 * c + 131071 * g') :
    N * (J 4 s t - J 3 (s-ds) (t-dt)) + V (719271 - 131071 - H) 131071 4 (s-ds) (t-dt)
      < V 719271 131071 5 s t := by
  have hv := V_affine 719271 131071 5 s t (by decide)
  have hv' := V_affine (719271 - 131071 - H) 131071 4 (s-ds) (t-dt) (by omega)
  rw [hc, hg] at hv
  rw [hc', hg'] at hv'
  have hw : 719271 - 131071 - H + 1 ≤ (588201 - lo) + e := by omega
  have hm : N * j + (719271 - 131071 - H + 1) * c' ≤
      262144 * j + (588201 - lo) * c' := by
    calc
      _ ≤ N * j + ((588201 - lo) + e) * c' :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hw) _
      _ = N * j + e * c' + (588201 - lo) * c' := by ring
      _ ≤ N * j + e * j + (588201 - lo) * c' :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hgain) _) _
      _ = _ := by rw [← Nat.add_mul, hN]
  rw [hj]
  omega
theorem bank_surplus (b : Bank) (h H e N : ℕ) (hlo : originalFloor b ≤ h)
    (hmax : h ≤ heightCap) (hH : H + e = h) (hN : N + e = blockLength) :
    N * (J 4 b.s b.t - J 3 (b.s - b.dS) (b.t - b.dT)) +
      V (weightedCutoff - 131071 - H) 131071 4 (b.s - b.dS) (b.t - b.dT) <
      V weightedCutoff 131071 5 b.s b.t := by
  cases b with
  | w12 =>
    exact surplus_of_stats h H e N 24373 16 10 1 2 2982 9324 1675 4189 2010
      hlo hmax hH hN dims_5_16_10.1 dims_5_16_10.2 dims_4_15_8.1 dims_4_15_8.2
      (by rw [jets_4_16_10, jets_3_15_8]) (by decide) (by decide)
  | w13 =>
    exact surplus_of_stats h H e N 32498 8 7 1 3 952 2814 355 809 855
      hlo hmax hH hN dims_5_8_7.1 dims_5_8_7.2 dims_4_7_4.1 dims_4_7_4.2
      (by rw [jets_4_8_7, jets_3_7_4]) (by decide) (by decide)
  | w21 =>
    exact surplus_of_stats h H e N 24373 10 16 2 1 2982 9324 1675 4189 2010
      hlo hmax hH hN dims_5_10_16.1 dims_5_10_16.2 dims_4_8_15.1 dims_4_8_15.2
      (by rw [jets_4_10_16, jets_3_8_15]) (by decide) (by decide)
  | w22 =>
    exact surplus_of_stats h H e N 24373 11 10 2 2 2002 6174 985 2419 1495
      hlo hmax hH hN dims_5_11_10.1 dims_5_11_10.2 dims_4_9_8.1 dims_4_9_8.2
      (by rw [jets_4_11_10, jets_3_9_8]) (by decide) (by decide)
  | w22Swapped =>
    exact surplus_of_stats h H e N 24373 10 11 2 2 2002 6174 985 2419 1495
      hlo hmax hH hN dims_5_10_11.1 dims_5_10_11.2 dims_4_8_9.1 dims_4_8_9.2
      (by rw [jets_4_10_11, jets_3_8_9]) (by decide) (by decide)
  | w23 =>
    exact surplus_of_stats h H e N 32498 8 6 2 3 798 2324 215 459 800
      hlo hmax hH hN dims_5_8_6.1 dims_5_8_6.2 dims_4_6_3.1 dims_4_6_3.2
      (by rw [jets_4_8_6, jets_3_6_3]) (by decide) (by decide)
  | w31 =>
    exact surplus_of_stats h H e N 32498 7 8 3 1 952 2814 355 809 855
      hlo hmax hH hN dims_5_7_8.1 dims_5_7_8.2 dims_4_4_7.1 dims_4_4_7.2
      (by rw [jets_4_7_8, jets_3_4_7]) (by decide) (by decide)
  | w32 =>
    exact surplus_of_stats h H e N 32498 6 8 3 2 798 2324 215 459 800
      hlo hmax hH hN dims_5_6_8.1 dims_5_6_8.2 dims_4_3_6.1 dims_4_3_6.2
      (by rw [jets_4_6_8, jets_3_3_6]) (by decide) (by decide)
  | w33 =>
    exact surplus_of_stats h H e N 32498 6 8 3 3 798 2324 175 364 835
      hlo hmax hH hN dims_5_6_8.1 dims_5_6_8.2 dims_4_3_5.1 dims_4_3_5.2
      (by rw [jets_4_6_8, jets_3_3_5]) (by decide) (by decide)
  | w33Swapped =>
    exact surplus_of_stats h H e N 32498 8 6 3 3 798 2324 175 364 835
      hlo hmax hH hN dims_5_8_6.1 dims_5_8_6.2 dims_4_5_3.1 dims_4_5_3.2
      (by rw [jets_4_8_6, jets_3_5_3]) (by decide) (by decide)
def chartRate (b : Bank) : ℚ := (131073 / 48747 : ℚ) * b.M
def chartFee (b : Bank) : ℚ := b.E * chartRate b ^ 2
abbrev tariff : ℕ := 250000000000000000
private theorem priced (E M zeroFee cap : ℕ)
    (h : zeroFee * 48747^2 + 5 * E * (131073*M)^2 ≤ cap * 48747^2)
    (hc : cap ≤ tariff) :
    (zeroFee : ℚ) + 5 * ((E : ℚ) * ((131073 / 48747 : ℚ) * M)^2) ≤ tariff :=
  (rational_fee E M zeroFee cap 131073 48747 (by decide) h).trans (by exact_mod_cast hc)
local notation "fee!" e "," m "," z "," c => priced e m z c (by decide) (by decide)
theorem bank_fee (b : Bank) : (b.zeroFee : ℚ) + 5 * chartFee b ≤ tariff := by
  cases b with
  | w12 => exact fee! 36, 9174936, 0x771000024, 250000000000000000
  | w21 => exact fee! 36, 9174936, 0x7f0000024, 250000000000000000
  | w22Swapped => exact fee! 36, 9174936, 0x7f0000024, 250000000000000000
  | w13 => exact fee! 30, 7602090, 0x86f00001e, 250000000000000000
  | w31 => exact fee! 30, 7602090, 0x3f800001e, 250000000000000000
  | w23 => exact fee! 34, 8650654, 0x7f0000022, 250000000000000000
  | w32 => exact fee! 34, 8650654, 0x673000022, 250000000000000000
  | w33 => exact fee! 39, 9961359, 0x8ee000027, 250000000000000000
  | w22 => exact fee! 36, 9174936, 0x771000024, 250000000000000000
  | w33Swapped => exact fee! 39, 9961359, 0x7f0000027, 250000000000000000
theorem bank_rate_ge (b : Bank) : (262144 : ℚ) ≤ chartRate b := by
  have hm : (262144 : ℕ) ≤ b.M := by cases b <;> decide
  have hr : (1 : ℚ) ≤ 131073 / 48747 := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 48747)).mpr
    rw [one_mul]
    exact_mod_cast (show (48747 : ℕ) ≤ 131073 by decide)
  exact (by exact_mod_cast hm : (262144 : ℚ) ≤ b.M).trans
    (by simpa only [one_mul, chartRate] using
      mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℚ) ≤ b.M))
end Front6960_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
namespace Front6960_4
noncomputable section
open MvPolynomial
open Front6960 (heightCap)
open P2_4 (Bank ContactData Multipliers)
open K1_11 (V J filtered filteredMul filteredMul_injective mem_filteredMul_range_iff
  sourceWeights sourceBounds source_filtered_finrank sourceToJet contactWeight)
open K1_11 (exists_kernel_outside)
open P2_4 (LocalSpace localMultiply local_finrank)
abbrev Source (F : Type*) [Field F] (b : Bank) :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds weightedCutoff 5 b.s b.t)
variable {F : Type*} [Field F]
  {N : ℕ} {L : MvPolynomial (Fin 5) F} {b : Bank} {H : ℕ} (D : ContactData N L b)
private def nodeMap (i : Fin N) : Source F b →ₗ[F] LocalSpace D i :=
  (LinearMap.range (localMultiply D i)).mkQ.comp
    (sourceToJet weightedCutoff 131071 5 b.s b.t 3 (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i))
private theorem localContact (Q : Source F b) (i : Fin N) (hi : nodeMap D i Q = 0) :
    ∃ R : Multipliers F b, D.shifted i Q.val - D.shifted i L * R.val ∈
      restrictWeightedOrder contactWeight 4 := by
  have hmem : sourceToJet weightedCutoff 131071 5 b.s b.t 3 (D.x i)
      (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q ∈
      LinearMap.range (localMultiply D i) :=
    (Submodule.Quotient.mk_eq_zero _).mp hi
  obtain ⟨R, hR⟩ := hmem
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm
theorem exists_quotient_source (h e : ℕ) (hmin : originalFloor b ≤ h) (hmax : h ≤ heightCap)
    (hH : H + e = h) (hN : N + e = 262144)
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j) :
    ∃ Q : Source F b, ¬ L ∣ Q.val ∧ ∀ i, ∃ R : Multipliers F b,
      D.shifted i Q.val - D.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hupper : H ≤ 33579 := by
    have hh : h ≤ 33579 := hmax
    omega
  have hD : weightedCutoff = 719271 := rfl
  have hfit : ∀ i, b.relationBounds H i ≤ sourceBounds weightedCutoff 5 b.s b.t i := by
    intro i
    cases b <;> fin_cases i <;>
      simp [Bank.relationBounds, Bank.s, Bank.t, Bank.dS, Bank.dT, sourceBounds, hD] <;> omega
  have hshift : (fun i => sourceBounds weightedCutoff 5 b.s b.t i - b.relationBounds H i) =
      sourceBounds (weightedCutoff - 131071 - H) 4 (b.s-b.dS) (b.t-b.dT) := by
    funext i
    fin_cases i <;> simp [sourceBounds, Bank.relationBounds, hD]
    omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds weightedCutoff 5 b.s b.t)
    (b.relationBounds H) L D.nonzero hdeg hfit
  have hdimMult : Module.finrank F (LinearMap.range mult) =
      V (weightedCutoff - 131071 - H) 131071 4 (b.s-b.dS) (b.t-b.dT) := by
    rw [LinearMap.finrank_range_of_inj
      (filteredMul_injective _ _ _ L D.nonzero hdeg hfit), hshift, source_filtered_finrank]
  have hdimLocal : Module.finrank F (∀ i : Fin N, LocalSpace D i) =
      N * (J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT)) := by
    let (i : Fin N) : Module.Free F (LocalSpace D i) := Module.Free.of_divisionRing F _
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank D, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace D i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F b) := by
    rw [hdimLocal, hdimMult, source_filtered_finrank]
    exact bank_surplus b h H e N hmin hmax hH hN
  let : Module F (∀ i : Fin N, LocalSpace D i) := Pi.module _ _ _
  have hk := exists_kernel_outside (G := ∀ i : Fin N, LocalSpace D i)
    (LinearMap.pi (nodeMap D)) (LinearMap.range mult) hdim
  obtain ⟨Q, hQ, hnot⟩ := hk
  exact ⟨Q, (mem_filteredMul_range_iff _ _ _ L D.nonzero hdeg hfit Q).not.mp hnot,
    fun i => localContact D Q i (congrFun hQ i)⟩
end
end Front6960_4
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Front6960_4
noncomputable section
open Front6960 FrobeniusLocator MvPolynomial
open P2_4 (Bank Puncture ContactInput)
open K1_11 (contactWeight contactDecoderImages decoder_contact_composition contactDecoderImages_vanish
  decoder_eval_degree eq_zero_of_many_contacts decoder_contact_multiplicity decoderImages
  sourceWeights mem_filtered correctOn nodes_injective indexedSupport indexedSupport_card
  scalarWeightY scalarWeightYS scalarWeightT scalarEliminant
  scalarEliminant_ne_zero polynomialView_source_coefficients clearedEval_weight_bound
  polynomialView scalarEliminant_annihilates)
open K1_11 (scalar_total_weight_le)
open P2_4 (asContactData bank_cancel contact_order_one_mem)
variable {u : Words} {deleted : Finset I} {P : Puncture deleted} {b : Bank} {H : ℕ}
    (D : ContactInput u P b H)
private theorem relation_on_support (hH : H ≤ 33579) (Q Q' : Polynomial K)
    (hQ : Q.natDegree ≤ 131071) (hQ' : Q'.natDegree ≤ 131071)
    (s t : K) (S : Finset (Fin P.N)) (hS : agreement ≤ S.card) (hc : correctOn u P Q Q' s t S) :
    aeval (decoderImages Q Q' s t) D.L = 0 := by
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 1
  · intro i hi
    have ho := contact_order_one_mem contactWeight (D.shifted i D.L) (D.order_one i)
    have hd := pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder Polynomial.C ho
      (contactDecoderImages_vanish _ _ _ _ _ s t Q Q' (hc i hi).1 (hc i hi).2)
    change (Polynomial.X-Polynomial.C (P.nodes i))^1 ∣
      aeval (contactDecoderImages (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i)^p) (u 1 (P.index i)^p) s t Q Q') (D.shifted i D.L) at hd
    rwa [ContactInput.shifted, decoder_contact_composition] at hd
  · have hdeg : D.L.weightedTotalDegree (sourceWeights 131071 0) ≤ 131071+H :=
      le_of_eq (D.degrees 0)
    have hd := decoder_eval_degree 131071 (131071+H) D.L hdeg Q Q' hQ hQ' s t
    change 179818 ≤ S.card at hS
    omega
theorem exists_two_decoder_source (h : ℕ) (hmin : originalFloor b ≤ h) (hmax : h ≤ heightCap)
    (hH : H + deleted.card = h) :
    ∃ G : Source K b, ¬ D.L ∣ G.val ∧
      ∀ (Q Q' : Polynomial K), Q.natDegree ≤ 131071 → Q'.natDegree ≤ 131071 →
        ∀ (s t : K) (S : Finset (Fin P.N)), agreement ≤ S.card → correctOn u P Q Q' s t S →
          aeval (decoderImages Q Q' s t) G.val = 0 := by
  obtain ⟨G, hnot, hnode⟩ := exists_quotient_source (asContactData D) h deleted.card hmin hmax hH P.size D.degrees
  refine ⟨G, hnot, ?_⟩
  intro Q Q' hQ hQ' s t S hS hc
  have hmax' : h ≤ 33579 := hmax
  have hrel := relation_on_support D (by omega) Q Q' hQ hQ' s t S hS hc
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hnode i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ s t Q Q' G.val D.L R.val
      (hc i hi).1 (hc i hi).2 hrel hR
  · have hd := decoder_eval_degree 131071 weightedCutoff G.val
      ((mem_filtered _ _ _).mp G.property 0) Q Q' hQ hQ' s t
    change _ ≤ 719271 at hd
    change 179818 ≤ S.card at hS
    omega
def SupportAt {u : Words} {deleted : Finset I} {Γ : Finset K} (F : Marks u deleted Γ) : Prop :=
  ∀ γ (hγ : γ ∈ Γ), agreement ≤ (F.mark γ hγ).support.card
def selectMarks {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {Γ : Finset K} (hΓ : BadFamily u Γ) (hn : ∀ γ ∈ Γ, Normal u γ) :
    { F : Marks u (fixedNodes R) Γ // SupportAt F } := by
  let M := fun γ hγ => Classical.choice (Front6960.bad_mark u Γ hΓ γ hγ)
  refine ⟨{
    mark := M
    survives := fun γ hγ i hi hid => D.deleted_error γ (hn γ hγ) (M γ hγ) i hid
      ((M γ hγ).hits i hi)
  }, fun γ hγ => (M γ hγ).agreement⟩
theorem exists_annihilator {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {b : Bank} {H : ℕ} (C : ContactInput u P b H) (h : ℕ)
    (hmin : originalFloor b ≤ h) (hmax : h ≤ heightCap) (hH : H + deleted.card = h)
    {Γ : Finset K} (F : Marks u deleted Γ) (hF : SupportAt F) : Nonempty (Annihilator F b) := by
  obtain ⟨G, hG, hgAnn⟩ := exists_two_decoder_source C h hmin hmax hH
  let Q := scalarEliminant 5 G.val C.numerator C.denominator
  have hne : Q ≠ 0 := scalarEliminant_ne_zero weightedCutoff 131071 5 b.s b.t
    G.val C.L G.property hG C.numerator C.denominator C.denominator_ne C.linear C.primitive
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients weightedCutoff 131071 5 b.s b.t G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 := by
    simpa [Q, scalarEliminant] using
      clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val)
        C.numerator C.denominator (by simpa using hY) C.numerator_Y C.denominator_Y (by omega)
  have hs : Q.weightedTotalDegree scalarWeightYS ≤ b.a := by
    simpa [Q, scalarEliminant, Bank.a] using
      clearedEval_weight_bound scalarWeightYS 5 b.s 0 b.dS b.dS (polynomialView G.val)
        C.numerator C.denominator (by simpa using hS) C.numerator_S C.denominator_S (by omega)
  have ht : Q.weightedTotalDegree scalarWeightT ≤ b.b := by
    simpa [Q, scalarEliminant, Bank.b] using
      clearedEval_weight_bound scalarWeightT 5 b.t 1 b.dT (b.dT-1) (polynomialView G.val)
        C.numerator C.denominator (by simpa using hT) C.numerator_T C.denominator_T (bank_cancel b).ge
  refine ⟨⟨Q, hne, hy, hs, ht, scalar_total_weight_le Q b.a b.b hs ht, ?_⟩⟩
  intro γ hγ
  let M := F.mark γ hγ
  let S := indexedSupport P M.support
  have hS : agreement ≤ S.card := by
    rw [indexedSupport_card P M.support (F.survives γ hγ)]
    exact hF γ hγ
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 :=
    Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hmax' : h ≤ 33579 := hmax
  have hrel := relation_on_support C (by omega) _ _ hd hd' γ (γ ^ p) S hS hcorrect
  exact scalarEliminant_annihilates weightedCutoff 131071 5 b.s b.t G.val C.L G.property
    C.numerator C.denominator C.linear _ _ γ (γ^p) hrel
    (hgAnn _ _ hd hd' γ (γ^p) S hS hcorrect)
end
end Front6960_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Front6960_4
noncomputable section
open Front6960 MvPolynomial
open P2_4 (Bank Puncture nodeCut)
open scoped BigOperators
open K1_11 (indexedSupport mem_indexedSupport indexedSupport_card)
open K1_11 (ncard_inter_filter surface_count_with_terminal)
variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
private theorem chart_agreements (chart : TaylorChart u P F b Λ) (hF : SupportAt F) (γ : K) (hγ : γ ∈ Λ) :
    179818 ≤ {i | MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0}.ncard := by
  let M := F.mark γ (chart.subset hγ)
  have hsub : (indexedSupport P M.support : Set (Fin P.N)) ⊆
      {i | MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0} := by
    intro i hi
    exact (chart_cut_iff chart γ hγ i).mpr (M.hits _ ((mem_indexedSupport P M.support i).mp hi))
  have h := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, indexedSupport_card P M.support (F.survives γ (chart.subset hγ))] at h
  exact (hF γ (chart.subset hγ)).trans h
theorem chart_count {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
    (chart : TaylorChart u P F b Λ) (hF : SupportAt F) : (Λ.card : ℚ) ≤ chartFee b := by
  classical
  let S := Λ.image chart.point
  let R : ℚ := chartRate b
  have hRbig : (262144 : ℚ) ≤ R := bank_rate_ge b
  have hone : (1 : ℚ) ≤ 262144 := by
    exact_mod_cast (show (1 : ℕ) ≤ 262144 by decide)
  have hR : 1 ≤ R := hone.trans hRbig
  have hN : P.N ≤ 262144 := by have := P.size; omega
  have hinj : Set.InjOn chart.point (Λ : Set K) := by
    intro γ hγ δ hδ he
    apply (algebraMap K Frac).injective
    exact (chart.slope γ hγ).symm.trans ((congrFun he 1).trans (chart.slope δ hδ))
  have hcard : S.card = Λ.card := Finset.card_image_of_injOn hinj
  let cuts := nodeCut u P chart.numerator chart.denominator
  have hratio (m : ℕ) (hm : m < 131072) :
      (((Fintype.card (Fin P.N) - m) * b.M : ℕ) : ℚ) ≤ R * ((179818 - m : ℕ) : ℚ) := by
    have hnat : (P.N - m) * 48747 ≤ 131073 * (179818 - m) := by omega
    have hrat : ((P.N - m : ℕ) : ℚ) * 48747 ≤ 131073 * ((179818 - m : ℕ) : ℚ) := by
      exact_mod_cast hnat
    have hh : ((P.N - m : ℕ) : ℚ) ≤ (131073/48747 : ℚ) * ((179818 - m : ℕ) : ℚ) := by
      linarith
    rw [Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (b.M : ℚ))).trans_eq (by dsimp [R, chartRate]; ring)
  rw [← hcard]
  refine surface_count_with_terminal chart.equation chart.denominator chart.equation_ne cuts
    (L := 131072) (A := 179818) (by decide) chart.equation_degree chart.cut_degree hR hratio S
    (fun x hx => ?_) (fun x hx => ?_) (fun J hJ => ?_)
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨chart.on_equation γ hγ, chart.regular γ hγ⟩
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact chart_agreements chart hF γ hγ
  · let W := Λ.filter fun γ => chart.point γ ∈ zeroLocus Frac J
    have hW : W ⊆ Λ := Finset.filter_subset _ _
    have hWimage : W.image chart.point = S.filter (· ∈ zeroLocus Frac J) := by
      ext x
      simp only [W, S, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨γ, ⟨hγ, hJγ⟩, rfl⟩
        exact ⟨⟨γ, hγ, rfl⟩, hJγ⟩
      · rintro ⟨⟨γ, hγ, rfl⟩, hJγ⟩
        exact ⟨γ, ⟨hγ, hJγ⟩, rfl⟩
    have hbound := chart_persistent chart J W hW (fun γ hγ => (Finset.mem_filter.mp hγ).2) hJ
    rw [ncard_inter_filter, ← hWimage, Finset.card_image_of_injOn (hinj.mono hW)]
    exact (by exact_mod_cast hbound.trans hN : (W.card : ℚ) ≤ 262144).trans hRbig
end
end Front6960_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Front6960_4
open Front6960
open P2_4 (Bank)
def c1 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    Nonempty (IndependentLift R)
def c2 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    T.height ≤ heightCap → ∀ (A : IndependentLift R),
      Nonempty (ReducedPair D A)
private theorem card_from_cover (b : Bank) (Γ exceptional : Finset K)
    (charts : Fin 5 → Finset K) (hfee : exceptional.card ≤ b.zeroFee)
    (hcover : ∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j)
    (hcharts : ∀ j, ((charts j).card : ℚ) ≤ chartFee b) :
    Γ.card ≤ tariff := by
  classical
  have hsub : Γ ⊆ exceptional ∪ Finset.univ.biUnion charts := by
    intro γ hγ
    exact Finset.mem_union.mpr ((hcover γ hγ).imp id (fun ⟨j, hj⟩ =>
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩))
  have hcount := (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hbound : (Γ.card : ℚ) ≤ b.zeroFee + 5 * chartFee b := by
    calc
      (Γ.card : ℚ) ≤ (exceptional.card : ℚ) + ∑ j : Fin 5, ((charts j).card : ℚ) := by
        exact_mod_cast hcount
      _ ≤ (b.zeroFee : ℚ) + ∑ _j : Fin 5, chartFee b := by
        exact add_le_add (by exact_mod_cast hfee) (Finset.sum_le_sum fun j _ => hcharts j)
      _ = _ := by simp
  have hcap := hbound.trans (bank_fee b)
  exact_mod_cast hcap
theorem of_children (h1 : c1) (h2 : c2) : Front6960.c4 := by
  intro u hu T R D _ hr Γ hΓ hn
  classical
  have hmax := relation_height_le hu T
  obtain ⟨A⟩ := h1 u hu T R
  obtain ⟨B⟩ := h2 u T R D hmax A
  let P := K1_11.nativePuncture (fixedNodes R)
  let F := selectMarks D hΓ hn
  obtain ⟨b, hfloor, ⟨C⟩⟩ := contact_input B hr hmax P
  obtain ⟨Q⟩ := exists_annihilator C T.height hfloor hmax D.height_eq F.val F.property
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ := chart_cover P Q
  refine card_from_cover b Γ exceptional charts hfee hcover fun j => ?_
  rcases hcharts j with he | chart
  · simp only [he, Finset.card_empty, Nat.cast_zero]
    unfold chartFee
    positivity
  · exact chart_count (Classical.choice chart) F.property
end Front6960_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000
namespace Front6960_4_1
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark Front6960
open K1_11_1 (Seeds PlaneField planeSlice planeStack graph rank_graph mulVec_map)
open K1_11_1 (syndrome_degree graph_slice_map graph_stack_map certificate_kernel)
private theorem first_slice_nullity (u : Words) (T : TwoActive u) :
    GenericLayer.genericNullity
      (Strata.parameterRelation p node (u 0) (u 1) k T.height) = 1 :=
  Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
theorem plane_first_slice_nullity (u : Words) (T : TwoActive u)
    (hh : T.height ≤ heightCap) :
    Module.finrank (PlaneField K) (LinearMap.ker
      ((planeSlice p node (u 0) (u 1) k T.height).map
        (algebraMap (Seeds K) (PlaneField K))).mulVecLin) = 1 := by
  let A := planeSlice p node (u 0) (u 1) k T.height
  have hdeg (j : Fin (k - T.height)) (b : Fin 2 × Fin (T.height + 1)) :
      (A j b).degreeOf 0 ≤ if b.1 = 0 then 1 else 0 :=
    syndrome_degree p node (u 0) (u 1) b.1 0 _
  have hsize : T.height + 1 < p :=
    (Nat.add_le_add_right hh 1).trans_lt (by decide)
  have he := rank_graph p (by decide) hsize A hdeg
  change (A.map (algebraMap (Seeds K) (PlaneField K))).rank =
    ((planeSlice p node (u 0) (u 1) k T.height).map _).rank at he
  rw [graph_slice_map] at he
  have hn := GenericLayer.rank_add_nullity
    (Strata.parameterRelation p node (u 0) (u 1) k T.height)
  rw [first_slice_nullity u T] at hn
  apply GenericRank.nullity_one_of_rank
  change (A.map (algebraMap (Seeds K) (PlaneField K))).rank + 1 = _
  rw [he]
  exact hn
theorem plane_stack_degree (u : Words) (b : Fin 2 × Fin L) (j : Fin (t + 1))
    (i : Fin 2) :
    (planeStack p node (u 0) (u 1) L t b j).degreeOf i ≤
      if b.1 = i then 1 else 0 :=
  syndrome_degree p node (u 0) (u 1) b.1 i _
theorem plane_stack_rank (u : Words) :
    ((planeStack p node (u 0) (u 1) L t).map
      (algebraMap (Seeds K) (PlaneField K))).rank = stackRank u := by
  let A := planeStack p node (u 0) (u 1) L t
  have hdeg (j : Fin (t + 1)) (b : Fin 2 × Fin L) :
      (A.transpose j b).degreeOf 0 ≤ if b.1 = 0 then 1 else 0 :=
    plane_stack_degree u b j 0
  have he := rank_graph p (by decide) (by decide) A.transpose hdeg
  rw [Matrix.transpose_map, Matrix.transpose_map, Matrix.rank_transpose, Matrix.rank_transpose] at he
  change ((planeStack p node (u 0) (u 1) L t).map _).rank =
    ((planeStack p node (u 0) (u 1) L t).map _).rank at he
  rw [graph_stack_map] at he
  exact he
theorem graph_content (u : Words) (T : TwoActive u) (R : Relation T)
    (Q : Fin 2 × Fin (T.height + 1) → Seeds K)
    (hQ : (planeSlice p node (u 0) (u 1) k T.height).mulVec Q = 0)
    (hgraph : (fun j => graph p (Q j)) ≠ 0) :
    ∃ c : (Polynomial K), c ≠ 0 ∧ ∀ j, graph p (Q j) = c * R.coefficients j := by
  classical
  let f := algebraMap (Polynomial K) Frac
  let M := (Strata.parameterRelation p node (u 0) (u 1) k T.height).map f
  let E := fun j => f (R.coefficients j)
  let V := fun j => f (graph p (Q j))
  obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout R.coefficients).mp R.primitive
  have hinj := IsFractionRing.injective (Polynomial K) Frac
  have hE : E ≠ 0 := by
    intro he
    have hzero (j : Fin 2 × Fin (T.height + 1)) : R.coefficients j = 0 :=
      hinj ((congrFun he j).trans (map_zero f).symm)
    simp only [hzero, mul_zero, Finset.sum_const_zero, zero_ne_one] at ha
  have hME : M.mulVec E = 0 :=
    certificate_kernel p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed k k T.height
      (by rw [IRSProfile.card_index]; decide) R
  have hMV : M.mulVec V = 0 := by
    change ((Strata.parameterRelation p node (u 0) (u 1) k T.height).map f).mulVec V = 0
    rw [← graph_slice_map]
    change ((planeSlice p node (u 0) (u 1) k T.height).map
      (f.comp (graph p).toRingHom)).mulVec
      (fun j => (f.comp (graph p).toRingHom) (Q j)) = 0
    rw [mulVec_map, hQ]
    funext j
    rw [Pi.zero_apply, map_zero, Pi.zero_apply]
  obtain ⟨b, hb⟩ := GenericRank.kernel_line_of_finrank M
    (first_slice_nullity u T) E hE hME V hMV
  let c := ∑ j, a j * graph p (Q j)
  have hc : f c = b := by
    have hbe := congrArg f ha
    simp only [map_sum, map_mul, map_one] at hbe
    simp only [c, map_sum, map_mul]
    have he (j : Fin 2 × Fin (T.height + 1)) : f (graph p (Q j)) = b * f (R.coefficients j) :=
      congrFun hb j
    simp_rw [he, mul_left_comm (f (a _)) b, ← Finset.mul_sum, hbe, mul_one]
  have he (j : Fin 2 × Fin (T.height + 1)) : graph p (Q j) = c * R.coefficients j := by
    apply hinj
    rw [map_mul, hc]
    exact congrFun hb j
  refine ⟨c, ?_, he⟩
  intro hzero
  apply hgraph
  funext j
  rw [he, hzero, zero_mul, Pi.zero_apply]
end
end Front6960_4_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace Front6960_4_1
noncomputable section
open Polynomial Matrix FrobeniusLocator Front6960
open K1_11_1 (Seeds PlaneField planePair planeStack plane_generator shifts_annihilate
  blockDegree degreeOf_coordinate graph graph_ne_zero seedPositions intoFive intoFive_omitted
  intoFive_height intoFive_seed_degree intoFive_primitive graph_intoFive)
private theorem graph_pair {F : Type} [Field F] {h : ℕ} (q : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (a : Fin 2 × Fin (h + 1) → (Polynomial F))
    (c : (Polynomial F)) (hQ : ∀ j, graph q (Q j) = c * a j) (b : Fin 2) :
    (planePair Q b).map (graph q).toRingHom =
      Polynomial.C c * Principal.assemble (fun j => a (b, j)) := by
  rw [planePair, Principal.map_assemble]
  change Principal.assemble (fun j => graph q (Q (b, j))) = _
  simp only [hQ, Principal.assemble, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.C_mul_monomial]
theorem proof : Front6960_4.c1 := by
  intro u front T R
  classical
  let h := T.height
  let s := L - h
  have hbal : L + h + nullity u = t + 1 := relation_height_balance T
  have hhi : h ≤ heightCap := relation_height_le front T
  have hL : h < L := hhi.trans_lt (by decide)
  have hsum : h + s = L := by omega
  have hs : 0 < s := by omega
  have hsL : s ≤ L := Nat.sub_le _ _
  have hSlice := plane_first_slice_nullity u T hhi
  obtain ⟨Q, hQne, hQ, hPrim⟩ := plane_generator _ (by rw [hSlice]; decide)
  let M := planeStack p node (u 0) (u 1) L t
  let W := K1_6.shifts (planePair Q) L s
  have hRank : (M.map (algebraMap (Seeds K) (PlaneField K))).rank + s = 2 * L := by
    rw [plane_stack_rank u, actual_stackRank u]
    omega
  have hker : W.transpose * M = 0 :=
    shifts_annihilate p node (u 0) (u 1) h L s t hsum Q hQ
  obtain ⟨hMP, hattain⟩ := K1_11_1_1.proof K h L s Q hsum hs hQne hPrim
  have hprod (b i : Fin 2) : s * blockDegree Q b i ≤ if b = i then h else L := by
    by_cases hd : blockDegree Q b i = 0
    · simp only [hd, Nat.mul_zero, Nat.zero_le]
    obtain ⟨rows, hdet⟩ := hattain b i (Nat.pos_of_ne_zero hd)
    have hb := K1_11_1_2.proof K L (t + 1) s M W hs hsL hRank hker
      (plane_stack_degree u) hMP b i rows
    rw [hdet] at hb
    simpa only [show L - s = h by omega] using hb
  have hgraph : (fun j => graph p (Q j)) ≠ 0 := by
    intro hz
    apply hQne
    funext j
    change Q j = 0
    by_contra hne
    obtain ⟨b, i⟩ := j
    have hbound : s * blockDegree Q b 0 ≤ L := by
      apply (hprod b 0).trans
      split_ifs
      · exact hL.le
      · exact le_rfl
    have hone : 1 ≤ s := hs
    have hdeg : (Q (b, i)).degreeOf 0 ≤ L :=
      (degreeOf_coordinate Q b 0 i).trans
        ((by simpa only [one_mul] using Nat.mul_le_mul_right (blockDegree Q b 0) hone :
          blockDegree Q b 0 ≤ s * blockDegree Q b 0).trans hbound)
    exact graph_ne_zero p (by decide) _ hne (hdeg.trans_lt (by decide)) (congrFun hz (b, i))
  obtain ⟨c, hc, hgraphQ⟩ := graph_content u T R Q hQ hgraph
  have hdegree (b i : Fin 2) :
      s * (intoFive (planePair Q b)).degreeOf (seedPositions i) ≤
        if b = i then h else L :=
    (Nat.mul_le_mul_left s (intoFive_seed_degree Q b i)).trans (hprod b i)
  refine ⟨{
    U := intoFive (planePair Q 0)
    V := intoFive (planePair Q 1)
    U_omits := ⟨intoFive_omitted Q 0 1 (Or.inl rfl), intoFive_omitted Q 0 2 (Or.inr rfl)⟩
    V_omits := ⟨intoFive_omitted Q 1 1 (Or.inl rfl), intoFive_omitted Q 1 2 (Or.inr rfl)⟩
    heights := ⟨intoFive_height Q 0, intoFive_height Q 1⟩
    bounds := ?_
    primitive := intoFive_primitive Q hPrim
    content := c
    content_ne := hc
    graphU := (graph_intoFive p (planePair Q 0)).trans (graph_pair p Q R.coefficients c hgraphQ 0)
    graphV := (graph_intoFive p (planePair Q 1)).trans (graph_pair p Q R.coefficients c hgraphQ 1)
  }⟩
  have hseedS : seedPositions 0 = 3 := rfl
  have hseedT : seedPositions 1 = 4 := rfl
  exact ⟨by simpa only [hseedS, ite_true] using hdegree 0 0,
    by simpa only [hseedT, ite_eq_right (show (0 : Fin 2) ≠ 1 by decide)] using hdegree 0 1,
    by simpa only [hseedS, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] using hdegree 1 0,
    by simpa only [hseedT, ite_true] using hdegree 1 1⟩
end
end Front6960_4_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace Front6960_4_2
noncomputable section
open Front6960 MvPolynomial
open FrobeniusLocator (locator locator_monic)
open K1_11_2 (graph OmitsMessages)
open K1_11_2_1 (graph_natDegree)
open K1_11_2_1 (divide_plane planeLocator degreeOf_le_of_dvd omits_of_dvd native_p_pos seedRelPrime parameter_only)
open Front6960_4 (degree_lt_of_product)
private theorem seed_degree_lt {h d : ℕ} (hmax : h ≤ heightCap)
    (hd : (L - h) * d ≤ L) : d < p := by
  have hh : h ≤ 33579 := hmax
  have hd' : d < 4 := degree_lt_of_product _ _ 4 _ hd (by
    change 48746 < (48746 - h) * 4
    omega)
  exact hd'.trans_le (by change 4 ≤ 2130706433; decide)
private theorem reduced_relPrime {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : Front6960_4.IndependentLift R)
    {U V : MvPolynomial (Fin 5) K} (hU : U ≠ 0) (hUo : OmitsMessages U)
    (hS : U.degreeOf 3 < p) (hAdU : U ∣ A.U) (hAdV : V ∣ A.V)
    (hgU : graph p U = Polynomial.C A.content * D.U)
    (hgV : graph p V = Polynomial.C A.content * D.V) :
    IsRelPrime U V := by
  intro d hdU hdV
  let f := (Polynomial.mapRingHom K1_8.seedInclusion).comp (graph (F := K) p).toRingHom
  have hfdU : f d ∣ extendSeed (Polynomial.C A.content * D.U) := by
    rw [← hgU]
    exact _root_.map_dvd f hdU
  have hfdV : f d ∣ extendSeed (Polynomial.C A.content * D.V) := by
    rw [← hgV]
    exact _root_.map_dvd f hdV
  have hu := seedRelPrime D.coprime A.content_ne hfdU hfdV
  have hx := Polynomial.natDegree_eq_zero_of_isUnit hu
  change ((graph p d).map K1_8.seedInclusion).natDegree = 0 at hx
  have hdo := omits_of_dvd hU hUo hdU
  rw [Polynomial.natDegree_map_eq_of_injective K1_8.seedInclusion_injective,
    graph_natDegree p native_p_pos d hdo
      ((degreeOf_le_of_dvd hU hdU 3).trans_lt hS)] at hx
  obtain ⟨q, rfl⟩ := parameter_only hdo hx
  exact (A.primitive q (hdU.trans hAdU) (hdV.trans hAdV)).map
    (rename (![3, 4] : Fin 2 → Fin 5))
theorem proof : Front6960_4.c2 := by
  intro u T R D hmax A
  have hhcap : T.height ≤ 33579 := hmax
  have hh : T.height ≤ L := hhcap.trans (by decide : 33579 ≤ 48746)
  have hASU := seed_degree_lt hmax (A.bounds.1.trans hh)
  have hASV := seed_degree_lt hmax A.bounds.2.2.1
  obtain ⟨U, hfU, hU, hgU⟩ := divide_plane (fixedNodes R) A.U D.U A.content D.U_ne
    A.content_ne A.U_omits hASU (A.graphU.trans (by simp only [D.U_factor, P0.liftX, K1.liftX]))
  obtain ⟨V, hfV, hV, hgV⟩ := divide_plane (fixedNodes R) A.V D.V A.content D.V_ne
    A.content_ne A.V_omits hASV (A.graphV.trans (by simp only [D.V_factor, P0.liftX, K1.liftX]))
  have hAdU : U ∣ A.U := hfU.symm ▸ dvd_mul_left U (planeLocator (fixedNodes R))
  have hAdV : V ∣ A.V := hfV.symm ▸ dvd_mul_left V (planeLocator (fixedNodes R))
  have hl : planeLocator (fixedNodes R) ≠ 0 := by
    simpa only [planeLocator, EmbeddingLike.map_ne_zero_iff] using
      ((locator_monic node (fixedNodes R)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K)).ne_zero
  have hAu : A.U ≠ 0 := hfU.symm ▸ mul_ne_zero hl hU
  have hAv : A.V ≠ 0 := hfV.symm ▸ mul_ne_zero hl hV
  have hUo := omits_of_dvd hAu A.U_omits hAdU
  have hVo := omits_of_dvd hAv A.V_omits hAdV
  have hUS := (degreeOf_le_of_dvd hAu hAdU 3).trans_lt hASU
  have hVS := (degreeOf_le_of_dvd hAv hAdV 3).trans_lt hASV
  refine ⟨⟨U, V, hUo, hVo, hU, hV, hAdU, hAdV,
    reduced_relPrime D A hU hUo hUS hAdU hAdV hgU hgV, ?_, hgU, hgV⟩⟩
  rw [← graph_natDegree p native_p_pos U hUo hUS,
    ← graph_natDegree p native_p_pos V hVo hVS, hgU, hgV,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr A.content_ne) D.U_ne,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr A.content_ne) D.V_ne,
    Polynomial.natDegree_C, zero_add, zero_add, D.max_degree]
end
end Front6960_4_2
end

end Merged_R6960Front6960Rank4
