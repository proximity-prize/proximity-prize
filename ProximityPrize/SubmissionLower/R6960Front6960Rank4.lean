import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup58
import ProximityPrize.SubmissionLower.Fat6966Bank24000
import ProximityPrize.SubmissionLower.Fat6966Bank32000
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.HighCore82258Pairs
import ProximityPrize.SubmissionLower.KoalaRectReceipts
import ProximityPrize.SubmissionLower.R6960Anchor6966
import ProximityPrize.SubmissionLower.R6960Anchor6966Columns
import ProximityPrize.SubmissionLower.R6960Low6960Retained
import ProximityPrize.SubmissionLower.UpperBranch3
import ProximityPrize.SubmissionLower.UpperBranch5

section Merged6967_R6960Front6960Rank4
set_option Elab.async false



set_option Elab.async false

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

end Merged6967_R6960Front6960Rank4

section Merged6967_R6960HelperSourceArithmetic
set_option Elab.async false







set_option Elab.async false

-- merged module PortLow7
section Merged_PortLow7
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_7
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32)
open P0_9 (linearChart taylorLength physicalDegree )
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
end
end P0_9_7
end
section
namespace P0_9_7_1
theorem sparse_bound : K1_13_7_1.c1 :=
  K1_13_7_1_1.of_children
    (K1_13_7_1_1_1.of_children
      (K1_13_7_1_1_1_1.of_children K1_13_7_1_1_1_1_1.proof K1_13_7_1_1_1_1_2.proof)
      (K1_13_7_1_1_1_2.of_children K1_13_7_1_1_1_2_1.proof K1_13_7_1_1_1_2_2.proof))
    K1_13_7_1_1_2.proof
theorem surface_sections : K1_13_7_1.c2 :=
  K1_13_7_1_2.of_children K1_13_7_1_2_1.proof
    (K1_13_7_1_2_2.of_children
      (K1_13_7_1_2_2_1.of_children K1_13_7_1_2_2_1_1.proof K1_13_7_1_2_2_1_2.proof)
      (K1_13_7_1_2_2_2.of_children K1_13_7_1_2_2_2_1.proof K1_13_7_1_2_2_2_2.proof))
end P0_9_7_1
end
section
namespace P0_9_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_1
open K1_13_7_1 (topAt eval_topAt topAt_coeff topView_separant)
def derivativeBox (p : Shape) : Shape := ⟨p.b - 1, p.j - 3, p.t - 1⟩
theorem derivative_box (f : Row 4) {j : ℕ} (hj : 0 < j) :
    InBox (shape ((separant^[j]) f)) (derivativeBox (shape f).chamber) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [Function.iterate_succ_apply]
  have h := derivative_in_box (separant f) k
  have hb : (shape (separant f)).b ≤ (shape f).b - 1 := by
    have hd := weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) 3 f
    simpa only [shape, weightedTotalDegree_one, Pi.one_apply, separant] using hd
  have hi : (shape (separant f)).j ≤ (shape f).j - 3 := by
    have hd := weightedTotalDegree_pderiv_le_sub (fun i : Fin 4 => i.val) 3 f
    have hthree : (3 : Fin 4).val = 3 := rfl
    simpa only [shape, indexDegree_eq, separant, hthree] using hd
  have ht : (shape (separant f)).t ≤ (shape f).t - 1 := by
    simpa only [Function.iterate_one] using derivative_degree f 1
  exact ⟨h.1.trans (hb.trans (Nat.sub_le_sub_right (le_max_left _ _) 1)),
    h.2.1.trans hi, h.2.2.trans ht⟩
end
end P0_9_7_1
end
section
namespace P0_9_7_2
noncomputable section
open Polynomial
open K1_13 (Geom Row Shape InBox shape mixed32)
open K1_13_6 (GeoJets toGeneric separant)
open K1_13_7_2 (evalTrajectory)
open P0_9 (taylorLength physicalDegree)
open P0_9_7 (fatChart )
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (P0_9_6.membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : (Polynomial L)),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
end
end P0_9_7_2
end
section
namespace P0_9_7_2
noncomputable section
open K1_13 K1_13_6 K1_13_7 K1_13_7_2 K1_13_7_2_1 K1_13_7_2_1_2
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial
open K1_13_7_2_1 (geometric_injective liftLower_ne_zero)
open K1_13_7_2_1 (local_length_one tangent_invariant)
open K1_13_7_2_1_2 (top top_rename_lower top_map top_derivative)
theorem local_generators (f : Row 4) (q : Row 3)
    (hq : Squarefree (genericRow q)) (surface : Ideal GeoJets)
    (h : LiftedSurface f q surface) : LocalGenerators f q surface h.minimal.isPrime := by
  let : surface.IsPrime := h.minimal.isPrime
  let A := Localization.AtPrime surface
  let l : GeoJets →+* A := algebraMap GeoJets A
  let J := intersectionIdeal f (liftLower q)
  let e : GeoJets ≃ₐ[GeoField] (Polynomial Lower) := top
  let F := e (toGeneric f)
  have hlower (u : Row 3) : e (toGeneric (liftLower u)) = Polynomial.C (genericRow u) := by
    change top (MvPolynomial.map genericCoeffs (MvPolynomial.rename Fin.castSucc u)) = _
    rw [MvPolynomial.map_rename, top_rename_lower]
    rfl
  have hlead : e (toGeneric (liftLower (K1_13_1.anchorLead f))) = Polynomial.C F.leadingCoeff := by
    rw [hlower]
    congr 1
    change MvPolynomial.map genericCoeffs (top f).leadingCoeff =
      (top (MvPolynomial.map genericCoeffs f)).leadingCoeff
    have hinj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp
        (IsFractionRing.injective (Polynomial Geom) GenericField)
    rw [top_map, Polynomial.leadingCoeff_map_of_injective (MvPolynomial.map_injective _ hinj)]
  have hsep : e (toGeneric (separant f)) = F.derivative := by
    change top (MvPolynomial.map genericCoeffs (MvPolynomial.pderiv 3 f)) =
      (top (MvPolynomial.map genericCoeffs f)).derivative
    rw [← MvPolynomial.pderiv_map, top_derivative]
  have hJ : J.map e.toRingHom = Ideal.span {F, Polynomial.C (genericRow q)} := by
    change (Ideal.span {toGeneric f, toGeneric (liftLower q)}).map e.toRingHom = _
    rw [Ideal.map_span, Set.image_pair]
    change Ideal.span {F, e (toGeneric (liftLower q))} = _
    rw [hlower]
  have hqrad : (Ideal.span ({genericRow q} : Set Lower)).IsRadical :=
    isRadical_iff_span_singleton.mp (isRadical_iff_squarefree_or_zero.mpr (Or.inl hq))
  have hrad : (J.map l).radical ≤ J.map l := by
    rw [← IsLocalization.map_radical surface.primeCompl A J]
    apply Ideal.map_le_iff_le_comap.mpr
    intro g hg
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hg
    have hn' : e g ^ n ∈ Ideal.span {F, Polynomial.C (genericRow q)} := by
      rw [← hJ, ← map_pow]
      exact Ideal.mem_map_of_mem e.toRingHom hn
    obtain ⟨k, hk⟩ := clear_monic_cut F (e g) hqrad hn'
    let u := toGeneric (liftLower (K1_13_1.anchorLead f)) ^ k * toGeneric (separant f)
    have hu : u ∉ surface := h.minimal.isPrime.mul_notMem
      (fun hm => h.leading (h.minimal.isPrime.mem_of_pow_mem _ hm)) h.regular
    have humem : u * g ∈ J := by
      have hc : (J.map e.toRingHom).comap e.toRingHom = J :=
        Ideal.comap_map_of_bijective e.toRingHom e.bijective
      rw [← hc, Ideal.mem_comap, hJ]
      change e (u * g) ∈ _
      simpa only [u, map_mul, map_pow, hlead, hsep, mul_assoc] using hk
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff surface.primeCompl A J g).mpr
      ⟨u, hu, humem⟩
  change J.map l = IsLocalRing.maximalIdeal A
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal surface A,
      ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A surface J h.minimal]
  exact le_antisymm Ideal.le_radical hrad
end
end P0_9_7_2
end
section
namespace P0_9_7_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row shape)
open K1_13_6 (GeoJets GeoField GenericField toGeneric genericCoeffs divisorIdeal)
open K1_13_6_3 (JetIdeal dimension geomConstants)
open K1_13_7_2_5 (wholeComponents properComponents)
open P0_9_7 (fatChart)
open P0_9_7_2 ( FatTaylor)
open scoped BigOperators
private theorem generic_degree_le (g : Row 4) : (toGeneric g).totalDegree ≤ g.totalDegree := by
  rw [toGeneric, MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
theorem generic_ne_zero {f : Row 4} (hf : Irreducible f) : toGeneric f ≠ 0 := by
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
  exact (map_ne_zero_iff (MvPolynomial.map genericCoeffs) (MvPolynomial.map_injective _ hinj)).mpr
    hf.ne_zero
theorem whole_dimension {f : Row 4} {component : JetIdeal} (hf : Irreducible f)
    (hZ : (Ideal.span {toGeneric f}).IsMinimalPrime component) : dimension component = 3 := by
  have h := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton
    (generic_ne_zero hf) hZ
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  change dimension component + 1 = 4 at h
  omega
theorem whole_sum {f : Row 4} (hf : Irreducible f) :
    ∑ component ∈ wholeComponents f, affineDegree component ≤ ((shape f).chamber.b : ℚ) := by
  have hn : toGeneric f ∉ (⊥ : JetIdeal) := fun h => generic_ne_zero hf ((Ideal.mem_bot).mp h)
  have hd : (toGeneric f).totalDegree ≤ (shape f).chamber.b :=
    (generic_degree_le f).trans (Nat.le_max_left _ _)
  simpa only [wholeComponents, bot_sup_eq, affineDegree_bot, mul_one] using (principalCut_sum_affineDegree_minimalPrimes_le (P := (⊥ : JetIdeal)) hn hd)
end
end P0_9_7_2_3
end
section
namespace P0_9_7_3
noncomputable section
open Polynomial K1_13 K1_13_7 K1_13_7_1 K1_13_7_5 K1_13_7_5_1 K1_13_7_5_3
open scoped BigOperators Pointwise
open K1_13_7_5_1 (lift_length_ge lift_length_finite)
open K1_13_7_5_3 (supported_anchor supported_lower supported_coordinate mixed_matches)
theorem common_section : K1_13_7_5_3.c1 :=
  K1_13_7_5_3_1.of_children K1_13_7_5_3_1_1.proof K1_13_7_5_3_1_2.proof
theorem sparse_length : K1_13_7_5_3.c3 :=
  K1_13_7_5_3_3.of_children K1_13_7_5_3_3_1.proof
    (K1_13_7_5_3_3_2.of_children K1_13_7_5_3_3_2_1.proof K1_13_7_5_3_3_2_2.proof)
    (K1_13_7_5_3_3_3.of_children K1_13_7_5_3_3_3_1.proof K1_13_7_5_3_3_3_2.proof)
    K1_13_7_5_3_3_4.proof
end
end P0_9_7_3
end
section
namespace P0_9_7_3
noncomputable section
open Polynomial Finset K1 K1_13 K1_13_7 K1_13_7_5 K1_13_7_1
open scoped BigOperators
open K1_13_7_5 (supported_sub supported_C supported_X exists_coordinate_cut jetPoint_injective chart_section eval_chart_section weighted_ceil)
theorem choose_linear_cut {f : Row 4} (ht : 0 < (shape f).t)
    {r : PrimeSpectrum Jets} {y : JetPoint} (h : r.asIdeal < jetPointIdeal y) :
    ∃ F : Jets, Supported (shape f).chamber F ∧ F ∉ r.asIdeal ∧
      r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_cut h
  obtain ⟨hb, hj⟩ := shape_chamber f
  have hj' : 3 ≤ (shape f).chamber.j := by
    have htop : 0 < (shape f).chamber.t := ht
    omega
  have hb' : 1 ≤ (shape f).chamber.b := (by decide : 1 ≤ 3).trans (hj'.trans hb)
  exact ⟨MvPolynomial.X i - MvPolynomial.C (y i),
    supported_sub (supported_X hb' hj' ht i) (supported_C _ _), hi, h.le, by simp⟩
end
end P0_9_7_3
end
section
namespace P0_9_7_3_1
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open scoped BigOperators
open K1_13_7_5_2 (linearJet eval_linearJet separant_bound linearJet_bound denominator ordinary_eq_hasse)
open K1_13_7_5_2 (supported_of_fits eval_center)
open K1_13_7_5 (supported_C_mul)
local notation "W" => MvPolynomial.weightedTotalDegree
def numerator (L : ℕ) (f : Row 4) (n : ℕ) : Row 4 :=
  if hn : n < 4 then MvPolynomial.X ⟨n, hn⟩ * K1_13_7_5_2.denominator L f
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial : Geom)⁻¹) *
      (separant f ^ (L - n) * linearJet f n)
theorem denominator_bound (L : ℕ) (w : Fin 4 → ℕ) {f : Row 4} {B : ℕ}
    (hf : W w f ≤ B) : W w (K1_13_7_5_2.denominator L f) ≤ L * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (separant_bound w hf))
theorem numerator_bound {L n : ℕ} (hn : n ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {f : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hf : W w f ≤ B) :
    W w (numerator L f n) ≤ d₀ + L * (B - w 3 + Δ) := by
  unfold numerator
  split_ifs with hinit
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (denominator_bound L w hf)).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _))
  · have hp := (weightedTotalDegree_pow_le w (separant f) (L - n)).trans
      (Nat.mul_le_mul_left _ (separant_bound w hf))
    apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ (L - n) * (B - w 3) + (w 0 + n * (B - w 3 + Δ)) :=
        Nat.add_le_add hp (linearJet_bound w Δ hshift hB hf n)
      _ = w 0 + ((L - n) + n) * (B - w 3) + n * Δ := by ring
      _ ≤ _ := by
        rw [Nat.sub_add_cancel hn, Nat.mul_add]
        simpa only [Nat.add_assoc] using
          Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hn)
theorem coefficients_recover {L : ℕ} (hL : L < K1.p) {f : Row 4}
    (hf : (shape f).t = 1) (S : (Polynomial Geom)) (hon : atJet f S = 0) (hr : RegularAt f S) :
    evalGeneric S (toGeneric (K1_13_7_5_2.denominator L f)) ≠ 0 ∧
      ∀ i : Fin L, evalGeneric S (toGeneric (numerator L f i.val)) =
        evalGeneric S (toGeneric (K1_13_7_5_2.denominator L f)) * genericCoeffs (hasseDeriv i.val S) := by
  have hp : atJet (separant f) S ≠ 0 := hr
  have hden : atJet (K1_13_7_5_2.denominator L f) S = atJet (separant f) S ^ L :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))) _ _
  constructor
  · rw [evalGeneric_toGeneric, hden]
    exact (map_ne_zero_iff _ genericCoeffs_injective).mpr (pow_ne_zero _ hp)
  · intro i
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant f) S ^ (L - i.val) *
        atJet (linearJet f i.val) S) = _
      rw [eval_linearJet hf S hon hr, K1_13_7_5_2.ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ *
          Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero (i.isLt.trans hL)), map_one]
      have hpow : L - i.val + i.val = L := Nat.sub_add_cancel i.isLt.le
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant f) S ^ (L - i.val) * atJet (separant f) S ^ i.val) *
              hasseDeriv i.val S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
private abbrev constants : Geom →+* GeometricX := genericCoeff.comp Polynomial.C
private abbrev center : GeometricX := genericCoeff Polynomial.X
private theorem eval_taylor {L : ℕ} (S : (Polynomial K)) (hS : S.natDegree < L) (x : K) :
    (∑ j : Fin L, (constantCoeff x - center) ^ j.val *
      genericCoeff (hasseDeriv j.val (extend S))) = constantCoeff (S.eval x) := by
  let P := (extend S).map constants
  let u := constantCoeff x - center
  have hcoeff (n : ℕ) : (Polynomial.taylor center P).coeff n =
      genericCoeff (hasseDeriv n (extend S)) := by
    rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
  have hd : (Polynomial.taylor center P).natDegree < L := by
    rw [Polynomial.natDegree_taylor]
    exact (Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le).trans_lt hS
  have hev : P.eval (constantCoeff x) = constantCoeff (S.eval x) := by
    change ((S.map embed).map constants).eval (constantCoeff x) = _
    rw [Polynomial.map_map]
    exact Polynomial.eval_map_apply K1_13_7_5.constantCoeff x
  calc
    _ = (Polynomial.taylor center P).eval u := by
      rw [Polynomial.eval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range]
      simp only [hcoeff, u]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = P.eval (constantCoeff x) := Polynomial.taylor_eval_sub _ _ _
    _ = _ := hev
theorem values_of_coefficients {L : ℕ} {H : Shape} (D : GeoJets) (N : Fin L → GeoJets)
    (hD : GeoFits D H) (hN : ∀ j, GeoFits (N j) H) :
    ∃ C : ValueChart H, ∀ S : (Polynomial K), S.natDegree < L →
      (evalGeneric (extend S) D ≠ 0 ∧ ∀ j, evalGeneric (extend S) (N j) =
        evalGeneric (extend S) D * genericCoeffs (hasseDeriv j.val (extend S))) →
      C.recovers S := by
  let value (i : I) : Jets :=
    ∑ j : Fin L, MvPolynomial.C ((constantCoeff (node i) - center) ^ j.val) * N j
  have hvalue (i : I) : Supported H (value i) := by
    classical
    intro m hm
    unfold value at hm
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    exact supported_C_mul (supported_of_fits (hN j)) _ m hj
  refine ⟨⟨D, value, supported_of_fits hD, hvalue⟩, ?_⟩
  intro S hS h
  refine ⟨h.1, fun i => ?_⟩
  let ev := evalGeneric (extend S)
  change ev (value i) = constantCoeff (S.eval (node i)) * ev D
  have hc (a : GeometricX) : ev (MvPolynomial.C a) = a := MvPolynomial.eval_C a
  have he (j : Fin L) : ev (N j) =
      ev D * genericCoeff (hasseDeriv j.val (extend S)) := h.2 j
  simp only [value, map_sum, map_mul, hc, he]
  calc
    _ = ev D * (∑ j : Fin L, (constantCoeff (node i) - center) ^ j.val *
        genericCoeff (hasseDeriv j.val (extend S))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_left_comm _ _ _)
    _ = _ := by rw [eval_taylor S hS, mul_comm]
end
end P0_9_7_3_1
end
section
namespace P0_9_7_3_2
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open K1_13_1 (indexDegree_eq)
open scoped BigOperators
open K1_13_7_1 (denominator denominator_bound topPartial_bound jet_bound ordinary_eq_hasse)
open K1_13_7_5_2 (supported_of_fits constants center eval_center)
open K1_13_7_5 (supported_C_mul)
local notation "W" => MvPolynomial.weightedTotalDegree
def coefficientNumerator (L : ℕ) (g : Row 4) (n : ℕ) : Row 4 :=
  if hn : n < 4 then MvPolynomial.X ⟨n, hn⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - n)) * jetNumerator g n)
private theorem numerator_bound {L n : ℕ} (hn : n ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) :
    W w (coefficientNumerator L g n) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  unfold coefficientNumerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (denominator_bound L w hg)).trans
        (Nat.le_add_right _ _))
  · have hp := (weightedTotalDegree_pow_le w (separant g) (2 * (L - n))).trans
      (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))
    apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - n) * (B - w 3) + (w 0 + n * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add hp (jet_bound w Δ hshift hB hg n)
      _ = w 0 + 2 * (n + (L - n)) * (B - w 3) + n * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hn]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hn)
theorem coefficients_fit (L : ℕ) (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t) :
    GeoFits (toGeneric (denominator L g)) (chart L p) ∧
      ∀ n ≤ L, GeoFits (toGeneric (coefficientNumerator L g n)) (chart L p) := by
  have hb : 1 ≤ p.b := by have := hp.1; have := hp.2; omega
  have hj : 3 ≤ p.j := by have := hp.2; omega
  have h₁ : W 1 g ≤ p.b := by simpa only [shape, weightedTotalDegree_one] using hB.1
  have h₂ : W Fin.val g ≤ p.j := by simpa only [shape, indexDegree_eq] using hB.2.1
  let w : Fin 4 → ℕ := Pi.single 3 1
  have h₃ : W w g ≤ p.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, w i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have hw3 : w 3 = 1 := by decide
  have fits (P : Row 4) (hb' : W 1 P ≤ 1 + 2 * L * (p.b - 1))
      (hj' : W Fin.val P ≤ 2 * L * (p.j - 3) + L + 3)
      (ht' : W w P ≤ 2 * L * (p.t - 1) + L + 1) :
      GeoFits (toGeneric P) (chart L p) := by
    apply toGeneric_fits
    refine ⟨?_, ?_, ?_⟩
    · change P.totalDegree ≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree ≤ 1 + 2 * L * (p.b - 1)).trans (le_max_left _ _)
    · change indexDegree P ≤ _
      rwa [indexDegree_eq]
    · change P.degreeOf 3 ≤ min _ _
      apply le_min
      · simpa only [w, weightedTotalDegree_piSingle] using ht'
      · have h := (top_le_index P).trans hj'
        omega
  constructor
  · apply fits
    · exact (denominator_bound L _ h₁).trans (Nat.le_add_left _ _)
    · exact (denominator_bound L _ h₂).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    · have h := denominator_bound L w h₃
      rw [hw3] at h
      exact h.trans (by omega)
  · intro n hn
    apply fits
    · have h := numerator_bound hn 1 0 1 (fun _ => by simp) (fun _ => le_rfl) hb h₁
      change W 1 (coefficientNumerator L g n) ≤ 1 + 2 * L * (p.b - 1) + L * 0 at h
      simpa only [mul_zero, add_zero] using h
    · have h := numerator_bound hn Fin.val 1 3 (fun _ => by rfl)
        (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj h₂
      change W Fin.val (coefficientNumerator L g n) ≤ 3 + 2 * L * (p.j - 3) + L * 1 at h
      simpa only [mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
    · have hwle : w 3 ≤ p.t := hw3.symm ▸ ht
      have h := numerator_bound hn w 1 1 hshift hw hwle h₃
      simpa only [hw3, mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
theorem coefficients_recover (L : ℕ) (g : Row 4) (S : (Polynomial Geom))
    (hg : atJet g S = 0) (hr : RegularAt g S) :
    evalGeneric S (toGeneric (denominator L g)) ≠ 0 ∧
      ∀ n ≤ L, n < K1.p →
        evalGeneric S (toGeneric (coefficientNumerator L g n)) =
          evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv n S) := by
  have hp : atJet (separant g) S ≠ 0 := hr
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))) _ _
  constructor
  · rw [evalGeneric_toGeneric]
    apply (map_ne_zero_iff _ genericCoeffs_injective).mpr
    rw [hden]
    exact pow_ne_zero _ hp
  · intro n hn hc
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold coefficientNumerator
    split_ifs
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - n)) * atJet (jetNumerator g n) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑n.factorial : Geom)⁻¹ * Polynomial.C (↑n.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero hc), map_one]
      have hpow : 2 * (L - n) + 2 * n = 2 * L := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hn]
      calc
        _ = (Polynomial.C (↑n.factorial : Geom)⁻¹ * Polynomial.C (↑n.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - n)) * atJet (separant g) S ^ (2 * n)) *
              hasseDeriv n S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
end
end P0_9_7_3_2
end

end Merged_PortLow7

-- merged module GoldBranch6N6
section Merged_GoldBranch6N6
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_6
noncomputable section
open Polynomial
open P3 (K)
open P3_6 ( physicalDegree primaryBox  taylorLength TrueWeightLE)
open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength + 1)
end
end P3_6_6
end
section
namespace P3_6_6
noncomputable section
open Polynomial
open P3 (K)
open P3_6 (physicalPrice primaryBox surfaceNumerator32 taylorLength)
open K1_13 (Row Shape Geom extend atJet shape ceilDiv)
open K1_13_6 (Pieces toGeneric
  separant jetNumerator HighMark divisorIdeal cycleLength eval_jetNumerator)
open K1_13_6_1 (mem_markIdeal mark_curve)
open scoped BigOperators
end
end P3_6_6
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial
open P3 (K)
open P3_6 (physicalDegree primaryBox taylorLength)
open P3_6_6 (membershipTest nextTest)
open K1_13 (Row Shape Geom shape extend chart liftedChart mixed32)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength CanonicalChart
  Invariant separant divisorIdeal partialFlow)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint Box4 Box5 graphBox)
open scoped BigOperators
structure Branch (f Q : Row 4) (l : ℕ) where
  surface : Ideal GeoJets
  r : ℕ
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  chart : CanonicalChart f surface r
  invariant : Invariant ((separant^[r]) f) surface
  proper : toGeneric (membershipTest ((separant^[r]) f)) ∉ surface
  curve : Ideal GeoJets
  divisor : (divisorIdeal surface (membershipTest ((separant^[r]) f))).IsMinimalPrime curve
  regularCurve : toGeneric (separant ((separant^[r]) f)) ∉ curve
  terminal :
    cycleLength (divisorIdeal surface (membershipTest ((separant^[r]) f))) curve
      divisor.isPrime ≠ 1 ∨ toGeneric (nextTest ((separant^[r]) f)) ∉ curve
namespace Branch
variable {f Q : Row 4} {l : ℕ} (b : Branch f Q l)
def g : Row 4 := (separant^[b.r]) f
def sigma : GeoJets := toGeneric (separant b.g)
def graph : GeoJets5 :=
  MvPolynomial.rename Fin.castSucc (toGeneric (partialFlow b.g)) +
    MvPolynomial.C (4 : GeoField) * MvPolynomial.rename Fin.castSucc b.sigma *
      MvPolynomial.X (Fin.last 4)
abbrev Local := Localization.Away b.sigma
def localMap : GeoJets →+* b.Local := algebraMap GeoJets b.Local
def onGraph : GeoJets5 →+* b.Local :=
  MvPolynomial.eval₂Hom (b.localMap.comp MvPolynomial.C)
    (Fin.lastCases
      (b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma)
      (fun i => b.localMap (MvPolynomial.X i)))
end Branch
end
end P3_6_6_2
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial
open P3_6 (physicalDegree)
open K1_13 (Geom Row Shape shape InBox atJet jet indexDegree)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GenericField GeoField genericCoeffs toGeneric separant)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open scoped BigOperators
namespace Branch
variable {f Q : Row 4} {l : ℕ}
end Branch
end
end P3_6_6_2
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial MvPolynomial
open P3 (K)
open P3_6 (physicalDegree  taylorLength)
open K1_13 (Row Shape Geom InBox embed extend shape chart atJet jet)
open K1_13_6 (GeoJets GeoField GenericField genericCoeffs evalGeneric toGeneric
  separant jetNumerator eval_jetNumerator)
open K1_13_6_2_1 (jet_fits oldBox_of_fits three_weights separant_pow_bound jet_bound)
open K1_13_7_1 (Chamber GeoFits shape_chamber weight_X_le weight_const_mul_le)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private abbrev TaylorIndex := Fin taylorLength
private structure TaylorChart where
  denom : GeoJets
  numerator : TaylorIndex → GeoJets
end
end P3_6_6_2
end
section
namespace P3_6_6_2_1
noncomputable section
open Polynomial MvPolynomial
open P3_6_6_2 (Branch )
open K1_13 (Geom Row Shape InBox shape indexDegree liftedChart)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GeoField genericCoeffs toGeneric separant partialFlow jetNumerator)
open K1_13_6_2 (GeoJets5 Box5 graphBox)
open K1_13_6_2_2 (lift4 generic5 rawGraph numerator denominator padded)
open K1_13_6_2_2_2 (Chart incl S invS S_mul_invS negQuarter q constants W
  graphMap graphMap_lift graphMap_X_last)
open scoped BigOperators
open K1_13_6_2_2_2 (compare_numerators)
open K1_13_6_2_2_1 (support_bounds topWeight fifthWeight box_of_weights)
variable {f Q : Row 4} {l : ℕ}
@[simp] theorem onGraph_C (b : Branch f Q l) (a : GeoField) :
    b.onGraph (MvPolynomial.C a) = b.localMap (MvPolynomial.C a) := by
  simp [Branch.onGraph]
private def toBranch (b : Branch f Q l) : Chart b.g →+* b.Local :=
  IsLocalization.Away.lift (separant b.g)
    (g := b.localMap.comp (MvPolynomial.map genericCoeffs))
    (IsLocalization.Away.algebraMap_isUnit b.sigma)
@[simp] private theorem toBranch_incl (b : Branch f Q l) (P : Row 4) :
    toBranch b (incl b.g P) = b.localMap (toGeneric P) :=
  IsLocalization.Away.lift_eq _ _ _
local notation "wtDegree" => MvPolynomial.weightedTotalDegree
end
end P3_6_6_2_1
end
section
namespace P3_6_6_2_3
noncomputable section
open P3_6 (primaryBox taylorLength)
open P3_6_6_2 (Branch)
open K1_13 (Shape liftedChart)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5 graphBox)
open K1_13_6_2_4 (Boxes)
end
end P3_6_6_2_3
end
section
namespace P3_6_6_2_3
noncomputable section
open P3_6_6_2 (Branch)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (oldEmbedding)
end
end P3_6_6_2_3
end
section
namespace P3_6_6_2_3_2
noncomputable section
open P3_6_6 (membershipTest)
open P3_6_6_2 (Branch)
open K1_13_6 (GeoField GeoJets toGeneric partialFlow divisorIdeal cycleLength)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_3 (localWeight weight_cast weight_pos)
open K1_13_6_2_4 (OfDim LengthAt sectionIdeal oldEmbedding)
open K1_13_6_2_4_5 (four_ne_zero)
open K1_13_6_2_4_5 (length_le_of_surjection dim_after_proper_cut)
local notation "memberDiv" b => divisorIdeal (Branch.surface b) (membershipTest (Branch.g b))
end
end P3_6_6_2_3_2
end
section
set_option autoImplicit false
namespace P3_6_6_3
noncomputable section
open K1_13 (Row)
open K1_13_6 (toGeneric divisorIdeal cycleLength)
open K1_13_6_3 (CoeffIdeal JetIdeal)
open P3_6_6 (membershipTest nextTest)
end
end P3_6_6_3
end
section
set_option autoImplicit false
namespace P3_6_6_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal)
open K1_13_6_3_1
attribute [local instance] MvPolynomial.algebraMvPolynomial
open P0_9_6_3 (flat_sepToGeo map_eq_maximal_of_length_one step_in_sep sep_sq_dvd_jet nonvanishing_of_simple_cut stable_of_simple_cut)
end
end P3_6_6_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace P3_6_6_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_6_3_5_3 (tupleHeight_le_of_inclusion finsum_weighted cone_eval_jets jet_zero_nonzero)
end
end P3_6_6_3_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace P3_6_6_3_2
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3 K1_13_6_3_5
attribute [local instance] MvPolynomial.gradedAlgebra
end
end P3_6_6_3_2
end

end Merged_GoldBranch6N6

-- merged module GoldBranch6N7
section Merged_GoldBranch6N7
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_7
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32 Row)
open K1_13_7 (LowerPoint pointIdeal pairIdeal tripleIdeal localColength)
open P3_6 (commonBox resultantBox fatOrder divisorOrder isolatedOrder taylorLength
  linearChart incidenceGap physicalDegree)
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
end
end P3_6_7
end
section
namespace P3_6_7_2
noncomputable section
open Polynomial
open K1_13 (Geom Row Shape InBox shape mixed32 atJet)
open K1_13_6 (GeoJets toGeneric separant cycleLength intersectionIdeal Invariant)
open K1_13_7 (LowerCaps genericRow)
open K1_13_7_2 (evalTrajectory LiftedSurface lowerFlow liftLower)
open P3_6 (taylorLength physicalDegree)
open P3_6_7 (fatChart )
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (P3_6_6.membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : (Polynomial L)),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
end
end P3_6_7_2
end
section
namespace P3_6_7_2
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open K1_13_7_2_2 (stride raw topLinear denominator numerator hasseNumerator)
open K1_13_7_1 (weight_const_mul_le top_le_index shape_chamber Chamber)
open K1_13_1 (indexDegree_eq)
open K1_13_7_2_2 (raw_false raw_true_compare)
open K1_13_7_2_2 (raw_bound sep_pow_bound)
open K1_13_7_2_2 (specializes topLinear_regular)
local notation "W" => MvPolynomial.weightedTotalDegree
end
end P3_6_7_2
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace P3_6_7_2_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_3 K1_13_7
open K1_13_7_2_4 K1_13_7_2_4_2
open P3_6 (physicalDegree )
open K1_13_7_2_4_2 (intDerivation coeffDeriv coeffDeriv_zero_of_shift zero_of_stationary_eval rowTrajectory rowTrajectory_stationary eval_chartTrajectory)
open K1_13_7_2_4 (sum_monomial_eq_of_coeffs)
open K1_13_7_2_4 (trajectory_at_component component_ne_zero)
end
end P3_6_7_2_2
end
section
set_option autoImplicit false
namespace P3_6_7_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row)
open K1_13_6 (GeoField GeoJets toGeneric separant)
open K1_13_6_3 (JetIdeal dimension geomConstants genericArgument)
open P3_6 (taylorLength)
open P3_6_7_2 ( FatTaylor)
end
end P3_6_7_2_3
end
section
namespace P3_6_7_3
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open K1_13_1 (indexDegree_eq)
open P3_6 (physicalDegree)
section
open K1_13_7_5_2 (denominator)
open P0_9_7_3_1 (numerator numerator_bound denominator_bound coefficients_recover)
local notation "W" => MvPolynomial.weightedTotalDegree
end
section
open K1_13_7_1 (denominator)
open P0_9_7_3_2 (coefficientNumerator coefficients_fit coefficients_recover)
end
end
end P3_6_7_3
end

end Merged_GoldBranch6N7

-- merged module LowerBase
section Merged_LowerBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_6
noncomputable section
open Polynomial
open P1 (I K k node agreement)
open K1_13 (Geom embed extend Row Shape shape InBox atJet OnFactor OrderAt indexDegree
  chart liftedChart mixed32 ceilDiv)
open scoped BigOperators
inductive Bank where
  | primary
  | secondary
  deriving DecidableEq
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ 3284
  common_index : indexDegree common ≤ 1120
  residual_total : residual.totalDegree ≤ 409200000
  residual_index : indexDegree residual ≤ 129000000
end
end P1_6
end
section
namespace P1_6
noncomputable section
open Polynomial
open P1 (K I k node AnchorModel AnchoredFamily)
open K1_13 (Geom embed extend atJet PoleData)
open scoped BigOperators
end
end P1_6
end

end Merged_LowerBase

-- merged module UpperBranch8
section Merged_UpperBranch8
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_8
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P1 (K I node agreement)
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8
noncomputable section
open Polynomial Finset
open P1 (K I Words AnchorModel AnchoredFamily p node agreement blockLength)
open P1_7 (Reduced AdjacentChart regularRoot degreeAt quotientOrder singularDegree)
open K1_14 (L FX Seeds Equation SeedBound liftPoly atMark seedEmbedding)
open K1_14_4 (seedDegree)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten cleared separant markEval)
open scoped BigOperators
structure Input where
  words : Words
  deleted : Finset I
  model : AnchorModel words deleted
  labels : Finset K
  family : AnchoredFamily model labels
  shift_out : model.shift ∉ labels
  block : (Polynomial L)
  chart : AdjacentChart model family block
  marks : Finset K
  marks_sub : marks ⊆ labels
  f : Equation
  regular : ∀ γ ∈ marks, regularRoot f (model.label γ) (family.scalar γ)
  reduced : Reduced f
  sheets : 3 ≤ f.natDegree
  seed_pos : 0 < seedDegree f
  v : ℕ
  seed_bound : SeedBound f v
  lo : ℕ
  hi : ℕ
  lower : lo ≤ model.overhead.toNat
  upper : model.overhead.toNat ≤ hi
  positive : 0 < model.overhead.toNat
  quotient_pos : 0 < quotientOrder model.overhead.toNat
  agreement_gap : degreeAt hi < agreement
  factorial_guard : degreeAt hi + 1 < p
  separant_guard : singularDegree f.natDegree v < p
  flat_guard : f.natDegree * degreeAt hi + v < p
abbrev Input.w (J : Input) : ℕ := J.model.overhead.toNat
abbrev Input.ell (J : Input) : ℕ := quotientOrder J.w
abbrev Input.e (J : Input) : ℕ := J.f.natDegree
def Input.secondBlock (J : Input) : (Polynomial L) := J.block.map (frobenius L p)
def Input.blockProduct (J : Input) : (Polynomial L) := J.block * J.secondBlock
abbrev SeedConstants := MvPolynomial (Fin 2) L
def residueData (_J : Input) (i : Fin 2) (g : (Polynomial K)) : (Polynomial SeedConstants) :=
  ((liftPoly g).map (if i = 0 then RingHom.id L else frobenius L p)).map MvPolynomial.C
def blockAt (J : Input) (i : Fin 2) : (Polynomial L) :=
  if i = 0 then J.block else J.secondBlock
def residueDenominator (J : Input) (i : Fin 2) : (Polynomial SeedConstants) :=
  residueData J i (J.model.factor * J.model.A₀) +
    C (MvPolynomial.X i) * residueData J i (J.model.factor * J.model.A₁)
def evalSeedConstants (z : K) : SeedConstants →+* L :=
  MvPolynomial.eval ![algebraMap K L z, (algebraMap K L z)^p]
structure ResidueLift (J : Input) where
  denominator : SeedConstants
  numerator : (Polynomial SeedConstants)
  denominator_ne : denominator ≠ 0
  denominator_degree : denominator.totalDegree ≤ 2 * J.w
  numerator_degree : ∀ j, (numerator.coeff j).totalDegree ≤ 2 * J.w
  numerator_width : numerator.natDegree < 2 * J.w
  congruences : ∀ i : Fin 2, (blockAt J i).map MvPolynomial.C ∣
    residueDenominator J i * numerator +
      C (MvPolynomial.X i * denominator) * residueData J i J.model.Q
  unit_at_marks : ∀ γ ∈ J.labels, evalSeedConstants (J.model.label γ) denominator ≠ 0
def constantAbscissa : L →+* FX :=
  (algebraMap (Polynomial L) FX).comp Polynomial.C
def liftSeeds : SeedConstants →+* Seeds := MvPolynomial.map constantAbscissa
def seedBiform : SeedConstants →+* Biform :=
  (MvPolynomial.rename (R := FX) (some : Fin 2 → Option (Fin 2))).toRingHom.comp liftSeeds
def center : FX := algebraMap (Polynomial L) FX Polynomial.X
def liftTaylor (P : (Polynomial SeedConstants)) (i : ℕ) : Biform :=
  (Polynomial.taylor (MvPolynomial.C center) (P.map seedBiform)).coeff i
def inverseBlockCoeff (J : Input) (i : ℕ) : FX :=
  (i.factorial : FX)⁻¹ *
    (Dx^[i]) ((algebraMap (Polynomial L) FX J.blockProduct)⁻¹)
def ordinateTaylorNum (f : Equation) (r : ℕ) : ℕ → Biform
  | 0 => separant (flatten f) ^ (2*r-1) * MvPolynomial.X none
  | i + 1 => MvPolynomial.C (((i+1).factorial : FX)⁻¹) *
      (separant (flatten f) ^ ((2*r-1)-(2*i+1)) * cleared (flatten f) i)
def quotientNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  ∑ i ∈ range (r+1), MvPolynomial.C (inverseBlockCoeff J (r-i)) *
    (seedBiform B.denominator * ordinateTaylorNum J.f r i -
      separant (flatten J.f) ^ (2*r-1) * liftTaylor B.numerator i)
def quotientDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  seedBiform B.denominator * separant (flatten J.f) ^ (2*r-1)
def cutoff (J : Input) (B : ResidueLift J) : Equation :=
  MvPolynomial.optionEquivLeft FX (Fin 2) (quotientNumerator J B (J.ell+1))
abbrev SeedField := FractionRing Seeds
def generic (q : Equation) : (Polynomial SeedField) := q.map (algebraMap Seeds SeedField)
def rootOn (J : Input) (q : Equation) (γ : K) : Prop :=
  atMark q (J.model.label γ) (J.family.scalar γ) = 0
structure Factors (J : Input) (B : ResidueLift J) where
  proper : Equation
  count : ℕ
  flat : Fin count → Equation
  product : J.f = proper * ∏ j, flat j
  cutoff_at_marks : ∀ γ ∈ J.marks, rootOn J (cutoff J B) γ
  proper_coprime : IsCoprime (generic proper) (generic (cutoff J B))
  flat_reduced : ∀ j, Reduced (flat j)
  flat_irred : ∀ j, Irreducible (generic (flat j))
  flat_cutoff : ∀ j, generic (flat j) ∣ generic (cutoff J B)
  sheets : count ≤ J.e
  degree_each : ∀ j, (flat j).natDegree ≤ J.e
  seed_sum : ∑ j, seedDegree (flat j) ≤ J.v
structure ProperCurve (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime : Ideal Equation
  isPrime : prime.IsPrime
  onProper : D.proper ∈ prime
  onCutoff : cutoff J B ∈ prime
  marks : Finset K
  sub : marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker
    (eval₂RingHom (K1_14.graphEval (J.model.label γ)) (K1_14.atX (J.family.scalar γ)))
  persistent : Finset I
  hits : ∀ γ ∈ marks, ∀ x ∈ persistent, (J.family.scalar γ).eval (node x) = J.model.word x
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
  positive_seed : 0 < seed
  sections : ∀ x ∉ persistent,
    let r := J.ell - persistent.card
    (marks.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x).card ≤
      (1 + (J.e-3)*r)*fiber + r*tangent + (r*J.v + 2*J.w)*seed
def cutVelocity (J : Input) : ℕ := quotientOrder J.lo + 1
def cutOrdinate (J : Input) : ℕ := 1 + cutVelocity J * (J.e-1)
def cutSeed (J : Input) : ℕ := cutVelocity J * J.v + 2*J.hi
structure ProperCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count : ℕ
  curves : Fin count → ProperCurve J B D
  covers : ∀ γ ∈ J.marks, rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).fiber ≤ J.v*cutSeed J + J.v^2*cutVelocity J
  tangent : ∑ j, (curves j).tangent ≤ 2*J.e*J.v*cutSeed J + J.v^2*cutOrdinate J
  seed : ∑ j, (curves j).seed ≤
    J.e*cutSeed J + J.v*((2*J.e-2)*cutVelocity J + cutOrdinate J)
abbrev SeedClosure := AlgebraicClosure SeedField
def intoSeedClosure : Seeds →+* SeedClosure :=
  (algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField)
def genericPoint (y : SeedClosure) : Biform →+* SeedClosure :=
  (eval₂RingHom intoSeedClosure y).comp (MvPolynomial.optionEquivLeft FX (Fin 2)).toRingHom
def liftConstantSeeds : SeedConstants →+* SeedClosure :=
  intoSeedClosure.comp liftSeeds
def reconstructed (J : Input) (B : ResidueLift J) (y : SeedClosure) : (Polynomial SeedClosure) :=
  let ζ := intoSeedClosure (MvPolynomial.C center)
  let ev := genericPoint y
  C ((liftConstantSeeds B.denominator)⁻¹) * B.numerator.map liftConstantSeeds +
    J.blockProduct.map (liftConstantSeeds.comp MvPolynomial.C) *
      ∑ j ∈ range (J.ell+1),
        C (ev (quotientNumerator J B j) / ev (quotientDenominator J B j)) *
          (Polynomial.X - C ζ)^j
def genericRoots (q : Equation) : Finset SeedClosure := by
  classical
  exact (q.map intoSeedClosure).roots.toFinset
structure DifferentialProduct (J : Input) (B : ResidueLift J) (q : Equation) where
  numerator : Polynomial (Polynomial Seeds)
  denominator : Seeds
  denominator_ne : denominator ≠ 0
  leading : numerator.coeff q.natDegree = C denominator
  abscissa_width : ∀ j, (numerator.coeff j).natDegree ≤ q.natDegree * degreeAt J.hi
  numerator_constant : ∀ i j m, Dx (((numerator.coeff i).coeff j).coeff m) = 0
  denominator_constant : ∀ m, Dx (denominator.coeff m) = 0
  identity :
    numerator.map (Polynomial.mapRingHom intoSeedClosure) =
      C (C (intoSeedClosure denominator)) *
        ∏ y ∈ genericRoots q,
          (Polynomial.X - C (reconstructed J B y))
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8
noncomputable section
open P1 (agreement blockLength)
open P1_7 (degreeAt quotientOrder     ceilRatio )
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8_3
noncomputable section
open P1 (K I node)
open P1_7_8 (Input ResidueLift Factors)
open K1_14 (FX Equation Seeds atX graphEval seedEmbedding)
open K1_14_6_1 (Dx partialX flatten)
open Polynomial (eval₂RingHom)
abbrev JetRing := Polynomial Equation
instance jetCommRing : CommRing JetRing := @AddMonoidAlgebra.commRing Equation ℕ inferInstance _
abbrev Degree := ℕ × ℕ × ℕ
def nefDegree (h t s : ℕ) : Degree := (h + 2*t, t, s)
abbrev CoxVar := Fin 2 ⊕ (Fin 2 ⊕ Fin 3)
abbrev Cox := MvPolynomial CoxVar FX
def coxWeight : CoxVar → Degree
  | .inl _ => (1, 0, 0)
  | .inr (.inl i) => (2*i.val, 1, 0)
  | .inr (.inr _) => (0, 0, 1)
def ordinate : JetRing := Polynomial.C Polynomial.X
def seedVar (i : Fin 2) : JetRing :=
  Polynomial.C (Polynomial.C (MvPolynomial.X i))
def affineCoord : CoxVar → JetRing
  | .inl i => if i = 0 then 1 else ordinate
  | .inr (.inl i) => if i = 0 then 1 else Polynomial.X
  | .inr (.inr i) => if hi : i.val < 2 then seedVar ⟨i.val, hi⟩ else 1
def dehom : Cox →ₐ[FX] JetRing := MvPolynomial.aeval affineCoord
structure RelativeSection (Q : Ideal JetRing) (d : Degree) where
  order : ℕ
  finiteChart : Cox
  inverseChart : Cox
  finite_degree :
    finiteChart.IsWeightedHomogeneous coxWeight (d + order • (1, 0, 0))
  inverse_degree :
    inverseChart.IsWeightedHomogeneous coxWeight (d + order • (1, 0, 0))
  glue : ordinate ^ order * dehom finiteChart - dehom inverseChart ∈ Q
def RelativeSection.affine {Q : Ideal JetRing} {d : Degree}
    (S : RelativeSection Q d) : JetRing :=
  dehom S.finiteChart
def gradedPiece (Q : Ideal JetRing) (d : Degree) : Submodule FX (JetRing ⧸ Q) :=
  (MvPolynomial.weightedHomogeneousSubmodule FX coxWeight d).map
    (((Ideal.Quotient.mkₐ FX Q).comp dehom).toLinearMap)
structure CurveProbe (Q : Ideal JetRing) where
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
  offset : ℤ
  threshold : ℕ
  hilbert : ∀ h t s, threshold ≤ h → threshold ≤ t → threshold ≤ s →
    (Module.finrank FX (gradedPiece Q (nefDegree h t s)) : ℤ) =
      (h*fiber + t*tangent + s*seed : ℕ) + offset
def markRoot (J : Input) (γ : K) : Equation →+* FX :=
  eval₂RingHom (graphEval (J.model.label γ)) (atX (J.family.scalar γ))
def markPoint (J : Input) (γ : K) : JetRing →ₐ[FX] FX where
  toRingHom := eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ)))
  commutes' a := by
    change (eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ))))
      (Polynomial.C (Polynomial.C (MvPolynomial.C a))) = a
    simp [markRoot, graphEval]
def tangentEquation (f : Equation) : JetRing :=
  Polynomial.C (MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten f))) +
    Polynomial.X * Polynomial.C f.derivative
def rootIdeal {J : Input} {B : ResidueLift J} (D : Factors J B) : Ideal JetRing :=
  Ideal.span {Polynomial.C D.proper}
def residueInJet {J : Input} (B : ResidueLift J) : JetRing :=
  Polynomial.C (Polynomial.C (P1_7_8.liftSeeds B.denominator))
def openFactor (J : Input) (B : ResidueLift J) : JetRing :=
  residueInJet B * Polynomial.C J.f.derivative
def saturate (Q : Ideal JetRing) (g : JetRing) : Ideal JetRing where
  carrier := {f | ∃ n : ℕ, g^n * f ∈ Q}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f h ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m+n, ?_⟩
    rw [mul_add, pow_add]
    have hf : g^m * g^n * f = g^n * (g^m * f) := by ring
    have hh : g^m * g^n * h = g^m * (g^n * h) := by ring
    rw [hf, hh]
    exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
  smul_mem' := by
    rintro a f ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change g^n * (a * f) ∈ Q
    rw [show g^n * (a*f) = a * (g^n*f) by ring]
    exact Q.mul_mem_left _ hn
def graphIdeal (J : Input) (B : ResidueLift J) (D : Factors J B) : Ideal JetRing :=
  saturate (Ideal.span {Polynomial.C D.proper, tangentEquation J.f}) (openFactor J B)
structure TangentSection (J : Input) {B : ResidueLift J} (D : Factors J B) where
  section_ : RelativeSection (rootIdeal D) (J.e, 1, J.v)
  affine_eq : section_.affine = tangentEquation J.f
def jetDegree (J : Input) (r : ℕ) : Degree :=
  nefDegree (1 + (J.e-3)*r) r (r*J.v + 2*J.w)
def jetDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  residueInJet B * Polynomial.C J.f.derivative ^ (r-1)
def oldDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (P1_7_8.quotientDenominator J B r))
def oldNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (P1_7_8.quotientNumerator J B r))
structure TaylorSections (J : Input) (B : ResidueLift J) (D : Factors J B) (r : ℕ) where
  denominator : RelativeSection (graphIdeal J B D) (jetDegree J r)
  numerator : Fin (r+1) → RelativeSection (graphIdeal J B D) (jetDegree J r)
  den_eq : denominator.affine = jetDenominator J B r
  agrees : ∀ j : Fin (r+1),
    oldDenominator J B j.val * (numerator j).affine -
      oldNumerator J B j.val * denominator.affine ∈ graphIdeal J B D
structure CurveMarks (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime : Ideal JetRing
  isPrime : prime.IsPrime
  onGraph : graphIdeal J B D ≤ prime
  onCutoff : Polynomial.C (P1_7_8.cutoff J B) ∈ prime
  regular : openFactor J B ∉ prime
  marks : Finset K
  sub : marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker (markPoint J γ).toRingHom
structure CurveSlice (J : Input) (B : ResidueLift J) (D : Factors J B)
    extends CurveMarks J B D where
  probe : CurveProbe prime
  positive_seed : 0 < probe.seed
open scoped BigOperators
structure MixedCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count : ℕ
  curves : Fin count → CurveSlice J B D
  covers : ∀ γ ∈ J.marks, P1_7_8.rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).probe.fiber ≤
    J.v*P1_7_8.cutSeed J + J.v^2*P1_7_8.cutVelocity J
  tangent : ∑ j, (curves j).probe.tangent ≤
    2*J.e*J.v*P1_7_8.cutSeed J + J.v^2*P1_7_8.cutOrdinate J
  seed : ∑ j, (curves j).probe.seed ≤
    J.e*P1_7_8.cutSeed J + J.v*((2*J.e-2)*P1_7_8.cutVelocity J + P1_7_8.cutOrdinate J)
structure NodeSections {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C : CurveMarks J B D) where
  persistent : Finset I
  hits : ∀ γ ∈ C.marks, ∀ x ∈ persistent,
    (J.family.scalar γ).eval (node x) = J.model.word x
  cuts : ∀ x ∉ persistent,
    ∃ S : RelativeSection C.prime (jetDegree J (J.ell - persistent.card)),
      S.affine ∉ C.prime ∧
      ∀ γ ∈ C.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
        markPoint J γ S.affine = 0
end
end P1_7_8_3
end

end Merged_UpperBranch8

-- merged module UpperBranch4
section Merged_UpperBranch4
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand K p agreement blockLength AnchorModel AnchoredFamily)
open P1_7 (Stage stages terminal fullCutoff degreeAt  fees )
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
abbrev Mass := Fin 4 → ℚ
def massQ (S : Finset (Ideal Ambient)) : Mass := fun k => mass S k
def dotQ (a c : Mass) : ℚ := ∑ k, a k * c k
def capMin (a c : Mass) : Mass := fun k => min (a k) (c k)
def pairMinSeed (s t : Shape) : ℕ := min s.U t.U
def pairMinOrdinate (s t : Shape) : ℕ := min s.B t.B
def sharedBound (s t : Shape) (x z r m : ℕ) (square : Bool) (k : Fin 4) : ℚ :=
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  (highCap x z k : ℚ) / highScale r k +
    (pairCap (residualShape s x z) (residualShape t x z) k : ℚ) / d
def cornerBound (s t : Shape) (r m : ℕ) (square : Bool) (k : Fin 4) : ℚ :=
  let xs := [0, pairMinSeed s t]
  let zMax := pairMinOrdinate s t
  let zs := [0, zMax, min zMax (s.B-s.J), min zMax (t.B-t.J)]
  (xs.flatMap fun x => zs.map fun z => sharedBound s t x z r m square k).foldl max 0
def pairedCap (s t : Shape) (reserve : ℕ) (square : Bool) : Mass :=
  fun k =>
    let m := reserve+1
    (List.range m).foldl
      (fun a r => min a (cornerBound s t (r+1) m square k))
      (cornerBound s t 1 m square k)
def PairedMass : Prop :=
  ∀ (s t : Shape) (r : ℕ) (square : Bool) (P Q : Jet),
    0 < r → r < p → s.B < p → t.B < p → s.U < p → t.U < p →
    s.J ≤ s.B → t.J ≤ t.B → P ≠ 0 → Q ≠ 0 →
    K1_14_3.RowCaps P s → K1_14_3.RowCaps Q t → K1_14_3.NoMovingCommon P Q →
    ∀ (A : FixedPart P s) (B : FixedPart Q t) (S : Finset (Ideal Ambient)),
    (square = true → ∀ I ∈ S, K1_14_2_2.dual I) →
    (∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      K1_14_2_2.orderOn I P (r+1) ∧ K1_14_2_2.orderOn I Q (r+1)) →
    ∀ k, massQ S k ≤ pairedCap s t r square k
def stageAt (b : HighBand) (i : ℕ) : Stage :=
  ((stages b)[i]?).getD ⟨0, terminal b, terminal b⟩
theorem stage_mem {b : HighBand} {i : ℕ} (hi : i < (stages b).length) :
    stageAt b i ∈ stages b := by
  rw [stageAt, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
def introIndices : HighBand → List ℕ
  | .h2370 | .h2390 | .h2420 | .h2440 => List.range' 1 11
  | .h2410 => List.range' 1 9 ++ [11]
  | .h2460 | .h2480 | .h2500 | .h2520 | .h2530 | .h2540 |
    .h2550 | .h2560 | .h2570 | .h2585 | .h2590 | .h2600 | .h2601 | .h2611 |
    .h2621 | .h2640 | .h2670 | .h2700 | .h2750 | .h2800 | .h2900 | .h2950 |
    .h2980 | .h3000 | .h3050 | .h3100 | .h3200 | .h3400 | .h3555 => List.range' 1 8
  | _ => []
def stopIndex : HighBand → ℕ
  | .h4000 => 2
  | .h4800 => 1
  | _ => 0
def degreeVector (s : Shape) : Fin 3 → ℕ := ![s.B, s.J, s.U]
def introWeight (s : Shape) (k : Fin 4) : Fin 3 → ℕ :=
  ![![s.J, s.B-s.J, 0], ![0, s.U, s.J], ![s.U, 0, s.B], ![0, 0, s.U]] k
def introJump (cap old : Fin 3 → ℕ) (s : Shape) (k : Fin 4) : ℕ :=
  ∑ j, (max (old j) (introWeight s k j) - old j) * cap j
def introAccount (b : HighBand) (k : Fin 4) :
    List ℕ → (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ
  | [], cap, old =>
    introJump cap old (stageAt b 0).moving.shape k +
      (![cap 0, cap 2, 2*cap 0*cap 2, cap 2 * cap 2] : Fin 4 → ℕ) k
  | i :: is, cap, old =>
    let s := stageAt b i
    let c := s.free.shape
    introJump cap old c k + introAccount b k is
      (fun j => min (cap j) (degreeVector c j / (s.reserve+1)))
      (fun j => max (old j) (introWeight c k j))
def initialCap (b : HighBand) (k : Fin 4) : ℕ :=
  let s := stageAt b 0
  if (introIndices b).isEmpty then
    (cornerBound s.free.shape s.moving.shape 1 1 false k).floor.toNat
  else introAccount b k (introIndices b) (degreeVector s.free.shape) (fun _ => 0)
def initialE (b : HighBand) : ℕ :=
  if (introIndices b).isEmpty then
    let s := stageAt b 0
    s.free.shape.U * s.moving.shape.U + (pairMinSeed s.free.shape s.moving.shape)^2
  else initialCap b 3
def stageCap (b : HighBand) (i : ℕ) (square : Bool) : Mass :=
  let s := stageAt b i
  pairedCap s.free.shape s.moving.shape s.reserve square
def history (b : HighBand) : ℕ → Mass
  | 0 => fun k => initialCap b k
  | i+1 => capMin (history b i) (stageCap b (i+1) (decide (stopIndex b ≤ i+1)))
def envelope (s : Stage) : Shape :=
  let a := s.free.shape
  let b := s.moving.shape
  let j := max a.J b.J
  ⟨0, max (a.B-a.J) (b.B-b.J) + j, j, max a.U b.U⟩
def running (v : ℕ → Mass) : ℕ → Mass
  | 0 => fun _ => 0
  | i+1 => fun k => max (running v i k) (v i k)
def weightedBill (n : ℕ) (v : ℕ → Mass) (hist : ℕ → Mass) : ℚ :=
  ∑ i ∈ Finset.range n, dotQ (fun k => running v (i+1) k - running v i k) (hist i)
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
structure ODEGuard (B J : ℕ) : Prop where
  bmin : 2 ≤ B
  jpos : 0 < J
  jb : J ≤ B
  small : B < p
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (b : HighBand) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  mass_bound : Fits parents (initialCap b)
  seed : K1_14_3.SeedCover
  seed_le : seed.curve.totalDegree ≤ initialCap b 2
  seed_points : seed.points.card ≤ initialE b
  ordinates : Finset FX
  ordinate_le : ordinates.card ≤ initialCap b 0
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, seed.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    graphEval (M.label γ) content = 0 ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace P1_7_4
noncomputable section
open P1 (HighBand)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass)
open scoped BigOperators Classical
theorem massQ_mono {S T : Finset (Ideal Ambient)} (h : S ⊆ T) (k : Fin 4) :
    massQ S k ≤ massQ T k := by
  exact (Nat.cast_le (α := ℚ)).mpr (K1_14_2_2.mass_mono h k)
theorem massQ_nonneg (S : Finset (Ideal Ambient)) (k : Fin 4) : 0 ≤ massQ S k :=
  Nat.cast_nonneg _
theorem massQ_split {S T : Finset (Ideal Ambient)} (h : T ⊆ S) (k : Fin 4) :
    massQ (S \ T) k + massQ T k = massQ S k := by
  unfold massQ
  exact_mod_cast (Finset.sum_sdiff h :
    mass (S \ T) k + mass T k = mass S k)
theorem dotQ_nonneg {v c : Mass} (hv : ∀ k, 0 ≤ v k) (hc : ∀ k, 0 ≤ c k) :
    0 ≤ dotQ v c :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hv k) (hc k)
theorem dotQ_mono_mass {v c d : Mass} (hv : ∀ k, 0 ≤ v k) (h : ∀ k, c k ≤ d k) :
    dotQ v c ≤ dotQ v d :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (hv k)
theorem dotQ_mono_weight {v w c : Mass} (hc : ∀ k, 0 ≤ c k) (h : ∀ k, v k ≤ w k) :
    dotQ v c ≤ dotQ w c :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h k) (hc k)
theorem dotQ_scale_add (a h : ℚ) (v w x : Mass) :
    a * dotQ v x + h * dotQ w x = dotQ (fun k => a*v k + h*w k) x := by
  simp only [dotQ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
private theorem running_nonneg (v : ℕ → Mass) (i : ℕ) (k : Fin 4) :
    0 ≤ running v i k := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact ih.trans (le_max_left _ _)
private theorem jump_nonneg (v : ℕ → Mass) (i : ℕ) (k : Fin 4) :
    0 ≤ running v (i+1) k - running v i k :=
  sub_nonneg.mpr (le_max_left _ _)
private theorem running_succ_dot (v : ℕ → Mass) (i : ℕ) (c : Mass) :
    dotQ (running v (i+1)) c = dotQ (running v i) c +
      dotQ (fun k => running v (i+1) k - running v i k) c := by
  unfold dotQ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
private theorem pay_one (v : ℕ → Mass) (hist : ℕ → Mass) (i : ℕ)
    {S T U : Finset (Ideal Ambient)} (hT : T ⊆ S) (hU : U ⊆ S \ T)
    (hcap : ∀ k, massQ S k ≤ hist i k) :
    dotQ (v i) (massQ U) + dotQ (running v (i+1)) (massQ T) ≤
      dotQ (running v i) (massQ S) +
        dotQ (fun k => running v (i+1) k - running v i k) (hist i) := by
  have hleft : dotQ (v i) (massQ U) ≤ dotQ (running v (i+1)) (massQ (S \ T)) :=
    (dotQ_mono_weight (massQ_nonneg U) (fun k => le_max_right _ _)).trans
      (dotQ_mono_mass (running_nonneg v (i+1)) (massQ_mono hU))
  have hsplit :
      dotQ (running v (i+1)) (massQ (S \ T)) + dotQ (running v (i+1)) (massQ T) =
        dotQ (running v (i+1)) (massQ S) := by
    unfold dotQ
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_add, massQ_split hT]
  calc
    _ ≤ _ := add_le_add hleft le_rfl
    _ = _ := hsplit
    _ = _ := running_succ_dot v i _
    _ ≤ _ := add_le_add le_rfl (dotQ_mono_mass (jump_nonneg v i) hcap)
/-- Unspent weight on the final components is available for their terminal count. -/
theorem bill_bound_with_final (n : ℕ) (v hist : ℕ → Mass)
    (live lost : ℕ → Finset (Ideal Ambient))
    (next : ∀ i < n, live (i+1) ⊆ live i)
    (fail : ∀ i < n, lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k, massQ (live i) k ≤ hist i k) :
    (∑ i ∈ Finset.range n, dotQ (v i) (massQ (lost i))) +
      dotQ (running v n) (massQ (live n)) ≤ weightedBill n v hist := by
  induction n with
  | zero => simp [running, dotQ, weightedBill]
  | succ n ih =>
    have old := ih (fun i hi => next i (by omega)) (fun i hi => fail i (by omega))
      (fun i hi => cap i (by omega))
    have step := pay_one v hist n (next n (by omega)) (fail n (by omega)) (cap n (by omega))
    unfold weightedBill at old ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

theorem final_credit_nonneg (n : ℕ) (v : ℕ → Mass) (S : Finset (Ideal Ambient)) :
    0 ≤ dotQ (running v n) (massQ S) :=
  dotQ_nonneg (running_nonneg v n) (massQ_nonneg S)

theorem bill_bound (n : ℕ) (v hist : ℕ → Mass)
    (live lost : ℕ → Finset (Ideal Ambient))
    (next : ∀ i < n, live (i+1) ⊆ live i)
    (fail : ∀ i < n, lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k, massQ (live i) k ≤ hist i k) :
    (∑ i ∈ Finset.range n, dotQ (v i) (massQ (lost i))) ≤ weightedBill n v hist := by
  have h := bill_bound_with_final n v hist live lost next fail cap
  exact (le_add_of_nonneg_right (dotQ_nonneg (running_nonneg v n) (massQ_nonneg _))).trans h
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand AnchorModel AnchoredFamily K p agreement)
open P1_7 (Stage    stages terminal fullCutoff buffered )
open K1_14 (Shape Banks Jet Equation jetAt seedHasse seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField
  JetSeedSection JetYSection ODE)
open K1_14_2_2 (Active dual orderOn FixedPart ODECaps fixedOn RowCaps CutCover
  sectionDegree weight dot joinCuts joinCuts_cost sum_dot emptyCut mass)
open K1_14_2_2_3
open K1_14_2_2_7
open K1_14_2_2_3 (specialize_shiftedWord shift_word)
open K1_14_2_2_7 (seed_value_eq)
open K1_14_2_2_5 (parent_caps)
open scoped BigOperators Classical
abbrev StageIndex (b : HighBand) := Fin (stages b).length
def pairAt {b h rows} (pairs : P1_7.Pairs b h rows) (i : StageIndex b) :
    P1_7.BufferedPair h rows (stageAt b i) :=
  pairs _ (stage_mem i.isLt)
structure FixedRows {b h rows} (pairs : P1_7.Pairs b h rows) (i : StageIndex b) where
  free : FixedPart (pairAt pairs i).free (stageAt b i).free.shape
  moving : FixedPart (pairAt pairs i).moving (stageAt b i).moving.shape
theorem rank_equation (S : Finset (Ideal Ambient))
    (hS : ∀ I ∈ S, Active I ∧ ¬ dual I) {B J : ℕ}
    (hord : mass S 1 ≤ J) (hmix : mass S 2 ≤ B) :
    ∃ G : ODE, ODECaps G B J ∧ ∀ I ∈ S, fixedOn G I := by
  have hchoose (I : Ideal Ambient) :
      ∃ G : ODE, I ∈ S → ODECaps G (sectionDegree I 2) (sectionDegree I 1) ∧ fixedOn G I := by
    by_cases hI : I ∈ S
    · obtain ⟨G, hg⟩ := parent_caps K1_14_2_2_5_1.proof K1_14_2_2_5_2.proof
        (hS I hI).1 (hS I hI).2
      exact ⟨G, fun _ => hg⟩
    · exact ⟨1, fun h => (hI h).elim⟩
  choose G hG using hchoose
  have hp := K1_14_2_2_5.product_caps S G (fun I => sectionDegree I 2)
    (fun I => sectionDegree I 1) (fun I hI => (hG I hI).1)
  exact ⟨∏ I ∈ S, G I, ⟨hp.1, hp.2.1.trans hord, fun j i h => (hp.2.2 j i h).trans hmix⟩,
    fun I hI => K1_14_2_2_5.product_fixedOn hI G (hG I hI).2⟩
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand AnchorModel AnchoredFamily K p)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength
  yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped BigOperators Classical
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1500000
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand K p AnchorModel AnchoredFamily)
open P1_7 ( stages terminal   PrefixBooks PrefixInventory fees)
open K1_14 (Jet Banks seedHasse jetAt atX graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (FixedPart ODECaps fixedOn dual)
open K1_14_3 (SeedCover Surface RowCaps NoMovingCommon)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open scoped BigOperators Classical
def c2 : Prop := PairedMass
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace P1_7_4_2
noncomputable section
open P1 (p)
open P1_7_4 (massQ sharedBound)
open K1_14 (Jet Shape)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 K1_14_2_2_4 Polynomial
open scoped Classical
open K1_14_2_2_4 (cancel_fixed)
open K1_14_2_2_4_1 (factor_caps)
private theorem cancellation : K1_14_2_2_4.c3 :=
  K1_14_2_2_4_3.of_children K1_14_2_2_4_3_1.proof K1_14_2_2_4_3_2.proof
theorem sections : K1_14_2_2_4.c5 :=
  K1_14_2_2_4_5.of_children K1_14_2_2_4_5_1.proof K1_14_2_2_4_5_2.proof
    K1_14_2_2_4_5_3.proof K1_14_2_2_4_5_4.proof K1_14_2_2_4_5_5.proof
private theorem scaled_le_div {d m c : ℕ} (hd : 0 < d) (h : d * m ≤ c) :
    (m : ℚ) ≤ (c : ℚ) / (d : ℚ) := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℚ) < (d : ℚ))).mpr
  rw [mul_comm]
  exact_mod_cast h
private theorem paired_stage {s t : Shape} {P Q : Jet} {A : FixedPart P s} {B : FixedPart Q t}
    (G : P0_10R_2.SharedGcd A B) (S : Finset (Ideal Ambient)) (square : Bool)
    (m r : ℕ) (k : Fin 4) (hr : 0 < r) (hrm : r ≤ m)
    (hx : seedDegree G.ordinary < p) (hz : G.ordinary.natDegree < p)
    (hdual : square = true → ∀ I ∈ S, dual I)
    (hpass : ∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧ orderOn I P m ∧ orderOn I Q m) :
    massQ S k ≤ sharedBound s t (seedDegree G.ordinary) G.ordinary.natDegree r m square k := by
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < d := by
    unfold d
    split
    · exact Nat.pow_pos hn
    · exact hn
  have hg : 0 < highScale r k := by
    fin_cases k <;> first | exact hr | exact Nat.pow_pos hr
  have hh : highScale r k * mass (S.filter (HighOn G.ordinary r)) k ≤ highCap x z k := by
    apply K1_14_2_2R.high_graph_mass K1_14_2_2_4_4.proof sections G.ordinary P Q
      _ r G.ordinary_ne hz hr
    · refine ⟨fixedIncl A.equation * G.left, G.left_factor.trans ?_⟩
      ring
    · refine ⟨fixedIncl B.equation * G.right, G.right_factor.trans ?_⟩
      ring
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    exact ⟨(hpass I hm).1, (hpass I hm).2.1, hf⟩
  have hl : d * mass (S.filter fun I => ¬ HighOn G.ordinary r I) k ≤
      pairCap (residualShape s x z) (residualShape t x z) k := by
    apply sections G.left G.right _ _ _ k d G.left_ne G.right_ne G.relativelyPrime
      (min_le_right _ _) (min_le_right _ _) G.left_caps G.right_caps hd
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨ha, _, hA, hB, hP, hQ⟩ := hpass I hm
    rw [G.left_factor] at hP
    rw [G.right_factor] at hQ
    have hlP := cancellation G.ordinary G.left I m r G.ordinary_ne hx hz ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hA hP)
    have hlQ := cancellation G.ordinary G.right I m r G.ordinary_ne hx hz ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hB hQ)
    have hlen := K1_14_2_2_4_4.proof G.left G.right I ha n hn hlP hlQ
    refine ⟨ha, fun hdegree => ?_⟩
    by_cases hIdual : dual I
    · rw [ite_eq_left hIdual] at hlen
      apply le_trans _ hlen
      apply Nat.cast_le.mpr
      unfold d
      split
      · exact le_rfl
      · simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
    · have hs : square = false := Bool.eq_false_iff.mpr fun he => hIdual (hdual he I hm)
      have hk : k ≠ 3 := fun he => hIdual (show 0 < sectionDegree I 3 by
        rw [← he]
        exact Nat.pos_of_ne_zero hdegree)
      simpa [d, hs, hk, hIdual] using hlen
  have hadd : mass (S.filter (HighOn G.ordinary r)) k +
      mass (S.filter fun I => ¬ HighOn G.ordinary r I) k = mass S k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (mass S k : ℚ) ≤ (highCap x z k : ℚ) / highScale r k +
    (pairCap (residualShape s x z) (residualShape t x z) k : ℚ) / d
  rw [← hadd, Nat.cast_add]
  exact add_le_add (scaled_le_div hg hh) (scaled_le_div hd hl)
theorem paired_thresholds (s t : Shape) (m : ℕ) (square : Bool) (P Q : Jet)
    (hsB : s.B < p) (hsU : s.U < p) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPs : RowCaps P s) (hQt : RowCaps Q t) (hno : K1_14_3.NoMovingCommon P Q)
    (A : FixedPart P s) (B : FixedPart Q t) (S : Finset (Ideal Ambient))
    (hdual : square = true → ∀ I ∈ S, dual I)
    (hpass : ∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧ orderOn I P m ∧ orderOn I Q m) :
    ∃ x ≤ P1_7_4.pairMinSeed s t, ∃ z ≤ P1_7_4.pairMinOrdinate s t,
      ∀ r, 0 < r → r ≤ m → ∀ k, massQ S k ≤ sharedBound s t x z r m square k := by
  obtain ⟨G⟩ := P0_10R_2.sharedGcd A B hP hQ hPs hQt hno
  obtain ⟨hU, hB, _⟩ := factor_caps hQ G.ordinary_ne hQt G.right_factor
  refine ⟨seedDegree G.ordinary, le_min G.seed_le hU, G.ordinary.natDegree,
    le_min G.ordinate_le hB, ?_⟩
  intro r hr hrm k
  exact paired_stage G S square m r k hr hrm (G.seed_le.trans_lt hsU)
    (G.ordinate_le.trans_lt hsB) hdual hpass
end
end P1_7_4_2
end
section
set_option maxHeartbeats 1000000
namespace P1_7_4_2
noncomputable section
open P1_7_4 (pairMinSeed pairMinOrdinate cornerBound sharedBound)
open K1_14 (Shape)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
private theorem at_endpoints {F : ℕ → ℚ} {l x u : ℕ} {a b c M : ℚ}
    (hl : l ≤ x) (hu : x ≤ u) (ha : 0 ≤ a)
    (hF : ∀ y, l ≤ y → y ≤ u → F y = a * (y : ℚ)^2 + b * (y : ℚ) + c)
    (hL : F l ≤ M) (hU : F u ≤ M) : F x ≤ M := by
  have hl' : (l : ℚ) ≤ x := by exact_mod_cast hl
  have hu' : (x : ℚ) ≤ u := by exact_mod_cast hu
  have hchord := mul_nonneg ha (mul_nonneg (sub_nonneg.mpr hl') (sub_nonneg.mpr hu'))
  rw [hF x hl hu]
  rw [hF l le_rfl (hl.trans hu)] at hL
  rw [hF u (hl.trans hu) le_rfl] at hU
  by_cases hs : 0 ≤ a * ((l : ℚ) + u) + b
  · have h := mul_nonneg hs (sub_nonneg.mpr hu')
    linarith only [hU, hchord, h]
  · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hl')
    linarith only [hL, hchord, h]
private def sectionBound (s t : Shape) (a b : ℚ) (k : Fin 4) (x z : ℕ) : ℚ :=
  a * (highCap x z k : ℚ) + b * (pairCap (residualShape s x z) (residualShape t x z) k : ℚ)
private theorem cast_trapezoid (B C J E : ℕ) (hJ : J ≤ B) :
    ((B * E + C * J - J * E : ℕ) : ℚ) =
      (B : ℚ) * E + (C : ℚ) * J - (J : ℚ) * E := by
  have h := (Nat.mul_le_mul_right E hJ).trans (Nat.le_add_right (B * E) (C * J))
  simp only [Nat.cast_sub h, Nat.cast_add, Nat.cast_mul]
private theorem seed_endpoints (s t : Shape) {a b M : ℚ} (hb : 0 ≤ b)
    {x z : ℕ} (hz : z ≤ pairMinOrdinate s t) (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B)
    (h0 : sectionBound s t a b 0 0 0 ≤ M)
    (hZ : sectionBound s t a b 0 0 (pairMinOrdinate s t) ≤ M)
    (hC : sectionBound s t a b 0 0 (min (s.B-s.J) (t.B-t.J)) ≤ M) :
    sectionBound s t a b 0 x z ≤ M := by
  let C := min (s.B-s.J) (t.B-t.J)
  let limit := pairMinOrdinate s t
  let F (y : ℕ) := sectionBound s t a b 0 0 y
  have hcS : C ≤ s.B-s.J := min_le_left _ _
  have hcT : C ≤ t.B-t.J := min_le_right _ _
  change F z ≤ M
  by_cases hlow : z ≤ C
  · refine at_endpoints (F := F) (l := 0) (u := C) (a := 0)
      (b := a - b * ((s.J : ℚ) + t.J))
      (c := b * ((s.B : ℚ) * t.J + (t.B : ℚ) * s.J - (s.J : ℚ) * t.J))
      (Nat.zero_le z) hlow le_rfl ?_ h0 hC
    intro y _ hy
    have hsj : s.J ≤ s.B-y := by omega
    have htj : t.J ≤ t.B-y := by omega
    change a * (y : ℚ) + b * (((s.B-y) * min t.J (t.B-y) +
      (t.B-y) * min s.J (s.B-y) - min s.J (s.B-y) * min t.J (t.B-y) : ℕ) : ℚ) = _
    rw [min_eq_left hsj, min_eq_left htj, cast_trapezoid _ _ _ _ hsj,
      Nat.cast_sub (show y ≤ s.B by omega), Nat.cast_sub (show y ≤ t.B by omega)]
    ring
  · refine at_endpoints (F := F) (l := C) (u := limit) (a := b)
      (b := a - b * ((s.B : ℚ) + t.B)) (c := b * (s.B : ℚ) * t.B)
      (by omega) hz hb ?_ hC hZ
    intro y hy hyZ
    have hyS := hyZ.trans (min_le_left s.B t.B)
    have hyT := hyZ.trans (min_le_right s.B t.B)
    change a * (y : ℚ) + b * (((s.B-y) * min t.J (t.B-y) +
      (t.B-y) * min s.J (s.B-y) - min s.J (s.B-y) * min t.J (t.B-y) : ℕ) : ℚ) = _
    rw [cast_trapezoid _ _ _ _ (min_le_right _ _)]
    rcases min_choice (s.B-s.J) (t.B-t.J) with hc | hc
    · have hj : s.B-y ≤ s.J := by change min (s.B-s.J) (t.B-t.J) ≤ y at hy; omega
      rw [min_eq_right hj, Nat.cast_sub hyS, Nat.cast_sub hyT]
      ring
    · have hj : t.B-y ≤ t.J := by change min (s.B-s.J) (t.B-t.J) ≤ y at hy; omega
      rw [min_eq_right hj, Nat.cast_sub hyS, Nat.cast_sub hyT]
      ring
private theorem ordinate_endpoints (s t : Shape) {a b M : ℚ} (hb : 0 ≤ b)
    {x z : ℕ} (hx : x ≤ pairMinSeed s t) (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B)
    (h0 : sectionBound s t a b 1 0 0 ≤ M)
    (hX : sectionBound s t a b 1 (pairMinSeed s t) 0 ≤ M) :
    sectionBound s t a b 1 x z ≤ M := by
  have hmono : sectionBound s t a b 1 x z ≤ sectionBound s t a b 1 x 0 := by
    change a * (x : ℚ) + b * (((s.U-x) * min t.J (t.B-z) +
      (t.U-x) * min s.J (s.B-z) : ℕ) : ℚ) ≤ a * (x : ℚ) +
      b * (((s.U-x) * min t.J (t.B-0) + (t.U-x) * min s.J (s.B-0) : ℕ) : ℚ)
    simp only [Nat.sub_zero, min_eq_left hsJ, min_eq_left htJ]
    apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hb)
    exact_mod_cast Nat.add_le_add (Nat.mul_le_mul_left _ (min_le_left _ _))
      (Nat.mul_le_mul_left _ (min_le_left _ _))
  apply hmono.trans
  refine at_endpoints (F := fun y => sectionBound s t a b 1 y 0)
    (l := 0) (u := pairMinSeed s t) (a := 0)
    (b := a - b * ((t.J : ℚ) + s.J)) (c := b * ((s.U : ℚ) * t.J + (t.U : ℚ) * s.J))
    (Nat.zero_le x) hx le_rfl ?_ h0 hX
  intro y _ hy
  change a * (y : ℚ) + b * (((s.U-y) * min t.J (t.B-0) +
    (t.U-y) * min s.J (s.B-0) : ℕ) : ℚ) = _
  simp only [Nat.sub_zero, min_eq_left hsJ, min_eq_left htJ, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
    Nat.cast_sub (hy.trans (min_le_right s.U t.U))]
  ring
private theorem mixed_endpoints (s t : Shape) {a b M : ℚ} {x z : ℕ}
    (hx : x ≤ pairMinSeed s t) (hz : z ≤ pairMinOrdinate s t)
    (hC : ∀ y, (y = 0 ∨ y = pairMinSeed s t) → ∀ w,
      (w = 0 ∨ w = pairMinOrdinate s t) → sectionBound s t a b 2 y w ≤ M) :
    sectionBound s t a b 2 x z ≤ M := by
  have hform (y w : ℕ) (hy : y ≤ pairMinSeed s t) (hw : w ≤ pairMinOrdinate s t) :
      sectionBound s t a b 2 y w =
        a * (2 * (y : ℚ) * (w : ℚ)) +
          b * (((s.U : ℚ)-y) * ((t.B : ℚ)-w) + ((t.U : ℚ)-y) * ((s.B : ℚ)-w)) := by
    change a * ((2*y*w : ℕ) : ℚ) +
      b * (((s.U-y) * (t.B-w) + (t.U-y) * (s.B-w) : ℕ) : ℚ) = _
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
      Nat.cast_sub (hy.trans (min_le_right s.U t.U)),
      Nat.cast_sub (hw.trans (min_le_left s.B t.B)),
      Nat.cast_sub (hw.trans (min_le_right s.B t.B))]
  have hxCorner (y : ℕ) (hy : y = 0 ∨ y = pairMinSeed s t) :
      sectionBound s t a b 2 y z ≤ M := by
    have hy' : y ≤ pairMinSeed s t := hy.elim (fun h => h ▸ Nat.zero_le _) (fun h => h ▸ le_rfl)
    refine at_endpoints (F := sectionBound s t a b 2 y)
      (l := 0) (u := pairMinOrdinate s t) (a := 0)
      (b := 2 * a * y - b * (((s.U : ℚ)-y) + ((t.U : ℚ)-y)))
      (c := b * (((s.U : ℚ)-y) * t.B + ((t.U : ℚ)-y) * s.B))
      (Nat.zero_le z) hz le_rfl ?_ (hC y hy 0 (Or.inl rfl)) (hC y hy _ (Or.inr rfl))
    intro w _ hw
    rw [hform y w hy' hw]
    ring
  refine at_endpoints (F := fun y => sectionBound s t a b 2 y z)
    (l := 0) (u := pairMinSeed s t) (a := 0)
    (b := 2 * a * z - b * (((t.B : ℚ)-z) + ((s.B : ℚ)-z)))
    (c := b * ((s.U : ℚ) * ((t.B : ℚ)-z) + (t.U : ℚ) * ((s.B : ℚ)-z)))
    (Nat.zero_le x) hx le_rfl ?_ (hxCorner 0 (Or.inl rfl)) (hxCorner _ (Or.inr rfl))
  intro y _ hy
  rw [hform y z hy hz]
  ring
private theorem jet_endpoints (s t : Shape) {a b M : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {x z : ℕ} (hx : x ≤ pairMinSeed s t)
    (h0 : sectionBound s t a b 3 0 0 ≤ M)
    (hX : sectionBound s t a b 3 (pairMinSeed s t) 0 ≤ M) :
    sectionBound s t a b 3 x z ≤ M := by
  change sectionBound s t a b 3 x 0 ≤ M
  refine at_endpoints (F := fun y => sectionBound s t a b 3 y 0)
    (l := 0) (u := pairMinSeed s t) (a := a+b)
    (b := -b * ((s.U : ℚ) + t.U)) (c := b * (s.U : ℚ) * t.U)
    (Nat.zero_le x) hx (add_nonneg ha hb) ?_ h0 hX
  intro y _ hy
  change a * ((y*y : ℕ) : ℚ) + b * (((s.U-y) * (t.U-y) : ℕ) : ℚ) = _
  simp only [Nat.cast_mul, Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
    Nat.cast_sub (hy.trans (min_le_right s.U t.U))]
  ring
private theorem foldMax_ge {w : ℚ} (L : List ℚ) (init : ℚ)
    (h : w ≤ init ∨ w ∈ L) : w ≤ L.foldl max init := by
  induction L generalizing init with
  | nil => exact h.resolve_right List.not_mem_nil
  | cons v L ih =>
    apply ih
    rcases h with h | h
    · exact Or.inl (h.trans (le_max_left _ _))
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (le_max_right _ _)
      · exact Or.inr h
private def ordinateCorners (s t : Shape) : List ℕ :=
  [0, pairMinOrdinate s t, min (pairMinOrdinate s t) (s.B-s.J),
    min (pairMinOrdinate s t) (t.B-t.J)]
private theorem first_break_mem (s t : Shape) :
    min (s.B-s.J) (t.B-t.J) ∈ ordinateCorners s t := by
  let c := min (s.B-s.J) (t.B-t.J)
  have hc : c ≤ pairMinOrdinate s t :=
    le_min ((min_le_left _ _).trans (Nat.sub_le ..)) ((min_le_right _ _).trans (Nat.sub_le ..))
  rcases min_choice (s.B-s.J) (t.B-t.J) with h | h
  · have he := min_eq_right (show s.B-s.J ≤ pairMinOrdinate s t from h ▸ hc)
    simp [ordinateCorners, h, he]
  · have he := min_eq_right (show t.B-t.J ≤ pairMinOrdinate s t from h ▸ hc)
    simp [ordinateCorners, h, he]
theorem shared_le_corner (s t : Shape) {x z r m : ℕ} (square : Bool) (k : Fin 4)
    (hx : x ≤ pairMinSeed s t) (hz : z ≤ pairMinOrdinate s t)
    (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B) :
    sharedBound s t x z r m square k ≤ cornerBound s t r m square k := by
  let a : ℚ := (highScale r k : ℚ)⁻¹
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  let b : ℚ := (d : ℚ)⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hb : 0 ≤ b := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hEq (y w : ℕ) : sharedBound s t y w r m square k = sectionBound s t a b k y w := by
    simp only [sharedBound, sectionBound, a, b, d, n, div_eq_mul_inv, mul_comm]
  have hcorner (y w : ℕ) (hy : y = 0 ∨ y = pairMinSeed s t) (hw : w ∈ ordinateCorners s t) :
      sectionBound s t a b k y w ≤ cornerBound s t r m square k := by
    rw [← hEq]
    apply foldMax_ge
    refine Or.inr (List.mem_flatMap.mpr ⟨y, ?_, List.mem_map.mpr ⟨w, hw, rfl⟩⟩)
    exact hy.elim (fun h => by simp [h]) (fun h => by simp [h])
  rw [hEq]
  have h0 : 0 ∈ ordinateCorners s t := by simp [ordinateCorners]
  have hZ : pairMinOrdinate s t ∈ ordinateCorners s t := by simp [ordinateCorners]
  fin_cases k
  · exact seed_endpoints s t hb hz hsJ htJ (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner 0 _ (Or.inl rfl) hZ) (hcorner 0 _ (Or.inl rfl) (first_break_mem s t))
  · exact ordinate_endpoints s t hb hx hsJ htJ (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner _ 0 (Or.inr rfl) h0)
  · exact mixed_endpoints s t hx hz (fun y hy w hw =>
      hcorner y w hy (hw.elim (fun h => h ▸ h0) (fun h => h ▸ hZ)))
  · exact jet_endpoints s t ha hb hx (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner _ 0 (Or.inr rfl) h0)
end
end P1_7_4_2
end
section
namespace P1_7_4_2
open P1_7_4 (pairedCap cornerBound)
private theorem le_foldMin (v : ℚ) (f : ℕ → ℚ) (L : List ℕ) (init : ℚ)
    (hi : v ≤ init) (h : ∀ j ∈ L, v ≤ f j) :
    v ≤ L.foldl (fun a j => min a (f j)) init := by
  induction L generalizing init with
  | nil => exact hi
  | cons j L ih =>
    exact ih _ (le_min hi (h j (List.mem_cons_self ..)))
      (fun i hii => h i (List.mem_cons_of_mem _ hii))
theorem proof : P1_7_4.c2 := by
  intro s t r square P Q _ _ hsB _ hsU _ hsJ htJ hP hQ hPs hQt hno A B S hdual hpass k
  let m := r + 1
  obtain ⟨x, hx, z, hz, ht⟩ :=
    paired_thresholds s t m square P Q hsB hsU hP hQ hPs hQt hno A B S hdual hpass
  have bound (j : ℕ) (hj : j < m) :
      P1_7_4.massQ S k ≤ cornerBound s t (j+1) m square k :=
    (ht (j+1) (Nat.succ_pos _) hj k).trans (shared_le_corner s t square k hx hz hsJ htJ)
  change _ ≤ pairedCap s t r square k
  unfold pairedCap
  exact le_foldMin _ _ _ _ (bound 0 (Nat.succ_pos _))
    (fun j hj => bound j (List.mem_range.mp hj))
end P1_7_4_2
end
section
namespace P1_7_4_1
noncomputable section
open P1 (HighBand K p AnchorModel AnchoredFamily)
open P1_7_4 (stageAt introIndices initialCap OnParent)
open K1_14 (Jet Shape Seeds FX graphEval seedHasse)
open K1_14_2 (Ambient CoordinateRing ODE OnJet fixedAt)
open K1_14_2_2 (Fits RowCaps)
open K1_14_2_2_2 (FiniteSections residualBudget afterGcd ordinaryBudget)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open scoped BigOperators
def SectionGeometry (S : Finset (Ideal Ambient)) : Prop :=
  ∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧ FiniteSections I
structure AffineCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (b : HighBand) (G H : ODE) where
  components : Finset (Ideal Ambient)
  geometry : SectionGeometry components
  fits : Fits components (initialCap b)
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, graphEval (M.label γ) content = 0 ∨
    fixedAt G (F.scalar γ) = 0 ∨ fixedAt H (F.scalar γ) = 0 ∨
      ∃ I ∈ components, OnParent F I γ
def factorDegree (D : Jet) : Fin 3 → ℕ :=
  ![jetDegree D, D.natDegree, seedDegree D]
def factorMass (D : Finset Jet) (j : Fin 3) : ℕ :=
  ∑ f ∈ D, factorDegree f j
def IntroHasse : Prop :=
  ∀ (s : Shape) (P : Jet), RowCaps P s →
    ∀ j a, RowCaps (seedHasse j a P) s
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace P1_7_4_1
noncomputable section
open P1 (K p HighBand AnchorModel AnchoredFamily)
open P1_7_4 (stageAt initialCap initialE  InitialCover OnParent)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover joinCovers joinCovers_degree joinCovers_points joinCovers_covers)
open scoped BigOperators Classical
open P0_10R_1 (section_bound seed_projection component_height ordinary_cover)
theorem proper_cover {P Q : Jet} (hp : ProperPair P Q) {s t : Shape}
    (hs : s.J ≤ s.B) (ht : t.J ≤ t.B) (hP : RowCaps P s) (hQ : RowCaps Q t) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (residualBudget s t) ∧
      ∀ z R, jetAt P z R = 0 → jetAt Q z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨S, hS, hcover⟩ := K1_14_2_2_2_3.proof _ _ hp
  obtain ⟨hfinite, hfits⟩ := section_bound _ _ hp s t hs ht hP hQ S hS
  refine ⟨S, ?_, hfits, hcover⟩
  intro I hI
  obtain ⟨hprime, hdim, hrow, hcut⟩ := hS I hI
  exact ⟨hprime, hdim, component_height hp hprime hdim hrow hcut, hfinite I hI⟩
theorem ordinary_component_cover (f : Equation) (hi : Irreducible f)
    (hd : 0 < f.natDegree) (hp : f.natDegree < p) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨S, hS, hf, hc⟩ := ordinary_cover f hi hd hp
  exact ⟨S, fun I hI => ⟨(hS I hI).1, (hS I hI).2.1, (hS I hI).2.2.1,
    (hS I hI).2.2.2.1⟩, hf, hc⟩
theorem collect {α : Type*} (D : Finset α)
    (budget : α → Fin 4 → ℕ) (T : α → K → (Polynomial K) → Prop)
    (h : ∀ d ∈ D, ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (budget d) ∧
      ∀ z R, T d z R → ∃ I ∈ S, OnJet I z R) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (fun k => ∑ d ∈ D, budget d k) ∧
      ∀ d ∈ D, ∀ z R, T d z R → ∃ I ∈ S, OnJet I z R := by
  classical
  let C (d : α) := if hd : d ∈ D then Classical.choose (h d hd) else ∅
  have hC (d : α) (hd : d ∈ D) :
      SectionGeometry (C d) ∧ Fits (C d) (budget d) ∧
      ∀ z R, T d z R → ∃ I ∈ C d, OnJet I z R := by
    simpa only [C, dite_eq_left hd] using Classical.choose_spec (h d hd)
  refine ⟨D.biUnion C, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨d, hd, hi⟩ := Finset.mem_biUnion.mp hI
    exact (hC d hd).1 I hi
  · intro k
    exact (sum_biUnion_le D C (fun I => sectionDegree I k)).trans
      (Finset.sum_le_sum fun d hd => (hC d hd).2.1 k)
  · intro d hd z R hr
    obtain ⟨I, hI, hone⟩ := (hC d hd).2.2 z R hr
    exact ⟨I, Finset.mem_biUnion.mpr ⟨d, hd, hI⟩, hone⟩
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace P1_7_4_1
noncomputable section
open P1 (K p)
open P1_7_4 (degreeVector)
open K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial UniqueFactorizationMonoid
open K1_14_2_2_2_1 (extractSeed rowCaps_iff jetDegree seedDegree seedDegree_le
  jetDegree_mul seedDegree_mul seedDegree_seed jetDegree_C)
open K1_14_2_1_1 (view exists_view_degree_pos view_seedHasse view_degree_le OtherSeed)
open K1_14_3_2_1 (seedToJet markEval_fixed markEval_seed)
open K1_14_3 (fixedEmbedding)
open scoped BigOperators Classical
open K1_14_2_2_2_1 (seedContent_cap divisor_caps)
open K1_14_2_2_2_1 (exists_fixedIncl)
open K1_14_2_1_1 (dvd_pow_of_dvd_hasse derivative_not_dvd)
structure Stripped {P : Jet} {s : Shape} (A : FixedPart P s) where
  content : Seeds
  row : Jet
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ s.U
  row_ne : row ≠ 0
  row_dvd : row ∣ P
  row_caps : RowCaps row s
  residual_eq : A.residual = C (C content) * row
  primitive : ∀ b : Seeds, C (C b) ∣ row → IsUnit b
  no_fixed : ∀ g : ODE, Irreducible (fixedIncl g) → ¬ fixedIncl g ∣ row
  covers : ∀ z S, jetAt P z S = 0 →
    graphEval z content = 0 ∨ fixedAt A.equation S = 0 ∨ jetAt row z S = 0
theorem strip {P : Jet} {s : Shape} (hP : P ≠ 0) (hc : RowCaps P s) (A : FixedPart P s) :
    Nonempty (Stripped A) := by
  have hr : A.residual ≠ 0 := fun hz => hP (by rw [A.factorization, hz, mul_zero])
  have hd : A.residual ∣ P := ⟨_, A.factorization.trans (mul_comm _ _)⟩
  obtain ⟨a, R, he, hprim⟩ := extractSeed A.residual hr
  have hm : (C (C a) * R : Jet) ≠ 0 := he ▸ hr
  have hR := (show R ∣ A.residual from ⟨_, he.trans (mul_comm _ _)⟩)
  refine ⟨⟨a, R, by simpa using left_ne_zero_of_mul hm,
    seedContent_cap hP hc ((show C (C a) ∣ A.residual from ⟨R, he⟩).trans hd),
    right_ne_zero_of_mul hm, hR.trans hd, divisor_caps hP hc (hR.trans hd),
    he, hprim, fun g hg hgR => A.stripped g hg (hgR.trans hR), ?_⟩⟩
  intro z S h
  have H := congrArg (markEval z S) (A.factorization.trans (congrArg (fixedIncl A.equation * ·) he))
  change markEval z S P = 0 at h
  rw [h, map_mul, map_mul] at H
  change 0 = markEval z S (fixedEmbedding A.equation) *
    (markEval z S (seedToJet a) * markEval z S R) at H
  rw [markEval_fixed, markEval_seed, eq_comm, mul_eq_zero, mul_eq_zero] at H
  rcases H with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
theorem factorDegree_add {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0) (j : Fin 3) :
    factorDegree (P * Q) j = factorDegree P j + factorDegree Q j := by
  fin_cases j
  · exact jetDegree_mul hP hQ
  · exact natDegree_mul hP hQ
  · exact seedDegree_mul hP hQ
private theorem factorDegree_one (j : Fin 3) : factorDegree 1 j = 0 := by
  fin_cases j
  · exact jetDegree_C (1 : Equation) |>.trans natDegree_one
  · exact natDegree_one
  · exact seedDegree_seed (1 : Seeds) |>.trans MvPolynomial.totalDegree_one
theorem factorDegree_pow {P : Jet} (hP : P ≠ 0) (r : ℕ) (j : Fin 3) :
    factorDegree (P ^ r) j = r * factorDegree P j := by
  induction r with
  | zero => simp [factorDegree_one]
  | succ r ih =>
    rw [pow_succ, factorDegree_add (pow_ne_zero _ hP) hP, ih, Nat.succ_mul]
theorem factorDegree_prod {S : Finset Jet} {f : Jet → Jet} (hf : ∀ d ∈ S, f d ≠ 0) (j : Fin 3) :
    factorDegree (∏ d ∈ S, f d) j = ∑ d ∈ S, factorDegree (f d) j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [factorDegree_one]
  | insert d S hd ih =>
    have hS : ∀ e ∈ S, f e ≠ 0 := fun e he => hf e (Finset.mem_insert_of_mem he)
    rw [Finset.prod_insert hd, Finset.sum_insert hd,
      factorDegree_add (hf d (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hS), ih hS]
theorem factorDegree_dvd {P Q : Jet} (hQ : Q ≠ 0) (hd : P ∣ Q) (j : Fin 3) :
    factorDegree P j ≤ factorDegree Q j := by
  obtain ⟨T, rfl⟩ := hd
  rw [factorDegree_add (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)]
  exact Nat.le_add_right _ _
theorem caps_iff (P : Jet) (s : Shape) :
    RowCaps P s ↔ ∀ j, factorDegree P j ≤ degreeVector s j := by
  rw [rowCaps_iff]
  constructor
  · rintro ⟨hB, hJ, hU⟩ j
    fin_cases j <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2⟩
def ownShape (P : Jet) : Shape :=
  ⟨0, factorDegree P 0, factorDegree P 1, factorDegree P 2⟩
theorem own_caps (P : Jet) : RowCaps P (ownShape P) := by
  apply (caps_iff _ _).mpr
  intro j
  fin_cases j <;> exact le_rfl
theorem own_J_le_B {P : Jet} (hP : P ≠ 0) : (ownShape P).J ≤ (ownShape P).B := by
  have hc : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
    rw [coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  exact (Nat.le_add_left _ _).trans ((own_caps P) _ _ hc).1
theorem factorMass_mono {D E : Finset Jet} (h : D ⊆ E) (j : Fin 3) :
    factorMass D j ≤ factorMass E j :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)
structure IntroFactors (P : Jet) (D : Finset Jet) : Prop where
  factors : ∀ f ∈ D, Irreducible f ∧ f ∣ P ∧ UsesSeed f ∧
    f ∉ Set.range seedToJet ∧ f ∉ Set.range fixedEmbedding
  pairwise : (D : Set Jet).Pairwise IsRelPrime
theorem IntroFactors.mono {P : Jet} {D E : Finset Jet} (h : IntroFactors P E) (he : D ⊆ E) :
    IntroFactors P D :=
  ⟨fun f hf => h.factors f (he hf), h.pairwise.mono he⟩
theorem initial_factors {P : Jet} {s : Shape} {A : FixedPart P s} (R : Stripped A) :
    ∃ D : Finset Jet, IntroFactors P D ∧ (∀ j, factorMass D j ≤ degreeVector s j) ∧
      ∀ z S, jetAt R.row z S = 0 → ∃ f ∈ D, jetAt f z S = 0 := by
  classical
  let _ : StrongNormalizationMonoid Jet := UniqueFactorizationMonoid.strongNormalizationMonoid
  let N := normalizedFactors R.row
  let D := N.toFinset
  have hmem (f : Jet) (hf : f ∈ D) : f ∈ N := Multiset.mem_toFinset.mp hf
  have hirr (f : Jet) (hf : f ∈ D) : Irreducible f :=
    irreducible_of_normalized_factor f (hmem f hf)
  have hdvd (f : Jet) (hf : f ∈ D) : f ∣ R.row := dvd_of_mem_normalizedFactors (hmem f hf)
  have hprod : (∏ f ∈ D, f) ∣ R.row :=
    (Multiset.toFinset_prod_dvd_prod N).trans (prod_normalizedFactors R.row_ne).dvd
  refine ⟨D, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro f hf
    have hfix : f ∉ Set.range fixedEmbedding := by
      rintro ⟨g, rfl⟩
      exact R.no_fixed g (hirr _ hf) (hdvd _ hf)
    have hseed : f ∉ Set.range seedToJet := by
      rintro ⟨a, rfl⟩
      exact (hirr _ hf).not_isUnit (isUnit_C.mpr (isUnit_C.mpr (R.primitive a (hdvd _ hf))))
    exact ⟨hirr f hf, (hdvd f hf).trans R.row_dvd,
      by_contra (fun h => hfix (by
        obtain ⟨g, hg⟩ := exists_fixedIncl f h
        exact ⟨g, hg.symm⟩)), hseed, hfix⟩
  · intro f hf g hg hne
    exact (hirr f hf).isRelPrime_iff_not_dvd.mpr fun hd =>
      hne (normalizedFactors_eq_of_dvd R.row f (hmem _ hf) g (hmem _ hg) hd)
  · intro j
    calc
      _ = factorDegree (∏ f ∈ D, id f) j :=
        (factorDegree_prod (f := id) (fun f hf => (hirr f hf).ne_zero) j).symm
      _ ≤ factorDegree R.row j := factorDegree_dvd R.row_ne hprod j
      _ ≤ _ := (caps_iff _ _).mp R.row_caps j
  · intro z S hz
    change markEval z S R.row = 0 at hz
    have hm := map_dvd (markEval z S) (prod_normalizedFactors R.row_ne).symm.dvd
    change markEval z S R.row ∣ markEval z S N.prod at hm
    rw [hz, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hm
    obtain ⟨f, hf, he⟩ := hm
    exact ⟨f, Multiset.mem_toFinset.mpr hf, he⟩
theorem hasse_power {D R : Jet} {s : Shape} (hi : Irreducible D) (hseed : UsesSeed D)
    (hR : R ≠ 0) (hcap : RowCaps R s) (hsmall : s.U < p) {e : ℕ}
    (hall : ∀ i a, a ≤ e → D ∣ seedHasse i a R) : D^(e+1) ∣ R := by
  obtain ⟨i, hpos⟩ := exists_view_degree_pos D hseed
  have hD : D ∣ R := by
    apply (map_dvd_iff (view i)).mp
    simpa only [view_seedHasse, hasseDeriv_zero'] using
      (map_dvd_iff (view i)).mpr (hall i 0 (Nat.zero_le _))
  have hbound : (view i D).natDegree < p :=
    ((natDegree_le_of_dvd ((map_dvd_iff (view i)).mpr hD)
      ((view i).map_ne_zero_iff.mpr hR)).trans
        (view_degree_le i R s.U ((seedDegree_le _ _).mp ((rowCaps_iff _ _).mp hcap).2.2))).trans_lt hsmall
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  let : CharP OtherSeed p := charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 1) FX) p
  have hirr : Irreducible (view i D) := (MulEquiv.irreducible_iff (view i)).mpr hi
  have hprime : Prime (view i D) := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  apply (map_dvd_iff (view i)).mp
  rw [map_pow]
  apply dvd_pow_of_dvd_hasse hprime (derivative_not_dvd _ hpos hbound)
  intro a ha
  rw [← view_seedHasse]
  exact (map_dvd_iff (view i)).mpr (hall i a (Nat.le_of_lt_succ ha))
theorem retained_mass {P R : Jet} {D : Finset Jet} (hD : IntroFactors P D)
    {s : Shape} (hR : R ≠ 0) (hcap : RowCaps R s) (hsmall : s.U < p)
    (e : ℕ) (hall : ∀ f ∈ D, ∀ i a, a ≤ e → f ∣ seedHasse i a R) (j : Fin 3) :
    factorMass D j ≤ degreeVector s j / (e+1) := by
  have hprod : (∏ f ∈ D, f^(e+1)) ∣ R := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro f hf g hg hne
      exact (hD.pairwise hf hg hne).pow_left.pow_right
    · intro f hf
      exact hasse_power (hD.factors f hf).1 (hD.factors f hf).2.2.1 hR hcap hsmall (hall f hf)
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos e)).mpr
  rw [Nat.mul_comm, factorMass, Finset.mul_sum]
  calc
    _ = factorDegree (∏ f ∈ D, f^(e+1)) j := by
      rw [factorDegree_prod (fun f hf => pow_ne_zero _ (hD.factors f hf).1.ne_zero)]
      exact Finset.sum_congr rfl fun f hf =>
        (factorDegree_pow (hD.factors f hf).1.ne_zero _ j).symm
    _ ≤ factorDegree R j := factorDegree_dvd hR hprod j
    _ ≤ _ := (caps_iff _ _).mp hcap j
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P1_7_4_1
noncomputable section
open P1_7_4 (introWeight introJump)
open K1_14 (Jet Shape)
open K1_14_2_2_2 (residualBudget ordinaryBudget)
open scoped BigOperators Classical
def factorTariff (s : Shape) (k : Fin 4) (f : Jet) : ℕ :=
  ∑ j, introWeight s k j * factorDegree f j
def weightedDegree (w : Fin 3 → ℕ) (D : Finset Jet) : ℕ :=
  ∑ j, w j * factorMass D j
theorem weighted_factors (w : Fin 3 → ℕ) (D : Finset Jet) :
    weightedDegree w D = ∑ f ∈ D, ∑ j, w j * factorDegree f j := by
  unfold weightedDegree factorMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
theorem residual_tariff (f : Jet) (s : Shape) (hs : s.J ≤ s.B) (k : Fin 4) :
    residualBudget (ownShape f) s k = factorTariff s k f := by
  fin_cases k
  · simp only [residualBudget, factorTariff, Fin.sum_univ_three, introWeight, ownShape]
    change factorDegree f 0*s.J + s.B*factorDegree f 1 - factorDegree f 1*s.J =
      s.J*factorDegree f 0 + (s.B-s.J)*factorDegree f 1 + 0*factorDegree f 2
    have hm := Nat.mul_le_mul_right (factorDegree f 1) hs
    rw [Nat.mul_comm (factorDegree f 1) s.J, Nat.add_sub_assoc hm, ← Nat.sub_mul]
    ring
  · change _ = ∑ j, introWeight s 1 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.J + s.U*factorDegree f 1 =
      0*factorDegree f 0 + s.U*factorDegree f 1 + s.J*factorDegree f 2
    ring
  · change _ = ∑ j, introWeight s 2 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.B + s.U*factorDegree f 0 =
      s.U*factorDegree f 0 + 0*factorDegree f 1 + s.B*factorDegree f 2
    ring
  · change _ = ∑ j, introWeight s 3 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.U = 0*factorDegree f 0 + 0*factorDegree f 1 + s.U*factorDegree f 2
    ring
theorem tariff_step {D T : Finset Jet} (hT : T ⊆ D) (cap old : Fin 3 → ℕ)
    (s : Shape) (k : Fin 4) (hcap : ∀ j, factorMass D j ≤ cap j) :
    (∑ f ∈ D \ T, factorTariff s k f) +
      weightedDegree (fun j => max (old j) (introWeight s k j)) T ≤
      weightedDegree old D + introJump cap old s k := by
  classical
  let w := fun j => max (old j) (introWeight s k j)
  have hadd (j : Fin 3) : old j + (w j-old j) = w j :=
    Nat.add_sub_of_le (le_max_left _ _)
  calc
    _ ≤ weightedDegree w (D \ T) + weightedDegree w T := by
      apply Nat.add_le_add_right
      rw [weighted_factors]
      exact Finset.sum_le_sum fun f _ =>
        Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (le_max_right _ _)
    _ = weightedDegree w D := by
      simp only [weighted_factors]
      exact Finset.sum_sdiff hT
    _ = weightedDegree old D + ∑ j, (w j-old j) * factorMass D j := by
      unfold weightedDegree
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← Nat.add_mul, hadd]
    _ ≤ _ := Nat.add_le_add_left
      (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (hcap j)) _
theorem ordinary_charge (D : Finset Jet) (cap : Fin 3 → ℕ)
    (hcap : ∀ j, factorMass D j ≤ cap j) (k : Fin 4) :
    (∑ f ∈ D, ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) ≤
      ordinaryBudget (cap 2) (cap 0) k := by
  fin_cases k
  · exact hcap 0
  · exact hcap 2
  · change (∑ f ∈ D, 2 * factorDegree f 2 * factorDegree f 0) ≤ 2 * cap 2 * cap 0
    calc
      _ ≤ ∑ f ∈ D, 2 * factorDegree f 2 * cap 0 := by
        exact Finset.sum_le_sum fun f hf => Nat.mul_le_mul_left _
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans (hcap 0))
      _ = (2 * factorMass D 2) * cap 0 := by rw [factorMass, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hcap 2))
  · change (∑ f ∈ D, factorDegree f 2 * factorDegree f 2) ≤ cap 2 * cap 2
    calc
      _ ≤ ∑ f ∈ D, factorDegree f 2 * cap 2 := by
        exact Finset.sum_le_sum fun f hf => Nat.mul_le_mul_left _
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans (hcap 2))
      _ = factorMass D 2 * cap 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (hcap 2)
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1400000
namespace P1_7_4_1
noncomputable section
open P1 (K p HighBand AnchorModel AnchoredFamily)
open P1_7_4 (stageAt introIndices initialCap  introAccount introJump introWeight degreeVector)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (NoMovingCommon)
open K1_14_2_2_2_1 (jetDegree_C seedDegree_C)
open scoped BigOperators Classical
open K1_14_3_2_1 (ordinary_factor)
theorem irreducible_cut {f C : Jet} (hf : Irreducible f) (hd : ¬ f ∣ C) :
    ProperPair f C :=
  ⟨hf.ne_zero, fun h => hd (h ▸ dvd_zero _), fun _ hD hDf hDC =>
    hd ((hD.associated_of_dvd hf hDf).dvd'.trans hDC)⟩
theorem terminal_piece {P Q : Jet} {t : Shape} {D : Finset Jet}
    (hD : IntroFactors P D) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q t) (hJB : t.J ≤ t.B) (hB : t.B < p) (hQ : Q ≠ 0)
    (f : Jet) (hf : f ∈ D) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      Fits S (fun k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) ∧
      ∀ z R, (jetAt f z R = 0 ∧ jetAt Q z R = 0) → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨hi, hPf, _, hs, hfix⟩ := hD.factors f hf
  by_cases hd : f ∣ Q
  · have hv : f.natDegree = 0 := by
      by_contra h
      exact hfix (hnc f hi hPf hd (Nat.pos_of_ne_zero h))
    obtain ⟨hc, hirr, hpos⟩ := ordinary_factor hi hv hs
    have hdegrees : factorDegree f 0 = (f.coeff 0).natDegree ∧
        factorDegree f 2 = ordinarySeedDegree (f.coeff 0) :=
      ⟨(congrArg K1_14_2_2_2_1.jetDegree hc).symm.trans (jetDegree_C _),
       (congrArg K1_14_2_2_2_1.seedDegree hc).symm.trans (seedDegree_C _)⟩
    have hsmall : (f.coeff 0).natDegree < p := by
      rw [← hdegrees.1]
      exact ((factorDegree_dvd hQ hd 0).trans ((caps_iff _ _).mp hQc 0)).trans_lt hB
    obtain ⟨S, hG, hF, hC⟩ := ordinary_component_cover _ hirr hpos hsmall
    refine ⟨S, hG, fun k => (hF k).trans ?_, fun z R h => hC z R ?_⟩
    · rw [hdegrees.1, hdegrees.2]
      exact Nat.le_add_left _ _
    · have hz := h.1
      rw [← hc] at hz
      simpa [jetAt, atMark] using hz
  · obtain ⟨S, hG, hF, hC⟩ :=
      proper_cover (irreducible_cut hi hd) (own_J_le_B hi.ne_zero) hJB (own_caps f) hQc
    refine ⟨S, hG, fun k => (hF k).trans ?_, fun z R h => hC z R h.1 h.2⟩
    rw [residual_tariff f t hJB]
    exact Nat.le_add_right _ _
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_1
def c2 : Prop := IntroHasse
end P1_7_4_1
end
section
namespace P1_7_4_1_1
open K1_14 (Shape)
open K1_14_2_2_2 (afterGcd residualBudget ordinaryBudget)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
open P1_7_4 (sharedBound stageAt initialCap)
end P1_7_4_1_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_1_2
open K1_14 (FX Seeds Jet seedHasse)
open K1_14_1_3 (translation seedCoeff mapCoeffs mapCoeffs_coeff)
private theorem seedCoeff_totalDegree (i : Fin 2) (r : ℕ) (P : Seeds) :
    (seedCoeff i r P).totalDegree ≤ P.totalDegree := by
  classical
  let g : Fin 2 → MvPolynomial (Option (Fin 2)) FX :=
    fun j => MvPolynomial.X (some j) + if j = i then MvPolynomial.X none else 0
  let f : Seeds →ₐ[FX] MvPolynomial (Option (Fin 2)) FX := MvPolynomial.aeval g
  have htrans : translation i = (MvPolynomial.optionEquivLeft FX (Fin 2)).toAlgHom.comp f := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i <;> simp [translation, f, g, hj]
  have hg (j : Fin 2) : (g j).totalDegree ≤ 1 := by
    by_cases hj : j = i
    · simpa [g, hj] using (MvPolynomial.totalDegree_add
        (MvPolynomial.X (some j) : MvPolynomial (Option (Fin 2)) FX)
        (MvPolynomial.X none))
    · simp [g, hj]
  have hf : (f P).totalDegree ≤ P.totalDegree := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    change (MvPolynomial.aeval g (MvPolynomial.monomial m (P.coeff m))).totalDegree ≤ _
    rw [MvPolynomial.aeval_monomial]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (MvPolynomial.le_totalDegree hm)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) (hg j))
  change ((translation i P).coeff r).totalDegree ≤ _
  rw [htrans]
  exact (MvPolynomial.totalDegree_coeff_optionEquivLeft_le FX (Fin 2) (f P) r).trans hf
private theorem seedHasse_coeff (i : Fin 2) (r : ℕ) (P : Jet) (j k : ℕ) :
    ((seedHasse i r P).coeff j).coeff k = seedCoeff i r ((P.coeff j).coeff k) := by
  change ((mapCoeffs (mapCoeffs (seedCoeff i r)) P).coeff j).coeff k = _
  rw [mapCoeffs_coeff, mapCoeffs_coeff]
theorem proof : P1_7_4_1.c2 := by
  intro s P hP i r j k hc
  rw [seedHasse_coeff] at hc ⊢
  have hsource : (P.coeff j).coeff k ≠ 0 := by
    intro hz
    exact hc (by rw [hz, map_zero])
  obtain ⟨hB, hJ, hU⟩ := hP j k hsource
  exact ⟨hB, hJ, (seedCoeff_totalDegree i r _).trans hU⟩
end P1_7_4_1_2
end
section
namespace P1_7_4_3
noncomputable section
open Polynomial Finset
open P1 (K I node agreement)
open K1_13 (Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_3_6 (totalCap topCap)
def mix (b j : ℕ) (a v : ℚ) : ℚ := (↑(b-j : ℕ) : ℚ) * v + j * a
theorem mix_eq {b j : ℕ} (h : j ≤ b) (a v : ℚ) :
    mix b j a v = (b : ℚ) * v + j * (a-v) := by
  unfold mix
  rw [Nat.cast_sub h]
  ring
theorem cast_mixed {b j a v : ℕ} (h : j ≤ b) (hv : v ≤ a) :
    (MvPolynomial.cappedDegreeMixedVolume b j a v : ℚ) = mix b j a v := by
  rw [MvPolynomial.cappedDegreeMixedVolume_eq h hv, mix]
  push_cast
  rfl
end
end P1_7_4_3
end
section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_3
noncomputable section
open Polynomial PolynomialDifferential
open P1 (K I node p agreement)
open K1_13 (Row Geom extend embed atJet)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14 (seedEmbedding)
open K1_14_3_6 (power totalCap topCap)
open scoped BigOperators
open K1_14_3_6_2 (specialization_flatten eval_at_center)
private theorem solution_taylor {f : Row 2} {S : (Polynomial K)} {d : ℕ}
    (hd : d < p) (hS : RegularAt 1 f (extend S)) :
    MvPolynomial.aeval (marked (extend S)) (initialJetSeparant center (chart f)) ≠ 0 ∧
    ∀ j ≤ d, rationalTaylorCoefficient center (chart f) (marked (extend S)) j =
      (Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
  let P := (extend S).map constants
  have hsol : differentialSpecialization (chart f) P = 0 := by
    change differentialSpecialization (chart f) ((extend S).map constants) = 0
    rw [chart, ← map_differentialSpecialization, K1_14_3_6_2.specialization_flatten, hS.1, Polynomial.map_zero]
  have hsf : differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) (extend S) ≠ 0 := by
    change differentialSpecialization
      (MvPolynomial.pderiv (some 1) ((MvPolynomial.optionEquivRight Geom (Fin 2)).symm f)) _ ≠ 0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]
    exact (K1_14_3_6_2.specialization_flatten (MvPolynomial.pderiv 1 f) _).substr hS.2
  have hsep : jetEvaluation (PolynomialDifferential.separant (chart f) (Fin.last 1))
      center (marked (extend S)) ≠ 0 := by
    change jetEvaluation (PolynomialDifferential.separant (chart f) 1) center (marked (extend S)) ≠ 0
    rw [marked, ← eval_differentialSpecialization, chart, ← map_separant,
      ← map_differentialSpecialization, K1_14_3_6_2.eval_at_center]
    exact fun he => hsf (toCenter_inj (he.trans (map_zero _).symm))
  refine ⟨by rwa [aeval_initialJetSeparant], ?_⟩
  have hcharG : CharP Geom p := charP_of_injective_ringHom embed.injective p
  have : CharP CenterField p := charP_of_injective_ringHom constants.injective p
  have hP : P = S.map seedEmbedding := by
    change (extend S).map constants = _
    rw [Polynomial.map_map]
    rfl
  intro j hj
  rw [← hP]
  refine rationalTaylorCoefficient_eq_solution center (chart f) P hsol hsep j (fun i hi ht => ?_)
  rw [Nat.choose_one_right]
  intro hz
  exact (not_le_of_gt ((ht.trans hj).trans_lt hd))
    (Nat.le_of_dvd (by omega : 0 < i) ((CharP.cast_eq_zero_iff CenterField p i).mp hz))
private theorem short_numerator_bound (f : Row 2) {B J t : ℕ} (hJ : 0 < J)
    (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J) (j : Fin (t+1)) :
    commonTaylorNumerator center (chart f) (power t) j ∈
      MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) := by
  let Q := chart f
  let N := commonTaylorNumerator center Q (power t) j
  have hτ : TaylorExponentSufficient 1 (t+1) (power t) :=
    taylorExponentSufficient_firstOrder_tight t
  have htot : N.totalDegree ≤ totalCap t B :=
    (totalDegree_commonTaylorNumerator_le center Q (hτ j)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1)) 1)
  exact mem_capped _ htot (le_min
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans htot)
    ((degreeOf_commonTaylorNumerator_firstOrder_le center Q J (t+1) (power t) hτ
      ((chart_top f).trans hj) j).trans (Nat.add_le_add_left (Nat.le_of_lt_succ j.isLt) _)))
private theorem short_denominator_bound (f : Row 2) {B J t : ℕ}
    (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J) :
    initialJetSeparant center (chart f) ^ power t ∈
      MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) := by
  let Q := chart f
  let D := initialJetSeparant center Q ^ power t
  have hD₀ : D.totalDegree ≤ totalCap t B :=
    (MvPolynomial.totalDegree_pow _ _).trans ((Nat.mul_le_mul_left _
      ((totalDegree_initialJetSeparant_le center Q).trans
        (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1))).trans (Nat.le_add_left _ _))
  have hD₁ : D.degreeOf 1 ≤ power t * (J-1) :=
    (MvPolynomial.degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _
      ((degreeOf_initialJetSeparant_le center Q).trans
        (Nat.sub_le_sub_right ((chart_top f).trans hj) 1)))
  exact mem_capped D hD₀ (le_min
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans hD₀) (hD₁.trans (Nat.le_add_right _ _)))
theorem short_cut (f : Row 2) {d t B J : ℕ} (hd : d < p) (ht : t ≤ d)
    (hJ : 0 < J) (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (sites : Finset I) (hs : d ≤ sites.card + t) (w : I → K) (i : I) :
    ∃ cut : MvPolynomial (Fin 2) CenterField,
      cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) ∧
      ∀ S : (Polynomial K), S.natDegree ≤ d → RegularAt 1 f (extend S) →
        (∀ j ∈ sites, S.eval (node j) = w j) →
        (MvPolynomial.aeval (marked (extend S)) cut = 0 ↔ S.eval (node i) = w i) := by
  classical
  obtain ⟨c, a, ha⟩ := P1_7_3.interpolation_weights sites d t hs w (node i)
  let Q := chart f
  let D := initialJetSeparant center Q ^ power t
  let N (j : Fin (t+1)) := commonTaylorNumerator center Q (power t) j
  let cut := MvPolynomial.C (c - seedEmbedding (w i)) * D + ∑ j, MvPolynomial.C (a j) * N j
  have hτ : TaylorExponentSufficient 1 (t+1) (power t) :=
    taylorExponentSufficient_firstOrder_tight t
  refine ⟨cut, ?_, ?_⟩
  · dsimp only [cut]
    apply Submodule.add_mem
    · rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (short_denominator_bound f hB hj)
    · apply Submodule.sum_mem
      intro j _
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (short_numerator_bound f hJ hB hj j)
  · intro S hS hreg hnodes
    obtain ⟨hsep, hcoef⟩ := solution_taylor hd hreg
    have hval := ha (S.map seedEmbedding) (Polynomial.natDegree_map_le.trans hS)
      (fun j hj => by rw [Polynomial.eval_map_apply, hnodes j hj])
    change (S.map seedEmbedding).eval (seedEmbedding (node i)) = _ at hval
    rw [Polynomial.eval_map_apply] at hval
    let x := marked (extend S)
    have he (j : Fin (t+1)) : MvPolynomial.aeval x (N j) =
        MvPolynomial.aeval x D * (Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
      dsimp only [N, D]
      rw [aeval_commonTaylorNumerator center Q x (hτ j) hsep, map_pow,
        hcoef _ ((Nat.le_of_lt_succ j.isLt).trans ht)]
    have hdne : MvPolynomial.aeval x D ≠ 0 := by
      dsimp only [D]
      rw [map_pow]
      exact pow_ne_zero _ hsep
    have hc : MvPolynomial.aeval x cut =
        MvPolynomial.aeval x D * (seedEmbedding (S.eval (node i)) - seedEmbedding (w i)) := by
      dsimp only [cut]
      rw [hval, map_add, map_mul, map_sum, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply,
        mul_sub, mul_add, Finset.mul_sum]
      simp only [map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, he]
      have hsum : (∑ j : Fin (t+1), a j *
          (MvPolynomial.aeval x D * (Polynomial.taylor center (S.map seedEmbedding)).coeff j)) =
          ∑ j : Fin (t+1), MvPolynomial.aeval x D *
            (a j * (Polynomial.taylor center (S.map seedEmbedding)).coeff j) :=
        Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum]
      ring
    change MvPolynomial.aeval x cut = 0 ↔ _
    rw [hc, mul_eq_zero, or_iff_right hdne, sub_eq_zero, seedEmbedding.injective.eq_iff]
end
end P1_7_4_3
end
section
namespace P1_7_4_3
noncomputable section
open Polynomial Finset
open P1 (K I node p agreement blockLength HighBand AnchorModel AnchoredFamily)
open P1_7 (degreeAt )
open P1_7_4 (ODEGuard )
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (totalCap topCap)
open scoped BigOperators
end
end P1_7_4_3
end

end Merged_UpperBranch4

-- merged module R6960PowerLayers
section Merged_R6960PowerLayers
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace Lower6960.PowerLayers
open K1_14 (Shape Jet Equation Seeds FX triangle)
open K1_14_3 (RowCaps)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (jetDegree seedDegree jetDegree_le seedDegree_le jetDegree_mul seedDegree_mul)
open P1_7_4_1 (factorDegree factorDegree_pow factorDegree_add)
open Polynomial Finset
open scoped BigOperators Classical
open K1_14_2_1_2 (seed_finrank)
theorem forced_power {h N W U : ℕ} (hh : 0<h) (hw : W<N) {G P R : Jet}
    (irr : Irreducible G) (slope : 0<G.natDegree) (seeded : UsesSeed G)
    (np : P≠0) (div : G∣P) (small : U<K1.p)
    (caps : ∀ j i, ((P.coeff j).coeff i).totalDegree≤U)
    (shifts : ∀ (i : Fin 2) a, W+2*h*a≤N-1 → G∣K1_14.seedHasse i a R) :
    G^(1+(N-1-W)/(2*h))∣R := by
  apply K1_14_2_1_1.proof G P R U _ irr slope seeded np div small caps
  intro i a ha
  apply shifts i a
  have le : a≤(N-1-W)/(2*h) := by omega
  have := (Nat.le_div_iff_mul_le (by omega : 0<2*h)).mp le
  rw [Nat.mul_comm a] at this
  omega
def positions (s : Shape) (h W : ℕ) (F : Jet) : Finset (ℕ×ℕ) :=
  ((range (s.B+1)).product (range (s.J+1))).filter fun a =>
    a.1+a.2+jetDegree F≤s.B ∧ a.2+F.natDegree≤s.J ∧
    (a.1+a.2+F.leadingCoeff.natDegree+F.natDegree)*(131071-h) ≤ W+(a.2+F.natDegree)
theorem quotient_rank (s : Shape) (h W : ℕ) (V : Submodule FX Jet) (F : Jet)
    (nf : F≠0) (dvd : ∀ R∈V,F∣R) (caps : ∀ R∈V,RowCaps R s)
    (lead : ∀ R∈V,R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree) :
    Module.finrank FX V≤(positions s h W F).card*triangle (s.U-seedDegree F) := by
  classical
  let U := V.comap (Algebra.lmul FX Jet F)
  let mulF : U →ₗ[FX] V := (((Algebra.lmul FX Jet F).comp U.subtype).codRestrict V
    (fun Q=>Q.property))
  have eqv : Function.Bijective mulF := by
    constructor
    · intro x y he
      exact Subtype.ext (mul_left_cancel₀ nf (congrArg Subtype.val he))
    · intro x
      obtain ⟨y,hy⟩:=dvd x x.property
      exact ⟨⟨y,by change F*y∈V; rw [←hy]; exact x.property⟩, Subtype.ext hy.symm⟩
  have cdeg (Q : U) : seedDegree (Q : Jet)≤s.U-seedDegree F := by
    by_cases zero : (Q : Jet)=0
    · simp [zero,seedDegree]
    have hp : seedDegree (F*(Q : Jet))≤s.U := by
      apply (seedDegree_le ..).2
      intro j i
      by_cases z : (((F*(Q : Jet)).coeff j).coeff i)=0
      · simp [z]
      exact (caps _ Q.property j i z).2.2
    rw [seedDegree_mul nf zero] at hp
    omega
  let T := MvPolynomial.restrictTotalDegree (Fin 2) FX (s.U-seedDegree F)
  let S := positions s h W F
  let coord (a : S) : U →ₗ[FX] Seeds :=
    (((lcoeff Seeds a.val.1).restrictScalars FX).comp
      ((lcoeff Equation a.val.2).restrictScalars FX)).comp U.subtype
  let proj : U →ₗ[FX] (S→T) := LinearMap.pi fun a => (coord a).codRestrict T (fun Q =>
    (MvPolynomial.mem_restrictTotalDegree ..).2 ((seedDegree_le ..).1 (cdeg Q) a.val.2 a.val.1))
  have hz : ∀ Q : U, proj Q=0 → Q=0 := by
    intro Q z
    apply Subtype.ext
    by_contra bad
    have nq : (Q : Jet)≠0 := bad
    let j := (Q : Jet).natDegree
    let i := (Q : Jet).leadingCoeff.natDegree
    have coeff : (((Q : Jet).coeff j).coeff i)≠0 := by
      dsimp only [i,j]
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nq)
    have jq := (jetDegree_le (Q : Jet) _).1 le_rfl j i coeff
    have total : jetDegree (F*(Q : Jet))≤s.B := (jetDegree_le ..).2 (fun v y ne=>(caps _ Q.property v y ne).1)
    rw [jetDegree_mul nf nq] at total
    have nd : (F*(Q : Jet)).natDegree≤s.J := by
      let R := F*(Q : Jet)
      have hn : R≠0 := mul_ne_zero nf nq
      apply (caps R Q.property R.natDegree R.leadingCoeff.natDegree ?_).2.1
      rw [coeff_natDegree,coeff_natDegree]; exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    have l := lead (F*(Q:Jet)) Q.property (mul_ne_zero nf nq)
    rw [natDegree_mul nf nq] at nd l
    rw [leadingCoeff_mul,natDegree_mul (leadingCoeff_ne_zero.mpr nf) (leadingCoeff_ne_zero.mpr nq)] at l
    have mem : (i,j)∈S := by
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by dsimp [j]; omega)⟩,?_,?_,?_⟩
      · omega
      · dsimp [j]; omega
      · dsimp [i,j]; linarith
    have witness := congrArg (fun f : S→T => ((f ⟨(i,j),mem⟩ : T) : Seeds)) z
    exact coeff witness
  have inj : Function.Injective proj := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,hxy]
    ext a
    exact sub_self _
  let eq := LinearEquiv.ofBijective mulF eqv
  rw [←eq.finrank_eq]
  calc _ ≤ Module.finrank FX (S→T) := LinearMap.finrank_le_finrank_of_injective inj
       _ = _ := by
          let : Module.Free FX T := Module.Free.of_basis (MvPolynomial.basisRestrictSupport FX _)
          rw [Module.finrank_pi_fintype FX (M:=fun _ : S=>T)]
          simp [T,S,seed_finrank]
def eligiblePositions (s : Shape) (h W slope trim : ℕ) : Finset (ℕ×ℕ) :=
  ((range (s.B+1)).product (range (s.J+1))).filter fun a =>
    a.2≤a.1 ∧ slope≤a.2 ∧ a.1+trim≤s.B ∧ a.1*(131071-h)≤W+a.2
theorem layer_rank (s : Shape) (h W k slope extra u : ℕ) (V : Submodule FX Jet)
    (G : Jet) (g : G≠0) (sg : slope≤G.natDegree) (ug : u≤seedDegree G)
    (bg : G.natDegree+extra≤jetDegree G)
    (dvd : ∀ R∈V,G^k∣R) (caps : ∀ R∈V,RowCaps R s)
    (lead : ∀ R∈V,R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree) :
    Module.finrank FX V ≤ (eligiblePositions s h W (k*slope) (k*extra)).card *
      (if k*u≤s.U then triangle (s.U-k*u) else 0) := by
  classical
  let F:=G^k
  have nf : F≠0 := pow_ne_zero k g
  have ds : F.natDegree=k*G.natDegree := natDegree_pow G k
  have du : seedDegree F=k*seedDegree G := factorDegree_pow g k 2
  have db : jetDegree F=k*jetDegree G := factorDegree_pow g k 0
  have sfit : k*slope≤F.natDegree := ds ▸ Nat.mul_le_mul_left _ sg
  have bfit : F.natDegree+k*extra≤jetDegree F := by
    rw [ds,db,←Nat.mul_add]; exact Nat.mul_le_mul_left _ bg
  have ufit : k*u≤seedDegree F := du ▸ Nat.mul_le_mul_left _ ug
  by_cases zero : s.U<k*u
  · rw [ite_eq_right (Nat.not_le.mpr zero),Nat.mul_zero]
    have sub : V=⊥ := by
      apply bot_unique
      intro R hr
      change R=0
      by_contra nr
      obtain ⟨Q,hq⟩:=dvd R hr
      have qn : Q≠0 := right_ne_zero_of_mul (hq ▸ nr)
      have cap : seedDegree R≤s.U := (seedDegree_le ..).2 (by
        intro j i
        by_cases hz : ((R.coeff j).coeff i)=0
        · simp [hz]
        exact (caps R hr j i hz).2.2)
      change R=F*Q at hq
      rw [hq,seedDegree_mul nf qn] at cap
      omega
    rw [sub,finrank_bot]
  · rw [ite_eq_left (Nat.le_of_not_gt zero)]
    have rank:=quotient_rank s h W V F nf dvd caps lead
    have card : (positions s h W F).card ≤ (eligiblePositions s h W (k*slope) (k*extra)).card := by
      apply card_le_card_of_injOn (fun a:ℕ×ℕ=>(a.1+a.2+F.natDegree,a.2+F.natDegree))
      · intro a ha
        obtain ⟨_,ht,hj,hw⟩:=mem_filter.mp ha
        apply mem_filter.mpr
        dsimp only
        refine ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,
          by omega, by omega, by omega, ?_⟩
        exact (Nat.mul_le_mul_right _ (by omega)).trans hw
      · rintro ⟨i,j⟩ _ ⟨i',j'⟩ _ he
        simp only [Prod.mk.injEq,Nat.add_left_inj] at he
        obtain ⟨ha,rfl⟩:=he
        simp_all
    have tri : triangle (s.U-seedDegree F)≤triangle (s.U-k*u) := by
      unfold triangle
      apply Nat.div_le_div_right
      have := Nat.sub_le_sub_left ufit s.U
      exact Nat.mul_le_mul (by omega) (by omega)
    exact rank.trans (Nat.mul_le_mul card tri)
def layerCost (s : Shape) (h N W slope extra u : ℕ) : ℕ :=
  let k:=1+(N-1-W)/(2*h)
  (eligiblePositions s h W (k*slope) (k*extra)).card *
    (if k*u≤s.U then triangle (s.U-k*u) else 0)
theorem no_common_power (s : Shape) (h N slope extra u : ℕ)
    (rows : ℕ→Submodule FX Jet) (G : Jet) (nz : G≠0)
    (sg : slope≤G.natDegree) (ug : u≤seedDegree G) (bg : G.natDegree+extra≤jetDegree G)
    (caps : ∀ W<N, ∀ R∈rows W, RowCaps R s)
    (lead : ∀ W<N, ∀ R∈rows W, R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree)
    (supply : (∑ W∈range N,layerCost s h N W slope extra u) <
      ∑ W∈range N,Module.finrank FX (rows W)) :
    ¬ (∀ W<N, ∀ R∈rows W,G^(1+(N-1-W)/(2*h))∣R) := by
  intro power
  apply (Nat.not_lt_of_ge (Finset.sum_le_sum (s:=range N) (fun W mem =>
    layer_rank s h W _ slope extra u (rows W) G nz sg ug bg (power W (mem_range.mp mem))
      (caps W (mem_range.mp mem)) (lead W (mem_range.mp mem))))) supply
theorem avoiding_row (s : Shape) (h N slope extra u : ℕ) (hh : 0<h)
    (rows : ℕ→Submodule FX Jet) (G P : Jet) (irr : Irreducible G)
    (gs : 0<G.natDegree) (seeded : UsesSeed G) (np : P≠0) (gp : G∣P)
    (small : s.U<K1.p) (pc : ∀ j i,((P.coeff j).coeff i).totalDegree≤s.U)
    (sg : slope≤G.natDegree) (ug : u≤seedDegree G) (bg : G.natDegree+extra≤jetDegree G)
    (caps : ∀ W<N, ∀ R∈rows W, RowCaps R s)
    (lead : ∀ W<N, ∀ R∈rows W, R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree)
    (shift : ∀ W<N,∀ R∈rows W,∀ i a, W+2*h*a≤N-1 → K1_14.seedHasse i a R∈rows (N-1))
    (supply : (∑ W∈range N,layerCost s h N W slope extra u) <
      ∑ W∈range N,Module.finrank FX (rows W)) :
    ∃ Q∈rows (N-1), ¬ G∣Q := by
  by_contra! shared
  apply no_common_power s h N slope extra u rows G irr.ne_zero sg ug bg caps lead supply
  intro W hw R hr
  exact forced_power hh hw irr gs seeded np gp small pc
    (fun i a hsp => shared _ (shift W hw R hr i a hsp))
def net {ι : Type*} (T : Finset ι) (weight : ι→ℕ) (a b : ι→ℤ)
    (c d : ℤ) (x : ℕ) : ℤ :=
  (∑ i∈T, (weight i : ℤ)*max 0 (a i+b i*(x:ℤ)))-(c+d*(x:ℤ))
private theorem clip_second (x y : ℤ) :
    2*max 0 (x+y) ≤ max 0 x + max 0 (x+2*y) := by
  by_cases h : 0≤x+y
  · rw [max_eq_right h]
    have h1 := le_max_right 0 x
    have h2 := le_max_right 0 (x+2*y)
    omega
  · rw [max_eq_left (by omega : x+y≤0)]
    have h1 := le_max_left 0 x
    have h2 := le_max_left 0 (x+2*y)
    omega
theorem net_convex {ι : Type*} (T : Finset ι) (weight : ι→ℕ) (a b : ι→ℤ)
    (c d : ℤ) (x : ℕ) :
    2*net T weight a b c d (x+1) ≤ net T weight a b c d x + net T weight a b c d (x+2) := by
  classical
  have each (i) : 2*((weight i:ℤ)*max 0 (a i+b i*((x:ℤ)+1))) ≤
      (weight i:ℤ)*max 0 (a i+b i*(x:ℤ)) + (weight i:ℤ)*max 0 (a i+b i*((x:ℤ)+2)) := by
    have z:=mul_le_mul_of_nonneg_left (clip_second (a i+b i*(x:ℤ)) (b i)) (Int.natCast_nonneg (weight i))
    rw [show a i+b i*((x:ℤ)+1)=a i+b i*(x:ℤ)+b i by ring,
      show a i+b i*((x:ℤ)+2)=a i+b i*(x:ℤ)+2*b i by ring]
    linarith only [z]
  have total:=sum_le_sum (s:=T) (fun i _=>each i)
  rw [←Finset.mul_sum, Finset.sum_add_distrib] at total
  unfold net
  push_cast
  linarith only [total]
theorem from_two_heights (f : ℕ→ℤ) (lo : ℕ) (positive : 0<f lo)
    (next : f lo≤f (lo+1)) (convex : ∀ x,2*f (x+1)≤f x+f (x+2)) :
    ∀ y,lo≤y → 0<f y := by
  intro y hy
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hy
  have both : ∀ n, 0<f (lo+n) ∧ f (lo+n)≤f (lo+n+1) := by
    intro t
    induction t with
    | zero => exact ⟨positive,next⟩
    | succ t ih =>
      have := convex (lo+t)
      exact ⟨lt_of_lt_of_le ih.1 ih.2,by
        change f (lo+t+1)≤f (lo+t+2)
        omega⟩
  exact (both n).1
theorem sum_layer_gains (N width shift layers : ℕ) (delta : ℕ→ℕ) :
    (∑ W∈range N, ∑ i∈range layers,
      if width≤W ∧ W+shift*i<N then delta i else 0) =
      ∑ i∈range layers, (N-width-shift*i)*delta i := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have support : (range N).filter (fun W=>width≤W ∧ W+shift*i<N) = Ico width (N-shift*i) := by
    ext W
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [←Finset.sum_filter,support,Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
  change (N-shift*i-width)*delta i=(N-width-shift*i)*delta i
  rw [Nat.sub_sub,Nat.sub_sub,Nat.add_comm (shift*i) width]
#print axioms sum_layer_gains
#print axioms net_convex
#print axioms from_two_heights
#print axioms avoiding_row
#print axioms layer_rank
#print axioms forced_power
#print axioms quotient_rank
end Lower6960.PowerLayers

end
end Merged_R6960PowerLayers

-- merged module R6960HelperSource
section Merged_R6960HelperSource
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.HelperSource
open Finset Polynomial
open K1_14 (Shape Jet FX L Banks shapeSum triangle slots seedHasse jetAt)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open K1_14_3 (RowCaps)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open P1_7 (Bank debit)
open P1_7_1 (nodeRows groupedPoleMoment)
open P1_7_5 (kept)
open PowerLayers (eligiblePositions layerCost)
open P1_7_5 (position_sum)
open P1_7_1 (pole_bound)
open P1_7_6 (slots_anti rise_of_convex)
def orderCap (s : Shape) (d c q j : ℕ) : ℕ :=
  if c = 0 then j/d else min (j/d) ((s.B-q)/c)
theorem le_orderCap (s : Shape) {d c q j k : ℕ} (hd : 0 < d) (hq : q ≤ s.B) :
    k ≤ orderCap s d c q j ↔ k*d ≤ j ∧ q+k*c ≤ s.B := by
  unfold orderCap
  split
  · rename_i hc
    rw [hc, Nat.mul_zero, Nat.add_zero, Nat.le_div_iff_mul_le hd]
    simp [hq]
  · rename_i hc
    rw [le_min_iff, Nat.le_div_iff_mul_le hd, Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc)]
    omega
def coordinateGain (s : Shape) (A h r d c v q j : ℕ) : ℕ :=
  let C := kept s.U v (orderCap s d c q j)
  ∑ i ∈ range (orderCap s d c q j + 1),
    (C i - C (i+1)) * (s.m*A+j-q*(131071-h)-2*h*(r+i))
def gain (s : Shape) (A h r d c v : ℕ) : ℕ :=
  shapeSum s (coordinateGain s A h r d c v)
def cutoffCount (s : Shape) (A h r : ℕ) : ℕ := s.m*A-2*h*r
private theorem layerCost_eq (s : Shape) (h N W d c v : ℕ) (hd : 0 < d) :
    layerCost s h N W d c v =
      shapeSum s fun q j =>
        if q*(131071-h) ≤ W+j then
          kept s.U v (orderCap s d c q j) (1+(N-1-W)/(2*h))
        else 0 := by
  classical
  let k := 1+(N-1-W)/(2*h)
  unfold layerCost eligiblePositions
  change (((range (s.B+1)).product (range (s.J+1))).filter (fun a =>
    a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2)).card *
    slots s.U (k*v) = _
  rw [← Nat.nsmul_eq_mul, ← sum_const, sum_filter]
  change (∑ a ∈ range (s.B+1) ×ˢ range (s.J+1),
    if a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2 then slots s.U (k*v) else 0) = _
  rw [sum_product (range (s.B+1)) (range (s.J+1)) (fun a : ℕ×ℕ =>
    if a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2 then slots s.U (k*v) else 0)]
  unfold shapeSum
  apply sum_congr rfl
  intro q hq
  have hqb : q ≤ s.B := Nat.le_of_lt_succ (mem_range.mp hq)
  rw [← sum_subset (s₁ := range (min q s.J+1)) (s₂ := range (s.J+1))
    (range_mono (Nat.succ_le_succ (min_le_right _ _)))]
  · apply sum_congr rfl
    intro j hj
    have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
    change (if j≤q ∧ k*d≤j ∧ q+k*c≤s.B ∧ q*(131071-h)≤W+j then slots s.U (k*v) else 0) =
      if q*(131071-h)≤W+j then kept s.U v (orderCap s d c q j) k else 0
    simp only [kept, le_orderCap s hd hqb]
    by_cases hw : q*(131071-h) ≤ W+j
    · simp only [hjq, hw, true_and, and_true, ite_true]
    · simp only [hw, and_false, ite_false]
  · intro j hj hn
    have hq' : ¬ j≤q := by
      simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hn
      omega
    simp [hq']
private theorem coordinate_total (s : Shape) (A h r d c v q j : ℕ) (hh : 0<h)
    (hk : 1≤131071-h) (hj : j≤q) :
    let N := cutoffCount s A h r
    (∑ W ∈ range N, if q*(131071-h) ≤ W+j then
      kept s.U v (orderCap s d c q j) (1+(N-1-W)/(2*h)) else 0) +
    coordinateGain s A h r d c v q j = triangle s.U*(N+j-q*(131071-h)) := by
  dsimp only
  let N := cutoffCount s A h r
  let t := q*(131071-h)
  let g := orderCap s d c q j
  have hq : q ≤ t := by simpa [t] using Nat.mul_le_mul_left q hk
  have hjt : j ≤ t := hj.trans hq
  have he (i : ℕ) : N+0-(t-j)-2*h*(0+i) = s.m*A+j-t-2*h*(r+i) := by
    simp only [Nat.add_zero, Nat.zero_add]
    unfold N cutoffCount
    rw [Nat.mul_add]
    omega
  have eq := position_sum N (2*h) (t-j) 0 s.U v g (Nat.zero_le _) (by omega)
  simp only [Nat.add_zero, Nat.sub_zero, Nat.zero_add] at eq
  have hwidth : N-(t-j) = N+j-t := by omega
  have he' (i : ℕ) : N-(t-j)-2*h*i = s.m*A+j-t-2*h*(r+i) := by simpa using he i
  simp_rw [he'] at eq
  rw [hwidth] at eq
  have hsplit :
      coordinateGain s A h r d c v q j =
      (∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v)) *
         (s.m*A+j-t-2*h*(r+a))) +
      slots s.U (g*v) * (s.m*A+j-t-2*h*(r+g)) := by
    unfold coordinateGain
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro i hi
      have h := mem_range.mp hi
      simp only [kept, ite_eq_left h.le, ite_eq_left (Nat.succ_le_of_lt h)]
      rfl
    · simp [kept, g, t]
  rw [hsplit]
  have hguard (W : ℕ) : t-j ≤ W ↔ t ≤ W+j := by omega
  simpa only [hguard] using eq
theorem cutoff_total (s : Shape) (A h r d c v : ℕ) (hh : 0 < h) (hk : 1 ≤ 131071-h)
    (hd : 0 < d) :
    let N := cutoffCount s A h r
    (∑ W ∈ range N, layerCost s h N W d c v) + gain s A h r d c v =
      triangle s.U * shapeSum s (fun q j => N+j-q*(131071-h)) := by
  dsimp only
  let N := cutoffCount s A h r
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range N, shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range N, F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp_rw [layerCost_eq s h (cutoffCount s A h r) _ d c v hd]
  rw [hswap]
  simp only [gain, shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  exact coordinate_total s A h r d c v q j hh hk
    ((Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _))
theorem crt_rank_floor {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (hh : 0<h) (hk : h≤131070)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (W : ℕ)
    (hW : K1_14_1.rawWidthCond h t.shape W) :
    K1_14_1.rawVolumeAt h t.shape W ≤ debit h t +
      ∑ w ∈ range (W+1), Module.finrank FX (evaluated Crt word t.shape w) := by
  have hlocal := P1_7_1_1.of_children P1_7_1_1_1.proof P1_7_1_1_2.proof
  have hvol := P0_10_1.ambient_bound (by omega : h ≤ 131071) t.shape W hW
  have hcontact := P0_10_1.physical_bound h word t.shape W
  have hpole := pole_bound hlocal hh (hk.trans_lt (by decide)) Crt word t.shape small W
  have hsum := P1_7_1.telescope hk Crt word t.shape W
  have hphys : K1_14_1.physicalDebit t.shape = triangle t.shape.U * t.nodeRows := by
    rw [← hnodes]
    unfold K1_14_1.physicalDebit nodeRows
    rw [Nat.mul_assoc]
  rw [hphys] at hcontact
  have hextra := Nat.mul_le_mul_left (2*h*(t.shape.U+1)) hmoment
  unfold debit
  omega
def WidthGuard (t : Bank) (A h r : ℕ) : Prop :=
  t.shape.B * (131071-h) < cutoffCount t.shape A h r
theorem crt_supply {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (A r d c v : ℕ) (hh : 0<h) (hk : h≤131070) (hd : 0<d)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (width : WidthGuard t A h r)
    (surplus : debit h t < gain t.shape A h r d c v) :
    let N := cutoffCount t.shape A h r
    (∑ W ∈ range N, layerCost t.shape h N W d c v) <
      ∑ W ∈ range N, Module.finrank FX (evaluated Crt word t.shape W) := by
  dsimp only
  let N := cutoffCount t.shape A h r
  have hw : t.shape.B*(131071-h)<N := width
  have hcomplete : N-1+1=N := by omega
  have hf := crt_rank_floor Crt word t hh hk hnodes hmoment small (N-1) (by
    intro q hq j _
    rw [hcomplete]
    exact (Nat.mul_le_mul_right _ hq).trans (hw.le.trans (Nat.le_add_right N j)))
  unfold K1_14_1.rawVolumeAt at hf
  rw [hcomplete] at hf
  have ht := cutoff_total t.shape A h r d c v hh (by omega) hd
  dsimp only at ht
  change (∑ W ∈ range N, layerCost t.shape h N W d c v) + gain t.shape A h r d c v =
    triangle t.shape.U * shapeSum t.shape (fun q j => N+j-q*(131071-h)) at ht
  change (∑ W ∈ range N, layerCost t.shape h N W d c v) <
    ∑ W ∈ range N, Module.finrank FX (evaluated Crt word t.shape W)
  omega
theorem nonzero_of_supply {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (s : Shape) (N : ℕ) (supply : 0 < ∑ W ∈ range N, Module.finrank FX (evaluated Crt word s W)) :
    ∃ P ∈ evaluated Crt word s (N-1), P ≠ 0 := by
  by_contra! hz
  have hall : (∑ W ∈ range N, Module.finrank FX (evaluated Crt word s W)) = 0 := by
    apply sum_eq_zero
    intro W hW
    have hW' : W ≤ N-1 := by have := mem_range.mp hW; omega
    have hb : evaluated Crt word s W = ⊥ := by
      apply bot_unique
      intro P hP
      exact (Submodule.mem_bot FX).mpr
        (hz P (evaluated_mono Crt word rfl rfl rfl le_rfl hW' hP))
    rw [hb, finrank_bot]
  omega
theorem crt_avoiding_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (A r d c v : ℕ) (hh : 0<h) (hk : h≤131070) (hd : 0<d)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (smallSeed : t.shape.U<K1.p) (width : WidthGuard t A h r)
    (surplus : debit h t < gain t.shape A h r d c v)
    {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : d≤G.natDegree) (seed : v≤seedDegree G) (excess : G.natDegree+c≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word t.shape (cutoffCount t.shape A h r-1), ¬ G∣Q := by
  by_contra! shared
  let N := cutoffCount t.shape A h r
  have supply := crt_supply Crt word t A r d c v hh hk hd hnodes hmoment small width surplus
  obtain ⟨P, hP, hnP⟩ := nonzero_of_supply Crt word t.shape N (lt_of_le_of_lt (Nat.zero_le _) supply)
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ t.shape.U := by
    by_cases hz : ((P.coeff j).coeff i)=0
    · simp [hz]
    · exact (evaluated_shape Crt word hP j i hz).2.2
  obtain ⟨Q, hQ, hAvoid⟩ := PowerLayers.avoiding_row t.shape h N d c v hh
    (evaluated Crt word t.shape) G P irr (hd.trans_le slope) seeded hnP (shared P hP)
    smallSeed hpc slope seed excess
    (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound hh hk Crt word t.shape W R hR hnR)
    (fun _ _ _ hR i a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR i a))
    supply
  exact hAvoid (shared Q hQ)
#print axioms cutoff_total
#print axioms crt_rank_floor
#print axioms crt_avoiding_row
def signedWidth (s : Shape) (A h r q j i : ℕ) : ℤ :=
  (s.m : ℤ)*A+j-(131071-(h : ℤ))*q-2*(h : ℤ)*(r+i)
theorem width_cast (s : Shape) (A h r q j i : ℕ) (hk : h≤131071) :
    ((s.m*A+j-q*(131071-h)-2*h*(r+i) : ℕ) : ℤ) =
      max 0 (signedWidth s A h r q j i) := by
  rw [Nat.sub_sub]
  have he : (↑(s.m*A+j : ℕ) : ℤ) - (↑(q*(131071-h)+2*h*(r+i) : ℕ) : ℤ) =
      signedWidth s A h r q j i := by
    simp only [signedWidth, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]
    ring
  generalize s.m*A+j = x at *
  generalize q*(131071-h)+2*h*(r+i) = y at *
  by_cases hxy : y≤x
  · rw [Int.ofNat_sub hxy, he, max_eq_right (by omega)]
  · have hz : x-y=0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, Int.ofNat_zero, max_eq_left (by omega)]
private theorem weighted_convex (s : Shape) (A h r q j i c : ℕ) (hk : h+2≤131071) :
    let f := fun h => ((c*(s.m*A+j-q*(131071-h)-2*h*(r+i)) : ℕ) : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  dsimp only
  simp only [Nat.cast_mul, width_cast s A h r q j i (by omega),
    width_cast s A (h+1) r q j i (by omega), width_cast s A (h+2) r q j i hk, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg c)
  by_cases hn : signedWidth s A (h+1) r q j i ≤ 0
  · rw [max_eq_left hn, zero_add]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hn)]
    have hlin : signedWidth s A (h+1) r q j i + signedWidth s A (h+1) r q j i =
        signedWidth s A h r q j i + signedWidth s A (h+2) r q j i := by
      simp only [signedWidth, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hlin]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
def surplus (t : Bank) (A h r d c v : ℕ) : ℤ :=
  (gain t.shape A h r d c v : ℤ)-(debit h t : ℤ)
theorem surplus_convex (t : Bank) (A h r d c v : ℕ) (hk : h+2≤131071) :
    surplus t A (h+1) r d c v + surplus t A (h+1) r d c v ≤
      surplus t A h r d c v + surplus t A (h+2) r d c v := by
  have hg : (gain t.shape A (h+1) r d c v : ℤ) + gain t.shape A (h+1) r d c v ≤
      (gain t.shape A h r d c v : ℤ) + gain t.shape A (h+2) r d c v := by
    simp only [gain, shapeSum, coordinateGain, Nat.cast_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro q _
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro i _
    exact weighted_convex t.shape A h r q j i _ hk
  have hd : (debit (h+1) t : ℤ) + debit (h+1) t = (debit h t : ℤ) + debit (h+2) t := by
    simp only [debit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  unfold surplus
  omega
theorem surplus_positive (t : Bank) (A lo h r d c v : ℕ) (hl : lo≤h) (hk : h≤131070)
    (positive : 0<surplus t A lo r d c v)
    (increasing : surplus t A lo r d c v ≤ surplus t A (lo+1) r d c v) :
    debit h t < gain t.shape A h r d c v := by
  have inc := rise_of_convex (f := fun n => surplus t A n r d c v)
    (fun n hn => surplus_convex t A n r d c v (by omega)) hl increasing
  have hp := positive.trans_le inc.1
  unfold surplus at hp
  omega
theorem width_at_height (t : Bank) (A lo h r : ℕ) (hl : lo≤h) (hk : h≤131071)
    (hs : 2*r≤t.shape.B) (hw : WidthGuard t A lo r) :
    WidthGuard t A h r := by
  unfold WidthGuard cutoffCount at *
  have hl' : lo ≤ 131071 := hl.trans hk
  have z := Nat.mul_le_mul_left (h-lo) hs
  have hlip : t.shape.B*(131071-h) + 2*h*r ≤
      t.shape.B*(131071-lo) + 2*lo*r := by
    have h₁ : 131071-h+(h-lo)=131071-lo := by omega
    have h₂ : lo+(h-lo)=h := by omega
    have h₁' := congrArg (t.shape.B * ·) h₁
    have h₂' := congrArg (fun n : ℕ => 2*n*r) h₂
    simp only [Nat.mul_add, Nat.add_mul] at h₁' h₂'
    rw [Nat.mul_comm t.shape.B (h-lo)] at h₁'
    rw [Nat.mul_comm (2*(h-lo)) r, ←Nat.mul_assoc r 2 (h-lo),
      Nat.mul_comm r 2, Nat.mul_comm (2*r) (h-lo)] at h₂'
    omega
  omega
#print axioms surplus_positive
#print axioms width_at_height
end Lower6960.HelperSource

end Merged_R6960HelperSource

-- merged module R6960HelperSourceArithmetic
section Merged_R6960HelperSourceArithmetic
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.HelperSource
open Finset
open K1_14 (Shape shapeSum slots)
open P1_7 (Bank debit)
open P1_7_5 (kept)
open P1_7_6 (linearEnd lt_linearEnd)
open P1_7_1_3 (evaluate evaluate_eq)
open P1_7_6 (slots_anti)
def clippedSum (base step bound cap : ℕ) : ℕ :=
  let len := linearEnd base step bound cap
  len*bound-(len*base+step*(len*(len-1)/2))
theorem clippedSum_eq (base step bound cap : ℕ) :
    clippedSum base step bound cap = ∑ a ∈ range cap, (bound-(base+step*a)) := by
  let len := linearEnd base step bound cap
  have hle : len ≤ cap := by
    by_contra! bad
    exact (lt_linearEnd base step bound cap cap).mp bad |>.1.false
  rw [← sum_subset (range_mono hle) (f := fun a => bound-(base+step*a)) (by
    intro a ha hna
    apply Nat.sub_eq_zero_of_le
    have hn := fun h => hna (mem_range.mpr ((lt_linearEnd base step bound cap a).mpr
      ⟨mem_range.mp ha,h⟩))
    exact Nat.le_of_not_gt hn)]
  have hadd : (∑ a ∈ range len, (bound-(base+step*a))) +
      (∑ a ∈ range len, (base+step*a)) = len*bound := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _ ∈ range len, bound := by
        apply sum_congr rfl
        intro a ha
        exact Nat.sub_add_cancel ((lt_linearEnd base step bound cap a).mp (mem_range.mp ha)).2.le
      _ = _ := by simp
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, Finset.sum_range_id] at hadd
  change len*bound-(len*base+step*(len*(len-1)/2)) = _
  exact (Nat.eq_sub_of_add_eq hadd).symm
private def boxPhase (s : Shape) (A h r d c v δ q j : ℕ) : ℕ :=
  ∑ i ∈ range (s.J/d+1),
    if j≤q ∧ (i+δ)*d≤j ∧ q+(i+δ)*c≤s.B then
      slots s.U ((i+δ)*v)*(s.m*A+j-q*(131071-h)-2*h*(r+i))
    else 0
private theorem coordinate_phases (s : Shape) (A h r d c v q j : ℕ)
    (hd : 0<d) (hq : q≤s.B) (hjq : j≤q) (hj : j≤s.J) :
    coordinateGain s A h r d c v q j + boxPhase s A h r d c v 1 q j =
      boxPhase s A h r d c v 0 q j := by
  let K := orderCap s d c q j
  let C := kept s.U v K
  let w := fun i => s.m*A+j-q*(131071-h)-2*h*(r+i)
  have hphase (δ : ℕ) : boxPhase s A h r d c v δ q j =
      ∑ i ∈ range (s.J/d+1), C (i+δ)*w i := by
    apply sum_congr rfl
    intro i _
    simp only [C, K, w, kept, le_orderCap s hd hq, hjq, true_and, ite_mul, zero_mul]
  have hmono : Antitone C := by
    intro i l hi
    by_cases hl : l≤K
    · simp only [C, kept, ite_eq_left hl, ite_eq_left (hi.trans hl)]
      exact slots_anti _ (Nat.mul_le_mul_right _ hi)
    · simp [C, kept, hl]
  have hK : K ≤ s.J/d := by
    have h := ((le_orderCap s hd hq).mp (le_rfl (a := K))).1.trans hj
    exact (Nat.le_div_iff_mul_le hd).mpr h
  have hsum : coordinateGain s A h r d c v q j =
      ∑ i ∈ range (s.J/d+1), (C i-C (i+1))*w i := by
    apply sum_subset (range_mono (Nat.succ_le_succ hK))
    intro i _ hi
    have hi' : ¬ i≤K := by
      intro h
      exact hi (mem_range.mpr (Nat.lt_succ_of_le h))
    have hi'' : ¬ i+1≤K := by omega
    change (C i-C (i+1))*w i = 0
    simp only [C, kept, ite_eq_right hi', ite_eq_right hi'', Nat.sub_self, Nat.zero_mul]
  rw [hsum, hphase 1, hphase 0, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← Nat.add_mul, Nat.sub_add_cancel (hmono (Nat.le_succ i)), Nat.add_zero]
def column (s : Shape) (A h r c i δ j : ℕ) : ℕ :=
  clippedSum (j*(131071-h)+2*h*(r+i)) (131071-h) (s.m*A+j)
    (s.B+1-(i+δ)*c-j)
theorem column_eq (s : Shape) (A h r c i δ j : ℕ) :
    column s A h r c i δ j =
      ∑ q ∈ Ico j (s.B+1-(i+δ)*c), (s.m*A+j-q*(131071-h)-2*h*(r+i)) := by
  rw [column, clippedSum_eq, sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro a _
  have h := Nat.add_mul j a (131071-h)
  rw [Nat.sub_sub, h]
  congr 1
  ring
def phaseLayer (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  slots s.U ((i+δ)*v) *
    evaluate (fun a => column s A h r c i δ ((i+δ)*d+a)) (s.J+1-(i+δ)*d)
def compressedPhase (s : Shape) (A h r d c v δ : ℕ) : ℕ :=
  evaluate (phaseLayer s A h r d c v δ) (s.J/d+1)
private theorem sum_boxPhase (s : Shape) (A h r d c v δ : ℕ) :
    (∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), boxPhase s A h r d c v δ q j) =
      compressedPhase s A h r d c v δ := by
  unfold boxPhase compressedPhase
  rw [evaluate_eq]
  conv_lhs =>
    enter [2, q]
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm, phaseLayer, evaluate_eq, ← sum_Ico_eq_sum_range, mul_sum]
  have hfilter : (range (s.J+1)).filter ((i+δ)*d ≤ ·) = Ico ((i+δ)*d) (s.J+1) := by
    ext j; simp [and_comm]
  rw [← hfilter, sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases hj : (i+δ)*d≤j
  · rw [ite_eq_left hj, column_eq, mul_sum]
    have hqfilter :
        (range (s.B+1)).filter (fun q => j≤q ∧ q+(i+δ)*c≤s.B) =
          Ico j (s.B+1-(i+δ)*c) := by
      ext q
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    simp only [hj, true_and]
    rw [← sum_filter, hqfilter]
  · simp [hj]
theorem gain_eq_compressed (s : Shape) (A h r d c v : ℕ) (hd : 0<d) :
    gain s A h r d c v =
      compressedPhase s A h r d c v 0 - compressedPhase s A h r d c v 1 := by
  have hbox (δ q : ℕ) :
      (∑ j ∈ range (s.J+1), boxPhase s A h r d c v δ q j) =
        ∑ j ∈ range (min q s.J+1), boxPhase s A h r d c v δ q j := by
    symm
    apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
    intro j hj hnot
    have hn : ¬ j≤q := by
      simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
      omega
    simp [boxPhase, hn]
  apply Nat.eq_sub_of_add_eq
  rw [← sum_boxPhase, ← sum_boxPhase]
  simp only [hbox, gain, shapeSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
  exact coordinate_phases s A h r d c v q j hd (Nat.le_of_lt_succ (mem_range.mp hq))
    (hj'.trans (min_le_left _ _)) (hj'.trans (min_le_right _ _))
#print axioms gain_eq_compressed
end Lower6960.HelperSource

end Merged_R6960HelperSourceArithmetic

end Merged6967_R6960HelperSourceArithmetic

section Merged6967_R6960Low6960SharedRational
set_option Elab.async false



set_option Elab.async false
set_option maxHeartbeats 800000
namespace Low6960SharedRational
noncomputable section

open K1_13 (Geom Row)
open K1_13_3 (symbolAt)
open K1_13_6 (GenericField GeoField genericCoeffs toGeneric)
open Polynomial MvPolynomial
open scoped BigOperators nonZeroDivisors

abbrev FractionJet := MvPolynomial (Fin 4) GenericField

def toFraction (P : Row 4) : FractionJet :=
  MvPolynomial.map (algebraMap (Polynomial Geom) GenericField) P

def toGeometric : FractionJet →+* K1_13_6.GeoJets :=
  MvPolynomial.map (algebraMap GenericField GeoField)

theorem fraction_geometric (P : Row 4) :
    toGeometric (toFraction P) = toGeneric P := by
  simp [toGeometric,toFraction,toGeneric,genericCoeffs,MvPolynomial.map_map]

theorem fraction_injective : Function.Injective toFraction :=
  MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial Geom) _)

theorem support_fraction (P : Row 4) : (toFraction P).support = P.support :=
  MvPolynomial.support_map_of_injective P (IsFractionRing.injective (Polynomial Geom) GenericField)

private theorem primitive_relation {ι : Type*} (s : Finset ι) (c : ι → (Polynomial Geom))
    (e : ι → Row 4) (h : ∑ i ∈ s, c i • e i = 0)
    (hne : ∃ i ∈ s, c i ≠ 0) (x : Geom) :
    ∃ b : ι → (Polynomial Geom), (∑ i ∈ s, b i • e i = 0) ∧ ∃ i ∈ s, (b i).eval x ≠ 0 := by
  classical
  let S := s.filter fun i => c i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi, hc⟩ := hne
    exact ⟨i,Finset.mem_filter.mpr ⟨hi,hc⟩⟩
  obtain ⟨i,hi,hmin⟩ := S.exists_min_image (fun i => (c i).rootMultiplicity x) hS
  let k := (c i).rootMultiplicity x
  let D : (Polynomial Geom) := (Polynomial.X - Polynomial.C x)^k
  have hd : D ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)
  have hdiv (j : ι) : D ∣ c j ∨ j ∉ s := by
    by_cases hzero : c j = 0
    · exact Or.inl (hzero.symm ▸ dvd_zero D)
    · by_cases hs : j ∈ s
      · exact Or.inl ((pow_dvd_pow _ (hmin j (Finset.mem_filter.mpr ⟨hs,hzero⟩))).trans
          (Polynomial.pow_rootMultiplicity_dvd _ _))
      · exact Or.inr hs
  have hclear (j : ι) : ∃ b : (Polynomial Geom), j ∈ s → c j = D*b := by
    rcases hdiv j with ⟨b,hb⟩ | hno
    · exact ⟨b,fun _ => hb⟩
    · exact ⟨0,fun hyes => (hno hyes).elim⟩
  choose b hb using hclear
  have hii := Finset.mem_filter.mp hi
  have hsum : D • (∑ j ∈ s, b j • e j) = 0 := by
    rw [Finset.smul_sum]
    refine (Finset.sum_congr rfl fun j hj => ?_).trans h
    rw [smul_smul,← hb j hj]
  have hz : ∑ j ∈ s, b j • e j = 0 := (smul_eq_zero.mp hsum).resolve_left hd
  refine ⟨b,hz,i,hii.1,?_⟩
  intro he
  obtain ⟨P,hP⟩ := (Polynomial.dvd_iff_isRoot).mpr he
  have hnot : ¬ (Polynomial.X - Polynomial.C x)^(k+1) ∣ c i :=
    Polynomial.pow_rootMultiplicity_not_dvd hii.2 x
  apply hnot
  refine ⟨P, ?_⟩
  calc
    c i = D * b i := hb i hii.1
    _ = _ := by rw [hP]; dsimp only [D]; rw [pow_succ,mul_assoc]


/-- Specialization independence implies function-field independence. -/
theorem independent_fraction {ι : Type*} (x : Geom) (e : ι → Row 4)
    (he : LinearIndependent Geom (fun i => symbolAt x (e i))) :
    LinearIndependent GenericField (fun i => toFraction (e i)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  let R := (Polynomial Geom)
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples (R⁰) s a
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hc (j : ι) : ∃ c : R, j ∈ s →
      algebraMap R GenericField c = algebraMap R GenericField d * a j := by
    by_cases hm : j ∈ s
    · obtain ⟨c,hc⟩ := hd j hm
      exact ⟨c,fun _ => hc.trans (Algebra.smul_def _ _)⟩
    · exact ⟨0,fun hj => (hm hj).elim⟩
  choose c hc using hc
  have hcleared : ∑ j ∈ s, c j • e j = 0 := by
    apply fraction_injective
    unfold toFraction
    simp only [map_sum,map_zero]
    calc
      _ = ∑ j ∈ s, (algebraMap R GenericField d * a j) •
          MvPolynomial.map (algebraMap R GenericField) (e j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have heq := hc j hj
        change algebraMap (Polynomial Geom) GenericField (c j) = _ at heq
        simp only [← MvPolynomial.C_mul', map_mul,MvPolynomial.map_C,heq]
        rw [mul_assoc]
      _ = (algebraMap R GenericField d) • ∑ j ∈ s, a j • toFraction (e j) := by
        rw [Finset.smul_sum]
        simp only [smul_smul, toFraction]
        rfl
      _ = 0 := by rw [ha,smul_zero]
  by_contra ha0
  have hc0 : c i ≠ 0 := by
    intro hz
    have heC := hc i hi
    rw [hz,map_zero] at heC
    have hNZ : algebraMap R GenericField d ≠ 0 := fun hz =>
      hd0 (IsFractionRing.injective R GenericField (hz.trans (map_zero _).symm))
    exact (mul_ne_zero hNZ ha0) heC.symm
  obtain ⟨b,hb,j,hj,hjx⟩ := primitive_relation s c e hcleared ⟨i,hi,hc0⟩ x
  have hx : ∑ j ∈ s, (b j).eval x • symbolAt x (e j) = 0 := by
    have hs := congrArg (symbolAt x) hb
    simp only [map_sum,map_zero,← MvPolynomial.C_mul',map_mul] at hs
    change (∑ j ∈ s, (evalRingHom x) (b j) • symbolAt x (e j)) = 0
    simpa only [symbolAt, MvPolynomial.map_C, MvPolynomial.C_mul'] using hs
  exact hjx (linearIndependent_iff'.mp he s (fun j => (b j).eval x) hx j hj)

theorem clear_denominators (R : FractionJet) :
    ∃ (d : (Polynomial Geom)) (Q : Row 4), d ≠ 0 ∧ Q.support = R.support ∧
      toFraction Q = MvPolynomial.C (algebraMap (Polynomial Geom) GenericField d) * R := by
  classical
  let M := nonZeroDivisors ((Polynomial Geom))
  let d := IsLocalization.commonDenom M R.support R.coeff
  let num := IsLocalization.integerMultiple M R.support R.coeff
  let Q : Row 4 := ∑ a : ↥R.support, MvPolynomial.monomial a.val (num a)
  have hd : (d : (Polynomial Geom)) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : algebraMap (Polynomial Geom) GenericField (d : (Polynomial Geom)) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericField)).mpr hd
  have hQ : toFraction Q = MvPolynomial.C (algebraMap (Polynomial Geom) GenericField d) * R := by
    unfold toFraction
    ext m
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, Q, MvPolynomial.coeff_sum]
    by_cases hm : m ∈ R.support
    · let a : ↥R.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M R.support R.coeff a
        change algebraMap (Polynomial Geom) GenericField (num a) = (d : (Polynomial Geom)) • R.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [MvPolynomial.coeff_monomial, hb]
    · have hz : R.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥R.support,
          (MvPolynomial.monomial a.val (num a) : Row 4).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [MvPolynomial.coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  refine ⟨d, Q, hd, ?_, hQ⟩
  rw [← support_fraction Q, hQ]
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, hi]

#print axioms clear_denominators
#print axioms independent_fraction
end
end Low6960SharedRational

end Merged6967_R6960Low6960SharedRational

section Merged6967_R6960Low6960SurfaceLinearFour
set_option Elab.async false







set_option Elab.async false

-- merged module R6960Low6960Inventory
section Merged_R6960Low6960Inventory

-- merged module Euler50Price
section Merged_Euler50Price

set_option Elab.async false
namespace Euler50Price
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement : ℕ := 179925
abbrev physicalDegree : ℕ := 133438
abbrev taylorLength : ℕ := physicalDegree + 1

def ActiveFits (f : Row 4) (K : ℕ) : Prop :=
  ∀ m ∈ f.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ K




structure Messages (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩

abbrev BentCap := Shape × ℕ


def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))





def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]



def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))







end
end Euler50Price

end Merged_Euler50Price

-- merged module Euler50GeoCover
section Merged_Euler50GeoCover
set_option Elab.async false
namespace Euler50GeoLead
open K1_13 (Geom Row shape indexDegree)
open K1_13_1 (topView topView_degree anchorLead anchorLead_ne indexDegree_eq)
open MvPolynomial
open scoped Polynomial
theorem term_weight (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, ∀ w : Fin 4 → ℕ,
      m.weight (fun i => w i.castSucc) + (shape P).t * w 3 = u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m :=
    (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, fun w => ?_⟩
  let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
  have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
    · simp [w']
  have hweight : (m.optionElim k).weight w' = u.weight w := by
    rw [← he]
    simp only [Finsupp.weight_apply, smul_eq_mul]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  rw [Finsupp.weight_optionElim] at hweight
  simpa only [w', Option.elim, k, topView_degree, smul_eq_mul, Nat.add_comm, Nat.mul_comm] using hweight
theorem lead_degree (P : Row 4) (hP : P ≠ 0) :
    (anchorLead P).totalDegree + (shape P).t ≤ P.totalDegree := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ ((support_nonempty.mpr (anchorLead_ne hP))) (fun m => m.weight (1 : Fin 3 → ℕ))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  have h := (hw (1 : Fin 4 → ℕ)).le.trans (le_weightedTotalDegree _ hu)
  rw [← weightedTotalDegree_one, weightedTotalDegree, he, ← weightedTotalDegree_one]
  have hconst : (fun i : Fin 3 => (1 : Fin 4 → ℕ) i.castSucc) = (1 : Fin 3 → ℕ) := rfl
  rw [hconst] at h
  simpa only [Pi.one_apply, Nat.mul_one] using h
theorem lead_index (P : Row 4) (hP : P ≠ 0) :
    indexDegree (anchorLead P) + 3 * (shape P).t ≤ indexDegree P := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr (anchorLead_ne hP)) (fun m => m.weight (fun i : Fin 3 => i.val))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  rw [indexDegree_eq, weightedTotalDegree, he, indexDegree_eq]
  simpa [Nat.mul_comm] using (hw (fun i => i.val)).le.trans (le_weightedTotalDegree _ hu)
end Euler50GeoLead
namespace Euler50GeoCover
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open Euler50Price (  physicalDegree    ActiveFits)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
def activeDegree (f : Row 4) : ℕ :=
  MvPolynomial.weightedTotalDegree (![1, 2, 2, 2] : Fin 4 → ℕ) f
private theorem activeWeight_at (m : Fin 4 →₀ ℕ) :
    m.weight (![1, 2, 2, 2] : Fin 4 → ℕ) = m 0 + 2*m 1 + 2*m 2 + 2*m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, Nat.mul_comm]
theorem activeFits_iff (f : Row 4) (K : ℕ) : ActiveFits f K ↔ activeDegree f ≤ K := by
  unfold ActiveFits activeDegree MvPolynomial.weightedTotalDegree
  rw [Finset.sup_le_iff]
  simp only [activeWeight_at]
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
end FactorCover
end
end Euler50GeoCover

end Merged_Euler50GeoCover

-- merged module Final50GeoCover
section Merged_Final50GeoCover

set_option Elab.async false
namespace Final50GeoCover
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open Final50Price (TrueWeightLE anchorCutoff physicalDegree Fits  SmallFactor ActiveFits)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)

abbrev activeDegree := Euler50GeoCover.activeDegree

theorem activeFits_iff (f : Row 4) (K : ℕ) : ActiveFits f K ↔ activeDegree f ≤ K :=
  Euler50GeoCover.activeFits_iff f K

theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
end FactorCover

end
end Final50GeoCover

end Merged_Final50GeoCover

-- merged module KoalaRetainedWitness
section Merged_KoalaRetainedWitness
set_option autoImplicit false
set_option Elab.async false
namespace KoalaRetainedCut
noncomputable section
open MvPolynomial
open K1_13 (Row Geom Shape shape InBox OrderAt atJet extend embed indexDegree)
open Final50Price (primaryBox primaryCutoff TrueWeightLE ActiveFits physicalDegree)
open P0_9_3_2 (translateTop topHasse topHasse_zero topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order exact_hasse_not_dvd)
open scoped Polynomial BigOperators
def residualBox (h : Shape) (l : ℕ) : Shape :=
  ⟨primaryBox.b-l*h.b, primaryBox.j-l*h.j, primaryBox.t-l*h.t⟩
private theorem wdegree_pow (w : Fin 4 → ℕ) {H : Row 4} (hn : H ≠ 0) (k : ℕ) :
    (H^k).weightedTotalDegree w = k*H.weightedTotalDegree w := by
  induction k with
  | zero => rw [pow_zero,zero_mul,← MvPolynomial.C_1,weightedTotalDegree_C]
  | succ k ih => rw [pow_succ,weightedTotalDegree_mul _ _ _ (pow_ne_zero k hn) hn,ih,Nat.succ_mul]
theorem residual_box {H G : Row 4} {v l : ℕ} (hv : l ≤ v)
    (hH : H ≠ 0) (hG : G ≠ 0) (hb : InBox (shape (H^v*G)) primaryBox) :
    InBox (shape G) (residualBox (shape H) l) := by
  have bound (w : Fin 4 → ℕ) {cap : ℕ} (hc : (H^v*G).weightedTotalDegree w ≤ cap) :
      G.weightedTotalDegree w ≤ cap - l*H.weightedTotalDegree w := by
    rw [weightedTotalDegree_mul _ _ _ (pow_ne_zero v hH) hG,wdegree_pow _ hH] at hc
    have hs := Nat.mul_le_mul_right (H.weightedTotalDegree w) hv
    omega
  have hb₁ : (H^v*G).totalDegree ≤ primaryBox.b := hb.1
  have hb₂ : indexDegree (H^v*G) ≤ primaryBox.j := hb.2.1
  have hb₃ : (H^v*G).degreeOf 3 ≤ primaryBox.t := hb.2.2
  rw [← weightedTotalDegree_one] at hb₁
  rw [K1_13_1.indexDegree_eq] at hb₂
  rw [← weightedTotalDegree_piSingle] at hb₃
  refine ⟨?_, ?_, ?_⟩
  · change G.totalDegree ≤ primaryBox.b-l*H.totalDegree
    simpa only [weightedTotalDegree_one] using bound (1 : Fin 4 → ℕ) hb₁
  · change indexDegree G ≤ primaryBox.j-l*indexDegree H
    simpa only [← K1_13_1.indexDegree_eq] using bound Fin.val hb₂
  · change G.degreeOf 3 ≤ primaryBox.t-l*H.degreeOf 3
    simpa only [weightedTotalDegree_piSingle] using bound (Pi.single (3 : Fin 4) 1) hb₃
private theorem weight_of_factor {P G : Row 4} {D : ℕ} (hP : P ≠ 0) (hG : G ∣ P)
    (hw : TrueWeightLE P D) : TrueWeightLE G D := by
  let e := MvPolynomial.optionEquivRight Geom (Fin 4)
  have hd := map_dvd e.symm.toRingHom hG
  have hn : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
  exact (Final50GeoCover.trueWeight_iff G).mpr <|
    (weightedTotalDegree_le_of_dvd _ hd hn).trans ((Final50GeoCover.trueWeight_iff P).mp hw)
private theorem topHasse_bounds (box : Shape) (T a : ℕ) (P : Row 4)
    (hb : InBox (shape P) box) (hw : TrueWeightLE P T) :
    InBox (shape (topHasse a P)) box ∧ TrueWeightLE (topHasse a P) T := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ box.b
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change indexDegree (topHasse a P) ≤ box.j
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Fin 4 →₀ ℕ => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change (topHasse a P).degreeOf 3 ≤ box.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hc := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : (Polynomial Geom))) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hc
    exact (Nat.add_le_add_right hc _).trans ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hp)
private theorem topHasse_one_not_dvd (f : Row 4) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 3) (hsmall : f.degreeOf 3 < K1.p) : ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : (Polynomial Geom)) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega
theorem exists_divided_cut {P H f : Row 4} {k a l A : ℕ} (hP : P ≠ 0) (hH : H ≠ 0)
    (hf : Irreducible f) (htop : 0 < f.degreeOf 3) (hchar : f.degreeOf 3 < K1.p)
    (hc : IsRelPrime f H) (hl : l ≤ k-a)
    (hb : InBox (shape P) primaryBox) (hw : TrueWeightLE P primaryCutoff)
    (hactive : ActiveFits P A) (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) (residualBox (shape H) l) ∧
      TrueWeightLE Q primaryCutoff ∧ ActiveFits Q A ∧
      ∀ S : (Polynomial Geom), atJet H S ≠ 0 → OrderAt P S k → OrderAt Q S l := by
  obtain ⟨G,rfl⟩ := divH
  have hn : G ≠ 0 := right_ne_zero_of_mul hP
  have hGb := residual_box (hl.trans (Nat.sub_le k a)) hH hn hb
  have hGw := weight_of_factor hP (dvd_mul_left G (H^k)) hw
  have hdiv : f^a ∣ G := hc.pow.dvd_of_dvd_mul_left divF
  have hnext : ¬ f^(a+1) ∣ G := fun hd => exactF (hd.trans (dvd_mul_left G _))
  have hnd := exact_hasse_not_dvd translateTop topHasse_zero f G a
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
    (topHasse_one_not_dvd f hf htop hchar) hdiv hnext
  obtain ⟨boxQ,weightQ⟩ := topHasse_bounds _ _ a G hGb hGw
  have hactiveG : ActiveFits G A := (Final50GeoCover.activeFits_iff G A).mpr
    ((weightedTotalDegree_le_of_dvd _ (dvd_mul_left G (H^k)) hP).trans
      ((Final50GeoCover.activeFits_iff _ A).mp hactive))
  have hactiveQ : ActiveFits (topHasse a G) A := by
    intro m hm
    have hh := hactiveG _ (source_support hm)
    simp [Finsupp.add_apply] at hh
    omega
  refine ⟨topHasse a G,hnd,boxQ,weightQ,hactiveQ,?_⟩
  intro S hS hPS m hm
  have hor := orderAt_off_quotient hS hPS
  exact hl.trans (topHasse_order a k G S hor m hm)
theorem retained_power_dvd {ι : Type*} [Fintype ι] [DecidableEq ι] (z : Finset ι)
    (f : ι → Row 4) (hfi : ∀ i, Irreducible (f i))
    (hdis : ∀ i j, i ≠ j → ¬ Associated (f i) (f j))
    {P : Row 4} {k : ℕ} (hdiv : ∀ i ∈ z, f i ^ k ∣ P) : (∏ i ∈ z, f i)^k ∣ P := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro i _ j _ hij
    exact ((hfi i).isRelPrime_iff_not_dvd.mpr
      (fun hd => hdis i j hij ((hfi i).associated_of_dvd (hfi j) hd))).pow
  · exact hdiv
theorem prime_off_product {ι : Type*} [DecidableEq ι] (z : Finset ι)
    (f : ι → Row 4) (hfi : ∀ i, Irreducible (f i))
    (hdis : ∀ i j, i ≠ j → ¬ Associated (f i) (f j))
    {i : ι} (hi : i ∉ z) : IsRelPrime (f i) (∏ j ∈ z, f j) := by
  apply IsRelPrime.prod_right
  intro j hj
  exact (hfi i).isRelPrime_iff_not_dvd.mpr
    (fun hd => hdis i j (fun eq => hi (eq ▸ hj)) ((hfi i).associated_of_dvd (hfi j) hd))
#print axioms residual_box
#print axioms exists_divided_cut
#print axioms retained_power_dvd
end
end KoalaRetainedCut

end Merged_KoalaRetainedWitness

-- merged module KoalaRetainedCover
section Merged_KoalaRetainedCover
set_option autoImplicit false
set_option Elab.async false
namespace KoalaRetainedCut
noncomputable section
open P3 (K)
open K1_13 (Geom Row shape topLead atJet jet extend OnFactor)
open K1_13_1 (anchorLead anchorLead_mul eval_anchorLead atJet_eq_anchorLead_of_top_zero)
open UniqueFactorizationMonoid MvPolynomial
open scoped Polynomial BigOperators
theorem anchor_factors {P : Row 4} (hP : P ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → Row 4),
      (∀ i, Irreducible (f i) ∧ 0 < (shape (f i)).t ∧ f i ∣ P) ∧
      (∀ i j, i ≠ j → ¬ Associated (f i) (f j)) ∧ (∏ i, f i) ∣ P ∧
      ∀ S : (Polynomial Geom), atJet P S = 0 → atJet (anchorLead P) S = 0 ∨ ∃ i, OnFactor (f i) S := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT (q) (hq : q ∈ T) : q ∈ A ∧ 0 < (shape q).t := by simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  refine ⟨n,f,fun i => ⟨irreducible_of_normalized_factor _ (hfi i).1,(hfi i).2,
    dvd_of_mem_normalizedFactors (hfi i).1⟩,?_,?_,?_⟩
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  · intro S hz
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : MvPolynomial.eval (jet S) A.prod = 0 := by
      have hdiv := _root_.map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ MvPolynomial.eval (jet S) A.prod at hdiv
      rw [hz,zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hSA
    obtain ⟨q,hq,hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R,hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR,anchorLead_mul,atJet,map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq,hqt⟩
    let j := e.symm ⟨q,hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q,hqT⟩)
    exact ⟨j,by rw [hj,OnFactor,← eval_anchorLead]; exact ⟨hqS,hqlead⟩⟩
theorem topLead_off_lower {P f : Row 4} {S : (Polynomial Geom)} (h : f ∣ P)
    (hoff : atJet (anchorLead P) S ≠ 0) : topLead f S ≠ 0 := by
  obtain ⟨G,rfl⟩ := h
  rw [anchorLead_mul,atJet,map_mul] at hoff
  rw [← eval_anchorLead]
  exact left_ne_zero_of_mul hoff
theorem priority_pieces {n : ℕ} {P : Row 4} {f : Fin n → Row 4} (hdiv : ∀ i, f i ∣ P)
    {Γ : Finset K} (s : K → (Polynomial K)) (book : Finset K) (z : Finset (Fin n))
    (hbase : ∀ γ ∈ Γ, atJet (anchorLead P) (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))) :
    ∃ (low : Finset K) (piece : Fin n → Finset K),
      low ⊆ Γ ∧ (∀ γ ∈ low, atJet (anchorLead P) (extend (s γ)) = 0) ∧
      (∀ i, piece i ⊆ Γ) ∧ (∀ i γ, γ ∈ piece i → γ ∉ book ∧ OnFactor (f i) (extend (s γ))) ∧
      (∀ i ∉ z, ∀ γ ∈ piece i, atJet (∏ j ∈ z, f j) (extend (s γ)) ≠ 0) ∧
      Γ.card ≤ book.card + low.card + ∑ i, (piece i).card := by
  classical
  let S (γ : K) := extend (s γ)
  let H := ∏ j ∈ z, f j
  let low := Γ.filter (fun γ => atJet (anchorLead P) (S γ)=0)
  let piece (i : Fin n) := Γ.filter (fun γ => γ∉book ∧ OnFactor (f i) (S γ) ∧
    (i∈z ∨ atJet H (S γ) ≠ 0))
  refine ⟨low,piece,Finset.filter_subset _ _,fun γ h => (Finset.mem_filter.mp h).2,
    fun i => Finset.filter_subset _ _,fun i _ h => ⟨(Finset.mem_filter.mp h).2.1,
      (Finset.mem_filter.mp h).2.2.1⟩,fun i hi _ h => (Finset.mem_filter.mp h).2.2.2.resolve_left hi,?_⟩
  have full : Γ ⊆ book ∪ low ∪ Finset.univ.biUnion piece := by
    intro γ hγ
    by_cases hb : γ∈book
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    by_cases hg : atJet (anchorLead P) (S γ)=0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ,hg⟩))
    apply Finset.mem_union_right
    by_cases hH : atJet H (S γ)=0
    · have hp : ∏ j∈z, atJet (f j) (S γ) = 0 := by
        simpa only [H,atJet,map_prod] using hH
      obtain ⟨i,hi,hzero⟩ := Finset.prod_eq_zero_iff.mp hp
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hb,⟨hzero,topLead_off_lower (hdiv i) hg⟩,Or.inl hi⟩⟩
    · obtain ⟨i,hon⟩ := (hbase γ hγ).resolve_left hg
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hb,hon,Or.inr hH⟩⟩
  exact (Finset.card_le_card full).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le))
#print axioms anchor_factors
#print axioms priority_pieces
end
end KoalaRetainedCut

end Merged_KoalaRetainedCover

-- merged module R6960Low6960Inventory
section Merged_R6960Low6960Inventory
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.Low
noncomputable section
open Finset Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open K1_13 (Geom extend Row Shape shape InBox atJet indexDegree OnFactor)
open K1_13_1 (anchorLead anchorLead_ne indexDegree_eq)
open Final50Price (ActiveFits)
open Final50GeoCover (activeDegree activeFits_iff)
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
open scoped BigOperators Polynomial Classical
abbrev anchorCutoff : ℕ := 101*agreement-1+57
def fullCap (top : ℕ) : Shape := ⟨136, 57, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 136 ∧ (∑ i, (a i).j) ≤ 57 ∧
    (∑ i, (a i).t) ≤ top
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g≠0 ∧ g.totalDegree≤136-top ∧ indexDegree g≤57-3*top ∧ TrueWeightLE g anchorCutoff
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0<(shape f).t ∧ InBox (shape f) (fullCap 14) ∧ TrueWeightLE f anchorCutoff
theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨136, 57, 14⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (shape P).t (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · have hb := (Euler50GeoLead.lead_degree P hP).trans hbox.1
    change (anchorLead P).totalDegree + (shape P).t ≤ 136 at hb
    change (anchorLead P).totalDegree ≤ 136 - (shape P).t
    omega
  · have hj := (Euler50GeoLead.lead_index P hP).trans hbox.2.1
    change indexDegree (anchorLead P) + 3 * (shape P).t ≤ 57 at hj
    change indexDegree (anchorLead P) ≤ 57 - 3 * (shape P).t
    omega
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨136, 57, 14⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
end FactorCover
structure Inventory (Γ : Finset K) (s : K→(Polynomial K)) where
  top : ℕ
  top_le : top≤14
  g : Row 3
  lower : LowerRow top g
  low : Finset K
  low_sub : low⊆Γ
  low_vanish : ∀ γ∈low,atJet g (extend (s γ))=0
  n : ℕ
  factor : Fin n→Row 4
  small : ∀ i,SmallFactor (factor i)
  different : ∀ i j,i≠j → ¬Associated (factor i) (factor j)
  fits : Fits top (fun i=>shape (factor i))
  active : (∑ i,activeDegree (factor i))≤169
  order : Fin n→ℕ
  layers : LayerBudget (fun i=>shape (factor i)) order
  proper : ∀ i,0<order i → ProperCut (factor i) Γ s (order i)
  zeros : Finset (Fin n)
  zero_iff : ∀ i,i∈zeros ↔ order i=0
  retained : zeros=∅ ∨ (Low6960Retained.Box (Low6960Retained.combined (fun i=>shape (factor i)) zeros) ∧
    1≤(Low6960Retained.combined (fun i=>shape (factor i)) zeros).t ∧
    (Low6960Retained.combined (fun i=>shape (factor i)) zeros).t≤2)
  pieces : Fin n→Finset K
  piece_sub : ∀ i,pieces i⊆Γ
  on_factor : ∀ i γ,γ∈pieces i → OnFactor (factor i) (extend (s γ))
  off_retained : ∀ i∉zeros,∀ γ∈pieces i,atJet (∏ j∈zeros,factor j) (extend (s γ))≠0
  book : Finset K
  book_cap : book.card≤140000
  fat : Low6960Fat.FatEquations
  fat_at : ∀ i γ,γ∈pieces i → Low6960Fat.Holds fat (extend (s γ))
  cover_count : Γ.card ≤ book.card+low.card+∑ i,(pieces i).card
theorem inventory_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179818 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2358) :
    Nonempty (Inventory Γ F.scalar) := by
  obtain ⟨P,hP,hbox,hact,weight,vanish⟩ := Low6960Anchor.anchor_of_family M F hi
  have hw : TrueWeightLE P anchorCutoff := by
    apply (trueWeight_iff P).mpr
    rw [← differentialWeight_eq,←differentialWeightedDegree]
    exact weight
  obtain ⟨n,f,factors,different,prodDvd,covers⟩ := KoalaRetainedCut.anchor_factors hP
  let top := (shape P).t
  have htop : top≤14 := hbox.2.2
  have small (i : Fin n) : SmallFactor (f i) := factor_small hP hbox hw
    (factors i).1 (factors i).2.1 (factors i).2.2
  have fits : Fits top (fun i => shape (f i)) := by
    refine ⟨fun i => ⟨(factors i).2.1,index_bounds (f i)⟩,?_,?_,?_⟩
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP prodDvd
      simp only [MvPolynomial.weightedTotalDegree_one] at h
      exact h.trans hbox.1
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd Fin.val Finset.univ f hP prodDvd
      simp only [← indexDegree_eq] at h
      exact h.trans hbox.2.1
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP prodDvd
      change (∑ i, (f i).degreeOf 3) ≤ P.degreeOf 3
      simpa only [MvPolynomial.weightedTotalDegree_piSingle] using h
  have active : (∑ i, activeDegree (f i)) ≤ 169 :=
    (MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ)
      Finset.univ f hP prodDvd).trans ((activeFits_iff P 169).mp hact)
  have hchar (i : Fin n) : (shape (f i)).t<K1.p := (small i).2.2.1.2.2.trans_lt (by decide)
  have hm := Low6960Order.messages_of_family M F hi
  obtain ⟨ord,layers,proper⟩ := Low6960Order.proper_layers hm (fun i=>(small i).1)
    (fun i=>(small i).2.1) hchar different
  let zeros := (univ : Finset (Fin n)).filter fun i=>ord i=0
  have zero_iff (i : Fin n) : i∈zeros ↔ ord i=0 := by simp [zeros]
  have retained := Low6960Retained.no_cut_shape _ _ fits.1 layers zeros
    (fun i hi=>(zero_iff i).mp hi)
  obtain ⟨book,E,booked,fat⟩ := fat_of_family M F lo hi
  obtain ⟨low,piece,lowSub,lowOn,sub,on,off,total⟩ := KoalaRetainedCut.priority_pieces
    (fun i => (factors i).2.2) F.scalar book zeros (fun γ hγ => covers _ (vanish γ hγ))
  exact ⟨⟨top,htop,K1_13_1.anchorLead P,lower_of_anchor P hP hbox hw,low,lowSub,lowOn,
    n,f,small,different,fits,active,ord,layers,proper,zeros,zero_iff,retained,piece,sub,
    (fun i γ hγ=>(on i γ hγ).2),off,book,booked,E,(fun i γ hγ=>fat γ (sub i hγ) (on i γ hγ).1),total⟩⟩
#print axioms inventory_of_family
end
end Lower6960.Low

end Merged_R6960Low6960Inventory

end Merged_R6960Low6960Inventory

-- merged module R6960Low6960Monotone
section Merged_R6960Low6960Monotone

-- merged module Final50FatReserve
section Merged_Final50FatReserve
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace Final50FatReserve
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open Final50Price (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)
private def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
private abbrev divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
private def divisorCut (h : Shape) : Shape :=
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
private def divisorFee (p h : Shape) (md mp : ℕ) : ℕ :=
  ceilDiv (Final50Price.errors * md) (32 * incidenceGap) + ceilDiv mp 32 +
    20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
private def singularFee (x : Shape) (ms : ℕ) : ℕ :=
  if 1 < x.t then ceilDiv (4 * x.t * ms) 32 + x.t * x.b ^ 2 + 1 else 0
private def curveFee (mc mq : ℕ) : ℕ :=
  let length := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  ceilDiv (Final50Price.errors * mc + incidenceGap * mq) (32 * incidenceGap * length)
private def isolatedFee : ℕ :=
  ceilDiv (3 * resultantBox.j ^ 2 * (2 * resultantBox.b - resultantBox.j))
    (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
private theorem fatPrice_expand (x : Shape) :
    fatPrice x =
      divisorFee x.chamber (fatChart x)
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) (fatChart x))
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) x.chamber) +
      singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) +
      curveFee (mixed32 x.chamber resultantBox resultantBox (fatChart x))
        (mixed32 x.chamber resultantBox resultantBox x.chamber) + isolatedFee := rfl
private theorem chamber_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE x.chamber y.chamber :=
  ⟨max_le_max h.1 h.2.1.le, h.2⟩
private theorem chart_widen (L : ℕ) {x y : Shape} (h : TotalLE x y) :
    TotalLE (chart L x) (chart L y) := by
  refine ⟨?_, by simp only [chart, h.2.1], by simp only [chart, h.2.1, h.2.2]⟩
  dsimp only [chart]
  rw [h.2.1]
  exact max_le_max
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h.1 _)) _) le_rfl
private theorem fatChart_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE (fatChart x) (fatChart y) := by
  have hp := chamber_widen h
  unfold fatChart
  rw [← h.2.2]
  split
  · refine ⟨?_, by simp only [linearChart, hp.2.1], by simp only [linearChart, hp.2.1]⟩
    dsimp only [linearChart]
    rw [hp.2.1]
    exact max_le_max
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hp.1 _)) _) le_rfl
  · exact chart_widen _ hp
private theorem cut_widen {h H : Shape} (hh : TotalLE h H) :
    TotalLE (divisorCut h) (divisorCut H) := by
  refine ⟨?_, by simp only [divisorCut, hh.2.1], by simp only [divisorCut, hh.2.2]⟩
  dsimp only [divisorCut]
  rw [hh.2.1]
  exact max_le_max (max_le_max hh.1 le_rfl) le_rfl
private theorem capped_index (b j t : ℕ) : IndexFits ⟨b, j, min t (j / 3)⟩ := by
  change 3 * min t (j / 3) ≤ j
  exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (by omega)
private theorem fatChart_index (x : Shape) : IndexFits (fatChart x) := by
  unfold fatChart
  split <;> exact capped_index _ _ _
private theorem cut_index {h : Shape} (hh : IndexFits h) : IndexFits (divisorCut h) := by
  change 3 * h.t ≤ h.j at hh
  change 3 * max 1 h.t ≤ max h.j (divisorBox.j + 1)
  rcases le_total 1 h.t with ht | ht
  · rw [max_eq_right ht]
    exact hh.trans (le_max_left _ _)
  · rw [max_eq_left ht]
    exact (show 3 * 1 ≤ divisorBox.j + 1 from by decide).trans (le_max_right _ _)
private theorem ceil_mono {a b l : ℕ} (h : a ≤ b) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h _) _)
theorem fatPrice_widen {x y : Shape} (h : TotalLE x y) (hv : IndexFits x) :
    fatPrice x ≤ fatPrice y := by
  have hp := chamber_widen h
  have hh := fatChart_widen h
  have hc := cut_widen hh
  have hp' : IndexFits x.chamber := hv
  have hh' := fatChart_index x
  have hc' := cut_index hh'
  have hbig : IndexFits divisorBox := Nat.zero_le _
  have hq : IndexFits resultantBox := Nat.zero_le _
  rw [fatPrice_expand x, fatPrice_expand y]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) le_rfl
  · have hd := mixed_mono_total hp (TotalLE.refl divisorBox) hc hh hp' hbig hc' hh'
    have hm := mixed_mono_total hp (TotalLE.refl divisorBox) hc hp hp' hbig hc' hp'
    dsimp only [divisorFee]
    refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_) le_rfl
    · exact ceil_mono (Nat.mul_le_mul_left _ hd)
    · exact ceil_mono hm
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1)
        (by simpa only [pow_two] using Nat.mul_le_mul hh.1 hh.1)
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1) hh.1
  · have hs := mixed_mono_total hp hp hh hh hp' hp' hh' hh'
    dsimp only [singularFee]
    rw [← h.2.2]
    split
    · exact Nat.add_le_add (Nat.add_le_add (ceil_mono (Nat.mul_le_mul_left _ hs))
        (Nat.mul_le_mul_left _ (by simpa only [pow_two] using Nat.mul_le_mul h.1 h.1))) le_rfl
    · exact le_rfl
  · have hc := mixed_mono_total hp (TotalLE.refl resultantBox) (TotalLE.refl resultantBox)
      hh hp' hq hq hh'
    have hm := mixed_mono_total hp (TotalLE.refl resultantBox) (TotalLE.refl resultantBox)
      hp hp' hq hq hp'
    exact ceil_mono (Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hm))
def degreeCap : ℕ → ℕ
  | 3 => 25
  | 4 => 23
  | 5 => 20
  | 6 => 16
  | 7 => 10
  | _ => 0
def charge (b j t : ℕ) : ℕ :=
  match t, j with
  | 1, 3 =>
    if b ≤ 1 then 2343347415003976
    else 16815154701363143
  | 1, 4 => 30532279541963794
  | 1, 5 => 46409127523914633
  | 1, 6 => 54064306903674190
  | 1, 7 => 48720018058055370
  | 2, 6 =>
    if b ≤ 3 then 78811583990757641
    else if b ≤ 11 then 135278860228783795
    else if b ≤ 13 then 158427079143371143
    else 193964641150607994
  | 2, 7 =>
    if b ≤ 6 then 143089016514969561
    else 194164445885822982
  | _, _ => 0
private theorem price_3_1_1 : fatPrice ⟨1,3,1⟩ ≤ charge 1 3 1 := by
  decide +kernel
private theorem price_3_1_25 : fatPrice ⟨25,3,1⟩ ≤ charge 25 3 1 := by
  decide +kernel
private theorem price_4_1_23 : fatPrice ⟨23,4,1⟩ ≤ charge 23 4 1 := by
  decide +kernel
private theorem price_5_1_20 : fatPrice ⟨20,5,1⟩ ≤ charge 20 5 1 := by
  decide +kernel
private theorem price_6_1_16 : fatPrice ⟨16,6,1⟩ ≤ charge 16 6 1 := by
  decide +kernel
private theorem price_7_1_10 : fatPrice ⟨10,7,1⟩ ≤ charge 10 7 1 := by
  decide +kernel
private theorem price_6_2_3 : fatPrice ⟨3,6,2⟩ ≤ charge 3 6 2 := by
  decide +kernel
private theorem price_6_2_11 : fatPrice ⟨11,6,2⟩ ≤ charge 11 6 2 := by
  decide +kernel
private theorem price_6_2_13 : fatPrice ⟨13,6,2⟩ ≤ charge 13 6 2 := by
  decide +kernel
private theorem price_6_2_16 : fatPrice ⟨16,6,2⟩ ≤ charge 16 6 2 := by
  decide +kernel
private theorem price_7_2_6 : fatPrice ⟨6,7,2⟩ ≤ charge 6 7 2 := by
  decide +kernel
private theorem price_7_2_10 : fatPrice ⟨10,7,2⟩ ≤ charge 10 7 2 := by
  decide +kernel
theorem single (x : Shape) (hv : Valid x) (hj : x.j ≤ 7) (hb : x.b ≤ degreeCap x.j) :
    fatPrice x ≤ charge x.b x.j x.t := by
  obtain ⟨b, j, t⟩ := x
  have hpos : 1 ≤ t := hv.1
  have hindex : 3 * t ≤ j := hv.2.1
  change j ≤ 7 at hj
  have htop : t = 1 ∨ t = 2 := by omega
  rcases htop with rfl | rfl
  · have hcases : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · by_cases hs1 : b ≤ 1
      · simpa [charge, hs1] using
          (fatPrice_widen (x := ⟨b,3,1⟩) (y := ⟨1,3,1⟩) ⟨hs1, rfl, rfl⟩ hindex).trans price_3_1_1
      · simpa [charge, hs1] using
          (fatPrice_widen (x := ⟨b,3,1⟩) (y := ⟨25,3,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_3_1_25
    · exact (fatPrice_widen (x := ⟨b,4,1⟩) (y := ⟨23,4,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_4_1_23
    · exact (fatPrice_widen (x := ⟨b,5,1⟩) (y := ⟨20,5,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_5_1_20
    · exact (fatPrice_widen (x := ⟨b,6,1⟩) (y := ⟨16,6,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_6_1_16
    · exact (fatPrice_widen (x := ⟨b,7,1⟩) (y := ⟨10,7,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_7_1_10
  · have hcases : j = 6 ∨ j = 7 := by omega
    rcases hcases with rfl | rfl
    · by_cases hs3 : b ≤ 3
      · simpa [charge, hs3] using
          (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨3,6,2⟩) ⟨hs3, rfl, rfl⟩ hindex).trans price_6_2_3
      · by_cases hs11 : b ≤ 11
        · simpa [charge, hs3, hs11] using
            (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨11,6,2⟩) ⟨hs11, rfl, rfl⟩ hindex).trans price_6_2_11
        · by_cases hs13 : b ≤ 13
          · simpa [charge, hs3, hs11, hs13] using
              (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨13,6,2⟩) ⟨hs13, rfl, rfl⟩ hindex).trans price_6_2_13
          · simpa [charge, hs3, hs11, hs13] using
              (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨16,6,2⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_6_2_16
    · by_cases hs6 : b ≤ 6
      · simpa [charge, hs6] using
          (fatPrice_widen (x := ⟨b,7,2⟩) (y := ⟨6,7,2⟩) ⟨hs6, rfl, rfl⟩ hindex).trans price_7_2_6
      · simpa [charge, hs6] using
          (fatPrice_widen (x := ⟨b,7,2⟩) (y := ⟨10,7,2⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_7_2_10
private def PairCap (j k cap : ℕ) : Prop :=
  (j + k = 6 ∧ (cap = 3 ∨ cap = 11 ∨ cap = 13 ∨ cap = 16)) ∨
  (j + k = 7 ∧ (cap = 6 ∨ cap = 10))
private theorem pair_endpoints (j k cap : ℕ) (hjk : 3 ≤ j ∧ 3 ≤ k ∧ j + k ≤ 7)
    (hcap : PairCap j k cap) :
    ∀ b : Fin (cap+1), j ≤ 3 * b.val → k ≤ 3 * (cap-b.val) →
      fatPrice ⟨b.val,j,1⟩ + fatPrice ⟨cap-b.val,k,1⟩ ≤ charge cap (j + k) 2 := by
  unfold PairCap at hcap
  have indices : (j = 3 ∧ k = 3) ∨ (j = 3 ∧ k = 4) ∨ (j = 4 ∧ k = 3) := by omega
  rcases indices with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have caps : cap = 3 ∨ cap = 11 ∨ cap = 13 ∨ cap = 16 := by omega
    rcases caps with rfl | rfl | rfl | rfl <;> decide +kernel
  · have caps : cap = 6 ∨ cap = 10 := by omega
    rcases caps with rfl | rfl <;> decide +kernel
  · have caps : cap = 6 ∨ cap = 10 := by omega
    rcases caps with rfl | rfl <;> decide +kernel
private theorem pair_width (j k cap : ℕ) (hjk : 3 ≤ j ∧ 3 ≤ k ∧ j + k ≤ 7)
    (hcap : PairCap j k cap)
    (b c : ℕ) (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ cap) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge cap (j + k) 2 := by
  have hc' : c ≤ cap-b := by omega
  have hck : k ≤ 3 * (cap-b) := hc.trans (Nat.mul_le_mul_left 3 hc')
  have hfee := fatPrice_widen (x := ⟨c,k,1⟩) (y := ⟨cap-b,k,1⟩) ⟨hc', rfl, rfl⟩ hjk.2.1
  exact (Nat.add_le_add_left hfee _).trans
    (pair_endpoints j k cap hjk hcap ⟨b, by omega⟩ hb hck)
theorem pair (b c j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) (hjk : j + k ≤ 7)
    (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ degreeCap (j+k)) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge (b+c) (j+k) 2 := by
  have indices : j + k = 6 ∨ j + k = 7 := by omega
  rcases indices with h | h
  · by_cases hs3 : b + c ≤ 3
    · have paid := pair_width j k 3 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs3
      simpa [charge, hs3, h] using paid
    · by_cases hs11 : b + c ≤ 11
      · have paid := pair_width j k 11 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs11
        simpa [charge, hs3, hs11, h] using paid
      · by_cases hs13 : b + c ≤ 13
        · have paid := pair_width j k 13 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs13
          simpa [charge, hs3, hs11, hs13, h] using paid
        · have paid := pair_width j k 16 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc (by simpa only [h, degreeCap] using hbc)
          simpa [charge, hs3, hs11, hs13, h] using paid
  · by_cases hs6 : b + c ≤ 6
    · have paid := pair_width j k 6 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs6
      simpa [charge, hs6, h] using paid
    · have paid := pair_width j k 10 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc (by simpa only [h, degreeCap] using hbc)
      simpa [charge, hs6, h] using paid
theorem family (n : ℕ) (a : Fin n → Shape) (hv : ∀ i, Valid (a i))
    (hj : (∑ i, (a i).j) ≤ 7)
    (hb : (∑ i, (a i).b) ≤ degreeCap (∑ i, (a i).j)) :
    (∑ i, fatPrice (a i)) ≤ charge (∑ i, (a i).b) (∑ i, (a i).j) (∑ i, (a i).t) := by
  have hsum : 3 * (∑ i, (a i).t) ≤ ∑ i, (a i).j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).2.1
  have hn' : n ≤ ∑ i, (a i).t := calc
    n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ i, (a i).t := Finset.sum_le_sum fun i _ => (hv i).1
  have hn : n ≤ 2 := by omega
  interval_cases n
  · simp [charge]
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    exact single _ (hv 0) hj hb
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0 := (hv 0).1
    have ht1 := (hv 1).1
    have h0 : (a 0).t = 1 := by omega
    have h1 : (a 1).t = 1 := by omega
    have he (i : Fin 2) : a i = ⟨(a i).b, (a i).j, (a i).t⟩ := by cases a i; rfl
    have hh := pair (a 0).b (a 1).b (a 0).j (a 1).j
      (by simpa only [h0] using (hv 0).2.1) (by simpa only [h1] using (hv 1).2.1)
      hj (hv 0).2.2 (hv 1).2.2 hb
    have ha0 : a 0 = ⟨(a 0).b, (a 0).j, 1⟩ :=
      (he 0).trans (congrArg (fun t => (⟨(a 0).b, (a 0).j, t⟩ : Shape)) h0)
    have ha1 : a 1 = ⟨(a 1).b, (a 1).j, 1⟩ :=
      (he 1).trans (congrArg (fun t => (⟨(a 1).b, (a 1).j, t⟩ : Shape)) h1)
    rw [h0, h1]
    simpa only [← ha0, ← ha1] using hh
#print axioms fatPrice_widen
#print axioms single
#print axioms pair
#print axioms family
end Final50FatReserve

end Merged_Final50FatReserve

-- merged module R6960Low6960RetainedFees
section Merged_R6960Low6960RetainedFees
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Lower6960.Low
open Finset
open K1_13 (Shape chart ceilDiv mixed32 shape)
open K1_13_8 (Valid)
open Low6960Fat (commonBox resultantBox)
open K1_13_8_4 (TotalLE)
open scoped BigOperators Classical
abbrev errors : ℕ := 262144-agreement
abbrev incidenceGap : ℕ := agreement-physicalDegree
abbrev taylorLength : ℕ := physicalDegree+1
abbrev fatOrder : ℕ := 23893
abbrev divisorOrder : ℕ := 22155
abbrev isolatedOrder : ℕ := 174
def lowDegreeCap : ℕ → ℕ
  | 3 => 26
  | 4 => 24
  | 5 => 21
  | 6 => 17
  | 7 => 12
  | 8 => 4
  | _ => 0
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (errors * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (errors * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated
def retainedTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 1952879554821531, 1952879554821531, 1952879554821531, 2264030333312493, 2582480582752554, 2910366730929716, 3249825205631977, 3602992434647339, 3972004845763800, 4358998866769362, 4766110925452023, 5195477449599785, 5649234867000646, 6129519605442608, 6638468092713669, 7178216756601831, 7750902024895092, 8358660325381453, 9003628085848914, 9687941734085476, 10413737697879137, 11183152405017899, 11998322283289760, 12861383760482722, 13774473264384783, 14739727222783944]
  | 4,1 => [0, 0, 4595623903046235, 4595623903046235, 4595623903046235, 5369691775899144, 6153195547489152, 6948271645604260, 7757056498032469, 8581686532561778, 9424298176980187, 10287027859075695, 11172012006636304, 12081387047450012, 13017289409304820, 13981855519988729, 14977221807289737, 16005524698995846, 17068900622895054, 18169486006775363, 19309417278424772, 20490830865631280, 21715863196182889, 22986650697867597, 24305329798473406]
  | 5,1 => [0, 0, 9797261559566592, 9797261559566592, 9797261559566592, 9797261559566592, 11239103013607327, 12692516794173162, 14159639329052097, 15642607046032133, 17143556372901268, 18664623737447503, 20207945567458838, 21775658290723275, 23369898335028810, 24992802128163445, 26646506097915180, 28333146672072016, 30054860278421951, 31813783344752986, 33612052298853121, 35451803568510358]
  | 6,1 => [0, 0, 17004859032909927, 17004859032909927, 17004859032909927, 17004859032909927, 17004859032909927, 19066433846681251, 21141717414765676, 23232846164951201, 25341956525025827, 27471184922777552, 29622667785994377, 31798541542464301, 34000942619975327, 36232007446315452, 38493872449272677, 40788674056635002]
  | 7,1 => [0, 0, 0, 26337331550252863, 26337331550252863, 26337331550252863, 26337331550252863, 26337331550252863, 29020776151542777, 31720065934933792, 34437337328213907, 37174726759171121, 39934370655593437]
  | 8,1 => [0, 0, 0, 37796815539383397, 37796815539383397]
  | 6,2 => [0, 0, 55462371369774712, 55462371369774722, 55462371369774736, 55462371369774754, 55462371369774776, 63291232093810052, 71174575000860732, 79120946314457695, 87138892258131824, 95236959055413996, 103423692929835092, 111707640104925991, 120097346804217575, 128601359251240723, 137228223669526315, 145986486282605231]
  | 7,2 => [0, 0, 0, 100206150776982578, 100206150776982592, 100206150776982610, 100206150776982632, 100206150776982658, 112072656565082685, 124002190759728996, 136003299584452471, 148084529262783989, 160254426018254432]
  | 8,2 => [0, 0, 0, 159588895902744113, 159588895902744127]
  | _,_ => []
def retainedTariff (b j t : ℕ) : ℕ := (retainedTariffs j t).getD b 0
def singleTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 1952879554821531, 1952879554821531, 1952879554821531, 2264030333312493, 2582480582752554, 2910366730929716, 3249825205631977, 3602992434647339, 3972004845763800, 4358998866769362, 4766110925452023, 5195477449599785, 5649234867000646, 6129519605442608, 6638468092713669, 7178216756601831, 7750902024895092, 8358660325381453, 9003628085848914, 9687941734085476, 10413737697879137, 11183152405017899, 11998322283289760, 12861383760482722, 13774473264384783, 14739727222783944]
  | 4,1 => [0, 0, 4595623903046235, 4595623903046235, 4595623903046235, 5369691775899144, 6153195547489152, 6948271645604260, 7757056498032469, 8581686532561778, 9424298176980187, 10287027859075695, 11172012006636304, 12081387047450012, 13017289409304820, 13981855519988729, 14977221807289737, 16005524698995846, 17068900622895054, 18169486006775363, 19309417278424772, 20490830865631280, 21715863196182889, 22986650697867597, 24305329798473406]
  | 5,1 => [0, 0, 9797261559566592, 9797261559566592, 9797261559566592, 9797261559566592, 11239103013607327, 12692516794173162, 14159639329052097, 15642607046032133, 17143556372901268, 18664623737447503, 20207945567458838, 21775658290723275, 23369898335028810, 24992802128163445, 26646506097915180, 28333146672072016, 30054860278421951, 31813783344752986, 33612052298853121, 35451803568510358]
  | 6,1 => [0, 0, 17004859032909927, 17004859032909927, 17004859032909927, 17004859032909927, 17004859032909927, 19066433846681251, 21141717414765676, 23232846164951201, 25341956525025827, 27471184922777552, 29622667785994377, 31798541542464301, 34000942619975327, 36232007446315452, 38493872449272677, 40788674056635002]
  | 7,1 => [0, 0, 0, 26337331550252863, 26337331550252863, 26337331550252863, 26337331550252863, 26337331550252863, 29020776151542777, 31720065934933792, 34437337328213907, 37174726759171121, 39934370655593437]
  | 8,1 => [0, 0, 0, 37796815539383397, 37796815539383397]
  | 6,2 => [0, 0, 55462371369774712, 55462371369774722, 55462371369774736, 55462371369774754, 55462371369774776, 63291232093810052, 71174575000860732, 79120946314457695, 87138892258131824, 95236959055413996, 103423692929835092, 111707640104925991, 120097346804217575, 128601359251240723, 137228223669526315, 145986486282605231]
  | 7,2 => [0, 0, 0, 100206150776982578, 100206150776982592, 100206150776982610, 100206150776982632, 100206150776982658, 112072656565082685, 124002190759728996, 136003299584452471, 148084529262783989, 160254426018254432]
  | 8,2 => [0, 0, 0, 159588895902744113, 159588895902744127]
  | _,_ => []
def singleTariff (b j t : ℕ) : ℕ := (singleTariffs j t).getD b 0
private theorem cell_1_3_1 : fatPrice ⟨1,3,1⟩ ≤ singleTariff 1 3 1 := by decide +kernel
private theorem cell_2_3_1 : fatPrice ⟨2,3,1⟩ ≤ singleTariff 2 3 1 := by decide +kernel
private theorem cell_3_3_1 : fatPrice ⟨3,3,1⟩ ≤ singleTariff 3 3 1 := by decide +kernel
private theorem cell_4_3_1 : fatPrice ⟨4,3,1⟩ ≤ singleTariff 4 3 1 := by decide +kernel
private theorem cell_5_3_1 : fatPrice ⟨5,3,1⟩ ≤ singleTariff 5 3 1 := by decide +kernel
private theorem cell_6_3_1 : fatPrice ⟨6,3,1⟩ ≤ singleTariff 6 3 1 := by decide +kernel
private theorem cell_7_3_1 : fatPrice ⟨7,3,1⟩ ≤ singleTariff 7 3 1 := by decide +kernel
private theorem cell_8_3_1 : fatPrice ⟨8,3,1⟩ ≤ singleTariff 8 3 1 := by decide +kernel
private theorem cell_9_3_1 : fatPrice ⟨9,3,1⟩ ≤ singleTariff 9 3 1 := by decide +kernel
private theorem cell_10_3_1 : fatPrice ⟨10,3,1⟩ ≤ singleTariff 10 3 1 := by decide +kernel
private theorem cell_11_3_1 : fatPrice ⟨11,3,1⟩ ≤ singleTariff 11 3 1 := by decide +kernel
private theorem cell_12_3_1 : fatPrice ⟨12,3,1⟩ ≤ singleTariff 12 3 1 := by decide +kernel
private theorem cell_13_3_1 : fatPrice ⟨13,3,1⟩ ≤ singleTariff 13 3 1 := by decide +kernel
private theorem cell_14_3_1 : fatPrice ⟨14,3,1⟩ ≤ singleTariff 14 3 1 := by decide +kernel
private theorem cell_15_3_1 : fatPrice ⟨15,3,1⟩ ≤ singleTariff 15 3 1 := by decide +kernel
private theorem cell_16_3_1 : fatPrice ⟨16,3,1⟩ ≤ singleTariff 16 3 1 := by decide +kernel
private theorem cell_17_3_1 : fatPrice ⟨17,3,1⟩ ≤ singleTariff 17 3 1 := by decide +kernel
private theorem cell_18_3_1 : fatPrice ⟨18,3,1⟩ ≤ singleTariff 18 3 1 := by decide +kernel
private theorem cell_19_3_1 : fatPrice ⟨19,3,1⟩ ≤ singleTariff 19 3 1 := by decide +kernel
private theorem cell_20_3_1 : fatPrice ⟨20,3,1⟩ ≤ singleTariff 20 3 1 := by decide +kernel
private theorem cell_21_3_1 : fatPrice ⟨21,3,1⟩ ≤ singleTariff 21 3 1 := by decide +kernel
private theorem cell_22_3_1 : fatPrice ⟨22,3,1⟩ ≤ singleTariff 22 3 1 := by decide +kernel
private theorem cell_23_3_1 : fatPrice ⟨23,3,1⟩ ≤ singleTariff 23 3 1 := by decide +kernel
private theorem cell_24_3_1 : fatPrice ⟨24,3,1⟩ ≤ singleTariff 24 3 1 := by decide +kernel
private theorem cell_25_3_1 : fatPrice ⟨25,3,1⟩ ≤ singleTariff 25 3 1 := by decide +kernel
private theorem cell_26_3_1 : fatPrice ⟨26,3,1⟩ ≤ singleTariff 26 3 1 := by decide +kernel
private theorem cell_2_4_1 : fatPrice ⟨2,4,1⟩ ≤ singleTariff 2 4 1 := by decide +kernel
private theorem cell_3_4_1 : fatPrice ⟨3,4,1⟩ ≤ singleTariff 3 4 1 := by decide +kernel
private theorem cell_4_4_1 : fatPrice ⟨4,4,1⟩ ≤ singleTariff 4 4 1 := by decide +kernel
private theorem cell_5_4_1 : fatPrice ⟨5,4,1⟩ ≤ singleTariff 5 4 1 := by decide +kernel
private theorem cell_6_4_1 : fatPrice ⟨6,4,1⟩ ≤ singleTariff 6 4 1 := by decide +kernel
private theorem cell_7_4_1 : fatPrice ⟨7,4,1⟩ ≤ singleTariff 7 4 1 := by decide +kernel
private theorem cell_8_4_1 : fatPrice ⟨8,4,1⟩ ≤ singleTariff 8 4 1 := by decide +kernel
private theorem cell_9_4_1 : fatPrice ⟨9,4,1⟩ ≤ singleTariff 9 4 1 := by decide +kernel
private theorem cell_10_4_1 : fatPrice ⟨10,4,1⟩ ≤ singleTariff 10 4 1 := by decide +kernel
private theorem cell_11_4_1 : fatPrice ⟨11,4,1⟩ ≤ singleTariff 11 4 1 := by decide +kernel
private theorem cell_12_4_1 : fatPrice ⟨12,4,1⟩ ≤ singleTariff 12 4 1 := by decide +kernel
private theorem cell_13_4_1 : fatPrice ⟨13,4,1⟩ ≤ singleTariff 13 4 1 := by decide +kernel
private theorem cell_14_4_1 : fatPrice ⟨14,4,1⟩ ≤ singleTariff 14 4 1 := by decide +kernel
private theorem cell_15_4_1 : fatPrice ⟨15,4,1⟩ ≤ singleTariff 15 4 1 := by decide +kernel
private theorem cell_16_4_1 : fatPrice ⟨16,4,1⟩ ≤ singleTariff 16 4 1 := by decide +kernel
private theorem cell_17_4_1 : fatPrice ⟨17,4,1⟩ ≤ singleTariff 17 4 1 := by decide +kernel
private theorem cell_18_4_1 : fatPrice ⟨18,4,1⟩ ≤ singleTariff 18 4 1 := by decide +kernel
private theorem cell_19_4_1 : fatPrice ⟨19,4,1⟩ ≤ singleTariff 19 4 1 := by decide +kernel
private theorem cell_20_4_1 : fatPrice ⟨20,4,1⟩ ≤ singleTariff 20 4 1 := by decide +kernel
private theorem cell_21_4_1 : fatPrice ⟨21,4,1⟩ ≤ singleTariff 21 4 1 := by decide +kernel
private theorem cell_22_4_1 : fatPrice ⟨22,4,1⟩ ≤ singleTariff 22 4 1 := by decide +kernel
private theorem cell_23_4_1 : fatPrice ⟨23,4,1⟩ ≤ singleTariff 23 4 1 := by decide +kernel
private theorem cell_24_4_1 : fatPrice ⟨24,4,1⟩ ≤ singleTariff 24 4 1 := by decide +kernel
private theorem cell_2_5_1 : fatPrice ⟨2,5,1⟩ ≤ singleTariff 2 5 1 := by decide +kernel
private theorem cell_3_5_1 : fatPrice ⟨3,5,1⟩ ≤ singleTariff 3 5 1 := by decide +kernel
private theorem cell_4_5_1 : fatPrice ⟨4,5,1⟩ ≤ singleTariff 4 5 1 := by decide +kernel
private theorem cell_5_5_1 : fatPrice ⟨5,5,1⟩ ≤ singleTariff 5 5 1 := by decide +kernel
private theorem cell_6_5_1 : fatPrice ⟨6,5,1⟩ ≤ singleTariff 6 5 1 := by decide +kernel
private theorem cell_7_5_1 : fatPrice ⟨7,5,1⟩ ≤ singleTariff 7 5 1 := by decide +kernel
private theorem cell_8_5_1 : fatPrice ⟨8,5,1⟩ ≤ singleTariff 8 5 1 := by decide +kernel
private theorem cell_9_5_1 : fatPrice ⟨9,5,1⟩ ≤ singleTariff 9 5 1 := by decide +kernel
private theorem cell_10_5_1 : fatPrice ⟨10,5,1⟩ ≤ singleTariff 10 5 1 := by decide +kernel
private theorem cell_11_5_1 : fatPrice ⟨11,5,1⟩ ≤ singleTariff 11 5 1 := by decide +kernel
private theorem cell_12_5_1 : fatPrice ⟨12,5,1⟩ ≤ singleTariff 12 5 1 := by decide +kernel
private theorem cell_13_5_1 : fatPrice ⟨13,5,1⟩ ≤ singleTariff 13 5 1 := by decide +kernel
private theorem cell_14_5_1 : fatPrice ⟨14,5,1⟩ ≤ singleTariff 14 5 1 := by decide +kernel
private theorem cell_15_5_1 : fatPrice ⟨15,5,1⟩ ≤ singleTariff 15 5 1 := by decide +kernel
private theorem cell_16_5_1 : fatPrice ⟨16,5,1⟩ ≤ singleTariff 16 5 1 := by decide +kernel
private theorem cell_17_5_1 : fatPrice ⟨17,5,1⟩ ≤ singleTariff 17 5 1 := by decide +kernel
private theorem cell_18_5_1 : fatPrice ⟨18,5,1⟩ ≤ singleTariff 18 5 1 := by decide +kernel
private theorem cell_19_5_1 : fatPrice ⟨19,5,1⟩ ≤ singleTariff 19 5 1 := by decide +kernel
private theorem cell_20_5_1 : fatPrice ⟨20,5,1⟩ ≤ singleTariff 20 5 1 := by decide +kernel
private theorem cell_21_5_1 : fatPrice ⟨21,5,1⟩ ≤ singleTariff 21 5 1 := by decide +kernel
private theorem cell_2_6_1 : fatPrice ⟨2,6,1⟩ ≤ singleTariff 2 6 1 := by decide +kernel
private theorem cell_3_6_1 : fatPrice ⟨3,6,1⟩ ≤ singleTariff 3 6 1 := by decide +kernel
private theorem cell_4_6_1 : fatPrice ⟨4,6,1⟩ ≤ singleTariff 4 6 1 := by decide +kernel
private theorem cell_5_6_1 : fatPrice ⟨5,6,1⟩ ≤ singleTariff 5 6 1 := by decide +kernel
private theorem cell_6_6_1 : fatPrice ⟨6,6,1⟩ ≤ singleTariff 6 6 1 := by decide +kernel
private theorem cell_7_6_1 : fatPrice ⟨7,6,1⟩ ≤ singleTariff 7 6 1 := by decide +kernel
private theorem cell_8_6_1 : fatPrice ⟨8,6,1⟩ ≤ singleTariff 8 6 1 := by decide +kernel
private theorem cell_9_6_1 : fatPrice ⟨9,6,1⟩ ≤ singleTariff 9 6 1 := by decide +kernel
private theorem cell_10_6_1 : fatPrice ⟨10,6,1⟩ ≤ singleTariff 10 6 1 := by decide +kernel
private theorem cell_11_6_1 : fatPrice ⟨11,6,1⟩ ≤ singleTariff 11 6 1 := by decide +kernel
private theorem cell_12_6_1 : fatPrice ⟨12,6,1⟩ ≤ singleTariff 12 6 1 := by decide +kernel
private theorem cell_13_6_1 : fatPrice ⟨13,6,1⟩ ≤ singleTariff 13 6 1 := by decide +kernel
private theorem cell_14_6_1 : fatPrice ⟨14,6,1⟩ ≤ singleTariff 14 6 1 := by decide +kernel
private theorem cell_15_6_1 : fatPrice ⟨15,6,1⟩ ≤ singleTariff 15 6 1 := by decide +kernel
private theorem cell_16_6_1 : fatPrice ⟨16,6,1⟩ ≤ singleTariff 16 6 1 := by decide +kernel
private theorem cell_17_6_1 : fatPrice ⟨17,6,1⟩ ≤ singleTariff 17 6 1 := by decide +kernel
private theorem cell_3_7_1 : fatPrice ⟨3,7,1⟩ ≤ singleTariff 3 7 1 := by decide +kernel
private theorem cell_4_7_1 : fatPrice ⟨4,7,1⟩ ≤ singleTariff 4 7 1 := by decide +kernel
private theorem cell_5_7_1 : fatPrice ⟨5,7,1⟩ ≤ singleTariff 5 7 1 := by decide +kernel
private theorem cell_6_7_1 : fatPrice ⟨6,7,1⟩ ≤ singleTariff 6 7 1 := by decide +kernel
private theorem cell_7_7_1 : fatPrice ⟨7,7,1⟩ ≤ singleTariff 7 7 1 := by decide +kernel
private theorem cell_8_7_1 : fatPrice ⟨8,7,1⟩ ≤ singleTariff 8 7 1 := by decide +kernel
private theorem cell_9_7_1 : fatPrice ⟨9,7,1⟩ ≤ singleTariff 9 7 1 := by decide +kernel
private theorem cell_10_7_1 : fatPrice ⟨10,7,1⟩ ≤ singleTariff 10 7 1 := by decide +kernel
private theorem cell_11_7_1 : fatPrice ⟨11,7,1⟩ ≤ singleTariff 11 7 1 := by decide +kernel
private theorem cell_12_7_1 : fatPrice ⟨12,7,1⟩ ≤ singleTariff 12 7 1 := by decide +kernel
private theorem cell_3_8_1 : fatPrice ⟨3,8,1⟩ ≤ singleTariff 3 8 1 := by decide +kernel
private theorem cell_4_8_1 : fatPrice ⟨4,8,1⟩ ≤ singleTariff 4 8 1 := by decide +kernel
private theorem cell_2_6_2 : fatPrice ⟨2,6,2⟩ ≤ singleTariff 2 6 2 := by decide +kernel
private theorem cell_3_6_2 : fatPrice ⟨3,6,2⟩ ≤ singleTariff 3 6 2 := by decide +kernel
private theorem cell_4_6_2 : fatPrice ⟨4,6,2⟩ ≤ singleTariff 4 6 2 := by decide +kernel
private theorem cell_5_6_2 : fatPrice ⟨5,6,2⟩ ≤ singleTariff 5 6 2 := by decide +kernel
private theorem cell_6_6_2 : fatPrice ⟨6,6,2⟩ ≤ singleTariff 6 6 2 := by decide +kernel
private theorem cell_7_6_2 : fatPrice ⟨7,6,2⟩ ≤ singleTariff 7 6 2 := by decide +kernel
private theorem cell_8_6_2 : fatPrice ⟨8,6,2⟩ ≤ singleTariff 8 6 2 := by decide +kernel
private theorem cell_9_6_2 : fatPrice ⟨9,6,2⟩ ≤ singleTariff 9 6 2 := by decide +kernel
private theorem cell_10_6_2 : fatPrice ⟨10,6,2⟩ ≤ singleTariff 10 6 2 := by decide +kernel
private theorem cell_11_6_2 : fatPrice ⟨11,6,2⟩ ≤ singleTariff 11 6 2 := by decide +kernel
private theorem cell_12_6_2 : fatPrice ⟨12,6,2⟩ ≤ singleTariff 12 6 2 := by decide +kernel
private theorem cell_13_6_2 : fatPrice ⟨13,6,2⟩ ≤ singleTariff 13 6 2 := by decide +kernel
private theorem cell_14_6_2 : fatPrice ⟨14,6,2⟩ ≤ singleTariff 14 6 2 := by decide +kernel
private theorem cell_15_6_2 : fatPrice ⟨15,6,2⟩ ≤ singleTariff 15 6 2 := by decide +kernel
private theorem cell_16_6_2 : fatPrice ⟨16,6,2⟩ ≤ singleTariff 16 6 2 := by decide +kernel
private theorem cell_17_6_2 : fatPrice ⟨17,6,2⟩ ≤ singleTariff 17 6 2 := by decide +kernel
private theorem cell_3_7_2 : fatPrice ⟨3,7,2⟩ ≤ singleTariff 3 7 2 := by decide +kernel
private theorem cell_4_7_2 : fatPrice ⟨4,7,2⟩ ≤ singleTariff 4 7 2 := by decide +kernel
private theorem cell_5_7_2 : fatPrice ⟨5,7,2⟩ ≤ singleTariff 5 7 2 := by decide +kernel
private theorem cell_6_7_2 : fatPrice ⟨6,7,2⟩ ≤ singleTariff 6 7 2 := by decide +kernel
private theorem cell_7_7_2 : fatPrice ⟨7,7,2⟩ ≤ singleTariff 7 7 2 := by decide +kernel
private theorem cell_8_7_2 : fatPrice ⟨8,7,2⟩ ≤ singleTariff 8 7 2 := by decide +kernel
private theorem cell_9_7_2 : fatPrice ⟨9,7,2⟩ ≤ singleTariff 9 7 2 := by decide +kernel
private theorem cell_10_7_2 : fatPrice ⟨10,7,2⟩ ≤ singleTariff 10 7 2 := by decide +kernel
private theorem cell_11_7_2 : fatPrice ⟨11,7,2⟩ ≤ singleTariff 11 7 2 := by decide +kernel
private theorem cell_12_7_2 : fatPrice ⟨12,7,2⟩ ≤ singleTariff 12 7 2 := by decide +kernel
private theorem cell_3_8_2 : fatPrice ⟨3,8,2⟩ ≤ singleTariff 3 8 2 := by decide +kernel
private theorem cell_4_8_2 : fatPrice ⟨4,8,2⟩ ≤ singleTariff 4 8 2 := by decide +kernel
private theorem price_3_1 (b : ℕ) (lo : 1≤b) (hi : b≤26) :
    fatPrice ⟨b,3,1⟩ ≤ singleTariff b 3 1 := by
  interval_cases b
  · exact cell_1_3_1
  · exact cell_2_3_1
  · exact cell_3_3_1
  · exact cell_4_3_1
  · exact cell_5_3_1
  · exact cell_6_3_1
  · exact cell_7_3_1
  · exact cell_8_3_1
  · exact cell_9_3_1
  · exact cell_10_3_1
  · exact cell_11_3_1
  · exact cell_12_3_1
  · exact cell_13_3_1
  · exact cell_14_3_1
  · exact cell_15_3_1
  · exact cell_16_3_1
  · exact cell_17_3_1
  · exact cell_18_3_1
  · exact cell_19_3_1
  · exact cell_20_3_1
  · exact cell_21_3_1
  · exact cell_22_3_1
  · exact cell_23_3_1
  · exact cell_24_3_1
  · exact cell_25_3_1
  · exact cell_26_3_1
private theorem price_4_1 (b : ℕ) (lo : 2≤b) (hi : b≤24) :
    fatPrice ⟨b,4,1⟩ ≤ singleTariff b 4 1 := by
  interval_cases b
  · exact cell_2_4_1
  · exact cell_3_4_1
  · exact cell_4_4_1
  · exact cell_5_4_1
  · exact cell_6_4_1
  · exact cell_7_4_1
  · exact cell_8_4_1
  · exact cell_9_4_1
  · exact cell_10_4_1
  · exact cell_11_4_1
  · exact cell_12_4_1
  · exact cell_13_4_1
  · exact cell_14_4_1
  · exact cell_15_4_1
  · exact cell_16_4_1
  · exact cell_17_4_1
  · exact cell_18_4_1
  · exact cell_19_4_1
  · exact cell_20_4_1
  · exact cell_21_4_1
  · exact cell_22_4_1
  · exact cell_23_4_1
  · exact cell_24_4_1
private theorem price_5_1 (b : ℕ) (lo : 2≤b) (hi : b≤21) :
    fatPrice ⟨b,5,1⟩ ≤ singleTariff b 5 1 := by
  interval_cases b
  · exact cell_2_5_1
  · exact cell_3_5_1
  · exact cell_4_5_1
  · exact cell_5_5_1
  · exact cell_6_5_1
  · exact cell_7_5_1
  · exact cell_8_5_1
  · exact cell_9_5_1
  · exact cell_10_5_1
  · exact cell_11_5_1
  · exact cell_12_5_1
  · exact cell_13_5_1
  · exact cell_14_5_1
  · exact cell_15_5_1
  · exact cell_16_5_1
  · exact cell_17_5_1
  · exact cell_18_5_1
  · exact cell_19_5_1
  · exact cell_20_5_1
  · exact cell_21_5_1
private theorem price_6_1 (b : ℕ) (lo : 2≤b) (hi : b≤17) :
    fatPrice ⟨b,6,1⟩ ≤ singleTariff b 6 1 := by
  interval_cases b
  · exact cell_2_6_1
  · exact cell_3_6_1
  · exact cell_4_6_1
  · exact cell_5_6_1
  · exact cell_6_6_1
  · exact cell_7_6_1
  · exact cell_8_6_1
  · exact cell_9_6_1
  · exact cell_10_6_1
  · exact cell_11_6_1
  · exact cell_12_6_1
  · exact cell_13_6_1
  · exact cell_14_6_1
  · exact cell_15_6_1
  · exact cell_16_6_1
  · exact cell_17_6_1
private theorem price_7_1 (b : ℕ) (lo : 3≤b) (hi : b≤12) :
    fatPrice ⟨b,7,1⟩ ≤ singleTariff b 7 1 := by
  interval_cases b
  · exact cell_3_7_1
  · exact cell_4_7_1
  · exact cell_5_7_1
  · exact cell_6_7_1
  · exact cell_7_7_1
  · exact cell_8_7_1
  · exact cell_9_7_1
  · exact cell_10_7_1
  · exact cell_11_7_1
  · exact cell_12_7_1
private theorem price_8_1 (b : ℕ) (lo : 3≤b) (hi : b≤4) :
    fatPrice ⟨b,8,1⟩ ≤ singleTariff b 8 1 := by
  interval_cases b
  · exact cell_3_8_1
  · exact cell_4_8_1
private theorem price_6_2 (b : ℕ) (lo : 2≤b) (hi : b≤17) :
    fatPrice ⟨b,6,2⟩ ≤ singleTariff b 6 2 := by
  interval_cases b
  · exact cell_2_6_2
  · exact cell_3_6_2
  · exact cell_4_6_2
  · exact cell_5_6_2
  · exact cell_6_6_2
  · exact cell_7_6_2
  · exact cell_8_6_2
  · exact cell_9_6_2
  · exact cell_10_6_2
  · exact cell_11_6_2
  · exact cell_12_6_2
  · exact cell_13_6_2
  · exact cell_14_6_2
  · exact cell_15_6_2
  · exact cell_16_6_2
  · exact cell_17_6_2
private theorem price_7_2 (b : ℕ) (lo : 3≤b) (hi : b≤12) :
    fatPrice ⟨b,7,2⟩ ≤ singleTariff b 7 2 := by
  interval_cases b
  · exact cell_3_7_2
  · exact cell_4_7_2
  · exact cell_5_7_2
  · exact cell_6_7_2
  · exact cell_7_7_2
  · exact cell_8_7_2
  · exact cell_9_7_2
  · exact cell_10_7_2
  · exact cell_11_7_2
  · exact cell_12_7_2
private theorem price_8_2 (b : ℕ) (lo : 3≤b) (hi : b≤4) :
    fatPrice ⟨b,8,2⟩ ≤ singleTariff b 8 2 := by
  interval_cases b
  · exact cell_3_8_2
  · exact cell_4_8_2
private theorem single_price {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤8) (hv : j≤3*b) (hb : b≤lowDegreeCap j) :
    fatPrice ⟨b,j,t⟩≤singleTariff b j t := by
  have ht2 : t≤2 := by omega
  interval_cases t
  · have jl : 3≤j := by omega
    interval_cases j
    · exact price_3_1 b (by omega) hb
    · exact price_4_1 b (by omega) hb
    · exact price_5_1 b (by omega) hb
    · exact price_6_1 b (by omega) hb
    · exact price_7_1 b (by omega) hb
    · exact price_8_1 b (by omega) hb
  · have jl : 6≤j := by omega
    interval_cases j
    · exact price_6_2 b (by omega) hb
    · exact price_7_2 b (by omega) hb
    · exact price_8_2 b (by omega) hb
private def splitPrices (b j : ℕ) : List ℕ :=
  (List.range (b+1)).flatMap (fun c=>(List.range (j+1)).map (fun k=>
    if 3≤k ∧ k≤3*c ∧ 3≤j-k ∧ j-k≤3*(b-c) then
      singleTariff c k 1+singleTariff (b-c) (j-k) 1 else 0))
private def widthCharge (b j t : ℕ) : ℕ :=
  if t=0 then 0 else
    max (singleTariff b j t) (if t=2 then (splitPrices b j).foldr max 0 else 0)
private theorem le_fold_max {v : ℕ} {L : List ℕ} (mem : v∈L) : v≤L.foldr max 0 := by
  induction L with
  | nil => simp at mem
  | cons a tail ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | m
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih m).trans (le_max_right _ _)
private theorem width_single (b j t : ℕ) (hp : 0<t) : singleTariff b j t≤widthCharge b j t := by
  unfold widthCharge
  rw [ite_eq_right (Nat.ne_of_gt hp)]
  exact le_max_left _ _
private theorem width_pair (b c j k : ℕ) (hj : 3≤j) (hk : 3≤k) (hb : j≤3*b) (hc : k≤3*c) :
    singleTariff b j 1+singleTariff c k 1≤widthCharge (b+c) (j+k) 2 := by
  unfold widthCharge
  rw [ite_eq_right (by decide : ¬(2 : ℕ)=0), ite_eq_left rfl]
  apply le_trans _ (le_max_right _ _)
  apply le_fold_max
  unfold splitPrices
  refine List.mem_flatMap.mpr ⟨b,List.mem_range.mpr (by omega),?_⟩
  refine List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),?_⟩
  rw [show b+c-b=c by omega,show j+k-j=k by omega]
  rw [ite_eq_left ⟨hj,hb,hk,hc⟩]
private theorem checked_row (j : Fin 9) (t : Fin 3) :
    (List.range (lowDegreeCap j.val+1)).all (fun b=>decide
      (1≤t.val → 3*t.val≤j.val → j.val≤3*b → widthCharge b j.val t.val≤retainedTariff b j.val t.val)) = true := by
  fin_cases j <;> fin_cases t <;> decide +kernel
private theorem width_checked {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤8) (hv : j≤3*b) (hb : b≤lowDegreeCap j) :
    widthCharge b j t≤retainedTariff b j t := by
  have inj : t<3 := by omega
  have h := List.all_eq_true.mp (checked_row ⟨j,by omega⟩ ⟨t,inj⟩)
    b (List.mem_range.mpr (Nat.lt_succ_of_le hb))
  exact of_decide_eq_true h ht hj hv
theorem retained_family_fee (n : ℕ) (a : Fin n→Shape) (hv : ∀ i,Valid (a i))
    (hj : (∑ i,(a i).j)≤8) (hb : (∑ i,(a i).b) ≤ lowDegreeCap (∑ i,(a i).j)) :
    (∑ i,fatPrice (a i)) ≤ retainedTariff (∑ i,(a i).b) (∑ i,(a i).j) (∑ i,(a i).t) := by
  have hsum : 3*(∑ i,(a i).t)≤∑ i,(a i).j := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun i _=>(hv i).2.1
  have hn' : n≤∑ i,(a i).t := calc
    n = ∑ _ : Fin n,1 := by simp
    _ ≤ ∑ i,(a i).t := sum_le_sum fun i _=>(hv i).1
  have hn : n≤2 := by omega
  interval_cases n
  · simp
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    have one := hv 0
    have eq : a 0=⟨(a 0).b,(a 0).j,(a 0).t⟩ := by cases a 0; rfl
    conv_lhs => rw [eq]
    exact (single_price one.1 one.2.1 hj one.2.2 hb).trans
      ((width_single _ _ _ one.1).trans (width_checked one.1 one.2.1 hj one.2.2 hb))
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0 : (a 0).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have ht1 : (a 1).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have he (i : Fin 2) : a i=⟨(a i).b,(a i).j,(a i).t⟩ := by cases a i; rfl
    have shape0 : a 0=⟨(a 0).b,(a 0).j,1⟩ :=
      (he 0).trans (congrArg (fun t=>(⟨(a 0).b,(a 0).j,t⟩ : Shape)) ht0)
    have shape1 : a 1=⟨(a 1).b,(a 1).j,1⟩ :=
      (he 1).trans (congrArg (fun t=>(⟨(a 1).b,(a 1).j,t⟩ : Shape)) ht1)
    have hj0 : 3≤(a 0).j := by simpa only [ht0,Nat.mul_one] using (hv 0).2.1
    have hj1 : 3≤(a 1).j := by simpa only [ht1,Nat.mul_one] using (hv 1).2.1
    have j0hi : (a 0).j≤5 := by omega
    have j1hi : (a 1).j≤5 := by omega
    have totalB : (a 0).b+(a 1).b≤17 := by
      apply hb.trans
      have eq : (a 0).j+(a 1).j=6 ∨ (a 0).j+(a 1).j=7 ∨ (a 0).j+(a 1).j=8 := by omega
      rcases eq with eq | eq | eq <;> rw [eq] <;> decide
    have below (j : ℕ) (lo : 3≤j) (hi : j≤5) : 17≤lowDegreeCap j := by
      interval_cases j <;> decide
    have p0 := single_price (b:=(a 0).b) (t:=1) (by decide) (by simpa using hj0) (by omega)
      (hv 0).2.2 ((by omega : (a 0).b≤17).trans (below _ hj0 j0hi))
    have p1 := single_price (b:=(a 1).b) (t:=1) (by decide) (by simpa using hj1) (by omega)
      (hv 1).2.2 ((by omega : (a 1).b≤17).trans (below _ hj1 j1hi))
    rw [←shape0] at p0
    rw [←shape1] at p1
    have h := width_pair (a 0).b (a 1).b (a 0).j (a 1).j hj0 hj1 (hv 0).2.2 (hv 1).2.2
    rw [ht0,ht1]
    exact (Nat.add_le_add p0 p1).trans (h.trans (width_checked (by decide) (by omega) hj (by
      have := (hv 0).2.2; have := (hv 1).2.2; omega) hb))
#print axioms retained_family_fee
end Lower6960.Low

end
end Merged_R6960Low6960RetainedFees

-- merged module R6960Low6960Width
section Merged_R6960Low6960Width

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.Low
open Finset Polynomial
open P3 (K)
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Low6960Retained (Box combined)
open Lower6960.Low (lowDegreeCap)
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty)
open scoped Classical BigOperators

theorem degree_bound {r : Shape} (hr : Valid r) (hx : Box r) :
    r.b ≤ lowDegreeCap r.j := by
  have hjl : 3≤r.j := (Nat.mul_le_mul_left 3 hr.1).trans hr.2.1
  have hju := hx.2.1
  have hj : r.j=3 ∨ r.j=4 ∨ r.j=5 ∨ r.j=6 ∨ r.j=7 ∨ r.j=8 := by omega
  rcases hj with hj | hj | hj | hj | hj | hj <;> rw [hj] <;> simp only [lowDegreeCap]
  · exact hx.1
  · exact hx.2.2.1 (by omega)
  · exact hx.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.2 (by omega)

/-- The retained factors selected by the actual primary bank spend the
finite charge for their exact total width, before the positive-order allocation. -/
theorem Inventory.retained_charge {Γ : Finset K} {s : K→(Polynomial K)} (d : Inventory Γ s) :
    let r := combined (fun i=>shape (d.factor i)) d.zeros
    (∑ i∈d.zeros,fatPrice (shape (d.factor i))) ≤ retainedTariff r.b r.j r.t := by
  let q i := shape (d.factor i)
  let r := combined q d.zeros
  change (∑ i∈d.zeros,fatPrice (q i)) ≤ retainedTariff r.b r.j r.t
  by_cases empty : d.zeros=∅
  · simp [empty,r,combined,P3_6_8.shapeSum_empty,zeroShape,retainedTariff,retainedTariffs]
  · have box := (d.retained.resolve_left empty).1
    have hv : Valid r := (P3_6_8.shapeSum_valid_or_empty d.fits.1 d.zeros).resolve_left empty
    let e := d.zeros.equivFin.symm
    let ar : Fin d.zeros.card→Shape := fun i=>q (e i).val
    have sums (g : Shape→ℕ) : (∑ i,g (ar i)) = ∑ i∈d.zeros,g (q i) := by
      rw [←sum_attach d.zeros (fun i=>g (q i))]
      exact Fintype.sum_equiv e _ _ (fun _=>rfl)
    have hj : (∑ i,(ar i).j)≤8 := by rw [sums]; exact box.2.1
    have hb : (∑ i,(ar i).b)≤lowDegreeCap (∑ i,(ar i).j) := by
      rw [sums,sums]
      exact degree_bound hv box
    have h := retained_family_fee d.zeros.card ar (fun i=>d.fits.1 (e i).val) hj hb
    rw [sums,sums,sums,sums] at h
    exact h

#print axioms Inventory.retained_charge
end Lower6960.Low

end
end Merged_R6960Low6960Width

-- merged module R6960Low6960Prices
section Merged_R6960Low6960Prices

set_option Elab.async false
namespace Low6960Prices
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement := Lower6960.Low.agreement
abbrev physicalDegree := Lower6960.Low.physicalDegree
abbrev errors := Lower6960.Low.errors
abbrev incidenceGap := Lower6960.Low.incidenceGap
abbrev taylorLength := Lower6960.Low.taylorLength
abbrev anchorCutoff := Lower6960.Low.anchorCutoff
abbrev primaryCutoff := Lower6960.Low.primaryCutoff
def primaryBox : Shape := ⟨4012,1650,550⟩
abbrev layerWidth := Lower6960.Low.layerWidth
abbrev layerNeed := Lower6960.Low.need
abbrev symbolCount := Final50Price.symbolCount
abbrev TrueWeightLE := @Lower6960.Low.TrueWeightLE
abbrev LayerBudget := @Lower6960.Low.LayerBudget
abbrev remaining := Final50Price.remaining
abbrev Messages := Lower6960.Low.Messages
abbrev SmallFactor := Lower6960.Low.SmallFactor
abbrev LowerRow := Lower6960.Low.LowerRow
abbrev ProperCut := Lower6960.Low.ProperCut
abbrev ActiveFits := Final50Price.ActiveFits
abbrev Fits := @Lower6960.Low.Fits
abbrev fullCap := Lower6960.Low.fullCap
def lowerWidth (top : ℕ) : ℕ := 136-top
def lowerIndex (top : ℕ) : ℕ := 57-3*top
def lowerTop (top : ℕ) : ℕ := lowerIndex top/2
abbrev fatPrice := Lower6960.Low.fatPrice
abbrev FatEquations := Low6960Fat.FatEquations
abbrev Holds := Low6960Fat.Holds
abbrev fatOrder := Lower6960.Low.fatOrder
abbrev divisorOrder := Lower6960.Low.divisorOrder
abbrev isolatedOrder := Lower6960.Low.isolatedOrder
abbrev commonBox := Low6960Fat.commonBox
abbrev resultantBox := Low6960Fat.resultantBox
abbrev linearChart := Lower6960.Low.linearChart

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  Lower6960.Low.Messages.mono h hΔ

def lowerCap : ℕ → ℕ
  | 0 => 28939832636599906
  | 1 => 26150061697196931
  | 2 => 23488581035640966
  | 3 => 20958102538135074
  | 4 => 18560287483819229
  | 5 => 16297730917037374
  | 6 => 14172203991418967
  | 7 => 12186197718951818
  | 8 => 10341580113663363
  | 9 => 8640751373865300
  | 10 => 7085662950714511
  | 11 => 5678637856703625
  | 12 => 4421697147673414
  | 13 => 3317100687331508
  | 14 => 2366924894579984
  | _ => 0

def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPriceOld (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
abbrev BentCap := Shape × ℕ

def bentGraph (p : Shape) : BentCap := (⟨max p.b (p.j + 1), p.j + 1, p.t + 1⟩, 1)

def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))

def bentIntegral (B J T H : ℤ) : ℤ :=
  -576 * H ^ 5 + 160 * T ^ 2 * H ^ 3 - 480 * T ^ 3 * H ^ 2 + 540 * T ^ 4 * H
  + 960 * J * H ^ 4 - 320 * J * T * H ^ 3 + 960 * J * T ^ 2 * H ^ 2 - 1200 * J * T ^ 3 * H
  - 480 * J ^ 2 * H ^ 3 - 480 * J ^ 2 * T * H ^ 2 + 840 * J ^ 2 * T ^ 2 * H
  + 240 * J ^ 3 * H ^ 2 - 240 * J ^ 3 * T * H - 960 * B * H ^ 4 + 640 * B * T * H ^ 3
  - 1440 * B * T ^ 2 * H ^ 2 + 1440 * B * T ^ 3 * H + 640 * B * J * H ^ 3
  + 960 * B * J * T * H ^ 2 - 1440 * B * J * T ^ 2 * H - 480 * B * J ^ 2 * H ^ 2
  + 480 * B * J ^ 2 * T * H

def addBent (p q : BentCap) : BentCap := (p.1.plus q.1, p.2 + q.2)

def ambientMix (caps : List BentCap) : ℕ :=
  (caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) *
      bentIntegral s.1.b s.1.j s.1.t s.2) 0).toNat

def tiltedSurface (p q : Shape) : ℕ :=
  ambientMix [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]

def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]

def activeLoss (cs : List (ℕ × ℕ)) : ℕ :=
  480 * ((cs.map Prod.snd).prod - (cs.map (fun x => x.2 - 2*x.1)).prod)

def tiltedSurfaceActive (p q : Shape) (K : ℕ) : ℕ :=
  tiltedSurface p q - activeLoss (activeClips p K)

def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))

def physicalPriceWith (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceTilted (x : Shape) (l : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurface x.chamber primaryBox)

def physicalPriceActive (x : Shape) (l K : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurfaceActive x.chamber primaryBox K)

def physicalPrice (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOld x l) (physicalPriceTilted x l)
    if activeFitsPrice x K then min base (physicalPriceActive x l K) else base
  else physicalPriceOld x l

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l K
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, Holds E (extend (s γ))) → Γ.card ≤ fatPrice (shape f)

end
end Low6960Prices

end Merged_R6960Low6960Prices

-- merged module R6960Low6960Monotone
section Merged_R6960Low6960Monotone
set_option Elab.async false
section
namespace Low6960Monotone
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩
theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩
theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩
theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩
theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩
theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩
theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩
private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega
theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (chart L x) (chart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [chart] <;> gcongr
private theorem lifted_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (liftedChart L x) (liftedChart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [liftedChart] <;> gcongr
private def graphShape (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
private theorem graph_chamber (x : Shape) : Chamber (graphShape x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem graph_mono {x y : Shape} (h : InBox x y) :
    InBox (graphShape x) (graphShape y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [graphShape] <;> gcongr
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    Low6960Prices.surfaceNumerator32 p q ≤ Low6960Prices.surfaceNumerator32 p' q := by
  let L := Low6960Prices.taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (box_refl q) (chart_mono _ hp) (chart_mono _ hp) hp' hq
      (chart_chamber _ _) hq (chart_chamber _ _) (chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (box_refl q) (lifted_mono _ hp) (lifted_mono _ hp) hp' hq
      (lifted_chamber _ _) hq (lifted_chamber _ _) (lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (graphShape p) (liftedChart M p) ≤ mixed32 p' q (graphShape p') (liftedChart M p') :=
    mixed_mono hp (box_refl q) (graph_mono hp) (lifted_mono _ hp) hp' hq
      (graph_chamber _) hq (graph_chamber _) (lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : Low6960Prices.physicalPriceOld x l ≤ Low6960Prices.physicalPriceOld y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6960Prices.primaryBox
  let L := Low6960Prices.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, le_rfl⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Low6960Prices.errors + 2*Low6960Prices.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (Low6960Prices.errors + 2*Low6960Prices.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6960Prices.errors hc) (Nat.mul_le_mul_left (2*Low6960Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6960Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)
end Low6960Monotone
end

namespace Low6960Monotone
open K1_13 (Shape)
open Low6960Prices (physicalPrice physicalPriceOld physicalPriceTilted physicalPriceActive physicalPriceWith)

theorem physicalPrice_le_old (x : Shape) (l K : ℕ) : physicalPrice x l K ≤ physicalPriceOld x l := by
  unfold physicalPrice
  split
  · split
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact min_le_left _ _
  · exact le_rfl

private theorem with_anti (a : Shape) (s : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPriceWith a u s ≤ physicalPriceWith a l s := by
  unfold physicalPriceWith
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _

theorem physicalPrice_anti (a : Shape) (K : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPrice a u K ≤ physicalPrice a l K := by
  have hold : physicalPriceOld a u ≤ physicalPriceOld a l := by
    unfold physicalPriceOld
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _
  have hnew : physicalPriceTilted a u ≤ physicalPriceTilted a l := with_anti a _ hl h
  have hactive : physicalPriceActive a u K ≤ physicalPriceActive a l K := with_anti a _ hl h
  unfold physicalPrice
  split
  · split
    · exact min_le_min (min_le_min hold hnew) hactive
    · exact min_le_min hold hnew
  · exact hold
end Low6960Monotone

end Merged_R6960Low6960Monotone

end Merged_R6960Low6960Monotone

-- merged module R6960Low6960SurfaceLinearFour
section Merged_R6960Low6960SurfaceLinearFour

-- merged module R6960Low6960SharedPrice
section Merged_R6960Low6960SharedPrice
set_option Elab.async false
set_option autoImplicit false
namespace Low6960SharedPrice
open K1_13 (Shape chart ceilDiv mixed32 shape OnFactor extend)
open Low6960Prices (Messages SmallFactor ActiveFits ProperCut taylorLength primaryBox
  physicalPrice physicalDegree errors incidenceGap tiltedFits tiltedSurface)
open scoped Polynomial
abbrev slope : Shape := ⟨62,26,7⟩
abbrev slopeLoss : ℕ := 20625302605067
inductive Surface where
  | ordinary
  | tilted
  deriving DecidableEq
def surfaceScale : Surface → ℕ
  | .ordinary => 32
  | .tilted => 1920
def surface (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltedSurface f.chamber q
def weights (kind : Surface) (f : Shape) : Shape :=
  let b := surface kind f ⟨1,0,0⟩
  let j := surface kind f ⟨1,1,0⟩ - b
  let t := surface kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
def coord (p : Shape) (i : Fin 3) : ℕ := (![p.b,p.j,p.t] : Fin 3 → ℕ) i
def expression (w q : Shape) (useIndex topIndex : Bool) : ℕ :=
  3*w.b*(if useIndex then q.j else q.b) + 3*w.j*q.j +
    w.t*(if topIndex then q.j else 3*q.t)
def deficit (r a : ℕ) (f : Shape) : Shape :=
  ⟨r*slope.b-a*f.b,r*slope.j-a*f.j,r*slope.t-a*f.t⟩
structure Rate where
  kind : Surface
  pivot : Fin 3
  split : ℕ
  topIndex : Bool
  amount : ℕ
def RateFits (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weights u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))
instance (f : Shape) (u : Rate) : Decidable (RateFits f u) := by
  unfold RateFits
  infer_instance
private theorem expression_line (w f : Shape) (r a : ℕ) (u t : Bool)
    (hb : a*f.b ≤ r*slope.b) (hj : a*f.j ≤ r*slope.j) (ht : a*f.t ≤ r*slope.t) :
    expression w (deficit r a f) u t + a*expression w f u t = r*expression w slope u t := by
  have b := Nat.sub_add_cancel hb
  have j := Nat.sub_add_cancel hj
  have h := Nat.sub_add_cancel ht
  cases u <;> cases t <;> simp only [expression, deficit, Bool.false_eq_true, ↓reduceIte, ite_true]
  all_goals
    rw [mul_add, mul_add]
    simp only [mul_assoc, ← mul_add, ← add_assoc] <;> ring_nf at b j h ⊢
    <;> nlinarith only [congrArg (fun z => w.b*z) b, congrArg (fun z => w.b*z) j,
      congrArg (fun z => w.j*z) j, congrArg (fun z => w.t*z) j, congrArg (fun z => w.t*z) h]
private theorem affine_of_endpoints (p q s x y W r a : ℕ)
    (hp : 0 < p) (hb : a*q ≤ r*p)
    (h₀ : x ≤ W) (h₁ : (q : ℤ)*x-p*y ≤ (q-(s:ℤ)*p)*W) :
    (r : ℤ)*x-a*y ≤ (r-(s:ℤ)*a)*W := by
  have hq : (0 : ℤ) < p := by exact_mod_cast hp
  have hr : (a : ℤ)*q ≤ (r : ℤ)*p := by exact_mod_cast hb
  have hzero : (0 : ℤ) ≤ (W : ℤ)-x := sub_nonneg.mpr (by exact_mod_cast h₀)
  have hA := mul_nonneg (sub_nonneg.mpr hr) hzero
  have hB := mul_nonneg (Int.natCast_nonneg a)
    (show 0 ≤ (p : ℤ)*((y:ℤ)-s*W)-q*((x:ℤ)-W) by linarith)
  apply sub_nonneg.mp
  refine nonneg_of_mul_nonneg_left ?_ hq
  have ident : (p : ℤ)*(((r:ℤ)-s*a)*W-((r:ℤ)*x-a*y)) =
      ((r:ℤ)*p-a*q)*((W:ℤ)-x)+a*(p*((y:ℤ)-s*W)-q*((x:ℤ)-W)) := by ring
  rw [mul_comm, ident]
  exact add_nonneg hA hB
private theorem pivot_pos (i : Fin 3) : 0 < coord slope i := by fin_cases i <;> decide
theorem rate_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (chooseWidth : Bool) :
    expression (weights u.kind f) (deficit r a f) chooseWidth u.topIndex ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let W := 3*surfaceScale u.kind*u.amount
  let w := weights u.kind f
  obtain ⟨_,hs,hpos,hcoord,h₀,h₁⟩ := hu
  have hp : 0 < p := pivot_pos u.pivot
  have hfitPivot : a*q ≤ r*p := hfit u.pivot
  have har : u.split*a ≤ r := by
    by_contra! hbad
    have hleft := Nat.mul_lt_mul_of_pos_right hbad hp
    have hright := Nat.mul_le_mul_left a (Nat.le_of_lt hpos)
    exact (not_lt_of_ge (hfitPivot.trans' (by
      simpa only [mul_left_comm, mul_assoc, mul_comm] using hright : u.split*a*p ≤ a*q))) hleft
  have f0 := expression_line w f q p chooseWidth u.topIndex
    (hcoord 0) (hcoord 1) (hcoord 2)
  have f1 := expression_line w f r a chooseWidth u.topIndex
    (hfit 0) (hfit 1) (hfit 2)
  have hend : ((q : ℤ)*expression w slope chooseWidth u.topIndex -
      p*expression w f chooseWidth u.topIndex) ≤ (q-(u.split:ℤ)*p)*W := by
    have hnum : expression w (deficit q p f) chooseWidth u.topIndex ≤ W*(q-u.split*p) := h₁ chooseWidth
    have hnum' : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤
        (W:ℤ)*(q-(u.split:ℤ)*p) := by
      have hh : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤ (W:ℤ) * ((q-u.split*p : ℕ) : ℤ) := by exact_mod_cast hnum
      change u.split*p < q at hpos
      rwa [Int.ofNat_sub (Nat.le_of_lt hpos)] at hh
    have hline : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) +
        p*expression w f chooseWidth u.topIndex = q*expression w slope chooseWidth u.topIndex := by
      exact_mod_cast f0
    nlinarith
  have haff := affine_of_endpoints p q u.split _ _ W r a hp hfitPivot (h₀ chooseWidth) hend
  have hline : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) +
      a*expression w f chooseWidth u.topIndex = r*expression w slope chooseWidth u.topIndex := by
    exact_mod_cast f1
  have hgoal : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) ≤
      (W:ℤ)*(r-(u.split:ℤ)*a) := by nlinarith
  rw [← Nat.cast_mul, ← Nat.cast_sub har, ← Nat.cast_mul] at hgoal
  exact_mod_cast hgoal
theorem remainder_pos {f : Shape} {u : Rate} (hu : RateFits f u) {r a : ℕ}
    (hr : 0 < r) (hfit : ∀ i, a*coord f i ≤ r*coord slope i) : 0 < r-u.split*a := by
  obtain ⟨_,_,hs,_,_,_⟩ := hu
  have hp := pivot_pos u.pivot
  have hmark := hfit u.pivot
  by_cases ha : a = 0
  · simpa [ha] using hr
  have hm := Nat.mul_lt_mul_of_pos_left hs (Nat.pos_of_ne_zero ha)
  have h : u.split*a * coord slope u.pivot < r * coord slope u.pivot := by
    simpa only [mul_left_comm,mul_assoc,mul_comm] using hm.trans_le hmark
  exact Nat.sub_pos_of_lt (Nat.lt_of_mul_lt_mul_right h)
theorem chamber_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (g : Shape)
    (hg : K1_13.InBox g (deficit r a f)) (hgt : 3*g.t ≤ g.j) :
    3*((weights u.kind f).b*g.chamber.b + (weights u.kind f).j*g.j + (weights u.kind f).t*g.t) ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let w := weights u.kind f
  let d := deficit r a f
  have hgB : g.b ≤ d.b := hg.1
  have hgJ : g.j ≤ d.j := hg.2.1
  have hgT : g.t ≤ d.t := hg.2.2
  have hTop : 3*g.t ≤ (if u.topIndex then d.j else 3*d.t) := by
    split
    · exact hgt.trans hgJ
    · exact Nat.mul_le_mul_left _ hgT
  have component (i : Bool)
      (hB : max g.b g.j ≤ (if i then d.j else d.b)) :
      3*(w.b*g.chamber.b + w.j*g.j + w.t*g.t) ≤ expression w d i u.topIndex := by
    change 3*(w.b*max g.b g.j + w.j*g.j + w.t*g.t) ≤ _
    unfold expression
    calc
      _ = 3*w.b*max g.b g.j + 3*w.j*g.j + w.t*(3*g.t) := by ring
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left _ hB) (Nat.mul_le_mul_left _ hgJ)) (Nat.mul_le_mul_left _ hTop)
  rcases le_total d.b d.j with h | h
  · exact (component true (max_le (hgB.trans h) hgJ)).trans (rate_bound hu r a hfit true)
  · exact (component false (max_le hgB (hgJ.trans h))).trans (rate_bound hu r a hfit false)
def additiveBase (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixed32 p q z h + 2*x.t*mixed32 p p p h
  let pt := mixed32 p q z p + 2*x.t*mixed32 p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)
def nonsharedFee (x : Shape) (l : ℕ) : ℕ :=
  ceilDiv (2*x.b*primaryBox.b^2*(chart (taylorLength+2) x.chamber).b) l
def price (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPrice x l K + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l
def cShared : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → ∀ u, RateFits (shape f) u →
      Γ.card ≤ price (shape f) l K u
end Low6960SharedPrice

end Merged_R6960Low6960SharedPrice

-- merged module R6960Low6960SurfaceLinearFour
section Merged_R6960Low6960SurfaceLinearFour
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Low6960SharedPrice
open K1_13 (Shape chart difference volume32)
open K1_13_8 (Valid)
open Low6960Prices (taylorLength)
open K1_13_8_2 (signedMixed signed_rotate signed_nonneg)
theorem surface_eq_weights_of_signed (kind : Surface) (f : Shape) (b j t : ℤ)
    (hb : 0 ≤ b) (hj : 0 ≤ j) (ht : 0 ≤ t)
    (h : ∀ q : Shape, (surface kind f q : ℤ) = b*q.b + j*q.j + t*q.t) (q : Shape) :
    surface kind f q = (weights kind f).b*q.b + (weights kind f).j*q.j +
      (weights kind f).t*q.t := by
  have hn (u : Shape) : surface kind f u = b.toNat*u.b + j.toNat*u.j + t.toNat*u.t := by
    apply Int.ofNat.inj
    change (surface kind f u : ℤ) = ((b.toNat*u.b + j.toNat*u.j + t.toNat*u.t : ℕ) : ℤ)
    rw [h u]
    push_cast
    rw [Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hj, Int.toNat_of_nonneg ht]
  have hw : weights kind f = ⟨b.toNat,j.toNat,t.toNat⟩ := by
    unfold weights
    simp only [hn ⟨1,0,0⟩, hn ⟨1,1,0⟩, hn ⟨3,3,1⟩, Nat.mul_one, Nat.mul_zero,
      Nat.add_zero, Nat.add_sub_cancel_left]
    congr 1
    omega
  rw [hw]
  exact hn q
private theorem signed_four_linear (q p r s : Shape) :
    signedMixed q p r s = signedMixed ⟨1,0,0⟩ p r s*q.b +
      signedMixed ⟨0,1,0⟩ p r s*q.j + signedMixed ⟨0,0,1⟩ p r s*q.t := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero,
    Nat.cast_one]
  ring
theorem surface_ordinary_eq_weights {f : Shape} (hf : Valid f) (q : Shape) :
    surface .ordinary f q = (weights .ordinary f).b*q.b + (weights .ordinary f).j*q.j +
      (weights .ordinary f).t*q.t := by
  let p := f.chamber
  let r := chart (taylorLength+1) p
  let s := chart (taylorLength+2) p
  have hp : K1_13_8_2.Chamber p := ⟨le_max_right _ _,hf.2.1⟩
  have hr : K1_13_8_2.Chamber r := K1_13_7_1.chart_chamber _ _
  have hs : K1_13_8_2.Chamber s := K1_13_7_1.chart_chamber _ _
  have hnonneg (u : Shape) : 0 ≤ signedMixed u r s p := signed_nonneg u r s p hr hs hp
  refine surface_eq_weights_of_signed .ordinary f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedMixed p u r s).toNat : ℤ) = _
  rw [signed_rotate, Int.toNat_of_nonneg (hnonneg u)]
  exact signed_four_linear u r s p
#print axioms surface_ordinary_eq_weights
end Low6960SharedPrice

end Merged_R6960Low6960SurfaceLinearFour

end Merged_R6960Low6960SurfaceLinearFour

end Merged6967_R6960Low6960SurfaceLinearFour

section Merged6967_R6960TerminalReceipts
set_option Elab.async false



set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6960.TerminalReceipts
open TerminalArithmetic
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

def terminalBank : P1_7.Bank := ⟨⟨4500,6286,1329,748778⟩,2693670660997120,42045879552530⟩

private theorem moment_6286_1329_part0 :
    blockEstimate 6286 1329 1329 128 = 2214802720 := by decide +kernel
private theorem moment_6286_1329_part1 :
    blockEstimate 6286 1329 1457 128 = 15027586336 := by decide +kernel
private theorem moment_6286_1329_part2 :
    blockEstimate 6286 1329 1585 128 = 39811962144 := by decide +kernel
private theorem moment_6286_1329_part3 :
    blockEstimate 6286 1329 1713 128 = 75762623776 := by decide +kernel
private theorem moment_6286_1329_part4 :
    blockEstimate 6286 1329 1841 128 = 122074264864 := by decide +kernel
private theorem moment_6286_1329_part5 :
    blockEstimate 6286 1329 1969 128 = 177941579040 := by decide +kernel
private theorem moment_6286_1329_part6 :
    blockEstimate 6286 1329 2097 128 = 242559259936 := by decide +kernel
private theorem moment_6286_1329_part7 :
    blockEstimate 6286 1329 2225 128 = 315122001184 := by decide +kernel
private theorem moment_6286_1329_part8 :
    blockEstimate 6286 1329 2353 128 = 394824496416 := by decide +kernel
private theorem moment_6286_1329_part9 :
    blockEstimate 6286 1329 2481 128 = 480861439264 := by decide +kernel
private theorem moment_6286_1329_part10 :
    blockEstimate 6286 1329 2609 128 = 572025083140 := by decide +kernel
private theorem moment_6286_1329_part11 :
    blockEstimate 6286 1329 2737 128 = 662020927680 := by decide +kernel
private theorem moment_6286_1329_part12 :
    blockEstimate 6286 1329 2865 128 = 746536235200 := by decide +kernel
private theorem moment_6286_1329_part13 :
    blockEstimate 6286 1329 2993 128 = 825473118400 := by decide +kernel
private theorem moment_6286_1329_part14 :
    blockEstimate 6286 1329 3121 128 = 898831577280 := by decide +kernel
private theorem moment_6286_1329_part15 :
    blockEstimate 6286 1329 3249 128 = 966611611840 := by decide +kernel
private theorem moment_6286_1329_part16 :
    blockEstimate 6286 1329 3377 128 = 1028813222080 := by decide +kernel
private theorem moment_6286_1329_part17 :
    blockEstimate 6286 1329 3505 128 = 1085436408000 := by decide +kernel
private theorem moment_6286_1329_part18 :
    blockEstimate 6286 1329 3633 128 = 1136481169600 := by decide +kernel
private theorem moment_6286_1329_part19 :
    blockEstimate 6286 1329 3761 128 = 1181947506880 := by decide +kernel
private theorem moment_6286_1329_part20 :
    blockEstimate 6286 1329 3889 128 = 1221835419840 := by decide +kernel
private theorem moment_6286_1329_part21 :
    blockEstimate 6286 1329 4017 128 = 1256144908480 := by decide +kernel
private theorem moment_6286_1329_part22 :
    blockEstimate 6286 1329 4145 128 = 1284875972800 := by decide +kernel
private theorem moment_6286_1329_part23 :
    blockEstimate 6286 1329 4273 128 = 1308028612800 := by decide +kernel
private theorem moment_6286_1329_part24 :
    blockEstimate 6286 1329 4401 128 = 1325602828480 := by decide +kernel
private theorem moment_6286_1329_part25 :
    blockEstimate 6286 1329 4529 128 = 1337598619840 := by decide +kernel
private theorem moment_6286_1329_part26 :
    blockEstimate 6286 1329 4657 128 = 1344015986880 := by decide +kernel
private theorem moment_6286_1329_part27 :
    blockEstimate 6286 1329 4785 128 = 1344854929600 := by decide +kernel
private theorem moment_6286_1329_part28 :
    blockEstimate 6286 1329 4913 128 = 1340115448000 := by decide +kernel
private theorem moment_6286_1329_part29 :
    blockEstimate 6286 1329 5041 128 = 1329797542080 := by decide +kernel
private theorem moment_6286_1329_part30 :
    blockEstimate 6286 1329 5169 128 = 1313901211840 := by decide +kernel
private theorem moment_6286_1329_part31 :
    blockEstimate 6286 1329 5297 128 = 1292426457280 := by decide +kernel
private theorem moment_6286_1329_part32 :
    blockEstimate 6286 1329 5425 128 = 1265373278400 := by decide +kernel
private theorem moment_6286_1329_part33 :
    blockEstimate 6286 1329 5553 128 = 1232741675200 := by decide +kernel
private theorem moment_6286_1329_part34 :
    blockEstimate 6286 1329 5681 128 = 1194531647680 := by decide +kernel
private theorem moment_6286_1329_part35 :
    blockEstimate 6286 1329 5809 128 = 1150743195840 := by decide +kernel
private theorem moment_6286_1329_part36 :
    blockEstimate 6286 1329 5937 128 = 1101376319680 := by decide +kernel
private theorem moment_6286_1329_part37 :
    blockEstimate 6286 1329 6065 128 = 1046431019200 := by decide +kernel
private theorem moment_6286_1329_part38 :
    blockEstimate 6286 1329 6193 128 = 985920946437 := by decide +kernel
private theorem moment_6286_1329_part39 :
    blockEstimate 6286 1329 6321 128 = 921179065408 := by decide +kernel
private theorem moment_6286_1329_part40 :
    blockEstimate 6286 1329 6449 128 = 854891400374 := by decide +kernel
private theorem moment_6286_1329_part41 :
    blockEstimate 6286 1329 6577 128 = 787869474317 := by decide +kernel
private theorem moment_6286_1329_part42 :
    blockEstimate 6286 1329 6705 128 = 720673141815 := by decide +kernel
private theorem moment_6286_1329_part43 :
    blockEstimate 6286 1329 6833 128 = 653842881703 := by decide +kernel
private theorem moment_6286_1329_part44 :
    blockEstimate 6286 1329 6961 128 = 587899797345 := by decide +kernel
private theorem moment_6286_1329_part45 :
    blockEstimate 6286 1329 7089 128 = 523345615005 := by decide +kernel
private theorem moment_6286_1329_part46 :
    blockEstimate 6286 1329 7217 128 = 460662686400 := by decide +kernel
private theorem moment_6286_1329_part47 :
    blockEstimate 6286 1329 7345 128 = 400313987006 := by decide +kernel
private theorem moment_6286_1329_part48 :
    blockEstimate 6286 1329 7473 128 = 342743116198 := by decide +kernel
private theorem moment_6286_1329_part49 :
    blockEstimate 6286 1329 7601 128 = 288069435510 := by decide +kernel
private theorem moment_6286_1329_part50 :
    blockEstimate 6286 1329 7729 128 = 236803710816 := by decide +kernel
private theorem moment_6286_1329_part51 :
    blockEstimate 6286 1329 7857 128 = 189859721056 := by decide +kernel
private theorem moment_6286_1329_part52 :
    blockEstimate 6286 1329 7985 128 = 147494272864 := by decide +kernel
private theorem moment_6286_1329_part53 :
    blockEstimate 6286 1329 8113 128 = 109959024480 := by decide +kernel
private theorem moment_6286_1329_part54 :
    blockEstimate 6286 1329 8241 128 = 77505634144 := by decide +kernel
private theorem moment_6286_1329_part55 :
    blockEstimate 6286 1329 8369 128 = 50385760096 := by decide +kernel
private theorem moment_6286_1329_part56 :
    blockEstimate 6286 1329 8497 128 = 28851060576 := by decide +kernel
private theorem moment_6286_1329_part57 :
    blockEstimate 6286 1329 8625 128 = 13153193824 := by decide +kernel
private theorem moment_6286_1329_part58 :
    blockEstimate 6286 1329 8753 128 = 3543818080 := by decide +kernel
private theorem moment_6286_1329_part59 :
    blockEstimate 6286 1329 8881 63 = 139859376 := by decide +kernel
private theorem moment_6286_1329_join0 :
    blockEstimate 6286 1329 1457 256 = 54839548480 :=
  block_append moment_6286_1329_part1 moment_6286_1329_part2 rfl rfl rfl
private theorem moment_6286_1329_join1 :
    blockEstimate 6286 1329 1329 384 = 57054351200 :=
  block_append moment_6286_1329_part0 moment_6286_1329_join0 rfl rfl rfl
private theorem moment_6286_1329_join2 :
    blockEstimate 6286 1329 1713 256 = 197836888640 :=
  block_append moment_6286_1329_part3 moment_6286_1329_part4 rfl rfl rfl
private theorem moment_6286_1329_join3 :
    blockEstimate 6286 1329 1969 256 = 420500838976 :=
  block_append moment_6286_1329_part5 moment_6286_1329_part6 rfl rfl rfl
private theorem moment_6286_1329_join4 :
    blockEstimate 6286 1329 1713 512 = 618337727616 :=
  block_append moment_6286_1329_join2 moment_6286_1329_join3 rfl rfl rfl
private theorem moment_6286_1329_join5 :
    blockEstimate 6286 1329 1329 896 = 675392078816 :=
  block_append moment_6286_1329_join1 moment_6286_1329_join4 rfl rfl rfl
private theorem moment_6286_1329_join6 :
    blockEstimate 6286 1329 2225 256 = 709946497600 :=
  block_append moment_6286_1329_part7 moment_6286_1329_part8 rfl rfl rfl
private theorem moment_6286_1329_join7 :
    blockEstimate 6286 1329 2481 256 = 1052886522404 :=
  block_append moment_6286_1329_part9 moment_6286_1329_part10 rfl rfl rfl
private theorem moment_6286_1329_join8 :
    blockEstimate 6286 1329 2225 512 = 1762833020004 :=
  block_append moment_6286_1329_join6 moment_6286_1329_join7 rfl rfl rfl
private theorem moment_6286_1329_join9 :
    blockEstimate 6286 1329 2737 256 = 1408557162880 :=
  block_append moment_6286_1329_part11 moment_6286_1329_part12 rfl rfl rfl
private theorem moment_6286_1329_join10 :
    blockEstimate 6286 1329 2993 256 = 1724304695680 :=
  block_append moment_6286_1329_part13 moment_6286_1329_part14 rfl rfl rfl
private theorem moment_6286_1329_join11 :
    blockEstimate 6286 1329 2737 512 = 3132861858560 :=
  block_append moment_6286_1329_join9 moment_6286_1329_join10 rfl rfl rfl
private theorem moment_6286_1329_join12 :
    blockEstimate 6286 1329 2225 1024 = 4895694878564 :=
  block_append moment_6286_1329_join8 moment_6286_1329_join11 rfl rfl rfl
private theorem moment_6286_1329_join13 :
    blockEstimate 6286 1329 1329 1920 = 5571086957380 :=
  block_append moment_6286_1329_join5 moment_6286_1329_join12 rfl rfl rfl
private theorem moment_6286_1329_join14 :
    blockEstimate 6286 1329 3377 256 = 2114249630080 :=
  block_append moment_6286_1329_part16 moment_6286_1329_part17 rfl rfl rfl
private theorem moment_6286_1329_join15 :
    blockEstimate 6286 1329 3249 384 = 3080861241920 :=
  block_append moment_6286_1329_part15 moment_6286_1329_join14 rfl rfl rfl
private theorem moment_6286_1329_join16 :
    blockEstimate 6286 1329 3633 256 = 2318428676480 :=
  block_append moment_6286_1329_part18 moment_6286_1329_part19 rfl rfl rfl
private theorem moment_6286_1329_join17 :
    blockEstimate 6286 1329 3889 256 = 2477980328320 :=
  block_append moment_6286_1329_part20 moment_6286_1329_part21 rfl rfl rfl
private theorem moment_6286_1329_join18 :
    blockEstimate 6286 1329 3633 512 = 4796409004800 :=
  block_append moment_6286_1329_join16 moment_6286_1329_join17 rfl rfl rfl
private theorem moment_6286_1329_join19 :
    blockEstimate 6286 1329 3249 896 = 7877270246720 :=
  block_append moment_6286_1329_join15 moment_6286_1329_join18 rfl rfl rfl
private theorem moment_6286_1329_join20 :
    blockEstimate 6286 1329 4145 256 = 2592904585600 :=
  block_append moment_6286_1329_part22 moment_6286_1329_part23 rfl rfl rfl
private theorem moment_6286_1329_join21 :
    blockEstimate 6286 1329 4401 256 = 2663201448320 :=
  block_append moment_6286_1329_part24 moment_6286_1329_part25 rfl rfl rfl
private theorem moment_6286_1329_join22 :
    blockEstimate 6286 1329 4145 512 = 5256106033920 :=
  block_append moment_6286_1329_join20 moment_6286_1329_join21 rfl rfl rfl
private theorem moment_6286_1329_join23 :
    blockEstimate 6286 1329 4657 256 = 2688870916480 :=
  block_append moment_6286_1329_part26 moment_6286_1329_part27 rfl rfl rfl
private theorem moment_6286_1329_join24 :
    blockEstimate 6286 1329 4913 256 = 2669912990080 :=
  block_append moment_6286_1329_part28 moment_6286_1329_part29 rfl rfl rfl
private theorem moment_6286_1329_join25 :
    blockEstimate 6286 1329 4657 512 = 5358783906560 :=
  block_append moment_6286_1329_join23 moment_6286_1329_join24 rfl rfl rfl
private theorem moment_6286_1329_join26 :
    blockEstimate 6286 1329 4145 1024 = 10614889940480 :=
  block_append moment_6286_1329_join22 moment_6286_1329_join25 rfl rfl rfl
private theorem moment_6286_1329_join27 :
    blockEstimate 6286 1329 3249 1920 = 18492160187200 :=
  block_append moment_6286_1329_join19 moment_6286_1329_join26 rfl rfl rfl
private theorem moment_6286_1329_join28 :
    blockEstimate 6286 1329 1329 3840 = 24063247144580 :=
  block_append moment_6286_1329_join13 moment_6286_1329_join27 rfl rfl rfl
private theorem moment_6286_1329_join29 :
    blockEstimate 6286 1329 5297 256 = 2557799735680 :=
  block_append moment_6286_1329_part31 moment_6286_1329_part32 rfl rfl rfl
private theorem moment_6286_1329_join30 :
    blockEstimate 6286 1329 5169 384 = 3871700947520 :=
  block_append moment_6286_1329_part30 moment_6286_1329_join29 rfl rfl rfl
private theorem moment_6286_1329_join31 :
    blockEstimate 6286 1329 5553 256 = 2427273322880 :=
  block_append moment_6286_1329_part33 moment_6286_1329_part34 rfl rfl rfl
private theorem moment_6286_1329_join32 :
    blockEstimate 6286 1329 5809 256 = 2252119515520 :=
  block_append moment_6286_1329_part35 moment_6286_1329_part36 rfl rfl rfl
private theorem moment_6286_1329_join33 :
    blockEstimate 6286 1329 5553 512 = 4679392838400 :=
  block_append moment_6286_1329_join31 moment_6286_1329_join32 rfl rfl rfl
private theorem moment_6286_1329_join34 :
    blockEstimate 6286 1329 5169 896 = 8551093785920 :=
  block_append moment_6286_1329_join30 moment_6286_1329_join33 rfl rfl rfl
private theorem moment_6286_1329_join35 :
    blockEstimate 6286 1329 6065 256 = 2032351965637 :=
  block_append moment_6286_1329_part37 moment_6286_1329_part38 rfl rfl rfl
private theorem moment_6286_1329_join36 :
    blockEstimate 6286 1329 6321 256 = 1776070465782 :=
  block_append moment_6286_1329_part39 moment_6286_1329_part40 rfl rfl rfl
private theorem moment_6286_1329_join37 :
    blockEstimate 6286 1329 6065 512 = 3808422431419 :=
  block_append moment_6286_1329_join35 moment_6286_1329_join36 rfl rfl rfl
private theorem moment_6286_1329_join38 :
    blockEstimate 6286 1329 6577 256 = 1508542616132 :=
  block_append moment_6286_1329_part41 moment_6286_1329_part42 rfl rfl rfl
private theorem moment_6286_1329_join39 :
    blockEstimate 6286 1329 6833 256 = 1241742679048 :=
  block_append moment_6286_1329_part43 moment_6286_1329_part44 rfl rfl rfl
private theorem moment_6286_1329_join40 :
    blockEstimate 6286 1329 6577 512 = 2750285295180 :=
  block_append moment_6286_1329_join38 moment_6286_1329_join39 rfl rfl rfl
private theorem moment_6286_1329_join41 :
    blockEstimate 6286 1329 6065 1024 = 6558707726599 :=
  block_append moment_6286_1329_join37 moment_6286_1329_join40 rfl rfl rfl
private theorem moment_6286_1329_join42 :
    blockEstimate 6286 1329 5169 1920 = 15109801512519 :=
  block_append moment_6286_1329_join34 moment_6286_1329_join41 rfl rfl rfl
private theorem moment_6286_1329_join43 :
    blockEstimate 6286 1329 7217 256 = 860976673406 :=
  block_append moment_6286_1329_part46 moment_6286_1329_part47 rfl rfl rfl
private theorem moment_6286_1329_join44 :
    blockEstimate 6286 1329 7089 384 = 1384322288411 :=
  block_append moment_6286_1329_part45 moment_6286_1329_join43 rfl rfl rfl
private theorem moment_6286_1329_join45 :
    blockEstimate 6286 1329 7473 256 = 630812551708 :=
  block_append moment_6286_1329_part48 moment_6286_1329_part49 rfl rfl rfl
private theorem moment_6286_1329_join46 :
    blockEstimate 6286 1329 7729 256 = 426663431872 :=
  block_append moment_6286_1329_part50 moment_6286_1329_part51 rfl rfl rfl
private theorem moment_6286_1329_join47 :
    blockEstimate 6286 1329 7473 512 = 1057475983580 :=
  block_append moment_6286_1329_join45 moment_6286_1329_join46 rfl rfl rfl
private theorem moment_6286_1329_join48 :
    blockEstimate 6286 1329 7089 896 = 2441798271991 :=
  block_append moment_6286_1329_join44 moment_6286_1329_join47 rfl rfl rfl
private theorem moment_6286_1329_join49 :
    blockEstimate 6286 1329 7985 256 = 257453297344 :=
  block_append moment_6286_1329_part52 moment_6286_1329_part53 rfl rfl rfl
private theorem moment_6286_1329_join50 :
    blockEstimate 6286 1329 8241 256 = 127891394240 :=
  block_append moment_6286_1329_part54 moment_6286_1329_part55 rfl rfl rfl
private theorem moment_6286_1329_join51 :
    blockEstimate 6286 1329 7985 512 = 385344691584 :=
  block_append moment_6286_1329_join49 moment_6286_1329_join50 rfl rfl rfl
private theorem moment_6286_1329_join52 :
    blockEstimate 6286 1329 8497 256 = 42004254400 :=
  block_append moment_6286_1329_part56 moment_6286_1329_part57 rfl rfl rfl
private theorem moment_6286_1329_join53 :
    blockEstimate 6286 1329 8753 191 = 3683677456 :=
  block_append moment_6286_1329_part58 moment_6286_1329_part59 rfl rfl rfl
private theorem moment_6286_1329_join54 :
    blockEstimate 6286 1329 8497 447 = 45687931856 :=
  block_append moment_6286_1329_join52 moment_6286_1329_join53 rfl rfl rfl
private theorem moment_6286_1329_join55 :
    blockEstimate 6286 1329 7985 959 = 431032623440 :=
  block_append moment_6286_1329_join51 moment_6286_1329_join54 rfl rfl rfl
private theorem moment_6286_1329_join56 :
    blockEstimate 6286 1329 7089 1855 = 2872830895431 :=
  block_append moment_6286_1329_join48 moment_6286_1329_join55 rfl rfl rfl
private theorem moment_6286_1329_join57 :
    blockEstimate 6286 1329 5169 3775 = 17982632407950 :=
  block_append moment_6286_1329_join42 moment_6286_1329_join56 rfl rfl rfl
private theorem moment_6286_1329_join58 :
    blockEstimate 6286 1329 1329 7615 = 42045879552530 :=
  block_append moment_6286_1329_join28 moment_6286_1329_join57 rfl rfl rfl

private theorem moment_6286_1329 : momentEstimate 6286 1329 = 42045879552530 := moment_6286_1329_join58


theorem bank_checked : P3_7_1.BankOK terminalBank :=
  P3_7_1.checked terminalBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) moment_6286_1329

def witness : ℕ → RectArgs
  | 0 => ⟨![655181, 93597], ![1200, 1201]⟩
  | 1 => ⟨![668256, 80522], ![0, 1167]⟩
  | 2 => ⟨![667439, 81339], ![0, 1162]⟩
  | 3 => ⟨![667789, 80989], ![0, 1157]⟩
  | 4 => ⟨![666987, 81791], ![0, 1152]⟩
  | 5 => ⟨![667342, 81436], ![0, 1147]⟩
  | 6 => ⟨![666555, 82223], ![0, 1142]⟩
  | 7 => ⟨![666915, 81863], ![0, 1137]⟩
  | 8 => ⟨![666143, 82635], ![0, 1132]⟩
  | 9 => ⟨![666581, 82197], ![0, 1126]⟩
  | 10 => ⟨![665825, 82953], ![0, 1121]⟩
  | 11 => ⟨![666269, 82509], ![0, 1115]⟩
  | 12 => ⟨![665529, 83249], ![0, 1110]⟩
  | 13 => ⟨![664875, 83903], ![0, 1104]⟩
  | 14 => ⟨![665255, 83523], ![0, 1099]⟩
  | 15 => ⟨![664618, 84160], ![0, 1093]⟩
  | 16 => ⟨![665080, 83698], ![0, 1087]⟩
  | 17 => ⟨![664461, 84317], ![0, 1081]⟩
  | 18 => ⟨![663854, 84924], ![0, 1075]⟩
  | 19 => ⟨![663259, 85519], ![0, 1069]⟩
  | 20 => ⟨![663739, 85039], ![0, 1063]⟩
  | 21 => ⟨![663243, 85535], ![0, 1056]⟩
  | 22 => ⟨![662679, 86099], ![0, 1050]⟩
  | 23 => ⟨![662210, 86568], ![0, 1043]⟩
  | 24 => ⟨![661671, 87107], ![0, 1037]⟩
  | 25 => ⟨![661229, 87549], ![0, 1030]⟩
  | 26 => ⟨![660801, 87977], ![0, 1023]⟩
  | 27 => ⟨![660474, 88304], ![0, 1015]⟩
  | 28 => ⟨![660075, 88703], ![0, 1008]⟩
  | 29 => ⟨![658779, 89999], ![0, 1000]⟩
  | 30 => ⟨![658416, 90362], ![0, 993]⟩
  | 31 => ⟨![658251, 90527], ![0, 984]⟩
  | 32 => ⟨![657035, 91743], ![0, 976]⟩
  | 33 => ⟨![655947, 92831], ![0, 967]⟩
  | 34 => ⟨![654895, 93883], ![0, 958]⟩
  | 35 => ⟨![653879, 94899], ![0, 949]⟩
  | 36 => ⟨![652213, 96565], ![0, 939]⟩
  | 37 => ⟨![651339, 97439], ![0, 928]⟩
  | 38 => ⟨![648826, 99952], ![0, 917]⟩
  | 39 => ⟨![645893, 102885], ![0, 905]⟩
  | 40 => ⟨![641859, 106919], ![0, 891]⟩
  | 41 => ⟨![630789, 117989], ![0, 874]⟩
  | 42 => ⟨![560486, 188292], ![0, 835]⟩
  | 43 => ⟨![505149, 243629], ![0, 757]⟩
  | 44 => ⟨![465194, 283584], ![0, 649]⟩
  | 45 => ⟨![434665, 314113], ![0, 516]⟩
  | 46 => ⟨![410482, 338296], ![0, 362]⟩
  | 47 => ⟨![390747, 358031], ![0, 189]⟩
  | 48 => ⟨![374389, 374389], ![0, 0]⟩
  | _ => ⟨![0,0],![0,0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 237981634351639402470019032960 237983016197583795606018194880 237974669393747764868183404800 237974714729431480402698700800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 52 208830063500119727264939106240 208831279067808833265999425280 208830015753767835573581164800 208830061089451551108096460800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 210690025217966817514038297600 210691251201257917813534694400 210689984872625804282538144000 210690030208309519817053440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 209893849353966810641119617600 209895070871221536535174814400 209893814480418356726442144000 209893859816102072260957440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 211716809842756842624006881280 211718041570725436241009786880 211716775953247410193855852800 211716821288931125728371148800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 210910508379593658446552858880 210911735589116016929031312480 210910469625287411611628908800 210910514960971127146144204800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 212696698756103776468951234560 212697935973618183665590844160 212696652500291195744607187200 212696697835974911279122483200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 211880250747771321938975400960 211881483394329302279379135360 211880189251806728704285651200 211880234587490444238800947200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 213629895112304496296185159680 213631137566245215084431646720 213629815595194536105401299200 213629860930878251639916595200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 212637741274985340733747211520 212638978142452076289380570880 212637719394366742067574124800 212637764730050457602089420800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 214349224249132582897634679360 214350470715050562085019104320 214349172102547518121630675200 214349217438231233656145971200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 213344574238038564141700968000 213345815051309974049430216000 213344570544726778375153824000 213344615880410493909669120000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 215018104969678252983561216000 215019355174451589652478064000 215018056843292929160751264000 215018102178976644695266560000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 216493530160745632124718673920 216494788611529116091614136320 216493520609303350098058195200 216493565944987065632573491200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 215636690624229092900655429120 215637944296352835689691275520 215636621373254864953203667200 215636666708938580487718963200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 217072467726241878734927578560 217073729429107546966237618560 217072420084123330913557459200 217072465419807046448072755200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 216031416404561962506067124160 216032672264242960966172952960 216031385176461435486395347200 216031430512145151020910643200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 217425842698621821925909080960 217427106364828663769233606080 217425814725189478176421228800 217425860060873193710936524800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 52 218790355679247020110736760000 218791626986612137195618920000 218790325117050226813282464000 218790370452733942347797760000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 220125126288870794299497696000 220126405073582551971588595200 220125085874866579631089824000 220125131210550295165605120000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 219048579061503658020294048000 219049851819594299481765849600 219048518201541846764202144000 219048563537225562298717440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 52 220160946382695051450385489920 220162225344081801121572802560 220160940681140077490658259200 220160986016823793025173555200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 52 221423602273290620294958720000 221424888321383137886537280000 221423553741173736496277664000 221423599076857452030792960000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 52 222471627184108978741628418240 222472919083155088618291633920 222471613384631035937741779200 222471658720314751472257075200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 53 223674073029589961317760432640 223675371687653947406872327680 223673992395369047287821676800 223674037731052762822336972800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 53 224658377463185210925267120000 224659681625546888477336208000 224658305906731099826530464000 224658351242414815361045760000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 53 225610074667506390732917418240 225611384157343305893814134400 225609997725155981718353260800 225610043060839697252868556800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 53 226336157165693048699998080000 226337470686568628772081480000 226336150424355869580437664000 226336195760039585114952960000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 53 227221110441966457303539978240 227222428929392717028547153920 227221066344055831599569875200 227221111679739547134085171200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 53 230086868088625006189824000000 230088202605994196804601600000 230086858881383025604143264000 230086904217066741138658560000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1420 53 230887299570225575532890898240 230888638597980957330731529600 230887210212054690222732652800 230887255547738405757247948800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1421 53 231250671804627020346666485760 231252012823296903796084930560 231250668342924201473504620800 231250713678607917008019916800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1423 53 233922771470214561085555138560 233924127462601446013441413120 233922730831277448235899859200 233922776166961163770415155200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1425 53 236303811393404045788111530240 236305180699698468982963564800 236303800179398377732470124800 236303845515082093266985420800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1427 53 238597367284248984805041008640 238598749427814529692899051520 238597351686761677572594643200 238597397022445393107109939200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1429 53 240804327080658528310159296000 240805721592590364653338022400 240804266760334508920776864000 240804312096018224455292160000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1432 53 244405809170127134300939869440 244407223836482910968526284160 244405754478609653935430611200 244405799814293369469945907200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1434 53 246286530411617514627110707200 246287955578138620939053158400 246286519417223425428138144000 246286564752907140962653440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1438 53 251661282787087631070700328640 251662738047968980052101666080 251661241335656831547503980800 251661286671340547082019276800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1443 54 257872359028714606545943570560 257873849061593624310499234560 257872287569047601327954899200 257872332904731316862470195200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1449 54 266305897658763806110887945600 266307434878505972084668972800 266305842877240648251582624000 266305888212924363786097920000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1464 54 288800488235356486054831123200 288802151336573520433974432000 288800435775714375895722144000 288800481111398091430237440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1479 55 409468215844277656624666252800 409470554175844752475448271840 409468175151306653981635948800 409468220486990369516151244800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1476 55 477480262896363051802297368000 477482981760834732436557888000 477480231356726164164552864000 477480276692409879699068160000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 55 511818599033200377683167111200 511821509984733129909793048800 511818570081474345207179424000 511818615417158060741694720000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 55 529709362428810639721068650880 529712373415466619837078543360 529709355951014196013751251200 529709401286697911548266547200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 54 538749068868124896700860278400 538752130368735670742501599680 538749066329868675658970476800 538749111665552391193485772800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 54 542764181102511084969798547200 542767265003788993237764648960 542764180430568593249695084800 542764225766252308784210380800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 54 543802171484466169451725536000 543805261155401904828952560000 543802108831725101386410144000 543802154167408816920925440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 49) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2359 (max 1 i.val) (witness i.val) := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41
  · exact check42
  · exact check43
  · exact check44
  · exact check45
  · exact check46
  · exact check47
  · exact check48

theorem positive {h : ℕ} (lo : 2359≤h) (hi : h≤33579) (i : Fin 49) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179818 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

#print axioms bank_checked
#print axioms positive
end Lower6960.TerminalReceipts

end Merged6967_R6960TerminalReceipts
