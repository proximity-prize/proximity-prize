import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdZZ6ou4c
import ProximityPrize.SubmissionLower.DdZdwiBha
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_MvPowerSeries_NoZeroDivisors

section Merged6967_A6966FinalAnchorSpace
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 2000000

namespace A6966FinalAnchorSpace
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

def gradeLimit (t : ℕ) : ℕ :=
  if 58 < t then 120 else
  if t ≤ 36 then 142 else
  if t ≤ 37 then 141 else
  if t ≤ 38 then 140 else
  if t ≤ 39 then 139 else
  if t ≤ 40 then 138 else
  if t ≤ 41 then 137 else
  if t ≤ 42 then 136 else
  if t ≤ 43 then 135 else
  if t ≤ 44 then 134 else
  if t ≤ 45 then 133 else
  if t ≤ 46 then 132 else
  if t ≤ 47 then 131 else
  if t ≤ 48 then 130 else
  if t ≤ 49 then 129 else
  if t ≤ 50 then 128 else
  if t ≤ 51 then 127 else
  if t ≤ 52 then 126 else
  if t ≤ 53 then 125 else
  if t ≤ 54 then 124 else
  if t ≤ 55 then 123 else
  if t ≤ 56 then 122 else
  if t ≤ 57 then 121 else
  if t ≤ 58 then 120 else
  120

def cap (s : ℕ) : ℕ :=
  min s (min 58 (
  if s ≤ 120 then 58 else
  if s ≤ 121 then 57 else
  if s ≤ 122 then 56 else
  if s ≤ 123 then 55 else
  if s ≤ 124 then 54 else
  if s ≤ 125 then 53 else
  if s ≤ 126 then 52 else
  if s ≤ 127 then 51 else
  if s ≤ 128 then 50 else
  if s ≤ 129 then 49 else
  if s ≤ 130 then 48 else
  if s ≤ 131 then 47 else
  if s ≤ 132 then 46 else
  if s ≤ 133 then 45 else
  if s ≤ 134 then 44 else
  if s ≤ 135 then 43 else
  if s ≤ 136 then 42 else
  if s ≤ 137 then 41 else
  if s ≤ 138 then 40 else
  if s ≤ 139 then 39 else
  if s ≤ 140 then 38 else
  if s ≤ 141 then 37 else
  if s ≤ 142 then 36 else
  36))

theorem cap_le_grade (s : ℕ) : cap s ≤ s := min_le_left _ _

theorem cap_le_index (s : ℕ) : cap s ≤ 58 := (min_le_right _ _).trans (min_le_left _ _)

private theorem gradeLimit_tail {t : ℕ} (ht : 58 < t) : gradeLimit t = 120 := by
  simp only [gradeLimit, if_pos ht]

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n < 59
  · have checks : ∀ t : Fin 59, gradeLimit (t.val + 1) ≤ gradeLimit t := by decide +kernel
    exact checks ⟨n, hn⟩
  · rw [gradeLimit_tail (by omega), gradeLimit_tail (by omega)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 58) (hts : t ≤ s) (h : s ≤ gradeLimit t) : t ≤ cap s := by
  have hb : (List.range 59).all (fun i => decide (gradeLimit i ≤ 142)) = true := by decide +kernel
  have hh := of_decide_eq_true (List.all_eq_true.mp hb t (List.mem_range.mpr (by omega)))
  have checks : (List.range 143).all (fun s => (List.range 59).all
      (fun t => decide (t ≤ s → s ≤ gradeLimit t → t ≤ cap s))) = true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checks s
    (List.mem_range.mpr (by omega))) t (List.mem_range.mpr (by omega)))) hts h

theorem cap_active (s : ℕ) (hs : s ≤ 142) : s + cap s ≤ 178 := by
  have checks : (List.range 143).all (fun g => decide (g + cap g ≤ 178)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 142 ∧ u.some.weight (fun i => i.val) ≤ 58 ∧ u (some 3) ≤ 15 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133484) ≤ 106 * 179808 - 1 + 58

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 106 x y).domRestrict _

end A6966FinalAnchorSpace

end Merged6967_A6966FinalAnchorSpace

section Merged6967_ListProofA
set_option Elab.async false

set_option Elab.async false
set_option autoImplicit true
section
namespace CJ0
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
theorem source_dimension (A : ℕ) (s : Source) (hs : ShapeOK s)
    (hw : s.m ≤ s.m*A - N*s.B) :
    Fintype.card (ColumnIndex A s) + N*(∑ j ∈ s.E, j.q) =
      s.m*A*s.E.card + ∑ j ∈ s.E, j.v := by
  classical
  have hbase : N*s.B ≤ s.m*A := by have := hs.multiplicity; omega
  have hone (j : Jet) (hj : j ∈ s.E) :
      width A s j + N*j.q = s.m*A + j.v := by
    have h := (Nat.mul_le_mul_left N (hs.support j hj).1).trans hbase
    unfold width
    omega
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Finset.sum_coe_sort]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ s.E, (s.m*A + j.v) := Finset.sum_congr rfl hone
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm s.E.card]
private theorem column_injective (A : ℕ) (s : Source) : Function.Injective (column A s) := by
  rintro ⟨⟨⟨c, b, a⟩, hj⟩, x⟩ ⟨⟨⟨c', b', a'⟩, hj'⟩, x'⟩ he
  have hc : c = c' := congrArg (fun z : SourceColumn 2 => z.higher 1) he
  have hb : b = b' := congrArg (fun z : SourceColumn 2 => z.higher 0) he
  have ha : a = a' := congrArg SourceColumn.y₀ he
  subst c'; subst b'; subst a'
  have hx : x.val = x'.val := congrArg SourceColumn.x he
  rw [Fin.ext hx]
theorem interpolant {A : ℕ} {s : Source} (hs : ShapeOK s)
    (hw : s.m ≤ s.m*A-N*s.B) (w : Node → K)
    (hr : stackRank A s w < Fintype.card (ColumnIndex A s)) :
    ∃ Q : DifferentialPolynomial K 2, OrderTwo s Q ∧
      differentialWeightedDegree N Q < s.m*A ∧
      ∀ i, SatisfiesLocalConstraints s.m (node i) (w i) Q := by
  classical
  let cols := column A s
  let M := localConstraintMatrix s.m (fun i => node i) w cols
  have hdep : ¬ LinearIndependent K M.col := by
    intro hi
    have he : M.rank = Fintype.card (ColumnIndex A s) :=
      M.rank_eq_finrank_span_cols.trans (finrank_span_eq_card hi)
    exact (Nat.ne_of_lt hr) he
  obtain ⟨v, hv, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let Q := SourceColumn.interpolant cols v
  have hQ : Q ≠ 0 := fun hz => hj (congrFun ((SourceColumn.interpolant_eq_zero_iff
    (column_injective A s)).mp hz) j)
  have hker : M.mulVec v = 0 := by
    funext row
    have h := congrFun hv row
    simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_comm, Matrix.col_apply] using h
  have hlocal := (localConstraintMatrix_mulVec_eq_zero_iff _ _ _ _ _).mp hker
  have hbase : N*s.B ≤ s.m*A := by have := hs.multiplicity; omega
  have hpos : 0 < s.m*A := by have := hs.multiplicity; omega
  have hsupp (u) (hu : u ∈ Q.support) : ∃ i, u = (cols i).exponent := by
    apply Astra7.generic_source_support (RingHom.id K) cols v u
    simpa only [MvPolynomial.map_id] using hu
  have ht : jetTotalDegree Q ≤ s.B := by
    apply (jetTotalDegree_le_iff _ _).mpr
    intro u hu
    obtain ⟨i, rfl⟩ := hsupp u hu
    simpa [cols, column, Jet.q, Fin.sum_univ_two, Nat.add_assoc] using (hs.support _ i.1.property).1
  have hi : Q.weightedTotalDegree indexWeight ≤ s.J := by
    apply Finset.sup_le
    intro u hu
    obtain ⟨i, rfl⟩ := hsupp u hu
    simpa [cols, column, indexWeight, SourceColumn.weight_exponent, Fin.sum_univ_two,
      Jet.v, Nat.mul_comm] using (hs.support _ i.1.property).2.1
  have hc : jetDegree Q (Fin.last 2) ≤ s.C := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    obtain ⟨i, rfl⟩ := hsupp u hu
    change (cols i).exponent (some (1 : Fin 2).succ) ≤ s.C
    rw [SourceColumn.exponent_succ]
    exact (hs.support _ i.1.property).2.2
  refine ⟨Q, ⟨hQ, ht, hi, hc⟩, ?_, hlocal⟩
  apply (Finset.sup_lt_iff hpos).mpr
  intro u hu
  obtain ⟨i, rfl⟩ := hsupp u hu
  have hx := i.2.isLt
  have hq := (Nat.mul_le_mul_left N (hs.support _ i.1.property).1).trans hbase
  simp only [width, Jet.q, Jet.v, N] at hx hq
  rw [SourceColumn.weight_exponent]
  simp [cols, column, differentialWeight, Fin.sum_univ_two, N]
  omega
theorem specializes {A : ℕ} {s : Source} {w : Node → K} {Q : DifferentialPolynomial K 2}
    (hwt : differentialWeightedDegree N Q < s.m*A)
    (hlocal : ∀ i, SatisfiesLocalConstraints s.m (node i) (w i) Q) :
    ∀ f ∈ close A w, differentialSpecialization Q f = 0 := by
  intro f hf
  have hd : f.natDegree ≤ N := by
    by_cases hz : f = 0
    · simp [hz]
    · have h := (natDegree_lt_iff_degree_lt hz).2 hf.1
      exact Nat.le_of_lt_succ h
  let hits := ReedSolomon.polynomialAgreementSet node w f
  apply differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    node w hits hwt (fun i _ => hlocal i) f hd node.injective.injOn hf.2
  intro i hi
  exact (Finset.mem_filter.mp hi).2
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
theorem section_capacity {A : ℕ} {w : Node → K} {T : Finset (Polynomial K)}
    (h : (T : Set (Polynomial K)) ⊆ close A w) (hA : AgreementOK A) (cap : ℕ)
    (hsection : ∀ i : Node, (∃ γ ∈ T, γ.eval (node i) ≠ w i) →
      (T.filter fun γ => γ.eval (node i) = w i).card ≤ cap) :
    (gap A) * T.card ≤ errors A * cap + (gap A) := by
  classical
  have hd := hA.gt_degree
  have hn := hA.lt_length
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (gap A) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : (Polynomial K)) : Finset Node := univ.filter fun i => γ.eval (node i) = w i
  let common : Finset Node := univ.filter fun i => ∀ γ ∈ T, γ.eval (node i) = w i
  let nodes : Finset Node := univ \ common
  have common_le (γ : (Polynomial K)) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : (Polynomial K)) (hγ : γ ∈ T) : A ≤ (hits γ).card := by
    exact (h hγ).2
  have degree (a : (Polynomial K)) (ha : a ∈ T) : a.natDegree ≤ N := by
    by_cases hz : a = 0
    · simp [hz]
    · have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hz).2 (h ha).1
      exact Nat.le_of_lt_succ hdeg
  have pair_count (a : (Polynomial K)) (ha : a ∈ T) (b : (Polynomial K)) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ N := by
    refine (FrobeniusLocator.Strata.root_nodes_card_le node node.injective
      (a-b) (sub_ne_zero.mpr hab) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (degree a ha) (degree b hb)))
    intro i hi
    change (a-b).eval (node i) = 0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ N :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := A - common.card
  let t := N - common.card
  have ht : t = x - (gap A) := by dsimp [t, x, gap]; omega
  have hx : gap A ≤ x := by dsimp [x, gap]; omega
  have hnodes : nodes.card = x + errors A := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    change n - common.card = (A-common.card) + (n-A)
    have hbound := hcommon.trans hd.le
    omega
  have exists_trim (γ : (Polynomial K)) : ∃ B : Finset Node, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : (Polynomial K)) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : (Polynomial K)) (ha : a ∈ T) (b : (Polynomial K)) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : Node) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, γ.eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic (errors A) _ _ _ _ (by omega) (Nat.sub_pos_of_lt hd) hx (Nat.sub_pos_of_lt hn) second first
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Finset MvPolynomial
open scoped Polynomial BigOperators
open K1_14_6 (curve_degree_nat)
def valueCut (x a : K) : CoeffRing :=
  (∑ i : Fin k, C (embed x ^ i.val) * MvPolynomial.X i) - C (embed a)
theorem valueCut_degree (x a : K) : (valueCut x a).totalDegree ≤ 1 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply totalDegree_finsetSum_le
  intro i _
  simpa only [totalDegree_C, totalDegree_X, zero_add] using
    (totalDegree_mul (C (embed x ^ i.val)) (MvPolynomial.X i))
private theorem natDegree_bound {f : (Polynomial K)} (h : f.degree < k) : f.natDegree < k := by
  by_cases hz : f = 0
  · rw [hz, Polynomial.natDegree_zero]
    exact Nat.zero_lt_succ _
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 h
theorem valueCut_eval {f : (Polynomial K)} (h : f.degree < k) (x a : K) :
    aeval (coeffPoint f) (valueCut x a) = 0 ↔ f.eval x = a := by
  have heval : f.eval x = ∑ j : Fin k, f.coeff j.val * x ^ j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => f.coeff j * x ^ j)]
    exact Polynomial.eval_eq_sum_range' (natDegree_bound h) x
  have hmap : embed (∑ j : Fin k, f.coeff j.val * x ^ j.val) =
      ∑ j : Fin k, embed x ^ j.val * embed (f.coeff j.val) := by
    rw [map_sum]
    exact sum_congr rfl fun _ _ => by rw [map_mul, map_pow, mul_comm]
  simp only [valueCut, coeffPoint, map_sub, map_sum, map_mul, aeval_C, aeval_X, sub_eq_zero,
    Algebra.algebraMap_self_apply]
  rw [heval, ← hmap]
  exact embed.injective.eq_iff
private theorem coeffPoint_injOn {A w} {Γ : Finset (Polynomial K)} (h : (Γ : Set (Polynomial K)) ⊆ close A w) :
    Set.InjOn coeffPoint (Γ : Set (Polynomial K)) := by
  intro f hf g hg heq
  apply Polynomial.ext
  intro j
  by_cases hj : j < k
  · exact embed.injective (congrFun heq ⟨j, hj⟩)
  · have hfj := (natDegree_bound (h hf).1).trans_le (Nat.le_of_not_gt hj)
    have hgj := (natDegree_bound (h hg).1).trans_le (Nat.le_of_not_gt hj)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hfj, Polynomial.coeff_eq_zero_of_natDegree_lt hgj]
private theorem zeroDim_count {A w} {Γ : Finset (Polynomial K)} (h : (Γ : Set (Polynomial K)) ⊆ close A w) (P : Ideal CoeffRing)
    (hdim : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ Γ, coeffPoint γ ∈ zeroLocus Geo P) :
    (Γ.card : ℚ) ≤ affineDegree P := by
  classical
  let A := Γ.image (coeffPoint)
  have hA : A.card = Γ.card := card_image_of_injOn (coeffPoint_injOn h)
  have hsub : (A : Set _) ⊆ zeroLocus Geo P := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := Geo) P hdim
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hA] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree
private theorem section_count {A w} {Γ : Finset (Polynomial K)} (h : (Γ : Set (Polynomial K)) ⊆ close A w) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hpoints : ∀ γ ∈ Γ, coeffPoint γ ∈ zeroLocus Geo P)
    (x a : K) (hmiss : ∃ γ ∈ Γ, γ.eval x ≠ a)
    {c : ℚ} (hc : 0 ≤ c)
    (bound : ∀ (V : Finset (Polynomial K)), V ⊆ Γ → ∀ (Q : Ideal CoeffRing), Q.IsPrime →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, coeffPoint γ ∈ zeroLocus Geo Q) →
      (V.card : ℚ) ≤ c * affineDegree Q) :
    ((Γ.filter fun γ => γ.eval x = a).card : ℚ) ≤ c * affineDegree P := by
  classical
  let prime := hP
  let cut := valueCut x a
  let Ps := (P ⊔ Ideal.span {cut}).minimalPrimesFinset
  let U := Γ.filter fun γ => γ.eval x = a
  let part (Q : Ideal CoeffRing) := U.filter fun f => coeffPoint f ∈ zeroLocus Geo Q
  have hproper : cut ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hm
    exact hv ((valueCut_eval (h hγ).1 x a).mp (hpoints γ hγ _ hm))
  have hcover : U ⊆ Ps.biUnion part := by
    intro γ hγ
    obtain ⟨hγΓ, hv⟩ := mem_filter.mp hγ
    have hp : coeffPoint γ ∈ zeroLocus Geo (P ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ, (valueCut_eval (h hγΓ).1 x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact mem_biUnion.mpr ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  have hsum : U.card ≤ ∑ Q ∈ Ps, (part Q).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hdeg : (∑ Q ∈ Ps, affineDegree Q) ≤ affineDegree P := by
    simpa only [Ps, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
  change (U.card : ℚ) ≤ c * affineDegree P
  calc
    _ ≤ ∑ Q ∈ Ps, ((part Q).card : ℚ) := by exact_mod_cast hsum
    _ ≤ ∑ Q ∈ Ps, c * affineDegree Q := by
      apply sum_le_sum
      intro Q hQ
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact bound _ ((filter_subset _ _).trans (filter_subset _ _)) Q hmin.isPrime
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => (mem_filter.mp hγ).2)
    _ ≤ c * affineDegree P := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hdeg hc
theorem curve_capacity {A w} {T : Finset (Polynomial K)} (hT : (T : Set (Polynomial K)) ⊆ close A w)
    (hA : AgreementOK A) {P : Ideal CoeffRing} (hp : P.IsPrime)
    (hd : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ f ∈ T, coeffPoint f ∈ zeroLocus Geo P) :
    ((gap A : ℕ) : ℚ)*T.card ≤ (errors A : ℚ)*affineDegree P + gap A ∧
    (T.card : ℚ) ≤ 2*affineDegree P := by
  classical
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hp hd
  have hcap := section_capacity hT hA δ fun i hi => by
    have hc := section_count hT hp hpoints (node i) (w i) hi (c := 1) zero_le_one
      (fun _ hV Q _ hdim hpts => by
        rw [one_mul]
        exact zeroDim_count (fun _ hf => hT (hV hf)) Q (by omega) hpts)
    rw [one_mul, hdeg] at hc
    exact_mod_cast hc
  rw [hdeg]
  refine ⟨by exact_mod_cast hcap, ?_⟩
  suffices hn : T.card ≤ 2*δ by exact_mod_cast hn
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left (gap A) (show 2*δ + 1 ≤ T.card by omega)
  rw [Nat.mul_add, Nat.mul_one] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hA.beta_lt_two hδ
  rw [mul_comm 2 (gap A), mul_assoc] at hstrict
  omega
private theorem surface_capacity {A w} {T : Finset (Polynomial K)} (hT : (T : Set (Polynomial K)) ⊆ close A w)
    (hA : AgreementOK A) {P : Ideal CoeffRing} (hp : P.IsPrime)
    (hd : (affineHilbertPolynomial P).natDegree = 2)
    (hpoints : ∀ f ∈ T, coeffPoint f ∈ zeroLocus Geo P) :
    (gap A : ℚ)*T.card ≤ (errors A : ℚ)*(2*affineDegree P) + gap A := by
  classical
  let cost := 2*affineDegree P
  have hcost : 0 ≤ cost := mul_nonneg (by decide) (affineDegree_nonneg P)
  have hn := section_capacity hT hA ⌊cost⌋₊ fun i hi => by
    apply (Nat.le_floor_iff hcost).mpr
    apply section_count hT hp hpoints (node i) (w i) hi (c := 2) (by decide)
    exact fun _ hV _ hprime hdim hpts =>
      (curve_capacity (fun _ hf => hT (hV hf)) hA hprime (by omega) hpts).2
  have hq : (gap A : ℚ)*T.card ≤ (errors A : ℚ)*(⌊cost⌋₊ : ℚ) + gap A := by exact_mod_cast hn
  exact hq.trans (add_le_add (mul_le_mul_of_nonneg_left (Nat.floor_le hcost)
    (Nat.cast_nonneg (errors A))) le_rfl)
theorem family_capacity {A w r budget} {T : Finset (Polynomial K)} (hT : (T : Set (Polynomial K)) ⊆ close A w)
    (hA : AgreementOK A) (hr : r = 1 ∨ r = 2) (F : Family r) (hg : ImageDegrees F budget)
    (hcover : ∀ f ∈ T, ∃ i, coeffPoint f ∈ (F.chart i).imageSet) :
    (gap A : ℚ)*T.card ≤ (errors A : ℚ)*(r*budget : ℕ) + (gap A : ℚ)*F.count := by
  classical
  let part (i : Fin F.count) := T.filter fun f => coeffPoint f ∈ (F.chart i).imageSet
  have hc : T.card ≤ ∑ i, (part i).card := by
    apply (card_le_card (t := univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i, hi⟩ := hcover f hf
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hf, hi⟩⟩
  have hone (i : Fin F.count) : (gap A : ℚ)*(part i).card ≤
      (errors A : ℚ)*r*affineDegree (F.chart i).ideal + gap A := by
    have hsub : (part i : Set (Polynomial K)) ⊆ close A w := fun _ hf => hT (mem_filter.mp hf).1
    have hp : ∀ f ∈ part i, coeffPoint f ∈ zeroLocus Geo (F.chart i).ideal :=
      fun _ hf => zeroLocus_vanishingIdeal_le _ (mem_filter.mp hf).2
    rcases hr with h | h
    · have hh := (curve_capacity hsub hA (hg.prime i) ((hg.dimension i).trans h) hp).1
      simpa only [h, Nat.cast_one, mul_one] using hh
    · have hh := surface_capacity hsub hA (hg.prime i) ((hg.dimension i).trans h) hp
      simpa only [h, Nat.cast_ofNat, mul_assoc] using hh
  have hq : (T.card : ℚ) ≤ ∑ i, ((part i).card : ℚ) := by exact_mod_cast hc
  calc
    _ ≤ (gap A : ℚ) * ∑ i, ((part i).card : ℚ) := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    _ = ∑ i, (gap A : ℚ) * (part i).card := mul_sum ..
    _ ≤ _ := sum_le_sum fun i _ => hone i
    _ = (errors A : ℚ)*r * (∑ i, affineDegree (F.chart i).ideal) + (gap A : ℚ)*F.count := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin, mul_comm (F.count : ℚ)]
    _ ≤ _ := by
      rw [Nat.cast_mul, ← mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left hg.total
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) le_rfl
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Polynomial PolynomialDifferential Finset
open scoped BigOperators
def c1 : Prop :=
  ∀ A s cut, ShapeOK s → s.m ≤ s.m*A - N*s.B → cut ≤ s.B+1 → SilentTail s cut →
    originRank A s ≤ prefixRank s cut
def c2 : Prop :=
  ∀ A s, ShapeOK s → s.m ≤ s.m*A - N*s.B → ∀ w : Node → K,
    stackRank A s w ≤ n * originRank A s
def c5 : Prop :=
  ∀ s, ShapeOK s → ∀ Q, OrderTwo s Q →
    ∃ Q₁, OrderOne s Q₁ ∧ ∀ f : (Polynomial K), f.degree < k →
      differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
      differentialSpecialization Q₁ f = 0
def c6 : Prop :=
  ∀ s, ShapeOK s → ∀ Q₁, OrderOne s Q₁ →
    ∃ F : Family 1, Family₁ s F ∧ CoversRegular F Q₁
def c7 : Prop :=
  ∀ s, ShapeOK s → ∀ F : Family 1, Family₁ s F → ImageDegrees F (R₁ s)
def c8 : Prop :=
  ∀ s, ShapeOK s → ∀ Q₁, OrderOne s Q₁ →
    ∃ G : Polynomial (Polynomial K), G ≠ 0 ∧ G.natDegree ≤ H s*(H s-1) ∧
      ∀ f : (Polynomial K), f.degree < k → differentialSpecialization Q₁ f = 0 →
        ¬ RegularRoot Q₁ f → G.eval f = 0
end
end CJ0
end
section
namespace CJ0_1
noncomputable section
open CJ0 (Jet blockEntry)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
abbrev LocalExponent := LocalVariable 2 →₀ ℕ
def rowJet (e : LocalExponent) : Jet :=
  ⟨e (localY (1 : Fin 2)), e (localY (0 : Fin 2)), e (localE 2)⟩
def rowBalance (e : LocalExponent) : ℤ :=
  (e (localT 2) : ℤ) - (rowJet e).a - (rowJet e).v
def colBalance (x : ℕ) (j : Jet) : ℤ := (x : ℤ) - j.v
private def exponent (t h d l : ℕ) : LocalExponent :=
  Finsupp.single (localT 2) t + Finsupp.single (localE 2) h +
    Finsupp.single (localY (0 : Fin 2)) d + Finsupp.single (localY (1 : Fin 2)) l
private theorem exponent_eq_iff (t h d l : ℕ) (e : LocalExponent) :
    exponent t h d l = e ↔
      t = e (localT 2) ∧ h = (rowJet e).a ∧ d = (rowJet e).b ∧ l = (rowJet e).c := by
  classical
  constructor
  · intro he
    have atVar (v : LocalVariable 2) := DFunLike.congr_fun he v
    exact ⟨by simpa [exponent, localT, localE, localAux, localY] using atVar (localT 2),
      by simpa [exponent, rowJet, Jet.a, localT, localE, localAux, localY] using atVar (localE 2),
      by simpa [exponent, rowJet, Jet.b, localT, localE, localAux, localY] using
        atVar (localY (0 : Fin 2)),
      by simpa [exponent, rowJet, Jet.c, localT, localE, localAux, localY] using
        atVar (localY (1 : Fin 2))⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ext v
    rcases v with _ | (_ | j)
    · simp [exponent, localT, localE, localAux, localY]
    · simp [exponent, rowJet, Jet.a, localT, localE, localAux, localY]
    · fin_cases j <;> simp [exponent, rowJet, Jet.b, Jet.c, localT, localE, localAux, localY]
variable {F : Type*} [CommRing F]
private theorem origin_substitution (x a b c : ℕ) :
    unscaledLocalSubstitution 2 (0 : F) 0 (sourceMonomial x a ![b,c]) =
      ∑ h ∈ Finset.range (a+1), ∑ j ∈ Finset.range (a-h+1),
        monomial (exponent (x+h+j+2*(a-h-j)) h (b+j) (c+(a-h-j)))
          ((-1 : F)^(a-h-j) * (a.choose h : F) * ((a-h).choose j : F)) := by
  classical
  let localX : LocalPolynomial F 2 := MvPolynomial.X (localT 2)
  let hiddenTerm : LocalPolynomial F 2 := localX * MvPolynomial.X (localE 2)
  let jetOne : LocalPolynomial F 2 := MvPolynomial.X (localY (0 : Fin 2))
  let jetTwo : LocalPolynomial F 2 := MvPolynomial.X (localY (1 : Fin 2))
  let firstTerm := localX * jetOne
  let secondTerm := -(localX^2 * jetTwo)
  have h₀ : unscaledLocalSubstitution 2 (0 : F) 0 (MvPolynomial.X (some 0)) = hiddenTerm + (firstTerm + secondTerm) := by
    simp [localCorrection, Fin.sum_univ_two, hiddenTerm, firstTerm, secondTerm, localX, jetOne, jetTwo]
    ac_rfl
  rw [sourceMonomial, Fin.prod_univ_two, map_mul, map_mul, map_mul,
    map_pow, map_pow, map_pow, map_pow, h₀]
  simp only [unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_succ, C_0, zero_add,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change localX^x * (hiddenTerm+(firstTerm+secondTerm))^a * (jetOne^b*jetTwo^c) = _
  rw [add_pow hiddenTerm (firstTerm+secondTerm), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [add_pow firstTerm secondTerm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hW : secondTerm = monomial (Finsupp.single (localT 2) 2 +
      Finsupp.single (localY (1 : Fin 2)) 1) (-1) := by
    change -(MvPolynomial.X (localT 2)^2 * MvPolynomial.X (localY (1 : Fin 2))) = _
    rw [ X_pow_eq_monomial]
    simp only [MvPolynomial.X, monomial_mul_monomial, one_mul, map_neg]
  have hE : hiddenTerm = monomial (Finsupp.single (localT 2) 1 +
      Finsupp.single (localE 2) 1) 1 := by simp [hiddenTerm, localX, MvPolynomial.X]
  have hV : firstTerm = monomial (Finsupp.single (localT 2) 1 +
      Finsupp.single (localY (0 : Fin 2)) 1) 1 := by simp [firstTerm, localX, jetOne, MvPolynomial.X]
  have hcast (n : ℕ) : (n : LocalPolynomial F 2) = monomial 0 (n : F) := by
    rw [monomial_zero', map_natCast]
  rw [hE, hV, hW]
  simp only [localX, jetOne, jetTwo, X_pow_eq_monomial, monomial_pow,
    hcast, monomial_mul_monomial, one_mul, mul_one, one_pow]
  apply congrArg₂ (fun a b => (monomial a b : LocalPolynomial F 2))
  · apply Finsupp.ext
    intro v
    rcases v with _ | (_ | u)
    · simp [exponent, localT, localE, localAux, localY, Nat.mul_comm, Nat.add_assoc]
    · simp [exponent, localT, localE, localAux, localY]
    · fin_cases u <;>
        simp [exponent, localT, localE, localAux, localY, Nat.add_comm]
  · ring
theorem origin_coefficient (x : ℕ) (j : Jet) (e : LocalExponent) :
    (unscaledLocalSubstitution 2 (0 : ZMod CJ0.p) 0
       (sourceMonomial x j.a ![j.b,j.c])).coeff e =
      if rowBalance e = colBalance x j then blockEntry (rowJet e) j else 0 := by
  classical
  let r := rowJet e
  let P : Prop := rowBalance e = colBalance x j ∧
    (j.b ≤ r.b ∧ j.c ≤ r.c ∧ r.a + (r.b-j.b) + (r.c-j.c) = j.a)
  have hexp (h u : ℕ) (hh : h ≤ j.a) (hu : u ≤ j.a-h) :
      exponent (x+h+u+2*(j.a-h-u)) h (j.b+u) (j.c+(j.a-h-u)) = e ↔
        P ∧ h = r.a ∧ u = r.b-j.b := by
    rw [exponent_eq_iff]
    change (x+h+u+2*(j.a-h-u) = e (localT 2) ∧
      h = r.a ∧ j.b+u = r.b ∧ j.c+(j.a-h-u) = r.c) ↔
      ((e (localT 2) : ℤ) - r.a - (r.b+2*r.c : ℕ) =
       (x : ℤ) - (j.b+2*j.c : ℕ) ∧
         (j.b ≤ r.b ∧ j.c ≤ r.c ∧ r.a + (r.b-j.b) + (r.c-j.c) = j.a)) ∧
       h = r.a ∧ u = r.b-j.b
    omega
  rw [origin_substitution]
  simp_rw [coeff_sum, coeff_monomial]
  by_cases hp : P
  · obtain ⟨hg, hb, hc, ha⟩ := hp
    have hh : r.a ≤ j.a := by omega
    have hu : r.b-j.b ≤ j.a-r.a := by omega
    rw [Finset.sum_eq_single_of_mem r.a (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem (r.b-j.b) (Finset.mem_range.mpr (by omega))]
      · rw [ite_eq_left ((hexp _ _ hh hu).2 ⟨⟨hg, hb, hc, ha⟩, rfl, rfl⟩), ite_eq_left hg]
        change _ = blockEntry r j
        rw [blockEntry, ite_eq_left ⟨hb, hc, ha⟩, show j.a-r.a-(r.b-j.b) = r.c-j.c by omega]
      · intro u hmem hne
        rw [ite_eq_right (fun he => hne ((hexp _ _ hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))).1 he).2.2)]
    · intro h hmem hne
      apply Finset.sum_eq_zero
      intro u humem
      rw [ite_eq_right (fun he => hne ((hexp _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp humem))).1 he).2.1)]
  · have hz := fun h u (hh : h ≤ j.a) (hu : u ≤ j.a-h) he =>
      hp ((hexp h u hh hu).1 he).1
    have hzero : (if rowBalance e = colBalance x j then blockEntry r j else 0) = 0 := by
      split
      · rename_i hg
        exact ite_eq_right (fun hb => hp ⟨hg, hb⟩)
      · rfl
    rw [hzero]
    apply Finset.sum_eq_zero
    intro h hmem
    apply Finset.sum_eq_zero
    intro u humem
    rw [ite_eq_right (hz h u (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)) (Nat.lt_succ_iff.mp (Finset.mem_range.mp humem)))]
end
end CJ0_1
end
section
namespace CJ0_1
noncomputable section
open scoped BigOperators Matrix
theorem rank_blockDiagonal_le {F I : Type*} [Field F] [Fintype I]
    {R C : I → Type*} [∀ i, Fintype (C i)] [DecidableEq I]
    (M : ∀ i, Matrix (R i) (C i) F) :
    (Matrix.blockDiagonal' M).rank ≤ ∑ i, (M i).rank := by
  let Φ := (Matrix.blockDiagonal' M).mulVecLin
  let φ := fun i => (M i).mulVecLin
  let project : Φ.range →ₗ[F] ∀ i, (φ i).range :=
    { toFun y i := ⟨fun r => y.val ⟨i,r⟩, by
        obtain ⟨v, hv⟩ := y.property
        refine ⟨fun c => v ⟨i,c⟩, ?_⟩
        rw [← hv]
        funext r
        change (∑ c : C i, M i r c * v ⟨i,c⟩) =
          ∑ j : Sigma C, Matrix.blockDiagonal' M ⟨i,r⟩ j * v j
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.sum_eq_single i]
        · simp [Matrix.blockDiagonal'_apply_eq]
        · intro j _ hji
          apply Finset.sum_eq_zero
          intro c _
          rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hji), zero_mul]
        · simp⟩
      map_add' x y := by ext i r; rfl
      map_smul' t x := by ext i r; rfl }
  have hinj : Function.Injective project := by
    intro x y h
    apply Subtype.ext
    funext ⟨i,r⟩
    exact congrFun (congrArg Subtype.val (congrFun h i)) r
  change Module.finrank F Φ.range ≤ ∑ i, Module.finrank F (φ i).range
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans_eq
    (Module.finrank_pi_fintype F)
end
end CJ0_1
end
section
namespace CJ0_1
noncomputable section
open CJ0 (Source ShapeOK SilentTail Jet ColumnIndex column blockRows blockCols blockMatrix
  blockEntry prefixRank p)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Matrix
local instance : Fact (Nat.Prime p) := ⟨KoalaBear.is_prime⟩
abbrev OriginRow (s : Source) := Unit × LowContactIndex 2 s.m
abbrev OriginCol (A : ℕ) (s : Source) := ColumnIndex A s
private def origin (A : ℕ) (s : Source) : Matrix (OriginRow s) (OriginCol A s) (ZMod p) :=
  localConstraintMatrix s.m (fun _ : Unit => 0) (fun _ => 0) (column A s)
private theorem origin_entry {A s} (r : OriginRow s) (j : OriginCol A s) :
    origin A s r j =
      if rowBalance r.2.val = colBalance j.2.val j.1.val then
        blockEntry (rowJet r.2.val) j.1.val else 0 := by
  rw [origin, localConstraintMatrix_apply, SourceColumn.polynomial_eq_sourceMonomial]
  exact origin_coefficient j.2.val j.1.val r.2.val
abbrev BlockIndex (s : Source) (cut : ℕ) := (q : Fin cut) × Fin (s.m+s.J-q.val)
private def balance {s cut} (i : BlockIndex s cut) : ℤ := (i.2.val : ℤ) - s.J
private structure InPrefix (s : Source) (cut q : ℕ) (g : ℤ) : Prop where
  grade : q < cut
  lower : -(s.J : ℤ) ≤ g
  upper : g + q < (s.m : ℤ)
private def blockIndex {s cut q g} (h : InPrefix s cut q g) : BlockIndex s cut :=
  ⟨⟨q, h.grade⟩, ⟨(g + s.J).toNat, by
    change (g + s.J).toNat < s.m+s.J-q
    have := h.lower
    have := h.upper
    omega⟩⟩
private theorem balance_blockIndex {s cut q g} (h : InPrefix s cut q g) :
    balance (blockIndex h) = g := by
  have := h.lower
  simp only [balance, blockIndex]
  omega
private theorem blockIndex_ext {s cut} {i j : BlockIndex s cut}
    (hq : i.1.val = j.1.val) (hg : balance i = balance j) : i = j := by
  rcases i with ⟨qi, ui⟩
  rcases j with ⟨qj, uj⟩
  have hgrade : qi = qj := Fin.ext hq
  subst qj
  have hoffset : ui = uj := Fin.ext (by simp only [balance] at hg; omega)
  subst uj
  rfl
private theorem row_mem {s : Source} (r : OriginRow s) :
    rowJet r.2.val ∈ blockRows s.m (rowJet r.2.val).q (rowBalance r.2.val) := by
  let j := rowJet r.2.val
  have hcontact := r.2.property
  rw [localContactOrder_eq] at hcontact
  change r.2.val (localT 2) + 2*j.a < s.m at hcontact
  have hweight : rowBalance r.2.val + (j.v : ℤ) + 3*(j.a : ℤ) =
      (r.2.val (localT 2) : ℤ) + 2*(j.a : ℤ) := by
    change (r.2.val (localT 2) : ℤ) - j.a - j.v + j.v + 3*j.a = _
    omega
  refine Finset.mem_filter.mpr ⟨?_, by rw [hweight]; omega⟩
  change j ∈ (Finset.range (j.q+1)).sigma
    (fun c => (Finset.range (j.q-c+1)).sigma fun b => {j.q-(b+c)})
  generalize j = i
  rcases i with ⟨c,b,a⟩
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_singleton, Jet.q, Jet.a, Jet.b, Jet.c]
  omega
private theorem origin_support {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (r : OriginRow s) (j : OriginCol A s) (hn : origin A s r j ≠ 0) :
    (rowJet r.2.val).q = j.1.val.q ∧ rowBalance r.2.val = colBalance j.2.val j.1.val ∧
      InPrefix s cut j.1.val.q (colBalance j.2.val j.1.val) := by
  let i := rowJet r.2.val
  let c := j.1.val
  have hg : rowBalance r.2.val = colBalance j.2.val c := by
    by_contra hn'
    exact hn (by rw [origin_entry, ite_eq_right hn'])
  have hbc : c.b ≤ i.b ∧ c.c ≤ i.c ∧ i.a + (i.b-c.b) + (i.c-c.c) = c.a := by
    by_contra hn'
    exact hn (by rw [origin_entry, ite_eq_left hg, blockEntry, ite_eq_right hn'])
  obtain ⟨hb, hc, ha⟩ := hbc
  have hq : i.q = c.q := by simp only [Jet.q]; omega
  have hcontact := r.2.property
  rw [localContactOrder_eq] at hcontact
  change r.2.val (localT 2) + 2*i.a < s.m at hcontact
  have heq : (r.2.val (localT 2) : ℤ) - i.a - (i.b + 2*i.c : ℕ) =
      (j.2.val : ℤ) - (c.b + 2*c.c : ℕ) := hg
  have hsmall : c.a < s.m := by omega
  have hgrade : c.q < cut := by
    by_contra! hbig
    exact (Nat.not_le_of_gt hsmall) (htail c j.1.property hbig)
  have hv := (hs.support c j.1.property).2.1
  refine ⟨hq, hg, hgrade, ?_, ?_⟩
  · change -(s.J : ℤ) ≤ (j.2.val : ℤ) - c.v
    change c.v ≤ s.J at hv
    omega
  · change (j.2.val : ℤ) - (c.b+2*c.c : ℕ) + (c.a+c.b+c.c : ℕ) < (s.m : ℤ)
    omega
private def activeRows (A : ℕ) (s : Source) : Finset (OriginRow s) :=
  localConstraintSupportedRows s.m (fun _ : Unit => (0 : ZMod p)) (fun _ => 0) (column A s)
private def activeCols (A : ℕ) (s : Source) : Finset (OriginCol A s) := by
  classical
  exact Finset.univ.filter fun j => ∃ r, origin A s r j ≠ 0
private theorem active_row_inPrefix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (r : activeRows A s) :
    InPrefix s cut (rowJet r.val.2.val).q (rowBalance r.val.2.val) := by
  obtain ⟨j, hj⟩ := (mem_localConstraintSupportedRows_iff _ _ _ _ _).mp r.property
  obtain ⟨hq, hg, h⟩ := origin_support hs htail r.val j hj
  rwa [hq, hg]
private theorem active_col_inPrefix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (j : activeCols A s) :
    InPrefix s cut j.val.1.val.q (colBalance j.val.2.val j.val.1.val) := by
  classical
  obtain ⟨r, hr⟩ := (Finset.mem_filter.mp j.property).2
  exact (origin_support hs htail r j.val hr).2.2
private abbrev BlockRow {s cut} (i : BlockIndex s cut) : Type := ↥(blockRows s.m i.1.val (balance i))
private abbrev BlockCol {s cut} (i : BlockIndex s cut) : Type := ↥(blockCols s i.1.val (balance i))
private def rowRep {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) (r : activeRows A s) :
    Sigma (BlockRow (s := s) (cut := cut)) :=
  let h := active_row_inPrefix hs htail r
  ⟨blockIndex h, ⟨rowJet r.val.2.val, by
    change rowJet r.val.2.val ∈
      blockRows s.m (rowJet r.val.2.val).q (balance (blockIndex h))
    rw [balance_blockIndex]
    exact row_mem r.val⟩⟩
private def colRep {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) (j : activeCols A s) :
    Sigma (BlockCol (s := s) (cut := cut)) :=
  let h := active_col_inPrefix hs htail j
  ⟨blockIndex h, ⟨j.val.1.val, by
    apply Finset.mem_filter.mpr
    refine ⟨j.val.1.property, rfl, ?_⟩
    rw [balance_blockIndex]
    simp [colBalance]⟩⟩
private def packet (s : Source) (cut : ℕ) :
    Matrix (Sigma (BlockRow (s := s) (cut := cut))) (Sigma (BlockCol (s := s) (cut := cut)))
      (ZMod p) :=
  Matrix.blockDiagonal' fun i => blockMatrix s i.1.val (balance i)
private theorem packet_entry {s cut} (r : Sigma (BlockRow (s := s) (cut := cut)))
    (c : Sigma (BlockCol (s := s) (cut := cut))) (h : r.1 = c.1) :
    packet s cut r c = blockEntry r.2.val c.2.val := by
  rcases r with ⟨i,r⟩
  rcases c with ⟨j,c⟩
  change i = j at h
  subst j
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _
private theorem origin_submatrix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) :
    (origin A s).submatrix (Subtype.val : activeRows A s → _) (Subtype.val : activeCols A s → _) =
      (packet s cut).submatrix (rowRep hs htail) (colRep hs htail) := by
  ext r c
  let i := rowRep hs htail r
  let j := colRep hs htail c
  change origin A s r.val c.val = packet s cut i j
  have hr : balance i.1 = rowBalance r.val.2.val :=
    balance_blockIndex (active_row_inPrefix hs htail r)
  have hc : balance j.1 = colBalance c.val.2.val c.val.1.val :=
    balance_blockIndex (active_col_inPrefix hs htail c)
  by_cases hij : i.1 = j.1
  · rw [packet_entry i j hij, origin_entry, ite_eq_left (hr.symm.trans ((congrArg balance hij).trans hc))]
    rfl
  · have hz : origin A s r.val c.val = 0 := by
      by_contra hn
      obtain ⟨hq, hg, _⟩ := origin_support hs htail r.val c.val hn
      exact hij (blockIndex_ext hq (hr.trans (hg.trans hc.symm)))
    rw [hz]
    exact (Matrix.blockDiagonal'_apply_ne _ _ _ hij).symm
private theorem origin_rank_eq_supported (A : ℕ) (s : Source) :
    (origin A s).rank =
      ((origin A s).submatrix (Subtype.val : activeRows A s → _) id).rank := by
  symm
  apply Matrix.rank_submatrix_eq_of_ne_zero_mem_range
  exact localConstraintMatrix_ne_zero_mem_range _ _ _ _
private theorem supported_rank_le (A : ℕ) (s : Source) :
    ((origin A s).submatrix (Subtype.val : activeRows A s → _) id).rank ≤
      ((origin A s).submatrix (Subtype.val : activeRows A s → _)
        (Subtype.val : activeCols A s → _)).rank := by
  classical
  apply Sol1.C52.rank_le_col_representatives
  intro j
  by_cases hj : j ∈ activeCols A s
  · exact Or.inr ⟨⟨j, hj⟩, rfl⟩
  · left
    funext r
    change origin A s r.val j = 0
    by_contra hn
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.val, hn⟩)
private theorem packet_rank_le (s : Source) (cut : ℕ) : (packet s cut).rank ≤ prefixRank s cut := by
  calc
    (packet s cut).rank ≤ ∑ i : BlockIndex s cut, (blockMatrix s i.1.val (balance i)).rank :=
      rank_blockDiagonal_le (fun i : BlockIndex s cut => blockMatrix s i.1.val (balance i))
    _ = prefixRank s cut := by
      rw [Fintype.sum_sigma]
      simp only [prefixRank, balance, Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [dite_eq_left (Finset.mem_range.mp hq)]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [dite_eq_left (Finset.mem_range.mp hu)]
      rfl
theorem proof : CJ0.c1 := by
  intro A s cut hs _ _ htail
  change (origin A s).rank ≤ prefixRank s cut
  rw [origin_rank_eq_supported]
  apply (supported_rank_le A s).trans
  rw [origin_submatrix hs htail]
  exact (Matrix.rank_submatrix_le _ _ _).trans (packet_rank_le s cut)
end
end CJ0_1
end
section
namespace CJ0_2
noncomputable section
open CJ0 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
private theorem lower_mem {s : Source} (hs : ShapeOK s) {c b a : ℕ}
    (h : (⟨c, b, a⟩ : Jet) ∈ s.E) {a' : ℕ} (ha : a' ≤ a) :
    (⟨c, b, a'⟩ : Jet) ∈ s.E := by
  induction a with
  | zero =>
    rw [Nat.eq_zero_of_le_zero ha]
    exact h
  | succ a ih =>
    rcases Nat.eq_or_lt_of_le ha with hEq | hlt
    · rw [hEq]
      exact h
    · exact ih (hs.lower _ h (Nat.succ_pos a)) (Nat.le_of_lt_succ hlt)
private def sourceSpan (F : Type*) [Field F] (A : ℕ) (s : Source) :
    Submodule F (DifferentialPolynomial F 2) :=
  Submodule.span F (Set.range fun i : ColumnIndex A s => (column A s i).polynomial)
private theorem column_mem_sourceSpan {F : Type*} [Field F] {A : ℕ} {s : Source}
    (i : ColumnIndex A s) : (column A s i).polynomial ∈ sourceSpan F A s :=
  Submodule.subset_span (Set.mem_range_self i)
private theorem translated_column_mem {F : Type*} [Field F] {A : ℕ} {s : Source}
    (hs : ShapeOK s) (center received : F) (i : ColumnIndex A s) :
    globalPointTranslation center received (column A s i).polynomial ∈ sourceSpan F A s := by
  classical
  let col := column A s i
  change globalPointTranslation center received col.polynomial ∈ sourceSpan F A s
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  simp only [sourceMonomial, map_mul, map_pow, map_prod, globalPointTranslation_X,
    globalPointTranslation_Y_zero, globalPointTranslation_Y_succ]
  rw [add_comm (MvPolynomial.C center), add_comm (MvPolynomial.C received), add_pow, add_pow,
    Finset.sum_mul, Finset.sum_mul]
  apply Submodule.sum_mem
  intro x hx
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro a ha
  have hx' : x ≤ i.2.val := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
  have ha' : a ≤ i.1.val.a := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  let j : Jet := ⟨i.1.val.c, i.1.val.b, a⟩
  have hj : j ∈ s.E := by
    rcases i with ⟨⟨⟨c, b, a₀⟩, hi⟩, i⟩
    exact lower_mem hs hi ha'
  have hq : j.q ≤ i.1.val.q :=
    Nat.add_le_add_right (Nat.add_le_add_right ha' _) _
  have hwidth : width A s i.1.val ≤ width A s j :=
    Nat.add_le_add_right (Nat.sub_le_sub_left (Nat.mul_le_mul_left N hq) _) _
  let l : ColumnIndex A s := ⟨⟨j, hj⟩, ⟨x, (hx'.trans_lt i.2.isLt).trans_le hwidth⟩⟩
  let coeff : F := center ^ (col.x - x) * (col.x.choose x : F) *
    received ^ (col.y₀ - a) * (col.y₀.choose a : F)
  have hterm :
      (MvPolynomial.X none ^ x * MvPolynomial.C center ^ (col.x - x) * (col.x.choose x : DifferentialPolynomial F 2) *
        (MvPolynomial.X (some 0) ^ a * MvPolynomial.C received ^ (col.y₀ - a) *
          (col.y₀.choose a : DifferentialPolynomial F 2))) *
        (∏ j, MvPolynomial.X (some j.succ) ^ col.higher j) =
      coeff • (column A s l).polynomial := by
    rw [smul_eq_C_mul, SourceColumn.polynomial_eq_sourceMonomial]
    change _ = MvPolynomial.C coeff * sourceMonomial x a col.higher
    simp only [coeff, sourceMonomial, map_mul, map_pow, map_natCast]
    ac_rfl
  rw [hterm]
  exact (sourceSpan F A s).smul_mem coeff (column_mem_sourceSpan l)
private def pointMatrix {F : Type*} [Field F] (A : ℕ) (s : Source)
    (center received : F) : Matrix (LowContactIndex 2 s.m) (ColumnIndex A s) F :=
  fun row i => localConstraintCoordinatesAt s.m center received (column A s i).polynomial row
private theorem point_rank_le_origin {F : Type*} [Field F] {A : ℕ} {s : Source}
    (hs : ShapeOK s) (center received : F) :
    (pointMatrix A s center received).rank ≤ (pointMatrix A s (0 : F) 0).rank := by
  classical
  let L := localConstraintCoordinatesAt (R := F) (d := 2) s.m 0 0
  have hmap : (sourceSpan F A s).map L =
      Submodule.span F (Set.range (pointMatrix A s (0 : F) 0).col) := by
    rw [sourceSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan : Submodule.span F (Set.range (pointMatrix A s center received).col) ≤
      Submodule.span F (Set.range (pointMatrix A s (0 : F) 0).col) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← hmap]
    exact ⟨globalPointTranslation center received (column A s i).polynomial,
      translated_column_mem hs center received i,
      (Sol1.C42.coordinates_translation s.m center received (column A s i).polynomial).symm⟩
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have := FiniteDimensional.span_of_finite (K := F)
    (Set.finite_range (pointMatrix A s (0 : F) 0).col)
  exact Submodule.finrank_mono hspan
private theorem constraint_matrix_map {R S ι κ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (m : ℕ) (centers received : ι → R) (cols : κ → SourceColumn 2) :
    (localConstraintMatrix m centers received cols).map φ =
      localConstraintMatrix m (fun i => φ (centers i)) (fun i => φ (received i)) cols := by
  ext row j
  simp only [Matrix.map_apply, localConstraintMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]
set_option maxHeartbeats 800000 in
private theorem native_origin_rank (A : ℕ) (s : Source) :
    (pointMatrix A s (0 : K) 0).rank ≤ originRank A s := by
  let φ : KoalaBear.Field →+* K := algebraMap KoalaBear.Field K
  let P := localConstraintMatrix s.m
    (fun _ : Unit => (0 : KoalaBear.Field)) (fun _ => 0) (column A s)
  let row : LowContactIndex 2 s.m → Unit × LowContactIndex 2 s.m := fun r => ((), r)
  have hmap : P.map φ =
      localConstraintMatrix s.m (fun _ : Unit => (0 : K)) (fun _ => 0) (column A s) := by
    simpa only [map_zero] using
      constraint_matrix_map φ s.m (fun _ : Unit => (0 : KoalaBear.Field)) (fun _ => 0) (column A s)
  calc
    _ = ((P.map φ).submatrix row (id : ColumnIndex A s → ColumnIndex A s)).rank := by
      rw [hmap]
      rfl
    _ ≤ (P.map φ).rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ P.rank := Matrix.rank_map_le φ P
    _ = _ := rfl
private theorem sum_const_card {ι : Type*} [Fintype ι] (r : ℕ) :
    (∑ _ : ι, r) = Fintype.card ι * r := by
  simp
theorem proof : CJ0.c2 := by
  intro A s hs _ w
  let M := localConstraintMatrix s.m (fun i => node i) w (column A s)
  change M.rank ≤ n * originRank A s
  apply (Matrix.rank_prod_rows_le_sum M).trans
  calc
    _ ≤ ∑ _ : Node, originRank A s := by
      apply Finset.sum_le_sum
      intro i _
      change (pointMatrix A s (node i) (w i)).rank ≤ originRank A s
      exact (point_rank_le_origin hs (node i) (w i)).trans (native_origin_rank A s)
    _ = _ := by rw [sum_const_card, ProximityPrize.Benchmark.IRSProfile.card_index]
end
end CJ0_2
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential
open scoped BigOperators Polynomial
abbrev Equation := DifferentialPolynomial K 2
def centerMap : (Polynomial K) →+* Geo :=
  (algebraMap FX Geo).comp (algebraMap (Polynomial K) FX)
def lifted (G : Equation) : DifferentialPolynomial Geo 2 :=
  MvPolynomial.map embed G
def initial (G : Equation) : InitialRing 2 :=
  initialJetEquation center (lifted G)
def initialSep (G : Equation) : InitialRing 2 :=
  initialJetSeparant center (lifted G)
def nativeJet (f : (Polynomial K)) : Fin 3 → Geo :=
  polynomialJet center (f.map embed)
structure FactorFamily (Q : Equation) where
  count : ℕ
  source : Fin count → Equation
  equation : Fin count → InitialRing 2
  source_irreducible : ∀ i, Irreducible (source i)
  source_dvd : ∀ i, source i ∣ Q
  irreducible : ∀ i, Irreducible (equation i)
  component : ∀ i, equation i ∣ initial (source i)
  regular : ∀ i, ¬ equation i ∣ initialSep (source i)
  product_dvd : (∏ i, equation i) ∣ initial Q
  covers : ∀ f : (Polynomial K), RegularRoot Q f →
    ∃ i, differentialSpecialization (source i) f = 0 ∧
      MvPolynomial.eval (nativeJet f) (equation i) = 0 ∧
      MvPolynomial.eval (nativeJet f) (initialSep (source i)) ≠ 0
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 Polynomial PolynomialDifferential
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
theorem centerMap_injective : Function.Injective centerMap :=
  (algebraMap FX Geo).injective.comp (IsFractionRing.injective (Polynomial K) FX)
theorem initial_eq_map (G : Equation) :
    initial G = MvPolynomial.map centerMap (MvPolynomial.optionEquivRight K (Fin 3) G) := by
  let a : Equation →+* InitialRing 2 :=
    (MvPolynomial.aeval (fun j : Option (Fin 3) => j.elim (MvPolynomial.C center)
      MvPolynomial.X)).toRingHom.comp (MvPolynomial.map embed)
  let b : Equation →+* InitialRing 2 := (MvPolynomial.map centerMap).comp
    (MvPolynomial.optionEquivRight K (Fin 3)).toAlgHom.toRingHom
  have he : a = b := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change a (MvPolynomial.C c) = b (MvPolynomial.C c)
      simp [a, b]
      rfl
    · intro j
      cases j with
      | none =>
        simp [a, b]
        rfl
      | some j => simp [a, b]
  exact DFunLike.congr_fun he G
theorem initial_injective : Function.Injective initial := by
  intro P Q h
  rw [initial_eq_map, initial_eq_map] at h
  exact (MvPolynomial.optionEquivRight K (Fin 3)).injective
    (MvPolynomial.map_injective _ centerMap_injective h)
theorem initial_ne_zero {G : Equation} (hG : G ≠ 0) : initial G ≠ 0 := by
  intro h
  apply hG
  exact initial_injective (h.trans (by simp [initial, lifted, initialJetEquation]))
theorem eval_at_center (P : (Polynomial K)) : (P.map embed).eval center = centerMap P := by
  rw [eval_map]
  change eval₂RingHom embed center P = centerMap P
  have h : eval₂RingHom embed center = centerMap := by
    apply Polynomial.ringHom_ext
    · intro a
      change eval₂ embed center (Polynomial.C a) = centerMap (Polynomial.C a)
      rw [eval₂_C]
      rfl
    · change eval₂ embed center Polynomial.X = centerMap Polynomial.X
      rw [eval₂_X]
      rfl
  rw [h]
theorem initial_eval (G : Equation) (f : (Polynomial K)) :
    MvPolynomial.eval (nativeJet f) (initial G) =
      centerMap (differentialSpecialization G f) := by
  rw [initial, ← MvPolynomial.aeval_eq_eval, aeval_initialJetEquation, nativeJet,
    ← eval_differentialSpecialization, lifted, ← map_differentialSpecialization, eval_at_center]
theorem initialSep_eval (G : Equation) (f : (Polynomial K)) :
    MvPolynomial.eval (nativeJet f) (initialSep G) =
      centerMap (differentialSpecialization (separant G (Fin.last 2)) f) := by
  have he : initialSep G = initial (separant G (Fin.last 2)) := by
    rw [initialSep, initialJetSeparant, initial, lifted, lifted, map_separant]
    rfl
  rw [he, initial_eval]
theorem readJet_eq {L : ℕ} (P : (Polynomial Geo)) (hp : P.degree < L) (j : ℕ) :
    (∑ i : Fin L, (i.val.choose j : Geo) * center^(i.val-j) * P.coeff i.val) =
      (hasseDeriv j P).eval center := by
  rw [hasseDeriv_apply, ← Polynomial.sum_fin
    (fun i c => monomial (i - j) ((i.choose j : Geo) * c)) (by simp) hp, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_monomial]
  ring
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
private theorem weighted_map_eq {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (hφ : Function.Injective φ) (w : σ → ℕ) (P : MvPolynomial σ R) :
    (MvPolynomial.map φ P).weightedTotalDegree w = P.weightedTotalDegree w := by
  unfold weightedTotalDegree
  rw [support_map_of_injective P hφ]
theorem initial_weight (w : Fin 3 → ℕ) (G : Equation) :
    (initial G).weightedTotalDegree w = G.weightedTotalDegree (fun j => j.elim 0 w) := by
  rw [initial_eq_map, weighted_map_eq _ centerMap_injective, weightedTotalDegree_optionEquivRight]
theorem lifted_weight (w : Option (Fin 3) → ℕ) (G : Equation) :
    (lifted G).weightedTotalDegree w = G.weightedTotalDegree w :=
  weighted_map_eq embed embed.injective w G
theorem lifted_total (G : Equation) : jetTotalDegree (lifted G) = jetTotalDegree G :=
  lifted_weight jetDegreeWeight G
theorem lifted_top (G : Equation) :
    jetDegree (lifted G) (Fin.last 2) = jetDegree G (Fin.last 2) := by
  simpa only [jetDegree, weightedTotalDegree_piSingle] using
    lifted_weight (Pi.single (some (Fin.last 2)) 1) G
theorem orderTwo_of_dvd {s : Source} {G Q : Equation} (hQ : OrderTwo s Q) (h : G ∣ Q) :
    OrderTwo s G := by
  refine ⟨ne_zero_of_dvd_ne_zero hQ.1 h,
    (weightedTotalDegree_le_of_dvd jetDegreeWeight h hQ.1).trans hQ.2.1,
    (weightedTotalDegree_le_of_dvd CJ0.indexWeight h hQ.1).trans hQ.2.2.1, ?_⟩
  have htop := weightedTotalDegree_le_of_dvd (Pi.single (some (Fin.last 2)) 1) h hQ.1
  rw [weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at htop
  exact htop.trans hQ.2.2.2
theorem totalWeight_eq : (fun j : Option (Fin 3) => j.elim 0 (1 : Fin 3 → ℕ)) =
    jetDegreeWeight := by
  funext j
  cases j <;> rfl
private theorem topWeight_eq : (fun j : Option (Fin 3) =>
    j.elim 0 (Pi.single (Fin.last 2) 1)) = Pi.single (some (Fin.last 2)) (1 : ℕ) := by
  funext j
  cases j <;> simp [Pi.single_apply]
theorem factor_weights {s : Source} {Q : Equation} (hQ : OrderTwo s Q) (F : FactorFamily Q) :
    (∑ i, (F.equation i).totalDegree) ≤ s.B ∧
    (∑ i, (F.equation i).weightedTotalDegree Fin.val) ≤ s.J ∧
    (∑ i, (F.equation i).degreeOf (Fin.last 2)) ≤ s.C := by
  have hn := initial_ne_zero hQ.1
  have h (w : Fin 3 → ℕ) :
      (∑ i, (F.equation i).weightedTotalDegree w) ≤ (initial Q).weightedTotalDegree w :=
    sum_weightedTotalDegree_le_of_prod_dvd w Finset.univ F.equation hn F.product_dvd
  have ht := h (1 : Fin 3 → ℕ)
  have hi := h Fin.val
  have hc := h (Pi.single (Fin.last 2) 1)
  rw [initial_weight, totalWeight_eq] at ht
  rw [initial_weight] at hi
  rw [initial_weight, topWeight_eq, weightedTotalDegree_piSingle] at hc
  simp only [weightedTotalDegree_one] at ht
  simp only [weightedTotalDegree_piSingle] at hc
  exact ⟨ht.trans hQ.2.1, hi.trans hQ.2.2.1, hc.trans hQ.2.2.2⟩
theorem factor_count {Q : Equation} (F : FactorFamily Q) :
    F.count ≤ ∑ i, (F.equation i).totalDegree := by
  classical
  have h (i : Fin F.count) : 1 ≤ (F.equation i).totalDegree := by
    by_contra! hh
    have hdeg : (F.equation i).totalDegree = 0 := by omega
    have he := totalDegree_eq_zero_iff_eq_C.mp hdeg
    have hz : (F.equation i).coeff 0 ≠ 0 := fun hz =>
      (F.irreducible i).ne_zero (he.trans (by rw [hz, map_zero]))
    exact (F.irreducible i).not_isUnit (he.symm ▸ (isUnit_iff_ne_zero.mpr hz).map MvPolynomial.C)
  calc
    F.count = ∑ _ : Fin F.count, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => h i
theorem degreeOf_top_of_index {P : InitialRing 2} {d : ℕ}
    (hP : P.weightedTotalDegree Fin.val ≤ d) : P.degreeOf (Fin.last 2) ≤ d / 2 := by
  classical
  apply degreeOf_le_iff.mpr
  intro m hm
  have hweight : 2 * m (Fin.last 2) ≤ Finsupp.weight Fin.val m := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    have hsum : m (Fin.last 2) • (Fin.last 2).val ≤ ∑ i, m i • Fin.val i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (m i • Fin.val i))
        (Finset.mem_univ (Fin.last 2))
    simpa only [Fin.val_last, smul_eq_mul, Nat.mul_comm 2] using hsum
  have h := hweight.trans ((le_weightedTotalDegree Fin.val hm).trans hP)
  omega
theorem indexWeight_eq : Astra7.jetWeight 0 1 3 = CJ0.indexWeight := by
  funext i
  cases i <;> simp [Astra7.jetWeight, CJ0.indexWeight]
theorem coeffWeight_eq : Astra7.coeffWeight 0 1 (2 + 1) = Fin.val := by
  funext i
  simp [Astra7.coeffWeight]
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential
open scoped BigOperators
set_option maxRecDepth 4000
def c1 : Prop :=
  ∀ Q : Equation, Q ≠ 0 → Nonempty (FactorFamily Q)
end
end CJ0_3
end
section
namespace CJ0_3_1
noncomputable section
open CJ0 CJ0_3 Polynomial PolynomialDifferential UniqueFactorizationMonoid
open scoped BigOperators
local instance : StrongNormalizationMonoid Equation :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : StrongNormalizationMonoid (InitialRing 2) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
private def initialHom : Equation →+* InitialRing 2 :=
  (MvPolynomial.aeval (fun j : Option (Fin 3) =>
    j.elim (MvPolynomial.C center) MvPolynomial.X)).toRingHom.comp (MvPolynomial.map embed)
private theorem root_of_associated {G G' : Equation} {f : (Polynomial K)}
    (ha : Associated G G') (hG : differentialSpecialization G f = 0)
    (hS : differentialSpecialization (separant G (Fin.last 2)) f ≠ 0) :
    differentialSpecialization G' f = 0 ∧
      differentialSpecialization (separant G' (Fin.last 2)) f ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  let ev := differentialSpecializationHom f (d := 2)
  have hu : ev (u : Equation) ≠ 0 := (u.isUnit.map ev).ne_zero
  change ev G = 0 at hG
  change ev (separant G (Fin.last 2)) ≠ 0 at hS
  change ev (G * u) = 0 ∧ ev (separant (G * u) (Fin.last 2)) ≠ 0
  refine ⟨by rw [map_mul, hG, zero_mul], ?_⟩
  rw [separant, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hG, zero_mul, add_zero]
  exact mul_ne_zero hS hu
private theorem root_in_factor {P : InitialRing 2} (hP : P ≠ 0) (u : Fin 3 → Geo)
    (h : MvPolynomial.eval u P = 0) :
    ∃ g ∈ normalizedFactors P, MvPolynomial.eval u g = 0 := by
  have hd := map_dvd (MvPolynomial.eval u) (prod_normalizedFactors hP).symm.dvd
  rw [h, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  exact hd
theorem proof : CJ0_3.c1 := by
  classical
  intro Q hQ
  let native := (normalizedFactors Q).toFinset
  let geometric (G : Equation) :=
    (normalizedFactors (initial G)).toFinset.filter fun g => ¬ g ∣ initialSep G
  let pairs := native.sigma geometric
  let n := pairs.card
  let e : Fin n ≃ ↥pairs := (Fintype.equivFinOfCardEq (Fintype.card_coe pairs)).symm
  let entry (i : Fin n) := (e i).val
  have hmember (i : Fin n) : (entry i).1 ∈ native ∧ (entry i).2 ∈ geometric (entry i).1 :=
    Finset.mem_sigma.mp (e i).property
  have hnative (i : Fin n) : (entry i).1 ∈ normalizedFactors Q :=
    Multiset.mem_toFinset.mp (hmember i).1
  have hgeometric (i : Fin n) :
      (entry i).2 ∈ normalizedFactors (initial (entry i).1) ∧
        ¬ (entry i).2 ∣ initialSep (entry i).1 := by
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp (hmember i).2
    exact ⟨Multiset.mem_toFinset.mp hm, hd⟩
  have hprod : (∏ a ∈ pairs, a.2) ∣ initial Q := by
    have hnativeProd : (∏ G ∈ native, G) ∣ Q :=
      (Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hQ).dvd
    have hm := map_dvd initialHom hnativeProd
    rw [map_prod] at hm
    change (∏ a ∈ native.sigma geometric, a.2) ∣ initialHom Q
    rw [Finset.prod_sigma]
    refine (Finset.prod_dvd_prod_of_dvd _ _ (fun G hG => ?_)).trans hm
    have hGne := initial_ne_zero (ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hG))
    change (∏ g ∈ geometric G, g) ∣ initial G
    exact (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      ((Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hGne).dvd)
  refine ⟨⟨n, fun i => (entry i).1, fun i => (entry i).2,
    fun i => irreducible_of_normalized_factor _ (hnative i),
    fun i => dvd_of_mem_normalizedFactors (hnative i),
    fun i => irreducible_of_normalized_factor _ (hgeometric i).1,
    fun i => dvd_of_mem_normalizedFactors (hgeometric i).1,
    fun i => (hgeometric i).2, ?_, ?_⟩⟩
  · have heq : (∏ i : Fin n, (entry i).2) = ∏ a ∈ pairs, a.2 := by
      calc
        _ = ∏ a : ↥pairs, a.val.2 := e.prod_comp (fun a : ↥pairs => a.val.2)
        _ = _ := Finset.prod_coe_sort pairs (fun a => a.2)
    rw [heq]
    exact hprod
  · intro f hreg
    obtain ⟨G, hGir, hGdvd, hGroot, hGsep⟩ := hreg
    obtain ⟨G', hGnative, hGassoc⟩ := exists_mem_normalizedFactors_of_dvd hQ hGir hGdvd
    obtain ⟨hroot, hsep⟩ := root_of_associated hGassoc hGroot hGsep
    have hinitial : MvPolynomial.eval (nativeJet f) (initial G') = 0 := by
      rw [initial_eval, hroot, map_zero]
    have hinitialSep : MvPolynomial.eval (nativeJet f) (initialSep G') ≠ 0 := by
      rw [initialSep_eval]
      exact map_ne_zero_iff centerMap centerMap_injective |>.mpr hsep
    have hne := initial_ne_zero (ne_zero_of_mem_normalizedFactors hGnative)
    obtain ⟨g, hgmem, hgroot⟩ := root_in_factor hne (nativeJet f) hinitial
    have hgreg : ¬ g ∣ initialSep G' := by
      intro hdvd
      have hm := map_dvd (MvPolynomial.eval (nativeJet f)) hdvd
      rw [hgroot, zero_dvd_iff] at hm
      exact hinitialSep hm
    have hpair : (⟨G', g⟩ : Sigma fun _ : Equation => InitialRing 2) ∈ pairs :=
      Finset.mem_sigma.mpr ⟨Multiset.mem_toFinset.mpr hGnative,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hgmem, hgreg⟩⟩
    let a : ↥pairs := ⟨⟨G', g⟩, hpair⟩
    refine ⟨e.symm a, ?_⟩
    change differentialSpecialization (e (e.symm a)).val.1 f = 0 ∧
      MvPolynomial.eval (nativeJet f) (e (e.symm a)).val.2 = 0 ∧
      MvPolynomial.eval (nativeJet f) (initialSep (e (e.symm a)).val.1) ≠ 0
    rw [e.apply_symm_apply]
    exact ⟨hroot, hgroot, hinitialSep⟩
end
end CJ0_3_1
end
section
namespace CJ0_3_2
noncomputable section
open CJ0 PolynomialDifferential MvPolynomial
open scoped BigOperators
set_option maxRecDepth 4000
private def coeffWeight {L : ℕ} (i : Fin L) : ℕ := i.val - 1
private def jetWeight (L : ℕ) : Option (Fin L) → ℕ :=
  fun i => i.elim 0 coeffWeight
private theorem jetWeight_initial :
    jetWeight 3 = Pi.single (some (Fin.last 2)) 1 := by
  funext i
  cases i with
  | none => simp [jetWeight]
  | some j => fin_cases j <;> decide
section Field
variable {F : Type*} [Field F]
private theorem universalJet_offset (L j : ℕ) :
    SupportWeightOffset (Finsupp.weight (jetWeight L))
      (Finsupp.weight (Astra7.displacementWeight 1 L)) (j - 1)
      (universalTaylorJet (F := F) L j) := by
  classical
  apply SupportWeightOffset.sum
  intro i hi
  apply SupportWeightOffset.monomial
  have hj := (Finset.mem_filter.mp hi).2
  simp only [map_add, Finsupp.weight_single, smul_eq_mul, jetWeight,
    Astra7.displacementWeight, coeffWeight, Option.elim_some, Option.elim_none,
    mul_zero, zero_add, one_mul, add_zero, mul_one]
  omega
private theorem residual_coeff_weight (L h : ℕ) (x : F) (Q : DifferentialPolynomial F 2)
    {c : ℕ} (hQ : Q.degreeOf (some (Fin.last 2)) ≤ c)
    {m : Fin L →₀ ℕ}
    (hm : m ∈ ((optionEquivLeft F (Fin L) (universalTaylorResidual L x Q)).coeff h).support) :
    Finsupp.weight coeffWeight m ≤ h + c := by
  have hres : SupportWeightOffset (Finsupp.weight (jetWeight L))
      (Finsupp.weight (Astra7.displacementWeight 1 L))
      (Q.weightedTotalDegree (jetWeight 3)) (universalTaylorResidual L x Q) := by
    apply supportWeightOffset_aeval
    intro i
    cases i with
    | none =>
      apply SupportWeightOffset.add
      · exact SupportWeightOffset.C x
      · apply SupportWeightOffset.monomial
        simp [jetWeight, Astra7.displacementWeight, Finsupp.weight_single]
    | some j => exact universalJet_offset L j.val
  have hw := hres (m.optionElim h) ((mem_support_coeff_optionEquivLeft F).mp hm)
  change Finsupp.weight (fun i : Option (Fin L) => i.elim 0 coeffWeight) (m.optionElim h) ≤
    Finsupp.weight (fun i : Option (Fin L) => i.elim 1 (fun _ => 0)) (m.optionElim h) +
      Q.weightedTotalDegree (jetWeight 3) at hw
  rw [Finsupp.weight_elim_one_zero, Finsupp.optionElim_apply_none,
    Finsupp.weight_optionElim, zero_mul, zero_add, jetWeight_initial,
    weightedTotalDegree_piSingle] at hw
  exact hw.trans (Nat.add_le_add_left hQ h)
private theorem initial_coord_bound (l : ℕ) (hl : l < 3) :
    (MvPolynomial.X (⟨l, hl⟩ : Fin 3) : MvPolynomial (Fin 3) F).degreeOf (Fin.last 2) ≤ l - 1 := by
  rw [degreeOf_X]
  split
  · rename_i he
    have he' := congrArg Fin.val he
    change 2 = l at he'
    omega
  · exact Nat.zero_le _
private theorem rationalTaylor_top (x : F) (Q : DifferentialPolynomial F 2) {c : ℕ}
    (hc : 0 < c) (hQ : Q.degreeOf (some (Fin.last 2)) ≤ c) (l : ℕ) :
    (rationalTaylorNumerator x Q l).degreeOf (Fin.last 2) ≤
      (2 * (l - 2) - 1) * (c - 1) + (l - 1) := by
  have hsep := (degreeOf_initialJetSeparant_le x Q).trans (Nat.sub_le_sub_right hQ 1)
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    rw [rationalTaylorNumerator]
    split_ifs with hl
    · exact (initial_coord_bound (F := F) l hl).trans (Nat.le_add_left _ _)
    · let R := (optionEquivLeft F (Fin l) (universalTaylorResidual l x Q)).coeff (l - 2)
      have hden : ∀ m ∈ R.support,
          Finsupp.weight (fun i : Fin l => 2 * (i.val - 2) - 1) m ≤ 2 * (l - 2) - 2 :=
        fun m hm => denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r := 2) (K := l) (h := l - 2) (by omega) x Q m hm
      have hw : ∀ m ∈ R.support, Finsupp.weight coeffWeight m ≤ (l - 2) + c :=
        fun _ hm => residual_coeff_weight l (l - 2) x Q hQ hm
      have hd := degreeOf_clearedSubstitution (Fin.last 2) (initialJetSeparant x Q)
        (fun i : Fin l => rationalTaylorNumerator x Q i.val)
        (fun i => 2 * (i.val - 2) - 1) coeffWeight (2 * (l - 2) - 2) (c - 1)
        ((l - 2) + c) R hsep (fun i => ih i.val i.isLt) hden hw
      have hstep : 2 * (l - 2) - 1 = (2 * (l - 2) - 2) + 1 := by omega
      have hbudget : (l - 2) + c = (c - 1) + (l - 1) := by omega
      refine (degreeOf_mul_le _ _ _).trans ?_
      simp only [degreeOf_neg, degreeOf_C, zero_add]
      apply hd.trans
      rw [hstep, Nat.add_mul, one_mul, hbudget, Nat.add_assoc]
theorem commonTaylor_top (x : F) (Q : DifferentialPolynomial F 2) {c L τ : ℕ}
    (hc : 0 < c) (hQ : Q.degreeOf (some (Fin.last 2)) ≤ c) (hτ : TaylorExponentSufficient 2 L τ)
    (l : Fin L) :
    (commonTaylorNumerator x Q τ l.val).degreeOf (Fin.last 2) ≤ τ * (c - 1) + (l.val - 1) := by
  have hsep := (degreeOf_initialJetSeparant_le x Q).trans (Nat.sub_le_sub_right hQ 1)
  let d := 2 * (l.val - 2) - 1
  have he : τ - d + d = τ := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumerator
  apply (degreeOf_mul_le _ _ _).trans
  apply (Nat.add_le_add (rationalTaylor_top x Q hc hQ l.val)
    ((degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left (τ - d) hsep))).trans
  change d * (c - 1) + (l.val - 1) + (τ - d) * (c - 1) ≤ _
  rw [Nat.add_right_comm, ← Nat.add_mul, Nat.add_comm d (τ - d), he]
end Field
end
end CJ0_3_2
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial
def sourceIdeal {r : ℕ} (T : Chart r) : Ideal (InitialRing r) :=
  Ideal.span {T.equation}
def bandSpace (a d e : ℕ) : Submodule Geo (InitialRing 2) :=
  restrictSupport Geo
    {u : Fin 3 →₀ ℕ | u.degree ≤ a ∧ u.weight Fin.val ≤ d ∧ u (Fin.last 2) ≤ e}
theorem mem_bandSpace {a d e : ℕ} {P : InitialRing 2} :
    P ∈ bandSpace a d e ↔
      P.totalDegree ≤ a ∧ P.weightedTotalDegree Fin.val ≤ d ∧ P.degreeOf (Fin.last 2) ≤ e := by
  rw [bandSpace, mem_restrictSupport_iff, totalDegree, weightedTotalDegree,
    Finset.sup_le_iff, Finset.sup_le_iff, degreeOf_le_iff]
  exact ⟨fun h => ⟨fun _ hu => (h hu).1, fun _ hu => (h hu).2.1, fun _ hu => (h hu).2.2⟩,
    fun ⟨ha, hd, he⟩ _ hu => ⟨ha _ hu, hd _ hu, he _ hu⟩⟩
theorem bandSpace_mono {a d e a' d' e' : ℕ} (ha : a ≤ a') (hd : d ≤ d') (he : e ≤ e') :
    bandSpace a d e ≤ bandSpace a' d' e' := by
  intro P hP
  obtain ⟨h₁, h₂, h₃⟩ := mem_bandSpace.mp hP
  exact mem_bandSpace.mpr ⟨h₁.trans ha, h₂.trans hd, h₃.trans he⟩
instance (a d e : ℕ) : Module.Finite Geo (bandSpace a d e) :=
  Module.Finite.of_injective
    (Submodule.inclusion (show bandSpace a d e ≤ restrictTotalDegree (Fin 3) Geo a from
      fun _ hP => (mem_restrictTotalDegree _ _ _).mpr (mem_bandSpace.mp hP).1))
    (Submodule.inclusion_injective _)
theorem mul_mem_bandSpace {a d e b j c : ℕ} {P Q : InitialRing 2}
    (hP : P ∈ bandSpace a d e) (hQ : Q ∈ bandSpace b j c) :
    P * Q ∈ bandSpace (a + b) (d + j) (e + c) := by
  obtain ⟨hP₁, hP₂, hP₃⟩ := mem_bandSpace.mp hP
  obtain ⟨hQ₁, hQ₂, hQ₃⟩ := mem_bandSpace.mp hQ
  exact mem_bandSpace.mpr
    ⟨(totalDegree_mul _ _).trans (Nat.add_le_add hP₁ hQ₁),
     (weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hP₂ hQ₂),
     (degreeOf_mul_le _ _ _).trans (Nat.add_le_add hP₃ hQ₃)⟩
def quotientBand (T : Chart 2) (a d e : ℕ) :
    Submodule Geo (InitialRing 2 ⧸ sourceIdeal T) :=
  (bandSpace a d e).map (Ideal.Quotient.mkₐ Geo (sourceIdeal T)).toLinearMap
theorem quotientBand_mono (T : Chart 2) {a d e a' d' e' : ℕ}
    (ha : a ≤ a') (hd : d ≤ d') (he : e ≤ e') :
    quotientBand T a d e ≤ quotientBand T a' d' e' :=
  Submodule.map_mono (bandSpace_mono ha hd he)
instance (T : Chart 2) (a d e : ℕ) : Module.Finite Geo (quotientBand T a d e) := by
  unfold quotientBand
  infer_instance
def bandCount (a d e : ℚ) : ℚ :=
  (e + 1) * (d + 1 - e) * (2 * a + 2 - d) / 2
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial
section
variable {r : ℕ}
abbrev ChartOpen (T : Chart r) :=
  Localization.Away (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
def localize (T : Chart r) : InitialRing r →ₐ[Geo] ChartOpen T :=
  (IsScalarTower.toAlgHom Geo (InitialRing r ⧸ sourceIdeal T) (ChartOpen T)).comp
    (Ideal.Quotient.mkₐ Geo (sourceIdeal T))
def invDenom (T : Chart r) : ChartOpen T :=
  IsLocalization.Away.invSelf (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
theorem denom_mul_inv (T : Chart r) :
    localize T T.denominator * invDenom T = 1 :=
  IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
def chartMap (T : Chart r) : CoeffRing →ₐ[Geo] ChartOpen T :=
  aeval fun i => localize T (T.numerator i) * invDenom T
private theorem in_zeroLocus {T : Chart r} {y : Fin (r+1) → Geo}
    (hy : y ∈ T.locus) : y ∈ zeroLocus Geo (sourceIdeal T) := by
  apply mem_zeroLocus_iff_le_ker_aeval.mpr
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact RingHom.mem_ker.mpr hy.1
private def pointEval {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus) :
    (InitialRing r ⧸ sourceIdeal T) →ₐ[Geo] Geo :=
  Ideal.Quotient.liftₐ (sourceIdeal T) (aeval y) fun q hq => in_zeroLocus hy q hq
def openEval {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus) :
    ChartOpen T →ₐ[Geo] Geo :=
  IsLocalization.Away.liftAlgHom (f := pointEval hy)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
theorem openEval_localize {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus)
    (q : InitialRing r) : openEval hy (localize T q) = eval y q :=
  IsLocalization.Away.lift_eq (g := (pointEval hy).toRingHom)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
    (Ideal.Quotient.mk (sourceIdeal T) q)
theorem openEval_chartMap {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus)
    (q : CoeffRing) : openEval hy (chartMap T q) = eval (T.output y) q := by
  have hu := congrArg (openEval hy) (denom_mul_inv T)
  rw [map_mul, openEval_localize, map_one] at hu
  have hi : openEval hy (invDenom T) = (eval y T.denominator)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hy.2).mpr ((mul_comm _ _).trans hu)
  have h : (openEval hy).comp (chartMap T) = aeval (T.output y) := by
    apply MvPolynomial.algHom_ext
    intro i
    change openEval hy (chartMap T (MvPolynomial.X i)) = aeval (T.output y) (MvPolynomial.X i)
    rw [chartMap, aeval_X, map_mul, openEval_localize, hi, aeval_X, Chart.output, div_eq_mul_inv]
  exact DFunLike.congr_fun h q
private theorem eq_zero_of_openEval {T : Chart r} [(sourceIdeal T).IsPrime]
    (hD : T.denominator ∉ sourceIdeal T) {z : ChartOpen T}
    (hz : ∀ y (hy : y ∈ T.locus), openEval hy z = 0) : z = 0 := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  change z * localize T T.denominator ^ m = localize T q at ha
  have hq : q ∈ sourceIdeal T := by
    have hmul : T.denominator * q ∈ sourceIdeal T := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := Geo) (sourceIdeal T)]
      intro y hy
      change eval y (T.denominator * q) = 0
      by_cases hyD : eval y T.denominator = 0
      · rw [map_mul, hyD, zero_mul]
      · have hy' : y ∈ T.locus := ⟨hy _ (Ideal.subset_span (by simp)), hyD⟩
        have he := congrArg (openEval hy') ha
        rw [map_mul, map_pow, openEval_localize, openEval_localize, hz y hy', zero_mul] at he
        rw [map_mul, ← he, mul_zero]
    exact (‹(sourceIdeal T).IsPrime›.mem_or_mem hmul).resolve_left hD
  have hq0 : localize T q = 0 := by
    change algebraMap (InitialRing r ⧸ sourceIdeal T) (ChartOpen T)
      (Ideal.Quotient.mk (sourceIdeal T) q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  rw [hq0] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := ChartOpen T)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator)).pow m).mul_right_cancel
      (ha.trans (zero_mul _).symm)
theorem imageIdeal_eq_ker (T : Chart r) [(sourceIdeal T).IsPrime]
    (hD : T.denominator ∉ sourceIdeal T) : T.ideal = RingHom.ker (chartMap T).toRingHom := by
  ext q
  change q ∈ vanishingIdeal Geo T.imageSet ↔ chartMap T q = 0
  constructor
  · intro hq
    apply eq_zero_of_openEval hD
    intro y hy
    rw [openEval_chartMap hy]
    exact hq _ ⟨y, hy, rfl⟩
  · intro hq
    rintro _ ⟨y, hy, rfl⟩
    change eval (T.output y) q = 0
    rw [← openEval_chartMap hy, hq, map_zero]
private def jetForm (j : ℕ) : CoeffRing :=
  ∑ i : Fin k, C ((i.val.choose j : Geo) * center^(i.val-j)) * MvPolynomial.X i
private theorem eval_jetForm (y : Fin k → Geo) (j : ℕ) :
    eval y (jetForm j) = readJet y j := by
  simp [jetForm, readJet]
private theorem chartMap_recover (T : Chart r) (hT : ChartOK T) [(sourceIdeal T).IsPrime]
    (hD : T.denominator ∉ sourceIdeal T) :
    (chartMap T).comp (aeval fun j : Fin (r+1) => jetForm j.val) = localize T := by
  apply MvPolynomial.algHom_ext
  intro j
  change chartMap T (aeval (fun j : Fin (r+1) => jetForm j.val) (MvPolynomial.X j)) =
    localize T (MvPolynomial.X j)
  rw [aeval_X, ← sub_eq_zero]
  apply eq_zero_of_openEval hD
  intro y hy
  rw [map_sub, openEval_chartMap, openEval_localize, eval_jetForm, eval_X, hT.recover y hy j, sub_self]
theorem image_geometry (T : Chart r) (hT : ChartOK T) :
    T.ideal.IsPrime ∧ (affineHilbertPolynomial T.ideal).natDegree = r := by
  have hprime : (sourceIdeal T).IsPrime :=
    Ideal.span_singleton_prime hT.irreducible.ne_zero |>.mpr hT.irreducible.prime
  let := hprime
  have hD : T.denominator ∉ sourceIdeal T :=
    fun h => hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  have hne : Ideal.Quotient.mk (sourceIdeal T) T.denominator ≠ 0 :=
    mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  let : IsDomain (ChartOpen T) := Localization.Away.isDomain hne
  have hreg := (IsRegular.of_ne_zero hne).1
  have hsource : (affineHilbertPolynomial (sourceIdeal T)).natDegree = r := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      hT.irreducible.ne_zero hprime.ne_top
    rw [Nat.card_fin] at h
    exact Nat.add_right_cancel h
  rw [imageIdeal_eq_ker T hD]
  refine ⟨RingHom.ker_isPrime _, Eq.trans (le_antisymm ?_ ?_) hsource⟩
  · let E := awayPresentationEquiv (sourceIdeal T) T.denominator
    exact (natDegree_affineHilbertPolynomial_le_of_injective
      (E.symm.toAlgHom.comp (Ideal.kerLiftAlg (chartMap T)))
      (E.symm.injective.comp (Ideal.kerLiftAlg_injective (chartMap T)))).trans
      (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le (sourceIdeal T) T.denominator)
  · exact natDegree_affineHilbertPolynomial_le_of_away_range (sourceIdeal T) T.denominator hreg
      (chartMap T)
      (fun q => ⟨_, DFunLike.congr_fun (chartMap_recover T hT hD) q⟩) le_rfl
end
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial Filter
open scoped BigOperators
def c1 : Prop :=
  ∀ (T : Chart 2) (a d e : ℕ), ChartOK T →
    T.denominator ∈ bandSpace a d e →
    (∀ i, T.numerator i ∈ bandSpace a d e) →
    ∀ m : ℕ, affineHilbertFunction T.ideal m ≤
      Module.finrank Geo (quotientBand T (m * a) (m * d) (m * e))
def c2 : Prop :=
  ∀ (a d e : ℕ), d ≤ a → 2 * e ≤ d →
    (Module.finrank Geo (bandSpace a d e) : ℚ) = bandCount a d e
private theorem quotientBand_add_finrank_le (T : Chart 2) (a d e b j c : ℕ)
    (hn : T.equation ≠ 0) (hf : T.equation ∈ bandSpace b j c) :
    Module.finrank Geo (quotientBand T (a+b) (d+j) (e+c)) +
      Module.finrank Geo (bandSpace a d e) ≤
      Module.finrank Geo (bandSpace (a+b) (d+j) (e+c)) := by
  let W := bandSpace (a+b) (d+j) (e+c)
  let F := (Ideal.Quotient.mkₐ Geo (sourceIdeal T)).toLinearMap.domRestrict W
  have hF : LinearMap.range F = quotientBand T (a+b) (d+j) (e+c) :=
    LinearMap.range_domRestrict W _
  let mul := (LinearMap.mulLeft Geo T.equation).domRestrict (bandSpace a d e)
  have hmul (p : bandSpace a d e) : mul p ∈ W := by
    simpa only [mul, W, LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, Nat.add_comm]
      using mul_mem_bandSpace hf p.property
  let g : bandSpace a d e →ₗ[Geo] W := mul.codRestrict W hmul
  have hg (p : bandSpace a d e) : g p ∈ LinearMap.ker F := by
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (sourceIdeal T) (T.equation * p.val) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨p.val, rfl⟩)
  let G := g.codRestrict (LinearMap.ker F) hg
  have hG : Function.Injective G := by
    intro p q hpq
    have he : T.equation * p.val = T.equation * q.val :=
      congrArg (fun x : LinearMap.ker F => x.val.val) hpq
    exact Subtype.ext (mul_left_cancel₀ hn he)
  have hRank := F.finrank_range_add_finrank_ker
  rw [hF] at hRank
  exact (Nat.add_le_add_left (LinearMap.finrank_le_finrank_of_injective hG) _).trans_eq hRank
def surfaceBound (a d e b j c : ℚ) : ℚ :=
  2 * e * (d-e) * b + e * (2*a-2*d+e) * j + (d-2*e) * (2*a-d) * c
private abbrev indexDegree (P : InitialRing 2) : ℕ :=
  P.weightedTotalDegree Fin.val
private theorem band_difference (a d e b j c : ℚ) :
    ∃ u v : ℚ, ∀ x : ℚ,
      bandCount (x*a+j+2*c+b) (x*d+2*c+j) (x*e+c) -
        bandCount (x*a+j+2*c) (x*d+2*c) (x*e) =
      (surfaceBound a d e b j c / 2) * x^2 + u*x + v := by
  let f (x : ℚ) :=
    bandCount (x*a+j+2*c+b) (x*d+2*c+j) (x*e+c) -
      bandCount (x*a+j+2*c) (x*d+2*c) (x*e)
  refine ⟨f 1 - f 0 - surfaceBound a d e b j c / 2, f 0, fun x => ?_⟩
  dsimp [f, bandCount, surfaceBound]
  ring
private theorem degree_le_of_quadratic
    (I : Ideal CoeffRing) (hdim : (affineHilbertPolynomial I).natDegree = 2)
    (q u v : ℚ) (hle : ∀ᶠ m : ℕ in atTop,
      (affineHilbertPolynomial I).eval (m : ℚ) ≤ q * (m : ℚ)^2 + u * (m : ℚ) + v) :
    affineDegree I ≤ 2 * q := by
  let P : Polynomial ℚ := Polynomial.C q * Polynomial.X^2 +
    Polynomial.C u * Polynomial.X + Polynomial.C v
  have hP : ∀ᶠ m : ℕ in atTop, (affineHilbertPolynomial I).eval (m : ℚ) ≤ P.eval (m : ℚ) := by
    filter_upwards [hle] with m hm
    simpa [P] using hm
  obtain ⟨hnat, hlead⟩ := Polynomial.natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg I) hP
  have hdeg : P.natDegree = 2 := by
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      have h₀ : i ≠ 0 := by omega
      have h₁ : i ≠ 1 := by omega
      have h₂ : i ≠ 2 := by omega
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
      simp [h₀, h₁, h₂]
    · simpa only [hdim] using hnat
  have hc : P.leadingCoeff = q := by
    rw [Polynomial.leadingCoeff, hdeg]
    simp [P]
  have hcoeff := hlead (hdim.trans hdeg.symm)
  rw [hc] at hcoeff
  rw [affineDegree, hdim]
  exact mul_le_mul_of_nonneg_left hcoeff (by norm_num)
theorem chart_degree (h1 : c1) (h2 : c2)
    (T : Chart 2) (hT : ChartOK T) (hdim : (affineHilbertPolynomial T.ideal).natDegree = 2)
    (a d e : ℕ) (hda : d ≤ a) (hed : 2*e ≤ d)
    (hD : T.denominator ∈ bandSpace a d e) (hN : ∀ i, T.numerator i ∈ bandSpace a d e) :
    affineDegree T.ideal ≤ surfaceBound a d e T.equation.totalDegree
      (indexDegree T.equation)
      (T.equation.degreeOf (Fin.last 2)) := by
  let b := T.equation.totalDegree
  let j := indexDegree T.equation
  let c := T.equation.degreeOf (Fin.last 2)
  have hf : T.equation ∈ bandSpace b j c := mem_bandSpace.mpr ⟨le_rfl, le_rfl, le_rfl⟩
  obtain ⟨u, v, hexpand⟩ := band_difference a d e b j c
  have hle : ∀ᶠ m : ℕ in atTop, (affineHilbertPolynomial T.ideal).eval (m : ℚ) ≤
      (surfaceBound a d e b j c / 2) * (m : ℚ)^2 + u * (m : ℚ) + v := by
    filter_upwards [eventually_eval_affineHilbertPolynomial T.ideal] with m hm
    have hma := Nat.mul_le_mul_left m hda
    have hme : 2*(m*e) ≤ m*d := by
      simpa only [Nat.mul_left_comm 2 m e] using Nat.mul_le_mul_left m hed
    have hmono : Module.finrank Geo (quotientBand T (m*a) (m*d) (m*e)) ≤
        Module.finrank Geo (quotientBand T (m*a+j+2*c+b) (m*d+2*c+j) (m*e+c)) :=
      Submodule.finrank_mono (quotientBand_mono T (by omega) (by omega) (by omega))
    have hdimNat := (Nat.add_le_add_right ((h1 T a d e hT hD hN m).trans hmono) _).trans
      (quotientBand_add_finrank_le T (m*a+j+2*c) (m*d+2*c) (m*e) b j c hT.irreducible.ne_zero hf)
    have hdimRat := (Nat.cast_le (α := ℚ)).mpr hdimNat
    rw [Nat.cast_add,
      h2 (m*a+j+2*c) (m*d+2*c) (m*e) (by omega) (by omega),
      h2 (m*a+j+2*c+b) (m*d+2*c+j) (m*e+c) (by omega) (by omega)] at hdimRat
    push_cast at hdimRat
    rw [hm, ← hexpand (m : ℚ)]
    exact le_sub_iff_add_le.mpr hdimRat
  calc
    _ ≤ 2 * (surfaceBound a d e b j c / 2) :=
      degree_le_of_quadratic T.ideal hdim (surfaceBound a d e b j c / 2) u v hle
    _ = _ := by ring
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4_1
noncomputable section
open CJ0 CJ0_4 MvPolynomial
theorem proof : CJ0_4.c1 := by
  intro T a d e hT hD hN m
  let : (sourceIdeal T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  have hD' : T.denominator ∉ sourceIdeal T :=
    fun h => hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  rw [imageIdeal_eq_ker T hD']
  let j := IsScalarTower.toAlgHom Geo (InitialRing 2 ⧸ sourceIdeal T) (ChartOpen T)
  let δ := localize T T.denominator
  have hδ : IsUnit δ :=
    IsLocalization.Away.algebraMap_isUnit (S := ChartOpen T)
      (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
  let y (i : Fin k) := localize T (T.numerator i) * invDenom T
  have hy (i : Fin k) : δ * y i = localize T (T.numerator i) := by
    change localize T T.denominator * (localize T (T.numerator i) * invDenom T) = _
    rw [mul_left_comm _ (localize T (T.numerator i)), denom_mul_inv, mul_one]
  let V (n : ℕ) : Submodule Geo (ChartOpen T) :=
    (quotientBand T (n * a) (n * d) (n * e)).map j.toLinearMap
  let W (n : ℕ) : Submodule Geo (ChartOpen T) :=
    (V n).comap (LinearMap.mulLeft Geo (δ ^ n))
  have hW (n : ℕ) (z : ChartOpen T) :
      z ∈ W n ↔ ∃ P ∈ bandSpace (n * a) (n * d) (n * e), localize T P = δ ^ n * z := by
    change δ ^ n * z ∈ V n ↔ _
    simp only [V, quotientBand, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap,
      Submodule.mem_map, AlgHom.toLinearMap_apply, localize, j]
  have hOne : (1 : InitialRing 2) ∈ bandSpace 0 0 0 := by
    have hw : weightedTotalDegree Fin.val (1 : InitialRing 2) = 0 := by
      rw [← C_1, weightedTotalDegree_C]
    exact mem_bandSpace.mpr ⟨totalDegree_one.le, hw.le, (degreeOf_one _).le⟩
  have hpow (n : ℕ) :
      T.denominator ^ n ∈ bandSpace (n * a) (n * d) (n * e) := by
    induction n with
    | zero => simpa only [pow_zero, Nat.zero_mul] using hOne
    | succ n ih => simpa only [pow_succ, Nat.succ_mul] using mul_mem_bandSpace ih hD
  have hmono : Monotone W := by
    intro n l hnl z hz
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨T.denominator ^ (l - n) * P, ?_, ?_⟩
    · simpa only [← Nat.add_mul, Nat.sub_add_cancel hnl] using
        mul_mem_bandSpace (hpow (l - n)) hP
    · rw [map_mul, map_pow, heq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnl]
  have hmul (i : Fin k) (n : ℕ) (z : ChartOpen T) (hz : z ∈ W n) :
      y i * z ∈ W (n + 1) := by
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨P * T.numerator i, ?_, ?_⟩
    · simpa only [Nat.add_mul, Nat.one_mul] using mul_mem_bandSpace hP (hN i)
    · rw [map_mul, heq, ← hy i, pow_succ]
      ac_rfl
  have h0 : (1 : ChartOpen T) ∈ W 0 :=
    (hW _ _).mpr ⟨1, by simpa only [Nat.zero_mul] using hOne, by simp⟩
  have hclear (P : CoeffRing) (hP : P.totalDegree ≤ m) : chartMap T P ∈ W m := by
    change aeval y P ∈ W m
    simpa only [Nat.one_mul] using
      (aeval_mem_of_forall_mul_mem y hmono h0 hmul hP)
  let Q := RingHom.ker (chartMap T).toRingHom
  let ι : (CoeffRing ⧸ Q) →ₐ[Geo] ChartOpen T := Ideal.kerLiftAlg (chartMap T)
  have hmem (x : quotientDegreeLE Q m) : δ ^ m * ι x.val ∈ V m := by
    obtain ⟨P, hP, heq⟩ := mem_quotientDegreeLE.mp x.property
    change ι x.val ∈ W m
    rw [← heq]
    change chartMap T P ∈ W m
    exact hclear P hP
  let L : quotientDegreeLE Q m →ₗ[Geo] V m :=
    (((LinearMap.mulLeft Geo (δ ^ m)).comp ι.toLinearMap).domRestrict
      (quotientDegreeLE Q m)).codRestrict (V m) hmem
  have hL : Function.Injective L := by
    intro x z hxz
    have h : δ ^ m * ι x.val = δ ^ m * ι z.val := congrArg Subtype.val hxz
    exact Subtype.ext (Ideal.kerLiftAlg_injective (chartMap T) ((hδ.pow m).mul_left_cancel h))
  exact (LinearMap.finrank_le_finrank_of_injective hL).trans (Submodule.finrank_map_le _ _)
end
end CJ0_4_1
end
section
set_option autoImplicit false
namespace CJ0_4_2
noncomputable section
open CJ0 CJ0_4 MvPolynomial
open scoped BigOperators
private abbrev BandExponents (a d e : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {u | u.degree ≤ a ∧ u.weight Fin.val ≤ d ∧ u (Fin.last 2) ≤ e}
private theorem degree_fin_three (u : Fin 3 →₀ ℕ) :
    u.degree = u 0 + u 1 + u 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc]
private theorem degree_fin_two (u : Fin 2 →₀ ℕ) : u.degree = u 0 + u 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
private theorem index_fin_three (u : Fin 3 →₀ ℕ) :
    u.weight Fin.val = u 1 + 2 * u 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, Nat.mul_comm]
private def bandFibers (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d) :
    BandExponents a d e ≃ Σ z : Fin (e + 1),
      cappedDegreeExponents (Fin 2) 1 (a - z) (d - 2 * z) where
  toFun u := by
    have htotal := u.property.1
    have hindex := u.property.2.1
    have htop := u.property.2.2
    rw [degree_fin_three] at htotal
    rw [index_fin_three] at hindex
    change u.val 2 ≤ e at htop
    let z : Fin (e + 1) := ⟨u.val 2, Nat.lt_succ_of_le htop⟩
    refine ⟨z, ⟨Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1], ?_⟩⟩
    rw [mem_cappedDegreeExponents, degree_fin_two]
    change u.val 0 + u.val 1 ≤ a - u.val 2 ∧ u.val 1 ≤ d - 2 * u.val 2
    omega
  invFun p := by
    obtain ⟨z, u⟩ := p
    have htotal := u.property.1
    rw [degree_fin_two] at htotal
    have hindex := u.property.2
    have hz := z.isLt
    let v : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1, z.val]
    refine ⟨v, ?_⟩
    change v.degree ≤ a ∧ v.weight Fin.val ≤ d ∧ v (Fin.last 2) ≤ e
    rw [degree_fin_three, index_fin_three]
    change u.val 0 + u.val 1 + z.val ≤ a ∧ u.val 1 + 2 * z.val ≤ d ∧ z.val ≤ e
    omega
  left_inv u := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨z, hz⟩, u⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
private theorem sum_widths (d e : ℕ) (hed : 2 * e ≤ d) :
    (∑ z ∈ Finset.range (e + 1), (d - 2 * z + 1)) = (e + 1) * (d + 1 - e) := by
  calc
    _ = ∑ z ∈ Finset.range (e + 1), (d - 2 * (e - z) + 1) := by
      symm
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (fun z => d - 2 * z + 1) (e + 1)
    _ = ∑ z ∈ Finset.range (e + 1), ((d - 2 * e + 1) + 2 * z) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hz' := Finset.mem_range.mp hz
      omega
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
        ← Finset.mul_sum, mul_comm 2 (∑ z ∈ Finset.range (e + 1), z),
        Finset.sum_range_id_mul_two, Nat.add_sub_cancel, ← Nat.mul_add]
      congr 1
      omega
private theorem two_mul_finrank_band (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d) :
    2 * Module.finrank Geo (bandSpace a d e) = (e + 1) * (d + 1 - e) * (2 * a + 2 - d) := by
  rw [bandSpace, Module.finrank_eq_nat_card_basis (basisRestrictSupport Geo _),
    Nat.card_congr (bandFibers a d e hda hed), Nat.card_sigma, Finset.mul_sum]
  calc
    _ = ∑ z : Fin (e + 1), (d - 2 * z.val + 1) * (2 * a + 2 - d) := by
      apply Finset.sum_congr rfl
      intro z _
      have hz := z.isLt
      have hcap : d - 2 * z.val ≤ a - z.val := by omega
      rw [Nat.card_coe_set_eq, two_mul_ncard_cappedDegreeExponents_fin_two _ _ hcap]
      congr 1
      omega
    _ = _ := by
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun z => d - 2 * z + 1),
        sum_widths d e hed]
theorem proof : CJ0_4.c2 := by
  intro a d e hda hed
  have he : e ≤ d + 1 := by omega
  have hd : d ≤ 2 * a + 2 := by omega
  have h := congrArg (fun n : ℕ => (n : ℚ)) (two_mul_finrank_band a d e hda hed)
  push_cast [Nat.cast_sub he, Nat.cast_sub hd] at h
  unfold bandCount
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2
  rw [mul_comm]
  exact h
end
end CJ0_4_2
end

end Merged6967_ListProofA

section Merged6967_PrimaryTaperBudget
set_option Elab.async false


set_option Elab.async false

-- merged module Primary82170
section Merged_Primary82170

set_option Elab.async false

namespace Primary82170

open K1_13 K1_13_2 K1_13_2_3
open scoped BigOperators
open K1_13_2_3 (combine baseline_budget_on savings_parts sum_add_pointwise_eq bound_le_baseline)




end Primary82170

end Merged_Primary82170

-- merged module PrimaryTaperRank
section Merged_PrimaryTaperRank

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

namespace TaperNormalize

noncomputable section

open K1_13 K1_13_2 K1_13_2_2
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

def blockExponents (k : ℕ) (i : BlockIndex) : Set SourceExponent :=
  {e | e ∈ K1_13_2.blockExponents i ∧ e (some 1) + e (some 2) + e (some 3) ≤ k}

def BlockSpace (k : ℕ) (i : BlockIndex) : Submodule Geom SourcePolynomial :=
  restrictSupport Geom (blockExponents k i)

instance (k : ℕ) (i : BlockIndex) : Module.Finite Geom (BlockSpace k i) :=
  restrictSupport_finite (sourceExponents_finite.subset (fun _ h => h.1.1))

def originBlock (k : ℕ) (i : BlockIndex) : BlockSpace k i →ₗ[Geom] Local :=
  (localConstraintAt 3000 0 0).domRestrict (BlockSpace k i)

variable (k : ℕ)
def residualDegree (k : ℕ) (i : BlockIndex) : ℕ := min i.1.val k

def activeFlag (i : BlockIndex) : Flag :=
  {K1_13_2_2.activeFlag i with degree := (residualDegree k i : ℤ)}

private theorem active_degree (i : BlockIndex) :
    (activeFlag k i).degree = (residualDegree k i : ℤ) := by
  rfl
private def removed (i : BlockIndex) : ℕ := i.1.val - residualDegree k i
private def stripped (i : BlockIndex) (e : SourceExponent) : JetExp :=
  Finsupp.equivFunOnFinite.symm
    ![e (some 0) - removed k i, e (some 1), e (some 2), e (some 3)]
private theorem source_grade (e : SourceExponent) :
    e.weight jetDegreeWeight = e (some 0) + e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four]
private theorem source_index (e : SourceExponent) :
    e.weight jetDerivativeWeight = e (some 1) + 2 * e (some 2) + 3 * e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, jetDerivativeWeight,
    smul_eq_mul, Nat.mul_comm]
private theorem removed_le (i : BlockIndex) (e : blockExponents k i) :
    removed k i ≤ e.val (some 0) := by
  have hd := e.property.1.2.2.1
  have hcap := e.property.2
  rw [source_grade] at hd
  simp only [removed, residualDegree]
  omega
private theorem stripped_mem (i : BlockIndex) (e : blockExponents k i) :
    stripped k i e ∈ oldExponents (activeFlag k i) := by
  have hd := e.property.1.2.2.1
  have hj := e.property.1.1.2.1
  have hc := e.property.1.1.2.2.1
  have hx := e.property.1.2.1
  have hg := e.property.1.2.2.2
  have ha := removed_le k i e
  rw [source_grade] at hd
  rw [source_index] at hj hg
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, topWeight, Pi.single_apply,
    smul_eq_mul] at hc
  change ((stripped k i e).weight gradeWeight : ℤ) = (activeFlag k i).degree ∧
    -offset i ≤ ((stripped k i e).weight oldWeight : ℤ) ∧
    ((stripped k i e).weight oldWeight : ℤ) ≤ min 1650 (2999 - offset i) ∧
    ((stripped k i e) 3 : ℤ) ≤ 550
  rw [active_degree]
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, gradeWeight, oldWeight, stripped,
    smul_eq_mul, Nat.mul_comm]
  simp only [removed, residualDegree] at *
  omega
private def encodeColumn (i : BlockIndex) (e : blockExponents k i) : oldSpace (activeFlag k i) := by
  refine ⟨monomial (stripped k i e) 1, ?_⟩
  change monomial (stripped k i e) 1 ∈ restrictSupport Geom (oldExponents (activeFlag k i))
  exact (monomial_mem_restrictSupport Geom).mpr (Or.inl (stripped_mem k i e))
private def encode (i : BlockIndex) : BlockSpace k i →ₗ[Geom] oldSpace (activeFlag k i) :=
  (basisRestrictSupport Geom (blockExponents k i)).constr Geom (encodeColumn k i)
private theorem encode_basis (i : BlockIndex) (e : blockExponents k i) :
    ((encode k i (basisRestrictSupport Geom (blockExponents k i) e)) : JetPoly) =
      monomial (stripped k i e) 1 :=
  congrArg Subtype.val
    ((basisRestrictSupport Geom (blockExponents k i)).constr_basis Geom (encodeColumn k i) e)
local notation "T" => (MvPolynomial.X (localT 3) : Local)
local notation "E" => (MvPolynomial.X (localE 3) : Local)
private def jetVar (j : Fin 3) : Local := MvPolynomial.X (localY j)
private def valueImage : Local := unscaledLocalImage 3 0 0 (some 0)
private def scaledImage : Fin 4 → Local :=
  ![T * E, T * jetVar 0, T ^ 2 * jetVar 1, T ^ 3 * jetVar 2]
private def originSubst : SourcePolynomial →ₐ[Geom] Local := unscaledLocalSubstitution 3 0 0
private theorem scaled_shear_zero : bind₁ scaledImage (shearImage 0) = valueImage := by
  simp [shearImage, scaledImage, valueImage, unscaledLocalImage, localCorrection, Fin.sum_univ_three, jetVar]
  ring
private theorem scaled_shear_succ (j : Fin 3) :
    bind₁ scaledImage (shearImage j.succ) = T ^ j.succ.val * jetVar j := by
  fin_cases j <;> simp [shearImage, scaledImage]
private theorem bind_monomial_one {σ τ : Type*} [Fintype σ]
    (f : σ → MvPolynomial τ Geom) (e : σ →₀ ℕ) :
    bind₁ f (monomial e 1) = ∏ j, f j ^ e j := by
  rw [bind₁_monomial, C_1, one_mul]
  exact Finsupp.prod_fintype e (fun j n => f j ^ n) (fun _ => pow_zero _)
private theorem origin_monomial (e : SourceExponent) :
    originSubst (monomial e 1) = T ^ e none *
      (valueImage ^ e (some 0) * (jetVar 0) ^ e (some 1) * (jetVar 1) ^ e (some 2) * (jetVar 2) ^ e (some 3)) := by
  rw [originSubst, unscaledLocalSubstitution, bind_monomial_one, Fintype.prod_option, Fin.prod_univ_four]
  change (C (0 : Geom) + T) ^ e none *
    (valueImage ^ e (some 0) * (jetVar 0) ^ e (some 1) * (jetVar 1) ^ e (some 2) * (jetVar 2) ^ e (some 3)) = _
  simp
private theorem stripped_monomial (i : BlockIndex) (e : SourceExponent) :
    bind₁ scaledImage (coordinateChange (monomial (stripped k i e) 1)) =
    valueImage ^ (e (some 0) - removed k i) *
      (T * jetVar 0) ^ e (some 1) * (T ^ 2 * jetVar 1) ^ e (some 2) * (T ^ 3 * jetVar 2) ^ e (some 3) := by
  rw [coordinateChange, bind₁_bind₁, bind_monomial_one, Fin.prod_univ_four]
  have h1 := scaled_shear_succ (0 : Fin 3)
  have h2 := scaled_shear_succ (1 : Fin 3)
  have h3 := scaled_shear_succ (2 : Fin 3)
  change bind₁ scaledImage (shearImage 1) = T ^ 1 * jetVar 0 at h1
  change bind₁ scaledImage (shearImage 2) = T ^ 2 * jetVar 1 at h2
  change bind₁ scaledImage (shearImage 3) = T ^ 3 * jetVar 2 at h3
  simp [scaled_shear_zero, h1, h2, h3, stripped]
private theorem shifted_origin_monomial (i : BlockIndex) (e : blockExponents k i) :
    T ^ (-offset i).toNat * originSubst (monomial e.val 1) =
    T ^ (offset i).toNat * valueImage ^ removed k i *
      bind₁ scaledImage (coordinateChange (monomial (stripped k i e) 1)) := by
  have hx := e.property.1.2.2.2
  rw [source_index] at hx
  have ht : (-offset i).toNat + e.val none =
      (offset i).toNat + e.val (some 1) + 2 * e.val (some 2) + 3 * e.val (some 3) := by omega
  have ha : removed k i + (e.val (some 0) - removed k i) = e.val (some 0) := by
    have := removed_le k i e
    omega
  have hT : T ^ (-offset i).toNat * T ^ e.val none =
      T ^ (offset i).toNat * T ^ e.val (some 1) * T ^ (2 * e.val (some 2)) *
        T ^ (3 * e.val (some 3)) := by
    simpa only [pow_add] using congrArg (T ^ ·) ht
  have hA : valueImage ^ e.val (some 0) =
      valueImage ^ removed k i * valueImage ^ (e.val (some 0) - removed k i) := by
    rw [← pow_add, ha]
  rw [origin_monomial, stripped_monomial]
  simp only [mul_pow, ← pow_mul]
  calc
    _ = (T ^ (-offset i).toNat * T ^ e.val none) *
        (valueImage ^ e.val (some 0) * (jetVar 0) ^ e.val (some 1) *
          (jetVar 1) ^ e.val (some 2) * (jetVar 2) ^ e.val (some 3)) := by ring
    _ = _ := by rw [hT, hA]; ring
private theorem shifted_origin (i : BlockIndex) (p : BlockSpace k i) :
    T ^ (-offset i).toNat * originSubst (p : SourcePolynomial) =
    T ^ (offset i).toNat * valueImage ^ removed k i *
      bind₁ scaledImage (coordinateChange ((encode k i p : oldSpace (activeFlag k i)) : JetPoly)) := by
  let l := (LinearMap.mulLeft Geom (T ^ (-offset i).toNat)).comp
    (originSubst.toLinearMap.comp (BlockSpace k i).subtype)
  let r := (LinearMap.mulLeft Geom (T ^ (offset i).toNat * valueImage ^ removed k i)).comp
    ((bind₁ scaledImage).toLinearMap.comp
      (coordinateChange.toLinearMap.comp ((oldSpace (activeFlag k i)).subtype.comp (encode k i))))
  have h : l = r := by
    apply (basisRestrictSupport Geom (blockExponents k i)).ext
    intro e
    change T ^ (-offset i).toNat *
      originSubst (↑(basisRestrictSupport Geom (blockExponents k i) e) : SourcePolynomial) =
      T ^ (offset i).toNat * valueImage ^ removed k i *
        bind₁ scaledImage (coordinateChange
          (↑(encode k i (basisRestrictSupport Geom (blockExponents k i) e)) : JetPoly))
    rw [encode_basis, coe_basisRestrictSupport_apply]
    exact shifted_origin_monomial k i e
  exact LinearMap.congr_fun h p
private def scaledWeight (j : Fin 4) : ℕ := contactWeight j + gradeWeight j
private theorem weight_scaled (e : JetExp) :
    e.weight scaledWeight = e.weight contactWeight + e.weight gradeWeight := by
  simp [Finsupp.weight_eq_sum, scaledWeight, smul_eq_mul, Nat.mul_add, Finset.sum_add_distrib]
private theorem t_power_order (n : ℕ) :
    T ^ n ∈ restrictWeightedOrder (localContactWeight 3) n := by
  simpa using pow_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := Geom) (localContactWeight 3) (localT 3) (m := 1) le_rfl) n
private theorem scaled_image_order (j : Fin 4) :
    scaledImage j ∈ restrictWeightedOrder (localContactWeight 3) (scaledWeight j) := by
  have hY (k : Fin 3) : jetVar k ∈ restrictWeightedOrder (localContactWeight 3) 0 := by simp
  have hE : E ∈ restrictWeightedOrder (localContactWeight 3) 3 :=
    X_mem_restrictWeightedOrder _ _ le_rfl
  fin_cases j
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 1) hE
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 1) (hY 0)
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 2) (hY 1)
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 3) (hY 2)
private theorem value_order :
    valueImage ∈ restrictWeightedOrder (localContactWeight 3) 1 := by
  have h (j : Fin 4) : scaledImage j ∈ restrictWeightedOrder (localContactWeight 3) 1 :=
    restrictWeightedOrder_anti _ (Nat.succ_le_succ (Nat.zero_le _)) (scaled_image_order j)
  rw [← scaled_shear_zero]
  simp only [shearImage, ite_true, map_add, map_sub, bind₁_X_right]
  exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (h 0) (h 1)) (h 2)) (h 3)
private theorem order_of_t_power_mul {n m : ℕ} {p : Local}
    (h : T ^ n * p ∈ restrictWeightedOrder (localContactWeight 3) (m + n)) :
    p ∈ restrictWeightedOrder (localContactWeight 3) m := by
  rw [MvPolynomial.X_pow_eq_monomial] at h
  intro e he
  have hh := mem_restrictWeightedOrder.mp h (Finsupp.single (localT 3) n + e) (by
    rw [MvPolynomial.mem_support_iff, coeff_monomial_mul, one_mul]
    exact MvPolynomial.mem_support_iff.mp he)
  change m ≤ e.weight (localContactWeight 3)
  simp only [map_add, Finsupp.weight_single, localContactWeight_T, smul_eq_mul, mul_one] at hh
  omega
private theorem kernel_le (i : BlockIndex) :
    LinearMap.ker ((flagContact (activeFlag k i)).comp (encode k i)) ≤ LinearMap.ker (originBlock k i) := by
  intro p hp
  let q : oldSpace (activeFlag k i) := encode k i p
  let shear : JetPoly := coordinateChange (q : JetPoly)
  let cut := (activeFlag k i).order.toNat
  have hz : weightedTruncation contactWeight cut shear = 0 := LinearMap.mem_ker.mp hp
  have hcontact := (weightedTruncation_eq_zero_iff _ _ _).mp hz
  have hgrade : (q : JetPoly).IsWeightedHomogeneous gradeWeight (residualDegree k i) := by
    intro e he
    have hd := (q.property (mem_support_iff.mpr he)).1
    change (e.weight gradeWeight : ℤ) = (activeFlag k i).degree at hd
    rw [active_degree] at hd
    omega
  have hshear : shear.IsWeightedHomogeneous gradeWeight (residualDegree k i) :=
    hgrade.bind₁ shearImage_grade
  have hscaled : shear ∈ restrictWeightedOrder scaledWeight (cut + residualDegree k i) := by
    intro e he
    have hg := hshear (mem_support_iff.mp he)
    have hc := mem_restrictWeightedOrder.mp hcontact e he
    change cut + residualDegree k i ≤ e.weight scaledWeight
    rw [weight_scaled, hg]
    exact Nat.add_le_add_right hc _
  have hprod := mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder (t_power_order (offset i).toNat)
      (by simpa using pow_mem_restrictWeightedOrder value_order (removed k i)))
    (bind₁_mem_restrictWeightedOrder scaled_image_order hscaled)
  have hbound : 3000 + (-offset i).toNat ≤
      (offset i).toNat + removed k i + (cut + residualDegree k i) := by
    change 3000 + (-offset i).toNat ≤ (offset i).toNat + removed k i +
      ((3000 - (i.1.val : ℤ) - offset i).toNat + residualDegree k i)
    simp only [removed, residualDegree]
    omega
  have hshift : T ^ (-offset i).toNat * originSubst (p : SourcePolynomial) ∈
      restrictWeightedOrder (localContactWeight 3) (3000 + (-offset i).toNat) := by
    rw [shifted_origin]
    exact restrictWeightedOrder_anti _ hbound hprod
  apply LinearMap.mem_ker.mpr
  change weightedTruncation (localContactWeight 3) 3000 (originSubst (p : SourcePolynomial)) = 0
  exact (weightedTruncation_eq_zero_iff _ _ _).mpr (order_of_t_power_mul hshift)
theorem origin_block_rank (i : BlockIndex) :
    Module.finrank Geom (LinearMap.range (originBlock k i)) ≤
      Module.finrank Geom (LinearMap.range (flagContact (activeFlag k i))) := by
  let f := (flagContact (activeFlag k i)).comp (encode k i)
  have hker := Submodule.finrank_mono (kernel_le k i)
  change Module.finrank Geom (LinearMap.ker f) ≤
    Module.finrank Geom (LinearMap.ker (originBlock k i)) at hker
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ := (originBlock k i).finrank_range_add_finrank_ker
  exact (show Module.finrank Geom (LinearMap.range (originBlock k i)) ≤
      Module.finrank Geom (LinearMap.range f) by omega).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))

open K1_13_2_2 (rank_zero_of_order_nonpos lower_le_kernel)

def initialFlag (i : BlockIndex) : Flag :=
  {K1_13_2.initialFlag i with degree := (residualDegree k i : ℤ)}

private theorem taper_active_range_le (i : BlockIndex) :
    LinearMap.range (flagContact (activeFlag k i)) ≤
      LinearMap.range (flagContact (initialFlag k i)) := by
  rintro _ ⟨p, rfl⟩
  refine ⟨⟨p.1, ?_⟩, rfl⟩
  intro e he
  obtain ⟨hgrade, hlow, hupp, hcap⟩ := p.2 he
  exact ⟨hgrade, hlow, hupp.trans (min_le_left _ _), hcap⟩

def bound (i : BlockIndex) (power : Fin 11 → ℕ) : ℕ :=
  let F := initialFlag k i
  if F.order ≤ 0 then 0 else
    let active := oldCount (activeFlag k i)
    let lower := max 0 (max (kernelLower F) (kernelLower (residualFlag F power)))
    (min active (oldCount F - lower)).toNat

theorem origin_block_rank_bound (h2 : K1_13_2_2.c2) (h3 : K1_13_2_2.c3) (h4 : K1_13_2_2.c4) (h5 : K1_13_2_2.c5)
    (i : BlockIndex) (power : Fin 11 → ℕ) :
    Module.finrank Geom (LinearMap.range (originBlock k i)) ≤ bound k i power := by
  let F := initialFlag k i
  let A := activeFlag k i
  have hOrigin := origin_block_rank k i
  change Module.finrank Geom (LinearMap.range (originBlock k i)) ≤
    Module.finrank Geom (LinearMap.range (flagContact A)) at hOrigin
  by_cases ho : F.order ≤ 0
  · have hz := rank_zero_of_order_nonpos A (show A.order ≤ 0 from ho)
    have h := hOrigin.trans (le_of_eq hz)
    have horder : (initialFlag k i).order ≤ 0 := ho
    simpa [bound, horder] using h
  have hActive := (flagContact A).finrank_range_le
  rw [finrank_oldSpace] at hActive
  have hCols := h3 h2
  have hRows := h4 h2
  have hKernel0 := lower_le_kernel F (hCols F) (hRows F)
  have hKernel1 := lower_le_kernel (residualFlag F power)
    (hCols (residualFlag F power)) (hRows (residualFlag F power))
  obtain ⟨f, hf⟩ := h5 F power
  have hInj := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hRank := Submodule.finrank_mono (taper_active_range_le k i)
  change Module.finrank Geom (LinearMap.range (flagContact A)) ≤
    Module.finrank Geom (LinearMap.range (flagContact F)) at hRank
  have hNullity := (flagContact F).finrank_range_add_finrank_ker
  rw [finrank_oldSpace] at hNullity
  have hFullCols := hCols F
  have hActiveCols := hCols A
  have hbound :
      (Module.finrank Geom (LinearMap.range (originBlock k i)) : ℤ) ≤
      min (oldCount A)
        (oldCount F - max 0 (max (kernelLower F) (kernelLower (residualFlag F power)))) := by
    apply le_min
    · omega
    · have hMax :
          max 0 (max (kernelLower F) (kernelLower (residualFlag F power))) ≤
            (Module.finrank Geom (LinearMap.ker (flagContact F)) : ℤ) := by
        exact max_le (Int.natCast_nonneg _) (max_le hKernel0 (by omega))
      omega
  unfold bound
  change Module.finrank Geom (LinearMap.range (originBlock k i)) ≤
    (if F.order ≤ 0 then 0 else
      (min (oldCount A)
        (oldCount F - max 0 (max (kernelLower F) (kernelLower (residualFlag F power))))).toNat)
  rw [ite_eq_right ho]
  omega

open P0_9_2 (high_monomial_vanishes)
open K1_13_2 (finrank_finset_sup_le)

def differentiated : JetVariable 3 → ℕ := fun v => v.elim 0 (fun j => if j = 0 then 0 else 1)

def Eligible (cap : ℕ → ℕ) (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧ e.weight jetDerivativeWeight ≤ 1650 ∧
    e.weight topWeight ≤ 550 ∧ e.weight differentiated ≤ cap (e.weight jetDegreeWeight)

def space (cap : ℕ → ℕ) : Submodule Geom SourcePolynomial := restrictSupport Geom {e | Eligible cap e}

private theorem differentiated_eq (e : SourceExponent) :
    e.weight differentiated = e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, differentiated]

private theorem translate_monomial {cap : ℕ → ℕ} (hc : Antitone cap)
    (x y : Geom) (e : SourceExponent) (c : Geom) (he : Eligible cap e) :
    globalPointTranslation x y (monomial e c) ∈ space cap := by
  have preserve {w : JetVariable 3 → ℕ} {n : ℕ} (h : e.weight w ≤ n) :
      ∀ a ∈ (globalPointTranslation x y (monomial e c)).support, a.weight w ≤ n :=
    mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x y ((monomial_mem_restrictWeightAtMost _ _ _ _).mpr (Or.inl h)))
  intro a ha
  have hgrade := preserve (w := jetDegreeWeight) (le_refl _) a ha
  exact ⟨hgrade.trans he.1, preserve he.2.1 a ha, preserve he.2.2.1 a ha,
    (preserve he.2.2.2 a ha).trans (hc hgrade)⟩

theorem translate {cap : ℕ → ℕ} (hc : Antitone cap) (x y : Geom) (Q : space cap) :
    globalPointTranslation x y Q.1 ∈ space cap := by
  rw [congrArg (globalPointTranslation x y) Q.1.as_sum, map_sum]
  exact Submodule.sum_mem _ fun e he => translate_monomial hc x y e (Q.1.coeff e) (Q.2 he)

private theorem finrank_of_column_cover {ι : Type*} [Fintype ι]
    (source : Set SourceExponent) (f f' : SourcePolynomial →ₗ[Geom] Local)
    (shift : SourcePolynomial → SourcePolynomial)
    (hshift : ∀ Q ∈ restrictSupport Geom source, shift Q ∈ restrictSupport Geom source)
    (heval : ∀ Q, f' Q = f (shift Q)) (p : ι → Submodule Geom Local)
    [∀ i, Module.Finite Geom (p i)] (bound : ι → ℕ)
    (hcol : ∀ e ∈ source, ∀ c, f (MvPolynomial.monomial e c) = 0 ∨
      ∃ i, f (MvPolynomial.monomial e c) ∈ p i)
    (hbound : ∀ i, Module.finrank Geom (p i) ≤ bound i) :
    Module.finrank Geom (LinearMap.range (f'.domRestrict (restrictSupport Geom source))) ≤ ∑ i, bound i := by
  classical
  have cover : LinearMap.range (f'.domRestrict (restrictSupport Geom source)) ≤ Finset.univ.sup p := by
    intro L hL
    obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp hL
    rw [← hQ]
    change f' Q.1 ∈ Finset.univ.sup p
    rw [heval]
    let R := shift Q.1
    have hR : R ∈ restrictSupport Geom source := hshift _ Q.2
    have expand := congrArg f R.as_sum
    rw [map_sum] at expand
    rw [expand]
    refine Submodule.sum_mem _ fun e he => ?_
    rcases hcol e (hR he) (R.coeff e) with hzero | ⟨i, hi⟩
    · rw [hzero]
      exact Submodule.zero_mem _
    · exact (Finset.le_sup (f := p) (Finset.mem_univ i)) hi
  exact (Submodule.finrank_mono cover).trans
    ((finrank_finset_sup_le p _).trans (Finset.sum_le_sum fun i _ => hbound i))
theorem rank_le_of_blocks {cap : ℕ → ℕ} (hc : Antitone cap) (x y : Geom)
    (budget : BlockIndex → ℕ)
    (hbudget : ∀ i, Module.finrank Geom (LinearMap.range (originBlock (cap i.1.val) i)) ≤ budget i) :
    Module.finrank Geom (LinearMap.range ((localConstraintAt 3000 x y).domRestrict (space cap))) ≤
      ∑ i : BlockIndex, budget i := by
  let ranges : BlockIndex → Submodule Geom Local :=
    fun i => LinearMap.range (originBlock (cap i.1.val) i)
  have (i : BlockIndex) : Module.Finite Geom (ranges i) := by dsimp only [ranges]; infer_instance
  refine finrank_of_column_cover {e | Eligible cap e}
    (localConstraintAt 3000 0 0) (localConstraintAt 3000 x y) (globalPointTranslation x y)
    (fun Q hQ => translate hc x y ⟨Q, hQ⟩)
    (fun Q => localConstraintAt_eq_zero_globalPointTranslation x y Q)
    ranges budget ?_ hbudget
  intro e he c
  by_cases hx : e none < 3000
  · have he' : Eligible cap e := he
    let grade := e.weight jetDegreeWeight
    let idx := e.weight jetDerivativeWeight
    have hb : grade ≤ 4012 := he'.1
    have hj : idx ≤ 1650 := he'.2.1
    let i : BlockIndex := (⟨grade, by omega⟩, ⟨e none + (1650 - idx), by omega⟩)
    have hw := weight_le_add_mul_totalJetDegree 133671 e
    change e.weight (differentialWeight 133671) ≤ e none + 133671 * grade at hw
    have hold : SourceEligible e := ⟨hb, hj, he'.2.2.1, by omega⟩
    have hi : e ∈ blockExponents (cap i.1.val) i := by
      refine ⟨⟨hold, hx, rfl, ?_⟩, ?_⟩
      · change (e none : ℤ) - idx = ((e none + (1650 - idx) : ℕ) : ℤ) - 1650
        omega
      · simpa only [← differentiated_eq] using he'.2.2.2
    have hm : monomial e c ∈ BlockSpace (cap i.1.val) i :=
      (monomial_mem_restrictSupport Geom).mpr (Or.inl hi)
    exact Or.inr ⟨i, ⟨⟨_, hm⟩, rfl⟩⟩
  · exact Or.inl (high_monomial_vanishes _ _ (Nat.le_of_not_gt hx))


theorem range_le_old (i : BlockIndex) :
    LinearMap.range (originBlock k i) ≤ LinearMap.range (K1_13_2.originBlock i) := by
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨p.1, fun e he => (p.2 he).1⟩, rfl⟩

#print axioms range_le_old
end
end TaperNormalize

end Merged_PrimaryTaperRank

-- merged module PrimaryTaperBudget
section Merged_PrimaryTaperBudget

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

namespace TaperBudget

open K1_13 (Geom)
open K1_13_2 K1_13_2_3
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

def cap (q : ℕ) : ℕ :=
  if q < 3514 then 1650 else (131312 - 26 * q) / 25

theorem cap_antitone : Antitone cap := by
  intro a b hab
  unfold cap
  split <;> split <;> omega

def valuePower (capAtGrade q j : ℕ) : ℕ :=
  min capAtGrade (3000 + capAtGrade - q - 4 * j)

def power (i : BlockIndex) : Fin 11 → ℕ :=
  (⟨valuePower (cap i.1.val) i.1.val i.2.val, 0, 0⟩ : Powers).expand

def tailSaving (i : BlockIndex) : ℕ :=
  if 3514 ≤ i.1.val then baseline i - TaperNormalize.bound (cap i.1.val) i (power i)
  else 0

def valueRowCell (s j : ℕ) : ℕ :=
  if hs : s < 499 then if hj : j < 1136 then
    tailSaving (⟨3514 + s, by omega⟩, ⟨j, by omega⟩)
  else 0 else 0

def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n



open K1_13_2_3_7 (fastCum signedKernel)
open K1_13_2_3_7 (chart oldCount_eq kernel_eq residual_eq)
open TaperNormalize (residualDegree)

def fastRank (d j : ℕ) (h : ℤ) (p : ℕ) : ℕ :=
  if h < 0 then 0 else
    (fastCum d 1650 - fastCum d (1649 - (j : ℤ)) -
      max 0 (max (signedKernel d j h) (signedKernel ((d : ℤ) - p) j h))).toNat

theorem tapered_rank_eq_fast (k p : ℕ) (i : BlockIndex) (hq : 3514 ≤ i.1.val) (hk : k ≤ i.1.val) (hp : p ≤ k) :
    TaperNormalize.bound k i (Powers.expand ⟨p, 0, 0⟩) =
      fastRank k i.2.val (4649 - (i.1.val : ℤ) - i.2.val) p := by
  let h : ℤ := 4649 - (i.1.val : ℤ) - i.2.val
  let f := chart k i.2.val h
  have hf : TaperNormalize.initialFlag k i = f := by
    simp [TaperNormalize.initialFlag, initialFlag, residualDegree, f, chart, h, offset, min_eq_right hk]
    omega
  have hA : TaperNormalize.activeFlag k i =
      { f with upper := min 1650 (2999 - offset i) } := by
    simp [TaperNormalize.activeFlag, K1_13_2_2.activeFlag, initialFlag, residualDegree, f, chart, h,
      offset, min_eq_right hk]
    omega
  have hOrder : f.order = h+1 := rfl
  have hj : (0 : ℤ) ≤ i.2.val := Int.natCast_nonneg _
  unfold TaperNormalize.bound fastRank
  rw [hf, hA]
  simp only
  rw [hOrder]
  by_cases hh : h < 0
  · rw [ite_eq_left (show h+1 ≤ 0 by omega), ite_eq_left hh]
  · rw [ite_eq_right (show ¬h+1 ≤ 0 by omega), ite_eq_right hh]
    have hU : min (1650 : ℤ) (2999 - offset i) = 1650 := by
      rw [min_eq_left]
      unfold offset h at *
      omega
    rw [hU]
    change (min (oldCount f) _).toNat = _
    have hn := le_max_left (0 : ℤ)
      (max (kernelLower f) (kernelLower (residualFlag f (Powers.expand ⟨p, 0, 0⟩))))
    rw [min_eq_right (by omega)]
    rw [show residualFlag f (Powers.expand ⟨p, 0, 0⟩) =
      chart ((k : ℤ)-p) i.2.val h from residual_eq _ _ _ _]
    rw [oldCount_eq _ _ _ hj, kernel_eq _ _ _ (Int.natCast_nonneg _) hj,
      kernel_eq _ _ _ (by omega) hj]

def fastCell (t j : ℕ) : ℕ :=
  let q := 3514 + t
  let h : ℤ := 1135 - (t : ℤ) - j
  let d := cap q
  fastRank 1650 j h 0 - fastRank d j h (valuePower d q j)

theorem old_flag_eq (i : BlockIndex) :
    TaperNormalize.initialFlag 1650 i = initialFlag i := by
  have hmin : ((min i.1.val 1650 : ℕ) : ℤ) = min (i.1.val : ℤ) 1650 := by omega
  simp [TaperNormalize.initialFlag, residualDegree, initialFlag, hmin]

theorem old_bound_eq (i : BlockIndex) (p : Fin 11 → ℕ) :
    TaperNormalize.bound 1650 i p = blockBound i p := by
  have hA : TaperNormalize.activeFlag 1650 i = K1_13_2_2.activeFlag i := by
    have hmin : ((min i.1.val 1650 : ℕ) : ℤ) = min (i.1.val : ℤ) 1650 := by omega
    simp [TaperNormalize.activeFlag, K1_13_2_2.activeFlag, residualDegree, initialFlag, hmin]
  simp only [TaperNormalize.bound, old_flag_eq, hA, blockBound]
  rfl

private theorem power_zero : (Powers.expand ⟨0, 0, 0⟩) = (fun _ => 0) := by
  funext x
  fin_cases x <;> rfl

theorem fastCell_eq {t j : ℕ} (ht : t < 499) (hj : j < 1136) :
    fastCell t j = valueRowCell t j := by
  let i : BlockIndex := (⟨3514 + t, by omega⟩, ⟨j, by omega⟩)
  have hq : i.1.val = 3514 + t := rfl
  have hji : i.2.val = j := rfl
  have hgrade : 3514 ≤ i.1.val := by omega
  have hd : cap i.1.val ≤ i.1.val := by simp [cap, show ¬ i.1.val < 3514 by omega]; omega
  let p := valuePower (cap i.1.val) i.1.val i.2.val
  have hp : p ≤ cap i.1.val := min_le_left _ _
  have ho := tapered_rank_eq_fast 1650 0 i hgrade (by omega) (by omega)
  rw [power_zero, old_bound_eq] at ho
  have hn := tapered_rank_eq_fast (cap i.1.val) p i hgrade hd hp
  unfold valueRowCell
  rw [dite_eq_left ht, dite_eq_left hj]
  change fastCell t j = tailSaving i
  rw [tailSaving, ite_eq_left hgrade]
  change fastCell t j = blockBound i (fun _ => 0) - TaperNormalize.bound (cap i.1.val) i (Powers.expand ⟨p,0,0⟩)
  rw [ho, hn]
  have hh : (4649 - (i.1.val : ℤ) - i.2.val) = 1135 - (t : ℤ) - j := by
    rw [hq, hji]
    push_cast
    ring
  rw [hh]
  rfl

def fastSavings (J : ℕ) : ℕ :=
  sumRange (fun t => sumRange (fastCell t) J) 499

theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]

theorem sumRange_fin (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ k : Fin n, f k.val := by
  rw [sumRange_eq, Fin.sum_univ_eq_sum_range]

private def windowEmbed {J : ℕ} (hJ : J ≤ 1136) : Fin 499 × Fin J ↪ BlockIndex where
  toFun i := (⟨3514 + i.1.val, by have := i.1.isLt; omega⟩, i.2.castLE (by omega))
  inj' := by
    intro x y h
    apply Prod.ext <;> apply Fin.ext
    · have e := congrArg (fun i : BlockIndex => i.1.val) h
      change 3514 + x.1.val = 3514 + y.1.val at e
      omega
    · exact congrArg (fun i : BlockIndex => i.2.val) h

open K1_13_2_3_7 (sum_embed_le)

theorem fastSavings_le {J : ℕ} (hJ : J ≤ 1136) :
    fastSavings J ≤ ∑ i : BlockIndex, tailSaving i := by
  unfold fastSavings
  simp only [sumRange_fin]
  rw [← Finset.sum_product Finset.univ Finset.univ (fun x : Fin 499 × Fin J => fastCell x.1.val x.2.val),
    Finset.univ_product_univ]
  calc
    _ = ∑ x : Fin 499 × Fin J, tailSaving (windowEmbed hJ x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [fastCell_eq x.1.isLt (LT.lt.trans_le x.2.isLt hJ)]
      simp only [valueRowCell, dite_eq_left x.1.isLt, dite_eq_left (LT.lt.trans_le x.2.isLt hJ)]
      rfl
    _ ≤ _ := sum_embed_le (windowEmbed hJ) tailSaving


open K1_13_2_3_7 (countParts natKernel)
open K1_13_2_3_7 (countParts_eq partValue natKernel_signed)

def natOld (d j : ℕ) : ℕ :=
  let hi := countParts d 1651
  let lo := countParts d (1650 - j)
  hi.1 + lo.2 - (hi.2 + lo.1)

private theorem old_eq (d j : ℕ) :
    natOld d j = (fastCum d 1650 - fastCum d (1649 - (j : ℤ))).toNat := by
  have hi := countParts_eq d 1650
  have lo := countParts_eq d (1649 - (j : ℤ))
  change partValue (countParts d 1651) = _ at hi
  rw [show (1649 - (j : ℤ) + 1).toNat = 1650 - j by omega] at lo
  unfold partValue at hi lo
  simp only [natOld]
  omega

def removed (d q : ℕ) : ℕ := (3003 + d - q) / 4

private theorem natKernel_eq_for (d q j : ℕ) (hq : 3514 ≤ q) (hj : q + j < 4650)
    (hD : d ≤ 1650) :
    natKernel d j (4650 - q - j) (removed d q) =
      (signedKernel d j (4649 - (q : ℤ) - j)).toNat := by
  let h := 4650 - q - j
  have hh : (h : ℤ) - 1 = 4649 - (q : ℤ) - j := by dsimp [h]; omega
  rw [← hh]
  have hb : (h : ℤ) - 1 - (1650 - j) + d = 2999 + (d : ℤ) - q := by omega
  apply natKernel_signed
  · unfold removed; omega
  · rw [hb]; unfold removed; omega
  · intro hr
    rw [hb, min_eq_right (by omega)]
    unfold removed at *
    omega

def rankNat (d q j p : ℕ) : ℕ :=
  if q + j < 4650 then
    let h := 4650 - q - j
    natOld d j - max (natKernel d j h (removed d q))
      (natKernel (d - p) j h (removed (d - p) q))
  else 0

theorem rankNat_eq (d q j p : ℕ) (hq : 3514 ≤ q) (hD : d ≤ 1650) (hp : p ≤ d) :
    rankNat d q j p = fastRank d j (4649 - (q : ℤ) - j) p := by
  unfold rankNat fastRank
  by_cases hj : q + j < 4650
  · rw [ite_eq_left hj, ite_eq_right (by omega)]
    simp only
    rw [old_eq, natKernel_eq_for d q j hq hj hD,
      natKernel_eq_for (d-p) q j hq hj (by omega), Nat.cast_sub hp]
    omega
  · rw [ite_eq_right hj, ite_eq_left (by omega)]

def natCell (t j : ℕ) : ℕ :=
  let q := 3514 + t
  let d := cap q
  rankNat 1650 q j 0 - rankNat d q j (valuePower d q j)

theorem natCell_eq (t j : ℕ) : natCell t j = fastCell t j := by
  have hd : cap (3514 + t) ≤ 1650 := by unfold cap; split <;> omega
  have hp : valuePower (cap (3514+t)) (3514+t) j ≤ cap (3514+t) := min_le_left _ _
  unfold natCell fastCell
  simp only
  rw [rankNat_eq 1650 (3514+t) j 0 (by omega) (by decide) (by decide),
    rankNat_eq (cap (3514+t)) (3514+t) j _ (by omega) hd hp]
  push_cast
  rw [show (4649 : ℤ) - (3514 + t) - j = 1135 - t - j by omega]



def sumChunk (f : ℕ → ℕ) (lo n : ℕ) : ℕ :=
  sumRange (fun i => f (lo + i)) n

theorem sumChunk_add (f : ℕ → ℕ) (lo n m : ℕ) :
    sumChunk f lo (n + m) = sumChunk f lo n + sumChunk f (lo+n) m := by
  induction m with
  | zero => simp [sumChunk,sumRange]
  | succ m ih =>
      rw [Nat.add_succ]
      change sumChunk f lo (n+m) + f (lo+(n+m)) =
        sumChunk f lo n + (sumChunk f (lo+n) m + f ((lo+n)+m))
      rw [ih]
      simp only [Nat.add_assoc]

def rowSum (J t : ℕ) : ℕ := sumRange (natCell t) J

theorem sumChunk_eq_fastSavings (J : ℕ) : sumChunk (rowSum J) 0 499 = fastSavings J := by
  unfold sumChunk fastSavings rowSum
  simp only [sumRange_eq, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact natCell_eq _ _

open K1_13_2_3 (combine baseline_budget_on sum_add_pointwise_eq bound_le_baseline savings_parts)

def fees (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if i.1.val < 3514 then blockBound i (combine p₁ p₂ p₃ (fun _ => ⟨0,0,0⟩) i).expand
  else min (baseline i) (TaperNormalize.bound (cap i.1.val) i (power i))

theorem fees_le_baseline (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) :
    fees p₁ p₂ p₃ i ≤ baseline i := by
  unfold fees
  split
  · exact bound_le_baseline _ _
  · exact min_le_left _ _



private abbrev zeroPowers : BlockIndex → Powers := fun _ => ⟨0,0,0⟩

private theorem saved_pointwise (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) :
    savings i (combine p₁ p₂ p₃ zeroPowers i) + tailSaving i ≤ baseline i - fees p₁ p₂ p₃ i := by
  by_cases hi : i.1.val < 3514
  · simp [fees, tailSaving, hi, show ¬3514 ≤ i.1.val by omega, savings]
  · have h₁ : ¬i.1.val < 2008 := by omega
    have h₂ : ¬i.1.val < 3012 := by omega
    simp only [combine, h₁, h₂, hi, ite_false, zeroPowers, savings, power_zero, show blockBound i (fun _ => 0) = baseline i by rfl,
      Nat.sub_self, Nat.zero_add, fees, tailSaving, show 3514 ≤ i.1.val by omega, ite_true]
    exact Nat.sub_le_sub_left (min_le_right _ _) _

private theorem saved_on (S : Finset BlockIndex) (p₁ p₂ p₃ : BlockIndex → Powers) :
    (∑ i ∈ S, savings i (combine p₁ p₂ p₃ zeroPowers i)) + (∑ i ∈ S, tailSaving i) ≤
      ∑ i ∈ S, (baseline i - fees p₁ p₂ p₃ i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum (s := S)
  intro i _
  exact saved_pointwise p₁ p₂ p₃ i

theorem saved_by_fees (p₁ p₂ p₃ : BlockIndex → Powers) :
    savingsSum w1 p₁ + savingsSum w2 p₂ + savingsSum w3 p₃ + (∑ i : BlockIndex, tailSaving i) ≤
      ∑ i : BlockIndex, (baseline i - fees p₁ p₂ p₃ i) := by
  have h₀ : savingsSum w4 zeroPowers = 0 := by
    unfold savingsSum
    apply Finset.sum_eq_zero
    intro i _
    simp [zeroPowers, savings, power_zero, baseline]
  have h := savings_parts p₁ p₂ p₃ zeroPowers
  rw [h₀, Nat.add_zero] at h
  exact (Nat.add_le_add_right h _).trans (saved_on Finset.univ p₁ p₂ p₃)


end TaperBudget

end Merged_PrimaryTaperBudget

end Merged6967_PrimaryTaperBudget

section Merged6967_R6966ProofRawPhysicalDegree
set_option Elab.async false



set_option Elab.async false

namespace Research6966.RawPhysicalDegree
open Polynomial
open scoped Polynomial
noncomputable section

variable {k : Type*} [Field k]
private abbrev Jets (k : Type*) [Semiring k] := k[X][X]
private abbrev Raw (k : Type*) [Semiring k] := k[X][X][X]

/-- The outer indeterminate records physical weight. Two independent tags in
the coefficient ring retain the ordinate and slope positions. -/
def encode (u v : ℕ) : Raw k →+* (Jets k)[X] :=
  let c : k →+* Jets k := C.comp C
  let phys : k[X] →+* (Jets k)[X] := mapRingHom c
  let y : (Jets k)[X] := monomial u (monomial 0 (monomial 1 (1:k)))
  let slope : (Jets k)[X] := monomial v (monomial 1 (monomial 0 (1:k)))
  eval₂RingHom (eval₂RingHom phys y) slope

private theorem encode_term (u v j i a : ℕ) (c : k) :
    encode u v (monomial j (monomial i (monomial a c))) =
      monomial (a+u*i+v*j) (monomial j (monomial i c)) := by
  simp only [encode,coe_eval₂RingHom,eval₂_monomial,coe_mapRingHom,map_monomial,
    RingHom.comp_apply,←monomial_zero_left,monomial_pow,monomial_mul_monomial,
    zero_mul,one_mul,one_pow,mul_one,zero_add,add_zero]

theorem coeff_encode (u v : ℕ) (P : Raw k) (n j i : ℕ) :
    (((encode u v P).coeff n).coeff j).coeff i =
      if u*i+v*j≤n then (((P.coeff j).coeff i).coeff (n-(u*i+v*j))) else 0 := by
  classical
  induction P using Polynomial.induction_on' with
  | add F G hF hG =>
    simp only [map_add,coeff_add,hF,hG];split <;> simp
  | monomial l F =>
    induction F using Polynomial.induction_on' with
    | add F G hF hG =>
      simp only [map_add,coeff_add,hF,hG];split <;> simp
    | monomial m F =>
      induction F using Polynomial.induction_on' with
      | add F G hF hG =>
        simp only [map_add,coeff_add,hF,hG];split <;> simp
      | monomial b c =>
        rw [encode_term]
        by_cases hj : l=j
        · subst l
          by_cases hi : m=i
          · subst m
            by_cases eq : b+u*i+v*j=n
            · subst n;simp [coeff_monomial,show u*i+v*j≤b+u*i+v*j by omega,
                            show b+u*i+v*j-(u*i+v*j)=b by omega]
            · by_cases le : u*i+v*j≤n
              · have ne : b≠n-(u*i+v*j) := by omega
                simp [coeff_monomial,eq,le,ne]
              · simp [coeff_monomial,eq,le]
          · by_cases t : b+u*m+v*j=n <;> simp [coeff_monomial,hi,t]
        · by_cases t : b+u*m+v*l=n <;> simp [coeff_monomial,hj,t]

theorem encode_injective (u v : ℕ) : Function.Injective (encode (k:=k) u v) := by
  intro F G eq
  ext j i a
  have converted:=congrArg (fun p : (Jets k)[X] => ((p.coeff (a+u*i+v*j)).coeff j).coeff i) eq
  simpa only [coeff_encode,ite_eq_left (show u*i+v*j≤a+u*i+v*j by omega),
    show a+u*i+v*j-(u*i+v*j)=a by omega] using converted

def weight (u v : ℕ) (P : Raw k) := (encode u v P).natDegree

theorem bounded_iff (u v W : ℕ) (P : Raw k) :
    K1_14_1_4.Bounded u v W P ↔ weight u v P≤W := by
  constructor
  · intro h
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    ext j i
    rw [coeff_encode]
    split
    · rename_i hw
      by_contra ne
      have nonzero : ((P.coeff j).coeff i).coeff (n-(u*i+v*j))≠0 := by simpa using ne
      have := h j i _ nonzero
      omega
    · simp
  · intro h j i a nonzero
    by_contra! larger
    have vanish:=coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h larger)
    have z := congrArg (fun q:Jets k => (q.coeff j).coeff i) vanish
    apply nonzero
    simpa only [coeff_encode,ite_eq_left (show u*i+v*j≤a+u*i+v*j by omega),
      show a+u*i+v*j-(u*i+v*j)=a by omega,coeff_zero] using z

theorem weight_product (u v : ℕ) {F G : Raw k} (f:F≠0) (g:G≠0) :
    weight u v (F*G)=weight u v F+weight u v G := by
  simp only [weight,map_mul,natDegree_mul
    ((map_ne_zero_iff _ (encode_injective u v)).mpr f)
    ((map_ne_zero_iff _ (encode_injective u v)).mpr g)]

/-- Paying the primitive graph's weight at every forced division shrinks the
actual raw quotient. This conclusion is for integral raw rows. -/
theorem quotient_cap (u v W t : ℕ) {F G Q : Raw k} (nz : F≠0) (eq : F=G^t*Q)
    (bounded : K1_14_1_4.Bounded u v W F) :
    K1_14_1_4.Bounded u v (W-t*weight u v G) Q := by
  have prod : G^t*Q≠0 := eq ▸ nz
  have cap := (bounded_iff u v W F).mp bounded
  rw [eq,weight_product u v (left_ne_zero_of_mul prod) (right_ne_zero_of_mul prod)] at cap
  have power:weight u v (G^t)=t*weight u v G := by simp [weight,natDegree_pow]
  rw [power] at cap
  apply (bounded_iff ..).mpr
  omega

#print axioms bounded_iff
#print axioms quotient_cap

/-- The complete integral bank pays the full raw weight of a graph factor
after clearing the two CRT poles. -/
theorem complete_graph_quotient {h : ℕ} (hpos : 0<h) (hh : h≤131070)
    {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D) (word : K1.I→K1_14.L)
    {s W P} (mem : P∈K1_14_1.complete Crt word s W) (G Q : K1_14_1.RawSource) (t : ℕ)
    (gn : G≠0)
    (exact_div : K1_14_1.forward Crt P =
      K1_14_1.jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)) * (G^t*Q)) :
    K1_14_1_4.Bounded (131071-h) (131071-h-1)
      (W-t*weight (131071-h) (131071-h-1) G) Q := by
  obtain ⟨R,eq,bounded⟩:=P0_10_1.complete_raw_bounded hpos hh Crt word mem
  have pole : K1_14_1.jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)) ≠ 0 := by
    exact C_ne_zero.mpr (C_ne_zero.mpr ((K1_14_1_4.rawBlock_monic D).pow _).ne_zero)
  have desc := mul_left_cancel₀ pole (eq.symm.trans exact_div)
  by_cases zero : Q=0
  · subst Q;intro j i a ne;simp at ne
  · have rn : R≠0 := desc ▸ mul_ne_zero (pow_ne_zero _ gn) zero
    exact quotient_cap _ _ _ _ rn desc bounded

#print axioms complete_graph_quotient
end
end Research6966.RawPhysicalDegree

end Merged6967_R6966ProofRawPhysicalDegree

section Merged6967_KoalaRetainedCut
set_option Elab.async false



set_option Elab.async false

set_option autoImplicit false
set_option Elab.async false

namespace KoalaRetainedCut
noncomputable section

open K1_13 (Row Geom Shape shape InBox jet shiftJet atJet OrderAt indexDegree)
open MvPolynomial
open scoped Polynomial

/-- Total Taylor order at the jet of the specified scalar polynomial. -/
def contactOrder (P : Row 4) (S : (Polynomial Geom)) : ℕ∞ :=
  ((shiftJet P S : Row 4) : MvPowerSeries (Fin 4) (Polynomial Geom)).order

theorem orderAt_iff {P : Row 4} {S : (Polynomial Geom)} {d : ℕ} :
    OrderAt P S d ↔ (d : ℕ∞) ≤ contactOrder P S := by
  constructor
  · intro h
    apply MvPowerSeries.nat_le_order
    intro m hm
    rw [MvPolynomial.coeff_coe]
    by_contra hnon
    have hle := h m (MvPolynomial.mem_support_iff.mpr hnon)
    change d ≤ Finsupp.degree m at hle
    exact (Nat.not_lt_of_ge hle hm)
  · intro h m hm
    have he : MvPowerSeries.coeff m ((shiftJet P S : Row 4) :
        MvPowerSeries (Fin 4) (Polynomial Geom)) ≠ 0 := by
      rw [MvPolynomial.coeff_coe]
      exact MvPolynomial.mem_support_iff.mp hm
    exact_mod_cast h.trans (MvPowerSeries.order_le he)

private def shifting (S : (Polynomial Geom)) : Row 4 →+* Row 4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))

theorem contactOrder_mul (H G : Row 4) (S : (Polynomial Geom)) :
    contactOrder (H*G) S = contactOrder H S + contactOrder G S := by
  unfold contactOrder
  change ((shifting S (H*G) : Row 4) : MvPowerSeries (Fin 4) (Polynomial Geom)).order = _
  rw [map_mul,MvPolynomial.coe_mul,MvPowerSeries.order_mul]
  rfl

theorem contactOrder_off {H : Row 4} {S : (Polynomial Geom)} (h : atJet H S ≠ 0) :
    contactOrder H S = 0 := by
  have het : (shiftJet H S).coeff 0 = atJet H S := by
    change (MvPolynomial.constantCoeff.comp (shifting S)) H = MvPolynomial.eval (jet S) H
    congr 1
    ext <;> simp [shifting]
  have hc : MvPowerSeries.coeff 0 ((shiftJet H S : Row 4) :
      MvPowerSeries (Fin 4) (Polynomial Geom)) ≠ 0 := by simpa only [MvPolynomial.coeff_coe,het] using h
  change ((shiftJet H S : Row 4) : MvPowerSeries (Fin 4) (Polynomial Geom)).order = 0
  exact le_bot_iff.mp (by simpa using MvPowerSeries.order_le hc)

theorem contactOrder_pow (H : Row 4) (S : (Polynomial Geom)) (v : ℕ) :
    contactOrder (H^v) S = v * contactOrder H S := by
  induction v with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, contactOrder_off]
    simp [atJet]
  | succ v ih =>
    rw [pow_succ,contactOrder_mul,ih,Nat.cast_succ,add_mul,one_mul]

/-- At a scalar with Taylor multiplicity at most e, division costs at most e per factor. -/
theorem orderAt_quotient {H G : Row 4} {S : (Polynomial Geom)} {v e k : ℕ}
    (he : contactOrder H S ≤ (e : ℕ∞)) (h : OrderAt (H^v*G) S k) :
    OrderAt G S (k-v*e) := by
  rw [orderAt_iff,contactOrder_mul,contactOrder_pow] at h
  rw [orderAt_iff]
  have hle := h.trans (add_le_add_left (mul_le_mul_right he (v : ℕ∞)) _)
  by_cases htop : contactOrder G S = ⊤
  · simp [htop]
  · obtain ⟨g,hg⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hg] at hle ⊢
    have hk : k ≤ v*e+g := by exact_mod_cast hle
    exact_mod_cast (by omega : k-v*e ≤ g)

theorem orderAt_off_quotient {H G : Row 4} {S : (Polynomial Geom)} {v k : ℕ}
    (hoff : atJet H S ≠ 0) (h : OrderAt (H^v*G) S k) : OrderAt G S k := by
  simpa using orderAt_quotient (e := 0) (le_of_eq (contactOrder_off hoff)) h

#print axioms orderAt_quotient
#print axioms orderAt_off_quotient

end
end KoalaRetainedCut

end Merged6967_KoalaRetainedCut

section Merged6967_R6966ListBridge
set_option Elab.async false



set_option Elab.async false

/-! M6 bridge: dadon's paired Curve-Johnson list (module family `Dd*`), regenerated at
A = 179759, Lambda = 51967810913705, is exactly our `CJ0.ScalarList`. -/

namespace R6966ListBridge

theorem scalar_list : CJ0.ScalarList 179759 51967810913705 :=
  P6_8.of_children P6_8_1.proof P6_8_2.proof

#print axioms scalar_list
end R6966ListBridge

end Merged6967_R6966ListBridge
