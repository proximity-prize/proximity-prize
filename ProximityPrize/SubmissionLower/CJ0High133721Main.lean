import ProximityPrize.SubmissionLower.CJ0High133721
import ProximityPrize.SubmissionLower.ShortenChart
import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# Case-B `StructuralList` / Order-Two Counting Theorem at `kHigh = 133,721` (`CJ0High133721Main`)

Lifts the full sharpened `StructuralList` counting pipeline (`ShortenChart` + `ScalarCutCapacity` +
`CJ0_4` + `CJ0_5` + `CJ0_6` + `CJ0_7` + `CJ0_8`) from `CJ0.k = 131,072` (`N = 131,071`) to
`kHigh = 133,721` (`NHigh = 133,720`), covering all polynomials of degree `≤ 131,071 + 2,649`
on the split lower-high band `h ∈ [2302, 2649]` at `69.63` (`A = 179,798`).

Main results:
1. `shortenChart_high`: shortened order-2 charts at `kHigh = 133,721`.
2. `cutCap_high`: evaluation-section capacity bound for order-2 surface charts at `kHigh = 133,721`.
3. `order_two_card_le_high133721`: any finite set `T ⊆ closeHigh A w` of degree-`< 133,721`
   polynomials annihilated by a nonzero order-2 differential polynomial `Q` of box shape `s`
   satisfies `T.card ≤ tariffHigh A s`.
4. `caseB_six_rects_card_le_6963`: concrete cardinality caps (`≤ 44.89e15`) for all 6 small
   Case-B Rescue rectangles at `69.63` (`A = 179,798`).
-/

namespace CJ0High133721

noncomputable section

open CJ0 Polynomial PolynomialDifferential MvPolynomial Finset Filter
open scoped BigOperators
open K1_14_6 (occupancy curve_degree_nat)
open P0_10 (incidence_arithmetic)
open K1_13_5_4_2 (ratio_image_degree)

/-! ## Section 1: Degree-`< 133,721` Geometry, Charts, and Capacity Bounds -/

abbrev closeHigh (A : ℕ) (w : Node → K) :=
  ReedSolomon.closePolynomialSet node w kHigh A

def boxToSource (b : BoxShape) : CJ0.Source :=
  ⟨1, b.B, b.J, b.C, CJ0.fullBox b.B b.J b.C⟩

abbrev OrderTwoHigh (b : BoxShape) (Q : DifferentialPolynomial K 2) : Prop :=
  CJ0.OrderTwo (boxToSource b) Q

abbrev OrderOneHigh (b : BoxShape) (Q : DifferentialPolynomial K 1) : Prop :=
  CJ0.OrderOne (boxToSource b) Q

theorem boxToSource_shapeOK (b : BoxShape) (hb : BoxOK b) : CJ0.ShapeOK (boxToSource b) where
  multiplicity := Nat.zero_lt_one
  top_pos := hb.top_pos
  index_top := by dsimp [boxToSource]; have := hb.index_top; omega
  total_index := hb.total_index
  characteristic := by
    have hc := hb.characteristic
    have hle : max CJ0.N (b.B * (b.B - 1)) ≤ max NHigh (b.B * (b.B - 1)) :=
      max_le_max_right _ (by decide)
    exact hle.trans_lt hc
  support := by
    intro j hj
    dsimp [boxToSource] at hj ⊢
    exact (CJ0.mem_fullBox hb.total_index (by have := hb.index_top; omega) j).mp hj
  lower := by
    intro j hj ha
    dsimp [boxToSource] at hj ⊢
    have hmem := (CJ0.mem_fullBox hb.total_index (by have := hb.index_top; omega) j).mp hj
    rw [CJ0.mem_fullBox hb.total_index (by have := hb.index_top; omega)]
    rcases j with ⟨c, b', a⟩
    simp only [Jet.q, Jet.v, Jet.c, Jet.b, Jet.a] at hmem ha ⊢
    omega

abbrev CoeffRingHigh := MvPolynomial (Fin kHigh) Geo

def coeffPointHigh (f : Polynomial K) (i : Fin kHigh) : Geo :=
  embed (f.coeff i.val)

def readJetHigh (y : Fin kHigh → Geo) (j : ℕ) : Geo :=
  ∑ i : Fin kHigh, (i.val.choose j : Geo) * center ^ (i.val - j) * y i

structure ChartHigh (r : ℕ) where
  equation : InitialRing r
  denominator : InitialRing r
  numerator : Fin kHigh → InitialRing r

def ChartHigh.locus {r : ℕ} (T : ChartHigh r) : Set (Fin (r + 1) → Geo) :=
  {u | MvPolynomial.eval u T.equation = 0 ∧ MvPolynomial.eval u T.denominator ≠ 0}

def ChartHigh.output {r : ℕ} (T : ChartHigh r) (u : Fin (r + 1) → Geo) (i : Fin kHigh) : Geo :=
  MvPolynomial.eval u (T.numerator i) / MvPolynomial.eval u T.denominator

def ChartHigh.imageSet {r : ℕ} (T : ChartHigh r) : Set (Fin kHigh → Geo) :=
  T.output '' T.locus

def ChartHigh.ideal {r : ℕ} (T : ChartHigh r) : Ideal CoeffRingHigh :=
  MvPolynomial.vanishingIdeal Geo T.imageSet

structure ChartOKHigh {r : ℕ} (T : ChartHigh r) : Prop where
  irreducible : Irreducible T.equation
  nonvanishing : ¬ T.equation ∣ T.denominator
  recover : ∀ u ∈ T.locus, ∀ j : Fin (r + 1), readJetHigh (T.output u) j.val = u j

structure FamilyHigh (r : ℕ) where
  count : ℕ
  chart : Fin count → ChartHigh r

def InBandHigh (s : BoxShape) (length : ℕ) (P : InitialRing 2) : Prop :=
  P.totalDegree ≤ totalCap s length ∧
  P.weightedTotalDegree Fin.val ≤ indexCap s length ∧
  P.degreeOf (Fin.last 2) ≤ topCap s length

structure ShortBandHigh (s : BoxShape) (length : ℕ) (T : ChartHigh 2) : Prop where
  denominator : InBandHigh s length T.denominator
  numerator : ∀ i : Fin kHigh, InBandHigh s length (T.numerator i)

def inBand1High (s : BoxShape) (P : InitialRing 1) : Prop :=
  P.totalDegree ≤ a1High s ∧ P.degreeOf (Fin.last 1) ≤ d1High s

structure Family1High (s : BoxShape) (F : FamilyHigh 1) : Prop where
  count : F.count ≤ HHigh s
  chart_ok : ∀ i, ChartOKHigh (F.chart i)
  total : (∑ i, (F.chart i).equation.totalDegree) ≤ HHigh s
  index : (∑ i, (F.chart i).equation.degreeOf (Fin.last 1)) ≤ I1High s
  bands : ∀ i, inBand1High s (F.chart i).denominator ∧ ∀ j, inBand1High s ((F.chart i).numerator j)

structure ImageDegreesHigh {r : ℕ} (F : FamilyHigh r) (budget : ℕ) : Prop where
  prime : ∀ i, (F.chart i).ideal.IsPrime
  dimension : ∀ i, (MvPolynomial.affineHilbertPolynomial (F.chart i).ideal).natDegree = r
  total : (∑ i, MvPolynomial.affineDegree (F.chart i).ideal) ≤ (budget : ℚ)

private theorem section_capacity_high {A : ℕ} {w : Node → K} {T : Finset (Polynomial K)}
    (h : (T : Set (Polynomial K)) ⊆ closeHigh A w) (hA : AgreementOKHigh A) (cap : ℕ)
    (hsection : ∀ i : Node, (∃ γ ∈ T, γ.eval (node i) ≠ w i) →
      (T.filter fun γ => γ.eval (node i) = w i).card ≤ cap) :
    gapHigh A * T.card ≤ errorsHigh A * cap + gapHigh A := by
  classical
  have hd := hA.gt_degree
  have hn := hA.lt_length
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (gapHigh A) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : Polynomial K) : Finset Node := univ.filter fun i => γ.eval (node i) = w i
  let common : Finset Node := univ.filter fun i => ∀ γ ∈ T, γ.eval (node i) = w i
  let nodes : Finset Node := univ \ common
  have common_le (γ : Polynomial K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : Polynomial K) (hγ : γ ∈ T) : A ≤ (hits γ).card := (h hγ).2
  have degree (a : Polynomial K) (ha : a ∈ T) : a.natDegree ≤ NHigh := by
    by_cases hz : a = 0
    · simp [hz]
    · have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hz).2 (h ha).1
      exact Nat.le_of_lt_succ hdeg
  have pair_count (a : Polynomial K) (ha : a ∈ T) (b : Polynomial K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ NHigh := by
    refine (FrobeniusLocator.Strata.root_nodes_card_le node node.injective
      (a - b) (sub_ne_zero.mpr hab) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (degree a ha) (degree b hb)))
    intro i hi
    change (a - b).eval (node i) = 0
    rw [Polynomial.eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ NHigh :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := A - common.card
  let t := NHigh - common.card
  have ht : t = x - gapHigh A := by dsimp [t, x, gapHigh]; omega
  have hx : gapHigh A ≤ x := by dsimp [x, gapHigh]; omega
  have hnodes : nodes.card = x + errorsHigh A := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ,
      ProximityPrize.Benchmark.IRSProfile.card_index]
    change nHigh - common.card = (A - common.card) + (nHigh - A)
    have hbound := hcommon.trans hd.le
    omega
  have exists_trim (γ : Polynomial K) :
      ∃ B : Finset Node, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
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
  have into_nodes (γ : Polynomial K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : Polynomial K) (ha : a ∈ T) (b : Polynomial K) (hb : b ∈ T) (hab : a ≠ b) :
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
    have hi' : i ∈ hits γ := (mem_sdiff.mp ((hB γ hγ).1 hi)).1
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp hi').2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic (errorsHigh A) _ _ _ _ (by omega)
    (Nat.sub_pos_of_lt hd) hx (Nat.sub_pos_of_lt hn) second first

def valueCutHigh (x a : K) : CoeffRingHigh :=
  (∑ i : Fin kHigh, MvPolynomial.C (embed x ^ i.val) * MvPolynomial.X i) - MvPolynomial.C (embed a)

theorem valueCutHigh_degree (x a : K) : (valueCutHigh x a).totalDegree ≤ 1 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply totalDegree_finsetSum_le
  intro i _
  simpa only [totalDegree_C, totalDegree_X, zero_add] using
    (totalDegree_mul (MvPolynomial.C (embed x ^ i.val)) (MvPolynomial.X i))

private theorem natDegree_bound_high {f : Polynomial K} (h : f.degree < kHigh) :
    f.natDegree < kHigh := by
  by_cases hz : f = 0
  · rw [hz, Polynomial.natDegree_zero]
    exact Nat.zero_lt_succ _
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 h

theorem valueCutHigh_eval {f : Polynomial K} (h : f.degree < kHigh) (x a : K) :
    MvPolynomial.aeval (coeffPointHigh f) (valueCutHigh x a) = 0 ↔ f.eval x = a := by
  have heval : f.eval x = ∑ j : Fin kHigh, f.coeff j.val * x ^ j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => f.coeff j * x ^ j)]
    exact Polynomial.eval_eq_sum_range' (natDegree_bound_high h) x
  have hmap : embed (∑ j : Fin kHigh, f.coeff j.val * x ^ j.val) =
      ∑ j : Fin kHigh, embed x ^ j.val * embed (f.coeff j.val) := by
    rw [map_sum]
    exact sum_congr rfl fun _ _ => by rw [map_mul, map_pow, mul_comm]
  simp only [valueCutHigh, coeffPointHigh, map_sub, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, sub_eq_zero, Algebra.algebraMap_self_apply]
  rw [heval, ← hmap]
  exact embed.injective.eq_iff

private theorem coeffPointHigh_injOn {A w} {Γ : Finset (Polynomial K)}
    (h : (Γ : Set (Polynomial K)) ⊆ closeHigh A w) :
    Set.InjOn coeffPointHigh (Γ : Set (Polynomial K)) := by
  intro f hf g hg heq
  apply Polynomial.ext
  intro j
  by_cases hj : j < kHigh
  · exact embed.injective (congrFun heq ⟨j, hj⟩)
  · have hfj := (natDegree_bound_high (h hf).1).trans_le (Nat.le_of_not_gt hj)
    have hgj := (natDegree_bound_high (h hg).1).trans_le (Nat.le_of_not_gt hj)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hfj, Polynomial.coeff_eq_zero_of_natDegree_lt hgj]

private theorem zeroDim_count_high {A w} {Γ : Finset (Polynomial K)}
    (h : (Γ : Set (Polynomial K)) ⊆ closeHigh A w) (P : Ideal CoeffRingHigh)
    (hdim : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ Γ, coeffPointHigh γ ∈ zeroLocus Geo P) :
    (Γ.card : ℚ) ≤ affineDegree P := by
  classical
  let Im := Γ.image coeffPointHigh
  have hIm : Im.card = Γ.card := card_image_of_injOn (coeffPointHigh_injOn h)
  have hsub : (Im : Set _) ⊆ zeroLocus Geo P := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := Geo) P hdim
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hIm] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree

private theorem section_count_high {A w} {Γ : Finset (Polynomial K)}
    (h : (Γ : Set (Polynomial K)) ⊆ closeHigh A w) {P : Ideal CoeffRingHigh}
    (hP : P.IsPrime) (hpoints : ∀ γ ∈ Γ, coeffPointHigh γ ∈ zeroLocus Geo P)
    (x a : K) (hmiss : ∃ γ ∈ Γ, γ.eval x ≠ a)
    {c : ℚ} (hc : 0 ≤ c)
    (bound : ∀ (V : Finset (Polynomial K)), V ⊆ Γ → ∀ (Q : Ideal CoeffRingHigh), Q.IsPrime →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, coeffPointHigh γ ∈ zeroLocus Geo Q) →
      (V.card : ℚ) ≤ c * affineDegree Q) :
    ((Γ.filter fun γ => γ.eval x = a).card : ℚ) ≤ c * affineDegree P := by
  classical
  let _ := hP
  let cut := valueCutHigh x a
  let Ps := (P ⊔ Ideal.span {cut}).minimalPrimesFinset
  let U := Γ.filter fun γ => γ.eval x = a
  let part (Q : Ideal CoeffRingHigh) := U.filter fun f => coeffPointHigh f ∈ zeroLocus Geo Q
  have hproper : cut ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hm
    exact hv ((valueCutHigh_eval (h hγ).1 x a).mp (hpoints γ hγ _ hm))
  have hcover : U ⊆ Ps.biUnion part := by
    intro γ hγ
    obtain ⟨hγΓ, hv⟩ := mem_filter.mp hγ
    have hp : coeffPointHigh γ ∈ zeroLocus Geo (P ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ, (valueCutHigh_eval (h hγΓ).1 x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact mem_biUnion.mpr ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  have hsum : U.card ≤ ∑ Q ∈ Ps, (part Q).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hdeg : (∑ Q ∈ Ps, affineDegree Q) ≤ affineDegree P := by
    simpa only [Ps, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCutHigh_degree x a)
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

theorem curve_capacity_high {A w} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w)
    (hA : AgreementOKHigh A) {P : Ideal CoeffRingHigh} (hp : P.IsPrime)
    (hd : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ f ∈ T, coeffPointHigh f ∈ zeroLocus Geo P) :
    ((gapHigh A : ℕ) : ℚ) * T.card ≤ (errorsHigh A : ℚ) * affineDegree P + gapHigh A ∧
    (T.card : ℚ) ≤ 2 * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hp hd
  have hcap := section_capacity_high hT hA δ fun i hi => by
    have hc := section_count_high hT hp hpoints (node i) (w i) hi (c := 1) zero_le_one
      (fun _ hV Q _ hdim hpts => by
        rw [one_mul]
        exact zeroDim_count_high (fun _ hf => hT (hV hf)) Q (by omega) hpts)
    rw [one_mul, hdeg] at hc
    exact_mod_cast hc
  rw [hdeg]
  refine ⟨by exact_mod_cast hcap, ?_⟩
  suffices hn : T.card ≤ 2 * δ by exact_mod_cast hn
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left (gapHigh A) (show 2 * δ + 1 ≤ T.card by omega)
  rw [Nat.mul_add, Nat.mul_one] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hA.beta_lt_two hδ
  rw [mul_comm 2 (gapHigh A), mul_assoc] at hstrict
  omega

theorem family1_capacity_high {A w budget} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w)
    (hA : AgreementOKHigh A) (F : FamilyHigh 1) (hg : ImageDegreesHigh F budget)
    (hcover : ∀ f ∈ T, ∃ i, coeffPointHigh f ∈ (F.chart i).imageSet) :
    (gapHigh A : ℚ) * T.card ≤ (errorsHigh A : ℚ) * (budget : ℚ) + (gapHigh A : ℚ) * F.count := by
  classical
  let part (i : Fin F.count) := T.filter fun f => coeffPointHigh f ∈ (F.chart i).imageSet
  have hc : T.card ≤ ∑ i, (part i).card := by
    apply (card_le_card (t := univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i, hi⟩ := hcover f hf
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hf, hi⟩⟩
  have hone (i : Fin F.count) : (gapHigh A : ℚ) * (part i).card ≤
      (errorsHigh A : ℚ) * affineDegree (F.chart i).ideal + gapHigh A := by
    have hsub : (part i : Set (Polynomial K)) ⊆ closeHigh A w := fun _ hf => hT (mem_filter.mp hf).1
    have hp : ∀ f ∈ part i, coeffPointHigh f ∈ zeroLocus Geo (F.chart i).ideal :=
      fun _ hf => zeroLocus_vanishingIdeal_le _ (mem_filter.mp hf).2
    exact (curve_capacity_high hsub hA (hg.prime i) (hg.dimension i) hp).1
  have hq : (T.card : ℚ) ≤ ∑ i, ((part i).card : ℚ) := by exact_mod_cast hc
  calc
    _ ≤ (gapHigh A : ℚ) * ∑ i, ((part i).card : ℚ) :=
      mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    _ = ∑ i, (gapHigh A : ℚ) * (part i).card := mul_sum ..
    _ ≤ _ := sum_le_sum fun i _ => hone i
    _ = (errorsHigh A : ℚ) * (∑ i, affineDegree (F.chart i).ideal) + (gapHigh A : ℚ) * F.count := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin,
        mul_comm (F.count : ℚ)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hg.total (Nat.cast_nonneg _)) le_rfl

/-! ## Section 2: Chart Image Geometry and Degree Bounds (`CJ0_4` at `kHigh`) -/

def sourceIdealHigh {r : ℕ} (T : ChartHigh r) : Ideal (InitialRing r) :=
  Ideal.span {T.equation}

def quotientBandHigh (T : ChartHigh 2) (a d e : ℕ) :
    Submodule Geo (InitialRing 2 ⧸ sourceIdealHigh T) :=
  (CJ0_4.bandSpace a d e).map (Ideal.Quotient.mkₐ Geo (sourceIdealHigh T)).toLinearMap

private theorem quotientBandHigh_mono (T : ChartHigh 2) {a d e a' d' e' : ℕ}
    (ha : a ≤ a') (hd : d ≤ d') (he : e ≤ e') :
    quotientBandHigh T a d e ≤ quotientBandHigh T a' d' e' :=
  Submodule.map_mono (CJ0_4.bandSpace_mono ha hd he)

local instance (T : ChartHigh 2) (a d e : ℕ) : Module.Finite Geo (quotientBandHigh T a d e) := by
  unfold quotientBandHigh
  infer_instance

abbrev ChartOpenHigh {r : ℕ} (T : ChartHigh r) :=
  Localization.Away (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)

def localizeHigh {r : ℕ} (T : ChartHigh r) : InitialRing r →ₐ[Geo] ChartOpenHigh T :=
  (IsScalarTower.toAlgHom Geo (InitialRing r ⧸ sourceIdealHigh T) (ChartOpenHigh T)).comp
    (Ideal.Quotient.mkₐ Geo (sourceIdealHigh T))

def invDenomHigh {r : ℕ} (T : ChartHigh r) : ChartOpenHigh T :=
  IsLocalization.Away.invSelf (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)

theorem denom_mul_inv_high {r : ℕ} (T : ChartHigh r) :
    localizeHigh T T.denominator * invDenomHigh T = 1 :=
  IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)

def chartMapHigh {r : ℕ} (T : ChartHigh r) : CoeffRingHigh →ₐ[Geo] ChartOpenHigh T :=
  MvPolynomial.aeval fun i => localizeHigh T (T.numerator i) * invDenomHigh T

private theorem in_zeroLocus_high {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo}
    (hy : y ∈ T.locus) : y ∈ zeroLocus Geo (sourceIdealHigh T) := by
  apply mem_zeroLocus_iff_le_ker_aeval.mpr
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact RingHom.mem_ker.mpr hy.1

private def pointEvalHigh {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo} (hy : y ∈ T.locus) :
    (InitialRing r ⧸ sourceIdealHigh T) →ₐ[Geo] Geo :=
  Ideal.Quotient.liftₐ (sourceIdealHigh T) (MvPolynomial.aeval y) fun q hq =>
    in_zeroLocus_high hy q hq

def openEvalHigh {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo} (hy : y ∈ T.locus) :
    ChartOpenHigh T →ₐ[Geo] Geo :=
  IsLocalization.Away.liftAlgHom (f := pointEvalHigh hy)
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)

theorem openEvalHigh_localize {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo} (hy : y ∈ T.locus)
    (q : InitialRing r) : openEvalHigh hy (localizeHigh T q) = MvPolynomial.eval y q :=
  IsLocalization.Away.lift_eq (g := (pointEvalHigh hy).toRingHom)
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
    (Ideal.Quotient.mk (sourceIdealHigh T) q)

theorem openEvalHigh_chartMap {r : ℕ} {T : ChartHigh r} {y : Fin (r + 1) → Geo} (hy : y ∈ T.locus)
    (q : CoeffRingHigh) : openEvalHigh hy (chartMapHigh T q) = MvPolynomial.eval (T.output y) q := by
  have hu := congrArg (openEvalHigh hy) (denom_mul_inv_high T)
  rw [map_mul, openEvalHigh_localize, map_one] at hu
  have hi : openEvalHigh hy (invDenomHigh T) = (MvPolynomial.eval y T.denominator)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hy.2).mpr ((mul_comm _ _).trans hu)
  have h : (openEvalHigh hy).comp (chartMapHigh T) = MvPolynomial.aeval (T.output y) := by
    apply MvPolynomial.algHom_ext
    intro i
    change openEvalHigh hy (chartMapHigh T (MvPolynomial.X i)) =
      MvPolynomial.aeval (T.output y) (MvPolynomial.X i)
    rw [chartMapHigh, MvPolynomial.aeval_X, map_mul, openEvalHigh_localize, hi, MvPolynomial.aeval_X,
      ChartHigh.output, div_eq_mul_inv]
  exact DFunLike.congr_fun h q

private theorem eq_zero_of_openEvalHigh {r : ℕ} {T : ChartHigh r} [(sourceIdealHigh T).IsPrime]
    (hD : T.denominator ∉ sourceIdealHigh T) {z : ChartOpenHigh T}
    (hz : ∀ y (hy : y ∈ T.locus), openEvalHigh hy z = 0) : z = 0 := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator) z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  change z * localizeHigh T T.denominator ^ m = localizeHigh T q at ha
  have hq : q ∈ sourceIdealHigh T := by
    have hmul : T.denominator * q ∈ sourceIdealHigh T := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := Geo) (sourceIdealHigh T)]
      intro y hy
      change MvPolynomial.eval y (T.denominator * q) = 0
      by_cases hyD : MvPolynomial.eval y T.denominator = 0
      · rw [map_mul, hyD, zero_mul]
      · have hy' : y ∈ T.locus := ⟨hy _ (Ideal.subset_span (by simp)), hyD⟩
        have he := congrArg (openEvalHigh hy') ha
        rw [map_mul, map_pow, openEvalHigh_localize, openEvalHigh_localize, hz y hy', zero_mul] at he
        rw [map_mul, ← he, mul_zero]
    exact (‹(sourceIdealHigh T).IsPrime›.mem_or_mem hmul).resolve_left hD
  have hq0 : localizeHigh T q = 0 := by
    change algebraMap (InitialRing r ⧸ sourceIdealHigh T) (ChartOpenHigh T)
      (Ideal.Quotient.mk (sourceIdealHigh T) q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  rw [hq0] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := ChartOpenHigh T)
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)).pow m).mul_right_cancel
      (ha.trans (zero_mul _).symm)

theorem imageIdeal_eq_ker_high {r : ℕ} (T : ChartHigh r) [(sourceIdealHigh T).IsPrime]
    (hD : T.denominator ∉ sourceIdealHigh T) :
    T.ideal = RingHom.ker (chartMapHigh T).toRingHom := by
  ext q
  change q ∈ vanishingIdeal Geo T.imageSet ↔ chartMapHigh T q = 0
  constructor
  · intro hq
    apply eq_zero_of_openEvalHigh hD
    intro y hy
    rw [openEvalHigh_chartMap hy]
    exact hq _ ⟨y, hy, rfl⟩
  · intro hq
    rintro _ ⟨y, hy, rfl⟩
    change MvPolynomial.eval (T.output y) q = 0
    rw [← openEvalHigh_chartMap hy, hq, map_zero]

private def jetFormHigh (j : ℕ) : CoeffRingHigh :=
  ∑ i : Fin kHigh, MvPolynomial.C ((i.val.choose j : Geo) * center ^ (i.val - j)) * MvPolynomial.X i

private theorem eval_jetFormHigh (y : Fin kHigh → Geo) (j : ℕ) :
    MvPolynomial.eval y (jetFormHigh j) = readJetHigh y j := by
  simp [jetFormHigh, readJetHigh]

private theorem chartMapHigh_recover {r : ℕ} (T : ChartHigh r) (hT : ChartOKHigh T)
    [(sourceIdealHigh T).IsPrime] (hD : T.denominator ∉ sourceIdealHigh T) :
    (chartMapHigh T).comp (MvPolynomial.aeval fun j : Fin (r + 1) => jetFormHigh j.val) =
      localizeHigh T := by
  apply MvPolynomial.algHom_ext
  intro j
  change chartMapHigh T (MvPolynomial.aeval (fun j : Fin (r + 1) => jetFormHigh j.val)
      (MvPolynomial.X j)) = localizeHigh T (MvPolynomial.X j)
  rw [MvPolynomial.aeval_X, ← sub_eq_zero]
  apply eq_zero_of_openEvalHigh hD
  intro y hy
  rw [map_sub, openEvalHigh_chartMap, openEvalHigh_localize, eval_jetFormHigh, MvPolynomial.eval_X,
    hT.recover y hy j, sub_self]

theorem image_geometry_high {r : ℕ} (T : ChartHigh r) (hT : ChartOKHigh T) :
    T.ideal.IsPrime ∧ (affineHilbertPolynomial T.ideal).natDegree = r := by
  have hprime : (sourceIdealHigh T).IsPrime :=
    Ideal.span_singleton_prime hT.irreducible.ne_zero |>.mpr hT.irreducible.prime
  let _ := hprime
  have hD : T.denominator ∉ sourceIdealHigh T :=
    fun h => hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  have hne : Ideal.Quotient.mk (sourceIdealHigh T) T.denominator ≠ 0 :=
    mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  let _ : IsDomain (ChartOpenHigh T) := Localization.Away.isDomain hne
  have hreg := (IsRegular.of_ne_zero hne).1
  have hsource : (affineHilbertPolynomial (sourceIdealHigh T)).natDegree = r := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      hT.irreducible.ne_zero hprime.ne_top
    rw [Nat.card_fin] at h
    exact Nat.add_right_cancel h
  rw [imageIdeal_eq_ker_high T hD]
  refine ⟨RingHom.ker_isPrime _, Eq.trans (le_antisymm ?_ ?_) hsource⟩
  · let E := awayPresentationEquiv (sourceIdealHigh T) T.denominator
    exact (natDegree_affineHilbertPolynomial_le_of_injective
      (E.symm.toAlgHom.comp (Ideal.kerLiftAlg (chartMapHigh T)))
      (E.symm.injective.comp (Ideal.kerLiftAlg_injective (chartMapHigh T)))).trans
      (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le (sourceIdealHigh T) T.denominator)
  · exact natDegree_affineHilbertPolynomial_le_of_away_range (sourceIdealHigh T) T.denominator hreg
      (chartMapHigh T)
      (fun q => ⟨_, DFunLike.congr_fun (chartMapHigh_recover T hT hD) q⟩) le_rfl

private theorem c1_high (T : ChartHigh 2) (a d e : ℕ) (hT : ChartOKHigh T)
    (hD : T.denominator ∈ CJ0_4.bandSpace a d e)
    (hN : ∀ i : Fin kHigh, T.numerator i ∈ CJ0_4.bandSpace a d e) (m : ℕ) :
    affineHilbertFunction T.ideal m ≤
      Module.finrank Geo (quotientBandHigh T (m * a) (m * d) (m * e)) := by
  let _ : (sourceIdealHigh T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  have hD' : T.denominator ∉ sourceIdealHigh T :=
    fun h => hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  rw [imageIdeal_eq_ker_high T hD']
  let j := IsScalarTower.toAlgHom Geo (InitialRing 2 ⧸ sourceIdealHigh T) (ChartOpenHigh T)
  let δ := localizeHigh T T.denominator
  have hδ : IsUnit δ :=
    IsLocalization.Away.algebraMap_isUnit (S := ChartOpenHigh T)
      (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator)
  let y (i : Fin kHigh) := localizeHigh T (T.numerator i) * invDenomHigh T
  have hy (i : Fin kHigh) : δ * y i = localizeHigh T (T.numerator i) := by
    change localizeHigh T T.denominator * (localizeHigh T (T.numerator i) * invDenomHigh T) = _
    rw [mul_left_comm _ (localizeHigh T (T.numerator i)), denom_mul_inv_high, mul_one]
  let V (n : ℕ) : Submodule Geo (ChartOpenHigh T) :=
    (quotientBandHigh T (n * a) (n * d) (n * e)).map j.toLinearMap
  let W (n : ℕ) : Submodule Geo (ChartOpenHigh T) :=
    (V n).comap (LinearMap.mulLeft Geo (δ ^ n))
  have hW (n : ℕ) (z : ChartOpenHigh T) :
      z ∈ W n ↔ ∃ P ∈ CJ0_4.bandSpace (n * a) (n * d) (n * e), localizeHigh T P = δ ^ n * z := by
    change δ ^ n * z ∈ V n ↔ _
    simp only [V, quotientBandHigh, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap,
      Submodule.mem_map, AlgHom.toLinearMap_apply, localizeHigh, j]
  have hOne : (1 : InitialRing 2) ∈ CJ0_4.bandSpace 0 0 0 := by
    have hw : weightedTotalDegree Fin.val (1 : InitialRing 2) = 0 := by
      rw [← MvPolynomial.C_1, weightedTotalDegree_C]
    exact CJ0_4.mem_bandSpace.mpr ⟨totalDegree_one.le, hw.le, (degreeOf_one _).le⟩
  have hpow (n : ℕ) : T.denominator ^ n ∈ CJ0_4.bandSpace (n * a) (n * d) (n * e) := by
    induction n with
    | zero => simpa only [pow_zero, Nat.zero_mul] using hOne
    | succ n ih => simpa only [pow_succ, Nat.succ_mul] using CJ0_4.mul_mem_bandSpace ih hD
  have hmono : Monotone W := by
    intro n l hnl z hz
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨T.denominator ^ (l - n) * P, ?_, ?_⟩
    · simpa only [← Nat.add_mul, Nat.sub_add_cancel hnl] using
        CJ0_4.mul_mem_bandSpace (hpow (l - n)) hP
    · rw [map_mul, map_pow, heq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnl]
  have hmul (i : Fin kHigh) (n : ℕ) (z : ChartOpenHigh T) (hz : z ∈ W n) :
      y i * z ∈ W (n + 1) := by
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨P * T.numerator i, ?_, ?_⟩
    · simpa only [Nat.add_mul, Nat.one_mul] using CJ0_4.mul_mem_bandSpace hP (hN i)
    · rw [map_mul, heq, ← hy i, pow_succ]
      ac_rfl
  have h0 : (1 : ChartOpenHigh T) ∈ W 0 :=
    (hW _ _).mpr ⟨1, by simpa only [Nat.zero_mul] using hOne, by simp⟩
  have hclear (P : CoeffRingHigh) (hP : P.totalDegree ≤ m) : chartMapHigh T P ∈ W m := by
    change MvPolynomial.aeval y P ∈ W m
    simpa only [Nat.one_mul] using
      (aeval_mem_of_forall_mul_mem y hmono h0 hmul hP)
  let Q := RingHom.ker (chartMapHigh T).toRingHom
  let ι : (CoeffRingHigh ⧸ Q) →ₐ[Geo] ChartOpenHigh T := Ideal.kerLiftAlg (chartMapHigh T)
  have hmem (x : quotientDegreeLE Q m) : δ ^ m * ι x.val ∈ V m := by
    obtain ⟨P, hP, heq⟩ := mem_quotientDegreeLE.mp x.property
    change ι x.val ∈ W m
    rw [← heq]
    change chartMapHigh T P ∈ W m
    exact hclear P hP
  let L : quotientDegreeLE Q m →ₗ[Geo] V m :=
    (((LinearMap.mulLeft Geo (δ ^ m)).comp ι.toLinearMap).domRestrict
      (quotientDegreeLE Q m)).codRestrict (V m) hmem
  have hL : Function.Injective L := by
    intro x z hxz
    have h : δ ^ m * ι x.val = δ ^ m * ι z.val := congrArg Subtype.val hxz
    exact Subtype.ext (Ideal.kerLiftAlg_injective (chartMapHigh T) ((hδ.pow m).mul_left_cancel h))
  exact (LinearMap.finrank_le_finrank_of_injective hL).trans (Submodule.finrank_map_le _ _)

private theorem quotientBandHigh_add_finrank_le (T : ChartHigh 2) (a d e b j c : ℕ)
    (hn : T.equation ≠ 0) (hf : T.equation ∈ CJ0_4.bandSpace b j c) :
    Module.finrank Geo (quotientBandHigh T (a + b) (d + j) (e + c)) +
      Module.finrank Geo (CJ0_4.bandSpace a d e) ≤
      Module.finrank Geo (CJ0_4.bandSpace (a + b) (d + j) (e + c)) := by
  let W := CJ0_4.bandSpace (a + b) (d + j) (e + c)
  let F := (Ideal.Quotient.mkₐ Geo (sourceIdealHigh T)).toLinearMap.domRestrict W
  have hF : LinearMap.range F = quotientBandHigh T (a + b) (d + j) (e + c) :=
    LinearMap.range_domRestrict W _
  let mul := (LinearMap.mulLeft Geo T.equation).domRestrict (CJ0_4.bandSpace a d e)
  have hmul (p : CJ0_4.bandSpace a d e) : mul p ∈ W := by
    simpa only [mul, W, LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, Nat.add_comm]
      using CJ0_4.mul_mem_bandSpace hf p.property
  let g : CJ0_4.bandSpace a d e →ₗ[Geo] W := mul.codRestrict W hmul
  have hg (p : CJ0_4.bandSpace a d e) : g p ∈ LinearMap.ker F := by
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (sourceIdealHigh T) (T.equation * p.val) = 0
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

private theorem band_difference_high (a d e b j c : ℚ) :
    ∃ u v : ℚ, ∀ x : ℚ,
      CJ0_4.bandCount (x * a + j + 2 * c + b) (x * d + 2 * c + j) (x * e + c) -
        CJ0_4.bandCount (x * a + j + 2 * c) (x * d + 2 * c) (x * e) =
      (CJ0_4.surfaceBound a d e b j c / 2) * x ^ 2 + u * x + v := by
  let f (x : ℚ) :=
    CJ0_4.bandCount (x * a + j + 2 * c + b) (x * d + 2 * c + j) (x * e + c) -
      CJ0_4.bandCount (x * a + j + 2 * c) (x * d + 2 * c) (x * e)
  refine ⟨f 1 - f 0 - CJ0_4.surfaceBound a d e b j c / 2, f 0, fun x => ?_⟩
  dsimp [f, CJ0_4.bandCount, CJ0_4.surfaceBound]
  ring

private theorem degree_le_of_quadratic_high
    (I : Ideal CoeffRingHigh) (hdim : (affineHilbertPolynomial I).natDegree = 2)
    (q u v : ℚ) (hle : ∀ᶠ m : ℕ in atTop,
      (affineHilbertPolynomial I).eval (m : ℚ) ≤ q * (m : ℚ) ^ 2 + u * (m : ℚ) + v) :
    affineDegree I ≤ 2 * q := by
  let P : Polynomial ℚ := Polynomial.C q * Polynomial.X ^ 2 +
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

theorem chart_degree_high (T : ChartHigh 2) (hT : ChartOKHigh T)
    (hdim : (affineHilbertPolynomial T.ideal).natDegree = 2)
    (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d)
    (hD : T.denominator ∈ CJ0_4.bandSpace a d e)
    (hN : ∀ i : Fin kHigh, T.numerator i ∈ CJ0_4.bandSpace a d e) :
    affineDegree T.ideal ≤ CJ0_4.surfaceBound a d e T.equation.totalDegree
      ((T.equation.weightedTotalDegree Fin.val : ℕ) : ℚ) (T.equation.degreeOf (Fin.last 2)) := by
  let b := T.equation.totalDegree
  let j := T.equation.weightedTotalDegree Fin.val
  let c := T.equation.degreeOf (Fin.last 2)
  have hf : T.equation ∈ CJ0_4.bandSpace b j c := CJ0_4.mem_bandSpace.mpr ⟨le_rfl, le_rfl, le_rfl⟩
  obtain ⟨u, v, hexpand⟩ := band_difference_high a d e b j c
  have hle : ∀ᶠ m : ℕ in atTop, (affineHilbertPolynomial T.ideal).eval (m : ℚ) ≤
      (CJ0_4.surfaceBound a d e b j c / 2) * (m : ℚ) ^ 2 + u * (m : ℚ) + v := by
    filter_upwards [eventually_eval_affineHilbertPolynomial T.ideal] with m hm
    have hma := Nat.mul_le_mul_left m hda
    have hme : 2 * (m * e) ≤ m * d := by
      simpa only [Nat.mul_left_comm 2 m e] using Nat.mul_le_mul_left m hed
    have hmono : Module.finrank Geo (quotientBandHigh T (m * a) (m * d) (m * e)) ≤
        Module.finrank Geo (quotientBandHigh T (m * a + j + 2 * c + b) (m * d + 2 * c + j) (m * e + c)) :=
      Submodule.finrank_mono (quotientBandHigh_mono T (by omega) (by omega) (by omega))
    have hdimNat := (Nat.add_le_add_right ((c1_high T a d e hT hD hN m).trans hmono) _).trans
      (quotientBandHigh_add_finrank_le T (m * a + j + 2 * c) (m * d + 2 * c) (m * e) b j c
        hT.irreducible.ne_zero hf)
    have hdimRat := (Nat.cast_le (α := ℚ)).mpr hdimNat
    rw [Nat.cast_add,
      CJ0_4_2.proof (m * a + j + 2 * c) (m * d + 2 * c) (m * e) (by omega) (by omega),
      CJ0_4_2.proof (m * a + j + 2 * c + b) (m * d + 2 * c + j) (m * e + c) (by omega) (by omega)] at hdimRat
    push_cast at hdimRat
    rw [hm, ← hexpand (m : ℚ)]
    exact le_sub_iff_add_le.mpr hdimRat
  calc
    _ ≤ 2 * (CJ0_4.surfaceBound a d e b j c / 2) :=
      degree_le_of_quadratic_high T.ideal hdim (CJ0_4.surfaceBound a d e b j c / 2) u v hle
    _ = _ := by ring

def bandVolumeHigh (s : BoxShape) (L b j c : ℕ) : ℚ :=
  volumeTotal s L * b + volumeIndex s L * j + volumeTop s L * c

def slicePriceHigh (A : ℕ) (s : BoxShape) (L b j c : ℕ) : ℚ :=
  curveFactor A * bandVolumeHigh s L b j c + (totalCap s L : ℚ) * b

theorem volume_nonneg_high (s : BoxShape) (hs : BoxOK s) (L : ℕ) (hL : 3 ≤ L) :
    0 ≤ volumeTotal s L ∧ 0 ≤ volumeIndex s L ∧ 0 ≤ volumeTop s L := by
  have hd : (indexCap s L : ℚ) ≤ totalCap s L := by exact_mod_cast indexCap_le_totalCap s hs L hL
  have he : 2 * (topCap s L : ℚ) ≤ indexCap s L := by exact_mod_cast twice_topCap_le s L
  have ha : 0 ≤ (totalCap s L : ℚ) := Nat.cast_nonneg _
  have ht : 0 ≤ (topCap s L : ℚ) := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · unfold volumeTotal; exact mul_nonneg (by positivity) (by linarith)
  · unfold volumeIndex; exact mul_nonneg ht (by linarith)
  · unfold volumeTop; exact mul_nonneg (by linarith) (by linarith)

theorem volumeDegree_high (s : BoxShape) (hs : BoxOK s) (L : ℕ) (hL : 3 ≤ L)
    (T : ChartHigh 2) (hT : ChartOKHigh T) (hb : ShortBandHigh s L T) :
    affineDegree T.ideal ≤ bandVolumeHigh s L T.equation.totalDegree
      (T.equation.weightedTotalDegree Fin.val) (T.equation.degreeOf (Fin.last 2)) := by
  simpa only [CJ0_4.surfaceBound, bandVolumeHigh, volumeTotal, volumeIndex, volumeTop] using
    (chart_degree_high T hT (image_geometry_high T hT).2
      (totalCap s L) (indexCap s L) (topCap s L) (indexCap_le_totalCap s hs L hL)
      (twice_topCap_le s L) (CJ0_4.mem_bandSpace.mpr hb.denominator)
      (fun i => CJ0_4.mem_bandSpace.mpr (hb.numerator i)))

theorem weighted_price_high (A common : ℕ) (s : BoxShape) (hs : BoxOK s)
    (hA : kHigh + 5 ≤ A) (hAn : A ≤ nHigh) (hc : common ≤ NHigh) (b j c : ℕ) :
    incidenceFactor A common * slicePriceHigh A s (shortLength common) b j c ≤
      baseFactor A * slicePriceHigh A s kHigh b j c := by
  let L := shortLength common
  have hL : 3 ≤ L := le_max_left ..
  have hK : L ≤ kHigh := max_le (by decide) (Nat.sub_le ..)
  obtain ⟨ha, hu, hv, hw⟩ := volumeScale s hs L hL hK
  have hscl : (kHigh : ℚ) * slicePriceHigh A s L b j c ≤
      (L : ℚ) * slicePriceHigh A s kHigh b j c := by
    have hui := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg b)
    have hvi := mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg j)
    have hwi := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg c)
    have hai := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg b)
    have hcurve : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hvol := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hui hvi) hwi) hcurve
    unfold slicePriceHigh bandVolumeHigh
    nlinarith only [hvol, hai]
  have hp : 0 ≤ slicePriceHigh A s kHigh b j c := by
    obtain ⟨hu, hv, hw⟩ := volume_nonneg_high s hs kHigh (by decide)
    have hcurve : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    unfold slicePriceHigh bandVolumeHigh
    positivity
  have h := mul_le_mul_of_nonneg_left hscl (show 0 ≤ incidenceFactor A common by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have h' := mul_le_mul_of_nonneg_right (incidenceLength A common hA hAn hc) hp
  have h'' : (kHigh : ℚ) * (incidenceFactor A common * slicePriceHigh A s L b j c) ≤
      (kHigh : ℚ) * (baseFactor A * slicePriceHigh A s kHigh b j c) := by
    nlinarith only [h, h']
  exact le_of_mul_le_mul_left h'' (by positivity)

theorem volume_full_high (s : BoxShape) (hs : BoxOK s) :
    bandVolumeHigh s kHigh s.B s.J s.C = R2High s := by
  have hda : DHigh s ≤ a0High s := indexCap_le_totalCap s hs kHigh (by decide)
  have hde : 2 * eHigh s ≤ DHigh s := twice_topCap_le s kHigh
  have hD' : DHigh s ≤ 2 * a0High s := by omega
  have hJ' : s.J ≤ 2 * s.B := by have := hs.total_index; omega
  have he' : eHigh s ≤ DHigh s := by omega
  have hC' : 2 * s.C * eHigh s ≤ s.C * DHigh s + eHigh s * s.J := by
    calc
      _ = s.C * (2 * eHigh s) := by ring
      _ ≤ s.C * DHigh s := Nat.mul_le_mul_left _ hde
      _ ≤ _ := Nat.le_add_right _ _
  unfold bandVolumeHigh volumeTotal volumeIndex volumeTop
  rw [show totalCap s kHigh = a0High s by rfl,
    show indexCap s kHigh = DHigh s by rfl,
    show topCap s kHigh = eHigh s by rfl]
  dsimp [R2High]
  push_cast [Nat.cast_sub hD', Nat.cast_sub hJ', Nat.cast_sub he', Nat.cast_sub hC']
  ring

/-! ## Section 3: Evaluation-Section Capacity (`ScalarCutCapacity.cutCap` at `kHigh`) -/

private def pullbackHigh (T : ChartHigh 2) (x a : K) : InitialRing 2 :=
  (∑ j : Fin kHigh, MvPolynomial.C (embed x ^ j.val) * T.numerator j) -
    MvPolynomial.C (embed a) * T.denominator

private theorem pullbackHigh_degree (T : ChartHigh 2) (x a : K) (b : ℕ)
    (hd : T.denominator.totalDegree ≤ b) (hn : ∀ j, (T.numerator j).totalDegree ≤ b) :
    (pullbackHigh T x a).totalDegree ≤ b := by
  apply (totalDegree_sub _ _).trans
  refine max_le (totalDegree_finsetSum_le ?_) ?_
  · intro j _
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hn j)
  · exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hd)

private theorem eval_pullbackHigh (T : ChartHigh 2) (x a : K) (y : Fin 3 → Geo)
    (hd : MvPolynomial.eval y T.denominator ≠ 0) :
    MvPolynomial.eval y (pullbackHigh T x a) =
      MvPolynomial.eval (T.output y) (valueCutHigh x a) * MvPolynomial.eval y T.denominator := by
  simp only [pullbackHigh, valueCutHigh, map_sub, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, ChartHigh.output]
  rw [sub_mul, sum_mul]
  refine congrArg₂ (· - ·) (sum_congr rfl ?_) rfl
  intro j _
  rw [mul_assoc, div_mul_cancel₀ _ hd]

private def componentImageHigh (T : ChartHigh 2) (Q : Ideal (InitialRing 2)) :
    Set (Fin kHigh → Geo) :=
  T.output '' {y | y ∈ zeroLocus Geo Q ∧ MvPolynomial.eval y T.denominator ≠ 0}

private theorem belongs_chart_high (T : ChartHigh 2) {Q : Ideal (InitialRing 2)}
    (hle : sourceIdealHigh T ≤ Q) {y : Fin 3 → Geo}
    (hy : y ∈ zeroLocus Geo Q) (hd : MvPolynomial.eval y T.denominator ≠ 0) : y ∈ T.locus :=
  ⟨hy _ (hle (Ideal.mem_span_singleton_self T.equation)), hd⟩

private theorem clear_at_chart_high (T : ChartHigh 2) (P : CoeffRingHigh) :
    ∃ R : InitialRing 2, ∃ m : ℕ, ∀ y ∈ T.locus,
      MvPolynomial.eval y R = MvPolynomial.eval (T.output y) P * MvPolynomial.eval y T.denominator ^ m := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (sourceIdealHigh T) T.denominator) (chartMapHigh T P)
  obtain ⟨R, rfl⟩ := Ideal.Quotient.mk_surjective a
  change chartMapHigh T P * localizeHigh T T.denominator ^ m = localizeHigh T R at ha
  refine ⟨R, m, fun y hy => ?_⟩
  have hh := congrArg (openEvalHigh hy) ha
  rw [map_mul, map_pow, openEvalHigh_chartMap hy, openEvalHigh_localize hy,
    openEvalHigh_localize hy] at hh
  exact hh.symm

private theorem component_image_prime_high (T : ChartHigh 2) (Q : Ideal (InitialRing 2))
    (hQ : Q.IsPrime) (hle : sourceIdealHigh T ≤ Q) (hD : T.denominator ∉ Q) :
    (vanishingIdeal Geo (componentImageHigh T Q)).IsPrime := by
  let _ := hQ
  have hrad := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := Geo) Q
  have hpoint : ∃ y ∈ zeroLocus Geo Q, MvPolynomial.eval y T.denominator ≠ 0 := by
    by_contra! h
    apply hD
    rw [← hrad]
    exact h
  apply Ideal.isPrime_iff.mpr
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨y, hy, hdy⟩ := hpoint
    have hone : (1 : CoeffRingHigh) ∈ vanishingIdeal Geo (componentImageHigh T Q) := by
      rw [h]; trivial
    have hh := hone _ ⟨y, ⟨hy, hdy⟩, rfl⟩
    exact one_ne_zero (by simpa only [map_one] using hh)
  · intro P₁ P₂ hmul
    obtain ⟨R₁, m₁, h₁⟩ := clear_at_chart_high T P₁
    obtain ⟨R₂, m₂, h₂⟩ := clear_at_chart_high T P₂
    have hRs : T.denominator * (R₁ * R₂) ∈ Q := by
      rw [← hrad]
      intro y hy
      change MvPolynomial.eval y (T.denominator * (R₁ * R₂)) = 0
      by_cases hdy : MvPolynomial.eval y T.denominator = 0
      · rw [map_mul, hdy, zero_mul]
      · have hchart := belongs_chart_high T hle hy hdy
        have hh : MvPolynomial.eval (T.output y) (P₁ * P₂) = 0 := hmul _ ⟨y, ⟨hy, hdy⟩, rfl⟩
        rw [map_mul] at hh
        rw [map_mul, map_mul, h₁ y hchart, h₂ y hchart]
        calc
          _ = (MvPolynomial.eval (T.output y) P₁ * MvPolynomial.eval (T.output y) P₂) *
              (MvPolynomial.eval y T.denominator * MvPolynomial.eval y T.denominator ^ m₁ *
                MvPolynomial.eval y T.denominator ^ m₂) := by ring
          _ = 0 := by rw [hh, zero_mul]
    have hor := hQ.mem_or_mem ((hQ.mem_or_mem hRs).resolve_left hD)
    have conclude {P : CoeffRingHigh} {R : InitialRing 2} {m : ℕ}
        (hr : R ∈ Q) (he : ∀ y ∈ T.locus,
          MvPolynomial.eval y R =
            MvPolynomial.eval (T.output y) P * MvPolynomial.eval y T.denominator ^ m) :
        P ∈ vanishingIdeal Geo (componentImageHigh T Q) := by
      rintro _ ⟨y, ⟨hy, hdy⟩, rfl⟩
      have hval : MvPolynomial.eval y R = 0 := hy R hr
      exact (mul_eq_zero.mp ((he y (belongs_chart_high T hle hy hdy)).symm.trans hval)).resolve_right
        (pow_ne_zero _ hdy)
    exact hor.imp (fun hr => conclude hr h₁) (fun hr => conclude hr h₂)

private theorem component_target_high (T : ChartHigh 2) (x a : K)
    {Q : Ideal (InitialRing 2)} (hQ : Q.IsPrime) (hle : sourceIdealHigh T ≤ Q)
    (hD : T.denominator ∉ Q) (hcut : pullbackHigh T x a ∈ Q) :
    ∃ P ∈ (T.ideal ⊔ Ideal.span {valueCutHigh x a}).minimalPrimesFinset,
      componentImageHigh T Q ⊆ zeroLocus Geo P := by
  let J := vanishingIdeal Geo (componentImageHigh T Q)
  let _ : J.IsPrime := component_image_prime_high T Q hQ hle hD
  have hT : T.ideal ≤ J := by
    intro q hq
    rintro _ ⟨y, ⟨hy, hdy⟩, rfl⟩
    exact hq _ ⟨y, belongs_chart_high T hle hy hdy, rfl⟩
  have hC : valueCutHigh x a ∈ J := by
    rintro _ ⟨y, ⟨hy, hdy⟩, rfl⟩
    have he : MvPolynomial.eval y (pullbackHigh T x a) = 0 := hy _ hcut
    exact (mul_eq_zero.mp ((eval_pullbackHigh T x a y hdy).symm.trans he)).resolve_right hdy
  obtain ⟨P, hP, hPJ⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hT ((Ideal.span_singleton_le_iff_mem J).mpr hC))
  exact ⟨P, Ideal.mem_minimalPrimesFinset.mpr hP, fun y hy q hq => hPJ hq _ hy⟩

theorem cutCap_high {A w} {V : Finset (Polynomial K)} (T : ChartHigh 2) (hT : ChartOKHigh T)
    (hA : AgreementOKHigh A) (hV : (V : Set (Polynomial K)) ⊆ closeHigh A w)
    (hcover : ∀ f ∈ V, coeffPointHigh f ∈ T.imageSet)
    (i : Node) (hmiss : ∃ f ∈ V, f.eval (node i) ≠ w i)
    (a : ℕ) (hden : T.denominator.totalDegree ≤ a) (hnum : ∀ j, (T.numerator j).totalDegree ≤ a) :
    (gapHigh A : ℚ) * (V.filter (fun f => f.eval (node i) = w i)).card ≤
      (errorsHigh A : ℚ) * affineDegree T.ideal + (gapHigh A : ℚ) * (a * T.equation.totalDegree : ℕ) := by
  classical
  let x := node i
  let b := w i
  let c := valueCutHigh x b
  let r := pullbackHigh T x b
  let J := sourceIdealHigh T ⊔ Ideal.span {r}
  let D := T.ideal ⊔ Ideal.span {c}
  let src := J.retainedMinimalPrimes T.denominator
  let Vhit := V.filter fun f => f.eval x = b
  have hp : (sourceIdealHigh T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  let _ := hp
  obtain ⟨hprime, hdim⟩ := image_geometry_high T hT
  let _ := hprime
  have hsrcDim : (affineHilbertPolynomial (sourceIdealHigh T)).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      hT.irreducible.ne_zero hp.ne_top
    rw [Nat.card_fin] at h
    exact Nat.add_right_cancel h
  obtain ⟨f, hf, hmiss⟩ := hmiss
  obtain ⟨y, hy, hyf⟩ := hcover f hf
  have hcNe : MvPolynomial.eval (T.output y) c ≠ 0 := by
    rw [hyf]
    exact fun h => hmiss ((valueCutHigh_eval (hV hf).1 x b).mp h)
  have hc : c ∉ T.ideal := fun hm => hcNe (hm _ ⟨y, hy, rfl⟩)
  have hr : r ∉ sourceIdealHigh T := by
    intro hh
    have hpt : y ∈ zeroLocus Geo (sourceIdealHigh T) := by
      apply mem_zeroLocus_iff_le_ker_aeval.mpr
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact RingHom.mem_ker.mpr hy.1
    have he : MvPolynomial.eval y r = 0 := hpt _ hh
    rw [eval_pullbackHigh T x b y hy.2] at he
    exact mul_ne_zero hcNe hy.2 he
  have srcDegree : (src.card : ℚ) ≤ (a * T.equation.totalDegree : ℕ) := by
    have hs := principalCut_sum_affineDegree_minimalPrimes_le hr (pullbackHigh_degree T x b a hden hnum)
    rw [show affineDegree (sourceIdealHigh T) = (T.equation.totalDegree : ℚ) from
      affineDegree_span_singleton hT.irreducible.ne_zero] at hs
    rw [Nat.cast_mul]
    calc
      _ = ∑ Q ∈ src, (1 : ℚ) := by simp
      _ ≤ ∑ Q ∈ src, affineDegree Q := by
        apply sum_le_sum
        intro Q hQ
        have hmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
        have hq := principalCut_natDegree_affineHilbertPolynomial_add_one hr hmin
        obtain ⟨n, hn, he⟩ := curve_degree_nat Q hmin.isPrime (by omega)
        rw [he]
        exact_mod_cast hn
      _ ≤ ∑ Q ∈ J.minimalPrimesFinset, affineDegree Q :=
        sum_le_sum_of_subset_of_nonneg (Ideal.retainedMinimalPrimes_subset _ _)
          (fun Q _ _ => affineDegree_nonneg Q)
      _ ≤ _ := hs
  have hcomp (Q : Ideal (InitialRing 2)) (hQ : Q ∈ src) :
      ∃ P ∈ D.minimalPrimesFinset, componentImageHigh T Q ⊆ zeroLocus Geo P := by
    obtain ⟨hmin, hdenQ⟩ := Ideal.mem_retainedMinimalPrimes.mp hQ
    exact component_target_high T x b hmin.isPrime (le_sup_left.trans hmin.le) hdenQ
      (hmin.le ((show Ideal.span {r} ≤ J from le_sup_right) (Ideal.mem_span_singleton_self r)))
  let pick (Q : Ideal (InitialRing 2)) : Ideal CoeffRingHigh :=
    if hQ : Q ∈ src then (hcomp Q hQ).choose else ⊤
  have picked (Q : Ideal (InitialRing 2)) (hQ : Q ∈ src) :
      pick Q ∈ D.minimalPrimesFinset ∧ componentImageHigh T Q ⊆ zeroLocus Geo (pick Q) := by
    dsimp only [pick]
    rw [dite_eq_left hQ]
    exact (hcomp Q hQ).choose_spec
  let Ps := src.image pick
  have hPs : Ps ⊆ D.minimalPrimesFinset := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hP
    exact (picked Q hQ).1
  let part (P : Ideal CoeffRingHigh) := Vhit.filter fun f => coeffPointHigh f ∈ zeroLocus Geo P
  have hpart : Vhit ⊆ Ps.biUnion part := by
    intro f hf
    obtain ⟨hfV, hfb⟩ := mem_filter.mp hf
    obtain ⟨z, hz, hzf⟩ := hcover f hfV
    have hzEq : MvPolynomial.eval z r = 0 := by
      have hv : MvPolynomial.eval (coeffPointHigh f) (valueCutHigh x b) = 0 :=
        (valueCutHigh_eval (hV hfV).1 x b).mpr hfb
      rw [eval_pullbackHigh T x b z hz.2, hzf, hv, zero_mul]
    have hzJ : z ∈ zeroLocus Geo J := by
      apply mem_zeroLocus_sup_span_singleton_iff.mpr
      refine ⟨?_, hzEq⟩
      apply mem_zeroLocus_iff_le_ker_aeval.mpr
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact RingHom.mem_ker.mpr hz.1
    obtain ⟨Q, hQ, hzQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J T.denominator z hzJ hz.2
    refine mem_biUnion.mpr ⟨pick Q, mem_image.mpr ⟨Q, hQ, rfl⟩, mem_filter.mpr ⟨hf, ?_⟩⟩
    apply (picked Q hQ).2
    exact ⟨z, ⟨hzQ, hz.2⟩, hzf⟩
  have hone (P : Ideal CoeffRingHigh) (hP : P ∈ Ps) :
      (gapHigh A : ℚ) * (part P).card ≤ (errorsHigh A : ℚ) * affineDegree P + gapHigh A := by
    have hmin := Ideal.mem_minimalPrimesFinset.mp (hPs hP)
    have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hc hmin
    exact (curve_capacity_high (fun _ hf => hV (mem_filter.mp (mem_filter.mp hf).1).1) hA
      hmin.isPrime (by omega) (fun _ hf => (mem_filter.mp hf).2)).1
  have hsum : (Vhit.card : ℚ) ≤ ∑ P ∈ Ps, ((part P).card : ℚ) := by
    exact_mod_cast ((card_le_card hpart).trans card_biUnion_le)
  have hpdeg : (∑ P ∈ Ps, affineDegree P) ≤ affineDegree T.ideal := by
    apply (sum_le_sum_of_subset_of_nonneg hPs (fun P _ _ => affineDegree_nonneg P)).trans
    simpa only [D, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hc (valueCutHigh_degree x b)
  have hcard : (Ps.card : ℚ) ≤ (a * T.equation.totalDegree : ℕ) :=
    (Nat.cast_le.mpr card_image_le).trans srcDegree
  calc
    _ ≤ (gapHigh A : ℚ) * ∑ P ∈ Ps, ((part P).card : ℚ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = ∑ P ∈ Ps, (gapHigh A : ℚ) * (part P).card := mul_sum ..
    _ ≤ _ := sum_le_sum hone
    _ = (errorsHigh A : ℚ) * (∑ P ∈ Ps, affineDegree P) + (gapHigh A : ℚ) * Ps.card := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm (Ps.card : ℚ)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hpdeg (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _))

/-! ## Section 4: Shortened Order-2 Charts at `kHigh = 133,721` -/

private theorem exponent_sufficient_high (length : ℕ) :
    TaylorExponentSufficient 2 length (exponent length) := by
  intro l
  have hl := l.isLt
  unfold exponent
  omega

private theorem top_monotone_high : Monotone (Pi.single (Fin.last 2) (1 : ℕ)) := by
  intro i j hij
  by_cases hi : i = Fin.last 2
  · have hj : j = Fin.last 2 := le_antisymm (Fin.le_last j) (hi ▸ hij)
    rw [hi, hj]
  · have hi₂ : i ≠ (2 : Fin 3) := hi
    have hw : (Pi.single (Fin.last 2) (1 : ℕ) : Fin 3 → ℕ) i = 0 := by simp [hi₂]
    rw [hw]
    exact Nat.zero_le _

private theorem lift_total_high {s : BoxShape} {G : CJ0_3.Equation} (hG : OrderTwoHigh s G)
    (g L : Polynomial K) :
    jetTotalDegree (CJ0_3.lifted (ShortenChart.transform g L G)) ≤ s.B := by
  rw [CJ0_3.lifted_total]
  have h := ShortenChart.transform_weight g L G 1 (fun _ _ _ => le_rfl)
  rw [CJ0_3.totalWeight_eq] at h
  exact h.trans hG.2.1

private theorem lift_index_high {s : BoxShape} {G : CJ0_3.Equation} (hG : OrderTwoHigh s G)
    (g L : Polynomial K) :
    (CJ0_3.lifted (ShortenChart.transform g L G)).weightedTotalDegree (Astra7.jetWeight 0 1 3) ≤ s.J := by
  rw [CJ0_3.lifted_weight, CJ0_3.indexWeight_eq]
  exact (ShortenChart.transform_weight g L G Fin.val (fun _ _ h => h)).trans hG.2.2.1

private theorem lift_top_high {s : BoxShape} {G : CJ0_3.Equation} (hG : OrderTwoHigh s G)
    (g L : Polynomial K) :
    (CJ0_3.lifted (ShortenChart.transform g L G)).degreeOf (some (Fin.last 2)) ≤ s.C := by
  change jetDegree (CJ0_3.lifted (ShortenChart.transform g L G)) (Fin.last 2) ≤ s.C
  rw [CJ0_3.lifted_top]
  have hw := ShortenChart.transform_weight g L G (Pi.single (Fin.last 2) 1) top_monotone_high
  have he : (fun v : Option (Fin 3) => v.elim 0 (Pi.single (Fin.last 2) 1)) =
      Pi.single (some (Fin.last 2)) (1 : ℕ) := by
    funext v
    cases v <;> simp [Pi.single_apply]
  rw [he, weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at hw
  exact hw.trans hG.2.2.2

private def basisPolynomialHigh (L : Polynomial K) (j : ℕ) : Polynomial Geo :=
  L.map embed * (Polynomial.X - Polynomial.C center) ^ j

private def rawDenominatorHigh (length : ℕ) (G : CJ0_3.Equation) : InitialRing 2 :=
  CJ0_3.initialSep G ^ exponent length

private def rawNumeratorHigh (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation)
    (i : Fin kHigh) : InitialRing 2 :=
  MvPolynomial.C ((g.map embed).coeff i.val) * rawDenominatorHigh length G +
    ∑ l : Fin length, MvPolynomial.C ((basisPolynomialHigh L l.val).coeff i.val) *
      commonTaylorNumerator center (CJ0_3.lifted G) (exponent length) l.val

def chartShortHigh (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation) (E : InitialRing 2) :
    ChartHigh 2 :=
  ⟨E, ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L)
      (rawDenominatorHigh length (ShortenChart.transform g L G)),
    fun i => ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L)
      (rawNumeratorHigh length g L (ShortenChart.transform g L G) i)⟩

private theorem rawDenominatorHigh_band (s : BoxShape) (length : ℕ) (hK : 3 ≤ length)
    (g L : Polynomial K) (G : CJ0_3.Equation) (hG : OrderTwoHigh s G) :
    InBandHigh s length (rawDenominatorHigh length (ShortenChart.transform g L G)) := by
  let Q := CJ0_3.lifted (ShortenChart.transform g L G)
  have hb : (initialJetSeparant center Q).totalDegree ≤ s.B - 1 :=
    (totalDegree_initialJetSeparant_le center Q).trans
      (Nat.sub_le_sub_right (lift_total_high hG g L) 1)
  have hi : (initialJetSeparant center Q).weightedTotalDegree Fin.val ≤ s.J - 2 := by
    simpa only [CJ0_3.coeffWeight_eq, zero_add, one_mul] using
      (Astra7.initialSeparant_weight 0 1 center Q).trans
        (Nat.sub_le_sub_right (lift_index_high hG g L) (0 + 1 * 2))
  have ht : (initialJetSeparant center Q).degreeOf (Fin.last 2) ≤ s.C - 1 :=
    (degreeOf_initialJetSeparant_le center Q).trans (Nat.sub_le_sub_right (lift_top_high hG g L) 1)
  have hindex : (initialJetSeparant center Q ^ exponent length).weightedTotalDegree Fin.val ≤
      indexCap s length :=
    ((weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ hi)).trans (by
      unfold indexCap; omega)
  refine ⟨((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hb)).trans (by unfold totalCap; omega),
    hindex, le_min ?_ (CJ0_3.degreeOf_top_of_index hindex)⟩
  exact ((degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ ht)).trans (by omega)

private theorem rawCenteredHigh_band (s : BoxShape) (hs : BoxOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : Polynomial K) (G : CJ0_3.Equation) (hG : OrderTwoHigh s G) (l : Fin length) :
    InBandHigh s length
      (commonTaylorNumerator center (CJ0_3.lifted (ShortenChart.transform g L G))
        (exponent length) l.val) := by
  let Q := CJ0_3.lifted (ShortenChart.transform g L G)
  have hlK := l.isLt
  have hJ := hs.index_top
  have hC := hs.top_pos
  have hi := Astra7.commonTaylor_weight 0 1 s.J length (exponent length) center Q
    (exponent_sufficient_high length) (by omega) (lift_index_high hG g L) l
  have hindex : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
      indexCap s length := by
    have h : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
        exponent length * (s.J - 2) + l.val := by
      simpa only [CJ0_3.coeffWeight_eq, zero_add, one_mul, add_zero] using hi
    exact h.trans (by unfold indexCap; omega)
  refine ⟨?_, hindex, le_min ?_ (CJ0_3.degreeOf_top_of_index hindex)⟩
  · exact (totalDegree_commonTaylorNumerator_le center Q (exponent_sufficient_high length l)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (lift_total_high hG g L) 1)) 1)
  · have hl : l.val - 1 ≤ length - 2 := by omega
    apply (CJ0_3_2.commonTaylor_top center Q hs.top_pos (lift_top_high hG g L)
      (exponent_sufficient_high length) l).trans
    rw [Nat.add_sub_assoc (by omega : 2 ≤ length)]
    exact Nat.add_le_add_left hl _

private theorem rawNumeratorHigh_band (s : BoxShape) (hs : BoxOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : Polynomial K) (G : CJ0_3.Equation) (hG : OrderTwoHigh s G) (i : Fin kHigh) :
    InBandHigh s length (rawNumeratorHigh length g L (ShortenChart.transform g L G) i) := by
  let V := CJ0_4.bandSpace (totalCap s length) (indexCap s length) (topCap s length)
  have hmem {P : InitialRing 2} (hp : InBandHigh s length P) : P ∈ V := CJ0_4.mem_bandSpace.mpr hp
  have hc (a : Geo) {P : InitialRing 2} (hp : InBandHigh s length P) : MvPolynomial.C a * P ∈ V := by
    rw [← MvPolynomial.smul_eq_C_mul]
    exact V.smul_mem _ (hmem hp)
  suffices h : rawNumeratorHigh length g L (ShortenChart.transform g L G) i ∈ V from
    CJ0_4.mem_bandSpace.mp h
  unfold rawNumeratorHigh
  exact V.add_mem (hc _ (rawDenominatorHigh_band s length hK g L G hG))
    (V.sum_mem fun l _ => hc _ (rawCenteredHigh_band s hs length hK g L G hG l))

private theorem inverse_band_high (s : BoxShape) (length : ℕ) (g L : Polynomial K) {P : InitialRing 2}
    (hp : InBandHigh s length P) :
    InBandHigh s length (ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) P) := by
  have hb := ShortenChart.inverse_weight (1 : Fin 3 → ℕ) (fun _ _ _ => le_rfl)
    (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) P
  have hi := ShortenChart.inverse_weight Fin.val (fun _ _ h => h)
    (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) P
  have ht := ShortenChart.inverse_weight (Pi.single (Fin.last 2) 1) top_monotone_high
    (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) P
  simp only [weightedTotalDegree_one] at hb
  simp only [weightedTotalDegree_piSingle] at ht
  exact ⟨hb.trans hp.1, hi.trans hp.2.1, ht.trans hp.2.2⟩

private theorem chartShortHigh_band (s : BoxShape) (hs : BoxOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : Polynomial K) (G : CJ0_3.Equation) (hG : OrderTwoHigh s G) (E : InitialRing 2) :
    ShortBandHigh s length (chartShortHigh length g L G E) :=
  ⟨inverse_band_high s length g L (rawDenominatorHigh_band s length hK g L G hG),
    fun i => inverse_band_high s length g L (rawNumeratorHigh_band s hs length hK g L G hG i)⟩

private theorem denominator_eval_high (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation)
    (E : InitialRing 2) (u : Fin 3 → Geo) (hL : L ≠ 0) :
    MvPolynomial.eval u (chartShortHigh length g L G E).denominator =
      (CJ0_3.nativeJet L 0 * MvPolynomial.eval u (CJ0_3.initialSep G)) ^ exponent length := by
  change MvPolynomial.eval u (ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L)
    (rawDenominatorHigh length (ShortenChart.transform g L G))) = _
  rw [ShortenChart.eval_inverse, rawDenominatorHigh, map_pow, ShortenChart.transform_initialSep,
    map_mul, MvPolynomial.eval_C, ShortenChart.eval_affine,
    ShortenChart.triangular_inverse _ _ _ (ShortenChart.nativeJet_zero_ne hL)]

private theorem denominator_regular_high (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation)
    (E : InitialRing 2) (hL : L ≠ 0) (hE : Irreducible E) (hreg : ¬ E ∣ CJ0_3.initialSep G) :
    ¬ E ∣ (chartShortHigh length g L G E).denominator := by
  have he : (chartShortHigh length g L G E).denominator =
      MvPolynomial.C (CJ0_3.nativeJet L 0 ^ exponent length) *
        (CJ0_3.initialSep G) ^ exponent length := by
    apply MvPolynomial.funext
    intro u
    rw [denominator_eval_high length g L G E u hL, map_mul, MvPolynomial.eval_C, map_pow, mul_pow]
  rw [he]
  have hu : IsUnit (MvPolynomial.C (CJ0_3.nativeJet L 0 ^ exponent length) : InitialRing 2) :=
    ((isUnit_iff_ne_zero).mpr (pow_ne_zero _ (ShortenChart.nativeJet_zero_ne hL))).map MvPolynomial.C
  intro h
  have hh := (hE.prime.dvd_or_dvd h).resolve_left (fun hd => hE.not_isUnit (isUnit_of_dvd_unit hd hu))
  exact hreg (hE.prime.dvd_of_dvd_pow hh)

private theorem reconstruct_basis_high (length : ℕ) (L : Polynomial K) (G : CJ0_3.Equation)
    (u : Fin 3 → Geo) :
    L.map embed * rationalTaylorPolynomial center (CJ0_3.lifted G) length u =
      ∑ l : Fin length, Polynomial.C (rationalTaylorCoefficient center (CJ0_3.lifted G) u l.val) *
        basisPolynomialHigh L l.val := by
  rw [rationalTaylorPolynomial, Polynomial.centeredCoefficientPrefix, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.taylor_monomial, map_neg, ← sub_eq_add_neg]
  unfold basisPolynomialHigh
  ring

private theorem raw_output_high (length : ℕ) (g L : Polynomial K) (G : CJ0_3.Equation)
    (u : Fin 3 → Geo) (hsep : MvPolynomial.eval u (CJ0_3.initialSep G) ≠ 0) (i : Fin kHigh) :
    MvPolynomial.eval u (rawNumeratorHigh length g L G i) /
      MvPolynomial.eval u (rawDenominatorHigh length G) =
      (g.map embed + L.map embed * rationalTaylorPolynomial center (CJ0_3.lifted G) length u).coeff i.val := by
  have hpow : MvPolynomial.eval u (CJ0_3.initialSep G) ^ exponent length ≠ 0 := pow_ne_zero _ hsep
  rw [reconstruct_basis_high, Polynomial.coeff_add, Polynomial.finsetSum_coeff, rawNumeratorHigh,
    map_add, add_div, map_mul, MvPolynomial.eval_C, rawDenominatorHigh, map_pow,
    mul_div_cancel_right₀ _ hpow, map_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.coeff_C_mul, map_mul, MvPolynomial.eval_C, ← MvPolynomial.aeval_eq_eval (f := u),
    aeval_commonTaylorNumerator center (CJ0_3.lifted G) u (exponent_sufficient_high length l) hsep]
  change _ * (MvPolynomial.eval u (CJ0_3.initialSep G) ^ exponent length * _) /
    MvPolynomial.eval u (CJ0_3.initialSep G) ^ exponent length = _
  field_simp

private theorem chartShortHigh_output (length : ℕ) (hK : 3 ≤ length) (g L : Polynomial K)
    (G : CJ0_3.Equation) (E : InitialRing 2) (u : Fin 3 → Geo)
    (hu : MvPolynomial.eval u (chartShortHigh length g L G E).denominator ≠ 0) (i : Fin kHigh) :
    (chartShortHigh length g L G E).output u i =
      (g.map embed + L.map embed * rationalTaylorPolynomial center
        (CJ0_3.lifted (ShortenChart.transform g L G)) length
        (ShortenChart.inverseJet (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) u)).coeff i.val := by
  let v := ShortenChart.inverseJet (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) u
  have hv : MvPolynomial.eval v (CJ0_3.initialSep (ShortenChart.transform g L G)) ≠ 0 := by
    intro hh
    apply hu
    change MvPolynomial.eval u (ShortenChart.inverseMap (CJ0_3.nativeJet g) (CJ0_3.nativeJet L)
      (rawDenominatorHigh length (ShortenChart.transform g L G))) = 0
    rw [ShortenChart.eval_inverse, rawDenominatorHigh, map_pow, hh, zero_pow]
    unfold exponent
    omega
  rw [ChartHigh.output, chartShortHigh, ShortenChart.eval_inverse, ShortenChart.eval_inverse]
  exact raw_output_high length g L (ShortenChart.transform g L G) v hv i

private theorem geoJet_affine_high (g L h : Polynomial Geo) :
    polynomialJet (d := 2) center (g + L * h) =
      ShortenChart.triangular (polynomialJet center g) (polynomialJet center L)
        (polynomialJet center h) := by
  funext i
  change Polynomial.evalRingHom center (ShortenChart.derivatives (g + L * h) i) =
    ShortenChart.triangular (Polynomial.evalRingHom center ∘ ShortenChart.derivatives g)
      (Polynomial.evalRingHom center ∘ ShortenChart.derivatives L)
      (Polynomial.evalRingHom center ∘ ShortenChart.derivatives h) i
  rw [ShortenChart.derivatives_affine]
  exact ShortenChart.map_triangular (Polynomial.evalRingHom center) _ _ _ i

private theorem natDegree_lt_any {F : Type*} [Field F] {P : Polynomial F} {b : ℕ} (hb : 0 < b)
    (hp : P.degree < b) : P.natDegree < b := by
  by_cases hz : P = 0
  · simpa [hz] using hb
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp

private theorem reconstruction_degree_high (length : ℕ) (hK : 3 ≤ length) (g L : Polynomial K)
    (hg : g.degree < kHigh) (hsum : L.natDegree + length ≤ kHigh) (G : CJ0_3.Equation)
    (u : Fin 3 → Geo) :
    (g.map embed + L.map embed * rationalTaylorPolynomial center (CJ0_3.lifted G) length u).degree <
      kHigh := by
  let U := rationalTaylorPolynomial center (CJ0_3.lifted G) length u
  have hU : U.natDegree < length :=
    natDegree_lt_any (by omega) (Polynomial.degree_centeredCoefficientPrefix_lt _ _ _)
  have hg' : (g.map embed).natDegree < kHigh :=
    Polynomial.natDegree_map_le.trans_lt (natDegree_lt_any (by decide) hg)
  have hm : (L.map embed * U).natDegree < kHigh :=
    (Polynomial.natDegree_mul_le).trans_lt
      ((Nat.add_lt_add_of_le_of_lt Polynomial.natDegree_map_le hU).trans_le hsum)
  have hh : (g.map embed + L.map embed * U).natDegree < kHigh :=
    (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hg' hm)
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hh)

private theorem chartShortHigh_ok (length : ℕ) (hK : 3 ≤ length) (g L : Polynomial K) (hL : L ≠ 0)
    (hg : g.degree < kHigh) (hsum : L.natDegree + length ≤ kHigh) (G : CJ0_3.Equation)
    (E : InitialRing 2) (hE : Irreducible E) (hreg : ¬ E ∣ CJ0_3.initialSep G) :
    ChartOKHigh (chartShortHigh length g L G E) := by
  refine ⟨hE, denominator_regular_high length g L G E hL hE hreg, ?_⟩
  intro u hu j
  let v := ShortenChart.inverseJet (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) u
  let U := rationalTaylorPolynomial center (CJ0_3.lifted (ShortenChart.transform g L G)) length v
  let P := g.map embed + L.map embed * U
  have hcoeff : (chartShortHigh length g L G E).output u = (fun i : Fin kHigh => P.coeff i.val) := by
    funext i
    exact chartShortHigh_output length hK g L G E u hu.2 i
  rw [hcoeff, show readJetHigh (fun i : Fin kHigh => P.coeff i.val) j.val =
    (polynomialJet (d := 2) center P) j from CJ0_3.readJet_eq P
      (reconstruction_degree_high length hK g L hg hsum (ShortenChart.transform g L G) v) j.val]
  have hU : polynomialJet (d := 2) center U = v :=
    polynomialJet_rationalTaylorPolynomial center (CJ0_3.lifted (ShortenChart.transform g L G))
      (by omega) v
  change (polynomialJet (d := 2) center (g.map embed + L.map embed * U)) j = u j
  rw [geoJet_affine_high, hU]
  exact congrFun (ShortenChart.triangular_inverse (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) u
    (ShortenChart.nativeJet_zero_ne hL)) j

private theorem chartShortHigh_contains (length : ℕ) (hK : 3 ≤ length) (hk : length ≤ kHigh)
    (g L : Polynomial K) (hL : L ≠ 0) (G : CJ0_3.Equation) (E : InitialRing 2)
    {f h : Polynomial K} (hh : h.degree < length) (hf : f = g + L * h)
    (hsol : differentialSpecialization G f = 0)
    (hE : MvPolynomial.eval (CJ0_3.nativeJet f) E = 0)
    (hsep : MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0) :
    coeffPointHigh f ∈ (chartShortHigh length g L G E).imageSet := by
  have hL0 := ShortenChart.nativeJet_zero_ne hL
  have hu : MvPolynomial.eval (CJ0_3.nativeJet f) (chartShortHigh length g L G E).denominator ≠ 0 := by
    rw [denominator_eval_high length g L G E _ hL]
    exact pow_ne_zero _ (mul_ne_zero hL0 hsep)
  have hv : ShortenChart.inverseJet (CJ0_3.nativeJet g) (CJ0_3.nativeJet L) (CJ0_3.nativeJet f) =
      CJ0_3.nativeJet h := by
    rw [hf, ShortenChart.nativeJet_affine]
    exact ShortenChart.inverse_triangular _ _ _ hL0
  have hs : MvPolynomial.eval (CJ0_3.nativeJet h)
      (CJ0_3.initialSep (ShortenChart.transform g L G)) ≠ 0 := by
    rw [ShortenChart.transform_initialSep, map_mul, MvPolynomial.eval_C, ShortenChart.eval_affine,
      ← ShortenChart.nativeJet_affine, ← hf]
    exact mul_ne_zero hL0 hsep
  have hsol' : differentialSpecialization (CJ0_3.lifted (ShortenChart.transform g L G))
      (h.map embed) = 0 := by
    rw [CJ0_3.lifted, ← map_differentialSpecialization, ShortenChart.transform_spec, ← hf, hsol,
      Polynomial.map_zero]
  have hsep' : jetEvaluation (separant (CJ0_3.lifted (ShortenChart.transform g L G)) (Fin.last 2))
      center (CJ0_3.nativeJet h) ≠ 0 := by
    simpa only [CJ0_3.initialSep, ← MvPolynomial.aeval_eq_eval, aeval_initialJetSeparant] using hs
  let _ : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hbin (i : ℕ) (hlo : 2 < i) (hhi : i < length) : (i.choose 2 : Geo) ≠ 0 := by
    have hb := natCast_choose_ne_zero_of_ringChar (F := Geo)
      (D := kHigh) (s := 2) (Or.inr (by rw [ringChar.eq Geo p]; norm_num)) (i - 2) (by omega)
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hlo)] using hb
  have hrec := rationalTaylorPolynomial_polynomialJet center
    (CJ0_3.lifted (ShortenChart.transform g L G)) (h.map embed) hsol' hsep'
    (Polynomial.degree_map_le.trans_lt hh) hbin
  refine ⟨CJ0_3.nativeJet f, ⟨hE, hu⟩, ?_⟩
  funext i
  rw [chartShortHigh_output length hK g L G E _ hu, hv, CJ0_3.nativeJet, hrec,
    ← Polynomial.map_mul, ← Polynomial.map_add, ← hf, Polynomial.coeff_map]
  rfl

theorem shortenChart_high (s : BoxShape) (hs : BoxOK s) (G : CJ0_3.Equation)
    (hG : OrderTwoHigh s G) (E : InitialRing 2) (hE : Irreducible E)
    (_hEdvd : E ∣ CJ0_3.initial G) (hreg : ¬ E ∣ CJ0_3.initialSep G)
    (S : Finset Node) (hS : S.card + 3 ≤ kHigh) (w : Node → K) :
    ∃ T : ChartHigh 2, ChartOKHigh T ∧ T.equation = E ∧ ShortBandHigh s (kHigh - S.card) T ∧
      ∀ f : Polynomial K, f.degree < kHigh → differentialSpecialization G f = 0 →
        MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 →
        MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0 →
        (∀ i ∈ S, f.eval (node i) = w i) → coeffPointHigh f ∈ T.imageSet := by
  classical
  let g := Lagrange.interpolate S node w
  let L := FrobeniusLocator.locator node S
  let length := kHigh - S.card
  have hK : 3 ≤ length := by dsimp [length]; omega
  have hk : length ≤ kHigh := Nat.sub_le _ _
  have hL := (FrobeniusLocator.locator_monic node S).ne_zero
  have hLn : L.natDegree = S.card := FrobeniusLocator.locator_natDegree _ _
  have hx : Function.Injective node := ProximityPrize.Benchmark.IRSProfile.domain.injective
  have hg : g.degree < kHigh := (Lagrange.degree_interpolate_lt w hx.injOn).trans_le
    (by exact_mod_cast (show S.card ≤ kHigh by omega))
  have hsum : L.natDegree + length ≤ kHigh := by rw [hLn]; dsimp [length]; omega
  refine ⟨chartShortHigh length g L G E, chartShortHigh_ok length hK g L hL hg hsum G E hE hreg,
    rfl, chartShortHigh_band s hs length hK g L G hG E, ?_⟩
  intro f hf hroot hEroot hsep hits
  have hdiv : L ∣ f - g := FrobeniusLocator.Strata.locator_dvd_of_eval_zero node hx S _
    (fun i hi => by
      rw [Polynomial.eval_sub, hits i hi, show g.eval (node i) = w i from
        Lagrange.eval_interpolate_at_node w hx.injOn hi, sub_self])
  have hd : (f - g).degree < kHigh := (Polynomial.degree_sub_le _ _).trans_lt (max_lt hf hg)
  have hdN : (f - g).natDegree ≤ NHigh := by
    have hh := natDegree_lt_any (by decide) hd
    change _ < 133721 at hh
    change _ ≤ 133720
    omega
  have hS' : S.card ≤ NHigh := by
    change _ ≤ 133721 at hS
    change _ ≤ 133720
    omega
  obtain ⟨h, hdeg, he⟩ :=
    FrobeniusLocator.Strata.bounded_locator_quotient node S (f - g) NHigh hS' hdN hdiv
  have hf' : f = g + L * h := by rw [← he]; ring
  have hlen : NHigh - S.card + 1 = length := by
    dsimp [length]
    change _ ≤ 133721 at hS
    change 133720 - S.card + 1 = 133721 - S.card
    omega
  rw [hlen] at hdeg
  exact chartShortHigh_contains length hK hk g L hL G E hdeg hf' hroot hEroot hsep

/-! ## Section 5: Order-2 → Order-1 Elimination, Order-1 Charts, and Order-0 Exceptional Locus -/

private theorem eliminate_ne_zero_high {G : DifferentialPolynomial K 2} (hG : Irreducible G)
    (hchar : jetDegree G (Fin.last 2) < p) : CJ0_5.eliminate G ≠ 0 := by
  let P := Sol1.C57.topPresentation 1 G
  let c := P.natDegree
  have hi : Irreducible P :=
    (MulEquiv.irreducible_iff (Sol1.C57.topPresentation 1).toMulEquiv).mpr hG
  change (if c = 0 then P.coeff 0 else P.resultant P.derivative c (c - 1)) ≠ 0
  by_cases h : c = 0
  · have hn := leadingCoeff_ne_zero.mpr hi.ne_zero
    change P.coeff c ≠ 0 at hn
    simpa only [h, ite_true] using hn
  · have hlt : c < p := (Sol1.C57.topPresentation_degree 1 G).trans_lt hchar
    have hcast : (c : K) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hlt) (Nat.le_of_dvd (Nat.pos_of_ne_zero h)
        ((CharP.cast_eq_zero_iff K p c).mp hz))
    have hc : (c : DifferentialPolynomial K 1) ≠ 0 := by
      simpa only [map_natCast, map_zero] using (MvPolynomial.C_injective _ K).ne hcast
    have hder : P.derivative ≠ 0 := by
      intro hz
      have hindex : c - 1 + 1 = c := by omega
      have hz' := congrArg (fun R : Polynomial (DifferentialPolynomial K 1) => R.coeff (c - 1)) hz
      rw [coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one, hindex, coeff_zero] at hz'
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr hi.ne_zero) hc hz'
    simpa only [ite_eq_right h] using Polynomial.resultant_derivative_ne_zero_of_irreducible P hi hder

private theorem eliminate_root_high (G : DifferentialPolynomial K 2) (f : Polynomial K)
    (hG : differentialSpecialization G f = 0)
    (hsep : differentialSpecialization (separant G (Fin.last 2)) f = 0) :
    differentialSpecialization (CJ0_5.eliminate G) f = 0 := by
  let P := Sol1.C57.topPresentation 1 G
  let ψ := (differentialSpecializationHom (d := 1) f).toRingHom
  have he : P.eval₂ ψ (hasseDeriv 2 f) = 0 := (Sol1.C57.topPresentation_eval 1 G f).trans hG
  change ψ (if P.natDegree = 0 then P.coeff 0 else
    P.resultant P.derivative P.natDegree (P.natDegree - 1)) = 0
  by_cases hc : P.natDegree = 0
  · rw [ite_eq_left hc]
    have h := congrArg (fun R : Polynomial (DifferentialPolynomial K 1) =>
      R.eval₂ ψ (hasseDeriv 2 f)) (eq_C_of_natDegree_eq_zero hc)
    change P.eval₂ ψ (hasseDeriv 2 f) = _ at h
    rw [Polynomial.eval₂_C] at h
    exact h.symm.trans he
  · rw [ite_eq_right hc]
    have hd : P.derivative.eval₂ ψ (hasseDeriv 2 f) = 0 := by
      change (Sol1.C57.topPresentation 1 G).derivative.eval₂ ψ _ = 0
      rw [Sol1.C57.topPresentation_derivative, Sol1.C57.topPresentation_eval]
      exact hsep
    exact Sol1.C40Primitives.map_resultant_eq_zero_of_common_root ψ P P.derivative
      P.natDegree (P.natDegree - 1) le_rfl (natDegree_derivative_le P) (Or.inl hc)
      (hasseDeriv 2 f) he hd

private theorem input_total_high :
    CJ0_5.inputWeight 1 jetDegreeWeight = jetDegreeWeight := by
  funext v
  rcases v with _ | j
  · simp [CJ0_5.inputWeight]
  · induction j using Fin.lastCases with
    | last => simp only [CJ0_5.inputWeight, Sol1.C57.topVariableEquiv_top, Option.elim_none,
        jetDegreeWeight_some]
    | cast j => simp [CJ0_5.inputWeight]

private theorem input_index_high :
    CJ0_5.inputWeight 2 CJ0.indexWeight = CJ0.indexWeight := by
  funext v
  rcases v with _ | j
  · simp [CJ0_5.inputWeight, CJ0.indexWeight]
  · induction j using Fin.lastCases with
    | last =>
      rw [CJ0_5.inputWeight, Sol1.C57.topVariableEquiv_top]
      rfl
    | cast j => simp [CJ0_5.inputWeight, CJ0.indexWeight]

private theorem output_index_high :
    CJ0.indexWeight = (Pi.single (some (Fin.last 1)) 1 : JetVariable 1 → ℕ) := by
  funext v
  rcases v with _ | j
  · simp [CJ0.indexWeight]
  · induction j using Fin.lastCases with
    | last =>
      change 1 = (Pi.single (some (Fin.last 1)) 1 : JetVariable 1 → ℕ) (some (Fin.last 1))
      simp only [Pi.single_eq_same]
    | cast j =>
      have hne : some j.castSucc ≠ some (Fin.last 1) :=
        (Option.some_injective _).ne (Fin.castSucc_ne_last j)
      rw [Pi.single_eq_of_ne hne]
      change j.val = 0
      omega

private theorem eliminate_orderTwo_high (s : BoxShape) (hs : BoxOK s)
    (Q : DifferentialPolynomial K 2) (hQ : OrderTwoHigh s Q) :
    ∃ Q₁ : DifferentialPolynomial K 1, OrderOneHigh s Q₁ ∧
      ∀ f : Polynomial K, differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
        differentialSpecialization Q₁ f = 0 := by
  classical
  obtain ⟨hq, hb, hj, hc⟩ := hQ
  dsimp [boxToSource] at hb hj hc
  let _ : StrongNormalizationMonoid (DifferentialPolynomial K 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := UniqueFactorizationMonoid.normalizedFactors Q
  let T := A.toFinset
  let c (G : DifferentialPolynomial K 2) := jetDegree G (Fin.last 2)
  let Q₁ : DifferentialPolynomial K 1 := ∏ G ∈ T, CJ0_5.eliminate G
  have hmem (G) (hG : G ∈ T) : G ∈ A := Multiset.mem_toFinset.mp hG
  have hirr (G) (hG : G ∈ T) : Irreducible G :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor G (hmem G hG)
  have hdvd : (∏ G ∈ T, G) ∣ Q :=
    (Multiset.toFinset_prod_dvd_prod A).trans
      (UniqueFactorizationMonoid.prod_normalizedFactors hq).dvd
  have hcSum : ∑ G ∈ T, c G ≤ s.C := by
    let w : JetVariable 2 → ℕ := Pi.single (some (Fin.last 2)) 1
    have hh := sum_weightedTotalDegree_le_of_prod_dvd w T id hq hdvd
    exact (by simpa only [w, id_eq, weightedTotalDegree_piSingle, jetDegree, c] using hh :
      (∑ G ∈ T, c G) ≤ jetDegree Q (Fin.last 2)).trans hc
  have h2 : 2 ≤ s.B := by have := hs.top_pos; have := hs.index_top; have := hs.total_index; omega
  have hC : s.C < p := calc
    s.C ≤ s.B := by have := hs.index_top; have := hs.total_index; omega
    _ = s.B * 1 := (Nat.mul_one _).symm
    _ ≤ s.B * (s.B - 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ max NHigh (s.B * (s.B - 1)) := le_max_right _ _
    _ < p := hs.characteristic
  have he (G) (hG : G ∈ T) : CJ0_5.eliminate G ≠ 0 :=
    eliminate_ne_zero_high (hirr G hG)
      (((Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) hG).trans hcSum).trans_lt hC)
  have hweight (a B : ℕ) (w : JetVariable 1 → ℕ)
      (hB : a * s.C ≤ B) (hQw : Q.weightedTotalDegree (CJ0_5.inputWeight a w) ≤ B) :
      Q₁.weightedTotalDegree w ≤ max B ((2 * s.C - 1) * B - a * s.C ^ 2) := by
    rw [show Q₁ = ∏ G ∈ T, CJ0_5.eliminate G from rfl, weightedTotalDegree_prod w T _ he]
    apply CJ0_5.aggregate T (fun G => G.weightedTotalDegree (CJ0_5.inputWeight a w)) c
      (fun G => (CJ0_5.eliminate G).weightedTotalDegree w) B a s.C
      ((sum_weightedTotalDegree_le_of_prod_dvd _ T id hq hdvd).trans hQw) hcSum hB
    · exact fun G _ => (CJ0_5.eliminate_weight a w G).1
    · exact fun G _ => (CJ0_5.eliminate_weight a w G).2.1
    · exact fun G _ => (CJ0_5.eliminate_weight a w G).2.2
  refine ⟨Q₁, ⟨Finset.prod_ne_zero_iff.mpr he, ?_, ?_⟩, ?_⟩
  · simpa only [jetTotalDegree, OrderOneHigh, CJ0.H, boxToSource, one_mul] using
      hweight 1 s.B jetDegreeWeight (by have := hs.index_top; have := hs.total_index; omega)
        (by simpa only [input_total_high, jetTotalDegree] using hb)
  · have hh := hweight 2 s.J CJ0.indexWeight (by have := hs.index_top; omega)
      (by rwa [input_index_high])
    simpa only [output_index_high, weightedTotalDegree_piSingle, jetDegree, OrderOneHigh, CJ0.I₁,
      boxToSource] using hh
  · intro f hf hsing
    let ψ := (differentialSpecializationHom (d := 2) f).toRingHom
    change ψ Q = 0 at hf
    have hz := map_dvd ψ (UniqueFactorizationMonoid.prod_normalizedFactors hq).symm.dvd
    change ψ Q ∣ ψ A.prod at hz
    rw [hf, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨G, hG, hg⟩ := hz
    have hgT : G ∈ T := Multiset.mem_toFinset.mpr hG
    have hsep : differentialSpecialization (separant G (Fin.last 2)) f = 0 := by
      by_contra hne
      exact hsing ⟨G, hirr G hgT, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hG, hg, hne⟩
    have hroot := eliminate_root_high G f hg hsep
    change (differentialSpecializationHom (d := 1) f).toRingHom (∏ G ∈ T, CJ0_5.eliminate G) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero hgT hroot

/-! ### Order-1 Charts at `kHigh = 133,721` -/

private def denominator1High (G : DifferentialPolynomial K 1) : InitialRing 1 :=
  CJ0_6.sep G ^ t1High

private theorem exponent1_sufficient_high : TaylorExponentSufficient 1 kHigh t1High :=
  taylorExponentSufficient_firstOrder_tight NHigh

private def shiftedWeightHigh (z : Geo) (l i : ℕ) : Geo :=
  (l.choose i : Geo) * z ^ (l - i)

private theorem coeff_taylor_sum_high {m : ℕ} (z : Geo) (a : Fin m → Geo) (i : ℕ) :
    (Polynomial.taylor z (∑ l : Fin m, Polynomial.monomial l.val (a l))).coeff i =
      ∑ l : Fin m, shiftedWeightHigh z l.val i * a l := by
  rw [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  unfold shiftedWeightHigh
  ring

private theorem readJetHigh_coeff {P : Polynomial Geo} (hP : P.degree < kHigh) (i : ℕ) :
    readJetHigh (fun j => P.coeff j.val) i = (Polynomial.taylor center P).coeff i := by
  have hnat : P.natDegree < kHigh := natDegree_lt_any (by decide) hP
  have hsum : P = ∑ l : Fin kHigh, Polynomial.monomial l.val (P.coeff l.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.monomial j (P.coeff j))]
    exact P.as_sum_range' _ hnat
  exact (coeff_taylor_sum_high center (fun j : Fin kHigh => P.coeff j.val) i).symm.trans
    (congrArg (fun P : Polynomial Geo => (Polynomial.taylor center P).coeff i) hsum.symm)

private def padded1High (G : DifferentialPolynomial K 1) (l : Fin kHigh) : InitialRing 1 :=
  commonTaylorNumerator center (CJ0_6.centeredEquation G) t1High l.val

private def combine1High {m : ℕ} (P : Fin m → InitialRing 1) (i : ℕ) : InitialRing 1 :=
  ∑ l : Fin m, MvPolynomial.C (shiftedWeightHigh (-center) l.val i) * P l

private def chart1High (G : DifferentialPolynomial K 1) (g : InitialRing 1) : ChartHigh 1 :=
  ⟨g, denominator1High G, fun i => combine1High (padded1High G) i.val⟩

private theorem denominator1High_band (s : BoxShape) (G : DifferentialPolynomial K 1)
    (hT : jetTotalDegree G ≤ HHigh s) (hI : jetDegree G (Fin.last 1) ≤ I1High s) :
    inBand1High s (denominator1High G) := by
  have ht : (CJ0_6.sep G).totalDegree ≤ HHigh s - 1 :=
    (totalDegree_initialJetSeparant_le center (CJ0_6.centeredEquation G)).trans
      (Nat.sub_le_sub_right ((jetTotalDegree_map_le embed G).trans hT) 1)
  have hi : (CJ0_6.sep G).degreeOf (Fin.last 1) ≤ I1High s - 1 := by
    rw [CJ0_6.sep, ← pderiv_last_initialJetEquation]
    exact (MvPolynomial.degreeOf_pderiv_le_sub_one _ _).trans
      (Nat.sub_le_sub_right ((CJ0_6.initial_top G).trans hI) 1)
  have hdt : (denominator1High G).totalDegree ≤ a1High s :=
    (MvPolynomial.totalDegree_pow _ _).trans
      ((Nat.mul_le_mul_left _ ht).trans (Nat.le_add_left _ _))
  refine ⟨hdt, le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans hdt) ?_⟩
  exact (MvPolynomial.degreeOf_pow_le _ _ _).trans
    ((Nat.mul_le_mul_left _ hi).trans (by unfold kHigh; omega))

private theorem padded1High_band (s : BoxShape) (G : DifferentialPolynomial K 1)
    (hT : jetTotalDegree G ≤ HHigh s) (hI : jetDegree G (Fin.last 1) ≤ I1High s) (l : Fin kHigh) :
    inBand1High s (padded1High G l) := by
  have htd : (padded1High G l).totalDegree ≤ a1High s :=
    (totalDegree_commonTaylorNumerator_le center (CJ0_6.centeredEquation G)
      (exponent1_sufficient_high l)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left t1High
        (Nat.sub_le_sub_right ((jetTotalDegree_map_le embed G).trans hT) 1)) 1)
  refine ⟨htd, le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans htd) ?_⟩
  have hm : (CJ0_6.centeredEquation G).degreeOf (some (1 : Fin 2)) ≤ I1High s := by
    rw [show (1 : Fin 2) = Fin.last 1 from rfl]
    apply le_trans _ hI
    simpa only [CJ0_6.centeredEquation, jetDegree, MvPolynomial.degreeOf_def] using
      (Multiset.count_le_of_le (some (Fin.last 1))
        (MvPolynomial.degrees_map_le (p := G) (f := embed)))
  exact (degreeOf_commonTaylorNumerator_firstOrder_le center (CJ0_6.centeredEquation G)
    (I1High s) kHigh t1High exponent1_sufficient_high hm l).trans (by
      have hl := l.isLt
      omega)

private theorem combine1High_band (s : BoxShape) {m : ℕ} (P : Fin m → InitialRing 1)
    (h : ∀ l, inBand1High s (P l)) (i : ℕ) : inBand1High s (combine1High P i) := by
  unfold inBand1High combine1High
  constructor
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro l _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C, zero_add] using (h l).1)
  · apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro l _
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by
      simpa only [MvPolynomial.degreeOf_C, zero_add] using (h l).2)

private theorem eval_combine1High {m : ℕ} (u : Fin 2 → Geo) (P : Fin m → InitialRing 1)
    (d : Geo) (hd : d ≠ 0) (a : Fin m → Geo) (h : ∀ l, MvPolynomial.eval u (P l) = d * a l)
    (i : ℕ) : MvPolynomial.eval u (combine1High P i) / d =
      (Polynomial.taylor (-center) (∑ l : Fin m, Polynomial.monomial l.val (a l))).coeff i := by
  rw [coeff_taylor_sum_high, combine1High, map_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul, MvPolynomial.eval_C, h]
  field_simp

set_option maxRecDepth 200000 in
private theorem output1High_coeff (G : DifferentialPolynomial K 1) (g : InitialRing 1)
    (u : Fin 2 → Geo) (hu : MvPolynomial.eval u (denominator1High G) ≠ 0) (i : Fin kHigh) :
    (chart1High G g).output u i =
      (rationalTaylorPolynomial center (CJ0_6.centeredEquation G) kHigh u).coeff i.val := by
  have hS : MvPolynomial.aeval u (CJ0_6.sep G) ≠ 0 := by
    intro hz
    apply hu
    change MvPolynomial.eval u (CJ0_6.sep G ^ t1High) = 0
    rw [map_pow, ← MvPolynomial.aeval_eq_eval, hz, zero_pow (by decide : t1High ≠ 0)]
  have he (l : Fin kHigh) : MvPolynomial.eval u (padded1High G l) =
      MvPolynomial.eval u (denominator1High G) *
        rationalTaylorCoefficient center (CJ0_6.centeredEquation G) u l.val := by
    simpa only [padded1High, denominator1High, CJ0_6.sep, map_pow, MvPolynomial.aeval_eq_eval] using
      aeval_commonTaylorNumerator center (CJ0_6.centeredEquation G) u
        (exponent1_sufficient_high l) hS
  simp only [ChartHigh.output, chart1High, rationalTaylorPolynomial,
    Polynomial.centeredCoefficientPrefix]
  exact eval_combine1High (m := kHigh) u (padded1High G) (MvPolynomial.eval u (denominator1High G))
    hu (fun l : Fin kHigh => rationalTaylorCoefficient center (CJ0_6.centeredEquation G) u l.val)
    he i.val

set_option maxRecDepth 200000 in
private theorem chart1High_ok (G : DifferentialPolynomial K 1) {g : InitialRing 1}
    (hg : Irreducible g) (hS : ¬ g ∣ denominator1High G) : ChartOKHigh (chart1High G g) := by
  refine ⟨hg, hS, ?_⟩
  intro u hu j
  have hd : MvPolynomial.eval u (denominator1High G) ≠ 0 := hu.2
  let P := rationalTaylorPolynomial center (CJ0_6.centeredEquation G) kHigh u
  have hout : (chart1High G g).output u = fun i => P.coeff i.val := by
    funext i
    exact output1High_coeff G g u hd i
  have hP : P.degree < kHigh := Polynomial.degree_centeredCoefficientPrefix_lt _ _ _
  rw [hout, readJetHigh_coeff hP]
  have h := congrFun (polynomialJet_rationalTaylorPolynomial center (CJ0_6.centeredEquation G)
    (show 1 < kHigh by decide) u) j
  change Polynomial.hasseCoeffAt center j.val P = u j at h
  rw [Polynomial.hasseCoeffAt_apply, ← Polynomial.taylor_coeff] at h
  exact h

private def centerMapHigh : Polynomial K →+* Geo :=
  (algebraMap FX Geo).comp (algebraMap (Polynomial K) FX)

private theorem centerMapHigh_injective : Function.Injective centerMapHigh :=
  (algebraMap FX Geo).injective.comp (IsFractionRing.injective (Polynomial K) FX)

private theorem eval_mapped_at_center_high (f : Polynomial K) :
    (f.map embed).eval center = centerMapHigh f := by
  rw [Polynomial.eval_map]
  change Polynomial.eval₂RingHom embed center f = centerMapHigh f
  congr 1
  apply Polynomial.ringHom_ext
  · intro a; simp [centerMapHigh, embed]
  · simp [centerMapHigh, center]

private theorem eval_mark_high (G : DifferentialPolynomial K 1) (f : Polynomial K) :
    jetEvaluation (CJ0_6.centeredEquation G) center (CJ0_6.mark f) =
      centerMapHigh (differentialSpecialization G f) := by
  rw [CJ0_6.mark, ← eval_differentialSpecialization, CJ0_6.centeredEquation,
    ← map_differentialSpecialization, eval_mapped_at_center_high]

private theorem sep_mark_high (G : DifferentialPolynomial K 1) (f : Polynomial K)
    (h : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    MvPolynomial.eval (CJ0_6.mark f) (CJ0_6.sep G) ≠ 0 := by
  rw [← MvPolynomial.aeval_eq_eval, CJ0_6.sep, aeval_initialJetSeparant, CJ0_6.centeredEquation,
    ← map_separant]
  exact fun hz => h (centerMapHigh_injective
    ((eval_mark_high _ _).symm.trans (hz.trans (map_zero _).symm)))

private theorem denominator1High_mark (G : DifferentialPolynomial K 1) (f : Polynomial K)
    (h : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    MvPolynomial.eval (CJ0_6.mark f) (denominator1High G) ≠ 0 := by
  rw [denominator1High, map_pow]
  exact pow_ne_zero _ (sep_mark_high G f h)

private theorem chart1High_contains (G : DifferentialPolynomial K 1) (g : InitialRing 1)
    (f : Polynomial K) (hf : f.degree < kHigh) (h : differentialSpecialization G f = 0)
    (hs : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0)
    (hg : MvPolynomial.eval (CJ0_6.mark f) g = 0) :
    coeffPointHigh f ∈ (chart1High G g).imageSet := by
  let _ : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hpiv : ∀ i : ℕ, 1 < i → i < kHigh → (i.choose 1 : Geo) ≠ 0 := by
    intro i hlo hhi hz
    rw [Nat.choose_one_right] at hz
    have hdiv := (CharP.cast_eq_zero_iff Geo p i).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (hhi.trans (by decide : kHigh < p))) hdiv
  have hsol : differentialSpecialization (CJ0_6.centeredEquation G) (f.map embed) = 0 := by
    rw [CJ0_6.centeredEquation, ← map_differentialSpecialization, h, Polynomial.map_zero]
  have hsep : jetEvaluation (separant (CJ0_6.centeredEquation G) (Fin.last 1)) center
      (CJ0_6.mark f) ≠ 0 := by
    rw [← aeval_initialJetSeparant, MvPolynomial.aeval_eq_eval]
    exact sep_mark_high G f hs
  have hdeg : (f.map embed).degree < kHigh := Polynomial.degree_map_le.trans_lt hf
  have hr := rationalTaylorPolynomial_polynomialJet center (CJ0_6.centeredEquation G)
    (f.map embed) hsol hsep hdeg hpiv
  refine ⟨CJ0_6.mark f, ⟨hg, denominator1High_mark G f hs⟩, ?_⟩
  funext i
  rw [output1High_coeff G g (CJ0_6.mark f) (denominator1High_mark G f hs), CJ0_6.mark, hr,
    Polynomial.coeff_map]
  rfl

private theorem root_of_associated_high {G G' : DifferentialPolynomial K 1} {f : Polynomial K}
    (ha : Associated G G') (hG : differentialSpecialization G f = 0)
    (hS : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    differentialSpecialization G' f = 0 ∧
      differentialSpecialization (separant G' (Fin.last 1)) f ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  let ev := differentialSpecializationHom f (d := 1)
  have hu : ev (u : DifferentialPolynomial K 1) ≠ 0 := (u.isUnit.map ev).ne_zero
  change ev G = 0 at hG
  change ev (separant G (Fin.last 1)) ≠ 0 at hS
  change ev (G * u) = 0 ∧ ev (separant (G * u) (Fin.last 1)) ≠ 0
  refine ⟨by rw [map_mul, hG, zero_mul], ?_⟩
  rw [separant, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hG, zero_mul, add_zero]
  exact mul_ne_zero hS hu

local instance : StrongNormalizationMonoid (InitialRing 1) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

private theorem root_in_factor_high {P : InitialRing 1} (hP : P ≠ 0) (u : Fin 2 → Geo)
    (h : MvPolynomial.eval u P = 0) :
    ∃ g ∈ UniqueFactorizationMonoid.normalizedFactors P, MvPolynomial.eval u g = 0 := by
  have hd := map_dvd (MvPolynomial.eval u)
    (UniqueFactorizationMonoid.prod_normalizedFactors hP).symm.dvd
  rw [h, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  exact hd

private theorem positive_total_high {g : InitialRing 1} (hg : Irreducible g) :
    1 ≤ g.totalDegree := by
  by_contra! h
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.lt_one_iff.mp h)
  have hcoef : g.coeff 0 ≠ 0 := fun hz => hg.ne_zero (by rw [hc, hz, map_zero])
  exact hg.not_isUnit (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
    ⟨g.coeff 0, isUnit_iff_ne_zero.mpr hcoef, hc⟩)

set_option maxRecDepth 200000 in
private theorem order_one_family_high (s : BoxShape) (_hs : BoxOK s)
    (Q : DifferentialPolynomial K 1) (hQ : OrderOneHigh s Q) :
    ∃ F : FamilyHigh 1, Family1High s F ∧
      ∀ f : Polynomial K, f.degree < kHigh → RegularRoot Q f →
        ∃ i, coeffPointHigh f ∈ (F.chart i).imageSet := by
  classical
  let _ : StrongNormalizationMonoid (DifferentialPolynomial K 1) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  let B (G : DifferentialPolynomial K 1) :=
    (UniqueFactorizationMonoid.normalizedFactors (CJ0_6.initial G)).toFinset.filter
      fun g => ¬ g ∣ denominator1High G
  let T := A.sigma B
  let n := T.card
  let e : Fin n ≃ ↥T := (Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let entry (i : Fin n) := (e i).val
  let F : FamilyHigh 1 := ⟨n, fun i => chart1High (entry i).1 (entry i).2⟩
  have hmember (i : Fin n) : (entry i).1 ∈ A ∧ (entry i).2 ∈ B (entry i).1 :=
    Finset.mem_sigma.mp (e i).property
  have hG (i : Fin n) : (entry i).1 ∣ Q :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (hmember i).1)
  have hg (i : Fin n) : Irreducible (entry i).2 ∧ ¬ (entry i).2 ∣ denominator1High (entry i).1 := by
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp (hmember i).2
    exact ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor _
      (Multiset.mem_toFinset.mp hm), hd⟩
  have hQ' : CJ0_6.initial Q ≠ 0 :=
    fun hz => hQ.1 (CJ0_6.initial_injective (hz.trans (map_zero CJ0_6.initial).symm))
  have hd : (∏ a ∈ T, a.2) ∣ CJ0_6.initial Q := by
    have hA : (∏ G ∈ A, G) ∣ Q :=
      (Multiset.toFinset_prod_dvd_prod _).trans
        (UniqueFactorizationMonoid.prod_normalizedFactors hQ.1).dvd
    have hm := map_dvd CJ0_6.initial hA
    rw [map_prod] at hm
    change (∏ a ∈ A.sigma B, a.2) ∣ CJ0_6.initial Q
    rw [Finset.prod_sigma]
    refine (Finset.prod_dvd_prod_of_dvd _ _ (fun G hGA => ?_)).trans hm
    have hne : CJ0_6.initial G ≠ 0 := ne_zero_of_dvd_ne_zero hQ'
      (map_dvd CJ0_6.initial (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
        (Multiset.mem_toFinset.mp hGA)))
    exact (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      ((Multiset.toFinset_prod_dvd_prod _).trans
        (UniqueFactorizationMonoid.prod_normalizedFactors hne).dvd)
  have heq (d : InitialRing 1 → ℕ) :
      (∑ i : Fin n, d (entry i).2) = ∑ a ∈ T, d a.2 := by
    calc
      _ = ∑ a : ↥T, d a.val.2 := e.sum_comp (fun a : ↥T => d a.val.2)
      _ = _ := Finset.sum_coe_sort T (fun a => d a.2)
  have ht : (∑ i : Fin n, (entry i).2.totalDegree) ≤ HHigh s := by
    rw [heq]
    have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd
      (1 : Fin 2 → ℕ) T (fun a => a.2) hQ' hd
    simp only [MvPolynomial.weightedTotalDegree_one] at h
    exact h.trans ((CJ0_6.initial_total Q).trans hQ.2.1)
  have hi : (∑ i : Fin n, (entry i).2.degreeOf (Fin.last 1)) ≤ I1High s := by
    rw [heq]
    have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd
      (Pi.single (Fin.last 1) 1) T (fun a => a.2) hQ' hd
    simp only [MvPolynomial.weightedTotalDegree_piSingle] at h
    exact h.trans ((CJ0_6.initial_top Q).trans hQ.2.2)
  have hn : n ≤ HHigh s := by
    calc
      n = ∑ _ : Fin n, 1 := by simp
      _ ≤ ∑ i : Fin n, (entry i).2.totalDegree :=
        Finset.sum_le_sum fun i _ => positive_total_high (hg i).1
      _ ≤ HHigh s := ht
  refine ⟨F, ⟨hn, fun i => chart1High_ok _ (hg i).1 (hg i).2, ht, hi, ?_⟩, ?_⟩
  · intro i
    have hT : jetTotalDegree (entry i).1 ≤ HHigh s :=
      (MvPolynomial.weightedTotalDegree_le_of_dvd jetDegreeWeight (hG i) hQ.1).trans hQ.2.1
    have hI : jetDegree (entry i).1 (Fin.last 1) ≤ I1High s := by
      have hb := MvPolynomial.weightedTotalDegree_le_of_dvd
        (Pi.single (some (Fin.last 1)) 1) (hG i) hQ.1
      simp only [MvPolynomial.weightedTotalDegree_piSingle] at hb
      exact hb.trans hQ.2.2
    exact ⟨denominator1High_band s _ hT hI, fun j : Fin kHigh =>
      combine1High_band s (m := kHigh) (padded1High (entry i).1)
        (padded1High_band s _ hT hI) j.val⟩
  · intro f hf hreg
    obtain ⟨G, hGir, hGdvd, hGroot, hGsep⟩ := hreg
    obtain ⟨G', hGA, hGassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hQ.1 hGir hGdvd
    obtain ⟨hroot, hsep⟩ := root_of_associated_high hGassoc hGroot hGsep
    have hne : CJ0_6.initial G' ≠ 0 := ne_zero_of_dvd_ne_zero hQ'
      (map_dvd CJ0_6.initial (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hGA))
    obtain ⟨g, hgM, hgroot⟩ := root_in_factor_high hne (CJ0_6.mark f) (CJ0_6.initial_mark G' f hroot)
    have hgden : ¬ g ∣ denominator1High G' := by
      intro hdvd
      have hm := map_dvd (MvPolynomial.eval (CJ0_6.mark f)) hdvd
      rw [hgroot, zero_dvd_iff] at hm
      exact denominator1High_mark G' f hsep hm
    have ht' : (⟨G', g⟩ : Sigma fun _ : DifferentialPolynomial K 1 => InitialRing 1) ∈ T :=
      Finset.mem_sigma.mpr ⟨Multiset.mem_toFinset.mpr hGA,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hgM, hgden⟩⟩
    let a : ↥T := ⟨⟨G', g⟩, ht'⟩
    refine ⟨e.symm a, ?_⟩
    change coeffPointHigh f ∈ (chart1High (e (e.symm a)).val.1 (e (e.symm a)).val.2).imageSet
    rw [e.apply_symm_apply]
    exact chart1High_contains G' g f hf hroot hsep hgroot

/-! ### Order-1 Image Degrees (`CJ0_7` at `kHigh = 133,721`) -/

private theorem equationIdeal_prime_high {r : ℕ} {T : ChartHigh r} (hT : ChartOKHigh T) :
    (sourceIdealHigh T).IsPrime :=
  (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime

private theorem mem_locus_iff_high {r : ℕ} (T : ChartHigh r) (u : Fin (r + 1) → Geo) :
    u ∈ T.locus ↔ u ∈ zeroLocus Geo (sourceIdealHigh T) ∧ MvPolynomial.aeval u T.denominator ≠ 0 := by
  rw [sourceIdealHigh, zeroLocus_span]
  simp only [ChartHigh.locus, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, aeval_eq_eval]

private theorem locus_ideal_high {r : ℕ} {T : ChartHigh r} (hT : ChartOKHigh T) :
    vanishingIdeal Geo T.locus = sourceIdealHigh T := by
  have hp := equationIdeal_prime_high hT
  ext g
  rw [mem_vanishingIdeal_iff]
  constructor
  · intro hg
    have hmul : T.denominator * g ∈ vanishingIdeal Geo (zeroLocus Geo (sourceIdealHigh T)) := by
      apply mem_vanishingIdeal_iff.mpr
      intro u hu
      rw [map_mul]
      by_cases hd : MvPolynomial.aeval u T.denominator = 0
      · rw [hd, zero_mul]
      · rw [hg u ((mem_locus_iff_high T u).2 ⟨hu, hd⟩), mul_zero]
    rw [vanishingIdeal_zeroLocus_eq_radical, hp.isRadical.radical] at hmul
    exact (hp.mem_or_mem hmul).resolve_left
      (fun hd => hT.nonvanishing (Ideal.mem_span_singleton.mp hd))
  · intro hg u hu
    exact ((mem_locus_iff_high T u).1 hu).1 g hg

private theorem curve_image_high {T : ChartHigh 1} (hT : ChartOKHigh T) {a d : ℕ}
    (ha : 0 < a) (hd : 0 < d)
    (hD : T.denominator ∈ restrictCappedDegree (Fin 2) Geo 1 a d)
    (hN : ∀ j : Fin kHigh, T.numerator j ∈ restrictCappedDegree (Fin 2) Geo 1 a d) :
    T.ideal.IsPrime ∧ (affineHilbertPolynomial T.ideal).natDegree = 1 ∧
      affineDegree T.ideal ≤ (cappedDegreeMixedVolume T.equation.totalDegree
        (T.equation.degreeOf (Fin.last 1)) a d : ℕ) := by
  let E := cappedDegreeExponents (Fin 2) 1 a d
  let φ := monomialMap Geo E
  let P := (sourceIdealHigh T).comap φ
  let A := monomialPoint E '' T.locus
  have hA : P = vanishingIdeal Geo A := by
    ext g
    change φ g ∈ sourceIdealHigh T ↔ g ∈ vanishingIdeal Geo A
    rw [← locus_ideal_high hT, mem_vanishingIdeal_iff, mem_vanishingIdeal_iff]
    constructor
    · rintro h _ ⟨u, hu, rfl⟩
      rw [aeval_monomialPoint]
      exact h u hu
    · intro h u hu
      simpa only [aeval_monomialPoint] using h (monomialPoint E u) ⟨u, hu, rfl⟩
  have hp : P.IsPrime := (equationIdeal_prime_high hT).comap φ.toRingHom
  have hdim : (affineHilbertPolynomial P).natDegree = 1 := by
    have h := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      φ (monomialMap_cappedDegreeExponents_surjective ha hd) hT.irreducible.ne_zero
      (equationIdeal_prime_high hT).ne_top
    rw [Nat.card_fin] at h
    change (affineHilbertPolynomial P).natDegree + 1 = 2 at h
    omega
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hp hdim
  have hone : 1 ≤ affineDegree P := by
    rw [hdeg]
    exact_mod_cast hδ
  let D := monomialLift T.denominator hD
  let N (j : Fin kHigh) := monomialLift (T.numerator j) (hN j)
  have eval_lift (u : Fin 2 → Geo) (g : InitialRing 1) (hg : g ∈ restrictSupport Geo E) :
      MvPolynomial.eval (monomialPoint E u) (monomialLift g hg) = MvPolynomial.eval u g := by
    simpa only [aeval_eq_eval, monomialMap_monomialLift] using
      aeval_monomialPoint u (monomialLift g hg)
  have eval_D (u : Fin 2 → Geo) :
      MvPolynomial.eval (monomialPoint E u) D = MvPolynomial.eval u T.denominator :=
    eval_lift u T.denominator hD
  have eval_N (u : Fin 2 → Geo) (j : Fin kHigh) :
      MvPolynomial.eval (monomialPoint E u) (N j) = MvPolynomial.eval u (T.numerator j) :=
    eval_lift u (T.numerator j) (hN j)
  have hden (z) (hz : z ∈ A) : MvPolynomial.eval z D ≠ 0 := by
    obtain ⟨u, hu, rfl⟩ := hz
    rw [eval_D]
    exact hu.2
  obtain ⟨Q, hQ, hdQ, hbQ, hcover⟩ :=
    ratio_image_degree A P hA hp hdim hone D N
      (totalDegree_monomialLift_le_one _ _) (fun j => totalDegree_monomialLift_le_one _ _) hden
  have hle : Q ≤ T.ideal := by
    intro g hg
    rw [ChartHigh.ideal, mem_vanishingIdeal_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hz := hcover (monomialPoint E u) ⟨u, hu, rfl⟩ g hg
    change MvPolynomial.aeval
      (fun i => MvPolynomial.eval u (T.numerator i) / MvPolynomial.eval u T.denominator) g = 0
    simpa only [eval_D, eval_N] using hz
  have hlower : 1 ≤ (affineHilbertPolynomial T.ideal).natDegree :=
    (image_geometry_high T hT).2.ge
  have heq : Q = T.ideal := by
    refine le_antisymm hle fun g hg => ?_
    by_contra hn
    have hdrop := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hQ hn le_rfl).1
    have hsub : Q ⊔ Ideal.span {g} ≤ T.ideal :=
      sup_le hle ((Ideal.span_singleton_le_iff_mem T.ideal).mpr hg)
    have h := natDegree_affineHilbertPolynomial_le_of_le hsub
    omega
  subst Q
  refine ⟨hQ, le_antisymm hdQ hlower, hbQ.trans ?_⟩
  exact affineDegree_comap_cappedDegree_span_singleton_le ha hd hT.irreducible.ne_zero
    (K1_13_5_3.mem_capped T.equation le_rfl le_rfl)

private theorem order_one_image_degrees_high (s : BoxShape) (F : FamilyHigh 1)
    (hF : Family1High s F) : ImageDegreesHigh F (R1High s) := by
  have ha : 0 < a1High s := by unfold a1High; omega
  have hk : 1 < kHigh := by decide
  have hpos : 0 < t1High * (I1High s - 1) + kHigh - 1 := by omega
  have hd : 0 < d1High s := by rw [d1High]; exact lt_min ha hpos
  have hda : d1High s ≤ a1High s := min_le_left _ _
  have hlocal (i : Fin F.count) := curve_image_high (hF.chart_ok i) ha hd
    (K1_13_5_3.mem_capped _ (hF.bands i).1.1 (hF.bands i).1.2)
    (fun j => K1_13_5_3.mem_capped _ ((hF.bands i).2 j).1 ((hF.bands i).2 j).2)
  refine ⟨fun i => (hlocal i).1, fun i => (hlocal i).2.1, ?_⟩
  let cap (i : Fin F.count) := cappedDegreeMixedVolume (F.chart i).equation.totalDegree
    ((F.chart i).equation.degreeOf (Fin.last 1)) (a1High s) (d1High s)
  have hsum : ∑ i, cap i ≤ R1High s := by
    simp only [cap, cappedDegreeMixedVolume, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [R1High, Nat.add_sub_assoc (Nat.mul_le_mul_left _ hda), ← Nat.mul_sub_left_distrib]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hF.total) (Nat.mul_le_mul_right _ hF.index)
  calc
    (∑ i, affineDegree (F.chart i).ideal) ≤ ∑ i, (cap i : ℚ) :=
      Finset.sum_le_sum fun i _ => (hlocal i).2.2
    _ = ((∑ i, cap i : ℕ) : ℚ) := by rw [Nat.cast_sum]
    _ ≤ (R1High s : ℚ) := Nat.cast_le.mpr hsum

/-! ### Order-1 Singular → Order-0 Exceptional Polynomial (`CJ0_8` without `f.degree < k`) -/

private theorem regularRoot_of_simple_high (Q : DifferentialPolynomial K 1) (f : Polynomial K) :
    differentialSpecialization Q f = 0 →
    differentialSpecialization (separant Q (Fin.last 1)) f ≠ 0 →
    RegularRoot Q f := by
  let φ := differentialSpecializationHom (d := 1) f
  induction Q using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro _ hsep
    change φ (pderiv (some (Fin.last 1)) 0) ≠ 0 at hsep
    exact (hsep (by simp only [map_zero])).elim
  | unit u hu =>
    intro hroot _
    change φ u = 0 at hroot
    exact ((hu.map φ.toRingHom).ne_zero hroot).elim
  | mul a i _ hi ih =>
    intro hroot hsep
    change φ (i * a) = 0 at hroot
    change φ (pderiv (some (Fin.last 1)) (i * a)) ≠ 0 at hsep
    rw [map_mul, mul_eq_zero] at hroot
    rw [pderiv_mul, map_add, map_mul, map_mul] at hsep
    rcases hroot with h_i | h_a
    · have hiSep : φ (pderiv (some (Fin.last 1)) i) ≠ 0 := by
        intro hz
        exact hsep (by rw [hz, h_i, zero_mul, zero_mul, add_zero])
      exact ⟨i, hi, dvd_mul_right i a, h_i, hiSep⟩
    · have haSep : φ (pderiv (some (Fin.last 1)) a) ≠ 0 := by
        intro hz
        exact hsep (by rw [hz, h_a, mul_zero, mul_zero, add_zero])
      obtain ⟨g, hg, hdvd, hzero, hnonzero⟩ := ih h_a haSep
      exact ⟨g, hg, hdvd.trans (dvd_mul_left a i), hzero, hnonzero⟩

private theorem height_bounds_high {s : BoxShape} (hs : BoxOK s) :
    2 ≤ HHigh s ∧ HHigh s < p := by
  have hB : 2 ≤ s.B := by have := hs.top_pos; have := hs.index_top; have := hs.total_index; omega
  have hC : 2 * s.C - 1 ≤ s.B - 1 := by have := hs.index_top; have := hs.total_index; omega
  have hBprod : s.B ≤ s.B * (s.B - 1) := by
    calc
      s.B = s.B * 1 := (Nat.mul_one _).symm
      _ ≤ s.B * (s.B - 1) := Nat.mul_le_mul_left _ (by omega)
  have hc := (le_max_right NHigh (s.B * (s.B - 1))).trans_lt hs.characteristic
  have hmax : HHigh s ≤ s.B * (s.B - 1) := by
    unfold HHigh
    apply max_le hBprod
    exact (Nat.sub_le _ _).trans
      ((Nat.mul_le_mul_right s.B hC).trans_eq (Nat.mul_comm _ _))
  exact ⟨hB.trans (le_max_left _ _), hmax.trans_lt hc⟩

private theorem exceptional_orderOne_high (s : BoxShape) (hs : BoxOK s)
    (Q : DifferentialPolynomial K 1) (hQ : OrderOneHigh s Q) :
    ∃ G : Polynomial (Polynomial K), G ≠ 0 ∧ G.natDegree ≤ HHigh s * (HHigh s - 1) ∧
      ∀ f : Polynomial K, differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
        G.eval f = 0 := by
  classical
  obtain ⟨hQ, hweight, _⟩ := hQ
  have hweight' : jetTotalDegree Q ≤ HHigh s := hweight
  obtain ⟨hH, hHp⟩ := height_bounds_high hs
  suffices ∃ R : DifferentialPolynomial K 0, R ≠ 0 ∧ jetTotalDegree R ≤ HHigh s * (HHigh s - 1) ∧
      ∀ f : Polynomial K, differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
        differentialSpecialization R f = 0 by
    obtain ⟨R, hR, hRdeg, hRroot⟩ := this
    refine ⟨orderZeroAsPolynomial R, ?_, ?_, ?_⟩
    · intro hz
      apply hR
      apply Sol1.C57.orderZeroAsPolynomial_injective
      simpa only [orderZeroAsPolynomial, map_zero, Polynomial.map_zero] using hz
    · exact (Sol1.C57.orderZeroAsPolynomial_degree R).trans_le hRdeg
    · intro f hroot hnreg
      exact (orderZeroAsPolynomial_eval R f).trans (hRroot f hroot hnreg)
  by_cases hb : jetDegree (Sol1.C57.regularPart 0 Q) (Fin.last 1) = 0
  · have hGone := Sol1.C57.regular_eq_one_of_degree_zero 0 Q hb
    have hsplit := (Sol1.C57.split_weight 0 Q).trans hweight'
    have hlow : jetTotalDegree (Sol1.C57.lowerPart 0 Q) ≤ HHigh s := by omega
    have hbudget : HHigh s ≤ HHigh s * (HHigh s - 1) :=
      (Nat.mul_one _).symm.le.trans (Nat.mul_le_mul_left _ (by omega))
    refine ⟨Sol1.C57.lowerPart 0 Q, Sol1.C57.lower_ne_zero 0 Q, hlow.trans hbudget, ?_⟩
    intro f hroot _
    rcases Sol1.C57.root_split 0 Q hQ f hroot with hc | hr
    · exact hc
    · rw [hGone] at hr
      exact (one_ne_zero (by simpa only [differentialSpecialization, map_one] using hr)).elim
  · have hbpos : 0 < jetDegree (Sol1.C57.regularPart 0 Q) (Fin.last 1) := Nat.pos_of_ne_zero hb
    have hchar : ringChar K = 0 ∨ jetDegree Q (Fin.last 1) < ringChar K := by
      right
      rw [ringChar.eq K p]
      exact (jetDegree_le_total Q (Fin.last 1)).trans_lt (hweight'.trans_lt hHp)
    refine ⟨Sol1.C57.exceptionalEquation 0 Q, Sol1.C57.exceptional_ne_zero 0 Q hchar,
      Sol1.C57.exceptional_weight_sharp 0 Q (HHigh s) hweight'
        (hbpos.trans_le (jetDegree_le_total (Sol1.C57.regularPart 0 Q) (Fin.last 1))), ?_⟩
    intro f hroot hnreg
    rcases Sol1.C57.root_regular_or_exceptional 0 Q hQ f hroot hbpos with hreg | hex
    · have hdvd : Sol1.C57.regularPart 0 Q ∣ Q := by
        obtain ⟨R, hR⟩ := radicalPrimPart_dvd_self none (Sol1.C57.topReindex 0 Q)
        refine ⟨(Sol1.C57.topReindex 0).symm R, ?_⟩
        simpa [Sol1.C57.regularPart] using congrArg (Sol1.C57.topReindex 0).symm hR
      obtain ⟨g, hg, hgdvd, hzero, hsep⟩ :=
        regularRoot_of_simple_high (Sol1.C57.regularPart 0 Q) f hreg.1 hreg.2
      exact (hnreg ⟨g, hg, hgdvd.trans hdvd, hzero, hsep⟩).elim
    · exact hex

/-! ## Section 6: Incidence, Regular Factor Pricing, and Main Theorem at `kHigh = 133,721` -/

private def commonSitesHigh (w : Node → K) (T : Finset (Polynomial K)) : Finset Node :=
  univ.filter fun i => ∀ f ∈ T, f.eval (node i) = w i

private theorem mem_commonSitesHigh {w : Node → K} {T : Finset (Polynomial K)} {i : Node} :
    i ∈ commonSitesHigh w T ↔ ∀ f ∈ T, f.eval (node i) = w i := by
  simp [commonSitesHigh]

private theorem commonSitesHigh_card_le {A w} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w) (hsize : 1 < T.card) :
    (commonSitesHigh w T).card ≤ NHigh := by
  obtain ⟨f, hf, g, hg, hfg⟩ := one_lt_card.mp hsize
  have hdeg {P : Polynomial K} (hP : P ∈ T) : P.natDegree ≤ NHigh := by
    by_cases hz : P = 0
    · simp [hz, NHigh]
    · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hz).2 (hT hP).1)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node node.injective (f - g)
    (sub_ne_zero.mpr hfg) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (hdeg hf) (hdeg hg)))
  intro i hi
  change (f - g).eval (node i) = 0
  rw [Polynomial.eval_sub, mem_commonSitesHigh.mp hi f hf, mem_commonSitesHigh.mp hi g hg, sub_self]

private theorem firstMoment_high {A w} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w) (_hS : (commonSitesHigh w T).card ≤ A)
    (cap : ℚ) (hcap : ∀ i ∉ commonSitesHigh w T,
      ((T.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ cap) :
    ((A - (commonSitesHigh w T).card : ℕ) : ℚ) * T.card ≤
      ((nHigh - (commonSitesHigh w T).card : ℕ) : ℚ) * cap := by
  classical
  let S := commonSitesHigh w T
  let candidates := (univ : Finset Node) \ S
  let hits := fun f : Polynomial K => univ.filter fun i : Node => f.eval (node i) = w i
  let occ := fun i : Node => (T.filter fun f => f.eval (node i) = w i).card
  have hcard : candidates.card = nHigh - S.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ,
      ProximityPrize.Benchmark.IRSProfile.card_index]
  have hnew (f : Polynomial K) (hf : f ∈ T) : A - S.card ≤ (hits f \ S).card := by
    have hsub : S ⊆ hits f := fun i hi => mem_filter.mpr ⟨mem_univ _, mem_commonSitesHigh.mp hi f hf⟩
    exact (Nat.sub_le_sub_right (hT hf).2 _).trans_eq (card_sdiff_of_subset hsub).symm
  have hsum : ∑ i ∈ candidates, occ i = ∑ f ∈ T, (hits f \ S).card := by
    simp only [occ, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun f _ => ?_
    rw [sum_boole, Nat.cast_id]
    have eqSet : (candidates.filter fun i => f.eval (node i) = w i) = hits f \ S := by
      ext i
      simp [candidates, hits, and_comm]
    rw [eqSet]
  have lower : T.card * (A - S.card) ≤ ∑ i ∈ candidates, occ i := by
    rw [hsum]
    calc
      _ = ∑ f ∈ T, (A - S.card) := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum hnew
  have hlower : (T.card : ℚ) * (A - S.card : ℕ) ≤ ∑ i ∈ candidates, (occ i : ℚ) := by
    exact_mod_cast lower
  calc
    _ = (T.card : ℚ) * (A - S.card : ℕ) := mul_comm _ _
    _ ≤ _ := hlower
    _ ≤ ∑ i ∈ candidates, cap := sum_le_sum fun i hi => hcap i (mem_sdiff.mp hi).2
    _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]

private theorem factorPrice_high
    {A w s} (hA : AgreementOKHigh A) (hA₅ : kHigh + 5 ≤ A) (hs : BoxOK s)
    {G : CJ0_3.Equation} (hG : OrderTwoHigh s G)
    {E : InitialRing 2} (hE : Irreducible E) (hEdvd : E ∣ CJ0_3.initial G)
    (hreg : ¬ E ∣ CJ0_3.initialSep G) (V : Finset (Polynomial K))
    (hV : (V : Set (Polynomial K)) ⊆ closeHigh A w)
    (hroots : ∀ f ∈ V, differentialSpecialization G f = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0) :
    (V.card : ℚ) ≤ baseFactor A * slicePriceHigh A s kHigh E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) + 1 := by
  classical
  by_cases hv : 1 < V.card
  · let S := commonSitesHigh w V
    obtain ⟨S', hsubset, hcard⟩ := exists_subset_card_eq (min_le_left S.card (kHigh - 3))
    have hshort : S'.card + 3 ≤ kHigh := by
      rw [hcard]; have := min_le_right S.card (kHigh - 3); unfold kHigh at *; omega
    have hL : kHigh - S'.card = shortLength S.card := by
      rw [hcard]; unfold shortLength kHigh; omega
    obtain ⟨T, hT, heq, hband, hcovers⟩ :=
      shortenChart_high s hs G hG E hE hEdvd hreg S' hshort w
    rw [hL] at hband
    have hcov (f : Polynomial K) (hf : f ∈ V) : coeffPointHigh f ∈ T.imageSet := by
      obtain ⟨h₁, h₂, h₃⟩ := hroots f hf
      exact hcovers f (hV hf).1 h₁ h₂ h₃ (fun i hi => mem_commonSitesHigh.mp (hsubset hi) f hf)
    have hc : S.card ≤ NHigh := commonSitesHigh_card_le hV hv
    have hS : S.card < A := hc.trans_lt hA.gt_degree
    have hd : (0 : ℚ) < gapHigh A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
    have hdegree := volumeDegree_high s hs (shortLength S.card) (le_max_left ..) T hT hband
    rw [heq] at hdegree
    let price := slicePriceHigh A s (shortLength S.card) E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2))
    have hprice (i : Node) (hi : i ∉ S) :
        ((V.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ price := by
      have hmiss : ∃ f ∈ V, f.eval (node i) ≠ w i := by
        simpa only [S, mem_commonSitesHigh, not_forall, exists_prop] using hi
      have cut := cutCap_high T hT hA hV hcov i hmiss
        (totalCap s (shortLength S.card)) hband.denominator.1 (fun j => (hband.numerator j).1)
      rw [heq, Nat.cast_mul] at cut
      have price_mul : (gapHigh A : ℚ) * price =
          (errorsHigh A : ℚ) * bandVolumeHigh s (shortLength S.card) E.totalDegree
            (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) +
          (gapHigh A : ℚ) * ((totalCap s (shortLength S.card) : ℚ) * E.totalDegree) := by
        dsimp only [price, slicePriceHigh, curveFactor]
        rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
      apply le_of_mul_le_mul_left _ hd
      rw [price_mul]
      exact cut.trans
        (add_le_add (mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg (errorsHigh A))) le_rfl)
    have hh := firstMoment_high hV hS.le price hprice
    have hu : (0 : ℚ) < (A - S.card : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hS)
    have hpart : (V.card : ℚ) ≤ incidenceFactor A S.card * price := by
      rw [incidenceFactor, div_mul_eq_mul_div, le_div_iff₀ hu, mul_comm (V.card : ℚ)]
      exact hh
    exact hpart.trans ((weighted_price_high A S.card s hs hA₅ hA.lt_length.le hc ..).trans
      (le_add_of_nonneg_right zero_le_one))
  · have hc : (V.card : ℚ) ≤ 1 := by exact_mod_cast (show V.card ≤ 1 by omega)
    have hp : 0 ≤ baseFactor A * slicePriceHigh A s kHigh E.totalDegree
        (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) := by
      obtain ⟨ht, hi, hz⟩ := volume_nonneg_high s hs kHigh (by decide)
      have hbf : 0 ≤ baseFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hcf : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      unfold slicePriceHigh bandVolumeHigh
      positivity
    exact hc.trans (le_add_of_nonneg_left hp)

private theorem regularPrice_high
    {A w s Q} (hA : AgreementOKHigh A) (hA₅ : kHigh + 5 ≤ A) (hs : BoxOK s)
    (hQ : OrderTwoHigh s Q) (T : Finset (Polynomial K))
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w) (hreg : ∀ f ∈ T, RegularRoot Q f) :
    (T.card : ℚ) ≤ surfacePriceHigh A s + s.B := by
  classical
  obtain ⟨F⟩ := CJ0_3_1.proof Q hQ.1
  let root (i : Fin F.count) (f : Polynomial K) :=
    differentialSpecialization (F.source i) f = 0 ∧
    MvPolynomial.eval (CJ0_3.nativeJet f) (F.equation i) = 0 ∧
    MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep (F.source i)) ≠ 0
  let part (i : Fin F.count) := T.filter (root i)
  have hc : T.card ≤ ∑ i, (part i).card := by
    apply (card_le_card (t := univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i, hi⟩ := F.covers f (hreg f hf)
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hf, hi⟩⟩
  let b (i : Fin F.count) := (F.equation i).totalDegree
  let j (i : Fin F.count) := (F.equation i).weightedTotalDegree Fin.val
  let c (i : Fin F.count) := (F.equation i).degreeOf (Fin.last 2)
  have hp (i : Fin F.count) : ((part i).card : ℚ) ≤
      baseFactor A * slicePriceHigh A s kHigh (b i) (j i) (c i) + 1 :=
    factorPrice_high hA hA₅ hs (CJ0_3.orderTwo_of_dvd hQ (F.source_dvd i))
      (F.irreducible i) (F.component i) (F.regular i) (part i)
      (fun _ hf => hT (mem_filter.mp hf).1) (fun _ hf => (mem_filter.mp hf).2)
  obtain ⟨hb, hj, ht⟩ := CJ0_3.factor_weights hQ F
  have hn : F.count ≤ s.B := (CJ0_3.factor_count F).trans hb
  have hbq : (∑ i, (b i : ℚ)) ≤ s.B := by exact_mod_cast hb
  have hjq : (∑ i, (j i : ℚ)) ≤ s.J := by exact_mod_cast hj
  have hcq : (∑ i, (c i : ℚ)) ≤ s.C := by exact_mod_cast ht
  obtain ⟨hu, hv, hw⟩ := volume_nonneg_high s hs kHigh (by decide)
  have hsum : (∑ i, bandVolumeHigh s kHigh (b i) (j i) (c i)) ≤ R2High s := by
    rw [← volume_full_high s hs]
    simp only [bandVolumeHigh, sum_add_distrib, ← mul_sum]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbq hu)
      (mul_le_mul_of_nonneg_left hjq hv)) (mul_le_mul_of_nonneg_left hcq hw)
  have hprice : (∑ i, slicePriceHigh A s kHigh (b i) (j i) (c i)) ≤
      curveFactor A * R2High s + (s.B : ℚ) * totalCap s kHigh := by
    simp only [slicePriceHigh, sum_add_distrib, ← mul_sum]
    rw [mul_comm (s.B : ℚ)]
    exact add_le_add (mul_le_mul_of_nonneg_left hsum
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (mul_le_mul_of_nonneg_left hbq (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ i, ((part i).card : ℚ) := by exact_mod_cast hc
    _ ≤ ∑ i, (baseFactor A * slicePriceHigh A s kHigh (b i) (j i) (c i) + 1) :=
      sum_le_sum fun i _ => hp i
    _ = baseFactor A * (∑ i, slicePriceHigh A s kHigh (b i) (j i) (c i)) + F.count := by
      simp only [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, mul_one, card_univ,
        Fintype.card_fin]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprice
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Nat.cast_le.mpr hn)

/-- **Main Case-B Order-Two Counting Theorem at `kHigh = 133,721`:**
Any finite set `T` of polynomials of degree `< 133,721` (`≤ 131,071 + 2,649`) agreeing with a
word `w` on at least `A` positions and annihilated by a nonzero order-2 differential polynomial `Q`
of box shape `s = (B, J, C)` has cardinality at most `tariffHigh A s`. -/
theorem order_two_card_le_high133721
    {A : ℕ} {w : Node → K} {s : BoxShape} {Q : DifferentialPolynomial K 2}
    (hA : AgreementOKHigh A) (hA₅ : kHigh + 5 ≤ A) (hs : BoxOK s)
    (hQ : OrderTwoHigh s Q)
    (T : Finset (Polynomial K)) (hT : (T : Set (Polynomial K)) ⊆ closeHigh A w)
    (hroots : ∀ f ∈ T, differentialSpecialization Q f = 0) :
    T.card ≤ tariffHigh A s := by
  classical
  obtain ⟨Q₁, hQ₁, hremain₁⟩ := eliminate_orderTwo_high s hs Q hQ
  obtain ⟨F₁, hF₁, hcover₁⟩ := order_one_family_high s hs Q₁ hQ₁
  obtain ⟨G, hG, hGdeg, hordinary⟩ := exceptional_orderOne_high s hs Q₁ hQ₁
  let T₂ := T.filter (RegularRoot Q)
  let rest := T.filter fun f => ¬ RegularRoot Q f
  let T₁ := rest.filter (RegularRoot Q₁)
  let T₀ := rest.filter fun f => ¬ RegularRoot Q₁ f
  have h₂ (f) (hf : f ∈ T₂) := hT (mem_filter.mp hf).1
  have hrest (f) (hf : f ∈ rest) := hT (mem_filter.mp hf).1
  have h₁ (f) (hf : f ∈ T₁) := hrest f (mem_filter.mp hf).1
  have p₂ := regularPrice_high hA hA₅ hs hQ T₂
    (fun f hf => h₂ f hf) (fun _ hf => (mem_filter.mp hf).2)
  have hprice₁ := family1_capacity_high (fun f hf => h₁ f hf) hA F₁
    (order_one_image_degrees_high s F₁ hF₁)
    (fun f hf => hcover₁ f (h₁ f hf).1 (mem_filter.mp hf).2)
  have hd : (0 : ℚ) < gapHigh A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
  have p₁ : (T₁.card : ℚ) ≤ curveFactor A * R1High s + HHigh s := by
    apply le_of_mul_le_mul_left _ hd
    unfold curveFactor
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
    have hcount : (F₁.count : ℚ) ≤ HHigh s := by exact_mod_cast hF₁.count
    exact hprice₁.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hd.le))
  have p₀ : T₀.card ≤ HHigh s * (HHigh s - 1) := by
    refine (Polynomial.card_le_degree_of_subset_roots (p := G) ?_).trans hGdeg
    intro f hf
    obtain ⟨hr', hsing₁⟩ := mem_filter.mp (show f ∈ T₀ from hf)
    have hf' := (mem_filter.mp hr').1
    exact (Polynomial.mem_roots hG).mpr
      (hordinary f (hremain₁ f (hroots f hf') (mem_filter.mp hr').2) hsing₁)
  have htail : ∀ h : ℕ, h + h * (h - 1) = h ^ 2 := by
    intro h
    cases h with
    | zero => rfl
    | succ h => rw [Nat.succ_sub_one]; ring
  have hp₀ : (HHigh s : ℚ) + T₀.card ≤ (HHigh s : ℚ) ^ 2 := by
    exact_mod_cast (Nat.add_le_add_left p₀ (HHigh s)).trans_eq (htail (HHigh s))
  have hpart₂ : T₂.card + rest.card = T.card := card_filter_add_card_filter_not ..
  have hpart₁ : T₁.card + T₀.card = rest.card := card_filter_add_card_filter_not ..
  have hp : (T.card : ℚ) ≤ totalPriceHigh A s := by
    rw [show T.card = T₂.card + T₁.card + T₀.card by omega, Nat.cast_add, Nat.cast_add]
    unfold totalPriceHigh
    linarith only [p₂, p₁, hp₀]
  exact Nat.cast_le.mp (hp.trans (Nat.le_ceil _))

/-- Concrete Case-B cardinality caps for all 6 small Rescue rectangles at `69.63` (`A = 179,798`). -/
theorem caseB_six_rects_card_le_6963 (w : Node → K) (T : Finset (Polynomial K))
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh 179798 w) :
    (∀ Q, OrderTwoHigh box_r0 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 2_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r1 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 640_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r2a Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 44_890_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r3a_j2 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 36_860_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r3a_j4 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 7_870_000_000_000_000) ∧
    (∀ Q, OrderTwoHigh box_r3a_j7 Q → (∀ f ∈ T, differentialSpecialization Q f = 0) →
      T.card ≤ 9_380_000_000_000_000) := by
  obtain ⟨hb0, hb1, hb2a, hb32, hb34, hb37⟩ := all_six_boxes_ok
  obtain ⟨ht0, ht1, ht2a, ht32, ht34, ht37⟩ := caseB_tariffs_6963
  have hA₅ : kHigh + 5 ≤ 179798 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb0 hQ T hT hr).trans ht0
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb1 hQ T hT hr).trans ht1
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb2a hQ T hT hr).trans ht2a
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb32 hQ T hT hr).trans ht32
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb34 hQ T hT hr).trans ht34
  · intro Q hQ hr
    exact (order_two_card_le_high133721 agreementOK_6963 hA₅ hb37 hQ T hT hr).trans ht37

end

end CJ0High133721

#print axioms CJ0High133721.shortenChart_high
#print axioms CJ0High133721.cutCap_high
#print axioms CJ0High133721.order_two_card_le_high133721
#print axioms CJ0High133721.caseB_six_rects_card_le_6963
