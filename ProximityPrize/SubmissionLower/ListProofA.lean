import ProximityPrize.SubmissionLower.PortHighBase
import ProximityPrize.SubmissionLower.PortHighFinish -- serialize candidate build
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
open private occupancy from ProximityPrize.SubmissionLower.Fast055
open private incidence_arithmetic from ProximityPrize.SubmissionLower.PortHighBase
theorem section_capacity {A : ℕ} {w : Node → K} {T : Finset K[X]}
    (h : (T : Set K[X]) ⊆ close A w) (hA : AgreementOK A) (cap : ℕ)
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
  let hits (γ : K[X]) : Finset Node := univ.filter fun i => γ.eval (node i) = w i
  let common : Finset Node := univ.filter fun i => ∀ γ ∈ T, γ.eval (node i) = w i
  let nodes : Finset Node := univ \ common
  have common_le (γ : K[X]) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K[X]) (hγ : γ ∈ T) : A ≤ (hits γ).card := by
    exact (h hγ).2
  have degree (a : K[X]) (ha : a ∈ T) : a.natDegree ≤ N := by
    by_cases hz : a = 0
    · simp [hz]
    · have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hz).2 (h ha).1
      exact Nat.le_of_lt_succ hdeg
  have pair_count (a : K[X]) (ha : a ∈ T) (b : K[X]) (hb : b ∈ T) (hab : a ≠ b) :
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
  have exists_trim (γ : K[X]) : ∃ B : Finset Node, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
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
  have into_nodes (γ : K[X]) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : K[X]) (ha : a ∈ T) (b : K[X]) (hb : b ∈ T) (hab : a ≠ b) :
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
open private curve_degree_nat from ProximityPrize.SubmissionLower.Fast055
private def valueCut (x a : K) : CoeffRing :=
  (∑ i : Fin k, C (embed x ^ i.val) * MvPolynomial.X i) - C (embed a)
private theorem valueCut_degree (x a : K) : (valueCut x a).totalDegree ≤ 1 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply totalDegree_finsetSum_le
  intro i _
  simpa only [totalDegree_C, totalDegree_X, zero_add] using
    (totalDegree_mul (C (embed x ^ i.val)) (MvPolynomial.X i))
theorem natDegree_bound {f : K[X]} (h : f.degree < k) : f.natDegree < k := by
  by_cases hz : f = 0
  · rw [hz, Polynomial.natDegree_zero]
    exact Nat.zero_lt_succ _
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 h
private theorem valueCut_eval {f : K[X]} (h : f.degree < k) (x a : K) :
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
private theorem coeffPoint_injOn {A w} {Γ : Finset K[X]} (h : (Γ : Set K[X]) ⊆ close A w) :
    Set.InjOn coeffPoint (Γ : Set K[X]) := by
  intro f hf g hg heq
  apply Polynomial.ext
  intro j
  by_cases hj : j < k
  · exact embed.injective (congrFun heq ⟨j, hj⟩)
  · have hfj := (natDegree_bound (h hf).1).trans_le (Nat.le_of_not_gt hj)
    have hgj := (natDegree_bound (h hg).1).trans_le (Nat.le_of_not_gt hj)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hfj, Polynomial.coeff_eq_zero_of_natDegree_lt hgj]
private theorem zeroDim_count {A w} {Γ : Finset K[X]} (h : (Γ : Set K[X]) ⊆ close A w) (P : Ideal CoeffRing)
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
private theorem section_count {A w} {Γ : Finset K[X]} (h : (Γ : Set K[X]) ⊆ close A w) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hpoints : ∀ γ ∈ Γ, coeffPoint γ ∈ zeroLocus Geo P)
    (x a : K) (hmiss : ∃ γ ∈ Γ, γ.eval x ≠ a)
    {c : ℚ} (hc : 0 ≤ c)
    (bound : ∀ (V : Finset K[X]), V ⊆ Γ → ∀ (Q : Ideal CoeffRing), Q.IsPrime →
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
private theorem curve_capacity {A w} {T : Finset K[X]} (hT : (T : Set K[X]) ⊆ close A w)
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
private theorem surface_capacity {A w} {T : Finset K[X]} (hT : (T : Set K[X]) ⊆ close A w)
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
theorem family_capacity {A w r budget} {T : Finset K[X]} (hT : (T : Set K[X]) ⊆ close A w)
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
    have hsub : (part i : Set K[X]) ⊆ close A w := fun _ hf => hT (mem_filter.mp hf).1
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
def c3 : Prop :=
  ∀ s, ShapeOK s → ∀ Q, OrderTwo s Q →
    ∃ F : Family 2, Family₂ s F ∧ CoversRegular F Q
def c4 : Prop :=
  ∀ s, ShapeOK s → ∀ F : Family 2, Family₂ s F → ImageDegrees F (R₂ s)
def c5 : Prop :=
  ∀ s, ShapeOK s → ∀ Q, OrderTwo s Q →
    ∃ Q₁, OrderOne s Q₁ ∧ ∀ f : K[X], f.degree < k →
      differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
      differentialSpecialization Q₁ f = 0
def c6 : Prop :=
  ∀ s, ShapeOK s → ∀ Q₁, OrderOne s Q₁ →
    ∃ F : Family 1, Family₁ s F ∧ CoversRegular F Q₁
def c7 : Prop :=
  ∀ s, ShapeOK s → ∀ F : Family 1, Family₁ s F → ImageDegrees F (R₁ s)
def c8 : Prop :=
  ∀ s, ShapeOK s → ∀ Q₁, OrderOne s Q₁ →
    ∃ G : Polynomial K[X], G ≠ 0 ∧ G.natDegree ≤ H s*(H s-1) ∧
      ∀ f : K[X], f.degree < k → differentialSpecialization Q₁ f = 0 →
        ¬ RegularRoot Q₁ f → G.eval f = 0
private theorem combine {u v b h r₂ r₁ x y z : ℕ}
    (hx : v*x ≤ u*(2*r₂)+v*b) (hy : v*y ≤ u*r₁+v*h) (hz : z ≤ h*(h-1)) :
    v*(x+y+z) ≤ u*(2*r₂+r₁)+v*(b+h^2) := by
  have htail : h+h*(h-1) = h^2 := by
    cases h with
    | zero => rfl
    | succ h => rw [Nat.succ_sub_one]; ring
  calc
    _ = v*x+v*y+v*z := by ring
    _ ≤ (u*(2*r₂)+v*b)+(u*r₁+v*h)+v*(h*(h-1)) :=
      Nat.add_le_add (Nat.add_le_add hx hy) (Nat.mul_le_mul_left v hz)
    _ = _ := by rw [← htail]; ring
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) (h8 : c8) : Main := by
  classical
  intro A s R hA hs hw hsur hcert w
  have horig : originRank A s ≤ R := by
    rcases hcert with h | ⟨cut, hcut, htail, hp⟩
    · exact h
    · exact (h1 A s cut hs hw hcut htail).trans hp
  have hr := (h2 A s hs hw w).trans (Nat.mul_le_mul_left n horig)
  have hdim := source_dimension A s hs hw
  unfold Surplus at hsur
  have hsmall : stackRank A s w < Fintype.card (ColumnIndex A s) := by omega
  obtain ⟨Q, hQ, hwt, hloc⟩ := interpolant hs hw w hsmall
  have hroot := specializes hwt hloc
  obtain ⟨F₂, hF₂, hcover₂⟩ := h3 s hs Q hQ
  obtain ⟨Q₁, hQ₁, hremain₁⟩ := h5 s hs Q hQ
  obtain ⟨F₁, hF₁, hcover₁⟩ := h6 s hs Q₁ hQ₁
  obtain ⟨G, hG, hGdeg, hordinary⟩ := h8 s hs Q₁ hQ₁
  have hfin : (close A w).Finite :=
    ReedSolomon.closePolynomialSet_finite node w (show k ≤ A from hA.gt_degree)
  let T := hfin.toFinset
  have hall (f : K[X]) (hf : f ∈ T) : f ∈ close A w := hfin.mem_toFinset.mp hf
  let T₂ := T.filter (RegularRoot Q)
  let rest := T.filter fun f => ¬ RegularRoot Q f
  let T₁ := rest.filter (RegularRoot Q₁)
  let T₀ := rest.filter fun f => ¬ RegularRoot Q₁ f
  have h₂ (f) (hf : f ∈ T₂) := hall f (mem_filter.mp hf).1
  have hrest (f) (hf : f ∈ rest) := hall f (mem_filter.mp hf).1
  have h₁ (f) (hf : f ∈ T₁) := hrest f (mem_filter.mp hf).1
  have hprice₂ := family_capacity (fun f hf => h₂ f hf) hA (Or.inr rfl) F₂ (h4 s hs F₂ hF₂)
    (fun f hf => hcover₂ f (h₂ f hf).1 (mem_filter.mp hf).2)
  have hprice₁ := family_capacity (fun f hf => h₁ f hf) hA (Or.inl rfl) F₁ (h7 s hs F₁ hF₁)
    (fun f hf => hcover₁ f (h₁ f hf).1 (mem_filter.mp hf).2)
  have p₂ : gap A*T₂.card ≤ errors A*(2*R₂ s) + gap A*F₂.count := by exact_mod_cast hprice₂
  have p₁ : gap A*T₁.card ≤ errors A*R₁ s + gap A*F₁.count := by
    simpa only [one_mul] using (show gap A*T₁.card ≤ errors A*(1*R₁ s) + gap A*F₁.count by
      exact_mod_cast hprice₁)
  have p₀ : T₀.card ≤ H s*(H s-1) := by
    refine (Polynomial.card_le_degree_of_subset_roots (p := G) ?_).trans hGdeg
    intro f hf
    obtain ⟨hr', hsing₁⟩ := mem_filter.mp (show f ∈ T₀ from hf)
    have hf' := hrest f hr'
    exact (Polynomial.mem_roots hG).mpr (hordinary f hf'.1
      (hremain₁ f hf'.1 (hroot f hf') (mem_filter.mp hr').2) hsing₁)
  have hpart₂ : T₂.card + rest.card = T.card := card_filter_add_card_filter_not ..
  have hpart₁ : T₁.card + T₀.card = rest.card := card_filter_add_card_filter_not ..
  have hp : gap A*T.card ≤ chargeNumerator A s := by
    rw [show T.card = T₂.card+T₁.card+T₀.card by omega]
    apply combine _ _ p₀
    · exact p₂.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hF₂.count) _)
    · exact p₁.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hF₁.count) _)
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hA.gt_degree)).2
  rw [mul_comm]
  exact hp.trans (Nat.le_add_right _ _)
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
theorem origin_substitution (x a b c : ℕ) :
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
theorem origin_entry {A s} (r : OriginRow s) (j : OriginCol A s) :
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
def blockIndex {s cut q g} (h : InPrefix s cut q g) : BlockIndex s cut :=
  ⟨⟨q, h.grade⟩, ⟨(g + s.J).toNat, by
    change (g + s.J).toNat < s.m+s.J-q
    have := h.lower
    have := h.upper
    omega⟩⟩
theorem balance_blockIndex {s cut q g} (h : InPrefix s cut q g) :
    balance (blockIndex h) = g := by
  have := h.lower
  simp only [balance, blockIndex]
  omega
theorem blockIndex_ext {s cut} {i j : BlockIndex s cut}
    (hq : i.1.val = j.1.val) (hg : balance i = balance j) : i = j := by
  rcases i with ⟨qi, ui⟩
  rcases j with ⟨qj, uj⟩
  have hgrade : qi = qj := Fin.ext hq
  subst qj
  have hoffset : ui = uj := Fin.ext (by simp only [balance] at hg; omega)
  subst uj
  rfl
theorem row_mem {s : Source} (r : OriginRow s) :
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
theorem origin_support {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
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
def activeRows (A : ℕ) (s : Source) : Finset (OriginRow s) :=
  localConstraintSupportedRows s.m (fun _ : Unit => (0 : ZMod p)) (fun _ => 0) (column A s)
def activeCols (A : ℕ) (s : Source) : Finset (OriginCol A s) := by
  classical
  exact Finset.univ.filter fun j => ∃ r, origin A s r j ≠ 0
theorem active_row_inPrefix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (r : activeRows A s) :
    InPrefix s cut (rowJet r.val.2.val).q (rowBalance r.val.2.val) := by
  obtain ⟨j, hj⟩ := (mem_localConstraintSupportedRows_iff _ _ _ _ _).mp r.property
  obtain ⟨hq, hg, h⟩ := origin_support hs htail r.val j hj
  rwa [hq, hg]
theorem active_col_inPrefix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (j : activeCols A s) :
    InPrefix s cut j.val.1.val.q (colBalance j.val.2.val j.val.1.val) := by
  classical
  obtain ⟨r, hr⟩ := (Finset.mem_filter.mp j.property).2
  exact (origin_support hs htail r j.val hr).2.2
abbrev BlockRow {s cut} (i : BlockIndex s cut) : Type := ↥(blockRows s.m i.1.val (balance i))
abbrev BlockCol {s cut} (i : BlockIndex s cut) : Type := ↥(blockCols s i.1.val (balance i))
def rowRep {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) (r : activeRows A s) :
    Sigma (BlockRow (s := s) (cut := cut)) :=
  let h := active_row_inPrefix hs htail r
  ⟨blockIndex h, ⟨rowJet r.val.2.val, by
    change rowJet r.val.2.val ∈
      blockRows s.m (rowJet r.val.2.val).q (balance (blockIndex h))
    rw [balance_blockIndex]
    exact row_mem r.val⟩⟩
def colRep {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) (j : activeCols A s) :
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
theorem packet_entry {s cut} (r : Sigma (BlockRow (s := s) (cut := cut)))
    (c : Sigma (BlockCol (s := s) (cut := cut))) (h : r.1 = c.1) :
    packet s cut r c = blockEntry r.2.val c.2.val := by
  rcases r with ⟨i,r⟩
  rcases c with ⟨j,c⟩
  change i = j at h
  subst j
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _
theorem origin_submatrix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) :
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
theorem origin_rank_eq_supported (A : ℕ) (s : Source) :
    (origin A s).rank =
      ((origin A s).submatrix (Subtype.val : activeRows A s → _) id).rank := by
  symm
  apply Matrix.rank_submatrix_eq_of_ne_zero_mem_range
  exact localConstraintMatrix_ne_zero_mem_range _ _ _ _
theorem supported_rank_le (A : ℕ) (s : Source) :
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
theorem packet_rank_le (s : Source) (cut : ℕ) : (packet s cut).rank ≤ prefixRank s cut := by
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
theorem lower_mem {s : Source} (hs : ShapeOK s) {c b a : ℕ}
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
theorem column_mem_sourceSpan {F : Type*} [Field F] {A : ℕ} {s : Source}
    (i : ColumnIndex A s) : (column A s i).polynomial ∈ sourceSpan F A s :=
  Submodule.subset_span (Set.mem_range_self i)
theorem translated_column_mem {F : Type*} [Field F] {A : ℕ} {s : Source}
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
theorem native_origin_rank (A : ℕ) (s : Source) :
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
theorem sum_const_card {ι : Type*} [Fintype ι] (r : ℕ) :
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
def centerMap : K[X] →+* Geo :=
  (algebraMap FX Geo).comp (algebraMap K[X] FX)
def lifted (G : Equation) : DifferentialPolynomial Geo 2 :=
  MvPolynomial.map embed G
def initial (G : Equation) : InitialRing 2 :=
  initialJetEquation center (lifted G)
def initialSep (G : Equation) : InitialRing 2 :=
  initialJetSeparant center (lifted G)
def nativeJet (f : K[X]) : Fin 3 → Geo :=
  polynomialJet center (f.map embed)
def centeredNumeratorAt (G : Equation) (τ l : ℕ) : InitialRing 2 :=
  commonTaylorNumerator center (lifted G) τ l
abbrev centeredNumerator (G : Equation) (l : Fin k) : InitialRing 2 :=
  centeredNumeratorAt G t l.val
def coefficientNumeratorAt (G : Equation) (τ : ℕ) {L : ℕ} (i : Fin L) : InitialRing 2 :=
  ∑ l : Fin L, MvPolynomial.C (((Polynomial.X - Polynomial.C center) ^ l.val).coeff i.val) *
    centeredNumeratorAt G τ l.val
abbrev coefficientNumerator (G : Equation) (i : Fin k) : InitialRing 2 :=
  coefficientNumeratorAt G t i
def chart (G : Equation) (P : InitialRing 2) : Chart 2 :=
  ⟨P, initialSep G ^ t, coefficientNumerator G⟩
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
  covers : ∀ f : K[X], RegularRoot Q f →
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
theorem exponent_sufficient : TaylorExponentSufficient 2 k t := by
  intro l
  have hl := l.isLt
  unfold t
  omega
theorem centerMap_injective : Function.Injective centerMap :=
  (algebraMap FX Geo).injective.comp (IsFractionRing.injective K[X] FX)
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
private theorem eval_at_center (P : K[X]) : (P.map embed).eval center = centerMap P := by
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
theorem initial_eval (G : Equation) (f : K[X]) :
    MvPolynomial.eval (nativeJet f) (initial G) =
      centerMap (differentialSpecialization G f) := by
  rw [initial, ← MvPolynomial.aeval_eq_eval, aeval_initialJetEquation, nativeJet,
    ← eval_differentialSpecialization, lifted, ← map_differentialSpecialization, eval_at_center]
theorem initialSep_eval (G : Equation) (f : K[X]) :
    MvPolynomial.eval (nativeJet f) (initialSep G) =
      centerMap (differentialSpecialization (separant G (Fin.last 2)) f) := by
  have he : initialSep G = initial (separant G (Fin.last 2)) := by
    rw [initialSep, initialJetSeparant, initial, lifted, lifted, map_separant]
    rfl
  rw [he, initial_eval]
theorem coeff_reconstruction (G : Equation) (u : Fin 3 → Geo) {L : ℕ} (i : Fin L) :
    (rationalTaylorPolynomial center (lifted G) L u).coeff i.val =
      ∑ l : Fin L, ((Polynomial.X - Polynomial.C center) ^ l.val).coeff i.val *
        rationalTaylorCoefficient center (lifted G) u l.val := by
  rw [rationalTaylorPolynomial, centeredCoefficientPrefix, map_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro l _
  rw [taylor_monomial, coeff_C_mul, map_neg, ← sub_eq_add_neg, mul_comm]
theorem eval_coefficientNumerator (G : Equation) (u : Fin 3 → Geo)
    (h : MvPolynomial.eval u (initialSep G) ≠ 0) {L τ : ℕ}
    (hτ : TaylorExponentSufficient 2 L τ) (i : Fin L) :
    MvPolynomial.eval u (coefficientNumeratorAt G τ i) /
      MvPolynomial.eval u (initialSep G ^ τ) =
      (rationalTaylorPolynomial center (lifted G) L u).coeff i.val := by
  have hpow : MvPolynomial.eval u (initialSep G) ^ τ ≠ 0 := pow_ne_zero _ h
  rw [coeff_reconstruction, coefficientNumeratorAt, map_sum, map_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul, MvPolynomial.eval_C, centeredNumeratorAt]
  rw [← MvPolynomial.aeval_eq_eval (f := u),
    aeval_commonTaylorNumerator center (lifted G) u (hτ l) h]
  change _ * (MvPolynomial.eval u (initialSep G) ^ τ * _) /
    MvPolynomial.eval u (initialSep G) ^ τ = _
  field_simp
theorem chart_output (G : Equation) (P : InitialRing 2) (u : Fin 3 → Geo)
    (h : MvPolynomial.eval u (initialSep G) ≠ 0) (i : Fin k) :
    (chart G P).output u i = (rationalTaylorPolynomial center (lifted G) k u).coeff i.val := by
  simp only [Chart.output, chart]
  exact eval_coefficientNumerator G u h (L := k) (τ := t) exponent_sufficient i
theorem readJet_eq {L : ℕ} (P : Geo[X]) (hp : P.degree < L) (j : ℕ) :
    (∑ i : Fin L, (i.val.choose j : Geo) * center^(i.val-j) * P.coeff i.val) =
      (hasseDeriv j P).eval center := by
  rw [hasseDeriv_apply, ← Polynomial.sum_fin
    (fun i c => monomial (i - j) ((i.choose j : Geo) * c)) (by simp) hp, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_monomial]
  ring
theorem chart_recovers (G : Equation) (P : InitialRing 2) (u : Fin 3 → Geo)
    (h : MvPolynomial.eval u (initialSep G) ≠ 0) (j : Fin 3) :
    readJet ((chart G P).output u) j.val = u j := by
  let U := rationalTaylorPolynomial center (lifted G) k u
  have hout : (chart G P).output u = (fun i : Fin k => U.coeff i.val) := by
    funext i
    exact chart_output G P u h i
  have he : readJet ((chart G P).output u) j.val = readJet (fun i => U.coeff i.val) j.val :=
    congrArg (fun y : Fin k → Geo => readJet y j.val) hout
  have hd : U.degree < k := degree_centeredCoefficientPrefix_lt _ _ _
  have hj : readJet (fun i => U.coeff i.val) j.val = (hasseDeriv j.val U).eval center :=
    readJet_eq (L := k) U hd j.val
  refine he.trans (hj.trans ?_)
  exact congrFun (polynomialJet_rationalTaylorPolynomial center (lifted G)
    (by decide : 2 < k) u) j
theorem chart_at_solution (G : Equation) (P : InitialRing 2) (f : K[X])
    (hf : f.degree < k) (hg : differentialSpecialization G f = 0)
    (hsep : MvPolynomial.eval (nativeJet f) (initialSep G) ≠ 0) :
    (chart G P).output (nativeJet f) = coeffPoint f := by
  have hsol : differentialSpecialization (lifted G) (f.map embed) = 0 := by
    rw [lifted, ← map_differentialSpecialization, hg, Polynomial.map_zero]
  have hsep' : jetEvaluation (separant (lifted G) (Fin.last 2)) center (nativeJet f) ≠ 0 := by
    simpa only [initialSep, ← MvPolynomial.aeval_eq_eval, aeval_initialJetSeparant] using hsep
  have hd : (f.map embed).degree < k := (Polynomial.degree_map_eq_of_injective embed.injective f) ▸ hf
  let : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hbin (i : ℕ) (hlo : 2 < i) (hhi : i < k) : (i.choose 2 : Geo) ≠ 0 :=
    Sol1.C40Primitives.native_binomial_guard 2 le_rfl i hlo (Nat.lt_succ_of_lt hhi)
  have hrec := rationalTaylorPolynomial_polynomialJet center (lifted G) (f.map embed)
    hsol hsep' hd hbin
  funext i
  rw [chart_output G P (nativeJet f) hsep i, nativeJet, hrec, coeff_map]
  rfl
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
theorem weighted_map_eq {σ R S : Type*} [CommSemiring R] [CommSemiring S]
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
theorem topWeight_eq : (fun j : Option (Fin 3) =>
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
theorem coefficient_weight (G : Equation) {L τ : ℕ} (i : Fin L) (w : Fin 3 → ℕ) (d : ℕ)
    (h : ∀ l : Fin L, (centeredNumeratorAt G τ l.val).weightedTotalDegree w ≤ d) :
    (coefficientNumeratorAt G τ i).weightedTotalDegree w ≤ d := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  rw [coefficientNumeratorAt]
  apply Submodule.sum_mem
  intro l _
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  apply (weightedTotalDegree_mul_le _ _ _).trans
  simpa only [weightedTotalDegree_C, zero_add] using h l
private theorem indexWeight_eq : Astra7.jetWeight 0 1 3 = CJ0.indexWeight := by
  funext i
  cases i <;> simp [Astra7.jetWeight, CJ0.indexWeight]
theorem coeffWeight_eq : Astra7.coeffWeight 0 1 (2 + 1) = Fin.val := by
  funext i
  simp [Astra7.coeffWeight]
theorem lifted_index {s : Source} {G : Equation} (hG : OrderTwo s G) :
    (lifted G).weightedTotalDegree (Astra7.jetWeight 0 1 3) ≤ s.J := by
  rw [lifted_weight, indexWeight_eq]
  exact hG.2.2.1
theorem sep_index {s : Source} {G : Equation} (hG : OrderTwo s G) :
    (initialSep G).weightedTotalDegree Fin.val ≤ s.J - 2 := by
  simpa only [initialSep, coeffWeight_eq, zero_add, one_mul] using
    (Astra7.initialSeparant_weight 0 1 center (lifted G)).trans
      (Nat.sub_le_sub_right (lifted_index hG) (0 + 1 * 2))
theorem centered_index {s : Source} (hs : ShapeOK s) {G : Equation}
    (hG : OrderTwo s G) (l : Fin k) :
    (centeredNumerator G l).weightedTotalDegree Fin.val ≤ D s := by
  have hJ := hs.index_top
  have hC := hs.top_pos
  have hcap : 0 + 1 * 2 ≤ s.J := by omega
  have h := Astra7.commonTaylor_weight 0 1 s.J k t center (lifted G)
    exponent_sufficient hcap (lifted_index hG) l
  have hl : l.val ≤ k - 1 := by have := l.isLt; omega
  have hi : (centeredNumerator G l).weightedTotalDegree Fin.val ≤ t * (s.J - 2) + l.val := by
    simpa only [centeredNumeratorAt, coeffWeight_eq, zero_add, add_zero, one_mul] using h
  exact hi.trans (Nat.add_le_add_left hl _)
theorem centered_total {s : Source} {G : Equation} (hG : OrderTwo s G) (l : Fin k) :
    (centeredNumerator G l).totalDegree ≤ a₀ s := by
  apply (totalDegree_commonTaylorNumerator_le center (lifted G) (exponent_sufficient l)).trans
  rw [rationalTaylorCutDegreeBound, lifted_total]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hG.2.1 1)) _
theorem denominator_band {s : Source} {G : Equation} (hG : OrderTwo s G) :
    inBand₂ s (initialSep G ^ t) := by
  have ht : (initialSep G).totalDegree ≤ s.B - 1 := by
    apply (totalDegree_initialJetSeparant_le center (lifted G)).trans
    rw [lifted_total]
    exact Nat.sub_le_sub_right hG.2.1 1
  have htop : (initialSep G).degreeOf (Fin.last 2) ≤ s.C - 1 := by
    apply (degreeOf_initialJetSeparant_le center (lifted G)).trans
    change jetDegree (lifted G) (Fin.last 2) - 1 ≤ s.C - 1
    rw [lifted_top]
    exact Nat.sub_le_sub_right hG.2.2.2 1
  have hi : (initialSep G ^ t).weightedTotalDegree Fin.val ≤ D s :=
    ((weightedTotalDegree_pow_le Fin.val _ _).trans
      (Nat.mul_le_mul_left _ (sep_index hG))).trans (Nat.le_add_right _ _)
  refine ⟨(totalDegree_pow _ _).trans ((Nat.mul_le_mul_left _ ht).trans ?_), hi, ?_⟩
  · simpa only [a₀, Nat.add_comm] using Nat.le_add_right (t * (s.B - 1)) 1
  · apply le_min
    · exact (degreeOf_pow_le _ _ _).trans
        ((Nat.mul_le_mul_left _ htop).trans (Nat.le_add_right _ _))
    · exact degreeOf_top_of_index hi
theorem numerator_band {s : Source} (hs : ShapeOK s) {G : Equation} (hG : OrderTwo s G)
    (hTop : ∀ l, (centeredNumerator G l).degreeOf (Fin.last 2) ≤ t * (s.C - 1) + k - 2)
    (i : Fin k) : inBand₂ s (coefficientNumerator G i) := by
  have hi := coefficient_weight G (τ := t) i Fin.val (D s) (centered_index hs hG)
  refine ⟨?_, hi, le_min ?_ (degreeOf_top_of_index hi)⟩
  · rw [← weightedTotalDegree_one]
    apply coefficient_weight (τ := t)
    intro l
    simpa only [weightedTotalDegree_one] using centered_total hG l
  · rw [← weightedTotalDegree_piSingle]
    apply coefficient_weight (τ := t)
    intro l
    simpa only [weightedTotalDegree_piSingle] using hTop l
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
def c2 : Prop :=
  ∀ s, ShapeOK s → ∀ G : Equation, OrderTwo s G → ∀ l : Fin k,
    (centeredNumerator G l).degreeOf (Fin.last 2) ≤ t * (s.C - 1) + k - 2
theorem of_children (h1 : c1) (h2 : c2) : CJ0.c3 := by
  intro s hs Q hQ
  obtain ⟨F⟩ := h1 Q hQ.1
  let T : Family 2 := ⟨F.count, fun i => chart (F.source i) (F.equation i)⟩
  have htotal := factor_weights hQ F
  have hlocal (i : Fin F.count) := orderTwo_of_dvd hQ (F.source_dvd i)
  refine ⟨T, ⟨(factor_count F).trans htotal.1, ?_, htotal.1, htotal.2.1, htotal.2.2, ?_⟩, ?_⟩
  · intro i
    refine ⟨F.irreducible i, fun hd => F.regular i ((F.irreducible i).prime.dvd_of_dvd_pow hd), ?_⟩
    intro u hu j
    apply chart_recovers
    intro hz
    exact hu.2 (by
      change MvPolynomial.eval u (initialSep (F.source i) ^ t) = 0
      rw [map_pow, hz, zero_pow (by decide : t ≠ 0)])
  · intro i
    simp only [T, chart]
    refine ⟨denominator_band (hlocal i), ?_⟩
    intro j
    exact numerator_band (G := F.source i) hs (hlocal i) (h2 s hs (F.source i) (hlocal i)) j
  · intro f hf hr
    obtain ⟨i, hz, hp, hsep⟩ := F.covers f hr
    refine ⟨i, ?_⟩
    change coeffPoint f ∈ (chart (F.source i) (F.equation i)).imageSet
    refine ⟨nativeJet f, ⟨hp, ?_⟩, ?_⟩
    · change MvPolynomial.eval (nativeJet f) (initialSep (F.source i) ^ t) ≠ 0
      rw [map_pow]
      exact pow_ne_zero _ hsep
    · exact chart_at_solution (F.source i) (F.equation i) f hf hz hsep
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
def initialHom : Equation →+* InitialRing 2 :=
  (MvPolynomial.aeval (fun j : Option (Fin 3) =>
    j.elim (MvPolynomial.C center) MvPolynomial.X)).toRingHom.comp (MvPolynomial.map embed)
private theorem root_of_associated {G G' : Equation} {f : K[X]}
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
theorem jetWeight_initial :
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
theorem initial_coord_bound (l : ℕ) (hl : l < 3) :
    (MvPolynomial.X (⟨l, hl⟩ : Fin 3) : MvPolynomial (Fin 3) F).degreeOf (Fin.last 2) ≤ l - 1 := by
  rw [degreeOf_X]
  split
  · rename_i he
    have he' := congrArg Fin.val he
    change 2 = l at he'
    omega
  · exact Nat.zero_le _
theorem rationalTaylor_top (x : F) (Q : DifferentialPolynomial F 2) {c : ℕ}
    (hc : 0 < c) (hQ : Q.degreeOf (some (Fin.last 2)) ≤ c) (l : ℕ) :
    (rationalTaylorNumerator x Q l).degreeOf (Fin.last 2) ≤
      (2 * (l - 2) - 1) * (c - 1) + (l - 1) := by
  have hsep := (degreeOf_initialJetSeparant_le x Q).trans (Nat.sub_le_sub_right hQ 1)
  induction l using Nat.strong_induction_on with
  | h l ih =>
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
theorem proof : CJ0_3.c2 := by
  intro s hs G hG l
  have htop : (CJ0_3.lifted G).degreeOf (some (Fin.last 2)) ≤ s.C := by
    change (MvPolynomial.map embed G).degreeOf (some (Fin.last 2)) ≤ s.C
    have hGtop := hG.2.2.2
    simp only [jetDegree, degreeOf_def] at hGtop
    simp only [degreeOf_def]
    exact (Multiset.count_le_of_le _ (degrees_map_le (p := G) (f := embed))).trans hGtop
  have hb := commonTaylor_top center (CJ0_3.lifted G) hs.top_pos htop CJ0_3.exponent_sufficient l
  have hl : l.val - 1 ≤ k - 2 := by have := l.isLt; omega
  apply hb.trans
  rw [Nat.add_sub_assoc (by decide : 2 ≤ k)]
  exact Nat.add_le_add_left hl _
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
theorem in_zeroLocus {T : Chart r} {y : Fin (r+1) → Geo}
    (hy : y ∈ T.locus) : y ∈ zeroLocus Geo (sourceIdeal T) := by
  apply mem_zeroLocus_iff_le_ker_aeval.mpr
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact RingHom.mem_ker.mpr hy.1
private def pointEval {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus) :
    (InitialRing r ⧸ sourceIdeal T) →ₐ[Geo] Geo :=
  Ideal.Quotient.liftₐ (sourceIdeal T) (aeval y) fun q hq => in_zeroLocus hy q hq
private def openEval {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus) :
    ChartOpen T →ₐ[Geo] Geo :=
  IsLocalization.Away.liftAlgHom (f := pointEval hy)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
private theorem openEval_localize {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus)
    (q : InitialRing r) : openEval hy (localize T q) = eval y q :=
  IsLocalization.Away.lift_eq (g := (pointEval hy).toRingHom)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
    (Ideal.Quotient.mk (sourceIdeal T) q)
private theorem openEval_chartMap {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus)
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
theorem eq_zero_of_openEval {T : Chart r} [(sourceIdeal T).IsPrime]
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
theorem eval_jetForm (y : Fin k → Geo) (j : ℕ) :
    eval y (jetForm j) = readJet y j := by
  simp [jetForm, readJet]
theorem chartMap_recover (T : Chart r) (hT : ChartOK T) [(sourceIdeal T).IsPrime]
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
theorem quotientBand_add_finrank_le (T : Chart 2) (a d e b j c : ℕ)
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
theorem band_difference (a d e b j c : ℚ) :
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
theorem degree_le_of_quadratic
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
private theorem chart_degree (h1 : c1) (h2 : c2)
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
private theorem shape_chamber (s : Source) (hs : ShapeOK s) :
    D s ≤ a₀ s ∧ 2 * e s ≤ D s := by
  constructor
  · have hC := hs.top_pos
    have hJ := hs.index_top
    have hB := hs.total_index
    change 262137 * (s.J-2) + 131072 - 1 ≤ 1 + 262137 * (s.B-1)
    omega
  · have he : e s ≤ D s / 2 := min_le_right _ _
    omega
theorem family_budget (s : Source) (hs : ShapeOK s) (F : Family 2) (hF : Family₂ s F)
    (hdeg : ∀ i, affineDegree (F.chart i).ideal ≤
      surfaceBound (a₀ s) (D s) (e s) (F.chart i).equation.totalDegree
        (indexDegree (F.chart i).equation)
        ((F.chart i).equation.degreeOf (Fin.last 2))) :
    (∑ i, affineDegree (F.chart i).ideal) ≤ (R₂ s : ℚ) := by
  obtain ⟨hda, hde⟩ := shape_chamber s hs
  let a : ℚ := a₀ s
  let d : ℚ := D s
  let e₀ : ℚ := e s
  have hdaQ : d ≤ a := by
    change (D s : ℚ) ≤ (a₀ s : ℚ)
    exact_mod_cast hda
  have hdeQ : 2*e₀ ≤ d := by
    change 2 * (e s : ℚ) ≤ (D s : ℚ)
    exact_mod_cast hde
  have heQ : 0 ≤ e₀ := Nat.cast_nonneg _
  let u := 2 * e₀ * (d-e₀)
  let v := e₀ * (2*a-2*d+e₀)
  let w := (d-2*e₀) * (2*a-d)
  have hu : 0 ≤ u := mul_nonneg (mul_nonneg (by norm_num) heQ) (by linarith)
  have hv : 0 ≤ v := mul_nonneg heQ (by linarith)
  have hw : 0 ≤ w := mul_nonneg (by linarith) (by linarith)
  have hb : (∑ i, ((F.chart i).equation.totalDegree : ℚ)) ≤ (s.B : ℚ) := by
    exact_mod_cast hF.total
  have hj : (∑ i, (indexDegree (F.chart i).equation : ℚ)) ≤ (s.J : ℚ) := by
    exact_mod_cast hF.index
  have hc : (∑ i, ((F.chart i).equation.degreeOf (Fin.last 2) : ℚ)) ≤ (s.C : ℚ) := by
    exact_mod_cast hF.top
  have hD' : D s ≤ 2*a₀ s := by omega
  have hJ' : s.J ≤ 2*s.B := by have := hs.total_index; omega
  have he' : e s ≤ D s := by omega
  have hC' : 2*s.C*e s ≤ s.C*D s + e s*s.J := by
    calc
      _ = s.C * (2*e s) := by ring
      _ ≤ s.C*D s := Nat.mul_le_mul_left _ hde
      _ ≤ _ := Nat.le_add_right _ _
  calc
    _ ≤ ∑ i, surfaceBound a d e₀ (F.chart i).equation.totalDegree
        (indexDegree (F.chart i).equation)
        ((F.chart i).equation.degreeOf (Fin.last 2)) := Finset.sum_le_sum fun i _ => hdeg i
    _ = u * (∑ i, ((F.chart i).equation.totalDegree : ℚ)) +
        v * (∑ i, (indexDegree (F.chart i).equation : ℚ)) +
        w * (∑ i, ((F.chart i).equation.degreeOf (Fin.last 2) : ℚ)) := by
      simp only [surfaceBound, u, v, w, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ u*s.B + v*s.J + w*s.C :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb hu) (mul_le_mul_of_nonneg_left hj hv))
        (mul_le_mul_of_nonneg_left hc hw)
    _ = (R₂ s : ℚ) := by
      dsimp [u, v, w, a, d, e₀, R₂]
      push_cast [Nat.cast_sub hD', Nat.cast_sub hJ', Nat.cast_sub he', Nat.cast_sub hC']
      ring
theorem of_children (h1 : c1) (h2 : c2) : CJ0.c4 := by
  intro s hs F hF
  have hg := fun i => image_geometry (F.chart i) (hF.chart_ok i)
  refine ⟨fun i => (hg i).1, fun i => (hg i).2, family_budget s hs F hF ?_⟩
  obtain ⟨hda, hde⟩ := shape_chamber s hs
  intro i
  exact chart_degree h1 h2 (F.chart i) (hF.chart_ok i) (hg i).2 (a₀ s) (D s) (e s)
    hda hde (mem_bandSpace.mpr (hF.bands i).1) (fun j => mem_bandSpace.mpr ((hF.bands i).2 j))
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
abbrev BandExponents (a d e : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {u | u.degree ≤ a ∧ u.weight Fin.val ≤ d ∧ u (Fin.last 2) ≤ e}
private theorem degree_fin_three (u : Fin 3 →₀ ℕ) :
    u.degree = u 0 + u 1 + u 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc]
private theorem degree_fin_two (u : Fin 2 →₀ ℕ) : u.degree = u 0 + u 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
theorem index_fin_three (u : Fin 3 →₀ ℕ) :
    u.weight Fin.val = u 1 + 2 * u 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, Nat.mul_comm]
def bandFibers (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d) :
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
theorem two_mul_finrank_band (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d) :
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
