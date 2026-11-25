import ProximityPrize.SubmissionLower.R6960Low6960FatBanks

set_option Elab.async false

-- merged module R6960Low6960FatEliminate
section Merged_R6960Low6960FatEliminate

set_option Elab.async false
section
namespace Low6960Fat
noncomputable section
open K1 K1_13 K1_13_4_5
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
private theorem mixedWeight_pos {a : SeedVar →₀ ℕ} (ha : a ≠ 0) : 0 < mixedWeight a := by
  by_contra! h
  change 7074 * a none + 48749 * a.some.degree ≤ 0 at h
  have hn : a none = 0 := by omega
  have hd : a.some.degree = 0 := by omega
  have hs := (Finsupp.degree_eq_zero_iff _).mp hd
  apply ha
  ext i
  cases i with
  | none => simpa using hn
  | some i => simpa using DFunLike.congr_fun hs i
private theorem order_cancel_coeff (A B : GenericRow) (d : ℕ) (hA : A.coeff 0 ≠ 0)
    (hAB : ∀ a, mixedWeight a < d → (A * B).coeff a = 0) :
    ∀ a, mixedWeight a < d → B.coeff a = 0 := by
  classical
  suffices h : ∀ n a, mixedWeight a = n → n < d → B.coeff a = 0 by
    exact fun a ha => h _ a rfl ha
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a ha hd
    have hab := hAB a (ha.symm ▸ hd)
    rw [MvPolynomial.coeff_mul, Finset.sum_eq_single_of_mem (0, a) (by simp)] at hab
    · exact (mul_eq_zero.mp hab).resolve_left hA
    · intro b hb hbne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hb₁ : b.1 ≠ 0 := by
        intro hz
        apply hbne
        exact Prod.ext hz (by simpa [hz] using hs)
      have hw := mixedWeight_add b.1 b.2
      rw [hs, ha] at hw
      have hpos := mixedWeight_pos hb₁
      rw [ih (mixedWeight b.2) (by omega) b.2 rfl (by omega), mul_zero]
private theorem translated_const (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) :
    (translate (atPoint z y) F).coeff 0 = MvPolynomial.eval (atPoint z y) F := by
  let e : GenericRow →+* GenericX := MvPolynomial.eval (fun _ => 0)
  have he : e.comp (K1_13_4.translate (atPoint z y)) = MvPolynomial.eval (atPoint z y) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [e, K1_13_4.translate]
    · intro i
      simp [e, K1_13_4.translate]
  rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero']
  exact DFunLike.congr_fun he F
private theorem mixedOrder_cancel (A B : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ)
    (hA : MvPolynomial.eval (atPoint z y) A ≠ 0) (h : MixedOrder (A * B) z y d) :
    MixedOrder B z y d := by
  intro a ha
  by_contra! hlt
  refine (MvPolynomial.mem_support_iff.mp ha) (order_cancel_coeff
    (translate (atPoint z y) A) (translate (atPoint z y) B) d ?_ ?_ a hlt)
  · rwa [translated_const]
  · intro b hb
    rw [← map_mul]
    by_contra hne
    exact (Nat.not_lt_of_ge (h b (MvPolynomial.mem_support_iff.mpr hne))) hb
open P3_6_4 (moving_lower total_prod index_prod eval_prod_factor_ne_zero)
theorem eliminate_common (Γ : Finset K) (z : K → Geom) (S : K → (Polynomial Geom))
    (hzinj : Function.Injective z) {F G : GenericRow} (D : CommonPair F G)
    (hOrders : ∀ γ ∈ Γ, PairOrders F G (inclConst (z γ)) (trajectory (S γ))) :
      ∃ (book : Finset K) (Q : Lower), book.card ≤ 140000 ∧ Q ≠ 0 ∧
        Q.totalDegree ≤ 2502 ∧ lowerIndex Q ≤ 811 ∧
        ∀ γ ∈ Γ, γ ∉ book → MvPolynomial.eval (trajectory (S γ)) Q = 0 ∨
          PairOrders D.left D.right (inclConst (z γ)) (trajectory (S γ)) := by
  classical
  have fix_ne (f : GenericRow) (hf : f ∈ D.fixed) : f ≠ 0 :=
    (D.fixed_kind f hf).1.ne_zero
  have mov_ne (f : GenericRow) (hf : f ∈ D.moving) : f ≠ 0 :=
    (D.moving_kind f hf).1.ne_zero
  have mov_total : (∑ f ∈ D.moving, jetTotal f) ≤ 17 := by
    simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_total
  have mov_index : (∑ f ∈ D.moving, jetIndex f) ≤ 5 := by
    simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_index
  have mov_seed : (∑ f ∈ D.moving, seedDegree f) ≤ 70 := by
    simpa only [seedDegree, MvPolynomial.degreeOf_prod_eq _ _ mov_ne] using D.moving_seed
  have seed_le (f : GenericRow) (hf : f ∈ D.moving) : seedDegree f ≤ 70 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_seed
  choose! q qn qt qi qe using
    (fun f hf => fixed_lower f (fix_ne f hf) (D.fixed_kind f hf).2.2)
  have exists_moving (f : GenericRow) (hf : f ∈ D.moving) :=
    moving_lower f (D.moving_kind f hf).1 (D.moving_kind f hf).2.1
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_total)
      (D.moving_kind f hf).2.2.1 (D.moving_kind f hf).2.2.2
  choose! r rn rt ri re using exists_moving
  let P : Lower := ∏ f ∈ D.fixed, q f
  let R : Lower := ∏ f ∈ D.moving, r f
  have Pn : P ≠ 0 := Finset.prod_ne_zero_iff.mpr qn
  have Rn : R ≠ 0 := Finset.prod_ne_zero_iff.mpr rn
  have Pt : P.totalDegree ≤ 122 := by
    change (∏ f ∈ D.fixed, q f).totalDegree ≤ 122
    rw [total_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetTotal f := Finset.sum_congr rfl qt
      _ ≤ _ := by
        simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_total
  have Pi : lowerIndex P ≤ 41 := by
    change lowerIndex (∏ f ∈ D.fixed, q f) ≤ 41
    rw [index_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetIndex f := Finset.sum_congr rfl qi
      _ ≤ _ := by
        simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_index
  have Rt : R.totalDegree ≤ 2 * 70 * 17 := by
    change (∏ f ∈ D.moving, r f).totalDegree ≤ 2 * 70 * 17
    rw [total_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, (2 * 70) * jetTotal f :=
        Finset.sum_le_sum fun f hf => (rt f hf).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf)))
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ mov_total
  have Ri : lowerIndex R ≤ (2 * 5 + 1) * 70 := by
    change lowerIndex (∏ f ∈ D.moving, r f) ≤ (2 * 5 + 1) * 70
    rw [index_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, ((2 * 70) * jetIndex f + seedDegree f) := by
        apply Finset.sum_le_sum
        intro f hf
        refine (ri f hf).trans ?_
        rw [Nat.add_mul, one_mul, Nat.mul_right_comm 2]
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf))) _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hh := Nat.mul_le_mul_left (2 * 70) mov_index
        omega
  let book := seedBook Γ z D.pure
  have hbook : book.card ≤ 140000 :=
    (count_seed_roots Γ z hzinj D.pure D.pure_ne).trans D.pure_degree
  refine ⟨book, P * R, hbook, mul_ne_zero Pn Rn, ?_, ?_, ?_⟩
  · simp only [← MvPolynomial.weightedTotalDegree_one] at Pt Rt ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pt Rt).trans (show 122 + 2 * 70 * 17 ≤ 2502 by decide)
  · simp only [lowerIndex_eq_weighted] at Pi Ri ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pi Ri).trans (show 41 + (2 * 5 + 1) * 70 ≤ 811 by decide)
  · intro γ hγ hnot
    let a := inclConst (z γ)
    let y := trajectory (S γ)
    change MvPolynomial.eval y (P * R) = 0 ∨ PairOrders D.left D.right a y
    by_cases hn : MvPolynomial.eval y (P * R) = 0
    · exact Or.inl hn
    rw [map_mul] at hn
    have hfixed (f : GenericRow) (hf : f ∈ D.fixed) :
        MvPolynomial.eval (atPoint a y) f ≠ 0 := by
      rw [qe f hf]
      exact eval_prod_factor_ne_zero (left_ne_zero_of_mul hn) hf
    have hmoving (f : GenericRow) (hf : f ∈ D.moving) :
        MvPolynomial.eval (atPoint a y) f ≠ 0 := by
      intro h0
      exact (eval_prod_factor_ne_zero (right_ne_zero_of_mul hn) hf) (re f hf _ _ h0)
    have hp : D.pure.eval a ≠ 0 := fun he => hnot (mem_seedBook.mpr ⟨hγ, he⟩)
    let A := pureSeed D.pure * (∏ f ∈ D.fixed, f ^ D.exponent f) *
      (∏ f ∈ D.moving, f ^ D.exponent f)
    have hA : MvPolynomial.eval (atPoint a y) A ≠ 0 := by
      simp only [A, map_mul, map_prod, map_pow, pure_eval]
      exact mul_ne_zero (mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr
        fun f hf => pow_ne_zero _ (hfixed f hf))) (Finset.prod_ne_zero_iff.mpr
        fun f hf => pow_ne_zero _ (hmoving f hf))
    refine Or.inr ⟨mixedOrder_cancel A D.left a y _ hA ?_,
      mixedOrder_cancel A D.right a y _ hA ?_⟩
    · simpa only [A, ← D.left_eq] using (hOrders γ hγ).1
    · simpa only [A, ← D.right_eq] using (hOrders γ hγ).2
end
end Low6960Fat
end
section
namespace Low6960Fat
open Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open P3_6_4 (resultant_taylor_formal)
private def weight (d i : ℕ) : ℕ := d - 7074 * i
private def power (w : ℕ) : ℕ := (48748 + w) / 48749
private theorem coefficient_bound {k : Type*} [CommRing k]
    (P : (Polynomial (Polynomial k))) (d e i j : ℕ) (hij : j ≤ i)
    (hP : ∀ i l : ℕ, 7074 * i + 48749 * l < d → (P.coeff i).coeff l = 0) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (d + e) i - weight e j) ∣ P.coeff (i - j) := by
  have hweight : weight (d + e) i ≤ weight e j + weight d (i - j) := by
    unfold weight
    omega
  apply X_pow_dvd_iff.mpr
  intro l hl
  apply hP
  unfold power at hl
  have hsmall : 48749 * l < weight (d + e) i - weight e j := by omega
  unfold weight at hweight hsmall
  omega
private def columnWeight {m n : ℕ} (j : Fin (m + n)) : ℕ :=
  j.addCases (fun j : Fin m => weight firstOrder j) (fun j : Fin n => weight secondOrder j)
private theorem sylvester_entry {k : Type*} [CommRing k]
    (F G : (Polynomial (Polynomial k))) (m n : ℕ)
    (hF : ∀ i l : ℕ, 7074 * i + 48749 * l < firstOrder → (F.coeff i).coeff l = 0)
    (hG : ∀ i l : ℕ, 7074 * i + 48749 * l < secondOrder → (G.coeff i).coeff l = 0)
    (i j : Fin (m + n)) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (firstOrder + secondOrder) i - columnWeight j) ∣
      sylvester F G m n i j := by
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, columnWeight, Set.mem_Icc]
    split_ifs with h
    · simpa only [add_comm secondOrder firstOrder] using
        coefficient_bound G secondOrder firstOrder i j h.1 hG
    · exact dvd_zero _
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right, columnWeight, Set.mem_Icc]
    split_ifs with h
    · exact coefficient_bound F firstOrder secondOrder i j h.1 hF
    · exact dvd_zero _
private theorem det_bound {k : Type*} [CommRing k] {N D : ℕ}
    (M : Matrix (Fin N) (Fin N) (Polynomial k)) (row col : Fin N → ℕ)
    (hM : ∀ i j, (Polynomial.X : (Polynomial k)) ^ power (row i - col j) ∣ M i j)
    (hbudget : (∑ j, col j) + 48749 * D ≤ (∑ i, row i) + 48748) :
    (Polynomial.X : (Polynomial k)) ^ D ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a : Fin N → ℕ := fun j => power (row (σ j) - col j)
  have hprod : (Polynomial.X : (Polynomial k)) ^ (∑ j, a j) ∣ ∏ j, M (σ j) j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hM (σ j) j)
  have hsum : (∑ i, row i) ≤ (∑ j, col j) + 48749 * (∑ j, a j) := by
    rw [← Equiv.sum_comp σ row, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [a, power]
    omega
  have hD : D ≤ ∑ j, a j := by omega
  exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hD).trans hprod) _
private theorem sum_weight {d t N : ℕ} (ht : t ≤ N) (hend : d ≤ 7074 * t)
    (hbefore : ∀ i < t, 7074 * i ≤ d) :
    (∑ i : Fin N, weight d i) = t * d - 7074 * (t * (t - 1) / 2) := by
  rw [Fin.sum_univ_eq_sum_range]
  have htrim : (∑ i ∈ Finset.range t, weight d i) = ∑ i ∈ Finset.range N, weight d i := by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold weight
    omega
  rw [← htrim]
  have hsum : (∑ i ∈ Finset.range t, weight d i) + 7074 * (∑ i ∈ Finset.range t, i) =
      t * d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ Finset.range t, d := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := hbefore i (Finset.mem_range.mp hi)
        unfold weight
        omega
      _ = _ := by simp [Nat.mul_comm]
  rw [Finset.sum_range_id] at hsum
  omega
private theorem benchmark_budget :
    (∑ j : Fin (27000 + 27000), columnWeight (m := 27000) (n := 27000) j) + 48749 * 23893 ≤
      (∑ i : Fin (27000 + 27000), weight (firstOrder + secondOrder) i) + 48748 := by
  have hF : (∑ i : Fin 27000, weight firstOrder i) = 1459774464 := by
    rw [sum_weight (t := 642) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder]; omega)]
    decide
  have hG : (∑ i : Fin 27000, weight secondOrder i) = 233606575 := by
    rw [sum_weight (t := 257) (by decide) (by decide)
      (by intro i hi; simp only [secondOrder]; omega)]
    decide
  have hFG : (∑ i : Fin (27000 + 27000), weight (firstOrder + secondOrder) i) =
      2858127770 := by
    rw [sum_weight (t := 899) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder, secondOrder]; omega)]
    decide
  rw [Fin.sum_univ_add, hFG]
  simp only [columnWeight, Fin.addCases_left, Fin.addCases_right, hF, hG]
  decide
private theorem resultant_bound
    (F G : (Polynomial (Polynomial GenericX))) (z : GenericX) {m n D : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (hFO : ∀ i l : ℕ, 7074 * i + 48749 * l < firstOrder →
      ((F.taylor (C z)).coeff i).coeff l = 0)
    (hGO : ∀ i l : ℕ, 7074 * i + 48749 * l < secondOrder →
      ((G.taylor (C z)).coeff i).coeff l = 0)
    (hbudget : (∑ j : Fin (m + n), columnWeight (m := m) (n := n) j) + 48749 * D ≤
      (∑ i : Fin (m + n), weight (firstOrder + secondOrder) i) + 48748) :
    (Polynomial.X : (Polynomial GenericX)) ^ D ∣ resultant F G m n := by
  rw [← resultant_taylor_formal F G (C z) hF hG]
  unfold resultant
  exact det_bound
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i => weight (firstOrder + secondOrder) i)
    (columnWeight (m := m) (n := n))
    (sylvester_entry _ _ m n hFO hGO) hbudget
theorem line_resultant_order (F G : (Polynomial (Polynomial GenericX))) (z : GenericX)
    (hF : F.natDegree ≤ 27000) (hG : G.natDegree ≤ 27000)
    (hFO : ∀ i j, 7074 * i + 48749 * j < firstOrder →
      ((F.taylor (Polynomial.C z)).coeff i).coeff j = 0)
    (hGO : ∀ i j, 7074 * i + 48749 * j < secondOrder →
      ((G.taylor (Polynomial.C z)).coeff i).coeff j = 0) :
    (Polynomial.X : (Polynomial GenericX)) ^ 23893 ∣ Polynomial.resultant F G 27000 27000 := by
  exact resultant_bound F G z (m := 27000) (n := 27000) (D := 23893)
    hF hG hFO hGO benchmark_budget
end Low6960Fat
end
section
namespace Low6960Fat
noncomputable section
open K1_13 Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped BigOperators
set_option maxRecDepth 4000
private def ray (v : Fin 3 → GenericX) : Lower →+* (Polynomial GenericX) :=
  MvPolynomial.eval₂Hom C (fun i => C (v i) * Polynomial.X)
private theorem ray_monomial (v : Fin 3 → GenericX) (a : Fin 3 →₀ ℕ) (c : GenericX) :
    ray v (MvPolynomial.monomial a c) =
      monomial a.degree (MvPolynomial.eval v (MvPolynomial.monomial a c)) := by
  rw [← C_mul_X_pow_eq_monomial]
  simp only [ray, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial, mul_pow,
    Finsupp.prod]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply, ← mul_assoc]
  simp only [map_mul, map_prod, map_pow]
private theorem ray_coeff (v : Fin 3 → GenericX) (Q : Lower) (j : ℕ) :
    (ray v Q).coeff j = MvPolynomial.eval v (MvPolynomial.homogeneousComponent j Q) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [ray_monomial, coeff_monomial,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    by_cases h : a.degree = j
    · simp [h]
    · simp [h, Ne.symm h]
  | add Q R hQ hR =>
    rw [map_add, coeff_add, hQ, hR, map_add, map_add]
private theorem line_translation (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX) :
    ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).comp (Polynomial.X + C (C z)) =
      (asSeedPoly (K1_13_4.translate (atPoint z y) F)).map (ray v) := by
  let e := (MvPolynomial.optionEquivLeft GenericX (Fin 3)).toRingHom
  let left := (compRingHom (Polynomial.X + C (C z))).comp ((mapRingHom ((ray v).comp (K1_13_4.translate y))).comp e)
  let right := (mapRingHom (ray v)).comp (e.comp (K1_13_4.translate (atPoint z y)))
  have he : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, e, K1_13_4.translate, ray]
    · intro i
      cases i <;>
        simp [left, right, e, K1_13_4.translate, ray, atPoint]
  exact DFunLike.congr_fun he F
private theorem line_order (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX)
    (d : ℕ) (hF : MixedOrder F z y d) :
    ∀ i j, 7074 * i + 48749 * j < d →
      ((((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).taylor (C z)).coeff i).coeff j = 0 := by
  intro i j h
  change ((((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).comp
    (Polynomial.X + C (C z))).coeff i).coeff j = 0
  rw [line_translation, coeff_map, ray_coeff]
  suffices hc : MvPolynomial.homogeneousComponent j
      ((asSeedPoly (K1_13_4.translate (atPoint z y) F)).coeff i) = 0 by
    rw [hc, map_zero]
  apply MvPolynomial.homogeneousComponent_eq_zero'
  intro a ha hj
  have hmem : a.optionElim i ∈ (K1_13_4.translate (atPoint z y) F).support := by
    rw [← MvPolynomial.mem_support_coeff_optionEquivLeft]
    exact ha
  have hb := hF _ hmem
  have hweight : mixedWeight (a.optionElim i) = 7074 * i + 48749 * j := by
    change 7074 * a.optionElim i none + 48749 * (a.optionElim i).some.degree = _
    rw [Finsupp.optionElim_apply_none, Finsupp.some_optionElim, hj]
  rw [hweight] at hb
  exact (Nat.not_lt_of_ge hb) h
private theorem order_of_rays (Q : Lower) (y : Fin 3 → GenericX) (d : ℕ)
    (h : ∀ v, Polynomial.X ^ d ∣ ray v (K1_13_4.translate y Q)) :
    LowerOrder Q y d := by
  let _ : Infinite GenericX := Infinite.of_injective inclConst inclConst.injective
  intro a ha
  change d ≤ a.degree
  by_contra! ha'
  have hm : MvPolynomial.homogeneousComponent a.degree (K1_13_4.translate y Q) = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_zero, ← ray_coeff]
    exact (X_pow_dvd_iff (n := d) (f := ray v (K1_13_4.translate y Q))).mp (h v) a.degree ha'
  have hc := congrArg (fun P : Lower => P.coeff a) hm
  simp [MvPolynomial.coeff_homogeneousComponent] at hc
  exact (MvPolynomial.mem_support_iff.mp ha) hc
def seedResultant27 (F G : GenericRow) : Lower :=
  Polynomial.resultant (asSeedPoly F) (asSeedPoly G) 27000 27000
private theorem line_resultant (F G : GenericRow) (y v : Fin 3 → GenericX) :
    resultant ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y)))
      ((asSeedPoly G).map ((ray v).comp (K1_13_4.translate y))) 27000 27000 =
        ray v (K1_13_4.translate y (seedResultant27 F G)) := by
  unfold seedResultant27
  rw [resultant_map_map, RingHom.comp_apply]
theorem mixedOrder_pad {F : GenericRow} {z : GenericX} {y : Fin 3 → GenericX}
    {d : ℕ} (a : (Polynomial Geom)) (h : MixedOrder F z y d) :
    MixedOrder (pad F a) z y d := by
  classical
  intro m hm
  rw [pad, map_mul] at hm
  obtain ⟨u, hu, v, _, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [mixedWeight_add]; exact Nat.le_add_right _ _)
theorem resultant_order (F G : GenericRow) (z : GenericX)
    (y : Fin 3 → GenericX) (hF : (asSeedPoly F).natDegree ≤ 27000)
    (hG : (asSeedPoly G).natDegree ≤ 27000) (h : PairOrders F G z y) :
    LowerOrder (seedResultant27 F G) y 23893 := by
  apply order_of_rays
  intro v
  rw [← line_resultant F G y v]
  exact line_resultant_order _ _ z (natDegree_map_le.trans hF) (natDegree_map_le.trans hG)
    (line_order F z y v _ h.1) (line_order G z y v _ h.2)
end
end Low6960Fat
end

#print axioms Low6960Fat.resultant_order

end Merged_R6960Low6960FatEliminate

-- merged module R6960Low6960FatPadding
section Merged_R6960Low6960FatPadding

set_option Elab.async false
/-! Low-specific padding of a coprime pair to seed degree exactly 27,000 and the resulting
resultant box (367,443,000, 124,200,000); a copy of the padding part of `Fast074`. -/
section
namespace Low6960Fat
noncomputable section
open K1_13 K1_13_4 Polynomial
open scoped Polynomial BigOperators Pointwise
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open K1_13_4_6 (Fiber toFiber embedConstant toFiber_injective coprime_in_fiber exists_constant_nonroot coprime_linear asSeedPoly_ne_zero deg deg_pad_coeff deg_resultant)
structure PaddedPair27 (F G : GenericRow) where
  a : (Polynomial Geom)
  b : (Polynomial Geom)
  degree_left : (asSeedPoly (pad F a)).natDegree = 27000
  degree_right : (asSeedPoly (pad G b)).natDegree = 27000
  nonzero : seedResultant27 (pad F a) (pad G b) ≠ 0
  total : (seedResultant27 (pad F a) (pad G b)).totalDegree ≤ 367443000
  index : lowerIndex (seedResultant27 (pad F a) (pad G b)) ≤ 124200000
  keeps_order : ∀ z y, PairOrders F G z y → PairOrders (pad F a) (pad G b) z y
private theorem pad_degree27 (F : GenericRow) (hF : F ≠ 0)
    (hcap : seedDegree F ≤ 27000) (a : Geom) :
    (asSeedPoly (pad F (((Polynomial.X : (Polynomial Geom)) - C a) ^
      (27000 - (asSeedPoly F).natDegree)))).natDegree = 27000 := by
  have hcap' : (asSeedPoly F).natDegree ≤ 27000 := by
    simpa only [asSeedPoly, MvPolynomial.natDegree_optionEquivLeft, seedDegree] using hcap
  rw [K1_13_4_6.asSeedPoly_pad, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    natDegree_mul (asSeedPoly_ne_zero hF) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow, natDegree_X_sub_C, mul_one, Nat.add_sub_of_le hcap']
theorem padding_exists27 {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0)
    (hfg : IsRelPrime F G) (hf : seedDegree F ≤ 27000) (hg : seedDegree G ≤ 27000) :
    ∃ a b : (Polynomial Geom), (asSeedPoly (pad F a)).natDegree = 27000 ∧
      (asSeedPoly (pad G b)).natDegree = 27000 ∧ seedResultant27 (pad F a) (pad G b) ≠ 0 := by
  classical
  let f := (asSeedPoly F).map toFiber
  let g := (asSeedPoly G).map toFiber
  have hf0 : f ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hF)
  have hg0 : g ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hG)
  have hcop : IsCoprime f g := by
    apply coprime_in_fiber (asSeedPoly_ne_zero hF)
    intro d hdf hdg
    let e := MvPolynomial.optionEquivLeft GenericX (Fin 3)
    have hu : IsUnit (e.symm d) :=
      hfg (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdf)
        (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdg)
    have he := hu.map e.toRingHom
    change IsUnit (e (e.symm d)) at he
    rwa [e.apply_symm_apply] at he
  obtain ⟨a, ha, _⟩ := exists_constant_nonroot g hg0 ∅
  obtain ⟨b, hb, hba⟩ := exists_constant_nonroot f hf0 {toFiber (embedConstant a)}
  let p := ((Polynomial.X : (Polynomial Geom)) - C a) ^ (27000 - (asSeedPoly F).natDegree)
  let q := ((Polynomial.X : (Polynomial Geom)) - C b) ^ (27000 - (asSeedPoly G).natDegree)
  have hp : (asSeedPoly (pad F p)).natDegree = 27000 := pad_degree27 F hF hf a
  have hq : (asSeedPoly (pad G q)).natDegree = 27000 := pad_degree27 G hG hg b
  refine ⟨p, q, hp, hq, ?_⟩
  have hab : toFiber (embedConstant a) ≠ toFiber (embedConstant b) := by
    simpa using (Finset.notMem_singleton.mp hba).symm
  have hpad : IsCoprime ((asSeedPoly (pad F p)).map toFiber)
      ((asSeedPoly (pad G q)).map toFiber) := by
    simp only [K1_13_4_6.asSeedPoly_pad, Polynomial.map_mul, p, q, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    exact (hcop.mul_right (coprime_linear f hb).symm.pow_right).mul_left
      ((coprime_linear g ha).pow_left.mul_right
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow)
  have hn := resultant_ne_zero _ _ hpad
  rw [natDegree_map_eq_of_injective toFiber_injective,
    natDegree_map_eq_of_injective toFiber_injective, hp, hq, resultant_map_map] at hn
  intro hz
  exact hn ((congrArg toFiber hz).trans (map_zero _))

theorem padded27 {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0) (hp : IsRelPrime F G)
    (hf : Low6960Fat.Caps27 firstBox F) (hg : Low6960Fat.Caps27 secondBox G) :
    Nonempty (PaddedPair27 F G) := by
  obtain ⟨a, b, ha, hb, hn⟩ := padding_exists27 hF hG hp (hf.2.trans (by decide)) (hg.2.trans (by decide))
  refine ⟨⟨a, b, ha, hb, hn, ?_, ?_, ?_⟩⟩
  · have h := deg_resultant (1 : Fin 3 → ℕ) (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      27000 27000 6789 6820 (fun i => (deg_pad_coeff _ F a i).trans hf.1.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1.1)
    simpa only [MvPolynomial.weightedTotalDegree_one, seedResultant27,
      ← Nat.mul_add, Nat.add_comm 6820 6789] using h.trans_eq (by norm_num)
  · have h := deg_resultant Fin.val (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      27000 27000 2300 2300 (fun i => (deg_pad_coeff _ F a i).trans hf.1.2.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1.2.1)
    simpa only [MvPolynomial.weightedTotalDegree, Finsupp.weight_apply, Nat.nsmul_eq_mul,
      Nat.mul_comm, lowerIndex, seedResultant27, ← Nat.mul_add] using h.trans_eq (by norm_num)
  · intro z y h
    exact ⟨mixedOrder_pad a h.1, mixedOrder_pad b h.2⟩
end
end Low6960Fat
end

end Merged_R6960Low6960FatPadding
