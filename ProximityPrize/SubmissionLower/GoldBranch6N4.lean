import ProximityPrize.SubmissionLower.GoldBranch3
import ProximityPrize.SubmissionLower.GoldBranch6
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_4
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
abbrev firstOrder : ℕ := 6317872
abbrev secondOrder : ℕ := 3661738
abbrev firstCut : ℕ := 5000 * P3.agreement - firstOrder
abbrev secondCut : ℕ := 5000 * P3.agreement - secondOrder
abbrev bankRank : ℕ := 0x4b8ba3f30d83cce664
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  6819 * a none + 48914 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
def Necessary {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P) :
    Submodule Geom PhysicalRow :=
  Submodule.span Geom {Q | ∃ t F a, Source w P L secondBox t F ∧
    t + mixedWeight a ≤ secondCut ∧ Q = mixedHasse a F}
def MixedOrder (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ) : Prop :=
  ∀ a ∈ (translate (atPoint z y) F).support, d ≤ mixedWeight a
def PairOrders (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) : Prop :=
  MixedOrder F z y firstOrder ∧ MixedOrder G z y secondOrder
structure CommonPair (F G : GenericRow) where
  fixed : Finset GenericRow
  moving : Finset GenericRow
  pure : GenericX[X]
  exponent : GenericRow → ℕ
  left : GenericRow
  right : GenericRow
  pure_ne : pure ≠ 0
  pure_degree : pure.natDegree ≤ 140000
  fixed_kind : ∀ f ∈ fixed, Irreducible f ∧ 0 < jetTotal f ∧ seedDegree f = 0
  moving_kind : ∀ f ∈ moving, Irreducible f ∧ 0 < jetTotal f ∧
    0 < seedDegree f ∧ f.degreeOf (some 2) = 0
  fixed_total : jetTotal (∏ f ∈ fixed, f) ≤ 125
  fixed_index : jetIndex (∏ f ∈ fixed, f) ≤ 42
  moving_total : jetTotal (∏ f ∈ moving, f) ≤ 17
  moving_index : jetIndex (∏ f ∈ moving, f) ≤ 5
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 180
  left_eq : F = (pureSeed pure * (∏ f ∈ fixed, f ^ exponent f) *
    (∏ f ∈ moving, f ^ exponent f)) * left
  right_eq : G = (pureSeed pure * (∏ f ∈ fixed, f ^ exponent f) *
    (∏ f ∈ moving, f ^ exponent f)) * right
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  proper : IsRelPrime left right
  left_caps : Caps firstBox left
  right_caps : Caps secondBox right
end
end P3_6_4
end
section
namespace P3_6_4
noncomputable section
open K1_13 K1_13_4 MvPolynomial
open scoped Polynomial BigOperators
open P0_9_4 (clear_denominators)
open private inclX_injective coefficientDerivative coeff_coefficientDerivative
  dotted polynomialPoint eval_dotted eval_map_point degreeOf_le_of_support_subset
  dotted_weight seed_weight from ProximityPrize.SubmissionLower.PortLow4
private theorem small_cast_ne_zero (n : ℕ) (hpos : 0 < n) (hsmall : n ≤ 17) :
    (n : GenericX) ≠ 0 := by
  let : CharP GenericX K1.p := charP_of_injective_ringHom (inclConst.comp embed).injective K1.p
  intro hz
  have hlarge : 17 < K1.p := by decide
  exact (not_le_of_gt (hsmall.trans_lt hlarge))
    (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff GenericX K1.p n).mp hz))
private theorem pderiv_moved {P : GenericRow} {i j k : SeedVar} (h : P.degreeOf k = 0) :
    pderiv k (MvPolynomial.X j * pderiv i P) = pderiv k (MvPolynomial.X j : GenericRow) * pderiv i P := by
  have hzero : pderiv k (pderiv i P) = 0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero (Nat.eq_zero_of_le_zero ((degreeOf_pderiv_le i k P).trans_eq h))
  rw [pderiv_mul, hzero, mul_zero, add_zero]
private theorem partial_not_dvd {f g : GenericRow} (i k : SeedVar) (a : GenericX)
    (hi : 0 < f.degreeOf i) (hsmall : f.degreeOf i ≤ 17) (hk : f.degreeOf k = 0)
    (ha : a ≠ 0) (hg : pderiv k g = C a * pderiv i f) : ¬ f ∣ g := by
  have hpartial : pderiv i f ≠ 0 :=
    pderiv_ne_zero_of_natCast_ne_zero i f (small_cast_ne_zero _ hi hsmall)
  have hnonzero : C a * pderiv i f ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha) hpartial
  have hdegree : (C a * pderiv i f).degreeOf i ≤ f.degreeOf i - 1 :=
    (degreeOf_C_mul_le _ _ _).trans (degreeOf_pderiv_le_sub_one i f)
  rintro ⟨q, hq⟩
  rw [hq, pderiv_mul, pderiv_eq_zero_of_degreeOf_eq_zero hk, zero_mul, zero_add] at hg
  have hq' : pderiv k q ≠ 0 := by
    intro hz
    exact hnonzero (by rw [← hg, hz, mul_zero])
  rw [← hg, degreeOf_mul_eq (ne_zero_of_degreeOf_ne_zero hi.ne') hq'] at hdegree
  omega
private theorem dotted_relPrime {f r : GenericRow} (hf : Irreducible f)
    (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 17) (htop : f.degreeOf (some 2) = 0)
    (hr : r.support ⊆ f.support) (a : GenericX) (ha : a ≠ 0) :
    IsRelPrime f (dotted r (C a * f)) := by
  have hd (i : SeedVar) : (C a * f).degreeOf i = f.degreeOf i := by
    rw [degreeOf_mul_eq (C_ne_zero.mpr ha) hf.ne_zero, degreeOf_C, zero_add]
  have hsmall (i : Fin 3) : f.degreeOf (some i) ≤ 17 :=
    (degreeOf_le_weightedTotalDegree (fun j : SeedVar => j.elim 0 (fun _ => 1))
      (some i) (show 0 < (1 : ℕ) by decide) f).trans ht
  have hzero (i : SeedVar) (hi : f.degreeOf i = 0) : pderiv i r = 0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero (Nat.eq_zero_of_le_zero
      ((degreeOf_le_of_support_subset hr i).trans_eq hi))
  have htop' : (C a * f).degreeOf (some 2) = 0 := (hd _).trans htop
  apply hf.isRelPrime_iff_not_dvd.mpr
  by_cases h₁ : f.degreeOf (some 1) = 0
  · have h₀ : 0 < f.degreeOf (some 0) := by
      by_contra! h₀
      have hz : jetTotal f ≤ 0 := by
        apply Finset.sup_le
        intro m hm
        have hm₀ := (le_degreeOf_of_mem_support (some 0) hm).trans h₀
        have hm₁ := (le_degreeOf_of_mem_support (some 1) hm).trans_eq h₁
        have hm₂ := (le_degreeOf_of_mem_support (some 2) hm).trans_eq htop
        rw [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_three]
        simp [Nat.eq_zero_of_le_zero hm₀, Nat.eq_zero_of_le_zero hm₁, Nat.eq_zero_of_le_zero hm₂]
      omega
    have h₁' : (C a * f).degreeOf (some 1) = 0 := (hd _).trans h₁
    refine partial_not_dvd (some 0) (some 1) a h₀ (hsmall 0) h₁ ha ?_
    unfold dotted
    rw [pderiv_eq_zero_of_degreeOf_eq_zero h₁']
    simp only [mul_zero, add_zero, map_add, hzero _ h₁, zero_add, pderiv_moved h₁',
      pderiv_X_self, one_mul]
    rw [pderiv_C_mul]
  · refine partial_not_dvd (some 1) (some 2) ((2 : GenericX) * a) (Nat.pos_of_ne_zero h₁)
      (hsmall 1) htop (mul_ne_zero (small_cast_ne_zero 2 (by decide) (by decide)) ha) ?_
    unfold dotted
    rw [map_add, map_add, hzero _ htop, pderiv_moved (i := some 0) (j := some 1) htop',
      pderiv_X_of_ne (by decide : (some 1 : SeedVar) ≠ some 2), zero_mul, add_zero,
      pderiv_C_mul, pderiv_moved htop', pderiv_X_self, one_mul, pderiv_C_mul]
    simp only [zero_add, map_mul, mul_assoc]
theorem moving_cutter (f : GenericRow) (hf : Irreducible f)
    (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 17) (htop : f.degreeOf (some 2) = 0) :
    ∃ g : GenericRow, IsRelPrime f g ∧ seedDegree g ≤ seedDegree f ∧
      jetTotal g ≤ jetTotal f ∧ jetIndex g ≤ jetIndex f + 1 ∧
      ∀ (z : Geom) (S : Geom[X]),
        eval (atPoint (inclConst z) (trajectory S)) f = 0 →
        eval (atPoint (inclConst z) (trajectory S)) g = 0 := by
  obtain ⟨d, P, hd, hs, hP⟩ := clear_denominators f
  let r := MvPolynomial.map inclX (coefficientDerivative P)
  let A := MvPolynomial.map inclX P
  have hA : A.support = f.support := (support_map_of_injective P inclX_injective).trans hs
  have hr : r.support ⊆ f.support := by
    intro m hm
    rw [← hs, MvPolynomial.mem_support_iff]
    rw [MvPolynomial.mem_support_iff, coeff_map, coeff_coefficientDerivative] at hm
    intro hz
    exact hm (by rw [hz, map_zero, map_zero])
  have htopP : P.degreeOf (some 2) = 0 := by rwa [degreeOf_eq_sup, hs, ← degreeOf_eq_sup]
  have ha : inclX d ≠ 0 := (map_ne_zero_iff inclX inclX_injective).mpr hd
  refine ⟨dotted r A, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show A = C (inclX d) * f from hP]
    exact dotted_relPrime hf hb ht htop hr _ ha
  · rw [← seed_weight, ← seed_weight]
    simpa [weightedTotalDegree, hA] using
      dotted_weight (Pi.single none 1) r A 0 (hA.symm ▸ hr) (by decide) (by decide)
  · simpa [jetTotal, weightedTotalDegree, hA] using
      dotted_weight (fun i => i.elim 0 (fun _ => 1)) r A 0 (hA.symm ▸ hr) (by decide) (by decide)
  · simpa [jetIndex, weightedTotalDegree, hA] using
      dotted_weight (fun i => i.elim 0 Fin.val) r A 1 (hA.symm ▸ hr) (by decide) (by decide)
  · intro z S hz
    have hzP : eval (polynomialPoint z S) P = 0 := by
      apply inclX_injective
      rw [map_zero, ← eval_map_point, hP, map_mul, hz, mul_zero]
    have hmap : dotted r A = MvPolynomial.map inclX (dotted (coefficientDerivative P) P) := by
      simp only [dotted, A, r, map_add, map_mul, map_X, pderiv_map, map_ofNat]
    rw [hmap, eval_map_point, eval_dotted P z S htopP, hzP, map_zero, map_zero]
end
end P3_6_4
end
section
namespace P3_6_4
noncomputable section
open K1 K1_13 K1_13_4_5
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
private theorem mixedWeight_pos {a : SeedVar →₀ ℕ} (ha : a ≠ 0) : 0 < mixedWeight a := by
  by_contra! h
  change 6819 * a none + 48914 * a.some.degree ≤ 0 at h
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
  | h n ih =>
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
private theorem moving_lower (f : GenericRow)
    (hf : Irreducible f) (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 17)
    (hu : 0 < seedDegree f) (htop : f.degreeOf (some 2) = 0) :
    ∃ q : Lower, q ≠ 0 ∧ q.totalDegree ≤ 2 * seedDegree f * jetTotal f ∧
      lowerIndex q ≤ (2 * jetIndex f + 1) * seedDegree f ∧
      ∀ (z : Geom) (S : Geom[X]),
        MvPolynomial.eval (atPoint (inclConst z) (trajectory S)) f = 0 →
        MvPolynomial.eval (trajectory S) q = 0 := by
  obtain ⟨g, hrel, hgu, hgb, hgj, htraj⟩ := moving_cutter f hf hb ht htop
  obtain ⟨htot, hind⟩ := K1_13_4_5_2.proof f g
  refine ⟨actualSeedResultant f g, actual_resultant_ne_zero hf hu hrel, ?_, ?_, fun z S hz =>
    actual_resultant_vanishes hu hz (htraj z S hz)⟩
  · calc
      _ ≤ seedDegree f * jetTotal f + seedDegree f * jetTotal f :=
        htot.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hgu) (Nat.mul_le_mul_left _ hgb))
      _ = _ := by ring
  · calc
      _ ≤ seedDegree f * jetIndex f + seedDegree f * (jetIndex f + 1) :=
        hind.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hgu) (Nat.mul_le_mul_left _ hgj))
      _ = _ := by ring
private theorem total_prod {ι : Type*} (s : Finset ι) (q : ι → Lower)
    (hn : ∀ i ∈ s, q i ≠ 0) :
    (∏ i ∈ s, q i).totalDegree = ∑ i ∈ s, (q i).totalDegree := by
  simp only [← MvPolynomial.weightedTotalDegree_one]
  exact MvPolynomial.weightedTotalDegree_prod _ s q hn
private theorem index_prod {ι : Type*} (s : Finset ι) (q : ι → Lower)
    (hn : ∀ i ∈ s, q i ≠ 0) :
    lowerIndex (∏ i ∈ s, q i) = ∑ i ∈ s, lowerIndex (q i) := by
  simp only [lowerIndex_eq_weighted]
  exact MvPolynomial.weightedTotalDegree_prod _ s q hn
private theorem eval_prod_factor_ne_zero {ι : Type*} {s : Finset ι} {q : ι → Lower}
    {y : Fin 3 → GenericX} (hq : MvPolynomial.eval y (∏ i ∈ s, q i) ≠ 0)
    {i : ι} (hi : i ∈ s) : MvPolynomial.eval y (q i) ≠ 0 :=
  (Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hq)) i hi
theorem eliminate_common (Γ : Finset K) (z : K → Geom) (S : K → Geom[X])
    (hzinj : Function.Injective z) {F G : GenericRow} (D : CommonPair F G)
    (hOrders : ∀ γ ∈ Γ, PairOrders F G (inclConst (z γ)) (trajectory (S γ))) :
      ∃ (book : Finset K) (Q : Lower), book.card ≤ 140000 ∧ Q ≠ 0 ∧
        Q.totalDegree ≤ 6245 ∧ lowerIndex Q ≤ 2022 ∧
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
  have mov_seed : (∑ f ∈ D.moving, seedDegree f) ≤ 180 := by
    simpa only [seedDegree, MvPolynomial.degreeOf_prod_eq _ _ mov_ne] using D.moving_seed
  have seed_le (f : GenericRow) (hf : f ∈ D.moving) : seedDegree f ≤ 180 :=
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
  have Pt : P.totalDegree ≤ 125 := by
    change (∏ f ∈ D.fixed, q f).totalDegree ≤ 125
    rw [total_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetTotal f := Finset.sum_congr rfl qt
      _ ≤ _ := by
        simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_total
  have Pi : lowerIndex P ≤ 42 := by
    change lowerIndex (∏ f ∈ D.fixed, q f) ≤ 42
    rw [index_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetIndex f := Finset.sum_congr rfl qi
      _ ≤ _ := by
        simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_index
  have Rt : R.totalDegree ≤ 2 * 180 * 17 := by
    change (∏ f ∈ D.moving, r f).totalDegree ≤ 2 * 180 * 17
    rw [total_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, (2 * 180) * jetTotal f :=
        Finset.sum_le_sum fun f hf => (rt f hf).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf)))
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ mov_total
  have Ri : lowerIndex R ≤ (2 * 5 + 1) * 180 := by
    change lowerIndex (∏ f ∈ D.moving, r f) ≤ (2 * 5 + 1) * 180
    rw [index_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, ((2 * 180) * jetIndex f + seedDegree f) := by
        apply Finset.sum_le_sum
        intro f hf
        refine (ri f hf).trans ?_
        rw [Nat.add_mul, one_mul, Nat.mul_right_comm 2]
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf))) _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hh := Nat.mul_le_mul_left (2 * 180) mov_index
        omega
  let book := seedBook Γ z D.pure
  have hbook : book.card ≤ 140000 :=
    (count_seed_roots Γ z hzinj D.pure D.pure_ne).trans D.pure_degree
  refine ⟨book, P * R, hbook, mul_ne_zero Pn Rn, ?_, ?_, ?_⟩
  · simp only [← MvPolynomial.weightedTotalDegree_one] at Pt Rt ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pt Rt).trans (show 125 + 2 * 180 * 17 ≤ 6245 by decide)
  · simp only [lowerIndex_eq_weighted] at Pi Ri ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pi Ri).trans (show 42 + (2 * 5 + 1) * 180 ≤ 2022 by decide)
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
end P3_6_4
end
section
namespace P3_6_4
open Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
private theorem resultant_taylor_formal {R : Type*} [CommRing R]
    (F G : R[X]) (z : R) {m n : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) :
    resultant (F.taylor z) (G.taylor z) m n = resultant F G m n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hF
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hG
  have expand (P Q : R[X]) :
      resultant P Q (P.natDegree + a) (Q.natDegree + b) =
        (-1) ^ ((Q.natDegree + b) * a) * Q.coeff (Q.natDegree + b) ^ a *
          (P.leadingCoeff ^ b * resultant P Q) := by
    rw [resultant_add_left_deg _ _ _ _ _ le_rfl,
      resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  have coeff_preserved :
      (G.taylor z).coeff (G.natDegree + b) = G.coeff (G.natDegree + b) := by
    by_cases hb : b = 0
    · simp [hb]
    · have hlt : G.natDegree < G.natDegree + b := by omega
      rw [coeff_eq_zero_of_natDegree_lt hlt,
        coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hlt)]
  have h := expand (F.taylor z) (G.taylor z)
  rw [resultant_taylor] at h
  simp only [natDegree_taylor, leadingCoeff_taylor, coeff_preserved] at h
  exact h.trans (expand F G).symm
private def weight (d i : ℕ) : ℕ := d - 6819 * i
private def power (w : ℕ) : ℕ := (48913 + w) / 48914
private theorem coefficient_bound {k : Type*} [CommRing k]
    (P : k[X][X]) (d e i j : ℕ) (hij : j ≤ i)
    (hP : ∀ i l : ℕ, 6819 * i + 48914 * l < d → (P.coeff i).coeff l = 0) :
    (Polynomial.X : k[X]) ^ power (weight (d + e) i - weight e j) ∣ P.coeff (i - j) := by
  have hweight : weight (d + e) i ≤ weight e j + weight d (i - j) := by
    unfold weight
    omega
  apply X_pow_dvd_iff.mpr
  intro l hl
  apply hP
  unfold power at hl
  have hsmall : 48914 * l < weight (d + e) i - weight e j := by omega
  unfold weight at hweight hsmall
  omega
private def columnWeight {m n : ℕ} (j : Fin (m + n)) : ℕ :=
  j.addCases (fun j : Fin m => weight firstOrder j) (fun j : Fin n => weight secondOrder j)
private theorem sylvester_entry {k : Type*} [CommRing k]
    (F G : k[X][X]) (m n : ℕ)
    (hF : ∀ i l : ℕ, 6819 * i + 48914 * l < firstOrder → (F.coeff i).coeff l = 0)
    (hG : ∀ i l : ℕ, 6819 * i + 48914 * l < secondOrder → (G.coeff i).coeff l = 0)
    (i j : Fin (m + n)) :
    (Polynomial.X : k[X]) ^ power (weight (firstOrder + secondOrder) i - columnWeight j) ∣
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
    (M : Matrix (Fin N) (Fin N) k[X]) (row col : Fin N → ℕ)
    (hM : ∀ i j, (Polynomial.X : k[X]) ^ power (row i - col j) ∣ M i j)
    (hbudget : (∑ j, col j) + 48914 * D ≤ (∑ i, row i) + 48913) :
    (Polynomial.X : k[X]) ^ D ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a : Fin N → ℕ := fun j => power (row (σ j) - col j)
  have hprod : (Polynomial.X : k[X]) ^ (∑ j, a j) ∣ ∏ j, M (σ j) j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hM (σ j) j)
  have hsum : (∑ i, row i) ≤ (∑ j, col j) + 48914 * (∑ j, a j) := by
    rw [← Equiv.sum_comp σ row, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [a, power]
    omega
  have hD : D ≤ ∑ j, a j := by omega
  exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hD).trans hprod) _
private theorem sum_weight {d t N : ℕ} (ht : t ≤ N) (hend : d ≤ 6819 * t)
    (hbefore : ∀ i < t, 6819 * i ≤ d) :
    (∑ i : Fin N, weight d i) = t * d - 6819 * (t * (t - 1) / 2) := by
  rw [Fin.sum_univ_eq_sum_range]
  have htrim : (∑ i ∈ Finset.range t, weight d i) = ∑ i ∈ Finset.range N, weight d i := by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold weight
    omega
  rw [← htrim]
  have hsum : (∑ i ∈ Finset.range t, weight d i) + 6819 * (∑ i ∈ Finset.range t, i) =
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
    (∑ j : Fin (70000 + 70000), columnWeight (m := 70000) (n := 70000) j) + 48914 * 69360 ≤
      (∑ i : Fin (70000 + 70000), weight (firstOrder + secondOrder) i) + 48913 := by
  have hF : (∑ i : Fin 70000, weight firstOrder i) = 0xaea36c7d := by
    rw [sum_weight (t := 927) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder]; omega)]
    decide
  have hG : (∑ i : Fin 70000, weight secondOrder i) = 0x3ab5c196 := by
    rw [sum_weight (t := 537) (by decide) (by decide)
      (by intro i hi; simp only [secondOrder]; omega)]
    decide
  have hFG : (∑ i : Fin (70000 + 70000), weight (firstOrder + secondOrder) i) =
      0x1b390b664 := by
    rw [sum_weight (t := 1464) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder, secondOrder]; omega)]
    decide
  rw [Fin.sum_univ_add, hFG]
  simp only [columnWeight, Fin.addCases_left, Fin.addCases_right, hF, hG]
  decide
private theorem resultant_bound
    (F G : GenericX[X][X]) (z : GenericX) {m n D : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (hFO : ∀ i l : ℕ, 6819 * i + 48914 * l < firstOrder →
      ((F.taylor (C z)).coeff i).coeff l = 0)
    (hGO : ∀ i l : ℕ, 6819 * i + 48914 * l < secondOrder →
      ((G.taylor (C z)).coeff i).coeff l = 0)
    (hbudget : (∑ j : Fin (m + n), columnWeight (m := m) (n := n) j) + 48914 * D ≤
      (∑ i : Fin (m + n), weight (firstOrder + secondOrder) i) + 48913) :
    (Polynomial.X : GenericX[X]) ^ D ∣ resultant F G m n := by
  rw [← resultant_taylor_formal F G (C z) hF hG]
  unfold resultant
  exact det_bound
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i => weight (firstOrder + secondOrder) i)
    (columnWeight (m := m) (n := n))
    (sylvester_entry _ _ m n hFO hGO) hbudget
theorem line_resultant_order (F G : GenericX[X][X]) (z : GenericX)
    (hF : F.natDegree ≤ 70000) (hG : G.natDegree ≤ 70000)
    (hFO : ∀ i j, 6819 * i + 48914 * j < firstOrder →
      ((F.taylor (Polynomial.C z)).coeff i).coeff j = 0)
    (hGO : ∀ i j, 6819 * i + 48914 * j < secondOrder →
      ((G.taylor (Polynomial.C z)).coeff i).coeff j = 0) :
    (Polynomial.X : GenericX[X]) ^ 69360 ∣ Polynomial.resultant F G 70000 70000 := by
  exact resultant_bound F G z (m := 70000) (n := 70000) (D := 69360)
    hF hG hFO hGO benchmark_budget
end P3_6_4
end
section
namespace P3_6_4
noncomputable section
open K1_13 Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped BigOperators
set_option maxRecDepth 4000
private def ray (v : Fin 3 → GenericX) : Lower →+* GenericX[X] :=
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
    ∀ i j, 6819 * i + 48914 * j < d →
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
  have hweight : mixedWeight (a.optionElim i) = 6819 * i + 48914 * j := by
    change 6819 * a.optionElim i none + 48914 * (a.optionElim i).some.degree = _
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
private theorem line_resultant (F G : GenericRow) (y v : Fin 3 → GenericX) :
    resultant ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y)))
      ((asSeedPoly G).map ((ray v).comp (K1_13_4.translate y))) 70000 70000 =
        ray v (K1_13_4.translate y (seedResultant F G)) := by
  unfold seedResultant
  rw [resultant_map_map, RingHom.comp_apply]
theorem mixedOrder_pad {F : GenericRow} {z : GenericX} {y : Fin 3 → GenericX}
    {d : ℕ} (a : Geom[X]) (h : MixedOrder F z y d) :
    MixedOrder (pad F a) z y d := by
  classical
  intro m hm
  rw [pad, map_mul] at hm
  obtain ⟨u, hu, v, _, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [mixedWeight_add]; exact Nat.le_add_right _ _)
theorem resultant_order (F G : GenericRow) (z : GenericX)
    (y : Fin 3 → GenericX) (hF : (asSeedPoly F).natDegree ≤ 70000)
    (hG : (asSeedPoly G).natDegree ≤ 70000) (h : PairOrders F G z y) :
    LowerOrder (seedResultant F G) y 69360 := by
  apply order_of_rays
  intro v
  rw [← line_resultant F G y v]
  exact line_resultant_order _ _ z (natDegree_map_le.trans hF) (natDegree_map_le.trans hG)
    (line_order F z y v _ h.1) (line_order G z y v _ h.2)
end
end P3_6_4
end
section
namespace P3_6_4
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2273 →
    (∃ F, F ≠ 0 ∧ Source w P L firstBox firstCut F) ∧
    HasRank w P L secondBox secondCut bankRank
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow),
    F ≠ 0 → Caps firstBox F → HasRank w P L secondBox secondCut bankRank →
    ∃ G, G ∈ Necessary w P L ∧ Nonempty (CommonPair (toGeneric F) (toGeneric G))
def c3 : Prop :=
  ∀ w Γ s, P3.Messages w Γ s →
    ∀ (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2273 →
      (∀ F, Source w P L firstBox firstCut F → ∀ γ ∈ Γ,
        MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstOrder) ∧
      (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
        MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondOrder)
private theorem inclX_injective : Function.Injective inclX :=
  IsFractionRing.injective Geom[X] GenericX
private theorem eval_cleared {Q : Row 3} {R : Lower} {d : Geom[X]}
    (hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R) (S : Geom[X])
    (hR : MvPolynomial.eval (trajectory S) R = 0) : atJet Q S = 0 := by
  have hcomm : inclX (atJet Q S) =
      MvPolynomial.eval (trajectory S) (MvPolynomial.map inclX Q) := by
    rw [atJet, MvPolynomial.eval_map]
    exact MvPolynomial.eval₂_comp inclX (jet S) Q
  apply inclX_injective
  rw [map_zero, hcomm, hQ, map_mul, hR, mul_zero]
private theorem map_shift (Q : Row 3) (S : Geom[X]) :
    MvPolynomial.map inclX (shiftJet Q S) =
      K1_13_4.translate (trajectory S) (MvPolynomial.map inclX Q) := by
  have hc : (MvPolynomial.map (σ := Fin 3) inclX).comp MvPolynomial.C =
      MvPolynomial.C.comp inclX := by
    apply RingHom.ext
    intro x
    simp
  unfold K1_13.shiftJet
  rw [MvPolynomial.eval₂_comp_left]
  change _ = MvPolynomial.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.X i + MvPolynomial.C (trajectory S i)) (MvPolynomial.map inclX Q)
  rw [MvPolynomial.eval₂_map, hc]
  congr 1
  funext i
  simp [trajectory]
private theorem order_cleared {Q : Row 3} {R : Lower} {d : Geom[X]}
    (hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R)
    (S : Geom[X]) {m : ℕ} (hR : LowerOrder R (trajectory S) m) : OrderAt Q S m := by
  have hs : MvPolynomial.map inclX (shiftJet Q S) =
      MvPolynomial.C (inclX d) * K1_13_4.translate (trajectory S) R := by
    rw [map_shift, hQ, map_mul, K1_13_4.translate, MvPolynomial.eval₂Hom_C]
  intro a ha
  apply hR
  have hcoeff := congrArg (fun P : Lower => P.coeff a) hs
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hcoeff
  rw [MvPolynomial.mem_support_iff] at ha ⊢
  intro hz
  rw [hz, mul_zero] at hcoeff
  exact ha (inclX_injective (hcoeff.trans (map_zero _).symm))
set_option maxRecDepth 2400 in
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : P3_6.c4 := by
  intro w Γ s hw Pnew
  let P := P3.asOldPole Pnew
  have hheight : P.H.natDegree ≤ 2273 := Pnew.small.2
  obtain ⟨L⟩ := K1_13_4_1.proof Γ s P
  obtain ⟨⟨F, neF, hF⟩, rank2⟩ := h1 w Γ s P L hheight
  obtain ⟨vanishes1, vanishes2⟩ := h3 w Γ s hw P L hheight
  obtain ⟨G, hG, ⟨D⟩⟩ := h2 w Γ s P L F neF hF.1 rank2
  have hOrders : ∀ γ ∈ Γ, PairOrders (toGeneric F) (toGeneric G)
      (inclConst (P.z γ)) (trajectory (extend (s γ))) := fun γ hγ =>
    ⟨vanishes1 F hF γ hγ, vanishes2 G hG γ hγ⟩
  obtain ⟨book, Q, hcard, hQ, htQ, hiQ, hcover⟩ :=
    eliminate_common Γ P.z (fun γ => extend (s γ)) P.injective D hOrders
  obtain ⟨J⟩ := K1_13_4_6.proof D.left D.right D.left_ne D.right_ne D.proper D.left_caps D.right_caps
  let R := seedResultant (pad D.left J.a) (pad D.right J.b)
  obtain ⟨_, Q', _, suppQ, mapQ⟩ := clear_denominators Q
  obtain ⟨_, R', _, suppR, mapR⟩ := clear_denominators R
  have neQ : Q' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppQ
    exact hQ suppQ
  have neR : R' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppR
    exact J.nonzero suppR
  have totalQ : Q'.totalDegree ≤ 6245 := by
    simpa only [MvPolynomial.totalDegree, suppQ] using htQ
  have indexQ : indexDegree Q' ≤ 2022 := by
    simpa only [K1_13.indexDegree, lowerIndex, suppQ] using hiQ
  have totalR : R'.totalDegree ≤ 0x38c7faf0 := by
    have htR : R.totalDegree ≤ 0x38c7faf0 := J.total
    simpa only [MvPolynomial.totalDegree, suppR] using htR
  have indexR : indexDegree R' ≤ 0x13315480 := by
    have hiR : lowerIndex R ≤ 0x13315480 := J.index
    simpa only [K1_13.indexDegree, lowerIndex, suppR] using hiR
  refine ⟨book, ⟨Q', R', neQ, neR, totalQ, indexQ, totalR, indexR⟩, hcard, ?_⟩
  intro γ hγ hb
  rcases hcover γ hγ hb with he | ho
  · exact Or.inl (eval_cleared mapQ _ he)
  · refine Or.inr (order_cleared mapR _ ?_)
    have hres : LowerOrder R (trajectory (extend (s γ))) 69360 :=
      resultant_order (pad D.left J.a) (pad D.right J.b) (inclConst (P.z γ)) _
        J.degree_left.le J.degree_right.le ⟨mixedOrder_pad J.a ho.1, mixedOrder_pad J.b ho.2⟩
    exact hres
end
end P3_6_4
end
section
namespace P3_6_4_1
open K1_13_4_2 (Bank)
def cut : Bank → ℕ
  | .first => P3_6_4.firstCut
  | .second => P3_6_4.secondCut
def targetRank : Bank → ℕ
  | .first => 1
  | .second => P3_6_4.bankRank
theorem cut_large (b : Bank) : 131071 * b.box.b ≤ cut b + 1 := by
  cases b <;> decide
def rawBase (b : Bank) : ℕ := cut b + 1 - 131071 * b.box.b
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h
end P3_6_4_1
end
section
namespace P3_6_4_1
open K1_13 (Geom)
open K1_13_4 K1_13_4_2
open K1_13_4_2_1 (jetSum)
open Function
open scoped BigOperators Polynomial
noncomputable section
open private Column colExp colX column column_li coordinate coordinate_column column_bounds
  space space_bounds from ProximityPrize.SubmissionLower.PortLow4
private abbrev NewColumn (b : Bank) (h : ℕ) :=
  Σ q : Fin (b.box.b + 1), Σ k : Fin (min q.val 1150 + 1),
    Σ l : Fin (min (q.val - k.val) (2300 - 2 * k.val) + 1),
      Fin (width b h q.val k.val l.val) × Fin 70001
private def offset (b : Bank) : ℕ := P0_9_4_1.cut b - cut b
private theorem cut_shift (b : Bank) : cut b + offset b = P0_9_4_1.cut b := by
  have h : cut b ≤ P0_9_4_1.cut b := by cases b <;> decide
  unfold offset
  omega
private theorem width_shift (b : Bank) (h q k l : ℕ) :
    width b h q k l + offset b = P0_9_4_1.width b h q k l := by
  have hc := cut_shift b
  have hl := cut_large b
  unfold width P0_9_4_1.width rawBase P0_9_4_1.rawBase
  omega
private def inOld (b : Bank) (h d : ℕ) (hd : d ≤ offset b) : NewColumn b h ↪ Column b h :=
  (Embedding.refl _).sigmaMap fun q =>
    (Embedding.refl _).sigmaMap fun k =>
      (Embedding.refl _).sigmaMap fun l =>
        ((Fin.addNatEmb d).trans (Fin.castLEEmb
          ((Nat.add_le_add_left hd _).trans_eq (width_shift b h q.val k.val l.val)))).prodMap
          (Embedding.refl _)
private abbrev base (b : Bank) (h : ℕ) := inOld b h 0 (Nat.zero_le _)
private def newSpace (b : Bank) (h : ℕ) : Submodule Geom PhysicalRow :=
  Submodule.span Geom (Set.range (column ∘ base b h))
private theorem occurs {b : Bank} {h : ℕ} {F : PhysicalRow}
    (hF : F ∈ newSpace b h) {e : SeedVar →₀ ℕ} {x : ℕ} (hne : (F.coeff e).coeff x ≠ 0) :
    ∃ c : NewColumn b h, colExp (base b h c) = e ∧ colX (base b h c) = x := by
  classical
  by_contra! hn
  have hle : newSpace b h ≤ LinearMap.ker (coordinate e x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change coordinate e x (column (base b h c)) = 0
    rw [coordinate_column, ite_eq_right]
    exact fun hc => (hn c hc.1 hc.2).elim
  exact hne (LinearMap.mem_ker.mp (hle hF))
private theorem fits (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ newSpace b h) :
    Caps b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F := by
  have hle : newSpace b h ≤ space b h := Submodule.span_mono (by
    rintro _ ⟨c, rfl⟩
    exact ⟨base b h c, rfl⟩)
  refine ⟨(space_bounds b h F (hle hF)).1, ?_⟩
  intro e he
  obtain ⟨c, hc, hx⟩ := occurs hF (by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp he)
  rcases c with ⟨q,k,l,x,u⟩
  let shifted := inOld b h (offset b) le_rfl ⟨q,k,l,x,u⟩
  have hw := (column_bounds shifted).2.2.2.2
  have he' : colExp shifted = e := hc
  have hx' : colX shifted = (F.coeff e).natDegree + offset b :=
    congrArg (· + offset b) hx
  rw [he', hx'] at hw
  have hs := cut_shift b
  omega
theorem ambient (b : Bank) (h : ℕ) :
    ∃ V : Submodule Geom PhysicalRow, Module.Finite Geom V ∧
      (∀ F ∈ V, Caps b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F) ∧
      Module.finrank Geom V = 70001 * jetSum b.box.b (width b h) := by
  refine ⟨newSpace b h, Module.Finite.span_of_finite _ (Set.finite_range _), fits b h, ?_⟩
  rw [newSpace, finrank_span_eq_card ((column_li b h).comp _ (base b h).injective)]
  simp only [NewColumn, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_comm _ 70001]
  unfold jetSum
  simp only [Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Fin.sum_univ_eq_sum_range]
end
end P3_6_4_1
end
section
namespace P3_6_4_1
open K1_13_4_2 (Bank poleDebit)
open K1_13_4_2_1 (jetSum)
open Finset
open scoped BigOperators
open private moment moment_eq slice antidifference credit extra pole_eq bank_moments
  from ProximityPrize.SubmissionLower.Fast074
private def rawVolume (b : Bank) : ℕ := moment b.box.b (rawBase b) 1 131071 0
private theorem volume_eq (b : Bank) (h : ℕ) :
    jetSum b.box.b (width b h) = rawVolume b + credit b.box.b * h := by
  simp only [width, rawVolume, moment, credit, jetSum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring
private theorem first_raw : rawVolume .first = 0x26f9d8897a518f7c := by
  change moment 6789 3756110 1 131071 0 = _
  refine moment_eq 6789 3756110 1 131071 0 _ (by decide) ?_
  change antidifference (slice 6789 3756110 1 131071 0) 1151 = _
  have h0 : slice 6789 3756110 1 131071 0 0 = 0x9d08bb217e22af0 := by decide
  have h1 : slice 6789 3756110 1 131071 0 1 = 0x9ce4d7f7fffeeb0 := by decide
  have h2 : slice 6789 3756110 1 131071 0 2 = 0x9cc0f57023cf8e0 := by decide
  have h3 : slice 6789 3756110 1 131071 0 3 = 0x9c9d1389c594ce0 := by decide
  have h4 : slice 6789 3756110 1 131071 0 4 = 0x9c793244c14ee10 := by decide
  unfold antidifference
  rw [h0, h1, h2, h3, h4]
  decide
private theorem second_raw : rawVolume .second = 0x2740fbe247538fab := by
  change moment 6820 2349043 1 131071 0 = _
  refine moment_eq 6820 2349043 1 131071 0 _ (by decide) ?_
  change antidifference (slice 6820 2349043 1 131071 0) 1151 = _
  have h0 : slice 6820 2349043 1 131071 0 0 = 0x9e256813f5bf350 := by decide
  have h1 : slice 6820 2349043 1 131071 0 1 = 0x9e0145928384020 := by decide
  have h2 : slice 6820 2349043 1 131071 0 2 = 0x9ddd23b2b338da0 := by decide
  have h3 : slice 6820 2349043 1 131071 0 3 = 0x9db9027460ddf30 := by decide
  have h4 : slice 6820 2349043 1 131071 0 4 = 0x9d94e1d76873830 := by decide
  unfold antidifference
  rw [h0, h1, h2, h3, h4]
  decide
private theorem endpoint (b : Bank) :
    targetRank b + 262144 * (70001 * b.nodeRank) + 2273 * extra b.box.b ≤
      70001 * rawVolume b := by
  obtain ⟨_, _, hfirst, hsecond⟩ := bank_moments
  cases b
  · have he : extra Bank.first.box.b = 0x1cc973f372d9cdc := hfirst
    have ha : (1 : ℕ) + 262144 * (70001 * 0x9bab8f5dfb7) + 2273 * 0x1cc973f372d9cdc ≤
        70001 * 0x26f9d8897a518f7c := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.first + 262144 * (70001 * Bank.first.nodeRank) + 2273 * x ≤ 70001 * y)
      he first_raw).mpr ha
  · have he : extra Bank.second.box.b = 0x1d32fca954a0ef7 := hsecond
    have ha : (0x4b8ba3f30d83cce664 : ℕ) + 262144 * (70001 * 0x9bac59312df) +
        2273 * 0x1d32fca954a0ef7 ≤ 70001 * 0x2740fbe247538fab := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.second + 262144 * (70001 * Bank.second.nodeRank) + 2273 * x ≤ 70001 * y)
      he second_raw).mpr ha
theorem budget (b : Bank) (h : ℕ) (hh : h ≤ 2273) :
    targetRank b + 262144 * (70001 * b.nodeRank) + h * poleDebit b.box ≤
      70001 * jetSum b.box.b (width b h) := by
  have he := endpoint b
  have hm := Nat.mul_le_mul_right (extra b.box.b) hh
  rw [pole_eq, volume_eq, Nat.mul_add, Nat.mul_add]
  have hc : h * (70001 * credit b.box.b) = 70001 * (credit b.box.b * h) := by ring
  omega
end P3_6_4_1
end
section
namespace P3_6_4_1
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2
open scoped Polynomial BigOperators
open private codim_inf_le codim_finset_inf_le separable_rank dimension_of_debits
  from ProximityPrize.SubmissionLower.Fast050
private theorem contact_bound : K1_13_4_2.c2 :=
  K1_13_4_2_2.of_children K1_13_4_2_2_1.proof K1_13_4_2_2_2.proof K1_13_4_2_2_3.proof
    K1_13_4_2_2_4.proof K1_13_4_2_2_5.proof K1_13_4_2_2_6.proof
private theorem simple_pole_bound : K1_13_4_2.c3 :=
  K1_13_4_2_3.of_children K1_13_4_2_3_1.proof K1_13_4_2_3_2.proof
private theorem deformation_bound : K1_13_4_2.c4 :=
  K1_13_4_2_4.of_children K1_13_4_2_4_1.proof K1_13_4_2_4_2.proof
private theorem rank_of_bounds (b : Bank) (w : I → K) {Γ s}
    (P : PoleData Γ s) (L : ResidueChart P) (hh : P.H.natDegree ≤ 2273) :
    HasRank w P L b.box (cut b) (targetRank b) := by
  classical
  obtain ⟨V, hV, hbox, hdimV⟩ := ambient b P.H.natDegree
  have hsize := (budget b P.H.natDegree hh).trans_eq hdimV.symm
  let : Module.Finite Geom V := hV
  have hcap : ∀ F ∈ V, Caps b.box F := fun F hF => (hbox F hF).1
  let A : I → Submodule Geom PhysicalRow := fun i => contactAt (embed (node i)) (embed (w i))
  let U : Submodule Geom PhysicalRow := ⨅ i, A i
  let W : Submodule Geom PhysicalRow := poleCondition P L b.box (liftX P.H)
  have hU : codimIn V U ≤ 262144 * (70001 * b.nodeRank) := by
    have hA (i : I) (_ : i ∈ Finset.univ) : codimIn V (A i) ≤ 70001 * b.nodeRank :=
      contact_bound b (embed (node i)) (embed (w i)) V hV hcap
    have h := codim_finset_inf_le V (Finset.univ : Finset I) A (70001 * b.nodeRank) hA
    have hc : (Finset.univ : Finset I).card = 262144 := Fintype.card_fin (2 ^ 18)
    rw [hc, Finset.inf_univ_eq_iInf] at h
    exact h
  have hW : codimIn V W ≤ P.H.natDegree * poleDebit b.box := by
    apply deformation_bound Γ s P L b.box V _ hV
    intro P' L' _ hdeg hsep
    rw [← hdeg]
    exact separable_rank simple_pole_bound P' L' b.box V hcap hsep
  have hdebit := (codim_inf_le V U W).trans (Nat.add_le_add hU hW)
  let S : Submodule Geom PhysicalRow := V ⊓ (U ⊓ W)
  have hdim : targetRank b ≤ Module.finrank Geom S := dimension_of_debits hsize hdebit
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Geom) (M := ↥S) hdim
  let e : Fin (targetRank b) → PhysicalRow := fun i => (f i).val
  refine ⟨e, hf.map_injOn S.subtype Subtype.val_injective.injOn, ?_⟩
  intro i
  have hm := Submodule.mem_inf.mp (f i).property
  have hUW : e i ∈ U ⊓ W := hm.2
  have hb := hbox (e i) hm.1
  refine ⟨hb.1, hb.2, ?_, (mem_poleCondition P L b.box _ _).mp (Submodule.mem_inf.mp hUW).2⟩
  intro j
  have hmem : e i ∈ A j := (Submodule.mem_iInf A).mp (Submodule.mem_inf.mp hUW).1 j
  exact (mem_contactAt (embed (node j)) (embed (w j)) (e i)).mp hmem
theorem proof : P3_6_4.c1 := by
  intro w Γ s P L hh
  refine ⟨?_, rank_of_bounds .second w P L hh⟩
  obtain ⟨e, he, hsource⟩ := rank_of_bounds .first w P L hh
  let i : Fin (targetRank Bank.first) := ⟨0, by decide⟩
  exact ⟨e i, he.ne_zero i, hsource i⟩
end
end P3_6_4_1
end
section
namespace P3_6_4_2
noncomputable section
open Polynomial K1 K1_13
open K1_13_4 (ResidueChart PhysicalRow GenericX GenericRow HasRank Source secondBox toGeneric)
open K1_13_4_4 (layerSpan)
open K1_13_4_4_1 (Exponent)
open P3_6_4 (secondCut bankRank)
open scoped BigOperators
open private bank bankEval mem_bank K1_13_4_4_1.kernel_le boundary below_boundary independent_generic
  from ProximityPrize.SubmissionLower.Fast050
open private K1_13_4_4_1.endpoint from ProximityPrize.SubmissionLower.Fast074
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem telescope (w : I → K) (Γ : Finset K) (s : K → K[X]) (P : PoleData Γ s)
    (L : ResidueChart P) (hr : HasRank w P L secondBox secondCut bankRank) :
    ∃ r : ℕ → ℕ, bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t ∧
      ∀ t ≤ secondCut, ∃ e : Fin (r t) → GenericRow,
        LinearIndependent GenericX e ∧ ∀ i, e i ∈ layerSpan w P L t := by
  classical
  let r (t : ℕ) := Module.finrank Geom (bankEval w P L t).range
  refine ⟨r, ?_, fun t _ => ?_⟩
  · have hzero : (bankEval w P L 0).ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro F hz
      have hsrc := (mem_bank w P L _ _).mp F.property
      refine Subtype.ext (K1_13_4_4_1.endpoint Γ s P L F.val (fun m hm => ?_) hsrc.2.2.2)
      simpa only [Nat.zero_add] using below_boundary hsrc.2.1 hz m hm
    have hsum (t : ℕ) : Module.finrank Geom (bank w P L t) ≤
        ∑ v ∈ Finset.range (t + 1), r v := by
      induction t with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w P L 0) (V₂ := Exponent → Geom) (bankEval w P L 0)
        rw [hzero, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.ge
      | succ t ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w P L (t + 1)) (V₂ := Exponent → Geom) (bankEval w P L (t + 1))
        rw [Finset.sum_range_succ, ← h, add_comm]
        exact Nat.add_le_add (le_trans (K1_13_4_4_1.kernel_le w P L t) ih) le_rfl
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom
        (fun i => (⟨e i, (mem_bank w P L _ _).mpr (hmem i)⟩ : bank w P L secondCut)) :=
      LinearIndependent.of_comp (bank w P L secondCut).subtype he
    exact (by simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank :
      bankRank ≤ Module.finrank Geom (bank w P L secondCut)).trans (hsum secondCut)
  · let b := Module.finBasis Geom (bankEval w P L t).range
    choose e he using fun i : Fin (r t) => LinearMap.mem_range.mp (b i).property
    have hsrc (i : Fin (r t)) : Source w P L secondBox t (e i).val :=
      (mem_bank w P L _ _).mp (e i).property
    refine ⟨fun i => toGeneric (e i).val,
      independent_generic (fun i => (e i).val) (fun i => (hsrc i).2.1) ?_,
      fun i => Submodule.subset_span ⟨(e i).val, hsrc i, rfl⟩⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (bankEval w P L t).range.subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => boundary P.H.natDegree t (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end P3_6_4_2
end
section
namespace P3_6_4_2
noncomputable section
open K1_13_4 hiding mixedWeight secondCut
open K1_13_4_4 (FactorsFor factorProduct mixedHasse_zero toGeneric_caps topSlots cutoff_sum_le slot_constants)
open P3_6_4 (mixedWeight secondCut bankRank)
open scoped Polynomial BigOperators
open private line line_zero line_toGeneric transverse pow_dvd_of_coeff positive_jet_degree
  from ProximityPrize.SubmissionLower.Fast076
def reserveCost (moving : Bool) : ℕ := if moving then 6819 else 48914
def layerPower (e t : ℕ) : ℕ := 1 + (secondCut - t) / e
private theorem choose_coordinate {moving : Bool} {A : Finset GenericRow}
    (hA : FactorsFor moving A) {F f : GenericRow} (hF : F ≠ 0) (hcap : Caps secondBox F)
    (hf : f ∈ A) (hd : f ∣ F) :
    ∃ i : SeedVar, (∀ n, mixedWeight (Finsupp.single i n) = n * reserveCost moving) ∧
      ¬ f ∣ (line i f).coeff 1 := by
  classical
  cases moving with
  | false =>
    obtain ⟨j, hj⟩ := positive_jet_degree (hA.jets f hf)
    have hjet : jetTotal f ≤ 6820 :=
      (MvPolynomial.weightedTotalDegree_le_of_dvd _ hd hF).trans hcap.1
    have hdeg : f.degreeOf (some j) ≤ jetTotal f :=
      MvPolynomial.degreeOf_le_weightedTotalDegree
        (fun i : SeedVar => i.elim 0 (fun _ => 1)) (some j) Nat.one_pos f
    refine ⟨some j, ?_, transverse hj (hdeg.trans_lt (hjet.trans_lt (by decide)))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]
  | true =>
    have hs : 0 < seedDegree f := hA.seed f hf
    have hdeg : seedDegree f ≤ 70000 := by
      simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
        (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hd hF).trans
          (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hcap.2.2.2)
    refine ⟨none, ?_, transverse hs (hdeg.trans_lt (by decide))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]
theorem factor_power (moving : Bool) (A : Finset GenericRow) (F : PhysicalRow) (t : ℕ)
    (hA : FactorsFor moving A) (hcap : Caps secondBox F) (ht : t ≤ secondCut)
    (htest : ∀ f ∈ A, ∀ a, t + mixedWeight a ≤ secondCut → f ∣ toGeneric (mixedHasse a F)) :
    factorProduct A ^ layerPower (reserveCost moving) t ∣ toGeneric F := by
  classical
  by_cases hF : toGeneric F = 0
  · rw [hF]
    exact dvd_zero _
  unfold factorProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro f hf g hg hfg
    refine IsRelPrime.pow ((hA.irreducible f hf).isRelPrime_iff_not_dvd.mpr ?_)
    intro hd
    exact hA.different hf hg hfg ((hA.irreducible f hf).associated_of_dvd (hA.irreducible g hg) hd)
  · intro f hf
    have hdiv : f ∣ toGeneric F := by
      simpa [mixedWeight, mixedHasse_zero] using htest f hf 0 (by simpa [mixedWeight] using ht)
    obtain ⟨i, hi, hsep⟩ := choose_coordinate hA hF (toGeneric_caps hcap) hf hdiv
    apply pow_dvd_of_coeff (line i) (line_zero i)
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hA.irreducible f hf)) hsep
    intro a ha
    rw [line_toGeneric]
    apply htest f hf
    rw [hi]
    have ha' : a ≤ (secondCut - t) / reserveCost moving := by
      unfold layerPower at ha
      omega
    have hm := (Nat.mul_le_mul_right (reserveCost moving) ha').trans
      (Nat.div_mul_le_self (secondCut - t) (reserveCost moving))
    omega
set_option maxRecDepth 1024
theorem factor_arithmetic :
    let T := 0x1de50d7332f37
    48914 * 6820 * T / bankRank = 125 ∧ 48914 * 2300 * T / bankRank = 42 ∧
      6819 * 6820 * T / bankRank = 17 ∧ 6819 * 2300 * T / bankRank = 5 ∧
      6819 * 70000 * T / bankRank = 180 := by decide
theorem resource_bound {e V d : ℕ} (he : 0 < e) (r : ℕ → ℕ)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hcap : ∀ t ≤ secondCut, r t ≤ topSlots 0)
    (hspend : ∀ t ≤ secondCut, r t ≠ 0 → layerPower e t * d ≤ V) :
    d ≤ e * V * topSlots 0 / bankRank := by
  by_cases hd : d = 0
  · simp [hd]
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  let q (k : ℕ) := if k < V / d then topSlots 0 else 0
  have hb := cutoff_sum_le (W := secondCut) (n := V / d) he r q
    (fun t ht => by
      by_cases hn : r t = 0
      · simp [hn]
      have hle := (Nat.le_div_iff_mul_le hd').mpr (hspend t ht hn)
      have hlt : (secondCut - t) / e < V / d := by
        unfold layerPower at hle
        omega
      simpa [q, hlt] using hcap t ht)
    (fun k hk => ite_eq_right (Nat.not_lt.mpr hk))
  have hc : (∑ k ∈ Finset.range (V / d), q k) = (V / d) * topSlots 0 := by
    have hsum : (∑ k ∈ Finset.range (V / d), q k) =
        ∑ _ ∈ Finset.range (V / d), topSlots 0 :=
      Finset.sum_congr rfl fun k hk => ite_eq_left (Finset.mem_range.mp hk)
    rw [hsum]
    simp
  rw [hc] at hb
  apply (Nat.le_div_iff_mul_le (by decide : 0 < bankRank)).mpr
  calc
    d * bankRank ≤ d * (e * (V / d * topSlots 0)) :=
      Nat.mul_le_mul_left d (hr.trans hb)
    _ = (e * topSlots 0) * (V / d * d) := by ring
    _ ≤ (e * topSlots 0) * V := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = e * V * topSlots 0 := by ring
theorem top_exclusion (r : ℕ → ℕ)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (h : ∀ t ≤ secondCut, r t ≤ topSlots (layerPower 6819 t)) : False := by
  have hb := cutoff_sum_le (W := secondCut) (n := 1150) (by decide : 0 < 6819)
    r (fun k => topSlots (1 + k)) h (fun k hk => by
      have hk' : 1151 - (1 + k) = 0 := by omega
      simp [topSlots, hk'])
  have hs := congrArg (fun n : ℕ => n / 7800) slot_constants.2
  change 7800 * (∑ k ∈ Finset.range 1150, topSlots (1 + k)) / 7800 =
    0x5535180af365254238 / 7800 at hs
  rw [Nat.mul_div_cancel_left _ (by decide : 0 < 7800)] at hs
  rw [hs] at hb
  exact (not_le_of_gt (by decide : 6819 * (0x5535180af365254238 / 7800) < bankRank)) (hr.trans hb)
end
end P3_6_4_2
end
section
namespace P3_6_4_2
noncomputable section
open K1_13_4 hiding CommonPair
open K1_13_4_4 (FactorsFor factorProduct)
open P3_6_4 (CommonPair)
open scoped Polynomial BigOperators
open private pureEval pureEval_section pure_degree_le caps_of_dvd from ProximityPrize.SubmissionLower.Fast050
theorem factor_pair
    (F G : GenericRow) (hF : F ≠ 0) (hG : G ≠ 0)
    (hFCap : Caps firstBox F) (hGCap : Caps secondBox G)
    (hfixed : ∀ A, FactorsFor false A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 125 ∧ jetIndex (factorProduct A) ≤ 42)
    (hmoving : ∀ A, FactorsFor true A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 17 ∧ jetIndex (factorProduct A) ≤ 5 ∧
      seedDegree (factorProduct A) ≤ 180 ∧ ∀ f ∈ A, f.degreeOf (some 2) = 0) :
    Nonempty (CommonPair F G) := by
  classical
  let _ : StrongNormalizationMonoid GenericRow :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : GCDMonoid GenericRow := UniqueFactorizationMonoid.toGCDMonoid GenericRow
  let g := gcd F G
  have hg : g ≠ 0 := gcd_ne_zero_of_left hF
  let N := UniqueFactorizationMonoid.normalizedFactors g
  let A := N.toFinset
  let pureFactors := A.filter (fun f => jetTotal f = 0)
  let jetFactors := A.filter (fun f => ¬ jetTotal f = 0)
  let fixed := jetFactors.filter (fun f => seedDegree f = 0)
  let moving := jetFactors.filter (fun f => ¬ seedDegree f = 0)
  let powCount : GenericRow → ℕ := N.count
  let pure : GenericX[X] := ∏ f ∈ pureFactors, (pureEval f) ^ powCount f
  have hpure : pureSeed pure = ∏ f ∈ pureFactors, f ^ powCount f := by
    let φ : GenericX[X] →+* GenericRow :=
      Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none)
    change φ (∏ f ∈ pureFactors, (pureEval f) ^ powCount f) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun f hf => ?_
    rw [map_pow]
    exact congrArg (fun R => R ^ powCount f)
      (pureEval_section (Finset.mem_filter.mp hf).2)
  let D := pureSeed pure * (∏ f ∈ fixed, f ^ powCount f) * (∏ f ∈ moving, f ^ powCount f)
  have hD : Associated D g := by
    suffices D = N.prod by
      rw [this]
      exact UniqueFactorizationMonoid.prod_normalizedFactors hg
    change pureSeed pure * (∏ f ∈ fixed, f ^ powCount f) *
      (∏ f ∈ moving, f ^ powCount f) = _
    rw [hpure, mul_assoc]
    unfold fixed moving
    rw [Finset.prod_filter_mul_prod_filter_not]
    unfold pureFactors jetFactors
    rw [Finset.prod_filter_mul_prod_filter_not]
    exact (Finset.prod_multiset_count N).symm
  have hDne : D ≠ 0 := ne_zero_of_dvd_ne_zero hg hD.dvd
  have hDF : D ∣ F := hD.dvd.trans (gcd_dvd_left F G)
  have hDG : D ∣ G := hD.dvd.trans (gcd_dvd_right F G)
  obtain ⟨F', hF'⟩ := hDF
  obtain ⟨G', hG'⟩ := hDG
  have hl : F' ≠ 0 := right_ne_zero_of_mul (hF' ▸ hF)
  have hr : G' ≠ 0 := right_ne_zero_of_mul (hG' ▸ hG)
  have hrel : IsRelPrime F' G' := by
    intro d hdF hdG
    have hdF' : D * d ∣ F := hF' ▸ mul_dvd_mul_left D hdF
    have hdG' : D * d ∣ G := hG' ▸ mul_dvd_mul_left D hdG
    have hd := (dvd_gcd hdF' hdG').trans hD.symm.dvd
    apply isUnit_of_dvd_one
    exact (mul_dvd_mul_iff_left hDne).mp (by simpa only [mul_one] using hd)
  have hcommon (f : GenericRow) (hf : f ∈ A) : f ∣ F ∧ f ∣ G := by
    have hfg : f ∣ g := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hf)
    exact ⟨hfg.trans (gcd_dvd_left F G), hfg.trans (gcd_dvd_right F G)⟩
  have hmake (b : Bool) (B : Finset GenericRow) (hBA : B ⊆ A)
      (hj : ∀ f ∈ B, 0 < jetTotal f)
      (hs : ∀ f ∈ B, if b then 0 < seedDegree f else seedDegree f = 0) :
      FactorsFor b B := by
    refine ⟨?_, ?_, hj, hs⟩
    · intro f hf q hq hne hassoc
      exact hne (UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
        (Multiset.mem_toFinset.mp (hBA hf)) (Multiset.mem_toFinset.mp (hBA hq)) hassoc)
    · intro f hf
      exact UniqueFactorizationMonoid.irreducible_of_normalized_factor _
        (Multiset.mem_toFinset.mp (hBA hf))
  have hfixedA : fixed ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmovingA : moving ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hfix := hmake false fixed hfixedA
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf => (Finset.mem_filter.mp hf).2)
  have hmov := hmake true moving hmovingA
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp hf).2)
  obtain ⟨hft, hfi⟩ := hfixed fixed hfix (fun f hf => hcommon f (hfixedA hf))
  obtain ⟨hmt, hmi, hms, hlow⟩ := hmoving moving hmov (fun f hf => hcommon f (hmovingA hf))
  have hpureF : pureSeed pure ∣ F :=
    (show pureSeed pure ∣ D by
      exact ⟨_, mul_assoc _ _ _⟩).trans ⟨F', hF'⟩
  have hpure_ne : pure ≠ 0 := by
    intro hz
    apply hDne
    simp [D, hz, pureSeed]
  refine ⟨{
    fixed := fixed
    moving := moving
    pure := pure
    exponent := powCount
    left := F'
    right := G'
    pure_ne := hpure_ne
    pure_degree := (pure_degree_le hF hpureF).trans (hFCap.2.2.2.trans (by decide))
    fixed_kind := fun f hf => ⟨hfix.irreducible f hf, hfix.jets f hf, hfix.seed f hf⟩
    moving_kind := fun f hf => ⟨hmov.irreducible f hf, hmov.jets f hf, hmov.seed f hf, hlow f hf⟩
    fixed_total := hft
    fixed_index := hfi
    moving_total := hmt
    moving_index := hmi
    moving_seed := hms
    left_eq := hF'
    right_eq := hG'
    left_ne := hl
    right_ne := hr
    proper := hrel
    left_caps := caps_of_dvd hF hFCap ⟨D, hF'.trans (mul_comm _ _)⟩
    right_caps := caps_of_dvd hG hGCap ⟨D, hG'.trans (mul_comm _ _)⟩
  }⟩
end
end P3_6_4_2
end
section
namespace P3_6_4_2
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (layerSpan FactorsFor factorProduct topSlots slot_constants rowMap
  capSpace mem_capSpace mixedHasse_zero toGeneric_ne_zero toGeneric_caps mixedHasse_caps layerSpan_caps)
open P3_6_4 (Necessary mixedWeight secondCut bankRank)
open scoped BigOperators
open private multiples mem_multiples count_layer weighted_pow from ProximityPrize.SubmissionLower.Fast050
set_option maxRecDepth 1024
private theorem has_nonzero_necessary {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} (hr : HasRank w P L secondBox secondCut bankRank) :
    ∃ G : Necessary w P L, G ≠ 0 := by
  obtain ⟨e, he, hs⟩ := hr
  let i : Fin bankRank := ⟨0, by decide⟩
  have hmem : e i ∈ Necessary w P L := by
    apply Submodule.subset_span
    exact ⟨secondCut, e i, 0, hs i, by simp [mixedWeight], (mixedHasse_zero _).symm⟩
  refine ⟨⟨e i, hmem⟩, fun h => he.ne_zero i ?_⟩
  exact congrArg (fun Q : Necessary w P L => Q.val) h
private theorem necessary_caps {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {Q : PhysicalRow} (hQ : Q ∈ Necessary w P L) :
    Caps secondBox (toGeneric Q) := by
  have hle : Necessary w P L ≤ ((capSpace secondBox).restrictScalars Geom).comap rowMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, F, a, hF, _, rfl⟩
    exact mem_capSpace.mpr (toGeneric_caps (mixedHasse_caps a F hF.1))
  exact mem_capSpace.mp (hle hQ)
private theorem select_row {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {F : PhysicalRow} (hF : F ≠ 0) (hr : HasRank w P L secondBox secondCut bankRank) :
    ∃ G, G ∈ Necessary w P L ∧ G ≠ 0 ∧
      ∀ f : GenericRow, Irreducible f → f ∣ toGeneric F → f ∣ toGeneric G →
        ∀ Q ∈ Necessary w P L, f ∣ toGeneric Q := by
  classical
  let N := Necessary w P L
  let _ : StrongNormalizationMonoid GenericRow :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let bad := (UniqueFactorizationMonoid.normalizedFactors (toGeneric F)).toFinset.filter
    (fun f => ∃ Q ∈ N, ¬ f ∣ toGeneric Q)
  let sub : Option ↥bad → Submodule Geom N
    | none => ⊥
    | some f => ((multiples f.val).restrictScalars Geom).comap (rowMap.comp N.subtype)
  have hproper (i : Option ↥bad) : sub i ≠ ⊤ := by
    cases i with
    | none =>
      obtain ⟨Q, hQ⟩ := has_nonzero_necessary hr
      intro h
      have hm : Q ∈ sub none := h ▸ Submodule.mem_top
      exact hQ ((Submodule.mem_bot Geom).mp hm)
    | some f =>
      obtain ⟨Q, hQ, hnd⟩ := (Finset.mem_filter.mp f.property).2
      intro h
      have hm : (⟨Q, hQ⟩ : N) ∈ sub (some f) := h ▸ Submodule.mem_top
      exact hnd (mem_multiples.mp hm)
  obtain ⟨G, hG⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := Option ↥bad) (K := Geom) (M := N) sub hproper
  refine ⟨G.val, G.property, ?_, fun f hf hdf hdg Q hQ => ?_⟩
  · intro h
    exact hG none ((Submodule.mem_bot Geom).mpr (Subtype.ext h))
  · by_contra hn
    obtain ⟨p, hp, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd (toGeneric_ne_zero hF) hf hdf
    have hp' : p ∈ bad := Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hp, Q, hQ, fun h => hn (hassoc.dvd_iff_dvd_left.mpr h)⟩
    exact hG (some ⟨p, hp'⟩) (mem_multiples.mpr (hassoc.dvd_iff_dvd_left.mp hdg))
private theorem layer_divides {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {moving : Bool} {A : Finset GenericRow} (hA : FactorsFor moving A)
    (hcommon : ∀ f ∈ A, ∀ Q ∈ Necessary w P L, f ∣ toGeneric Q)
    {t : ℕ} (ht : t ≤ secondCut) :
    layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower (reserveCost moving) t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨F, hF, rfl⟩
  apply mem_multiples.mpr (factor_power moving A F t hA hF.1 ht ?_)
  intro f hf a ha
  exact hcommon f hf _ (Submodule.subset_span ⟨t, F, a, hF, ha, rfl⟩)
private theorem product_ne_zero {moving : Bool} {A : Finset GenericRow} (hA : FactorsFor moving A) :
    factorProduct A ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun f hf => (hA.irreducible f hf).ne_zero
private theorem weighted_resource {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {e : ℕ} (he : 0 < e) {r : ℕ → ℕ} {D : GenericRow} (hD : D ≠ 0)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow, LinearIndependent GenericX u ∧
      ∀ i, u i ∈ layerSpan w P L t)
    (hcount : ∀ t ≤ secondCut, r t ≤ topSlots 0)
    (hdvd : ∀ t ≤ secondCut, layerSpan w P L t ≤ multiples (D ^ layerPower e t))
    (v : SeedVar → ℕ) (V : ℕ)
    (hcap : ∀ R : GenericRow, Caps secondBox R → R.weightedTotalDegree v ≤ V) :
    D.weightedTotalDegree v ≤ e * V * topSlots 0 / bankRank := by
  apply resource_bound he r hr hcount
  intro t ht hne
  obtain ⟨u, hu, hs⟩ := hb t ht
  let i : Fin (r t) := ⟨0, Nat.pos_of_ne_zero hne⟩
  have hm := MvPolynomial.weightedTotalDegree_le_of_dvd v
    (mem_multiples.mp (hdvd t ht (hs i))) (hu.ne_zero i)
  rw [weighted_pow _ _ hD] at hm
  exact hm.trans (hcap (u i) (layerSpan_caps (hs i)))
private theorem excludes_top {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {r : ℕ → ℕ} {A : Finset GenericRow} (hA : FactorsFor true A)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow,
      LinearIndependent GenericX u ∧ ∀ i, u i ∈ layerSpan w P L t)
    (hdvd : ∀ t ≤ secondCut,
      layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower 6819 t)) :
    ∀ f ∈ A, f.degreeOf (some 2) = 0 := by
  classical
  let v : SeedVar → ℕ := Pi.single (some 2) 1
  have hzero : (factorProduct A).weightedTotalDegree v = 0 := by
    by_contra hn
    apply top_exclusion r hr
    intro t ht
    apply count_layer (hb t ht)
    intro R hR hRne
    have h := MvPolynomial.weightedTotalDegree_le_of_dvd v
      (mem_multiples.mp (hdvd t ht hR)) hRne
    rw [weighted_pow _ _ (product_ne_zero hA)] at h
    have hle := Nat.mul_le_mul_left (layerPower 6819 t) (Nat.pos_of_ne_zero hn)
    rw [Nat.mul_one] at hle
    simpa only [v, MvPolynomial.weightedTotalDegree_piSingle] using hle.trans h
  intro f hf
  have hfd : f ∣ factorProduct A := Finset.dvd_prod_of_mem id hf
  have h := (MvPolynomial.weightedTotalDegree_le_of_dvd v hfd (product_ne_zero hA)).trans_eq hzero
  simpa only [v, MvPolynomial.weightedTotalDegree_piSingle, Nat.le_zero] using h
theorem proof : P3_6_4.c2 := by
  classical
  intro w Γ s P L F hF hFCaps hRank
  obtain ⟨r, hr, hb⟩ := telescope w Γ s P L hRank
  have hcount : ∀ t ≤ secondCut, r t ≤ topSlots 0 := fun t ht =>
    count_layer (hb t ht) (fun _ _ _ => Nat.zero_le _)
  obtain ⟨G, hG, hGne, hchoose⟩ := select_row hF hRank
  have hdiv (moving : Bool) (A : Finset GenericRow) (hA : FactorsFor moving A)
      (hcomm : ∀ f ∈ A, f ∣ toGeneric F ∧ f ∣ toGeneric G) :
      ∀ t ≤ secondCut, layerSpan w P L t ≤
        multiples (factorProduct A ^ layerPower (reserveCost moving) t) :=
    fun _ ht => layer_divides hA
      (fun f hf => hchoose f (hA.irreducible f hf) (hcomm f hf).1 (hcomm f hf).2) ht
  have hbound (moving : Bool) (A : Finset GenericRow) (hA : FactorsFor moving A)
      (hcomm : ∀ f ∈ A, f ∣ toGeneric F ∧ f ∣ toGeneric G)
      (v : SeedVar → ℕ) (V : ℕ)
      (hc : ∀ R : GenericRow, Caps secondBox R → R.weightedTotalDegree v ≤ V) :
      (factorProduct A).weightedTotalDegree v ≤ reserveCost moving * V * topSlots 0 / bankRank :=
    weighted_resource (by cases moving <;> decide) (product_ne_zero hA) hr hb hcount
      (hdiv moving A hA hcomm) v V hc
  have hbcap (R : GenericRow) (h : Caps secondBox R) : jetTotal R ≤ 6820 := h.1
  have hjcap (R : GenericRow) (h : Caps secondBox R) : jetIndex R ≤ 2300 := h.2.1
  have hscap (R : GenericRow) (h : Caps secondBox R) :
      R.weightedTotalDegree (Pi.single (none : SeedVar) 1) ≤ 70000 := by
    rw [MvPolynomial.weightedTotalDegree_piSingle]
    exact h.2.2.2
  obtain ⟨bF, jF, bM, jM, sM⟩ := factor_arithmetic
  refine ⟨G, hG, factor_pair _ _ (toGeneric_ne_zero hF) (toGeneric_ne_zero hGne)
    (toGeneric_caps hFCaps) (necessary_caps hG) ?_ ?_⟩
  · intro A hA hcomm
    have hbt := hbound false A hA hcomm _ _ hbcap
    have hji := hbound false A hA hcomm _ _ hjcap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    have hbt' : jetTotal (factorProduct A) ≤ 125 := by
      simpa only [reserveCost, Bool.false_eq_true, ite_false, slot_constants.1, bF] using hbt
    have hji' : jetIndex (factorProduct A) ≤ 42 := by
      simpa only [reserveCost, Bool.false_eq_true, ite_false, slot_constants.1, jF] using hji
    exact ⟨hbt', hji'⟩
  · intro A hA hcomm
    have hbt := hbound true A hA hcomm _ _ hbcap
    have hji := hbound true A hA hcomm _ _ hjcap
    have hse := hbound true A hA hcomm _ _ hscap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    rw [MvPolynomial.weightedTotalDegree_piSingle] at hse
    have hbt' : jetTotal (factorProduct A) ≤ 17 := by
      simpa only [reserveCost, ite_true, slot_constants.1, bM] using hbt
    have hji' : jetIndex (factorProduct A) ≤ 5 := by
      simpa only [reserveCost, ite_true, slot_constants.1, jM] using hji
    have hse' : seedDegree (factorProduct A) ≤ 180 := by
      simpa only [seedDegree, reserveCost, ite_true, slot_constants.1, sM] using hse
    exact ⟨hbt', hji', hse', excludes_top hA hr hb (hdiv true A hA hcomm)⟩
end
end P3_6_4_2
end
section
namespace P3_6_4_3
noncomputable section
open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
open private line eval_line coeff_contact order_of_locator_lines translate_map from ProximityPrize.SubmissionLower.PortLow4
set_option maxRecDepth 12000
private def Bounded (F : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (F.coeff j).natDegree ≤ b + 48914 * j
private theorem bounded_mul {F G : Polynomial Geom[X]} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C (f : Geom[X]) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial Geom[X]) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {f : Polynomial Geom[X]} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree (Q : Row 3) (T U : Geom[X]) (t : ℕ)
    (hQ : RawCut t Q) (hT : T.natDegree ≤ 131071) (hU : U.natDegree ≤ 179985)
    (j : ℕ) : ((line Q T U).coeff j).natDegree ≤ t + 48914 * j := by
  let b (i : Fin 3) : ℕ := 131071 - i.val
  let F (i : Fin 3) : Polynomial Geom[X] :=
    Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 3) : Bounded (F i) (b i) := by
    intro k
    have ht : (jet T i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT _)
    have hu : (jet U i).natDegree ≤ b i + 48914 := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 179985 - i.val ≤ (131071 - i.val) + 48914
      omega
    change ((F i).coeff k).natDegree ≤ b i + 48914 * k
    rw [show F i = _ from rfl, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using ht
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hterm := bounded_mul (bounded_C (Q.coeff a) le_rfl)
    (bounded_prod a.support (fun i => F i ^ a i) (fun i => b i * a i)
      (fun i _ => bounded_pow (hF i) (a i))) j
  exact hterm.trans (Nat.add_le_add_right (hQ a ha) _)
private theorem line_coeff_zero (w : I → K) (H res T : Geom[X]) (t r : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071) (hQ : RawCut t Q) (hcontact : RawContact r w H res Q)
    (A : Finset I) (hA : A.card = 179983)
    (hhit : ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 2) (j : ℕ) (hj : t + 48914 * j < r * 179983) :
    (line Q T (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 179985 :=
    natDegree_mul_le.trans (by rw [locator_natDegree, hA]; omega)
  have hc (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ r ∣ (line Q T U).eval (C c) := by
    rw [eval_line]
    apply hcontact i
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    have ht : (T + c • U).eval (x i) = T.eval (x i) := by simp [eval_smul, hU0]
    change (H * (T + c • U) + res).eval (x i) = _
    rw [eval_add, eval_mul, ht, ← eval_mul, ← eval_add]
    exact hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  apply K1_11.eq_zero_of_many_contacts A x hx r
  · exact fun i hi => coeff_contact _ _ _ (hc i hi) j
  · rw [hA]
    exact (line_degree Q T U t hQ hT hU j).trans_lt hj
theorem raw_locator_order (w : I → K) (H res T : Geom[X]) (t k : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071)
    (hhits : ∃ A : Finset I, 179983 ≤ A.card ∧
      ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (hc : RawContact 5000 w H res Q) (hQ : RawCut t Q)
    (hcut : t + 48914 * k < 5000 * 179983) :
    LowerOrder (MvPolynomial.map inclX Q) (trajectory T) (k + 1) := by
  obtain ⟨B, hB, hhits⟩ := hhits
  obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq hB
  let x (i : I) := embed (node i)
  have ho : OrderAt Q T (k + 1) := by
    apply order_of_locator_lines Q T (locator x A) (locator_monic x A).ne_zero
    intro V hV j hj
    exact line_coeff_zero w H res T t 5000 Q hT hQ hc A hA
      (fun i hi => hhits i (hAB hi)) V hV j (by omega)
  intro a
  rw [translate_map]
  intro ha
  exact ho a (MvPolynomial.support_map_subset _ _ ha)
end
end P3_6_4_3
end
section
namespace P3_6_4_3
noncomputable section
open K1 K1_13 K1_13_4_3 P3_6_4
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open private coeff_scalar support_seed weight_shift from ProximityPrize.SubmissionLower.Fast050
open private coeff_eq_zero_of_lowerOrder from ProximityPrize.SubmissionLower.Fast050
private theorem trueCut_seed (H : Geom[X]) (i t : ℕ) (F : PhysicalRow)
    (hH : H.natDegree ≤ 2273) (hF : TrueCut H.natDegree t F) :
    TrueCut H.natDegree (t + 6819 * i) (clearedSeed H i F) := by
  intro b hb
  obtain ⟨u, hu⟩ := coeff_scalar F i b
  have hbefore := hF _ (support_seed hb)
  let w : SeedVar → ℕ := fun j => j.elim 0 (fun k => 131071 + H.natDegree - k.val)
  have hw (a : SeedVar →₀ ℕ) :
      a.sum (fun j e => j.elim 0 (fun k => (131071 + H.natDegree - k.val) * e)) =
        Finsupp.weight w a := by
    rw [Finsupp.weight_apply]
    congr 1
    funext j e
    cases j <;> simp [w, Nat.mul_comm]
  rw [hw, weight_shift w rfl] at hbefore
  rw [hw]
  have hcoeff : ((clearedSeed H i F).coeff b).natDegree ≤
      (H ^ (3 * i)).natDegree + (F.coeff (Finsupp.single none i + b)).natDegree := by
    simp only [clearedSeed, ← partial_eq_mixedHasse, MvPolynomial.coeff_C_mul, hu]
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add_left (Polynomial.natDegree_mul_C_le _ _) _)
  have hp' : (H ^ (3 * i)).natDegree ≤ 6819 * i := by
    calc
      _ ≤ (3 * i) * H.natDegree := Polynomial.natDegree_pow_le
      _ ≤ (3 * i) * 2273 := Nat.mul_le_mul_left _ hH
      _ = 6819 * i := by ring
  omega
private theorem seed_motion (w : I → K) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (hh : P.H.natDegree ≤ 2273) (box : Shape) (t : ℕ) (F : PhysicalRow)
    (hF : Source w P L box t F) (i : ℕ) :
    Source w P L box (t + 6819 * i) (clearedSeed P.H i F) := by
  obtain ⟨hcap, hcut, hcontact, hpole⟩ := hF
  refine ⟨K1_13_4_3_1.caps_seed P.H i F box hcap, ?_, K1_13_4_3_1.contact_seed P.H i w F hcontact,
    K1_13_4_3_1.pole_seed P L _ i F hpole⟩
  simpa only [Nat.add_right_comm] using trueCut_seed P.H i _ F hh hcut
private theorem mixedOrder_iff_coeff {F : GenericRow} {z : GenericX}
    {y : Fin 3 → GenericX} {d : ℕ} :
    MixedOrder F z y d ↔
      ∀ a, mixedWeight a < d → (K1_13_4.translate (atPoint z y) F).coeff a = 0 := by
  constructor
  · intro h a ha
    by_contra hz
    exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))
  · intro h a ha
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp ha) (h a hlt)
private theorem fixed_seed_order (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : P3.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (k : ℕ) (hk : t + 48914 * k < 5000 * 179983) :
    LowerOrder (atSeed (inclConst (P.z γ)) (toGeneric F))
      (trajectory (extend (s γ))) (k + 1) := by
  let res := residueAt L.numerator L.denominator (P.z γ)
  obtain ⟨Q, hQ, hrestore⟩ := h2 w Γ s P L box t F hF γ hγ
  obtain ⟨T, hT, hST⟩ := L.quotient γ hγ
  change extend (s γ) = P.H * T + res at hST
  obtain ⟨A, hA, hhits⟩ := hw.hits γ hγ
  have hhit : ∃ B : Finset I, 179983 ≤ B.card ∧
      ∀ i ∈ B, (P.H * T + res).eval (embed (node i)) = embed (w i) := by
    refine ⟨A, hA, fun i hi => ?_⟩
    rw [← hST, extend, Polynomial.eval_map, Polynomial.eval₂_at_apply, hhits i hi]
  have hcontact := rawContact_of_restore 5000 w P.H res (P.z γ) (box.b + box.j) F Q
    P.nodes hF.2.2.1 hrestore
  have ho := raw_locator_order w P.H res T t k Q hT hhit hcontact hQ hk
  rw [hST]
  exact trueOrder_of_raw P.H res T (P.z γ) (box.b + box.j) (k + 1) F Q
    P.monic.ne_zero hrestore ho
private theorem source_order (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : P3.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (hh : P.H.natDegree ≤ 2273) {d : ℕ} (hd : t + d ≤ 5000 * 179983) :
    MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) d := by
  set z := inclConst (P.z γ)
  set y := trajectory (extend (s γ))
  apply mixedOrder_iff_coeff.mpr
  intro m hm
  let a : SeedVar →₀ ℕ := Finsupp.single none (m none)
  let b : SeedVar →₀ ℕ := m.some.optionElim 0
  have hab : a + b = m := by
    ext i
    cases i <;> simp [a, b]
  have hdis : ∀ i, i ∉ a.support ∨ i ∉ b.support := by
    intro i
    cases i <;> simp [a, b, Finsupp.mem_support_iff]
  have hlt : t + 6819 * m none + 48914 * m.some.degree < 5000 * 179983 := by
    change 6819 * m none + 48914 * m.some.degree < d at hm
    omega
  have hD := seed_motion w P L hh box t F hF (m none)
  have ho := fixed_seed_order h2 hw P L hD hγ m.some.degree hlt
  have hc := coeff_eq_zero_of_lowerOrder ho m.some (Nat.lt_succ_self _)
  change (K1_13_4.translate y (atSeed z (toGeneric (clearedSeed P.H (m none) F)))).coeff m.some = 0 at hc
  have hmap :
      K1_13_4.translate y (atSeed z (toGeneric (clearedSeed P.H (m none) F))) =
        MvPolynomial.C (inclX (P.H ^ (3 * m none))) *
          K1_13_4.translate y (atSeed z (toGeneric (mixedHasse a F))) := by
    simp [clearedSeed, toGeneric, a, atSeed, K1_13_4.translate]
  rw [hmap, MvPolynomial.coeff_C_mul] at hc
  have hn : inclX (P.H ^ (3 * m none)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericX)).mpr (pow_ne_zero _ P.monic.ne_zero)
  have hcoef := (mul_eq_zero.mp hc).resolve_left hn
  rw [translate_atSeed, coeff_atSeed_zero, ← partial_eq_mixedHasse, toGeneric, map_partial,
    translate_partial] at hcoef
  change (hasse a (K1_13_4.translate (atPoint z y) (toGeneric F))).coeff b = 0 at hcoef
  rw [coeff_partial_eq_of_disjoint _ _ _ hdis, hab] at hcoef
  exact hcoef
private theorem mixedHasse_order (F : PhysicalRow) (a : SeedVar →₀ ℕ)
    (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ)
    (hF : MixedOrder (toGeneric F) z y (d + mixedWeight a)) :
    MixedOrder (toGeneric (mixedHasse a F)) z y d := by
  apply mixedOrder_iff_coeff.mpr
  intro b hb
  have hlt : mixedWeight (a + b) < d + mixedWeight a := by rw [mixedWeight_add]; omega
  have hz := mixedOrder_iff_coeff.mp hF _ hlt
  rw [← partial_eq_mixedHasse, toGeneric, map_partial, translate_partial]
  exact coeff_partial_eq_zero _ _ _ hz
theorem proof : P3_6_4.c3 := by
  intro w Γ s hw P L hh
  let h2 := K1_13_4_3_2.proof
  constructor
  · intro F hF γ hγ
    exact source_order h2 hw P L hF hγ hh (Nat.sub_add_cancel (show 6317872 ≤ 0x35a39cf8 from by decide)).le
  · intro G hG γ hγ
    let z := inclConst (P.z γ)
    let y := trajectory (extend (s γ))
    change MixedOrder (toGeneric G) z y secondOrder
    change G ∈ Submodule.span Geom _ at hG
    induction hG using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨t, F, a, hF, ht, rfl⟩ := hQ
      apply mixedHasse_order
      apply source_order h2 hw P L hF hγ hh
      change t + mixedWeight a ≤ 5000 * 179983 - 3661738 at ht
      change t + (3661738 + mixedWeight a) ≤ 5000 * 179983
      omega
    | zero =>
      exact mixedOrder_iff_coeff.mpr (fun _ _ => by simp [toGeneric])
    | add Q R _ _ hQ hR =>
      exact mixedOrder_iff_coeff.mpr (fun a ha => by
        simp only [toGeneric, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
        exact (congrArg₂ (· + ·)
          (mixedOrder_iff_coeff.mp hQ a ha) (mixedOrder_iff_coeff.mp hR a ha)).trans (add_zero 0))
    | smul c Q _ hQ =>
      apply mixedOrder_iff_coeff.mpr
      intro a ha
      have hsmul : c • Q = MvPolynomial.C (Polynomial.C c) * Q := by
        rw [Algebra.smul_def]
        rfl
      rw [hsmul]
      simp only [toGeneric, map_mul, MvPolynomial.map_C, K1_13_4.translate, MvPolynomial.eval₂Hom_C,
        MvPolynomial.coeff_C_mul]
      exact mul_eq_zero.mpr (Or.inr (mixedOrder_iff_coeff.mp hQ a ha))
end
end P3_6_4_3
end
