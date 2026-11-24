import ProximityPrize.SubmissionLower.FrontBranch12
import ProximityPrize.SubmissionLower.GoldBranch3
import ProximityPrize.SubmissionLower.UpperBranch3

-- merged module GoldBranch6
section Merged_GoldBranch6
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6
noncomputable section
open Polynomial
open P3 (I K agreement)
open K1_13 (Geom extend Row Shape shape InBox Fits Contact remaining chart liftedChart
  mixed32 ceilDiv atJet OrderAt indexDegree)
open scoped BigOperators
abbrev physicalDegree := P3.physicalDegree
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev incidenceGap : ℕ := agreement - physicalDegree
abbrev primaryBox : Shape := P0_9.primaryBox
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
abbrev factorCap : ℕ := 0x32cdf437872295e
abbrev commonBox : Shape := ⟨6245, 2022, 0⟩
abbrev resultantBox : Shape := ⟨0x38c7faf0, 0x13315480, 0⟩
abbrev fatOrder : ℕ := 69360
abbrev divisorOrder : ℕ := 56875
abbrev isolatedOrder : ℕ := 1734
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ commonBox.b
  common_index : indexDegree common ≤ commonBox.j
  residual_total : residual.totalDegree ≤ resultantBox.b
  residual_index : indexDegree residual ≤ resultantBox.j
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPrice (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (P3.t * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (P3.t * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated
end
end P3_6
end
section
namespace P3_6
noncomputable section
open P3 (K)
open K1_13 (extend Row Shape shape Fits atJet OnFactor FatEligible)
open scoped BigOperators
end
end P3_6
end

end Merged_GoldBranch6

-- merged module GoldBranch6N4
section Merged_GoldBranch6N4
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
abbrev bankRank : ℕ := 0x4b8ba3f30d83cce664
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  6819 * a none + 48914 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
def MixedOrder (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ) : Prop :=
  ∀ a ∈ (translate (atPoint z y) F).support, d ≤ mixedWeight a
def PairOrders (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) : Prop :=
  MixedOrder F z y firstOrder ∧ MixedOrder G z y secondOrder
structure CommonPair (F G : GenericRow) where
  fixed : Finset GenericRow
  moving : Finset GenericRow
  pure : (Polynomial GenericX)
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
open P0_9_4 (inclX_injective coefficientDerivative coeff_coefficientDerivative dotted polynomialPoint eval_dotted eval_map_point degreeOf_le_of_support_subset dotted_weight seed_weight)
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
      ∀ (z : Geom) (S : (Polynomial Geom)),
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
theorem moving_lower (f : GenericRow)
    (hf : Irreducible f) (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 17)
    (hu : 0 < seedDegree f) (htop : f.degreeOf (some 2) = 0) :
    ∃ q : Lower, q ≠ 0 ∧ q.totalDegree ≤ 2 * seedDegree f * jetTotal f ∧
      lowerIndex q ≤ (2 * jetIndex f + 1) * seedDegree f ∧
      ∀ (z : Geom) (S : (Polynomial Geom)),
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
theorem total_prod {ι : Type*} (s : Finset ι) (q : ι → Lower)
    (hn : ∀ i ∈ s, q i ≠ 0) :
    (∏ i ∈ s, q i).totalDegree = ∑ i ∈ s, (q i).totalDegree := by
  simp only [← MvPolynomial.weightedTotalDegree_one]
  exact MvPolynomial.weightedTotalDegree_prod _ s q hn
theorem index_prod {ι : Type*} (s : Finset ι) (q : ι → Lower)
    (hn : ∀ i ∈ s, q i ≠ 0) :
    lowerIndex (∏ i ∈ s, q i) = ∑ i ∈ s, lowerIndex (q i) := by
  simp only [lowerIndex_eq_weighted]
  exact MvPolynomial.weightedTotalDegree_prod _ s q hn
theorem eval_prod_factor_ne_zero {ι : Type*} {s : Finset ι} {q : ι → Lower}
    {y : Fin 3 → GenericX} (hq : MvPolynomial.eval y (∏ i ∈ s, q i) ≠ 0)
    {i : ι} (hi : i ∈ s) : MvPolynomial.eval y (q i) ≠ 0 :=
  (Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hq)) i hi
theorem eliminate_common (Γ : Finset K) (z : K → Geom) (S : K → (Polynomial Geom))
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
theorem resultant_taylor_formal {R : Type*} [CommRing R]
    (F G : (Polynomial R)) (z : R) {m n : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) :
    resultant (F.taylor z) (G.taylor z) m n = resultant F G m n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hF
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hG
  have expand (P Q : (Polynomial R)) :
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
    (P : (Polynomial (Polynomial k))) (d e i j : ℕ) (hij : j ≤ i)
    (hP : ∀ i l : ℕ, 6819 * i + 48914 * l < d → (P.coeff i).coeff l = 0) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (d + e) i - weight e j) ∣ P.coeff (i - j) := by
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
    (F G : (Polynomial (Polynomial k))) (m n : ℕ)
    (hF : ∀ i l : ℕ, 6819 * i + 48914 * l < firstOrder → (F.coeff i).coeff l = 0)
    (hG : ∀ i l : ℕ, 6819 * i + 48914 * l < secondOrder → (G.coeff i).coeff l = 0)
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
    (hbudget : (∑ j, col j) + 48914 * D ≤ (∑ i, row i) + 48913) :
    (Polynomial.X : (Polynomial k)) ^ D ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a : Fin N → ℕ := fun j => power (row (σ j) - col j)
  have hprod : (Polynomial.X : (Polynomial k)) ^ (∑ j, a j) ∣ ∏ j, M (σ j) j := by
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
    (F G : (Polynomial (Polynomial GenericX))) (z : GenericX) {m n D : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (hFO : ∀ i l : ℕ, 6819 * i + 48914 * l < firstOrder →
      ((F.taylor (C z)).coeff i).coeff l = 0)
    (hGO : ∀ i l : ℕ, 6819 * i + 48914 * l < secondOrder →
      ((G.taylor (C z)).coeff i).coeff l = 0)
    (hbudget : (∑ j : Fin (m + n), columnWeight (m := m) (n := n) j) + 48914 * D ≤
      (∑ i : Fin (m + n), weight (firstOrder + secondOrder) i) + 48913) :
    (Polynomial.X : (Polynomial GenericX)) ^ D ∣ resultant F G m n := by
  rw [← resultant_taylor_formal F G (C z) hF hG]
  unfold resultant
  exact det_bound
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i => weight (firstOrder + secondOrder) i)
    (columnWeight (m := m) (n := n))
    (sylvester_entry _ _ m n hFO hGO) hbudget
theorem line_resultant_order (F G : (Polynomial (Polynomial GenericX))) (z : GenericX)
    (hF : F.natDegree ≤ 70000) (hG : G.natDegree ≤ 70000)
    (hFO : ∀ i j, 6819 * i + 48914 * j < firstOrder →
      ((F.taylor (Polynomial.C z)).coeff i).coeff j = 0)
    (hGO : ∀ i j, 6819 * i + 48914 * j < secondOrder →
      ((G.taylor (Polynomial.C z)).coeff i).coeff j = 0) :
    (Polynomial.X : (Polynomial GenericX)) ^ 69360 ∣ Polynomial.resultant F G 70000 70000 := by
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
private theorem inclX_injective : Function.Injective inclX :=
  IsFractionRing.injective (Polynomial Geom) GenericX
theorem eval_cleared {Q : Row 3} {R : Lower} {d : (Polynomial Geom)}
    (hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R) (S : (Polynomial Geom))
    (hR : MvPolynomial.eval (trajectory S) R = 0) : atJet Q S = 0 := by
  have hcomm : inclX (atJet Q S) =
      MvPolynomial.eval (trajectory S) (MvPolynomial.map inclX Q) := by
    rw [atJet, MvPolynomial.eval_map]
    exact MvPolynomial.eval₂_comp inclX (jet S) Q
  apply inclX_injective
  rw [map_zero, hcomm, hQ, map_mul, hR, mul_zero]
private theorem map_shift (Q : Row 3) (S : (Polynomial Geom)) :
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
theorem order_cleared {Q : Row 3} {R : Lower} {d : (Polynomial Geom)}
    (hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R)
    (S : (Polynomial Geom)) {m : ℕ} (hR : LowerOrder R (trajectory S) m) : OrderAt Q S m := by
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
end
end P3_6_4
end
section
namespace P3_6_4_2
noncomputable section
open K1_13_4 hiding CommonPair
open K1_13_4_4 (FactorsFor factorProduct)
open P3_6_4 (CommonPair)
open scoped Polynomial BigOperators
open K1_13_4_4 (pureEval pureEval_section pure_degree_le caps_of_dvd)
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
  let pure : (Polynomial GenericX) := ∏ f ∈ pureFactors, (pureEval f) ^ powCount f
  have hpure : pureSeed pure = ∏ f ∈ pureFactors, f ^ powCount f := by
    let φ : (Polynomial GenericX) →+* GenericRow :=
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

end Merged_GoldBranch6N4

-- merged module UpperBranch5
section Merged_UpperBranch5
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_5
open K1_14 (Shape slots shapeSum)
def kept (U v g r : ℕ) : ℕ :=
  if r ≤ g then slots U (r*v) else 0
end P1_7_5
end
section
namespace P1_7_5
noncomputable section
open Polynomial Finset MvPolynomial
open K1_14 (FX Jet Equation Shape SeedBound shapeSum slots triangle)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth seedDegree seedDegree_le_iff seedDegree_mul seedDegree_pow)
open K1_14_4 (flatten)
open K1_14_4 (gradeMap mem_filtered finrank_le_grades)
open K1_14_4 (shapeSum_swap)
end
end P1_7_5
end
section
namespace P1_7_5
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P1 (agreement)
open K1_14_4 (slots_antitone sum_slot_drops sum_interval power_threshold)
theorem position_sum (top step t j U v g : ℕ) (hj : j ≤ t) (hs : 0 < step) :
    (∑ W ∈ range top, if t ≤ W+j then
      kept U v g (1+(top-1-W)/step-j) else 0) +
    ((∑ a ∈ range g, (slots U (a*v) - slots U ((a+1)*v)) * (top+j-t-step*(j+a))) +
      slots U (g*v) * (top+j-t-step*(j+g))) =
    triangle U * (top+j-t) := by
  let A := kept U v g
  let L W := 1+(top-1-W)/step-j
  have hmono : Antitone A := by
    intro a b hab
    by_cases hb : b ≤ g
    · simpa only [A, kept, ite_eq_left hb, ite_eq_left (hab.trans hb)] using
        slots_antitone U (Nat.mul_le_mul_right v hab)
    · simp [A, kept, hb]
  have hmin (l : ℕ) : A (min (g+1) l) = A l := by
    by_cases hl : l ≤ g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [A, kept, show ¬ g+1 ≤ g by omega, show ¬ l ≤ g by omega]
  have hsplit :
      (∑ a ∈ range (g+1), (A a - A (a+1)) * (top+j-t-step*(j+a))) =
        (∑ a ∈ range g, (slots U (a*v) - slots U ((a+1)*v)) * (top+j-t-step*(j+a))) +
        slots U (g*v) * (top+j-t-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro a ha
      simp [A, kept, (mem_range.mp ha).le, Nat.succ_le_of_lt (mem_range.mp ha)]
    · simp [A, kept, show ¬ g+1 ≤ g by omega]
  rw [← hsplit]
  change (∑ W ∈ range top, if t ≤ W+j then A (L W) else 0) + _ = _
  have hzero : A 0 = triangle U := by simp [A, kept, slots]
  rw [← hzero]
  simp_rw [← sum_interval top j t _ _ hj]
  rw [sum_comm (s := range (g+1)), ← sum_add_distrib]
  have hbase := sum_interval top j t 0 (A 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt := mem_range.mp hW
  by_cases h : t ≤ W+j
  · simp only [h, true_and, Nat.add_zero, hWt, ite_true]
    have hsum := sum_slot_drops A hmono (g+1) (L W)
    rw [hmin, add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [show a < L W ↔ W+step*(j+a) < top from power_threshold _ _ _ _ _ hWt hs]
  · simp [h]
end P1_7_5
end

end Merged_UpperBranch5
