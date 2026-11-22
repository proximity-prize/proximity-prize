import ProximityPrize.SubmissionLower.FrontBranch12
import ProximityPrize.SubmissionLower.FrontBranch5
import ProximityPrize.SubmissionLower.GoldBranch6

-- merged module GoldBranch5
section Merged_GoldBranch5
set_option autoImplicit true
end Merged_GoldBranch5

set_option autoImplicit true
section
namespace P3_6_4
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
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
end P3_6_4
end
section
namespace P3_6_4
noncomputable section
open K1_13 Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped BigOperators
set_option maxRecDepth 4000
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