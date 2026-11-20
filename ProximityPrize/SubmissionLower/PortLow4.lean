import ProximityPrize.SubmissionLower.PortLowBase
set_option Elab.async false

section PackSource_P0_9_4Defs
set_option autoImplicit true
namespace P0_9_4

noncomputable section

open K1 (I K)
open K1_13 (Geom Shape)
open K1_13_4
open scoped Polynomial BigOperators

/-- The old residue chart depends on the actual pole and its raw quotient degree.
The only changed field of the input structure is a stricter height bound. -/
def asOldPole {Γ s} (P : P0_9.PoleData Γ s) : K1_13.PoleData Γ s where
  H := P.H
  monic := P.monic
  small := ⟨P.small.1, P.small.2.trans (by decide)⟩
  nodes := P.nodes
  degree := P.degree
  z := P.z
  injective := P.injective
  c := P.c
  q := P.q
  a₀ := P.a₀
  a₁ := P.a₁
  c_unit := P.c_unit
  q_unit := P.q_unit
  a₀_unit := P.a₀_unit
  regular := P.regular
  residue := P.residue

abbrev firstCut : ℕ := 5000 * P0.agreement - firstOrder
abbrev secondCut : ℕ := 5000 * P0.agreement - secondOrder
abbrev bankRank : ℕ := 2426980608909015050627

/-- Seed motion spends at most 7800 even on repeated poles. The raw quotient
has degree 131071, so each additional lower-jet order spends 49139. -/
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  7800 * a none + 49139 * a.some.degree

theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl

/-- Spans the true-jet Hasse derivatives available within the second cutoff. -/
def Necessary {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P) :
    Submodule Geom PhysicalRow :=
  Submodule.span Geom {Q | ∃ t F a, Source w P L secondBox t F ∧
    t + mixedWeight a ≤ secondCut ∧ Q = mixedHasse a F}

def MixedOrder (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ) : Prop :=
  ∀ a ∈ (translate (atPoint z y) F).support, d ≤ mixedWeight a

def PairOrders (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) : Prop :=
  MixedOrder F z y firstOrder ∧ MixedOrder G z y secondOrder

/-- Actual gcd decomposition with the retuned simultaneous resource bounds. -/
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
  fixed_total : jetTotal (∏ f ∈ fixed, f) ≤ 72
  fixed_index : jetIndex (∏ f ∈ fixed, f) ≤ 24
  moving_total : jetTotal (∏ f ∈ moving, f) ≤ 11
  moving_index : jetIndex (∏ f ∈ moving, f) ≤ 3
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 118
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
end P0_9_4
end PackSource_P0_9_4Defs

section PackSource_P0_9_4Moving
set_option autoImplicit true
namespace P0_9_4

noncomputable section

open K1_13 K1_13_4 MvPolynomial
open scoped Polynomial BigOperators

private theorem inclX_injective : Function.Injective inclX :=
  IsFractionRing.injective Geom[X] GenericX

/-- Use one common denominator without changing the support of the row. -/
theorem clear_denominators {σ : Type*} (f : MvPolynomial σ GenericX) :
    ∃ (d : Geom[X]) (P : MvPolynomial σ Geom[X]), d ≠ 0 ∧ P.support = f.support ∧
      MvPolynomial.map inclX P = C (inclX d) * f := by
  classical
  let M := nonZeroDivisors (Geom[X])
  let d := IsLocalization.commonDenom M f.support f.coeff
  let num := IsLocalization.integerMultiple M f.support f.coeff
  let P : MvPolynomial σ Geom[X] := ∑ a : ↥f.support, monomial a.val (num a)
  have hd : (d : Geom[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : inclX (d : Geom[X]) ≠ 0 := (map_ne_zero_iff inclX inclX_injective).mpr hd
  have hP : MvPolynomial.map inclX P = C (inclX d) * f := by
    ext m
    simp only [coeff_map, coeff_C_mul, P, coeff_sum]
    by_cases hm : m ∈ f.support
    · let a : ↥f.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M f.support f.coeff a
        change inclX (num a) = (d : Geom[X]) • f.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [coeff_monomial, hb]
    · have hz : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥f.support, (monomial a.val (num a) : MvPolynomial σ Geom[X]).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  refine ⟨d, P, hd, ?_, hP⟩
  rw [← support_map_of_injective P inclX_injective, hP]
  ext m
  simp [MvPolynomial.mem_support_iff, coeff_C_mul, hi]

private def coefficientDerivative (P : PhysicalRow) : PhysicalRow :=
  ∑ m ∈ P.support, monomial m (Polynomial.derivative (P.coeff m))

@[simp] private theorem coeff_coefficientDerivative (P : PhysicalRow) (m : SeedVar →₀ ℕ) :
    (coefficientDerivative P).coeff m = Polynomial.derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm, map_zero]

private theorem coefficientDerivative_C (c : Geom[X]) :
    coefficientDerivative (C c) = C (Polynomial.derivative c) := by
  ext m
  by_cases hm : 0 = m <;> simp [coeff_C, hm]

private theorem coefficientDerivative_add (P Q : PhysicalRow) :
    coefficientDerivative (P + Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp

private theorem coefficientDerivative_mul_X (P : PhysicalRow) (j : SeedVar) :
    coefficientDerivative (P * MvPolynomial.X j) = coefficientDerivative P * MvPolynomial.X j := by
  ext m
  rw [coeff_coefficientDerivative, coeff_mul_X', coeff_mul_X']
  split_ifs <;> simp

/-- The chain rule differentiates both the coefficients and the substituted variables. -/
private theorem eval_chain (P : PhysicalRow) (a : SeedVar → Geom[X]) :
    Polynomial.derivative (eval a P) = eval a (coefficientDerivative P) +
      ∑ i, Polynomial.derivative (a i) * eval a (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [coefficientDerivative_C]
  | add P Q hP hQ =>
    simp only [map_add, coefficientDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    rw [map_mul, eval_X, Polynomial.derivative_mul, ih, coefficientDerivative_mul_X,
      map_mul, eval_X]
    simp only [pderiv_mul, map_add, map_mul, eval_X, mul_add, Finset.sum_add_distrib]
    have left : (∑ i, Polynomial.derivative (a i) * (eval a (pderiv i P) * a j)) =
        (∑ i, Polynomial.derivative (a i) * eval a (pderiv i P)) * a j := by
      simp only [Finset.sum_mul, mul_assoc]
    have right : (∑ i, Polynomial.derivative (a i) * (eval a P * eval a (pderiv i (MvPolynomial.X j)))) =
        Polynomial.derivative (a j) * eval a P := by
      simp [pderiv_X, Pi.single_apply, mul_ite]
    rw [left, right]
    ring

/-- The dotted row, with the coefficient derivative supplied separately. -/
private def dotted {R : Type*} [CommRing R] (r P : SeedRow R) : SeedRow R :=
  r + MvPolynomial.X (some 1) * pderiv (some 0) P +
    C (2 : R) * (MvPolynomial.X (some 2) * pderiv (some 1) P)

private def polynomialPoint (z : Geom) (S : Geom[X]) : SeedVar → Geom[X] :=
  fun i => i.elim (Polynomial.C z) (jet S)

private theorem derivative_hasse (S : Geom[X]) (k : ℕ) :
    Polynomial.derivative (Polynomial.hasseDeriv k S) =
      Polynomial.C ((k + 1 : ℕ) : Geom) * Polynomial.hasseDeriv (k + 1) S := by
  have h := LinearMap.congr_fun (Polynomial.hasseDeriv_comp (R := Geom) 1 k) S
  simpa [Polynomial.hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul,
    Polynomial.C_eq_natCast, Nat.add_comm, add_mul] using h

private theorem eval_dotted (P : PhysicalRow) (z : Geom) (S : Geom[X])
    (htop : P.degreeOf (some 2) = 0) :
    eval (polynomialPoint z S) (dotted (coefficientDerivative P) P) =
      Polynomial.derivative (eval (polynomialPoint z S) P) := by
  have hzero := pderiv_eq_zero_of_degreeOf_eq_zero htop
  have h₀ : Polynomial.derivative (polynomialPoint z S (some 0)) =
      polynomialPoint z S (some 1) := by
    simp [polynomialPoint, jet]
  have h₁ : Polynomial.derivative (polynomialPoint z S (some 1)) =
      Polynomial.C (2 : Geom) * polynomialPoint z S (some 2) := by
    simpa [polynomialPoint, jet] using derivative_hasse S 1
  have hz : Polynomial.derivative (polynomialPoint z S none) = 0 :=
    Polynomial.derivative_C
  rw [eval_chain, Fintype.sum_option, Fin.sum_univ_three]
  simp only [dotted, map_add, map_mul, eval_X, eval_C, h₀, h₁, hzero, hz, map_zero, mul_zero,
    add_zero, zero_mul]
  rw [map_ofNat (Polynomial.C : Geom →+* Geom[X])]
  ring

private theorem eval_map_point (z : Geom) (S : Geom[X]) (P : PhysicalRow) :
    eval (atPoint (inclConst z) (trajectory S)) (MvPolynomial.map inclX P) =
      inclX (eval (polynomialPoint z S) P) := by
  have hpoint : atPoint (inclConst z) (trajectory S) = inclX ∘ polynomialPoint z S := by
    funext i
    cases i with
    | none => exact RingHom.congr_fun (IsScalarTower.algebraMap_eq Geom Geom[X] GenericX) z
    | some i => rfl
  rw [hpoint, MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp inclX (polynomialPoint z S) P).symm

private theorem degreeOf_le_of_support_subset {P Q : GenericRow} (h : P.support ⊆ Q.support)
    (i : SeedVar) : P.degreeOf i ≤ Q.degreeOf i := by
  apply degreeOf_le_iff.mpr
  intro m hm
  exact le_degreeOf_of_mem_support i (h hm)

/-- Moving one power from variable i to variable j increases the weight by at most d. -/
private theorem moved_weight (w : SeedVar → ℕ) (i j : SeedVar) (P : GenericRow) (d : ℕ)
    (h : w j ≤ w i + d) :
    (MvPolynomial.X j * pderiv i P).weightedTotalDegree w ≤ P.weightedTotalDegree w + d := by
  apply Finset.sup_le
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_X_mul'] at hm
  split_ifs at hm with hj
  · have hn : m - Finsupp.single j 1 + Finsupp.single i 1 ∈ P.support := by
      rw [coeff_pderiv] at hm
      exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)
    have hw := le_weightedTotalDegree w hn
    have he := Finsupp.weight_sub_single_add (w := w) (Finsupp.mem_support_iff.mp hj)
    rw [map_add, Finsupp.weight_single, one_smul] at hw
    omega
  · exact (hm rfl).elim

private theorem dotted_weight (w : SeedVar → ℕ) (r P : GenericRow) (d : ℕ)
    (hr : r.support ⊆ P.support)
    (h₀ : w (some 1) ≤ w (some 0) + d) (h₁ : w (some 2) ≤ w (some 1) + d) :
    (dotted r P).weightedTotalDegree w ≤ P.weightedTotalDegree w + d := by
  rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  have hr' : r ∈ restrictWeightedDegree w (P.weightedTotalDegree w + d) := by
    apply mem_restrictWeightedDegree.mpr
    intro m hm
    exact (le_weightedTotalDegree w (hr hm)).trans (Nat.le_add_right _ _)
  have h₀' := mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr (moved_weight w _ _ P d h₀)
  have h₁' := mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr (moved_weight w _ _ P d h₁)
  unfold dotted
  rw [MvPolynomial.C_mul']
  exact (restrictWeightedDegree w _).add_mem ((restrictWeightedDegree w _).add_mem hr' h₀')
    ((restrictWeightedDegree w _).smul_mem (2 : GenericX) h₁')

private theorem seed_weight (P : GenericRow) :
    P.weightedTotalDegree (Pi.single none 1) = seedDegree P := by
  rw [seedDegree, degreeOf_eq_sup, weightedTotalDegree]
  simp only [Finsupp.weight_single_one_apply]

private theorem small_cast_ne_zero (n : ℕ) (hpos : 0 < n) (hsmall : n ≤ 11) :
    (n : GenericX) ≠ 0 := by
  let : CharP GenericX K1.p := charP_of_injective_ringHom (inclConst.comp embed).injective K1.p
  intro hz
  have hlarge : 11 < K1.p := by decide
  exact (not_le_of_gt (hsmall.trans_lt hlarge))
    (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff GenericX K1.p n).mp hz))

private theorem pderiv_moved {P : GenericRow} {i j k : SeedVar} (h : P.degreeOf k = 0) :
    pderiv k (MvPolynomial.X j * pderiv i P) = pderiv k (MvPolynomial.X j : GenericRow) * pderiv i P := by
  have hzero : pderiv k (pderiv i P) = 0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero (Nat.eq_zero_of_le_zero ((degreeOf_pderiv_le i k P).trans_eq h))
  rw [pderiv_mul, hzero, mul_zero, add_zero]

/-- If k is absent from f, divisibility by f survives the k partial. -/
private theorem partial_not_dvd {f g : GenericRow} (i k : SeedVar) (a : GenericX)
    (hi : 0 < f.degreeOf i) (hsmall : f.degreeOf i ≤ 11) (hk : f.degreeOf k = 0)
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
    (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 11) (htop : f.degreeOf (some 2) = 0)
    (hr : r.support ⊆ f.support) (a : GenericX) (ha : a ≠ 0) :
    IsRelPrime f (dotted r (C a * f)) := by
  have hd (i : SeedVar) : (C a * f).degreeOf i = f.degreeOf i := by
    rw [degreeOf_mul_eq (C_ne_zero.mpr ha) hf.ne_zero, degreeOf_C, zero_add]
  have hsmall (i : Fin 3) : f.degreeOf (some i) ≤ 11 :=
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

/-- A moving common factor of the retuned bank has degree at most eleven.
Its coefficient-and-jet derivative is a proper cutter along each marked trajectory. -/
theorem moving_cutter (f : GenericRow) (hf : Irreducible f)
    (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 11) (htop : f.degreeOf (some 2) = 0) :
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

end P0_9_4
end PackSource_P0_9_4Moving

section PackSource_P0_9_4Eliminate
set_option autoImplicit true
namespace P0_9_4
noncomputable section

open K1 K1_13 K1_13_4 K1_13_4_5
open scoped Polynomial BigOperators

private theorem mixedWeight_pos {a : SeedVar →₀ ℕ} (ha : a ≠ 0) : 0 < mixedWeight a := by
  by_contra! h
  change 7800 * a none + 49139 * a.some.degree ≤ 0 at h
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
    (hf : Irreducible f) (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 11)
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

/-- Book the pure seed roots and eliminate both kinds of common jet factors. -/
theorem eliminate_common (Γ : Finset K) (z : K → Geom) (S : K → Geom[X])
    (hzinj : Function.Injective z) {F G : GenericRow} (D : CommonPair F G)
    (hOrders : ∀ γ ∈ Γ, PairOrders F G (inclConst (z γ)) (trajectory (S γ))) :
      ∃ (book : Finset K) (Q : Lower), book.card ≤ 140000 ∧ Q ≠ 0 ∧
        Q.totalDegree ≤ 6300 ∧ lowerIndex Q ≤ 2403 ∧
        ∀ γ ∈ Γ, γ ∉ book → MvPolynomial.eval (trajectory (S γ)) Q = 0 ∨
          PairOrders D.left D.right (inclConst (z γ)) (trajectory (S γ)) := by
  classical
  have fix_ne (f : GenericRow) (hf : f ∈ D.fixed) : f ≠ 0 :=
    (D.fixed_kind f hf).1.ne_zero
  have mov_ne (f : GenericRow) (hf : f ∈ D.moving) : f ≠ 0 :=
    (D.moving_kind f hf).1.ne_zero
  have mov_total : (∑ f ∈ D.moving, jetTotal f) ≤ 11 := by
    simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_total
  have mov_index : (∑ f ∈ D.moving, jetIndex f) ≤ 3 := by
    simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_index
  have mov_seed : (∑ f ∈ D.moving, seedDegree f) ≤ 118 := by
    simpa only [seedDegree, MvPolynomial.degreeOf_prod_eq _ _ mov_ne] using D.moving_seed
  have seed_le (f : GenericRow) (hf : f ∈ D.moving) : seedDegree f ≤ 118 :=
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
  have Pt : P.totalDegree ≤ 72 := by
    change (∏ f ∈ D.fixed, q f).totalDegree ≤ 72
    rw [total_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetTotal f := Finset.sum_congr rfl qt
      _ ≤ _ := by
        simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_total
  have Pi : lowerIndex P ≤ 24 := by
    change lowerIndex (∏ f ∈ D.fixed, q f) ≤ 24
    rw [index_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetIndex f := Finset.sum_congr rfl qi
      _ ≤ _ := by
        simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_index
  have Rt : R.totalDegree ≤ 2 * 118 * 11 := by
    change (∏ f ∈ D.moving, r f).totalDegree ≤ 2 * 118 * 11
    rw [total_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, (2 * 118) * jetTotal f :=
        Finset.sum_le_sum fun f hf => (rt f hf).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf)))
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ mov_total
  have Ri : lowerIndex R ≤ (2 * 3 + 1) * 118 := by
    change lowerIndex (∏ f ∈ D.moving, r f) ≤ (2 * 3 + 1) * 118
    rw [index_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, ((2 * 118) * jetIndex f + seedDegree f) := by
        apply Finset.sum_le_sum
        intro f hf
        refine (ri f hf).trans ?_
        rw [Nat.add_mul, one_mul, Nat.mul_right_comm 2]
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf))) _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hh := Nat.mul_le_mul_left (2 * 118) mov_index
        omega
  let book := seedBook Γ z D.pure
  have hbook : book.card ≤ 140000 :=
    (count_seed_roots Γ z hzinj D.pure D.pure_ne).trans D.pure_degree
  refine ⟨book, P * R, hbook, mul_ne_zero Pn Rn, ?_, ?_, ?_⟩
  · simp only [← MvPolynomial.weightedTotalDegree_one] at Pt Rt ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pt Rt).trans (show 72 + 2 * 118 * 11 ≤ 6300 by decide)
  · simp only [lowerIndex_eq_weighted] at Pi Ri ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pi Ri).trans (show 24 + (2 * 3 + 1) * 118 ≤ 2403 by decide)
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
end P0_9_4
end PackSource_P0_9_4Eliminate

section PackSource_P0_9_4Local
set_option autoImplicit true
namespace P0_9_4

open K1_13_4 Polynomial
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

/-- The part of a mixed order still required after accounting for a seed exponent. -/
private def weight (d i : ℕ) : ℕ := d - 7800 * i

-- Put the variable in the recursive argument of Nat.add.
private def power (w : ℕ) : ℕ := (49138 + w) / 49139

private theorem coefficient_bound {k : Type*} [CommRing k]
    (P : k[X][X]) (d e i j : ℕ) (hij : j ≤ i)
    (hP : ∀ i l : ℕ, 7800 * i + 49139 * l < d → (P.coeff i).coeff l = 0) :
    (Polynomial.X : k[X]) ^ power (weight (d + e) i - weight e j) ∣ P.coeff (i - j) := by
  have hweight : weight (d + e) i ≤ weight e j + weight d (i - j) := by
    unfold weight
    omega
  apply X_pow_dvd_iff.mpr
  intro l hl
  apply hP
  unfold power at hl
  have hsmall : 49139 * l < weight (d + e) i - weight e j := by omega
  unfold weight at hweight hsmall
  omega

/-- The two sets of columns shift the coefficients of G and F, respectively.
Each column uses the weight for the opposite polynomial at its shift. -/
private def columnWeight {m n : ℕ} (j : Fin (m + n)) : ℕ :=
  j.addCases (fun j : Fin m => weight firstOrder j) (fun j : Fin n => weight secondOrder j)

private theorem sylvester_entry {k : Type*} [CommRing k]
    (F G : k[X][X]) (m n : ℕ)
    (hF : ∀ i l : ℕ, 7800 * i + 49139 * l < firstOrder → (F.coeff i).coeff l = 0)
    (hG : ∀ i l : ℕ, 7800 * i + 49139 * l < secondOrder → (G.coeff i).coeff l = 0)
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

/-- Every Leibniz term uses every row and every column once. Summing the
entry powers therefore bounds the divisibility of each whole term. -/
private theorem det_bound {k : Type*} [CommRing k] {N D : ℕ}
    (M : Matrix (Fin N) (Fin N) k[X]) (row col : Fin N → ℕ)
    (hM : ∀ i j, (Polynomial.X : k[X]) ^ power (row i - col j) ∣ M i j)
    (hbudget : (∑ j, col j) + 49139 * D ≤ (∑ i, row i) + 49138) :
    (Polynomial.X : k[X]) ^ D ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a : Fin N → ℕ := fun j => power (row (σ j) - col j)
  have hprod : (Polynomial.X : k[X]) ^ (∑ j, a j) ∣ ∏ j, M (σ j) j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hM (σ j) j)
  have hsum : (∑ i, row i) ≤ (∑ j, col j) + 49139 * (∑ j, a j) := by
    rw [← Equiv.sum_comp σ row, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [a, power]
    omega
  have hD : D ≤ ∑ j, a j := by omega
  exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hD).trans hprod) _

private theorem sum_weight {d t N : ℕ} (ht : t ≤ N) (hend : d ≤ 7800 * t)
    (hbefore : ∀ i < t, 7800 * i ≤ d) :
    (∑ i : Fin N, weight d i) = t * d - 7800 * (t * (t - 1) / 2) := by
  rw [Fin.sum_univ_eq_sum_range]
  have htrim : (∑ i ∈ Finset.range t, weight d i) = ∑ i ∈ Finset.range N, weight d i := by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold weight
    omega
  rw [← htrim]
  have hsum : (∑ i ∈ Finset.range t, weight d i) + 7800 * (∑ i ∈ Finset.range t, i) =
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
    (∑ j : Fin (70000 + 70000), columnWeight (m := 70000) (n := 70000) j) + 49139 * 41522 ≤
      (∑ i : Fin (70000 + 70000), weight (firstOrder + secondOrder) i) + 49138 := by
  have hF : (∑ i : Fin 70000, weight firstOrder i) = 2119578835 := by
    rw [sum_weight (t := 737) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder]; omega)]
    decide
  have hG : (∑ i : Fin 70000, weight secondOrder i) = 493235864 := by
    rw [sum_weight (t := 356) (by decide) (by decide)
      (by intro i hi; simp only [secondOrder]; omega)]
    decide
  have hFG : (∑ i : Fin (70000 + 70000), weight (firstOrder + secondOrder) i) =
      4653502308 := by
    rw [sum_weight (t := 1092) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder, secondOrder]; omega)]
    decide
  rw [Fin.sum_univ_add, hFG]
  simp only [columnWeight, Fin.addCases_left, Fin.addCases_right, hF, hG]
  decide

private theorem resultant_bound
    (F G : GenericX[X][X]) (z : GenericX) {m n D : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (hFO : ∀ i l : ℕ, 7800 * i + 49139 * l < firstOrder →
      ((F.taylor (C z)).coeff i).coeff l = 0)
    (hGO : ∀ i l : ℕ, 7800 * i + 49139 * l < secondOrder →
      ((G.taylor (C z)).coeff i).coeff l = 0)
    (hbudget : (∑ j : Fin (m + n), columnWeight (m := m) (n := n) j) + 49139 * D ≤
      (∑ i : Fin (m + n), weight (firstOrder + secondOrder) i) + 49138) :
    (Polynomial.X : GenericX[X]) ^ D ∣ resultant F G m n := by
  rw [← resultant_taylor_formal F G (C z) hF hG]
  unfold resultant
  exact det_bound
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i => weight (firstOrder + secondOrder) i)
    (columnWeight (m := m) (n := n))
    (sylvester_entry _ _ m n hFO hGO) hbudget

/-- Divisibility on a line from the mixed orders and the fixed-size determinant. -/
theorem line_resultant_order (F G : GenericX[X][X]) (z : GenericX)
    (hF : F.natDegree ≤ 70000) (hG : G.natDegree ≤ 70000)
    (hFO : ∀ i j, 7800 * i + 49139 * j < firstOrder →
      ((F.taylor (Polynomial.C z)).coeff i).coeff j = 0)
    (hGO : ∀ i j, 7800 * i + 49139 * j < secondOrder →
      ((G.taylor (Polynomial.C z)).coeff i).coeff j = 0) :
    (Polynomial.X : GenericX[X]) ^ 41522 ∣ Polynomial.resultant F G 70000 70000 := by
  exact resultant_bound F G z (m := 70000) (n := 70000) (D := 41522)
    hF hG hFO hGO benchmark_budget

end P0_9_4
end PackSource_P0_9_4Local

section PackSource_P0_9_4Resultant
set_option autoImplicit true
namespace P0_9_4
noncomputable section

open K1_13 K1_13_4 Polynomial
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
    ∀ i j, 7800 * i + 49139 * j < d →
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
  have hweight : mixedWeight (a.optionElim i) = 7800 * i + 49139 * j := by
    change 7800 * a.optionElim i none + 49139 * (a.optionElim i).some.degree = _
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

/-- Multiplication by the padding preserves all required mixed orders. -/
theorem mixedOrder_pad {F : GenericRow} {z : GenericX} {y : Fin 3 → GenericX}
    {d : ℕ} (a : Geom[X]) (h : MixedOrder F z y d) :
    MixedOrder (pad F a) z y d := by
  classical
  intro m hm
  rw [pad, map_mul] at hm
  obtain ⟨u, hu, v, _, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [mixedWeight_add]; exact Nat.le_add_right _ _)

/-- Detect the ordinary order from restrictions to lines in the three jets. -/
theorem resultant_order (F G : GenericRow) (z : GenericX)
    (y : Fin 3 → GenericX) (hF : (asSeedPoly F).natDegree ≤ 70000)
    (hG : (asSeedPoly G).natDegree ≤ 70000) (h : PairOrders F G z y) :
    LowerOrder (seedResultant F G) y 41522 := by
  apply order_of_rays
  intro v
  rw [← line_resultant F G y v]
  exact line_resultant_order _ _ z (natDegree_map_le.trans hF) (natDegree_map_le.trans hG)
    (line_order F z y v _ h.1) (line_order G z y v _ h.2)

end
end P0_9_4
end PackSource_P0_9_4Resultant

section PackSource_P0_9_4Locator
set_option autoImplicit true
namespace P0_9_4

noncomputable section

open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators

set_option maxRecDepth 12000

/-- Substitute the raw jets along a line of polynomial paths. -/
private def line (Q : Row 3) (T U : Geom[X]) : Polynomial Geom[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X) Q

private def Bounded (F : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (F.coeff j).natDegree ≤ b + 49139 * j

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
    (hQ : RawCut t Q) (hT : T.natDegree ≤ 131071) (hU : U.natDegree ≤ 180210)
    (j : ℕ) : ((line Q T U).coeff j).natDegree ≤ t + 49139 * j := by
  let b (i : Fin 3) : ℕ := 131071 - i.val
  let F (i : Fin 3) : Polynomial Geom[X] :=
    Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 3) : Bounded (F i) (b i) := by
    intro k
    have ht : (jet T i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT _)
    have hu : (jet U i).natDegree ≤ b i + 49139 := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 180210 - i.val ≤ (131071 - i.val) + 49139
      omega
    change ((F i).coeff k).natDegree ≤ b i + 49139 * k
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

private theorem eval_line (Q : Row 3) (T U : Geom[X]) (c : Geom) :
    (line Q T U).eval (Polynomial.C c) = atJet Q (T + c • U) := by
  change (evalRingHom (Polynomial.C c))
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X) Q) = _
  rw [MvPolynomial.hom_eval₂]
  have hC : (evalRingHom (C c)).comp C = RingHom.id Geom[X] := RingHom.ext fun p => by simp
  rw [hC]
  change MvPolynomial.eval _ Q = MvPolynomial.eval (jet (T + c • U)) Q
  have heq : (fun i : Fin 3 => (evalRingHom (C c))
      (Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X)) =
      jet (T + c • U) := by
    funext i
    simp only [coe_evalRingHom, eval_mul, eval_C, eval_X, jet, map_add]
    rw [(hasseDeriv i.val).map_smul, Algebra.smul_def, algebraMap_eq, mul_comm]
  rw [heq]

private theorem swapped_coeff (F : Polynomial Geom[X]) (i j : ℕ) :
    ((Bivariate.swap F).coeff i).coeff j = (F.coeff j).coeff i := by
  induction F using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial m c =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]

/-- Taylor coefficients below the contact order vanish as parameter polynomials. -/
private theorem coeff_contact (F : Polynomial Geom[X]) (x : Geom) (r : ℕ)
    (h : ∀ c : Geom, (Polynomial.X - C x) ^ r ∣ F.eval (C c)) (j : ℕ) :
    (Polynomial.X - C x) ^ r ∣ F.coeff j := by
  let f : Geom[X] →+* Geom[X] := (taylorAlgHom x).toRingHom
  let A := F.map f
  have heval (c : Geom) : A.eval (C c) = taylor x (F.eval (C c)) := by
    change (F.map f).eval (C c) = f (F.eval (C c))
    have hC : f (C c) = C c := taylor_C _ _
    rw [← hC, eval_map, eval₂_at_apply]
    rw [hC]
  have hzero (i : ℕ) (hi : i < r) : (Bivariate.swap A).coeff i = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hz (c : Geom) : ((Bivariate.swap A).coeff i).eval c = 0 := by
      have hs : (Bivariate.swap A).map (evalRingHom c) = A.eval (C c) := by
        simpa [Polynomial.aeval_def] using (Bivariate.aveal_eq_map_swap c A).symm
      change evalRingHom c ((Bivariate.swap A).coeff i) = 0
      rw [← Polynomial.coeff_map, hs, heval]
      exact X_pow_dvd_iff.mp ((X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mpr (h c)) i hi
    simpa [IsRoot, hz] using (Set.infinite_univ : (Set.univ : Set Geom).Infinite)
  apply (X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mp
  apply X_pow_dvd_iff.mpr
  intro i hi
  change (f (F.coeff j)).coeff i = 0
  rw [← Polynomial.coeff_map, ← swapped_coeff, hzero i hi, Polynomial.coeff_zero]

/-- Each surviving parameter coefficient must vanish by contact at the selected hits. -/
private theorem line_coeff_zero (w : I → K) (H res T : Geom[X]) (t r : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071) (hQ : RawCut t Q) (hcontact : RawContact r w H res Q)
    (A : Finset I) (hA : A.card = 180208)
    (hhit : ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 2) (j : ℕ) (hj : t + 49139 * j < r * 180208) :
    (line Q T (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 180210 :=
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


/-- Multiplication by the locator is invertible in the local three-jet ring
away from its roots. Reduce the inverse times the target to degree at most two. -/
private theorem exists_direction (L : Geom[X]) (x : Geom) (hx : L.eval x ≠ 0)
    (v : Fin 3 → Geom) :
    ∃ V : Geom[X], V.natDegree ≤ 2 ∧ ∀ i : Fin 3, (jet (L * V) i).eval x = v i := by
  classical
  let B := (Polynomial.X - C x) ^ 3
  have hB : B.Monic := (monic_X_sub_C x).pow _
  have hdeg : B.natDegree = 3 := by simp [B, natDegree_pow]
  have hcop : IsCoprime L B := by
    apply (irreducible_X_sub_C x).coprime_pow_of_not_dvd
    simpa [dvd_iff_isRoot, IsRoot] using hx
  obtain ⟨a, b, hab⟩ := hcop
  let F := taylor (-x) (ofFn 3 v)
  let V := (a * F) %ₘ B
  have hdiv : B ∣ L * V - F := by
    refine ⟨-(b * F + L * ((a * F) /ₘ B)), ?_⟩
    dsimp only [V]
    rw [modByMonic_eq_sub_mul_div]
    linear_combination F * hab
  have hjet := (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (L * V - F) x 3).mp hdiv
  refine ⟨V, ?_, fun i => ?_⟩
  · have hne : B ≠ 1 := by
      intro h
      rw [h, natDegree_one] at hdeg
      omega
    have hsmall := natDegree_modByMonic_lt (a * F) hB hne
    rw [hdeg] at hsmall
    exact Nat.le_of_lt_succ hsmall
  · have h := hjet i.val i.isLt
    rw [map_sub, eval_sub, sub_eq_zero] at h
    change (hasseDeriv i.val (L * V)).eval x = v i
    rw [h, ← taylor_coeff, show F = taylor (-x) (ofFn 3 v) from rfl, taylor_taylor,
      add_neg_cancel, taylor_zero, ofFn_coeff_eq_val_of_lt v i.isLt]

/-- Along a scalar line through the origin, the coefficient at degree j
is the degree-j homogeneous component evaluated at the direction. -/
private theorem coeff_line_through_zero (P : MvPolynomial (Fin 3) Geom) (v : Fin 3 → Geom) (j : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff j =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent j P) := by
  classical
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff, MvPolynomial.homogeneousComponent_apply]
  change _ = MvPolynomial.eval₂Hom (RingHom.id _) v _
  rw [map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow Polynomial.C,
    ← map_prod Polynomial.C, ← map_mul Polynomial.C, ← mul_assoc, Finset.prod_pow_eq_pow_sum,
    Polynomial.coeff_C_mul_X_pow, RingHom.id_apply, Finsupp.degree_apply]
  split_ifs <;> simp_all

private theorem line_at_abscissa (P : Row 3) (S U : Geom[X]) (x : Geom) :
    (line P S U).map (evalRingHom x) =
      MvPolynomial.eval₂ Polynomial.C (fun i : Fin 3 => Polynomial.C ((jet U i).eval x) *
        Polynomial.X) (MvPolynomial.map (evalRingHom x) (shiftJet P S)) := by
  let f := evalRingHom x
  let g (i : Fin 3) : Geom[X] := Polynomial.C (f (jet U i)) * Polynomial.X
  change (mapRingHom f) (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 3 => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) =
    MvPolynomial.eval₂Hom Polynomial.C g
      (MvPolynomial.map f (MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P))
  rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂Hom_map_hom]
  change _ = MvPolynomial.eval₂Hom (Polynomial.C.comp f) g
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P)
  rw [MvPolynomial.map_eval₂Hom]
  have hl : (mapRingHom f).comp Polynomial.C = Polynomial.C.comp f := RingHom.ext fun p => by simp
  have hr : (MvPolynomial.eval₂Hom (Polynomial.C.comp f) g).comp MvPolynomial.C =
      Polynomial.C.comp f := RingHom.ext fun p => by simp
  rw [hl, hr]
  congr 1
  funext i
  simp [g, add_comm]

private theorem order_of_locator_lines (P : Row 3) (S L : Geom[X]) (hL : L ≠ 0) (d : ℕ)
    (h : ∀ (V : Geom[X]), V.natDegree ≤ 2 → ∀ j < d, (line P S (L * V)).coeff j = 0) :
    OrderAt P S d := by
  intro m hm
  change d ≤ m.degree
  by_contra! hlt
  have hz (x : Geom) (hx : L.eval x ≠ 0) : ((shiftJet P S).coeff m).eval x = 0 := by
    let A := MvPolynomial.map (evalRingHom x) (shiftJet P S)
    let Q := MvPolynomial.homogeneousComponent m.degree A
    have hQ : Q = 0 := by
      apply (MvPolynomial.homogeneousComponent_isHomogeneous _ _).eq_zero_of_forall_eval_eq_zero
      intro v
      obtain ⟨V, hV, hv⟩ := exists_direction L x hx v
      have heval := congrArg (evalRingHom x) (h V hV m.degree hlt)
      rw [map_zero, ← Polynomial.coeff_map, line_at_abscissa] at heval
      let along (u : Fin 3 → Geom) :=
        (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (u i) * Polynomial.X) A).coeff
          m.degree
      have hdir := congrArg along (funext hv)
      have hvanish : along v = 0 := hdir.symm.trans heval
      simpa only [along, coeff_line_through_zero] using hvanish
    have hcoeff := congrArg (fun F : MvPolynomial (Fin 3) Geom => F.coeff m) hQ
    simpa [Q, MvPolynomial.coeff_homogeneousComponent, A, MvPolynomial.coeff_map]
      using hcoeff
  have hzero : (shiftJet P S).coeff m = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine (finite_setOfPred_isRoot hL).infinite_compl.mono ?_
    intro x hx
    exact hz x hx
  exact MvPolynomial.mem_support_iff.mp hm hzero

private theorem translate_map (Q : Row 3) (T : Geom[X]) :
    K1_13_4.translate (trajectory T) (MvPolynomial.map inclX Q) =
      MvPolynomial.map inclX (shiftJet Q T) := by
  let left := (K1_13_4.translate (trajectory T)).comp (MvPolynomial.map inclX)
  let right := (MvPolynomial.map inclX).comp (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin 3 => MvPolynomial.X i + MvPolynomial.C (jet T i)))
  have h : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, K1_13_4.translate]
    · intro i
      simp [left, right, K1_13_4.translate, trajectory]
  exact DFunLike.congr_fun h Q

/-- Locator multiplicity in the raw quotient jets at one regular marked seed. -/
theorem raw_locator_order (w : I → K) (H res T : Geom[X]) (t k : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071)
    (hhits : ∃ A : Finset I, 180208 ≤ A.card ∧
      ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (hc : RawContact 5000 w H res Q) (hQ : RawCut t Q)
    (hcut : t + 49139 * k < 5000 * 180208) :
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
end P0_9_4
end PackSource_P0_9_4Locator

section PackSource_P0_9_4Split
set_option autoImplicit true
namespace P0_9_4

noncomputable section

open K1 K1_13 K1_13_4 K1_13_4_3
open scoped Polynomial BigOperators

/-- A nonzero first source and the retuned rank of the second true-jet bank. -/
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2480 →
    (∃ F, F ≠ 0 ∧ Source w P L firstBox firstCut F) ∧
    HasRank w P L secondBox secondCut bankRank

/-- Select the second row in the complete cutoff span and bound its common factors
with the first row, including exclusion of moving factors in the top jet. -/
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow),
    F ≠ 0 → Caps firstBox F → HasRank w P L secondBox secondCut bankRank →
    ∃ G, G ∈ Necessary w P L ∧ Nonempty (CommonPair (toGeneric F) (toGeneric G))

private theorem coeff_eq_zero_of_lowerOrder {F : Lower} {x : Fin 3 → GenericX}
    {d : ℕ} (h : LowerOrder F x d) (a : Fin 3 →₀ ℕ) (ha : a.degree < d) :
    (K1_13_4.translate x F).coeff a = 0 := by
  by_contra hz
  exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))

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
    {w Γ s} (hw : P0_9.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (k : ℕ) (hk : t + 49139 * k < 5000 * 180208) :
    LowerOrder (atSeed (inclConst (P.z γ)) (toGeneric F))
      (trajectory (extend (s γ))) (k + 1) := by
  let res := residueAt L.numerator L.denominator (P.z γ)
  obtain ⟨Q, hQ, hrestore⟩ := h2 w Γ s P L box t F hF γ hγ
  obtain ⟨T, hT, hST⟩ := L.quotient γ hγ
  change extend (s γ) = P.H * T + res at hST
  obtain ⟨A, hA, hhits⟩ := hw.hits γ hγ
  have hhit : ∃ B : Finset I, 180208 ≤ B.card ∧
      ∀ i ∈ B, (P.H * T + res).eval (embed (node i)) = embed (w i) := by
    refine ⟨A, hA, fun i hi => ?_⟩
    rw [← hST, extend, Polynomial.eval_map, Polynomial.eval₂_at_apply, hhits i hi]
  have hcontact := rawContact_of_restore 5000 w P.H res (P.z γ) (box.b + box.j) F Q
    P.nodes hF.2.2.1 hrestore
  have ho := raw_locator_order w P.H res T t k Q hT hhit hcontact hQ hk
  rw [hST]
  exact trueOrder_of_raw P.H res T (P.z γ) (box.b + box.j) (k + 1) F Q
    P.monic.ne_zero hrestore ho

private theorem source_order (h1 : K1_13_4_3.c1) (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : P0_9.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    {d : ℕ} (hd : t + d ≤ 5000 * 180208) :
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
  have hlt : t + 7800 * m none + 49139 * m.some.degree < 5000 * 180208 := by
    change 7800 * m none + 49139 * m.some.degree < d at hm
    omega
  have hD := h1 w Γ s P L box t F hF (m none)
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

private theorem source_orders (w : I → K) (Γ : Finset K) (s : K → K[X])
    (hw : P0_9.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P) :
    (∀ F, Source w P L firstBox firstCut F → ∀ γ ∈ Γ,
      MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstOrder) ∧
    (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
      MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondOrder) := by
  let h1 := K1_13_4_3_1.proof
  let h2 := K1_13_4_3_2.proof
  constructor
  · intro F hF γ hγ
    exact source_order h1 h2 hw P L hF hγ (by decide)
  · intro G hG γ hγ
    let z := inclConst (P.z γ)
    let y := trajectory (extend (s γ))
    change MixedOrder (toGeneric G) z y secondOrder
    change G ∈ Submodule.span Geom _ at hG
    induction hG using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨t, F, a, hF, ht, rfl⟩ := hQ
      apply mixedHasse_order
      apply source_order h1 h2 hw P L hF hγ
      change t + mixedWeight a ≤ 5000 * 180208 - 2769994 at ht
      change t + (2769994 + mixedWeight a) ≤ 5000 * 180208
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


private theorem inclX_injective_P0_9_4Split : Function.Injective inclX :=
  IsFractionRing.injective Geom[X] GenericX

private theorem eval_cleared {Q : Row 3} {R : Lower} {d : Geom[X]}
    (hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R) (S : Geom[X])
    (hR : MvPolynomial.eval (trajectory S) R = 0) : atJet Q S = 0 := by
  have hcomm : inclX (atJet Q S) =
      MvPolynomial.eval (trajectory S) (MvPolynomial.map inclX Q) := by
    rw [atJet, MvPolynomial.eval_map]
    exact MvPolynomial.eval₂_comp inclX (jet S) Q
  apply inclX_injective_P0_9_4Split
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
  exact ha (inclX_injective_P0_9_4Split (hcoeff.trans (map_zero _).symm))

private theorem lowerOrder_weaken {F : Lower} {y : Fin 3 → GenericX} {a b : ℕ}
    (hab : a ≤ b) (h : LowerOrder F y b) : LowerOrder F y a :=
  fun m hm => hab.trans (h m hm)

set_option maxRecDepth 2400 in
theorem of_children (h1 : c1) (h2 : c2) : P0_9.c4 := by
  intro w Γ s hw Pnew
  let P := asOldPole Pnew
  obtain ⟨L⟩ := K1_13_4_1.proof Γ s P
  obtain ⟨⟨F, neF, hF⟩, rank2⟩ := h1 w Γ s P L Pnew.small.2
  obtain ⟨vanishes1, vanishes2⟩ := source_orders w Γ s hw P L
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
  have totalQ : Q'.totalDegree ≤ 6300 := by
    simpa only [MvPolynomial.totalDegree, suppQ] using htQ
  have indexQ : indexDegree Q' ≤ 2403 := by
    simpa only [K1_13.indexDegree, lowerIndex, suppQ] using hiQ
  have totalR : R'.totalDegree ≤ 952630000 := by
    have htR : R.totalDegree ≤ 952630000 := J.total
    simpa only [MvPolynomial.totalDegree, suppR] using htR
  have indexR : indexDegree R' ≤ 322000000 := by
    have hiR : lowerIndex R ≤ 322000000 := J.index
    simpa only [K1_13.indexDegree, lowerIndex, suppR] using hiR
  refine ⟨book, ⟨Q', R', neQ, neR, totalQ, indexQ, totalR, indexR⟩, hcard, ?_⟩
  intro γ hγ hb
  rcases hcover γ hγ hb with he | ho
  · exact Or.inl (eval_cleared mapQ _ he)
  · refine Or.inr (order_cleared mapR _ ?_)
    have hres : LowerOrder R (trajectory (extend (s γ))) 41522 :=
      resultant_order (pad D.left J.a) (pad D.right J.b) (inclConst (P.z γ)) _
        J.degree_left.le J.degree_right.le ⟨mixedOrder_pad J.a ho.1, mixedOrder_pad J.b ho.2⟩
    exact lowerOrder_weaken (by decide : 41481 ≤ 41522) hres

end
end P0_9_4
end PackSource_P0_9_4Split

section PackSource_P0_9_4_1Defs
set_option autoImplicit true
namespace P0_9_4_1

open K1_13_4_2 (Bank)

def cut : Bank → ℕ
  | .first => P0_9_4.firstCut
  | .second => P0_9_4.secondCut

def targetRank : Bank → ℕ
  | .first => 1
  | .second => P0_9_4.bankRank

theorem cut_large (b : Bank) : 131071 * b.box.b ≤ cut b + 1 := by
  cases b <;> decide

def rawBase (b : Bank) : ℕ := cut b + 1 - 131071 * b.box.b

/-- Inclusive X width in the retuned bank, using the deficit from the total jet cap. -/
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h

end P0_9_4_1
end PackSource_P0_9_4_1Defs

section PackSource_P0_9_4_1Columns
set_option autoImplicit true
namespace P0_9_4_1

open K1 K1_13 K1_13_4 K1_13_4_2
open K1_13_4_2_1 (box_index jetSum)
open scoped BigOperators Polynomial
noncomputable section

set_option backward.isDefEq.respectTransparency false

private abbrev Column (b : Bank) (h : ℕ) :=
  Σ q : Fin (b.box.b + 1), Σ k : Fin (min q.val 1150 + 1),
    Σ l : Fin (min (q.val - k.val) (2300 - 2 * k.val) + 1),
      Fin (width b h q.val k.val l.val) × Fin 70001

private def exponent (u i l k : ℕ) : SeedVar →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => j.elim u (![i, l, k] ·))

@[simp] private theorem exponent_none (u i l k : ℕ) : exponent u i l k none = u := by
  simp [exponent]

@[simp] private theorem exponent_zero (u i l k : ℕ) : exponent u i l k (some 0) = i := by
  simp [exponent]

@[simp] private theorem exponent_one (u i l k : ℕ) : exponent u i l k (some 1) = l := by
  simp [exponent]

@[simp] private theorem exponent_two (u i l k : ℕ) : exponent u i l k (some 2) = k := by
  simp [exponent]

private def colExp {b : Bank} {h : ℕ} (c : Column b h) : SeedVar →₀ ℕ :=
  exponent c.2.2.2.2.val (c.1.val - c.2.1.val - c.2.2.1.val) c.2.2.1.val c.2.1.val

private def colX {b : Bank} {h : ℕ} (c : Column b h) : ℕ := c.2.2.2.1.val

private theorem column_injective (b : Bank) (h : ℕ) :
    Function.Injective (fun c : Column b h => (colExp c, colX c)) := by
  rintro ⟨q,k,l,x,u⟩ ⟨q',k',l',x',u'⟩ he
  have he₀ := congrArg (fun p : (SeedVar →₀ ℕ) × ℕ => p.1 (some 0)) he
  have he₁ := congrArg (fun p : (SeedVar →₀ ℕ) × ℕ => p.1 (some 1)) he
  have he₂ := congrArg (fun p : (SeedVar →₀ ℕ) × ℕ => p.1 (some 2)) he
  have heu := congrArg (fun p : (SeedVar →₀ ℕ) × ℕ => p.1 none) he
  have hex := congrArg Prod.snd he
  simp only [colExp, colX, exponent_zero, exponent_one, exponent_two, exponent_none] at *
  have hk := k.isLt
  have hl := l.isLt
  have hk' := k'.isLt
  have hl' := l'.isLt
  simp only [Nat.lt_succ_iff, le_min_iff] at hk hl hk' hl'
  have hq : q = q' := Fin.ext (by omega)
  subst q'
  have hkk : k = k' := Fin.ext he₂
  subst k'
  have hll : l = l' := Fin.ext he₁
  subst l'
  have hxx : x = x' := Fin.ext hex
  have huu : u = u' := Fin.ext heu
  subst x'
  subst u'
  rfl

private def coordinate (e : SeedVar →₀ ℕ) (x : ℕ) : PhysicalRow →ₗ[Geom] Geom :=
  (Polynomial.lcoeff Geom x).comp ((MvPolynomial.lcoeff Geom[X] e).restrictScalars Geom)

private def column {b : Bank} {h : ℕ} (c : Column b h) : PhysicalRow :=
  MvPolynomial.monomial (colExp c) (Polynomial.monomial (colX c) 1)

private theorem coordinate_column {b : Bank} {h : ℕ} (c : Column b h)
    (e : SeedVar →₀ ℕ) (x : ℕ) :
    coordinate e x (column c) = if colExp c = e ∧ colX c = x then 1 else 0 := by
  classical
  change ((column c).coeff e).coeff x = _
  by_cases he : colExp c = e <;> simp [column, he, Polynomial.coeff_monomial]

private theorem column_li (b : Bank) (h : ℕ) :
    LinearIndependent Geom (column (b := b) (h := h)) := by
  classical
  let L : PhysicalRow →ₗ[Geom] (Column b h → Geom) :=
    LinearMap.pi (fun c : Column b h => coordinate (colExp c) (colX c))
  apply LinearIndependent.of_comp L
  have he : L ∘ column = (Pi.basisFun Geom (Column b h) : Column b h → Column b h → Geom) := by
    funext c d
    rw [Function.comp_apply, Pi.basisFun_apply, Pi.single_apply]
    change coordinate (colExp d) (colX d) (column c) = _
    simp only [coordinate_column, ← Prod.mk.injEq, (column_injective b h).eq_iff, eq_comm]
  rw [he]
  exact (Pi.basisFun Geom (Column b h)).linearIndependent

private def space (b : Bank) (h : ℕ) : Submodule Geom PhysicalRow :=
  Submodule.span Geom (Set.range (column (b := b) (h := h)))

private theorem occurs_in_column {b : Bank} {h : ℕ} {F : PhysicalRow}
    (hF : F ∈ space b h) {e : SeedVar →₀ ℕ} {x : ℕ} (hne : (F.coeff e).coeff x ≠ 0) :
    ∃ c : Column b h, colExp c = e ∧ colX c = x := by
  classical
  by_contra! hn
  have hle : space b h ≤ LinearMap.ker (coordinate e x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change coordinate e x (column c) = 0
    rw [coordinate_column, ite_eq_right]
    exact fun hc => (hn c hc.1 hc.2).elim
  exact hne (LinearMap.mem_ker.mp (hle hF))

private theorem column_bounds {b : Bank} {h : ℕ} (c : Column b h) :
    let e := colExp c
    Finsupp.weight (fun i : SeedVar => i.elim 0 (fun _ => 1)) e ≤ b.box.b ∧
    Finsupp.weight (fun i : SeedVar => i.elim 0 Fin.val) e ≤ b.box.j ∧
    e (some 2) ≤ b.box.t ∧ e none ≤ 70000 ∧
    colX c + e.sum (fun i n => i.elim 0 (fun j => (131071 + h - j.val) * n)) ≤
      cut b + (b.box.b + b.box.j) * h := by
  rcases c with ⟨q,k,l,x,u⟩
  have hq := q.isLt
  have hk := k.isLt
  have hl := l.isLt
  have hx := x.isLt
  have hu := u.isLt
  simp only [Nat.lt_succ_iff, le_min_iff] at hq hk hl
  have hs : q.val - k.val - l.val + l.val + k.val = q.val := by omega
  have hi : l.val + 2 * k.val ≤ 2300 := by omega
  have hraw : rawBase b + 131071 * b.box.b = cut b + 1 := by
    unfold rawBase
    have := cut_large b
    omega
  have hcredit : (2300 + (b.box.b - q.val)) * h + h * q.val = (b.box.b + 2300) * h := by
    rw [mul_comm h q.val, ← Nat.add_mul]
    congr 1
    omega
  have hweight :
      (131071 + h - 0) * (q.val - k.val - l.val) +
        (131071 + h - 1) * l.val + (131071 + h - 2) * k.val + (l.val + 2 * k.val) =
      131071 * q.val + h * q.val := by
    have h₁ : 131071 + h - 1 + 1 = 131071 + h := by omega
    have h₂ : 131071 + h - 2 + 2 = 131071 + h := by omega
    calc
      _ = (131071 + h) * (q.val - k.val - l.val) +
          (131071 + h - 1 + 1) * l.val + (131071 + h - 2 + 2) * k.val := by
        simp only [Nat.sub_zero]
        ring
      _ = _ := by rw [h₁, h₂, ← Nat.mul_add, ← Nat.mul_add, hs, Nat.add_mul]
  have hsum :
      (exponent u.val (q.val - k.val - l.val) l.val k.val).sum
        (fun i n => i.elim 0 (fun j => (131071 + h - j.val) * n)) =
      (131071 + h - 0) * (q.val - k.val - l.val) +
        (131071 + h - 1) * l.val + (131071 + h - 2) * k.val := by
    rw [Finsupp.sum_fintype _ _ (fun i => by cases i <;> simp),
      Fintype.sum_option, Fin.sum_univ_three]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option, Fin.sum_univ_succ,
      colExp, smul_eq_mul, ← Nat.add_assoc, hs] using hq
  · simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option, Fin.sum_univ_succ,
      colExp, smul_eq_mul, Nat.mul_comm] using hi
  · simpa [colExp] using hk.2
  · simpa [colExp] using Nat.le_of_lt_succ hu
  · change x.val + (exponent u.val (q.val - k.val - l.val) l.val k.val).sum
      (fun i n => i.elim 0 (fun j => (131071 + h - j.val) * n)) ≤
        cut b + (b.box.b + b.box.j) * h
    rw [hsum, box_index]
    change x.val < width b h q.val k.val l.val at hx
    unfold width at hx
    omega

private theorem space_bounds (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ space b h) :
    Caps b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F := by
  have he (e : SeedVar →₀ ℕ) (hm : e ∈ F.support) :
      ∃ c : Column b h, colExp c = e ∧ colX c = (F.coeff e).natDegree := by
    exact occurs_in_column hF (by
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact MvPolynomial.mem_support_iff.mp hm)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · apply Finset.sup_le
    intro e hm
    obtain ⟨c, rfl, _⟩ := he e hm
    exact (column_bounds c).1
  · apply Finset.sup_le
    intro e hm
    obtain ⟨c, rfl, _⟩ := he e hm
    exact (column_bounds c).2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e hm
    obtain ⟨c, rfl, _⟩ := he e hm
    exact (column_bounds c).2.2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e hm
    obtain ⟨c, rfl, _⟩ := he e hm
    exact (column_bounds c).2.2.2.1
  · intro e hm
    obtain ⟨c, rfl, hx⟩ := he e hm
    rw [← hx]
    exact (column_bounds c).2.2.2.2

/-- The true ambient space, with the full independent seed cap. -/
theorem ambient (b : Bank) (h : ℕ) :
    ∃ V : Submodule Geom PhysicalRow, Module.Finite Geom V ∧
      (∀ F ∈ V, Caps b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F) ∧
      Module.finrank Geom V = 70001 * jetSum b.box.b (width b h) := by
  refine ⟨space b h, Module.Finite.span_of_finite _ (Set.finite_range _), space_bounds b h, ?_⟩
  rw [space, finrank_span_eq_card (column_li b h)]
  simp only [Column, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
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
end P0_9_4_1
end PackSource_P0_9_4_1Columns

section PackSource_P0_9_4_1Arithmetic
set_option autoImplicit true
namespace P0_9_4_1

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

/-- Certify the two retuned raw volumes using the old symbolic moment formula.
Each of the five slices is a polynomial evaluation at one literal argument. -/
private theorem first_raw : rawVolume .first = 2821190095054679460 := by
  change moment 6789 5452627 1 131071 0 = _
  refine moment_eq 6789 5452627 1 131071 0 _ (by decide) ?_
  change antidifference (slice 6789 5452627 1 131071 0) 1151 = _
  have h0 : slice 6789 5452627 1 131071 0 0 = 710389155829008240 := by decide
  have h1 : slice 6789 5452627 1 131071 0 1 = 709755063171620400 := by decide
  have h2 : slice 6789 5452627 1 131071 0 2 = 709121013902162784 := by decide
  have h3 : slice 6789 5452627 1 131071 0 3 = 708487007982887520 := by decide
  have h4 : slice 6789 5452627 1 131071 0 4 = 707853045376046736 := by decide
  unfold antidifference
  rw [h0, h1, h2, h3, h4]
  decide

private theorem second_raw : rawVolume .second = 2843689204984221187 := by
  change moment 6820 4365787 1 131071 0 = _
  refine moment_eq 6820 4365787 1 131071 0 _ (by decide) ?_
  change antidifference (slice 6820 4365787 1 131071 0) 1151 = _
  have h0 : slice 6820 4365787 1 131071 0 0 = 716016370683461328 := by decide
  have h1 : slice 6820 4365787 1 131071 0 1 = 715377386932594848 := by decide
  have h2 : slice 6820 4365787 1 131071 0 2 = 714738446569640736 := by decide
  have h3 : slice 6820 4365787 1 131071 0 3 = 714099549556851120 := by decide
  have h4 : slice 6820 4365787 1 131071 0 4 = 713460695856478128 := by decide
  unfold antidifference
  rw [h0, h1, h2, h3, h4]
  decide

private theorem endpoint (b : Bank) :
    targetRank b + 262144 * (70001 * b.nodeRank) + 2480 * extra b.box.b ≤
      70001 * rawVolume b := by
  obtain ⟨_, _, hfirst, hsecond⟩ := bank_moments
  cases b
  · have he : extra Bank.first.box.b = 129644787051371740 := hfirst
    have ha : (1 : ℕ) + 262144 * (70001 * 10697571688375) + 2480 * 129644787051371740 ≤
        70001 * 2821190095054679460 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.first + 262144 * (70001 * Bank.first.nodeRank) + 2480 * x ≤ 70001 * y)
      he first_raw).mpr ha
  · have he : extra Bank.second.box.b = 131501361258434295 := hsecond
    have ha : (2426980608909015050627 : ℕ) + 262144 * (70001 * 10697783317215) +
        2480 * 131501361258434295 ≤ 70001 * 2843689204984221187 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.second + 262144 * (70001 * Bank.second.nodeRank) + 2480 * x ≤ 70001 * y)
      he second_raw).mpr ha

/-- Cancel the height credit before charging the remaining simple-pole debit. -/
theorem budget (b : Bank) (h : ℕ) (hh : h ≤ 2480) :
    targetRank b + 262144 * (70001 * b.nodeRank) + h * poleDebit b.box ≤
      70001 * jetSum b.box.b (width b h) := by
  have he := endpoint b
  have hm := Nat.mul_le_mul_right (extra b.box.b) hh
  rw [pole_eq, volume_eq, Nat.mul_add, Nat.mul_add]
  have hc : h * (70001 * credit b.box.b) = 70001 * (credit b.box.b * h) := by ring
  omega

end P0_9_4_1
end PackSource_P0_9_4_1Arithmetic

section PackSource_P0_9_4_1Proof
set_option autoImplicit true
namespace P0_9_4_1

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
    (P : PoleData Γ s) (L : ResidueChart P) (hh : P.H.natDegree ≤ 2480) :
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

theorem proof : P0_9_4.c1 := by
  intro w Γ s P L hh
  refine ⟨?_, rank_of_bounds .second w P L hh⟩
  obtain ⟨e, he, hsource⟩ := rank_of_bounds .first w P L hh
  let i : Fin (targetRank Bank.first) := ⟨0, by decide⟩
  exact ⟨e i, he.ne_zero i, hsource i⟩

end
end P0_9_4_1
end PackSource_P0_9_4_1Proof

section PackSource_P0_9_4_2Filtration
set_option autoImplicit true
namespace P0_9_4_2
noncomputable section

open Polynomial K1 K1_13
open K1_13_4 (ResidueChart PhysicalRow GenericX GenericRow HasRank Source secondBox toGeneric)
open K1_13_4_4 (layerSpan)
open K1_13_4_4_1 (Exponent)
open P0_9_4 (secondCut bankRank)
open scoped BigOperators

open private bank bankEval mem_bank K1_13_4_4_1.kernel_le boundary below_boundary independent_generic
  from ProximityPrize.SubmissionLower.Fast050
open private K1_13_4_4_1.endpoint from ProximityPrize.SubmissionLower.Fast074

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The leading coefficient images of the complete spaces pay for the rank at the retuned cutoff. -/
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
end P0_9_4_2
end PackSource_P0_9_4_2Filtration

section PackSource_P0_9_4_2Hasse
set_option autoImplicit true
namespace P0_9_4_2
noncomputable section

open K1_13_4 hiding mixedWeight secondCut
open K1_13_4_4 (FactorsFor factorProduct mixedHasse_zero toGeneric_caps)
open P0_9_4 (mixedWeight secondCut)
open scoped Polynomial BigOperators

open private line line_zero line_toGeneric transverse pow_dvd_of_coeff positive_jet_degree
  from ProximityPrize.SubmissionLower.Fast076

def reserveCost (moving : Bool) : ℕ := if moving then 7800 else 49139

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

/-- A factor tested by all available derivatives divides each source to its charged power. -/
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

end
end P0_9_4_2
end PackSource_P0_9_4_2Hasse

section PackSource_P0_9_4_2Budget
set_option autoImplicit true
namespace P0_9_4_2
noncomputable section

open K1_13_4_4 (topSlots cutoff_sum_le slot_constants)
open P0_9_4 (secondCut bankRank)
open scoped BigOperators

set_option maxRecDepth 1024

theorem factor_arithmetic :
    let T := 525913765916471
    let S := P0_9_4.bankRank
    49139 * 6820 * T / S = 72 ∧ 49139 * 2300 * T / S = 24 ∧
      7800 * 6820 * T / S = 11 ∧ 7800 * 2300 * T / S = 3 ∧
      7800 * 70000 * T / S = 118 ∧ 1571799066189253395000 < S := by
  decide

/-- Each of the nonempty cutoff layers spends d units per copy of the product. -/
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

/-- A common moving factor with positive Y₂ degree would require too many symbols. -/
theorem top_exclusion (r : ℕ → ℕ)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (h : ∀ t ≤ secondCut, r t ≤ topSlots (layerPower 7800 t)) : False := by
  have hb := cutoff_sum_le (W := secondCut) (n := 1150) (by decide : 0 < 7800)
    r (fun k => topSlots (1 + k)) h (fun k hk => by
      have hk' : 1151 - (1 + k) = 0 := by omega
      simp [topSlots, hk'])
  rw [slot_constants.2] at hb
  exact (not_le_of_gt factor_arithmetic.2.2.2.2.2) (hr.trans hb)

end
end P0_9_4_2
end PackSource_P0_9_4_2Budget

section PackSource_P0_9_4_2Gcd
set_option autoImplicit true
namespace P0_9_4_2
noncomputable section

open K1_13_4 hiding CommonPair
open K1_13_4_4 (FactorsFor factorProduct)
open P0_9_4 (CommonPair)
open scoped Polynomial BigOperators

open private pureEval pureEval_section pure_degree_le caps_of_dvd from ProximityPrize.SubmissionLower.Fast050

/-- Package the normalized factorization of the actual common gcd.
The pure factor already has seed degree at most that of the first row. -/
theorem factor_pair
    (F G : GenericRow) (hF : F ≠ 0) (hG : G ≠ 0)
    (hFCap : Caps firstBox F) (hGCap : Caps secondBox G)
    (hfixed : ∀ A, FactorsFor false A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 72 ∧ jetIndex (factorProduct A) ≤ 24)
    (hmoving : ∀ A, FactorsFor true A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 11 ∧ jetIndex (factorProduct A) ≤ 3 ∧
      seedDegree (factorProduct A) ≤ 118 ∧ ∀ f ∈ A, f.degreeOf (some 2) = 0) :
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
end P0_9_4_2
end PackSource_P0_9_4_2Gcd

section PackSource_P0_9_4_2Proof
set_option autoImplicit true
namespace P0_9_4_2
noncomputable section

open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (layerSpan FactorsFor factorProduct topSlots slot_constants rowMap
  capSpace mem_capSpace mixedHasse_zero toGeneric_ne_zero toGeneric_caps mixedHasse_caps layerSpan_caps)
open P0_9_4 (Necessary mixedWeight secondCut bankRank)
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

/-- A single constant linear combination avoids every avoidable factor of F. -/
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
      layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower 7800 t)) :
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
    have hle := Nat.mul_le_mul_left (layerPower 7800 t) (Nat.pos_of_ne_zero hn)
    rw [Nat.mul_one] at hle
    simpa only [v, MvPolynomial.weightedTotalDegree_piSingle] using hle.trans h
  intro f hf
  have hfd : f ∣ factorProduct A := Finset.dvd_prod_of_mem id hf
  have h := (MvPolynomial.weightedTotalDegree_le_of_dvd v hfd (product_ne_zero hA)).trans_eq hzero
  simpa only [v, MvPolynomial.weightedTotalDegree_piSingle, Nat.le_zero] using h

theorem proof : P0_9_4.c2 := by
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
  obtain ⟨bF, jF, bM, jM, sM, _⟩ := factor_arithmetic
  refine ⟨G, hG, factor_pair _ _ (toGeneric_ne_zero hF) (toGeneric_ne_zero hGne)
    (toGeneric_caps hFCaps) (necessary_caps hG) ?_ ?_⟩
  · intro A hA hcomm
    have hbt := hbound false A hA hcomm _ _ hbcap
    have hji := hbound false A hA hcomm _ _ hjcap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    have hbt' : jetTotal (factorProduct A) ≤ 72 := by
      simpa only [reserveCost, Bool.false_eq_true, ite_false, slot_constants.1, bF] using hbt
    have hji' : jetIndex (factorProduct A) ≤ 24 := by
      simpa only [reserveCost, Bool.false_eq_true, ite_false, slot_constants.1, jF] using hji
    exact ⟨hbt', hji'⟩
  · intro A hA hcomm
    have hbt := hbound true A hA hcomm _ _ hbcap
    have hji := hbound true A hA hcomm _ _ hjcap
    have hse := hbound true A hA hcomm _ _ hscap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    rw [MvPolynomial.weightedTotalDegree_piSingle] at hse
    have hbt' : jetTotal (factorProduct A) ≤ 11 := by
      simpa only [reserveCost, ite_true, slot_constants.1, bM] using hbt
    have hji' : jetIndex (factorProduct A) ≤ 3 := by
      simpa only [reserveCost, ite_true, slot_constants.1, jM] using hji
    have hse' : seedDegree (factorProduct A) ≤ 118 := by
      simpa only [seedDegree, reserveCost, ite_true, slot_constants.1, sM] using hse
    exact ⟨hbt', hji', hse', excludes_top hA hr hb (hdiv true A hA hcomm)⟩

end
end P0_9_4_2
end PackSource_P0_9_4_2Proof
