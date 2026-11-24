import ProximityPrize.SubmissionLower.PortLow5
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_4
noncomputable section
open K1 (I K)
open K1_13 (Geom Shape)
open K1_13_4
open scoped Polynomial BigOperators
abbrev firstCut : ℕ := 5000 * P0.agreement - firstOrder
abbrev secondCut : ℕ := 5000 * P0.agreement - secondOrder
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
  fixed_total : jetTotal (∏ f ∈ fixed, f) ≤ 71
  fixed_index : jetIndex (∏ f ∈ fixed, f) ≤ 24
  moving_total : jetTotal (∏ f ∈ moving, f) ≤ 11
  moving_index : jetIndex (∏ f ∈ moving, f) ≤ 3
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 117
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
end
section
namespace P0_9_4
noncomputable section
open K1_13 K1_13_4 MvPolynomial
open scoped Polynomial BigOperators
theorem inclX_injective : Function.Injective inclX :=
  IsFractionRing.injective (Polynomial Geom) GenericX
theorem clear_denominators {σ : Type*} (f : MvPolynomial σ GenericX) :
    ∃ (d : (Polynomial Geom)) (P : MvPolynomial σ (Polynomial Geom)), d ≠ 0 ∧ P.support = f.support ∧
      MvPolynomial.map inclX P = C (inclX d) * f := by
  classical
  let M := nonZeroDivisors ((Polynomial Geom))
  let d := IsLocalization.commonDenom M f.support f.coeff
  let num := IsLocalization.integerMultiple M f.support f.coeff
  let P : MvPolynomial σ (Polynomial Geom) := ∑ a : ↥f.support, monomial a.val (num a)
  have hd : (d : (Polynomial Geom)) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : inclX (d : (Polynomial Geom)) ≠ 0 := (map_ne_zero_iff inclX inclX_injective).mpr hd
  have hP : MvPolynomial.map inclX P = C (inclX d) * f := by
    ext m
    simp only [coeff_map, coeff_C_mul, P, coeff_sum]
    by_cases hm : m ∈ f.support
    · let a : ↥f.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M f.support f.coeff a
        change inclX (num a) = (d : (Polynomial Geom)) • f.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [coeff_monomial, hb]
    · have hz : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥f.support, (monomial a.val (num a) : MvPolynomial σ (Polynomial Geom)).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  refine ⟨d, P, hd, ?_, hP⟩
  rw [← support_map_of_injective P inclX_injective, hP]
  ext m
  simp [MvPolynomial.mem_support_iff, coeff_C_mul, hi]
def coefficientDerivative (P : PhysicalRow) : PhysicalRow :=
  ∑ m ∈ P.support, monomial m (Polynomial.derivative (P.coeff m))
@[simp] theorem coeff_coefficientDerivative (P : PhysicalRow) (m : SeedVar →₀ ℕ) :
    (coefficientDerivative P).coeff m = Polynomial.derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm, map_zero]
private theorem coefficientDerivative_C (c : (Polynomial Geom)) :
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
private theorem eval_chain (P : PhysicalRow) (a : SeedVar → (Polynomial Geom)) :
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
def dotted {R : Type*} [CommRing R] (r P : SeedRow R) : SeedRow R :=
  r + MvPolynomial.X (some 1) * pderiv (some 0) P +
    C (2 : R) * (MvPolynomial.X (some 2) * pderiv (some 1) P)
def polynomialPoint (z : Geom) (S : (Polynomial Geom)) : SeedVar → (Polynomial Geom) :=
  fun i => i.elim (Polynomial.C z) (jet S)
private theorem derivative_hasse (S : (Polynomial Geom)) (k : ℕ) :
    Polynomial.derivative (Polynomial.hasseDeriv k S) =
      Polynomial.C ((k + 1 : ℕ) : Geom) * Polynomial.hasseDeriv (k + 1) S := by
  have h := LinearMap.congr_fun (Polynomial.hasseDeriv_comp (R := Geom) 1 k) S
  simpa [Polynomial.hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul,
    Polynomial.C_eq_natCast, Nat.add_comm, add_mul] using h
theorem eval_dotted (P : PhysicalRow) (z : Geom) (S : (Polynomial Geom))
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
  rw [map_ofNat (Polynomial.C : Geom →+* (Polynomial Geom))]
  ring
theorem eval_map_point (z : Geom) (S : (Polynomial Geom)) (P : PhysicalRow) :
    eval (atPoint (inclConst z) (trajectory S)) (MvPolynomial.map inclX P) =
      inclX (eval (polynomialPoint z S) P) := by
  have hpoint : atPoint (inclConst z) (trajectory S) = inclX ∘ polynomialPoint z S := by
    funext i
    cases i with
    | none => exact RingHom.congr_fun (IsScalarTower.algebraMap_eq Geom (Polynomial Geom) GenericX) z
    | some i => rfl
  rw [hpoint, MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp inclX (polynomialPoint z S) P).symm
theorem degreeOf_le_of_support_subset {P Q : GenericRow} (h : P.support ⊆ Q.support)
    (i : SeedVar) : P.degreeOf i ≤ Q.degreeOf i := by
  apply degreeOf_le_iff.mpr
  intro m hm
  exact le_degreeOf_of_mem_support i (h hm)
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
theorem dotted_weight (w : SeedVar → ℕ) (r P : GenericRow) (d : ℕ)
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
theorem seed_weight (P : GenericRow) :
    P.weightedTotalDegree (Pi.single none 1) = seedDegree P := by
  rw [seedDegree, degreeOf_eq_sup, weightedTotalDegree]
  simp only [Finsupp.weight_single_one_apply]
end
end P0_9_4
end
section
namespace P0_9_4
noncomputable section
open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
set_option maxRecDepth 12000
def line (Q : Row 3) (T U : (Polynomial Geom)) : Polynomial (Polynomial Geom) :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X) Q
theorem eval_line (Q : Row 3) (T U : (Polynomial Geom)) (c : Geom) :
    (line Q T U).eval (Polynomial.C c) = atJet Q (T + c • U) := by
  change (evalRingHom (Polynomial.C c))
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X) Q) = _
  rw [MvPolynomial.hom_eval₂]
  have hC : (evalRingHom (C c)).comp C = RingHom.id (Polynomial Geom) := RingHom.ext fun p => by simp
  rw [hC]
  change MvPolynomial.eval _ Q = MvPolynomial.eval (jet (T + c • U)) Q
  have heq : (fun i : Fin 3 => (evalRingHom (C c))
      (Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X)) =
      jet (T + c • U) := by
    funext i
    simp only [coe_evalRingHom, eval_mul, eval_C, eval_X, jet, map_add]
    rw [(hasseDeriv i.val).map_smul, Algebra.smul_def, algebraMap_eq, mul_comm]
  rw [heq]
private theorem swapped_coeff (F : Polynomial (Polynomial Geom)) (i j : ℕ) :
    ((Bivariate.swap F).coeff i).coeff j = (F.coeff j).coeff i := by
  induction F using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial m c =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]
theorem coeff_contact (F : Polynomial (Polynomial Geom)) (x : Geom) (r : ℕ)
    (h : ∀ c : Geom, (Polynomial.X - C x) ^ r ∣ F.eval (C c)) (j : ℕ) :
    (Polynomial.X - C x) ^ r ∣ F.coeff j := by
  let f : (Polynomial Geom) →+* (Polynomial Geom) := (taylorAlgHom x).toRingHom
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
private theorem exists_direction (L : (Polynomial Geom)) (x : Geom) (hx : L.eval x ≠ 0)
    (v : Fin 3 → Geom) :
    ∃ V : (Polynomial Geom), V.natDegree ≤ 2 ∧ ∀ i : Fin 3, (jet (L * V) i).eval x = v i := by
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
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow (Polynomial.C (R := Geom)),
    ← map_prod (Polynomial.C (R := Geom)), ← map_mul (Polynomial.C (R := Geom)), ← mul_assoc, Finset.prod_pow_eq_pow_sum,
    Polynomial.coeff_C_mul_X_pow, RingHom.id_apply, Finsupp.degree_apply]
  split_ifs <;> simp_all
private theorem line_at_abscissa (P : Row 3) (S U : (Polynomial Geom)) (x : Geom) :
    (line P S U).map (evalRingHom x) =
      MvPolynomial.eval₂ Polynomial.C (fun i : Fin 3 => Polynomial.C ((jet U i).eval x) *
        Polynomial.X) (MvPolynomial.map (evalRingHom x) (shiftJet P S)) := by
  let f := evalRingHom x
  let g (i : Fin 3) : (Polynomial Geom) := Polynomial.C (f (jet U i)) * Polynomial.X
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
theorem order_of_locator_lines (P : Row 3) (S L : (Polynomial Geom)) (hL : L ≠ 0) (d : ℕ)
    (h : ∀ (V : (Polynomial Geom)), V.natDegree ≤ 2 → ∀ j < d, (line P S (L * V)).coeff j = 0) :
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
theorem translate_map (Q : Row 3) (T : (Polynomial Geom)) :
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
end
end P0_9_4
end
section
namespace P0_9_4_1
open K1_13_4_2 (Bank)
def cut : Bank → ℕ
  | .first => P0_9_4.firstCut
  | .second => P0_9_4.secondCut
theorem cut_large (b : Bank) : 131071 * b.box.b ≤ cut b + 1 := by
  cases b <;> decide
def rawBase (b : Bank) : ℕ := cut b + 1 - 131071 * b.box.b
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h
end P0_9_4_1
end
section
namespace P0_9_4_1
open K1 K1_13 K1_13_4 K1_13_4_2
open K1_13_4_2_1 (box_index jetSum)
open scoped BigOperators Polynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev Column (b : Bank) (h : ℕ) :=
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
def colExp {b : Bank} {h : ℕ} (c : Column b h) : SeedVar →₀ ℕ :=
  exponent c.2.2.2.2.val (c.1.val - c.2.1.val - c.2.2.1.val) c.2.2.1.val c.2.1.val
def colX {b : Bank} {h : ℕ} (c : Column b h) : ℕ := c.2.2.2.1.val
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
def coordinate (e : SeedVar →₀ ℕ) (x : ℕ) : PhysicalRow →ₗ[Geom] Geom :=
  (Polynomial.lcoeff Geom x).comp ((MvPolynomial.lcoeff (Polynomial Geom) e).restrictScalars Geom)
def column {b : Bank} {h : ℕ} (c : Column b h) : PhysicalRow :=
  MvPolynomial.monomial (colExp c) (Polynomial.monomial (colX c) 1)
theorem coordinate_column {b : Bank} {h : ℕ} (c : Column b h)
    (e : SeedVar →₀ ℕ) (x : ℕ) :
    coordinate e x (column c) = if colExp c = e ∧ colX c = x then 1 else 0 := by
  classical
  change ((column c).coeff e).coeff x = _
  by_cases he : colExp c = e <;> simp [column, he, Polynomial.coeff_monomial, Finsupp.single_apply]
theorem column_li (b : Bank) (h : ℕ) :
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
def space (b : Bank) (h : ℕ) : Submodule Geom PhysicalRow :=
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
theorem column_bounds {b : Bank} {h : ℕ} (c : Column b h) :
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
theorem space_bounds (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ space b h) :
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
end
end P0_9_4_1
end
