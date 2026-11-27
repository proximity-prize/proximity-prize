import ProximityPrize.SubmissionLower.PortLowBase
import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.UpperBranch3

set_option Elab.async false

-- merged module PortLow5
section Merged_PortLow5
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_5
noncomputable section
open P0 (K I)
open P0_9 (TrueWeightLE anchorCutoff taylorLength)
open K1_13 (Row Shape indexDegree)
open K1_13_5 (NodeFamily lowBox liftedBox graphBox mixed3)
open scoped BigOperators Polynomial
def mixedBudget : ℕ :=
  let a := liftedBox (taylorLength + 1)
  let b := liftedBox (taylorLength + 2)
  mixed3 lowBox a b + (taylorLength - 1) * mixed3 lowBox graphBox b +
    taylorLength * mixed3 lowBox graphBox a
def invariantBudget : ℕ :=
  lowBox.b * (1 + (2 * (taylorLength + 1) - 7) * (lowBox.b - 1))
structure ProperCover (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget
  fresh : invariant.totalCap ≤ invariantBudget
  components : multiple.n + invariant.n ≤ 2 * invariantBudget
end
end P0_9_5
end
section
set_option autoImplicit false
namespace P0_9_5_1_4
noncomputable section
open K1_13_5_4 (GeometricX)
open MvPolynomial
open scoped BigOperators
def restrictVariables {k : Type*} [Field k] {m n : ℕ} :
    Fin n → MvPolynomial (Fin m) k :=
  fun i => if hi : i.val < m then MvPolynomial.X ⟨i.val, hi⟩ else 0
theorem restrict_rename {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
    (p : MvPolynomial (Fin m) k) :
    MvPolynomial.aeval restrictVariables (rename (Fin.castLE h) p) = p := by
  have he : (MvPolynomial.aeval restrictVariables).comp (rename (R := k) (Fin.castLE h)) =
      AlgHom.id k (MvPolynomial (Fin m) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [restrictVariables, i.isLt]
  exact DFunLike.congr_fun he p
theorem padded_hilbert {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
    (Q : Ideal (MvPolynomial (Fin m) k)) :
    affineHilbertPolynomial (Q.comap (MvPolynomial.aeval (R := k)
      (restrictVariables : Fin n → MvPolynomial (Fin m) k))) = affineHilbertPolynomial Q := by
  let r := MvPolynomial.aeval (R := k) (restrictVariables (k := k) (m := m) (n := n))
  let P := Q.comap r
  let s := rename (R := k) (Fin.castLE h)
  have hSQ : Q ≤ P.comap s := by
    intro p hp
    change r (s p) ∈ Q
    rwa [restrict_rename h]
  let g := Ideal.quotientMapₐ Q r (show P ≤ Q.comap r from le_rfl)
  let j := Ideal.quotientMapₐ P s hSQ
  have hg : Function.Injective g := Ideal.quotientMap_injective
  have hj : Function.Injective j := Ideal.quotientMap_injective' (H := hSQ) (by
    intro p hp
    change r (s p) ∈ Q at hp
    rwa [restrict_rename h] at hp)
  have hgX (i : Fin n) : g (Ideal.Quotient.mk P (MvPolynomial.X i)) ∈ quotientDegreeLE Q 1 := by
    change Ideal.Quotient.mk Q (r (MvPolynomial.X i)) ∈ _
    rw [show r (MvPolynomial.X i) = restrictVariables i from MvPolynomial.aeval_X _ _]
    by_cases hi : i.val < m
    · rw [restrictVariables, dite_eq_left hi]
      exact mk_mem_quotientDegreeLE (totalDegree_X _).le
    · rw [restrictVariables, dite_eq_right hi, map_zero]
      exact zero_mem _
  have hjX (i : Fin m) : j (Ideal.Quotient.mk Q (MvPolynomial.X i)) ∈ quotientDegreeLE P 1 := by
    change Ideal.Quotient.mk P (s (MvPolynomial.X i)) ∈ _
    rw [show s (MvPolynomial.X i) = MvPolynomial.X (Fin.castLE h i) from rename_X _ _]
    exact mk_mem_quotientDegreeLE (totalDegree_X _).le
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial Q
  symm
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := N)
  intro d hd
  rw [hN d hd]
  have heq : affineHilbertFunction Q d = affineHilbertFunction P d :=
    le_antisymm
      (by simpa only [one_mul] using affineHilbertFunction_le_of_injective j hj hjX d)
      (by simpa only [one_mul] using affineHilbertFunction_le_of_injective g hg hgX d)
  change (affineHilbertFunction Q d : ℚ) = (affineHilbertFunction P d : ℚ)
  exact_mod_cast heq
theorem sum_monomial_eq_of_tail_zero {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
    (b : Fin n → k) (hb : ∀ i, m ≤ i.val → b i = 0) :
    (∑ i : Fin n, Polynomial.monomial i.val (b i)) =
      ∑ i : Fin m, Polynomial.monomial i.val (b (Fin.castLE h i)) := by
  classical
  let e : Fin m ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  calc
    _ = ∑ i ∈ Finset.univ.map e, Polynomial.monomial i.val (b i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hi' : m ≤ i.val := le_of_not_gt fun hl =>
        hi (Finset.mem_map.mpr ⟨⟨i.val, hl⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [hb i hi', Polynomial.monomial_zero_right]
    _ = _ := Finset.sum_map _ _ _
end
end P0_9_5_1_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P0_9_5_2
noncomputable section
open K1_13 (Geom embed Row atJet)
open K1_13_5 (RegularAt separant compatibilityNumerator)
open K1_13_5_5 K1_13_5_5_1
open P0_9 (taylorLength physicalDegree TrueWeightLE anchorCutoff)
open scoped Polynomial
open K1_13_5_5_1_2 (evalRow coeffValue jetValue existsDerivation deriv_poly deriv_jet evalNumerator iterate_value)
open K1_13_5_5_1_3 (reconstruct mapCoeffs_trajectory eq_zero_of_constant_coeffs)
private theorem reconstruct_solution {F : Type} [Field F] [CharP F K1.p]
    (D : Derivation ℕ F F) (L : ℕ) (hL : 3 ≤ L) (hchar : L < K1.p)
    (f : Row 3) (k : Geom →+* F) (x : F) (y : Fin 3 → F)
    (hx : D x = 1) (hk : ∀ a, D (k a) = 0)
    (hy₀ : D (y 0) = y 1) (hy₁ : D (y 1) = 2 * y 2)
    (hcut : ((D : F → F)^[L]) (y 0) = 0) (hzero : rowAt k x y f = 0)
    (hweight : ∀ U : (Polynomial F), U.natDegree < L → (trajectory k U f).natDegree < K1.p) :
    ∃ U : (Polynomial F), U.natDegree < L ∧ trajectory k U f = 0 ∧ jetAt x U = y := by
  let _ : Differential F :=
    ⟨Derivation.mk' D.toLinearMap.toAddMonoidHom.toIntLinearMap (fun a b => D.leibniz a b)⟩
  obtain ⟨U, hU, hc, hinit⟩ := reconstruct hL hchar x y hx hy₀ hy₁ hcut
  have hroot : (trajectory k U f).eval x = 0 := by
    rwa [eval_trajectory, hinit]
  exact ⟨U, hU, eq_zero_of_constant_coeffs _ hx _ (hweight U hU)
    (mapCoeffs_trajectory _ hk hc f) hroot, hinit⟩
theorem chart_trajectory (f : Row 3) [(chartIdeal f).IsPrime]
    (L : ℕ) (hL : 3 ≤ L) (hchar : L < K1.p)
    (hs : freshRow (separant f) ∉ chartIdeal f)
    (hweight : ∀ U : (Polynomial (ChartField f)), U.natDegree < L →
      (trajectory (chartConstants f) U f).natDegree < K1.p)
    (hwhole : f ∣ compatibilityNumerator f (L - 3)) :
    ∃ U : (Polynomial (ChartField f)), U.natDegree < L ∧
      trajectory (chartConstants f) U f = 0 ∧ jetAt (chartCenter f) U = chartJets f := by
  let e := onChart f
  let π : FreshJetRing →+* ChartRing f := Ideal.Quotient.mk (chartIdeal f)
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = chartIdeal f := Ideal.mk_ker
  have hregular : evalRow e (separant f) ≠ 0 :=
    fun h => hs ((onChart_eq_zero f _).mp h)
  let qr : CommRing (ChartRing f) := Ideal.Quotient.commRing (chartIdeal f)
  let qd : IsDomain (ChartRing f) := Ideal.Quotient.isDomain (chartIdeal f)
  let kf : Field (ChartField f) := FractionRing.field (ChartRing f)
  let ka : Algebra (ChartRing f) (ChartField f) := inferInstance
  let kl : IsFractionRing (ChartRing f) (ChartField f) := inferInstance
  obtain ⟨D, hD⟩ := @existsDerivation (ChartRing f) (ChartField f) qr kf ka qd kl π f
    hsurj hker hregular
  have hnum : evalRow e (compatibilityNumerator f (L - 3)) = 0 := by
    obtain ⟨q, hq⟩ := hwhole
    have hzero : evalRow e f = 0 :=
      (onChart_eq_zero f _).mpr (Ideal.mem_span_singleton_self _)
    rw [hq, map_mul, hzero, zero_mul]
  rw [evalNumerator e f D hD hregular] at hnum
  have hjet := (mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hregular)
  have hcut : ((D : ChartField f → ChartField f)^[L]) (chartJets f 0) = 0 := by
    change ((D : ChartField f → ChartField f)^[L]) (jetValue e 0) = 0
    rw [show L = (L - 3 + 1) + 2 by omega,
      iterate_value e f D hD, hjet, mul_zero]
  let _ : CharP (ChartField f) K1.p :=
    charP_of_injective_ringHom ((chartConstants f).comp embed).injective K1.p
  have hx : D (chartCenter f) = 1 := by
    change D (coeffValue e Polynomial.X) = 1
    rw [deriv_poly e f D hD, Polynomial.derivative_X, map_one]
  have hk (a : Geom) : D (chartConstants f a) = 0 := by
    change D (coeffValue e (Polynomial.C a)) = 0
    rw [deriv_poly e f D hD, Polynomial.derivative_C, map_zero]
  have hzero : rowAt (chartConstants f) (chartCenter f) (chartJets f) f = 0 := by
    rw [rowAt_chart]
    exact (onChart_eq_zero f _).mpr (Ideal.mem_span_singleton_self _)
  exact reconstruct_solution D L hL hchar f (chartConstants f) (chartCenter f) (chartJets f)
    hx hk (deriv_jet e f D hD 0) (deriv_jet e f D hD 1) hcut hzero hweight
end
end P0_9_5_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P0_9_5_2
noncomputable section
open K1_13 (Geom)
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open P0_9 (physicalDegree)
open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_5_5_2_1 (monic_chart_aux)
open K1_13_5_5_2_1 (commonFactor_monic trimmedValue_monic trimmedValue_dvd)
private theorem square_dvd_trimmed_pow {A : Type} [CommRing A] [IsDomain A]
    {f : (Polynomial A)} (s : Factorization f) {d : ℕ} (hf : f.natDegree ≤ d) (hd : 2 ≤ d) :
    f ^ 2 ∣ (trimmedValue s) ^ d := by
  classical
  have hdegree : (∑ i, s.multiplicity i * (s.factor i).natDegree) = f.natDegree := by
    conv_rhs => rw [s.product_eq]
    rw [Polynomial.natDegree_prod_of_monic Finset.univ _ (fun i _ => (s.monic i).pow _)]
    simp only [Polynomial.natDegree_pow]
  refine (dvd_of_eq (congrArg (fun g : (Polynomial A) => g ^ 2) s.product_eq)).trans ?_
  rw [trimmedValue, ← Finset.prod_pow, ← Finset.prod_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  by_cases hconstant : (s.factor i).natDegree = 0
  · simp [Polynomial.eq_one_of_monic_natDegree_zero (s.monic i) hconstant]
  have hmi : s.multiplicity i ≤ d := calc
    _ = s.multiplicity i * 1 := (mul_one _).symm
    _ ≤ s.multiplicity i * (s.factor i).natDegree :=
      Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hconstant)
    _ ≤ ∑ j, s.multiplicity j * (s.factor j).natDegree :=
      Finset.single_le_sum (f := fun j => s.multiplicity j * (s.factor j).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = f.natDegree := hdegree
    _ ≤ d := hf
  rw [← pow_mul, ← pow_mul]
  apply pow_dvd_pow
  by_cases h : s.multiplicity i ≤ 2
  · rw [min_eq_left h]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (s.multiplicity i) hd
  · rw [min_eq_right (by omega)]
    exact (Nat.mul_le_mul_right 2 hmi).trans_eq (Nat.mul_comm d 2)
theorem eval_divisions {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    (e : (Polynomial A) →+* B) {f : (Polynomial A)} (s : Factorization f) {d : ℕ}
    (hf : f.natDegree ≤ d) (hd : 2 ≤ d) :
    e (trimmedValue s) ∣ e f ∧ e f ^ 2 ∣ e (trimmedValue s) ^ d :=
  ⟨map_dvd e (trimmedValue_dvd s),
    by simpa only [map_pow] using map_dvd e (square_dvd_trimmed_pow s hf hd)⟩
end
end P0_9_5_2
end

end Merged_PortLow5

-- merged module PortLow4
section Merged_PortLow4
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
@[simp] theorem exponent_none (u i l k : ℕ) : exponent u i l k none = u := by
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

end Merged_PortLow4

-- merged module PortFrontB
section Merged_PortFrontB
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_6
noncomputable section
open P0 Polynomial
end
end P0_6
end
section
namespace P0_6
noncomputable section
open P0 Polynomial ProximityPrize.Benchmark FrobeniusLocator
theorem amp_le (v : Fin 2 → (Polynomial K)) (j : Fin 2) :
    (v j).natDegree ≤ amplitudeDegree (v 0) (v 1) := by
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _
private theorem amp_witness (v : Fin 2 → (Polynomial K)) (hc : IsCoprime (v 0) (v 1)) :
    ∃ j, v j ≠ 0 ∧ (v j).natDegree = amplitudeDegree (v 0) (v 1) := by
  by_cases hv : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h
      obtain ⟨a, b, hab⟩ := hc
      simp [hv, h] at hab
    exact ⟨1, h1, by simp [amplitudeDegree, hv]⟩
  by_cases hd : (v 1).natDegree ≤ (v 0).natDegree
  · exact ⟨0, hv, (max_eq_left hd).symm⟩
  · refine ⟨1, ?_, (max_eq_right (by omega)).symm⟩
    intro hz
    simp [hz] at hd
theorem primitive_lift (del : Finset I) (v L : Fin 2 → (Polynomial K)) (w : I → K)
    (t : ℕ) (hc : IsCoprime (v 0) (v 1)) (hL : ∀ j, (L j).natDegree < t)
    (he : ∀ i ∉ del, ∀ j, (L j).eval (node i) = (v j).eval (node i) * w i)
    (hpos : amplitudeDegree (v 0) (v 1) < t)
    (hroom : t + amplitudeDegree (v 0) (v 1) + del.card ≤ 262144) :
    ∃ P : (Polynomial K), P.natDegree + amplitudeDegree (v 0) (v 1) < t ∧
      ∀ i ∉ del, P.eval (node i) = w i := by
  classical
  have hcross : v 0 * L 1 - v 1 * L 0 = 0 := by
    by_contra hn
    have hb := Strata.root_nodes_card_le node IRSProfile.domain.injective _ hn (Finset.univ \ del)
      (by
        intro i hi
        simp only [eval_sub, eval_mul, he i (Finset.mem_sdiff.mp hi).2]
        ring)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index] at hb
    have hprod (i j : Fin 2) : (v i * L j).natDegree < amplitudeDegree (v 0) (v 1) + t :=
      natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt (amp_le v i) (hL j))
    have hlt := (natDegree_sub_le (v 0 * L 1) (v 1 * L 0)).trans_lt
      (max_lt (hprod 0 1) (hprod 1 0))
    omega
  obtain ⟨a,b,hab⟩ := hc
  let P := a * L 0 + b * L 1
  have hdiv (j : Fin 2) : v j * P = L j := by
    dsimp [P]
    fin_cases j
    · change v 0 * (a * L 0 + b * L 1) = L 0
      linear_combination L 0 * hab + b * hcross
    · change v 1 * (a * L 0 + b * L 1) = L 1
      linear_combination L 1 * hab - a * hcross
  refine ⟨P, ?_, ?_⟩
  · by_cases hz : P = 0
    · simpa [hz] using hpos
    obtain ⟨j,hv,hd⟩ := amp_witness v ⟨a,b,hab⟩
    have hh := hL j
    rw [← hdiv j, natDegree_mul hv hz, hd, add_comm] at hh
    exact hh
  · intro i hi
    have hh := congrArg (Polynomial.eval (node i)) hab
    simp only [eval_add, eval_mul, eval_one] at hh
    simp only [P, eval_add, eval_mul, he i hi]
    linear_combination w i * hh
theorem contraction_degree {U V P Q : (Polynomial K)} {s t : ℕ}
    (hU : U.natDegree ≤ s) (hV : V.natDegree ≤ s)
    (hP : P.natDegree < t) (hQ : Q.natDegree < t) :
    (U * P - V * Q).natDegree < t + s := by
  apply (natDegree_sub_le _ _).trans_lt
  rw [add_comm t s]
  exact max_lt (natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt hU hP))
    (natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt hV hQ))
end
end P0_6
end
section
namespace P0_6
noncomputable section
open P0
open scoped BigOperators
theorem sum_rows {n : ℕ} (f : ℕ → ℕ) (rows : Fin n → ℕ)
    (h : ∀ i : Fin n, f i.val = rows i) :
    (∑ i ∈ Finset.range n, f i) = ∑ i : Fin n, rows i := by
  rw [← Fin.sum_univ_eq_sum_range f n]
  exact Finset.sum_congr rfl (fun i _ => h i)
theorem ceil_sq_div_eq (a b c v : ℕ) (hb : 0 < b) (hv : v ≠ 0)
    (hl : (v - 1) * b ^ 2 < c * a ^ 2) (hu : c * a ^ 2 ≤ v * b ^ 2) :
    ⌈(c : ℚ) * ((a : ℚ) / (b : ℚ)) ^ 2⌉₊ = v := by
  rw [Nat.ceil_eq_iff hv, div_pow, ← mul_div_assoc]
  have hpos : 0 < (b : ℚ) ^ 2 := pow_pos (Nat.cast_pos.mpr hb) 2
  constructor
  · apply (lt_div_iff₀ hpos).mpr
    exact_mod_cast hl
  · apply (div_le_iff₀ hpos).mpr
    exact_mod_cast hu
end
end P0_6
end
section
namespace P0_6
noncomputable section
open P0 FrobeniusLocator ProximityPrize.Benchmark Polynomial
theorem natDegree_lt_of_degree_lt_pos {P : (Polynomial K)} {m : ℕ} (hm : 0 < m)
    (h : P.degree < m) : P.natDegree < m := by
  by_cases hP : P = 0
  · simpa [hP] using hm
  · exact (natDegree_lt_iff_degree_lt hP).mpr h
end
end P0_6
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P0_6
noncomputable section
open P0 Polynomial FrobeniusLocator
attribute [local instance 2500] CJ0.stackRank._proof_1 P0.ordinary._proof_1
local notation "KS" => @CommSemiring.toSemiring K
  (@Semifield.toCommSemiring K (@Field.toSemifield K
    (@CompPoly.Extension.Ext.instField KoalaBear.Field KoalaBear.instFieldField KoalaBear.ext6Params
      CJ0.stackRank._proof_1 KoalaBear.instFactEqNatCardFieldQExt6Params
      KoalaBear.instFactIrreduciblePolynomialFieldPolyExt6Params)))
def column (n : ℕ) (f : Fin 2 → (Polynomial K)) : Bivar :=
  liftX (f 0) + liftX (f 1) * C (Polynomial.X ^ n)
theorem column_ne {n : ℕ} (hn : n ≠ 0) {f : Fin 2 → (Polynomial K)}
    (hf : ∃ j, f j ≠ 0) : column n f ≠ 0 := by
  intro hz
  have h := congrArg Polynomial.Bivariate.swap hz
  simp only [column, liftX, map_add, map_mul, Bivariate.swap_map_C, Bivariate.swap_C,
    Polynomial.map_pow, Polynomial.map_X, map_zero] at h
  have hcoeff (i : ℕ) := congrArg (fun q : Bivar => q.coeff i) h
  have h0 : f 0 = 0 := by simpa [coeff_C_mul_X_pow, Ne.symm hn] using hcoeff 0
  have h1 : f 1 = 0 := by simpa [coeff_C_mul_X_pow, coeff_C, hn] using hcoeff n
  obtain ⟨j,hj⟩ := hf
  fin_cases j
  · exact hj h0
  · exact hj h1
theorem column_bound (n : ℕ) (f : Fin 2 → (Polynomial K)) :
    (column n f).natDegree ≤ amplitudeDegree (f 0) (f 1) :=
  (natDegree_add_le _ _).trans (max_le_max natDegree_map_le
    ((natDegree_mul_C_le _ _).trans natDegree_map_le))
theorem column_dvd (n : ℕ) (f : Fin 2 → (Polynomial K)) (q : (Polynomial K))
    (hd : ∀ j, q ∣ f j) : liftX q ∣ column n f :=
  dvd_add ((Polynomial.mapRingHom Polynomial.C).map_dvd (hd 0))
    ((((Polynomial.mapRingHom Polynomial.C).map_dvd (hd 1))).mul_right _)
private theorem column_mul (a : (Polynomial K)) (n : ℕ) (f : Fin 2 → (Polynomial K)) :
    liftX a * (liftX (f 0) + seed ^ n * liftX (f 1)) =
      column n (fun j => a * f j) := by
  simp only [column, liftX, seed, Polynomial.map_mul, ← C_pow]
  ring
private def firstColumn (d : ℕ) (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) : Bivar :=
  liftX a * (liftX (@Polynomial.map K K KS KS twist (β 0)) +
    seed ^ d * liftX (@Polynomial.map K K KS KS twist (β 1)))
theorem threeU_fun : threeU = firstColumn p := rfl
theorem firstColumn_normal (d : ℕ) (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) :
    firstColumn d a β = column d (fun j => a * (β j).map twist) :=
  column_mul a d (fun j => (β j).map twist)
theorem tight_pair {F : Type*} [Field F] (U V U' V' : (Polynomial F))
    (hneU : U ≠ 0) (hneV : V ≠ 0) (hne' : U' ≠ 0) (hc : IsCoprime U V)
    (he : U * V' = V * U') (hmax : max U'.natDegree V'.natDegree ≤ max U.natDegree V.natDegree) :
    max U'.natDegree V'.natDegree = max U.natDegree V.natDegree ∧ IsCoprime U' V' := by
  obtain ⟨a,b,hab⟩ := hc
  let m := a * U' + b * V'
  have hu : U' = m * U := by dsimp [m]; linear_combination -U' * hab - b * he
  have hv : V' = m * V := by dsimp [m]; linear_combination -V' * hab + a * he
  have hm : m ≠ 0 := by intro h; exact hne' (hu.trans (by simp [h]))
  have huD := congrArg Polynomial.natDegree hu
  have hvD := congrArg Polynomial.natDegree hv
  rw [natDegree_mul hm hneU] at huD
  rw [natDegree_mul hm hneV] at hvD
  have hdeg : m.natDegree = 0 := by omega
  have hunit : IsUnit m := isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hm, hdeg]; rfl)
  obtain ⟨k,hk⟩ := isUnit_iff_dvd_one.mp hunit
  refine ⟨by omega, a*k, b*k, ?_⟩
  calc
    a*k*U' + b*k*V' = (m*k) * (a*U + b*V) := by rw [hu,hv]; ring
    _ = 1 := by rw [← hk,hab,one_mul]
private def slice (P : Bivar) (n : ℕ) : (Polynomial K) :=
  ∑ j ∈ Finset.range (P.natDegree + 1), monomial j ((P.coeff j).coeff n)
private theorem slice_eval (P : Bivar) (n : ℕ) (x : K) :
    (slice P n).eval x = (P.eval (C x)).coeff n := by
  rw [eval_eq_sum_range (C x)]
  simp only [slice, eval_finsetSum, eval_monomial, finsetSum_coeff, ← C_pow, coeff_mul_C]
theorem slice_bound (P : Bivar) (n : ℕ) : (slice P n).natDegree ≤ P.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
private theorem select_four (d : ℕ) (hd : 1 < d) (r : Fin 2 → Fin 2 → K) (j l : Fin 2) :
    ((C (r 0 0) + C (r 1 0)*Polynomial.X + C (r 0 1)*Polynomial.X^d +
      C (r 1 1)*Polynomial.X^(d+1)) : (Polynomial K)).coeff (j.val + d*l.val) = r j l := by
  fin_cases j <;> fin_cases l <;>
    simp only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_C, Nat.mul_zero,
      Nat.mul_one, Nat.zero_add, Nat.add_zero] <;>
    split_ifs <;> first | omega | simp_all
private theorem four_coeff (d : ℕ) (hd : 1 < d) (u v w z : Fin 2 → K) (j l : Fin 2) :
    (((C (u 0) + C (u 1) * Polynomial.X ^ d) * (C (w 0) + Polynomial.X * C (w 1)) +
      (C (v 0) + C (v 1) * Polynomial.X) * (C (z 0) + Polynomial.X^d * C (z 1)) : (Polynomial K)).coeff
      (j.val + d*l.val)) = u l*w j + v j*z l := by
  let r := fun j l => u l*w j + v j*z l
  have hex : (C (u 0) + C (u 1) * Polynomial.X ^ d) * (C (w 0) + Polynomial.X * C (w 1)) +
      (C (v 0) + C (v 1) * Polynomial.X) * (C (z 0) + Polynomial.X^d * C (z 1)) =
      C (r 0 0) + C (r 1 0)*Polynomial.X + C (r 0 1)*Polynomial.X^d +
      C (r 1 1)*Polynomial.X^(d+1) := by
    simp only [r, map_add, map_mul, pow_succ]
    ring
  rw [hex]
  exact select_four d hd r j l
private theorem column_eval (d : ℕ) (f : Fin 2 → (Polynomial K)) (x : K) :
    (column d f).eval (C x) = C ((f 0).eval x) + C ((f 1).eval x) * Polynomial.X^d := by
  simp only [column, liftX, eval_add, eval_mul, eval_C, eval_map_apply]
private theorem word_coeff (d : ℕ) (hd : 1 < d) (U V : Fin 2 → (Polynomial K)) (u : Words)
    (i : I) (j l : Fin 2) :
    (U l).eval (node i) * u j i + (V j).eval (node i) * (u l i)^d =
    (((C ((U 0).eval (node i)) + C ((U 1).eval (node i)) * Polynomial.X^d) *
          (C (u 0 i) + Polynomial.X * C (u 1 i)) +
        (C ((V 0).eval (node i)) + C ((V 1).eval (node i)) * Polynomial.X) *
          (C ((u 0 i)^d) + Polynomial.X^d * C ((u 1 i)^d))) : (Polynomial K)).coeff
        (j.val + d*l.val) :=
  (four_coeff d hd (fun l => (U l).eval (node i)) (fun j => (V j).eval (node i))
    (fun j => u j i) (fun l => (u l i)^d) j l).symm
private def relationAt (d : ℕ) (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ d) + Polynomial.X (R := K) ^ d * C (u 1 i ^ d)) =
      output.eval (C (node i))
theorem relationOn_fun : relationOn = relationAt p := rfl
def outputs (d : ℕ) (P : Bivar) (j l : Fin 2) := slice P (j.val + d*l.val)
theorem nodes_of_columns (d : ℕ) (hd : 1 < d) (u : Words) (deleted : Finset I)
    (U V : Fin 2 → (Polynomial K)) (P : Bivar)
    (h : relationAt d u deleted (column d U) (column 1 V) P) :
    K1_10.planeNodes d u deleted U V (outputs d P) := by
  intro i hi j l
  rw [outputs, slice_eval, ← h i hi, column_eval, column_eval, pow_one]
  exact word_coeff d hd U V u i j l
end
end P0_6
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace P0_6_1
noncomputable section
open MvPolynomial K1_11
open K1_10_1 (Contacts  relationBounds)
theorem exists_kernel_outside {F E G : Type*} [Field F]
    [AddCommGroup E] [Module F E] [Module.Finite F E]
    [AddCommGroup G] [Module F G] [Module.Finite F G]
    (f : E →ₗ[F] G) (R : Submodule F E)
    (hdim : Module.finrank F G + Module.finrank F R < Module.finrank F E) :
    ∃ q : E, f q = 0 ∧ q ∉ R := by
  by_contra hn
  have hle : LinearMap.ker f ≤ R := by
    intro q hq
    by_contra hnot
    exact hn ⟨q, LinearMap.mem_ker.mp hq, hnot⟩
  have hk := Submodule.finrank_mono hle
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hr := (LinearMap.range f).finrank_le
  omega
variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}
variable (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)
end
end P0_6_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P0_6_1
noncomputable section
open K1 K1_10 K1_11 MvPolynomial
open K1_10_1 (Contacts denominator liftOrdinary numerator pencil planeRelation
  planeRelation_view relationBounds toScalarSource )
private theorem eval_liftOrdinary (Q P : Polynomial K) (s t : K) :
    aeval (scalarImages P s t) (liftOrdinary Q) = Q := by
  let φ : MvPolynomial (Fin 4) K →+* Polynomial K := (aeval (scalarImages P s t)).toRingHom
  have hh : φ.comp liftOrdinary = RingHom.id (Polynomial K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [φ, liftOrdinary]
    · simp [φ, liftOrdinary, scalarImages]
  exact RingHom.congr_fun hh Q
private theorem eval_denominator (V : Fin 2 → Polynomial K) (P : Polynomial K) (s t : K) :
    aeval (scalarImages P s t) (denominator V) = V 0 + Polynomial.C s * V 1 := by
  simp only [denominator, pencil, map_add, map_mul, aeval_X, eval_liftOrdinary]
  rfl
theorem denominator_ne {V : Fin 2 → Polynomial K} (hV : ∃ j, V j ≠ 0) :
    denominator V ≠ 0 := by
  intro hz
  have h (s : K) := eval_denominator V 0 s 0
  simp only [hz, map_zero] at h
  have h0 : V 0 = 0 := by simpa using (h 0).symm
  have h1 : V 1 = 0 := by simpa [h0] using (h 1).symm
  obtain ⟨j,hj⟩ := hV
  fin_cases j
  · exact hj h0
  · exact hj h1
theorem relation_eval (U V : Fin 2 → Polynomial K) (O : Fin 2 → Fin 2 → Polynomial K)
    (Q Q' : Polynomial K) (s t : K) :
    aeval (decoderImages Q Q' s t) (planeRelation U V O) =
      (V 0 + Polynomial.C s * V 1) * Q' -
      ((O 0 0 + Polynomial.C s * O 1 0) + Polynomial.C t * (O 0 1 + Polynomial.C s * O 1 1) -
        (U 0 + Polynomial.C t * U 1) * Q) := by
  rw [decoderImages, ← polynomialView_eval, planeRelation_view]
  simp [eval_denominator, numerator, pencil, eval_liftOrdinary]
  rfl
theorem coeff_bounds (L : MvPolynomial (Fin 5) K) (a b : MvPolynomial (Fin 4) K)
    (d : ℕ) (hL : L ∈ filtered (sourceWeights 131071) (sourceBounds d 1 1 1))
    (hview : polynomialView L = Polynomial.C b * Polynomial.X - Polynomial.C a)
    (hb : b ≠ 0) :
    a.weightedTotalDegree scalarWeightY ≤ 1 ∧ b.weightedTotalDegree scalarWeightY ≤ 0 ∧
    a.weightedTotalDegree scalarWeightYS ≤ 1 ∧ b.weightedTotalDegree scalarWeightYS ≤ 1 ∧
    a.weightedTotalDegree scalarWeightT ≤ 1 ∧ b.weightedTotalDegree scalarWeightT ≤ 0 := by
  have hz : (polynomialView L).coeff 0 = -a := by
    rw [hview]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X]
  have hone : (polynomialView L).coeff 1 = b := by
    rw [hview]
    simp [Polynomial.coeff_sub, Polynomial.coeff_C]
  obtain ⟨hy, hs, ht⟩ := polynomialView_source_coefficients d 131071 1 1 1 L hL
  have hs1 := hs 1 (by decide) (hone ▸ hb)
  have hy1 := hy 1 (by decide) (hone ▸ hb)
  have ht1 := ht 1 (by decide) (hone ▸ hb)
  rw [hone] at hs1 hy1 ht1
  have ha (v : Fin 4 → ℕ) : (-a).weightedTotalDegree v = a.weightedTotalDegree v := by
    simp [weightedTotalDegree]
  have ha0 : a.weightedTotalDegree scalarWeightY ≤ 1 ∧
      a.weightedTotalDegree scalarWeightYS ≤ 1 ∧ a.weightedTotalDegree scalarWeightT ≤ 1 := by
    by_cases ha' : a = 0
    · simp [ha', weightedTotalDegree]
    · have h0 : (polynomialView L).coeff 0 ≠ 0 := hz ▸ neg_ne_zero.mpr ha'
      have hy0 := hy 0 (by decide) h0
      have hs0 := hs 0 (by decide) h0
      have ht0 := ht 0 (by decide) h0
      simp only [hz, ha, Nat.add_zero] at hy0 hs0 ht0
      exact ⟨hy0, hs0, ht0⟩
  exact ⟨ha0.1, by omega, ha0.2.1, hs1, ha0.2.2, by omega⟩
end
end P0_6_1
end

end Merged_PortFrontB

-- merged module FrontBranch3
section Merged_FrontBranch3
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_3
noncomputable section
open P1 Polynomial
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : (Polynomial K) :=
  B.a * (B.β l).map twist
abbrev Plane := K1_10.Plane
abbrev Adjugate := K1_10.Adjugate
inductive Bank where
  | st
  | ts
def Bank.first : Bank → ℕ
  | .st => 20
  | .ts => 17
def Bank.second : Bank → ℕ
  | .st => 17
  | .ts => 20
structure ScalarSource (bank : Bank) where
  poly : MvPolynomial (Fin 2) K1_10.SeedPoly
  nonzero : poly ≠ 0
  y_degree : poly.degreeOf 1 ≤ 5
  s_degree : ∀ e ∈ poly.support, (poly.coeff e).degreeOf 0 ≤ bank.first + 5
  t_degree : ∀ e ∈ poly.support, (poly.coeff e).degreeOf 1 ≤ bank.second
  total : ∀ e ∈ poly.support, e 1 + (poly.coeff e).totalDegree ≤ 42
def ScalarSource.atLabel {bank} (A : ScalarSource bank) (γ : K) : MvPolynomial (Fin 2) K :=
  A.poly.map (MvPolynomial.eval ![γ, γ ^ p])
def ScalarSource.atDecoder {bank} (A : ScalarSource bank) (γ : K) (P : (Polynomial K)) : (Polynomial K) :=
  MvPolynomial.aeval ![Polynomial.X, P] (A.atLabel γ)
abbrev cutDegree : ℕ := (2 * (k - 1) - 1) * (42 - 1) + 1
def incidenceRatio : ℚ :=
  (((blockLength - (k - 1)) * cutDegree : ℕ) : ℚ) / ((agreement - (k - 1) : ℕ) : ℚ)
def Bank.graphFee (bank : Bank) : ℕ := bank.first + 5 + p * bank.second
end
end P1_3
end
section
namespace P1_3
noncomputable section
open P1
open scoped BigOperators
open P0_6 (sum_rows ceil_sq_div_eq)
private theorem jet_st : K1_10.jetDim 4 20 17 = 6981 := by
  let rows : Fin 4 → ℕ := ![3570, 2080, 1007, 324]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 4, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 6981 := by decide
private theorem jet_ts : K1_10.jetDim 4 17 20 = 6981 := by
  let rows : Fin 4 → ℕ := ![3600, 2074, 992, 315]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 4, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 6981 := by decide
private theorem local_st : K1_10.jetDim 3 19 16 = 3216 := by
  let rows : Fin 3 → ℕ := ![1960, 950, 306]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 3, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 3216 := by decide
private theorem local_ts : K1_10.jetDim 3 16 19 = 3216 := by
  let rows : Fin 3 → ℕ := ![1972, 944, 300]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 3, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 3216 := by decide
theorem jet_quotient (bank : Bank) :
    K1_10.jetDim 4 bank.first bank.second -
      K1_10.jetDim 3 (bank.first - 1) (bank.second - 1) = 3765 := by
  cases bank
  · change K1_10.jetDim 4 20 17 - K1_10.jetDim 3 19 16 = 3765
    rw [jet_st, local_st]
  · change K1_10.jetDim 4 17 20 - K1_10.jetDim 3 16 19 = 3765
    rw [jet_ts, local_ts]
end
end P1_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace P1_3_1
noncomputable section
open MvPolynomial K1_11
open K1_10_1 (Contacts relationBounds)
open P0_6_1 (exists_kernel_outside)
abbrev Multipliers (F : Type*) [Field F] (bank : P1_3.Bank) :=
  JetSpace F 2 (bank.first - 1) (bank.second - 1)
variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}
variable (bank : P1_3.Bank) (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)
private theorem first_sub_add (b : P1_3.Bank) : b.first - 1 + 1 = b.first := by cases b <;> rfl
private theorem second_sub_add (b : P1_3.Bank) : b.second - 1 + 1 = b.second := by cases b <;> rfl
def localMultiply (i : Fin N) : Multipliers F bank →ₗ[F] JetSpace F 3 bank.first bank.second where
  toFun Q := ⟨weightedTruncation contactWeight 4 (C.shifted i L * Q.val), by
    simpa only [first_sub_add, second_sub_add] using
      truncated_mul_mem_jet 2 (bank.first - 1) (bank.second - 1) 1 1 (C.shifted i L)
        ((contactShift_parameter_weights _ _ _ _ _ L).1.trans (le_of_eq (hdeg 2)))
        ((contactShift_parameter_weights _ _ _ _ _ L).2.trans (le_of_eq (hdeg 3))) Q⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp
abbrev LocalSpace (i : Fin N) :=
  (JetSpace F 3 bank.first bank.second) ⧸ LinearMap.range (localMultiply bank C hdeg i)
theorem local_finrank (i : Fin N) :
    Module.finrank F (LocalSpace bank C hdeg i) =
      J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1) := by
  have hinj : Function.Injective (localMultiply bank C hdeg i) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro Q hQ
    by_contra hn
    have hprod : weightedTruncation contactWeight 4 (C.shifted i L * Q.val) = 0 :=
      congrArg (fun x : JetSpace F 3 bank.first bank.second => x.val) hQ
    have horder := C.order_one i
    change (contactLift contactWeight (C.shifted i L)).natTrailingDegree = 1 at horder
    have hL : C.shifted i L ≠ 0 := by
      intro hz
      simp [hz] at horder
    exact contact_product_not_high_order contactWeight 4 (C.shifted i L) Q.val
      horder hL (fun hz => hn (Subtype.ext hz)) (jetSpace_support_bound _ _ _ Q)
      ((weightedTruncation_eq_zero_iff _ _ _).mp hprod)
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (localMultiply bank C hdeg i))
  rw [LinearMap.finrank_range_of_inj hinj, jetSpace_finrank, jetSpace_finrank] at hq
  change Module.finrank F (LocalSpace bank C hdeg i) + J 3 (bank.first - 1) (bank.second - 1) =
    J 4 bank.first bank.second at hq
  omega
end
end P1_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace P1_3_1
noncomputable section
open MvPolynomial
open K1_11 (scalarWeightY scalarWeightYS scalarWeightT scalarWeightTotal scalarImages)
open K1_10_1 (groupSeeds)
open P1 (K p)
open P1_3 (Bank ScalarSource)
open K1_10_1 (grouped_coeff joinExponents joinExponents_apply group_eval)
def toScalarSource {bank : Bank} (Q : MvPolynomial (Fin 4) K) (hn : Q ≠ 0)
    (hy : Q.weightedTotalDegree scalarWeightY ≤ 5)
    (hs : Q.weightedTotalDegree scalarWeightYS ≤ bank.first + 5)
    (ht : Q.weightedTotalDegree scalarWeightT ≤ bank.second)
    (htot : Q.weightedTotalDegree scalarWeightTotal ≤ 42) : ScalarSource bank := by
  have bounds (e f : Fin 2 →₀ ℕ) (hf : f ∈ ((groupSeeds Q).coeff e).support) :
      e 1 ≤ 5 ∧ f 0 ≤ bank.first + 5 ∧ f 1 ≤ bank.second ∧ e 1 + (f 0 + f 1) ≤ 42 := by
    have he : joinExponents e f ∈ Q.support := by
      rw [MvPolynomial.mem_support_iff, ← grouped_coeff]
      exact MvPolynomial.mem_support_iff.mp hf
    have ⟨h0, h1, h2, h3⟩ := joinExponents_apply e f
    have hy' := (le_weightedTotalDegree scalarWeightY he).trans hy
    have hs' := (le_weightedTotalDegree scalarWeightYS he).trans hs
    have ht' := (le_weightedTotalDegree scalarWeightT he).trans ht
    have htot' := (le_weightedTotalDegree scalarWeightTotal he).trans htot
    simp [scalarWeightY, scalarWeightYS, scalarWeightT, scalarWeightTotal,
      Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ,
      h0, h1, h2, h3, smul_eq_mul] at hy' hs' ht' htot'
    omega
  refine ⟨groupSeeds Q, (map_ne_zero_iff (groupSeeds (F := K)).toRingHom
    (groupSeeds (F := K)).injective).mpr hn, ?_, ?_, ?_, ?_⟩
  · rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro e he
    obtain ⟨f, hf⟩ := support_nonempty.mpr (MvPolynomial.mem_support_iff.mp he)
    exact (bounds e f hf).1
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf => (bounds e f hf).2.1)
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf => (bounds e f hf).2.2.1)
  · intro e he
    have hcoeff := MvPolynomial.mem_support_iff.mp he
    obtain ⟨f, hf⟩ := support_nonempty.mpr hcoeff
    have he' := (bounds e f hf).2.2.2
    have hb : ((groupSeeds Q).coeff e).totalDegree ≤ 42 - e 1 := by
      apply Finset.sup_le
      intro g hg
      have hh := (bounds e g hg).2.2.2
      simp [Finsupp.sum_fintype, Fin.sum_univ_succ]
      omega
    omega
theorem toScalarSource_atDecoder {bank : Bank} (Q : MvPolynomial (Fin 4) K) (hn)
    (hy : Q.weightedTotalDegree scalarWeightY ≤ 5)
    (hs : Q.weightedTotalDegree scalarWeightYS ≤ bank.first + 5)
    (ht) (htot) (γ : K) (P : Polynomial K) :
    (toScalarSource Q hn hy hs ht htot).atDecoder γ P =
      aeval (scalarImages P γ (γ ^ p)) Q := group_eval Q P γ (γ ^ p)
end
end P1_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_3_2
noncomputable section
open P1 MvPolynomial
open P1_3 (cutDegree)
open K1_10_2 (Row toGeneric)
open K1_10_2_2 (dx dy flow numerator)
open scoped Polynomial
open K1_10_2_2 (dx_degree dy_degree)
open K1_10_2_2 (clearPower separant taylorNumerator received nodeCut toGeneric_degree order_le_clearPower received_degree)
private theorem separant_degree {g : Row} (h : g.totalDegree ≤ 42) : (dy g).totalDegree ≤ 41 := by
  have := dy_degree g
  omega
private theorem flow_degree {g f : Row} {d : ℕ}
    (hg : g.totalDegree ≤ 42) (hf : f.totalDegree ≤ d) (hd : 0 < d) :
    (flow g f).totalDegree ≤ d + 41 := by
  have ha := separant_degree hg
  have hx := dx_degree g
  have hfx := dx_degree f
  have hfy := dy_degree f
  unfold flow
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    omega
  · apply (totalDegree_mul _ _).trans
    omega
private theorem numerator_degree {g : Row} (hg : g.totalDegree ≤ 42) (n : ℕ) :
    (numerator g n).totalDegree ≤ (2*n+1)*41+1 := by
  induction n with
  | zero =>
    simpa [numerator, totalDegree_neg] using (dx_degree g).trans hg
  | succ n ih =>
    have ha := separant_degree hg
    have hf := flow_degree hg ih (by omega)
    have hfa := flow_degree hg ha (by decide)
    rw [numerator]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      omega
    · apply (totalDegree_mul _ _).trans
      have hc := totalDegree_mul
        (MvPolynomial.C ((2*n+1 : ℕ) : (Polynomial K)) : Row) (flow g (dy g))
      rw [totalDegree_C, zero_add] at hc
      omega
private theorem sep_pow_degree (g : Row) (hg : g.totalDegree ≤ 42) (a : ℕ) :
    (separant g ^ a).totalDegree ≤ a * 41 :=
  (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left a ((toGeneric_degree _).trans (separant_degree hg)))
private theorem taylorNumerator_degree (g : Row) (hg : g.totalDegree ≤ 42) (x : K) :
    (taylorNumerator g x).totalDegree ≤ cutDegree := by
  unfold taylorNumerator
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    exact Nat.add_le_add_right (sep_pow_degree g hg clearPower) 1
  · apply totalDegree_finsetSum_le
    intro n hn
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, add_zero]
    apply (totalDegree_mul _ _).trans
    have h1 := sep_pow_degree g hg (clearPower - (2*n+1))
    have h2 := (toGeneric_degree (numerator g n)).trans (numerator_degree hg n)
    have h3 := Nat.sub_add_cancel (order_le_clearPower hn)
    change _ ≤ clearPower * 41 + 1
    omega
theorem nodeCut_degree (u : Words) (g : Row) (hg : g.totalDegree ≤ 42) (i : I) :
    (nodeCut u g i).totalDegree ≤ cutDegree := by
  unfold nodeCut
  apply (totalDegree_sub _ _).trans
  refine max_le (taylorNumerator_degree g hg _) ((totalDegree_mul _ _).trans ?_)
  exact Nat.add_le_add (sep_pow_degree g hg clearPower) (received_degree u i)
end
end P1_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace P1_3_2
noncomputable section
open P1 MvPolynomial
open P1_3 (ScalarSource incidenceRatio)
open K1_10_2 (Row RegularRoot derivativeOrder toGeneric atTrajectory point)
open scoped Polynomial
open K1_10_2_1 (seedRow seedRow_degree regroup specialize specialize_regroup decoderView decoderView_injective decoderView_degree eval_decoderView exists_simple_derivative eval_specialize specialize_iterate specialize_pderiv)
open K1_10_2_2 (nodeCut eval_nodeCut)
open K1_10_2 (derivativeOrder_degree eval_toGeneric)
private theorem regroup_degree {bank : P1_3.Bank} (A : ScalarSource bank) : (regroup A.poly).totalDegree ≤ 42 := by
  classical
  have hsum : regroup A.poly =
      ∑ e ∈ A.poly.support, regroup (monomial e (A.poly.coeff e)) := by
    conv_lhs => rw [A.poly.as_sum]
    rw [map_sum]
  rw [hsum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [regroup, eval₂Hom_monomial, Finsupp.prod_pow, Fin.prod_univ_two]
  change (seedRow (A.poly.coeff e) *
    ((C (Polynomial.X : (Polynomial K)) : Row) ^ e 0 * (MvPolynomial.X (0 : Fin 3) : Row) ^ e 1)).totalDegree ≤ 42
  have hx : ((C (Polynomial.X : (Polynomial K)) : Row) ^ e 0).totalDegree = 0 := by
    rw [← map_pow, totalDegree_C]
  calc
    _ ≤ (seedRow (A.poly.coeff e)).totalDegree +
        (((C (Polynomial.X : (Polynomial K)) : Row) ^ e 0) * (MvPolynomial.X (0 : Fin 3) : Row) ^ e 1).totalDegree :=
      totalDegree_mul _ _
    _ ≤ (A.poly.coeff e).totalDegree + e 1 := by
      apply Nat.add_le_add (seedRow_degree _)
      exact (totalDegree_mul _ _).trans (by rw [hx, zero_add, totalDegree_X_pow])
    _ ≤ 42 := by simpa only [Nat.add_comm] using A.total e he
theorem assign_charts {bank : P1_3.Bank} (A : ScalarSource bank) (Γ : Finset K)
    (P : ∀ γ ∈ Γ, (Polynomial K))
    (hF : ∀ γ (hγ : γ ∈ Γ), A.atLabel γ ≠ 0 ∧ A.atDecoder γ (P γ hγ) = 0) :
    ∃ g : Row, g.totalDegree ≤ 42 ∧
      ∀ γ (hγ : γ ∈ Γ), ∃ j : Fin 5, RegularRoot (derivativeOrder g j) γ (P γ hγ) := by
  let g := regroup A.poly
  refine ⟨g, regroup_degree A, ?_⟩
  intro γ hγ
  let Q := P γ hγ
  let specializeLabel := specialize (Polynomial.C γ) (Polynomial.C (γ ^ p))
  have hview : specializeLabel g = decoderView (A.atLabel γ) :=
    specialize_regroup A.poly γ (γ ^ p)
  have hne : specializeLabel g ≠ 0 := by
    rw [hview]
    intro hz
    exact (hF γ hγ).1 (decoderView_injective (hz.trans (map_zero _).symm))
  have hdegree : (specializeLabel g).natDegree ≤ 5 := by
    rw [hview]
    apply (decoderView_degree _).trans
    rw [degreeOf_eq_sup, Finset.sup_le_iff]
    intro e he
    exact (le_degreeOf_of_mem_support 1 (support_map_subset _ _ he)).trans A.y_degree
  have hroot : (specializeLabel g).IsRoot Q := by
    change (specializeLabel g).eval Q = 0
    rw [hview, eval_decoderView]
    exact (hF γ hγ).2
  obtain ⟨j, hj, hz, hsep⟩ :=
    exists_simple_derivative p 5 _ hne hdegree (by decide) Q hroot
  refine ⟨⟨j, hj⟩, ?_, ?_⟩
  · change MvPolynomial.eval ![Q, Polynomial.C γ, Polynomial.C (γ ^ p)]
      (derivativeOrder g ⟨j, hj⟩) = 0
    rw [← eval_specialize, derivativeOrder, specialize_iterate]
    exact hz
  · change MvPolynomial.eval ![Q, Polynomial.C γ, Polynomial.C (γ ^ p)]
      (pderiv 0 (derivativeOrder g ⟨j, hj⟩)) ≠ 0
    rw [← eval_specialize, specialize_pderiv, derivativeOrder, specialize_iterate]
    exact hsep
end
end P1_3_2
end

end Merged_FrontBranch3
