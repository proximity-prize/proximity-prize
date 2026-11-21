import ProximityPrize.SubmissionLower.PortLowBase
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
structure SecondFactors {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  weight : ∀ i, TrueWeightLE (f i) anchorCutoff
  total : (∑ i, (f i).totalDegree) ≤ 120
  index : (∑ i, indexDegree (f i)) ≤ 48
  top : (∑ i, (f i).degreeOf 2) ≤ 24
def Whole (f : Row 3) : Prop :=
  f ∣ K1_13_5.compatibilityNumerator f (taylorLength - 3)
def mixedBudget : ℕ :=
  let a := liftedBox (taylorLength + 1)
  let b := liftedBox (taylorLength + 2)
  mixed3 lowBox a b + (taylorLength - 1) * mixed3 lowBox graphBox b +
    taylorLength * mixed3 lowBox graphBox a
def invariantBudget : ℕ :=
  lowBox.b * (1 + (2 * (taylorLength + 1) - 7) * (lowBox.b - 1))
structure ProperCover (w : I → K) (Γ : Finset K) (s : K → K[X]) where
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
private def restrictVariables {k : Type*} [Field k] {m n : ℕ} :
    Fin n → MvPolynomial (Fin m) k :=
  fun i => if hi : i.val < m then MvPolynomial.X ⟨i.val, hi⟩ else 0
private theorem restrict_rename {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
    (p : MvPolynomial (Fin m) k) :
    MvPolynomial.aeval restrictVariables (rename (Fin.castLE h) p) = p := by
  have he : (MvPolynomial.aeval restrictVariables).comp (rename (R := k) (Fin.castLE h)) =
      AlgHom.id k (MvPolynomial (Fin m) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [restrictVariables, i.isLt]
  exact DFunLike.congr_fun he p
private theorem padded_hilbert {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
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
private theorem sum_monomial_eq_of_tail_zero {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
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
open P0_9_5 (Whole)
open scoped Polynomial
open private evalRow coeffValue jetValue existsDerivation deriv_poly deriv_jet
  evalNumerator iterate_value from ProximityPrize.SubmissionLower.Fast071
open private reconstruct mapCoeffs_trajectory eq_zero_of_constant_coeffs
  from ProximityPrize.SubmissionLower.Fast071
theorem reconstruct_solution {F : Type} [Field F] [CharP F K1.p]
    (D : Derivation ℕ F F) (L : ℕ) (hL : 3 ≤ L) (hchar : L < K1.p)
    (f : Row 3) (k : Geom →+* F) (x : F) (y : Fin 3 → F)
    (hx : D x = 1) (hk : ∀ a, D (k a) = 0)
    (hy₀ : D (y 0) = y 1) (hy₁ : D (y 1) = 2 * y 2)
    (hcut : ((D : F → F)^[L]) (y 0) = 0) (hzero : rowAt k x y f = 0)
    (hweight : ∀ U : F[X], U.natDegree < L → (trajectory k U f).natDegree < K1.p) :
    ∃ U : F[X], U.natDegree < L ∧ trajectory k U f = 0 ∧ jetAt x U = y := by
  let _ : Differential F :=
    ⟨Derivation.mk' D.toLinearMap.toAddMonoidHom.toIntLinearMap (fun a b => D.leibniz a b)⟩
  obtain ⟨U, hU, hc, hinit⟩ := reconstruct hL hchar x y hx hy₀ hy₁ hcut
  have hroot : (trajectory k U f).eval x = 0 := by
    rwa [eval_trajectory, hinit]
  exact ⟨U, hU, eq_zero_of_constant_coeffs _ hx _ (hweight U hU)
    (mapCoeffs_trajectory _ hk hc f) hroot, hinit⟩
private theorem chart_trajectory (f : Row 3) [(chartIdeal f).IsPrime]
    (L : ℕ) (hL : 3 ≤ L) (hchar : L < K1.p)
    (hs : freshRow (separant f) ∉ chartIdeal f)
    (hweight : ∀ U : (ChartField f)[X], U.natDegree < L →
      (trajectory (chartConstants f) U f).natDegree < K1.p)
    (hwhole : f ∣ compatibilityNumerator f (L - 3)) :
    ∃ U : (ChartField f)[X], U.natDegree < L ∧
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
open private monic_chart_aux from ProximityPrize.SubmissionLower.Fast064
open private commonFactor_monic trimmedValue_monic trimmedValue_dvd from ProximityPrize.SubmissionLower.Fast064
theorem square_dvd_trimmed_pow {A : Type} [CommRing A] [IsDomain A]
    {f : A[X]} (s : Factorization f) {d : ℕ} (hf : f.natDegree ≤ d) (hd : 2 ≤ d) :
    f ^ 2 ∣ (trimmedValue s) ^ d := by
  classical
  have hdegree : (∑ i, s.multiplicity i * (s.factor i).natDegree) = f.natDegree := by
    conv_rhs => rw [s.product_eq]
    rw [Polynomial.natDegree_prod_of_monic Finset.univ _ (fun i _ => (s.monic i).pow _)]
    simp only [Polynomial.natDegree_pow]
  refine (dvd_of_eq (congrArg (fun g : A[X] => g ^ 2) s.product_eq)).trans ?_
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
private theorem eval_divisions {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    (e : A[X] →+* B) {f : A[X]} (s : Factorization f) {d : ℕ}
    (hf : f.natDegree ≤ d) (hd : 2 ≤ d) :
    e (trimmedValue s) ∣ e f ∧ e f ^ 2 ∣ e (trimmedValue s) ^ d :=
  ⟨map_dvd e (trimmedValue_dvd s),
    by simpa only [map_pow] using map_dvd e (square_dvd_trimmed_pow s hf hd)⟩
end
end P0_9_5_2
end
