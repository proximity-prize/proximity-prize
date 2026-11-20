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
abbrev firstExponent : ℕ := 2 * taylorLength - 5
abbrev firstChartTotal : ℕ := 1 + firstExponent * (5064 - 1)
abbrev firstChartTop : ℕ := min firstChartTotal (firstExponent * (1104 - 1) + taylorLength - 1)
def firstMixedBudget : ℕ :=
  5064 * firstChartTop + 1104 * (firstChartTotal - firstChartTop)
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
namespace P0_9_5_1
noncomputable section
open K1_13 (Geom Row Shape atJet)
open K1_13_5 (RegularAt compatibilityNumerator graphBox liftedBox separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericRow graph graphPoint
  InLiftedBox RepresentsOnGraph jetPoint regularLocus extendedAtJet)
open P0_9 (taylorLength physicalDegree)
open P0_9_5 (Whole mixedBudget)
open Polynomial
open scoped BigOperators
abbrev Coefficients := Fin taylorLength → GeometricX
abbrev CoefficientIdeal := Ideal (GeoRow taylorLength)
abbrev CurveIndex (n : ℕ) := Fin n × Ideal (GeoRow 3)
def coefficientPoint (S : Geom[X]) : Coefficients :=
  fun j => algebraMap Geom GeometricX (S.coeff j)
def coefficientPolynomial (a : Coefficients) : GeometricX[X] :=
  ∑ j : Fin taylorLength, Polynomial.monomial j.val (a j)
def oldCut (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 3)
def oldNext (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 2)
open private compatibility_degree from ProximityPrize.SubmissionLower.Fast048
theorem ordinary_bound (f : Row 3) :
    (oldCut f).totalDegree ≤ 1 + (2 * (taylorLength + 1) - 7) * (f.totalDegree - 1) :=
  compatibility_degree f (taylorLength - 3)
def oldCutIdeal (f : Row 3) : Ideal (GeoRow 3) :=
  Ideal.span {genericRow f, genericRow (oldCut f)}
def properComponents {n : ℕ} (f : Fin n → Row 3) : Finset (CurveIndex n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Whole (f i) then ∅ else
      ((oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i)))).image
        (fun P => (i, P))
theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {i : Fin n}
    {P : Ideal (GeoRow 3)} : (i, P) ∈ properComponents f ↔
    ¬ Whole (f i) ∧ P ∈ (oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i))) := by
  classical
  simp only [properComponents, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hw : Whole (f k)
    · simp [hw] at hk
    · simp only [hw, ite_false] at hk
      obtain ⟨P', hP', he⟩ := Finset.mem_image.mp hk
      cases he
      exact ⟨hw, hP'⟩
  · rintro ⟨hw, hP⟩
    exact ⟨i, by simpa only [hw, ite_false] using Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩
def componentLength (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ∞ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let A := Localization.AtPrime P
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A))
  else 0
def SimpleInvariant (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  componentLength f P = 1 ∧ genericRow (oldNext f) ∈ P
def nextCutLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ regularLocus f P ∧ MvPolynomial.eval y (genericRow (oldNext f)) = 0}
def reconstruct (f : Row 3) (numerator : Fin taylorLength → GeoRow 4)
    (y : Fin 3 → GeometricX) : Coefficients :=
  fun i => MvPolynomial.eval (graphPoint f y) (numerator i) /
    MvPolynomial.eval y (genericRow (separant f)) ^ (taylorLength - 4)
structure LiftedChart (f : Row 3) where
  cut : GeoRow 4
  next : GeoRow 4
  numerator : Fin taylorLength → GeoRow 4
  graph_box : InLiftedBox (graph f) graphBox 1
  cut_box : InLiftedBox cut (liftedBox (taylorLength + 1)) (taylorLength - 1)
  next_box : InLiftedBox next (liftedBox (taylorLength + 2)) taylorLength
  coefficient_box : ∀ i, InLiftedBox (numerator i) (liftedBox taylorLength) (taylorLength - 2)
  cut_represents : RepresentsOnGraph f (oldCut f) cut
  next_represents : RepresentsOnGraph f (oldNext f) next
  actual : ∀ S : Geom[X], S.natDegree ≤ physicalDegree → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S
structure MixedSections {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart (f i)) where
  length : CurveIndex n → ℕ
  degree : CurveIndex n → ℕ
  length_eq : ∀ a ∈ properComponents f, (length a : ℕ∞) = componentLength (f a.1) a.2
  length_pos : ∀ a ∈ properComponents f, 0 < length a
  total : (∑ a ∈ properComponents f, length a * degree a) ≤ mixedBudget
  points : ∀ a ∈ properComponents f, genericRow (oldNext (f a.1)) ∉ a.2 →
    (nextCutLocus (f a.1) a.2).Finite ∧ (nextCutLocus (f a.1) a.2).ncard ≤ degree a
  curves : ∀ a ∈ properComponents f, 2 ≤ length a →
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      0 < degree a ∧ MvPolynomial.affineDegree Q ≤ (degree a : ℚ) ∧
      ∀ y ∈ regularLocus (f a.1) a.2,
        reconstruct (f a.1) (T a.1).numerator y ∈ MvPolynomial.zeroLocus GeometricX Q
structure ActualSolutionCurve (f : Row 3) (Q : CoefficientIdeal) : Prop where
  prime : Q.IsPrime
  dimension : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1
  solves : ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet f (coefficientPolynomial a) = 0
  regular : ∃ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet (separant f) (coefficientPolynomial a) ≠ 0
end
end P0_9_5_1
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
theorem length_le : P0_9.taylorLength ≤ K1_13.taylorLength := by decide
private def dropCoefficients : K1_13_5_4.GeoRow K1_13.taylorLength →ₐ[GeometricX]
    K1_13_5_4.GeoRow P0_9.taylorLength :=
  MvPolynomial.aeval restrictVariables
def pad (Q : P0_9_5_1.CoefficientIdeal) : K1_13_5_4.CoefficientIdeal :=
  Q.comap dropCoefficients
theorem pad_injective : Function.Injective pad :=
  Ideal.comap_injective_of_surjective dropCoefficients
    (fun p => ⟨rename (Fin.castLE length_le) p, restrict_rename length_le p⟩)
theorem pad_hilbert (Q : P0_9_5_1.CoefficientIdeal) :
    affineHilbertPolynomial (pad Q) = affineHilbertPolynomial Q :=
  padded_hilbert length_le Q
theorem pad_degree (Q : P0_9_5_1.CoefficientIdeal) :
    affineDegree (pad Q) = affineDegree Q := by
  unfold affineDegree
  rw [pad_hilbert]
theorem pad_points {Q : P0_9_5_1.CoefficientIdeal} {b : K1_13_5_4.Coefficients}
    (hb : b ∈ zeroLocus GeometricX (pad Q)) :
    let a := b ∘ Fin.castLE length_le
    a ∈ zeroLocus GeometricX Q ∧
      K1_13_5_4.coefficientPolynomial b = P0_9_5_1.coefficientPolynomial a := by
  dsimp only
  constructor
  · intro p hp
    have hv := hb (rename (Fin.castLE length_le) p)
      (show dropCoefficients (rename (Fin.castLE length_le) p) ∈ Q from
        (restrict_rename length_le p).symm ▸ hp)
    change eval b (rename (Fin.castLE length_le) p) = 0 at hv
    rwa [eval_rename] at hv
  · apply sum_monomial_eq_of_tail_zero length_le
    intro i hi
    have hx : MvPolynomial.X i ∈ pad Q := by
      change dropCoefficients (MvPolynomial.X i) ∈ Q
      simp [dropCoefficients, restrictVariables, Nat.not_lt.mpr hi]
    exact (eval_X (f := b) i).symm.trans (hb _ hx)
private def paddedPoint (a : P0_9_5_1.Coefficients) : K1_13_5_4.Coefficients :=
  fun i => if hi : i.val < P0_9.taylorLength then a ⟨i.val, hi⟩ else 0
private theorem eval_paddedPoint (a : P0_9_5_1.Coefficients) :
    MvPolynomial.aeval (paddedPoint a) =
      (MvPolynomial.aeval a).comp dropCoefficients := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i.val < P0_9.taylorLength <;>
    simp [dropCoefficients, restrictVariables, paddedPoint, hi]
theorem pad_actual {f : K1_13.Row 3} {Q : P0_9_5_1.CoefficientIdeal}
    (h : P0_9_5_1.ActualSolutionCurve f Q) : K1_13_5_4.ActualSolutionCurve f (pad Q) := by
  refine ⟨h.prime.comap dropCoefficients, ?_, ?_, ?_⟩
  · rw [pad_hilbert]
    exact h.dimension
  · intro b hb
    obtain ⟨ha, he⟩ := pad_points hb
    rw [he]
    exact h.solves _ ha
  · obtain ⟨a, ha, hs⟩ := h.regular
    have hb : paddedPoint a ∈ zeroLocus GeometricX (pad Q) := by
      intro p hp
      exact (DFunLike.congr_fun (eval_paddedPoint a) p).trans (ha _ hp)
    obtain ⟨_, he⟩ := pad_points hb
    exact ⟨paddedPoint a, hb, by
      have hrestrict : paddedPoint a ∘ Fin.castLE length_le = a := by
        funext i
        simp [paddedPoint, i.isLt]
      rw [he, hrestrict]
      exact hs⟩
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
def LowSupport (P : Ideal CoeffRing) : Prop :=
  ∀ i : CoeffIndex, taylorLength ≤ i.val → MvPolynomial.X i ∈ P
private theorem degree_trajectory {F : Type} [Field F] (k : Geom →+* F) {U : F[X]}
    (hU : U.natDegree < taylorLength) (f : Row 3) (hf : TrueWeightLE f anchorCutoff) :
    (trajectory k U f).natDegree ≤ anchorCutoff := by
  classical
  unfold trajectory
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hprod : (∏ i ∈ m.support, Polynomial.hasseDeriv i.val U ^ m i).natDegree ≤
      m.sum (fun i e => (physicalDegree - i.val) * e) := by
    unfold Finsupp.sum
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    change ((Polynomial.hasseDeriv i.val U) ^ m i).natDegree ≤ (physicalDegree - i.val) * m i
    rw [Nat.mul_comm]
    exact Polynomial.natDegree_pow_le_of_le _ ((Polynomial.natDegree_hasseDeriv_le U i.val).trans
      (Nat.sub_le_sub_right (Nat.le_of_lt_succ hU) _))
  exact (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_map_le hprod).trans (hf m hm)
private theorem reconstruct_solution {F : Type} [Field F] [CharP F K1.p]
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
theorem chart_of_whole (f : Row 3) (hf : Irreducible f)
    (hd : 0 < f.degreeOf 2) (hmax : f.degreeOf 2 ≤ 24)
    (hw : TrueWeightLE f anchorCutoff) (hwhole : Whole f) :
    ∃ P : Ideal CoeffRing, FreshChart P (freshRow f) (freshRow (separant f)) ∧
      LowSupport P ∧ ∀ S : Geom[X], S.natDegree ≤ physicalDegree → RegularAt 2 f S →
        coeffPoint S ∈ MvPolynomial.zeroLocus Geom P := by
  let hp : (chartIdeal f).IsPrime := chart_prime f hf hd
  have hs := separant_regular f hf hd hmax
  have hweight (U : (ChartField f)[X]) (hU : U.natDegree < taylorLength) :
      (trajectory (chartConstants f) U f).natDegree < K1.p :=
    (degree_trajectory _ hU f hw).trans_lt (by decide : anchorCutoff < K1.p)
  obtain ⟨U, hsmall, hsol, hinit⟩ :=
    chart_trajectory f taylorLength (by decide) (by decide) hs hweight hwhole
  have length_le : taylorLength ≤ K1_13.taylorLength := by decide
  have hU := hsmall.trans_le length_le
  obtain ⟨m, v, hv⟩ := K1_13_5_5_1_1.proof f
  let k := chartConstants f
  let point : CoeffIndex → ChartField f := fun a => U.coeff a.val
  let P := RingHom.ker (coeffEval k point)
  have hbase := freshIdeal_eq_ker k point
  have himage := freshJetEval_ker f hf hd U hU hsol hinit
  have hD : onChart f (freshRow (separant f)) ≠ 0 :=
    fun h => hs ((onChart_eq_zero f _).mp h)
  have hUreg : trajectory k U (separant f) ≠ 0 := by
    intro hz
    have h := eval_trajectory k U (chartCenter f) (separant f)
    rw [hz, Polynomial.eval_zero, hinit, rowAt_chart] at h
    exact hD h.symm
  refine ⟨P, ⟨RingHom.ker_isPrime _, ?_, ?_, hs, ?_⟩, ?_, ?_⟩
  · exact fun h => hf.ne_zero (rowMap_injective (h.trans (map_zero _).symm))
  · change (freshIdeal P).comap freshProjection.toRingHom = chartIdeal f
    rw [hbase, RingHom.comap_ker]
    exact himage
  · intro a
    refine ⟨freshRow (v a), m, ?_⟩
    have hU' : (U.map (newConstants : ChartField f →+* NewField (ChartField f))).natDegree <
        K1_13.taylorLength := Polynomial.natDegree_map_le.trans_lt hU
    have hsol' : trajectory (newConstants.comp k) (U.map newConstants) f = 0 := by
      rw [← map_trajectory, hsol, Polynomial.map_zero]
    have hs' : rowAt (newConstants.comp k) newCenter
        (jetAt newCenter (U.map newConstants)) (separant f) ≠ 0 := by
      rw [newTrajectory_eval]
      exact fun h => hUreg ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
    have h := hv (NewField (ChartField f)) (newConstants.comp k) (U.map newConstants) newCenter
      hU' hsol' hs' a
    rw [newTrajectory_eval, newTrajectory_eval, Polynomial.coeff_map,
      ← freshJetEval_row k U hU, ← freshJetEval_row k U hU] at h
    exact fresh_recovered_mem k U a m _ _ h
  · intro a ha
    change coeffEval k point (MvPolynomial.X a) = 0
    rw [coeffEval, MvPolynomial.eval₂Hom_X']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hsmall.trans_le ha)
  · intro S hS hreg
    let e : FreshJetRing →+* ChartField f := onChart f
    let g : FreshJetRing →+* FreshField :=
      MvPolynomial.eval (jetAt freshCenter (S.map freshConstants))
    let b : Geom →+* FreshJetRing := MvPolynomial.C.comp freshConstants
    have hg (q : Row 3) : g (freshRow q) = algebraMap Geom[X] FreshField (atJet q S) := by
      rw [← actual_eval, actual_eval_fresh]
      rfl
    have hreg' : g (freshRow (separant f)) ≠ 0 := by
      rw [hg]
      exact fun h => hreg.2 ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
    have hker : RingHom.ker e ≤ RingHom.ker g := by
      rw [show RingHom.ker e = chartIdeal f by
        ext q
        exact onChart_eq_zero f q]
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker, hg, hreg.1, map_zero]
    have hS' : (S.map freshConstants).natDegree < K1_13.taylorLength :=
      Polynomial.natDegree_map_le.trans_lt ((Nat.lt_succ_of_le hS).trans_le length_le)
    have hsolS : trajectory freshConstants (S.map freshConstants) f = 0 := by
      simpa only [trajectory_actual, hreg.1, Polynomial.map_zero, RingHom.comp_id] using
        (map_trajectory (RingHom.id Geom) freshConstants S f).symm
    have hrecU (a : CoeffIndex) :
        e (freshRow (separant f)) ^ m * point a = e (freshRow (v a)) := by
      have hc := hv (ChartField f) k U (chartCenter f) hU hsol
        (by rwa [hinit, rowAt_chart]) a
      rwa [hinit, rowAt_chart] at hc
    have hrecS (a : CoeffIndex) :
        g (freshRow (separant f)) ^ m * freshConstants (S.coeff a.val) = g (freshRow (v a)) := by
      have hc := hv FreshField freshConstants (S.map freshConstants) freshCenter hS' hsolS
        (by rwa [actual_eval_fresh]) a
      rwa [actual_eval_fresh, Polynomial.coeff_map] at hc
    have hle := eval_kernel_le_of_cleared b e g hker (freshRow (separant f)) m
      (fun a => freshRow (v a)) hD hreg' point (freshConstants ∘ coeffPoint S) hrecU hrecS
    intro q hq
    have hz := hle hq
    change MvPolynomial.eval₂Hom (g.comp b) (freshConstants ∘ coeffPoint S) q = 0 at hz
    have hqmap : MvPolynomial.eval₂Hom (g.comp b) (freshConstants ∘ coeffPoint S) =
        freshConstants.comp (MvPolynomial.aeval (coeffPoint S)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [b, g]
      · intro a
        simp
    rw [hqmap] at hz
    exact freshConstants.injective (hz.trans (map_zero _).symm)
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
private theorem square_dvd_trimmed_pow {A : Type} [CommRing A] [IsDomain A]
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
private theorem supported_height (Q : Ideal CoeffRing) (L : Fin 2 → FreshJetRing)
    (hQ : Q.IsPrime) (hhom : Q.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom))
    (hdim : (affineHilbertPolynomial Q).natDegree = 2)
    (hL : FiniteJetPair L (jetImage (freshIdeal Q))) (hlow : LowSupport Q) :
    2 * affineDegree Q ≤
      (physicalDegree : ℚ) * (genericFiberDimension L (freshIdeal Q) : ℚ) := by
  have h1 := K1_13_5_5_2_1_1.of_children K1_13_5_5_2_1_1_1.proof
    K1_13_5_5_2_1_1_2.proof K1_13_5_5_2_1_1_3.proof
  have h2 := K1_13_5_5_2_1_2.proof
  have h3 := K1_13_5_5_2_1_3.proof
  have h4 := K1_13_5_5_2_1_4.of_children K1_13_5_5_2_1_4_1.proof K1_13_5_5_2_1_4_2.proof
  have h5 := K1_13_5_5_2_1_5.proof
  have h6 := K1_13_5_5_2_1_6.proof
  obtain ⟨i, hi, hchart, hmonic, hdegree⟩ := monic_chart_aux Q hQ hhom (by omega)
  have hid : i.val ≤ physicalDegree :=
    Nat.le_of_lt_succ (lt_of_not_ge (fun h => hi (hlow i h)))
  let : IsDomain (ChartRing Q i) := hchart
  obtain ⟨a, ha, ⟨s⟩⟩ := h2 (ChartRing Q i) (direction Q i) hmonic ((hdegree.trans hid).trans (by decide))
  obtain ⟨hdom, heval, hfinite, hcoeff⟩ := h1 Q i a hQ hhom hdim hi hchart ha
  let : IsDomain (FreshOpen Q i a) := hdom
  let : IsDomain (OpenRing Q i a) := IsLocalization.Away.isDomain _ ha
  change Factorization (openDirection Q i a) at s
  obtain ⟨q, hq0, hq, hqspan⟩ := h3 (OpenRing Q i a) (openDirection Q i a) s
  let e : (OpenRing Q i a)[X] →+* FreshOpen Q i a := freshEval (OpenRing Q i a)
  let x := e (openDirection Q i a)
  let b := e (commonFactor s)
  let d : Fin 3 → FreshOpen Q i a := fun j => e (q j)
  have hx : x ≠ 0 := by
    simpa only [e, x, openDirection, map_zero] using
      heval.ne (hmonic.map (algebraMap _ (OpenRing Q i a))).ne_zero
  have hb : b ≠ 0 := by
    simpa only [e, b, map_zero] using heval.ne (commonFactor_monic s).ne_zero
  have hd : d 0 ≠ 0 := by
    simpa only [d, hq0, e, map_zero] using heval.ne (trimmedValue_monic s).ne_zero
  have htrim : ∀ j, b * d j = e (Polynomial.hasseDeriv j.val (openDirection Q i a)) := by
    intro j
    exact (e.map_mul _ _).symm.trans (congrArg e (hq j))
  have hspan : Ideal.span (Set.range d) = ⊤ := by
    have hm := congrArg (Ideal.map e) hqspan
    rwa [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at hm
  let : Module.Finite FreshField (PrincipalQuot x) := hfinite
  have hdegree' : (openDirection Q i a).natDegree ≤ physicalDegree :=
    Polynomial.natDegree_map_le.trans (hdegree.trans hid)
  have hdiv := eval_divisions e s hdegree' (by decide)
  have hdeq : d 0 = e (trimmedValue s) := congrArg e hq0
  rw [← hdeq] at hdiv
  obtain ⟨hdfin, hlen⟩ := length_bound x (d 0) physicalDegree hx hd hdiv.1 hdiv.2
  rw [← hcoeff]
  have hlenQ : 2 * (Module.finrank FreshField (PrincipalQuot x) : ℚ) ≤
      (physicalDegree : ℚ) * (Module.finrank FreshField (PrincipalQuot (d 0)) : ℚ) := by
    exact_mod_cast hlen
  by_cases hu : IsUnit (d 0)
  · have hzero : Module.finrank FreshField (PrincipalQuot (d 0)) = 0 := by
      have : Subsingleton (PrincipalQuot (d 0)) :=
        Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
      exact Module.finrank_zero_of_subsingleton
    exact hlenQ.trans (by rw [hzero, Nat.cast_zero, mul_zero]; positivity)
  · obtain ⟨hk, hcomparison⟩ := h4 Q i a hQ hhom hdim hi hchart ha hdom b d hb htrim
    obtain ⟨hpairfin, hrank⟩ := hcomparison L hL
    have hL' : FiniteJetPair L (coneJetIdeal d) := hk ▸ hL
    obtain ⟨M, w, hM, hMw, hinj, hw⟩ := h5 _ d L hd hu hspan hL'
    obtain ⟨hwfin, hwRank⟩ := h6 _ d L M hL' hpairfin hM hinj
    rw [hMw] at hwfin hwRank hinj
    let : Module.Finite PairField (pairFiber (valuePairMap (d 0) w)) := hwfin
    let : Module.Finite FreshField (PrincipalQuot (d 0)) := hdfin
    have hbound := pin_bound (d 0) w hw hinj
    rw [hwRank, hrank] at hbound
    exact hlenQ.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hbound)
      (Nat.cast_nonneg physicalDegree))
theorem chart_degree (P : Ideal CoeffRing) (g d : FreshJetRing)
    (hchart : FreshChart P g d) (hlow : LowSupport P) :
    (affineHilbertPolynomial P).natDegree = 2 ∧
      2 * affineDegree P ≤ (physicalDegree : ℚ) * (g.totalDegree : ℚ) := by
  have hdim := K1_13_5_5_2.chart_dimension P g d hchart
  refine ⟨hdim, ?_⟩
  have h2 := K1_13_5_5_2_2.of_children K1_13_5_5_2_2_1.proof K1_13_5_5_2_2_2.proof
  have h3 := K1_13_5_5_2_3.of_children K1_13_5_5_2_3_1.proof
    K1_13_5_5_2_3_2.proof K1_13_5_5_2_3_3.proof
  obtain ⟨n, Q, hQ, hdeg, hfiber⟩ := h2 P hchart.prime hdim
  obtain ⟨L, hL, hfinite, hbudget⟩ := h3 P g d hchart
  have htail : LowSupport (infinityIdeal P) := by
    intro i hi
    change MvPolynomial.X i ∈ Ideal.span _
    apply Ideal.subset_span
    refine ⟨MvPolynomial.X i, hlow i hi, ?_⟩
    change homogeneousComponent (MvPolynomial.X (R := Geom) i).totalDegree
      (MvPolynomial.X i) = MvPolynomial.X i
    rw [totalDegree_X]
    exact homogeneousComponent_eq_self (isHomogeneous_X Geom i)
  have hcurve (i : Fin n) : 2 * affineDegree (Q i) ≤
      (physicalDegree : ℚ) * (genericFiberDimension L (freshIdeal (Q i)) : ℚ) := by
    obtain ⟨hi, hhom, hd⟩ := hQ i
    have hle : jetImage (freshIdeal (infinityIdeal P)) ≤ jetImage (freshIdeal (Q i)) :=
      Ideal.comap_mono (Ideal.map_mono hi.le)
    exact supported_height (Q i) L hi.isPrime hhom hd (hL.of_le hle)
      (fun j hj => hi.le (htail j hj))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcurve i)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [hdeg]
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg physicalDegree))
  exact_mod_cast (hfiber L hfinite).trans hbudget
end
end P0_9_5_2
end
