import ProximityPrize.SubmissionLower.Fast069
import ProximityPrize.SubmissionLower.Fast075
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_10_1
noncomputable section
open MvPolynomial K1_11
def scalarVariables : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  Equiv.ofBijective ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1] (by decide)
variable {F : Type*} [Field F]
def groupSeeds : MvPolynomial (Fin 4) F ≃+* MvPolynomial (Fin 2) (MvPolynomial (Fin 2) F) :=
  (renameEquiv F scalarVariables).toRingEquiv.trans (sumRingEquiv F (Fin 2) (Fin 2))
private def joinExponents (e f : Fin 2 →₀ ℕ) : Fin 4 →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, f)).mapDomain scalarVariables.symm
private theorem joinExponents_apply (e f : Fin 2 →₀ ℕ) :
    joinExponents e f 0 = e 0 ∧ joinExponents e f 1 = e 1 ∧
      joinExponents e f 2 = f 0 ∧ joinExponents e f 3 = f 1 := by
  simp [joinExponents, scalarVariables]
private theorem grouped_coeff (Q : MvPolynomial (Fin 4) F) (e f : Fin 2 →₀ ℕ) :
    ((groupSeeds Q).coeff e).coeff f = Q.coeff (joinExponents e f) := by
  classical
  let g := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, f)
  have hg : (joinExponents e f).mapDomain scalarVariables = g := by
    have he : (scalarVariables : Fin 4 → Fin 2 ⊕ Fin 2) ∘ scalarVariables.symm = id :=
      funext scalarVariables.apply_symm_apply
    rw [joinExponents, ← Finsupp.mapDomain_comp, he, Finsupp.mapDomain_id]
  rw [← coeff_rename_mapDomain scalarVariables scalarVariables.injective, hg]
  change ((sumRingEquiv F (Fin 2) (Fin 2) (rename scalarVariables Q)).coeff e).coeff f =
    (rename scalarVariables Q).coeff g
  generalize rename scalarVariables Q = P
  induction P using MvPolynomial.induction_on' with
  | add P R hp hr => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hr]
  | monomial a b =>
    change ((AddMonoidAlgebra.curryRingEquiv
        (AddMonoidAlgebra.mapDomainRingEquiv F Finsupp.sumFinsuppAddEquivProdFinsupp
          (AddMonoidAlgebra.single a b))).coeff e).coeff f = _
    rw [AddMonoidAlgebra.mapDomainRingEquiv_single]
    generalize hpair : Finsupp.sumFinsuppAddEquivProdFinsupp a = pair
    rcases pair with ⟨i,j⟩
    rw [AddMonoidAlgebra.curryRingEquiv_single]
    change ((monomial i (monomial j b)).coeff e).coeff f = (monomial a b).coeff g
    have ha : a = g ↔ i = e ∧ j = f := by
      rw [← Finsupp.sumFinsuppAddEquivProdFinsupp.injective.eq_iff, hpair,
        show Finsupp.sumFinsuppAddEquivProdFinsupp g = (e, f) from AddEquiv.apply_symm_apply _ _, Prod.mk.injEq]
    by_cases hi : i = e <;> by_cases hj : j = f <;> simp [coeff_monomial, ha, hi, hj]
private theorem group_eval (Q : MvPolynomial (Fin 4) F) (P : Polynomial F) (s t : F) :
    aeval ![Polynomial.X, P] ((groupSeeds Q).map (eval ![s,t])) =
      aeval (scalarImages P s t) Q := by
  let lhs := (aeval ![Polynomial.X, P]).toRingHom.comp
    ((map (eval ![s,t])).comp (groupSeeds (F:=F)).toRingHom)
  have heq : lhs = (aeval (scalarImages P s t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, groupSeeds]
    · intro i
      fin_cases i <;> simp [lhs, groupSeeds, scalarVariables, scalarImages]
  exact RingHom.congr_fun heq Q
def toScalarSource (Q : MvPolynomial (Fin 4) K1.K) (hn : Q ≠ 0)
    (hy : Q.weightedTotalDegree scalarWeightY ≤ 5)
    (hs : Q.weightedTotalDegree scalarWeightYS ≤ 26)
    (ht : Q.weightedTotalDegree scalarWeightT ≤ 21)
    (htot : Q.weightedTotalDegree scalarWeightTotal ≤ 37) : K1_10.ScalarSource := by
  have bounds (e f : Fin 2 →₀ ℕ) (hf : f ∈ ((groupSeeds Q).coeff e).support) :
      e 1 ≤ 5 ∧ f 0 ≤ 26 ∧ f 1 ≤ 21 ∧ e 1 + (f 0 + f 1) ≤ 37 := by
    have he : joinExponents e f ∈ Q.support := by
      rw [MvPolynomial.mem_support_iff, ← grouped_coeff]
      exact MvPolynomial.mem_support_iff.mp hf
    have ⟨h0,h1,h2,h3⟩ := joinExponents_apply e f
    have hy' := (le_weightedTotalDegree scalarWeightY he).trans hy
    have hs' := (le_weightedTotalDegree scalarWeightYS he).trans hs
    have ht' := (le_weightedTotalDegree scalarWeightT he).trans ht
    have htot' := (le_weightedTotalDegree scalarWeightTotal he).trans htot
    simp [scalarWeightY, scalarWeightYS, scalarWeightT, scalarWeightTotal,
      Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ,
      h0,h1,h2,h3, smul_eq_mul] at hy' hs' ht' htot'
    omega
  refine ⟨groupSeeds Q, (map_ne_zero_iff (groupSeeds (F:=K1.K)).toRingHom
    (groupSeeds (F:=K1.K)).injective).mpr hn, ?_, ?_, ?_, ?_⟩
  · rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro e he
    obtain ⟨f,hf⟩ := support_nonempty.mpr (MvPolynomial.mem_support_iff.mp he)
    exact (bounds e f hf).1
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf => (bounds e f hf).2.1)
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf => (bounds e f hf).2.2.1)
  · intro e he
    have hcoeff := MvPolynomial.mem_support_iff.mp he
    obtain ⟨f,hf⟩ := support_nonempty.mpr hcoeff
    have he' := (bounds e f hf).2.2.2
    have hb : ((groupSeeds Q).coeff e).totalDegree ≤ 37 - e 1 := by
      apply Finset.sup_le
      intro g hg
      have hh := (bounds e g hg).2.2.2
      simp [Finsupp.sum_fintype, Fin.sum_univ_succ]
      omega
    omega
theorem toScalarSource_atDecoder (Q : MvPolynomial (Fin 4) K1.K) (hn) (hy) (hs) (ht) (htot)
    (γ : K1.K) (P : Polynomial K1.K) :
    (toScalarSource Q hn hy hs ht htot).atDecoder γ P =
      aeval (scalarImages P γ (γ ^ K1.p)) Q := group_eval Q P γ (γ ^ K1.p)
end
end K1_10_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_10_1
noncomputable section
open K1 K1_10 K1_11 MvPolynomial
def c1 : Prop :=
  ∀ u deleted h U V (W : Plane u deleted h U V),
    ∀ j, (planeRelation U V W.output).weightedTotalDegree (sourceWeights 131071 j) =
      relationBounds h j
def c2 : Prop :=
  ∀ u deleted h U V (W : Plane u deleted h U V), ∀ i ∉ deleted,
    (contactLift contactWeight (shiftAt u i (planeRelation U V W.output))).natTrailingDegree = 1
def c3 : Prop :=
  ∀ u deleted h U V (W : Plane u deleted h U V),
    (Polynomial.C (denominator V) * Polynomial.X - Polynomial.C (numerator U W.output)).IsPrimitive
end
end K1_10_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_10_1_2
noncomputable section
open K1 K1_10 K1_10_1 K1_11 K1_11_2 MvPolynomial
abbrev PlanePoly := MvPolynomial (Fin 5) K
private def ordinary : Polynomial K →+* PlanePoly :=
  Polynomial.eval₂RingHom C (MvPolynomial.X 0)
def planePencil (A : Fin 2 → Polynomial K) (z : PlanePoly) : PlanePoly :=
  ordinary (A 0) + z * ordinary (A 1)
def planeOutput (O : Fin 2 → Fin 2 → Polynomial K) : PlanePoly :=
  planePencil (fun j => O j 0) (MvPolynomial.X 3) +
    MvPolynomial.X 4 * planePencil (fun j => O j 1) (MvPolynomial.X 3)
theorem view_ordinary (Q : Polynomial K) :
    polynomialView (ordinary Q) = Polynomial.C (liftOrdinary Q) := by
  have hh : (polynomialView (F := K)).toRingHom.comp ordinary =
      Polynomial.C.comp liftOrdinary := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [ordinary, liftOrdinary, polynomialView, finSuccEquiv_apply]
    · simp [ordinary, liftOrdinary, polynomialView_X]
  exact RingHom.congr_fun hh Q
theorem relation_eq (U V : Fin 2 → Polynomial K)
    (O : Fin 2 → Fin 2 → Polynomial K) :
    planeRelation U V O =
      planePencil U (MvPolynomial.X 4) * MvPolynomial.X 1 +
      planePencil V (MvPolynomial.X 3) * MvPolynomial.X 2 - planeOutput O := by
  apply polynomialView.injective
  simp only [planeRelation_view, planePencil, planeOutput, map_sub, map_add, map_mul,
    view_ordinary, polynomialView_X]
  change _ = (Polynomial.C (liftOrdinary (U 0)) +
      Polynomial.C (MvPolynomial.X 3) * Polynomial.C (liftOrdinary (U 1))) * Polynomial.C (MvPolynomial.X 1) +
      (Polynomial.C (liftOrdinary (V 0)) +
      Polynomial.C (MvPolynomial.X 2) * Polynomial.C (liftOrdinary (V 1))) * Polynomial.X -
      ((Polynomial.C (liftOrdinary (O 0 0)) +
      Polynomial.C (MvPolynomial.X 2) * Polynomial.C (liftOrdinary (O 1 0))) +
      Polynomial.C (MvPolynomial.X 3) * (Polynomial.C (liftOrdinary (O 0 1)) +
      Polynomial.C (MvPolynomial.X 2) * Polynomial.C (liftOrdinary (O 1 1))))
  simp only [denominator, numerator, pencil, map_sub, map_add, map_mul]
  ring
theorem omits_add {P Q : PlanePoly} (hp : OmitsMessages P) (hq : OmitsMessages Q) :
    OmitsMessages (P + Q) := by
  constructor
  · exact Nat.eq_zero_of_le_zero (by simpa only [hp.1, hq.1, max_self] using degreeOf_add_le 1 P Q)
  · exact Nat.eq_zero_of_le_zero (by simpa only [hp.2, hq.2, max_self] using degreeOf_add_le 2 P Q)
theorem omits_mul {P Q : PlanePoly} (hp : OmitsMessages P) (hq : OmitsMessages Q) :
    OmitsMessages (P * Q) := by
  constructor
  · exact Nat.eq_zero_of_le_zero (by simpa only [hp.1, hq.1, Nat.add_zero] using degreeOf_mul_le 1 P Q)
  · exact Nat.eq_zero_of_le_zero (by simpa only [hp.2, hq.2, Nat.add_zero] using degreeOf_mul_le 2 P Q)
theorem omits_ordinary (Q : Polynomial K) : OmitsMessages (ordinary Q) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq =>
    rw [map_add]
    exact omits_add hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    simp only [ordinary, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
    apply omits_mul
    · exact ⟨degreeOf_C _ _, degreeOf_C _ _⟩
    · exact ⟨degreeOf_X_pow_of_ne _ (by decide), degreeOf_X_pow_of_ne _ (by decide)⟩
theorem omits_pencil (A : Fin 2 → Polynomial K) {z : PlanePoly}
    (hz : OmitsMessages z) : OmitsMessages (planePencil A z) :=
  omits_add (omits_ordinary _) (omits_mul hz (omits_ordinary _))
theorem omits_seed (j : Fin 5) (h1 : (1 : Fin 5) ≠ j) (h2 : (2 : Fin 5) ≠ j) :
    OmitsMessages (MvPolynomial.X j : PlanePoly) :=
  ⟨degreeOf_X_of_ne h1, degreeOf_X_of_ne h2⟩
theorem node_ordinary (x a b c d : K) (Q : Polynomial K) :
    nodeWordMap x a b c d (ordinary Q) = C (Q.eval x) := by
  have hh : (nodeWordMap x a b c d).toRingHom.comp ordinary =
      C.comp (Polynomial.evalRingHom x) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [ordinary, nodeWordMap]
    · simp [ordinary, nodeWordMap, nodeWordImages]
  exact RingHom.congr_fun hh Q
theorem node_pencil (x a b c d : K) (A : Fin 2 → Polynomial K)
    (j : Fin 5) (hj : j = 3 ∨ j = 4) :
    nodeWordMap x a b c d (planePencil A (MvPolynomial.X j)) =
      C ((A 0).eval x) + MvPolynomial.X j * C ((A 1).eval x) := by
  simp only [planePencil, map_add, map_mul, node_ordinary]
  rcases hj with rfl | rfl <;> simp [nodeWordMap, nodeWordImages]
theorem node_relation {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (i : I) (hi : i ∉ deleted) :
    nodeWordMap (node i) (u 0 i) (u 1 i) (u 0 i ^ p) (u 1 i ^ p)
      (planePencil U (MvPolynomial.X 4) * MvPolynomial.X 1 +
        planePencil V (MvPolynomial.X 3) * MvPolynomial.X 2 - planeOutput W.output) = 0 := by
  simp only [planeOutput, map_add, map_mul, map_sub, node_pencil _ _ _ _ _ _ _ (Or.inl rfl),
    node_pencil _ _ _ _ _ _ _ (Or.inr rfl)]
  simp only [nodeWordMap, aeval_X, nodeWordImages, Matrix.cons_val]
  have hnode (j l : Fin 2) :
      C ((U l).eval (node i)) * C (u j i) + C ((V j).eval (node i)) * C (u l i ^ p) =
        (C ((W.output j l).eval (node i)) : PlanePoly) := by
    simpa only [map_add, map_mul] using congrArg (C : K →+* PlanePoly) (W.nodes i hi j l)
  linear_combination hnode 0 0 + MvPolynomial.X 3 * hnode 1 0 + MvPolynomial.X 4 * hnode 0 1 +
    (MvPolynomial.X 3 * MvPolynomial.X 4) * hnode 1 1
theorem affine_coefficients_zero (j : Fin 5) (a b : K)
    (hz : C a + MvPolynomial.X j * C b = (0 : PlanePoly)) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    simpa using congrArg (MvPolynomial.eval (fun _ : Fin 5 => (0 : K))) hz
  have hb : b = 0 := by
    simpa [ha] using congrArg (MvPolynomial.eval (fun _ : Fin 5 => (1 : K))) hz
  exact ⟨ha, hb⟩
theorem node_pencils_ne {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (i : I) :
    nodeWordMap (node i) (u 0 i) (u 1 i) (u 0 i ^ p) (u 1 i ^ p)
      (planePencil U (MvPolynomial.X 4)) ≠ 0 ∨
    nodeWordMap (node i) (u 0 i) (u 1 i) (u 0 i ^ p) (u 1 i ^ p)
      (planePencil V (MvPolynomial.X 3)) ≠ 0 := by
  by_contra! hz
  rw [node_pencil _ _ _ _ _ _ _ (Or.inr rfl), node_pencil _ _ _ _ _ _ _ (Or.inl rfl)] at hz
  have hu := affine_coefficients_zero _ _ _ hz.1
  have hv := affine_coefficients_zero _ _ _ hz.2
  apply Polynomial.not_isUnit_X_sub_C (node i)
  apply W.primitive
  · intro l
    apply Polynomial.dvd_iff_isRoot.mpr
    fin_cases l
    · exact hu.1
    · exact hu.2
  · intro j
    apply Polynomial.dvd_iff_isRoot.mpr
    fin_cases j
    · exact hv.1
    · exact hv.2
theorem proof : K1_10_1.c2 := by
  intro u deleted h U V W i hi
  rw [shiftAt, relation_eq]
  have hs := omits_seed 3 (by decide) (by decide)
  have ht := omits_seed 4 (by decide) (by decide)
  apply linear_relation_node_contact_one _ _ _ _ _
    _ _ _ (omits_pencil U ht) (omits_pencil V hs)
    (omits_add (omits_pencil _ hs) (omits_mul ht (omits_pencil _ hs)))
  · rw [contactConstant_shift]
    simpa only [planeOutput] using node_relation W i hi
  · simpa only [contactConstant_shift] using node_pencils_ne W i
end
end K1_10_1_2
end
section
set_option autoImplicit false
namespace K1_10_1_3
noncomputable section
open K1 K1_10 K1_10_1 MvPolynomial
private abbrev R := MvPolynomial (Fin 4) K
theorem lift_degree_zero (Q : Polynomial K) {i : Fin 4} (hi : i ≠ 0) :
    (liftOrdinary Q).degreeOf i = 0 := by
  induction Q using Polynomial.induction_on' with
  | monomial n a =>
    change (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (Polynomial.monomial n a)).degreeOf i = 0
    rw [Polynomial.eval₂_monomial]
    exact Nat.eq_zero_of_le_zero ((degreeOf_mul_le i _ _).trans_eq (by
      rw [degreeOf_C, degreeOf_X_pow_of_ne n hi, Nat.zero_add]))
  | add P Q hP hQ =>
    rw [map_add]
    exact Nat.eq_zero_of_le_zero ((degreeOf_add_le i _ _).trans_eq (by simp [hP, hQ]))
theorem pencil_degree_zero (A : Fin 2 → Polynomial K) {i j : Fin 4}
    (hi : i ≠ 0) (hij : i ≠ j) : (pencil A (MvPolynomial.X j)).degreeOf i = 0 := by
  have hm := degreeOf_mul_le i (MvPolynomial.X j : R) (liftOrdinary (A 1))
  rw [degreeOf_X_of_ne hij, lift_degree_zero _ hi, Nat.zero_add] at hm
  exact Nat.eq_zero_of_le_zero ((degreeOf_add_le i _ _).trans_eq (by
    rw [lift_degree_zero _ hi, Nat.eq_zero_of_le_zero hm, max_self]))
private theorem eval_lift (v : Fin 4 → Polynomial K) (hv : v 0 = Polynomial.X)
    (Q : Polynomial K) : aeval v (liftOrdinary Q) = Q := by
  have hh : (aeval v).toRingHom.comp liftOrdinary = RingHom.id (Polynomial K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [liftOrdinary]
    · simp [liftOrdinary, hv]
  exact RingHom.congr_fun hh Q
theorem dvd_pencil_coeffs (d : R) (f : Polynomial K)
    (heval : ∀ v : Fin 4 → Polynomial K, v 0 = Polynomial.X → aeval v d = f)
    (A : Fin 2 → Polynomial K) {i : Fin 4} (hi : i ≠ 0)
    (hd : d ∣ pencil A (MvPolynomial.X i)) : ∀ j, f ∣ A j := by
  have hval (z : Polynomial K) : f ∣ A 0 + z * A 1 := by
    let v := Function.update (K1_11.scalarImages (F := K) 0 0 0) i z
    have hv : v 0 = Polynomial.X := by
      simp only [v, Function.update_of_ne (Ne.symm hi)]
      rfl
    have hvi : v i = z := Function.update_self _ _ _
    have h := (aeval v).toRingHom.map_dvd hd
    change aeval v d ∣ aeval v (pencil A (MvPolynomial.X i)) at h
    simpa only [heval v hv, pencil, map_add, map_mul, aeval_X, eval_lift v hv, hvi] using h
  have h0 : f ∣ A 0 := by simpa using hval 0
  have h1 : f ∣ A 1 := by simpa using dvd_sub (hval 1) h0
  intro j
  fin_cases j
  · exact h0
  · exact h1
theorem pencil_ne (A : Fin 2 → Polynomial K) (hA : ∃ j, A j ≠ 0)
    {i : Fin 4} (hi : i ≠ 0) : pencil A (MvPolynomial.X i) ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := hA
  apply hj
  have hd : (0 : R) ∣ pencil A (MvPolynomial.X i) := zero_dvd_iff.mpr h
  exact zero_dvd_iff.mp (dvd_pencil_coeffs 0 0 (by simp) A hi hd j)
theorem divisor_degree_zero {d P : R} (hd : d ∣ P) (hP : P ≠ 0)
    {i : Fin 4} (hi : P.degreeOf i = 0) : d.degreeOf i = 0 := by
  obtain ⟨q, rfl⟩ := hd
  have he : (d * q).degreeOf i = d.degreeOf i + q.degreeOf i :=
    degreeOf_mul_eq (left_ne_zero_of_mul hP) (right_ne_zero_of_mul hP)
  omega
theorem deriv_zero_of_degree_zero {d : R} {i : Fin 4}
    (h : d.degreeOf i = 0) : pderiv i d = 0 :=
  pderiv_eq_zero_of_notMem_vars (fun hi => (mem_vars_iff_degreeOf_ne_zero.mp hi) h)
theorem lift_of_degree_zero (d : R) (h : ∀ i ≠ 0, d.degreeOf i = 0) :
    ∃ f : Polynomial K, liftOrdinary f = d := by
  let v := K1_11.scalarImages (F := K) 0 0 0
  refine ⟨aeval v d, ?_⟩
  change (liftOrdinary.comp (aeval v).toRingHom) d = (RingHom.id R) d
  apply hom_congr_vars
  · ext a
    simp [liftOrdinary]
  · intro i hi _
    have h0 : i = 0 := by
      by_contra hn
      exact (mem_vars_iff_degreeOf_ne_zero.mp hi) (h i hn)
    subst i
    simp [liftOrdinary, v, K1_11.scalarImages]
  · rfl
theorem proof : K1_10_1.c3 := by
  intro u deleted h U V W
  apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro d hd
  have hc := (Polynomial.C_dvd_iff_dvd_coeff d _).mp hd
  have hdV : d ∣ denominator V := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] using hc 1
  have hdN : d ∣ numerator U W.output := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] using hc 0
  have hV : denominator V ≠ 0 := pencil_ne V W.V_ne (by decide)
  have hy : d.degreeOf 1 = 0 :=
    divisor_degree_zero hdV hV (pencil_degree_zero V (by decide) (by decide))
  have ht : d.degreeOf 3 = 0 :=
    divisor_degree_zero hdV hV (pencil_degree_zero V (by decide) (by decide))
  have hderiv (A : Fin 2 → Polynomial K) (i : Fin 4) (hi : (1 : Fin 4) ≠ i) :
      pderiv 1 (pencil A (MvPolynomial.X i)) = 0 :=
    deriv_zero_of_degree_zero (pencil_degree_zero A (by decide) hi)
  have hdU : d ∣ pencil U (MvPolynomial.X 3) := by
    obtain ⟨q, hq⟩ := hdN
    have he : -(pencil U (MvPolynomial.X 3)) = d * pderiv 1 q := by
      simpa [numerator, pderiv_mul, hderiv _ 2 (by decide), hderiv _ 3 (by decide),
        pderiv_X_of_ne (by decide : (3 : Fin 4) ≠ 1),
        deriv_zero_of_degree_zero hy] using congrArg (pderiv (R := K) (1 : Fin 4)) hq
    exact ⟨-pderiv 1 q, by rw [mul_neg, ← he, neg_neg]⟩
  have hU : pencil U (MvPolynomial.X 3) ≠ 0 := pencil_ne U W.U_ne (by decide)
  have hs : d.degreeOf 2 = 0 :=
    divisor_degree_zero hdU hU (pencil_degree_zero U (by decide) (by decide))
  obtain ⟨f, hf⟩ := lift_of_degree_zero d (by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact hy
    · exact hs
    · exact ht)
  have heval (v : Fin 4 → Polynomial K) (hv : v 0 = Polynomial.X) :
      aeval v d = f := by rw [← hf, eval_lift v hv]
  rw [← hf]
  exact (W.primitive f
    (dvd_pencil_coeffs d f heval U (by decide) hdU)
    (dvd_pencil_coeffs d f heval V (by decide) hdV)).map liftOrdinary
end
end K1_10_1_3
end
section
set_option autoImplicit false
namespace K1_13_7_6_2
noncomputable section
open K1_13_7 K1_13_7_6
open scoped BigOperators
def c1 : Prop :=
  ∀ (f g h : Lower) (y : LowerPoint) (q : PrimeSpectrum Lower),
    q.asIdeal = pointIdeal y →
    q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes →
    f ≠ 0 ∧ RegularCut q (Ideal.span {f, g}) h ∧
      ∀ r ∈ precedingPrimes (Ideal.span {f, g}) q, RegularCut r (Ideal.span {f}) g
def c2 : Prop :=
  ∀ (J : Ideal Lower) (t : Lower) (q : PrimeSpectrum Lower),
    q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes →
    RegularCut q J t →
    (localColength q (J ⊔ Ideal.span {t})).toNat =
      ∑ p ∈ precedingPrimes J q,
        (localColength p J).toNat * (localColength q (cutIdeal p t)).toNat
theorem span_pair (f g : Lower) :
    Ideal.span ({f, g} : Set Lower) = Ideal.span {f} ⊔ Ideal.span {g} := by
  rw [← Ideal.span_union]
  congr 1
theorem span_triple (f g h : Lower) :
    Ideal.span ({f, g, h} : Set Lower) = Ideal.span {f, g} ⊔ Ideal.span {h} := by
  rw [← Ideal.span_union]
  congr 1
  ext t
  simp [or_left_comm, or_comm]
theorem cut_of_preceding {J : Ideal Lower} {t : Lower}
    {q p : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hreg : RegularCut q J t) (hp : p ∈ precedingPrimes J q) :
    t ∉ p.asIdeal ∧ q.asIdeal ∈ (cutIdeal p t).minimalPrimes := by
  obtain ⟨hpJ, hpq⟩ := (mem_precedingPrimes J q p).mp hp
  let A := Localization.AtPrime q.asIdeal
  let a : Lower →+* A := algebraMap Lower A
  have hdisj : Disjoint (q.asIdeal.primeCompl : Set Lower) (p.asIdeal : Set Lower) :=
    Set.disjoint_left.mpr (fun _ hx hxp => hx (hpq hxp))
  have hcomap : (p.asIdeal.map a).under Lower = p.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A p.isPrime hdisj
  have hmin : p.asIdeal.map a ∈ (J.map a).minimalPrimes := by
    change p.asIdeal.map a ∈ (J.map (algebraMap Lower A)).minimalPrimes
    rw [IsLocalization.minimalPrimes_map q.asIdeal.primeCompl A, Set.mem_preimage, hcomap]
    exact hpJ
  change IsSMulRegular (A ⧸ J.map a) (a t) at hreg
  have hmin' : p.asIdeal.map a ∈ (Module.annihilator A (A ⧸ J.map a)).minimalPrimes := by
    rwa [Ideal.annihilator_quotient]
  refine ⟨fun ht => (hreg.notMem_of_mem_minimalPrimes hmin') (Ideal.mem_map_of_mem a ht), ?_⟩
  have htq : Ideal.span {t} ≤ q.asIdeal := le_sup_right.trans hq.le
  refine ⟨⟨q.isPrime, sup_le hpq htq⟩, ?_⟩
  intro s hs hsq
  exact hq.2 ⟨hs.1, sup_le (hpJ.le.trans (le_sup_left.trans hs.2))
    (le_sup_right.trans hs.2)⟩ hsq
theorem pointPrime_injective : Function.Injective K1_13_7_4.pointPrime := by
  intro y z hyz
  have heq : pointIdeal y = pointIdeal z := congrArg PrimeSpectrum.asIdeal hyz
  funext i
  have hm : MvPolynomial.X i - MvPolynomial.C (y i) ∈ pointIdeal y := by
    simp [pointIdeal, RingHom.mem_ker]
  rw [heq] at hm
  have hz : z i - y i = 0 := by
    simpa [pointIdeal, RingHom.mem_ker] using hm
  exact (sub_eq_zero.mp hz).symm
private def step (p : PrimeSpectrum Lower) (t : Lower) (q : PrimeSpectrum Lower) : ℚ := by
  classical
  exact if t ∉ p.asIdeal ∧ q.asIdeal ∈ (cutIdeal p t).minimalPrimes
    then (localColength q (cutIdeal p t)).toNat else 0
theorem step_nonneg (p : PrimeSpectrum Lower) (t : Lower) (q : PrimeSpectrum Lower) :
    0 ≤ step p t q := by
  unfold step
  split <;> positivity
private theorem step_bound (D : PrimeSpectrum Lower → ℚ) (hD : ∀ p, 0 ≤ D p)
    (p : PrimeSpectrum Lower) (t : Lower)
    (hpay : t ∉ p.asIdeal → ∀ qs : Finset (PrimeSpectrum Lower),
      (∀ q ∈ qs, q.asIdeal ∈ (cutIdeal p t).minimalPrimes) →
      (∀ q ∈ qs, localColength q (cutIdeal p t) < ⊤) →
      cutCost D p t qs ≤ D p)
    (qs : Finset (PrimeSpectrum Lower)) :
    ∑ q ∈ qs, step p t q * D q ≤ D p := by
  classical
  by_cases ht : t ∈ p.asIdeal
  · simpa [step, ht] using hD p
  let qs' := qs.filter (fun q => q.asIdeal ∈ (cutIdeal p t).minimalPrimes)
  have hmin : ∀ q ∈ qs', q.asIdeal ∈ (cutIdeal p t).minimalPrimes :=
    fun q hq => (Finset.mem_filter.mp hq).2
  simpa [qs', cutCost, Finset.sum_filter, step, ht, ite_mul] using
    hpay ht qs' hmin (fun q hq => K1_13_7_4.localColength_lt_top (hmin q hq))
theorem step_formula (hassoc : c2)
    {J : Ideal Lower} {t : Lower} {q : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hreg : RegularCut q J t) :
    ((localColength q (J ⊔ Ideal.span {t})).toNat : ℚ) =
      ∑ p ∈ precedingPrimes J q, (localColength p J).toNat * step p t q := by
  classical
  rw [hassoc J t q hq hreg]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  simp [step, cut_of_preceding hq hreg hp]
theorem point_chain_bound (hregular : c1) (hassoc : c2)
    (f g h : Lower) (y : LowerPoint) (q : PrimeSpectrum Lower)
    (hy : q.asIdeal = pointIdeal y) (hq : q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes) :
    ((localColength q (Ideal.span {f, g, h})).toNat : ℚ) ≤
      ∑ r ∈ minPrimes (Ideal.span {f, g}),
        (∑ p ∈ minPrimes (Ideal.span {f}), step zeroPrime f p * step p g r) * step r h q := by
  classical
  obtain ⟨hf, hreg, hregs⟩ := hregular f g h y q hy hq
  have hzero : cutIdeal zeroPrime f = Ideal.span {f} := by simp [cutIdeal, zeroPrime]
  have hf' : f ∉ zeroPrime.asIdeal := by simpa [zeroPrime, Ideal.mem_bot] using hf
  rw [span_triple f g h] at hq ⊢
  rw [step_formula hassoc hq hreg]
  calc
    _ ≤ ∑ r ∈ precedingPrimes (Ideal.span {f, g}) q,
        (∑ p ∈ minPrimes (Ideal.span {f}), step zeroPrime f p * step p g r) * step r h q := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right _ (step_nonneg r h q)
      have hrmin := ((mem_precedingPrimes _ _ _).mp hr).1
      rw [span_pair f g] at hrmin ⊢
      rw [step_formula hassoc hrmin (hregs r hr)]
      have hstart (p : PrimeSpectrum Lower) (hp : p ∈ precedingPrimes (Ideal.span {f}) r) :
          ((localColength p (Ideal.span {f})).toNat : ℚ) = step zeroPrime f p := by
        have hpmin := ((mem_precedingPrimes _ _ _).mp hp).1
        simp [step, hf', hzero, hpmin]
      trans ∑ p ∈ precedingPrimes (Ideal.span {f}) r, step zeroPrime f p * step p g r
      · exact le_of_eq (Finset.sum_congr rfl fun p hp => by rw [hstart p hp])
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (mem_minPrimes _ _).mpr ((mem_precedingPrimes _ _ _).mp hp).1
      · intro p _ _
        exact mul_nonneg (step_nonneg zeroPrime f p) (step_nonneg p g r)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact (mem_minPrimes _ _).mpr ((mem_precedingPrimes _ _ _).mp hr).1
      · intro r _ _
        exact mul_nonneg (Finset.sum_nonneg fun p _ =>
          mul_nonneg (step_nonneg zeroPrime f p) (step_nonneg p g r)) (step_nonneg r h q)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_6.c2 := by
  classical
  intro f g h D hD hpoint hpay points w hmarks
  let ps := minPrimes (Ideal.span {f})
  let rs := minPrimes (Ideal.span {f, g})
  let qs := points.image K1_13_7_4.pointPrime
  have hcard : qs.card = points.card := Finset.card_image_of_injective _ pointPrime_injective
  have hq (q : PrimeSpectrum Lower) (hq : q ∈ qs) :
      (w : ℚ) ≤ ∑ r ∈ rs, (∑ p ∈ ps, step zeroPrime f p * step p g r) * (step r h q * D q) := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨q, hp, hm, hw, hfin⟩ := hmarks y hy
    have heq : q = K1_13_7_4.pointPrime y := PrimeSpectrum.ext_iff.mpr hp
    subst q
    refine le_trans ?_ (le_trans (point_chain_bound h1 h2 f g h y _ hp hm) ?_)
    · exact_mod_cast (by simpa only [ENat.toNat_natCast] using
        ENat.toNat_le_toNat hw hfin.ne : w ≤ (localColength
          (K1_13_7_4.pointPrime y) (Ideal.span {f, g, h})).toNat)
    · exact Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right (step_nonneg r h _) (hpoint y _ hp))
          (Finset.sum_nonneg fun p _ =>
            mul_nonneg (step_nonneg zeroPrime f p) (step_nonneg p g r))
  have budget (p : PrimeSpectrum Lower) (t : Lower)
      (ht : t ∈ ({f, g, h} : Set Lower)) (s : Finset (PrimeSpectrum Lower)) :
      ∑ q ∈ s, step p t q * D q ≤ D p :=
    step_bound D hD p t (hpay t ht p) s
  calc
    (points.card : ℚ) * w = ∑ _ ∈ qs, (w : ℚ) := by simp [hcard]
    _ ≤ ∑ q ∈ qs, ∑ r ∈ rs, (∑ p ∈ ps, step zeroPrime f p * step p g r) *
        (step r h q * D q) := Finset.sum_le_sum hq
    _ = ∑ r ∈ rs, (∑ p ∈ ps, step zeroPrime f p * step p g r) *
        (∑ q ∈ qs, step r h q * D q) := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ rs, (∑ p ∈ ps, step zeroPrime f p * step p g r) * D r := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left (budget r h (by simp) qs)
        (Finset.sum_nonneg fun p _ =>
          mul_nonneg (step_nonneg zeroPrime f p) (step_nonneg p g r))
    _ = ∑ p ∈ ps, step zeroPrime f p * (∑ r ∈ rs, step p g r * D r) := by
      simp_rw [Finset.sum_mul, mul_assoc, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ ps, step zeroPrime f p * D p := by
      exact Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (budget p g (by simp) rs) (step_nonneg zeroPrime f p)
    _ ≤ D zeroPrime := budget zeroPrime f (by simp) ps
end
end K1_13_7_6_2
end
section
set_option autoImplicit false
namespace K1_13_7_6_2_1
noncomputable section
open K1_13_7 MvPolynomial
def coordinate (y : LowerPoint) (i : Fin 3) : Lower := MvPolynomial.X i - C (y i)
private def prefixIdeal (y : LowerPoint) (n : ℕ) : Ideal Lower :=
  Ideal.span (coordinate y '' {i | i.val < n})
private def specialize (y : LowerPoint) (n : ℕ) : Lower →+* Lower :=
  eval₂Hom C (fun i => if i.val < n then C (y i) else MvPolynomial.X i)
theorem ker_specialize (y : LowerPoint) (n : ℕ) :
    RingHom.ker (specialize y n) = prefixIdeal y n := by
  let I := prefixIdeal y n
  have hmk : (Ideal.Quotient.mk I).comp (specialize y n) = Ideal.Quotient.mk I := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [specialize]
    · intro i
      simp only [RingHom.comp_apply, specialize, eval₂Hom_X']
      split_ifs with hi
      · have hm : coordinate y i ∈ I := Ideal.subset_span ⟨i, hi, rfl⟩
        have he := (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr hm
        rw [coordinate, map_sub, sub_eq_zero] at he
        exact he.symm
      · rfl
  apply le_antisymm
  · intro f hf
    apply (Ideal.Quotient.eq_zero_iff_mem (I := I)).mp
    have he := DFunLike.congr_fun hmk f
    change Ideal.Quotient.mk I (specialize y n f) = Ideal.Quotient.mk I f at he
    rw [RingHom.mem_ker.mp hf, map_zero] at he
    exact he.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i.val < n := hi
    simp [RingHom.mem_ker, coordinate, specialize, hi']
private instance prefixIdeal_prime (y : LowerPoint) (n : ℕ) :
    (prefixIdeal y n).IsPrime := by
  rw [← ker_specialize]
  exact RingHom.ker_isPrime _
theorem coordinate_ne_zero (y : LowerPoint) (i : Fin 3) :
    coordinate y i ≠ 0 := by
  intro he
  have he' := congrArg (MvPolynomial.eval (fun _ => y i + 1)) he
  simp [coordinate] at he'
theorem coordinate_notMem (y : LowerPoint) (i : Fin 3) {n : ℕ}
    (hi : n ≤ i.val) : coordinate y i ∉ prefixIdeal y n := by
  rw [← ker_specialize, RingHom.mem_ker]
  simpa [specialize, coordinate, not_lt.mpr hi] using coordinate_ne_zero y i
theorem prefixIdeal_succ (y : LowerPoint) (i : Fin 3) :
    prefixIdeal y (i.val + 1) = Ideal.span {coordinate y i} ⊔ prefixIdeal y i.val := by
  rw [prefixIdeal, prefixIdeal, ← Ideal.span_insert]
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    change j.val < i.val + 1 at hj
    by_cases hji : j = i
    · exact Or.inl (congrArg (coordinate y) hji)
    · have hv : j.val ≠ i.val := fun he => hji (Fin.ext he)
      exact Or.inr ⟨j, (show j.val < i.val by omega), rfl⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨i, Nat.lt_succ_self _, rfl⟩
    · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
theorem prefixIdeal_lt_succ (y : LowerPoint) (i : Fin 3) :
    prefixIdeal y i.val < prefixIdeal y (i.val + 1) := by
  rw [prefixIdeal_succ]
  refine lt_of_le_of_ne le_sup_right ?_
  intro he
  apply coordinate_notMem y i le_rfl
  rw [he]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
theorem prefixIdeal_three (y : LowerPoint) :
    prefixIdeal y 3 = pointIdeal y := by
  have he : specialize y 3 = C.comp (eval y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [specialize]
    · intro i
      simp [specialize]
  rw [← ker_specialize, he, pointIdeal]
  ext p
  simp [RingHom.mem_ker]
theorem point_height_lower (y : LowerPoint) : 3 ≤ (pointIdeal y).height := by
  have h0 := Ideal.height_add_one_le_of_lt_of_isPrime (prefixIdeal_lt_succ y 0)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (prefixIdeal_lt_succ y 1)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (prefixIdeal_lt_succ y 2)
  change (prefixIdeal y 0).height + 1 ≤ (prefixIdeal y 1).height at h0
  change (prefixIdeal y 1).height + 1 ≤ (prefixIdeal y 2).height at h1
  change (prefixIdeal y 2).height + 1 ≤ (prefixIdeal y 3).height at h2
  rw [← prefixIdeal_three]
  calc
    (3 : ℕ∞) = ((0 : ℕ∞) + 1) + 1 + 1 := by norm_num
    _ ≤ (prefixIdeal y 1).height + 1 + 1 :=
      add_le_add (add_le_add ((add_le_add (zero_le : 0 ≤ (prefixIdeal y 0).height) le_rfl).trans h0) le_rfl) le_rfl
    _ ≤ (prefixIdeal y 2).height + 1 := add_le_add h1 le_rfl
    _ ≤ (prefixIdeal y 3).height := h2
theorem localized_prefix (y : LowerPoint) (q : PrimeSpectrum Lower)
    (hy : q.asIdeal = pointIdeal y) (i : Fin 3) :
    let A := Localization.AtPrime q.asIdeal
    let a := algebraMap Lower A
    let I := (prefixIdeal y i.val).map a
    I.IsPrime ∧ a (coordinate y i) ∉ I := by
  dsimp only
  let A := Localization.AtPrime q.asIdeal
  let a := algebraMap Lower A
  let J := prefixIdeal y i.val
  have hle : J ≤ q.asIdeal := by
    rw [hy, ← prefixIdeal_three]
    apply Ideal.span_mono
    rintro _ ⟨j, _, rfl⟩
    exact ⟨j, j.isLt, rfl⟩
  have hd : Disjoint (q.asIdeal.primeCompl : Set Lower) (J : Set Lower) :=
    Set.disjoint_left.mpr (fun _ hx hz => hx (hle hz))
  refine ⟨IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl A J
    (prefixIdeal_prime y i.val) hd, ?_⟩
  have he := IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A
    (prefixIdeal_prime y i.val) hd
  change coordinate y i ∉ (J.map a).under Lower
  rw [he]
  exact coordinate_notMem y i le_rfl
theorem localized_coordinates (y : LowerPoint) (q : PrimeSpectrum Lower)
    (hy : q.asIdeal = pointIdeal y) :
    let A := Localization.AtPrime q.asIdeal
    let a := algebraMap Lower A
    let u := a (coordinate y 0)
    let v := a (coordinate y 1)
    let w := a (coordinate y 2)
    u ≠ 0 ∧ (Ideal.span {u}).IsPrime ∧ v ∉ Ideal.span {u} ∧
      (Ideal.span {u, v}).IsPrime ∧ w ∉ Ideal.span {u, v} := by
  dsimp only
  have h0 : prefixIdeal y 0 = ⊥ := by simp [prefixIdeal]
  have h1 : prefixIdeal y 1 = Ideal.span {coordinate y 0} := by
    have h := prefixIdeal_succ y 0
    change prefixIdeal y 1 = _ ⊔ prefixIdeal y 0 at h
    simpa [h0] using h
  have h2 : prefixIdeal y 2 = Ideal.span {coordinate y 0, coordinate y 1} := by
    have h := prefixIdeal_succ y 1
    change prefixIdeal y 2 = _ ⊔ prefixIdeal y 1 at h
    rw [h, h1, Ideal.span_insert, sup_comm]
  have hp1 := localized_prefix y q hy 1
  have hp2 := localized_prefix y q hy 2
  dsimp only at hp1 hp2
  change ((prefixIdeal y 1).map _).IsPrime ∧ _ ∉ (prefixIdeal y 1).map _ at hp1
  change ((prefixIdeal y 2).map _).IsPrime ∧ _ ∉ (prefixIdeal y 2).map _ at hp2
  rw [h1, Ideal.map_span, Set.image_singleton] at hp1
  rw [h2, Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at hp2
  refine ⟨?_, hp1.1, hp1.2, hp2.1, hp2.2⟩
  simpa only [map_zero] using (IsLocalization.injective (Localization.AtPrime q.asIdeal)
    q.asIdeal.primeCompl_le_nonZeroDivisors).ne (coordinate_ne_zero y 0)
end
end K1_13_7_6_2_1
end
section
set_option autoImplicit false
namespace K1_13_7_6_2_2
noncomputable section
open K1_13_7 K1_13_7_6 K1_13_7_6_2
open scoped Classical
theorem cut_minimal {J : Ideal Lower} {t : Lower} {q p : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hJp : J ≤ p.asIdeal) (hpq : p.asIdeal ≤ q.asIdeal) :
    q.asIdeal ∈ (cutIdeal p t).minimalPrimes := by
  have htq : Ideal.span {t} ≤ q.asIdeal := le_sup_right.trans hq.le
  refine ⟨⟨q.isPrime, sup_le hpq htq⟩, ?_⟩
  intro s hs hsq
  exact hq.2 ⟨hs.1, sup_le (hJp.trans (le_sup_left.trans hs.2))
    (le_sup_right.trans hs.2)⟩ hsq
theorem eq_of_prime_between {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P I Q : Ideal R} {t : R} (hP : P.IsPrime) (hI : I.IsPrime)
    (hQ : Q ∈ (P ⊔ Ideal.span {t}).minimalPrimes) (hPI : P ≤ I) (hIQ : I ≤ Q)
    (hne : I ≠ Q) : I = P := by
  let f : R →+* R ⧸ P := Ideal.Quotient.mk P
  have := hQ.isPrime
  have hPQ := hPI.trans hIQ
  have hh : (Q.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have : (Q.map f).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have hi : (I.map f).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPI
  have hlt : I.map f < Q.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hIQ) fun he => hne ?_
    calc
      I = (I.map f).comap f := (Ideal.comap_map_mk hPI).symm
      _ = (Q.map f).comap f := congrArg (Ideal.comap f) he
      _ = Q := Ideal.comap_map_mk hPQ
  have hz := (Ideal.height_le_iff (n := 1)).mp hh (I.map f) hi hlt
  have hbot := Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp hz)
  calc
    I = (I.map f).comap f := (Ideal.comap_map_mk hPI).symm
    _ = RingHom.ker f := by rw [hbot, RingHom.ker_eq_comap_bot]
    _ = P := Ideal.mk_ker
theorem prime_below_cut {J : Ideal Lower} {t : Lower} {q r : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hJr : J ≤ r.asIdeal) (hrq : r.asIdeal ≤ q.asIdeal) :
    r = q ∨ r ∈ precedingPrimes J q := by
  by_cases h : r = q
  · exact Or.inl h
  right
  obtain ⟨P, hP, hPr⟩ := Ideal.exists_minimalPrimes_le hJr
  let p : PrimeSpectrum Lower := ⟨P, hP.isPrime⟩
  have hpq : q.asIdeal ∈ (P ⊔ Ideal.span {t}).minimalPrimes :=
    cut_minimal (p := p) hq hP.le (hPr.trans hrq)
  have he : r.asIdeal = P := eq_of_prime_between hP.isPrime r.isPrime hpq hPr hrq
    (fun he => h (PrimeSpectrum.ext_iff.mpr he))
  exact (mem_precedingPrimes J q r).mpr ⟨he.symm ▸ hP, hrq⟩
theorem cut_regular_on_prime {J : Ideal Lower} {t : Lower}
    {q p : PrimeSpectrum Lower} (hreg : RegularCut q J t)
    (hp : p ∈ precedingPrimes J q) :
    IsSMulRegular (At q ⧸ p.asIdeal.map (algebraMap Lower (At q))) (algebraMap Lower (At q) t) := by
  obtain ⟨hpJ, hpq⟩ := (mem_precedingPrimes J q p).mp hp
  let A := At q
  let a := algebraMap Lower A
  let Q := p.asIdeal.map a
  have hdisj : Disjoint (q.asIdeal.primeCompl : Set Lower) (p.asIdeal : Set Lower) :=
    Set.disjoint_left.mpr (fun _ hx hxp => hx (hpq hxp))
  let : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl A p.asIdeal p.isPrime hdisj
  have hcomap : Q.under Lower = p.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl A p.isPrime hdisj
  have hmin : Q ∈ (J.map a).minimalPrimes := by
    change Q ∈ (J.map (algebraMap Lower A)).minimalPrimes
    rw [IsLocalization.minimalPrimes_map q.asIdeal.primeCompl A, Set.mem_preimage, hcomap]
    exact hpJ
  change IsSMulRegular (A ⧸ J.map a) (a t) at hreg
  have hmin' : Q ∈ (Module.annihilator A (A ⧸ J.map a)).minimalPrimes := by
    rwa [Ideal.annihilator_quotient]
  have ha : Ideal.Quotient.mk Q (a t) ≠ 0 :=
    fun he => (hreg.notMem_of_mem_minimalPrimes hmin') (Ideal.Quotient.eq_zero_iff_mem.mp he)
  change IsSMulRegular (A ⧸ Q) (a t)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  exact (mul_eq_zero.mp (show Ideal.Quotient.mk Q (a t) * x = 0 from hx)).resolve_left ha
theorem locLength_at_preceding {J : Ideal Lower} {q p r : PrimeSpectrum Lower}
    (hp : p ∈ precedingPrimes J q) (hr : J ≤ r.asIdeal) :
    locLength p (Lower ⧸ r.asIdeal) = if r = p then 1 else 0 := by
  classical
  by_cases he : r = p
  · subst r
    simpa using locLength_prime_self p
  rw [ite_eq_right he]
  apply locLength_prime_away
  intro hrp
  have hm := ((mem_precedingPrimes J q p).mp hp).1
  have hle : p.asIdeal ≤ r.asIdeal := hm.2 ⟨r.isPrime, hr⟩ hrp
  exact he (PrimeSpectrum.ext_iff.mpr (hrp.antisymm hle))
theorem cut_prime_factor {J : Ideal Lower} {t : Lower} {q r : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hreg : RegularCut q J t) (hr : J ≤ r.asIdeal) :
    CutFinite (algebraMap Lower (At q) t) (Loc q (Lower ⧸ r.asIdeal)) ∧
      cutEuler (algebraMap Lower (At q) t) (Loc q (Lower ⧸ r.asIdeal)) =
        if r ∈ precedingPrimes J q then ((localColength q (cutIdeal r t)).toNat : ℤ) else 0 := by
  classical
  by_cases hp : r ∈ precedingPrimes J q
  · rw [ite_eq_left hp]
    exact cut_regular q r.asIdeal t (cut_regular_on_prime hreg hp)
      (K1_13_7_4.localColength_lt_top (cut_minimal (p := r) hq hr ((mem_precedingPrimes J q r).mp hp).2))
  rw [ite_eq_right hp]
  apply cut_of_finite_length
  change locLength q (Lower ⧸ r.asIdeal) < ⊤
  by_cases hrq : r.asIdeal ≤ q.asIdeal
  · rcases prime_below_cut hq hr hrq with h | h
    · subst r
      simp [locLength_prime_self]
    · exact (hp h).elim
  · simp [locLength_prime_away hrq]
end
end K1_13_7_6_2_2
end
section
set_option autoImplicit false
namespace K1_13_7_6_2_1
noncomputable section
open K1_13_7 K1_13_7_6_2
local instance : GCDMonoid Lower := UniqueFactorizationMonoid.toGCDMonoid Lower
theorem not_minimal_pair {q : Ideal Lower} (hq : 3 ≤ q.height) (a b : Lower) :
    q ∉ (Ideal.span {a, b}).minimalPrimes := by
  intro hp
  have hn : ({a, b} : Set Lower).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  have hle : q.height ≤ 2 :=
    (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hp).trans (by exact_mod_cast hn)
  exact (by norm_num : ¬ (3 : ℕ∞) ≤ 2) (hq.trans hle)
theorem gcd_avoids {f g h : Lower} {q : PrimeSpectrum Lower}
    (hh : 3 ≤ q.asIdeal.height) (hq : q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes) :
    gcd f g ∉ q.asIdeal := by
  intro hd
  apply not_minimal_pair hh (gcd f g) h
  have ht : h ∈ q.asIdeal := hq.le (Ideal.subset_span (by simp))
  refine ⟨⟨q.isPrime, Ideal.span_le.mpr ?_⟩, ?_⟩
  · simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hd, ht⟩
  intro p hp hpq
  have hdp : gcd f g ∈ p := hp.2 (Ideal.subset_span (by simp))
  have hhp : h ∈ p := hp.2 (Ideal.subset_span (by simp))
  have hfp : f ∈ p := by
    obtain ⟨k, hk⟩ := gcd_dvd_left f g
    rw [hk]
    exact p.mul_mem_right _ hdp
  have hgp : g ∈ p := by
    obtain ⟨k, hk⟩ := gcd_dvd_right f g
    rw [hk]
    exact p.mul_mem_right _ hdp
  apply hq.2 ⟨hp.1, Ideal.span_le.mpr ?_⟩ hpq
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hfp, hgp, hhp⟩
theorem regular_pair (p : PrimeSpectrum Lower) {f g : Lower}
    (hd : gcd f g ∉ p.asIdeal) : RegularCut p (Ideal.span {f}) g := by
  let A := Localization.AtPrime p.asIdeal
  let a := algebraMap Lower A
  let J : Ideal Lower := Ideal.span {f}
  change IsSMulRegular (A ⧸ J.map a) (a g)
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (J.map a) (a g)).mpr
  intro z hz
  change a g * z ∈ J.map a at hz
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl z
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff] at hz
  obtain ⟨t, ht, htx⟩ := hz
  rw [← mul_left_comm g t x, Ideal.mem_span_singleton] at htx
  have hdx : t * (gcd f g * x) ∈ J := by
    change t * (gcd f g * x) ∈ Ideal.span {f}
    rw [mul_left_comm t, Ideal.mem_span_singleton]
    exact dvd_gcd_mul_of_dvd_mul htx
  have hmem : a (gcd f g) * IsLocalization.mk' A x s ∈ J.map a := by
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨t, ht, hdx⟩
  exact ((J.map a).unit_mul_mem_iff_mem
    (IsLocalization.map_units A (⟨gcd f g, hd⟩ : p.asIdeal.primeCompl))).mp hmem
theorem pair_syzygy {A : Type*} [CommRing A] [IsDomain A]
    {f g : A} (hf : f ≠ 0) (hg : IsSMulRegular (A ⧸ Ideal.span {f}) g)
    {a b : A} (hab : f * a + g * b = 0) :
    ∃ c : A, a = g * c ∧ b = -(f * c) := by
  have hm : g * b ∈ Ideal.span {f} := by
    have he : g * b = f * (-a) := by linear_combination hab
    rw [he]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right f (-a))
  have hb : f ∣ b := Ideal.mem_span_singleton.mp
    (mem_of_isSMulRegular_quotient_of_smul_mem hg hm)
  obtain ⟨k, hk⟩ := hb
  refine ⟨-k, mul_left_cancel₀ hf ?_, by rw [hk]; ring⟩
  linear_combination hab - g * hk
theorem no_coordinate_socle {A : Type*} [CommRing A] [IsDomain A]
    {u v w f g z : A} (hu : u ≠ 0)
    (hU : (Ideal.span ({u} : Set A)).IsPrime) (hv : v ∉ Ideal.span {u})
    (hUV : (Ideal.span ({u, v} : Set A)).IsPrime) (hw : w ∉ Ideal.span {u, v})
    (hf : f ≠ 0) (hg : IsSMulRegular (A ⧸ Ideal.span {f}) g)
    (hz0 : u * z ∈ Ideal.span {f, g}) (hz1 : v * z ∈ Ideal.span {f, g})
    (hz2 : w * z ∈ Ideal.span {f, g}) :
    z ∈ Ideal.span {f, g} := by
  obtain ⟨a0, b0, h0⟩ := Ideal.mem_span_pair.mp hz0
  obtain ⟨a1, b1, h1⟩ := Ideal.mem_span_pair.mp hz1
  obtain ⟨a2, b2, h2⟩ := Ideal.mem_span_pair.mp hz2
  obtain ⟨c01, ha01, hb01⟩ := pair_syzygy hf hg
    (a := u * a1 - v * a0) (b := u * b1 - v * b0) (by
      linear_combination u * h1 - v * h0)
  obtain ⟨c02, _, hb02⟩ := pair_syzygy hf hg
    (a := u * a2 - w * a0) (b := u * b2 - w * b0) (by
      linear_combination u * h2 - w * h0)
  obtain ⟨c12, _, hb12⟩ := pair_syzygy hf hg
    (a := v * a2 - w * a1) (b := v * b2 - w * b1) (by
      linear_combination v * h2 - w * h1)
  have hc : u * c12 - v * c02 + w * c01 = 0 := by
    apply mul_left_cancel₀ hf
    linear_combination u * hb12 - v * hb02 + w * hb01
  have hwc : w * c01 ∈ Ideal.span {u, v} :=
    Ideal.mem_span_pair.mpr ⟨-c12, c02, by linear_combination -hc⟩
  have hc' := (hUV.mem_or_mem hwc).resolve_left hw
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hc'
  have div_first {x y : A} (he : u * y = v * x) : u ∣ x := by
    have hm : v * x ∈ Ideal.span {u} := he ▸
      Ideal.mem_span_singleton.mpr (dvd_mul_right u y)
    exact Ideal.mem_span_singleton.mp ((hU.mem_or_mem hm).resolve_left hv)
  obtain ⟨a, ha⟩ := div_first (x := a0 + g * d) (y := a1 - g * c)
    (by linear_combination ha01 - g * hcd)
  obtain ⟨b, hb⟩ := div_first (x := b0 - f * d) (y := b1 + f * c)
    (by linear_combination hb01 + f * hcd)
  refine Ideal.mem_span_pair.mpr ⟨a, b, mul_left_cancel₀ hu ?_⟩
  linear_combination h0 - f * ha - g * hb
theorem regular_third {f g h : Lower} {y : LowerPoint} {q : PrimeSpectrum Lower}
    (hy : q.asIdeal = pointIdeal y) (hf : f ≠ 0)
    (hg : RegularCut q (Ideal.span {f}) g)
    (hq : q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes) :
    RegularCut q (Ideal.span {f, g}) h := by
  let A := Localization.AtPrime q.asIdeal
  let a := algebraMap Lower A
  let F := a f
  let G := a g
  let H := a h
  let J : Ideal A := Ideal.span {F, G}
  have hMapPair : (Ideal.span ({f, g} : Set Lower)).map a = J := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change IsSMulRegular (A ⧸ (Ideal.span {f, g}).map a) H
  rw [hMapPair]
  change IsSMulRegular (A ⧸ (Ideal.span {f}).map a) G at hg
  rw [Ideal.map_span, Set.image_singleton] at hg
  have hF : F ≠ 0 := by
    simpa only [map_zero] using
      (IsLocalization.injective A q.asIdeal.primeCompl_le_nonZeroDivisors).ne hf
  have hrad : (Ideal.span ({F, G, H} : Set A)).radical = IsLocalRing.maximalIdeal A := by
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal A] using
      (IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := A) q.asIdeal
        (Ideal.span {f, g, h}) hq)
  by_contra hn
  have hmem : H ∈ ⋃ p ∈ associatedPrimes A (A ⧸ J), (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hn
  obtain ⟨p, hp, hH⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨hpPrime, x, hx⟩ := isAssociatedPrime_iff.mp hp
  have hJ : J ≤ p := by
    rw [← Ideal.annihilator_quotient (I := J)]
    intro t ht
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact Module.mem_annihilator.mp ht x
  have hmp : IsLocalRing.maximalIdeal A ≤ p := by
    rw [← hrad, ← hpPrime.radical]
    apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hJ (Ideal.subset_span (by simp)), hJ (Ideal.subset_span (by simp)), hH⟩
  have hxne : x ≠ 0 := by
    intro he
    exact hpPrime.ne_top' (by simp [hx, he, Submodule.colon_singleton_zero])
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hz (i : Fin 3) : a (coordinate y i) * z ∈ J := by
    have hm : a (coordinate y i) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal A]
      apply Ideal.mem_map_of_mem
      rw [hy]
      simp [coordinate, pointIdeal, RingHom.mem_ker]
    have hp' := hmp hm
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot] at hp'
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    exact hp'
  obtain ⟨hu, hU, hv, hUV, hw⟩ := localized_coordinates y q hy
  exact hxne (Ideal.Quotient.eq_zero_iff_mem.mpr
    (no_coordinate_socle hu hU hv hUV hw hF hg (hz 0) (hz 1) (hz 2)))
theorem proof : K1_13_7_6_2.c1 := by
  intro f g h y q hy hq
  have hh : 3 ≤ q.asIdeal.height := hy.symm ▸ point_height_lower y
  have hf : f ≠ 0 := by
    intro he
    subst f
    exact not_minimal_pair hh g h (by simpa only [Ideal.span_insert_zero] using hq)
  have hd := gcd_avoids hh hq
  refine ⟨hf, regular_third hy hf (regular_pair q hd) hq, ?_⟩
  intro r hr
  have hrq := ((mem_precedingPrimes _ _ _).mp hr).2
  exact regular_pair r (fun hm => hd (hrq hm))
end
end K1_13_7_6_2_1
end
section
set_option autoImplicit false
namespace K1_13_7_6_2_2
noncomputable section
open K1_13_7 K1_13_7_6 K1_13_7_6_2
open scoped BigOperators
private def cutWeight (q : PrimeSpectrum Lower) (t : Lower) (p : PrimeSpectrum Lower) : ℤ :=
  (localColength q (cutIdeal p t)).toNat
theorem module_formula {J : Ideal Lower} {t : Lower} {q : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (J ⊔ Ideal.span {t}).minimalPrimes)
    (hreg : RegularCut q J t)
    (M : Type) [AddCommGroup M] [Module Lower M] [Module.Finite Lower M]
    (hJ : J ≤ Module.annihilator Lower M) :
    CutFinite (algebraMap Lower (At q) t) (Loc q M) ∧
      (∀ p ∈ precedingPrimes J q, locLength p M < ⊤) ∧
      cutEuler (algebraMap Lower (At q) t) (Loc q M) =
        ∑ p ∈ precedingPrimes J q, (locLength p M).toNat * cutWeight q t p := by
  classical
  let u := algebraMap Lower (At q) t
  revert hJ
  induction (inferInstance : Module.Finite Lower M) using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime Lower with
  | subsingleton N =>
    intro _
    have h (p : PrimeSpectrum Lower) : locLength p N = 0 := Module.length_eq_zero
    have hz := cut_of_finite_length u (show locLength q N < ⊤ by simp [h])
    refine ⟨hz.1, fun p _ => by simp [h], ?_⟩
    simpa [h] using hz.2
  | quotient N r e =>
    intro hJ
    rw [e.annihilator_eq, Ideal.annihilator_quotient] at hJ
    let E (p : PrimeSpectrum Lower) : Loc p N ≃ₗ[At p] Loc p (Lower ⧸ r.asIdeal) :=
      IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (Lower ⧸ r.asIdeal)) (At p) e
    have hw (p : PrimeSpectrum Lower) (hp : p ∈ precedingPrimes J q) :
        locLength p N = if r = p then 1 else 0 :=
      (E p).length_eq.trans (locLength_at_preceding hp hJ)
    have hc := cut_prime_factor hq hreg hJ
    have he := cut_congr u (E q)
    refine ⟨he.1.mpr hc.1, fun p hp => by rw [hw p hp]; split <;> simp, ?_⟩
    rw [he.2, hc.2]
    by_cases hr : r ∈ precedingPrimes J q
    · rw [ite_eq_left hr, Finset.sum_eq_single r]
      · simp [hw r hr, cutWeight]
      · intro p hp hpr
        simp [hw p hp, Ne.symm hpr]
      · exact fun h => (h hr).elim
    · rw [ite_eq_right hr, Finset.sum_eq_zero]
      intro p hp
      have hne : r ≠ p := fun h => hr (h ▸ hp)
      simp [hw p hp, hne]
  | exact N₁ N₂ N₃ f g hf hg hfg ih₁ ih₃ =>
    intro hJ
    have h₁ := ih₁ (hJ.trans (f.annihilator_le_of_injective hf))
    have h₃ := ih₃ (hJ.trans (g.annihilator_le_of_surjective hg))
    have hex (p : PrimeSpectrum Lower) :
        Function.Exact (LocalizedModule.map p.asIdeal.primeCompl f)
          (LocalizedModule.map p.asIdeal.primeCompl g) :=
      LocalizedModule.map_exact p.asIdeal.primeCompl f g hfg
    have hl (p : PrimeSpectrum Lower) : locLength p N₂ = locLength p N₁ + locLength p N₃ :=
      Module.length_eq_add_of_exact _ _
        (LocalizedModule.map_injective p.asIdeal.primeCompl f hf)
        (LocalizedModule.map_surjective p.asIdeal.primeCompl g hg) (hex p)
    have hc := cut_add u _ _ (LocalizedModule.map_injective q.asIdeal.primeCompl f hf)
      (LocalizedModule.map_surjective q.asIdeal.primeCompl g hg) (hex q) h₁.1 h₃.1
    refine ⟨hc.1, fun p hp => (hl p).symm ▸ ENat.add_lt_top.mpr ⟨h₁.2.1 p hp, h₃.2.1 p hp⟩, ?_⟩
    rw [hc.2, h₁.2.2, h₃.2.2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hl p, ENat.toNat_add (h₁.2.1 p hp).ne (h₃.2.1 p hp).ne, Nat.cast_add, add_mul]
theorem proof : K1_13_7_6_2.c2 := by
  intro J t q hq hreg
  have hm := module_formula hq hreg (Lower ⧸ J)
    (show J ≤ Module.annihilator Lower (Lower ⧸ J) by rw [Ideal.annihilator_quotient])
  have hc := cut_regular q J t hreg (K1_13_7_4.localColength_lt_top hq)
  have h := hm.2.2
  rw [hc.2] at h
  simp only [locLength_quotient, cutWeight] at h
  exact_mod_cast h
end
end K1_13_7_6_2_2
end
section
set_option autoImplicit false
namespace K1_14_2_3_2
open K1_14_2 K1_14_2_3
def c1 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime → Nontrivial (JetSeedSection I) →
    IsDomain (JetSeedSection I) ∧
      ∃ (f : PlaneSeedSection (seedImage I) →ₐ[SeedField] RootSeedSection (rootImage I))
        (j : RootSeedSection (rootImage I) →ₐ[SeedField] JetSeedSection I),
        Function.Injective f ∧ Function.Injective j
def c2 : Prop :=
  ∀ I : Ideal Ambient,
    ∃ j : RootYSection (rootImage I) →ₐ[SeedField] JetYSection I, Function.Injective j
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_3.c2 :=
  assemble h1 plane_degree h2
end K1_14_2_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_3_2_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_3 K1_14_2_3_1
open scoped Polynomial
local instance (n : ℕ) (I : Ideal (Raw n)) : CommRing (CoordinateRing I)[X] :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)
private theorem clear_denominator {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    (x : Slice I i j) :
    ∃ (q : (CoordinateRing I)[X]) (d : SeedField), d ≠ 0 ∧
      x * algebraMap SeedField (Slice I i j) d = slopeToSlice I i j q := by
  let : Algebra (MvPolynomial (Fin n) Seeds) (Over n) := MvPolynomial.algebraMvPolynomial
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨g, m⟩, hgm⟩ := IsLocalization.surj
    (M := (nonZeroDivisors Seeds).map (MvPolynomial.C (σ := Fin n))) f
  obtain ⟨d, hd, hdm⟩ := m.property
  let lift : MvPolynomial (Fin n) Seeds →+* (CoordinateRing I)[X] :=
    MvPolynomial.eval₂Hom (parameterMap I i j) (fun k => Polynomial.C (coord I k))
  have hcomp : (slopeToSlice I i j).comp lift =
      (Ideal.Quotient.mk (sectionIdeal I i j)).comp
        (MvPolynomial.map (algebraMap Seeds SeedField)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, lift, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact RingHom.congr_fun (parameter_commutes I i j) a
    · intro k
      simp [lift, slopeToSlice, toSlice, RingHom.comp_apply]
  refine ⟨lift g, algebraMap Seeds SeedField d, ?_, ?_⟩
  · exact fun h => mem_nonZeroDivisors_iff_ne_zero.mp hd
      (IsFractionRing.injective Seeds SeedField (h.trans (map_zero _).symm))
  · have hgm' : f * MvPolynomial.C (algebraMap Seeds SeedField d) =
        MvPolynomial.map (algebraMap Seeds SeedField) g := by
      simpa only [MvPolynomial.algebraMap_def, ← hdm, MvPolynomial.map_C] using hgm
    calc
      _ = Ideal.Quotient.mk (sectionIdeal I i j)
          (f * MvPolynomial.C (algebraMap Seeds SeedField d)) := (map_mul _ _ _).symm
      _ = _ := (congrArg (Ideal.Quotient.mk (sectionIdeal I i j)) hgm').trans
        (RingHom.congr_fun hcomp g).symm
theorem cancel_denominator {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    {x : Slice I i j} {d : SeedField} (hd : d ≠ 0)
    (h : x * algebraMap SeedField (Slice I i j) d = 0) : x = 0 :=
  ((isUnit_iff_ne_zero.mpr hd).map (algebraMap SeedField (Slice I i j))).mul_right_cancel
    (h.trans (zero_mul _).symm)
theorem slice_isDomain {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] : IsDomain (Slice I i j) := by
  let : NoZeroDivisors (Slice I i j) := by
    constructor
    intro x y hxy
    obtain ⟨q, d, hd, hq⟩ := clear_denominator I i j x
    obtain ⟨r, e, he, hr⟩ := clear_denominator I i j y
    let d' : Slice I i j := algebraMap SeedField (Slice I i j) d
    let e' : Slice I i j := algebraMap SeedField (Slice I i j) e
    have hqr : slopeToSlice I i j (q * r) = 0 := calc
      _ = slopeToSlice I i j q * slopeToSlice I i j r := map_mul _ q r
      _ = (x * d') * (y * e') := congrArg₂ (· * ·) hq.symm hr.symm
      _ = (x * y) * (d' * e') := mul_mul_mul_comm x d' y e'
      _ = 0 := by rw [hxy, zero_mul]
    have hz : q * r = 0 := slope_injective I i j (hqr.trans (map_zero _).symm)
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (cancel_denominator I i j hd (by simpa only [h, map_zero] using hq))
    · exact Or.inr (cancel_denominator I i j he (by simpa only [h, map_zero] using hr))
  exact NoZeroDivisors.to_isDomain _
private abbrev extendCoeffs (n : ℕ) : Raw n →+* Over n :=
  MvPolynomial.map (algebraMap FX SeedField)
private abbrev contraction {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m)) :
    Ideal (Raw n) :=
  I.comap (MvPolynomial.rename e).toRingHom
theorem rename_coeffs {n m : ℕ} (e : Fin n → Fin m) :
    ((MvPolynomial.rename e : Over n →ₐ[SeedField] Over m).toRingHom).comp
        (extendCoeffs n) =
      (extendCoeffs m).comp (MvPolynomial.rename e : Raw n →ₐ[FX] Raw m).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply]
  · intro k
    simp [RingHom.comp_apply]
theorem sectionIdeal_le {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m))
    (i j : Fin n) :
    sectionIdeal (contraction e I) i j ≤
      (sectionIdeal I (e i) (e j)).comap (MvPolynomial.rename e : Over n →ₐ[SeedField] Over m) := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
  · intro p hp
    change (((MvPolynomial.rename e : Over n →ₐ[SeedField] Over m).toRingHom).comp
      (extendCoeffs n)) p ∈ sectionIdeal I (e i) (e j)
    rw [rename_coeffs]
    exact (show I.map (extendCoeffs m) ≤ sectionIdeal I (e i) (e j) from le_sup_left)
      (Ideal.mem_map_of_mem (extendCoeffs m) hp)
  · intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change MvPolynomial.rename e (seedLine i j) ∈ sectionIdeal I (e i) (e j)
    have h : MvPolynomial.rename e (seedLine i j) = seedLine (e i) (e j) := by
      simp [seedLine]
    rw [h]
    exact (show Ideal.span {seedLine (e i) (e j)} ≤ sectionIdeal I (e i) (e j) from le_sup_right)
      (Ideal.mem_span_singleton_self _)
def sliceRename {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m))
    (i j : Fin n) : Slice (contraction e I) i j →ₐ[SeedField] Slice I (e i) (e j) :=
  Ideal.quotientMapₐ (sectionIdeal I (e i) (e j)) (MvPolynomial.rename e) (sectionIdeal_le e I i j)
def quotientRename {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m)) :
    CoordinateRing (contraction e I) →+* CoordinateRing I :=
  Ideal.quotientMap I (MvPolynomial.rename e).toRingHom le_rfl
theorem slice_slope_commutes {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m))
    (i j : Fin n) :
    (sliceRename e I i j).toRingHom.comp (slopeToSlice (contraction e I) i j) =
      (slopeToSlice I (e i) (e j)).comp (Polynomial.mapRingHom (quotientRename e I)) := by
  apply Polynomial.ringHom_ext
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, slopeToSlice,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C,
      toSlice, quotientRename, Ideal.quotientMap_mk, sliceRename, Ideal.quotient_map_mkₐ,
      Ideal.Quotient.mkₐ_eq_mk]
    exact congrArg (Ideal.Quotient.mk (sectionIdeal I (e i) (e j)))
      (RingHom.congr_fun (rename_coeffs e) a)
  · simp [slopeToSlice, RingHom.comp_apply]
theorem sliceRename_injective {n m : ℕ} (e : Fin n → Fin m) (I : Ideal (Raw m))
    (i j : Fin n) [I.IsPrime] [Nontrivial (Slice I (e i) (e j))] :
    Function.Injective (sliceRename e I i j) := by
  apply (injective_iff_map_eq_zero (sliceRename e I i j)).mpr
  intro x hx
  obtain ⟨q, d, hd, hq⟩ := clear_denominator (contraction e I) i j x
  have hq' : sliceRename e I i j (slopeToSlice (contraction e I) i j q) = 0 := by
    rw [← hq, map_mul, hx, zero_mul]
  have hs : slopeToSlice I (e i) (e j) (Polynomial.map (quotientRename e I) q) = 0 :=
    (RingHom.congr_fun (slice_slope_commutes e I i j) q).symm.trans hq'
  have hq0 : q = 0 := (Polynomial.map_eq_zero_iff
      (show Function.Injective (quotientRename e I) from Ideal.quotientMap_injective)).mp
    ((injective_iff_map_eq_zero _).mp (slope_injective I (e i) (e j)) _ hs)
  exact cancel_denominator (contraction e I) i j hd (by simpa only [hq0, map_zero] using hq)
theorem proof : K1_14_2_3_2.c1 := by
  intro I hI hJet
  let e : Fin 2 → Fin 3 := Fin.castLE (by decide)
  let t : Fin 3 → Fin 4 := Fin.castLE (by decide)
  let j : K1_14_2.RootSeedSection (rootImage I) →ₐ[SeedField] JetSeedSection I :=
    sliceRename t I 0 1
  have hj : Function.Injective j := @sliceRename_injective 3 4 t I 0 1 hI hJet
  have hRootPrime : (rootImage I).IsPrime := hI.comap rootIncl
  have hRoot : Nontrivial (RootSeedSection (rootImage I)) := by
    let : Nontrivial (JetSeedSection I) := hJet
    exact j.toRingHom.domain_nontrivial
  let f : K1_14_2_3_2.PlaneSeedSection (seedImage I) →ₐ[SeedField] RootSeedSection (rootImage I) :=
    sliceRename e (rootImage I) 0 1
  exact ⟨@slice_isDomain 4 I 0 1 hI hJet, f, j,
    @sliceRename_injective 2 3 e (rootImage I) 0 1 hRootPrime hRoot, hj⟩
end
end K1_14_2_3_2_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000
namespace K1_14_2_3_2_2
noncomputable section
open K1_14 K1_14_2
abbrev Raw (n : ℕ) := MvPolynomial (Fin n) FX
abbrev Integral (n : ℕ) := MvPolynomial (Fin n) Seeds
abbrev Over (n : ℕ) := MvPolynomial (Fin n) SeedField
local instance (n : ℕ) (I : Ideal (Raw n)) : CommRing (Polynomial (CoordinateRing I)) :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)
abbrev rawToIntegral (n : ℕ) : Raw n →+* Integral n :=
  MvPolynomial.map MvPolynomial.C
abbrev relation {n : ℕ} (i : Fin n) : Integral n :=
  MvPolynomial.X i - MvPolynomial.C (MvPolynomial.X (1 : Fin 2))
abbrev integralIdeal {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) : Ideal (Integral n) :=
  I.map (rawToIntegral n) ⊔ Ideal.span {relation i}
abbrev integralQuot {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :=
  Integral n ⧸ integralIdeal I i
abbrev coord {n : ℕ} (I : Ideal (Raw n)) (k : Fin n) : CoordinateRing I :=
  Ideal.Quotient.mk I (MvPolynomial.X k)
def parameter {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    Seeds →+* Polynomial (CoordinateRing I) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap FX (CoordinateRing I)))
    ![Polynomial.X, Polynomial.C (coord I i)]
def eliminate {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    Integral n →+* Polynomial (CoordinateRing I) :=
  MvPolynomial.eval₂Hom (parameter I i) (fun k => Polynomial.C (coord I k))
theorem eliminate_raw {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    (eliminate I i).comp (rawToIntegral n) = Polynomial.C.comp (Ideal.Quotient.mk I) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [eliminate, parameter]
    rfl
  · intro k
    simp [eliminate]
def rawQuotToIntegralQuot {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    CoordinateRing I →+* integralQuot I i :=
  Ideal.quotientMap (integralIdeal I i) (rawToIntegral n)
    (Ideal.map_le_iff_le_comap.mp le_sup_left)
private def restore {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    Polynomial (CoordinateRing I) →+* integralQuot I i :=
  Polynomial.eval₂RingHom (rawQuotToIntegralQuot I i)
    (Ideal.Quotient.mk (integralIdeal I i) (MvPolynomial.C (MvPolynomial.X (0 : Fin 2))))
theorem integral_relation_eq {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    Ideal.Quotient.mk (integralIdeal I i) (MvPolynomial.X i) =
      Ideal.Quotient.mk (integralIdeal I i) (MvPolynomial.C (MvPolynomial.X (1 : Fin 2))) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (show Ideal.span {relation i} ≤ integralIdeal I i from le_sup_right)
    (Ideal.mem_span_singleton_self _)
theorem restore_eliminate {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    (restore I i).comp (eliminate I i) = Ideal.Quotient.mk (integralIdeal I i) := by
  apply MvPolynomial.ringHom_ext
  · intro s
    have h : (restore I i).comp (parameter I i) =
        (Ideal.Quotient.mk (integralIdeal I i)).comp MvPolynomial.C := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [parameter, restore, rawQuotToIntegralQuot, MvPolynomial.algebraMap_eq]
      · intro k
        fin_cases k
        · simp [parameter, restore]
        · simpa [parameter, restore, rawQuotToIntegralQuot] using integral_relation_eq I i
    simpa [eliminate] using RingHom.congr_fun h s
  · intro k
    simp [eliminate, restore, rawQuotToIntegralQuot]
theorem mem_integralIdeal_iff {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) (f : Integral n) :
    f ∈ integralIdeal I i ↔ eliminate I i f = 0 := by
  constructor
  · change f ∈ integralIdeal I i → f ∈ RingHom.ker (eliminate I i)
    apply (show integralIdeal I i ≤ RingHom.ker (eliminate I i) from ?_)
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      change ((eliminate I i).comp (rawToIntegral n)) p = 0
      rw [eliminate_raw]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    · rintro p (rfl : p = relation i)
      simp [eliminate, parameter, RingHom.mem_ker]
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← restore_eliminate I i]
    simp [h]
end
end K1_14_2_3_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000
namespace K1_14_2_3_2_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_3
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance (n : ℕ) (I : Ideal (Raw n)) : CommRing (Polynomial (CoordinateRing I)) :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)
private abbrev keep : Fin 3 → Fin 4 := Fin.castLE (by decide : 3 ≤ 4)
private abbrev incl (R : Type) [CommRing R] :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 4) R :=
  MvPolynomial.rename keep
private abbrev extendCoeffs (n : ℕ) : Raw n →+* Over n :=
  MvPolynomial.map (algebraMap FX SeedField)
private abbrev localize (n : ℕ) : Integral n →+* Over n :=
  algebraMap (Integral n) (Over n)
private abbrev denominators (n : ℕ) : Submonoid (Integral n) :=
  (nonZeroDivisors Seeds).map MvPolynomial.C
private abbrev sectionIdeal {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) : Ideal (Over n) :=
  I.map (extendCoeffs n) ⊔ Ideal.span {ySection i}
theorem map_integralIdeal {n : ℕ} (I : Ideal (Raw n)) (i : Fin n) :
    (integralIdeal I i).map (localize n) = sectionIdeal I i := by
  rw [integralIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  have h : (localize n).comp (rawToIntegral n) = extendCoeffs n := by
    have hbase : (algebraMap Seeds SeedField).comp (MvPolynomial.C : FX →+* Seeds) =
        algebraMap FX SeedField :=
      (IsScalarTower.algebraMap_eq FX Seeds SeedField).symm
    apply RingHom.ext
    intro f
    change MvPolynomial.map (algebraMap Seeds SeedField) (MvPolynomial.map MvPolynomial.C f) =
      MvPolynomial.map (algebraMap FX SeedField) f
    rw [MvPolynomial.map_map, hbase]
  rw [h]
  have hr : localize n (relation i) = ySection i := by
    change MvPolynomial.map (algebraMap Seeds SeedField) (relation i) = ySection i
    simp only [relation, ySection, map_sub, MvPolynomial.map_X, MvPolynomial.map_C, generic]
  rw [hr]
def rawToJet (I : Ideal Ambient) : CoordinateRing (rootImage I) →+* CoordinateRing I :=
  Ideal.quotientMap I rootIncl le_rfl
theorem rawToJet_injective (I : Ideal Ambient) : Function.Injective (rawToJet I) :=
  Ideal.quotientMap_injective
theorem rawToJet_coord (I : Ideal Ambient) (k : Fin 3) :
    rawToJet I (coord (rootImage I) k) = coord I (keep k) := by
  simp [rawToJet, rootIncl]
theorem eliminate_incl (I : Ideal Ambient) :
    (eliminate I 2).comp (incl Seeds).toRingHom =
      (Polynomial.mapRingHom (rawToJet I)).comp (eliminate (rootImage I) 2) := by
  have hp : (Polynomial.mapRingHom (rawToJet I)).comp (parameter (rootImage I) 2) =
      parameter I 2 := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [parameter, rawToJet, rootIncl, MvPolynomial.algebraMap_eq]
      rfl
    · intro k
      fin_cases k
      · simp [parameter]
      · simpa [parameter, show keep (2 : Fin 3) = (2 : Fin 4) from rfl] using
          congrArg Polynomial.C (rawToJet_coord I 2)
  apply MvPolynomial.ringHom_ext
  · intro s
    simpa [eliminate] using (RingHom.congr_fun hp s).symm
  · intro k
    simpa [eliminate] using (congrArg Polynomial.C (rawToJet_coord I k)).symm
theorem integral_mem_of_incl (I : Ideal Ambient) (f : Integral 3)
    (hf : incl Seeds f ∈ integralIdeal I 2) : f ∈ integralIdeal (rootImage I) 2 := by
  rw [mem_integralIdeal_iff] at hf ⊢
  have h := RingHom.congr_fun (eliminate_incl I) f
  exact (Polynomial.map_eq_zero_iff (rawToJet_injective I)).mp (h.symm.trans hf)
theorem localize_incl (f : Integral 3) :
    incl SeedField (localize 3 f) = localize 4 (incl Seeds f) :=
  (MvPolynomial.map_rename (algebraMap Seeds SeedField) keep f).symm
theorem section_le (I : Ideal Ambient) :
    sectionIdeal (rootImage I) 2 ≤ (sectionIdeal I 2).comap (incl SeedField).toRingHom := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
  · intro p hp
    change incl SeedField (extendCoeffs 3 p) ∈ sectionIdeal I 2
    rw [← MvPolynomial.map_rename]
    exact (show I.map (extendCoeffs 4) ≤ sectionIdeal I 2 from le_sup_left)
      (Ideal.mem_map_of_mem (extendCoeffs 4) hp)
  · rintro q (rfl : q = ySection (2 : Fin 3))
    change incl SeedField (ySection (2 : Fin 3)) ∈ sectionIdeal I 2
    have hy : incl SeedField (ySection (2 : Fin 3)) = ySection (2 : Fin 4) := by
      simp [ySection, show keep (2 : Fin 3) = (2 : Fin 4) from rfl]
    rw [hy]
    exact (show Ideal.span {ySection (2 : Fin 4)} ≤ sectionIdeal I 2 from le_sup_right)
      (Ideal.mem_span_singleton_self _)
theorem localized_mem_of_incl (I : Ideal Ambient) (f : Integral 3)
    (hf : localize 4 (incl Seeds f) ∈ sectionIdeal I 2) :
    localize 3 f ∈ sectionIdeal (rootImage I) 2 := by
  rw [← map_integralIdeal] at hf ⊢
  obtain ⟨_, ⟨d, hd, rfl⟩, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (denominators 4)
      (Over 4) (integralIdeal I 2) (incl Seeds f)).mp hf
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (denominators 3)]
  refine ⟨MvPolynomial.C d, Submonoid.mem_map_of_mem _ hd, ?_⟩
  apply integral_mem_of_incl I
  simpa only [map_mul, MvPolynomial.rename_C] using hmem
theorem section_mem_of_incl (I : Ideal Ambient) (f : Over 3)
    (hf : incl SeedField f ∈ sectionIdeal I 2) :
    f ∈ sectionIdeal (rootImage I) 2 := by
  obtain ⟨⟨g, m⟩, hm⟩ := IsLocalization.surj
    (M := denominators 3) f
  obtain ⟨d, hd, hdm⟩ := m.property
  have heq : f * MvPolynomial.C (algebraMap Seeds SeedField d) = localize 3 g := by
    simpa only [← hdm, MvPolynomial.algebraMap_def, MvPolynomial.map_C] using hm
  have hg : localize 4 (incl Seeds g) ∈ sectionIdeal I 2 := by
    rw [← localize_incl, ← heq, map_mul]
    exact Ideal.mul_mem_right _ _ hf
  have hu : IsUnit (MvPolynomial.C (σ := Fin 3) (algebraMap Seeds SeedField d)) :=
    (IsLocalization.map_units SeedField (⟨d, hd⟩ : nonZeroDivisors Seeds)).map MvPolynomial.C
  apply (Ideal.mul_unit_mem_iff_mem _ hu).mp
  rw [heq]
  exact localized_mem_of_incl I g hg
private def toJet (I : Ideal Ambient) : RootYSection (rootImage I) →ₐ[SeedField] JetYSection I :=
  Ideal.quotientMapₐ (sectionIdeal I 2) (incl SeedField) (section_le I)
theorem proof : K1_14_2_3_2.c2 := by
  intro I
  refine ⟨toJet I, (injective_iff_map_eq_zero _).mpr ?_⟩
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply section_mem_of_incl I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [toJet, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk] using hx
end
end K1_14_2_3_2_2
end
section
namespace K1_13_4_2_3_1
open K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem slot_grade (a : Shape) (q : ℕ) (s : Slot a q) :
    grade (exponent a q s) = q := by
  have h₂ := s.1.isLt
  have h₁ := s.2.isLt
  simp only [Nat.lt_succ_iff, le_min_iff] at h₂ h₁
  simp [grade, exponent]
  omega
theorem slot_of_exp (a : Shape) (q : ℕ) (e : Exp) (h : grade e = q)
    (hw : weight e ≤ a.j) (ht : e 2 ≤ a.t) : ∃ s : Slot a q, exponent a q s = e := by
  unfold grade at h
  unfold weight at hw
  let e₂ : Fin (min q (min a.t (a.j / 2)) + 1) := ⟨e 2, by
    apply Nat.lt_succ_of_le
    simp only [le_min_iff]
    omega⟩
  let e₁ : Fin (min (q - e₂.val) (a.j - 2 * e₂.val) + 1) := ⟨e 1, by
    apply Nat.lt_succ_of_le
    simp only [le_min_iff, e₂]
    omega⟩
  refine ⟨⟨e₂, e₁⟩, ?_⟩
  ext i
  fin_cases i <;> simp [exponent, e₂, e₁]
  omega
private theorem exponent_injective (a : Shape) (q : ℕ) :
    Function.Injective (exponent a q) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hi := DFunLike.congr_fun h 2
  have hj := DFunLike.congr_fun h 1
  simp [exponent] at hi hj
  have he : i = i' := Fin.ext hi
  subst i'
  exact congrArg (Sigma.mk i) (Fin.ext hj)
def testEquiv (a : Shape) (q : ℕ) :
    Test a q ≃ (Fin (a.b + a.j - q) × Slot a q) := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin, gradeCount]
  rw [Fin.sum_univ_eq_sum_range (fun e : ℕ => min (q - e) (a.j - 2 * e) + 1)]
private abbrev part {R : Type*} [CommRing R] (q : ℕ) :
    K1_13_4_2_3_1.Jets R →ₗ[R] K1_13_4_2_3_1.Jets R :=
  MvPolynomial.homogeneousComponent q
theorem coeff_part {R : Type*} [CommRing R] (q : ℕ) (G : K1_13_4_2_3_1.Jets R) (e : Exp) :
    (part q G).coeff e = if grade e = q then G.coeff e else 0 := by
  rw [MvPolynomial.coeff_homogeneousComponent, Finsupp.degree_eq_sum, Fin.sum_univ_three]
  simp [grade, Nat.add_assoc]
theorem part_canonical {R : Type*} [CommRing R] (t : R) (q : ℕ) (G : K1_13_4_2_3_1.Jets R) :
    part q (canonical t G) = canonical t (part q G) := by
  classical
  induction G using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial d r =>
      have hmono (P : K1_13_4_2_3_1.Jets R) (hP : ∀ e ∈ P.support, grade e = grade d) :
          part q P = if grade d = q then P else 0 := by
        apply MvPolynomial.ext
        intro e
        rw [coeff_part]
        by_cases he : e ∈ P.support
        · rw [hP e he]
          split <;> simp_all
        · split_ifs <;> simp [MvPolynomial.notMem_support_iff.mp he]
      have hd (e : Exp) (he : e ∈ (MvPolynomial.monomial d r).support) : grade e = grade d :=
        congrArg grade (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he))
      rw [hmono _ hd, hmono]
      · split <;> simp
      · intro e he
        obtain ⟨f, hf, h, _⟩ := canonical_support _ _ he
        exact h.trans (hd _ hf)
theorem part_cap {a : Shape} {R : Type*} [CommRing R] {q : ℕ} {G : K1_13_4_2_3_1.Jets R}
    (hG : ∀ e ∈ G.support, admissible a e) {e : Exp} (he : e ∈ (part q G).support) :
    grade e = q ∧ weight e ≤ a.j ∧ e 2 ≤ a.t := by
  rw [MvPolynomial.mem_support_iff, coeff_part] at he
  split at he
  next h => exact ⟨h, (hG _ (MvPolynomial.mem_support_iff.mpr he)).2⟩
  next => contradiction
private def term {R : Type*} [CommRing R] (a : Shape) (q : ℕ) (c : JetCoeff a q) : K1_13_4_2_3_1.Jets R[X] :=
  MvPolynomial.monomial (exponent a q c.2) (Polynomial.X ^ c.1.val)
private def trunc {R : Type*} [CommRing R] (a : Shape) (q : ℕ) (G : K1_13_4_2_3_1.Jets R[X]) : K1_13_4_2_3_1.Jets R[X] :=
  ∑ c : JetCoeff a q, MvPolynomial.C (Polynomial.C ((G.coeff (exponent a q c.2)).coeff c.1.val)) *
    term a q c
theorem coeff_trunc {R : Type*} [CommRing R] {a : Shape} {q : ℕ} (G : K1_13_4_2_3_1.Jets R[X])
    (e : Exp) (n : ℕ) (hn : n < a.b + a.j)
    (hG : G.coeff e ≠ 0 → ∃ s : Slot a q, exponent a q s = e) :
    ((trunc a q G).coeff e).coeff n = (G.coeff e).coeff n := by
  classical
  simp only [trunc, term, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  by_cases he : ∃ s : Slot a q, exponent a q s = e
  · obtain ⟨s, rfl⟩ := he
    rw [Finset.sum_eq_single (⟨⟨n, hn⟩, s⟩ : JetCoeff a q)]
    · simp
    · rintro ⟨k, f⟩ _ hne
      by_cases hf : f = s
      · subst f
        have hk : n ≠ k.val := by
          intro h
          exact hne (Prod.ext (Fin.ext h.symm) rfl)
        simp [Polynomial.coeff_X_pow, hk]
      · have hne' := (exponent_injective a q).ne hf
        simp [hne']
    · simp
  · have hz : G.coeff e = 0 := by
      by_contra h
      exact he (hG h)
    rw [hz, Polynomial.coeff_zero]
    apply Finset.sum_eq_zero
    intro c _
    have hne : exponent a q c.2 ≠ e := fun h => he ⟨c.2, h⟩
    simp [hne]
theorem probe_trunc {R : Type*} [CommRing R] {a : Shape} {q : ℕ} (G : K1_13_4_2_3_1.Jets R[X])
    (hG : ∀ e ∈ G.support, grade e = q ∧ weight e ≤ a.j ∧ e 2 ≤ a.t)
    (e : Exp) (i : Fin (a.b + a.j - q)) :
    probe q e i.val G = probe q e i.val (trunc a q G) := by
  have hcoeff (f : Exp) (n : ℕ) (hn : n < a.b + a.j) :
      ((trunc a q G).coeff f).coeff n = (G.coeff f).coeff n := by
    apply coeff_trunc _ _ _ hn
    intro hf
    obtain ⟨hg, hw, ht⟩ := hG f (MvPolynomial.mem_support_iff.mpr hf)
    exact slot_of_exp a q f hg hw ht
  have hdiv : MvPolynomial.C ((Polynomial.X : R[X]) ^ (a.b + a.j)) ∣ G - trunc a q G := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro f
    rw [Polynomial.X_pow_dvd_iff]
    intro n hn
    simp [hcoeff f n hn]
  have himg := map_dvd (canonical (Polynomial.X : R[X])) hdiv
  rw [canonical_C, map_sub, MvPolynomial.C_dvd_iff_dvd_coeff] at himg
  unfold probe
  split
  · exact (hcoeff e _ (by have := i.isLt; omega)).symm
  · have h := (Polynomial.X_pow_dvd_iff.mp (himg e)) (q + i.val)
      (by have := i.isLt; omega)
    simpa [sub_eq_zero] using h
theorem probe_sum {R : Type*} [CommRing R] {a : Shape} {q : ℕ}
    (G : K1_13_4_2_3_1.Jets R[X]) (e : Exp) (i : ℕ) :
    probe q e i (trunc a q G) = ∑ c : JetCoeff a q,
      ((G.coeff (exponent a q c.2)).coeff c.1.val) * probe q e i (term a q c) := by
  by_cases h : i < weight e <;>
    simp [probe, h, trunc, map_sum, map_mul, MvPolynomial.coeff_C_mul,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
theorem probe_term_map (a : Shape) (q : ℕ) (c : JetCoeff a q) (e : Exp) (i : ℕ) :
    probe (R := GenericSeed) q e i (term a q c) =
      algebraMap Geom GenericSeed (probe q e i (term a q c)) := by
  let f := Polynomial.mapRingHom (algebraMap Geom GenericSeed)
  have hterm : MvPolynomial.map f (term a q c) = term a q c := by simp [term, f]
  have himg : MvPolynomial.map f (canonical Polynomial.X (term a q c)) =
      canonical Polynomial.X (term a q c) := by
    rw [map_canonical, hterm]
    simp [f]
  by_cases h : i < weight e
  · simp only [probe, ite_eq_left h]
    rw [← hterm, MvPolynomial.coeff_map]
    simp [f, Polynomial.coeff_map]
  · simp only [probe, ite_eq_right h]
    rw [← himg, MvPolynomial.coeff_map]
    simp [f, Polynomial.coeff_map]
theorem proof : K1_13_4_2_3.c1 := by
  classical
  intro a α
  let L := a.b + a.j
  let F := MvPolynomial.mapEquiv (Fin 3)
    (Polynomial.taylorEquiv (algebraMap Geom GenericSeed α)).toRingEquiv
  have hF (G : RawRow) (e : Exp) :
      (F G).coeff e = (G.coeff e).taylor (algebraMap Geom GenericSeed α) := by
    exact MvPolynomial.coeff_map
      (Polynomial.taylorEquiv (algebraMap Geom GenericSeed α)).toRingEquiv.toRingHom G e
  have hX : (Polynomial.taylorEquiv (algebraMap Geom GenericSeed α)) (localPole α) =
      Polynomial.X := by
    change Polynomial.taylor (algebraMap Geom GenericSeed α) (localPole α) = _
    simp [localPole]
  refine ⟨fun q i c =>
    let es := testEquiv a q.val i
    probe q.val (exponent a q.val es.2) es.1.val (term a q.val c), ?_⟩
  intro G hG
  have hcap (e : Exp) (he : e ∈ (F G).support) : admissible a e := by
    apply hG e
    rw [MvPolynomial.mem_support_iff, hF] at he
    exact MvPolynomial.mem_support_iff.mpr (fun h => he (by simp [h]))
  have htranslated (H : RawRow) : F (canonical (localPole α) H) =
      canonical Polynomial.X (F H) := by
    simpa [F, hX] using map_canonical
      (Polynomial.taylorEquiv (algebraMap Geom GenericSeed α)).toRingEquiv.toRingHom
      (localPole α) H
  rw [← map_dvd_iff F, map_pow, htranslated]
  have hpow : F (MvPolynomial.C (localPole α)) = MvPolynomial.C (Polynomial.X : GenericSeed[X]) := by
    simpa [F] using congrArg (MvPolynomial.C (σ := Fin 3)) hX
  rw [hpow, ← map_pow]
  have hgrade (q : Fin (a.b + 1)) (e : Exp) (he : e ∈ (part q.val (F G)).support) :
      grade e = q.val ∧ q.val + weight e ≤ L := by
    obtain ⟨hg, hw, _⟩ := part_cap hcap he
    exact ⟨hg, Nat.add_le_add (Nat.le_of_lt_succ q.isLt) hw⟩
  have hprobes (q : Fin (a.b + 1)) :
      MvPolynomial.C ((Polynomial.X : GenericSeed[X]) ^ L) ∣
          part q.val (canonical Polynomial.X (F G)) ↔
        ∀ i : Test a q.val,
          probe q.val (exponent a q.val (testEquiv a q.val i).2)
            (testEquiv a q.val i).1.val (part q.val (F G)) = 0 := by
    rw [part_canonical, grade_probe_iff _ _ _ (hgrade q) (by have := q.isLt; omega)]
    constructor
    · intro h i
      exact h _ _ (testEquiv a q.val i).1.isLt
    · intro h e i hi
      let P := part q.val (F G)
      by_cases he : ∃ s : Slot a q.val, exponent a q.val s = e
      · obtain ⟨s, rfl⟩ := he
        simpa using h ((testEquiv a q.val).symm (⟨i, hi⟩, s))
      · have hP : P.coeff e = 0 := by
          apply MvPolynomial.notMem_support_iff.mp
          intro hm
          obtain ⟨hg, hw, ht⟩ := part_cap hcap hm
          exact he (slot_of_exp a q.val e hg hw ht)
        have hA : (canonical Polynomial.X P).coeff e = 0 := by
          apply MvPolynomial.notMem_support_iff.mp
          intro hm
          obtain ⟨d, hd, hg, hw, ht⟩ := canonical_support _ _ hm
          obtain ⟨hg', hw', ht'⟩ := part_cap hcap hd
          exact he (slot_of_exp a q.val e (hg.trans hg') (hw.trans hw') (ht.trans ht'))
        change probe q.val e i P = 0
        simp [probe, hP, hA]
  have hdot (q : Fin (a.b + 1)) (i : Test a q.val) :
      probe q.val (exponent a q.val (testEquiv a q.val i).2)
        (testEquiv a q.val i).1.val (part q.val (F G)) =
          dot a α q.val (fun c => probe q.val (exponent a q.val (testEquiv a q.val i).2)
            (testEquiv a q.val i).1.val (term a q.val c)) G := by
    rw [probe_trunc _ (fun _ he => part_cap hcap he), probe_sum, dot]
    apply Finset.sum_congr rfl
    intro c _
    rw [probe_term_map, coeff_part, slot_grade a q.val c.2, ite_eq_left rfl, hF, localCoeff, mul_comm]
  have hparts :
      MvPolynomial.C ((Polynomial.X : GenericSeed[X]) ^ L) ∣ canonical Polynomial.X (F G) ↔
        ∀ q : Fin (a.b + 1), MvPolynomial.C ((Polynomial.X : GenericSeed[X]) ^ L) ∣
          part q.val (canonical Polynomial.X (F G)) := by
    simp only [MvPolynomial.C_dvd_iff_dvd_coeff, coeff_part]
    constructor
    · intro h q e
      split
      · exact h e
      · exact dvd_zero _
    · intro h e
      by_cases he : e ∈ (canonical Polynomial.X (F G)).support
      · obtain ⟨d, hd, hg, _⟩ := canonical_support _ _ he
        have hb : grade e ≤ a.b := hg.le.trans (hcap d hd).1
        simpa using h ⟨grade e, Nat.lt_succ_of_le hb⟩ e
      · rw [MvPolynomial.notMem_support_iff.mp he]
        exact dvd_zero _
  rw [hparts]
  simp_rw [hprobes, hdot]
end
end K1_13_4_2_3_1
end
section
namespace K1_13_4_2_4_2
noncomputable section
set_option maxHeartbeats 600000
open K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_4 Polynomial
open scoped Polynomial BigOperators
abbrev PolynomialRow := MvPolynomial (Fin 3) ShiftSeed[X]
private def constSeed : Geom →+* ShiftSeed :=
  Polynomial.C.comp (Polynomial.C : Geom →+* Geom[X])
private def fibreSeed (ε : Geom) : ShiftSeed →+* GenericSeed :=
  (algebraMap Geom[X] GenericSeed).comp (specializeShift ε)
private def fibre (ε : Geom) : PolynomialRow →+* RawRow :=
  MvPolynomial.map (Polynomial.mapRingHom (fibreSeed ε))
@[simp] private theorem fibreSeed_const (ε c : Geom) :
    fibreSeed ε (constSeed c) = algebraMap Geom GenericSeed c := by
  rw [IsScalarTower.algebraMap_apply Geom Geom[X] GenericSeed]
  simp [fibreSeed, constSeed, specializeShift]
@[simp] private theorem fibreSeed_comp (ε : Geom) :
    (fibreSeed ε).comp constSeed = algebraMap Geom GenericSeed :=
  RingHom.ext (fibreSeed_const ε)
def formalBlock (H : Geom[X]) : ShiftSeed[X] :=
  H.map constSeed + Polynomial.C (Polynomial.C Polynomial.X)
theorem formalBlock_monic {H : Geom[X]} (hm : H.Monic) (hp : 0 < H.natDegree) :
    (formalBlock H).Monic := by
  apply (hm.map constSeed).add_of_left
  exact degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp (by
    rwa [hm.natDegree_map]))
@[simp] private theorem formalBlock_fibre (H : Geom[X]) (ε : Geom) :
    (formalBlock H).map (fibreSeed ε) = liftX (shiftedBlock H ε) := by
  have h : fibreSeed ε (Polynomial.C Polynomial.X) =
      algebraMap Geom GenericSeed ε := by
    rw [IsScalarTower.algebraMap_apply Geom Geom[X] GenericSeed]
    simp [fibreSeed, specializeShift]
  simp [formalBlock, liftX, shiftedBlock, Polynomial.map_map, h]
def rawConst {A : Type*} [CommRing A] (a : A) : MvPolynomial (Fin 3) A[X] :=
  MvPolynomial.C (Polynomial.C a)
@[simp] private theorem fibre_rawConst (ε : Geom) (a : ShiftSeed) :
    fibre ε (rawConst a) = rawConst (fibreSeed ε a) := by
  simp [fibre, rawConst]
def homogeneousJet {A : Type*} [CommRing A] (B : A[X]) (i : Fin 3) :
    MvPolynomial (Fin 3) A[X] :=
  ∑ j : Fin 3, if j.val ≤ i.val then
    MvPolynomial.C (hasseDeriv (i.val - j.val) B) * MvPolynomial.X j
  else 0
@[simp] private theorem fibre_homogeneousJet (ε : Geom) (B : ShiftSeed[X]) (i : Fin 3) :
    fibre ε (homogeneousJet B i) = homogeneousJet (B.map (fibreSeed ε)) i := by
  simp [fibre, homogeneousJet, apply_ite, ← hasseDeriv_map]
private def restoreHom (H : Geom[X]) (R : GenericSeed[X]) : PhysicalRow →+* RawRow :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap Geom GenericSeed)))
    (fun i : SeedVar => i.elim
      (rawConst (algebraMap Geom[X] GenericSeed Polynomial.X))
      (fun j => MvPolynomial.C (hasseDeriv j.val R) + homogeneousJet (liftX H) j))
theorem restoreHom_apply (H : Geom[X]) (R : GenericSeed[X]) (F : PhysicalRow) :
    restoreHom H R F = restoreWith H R F := rfl
theorem fibreSeed_ne_zero (ε : Geom) {D : ShiftSeed} (hD : specializeShift ε D ≠ 0) :
    fibreSeed ε D ≠ 0 := by
  intro hz
  exact hD ((IsFractionRing.injective Geom[X] GenericSeed)
    (hz.trans (map_zero (algebraMap Geom[X] GenericSeed)).symm))
theorem residue_hasse (N : ShiftSeed[X]) (D : ShiftSeed) (ε : Geom) (i : ℕ) :
    hasseDeriv i (residueAtShift N D ε) =
      Polynomial.C ((fibreSeed ε D)⁻¹) * (hasseDeriv i N).map (fibreSeed ε) := by
  simp only [residueAtShift, genericResidue, Polynomial.map_map, fibreSeed, RingHom.comp_apply,
    ← Polynomial.smul_eq_C_mul, map_smul, hasseDeriv_map]
theorem rawConst_mul_C_inv {d : GenericSeed} (hd : d ≠ 0) (p : GenericSeed[X]) :
    rawConst d * (MvPolynomial.C (Polynomial.C d⁻¹ * p) : RawRow) = MvPolynomial.C p := by
  have hc : Polynomial.C d * (Polynomial.C d⁻¹ * p) = p := by
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hd, Polynomial.C_1, one_mul]
  calc
    _ = (MvPolynomial.C (Polynomial.C d * (Polynomial.C d⁻¹ * p)) : RawRow) :=
      (MvPolynomial.C_mul (σ := Fin 3)).symm
    _ = _ := congrArg (MvPolynomial.C : GenericSeed[X] →+* RawRow) hc
theorem clear_variable (H : Geom[X]) (N : ShiftSeed[X]) (D : ShiftSeed) (i : SeedVar) :
    ∃ (r : ℕ) (P : PolynomialRow), ∀ ε, specializeShift ε D ≠ 0 →
      fibre ε P = (rawConst (fibreSeed ε D)) ^ r *
        restoreHom (shiftedBlock H ε) (residueAtShift N D ε) (MvPolynomial.X i) := by
  cases i with
  | none =>
    refine ⟨0, rawConst Polynomial.X, fun ε _ => ?_⟩
    simp [restoreHom, fibreSeed, specializeShift]
  | some i =>
    refine ⟨1, MvPolynomial.C (hasseDeriv i.val N) +
      rawConst D * homogeneousJet (formalBlock H) i, fun ε hD => ?_⟩
    simp only [map_add, map_mul, fibre_rawConst, fibre_homogeneousJet,
      formalBlock_fibre, pow_one, restoreHom, MvPolynomial.eval₂Hom_X', Option.elim_some,
      residue_hasse, mul_add]
    congr 1
    simpa only [fibre, MvPolynomial.map_C, Polynomial.coe_mapRingHom, MvPolynomial.C_mul] using
      (rawConst_mul_C_inv (fibreSeed_ne_zero ε hD)
        ((hasseDeriv i.val N).map (fibreSeed ε))).symm
theorem clear_row (H : Geom[X]) (N : ShiftSeed[X]) (D : ShiftSeed) (F : PhysicalRow) :
    ∃ (r : ℕ) (P : PolynomialRow), ∀ ε, specializeShift ε D ≠ 0 →
      fibre ε P = (rawConst (fibreSeed ε D)) ^ r *
        restoreHom (shiftedBlock H ε) (residueAtShift N D ε) F := by
  induction F using MvPolynomial.induction_on with
  | C p =>
    refine ⟨0, MvPolynomial.C (p.map constSeed), fun ε _ => ?_⟩
    simp [fibre, restoreHom, Polynomial.map_map]
  | add p q hp hq =>
    obtain ⟨r, P, hP⟩ := hp
    obtain ⟨s, Q, hQ⟩ := hq
    refine ⟨r + s, rawConst D ^ s * P + rawConst D ^ r * Q, fun ε hD => ?_⟩
    simp only [map_add, map_mul, map_pow, fibre_rawConst, hP ε hD, hQ ε hD, pow_add, mul_add]
    rw [← mul_assoc, ← mul_assoc, mul_comm (rawConst (fibreSeed ε D) ^ s)
      (rawConst (fibreSeed ε D) ^ r)]
  | mul_X p i hp =>
    obtain ⟨r, P, hP⟩ := hp
    obtain ⟨s, Q, hQ⟩ := clear_variable H N D i
    refine ⟨r + s, P * Q, fun ε hD => ?_⟩
    simp only [map_mul, hP ε hD, hQ ε hD, pow_add]
    exact mul_mul_mul_comm _ _ _ _
theorem clear_columns (H : Geom[X]) (N : ShiftSeed[X]) (D : ShiftSeed)
    {m : ℕ} (F : Fin m → PhysicalRow) :
    ∃ (r : ℕ) (P : Fin m → PolynomialRow), ∀ ε, specializeShift ε D ≠ 0 → ∀ j,
      fibre ε (P j) = (rawConst (fibreSeed ε D)) ^ r *
        restoreHom (shiftedBlock H ε) (residueAtShift N D ε) (F j) := by
  classical
  choose r P hP using fun j => clear_row H N D (F j)
  let b := Finset.univ.sup r
  refine ⟨b, fun j => rawConst D ^ (b - r j) * P j, fun ε hD j => ?_⟩
  have hj : r j ≤ b := Finset.le_sup (Finset.mem_univ j)
  rw [map_mul, map_pow, fibre_rawConst, hP j ε hD, ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel hj]
private def combine {m : ℕ} (P : Fin m → PolynomialRow) (v : Fin m → Geom) : PolynomialRow :=
  ∑ j, rawConst (constSeed (v j)) * P j
theorem restoreHom_smul (H : Geom[X]) (R : GenericSeed[X]) (a : Geom)
    (F : PhysicalRow) :
    restoreHom H R (a • F) = rawConst (algebraMap Geom GenericSeed a) * restoreHom H R F := by
  have hs : a • F = MvPolynomial.C (Polynomial.C a) * F := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply Geom Geom[X] PhysicalRow,
      MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq]
  rw [hs, map_mul]
  simp only [restoreHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_C, rawConst]
theorem fibre_combine {H : Geom[X]} {N : ShiftSeed[X]} {D : ShiftSeed}
    {ε : Geom} {m r : ℕ} (P : Fin m → PolynomialRow) (F : Fin m → PhysicalRow)
    (hP : ∀ j, fibre ε (P j) = rawConst (fibreSeed ε D) ^ r *
      restoreHom (shiftedBlock H ε) (residueAtShift N D ε) (F j)) (v : Fin m → Geom) :
    fibre ε (combine P v) = rawConst (fibreSeed ε D) ^ r *
      restoreHom (shiftedBlock H ε) (residueAtShift N D ε) (∑ j, v j • F j) := by
  rw [combine, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, fibre_rawConst, fibreSeed_const, hP j, restoreHom_smul]
  exact mul_left_comm _ _ _
private abbrev Coordinate := (Fin 3 →₀ ℕ) × ℕ × ℕ
private def entry (B : ShiftSeed[X]) (P : PolynomialRow) (u : Coordinate) : Geom[X] :=
  (((P.coeff u.1) %ₘ B).coeff u.2.1).coeff u.2.2
private def coordinates (B : ShiftSeed[X]) (P : PolynomialRow) : Finset Coordinate := by
  classical
  exact P.support.biUnion fun a =>
    ((P.coeff a) %ₘ B).support.biUnion fun i =>
      (((P.coeff a) %ₘ B).coeff i).support.image fun j => (a, i, j)
theorem mem_coordinates {B : ShiftSeed[X]} {P : PolynomialRow} {u : Coordinate}
    (he : entry B P u ≠ 0) : u ∈ coordinates B P := by
  classical
  obtain ⟨a, i, j⟩ := u
  have hi : ((P.coeff a) %ₘ B).coeff i ≠ 0 := by
    intro h
    exact he (by simp [entry, h])
  have ha : P.coeff a ≠ 0 := by
    intro h
    exact hi (by simp [h])
  exact Finset.mem_biUnion.mpr ⟨a, MvPolynomial.mem_support_iff.mpr ha,
    Finset.mem_biUnion.mpr ⟨i, Polynomial.mem_support_iff.mpr hi,
      Finset.mem_image.mpr ⟨j, Polynomial.mem_support_iff.mpr he, rfl⟩⟩⟩
theorem entry_combine {m : ℕ} (B : ShiftSeed[X]) (P : Fin m → PolynomialRow)
    (v : Fin m → Geom) (u : Coordinate) :
    entry B (combine P v) u = ∑ j, Polynomial.C (v j) * entry B (P j) u := by
  have h :
      (∑ j, Polynomial.C (constSeed (v j)) * (P j).coeff u.1) %ₘ B =
      ∑ j, Polynomial.C (constSeed (v j)) * ((P j).coeff u.1 %ₘ B) := by
    simp only [← Polynomial.smul_eq_C_mul, ← modByMonicHom_apply, map_sum, map_smul]
  simp only [entry, combine, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, rawConst, h]
  simp only [
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, constSeed, RingHom.comp_apply]
theorem fibre_dvd_iff_entries (B : ShiftSeed[X]) (hB : B.Monic) (P : PolynomialRow)
    (ε : Geom) :
    MvPolynomial.C (B.map (fibreSeed ε)) ∣ fibre ε P ↔
      ∀ u, evalRingHom ε (entry B P u) = 0 := by
  rw [MvPolynomial.C_dvd_iff_dvd_coeff]
  have hcoeff (a : Fin 3 →₀ ℕ) :
      B.map (fibreSeed ε) ∣ (fibre ε P).coeff a ↔
        ∀ i j, evalRingHom ε (entry B P (a, i, j)) = 0 := by
    rw [← modByMonic_eq_zero_iff_dvd (hB.map (fibreSeed ε))]
    simp only [fibre, MvPolynomial.coeff_map, Polynomial.coe_mapRingHom, ← map_modByMonic _ hB,
      Polynomial.ext_iff, coeff_map, coeff_zero, fibreSeed, RingHom.comp_apply,
      map_eq_zero_iff _ (IsFractionRing.injective Geom[X] GenericSeed), specializeShift]
    rfl
  exact ⟨fun h u => (hcoeff u.1).mp (h u.1) u.2.1 u.2.2,
    fun h a => (hcoeff a).mpr (fun i j => h (a, i, j))⟩
theorem proof : K1_13_4_2_4.c2 := by
  classical
  intro H hm hp N D n m F
  obtain ⟨r, P, hP⟩ := clear_columns H N D F
  let B := formalBlock H ^ n
  have hB : B.Monic := (formalBlock_monic hm hp).pow n
  let T := Finset.univ.biUnion fun j : Fin m => coordinates B (P j)
  let e := T.equivFin.symm
  let M : Matrix (Fin T.card) (Fin m) Geom[X] := fun i j => entry B (P j) (e i)
  refine ⟨T.card, M, fun ε hD v => ?_⟩
  have htest (i : Fin T.card) :
      ((M.map (evalRingHom ε)).mulVecLin v) i = evalRingHom ε (entry B (combine P v) (e i)) := by
    change (∑ j, evalRingHom ε (entry B (P j) (e i)) * v j) = _
    rw [entry_combine, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    change _ = (Polynomial.C (v j)).eval ε * _
    rw [eval_C, mul_comm]
  have hmatrix : (M.map (evalRingHom ε)).mulVecLin v = 0 ↔
      ∀ u, evalRingHom ε (entry B (combine P v) u) = 0 := by
    constructor
    · intro hz u
      by_cases hu : u ∈ T
      · let i := T.equivFin ⟨u, hu⟩
        have hi := congrFun hz i
        rw [htest] at hi
        simpa [i, e] using hi
      · have hcol (j : Fin m) : entry B (P j) u = 0 :=
          not_ne_iff.mp fun h => hu (Finset.mem_biUnion.mpr
            ⟨j, Finset.mem_univ _, mem_coordinates h⟩)
        simp [entry_combine, hcol]
    · intro hz
      funext i
      exact (htest i).trans (hz (e i))
  have hunit : IsUnit (rawConst (fibreSeed ε D) ^ r) :=
    (((isUnit_iff_ne_zero.mpr (fibreSeed_ne_zero ε hD)).map
      (Polynomial.C : GenericSeed →+* GenericSeed[X])).map
      (MvPolynomial.C : GenericSeed[X] →+* RawRow)).pow r
  rw [hmatrix, ← fibre_dvd_iff_entries B hB, fibre_combine P F (hP ε hD),
    hunit.dvd_mul_left]
  simp only [B, Polynomial.map_pow, formalBlock_fibre, map_pow, restoreHom_apply]
end
end K1_13_4_2_4_2
end
section
namespace K1_13_4_2_2_1
noncomputable section
open K1_13 K1_13_4_2_2 Finset MvPolynomial
open scoped BigOperators
private def weighted (u : ℕ) : Finset (ℕ × ℕ) :=
  ((range (u + 1)).product (range (u + 1))).filter fun p => p.2 + 2 * p.1 ≤ u
theorem mem_weighted (u : ℕ) (p : ℕ × ℕ) :
    p ∈ weighted u ↔ p.2 + 2 * p.1 ≤ u := by
  simp only [weighted, product_eq_sprod, mem_filter, mem_product, mem_range]
  omega
theorem card_weighted (u : ℕ) :
    ((weighted u).card : ℤ) = ((u : ℤ) + 2) ^ 2 / 4 := by
  let m := u / 2
  let n := u - m
  have hmn : m ≤ n ∧ n ≤ m + 1 ∧ u = m + n := by
    dsimp [m, n]
    omega
  have hc : (weighted u).card = (m + 1) * (n + 1) := by
    rw [← card_range (m + 1), ← card_range (n + 1), ← card_product]
    apply card_nbij'
      (fun p => if p.1 + p.2 ≤ n then (p.1, p.1 + p.2) else (u + 1 - (p.1 + p.2), p.1))
      (fun p => if p.1 ≤ p.2 then (p.1, p.2 - p.1) else (p.2, u + 1 - p.1 - p.2))
    · rintro ⟨c, b⟩ h
      simp only [mem_coe, mem_weighted] at h
      simp only [mem_coe, mem_product, mem_range]
      split <;> dsimp <;> omega
    · rintro ⟨x, y⟩ h
      simp only [mem_coe, mem_product, mem_range] at h
      simp only [mem_coe, mem_weighted]
      split <;> dsimp <;> omega
    · rintro ⟨c, b⟩ h
      simp only [mem_coe, mem_weighted] at h
      by_cases hcb : c + b ≤ n
      · have hcc : c ≤ c + b := by omega
        simp [hcb, hcc]
      · have hcc : ¬ u + 1 - (c + b) ≤ c := by omega
        simp [hcb, hcc]
        omega
    · rintro ⟨x, y⟩ h
      simp only [mem_coe, mem_product, mem_range] at h
      by_cases hxy : x ≤ y
      · simp [hxy]
        omega
      · have hxy' : ¬ y + (u + 1 - x - y) ≤ n := by omega
        simp [hxy, hxy']
        omega
  simp only [hc, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hu : (u : ℤ) = (m : ℤ) + n := by omega
  have hn : (n : ℤ) - m = 0 ∨ (n : ℤ) - m = 1 := by omega
  have hsq : ((n : ℤ) - m) ^ 2 = 0 ∨ ((n : ℤ) - m) ^ 2 = 1 := by
    rcases hn with hn | hn <;> simp [hn]
  have hsq' : ((u : ℤ) + 2) ^ 2 =
      4 * ((m + 1 : ℤ) * (n + 1)) + ((n : ℤ) - m) ^ 2 := by
    rw [hu]
    ring
  omega
private def triangle (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (range n).sigma fun i => range (i + 1)
theorem mem_triangle (n : ℕ) (p : Σ _ : ℕ, ℕ) :
    p ∈ triangle n ↔ p.1 < n ∧ p.2 ≤ p.1 := by
  simp [triangle]
theorem card_triangle (n : ℕ) :
    ((triangle n).card : ℤ) = triangular n := by
  simp only [triangle, card_sigma, card_range, Nat.cast_sum, Nat.cast_add, Nat.cast_one]
  have h : ∀ k : ℕ, 2 * (∑ i ∈ range k, ((i : ℤ) + 1)) = (k : ℤ) * (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, Nat.cast_succ, mul_add, ih]; ring
  unfold triangular
  have hn := h n
  omega
theorem card_excluded (d u : ℕ) (hu : u ≤ 2 * d) :
    ((weighted u).filter fun p => ¬ p.1 + p.2 ≤ d).card = (triangle (u - d)).card := by
  apply card_nbij'
    (fun p => ⟨u - (p.1 + p.2), p.1⟩)
    (fun p => (p.2, u - p.1 - p.2))
  · rintro ⟨c, b⟩ h
    simp only [mem_coe, mem_filter, mem_weighted] at h
    simp only [mem_coe, mem_triangle]
    omega
  · rintro ⟨i, c⟩ h
    simp only [mem_coe, mem_triangle] at h
    simp only [mem_coe, mem_filter, mem_weighted]
    omega
  · rintro ⟨c, b⟩ h
    simp only [mem_coe, mem_filter, mem_weighted] at h
    change (c, u - (u - (c + b)) - c) = (c, b)
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨i, c⟩ h
    simp only [mem_coe, mem_triangle] at h
    have hi : u - (c + (u - i - c)) = i := by omega
    change (⟨u - (c + (u - i - c)), c⟩ : Σ _ : ℕ, ℕ) = ⟨i, c⟩
    rw [hi]
def prefixPairs (d : ℕ) (w : ℤ) : Finset (ℕ × ℕ) :=
  if w < 0 then ∅ else
    (weighted (min w (2 * (d : ℤ))).toNat).filter fun p => p.1 + p.2 ≤ d
theorem mem_prefix (d : ℕ) (w : ℤ) (p : ℕ × ℕ) :
    p ∈ prefixPairs d w ↔ p.1 + p.2 ≤ d ∧ (p.2 : ℤ) + 2 * p.1 ≤ w := by
  unfold prefixPairs
  split
  · simp only [notMem_empty, false_iff]
    omega
  · rw [mem_filter, mem_weighted]
    omega
theorem card_prefix (d : ℕ) (w : ℤ) :
    ((prefixPairs d w).card : ℤ) = cumulative d w := by
  by_cases hw : w < 0
  · simp [prefixPairs, cumulative, hw]
  let u := (min w (2 * (d : ℤ))).toNat
  have hu : (u : ℤ) = min w (2 * (d : ℤ)) := by dsimp [u]; omega
  have hud : u ≤ 2 * d := by omega
  have hd : ((u - d : ℕ) : ℤ) = max 0 ((u : ℤ) - d) := by omega
  have h := card_filter_add_card_filter_not (s := weighted u) (fun p => p.1 + p.2 ≤ d)
  rw [card_excluded d u hud] at h
  have h' := congrArg (fun n : ℕ => (n : ℤ)) h
  simp only [Nat.cast_add, card_triangle, card_weighted, hd] at h'
  simp only [prefixPairs, cumulative, ite_eq_right hw]
  change (((weighted u).filter fun p => p.1 + p.2 ≤ d).card : ℤ) =
    (min w (2 * (d : ℤ)) + 2) ^ 2 / 4 - triangular (max 0 (min w (2 * (d : ℤ)) - d))
  rw [← hu]
  omega
private def window (d : ℕ) (g : ℤ) : Finset (ℕ × ℕ) :=
  prefixPairs d 2300 \ prefixPairs d (min 2300 (-g - 1))
theorem mem_window (d : ℕ) (g : ℤ) (p : ℕ × ℕ) :
    p ∈ window d g ↔
      p.1 + p.2 ≤ d ∧ -g ≤ (p.2 : ℤ) + 2 * p.1 ∧ p.2 + 2 * p.1 ≤ 2300 := by
  simp only [window, mem_sdiff, mem_prefix]
  omega
theorem card_window (q : ℕ) (g : ℤ) :
    ((window (residualDegree q) g).card : ℤ) = columnCount q g := by
  have hs : prefixPairs (residualDegree q) (min 2300 (-g - 1)) ⊆ prefixPairs (residualDegree q) 2300 := by
    intro p hp
    rw [mem_prefix] at hp ⊢
    omega
  have hc := card_sdiff_add_card_eq_card hs
  have h := congrArg (fun n : ℕ => (n : ℤ)) hc
  simp only [Nat.cast_add] at h
  change ((window (residualDegree q) g).card : ℤ) +
    ((prefixPairs (residualDegree q) (min 2300 (-g - 1))).card : ℤ) =
    ((prefixPairs (residualDegree q) 2300).card : ℤ) at h
  rw [card_prefix, card_prefix] at h
  exact eq_sub_of_add_eq h
private def exponent (d : ℕ) (p : ℕ × ℕ) : PlaneExp :=
  Finsupp.equivFunOnFinite.symm ![d - (p.1 + p.2), p.2, p.1]
private theorem exponent_injective (d : ℕ) : Function.Injective (exponent d) := by
  intro p r h
  apply Prod.ext
  · simpa [exponent] using congrArg (fun e : PlaneExp => e 2) h
  · simpa [exponent] using congrArg (fun e : PlaneExp => e 1) h
theorem plane_grade (e : PlaneExp) :
    e.weight (fun _ => 1) = e 0 + e 1 + e 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul, add_assoc]
theorem plane_index (e : PlaneExp) :
    e.weight Fin.val = e 1 + 2 * e 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul, Nat.mul_comm]
private theorem columns_eq (q : ℕ) (g : ℤ) :
    (↑((window (residualDegree q) g).image (exponent (residualDegree q))) : Set PlaneExp) =
      planeExponents q g := by
  ext e
  simp only [mem_coe, mem_image, mem_window]
  change _ ↔ e.weight (fun _ => 1) = residualDegree q ∧
    -g ≤ (e.weight Fin.val : ℤ) ∧ e.weight Fin.val ≤ 2300 ∧ e 2 ≤ 1150
  rw [plane_grade, plane_index]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp [exponent]
    omega
  · intro he
    refine ⟨(e 2, e 1), ?_, ?_⟩
    · dsimp
      omega
    · ext j
      fin_cases j <;> simp [exponent]
      omega
theorem source_count (q : ℕ) (g : ℤ) :
    (Module.finrank Geom (PlaneSource q g) : ℤ) = columnCount q g := by
  unfold PlaneSource
  rw [← columns_eq q g, finrank_restrictSupport_finset,
    card_image_of_injective _ (exponent_injective _), card_window]
theorem proof : K1_13_4_2_2.c1 := by
  intro q _ k _
  exact (source_count q (offset k)).le
end
end K1_13_4_2_2_1
end
section
namespace K1_13_6_2_3_2_6
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial
private theorem component_mul {ι σ : Type}
    {w : σ → ι → ℕ} {s : ι → ℕ} {L : MvPolynomial σ GeoField}
    (hL : IsWeightedHomogeneous w L s) (f : MvPolynomial σ GeoField) (a : ι → ℕ) :
    weightedHomogeneousComponent w (a + s) (L * f) =
      L * weightedHomogeneousComponent w a f := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul, Finset.ite_sum_zero]
  apply Finset.sum_congr rfl
  rintro ⟨u, v⟩ huv
  rw [coeff_weightedHomogeneousComponent]
  by_cases hu : L.coeff u = 0
  · simp [hu]
  · have hw : Finsupp.weight w e = a + s ↔ Finsupp.weight w v = a := by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp huv, map_add, hL hu, add_comm s, add_right_cancel_iff]
    simp only [hw]
    split <;> simp_all
theorem component_mul_eq_zero {ι σ : Type}
    {w : σ → ι → ℕ} {s : ι → ℕ} {L : MvPolynomial σ GeoField}
    (hL : IsWeightedHomogeneous w L s) (f : MvPolynomial σ GeoField) (b : ι → ℕ)
    (hb : ¬ ∃ a, b = a + s) :
    weightedHomogeneousComponent w b (L * f) = 0 := by
  classical
  apply weightedHomogeneousComponent_eq_zero'
  intro e he hdeg
  rw [MvPolynomial.mem_support_iff, coeff_mul] at he
  obtain ⟨⟨u, v⟩, huv, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hu : L.coeff u ≠ 0 := fun h => hc (by simp [h])
  apply hb
  refine ⟨Finsupp.weight w v, ?_⟩
  rw [← hdeg, ← Finset.HasAntidiagonal.mem_antidiagonal.mp huv, map_add, hL hu, add_comm]
theorem graded_cut {ι σ : Type} [Fintype ι] [DecidableEq ι]
    (slot : σ → ι) {I : Ideal (MvPolynomial σ GeoField)} {L : MvPolynomial σ GeoField}
    {s : ι → ℕ} (hI : Graded slot I) (hL : IsWeightedHomogeneous (step ∘ slot) L s) :
    Graded slot (I ⊔ Ideal.span {L}) := by
  intro f hf b
  rw [sup_comm, Ideal.mem_span_singleton_sup] at hf
  obtain ⟨g, j, hj, rfl⟩ := hf
  rw [map_add, mul_comm g L]
  apply Ideal.add_mem _
  · by_cases hb : ∃ a, b = a + s
    · obtain ⟨a, rfl⟩ := hb
      rw [component_mul hL]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨_, rfl⟩)
    · rw [component_mul_eq_zero hL g b hb]
      exact Ideal.zero_mem _
  · exact Ideal.mem_sup_left (hI j hj b)
theorem finite_piece {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (a : ι → ℕ) :
    Module.Finite GeoField (weightedHomogeneousSubmodule GeoField (step ∘ slot) a) := by
  classical
  let _ := Fintype.ofFinite σ
  have hd (e : σ →₀ ℕ) : e.degree = ∑ i, Finsupp.weight (step ∘ slot) e i := by
    simp only [Finsupp.degree_eq_sum, Finsupp.weight_eq_sum, Finset.sum_apply,
      Function.comp_apply, Pi.smul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp [step, Pi.single_apply, mul_ite]
  have := ((Finsupp.finite_of_degree_le (∑ i, a i)).subset
    (show {e | Finsupp.weight (step ∘ slot) e = a} ⊆ _ from
      fun e he => le_of_eq ((hd e).trans (congrArg _ he)))).to_subtype
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.of_basis (basisRestrictSupport GeoField _)
theorem hilbert_cut {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (I K : Ideal (MvPolynomial σ GeoField)) (L : MvPolynomial σ GeoField)
    (a s : ι → ℕ) (hI : Graded slot I) (hL : IsWeightedHomogeneous (step ∘ slot) L s)
    (hcolon : ∀ f, L * f ∈ I ↔ f ∈ K) :
    hilbert slot (I ⊔ Ideal.span {L}) (a + s) + hilbert slot K a = hilbert slot I (a + s) := by
  classical
  let w := step ∘ slot
  let S := weightedHomogeneousSubmodule GeoField w a
  let T := weightedHomogeneousSubmodule GeoField w (a + s)
  let B := I ⊔ Ideal.span {L}
  have hIB : I ≤ B := le_sup_left
  let V (J : Ideal (MvPolynomial σ GeoField)) :=
    T.map (Ideal.Quotient.mkₐ GeoField J).toLinearMap
  let src := (Ideal.Quotient.mkₐ GeoField K).toLinearMap.domRestrict S
  let multiply := (Ideal.Quotient.mkₐ GeoField I).toLinearMap.comp (LinearMap.mulLeft GeoField L)
  let mul : S →ₗ[GeoField] V I :=
    (multiply.domRestrict S).codRestrict (V I) (fun g => by
      have hg : IsWeightedHomogeneous w (g : MvPolynomial σ GeoField) a := g.2
      have hprod := hL.mul hg
      rw [add_comm s a] at hprod
      exact Submodule.mem_map.mpr ⟨L * g, hprod, rfl⟩)
  let proj : V I →ₗ[GeoField] V B :=
    ((Ideal.Quotient.factorₐ GeoField hIB).toLinearMap.domRestrict (V I)).codRestrict (V B)
      (fun x => by
        obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
        exact Submodule.mem_map.mpr ⟨f, hf, by
          change Ideal.Quotient.mk B f = Ideal.Quotient.factor hIB x.val
          rw [← hfx]
          rfl⟩)
  have hsurj : Function.Surjective proj := by
    intro x
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
    exact ⟨⟨Ideal.Quotient.mk I f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩⟩, Subtype.ext hfx⟩
  have hker : LinearMap.ker mul = LinearMap.ker src := by
    ext g
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hg
      have hz : Ideal.Quotient.mk I (L * (g : MvPolynomial σ GeoField)) = 0 :=
        congrArg Subtype.val hg
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hcolon _).mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    · intro hg
      exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr ((hcolon _).mpr
        (Ideal.Quotient.eq_zero_iff_mem.mp hg)))
  have hrange : LinearMap.range mul = LinearMap.ker proj := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change Ideal.Quotient.mk B (L * (g : MvPolynomial σ GeoField)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨_, rfl⟩))
    · intro hx
      obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
      have hx0 : Ideal.Quotient.factor hIB x.val = 0 :=
        congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      rw [← hfx] at hx0
      have hfB : f ∈ B := Ideal.Quotient.eq_zero_iff_mem.mp hx0
      change f ∈ I ⊔ Ideal.span {L} at hfB
      rw [sup_comm, Ideal.mem_span_singleton_sup] at hfB
      obtain ⟨g, j, hj, hgj⟩ := hfB
      let g' := weightedHomogeneousComponent w a g
      have he := congrArg (weightedHomogeneousComponent w (a + s)) hgj
      rw [map_add, mul_comm g L, component_mul hL, weightedHomogeneousComponent_eq_self hf] at he
      change L * g' + weightedHomogeneousComponent w (a + s) j = f at he
      refine ⟨⟨g', weightedHomogeneousComponent_mem w g a⟩, Subtype.ext ?_⟩
      change Ideal.Quotient.mk I (L * g') = x.val
      change Ideal.Quotient.mk I f = x.val at hfx
      rw [← hfx, ← he, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (hI j hj (a + s)), add_zero]
  let _ : Module.Finite GeoField S := finite_piece slot a
  let _ : Module.Finite GeoField T := finite_piece slot (a + s)
  let _ : Module.Finite GeoField (V I) := Module.Finite.map _ _
  have hm := mul.finrank_range_add_finrank_ker
  have hk := src.finrank_range_add_finrank_ker
  rw [hrange, hker] at hm
  have hdim : Module.finrank GeoField (LinearMap.ker proj) =
      Module.finrank GeoField (LinearMap.range src) := by omega
  have hp := proj.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hdim] at hp
  dsimp only [src] at hp
  rw [LinearMap.range_domRestrict] at hp
  unfold hilbert
  exact_mod_cast hp
theorem proof : K1_13_6_2_3_2.c6 := by
  classical
  intro ι _ _ shapes i J D hD hreg
  dsimp only
  intro hI hI₂
  obtain ⟨L, hL, heL⟩ := exists_lift shapes i D (box_support hD)
  obtain ⟨M, hM, heM⟩ := exists_lift shapes i (D ^ 2) (box_sq_support hD)
  have hle : cut J (D ^ 2) ≤ cut J D := by
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨D, pow_two D⟩)
  have : Finite (CapVar shapes) := inferInstance
  refine ⟨capIdeal shapes J ⊔ Ideal.span {M}, capIdeal shapes (cut J (D ^ 2)) ⊔ Ideal.span {L},
    graded_cut _ hI hM, graded_cut _ hI₂ hL, ?_, ?_, ?_, ?_⟩
  · exact sup_le (capIdeal_mono shapes le_sup_left)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (lift_mem heM (Ideal.mem_sup_right
        (Ideal.mem_span_singleton_self _)))))
  · exact sup_le (capIdeal_mono shapes hle)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (lift_mem heL (Ideal.mem_sup_right
        (Ideal.mem_span_singleton_self _)))))
  · intro a
    exact hilbert_cut _ _ _ M a _ hI hM
      (lift_mul_mem_iff heM (square_mul_mem_iff J D hreg))
  · intro a
    exact hilbert_cut _ _ _ L a _ hI₂ hL
      (lift_mul_mem_iff heL (cut_square_mul_mem_iff J D hreg))
end
end K1_13_6_2_3_2_6
end
section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
namespace K1_14_2_1_1
noncomputable section
open K1_14 K1_14_2 Polynomial
abbrev OtherSeed := MvPolynomial (Fin 1) FX
abbrev Fixed := Polynomial (Polynomial OtherSeed)
def seedPerm (i : Fin 2) : Fin 2 ≃ Fin 2 := Equiv.swap i 0
theorem seedPerm_active (i : Fin 2) : seedPerm i i = 0 :=
  Equiv.swap_apply_left i 0
private def seedView (i : Fin 2) : Seeds ≃ₐ[FX] Polynomial OtherSeed :=
  (MvPolynomial.renameEquiv FX (seedPerm i)).trans (MvPolynomial.finSuccEquiv FX 1)
theorem seedView_degree (i : Fin 2) (f : Seeds) :
    (seedView i f).natDegree = f.degreeOf i := by
  change (MvPolynomial.finSuccEquiv FX 1 (MvPolynomial.rename (seedPerm i) f)).natDegree = _
  rw [MvPolynomial.natDegree_finSuccEquiv, ← seedPerm_active i]
  exact MvPolynomial.degreeOf_rename_of_injective (seedPerm i).injective i
private theorem seedView_C (i : Fin 2) (a : FX) :
    seedView i (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  change MvPolynomial.finSuccEquiv FX 1 (MvPolynomial.rename (seedPerm i) (MvPolynomial.C a)) = _
  rw [MvPolynomial.rename_C, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
  rfl
private theorem seedView_X (i j : Fin 2) :
    seedView i (MvPolynomial.X j) =
      if j = i then Polynomial.X else Polynomial.C (MvPolynomial.X 0) := by
  change MvPolynomial.finSuccEquiv FX 1 (MvPolynomial.rename (seedPerm i) (MvPolynomial.X j)) = _
  rw [MvPolynomial.rename_X]
  by_cases h : j = i
  · subst j
    rw [ite_eq_left rfl, seedPerm_active, MvPolynomial.finSuccEquiv_X_zero]
  · have hj : seedPerm i j ≠ 0 := by
      intro hz
      exact h ((seedPerm i).injective (hz.trans (seedPerm_active i).symm))
    have h1 : seedPerm i j = (0 : Fin 1).succ := by
      apply Fin.ext
      have hjv : (seedPerm i j).val ≠ 0 := fun hz => hj (Fin.ext hz)
      have hb := (seedPerm i j).isLt
      change (seedPerm i j).val = 1
      omega
    rw [ite_eq_right h, h1, MvPolynomial.finSuccEquiv_X_succ]
theorem seedView_translate (i : Fin 2) (f : Seeds) :
    (translateSeed i f).map (seedView i).toRingHom =
      taylor (Polynomial.X : Polynomial OtherSeed) ((seedView i f).map Polynomial.C) := by
  let lhs := (mapRingHom (seedView i).toRingHom).comp (translateSeed i)
  let rhs := (taylorAlgHom (Polynomial.X : Polynomial OtherSeed)).toRingHom.comp
    ((mapRingHom (Polynomial.C : OtherSeed →+* Polynomial OtherSeed)).comp
      (seedView i).toRingHom)
  suffices h : lhs = rhs from RingHom.congr_fun h f
  apply MvPolynomial.ringHom_ext
  · intro a
    change (translateSeed i (MvPolynomial.C a)).map (seedView i).toRingHom =
      taylor _ ((seedView i (MvPolynomial.C a)).map Polynomial.C)
    simp [translateSeed, seedView_C]
  · intro j
    change (translateSeed i (MvPolynomial.X j)).map (seedView i).toRingHom =
      taylor _ ((seedView i (MvPolynomial.X j)).map Polynomial.C)
    by_cases h : j = i
    · simp [translateSeed, seedView_X, h, add_comm]
    · simp [translateSeed, seedView_X, h]
theorem seedView_coeff_translate (i : Fin 2) (r : ℕ) (f : Seeds) :
    seedView i ((translateSeed i f).coeff r) = hasseDeriv r (seedView i f) := by
  calc
    _ = ((translateSeed i f).map (seedView i).toRingHom).coeff r := (coeff_map _ _).symm
    _ = _ := by rw [seedView_translate, taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]
private theorem swapped_coeff {A : Type*} [CommSemiring A]
    (F : Polynomial (Polynomial A)) (i j : ℕ) :
    ((Bivariate.swap F).coeff i).coeff j = (F.coeff j).coeff i := by
  induction F using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial m c =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]
def view (i : Fin 2) : Jet ≃+* Polynomial Fixed :=
  let inner := ((Polynomial.mapEquiv (seedView i).toRingEquiv).trans
    (Bivariate.swap (R := OtherSeed)).toRingEquiv)
  (Polynomial.mapEquiv inner).trans (Bivariate.swap (R := Polynomial OtherSeed)).toRingEquiv
theorem view_coeff (i : Fin 2) (F : Jet) (n j k : ℕ) :
    (((view i F).coeff n).coeff j).coeff k = (seedView i ((F.coeff j).coeff k)).coeff n := by
  let inner := ((Polynomial.mapEquiv (seedView i).toRingEquiv).trans
    (Bivariate.swap (R := OtherSeed)).toRingEquiv)
  change (((Bivariate.swap (F.map inner.toRingHom)).coeff n).coeff j).coeff k = _
  rw [swapped_coeff, coeff_map]
  change ((Bivariate.swap ((F.coeff j).map (seedView i).toRingHom)).coeff n).coeff k = _
  rw [swapped_coeff, coeff_map]
  rfl
theorem coeff_sum_monomial_map {A B : Type*} [Semiring A] [Semiring B]
    (F : Polynomial A) (f : A → B) (h0 : f 0 = 0) (n : ℕ) :
    (F.sum fun k c => monomial k (f c)).coeff n = f (F.coeff n) := by
  classical
  rw [coeff_sum, Polynomial.sum, Finset.sum_eq_single n]
  · simp
  · intro k _ hkn
    simp [coeff_monomial, hkn]
  · intro hn
    rw [notMem_support_iff.mp hn, h0, monomial_zero_right, coeff_zero]
private theorem seedHasse_coeff (i : Fin 2) (r : ℕ) (F : Jet) (j k : ℕ) :
    ((seedHasse i r F).coeff j).coeff k = (translateSeed i ((F.coeff j).coeff k)).coeff r := by
  unfold seedHasse
  rw [coeff_sum_monomial_map, coeff_sum_monomial_map]
  · simp
  · simp
theorem view_seedHasse (i : Fin 2) (r : ℕ) (F : Jet) :
    view i (seedHasse i r F) = hasseDeriv r (view i F) := by
  ext n j k : 3
  rw [view_coeff, seedHasse_coeff, seedView_coeff_translate, hasseDeriv_coeff]
  simp only [hasseDeriv_coeff, coeff_natCast_mul, view_coeff]
theorem view_degree_le (i : Fin 2) (F : Jet) (U : ℕ)
    (hbound : ∀ j k, ((F.coeff j).coeff k).totalDegree ≤ U) :
    (view i F).natDegree ≤ U := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext j k : 2
  rw [view_coeff]
  simp only [Polynomial.coeff_zero]
  apply coeff_eq_zero_of_natDegree_lt
  rw [seedView_degree]
  exact ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hbound j k)).trans_lt hn
theorem exists_view_degree_pos (F : Jet) (hf : UsesSeed F) :
    ∃ i : Fin 2, 0 < (view i F).natDegree := by
  obtain ⟨j, k, h⟩ := hf
  obtain ⟨d, hd, hp⟩ := Finset.lt_sup_iff.mp h
  obtain ⟨i, hi⟩ : ∃ i, 0 < d i := by
    by_contra! hzero
    have hz : d = 0 := Finsupp.ext fun i => Nat.eq_zero_of_le_zero (hzero i)
    simp [hz] at hp
  have hseed : 0 < (seedView i ((F.coeff j).coeff k)).natDegree := by
    rw [seedView_degree]
    exact hi.trans_le (MvPolynomial.monomial_le_degreeOf i hd)
  refine ⟨i, hseed.trans_le (le_natDegree_of_ne_zero ?_)⟩
  intro hz
  have hc := view_coeff i F (seedView i ((F.coeff j).coeff k)).natDegree j k
  rw [hz, Polynomial.coeff_zero, Polynomial.coeff_zero] at hc
  have hn : seedView i ((F.coeff j).coeff k) ≠ 0 := by
    intro hn
    simp [hn] at hseed
  exact (leadingCoeff_ne_zero.mpr hn) hc.symm
end
end K1_14_2_1_1
end
section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
namespace K1_14_2_1_1
noncomputable section
open K1 K1_14 Polynomial
private theorem dvd_pow_of_dvd_hasse {A : Type*} [CommRing A] {g f : Polynomial A}
    (hg : Prime g) (hd : ¬ g ∣ g.derivative) (e : ℕ)
    (hall : ∀ r < e, g ∣ hasseDeriv r f) : g ^ e ∣ f := by
  let I : Ideal (Polynomial A) := Ideal.span ({g} : Set (Polynomial A))
  let : I.IsPrime := (Ideal.span_singleton_prime hg.ne_zero).mpr hg
  let q := Ideal.Quotient.mk I
  have hq (s : Polynomial A) : q s = 0 ↔ g ∣ s :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  let shift : Polynomial A →+* Polynomial (Polynomial A ⧸ I) :=
    (taylorAlgHom (q Polynomial.X)).toRingHom.comp (mapRingHom (q.comp Polynomial.C))
  have hcoeff (s : Polynomial A) (r : ℕ) :
      (shift s).coeff r = q (hasseDeriv r s) := by
    change (taylor (q Polynomial.X) (s.map (q.comp Polynomial.C))).coeff r = _
    rw [taylor_coeff, hasseDeriv_map, eval_map, ← Polynomial.hom_eval₂, eval₂_C_X]
  have hzero (s : Polynomial A) : (shift s).coeff 0 = q s := by
    rw [hcoeff, hasseDeriv_zero']
  have hone : (shift g).coeff 1 ≠ 0 := by
    rw [hcoeff, hasseDeriv_one']
    exact mt (hq _).mp hd
  obtain ⟨T, hT⟩ : (Polynomial.X : Polynomial (Polynomial A ⧸ I)) ∣ shift g := by
    rw [Polynomial.X_dvd_iff, hzero]
    exact (hq g).mpr (dvd_refl g)
  have hT0 : T.coeff 0 ≠ 0 := by
    rw [hT, Polynomial.coeff_X_mul T 0] at hone
    exact hone
  have horder (a : ℕ) (s : Polynomial A) :
      (shift (g ^ a * s)).coeff a = T.coeff 0 ^ a * (shift s).coeff 0 := by
    rw [map_mul, map_pow, hT, mul_pow]
    have hprod : (Polynomial.X ^ a * T ^ a) * shift s =
        (T ^ a * shift s) * Polynomial.X ^ a := by ac_rfl
    rw [hprod]
    calc
      _ = (T ^ a * shift s).coeff 0 := by
        simpa only [Nat.zero_add] using Polynomial.coeff_mul_X_pow (T ^ a * shift s) a 0
      _ = _ := by
        change constantCoeff (T ^ a * shift s) = constantCoeff T ^ a * constantCoeff (shift s)
        rw [map_mul, map_pow]
  induction e with
  | zero => simp
  | succ a ih =>
    obtain ⟨s, hs⟩ := ih (fun r hr => hall r (Nat.lt_succ_of_lt hr))
    have hz := (hq _).mpr (hall a (Nat.lt_succ_self a))
    rw [hs, ← hcoeff, horder, hzero] at hz
    have hdiv := (hq s).mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hT0))
    obtain ⟨t, ht⟩ := hdiv
    exact ⟨t, by rw [hs, ht, pow_succ, mul_assoc]⟩
private theorem derivative_not_dvd {A : Type*} [CommRing A] [IsDomain A] {q : ℕ} [CharP A q]
    (g : Polynomial A) (hpos : 0 < g.natDegree) (hsmall : g.natDegree < q) :
    ¬ g ∣ g.derivative := by
  have hc : (g.natDegree : A) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hsmall) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff A q _).mp hz))
  have hlead : g.leadingCoeff ≠ 0 := by
    apply leadingCoeff_ne_zero.mpr
    intro hz
    simp [hz] at hpos
  have hcoeff : g.derivative.coeff (g.natDegree - 1) ≠ 0 := by
    rw [coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    exact mul_ne_zero hlead hc
  have hn : g.derivative ≠ 0 := by
    intro hz
    exact hcoeff (by simp [hz])
  intro hdiv
  exact (not_le_of_gt (natDegree_derivative_lt hpos.ne')) (natDegree_le_of_dvd hdiv hn)
theorem proof : K1_14_2_1.c1 := by
  intro G P R U e hG _ hmove hP hGP hsmall hcaps hhasse
  obtain ⟨i, hpos⟩ := exists_view_degree_pos G hmove
  have hbound : (view i G).natDegree < p :=
    ((natDegree_le_of_dvd ((map_dvd_iff (view i)).mpr hGP)
      ((view i).map_ne_zero_iff.mpr hP)).trans (view_degree_le i P U hcaps)).trans_lt hsmall
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  let : CharP OtherSeed p := charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 1) FX) p
  have hirr : Irreducible (view i G) := (MulEquiv.irreducible_iff (view i)).mpr hG
  have hprime : Prime (view i G) := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  apply (map_dvd_iff (view i)).mp
  rw [map_pow]
  apply dvd_pow_of_dvd_hasse hprime (derivative_not_dvd _ hpos hbound)
  intro r hr
  rw [← view_seedHasse]
  exact (map_dvd_iff (view i)).mpr (hhasse i r hr)
end
end K1_14_2_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 12
namespace K1_13_5_4_2_4_2_1
noncomputable section
open K1_13_5_4 (GeometricX)
open K1_13_5_4_2_4 MvPolynomial Algebra
open scoped nonZeroDivisors
variable {A : Fin 4 → Finset Exponent}
private abbrev CoeffIndex (A : Fin 4 → Finset Exponent) := Σ i : Fin 4, ↥(A i)
abbrev FreeCoeff (A : Fin 4 → Finset Exponent) :=
  {v : CoeffIndex A // v.2.val ≠ 0}
private abbrev Incidence (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (FreeCoeff A ⊕ Fin 4) GeometricX
private def pivot (hz : ∀ i, 0 ∈ A i) (i : Fin 4) : ↥(A i) := ⟨0, hz i⟩
def otherTerm (i : Fin 4) (a : ↥(A i)) : Incidence A :=
  if h : a.val = 0 then 0 else
    MvPolynomial.X (Sum.inl ⟨⟨i, a⟩, h⟩) *
      a.val.prod (fun j n => MvPolynomial.X (Sum.inr j) ^ n)
def otherTerms (A : Fin 4 → Finset Exponent) (i : Fin 4) : Incidence A :=
  ∑ a : ↥(A i), otherTerm i a
private def parameterMap (A : Fin 4 → Finset Exponent) :
    CoefficientRing A →ₐ[GeometricX] Incidence A :=
  aeval fun v => if h : v.2.val = 0 then -otherTerms A v.1 else MvPolynomial.X (Sum.inl ⟨v, h⟩)
def quotientMk (A : Fin 4 → Finset Exponent) :
    MvPolynomial (Fin 4) (CoefficientField A) →+* GenericQuotient A :=
  Ideal.Quotient.mk _
theorem quotientMk_C (r : CoefficientField A) :
    quotientMk A (C r) = algebraMap (CoefficientField A) (GenericQuotient A) r := by
  rw [← MvPolynomial.algebraMap_eq, quotientMk, Ideal.Quotient.mk_algebraMap]
def quotientCoefficients (A : Fin 4 → Finset Exponent) :
    CoefficientRing A →+* GenericQuotient A :=
  (algebraMap (CoefficientField A) (GenericQuotient A)).comp
    (algebraMap (CoefficientRing A) (CoefficientField A))
private def projection (A : Fin 4 → Finset Exponent) : Incidence A →+* GenericQuotient A :=
  eval₂Hom ((quotientCoefficients A).comp (algebraMap GeometricX (CoefficientRing A)))
    (Sum.elim (fun v => quotientCoefficients A (MvPolynomial.X v.val))
      (fun j => quotientMk A (MvPolynomial.X j)))
theorem projection_inr (i : Fin 4) :
    projection A (MvPolynomial.X (Sum.inr i)) = quotientMk A (MvPolynomial.X i) :=
  eval₂Hom_X' _ _ _
theorem projection_term (i : Fin 4) (a : ↥(A i)) (ha : a.val ≠ 0) :
    projection A (otherTerm i a) =
      quotientMk A (monomial a.val
        (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩))) := by
  simp only [otherTerm, dite_eq_right ha, map_mul, map_finsuppProd, map_pow, projection_inr,
    monomial_eq]
  rw [show projection A (MvPolynomial.X (Sum.inl ⟨⟨i, a⟩, ha⟩)) =
    quotientCoefficients A (MvPolynomial.X ⟨i, a⟩) from eval₂Hom_X' _ _ _]
  rfl
theorem projection_terms (hz : ∀ i, 0 ∈ A i) (i : Fin 4) :
    projection A (otherTerms A i) + quotientCoefficients A (MvPolynomial.X ⟨i, pivot hz i⟩) = 0 := by
  classical
  let p := pivot hz i
  have hzero : projection A (otherTerm i p) = 0 := by simp [p, pivot, otherTerm]
  have hterms : projection A (otherTerms A i) =
      ∑ a ∈ Finset.univ.erase p, quotientMk A (monomial a.val
        (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩))) := by
    rw [otherTerms, map_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ p), hzero, add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    exact projection_term i a (fun he => (Finset.mem_erase.mp ha).1 (Subtype.ext he))
  have hrelation : quotientMk A (genericEquation A i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [genericEquation, map_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ p),
    ← hterms] at hrelation
  simpa only [p, pivot, monomial_zero', quotientMk_C, quotientCoefficients,
    RingHom.comp_apply] using hrelation
theorem parameter_square (hz : ∀ i, 0 ∈ A i) :
    (projection A).comp (parameterMap A).toRingHom = quotientCoefficients A := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change projection A (parameterMap A (C r)) = quotientCoefficients A (C r)
    rw [show parameterMap A (C r) = C r from (parameterMap A).commutes r]
    exact eval₂Hom_C _ _ _
  · rintro ⟨i, a⟩
    change projection A (parameterMap A (MvPolynomial.X ⟨i, a⟩)) =
      quotientCoefficients A (MvPolynomial.X ⟨i, a⟩)
    rw [parameterMap, aeval_X]
    by_cases ha : a.val = 0
    · have he : a = pivot hz i := Subtype.ext ha
      subst a
      rw [dite_eq_left (show (pivot hz i).val = 0 from rfl), map_neg]
      exact neg_eq_iff_add_eq_zero.mpr (projection_terms hz i)
    · rw [dite_eq_right ha]
      exact eval₂Hom_X' _ _ _
def incidenceIndexEquiv (hz : ∀ i, 0 ∈ A i) : FreeCoeff A ⊕ Fin 4 ≃ CoeffIndex A := by
  classical
  let constants : Fin 4 ≃ {v : CoeffIndex A // ¬ v.2.val ≠ 0} :=
    { toFun := fun i => ⟨⟨i, pivot hz i⟩, by simp [pivot]⟩
      invFun := fun v => v.val.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨i, a⟩, ha⟩
        have he : a = pivot hz i := Subtype.ext (not_ne_iff.mp ha)
        subst a
        rfl }
  exact (Equiv.sumCongr (Equiv.refl _) constants).trans (Equiv.sumCompl _)
private theorem incidence_trdeg (hz : ∀ i, 0 ∈ A i) :
    trdeg GeometricX (Incidence A) = trdeg GeometricX (CoefficientRing A) := by
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] using
    Cardinal.mk_congr (incidenceIndexEquiv hz)
theorem coefficient_trdeg_finite (A : Fin 4 → Finset Exponent) :
    trdeg GeometricX (CoefficientField A) < Cardinal.aleph0 := by
  let : Algebra.IsAlgebraic (CoefficientRing A) (CoefficientField A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (CoefficientRing A))
  rw [← trdeg_add_eq GeometricX (CoefficientRing A), trdeg_eq_zero (R := CoefficientRing A), add_zero,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id]
  exact Cardinal.mk_lt_aleph0
theorem projection_surjective {D : Type} [CommRing D]
    (g : D →+* GenericQuotient A) (u : CoefficientField A →+* D)
    (hgu : g.comp u = algebraMap (CoefficientField A) (GenericQuotient A))
    (coord : Fin 4 → D) (hcoord : ∀ i, g (coord i) = quotientMk A (MvPolynomial.X i)) :
    Function.Surjective g := by
  let eval : MvPolynomial (Fin 4) (CoefficientField A) →+* D := eval₂Hom u coord
  have he : g.comp eval = quotientMk A := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, eval, eval₂Hom_C]
      exact (RingHom.congr_fun hgu r).trans (quotientMk_C r).symm
    · intro i
      simp only [RingHom.comp_apply, eval, eval₂Hom_X']
      exact hcoord i
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨eval p, RingHom.congr_fun he p⟩
theorem finiteOfIncidence {k R B F Q : Type}
    [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [CommRing B] [IsDomain B] [Algebra k B]
    [Field F] [Algebra R F] [IsFractionRing R F] [Algebra k F] [IsScalarTower k R F]
    [CommRing Q] [Nontrivial Q] [Algebra F Q] [Algebra.FiniteType F Q]
    (j : R →ₐ[k] B) (p : B →+* Q)
    (hpj : p.comp j.toRingHom = (algebraMap F Q).comp (algebraMap R F))
    (hdeg : trdeg k B = trdeg k R) (hfinite : trdeg k F < Cardinal.aleph0)
    (surjective : ∀ (D : Type) [CommRing D] (u : F →+* D) (g : D →+* Q) (w : B →+* D),
      g.comp u = algebraMap F Q → g.comp w = p → Function.Surjective g) :
    Module.Finite F Q := by
  have hinj : Function.Injective (p.comp j.toRingHom) := by
    rw [hpj]
    exact (algebraMap F Q).injective.comp (IsFractionRing.injective R F)
  have hj : Function.Injective j := fun _ _ h => hinj (congrArg p h)
  let M := (nonZeroDivisors R).map j.toRingHom.toMonoidHom
  have hM : M ≤ nonZeroDivisors B :=
    map_le_nonZeroDivisors_of_injective j.toRingHom hj le_rfl
  let D := Localization M
  let : IsDomain D := IsLocalization.isDomain_localization hM
  let : FaithfulSMul B D :=
    (faithfulSMul_iff_algebraMap_injective B D).mpr (IsLocalization.injective D hM)
  let u : F →+* D :=
    IsLocalization.lift (M := nonZeroDivisors R) (g := (algebraMap B D).comp j.toRingHom)
      (fun x => IsLocalization.map_units D (⟨j x, ⟨x, x.2, rfl⟩⟩ : M))
  let : Algebra F D := u.toAlgebra
  let : IsScalarTower k F D := IsScalarTower.of_algebraMap_eq (by
    intro r
    rw [IsScalarTower.algebraMap_apply k B D, IsScalarTower.algebraMap_apply k R F]
    change algebraMap B D (algebraMap k B r) = u (algebraMap R F (algebraMap k R r))
    simp only [u, IsLocalization.lift_eq, RingHom.comp_apply]
    exact congrArg (algebraMap B D) (j.commutes r).symm)
  have hd : trdeg k D = trdeg k F := by
    let : Algebra.IsAlgebraic B D := IsLocalization.isAlgebraic D M
    let : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
    calc
      trdeg k D = trdeg k B := by
        rw [← trdeg_add_eq k B (A := D), trdeg_eq_zero (R := B), add_zero]
      _ = trdeg k R := hdeg
      _ = trdeg k F := by
        rw [← trdeg_add_eq k R (A := F), trdeg_eq_zero (R := R), add_zero]
  let : FaithfulSMul F D :=
    (faithfulSMul_iff_algebraMap_injective F D).mpr u.injective
  have hzero : trdeg F D = 0 := by
    have hle : trdeg F D ≤ 0 := by
      apply (Cardinal.add_le_add_iff_of_lt_aleph0 hfinite).mp
      calc
        trdeg F D + trdeg k F = trdeg k D :=
          (add_comm _ _).trans (trdeg_add_eq k F (A := D))
        _ ≤ 0 + trdeg k F := by rw [hd, zero_add]
    exact le_antisymm hle bot_le
  let : Algebra.IsIntegral F D :=
    Algebra.isAlgebraic_iff_isIntegral.mp (trdeg_eq_zero_iff.mp hzero)
  have hunits : ∀ x : M, IsUnit (p x) := by
    rintro ⟨_, x, hx, rfl⟩
    change IsUnit ((p.comp j.toRingHom) x)
    rw [hpj, RingHom.comp_apply]
    have hx' : algebraMap R F x ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R F).ne
        (mem_nonZeroDivisors_iff_ne_zero.mp hx)
    exact (isUnit_iff_ne_zero.mpr hx').map (algebraMap F Q)
  let g : D →+* Q := IsLocalization.lift hunits
  have hgu : g.comp u = algebraMap F Q := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, g, u, IsLocalization.lift_eq]
    exact RingHom.congr_fun hpj x
  let e : D →ₐ[F] Q := ⟨g, RingHom.congr_fun hgu⟩
  have hg := surjective D u g (algebraMap B D) hgu (IsLocalization.lift_comp hunits)
  let : Algebra.IsIntegral F Q := ⟨fun q => by
    obtain ⟨d, rfl⟩ := hg q
    exact (Algebra.IsIntegral.isIntegral d).map e⟩
  exact Algebra.IsIntegral.finite
theorem finiteNontrivial (hz : ∀ i, 0 ∈ A i) [Nontrivial (GenericQuotient A)] :
    Module.Finite (CoefficientField A) (GenericQuotient A) := by
  apply finiteOfIncidence (parameterMap A) (projection A) (parameter_square hz)
    (incidence_trdeg hz) (coefficient_trdeg_finite A)
  intro D _ u g w hgu hgw
  refine projection_surjective g u hgu (fun i => w (MvPolynomial.X (Sum.inr i))) ?_
  intro i
  exact (RingHom.congr_fun hgw _).trans (projection_inr i)
theorem proof : K1_13_5_4_2_4_2.c1 := by
  intro A hz
  rcases subsingleton_or_nontrivial (GenericQuotient A) with hQ | hQ
  · let := hQ
    exact Module.Finite.of_surjective (Algebra.linearMap (CoefficientField A) (GenericQuotient A))
      (fun q => ⟨0, Subsingleton.elim _ q⟩)
  · let := hQ
    exact finiteNontrivial hz
end
end K1_13_5_4_2_4_2_1
end
section
namespace K1_13_5_1
noncomputable section
open K1_13 K1_13_5 MvPolynomial
open scoped Polynomial BigOperators
def view {r : ℕ} : Row (r + 1) ≃ₐ[Geom[X]] Polynomial (Row r) :=
  (renameEquiv Geom[X] finSuccEquivLast).trans (optionEquivLeft Geom[X] (Fin r))
theorem view_degree {r : ℕ} (f : Row (r + 1)) :
    (view f).natDegree = f.degreeOf (Fin.last r) := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast f)).natDegree = _
  rw [natDegree_optionEquivLeft]
  simpa only [finSuccEquivLast_last] using
    degreeOf_rename_of_injective (p := f) finSuccEquivLast.injective (Fin.last r)
theorem view_derivative {r : ℕ} (f : Row (r + 1)) :
    view (pderiv (Fin.last r) f) = (view f).derivative := by
  change optionEquivLeft _ _ (rename finSuccEquivLast (pderiv (Fin.last r) f)) = _
  rw [← pderiv_rename finSuccEquivLast.injective, finSuccEquivLast_last,
    optionEquivLeft_pderiv_none]
  rfl
theorem view_eval {r : ℕ} (f : Row (r + 1)) (S : Geom[X]) :
    atJet f S = ((view f).map (eval (jet S))).eval (jet S (Fin.last r)) := by
  rw [atJet, view, AlgEquiv.trans_apply, renameEquiv_apply, ← optionEquivLeft_elim_eval,
    eval_rename]
  apply congrArg (fun v => eval v f)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [finSuccEquivLast_last]
  · simp [jet]
theorem view_coeff_weight {r : ℕ} (w : Fin (r + 1) → ℕ)
    (f : Row (r + 1)) (k : ℕ)
    (hk : k ≤ (view f).natDegree) :
    ((view f).coeff k).weightedTotalDegree (fun i => w i.castSucc) +
      w (Fin.last r) * k ≤ f.weightedTotalDegree w := by
  classical
  let w' : Option (Fin r) → ℕ := fun i => i.elim (w (Fin.last r)) (fun j => w j.castSucc)
  have hw : ∀ i : Fin (r + 1), w' (finSuccEquivLast i) = w i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [w', finSuccEquivLast_last]
  have hrename : (rename finSuccEquivLast f).weightedTotalDegree w' =
      f.weightedTotalDegree w := by
    rw [weightedTotalDegree, weightedTotalDegree, support_rename_of_injective
      finSuccEquivLast.injective, Finset.sup_image]
    congr 1
    funext u
    simp only [Function.comp_apply, Finsupp.weight_apply, smul_eq_mul]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  have hterm (k : ℕ) (m : Fin r →₀ ℕ) (hm : m ∈ ((view f).coeff k).support) :
      m.weight (fun i => w i.castSucc) + w (Fin.last r) * k ≤ f.weightedTotalDegree w := by
    have hs := (mem_support_coeff_optionEquivLeft _).mp hm
    have hle := le_weightedTotalDegree w' hs
    change _ ≤ (rename finSuccEquivLast f).weightedTotalDegree w' at hle
    rw [hrename, Finsupp.weight_optionElim] at hle
    simpa only [w', Nat.add_comm, Nat.mul_comm] using hle
  have hcoeff (j : ℕ) (hj : (view f).coeff j ≠ 0) :
      ((view f).coeff j).weightedTotalDegree (fun i => w i.castSucc) +
        w (Fin.last r) * j ≤ f.weightedTotalDegree w := by
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup
      _ (support_nonempty.mpr hj) (fun m => m.weight (fun i : Fin r => w i.castSucc))
    rw [weightedTotalDegree, hmax]
    exact hterm j m hm
  by_cases hzero : (view f).coeff k = 0
  · rw [hzero, weightedTotalDegree_zero, bot_eq_zero, zero_add]
    by_cases hf : view f = 0
    · simp_all
    have h := hcoeff _ (Polynomial.leadingCoeff_ne_zero.mpr hf)
    exact (Nat.mul_le_mul_left _ hk).trans ((Nat.le_add_left _ _).trans h)
  · exact hcoeff k hzero
def elimination {r : ℕ} (f : Row (r + 1)) : Row r :=
  let F := view f
  let c := F.natDegree
  if c = 0 then F.coeff 0 else F.resultant F.derivative c (c - 1)
theorem elimination_eval {r : ℕ} (f : Row (r + 1)) (S : Geom[X])
    (hf : atJet f S = 0) :
    atJet (elimination f) S = 0 ∨
      (0 < (view f).natDegree ∧ RegularAt (Fin.last r) f S) := by
  by_cases hdeg : (view f).natDegree = 0
  · left
    rw [view_eval, Polynomial.eq_C_of_natDegree_eq_zero hdeg, Polynomial.map_C,
      Polynomial.eval_C] at hf
    simpa [elimination, hdeg, atJet] using hf
  · by_cases hder : atJet (pderiv (Fin.last r) f) S = 0
    · left
      rw [view_eval, view_derivative] at hder
      rw [view_eval] at hf
      simpa only [elimination, ite_eq_right hdeg, atJet] using
        Polynomial.map_resultant_eq_zero_of_common_root (eval (jet S))
          (view f) (view f).derivative le_rfl (Polynomial.natDegree_derivative_le _)
          (Or.inl hdeg) (jet S (Fin.last r)) hf hder
    · exact Or.inr ⟨Nat.pos_of_ne_zero hdeg, hf, hder⟩
theorem elimination_ne_zero {r : ℕ} {f : Row (r + 1)} (hf : Irreducible f)
    (hc : (view f).natDegree < K1.p) : elimination f ≠ 0 := by
  let F := view f
  let c := F.natDegree
  have hi : Irreducible F := (MulEquiv.irreducible_iff view.toMulEquiv).mpr hf
  change (if c = 0 then F.coeff 0 else F.resultant F.derivative c (c - 1)) ≠ 0
  by_cases h : c = 0
  · have hnz := Polynomial.leadingCoeff_ne_zero.mpr hi.ne_zero
    change F.coeff c ≠ 0 at hnz
    rw [h] at hnz
    simpa only [ite_eq_left h] using hnz
  · have : CharP Geom K1.p :=
      charP_of_injective_ringHom (RingHom.injective embed) K1.p
    have hcast : (c : Geom) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hc) (Nat.le_of_dvd (Nat.pos_of_ne_zero h)
        ((CharP.cast_eq_zero_iff Geom K1.p c).mp hz))
    have hc' : (c : Row r) ≠ 0 := by
      let ι : Geom →+* Row r := MvPolynomial.C.comp Polynomial.C
      have hinj : Function.Injective ι :=
        (MvPolynomial.C_injective _ _).comp Polynomial.C_injective
      simpa only [map_natCast, map_zero] using (hinj.ne hcast :
        ι (c : Geom) ≠ ι 0)
    have hder : F.derivative ≠ 0 := by
      intro hz
      have hindex : c - 1 + 1 = c := by omega
      have hz' := congrArg (fun p : Polynomial (Row r) => p.coeff (c - 1)) hz
      rw [Polynomial.coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one, hindex,
        Polynomial.coeff_zero] at hz'
      exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hi.ne_zero) hc') hz'
    simpa only [ite_eq_right h] using
      Polynomial.resultant_derivative_ne_zero_of_irreducible F hi hder
end
end K1_13_5_1
end
section
namespace K1_13_5_1
noncomputable section
open K1_13 MvPolynomial
open scoped Polynomial BigOperators
private theorem resultant_weight {r : ℕ} (w : Fin r → ℕ) (a : ℕ)
    (P Q : Polynomial (Row r)) (m n B D : ℕ)
    (hP : ∀ i ≤ m, (P.coeff i).weightedTotalDegree w + a * i ≤ B)
    (hQ : ∀ i ≤ n, (Q.coeff i).weightedTotalDegree w + a * i ≤ D) :
    (P.resultant Q m n).weightedTotalDegree w + a * (m * n) ≤ n * B + m * D := by
  classical
  let M := Polynomial.sylvester P Q m n
  let W : Fin (m + n) → ℕ :=
    Fin.addCases (fun j : Fin m => D + a * j.val) (fun j : Fin n => B + a * j.val)
  have hentry (σ : Equiv.Perm (Fin (m + n))) (i : Fin (m + n))
      (hne : M (σ i) i ≠ 0) :
      (M (σ i) i).weightedTotalDegree w + a * (σ i).val ≤ W i := by
    cases i using Fin.addCases with
    | left j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hj : j.val ≤ (σ (j.castAdd n)).val := h.1
        have hh := hQ ((σ (j.castAdd n)).val - j.val) (by have := h.2; omega)
        simp only [W, Fin.addCases_left]
        have hid : a * ((σ (j.castAdd n)).val - j.val) + a * j.val =
            a * (σ (j.castAdd n)).val := by rw [← Nat.mul_add, Nat.sub_add_cancel hj]
        omega
      · exact absurd rfl hne
    | right j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hj : j.val ≤ (σ (j.natAdd m)).val := h.1
        have hh := hP ((σ (j.natAdd m)).val - j.val) (by have := h.2; omega)
        simp only [W, Fin.addCases_right]
        have hid : a * ((σ (j.natAdd m)).val - j.val) + a * j.val =
            a * (σ (j.natAdd m)).val := by rw [← Nat.mul_add, Nat.sub_add_cancel hj]
        omega
      · exact absurd rfl hne
  let S := (∑ j : Fin m, a * j.val) + ∑ j : Fin n, a * j.val
  have hW : ∑ i, W i = m * D + n * B + S := by
    simp only [W, S, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hsum : ∑ i : Fin (m + n), a * i.val = a * (m * n) + S := by
    simp only [S, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, Nat.mul_add,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hbase : a * (m * n) ≤ n * B := by
    rw [show a * (m * n) = n * (a * m) by ring]
    exact Nat.mul_le_mul_left n ((Nat.le_add_left _ _).trans (hP m le_rfl))
  have hterm (σ : Equiv.Perm (Fin (m + n))) :
      (∏ i, M (σ i) i).weightedTotalDegree w ≤ n * B + m * D - a * (m * n) := by
    by_cases hz : ∃ i, M (σ i) i = 0
    · obtain ⟨i, hi⟩ := hz
      have hp : (∏ j, M (σ j) j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hp, weightedTotalDegree_zero]
      exact Nat.zero_le _
    · simp only [not_exists] at hz
      rw [weightedTotalDegree_prod _ _ _ (fun i _ => hz i)]
      have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hentry σ i (hz i))
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i => a * i.val), hW, hsum] at h
      omega
  have hdet : M.det.weightedTotalDegree w ≤ n * B + m * D - a * (m * n) := by
    rw [Matrix.det_apply]
    refine AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]
      exact hterm σ
    · have hsign : Equiv.Perm.sign σ • (∏ i, M (σ i) i) = -(∏ i, M (σ i) i) := by
        simp [hs]
      rw [hsign, AddMonoidAlgebra.supDegree_neg]
      exact hterm σ
  change M.det.weightedTotalDegree w + a * (m * n) ≤ _
  omega
theorem coeff_derivative_weight {r : ℕ} (w : Fin r → ℕ) (P : Polynomial (Row r))
    (i : ℕ) :
    (P.derivative.coeff i).weightedTotalDegree w ≤ (P.coeff (i + 1)).weightedTotalDegree w := by
  rw [Polynomial.coeff_derivative, ← Nat.cast_succ, ← map_natCast (MvPolynomial.C : Geom[X] →+* Row r)]
  exact (weightedTotalDegree_mul_le _ _ _).trans (by rw [weightedTotalDegree_C, Nat.add_zero])
theorem elimination_weight_positive {r : ℕ} (w : Fin (r + 1) → ℕ)
    (f : Row (r + 1)) (hc : 0 < (view f).natDegree) :
    let c := (view f).natDegree
    (elimination f).weightedTotalDegree (fun i => w i.castSucc) +
      w (Fin.last r) * c ^ 2 ≤ (2 * c - 1) * f.weightedTotalDegree w := by
  let A := view f
  let a := w (Fin.last r)
  let v : Fin r → ℕ := fun i => w i.castSucc
  let B := f.weightedTotalDegree w
  change 0 < A.natDegree at hc
  obtain ⟨k, hk⟩ : ∃ k, A.natDegree = k + 1 :=
    ⟨A.natDegree - 1, by omega⟩
  have hA : ∀ i ≤ k + 1, (A.coeff i).weightedTotalDegree v + a * i ≤ B :=
    fun i hi => view_coeff_weight w f i (by rwa [hk])
  have hab : a ≤ B := by
    have htop := hA (k + 1) le_rfl
    rw [Nat.mul_add, Nat.mul_one] at htop
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  have hD : ∀ i ≤ k, (A.derivative.coeff i).weightedTotalDegree v + a * i ≤ d := by
    intro i hi
    have h := hA (i + 1) (by omega)
    rw [Nat.mul_add, Nat.mul_one, hd] at h
    have h' := coeff_derivative_weight v A i
    omega
  have h := resultant_weight v a A A.derivative (k + 1) k B d hA hD
  have hEq : elimination f = A.resultant A.derivative (k + 1) k := by
    change (if A.natDegree = 0 then A.coeff 0
      else A.resultant A.derivative A.natDegree (A.natDegree - 1)) = _
    simp [hk]
  have hR : (2 * (k + 1) - 1) * B = k * B + (k + 1) * d + (k + 1) * a := by
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, hd]
    ring
  have hL : a * (k + 1) ^ 2 = a * ((k + 1) * k) + (k + 1) * a := by ring
  change (elimination f).weightedTotalDegree v + a * A.natDegree ^ 2 ≤ (2 * A.natDegree - 1) * B
  rw [hk, hEq, hL, hR]
  omega
theorem elimination_weight_zero {r : ℕ} (w : Fin (r + 1) → ℕ)
    (f : Row (r + 1)) (hc : (view f).natDegree = 0) :
    (elimination f).weightedTotalDegree (fun i => w i.castSucc) ≤ f.weightedTotalDegree w := by
  simpa [elimination, hc] using view_coeff_weight w f 0 (Nat.zero_le _)
end
end K1_13_5_1
end
section
namespace K1_13_5_1
noncomputable section
open scoped BigOperators
private theorem increase_budget {a b c C t d : ℕ} (hc : 0 < c) (hC : c ≤ C)
    (ht : a * t ≤ 2 * b) (hd : d + a * c ^ 2 ≤ (2 * c - 1) * b) :
    d + a * c ^ 2 + a * ((C - c) * t) ≤ (2 * C - 1) * b := by
  have hincr := Nat.mul_le_mul_left (C - c) ht
  have he : 2 * C - 1 = (2 * c - 1) + 2 * (C - c) := by omega
  rw [he, Nat.add_mul]
  rw [show a * ((C - c) * t) = (C - c) * (a * t) by ring,
    show 2 * (C - c) * b = (C - c) * (2 * b) by ring]
  exact Nat.add_le_add hd hincr
theorem aggregate {ι : Type*} (T : Finset ι) (b c d : ι → ℕ) (B a : ℕ)
    (hb : ∑ i ∈ T, b i ≤ B) (hc : ∑ i ∈ T, c i ≤ 24) (hB : a * 24 ≤ B)
    (hbase : ∀ i ∈ T, a * c i ≤ b i)
    (hzero : ∀ i ∈ T, c i = 0 → d i ≤ b i)
    (hpos : ∀ i ∈ T, 0 < c i → d i + a * (c i)^2 ≤ (2 * c i - 1) * b i) :
    ∑ i ∈ T, d i ≤ 47 * B - a * 24^2 := by
  let C := ∑ i ∈ T, c i
  have hci (i : ι) (hi : i ∈ T) : c i ≤ C := Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) hi
  by_cases hC : C = 0
  · have h := (Finset.sum_le_sum fun i hi => hzero i hi (by have := hci i hi; omega)).trans hb
    omega
  have hCpos := Nat.pos_of_ne_zero hC
  have hterm (i : ι) (hi : i ∈ T) : d i + a * (C * c i) ≤ (2 * C - 1) * b i := by
    by_cases hi₀ : c i = 0
    · rw [hi₀, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      exact (hzero i hi hi₀).trans (by
        simpa using Nat.mul_le_mul_right (b i) (show 1 ≤ 2 * C - 1 by omega))
    · have h := increase_budget (Nat.pos_of_ne_zero hi₀) (hci i hi)
        ((hbase i hi).trans (by omega : b i ≤ 2 * b i)) (hpos i hi (Nat.pos_of_ne_zero hi₀))
      have he : C = c i + (C - c i) := by have := hci i hi; omega
      have hweight : a * (C * c i) = a * (c i)^2 + a * ((C - c i) * c i) := by
        calc
          _ = a * ((c i + (C - c i)) * c i) := congrArg (fun n => a * (n * c i)) he
          _ = _ := by ring
      rw [hweight, ← Nat.add_assoc]
      exact h
  have hs : (∑ i ∈ T, (d i + a * (C * c i))) ≤ (2 * C - 1) * B :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ hb)
  have hjoint : (∑ i ∈ T, d i) + a * C ^ 2 ≤ (2 * C - 1) * B := by
    simp only [Finset.sum_add_distrib, ← Nat.mul_assoc, ← Finset.mul_sum] at hs
    change (∑ i ∈ T, d i) + (a * C) * C ≤ _ at hs
    rwa [Nat.mul_assoc, ← pow_two] at hs
  have ha : a * (24 + C) ≤ 2 * B := by
    calc
      _ ≤ a * (24 + 24) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hc 24)
      _ = 2 * (a * 24) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hB
  have hfinal := increase_budget hCpos hc ha hjoint
  have he : 24 = C + (24 - C) := by omega
  have hsq : a * C ^ 2 + a * ((24 - C) * (24 + C)) = a * 24 ^ 2 := by
    calc
      _ = a * C ^ 2 + a * ((24 - C) * ((C + (24 - C)) + C)) := by
        exact congrArg (fun n => a * C ^ 2 + a * ((24 - C) * (n + C))) he
      _ = a * (C + (24 - C)) ^ 2 := by ring
      _ = _ := by rw [← he]
  exact Nat.le_sub_of_add_le (by simpa only [Nat.add_assoc, hsq] using hfinal)
end
end K1_13_5_1
end
section
namespace K1_13_5_4_1_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_1
open K1_13_6 (coefficientDerivative partialFlow)
open MvPolynomial
open scoped Polynomial
theorem coefficientDerivative_coeff (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = Polynomial.derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
theorem row_coeff_add (P Q : Row 4) (m : Fin 4 →₀ ℕ) :
    (P + Q).coeff m = P.coeff m + Q.coeff m :=
  map_add (MvPolynomial.coeffAddMonoidHom m) P Q
private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P + Q) = coefficientDerivative P + coefficientDerivative Q := by
  apply MvPolynomial.ext
  intro m
  simp only [coefficientDerivative_coeff, row_coeff_add, Polynomial.derivative_add]
private theorem coefficientDerivative_mul (P Q : Row 4) :
    coefficientDerivative (P * Q) = P * coefficientDerivative Q + coefficientDerivative P * Q := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [coefficientDerivative_coeff, row_coeff_add, MvPolynomial.coeff_mul,
    Polynomial.derivative_sum, Polynomial.derivative_mul, Finset.sum_add_distrib]
  exact add_comm _ _
private theorem partialFlow_add (P Q : Row 4) :
    partialFlow (P + Q) = partialFlow P + partialFlow Q := by
  simp only [partialFlow, coefficientDerivative_add, map_add, mul_add, Finset.sum_add_distrib]
  ring
private theorem partialFlow_mul (P Q : Row 4) :
    partialFlow (P * Q) = P * partialFlow Q + partialFlow P * Q := by
  let weight (i : Fin 3) : Row 4 :=
    MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) * MvPolynomial.X i.succ
  have hsum :
      (∑ i : Fin 3, weight i * pderiv i.castSucc (P * Q)) =
        P * (∑ i : Fin 3, weight i * pderiv i.castSucc Q) +
        (∑ i : Fin 3, weight i * pderiv i.castSucc P) * Q := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pderiv_mul]
    ring
  change coefficientDerivative (P * Q) + (∑ i : Fin 3, weight i * pderiv i.castSucc (P * Q)) =
    P * (coefficientDerivative Q + (∑ i : Fin 3, weight i * pderiv i.castSucc Q)) +
      (coefficientDerivative P + (∑ i : Fin 3, weight i * pderiv i.castSucc P)) * Q
  rw [coefficientDerivative_mul, hsum]
  ring
def scaledFlow (f : Row 3) : Row 4 →+ Row 4 where
  toFun b := liftSep f * partialFlow b + thirdVelocityNumerator f * pderiv 3 b
  map_zero' := by simp [partialFlow, coefficientDerivative]
  map_add' P Q := by rw [partialFlow_add, map_add]; ring
theorem scaledFlow_apply (f : Row 3) (b : Row 4) :
    scaledFlow f b = liftSep f * partialFlow b + thirdVelocityNumerator f * pderiv 3 b := rfl
theorem scaledFlow_mul (f : Row 3) (P Q : Row 4) :
    scaledFlow f (P * Q) = P * scaledFlow f Q + scaledFlow f P * Q := by
  simp only [scaledFlow_apply, partialFlow_mul, pderiv_mul]
  ring
theorem scaledFlow_one (f : Row 3) : scaledFlow f 1 = 0 := by
  have h := scaledFlow_mul f 1 1
  simp only [one_mul, mul_one] at h
  exact add_left_cancel (show scaledFlow f 1 + scaledFlow f 1 = scaledFlow f 1 + 0 by
    rw [add_zero]; exact h.symm)
theorem scaledFlow_natCast (f : Row 3) (n : ℕ) : scaledFlow f (n : Row 4) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, map_add, ih, scaledFlow_one, add_zero]
theorem scaledFlow_pow (f : Row 3) (b : Row 4) (k : ℕ) :
    scaledFlow f (b ^ (k + 1)) = (↑(k + 1) : Row 4) * b ^ k * scaledFlow f b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ b (k + 1), scaledFlow_mul, ih, pow_succ b k]
    simp only [Nat.cast_succ]
    ring
def thirdConstant : Geom[X] := Polynomial.C ((3 : Geom)⁻¹)
theorem three_mul_thirdConstant : (3 : Geom[X]) * thirdConstant = 1 := by
  have h : (3 : Geom) ≠ 0 := geomCast_ne_zero (a := 3) (by decide) (by decide)
  change (Polynomial.C (3 : Geom)) * Polynomial.C ((3 : Geom)⁻¹) = 1
  rw [← map_mul, mul_inv_cancel₀ h, map_one]
theorem scaledFlow_graph (f : Row 3) : scaledFlow f (graphRaw f) = 0 := by
  have h := congrArg (MvPolynomial.C : Geom[X] →+* Row 4) three_mul_thirdConstant
  simp only [map_mul, map_ofNat, map_one] at h
  have hvelocity : 3 * thirdVelocityNumerator f = -partialFlow (graphRaw f) := by
    rw [thirdVelocityNumerator, Polynomial.C_neg]
    change 3 * (MvPolynomial.C (-thirdConstant) * partialFlow (graphRaw f)) = _
    rw [map_neg]
    calc
      _ = -(3 * MvPolynomial.C thirdConstant) * partialFlow (graphRaw f) := by ring
      _ = _ := by rw [h]; ring
  change liftSep f * partialFlow (graphRaw f) +
    thirdVelocityNumerator f * K1_13_6.separant (graphRaw f) = 0
  rw [graph_separant]
  calc
    _ = liftSep f * partialFlow (graphRaw f) + (3 * thirdVelocityNumerator f) * liftSep f := by ring
    _ = 0 := by rw [hvelocity]; ring
abbrev rawGraphIdeal (f : Row 3) : Ideal (Row 4) := Ideal.span {graphRaw f}
abbrev classOf (f : Row 3) := Ideal.Quotient.mk (rawGraphIdeal f)
theorem scaledFlow_congr (f : Row 3) {P Q : Row 4} (h : classOf f P = classOf f Q) :
    classOf f (scaledFlow f P) = classOf f (scaledFlow f Q) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h)
  apply Ideal.Quotient.eq.mpr
  rw [← map_sub, ← hb, scaledFlow_mul, scaledFlow_graph, mul_zero, zero_add]
  exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
theorem scaledFlow_lift (f b : Row 3) :
    classOf f (scaledFlow f (liftRaw b)) = classOf f (liftRaw (tangentNumerator f b)) := by
  apply Ideal.Quotient.eq.mpr
  rw [scaledFlow_apply, pderiv_last_lift, mul_zero, add_zero, partialFlow_lift]
  refine Ideal.mem_span_singleton'.mpr ⟨liftRaw (pderiv 2 b), ?_⟩
  simp only [graphRaw, tangentNumerator, liftSep, separant, map_sub, map_mul]
  ring
theorem scaledFlow_sep (f : Row 3) :
    scaledFlow f (liftSep f) = liftSep f * partialFlow (liftSep f) := by
  rw [scaledFlow_apply, pderiv_last_lift, mul_zero, add_zero]
theorem scaledFlow_scaled (f : Row 3) (k : ℕ) (b : Row 4) :
    scaledFlow f (3 * liftSep f ^ (k + 1) * b) =
      3 * liftSep f ^ (k + 1) * scaledFlow f b +
        3 * (↑(k + 1) : Row 4) * liftSep f ^ (k + 1) * partialFlow (liftSep f) * b := by
  have h3 : scaledFlow f 3 = 0 := scaledFlow_natCast f 3
  rw [scaledFlow_mul, scaledFlow_mul f 3, h3, zero_mul, add_zero, scaledFlow_pow, scaledFlow_sep,
    pow_succ (liftSep f) k]
  ring
theorem rawComparison (f : Row 3) (k : ℕ) :
    classOf f (3 * liftSep f ^ (k + 1) * thirdNumerator f k) =
      classOf f (liftRaw (compatibilityNumerator f k)) := by
  induction k with
  | zero =>
    apply Ideal.Quotient.eq.mpr
    refine Ideal.mem_span_singleton'.mpr ⟨1, ?_⟩
    simp only [one_mul, thirdNumerator, compatibilityNumerator, zero_add, pow_one, map_neg, graphRaw]
    ring
  | succ k ih =>
    let s := liftSep f
    let b := thirdNumerator f k
    let A := compatibilityNumerator f k
    let q := classOf f
    have h : q (3 * s ^ (k + 1) * b) = q (liftRaw A) := ih
    have hD := (scaledFlow_congr f h).trans (scaledFlow_lift f A)
    have hs := scaledFlow_lift f (separant f)
    change q (scaledFlow f (3 * s ^ (k + 1) * b)) = q (liftRaw (tangentNumerator f A)) at hD
    change q (scaledFlow f s) = q (liftRaw (tangentNumerator f (separant f))) at hs
    calc
      q (3 * s ^ (k + 1 + 1) * liftedStep f k b) =
          q (s * scaledFlow f (3 * s ^ (k + 1) * b) -
            (↑(2 * k + 1) : Row 4) * (3 * s ^ (k + 1) * b) * scaledFlow f s) := by
        congr 1
        rw [liftedStep, scaledFlow_scaled, scaledFlow_sep, scaledFlow_apply, pow_succ s (k + 1)]
        push_cast
        ring
      _ = q (liftRaw (compatibilityNumerator f (k + 1))) := by
        rw [map_sub q, map_mul q, map_mul q, map_mul q, hD, h, hs]
        simp only [compatibilityNumerator, map_sub, map_mul, map_natCast]
        rfl
theorem genericRow_mem_graphIdeal (f : Row 3) {P : Row 4} (h : P ∈ rawGraphIdeal f) :
    genericRow P ∈ graphIdeal f := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h
  rw [← hb, genericRow, map_mul]
  change genericRow b * genericRow (graphRaw f) ∈ graphIdeal f
  rw [generic_graph]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
private theorem represents (f : Row 3) (k : ℕ) :
    RepresentsOnGraph f (compatibilityNumerator f k) (genericRow (thirdNumerator f k)) := by
  have h := genericRow_mem_graphIdeal f (Ideal.Quotient.eq.mp (rawComparison f k))
  change MvPolynomial.map genericCoeff (_ - _) ∈ graphIdeal f at h
  rw [map_sub, map_mul, map_mul, map_pow, map_ofNat] at h
  change 3 * genericRow (liftSep f) ^ (k + 1) * genericRow (thirdNumerator f k) -
    genericRow (liftRaw (compatibilityNumerator f k)) ∈ graphIdeal f at h
  rw [generic_lift, generic_lift] at h
  let c := genericCoeff thirdConstant
  have h3 : 3 * c = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg genericCoeff three_mul_thirdConstant
  have hc : c ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h3
    exact zero_ne_one h3
  have hC : (3 : GeoRow 4) * MvPolynomial.C c = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (MvPolynomial.C : GeometricX →+* GeoRow 4) h3
  refine ⟨0, k + 1, c, hc, ?_⟩
  simp only [pow_zero, one_mul]
  convert Ideal.mul_mem_left (graphIdeal f) (MvPolynomial.C c) h using 1
  rw [mul_sub, ← mul_assoc (MvPolynomial.C c), ← mul_assoc (MvPolynomial.C c), mul_comm (MvPolynomial.C c) 3,
    hC, one_mul]
end
end K1_13_5_4_1_2
end
section
namespace K1_13_4_4_2
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_4
open scoped Polynomial BigOperators
private def line {R : Type*} [CommSemiring R] (i : SeedVar) :
    SeedRow R →+* (SeedRow R)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun j =>
    Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0
theorem line_C {R : Type*} [CommSemiring R] (i : SeedVar) (r : R) :
    line i (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  simp [line]
theorem line_X {R : Type*} [CommSemiring R] (i j : SeedVar) :
    line i (MvPolynomial.X j : SeedRow R) =
      Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0 := by
  simp [line]
theorem line_mul_X {R : Type*} [CommSemiring R] (i j : SeedVar) (F : SeedRow R) :
    line i (F * MvPolynomial.X j) =
      (if j = i then line i F * Polynomial.X else 0) +
        Polynomial.C (MvPolynomial.X j) * line i F := by
  rw [map_mul, line_X]
  by_cases h : j = i <;> simp [h, mul_add, mul_comm, add_comm]
private theorem line_zero {R : Type*} [CommSemiring R] (i : SeedVar) (F : SeedRow R) :
    (line i F).coeff 0 = F := by
  let ev := (Polynomial.constantCoeff (R := SeedRow R)).comp (line i)
  change ev F = (RingHom.id _) F
  have he : ev = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ev, line_C]
    · intro j
      by_cases h : j = i <;> simp [ev, line_X, h]
  rw [he]
theorem line_one {R : Type*} [CommSemiring R] (i : SeedVar) (F : SeedRow R) :
    (line i F).coeff 1 = MvPolynomial.pderiv i F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [line_C]
  | add P Q hp hq => simp [hp, hq]
  | mul_X P j hp =>
    rw [line_mul_X, Polynomial.coeff_add, Polynomial.coeff_C_mul, hp, MvPolynomial.pderiv_mul]
    by_cases h : j = i
    · subst j
      simp only [ite_true, MvPolynomial.pderiv_X_self, mul_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, Polynomial.coeff_mul_X, line_zero, mul_comm]
      exact add_comm _ _
    · simp [h, MvPolynomial.pderiv_X_of_ne h, mul_comm]
private theorem line_coeff {R : Type*} [CommSemiring R] (i : SeedVar) (F : SeedRow R) (n : ℕ) :
    (line i F).coeff n = K1_13_4_3.hasse (Finsupp.single i n) F := by
  classical
  induction F using MvPolynomial.induction_on generalizing n with
  | C c =>
    cases n <;> simp [line_C, K1_13_4_3.partial_C, Finsupp.single_eq_zero]
  | add P Q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp, hq, K1_13_4_3.hasse,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | mul_X P j hp =>
    rw [line_mul_X, Polynomial.coeff_add, Polynomial.coeff_C_mul, hp, K1_13_4_3.partial_mul_X]
    by_cases h : j = i
    · subst j
      cases n with
      | zero => simp [mul_comm]
      | succ n =>
        have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
        simp only [ite_true, Polynomial.coeff_mul_X, hp, Finsupp.mem_support_iff,
          Finsupp.single_eq_same, ← Finsupp.single_tsub, Nat.succ_sub_one]
        rw [ite_eq_left hn, mul_comm (MvPolynomial.X i)]
    · simp [h, Finsupp.single_eq_of_ne h, mul_comm]
private theorem line_toGeneric (i : SeedVar) (F : PhysicalRow) (n : ℕ) :
    (line i (toGeneric F)).coeff n = toGeneric (mixedHasse (Finsupp.single i n) F) := by
  let g : PhysicalRow →+* GenericRow := MvPolynomial.map inclX
  let l := (line i).comp g
  let r := (Polynomial.mapRingHom g).comp (line i)
  have he : l = r := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [l, r, g, line_C, Polynomial.coe_mapRingHom]
    · intro j
      by_cases h : j = i <;> simp [l, r, g, line_X, h, Polynomial.coe_mapRingHom]
  have h : line i (toGeneric F) = (line i F).map g := DFunLike.congr_fun he F
  rw [h, Polynomial.coeff_map, line_coeff, K1_13_4_3.partial_eq_mixedHasse]
  rfl
private theorem transverse {f : GenericRow} {i : SeedVar}
    (hpos : 0 < f.degreeOf i) (hsmall : f.degreeOf i < K1.p) :
    ¬ f ∣ (line i f).coeff 1 := by
  classical
  rw [line_one]
  have hdeg : (MvPolynomial.pderiv i f).degreeOf i ≤ f.degreeOf i - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    have hd := MvPolynomial.le_degreeOf_of_mem_support i (MvPolynomial.mem_support_iff.mpr
      (left_ne_zero_of_mul hm))
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hd
    omega
  have hnz : MvPolynomial.pderiv i f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m i) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    have hup : 0 < u i := hsup.trans_le htop
    have hult := (MvPolynomial.le_degreeOf_of_mem_support i hu).trans_lt hsmall
    let m := u - Finsupp.single i 1
    have hsum : m + Finsupp.single i 1 = u :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hup)
    have hm : (m i).succ = u i := by
      change m i + 1 = u i
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using
        congrArg (fun a : SeedVar →₀ ℕ => a i) hsum
    let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
    let _ : CharP GenericX K1.p := charP_of_injective_ringHom inclConst.injective K1.p
    have hcast : (↑(u i) : GenericX) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hup ((CharP.cast_eq_zero_iff GenericX K1.p _).mp hz))
    have hcoeff : (MvPolynomial.pderiv i f).coeff m ≠ 0 := by
      rw [MvPolynomial.coeff_pderiv, ← Nat.cast_succ, hm, hsum]
      exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hu) hcast
    intro hz
    exact hcoeff (by simp [hz])
  rintro ⟨g, hg⟩
  have hne : f ≠ 0 ∧ g ≠ 0 := by simpa [hg] using hnz
  rw [hg, MvPolynomial.degreeOf_mul_eq hne.1 hne.2] at hdeg
  omega
theorem exact_coeff {R : Type*} [CommRing R]
    (T : R →+* R[X]) (hzero : ∀ G, (T G).coeff 0 = G)
    {f P : R} {a : ℕ} (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (ha : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) :
    ¬ f ∣ (T P).coeff a := by
  obtain ⟨U, rfl⟩ := ha
  have hu : ¬ f ∣ U := by
    rintro ⟨V, rfl⟩
    exact hexact ⟨V, by rw [pow_succ, mul_assoc]⟩
  let J := Ideal.span ({f} : Set R)
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  let reduce := Ideal.Quotient.mk J
  let tr := (Polynomial.mapRingHom reduce).comp T
  have hz (G : R) : reduce G = 0 ↔ f ∣ G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hc (G : R) (n : ℕ) : (tr G).coeff n = reduce ((T G).coeff n) :=
    Polynomial.coeff_map _ _
  have hc₀ (G : R) : (tr G).coeff 0 = reduce G := by rw [hc, hzero]
  obtain ⟨V, hV⟩ := Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0 = 0 by rw [hc₀]; exact (hz _).mpr dvd_rfl)
  have hfirst : V.coeff 0 = reduce ((T f).coeff 1) := by
    rw [← hc, hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr : reduce ((T (f ^ a * U)).coeff a) = reduce ((T f).coeff 1) ^ a * reduce U := by
    rw [← hc, map_mul, map_pow, hV, mul_pow, mul_assoc]
    have he := Polynomial.coeff_X_pow_mul (V ^ a * tr U) a 0
    rw [zero_add] at he
    rw [he]
    change Polynomial.constantCoeff (V ^ a * tr U) = _
    rw [map_mul, map_pow]
    change (V.coeff 0) ^ a * (tr U).coeff 0 = _
    rw [hfirst, hc₀]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hz _).not.mpr hsep)) ((hz _).not.mpr hu))
    (hr.symm.trans ((hz _).mpr h))
private theorem pow_dvd_of_coeff {R : Type*} [CommRing R]
    (T : R →+* R[X]) (hzero : ∀ G, (T G).coeff 0 = G)
    {f P : R} (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (n : ℕ) (htest : ∀ a < n, f ∣ (T P).coeff a) : f ^ n ∣ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih fun a ha => htest a (Nat.lt_succ_of_lt ha)
    by_contra hexact
    exact exact_coeff T hzero hf hsep hn hexact (htest n (Nat.lt_succ_self n))
private theorem positive_jet_degree {f : GenericRow} (hf : 0 < jetTotal f) :
    ∃ j : Fin 3, 0 < f.degreeOf (some j) := by
  classical
  by_contra h
  apply (not_le_of_gt hf)
  rw [jetTotal, MvPolynomial.weightedTotalDegree]
  apply Finset.sup_le
  intro m hm
  apply le_of_eq
  rw [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro i _
  cases i with
  | none => simp
  | some j =>
    have hj₀ : f.degreeOf (some j) ≤ 0 :=
      Nat.le_of_not_gt fun hj => h ⟨j, hj⟩
    have hj := (MvPolynomial.le_degreeOf_of_mem_support (some j) hm).trans hj₀
    simp [Nat.eq_zero_of_le_zero hj]
end
end K1_13_4_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_3_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_3 MvPolynomial
private theorem exists_open_prime {R : Type*} [CommRing R] {I P : Ideal R}
    [P.IsPrime] {s : R} (hIP : I ≤ P) (hs : s ∉ P) :
    ∃ q : Ideal (OpenRing I s), q.IsPrime ∧ q.comap (onOpen I s) = P := by
  let p := P.map (Ideal.Quotient.mk I)
  have hp : p.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hcomap : p.comap (Ideal.Quotient.mk I) = P := by
    change (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIP]
  let M := Submonoid.powers (Ideal.Quotient.mk I s)
  have hM : Disjoint (M : Set (R ⧸ I)) (p : Set (R ⧸ I)) := by
    have hle : M ≤ p.primeCompl := Submonoid.powers_le.mpr (by
      change s ∉ p.comap (Ideal.Quotient.mk I)
      rwa [hcomap])
    exact Set.disjoint_left.mpr fun _ ha hb => hle ha hb
  let q := p.map (algebraMap (R ⧸ I) (OpenRing I s))
  refine ⟨q, IsLocalization.isPrime_of_isPrime_disjoint M _ p hp hM, ?_⟩
  rw [onOpen, ← Ideal.comap_comap]
  change (q.under (R ⧸ I)).comap (Ideal.Quotient.mk I) = P
  rw [show q.under (R ⧸ I) = p from
    IsLocalization.under_map_of_isPrime_disjoint M _ hp hM, hcomap]
private def openAtPrimeEquivQuotient {R : Type*} [CommRing R] {I P : Ideal R}
    [P.IsPrime] {s : R} (q : Ideal (OpenRing I s)) [q.IsPrime]
    (hP : q.comap (onOpen I s) = P) :
    Localization.AtPrime q ≃+*
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  let p := q.comap (algebraMap (R ⧸ I) (OpenRing I s))
  letI : p.IsPrime := Ideal.comap_isPrime _ q
  have hp : p.comap (Ideal.Quotient.mk I) = P := hP
  let A := Localization.AtPrime P
  let C := A ⧸ I.map (algebraMap R A)
  have hmonoid : Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl = p.primeCompl := by
    change P.primeCompl.map (Ideal.Quotient.mk I) = p.primeCompl
    simpa only [hp] using
      p.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : IsLocalization p.primeCompl C := hmonoid ▸
    (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl) C)
  letI : IsLocalization p.primeCompl (Localization.AtPrime q) := by
    change IsLocalization.AtPrime (Localization.AtPrime q)
      (q.comap (algebraMap (R ⧸ I) (OpenRing I s)))
    infer_instance
  exact (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime q) C).toRingEquiv
private theorem colength_eq_of_quotient_equiv {A B : Type*} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B} (e : (A ⧸ I) ≃+* (B ⧸ J)) :
    Module.length A (A ⧸ I) = Module.length B (B ⧸ J) := by
  rw [Module.length_eq_of_surjective (R := A ⧸ I) Ideal.Quotient.mk_surjective,
    Module.length_eq_of_surjective (R := B ⧸ J) Ideal.Quotient.mk_surjective]
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm
end
end K1_13_5_4_2_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_5
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5_3 Polynomial
open scoped Polynomial WithZero
theorem algebraic_over_parameter {k F : Type} [Field k] [Field F] [Algebra k F]
    (hF : CurveField k F) {x : F} (hx : Transcendental k x) (y : F) :
    IsAlgebraic (IntermediateField.adjoin k {x}) y := by
  obtain ⟨t, ht, hfinite⟩ := hF
  let := hfinite
  have halg (z : F) : IsAlgebraic (Algebra.adjoin k {t}) z :=
    IntermediateField.isAlgebraic_adjoin_iff.mp
      (Algebra.IsAlgebraic.isAlgebraic (R := IntermediateField.adjoin k {t}) z)
  have ht' : IsAlgebraic (Algebra.adjoin k {x}) t := by
    simpa using IsAlgebraic.adjoin_singleton ht hx (halg x)
  rw [IntermediateField.isAlgebraic_adjoin_iff]
  apply IsAlgebraic.adjoin_of_forall_isAlgebraic (s := {t}) (t := {x}) _ (halg y)
  intro z hz
  have hzt : z = t := hz.1
  simpa only [hzt] using ht'
private theorem residue_zero_iff {F : Type} [Field F] (w : Valuation F ℤᵐ⁰)
    (x : w.valuationSubring) :
    IsLocalRing.residue w.valuationSubring x = 0 ↔ w (x : F) < 1 :=
  (IsLocalRing.residue_eq_zero_iff x).trans (w.mem_maximalIdeal_iff (a := x))
theorem residue_constant {k F : Type} [Field k] [IsAlgClosed k]
    [Field F] [Algebra k F] (hF : CurveField k F) (w : Valuation F ℤᵐ⁰)
    (hk : w.IsTrivialOn k) (hn : ∃ y : F, y ≠ 0 ∧ w y ≠ 1)
    (x : F) (hx : w x ≤ 1) :
    ∃ c : k, w (x - algebraMap k F c) < 1 := by
  let : w.IsTrivialOn k := hk
  let A := w.valuationSubring
  let ι : k →+* A := (algebraMap k F).codRestrict A
    (fun c => Valuation.IsTrivialOn.valuation_algebraMap_le_one w c)
  let ρ := IsLocalRing.residue A
  let : Algebra k (IsLocalRing.ResidueField A) := (ρ.comp ι).toAlgebra
  let u : A := ⟨x, hx⟩
  have hres : IsAlgebraic k (ρ u) := by
    by_contra htrans
    have hpoly (p : k[X]) (hp : p ≠ 0) : w (aeval x p) = 1 := by
      let z := p.eval₂ ι u
      have hz : (z : F) = aeval x p := Polynomial.hom_eval₂ p ι A.subtype u
      have hzres : ρ z ≠ 0 := by
        intro hzero
        apply htrans
        refine ⟨p, hp, ?_⟩
        change p.eval₂ (ρ.comp ι) (ρ u) = 0
        rw [← Polynomial.hom_eval₂ p ι ρ u]
        exact hzero
      rw [← hz]
      exact le_antisymm z.2 (le_of_not_gt fun hlt => hzres ((residue_zero_iff w z).2 hlt))
    have htr : Transcendental k x := by
      rintro ⟨p, hp, hzero⟩
      have he := hpoly p hp
      rw [hzero, map_zero] at he
      exact zero_ne_one he
    let B := IntermediateField.adjoin k {x}
    let : w.IsTrivialOn B := ⟨by
      intro b hb
      have hb' : (b : F) ≠ 0 := fun h => hb (Subtype.ext h)
      obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff k (b : F)).1 b.2
      have hp : p ≠ 0 := fun h => hb' (by simp [hpq, h])
      have hq : q ≠ 0 := fun h => hb' (by simp [hpq, h])
      change w (b : F) = 1
      rw [hpq, w.map_div, hpoly p hp, hpoly q hq, div_self one_ne_zero]⟩
    obtain ⟨y, hy, hvy⟩ := hn
    exact (Valuation.transcendental_of_ne_one B (v := w) y hy hvy)
      (algebraic_over_parameter hF htr y)
  let B := IntermediateField.adjoin k {ρ u}
  let : Algebra.IsAlgebraic k B :=
    IntermediateField.isAlgebraic_adjoin_simple (isAlgebraic_iff_isIntegral.mp hres)
  have hB := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic B
  have hu : ρ u ∈ (⊥ : IntermediateField k (IsLocalRing.ResidueField A)) :=
    hB ▸ IntermediateField.mem_adjoin_simple_self k (ρ u)
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hu
  refine ⟨c, (residue_zero_iff w (u - ι c)).1 ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr hc.symm
theorem gauss_of_residue_constants {k F L : Type} [Field k] [Field F]
    [Algebra k F] [Field L] (j : F →+* L) (a : L) (v : Valuation L ℤᵐ⁰)
    (ha : v a = 1)
    (hres : ∀ x : F, v (j x) ≤ 1 → ∃ c : k, v (j (x - algebraMap k F c)) < 1)
    (hfresh : ∀ q : k[X], q ≠ 0 → v (q.eval₂ (j.comp (algebraMap k F)) a) = 1)
    (g : F[X]) :
    v (g.eval₂ j a) = g.support.sup (fun i => v (j (g.coeff i))) := by
  classical
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_mem_eq_sup g.support (nonempty_support_iff.mpr hg)
      (fun i => v (j (g.coeff i)))
  let b := g.coeff m
  have hb : b ≠ 0 := mem_support_iff.mp hm
  have hvb : 0 < v (j b) := v.pos_iff.mpr ((map_ne_zero j).2 hb)
  let d (i : ℕ) := g.coeff i / b
  have hd (i : ℕ) : v (j (d i)) ≤ 1 := by
    by_cases hi : i ∈ g.support
    · dsimp only [d]
      rw [map_div₀, v.map_div, div_le_one₀ hvb]
      change v (j (g.coeff i)) ≤ v (j (g.coeff m))
      rw [← hmax]
      exact Finset.le_sup (f := fun n => v (j (g.coeff n))) hi
    · simp [d, notMem_support_iff.mp hi]
  choose c hc using fun i => hres (d i) (hd i)
  have hcm : c m ≠ 0 := by
    intro hz
    have h := hc m
    simp [d, b, hb, hz] at h
  let q : k[X] := ∑ i ∈ g.support, monomial i (c i)
  have hqcoeff : q.coeff m = c m := by
    simp [q, finsetSum_coeff, coeff_monomial, hm]
  have hq : q ≠ 0 := fun h => hcm (by simpa [h] using hqcoeff.symm)
  let r := j.comp (algebraMap k F)
  let s := ∑ i ∈ g.support, j (d i) * a ^ i
  have hqeval : q.eval₂ r a = ∑ i ∈ g.support, r (c i) * a ^ i := by
    simp only [q, eval₂_finsetSum, eval₂_monomial]
  have hdiff : v (s - q.eval₂ r a) < 1 := by
    dsimp only [s]
    rw [hqeval, ← Finset.sum_sub_distrib]
    apply v.map_sum_lt one_ne_zero
    intro i _
    rw [← sub_mul, map_mul, map_pow, ha, one_pow, mul_one]
    change v (j (d i) - j (algebraMap k F (c i))) < 1
    rw [← map_sub]
    exact hc i
  have hqv := hfresh q hq
  have hdom : v (s - q.eval₂ r a) < v (q.eval₂ r a) := lt_of_lt_of_eq hdiff hqv.symm
  have hs : v s = 1 := (v.map_eq_of_sub_lt hdom).trans hqv
  have hscale : g.eval₂ j a = j b * s := by
    dsimp only [s]
    rw [eval₂_eq_sum, sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [d]
    rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hb]
  rw [hscale, map_mul, hs, mul_one]
  exact hmax.symm
theorem proof : K1_13_6_3_5_3.c5 := by
  intro R D v
  unfold FreshGauss
  by_cases h : ∀ x : D.Old, x ≠ 0 → v.value (D.includeOld x) = 1
  · exact Or.inl h
  right
  let w := v.value.comap D.includeOld
  have hk : w.IsTrivialOn Geom := ⟨by
    intro c hc
    change v.value ((D.includeOld.comp (algebraMap Geom D.Old)) c) = 1
    rw [D.constants]
    exact v.on_constants (geomConstants c) ((map_ne_zero geomConstants).2 hc)⟩
  have hn : ∃ y : D.Old, y ≠ 0 ∧ w y ≠ 1 := by
    obtain ⟨y, hy⟩ := not_forall.mp h
    exact ⟨y, (Classical.not_imp.mp hy).1, (Classical.not_imp.mp hy).2⟩
  have hfresh (q : Geom[X]) (hq : q ≠ 0) :
      v.value (q.eval₂ (D.includeOld.comp (algebraMap Geom D.Old)) D.center) = 1 := by
    have heval : q.eval₂ (D.includeOld.comp (algebraMap Geom D.Old)) D.center =
        algebraMap GeoField D.Fresh (genericCoeffs q) := by
      rw [D.constants, FreshCurve.center, ← Polynomial.hom_eval₂,
        geomConstants, genericArgument, ← Polynomial.hom_eval₂, eval₂_C_X]
    have hginj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp
        (IsFractionRing.injective Geom[X] GenericField)
    rw [heval]
    exact v.on_constants _ (map_ne_zero_iff genericCoeffs hginj |>.2 hq)
  have ha : v.value D.center = 1 := by
    simpa only [eval₂_X] using hfresh Polynomial.X Polynomial.X_ne_zero
  exact gauss_of_residue_constants D.includeOld D.center v.value ha
    (residue_constant D.oldCurve w hk hn) hfresh
end K1_13_6_3_5_3_5
end
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_2_2
noncomputable section
open MvPolynomial K1_11_2
variable {F : Type*} [Field F]
def parameterNode (x : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4]
theorem nodeWord_omits (x a b c d : F) (Q : MvPolynomial (Fin 5) F)
    (hQ : OmitsMessages Q) : nodeWordMap x a b c d Q = parameterNode x Q := by
  change eval₂ C (nodeWordImages x a b c d) Q = eval₂ C ![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4] Q
  apply eval₂_congr
  intro i e hi hc
  have ht := omitted_message_tag Q hQ e (mem_support_iff.mpr hc)
  have hin := Finsupp.mem_support_iff.mp hi
  fin_cases i <;> simp_all [nodeWordImages]
def seedEval (q : ℕ) : MvPolynomial (Fin 5) F →ₐ[F] Polynomial F :=
  aeval ![0, 0, 0, Polynomial.X, Polynomial.X ^ q]
theorem eval_graph (q : ℕ) (x : F) (Q : MvPolynomial (Fin 5) F) :
    (graph q Q).eval (Polynomial.C x) = seedEval q (parameterNode x Q) := by
  have heq : (Polynomial.evalRingHom (Polynomial.C x)).comp (graph (F := F) q).toRingHom =
      (seedEval q).toRingHom.comp (parameterNode x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [graph, seedEval, parameterNode, Polynomial.algebraMap_apply]
    · intro i
      fin_cases i <;> simp [graph, seedEval, parameterNode]
  exact RingHom.congr_fun heq Q
end
end K1_11_2_2
end
section
namespace K1_14_3R_1
open K1_14_3 Polynomial
theorem fibre_pow_of_hasse (F : FibreJet) (y v : SeedClosure) (k : ℕ)
    (h : ∀ a b : ℕ, a + b < k →
      (hasseDeriv a ((hasseDeriv b F).eval (C v))).eval y = 0) :
    F ∈ fibrePoint y v ^ k := by
  let I := fibrePoint y v
  let yDiff := Polynomial.X (R := SeedClosure) - C y
  let vDiff := Polynomial.X (R := Polynomial SeedClosure) - C (C v)
  have hY : C yDiff ∈ I := Ideal.subset_span (by simp [yDiff])
  have hV : vDiff ∈ I := Ideal.subset_span (by simp [vDiff])
  suffices hsum : (taylor (C v) F).sum (fun b B => C B * vDiff ^ b) ∈ I ^ k by
    simpa only [vDiff, sum_taylor_eq] using hsum
  unfold Polynomial.sum
  apply Ideal.sum_mem
  intro b _
  let B := (taylor (C v) F).coeff b
  change C B * vDiff ^ b ∈ I ^ k
  have hB : (taylor y B).sum (fun a c => C c * yDiff ^ a) = B :=
    sum_taylor_eq B y
  rw [← hB]
  unfold Polynomial.sum
  rw [map_sum, Finset.sum_mul]
  apply Ideal.sum_mem
  intro a _
  rw [map_mul, map_pow, mul_assoc]
  by_cases hab : a + b < k
  · have hc : (taylor y B).coeff a = 0 := by
      simpa only [B, taylor_coeff] using h a b hab
    simp [hc]
  · apply Ideal.mul_mem_left
    apply Ideal.pow_le_pow_right (le_of_not_gt hab)
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hY a) (Ideal.pow_mem_pow hV b)
end K1_14_3R_1
end
