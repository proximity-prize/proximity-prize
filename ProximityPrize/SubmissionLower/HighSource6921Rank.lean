import ProximityPrize.SubmissionLower.HighSource6921Contact

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

section PackSource_K1_14_1_4Weight
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace HighSource6921.Weight

noncomputable section

open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial BigOperators

def Bounded {R : Type*} [Semiring R] (u v N : ℕ)
    (P : Polynomial (Polynomial R[X])) : Prop :=
  ∀ j i a, (((P.coeff j).coeff i).coeff a) ≠ 0 → a + u*i + v*j ≤ N

private theorem bounded_mono {R : Type*} [Semiring R] {u v N M : ℕ}
    {P : Polynomial (Polynomial R[X])} (hp : Bounded u v N P) (hn : N ≤ M) :
    Bounded u v M P :=
  fun j i a ha => (hp j i a ha).trans hn

private theorem bounded_add {R : Type*} [Semiring R] {u v N : ℕ}
    {P Q : Polynomial (Polynomial R[X])} (hp : Bounded u v N P) (hq : Bounded u v N Q) :
    Bounded u v N (P + Q) := by
  intro j i a h
  by_contra hn
  simp only [coeff_add, not_imp_comm.mp (hp j i a) hn, not_imp_comm.mp (hq j i a) hn,
    add_zero] at h
  exact h rfl

private theorem bounded_sum {R ι : Type*} [Semiring R] {u v N : ℕ}
    (T : Finset ι) (P : ι → Polynomial (Polynomial R[X]))
    (hp : ∀ t ∈ T, Bounded u v N (P t)) : Bounded u v N (∑ t ∈ T, P t) := by
  intro j i a hn
  by_contra hx
  apply hn
  simp only [finsetSum_coeff]
  exact Finset.sum_eq_zero fun t ht => not_imp_comm.mp (hp t ht j i a) hx

private theorem bounded_mul {R : Type*} [Semiring R] {u v N M : ℕ}
    {P Q : Polynomial (Polynomial R[X])}
    (hp : Bounded u v N P) (hq : Bounded u v M Q) : Bounded u v (N+M) (P*Q) := by
  intro j i a hn
  by_contra! hx
  apply hn
  rw [coeff_mul]
  simp only [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ij hj
  rw [coeff_mul, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ii hi
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ia ha
  by_contra hprod
  have h₁ := hp ij.1 ii.1 ia.1 (left_ne_zero_of_mul hprod)
  have h₂ := hq ij.2 ii.2 ia.2 (right_ne_zero_of_mul hprod)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hj hi ha
  rw [← hj, ← hi, ← ha, Nat.mul_add, Nat.mul_add] at hx
  omega

private theorem bounded_jetConstant {R : Type*} [CommSemiring R] {u v N : ℕ}
    {p : R[X]} (hp : p.natDegree ≤ N) : Bounded u v N (jetConstant p) := by
  intro j i a ha
  have hj : j = 0 := by by_contra hj; simp [jetConstant, coeff_C, hj] at ha
  have hi : i = 0 := by subst j; by_contra hi; simp [jetConstant, coeff_C, hi] at ha
  subst j i
  simp only [jetConstant, RingHom.comp_apply, coeff_C_zero, mul_zero, add_zero] at *
  exact (le_natDegree_of_ne_zero ha).trans hp

abbrev ordinate {R : Type*} [Semiring R] : Polynomial (Polynomial R) :=
  (@Polynomial.C (Polynomial R) _) (Polynomial.X (R := R))

private theorem bounded_y {R : Type*} [CommSemiring R] (u v : ℕ) :
    Bounded u v u (ordinate (R := R[X])) := by
  intro j i a ha
  have hj : j = 0 := by by_contra hj; simp [coeff_C, hj] at ha
  have hi : i = 1 := by subst j; by_contra hi; simp [coeff_X, Ne.symm hi] at ha
  subst j i
  have ha₀ : a = 0 := by by_contra h; simp [coeff_X, coeff_one, h] at ha
  simp [ha₀]

private theorem bounded_v {R : Type*} [CommSemiring R] (u v : ℕ) :
    Bounded u v v (Polynomial.X : Polynomial (Polynomial R[X])) := by
  intro j i a ha
  have hj : j = 1 := by by_contra hj; simp [coeff_X, Ne.symm hj] at ha
  have hi : i = 0 := by subst j; by_contra hi; simp [coeff_one, hi] at ha
  subst j i
  have ha₀ : a = 0 := by by_contra h; simp [coeff_one, h] at ha
  simp [ha₀]

private theorem bounded_pow {R : Type*} [CommSemiring R] {u v N : ℕ}
    {P : Polynomial (Polynomial R[X])} (hp : Bounded u v N P) (n : ℕ) :
    Bounded u v (N*n) (P^n) := by
  induction n with
  | zero => simpa using (bounded_jetConstant (u := u) (v := v) (N := 0)
      (p := (1 : R[X])) (by simp))
  | succ n ih => simpa [pow_succ, Nat.mul_succ] using bounded_mul ih hp

/-- Substitute the two jet variables after mapping their common coefficient ring. -/
def substitute {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y v : Polynomial (Polynomial B)) :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial B) :=
  eval₂RingHom (eval₂RingHom ((jetConstant (R := B)).comp f) y) v

@[simp] theorem substitute_C {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y v : Polynomial (Polynomial B)) (g : A[X]) :
    substitute f y v (C g) = eval₂RingHom ((jetConstant (R := B)).comp f) y g := by
  simp [substitute]

@[simp] theorem substitute_X {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y v : Polynomial (Polynomial B)) :
    substitute f y v (Polynomial.X : Polynomial A[X]) = v := by
  simp [substitute]

def rawOrdinate {h} (D : PoleData h) (Crt : CRTLift D) : RawSource :=
  jetConstant (rawBlock D) * ordinate + jetConstant (crtPolynomial Crt)

def rawVelocity {h} (D : PoleData h) (Crt : CRTLift D) : RawSource :=
  jetConstant (rawBlock D) * Polynomial.X + jetConstant (rawBlock D).derivative * ordinate +
    jetConstant (crtPolynomial Crt).derivative

theorem forward_apply {h} {D : PoleData h} (Crt : CRTLift D) (P : Source) :
    forward Crt P =
      substitute genericCoefficients.toRingHom (rawOrdinate D Crt) (rawVelocity D Crt) P :=
  rfl

theorem rawBlock_monic {h} (D : PoleData h) : (rawBlock D).Monic :=
  ((D.monic 0).mul (D.monic 1)).map _

theorem rawBlock_degree {h} (D : PoleData h) : (rawBlock D).natDegree = 2*h := by
  rw [rawBlock, poleProduct, ((D.monic 0).mul (D.monic 1)).natDegree_map,
    (D.monic 0).natDegree_mul (D.monic 1),
    D.degree, D.degree, two_mul]

private theorem crt_degree {h} (D : PoleData h) (Crt : CRTLift D) :
    (crtPolynomial Crt).natDegree ≤ 2*h := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  refine (natDegree_smul_le _ _).trans (natDegree_map_le.trans ?_)
  exact natDegree_le_iff_degree_le.mpr (Crt.numerator_degree i).le

private theorem ambient_degree {h s W P} (hp : P ∈ ambient h s W) {j i : ℕ}
    (hij : (P.coeff j).coeff i ≠ 0) :
    ((P.coeff j).coeff i).natDegree + (i+j)*(131071+h) ≤ W+(s.B+s.J)*(2*h)+j := by
  have hc := leadingCoeff_ne_zero.mpr hij
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr
    (show (((P.coeff j).coeff i).leadingCoeff).support ≠ ∅ by simpa using hc)
  have hne := MvPolynomial.mem_support_iff.mp he
  have hel : trueEligible h s W j i ((P.coeff j).coeff i).natDegree e := by
    by_contra nh
    exact hne (hp j i _ e nh)
  exact hel.2.2.2

theorem forward_bounded {h} (hpos : 0 < h) (hh : h ≤ 32970) {D : PoleData h} (Crt : CRTLift D)
    {s W P} (hp : P ∈ ambient h s W) :
    Bounded (131071-h) (131071-h-1) (W+(s.B+s.J)*(2*h)) (forward Crt P) := by
  let u := 131071-h
  let v := u-1
  have huv : v+1 = u := by dsimp [u, v]; omega
  have hd : 131071+h = 2*h+u := by dsimp [u]; omega
  have hy : Bounded u v (2*h+u) (rawOrdinate D Crt) :=
    bounded_add (bounded_mul (bounded_jetConstant (rawBlock_degree D).le) (bounded_y u v))
      (bounded_jetConstant ((crt_degree D Crt).trans (by omega)))
  have hv : Bounded u v (2*h+v) (rawVelocity D Crt) := by
    have hh' : (rawBlock D).derivative.natDegree ≤ 2*h-1 :=
      (natDegree_derivative_le _).trans (by rw [rawBlock_degree])
    refine bounded_add (bounded_add
      (bounded_mul (bounded_jetConstant (rawBlock_degree D).le) (bounded_v u v)) ?_) ?_
    · exact bounded_mono (bounded_mul (bounded_jetConstant hh') (bounded_y u v)) (by omega)
    · exact bounded_jetConstant (((natDegree_derivative_le _).trans
        (Nat.sub_le_sub_right (crt_degree D Crt) 1)).trans (by omega))
  change Bounded u v _ (forward Crt P)
  rw [forward_apply, P.as_sum_support_C_mul_X_pow, map_sum]
  apply bounded_sum
  intro j hj
  rw [map_mul, map_pow, (P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [substitute_C, substitute_X]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X, RingHom.comp_apply]
  apply bounded_sum
  intro i hi
  have hdeg := ambient_degree hp (mem_support_iff.mp hi)
  have hw : ((P.coeff j).coeff i).natDegree + (2*h+u)*i + (2*h+v)*j ≤
      W+(s.B+s.J)*(2*h) := by
    have hjmul : j*(2*h+u) = (2*h+v)*j+j := by
      rw [show 2*h+u = (2*h+v)+1 by omega, Nat.mul_add, Nat.mul_one, Nat.mul_comm j (2*h+v)]
    rw [hd, Nat.add_mul, hjmul, Nat.mul_comm i (2*h+u)] at hdeg
    omega
  apply bounded_mono (bounded_mul (bounded_mul ?_ (bounded_pow hy i)) (bounded_pow hv j)) hw
  exact bounded_jetConstant natDegree_map_le

theorem quotient_positions {h} {D : PoleData h} (s : Shape) (W : ℕ) {F Q : RawSource}
    (hF : Bounded (131071-h) (131071-h-1) (W+(s.B+s.J)*(2*h)) F)
    (he : F = jetConstant ((rawBlock D)^(s.B+s.J)) * Q) :
    ∀ j i, W < (131071-h)*i+(131071-h-1)*j → (Q.coeff j).coeff i = 0 := by
  intro j i hw
  by_contra hn
  let G := (F.coeff j).coeff i
  have hc : G = (rawBlock D)^(s.B+s.J) * (Q.coeff j).coeff i := by
    dsimp [G]
    rw [he]
    change ((C (C ((rawBlock D)^(s.B+s.J))) * Q).coeff j).coeff i = _
    rw [coeff_C_mul, coeff_C_mul]
  have hd : G.natDegree = (s.B+s.J)*(2*h) + ((Q.coeff j).coeff i).natDegree := by
    rw [hc, ((rawBlock_monic D).pow _).natDegree_mul' hn, natDegree_pow, rawBlock_degree]
  have hne : G ≠ 0 := by
    rw [hc]
    exact mul_ne_zero ((rawBlock_monic D).pow _).ne_zero hn
  have hb := hF j i G.natDegree (leadingCoeff_ne_zero.mpr hne)
  rw [hd] at hb
  omega

end
end HighSource6921.Weight
end PackSource_K1_14_1_4Weight

section PackSource_K1_14_1_4Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace HighSource6921.Weight

noncomputable section

open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial

private abbrev CentreField := FractionRing Seeds
private abbrev CentreJet := Polynomial (Polynomial CentreField)

private def doubleMap {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial B) :=
  mapRingHom (mapRingHom f)

private theorem map_substitute {A B C' : Type*} [CommSemiring A] [CommSemiring B]
    [CommSemiring C'] (f : A →+* B) (g : B →+* C') (y v : Polynomial (Polynomial B)) :
    (doubleMap g).comp (substitute f y v) =
      substitute (g.comp f) (doubleMap g y) (doubleMap g v) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [substitute, doubleMap, jetConstant]
    · simp [substitute]
  · simp

private theorem substitute_map {A B C' : Type*} [CommSemiring A] [CommSemiring B]
    [CommSemiring C'] (f : A →+* B) (g : B →+* C') (y v : Polynomial (Polynomial C')) :
    (substitute g y v).comp (doubleMap f) = substitute (g.comp f) y v := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [substitute, doubleMap]
    · simp [substitute, doubleMap]
  · simp [doubleMap]

private def seedMap : SeedPoly →+* Seeds :=
  MvPolynomial.map (algebraMap L FX)

private abbrev ξ : FX := algebraMap L[X] FX (Polynomial.X : L[X])

private def centerBase : SeedPoly[X] →+* Seeds :=
  eval₂RingHom seedMap (MvPolynomial.C ξ)

private theorem centerEval_apply (P : Source) : centerEval P = doubleMap centerBase P := rfl

private def liftSeeds : SeedField →+* CentreField :=
  IsFractionRing.lift (g := (algebraMap Seeds CentreField).comp seedMap)
    ((IsFractionRing.injective Seeds CentreField).comp
      (MvPolynomial.map_injective (algebraMap L FX) (FaithfulSMul.algebraMap_injective L FX)))

private def evalRaw : SeedField[X] →+* CentreField :=
  eval₂RingHom liftSeeds (algebraMap FX CentreField ξ)

private theorem evalRaw_generic :
    evalRaw.comp genericCoefficients.toRingHom = (algebraMap Seeds CentreField).comp centerBase := by
  apply Polynomial.ringHom_ext
  · intro a
    change evalRaw ((C a).map (algebraMap SeedPoly SeedField)) =
      algebraMap Seeds CentreField (centerBase (C a))
    simp [evalRaw, centerBase, liftSeeds]
  · change evalRaw ((Polynomial.X : SeedPoly[X]).map (algebraMap SeedPoly SeedField)) =
      algebraMap Seeds CentreField (centerBase Polynomial.X)
    simp only [Polynomial.map_X, evalRaw, centerBase, coe_eval₂RingHom, eval₂_X]
    rfl

private theorem evalRaw_block {h} (D : PoleData h) :
    evalRaw (rawBlock D) = algebraMap FX CentreField (algebraMap L[X] FX (poleProduct D)) := by
  have he : evalRaw.comp (mapRingHom (algebraMap L SeedField)) =
      (algebraMap FX CentreField).comp (algebraMap L[X] FX) := by
    apply Polynomial.ringHom_ext
    · intro a
      change evalRaw ((C a).map (algebraMap L SeedField)) =
        algebraMap FX CentreField (algebraMap L[X] FX (C a))
      simp only [Polynomial.map_C, evalRaw, coe_eval₂RingHom, eval₂_C]
      change liftSeeds (algebraMap SeedPoly SeedField (MvPolynomial.C a)) = _
      simp only [liftSeeds, IsFractionRing.lift_algebraMap, RingHom.comp_apply, seedMap,
        MvPolynomial.map_C]
      rfl
    · change evalRaw ((Polynomial.X : L[X]).map (algebraMap L SeedField)) =
        algebraMap FX CentreField ξ
      simp [evalRaw]
  exact RingHom.congr_fun he (poleProduct D)

private theorem evalRaw_block_ne_zero {h} (D : PoleData h) : evalRaw (rawBlock D) ≠ 0 := by
  rw [evalRaw_block]
  have hne := ((IsFractionRing.injective L[X] FX).ne ((D.monic 0).mul (D.monic 1)).ne_zero)
  exact (map_ne_zero (algebraMap FX CentreField)).2 (by simpa only [poleProduct, map_zero] using hne)

private def specialized {h} {D : PoleData h} (Crt : CRTLift D) : Jet →ₐ[FX] CentreJet where
  toRingHom := substitute (algebraMap Seeds CentreField)
    (doubleMap evalRaw (rawOrdinate D Crt)) (doubleMap evalRaw (rawVelocity D Crt))
  commutes' x := by
    change substitute _ _ _ (jetConstant (MvPolynomial.C x)) =
      jetConstant (algebraMap FX CentreField x)
    simp [substitute, jetConstant]
    rfl

private theorem specialized_center {h} {D : PoleData h} (Crt : CRTLift D) (P : Source) :
    specialized Crt (centerEval P) = doubleMap evalRaw (forward Crt P) := by
  rw [centerEval_apply, forward_apply]
  change ((substitute _ _ _).comp (doubleMap centerBase)) P =
     ((doubleMap evalRaw).comp (substitute genericCoefficients.toRingHom _ _)) P
  rw [map_substitute, substitute_map, evalRaw_generic]

private def innerEval {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y : B[X]) : A[X] →+* B[X] :=
  eval₂RingHom (C.comp f) y

private theorem innerEval_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y : B[X]) (p : A[X]) :
    innerEval f y p = (p.map f).comp y := by
  change _ = (p.map f).eval₂ C y
  rw [eval₂_map]
  rfl

private theorem substitute_affine {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (y : B[X]) (v : Polynomial B[X]) (P : Polynomial A[X]) :
    substitute f (C y) v P = (P.map (innerEval f y)).comp v := by
  change P.eval₂ (eval₂RingHom ((jetConstant (R := B)).comp f) (C y)) v =
    (P.map (innerEval f y)).eval₂ C v
  rw [eval₂_map]
  congr 1
  apply Polynomial.ringHom_ext <;> simp [innerEval, jetConstant]

private theorem affine_leading {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) {a b : B} (ha : a ≠ 0)
    (c : B[X]) {P : Polynomial A[X]} (hP : P ≠ 0) :
    let Q := substitute f (C (C a * Polynomial.X + C b)) (C (C a) * Polynomial.X + C c) P
    Q.natDegree = P.natDegree ∧ Q.leadingCoeff.natDegree = P.leadingCoeff.natDegree ∧ Q ≠ 0 := by
  let y : B[X] := C a * Polynomial.X + C b
  let v : Polynomial B[X] := C (C a) * Polynomial.X + C c
  let ev := innerEval f y
  have ev_degree (p : A[X]) : (ev p).natDegree = p.natDegree := by
    rw [innerEval_apply, natDegree_comp, natDegree_linear ha, mul_one, natDegree_map_eq_of_injective hf]
  have ev_inj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).mpr
    intro p hp
    by_contra hn
    have hel : (p.map f).leadingCoeff ≠ 0 := by
      apply leadingCoeff_ne_zero.mpr
      intro hz
      apply hn
      exact map_injective f hf (by simpa only [Polynomial.map_zero] using hz)
    have he := leadingCoeff_comp (p := p.map f) (q := y) (by rw [show y.natDegree = 1 from natDegree_linear ha]; decide)
    rw [show (p.map f).comp y = ev p from (innerEval_apply f y p).symm, hp,
      leadingCoeff_zero, leadingCoeff_linear ha] at he
    exact (mul_ne_zero hel (pow_ne_zero _ ha)) he.symm
  have ha' : (C a : B[X]) ≠ 0 := C_ne_zero.mpr ha
  have hv : v.natDegree = 1 := natDegree_linear ha'
  have hlead : ((P.map ev).comp v).leadingCoeff = ev P.leadingCoeff * C (a^P.natDegree) := by
    rw [leadingCoeff_comp (by rw [hv]; decide), leadingCoeff_linear ha',
      leadingCoeff_map_of_injective ev_inj, natDegree_map_eq_of_injective ev_inj, map_pow]
  change (substitute f (C y) v P).natDegree = _ ∧
    (substitute f (C y) v P).leadingCoeff.natDegree = _ ∧ substitute f (C y) v P ≠ 0
  rw [substitute_affine, natDegree_comp, hv, mul_one, natDegree_map_eq_of_injective ev_inj,
    hlead, natDegree_mul_C (pow_ne_zero _ ha), ev_degree]
  refine ⟨rfl, rfl, leadingCoeff_ne_zero.mp ?_⟩
  rw [hlead]
  apply mul_ne_zero _ (C_ne_zero.mpr (pow_ne_zero _ ha))
  simpa only [map_zero] using ev_inj.ne (leadingCoeff_ne_zero.mpr hP)

private theorem specialized_leading {h} {D : PoleData h} (Crt : CRTLift D) {P : Jet}
    (hP : P ≠ 0) :
    (specialized Crt P).natDegree = P.natDegree ∧
    (specialized Crt P).leadingCoeff.natDegree = P.leadingCoeff.natDegree ∧ specialized Crt P ≠ 0 := by
  let a := evalRaw (rawBlock D)
  let b := evalRaw (crtPolynomial Crt)
  let c : CentreField[X] := C (evalRaw (rawBlock D).derivative) * Polynomial.X +
    C (evalRaw (crtPolynomial Crt).derivative)
  have heY : doubleMap evalRaw (rawOrdinate D Crt) = C (C a * Polynomial.X + C b) := by
    simp [rawOrdinate, jetConstant, doubleMap, a, b]
  have heV : doubleMap evalRaw (rawVelocity D Crt) = C (C a) * Polynomial.X + C c := by
    simp [rawVelocity, jetConstant, doubleMap, a, c, map_add, map_mul, add_assoc]
  change (substitute _ _ _ P).natDegree = _ ∧ (substitute _ _ _ P).leadingCoeff.natDegree = _ ∧
    substitute _ _ _ P ≠ 0
  rw [heY, heV]
  exact affine_leading _ (IsFractionRing.injective Seeds CentreField) (evalRaw_block_ne_zero D) c hP

private def rawPosition {h} {D : PoleData h} (Crt : CRTLift D) (j i : ℕ) : Jet →ₗ[FX] CentreField where
  toFun P := ((specialized Crt P).coeff j).coeff i
  map_add' P Q := by simp
  map_smul' b P := by simp [Polynomial.coeff_smul]

private theorem rawPosition_zero {h} (hpos : 0 < h) (hh : h ≤ 32970) {D : PoleData h} (Crt : CRTLift D)
    (word : I → L) {s W P} (hP : P ∈ evaluated Crt word s W) (j i : ℕ)
    (hw : W < (131071-h)*i+(131071-h-1)*j) : rawPosition Crt j i P = 0 := by
  have hsub : evaluated Crt word s W ≤ LinearMap.ker (rawPosition Crt j i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    apply LinearMap.mem_ker.mpr
    rcases hA.2 with ⟨Q, hQ⟩
    have hz := quotient_positions s W (forward_bounded hpos hh Crt hA.1.1) hQ j i hw
    change ((specialized Crt (centerEval A)).coeff j).coeff i = 0
    rw [specialized_center, hQ]
    simp only [map_mul, doubleMap, coe_mapRingHom, Polynomial.map_C, jetConstant,
      RingHom.comp_apply, coeff_C_mul, coeff_map, hz, map_zero, mul_zero]
  exact LinearMap.mem_ker.mp (hsub hP)

theorem proof : LeadingWeight := by
  intro h hl hh D Crt word s W P hP hn
  let j := P.natDegree
  let i := P.leadingCoeff.natDegree
  change (i+j)*(131071-h) ≤ W+j
  have huv : 131071-h = (131071-h-1)+1 := by omega
  have he : (i+j)*(131071-h) = (131071-h)*i+(131071-h-1)*j+j := by
    have hj : j*(131071-h) = (131071-h-1)*j+j := by
      calc
        j*(131071-h) = j*((131071-h-1)+1) := congrArg (j*·) huv
        _ = (131071-h-1)*j+j := by ring
    rw [Nat.add_mul, hj, Nat.mul_comm i]
    omega
  rw [he]
  by_contra! hw
  have hz := rawPosition_zero (by omega) hh Crt word hP j i (by omega)
  obtain ⟨hj, hi, hn'⟩ := specialized_leading Crt hn
  change ((specialized Crt P).coeff j).coeff i = 0 at hz
  have hj' : (specialized Crt P).natDegree = j := hj
  have hi' : (specialized Crt P).leadingCoeff.natDegree = i := hi
  rw [← hj', coeff_natDegree, ← hi', coeff_natDegree] at hz
  exact (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn')) hz

end
end HighSource6921.Weight
end PackSource_K1_14_1_4Proof

section PackSource_K1_14_1_5Proof
set_option autoImplicit true
namespace HighSource6921.Ambient

noncomputable section

open K1_14 K1_14_1
open scoped BigOperators

/-- Number of nonnegative X exponents satisfying the inclusive true cutoff. -/
private def trueWidth (h : ℕ) (s : Shape) (W q j : ℕ) : ℕ :=
  W + (s.B + s.J) * (2 * h) + j + 1 - q * (131071 + h)

private theorem lt_trueWidth_iff (h : ℕ) (s : Shape) (W q j a : ℕ) :
    a < trueWidth h s W q j ↔
      a + q * (131071 + h) ≤ W + (s.B + s.J) * (2 * h) + j := by
  unfold trueWidth
  omega

private abbrev SeedIndex (U : ℕ) := Σ t : Fin (U + 1), Fin (t.val + 1)

private def seedExponent {U : ℕ} (b : SeedIndex U) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![b.1.val - b.2.val, b.2.val]

private theorem seedExponent_zero {U : ℕ} (b : SeedIndex U) :
    seedExponent b 0 = b.1.val - b.2.val := by
  simp [seedExponent]

private theorem seedExponent_one {U : ℕ} (b : SeedIndex U) :
    seedExponent b 1 = b.2.val := by
  simp [seedExponent]

private theorem seedWeight_eq (e : Fin 2 →₀ ℕ) : seedWeight e = e 0 + e 1 := by
  unfold seedWeight
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]

private theorem seedWeight_seedExponent {U : ℕ} (b : SeedIndex U) :
    seedWeight (seedExponent b) = b.1.val := by
  rw [seedWeight_eq, seedExponent_zero, seedExponent_one]
  have := b.2.isLt
  omega

private theorem seedExponent_injective (U : ℕ) :
    Function.Injective (seedExponent (U := U)) := by
  rintro ⟨t, b⟩ ⟨t', b'⟩ he
  have ht := congrArg seedWeight he
  simp only [seedWeight_seedExponent] at ht
  have htotal : t = t' := Fin.ext ht
  subst t'
  have hb := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
  simp only [seedExponent_one] at hb
  have hlast : b = b' := Fin.ext hb
  subst b'
  rfl

private theorem exists_seedIndex {U : ℕ} (e : Fin 2 →₀ ℕ) (he : seedWeight e ≤ U) :
    ∃ b : SeedIndex U, seedExponent b = e := by
  let t : Fin (U + 1) := ⟨seedWeight e, by omega⟩
  have ht : t.val = e 0 + e 1 := seedWeight_eq e
  let b : Fin (t.val + 1) := ⟨e 1, by omega⟩
  refine ⟨⟨t, b⟩, Finsupp.ext fun k => ?_⟩
  fin_cases k
  · change seedExponent (⟨t, b⟩ : SeedIndex U) 0 = e 0
    rw [seedExponent_zero]
    change t.val - e 1 = e 0
    omega
  · exact seedExponent_one ⟨t, b⟩

private theorem card_seedIndex (U : ℕ) : Fintype.card (SeedIndex U) = triangle U := by
  simp only [SeedIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => t + 1)]
  have hsum := Finset.sum_range_succ' (fun t : ℕ => t) (U + 1)
  simp only [add_zero] at hsum
  rw [← hsum]
  simp [Finset.sum_range_id, triangle, Nat.mul_comm]

private abbrev MonomialIndex (h : ℕ) (s : Shape) (W : ℕ) :=
  Σ q : Fin (s.B + 1), Σ j : Fin (min q.val s.J + 1),
    Fin (trueWidth h s W q.val j.val) × SeedIndex s.U

private abbrev Exponents := ℕ × ℕ × ℕ × (Fin 2 →₀ ℕ)

private def exponents {h : ℕ} {s : Shape} {W : ℕ} (k : MonomialIndex h s W) : Exponents :=
  ⟨k.2.1.val, k.1.val - k.2.1.val, k.2.2.1.val, seedExponent k.2.2.2⟩

private theorem exponents_eligible {h : ℕ} {s : Shape} {W : ℕ} (k : MonomialIndex h s W) :
    trueEligible h s W (exponents k).1 (exponents k).2.1 (exponents k).2.2.1
      (exponents k).2.2.2 := by
  rcases k with ⟨q, j, a, b⟩
  have hq := q.isLt
  have hj := j.isLt
  have hjq := Nat.min_le_left q.val s.J
  have hjJ := Nat.min_le_right q.val s.J
  have hgrade : q.val - j.val + j.val = q.val := by omega
  have hb := b.1.isLt
  simp only [exponents, trueEligible, hgrade, seedWeight_seedExponent]
  exact ⟨by omega, by omega, by omega, (lt_trueWidth_iff h s W _ _ _).mp a.isLt⟩

private theorem exists_monomialIndex {h : ℕ} {s : Shape} {W j i a : ℕ} {e : Fin 2 →₀ ℕ}
    (hel : trueEligible h s W j i a e) :
    ∃ k : MonomialIndex h s W, exponents k = (j, i, a, e) := by
  obtain ⟨hq, hj, he, ha⟩ := hel
  obtain ⟨b, hb⟩ := exists_seedIndex e he
  let q : Fin (s.B + 1) := ⟨i + j, by omega⟩
  let v : Fin (min q.val s.J + 1) := ⟨j, by
    have h : j ≤ min (i + j) s.J := le_min (by omega) hj
    exact Nat.lt_succ_of_le h⟩
  let x : Fin (trueWidth h s W q.val v.val) :=
    ⟨a, (lt_trueWidth_iff h s W _ _ _).mpr ha⟩
  refine ⟨⟨q, v, x, b⟩, ?_⟩
  simp [exponents, q, v, x, hb]

private theorem exponents_injective (h : ℕ) (s : Shape) (W : ℕ) :
    Function.Injective (exponents (h := h) (s := s) (W := W)) := by
  rintro ⟨q, j, a, b⟩ ⟨q', j', a', b'⟩ he
  have hj := congrArg (fun p : Exponents => p.1) he
  have hi := congrArg (fun p : Exponents => p.2.1) he
  change j.val = j'.val at hj
  change q.val - j.val = q'.val - j'.val at hi
  have hlt := j.isLt
  have hlt' := j'.isLt
  have hmin := Nat.min_le_left q.val s.J
  have hmin' := Nat.min_le_left q'.val s.J
  have hq : q = q' := Fin.ext (by omega)
  subst q'
  have hv : j = j' := Fin.ext hj
  subst j'
  have hx : a = a' := Fin.ext (congrArg (fun p : Exponents => p.2.2.1) he)
  subst a'
  have hb : b = b' := seedExponent_injective s.U (congrArg (fun p : Exponents => p.2.2.2) he)
  subst b'
  rfl

private def monomialAt (k : Exponents) : Source :=
  Polynomial.monomial k.1 (Polynomial.monomial k.2.1
    (Polynomial.monomial k.2.2.1 (MvPolynomial.monomial k.2.2.2 1)))

private theorem coeffAt_monomialAt (k d : Exponents) :
    coeffAt (monomialAt k) d.1 d.2.1 d.2.2.1 d.2.2.2 = if k = d then 1 else 0 := by
  classical
  rcases k with ⟨j, i, a, e⟩
  rcases d with ⟨j', i', a', e'⟩
  by_cases hj : j = j'
  · subst j'
    by_cases hi : i = i'
    · subst i'
      by_cases ha : a = a'
      · subst a'
        simp [coeffAt, monomialAt]
      · simp [coeffAt, monomialAt, Polynomial.coeff_monomial, ha]
    · simp [coeffAt, monomialAt, Polynomial.coeff_monomial, hi]
  · simp [coeffAt, monomialAt, Polynomial.coeff_monomial, hj]

private def ambientMonomial {h : ℕ} {s : Shape} {W : ℕ} (k : MonomialIndex h s W) :
    ambient h s W := by
  refine ⟨monomialAt (exponents k), ?_⟩
  intro j i a e hbad
  rw [coeffAt_monomialAt (exponents k) (j, i, a, e), ite_eq_right]
  intro he
  apply hbad
  simpa only [he] using exponents_eligible k

private def coordinates (h : ℕ) (s : Shape) (W : ℕ) :
    ambient h s W →ₗ[L] (MonomialIndex h s W → L) where
  toFun P k := coeffAt P (exponents k).1 (exponents k).2.1 (exponents k).2.2.1 (exponents k).2.2.2
  map_add' P Q := by
    funext k
    simp [coeffAt]
  map_smul' b P := by
    funext k
    simp [coeffAt, Polynomial.coeff_smul]

private theorem coordinates_monomial {h : ℕ} {s : Shape} {W : ℕ} (k d : MonomialIndex h s W) :
    coordinates h s W (ambientMonomial k) d = if k = d then 1 else 0 := by
  classical
  change coeffAt (monomialAt (exponents k)) (exponents d).1 (exponents d).2.1
    (exponents d).2.2.1 (exponents d).2.2.2 = _
  simp only [coeffAt_monomialAt, (exponents_injective h s W).eq_iff]

private def coordinateEquiv (h : ℕ) (s : Shape) (W : ℕ) :
    ambient h s W ≃ₗ[L] (MonomialIndex h s W → L) := by
  classical
  refine LinearEquiv.ofBijective (coordinates h s W) ⟨?_, ?_⟩
  · intro P Q hPQ
    apply Subtype.ext
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    apply MvPolynomial.ext
    intro e
    change coeffAt P j i a e = coeffAt Q j i a e
    by_cases he : trueEligible h s W j i a e
    · obtain ⟨k, hk⟩ := exists_monomialIndex he
      have hcoeff := congrFun hPQ k
      change coeffAt P (exponents k).1 (exponents k).2.1 (exponents k).2.2.1
          (exponents k).2.2.2 =
        coeffAt Q (exponents k).1 (exponents k).2.1 (exponents k).2.2.1
          (exponents k).2.2.2 at hcoeff
      simpa only [hk] using hcoeff
    · exact (P.property j i a e he).trans (Q.property j i a e he).symm
  · intro f
    refine ⟨∑ k, f k • ambientMonomial k, ?_⟩
    funext d
    rw [map_sum]
    simp [Finset.sum_apply, coordinates_monomial, mul_ite]

/-- True ambient dimension at an inclusive cutoff, with a separate seed cap. -/
private theorem finrank_ambient (h : ℕ) (s : Shape) (W : ℕ) :
    Module.finrank L (ambient h s W) = triangle s.U * shapeSum s (trueWidth h s W) := by
  rw [(coordinateEquiv h s W).finrank_eq, Module.finrank_pi]
  unfold MonomialIndex
  rw [Fintype.card_sigma]
  calc
    _ = ∑ q : Fin (s.B + 1), ∑ j : Fin (min q.val s.J + 1),
        triangle s.U * trueWidth h s W q j := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.card_prod, Fintype.card_fin, card_seedIndex, Nat.mul_comm]
    _ = _ := by
      unfold shapeSum
      simp only [Finset.mul_sum]
      rw [Fin.sum_univ_eq_sum_range (fun q => ∑ j : Fin (min q s.J + 1),
        triangle s.U * trueWidth h s W q j)]
      apply Finset.sum_congr rfl
      intro q _
      exact Fin.sum_univ_eq_sum_range (fun j => triangle s.U * trueWidth h s W q j)
        (min q s.J + 1)

private theorem trueWidth_eq_add {h : ℕ} {s : Shape} {W q j : ℕ} (hh : h ≤ 131071)
    (hw : rawWidthCond h s W) (hq : q ≤ s.B) (hj : j ≤ min q s.J) :
    trueWidth h s W q j = W + 1 + j - q * (131071 - h) + 2 * h * (s.B + s.J - q) := by
  have hdegree : 131071 + h = (131071 - h) + 2 * h := by omega
  have hcredit : q * (2 * h) + (s.B + s.J - q) * (2 * h) = (s.B + s.J) * (2 * h) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hraw := hw q hq j hj
  rw [trueWidth, hdegree, Nat.mul_add, Nat.mul_comm (2 * h) (s.B + s.J - q)]
  omega

theorem proof : AmbientRank := by
  intro h _ hhi s W hw
  rw [finrank_ambient]
  have hsum : shapeSum s (trueWidth h s W) =
      shapeSum s (fun q j => W + 1 + j - q * (131071 - h)) +
        2 * h * shapeSum s (fun q _ => s.B + s.J - q) := by
    unfold shapeSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    exact trueWidth_eq_add (by omega) hw (by simpa using hq) (by simpa using hj)
  simp only [hsum, rawVolumeAt, poleCredit, Nat.mul_add, Nat.mul_assoc, Nat.le_refl]

end
end HighSource6921.Ambient
end PackSource_K1_14_1_5Proof

section PackSource_K1_14_1_7_3Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace HighSource6921.Deform

noncomputable section

open K1 K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_3 Polynomial
open scoped BigOperators Polynomial

private abbrev G := GenericField
private abbrev F := SeedFrac G
private abbrev g : Parameter →+* G := K1_14_1_7.genericPoint
private abbrev inc : G →+* F := algebraMap G F

private theorem generic_den {d : Seed Parameter} (hd : specialSeed d ≠ 0) :
    MvPolynomial.map g d ≠ 0 :=
  fun hz => hd (by
    rw [(MvPolynomial.map_injective g generic_injective)
      (hz.trans (map_zero (MvPolynomial.map g)).symm), map_zero])

private theorem generic_centre {h : ℕ} {D : PoleData h} {Crt : CRTLift D}
    (B : ∀ i, BlockLift D Crt i) (i : Fin 2) (α : G)
    (hr : (genericBlock D i).eval α = 0) (hb : ((D.constant i).map constGeneric).eval α ≠ 0) :
    (∑ j, liftAt g (B j).num (B j).den).eval (inc α) =
      residue i (-((D.offset i).map constGeneric).eval α)
        (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α) := by
  let ev := eval₂RingHom (seedEmbed g) (inc α)
  let z := algebraMap (Seed G) F (MvPolynomial.X i)
  let b := ((D.constant i).map constGeneric).eval α
  let c := ((D.slope i).map constGeneric).eval α
  let a := ((D.offset i).map constGeneric).eval α
  have hcomp : (seedEmbed g).comp MvPolynomial.C = inc.comp g := by
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, seedEmbed, MvPolynomial.map_C]
    rw [IsScalarTower.algebraMap_apply G (Seed G) F, MvPolynomial.algebraMap_eq]
  have hparam (P : Parameter[X]) :
      ev (P.map MvPolynomial.C) = inc ((P.map g).eval α) := by
    change (P.map MvPolynomial.C).eval₂ (seedEmbed g) (inc α) = _
    rw [← eval_map, map_map, hcomp, ← map_map, eval_map_apply]
  have hL (P : L[X]) : ev (P.map constSeed) = inc ((P.map constGeneric).eval α) := by
    rw [constSeed, ← map_map, hparam, map_map]
  have hC (x : Seed Parameter) : ev (C x) = seedEmbed g x := eval₂_C _ _
  have hX : ev (C (MvPolynomial.X i)) = z := by rw [hC]; simp [seedEmbed, z]
  have hA : ev (familyAmplitude D i) = inc b + z * inc c := by
    rw [familyAmplitude, map_add, map_mul, hL, hL]
    exact congrArg (fun x => inc b + x * inc c) hX
  have hQ : ev (familyOffset D i) = z * inc a := by
    rw [familyOffset, map_mul, hL]
    exact congrArg (fun x => x * inc a) hX
  have hne : inc b + z * inc c ≠ 0 := by
    have hf : (MvPolynomial.C b + MvPolynomial.X i * MvPolynomial.C c : Seed G) ≠ 0 := by
      intro he
      have hv := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : G))) he
      exact hb (by simpa [b] using hv)
    have he : algebraMap (Seed G) F (MvPolynomial.C b + MvPolynomial.X i * MvPolynomial.C c) ≠ 0 :=
      fun hz => hf ((IsFractionRing.injective (Seed G) F)
        (hz.trans (map_zero (algebraMap (Seed G) F)).symm))
    have hinc (x : G) : algebraMap (Seed G) F (MvPolynomial.C x) = inc x :=
      (IsScalarTower.algebraMap_apply G (Seed G) F x).symm
    simpa only [map_add, map_mul, z, hinc] using he
  have hzero : ev (familyBlock D i) = 0 := by rw [familyBlock, hparam, hr, map_zero]
  have hnot : ev (B (otherBlock i)).num = 0 := by
    have he := map_dvd ev (B (otherBlock i)).other_dvd
    rw [other_invol, hzero, zero_dvd_iff] at he
    exact he
  have hval (j : Fin 2) : (liftAt g (B j).num (B j).den).eval (inc α) =
      (seedEmbed g (B j).den)⁻¹ * ev (B j).num := by
    rw [liftAt, smul_eq_C_mul, eval_mul, eval_C, eval_map]
    rfl
  have he := map_dvd ev (B i).congruence
  rw [hzero, zero_dvd_iff, map_add, map_mul, map_mul, hA, hQ, hC] at he
  have hd := seedEmbed_ne_zero g (generic_den (B i).specialDen)
  rw [sum_other _ i, eval_add, hval, hval, hnot, mul_zero, add_zero]
  unfold residue
  change _ = inc (-a) * z / (inc b + inc c * z)
  rw [mul_comm (inc c) z, map_neg]
  apply (eq_div_iff hne).mpr
  calc
    _ = (seedEmbed g (B i).den)⁻¹ * ((inc b + z * inc c) * ev (B i).num) := by ring
    _ = -inc a * z := by
      rw [eq_neg_of_add_eq_zero_left he, mul_neg, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
      ring

theorem proof (h : ℕ) (hlo : 2442 ≤ h) (hhi : h ≤ 32970)
    (D : PoleData h) (Crt : CRTLift D) : Nonempty (RegularDeformation D Crt) := by
  have hh : 0 < h := by omega
  have hp : h < K1.p := by change h < 2130706433; omega
  let B : ∀ i, BlockLift D Crt i := blockLift hh D Crt
  let den := (B 0).den * (B 1).den
  let num := C (B 1).den * (B 0).num + C (B 0).den * (B 1).num
  have hden : specialSeed den ≠ 0 := by
    dsimp only [den]
    rw [map_mul]
    exact mul_ne_zero (B 0).specialDen (B 1).specialDen
  have hmonic : (movingProduct D).Monic :=
    (movingBlock_degree hh D 0).monic.mul (movingBlock_degree hh D 1).monic
  refine ⟨⟨movingProduct D, num, den, hmonic, ?_, hden, ?_, generic_den hden, ?_⟩⟩
  · rw [movingProduct, Polynomial.map_mul, movingBlock_spec, movingBlock_spec, poleProduct]
  · dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift, (B 1).specialLift, crtPolynomial, Fin.sum_univ_two]
  · apply simplePoles hh hp D _
    intro i α hr hb
    dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (generic_den (B 0).specialDen) (generic_den (B 1).specialDen)]
    simpa only [Fin.sum_univ_two] using generic_centre B i α hr hb

end
end HighSource6921.Deform
end PackSource_K1_14_1_7_3Proof

section PackSource_K1_14_1_7Split
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace HighSource6921.Pole

noncomputable section

open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial

private theorem poleTest_of_local {F : Type} [Field F] (s : Shape) {h : ℕ}
    {H : F[X]} {lift : (SeedFrac F)[X]} (G : SimplePoles h H lift)
    (P : TrueSource F)
    (hd : ∀ t, (jetConstant ((Polynomial.X (R := SeedFrac F) -
        Polynomial.C (algebraMap F (SeedFrac F) (G.root t))) ^ (s.B+s.J)) :
      JetPolys (SeedFrac F)) ∣ forward H lift P) :
    PoleTest s H lift P := by
  let r : Fin (2*h) → (SeedFrac F)[X] := fun t =>
    Polynomial.X - Polynomial.C (algebraMap F (SeedFrac F) (G.root t))
  have hr : Pairwise (Function.onFun IsCoprime r) :=
    Polynomial.pairwise_coprime_X_sub_C
      ((algebraMap F (SeedFrac F)).injective.comp G.distinct)
  have hcop : Pairwise (Function.onFun IsCoprime
      (fun t => (jetConstant (r t ^ (s.B+s.J)) : JetPolys (SeedFrac F)))) := by
    intro t u hne
    exact ((hr hne).pow).map jetConstant
  have hp := Fintype.prod_dvd_of_coprime hcop hd
  have hprod : H.map (algebraMap F (SeedFrac F)) = ∏ t, r t := by
    rw [G.factorization, Polynomial.map_prod]
    simp [r]
  unfold PoleTest
  rw [hprod, ← Finset.prod_pow, map_prod]
  exact hp

private abbrev ScalarRow (h : ℕ) (s : Shape) :=
  Σ _ : Fin (2*h), Σ q : Grade s,
    LocalRow s q.val × Fin (triangle s.U + (s.U+1)*(s.B-q.val))

private theorem shapeSum_fin (s : Shape) (g : ℕ → ℕ → ℕ) :
    shapeSum s g = ∑ q : Grade s, ∑ j : GradeSlot s q.val, g q.val j.val := by
  unfold shapeSum
  rw [← Fin.sum_univ_eq_sum_range (fun q : ℕ =>
    ∑ j ∈ Finset.range (min q s.J + 1), g q j)]
  apply Finset.sum_congr rfl
  intro q _
  exact (Fin.sum_univ_eq_sum_range (g q.val) (min q.val s.J + 1)).symm

private theorem scalarRow_card (h : ℕ) (s : Shape) :
    Fintype.card (ScalarRow h s) = poleCredit h s + poleSeedDebit h s := by
  let a : Grade s → ℕ := fun q => s.B+s.J-q.val
  let b : Grade s → ℕ := fun q => s.B-q.val
  let j : Grade s → ℕ := fun q => min q.val s.J + 1
  change Fintype.card (ScalarRow h s) = _
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (2*h) * (∑ q : Grade s, (a q * j q) * (triangle s.U + (s.U+1)*b q)) = _
  have hterm (q : Grade s) :
      (a q * j q) * (triangle s.U + (s.U+1)*b q) =
      triangle s.U * (∑ _ : GradeSlot s q.val, a q) +
        (s.U+1) * (∑ _ : GradeSlot s q.val, a q * b q) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change _ = triangle s.U * (j q * a q) + (s.U+1) * (j q * (a q * b q))
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold poleCredit poleSeedDebit
  rw [shapeSum_fin, shapeSum_fin]
  dsimp only [a, b]
  ring

private theorem simple_rank_le (h1 : K1_14_1_7.c1) (h2 : K1_14_1_7.c2)
    {F ι : Type} [Field F] [Fintype ι] {h : ℕ} {H : F[X]} {lift : (SeedFrac F)[X]}
    (G : SimplePoles h H lift) (s : Shape) (P : ι → TrueSource F)
    (hP : ∀ k, Shaped s (P k)) {n : ℕ} (M : Matrix (Fin n) ι F)
    (hM : ∀ v, M.mulVec v = 0 ↔ PoleTest s H lift (Fintype.linearCombination F P v)) :
    M.rank ≤ poleCredit h s + poleSeedDebit h s := by
  classical
  choose rows hrows using h1 F s
  have hlocal (t) := h2 F s H lift (G.root t) (G.side t) (G.a t) (G.b t) (G.c t)
    (G.vanishes t) (G.simple t) (G.b_ne t) (G.centre t) rows hrows
  choose tests hwindow htest using hlocal
  have hread (t : Fin (2*h)) (q : Grade s) := seedWindow_read F s.U (s.B-q.val) (G.side t)
  choose read hread using hread
  let f : (ι → F) →ₗ[F] (ScalarRow h s → F) :=
    LinearMap.pi fun r =>
      ((LinearMap.proj r.2.2.2).comp (read r.1 r.2.1)).comp
        ((tests r.1 r.2.1 r.2.2.1).comp (Fintype.linearCombination F P))
  have hker : LinearMap.ker f ≤ LinearMap.ker M.mulVecLin := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply poleTest_of_local s G
    intro t
    have hv' := shaped_combination hP v
    apply htest t _ hv'
    intro q r
    apply hread t q _ (hwindow t q r _ hv')
    funext k
    exact congrFun (LinearMap.mem_ker.mp hv) ⟨t, q, r, k⟩
  have hn := Submodule.finrank_mono hker
  have hr : Module.finrank F (LinearMap.range f) ≤ poleCredit h s + poleSeedDebit h s := by
    have hr := (LinearMap.range f).finrank_le
    rwa [Module.finrank_pi, scalarRow_card] at hr
  have hf := f.finrank_range_add_finrank_ker
  have hm := M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega

theorem proof : PoleRank := by
  classical
  intro h hlo hhi D Crt word s W
  obtain ⟨E⟩ := Deform.proof h hlo hhi D Crt
  have h1 := K1_14_1_7_1.proof
  have h2 := K1_14_1_7_2.of_children K1_14_1_7_2_1.proof K1_14_1_7_2_2.proof
  have h4 : K1_14_1_7.c4 := @K1_14_1_7_4.proof
  let A := contacted h word s W
  let _ : Module.Finite L A := contacted_finite h word s W
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source := fun k => basis k
  have hP (k : Fin d) : Shaped s (P k) := contacted_shaped (basis k).property
  obtain ⟨n, M, hs, hg⟩ := h4 E s (Fin d) P hP
  have hgen := simple_rank_le h1 h2 E.genericPoles s _
    (fun k => shaped_map (genericPoint.comp (Polynomial.C (R := L))) (hP k)) _ hg
  have hrank := (specialization_rank_le M).trans hgen
  let f := (M.map specialPoint).mulVecLin
  have hf : ∀ v : Fin d → L,
      Fintype.linearCombination L P v = ((basis.equivFun.symm v : A) : Source) := by
    intro v
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul, Submodule.subtype_apply, P] using
      map_sum A.subtype (fun k => v k • basis k) Finset.univ
  have hk (v : LinearMap.ker f) :
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source) ∈ complete Crt word s W := by
    have hv := (hs v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property, hv⟩
  let g : LinearMap.ker f →ₗ[L] complete Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  let _ : Module.Finite L (complete Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : complete Crt word s W => (x : Source)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ _
  omega

end
end HighSource6921.Pole
end PackSource_K1_14_1_7Split

section PackSource_K1_14_1_8Base
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16

namespace HighSource6921.Telescope

noncomputable section

open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial BigOperators

/-- The leading coefficient after an affine change of the polynomial variable. -/
private theorem affine_coeff {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : S) (P : R[X]) :
    (P.eval₂ (C.comp f) (C a * (Polynomial.X (R := S)) + C b)).coeff P.natDegree =
      f P.leadingCoeff * a ^ P.natDegree := by
  let Q : S[X] := C a * (Polynomial.X (R := S)) + C b
  change (P.eval₂ (C.comp f) Q).coeff P.natDegree = _
  have hQ : Q.natDegree ≤ 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    simp [Q, coeff_C_mul, coeff_X, coeff_C, show 1 ≠ k by omega, show k ≠ 0 by omega]
  rw [eval₂_eq_sum_range, Polynomial.finsetSum_coeff, Finset.sum_range_succ]
  have hz : ∑ k ∈ Finset.range P.natDegree,
      (C (f (P.coeff k)) * Q ^ k).coeff P.natDegree = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply coeff_eq_zero_of_natDegree_lt
    refine natDegree_mul_le.trans_lt ?_
    simp only [natDegree_C, zero_add]
    exact natDegree_pow_le.trans_lt
      ((Nat.mul_le_mul_left k hQ).trans_lt (by simpa using Finset.mem_range.mp hk))
  simp only [RingHom.comp_apply] at ⊢
  rw [hz, zero_add, coeff_C_mul, coeff_natDegree]
  have hp := coeff_pow_of_natDegree_le (m := P.natDegree) hQ
  simpa [Q, coeff_C_mul, coeff_C] using congrArg (f P.leadingCoeff * ·) hp

private theorem leading_forward {h} {D : PoleData h} (Crt : CRTLift D) (P : Source) :
    let j := P.natDegree
    let i := P.leadingCoeff.natDegree
    ((forward Crt P).coeff j).coeff i =
      genericCoefficients P.leadingCoeff.leadingCoeff * rawBlock D ^ (i+j) := by
  let H := rawBlock D
  let A := crtPolynomial Crt
  let x := Polynomial.X (R := SeedField[X])
  let y : (SeedField[X])[X] := C H * x + C A
  let v₀ : (SeedField[X])[X] := C H.derivative * x + C A.derivative
  let f : SeedPoly[X] →+* (SeedField[X])[X] := C.comp genericCoefficients.toRingHom
  let g := eval₂RingHom f y
  let c : SeedField[X] →+* RawSource := jetConstant
  let g' : Polynomial (SeedPoly[X]) →+* RawSource :=
    eval₂RingHom (R := SeedPoly[X]) (S := RawSource)
      ((Polynomial.C (R := (SeedField[X])[X])).comp f)
      (c H * C x + c A)
  change ((P.eval₂ g' (c H * Polynomial.X + c H.derivative * C x + c A.derivative)).coeff
    P.natDegree).coeff P.leadingCoeff.natDegree = _
  have hg : g' = C.comp g := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [g', g, eval₂_C]
    · simp only [g', g, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
      simp [c, jetConstant, y, map_add, map_mul]
  have hv : c H * Polynomial.X + c H.derivative * C x + c A.derivative =
      C (C H) * Polynomial.X + C v₀ := by
    rw [add_assoc]
    simp [c, jetConstant, v₀, map_add, map_mul]
  rw [hg, hv, affine_coeff g]
  change ((P.leadingCoeff.eval₂ f y) * C H ^ P.natDegree).coeff
    P.leadingCoeff.natDegree = _
  rw [← C_pow, coeff_mul_C]
  unfold f y x
  rw [affine_coeff genericCoefficients.toRingHom]
  simp [H, pow_add, mul_assoc]

/-- The signed cutoff immediately before zero has no nonzero complete row. -/
theorem zero_of_strict_cutoff {h} (hhi : h ≤ 32970) {D : PoleData h}
    (Crt : CRTLift D) (s : Shape) (P : Source) (hp : P ∈ poleSpace Crt s)
    (hs : ∀ j i a e, coeffAt P j i a e ≠ 0 →
      a+(i+j)*(131071+h) < (s.B+s.J)*(2*h)+j) : P = 0 := by
  by_contra hP
  let j := P.natDegree
  let i := P.leadingCoeff.natDegree
  let g := P.leadingCoeff.leadingCoeff
  have hg : g ≠ 0 := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  obtain ⟨e, he⟩ : ∃ e, g.leadingCoeff.coeff e ≠ 0 := by
    by_contra! hh
    exact (leadingCoeff_ne_zero.mpr hg) (MvPolynomial.eq_zero_iff.mpr hh)
  have hcoeff : coeffAt P j i g.natDegree e ≠ 0 := by
    simpa [coeffAt, j, i, g, coeff_natDegree] using he
  have hlt := hs j i g.natDegree e hcoeff
  let H := rawBlock D
  have hm : H.Monic := ((D.monic 0).mul (D.monic 1)).map _
  have hd : H.natDegree = 2*h := by
    unfold H rawBlock poleProduct
    rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective (algebraMap L SeedField)),
      natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero, D.degree, D.degree]
    omega
  have hinj : Function.Injective (algebraMap SeedPoly SeedField) :=
    IsFractionRing.injective SeedPoly SeedField
  have hg' : genericCoefficients g ≠ 0 := Polynomial.map_ne_zero_iff hinj |>.2 hg
  have hdeg : (genericCoefficients g).natDegree = g.natDegree := Polynomial.natDegree_map_eq_of_injective hinj g
  obtain ⟨Q, hQ⟩ := hp
  have hdvd : H^(s.B+s.J) ∣ genericCoefficients g * H^(i+j) := by
    refine ⟨(Q.coeff j).coeff i, ?_⟩
    have hc := congrArg (fun R : RawSource => (R.coeff j).coeff i) hQ
    change ((forward Crt P).coeff j).coeff i = _ at hc
    have hlead := leading_forward Crt P
    dsimp only at hlead
    rw [show j = P.natDegree from rfl, show i = P.leadingCoeff.natDegree from rfl, hlead] at hc
    simpa only [jetConstant, RingHom.comp_apply, coeff_C_mul, H, i, j, g] using hc
  have hlo := natDegree_le_of_dvd hdvd (mul_ne_zero hg' (pow_ne_zero _ hm.ne_zero))
  rw [natDegree_mul hg' (pow_ne_zero _ hm.ne_zero), hdeg, natDegree_pow, natDegree_pow, hd] at hlo
  have hweights : (i+j)*(131071+h) = (i+j)*(2*h) + (i+j)*(131071-h) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hj : j ≤ (i+j)*(131071-h) := (Nat.le_add_left j i).trans
    (by simpa using Nat.mul_le_mul_left (i+j) (show 1 ≤ 131071-h by omega))
  rw [hweights] at hlt
  omega

end
end HighSource6921.Telescope
end PackSource_K1_14_1_8Base

section PackSource_K1_14_1_8Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16

namespace HighSource6921.Telescope

noncomputable section

open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial BigOperators nonZeroDivisors

private abbrev Position := ℕ × ℕ × (Fin 2 →₀ ℕ)

private def scalarPoly (e : Fin 2 →₀ ℕ) (g : SeedPoly[X]) : L[X] :=
  ⟨⟨g.toFinsupp.coeff.mapRange (fun p => p.coeff e) (by simp)⟩⟩

@[simp] private theorem scalarPoly_coeff (e : Fin 2 →₀ ℕ) (g : SeedPoly[X]) (a : ℕ) :
    (scalarPoly e g).coeff a = (g.coeff a).coeff e := rfl

private def sourceCoord (P : Source) (t : Position) : L[X] :=
  scalarPoly t.2.2 ((P.coeff t.1).coeff t.2.1)

private def jetCoords : Jet →ₗ[FX] (Position → FX) :=
  LinearMap.pi fun t => {
    toFun P := ((P.coeff t.1).coeff t.2.1).coeff t.2.2
    map_add' P Q := by simp
    map_smul' r P := by simp }

private theorem coords_center (P : Source) (t : Position) :
    jetCoords (centerEval P) t = algebraMap L[X] FX (sourceCoord P t) := by
  let ξ := algebraMap L[X] FX (Polynomial.X (R := L))
  let g := (P.coeff t.1).coeff t.2.1
  let e := t.2.2
  change (((centerEval P).coeff t.1).coeff t.2.1).coeff e = _
  simp only [centerEval, Polynomial.coeff_mapAlgHom_apply]
  change (g.eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ)).coeff e =
    (IsScalarTower.toAlgHom L L[X] FX) (scalarPoly e g)
  have hdeg : (scalarPoly e g).natDegree ≤ g.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro a ha
    simp [coeff_eq_zero_of_natDegree_lt ha]
  rw [← Polynomial.eval₂_algebraMap_X (scalarPoly e g) (IsScalarTower.toAlgHom L L[X] FX),
    Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hdeg), Polynomial.eval₂_eq_sum_range]
  simp only [MvPolynomial.coeff_sum, scalarPoly_coeff]
  apply Finset.sum_congr rfl
  intro a _
  rw [← map_pow, mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm]
  rfl

private def coeffLin (j i a : ℕ) (e : Fin 2 →₀ ℕ) : Source →ₗ[L] L where
  toFun P := coeffAt P j i a e
  map_add' P Q := by simp [coeffAt]
  map_smul' r P := by simp [coeffAt]

private theorem source_ext {P Q : Source}
    (heq : ∀ j i a e, coeffAt P j i a e = coeffAt Q j i a e) : P = Q :=
  Polynomial.ext fun j => Polynomial.ext fun i => Polynomial.ext fun a =>
    MvPolynomial.ext _ _ fun e => heq j i a e

private theorem seed_exp_le (e : Fin 2 →₀ ℕ) (k : Fin 2) : e k ≤ seedWeight e := by
  rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (e i)) (Finset.mem_univ k)

private instance completeFinite {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : Module.Finite L (complete Crt word s W) := by
  classical
  let A := W + (s.B+s.J)*(2*h) + s.J
  let T := Fin (s.J+1) × Fin (s.B+1) × Fin (A+1) × (Fin 2 → Fin (s.U+1))
  let f : complete Crt word s W →ₗ[L] (T → L) :=
    LinearMap.pi fun t => (coeffLin t.1 t.2.1 t.2.2.1
      (Finsupp.equivFunOnFinite.symm fun k => (t.2.2.2 k : ℕ))).comp
      (complete Crt word s W).subtype
  apply Module.Finite.of_injective f
  intro P Q hPQ
  apply Subtype.ext
  apply source_ext
  intro j i a e
  by_cases he : trueEligible h s W j i a e
  · obtain ⟨hB, hJ, hU, hA⟩ := he
    let t : T := ⟨⟨j, by omega⟩, ⟨i, by omega⟩, ⟨a, by dsimp [A]; omega⟩,
      fun k => ⟨e k, Nat.lt_succ_of_le ((seed_exp_le e k).trans hU)⟩⟩
    have ht := congrFun hPQ t
    change coeffAt (P : Source) j i a (Finsupp.equivFunOnFinite.symm (e : Fin 2 → ℕ)) =
      coeffAt (Q : Source) j i a (Finsupp.equivFunOnFinite.symm (e : Fin 2 → ℕ)) at ht
    simpa only [Finsupp.equivFunOnFinite_symm_coe] using ht
  · exact (P.property.1.1 j i a e he).trans (Q.property.1.1 j i a e he).symm

private instance evaluatedFinite {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : Module.Finite FX (evaluated Crt word s W) := by
  change Module.Finite FX
    (Submodule.span FX ((complete Crt word s W).map centerEval.toLinearMap : Set Jet))
  exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp inferInstance).span (A := FX))

private def boundaryDegree (h : ℕ) (s : Shape) (W : ℕ) (t : Position) : ℕ :=
  W + (s.B+s.J)*(2*h) + t.1 - (t.2.1+t.1)*(131071+h)

private def boundaryMap {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : complete Crt word s W →ₗ[L] (Position → L) :=
  LinearMap.pi fun t =>
    (coeffLin t.1 t.2.1 (boundaryDegree h s W t) t.2.2).comp (complete Crt word s W).subtype

private theorem sourceCoord_degree {h} {D : PoleData h} {Crt : CRTLift D} {word : I → L}
    {s W} (P : complete Crt word s W) (t : Position) :
    (sourceCoord (P : Source) t).natDegree ≤ boundaryDegree h s W t := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro a ha
  change coeffAt (P : Source) t.1 t.2.1 a t.2.2 = 0
  apply P.property.1.1
  intro he
  have hw := he.2.2.2
  unfold boundaryDegree at ha
  omega

/-- Leading coefficient independence in a columnwise degree bound survives passing to L(X). -/
private theorem independent_at_fraction {ι σ : Type*} [Fintype ι]
    (v : ι → σ → L[X]) (d : σ → ℕ) (hd : ∀ k t, (v k t).natDegree ≤ d t)
    (hli : LinearIndependent L (fun k t => (v k t).coeff (d t))) :
    LinearIndependent FX (fun k t => algebraMap L[X] FX (v k t)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (L[X])⁰ c
  choose f hf using hb
  let n := Finset.univ.sup fun k => (f k).natDegree
  have hn (k : ι) : (f k).natDegree ≤ n :=
    Finset.le_sup (f := fun k => (f k).natDegree) (Finset.mem_univ k)
  have hinj := IsFractionRing.injective L[X] FX
  have hsum (t : σ) : ∑ k, f k * v k t = 0 := by
    apply hinj
    rw [map_sum, map_zero]
    simp only [map_mul, hf, Algebra.smul_def, mul_assoc, ← Finset.mul_sum]
    have ht := congrFun hc t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ht
    rw [ht, mul_zero]
  have hlead : ∑ k, (f k).coeff n • (fun t => (v k t).coeff (d t)) = 0 := by
    funext t
    simpa only [Polynomial.finsetSum_coeff, coeff_mul_add_eq_of_natDegree_le (hn _) (hd _ _),
      coeff_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrArg (fun Q : L[X] => Q.coeff (n+d t)) (hsum t)
  have hzero := hli _ hlead
  have hfn (k : ι) : f k = 0 := by
    by_contra hk
    have hlt : (f k).natDegree < n :=
      lt_of_le_of_ne (hn k) (fun he => hk (leadingCoeff_eq_zero.mp (by
        rw [← coeff_natDegree, he, hzero])))
    have hn0 : n ≠ 0 := by omega
    have hprev : n ≤ n - 1 := Finset.sup_le fun k' _ => by
      have hbd := hn k'
      by_cases hq : f k' = 0
      · simp [hq]
      · have hne : (f k').natDegree ≠ n := fun he =>
          hq (leadingCoeff_eq_zero.mp (by rw [← coeff_natDegree, he, hzero]))
        omega
    omega
  intro k
  have hk := hf k
  rw [hfn k, map_zero, Algebra.smul_def] at hk
  have hb0 : algebraMap L[X] FX (b : L[X]) ≠ 0 :=
    fun hz => nonZeroDivisors.coe_ne_zero b (hinj (hz.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hk.symm).resolve_left hb0

private theorem boundary_rank_le {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) :
    Module.finrank L (boundaryMap Crt word s W).range ≤
      Module.finrank FX (evaluated Crt word s W) := by
  classical
  let F := boundaryMap Crt word s W
  let b := Module.finBasis L F.range
  have hex (k : Fin (Module.finrank L F.range)) :
      ∃ P : complete Crt word s W, F P = (b k : Position → L) := (b k).property
  choose P hP using hex
  have hli : LinearIndependent L (fun k t =>
      (sourceCoord (P k : Source) t).coeff (boundaryDegree h s W t)) := by
    change LinearIndependent L (F ∘ P)
    have heq : F ∘ P = fun k => ((b k : F.range) : Position → L) := funext hP
    rw [heq]
    exact b.linearIndependent.map' F.range.subtype F.range.ker_subtype
  have heval : LinearIndependent FX (fun k => centerEval (P k : Source)) := by
    apply LinearIndependent.of_comp jetCoords
    have hf : jetCoords ∘ (fun k => centerEval (P k : Source)) =
        fun k t => algebraMap L[X] FX (sourceCoord (P k : Source) t) :=
      funext fun k => funext fun t => coords_center (P k : Source) t
    rw [hf]
    exact independent_at_fraction (fun k => sourceCoord (P k : Source))
        (boundaryDegree h s W) (fun k => sourceCoord_degree (P k)) hli
  let u (k : Fin (Module.finrank L F.range)) : evaluated Crt word s W :=
    ⟨centerEval (P k : Source), Submodule.subset_span ⟨_, (P k).property, rfl⟩⟩
  have hu : LinearIndependent FX u :=
    LinearIndependent.of_comp (evaluated Crt word s W).subtype heval
  simpa [F] using hu.fintype_card_le_finrank

private theorem strict_of_ker {h} {D : PoleData h} {Crt : CRTLift D} {word : I → L} {s W}
    (P : (boundaryMap Crt word s W).ker) {j i a e} (hn : coeffAt (P.1 : Source) j i a e ≠ 0) :
    a+(i+j)*(131071+h) < W+(s.B+s.J)*(2*h)+j := by
  have he : trueEligible h s W j i a e := by
    by_contra hh
    exact hn (P.1.property.1.1 j i a e hh)
  have hw := he.2.2.2
  by_contra hlt
  have ha : a = boundaryDegree h s W (j,i,e) := by
    unfold boundaryDegree
    dsimp
    omega
  exact hn (by rw [ha]; exact congrFun (LinearMap.mem_ker.mp P.property) (j,i,e))

private theorem ker_step_le {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : Module.finrank L (boundaryMap Crt word s (W+1)).ker ≤
      Module.finrank L (complete Crt word s W) := by
  let F := boundaryMap Crt word s (W+1)
  have hm (P : F.ker) : (P.1 : Source) ∈ complete Crt word s W := by
    refine ⟨⟨?_, P.1.property.1.2⟩, P.1.property.2⟩
    intro j i a e hb
    by_contra hn
    have he : trueEligible h s (W+1) j i a e := by
      by_contra hh
      exact hn (P.1.property.1.1 j i a e hh)
    have hl := strict_of_ker P hn
    exact hb ⟨he.1, he.2.1, he.2.2.1, by omega⟩
  let f := ((complete Crt word s (W+1)).subtype.comp F.ker.subtype).codRestrict
    (complete Crt word s W) hm
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro P Q he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : complete Crt word s W => (x : Source)) he

private theorem ker_zero {h} (hhi : h ≤ 32970) {D : PoleData h} (Crt : CRTLift D)
    (word : I → L) (s : Shape) : (boundaryMap Crt word s 0).ker = ⊥ := by
  apply bot_unique
  intro P hP
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply zero_of_strict_cutoff hhi Crt s P P.property.2
  intro j i a e hn
  simpa using strict_of_ker ⟨P, hP⟩ hn

theorem proof : CutoffRank := by
  intro h _ hhi D Crt word s W
  induction W with
  | zero =>
    have hr := (boundaryMap Crt word s 0).finrank_range_add_finrank_ker
    rw [ker_zero hhi Crt word s, finrank_bot, add_zero] at hr
    simpa [← hr] using boundary_rank_le Crt word s 0
  | succ W ih =>
    rw [Finset.sum_range_succ]
    have hr := (boundaryMap Crt word s (W+1)).finrank_range_add_finrank_ker
    have ha := boundary_rank_le Crt word s (W+1)
    have hb := ker_step_le Crt word s W
    omega

end
end HighSource6921.Telescope
end PackSource_K1_14_1_8Proof
