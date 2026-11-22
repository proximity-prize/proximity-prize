import ProximityPrize.SubmissionLower.Fast061
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators Polynomial
abbrev SeedPoly := MvPolynomial (Fin 2) L
abbrev SeedField := FractionRing SeedPoly
abbrev Source := Polynomial (Polynomial (Polynomial SeedPoly))
abbrev RawSource := Polynomial (Polynomial (Polynomial SeedField))
def otherBlock (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0
structure PoleData (h : ℕ) where
  block : Fin 2 → L[X]
  offset : Fin 2 → L[X]
  constant : Fin 2 → L[X]
  slope : Fin 2 → L[X]
  monic : ∀ i, (block i).Monic
  degree : ∀ i, (block i).natDegree = h
  coprime : IsCoprime (block 0) (block 1)
  determinant : ∀ i, IsCoprime (offset i * constant i) (block i)
def poleProduct {h} (D : PoleData h) : L[X] := D.block 0 * D.block 1
structure CRTLift {h : ℕ} (D : PoleData h) where
  denominator : Fin 2 → L[X]
  numerator : Fin 2 → Polynomial L[X]
  denominator_ne_zero : ∀ i, denominator i ≠ 0
  numerator_degree : ∀ i, (numerator i).degree < (2 * h : ℕ)
  other_dvd : ∀ i, (D.block (otherBlock i)).map (Polynomial.C (R := L)) ∣ numerator i
  congruence : ∀ i, (D.block i).map (Polynomial.C (R := L)) ∣
      ((D.constant i).map (Polynomial.C (R := L)) +
        (@Polynomial.C (Polynomial L) _) (Polynomial.X (R := L)) * (D.slope i).map (Polynomial.C (R := L))) * numerator i +
        (@Polynomial.C (Polynomial L) _) (denominator i * Polynomial.X) * (D.offset i).map (Polynomial.C (R := L))
  regular : ∀ i z, IsCoprime (D.constant i + C z * D.slope i) (D.block i) →
    (denominator i).eval z ≠ 0
def seedInField (i : Fin 2) : L[X] →ₐ[L] SeedField :=
  Polynomial.aeval (algebraMap SeedPoly SeedField (MvPolynomial.X i))
def crtPolynomial {h} {D : PoleData h} (Crt : CRTLift D) : SeedField[X] :=
  ∑ i, (seedInField i (Crt.denominator i))⁻¹ • (Crt.numerator i).map (seedInField i)
def jetConstant {R : Type*} [CommSemiring R] :
    R →+* Polynomial (Polynomial R) :=
  C.comp C
private def jetSubstitute {R S A : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring A] [Algebra R S] [Algebra R A]
    (base : S →ₐ[R] A) (y v : A) : Polynomial (Polynomial S) →ₐ[R] A :=
  eval₂AlgHom (eval₂AlgHom base y (fun _ => Commute.all _ _))
    v (fun _ => Commute.all _ _)
def genericCoefficients : SeedPoly[X] →ₐ[L] SeedField[X] :=
  Polynomial.mapAlgHom (IsScalarTower.toAlgHom L SeedPoly SeedField)
def rawBlock {h} (D : PoleData h) : SeedField[X] :=
  (poleProduct D).map (algebraMap L SeedField)
def forward {h} {D : PoleData h} (Crt : CRTLift D) : Source →ₐ[L] RawSource :=
  let H := rawBlock D
  let lift := crtPolynomial Crt
  let c : SeedField[X] →+* RawSource := jetConstant
  let rawOrd : RawSource := (@Polynomial.C (Polynomial (Polynomial SeedField)) _)
    (Polynomial.X (R := Polynomial SeedField))
  let rawDeriv : RawSource := Polynomial.X
  jetSubstitute (R := L) (S := SeedPoly[X]) (A := RawSource)
    ((IsScalarTower.toAlgHom L SeedField[X] RawSource).comp genericCoefficients)
    (c H * rawOrd + c lift) (c H * rawDeriv + c H.derivative * rawOrd + c lift.derivative)
def atPhysical (x r : L) : Source →ₐ[L] Source :=
  let c : SeedPoly[X] →+* Source := jetConstant
  let base : SeedPoly[X] →ₐ[L] SeedPoly[X] :=
    eval₂AlgHom (IsScalarTower.toAlgHom L SeedPoly SeedPoly[X])
      (Polynomial.X (R := SeedPoly) + (@Polynomial.C SeedPoly _) (MvPolynomial.C x))
      (fun _ => Commute.all _ _)
  let η : Source := (@Polynomial.C (Polynomial (Polynomial SeedPoly)) _)
    (Polynomial.X (R := Polynomial SeedPoly))
  let deriv : Source := Polynomial.X
  jetSubstitute (R := L) (S := SeedPoly[X]) (A := Source)
    ((IsScalarTower.toAlgHom L SeedPoly[X] Source).comp base)
    (c ((@Polynomial.C SeedPoly _) (MvPolynomial.C r)) + c (Polynomial.X (R := SeedPoly)) * deriv + η) deriv
def coeffAt (P : Source) (j i a : ℕ) (e : Fin 2 →₀ ℕ) : L :=
  (((P.coeff j).coeff i).coeff a).coeff e
def seedWeight (e : Fin 2 →₀ ℕ) : ℕ := e.sum fun _ n => n
def trueEligible (h : ℕ) (s : Shape) (W j i a : ℕ) (e : Fin 2 →₀ ℕ) : Prop :=
  i + j ≤ s.B ∧ j ≤ s.J ∧ seedWeight e ≤ s.U ∧
    a + (i+j)*(131071+h) ≤ W + (s.B+s.J)*(2*h) + j
def ambient (h : ℕ) (s : Shape) (W : ℕ) : Submodule L Source where
  carrier := {P | ∀ j i a e, ¬ trueEligible h s W j i a e → coeffAt P j i a e = 0}
  zero_mem' := by simp [coeffAt]
  add_mem' := by
    intro P Q hP hQ j i a e he
    have hp := hP j i a e he
    have hq := hQ j i a e he
    unfold coeffAt at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro b P hP j i a e he
    have hp := hP j i a e he
    unfold coeffAt at hp ⊢
    simp [Polynomial.coeff_smul, hp]
def nodeL (i : I) : L := algebraMap K L (node i)
def physical (word : I → L) (s : Shape) : Submodule L Source where
  carrier := {P | ∀ i a b j e, a + 2*b < s.m →
    coeffAt (atPhysical (nodeL i) (word i) P) j b a e = 0}
  zero_mem' := by simp [coeffAt]
  add_mem' := by
    intro P Q hP hQ i a b j e he
    have hp := hP i a b j e he
    have hq := hQ i a b j e he
    unfold coeffAt at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro b P hP i a k j e he
    have hp := hP i a k j e he
    unfold coeffAt at hp ⊢
    simp [Polynomial.coeff_smul, hp]
def poleSpace {h} {D : PoleData h} (Crt : CRTLift D) (s : Shape) : Submodule L Source where
  carrier := {P | (jetConstant ((rawBlock D) ^ (s.B+s.J)) : RawSource) ∣ forward Crt P}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change _ ∣ forward Crt (P + Q)
    rw [map_add]
    exact dvd_add hP hQ
  smul_mem' := by
    intro b P hP
    change _ ∣ forward Crt (b • P)
    rw [map_smul, Algebra.smul_def]
    exact dvd_mul_of_dvd_right hP _
def contacted (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) : Submodule L Source :=
  ambient h s W ⊓ physical word s
def complete {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) : Submodule L Source :=
  contacted h word s W ⊓ poleSpace Crt s
def centerEval : Source →ₐ[L] Jet :=
  let ξ := algebraMap (Polynomial L) FX (Polynomial.X (R := L))
  let base : SeedPoly[X] →ₐ[L] Seeds :=
    eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
      (MvPolynomial.C ξ) (fun _ => Commute.all _ _)
  Polynomial.mapAlgHom (Polynomial.mapAlgHom base)
def evaluated {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L) : Banks :=
  fun s W => Submodule.span FX (centerEval '' (complete Crt word s W : Set Source))
def rawWidthCond (h : ℕ) (s : Shape) (W : ℕ) : Prop :=
  ∀ q ≤ s.B, ∀ j ≤ min q s.J, q*(131071-h) ≤ W+1+j
def rawVolumeAt (h : ℕ) (s : Shape) (W : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => W+1+j - q*(131071-h))
def poleCredit (h : ℕ) (s : Shape) : ℕ :=
  triangle s.U * (2*h) * shapeSum s (fun q _ => s.B+s.J-q)
def physicalDebit (s : Shape) : ℕ :=
  triangle s.U * 262144 * shapeSum s (fun q i => s.m + min q s.J - (q + 2*i))
def poleSeedDebit (h : ℕ) (s : Shape) : ℕ :=
  2*h*(s.U+1)*shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q))
def seedPair (z : K) : Fin 2 → L :=
  ![algebraMap K L z, (algebraMap K L z)^p]
def residueAt {h} (D : PoleData h) (i : Fin 2) (z : L) : L[X] :=
  D.constant i + (@Polynomial.C L _) z * D.slope i
def MarkResidues {h} (D : PoleData h) (z : K) (S : K[X]) : Prop :=
  ∀ i, IsCoprime (residueAt D i (seedPair z i)) (D.block i) ∧
    D.block i ∣ residueAt D i (seedPair z i) * liftPoly S +
      (@Polynomial.C L _) (seedPair z i) * D.offset i
end
end K1_14_1
end
section
namespace K1_14_1
noncomputable section
open K1 K1_14 Polynomial
open scoped Polynomial
theorem complete_mono {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s s' : Shape} (hm : s.m = s'.m) (hB : s.B = s'.B) (hJ : s.J = s'.J)
    (hU : s.U ≤ s'.U) {W W' : ℕ} (hW : W ≤ W') :
    complete Crt word s W ≤ complete Crt word s' W' := by
  intro P hP
  rcases SetLike.mem_coe.mp hP with ⟨⟨ha, hp⟩, hc⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j i a e hn
    apply ha j i a e
    intro ⟨hb, hj, hu, hw⟩
    apply hn
    exact ⟨hB ▸ hb, hJ ▸ hj, hu.trans hU, by
      rw [← hB, ← hJ]
      omega⟩
  · intro i a b j e he
    exact hp i a b j e (hm ▸ he)
  · change (jetConstant ((rawBlock D) ^ (s'.B+s'.J)) : RawSource) ∣ forward Crt P
    rw [← hB, ← hJ]
    exact hc
theorem evaluated_mono {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s s' : Shape} (hm : s.m = s'.m) (hB : s.B = s'.B) (hJ : s.J = s'.J)
    (hU : s.U ≤ s'.U) {W W' : ℕ} (hW : W ≤ W') :
    evaluated Crt word s W ≤ evaluated Crt word s' W' :=
  Submodule.span_mono (Set.image_mono (complete_mono Crt word hm hB hJ hU hW))
private def centerCoeff (j i : ℕ) (e : Fin 2 →₀ ℕ) : Jet →ₗ[FX] FX where
  toFun P := ((P.coeff j).coeff i).coeff e
  map_add' P Q := by simp
  map_smul' b P := by simp [Polynomial.coeff_smul]
private theorem centerCoeff_eval (P : Source) (j i : ℕ) (e : Fin 2 →₀ ℕ)
    (hz : ∀ a, coeffAt P j i a e = 0) :
    centerCoeff j i e (centerEval P) = 0 := by
  let ξ := algebraMap (Polynomial L) FX (Polynomial.X (R := L))
  let g := (P.coeff j).coeff i
  change (((centerEval P).coeff j).coeff i).coeff e = 0
  simp only [centerEval, Polynomial.coeff_mapAlgHom_apply]
  change (g.eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ)).coeff e = 0
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro a _
  have he : (g.coeff a).coeff e = 0 := hz a
  rw [← map_pow, mul_comm, MvPolynomial.coeff_C_mul]
  change ξ^a * (MvPolynomial.map (algebraMap L FX) (g.coeff a)).coeff e = 0
  rw [MvPolynomial.coeff_map, he, map_zero, mul_zero]
private theorem centerCoeff_zero {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s W P} (hP : P ∈ evaluated Crt word s W)
    (j i : ℕ) (e : Fin 2 →₀ ℕ) (hf : ¬ (i+j ≤ s.B ∧ j ≤ s.J ∧ seedWeight e ≤ s.U)) :
    centerCoeff j i e P = 0 := by
  have hsub : evaluated Crt word s W ≤ LinearMap.ker (centerCoeff j i e) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨Q, hQ, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply centerCoeff_eval
      intro a
      exact hQ.1.1 j i a e (fun hh => hf ⟨hh.1, hh.2.1, hh.2.2.1⟩))
  exact LinearMap.mem_ker.mp (hsub hP)
theorem evaluated_shape {h} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s W P} (hP : P ∈ evaluated Crt word s W) (j i : ℕ)
    (hne : ((P.coeff j).coeff i) ≠ 0) :
    i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U := by
  classical
  let g := (P.coeff j).coeff i
  have he (e) (hes : e ∈ g.support) :
      i+j ≤ s.B ∧ j ≤ s.J ∧ seedWeight e ≤ s.U := by
    by_contra hbad
    exact (MvPolynomial.mem_support_iff.mp hes) (centerCoeff_zero Crt word hP j i e hbad)
  obtain ⟨e, heS⟩ := Finset.nonempty_iff_ne_empty.mpr (by simpa [g] using hne :
    g.support ≠ ∅)
  refine ⟨(he e heS).1, (he e heS).2.1, ?_⟩
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  exact fun a ha => (he a ha).2.2
end
end K1_14_1
end
section
namespace K1_14_1
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ h, 2601 ≤ h → h ≤ 32680 → ∀ D : PoleData h, Nonempty (CRTLift D)
end
end K1_14_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 16
namespace K1_14_1_2
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators
def evalThree {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) : Polynomial (Polynomial (Polynomial A)) →+* R :=
  eval₂RingHom (eval₂RingHom (eval₂RingHom f x) y) v
def composed (t : Fin 2 → L) (S : L[X]) : Source →+* L[X] :=
  evalThree (C.comp (MvPolynomial.eval t)) Polynomial.X S S.derivative
theorem evalThree_ext {A R : Type*} [CommSemiring A] [CommSemiring R]
    {f g : Polynomial (Polynomial (Polynomial A)) →+* R}
    (hc : ∀ a : A, f (C (C (C a))) = g (C (C (C a))))
    (hx : f (C (C Polynomial.X)) = g (C (C Polynomial.X)))
    (hy : f (C Polynomial.X) = g (C Polynomial.X))
    (hv : f Polynomial.X = g Polynomial.X) : f = g := by
  apply Polynomial.ringHom_ext _ hv
  have hbase : (f.comp C).comp C = (g.comp C).comp C :=
    Polynomial.ringHom_ext hc hx
  have hinner : f.comp C = g.comp C :=
    Polynomial.ringHom_ext (DFunLike.congr_fun hbase) hy
  exact DFunLike.congr_fun hinner
@[simp] theorem evalThree_const {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) (a : A) :
    evalThree f x y v (C (C (C a))) = f a := by
  simp [evalThree]
@[simp] theorem evalThree_X {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) :
    evalThree f x y v (C (C Polynomial.X)) = x := by
  simp [evalThree]
@[simp] theorem evalThree_Y {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) :
    evalThree f x y v (C Polynomial.X) = y := by
  simp [evalThree]
@[simp] theorem evalThree_V {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) :
    evalThree f x y v Polynomial.X = v := by
  simp [evalThree]
theorem evalThree_sum {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v : R) (P : Polynomial (Polynomial (Polynomial A))) :
    evalThree f x y v P =
      ∑ j ∈ P.support, (∑ i ∈ (P.coeff j).support, (∑ a ∈ ((P.coeff j).coeff i).support,
        f (((P.coeff j).coeff i).coeff a) * x ^ a) * y ^ i) * v ^ j := by
  simp only [evalThree, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum]
theorem composed_degree {h : ℕ} {s : Shape} {W : ℕ} {P : Source}
    (hP : P ∈ ambient h s W) (t : Fin 2 → L) (S : L[X])
    (hd : S.natDegree ≤ 131071+h) :
    (composed t S P).natDegree ≤ W+(s.B+s.J)*(2*h) := by
  let d := 131071+h
  change S.natDegree ≤ d at hd
  have hd' : S.derivative.natDegree ≤ d-1 :=
    (natDegree_derivative_le S).trans (Nat.sub_le_sub_right hd _)
  have hpred : d-1+1 = d := by dsimp [d]; omega
  rw [composed, evalThree_sum]
  apply natDegree_sum_le_of_forall_le
  intro j _
  rw [Finset.sum_mul]
  apply natDegree_sum_le_of_forall_le
  intro i _
  rw [Finset.sum_mul, Finset.sum_mul]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hne : ((P.coeff j).coeff i).coeff a ≠ 0 :=
    mem_support_iff.mp ha
  have hw : a+(i+j)*d ≤ W+(s.B+s.J)*(2*h)+j := by
    by_contra hn
    apply hne
    ext e
    exact hP j i a e (fun he => hn he.2.2.2)
  refine (natDegree_mul_le_of_le (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (by simp : (C _ : L[X]).natDegree ≤ 0) (by simp : (Polynomial.X ^ a : L[X]).natDegree ≤ a))
    (natDegree_pow_le_of_le i hd)) (natDegree_pow_le_of_le j hd')).trans ?_
  have hj : j*(d-1)+j = j*d := by rw [← Nat.mul_succ, Nat.succ_eq_add_one, hpred]
  rw [Nat.add_mul] at hw
  omega
theorem composed_center (z : K) (S : K[X]) (P : Source) :
    jetAt (centerEval P) z S = algebraMap L[X] FX (composed (seedPair z) (liftPoly S) P) := by
  let ev := eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
  let f := algebraMap L[X] FX
  change (ev.comp centerEval.toRingHom) P = (f.comp (composed (seedPair z) (liftPoly S))) P
  apply DFunLike.congr_fun
  apply evalThree_ext
  · intro g
    have he :
        (graphEval z).comp (MvPolynomial.map (algebraMap L FX)) =
          (f.comp C).comp (MvPolynomial.eval (seedPair z)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [graphEval, RingHom.comp_apply, f]
        rfl
      · intro i
        fin_cases i <;> simp [graphEval, seedPair, seedEmbedding, f]
    simpa [RingHom.comp_apply, centerEval, ev, composed] using DFunLike.congr_fun he g
  · simp [RingHom.comp_apply, centerEval, ev, composed, graphEval, f]
  · simp [RingHom.comp_apply, centerEval, ev, composed, f, atX]
  · simp [RingHom.comp_apply, centerEval, ev, composed, f, atX, liftPoly, derivative_map]
theorem span_vanish {h : ℕ} {D : PoleData h} {Crt : CRTLift D}
    {word : I → L} {s : Shape} {W : ℕ} (z : K) (S : K[X])
    (hz : ∀ P ∈ complete Crt word s W, composed (seedPair z) (liftPoly S) P = 0)
    {P : Jet} (hP : P ∈ evaluated Crt word s W) : jetAt P z S = 0 := by
  let ev := eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
  change P ∈ Submodule.span FX _ at hP
  change ev P = 0
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Q, hQ, rfl⟩ := hP
    change jetAt (centerEval Q) z S = 0
    rw [composed_center, hz Q hQ, map_zero]
  | zero => exact map_zero ev
  | add A B _ _ hA hB => rw [map_add, hA, hB, add_zero]
  | smul r A _ hA => rw [Algebra.smul_def, map_mul, hA, mul_zero]
private theorem physical_substitute (t : Fin 2 → L) (S : L[X]) (x r : L) :
    (evalThree (C.comp (MvPolynomial.eval t)) (Polynomial.X-C x)
      (S-C r-(Polynomial.X-C x)*S.derivative) S.derivative).comp (atPhysical x r).toRingHom =
      composed t S := by
  let δ : L[X] := Polynomial.X-C x
  let η : L[X] := S-C r-δ*S.derivative
  let E := evalThree (C.comp (MvPolynomial.eval t)) δ η S.derivative
  let c : SeedPoly[X] →+* Source := jetConstant
  let u : SeedPoly[X] := Polynomial.X + C (MvPolynomial.C x)
  let b : SeedPoly[X] →+* Source := c.comp (eval₂RingHom C u)
  let y : Source := c (C (MvPolynomial.C r)) + c Polynomial.X * Polynomial.X + C Polynomial.X
  let _ : CommSemiring Source := inferInstanceAs (CommSemiring (Polynomial (Polynomial (Polynomial SeedPoly))))
  have hform : (atPhysical x r).toRingHom = eval₂RingHom (eval₂RingHom b y) Polynomial.X := rfl
  change E.comp (atPhysical x r).toRingHom = composed t S
  rw [hform]
  apply evalThree_ext
  · intro g
    simp [E, composed, b, c, jetConstant, RingHom.comp_apply]
  · simp [E, composed, b, c, u, δ, jetConstant, RingHom.comp_apply]
  · simp [E, composed, y, c, η, jetConstant, RingHom.comp_apply]
  · simp [E, composed, RingHom.comp_apply]
private theorem remainder_order_two (S : L[X]) (x r : L) (hx : S.eval x = r) :
    (Polynomial.X-C x)^2 ∣ S-C r-(Polynomial.X-C x)*S.derivative := by
  rw [X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero]
  intro k hk
  have he : k = 0 ∨ k = 1 := by omega
  rcases he with rfl | rfl
  · simp [hx]
  · simp [hasseDeriv_one, derivative_sub, derivative_mul]
theorem composed_contact {word : I → L} {s : Shape} {P : Source}
    (hP : P ∈ physical word s) (t : Fin 2 → L) (S : L[X])
    (k : I) (hk : S.eval (nodeL k) = word k) :
    (Polynomial.X-C (nodeL k)) ^ s.m ∣ composed t S P := by
  let x := nodeL k
  let r := word k
  let δ : L[X] := Polynomial.X-C x
  let η : L[X] := S-C r-δ*S.derivative
  let E := evalThree (C.comp (MvPolynomial.eval t)) δ η S.derivative
  let Q := atPhysical x r P
  change δ ^ s.m ∣ composed t S P
  have he : E Q = composed t S P :=
    DFunLike.congr_fun (physical_substitute t S x r) P
  rw [← he]
  dsimp only [E]
  rw [evalThree_sum]
  apply Finset.dvd_sum
  intro j _
  apply Dvd.dvd.mul_right
  apply Finset.dvd_sum
  intro b _
  rw [Finset.sum_mul]
  apply Finset.dvd_sum
  intro a ha
  have hw : s.m ≤ a+2*b := by
    by_contra hn
    apply mem_support_iff.mp ha
    ext e
    exact hP k a b j e (by omega)
  have hη : δ ^ 2 ∣ η := remainder_order_two S x r hk
  have hpow : δ ^ (a+2*b) ∣ δ ^ a * η ^ b := by
    rw [pow_add, pow_mul]
    exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hη b)
  exact (pow_dvd_pow _ hw).trans (by simpa only [mul_assoc] using hpow.mul_left _)
def markedLift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L) : L[X] :=
  ∑ i, C (((Crt.denominator i).eval (t i))⁻¹) * (Crt.numerator i).map (evalRingHom (t i))
private theorem map_eval_C (t : L) (P : L[X]) :
    (P.map (C : L →+* L[X])).map (evalRingHom t) = P := by
  rw [map_map]
  have he : (evalRingHom t).comp (C : L →+* L[X]) = RingHom.id L := by ext a; simp
  simp [he]
theorem markedLift_residue {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    {z : K} {S : K[X]} (hm : MarkResidues D z S) :
    poleProduct D ∣ liftPoly S - markedLift Crt (seedPair z) := by
  let t := seedPair z
  let d (i : Fin 2) := (Crt.denominator i).eval (t i)
  let N (i : Fin 2) := (Crt.numerator i).map (evalRingHom (t i))
  let U (i : Fin 2) := C (d i)⁻¹ * N i
  have hd (i : Fin 2) : d i ≠ 0 := Crt.regular i (t i) (hm i).1
  have hc (i : Fin 2) : D.block i ∣ residueAt D i (t i) * U i + C (t i) * D.offset i := by
    have h0 := map_dvd (mapRingHom (evalRingHom (t i))) (Crt.congruence i)
    have h1 : D.block i ∣ residueAt D i (t i) * N i + C (d i * t i) * D.offset i := by
      simpa [residueAt, N, d, map_eval_C] using h0
    have he : (C (d i)⁻¹ : L[X]) * C (d i * t i) = C (t i) := by
      rw [← map_mul, ← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
    simpa only [mul_add, ← mul_assoc, mul_comm (C (d i)⁻¹) (residueAt D i (t i)), he, U] using
      h1.mul_left (C (d i)⁻¹)
  have ho (i : Fin 2) : D.block (otherBlock i) ∣ U i := by
    apply Dvd.dvd.mul_left
    simpa [N, map_eval_C] using map_dvd (mapRingHom (evalRingHom (t i))) (Crt.other_dvd i)
  have hsum (i : Fin 2) : markedLift Crt t = U i + U (otherBlock i) := by
    rw [markedLift, Fin.sum_univ_two]
    fin_cases i
    · rfl
    · exact add_comm _ _
  have hblock (i : Fin 2) : D.block i ∣ liftPoly S - markedLift Crt t := by
    apply (hm i).1.symm.dvd_of_dvd_mul_left
    have hoi : D.block i ∣ U (otherBlock i) := by
      have hother : otherBlock (otherBlock i) = i := by fin_cases i <;> decide
      simpa only [hother] using ho (otherBlock i)
    have hmark : D.block i ∣ residueAt D i (t i) * markedLift Crt t + C (t i) * D.offset i := by
      rw [hsum, mul_add, add_right_comm]
      exact dvd_add (hc i) (hoi.mul_left _)
    have hactual : D.block i ∣ residueAt D i (t i) * liftPoly S + C (t i) * D.offset i :=
      (hm i).2
    change D.block i ∣ residueAt D i (t i) * (liftPoly S - markedLift Crt t)
    simpa only [mul_sub, add_sub_add_right_eq_sub] using dvd_sub hactual hmark
  exact D.coprime.mul_dvd (hblock 0) (hblock 1)
private def regularSeeds (t : Fin 2 → L) : Submonoid SeedPoly where
  carrier := {a | MvPolynomial.eval t a ≠ 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change MvPolynomial.eval t (a*b) ≠ 0
    exact (map_mul (MvPolynomial.eval t) a b).symm ▸ mul_ne_zero ha hb
private abbrev RegularRing (t : Fin 2 → L) := Localization (regularSeeds t)
private def specialize (t : Fin 2 → L) : RegularRing t →+* L :=
  IsLocalization.lift (g := MvPolynomial.eval t)
    (fun a : regularSeeds t => isUnit_iff_ne_zero.mpr a.property)
private def includeGeneric (t : Fin 2 → L) : RegularRing t →+* SeedField :=
  IsLocalization.lift (g := algebraMap SeedPoly SeedField)
    (fun a : regularSeeds t => isUnit_iff_ne_zero.mpr
      (fun he => a.property (by
        have hzero := (IsFractionRing.injective SeedPoly SeedField) (he.trans (map_zero _).symm)
        simp [hzero])))
private theorem includeGeneric_injective (t : Fin 2 → L) :
    Function.Injective (includeGeneric t) := by
  unfold includeGeneric
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  have h : regularSeeds t ≤ nonZeroDivisors SeedPoly := fun x hx =>
    mem_nonZeroDivisors_iff_ne_zero.mpr (fun he => hx (by simp [he]))
  rw [(IsLocalization.injective (RegularRing t) h).eq_iff,
    (IsFractionRing.injective SeedPoly SeedField).eq_iff]
private def seedPolynomial (i : Fin 2) : L[X] →+* SeedPoly :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X i)
private theorem map_seedPolynomial (i : Fin 2) :
    (algebraMap SeedPoly SeedField).comp (seedPolynomial i) = (seedInField i).toRingHom := by
  apply Polynomial.ringHom_ext <;>
    simp [seedPolynomial, seedInField, aeval_def, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply L SeedPoly SeedField]
private theorem eval_seedPolynomial (t : Fin 2 → L) (i : Fin 2) :
    (MvPolynomial.eval t).comp (seedPolynomial i) = evalRingHom (t i) := by
  apply Polynomial.ringHom_ext <;> simp [seedPolynomial, RingHom.comp_apply]
private def localLift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) : (RegularRing t)[X] :=
  ∑ i, C (IsLocalization.mk' (RegularRing t) 1
      (⟨seedPolynomial i (Crt.denominator i), by
        change (MvPolynomial.eval t).comp (seedPolynomial i) (Crt.denominator i) ≠ 0
        rw [eval_seedPolynomial]
        exact hd i⟩ : regularSeeds t)) *
    (Crt.numerator i).map ((algebraMap SeedPoly (RegularRing t)).comp (seedPolynomial i))
private theorem map_localLift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) :
    (localLift Crt t hd).map (includeGeneric t) = crtPolynomial Crt := by
  rw [localLift, crtPolynomial, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : algebraMap SeedPoly SeedField (seedPolynomial i (Crt.denominator i)) =
      seedInField i (Crt.denominator i) :=
    RingHom.congr_fun (map_seedPolynomial i) (Crt.denominator i)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, includeGeneric,
    IsLocalization.lift_mk', IsLocalization.lift_comp, ← RingHom.comp_assoc, map_seedPolynomial,
    smul_eq_C_mul, map_one, Units.val_inv_eq_inv_val, one_mul,
    IsUnit.liftRight_apply, IsUnit.unit_spec, MonoidHom.domRestrict_apply]
  change C ((algebraMap SeedPoly SeedField (seedPolynomial i (Crt.denominator i)))⁻¹) * _ = _
  rw [he]
  rfl
private theorem specialize_localLift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) :
    (localLift Crt t hd).map (specialize t) = markedLift Crt t := by
  rw [localLift, markedLift, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : MvPolynomial.eval t (seedPolynomial i (Crt.denominator i)) =
      (Crt.denominator i).eval (t i) :=
    RingHom.congr_fun (eval_seedPolynomial t i) (Crt.denominator i)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, specialize,
    IsLocalization.lift_mk', IsLocalization.lift_comp, ← RingHom.comp_assoc, eval_seedPolynomial,
    map_one, Units.val_inv_eq_inv_val, one_mul, IsUnit.liftRight_apply, IsUnit.unit_spec,
    MonoidHom.domRestrict_apply]
  change C ((MvPolynomial.eval t (seedPolynomial i (Crt.denominator i)))⁻¹) * _ = _
  rw [he]
private def rawEval (T : SeedField[X]) : RawSource →+* SeedField[X] :=
  eval₂RingHom (eval₂RingHom (RingHom.id _) T) T.derivative
private theorem forward_eval {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    (T : SeedField[X]) :
    (rawEval T).comp (forward Crt).toRingHom =
      evalThree (C.comp (algebraMap SeedPoly SeedField)) Polynomial.X
        (rawBlock D*T + crtPolynomial Crt)
        (rawBlock D*T.derivative + (rawBlock D).derivative*T + (crtPolynomial Crt).derivative) := by
  let c : SeedField[X] →+* RawSource := jetConstant
  let H := rawBlock D
  let lift := crtPolynomial Crt
  let o : RawSource := C (Polynomial.X (R := Polynomial SeedField))
  let v : RawSource := Polynomial.X
  let b : SeedPoly[X] →+* RawSource := c.comp (mapRingHom (algebraMap SeedPoly SeedField))
  let _ : CommSemiring RawSource := inferInstanceAs (CommSemiring (Polynomial (Polynomial (Polynomial SeedField))))
  have hf : (forward Crt).toRingHom =
      eval₂RingHom (eval₂RingHom b (c H*o+c lift)) (c H*v+c H.derivative*o+c lift.derivative) := rfl
  rw [hf]
  apply evalThree_ext <;> simp [rawEval, c, jetConstant, H, lift, o, v, b, RingHom.comp_apply]
private theorem evalThree_map {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (jetY jetV : A[X]) :
    (mapRingHom g).comp (evalThree (C.comp f) Polynomial.X jetY jetV) =
      evalThree (C.comp (g.comp f)) Polynomial.X (jetY.map g) (jetV.map g) := by
  apply evalThree_ext <;> simp [RingHom.comp_apply]
theorem specialized_poles {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    {z : K} {S : K[X]} (hm : MarkResidues D z S) {s : Shape} {P : Source}
    (hP : P ∈ poleSpace Crt s) :
    poleProduct D ^ (s.B+s.J) ∣ composed (seedPair z) (liftPoly S) P := by
  let t := seedPair z
  let A := RegularRing t
  let f := algebraMap SeedPoly A
  let e := specialize t
  let g := includeGeneric t
  let j : L →+* A := f.comp MvPolynomial.C
  have hef : e.comp f = MvPolynomial.eval t := IsLocalization.lift_comp _
  have hgf : g.comp f = algebraMap SeedPoly SeedField := IsLocalization.lift_comp _
  have hej : e.comp j = RingHom.id L := by
    change (e.comp f).comp MvPolynomial.C = _
    rw [hef]
    ext a
    simp
  have hgj : g.comp j = algebraMap L SeedField := by
    change (g.comp f).comp MvPolynomial.C = _
    rw [hgf]
    ext a
    simp [IsScalarTower.algebraMap_apply L SeedPoly SeedField, MvPolynomial.algebraMap_eq]
  have hd (i : Fin 2) : (Crt.denominator i).eval (t i) ≠ 0 := Crt.regular i _ (hm i).1
  obtain ⟨T, hT⟩ := markedLift_residue Crt hm
  have hS : poleProduct D*T + markedLift Crt t = liftPoly S := by
    rw [← hT]
    abel
  let H := (poleProduct D).map j
  let U := T.map j
  let lift := localLift Crt t hd
  let jetY := H*U + lift
  let Q := evalThree (C.comp f) Polynomial.X jetY jetY.derivative P
  let F := H^(s.B+s.J)
  have hFm : F.Monic := ((D.monic 0).mul (D.monic 1) |>.map j).pow _
  have egH : H.map g = rawBlock D := by rw [map_map, hgj]; rfl
  have eeH : H.map e = poleProduct D := by rw [map_map, hej, map_id]
  have eeU : U.map e = T := by rw [map_map, hej, map_id]
  have egY : jetY.map g = rawBlock D * U.map g + crtPolynomial Crt := by
    rw [Polynomial.map_add, Polynomial.map_mul, egH, map_localLift]
  have eeY : jetY.map e = liftPoly S := by
    rw [Polynomial.map_add, Polynomial.map_mul, eeH, eeU, specialize_localLift, hS]
  have hgQ :
      Q.map g = rawEval (U.map g) (forward Crt P) := by
    change ((mapRingHom g).comp (evalThree (C.comp f) Polynomial.X jetY jetY.derivative)) P =
      ((rawEval (U.map g)).comp (forward Crt).toRingHom) P
    rw [evalThree_map, hgf, ← derivative_map, egY, forward_eval, derivative_add, derivative_mul]
    congr 2
    abel
  have hgF : F.map g = rawBlock D ^ (s.B+s.J) := by rw [Polynomial.map_pow, egH]
  have hdiv : F.map g ∣ Q.map g := by
    rw [hgF, hgQ]
    have h := map_dvd (rawEval (U.map g)) hP
    simpa [rawEval, jetConstant, eval₂_pow] using h
  have hlocal : F ∣ Q := by
    apply (modByMonic_eq_zero_iff_dvd hFm).mp
    apply map_injective g (includeGeneric_injective t)
    rw [map_modByMonic g hFm, Polynomial.map_zero]
    exact (modByMonic_eq_zero_iff_dvd (hFm.map g)).mpr hdiv
  have heQ : Q.map e = composed t (liftPoly S) P := by
    change ((mapRingHom e).comp (evalThree (C.comp f) Polynomial.X jetY jetY.derivative)) P = _
    rw [evalThree_map, hef, ← derivative_map, eeY]
    rfl
  have heF : F.map e = poleProduct D^(s.B+s.J) := by rw [Polynomial.map_pow, eeH]
  have hmapped := map_dvd (mapRingHom e) hlocal
  change F.map e ∣ Q.map e at hmapped
  rwa [heF, heQ] at hmapped
end
end K1_14_1_2
end
section
namespace K1_14_1_3
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial
def translation {R : Type*} [CommSemiring R] (i : Fin 2) :
    MvPolynomial (Fin 2) R →ₐ[R] (MvPolynomial (Fin 2) R)[X] :=
  MvPolynomial.aeval fun j =>
    C (MvPolynomial.X j) + if j = i then Polynomial.X else 0
def seedCoeff {R : Type*} [CommSemiring R] (i : Fin 2) (r : ℕ) :
    MvPolynomial (Fin 2) R →ₗ[R] MvPolynomial (Fin 2) R where
  toFun P := (translation i P).coeff r
  map_add' P Q := by simp
  map_smul' a P := by simp
def mapCoeffs {R A B : Type*} [Semiring R] [Semiring A] [Semiring B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) : A[X] →ₗ[R] B[X] :=
  Polynomial.lsum fun n =>
    { toFun := fun a => monomial n (f a)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun c a => by rw [map_smul, ← smul_monomial]; rfl }
@[simp] theorem mapCoeffs_coeff {R A B : Type*} [Semiring R] [Semiring A] [Semiring B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) (Q : A[X]) (n : ℕ) :
    (mapCoeffs f Q).coeff n = f (Q.coeff n) := by
  change (Q.sum fun j a => monomial j (f a)).coeff n = f (Q.coeff n)
  classical
  simp only [Polynomial.sum, Polynomial.finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq']
  split
  · rfl
  next h => rw [notMem_support_iff.mp h, map_zero]
@[simp] theorem mapCoeffs_monomial {R A B : Type*} [Semiring R] [Semiring A] [Semiring B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) (n : ℕ) (a : A) :
    mapCoeffs f (monomial n a) = monomial n (f a) := by
  ext m
  simp only [mapCoeffs_coeff, coeff_monomial]
  split <;> simp
def sourceHasse (i : Fin 2) (r : ℕ) : Source →ₗ[L] Source :=
  mapCoeffs (mapCoeffs (mapCoeffs (seedCoeff i r)))
def sourceX (E : L[X]) : SeedPoly[X] :=
  E.map MvPolynomial.C
def cleared {h : ℕ} (D : PoleData h) (i : Fin 2) (r : ℕ) (Q : Source) : Source :=
  jetConstant (sourceX (D.block i ^ (2*r))) * sourceHasse i r Q
end
end K1_14_1_3
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_1_3
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
private theorem seedCoeff_totalDegree (i : Fin 2) (r : ℕ) (P : SeedPoly) :
    (seedCoeff i r P).totalDegree ≤ P.totalDegree := by
  classical
  let g : Fin 2 → MvPolynomial (Option (Fin 2)) L :=
    fun j => MvPolynomial.X (some j) + if j = i then MvPolynomial.X none else 0
  let f : SeedPoly →ₐ[L] MvPolynomial (Option (Fin 2)) L := MvPolynomial.aeval g
  have htrans : translation i = (MvPolynomial.optionEquivLeft L (Fin 2)).toAlgHom.comp f := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i <;> simp [translation, f, g, hj]
  have hg (j : Fin 2) : (g j).totalDegree ≤ 1 := by
    by_cases hj : j = i
    · simpa [g, hj] using (MvPolynomial.totalDegree_add
        (MvPolynomial.X (some j) : MvPolynomial (Option (Fin 2)) L)
        (MvPolynomial.X none))
    · simp [g, hj]
  have hf : (f P).totalDegree ≤ P.totalDegree := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    change (MvPolynomial.aeval g (MvPolynomial.monomial m (P.coeff m))).totalDegree ≤ _
    rw [MvPolynomial.aeval_monomial]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (MvPolynomial.le_totalDegree hm)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) (hg j))
  change ((translation i P).coeff r).totalDegree ≤ _
  rw [htrans]
  exact (MvPolynomial.totalDegree_coeff_optionEquivLeft_le L (Fin 2) (f P) r).trans hf
theorem ambient_cleared {h : ℕ} (D : PoleData h) {s : Shape} {W : ℕ} {Q : Source}
    (hQ : Q ∈ ambient h s W) (i : Fin 2) (r : ℕ) :
    cleared D i r Q ∈ ambient h s (W+2*h*r) := by
  classical
  intro j k a e he
  simp only [cleared, coeffAt, jetConstant, RingHom.comp_apply]
  rw [coeff_C_mul, coeff_C_mul, coeff_mul, MvPolynomial.coeff_sum]
  simp only [sourceX, coeff_map, MvPolynomial.coeff_C_mul, sourceHasse, mapCoeffs_coeff]
  apply Finset.sum_eq_zero
  rintro ⟨b, c⟩ hbc
  by_cases hb : (D.block i ^ (2*r)).coeff b = 0
  · simp [hb]
  have hbdeg : b ≤ 2*h*r := by
    have hb' := le_natDegree_of_ne_zero hb
    rw [natDegree_pow, D.degree] at hb'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb'
  have hbc' : b + c = a := by
    simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using hbc
  let A := ((Q.coeff j).coeff k).coeff c
  change (D.block i ^ (2*r)).coeff b * (seedCoeff i r A).coeff e = 0
  by_contra hne
  have hseed : (seedCoeff i r A).coeff e ≠ 0 := fun hz => hne (by simp [hz])
  have ht : seedWeight e ≤ A.totalDegree :=
    (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hseed)).trans
      (seedCoeff_totalDegree i r A)
  have hAnz : A ≠ 0 := fun hz => hseed (by simp [hz])
  have hshape : ∃ d, trueEligible h s W j k c d := by
    by_contra hall
    apply hAnz
    apply MvPolynomial.ext
    intro d
    simpa [coeffAt, A] using hQ j k c d (fun hd => hall ⟨d, hd⟩)
  obtain ⟨d, hs, hj, _, hw⟩ := hshape
  have hseedCap : A.totalDegree ≤ s.U := by
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro d hd
    by_contra hbad
    exact (MvPolynomial.mem_support_iff.mp hd) (hQ j k c d (fun hd' => hbad hd'.2.2.1))
  exact he ⟨hs, hj, ht.trans hseedCap, by omega⟩
end
end K1_14_1_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
abbrev Seed (R : Type) [CommSemiring R] := MvPolynomial (Fin 2) R
abbrev SeedFrac (F : Type) [Field F] := FractionRing (Seed F)
abbrev JetPolys (R : Type) [Semiring R] := Polynomial (Polynomial (Polynomial R))
abbrev TrueSource (R : Type) [CommSemiring R] := JetPolys (Seed R)
abbrev Exponent := Fin 2 →₀ ℕ
def sourceCoeff {R : Type} [CommSemiring R] (P : TrueSource R)
    (j i a : ℕ) (e : Exponent) : R :=
  (((P.coeff j).coeff i).coeff a).coeff e
def Shaped {R : Type} [CommSemiring R] (s : Shape) (P : TrueSource R) : Prop :=
  ∀ j i a e, sourceCoeff P j i a e ≠ 0 → i + j ≤ s.B ∧ j ≤ s.J ∧ seedWeight e ≤ s.U
def mapSource {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    TrueSource R →+* TrueSource S :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.map f)))
def SeedWindow {F : Type} [Field F] (U d : ℕ) (side : Fin 2) (g : Seed F) : Prop :=
  ∀ e, g.coeff e ≠ 0 → e (otherBlock side) ≤ U ∧ e side + e (otherBlock side) ≤ U + d
private def substituteJets {R S A : Type} [CommSemiring R] [CommSemiring S]
    [CommSemiring A] [Algebra R S] [Algebra R A]
    (base : S →ₐ[R] A) (y v : A) : Polynomial (Polynomial S) →ₐ[R] A :=
  eval₂AlgHom (eval₂AlgHom base y (fun _ => Commute.all _ _))
    v (fun _ => Commute.all _ _)
def forward {F : Type} [Field F] (H : F[X]) (lift : (SeedFrac F)[X]) :
    TrueSource F →ₐ[F] JetPolys (SeedFrac F) :=
  let H' := H.map (algebraMap F (SeedFrac F))
  let c : (SeedFrac F)[X] →+* JetPolys (SeedFrac F) := jetConstant
  let rawY : JetPolys (SeedFrac F) := C (Polynomial.X (R := Polynomial (SeedFrac F)))
  let rawV : JetPolys (SeedFrac F) := Polynomial.X
  let coeffs : (Seed F)[X] →ₐ[F] (SeedFrac F)[X] :=
    Polynomial.mapAlgHom (IsScalarTower.toAlgHom F (Seed F) (SeedFrac F))
  let base := (IsScalarTower.toAlgHom F (SeedFrac F)[X] (JetPolys (SeedFrac F))).comp coeffs
  substituteJets base (c H' * rawY + c lift)
    (c H' * rawV + c H'.derivative * rawY + c lift.derivative)
def PoleTest {F : Type} [Field F] (s : Shape) (H : F[X])
    (lift : (SeedFrac F)[X]) (P : TrueSource F) : Prop :=
  (jetConstant ((H.map (algebraMap F (SeedFrac F))) ^ (s.B + s.J)) :
    JetPolys (SeedFrac F)) ∣ forward H lift P
abbrev Grade (s : Shape) := Fin (s.B + 1)
abbrev GradeSlot (s : Shape) (q : ℕ) := Fin (min q s.J + 1)
abbrev LocalJet (s : Shape) := Fin (s.B + s.J)
abbrev LocalRow (s : Shape) (q : ℕ) := Fin (s.B + s.J - q) × GradeSlot s q
abbrev ZeroRows (F : Type) (s : Shape) (q : ℕ) :=
  LocalRow s q → GradeSlot s q → LocalJet s → F
def zeroGrade {F : Type} [Field F] (s : Shape) (q : ℕ)
    (f : GradeSlot s q → F[X]) (k : GradeSlot s q) : F[X] :=
  ∑ j, if k.val ≤ j.val then
    f j * Polynomial.C (R := F) (j.val.choose k.val : F) *
      (Polynomial.X (R := F)) ^ (q - j.val + k.val) else 0
def ZeroRowsValid {F : Type} [Field F] (s : Shape) (q : ℕ)
    (rows : ZeroRows F s q) : Prop :=
  ∀ f : GradeSlot s q → (SeedFrac F)[X],
    (∀ k, (Polynomial.X (R := SeedFrac F)) ^ (s.B + s.J) ∣ zeroGrade s q f k) ↔
      ∀ r, ∑ j, ∑ a, algebraMap F (SeedFrac F) (rows r j a) * (f j).coeff a.val = 0
def residue {F : Type} [Field F] (side : Fin 2) (a b c : F) : SeedFrac F :=
  let z := algebraMap (Seed F) (SeedFrac F) (MvPolynomial.X side)
  algebraMap F (SeedFrac F) a * z /
    (algebraMap F (SeedFrac F) b + algebraMap F (SeedFrac F) c * z)
structure SimplePoles {F : Type} [Field F] (h : ℕ) (H : F[X])
    (lift : (SeedFrac F)[X]) where
  root : Fin (2 * h) → F
  side : Fin (2 * h) → Fin 2
  a : Fin (2 * h) → F
  b : Fin (2 * h) → F
  c : Fin (2 * h) → F
  distinct : Function.Injective root
  factorization : H = ∏ t, (Polynomial.X (R := F) - Polynomial.C (root t))
  vanishes : ∀ t, H.eval (root t) = 0
  simple : ∀ t, H.derivative.eval (root t) ≠ 0
  b_ne : ∀ t, b t ≠ 0
  centre : ∀ t, lift.eval (algebraMap F (SeedFrac F) (root t)) =
    residue (side t) (a t) (b t) (c t)
abbrev Parameter := L[X]
abbrev GenericField := AlgebraicClosure (FractionRing Parameter)
def specialPoint : Parameter →+* L := Polynomial.evalRingHom 0
def genericPoint : Parameter →+* GenericField :=
  (algebraMap (FractionRing Parameter) GenericField).comp
    (algebraMap Parameter (FractionRing Parameter))
def liftAt {F : Type} [Field F] (point : Parameter →+* F) (num : (Seed Parameter)[X])
    (den : Seed Parameter) : (SeedFrac F)[X] :=
  (algebraMap (Seed F) (SeedFrac F) (MvPolynomial.map point den))⁻¹ •
    num.map ((algebraMap (Seed F) (SeedFrac F)).comp (MvPolynomial.map point))
structure RegularDeformation {h : ℕ} (D : PoleData h) (Crt : CRTLift D) where
  H : Parameter[X]
  num : (Seed Parameter)[X]
  den : Seed Parameter
  monic : H.Monic
  specialH : H.map specialPoint = poleProduct D
  specialDen : MvPolynomial.map specialPoint den ≠ 0
  specialLift : liftAt specialPoint num den = crtPolynomial Crt
  genericDen : MvPolynomial.map genericPoint den ≠ 0
  genericPoles : SimplePoles h (H.map genericPoint) (liftAt genericPoint num den)
end
end K1_14_1_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
def readCoeff {F : Type} [Field F] (j i a : ℕ) (e : Exponent) :
    TrueSource F →ₗ[F] F where
  toFun P := sourceCoeff P j i a e
  map_add' P Q := by simp [sourceCoeff]
  map_smul' b P := by simp [sourceCoeff, Polynomial.coeff_smul]
theorem shaped_map {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {s : Shape} {P : TrueSource R} (h : Shaped s P) :
    Shaped s (mapSource f P) := by
  intro j i a e hne
  apply h j i a e
  intro hz
  apply hne
  simpa [sourceCoeff, mapSource, Polynomial.coeff_map, MvPolynomial.coeff_map] using
    (congrArg f hz).trans (map_zero f)
theorem shaped_combination {F ι : Type} [Field F] [Fintype ι]
    {s : Shape} {P : ι → TrueSource F} (hP : ∀ i, Shaped s (P i)) (v : ι → F) :
    Shaped s (Fintype.linearCombination F P v) := by
  intro j i a e hne
  by_contra hbad
  apply hne
  change readCoeff j i a e (Fintype.linearCombination F P v) = 0
  rw [Fintype.linearCombination_apply, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  have he : sourceCoeff (P k) j i a e = 0 := by
    by_contra hz
    exact hbad (hP k j i a e hz)
  rw [map_smul]
  change v k • sourceCoeff (P k) j i a e = 0
  rw [he, smul_zero]
private abbrev CoeffBox (B M U : ℕ) :=
  Fin (B + 1) × Fin (B + 1) × Fin (M + 1) × (Fin 2 → Fin (U + 1))
theorem contacted_finite (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) :
    Module.Finite L (contacted h word s W) := by
  classical
  let M := W + (s.B+s.J)*(2*h) + s.J
  let f : contacted h word s W →ₗ[L] (CoeffBox s.B M s.U → L) :=
    LinearMap.pi fun u =>
      (readCoeff u.1.val u.2.1.val u.2.2.1.val
        (Finsupp.equivFunOnFinite.symm fun k => (u.2.2.2 k).val)).comp
          (contacted h word s W).subtype
  have hzero (Q : contacted h word s W) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    have hA : P ∈ ambient h s W := hP.1
    apply Subtype.ext
    change P = 0
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_zero]
    apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_zero]
    apply Polynomial.ext
    intro a
    rw [Polynomial.coeff_zero]
    apply MvPolynomial.ext
    intro e
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    change coeffAt P j i a e = 0
    by_cases he : trueEligible h s W j i a e
    · obtain ⟨hB, hJ, hU, hW⟩ := he
      have hM : a ≤ M := by dsimp [M]; omega
      have hU' (k : Fin 2) : e k ≤ s.U := by
        apply le_trans _ hU
        rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      let u : CoeffBox s.B M s.U :=
        (⟨j, by omega⟩, ⟨i, by omega⟩, ⟨a, by omega⟩,
          fun k => ⟨e k, Nat.lt_succ_of_le (hU' k)⟩)
      have hz := congrFun hQ u
      change coeffAt P j i a (Finsupp.equivFunOnFinite.symm (fun k => e k)) = 0 at hz
      exact (Finsupp.equivFunOnFinite.symm_apply_apply e) ▸ hz
    · exact hA j i a e he
  apply Module.Finite.of_injective f
  intro P Q hPQ
  apply sub_eq_zero.mp
  exact hzero (P - Q) (by rw [map_sub, hPQ, sub_self])
theorem contacted_shaped {h : ℕ} {word : I → L} {s : Shape} {W : ℕ}
    {P : Source} (hP : P ∈ contacted h word s W) : Shaped s P := by
  intro j i a e hn
  have he : trueEligible h s W j i a e := by
    by_contra hf
    exact hn (hP.1 j i a e hf)
  exact ⟨he.1, he.2.1, he.2.2.1⟩
private abbrev WindowSlots (U d : ℕ) :=
  Σ k : Fin (U + 1), Fin (d + k.val + 1)
private def windowExponent {U d : ℕ} (side : Fin 2) (k : WindowSlots U d) : Exponent :=
  Finsupp.equivFunOnFinite.symm (fun t => if t = side then k.2.val else U - k.1.val)
private theorem windowCoeff_card (U d : ℕ) :
    Fintype.card (WindowSlots U d) = triangle U + (U+1)*d := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp_rw [show ∀ k : Fin (U+1), d + k.val + 1 = (k.val + 1) + d by omega]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k + 1)]
  have hsum := Finset.sum_range_id (U+2)
  rw [Finset.sum_range_succ'] at hsum
  simpa [triangle, Nat.mul_comm (U+2) (U+1), Nat.add_comm 1] using hsum
theorem seedWindow_read (F : Type) [Field F] (U d : ℕ) (side : Fin 2) :
    ∃ read : Seed F →ₗ[F] (Fin (triangle U + (U+1)*d) → F),
      ∀ g, SeedWindow U d side g → read g = 0 → g = 0 := by
  classical
  let eq := Fintype.equivFinOfCardEq (windowCoeff_card U d)
  let read : Seed F →ₗ[F] (Fin (triangle U + (U+1)*d) → F) :=
    LinearMap.pi fun k => MvPolynomial.lcoeff F (windowExponent side (eq.symm k))
  refine ⟨read, ?_⟩
  intro g hg hzero
  apply MvPolynomial.ext
  intro e
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hn
  obtain ⟨ho, ht⟩ := hg e hn
  let k : WindowSlots U d :=
    ⟨⟨U - e (otherBlock side), by omega⟩, ⟨e side, by dsimp; omega⟩⟩
  have he : windowExponent side k = e := by
    ext t
    simp only [windowExponent, Finsupp.coe_equivFunOnFinite_symm]
    by_cases hts : t = side
    · simp [hts, k]
    · have hto : t = otherBlock side := by
        fin_cases t <;> fin_cases side <;> simp_all [otherBlock]
      rw [ite_eq_right hts, hto]
      exact Nat.sub_sub_self ho
  have hz := congrFun hzero (eq k)
  change g.coeff (windowExponent side (eq.symm (eq k))) = 0 at hz
  rw [eq.symm_apply_apply, he] at hz
  exact hn hz
end
end K1_14_1_7
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_1_3
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial
def c1 : Prop :=
  ∀ h (D : PoleData h) (word : I → L) s, ∀ Q ∈ physical word s, ∀ i r,
    cleared D i r Q ∈ physical word s
def c2 : Prop :=
  ∀ h (D : PoleData h) (Crt : CRTLift D) s, ∀ Q ∈ poleSpace Crt s, ∀ i r,
    cleared D i r Q ∈ poleSpace Crt s
private def evaluatedHasse (i : Fin 2) (r : ℕ) : Jet →ₗ[FX] Jet :=
  mapCoeffs (mapCoeffs (seedCoeff i r))
private theorem evaluatedHasse_eq (i : Fin 2) (r : ℕ) (P : Jet) :
    evaluatedHasse i r P = seedHasse i r P := rfl
private theorem translation_natural {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (i : Fin 2) (P : MvPolynomial (Fin 2) R) :
    (translation i P).map (MvPolynomial.map f) = translation i (MvPolynomial.map f P) := by
  let a := (Polynomial.mapRingHom (MvPolynomial.map f)).comp (translation (R := R) i).toRingHom
  let b := (translation (R := S) i).toRingHom.comp (MvPolynomial.map f)
  have hab : a = b := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [a, b, translation, MvPolynomial.algebraMap_eq]
    · intro j
      by_cases hj : j = i <;> simp [a, b, translation, hj]
  exact DFunLike.congr_fun hab P
private theorem seedCoeff_natural {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (i : Fin 2) (r : ℕ) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (seedCoeff i r P) = seedCoeff i r (MvPolynomial.map f P) := by
  change MvPolynomial.map f ((translation i P).coeff r) =
    (translation i (MvPolynomial.map f P)).coeff r
  rw [← coeff_map, translation_natural]
private def ξ : FX := algebraMap (Polynomial L) FX (Polynomial.X (R := L))
private def centerBase : SeedPoly[X] →ₐ[L] Seeds :=
  eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
    (MvPolynomial.C ξ) (fun _ => Commute.all _ _)
private theorem centerBase_hasse (i : Fin 2) (r : ℕ) (Q : SeedPoly[X]) :
    centerBase (mapCoeffs (seedCoeff i r) Q) = seedCoeff i r (centerBase Q) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq =>
    rw [map_add, map_add, map_add, map_add, hp, hq]
  | monomial n a =>
    rw [mapCoeffs_monomial]
    change (monomial n (seedCoeff i r a)).eval₂ (MvPolynomial.map (algebraMap L FX))
      (MvPolynomial.C ξ) = seedCoeff i r
      ((monomial n a).eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ))
    rw [eval₂_monomial, eval₂_monomial, ← map_pow]
    simp only [mul_comm _ (MvPolynomial.C (ξ ^ n)), ← MvPolynomial.smul_eq_C_mul,
      map_smul, seedCoeff_natural]
private theorem centerEval_hasse (i : Fin 2) (r : ℕ) (Q : Source) :
    centerEval (sourceHasse i r Q) = evaluatedHasse i r (centerEval Q) := by
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro k
  change ((Polynomial.mapAlgHom (Polynomial.mapAlgHom centerBase)
    (sourceHasse i r Q)).coeff j).coeff k =
      ((evaluatedHasse i r (Polynomial.mapAlgHom (Polynomial.mapAlgHom centerBase) Q)).coeff j).coeff k
  simp only [sourceHasse, evaluatedHasse, coeff_mapAlgHom_apply, mapCoeffs_coeff]
  exact centerBase_hasse i r ((Q.coeff j).coeff k)
private theorem centerBase_sourceX (E : L[X]) :
    centerBase (sourceX E) = MvPolynomial.C (algebraMap L[X] FX E) := by
  change (E.map MvPolynomial.C).eval₂ (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C ξ) = _
  rw [eval₂_map]
  have hc : (MvPolynomial.map (algebraMap L FX)).comp
      (MvPolynomial.C : L →+* SeedPoly) = MvPolynomial.C.comp (algebraMap L FX) := by
    ext a
    simp
  rw [hc]
  exact eval₂_algebraMap_X E
    ((IsScalarTower.toAlgHom L FX Seeds).comp (IsScalarTower.toAlgHom L L[X] FX))
private theorem centerEval_clear {h : ℕ} (D : PoleData h) (i : Fin 2) (r : ℕ) (Q : Source) :
    centerEval (cleared D i r Q) =
      (algebraMap L[X] FX (D.block i ^ (2*r))) • evaluatedHasse i r (centerEval Q) := by
  rw [cleared, map_mul, centerEval_hasse]
  change Polynomial.map (Polynomial.mapRingHom centerBase.toRingHom)
    (C (C (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [Polynomial.map_C]
  change C (Polynomial.map centerBase.toRingHom (C (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [Polynomial.map_C]
  change C (C (centerBase (sourceX (D.block i ^ (2*r))))) * _ = _
  rw [centerBase_sourceX, Algebra.smul_def]
  rfl
end
end K1_14_1_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7
noncomputable section
open K1_14 Polynomial
theorem specialization_rank_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) Parameter) :
    (M.map specialPoint).rank ≤ (M.map genericPoint).rank := by
  classical
  let B := M.map specialPoint
  let f := B.mulVecLin
  let k := B.rank
  let e : LinearMap.range f ≃ₗ[L] (Fin k → L) :=
    (Module.finBasis L (LinearMap.range f)).equivFun
  obtain ⟨right, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨left, hl⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective
    (LinearMap.range f).ker_subtype
  let U : Matrix (Fin k) (Fin m) L := (e.toLinearMap.comp left).toMatrix'
  let V : Matrix (Fin n) (Fin k) L := (right.comp e.symm.toLinearMap).toMatrix'
  have hB : U * B * V = 1 := by
    apply (Matrix.toLin' (R := L)).injective
    rw [Matrix.toLin'_one, Matrix.toLin'_mul, Matrix.toLin'_mul]
    simp only [U, V, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    change e (left (f (right (e.symm v)))) = v
    have hright := LinearMap.congr_fun hr (e.symm v)
    have hleft := LinearMap.congr_fun hl (e.symm v)
    change f.rangeRestrict (right (e.symm v)) = e.symm v at hright
    change left (f.range.subtype (e.symm v)) = e.symm v at hleft
    change e (left (f.range.subtype (f.rangeRestrict (right (e.symm v))))) = v
    rw [hright, hleft, e.apply_symm_apply]
  let U₀ := U.map (Polynomial.C (R := L))
  let V₀ := V.map (Polynomial.C (R := L))
  let S := U₀ * M * V₀
  have hS : S.map specialPoint = 1 := by
    rw [Matrix.map_mul, Matrix.map_mul]
    have hU : U₀.map specialPoint = U := by
      ext i j
      simp [U₀, Matrix.map_apply, specialPoint]
    have hV : V₀.map specialPoint = V := by
      ext i j
      simp [V₀, Matrix.map_apply, specialPoint]
    rw [hU, hV]
    exact hB
  have hdet : S.det ≠ 0 := by
    intro hz
    have he := specialPoint.map_det S
    change specialPoint S.det = (S.map specialPoint).det at he
    rw [hS, hz, map_zero, Matrix.det_one] at he
    exact zero_ne_one he
  have hg : (S.map genericPoint).det ≠ 0 := by
    change (genericPoint.mapMatrix S).det ≠ 0
    rw [← genericPoint.map_det]
    have hinj : Function.Injective genericPoint :=
      (algebraMap (FractionRing Parameter) GenericField).injective.comp
        (IsFractionRing.injective Parameter (FractionRing Parameter))
    intro hz
    exact hdet (hinj (hz.trans (map_zero genericPoint).symm))
  calc
    B.rank = (S.map genericPoint).rank := by
      rw [Matrix.rank_of_det_ne_zero hg, Fintype.card_fin]
    _ ≤ (M.map genericPoint).rank := by
      rw [Matrix.map_mul, Matrix.map_mul]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
end
end K1_14_1_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
def c1 : Prop :=
  ∀ (F : Type) [Field F] (s : Shape) (q : Grade s),
    ∃ rows : ZeroRows F s q.val, ZeroRowsValid s q.val rows
def c2 : Prop :=
  ∀ (F : Type) [Field F] (s : Shape) (H : F[X]) (lift : (SeedFrac F)[X])
    (α : F) (side : Fin 2) (a b c : F),
    H.eval α = 0 → H.derivative.eval α ≠ 0 → b ≠ 0 →
    lift.eval (algebraMap F (SeedFrac F) α) = residue side a b c →
    ∀ rows : (q : Grade s) → ZeroRows F s q.val,
      (∀ q, ZeroRowsValid s q.val (rows q)) →
      ∃ tests : (q : Grade s) → LocalRow s q.val → TrueSource F →ₗ[F] Seed F,
        (∀ q r P, Shaped s P → SeedWindow s.U (s.B - q.val) side (tests q r P)) ∧
        ∀ P, Shaped s P → (∀ q r, tests q r P = 0) →
          (jetConstant ((Polynomial.X (R := SeedFrac F) -
              Polynomial.C (algebraMap F (SeedFrac F) α)) ^ (s.B+s.J)) :
            JetPolys (SeedFrac F)) ∣ forward H lift P
def c4 : Prop :=
  ∀ {h : ℕ} {D : PoleData h} {Crt : CRTLift D} (E : RegularDeformation D Crt)
    (s : Shape) (ι : Type) [Fintype ι] (P : ι → Source),
    (∀ k, Shaped s (P k)) →
    ∃ n : ℕ, ∃ M : Matrix (Fin n) ι Parameter,
      (∀ v : ι → L, (M.map specialPoint).mulVec v = 0 ↔
        PoleTest s (poleProduct D) (crtPolynomial Crt) (Fintype.linearCombination L P v)) ∧
      ∀ v : ι → GenericField, (M.map genericPoint).mulVec v = 0 ↔
        PoleTest s (E.H.map genericPoint) (liftAt genericPoint E.num E.den)
          (Fintype.linearCombination GenericField (fun k => mapSource (genericPoint.comp (Polynomial.C (R := L))) (P k)) v)
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
private theorem simple_rank_le (h1 : c1) (h2 : c2)
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
end
end K1_14_1_7
end
section
namespace K1_14_1_3_2
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
def seriesPolynomial {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* PowerSeries B) : A[X] →+* PowerSeries (B[X]) :=
  eval₂RingHom ((PowerSeries.map Polynomial.C).comp f) (PowerSeries.C Polynomial.X)
@[simp] theorem seriesPolynomial_C {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* PowerSeries B) (a : A) :
    seriesPolynomial f (C a) = PowerSeries.map Polynomial.C (f a) :=
  eval₂_C _ _
@[simp] theorem seriesPolynomial_X {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* PowerSeries B) :
    seriesPolynomial f Polynomial.X = PowerSeries.C Polynomial.X :=
  eval₂_X _ _
theorem seriesPolynomial_coeff {A B R : Type*} [CommSemiring A] [CommSemiring B]
    [Semiring R] [Module R A] [Module R B]
    (f : A →+* PowerSeries B) (g : A →ₗ[R] B) (r : ℕ)
    (hg : ∀ a, PowerSeries.coeff r (f a) = g a) (P : A[X]) :
    PowerSeries.coeff r (seriesPolynomial f P) = mapCoeffs g P := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    rw [mapCoeffs_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, seriesPolynomial_C,
      seriesPolynomial_X, ← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_map, hg,
      C_mul_X_pow_eq_monomial]
theorem seriesPolynomial_fixed {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : B →+* PowerSeries B) (g : A →+* B)
    (hf : ∀ a, f (g a) = PowerSeries.C (g a)) (P : A[X]) :
    seriesPolynomial f (P.map g) = PowerSeries.C (P.map g) := by
  have he : (seriesPolynomial f).comp (Polynomial.mapRingHom g) =
      PowerSeries.C.comp (Polynomial.mapRingHom g) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [hf]
    · simp
  exact DFunLike.congr_fun he P
theorem seriesPolynomial_constantCoeff {A : Type*} [CommSemiring A]
    (f : A →+* PowerSeries A) (hf : ∀ a, PowerSeries.constantCoeff (f a) = a)
    (P : A[X]) : PowerSeries.constantCoeff (seriesPolynomial f P) = P := by
  have he : PowerSeries.constantCoeff.comp (seriesPolynomial f) = RingHom.id A[X] := by
    apply Polynomial.ringHom_ext
    · intro a
      have hfa : PowerSeries.coeff 0 (f a) = a :=
        (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (hf a)
      simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hfa]
    · simp
  exact DFunLike.congr_fun he P
def sourceSeedShift (i : Fin 2) : SeedPoly →+* PowerSeries SeedPoly :=
  Polynomial.coeToPowerSeries.ringHom.comp (translation i).toRingHom
def sourceShift (i : Fin 2) : Source →+* PowerSeries Source :=
  seriesPolynomial (seriesPolynomial (seriesPolynomial (sourceSeedShift i)))
theorem sourceShift_coeff (i : Fin 2) (r : ℕ) (Q : Source) :
    PowerSeries.coeff r (sourceShift i Q) = sourceHasse i r Q := by
  unfold sourceShift sourceHasse
  apply seriesPolynomial_coeff (R := L)
  intro P
  apply seriesPolynomial_coeff (R := L)
  intro p
  apply seriesPolynomial_coeff (R := L)
  intro a
  exact Polynomial.coeff_coe (φ := translation i a) r
def genericSeedShift (i : Fin 2) : SeedPoly →+* PowerSeries SeedField :=
  (PowerSeries.map (algebraMap SeedPoly SeedField)).comp (sourceSeedShift i)
theorem genericSeedShift_constantCoeff (i : Fin 2) (P : SeedPoly) :
    PowerSeries.constantCoeff (genericSeedShift i P) = algebraMap SeedPoly SeedField P := by
  have he : PowerSeries.constantCoeff.comp (genericSeedShift i) =
      algebraMap SeedPoly SeedField := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [genericSeedShift, sourceSeedShift, translation, MvPolynomial.algebraMap_eq]
    · intro j
      by_cases hj : j = i <;> simp [genericSeedShift, sourceSeedShift, translation, hj]
  exact DFunLike.congr_fun he P
def seedShift (i : Fin 2) : SeedField →+* PowerSeries SeedField :=
  IsLocalization.lift (M := nonZeroDivisors SeedPoly) (S := SeedField)
    (g := genericSeedShift i) fun a =>
      PowerSeries.isUnit_iff_constantCoeff.mpr (by
        rw [genericSeedShift_constantCoeff, isUnit_iff_ne_zero]
        simpa only [map_zero] using
          (IsFractionRing.injective SeedPoly SeedField).ne (nonZeroDivisors.ne_zero a.prop))
@[simp] theorem seedShift_algebraMap (i : Fin 2) (a : SeedPoly) :
    seedShift i (algebraMap SeedPoly SeedField a) = genericSeedShift i a :=
  IsLocalization.lift_eq _ _
theorem seedShift_constantCoeff (i : Fin 2) (a : SeedField) :
    PowerSeries.constantCoeff (seedShift i a) = a := by
  have he : PowerSeries.constantCoeff.comp (seedShift i) = RingHom.id SeedField := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors SeedPoly)
    apply RingHom.ext
    intro P
    simp [genericSeedShift_constantCoeff]
  exact DFunLike.congr_fun he a
theorem seedShift_base (i : Fin 2) (a : L) :
    seedShift i (algebraMap L SeedField a) = PowerSeries.C (algebraMap L SeedField a) := by
  rw [IsScalarTower.algebraMap_apply L SeedPoly SeedField, seedShift_algebraMap]
  simp [genericSeedShift, sourceSeedShift, translation, MvPolynomial.algebraMap_eq]
theorem seedShift_other (i j : Fin 2) (hji : j ≠ i) (P : L[X]) :
    seedShift i (seedInField j P) = PowerSeries.C (seedInField j P) := by
  have he : (seedShift i).comp (seedInField j).toRingHom =
      PowerSeries.C.comp (seedInField j).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change seedShift i (seedInField j (C a)) = PowerSeries.C (seedInField j (C a))
      simpa [seedInField] using seedShift_base i a
    · change seedShift i (seedInField j Polynomial.X) = PowerSeries.C (seedInField j Polynomial.X)
      simp [seedInField, genericSeedShift, sourceSeedShift, translation, hji]
  exact DFunLike.congr_fun he P
theorem seedShift_inv_fixed (i : Fin 2) (a : SeedField)
    (ha : seedShift i a = PowerSeries.C a) :
    seedShift i a⁻¹ = PowerSeries.C a⁻¹ := by
  by_cases hz : a = 0
  · simp [hz]
  apply (isUnit_iff_ne_zero.mpr hz |>.map (PowerSeries.C (R := SeedField))).mul_left_cancel
  rw [← ha, ← map_mul, mul_inv_cancel₀ hz, map_one, ha, ← map_mul, mul_inv_cancel₀ hz, map_one]
theorem rescale_C {R : Type*} [CommSemiring R] (a b : R) :
    PowerSeries.rescale a (PowerSeries.C b) = PowerSeries.C b := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [PowerSeries.coeff_C]
theorem rescale_difference {R : Type*} [CommRing R] (a b : R)
    (F : PowerSeries R) (hF : PowerSeries.constantCoeff F = b) :
    ∃ B, PowerSeries.rescale a F = PowerSeries.C b + PowerSeries.C a * B := by
  have hd : (PowerSeries.X : PowerSeries R) ∣ F - PowerSeries.C b := by
    rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, hF, sub_self]
  obtain ⟨U, hU⟩ := hd
  have he := congrArg (PowerSeries.rescale a) hU
  rw [map_sub, rescale_C, map_mul, PowerSeries.rescale_X, mul_assoc] at he
  exact ⟨PowerSeries.X * PowerSeries.rescale a U, by rw [← he]; ring⟩
end
end K1_14_1_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_3
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
def movingBlock {h : ℕ} (D : PoleData h) (i : Fin 2) : Parameter[X] :=
  (D.block i).map C + C (Polynomial.X (R := L))
def movingProduct {h : ℕ} (D : PoleData h) : Parameter[X] :=
  movingBlock D 0 * movingBlock D 1
theorem movingBlock_spec {h : ℕ} (D : PoleData h) (i : Fin 2) :
    (movingBlock D i).map specialPoint = D.block i := by
  have hc : specialPoint.comp (C (R := L)) = RingHom.id L :=
    RingHom.ext fun a => eval_C
  rw [movingBlock, Polynomial.map_add, map_map, hc, map_id, Polynomial.map_C]
  simp [specialPoint]
theorem movingBlock_degree {h : ℕ} (hh : 0 < h) (D : PoleData h) (i : Fin 2) :
    IsMonicOfDegree (movingBlock D i) h := by
  have hb : IsMonicOfDegree ((D.block i).map (C (R := L))) h :=
    ⟨((D.monic i).natDegree_map _).trans (D.degree i), (D.monic i).map _⟩
  exact hb.add_right (by simpa using hh)
theorem generic_injective : Function.Injective genericPoint :=
  (algebraMap (FractionRing Parameter) GenericField).injective.comp
    (IsFractionRing.injective Parameter (FractionRing Parameter))
abbrev constGeneric : L →+* GenericField := genericPoint.comp (C (R := L))
abbrev genericBlock {h : ℕ} (D : PoleData h) (i : Fin 2) : GenericField[X] :=
  (movingBlock D i).map genericPoint
private theorem genericBlock_eq {h : ℕ} (D : PoleData h) (i : Fin 2) :
    genericBlock D i = (D.block i).map constGeneric + C (genericPoint Polynomial.X) := by
  unfold genericBlock movingBlock
  rw [Polynomial.map_add, map_map, Polynomial.map_C]
theorem other_invol (i : Fin 2) : otherBlock (otherBlock i) = i := by
  fin_cases i <;> decide
theorem sum_other {R : Type*} [AddCommMonoid R] (f : Fin 2 → R) (i : Fin 2) :
    (∑ j, f j) = f i + f (otherBlock i) := by
  rw [Fin.sum_univ_two]
  fin_cases i
  · rfl
  · exact add_comm _ _
theorem coprime_other {h : ℕ} (D : PoleData h) (i : Fin 2) :
    IsCoprime (D.block i) (D.block (otherBlock i)) := by
  fin_cases i
  · exact D.coprime
  · exact D.coprime.symm
private theorem derivative_block_ne_zero {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p)
    (D : PoleData h) (i : Fin 2) : (D.block i).derivative ≠ 0 := by
  let _ : CharP L K1.p := charP_of_injective_ringHom (algebraMap K L).injective K1.p
  have hn : (h : L) ≠ 0 := fun hz =>
    (not_le_of_gt hhi) (Nat.le_of_dvd hlo ((CharP.cast_eq_zero_iff _ _ _).mp hz))
  intro hd
  have he := congrArg (fun f : L[X] => f.coeff (h - 1)) hd
  have hh : h - 1 + 1 = h := by omega
  have hlead : (D.block i).coeff h = 1 := by
    simpa only [← coeff_natDegree, D.degree i] using (D.monic i).leadingCoeff
  rw [coeff_derivative, hh, hlead, one_mul, coeff_zero] at he
  have hcast : ((h - 1 : ℕ) : L) + 1 = (h : L) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : L)) hh
  exact hn (hcast.symm.trans he)
private theorem root_not_const {h : ℕ} (D : PoleData h) (i : Fin 2) (x : L) :
    (genericBlock D i).eval (constGeneric x) ≠ 0 := by
  rw [genericBlock_eq, eval_add, eval_map_apply, eval_C]
  change genericPoint (C ((D.block i).eval x)) + genericPoint Polynomial.X ≠ 0
  rw [← map_add, ← map_zero K1_14_1_7.genericPoint]
  intro he
  have hc := congrArg (fun P : Parameter => P.coeff 1) (generic_injective he)
  simp at hc
private theorem fixed_eval_ne_zero {h : ℕ} (D : PoleData h) (i : Fin 2)
    {α : GenericField} (hr : (genericBlock D i).eval α = 0)
    {f : L[X]} (hf : f ≠ 0) : (f.map constGeneric).eval α ≠ 0 := by
  intro he
  obtain ⟨x, rfl⟩ := (IsAlgClosed.splits f).mem_range_of_isRoot hf he
  exact root_not_const D i x hr
private theorem other_eval_ne_zero {h : ℕ} (hh : 0 < h) (D : PoleData h)
    (i : Fin 2) {α : GenericField} (hr : (genericBlock D i).eval α = 0) :
    (genericBlock D (otherBlock i)).eval α ≠ 0 := by
  have hdiff : D.block i - D.block (otherBlock i) ≠ 0 := by
    intro he
    have hu := coprime_other D i
    rw [← sub_eq_zero.mp he] at hu
    exact not_isUnit_of_natDegree_pos _ (by simpa [D.degree] using hh) (isCoprime_self.mp hu)
  intro ho
  apply fixed_eval_ne_zero D i hr hdiff
  rw [Polynomial.map_sub, eval_sub]
  rw [genericBlock_eq, eval_add, eval_C] at hr ho
  exact sub_eq_zero.mpr (add_right_cancel (hr.trans ho.symm))
private theorem deriv_eval_ne_zero {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p)
    (D : PoleData h) (i : Fin 2) {α : GenericField}
    (hr : (genericBlock D i).eval α = 0) : (genericBlock D i).derivative.eval α ≠ 0 := by
  rw [genericBlock_eq, derivative_add, derivative_C, add_zero, derivative_map]
  exact fixed_eval_ne_zero D i hr (derivative_block_ne_zero hlo hhi D i)
private theorem constant_eval_ne_zero {h : ℕ} (hh : 0 < h) (D : PoleData h)
    (i : Fin 2) {α : GenericField} (hr : (genericBlock D i).eval α = 0) :
    ((D.constant i).map constGeneric).eval α ≠ 0 := by
  refine fixed_eval_ne_zero D i hr ?_
  intro he
  have hc := (D.determinant i).of_mul_left_right
  rw [he, isCoprime_zero_left] at hc
  exact not_isUnit_of_natDegree_pos _ (by simpa [D.degree] using hh) hc
def simplePoles {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p) (D : PoleData h)
    (lift : (SeedFrac GenericField)[X])
    (hcentre : ∀ i α, (genericBlock D i).eval α = 0 →
      ((D.constant i).map constGeneric).eval α ≠ 0 →
      lift.eval (algebraMap GenericField (SeedFrac GenericField) α) =
        residue i (-((D.offset i).map constGeneric).eval α)
          (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α)) :
    SimplePoles h ((movingProduct D).map genericPoint) lift := by
  classical
  let H := (movingProduct D).map genericPoint
  have hblocks : H = genericBlock D 0 * genericBlock D 1 := by
    simp only [H, movingProduct, Polynomial.map_mul]
  have hmonic : H.Monic :=
    (((movingBlock_degree hlo D 0).monic.mul (movingBlock_degree hlo D 1).monic).map _)
  have hdegree : H.natDegree = 2 * h := by
    have hd (i : Fin 2) : (genericBlock D i).natDegree = h :=
      ((movingBlock_degree hlo D i).monic.natDegree_map _).trans
        (movingBlock_degree hlo D i).natDegree_eq
    have hm (i : Fin 2) : (genericBlock D i).Monic :=
      (movingBlock_degree hlo D i).monic.map _
    rw [hblocks, natDegree_mul (hm 0).ne_zero (hm 1).ne_zero, hd, hd]
    omega
  have hside (α : GenericField) (hr : H.eval α = 0) :
      ∃ i, (genericBlock D i).eval α = 0 := by
    rw [hblocks, eval_mul, mul_eq_zero] at hr
    exact hr.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
  have hsimple (α : GenericField) (hr : H.eval α = 0) : H.derivative.eval α ≠ 0 := by
    obtain ⟨i, hi⟩ := hside α hr
    have hn := deriv_eval_ne_zero hlo hhi D i hi
    have ho := other_eval_ne_zero hlo D i hi
    rw [hblocks, derivative_mul, eval_add, eval_mul, eval_mul]
    fin_cases i
    · change (genericBlock D 0).eval α = 0 at hi
      change (genericBlock D 1).eval α ≠ 0 at ho
      rw [hi, zero_mul, add_zero]
      exact mul_ne_zero hn ho
    · change (genericBlock D 1).eval α = 0 at hi
      change (genericBlock D 0).eval α ≠ 0 at ho
      rw [hi, mul_zero, zero_add]
      exact mul_ne_zero ho hn
  have hsep : H.Separable := by
    apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed GenericField GenericField H H.derivative).mpr
    intro α
    by_cases he : H.eval α = 0
    · exact Or.inr (by simpa using hsimple α he)
    · exact Or.inl (by simpa using he)
  let s := H.roots.toFinset
  have hcard : Fintype.card s = 2 * h := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      ← (IsAlgClosed.splits H).natDegree_eq_card_roots, hdegree]
  let e : Fin (2 * h) ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  let α : Fin (2 * h) → GenericField := fun t => (e t).val
  have hroot (t : Fin (2 * h)) : H.eval (α t) = 0 :=
    (mem_roots hmonic.ne_zero).mp (Multiset.mem_toFinset.mp (e t).property)
  choose i hi using fun t => hside (α t) (hroot t)
  refine ⟨α, i, _, _, _, Subtype.val_injective.comp e.injective, ?_, hroot,
    fun t => hsimple _ (hroot t), fun t => constant_eval_ne_zero hlo D _ (hi t),
    fun t => hcentre _ _ (hi t) (constant_eval_ne_zero hlo D _ (hi t))⟩
  rw [e.prod_comp (fun x => Polynomial.X - C x.val)]
  rw [Finset.prod_coe_sort s (fun x => Polynomial.X - C x)]
  have hs : s.val = H.roots := by
    exact (Multiset.toFinset_val _).trans (nodup_roots hsep).dedup
  simpa only [Finset.prod, hs] using (IsAlgClosed.splits H).eq_prod_roots_of_monic hmonic
end
end K1_14_1_7_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
def substitute {R A : Type*} [CommSemiring R] [CommSemiring A]
    (base : R →+* A) (y v : A) : R[X][X] →+* A :=
  eval₂RingHom (eval₂RingHom base y) v
def centered {F : Type} [Field F] (α : F) (z : SeedFrac F) :
    TrueSource F →+* JetPolys (SeedFrac F) :=
  let xα := algebraMap F (SeedFrac F) α
  let coeffs := (Polynomial.taylorAlgHom xα).toRingHom.comp
    (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F)))
  substitute (jetConstant.comp coeffs)
    (Polynomial.C Polynomial.X + jetConstant (Polynomial.C z)) Polynomial.X
def zeroSubst {R : Type} [CommSemiring R] : JetPolys R →+* JetPolys R :=
  let x := jetConstant (Polynomial.X (R := R))
  let y : JetPolys R := Polynomial.C Polynomial.X
  substitute jetConstant (x * y) (x * Polynomial.X + y)
def packGrades {R : Type} [CommSemiring R] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → R[X]) : JetPolys R :=
  ∑ q : Grade s, ∑ j : GradeSlot s q.val,
    Polynomial.C (Polynomial.C (f q j) * Polynomial.X ^ (q.val - j.val)) *
      Polynomial.X ^ j.val
abbrev Shift (s : Shape) (q : Grade s) := Fin (s.B - q.val + 1)
def inputOrdinate {s : Shape} (q : Grade s) (j : GradeSlot s q.val)
    (p : Shift s q) : ℕ :=
  q.val - j.val + p.val
def inputTaylor {F : Type} [Field F] (α : F) (P : TrueSource F) (j i : ℕ) : (Seed F)[X] :=
  Polynomial.taylor (algebraMap F (Seed F) α) ((P.coeff j).coeff i)
def localSlots {F : Type} [Field F] (s : Shape) (α : F) (z : SeedFrac F)
    (P : TrueSource F) (q : Grade s) (j : GradeSlot s q.val) : (SeedFrac F)[X] :=
  ∑ p : Shift s q,
    Polynomial.C ((Nat.choose (inputOrdinate q j p) (q.val - j.val) : SeedFrac F) * z ^ p.val) *
      (inputTaylor α P j.val (inputOrdinate q j p)).map (algebraMap (Seed F) (SeedFrac F))
def inputTaylorCoeff {F : Type} [Field F] (α : F) (j i t : ℕ) :
    TrueSource F →ₗ[F] Seed F :=
  ((Polynomial.lcoeff (Seed F) t).restrictScalars F).comp
    (((Polynomial.taylor (algebraMap F (Seed F) α)).restrictScalars F).comp
      (((Polynomial.lcoeff ((Seed F)[X]) i).restrictScalars F).comp
        ((Polynomial.lcoeff (((Seed F)[X])[X]) j).restrictScalars F)))
end
end K1_14_1_7_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_3
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Module Polynomial
open scoped Polynomial
private def quotientBasis {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) : Basis (Fin n) R (AdjoinRoot b) :=
  (AdjoinRoot.powerBasisAux' hb).reindex (finCongr hd)
private def mulMatrix {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : R[X]) : Matrix (Fin n) (Fin n) R :=
  Algebra.leftMulMatrix (quotientBasis hb hd) (AdjoinRoot.mk b a)
private theorem mulMatrix_entry {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : R[X]) (i j : Fin n) :
    mulMatrix hb hd a i j = ((a * Polynomial.X (R := R) ^ (j : ℕ)) %ₘ b).coeff i := by
  have hpow (k : Fin b.natDegree) :
      (AdjoinRoot.powerBasisAux' hb) k = AdjoinRoot.root b ^ (k : ℕ) :=
    (AdjoinRoot.powerBasis' hb).basis_eq_pow k
  unfold mulMatrix
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  unfold quotientBasis
  rw [Basis.reindex_apply, hpow, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    Basis.repr_reindex_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  rfl
private theorem regularInverse {R S : Type*} [CommRing R] [Field S]
    (point : R →+* S) {b a : R[X]} (hb : b.Monic)
    (hcop : IsCoprime (a.map point) (b.map point)) :
    ∃ (d : R) (u : R[X]), point d ≠ 0 ∧ b ∣ a * u - C d := by
  let basis := quotientBasis hb rfl
  let M := mulMatrix hb rfl a
  let d := M.det
  let d' := (hb.natDegree_map point)
  have hmap : M.map point = mulMatrix (hb.map point) d' (a.map point) := by
    ext i j
    change point (mulMatrix hb rfl a i j) = _
    rw [mulMatrix_entry, mulMatrix_entry, ← coeff_map, map_modByMonic point hb,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  obtain ⟨v, w, hvw⟩ := hcop
  have hinv : AdjoinRoot.mk (b.map point) v * AdjoinRoot.mk (b.map point) (a.map point) = 1 := by
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] using
      congrArg (AdjoinRoot.mk (b.map point)) hvw
  have hmat : mulMatrix (hb.map point) d' v * M.map point = 1 := by
    rw [hmap]
    unfold mulMatrix
    rw [← map_mul, hinv, map_one]
  have hd : point d ≠ 0 := by
    have he := congrArg Matrix.det hmat
    rw [Matrix.det_mul, Matrix.det_one] at he
    change _ * (point.mapMatrix M).det = 1 at he
    rw [← point.map_det] at he
    intro hz
    change point M.det = 0 at hz
    rw [hz, mul_zero] at he
    exact zero_ne_one he
  let x := basis.equivFun.symm (M.cramer (basis.equivFun 1))
  have hsol : AdjoinRoot.mk b a * x = d • (1 : AdjoinRoot b) := by
    apply basis.equivFun.injective
    have hv := Algebra.leftMulMatrix_mulVec_repr basis (AdjoinRoot.mk b a) x
    change M.mulVec (basis.repr x) = ⇑(basis.repr (AdjoinRoot.mk b a * x)) at hv
    rw [← Basis.equivFun_apply, ← Basis.equivFun_apply,
      show basis.equivFun x = M.cramer (basis.equivFun 1) from basis.equivFun.apply_symm_apply _,
      Matrix.mulVec_cramer] at hv
    rw [map_smul]
    exact hv.symm
  obtain ⟨u, hu⟩ := AdjoinRoot.mk_surjective x
  refine ⟨d, u, hd, AdjoinRoot.mk_eq_zero.mp ?_⟩
  rw [map_sub, map_mul, hu, hsol, AdjoinRoot.mk_C, Algebra.smul_def, mul_one]
  exact sub_self _
abbrev specialSeed : Seed Parameter →+* Seed L := MvPolynomial.map specialPoint
private abbrev liftSeed : Seed L →+* Seed Parameter := MvPolynomial.map (C (R := L))
private theorem special_liftSeed : specialSeed.comp liftSeed = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> simp [RingHom.comp_apply, specialPoint]
private theorem map_liftSeed (f : (Seed L)[X]) :
    (f.map liftSeed).map specialSeed = f := by
  rw [map_map, special_liftSeed, map_id]
def seedEmbed {F : Type} [Field F] (point : Parameter →+* F) :
    Seed Parameter →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (MvPolynomial.map point)
theorem seedEmbed_ne_zero {F : Type} [Field F] (point : Parameter →+* F)
    {d : Seed Parameter} (hd : MvPolynomial.map point d ≠ 0) : seedEmbed point d ≠ 0 :=
  fun hz => hd ((IsFractionRing.injective (Seed F) (SeedFrac F))
    (hz.trans (map_zero (algebraMap (Seed F) (SeedFrac F))).symm))
private theorem cancel_scalar {F : Type*} [Field F] {a b : F} (ha : a ≠ 0)
    (P : F[X]) : C ((a * b)⁻¹) * (C a * P) = C (b⁻¹) * P := by
  rw [← mul_assoc, ← map_mul]
  congr 2
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ ha, mul_one]
theorem liftAt_add {F : Type} [Field F] (point : Parameter →+* F)
    (N M : (Seed Parameter)[X]) (d e : Seed Parameter)
    (hd : MvPolynomial.map point d ≠ 0) (he : MvPolynomial.map point e ≠ 0) :
    liftAt point (C e * N + C d * M) (d * e) =
      liftAt point N d + liftAt point M e := by
  simp only [liftAt, smul_eq_C_mul]
  change C ((seedEmbed point (d * e))⁻¹) * (C e * N + C d * M).map (seedEmbed point) =
    C ((seedEmbed point d)⁻¹) * N.map (seedEmbed point) +
    C ((seedEmbed point e)⁻¹) * M.map (seedEmbed point)
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_C, map_mul (seedEmbed point), mul_add]
  congr 1
  · rw [mul_comm (seedEmbed point d) (seedEmbed point e), cancel_scalar (seedEmbed_ne_zero point he)]
  · exact cancel_scalar (seedEmbed_ne_zero point hd) _
abbrev familyBlock {h : ℕ} (D : PoleData h) (i : Fin 2) : (Seed Parameter)[X] :=
  (movingBlock D i).map MvPolynomial.C
abbrev constSeed : L →+* Seed Parameter := MvPolynomial.C.comp (C (R := L))
def familyAmplitude {h : ℕ} (D : PoleData h) (i : Fin 2) : (Seed Parameter)[X] :=
  (D.constant i).map constSeed + C (MvPolynomial.X i) * (D.slope i).map constSeed
def familyOffset {h : ℕ} (D : PoleData h) (i : Fin 2) : (Seed Parameter)[X] :=
  C (MvPolynomial.X i) * (D.offset i).map constSeed
private theorem map_familyBlock {h : ℕ} (D : PoleData h) (i : Fin 2) :
    (familyBlock D i).map specialSeed = (D.block i).map MvPolynomial.C := by
  have hc : specialSeed.comp (MvPolynomial.C : Parameter →+* Seed Parameter) =
      (MvPolynomial.C : L →+* Seed L).comp specialPoint :=
    RingHom.ext fun x => MvPolynomial.map_C specialPoint x
  rw [familyBlock, map_map, hc, ← map_map, movingBlock_spec]
private theorem special_constSeed :
    specialSeed.comp constSeed = (MvPolynomial.C : L →+* Seed L) := by
  ext x
  simp [RingHom.comp_apply, specialPoint]
private def zeroSeeds : Seed L →+* L := MvPolynomial.eval fun _ => 0
private theorem zeroSeeds_constants (f : L[X]) :
    (f.map MvPolynomial.C).map zeroSeeds = f := by
  have h : zeroSeeds.comp MvPolynomial.C = RingHom.id L :=
    RingHom.ext fun c => MvPolynomial.eval_C _
  rw [map_map, h, map_id]
private def seedPolynomial (i : Fin 2) : L[X] →+* Seed L :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X i)
private theorem frac_seedPolynomial (i : Fin 2) :
    (algebraMap (Seed L) (SeedFrac L)).comp (seedPolynomial i) = (seedInField i).toRingHom := by
  apply Polynomial.ringHom_ext <;>
    simp [seedPolynomial, seedInField, aeval_def, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply L (Seed L) (SeedFrac L)]
private theorem zero_seedPolynomial (i : Fin 2) :
    zeroSeeds.comp (seedPolynomial i) = evalRingHom 0 := by
  apply Polynomial.ringHom_ext <;> simp [zeroSeeds, seedPolynomial, RingHom.comp_apply]
structure BlockLift {h : ℕ} (D : PoleData h) (Crt : CRTLift D) (i : Fin 2) where
  den : Seed Parameter
  num : (Seed Parameter)[X]
  specialDen : specialSeed den ≠ 0
  other_dvd : familyBlock D (otherBlock i) ∣ num
  congruence : familyBlock D i ∣ familyAmplitude D i * num + C den * familyOffset D i
  specialLift : liftAt specialPoint num den =
    (seedInField i (Crt.denominator i))⁻¹ • (Crt.numerator i).map (seedInField i)
set_option maxHeartbeats 800000 in
def blockLift {h : ℕ} (hh : 0 < h) (D : PoleData h) (Crt : CRTLift D) (i : Fin 2) :
    BlockLift D Crt i := Classical.choice (by
  let b := familyBlock D i
  let e := familyBlock D (otherBlock i)
  let a := familyAmplitude D i * e
  let q := familyOffset D i
  let z := zeroSeeds.comp specialSeed
  let d₀ := seedPolynomial i (Crt.denominator i)
  let N₀ := (Crt.numerator i).map (seedPolynomial i)
  have hconst := (D.determinant i).of_mul_left_right
  have hd₀ : d₀ ≠ 0 := by
    intro he
    have hz : zeroSeeds d₀ = (Crt.denominator i).eval 0 :=
      DFunLike.congr_fun (zero_seedPolynomial i) _
    rw [he, map_zero] at hz
    exact Crt.regular i 0 (by simpa using hconst) hz.symm
  have hb : b.Monic := (movingBlock_degree hh D i).monic.map _
  have hzb (j : Fin 2) : (familyBlock D j).map z = D.block j := by
    change (familyBlock D j).map (zeroSeeds.comp specialSeed) = _
    rw [← map_map, map_familyBlock, zeroSeeds_constants]
  have hza : a.map z = D.constant i * D.block (otherBlock i) := by
    have hc : z.comp constSeed = RingHom.id L := by
      change (zeroSeeds.comp specialSeed).comp constSeed = RingHom.id L
      rw [RingHom.comp_assoc, special_constSeed]
      exact RingHom.ext fun c => MvPolynomial.eval_C _
    have hX : z (MvPolynomial.X i) = 0 := by simp [z, zeroSeeds]
    simp only [a, e, familyAmplitude, Polynomial.map_mul, Polynomial.map_add, map_map,
      Polynomial.map_C, hc, map_id, hX, C_0, zero_mul, add_zero, hzb]
  have hc : IsCoprime (a.map z) (b.map z) := by
    change IsCoprime (a.map z) ((familyBlock D i).map z)
    rw [hza, hzb i]
    exact hconst.mul_left (coprime_other D i).symm
  obtain ⟨d, u, hd, hu⟩ := regularInverse z hb hc
  have hds : specialSeed d ≠ 0 := fun he => hd (by simp [z, he])
  have hseedConst : (seedPolynomial i).comp C = (MvPolynomial.C : L →+* Seed L) := by
    ext c
    simp [seedPolynomial]
  have hseedX : seedPolynomial i Polynomial.X = MvPolynomial.X i := by simp [seedPolynomial]
  obtain ⟨t₀, ht₀⟩ : e.map specialSeed ∣ N₀ := by
    change (familyBlock D (otherBlock i)).map specialSeed ∣ N₀
    rw [map_familyBlock]
    simpa only [coe_mapRingHom, map_map, hseedConst, N₀] using
      map_dvd (mapRingHom (seedPolynomial i)) (Crt.other_dvd i)
  obtain ⟨w₀, hw₀⟩ : b.map specialSeed ∣ a.map specialSeed * t₀ + C d₀ * q.map specialSeed := by
    have he : (familyAmplitude D i).map specialSeed =
        (D.constant i).map MvPolynomial.C +
          C (MvPolynomial.X i) * (D.slope i).map MvPolynomial.C := by
      simp [familyAmplitude, Polynomial.map_add, Polynomial.map_mul, map_map, special_constSeed]
    have hq : q.map specialSeed = C (MvPolynomial.X i) * (D.offset i).map MvPolynomial.C := by
      simp [q, familyOffset, Polynomial.map_mul, map_map, special_constSeed]
    dsimp only [a, b]
    rw [Polynomial.map_mul, mul_assoc, ← ht₀, he, hq, map_familyBlock,
      ← mul_assoc (C d₀), ← map_mul C]
    simpa only [coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      map_map, hseedConst, map_mul (seedPolynomial i), hseedX, N₀, d₀] using
      map_dvd (mapRingHom (seedPolynomial i)) (Crt.congruence i)
  let r := a * t₀.map liftSeed + C (liftSeed d₀) * q - b * w₀.map liftSeed
  let t := C d * t₀.map liftSeed - u * r
  let N := e * t
  let den := d * liftSeed d₀
  have hseed (c : Seed L) : specialSeed (liftSeed c) = c :=
    DFunLike.congr_fun special_liftSeed c
  have hden : specialSeed den = specialSeed d * d₀ := by
    dsimp only [den]
    rw [map_mul, hseed]
  have hr : r.map specialSeed = 0 := by
    simp only [r, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      map_liftSeed, hseed, hw₀, sub_self]
  have hN : N.map specialSeed = C (specialSeed d) * N₀ := by
    simp only [N, t, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, hr, mul_zero,
      sub_zero, map_liftSeed, ht₀]
    ring
  refine ⟨⟨den, N, by rw [hden]; exact mul_ne_zero hds hd₀, dvd_mul_right _ _, ?_, ?_⟩⟩
  · change b ∣ familyAmplitude D i * N + C den * q
    have he : familyAmplitude D i * N + C den * q =
        b * (C d * w₀.map liftSeed) - (a * u - C d) * r := by
      simp only [N, den, t, r, a, map_mul]
      ring
    rw [he]
    exact dvd_sub (dvd_mul_right _ _) (hu.mul_right _)
  · have hfd := seedEmbed_ne_zero specialPoint hds
    rw [liftAt, smul_eq_C_mul, ← map_map]
    let f := algebraMap (Seed L) (SeedFrac L)
    change f (specialSeed d) ≠ 0 at hfd
    change C ((f (specialSeed den))⁻¹) * (N.map specialSeed).map f =
      (seedInField i (Crt.denominator i))⁻¹ • (Crt.numerator i).map (seedInField i)
    rw [hden, hN, map_mul f, Polynomial.map_mul, Polynomial.map_C, cancel_scalar hfd]
    dsimp only [N₀, d₀]
    rw [map_map, smul_eq_C_mul]
    change C (((f.comp (seedPolynomial i)) (Crt.denominator i))⁻¹) * _ = _
    rw [frac_seedPolynomial]
    rfl)
end
end K1_14_1_7_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_4
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
abbrev jetMap {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    JetPolys R →+* JetPolys S :=
  mapRingHom (mapRingHom (mapRingHom f))
abbrev seedAt {F : Type} [Field F] (point : Parameter →+* F) :
    Seed Parameter →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (MvPolynomial.map point)
abbrev scalarJet {R : Type} [CommSemiring R] (d : R) : JetPolys R :=
  jetConstant (Polynomial.C d)
private abbrev ordinate {R : Type} [CommSemiring R] : JetPolys R :=
  Polynomial.C (Polynomial.X (R := R[X]))
private def ordinateImage {R : Type} [CommSemiring R] (H N : R[X]) : JetPolys R :=
  jetConstant H * ordinate + jetConstant N
private def velocityImage {R : Type} [CommSemiring R] (H N : R[X]) : JetPolys R :=
  jetConstant H * Polynomial.X + jetConstant H.derivative * ordinate + jetConstant N.derivative
private def clearedOrdinate {R : Type} [CommSemiring R] (H N : R[X]) (d : R) : JetPolys R :=
  scalarJet d * (jetConstant H * ordinate) + jetConstant N
private def clearedVelocity {R : Type} [CommSemiring R] (H N : R[X]) (d : R) : JetPolys R :=
  scalarJet d * (jetConstant H * Polynomial.X + jetConstant H.derivative * ordinate) +
    jetConstant N.derivative
def cleared (s : Shape) (H : Parameter[X]) (N : (Seed Parameter)[X])
    (d : Seed Parameter) (P : Source) : TrueSource Parameter :=
  let h := H.map (MvPolynomial.C (σ := Fin 2))
  let y := clearedOrdinate h N d
  let v := clearedVelocity h N d
  ∑ j ∈ P.support, ∑ i ∈ (P.coeff j).support,
    scalarJet d ^ (s.B - (i + j)) *
      (jetConstant (((P.coeff j).coeff i).map (MvPolynomial.map (Polynomial.C (R := L)))) *
        y ^ i * v ^ j)
private theorem jetMap_constant {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : R[X]) :
    jetMap f (jetConstant q) = jetConstant (q.map f) := by
  simp only [jetMap, jetConstant, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C]
private theorem jetMap_ordinate {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) :
    jetMap f (ordinate : JetPolys R) = (ordinate : JetPolys S) := by
  simp only [jetMap, coe_mapRingHom, Polynomial.map_C, Polynomial.map_X]
private theorem jetMap_velocity {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) :
    jetMap f (Polynomial.X : JetPolys R) = (Polynomial.X : JetPolys S) :=
  Polynomial.map_X _
private theorem forward_constant {F : Type} [Field F] (H : F[X]) (N : (SeedFrac F)[X])
    (q : (Seed F)[X]) :
    K1_14_1_7.forward H N (jetConstant q) =
      jetConstant (q.map (algebraMap (Seed F) (SeedFrac F))) := by
  change (C (C q)).eval₂ _ _ = _
  rw [eval₂_C]
  change (C q).eval₂ _ _ = _
  rw [eval₂_C]
  rfl
private theorem forward_ordinate {F : Type} [Field F] (H : F[X]) (N : (SeedFrac F)[X]) :
    K1_14_1_7.forward H N ordinate =
      ordinateImage (H.map (algebraMap F (SeedFrac F))) N := by
  change (C (Polynomial.X (R := (Seed F)[X]))).eval₂ _ _ = _
  rw [eval₂_C]
  change Polynomial.X.eval₂ _ _ = _
  rw [eval₂_X]
  rfl
private theorem forward_velocity {F : Type} [Field F] (H : F[X]) (N : (SeedFrac F)[X]) :
    K1_14_1_7.forward H N Polynomial.X =
      velocityImage (H.map (algebraMap F (SeedFrac F))) N := by
  change Polynomial.X.eval₂ _ _ = _
  rw [eval₂_X]
  rfl
private theorem eval_expansion {A T : Type} [CommSemiring A] [CommSemiring T]
    (f : JetPolys A →+* T) (P : JetPolys A) :
    f P = ∑ j ∈ P.support, ∑ i ∈ (P.coeff j).support,
      f (jetConstant ((P.coeff j).coeff i)) * f ordinate ^ i * f Polynomial.X ^ j := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  congr 1
  conv_lhs => rw [(P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, jetConstant, RingHom.comp_apply, ordinate]
private theorem degree_of_shaped {s : Shape} {P : Source} (hP : Shaped s P)
    {j i : ℕ} (hi : i ∈ (P.coeff j).support) : i + j ≤ s.B := by
  let q := (P.coeff j).coeff i
  have hn : q ≠ 0 := Polynomial.mem_support_iff.mp hi
  by_contra hb
  apply hn
  apply Polynomial.ext
  intro a
  rw [Polynomial.coeff_zero]
  apply MvPolynomial.ext
  intro e
  change sourceCoeff P j i a e = (0 : Seed L).coeff e
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra he
  exact hb (hP j i a e he).1
private theorem lift_cancel {F : Type} [Field F] (point : Parameter →+* F)
    (N : (Seed Parameter)[X]) (d : Seed Parameter) (hd : MvPolynomial.map point d ≠ 0) :
    Polynomial.C (seedAt point d) * liftAt point N d = N.map (seedAt point) := by
  have hz : seedAt point d ≠ 0 :=
    fun h => hd (IsFractionRing.injective (Seed F) (SeedFrac F) (h.trans (map_zero _).symm))
  change C (seedAt point d) * ((seedAt point d)⁻¹ • N.map (seedAt point)) =
    N.map (seedAt point)
  rw [Polynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hz, map_one, one_mul]
theorem map_abscissa {F : Type} [Field F] (point : Parameter →+* F) (H : Parameter[X]) :
    (H.map (MvPolynomial.C (σ := Fin 2))).map (seedAt point) =
      (H.map point).map (algebraMap F (SeedFrac F)) := by
  simp only [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro a
  simp only [seedAt, RingHom.comp_apply, MvPolynomial.map_C]
  exact (IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F) (point a)).symm
private theorem scale_term {R : Type} [CommSemiring R] (d c y v : R)
    {B i j : ℕ} (hb : i + j ≤ B) :
    d ^ (B - (i + j)) * (c * (d * y) ^ i * (d * v) ^ j) =
      d ^ B * (c * y ^ i * v ^ j) := by
  have he : B - (i + j) + i + j = B := by omega
  conv_rhs => rw [← he, pow_add d (B - (i + j) + i), pow_add d (B - (i + j))]
  rw [mul_pow, mul_pow]
  ring
set_option maxHeartbeats 800000 in
theorem cleared_specializes {F : Type} [Field F] (point : Parameter →+* F)
    (s : Shape) (H : Parameter[X]) (N : (Seed Parameter)[X])
    (d : Seed Parameter) (hd : MvPolynomial.map point d ≠ 0) (P : Source) (hP : Shaped s P) :
    jetMap (seedAt point) (cleared s H N d P) =
      scalarJet (seedAt point d) ^ s.B *
        K1_14_1_7.forward (H.map point) (liftAt point N d)
          (mapSource (point.comp (Polynomial.C (R := L))) P) := by
  let f := seedAt point
  let A' := (H.map point).map (algebraMap F (SeedFrac F))
  let N' := liftAt point N d
  let D := scalarJet (f d)
  have hA : (H.map (MvPolynomial.C (σ := Fin 2))).map f = A' := map_abscissa point H
  have hN : jetConstant (N.map f) = D * jetConstant N' := by
    rw [← lift_cancel point N d hd]
    exact map_mul jetConstant _ _
  have hdN : jetConstant (N.derivative.map f) = D * jetConstant N'.derivative := by
    have he := congrArg Polynomial.derivative (lift_cancel point N d hd)
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_map] at he
    rw [← he]
    exact map_mul jetConstant _ _
  have hy : jetMap f (clearedOrdinate (H.map MvPolynomial.C) N d) = D * ordinateImage A' N' := by
    simp only [clearedOrdinate, ordinateImage, map_add, map_mul, scalarJet, jetMap_constant,
      Polynomial.map_C, jetMap_ordinate, hA, hN, D, mul_add]
  have hv : jetMap f (clearedVelocity (H.map MvPolynomial.C) N d) = D * velocityImage A' N' := by
    simp only [clearedVelocity, velocityImage, map_add, map_mul, scalarJet, jetMap_constant,
      Polynomial.map_C, jetMap_ordinate, jetMap_velocity, ← derivative_map (H.map MvPolynomial.C) f, hA, hdN,
      D, mul_add, add_assoc]
  let g := (K1_14_1_7.forward (H.map point) N').toRingHom.comp
    (mapSource (point.comp (Polynomial.C (R := L))))
  have hgC (q : (Seed L)[X]) :
      g (jetConstant q) =
        jetConstant ((q.map (MvPolynomial.map (Polynomial.C (R := L)))).map f) := by
    change (K1_14_1_7.forward (H.map point) N')
      (jetMap (MvPolynomial.map (point.comp (Polynomial.C (R := L)))) (jetConstant q)) = _
    rw [jetMap_constant, forward_constant]
    congr 1
    apply Polynomial.ext
    intro a
    simp only [Polynomial.coeff_map, f, RingHom.comp_apply, MvPolynomial.map_map]
  have hgy : g ordinate = ordinateImage A' N' := by
    change (K1_14_1_7.forward (H.map point) N')
      (jetMap (MvPolynomial.map (point.comp (Polynomial.C (R := L)))) ordinate) = _
    rw [jetMap_ordinate, forward_ordinate]
  have hgv : g Polynomial.X = velocityImage A' N' := by
    change (K1_14_1_7.forward (H.map point) N')
      (jetMap (MvPolynomial.map (point.comp (Polynomial.C (R := L)))) Polynomial.X) = _
    rw [jetMap_velocity, forward_velocity]
  change jetMap f (cleared s H N d P) = D ^ s.B * g P
  rw [eval_expansion g P]
  simp only [cleared, map_sum, map_mul, map_pow, scalarJet, jetMap_constant,
    Polynomial.map_C, hy, hv, hgC, hgy, hgv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  exact scale_term D _ _ _ (degree_of_shaped hP hi)
end
end K1_14_1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
@[simp] theorem inputTaylorCoeff_apply {F : Type} [Field F] (α : F) (j i t : ℕ)
    (P : TrueSource F) :
    inputTaylorCoeff α j i t P = (inputTaylor α P j i).coeff t := rfl
end
end K1_14_1_7_2
end
section
namespace K1_14_1_3_2
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
abbrev Abscissa := SeedField[X]
def basePolynomial (P : L[X]) : Abscissa :=
  P.map (algebraMap L SeedField)
def scaledShift (i : Fin 2) (E : Abscissa) :
    Abscissa →+* PowerSeries Abscissa :=
  (PowerSeries.rescale (E^2)).comp (seriesPolynomial (seedShift i))
theorem scaledShift_base (i : Fin 2) (E : Abscissa) (P : L[X]) :
    scaledShift i E (basePolynomial P) = PowerSeries.C (basePolynomial P) := by
  unfold scaledShift basePolynomial
  rw [RingHom.comp_apply, seriesPolynomial_fixed _ _ (seedShift_base i), rescale_C]
theorem scaledShift_base_derivative (i : Fin 2) (E : Abscissa) (P : L[X]) :
    scaledShift i E (basePolynomial P).derivative =
      PowerSeries.C (basePolynomial P).derivative := by
  change scaledShift i E ((P.map _).derivative) = PowerSeries.C ((P.map _).derivative)
  rw [derivative_map]
  exact scaledShift_base i E P.derivative
private def crtTerm {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (j : Fin 2) : Abscissa :=
  C (seedInField j (Crt.denominator j))⁻¹ * (Crt.numerator j).map (seedInField j).toRingHom
private theorem crt_add {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    crtPolynomial Crt = crtTerm Crt i + crtTerm Crt (otherBlock i) := by
  have he (j : Fin 2) :
      (seedInField j (Crt.denominator j))⁻¹ • (Crt.numerator j).map (seedInField j) =
        crtTerm Crt j := Polynomial.smul_eq_C_mul _
  simp only [crtPolynomial, Fin.sum_univ_two, he]
  fin_cases i
  · rfl
  · exact add_comm _ _
private theorem crtTerm_factor {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    ∃ W, crtTerm Crt i = basePolynomial (D.block (otherBlock i)) * W := by
  obtain ⟨N, hN⟩ := Crt.other_dvd i
  have hf : (seedInField i).toRingHom.comp (C (R := L)) = algebraMap L SeedField := by
    apply RingHom.ext
    intro a
    exact (seedInField i).commutes a
  refine ⟨C (seedInField i (Crt.denominator i))⁻¹ * N.map (seedInField i).toRingHom, ?_⟩
  rw [crtTerm, hN, Polynomial.map_mul, Polynomial.map_map, hf, basePolynomial]
  exact mul_left_comm _ _ _
private theorem crtTerm_fixed {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i j : Fin 2)
    (hji : j ≠ i) (E : Abscissa) :
    scaledShift i E (crtTerm Crt j) = PowerSeries.C (crtTerm Crt j) ∧
    scaledShift i E (crtTerm Crt j).derivative = PowerSeries.C (crtTerm Crt j).derivative := by
  have hd : seedShift i (seedInField j (Crt.denominator j))⁻¹ =
      PowerSeries.C (seedInField j (Crt.denominator j))⁻¹ :=
    seedShift_inv_fixed _ _ (seedShift_other i j hji _)
  have hm (P : Polynomial L[X]) :
      scaledShift i E (C (seedInField j (Crt.denominator j))⁻¹ * P.map (seedInField j).toRingHom) =
        PowerSeries.C (C (seedInField j (Crt.denominator j))⁻¹ * P.map (seedInField j).toRingHom) := by
    have hmap := seriesPolynomial_fixed (seedShift i) (seedInField j).toRingHom
      (seedShift_other i j hji) P
    simp only [scaledShift, RingHom.comp_apply, map_mul, seriesPolynomial_C, hd,
      PowerSeries.map_C, hmap, rescale_C]
  exact ⟨hm _, by
    simp only [crtTerm, derivative_mul, derivative_C, zero_mul, zero_add, derivative_map]
    exact hm _⟩
private theorem rawBlock_factor {h : ℕ} (D : PoleData h) (i : Fin 2) :
    rawBlock D = basePolynomial (D.block i) * basePolynomial (D.block (otherBlock i)) := by
  fin_cases i <;> simp [rawBlock, poleProduct, basePolynomial, otherBlock, Polynomial.map_mul,
    mul_comm]
theorem crt_corrections {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2) :
    let E := basePolynomial (D.block i)
    let H := rawBlock D
    let ρ := scaledShift i E
    let C₀ := PowerSeries.C (R := Abscissa)
    ∃ B B₁ : PowerSeries Abscissa,
      ρ (crtPolynomial Crt) = C₀ (crtPolynomial Crt) + C₀ H * C₀ E * B ∧
      ρ (crtPolynomial Crt).derivative = C₀ (crtPolynomial Crt).derivative +
        (C₀ H.derivative * C₀ E - C₀ H * C₀ E.derivative) * B + C₀ H * C₀ E * B₁ := by
  dsimp only
  let E := basePolynomial (D.block i)
  let G := basePolynomial (D.block (otherBlock i))
  let ρ := scaledShift i E
  let C₀ := PowerSeries.C (R := Abscissa)
  have hH : rawBlock D = E * G := rawBlock_factor D i
  obtain ⟨W, hW⟩ := crtTerm_factor Crt i
  have heq : crtPolynomial Crt = G * W + crtTerm Crt (otherBlock i) :=
    (crt_add Crt i).trans (congrArg (· + crtTerm Crt (otherBlock i)) hW)
  have hne : otherBlock i ≠ i := by fin_cases i <;> decide
  obtain ⟨hfixed, hfixed'⟩ := crtTerm_fixed Crt i (otherBlock i) hne E
  have hG : ρ G = C₀ G := scaledShift_base _ _ _
  have hG' : ρ G.derivative = C₀ G.derivative := scaledShift_base_derivative _ _ _
  have hc (P : Abscissa) : ∃ U, ρ P = C₀ P + C₀ (E^2) * U :=
    rescale_difference _ _ _
      (seriesPolynomial_constantCoeff _ (seedShift_constantCoeff i) P)
  obtain ⟨B, hB⟩ := hc W
  obtain ⟨B₁, hB₁⟩ := hc W.derivative
  change ρ _ = _ at hfixed hfixed'
  change ∃ U V, ρ _ = C₀ _ + C₀ _ * C₀ _ * U ∧ ρ _ = _ + _ * U + _ * V
  refine ⟨B, B₁, ?_, ?_⟩
  · rw [heq, hH, map_add ρ, map_mul ρ, hG, hB, hfixed]
    simp only [map_add, map_mul, map_pow]
    ring
  · rw [heq, hH, derivative_add, derivative_mul, derivative_mul]
    simp only [map_add, map_mul, hG, hG', hB, hB₁, hfixed', map_pow]
    ring
end
end K1_14_1_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_1_3_1
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial
private abbrev sx : Source := C (C (Polynomial.X (R := SeedPoly)))
private abbrev sy : Source := C (Polynomial.X (R := SeedPoly[X]))
private abbrev sv : Source := Polynomial.X
private abbrev seedC : SeedPoly →+* Source := C.comp (C.comp C)
private theorem physical_x (x y : L) : atPhysical x y sx = sx + algebraMap L Source x := by
  change Polynomial.eval₂ _ _ (C (C (Polynomial.X (R := SeedPoly)))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_C]
  change (algebraMap SeedPoly[X] Source)
    (Polynomial.eval₂ _ _ (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_X, map_add]
  rfl
private theorem physical_y (x y : L) :
    atPhysical x y sy = algebraMap L Source y + sx * sv + sy := by
  change Polynomial.eval₂ _ _ (C (Polynomial.X (R := SeedPoly[X]))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (Polynomial.X (R := SeedPoly[X])) = _
  rw [eval₂_X]
  rfl
private theorem physical_v (x y : L) : atPhysical x y sv = sv := by
  change Polynomial.eval₂ _ _ (Polynomial.X : Source) = _
  rw [eval₂_X]
private theorem physical_seed (x y : L) (p : SeedPoly) :
    atPhysical x y (seedC p) = seedC p := by
  change Polynomial.eval₂ _ _ (C (C (C p))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C (C p)) = _
  rw [eval₂_C]
  change (algebraMap SeedPoly[X] Source) (Polynomial.eval₂ _ _ (C p)) = _
  rw [eval₂_C]
  rfl
private theorem source_ext {T : Type*} [Semiring T] {f g : Source →+* T}
    (hSeed : ∀ p, f (seedC p) = g (seedC p)) (hX : f sx = g sx)
    (hY : f sy = g sy) (hV : f sv = g sv) : f = g := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · exact Polynomial.ringHom_ext hSeed hX
    · exact hY
  · exact hV
private def extendTranslation {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* S[X]) : A[X] →+* Polynomial (Polynomial S) :=
  eval₂RingHom ((mapRingHom (C : S →+* S[X])).comp f) (C (Polynomial.X : S[X]))
@[simp] private theorem extendTranslation_C {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* S[X]) (a : A) :
    extendTranslation f (C a) = (f a).map (C : S →+* S[X]) := by
  simp [extendTranslation]
@[simp] private theorem extendTranslation_X {A S : Type*} [CommSemiring A] [CommSemiring S]
    (f : A →+* S[X]) : extendTranslation f Polynomial.X = C (Polynomial.X : S[X]) := by
  simp [extendTranslation]
private theorem extendTranslation_coeff {A S : Type*} [CommSemiring A] [CommSemiring S]
    [Module L A] [Module L S] {f : A →+* S[X]} {g : A →ₗ[L] S} {r : ℕ}
    (hg : ∀ a, (f a).coeff r = g a) (P : A[X]) :
    (extendTranslation f P).coeff r = mapCoeffs g P := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => rw [map_add, coeff_add, map_add, hp, hq]
  | monomial n a =>
    rw [mapCoeffs_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
      extendTranslation_C, extendTranslation_X,
      ← (C : S[X] →+* Polynomial (Polynomial S)).map_pow, coeff_mul_C, coeff_map, hg,
      C_mul_X_pow_eq_monomial]
private def translateSource (i : Fin 2) : Source →+* Source[X] :=
  extendTranslation (extendTranslation (extendTranslation (translation i).toRingHom))
private theorem translateSource_coeff (i : Fin 2) (r : ℕ) (P : Source) :
    (translateSource i P).coeff r = sourceHasse i r P := by
  unfold translateSource sourceHasse
  apply extendTranslation_coeff
  intro Q
  apply extendTranslation_coeff
  intro q
  apply extendTranslation_coeff
  intro a
  rfl
private theorem translateSource_seed (i : Fin 2) (p : SeedPoly) :
    translateSource i (seedC p) = (translation i p).map seedC := by
  simp only [translateSource, seedC, RingHom.comp_apply, extendTranslation_C,
    Polynomial.map_map]
  rfl
private theorem translateSource_scalar (i : Fin 2) (x : L) :
    translateSource i (algebraMap L Source x) = C (algebraMap L Source x) := by
  change translateSource i (seedC (MvPolynomial.C x)) = C (seedC (MvPolynomial.C x))
  rw [translateSource_seed]
  have h : translation i (MvPolynomial.C x) = C (MvPolynomial.C x) := by
    simp [translation, MvPolynomial.algebraMap_eq]
  rw [h, Polynomial.map_C]
private theorem translateSource_x (i : Fin 2) : translateSource i sx = C sx := by
  simp only [translateSource, sx, extendTranslation_C, extendTranslation_X, map_C]
private theorem translateSource_y (i : Fin 2) : translateSource i sy = C sy := by
  simp only [translateSource, sy, extendTranslation_C, extendTranslation_X, map_C]
private theorem translateSource_v (i : Fin 2) : translateSource i sv = C sv :=
  extendTranslation_X _
private theorem physical_hasse (x y : L) (i : Fin 2) (r : ℕ) (P : Source) :
    atPhysical x y (sourceHasse i r P) = sourceHasse i r (atPhysical x y P) := by
  let f := (mapRingHom (atPhysical x y).toRingHom).comp (translateSource i)
  let g := (translateSource i).comp (atPhysical x y).toRingHom
  have hfg : f = g := by
    apply source_ext
    · intro p
      change (translateSource i (seedC p)).map (atPhysical x y).toRingHom =
        translateSource i (atPhysical x y (seedC p))
      rw [physical_seed, translateSource_seed, Polynomial.map_map]
      have hseed : (atPhysical x y).toRingHom.comp seedC = seedC :=
        RingHom.ext (physical_seed x y)
      rw [hseed]
    · change (translateSource i sx).map (atPhysical x y).toRingHom =
        translateSource i (atPhysical x y sx)
      rw [translateSource_x, Polynomial.map_C]
      change C (atPhysical x y sx) = _
      simp only [physical_x, map_add, translateSource_x, translateSource_scalar]
    · change (translateSource i sy).map (atPhysical x y).toRingHom =
        translateSource i (atPhysical x y sy)
      rw [translateSource_y, Polynomial.map_C]
      change C (atPhysical x y sy) = _
      simp only [physical_y, map_add, map_mul, translateSource_scalar, translateSource_x,
        translateSource_y, translateSource_v]
    · change (translateSource i sv).map (atPhysical x y).toRingHom =
        translateSource i (atPhysical x y sv)
      rw [translateSource_v, Polynomial.map_C]
      change C (atPhysical x y sv) = _
      rw [physical_v, translateSource_v]
  have h := congrArg (fun F : Source →+* Source[X] => (F P).coeff r) hfg
  change ((translateSource i P).map (atPhysical x y).toRingHom).coeff r =
    (translateSource i (atPhysical x y P)).coeff r at h
  rw [coeff_map] at h
  change atPhysical x y ((translateSource i P).coeff r) =
    (translateSource i (atPhysical x y P)).coeff r at h
  simpa only [translateSource_coeff] using h
private def shiftAbscissa (x : L) (P : SeedPoly[X]) : SeedPoly[X] :=
  P.eval₂ C (Polynomial.X + C (MvPolynomial.C x))
private theorem physical_jetConstant (x y : L) (P : SeedPoly[X]) :
    atPhysical x y (jetConstant P) = jetConstant (shiftAbscissa x P) := by
  change Polynomial.eval₂ _ _ (C (C P)) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C P) = _
  rw [eval₂_C]
  rfl
theorem proof : K1_14_1_3.c1 := by
  classical
  intro h D word s Q hQ i r t a b j e hab
  rw [cleared, map_mul, physical_jetConstant, physical_hasse]
  simp only [coeffAt, jetConstant, RingHom.comp_apply]
  rw [coeff_C_mul, coeff_C_mul, coeff_mul, MvPolynomial.coeff_sum]
  simp only [sourceHasse, mapCoeffs_coeff]
  apply Finset.sum_eq_zero
  rintro ⟨u, v⟩ huv
  have huv' : u + v = a := by simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using huv
  have hv : (((atPhysical (nodeL t) (word t) Q).coeff j).coeff b).coeff v = 0 := by
    apply MvPolynomial.ext
    intro d
    exact hQ t v b j d (by omega)
  simp [hv]
end
end K1_14_1_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped Polynomial
@[simp] theorem substitute_base {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y v : A) (p : R) : substitute f y v (jetConstant p) = f p := by
  simp [substitute, jetConstant]
@[simp] theorem substitute_ordinate {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y v : A) :
    substitute f y v (C (Polynomial.X (R := R))) = y := by
  simp [substitute]
@[simp] theorem substitute_velocity {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y v : A) :
    substitute f y v (Polynomial.X (R := R[X])) = v := by
  simp [substitute]
theorem jetHom_ext {R A : Type*} [CommSemiring R] [CommSemiring A]
    {f g : R[X][X] →+* A}
    (hbase : ∀ p : R, f (jetConstant p) = g (jetConstant p))
    (hy : f (C Polynomial.X) = g (C Polynomial.X)) (hv : f Polynomial.X = g Polynomial.X) :
    f = g := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · exact hbase
    · exact hy
  · exact hv
theorem forward_as_substitute {F : Type} [Field F] (H : F[X]) (lift : (SeedFrac F)[X]) :
    let h := H.map (algebraMap F (SeedFrac F))
    let c : (SeedFrac F)[X] →+* JetPolys (SeedFrac F) := jetConstant
    let y : JetPolys (SeedFrac F) := C Polynomial.X
    (K1_14_1_7.forward H lift).toRingHom = substitute
      (c.comp (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F))))
      (c h * y + c lift) (c h * Polynomial.X + c h.derivative * y + c lift.derivative) := by
  rfl
theorem transfer_dvd {F : Type} [Field F] (H : F[X]) (lift : (SeedFrac F)[X])
    (α : F) (z : SeedFrac F) (N : ℕ) (P : TrueSource F)
    (hH : H.eval α = 0) (hz : lift.eval (algebraMap F (SeedFrac F) α) = z)
    (hd : (jetConstant ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys (SeedFrac F)) ∣ K1_14_1_7.forward (Polynomial.X - C α) (C z) P) :
    (jetConstant ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys (SeedFrac F)) ∣ K1_14_1_7.forward H lift P := by
  let x : (SeedFrac F)[X] := Polynomial.X - C (algebraMap F (SeedFrac F) α)
  let h := H.map (algebraMap F (SeedFrac F))
  have hh : x ∣ h := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [h, Polynomial.IsRoot, hH]
  have hl : x ∣ lift - C z := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [Polynomial.IsRoot, hz]
  obtain ⟨u, hu⟩ := hh
  obtain ⟨δ, hδ⟩ := hl
  have hlift : lift = x * δ + C z := by
    rw [← hδ, sub_add_cancel]
  let c : (SeedFrac F)[X] →+* JetPolys (SeedFrac F) := jetConstant
  let y : JetPolys (SeedFrac F) := C Polynomial.X
  let v : JetPolys (SeedFrac F) := Polynomial.X
  let E := substitute c (c u * y + c δ) (c u * v + c u.derivative * y + c δ.derivative)
  have hx : x.derivative = 1 := by simp [x]
  have hmap : (Polynomial.X - C α).map (algebraMap F (SeedFrac F)) = x := by simp [x]
  have hnorm := forward_as_substitute (Polynomial.X - C α) (C z)
  dsimp only at hnorm
  rw [hmap, hx, Polynomial.derivative_C, map_one, map_zero, one_mul, add_zero] at hnorm
  have he : E.comp (K1_14_1_7.forward (Polynomial.X - C α) (C z)).toRingHom =
      (K1_14_1_7.forward H lift).toRingHom := by
    rw [hnorm, forward_as_substitute]
    apply jetHom_ext
    · intro g
      simp [E, c]
    · change E _ = _
      simp only [substitute_ordinate]
      change E (c x * y + c (C z)) = c h * y + c lift
      rw [map_add, map_mul, hu, hlift]
      simp only [E, c, y, substitute_base, substitute_ordinate, map_mul, map_add]
      ring
    · change E _ = _
      simp only [substitute_velocity]
      change E (c x * v + y) = c h * v + c h.derivative * y + c lift.derivative
      rw [map_add, map_mul, hu, hlift, Polynomial.derivative_add, Polynomial.derivative_mul,
        Polynomial.derivative_mul, Polynomial.derivative_C, hx]
      simp only [E, c, y, v, substitute_base, substitute_ordinate, substitute_velocity,
        map_mul, map_add, map_one, map_zero]
      ring
  have hp := map_dvd E hd
  rw [show E (jetConstant (x ^ N)) = jetConstant (x ^ N) from substitute_base ..] at hp
  exact (DFunLike.congr_fun he P) ▸ hp
private def undoTaylor {R : Type} [CommRing R] (a : R) : JetPolys R →+* JetPolys R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.taylorAlgHom (-a)).toRingHom)
private theorem undoTaylor_base {R : Type} [CommRing R] (a : R) (g : R[X]) :
    undoTaylor a (jetConstant g) = jetConstant (Polynomial.taylor (-a) g) := by
  simp [undoTaylor, jetConstant]
private theorem undoTaylor_ordinate {R : Type} [CommRing R] (a : R) :
    undoTaylor a (Polynomial.C (Polynomial.X (R := R[X]))) = Polynomial.C Polynomial.X := by
  simp [undoTaylor]
private theorem undoTaylor_velocity {R : Type} [CommRing R] (a : R) :
    undoTaylor a (Polynomial.X (R := R[X][X])) = Polynomial.X := by
  simp [undoTaylor]
theorem linear_pole_dvd {F : Type} [Field F] (α : F) (z : SeedFrac F) (N : ℕ)
    (P : TrueSource F)
    (hd : (jetConstant ((Polynomial.X (R := SeedFrac F)) ^ N) :
      JetPolys (SeedFrac F)) ∣ zeroSubst (centered α z P)) :
    (jetConstant ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys (SeedFrac F)) ∣ K1_14_1_7.forward (Polynomial.X - C α) (C z) P := by
  let a := algebraMap F (SeedFrac F) α
  let x : (SeedFrac F)[X] := Polynomial.X - C a
  have hx : x.derivative = 1 := by simp [x]
  have ht : Polynomial.taylor (-a) Polynomial.X = x := by
    simp [x, sub_eq_add_neg]
  have hmap : (Polynomial.X - C α).map (algebraMap F (SeedFrac F)) = x := by simp [x, a]
  have hnorm := forward_as_substitute (Polynomial.X - C α) (C z)
  dsimp only at hnorm
  rw [hmap, hx, Polynomial.derivative_C, map_one, map_zero, one_mul, add_zero] at hnorm
  have he : (undoTaylor a).comp (zeroSubst.comp (centered α z)) =
      (K1_14_1_7.forward (Polynomial.X - C α) (C z)).toRingHom := by
    rw [hnorm]
    apply jetHom_ext
    · intro g
      simp only [RingHom.comp_apply, centered, zeroSubst, substitute_base, undoTaylor_base,
        coe_mapRingHom]
      change jetConstant (Polynomial.taylor (-a) (Polynomial.taylor a _)) = jetConstant _
      rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
    · simp only [RingHom.comp_apply, centered, zeroSubst, substitute_ordinate, map_add,
        substitute_base, map_mul, undoTaylor_base, ht, undoTaylor_ordinate, Polynomial.taylor_C]
    · simp only [RingHom.comp_apply, centered, zeroSubst, substitute_velocity, map_add,
        map_mul, undoTaylor_base, ht, undoTaylor_ordinate, undoTaylor_velocity]
  have hp := map_dvd (undoTaylor a) hd
  rw [undoTaylor_base, Polynomial.taylor_pow, ht] at hp
  exact (DFunLike.congr_fun he P) ▸ hp
end
end K1_14_1_7_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
namespace K1_14_1_8
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial BigOperators
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
end
end K1_14_1_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
private theorem taylor_seed_degree {F : Type} [Field F] (s : Shape) (α : F)
    (P : TrueSource F) (hP : Shaped s P) (j i t : ℕ) :
    ((inputTaylor α P j i).coeff t).totalDegree ≤ s.U := by
  have hc (a : ℕ) : (((P.coeff j).coeff i).coeff a).totalDegree ≤ s.U := by
    apply Finset.sup_le
    intro e he
    exact (hP j i a e (MvPolynomial.mem_support_iff.mp he)).2.2
  rw [inputTaylor, taylor_coeff, eval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  rw [hasseDeriv_coeff]
  have he :
      ((k + t).choose t : Seed F) * ((P.coeff j).coeff i).coeff (k + t) *
          (algebraMap F (Seed F) α) ^ k =
        MvPolynomial.C (((k + t).choose t : F) * α ^ k) *
          ((P.coeff j).coeff i).coeff (k + t) := by
    simp only [MvPolynomial.algebraMap_eq, map_mul, map_pow, map_natCast]
    ring
  rw [he]
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hc (k + t))
private theorem seedWeight_add (side : Fin 2) (e : Exponent) :
    seedWeight e = e side + e (otherBlock side) := by
  rw [seedWeight, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  fin_cases side <;> simp [otherBlock, Nat.add_comm]
private theorem window_sum {F ι : Type} [Field F] [Fintype ι]
    {U d : ℕ} {side : Fin 2} (g : ι → Seed F) (hg : ∀ i, SeedWindow U d side (g i)) :
    SeedWindow U d side (∑ i, g i) := by
  intro e he
  by_contra h
  apply he
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_eq_zero fun i _ => not_imp_comm.mp (hg i e) h
end
end K1_14_1_7_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_4
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
end K1_14_1_4
end
section
namespace K1_14_1_5
noncomputable section
open K1_14 K1_14_1
open scoped BigOperators
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
end
end K1_14_1_5
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1200000
namespace K1_14_1_6
noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped BigOperators Polynomial
private abbrev sx : Source := Polynomial.C (Polynomial.C (Polynomial.X (R := SeedPoly)))
private abbrev sy : Source := Polynomial.C (Polynomial.X (R := SeedPoly[X]))
private abbrev sv : Source := Polynomial.X
private abbrev shiftedY : Source := sy + sx * sv
private abbrev seedC : SeedPoly →+* Source := C.comp (C.comp C)
private theorem physical_x (x r : L) : atPhysical x r sx = sx + algebraMap L Source x := by
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.C (Polynomial.X (R := SeedPoly)))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_C]
  change (algebraMap SeedPoly[X] Source) (Polynomial.eval₂ _ _ (Polynomial.X (R := SeedPoly))) = _
  rw [eval₂_X, map_add]
  rfl
private theorem physical_y (x r : L) :
    atPhysical x r sy = shiftedY + algebraMap L Source r := by
  change Polynomial.eval₂ _ _ (Polynomial.C (Polynomial.X (R := SeedPoly[X]))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (Polynomial.X (R := SeedPoly[X])) = _
  rw [eval₂_X]
  change algebraMap L Source r + sx * sv + sy = shiftedY + algebraMap L Source r
  dsimp only [shiftedY]
  ac_rfl
private theorem physical_v (x r : L) : atPhysical x r sv = sv := by
  change Polynomial.eval₂ _ _ (Polynomial.X : Source) = _
  rw [eval₂_X]
private theorem physical_seed (x r : L) (p : SeedPoly) :
    atPhysical x r (seedC p) = seedC p := by
  change Polynomial.eval₂ _ _ (C (C (C p))) = _
  rw [eval₂_C]
  change Polynomial.eval₂ _ _ (C (C p)) = _
  rw [eval₂_C]
  change (algebraMap SeedPoly[X] Source) (Polynomial.eval₂ _ _ (C p)) = _
  rw [eval₂_C]
  rfl
private theorem product_eq_monomial (p : SeedPoly) (a b j : ℕ) :
    seedC p * sx^a * sy^b * sv^j =
      monomial j (monomial b (monomial a p)) := by
  simp only [seedC, RingHom.comp_apply, sx, sy, sv, ← map_pow, ← map_mul,
    C_mul_X_pow_eq_monomial]
private theorem seed_scalar (e : Fin 2 →₀ ℕ) (c : L) :
    seedC (MvPolynomial.monomial e c) = c • seedC (MvPolynomial.monomial e 1) := by
  rw [Algebra.smul_def]
  change _ = seedC (MvPolynomial.C c) * _
  rw [← map_mul, MvPolynomial.C_mul_monomial, mul_one]
private theorem mem_of_monomials (M : Submodule L Source) (P : Source)
    (H : ∀ j b a e, coeffAt P j b a e ≠ 0 →
      monomial j (monomial b (monomial a (MvPolynomial.monomial e
        (coeffAt P j b a e)))) ∈ M) : P ∈ M := by
  rw [P.as_sum_support]
  apply M.sum_mem
  intro j _
  rw [show monomial j (P.coeff j) =
      monomial j (∑ b ∈ (P.coeff j).support, monomial b ((P.coeff j).coeff b)) from
    congrArg _ (P.coeff j).as_sum_support, map_sum]
  apply M.sum_mem
  intro b _
  let p := (P.coeff j).coeff b
  change monomial j (monomial b p) ∈ M
  rw [show p = ∑ a ∈ p.support, monomial a (p.coeff a) from p.as_sum_support]
  simp only [map_sum]
  apply M.sum_mem
  intro a _
  rw [show monomial a (p.coeff a) =
      monomial a (∑ e ∈ (p.coeff a).support, MvPolynomial.monomial e ((p.coeff a).coeff e)) from
    congrArg _ (p.coeff a).as_sum]
  simp only [map_sum]
  apply M.sum_mem
  intro e he
  exact H j b a e (MvPolynomial.mem_support_iff.mp he)
private theorem mul_add_pow_mem (M : Submodule L Source) (p u v : Source)
    (n : ℕ) (H : ∀ k ≤ n, p * u^k * v^(n-k) ∈ M) :
    p * (u+v)^n ∈ M := by
  rw [add_pow u v n, Finset.mul_sum]
  apply M.sum_mem
  intro k hk
  have h := M.smul_mem (n.choose k : L) (H k (by simpa using hk))
  rw [Algebra.smul_def, map_natCast] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h
private theorem mul_shift_pow_mem (M : Submodule L Source) (p u : Source)
    (r : L) (n : ℕ) (H : ∀ k ≤ n, p * u^k ∈ M) :
    p * (u + algebraMap L Source r)^n ∈ M := by
  apply mul_add_pow_mem
  intro k hk
  rw [mul_comm (p * u^k), ← map_pow, ← Algebra.smul_def]
  exact M.smul_mem _ (H k hk)
private structure Low (m : ℕ) where
  j : ℕ
  b : ℕ
  a : ℕ
  e : Fin 2 →₀ ℕ
  low : a + 2*b < m
private def cut (s : Shape) : Source →ₗ[L] (Low s.m → L) where
  toFun P z := coeffAt P z.j z.b z.a z.e
  map_add' P Q := by
    funext z
    simp [coeffAt]
  map_smul' c P := by
    funext z
    simp [coeffAt, Polynomial.coeff_smul]
private abbrev SeedIdx (U : ℕ) := Σ a : Fin (U+1), Fin (U+1-a.val)
private def seedExp {U : ℕ} (i : SeedIdx U) : Fin 2 →₀ ℕ :=
  (finTwoArrowEquiv' ℕ).symm (i.1.val, i.2.val)
private theorem exists_seedIdx {U : ℕ} {e : Fin 2 →₀ ℕ} (he : seedWeight e ≤ U) :
    ∃ i : SeedIdx U, seedExp i = e := by
  let pair := finTwoArrowEquiv' ℕ e
  have hw : pair.1 + pair.2 ≤ U := by
    simpa only [pair, seedWeight, Equiv.symm_apply_apply, ← finTwoArrowEquiv'_sum_eq (d := pair)]
      using he
  refine ⟨⟨⟨pair.1, by omega⟩, ⟨pair.2, ?_⟩⟩, ?_⟩
  · change pair.2 < U+1-pair.1
    omega
  · exact (finTwoArrowEquiv' ℕ).symm_apply_apply e
private theorem seed_card (U : ℕ) : Fintype.card (SeedIdx U) = triangle U := by
  simp only [SeedIdx, Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  calc
    (∑ a ∈ Finset.range (U+1), (U+1-a)) = (∑ a ∈ Finset.range (U+1), (a+1)) := by
      rw [← Finset.sum_range_reflect (fun a => U+1-a) (U+1)]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.mem_range] at ha
      omega
    _ = (∑ a ∈ Finset.range (U+2), a) := by
      simpa only [Nat.add_zero] using (Finset.sum_range_succ' (fun a : ℕ => a) (U+1)).symm
    _ = triangle U := by
      rw [Finset.sum_range_id, triangle, show U+2-1 = U+1 by omega, Nat.mul_comm]
private abbrev GenIdx (s : Shape) :=
  (Σ q : Fin (s.B+1), Σ k : Fin (min q.val s.J+1),
    Fin (s.m + min q.val s.J - (q.val + 2*k.val))) × SeedIdx s.U
private theorem gen_card (s : Shape) :
    Fintype.card (GenIdx s) =
      shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * triangle s.U := by
  unfold GenIdx
  rw [Fintype.card_prod, seed_card, shapeSum]
  congr 1
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => ∑ k : Fin (min q s.J+1), (s.m + min q s.J - (q + 2*k.val)))]
  refine Finset.sum_congr rfl ?_
  intro q _
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => s.m + min q s.J - (q + 2*k)) (min q s.J+1)
private def localGen (q d k a : ℕ) (e : Fin 2 →₀ ℕ) : Source :=
  seedC (MvPolynomial.monomial e 1) * sx^a * sy^k * sv^(d-k) * shiftedY^(q-d)
private def generators (s : Shape) (i : GenIdx s) : Low s.m → L :=
  cut s (localGen i.1.1.val (min i.1.1.val s.J) i.1.2.1.val i.1.2.2.val (seedExp i.2))
private def localSpan (s : Shape) : Submodule L (Low s.m → L) :=
  Submodule.span L (Set.range (generators s))
private abbrev preimage (s : Shape) : Submodule L Source := (localSpan s).comap (cut s)
private theorem high_mono (s : Shape) (e : Fin 2 →₀ ℕ) (a b j : ℕ)
    (h : s.m ≤ a+2*b) :
    seedC (MvPolynomial.monomial e 1) * sx^a * sy^b * sv^j ∈ LinearMap.ker (cut s) := by
  apply LinearMap.mem_ker.mpr
  funext z
  change coeffAt _ z.j z.b z.a z.e = 0
  rw [product_eq_monomial]
  have hz := z.low
  by_cases hj : j = z.j
  · by_cases hb : b = z.b
    · by_cases ha : a = z.a
      · omega
      · simp [coeffAt, Polynomial.coeff_monomial, hj, hb, ha]
    · simp [coeffAt, Polynomial.coeff_monomial, hj, hb]
  · simp [coeffAt, Polynomial.coeff_monomial, hj]
private theorem collect_powers {R : Type*} [CommMonoid R] (c x y v : R)
    (a k j t n : ℕ) :
    (c * x^a * y^k * v^j) * y^t * (x*v)^n = c * x^(a+n) * y^(k+t) * v^(j+n) := by
  simp only [pow_add, mul_pow]
  ac_rfl
private theorem collect_adapted {R : Type*} [CommMonoid R] (c x y v A : R)
    (a j k n : ℕ) :
    (c * x^a * v^j * A) * y^k * (x*v)^n = c * x^(a+n) * y^k * v^(j+n) * A := by
  simp only [pow_add, mul_pow]
  ac_rfl
private theorem move_v {R : Type*} [CommMonoid R] (c v x y : R) :
    c * v * x * y = c * x * y * v := by ac_rfl
private theorem high_gen (s : Shape) (q d k a : ℕ) (e : Fin 2 →₀ ℕ)
    (h : s.m ≤ a+(q-d)+2*k) : localGen q d k a e ∈ LinearMap.ker (cut s) := by
  unfold localGen
  change _ * (sy + sx * sv)^(q-d) ∈ _
  apply mul_add_pow_mem
  intro t ht
  have ht' := high_mono s e (a+(q-d-t)) (k+t) (d-k+(q-d-t)) (by omega)
  rw [collect_powers]
  exact ht'
private theorem gen_mem (s : Shape) (q k a : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : q ≤ s.B) (hk : k ≤ min q s.J) (he : seedWeight e ≤ s.U) :
    localGen q (min q s.J) k a e ∈ preimage s := by
  change cut s _ ∈ localSpan s
  have hd : min q s.J ≤ q := min_le_left _ _
  by_cases ha : a < s.m + min q s.J - (q+2*k)
  · obtain ⟨i, rfl⟩ := exists_seedIdx he
    exact Submodule.subset_span
      ⟨(⟨⟨q, Nat.lt_succ_of_le hq⟩, ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, ha⟩⟩⟩, i), rfl⟩
  · rw [LinearMap.mem_ker.mp (high_gen s q (min q s.J) k a e (by omega))]
    exact (localSpan s).zero_mem
private theorem shifted_mono_mem (s : Shape) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : seedWeight e ≤ s.U) :
    seedC (MvPolynomial.monomial e 1) * sx^a * shiftedY^b * sv^j ∈ preimage s := by
  let q := b+j
  let d := min q s.J
  have hd : d ≤ q := min_le_left _ _
  have hjd : j ≤ d := le_min (Nat.le_add_left _ _) hj
  let p := seedC (MvPolynomial.monomial e 1) * sx^a * sv^j * shiftedY^(q-d)
  have hpow : shiftedY^b = shiftedY^(q-d) * shiftedY^(d-j) := by
    rw [← pow_add, show q-d+(d-j) = b by dsimp only [q] at *; omega]
  have hexpand : p * (sy + sx*sv)^(d-j) ∈ preimage s := by
    apply mul_add_pow_mem
    intro k hk
    have hV : d-k = j+(d-j-k) := by omega
    have hgen := gen_mem s q k (a+(d-j-k)) e hq (by omega) he
    change localGen q d k (a+(d-j-k)) e ∈ _ at hgen
    rw [localGen, hV] at hgen
    dsimp only [p]
    rw [collect_adapted]
    exact hgen
  dsimp only [p] at hexpand
  change (seedC (MvPolynomial.monomial e 1) * sx^a * sv^j * shiftedY^(q-d)) *
    shiftedY^(d-j) ∈ preimage s at hexpand
  rw [move_v (seedC (MvPolynomial.monomial e 1) * sx^a), mul_assoc
    (seedC (MvPolynomial.monomial e 1) * sx^a), ← hpow] at hexpand
  exact hexpand
private theorem translated_mono_mem (s : Shape) (x r : L) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : seedWeight e ≤ s.U) :
    seedC (MvPolynomial.monomial e 1) * (sx + algebraMap L Source x)^a *
      (shiftedY + algebraMap L Source r)^b * sv^j ∈ preimage s := by
  let p := seedC (MvPolynomial.monomial e 1) * sv^j
  have h : (p * (shiftedY + algebraMap L Source r)^b) *
      (sx + algebraMap L Source x)^a ∈ preimage s := by
    apply mul_shift_pow_mem
    intro t _
    have h' : (p * sx^t) * (shiftedY + algebraMap L Source r)^b ∈ preimage s := by
      apply mul_shift_pow_mem
      intro k hk
      dsimp only [p]
      rw [move_v]
      exact shifted_mono_mem s t k j e (by omega) hj he
    rw [mul_right_comm]
    exact h'
  rw [mul_right_comm p] at h
  dsimp only [p] at h
  rw [move_v] at h
  exact h
private theorem atPhysical_mem (h : ℕ) (s : Shape) (W : ℕ) (x r : L)
    (P : ambient h s W) : cut s (atPhysical x r P.val) ∈ localSpan s := by
  change P.val ∈ (preimage s).comap (atPhysical x r).toLinearMap
  apply mem_of_monomials
  intro j b a e hne
  have hel : trueEligible h s W j b a e := by
    by_contra hn
    exact hne (P.property j b a e hn)
  obtain ⟨hq, hj, he, _⟩ := hel
  change atPhysical x r _ ∈ preimage s
  rw [← product_eq_monomial, seed_scalar, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, map_smul]
  apply (preimage s).smul_mem
  simp only [map_mul, map_pow, physical_x, physical_y, physical_v, physical_seed]
  exact translated_mono_mem s x r a b j e hq hj he
private def nodeMap (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) (i : I) :
    ambient h s W →ₗ[L] localSpan s :=
  LinearMap.codRestrict (localSpan s)
    (((cut s).comp (atPhysical (nodeL i) (word i)).toLinearMap).domRestrict (ambient h s W))
    (atPhysical_mem h s W (nodeL i) (word i))
private theorem localSpan_finrank (s : Shape) :
    Module.finrank L (localSpan s) ≤
      shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * triangle s.U := by
  rw [← gen_card]
  exact finrank_range_le_card (R := L) (generators s)
end
end K1_14_1_6
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
def c1 : Prop :=
  ∀ (F : Type) [Field F] (s : Shape) (α : F) (z : SeedFrac F) (P : TrueSource F),
    Shaped s P → centered α z P = packGrades s (localSlots s α z P)
def c2 : Prop :=
  ∀ (F : Type) [Field F] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → (SeedFrac F)[X]),
    (∀ q k, (Polynomial.X (R := SeedFrac F)) ^ (s.B+s.J) ∣ zeroGrade s q.val (f q) k) →
    (jetConstant ((Polynomial.X (R := SeedFrac F)) ^ (s.B+s.J)) : JetPolys (SeedFrac F)) ∣
      zeroSubst (packGrades s f)
end
end K1_14_1_7_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
namespace K1_14_1_8
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
end
end K1_14_1_8
end
section
namespace K1_14_1_1
noncomputable section
open K1_14 K1_14_1 Module Polynomial
open scoped Polynomial
private def quotientBasis {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) : Basis (Fin n) R (AdjoinRoot b) :=
  (AdjoinRoot.powerBasisAux' hb).reindex (finCongr hd)
private def mulMatrix {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : R[X]) : Matrix (Fin n) (Fin n) R :=
  Algebra.leftMulMatrix (quotientBasis hb hd) (AdjoinRoot.mk b a)
private theorem mulMatrix_entry {R : Type*} [CommRing R] {b : R[X]} {n : ℕ}
    (hb : b.Monic) (hd : b.natDegree = n) (a : R[X]) (i j : Fin n) :
    mulMatrix hb hd a i j = ((a * Polynomial.X (R := R) ^ (j : ℕ)) %ₘ b).coeff i := by
  have hpow (k : Fin b.natDegree) :
      (AdjoinRoot.powerBasisAux' hb) k = AdjoinRoot.root b ^ (k : ℕ) :=
    (AdjoinRoot.powerBasis' hb).basis_eq_pow k
  unfold mulMatrix
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  unfold quotientBasis
  rw [Basis.reindex_apply, hpow, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    Basis.repr_reindex_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  rfl
private theorem mulMatrix_specialize {R S : Type*} [CommRing R] [CommRing S]
    {b a : R[X]} {b' a' : S[X]} {n : ℕ} (f : R →+* S)
    (hb : b.Monic) (hd : b.natDegree = n) (hb' : b'.Monic) (hd' : b'.natDegree = n)
    (hmapb : b.map f = b') (hmapa : a.map f = a') :
    f (mulMatrix hb hd a).det = (mulMatrix hb' hd' a').det := by
  rw [f.map_det]
  congr 1
  ext i j
  change f (mulMatrix hb hd a i j) = mulMatrix hb' hd' a' i j
  rw [mulMatrix_entry, mulMatrix_entry, ← Polynomial.coeff_map, Polynomial.map_modByMonic f hb,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, hmapa, hmapb]
private theorem mulMatrix_det_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {b a : R[X]} {n : ℕ} (hb : b.Monic) (hd : b.natDegree = n)
    (hcop : IsCoprime a b) : (mulMatrix hb hd a).det ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hcop
  have hinv : AdjoinRoot.mk b u * AdjoinRoot.mk b a = 1 := by
    have h := congrArg (AdjoinRoot.mk b) huv
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] using h
  have hmat : mulMatrix hb hd u * mulMatrix hb hd a = 1 := by
    unfold mulMatrix
    rw [← map_mul, hinv, map_one]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  intro hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet
private theorem clearedSolution {R : Type*} [CommRing R] [Nontrivial R]
    {b : R[X]} {n : ℕ} (hb : b.Monic) (hd : b.natDegree = n) (a q : R[X]) :
    ∃ t : R[X], t.degree < b.degree ∧ b ∣ a * t + C (mulMatrix hb hd a).det * q := by
  let basis := quotientBasis hb hd
  let matrix := mulMatrix hb hd a
  let target := AdjoinRoot.mk b (-q)
  let solution := basis.equivFun.symm (matrix.cramer (basis.equivFun target))
  have hcoord : basis.equivFun solution = matrix.cramer (basis.equivFun target) :=
    basis.equivFun.apply_symm_apply _
  have hsol : AdjoinRoot.mk b a * solution = matrix.det • target := by
    apply basis.equivFun.injective
    have hvec := Algebra.leftMulMatrix_mulVec_repr basis (AdjoinRoot.mk b a) solution
    change matrix.mulVec (basis.repr solution) = ⇑(basis.repr (AdjoinRoot.mk b a * solution)) at hvec
    rw [← Basis.equivFun_apply, ← Basis.equivFun_apply, hcoord, Matrix.mulVec_cramer] at hvec
    rw [map_smul]
    exact hvec.symm
  obtain ⟨t, ht⟩ := AdjoinRoot.mk_surjective solution
  have hrep : AdjoinRoot.mk b (t %ₘ b) = solution := by
    rw [← AdjoinRoot.modByMonicHom_mk hb, AdjoinRoot.mk_leftInverse hb, ht]
  refine ⟨t %ₘ b, degree_modByMonic_lt _ hb, AdjoinRoot.mk_eq_zero.mp ?_⟩
  change AdjoinRoot.mk b (a * (t %ₘ b) + C matrix.det * q) = 0
  rw [map_add, map_mul, map_mul, hrep, hsol, AdjoinRoot.mk_C]
  simp [target, Algebra.smul_def]
private theorem eval_map_constants {F : Type*} [Field F] (z : F) (g : F[X]) :
    (g.map (C : F →+* F[X])).map (evalRingHom z) = g := by
  have hc : (evalRingHom z).comp (C : F →+* F[X]) = RingHom.id F :=
    RingHom.ext fun x => eval_C
  rw [Polynomial.map_map, hc, Polynomial.map_id]
private theorem blockContribution {h : ℕ} (D : PoleData h) (i : Fin 2) :
    ∃ (d : L[X]) (N : Polynomial L[X]),
      d ≠ 0 ∧ N.degree < (2 * h : ℕ) ∧
      (D.block (otherBlock i)).map C ∣ N ∧
      (D.block i).map C ∣
        ((D.constant i).map C + C (Polynomial.X (R := L)) * (D.slope i).map C) * N +
          C (d * Polynomial.X (R := L)) * (D.offset i).map C ∧
      ∀ z, IsCoprime (D.constant i + C z * D.slope i) (D.block i) → d.eval z ≠ 0 := by
  let b := (D.block i).map (C : L →+* L[X])
  let e := (D.block (otherBlock i)).map (C : L →+* L[X])
  let amplitude := (D.constant i).map (C : L →+* L[X]) +
    C (Polynomial.X (R := L)) * (D.slope i).map (C : L →+* L[X])
  let a := amplitude * e
  let q := C (Polynomial.X (R := L)) * (D.offset i).map (C : L →+* L[X])
  have hb : b.Monic := (D.monic i).map _
  have he : e.Monic := (D.monic (otherBlock i)).map _
  have hbd : b.natDegree = h := ((D.monic i).natDegree_map _).trans (D.degree i)
  have hed : e.natDegree = h :=
    ((D.monic (otherBlock i)).natDegree_map _).trans (D.degree (otherBlock i))
  have hcop : IsCoprime (D.block (otherBlock i)) (D.block i) := by
    fin_cases i
    · exact D.coprime.symm
    · exact D.coprime
  let d := (mulMatrix hb hbd a).det
  have hregular (z : L) (hz : IsCoprime (D.constant i + C z * D.slope i) (D.block i)) :
      d.eval z ≠ 0 := by
    have hmapa : a.map (evalRingHom z) =
        (D.constant i + C z * D.slope i) * D.block (otherBlock i) := by
      simp only [a, amplitude, e, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        eval_map_constants, coe_evalRingHom, eval_X]
    change (evalRingHom z) (mulMatrix hb hbd a).det ≠ 0
    rw [mulMatrix_specialize (evalRingHom z) hb hbd (D.monic i) (D.degree i)
      (eval_map_constants z (D.block i)) hmapa]
    exact mulMatrix_det_ne_zero _ _ (hz.mul_left hcop)
  have hd : d ≠ 0 := by
    have hc : IsCoprime (D.constant i) (D.block i) := (D.determinant i).of_mul_left_right
    intro hd
    exact hregular 0 (by simpa using hc) (by simp [hd])
  obtain ⟨t, ht, hdiv⟩ := clearedSolution hb hbd a q
  refine ⟨d, e * t, hd, ?_, dvd_mul_right _ _, ?_, hregular⟩
  · by_cases ht0 : t = 0
    · rw [ht0, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    have htn : t.natDegree < h := by
      rw [degree_eq_natDegree ht0, degree_eq_natDegree hb.ne_zero, hbd, Nat.cast_lt] at ht
      exact ht
    apply (degree_mul_le e t).trans_lt
    rw [degree_eq_natDegree he.ne_zero, degree_eq_natDegree ht0, hed, ← Nat.cast_add, Nat.cast_lt]
    omega
  · change b ∣ amplitude * (e * t) + C (d * Polynomial.X (R := L)) * (D.offset i).map C
    simpa only [a, q, ← mul_assoc, ← map_mul] using hdiv
set_option maxHeartbeats 800000 in
theorem proof : K1_14_1.c1 := by
  intro h _ _ D
  choose d N hN using blockContribution D
  exact ⟨⟨d, N, fun i => (hN i).1, fun i => (hN i).2.1, fun i => (hN i).2.2.1,
    fun i => (hN i).2.2.2.1, fun i => (hN i).2.2.2.2⟩⟩
end
end K1_14_1_1
end
section
namespace K1_14_1_3_2
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 1000000
private def jetHom {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y v : B) : Polynomial (Polynomial A) →+* B :=
  eval₂RingHom (eval₂RingHom base y) v
@[simp] private theorem jetHom_base {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y v : B) (a : A) :
    jetHom base y v (C (C a)) = base a := by
  simp [jetHom]
@[simp] private theorem jetHom_y {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y v : B) :
    jetHom base y v (C Polynomial.X) = y := by
  simp [jetHom]
@[simp] private theorem jetHom_v {A B : Type*} [CommSemiring A] [CommSemiring B]
    (base : A →+* B) (y v : B) :
    jetHom base y v Polynomial.X = v := by
  simp [jetHom]
private abbrev rawY : RawSource := C (Polynomial.X (R := Abscissa))
private abbrev rawV : RawSource := Polynomial.X
private abbrev rawC : Abscissa →+* RawSource := jetConstant
private abbrev rawSeriesC : PowerSeries Abscissa →+* PowerSeries RawSource :=
  PowerSeries.map rawC
private theorem forward_def {h : ℕ} {D : PoleData h} (Crt : CRTLift D) :
    (forward Crt).toRingHom = jetHom (rawC.comp genericCoefficients.toRingHom)
      (rawC (rawBlock D) * rawY + rawC (crtPolynomial Crt))
      (rawC (rawBlock D) * rawV + rawC (rawBlock D).derivative * rawY +
        rawC (crtPolynomial Crt).derivative) :=
  rfl
private theorem forward_base {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (P : SeedPoly[X]) :
    forward Crt (C (C P)) = rawC (genericCoefficients P) := by
  change (forward Crt).toRingHom (C (C P)) = _
  rw [forward_def, jetHom_base, RingHom.comp_apply]
  rfl
private theorem forward_seed {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (a : SeedPoly) :
    (forward Crt).toRingHom (C (C (C a))) = rawC (C (algebraMap SeedPoly SeedField a)) := by
  change forward Crt _ = _
  rw [forward_base]
  change rawC ((C a).map (algebraMap SeedPoly SeedField)) = _
  rw [Polynomial.map_C]
private def rawShift (i : Fin 2) (E : Abscissa) (B B₁ : PowerSeries Abscissa) :
    RawSource →+* PowerSeries RawSource :=
  jetHom (rawSeriesC.comp (scaledShift i E))
    (PowerSeries.C rawY - rawSeriesC (PowerSeries.C E * B))
    (PowerSeries.C rawV + rawSeriesC (PowerSeries.C E.derivative * B - PowerSeries.C E * B₁))
private theorem rawShift_y (i : Fin 2) (E : Abscissa) (B B₁ : PowerSeries Abscissa) :
    rawShift i E B B₁ rawY = PowerSeries.C rawY - rawSeriesC (PowerSeries.C E * B) :=
  jetHom_y _ _ _
private theorem rawShift_v (i : Fin 2) (E : Abscissa) (B B₁ : PowerSeries Abscissa) :
    rawShift i E B B₁ rawV =
      PowerSeries.C rawV + rawSeriesC (PowerSeries.C E.derivative * B - PowerSeries.C E * B₁) :=
  jetHom_v _ _ _
private theorem rawShift_constants (i : Fin 2) (E : Abscissa) (B B₁ : PowerSeries Abscissa)
    (P : Abscissa) (hP : scaledShift i E P = PowerSeries.C P) :
    rawShift i E B B₁ (rawC P) = PowerSeries.C (rawC P) := by
  change rawShift i E B B₁ (C (C P)) = _
  simp [rawShift, hP]
private theorem cancel_ordinate {R : Type*} [CommRing R] (H E T l B : R) :
    H * (T - E * B) + (l + H * E * B) = H * T + l := by ring
private theorem cancel_velocity {R : Type*} [CommRing R] (H H' E E' T V l B B₁ : R) :
    H * (V + (E' * B - E * B₁)) + H' * (T - E * B) +
      (l + (H' * E - H * E') * B + H * E * B₁) = H * V + H' * T + l := by ring
private theorem forward_shift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (i : Fin 2)
    (B B₁ : PowerSeries Abscissa)
    (hY : scaledShift i (basePolynomial (D.block i)) (crtPolynomial Crt) =
      PowerSeries.C (crtPolynomial Crt) + PowerSeries.C (rawBlock D) *
        PowerSeries.C (basePolynomial (D.block i)) * B)
    (hV : scaledShift i (basePolynomial (D.block i)) (crtPolynomial Crt).derivative =
      PowerSeries.C (crtPolynomial Crt).derivative +
        (PowerSeries.C (rawBlock D).derivative * PowerSeries.C (basePolynomial (D.block i)) -
          PowerSeries.C (rawBlock D) * PowerSeries.C (basePolynomial (D.block i)).derivative) * B +
        PowerSeries.C (rawBlock D) * PowerSeries.C (basePolynomial (D.block i)) * B₁) :
    let E := basePolynomial (D.block i)
    (rawShift i E B B₁).comp (forward Crt).toRingHom =
      (PowerSeries.rescale (rawC (E^2))).comp
        ((PowerSeries.map (forward Crt).toRingHom).comp (sourceShift i)) := by
  let E := basePolynomial (D.block i)
  let F := (forward Crt).toRingHom
  let Φ := rawShift i E B B₁
  let S := PowerSeries.rescale (rawC (E^2))
  have hH : scaledShift i E (rawBlock D) = PowerSeries.C (rawBlock D) :=
    scaledShift_base i E (poleProduct D)
  have hH' : scaledShift i E (rawBlock D).derivative = PowerSeries.C (rawBlock D).derivative :=
    scaledShift_base_derivative i E (poleProduct D)
  have hbase (P : Abscissa) (hp : scaledShift i E P = PowerSeries.C P) :
      Φ (rawC P) = PowerSeries.C (rawC P) := rawShift_constants _ _ _ _ _ hp
  change Φ.comp F = S.comp ((PowerSeries.map F).comp (sourceShift i))
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        change Φ (F (C (C (C a)))) = S (PowerSeries.map F (sourceShift i (C (C (C a)))))
        rw [show F (C (C (C a))) = _ from forward_seed Crt a]
        change rawShift i E B B₁ (C (C (C (algebraMap SeedPoly SeedField a)))) = _
        apply PowerSeries.ext
        intro n
        simp only [rawShift, jetHom_base, RingHom.comp_apply, scaledShift, seriesPolynomial_C,
          seedShift_algebraMap, genericSeedShift, sourceShift, S, PowerSeries.coeff_rescale,
          PowerSeries.coeff_map, F, forward_seed, map_mul, map_pow]
      · change Φ (F (C (C Polynomial.X))) = S (PowerSeries.map F (sourceShift i (C (C Polynomial.X))))
        rw [show F (C (C Polynomial.X)) = rawC Polynomial.X from
          (forward_base Crt _).trans (congrArg rawC (Polynomial.map_X _))]
        simp only [sourceShift, seriesPolynomial_C, seriesPolynomial_X, PowerSeries.map_C]
        change Φ (rawC Polynomial.X) = S (PowerSeries.C (F (C (C Polynomial.X))))
        rw [show F (C (C Polynomial.X)) = rawC Polynomial.X from
          (forward_base Crt _).trans (congrArg rawC (Polynomial.map_X _)), rescale_C]
        exact hbase _ (by simp [scaledShift, rescale_C])
    · change Φ (F (C Polynomial.X)) = S (PowerSeries.map F (sourceShift i (C Polynomial.X)))
      simp only [sourceShift, seriesPolynomial_C, seriesPolynomial_X, PowerSeries.map_C, S,
        rescale_C]
      change Φ (F (C Polynomial.X)) = PowerSeries.C (F (C Polynomial.X))
      simp only [F, forward_def, jetHom_y, map_add, map_mul, hbase _ hH]
      change scaledShift i E _ = _ at hY
      have he : Φ (rawC (crtPolynomial Crt)) =
          rawSeriesC (scaledShift i E (crtPolynomial Crt)) :=
        jetHom_base _ _ _ _
      rw [he, hY, show Φ rawY = _ from rawShift_y i E B B₁]
      simp only [map_add, map_mul, PowerSeries.map_C]
      exact cancel_ordinate _ _ _ _ _
  · change Φ (F Polynomial.X) = S (PowerSeries.map F (sourceShift i Polynomial.X))
    simp only [sourceShift, seriesPolynomial_X, PowerSeries.map_C, S, rescale_C]
    simp only [F, forward_def, jetHom_v, map_add, map_mul, hbase _ hH, hbase _ hH']
    change scaledShift i E _ = _ at hV
    have he : Φ (rawC (crtPolynomial Crt).derivative) =
        rawSeriesC (scaledShift i E (crtPolynomial Crt).derivative) :=
      jetHom_base _ _ _ _
    rw [he, hV, show Φ rawV = _ from rawShift_v i E B B₁,
      show Φ rawY = _ from rawShift_y i E B B₁]
    simp only [map_add, map_mul, map_sub, PowerSeries.map_C]
    exact cancel_velocity _ _ _ _ _ _ _ _ _
private theorem generic_sourceX (P : L[X]) :
    genericCoefficients (sourceX P) = basePolynomial P := by
  change (P.map MvPolynomial.C).map (algebraMap SeedPoly SeedField) =
    P.map (algebraMap L SeedField)
  rw [Polynomial.map_map]
  have h : (algebraMap SeedPoly SeedField).comp (MvPolynomial.C : L →+* SeedPoly) =
      algebraMap L SeedField := by
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h]
theorem proof : K1_14_1_3.c2 := by
  intro h D Crt s Q hQ i r
  let E := basePolynomial (D.block i)
  let H := rawBlock D
  let m := s.B + s.J
  obtain ⟨B, B₁, hY, hV⟩ := crt_corrections Crt i
  let Φ := rawShift i E B B₁
  have hcompat := RingHom.congr_fun (forward_shift Crt i B B₁ hY hV) Q
  have hr := congrArg (PowerSeries.coeff r) hcompat
  change PowerSeries.coeff r (Φ (forward Crt Q)) =
    PowerSeries.coeff r (PowerSeries.rescale (rawC (E^2))
      (PowerSeries.map (forward Crt).toRingHom (sourceShift i Q))) at hr
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, sourceShift_coeff] at hr
  have hrow : forward Crt (cleared D i r Q) =
      (rawC (E^2)) ^ r * forward Crt (sourceHasse i r Q) := by
    rw [cleared, map_mul]
    change forward Crt (C (C (sourceX (D.block i ^ (2*r))))) * _ = _
    rw [forward_base, generic_sourceX, basePolynomial, Polynomial.map_pow, pow_mul, map_pow]
    rfl
  change rawC (H^m) ∣ forward Crt Q at hQ
  obtain ⟨W, hW⟩ := hQ
  have hfix : Φ (rawC (H^m)) = PowerSeries.C (rawC (H^m)) := by
    apply rawShift_constants
    rw [map_pow, show scaledShift i E H = PowerSeries.C H from
      scaledShift_base i E (poleProduct D), map_pow]
  rw [hW, map_mul, hfix, PowerSeries.coeff_C_mul] at hr
  change rawC (H^m) ∣ forward Crt (cleared D i r Q)
  exact ⟨PowerSeries.coeff r (Φ W), hrow.trans hr.symm⟩
end
end K1_14_1_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2_1
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_2 Polynomial
open scoped BigOperators Polynomial
private theorem substitute_fixed_velocity {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (y : S[X]) :
    substitute (jetConstant.comp f) (C y) Polynomial.X =
      Polynomial.mapRingHom (Polynomial.eval₂RingHom (C.comp f) y) := by
  apply jetHom_ext
  · intro a
    rw [substitute_base]
    simp [jetConstant]
  · simp
  · simp
private theorem centered_row {F : Type} [Field F] (α : F) (z : SeedFrac F)
    (P : TrueSource F) (j : ℕ) :
    let f := (Polynomial.taylorAlgHom (algebraMap F (SeedFrac F) α)).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F)))
    ((centered α z P).coeff j) =
      Polynomial.eval₂RingHom (C.comp f) (Polynomial.X + C (C z)) (P.coeff j) := by
  dsimp only
  unfold centered
  rw [show (C Polynomial.X + jetConstant (C z) : JetPolys (SeedFrac F)) =
    C (Polynomial.X + C (C z)) by simp [jetConstant], substitute_fixed_velocity,
    coe_mapRingHom, Polynomial.coeff_map]
private theorem source_slot_eq_zero {F : Type} [Field F] {s : Shape}
    {P : TrueSource F} (hP : Shaped s P) {i j : ℕ}
    (h : ¬ (i + j ≤ s.B ∧ j ≤ s.J)) : (P.coeff j).coeff i = 0 := by
  apply Polynomial.ext
  intro a
  rw [Polynomial.coeff_zero]
  apply MvPolynomial.ext
  intro e
  change sourceCoeff P j i a e = 0
  by_contra hn
  exact h ⟨(hP j i a e hn).1, (hP j i a e hn).2.1⟩
private theorem centered_coeff_sum {F : Type} [Field F] (α : F) (z : SeedFrac F)
    (P : TrueSource F) (i j N : ℕ) (hN : (P.coeff j).natDegree < N) :
    ((centered α z P).coeff j).coeff i =
      ∑ n ∈ Finset.range N,
        C ((n.choose i : SeedFrac F) * z ^ (n - i)) *
          (inputTaylor α P j n).map (algebraMap (Seed F) (SeedFrac F)) := by
  rw [centered_row]
  conv_lhs => rw [(P.coeff j).as_sum_range_C_mul_X_pow' hN]
  simp only [coe_eval₂RingHom, eval₂_finsetSum, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow, RingHom.comp_apply, coe_mapRingHom]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hc : algebraMap (Seed F) (SeedFrac F) (algebraMap F (Seed F) α) =
      algebraMap F (SeedFrac F) α :=
    (IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F) α).symm
  rw [inputTaylor, map_taylor, hc, ← (C (R := SeedFrac F)).map_pow,
    ← map_natCast (C (R := SeedFrac F)), ← map_mul (C (R := SeedFrac F)),
    mul_comm (z ^ (n - i)), mul_comm]
  rfl
private theorem pack_coeff_term {R : Type} [CommSemiring R] {s : Shape}
    (f : (q : Grade s) → GradeSlot s q.val → R[X]) (q : Grade s)
    (k : GradeSlot s q.val) (i j : ℕ) :
    ((C (C (f q k) * Polynomial.X ^ (q.val - k.val)) * Polynomial.X ^ k.val).coeff j).coeff i =
      if j = k.val ∧ i + j = q.val then f q k else 0 := by
  have hk : k.val ≤ q.val := (Nat.lt_succ_iff.mp k.isLt).trans (min_le_left ..)
  by_cases hj : j = k.val
  · have hi : i = q.val - k.val ↔ i + j = q.val := by omega
    simp only [coeff_C_mul_X_pow, hj, ite_true, true_and, hi]
  · simp only [coeff_C_mul_X_pow, hj, ite_false, false_and, Polynomial.coeff_zero]
private theorem pack_coeff {R : Type} [CommSemiring R] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → R[X]) (i j : ℕ)
    (hq : i + j ≤ s.B) (hj : j ≤ s.J) :
    ((packGrades s f).coeff j).coeff i =
      f ⟨i + j, Nat.lt_succ_of_le hq⟩
        ⟨j, Nat.lt_succ_of_le (le_min (show j ≤ i + j by omega) hj)⟩ := by
  let q : Grade s := ⟨i + j, Nat.lt_succ_of_le hq⟩
  let k : GradeSlot s q.val := ⟨j, Nat.lt_succ_of_le (le_min (by dsimp [q]; omega) hj)⟩
  change _ = f q k
  simp only [packGrades, finsetSum_coeff, pack_coeff_term]
  rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ q)]
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · simp [q, k]
    · intro k' _ hne
      have hval : j ≠ k'.val := fun he => hne (Fin.ext he.symm)
      simp [hval]
  · intro q' _ hne
    have hval : i + j ≠ q'.val := fun he => hne (Fin.ext he.symm)
    simp [hval]
private theorem pack_coeff_eq_zero {R : Type} [CommSemiring R] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → R[X]) (i j : ℕ)
    (h : ¬ (i + j ≤ s.B ∧ j ≤ s.J)) :
    ((packGrades s f).coeff j).coeff i = 0 := by
  simp only [packGrades, finsetSum_coeff, pack_coeff_term]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun k _ => ?_
  have hq : q.val ≤ s.B := Nat.lt_succ_iff.mp q.isLt
  have hk : k.val ≤ s.J := (Nat.lt_succ_iff.mp k.isLt).trans (min_le_right ..)
  have hn : ¬ (j = k.val ∧ i + j = q.val) := by omega
  simp [hn]
theorem proof : K1_14_1_7_2.c1 := by
  intro F _ s α z P hP
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  have hN : (P.coeff j).natDegree < s.B - j + 1 := by
    apply Nat.lt_succ_of_le
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact source_slot_eq_zero hP (by omega)
  by_cases h : i + j ≤ s.B ∧ j ≤ s.J
  · rcases h with ⟨hq, hj⟩
    rw [pack_coeff s _ i j hq hj]
    rw [centered_coeff_sum α z P i j (s.B - j + 1) hN]
    let term (n : ℕ) := C ((n.choose i : SeedFrac F) * z ^ (n - i)) *
      (inputTaylor α P j n).map (algebraMap (Seed F) (SeedFrac F))
    change (∑ n ∈ Finset.range (s.B - j + 1), term n) = _
    have hs := Finset.sum_range_add term i (s.B - (i + j) + 1)
    rw [show i + (s.B - (i + j) + 1) = s.B - j + 1 by omega] at hs
    have hzero : (∑ n ∈ Finset.range i, term n) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      simp [term, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn)]
    rw [hs, hzero, zero_add]
    rw [← Fin.sum_univ_eq_sum_range (fun n => term (i + n)) (s.B - (i + j) + 1)]
    unfold localSlots
    refine Finset.sum_congr rfl fun n _ => ?_
    have hi : i + j - j = i := by omega
    simp only [term, inputOrdinate, hi, Nat.add_sub_cancel_left]
  · rw [pack_coeff_eq_zero s _ i j h]
    by_cases hj : j ≤ s.B ∧ j ≤ s.J
    · rw [centered_coeff_sum α z P i j (s.B - j + 1) hN]
      refine Finset.sum_eq_zero fun n hn => ?_
      have hn' := Finset.mem_range.mp hn
      simp [Nat.choose_eq_zero_of_lt (show n < i by omega)]
    · have hrow : P.coeff j = 0 := by
        exact Polynomial.ext fun n => (source_slot_eq_zero hP (by omega)).trans
          (Polynomial.coeff_zero n).symm
      rw [centered_row, hrow, map_zero, Polynomial.coeff_zero]
end
end K1_14_1_7_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_4
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
private abbrev Row := ℕ × ℕ × ℕ × Exponent
private def readRow {R : Type} [CommRing R] (Q : TrueSource R) (G : (Seed R)[X])
    (r : Row) : R :=
  ((((Q.coeff r.1).coeff r.2.1) %ₘ G).coeff r.2.2.1).coeff r.2.2.2
private def rowsOfColumn (Q : TrueSource Parameter) (G : (Seed Parameter)[X]) :
    Finset Row :=
  Q.support.biUnion fun j => (Q.coeff j).support.biUnion fun i =>
    let p := (Q.coeff j).coeff i %ₘ G
    p.support.biUnion fun a => (p.coeff a).support.image fun e => (j, i, a, e)
private theorem mem_rowsOfColumn (Q : TrueSource Parameter) (G : (Seed Parameter)[X])
    (r : Row) (hr : readRow Q G r ≠ 0) : r ∈ rowsOfColumn Q G := by
  obtain ⟨j, i, a, e⟩ := r
  refine Finset.mem_biUnion.mpr ⟨j, Polynomial.mem_support_iff.mpr ?_, ?_⟩
  · intro h
    exact hr (by simp [readRow, h])
  refine Finset.mem_biUnion.mpr ⟨i, Polynomial.mem_support_iff.mpr ?_, ?_⟩
  · intro h
    exact hr (by simp [readRow, h])
  refine Finset.mem_biUnion.mpr ⟨a, Polynomial.mem_support_iff.mpr ?_, ?_⟩
  · intro h
    exact hr (by simp [readRow, h])
  exact Finset.mem_image.mpr ⟨e, MvPolynomial.mem_support_iff.mpr hr, rfl⟩
private theorem readRow_map {F : Type} [Field F] (point : Parameter →+* F)
    (Q : TrueSource Parameter) {G : (Seed Parameter)[X]} (hG : G.Monic) (r : Row) :
    readRow (mapSource point Q) (G.map (MvPolynomial.map point)) r =
      point (readRow Q G r) := by
  simp only [readRow, mapSource, coe_mapRingHom, Polynomial.coeff_map,
    ← map_modByMonic (MvPolynomial.map point) hG, MvPolynomial.coeff_map]
private def readRowLinear {F : Type} [Field F] (G : (Seed F)[X])
    (r : Row) : TrueSource F →ₗ[F] F :=
  (MvPolynomial.lcoeff F r.2.2.2).comp <|
    ((Polynomial.lcoeff (Seed F) r.2.2.1).restrictScalars F).comp <|
    ((Polynomial.modByMonicHom G).restrictScalars F).comp <|
    ((Polynomial.lcoeff (Seed F)[X] r.2.1).restrictScalars F).comp <|
    (Polynomial.lcoeff ((Seed F)[X])[X] r.1).restrictScalars F
private theorem readRow_sum {F ι : Type} [Field F] [Fintype ι]
    (Q : ι → TrueSource F) (v : ι → F) (G : (Seed F)[X]) (r : Row) :
    readRow (∑ k, v k • Q k) G r = ∑ k, v k * readRow (Q k) G r := by
  change readRowLinear G r (∑ k, v k • Q k) = ∑ k, v k • readRowLinear G r (Q k)
  simp only [map_sum, map_smul]
private theorem dvd_iff_read {F : Type} [Field F] (Q : TrueSource F)
    {G : (Seed F)[X]} (hG : G.Monic) :
    (jetConstant (G.map (algebraMap (Seed F) (SeedFrac F))) : JetPolys (SeedFrac F)) ∣
      jetMap (algebraMap (Seed F) (SeedFrac F)) Q ↔
      ∀ r, readRow Q G r = 0 := by
  let f := algebraMap (Seed F) (SeedFrac F)
  have h : (jetConstant (G.map f) : JetPolys (SeedFrac F)) ∣ jetMap f Q ↔
      ∀ j i, (Q.coeff j).coeff i %ₘ G = 0 := by
    simp only [jetConstant, RingHom.comp_apply, C_dvd_iff_dvd_coeff,
      jetMap, coe_mapRingHom, Polynomial.coeff_map]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro i
    rw [← modByMonic_eq_zero_iff_dvd (hG.map f), ← map_modByMonic f hG,
      Polynomial.map_eq_zero_iff (IsFractionRing.injective (Seed F) (SeedFrac F))]
  rw [h]
  constructor
  · intro hz r
    simp [readRow, hz]
  · intro hz j i
    apply Polynomial.ext
    intro a
    rw [Polynomial.coeff_zero]
    apply MvPolynomial.ext
    intro e
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact hz (j, i, a, e)
private theorem matrix_of_columns {ι : Type} [Fintype ι]
    (Q : ι → TrueSource Parameter) (G : (Seed Parameter)[X]) (hG : G.Monic) :
    ∃ n : ℕ, ∃ M : Matrix (Fin n) ι Parameter,
      ∀ (F : Type) [Field F] (point : Parameter →+* F) (v : ι → F),
        (M.map point).mulVec v = 0 ↔
          (jetConstant (G.map (seedAt point)) : JetPolys (SeedFrac F)) ∣
            ∑ k, v k • jetMap (seedAt point) (Q k) := by
  classical
  let rows := Finset.univ.biUnion fun k => rowsOfColumn (Q k) G
  let e : Fin rows.card ≃ ↥rows := (Fintype.equivFinOfCardEq (Fintype.card_coe rows)).symm
  let M : Matrix (Fin rows.card) ι Parameter := fun r k => readRow (Q k) G (e r).val
  refine ⟨rows.card, M, ?_⟩
  intro F _ point v
  let inc := algebraMap (Seed F) (SeedFrac F)
  let incAlg : TrueSource F →ₐ[F] JetPolys (SeedFrac F) :=
    mapAlgHom (mapAlgHom (mapAlgHom (IsScalarTower.toAlgHom F (Seed F) (SeedFrac F))))
  let G' := G.map (MvPolynomial.map point)
  let Q' : ι → TrueSource F := fun k => mapSource point (Q k)
  let q := ∑ k, v k • Q' k
  have hcomp (k : ι) : incAlg (Q' k) = jetMap (seedAt point) (Q k) := by
    change jetMap inc (jetMap (MvPolynomial.map point) (Q k)) = _
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    simp only [jetMap, coe_mapRingHom, Polynomial.coeff_map, seedAt, inc, RingHom.comp_apply]
  have hq : jetMap inc q = ∑ k, v k • jetMap (seedAt point) (Q k) := by
    change incAlg (∑ k, v k • Q' k) = _
    simp only [map_sum, map_smul, hcomp]
  rw [← hq, ← Polynomial.map_map (MvPolynomial.map point) inc, dvd_iff_read q (hG.map _)]
  have hread (r : Row) : readRow q G' r = ∑ k, v k * point (readRow (Q k) G r) := by
    rw [readRow_sum]
    simp only [Q', G', readRow_map point _ hG]
  have heval (r : Fin rows.card) : ((M.map point).mulVec v) r = readRow q G' (e r).val := by
    rw [hread]
    change ∑ k, point (readRow (Q k) G (e r).val) * v k = _
    simp only [mul_comm]
  change (M.map point).mulVec v = 0 ↔ ∀ r, readRow q G' r = 0
  constructor
  · intro hv r
    by_cases hr : r ∈ rows
    · have he := congrFun hv (e.symm ⟨r, hr⟩)
      rw [heval] at he
      simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using he
    · rw [hread]
      apply Finset.sum_eq_zero
      intro k _
      have hz : readRow (Q k) G r = 0 := by
        by_contra hn
        exact hr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, mem_rowsOfColumn _ _ _ hn⟩)
      rw [hz, map_zero, mul_zero]
  · intro hv
    funext r
    exact (heval r).trans (hv (e r).val)
theorem proof : K1_14_1_7.c4 := by
  classical
  intro h D Crt E s ι _ P hP
  let G := (E.H.map (MvPolynomial.C (σ := Fin 2))) ^ (s.B + s.J)
  obtain ⟨n, M, hM⟩ := matrix_of_columns (fun k => cleared s E.H E.num E.den (P k)) G
    ((E.monic.map _).pow _)
  have fibre {F : Type} [Field F] (point : Parameter →+* F)
      (hd : MvPolynomial.map point E.den ≠ 0) (v : ι → F) :
      (M.map point).mulVec v = 0 ↔
        PoleTest s (E.H.map point) (liftAt point E.num E.den)
          (Fintype.linearCombination F (fun k => mapSource (point.comp (Polynomial.C (R := L))) (P k)) v) := by
    let f := K1_14_1_7.forward (E.H.map point) (liftAt point E.num E.den)
    let d := scalarJet (seedAt point E.den)
    have hu : IsUnit d := by
      have hn : seedAt point E.den ≠ 0 := by
        intro hzero
        exact hd (IsFractionRing.injective (Seed F) (SeedFrac F) (hzero.trans (map_zero _).symm))
      exact (isUnit_iff_ne_zero.mpr hn).map (jetConstant.comp Polynomial.C)
    rw [hM F point v]
    simp only [cleared_specializes point s E.H E.num E.den hd _ (hP _)]
    have hsum : (∑ k, v k • (d ^ s.B * f (mapSource (point.comp (Polynomial.C (R := L))) (P k)))) =
        d ^ s.B * f (Fintype.linearCombination F
          (fun k => mapSource (point.comp (Polynomial.C (R := L))) (P k)) v) := by
      simp only [Fintype.linearCombination_apply, map_sum, map_smul, Finset.mul_sum,
        mul_smul_comm]
    have hG : G.map (seedAt point) =
        ((E.H.map point).map (algebraMap F (SeedFrac F))) ^ (s.B + s.J) := by
      simp only [G, Polynomial.map_pow, map_abscissa]
    rw [hsum, (hu.pow s.B).dvd_mul_left, hG]
    rfl
  refine ⟨n, M, ?_, fibre genericPoint E.genericDen⟩
  intro v
  have hpoint : specialPoint.comp (Polynomial.C (R := L)) = RingHom.id L := by
    ext a
    simp [specialPoint]
  have hmap (Q : Source) : mapSource (RingHom.id L) Q = Q := by
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    simp only [mapSource, coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.map_id]
  simpa only [E.specialH, E.specialLift, hpoint, hmap] using fibre specialPoint E.specialDen v
end
end K1_14_1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_2_2
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_2 Polynomial
open scoped BigOperators Polynomial
private def slot {R : Type} [CommSemiring R] (a : R[X]) (i k : ℕ) : JetPolys R :=
  jetConstant a * (C (Polynomial.X (R := R[X]))) ^ i * Polynomial.X ^ k
private theorem pack_eq_sum {R : Type} [CommSemiring R] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → R[X]) :
    packGrades s f = ∑ q : Grade s, ∑ j : GradeSlot s q.val,
      slot (f q j) (q.val - j.val) j.val := by
  simp only [packGrades, slot, jetConstant, RingHom.comp_apply, map_mul, map_pow]
private theorem zeroSubst_slot {R : Type} [CommSemiring R] (a : R[X]) (i j : ℕ) :
    zeroSubst (slot a i j) = ∑ k ∈ Finset.range (j + 1),
      slot (a * C (j.choose k : R) * Polynomial.X ^ (i + k)) (i + (j - k)) k := by
  simp only [slot, map_mul, map_pow, zeroSubst, substitute_base,
    substitute_ordinate, substitute_velocity]
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_pow, pow_add, map_natCast]
  ac_rfl
private theorem sum_range_eq_slots {M : Type*} [AddCommMonoid M] {s : Shape} {q : ℕ}
    (j : GradeSlot s q) (g : ℕ → M) :
    (∑ k ∈ Finset.range (j.val + 1), g k) =
      ∑ k : GradeSlot s q, if k.val ≤ j.val then g k.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ j.val then g k else 0)]
  calc
    _ = ∑ k ∈ Finset.range (j.val + 1), (if k ≤ j.val then g k else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = _ := by
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt j.isLt)) ?_
      intro k _ hk
      exact ite_eq_right (fun h => hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
private theorem zeroSubst_grade_slot {E : Type} [Field E] (s : Shape) (q : ℕ)
    (f : GradeSlot s q → E[X]) (j : GradeSlot s q) :
    zeroSubst (slot (f j) (q - j.val) j.val) =
      ∑ k : GradeSlot s q, if k.val ≤ j.val then
        slot (f j * C (j.val.choose k.val : E) * Polynomial.X ^ (q - j.val + k.val))
          (q - k.val) k.val else 0 := by
  rw [zeroSubst_slot, sum_range_eq_slots j]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : k.val ≤ j.val
  · have hj : j.val ≤ q := (Nat.le_of_lt_succ j.isLt).trans (min_le_left _ _)
    simp only [ite_eq_left h, show q - j.val + (j.val - k.val) = q - k.val by omega]
  · simp only [ite_eq_right h]
private theorem zeroSubst_packGrades {E : Type} [Field E] (s : Shape)
    (f : (q : Grade s) → GradeSlot s q.val → E[X]) :
    zeroSubst (packGrades s f) = packGrades s (fun q k => zeroGrade s q.val (f q) k) := by
  simp only [pack_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [zeroSubst_grade_slot s q.val (f q)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [zeroGrade, slot, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp
theorem proof : K1_14_1_7_2.c2 := by
  intro F _ s f h
  rw [zeroSubst_packGrades, pack_eq_sum]
  apply Finset.dvd_sum
  intro q _
  apply Finset.dvd_sum
  intro k _
  unfold slot
  have hc : (jetConstant (Polynomial.X ^ (s.B + s.J)) : JetPolys (SeedFrac F)) ∣
      jetConstant (zeroGrade s q.val (f q) k) :=
    _root_.map_dvd jetConstant (h q k)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _
end
end K1_14_1_7_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_4
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
end
end K1_14_1_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_1
open K1_14 K1_14_1_7 Polynomial
open scoped BigOperators Polynomial
private theorem coeff_zeroGrade {E : Type} [Field E] (s : Shape) (q : ℕ)
    (f : GradeSlot s q → E[X]) (k : GradeSlot s q) (l : ℕ) :
    (zeroGrade s q f k).coeff l =
      ∑ j : GradeSlot s q,
        if k.val ≤ j.val ∧ q - j.val + k.val ≤ l then
          (j.val.choose k.val : E) * (f j).coeff (l - (q - j.val + k.val))
        else 0 := by
  rw [zeroGrade, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : k.val ≤ j.val
  · rw [ite_eq_left hj, coeff_mul_X_pow', coeff_mul_C]
    by_cases hl : q - j.val + k.val ≤ l
    · simp only [hj, hl, and_self, ite_true, mul_comm]
    · simp [hj, hl]
  · simp [hj]
end K1_14_1_7_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_1_7_3
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
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
end
end K1_14_1_7_3
end
section
namespace K1_14_3_4_5
noncomputable section
open K1_14 K1_14_3 Polynomial
abbrev Plane (F : Type*) [Semiring F] := Polynomial (Polynomial F)
def inner {R : Type*} [Semiring R] : Plane R := Polynomial.C (R := Polynomial R) (Polynomial.X (R := R))
def outer {R : Type*} [Semiring R] : Plane R := Polynomial.X (R := Polynomial R)
def parameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def parameterInPlane (i : Fin 4) : Plane SectionField := C (C (parameter i))
def seedValues (k : Slice) : Fin 2 → Plane SectionField :=
  match k with
  | .seed => ![parameterInPlane 2, parameterInPlane 3]
  | .ordinate | .mixed => ![parameterInPlane 2 - parameterInPlane 0 * inner, inner]
  | .jets => ![inner, outer]
def derivativeValue (k : Slice) : Plane SectionField :=
  match k with
  | .jets => parameterInPlane 3
  | _ => outer
def evalRow {F R : Type*} [CommRing F] [CommRing R] (a : F →+* R)
    (t : Fin 2 → R) (y v : R) : Polynomial (Polynomial (MvPolynomial (Fin 2) F)) →+* R :=
  eval₂RingHom (eval₂RingHom (MvPolynomial.eval₂Hom a t) y) v
end
end K1_14_3_4_5
end
section
namespace K1_14_3_4_5
noncomputable section
open K1_14 K1_14_3 K1_14_3_4 Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
local instance sectionRing : CommRing SectionJet := Polynomial.commRing
@[simp] theorem evalRow_const {F R : Type*} [CommRing F] [CommRing R]
    (a : F →+* R) (t : Fin 2 → R) (y v : R) (c : F) :
    evalRow a t y v (C (C (MvPolynomial.C c))) = a c := by
  simp [evalRow]
@[simp] theorem evalRow_seed {F R : Type*} [CommRing F] [CommRing R]
    (a : F →+* R) (t : Fin 2 → R) (y v : R) (i : Fin 2) :
    evalRow a t y v (C (C (MvPolynomial.X i))) = t i := by
  simp [evalRow]
@[simp] theorem evalRow_y {F R : Type*} [CommRing F] [CommRing R]
    (a : F →+* R) (t : Fin 2 → R) (y v : R) :
    evalRow a t y v (C (R := Polynomial (MvPolynomial (Fin 2) F)) (Polynomial.X (R := MvPolynomial (Fin 2) F))) = y := by
  simp [evalRow]
@[simp] theorem evalRow_v {F R : Type*} [CommRing F] [CommRing R]
    (a : F →+* R) (t : Fin 2 → R) (y v : R) :
    evalRow a t y v (Polynomial.X (R := Polynomial (MvPolynomial (Fin 2) F))) = v := by
  simp [evalRow]
theorem rowHom_ext {F R : Type*} [CommRing F] [CommRing R]
    {f g : Polynomial (Polynomial (MvPolynomial (Fin 2) F)) →+* R}
    (hc : ∀ c : F, f (C (C (MvPolynomial.C c))) = g (C (C (MvPolynomial.C c))))
    (ht : ∀ i, f (C (C (MvPolynomial.X i))) = g (C (C (MvPolynomial.X i))))
    (hy : f (C (R := Polynomial (MvPolynomial (Fin 2) F)) (Polynomial.X (R := MvPolynomial (Fin 2) F))) =
      g (C (R := Polynomial (MvPolynomial (Fin 2) F)) (Polynomial.X (R := MvPolynomial (Fin 2) F))))
    (hv : f (Polynomial.X (R := Polynomial (MvPolynomial (Fin 2) F))) =
      g (Polynomial.X (R := Polynomial (MvPolynomial (Fin 2) F)))) : f = g := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext <;> assumption
    · exact hy
  · exact hv
end
end K1_14_3_4_5
end
section
namespace K1_14_3_4_5_1
noncomputable section
open K1_14 K1_14_3 K1_14_3_2 K1_14_3_4_5 Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
private abbrev Extended := MvPolynomial (Fin 2) Jet
private abbrev Parameters := MvPolynomial (Fin 4) FX
private abbrev RawPlane := Plane Parameters
private def rawParameter (i : Fin 4) : RawPlane := C (C (MvPolynomial.X i))
private def rawSeeds (k : Slice) : Fin 2 → RawPlane :=
  match k with
  | .seed => ![rawParameter 2, rawParameter 3]
  | .ordinate | .mixed => ![rawParameter 2 - rawParameter 0 * K1_14_3_4_5.inner, K1_14_3_4_5.inner]
  | .jets => ![K1_14_3_4_5.inner, outer]
private def rawY (k : Slice) : RawPlane :=
  match k with
  | .seed => K1_14_3_4_5.inner
  | .ordinate => rawParameter 3
  | .mixed => rawParameter 3 - rawParameter 1 * outer
  | .jets => rawParameter 2
private def rawV (k : Slice) : RawPlane :=
  match k with
  | .jets => rawParameter 3
  | _ => outer
private def rawRow (k : Slice) : Jet →+* RawPlane :=
  evalRow (C.comp (C.comp MvPolynomial.C)) (rawSeeds k) (rawY k) (rawV k)
private def slopeIndex (i : Fin 2) : Fin 4 := Fin.castLE (by decide) i
private def forward (k : Slice) : Extended →+* RawPlane :=
  MvPolynomial.eval₂Hom (rawRow k) (fun i => rawParameter (slopeIndex i))
private abbrev oldSeed (i : Fin 2) : Extended :=
  MvPolynomial.C (C (C (MvPolynomial.X i)))
private abbrev oldY : Extended := MvPolynomial.C (C (Polynomial.X (R := Seeds)))
private abbrev oldV : Extended :=
  MvPolynomial.C (Polynomial.X (R := Polynomial Seeds))
private abbrev slope (i : Fin 2) : Extended := MvPolynomial.X i
private def parameterBack (k : Slice) : Fin 4 → Extended :=
  match k with
  | .seed => ![slope 0, slope 1, oldSeed 0, oldSeed 1]
  | .ordinate => ![slope 0, slope 1, oldSeed 0 + slope 0 * oldSeed 1, oldY]
  | .mixed => ![slope 0, slope 1, oldSeed 0 + slope 0 * oldSeed 1, oldY + slope 1 * oldV]
  | .jets => ![slope 0, slope 1, oldY, oldV]
private def innerBack (k : Slice) : Extended :=
  match k with
  | .seed => oldY
  | .ordinate | .mixed => oldSeed 1
  | .jets => oldSeed 0
private def outerBack (k : Slice) : Extended :=
  match k with
  | .jets => oldSeed 1
  | _ => oldV
private def back (k : Slice) : RawPlane →+* Extended :=
  eval₂RingHom
    (eval₂RingHom
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (C.comp (C.comp MvPolynomial.C)))
        (parameterBack k)) (innerBack k)) (outerBack k)
@[simp] private theorem forward_const (k : Slice) (c : FX) :
    forward k (MvPolynomial.C (C (C (MvPolynomial.C c)))) =
      C (C (MvPolynomial.C c)) := by
  simp [forward, rawRow]
@[simp] private theorem forward_seed (k : Slice) (i : Fin 2) :
    forward k (oldSeed i) = rawSeeds k i := by
  simp [forward, rawRow]
@[simp] private theorem forward_y (k : Slice) : forward k oldY = rawY k := by
  simp [forward, rawRow]
@[simp] private theorem forward_v (k : Slice) : forward k oldV = rawV k := by
  simp [forward, rawRow]
@[simp] private theorem forward_slope (k : Slice) (i : Fin 2) :
    forward k (slope i) = rawParameter (slopeIndex i) := by
  simp [forward]
@[simp] private theorem back_const (k : Slice) (c : FX) :
    back k (C (C (MvPolynomial.C c))) = MvPolynomial.C (C (C (MvPolynomial.C c))) := by
  simp [back]
@[simp] private theorem back_parameter (k : Slice) (i : Fin 4) :
    back k (rawParameter i) = parameterBack k i := by
  simp [back, rawParameter]
@[simp] private theorem back_inner (k : Slice) :
    back k K1_14_3_4_5.inner = innerBack k := by
  simp [back, K1_14_3_4_5.inner]
@[simp] private theorem back_outer (k : Slice) :
    back k outer = outerBack k := by
  simp [back, outer]
private theorem forward_back (k : Slice) : (forward k).comp (back k) = RingHom.id RawPlane := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        change forward k (back k (C (C (MvPolynomial.C c)))) = _
        simp
      · intro i
        change forward k (back k (rawParameter i)) = rawParameter i
        fin_cases i <;> cases k <;>
          simp [parameterBack, slopeIndex, rawSeeds, rawY, rawV]
    · change forward k (back k K1_14_3_4_5.inner) = K1_14_3_4_5.inner
      cases k <;> simp [innerBack, rawSeeds, rawY]
  · change forward k (back k outer) = outer
    cases k <;> simp [outerBack, rawSeeds, rawV]
private theorem back_forward (k : Slice) : (back k).comp (forward k) = RingHom.id Extended := by
  apply MvPolynomial.ringHom_ext'
  · apply K1_14_3_4_5.rowHom_ext
    · intro c
      change back k (forward k (MvPolynomial.C (C (C (MvPolynomial.C c))))) = _
      simp
    · intro i
      change back k (forward k (oldSeed i)) = oldSeed i
      fin_cases i <;> cases k <;> simp [rawSeeds, parameterBack, innerBack, outerBack]
    · change back k (forward k oldY) = oldY
      cases k <;> simp [rawY, parameterBack, innerBack, outerBack]
    · change back k (forward k oldV) = oldV
      cases k <;> simp [rawV, parameterBack, outerBack]
  · intro i
    change back k (forward k (slope i)) = slope i
    fin_cases i <;> cases k <;> simp [slopeIndex, parameterBack]
private def coordinates (k : Slice) : Extended ≃+* RawPlane :=
  RingEquiv.ofRingHom (forward k) (back k) (forward_back k) (back_forward k)
@[simp] private theorem coordinates_C (k : Slice) (x : Jet) :
    coordinates k (MvPolynomial.C x) = rawRow k x := by
  change forward k (MvPolynomial.C x) = _
  simp [forward]
attribute [local instance] Polynomial.algebra
private abbrev denominators : Submonoid RawPlane :=
  ((nonZeroDivisors Parameters).map (C : Parameters →+* Polynomial Parameters)).map
    (C : Polynomial Parameters →+* RawPlane)
private instance : IsLocalization denominators (Plane SectionField) := by
  let := Polynomial.isLocalization (nonZeroDivisors Parameters) SectionField
  exact Polynomial.isLocalization
    ((nonZeroDivisors Parameters).map (C : Parameters →+* Polynomial Parameters))
      (Polynomial SectionField)
end
end K1_14_3_4_5_1
end
section
set_option autoImplicit false
namespace K1_11
noncomputable section
open K1 MvPolynomial
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  omitted : U.degreeOf 1 = 0 ∧ U.degreeOf 2 = 0 ∧
    V.degreeOf 1 = 0 ∧ V.degreeOf 2 = 0
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  boxes : U.degreeOf 3 ≤ 1 ∧ U.degreeOf 4 ≤ 2 ∧ V.degreeOf 3 ≤ 2 ∧ V.degreeOf 4 ≤ 1
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : aeval ![Polynomial.X, 0, 0, seed, seed ^ p] U =
    Polynomial.C content * leftU R
  graphV : aeval ![Polynomial.X, 0, 0, seed, seed ^ p] V =
    Polynomial.C content * leftV R
  original_height : 24597 ≤ T.height
structure Puncture (deleted : Finset I) where
  N : ℕ
  index : Fin N ↪ I
  retained : ∀ i, i ∈ Set.range index ↔ i ∉ deleted
  size : N + deleted.card = 262144
def Puncture.nodes {deleted : Finset I} (P : Puncture deleted) (i : Fin P.N) : K :=
  node (P.index i)
structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted
inductive Bank
  | symmetric
  | lowS
  | lowT
def Bank.dS : Bank → ℕ
  | .symmetric => 2
  | .lowS => 1
  | .lowT => 2
def Bank.dT : Bank → ℕ
  | .symmetric => 2
  | .lowS => 2
  | .lowT => 1
def Bank.s : Bank → ℕ
  | .symmetric => 10
  | .lowS => 14
  | .lowT => 9
def Bank.t : Bank → ℕ
  | .symmetric => 10
  | .lowS => 9
  | .lowT => 14
def Bank.a (b : Bank) : ℕ := b.s + 5 * b.dS
def Bank.b (b : Bank) : ℕ := b.t + 5 * (b.dT - 1)
def Bank.E (b : Bank) : ℕ := b.a + b.b
def Bank.M (b : Bank) : ℕ := (2 * 131071 - 1) * (b.E - 1) + 1
def Bank.relationBounds (b : Bank) (H : ℕ) : Fin 4 → ℕ := ![131071 + H, 1, b.dS, b.dT]
structure ContactInput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (b : Bank) (H : ℕ) where
  L : MvPolynomial (Fin 5) K
  L_ne : L ≠ 0
  degrees : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j
  order_one : ∀ i : Fin P.N,
    (contactLift contactWeight
      (contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) L)).natTrailingDegree = 1
  numerator : MvPolynomial (Fin 4) K
  denominator : MvPolynomial (Fin 4) K
  denominator_ne : denominator ≠ 0
  linear : polynomialView L =
    Polynomial.C denominator * Polynomial.X - Polynomial.C numerator
  primitive : (Polynomial.C denominator * Polynomial.X - Polynomial.C numerator).IsPrimitive
  numerator_Y : numerator.weightedTotalDegree scalarWeightY ≤ 1
  denominator_Y : denominator.weightedTotalDegree scalarWeightY ≤ 0
  numerator_S : numerator.weightedTotalDegree scalarWeightYS ≤ b.dS
  denominator_S : denominator.weightedTotalDegree scalarWeightYS ≤ b.dS
  numerator_T : numerator.weightedTotalDegree scalarWeightT ≤ b.dT
  denominator_T : denominator.weightedTotalDegree scalarWeightT ≤ b.dT - 1
def scalarWeightTotal : Fin 4 → ℕ := ![0, 1, 1, 1]
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0
def nodeCut (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (numerator : Polynomial (MvPolynomial (Fin 3) Frac)) (denominator : MvPolynomial (Fin 3) Frac)
    (i : Fin P.N) : MvPolynomial (Fin 3) Frac :=
  numerator.eval (C (algebraMap K Frac (P.nodes i))) -
    denominator * (C (algebraMap K Frac (u 0 (P.index i))) +
      MvPolynomial.X 1 * C (algebraMap K Frac (u 1 (P.index i))))
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)
end
end K1_11
end
section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace K1_11
noncomputable section
open MvPolynomial
private theorem exists_kernel_outside {F E G : Type*} [Field F]
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
variable {F : Type*} [Field F]
structure ContactData (N : ℕ) (L : MvPolynomial (Fin 5) F) (b : Bank) where
  x : Fin N → F
  first : Fin N → F
  firstSlope : Fin N → F
  second : Fin N → F
  secondSlope : Fin N → F
  nonzero : L ≠ 0
  degreeS : L.weightedTotalDegree (sourceWeights 1 2) ≤ b.dS
  degreeT : L.weightedTotalDegree (sourceWeights 1 3) ≤ b.dT
  order_one : ∀ i, (contactLift contactWeight
    (contactShift (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree = 1
variable {N : ℕ} {L : MvPolynomial (Fin 5) F} {b : Bank} {H : ℕ} (D : ContactData N L b)
end
end K1_11
end
section
set_option autoImplicit false
namespace K1_11_1
noncomputable section
open Polynomial Matrix FrobeniusLocator
abbrev Seeds (F : Type) [Field F] := MvPolynomial (Fin 2) F
abbrev PlaneField (F : Type) [Field F] := FractionRing (Seeds F)
def graph {F : Type} [Field F] (p : ℕ) : Seeds F →ₐ[F] F[X] :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.X ^ p]
def coefficientPrimitive {A ι : Type} [CommMonoid A] (v : ι → A) : Prop :=
  ∀ q : A, (∀ i, q ∣ v i) → IsUnit q
def planePair {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) : (Seeds F)[X] :=
  Principal.assemble (fun j => Q (b, j))
def blockDegree {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b i : Fin 2) : ℕ :=
  Finset.univ.sup (fun j : Fin (h + 1) => (Q (b, j)).degreeOf i)
def planeSyndrome {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (b : Fin 2) (j : ℕ) : Seeds F :=
  if b = 0 then
    MvPolynomial.C (syndrome x u j) + MvPolynomial.X b * MvPolynomial.C (syndrome x v j)
  else
    MvPolynomial.C (syndrome x u j ^ p) + MvPolynomial.X b * MvPolynomial.C (syndrome x v j ^ p)
def planeSlice {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (m h : ℕ) :
    Matrix (Fin (m - h)) (Fin 2 × Fin (h + 1)) (Seeds F) :=
  fun j b => planeSyndrome p x u v b.1 (b.2.val + j.val)
def planeStack {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (L t : ℕ) : Matrix (Fin 2 × Fin L) (Fin (t + 1)) (Seeds F) :=
  fun b j => planeSyndrome p x u v b.1 (b.2.val + j.val)
def seedPositions : Fin 2 → Fin 5 := ![3, 4]
def intoFive {F : Type} [Field F] : (Seeds F)[X] →+* MvPolynomial (Fin 5) F :=
  Polynomial.eval₂RingHom (MvPolynomial.rename seedPositions).toRingHom (MvPolynomial.X 0)
end
end K1_11_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11_1
noncomputable section
open MvPolynomial Finset Polynomial
open FrobeniusLocator
variable {F : Type} [Field F]
def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1
theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption
theorem graph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    graph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [graph,MvPolynomial.aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]
theorem graph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0 < p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (graph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : graph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,graph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    rw [Polynomial.coeff_monomial,ite_eq_right]
    intro h
    apply hfe
    apply graphExponent_injOn p hp
    · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
    · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
    · exact h
  · simp
theorem graph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0 < p) : graph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := graph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm
section Rank
open Matrix
variable {r H J : ℕ}
private theorem exists_rank_minor {ι κ E : Type} [Fintype ι] [Fintype κ] [Field E]
    (A : Matrix ι κ E) :
    ∃ (rows : Fin A.rank → ι) (cols : Fin A.rank → κ), (A.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis
    (Polynomial.evalRingHom (0 : E)) (A.map Polynomial.C) A.rank (by
      have heq : (A.map Polynomial.C).map (Polynomial.evalRingHom (0 : E)) = A := by
        ext i j
        simp
      rw [heq])
  refine ⟨B.rows, B.cols, ?_⟩
  intro h
  apply B.minor_ne
  change ((A.submatrix B.rows B.cols).map Polynomial.C).det = 0
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
private theorem minor_degree {υ : Type} [Fintype υ] [DecidableEq υ]
    (i : Fin 2) (A : Matrix υ υ (Seeds F)) (d : υ → ℕ)
    (hd : ∀ j k, (A j k).degreeOf i ≤ d k) :
    A.det.degreeOf i ≤ ∑ k, d k := by
  classical
  rw [Matrix.det_apply']
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  have hc : ((↑↑(Equiv.Perm.sign σ) : Seeds F)).degreeOf i = 0 := by
    rw [← map_intCast (MvPolynomial.C : F →+* Seeds F), degreeOf_C]
  apply (degreeOf_mul_le _ _ _).trans
  rw [hc, zero_add]
  exact (degreeOf_prod_le _ _ _).trans (Finset.sum_le_sum (fun k _ => hd (σ k) k))
private theorem graph_minor_ne_zero (p : ℕ) (hp : 0 < p) (hH : H < p)
    (A : Matrix (Fin J) (Fin 2 × Fin H) (Seeds F))
    (hd : ∀ j k, (A j k).degreeOf 0 ≤ if k.1 = 0 then 1 else 0)
    (rows : Fin r → Fin J) (cols : Fin r → Fin 2 × Fin H)
    (hminor : (A.submatrix rows cols).det ≠ 0) :
    graph p (A.submatrix rows cols).det ≠ 0 := by
  classical
  have hinj : Function.Injective cols := by
    intro j k hjk
    by_contra hne
    exact hminor (Matrix.det_zero_of_column_eq hne (by
      intro l
      change A (rows l) (cols j) = A (rows l) (cols k)
      rw [hjk]))
  apply graph_ne_zero p hp _ hminor
  apply (minor_degree 0 (A.submatrix rows cols) (fun k => if (cols k).1 = 0 then 1 else 0)
    (fun j k => hd (rows j) (cols k))).trans_lt
  apply lt_of_le_of_lt _ hH
  let S : Finset (Fin r) := Finset.univ.filter (fun k => (cols k).1 = 0)
  have hsum : (∑ k, if (cols k).1 = 0 then 1 else 0) = S.card := by
    simp [S, Finset.sum_boole]
  rw [hsum]
  have hle : S.card ≤ Fintype.card (Fin H) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_le_of_injective (fun k : S => (cols k.val).2) ?_
    intro j k hjk
    apply Subtype.ext
    apply hinj
    have hj : (cols j.val).1 = 0 := (Finset.mem_filter.mp j.property).2
    have hk : (cols k.val).1 = 0 := (Finset.mem_filter.mp k.property).2
    exact Prod.ext (hj.trans hk.symm) hjk
  simpa only [Fintype.card_fin] using hle
theorem rank_graph (q : ℕ) (hq : 0 < q) (hH : H < q)
    (A : Matrix (Fin J) (Fin 2 × Fin H) (Seeds F))
    (hd : ∀ j k, (A j k).degreeOf 0 ≤ if k.1 = 0 then 1 else 0) :
    (A.map (algebraMap (Seeds F) (PlaneField F))).rank =
      (A.map ((algebraMap F[X] (FrobeniusLocator.GenericLayer.GenericField F)).comp
        (graph q).toRingHom)).rank := by
  let f := algebraMap (Seeds F) (PlaneField F)
  let g := (algebraMap F[X] (FrobeniusLocator.GenericLayer.GenericField F)).comp
    (graph (F := F) q).toRingHom
  have hdet {E : Type} [Field E] (φ : Seeds F →+* E) {s : ℕ} (rows : Fin s → Fin J) (cols : Fin s → Fin 2 × Fin H) :
      ((A.map φ).submatrix rows cols).det = φ (A.submatrix rows cols).det := by
    have he := φ.map_det (A.submatrix rows cols)
    rw [RingHom.mapMatrix_apply] at he
    exact he.symm
  change (A.map f).rank = (A.map g).rank
  apply le_antisymm
  · obtain ⟨rows, cols, hn⟩ := exists_rank_minor (A.map f)
    rw [hdet f] at hn
    have hn' : (A.submatrix rows cols).det ≠ 0 := fun h => hn (by rw [h, map_zero])
    have hg : ((A.map g).submatrix rows cols).det ≠ 0 := by
      rw [hdet g]
      change algebraMap F[X] (GenericLayer.GenericField F) (graph q _) ≠ 0
      rw [← map_zero (algebraMap F[X] (GenericLayer.GenericField F))]
      exact (IsFractionRing.injective F[X] _).ne
        (graph_minor_ne_zero q hq hH A hd rows cols hn')
    have h := Matrix.rank_submatrix_le (A.map g) rows cols
    rwa [Matrix.rank_of_det_ne_zero hg, Fintype.card_fin] at h
  · obtain ⟨rows, cols, hn⟩ := exists_rank_minor (A.map g)
    rw [hdet g] at hn
    have hn' : (A.submatrix rows cols).det ≠ 0 := fun h => hn (by rw [h, map_zero])
    have hf : ((A.map f).submatrix rows cols).det ≠ 0 := by
      rw [hdet f]
      rw [← map_zero f]
      exact (IsFractionRing.injective (Seeds F) _).ne hn'
    have h := Matrix.rank_submatrix_le (A.map f) rows cols
    rwa [Matrix.rank_of_det_ne_zero hf, Fintype.card_fin] at h
end Rank
end
end K1_11_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace K1_11
noncomputable section
open K1 MvPolynomial
variable {u : Words} {deleted : Finset I} {P : Puncture deleted} {b : Bank} {H : ℕ}
    (D : ContactInput u P b H)
def correctOn (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (Q Q' : Polynomial K) (s t : K) (S : Finset (Fin P.N)) : Prop :=
  ∀ i ∈ S, Q.eval (P.nodes i) = u 0 (P.index i) + s * u 1 (P.index i) ∧
    Q'.eval (P.nodes i) = u 0 (P.index i) ^ p + t * u 1 (P.index i) ^ p
theorem nodes_injective : Function.Injective P.nodes :=
  ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective
end
end K1_11
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11_1
noncomputable section
open Polynomial Matrix FrobeniusLocator
open scoped BigOperators nonZeroDivisors
theorem mulVec_map {A B ι κ : Type} [CommRing A] [CommRing B] [Fintype κ]
    (f : A →+* B) (M : Matrix ι κ A) (v : κ → A) :
    (M.map f).mulVec (fun j => f (v j)) = fun i => f (M.mulVec v i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
private theorem primitive_vector {A κ : Type} [CommRing A] [IsDomain A]
    [NormalizedGCDMonoid A] [Fintype κ] (v : κ → A) (hv : v ≠ 0) :
    ∃ (g : A) (Q : κ → A), g ≠ 0 ∧ v = g • Q ∧ coefficientPrimitive Q := by
  classical
  let g := Finset.univ.gcd v
  have hdiv (i : κ) : g ∣ v i := Finset.gcd_dvd (Finset.mem_univ i)
  have hg : g ≠ 0 := by
    intro he
    apply hv
    funext i
    simpa only [he, zero_dvd_iff, Pi.zero_apply] using hdiv i
  choose Q hQ using hdiv
  refine ⟨g, Q, hg, funext hQ, fun q hq => ?_⟩
  have hd : g * q ∣ g := Finset.dvd_gcd (fun i _ => by
    rw [hQ i, mul_dvd_mul_iff_left hg]
    exact hq i)
  apply isUnit_iff_dvd_one.mpr
  apply (mul_dvd_mul_iff_left hg).mp
  simpa only [mul_one] using hd
theorem plane_generator {F ι κ : Type} [Field F] [Fintype κ]
    (M : Matrix ι κ (Seeds F))
    (hn : 0 < Module.finrank (PlaneField F)
      (LinearMap.ker (M.map (algebraMap (Seeds F) (PlaneField F))).mulVecLin)) :
    ∃ Q : κ → Seeds F, Q ≠ 0 ∧ M.mulVec Q = 0 ∧ coefficientPrimitive Q := by
  classical
  let N := M.map (algebraMap (Seeds F) (PlaneField F))
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hn
  let v : κ → PlaneField F := w.val
  have hv : v ≠ 0 := fun he => hw (Subtype.ext he)
  have hk : N.mulVec v = 0 := w.property
  let D := (Seeds F)⁰
  let g := IsLocalization.commonDenom D Finset.univ v
  let W (i : κ) : Seeds F := IsLocalization.integerMultiple D Finset.univ v ⟨i, Finset.mem_univ i⟩
  have hW (i : κ) : algebraMap (Seeds F) (PlaneField F) (W i) =
      algebraMap (Seeds F) (PlaneField F) (g : Seeds F) * v i := by
    have he := IsLocalization.map_integerMultiple D Finset.univ v ⟨i, Finset.mem_univ i⟩
    change _ = (g : Seeds F) • v i at he
    simpa only [Algebra.smul_def] using he
  have hg : algebraMap (Seeds F) (PlaneField F) (g : Seeds F) ≠ 0 :=
    fun hz => (mem_nonZeroDivisors_iff_ne_zero.mp g.property)
      (IsFractionRing.injective (Seeds F) (PlaneField F) (hz.trans (map_zero _).symm))
  have hWne : W ≠ 0 := by
    intro he
    apply hv
    funext i
    have hf := hW i
    rw [he, Pi.zero_apply, map_zero] at hf
    exact (mul_eq_zero.mp hf.symm).resolve_left hg
  have hWM : M.mulVec W = 0 := by
    have h := mulVec_map (algebraMap (Seeds F) (PlaneField F)) M W
    simp only [hW] at h
    change N.mulVec ((algebraMap (Seeds F) (PlaneField F) (g : Seeds F)) • v) = _ at h
    rw [Matrix.mulVec_smul, hk, smul_zero] at h
    funext i
    apply IsFractionRing.injective (Seeds F) (PlaneField F)
    rw [Pi.zero_apply, map_zero]
    exact (congrFun h i).symm
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := Seeds F)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Seeds F)
  obtain ⟨a, Q, ha, he, hp⟩ := primitive_vector W hWne
  refine ⟨Q, ?_, ?_, hp⟩
  · intro hz
    rw [hz, smul_zero] at he
    exact hWne he
  · rw [he, Matrix.mulVec_smul] at hWM
    funext i
    exact (mul_eq_zero.mp (congrFun hWM i)).resolve_left ha
theorem shifts_annihilate {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (h L s t : ℕ) (hs : h + s = L)
    (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (hQ : (planeSlice p x u v (L + t) h).mulVec Q = 0) :
    (K1_6.shifts (planePair Q) L s).transpose * planeStack p x u v L t = 0 := by
  classical
  apply Matrix.ext
  intro d j
  let e : Fin 2 × Fin (h + 1) ↪ Fin 2 × Fin L :=
    ⟨fun z => (z.1, ⟨z.2.val + d.val, by have := z.2.isLt; have := d.isLt; omega⟩),
      fun a b hab => Prod.ext (congrArg (fun z : Fin 2 × Fin L => z.1) hab)
        (Fin.ext (by
          have he := congrArg (fun z : Fin 2 × Fin L => z.2.val) hab
          exact Nat.add_right_cancel he))⟩
  let jd : Fin (L + t - h) := ⟨j.val + d.val, by have := j.isLt; have := d.isLt; omega⟩
  have hshift (z : Fin 2 × Fin (h + 1)) :
      (K1_6.shifts (planePair Q) L s) (e z) d = Q z := by
    change (planePair Q z.1 * Polynomial.X ^ d.val).coeff (z.2.val + d.val) = Q z
    rw [coeff_mul_X_pow, planePair, Principal.assemble_coeff]
  have hzero (z : Fin 2 × Fin L) (hz : z ∉ Set.range e) :
      (K1_6.shifts (planePair Q) L s) z d = 0 := by
    change (planePair Q z.1 * Polynomial.X ^ d.val).coeff z.2.val = 0
    by_cases hlo : z.2.val < d.val
    · rw [coeff_mul_X_pow', ite_eq_right (not_le.mpr hlo)]
    · have hhi : h < z.2.val - d.val := by
        by_contra! hh
        apply hz
        refine ⟨(z.1, ⟨z.2.val - d.val, by omega⟩), Prod.ext rfl (Fin.ext ?_)⟩
        change z.2.val - d.val + d.val = z.2.val
        omega
      have he : z.2.val - d.val + d.val = z.2.val := Nat.sub_add_cancel (by omega)
      rw [← he, coeff_mul_X_pow]
      exact coeff_eq_zero_of_natDegree_lt ((Principal.assemble_natDegree_le _).trans_lt hhi)
  change (∑ z, K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j) = 0
  have hsum : (∑ z : Fin 2 × Fin L, K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j) =
      ∑ z : Fin 2 × Fin (h + 1), K1_6.shifts (planePair Q) L s (e z) d *
        planeStack p x u v L t (e z) j := by
    let f (z : Fin 2 × Fin L) := K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j
    calc
      _ = ∑ z ∈ Finset.univ.map e, f z := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro z _ hz
        change K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j = 0
        rw [hzero z (fun hm => hz (by
          obtain ⟨w, rfl⟩ := hm
          exact Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩)), zero_mul]
      _ = _ := Finset.sum_map _ e f
  rw [hsum]
  have hk := congrFun hQ jd
  change (∑ z, planeSlice p x u v (L + t) h jd z * Q z) = 0 at hk
  rw [← hk]
  apply Finset.sum_congr rfl
  intro z _
  rw [hshift, mul_comm]
  congr 1
  change planeSyndrome p x u v z.1 (z.2.val + d.val + j.val) =
    planeSyndrome p x u v z.1 (z.2.val + (j.val + d.val))
  congr 1
  omega
end
end K1_11_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000
namespace K1_11_1
noncomputable section
open Polynomial Matrix FrobeniusLocator K1 ProximityPrize.Benchmark
open scoped BigOperators
private theorem graph_syndrome {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (b : Fin 2) (j : ℕ) :
    graph q (planeSyndrome q x u v b j) = Principal.parameterSyndromes q x u v b j := by
  fin_cases b <;> simp [graph, planeSyndrome, Principal.parameterSyndromes]
private theorem syndrome_degree {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (b i : Fin 2) (j : ℕ) :
    (planeSyndrome q x u v b j).degreeOf i ≤ if b = i then 1 else 0 := by
  have h (a c : F) :
      (MvPolynomial.C a + MvPolynomial.X b * MvPolynomial.C c).degreeOf i ≤
        if b = i then 1 else 0 := by
    apply (MvPolynomial.degreeOf_add_le i _ _).trans
    apply max_le
    · simp
    · apply (MvPolynomial.degreeOf_mul_C_le _ _ _).trans
      rw [MvPolynomial.degreeOf_X]
      by_cases he : b = i
      · simp [he]
      · simp [he, Ne.symm he]
  unfold planeSyndrome
  by_cases hb : b = 0
  · simpa only [hb, ite_true] using h (syndrome x u j) (syndrome x v j)
  · simpa only [hb, ite_false] using h (syndrome x u j ^ q) (syndrome x v j ^ q)
private theorem graph_slice_map {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (m h : ℕ) :
    (planeSlice q x u v m h).map
        ((algebraMap F[X] (GenericLayer.GenericField F)).comp (graph q).toRingHom) =
      (Strata.parameterRelation q x u v m h).map (algebraMap F[X] (GenericLayer.GenericField F)) := by
  apply Matrix.ext
  intro j b
  change algebraMap F[X] (GenericLayer.GenericField F)
      (graph q (planeSyndrome q x u v b.1 (b.2.val + j.val))) =
    algebraMap F[X] (GenericLayer.GenericField F)
      (Principal.parameterSyndromes q x u v b.1 (b.2.val + j.val))
  rw [graph_syndrome]
private theorem graph_stack_map {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (L t : ℕ) :
    (planeStack q x u v L t).map
        ((algebraMap F[X] (GenericLayer.GenericField F)).comp (graph q).toRingHom) =
      (stacked q x u v L t).map (algebraMap F[X] (GenericLayer.GenericField F)) := by
  apply Matrix.ext
  intro b j
  change algebraMap F[X] (GenericLayer.GenericField F)
      (graph q (planeSyndrome q x u v b.1 (b.2.val + j.val))) =
    algebraMap F[X] (GenericLayer.GenericField F)
      (Principal.parameterSyndromes q x u v b.1 (b.2.val + j.val))
  rw [graph_syndrome]
private theorem map_syndrome {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (f : F →+* E)
    (x w : ι → F) (j : ℕ) :
    f (syndrome x w j) = syndrome (fun i => f (x i)) (fun i => f (w i)) j := by
  simp only [syndrome, weight, map_sum, map_mul, map_pow, map_inv₀, map_prod, map_sub]
private theorem certificate_kernel {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) [ExpChar F q] (x u v : ι → F) (hx : Function.Injective x)
    (hfix : ∀ i, x i ^ q = x i) (k m h : ℕ)
    (hkm : k + m = Fintype.card ι)
    (R : Strata.PolynomialRelationCertificate q x u v k h) :
    ((Strata.parameterRelation q x u v m h).map
      (algebraMap F[X] (GenericLayer.GenericField F))).mulVec
      (fun j => algebraMap F[X] (GenericLayer.GenericField F) (R.coefficients j)) = 0 := by
  classical
  let E := GenericLayer.GenericField F
  let φ := algebraMap F[X] E
  let f := φ.comp Polynomial.C
  let y := fun i => f (x i)
  let z := φ Polynomial.X
  let w : Fin 2 → ι → E := fun b i =>
    if b = 0 then f (u i) + z * f (v i)
    else f (u i ^ q) + z ^ q * f (v i ^ q)
  let P (b : Fin 2) : E[X] := (Principal.assemble (fun j => R.coefficients (b, j))).map φ
  have hmoment (b : Fin 2) (j : ℕ) :
      φ (Principal.parameterSyndromes q x u v b j) = syndrome y (w b) j := by
    by_cases hb : b = 0
    · simp only [Principal.parameterSyndromes, hb, ite_true, map_add, map_mul]
      change f (syndrome x u j) + z * f (syndrome x v j) = _
      rw [map_syndrome, map_syndrome]
      simpa only [w, hb, ite_true, one_mul] using
        (Principal.syndrome_linear y (fun i => f (u i)) (fun i => f (v i)) 1 z j).symm
    · simp only [Principal.parameterSyndromes, hb, ite_false, map_add, map_mul]
      rw [φ.map_pow Polynomial.X]
      change f (syndrome x u j ^ q) + z ^ q * f (syndrome x v j ^ q) = _
      rw [← syndrome_frobenius q x hfix, ← syndrome_frobenius q x hfix,
        map_syndrome, map_syndrome]
      simpa only [w, hb, ite_false, one_mul] using
        (Principal.syndrome_linear y (fun i => f (u i ^ q)) (fun i => f (v i ^ q)) 1 (z ^ q) j).symm
  have hnodes (i : ι) :
      (P 0).eval (y i) * w 0 i + (P 1).eval (y i) * w 1 i =
        (R.output.map φ).eval (y i) := by
    have he := congrArg φ (R.nodes i)
    simpa only [P, y, f, RingHom.comp_apply, z, w, zero_ne_one, one_ne_zero,
      ite_true, ite_false, map_add, map_mul, map_pow, eval_map_apply] using he
  have hP (b : Fin 2) : (P b).natDegree ≤ h := natDegree_map_le.trans (R.x_degree b)
  rw [Strata.parameterRelation_map]
  apply (Strata.relation_equations _ m h _).mpr
  intro j
  have hcoeff (b : Fin 2) (l : Fin (h + 1)) :
      φ (R.coefficients (b, l)) = (P b).coeff l.val := by
    change φ (R.coefficients (b, l)) =
      ((Principal.assemble (fun j => R.coefficients (b, j))).map φ).coeff l.val
    rw [coeff_map, Principal.assemble_coeff]
  change (∑ b : Fin 2, ∑ l : Fin (h + 1),
    φ (R.coefficients (b, l)) * φ (Principal.parameterSyndromes q x u v b (l.val + j.val))) = 0
  simp only [Fin.sum_univ_two, hmoment, hcoeff]
  change (∑ l : Fin (h + 1), (P 0).coeff l.val * syndrome y (w 0) (l.val + j.val)) +
    (∑ l : Fin (h + 1), (P 1).coeff l.val * syndrome y (w 1) (l.val + j.val)) = 0
  rw [← Strata.syndrome_polynomial_multiple y (w 0) _ _ _ (hP 0),
    ← Strata.syndrome_polynomial_multiple y (w 1) _ _ _ (hP 1)]
  have hlin := Principal.syndrome_linear y
    (fun i => (P 0).eval (y i) * w 0 i) (fun i => (P 1).eval (y i) * w 1 i) 1 1 j.val
  simp only [one_mul] at hlin
  rw [← hlin]
  simp_rw [hnodes]
  exact Strata.syndrome_eval_zero y (f.injective.comp hx) _ (k + h) j.val
    (degree_map_le.trans_lt R.output_degree) (by have := j.isLt; omega)
end
end K1_11_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11
noncomputable section
open K1 FrobeniusLocator
def nativePuncture (deleted : Finset I) : Puncture deleted := by
  classical
  let kept := Finset.univ \ deleted
  let idx := kept.equivFin.symm
  refine ⟨kept.card, idx.toEmbedding.trans (Function.Embedding.subtype _), ?_, ?_⟩
  · intro i
    constructor
    · rintro ⟨j, rfl⟩
      exact (Finset.mem_sdiff.mp (idx j).property).2
    · intro hi
      let old : kept := ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
      exact ⟨idx.symm old, congrArg Subtype.val (idx.apply_symm_apply old)⟩
  · simpa only [kept, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ deleted)
def indexedSupport {deleted : Finset I} (P : Puncture deleted) (S : Finset I) : Finset (Fin P.N) :=
  Finset.univ.filter fun i => P.index i ∈ S
theorem mem_indexedSupport {deleted : Finset I} (P : Puncture deleted) (S : Finset I)
    (i : Fin P.N) : i ∈ indexedSupport P S ↔ P.index i ∈ S := by simp [indexedSupport]
theorem indexedSupport_card {deleted : Finset I} (P : Puncture deleted) (S : Finset I)
    (hS : ∀ i ∈ S, i ∉ deleted) : (indexedSupport P S).card = S.card := by
  have heq : (indexedSupport P S).map P.index = S := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact (mem_indexedSupport P S j).mp hj
    · intro hi
      obtain ⟨j, hj⟩ := (P.retained i).mpr (hS i hi)
      refine Finset.mem_map.mpr ⟨j, (mem_indexedSupport P S j).mpr ?_, hj⟩
      rwa [hj]
  calc
    (indexedSupport P S).card = ((indexedSupport P S).map P.index).card := (Finset.card_map _).symm
    _ = S.card := congrArg Finset.card heq
end
end K1_11
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_2
noncomputable section
open K1 K1_11 MvPolynomial
def OmitsMessages {F : Type*} [Field F] (Q : MvPolynomial (Fin 5) F) : Prop :=
  Q.degreeOf 1 = 0 ∧ Q.degreeOf 2 = 0
def graph {F : Type*} [Field F] (q : ℕ) :
    MvPolynomial (Fin 5) F →ₐ[F] Polynomial (Polynomial F) :=
  aeval ![Polynomial.X, 0, 0, Polynomial.C Polynomial.X, (Polynomial.C Polynomial.X)^q]
def nodeWordImages {F : Type*} [Field F] (x a b c d : F) : Fin 5 → MvPolynomial (Fin 5) F :=
  ![MvPolynomial.C x, MvPolynomial.C a + MvPolynomial.X 3 * MvPolynomial.C b,
    MvPolynomial.C c + MvPolynomial.X 4 * MvPolynomial.C d, MvPolynomial.X 3, MvPolynomial.X 4]
def nodeWordMap {F : Type*} [Field F] (x a b c d : F) :
    MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval (nodeWordImages x a b c d)
def sWeight {F : Type*} [Field F] (U V : MvPolynomial (Fin 5) F) : ℕ :=
  max (1 + U.degreeOf 3) (V.degreeOf 3)
def tWeight {F : Type*} [Field F] (U V : MvPolynomial (Fin 5) F) : ℕ :=
  max (U.degreeOf 4) (1 + V.degreeOf 4)
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : OmitsMessages U
  V_omits : OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  boxes : U.degreeOf 3 ≤ 1 ∧ U.degreeOf 4 ≤ 2 ∧ V.degreeOf 3 ≤ 2 ∧ V.degreeOf 4 ≤ 1
  graphU : graph p U = Polynomial.C A.content * D.U
  graphV : graph p V = Polynomial.C A.content * D.V
structure PlaneOutput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (H : ℕ) (U V : MvPolynomial (Fin 5) K) where
  W : MvPolynomial (Fin 5) K
  omits : OmitsMessages W
  height : W.degreeOf 0 ≤ 131071 + H
  degreeS : W.degreeOf 3 ≤ sWeight U V
  degreeT : W.degreeOf 4 ≤ tWeight U V
  node : ∀ i : Fin P.N,
    nodeWordMap (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
      (u 0 (P.index i)^p) (u 1 (P.index i)^p) (U * MvPolynomial.X 1 + V * MvPolynomial.X 2 - W) = 0
end
end K1_11_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_11_2
noncomputable section
open K1_11 MvPolynomial
variable {F : Type*} [Field F]
def contactConstant : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![0,0,0,MvPolynomial.X 3,MvPolynomial.X 4]
theorem contactConstant_monomial (e : Fin 5 →₀ ℕ) (a : F) :
    contactConstant (monomial e a)=if e.weight contactWeight<1 then monomial e a else 0 := by
  classical
  rw [contactConstant,aeval_monomial]
  by_cases h0 : e 0=0 <;> by_cases h1 : e 1=0 <;> by_cases h2 : e 2=0 <;>
    simp [Finsupp.prod_fintype,Fin.prod_univ_succ,contactWeight,weight5,
      h0,h1,h2,monomial_eq]
theorem truncation_one_monomial (e : Fin 5 →₀ ℕ) (a : F) :
    weightedTruncation contactWeight 1 (monomial e a)=
      if e.weight contactWeight<1 then monomial e a else 0 := by
  classical
  ext f
  by_cases hfe : e=f
  · subst f
    split_ifs <;> simp_all [coeff_weightedTruncation,MvPolynomial.coeff_monomial]
  · split_ifs <;> simp_all [coeff_weightedTruncation,MvPolynomial.coeff_monomial]
theorem contactConstant_eq_truncation (P : MvPolynomial (Fin 5) F) :
    contactConstant P=weightedTruncation contactWeight 1 P := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a => rw [contactConstant_monomial,truncation_one_monomial]
  | add P Q hp hq => simp only [map_add,hp,hq]
theorem exact_contact_one_of_gradient (P : MvPolynomial (Fin 5) F) (i : Fin 5)
    (hi : contactWeight i=1) (hvalue : contactConstant P=0)
    (hgradient : contactConstant (pderiv i P)≠0) :
    (contactLift contactWeight P).natTrailingDegree=1 := by
  have hzero : P∈restrictWeightedOrder contactWeight 1 := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mp
    rwa [← contactConstant_eq_truncation]
  obtain ⟨e,he⟩ := support_nonempty.mpr hgradient
  have hec := mem_support_iff.mp he
  rw [contactConstant_eq_truncation,coeff_weightedTruncation] at hec
  have heweight : e.weight contactWeight<1 := by
    by_contra hn
    exact hec (ite_eq_right hn)
  rw [ite_eq_left heweight,coeff_pderiv] at hec
  have hcoeff : P.coeff (e+Finsupp.single i 1)≠0 := left_ne_zero_of_mul hec
  have hweight : (e+Finsupp.single i 1).weight contactWeight=1 := by
    rw [map_add,Finsupp.weight_single,one_smul,hi]
    omega
  exact contact_order_one_of_coefficient contactWeight P hzero _ hweight hcoeff
theorem pderiv_zero_of_degree_zero (i : Fin 5) (P : MvPolynomial (Fin 5) F)
    (hP : P.degreeOf i=0) : pderiv i P=0 := by
  ext e
  rw [coeff_pderiv]
  have hc : P.coeff (e+Finsupp.single i 1)=0 := by
    apply notMem_support_iff.mp
    apply notMem_support_of_degreeOf_lt i
    simp [hP]
  simp [hc]
theorem linear_form_message_derivatives (U V R : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R) :
    pderiv 1 (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=U ∧ pderiv 2 (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=V := by
  constructor <;> simp [pderiv_zero_of_degree_zero _ U hU.1,
    pderiv_zero_of_degree_zero _ U hU.2,pderiv_zero_of_degree_zero _ V hV.1,
    pderiv_zero_of_degree_zero _ V hV.2,pderiv_zero_of_degree_zero _ R hR.1,
    pderiv_zero_of_degree_zero _ R hR.2]
theorem contactShift_message_derivative (x a b c d : F) (P : MvPolynomial (Fin 5) F)
    (i : Fin 5) (hi : i=1 ∨ i=2) :
    pderiv i (contactShift x a b c d P)=contactShift x a b c d (pderiv i P) := by
  have hvar (j : Fin 5) : pderiv i (contactShift x a b c d (MvPolynomial.X j))=
      contactShift x a b c d (pderiv i (MvPolynomial.X j)) := by
    rcases hi with rfl | rfl
    all_goals fin_cases j <;> simp [contactShift,shiftImages]
  induction P using MvPolynomial.induction_on with
  | C r => simp [contactShift]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P j hp => simp only [map_mul,pderiv_mul,map_add,hp,hvar]
theorem linear_relation_node_contact_one (x a b c d : F)
    (U V R : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R)
    (hnode : contactConstant (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))=0)
    (hnonzero : contactConstant (contactShift x a b c d U)≠0 ∨
      contactConstant (contactShift x a b c d V)≠0) :
    (contactLift contactWeight (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))).natTrailingDegree=1 := by
  have hd := linear_form_message_derivatives U V R hU hV hR
  rcases hnonzero with hu | hv
  · apply exact_contact_one_of_gradient _ 1 (by decide) hnode
    rw [contactShift_message_derivative x a b c d _ 1 (Or.inl rfl),hd.1]
    exact hu
  · apply exact_contact_one_of_gradient _ 2 (by decide) hnode
    rw [contactShift_message_derivative x a b c d _ 2 (Or.inr rfl),hd.2]
    exact hv
def messageTag (P : MvPolynomial (Fin 5) F) (a b : ℕ) : Prop :=
  ∀ e∈P.support,e 1=a ∧ e 2=b
theorem omitted_message_tag (P : MvPolynomial (Fin 5) F) (hP : OmitsMessages P) : messageTag P 0 0 := by
  rcases hP with ⟨hP1,hP2⟩
  intro e he
  have h1 := le_degreeOf_of_mem_support 1 he
  have h2 := le_degreeOf_of_mem_support 2 he
  exact ⟨by omega,by omega⟩
theorem relatively_prime_not_both_eval_zero {R : Type*} [CommRing R] [IsDomain R]
    (U V : Polynomial R) (hUV : IsRelPrime U V) (x : R) : U.eval x≠0 ∨ V.eval x≠0 := by
  by_contra hn
  push Not at hn
  have hu : Polynomial.X-Polynomial.C x∣U := Polynomial.dvd_iff_isRoot.mpr hn.1
  have hv : Polynomial.X-Polynomial.C x∣V := Polynomial.dvd_iff_isRoot.mpr hn.2
  exact Polynomial.not_isUnit_X_sub_C x (hUV hu hv)
def partialXMap (x : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![C x,MvPolynomial.X 1,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]
theorem contactConstant_shift (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    contactConstant (contactShift x a b c d P)=nodeWordMap x a b c d P := by
  rw [contactShift,aeval_eq_bind₁,contactConstant,aeval_bind₁]
  have hf : (fun i => aeval ![0,0,0,MvPolynomial.X 3,MvPolynomial.X 4] (shiftImages x a b c d i))=
      nodeWordImages x a b c d := by
    funext i
    fin_cases i <;> simp [shiftImages,nodeWordImages]
  rw [hf]
  rfl
theorem nodeWord_omitted_eq_partialX (x a b c d : F) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) : nodeWordMap x a b c d P=partialXMap x P := by
  change eval₂ C (nodeWordImages x a b c d) P=eval₂ C ![C x,MvPolynomial.X 1,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4] P
  apply eval₂_congr
  intro i e hi hc
  have he : e∈P.support := mem_support_iff.mpr hc
  have ht := omitted_message_tag P hP e he
  have hin : e i≠0 := Finsupp.mem_support_iff.mp hi
  have h1 : i≠1 := by intro hi1; subst i; exact hin ht.1
  have h2 : i≠2 := by intro hi2; subst i; exact hin ht.2
  fin_cases i <;> simp [nodeWordImages] at *
theorem partialX_via_polynomial (x : F) (P : MvPolynomial (Fin 5) F) :
    partialXMap x P=rename Fin.succ ((finSuccEquiv F 4 P).eval (C x)) := by
  have heq : (partialXMap x).toRingHom=
      (rename (Fin.succ : Fin 4 → Fin 5)).toRingHom.comp ((Polynomial.evalRingHom (C x)).comp (finSuccEquiv F 4).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [partialXMap,finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [partialXMap, finSuccEquiv_X_zero]
      · change partialXMap x (MvPolynomial.X j.succ) =
          rename Fin.succ ((finSuccEquiv F 4 (MvPolynomial.X j.succ)).eval (C x))
        rw [finSuccEquiv_X_succ, Polynomial.eval_C, rename_X]
        fin_cases j <;> simp [partialXMap]
  exact RingHom.congr_fun heq P
theorem relatively_prime_polynomial_view (U V : MvPolynomial (Fin 5) F)
    (hUV : IsRelPrime U V) : IsRelPrime (finSuccEquiv F 4 U) (finSuccEquiv F 4 V) := by
  intro d hdU hdV
  have hu : (finSuccEquiv F 4).symm d∣U := by
    obtain ⟨q,hq⟩ := hdU
    refine ⟨(finSuccEquiv F 4).symm q,?_⟩
    apply (finSuccEquiv F 4).injective
    simpa only [map_mul,AlgEquiv.apply_symm_apply] using hq
  have hv : (finSuccEquiv F 4).symm d∣V := by
    obtain ⟨q,hq⟩ := hdV
    refine ⟨(finSuccEquiv F 4).symm q,?_⟩
    apply (finSuccEquiv F 4).injective
    simpa only [map_mul,AlgEquiv.apply_symm_apply] using hq
  have hu' := (hUV hu hv).map (finSuccEquiv F 4).toRingHom
  change IsUnit ((finSuccEquiv F 4) ((finSuccEquiv F 4).symm d)) at hu'
  simpa only [AlgEquiv.apply_symm_apply] using hu'
theorem relatively_prime_node_nondegenerate (x a b c d : F)
    (U V : MvPolynomial (Fin 5) F) (hUV : IsRelPrime U V)
    (hU : OmitsMessages U) (hV : OmitsMessages V) :
    nodeWordMap x a b c d U≠0 ∨ nodeWordMap x a b c d V≠0 := by
  have hn := relatively_prime_not_both_eval_zero (finSuccEquiv F 4 U) (finSuccEquiv F 4 V)
    (relatively_prime_polynomial_view U V hUV) (C x)
  rw [nodeWord_omitted_eq_partialX x a b c d U hU,
    nodeWord_omitted_eq_partialX x a b c d V hV,partialX_via_polynomial,partialX_via_polynomial]
  have hinj : Function.Injective (rename (R:=F) (Fin.succ : Fin 4 → Fin 5)) :=
    rename_injective _ (Fin.succ_injective 4)
  rcases hn with hu | hv
  · left
    exact fun hz => hu (hinj (hz.trans (map_zero _).symm))
  · right
    exact fun hz => hv (hinj (hz.trans (map_zero _).symm))
theorem linear_relation_contact_order_one (x a b c d : F)
    (U V R : MvPolynomial (Fin 5) F) (hUV : IsRelPrime U V)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R)
    (hnode : nodeWordMap x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=0) :
    (contactLift contactWeight (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))).natTrailingDegree=1 := by
  apply linear_relation_node_contact_one x a b c d U V R hU hV hR
  · rwa [contactConstant_shift]
  · simpa only [contactConstant_shift] using relatively_prime_node_nondegenerate x a b c d U V hUV hU hV
end
end K1_11_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace K1_11
noncomputable section
open K1 FrobeniusLocator MvPolynomial
open scoped BigOperators
variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
private theorem seed_eq_of_mismatch {F : Type*} [Field F] {s t a b c d : F}
    (hs : a + s * b = c + s * d) (ht : a + t * b = c + t * d)
    (hm : a ≠ c ∨ b ≠ d) : s = t := by
  have hz : (s - t) * (b - d) = 0 := by linear_combination hs - ht
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · have hb := sub_eq_zero.mp h
    exact False.elim (hm.elim
      (fun hne => hne (by simpa only [hb, add_left_inj] using hs))
      (fun hne => hne hb))
variable (chart : TaylorChart u P F b Λ)
end
end K1_11
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11_1
noncomputable section
open Polynomial FrobeniusLocator
open scoped BigOperators
variable {F : Type} [Field F]
theorem degreeOf_coordinate {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b i : Fin 2) (j : Fin (h + 1)) : (Q (b, j)).degreeOf i ≤ blockDegree Q b i :=
  Finset.le_sup (f := fun j : Fin (h + 1) => (Q (b, j)).degreeOf i) (Finset.mem_univ j)
theorem seedPositions_injective : Function.Injective seedPositions := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction
private theorem rename_degree_zero (a : Seeds F) (i : Fin 5) (hi : i ∉ Set.range seedPositions) :
    (MvPolynomial.rename seedPositions a).degreeOf i = 0 := by
  by_contra h
  obtain ⟨j, _, hej⟩ := MvPolynomial.mem_vars_rename seedPositions a
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)
  exact hi ⟨j, hej⟩
private theorem intoFive_degree {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b : Fin 2) (i : Fin 5) (a d : ℕ)
    (ha : ∀ j : Fin (h + 1), (MvPolynomial.rename seedPositions (Q (b, j))).degreeOf i ≤ a)
    (hd : ∀ j : Fin (h + 1), ((MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) F) ^ j.val).degreeOf i ≤ d) :
    (intoFive (planePair Q b)).degreeOf i ≤ a + d := by
  classical
  simp only [planePair, Principal.assemble, map_sum, intoFive, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_monomial, AlgHom.toRingHom_eq_coe]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  exact Finset.sup_le fun j _ => (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (ha j) (hd j))
theorem intoFive_height {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) :
    (intoFive (planePair Q b)).degreeOf 0 ≤ h := by
  simpa only [zero_add] using intoFive_degree Q b 0 0 h
    (fun j => (rename_degree_zero (Q (b, j)) 0 (by
      rintro ⟨i, hi⟩
      fin_cases i <;> contradiction)).le)
    (fun j => by rw [MvPolynomial.degreeOf_X_self_pow]; omega)
theorem intoFive_seed_degree {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b i : Fin 2) :
    (intoFive (planePair Q b)).degreeOf (seedPositions i) ≤ blockDegree Q b i := by
  simpa only [add_zero] using intoFive_degree Q b (seedPositions i) (blockDegree Q b i) 0
    (fun j => by rw [MvPolynomial.degreeOf_rename_of_injective seedPositions_injective]; exact degreeOf_coordinate Q b i j)
    (fun j => (MvPolynomial.degreeOf_X_pow_of_ne _ (by fin_cases i <;> decide)).le)
theorem intoFive_omitted {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2)
    (i : Fin 5) (hi : i = 1 ∨ i = 2) :
    (intoFive (planePair Q b)).degreeOf i = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [zero_add] using intoFive_degree Q b i 0 0
    (fun j => (rename_degree_zero (Q (b, j)) i (by
      rintro ⟨l, rfl⟩
      fin_cases l <;> rcases hi with he | he <;> contradiction)).le)
    (fun j => (MvPolynomial.degreeOf_X_pow_of_ne _ (by rcases hi with rfl | rfl <;> decide)).le)
private def fromFive : MvPolynomial (Fin 5) F →ₐ[F] (Seeds F)[X] :=
  MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (MvPolynomial.X 0), Polynomial.C (MvPolynomial.X 1)]
private theorem fromFive_rename (a : Seeds F) :
    fromFive (MvPolynomial.rename seedPositions a) = Polynomial.C a := by
  have he : (fromFive (F := F)).toRingHom.comp (MvPolynomial.rename seedPositions).toRingHom =
      Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [fromFive]
    · intro i
      fin_cases i <;> simp [fromFive, seedPositions]
  exact RingHom.congr_fun he a
private theorem fromFive_intoFive (A : (Seeds F)[X]) : fromFive (intoFive A) = A := by
  have he : (fromFive (F := F)).toRingHom.comp intoFive = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a
      change fromFive (intoFive (Polynomial.C a)) = Polynomial.C a
      rw [intoFive, coe_eval₂RingHom, eval₂_C]
      exact fromFive_rename a
    · simp [fromFive, intoFive]
  exact RingHom.congr_fun he A
theorem intoFive_primitive {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (hQ : coefficientPrimitive Q) (a : Seeds F)
    (hU : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q 0))
    (hV : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q 1)) :
    IsUnit a := by
  have hd (b : Fin 2) : Polynomial.C a ∣ planePair Q b := by
    have hb : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q b) := by
      fin_cases b
      · exact hU
      · exact hV
    have ht := map_dvd (fromFive (F := F)) hb
    simpa only [fromFive_rename, fromFive_intoFive] using ht
  apply hQ
  rintro ⟨b, j⟩
  simpa only [planePair, Principal.assemble_coeff] using
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mp (hd b) j.val
private def graphFive (q : ℕ) : MvPolynomial (Fin 5) F →ₐ[F] F[X][X] :=
  MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (Polynomial.X : F[X]),
    (Polynomial.C (Polynomial.X : F[X])) ^ q]
private theorem graphFive_rename (q : ℕ) (a : Seeds F) :
    graphFive q (MvPolynomial.rename seedPositions a) = Polynomial.C (graph q a) := by
  have he : (graphFive (F := F) q).toRingHom.comp (MvPolynomial.rename seedPositions).toRingHom =
      Polynomial.C.comp (graph q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [graphFive, graph]
    · intro i
      fin_cases i <;> simp [graphFive, graph, seedPositions]
  exact RingHom.congr_fun he a
theorem graph_intoFive (q : ℕ) (A : (Seeds F)[X]) :
    MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (Polynomial.X : F[X]),
      (Polynomial.C (Polynomial.X : F[X])) ^ q] (intoFive A) =
      A.map (graph q).toRingHom := by
  change graphFive q (intoFive A) = _
  have he : (graphFive (F := F) q).toRingHom.comp intoFive = Polynomial.mapRingHom (graph q).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change graphFive q (intoFive (Polynomial.C a)) = (Polynomial.C a).map (graph q).toRingHom
      rw [intoFive, coe_eval₂RingHom, eval₂_C, Polynomial.map_C]
      exact graphFive_rename q a
    · simp [graphFive, intoFive]
  exact RingHom.congr_fun he A
end
end K1_11_1
end
section
set_option autoImplicit false
namespace K1_11_3
noncomputable section
open K1 K1_11 MvPolynomial
def derivativeChart {F : Type*} [CommRing F] (G : MvPolynomial (Fin 4) F) (j : ℕ) :
    MvPolynomial (Fin 4) F :=
  (fun H : MvPolynomial (Fin 4) F => pderiv 1 H)^[j] G
def SimpleRoot {F : Type*} [Field F] (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) : Prop :=
  aeval (scalarImages D s t) G = 0 ∧
    aeval (scalarImages D s t) (pderiv 1 G) ≠ 0
def implicitDeriv {F : Type*} [CommRing F] (G H : MvPolynomial (Fin 4) F) :
    MvPolynomial (Fin 4) F :=
  pderiv 1 G * pderiv 0 H - pderiv 0 G * pderiv 1 H
def implicitNumerator {F : Type*} [CommRing F] (G : MvPolynomial (Fin 4) F) :
    ℕ → MvPolynomial (Fin 4) F
  | 0 => -pderiv 0 G
  | n + 1 =>
    pderiv 1 G * implicitDeriv G (implicitNumerator G n) -
      C (↑(2 * n + 1) : F) * implicitNumerator G n * implicitDeriv G (pderiv 1 G)
def paddedTaylorCoeff {F : Type*} [Field F] (G : MvPolynomial (Fin 4) F)
    (w : ℕ) : ℕ → MvPolynomial (Fin 4) F
  | 0 => MvPolynomial.X 1 * pderiv 1 G ^ (2 * w - 1)
  | n + 1 =>
    C ((↑(Nat.factorial (n + 1)) : F)⁻¹) *
      implicitNumerator G n * pderiv 1 G ^ (2 * w - 1 - (2 * n + 1))
end
end K1_11_3
end
