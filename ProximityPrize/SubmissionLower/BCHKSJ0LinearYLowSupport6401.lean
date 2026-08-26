import ProximityPrize.SubmissionLower.BCHKSLinearYLowSupport6401
import ProximityPrize.SubmissionLower.BCHKSJ0LinearYInterpolation6401
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusWeakCurveSeed6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSJ0LinearYLowSupport6401
open ProximityPrize.Benchmark
open Polynomial
open BCHKSSubstitutionVanish
open BCHKSLinearYLowSupport6401
open BCHKSJ0ConcreteGlobalInput6400
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFrobeniusCubicMassLedger6401
open BCHKSFrobeniusProjectiveSectionLine6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
abbrev BenchmarkField := IRSProfile.Field
abbrev Index := IRSProfile.Index
abbrev TriPoly := Polynomial (Polynomial (Polynomial BenchmarkField))
theorem natDegreeY_le_one_of_support6401
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 → j < 2) :
    Q.natDegree ≤ 1 := by
  have houter : Q.coeff Q.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ
  obtain ⟨x, hx⟩ := Polynomial.nonempty_support_iff.mpr houter
  have hlt := hcaps Q.natDegree x (Polynomial.mem_support_iff.mp hx)
  omega
theorem triEval_eq_linearY6401
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : F[X])
    (hdegree : Q.natDegree ≤ 1) :
    triEval Q z P =
      (Q.coeff 0).map (Polynomial.evalRingHom z) +
        (Q.coeff 1).map (Polynomial.evalRingHom z) * P := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegree]
  simp [triEval, specializeZ]
  ring
theorem shift_coeff_zero_zero6401
    {R : Type*} [CommRing R]
    (Q : Polynomial (Polynomial R)) (x y : R) :
    ((Polynomial.Bivariate.shift Q x y).coeff 0).coeff 0 =
      Polynomial.eval y (Q.map (Polynomial.evalRingHom x)) := by
  simp only [Polynomial.Bivariate.shift, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coe_compRingHom_apply, Polynomial.eval₂_at_zero,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, zero_add, Polynomial.eval_map]
  simpa only [Polynomial.eval_map] using
    (Polynomial.map_evalRingHom_eval x y Q).symm
theorem linearY_coordinate_identity6401
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (x : F) (y : F[X]) (hdegree : Q.natDegree ≤ 1)
    (hvan : ((Polynomial.Bivariate.shift Q (Polynomial.C x) y).coeff 0).coeff 0 = 0) :
    (Q.coeff 0).eval (Polynomial.C x) +
      (Q.coeff 1).eval (Polynomial.C x) * y = 0 := by
  rw [shift_coeff_zero_zero6401] at hvan
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegree] at hvan
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at hvan
  change (Q.coeff 1).eval (Polynomial.C x) * y +
    (Q.coeff 0).eval (Polynomial.C x) = 0 at hvan
  simpa only [add_comm] using hvan
theorem component_parameter_caps6401
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    (∀ x, ((Q.coeff 0).coeff x).natDegree ≤ 65537) ∧
      (∀ x, ((Q.coeff 1).coeff x).natDegree ≤ 65536) := by
  constructor <;> intro x
  · by_cases hx : (Q.coeff 0).coeff x = 0
    · simp [hx]
    · have h := (hcaps 0 x hx).2.2
      omega
  · by_cases hx : (Q.coeff 1).coeff x = 0
    · simp [hx]
    · have h := (hcaps 1 x hx).2.2
      omega
theorem component_X_caps6401
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    (Q.coeff 0).natDegree ≤ 196607 ∧
      (Q.coeff 1).natDegree ≤ 65536 := by
  constructor
  · by_cases hA : Q.coeff 0 = 0
    · simp [hA]
    · have hlead : (Q.coeff 0).coeff (Q.coeff 0).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hA
      have h := (hcaps 0 (Q.coeff 0).natDegree hlead).2.1
      omega
  · by_cases hB : Q.coeff 1 = 0
    · simp [hB]
    · have hlead : (Q.coeff 1).coeff (Q.coeff 1).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hB
      have h := (hcaps 1 (Q.coeff 1).natDegree hlead).2.1
      omega
def optionLinearYCap6401 : Option (Fin 131072) → Nat
  | none => 65537
  | some _ => 65536
theorem optionLinearYCap_sum6401 :
    ∑ c : Option (Fin 131072), optionLinearYCap6401 c = 8590000129 := by
  native_decide
theorem augmented_degree_caps6401
    {F : Type*} [Field F] (A B : F[X][X])
    (hA : A.natDegree ≤ 196607) (hB : B.natDegree ≤ 65536)
    (hAz : ∀ r, (A.coeff r).natDegree ≤ 65537)
    (hBz : ∀ r, (B.coeff r).natDegree ≤ 65536) :
    (∀ c : Option (Fin 131072),
      linearYAugmented A B 131072 c = 0 ∨
        (linearYAugmented A B 131072 c).natDegree < 196608) ∧
      (∀ r c,
        ((linearYAugmented A B 131072 c).coeff r).natDegree ≤
          optionLinearYCap6401 c) := by
  constructor
  · intro c
    cases c with
    | none => exact Or.inr (hA.trans_lt (by norm_num))
    | some j =>
        right
        exact Polynomial.natDegree_mul_le.trans_lt (by
          have hx : ((Polynomial.X : F[X][X]) ^ (j : Nat)).natDegree ≤
              (j : Nat) := by simp
          have hj := j.isLt
          omega)
  · intro r c
    cases c with
    | none => exact hAz r
    | some j =>
        dsimp [linearYAugmented, optionLinearYCap6401]
        rw [Polynomial.coeff_X_pow_mul']
        split_ifs with hjr
        · exact hBz (r - (j : Nat))
        · simp
theorem card_le_natDegree_of_eval_zero6401
    {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]
    (alpha : I ↪ K) (R : K[X]) (hR : R ≠ 0)
    (S : Finset I) (hroot : ∀ i ∈ S, R.eval (alpha i) = 0) :
    S.card ≤ R.natDegree := by
  let roots : Finset K := S.map alpha
  have hsubset : roots ⊆ R.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact Multiset.mem_toFinset.mpr
      (Polynomial.mem_roots hR |>.2 (hroot i hi))
  calc
    S.card = roots.card := by simp [roots]
    _ ≤ R.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ R.roots.card := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := Polynomial.card_roots' R
theorem mapped_coordinate_identity6401
    {F I : Type*} [Field F]
    (alpha : I → F) (u₀ u₁ : I → F)
    (A B : F[X][X])
    (hcoord : ∀ i,
      A.eval (Polynomial.C (alpha i)) +
        B.eval (Polynomial.C (alpha i)) *
          (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)) = 0) :
    ∀ i,
      ((A.map (algebraMap F[X] (RatFunc F))).eval
          (algebraMap F (RatFunc F) (alpha i))) +
        ((B.map (algebraMap F[X] (RatFunc F))).eval
          (algebraMap F (RatFunc F) (alpha i))) *
          (algebraMap F (RatFunc F) (u₀ i) +
            RatFunc.X * algebraMap F (RatFunc F) (u₁ i)) = 0 := by
  intro i
  let phi : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F)
  let eta : F →+* RatFunc F := algebraMap F (RatFunc F)
  have hC (a : F) : phi (Polynomial.C a) = eta a := by
    rfl
  have hX : phi Polynomial.X = RatFunc.X := by
    rfl
  have hA : phi (A.eval (Polynomial.C (alpha i))) =
      (A.map phi).eval (eta (alpha i)) := by
    rw [← hC]
    exact (Polynomial.eval_map_apply (p := A) phi _).symm
  have hB : phi (B.eval (Polynomial.C (alpha i))) =
      (B.map phi).eval (eta (alpha i)) := by
    rw [← hC]
    exact (Polynomial.eval_map_apply (p := B) phi _).symm
  have hy : phi (Polynomial.C (u₀ i) +
      Polynomial.X * Polynomial.C (u₁ i)) =
      eta (u₀ i) + RatFunc.X * eta (u₁ i) := by
    rw [map_add, map_mul, hC, hX, hC]
  have h := congrArg phi (hcoord i)
  rw [map_add, map_mul, map_zero, hA, hB, hy] at h
  exact h
theorem exists_affine_quotient6401
    (A B : BenchmarkField[X][X])
    (hB : B ≠ 0) (hBX : B.natDegree ≤ 65536)
    (u₀ u₁ : Index → BenchmarkField)
    (hcoord : ∀ i,
      A.eval (Polynomial.C (IRSProfile.domain i)) +
        B.eval (Polynomial.C (IRSProfile.domain i)) *
          (Polynomial.C (u₀ i) +
            Polynomial.X * Polynomial.C (u₁ i)) = 0)
    (R : (RatFunc BenchmarkField)[X])
    (hRdegree : R.natDegree < 131072)
    (hdiv : A.map (algebraMap BenchmarkField[X]
        (RatFunc BenchmarkField)) =
      R * B.map (algebraMap BenchmarkField[X]
        (RatFunc BenchmarkField))) :
    ∃ p₀ p₁ : BenchmarkField[X],
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      -R = p₀.map (algebraMap BenchmarkField (RatFunc BenchmarkField)) +
        Polynomial.C RatFunc.X *
          p₁.map (algebraMap BenchmarkField (RatFunc BenchmarkField)) := by
  classical
  let phi : BenchmarkField[X] →+* RatFunc BenchmarkField :=
    algebraMap BenchmarkField[X] (RatFunc BenchmarkField)
  let eta : BenchmarkField →+* RatFunc BenchmarkField :=
    algebraMap BenchmarkField (RatFunc BenchmarkField)
  let Abar : (RatFunc BenchmarkField)[X] := A.map phi
  let Bbar : (RatFunc BenchmarkField)[X] := B.map phi
  let alphaRF : Index ↪ RatFunc BenchmarkField := {
    toFun := fun i => eta (IRSProfile.domain i)
    inj' := eta.injective.comp IRSProfile.domain.injective
  }
  have hBbar : Bbar ≠ 0 := by
    simpa [Bbar] using (Polynomial.map_injective phi
      (RatFunc.algebraMap_injective BenchmarkField)).ne hB
  have hBbarDegree : Bbar.natDegree ≤ 65536 :=
    Polynomial.natDegree_map_le.trans hBX
  let bad : Finset Index := Finset.univ.filter fun i =>
    Bbar.eval (alphaRF i) = 0
  let good : Finset Index := Finset.univ.filter fun i =>
    Bbar.eval (alphaRF i) ≠ 0
  have hbad : bad.card ≤ 65536 := by
    have hroots : bad.card ≤ Bbar.natDegree :=
      card_le_natDegree_of_eval_zero6401 alphaRF Bbar hBbar bad (by
        intro i hi
        exact (Finset.mem_filter.mp hi).2)
    exact hroots.trans hBbarDegree
  have hpartition : bad.card + good.card = Fintype.card Index := by
    simpa [bad, good] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset Index))
        (fun i => Bbar.eval (alphaRF i) = 0))
  have hIndex : Fintype.card Index = 262144 := by
    norm_num [Index, IRSProfile.Index]
  have hgood : 131072 ≤ good.card := by
    rw [hIndex] at hpartition
    omega
  have hcoordRF := mapped_coordinate_identity6401 IRSProfile.domain u₀ u₁ A B hcoord
  have heval : ∀ i ∈ good,
      (-R).eval (eta (IRSProfile.domain i)) =
        eta (u₀ i) + RatFunc.X * eta (u₁ i) := by
    intro i hi
    have hBi : Bbar.eval (alphaRF i) ≠ 0 :=
      (Finset.mem_filter.mp hi).2
    have hc := hcoordRF i
    have hd := congrArg (Polynomial.eval (alphaRF i)) hdiv
    have hd' : Abar.eval (alphaRF i) =
        R.eval (alphaRF i) * Bbar.eval (alphaRF i) := by
      simpa [Abar, Bbar, phi, alphaRF] using hd
    have hc' : Abar.eval (alphaRF i) +
        Bbar.eval (alphaRF i) *
          (eta (u₀ i) + RatFunc.X * eta (u₁ i)) = 0 := by
      simpa [Abar, Bbar, phi, eta, alphaRF] using hc
    have hprod : Bbar.eval (alphaRF i) *
        (R.eval (alphaRF i) +
          (eta (u₀ i) + RatFunc.X * eta (u₁ i))) = 0 := by
      calc
        _ = R.eval (alphaRF i) * Bbar.eval (alphaRF i) +
            Bbar.eval (alphaRF i) *
              (eta (u₀ i) + RatFunc.X * eta (u₁ i)) := by ring
        _ = 0 := by rw [← hd']; exact hc'
    have hsum := (mul_eq_zero.mp hprod).resolve_left hBi
    have hneg : -R.eval (alphaRF i) =
        eta (u₀ i) + RatFunc.X * eta (u₁ i) :=
      neg_eq_iff_add_eq_zero.mpr hsum
    simpa [alphaRF, eta] using hneg
  have hnegDegree : (-R).natDegree ≤ 131071 := by
    rw [Polynomial.natDegree_neg]
    omega
  exact ratFuncPolynomial_eq_affine_of_many_evals
    (-R) 131071 good IRSProfile.domain u₀ u₁ hgood hnegDegree heval
theorem polynomial_identity_of_affine_quotient6401
    (A B : BenchmarkField[X][X])
    (R : (RatFunc BenchmarkField)[X])
    (p₀ p₁ : BenchmarkField[X])
    (hdiv : A.map (algebraMap BenchmarkField[X]
        (RatFunc BenchmarkField)) =
      R * B.map (algebraMap BenchmarkField[X]
        (RatFunc BenchmarkField)))
    (haffine : -R =
      p₀.map (algebraMap BenchmarkField (RatFunc BenchmarkField)) +
        Polynomial.C RatFunc.X *
          p₁.map (algebraMap BenchmarkField (RatFunc BenchmarkField))) :
    A + B *
      (p₀.map Polynomial.C + Polynomial.C Polynomial.X *
        p₁.map Polynomial.C) = 0 := by
  let phi : BenchmarkField[X] →+* RatFunc BenchmarkField :=
    algebraMap BenchmarkField[X] (RatFunc BenchmarkField)
  let eta : BenchmarkField →+* RatFunc BenchmarkField :=
    algebraMap BenchmarkField (RatFunc BenchmarkField)
  let L : BenchmarkField[X][X] :=
    p₀.map Polynomial.C + Polynomial.C Polynomial.X * p₁.map Polynomial.C
  have hC (a : BenchmarkField) : phi (Polynomial.C a) = eta a := by rfl
  have hX : phi Polynomial.X = RatFunc.X := by rfl
  have hpmap (p : BenchmarkField[X]) :
      (p.map Polynomial.C).map phi = p.map eta := by
    rw [Polynomial.map_map]
    apply Polynomial.ext
    intro n
    simp only [Polynomial.coeff_map]
    exact hC (p.coeff n)
  have hL : L.map phi =
      p₀.map eta + Polynomial.C RatFunc.X * p₁.map eta := by
    simp only [L, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, hpmap, hX]
  have hmapped : (A + B * L).map phi = 0 := by
    rw [Polynomial.map_add, Polynomial.map_mul, hdiv, hL]
    rw [← haffine]
    ring
  have hinj := Polynomial.map_injective phi
    (RatFunc.algebraMap_injective BenchmarkField)
  apply hinj
  simpa [L] using hmapped
theorem owner_eq_affine_of_polynomial_identity6401
    {F : Type*} [Field F]
    (A B : F[X][X]) (P p₀ p₁ : F[X]) (z : F)
    (howner : A.map (Polynomial.evalRingHom z) +
      B.map (Polynomial.evalRingHom z) * P = 0)
    (hidentity : A + B *
      (p₀.map Polynomial.C + Polynomial.C Polynomial.X *
        p₁.map Polynomial.C) = 0)
    (hBz : B.map (Polynomial.evalRingHom z) ≠ 0) :
    P = p₀ + Polynomial.C z * p₁ := by
  let ez : F[X] →+* F := Polynomial.evalRingHom z
  let L : F[X][X] := p₀.map Polynomial.C +
    Polynomial.C Polynomial.X * p₁.map Polynomial.C
  have hpmap (p : F[X]) : (p.map Polynomial.C).map ez = p := by
    apply Polynomial.ext
    intro n
    simp [ez, Polynomial.coeff_map]
  have hX : ez Polynomial.X = z := by simp [ez]
  have hL : L.map ez = p₀ + Polynomial.C z * p₁ := by
    rw [Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, hpmap, hpmap, hX]
  have hidentityL : A + B * L = 0 := by simpa [L] using hidentity
  have hi := congrArg (Polynomial.map ez) hidentityL
  have hiL : A.map ez + B.map ez * L.map ez = 0 := by
    simpa only [Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_zero] using hi
  have hi' : A.map ez + B.map ez *
      (p₀ + Polynomial.C z * p₁) = 0 := by
    rw [hL] at hiL
    exact hiL
  have hprod : B.map ez *
      (P - (p₀ + Polynomial.C z * p₁)) = 0 := by
    calc
      _ = (A.map ez + B.map ez * P) -
          (A.map ez + B.map ez *
            (p₀ + Polynomial.C z * p₁)) := by ring
      _ = 0 := by rw [howner, hi']; simp
  have := (mul_eq_zero.mp hprod).resolve_left hBz
  exact sub_eq_zero.mp this
set_option maxHeartbeats 100000 in
theorem lowSupportOwners_curve_or_cap_of_interpolant6401
    {received : Fin 2 → Index → BenchmarkField}
    {S : Finset BenchmarkField}
    {agreements : BenchmarkField → Finset Index}
    (J : J0BenchmarkInterpolant received S agreements)
    (hlow : ∀ z ∈ S, 196608 ≤ (agreements z).card)
    (Q : TriPoly) (hQ : Q ≠ 0)
    (hvan : ∀ i s t, s + t < 1 →
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (received 0 i) +
          Polynomial.X * Polynomial.C (received 1 i))).coeff t).coeff s = 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    PolynomialAffineCurveWitness6401 S J.P ∨
      S.card ≤ linearYMinorDegreeCap6401 := by
  classical
  let A : BenchmarkField[X][X] := Q.coeff 0
  let B : BenchmarkField[X][X] := Q.coeff 1
  let yZ : Index → BenchmarkField[X] := fun i =>
    Polynomial.C (received 0 i) +
      Polynomial.X * Polynomial.C (received 1 i)
  have hY : Q.natDegree ≤ 1 :=
    natDegreeY_le_one_of_support6401 Q hQ (fun j x hx => (hcaps j x hx).1)
  have hcomponentZ := component_parameter_caps6401 Q hcaps
  have hcomponentX := component_X_caps6401 Q hcaps
  have htri : ∀ z ∈ S, triEval Q z (J.P z) = 0 := by
    intro z hz
    apply triEval_eq_zero_of_many_shift_vanishing_of_weighted_X_cap
      Q z (J.P z) IRSProfile.domain (agreements z) yZ
      1 131071 196607
    · intro i hi s t h hst
      have hv := hvan i s t hst
      rw [hv]
      simp
    · intro i hi
      rw [J.agrees z hz i hi]
      simp only [yZ, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X]
    · exact J.root_degree z hz
    · intro j x hx
      have h := (hcaps j x hx).2.1
      omega
    · have h := hlow z hz
      omega
  have hzero : ∀ z ∈ S,
      A.map (Polynomial.evalRingHom z) +
        B.map (Polynomial.evalRingHom z) * J.P z = 0 := by
    intro z hz
    rw [← triEval_eq_linearY6401 Q z (J.P z) hY]
    exact htri z hz
  have hcoord : ∀ i,
      A.eval (Polynomial.C (IRSProfile.domain i)) +
        B.eval (Polynomial.C (IRSProfile.domain i)) * yZ i = 0 := by
    intro i
    apply linearY_coordinate_identity6401 Q
      (IRSProfile.domain i) (yZ i) hY
    exact hvan i 0 0 (by norm_num)
  by_cases hcurve : PolynomialAffineCurveWitness6401 S J.P
  · exact Or.inl hcurve
  right
  by_cases hB : B = 0
  · have hQform := Polynomial.eq_X_add_C_of_natDegree_le_one hY
    have hA : A ≠ 0 := by
      intro hAzero
      apply hQ
      rw [hQform]
      simp [A, B, hAzero, hB]
    obtain ⟨x, hx⟩ := Polynomial.nonempty_support_iff.mpr hA
    have hAx : A.coeff x ≠ 0 := Polynomial.mem_support_iff.mp hx
    have hroots : ∀ z ∈ S, Polynomial.eval z (A.coeff x) = 0 := by
      intro z hz
      have hz0 := hzero z hz
      rw [hB] at hz0
      simp only [Polynomial.map_zero, zero_mul, add_zero] at hz0
      have hc := congrArg (fun P : BenchmarkField[X] => P.coeff x) hz0
      simpa [A, Polynomial.coeff_map] using hc
    have hcap := card_le_natDegree_of_eval_zero6401
      (Function.Embedding.refl BenchmarkField) (A.coeff x) hAx S hroots
    calc
      S.card ≤ 65537 := hcap.trans (hcomponentZ.1 x)
      _ ≤ linearYMinorDegreeCap6401 := by
        rw [lowSupport_ledger_exact6401.2.2]
        norm_num
  · let phi : BenchmarkField[X] →+* RatFunc BenchmarkField :=
      algebraMap BenchmarkField[X] (RatFunc BenchmarkField)
    let Abar : (RatFunc BenchmarkField)[X] := A.map phi
    let Bbar : (RatFunc BenchmarkField)[X] := B.map phi
    have hBbar : Bbar ≠ 0 := by
      simpa [Bbar] using (Polynomial.map_injective phi
        (RatFunc.algebraMap_injective BenchmarkField)).ne hB
    have hdegrees := augmented_degree_caps6401 A B
      hcomponentX.1 hcomponentX.2 hcomponentZ.1 hcomponentZ.2
    by_cases hind : LinearIndependent (RatFunc BenchmarkField)
        (fun c : Option (Fin 131072) =>
          (linearYAugmented A B 131072 c).map phi)
    · have hcap := ownerFamily_card_le_of_linearYAugmentedIndependent
        A B 131072 196608 optionLinearYCap6401
        hdegrees.1 hdegrees.2 hind S J.P
        (fun z hz => by
          have := J.root_degree z hz
          omega)
        hzero
      calc
        S.card ≤ ∑ c : Option (Fin 131072), optionLinearYCap6401 c := hcap
        _ = linearYMinorDegreeCap6401 := by
          rw [optionLinearYCap_sum6401,
            lowSupport_ledger_exact6401.2.2]
    · have hdep : ¬ LinearIndependent (RatFunc BenchmarkField)
          (fun o : Option (Fin 131072) =>
            Option.casesOn' o Abar
              (fun j => (Polynomial.X : (RatFunc BenchmarkField)[X]) ^
                (j : Nat) * Bbar)) := by
        have hfamily :
            (fun c : Option (Fin 131072) =>
              (linearYAugmented A B 131072 c).map phi) =
            (fun o : Option (Fin 131072) =>
              Option.casesOn' o Abar
                (fun j => (Polynomial.X : (RatFunc BenchmarkField)[X]) ^
                  (j : Nat) * Bbar)) := by
          funext c
          cases c with
          | none => rfl
          | some j =>
              simp only [linearYAugmented, Polynomial.map_mul,
                Polynomial.map_pow, Polynomial.map_X]
              rfl
        intro hli
        apply hind
        rw [hfamily]
        exact hli
      obtain ⟨R, hRdegree, hdiv⟩ :=
        exists_bounded_quotient_of_augmented_dependent
          Abar Bbar 131072 hBbar (by norm_num) hdep
      obtain ⟨p₀, p₁, hp₀, hp₁, haffine⟩ :=
        exists_affine_quotient6401 A B hB hcomponentX.2
          (received 0) (received 1) (by simpa [yZ] using hcoord)
          R hRdegree hdiv
      have hidentity := polynomial_identity_of_affine_quotient6401
        A B R p₀ p₁ hdiv haffine
      obtain ⟨x, hx⟩ := Polynomial.nonempty_support_iff.mpr hB
      have hBx : B.coeff x ≠ 0 := Polynomial.mem_support_iff.mp hx
      let bad : Finset BenchmarkField := S.filter fun z =>
        Polynomial.eval z (B.coeff x) = 0
      let good : Finset BenchmarkField := S.filter fun z =>
        Polynomial.eval z (B.coeff x) ≠ 0
      have hbad : bad.card ≤ 65536 := by
        have hr := card_le_natDegree_of_eval_zero6401
          (Function.Embedding.refl BenchmarkField) (B.coeff x) hBx bad (by
            intro z hz
            exact (Finset.mem_filter.mp hz).2)
        exact hr.trans (hcomponentZ.2 x)
      have hgoodSub : good ⊆ S := Finset.filter_subset _ _
      have halign : ∀ z ∈ good,
          J.P z = p₀ + Polynomial.C z * p₁ := by
        intro z hz
        have hzx : Polynomial.eval z (B.coeff x) ≠ 0 :=
          (Finset.mem_filter.mp hz).2
        have hBz : B.map (Polynomial.evalRingHom z) ≠ 0 := by
          intro hzB
          have hc := congrArg (fun P : BenchmarkField[X] => P.coeff x) hzB
          exact hzx (by simpa [Polynomial.coeff_map] using hc)
        exact owner_eq_affine_of_polynomial_identity6401
          A B (J.P z) p₀ p₁ z (hzero z (hgoodSub hz)) hidentity hBz
      have hgoodCard : good.card ≤ 1182 :=
        affineFamily_card_le_1182_of_no_curveWitness6401
          S good J.P p₀ p₁ hcurve hp₀ hp₁ hgoodSub halign
      have hpartition : bad.card + good.card = S.card := by
        simpa [bad, good] using
          (Finset.card_filter_add_card_filter_not
            (s := S) (fun z => Polynomial.eval z (B.coeff x) = 0))
      rw [lowSupport_ledger_exact6401.2.2]
      omega
theorem J0BenchmarkInterpolant.lowSupportOwners_curve_or_cap6401
    {received : Fin 2 → Index → BenchmarkField}
    {S : Finset BenchmarkField}
    {agreements : BenchmarkField → Finset Index}
    (J : J0BenchmarkInterpolant received S agreements)
    (hlow : ∀ z ∈ S, 196608 ≤ (agreements z).card) :
    PolynomialAffineCurveWitness6401 S J.P ∨
      S.card ≤ linearYMinorDegreeCap6401 := by
  obtain ⟨Q, hQ, hvan, hcaps⟩ :=
    BCHKSConcreteGSLinearY6401.exists_interpolant
      IRSProfile.domain (received 0) (received 1)
  exact lowSupportOwners_curve_or_cap_of_interpolant6401
    J hlow Q hQ hvan hcaps
def exactOwnerPoolAfterLinearY6401 : Nat :=
  unsplitWeakSeedOwnerPool6401 - linearYMinorDegreeCap6401
def exactDenseLineFloorAfterLinearY6401 : Nat := 128403983
theorem exactPostLinearY_constants6401 :
    exactOwnerPoolAfterLinearY6401 = 273591190752810939 ∧
      exactDenseLineFloorAfterLinearY6401 = 128403983 := by
  native_decide
theorem exactPostLinearY_projectivePlane_dense6401 :
    projectivePlaneLineCount6401 *
        (exactDenseLineFloorAfterLinearY6401 - 1) <
      exactOwnerPoolAfterLinearY6401 *
        (BCHKSTwoFrobeniusModuleAudit6401.q6401 + 1) := by
  native_decide
theorem exactPostLinearY_projectiveFq2Subline_dense6401 :
    projectiveFqSublineCount6401 *
        (exactDenseLineFloorAfterLinearY6401 - 1) <
      exactOwnerPoolAfterLinearY6401 *
        projectiveFqSublineReplication6401 := by
  native_decide
theorem exactPostLinearY_sevenFibre_margin6401 :
    cubicOwnerFibreMultiplicity6401 * quadraticPencilFibreCap6401 <
        exactDenseLineFloorAfterLinearY6401 ∧
      exactDenseLineFloorAfterLinearY6401 -
          cubicOwnerFibreMultiplicity6401 * quadraticPencilFibreCap6401 =
        5241762 := by
  native_decide
end BCHKSJ0LinearYLowSupport6401
end ProximityPrize.SubmissionLower
