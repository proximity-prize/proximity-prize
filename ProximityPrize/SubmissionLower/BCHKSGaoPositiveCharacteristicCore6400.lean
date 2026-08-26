import ProximityPrize.SubmissionLower.BCHKSGaoSpecializationCore6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSGaoPositiveCharacteristicCore6400
open Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section DerivativeZero
variable {R : Type*} [CommRing R] [NoZeroDivisors R]
variable {p : ℕ} [CharP R p]
theorem char_dvd_of_mem_support_of_derivative_eq_zero
    (hp : p ≠ 0) {f : R[X]} (hderiv : f.derivative = 0)
    {i : ℕ} (hi : i ∈ f.support) :
    p ∣ i := by
  have hexpand : expand R p (contract p f) = f :=
    expand_contract p hderiv hp
  by_contra hpid
  have hcoeff : (expand R p (contract p f)).coeff i = 0 := by
    rw [coeff_expand hp.bot_lt, if_neg hpid]
  rw [hexpand] at hcoeff
  exact (mem_support_iff.mp hi) hcoeff
theorem eq_zero_or_char_le_natDegree_of_derivative_eq_zero
    (hp : p ≠ 0) (f : R[X]) (hderiv : f.derivative = 0) :
    f.natDegree = 0 ∨ p ≤ f.natDegree := by
  by_cases hdegree : f.natDegree = 0
  · exact Or.inl hdegree
  · right
    have hf : f ≠ 0 := fun hf ↦ hdegree (hf.symm ▸ natDegree_zero)
    have hmem : f.natDegree ∈ f.support :=
      natDegree_mem_support_of_nonzero hf
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hdegree)
      (char_dvd_of_mem_support_of_derivative_eq_zero hp hderiv hmem)
theorem eq_C_coeff_zero_of_derivative_eq_zero_of_natDegree_lt_char
    (hp : p ≠ 0) (f : R[X]) (hderiv : f.derivative = 0)
    (hdegree : f.natDegree < p) :
    f = C (f.coeff 0) := by
  apply eq_C_of_natDegree_eq_zero
  rcases eq_zero_or_char_le_natDegree_of_derivative_eq_zero hp f hderiv with h | h
  · exact h
  · exact (Nat.not_le_of_lt hdegree h).elim
theorem exists_eq_expand_of_derivative_eq_zero
    (hp : p ≠ 0) (f : R[X]) (hderiv : f.derivative = 0) :
    ∃ u : R[X], f = expand R p u := by
  exact ⟨contract p f, (expand_contract p hderiv hp).symm⟩
end DerivativeZero
section DifferentialMinpoly
variable {F L : Type*} [Field F] [Field L]
variable [Differential F] [Differential L]
variable [Algebra F L] [DifferentialAlgebra F L]
theorem mapCoeffs_minpoly_eq_zero_of_deriv_eq_zero
    (a : L) (ha : IsIntegral F a) (haderiv : Differential.deriv a = 0) :
    Differential.mapCoeffs (minpoly F a) = 0 := by
  let T : F[X] := minpoly F a
  change Differential.mapCoeffs T = 0
  have heval : aeval a (Differential.mapCoeffs T) = 0 := by
    have hchain := Differential.deriv_aeval_eq a T
    simpa [T, minpoly.aeval, haderiv] using hchain.symm
  have hdvd : T ∣ Differential.mapCoeffs T := by
    exact minpoly.dvd F a heval
  have hdegree : (Differential.mapCoeffs T).natDegree ≤ T.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [Differential.coeff_mapCoeffs,
      Polynomial.coeff_eq_zero_of_natDegree_lt hi]
    simp
  have hlead :
      (Differential.mapCoeffs T).coeff T.natDegree = 0 := by
    rw [Differential.coeff_mapCoeffs, Polynomial.coeff_natDegree]
    have hmonic : T.Monic := minpoly.monic ha
    rw [hmonic.leadingCoeff]
    simp
  have hpred :
      (Differential.mapCoeffs T).natDegree ≤ T.natDegree - 1 :=
    Polynomial.natDegree_le_pred hdegree hlead
  have hpos : 0 < T.natDegree := minpoly.natDegree_pos ha
  exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (by omega)
theorem deriv_coeff_minpoly_eq_zero_of_deriv_eq_zero
    (a : L) (ha : IsIntegral F a) (haderiv : Differential.deriv a = 0)
    (i : ℕ) :
    Differential.deriv ((minpoly F a).coeff i) = 0 := by
  have h := congrArg (fun q : F[X] ↦ q.coeff i)
    (mapCoeffs_minpoly_eq_zero_of_deriv_eq_zero a ha haderiv)
  simpa using h
end DifferentialMinpoly
section RatFuncDifferential
variable {K : Type*} [Field K]
noncomputable def quotientDerivValue (p q : K[X]) : RatFunc K :=
  ((algebraMap K[X] (RatFunc K) p.derivative) *
      (algebraMap K[X] (RatFunc K) q) -
    (algebraMap K[X] (RatFunc K) p) *
      (algebraMap K[X] (RatFunc K) q.derivative)) /
    (algebraMap K[X] (RatFunc K) q) ^ 2
theorem quotientDerivValue_scale
    {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0) :
    quotientDerivValue (a * p) (a * q) = quotientDerivValue p q := by
  have hqa : algebraMap K[X] (RatFunc K) q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq
  have haa : algebraMap K[X] (RatFunc K) a ≠ 0 :=
    RatFunc.algebraMap_ne_zero ha
  simp only [quotientDerivValue, derivative_mul, map_add, map_mul]
  field_simp
  ring
noncomputable def ratFuncDerivFun (x : RatFunc K) : RatFunc K :=
  x.liftOn' quotientDerivValue fun hq ha ↦ quotientDerivValue_scale hq ha
theorem ratFuncDerivFun_div (p q : K[X]) :
    ratFuncDerivFun
      (algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) q) = quotientDerivValue p q := by
  apply RatFunc.liftOn'_div
  intro p
  simp [quotientDerivValue]
theorem ratFuncDerivFun_add (x y : RatFunc K) :
    ratFuncDerivFun (x + y) = ratFuncDerivFun x + ratFuncDerivFun y := by
  induction x using RatFunc.induction_on with
  | _ p q hq =>
    induction y using RatFunc.induction_on with
    | _ r s hs =>
      have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 :=
        RatFunc.algebraMap_ne_zero hq
      have hs' : algebraMap K[X] (RatFunc K) s ≠ 0 :=
        RatFunc.algebraMap_ne_zero hs
      have hadd :
          algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q +
              algebraMap K[X] (RatFunc K) r / algebraMap K[X] (RatFunc K) s =
            algebraMap K[X] (RatFunc K) (p * s + q * r) /
              algebraMap K[X] (RatFunc K) (q * s) := by
        rw [div_add_div _ _ hq' hs']
        simp
      rw [hadd]
      rw [ratFuncDerivFun_div, ratFuncDerivFun_div, ratFuncDerivFun_div]
      simp only [quotientDerivValue, derivative_mul, map_add, map_mul]
      field_simp
      ring
theorem ratFuncDerivFun_smul (c : K) (x : RatFunc K) :
    ratFuncDerivFun (c • x) = c • ratFuncDerivFun x := by
  induction x using RatFunc.induction_on with
  | _ p q hq =>
    rw [← RatFunc.div_smul, ratFuncDerivFun_div, ratFuncDerivFun_div]
    simp only [quotientDerivValue, map_smul]
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    simp only [map_mul]
    have hc :
        algebraMap K[X] (RatFunc K) (algebraMap K K[X] c) =
          algebraMap K (RatFunc K) c := by
      symm
      rw [RatFunc.algebraMap_apply]
      simp
    rw [hc]
    ring
theorem ratFuncDerivFun_mul (x y : RatFunc K) :
    ratFuncDerivFun (x * y) =
      x * ratFuncDerivFun y + y * ratFuncDerivFun x := by
  induction x using RatFunc.induction_on with
  | _ p q hq =>
    induction y using RatFunc.induction_on with
    | _ r s hs =>
      have hmul :
          (algebraMap K[X] (RatFunc K) p /
              algebraMap K[X] (RatFunc K) q) *
              (algebraMap K[X] (RatFunc K) r /
                algebraMap K[X] (RatFunc K) s) =
            algebraMap K[X] (RatFunc K) (p * r) /
              algebraMap K[X] (RatFunc K) (q * s) := by
        rw [div_mul_div_comm]
        simp
      rw [hmul, ratFuncDerivFun_div, ratFuncDerivFun_div,
        ratFuncDerivFun_div]
      simp only [quotientDerivValue, derivative_mul, map_add, map_mul]
      have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 :=
        RatFunc.algebraMap_ne_zero hq
      have hs' : algebraMap K[X] (RatFunc K) s ≠ 0 :=
        RatFunc.algebraMap_ne_zero hs
      field_simp
      ring
noncomputable def ratFuncDerivLinearMap :
    RatFunc K →ₗ[K] RatFunc K where
  toFun := ratFuncDerivFun
  map_add' := ratFuncDerivFun_add
  map_smul' := ratFuncDerivFun_smul
noncomputable def ratFuncDerivation :
    Derivation K (RatFunc K) (RatFunc K) :=
  Derivation.mk' ratFuncDerivLinearMap ratFuncDerivFun_mul
theorem ratFuncDerivation_div (p q : K[X]) :
    ratFuncDerivation
      (algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) q) = quotientDerivValue p q := by
  exact ratFuncDerivFun_div p q
theorem ratFuncDerivation_algebraMap_polynomial (p : K[X]) :
    ratFuncDerivation (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  calc
    ratFuncDerivation (algebraMap K[X] (RatFunc K) p) =
        ratFuncDerivation
          (algebraMap K[X] (RatFunc K) p /
            algebraMap K[X] (RatFunc K) (1 : K[X])) := by simp
    _ = quotientDerivValue p 1 := ratFuncDerivation_div p 1
    _ = algebraMap K[X] (RatFunc K) p.derivative := by
      simp [quotientDerivValue]
noncomputable def ratFuncDerivAddHom : RatFunc K →+ RatFunc K where
  toFun := ratFuncDerivFun
  map_zero' := by
    simpa using ratFuncDerivFun_add (0 : RatFunc K) 0
  map_add' := ratFuncDerivFun_add
@[reducible]
noncomputable def differentialRatFunc : Differential (RatFunc K) where
  deriv := by
    letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra (RatFunc K)
    exact
      { toLinearMap :=
        { toFun := ratFuncDerivFun
          map_add' := ratFuncDerivFun_add
          map_smul' := by
            intro n x
            simp only [Algebra.smul_def, RingHom.id_apply]
            rw [algebraMap_int_eq]
            simp only [Int.coe_castRingHom]
            have h := (ratFuncDerivAddHom (K := K)).map_zsmul n x
            change ratFuncDerivFun (n • x) =
              n • ratFuncDerivFun x at h
            simpa only [zsmul_eq_mul] using h }
        map_one_eq_zero' := by
          have h := ratFuncDerivFun_div (K := K) (1 : K[X]) 1
          simpa [quotientDerivValue] using h
        leibniz' := ratFuncDerivFun_mul }
theorem differentialRatFunc_deriv_algebraMap_polynomial (p : K[X]) :
    letI := differentialRatFunc (K := K)
    Differential.deriv (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  exact ratFuncDerivation_algebraMap_polynomial p
theorem differentialRatFunc_deriv_div (p q : K[X]) :
    letI := differentialRatFunc (K := K)
    Differential.deriv
      (algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) q) = quotientDerivValue p q := by
  exact ratFuncDerivFun_div p q
end RatFuncDifferential
section SeparableDifferentialExtension
variable {F : Type*} [Field F] [Differential F]
@[reducible]
noncomputable def differentialAdjoinRootSeparable
    (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic]
    (hsep : p.Separable) : Differential (AdjoinRoot p) where
  deriv := Derivation.liftOfSurjective
    (f := (AdjoinRoot.mk p).toIntAlgHom) AdjoinRoot.mk_surjective
    (d := Differential.implicitDeriv <| AdjoinRoot.modByMonicHom Fact.out <|
      - (aeval (AdjoinRoot.root p) (Differential.mapCoeffs p)) /
        (aeval (AdjoinRoot.root p) (derivative p))) (by
      rintro x hx
      simp_all only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero]
      obtain ⟨q, rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold Differential.implicitDeriv
      simp only [AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul,
        Pi.add_apply, Pi.smul_apply, Derivation.restrictScalars_apply,
        derivative'_apply, smul_eq_mul, map_add, map_mul,
        AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀, add_neg_cancel]
      have hne := hsep.aeval_derivative_ne_zero (by
          rw [AdjoinRoot.aeval_eq]
          exact AdjoinRoot.mk_eq_zero.mpr dvd_rfl)
      rw [AdjoinRoot.aeval_eq] at hne
      exact hne)
theorem differentialAlgebraAdjoinRootSeparable
    (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic]
    (hsep : p.Separable) :
    letI := differentialAdjoinRootSeparable p hsep
    DifferentialAlgebra F (AdjoinRoot p) := by
  letI := differentialAdjoinRootSeparable p hsep
  refine ⟨?_⟩
  intro a
  change (Derivation.liftOfSurjective _ _)
      ((AdjoinRoot.mk p).toIntAlgHom (C a)) = _
  rw [Derivation.liftOfSurjective_apply, Differential.implicitDeriv_C]
  rfl
@[reducible]
noncomputable def differentialFiniteSeparable
    (F K : Type*) [Field F] [Field K] [Differential F] [Algebra F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K] : Differential K :=
  let k := (Field.exists_primitive_element F K).choose
  have h : IntermediateField.adjoin F {k} = ⊤ :=
    (Field.exists_primitive_element F K).choose_spec
  have hk : IsIntegral F k := Algebra.IsIntegral.isIntegral k
  have hpsep : (minpoly F k).Separable :=
    Algebra.IsSeparable.isSeparable F k
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic hk⟩
  have : Fact (Irreducible (minpoly F k)) := ⟨minpoly.irreducible hk⟩
  letI : Differential (AdjoinRoot (minpoly F k)) :=
    differentialAdjoinRootSeparable (minpoly F k) hpsep
  Differential.equiv (IntermediateField.adjoinRootEquivAdjoin F hk
    |>.trans (IntermediateField.equivOfEq h)
    |>.trans IntermediateField.topEquiv).symm.toRingEquiv
theorem differentialAlgebraFiniteSeparable
    (F K : Type*) [Field F] [Field K] [Differential F] [Algebra F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K] :
    letI := differentialFiniteSeparable F K
    DifferentialAlgebra F K := by
  let k := (Field.exists_primitive_element F K).choose
  haveI h : IntermediateField.adjoin F {k} = ⊤ :=
    (Field.exists_primitive_element F K).choose_spec
  have hk : IsIntegral F k := Algebra.IsIntegral.isIntegral k
  have hpsep : (minpoly F k).Separable :=
    Algebra.IsSeparable.isSeparable F k
  haveI : Fact (minpoly F k).Monic := ⟨minpoly.monic hk⟩
  haveI : Fact (Irreducible (minpoly F k)) := ⟨minpoly.irreducible hk⟩
  letI : Differential (AdjoinRoot (minpoly F k)) :=
    differentialAdjoinRootSeparable (minpoly F k) hpsep
  letI : DifferentialAlgebra F (AdjoinRoot (minpoly F k)) :=
    differentialAlgebraAdjoinRootSeparable (minpoly F k) hpsep
  apply DifferentialAlgebra.equiv
end SeparableDifferentialExtension
section RatFuncSeparableExtension
variable {K L : Type*} [Field K] [Field L]
variable [Algebra (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
variable [Algebra.IsSeparable (RatFunc K) L]
theorem deriv_coeff_minpoly_ratFunc_eq_zero
    (a : L) (ha : IsIntegral (RatFunc K) a) (i : ℕ) :
    letI : Differential (RatFunc K) := differentialRatFunc
    letI : Differential L := differentialFiniteSeparable (RatFunc K) L
    Differential.deriv a = 0 →
      Differential.deriv ((minpoly (RatFunc K) a).coeff i) = 0 := by
  letI : Differential (RatFunc K) := differentialRatFunc
  letI : Differential L := differentialFiniteSeparable (RatFunc K) L
  letI : DifferentialAlgebra (RatFunc K) L :=
    differentialAlgebraFiniteSeparable (RatFunc K) L
  intro haderiv
  exact deriv_coeff_minpoly_eq_zero_of_deriv_eq_zero a ha haderiv i
theorem coeff_mapCoeffs_map_ratFunc
    (f : Polynomial (Polynomial K)) (i : ℕ) :
    letI : Differential (RatFunc K) := differentialRatFunc
    (Differential.mapCoeffs
      (f.map (algebraMap K[X] (RatFunc K)))).coeff i =
        algebraMap K[X] (RatFunc K) (f.coeff i).derivative := by
  letI : Differential (RatFunc K) := differentialRatFunc
  rw [Differential.coeff_mapCoeffs, coeff_map,
    differentialRatFunc_deriv_algebraMap_polynomial]
theorem deriv_aeval_bivariate_eq
    (f : Polynomial (Polynomial K)) (beta : L) :
    letI : Differential (RatFunc K) := differentialRatFunc
    letI : Differential L := differentialFiniteSeparable (RatFunc K) L
    Differential.deriv
        (aeval beta (f.map (algebraMap K[X] (RatFunc K)))) =
      aeval beta
          (Differential.mapCoeffs
            (f.map (algebraMap K[X] (RatFunc K)))) +
        aeval beta
            (f.derivative.map (algebraMap K[X] (RatFunc K))) *
          Differential.deriv beta := by
  letI : Differential (RatFunc K) := differentialRatFunc
  letI : Differential L := differentialFiniteSeparable (RatFunc K) L
  letI : DifferentialAlgebra (RatFunc K) L :=
    differentialAlgebraFiniteSeparable (RatFunc K) L
  simpa only [Polynomial.derivative_map] using
    Differential.deriv_aeval_eq beta
      (f.map (algebraMap K[X] (RatFunc K)))
theorem deriv_eq_neg_div_of_aeval_eq_zero
    (f : Polynomial (Polynomial K)) (beta : L)
    (hroot : aeval beta
      (f.map (algebraMap K[X] (RatFunc K))) = 0)
    (hfx : aeval beta
      (f.derivative.map (algebraMap K[X] (RatFunc K))) ≠ 0) :
    letI : Differential (RatFunc K) := differentialRatFunc
    letI : Differential L := differentialFiniteSeparable (RatFunc K) L
    Differential.deriv beta =
      -aeval beta
          (Differential.mapCoeffs
            (f.map (algebraMap K[X] (RatFunc K)))) /
        aeval beta
          (f.derivative.map (algebraMap K[X] (RatFunc K))) := by
  letI : Differential (RatFunc K) := differentialRatFunc
  letI : Differential L := differentialFiniteSeparable (RatFunc K) L
  letI : DifferentialAlgebra (RatFunc K) L :=
    differentialAlgebraFiniteSeparable (RatFunc K) L
  have hchain := deriv_aeval_bivariate_eq f beta
  rw [hroot, map_zero] at hchain
  rw [eq_div_iff hfx]
  linear_combination -hchain
end RatFuncSeparableExtension
section DifferentialResidue
theorem derivative_mapCoeffs_eq_mapCoeffs_derivative
    {F : Type*} [Field F] [Differential F] (f : F[X]) :
    (Differential.mapCoeffs f).derivative =
      Differential.mapCoeffs f.derivative := by
  ext i
  simp [Differential.coeff_mapCoeffs, Polynomial.coeff_derivative,
    mul_comm]
theorem deriv_residue_eq_zero_of_pde
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E]
    (f g h : F[X]) (beta : E)
    (hroot : aeval beta f = 0)
    (hfx : aeval beta f.derivative ≠ 0)
    (hpde :
      f * (Differential.mapCoeffs g - h.derivative) +
          h * f.derivative - g * Differential.mapCoeffs f = 0) :
    Differential.deriv
      (aeval beta g / aeval beta f.derivative) = 0 := by
  let ev : F[X] →+* E := (aeval beta).toRingHom
  let Fy : E := ev (Differential.mapCoeffs f)
  let Fx : E := ev f.derivative
  let Fxy : E := ev (Differential.mapCoeffs f.derivative)
  let Fxx : E := ev f.derivative.derivative
  let G : E := ev g
  let Gy : E := ev (Differential.mapCoeffs g)
  let Gx : E := ev g.derivative
  let H : E := ev h
  let B : E := Differential.deriv beta
  have hFx : Fx ≠ 0 := by simpa [Fx, ev] using hfx
  have hchainf := Differential.deriv_aeval_eq beta f
  have hA : Fy + Fx * B = 0 := by
    rw [hroot, map_zero] at hchainf
    simpa [Fy, Fx, B, ev] using hchainf.symm
  have hpde0 := congrArg ev hpde
  have hP0 : H * Fx - G * Fy = 0 := by
    simpa [H, Fx, G, Fy, ev, hroot] using hpde0
  have hpde' := congrArg Polynomial.derivative hpde
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_zero,
    derivative_mapCoeffs_eq_mapCoeffs_derivative] at hpde'
  have hpde1 := congrArg ev hpde'
  have hP1 : Fx * Gy + H * Fxx - Gx * Fy - G * Fxy = 0 := by
    dsimp only [ev] at hpde1
    simp [hroot] at hpde1
    dsimp [Fx, Gy, H, Fxx, Gx, Fy, G, Fxy, ev]
    linear_combination hpde1
  have hFy : Fy = -Fx * B := by
    linear_combination hA
  have hH : H = -G * B := by
    apply mul_right_cancel₀ hFx
    linear_combination hP0 + G * hA
  have hchaing := Differential.deriv_aeval_eq beta g
  have hchainfx := Differential.deriv_aeval_eq beta f.derivative
  have hDg : Differential.deriv (ev g) = Gy + Gx * B := by
    simpa [Gy, Gx, B, ev] using hchaing
  have hDfx : Differential.deriv (ev f.derivative) = Fxy + Fxx * B := by
    simpa [Fxy, Fxx, B, ev] using hchainfx
  rw [(Differential.deriv : Derivation ℤ E E).leibniz_div]
  simp only [smul_eq_mul]
  apply mul_eq_zero.mpr
  right
  change Fx * Differential.deriv (ev g) -
    G * Differential.deriv (ev f.derivative) = 0
  rw [hDg, hDfx]
  rw [hFy, hH] at hP1
  linear_combination hP1
end DifferentialResidue
section PrimitiveCoefficientDescent
variable {K : Type*} [Field K]
theorem polynomial_relation_of_ratFunc_deriv_div_eq_zero
    (a b : K[X]) (hb : b ≠ 0) :
    letI : Differential (RatFunc K) := differentialRatFunc
    Differential.deriv
        (algebraMap K[X] (RatFunc K) a /
          algebraMap K[X] (RatFunc K) b) = 0 →
      b * a.derivative = a * b.derivative := by
  letI : Differential (RatFunc K) := differentialRatFunc
  intro hderiv
  rw [differentialRatFunc_deriv_div] at hderiv
  have hbmap : algebraMap K[X] (RatFunc K) b ≠ 0 :=
    RatFunc.algebraMap_ne_zero hb
  have hnum :
      algebraMap K[X] (RatFunc K) a.derivative *
          algebraMap K[X] (RatFunc K) b -
        algebraMap K[X] (RatFunc K) a *
          algebraMap K[X] (RatFunc K) b.derivative = 0 := by
    apply (div_eq_zero_iff).mp hderiv |>.resolve_right
    exact pow_ne_zero 2 hbmap
  have hpoly : a.derivative * b - a * b.derivative = 0 := by
    apply RatFunc.algebraMap_injective (K := K)
    simpa only [map_sub, map_mul, map_zero] using hnum
  rw [sub_eq_zero] at hpoly
  simpa only [mul_comm b] using hpoly
theorem derivatives_eq_zero_of_isPrimitive_of_derivative_rel
    (T : Polynomial (Polynomial K)) (hprimitive : T.IsPrimitive)
    (hrel : ∀ i,
      T.leadingCoeff * (T.coeff i).derivative =
        T.coeff i * T.leadingCoeff.derivative) :
    ∀ i, (T.coeff i).derivative = 0 := by
  classical
  have hTzero : T ≠ 0 := hprimitive.ne_zero
  have hvzero : T.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hTzero
  have hCdvd :
      C T.leadingCoeff ∣ C T.leadingCoeff.derivative * T := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_C_mul]
    exact ⟨(T.coeff i).derivative, by
      simpa only [mul_comm] using (hrel i).symm⟩
  have hvdvdContent :
      T.leadingCoeff ∣ (C T.leadingCoeff.derivative * T).content :=
    Polynomial.dvd_content_iff_C_dvd.mpr hCdvd
  have hvdvd : T.leadingCoeff ∣ T.leadingCoeff.derivative := by
    rw [Polynomial.content_C_mul, hprimitive.content_eq_one, mul_one]
      at hvdvdContent
    exact dvd_normalize_iff.mp hvdvdContent
  have hvderiv : T.leadingCoeff.derivative = 0 := by
    by_cases hdegree : T.leadingCoeff.natDegree = 0
    · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegree
      rw [← hc]
      simp
    · exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hvdvd
        (Polynomial.natDegree_derivative_lt hdegree)
  intro i
  have hi := hrel i
  rw [hvderiv, mul_zero] at hi
  exact (mul_eq_zero.mp hi).resolve_left hvzero
theorem derivatives_eq_zero_of_isPrimitive_of_ratios_deriv_eq_zero
    (T : Polynomial (Polynomial K)) (hprimitive : T.IsPrimitive)
    (hratios : ∀ i,
      letI : Differential (RatFunc K) := differentialRatFunc
      Differential.deriv
        (algebraMap K[X] (RatFunc K) (T.coeff i) /
          algebraMap K[X] (RatFunc K) T.leadingCoeff) = 0) :
    ∀ i, (T.coeff i).derivative = 0 := by
  apply derivatives_eq_zero_of_isPrimitive_of_derivative_rel T hprimitive
  intro i
  exact polynomial_relation_of_ratFunc_deriv_div_eq_zero
    (T.coeff i) T.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hprimitive.ne_zero) (hratios i)
variable {L : Type*} [Field L]
variable [Algebra (RatFunc K) L]
theorem exists_primitive_map_eq_C_mul_minpoly
    (a : L) (ha : IsIntegral (RatFunc K) a) :
    ∃ T : Polynomial (Polynomial K), T.IsPrimitive ∧
      T.map (algebraMap K[X] (RatFunc K)) =
        C (algebraMap K[X] (RatFunc K) T.leadingCoeff) *
          minpoly (RatFunc K) a := by
  classical
  let P : Polynomial (RatFunc K) := minpoly (RatFunc K) a
  let q : Polynomial (Polynomial K) :=
    IsLocalization.integerNormalization
      (nonZeroDivisors (Polynomial K)) P
  let T : Polynomial (Polynomial K) := q.primPart
  have hPzero : P ≠ 0 := minpoly.ne_zero ha
  have hPmonic : P.Monic := minpoly.monic ha
  have hqzero : q ≠ 0 := by
    change IsLocalization.integerNormalization
      (nonZeroDivisors (Polynomial K)) P ≠ 0
    intro h
    exact hPzero (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  have hcontentzero : q.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  obtain ⟨b, hbmem, hqmap⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors (Polynomial K)) P
  have hbzero : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have hbmapzero : algebraMap K[X] (RatFunc K) b ≠ 0 :=
    RatFunc.algebraMap_ne_zero hbzero
  have hcmapzero : algebraMap K[X] (RatFunc K) q.content ≠ 0 :=
    RatFunc.algebraMap_ne_zero hcontentzero
  have hproduct :
      C (algebraMap K[X] (RatFunc K) q.content) *
          T.map (algebraMap K[X] (RatFunc K)) =
        C (algebraMap K[X] (RatFunc K) b) * P := by
    calc
      C (algebraMap K[X] (RatFunc K) q.content) *
          T.map (algebraMap K[X] (RatFunc K)) =
          q.map (algebraMap K[X] (RatFunc K)) := by
        dsimp only [T]
        rw [← map_C, ← Polynomial.map_mul]
        exact congrArg
          (Polynomial.map (algebraMap K[X] (RatFunc K)))
          q.eq_C_content_mul_primPart.symm
      _ = b • P := hqmap
      _ = C (algebraMap K[X] (RatFunc K) b) * P := by
        rw [Algebra.smul_def]
        rfl
  let c : RatFunc K :=
    algebraMap K[X] (RatFunc K) b /
      algebraMap K[X] (RatFunc K) q.content
  have hczero : c ≠ 0 := div_ne_zero hbmapzero hcmapzero
  have hscale :
      T.map (algebraMap K[X] (RatFunc K)) = C c * P := by
    apply mul_left_cancel₀
      (show C (algebraMap K[X] (RatFunc K) q.content) ≠ 0 by
        simpa using hcmapzero)
    rw [hproduct]
    have hdc : algebraMap K[X] (RatFunc K) q.content * c =
        algebraMap K[X] (RatFunc K) b := by
      dsimp [c]
      exact mul_div_cancel₀ _ hcmapzero
    calc
      C (algebraMap K[X] (RatFunc K) b) * P =
          C (algebraMap K[X] (RatFunc K) q.content * c) * P := by
        rw [hdc]
      _ = C (algebraMap K[X] (RatFunc K) q.content) *
          (C c * P) := by rw [C_mul, mul_assoc]
  have hlc := congrArg
    (fun Q : Polynomial (RatFunc K) ↦ Q.leadingCoeff) hscale
  have hmapinjective : Function.Injective
      (algebraMap K[X] (RatFunc K)) := RatFunc.algebraMap_injective K
  have hlc_eq : algebraMap K[X] (RatFunc K) T.leadingCoeff = c := by
    simpa only [Polynomial.leadingCoeff_map_of_injective hmapinjective,
      Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C c,
      hPmonic.leadingCoeff, mul_one] using hlc
  refine ⟨T, q.isPrimitive_primPart, ?_⟩
  rw [hlc_eq]
  exact hscale
variable [FiniteDimensional (RatFunc K) L]
variable [Algebra.IsSeparable (RatFunc K) L]
theorem primitive_coeff_derivatives_eq_zero_of_map_eq_C_mul_minpoly
    (a : L) (ha : IsIntegral (RatFunc K) a)
    (T : Polynomial (Polynomial K)) (hprimitive : T.IsPrimitive)
    (hmap : T.map (algebraMap K[X] (RatFunc K)) =
      C (algebraMap K[X] (RatFunc K) T.leadingCoeff) *
        minpoly (RatFunc K) a) :
    letI : Differential (RatFunc K) := differentialRatFunc
    letI : Differential L := differentialFiniteSeparable (RatFunc K) L
    Differential.deriv a = 0 →
      ∀ i, (T.coeff i).derivative = 0 := by
  letI : Differential (RatFunc K) := differentialRatFunc
  letI : Differential L := differentialFiniteSeparable (RatFunc K) L
  letI : DifferentialAlgebra (RatFunc K) L :=
    differentialAlgebraFiniteSeparable (RatFunc K) L
  intro haderiv
  apply derivatives_eq_zero_of_isPrimitive_of_ratios_deriv_eq_zero
    T hprimitive
  intro i
  have hv : algebraMap K[X] (RatFunc K) T.leadingCoeff ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr hprimitive.ne_zero)
  have hcoeff := congrArg
    (fun P : Polynomial (RatFunc K) ↦ P.coeff i) hmap
  simp only [coeff_map, coeff_C_mul] at hcoeff
  have hratio :
      algebraMap K[X] (RatFunc K) (T.coeff i) /
          algebraMap K[X] (RatFunc K) T.leadingCoeff =
        (minpoly (RatFunc K) a).coeff i := by
    rw [div_eq_iff hv]
    simpa only [mul_comm] using hcoeff
  rw [hratio]
  exact deriv_coeff_minpoly_eq_zero_of_deriv_eq_zero
    a ha haderiv i
end PrimitiveCoefficientDescent
section CoefficientFamily
variable {K : Type*} [Field K]
theorem degreeX_add_le_max
    (a b : Polynomial (Polynomial K)) :
    Polynomial.Bivariate.degreeX (a + b) ≤
      max (Polynomial.Bivariate.degreeX a)
        (Polynomial.Bivariate.degreeX b) := by
  rw [← Polynomial.Bivariate.natDegreeY_swap]
  change (Polynomial.Bivariate.swap (a + b)).natDegree ≤ _
  rw [map_add]
  calc
    (Polynomial.Bivariate.swap a +
        Polynomial.Bivariate.swap b).natDegree
        ≤ max (Polynomial.Bivariate.swap a).natDegree
          (Polynomial.Bivariate.swap b).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ = max (Polynomial.Bivariate.degreeX a)
          (Polynomial.Bivariate.degreeX b) := by
      have ha := Polynomial.Bivariate.natDegreeY_swap a
      have hb := Polynomial.Bivariate.natDegreeY_swap b
      simpa only [Polynomial.Bivariate.natDegreeY] using congrArg₂ max ha hb
theorem degreeX_neg (a : Polynomial (Polynomial K)) :
    Polynomial.Bivariate.degreeX (-a) =
      Polynomial.Bivariate.degreeX a := by
  rw [← Polynomial.Bivariate.natDegreeY_swap]
  change (Polynomial.Bivariate.swap (-a)).natDegree = _
  rw [map_neg, Polynomial.natDegree_neg]
  simpa only [Polynomial.Bivariate.natDegreeY] using
    Polynomial.Bivariate.natDegreeY_swap a
theorem degreeX_sub_le_max
    (a b : Polynomial (Polynomial K)) :
    Polynomial.Bivariate.degreeX (a - b) ≤
      max (Polynomial.Bivariate.degreeX a)
        (Polynomial.Bivariate.degreeX b) := by
  rw [sub_eq_add_neg]
  simpa only [degreeX_neg] using degreeX_add_le_max a (-b)
theorem degreeX_C_le_natDegree (a : Polynomial K) :
    Polynomial.Bivariate.degreeX (C a) ≤ a.natDegree := by
  rw [← Polynomial.Bivariate.natDegreeY_swap]
  change (Polynomial.Bivariate.swap (C a)).natDegree ≤ a.natDegree
  rw [Polynomial.Bivariate.swap_C]
  exact Polynomial.natDegree_map_le
theorem degreeX_outerVariable :
    Polynomial.Bivariate.degreeX
      (Polynomial.X : Polynomial (Polynomial K)) = 0 := by
  let innerX : Polynomial K := Polynomial.X
  have h := Polynomial.Bivariate.degreeX_swap
    (f := Polynomial.C innerX)
  rw [Polynomial.Bivariate.swap_C] at h
  calc
    Polynomial.Bivariate.degreeX
        (Polynomial.X : Polynomial (Polynomial K)) =
        Polynomial.Bivariate.natDegreeY (Polynomial.C innerX) := by
      simpa [innerX] using h
    _ = 0 := by simp [Polynomial.Bivariate.natDegreeY]
noncomputable def gaoAnnihilatingResultant
    (f g : Polynomial (Polynomial K)) (m : ℕ) :
    Polynomial (Polynomial K) :=
  let fA : Polynomial (Polynomial (Polynomial K)) := f.map C
  let residueEquation : Polynomial (Polynomial (Polynomial K)) :=
    C (Polynomial.X : Polynomial (Polynomial K)) *
      f.derivative.map C - g.map C
  resultant fA residueEquation m (m - 1)
variable {p : ℕ} [CharP K p]
noncomputable def coefficientDegree (T : Polynomial (Polynomial K)) : ℕ :=
  T.support.sup fun i ↦ (T.coeff i).natDegree
theorem coefficientDegree_eq_degreeX (T : Polynomial (Polynomial K)) :
    coefficientDegree T = Polynomial.Bivariate.degreeX T := by
  rfl
theorem coeff_natDegree_le_coefficientDegree
    (T : Polynomial (Polynomial K)) (i : ℕ) :
    (T.coeff i).natDegree ≤ coefficientDegree T := by
  classical
  by_cases hi : T.coeff i = 0
  · simp [hi]
  · exact Finset.le_sup (f := fun j ↦ (T.coeff j).natDegree)
      (mem_support_iff.mpr hi)
theorem char_le_coefficientDegree_of_derivatives_eq_zero
    (hp : p ≠ 0) (T : Polynomial (Polynomial K))
    (hderiv : ∀ i, (T.coeff i).derivative = 0)
    (hnonconstant : ∃ i, (T.coeff i).natDegree ≠ 0) :
    p ≤ coefficientDegree T := by
  obtain ⟨i, hi⟩ := hnonconstant
  exact (eq_zero_or_char_le_natDegree_of_derivative_eq_zero
      hp (T.coeff i) (hderiv i)).resolve_left hi |>.trans
    (coeff_natDegree_le_coefficientDegree T i)
theorem coeff_eq_C_of_derivatives_eq_zero_of_coefficientDegree_lt_char
    (hp : p ≠ 0) (T : Polynomial (Polynomial K))
    (hderiv : ∀ i, (T.coeff i).derivative = 0)
    (hdegree : coefficientDegree T < p) (i : ℕ) :
    T.coeff i = C ((T.coeff i).coeff 0) := by
  apply eq_C_coeff_zero_of_derivative_eq_zero_of_natDegree_lt_char
      hp (T.coeff i) (hderiv i)
  exact (coeff_natDegree_le_coefficientDegree T i).trans_lt hdegree
theorem map_C_map_eval_zero_eq_of_derivatives_eq_zero_of_coefficientDegree_lt_char
    (hp : p ≠ 0) (T : Polynomial (Polynomial K))
    (hderiv : ∀ i, (T.coeff i).derivative = 0)
    (hdegree : coefficientDegree T < p) :
    (T.map (evalRingHom 0)).map C = T := by
  ext i
  simp only [coeff_map, coe_evalRingHom]
  rw [coeff_eq_C_of_derivatives_eq_zero_of_coefficientDegree_lt_char
    hp T hderiv hdegree i]
  simp
theorem coefficientDegree_le_of_dvd
    (T M : Polynomial (Polynomial K)) (hM : M ≠ 0) (hdiv : T ∣ M) :
    coefficientDegree T ≤ coefficientDegree M := by
  obtain ⟨C, rfl⟩ := hdiv
  have hnz : T ≠ 0 ∧ C ≠ 0 := mul_ne_zero_iff.mp hM
  rw [coefficientDegree_eq_degreeX, coefficientDegree_eq_degreeX,
    Polynomial.Bivariate.degreeX_mul T C hnz.1 hnz.2]
  exact Nat.le_add_right _ _
theorem exists_constantPolynomial_of_derivatives_eq_zero_of_dvd_degree_lt_char
    (hp : p ≠ 0) (T M : Polynomial (Polynomial K))
    (hderiv : ∀ i, (T.coeff i).derivative = 0)
    (hM : M ≠ 0) (hdiv : T ∣ M)
    (hMdegree : coefficientDegree M < p) :
    ∃ t : Polynomial K, t.map C = T := by
  have hTdegree : coefficientDegree T < p :=
    (coefficientDegree_le_of_dvd T M hM hdiv).trans_lt hMdegree
  exact ⟨T.map (evalRingHom 0),
    map_C_map_eval_zero_eq_of_derivatives_eq_zero_of_coefficientDegree_lt_char
      hp T hderiv hTdegree⟩
end CoefficientFamily
section PositiveCharacteristicLemma24Core
variable {K L : Type*} [Field K] [Field L]
variable {p : ℕ} [CharP K p]
variable [Algebra (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
variable [Algebra.IsSeparable (RatFunc K) L]
theorem exists_constantPolynomial_of_primitive_minpoly_dvd_degree_lt_char
    (hp : p ≠ 0) (a : L) (ha : IsIntegral (RatFunc K) a)
    (T M : Polynomial (Polynomial K)) (hprimitive : T.IsPrimitive)
    (hmap : T.map (algebraMap K[X] (RatFunc K)) =
      C (algebraMap K[X] (RatFunc K) T.leadingCoeff) *
        minpoly (RatFunc K) a)
    (hM : M ≠ 0) (hdiv : T ∣ M)
    (hMdegree : coefficientDegree M < p) :
    letI : Differential (RatFunc K) := differentialRatFunc
    letI : Differential L := differentialFiniteSeparable (RatFunc K) L
    Differential.deriv a = 0 →
      ∃ t : Polynomial K, t.map C = T := by
  letI : Differential (RatFunc K) := differentialRatFunc
  letI : Differential L := differentialFiniteSeparable (RatFunc K) L
  intro haderiv
  have hcoeff :=
    primitive_coeff_derivatives_eq_zero_of_map_eq_C_mul_minpoly
      a ha T hprimitive hmap haderiv
  exact exists_constantPolynomial_of_derivatives_eq_zero_of_dvd_degree_lt_char
    hp T M hcoeff hM hdiv hMdegree
end PositiveCharacteristicLemma24Core
section CommonRoot
variable {K : Type*} [Field K]
theorem resultant_eq_zero_of_common_root
    (f g : K[X]) (x : K) (hnonzero : f ≠ 0 ∨ g ≠ 0)
    (hf : f.eval x = 0) (hg : g.eval x = 0) :
    resultant f g = 0 := by
  rw [resultant_eq_zero_iff]
  refine ⟨hnonzero, ?_⟩
  intro hcoprime
  obtain ⟨a, b, hab⟩ := hcoprime
  have heval := congrArg (eval x) hab
  simp [hf, hg] at heval
theorem resultant_eq_zero_of_common_root_of_natDegree_le
    (f g : K[X]) (m n : ℕ)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n)
    (x : K) (hnonzero : f ≠ 0 ∨ g ≠ 0)
    (hf : f.eval x = 0) (hg : g.eval x = 0) :
    resultant f g m n = 0 := by
  have hbase : resultant f g f.natDegree g.natDegree = 0 :=
    resultant_eq_zero_of_common_root f g x hnonzero hf hg
  calc
    resultant f g m n =
        resultant f g (f.natDegree + (m - f.natDegree))
          (g.natDegree + (n - g.natDegree)) := by
      rw [Nat.add_sub_of_le hfm, Nat.add_sub_of_le hgn]
    _ = (-1) ^ ((g.natDegree + (n - g.natDegree)) *
          (m - f.natDegree)) *
        g.coeff (g.natDegree + (n - g.natDegree)) ^
          (m - f.natDegree) *
        resultant f g f.natDegree
          (g.natDegree + (n - g.natDegree)) := by
      rw [resultant_add_left_deg f g f.natDegree
        (g.natDegree + (n - g.natDegree)) (m - f.natDegree) le_rfl]
    _ = (-1) ^ ((g.natDegree + (n - g.natDegree)) *
          (m - f.natDegree)) *
        g.coeff (g.natDegree + (n - g.natDegree)) ^
          (m - f.natDegree) *
        (f.coeff f.natDegree ^ (n - g.natDegree) *
          resultant f g f.natDegree g.natDegree) := by
      rw [resultant_add_right_deg f g f.natDegree g.natDegree
        (n - g.natDegree) le_rfl]
    _ = 0 := by rw [hbase]; simp
end CommonRoot
section GaoAnnihilation
variable {K L : Type*} [Field K] [Field L]
variable [Algebra (RatFunc K) L]
noncomputable def polynomialCoeffToExtension : Polynomial K →+* L :=
  (algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K))
theorem aeval_gaoAnnihilatingResultant_eq_zero
    (f g : Polynomial (Polynomial K)) (m : ℕ) (hm : 1 ≤ m)
    (hfdegree : f.natDegree = m)
    (hgdegree : g.natDegree ≤ m - 1)
    (beta a : L)
    (hroot : (f.map polynomialCoeffToExtension).eval beta = 0)
    (hresidue :
      a * (f.map polynomialCoeffToExtension).derivative.eval beta =
        (g.map polynomialCoeffToExtension).eval beta) :
    aeval a
      ((gaoAnnihilatingResultant f g m).map
        (algebraMap K[X] (RatFunc K))) = 0 := by
  let fL : Polynomial L := f.map polynomialCoeffToExtension
  let gL : Polynomial L := g.map polynomialCoeffToExtension
  let qL : Polynomial L := C a * fL.derivative - gL
  have hfzero : f ≠ 0 := by
    intro hf
    rw [hf, natDegree_zero] at hfdegree
    omega
  have hcoeffinjective : Function.Injective
      (polynomialCoeffToExtension (K := K) (L := L)) :=
    (algebraMap (RatFunc K) L).injective.comp
      (RatFunc.algebraMap_injective K)
  have hfLzero : fL ≠ 0 :=
    (Polynomial.map_ne_zero_iff hcoeffinjective).mpr hfzero
  have hfLdegree : fL.natDegree ≤ m := by
    exact Polynomial.natDegree_map_le.trans hfdegree.le
  have hgLdegree : gL.natDegree ≤ m - 1 := by
    exact Polynomial.natDegree_map_le.trans hgdegree
  have hqLdegree : qL.natDegree ≤ m - 1 := by
    dsimp only [qL]
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    apply max_le
    · exact (Polynomial.natDegree_C_mul_le a fL.derivative).trans
        ((Polynomial.natDegree_derivative_le fL).trans
          (Nat.sub_le_sub_right hfLdegree 1))
    · exact hgLdegree
  have hqroot : qL.eval beta = 0 := by
    dsimp only [qL, fL, gL]
    rw [eval_sub, eval_mul, eval_C, hresidue, sub_self]
  have hresultant : resultant fL qL m (m - 1) = 0 :=
    resultant_eq_zero_of_common_root_of_natDegree_le
      fL qL m (m - 1) hfLdegree hqLdegree beta
      (Or.inl hfLzero) hroot hqroot
  let phi : Polynomial (Polynomial K) →+* L :=
    Polynomial.eval₂RingHom polynomialCoeffToExtension a
  have hmapf :
      (f.map C).map phi = fL := by
    ext i
    simp [phi, fL, polynomialCoeffToExtension]
  have hmapq :
      (C (Polynomial.X : Polynomial (Polynomial K)) *
          f.derivative.map C - g.map C).map phi = qL := by
    ext i
    simp [phi, qL, fL, gL, polynomialCoeffToExtension,
      Polynomial.derivative_map]
  change Polynomial.eval₂ (algebraMap (RatFunc K) L) a
    ((gaoAnnihilatingResultant f g m).map
      (algebraMap K[X] (RatFunc K))) = 0
  rw [Polynomial.eval₂_map]
  change phi (gaoAnnihilatingResultant f g m) = 0
  unfold gaoAnnihilatingResultant
  rw [← Polynomial.resultant_map_map]
  rw [hmapf, hmapq]
  exact hresultant
theorem primitive_minpoly_dvd_gaoAnnihilatingResultant
    (f g : Polynomial (Polynomial K)) (m : ℕ) (hm : 1 ≤ m)
    (hfdegree : f.natDegree = m)
    (hgdegree : g.natDegree ≤ m - 1)
    (beta a : L)
    (hroot : (f.map polynomialCoeffToExtension).eval beta = 0)
    (hresidue :
      a * (f.map polynomialCoeffToExtension).derivative.eval beta =
        (g.map polynomialCoeffToExtension).eval beta)
    (T : Polynomial (Polynomial K)) (hprimitive : T.IsPrimitive)
    (hTmap : T.map (algebraMap K[X] (RatFunc K)) =
      C (algebraMap K[X] (RatFunc K) T.leadingCoeff) *
        minpoly (RatFunc K) a) :
    T ∣ gaoAnnihilatingResultant f g m := by
  classical
  let M : Polynomial (Polynomial K) :=
    gaoAnnihilatingResultant f g m
  have hvanish :
      aeval a (M.map (algebraMap K[X] (RatFunc K))) = 0 :=
    aeval_gaoAnnihilatingResultant_eq_zero
      f g m hm hfdegree hgdegree beta a hroot hresidue
  have hmindvd :
      minpoly (RatFunc K) a ∣
        M.map (algebraMap K[X] (RatFunc K)) :=
    minpoly.dvd (RatFunc K) a hvanish
  obtain ⟨Q, hQ⟩ := hmindvd
  have hlc : algebraMap K[X] (RatFunc K) T.leadingCoeff ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr hprimitive.ne_zero)
  have hmapdvd :
      T.map (algebraMap K[X] (RatFunc K)) ∣
        M.map (algebraMap K[X] (RatFunc K)) := by
    let lc : RatFunc K :=
      algebraMap K[X] (RatFunc K) T.leadingCoeff
    refine ⟨C lc⁻¹ * Q, ?_⟩
    rw [hTmap, hQ]
    change minpoly (RatFunc K) a * Q =
      (C lc * minpoly (RatFunc K) a) * (C lc⁻¹ * Q)
    calc
      minpoly (RatFunc K) a * Q =
          C (lc * lc⁻¹) * (minpoly (RatFunc K) a * Q) := by
        rw [mul_inv_cancel₀ (show lc ≠ 0 from hlc), C_1, one_mul]
      _ = (C lc * minpoly (RatFunc K) a) * (C lc⁻¹ * Q) := by
        rw [C_mul]
        ring
  exact hprimitive.dvd_of_fraction_map_dvd_fraction_map hmapdvd
end GaoAnnihilation
section ResultantNonvanishing
theorem coeff_prod_at_sum_caps
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (f : ι → R[X]) (cap : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ cap i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, cap i) =
      ∏ i ∈ s, (f i).coeff (cap i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha' : (f a).natDegree ≤ cap a :=
        h a (Finset.mem_insert_self _ _)
      have hs : ∀ i ∈ s, (f i).natDegree ≤ cap i := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Polynomial.coeff_mul_add_eq_of_natDegree_le ha']
      · rw [ih hs, Finset.prod_insert ha]
      · exact (Polynomial.natDegree_prod_le _ _).trans
          (Finset.sum_le_sum hs)
theorem coeff_resultant_parameter_mul_sub
    {R : Type*} [CommRing R]
    (f h g : R[X]) (m n : ℕ) :
    (resultant (f.map (Polynomial.C : R →+* R[X]))
      (Polynomial.C (Polynomial.X : R[X]) *
        h.map (Polynomial.C : R →+* R[X]) -
        g.map (Polynomial.C : R →+* R[X])) m n).coeff m =
        resultant f h m n := by
  classical
  let cap : Fin (m + n) → ℕ :=
    Fin.addCases (fun _ : Fin m ↦ 1) (fun _ : Fin n ↦ 0)
  have hsum : ∑ j, cap j = m := by
    rw [Fin.sum_univ_add]
    simp [cap]
  unfold resultant
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [Polynomial.coeff_smul]
  congr 1
  have hdegree : ∀ j ∈ (Finset.univ : Finset (Fin (m + n))),
      ((sylvester
        (f.map (Polynomial.C : R →+* R[X]))
        (Polynomial.C (Polynomial.X : R[X]) *
          h.map (Polynomial.C : R →+* R[X]) -
          g.map (Polynomial.C : R →+* R[X])) m n) (σ j) j).natDegree ≤
        cap j := by
    intro j _
    exact Fin.addCases
      (fun j ↦ by
        simp only [sylvester, Matrix.of_apply, Fin.addCases_left, cap]
        split_ifs
        · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
            Polynomial.coeff_map]
          compute_degree
        · simp)
      (fun j ↦ by
        simp only [sylvester, Matrix.of_apply, Fin.addCases_right, cap]
        split_ifs <;> simp [Polynomial.coeff_map])
      j
  have htop := coeff_prod_at_sum_caps
    (Finset.univ : Finset (Fin (m + n)))
    (fun j ↦
      (sylvester
        (f.map (Polynomial.C : R →+* R[X]))
        (Polynomial.C (Polynomial.X : R[X]) *
          h.map (Polynomial.C : R →+* R[X]) -
          g.map (Polynomial.C : R →+* R[X])) m n) (σ j) j)
    cap hdegree
  simp only [hsum] at htop
  rw [htop]
  refine Finset.prod_congr rfl ?_
  intro j _
  exact Fin.addCases
    (fun j ↦ by
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, cap]
      split_ifs
      · simp [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_map]
      · simp)
    (fun j ↦ by
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, cap]
      split_ifs <;> simp [Polynomial.coeff_map])
    j
theorem natDegree_derivative_eq_pred_of_natDegree_lt_char
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {p m : ℕ} [CharP R p]
    (f : R[X]) (hm : 1 ≤ m) (hfdegree : f.natDegree = m)
    (hmp : m < p) :
    f.derivative.natDegree = m - 1 := by
  have hmcast : (m : R) ≠ 0 := by
    intro hz
    have hdvd : p ∣ m := (CharP.cast_eq_zero_iff R p m).mp hz
    exact (Nat.not_le_of_lt hmp)
      (Nat.le_of_dvd (Nat.zero_lt_of_lt hm) hdvd)
  have hf : f ≠ 0 := by
    intro hf
    simp [hf] at hfdegree
    omega
  have hlc : f.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hf
  have hcoeff : f.derivative.coeff (m - 1) ≠ 0 := by
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hm]
    rw [show f.coeff m = f.leadingCoeff by
      rw [← hfdegree, Polynomial.coeff_natDegree]]
    have hcasteq : ((↑(m - 1) : R) + 1) = (m : R) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun n : ℕ ↦ (n : R)) (Nat.sub_add_cancel hm)
    rw [hcasteq]
    exact mul_ne_zero hlc hmcast
  apply le_antisymm
  · simpa [hfdegree] using Polynomial.natDegree_derivative_le f
  · exact Polynomial.le_natDegree_of_ne_zero hcoeff
theorem resultant_parameter_mul_sub_ne_zero
    {R : Type*} [CommRing R] [IsDomain R]
    (f h g : R[X]) (m n : ℕ)
    (hfdegree : f.natDegree = m) (hhdegree : h.natDegree = n)
    (hc : IsCoprime f h) :
    resultant (f.map (Polynomial.C : R →+* R[X]))
      (Polynomial.C (Polynomial.X : R[X]) *
        h.map (Polynomial.C : R →+* R[X]) -
        g.map (Polynomial.C : R →+* R[X])) m n ≠ 0 := by
  intro hz
  have hcoeff := congrArg (fun P : R[X] ↦ P.coeff m) hz
  rw [coeff_resultant_parameter_mul_sub, Polynomial.coeff_zero] at hcoeff
  have hres : resultant f h ≠ 0 :=
    Polynomial.resultant_ne_zero f h hc
  apply hres
  simpa only [hfdegree, hhdegree] using hcoeff
variable {K : Type*} [Field K] {p : ℕ} [CharP K p]
theorem gaoAnnihilatingResultant_ne_zero_of_isCoprime
    (f g : Polynomial (Polynomial K)) (m : ℕ)
    (hm : 1 ≤ m) (hfdegree : f.natDegree = m)
    (hmp : m < p) (hc : IsCoprime f f.derivative) :
    gaoAnnihilatingResultant f g m ≠ 0 := by
  have hfderivdegree : f.derivative.natDegree = m - 1 :=
    natDegree_derivative_eq_pred_of_natDegree_lt_char
      f hm hfdegree hmp
  unfold gaoAnnihilatingResultant
  exact resultant_parameter_mul_sub_ne_zero
    f f.derivative g m (m - 1) hfdegree hfderivdegree hc
end ResultantNonvanishing
section ResultantDegree
theorem natDegree_det_le_sum_rowCaps_commRing
    {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (M : Matrix I I R[X]) (rowCap : I → ℕ)
    (hentry : ∀ i j, (M i j).natDegree ≤ rowCap i) :
    M.det.natDegree ≤ ∑ i, rowCap i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro sigma _
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simpa using hentry i (sigma i)
variable {K : Type*} [Field K]
theorem coefficientDegree_det_le_sum_rowCaps
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (Polynomial (Polynomial K))) (rowCap : I → ℕ)
    (hentry : ∀ i j,
      Polynomial.Bivariate.degreeX (M i j) ≤ rowCap i) :
    Polynomial.Bivariate.degreeX M.det ≤ ∑ i, rowCap i := by
  rw [← Polynomial.Bivariate.natDegreeY_swap]
  change (Polynomial.Bivariate.swap M.det).natDegree ≤ _
  rw [show Polynomial.Bivariate.swap M.det =
      ((Polynomial.Bivariate.swap.toRingEquiv.toRingHom).mapMatrix M).det by
    simpa using RingHom.map_det
      Polynomial.Bivariate.swap.toRingEquiv.toRingHom M]
  apply natDegree_det_le_sum_rowCaps_commRing
  intro i j
  change (Polynomial.Bivariate.swap (M i j)).natDegree ≤ rowCap i
  simpa only [Polynomial.Bivariate.natDegreeY] using
    (Polynomial.Bivariate.natDegreeY_swap (M i j)).le.trans
      (hentry i j)
theorem natDegree_resultant_le_bihomogeneous
    (f g : Polynomial (Polynomial K)) (m n df dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ dg) :
    (resultant f g m n).natDegree ≤ m * dg + n * df := by
  classical
  unfold resultant
  rw [← Matrix.det_transpose]
  let rowCap : Fin (m + n) → ℕ :=
    Fin.addCases (fun _ : Fin m ↦ dg) (fun _ : Fin n ↦ df)
  calc
    (Matrix.transpose (sylvester f g m n)).det.natDegree
        ≤ ∑ j, rowCap j := by
      apply BCHKSGaoSpecializationCore6400.natDegree_det_le_sum_rowCaps
      intro j i
      exact Fin.addCases
        (fun j ↦ by
          simp only [Matrix.transpose_apply, sylvester, Matrix.of_apply,
            Fin.addCases_left, rowCap]
          split_ifs
          · exact hg _
          · simp)
        (fun j ↦ by
          simp only [Matrix.transpose_apply, sylvester, Matrix.of_apply,
            Fin.addCases_right, rowCap]
          split_ifs
          · exact hf _
          · simp)
        j
    _ = m * dg + n * df := by
      rw [Fin.sum_univ_add]
      simp [rowCap]
theorem coefficientDegree_resultant_le_bihomogeneous
    (f g : Polynomial (Polynomial (Polynomial K))) (m n df dg : ℕ)
    (hf : ∀ i,
      Polynomial.Bivariate.degreeX (f.coeff i) ≤ df)
    (hg : ∀ i,
      Polynomial.Bivariate.degreeX (g.coeff i) ≤ dg) :
    coefficientDegree (resultant f g m n) ≤ m * dg + n * df := by
  classical
  rw [coefficientDegree_eq_degreeX]
  unfold resultant
  rw [← Matrix.det_transpose]
  let rowCap : Fin (m + n) → ℕ :=
    Fin.addCases (fun _ : Fin m ↦ dg) (fun _ : Fin n ↦ df)
  calc
    Polynomial.Bivariate.degreeX
        (Matrix.transpose (sylvester f g m n)).det
        ≤ ∑ j, rowCap j := by
      apply coefficientDegree_det_le_sum_rowCaps
      intro j i
      exact Fin.addCases
        (fun j ↦ by
          simp only [Matrix.transpose_apply, sylvester, Matrix.of_apply,
            Fin.addCases_left, rowCap]
          split_ifs
          · exact hg _
          · simp [Polynomial.Bivariate.degreeX])
        (fun j ↦ by
          simp only [Matrix.transpose_apply, sylvester, Matrix.of_apply,
            Fin.addCases_right, rowCap]
          split_ifs
          · exact hf _
          · simp [Polynomial.Bivariate.degreeX])
        j
    _ = m * dg + n * df := by
      rw [Fin.sum_univ_add]
      simp [rowCap]
theorem coefficientDegree_gaoAnnihilatingResultant_le
    (f g : Polynomial (Polynomial K)) (m n : ℕ) (hm : 1 ≤ m)
    (hf : ∀ i, (f.coeff i).natDegree ≤ n)
    (hg : ∀ i, (g.coeff i).natDegree ≤ n) :
    coefficientDegree (gaoAnnihilatingResultant f g m) ≤
      (2 * m - 1) * n := by
  have hfderiv : ∀ i, (f.derivative.coeff i).natDegree ≤ n := by
    intro i
    rw [coeff_derivative]
    calc
      (f.coeff (i + 1) * (↑i + 1)).natDegree ≤
          (f.coeff (i + 1)).natDegree +
            (↑i + 1 : Polynomial K).natDegree :=
        Polynomial.natDegree_mul_le
      _ = (f.coeff (i + 1)).natDegree := by
        have hcast : (↑i + 1 : Polynomial K) =
            (↑(i + 1) : Polynomial K) := by norm_num
        rw [hcast, Polynomial.natDegree_natCast, Nat.add_zero]
      _ ≤ n := hf (i + 1)
  unfold gaoAnnihilatingResultant
  have hbound := coefficientDegree_resultant_le_bihomogeneous
    (f.map C)
    (C (Polynomial.X : Polynomial (Polynomial K)) *
      f.derivative.map C - g.map C)
    m (m - 1) n n
    (fun i ↦ by
      rw [coeff_map]
      exact (degreeX_C_le_natDegree (f.coeff i)).trans (hf i))
    (fun i ↦ by
      simp only [coeff_sub, coeff_C_mul, coeff_map]
      refine (degreeX_sub_le_max _ _).trans ?_
      apply max_le
      · calc
          Polynomial.Bivariate.degreeX
              ((Polynomial.X : Polynomial (Polynomial K)) *
                C (f.derivative.coeff i))
              ≤ Polynomial.Bivariate.degreeX
                    (Polynomial.X : Polynomial (Polynomial K)) +
                  Polynomial.Bivariate.degreeX
                    (C (f.derivative.coeff i)) :=
            Polynomial.Bivariate.degreeX_mul_le _ _
          _ ≤ 0 + n := Nat.add_le_add degreeX_outerVariable.le
            ((degreeX_C_le_natDegree _).trans (hfderiv i))
          _ = n := by simp
      · exact (degreeX_C_le_natDegree (g.coeff i)).trans (hg i))
  calc
    coefficientDegree (resultant (f.map C)
        (C (Polynomial.X : Polynomial (Polynomial K)) *
          f.derivative.map C - g.map C) m (m - 1))
        ≤ m * n + (m - 1) * n := hbound
    _ = (2 * m - 1) * n := by
      have hm' : 2 * m - 1 = m + (m - 1) := by omega
      rw [hm', Nat.add_mul]
theorem natDegree_resultant_le_gao
    (f g : Polynomial (Polynomial K)) (m n : ℕ) (hm : 1 ≤ m)
    (hf : ∀ i, (f.coeff i).natDegree ≤ n)
    (hg : ∀ i, (g.coeff i).natDegree ≤ n) :
    (resultant f g m (m - 1)).natDegree ≤ (2 * m - 1) * n := by
  have h := natDegree_resultant_le_bihomogeneous
    f g m (m - 1) n n hf hg
  calc
    (resultant f g m (m - 1)).natDegree
        ≤ m * n + (m - 1) * n := h
    _ = (2 * m - 1) * n := by
      have hm' : 2 * m - 1 = m + (m - 1) := by omega
      rw [hm', Nat.add_mul]
end ResultantDegree
section GaoLemma24
variable {K L : Type*} [Field K] [Field L]
variable {p : ℕ} [CharP K p]
variable [Algebra (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
variable [Algebra.IsSeparable (RatFunc K) L]
theorem exists_constant_polynomial_of_gao_residue
    (f g : Polynomial (Polynomial K)) (m n : ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hfdegree : f.natDegree = m)
    (hgdegree : g.natDegree ≤ m - 1)
    (hfcoeff : ∀ i, (f.coeff i).natDegree ≤ n)
    (hgcoeff : ∀ i, (g.coeff i).natDegree ≤ n)
    (hchar : (2 * m - 1) * n < p)
    (hc : IsCoprime f f.derivative)
    (beta a : L)
    (hroot : (f.map polynomialCoeffToExtension).eval beta = 0)
    (hresidue :
      a * (f.map polynomialCoeffToExtension).derivative.eval beta =
        (g.map polynomialCoeffToExtension).eval beta)
    (ha : IsIntegral (RatFunc K) a)
    (T : Polynomial (Polynomial K)) (hprimitive : T.IsPrimitive)
    (hTmap : T.map (algebraMap K[X] (RatFunc K)) =
      C (algebraMap K[X] (RatFunc K) T.leadingCoeff) *
        minpoly (RatFunc K) a) :
    letI : Differential (RatFunc K) := differentialRatFunc
    letI : Differential L := differentialFiniteSeparable (RatFunc K) L
    Differential.deriv a = 0 →
      ∃ t : Polynomial K, t.map C = T := by
  letI : Differential (RatFunc K) := differentialRatFunc
  letI : Differential L := differentialFiniteSeparable (RatFunc K) L
  intro haderiv
  let M : Polynomial (Polynomial K) :=
    gaoAnnihilatingResultant f g m
  have hm_le_two : m ≤ 2 * m - 1 := by omega
  have htwo_le_product : 2 * m - 1 ≤ (2 * m - 1) * n :=
    Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt hn)
  have hmp : m < p :=
    (hm_le_two.trans htwo_le_product).trans_lt hchar
  have hp : p ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hmp)
  have hM : M ≠ 0 :=
    gaoAnnihilatingResultant_ne_zero_of_isCoprime
      f g m hm hfdegree hmp hc
  have hdiv : T ∣ M :=
    primitive_minpoly_dvd_gaoAnnihilatingResultant
      f g m hm hfdegree hgdegree beta a hroot hresidue
        T hprimitive hTmap
  have hMdegree_le : coefficientDegree M ≤ (2 * m - 1) * n := by
    dsimp only [M]
    exact coefficientDegree_gaoAnnihilatingResultant_le
      f g m n hm hfcoeff hgcoeff
  have hMdegree : coefficientDegree M < p :=
    hMdegree_le.trans_lt hchar
  exact exists_constantPolynomial_of_primitive_minpoly_dvd_degree_lt_char
    hp a ha T M hprimitive hTmap hM hdiv hMdegree haderiv
theorem exists_primitive_constant_minpoly_of_gao_residue
    (f g : Polynomial (Polynomial K)) (m n : ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hfdegree : f.natDegree = m)
    (hgdegree : g.natDegree ≤ m - 1)
    (hfcoeff : ∀ i, (f.coeff i).natDegree ≤ n)
    (hgcoeff : ∀ i, (g.coeff i).natDegree ≤ n)
    (hchar : (2 * m - 1) * n < p)
    (hc : IsCoprime f f.derivative)
    (beta a : L)
    (hroot : (f.map polynomialCoeffToExtension).eval beta = 0)
    (hresidue :
      a * (f.map polynomialCoeffToExtension).derivative.eval beta =
        (g.map polynomialCoeffToExtension).eval beta)
    (ha : IsIntegral (RatFunc K) a) :
    letI : Differential (RatFunc K) := differentialRatFunc
    letI : Differential L := differentialFiniteSeparable (RatFunc K) L
    Differential.deriv a = 0 →
      ∃ (T : Polynomial (Polynomial K)) (t : Polynomial K),
        T.IsPrimitive ∧
        T.map (algebraMap K[X] (RatFunc K)) =
          C (algebraMap K[X] (RatFunc K) T.leadingCoeff) *
            minpoly (RatFunc K) a ∧
        t.map C = T := by
  letI : Differential (RatFunc K) := differentialRatFunc
  letI : Differential L := differentialFiniteSeparable (RatFunc K) L
  intro haderiv
  obtain ⟨T, hprimitive, hTmap⟩ :=
    exists_primitive_map_eq_C_mul_minpoly a ha
  obtain ⟨t, ht⟩ := exists_constant_polynomial_of_gao_residue
    f g m n hm hn hfdegree hgdegree hfcoeff hgcoeff hchar hc
      beta a hroot hresidue ha T hprimitive hTmap haderiv
  exact ⟨T, t, hprimitive, hTmap, ht⟩
theorem isIntegral_of_constant_cleared_minpoly
    [Algebra K L] [IsScalarTower K (RatFunc K) L]
    (a : L)
    (T : Polynomial (Polynomial K)) (hprimitive : T.IsPrimitive)
    (hTmap : T.map (algebraMap K[X] (RatFunc K)) =
      C (algebraMap K[X] (RatFunc K) T.leadingCoeff) *
        minpoly (RatFunc K) a)
    (t : Polynomial K) (ht : t.map C = T) :
    IsIntegral K a := by
  have hTvanish :
      aeval a (T.map (algebraMap K[X] (RatFunc K))) = 0 := by
    rw [hTmap]
    simp [minpoly.aeval]
  have htvanish : aeval a t = 0 := by
    rw [← ht, Polynomial.map_map] at hTvanish
    have hcomp :
        (algebraMap (RatFunc K) L).comp RatFunc.C = algebraMap K L := by
      ext x
      simpa using
        (IsScalarTower.algebraMap_apply K (RatFunc K) L x).symm
    simpa [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp] using
      hTvanish
  have htzero : t ≠ 0 := by
    intro hz
    apply hprimitive.ne_zero
    rw [← ht, hz, Polynomial.map_zero]
  refine ⟨t * C t.leadingCoeff⁻¹,
    Polynomial.monic_mul_leadingCoeff_inv htzero, ?_⟩
  change Polynomial.eval₂ (algebraMap K L) a t = 0 at htvanish
  rw [Polynomial.eval₂_mul, htvanish, zero_mul]
theorem exists_algebraMap_eq_of_isIntegral_of_isAlgClosed
    {K L : Type*} [Field K] [Field L] [IsAlgClosed K]
    [Algebra K L] (a : L) (ha : IsIntegral K a) :
    ∃ c : K, algebraMap K L c = a := by
  have hlc : (minpoly K a).leadingCoeff = 1 :=
    (minpoly.monic ha).leadingCoeff
  have hdegree : (minpoly K a).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible ha)
  have haval : aeval a (minpoly K a) = 0 := minpoly.aeval K a
  refine ⟨-(minpoly K a).coeff 0, ?_⟩
  rw [eq_X_add_C_of_degree_eq_one hdegree, hlc, C_1, one_mul,
    aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at haval
  simpa using haval.symm
theorem exists_ground_constant_of_gao_residue
    [IsAlgClosed K] [Algebra K L] [IsScalarTower K (RatFunc K) L]
    (f g : Polynomial (Polynomial K)) (m n : ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hfdegree : f.natDegree = m)
    (hgdegree : g.natDegree ≤ m - 1)
    (hfcoeff : ∀ i, (f.coeff i).natDegree ≤ n)
    (hgcoeff : ∀ i, (g.coeff i).natDegree ≤ n)
    (hchar : (2 * m - 1) * n < p)
    (hc : IsCoprime f f.derivative)
    (beta a : L)
    (hroot : (f.map polynomialCoeffToExtension).eval beta = 0)
    (hresidue :
      a * (f.map polynomialCoeffToExtension).derivative.eval beta =
        (g.map polynomialCoeffToExtension).eval beta)
    (ha : IsIntegral (RatFunc K) a) :
    letI : Differential (RatFunc K) := differentialRatFunc
    letI : Differential L := differentialFiniteSeparable (RatFunc K) L
    Differential.deriv a = 0 →
      ∃ c : K, algebraMap K L c = a := by
  letI : Differential (RatFunc K) := differentialRatFunc
  letI : Differential L := differentialFiniteSeparable (RatFunc K) L
  intro haderiv
  obtain ⟨T, t, hprimitive, hTmap, ht⟩ :=
    exists_primitive_constant_minpoly_of_gao_residue
      f g m n hm hn hfdegree hgdegree hfcoeff hgcoeff hchar hc
        beta a hroot hresidue ha haderiv
  have haK : IsIntegral K a :=
    isIntegral_of_constant_cleared_minpoly
      a T hprimitive hTmap t ht
  exact exists_algebraMap_eq_of_isIntegral_of_isAlgClosed a haK
end GaoLemma24
end BCHKSGaoPositiveCharacteristicCore6400
end ProximityPrize.SubmissionLower
