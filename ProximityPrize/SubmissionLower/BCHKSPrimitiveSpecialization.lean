import ProximityPrize.SubmissionLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionLower.BCHKSParameters
import ProximityPrize.SubmissionLower.BCHKSConcreteGS
import ProximityPrize.SubmissionLower.BCHKSResultantDegree

namespace ProximityPrize.SubmissionLower

open Polynomial

/-- A full-`Y`-degree divisor of a primitive polynomial has only a unit
cofactor.  This is the Gauss-content step needed by the selected Hensel setup;
no ring-level separability of the specialized trivariate factor is required. -/
theorem isUnit_cofactor_of_isPrimitive_of_full_natDegree
    {A : Type} [CommSemiring A] [NoZeroDivisors A] [Nontrivial A]
    {R H q : A[X]}
    (hprim : R.IsPrimitive) (hH : H ≠ 0)
    (hfac : R = H * q) (hdeg : H.natDegree = R.natDegree) :
    IsUnit q := by
  have hR : R ≠ 0 := hprim.ne_zero
  have hq : q ≠ 0 := by
    intro hq0
    apply hR
    rw [hfac, hq0, mul_zero]
  have hqdeg : q.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hH hq
    rw [← hfac] at hmul
    omega
  let a : A := q.coeff 0
  have hqC : q = Polynomial.C a :=
    Polynomial.eq_C_of_natDegree_le_zero hqdeg.le
  have hCdvd : Polynomial.C a ∣ R := by
    refine ⟨H, ?_⟩
    calc
      R = H * q := hfac
      _ = H * Polynomial.C a := by rw [hqC]
      _ = Polynomial.C a * H := mul_comm _ _
  have hunitCoeff : IsUnit a :=
    (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprim) _ hCdvd
  rw [hqC, Polynomial.isUnit_C]
  exact hunitCoeff

/-- Divisibility form, producing the cofactor and proving it is a unit. -/
theorem exists_unit_cofactor_of_isPrimitive_dvd_full_natDegree
    {A : Type} [CommSemiring A] [NoZeroDivisors A] [Nontrivial A]
    {R H : A[X]}
    (hprim : R.IsPrimitive) (hH : H ≠ 0) (hdvd : H ∣ R)
    (hdeg : H.natDegree = R.natDegree) :
    ∃ q : A[X], R = H * q ∧ IsUnit q := by
  obtain ⟨q, rfl⟩ := hdvd
  refine ⟨q, rfl, ?_⟩
  apply isUnit_cofactor_of_isPrimitive_of_full_natDegree
    (R := H * q) (H := H) (q := q) hprim hH rfl
  exact hdeg

/-- In particular a full-degree normalized irreducible factor is associated to
its primitive ambient polynomial.  Irreducibility is recorded because this is
the exact Hensel-call interface, although the content argument itself only
needs nonzeroness. -/
theorem associated_of_isPrimitive_irreducible_dvd_full_natDegree
    {A : Type} [CommSemiring A] [NoZeroDivisors A] [Nontrivial A]
    {R H : A[X]}
    (hprim : R.IsPrimitive) (hirr : Irreducible H) (hdvd : H ∣ R)
    (hdeg : H.natDegree = R.natDegree) : Associated H R := by
  obtain ⟨q, hfac, hq⟩ :=
    exists_unit_cofactor_of_isPrimitive_dvd_full_natDegree
      hprim hirr.ne_zero hdvd hdeg
  obtain ⟨u, hu⟩ := hq
  refine ⟨u, ?_⟩
  rw [hu]
  exact hfac.symm


/-- The exact missing elimination-theory interface for primitive
specialization.  An obstruction is a nonzero polynomial in the specialization
parameter whose nonvanishing guarantees that content does not appear. -/
structure PrimitiveSpecializationObstruction
    (F : Type) [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) where
  polynomial : Polynomial F
  ne_zero : polynomial ≠ 0
  cert : ∀ x : F, Polynomial.eval x polynomial ≠ 0 →
    (triSpecializeX R x).IsPrimitive

/-- Effective single-factor obstruction data: a concrete nonzero polynomial
whose nonvanishing certifies primitive specialization. -/
structure EffectivePrimitiveObstruction
    (F : Type) [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) where
  obstruction : Polynomial F
  ne : obstruction ≠ 0
  property : ∀ x : F, Polynomial.eval x obstruction ≠ 0 →
    (triSpecializeX R x).IsPrimitive

/-- Once such obstructions are constructed with the aggregate degree bound,
one point makes every selected factor primitive. -/
theorem exists_simultaneously_primitive_of_obstructions
    {ρ : Type} [DecidableEq ρ]
    (T : Finset ρ)
    (R : ρ → Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (o : ∀ r, PrimitiveSpecializationObstruction
      ProximityPrize.Benchmark.IRSProfile.Field (R r))
    (hdeg : (∑ r ∈ T, (o r).polynomial.natDegree) ≤ bchksBadBudget) :
    ∃ x₀ : ProximityPrize.Benchmark.IRSProfile.Field,
      ∀ r ∈ T, (triSpecializeX (R r) x₀).IsPrimitive := by
  classical
  let P : Polynomial ProximityPrize.Benchmark.IRSProfile.Field :=
    ∏ r ∈ T, (o r).polynomial
  have hP : P ≠ 0 := by
    change (∏ r ∈ T, (o r).polynomial) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro r hr
    exact (o r).ne_zero
  have hPdeg : P.natDegree <
      Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
    exact (Polynomial.natDegree_prod_le T (fun r => (o r).polynomial)).trans_lt
      (hdeg.trans_lt bchksBadBudget_lt_field)
  by_contra hnone
  push Not at hnone
  have hPeval : ∀ x : ProximityPrize.Benchmark.IRSProfile.Field,
      Polynomial.eval x P = 0 := by
    intro x
    obtain ⟨r, hr, hbad⟩ := hnone x
    have heval : Polynomial.eval x (o r).polynomial = 0 := by
      by_contra hne
      exact hbad ((o r).cert x hne)
    change Polynomial.eval x (∏ r ∈ T, (o r).polynomial) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hr heval
  exact hP (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    P Function.injective_id hPeval hPdeg)

/-- Thus the sole remaining specialization lemma is to construct, for each
positive normalized irreducible factor `R`, a
`PrimitiveSpecializationObstruction F R` and prove the sum of its degrees is at
most `bchksBadBudget`.  Algebraically this is an elimination/resultant witness
for the coefficient polynomials of `R` in `Y`: its nonvanishing must rule out a
common nonunit factor in `F[Z]` after `X = x₀`. -/
def PrimitiveSpecializationCapGoal : Prop :=
  ∀ (Q : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field))) (hQ : Q ≠ 0),
    let T := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R => 0 < R.natDegree)
    ∃ o : ∀ R, PrimitiveSpecializationObstruction
      ProximityPrize.Benchmark.IRSProfile.Field R,
      (∑ R ∈ T, (o R).polynomial.natDegree) ≤ bchksBadBudget


/-- The ideal generated by the `Y`-coefficients, after swapping each coefficient
from `F[Z][X]` to `F[X][Z]`. -/
noncomputable def swappedCoefficientIdeal {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) :
    Ideal (Polynomial (Polynomial F)) :=
  Ideal.span (Set.range fun j : ℕ =>
    Polynomial.Bivariate.swap (R.coeff j))

/-- A cleared Bezout certificate: the swapped coefficient ideal contains a
nonzero polynomial depending only on `X`. -/
structure ClearedPrimitiveCertificate
    (F : Type) [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) where
  obstruction : Polynomial F
  obstruction_ne_zero : obstruction ≠ 0
  cleared_identity : Polynomial.C obstruction ∈ swappedCoefficientIdeal R

private theorem map_swap_coeff_eq_specialized_coeff
    {F : Type} [Field F]
    (c : Polynomial (Polynomial F)) (x : F) :
    Polynomial.map (Polynomial.evalRingHom x)
        (Polynomial.Bivariate.swap c) =
      Polynomial.eval (Polynomial.C x) c := by
  rw [← Polynomial.Bivariate.evalX_eq_map]
  exact (Polynomial.Bivariate.evalY_eq_evalX_swap x c).symm

/-- A cleared Bezout certificate really is a primitive-specialization
obstruction. -/
theorem ClearedPrimitiveCertificate.isPrimitive_of_eval_ne_zero
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))}
    (w : ClearedPrimitiveCertificate F R) (x : F)
    (hx : Polynomial.eval x w.obstruction ≠ 0) :
    (triSpecializeX R x).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro a ha
  have hacoeff : ∀ j : ℕ, a ∣ (triSpecializeX R x).coeff j :=
    (Polynomial.C_dvd_iff_dvd_coeff a (triSpecializeX R x)).mp ha
  let ψ : Polynomial (Polynomial F) →+* Polynomial F :=
    Polynomial.mapRingHom (Polynomial.evalRingHom x)
  let J : Ideal (Polynomial F) := Ideal.span {a}
  have hmap_le : Ideal.map ψ (swappedCoefficientIdeal R) ≤ J := by
    rw [swappedCoefficientIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    intro y hy
    rcases hy with ⟨c, ⟨j, rfl⟩, rfl⟩
    change ψ (Polynomial.Bivariate.swap (R.coeff j)) ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton]
    change a ∣ Polynomial.map (Polynomial.evalRingHom x)
      (Polynomial.Bivariate.swap (R.coeff j))
    rw [map_swap_coeff_eq_specialized_coeff]
    simpa [triSpecializeX] using hacoeff j
  have hmemMap : ψ (Polynomial.C w.obstruction) ∈
      Ideal.map ψ (swappedCoefficientIdeal R) :=
    Ideal.mem_map_of_mem ψ w.cleared_identity
  have hmemJ : ψ (Polynomial.C w.obstruction) ∈ J := hmap_le hmemMap
  have heq : ψ (Polynomial.C w.obstruction) =
      Polynomial.C (Polynomial.eval x w.obstruction) := by
    simp [ψ]
  rw [heq, Ideal.mem_span_singleton] at hmemJ
  have hunitRhs : IsUnit (Polynomial.C (Polynomial.eval x w.obstruction)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx)
  have hadivOne : a ∣ 1 :=
    dvd_trans hmemJ (isUnit_iff_dvd_one.mp hunitRhs)
  exact isUnit_iff_dvd_one.mpr hadivOne



/-- A quantitative resultant certificate for primitivity.  The two bounded
`Z`-polynomials are viewed over `F[X]`; their fixed-degree resultant is the
obstruction.  Recording the resulting Bezout membership avoids exposing a
particular Sylvester-matrix implementation to downstream arguments. -/
structure PrimitiveObstruction
    (F : Type) [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (DZ DX : ℕ) where
  f : Polynomial (Polynomial F)
  h : Polynomial (Polynomial F)
  f_degreeZ : f.natDegree ≤ DZ
  h_degreeZ : h.natDegree ≤ DZ
  f_degreeX : Polynomial.Bivariate.degreeX f ≤ DX
  h_degreeX : Polynomial.Bivariate.degreeX h ≤ DX
  resultant_ne_zero : Polynomial.resultant f h ≠ 0
  cleared_identity : Polynomial.C (Polynomial.resultant f h) ∈
    swappedCoefficientIdeal R

/-- Build the quantitative package once the lambda-avoidance argument has
produced a coprime bounded pair and the standard resultant Bezout identity has
been placed in the coefficient ideal. -/
noncomputable def PrimitiveObstruction.of_isCoprime
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {DZ DX : ℕ}
    (f h : Polynomial (Polynomial F))
    (hfZ : f.natDegree ≤ DZ) (hhZ : h.natDegree ≤ DZ)
    (hfX : Polynomial.Bivariate.degreeX f ≤ DX)
    (hhX : Polynomial.Bivariate.degreeX h ≤ DX)
    (hc : IsCoprime f h)
    (hid : Polynomial.C (Polynomial.resultant f h) ∈
      swappedCoefficientIdeal R) : PrimitiveObstruction F R DZ DX where
  f := f
  h := h
  f_degreeZ := hfZ
  h_degreeZ := hhZ
  f_degreeX := hfX
  h_degreeX := hhX
  resultant_ne_zero := Polynomial.resultant_ne_zero f h hc
  cleared_identity := hid

/-- The fixed-degree resultant carried by a quantitative certificate. -/
noncomputable def PrimitiveObstruction.obstruction
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {DZ DX : ℕ}
    (w : PrimitiveObstruction F R DZ DX) : Polynomial F :=
  Polynomial.resultant w.f w.h

/-- Forgetting the quantitative data gives the coefficient-ideal certificate
used by the specialization argument. -/
noncomputable def PrimitiveObstruction.toCleared
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {DZ DX : ℕ}
    (w : PrimitiveObstruction F R DZ DX) :
    ClearedPrimitiveCertificate F R where
  obstruction := w.obstruction
  obstruction_ne_zero := w.resultant_ne_zero
  cleared_identity := w.cleared_identity

/-- Both inputs have `X`-degree at most `DX`, so the resultant obstruction has
`X`-degree at most `2 * DZ * DX`. -/
theorem PrimitiveObstruction.obstruction_natDegree_le
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {DZ DX : ℕ}
    (w : PrimitiveObstruction F R DZ DX) :
    w.obstruction.natDegree ≤ 2 * DZ * DX := by
  change (Polynomial.resultant w.f w.h).natDegree ≤ 2 * DZ * DX
  refine (bivariate_resultant_natDegree_le w.f w.h
    w.f.natDegree w.h.natDegree).trans ?_
  calc
    w.h.natDegree * Polynomial.Bivariate.degreeX w.f +
        w.f.natDegree * Polynomial.Bivariate.degreeX w.h ≤ DZ * DX + DZ * DX :=
      Nat.add_le_add
        (Nat.mul_le_mul w.h_degreeZ w.f_degreeX)
        (Nat.mul_le_mul w.f_degreeZ w.h_degreeX)
    _ = 2 * DZ * DX := by simp [two_mul, Nat.add_mul]

/-- Nonvanishing of the quantitative resultant obstruction guarantees that no
nonunit content appears after specializing `X`. -/
theorem PrimitiveObstruction.isPrimitive_of_eval_ne_zero
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {DZ DX : ℕ}
    (w : PrimitiveObstruction F R DZ DX) (x : F)
    (hx : Polynomial.eval x w.obstruction ≠ 0) :
    (triSpecializeX R x).IsPrimitive :=
  w.toCleared.isPrimitive_of_eval_ne_zero x hx

/-- Localization clears the Bezout denominators automatically.  Thus proving
that the coefficient ideal becomes the unit ideal over `F(X)[Z]` constructs
an actual nonzero polynomial obstruction in `F[X]`. -/
theorem exists_clearedPrimitiveCertificate_of_localized_span_eq_top
    {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (htop : Ideal.map
      (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))
      (swappedCoefficientIdeal R) = ⊤) :
    Nonempty (ClearedPrimitiveCertificate F R) := by
  let M : Submonoid F[X] := nonZeroDivisors F[X]
  let B := Polynomial (Polynomial F)
  let K := RatFunc F
  let BK := Polynomial K
  letI : Algebra B BK :=
    (Polynomial.mapRingHom (algebraMap (Polynomial F) K)).toAlgebra
  letI : IsLocalization (M.map Polynomial.C) BK :=
    Polynomial.isLocalization M K
  have hone : algebraMap B BK (1 : B) ∈
      Ideal.map (algebraMap B BK) (swappedCoefficientIdeal R) := by
    have hmap : Ideal.map (algebraMap B BK) (swappedCoefficientIdeal R) = ⊤ := by
      simpa [B, BK, K] using htop
    rw [hmap]
    simp
  obtain ⟨m, hmM, hmI⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (M.map Polynomial.C) BK (swappedCoefficientIdeal R) 1).mp hone
  rcases hmM with ⟨p, hpM, hmp⟩
  have hp0 : p ≠ 0 := by
    intro hp
    subst p
    simpa [M] using hpM
  refine ⟨ClearedPrimitiveCertificate.mk p hp0 ?_⟩
  rw [hmp]
  simpa using hmI

/-- Single-factor primitive specialization from the localized Bezout span,
with an explicit degree hypothesis only for choosing a base-field point. -/
theorem exists_primitive_specialization_of_localized_span
    (R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (htop : Ideal.map
      (Polynomial.mapRingHom
        (algebraMap ProximityPrize.Benchmark.IRSProfile.Field[X]
          (RatFunc ProximityPrize.Benchmark.IRSProfile.Field)))
      (swappedCoefficientIdeal R) = ⊤)
    (hdegree : ∀ w : ClearedPrimitiveCertificate
        ProximityPrize.Benchmark.IRSProfile.Field R,
      w.obstruction.natDegree <
        Fintype.card ProximityPrize.Benchmark.IRSProfile.Field) :
    ∃ x₀ : ProximityPrize.Benchmark.IRSProfile.Field,
      (triSpecializeX R x₀).IsPrimitive := by
  obtain ⟨w⟩ := exists_clearedPrimitiveCertificate_of_localized_span_eq_top R htop
  by_contra h
  push Not at h
  have hz : ∀ x : ProximityPrize.Benchmark.IRSProfile.Field,
      Polynomial.eval x w.obstruction = 0 := by
    intro x
    by_contra hx
    exact h x (w.isPrimitive_of_eval_ne_zero x hx)
  exact w.obstruction_ne_zero
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      w.obstruction Function.injective_id hz (hdegree w))


/-- Over a principal ideal domain, the coefficients of a primitive polynomial
actually generate the unit ideal (not merely have gcd one). -/
theorem span_range_coeff_eq_top_of_isPrimitive
    {A : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {P : Polynomial A} (hP : P.IsPrimitive) :
    Ideal.span (Set.range P.coeff) = ⊤ := by
  let I : Ideal A := Ideal.span (Set.range P.coeff)
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have haIdeal : I = Ideal.span {a} := by
    simpa [Ideal.span_singleton_eq_span_singleton] using ha
  have hadiv : ∀ i : ℕ, a ∣ P.coeff i := by
    intro i
    rw [← Ideal.mem_span_singleton]
    rw [← haIdeal]
    exact Ideal.subset_span (Set.mem_range_self i)
  have haunit : IsUnit a :=
    (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hP) a
      ((Polynomial.C_dvd_iff_dvd_coeff a P).mpr hadiv)
  change I = ⊤
  rw [haIdeal, Ideal.span_singleton_eq_top]
  exact haunit


noncomputable def localizedSwapY {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial (RatFunc F)) :=
  (R.map Polynomial.Bivariate.swap.toRingHom).map
    (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

/-- Irreducibility after the coefficient-ring localization supplies precisely
 the localized-span hypothesis used by denominator clearing. -/
theorem localized_span_eq_top_of_irreducible
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : Irreducible (localizedSwapY R))
    (hpos : 0 < (localizedSwapY R).natDegree) :
    Ideal.map
      (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))
      (swappedCoefficientIdeal R) = ⊤ := by
  have hp : (localizedSwapY R).IsPrimitive := hR.isPrimitive hpos.ne'
  have hs := span_range_coeff_eq_top_of_isPrimitive hp
  rw [swappedCoefficientIdeal, Ideal.map_span]
  rw [← hs]
  congr 1
  ext q
  simp [localizedSwapY]

/-- Fully feeds localized irreducibility into the cleared-certificate
construction. -/
theorem exists_clearedPrimitiveCertificate_of_localized_irreducible
    {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (hR : Irreducible (localizedSwapY R))
    (hpos : 0 < (localizedSwapY R).natDegree) :
    Nonempty (ClearedPrimitiveCertificate F R) :=
  exists_clearedPrimitiveCertificate_of_localized_span_eq_top R
    (localized_span_eq_top_of_irreducible hR hpos)




/-- Positive outer degree prevents an irreducible polynomial from meeting a
coefficient-localization denominator; hence coefficient localization preserves
irreducibility. -/
theorem irreducible_map_of_isLocalization_of_natDegree_pos
    {A S : Type} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing S] [IsDomain S]
    (M : Submonoid A) [Algebra A S] [IsLocalization M S]
    (hM0 : ∀ m : M, (m : A) ≠ 0)
    {P : Polynomial A} (hP : Irreducible P) (hdeg : 0 < P.natDegree) :
    Irreducible (P.map (algebraMap A S)) := by
  let MY : Submonoid (Polynomial A) := M.map Polynomial.C
  letI : Algebra (Polynomial A) (Polynomial S) :=
    (Polynomial.mapRingHom (algebraMap A S)).toAlgebra
  letI : IsLocalization MY (Polynomial S) := Polynomial.isLocalization M S
  have hP0 : P ≠ 0 := hP.ne_zero
  have hprime : (Ideal.span {P} : Ideal (Polynomial A)).IsPrime :=
    (Ideal.span_singleton_prime hP0).mpr hP.prime
  letI : (Ideal.span {P} : Ideal (Polynomial A)).IsPrime := hprime
  have hdisj : Disjoint (MY : Set (Polynomial A))
      (Ideal.span {P} : Set (Polynomial A)) := by
    rw [Set.disjoint_left]
    intro d hdM hdI
    change d ∈ Ideal.span {P} at hdI
    rw [Ideal.mem_span_singleton] at hdI
    rcases hdM with ⟨m, hm, rfl⟩
    have hCm0 : Polynomial.C (m : A) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (hM0 ⟨m, hm⟩)
    have hle := Polynomial.natDegree_le_of_dvd hdI hCm0
    have : P.natDegree ≤ 0 := by simpa using hle
    omega
  have hmapPrime : (Ideal.map (algebraMap (Polynomial A) (Polynomial S))
      (Ideal.span {P})).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint MY (Polynomial S)
      (Ideal.span {P}) hprime hdisj
  have heq : Ideal.map (algebraMap (Polynomial A) (Polynomial S))
      (Ideal.span {P}) = Ideal.span {P.map (algebraMap A S)} := by
    rw [Ideal.map_span]
    congr 1
    ext q
    simp
  have hMle : M ≤ nonZeroDivisors A := by
    intro m hm
    simpa using hM0 ⟨m, hm⟩
  have hmap0 : P.map (algebraMap A S) ≠ 0 :=
    (Polynomial.map_eq_zero_iff (IsLocalization.injective S hMle)).not.mpr hP0
  apply Prime.irreducible
  rw [← Ideal.span_singleton_prime hmap0]
  rw [← heq]
  exact hmapPrime


/-- The raw bridge: irreducibility and positive `Y`-degree survive swapping
`X,Z` in the coefficient ring and then localizing `F[X]` to `F(X)`. -/
theorem localizedSwapY_irreducible_of_irreducible
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : Irreducible R) (hpos : 0 < R.natDegree) :
    Irreducible (localizedSwapY R) := by
  let A := Polynomial (Polynomial F)
  let K := RatFunc F
  let S := Polynomial K
  let M0 : Submonoid (Polynomial F) := nonZeroDivisors (Polynomial F)
  let M : Submonoid A := M0.map Polynomial.C
  letI : Algebra A S :=
    (Polynomial.mapRingHom (algebraMap (Polynomial F) K)).toAlgebra
  letI : IsLocalization M S := Polynomial.isLocalization M0 K
  let swapped : Polynomial A := R.map Polynomial.Bivariate.swap.toRingHom
  have hirr : Irreducible swapped := by
    exact hR.map (Polynomial.mapEquiv Polynomial.Bivariate.swap.toRingEquiv)
  have hdeg : 0 < swapped.natDegree := by
    have heq : swapped.natDegree = R.natDegree := by
      exact Polynomial.natDegree_map_eq_of_injective
        Polynomial.Bivariate.swap.injective R
    omega
  have hM0 : ∀ m : M, (m : A) ≠ 0 := by
    intro m
    rcases m.property with ⟨p, hp, hpm⟩
    have hp0 : p ≠ 0 := by simpa [M0] using hp
    rw [← hpm]
    exact Polynomial.C_ne_zero.mpr hp0
  have hi := irreducible_map_of_isLocalization_of_natDegree_pos
    (S := S) M hM0 hirr hdeg
  simpa [localizedSwapY, swapped, A, S, K] using hi

/-- Raw irreducibility now feeds all the way into denominator clearing. -/
theorem exists_clearedPrimitiveCertificate_of_irreducible
    {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (hR : Irreducible R) (hpos : 0 < R.natDegree) :
    Nonempty (ClearedPrimitiveCertificate F R) := by
  have hi := localizedSwapY_irreducible_of_irreducible hR hpos
  have hinj : Function.Injective
      (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) :=
    Polynomial.map_injective _ (IsFractionRing.injective F[X] (RatFunc F))
  have hp : 0 < (localizedSwapY R).natDegree := by
    rw [localizedSwapY,
      Polynomial.natDegree_map_eq_of_injective hinj]
    have heq :
        (R.map Polynomial.Bivariate.swap.toRingEquiv.toRingHom).natDegree =
          R.natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        Polynomial.Bivariate.swap.toRingEquiv.injective R
    omega
  exact exists_clearedPrimitiveCertificate_of_localized_irreducible R hi hp


/-- Determinants of polynomial matrices have the expected row-count times
entry-degree bound.  This is the quantitative core used by a minor
obstruction. -/
theorem natDegree_det_le_card_mul
    {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial F)) (D : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ D) :
    A.det.natDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le Finset.univ
    (fun i => A (σ i) i)).trans ?_
  calc
    (∑ i, (A (σ i) i).natDegree) ≤ ∑ _i : ι, D := by
      exact Finset.sum_le_sum fun i hi => hA (σ i) i
    _ = Fintype.card ι * D := by simp

/-- A nonzero square minor with at most `2*DZ` rows and entry `X`-degrees at
most `DX` is a single-factor obstruction of degree at most `2*DZ*DX`. -/
theorem squareMinor_obstruction_degree
    {F : Type} [Field F] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Polynomial F))
    (hN : N ≤ 2 * BCHKSConcreteGS.DZ)
    (hA : ∀ i j, (A i j).natDegree ≤ BCHKSConcreteGS.DX) :
    A.det.natDegree ≤ 2 * BCHKSConcreteGS.DZ * BCHKSConcreteGS.DX := by
  refine (natDegree_det_le_card_mul A BCHKSConcreteGS.DX hA).trans ?_
  simp only [Fintype.card_fin]
  exact Nat.mul_le_mul_right BCHKSConcreteGS.DX hN

/-- Numerically the determinant obstruction is far smaller than the concrete
base field. -/
theorem squareMinor_obstruction_lt_field
    {N : ℕ}
    (A : Matrix (Fin N) (Fin N)
      (Polynomial ProximityPrize.Benchmark.IRSProfile.Field))
    (hN : N ≤ 2 * BCHKSConcreteGS.DZ)
    (hA : ∀ i j, (A i j).natDegree ≤ BCHKSConcreteGS.DX) :
    A.det.natDegree <
      Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
  refine (squareMinor_obstruction_degree A hN hA).trans_lt ?_
  norm_num [BCHKSConcreteGS.DX, BCHKSConcreteGS.DZ, ProximityPrize.Benchmark.IRSProfile.Field]

/-- Consequently every nonzero such minor has a concrete evaluation point
where it stays nonzero. -/
theorem exists_eval_det_ne_zero_of_squareMinor
    {N : ℕ}
    (A : Matrix (Fin N) (Fin N)
      (Polynomial ProximityPrize.Benchmark.IRSProfile.Field))
    (hdet : A.det ≠ 0) (hN : N ≤ 2 * BCHKSConcreteGS.DZ)
    (hA : ∀ i j, (A i j).natDegree ≤ BCHKSConcreteGS.DX) :
    ∃ x : ProximityPrize.Benchmark.IRSProfile.Field,
      Polynomial.eval x A.det ≠ 0 := by
  by_contra h
  push Not at h
  exact hdet (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    A.det Function.injective_id h
      (squareMinor_obstruction_lt_field A hN hA))


/-- Abstract output of the completed-column/adjugate construction.  The matrix
is the completion of selected shifted coefficient columns; `cleared_identity`
is the polynomial identity obtained from `M * adjugate M = det(M)`. -/
structure CompletedColumnCertificate
    (F : Type) [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (N : ℕ) where
  completion : Matrix (Fin N) (Fin N) (Polynomial F)
  size_le : N ≤ 2 * BCHKSConcreteGS.DZ
  entry_degree_le : ∀ i j,
    (completion i j).natDegree ≤ BCHKSConcreteGS.DX
  det_ne_zero : completion.det ≠ 0
  cleared_identity : Polynomial.C completion.det ∈ swappedCoefficientIdeal R

/-- A completed-column certificate is a cleared primitive certificate, with
its obstruction chosen to be the pivot determinant. -/
noncomputable def CompletedColumnCertificate.toCleared
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {N : ℕ}
    (w : CompletedColumnCertificate F R N) :
    ClearedPrimitiveCertificate F R where
  obstruction := w.completion.det
  obstruction_ne_zero := w.det_ne_zero
  cleared_identity := w.cleared_identity

/-- The completed-column determinant has the promised effective degree. -/
theorem CompletedColumnCertificate.det_natDegree_le
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {N : ℕ}
    (w : CompletedColumnCertificate F R N) :
    w.completion.det.natDegree ≤
      2 * BCHKSConcreteGS.DZ * BCHKSConcreteGS.DX :=
  squareMinor_obstruction_degree w.completion w.size_le w.entry_degree_le

/-- Off the determinant hypersurface, the completed-column identity makes the
specialized polynomial primitive. -/
theorem CompletedColumnCertificate.isPrimitive_of_det_eval_ne_zero
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))} {N : ℕ}
    (w : CompletedColumnCertificate F R N) (x : F)
    (hx : Polynomial.eval x w.completion.det ≠ 0) :
    (triSpecializeX R x).IsPrimitive :=
  w.toCleared.isPrimitive_of_eval_ne_zero x hx

/-- For the concrete field, every completed-column certificate therefore
produces a good primitive specialization. -/
theorem CompletedColumnCertificate.exists_primitive_specialization
    {R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field))} {N : ℕ}
    (w : CompletedColumnCertificate
      ProximityPrize.Benchmark.IRSProfile.Field R N) :
    ∃ x : ProximityPrize.Benchmark.IRSProfile.Field,
      (triSpecializeX R x).IsPrimitive := by
  obtain ⟨x, hx⟩ := exists_eval_det_ne_zero_of_squareMinor
    w.completion w.det_ne_zero w.size_le w.entry_degree_le
  exact ⟨x, w.isPrimitive_of_det_eval_ne_zero x hx⟩


/-- Regard a bounded coefficient vector as a polynomial. -/
noncomputable def vectorPolynomial {F : Type} [Field F] {N : ℕ}
    (v : Fin N → Polynomial F) : Polynomial (Polynomial F) :=
  ∑ i : Fin N, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)

noncomputable def matrixColumnPolynomial {F : Type} [Field F] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (Polynomial F)) (j : Fin N) :
    Polynomial (Polynomial F) := vectorPolynomial (fun i => M i j)

/-- Vectorization intertwines matrix-vector multiplication with polynomial
linear combinations of columns. -/
theorem vectorPolynomial_mulVec {F : Type} [Field F] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (Polynomial F))
    (u : Fin N → Polynomial F) :
    vectorPolynomial (M.mulVec u) =
      ∑ j : Fin N, Polynomial.C (u j) * matrixColumnPolynomial M j := by
  classical
  simp only [vectorPolynomial, matrixColumnPolynomial, Matrix.mulVec,
    dotProduct, map_sum, map_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The adjugate column gives the determinant times the constant vector after
vectorization. -/
theorem vectorPolynomial_mulVec_adjugate_zero {F : Type} [Field F] {N : ℕ}
    [NeZero N]
    (M : Matrix (Fin N) (Fin N) (Polynomial F)) :
    vectorPolynomial (M.mulVec (fun j => M.adjugate j 0)) =
      Polynomial.C M.det := by
  classical
  have hmul := Matrix.mul_adjugate M
  have hv : M.mulVec (fun j => M.adjugate j 0) =
      fun i => if i = 0 then M.det else 0 := by
    funext i
    have hij := congrArg (fun A => A i (0 : Fin N)) hmul
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      smul_eq_mul] using hij
  rw [hv]
  rw [vectorPolynomial, Finset.sum_eq_single (0 : Fin N)]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

/-- An adjugate completion whose genuine columns lie in the coefficient ideal
and whose artificial-column cofactors vanish yields the cleared identity. -/
theorem cleared_identity_of_adjugate_completion
    {F : Type} [Field F] {N : ℕ} [NeZero N]
    {R : Polynomial (Polynomial (Polynomial F))}
    (M : Matrix (Fin N) (Fin N) (Polynomial F))
    (genuine : Finset (Fin N))
    (hcol : ∀ j ∈ genuine,
      matrixColumnPolynomial M j ∈ swappedCoefficientIdeal R)
    (hzero : ∀ j ∉ genuine, M.adjugate j 0 = 0) :
    Polynomial.C M.det ∈ swappedCoefficientIdeal R := by
  rw [← vectorPolynomial_mulVec_adjugate_zero M,
    vectorPolynomial_mulVec]
  apply Ideal.sum_mem
  intro j hj
  by_cases hgj : j ∈ genuine
  · exact Ideal.mul_mem_left _ _ (hcol j hgj)
  · rw [hzero j hgj, map_zero, zero_mul]
    exact (swappedCoefficientIdeal R).zero_mem

end ProximityPrize.SubmissionLower
