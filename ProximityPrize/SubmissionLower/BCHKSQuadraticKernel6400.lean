import ProximityPrize.SubmissionLower.BCHKSQuadraticSquareSpecialization6400
import ProximityPrize.SubmissionLower.BCHKSSeparableFactors

namespace ProximityPrize.SubmissionLower
namespace BCHKSQuadraticKernel6400

open Polynomial
open BCHKSQuadraticSquareSpecialization6400
open BCHKSQuadraticBranchAlgebra6400

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
The parity decomposition needed by the quadratic discriminant route.  The
construction is deliberately stated for an arbitrary unique factorization
monoid: it avoids choosing an ordering of normalized factors and absorbs the
unit part into the squarefree kernel.
-/

/-- Every nonzero element of a UFD is exactly a square times a squarefree
element.  In contrast to an association-only factorization, the unit is
absorbed into the squarefree factor, so this statement can be specialized by
a ring homomorphism without an untracked scalar. -/
theorem exists_sq_mul_squarefree
    {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    (a : R) (ha : a ≠ 0) :
    ∃ b s : R, Squarefree s ∧ a = b ^ 2 * s := by
  induction a using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (ha rfl).elim
  | unit u hu =>
      exact ⟨1, u, hu.squarefree, by simp⟩
  | mul z p hz hp ih =>
      obtain ⟨b, s, hs, hzs⟩ := ih hz
      by_cases hps : p ∣ s
      · obtain ⟨t, rfl⟩ := hps
        refine ⟨p * b, t, hs.of_mul_right, ?_⟩
        rw [hzs]
        simp only [pow_two]
        ac_rfl
      · refine ⟨b, p * s, ?_, ?_⟩
        · exact squarefree_mul_iff.mpr
            ⟨hp.isRelPrime_iff_not_dvd.mpr hps, hp.squarefree, hs⟩
        · rw [hzs]
          ac_rfl

/-- The squarefree kernel divides the original element. -/
theorem exists_sq_mul_squarefree_dvd
    {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    (a : R) (ha : a ≠ 0) :
    ∃ b s : R, Squarefree s ∧ a = b ^ 2 * s ∧ s ∣ a := by
  obtain ⟨b, s, hs, h⟩ := exists_sq_mul_squarefree a ha
  exact ⟨b, s, hs, h, ⟨b ^ 2, by simpa [mul_comm] using h⟩⟩

/-- Polynomial degree control for the exact parity kernel. -/
theorem exists_polynomial_sq_mul_squarefree_natDegree_le
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid (Polynomial R)]
    (a : Polynomial R) (ha : a ≠ 0) :
    ∃ b s : Polynomial R,
      Squarefree s ∧ a = b ^ 2 * s ∧ s.natDegree ≤ a.natDegree := by
  obtain ⟨b, s, hs, h, hsd⟩ := exists_sq_mul_squarefree_dvd a ha
  exact ⟨b, s, hs, h, Polynomial.natDegree_le_of_dvd hsd ha⟩

/-- Gauss transfer for squarefreeness.  Squarefreeness need not survive an
arbitrary injective map, but it does survive passage from a primitive
polynomial over a GCD domain to its fraction field. -/
theorem Polynomial.IsPrimitive.squarefree_map_fraction
    {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [UniqueFactorizationMonoid (Polynomial R)]
    (P : Polynomial R) (hprim : P.IsPrimitive) (hsq : Squarefree P) :
    Squarefree (P.map (algebraMap R K)) := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hprim.ne_zero rfl).elim
  | unit u hu =>
      exact (hu.map (Polynomial.mapRingHom (algebraMap R K))).squarefree
  | mul z p hz hp ih =>
      have hpDvd : p ∣ p * z := dvd_mul_right p z
      have hzDvd : z ∣ p * z := dvd_mul_left z p
      have hpprim : p.IsPrimitive := Polynomial.isPrimitive_of_dvd hprim hpDvd
      have hzprim : z.IsPrimitive := Polynomial.isPrimitive_of_dvd hprim hzDvd
      have hparts := squarefree_mul_iff.mp hsq
      have hmapP : Irreducible (p.map (algebraMap R K)) :=
        hpprim.irreducible_iff_irreducible_map_fraction_map.mp hp
      have hmapZ : Squarefree (z.map (algebraMap R K)) := ih hzprim hparts.2.2
      rw [Polynomial.map_mul]
      exact squarefree_mul_iff.mpr ⟨
        hmapP.isRelPrime_iff_not_dvd.mpr (fun hdiv =>
          (hp.isRelPrime_iff_not_dvd.mp hparts.1)
            ((hpprim.dvd_iff_fraction_map_dvd_fraction_map K).mpr hdiv)),
        hmapP.squarefree, hmapZ⟩

private theorem bivariate_degreeX_C_eq_natDegree
    {F : Type*} [Semiring F] (p : Polynomial F) :
    Polynomial.Bivariate.degreeX
        (Polynomial.C p : Polynomial (Polynomial F)) = p.natDegree := by
  unfold Polynomial.Bivariate.degreeX
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Polynomial.support_C hp]
    simp

/-- An irreducible genuine quadratic has nonzero discriminant away from
characteristic two.  This integral proof avoids adjoining a root or clearing
fraction-field denominators: if the discriminant vanished, the irreducible
quadratic would divide the square of its linear formal derivative and hence
the derivative itself. -/
theorem quadraticDiscriminant_ne_zero_of_irreducible
    {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid (Polynomial A)]
    (c a b : A) (htwo : (2 : A) ≠ 0)
    (hirr : Irreducible (quadratic c a b))
    (hdeg : (quadratic c a b).natDegree = 2) :
    quadraticDiscriminant c a b ≠ 0 := by
  let R : Polynomial A := quadratic c a b
  let L : Polynomial A := Polynomial.C (2 * c) * Polynomial.X + Polynomial.C a
  have hc : c ≠ 0 := by
    have htop : R.coeff 2 ≠ 0 := by
      rw [← hdeg]
      exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
    simpa [R, quadratic] using htop
  have hL0 : L ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun P : Polynomial A => P.coeff 1) hzero
    simp [L, htwo, hc] at hcoeff
  intro hdisc
  have hgeneral : Polynomial.C (4 * c) * quadratic c a b =
      (Polynomial.C (2 * c) * Polynomial.X + Polynomial.C a) ^ 2 -
        Polynomial.C (quadraticDiscriminant c a b) := by
    simp only [quadratic, quadraticDiscriminant, map_sub, map_mul, map_pow,
      map_ofNat]
    ring
  have hidentity : Polynomial.C (4 * c) * R = L ^ 2 := by
    dsimp [R, L]
    rw [hgeneral, hdisc]
    simp
  have hdivsq : R ∣ L ^ 2 := by
    refine ⟨Polynomial.C (4 * c), ?_⟩
    rw [← hidentity]
    ring
  have hdiv : R ∣ L := hirr.prime.dvd_of_dvd_pow hdivsq
  have hdegree : R.natDegree ≤ L.natDegree :=
    Polynomial.natDegree_le_of_dvd hdiv hL0
  have hLdegree : L.natDegree ≤ 1 := by
    dsimp [L]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simpa using Polynomial.natDegree_C_mul_le (2 * c) Polynomial.X
    · simp
  have hRdegree : R.natDegree = 2 := by simpa [R] using hdeg
  omega

/-- Coefficient reconstruction for an exact quadratic. -/
theorem eq_quadratic_coeffs_of_natDegree_eq_two
    {A : Type*} [CommRing A] (R : Polynomial A)
    (hdeg : R.natDegree = 2) :
    R = quadratic (R.coeff 2) (R.coeff 1) (R.coeff 0) := by
  ext n
  rcases n with _ | n
  · simp [quadratic]
  rcases n with _ | n
  · simp [quadratic]
  rcases n with _ | n
  · simp [quadratic]
  · have hzero : R.coeff (n + 3) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    simpa [quadratic, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hzero

/-- Benchmark-facing nonvanishing form, stated directly using the three
coefficients of an irreducible degree-two factor. -/
theorem coeff_quadraticDiscriminant_ne_zero_of_irreducible
    {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid (Polynomial A)]
    (R : Polynomial A) (htwo : (2 : A) ≠ 0)
    (hirr : Irreducible R) (hdeg : R.natDegree = 2) :
    quadraticDiscriminant (R.coeff 2) (R.coeff 1) (R.coeff 0) ≠ 0 := by
  have hshape := eq_quadratic_coeffs_of_natDegree_eq_two R hdeg
  apply quadraticDiscriminant_ne_zero_of_irreducible
    (R.coeff 2) (R.coeff 1) (R.coeff 0) htwo
  · rw [← hshape]
    exact hirr
  · rw [← hshape]
    exact hdeg

/-- A positive-`Y` irreducible trivariate factor has no identically-zero
coordinate slice.  If all of its `Y` coefficients vanished after `X = x`,
then the coefficient-ring factor `X-x` would divide the whole polynomial;
irreducibility would force outer `Y` degree zero. -/
theorem irreducible_map_evalRingHom_ne_zero
    {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (x : F)
    (hirr : Irreducible R) (hpos : 0 < R.natDegree) :
    R.map (Polynomial.evalRingHom (Polynomial.C x)) ≠ 0 := by
  let D : Polynomial (Polynomial F) :=
    Polynomial.X - Polynomial.C (Polynomial.C x)
  have hDdeg : D.natDegree = 1 := by
    simp [D]
  have hD0 : D ≠ 0 := by
    intro hzero
    rw [hzero] at hDdeg
    simp at hDdeg
  have hDnonunit : ¬ IsUnit D := by
    intro hunit
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  intro hzero
  have hCDdiv : Polynomial.C D ∣ R := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro j
    rw [Polynomial.dvd_iff_isRoot]
    change Polynomial.eval (Polynomial.C x) (R.coeff j) = 0
    have hcoeff := congrArg
      (fun Q : Polynomial (Polynomial F) => Q.coeff j) hzero
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
      Polynomial.coe_evalRingHom] using hcoeff
  obtain ⟨E, hRE⟩ := hCDdiv
  have hCDnonunit : ¬ IsUnit (Polynomial.C D :
      Polynomial (Polynomial (Polynomial F))) := by
    simpa [Polynomial.isUnit_C] using hDnonunit
  rcases hirr.isUnit_or_isUnit hRE with hCDunit | hEunit
  · exact hCDnonunit hCDunit
  · have hCD0 : (Polynomial.C D :
        Polynomial (Polynomial (Polynomial F))) ≠ 0 := by simp [hD0]
    have hE0 : E ≠ 0 := hEunit.ne_zero
    have hRdeg0 : R.natDegree = 0 := by
      rw [hRE, Polynomial.natDegree_mul hCD0 hE0,
        Polynomial.natDegree_C,
        Polynomial.natDegree_eq_zero_of_isUnit hEunit]
    omega

/-- Two roots on the same global quadratic branch agree as soon as the
specialized slice is nondegenerate.  The disjunction is sharp: `h ≠ 0`
handles a linear degree drop (`c = 0`), while `c ≠ 0` handles the double-root
case (`h = 0`). -/
theorem eq_of_quadratic_roots_same_sign_of_nondegenerate
    {A : Type*} [CommRing A] [IsDomain A]
    (c a b p u h : A) (htwo : (2 : A) ≠ 0)
    (hp : c * p ^ 2 + a * p + b = 0)
    (hu : c * u ^ 2 + a * u + b = 0)
    (hpsign : a + 2 * c * p = h)
    (husign : a + 2 * c * u = h)
    (hnondeg : h ≠ 0 ∨ c ≠ 0) :
    p = u := by
  rcases Classical.em (c = 0) with hc | hc
  · subst c
    have hh : h ≠ 0 := hnondeg.resolve_right (by simp)
    have hpsign' : a = h := by simpa using hpsign
    have ha : a ≠ 0 := by
      exact fun ha0 => hh (hpsign'.symm.trans ha0)
    apply mul_left_cancel₀ ha
    have heq : a * p = a * u := by
      linear_combination hp - hu
    exact heq
  · exact eq_of_quadratic_branch_sign_eq c a p u h htwo hc hpsign husign

/-- A global discriminant square specializes to one genuine sign bit for
each polynomial root.  In particular, the bit is not chosen independently
at the individual evaluation coordinates. -/
theorem specialized_quadratic_root_has_global_sign
    {F : Type*} [Field F]
    (c a b H : Polynomial (Polynomial F)) (z : F) (P : Polynomial F)
    (hdisc : quadraticDiscriminant c a b = H ^ 2)
    (hroot :
      c.map (Polynomial.evalRingHom z) * P ^ 2 +
          a.map (Polynomial.evalRingHom z) * P +
          b.map (Polynomial.evalRingHom z) = 0) :
    a.map (Polynomial.evalRingHom z) +
          2 * c.map (Polynomial.evalRingHom z) * P =
        H.map (Polynomial.evalRingHom z) ∨
      a.map (Polynomial.evalRingHom z) +
          2 * c.map (Polynomial.evalRingHom z) * P =
        -H.map (Polynomial.evalRingHom z) := by
  apply quadratic_root_has_global_sign
    (c.map (Polynomial.evalRingHom z))
    (a.map (Polynomial.evalRingHom z))
    (b.map (Polynomial.evalRingHom z)) P
    (H.map (Polynomial.evalRingHom z)) hroot
  have hmapped := congrArg
    (Polynomial.mapRingHom (Polynomial.evalRingHom z)) hdisc
  simpa [quadraticDiscriminant] using hmapped

/-- Substituting an affine received value into a quadratic preserves its
`Z+Y` support mass.  These are precisely the coefficient inequalities
inherited from `YZFactorCap` for `Y` indices `2,1,0`. -/
theorem quadratic_affine_substitution_natDegree_le
    {F : Type*} [Field F]
    (c a b U : Polynomial F) (d : ℕ)
    (hc : c.natDegree + 2 ≤ d)
    (ha : a.natDegree + 1 ≤ d)
    (hb : b.natDegree ≤ d)
    (hU : U.natDegree ≤ 1) :
    (c * U ^ 2 + a * U + b).natDegree ≤ d := by
  have hU2 : (U ^ 2).natDegree ≤ 2 := by
    exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hU)
  have hcu : (c * U ^ 2).natDegree ≤ d := by
    calc
      (c * U ^ 2).natDegree ≤ c.natDegree + (U ^ 2).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ d := by omega
  have hau : (a * U).natDegree ≤ d := by
    calc
      (a * U).natDegree ≤ a.natDegree + U.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ d := by omega
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le hcu hau)) hb)

/-- If a quadratic discriminant of `Z+Y` mass `d` is a square, its square
root has degree at most `d-1`.  This is the sharp degree needed for the
fixed-sign coordinate charge. -/
theorem quadratic_square_root_natDegree_add_one_le
    {F : Type*} [Field F]
    (c a b H : Polynomial F) (d : ℕ)
    (hd : 1 ≤ d)
    (hc : c.natDegree + 2 ≤ d)
    (ha : a.natDegree + 1 ≤ d)
    (hb : b.natDegree ≤ d)
    (hdisc : quadraticDiscriminant c a b = H ^ 2) :
    H.natDegree + 1 ≤ d := by
  have ha2 : (a ^ 2).natDegree ≤ 2 * (d - 1) := by
    calc
      (a ^ 2).natDegree ≤ 2 * a.natDegree := Polynomial.natDegree_pow_le
      _ ≤ 2 * (d - 1) := by omega
  have h4c : (4 * c).natDegree ≤ c.natDegree := by
    change (Polynomial.C (4 : F) * c).natDegree ≤ c.natDegree
    exact Polynomial.natDegree_C_mul_le _ _
  have hcb : (4 * c * b).natDegree ≤ 2 * (d - 1) := by
    calc
      (4 * c * b).natDegree ≤ (4 * c).natDegree + b.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ c.natDegree + b.natDegree := Nat.add_le_add_right h4c _
      _ ≤ 2 * (d - 1) := by omega
  have hDelta : (quadraticDiscriminant c a b).natDegree ≤ 2 * (d - 1) := by
    unfold quadraticDiscriminant
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le ha2 hcb)
  have hHdegree : 2 * H.natDegree ≤ 2 * (d - 1) := by
    have heq := congrArg Polynomial.natDegree hdisc
    rw [Polynomial.natDegree_pow] at heq
    omega
  omega

/-- Integral parity decomposition with the coefficient content separated from
the primitive `X`-dependent kernel.  This is the form needed for controlled
specialization: the only coefficient-only odd factor is `s`, while `S` is
primitive and remains squarefree over `F(Z)` by Gauss's lemma. -/
theorem exists_primitive_quadratic_parity_kernel
    {F : Type*} [Field F] [DecidableEq F]
    (Delta : Polynomial (Polynomial F))
    (hDelta : Delta ≠ 0) :
    ∃ B : Polynomial (Polynomial F), ∃ s : Polynomial F,
      ∃ S : Polynomial (Polynomial F),
        Squarefree s ∧ Squarefree S ∧ S.IsPrimitive ∧
        Delta = B ^ 2 * (Polynomial.C s * S) ∧
        S.natDegree ≤ Delta.natDegree ∧
        Polynomial.Bivariate.degreeX S ≤
          Polynomial.Bivariate.degreeX Delta ∧
        s.natDegree ≤ Polynomial.Bivariate.degreeX Delta := by
  have hc0 : Delta.content ≠ 0 := by
    intro hzero
    exact hDelta (Polynomial.content_eq_zero_iff.mp hzero)
  obtain ⟨bc, s, hs, hcontent, hsdeg⟩ :=
    exists_polynomial_sq_mul_squarefree_natDegree_le Delta.content hc0
  have hp0 : Delta.primPart ≠ 0 := Polynomial.primPart_ne_zero Delta
  obtain ⟨bp, S, hS, hprimPart, hSdeg⟩ :=
    exists_polynomial_sq_mul_squarefree_natDegree_le Delta.primPart hp0
  have hSdP : S ∣ Delta.primPart :=
    ⟨bp ^ 2, by simpa [mul_comm] using hprimPart⟩
  have hSprim : S.IsPrimitive :=
    Polynomial.isPrimitive_of_dvd Delta.isPrimitive_primPart hSdP
  have hS0 : S ≠ 0 := hS.ne_zero
  have hSx : Polynomial.Bivariate.degreeX S ≤
      Polynomial.Bivariate.degreeX Delta.primPart := by
    obtain ⟨T, hT⟩ := hSdP
    have hT0 : T ≠ 0 := by
      intro hzero
      apply hp0
      rw [hT, hzero, mul_zero]
    rw [hT, Polynomial.Bivariate.degreeX_mul S T hS0 hT0]
    omega
  have hdegDelta : Polynomial.Bivariate.degreeX Delta =
      Delta.content.natDegree +
        Polynomial.Bivariate.degreeX Delta.primPart := by
    calc
      Polynomial.Bivariate.degreeX Delta =
          Polynomial.Bivariate.degreeX
            (Polynomial.C Delta.content * Delta.primPart) :=
        congrArg Polynomial.Bivariate.degreeX
          Delta.eq_C_content_mul_primPart
      _ = Polynomial.Bivariate.degreeX (Polynomial.C Delta.content) +
          Polynomial.Bivariate.degreeX Delta.primPart :=
        Polynomial.Bivariate.degreeX_mul _ _ (by simpa using hc0) hp0
      _ = Delta.content.natDegree +
          Polynomial.Bivariate.degreeX Delta.primPart := by
        rw [bivariate_degreeX_C_eq_natDegree]
  have hprimX : Polynomial.Bivariate.degreeX Delta.primPart ≤
      Polynomial.Bivariate.degreeX Delta := by
    rw [hdegDelta]
    omega
  have hcontentX : Delta.content.natDegree ≤
      Polynomial.Bivariate.degreeX Delta := by
    rw [hdegDelta]
    omega
  refine ⟨Polynomial.C bc * bp, s, S, hs, hS, hSprim, ?_, ?_,
    hSx.trans hprimX, hsdeg.trans hcontentX⟩
  · rw [Delta.eq_C_content_mul_primPart, hcontent, hprimPart]
    simp only [map_mul, map_pow]
    ring
  · simpa [Polynomial.natDegree_primPart] using hSdeg

/-- Below the characteristic, UFD squarefreeness agrees with derivative
separability.  The degree hypothesis rules out the inseparable irreducibles
that can occur over the imperfect fraction field `F(Z)`. -/
theorem squarefree_separable_of_natDegree_lt_char
    {K : Type} [Field K] (p : ℕ) [CharP K p]
    (S : Polynomial K) (hS : Squarefree S) (hlt : S.natDegree < p) :
    S.Separable := by
  induction S using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hS.ne_zero rfl).elim
  | unit u hu =>
      exact (associated_one_iff_isUnit.mpr hu).symm.separable Polynomial.separable_one
  | mul z q hz hq ih =>
      have hparts := squarefree_mul_iff.mp hS
      have hqpos : 0 < q.natDegree :=
        Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_irreducible hq)
      have hq0 : q ≠ 0 := hq.ne_zero
      have hqdeg : q.natDegree ≤ (q * z).natDegree := by
        rw [Polynomial.natDegree_mul hq0 hz]
        omega
      have hzdeg : z.natDegree ≤ (q * z).natDegree := by
        rw [Polynomial.natDegree_mul hq0 hz]
        omega
      have hqsep : q.Separable := by
        rw [Polynomial.separable_def]
        exact irreducible_isCoprime_derivative_of_natDegree_lt_char
          p q hq hqpos (hqdeg.trans_lt hlt)
      exact hqsep.mul (ih hparts.2.2 (hzdeg.trans_lt hlt)) hparts.1.isCoprime

noncomputable def parityKernelResultant {A : Type*} [CommRing A]
    (S : Polynomial A) : A :=
  Polynomial.resultant S S.derivative S.natDegree (S.natDegree - 1)

/-- The raw `X`-resultant of a positive-degree primitive parity kernel is
nonzero.  This is the exact nonzero obstruction needed before counting its
`Z`-specialization roots. -/
theorem rawSepResultant_ne_zero_of_primitive_squarefree
    {A : Type} [CommRing A] [IsDomain A] [IsGCDMonoid A]
    [UniqueFactorizationMonoid (Polynomial A)]
    (p : ℕ) [CharP A p] (S : Polynomial A)
    (hprim : S.IsPrimitive) (hS : Squarefree S)
    (hpos : 0 < S.natDegree) (hlt : S.natDegree < p) :
    parityKernelResultant S ≠ 0 := by
  let K := FractionRing A
  let f : A →+* K := algebraMap A K
  let SK : Polynomial K := S.map f
  letI : CharP K p :=
    charP_of_injective_algebraMap (IsFractionRing.injective A K) p
  have hf : Function.Injective f := IsFractionRing.injective A K
  have hSKdeg : SK.natDegree = S.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf S
  have hSKsq : Squarefree SK :=
    Polynomial.IsPrimitive.squarefree_map_fraction S hprim hS
  have hSKsep : SK.Separable :=
    squarefree_separable_of_natDegree_lt_char p SK hSKsq (by simpa [hSKdeg])
  have hresK : SK.resultant SK.derivative ≠ 0 := by
    intro hzero
    exact (Polynomial.resultant_eq_zero_iff.mp hzero).2 hSKsep
  have hposK : 0 < SK.natDegree := by simpa [hSKdeg]
  have hltK : SK.natDegree < p := by simpa [hSKdeg]
  have hddegK : SK.derivative.natDegree = SK.natDegree - 1 := by
    apply le_antisymm (Polynomial.natDegree_derivative_le SK)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.coeff_derivative]
    have hs : SK.natDegree - 1 + 1 = SK.natDegree := by omega
    rw [hs]
    have hcastSucc : ((SK.natDegree - 1 : ℕ) : K) + 1 =
        (SK.natDegree : K) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun z : ℕ => (z : K)) hs
    rw [hcastSucc, Polynomial.coeff_natDegree]
    have hcast : (SK.natDegree : K) ≠ 0 := by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt hposK hltK)
        ((CharP.cast_eq_zero_iff K p SK.natDegree).mp hz)
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hSKsep.ne_zero) hcast
  have hfixedK :
      SK.resultant SK.derivative S.natDegree (S.natDegree - 1) ≠ 0 := by
    simpa [hSKdeg, hddegK] using hresK
  intro hraw
  apply hfixedK
  dsimp [SK]
  rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
  unfold parityKernelResultant at hraw
  rw [hraw]
  exact map_zero _

/-- Cancel the specialized square factor from an exact parity
decomposition.  This uses only unique factorization in the univariate
polynomial ring; no coprimality between the square factor and the kernel is
required. -/
theorem cancel_square_factor
    {F : Type*} [Field F] (B T W : Polynomial F)
    (hB : B ≠ 0) (hEq : B ^ 2 * T = W ^ 2) :
    ∃ V : Polynomial F, T = V ^ 2 := by
  have hBdW : B ∣ W := by
    apply polynomial_dvd_of_sq_dvd_sq B W
    exact ⟨T, hEq.symm⟩
  obtain ⟨V, rfl⟩ := hBdW
  refine ⟨V, ?_⟩
  have hBsq : B ^ 2 ≠ 0 := pow_ne_zero 2 hB
  apply mul_left_cancel₀ hBsq
  calc
    B ^ 2 * T = (B * V) ^ 2 := hEq
    _ = B ^ 2 * V ^ 2 := by ring

/-- A nonzero scalar multiple of a positive-degree square has zero
squarefree resultant.  This is the specialization statement appropriate for
the primitive kernel: coefficient content specializes to the scalar `a`. -/
theorem scalar_square_specialization_is_resultant_root
    {F : Type} [Field F]
    (S : Polynomial (Polynomial F)) (z a : F) (W : Polynomial F) (r : ℕ)
    (hSY : S.natDegree ≤ r) (ha : a ≠ 0)
    (hSquare : Polynomial.C a * S.map (Polynomial.evalRingHom z) = W ^ 2)
    (hSpos : 0 < (S.map (Polynomial.evalRingHom z)).natDegree) :
    Polynomial.eval z
      (Polynomial.resultant S S.derivative r (r - 1)) = 0 := by
  let Sz : Polynomial F := S.map (Polynomial.evalRingHom z)
  have hSzpos : 0 < Sz.natDegree := by simpa [Sz] using hSpos
  have hSz0 : Sz ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hSzpos
  have hSzle : Sz.natDegree ≤ r := by
    have hmaple : Sz.natDegree ≤ S.natDegree := by
      simpa [Sz] using Polynomial.natDegree_map_le (f :=
        Polynomial.evalRingHom z) (p := S)
    exact hmaple.trans hSY
  have hCa0 : Polynomial.C a ≠ (0 : Polynomial F) := by simpa using ha
  have hW0 : W ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hSquare
    exact mul_ne_zero hCa0 hSz0 hSquare
  have hWpos : 0 < W.natDegree := by
    have hdeg := congrArg Polynomial.natDegree hSquare
    rw [Polynomial.natDegree_mul hCa0 hSz0, Polynomial.natDegree_C,
      zero_add, pow_two, Polynomial.natDegree_mul hW0 hW0] at hdeg
    omega
  have hsqres : Polynomial.resultant
      (Polynomial.C a * Sz) (Polynomial.C a * Sz).derivative = 0 := by
    rw [hSquare]
    exact resultant_square_derivative_eq_zero W hWpos
  have hncp : ¬ IsCoprime
      (Polynomial.C a * Sz) (Polynomial.C a * Sz).derivative :=
    (Polynomial.resultant_eq_zero_iff.mp hsqres).2
  have hres : Polynomial.resultant Sz Sz.derivative = 0 := by
    rw [Polynomial.resultant_eq_zero_iff]
    refine ⟨Or.inl hSz0, ?_⟩
    intro hcop
    apply hncp
    rw [Polynomial.derivative_C_mul]
    exact (isCoprime_mul_unit_left
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha))
      Sz Sz.derivative).mpr hcop
  rw [bivariate_resultant_eval, ← Polynomial.derivative_map]
  change Polynomial.resultant Sz Sz.derivative r (r - 1) = 0
  apply resultant_fixed_degree_eq_zero_of_resultant_eq_zero
  · exact hSzle
  · exact (Polynomial.natDegree_derivative_le Sz).trans
      (Nat.sub_le_sub_right hSzle 1)
  · exact hres

/-- Complete specialization dichotomy for the integral parity kernel.  If a
square discriminant specialization is nonzero and the primitive kernel keeps
positive `X` degree, then that challenge is a root of the single nonzero
resultant obstruction.  Thus the only pre-resultant exceptions are exactly
`Delta_z = 0` and loss of positive degree of `S_z`. -/
theorem parity_kernel_square_specialization_is_resultant_root
    {F : Type} [Field F]
    (Delta B : Polynomial (Polynomial F)) (s : Polynomial F)
    (S : Polynomial (Polynomial F)) (z : F) (W : Polynomial F)
    (hdecomp : Delta = B ^ 2 * (Polynomial.C s * S))
    (hSquare : Delta.map (Polynomial.evalRingHom z) = W ^ 2)
    (hDeltaZ : Delta.map (Polynomial.evalRingHom z) ≠ 0)
    (hSpos : 0 < (S.map (Polynomial.evalRingHom z)).natDegree) :
    Polynomial.eval z (parityKernelResultant S) = 0 := by
  let Bz : Polynomial F := B.map (Polynomial.evalRingHom z)
  let Sz : Polynomial F := S.map (Polynomial.evalRingHom z)
  let a : F := s.eval z
  have hmapped : Delta.map (Polynomial.evalRingHom z) =
      Bz ^ 2 * (Polynomial.C a * Sz) := by
    rw [hdecomp]
    simp [Bz, Sz, a, Polynomial.map_mul, Polynomial.map_pow]
  have hBz : Bz ≠ 0 := by
    intro hzero
    apply hDeltaZ
    rw [hmapped, hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  have ha : a ≠ 0 := by
    intro hzero
    apply hDeltaZ
    rw [hmapped, hzero, Polynomial.C_0, zero_mul, mul_zero]
  have hscalar : ∃ V : Polynomial F, Polynomial.C a * Sz = V ^ 2 := by
    apply cancel_square_factor Bz (Polynomial.C a * Sz) W hBz
    rw [← hSquare]
    exact hmapped.symm
  obtain ⟨V, hV⟩ := hscalar
  unfold parityKernelResultant
  exact scalar_square_specialization_is_resultant_root S z a V S.natDegree
    le_rfl ha hV hSpos

/-- The parity-kernel resultant has exactly the bidegree ledger used by the
score-6400 arithmetic audit. -/
theorem parityKernelResultant_natDegree_le
    {F : Type} [Field F] (S : Polynomial (Polynomial F)) (d : ℕ)
    (hSZ : Polynomial.Bivariate.degreeX S ≤ 2 * d) :
    (parityKernelResultant S).natDegree ≤
      S.natDegree * (2 * d) + (S.natDegree - 1) * (2 * d) := by
  unfold parityKernelResultant
  apply squarefree_resultant_Z_degree_le6400
  · exact hSZ
  · exact (degreeX_derivative_le S).trans hSZ

/-- Exact `X`-degree accounting for the square factor in a nonzero parity
decomposition. -/
theorem square_factor_twice_natDegree_le
    {R : Type*} [CommRing R] [IsDomain R]
    (Delta B T : Polynomial R) (hDelta : Delta ≠ 0)
    (hdecomp : Delta = B ^ 2 * T) :
    2 * B.natDegree ≤ Delta.natDegree := by
  have hB : B ≠ 0 := by
    intro hzero
    apply hDelta
    rw [hdecomp, hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  have hT : T ≠ 0 := by
    intro hzero
    apply hDelta
    rw [hdecomp, hzero, mul_zero]
  rw [hdecomp, Polynomial.natDegree_mul (pow_ne_zero 2 hB) hT,
    pow_two, Polynomial.natDegree_mul hB hB]
  omega

/-- If the primitive parity kernel is constant in `X`, one nonvanishing
identity specialization whose discriminant is a square already forces the
entire discriminant to be a global square. -/
theorem global_square_of_constant_parity_kernel
    {F : Type*} [Field F]
    (Delta B S : Polynomial (Polynomial F)) (s x D : Polynomial F)
    (hdecomp : Delta = B ^ 2 * (Polynomial.C s * S))
    (hSdeg : S.natDegree = 0)
    (hBx : B.eval x ≠ 0)
    (hSquare : Delta.eval x = D ^ 2) :
    ∃ H : Polynomial (Polynomial F), Delta = H ^ 2 := by
  let u : Polynomial F := S.coeff 0
  have hSC : S = Polynomial.C u := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hSdeg]
  have hmapped : Delta.eval x =
      (B.eval x) ^ 2 * (s * u) := by
    rw [hdecomp, Polynomial.eval_mul, Polynomial.eval_pow, hSC]
    simp [u]
  have hkernel : ∃ V : Polynomial F, s * u = V ^ 2 := by
    apply cancel_square_factor (B.eval x) (s * u) D hBx
    rw [← hSquare]
    exact hmapped.symm
  obtain ⟨V, hV⟩ := hkernel
  refine ⟨B * Polynomial.C V, ?_⟩
  rw [hdecomp, hSC, ← Polynomial.C_mul, hV, map_pow]
  ring

/-- Benchmark-facing constant-kernel branch.  More than `k` identity
coordinates guarantee one at which the square factor does not vanish, because
its `X` degree is at most `k`; that single identity square then globalizes the
discriminant square. -/
theorem global_square_of_constant_parity_kernel_on_identities
    {F ι : Type*} [Field F] [DecidableEq ι]
    (Delta B S : Polynomial (Polynomial F)) (s : Polynomial F)
    (I : Finset ι) (omega : ι → F) (D : ι → Polynomial F) (k : ℕ)
    (hDelta : Delta ≠ 0)
    (hdecomp : Delta = B ^ 2 * (Polynomial.C s * S))
    (hSdeg : S.natDegree = 0)
    (hDX : Delta.natDegree ≤ 2 * k)
    (homega : Function.Injective omega)
    (hcard : k + 1 ≤ I.card)
    (hidentity : ∀ i ∈ I,
      Delta.eval (Polynomial.C (omega i)) = (D i) ^ 2) :
    ∃ H : Polynomial (Polynomial F), Delta = H ^ 2 := by
  have htwice : 2 * B.natDegree ≤ Delta.natDegree :=
    square_factor_twice_natDegree_le Delta B
      (Polynomial.C s * S) hDelta hdecomp
  have hBdeg : B.natDegree < I.card := by
    have : B.natDegree ≤ k := by omega
    omega
  have hB0 : B ≠ 0 := by
    intro hzero
    apply hDelta
    rw [hdecomp, hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  obtain ⟨i, hi, hBi⟩ := exists_eval_ne_zero_of_natDegree_lt_card
    I (fun i => Polynomial.C (omega i)) B
      (Polynomial.C_injective.comp homega) hB0 hBdeg
  exact global_square_of_constant_parity_kernel Delta B S s
    (Polynomial.C (omega i)) (D i) hdecomp hSdeg hBi (hidentity i hi)

/-- End-to-end algebraic kernel package.  Under the benchmark's
below-characteristic degree condition, every nonzero discriminant has either
a constant primitive kernel (the global-square branch) or one explicit
nonzero resultant obstruction with the advertised bidegree bound. -/
theorem exists_parity_kernel_resultant_dichotomy
    {F : Type} [Field F] [DecidableEq F]
    (p : ℕ) [CharP F p] (Delta : Polynomial (Polynomial F))
    (k d : ℕ) (hDelta : Delta ≠ 0)
    (hDX : Delta.natDegree ≤ 2 * k)
    (hDZ : Polynomial.Bivariate.degreeX Delta ≤ 2 * d)
    (hchar : 2 * k < p) :
    ∃ B : Polynomial (Polynomial F), ∃ s : Polynomial F,
      ∃ S : Polynomial (Polynomial F),
        Squarefree s ∧ Squarefree S ∧ S.IsPrimitive ∧
        Delta = B ^ 2 * (Polynomial.C s * S) ∧
        S.natDegree ≤ 2 * k ∧
        Polynomial.Bivariate.degreeX S ≤ 2 * d ∧
        s.natDegree ≤ 2 * d ∧
        (S.natDegree = 0 ∨ parityKernelResultant S ≠ 0) ∧
        (parityKernelResultant S).natDegree ≤
          S.natDegree * (2 * d) + (S.natDegree - 1) * (2 * d) := by
  obtain ⟨B, s, S, hs, hS, hprim, hdecomp, hSdeg, hSZ, hsdeg⟩ :=
    exists_primitive_quadratic_parity_kernel Delta hDelta
  have hSdeg' : S.natDegree ≤ 2 * k := hSdeg.trans hDX
  have hSZ' : Polynomial.Bivariate.degreeX S ≤ 2 * d := hSZ.trans hDZ
  have hsdeg' : s.natDegree ≤ 2 * d := hsdeg.trans hDZ
  have hdich : S.natDegree = 0 ∨ parityKernelResultant S ≠ 0 := by
    rcases S.natDegree.eq_zero_or_pos with hzero | hpos
    · exact Or.inl hzero
    · exact Or.inr (rawSepResultant_ne_zero_of_primitive_squarefree
        p S hprim hS hpos (hSdeg'.trans_lt hchar))
  exact ⟨B, s, S, hs, hS, hprim, hdecomp, hSdeg', hSZ', hsdeg',
    hdich, parityKernelResultant_natDegree_le S d hSZ'⟩

/-- Whole-polynomial zero specializations are controlled by one nonzero
coefficient, hence by one `degreeX` ledger. -/
theorem specialization_zero_card_le_degreeX
    {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial F)) (T : Finset F) (hQ : Q ≠ 0) :
    (T.filter fun z => Q.map (Polynomial.evalRingHom z) = 0).card ≤
      Polynomial.Bivariate.degreeX Q := by
  let c : Polynomial F := Q.coeff Q.natDegree
  have hc : c ≠ 0 := by
    change Q.coeff Q.natDegree ≠ 0
    simpa only [Polynomial.coeff_natDegree] using
      (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  have hsub : (T.filter fun z => Q.map (Polynomial.evalRingHom z) = 0) ⊆
      c.roots.toFinset := by
    intro z hz
    have hmap := (Finset.mem_filter.mp hz).2
    have hcoeff := congrArg
      (fun P : Polynomial F => P.coeff Q.natDegree) hmap
    have heval : Polynomial.eval z c = 0 := by
      change Polynomial.eval z (Q.coeff Q.natDegree) = 0
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
        Polynomial.coe_evalRingHom] using hcoeff
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hc]
    exact heval
  calc
    (T.filter fun z => Q.map (Polynomial.evalRingHom z) = 0).card ≤
        c.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ c.roots.card := Multiset.toFinset_card_le _
    _ ≤ c.natDegree := Polynomial.card_roots' c
    _ ≤ Polynomial.Bivariate.degreeX Q := by
      change (Q.coeff Q.natDegree).natDegree ≤
        Polynomial.Bivariate.degreeX Q
      exact Polynomial.Bivariate.coeff_natDegree_le_degreeX Q Q.natDegree

/-- Loss of positive `X` degree for a globally positive-degree kernel is
controlled by the leading coefficient, hence by the second `degreeX`
ledger. -/
theorem specialization_natDegree_zero_card_le_degreeX
    {F : Type*} [Field F] [DecidableEq F]
    (S : Polynomial (Polynomial F)) (T : Finset F)
    (hSpos : 0 < S.natDegree) :
    (T.filter fun z => (S.map (Polynomial.evalRingHom z)).natDegree = 0).card ≤
      Polynomial.Bivariate.degreeX S := by
  let c : Polynomial F := S.coeff S.natDegree
  have hS0 : S ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hSpos
  have hc : c ≠ 0 := by
    change S.coeff S.natDegree ≠ 0
    simpa only [Polynomial.coeff_natDegree] using
      (Polynomial.leadingCoeff_ne_zero.mpr hS0)
  have hsub :
      (T.filter fun z => (S.map (Polynomial.evalRingHom z)).natDegree = 0) ⊆
        c.roots.toFinset := by
    intro z hz
    have hdeg := (Finset.mem_filter.mp hz).2
    have htopzero : (S.map (Polynomial.evalRingHom z)).coeff S.natDegree = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa [hdeg] using hSpos
    have heval : Polynomial.eval z c = 0 := by
      change Polynomial.eval z (S.coeff S.natDegree) = 0
      simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom] using htopzero
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hc]
    exact heval
  calc
    (T.filter fun z => (S.map (Polynomial.evalRingHom z)).natDegree = 0).card ≤
        c.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ c.roots.card := Multiset.toFinset_card_le _
    _ ≤ c.natDegree := Polynomial.card_roots' c
    _ ≤ Polynomial.Bivariate.degreeX S := by
      change (S.coeff S.natDegree).natDegree ≤
        Polynomial.Bivariate.degreeX S
      exact Polynomial.Bivariate.coeff_natDegree_le_degreeX S S.natDegree

end BCHKSQuadraticKernel6400
end ProximityPrize.SubmissionLower
