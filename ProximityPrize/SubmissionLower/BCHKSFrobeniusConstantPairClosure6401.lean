import ProximityPrize.SubmissionLower.BCHKSFrobeniusProjectiveAffineLine6401
import ProximityPrize.SubmissionLower.BCHKSSphericalL3Bound6401

/-!
# Closing the constant primitive failure-pair branch

Suppose the syndrome line is projectively constant, so that for some scalar
`c` the word `v = u1 - c*u0` is an RS codeword.  Away from the one possible
root of `1+c*z`, normalize an owner by

`R_z = (P_z - z*v)/(1+c*z)`.

It has the original degree bound and agrees with the one fixed received word
`u0` on the original agreement set.  The target-radius spherical list bound
therefore permits at most `17045844` distinct `R_z`.  A fixed normalized
fiber is literally the affine owner line

`P_z = R + z*(v+c*R)`,

so failure of the requested `1183`-owner curve caps every fiber by `1182`.
The resulting complete cap is `1 + 1182*17045844 = 20148187609`.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusConstantPairClosure6401

open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSSphericalL3Bound6401

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-- Scalar polynomial form of the already-proved score-6401 spherical list
bound.  This avoids an unnecessary detour through the squared-word wrapper.
-/
theorem scalarPolynomialFamily_card_le_17045844
    {F J : Type*} [Field F] [DecidableEq F] [Fintype J]
    (alpha : Fin n6401 ↪ F) (received : Fin n6401 → F)
    (R : J → Polynomial F) (A : J → Finset (Fin n6401))
    (hRinj : Function.Injective R)
    (hRdeg : ∀ j, (R j).natDegree ≤ ownerDegreeCap6401)
    (hAcard : ∀ j, a6401 ≤ (A j).card)
    (hagree : ∀ j, ∀ i ∈ A j,
      Polynomial.eval (alpha i) (R j) = received i) :
    Fintype.card J ≤ BCHKSList6401.listBound6401 := by
  classical
  choose E hEA hEcard using fun j =>
    Finset.exists_subset_card_eq (hAcard j)
  have hinter : ∀ j k, j ≠ k → (E j ∩ E k).card ≤ 131071 := by
    intro j k hjk
    have hRne : R j ≠ R k := hRinj.ne hjk
    by_contra hnot
    have hlt : ownerDegreeCap6401 < (E j ∩ E k).card := by
      norm_num [ownerDegreeCap6401] at hnot ⊢
      omega
    let roots : Finset F := (E j ∩ E k).map alpha
    have hzero : R j - R k = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        (R j - R k) roots
      · intro x hx
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        have hiE := Finset.mem_inter.mp hi
        have hiAj : i ∈ A j := hEA j hiE.1
        have hiAk : i ∈ A k := hEA k hiE.2
        simp [Polynomial.eval_sub, hagree j i hiAj, hagree k i hiAk]
      · rw [Finset.card_map]
        exact (Polynomial.natDegree_sub_le (R j) (R k)).trans_lt
          (lt_of_le_of_lt (max_le (hRdeg j) (hRdeg k)) hlt)
    exact hRne (sub_eq_zero.mp hzero)
  have hsphere := exactAgreementFamily_card_le_17045844_of_card
    (owners := J) (coords := Fin n6401)
    (by native_decide) E
    (by
      intro j
      simpa [a6401] using hEcard j)
    hinter
  simpa [BCHKSList6401.listBound6401] using hsphere

/-- Division-free notation for the normalized owner polynomial. -/
noncomputable def normalizedOwner
    {F : Type*} [Field F]
    (c : F) (V : Polynomial F) (P : F → Polynomial F) (z : F) :
    Polynomial F :=
  Polynomial.C (1 + c * z)⁻¹ *
    (P z - Polynomial.C z * V)

theorem normalizedOwner_natDegree_le
    {F : Type*} [Field F]
    (c z : F) (V Pz : Polynomial F) (D : Nat)
    (hV : V.natDegree ≤ D) (hP : Pz.natDegree ≤ D) :
    (Polynomial.C (1 + c * z)⁻¹ *
      (Pz - Polynomial.C z * V)).natDegree ≤ D := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_sub_le _ _).trans
      (max_le hP ((Polynomial.natDegree_C_mul_le _ _).trans hV)))

theorem normalizedOwner_agrees
    {F : Type*} [Field F]
    (c z x u0 u1 : F) (V Pz : Polynomial F)
    (hden : 1 + c * z ≠ 0)
    (hV : Polynomial.eval x V = u1 - c * u0)
    (hP : Polynomial.eval x Pz = u0 + z * u1) :
    Polynomial.eval x
      (Polynomial.C (1 + c * z)⁻¹ *
        (Pz - Polynomial.C z * V)) = u0 := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    hV, hP]
  field_simp
  ring

/-- Equality of normalized owners is exactly an affine owner-line identity.
-/
theorem owner_eq_affine_of_normalizedOwner_eq
    {F : Type*} [Field F]
    (c z : F) (V R Pz : Polynomial F)
    (hden : 1 + c * z ≠ 0)
    (hnorm : Polynomial.C (1 + c * z)⁻¹ *
      (Pz - Polynomial.C z * V) = R) :
    Pz = R + Polynomial.C z * (V + Polynomial.C c * R) := by
  have hmul := congrArg
    (fun Q : Polynomial F => Polynomial.C (1 + c * z) * Q) hnorm
  have hcleared : Pz - Polynomial.C z * V =
      Polynomial.C (1 + c * z) * R := by
    calc
      Pz - Polynomial.C z * V =
          Polynomial.C 1 * (Pz - Polynomial.C z * V) := by simp
      _ = Polynomial.C ((1 + c * z) * (1 + c * z)⁻¹) *
          (Pz - Polynomial.C z * V) := by rw [mul_inv_cancel₀ hden]
      _ = Polynomial.C (1 + c * z) *
          (Polynomial.C (1 + c * z)⁻¹ *
            (Pz - Polynomial.C z * V)) := by
        simp only [map_mul]
        ring
      _ = Polynomial.C (1 + c * z) * R := by rw [hnorm]
  simp only [map_add, map_one, map_mul] at hcleared ⊢
  linear_combination hcleared

def constantPrimitiveFamilyCap6401 : Nat :=
  1 + 1182 * BCHKSList6401.listBound6401

theorem constantPrimitiveFamilyCap_exact6401 :
    constantPrimitiveFamilyCap6401 = 20148187609 ∧
      constantPrimitiveFamilyCap6401 < weakCurveSeedInput6401 := by
  native_decide

/-- Complete cap in the nonzero-base projectively constant syndrome case.

`V` is the degree-bounded RS representative of `u1-c*u0`.  All coding and
Frobenius semantics upstream are compressed into the literal evaluation
hypothesis `hVeval`; the rest is deterministic list/fiber algebra.
-/
theorem ownerFamily_card_le_constantPrimitiveFamilyCap6401_of_no_curve
    {F : Type*} [Field F] [DecidableEq F]
    (alpha : Fin n6401 ↪ F) (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F) (c : F) (V : Polynomial F)
    (hVdegree : V.natDegree ≤ ownerDegreeCap6401)
    (hVeval : ∀ i, Polynomial.eval (alpha i) V = u1 i - c * u0 i)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    S.card ≤ constantPrimitiveFamilyCap6401 := by
  classical
  let good := S.filter fun z => 1 + c * z ≠ 0
  let bad := S.filter fun z => 1 + c * z = 0
  let N : F → Polynomial F := normalizedOwner c V P
  let T : Finset (Polynomial F) := good.image N
  have hbad : bad.card ≤ 1 := by
    simpa [bad, mul_comm] using
      (fractionalLinear_poles_card_le_one S
        (0 : F) 1 1 c (by simp))
  have hpartition : good.card + bad.card = S.card := by
    simpa [good, bad, not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := S) (fun z => 1 + c * z ≠ 0))
  let source : {R // R ∈ T} → F := fun R =>
    Classical.choose (Finset.mem_image.mp R.2)
  have hsourceGood (R : {R // R ∈ T}) : source R ∈ good :=
    (Classical.choose_spec (Finset.mem_image.mp R.2)).1
  have hsourceEq (R : {R // R ∈ T}) : N (source R) = R.1 :=
    (Classical.choose_spec (Finset.mem_image.mp R.2)).2
  let AT : {R // R ∈ T} → Finset (Fin n6401) := fun R => A (source R)
  have hTcard : T.card ≤ BCHKSList6401.listBound6401 := by
    have hbound := scalarPolynomialFamily_card_le_17045844
      alpha u0 (fun R : {R // R ∈ T} => R.1) AT
      Subtype.val_injective
      (by
        intro R
        have hzS : source R ∈ S :=
          (Finset.mem_filter.mp (hsourceGood R)).1
        have hdeg := normalizedOwner_natDegree_le c (source R) V
          (P (source R)) ownerDegreeCap6401 hVdegree (hPdegree _ hzS)
        rw [← hsourceEq R]
        simpa [N, normalizedOwner] using hdeg)
      (by
        intro R
        exact hrow (source R)
          (Finset.mem_filter.mp (hsourceGood R)).1)
      (by
        intro R i hi
        have hz := hsourceGood R
        have hzS : source R ∈ S := (Finset.mem_filter.mp hz).1
        have hzden : 1 + c * source R ≠ 0 :=
          (Finset.mem_filter.mp hz).2
        rw [← hsourceEq R]
        exact normalizedOwner_agrees c (source R) (alpha i)
          (u0 i) (u1 i) V (P (source R)) hzden (hVeval i)
          (howner (source R) hzS i hi))
    simpa using hbound
  let fiber : Polynomial F → Finset F := fun R =>
    good.filter fun z => N z = R
  have hfiber : ∀ R ∈ T, (fiber R).card ≤ 1182 := by
    intro R hRT
    have hRdegree : R.natDegree ≤ ownerDegreeCap6401 := by
      obtain ⟨z, hzgood, hNz⟩ := Finset.mem_image.mp hRT
      rw [← hNz]
      have hzS : z ∈ S := (Finset.mem_filter.mp hzgood).1
      have hdeg := normalizedOwner_natDegree_le c z V (P z)
        ownerDegreeCap6401 hVdegree (hPdegree z hzS)
      simpa [N, normalizedOwner] using hdeg
    have hp1degree :
        (V + Polynomial.C c * R).natDegree ≤ ownerDegreeCap6401 :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le hVdegree ((Polynomial.natDegree_C_mul_le _ _).trans hRdegree))
    apply affineFamily_card_le_1182_of_no_curveWitness6401
      S (fiber R) P R (V + Polynomial.C c * R)
      hfail hRdegree hp1degree
    · intro z hz
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
    · intro z hz
      have hzgood : z ∈ good := (Finset.mem_filter.mp hz).1
      have hzden : 1 + c * z ≠ 0 := (Finset.mem_filter.mp hzgood).2
      have hNz : N z = R := (Finset.mem_filter.mp hz).2
      exact owner_eq_affine_of_normalizedOwner_eq c z V R (P z)
        hzden (by simpa [N, normalizedOwner] using hNz)
  have hcover : T.biUnion fiber = good := by
    ext z
    constructor
    · intro hz
      obtain ⟨R, hRT, hzfib⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp hzfib).1
    · intro hz
      apply Finset.mem_biUnion.mpr
      refine ⟨N z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  have hgood : good.card ≤
      BCHKSList6401.listBound6401 * 1182 := by
    rw [← hcover]
    exact (Finset.card_biUnion_le_card_mul T fiber 1182 hfiber).trans
      (Nat.mul_le_mul_right 1182 hTcard)
  rw [← hpartition]
  dsimp [constantPrimitiveFamilyCap6401]
  omega

/-- A weak-seed-sized family in the constant projective case necessarily
contains the requested `1183`-owner affine curve. -/
theorem constantPrimitive_ownerCurve6401
    {F : Type*} [Field F] [DecidableEq F]
    (alpha : Fin n6401 ↪ F) (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F) (c : F) (V : Polynomial F)
    (hVdegree : V.natDegree ≤ ownerDegreeCap6401)
    (hVeval : ∀ i, Polynomial.eval (alpha i) V = u1 i - c * u0 i)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    PolynomialAffineCurveWitness6401 S P := by
  by_contra hfail
  have hcap :=
    ownerFamily_card_le_constantPrimitiveFamilyCap6401_of_no_curve
      alpha u0 u1 S A P c V hVdegree hVeval hPdegree hrow howner hfail
  exact (not_le_of_gt constantPrimitiveFamilyCap_exact6401.2)
    (hSlarge.trans hcap)

/-! ## The zero base-syndrome case -/

/-- If `u0` itself is a codeword, subtract it and divide by the nonzero
challenge. -/
noncomputable def zeroBaseNormalizedOwner
    {F : Type*} [Field F]
    (Q : Polynomial F) (P : F → Polynomial F) (z : F) : Polynomial F :=
  Polynomial.C z⁻¹ * (P z - Q)

theorem zeroBaseNormalizedOwner_agrees
    {F : Type*} [Field F]
    (z x u0 u1 : F) (Q Pz : Polynomial F)
    (hz : z ≠ 0)
    (hQ : Polynomial.eval x Q = u0)
    (hP : Polynomial.eval x Pz = u0 + z * u1) :
    Polynomial.eval x (Polynomial.C z⁻¹ * (Pz - Q)) = u1 := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    hQ, hP]
  field_simp
  ring

theorem owner_eq_affine_of_zeroBaseNormalizedOwner_eq
    {F : Type*} [Field F]
    (z : F) (Q R Pz : Polynomial F) (hz : z ≠ 0)
    (hnorm : Polynomial.C z⁻¹ * (Pz - Q) = R) :
    Pz = Q + Polynomial.C z * R := by
  have hmul := congrArg (fun W : Polynomial F => Polynomial.C z * W) hnorm
  have hcleared : Pz - Q = Polynomial.C z * R := by
    calc
      Pz - Q = Polynomial.C 1 * (Pz - Q) := by simp
      _ = Polynomial.C (z * z⁻¹) * (Pz - Q) := by
        rw [mul_inv_cancel₀ hz]
      _ = Polynomial.C z * (Polynomial.C z⁻¹ * (Pz - Q)) := by
        simp only [map_mul]
        ring
      _ = Polynomial.C z * R := by rw [hnorm]
  linear_combination hcleared

/-- Complete no-curve cap when the base received word `u0` is itself an RS
codeword.  The one excluded challenge is `z=0`.
-/
theorem ownerFamily_card_le_zeroBaseFamilyCap6401_of_no_curve
    {F : Type*} [Field F] [DecidableEq F]
    (alpha : Fin n6401 ↪ F) (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F) (Q : Polynomial F)
    (hQdegree : Q.natDegree ≤ ownerDegreeCap6401)
    (hQeval : ∀ i, Polynomial.eval (alpha i) Q = u0 i)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    S.card ≤ constantPrimitiveFamilyCap6401 := by
  classical
  let good := S.filter fun z => z ≠ 0
  let bad := S.filter fun z => z = 0
  let N : F → Polynomial F := zeroBaseNormalizedOwner Q P
  let T : Finset (Polynomial F) := good.image N
  have hbad : bad.card ≤ 1 := by
    simpa [bad] using
      (fractionalLinear_poles_card_le_one S
        (1 : F) 0 0 1 (by simp))
  have hpartition : good.card + bad.card = S.card := by
    simpa [good, bad, not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := S) (fun z => z ≠ 0))
  let source : {R // R ∈ T} → F := fun R =>
    Classical.choose (Finset.mem_image.mp R.2)
  have hsourceGood (R : {R // R ∈ T}) : source R ∈ good :=
    (Classical.choose_spec (Finset.mem_image.mp R.2)).1
  have hsourceEq (R : {R // R ∈ T}) : N (source R) = R.1 :=
    (Classical.choose_spec (Finset.mem_image.mp R.2)).2
  let AT : {R // R ∈ T} → Finset (Fin n6401) := fun R => A (source R)
  have hTcard : T.card ≤ BCHKSList6401.listBound6401 := by
    have hbound := scalarPolynomialFamily_card_le_17045844
      alpha u1 (fun R : {R // R ∈ T} => R.1) AT
      Subtype.val_injective
      (by
        intro R
        have hzS : source R ∈ S :=
          (Finset.mem_filter.mp (hsourceGood R)).1
        have hdeg :
            (Polynomial.C (source R)⁻¹ *
              (P (source R) - Q)).natDegree ≤ ownerDegreeCap6401 :=
          (Polynomial.natDegree_C_mul_le _ _).trans
            ((Polynomial.natDegree_sub_le _ _).trans
              (max_le (hPdegree _ hzS) hQdegree))
        rw [← hsourceEq R]
        simpa [N, zeroBaseNormalizedOwner] using hdeg)
      (by
        intro R
        exact hrow (source R)
          (Finset.mem_filter.mp (hsourceGood R)).1)
      (by
        intro R i hi
        have hz := hsourceGood R
        have hzS : source R ∈ S := (Finset.mem_filter.mp hz).1
        have hzne : source R ≠ 0 := (Finset.mem_filter.mp hz).2
        rw [← hsourceEq R]
        exact zeroBaseNormalizedOwner_agrees (source R) (alpha i)
          (u0 i) (u1 i) Q (P (source R)) hzne (hQeval i)
          (howner (source R) hzS i hi))
    simpa using hbound
  let fiber : Polynomial F → Finset F := fun R =>
    good.filter fun z => N z = R
  have hfiber : ∀ R ∈ T, (fiber R).card ≤ 1182 := by
    intro R hRT
    have hRdegree : R.natDegree ≤ ownerDegreeCap6401 := by
      obtain ⟨z, hzgood, hNz⟩ := Finset.mem_image.mp hRT
      rw [← hNz]
      have hzS : z ∈ S := (Finset.mem_filter.mp hzgood).1
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_sub_le _ _).trans
          (max_le (hPdegree z hzS) hQdegree))
    apply affineFamily_card_le_1182_of_no_curveWitness6401
      S (fiber R) P Q R hfail hQdegree hRdegree
    · intro z hz
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
    · intro z hz
      have hzgood : z ∈ good := (Finset.mem_filter.mp hz).1
      have hzne : z ≠ 0 := (Finset.mem_filter.mp hzgood).2
      have hNz : N z = R := (Finset.mem_filter.mp hz).2
      exact owner_eq_affine_of_zeroBaseNormalizedOwner_eq z Q R (P z)
        hzne (by simpa [N, zeroBaseNormalizedOwner] using hNz)
  have hcover : T.biUnion fiber = good := by
    ext z
    constructor
    · intro hz
      obtain ⟨R, hRT, hzfib⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp hzfib).1
    · intro hz
      exact Finset.mem_biUnion.mpr
        ⟨N z, Finset.mem_image.mpr ⟨z, hz, rfl⟩,
          Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  have hgood : good.card ≤
      BCHKSList6401.listBound6401 * 1182 := by
    rw [← hcover]
    exact (Finset.card_biUnion_le_card_mul T fiber 1182 hfiber).trans
      (Nat.mul_le_mul_right 1182 hTcard)
  rw [← hpartition]
  dsimp [constantPrimitiveFamilyCap6401]
  omega

theorem zeroBasePrimitive_ownerCurve6401
    {F : Type*} [Field F] [DecidableEq F]
    (alpha : Fin n6401 ↪ F) (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F) (Q : Polynomial F)
    (hQdegree : Q.natDegree ≤ ownerDegreeCap6401)
    (hQeval : ∀ i, Polynomial.eval (alpha i) Q = u0 i)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    PolynomialAffineCurveWitness6401 S P := by
  by_contra hfail
  have hcap := ownerFamily_card_le_zeroBaseFamilyCap6401_of_no_curve
    alpha u0 u1 S A P Q hQdegree hQeval hPdegree hrow howner hfail
  exact (not_le_of_gt constantPrimitiveFamilyCap_exact6401.2)
    (hSlarge.trans hcap)

end BCHKSFrobeniusConstantPairClosure6401
end ProximityPrize.SubmissionLower
