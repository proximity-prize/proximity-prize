/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.PadeQuotientBridge

/-!
# Reciprocal reduction of the Padé quotient gate

The reciprocal `136`-selector experiment uses a reciprocal denominator of
formal degree `120`.  Its Padé numerator is reciprocal of formal degree `254`,
and the quotient is reciprocal of formal degree `134`.  Consequently the
seven forbidden high coefficients `128, ..., 134` vanish exactly when the
seven low coefficients `0, ..., 6` vanish.

This file isolates that symmetry argument.  It does not assert the missing
rank-one pencil: the seven low-coefficient equations remain genuine
obligations.
-/

namespace ProximityPrize.SubmissionUpper.ReciprocalPadeBridge

open Polynomial

variable {F : Type*} [Field F]

/-- A polynomial is reciprocal in a prescribed formal degree when reflecting
its coefficients in that degree fixes it.  The separate degree bound matters:
`Polynomial.reflect` leaves coefficients above the formal degree unchanged. -/
def ReciprocalAt (n : ℕ) (P : Polynomial F) : Prop :=
  P.reflect n = P

theorem coeff_eq_reflected_of_reciprocalAt {n : ℕ} {P : Polynomial F}
    (hP : ReciprocalAt n P) (i : ℕ) :
    P.coeff i = P.coeff (Polynomial.revAt n i) := by
  have h := congrArg (fun Q : Polynomial F => Q.coeff i) hP
  simpa only [Polynomial.coeff_reflect] using h.symm

theorem coeff_eq_coeff_sub_of_reciprocalAt {n i : ℕ} {P : Polynomial F}
    (hP : ReciprocalAt n P) (hi : i ≤ n) :
    P.coeff i = P.coeff (n - i) := by
  rw [coeff_eq_reflected_of_reciprocalAt hP, Polynomial.revAt_le hi]

/-- Raising the formal reflection degree by one multiplies the reflected
polynomial by `X`, provided the original degree fits in the old bound. -/
theorem reflect_succ_eq_X_mul_reflect {n : ℕ} {P : Polynomial F}
    (hPdegree : P.natDegree ≤ n) :
    P.reflect (n + 1) = (Polynomial.X : Polynomial F) * P.reflect n := by
  calc
    P.reflect (n + 1) = ((1 : Polynomial F) * P).reflect (1 + n) := by
      simp only [one_mul, Nat.add_comm]
    _ = (1 : Polynomial F).reflect 1 * P.reflect n := by
      rw [Polynomial.reflect_mul (1 : Polynomial F) P (by simp) hPdegree]
    _ = (Polynomial.X : Polynomial F) * P.reflect n := by
      rw [Polynomial.reflect_one]
      simp

/-- A polynomial remainder of degree at most `119` which is invariant under
inversion modulo a monic reciprocal degree-`120` denominator loses its top
coefficient and becomes reciprocal in formal degree `118`.

The quotient-ring relation is written without Laurent polynomials as
`D ∣ X * H - reflect 119 H`.  Since the dividend has degree at most `120`,
it is a scalar multiple of `D`.  Its endpoint coefficients are respectively
`H.coeff 119` and `-H.coeff 119`; the denominator has both endpoints equal to
one, so odd characteristic forces that coefficient to vanish. -/
theorem reciprocalAt_118_of_modular_inversion
    {D H : Polynomial F}
    (htwo : (2 : F) ≠ 0)
    (hDmonic : D.Monic) (hDdegree : D.natDegree = 120)
    (hDconstant : D.coeff 0 = 1)
    (hHdegree : H.natDegree ≤ 119)
    (hmod : D ∣ (Polynomial.X : Polynomial F) * H - H.reflect 119) :
    H.natDegree ≤ 118 ∧ ReciprocalAt 118 H := by
  let P : Polynomial F := (Polynomial.X : Polynomial F) * H - H.reflect 119
  have hPdegree : P.natDegree ≤ D.natDegree := by
    rw [hDdegree]
    dsimp only [P]
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    apply max_le
    · exact (Polynomial.natDegree_mul_le.trans
        (by simpa only [Polynomial.natDegree_X] using Nat.add_le_add_left hHdegree 1))
    · calc
        (H.reflect 119).natDegree ≤ max 119 H.natDegree :=
          Polynomial.natDegree_reflect_le
        _ ≤ 120 := max_le (by omega) (hHdegree.trans (by omega))
  have hPscalar := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    hDmonic hmod hPdegree
  change P = Polynomial.C P.leadingCoeff * D at hPscalar
  have htop : H.coeff 119 = P.leadingCoeff := by
    have h := congrArg (fun Q : Polynomial F => Q.coeff 120) hPscalar
    change ((Polynomial.X : Polynomial F) * H - H.reflect 119).coeff 120 = _ at h
    have hx : ((Polynomial.X : Polynomial F) * H).coeff 120 = H.coeff 119 := by
      simpa only [show 120 = 119 + 1 by norm_num] using Polynomial.coeff_X_mul H 119
    have hH120 : H.coeff 120 = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (p := H)
        (lt_of_le_of_lt hHdegree (by omega))
    have hreflect : (H.reflect 119).coeff 120 = 0 := by
      rw [Polynomial.coeff_reflect,
        Polynomial.revAt_eq_self_of_lt (by omega : 119 < 120), hH120]
    have hDtop : D.coeff 120 = 1 := by
      rw [← hDdegree]
      exact hDmonic.coeff_natDegree
    simp only [Polynomial.coeff_sub, hx, hreflect, sub_zero,
      Polynomial.coeff_C_mul, hDtop, mul_one] at h
    simpa using h
  have hbottom : -H.coeff 119 = P.leadingCoeff := by
    have h := congrArg (fun Q : Polynomial F => Q.coeff 0) hPscalar
    change ((Polynomial.X : Polynomial F) * H - H.reflect 119).coeff 0 = _ at h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero,
      Polynomial.coeff_reflect, Polynomial.revAt_zero, zero_sub,
      Polynomial.coeff_C_mul, hDconstant, mul_one] at h
    simpa using h
  have h119 : H.coeff 119 = 0 := by
    have hneg : -H.coeff 119 = H.coeff 119 := hbottom.trans htop.symm
    have h2 : (2 : F) * H.coeff 119 = 0 := by
      have hadd : -H.coeff 119 + H.coeff 119 = 0 := neg_add_cancel _
      rw [hneg] at hadd
      simpa only [two_mul] using hadd
    exact (mul_eq_zero.mp h2).resolve_left htwo
  have hPzero : P = 0 := by
    calc
      P = Polynomial.C P.leadingCoeff * D := hPscalar
      _ = 0 := by rw [← htop, h119]; simp
  have hreflection : (Polynomial.X : Polynomial F) * H = H.reflect 119 := by
    dsimp only [P] at hPzero
    exact sub_eq_zero.mp hPzero
  have hH118 : H.natDegree ≤ 118 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    by_cases hi119 : i = 119
    · simpa only [hi119] using h119
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hHdegree (by omega))
  refine ⟨hH118, ?_⟩
  rw [ReciprocalAt]
  ext i
  by_cases hi : i ≤ 118
  · have h := congrArg (fun Q : Polynomial F => Q.coeff (i + 1)) hreflection
    simp only [Polynomial.coeff_X_mul, Polynomial.coeff_reflect,
      Polynomial.revAt_le (by omega : i + 1 ≤ 119)] at h
    rw [show 119 - (i + 1) = 118 - i by omega] at h
    simpa only [Polynomial.coeff_reflect, Polynomial.revAt_le hi] using h.symm
  · simp only [Polynomial.coeff_reflect,
      Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hi)]

/-- The factorization used by the reciprocal Padé construction implies the
modular inversion relation needed above.  Reflection of
`D * Q = H * V - N` in formal degree `255`, followed by subtraction from
`X` times the original equality, gives

`D * (X * Q - reflect 135 Q) = V * (X * H - reflect 119 H)`.

Coprimality of `D` and the selector `V` then cancels `V`. -/
theorem modular_inversion_of_reciprocal_factorization
    {D Q H V N : Polynomial F}
    (hDdegree : D.natDegree ≤ 120) (hQdegree : Q.natDegree ≤ 135)
    (hHdegree : H.natDegree ≤ 119) (hVdegree : V.natDegree ≤ 136)
    (hNdegree : N.natDegree ≤ 254)
    (hD : ReciprocalAt 120 D) (hV : ReciprocalAt 136 V)
    (hN : ReciprocalAt 254 N)
    (hcoprime : IsCoprime D V)
    (hfactor : D * Q = H * V - N) :
    D ∣ (Polynomial.X : Polynomial F) * H - H.reflect 119 := by
  have hleft : (D * Q).reflect 255 = D * Q.reflect 135 := by
    rw [show 255 = 120 + 135 by norm_num,
      Polynomial.reflect_mul D Q hDdegree hQdegree, hD]
  have hHV : (H * V).reflect 255 = H.reflect 119 * V := by
    rw [show 255 = 119 + 136 by norm_num,
      Polynomial.reflect_mul H V hHdegree hVdegree, hV]
  have hNshift : N.reflect 255 = (Polynomial.X : Polynomial F) * N := by
    rw [show 255 = 254 + 1 by norm_num,
      reflect_succ_eq_X_mul_reflect hNdegree, hN]
  have hrefactor : D * Q.reflect 135 = H.reflect 119 * V -
      (Polynomial.X : Polynomial F) * N := by
    calc
      D * Q.reflect 135 = (D * Q).reflect 255 := hleft.symm
      _ = (H * V - N).reflect 255 := congrArg (Polynomial.reflect 255) hfactor
      _ = (H * V).reflect 255 - N.reflect 255 := by
        rw [Polynomial.reflect_sub]
      _ = H.reflect 119 * V - (Polynomial.X : Polynomial F) * N := by
        rw [hHV, hNshift]
  have hidentity : D * ((Polynomial.X : Polynomial F) * Q - Q.reflect 135) =
      V * ((Polynomial.X : Polynomial F) * H - H.reflect 119) := by
    calc
      D * ((Polynomial.X : Polynomial F) * Q - Q.reflect 135) =
          (Polynomial.X : Polynomial F) * (D * Q) - D * Q.reflect 135 := by ring
      _ = (Polynomial.X : Polynomial F) * (H * V - N) -
          (H.reflect 119 * V - (Polynomial.X : Polynomial F) * N) := by
        rw [hfactor, hrefactor]
      _ = V * ((Polynomial.X : Polynomial F) * H - H.reflect 119) := by ring
  apply hcoprime.dvd_of_dvd_mul_left
  exact ⟨(Polynomial.X : Polynomial F) * Q - Q.reflect 135, hidentity.symm⟩

/-- End-to-end reciprocal-remainder lemma for the benchmark degrees.  It
proves both the automatic disappearance of row `119` and the remaining
formal-degree-`118` symmetry directly from the Padé factorization. -/
theorem reciprocalAt_118_of_reciprocal_factorization
    {D Q H V N : Polynomial F}
    (htwo : (2 : F) ≠ 0)
    (hDmonic : D.Monic) (hDdegree : D.natDegree = 120)
    (hDconstant : D.coeff 0 = 1)
    (hQdegree : Q.natDegree ≤ 135) (hHdegree : H.natDegree ≤ 119)
    (hVdegree : V.natDegree ≤ 136) (hNdegree : N.natDegree ≤ 254)
    (hD : ReciprocalAt 120 D) (hV : ReciprocalAt 136 V)
    (hN : ReciprocalAt 254 N)
    (hcoprime : IsCoprime D V)
    (hfactor : D * Q = H * V - N) :
    H.natDegree ≤ 118 ∧ ReciprocalAt 118 H := by
  apply reciprocalAt_118_of_modular_inversion htwo hDmonic hDdegree hDconstant hHdegree
  apply modular_inversion_of_reciprocal_factorization
    (hDdegree.le) hQdegree hHdegree hVdegree hNdegree hD hV hN hcoprime hfactor

/-- Reflection respects the benchmark product degrees `120 + 134 = 254`. -/
theorem reciprocalAt_mul_120_134 {D Q : Polynomial F}
    (hDdeg : D.natDegree ≤ 120) (hQdeg : Q.natDegree ≤ 134)
    (hD : ReciprocalAt 120 D) (hQ : ReciprocalAt 134 Q) :
    ReciprocalAt 254 (D * Q) := by
  rw [ReciprocalAt, show 254 = 120 + 134 by norm_num,
    Polynomial.reflect_mul D Q hDdeg hQdeg, hD, hQ]

/-- The reciprocal cofactor and selector degrees add to the reciprocal
numerator degree used by the experiment. -/
theorem reciprocalAt_mul_118_136 {H V : Polynomial F}
    (hHdeg : H.natDegree ≤ 118) (hVdeg : V.natDegree ≤ 136)
    (hH : ReciprocalAt 118 H) (hV : ReciprocalAt 136 V) :
    ReciprocalAt 254 (H * V) := by
  rw [ReciprocalAt, show 254 = 118 + 136 by norm_num,
    Polynomial.reflect_mul H V hHdeg hVdeg, hH, hV]

/-- Subtracting a reciprocal numerator preserves formal-degree-254
reciprocity. -/
theorem reciprocalAt_mul_sub_254 {H V N : Polynomial F}
    (hHdeg : H.natDegree ≤ 118) (hVdeg : V.natDegree ≤ 136)
    (hH : ReciprocalAt 118 H) (hV : ReciprocalAt 136 V)
    (hN : ReciprocalAt 254 N) :
    ReciprocalAt 254 (H * V - N) := by
  rw [ReciprocalAt, Polynomial.reflect_sub,
    reciprocalAt_mul_118_136 hHdeg hVdeg hH hV, hN]

/-- Cancellation by a nonzero reciprocal denominator transfers reciprocity
from the numerator to the quotient. -/
theorem reciprocalAt_quotient_134 {D Q P : Polynomial F}
    (hDne : D ≠ 0) (hDdeg : D.natDegree ≤ 120) (hQdeg : Q.natDegree ≤ 134)
    (hD : ReciprocalAt 120 D) (hP : ReciprocalAt 254 P)
    (hfactor : D * Q = P) :
    ReciprocalAt 134 Q := by
  have hreflect : (D * Q).reflect 254 = D * Q := by
    rw [hfactor, hP]
  rw [show 254 = 120 + 134 by norm_num,
    Polynomial.reflect_mul D Q hDdeg hQdeg, hD] at hreflect
  exact mul_left_cancel₀ hDne hreflect

/-- For a reciprocal formal-degree-134 quotient, the seven low zeros force
the seven forbidden high zeros. -/
theorem high_seven_zero_of_low_seven_zero {Q : Polynomial F}
    (hrec : ReciprocalAt 134 Q)
    (hlow : ∀ j < 7, Q.coeff j = 0) :
    ∀ i, 128 ≤ i → i ≤ 134 → Q.coeff i = 0 := by
  intro i hi hlo
  rw [coeff_eq_coeff_sub_of_reciprocalAt hrec hlo]
  exact hlow (134 - i) (by omega)

/-- Conversely, the benchmark high band forces the seven low coefficients
to vanish on a reciprocal quotient. -/
theorem low_seven_zero_of_high_seven_zero {Q : Polynomial F}
    (hrec : ReciprocalAt 134 Q)
    (hhigh : ∀ i, 128 ≤ i → i ≤ 134 → Q.coeff i = 0) :
    ∀ j < 7, Q.coeff j = 0 := by
  intro j hj
  rw [coeff_eq_coeff_sub_of_reciprocalAt hrec (by omega : j ≤ 134)]
  exact hhigh (134 - j) (by omega) (by omega)

/-- Under the symmetry-provided ambient cap `134`, the seven low equations
are sufficient for the benchmark quotient cap `127`. -/
theorem natDegree_le_127_of_reciprocalAt_of_low_seven_zero
    {Q : Polynomial F} (hdeg : Q.natDegree ≤ 134)
    (hrec : ReciprocalAt 134 Q)
    (hlow : ∀ j < 7, Q.coeff j = 0) :
    Q.natDegree ≤ 127 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  by_cases h134 : i ≤ 134
  · exact high_seven_zero_of_low_seven_zero hrec hlow i (by omega) h134
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))

/-- The degree cap `127` also forces the seven low equations. -/
theorem low_seven_zero_of_natDegree_le_127_of_reciprocalAt
    {Q : Polynomial F} (hdeg : Q.natDegree ≤ 127)
    (hrec : ReciprocalAt 134 Q) :
    ∀ j < 7, Q.coeff j = 0 := by
  apply low_seven_zero_of_high_seven_zero hrec
  intro i hi _
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))

/-- Exact reciprocal form of the seven-row quotient gate. -/
theorem natDegree_le_127_iff_low_seven_zero
    {Q : Polynomial F} (hdeg : Q.natDegree ≤ 134)
    (hrec : ReciprocalAt 134 Q) :
    Q.natDegree ≤ 127 ↔ ∀ j < 7, Q.coeff j = 0 := by
  constructor
  · exact fun h => low_seven_zero_of_natDegree_le_127_of_reciprocalAt h hrec
  · exact natDegree_le_127_of_reciprocalAt_of_low_seven_zero hdeg hrec

/-- Divisibility by `X^7` is the compact polynomial form of the reciprocal
seven-row gate. -/
theorem natDegree_le_127_iff_X_pow_seven_dvd
    {Q : Polynomial F} (hdeg : Q.natDegree ≤ 134)
    (hrec : ReciprocalAt 134 Q) :
    Q.natDegree ≤ 127 ↔ (Polynomial.X : Polynomial F) ^ 7 ∣ Q := by
  rw [natDegree_le_127_iff_low_seven_zero hdeg hrec,
    Polynomial.X_pow_dvd_iff]

/-- Complete reciprocal Padé gate from a degree-`135` a priori quotient
bound.  The factorization first forces the remainder down from degree `119`
to `118`; that sharpens the quotient bound to `134`, transfers reciprocity
to the quotient, and identifies the final cap `127` with divisibility by
`X^7`. -/
theorem reciprocal_factorization_gate
    {D Q H V N : Polynomial F}
    (htwo : (2 : F) ≠ 0)
    (hDmonic : D.Monic) (hDdegree : D.natDegree = 120)
    (hDconstant : D.coeff 0 = 1)
    (hQdegree : Q.natDegree ≤ 135) (hHdegree : H.natDegree ≤ 119)
    (hVdegree : V.natDegree ≤ 136) (hNdegree : N.natDegree ≤ 254)
    (hD : ReciprocalAt 120 D) (hV : ReciprocalAt 136 V)
    (hN : ReciprocalAt 254 N)
    (hcoprime : IsCoprime D V)
    (hfactor : D * Q = H * V - N) :
    H.natDegree ≤ 118 ∧ ReciprocalAt 118 H ∧
      Q.natDegree ≤ 134 ∧ ReciprocalAt 134 Q ∧
      (Q.natDegree ≤ 127 ↔ (Polynomial.X : Polynomial F) ^ 7 ∣ Q) := by
  obtain ⟨hH118, hHrec⟩ := reciprocalAt_118_of_reciprocal_factorization
    htwo hDmonic hDdegree hDconstant hQdegree hHdegree hVdegree hNdegree
    hD hV hN hcoprime hfactor
  have hproductDegree : (H * V - N).natDegree ≤ 254 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ hNdegree)
    exact Polynomial.natDegree_mul_le.trans (by omega)
  have hQ134 : Q.natDegree ≤ 134 := by
    by_cases hQzero : Q = 0
    · simp [hQzero]
    · have hDQdegree : (D * Q).natDegree ≤ 254 := by
        rw [hfactor]
        exact hproductDegree
      rw [Polynomial.natDegree_mul hDmonic.ne_zero hQzero, hDdegree] at hDQdegree
      omega
  have hPRec : ReciprocalAt 254 (H * V - N) :=
    reciprocalAt_mul_sub_254 hH118 hVdegree hHrec hV hN
  have hQrec : ReciprocalAt 134 Q :=
    reciprocalAt_quotient_134 hDmonic.ne_zero hDdegree.le hQ134 hD hPRec hfactor
  exact ⟨hH118, hHrec, hQ134, hQrec,
    natDegree_le_127_iff_X_pow_seven_dvd hQ134 hQrec⟩

end ProximityPrize.SubmissionUpper.ReciprocalPadeBridge

#print axioms ProximityPrize.SubmissionUpper.ReciprocalPadeBridge.reciprocalAt_118_of_modular_inversion
#print axioms ProximityPrize.SubmissionUpper.ReciprocalPadeBridge.reciprocalAt_118_of_reciprocal_factorization
#print axioms ProximityPrize.SubmissionUpper.ReciprocalPadeBridge.reciprocalAt_quotient_134
#print axioms ProximityPrize.SubmissionUpper.ReciprocalPadeBridge.natDegree_le_127_iff_low_seven_zero
#print axioms ProximityPrize.SubmissionUpper.ReciprocalPadeBridge.natDegree_le_127_iff_X_pow_seven_dvd
#print axioms ProximityPrize.SubmissionUpper.ReciprocalPadeBridge.reciprocal_factorization_gate
