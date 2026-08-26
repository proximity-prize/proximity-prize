import ProximityPrize.SubmissionLower.BCHKSDerivativeLowering6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSTailoredRepeatedRepair6400

open BCHKSLocalValuation6400

/-!
Factor-tailored repair for repeated nonlinear owners at the score-6400
boundary.

If an irreducible factor `R` has local received-line orders `nu_i`, a repair
line only has to reproduce those orders at coordinates where `nu_i > 0`.
Writing

`b = #{i : nu_i > 0}` and `t = sum_i (nu_i - 1)`,

one first builds a scaled received line on the `b` relevant coordinates and
then multiplies it by the extra locator of degree `t`.  In the worst case
`b <= n`, the sharp tail-kernel line has multiplier overhead `87382`; hence
the profile line has

* leading-coefficient degree at most `87382 + t`, and
* `(1,k)` weight at most `218453 + t`.

Replacing `R^e` by

`(d M R - H * dR/dY) * H^(e-1)`

preserves every local interpolation order and lowers the `Y` degree.  The
arithmetic below proves that the global `87382` root-count margin pays for
this replacement for every `e >= 2` when `t <= 21844`.  In particular every
simple-profile repeated nonlinear factor (`t=0`) is covered.  The remaining
hole is now explicitly the high-ramification class `t >= 21845`; no purity or
specialization-stability assumption is hidden here.
-/

def repeatedRepairK6400 : ℕ := 131071
def repeatedRepairGlobalMargin6400 : ℕ := 87382
def repeatedRepairTailOverhead6400 : ℕ := 87382
def repeatedRepairLineWeight6400 : ℕ := 218453
def repeatedRepairExcessCap6400 : ℕ := 21844

lemma repeatedRepairLineWeight_eq6400 :
    repeatedRepairLineWeight6400 =
      repeatedRepairK6400 + repeatedRepairTailOverhead6400 := by
  norm_num [repeatedRepairLineWeight6400, repeatedRepairK6400,
    repeatedRepairTailOverhead6400]

lemma repeatedRepairExcessCutoff_eq6400 :
    repeatedRepairTailOverhead6400 + repeatedRepairExcessCap6400 = 109226 ∧
      repeatedRepairLineWeight6400 + repeatedRepairExcessCap6400 = 240297 ∧
      240297 + 21845 = 2 * repeatedRepairK6400 ∧
      109226 = repeatedRepairGlobalMargin6400 + 21844 := by
  norm_num [repeatedRepairTailOverhead6400, repeatedRepairExcessCap6400,
    repeatedRepairLineWeight6400, repeatedRepairK6400,
    repeatedRepairGlobalMargin6400]

/-- Local order of a nonzero power is exactly the corresponding multiple. -/
theorem localOrder_pow
    {A : Type*} [CommSemiring A] [IsDomain A]
    (R : Polynomial (Polynomial A)) (e nu : ℕ)
    (hR : R ≠ 0) (horder : localOrder R = nu) :
    localOrder (R ^ e) = e * nu := by
  induction e with
  | zero =>
      simp [localOrder, diagonalize]
  | succ e ih =>
      rw [pow_succ, localOrder_mul (pow_ne_zero e hR) hR, ih, horder]
      simp [Nat.succ_mul]

/-- Cancellation-safe repeated-factor replacement.  It is deliberately
stated using exact local order for `R` and only lower bounds for the two
replacement factors, which is the form delivered by the derivative lemma
and by a Hermite-profile received line. -/
theorem localVanish_repeated_replace
    {A : Type*} [CommSemiring A] [IsDomain A]
    {C R T H : Polynomial (Polynomial A)}
    {m nu e : ℕ}
    (he : 0 < e)
    (hC : C ≠ 0) (hR : R ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0)
    (hOld : LocalVanish (C * R ^ e) m)
    (hRorder : localOrder R = nu)
    (hTvan : LocalVanish T nu)
    (hHvan : LocalVanish H nu) :
    LocalVanish (C * (T * H ^ (e - 1))) m := by
  have hRpow : R ^ e ≠ 0 := pow_ne_zero e hR
  have hOld0 : C * R ^ e ≠ 0 := mul_ne_zero hC hRpow
  have hm : m <= localOrder C + e * nu := by
    have h := (localVanish_iff_le_localOrder hOld0 m).mp hOld
    rw [localOrder_mul hC hRpow, localOrder_pow R e nu hR hRorder] at h
    exact h
  have hTorder : nu <= localOrder T :=
    (localVanish_iff_le_localOrder hT nu).mp hTvan
  have hHorder : nu <= localOrder H :=
    (localVanish_iff_le_localOrder hH nu).mp hHvan
  have hHpow : H ^ (e - 1) ≠ 0 := pow_ne_zero _ hH
  have hnew0 : C * (T * H ^ (e - 1)) ≠ 0 :=
    mul_ne_zero hC (mul_ne_zero hT hHpow)
  apply (localVanish_iff_le_localOrder hnew0 m).mpr
  rw [localOrder_mul hC (mul_ne_zero hT hHpow),
    localOrder_mul hT hHpow,
    localOrder_pow H (e - 1) (localOrder H) hH rfl]
  have hepred : 1 + (e - 1) = e := by omega
  calc
    m <= localOrder C + e * nu := hm
    _ = localOrder C + (nu + (e - 1) * nu) := by
      rw [← hepred]
      simp [Nat.add_mul]
    _ <= localOrder C +
        (localOrder T + (e - 1) * localOrder H) := by
      exact Nat.add_le_add_left
        (Nat.add_le_add hTorder (Nat.mul_le_mul_left _ hHorder)) _

/-- All simple local profiles are safely inside the global margin.  The
statement is the exact weight ledger: `w` is the weight of `R`, `ell` the
tail-kernel overhead, and `e` its multiplicity in the interpolant. -/
theorem simpleRepeatedRepair_weight_fits6400
    (e w ell : ℕ) (he : 2 <= e)
    (hw : 2 * repeatedRepairK6400 <= w)
    (hell : ell <= repeatedRepairTailOverhead6400) :
    w + ell + (e - 1) * (repeatedRepairK6400 + ell) <=
      e * w + repeatedRepairGlobalMargin6400 := by
  have hline : repeatedRepairK6400 + ell <= w := by
    norm_num [repeatedRepairK6400,
      repeatedRepairTailOverhead6400] at hw hell ⊢
    omega
  have hmul := Nat.mul_le_mul_left (e - 1) hline
  have heq : 1 + (e - 1) = e := by omega
  calc
    w + ell + (e - 1) * (repeatedRepairK6400 + ell)
        <= w + repeatedRepairGlobalMargin6400 + (e - 1) * w := by
      exact Nat.add_le_add
        (Nat.add_le_add_left
          (hell.trans (le_rfl : repeatedRepairTailOverhead6400 <=
            repeatedRepairGlobalMargin6400)) w) hmul
    _ = (1 + (e - 1)) * w + repeatedRepairGlobalMargin6400 := by ring
    _ = e * w + repeatedRepairGlobalMargin6400 := by rw [heq]

/-- Ramification excess up to `21844` is also paid for.  At the endpoint the
profile-line leading overhead is `109226`, while its weight is `240297`, at
least `21845` below the minimum nonlinear factor weight `2k=262142`.  One
copy of that gap reduces the net cost to `87381`, strictly below the global
margin `87382`; further copies only help. -/
theorem ramifiedRepeatedRepair_weight_fits6400
    (e w ell t : ℕ) (he : 2 <= e)
    (hw : 2 * repeatedRepairK6400 <= w)
    (hell : ell <= repeatedRepairTailOverhead6400)
    (ht : t <= repeatedRepairExcessCap6400) :
    w + (ell + t) +
        (e - 1) * (repeatedRepairK6400 + ell + t) <=
      e * w + repeatedRepairGlobalMargin6400 := by
  have hover : ell + t <= 109226 := by
    norm_num [repeatedRepairTailOverhead6400,
      repeatedRepairExcessCap6400] at hell ht ⊢
    omega
  have hline : repeatedRepairK6400 + ell + t + 21845 <= w := by
    norm_num [repeatedRepairK6400] at hw ⊢
    omega
  have hepred : 1 <= e - 1 := by omega
  have hmul := Nat.mul_le_mul_left (e - 1) hline
  have hmul' :
      (e - 1) * (repeatedRepairK6400 + ell + t) +
          (e - 1) * 21845 <= (e - 1) * w := by
    simpa [Nat.mul_add] using hmul
  have hgain : 21845 <= (e - 1) * 21845 := by
    nlinarith
  have hpaid :
      (e - 1) * (repeatedRepairK6400 + ell + t) + 21845 <=
        (e - 1) * w := by
    omega
  have hover' :
      ell + t <= repeatedRepairGlobalMargin6400 + 21844 := by
    norm_num [repeatedRepairGlobalMargin6400] at hover ⊢
    exact hover
  have hcore :
      ell + t + (e - 1) * (repeatedRepairK6400 + ell + t) <=
        (e - 1) * w + repeatedRepairGlobalMargin6400 := by
    omega
  have heq : 1 + (e - 1) = e := by omega
  calc
    w + (ell + t) +
          (e - 1) * (repeatedRepairK6400 + ell + t)
        = w + (ell + t +
          (e - 1) * (repeatedRepairK6400 + ell + t)) := by omega
    _ <= w + ((e - 1) * w + repeatedRepairGlobalMargin6400) :=
      Nat.add_le_add_left hcore w
    _ = (1 + (e - 1)) * w + repeatedRepairGlobalMargin6400 := by ring
    _ = e * w + repeatedRepairGlobalMargin6400 := by rw [heq]

/-- The cutoff is honest: using only the worst-case degree bounds, increasing
`t` by one reaches the full `87382` margin exactly.  Thus `21845` cannot be
included in a strict-margin argument without another source of slack. -/
lemma ramifiedRepeatedRepair_next_is_boundary6400 :
    (87382 + 21845) + (repeatedRepairLineWeight6400 + 21845) -
        2 * repeatedRepairK6400 =
      repeatedRepairGlobalMargin6400 + 1 := by
  norm_num [repeatedRepairK6400, repeatedRepairLineWeight6400,
    repeatedRepairGlobalMargin6400]

end BCHKSTailoredRepeatedRepair6400
end ProximityPrize.SubmissionLower
