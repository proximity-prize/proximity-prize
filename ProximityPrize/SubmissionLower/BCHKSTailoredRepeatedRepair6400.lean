import ProximityPrize.SubmissionLower.BCHKSDerivativeLowering6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSTailoredRepeatedRepair6400
open BCHKSLocalValuation6400
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
lemma ramifiedRepeatedRepair_next_is_boundary6400 :
    (87382 + 21845) + (repeatedRepairLineWeight6400 + 21845) -
        2 * repeatedRepairK6400 =
      repeatedRepairGlobalMargin6400 + 1 := by
  norm_num [repeatedRepairK6400, repeatedRepairLineWeight6400,
    repeatedRepairGlobalMargin6400]
end BCHKSTailoredRepeatedRepair6400
end ProximityPrize.SubmissionLower
