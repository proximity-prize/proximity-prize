import ProximityPrize.SubmissionLower.PrimaryTaperBudget

set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Wide50EulerPrimary
open K1_13_2 K1_13_2_3
open scoped BigOperators

private def reduceFlag (F : Flag) (a b : ℕ) : Flag :=
  ⟨F.degree - a - b, F.lower - 3*b, F.upper - 3*b,
    F.cap - b, F.order - 2*b⟩

private theorem residual_eq (F : Flag) (a b : ℕ) :
    residualFlag F (Powers.expand ⟨a,b,0⟩) = reduceFlag F a b := by
  simp [residualFlag, reduceFlag, factorFlag, Powers.expand, Fin.sum_univ_succ, sub_sub]
  constructor <;> ring

/-- Two residual factors give a direct arithmetic formula for one compact block. -/
def twoFactorBound (k : ℕ) (i : BlockIndex) (a b : ℕ) : ℕ :=
  let F := TaperNormalize.initialFlag k i
  if F.order ≤ 0 then 0 else
    let active := oldCount (TaperNormalize.activeFlag k i)
    let lower := max 0 (max (kernelLower F) (kernelLower (reduceFlag F a b)))
    (min active (oldCount F - lower)).toNat

theorem twoFactorBound_eq (k : ℕ) (i : BlockIndex) (a b : ℕ) :
    twoFactorBound k i a b = TaperNormalize.bound k i (Powers.expand ⟨a,b,0⟩) := by
  simp only [twoFactorBound, TaperNormalize.bound, residual_eq]
def denN (u : ℕ) : ℕ :=
  let q := u / 6
  let r := u % 6
  1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)

def dd (a b : ℕ) : ℕ := if b ≤ a then denN (a - b) else 0

theorem den_alg (q r : ℕ) (hr : r < 6) :
    (1 + (r:ℤ)*(r+1)/2 + q*(22+7*r+ r*(r-1)/2) + (57+6*r)*(q*(q-1)/2) + 6*q*(q-1)*(q-2) : ℤ) =
    ((1 + r*(r+1)/2 + q*(22+7*r+r*(r-1)/2) + (57+6*r)*(q*(q-1)/2) + 6*q*(q-1)*(q-2) : ℕ):ℤ) := by
  interval_cases r <;> rcases q with _ | _ | _ | q <;> simp <;> omega

theorem denominator_nat (v c : ℕ) : denominator ((v : ℤ) - c) = ((dd v c : ℕ) : ℤ) := by
  unfold dd
  by_cases h : c ≤ v
  · rw [if_pos h]
    have e : (v : ℤ) - c = ((v - c : ℕ) : ℤ) := by omega
    rw [e]
    generalize v - c = u
    unfold denominator denN
    rw [if_neg (by omega)]
    have hq : ((u:ℤ)/6) = ((u/6 : ℕ):ℤ) := by omega
    have hr : ((u:ℤ)%6) = ((u%6 : ℕ):ℤ) := by omega
    simp only [hq, hr]
    exact den_alg (u/6) (u%6) (by omega)
  · rw [if_neg h]
    unfold denominator
    rw [if_pos (by omega)]
    rfl

def cumP (d u : ℕ) : ℤ :=
  let v := min u (3*d)
  ((denN v + dd v (2*d+3) + dd v (2*d+4) + dd v (2*d+5) : ℕ) : ℤ) -
    ((dd v (d+1) + dd v (d+2) + dd v (d+3) + dd v (3*d+6) : ℕ) : ℤ)
def cumI (d u : ℤ) : ℤ := if d < 0 || u < 0 then 0 else cumP d.toNat u.toNat

theorem dd_zero (v : ℕ) : dd v 0 = denN v := by simp [dd]

theorem cumulative_eq (d u : ℤ) : cumulative d u = cumI d u := by
  unfold cumulative cumI
  by_cases h : d < 0 || u < 0
  · simp [h]
  · rw [if_neg h, if_neg h]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h
    obtain ⟨hd, hu⟩ := h
    obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le hd
    obtain ⟨u', rfl⟩ := Int.eq_ofNat_of_zero_le hu
    simp only [Int.toNat_natCast]
    unfold cumP
    have hv : min (u' : ℤ) (3 * (d' : ℤ)) = ((min u' (3*d' ) : ℕ) : ℤ) := by push_cast; rfl
    rw [hv]
    generalize min u' (3*d') = v
    have e0 := denominator_nat v 0
    have e1 := denominator_nat v (d'+1)
    have e2 := denominator_nat v (d'+2)
    have e3 := denominator_nat v (d'+3)
    have e4 := denominator_nat v (2*d'+3)
    have e5 := denominator_nat v (2*d'+4)
    have e6 := denominator_nat v (2*d'+5)
    have e7 := denominator_nat v (3*d'+6)
    push_cast at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
    rw [dd_zero] at e0
    simp only [sub_zero] at e0
    have a1 : (v:ℤ) - d' - 1 = v - (d' + 1) := by ring
    have a2 : (v:ℤ) - d' - 2 = v - (d' + 2) := by ring
    have a3 : (v:ℤ) - d' - 3 = v - (d' + 3) := by ring
    have a4 : (v:ℤ) - 2*d' - 3 = v - (2*d' + 3) := by ring
    have a5 : (v:ℤ) - 2*d' - 4 = v - (2*d' + 4) := by ring
    have a6 : (v:ℤ) - 2*d' - 5 = v - (2*d' + 5) := by ring
    have a7 : (v:ℤ) - 3*d' - 6 = v - (3*d' + 6) := by ring
    rw [a1, a2, a3, a4, a5, a6, a7, e0, e1, e2, e3, e4, e5, e6, e7]
    push_cast
    ring

def cappedCountI (d u cap : ℤ) : ℤ :=
  if cap < 0 then 0 else cumI d u - cumI (d - cap - 1) (u - 3 * (cap + 1))
theorem cappedCount_eq : cappedCount = cappedCountI := by
  funext d u cap
  simp only [cappedCount, cappedCountI, cumulative_eq]
def oldCountI (F : Flag) : ℤ :=
  cappedCountI F.degree F.upper F.cap -
    cappedCountI F.degree (min F.upper (F.lower - 1)) F.cap
theorem oldCount_eq : oldCount = oldCountI := by
  funext F
  simp only [oldCount, oldCountI, cappedCount_eq]
def targetCountI (F : Flag) : ℤ :=
  let balance := F.order - 1 - F.lower + F.degree
  if balance < 0 then 0 else
    let removed := min F.degree (balance / 4) + 1
    cumI F.degree (F.order - 1) - cumI (F.degree - removed) (F.order - 1 - 3 * removed) -
      cumI F.degree (F.lower - 1) + cumI (F.degree - removed) (F.lower - 1)
theorem targetCount_eq : targetCount = targetCountI := by
  funext F
  simp only [targetCount, targetCountI, cumulative_eq]
def kernelLowerI (F : Flag) : ℤ :=
  if F.degree < 0 || F.upper < 0 || F.cap < 0 then 0 else oldCountI F - targetCountI F
theorem kernelLower_eq : kernelLower = kernelLowerI := by
  funext F
  simp only [kernelLower, kernelLowerI, oldCount_eq, targetCount_eq]

def twoFactorBoundI (k : ℕ) (i : BlockIndex) (a b : ℕ) : ℕ :=
  let F := TaperNormalize.initialFlag k i
  if F.order ≤ 0 then 0 else
    let active := oldCountI (TaperNormalize.activeFlag k i)
    let lower := max 0 (max (kernelLowerI F) (kernelLowerI (reduceFlag F a b)))
    (min active (oldCountI F - lower)).toNat

theorem twoFactorBoundI_eq (k : ℕ) (i : BlockIndex) (a b : ℕ) :
    twoFactorBoundI k i a b = twoFactorBound k i a b := by
  simp only [twoFactorBoundI, twoFactorBound, oldCount_eq, kernelLower_eq]

end Wide50EulerPrimary
