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
end Wide50EulerPrimary
