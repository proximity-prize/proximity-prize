import ProximityPrize.SubmissionLower.LocatorFixedStage
import ProximityPrize.SubmissionLower.LocatorHybridCost

/-!
# The identity branch is dominated by the hybrid cost

On the hybrid branch (`padB ≥ 1`) the identity-curve count
`(n - w) * (errors + 1) * identityCurveDegree flag a b s w / gap` is at most the
hybrid Bezout bound.  This is an exact polynomial identity with a
subtraction-free slack, in the style of `LocatorFixedStage.identity_budget_exact`.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridIdentity

open RCN095 RCN146 LocatorFactorAggregate LocatorHybridCost LocatorFixedStage RCN198

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Subtraction-free tails in the support coordinates `a, b, s` with `b = b' + 1`. -/
def sharpABS (a b s : ℕ) : FlagDegree :=
  ⟨2 * a * 131072, 1 + (2 * b + 1) * 131072, (2 * s + 3) * 131072⟩
def rationalABS (a b s : ℕ) : FlagDegree :=
  ⟨131072 * a + 2 * a, 131072 * b + 2 * b + 2, 131072 * s + 2 * s + 3⟩
def hybABS (a b s : ℕ) : FlagDegree := rationalABS a b s + ⟨0, 65536, 196608⟩
def mfibABS (a b s : ℕ) : FlagDegree := ⟨a, b + 1, s + 3⟩
def mcutABS (a b s : ℕ) : FlagDegree := rationalABS a b s + ⟨0, 131072, 262144⟩
def hybridCostABS (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed flag (sharpABS a b s) (hybABS a b s) +
    131072 * flagMixed flag (mfibABS a b s) (mcutABS a b s)

theorem tails_eq (p : FlagDegree) :
    sharpTail p = sharpABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    hybridCoordinate p = hybABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    movingFiber p = mfibABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    movingCut p = mcutABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) := by
  have h := pad_bounds p
  generalize hS : padS p = sP at h ⊢
  generalize hY : padY p = yP at h ⊢
  generalize hT : padT p = tP at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : 2 * (yP - sP) - 1 = 2 * (yP - sP - 1) + 1 := by omega
    have e2 : 2 * sP - 1 = 2 * (sP - 2) + 3 := by omega
    simp only [sharpTail, sharpABS, hS, hY, hT, e1, e2]
  · simp only [hybridCoordinate, rationalFlag, hybABS, rationalABS, hS, hY, hT]
  · have e1 : yP - sP = yP - sP - 1 + 1 := by omega
    have e2 : sP + 1 = sP - 2 + 3 := by omega
    simp only [movingFiber, mfibABS, hS, hY, hT, FlagDegree.mk.injEq]
    exact ⟨trivial, e1, e2⟩
  · simp only [movingCut, rationalFlag, mcutABS, rationalABS, hS, hY, hT]

theorem hybridCost_eq_abs (p : FlagDegree) (flag : FlagDegree) :
    flagMixed flag (sharpTail p) (hybridCoordinate p) +
        131072 * flagMixed flag (movingFiber p) (movingCut p) =
      hybridCostABS flag (padT p - padY p) (padY p - padS p - 1) (padS p - 2) := by
  have h := tails_eq p
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  rfl

/-- Slack polynomials for `errors = 80555` (`b = b' + 1`). -/
def hybridSlackZ (a b s : ℕ) : ℕ :=
  21451332007010302 + 15458111287399764 * s + 9546957997211648 * b +
    2603717623283712 * s ^ 2 + 5207435246567424 * b * s
def hybridSlackYZ (a b s : ℕ) : ℕ :=
  17299444028993530 + 12690185968721916 * s + 9546957997211648 * b + 9546957997211648 * a +
    2603717623283712 * s ^ 2 + 5207435246567424 * b * s + 5207435246567424 * a * s
def hybridSlackAll (a b s : ℕ) : ℕ :=
  16372876685094898 + 12690185968721916 * s + 12690185968721916 * b + 15458111287399764 * a +
    2603717623283712 * s ^ 2 + 5207435246567424 * b * s + 2603717623283712 * b ^ 2 +
    5207435246567424 * a * s + 5207435246567424 * a * b
def hybridSlack (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flag.zOnly * hybridSlackZ a b s + flag.yz * hybridSlackYZ a b s +
    flag.all * hybridSlackAll a b s

theorem hybrid_identity_exact (flag : FlagDegree) (a b s : ℕ) :
    gap * hybridCostABS flag a (b + 1) s =
      (n - w) * (errors + 1) * identityCurveDegree flag a (b + 1) s w +
        hybridSlack flag a b s := by
  rw [identityDegree_linear]
  norm_num [hybridCostABS, sharpABS, hybABS, rationalABS, mfibABS, mcutABS, w, n, errors, gap,
    hybridSlack, hybridSlackZ, hybridSlackYZ, hybridSlackAll, flagMixed,
    add_zOnly, add_yz, add_all]
  ring

theorem identity_le_hybrid (flag : FlagDegree) (a b s : ℕ) (hb : 1 ≤ b) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * hybridCostABS flag a b s := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [hybrid_identity_exact]
  exact Nat.le_add_right _ _

end ProximityPrize.SubmissionLower.LocatorHybridIdentity
