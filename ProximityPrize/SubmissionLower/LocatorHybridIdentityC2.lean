/-
THE IDENTITY BRANCH IS DOMINATED BY THE C2 HYBRID COST — 6787 ROW.

Self-contained in its row constants (errors 80624, agreements 181520,
gap 50449), so it does not inherit whatever `LocatorFixedStage` currently
carries.

C2 tails: first tail `reducedABS` (the reduced agreement flag at `w + 1`,
equal to `paddedTail p 131072`), coordinate `rationalABS`, moving factor
`131076 = w + 5`.

The slack polynomials were regenerated for errors = 80624 against the C2 cost
and are subtraction-free, so `identity_le_hybridC2` is `Nat.le_add_right`.
-/
import ProximityPrize.SubmissionLower.LocatorHybridCostC2
import ProximityPrize.SubmissionLower.LocatorFixedStage

namespace ProximityPrize.SubmissionLower.LocatorHybridIdentityC2

open RCN095 RCN146 RCN203 RCN206 LocatorFactorAggregate LocatorHybridCost
open LocatorHybridCostC1 LocatorHybridCostC2 RCN198

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! ### Row constants for 6787 -/

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80624
def agreements : ℕ := 181520
def gap : ℕ := 50449

theorem row_arithmetic : n - errors = agreements ∧ agreements - w = gap := by
  refine ⟨?_, ?_⟩ <;> norm_num [n, errors, agreements, w, gap]

/-- Local restatement of `LocatorFixedStage.identityDegree_linear`. -/
theorem identityDegree_linear (flag : FlagDegree) (a b s : ℕ) :
    identityCurveDegree flag a b s w =
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s) := by
  simp only [identityCurveDegree, paddedCut,
    RCN206.centreFlag, RCN206.directionFlag,
    flagMixed, unitZFlag, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all, w]
  ring

/-! ### Subtraction-free C2 tails in the support coordinates `a, b, s` -/

/-- The reduced first tail at `w + 1 = 131072`. -/
def reducedABS (a b s : ℕ) : FlagDegree :=
  ⟨2 * a * 131072, 1 + (2 * b + 2) * 131072, (2 * s + 2) * 131072⟩
def rationalABS (a b s : ℕ) : FlagDegree :=
  ⟨131072 * a + 2 * a, 131072 * b + 2 * b + 2, 131072 * s + 2 * s + 3⟩
def mfibABS (a b s : ℕ) : FlagDegree := ⟨a, b + 1, s + 3⟩
def mcutABS (a b s : ℕ) : FlagDegree := rationalABS a b s + ⟨0, 131072, 262144⟩

def hybridCostABSC2 (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed flag (reducedABS a b s) (rationalABS a b s) +
    131076 * flagMixed flag (mfibABS a b s) (mcutABS a b s)

theorem tails_eqC2 (p : FlagDegree) :
    reducedTail p = reducedABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    hybridCoordinateC1 p =
      rationalABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    movingFiber p = mfibABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) ∧
    movingCut p = mcutABS (padT p - padY p) (padY p - padS p - 1) (padS p - 2) := by
  have h := pad_bounds p
  generalize hS : padS p = sP at h ⊢
  generalize hY : padY p = yP at h ⊢
  generalize hT : padT p = tP at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : 2 * (yP - sP) = 2 * (yP - sP - 1) + 2 := by omega
    have e2 : 2 * (sP - 1) = 2 * (sP - 2) + 2 := by omega
    simp only [reducedTail, paddedTail, reducedABS, hS, hY, hT, e1, e2]
  · simp only [hybridCoordinateC1, rationalFlag, rationalABS, hS, hY, hT]
  · have e1 : yP - sP = yP - sP - 1 + 1 := by omega
    have e2 : sP + 1 = sP - 2 + 3 := by omega
    simp only [movingFiber, mfibABS, hS, hY, hT, FlagDegree.mk.injEq]
    exact ⟨trivial, e1, e2⟩
  · simp only [movingCut, rationalFlag, mcutABS, rationalABS, hS, hY, hT]

theorem hybridCostC2_eq_abs (p : FlagDegree) (flag : FlagDegree) :
    flagMixed flag (reducedTail p) (hybridCoordinateC1 p) +
        131076 * flagMixed flag (movingFiber p) (movingCut p) =
      hybridCostABSC2 flag (padT p - padY p) (padY p - padS p - 1)
        (padS p - 2) := by
  have h := tails_eqC2 p
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  rfl

/-! ### Slack polynomials for `errors = 80624` (regenerated for the C2 cost) -/

def hybridSlackZC2 (b s : ℕ) : ℕ :=
  11446059365548428 +
    11964255570717892 * s +
    2600187786307720 * s ^ 2 +
    6067208430663268 * b +
    5200375572615440 * b * s

def hybridSlackYZC2 (a b s : ℕ) : ℕ :=
  7290615100346553 +
    9193959393916642 * s +
    2600187786307720 * s ^ 2 +
    6067208430663268 * b +
    5200375572615440 * b * s +
    6067208430663268 * a +
    5200375572615440 * a * s

def hybridSlackAllC2 (a b s : ℕ) : ℕ :=
  5913634310451093 +
    9193959393916642 * s +
    2600187786307720 * s ^ 2 +
    9193959393916642 * b +
    5200375572615440 * b * s +
    2600187786307720 * b ^ 2 +
    11964255570717892 * a +
    5200375572615440 * a * s +
    5200375572615440 * a * b

def hybridSlackC2 (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flag.zOnly * hybridSlackZC2 b s + flag.yz * hybridSlackYZC2 a b s +
    flag.all * hybridSlackAllC2 a b s

theorem hybrid_identity_exactC2 (flag : FlagDegree) (a b s : ℕ) :
    gap * hybridCostABSC2 flag a (b + 1) s =
      (n - w) * (errors + 1) * identityCurveDegree flag a (b + 1) s w +
        hybridSlackC2 flag a b s := by
  rw [identityDegree_linear]
  norm_num [hybridCostABSC2, reducedABS, rationalABS, mfibABS, mcutABS,
    w, n, errors, gap, hybridSlackC2, hybridSlackZC2, hybridSlackYZC2,
    hybridSlackAllC2, flagMixed, add_zOnly, add_yz, add_all]
  ring

theorem identity_le_hybridC2 (flag : FlagDegree) (a b s : ℕ) (hb : 1 ≤ b) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * hybridCostABSC2 flag a b s := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [hybrid_identity_exactC2]
  exact Nat.le_add_right _ _

end ProximityPrize.SubmissionLower.LocatorHybridIdentityC2
