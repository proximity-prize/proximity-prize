import ProximityPrize.SubmissionLower.LocatorFactorAggregate
import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.LocatorChannelClosed
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.LocatorHybridCost
import ProximityPrize.SubmissionLower.LocatorHybridCostC2

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

open RCN095 RCN260 LocatorFactorAggregate LocatorLowQuotient

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private abbrev prime : ℕ := 2130706433
abbrev bound : ℕ := 263528531609206492
abbrev totalCap : ℕ := 3806
abbrev ysCap : ℕ := 102
abbrev slopeCap : ℕ := 21
private abbrev delta : ℕ := 50460
abbrev wY : ℕ := 0
abbrev wS : ℕ := 5
abbrev capSum : ℕ := totalCap + wY * ysCap + wS * slopeCap
/-- Maximum admissible repeated-projection depth for a source route. -/
abbrev routeCap : ℕ := 14

/-- A rectangular cumulative-degree box for one irreducible factor. -/
structure Box where
  r : ℕ
  ylo : ℕ
  yhi : ℕ
  tlo : ℕ
  thi : ℕ
  deriving DecidableEq

def Box.valid (b : Box) : Prop :=
  1 ≤ b.r ∧ b.r ≤ b.ylo ∧ b.ylo ≤ b.yhi ∧ b.yhi ≤ ysCap ∧
    b.ylo ≤ b.thi ∧ b.tlo ≤ b.thi ∧ b.thi ≤ totalCap

instance (b : Box) : Decidable b.valid := by unfold Box.valid; infer_instance

def Box.factorY (b : Box) : ℕ := min b.yhi b.thi
def Box.factorT (b : Box) : ℕ := max b.tlo b.ylo
def Box.ordinaryCap (b : Box) : FlagDegree := cap b.thi b.factorY b.r
def Box.ordinaryCost (b : Box) : ℕ :=
  if 3 ≤ b.r ∧ b.r + 2 ≤ b.ylo then
    min (LocatorHybridCostC2.hybridCostC2 b.ordinaryCap)
      (paddedCost 131072 131073 b.ordinaryCap)
  else paddedCost 131072 131073 b.ordinaryCap
def Box.weight (b : Box) : ℕ := b.factorT + wY * b.ylo + wS * b.r
def Box.ordinaryFits (b : Box) : Prop :=
  capSum * b.ordinaryCost ≤ bound * b.weight

instance (b : Box) : Decidable b.ordinaryFits := by
  unfold Box.ordinaryFits; infer_instance

/-- Arithmetic data for a kernel source embedded in the common ambient box. -/
structure Source where
  length : ℕ
  y : ℕ
  r : ℕ
  gap : ℕ
  deriving DecidableEq

def sourceA : Source := ⟨278867, 102, 21, 139502⟩
def sourceAux : Source := ⟨89400, 101, 22, 589927⟩
def sourceC : Source := ⟨130000, 394, 85, 538299882917330⟩
def sourceH1 : Source := ⟨350000, 491, 105, 3012828511088025⟩
def sourceH2 : Source := ⟨1000000, 692, 150, 26566017386262297⟩
def sourceH3 : Source := ⟨350000, 1121, 243, 40851803364289489⟩
def sourceH4 : Source := ⟨675716, 1689, 365, 279332634054767245⟩
def sourceH5 : Source := ⟨669072, 1038, 225, 62656658130794421⟩
def sourceH6 : Source := ⟨219707, 1038, 225, 19852261700439561⟩

def stageT (src : Source) (b : Box) (j : ℕ) : ℕ := src.length - j * b.factorT
def stageY (src : Source) (b : Box) (j : ℕ) : ℕ := src.y - j * b.ylo
def stageR (src : Source) (b : Box) (j : ℕ) : ℕ := src.r - j * b.r

def stageBand (src : Source) (b : Box) (j : ℕ) : ℕ :=
  delta * (if stageY src b j ≤ stageT src b j then
      LocatorChannelClosed.fastChannel
        (stageT src b j) (stageY src b j) (stageR src b j)
    else channelCount (stageT src b j) (stageY src b j) (stageR src b j))

/-- The fast branch is the same number: every grid stage has `stageY ≤ stageT`,
and off that branch the definition is the loop itself. -/
theorem stageBand_eq (src : Source) (b : Box) (j : ℕ) :
    stageBand src b j
      = delta * channelCount
          (stageT src b j) (stageY src b j) (stageR src b j) := by
  unfold stageBand
  by_cases h : stageY src b j ≤ stageT src b j
  · rw [if_pos h, ← LocatorChannelClosed.channelCount_eq_fast _ _ _ h]
  · rw [if_neg h]

def bandSum (src : Source) (b : Box) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bandSum src b k + stageBand src b (k + 1)

def stagePair (src : Source) (b : Box) (j : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181530, b.factorY, b.r, b.thi,
    stageY src b j, stageR src b j, stageT src b j⟩

def PairGates (P : UnequalParameters) : Prop :=
  1 ≤ P.leftR ∧ P.leftY < prime ∧ P.leftR < prime ∧ P.leftZ < prime ∧
    P.mixedCost.y < prime ∧ P.mixedCost.r < prime ∧ P.mixedCost.z < prime

instance (P : UnequalParameters) : Decidable (PairGates P) := by
  unfold PairGates; infer_instance

def stageCost (src : Source) (b : Box) (j : ℕ) : ℕ :=
  (stagePair src b j).regularCountCap

def routeCost (src : Source) (b : Box) : ℕ → ℕ
  | 0 => 0
  | k + 1 => max (routeCost src b k) (stageCost src b (k + 1))

theorem stageCost_le_routeCost (src : Source) (b : Box) (j k : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) : stageCost src b j ≤ routeCost src b k := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact (ih (by omega)).trans (Nat.le_max_left _ _)
      · have : j = k + 1 := by omega
        subst this
        exact Nat.le_max_right _ _

def pairGatesThrough (src : Source) (b : Box) : ℕ → Prop
  | 0 => True
  | k + 1 => pairGatesThrough src b k ∧ PairGates (stagePair src b (k + 1))

instance (src : Source) (b : Box) : ∀ k : ℕ, Decidable (pairGatesThrough src b k)
  | 0 => by unfold pairGatesThrough; infer_instance
  | k + 1 => by
      have := instDecidablePairGatesThrough src b k
      unfold pairGatesThrough
      infer_instance

theorem pairGates_of_pairGatesThrough (src : Source) (b : Box) (j k : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) (h : pairGatesThrough src b k) :
    PairGates (stagePair src b j) := by
  induction k with
  | zero => omega
  | succ k ih =>
      obtain ⟨hprev, hlast⟩ := h
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact ih (by omega) hprev
      · have : j = k + 1 := by omega
        subst this
        exact hlast

def terminalCoprime (src : Source) (b : Box) (k : ℕ) : Prop :=
  stageT src b k < b.factorT ∨
    stageY src b k < b.ylo ∨ stageR src b k < b.r

instance (src : Source) (b : Box) (k : ℕ) :
    Decidable (terminalCoprime src b k) := by
  unfold terminalCoprime; infer_instance

def RouteFits (src : Source) (k : ℕ) (b : Box) : Prop :=
  1 ≤ k ∧ k ≤ 45 ∧
    k * b.ylo ≤ src.y ∧ k * b.r ≤ src.r ∧
    k * b.factorT + stageY src b k ≤ src.length ∧
    bandSum src b k < src.gap ∧ terminalCoprime src b k ∧
    pairGatesThrough src b k ∧
    capSum * routeCost src b k ≤ bound * b.weight

instance (src : Source) (k : ℕ) (b : Box) : Decidable (RouteFits src k b) := by
  unfold RouteFits; infer_instance

/-- A receipt-local propositionally equivalent presentation of `RouteFits`. -/
def FastRouteFits (src : Source) (k : ℕ) (b : Box) : Prop :=
  1 ≤ k ∧ k ≤ 45 ∧
    k * b.ylo ≤ src.y ∧ k * b.r ≤ src.r ∧
    k * b.factorT + stageY src b k ≤ src.length ∧
    terminalCoprime src b k ∧ bandSum src b k < src.gap ∧
    pairGatesThrough src b k ∧
    capSum * routeCost src b k ≤ bound * b.weight

instance (src : Source) (k : ℕ) (b : Box) : Decidable (FastRouteFits src k b) := by
  unfold FastRouteFits; infer_instance

theorem fastRouteFits_iff (src : Source) (k : ℕ) (b : Box) :
    FastRouteFits src k b ↔ RouteFits src k b := by
  constructor
  · rintro ⟨hkpos, hkcap, hy, hr, hlen, hterminal, hband, hgates, hcost⟩
    exact ⟨hkpos, hkcap, hy, hr, hlen, hband, hterminal, hgates, hcost⟩
  · rintro ⟨hkpos, hkcap, hy, hr, hlen, hband, hterminal, hgates, hcost⟩
    exact ⟨hkpos, hkcap, hy, hr, hlen, hterminal, hband, hgates, hcost⟩

/-- Direct coprime-pair parameters for an unconditional helper source. -/
def helperPair (src : Source) (b : Box) : UnequalParameters :=
  ⟨262144, 131071, 181530, b.factorY, b.r, b.thi,
    src.y, src.r, src.length⟩

def HelperFits (src : Source) (k : ℕ) (b : Box) : Prop :=
  RouteFits src k b ∧ PairGates (helperPair src b) ∧
    capSum * max (routeCost src b k) (helperPair src b).regularCountCap ≤
      bound * b.weight

instance (src : Source) (k : ℕ) (b : Box) : Decidable (HelperFits src k b) := by
  unfold HelperFits
  infer_instance

def FastHelperFits (src : Source) (k : ℕ) (b : Box) : Prop :=
  FastRouteFits src k b ∧ PairGates (helperPair src b) ∧
    capSum * max (routeCost src b k) (helperPair src b).regularCountCap ≤
      bound * b.weight

instance (src : Source) (k : ℕ) (b : Box) :
    Decidable (FastHelperFits src k b) := by
  unfold FastHelperFits
  infer_instance

theorem fastHelperFits_iff (src : Source) (k : ℕ) (b : Box) :
    FastHelperFits src k b ↔ HelperFits src k b := by
  simp only [FastHelperFits, HelperFits, fastRouteFits_iff]

/-- Walk up to the first depth at which the route terminates, and accept it
only there.  Beyond that depth every ingredient of `RouteFits` moves the wrong
way -- the band sum grows, the stage cost is a max over more stages, and the
gate chain is a longer conjunction -- so a deeper terminal depth can never fit
when the first one does not.  Only soundness is proved here; completeness is
what the row receipts witness. -/
def routeDepthAux (src : Source) (b : Box) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, n + 1 =>
      if terminalCoprime src b k then
        (if FastRouteFits src k b then k else 0)
      else routeDepthAux src b (k + 1) n

def routeDepth (src : Source) (b : Box) : ℕ := routeDepthAux src b 1 routeCap

theorem routeDepthAux_spec (src : Source) (b : Box) (n : ℕ) :
    ∀ k, routeDepthAux src b k n ≠ 0 →
      RouteFits src (routeDepthAux src b k n) b := by
  induction n with
  | zero =>
      intro k h
      simp only [routeDepthAux, ne_eq, not_true_eq_false] at h
  | succ n ih =>
      intro k h
      simp only [routeDepthAux] at h ⊢
      by_cases hterm : terminalCoprime src b k
      · rw [if_pos hterm] at h ⊢
        by_cases hfit : FastRouteFits src k b
        · rw [if_pos hfit]
          exact (fastRouteFits_iff src k b).mp hfit
        · rw [if_neg hfit] at h
          exact absurd rfl h
      · rw [if_neg hterm] at h ⊢
        exact ih (k + 1) h

theorem routeDepth_spec (src : Source) (b : Box) (h : routeDepth src b ≠ 0) :
    RouteFits src (routeDepth src b) b :=
  routeDepthAux_spec src b routeCap 1 h

def CFits (b : Box) : Prop := routeDepth sourceC b ≠ 0

instance (b : Box) : Decidable (CFits b) := by unfold CFits; infer_instance

/-- Search one short explicit depth interval for the first helper route that
passes both its divisor route and its unconditional direct-pair charge. -/
def helperDepthAux (src : Source) (b : Box) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, n + 1 =>
      if FastHelperFits src k b then k else helperDepthAux src b (k + 1) n

theorem helperDepthAux_spec (src : Source) (b : Box) (n : ℕ) :
    ∀ k, helperDepthAux src b k n ≠ 0 →
      HelperFits src (helperDepthAux src b k n) b := by
  induction n with
  | zero =>
      intro k h
      simp only [helperDepthAux, ne_eq, not_true_eq_false] at h
  | succ n ih =>
      intro k h
      simp only [helperDepthAux] at h ⊢
      by_cases hfit : FastHelperFits src k b
      · rw [if_pos hfit]
        exact (fastHelperFits_iff src k b).mp hfit
      · rw [if_neg hfit] at h ⊢
        exact ih (k + 1) h

theorem helperDepthAux_bounds (src : Source) (b : Box) (n : ℕ) :
    ∀ k, helperDepthAux src b k n ≠ 0 →
      k ≤ helperDepthAux src b k n ∧ helperDepthAux src b k n < k + n := by
  induction n with
  | zero =>
      intro k h
      simp only [helperDepthAux, ne_eq, not_true_eq_false] at h
  | succ n ih =>
      intro k h
      simp only [helperDepthAux] at h ⊢
      by_cases hfit : FastHelperFits src k b
      · rw [if_pos hfit]
        omega
      · rw [if_neg hfit] at h ⊢
        have hb := ih (k + 1) h
        omega

def helperDepthH1 (b : Box) : ℕ := helperDepthAux sourceH1 b 10 4
def helperDepthH2 (b : Box) : ℕ := helperDepthAux sourceH2 b 14 5
def helperDepthH3 (b : Box) : ℕ := helperDepthAux sourceH3 b 26 5
def helperDepthH4 (b : Box) : ℕ := helperDepthAux sourceH4 b 43 3
def helperDepthH5 (b : Box) : ℕ := helperDepthAux sourceH5 b 28 1
def helperDepthH6 (b : Box) : ℕ := helperDepthAux sourceH6 b 25 3

def H1Fits (b : Box) : Prop := helperDepthH1 b ≠ 0
def H2Fits (b : Box) : Prop := helperDepthH2 b ≠ 0
def H3Fits (b : Box) : Prop := helperDepthH3 b ≠ 0
def H4Fits (b : Box) : Prop := helperDepthH4 b ≠ 0
def H5Fits (b : Box) : Prop := helperDepthH5 b ≠ 0
def H6Fits (b : Box) : Prop := helperDepthH6 b ≠ 0

instance (b : Box) : Decidable (H1Fits b) := by unfold H1Fits; infer_instance
instance (b : Box) : Decidable (H2Fits b) := by unfold H2Fits; infer_instance
instance (b : Box) : Decidable (H3Fits b) := by unfold H3Fits; infer_instance
instance (b : Box) : Decidable (H4Fits b) := by unfold H4Fits; infer_instance
instance (b : Box) : Decidable (H5Fits b) := by unfold H5Fits; infer_instance
instance (b : Box) : Decidable (H6Fits b) := by unfold H6Fits; infer_instance

theorem helperDepthH1_spec (b : Box) (h : H1Fits b) :
    HelperFits sourceH1 (helperDepthH1 b) b :=
  helperDepthAux_spec sourceH1 b 4 10 h

theorem helperDepthH2_spec (b : Box) (h : H2Fits b) :
    HelperFits sourceH2 (helperDepthH2 b) b :=
  helperDepthAux_spec sourceH2 b 5 14 h

theorem helperDepthH3_spec (b : Box) (h : H3Fits b) :
    HelperFits sourceH3 (helperDepthH3 b) b :=
  helperDepthAux_spec sourceH3 b 5 26 h

theorem helperDepthH4_spec (b : Box) (h : H4Fits b) :
    HelperFits sourceH4 (helperDepthH4 b) b :=
  helperDepthAux_spec sourceH4 b 3 43 h

theorem helperDepthH5_spec (b : Box) (h : H5Fits b) :
    HelperFits sourceH5 (helperDepthH5 b) b :=
  helperDepthAux_spec sourceH5 b 1 28 h

theorem helperDepthH6_spec (b : Box) (h : H6Fits b) :
    HelperFits sourceH6 (helperDepthH6 b) b :=
  helperDepthAux_spec sourceH6 b 3 25 h

theorem helperDepthH1_bounds (b : Box) (h : H1Fits b) :
    10 ≤ helperDepthH1 b ∧ helperDepthH1 b ≤ 13 := by
  change 10 ≤ helperDepthAux sourceH1 b 10 4 ∧
    helperDepthAux sourceH1 b 10 4 ≤ 13
  have hb := helperDepthAux_bounds sourceH1 b 4 10 h
  omega

theorem helperDepthH2_bounds (b : Box) (h : H2Fits b) :
    14 ≤ helperDepthH2 b ∧ helperDepthH2 b ≤ 18 := by
  change 14 ≤ helperDepthAux sourceH2 b 14 5 ∧
    helperDepthAux sourceH2 b 14 5 ≤ 18
  have hb := helperDepthAux_bounds sourceH2 b 5 14 h
  omega

theorem helperDepthH3_bounds (b : Box) (h : H3Fits b) :
    26 ≤ helperDepthH3 b ∧ helperDepthH3 b ≤ 30 := by
  change 26 ≤ helperDepthAux sourceH3 b 26 5 ∧
    helperDepthAux sourceH3 b 26 5 ≤ 30
  have hb := helperDepthAux_bounds sourceH3 b 5 26 h
  omega

theorem helperDepthH4_bounds (b : Box) (h : H4Fits b) :
    43 ≤ helperDepthH4 b ∧ helperDepthH4 b ≤ 45 := by
  change 43 ≤ helperDepthAux sourceH4 b 43 3 ∧
    helperDepthAux sourceH4 b 43 3 ≤ 45
  have hb := helperDepthAux_bounds sourceH4 b 3 43 h
  omega

theorem helperDepthH5_bounds (b : Box) (h : H5Fits b) :
    helperDepthH5 b = 28 := by
  change helperDepthAux sourceH5 b 28 1 = 28
  have hb := helperDepthAux_bounds sourceH5 b 1 28 h
  omega

theorem helperDepthH6_bounds (b : Box) (h : H6Fits b) :
    25 ≤ helperDepthH6 b ∧ helperDepthH6 b ≤ 27 := by
  change 25 ≤ helperDepthAux sourceH6 b 25 3 ∧
    helperDepthAux sourceH6 b 25 3 ≤ 27
  have hb := helperDepthAux_bounds sourceH6 b 3 25 h
  omega

def Fits (b : Box) : Prop :=
  b.ordinaryFits ∨ RouteFits sourceA 1 b ∨ RouteFits sourceAux 1 b ∨
    CFits b ∨ H1Fits b ∨ H2Fits b ∨ H3Fits b ∨ H4Fits b ∨ H5Fits b ∨
      H6Fits b

instance (b : Box) : Decidable (Fits b) := by unfold Fits; infer_instance

def FastFits (b : Box) : Prop :=
  b.ordinaryFits ∨ FastRouteFits sourceAux 1 b ∨
    FastRouteFits sourceA 1 b ∨ CFits b ∨ H1Fits b ∨ H2Fits b ∨ H3Fits b ∨
      H4Fits b ∨ H5Fits b ∨ H6Fits b

instance (b : Box) : Decidable (FastFits b) := by unfold FastFits; infer_instance

theorem fastFits_to_fits (b : Box) : FastFits b → Fits b := by
  intro h
  simp only [FastFits, Fits, fastRouteFits_iff] at h ⊢
  tauto

abbrev CoarseCell := Fin 21 × Fin 26 × Fin 30
def coarseR (c : CoarseCell) : ℕ := c.1.val + 1
def coarseYlo (c : CoarseCell) : ℕ := coarseR c + 4 * c.2.1.val
def coarseYhi (c : CoarseCell) : ℕ := min ysCap (coarseYlo c + 3)
def coarseTlo (c : CoarseCell) : ℕ := 128 * c.2.2.val
def coarseThi (c : CoarseCell) : ℕ := min totalCap (coarseTlo c + 127)
def coarseBox (c : CoarseCell) : Box :=
  ⟨coarseR c, coarseYlo c, coarseYhi c, coarseTlo c, coarseThi c⟩
def HardCoarse (c : CoarseCell) : Prop := (coarseBox c).valid ∧ ¬ Fits (coarseBox c)
instance (c : CoarseCell) : Decidable (HardCoarse c) := by
  unfold HardCoarse; infer_instance

def FastHardCoarse (c : CoarseCell) : Prop :=
  (coarseBox c).valid ∧ ¬ FastFits (coarseBox c)
instance (c : CoarseCell) : Decidable (FastHardCoarse c) := by
  unfold FastHardCoarse; infer_instance

structure FineCell where
  parent : {c : CoarseCell // HardCoarse c}
  yi : Fin 4
  ti : Fin 4
  deriving DecidableEq, Fintype

def fineR (c : FineCell) : ℕ := coarseR c.parent.1
def fineY (c : FineCell) : ℕ := coarseYlo c.parent.1 + c.yi.val
def fineTlo (c : FineCell) : ℕ := coarseTlo c.parent.1 + 32 * c.ti.val
def fineThi (c : FineCell) : ℕ := min (coarseThi c.parent.1) (fineTlo c + 31)
def fineBox (c : FineCell) : Box := ⟨fineR c, fineY c, fineY c, fineTlo c, fineThi c⟩
def HardFine (c : FineCell) : Prop := (fineBox c).valid ∧ ¬ Fits (fineBox c)
instance (c : FineCell) : Decidable (HardFine c) := by
  unfold HardFine; infer_instance

structure UnitCell where
  parent : {c : FineCell // HardFine c}
  ti : Fin 4
  deriving DecidableEq, Fintype

def unitR (c : UnitCell) : ℕ := fineR c.parent.1
def unitY (c : UnitCell) : ℕ := fineY c.parent.1
def unitTlo (c : UnitCell) : ℕ := fineTlo c.parent.1 + 8 * c.ti.val
def unitThi (c : UnitCell) : ℕ := min (fineThi c.parent.1) (unitTlo c + 7)
def unitBox (c : UnitCell) : Box :=
  ⟨unitR c, unitY c, unitY c, unitTlo c, unitThi c⟩

/-- Proof-irrelevant presentation of a fine box, used to split the finite
receipt into independent rows without repeatedly enumerating nested
subtypes. -/
def fineBoxAt (c : CoarseCell) (yi ti : Fin 4) : Box :=
  ⟨coarseR c, coarseYlo c + yi.val, coarseYlo c + yi.val,
    coarseTlo c + 32 * ti.val,
    min (coarseThi c) (coarseTlo c + 32 * ti.val + 31)⟩

/-- Proof-irrelevant presentation of a width-eight terminal box below a fine box. -/
def unitBoxAt (c : CoarseCell) (yi ti ui : Fin 4) : Box :=
  ⟨coarseR c, coarseYlo c + yi.val, coarseYlo c + yi.val,
    (coarseTlo c + 32 * ti.val) + 8 * ui.val,
    min (min (coarseThi c) (coarseTlo c + 32 * ti.val + 31))
      ((coarseTlo c + 32 * ti.val) + 8 * ui.val + 7)⟩

theorem fineBox_eq_fineBoxAt (c : FineCell) :
    fineBox c = fineBoxAt c.parent.1 c.yi c.ti := rfl

theorem unitBox_eq_unitBoxAt (c : UnitCell) :
    unitBox c = unitBoxAt c.parent.1.parent.1
      c.parent.1.yi c.parent.1.ti c.ti := rfl

abbrev Cell := CoarseCell ⊕ (FineCell ⊕ UnitCell)

def box : Cell → Box
  | .inl c => coarseBox c
  | .inr (.inl c) => fineBox c
  | .inr (.inr c) => unitBox c

def Leaf : Cell → Prop
  | .inl c => ¬ HardCoarse c
  | .inr (.inl c) => ¬ HardFine c
  | .inr (.inr _) => True

instance (c : Cell) : Decidable (Leaf c) := by
  rcases c with c | c
  · simp only [Leaf]; infer_instance
  · rcases c with c | c
    · simp only [Leaf]; infer_instance
    · simp only [Leaf]; infer_instance

def Valid (c : Cell) : Prop := (box c).valid ∧ Leaf c
instance (c : Cell) : Decidable (Valid c) := by unfold Valid; infer_instance

structure InCell (p : FlagDegree) (c : Cell) : Prop where
  all_eq : p.all = (box c).r
  ylo_le : (box c).ylo ≤ middle p
  middle_le_yhi : middle p ≤ (box c).yhi
  tlo_le : (box c).tlo ≤ total p
  total_le_thi : total p ≤ (box c).thi
  leaf : Leaf c

def coarseCellOf (p : FlagDegree) (hslo : 1 ≤ p.all) (hshi : p.all ≤ slopeCap)
    (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) : CoarseCell :=
  (⟨p.all - 1, by
      change p.all ≤ 21 at hshi
      omega⟩,
    ⟨(middle p - p.all) / 4, by
      change middle p ≤ 102 at hy
      omega⟩,
    ⟨total p / 128, by
      change total p ≤ 3806 at ht
      omega⟩)

theorem coarseCellOf_bounds (p : FlagDegree) (hslo : 1 ≤ p.all)
    (hshi : p.all ≤ slopeCap) (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) :
    p.all = coarseR (coarseCellOf p hslo hshi hy ht) ∧
      coarseYlo (coarseCellOf p hslo hshi hy ht) ≤ middle p ∧
      middle p ≤ coarseYhi (coarseCellOf p hslo hshi hy ht) ∧
      coarseTlo (coarseCellOf p hslo hshi hy ht) ≤ total p ∧
      total p ≤ coarseThi (coarseCellOf p hslo hshi hy ht) := by
  have hmy := all_le_middle p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change p.all = p.all - 1 + 1; omega
  · change (p.all - 1 + 1) + 4 * ((middle p - p.all) / 4) ≤ middle p; omega
  · change middle p ≤ min ysCap
      ((p.all - 1 + 1) + 4 * ((middle p - p.all) / 4) + 3)
    exact le_min hy (by omega)
  · change 128 * (total p / 128) ≤ total p; omega
  · change total p ≤ min totalCap (128 * (total p / 128) + 127)
    exact le_min ht (by omega)

def fineCellOf (p : FlagDegree) (c : CoarseCell) (hc : HardCoarse c)
    (hylo : coarseYlo c ≤ middle p) (hyhi : middle p ≤ coarseYhi c)
    (htlo : coarseTlo c ≤ total p) (hthi : total p ≤ coarseThi c) : FineCell :=
  ⟨⟨c, hc⟩, ⟨middle p - coarseYlo c, by
      have hcap : coarseYhi c ≤ coarseYlo c + 3 := Nat.min_le_right _ _
      omega⟩,
    ⟨(total p - coarseTlo c) / 32, by
      have hcap : coarseThi c ≤ coarseTlo c + 127 := Nat.min_le_right _ _
      omega⟩⟩

theorem fineCellOf_bounds (p : FlagDegree) (c : CoarseCell) (hc : HardCoarse c)
    (hylo : coarseYlo c ≤ middle p) (hyhi : middle p ≤ coarseYhi c)
    (htlo : coarseTlo c ≤ total p) (hthi : total p ≤ coarseThi c)
    (hr : p.all = fineR (fineCellOf p c hc hylo hyhi htlo hthi)) :
    p.all = fineR (fineCellOf p c hc hylo hyhi htlo hthi) ∧
      fineY (fineCellOf p c hc hylo hyhi htlo hthi) = middle p ∧
      fineTlo (fineCellOf p c hc hylo hyhi htlo hthi) ≤ total p ∧
      total p ≤ fineThi (fineCellOf p c hc hylo hyhi htlo hthi) := by
  refine ⟨hr, ?_, ?_, ?_⟩
  · simp only [fineY, fineCellOf]; omega
  · simp only [fineTlo, fineCellOf]; omega
  · simp only [fineThi]
    apply le_min hthi
    simp only [fineTlo, fineCellOf]
    omega

def unitCellOf (p : FlagDegree) (c : FineCell) (hc : HardFine c)
    (htlo : fineTlo c ≤ total p) (hthi : total p ≤ fineThi c) : UnitCell :=
  ⟨⟨c, hc⟩, ⟨(total p - fineTlo c) / 8, by
      have hcap : fineThi c ≤ fineTlo c + 31 := Nat.min_le_right _ _
      omega⟩⟩

theorem unitCellOf_bounds (p : FlagDegree) (c : FineCell) (hc : HardFine c)
    (htlo : fineTlo c ≤ total p) (hthi : total p ≤ fineThi c) :
    unitTlo (unitCellOf p c hc htlo hthi) ≤ total p ∧
      total p ≤ unitThi (unitCellOf p c hc htlo hthi) := by
  constructor
  · simp only [unitTlo, unitCellOf]
    omega
  · simp only [unitThi]
    apply le_min hthi
    simp only [unitTlo, unitCellOf]
    omega

def cellOf (p : FlagDegree) (hslo : 1 ≤ p.all) (hshi : p.all ≤ slopeCap)
    (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) : Cell :=
  let c := coarseCellOf p hslo hshi hy ht
  if hc : HardCoarse c then
    let hb := coarseCellOf_bounds p hslo hshi hy ht
    let f := fineCellOf p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
    if hf : HardFine f then
      let hfb := fineCellOf_bounds p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1
        hb.2.2.2.2 hb.1
      .inr (.inr (unitCellOf p f hf hfb.2.2.1 hfb.2.2.2))
    else .inr (.inl f)
  else .inl c

theorem cellOf_bounds (p : FlagDegree) (hslo : 1 ≤ p.all)
    (hshi : p.all ≤ slopeCap) (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) :
    InCell p (cellOf p hslo hshi hy ht) := by
  let c := coarseCellOf p hslo hshi hy ht
  have hb := coarseCellOf_bounds p hslo hshi hy ht
  by_cases hc : HardCoarse c
  · let f := fineCellOf p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
    have hfb := fineCellOf_bounds p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1
      hb.2.2.2.2 hb.1
    by_cases hf : HardFine f
    · have hu := unitCellOf_bounds p f hf hfb.2.2.1 hfb.2.2.2
      simp only [cellOf, c, hc, dite_true, f, hf]
      refine ⟨hfb.1, hfb.2.1.le, hfb.2.1.symm.le, ?_, ?_, trivial⟩
      · change unitTlo (unitCellOf p f hf hfb.2.2.1 hfb.2.2.2) ≤ total p
        exact hu.1
      · change total p ≤ unitThi (unitCellOf p f hf hfb.2.2.1 hfb.2.2.2)
        exact hu.2
    · simp only [cellOf, c, hc, dite_true, f, hf]
      exact ⟨hfb.1, hfb.2.1.le, hfb.2.1.symm.le, hfb.2.2.1,
        hfb.2.2.2, by simpa only [Leaf]⟩
  · simp only [cellOf, c, hc, dite_false]
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2,
      by simpa only [Leaf]⟩

theorem valid_of_inCell (p : FlagDegree) (c : Cell)
    (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) (h : InCell p c) : Valid c := by
  have hall := all_le_middle p
  have hmid := middle_le_total p
  have hrpos : 1 ≤ (box c).r := by
    rcases c with c | c
    · simp [box, coarseBox, coarseR]
    · rcases c with c | c
      · simp [box, fineBox, fineR, coarseR]
      · simp [box, unitBox, unitR, fineR, coarseR]
  have hry : (box c).r ≤ (box c).ylo := by
    rcases c with c | c
    · simp [box, coarseBox, coarseR, coarseYlo]
    · rcases c with c | c
      · simp [box, fineBox, fineR, fineY, coarseR, coarseYlo] <;> omega
      · simp [box, unitBox, unitR, unitY, fineR, fineY, coarseR, coarseYlo] <;> omega
  have hycap : (box c).yhi ≤ ysCap := by
    rcases c with c | c
    · simp [box, coarseBox, coarseYhi]
    · rcases c with c | c
      · have hlo := h.ylo_le
        have hhi := h.middle_le_yhi
        change fineY c ≤ middle p at hlo
        change middle p ≤ fineY c at hhi
        change fineY c ≤ ysCap
        omega
      · have hlo := h.ylo_le
        have hhi := h.middle_le_yhi
        change unitY c ≤ middle p at hlo
        change middle p ≤ unitY c at hhi
        change unitY c ≤ ysCap
        omega
  have htcap : (box c).thi ≤ totalCap := by
    rcases c with c | c
    · simp [box, coarseBox, coarseThi]
    · rcases c with c | c
      · exact (Nat.min_le_left _ _).trans (by simp [coarseThi])
      · change unitThi c ≤ totalCap
        exact (Nat.min_le_left _ _).trans
          ((Nat.min_le_left _ _).trans (by simp [coarseThi]))
  refine ⟨?_, h.leaf⟩
  exact ⟨hrpos, hry, h.ylo_le.trans h.middle_le_yhi, hycap,
    h.ylo_le.trans (hmid.trans h.total_le_thi),
    h.tlo_le.trans h.total_le_thi, htcap⟩

/-- The part of a slope-row receipt in a half-open coarse-Y interval. -/
def RowBandReceipt (ri : Fin 21) (lo hi : ℕ) : Prop :=
  ∀ (cy : Fin 26), lo ≤ cy.val → cy.val < hi → ∀ (ct : Fin 30),
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            FastFits (unitBoxAt coarse yi ti ui)

instance (ri : Fin 21) (lo hi : ℕ) : Decidable (RowBandReceipt ri lo hi) := by
  unfold RowBandReceipt
  infer_instance

/-- A rectangular coarse-Y/coarse-T part of a slope-row receipt. -/
def RowTileReceipt (ri : Fin 21) (ylo yhi tlo thi : ℕ) : Prop :=
  ∀ (cy : Fin 26), ylo ≤ cy.val → cy.val < yhi →
    ∀ (ct : Fin 30), tlo ≤ ct.val → ct.val < thi →
      let coarse : CoarseCell := (ri, cy, ct)
      FastHardCoarse coarse →
        ∀ (yi ti : Fin 4),
          ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
            ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
              FastFits (unitBoxAt coarse yi ti ui)

instance (ri : Fin 21) (ylo yhi tlo thi : ℕ) :
    Decidable (RowTileReceipt ri ylo yhi tlo thi) := by
  unfold RowTileReceipt
  infer_instance

/-- A receipt for one fixed coarse-Y cell and a half-open range of coarse-T
cells. Unlike `RowTileReceipt`, its decision procedure does not enumerate the
other twenty-nine values of `Fin 30`. -/
def FixedYReceipt (ri : Fin 21) (cy : Fin 26) (tlo thi : ℕ) : Prop :=
  ∀ (ct : Fin 30), tlo ≤ ct.val → ct.val < thi →
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            FastFits (unitBoxAt coarse yi ti ui)

instance (ri : Fin 21) (cy : Fin 26) (tlo thi : ℕ) :
    Decidable (FixedYReceipt ri cy tlo thi) := by
  unfold FixedYReceipt
  infer_instance

/-- Adapt a fixed-Y receipt to the existing singleton-Y tile interface. -/
theorem fixedYReceipt_to_rowTile (ri : Fin 21) (cy : Fin 26) (tlo thi : ℕ)
    (h : FixedYReceipt ri cy tlo thi) :
    RowTileReceipt ri cy.val (cy.val + 1) tlo thi := by
  intro cy' hylo hyhi ct htlo hthi
  have hcy : cy' = cy := by
    apply Fin.ext
    omega
  subst cy'
  exact h ct htlo hthi

/-- Adapt a full-total-range fixed-Y receipt to the existing singleton-Y band
interface. -/
theorem fixedYReceipt_to_rowBand (ri : Fin 21) (cy : Fin 26)
    (h : FixedYReceipt ri cy 0 30) :
    RowBandReceipt ri cy.val (cy.val + 1) := by
  intro cy' hylo hyhi ct
  have hcy : cy' = cy := by
    apply Fin.ext
    omega
  subst cy'
  exact h ct (Nat.zero_le _) ct.isLt

theorem rowTileFull_to_rowBand (ri : Fin 21) (cy : ℕ)
    (h : RowTileReceipt ri cy (cy + 1) 0 30) : RowBandReceipt ri cy (cy + 1) := by
  intro cy' hylo hyhi ct
  exact h cy' hylo hyhi ct (Nat.zero_le _) ct.isLt

/-- A closed slope-row receipt.  Kernel reduction is deliberately split at
this level: each auxiliary lemma evaluates one twentieth of the adaptive
grid and is cached before the next row starts. -/
def RowReceipt (ri : Fin 21) : Prop :=
  ∀ (cy : Fin 26) (ct : Fin 30),
    let coarse : CoarseCell := (ri, cy, ct)
    HardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ Fits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            Fits (unitBoxAt coarse yi ti ui)

instance (ri : Fin 21) : Decidable (RowReceipt ri) := by
  unfold RowReceipt
  infer_instance

/-- A receipt-local propositionally equivalent row presentation. -/
def FastRowReceipt (ri : Fin 21) : Prop :=
  ∀ (cy : Fin 26) (ct : Fin 30),
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            FastFits (unitBoxAt coarse yi ti ui)

instance (ri : Fin 21) : Decidable (FastRowReceipt ri) := by
  unfold FastRowReceipt
  infer_instance

theorem fastRowReceipt_to_rowReceipt (ri : Fin 21)
    (h : FastRowReceipt ri) : RowReceipt ri := by
  intro cy ct
  dsimp only
  intro hcoarse yi ti hfine ui hunit
  apply fastFits_to_fits
  exact h cy ct
    ⟨hcoarse.1, fun hfast => hcoarse.2 (fastFits_to_fits _ hfast)⟩ yi ti
    ⟨hfine.1, fun hfast => hfine.2 (fastFits_to_fits _ hfast)⟩ ui hunit

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
