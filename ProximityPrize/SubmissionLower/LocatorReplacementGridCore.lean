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

/-! ### Row constants

Single source of truth for the grid layer and for every module that imports
it, including the generic helper engine: those read these abbrevs instead of
repeating literals, so retuning a row is this block and nothing else.  All
public for that reason. -/

/-- Selected-polynomial degree cap, the `w` of the kernel tuples. -/
abbrev selectedDegree : ℕ := 131071
/-- Field characteristic. -/
abbrev prime : ℕ := 2130706433
/-- Agreement threshold, shared by every stage and helper pair. -/
abbrev agreements : ℕ := 181520
/-- Error budget, forced as `262144 - agreements`. -/
abbrev errors : ℕ := 80624
/-- Contact-band width, `agreements - selectedDegree + 1`. -/
abbrev delta : ℕ := 50450
abbrev bound : ℕ := 269159312872668139
abbrev totalCap : ℕ := 3922
/-- Caps of the factors that divide every A reconstruction (the narrow grid). -/
abbrev ysCap : ℕ := 101
abbrev slopeCap : ℕ := 22
/-- Caps of the whole common divisor, from the B box: every factor lies below
them, and the weighted budget is charged against them. -/
abbrev wholeSlopeCap : ℕ := 23
abbrev wholeYsCap : ℕ := 110

/-- Nonnegative linear weights for the aggregate charge, `wT * total + wY * middle
+ wS * slope`.  Row 6787: the exact model closes the grid at `(3, 0, 260)`: a factor
is charged mostly by its share of the whole divisor's slope (a slope-8 factor is a
third of slope 23), which is where the last hard cells sit.  These are the values
the receipts were generated at. -/
abbrev wT : ℕ := 3
abbrev wY : ℕ := 0
abbrev wS : ℕ := 260

/-- Total weight budget.  The whole-divisor support caps bound the three sums
`∑ total ≤ totalCap`, `∑ middle ≤ wholeYsCap` and `∑ all ≤ wholeSlopeCap`, so
the weighted sum over the factors is bounded by this. -/
abbrev capSum : ℕ := wT * totalCap + wY * wholeYsCap + wS * wholeSlopeCap

/-- Maximum admissible repeated-projection depth for the accepted source-C
route, which is the only route driven by `routeDepth`. -/
abbrev routeCap : ℕ := 14

/-- Maximum admissible depth for any route, including the helper sources whose
windows run deeper than the C route. -/
abbrev depthCap : ℕ := 200

/-- Grid dimensions.  A cap change means the matching band count changes here:
`yBands * 4` must cover `ysCap` and `tBands * 128` must cover `totalCap`. -/
abbrev slopeRows : ℕ := 22
abbrev yBands : ℕ := 26
abbrev tBands : ℕ := 31

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
/-- The least weighted charge any flag in the box can carry.  For `p` in the
box, `all p = b.r`, `middle p ≥ b.ylo`, and `total p ≥ max b.tlo b.ylo`
because `total p ≥ b.tlo` and `total p ≥ middle p ≥ b.ylo`, so
`total p + wY * middle p + wS * all p ≥ b.weight`. -/
def Box.weight (b : Box) : ℕ := wT * b.factorT + wY * b.ylo + wS * b.r

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

/-- Row 6787 sources: the A, Aux and C kernels and the helper kernels (nullities
from `LocatorHelperArithmeticGeneric`); the long ones exhaust their ys degree in
40..200 stages. -/
def sourceA : Source := ⟨130000, 105, 22, 255124945551⟩
def sourceAux : Source := ⟨130000, 105, 23, 422421820346⟩
def sourceC : Source := ⟨130000, 553, 120, 1591585493643178⟩
def sourceS2 : Source := ⟨1000000, 692, 150, 26099605139687297⟩
def sourceS3 : Source := ⟨350000, 1121, 243, 40160939066613289⟩
def sourceH3X : Source := ⟨2000000, 1121, 243, 236385995162913289⟩
def sourceH4 : Source := ⟨2000000, 1384, 300, 452270055375521215⟩
def sourceT10k : Source := ⟨10000, 747, 170, 56736169045377⟩
def sourceT15k : Source := ⟨15000, 761, 170, 236413037510670⟩
def sourceT20k : Source := ⟨20000, 775, 170, 427848492911895⟩
def sourceT30k : Source := ⟨30000, 789, 170, 825486901846260⟩
def sourceL1 : Source := ⟨100000, 1661, 360, 32824016747150030⟩
def sourceL2 : Source := ⟨100000, 2437, 540, 98869741656154847⟩
def sourceL3 : Source := ⟨100000, 3212, 720, 208366000154703552⟩
def sourceL4 : Source := ⟨200000, 2215, 480, 169689309551713640⟩
def sourceL5 : Source := ⟨200000, 4320, 960, 1173917541318584880⟩
def sourceL6 : Source := ⟨200000, 5401, 1200, 2147605378029326500⟩
def sourceM1 : Source := ⟨300000, 3600, 800, 1138451951765615400⟩
def sourceM3 : Source := ⟨300000, 4293, 950, 1879915212902702273⟩
def sourceN1 : Source := ⟨400000, 3600, 800, 1570210864625615400⟩
def sourceN3 : Source := ⟨400000, 6370, 1400, 8038176207758867660⟩
def sourceN4 : Source := ⟨400000, 7201, 1600, 11500069849226062000⟩

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
      = delta * channelCount (stageT src b j) (stageY src b j)
          (stageR src b j) := by
  unfold stageBand
  by_cases h : stageY src b j ≤ stageT src b j
  · rw [if_pos h, ← LocatorChannelClosed.channelCount_eq_fast _ _ _ h]
  · rw [if_neg h]

def bandSum (src : Source) (b : Box) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bandSum src b k + stageBand src b (k + 1)

def stagePair (src : Source) (b : Box) (j : ℕ) : UnequalParameters :=
  ⟨262144, selectedDegree, agreements, b.factorY, b.r, b.thi,
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

instance instDecidablePairGatesThrough (src : Source) (b : Box) :
    ∀ k : ℕ, Decidable (pairGatesThrough src b k)
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
  stageT src b k < b.factorT ∨ stageY src b k < b.ylo ∨ stageR src b k < b.r

instance (src : Source) (b : Box) (k : ℕ) :
    Decidable (terminalCoprime src b k) := by
  unfold terminalCoprime; infer_instance

def RouteFits (src : Source) (k : ℕ) (b : Box) : Prop :=
  1 ≤ k ∧ k ≤ depthCap ∧
    k * b.ylo ≤ src.y ∧ k * b.r ≤ src.r ∧
    k * b.factorT + stageY src b k ≤ src.length ∧
    bandSum src b k < src.gap ∧ terminalCoprime src b k ∧
    pairGatesThrough src b k ∧
    capSum * routeCost src b k ≤ bound * b.weight

instance (src : Source) (k : ℕ) (b : Box) : Decidable (RouteFits src k b) := by
  unfold RouteFits; infer_instance

/-- A receipt-local propositionally equivalent presentation of `RouteFits`. -/
def FastRouteFits (src : Source) (k : ℕ) (b : Box) : Prop :=
  1 ≤ k ∧ k ≤ depthCap ∧
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

theorem routeDepthAux_bounds (src : Source) (b : Box) (n : ℕ) :
    ∀ k, routeDepthAux src b k n ≠ 0 → routeDepthAux src b k n < k + n := by
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
          omega
        · rw [if_neg hfit] at h
          exact absurd rfl h
      · rw [if_neg hterm] at h ⊢
        have hb := ih (k + 1) h
        omega

/-- `RouteFits` now caps depth at `depthCap`, so the source-C consumer, which
is only sound up to `routeCap`, takes its depth bound from the walk itself. -/
theorem routeDepth_le_routeCap (src : Source) (b : Box)
    (h : routeDepth src b ≠ 0) : routeDepth src b ≤ routeCap := by
  have hb := routeDepthAux_bounds src b routeCap 1 h
  change routeDepthAux src b 1 routeCap ≤ routeCap
  omega

def CFits (b : Box) : Prop := routeDepth sourceC b ≠ 0

instance (b : Box) : Decidable (CFits b) := by unfold CFits; infer_instance

/-- Direct coprime-pair parameters for an unconditional helper source: the
right-hand side is the helper's own box, so one definition serves every
helper kernel.

Provenance.  The generic multi-helper shape is adapted from `jieyilong`
(PR #471); the per-source counting lemmas live in the generic modules. -/
def helperPair (src : Source) (b : Box) : UnequalParameters :=
  ⟨262144, selectedDegree, agreements, b.factorY, b.r, b.thi,
    src.y, src.r, src.length⟩

/-- A helper arm at one explicit depth: the divisor branch pays the depth-`k`
route, the non-divisor branch pays one coprime witness from the helper box. -/
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

/-- The A, Aux and C sources are no longer selected kernels: like the helpers
they are consumed through the per-factor divisor-or-helper switch, so each of
their arms carries the direct-pair charge as well as the route. -/
def AFits (b : Box) : Prop := HelperFits sourceA 1 b
def AuxFits (b : Box) : Prop := HelperFits sourceAux 1 b
def CHFits (b : Box) : Prop :=
  CFits b ∧ HelperFits sourceC (routeDepth sourceC b) b
def FastAFits (b : Box) : Prop := FastHelperFits sourceA 1 b
def FastAuxFits (b : Box) : Prop := FastHelperFits sourceAux 1 b
def FastCHFits (b : Box) : Prop :=
  CFits b ∧ FastHelperFits sourceC (routeDepth sourceC b) b

instance (b : Box) : Decidable (AFits b) := by unfold AFits; infer_instance
instance (b : Box) : Decidable (AuxFits b) := by unfold AuxFits; infer_instance
instance (b : Box) : Decidable (CHFits b) := by unfold CHFits; infer_instance
instance (b : Box) : Decidable (FastAFits b) := by unfold FastAFits; infer_instance
instance (b : Box) : Decidable (FastAuxFits b) := by unfold FastAuxFits; infer_instance
instance (b : Box) : Decidable (FastCHFits b) := by unfold FastCHFits; infer_instance

theorem fastAFits_iff (b : Box) : FastAFits b ↔ AFits b := fastHelperFits_iff _ _ _
theorem fastAuxFits_iff (b : Box) : FastAuxFits b ↔ AuxFits b := fastHelperFits_iff _ _ _
theorem fastCHFits_iff (b : Box) : FastCHFits b ↔ CHFits b := by
  simp only [FastCHFits, CHFits, fastHelperFits_iff]

/-- Scan one short explicit depth window and accept the first depth at which
the helper arm passes both its route and its direct-pair charge.  Unlike
`routeDepthAux` there is no terminal-coprimality gate: the window is chosen
per source, and soundness only needs the depth it returns to fit. -/
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

def helperDepthS2 (b : Box) : ℕ := helperDepthAux sourceS2 b 14 5
def S2Fits (b : Box) : Prop := helperDepthS2 b ≠ 0
instance (b : Box) : Decidable (S2Fits b) := by unfold S2Fits; infer_instance
theorem helperDepthS2_spec (b : Box) (h : S2Fits b) :
    HelperFits sourceS2 (helperDepthS2 b) b :=
  helperDepthAux_spec sourceS2 b 5 14 h
theorem helperDepthS2_bounds (b : Box) (h : S2Fits b) :
    14 ≤ helperDepthS2 b ∧ helperDepthS2 b ≤ 18 := by
  have hb := helperDepthAux_bounds sourceS2 b 5 14 h
  change 14 ≤ helperDepthAux sourceS2 b 14 5 ∧
    helperDepthAux sourceS2 b 14 5 ≤ 18
  omega

def helperDepthS3 (b : Box) : ℕ := helperDepthAux sourceS3 b 26 5
def S3Fits (b : Box) : Prop := helperDepthS3 b ≠ 0
instance (b : Box) : Decidable (S3Fits b) := by unfold S3Fits; infer_instance
theorem helperDepthS3_spec (b : Box) (h : S3Fits b) :
    HelperFits sourceS3 (helperDepthS3 b) b :=
  helperDepthAux_spec sourceS3 b 5 26 h
theorem helperDepthS3_bounds (b : Box) (h : S3Fits b) :
    26 ≤ helperDepthS3 b ∧ helperDepthS3 b ≤ 30 := by
  have hb := helperDepthAux_bounds sourceS3 b 5 26 h
  change 26 ≤ helperDepthAux sourceS3 b 26 5 ∧
    helperDepthAux sourceS3 b 26 5 ≤ 30
  omega

def helperDepthH3X (b : Box) : ℕ := helperDepthAux sourceH3X b 24 9
def H3XFits (b : Box) : Prop := helperDepthH3X b ≠ 0
instance (b : Box) : Decidable (H3XFits b) := by unfold H3XFits; infer_instance
theorem helperDepthH3X_spec (b : Box) (h : H3XFits b) :
    HelperFits sourceH3X (helperDepthH3X b) b :=
  helperDepthAux_spec sourceH3X b 9 24 h
theorem helperDepthH3X_bounds (b : Box) (h : H3XFits b) :
    24 ≤ helperDepthH3X b ∧ helperDepthH3X b ≤ 32 := by
  have hb := helperDepthAux_bounds sourceH3X b 9 24 h
  change 24 ≤ helperDepthAux sourceH3X b 24 9 ∧
    helperDepthAux sourceH3X b 24 9 ≤ 32
  omega

def helperDepthH4 (b : Box) : ℕ := helperDepthAux sourceH4 b 30 7
def H4Fits (b : Box) : Prop := helperDepthH4 b ≠ 0
instance (b : Box) : Decidable (H4Fits b) := by unfold H4Fits; infer_instance
theorem helperDepthH4_spec (b : Box) (h : H4Fits b) :
    HelperFits sourceH4 (helperDepthH4 b) b :=
  helperDepthAux_spec sourceH4 b 7 30 h
theorem helperDepthH4_bounds (b : Box) (h : H4Fits b) :
    30 ≤ helperDepthH4 b ∧ helperDepthH4 b ≤ 36 := by
  have hb := helperDepthAux_bounds sourceH4 b 7 30 h
  change 30 ≤ helperDepthAux sourceH4 b 30 7 ∧
    helperDepthAux sourceH4 b 30 7 ≤ 36
  omega

def helperDepthT10k (b : Box) : ℕ := helperDepthAux sourceT10k b 1 8
def T10kFits (b : Box) : Prop := helperDepthT10k b ≠ 0
instance (b : Box) : Decidable (T10kFits b) := by unfold T10kFits; infer_instance
theorem helperDepthT10k_spec (b : Box) (h : T10kFits b) :
    HelperFits sourceT10k (helperDepthT10k b) b :=
  helperDepthAux_spec sourceT10k b 8 1 h
theorem helperDepthT10k_bounds (b : Box) (h : T10kFits b) :
    1 ≤ helperDepthT10k b ∧ helperDepthT10k b ≤ 8 := by
  have hb := helperDepthAux_bounds sourceT10k b 8 1 h
  change 1 ≤ helperDepthAux sourceT10k b 1 8 ∧
    helperDepthAux sourceT10k b 1 8 ≤ 8
  omega

def helperDepthT15k (b : Box) : ℕ := helperDepthAux sourceT15k b 2 11
def T15kFits (b : Box) : Prop := helperDepthT15k b ≠ 0
instance (b : Box) : Decidable (T15kFits b) := by unfold T15kFits; infer_instance
theorem helperDepthT15k_spec (b : Box) (h : T15kFits b) :
    HelperFits sourceT15k (helperDepthT15k b) b :=
  helperDepthAux_spec sourceT15k b 11 2 h
theorem helperDepthT15k_bounds (b : Box) (h : T15kFits b) :
    2 ≤ helperDepthT15k b ∧ helperDepthT15k b ≤ 12 := by
  have hb := helperDepthAux_bounds sourceT15k b 11 2 h
  change 2 ≤ helperDepthAux sourceT15k b 2 11 ∧
    helperDepthAux sourceT15k b 2 11 ≤ 12
  omega

def helperDepthT20k (b : Box) : ℕ := helperDepthAux sourceT20k b 4 11
def T20kFits (b : Box) : Prop := helperDepthT20k b ≠ 0
instance (b : Box) : Decidable (T20kFits b) := by unfold T20kFits; infer_instance
theorem helperDepthT20k_spec (b : Box) (h : T20kFits b) :
    HelperFits sourceT20k (helperDepthT20k b) b :=
  helperDepthAux_spec sourceT20k b 11 4 h
theorem helperDepthT20k_bounds (b : Box) (h : T20kFits b) :
    4 ≤ helperDepthT20k b ∧ helperDepthT20k b ≤ 14 := by
  have hb := helperDepthAux_bounds sourceT20k b 11 4 h
  change 4 ≤ helperDepthAux sourceT20k b 4 11 ∧
    helperDepthAux sourceT20k b 4 11 ≤ 14
  omega

def helperDepthT30k (b : Box) : ℕ := helperDepthAux sourceT30k b 8 15
def T30kFits (b : Box) : Prop := helperDepthT30k b ≠ 0
instance (b : Box) : Decidable (T30kFits b) := by unfold T30kFits; infer_instance
theorem helperDepthT30k_spec (b : Box) (h : T30kFits b) :
    HelperFits sourceT30k (helperDepthT30k b) b :=
  helperDepthAux_spec sourceT30k b 15 8 h
theorem helperDepthT30k_bounds (b : Box) (h : T30kFits b) :
    8 ≤ helperDepthT30k b ∧ helperDepthT30k b ≤ 22 := by
  have hb := helperDepthAux_bounds sourceT30k b 15 8 h
  change 8 ≤ helperDepthAux sourceT30k b 8 15 ∧
    helperDepthAux sourceT30k b 8 15 ≤ 22
  omega

def helperDepthL1 (b : Box) : ℕ := helperDepthAux sourceL1 b 32 19
def L1Fits (b : Box) : Prop := helperDepthL1 b ≠ 0
instance (b : Box) : Decidable (L1Fits b) := by unfold L1Fits; infer_instance
theorem helperDepthL1_spec (b : Box) (h : L1Fits b) :
    HelperFits sourceL1 (helperDepthL1 b) b :=
  helperDepthAux_spec sourceL1 b 19 32 h
theorem helperDepthL1_bounds (b : Box) (h : L1Fits b) :
    32 ≤ helperDepthL1 b ∧ helperDepthL1 b ≤ 50 := by
  have hb := helperDepthAux_bounds sourceL1 b 19 32 h
  change 32 ≤ helperDepthAux sourceL1 b 32 19 ∧
    helperDepthAux sourceL1 b 32 19 ≤ 50
  omega

def helperDepthL2 (b : Box) : ℕ := helperDepthAux sourceL2 b 50 23
def L2Fits (b : Box) : Prop := helperDepthL2 b ≠ 0
instance (b : Box) : Decidable (L2Fits b) := by unfold L2Fits; infer_instance
theorem helperDepthL2_spec (b : Box) (h : L2Fits b) :
    HelperFits sourceL2 (helperDepthL2 b) b :=
  helperDepthAux_spec sourceL2 b 23 50 h
theorem helperDepthL2_bounds (b : Box) (h : L2Fits b) :
    50 ≤ helperDepthL2 b ∧ helperDepthL2 b ≤ 72 := by
  have hb := helperDepthAux_bounds sourceL2 b 23 50 h
  change 50 ≤ helperDepthAux sourceL2 b 50 23 ∧
    helperDepthAux sourceL2 b 50 23 ≤ 72
  omega

def helperDepthL3 (b : Box) : ℕ := helperDepthAux sourceL3 b 62 19
def L3Fits (b : Box) : Prop := helperDepthL3 b ≠ 0
instance (b : Box) : Decidable (L3Fits b) := by unfold L3Fits; infer_instance
theorem helperDepthL3_spec (b : Box) (h : L3Fits b) :
    HelperFits sourceL3 (helperDepthL3 b) b :=
  helperDepthAux_spec sourceL3 b 19 62 h
theorem helperDepthL3_bounds (b : Box) (h : L3Fits b) :
    62 ≤ helperDepthL3 b ∧ helperDepthL3 b ≤ 80 := by
  have hb := helperDepthAux_bounds sourceL3 b 19 62 h
  change 62 ≤ helperDepthAux sourceL3 b 62 19 ∧
    helperDepthAux sourceL3 b 62 19 ≤ 80
  omega

def helperDepthL4 (b : Box) : ℕ := helperDepthAux sourceL4 b 44 13
def L4Fits (b : Box) : Prop := helperDepthL4 b ≠ 0
instance (b : Box) : Decidable (L4Fits b) := by unfold L4Fits; infer_instance
theorem helperDepthL4_spec (b : Box) (h : L4Fits b) :
    HelperFits sourceL4 (helperDepthL4 b) b :=
  helperDepthAux_spec sourceL4 b 13 44 h
theorem helperDepthL4_bounds (b : Box) (h : L4Fits b) :
    44 ≤ helperDepthL4 b ∧ helperDepthL4 b ≤ 56 := by
  have hb := helperDepthAux_bounds sourceL4 b 13 44 h
  change 44 ≤ helperDepthAux sourceL4 b 44 13 ∧
    helperDepthAux sourceL4 b 44 13 ≤ 56
  omega

def helperDepthL5 (b : Box) : ℕ := helperDepthAux sourceL5 b 100 29
def L5Fits (b : Box) : Prop := helperDepthL5 b ≠ 0
instance (b : Box) : Decidable (L5Fits b) := by unfold L5Fits; infer_instance
theorem helperDepthL5_spec (b : Box) (h : L5Fits b) :
    HelperFits sourceL5 (helperDepthL5 b) b :=
  helperDepthAux_spec sourceL5 b 29 100 h
theorem helperDepthL5_bounds (b : Box) (h : L5Fits b) :
    100 ≤ helperDepthL5 b ∧ helperDepthL5 b ≤ 128 := by
  have hb := helperDepthAux_bounds sourceL5 b 29 100 h
  change 100 ≤ helperDepthAux sourceL5 b 100 29 ∧
    helperDepthAux sourceL5 b 100 29 ≤ 128
  omega

def helperDepthL6 (b : Box) : ℕ := helperDepthAux sourceL6 b 128 23
def L6Fits (b : Box) : Prop := helperDepthL6 b ≠ 0
instance (b : Box) : Decidable (L6Fits b) := by unfold L6Fits; infer_instance
theorem helperDepthL6_spec (b : Box) (h : L6Fits b) :
    HelperFits sourceL6 (helperDepthL6 b) b :=
  helperDepthAux_spec sourceL6 b 23 128 h
theorem helperDepthL6_bounds (b : Box) (h : L6Fits b) :
    128 ≤ helperDepthL6 b ∧ helperDepthL6 b ≤ 150 := by
  have hb := helperDepthAux_bounds sourceL6 b 23 128 h
  change 128 ≤ helperDepthAux sourceL6 b 128 23 ∧
    helperDepthAux sourceL6 b 128 23 ≤ 150
  omega

def helperDepthM1 (b : Box) : ℕ := helperDepthAux sourceM1 b 76 27
def M1Fits (b : Box) : Prop := helperDepthM1 b ≠ 0
instance (b : Box) : Decidable (M1Fits b) := by unfold M1Fits; infer_instance
theorem helperDepthM1_spec (b : Box) (h : M1Fits b) :
    HelperFits sourceM1 (helperDepthM1 b) b :=
  helperDepthAux_spec sourceM1 b 27 76 h
theorem helperDepthM1_bounds (b : Box) (h : M1Fits b) :
    76 ≤ helperDepthM1 b ∧ helperDepthM1 b ≤ 102 := by
  have hb := helperDepthAux_bounds sourceM1 b 27 76 h
  change 76 ≤ helperDepthAux sourceM1 b 76 27 ∧
    helperDepthAux sourceM1 b 76 27 ≤ 102
  omega

def helperDepthM3 (b : Box) : ℕ := helperDepthAux sourceM3 b 110 15
def M3Fits (b : Box) : Prop := helperDepthM3 b ≠ 0
instance (b : Box) : Decidable (M3Fits b) := by unfold M3Fits; infer_instance
theorem helperDepthM3_spec (b : Box) (h : M3Fits b) :
    HelperFits sourceM3 (helperDepthM3 b) b :=
  helperDepthAux_spec sourceM3 b 15 110 h
theorem helperDepthM3_bounds (b : Box) (h : M3Fits b) :
    110 ≤ helperDepthM3 b ∧ helperDepthM3 b ≤ 124 := by
  have hb := helperDepthAux_bounds sourceM3 b 15 110 h
  change 110 ≤ helperDepthAux sourceM3 b 110 15 ∧
    helperDepthAux sourceM3 b 110 15 ≤ 124
  omega

def helperDepthN1 (b : Box) : ℕ := helperDepthAux sourceN1 b 88 17
def N1Fits (b : Box) : Prop := helperDepthN1 b ≠ 0
instance (b : Box) : Decidable (N1Fits b) := by unfold N1Fits; infer_instance
theorem helperDepthN1_spec (b : Box) (h : N1Fits b) :
    HelperFits sourceN1 (helperDepthN1 b) b :=
  helperDepthAux_spec sourceN1 b 17 88 h
theorem helperDepthN1_bounds (b : Box) (h : N1Fits b) :
    88 ≤ helperDepthN1 b ∧ helperDepthN1 b ≤ 104 := by
  have hb := helperDepthAux_bounds sourceN1 b 17 88 h
  change 88 ≤ helperDepthAux sourceN1 b 88 17 ∧
    helperDepthAux sourceN1 b 88 17 ≤ 104
  omega

def helperDepthN3 (b : Box) : ℕ := helperDepthAux sourceN3 b 160 21
def N3Fits (b : Box) : Prop := helperDepthN3 b ≠ 0
instance (b : Box) : Decidable (N3Fits b) := by unfold N3Fits; infer_instance
theorem helperDepthN3_spec (b : Box) (h : N3Fits b) :
    HelperFits sourceN3 (helperDepthN3 b) b :=
  helperDepthAux_spec sourceN3 b 21 160 h
theorem helperDepthN3_bounds (b : Box) (h : N3Fits b) :
    160 ≤ helperDepthN3 b ∧ helperDepthN3 b ≤ 180 := by
  have hb := helperDepthAux_bounds sourceN3 b 21 160 h
  change 160 ≤ helperDepthAux sourceN3 b 160 21 ∧
    helperDepthAux sourceN3 b 160 21 ≤ 180
  omega

def helperDepthN4 (b : Box) : ℕ := helperDepthAux sourceN4 b 184 17
def N4Fits (b : Box) : Prop := helperDepthN4 b ≠ 0
instance (b : Box) : Decidable (N4Fits b) := by unfold N4Fits; infer_instance
theorem helperDepthN4_spec (b : Box) (h : N4Fits b) :
    HelperFits sourceN4 (helperDepthN4 b) b :=
  helperDepthAux_spec sourceN4 b 17 184 h
theorem helperDepthN4_bounds (b : Box) (h : N4Fits b) :
    184 ≤ helperDepthN4 b ∧ helperDepthN4 b ≤ 200 := by
  have hb := helperDepthAux_bounds sourceN4 b 17 184 h
  change 184 ≤ helperDepthAux sourceN4 b 184 17 ∧
    helperDepthAux sourceN4 b 184 17 ≤ 200
  omega

def Fits (b : Box) : Prop :=
  b.ordinaryFits ∨ AFits b ∨ AuxFits b ∨ CHFits b ∨
    S2Fits b ∨ S3Fits b ∨ H3XFits b ∨ H4Fits b ∨ T10kFits b ∨ T15kFits b ∨ T20kFits b ∨ T30kFits b ∨ L1Fits b ∨ L2Fits b ∨ L3Fits b ∨ L4Fits b ∨ L5Fits b ∨ L6Fits b ∨ M1Fits b ∨ M3Fits b ∨ N1Fits b ∨ N3Fits b ∨ N4Fits b

instance (b : Box) : Decidable (Fits b) := by unfold Fits; infer_instance

def FastFits (b : Box) : Prop :=
  b.ordinaryFits ∨ FastAFits b ∨ FastAuxFits b ∨ FastCHFits b ∨
    S2Fits b ∨ S3Fits b ∨ H3XFits b ∨ H4Fits b ∨ T10kFits b ∨ T15kFits b ∨ T20kFits b ∨ T30kFits b ∨ L1Fits b ∨ L2Fits b ∨ L3Fits b ∨ L4Fits b ∨ L5Fits b ∨ L6Fits b ∨ M1Fits b ∨ M3Fits b ∨ N1Fits b ∨ N3Fits b ∨ N4Fits b

instance (b : Box) : Decidable (FastFits b) := by unfold FastFits; infer_instance

theorem fastFits_to_fits (b : Box) : FastFits b → Fits b := by
  intro h
  simp only [FastFits, Fits, fastAFits_iff, fastAuxFits_iff, fastCHFits_iff] at h ⊢
  exact h

abbrev CoarseCell := Fin slopeRows × Fin yBands × Fin tBands
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

/-- Terminal cells are single total-degree points: the box rate compares the
cost at `thi` against `factorT`, so a width-eight terminal box is loose by the
width of its total-degree interval.  At width one the check is exact. -/
structure UnitCell where
  parent : {c : FineCell // HardFine c}
  ti : Fin 32
  deriving DecidableEq, Fintype

def unitR (c : UnitCell) : ℕ := fineR c.parent.1
def unitY (c : UnitCell) : ℕ := fineY c.parent.1
def unitTlo (c : UnitCell) : ℕ := fineTlo c.parent.1 + c.ti.val
def unitThi (c : UnitCell) : ℕ := min (fineThi c.parent.1) (unitTlo c)
def unitBox (c : UnitCell) : Box :=
  ⟨unitR c, unitY c, unitY c, unitTlo c, unitThi c⟩

/-- Proof-irrelevant presentation of a fine box, used to split the finite
receipt into independent rows without repeatedly enumerating nested
subtypes. -/
def fineBoxAt (c : CoarseCell) (yi ti : Fin 4) : Box :=
  ⟨coarseR c, coarseYlo c + yi.val, coarseYlo c + yi.val,
    coarseTlo c + 32 * ti.val,
    min (coarseThi c) (coarseTlo c + 32 * ti.val + 31)⟩

/-- Proof-irrelevant presentation of a single-point terminal box below a fine box. -/
def unitBoxAt (c : CoarseCell) (yi ti : Fin 4) (ui : Fin 32) : Box :=
  ⟨coarseR c, coarseYlo c + yi.val, coarseYlo c + yi.val,
    (coarseTlo c + 32 * ti.val) + ui.val,
    min (min (coarseThi c) (coarseTlo c + 32 * ti.val + 31))
      ((coarseTlo c + 32 * ti.val) + ui.val)⟩

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
      change p.all ≤ 22 at hshi
      show p.all - 1 < 22
      omega⟩,
    ⟨(middle p - p.all) / 4, by
      change middle p ≤ 101 at hy
      show (middle p - p.all) / 4 < 26
      omega⟩,
    ⟨total p / 128, by
      change total p ≤ 3922 at ht
      show total p / 128 < 31
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
  ⟨⟨c, hc⟩, ⟨total p - fineTlo c, by
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
def RowBandReceipt (ri : Fin slopeRows) (lo hi : ℕ) : Prop :=
  ∀ (cy : Fin yBands), lo ≤ cy.val → cy.val < hi → ∀ (ct : Fin tBands),
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 32, (unitBoxAt coarse yi ti ui).valid →
            FastFits (unitBoxAt coarse yi ti ui)

instance (ri : Fin slopeRows) (lo hi : ℕ) : Decidable (RowBandReceipt ri lo hi) := by
  unfold RowBandReceipt
  infer_instance

/-- A rectangular coarse-Y/coarse-T part of a slope-row receipt. -/
def RowTileReceipt (ri : Fin slopeRows) (ylo yhi tlo thi : ℕ) : Prop :=
  ∀ (cy : Fin yBands), ylo ≤ cy.val → cy.val < yhi →
    ∀ (ct : Fin tBands), tlo ≤ ct.val → ct.val < thi →
      let coarse : CoarseCell := (ri, cy, ct)
      FastHardCoarse coarse →
        ∀ (yi ti : Fin 4),
          ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
            ∀ ui : Fin 32, (unitBoxAt coarse yi ti ui).valid →
              FastFits (unitBoxAt coarse yi ti ui)

instance (ri : Fin slopeRows) (ylo yhi tlo thi : ℕ) :
    Decidable (RowTileReceipt ri ylo yhi tlo thi) := by
  unfold RowTileReceipt
  infer_instance

/-- A receipt for one fixed coarse-Y cell and a half-open range of coarse-T
cells.  Unlike `RowTileReceipt`, its decision procedure does not enumerate
the other twenty-seven values of `Fin 28`. -/
def FixedYReceipt (ri : Fin slopeRows) (cy : Fin yBands) (tlo thi : ℕ) : Prop :=
  ∀ (ct : Fin tBands), tlo ≤ ct.val → ct.val < thi →
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 32, (unitBoxAt coarse yi ti ui).valid →
            FastFits (unitBoxAt coarse yi ti ui)

instance (ri : Fin slopeRows) (cy : Fin yBands) (tlo thi : ℕ) :
    Decidable (FixedYReceipt ri cy tlo thi) := by
  unfold FixedYReceipt
  infer_instance

/-- Adapt a fixed-Y receipt to the existing singleton-Y tile interface. -/
theorem fixedYReceipt_to_rowTile (ri : Fin slopeRows) (cy : Fin yBands) (tlo thi : ℕ)
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
theorem fixedYReceipt_to_rowBand (ri : Fin slopeRows) (cy : Fin yBands)
    (h : FixedYReceipt ri cy 0 tBands) :
    RowBandReceipt ri cy.val (cy.val + 1) := by
  intro cy' hylo hyhi ct
  have hcy : cy' = cy := by
    apply Fin.ext
    omega
  subst cy'
  exact h ct (Nat.zero_le _) ct.isLt

theorem rowTileFull_to_rowBand (ri : Fin slopeRows) (cy : ℕ)
    (h : RowTileReceipt ri cy (cy + 1) 0 tBands) : RowBandReceipt ri cy (cy + 1) := by
  intro cy' hylo hyhi ct
  exact h cy' hylo hyhi ct (Nat.zero_le _) ct.isLt

/-- A closed slope-row receipt.  Kernel reduction is deliberately split at
this level: each auxiliary lemma evaluates one twenty-first of the adaptive
grid and is cached before the next row starts. -/
def RowReceipt (ri : Fin slopeRows) : Prop :=
  ∀ (cy : Fin yBands) (ct : Fin tBands),
    let coarse : CoarseCell := (ri, cy, ct)
    HardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ Fits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 32, (unitBoxAt coarse yi ti ui).valid →
            Fits (unitBoxAt coarse yi ti ui)

instance (ri : Fin slopeRows) : Decidable (RowReceipt ri) := by
  unfold RowReceipt
  infer_instance

/-- A receipt-local propositionally equivalent row presentation. -/
def FastRowReceipt (ri : Fin slopeRows) : Prop :=
  ∀ (cy : Fin yBands) (ct : Fin tBands),
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 32, (unitBoxAt coarse yi ti ui).valid →
            FastFits (unitBoxAt coarse yi ti ui)

instance (ri : Fin slopeRows) : Decidable (FastRowReceipt ri) := by
  unfold FastRowReceipt
  infer_instance

theorem fastRowReceipt_to_rowReceipt (ri : Fin slopeRows)
    (h : FastRowReceipt ri) : RowReceipt ri := by
  intro cy ct
  dsimp only
  intro hcoarse yi ti hfine ui hunit
  apply fastFits_to_fits
  exact h cy ct
    ⟨hcoarse.1, fun hfast => hcoarse.2 (fastFits_to_fits _ hfast)⟩ yi ti
    ⟨hfine.1, fun hfast => hfine.2 (fastFits_to_fits _ hfast)⟩ ui hunit

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
