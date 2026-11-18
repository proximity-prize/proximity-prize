/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.Koala6831MovingStages

open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (SourceNumbers)
open LocatorPhase6800Audit (powerBandBudget_mono_fuel)

theorem room_remaining_caps (roomOrder : ℕ) (remaining incoming source : FlagDegree)
    (hincoming : Below remaining incoming)
    (hsource : Below ((roomOrder + 1) • remaining) source) :
    remaining.all ≤ min incoming.all (source.all / (roomOrder + 1)) ∧
    middle remaining ≤ min (middle incoming) (middle source / (roomOrder + 1)) ∧
    total remaining ≤ min (total incoming) (total source / (roomOrder + 1)) := by
  have hpos : 0 < roomOrder + 1 := Nat.succ_pos _
  refine ⟨le_min hincoming.1 ((Nat.le_div_iff_mul_le hpos).2 ?_),
    le_min hincoming.2.1 ((Nat.le_div_iff_mul_le hpos).2 ?_),
    le_min hincoming.2.2 ((Nat.le_div_iff_mul_le hpos).2 ?_)⟩
  · rw [Nat.mul_comm]
    exact hsource.1
  · rw [Nat.mul_comm, middle, Nat.mul_add]
    exact hsource.2.1
  · rw [Nat.mul_comm, total, Nat.mul_add, Nat.mul_add]
    exact hsource.2.2

def weightGain : ℕ := 19106

def adaptiveBand (source : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget weightGain (total p) (middle p) p.all
    (source.totalCap - total p) (source.middleCap - middle p)
    (source.slopeCap - p.all) (source.fuel p)

theorem adaptiveBand_antitone (source : SourceNumbers) {p q : FlagDegree}
    (h : Below p q) (hs : 0 < p.all) : adaptiveBand source q ≤ adaptiveBand source p := by
  have hy : 0 < middle p := by unfold middle; omega
  have ht : 0 < total p := by unfold total; omega
  have hfuel : source.fuel q ≤ source.fuel p := by
    unfold LocatorPhase6800Oracle.SourceNumbers.fuel
    exact min_le_min (Nat.div_le_div_left h.2.2 ht)
      (min_le_min (Nat.div_le_div_left h.2.1 hy) (Nat.div_le_div_left h.1 hs))
  unfold adaptiveBand
  have hsameFuel := powerBandBudget_mono weightGain
    (total q) (middle q) q.all (source.totalCap - total q) (source.middleCap - middle q)
    (source.slopeCap - q.all)
    (total p) (middle p) p.all (source.totalCap - total p) (source.middleCap - middle p)
    (source.slopeCap - p.all) (source.fuel q)
    (Nat.sub_le_sub_left h.2.2 _) (Nat.sub_le_sub_left h.2.1 _)
    (Nat.sub_le_sub_left h.1 _) h.2.2 h.2.1 h.1
  exact hsameFuel.trans (powerBandBudget_mono_fuel _ _ _ _ _ _ _ hfuel)

def adaptiveGate (source : SourceNumbers) (p : FlagDegree) : Prop :=
  adaptiveBand source p < source.gap

theorem adaptiveGate_mono (source : SourceNumbers) {p q : FlagDegree}
    (h : Below p q) (hs : 0 < p.all) (hactive : adaptiveGate source p) :
    adaptiveGate source q :=
  (adaptiveBand_antitone source h hs).trans_lt hactive

def adaptiveSource1 : SourceNumbers := ⟨126000, 1657, 372, 8469781001465397⟩
def adaptiveSource2 : SourceNumbers := ⟨572000, 3591, 806, 641107786271542526⟩
def adaptiveSource3 : SourceNumbers := ⟨5100000, 41445, 9300, 9071824415736420630585⟩

end ProximityPrize.SubmissionLower.Koala6831MovingStages

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
