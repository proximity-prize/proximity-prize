import ProximityPrize.SubmissionLower.PackingFull6815_S07
import ProximityPrize.SubmissionLower.PackingLight6815_S13
namespace ProximityPrize.SubmissionLower.PackingData6815
open PackingSemantics6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
def full_slope (j : ℕ) : ℕ := match j with
  | 0 => PackingFull6815_S00.slope
  | 1 => PackingFull6815_S01.slope
  | 2 => PackingFull6815_S02.slope
  | 3 => PackingFull6815_S03.slope
  | 4 => PackingFull6815_S04.slope
  | 5 => PackingFull6815_S05.slope
  | 6 => PackingFull6815_S06.slope
  | 7 => PackingFull6815_S07.slope
  | _ => 0
def full_own (j : ℕ) : ℕ → Array ℕ := match j with
  | 0 => PackingFull6815_S00.own
  | 1 => PackingFull6815_S01.own
  | 2 => PackingFull6815_S02.own
  | 3 => PackingFull6815_S03.own
  | 4 => PackingFull6815_S04.own
  | 5 => PackingFull6815_S05.own
  | 6 => PackingFull6815_S06.own
  | 7 => PackingFull6815_S07.own
  | _ => fun _ => #[]
def full_packed (j : ℕ) : ℕ → Array ℕ := match j with
  | 0 => PackingFull6815_S00.packed
  | 1 => PackingFull6815_S01.packed
  | 2 => PackingFull6815_S02.packed
  | 3 => PackingFull6815_S03.packed
  | 4 => PackingFull6815_S04.packed
  | 5 => PackingFull6815_S05.packed
  | 6 => PackingFull6815_S06.packed
  | 7 => PackingFull6815_S07.packed
  | _ => fun _ => #[]
theorem full_bellman (j : ℕ) (hj : j<8) : AffineFactorAggregate6808.BellmanRows 39 182 (lookup (full_own j)) (lookup (full_packed j)) := by
  interval_cases j
  · exact PackingFull6815_S00.bellman
  · exact PackingFull6815_S01.bellman
  · exact PackingFull6815_S02.bellman
  · exact PackingFull6815_S03.bellman
  · exact PackingFull6815_S04.bellman
  · exact PackingFull6815_S05.bellman
  · exact PackingFull6815_S06.bellman
  · exact PackingFull6815_S07.bellman
def light_slope (j : ℕ) : ℕ := match j with
  | 0 => PackingLight6815_S00.slope
  | 1 => PackingLight6815_S01.slope
  | 2 => PackingLight6815_S02.slope
  | 3 => PackingLight6815_S03.slope
  | 4 => PackingLight6815_S04.slope
  | 5 => PackingLight6815_S05.slope
  | 6 => PackingLight6815_S06.slope
  | 7 => PackingLight6815_S07.slope
  | 8 => PackingLight6815_S08.slope
  | 9 => PackingLight6815_S09.slope
  | 10 => PackingLight6815_S10.slope
  | 11 => PackingLight6815_S11.slope
  | 12 => PackingLight6815_S12.slope
  | 13 => PackingLight6815_S13.slope
  | _ => 0
def light_own (j : ℕ) : ℕ → Array ℕ := match j with
  | 0 => PackingLight6815_S00.own
  | 1 => PackingLight6815_S01.own
  | 2 => PackingLight6815_S02.own
  | 3 => PackingLight6815_S03.own
  | 4 => PackingLight6815_S04.own
  | 5 => PackingLight6815_S05.own
  | 6 => PackingLight6815_S06.own
  | 7 => PackingLight6815_S07.own
  | 8 => PackingLight6815_S08.own
  | 9 => PackingLight6815_S09.own
  | 10 => PackingLight6815_S10.own
  | 11 => PackingLight6815_S11.own
  | 12 => PackingLight6815_S12.own
  | 13 => PackingLight6815_S13.own
  | _ => fun _ => #[]
def light_packed (j : ℕ) : ℕ → Array ℕ := match j with
  | 0 => PackingLight6815_S00.packed
  | 1 => PackingLight6815_S01.packed
  | 2 => PackingLight6815_S02.packed
  | 3 => PackingLight6815_S03.packed
  | 4 => PackingLight6815_S04.packed
  | 5 => PackingLight6815_S05.packed
  | 6 => PackingLight6815_S06.packed
  | 7 => PackingLight6815_S07.packed
  | 8 => PackingLight6815_S08.packed
  | 9 => PackingLight6815_S09.packed
  | 10 => PackingLight6815_S10.packed
  | 11 => PackingLight6815_S11.packed
  | 12 => PackingLight6815_S12.packed
  | 13 => PackingLight6815_S13.packed
  | _ => fun _ => #[]
theorem light_bellman (j : ℕ) (hj : j<14) : RectangularPacking6815.Bellman 19 70 (lookup (light_own j)) (lookup (light_packed j)) := by
  interval_cases j
  · exact PackingLight6815_S00.bellman
  · exact PackingLight6815_S01.bellman
  · exact PackingLight6815_S02.bellman
  · exact PackingLight6815_S03.bellman
  · exact PackingLight6815_S04.bellman
  · exact PackingLight6815_S05.bellman
  · exact PackingLight6815_S06.bellman
  · exact PackingLight6815_S07.bellman
  · exact PackingLight6815_S08.bellman
  · exact PackingLight6815_S09.bellman
  · exact PackingLight6815_S10.bellman
  · exact PackingLight6815_S11.bellman
  · exact PackingLight6815_S12.bellman
  · exact PackingLight6815_S13.bellman
end ProximityPrize.SubmissionLower.PackingData6815
