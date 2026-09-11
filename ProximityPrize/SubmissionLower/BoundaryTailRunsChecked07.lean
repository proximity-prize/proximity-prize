import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics
import ProximityPrize.SubmissionLower.BoundaryTailRunsChecked06

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseChecks Lower80801.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

/- Receipt tables are checked in chunks of at most eight cells. -/
theorem runs_r31_part0:∀ i ∈ List.range 8,RunsAt 31 (0+i):=by
  decide +kernel

theorem runs_r31_part1:∀ i ∈ List.range 8,RunsAt 31 (8+i):=by
  decide +kernel

theorem runs_r31_part2:∀ i ∈ List.range 8,RunsAt 31 (16+i):=by
  decide +kernel

theorem runs_r31_part3:∀ i ∈ List.range 8,RunsAt 31 (24+i):=by
  decide +kernel

theorem runs_r31_part4:∀ i ∈ List.range 8,RunsAt 31 (32+i):=by
  decide +kernel

theorem runs_r31_part5:∀ i ∈ List.range 8,RunsAt 31 (40+i):=by
  decide +kernel

theorem runs_r31_part6:∀ i ∈ List.range 8,RunsAt 31 (48+i):=by
  decide +kernel

theorem runs_r31_part7:∀ i ∈ List.range 8,RunsAt 31 (56+i):=by
  decide +kernel

theorem runs_r31_part8:∀ i ∈ List.range 8,RunsAt 31 (64+i):=by
  decide +kernel

theorem runs_r31_part9:∀ i ∈ List.range 8,RunsAt 31 (72+i):=by
  decide +kernel

theorem runs_r31_part10:∀ i ∈ List.range 8,RunsAt 31 (80+i):=by
  decide +kernel

theorem runs_r31_part11:∀ i ∈ List.range 8,RunsAt 31 (88+i):=by
  decide +kernel

theorem runs_r31_part12:∀ i ∈ List.range 8,RunsAt 31 (96+i):=by
  decide +kernel

theorem runs_r31_part13:∀ i ∈ List.range 8,RunsAt 31 (104+i):=by
  decide +kernel

theorem runs_r31:∀ V ∈ List.range 112,RunsAt 31 V:=by
  intro V hV
  have hv:V < 112:=List.mem_range.mp hV
  by_cases h0:V < 8
  · have hi:=runs_r31_part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hi
  ·
    by_cases h1:V < 16
    · have hi:=runs_r31_part1 (V-8) (List.mem_range.mpr (by omega))
      simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hi
    ·
      by_cases h2:V < 24
      · have hi:=runs_r31_part2 (V-16) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hi
      ·
        by_cases h3:V < 32
        · have hi:=runs_r31_part3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hi
        ·
          by_cases h4:V < 40
          · have hi:=runs_r31_part4 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hi
          ·
            by_cases h5:V < 48
            · have hi:=runs_r31_part5 (V-40) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hi
            ·
              by_cases h6:V < 56
              · have hi:=runs_r31_part6 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hi
              ·
                by_cases h7:V < 64
                · have hi:=runs_r31_part7 (V-56) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hi
                ·
                  by_cases h8:V < 72
                  · have hi:=runs_r31_part8 (V-64) (List.mem_range.mpr (by omega))
                    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hi
                  ·
                    by_cases h9:V < 80
                    · have hi:=runs_r31_part9 (V-72) (List.mem_range.mpr (by omega))
                      simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hi
                    ·
                      by_cases h10:V < 88
                      · have hi:=runs_r31_part10 (V-80) (List.mem_range.mpr (by omega))
                        simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hi
                      ·
                        by_cases h11:V < 96
                        · have hi:=runs_r31_part11 (V-88) (List.mem_range.mpr (by omega))
                          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hi
                        ·
                          by_cases h12:V < 104
                          · have hi:=runs_r31_part12 (V-96) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hi
                          ·
                            have hi:=runs_r31_part13 (V-104) (List.mem_range.mpr (by omega))
                            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hi

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
