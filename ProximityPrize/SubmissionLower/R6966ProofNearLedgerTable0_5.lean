import ProximityPrize.SubmissionLower.R6966ProofNearLedgerApply

set_option Elab.async false

namespace Research6966.NearLedger
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def q0_5_0 : Fin 23 → Quote :=
  ![⟨.fixed, none, none, none⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨37, 1⟩, some ⟨37, 1⟩⟩,
     ⟨.single, none, some ⟨38, 1⟩, some ⟨38, 1⟩⟩,
     ⟨.single, none, some ⟨38, 1⟩, some ⟨38, 1⟩⟩,
     ⟨.single, none, some ⟨38, 1⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 1⟩, none⟩]

private theorem q0_5_0_ok : ∀ j : Fin 23, (q0_5_0 j).Valid (band 0) 5 0 j := by
  decide +kernel

private def q0_5_1 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.surface, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.surface, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_1_ok : ∀ j : Fin 23, (q0_5_1 j).Valid (band 0) 5 1 j := by
  decide +kernel

private def q0_5_2 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.surface, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_2_ok : ∀ j : Fin 23, (q0_5_2 j).Valid (band 0) 5 2 j := by
  decide +kernel

private def q0_5_3 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_3_ok : ∀ j : Fin 23, (q0_5_3 j).Valid (band 0) 5 3 j := by
  decide +kernel

private def q0_5_4 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_4_ok : ∀ j : Fin 23, (q0_5_4 j).Valid (band 0) 5 4 j := by
  decide +kernel

private def q0_5_5 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_5_ok : ∀ j : Fin 23, (q0_5_5 j).Valid (band 0) 5 5 j := by
  decide +kernel

private def q0_5_6 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_6_ok : ∀ j : Fin 23, (q0_5_6 j).Valid (band 0) 5 6 j := by
  decide +kernel

private def q0_5_7 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_7_ok : ∀ j : Fin 23, (q0_5_7 j).Valid (band 0) 5 7 j := by
  decide +kernel

private def q0_5_8 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_8_ok : ∀ j : Fin 23, (q0_5_8 j).Valid (band 0) 5 8 j := by
  decide +kernel

private def q0_5_9 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_9_ok : ∀ j : Fin 23, (q0_5_9 j).Valid (band 0) 5 9 j := by
  decide +kernel

private def q0_5_10 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_10_ok : ∀ j : Fin 23, (q0_5_10 j).Valid (band 0) 5 10 j := by
  decide +kernel

private def q0_5_11 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_11_ok : ∀ j : Fin 23, (q0_5_11 j).Valid (band 0) 5 11 j := by
  decide +kernel

private def q0_5_12 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_12_ok : ∀ j : Fin 23, (q0_5_12 j).Valid (band 0) 5 12 j := by
  decide +kernel

private def q0_5_13 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_13_ok : ∀ j : Fin 23, (q0_5_13 j).Valid (band 0) 5 13 j := by
  decide +kernel

private def q0_5_14 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_14_ok : ∀ j : Fin 23, (q0_5_14 j).Valid (band 0) 5 14 j := by
  decide +kernel

private def q0_5_15 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_15_ok : ∀ j : Fin 23, (q0_5_15 j).Valid (band 0) 5 15 j := by
  decide +kernel

private def q0_5_16 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_16_ok : ∀ j : Fin 23, (q0_5_16 j).Valid (band 0) 5 16 j := by
  decide +kernel

private def q0_5_17 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨37, 0⟩, none⟩]

private theorem q0_5_17_ok : ∀ j : Fin 23, (q0_5_17 j).Valid (band 0) 5 17 j := by
  decide +kernel

private def q0_5_18 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨37, 0⟩, some ⟨37, 0⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨37, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 1⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 1⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 1⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 1⟩, none⟩]

private theorem q0_5_18_ok : ∀ j : Fin 23, (q0_5_18 j).Valid (band 0) 5 18 j := by
  decide +kernel

private def q0_5_19 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨38, 0⟩, some ⟨38, 0⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 0⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 0⟩, none⟩]

private theorem q0_5_19_ok : ∀ j : Fin 23, (q0_5_19 j).Valid (band 0) 5 19 j := by
  decide +kernel

private def q0_5_20 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨38, 0⟩, some ⟨38, 0⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 0⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 0⟩, none⟩]

private theorem q0_5_20_ok : ∀ j : Fin 23, (q0_5_20 j).Valid (band 0) 5 20 j := by
  decide +kernel

private def q0_5_21 : Fin 23 → Quote :=
  ![⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 0⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨37, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 0⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.axis, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 0⟩, some ⟨38, 1⟩⟩,
     ⟨.large, none, some ⟨38, 0⟩, none⟩]

private theorem q0_5_21_ok : ∀ j : Fin 23, (q0_5_21 j).Valid (band 0) 5 21 j := by
  decide +kernel

private def q0_5_22 : Fin 23 → Quote :=
  ![⟨.axis, none, none, some ⟨38, 0⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨37, 1⟩⟩,
     ⟨.axis, none, none, some ⟨38, 0⟩⟩,
     ⟨.axis, none, none, some ⟨38, 1⟩⟩,
     ⟨.axis, none, none, some ⟨38, 1⟩⟩,
     ⟨.large, none, none, some ⟨38, 1⟩⟩,
     ⟨.large, none, none, none⟩]

private theorem q0_5_22_ok : ∀ j : Fin 23, (q0_5_22 j).Valid (band 0) 5 22 j := by
  decide +kernel

def q0_5 : Fin 23 → Fin 23 → Quote :=
  ![q0_5_0, q0_5_1, q0_5_2, q0_5_3, q0_5_4, q0_5_5, q0_5_6, q0_5_7, q0_5_8, q0_5_9, q0_5_10, q0_5_11, q0_5_12, q0_5_13, q0_5_14, q0_5_15, q0_5_16, q0_5_17, q0_5_18, q0_5_19, q0_5_20, q0_5_21, q0_5_22]

theorem q0_5_ok (i j : Fin 23) : (q0_5 i j).Valid (band 0) 5 i j := by
  fin_cases i
  · exact q0_5_0_ok j
  · exact q0_5_1_ok j
  · exact q0_5_2_ok j
  · exact q0_5_3_ok j
  · exact q0_5_4_ok j
  · exact q0_5_5_ok j
  · exact q0_5_6_ok j
  · exact q0_5_7_ok j
  · exact q0_5_8_ok j
  · exact q0_5_9_ok j
  · exact q0_5_10_ok j
  · exact q0_5_11_ok j
  · exact q0_5_12_ok j
  · exact q0_5_13_ok j
  · exact q0_5_14_ok j
  · exact q0_5_15_ok j
  · exact q0_5_16_ok j
  · exact q0_5_17_ok j
  · exact q0_5_18_ok j
  · exact q0_5_19_ok j
  · exact q0_5_20_ok j
  · exact q0_5_21_ok j
  · exact q0_5_22_ok j

end Research6966.NearLedger
