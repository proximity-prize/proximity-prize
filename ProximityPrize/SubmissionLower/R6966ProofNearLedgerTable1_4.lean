import ProximityPrize.SubmissionLower.R6966ProofNearLedgerApply

set_option Elab.async false

namespace Research6966.NearLedger
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def q1_4_0 : Fin 23 → Quote :=
  ![⟨.fixed, none, none, none⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨34, 1⟩, some ⟨34, 1⟩⟩,
     ⟨.single, none, some ⟨35, 1⟩, some ⟨35, 1⟩⟩,
     ⟨.single, none, some ⟨35, 1⟩, some ⟨35, 1⟩⟩,
     ⟨.single, none, some ⟨35, 1⟩, some ⟨35, 1⟩⟩,
     ⟨.single, none, some ⟨35, 1⟩, some ⟨35, 1⟩⟩,
     ⟨.single, none, some ⟨35, 1⟩, some ⟨35, 1⟩⟩,
     ⟨.single, some ⟨36, 1⟩, some ⟨36, 1⟩, some ⟨36, 1⟩⟩,
     ⟨.single, some ⟨36, 1⟩, some ⟨36, 1⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨36, 1⟩, none⟩]

private theorem q1_4_0_ok : ∀ j : Fin 23, (q1_4_0 j).Valid (band 1) 4 0 j := by
  decide +kernel

private def q1_4_1 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_1_ok : ∀ j : Fin 23, (q1_4_1 j).Valid (band 1) 4 1 j := by
  decide +kernel

private def q1_4_2 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_2_ok : ∀ j : Fin 23, (q1_4_2 j).Valid (band 1) 4 2 j := by
  decide +kernel

private def q1_4_3 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_3_ok : ∀ j : Fin 23, (q1_4_3 j).Valid (band 1) 4 3 j := by
  decide +kernel

private def q1_4_4 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_4_ok : ∀ j : Fin 23, (q1_4_4 j).Valid (band 1) 4 4 j := by
  decide +kernel

private def q1_4_5 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.surface, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_5_ok : ∀ j : Fin 23, (q1_4_5 j).Valid (band 1) 4 5 j := by
  decide +kernel

private def q1_4_6 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_6_ok : ∀ j : Fin 23, (q1_4_6 j).Valid (band 1) 4 6 j := by
  decide +kernel

private def q1_4_7 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_7_ok : ∀ j : Fin 23, (q1_4_7 j).Valid (band 1) 4 7 j := by
  decide +kernel

private def q1_4_8 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_8_ok : ∀ j : Fin 23, (q1_4_8 j).Valid (band 1) 4 8 j := by
  decide +kernel

private def q1_4_9 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_9_ok : ∀ j : Fin 23, (q1_4_9 j).Valid (band 1) 4 9 j := by
  decide +kernel

private def q1_4_10 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_10_ok : ∀ j : Fin 23, (q1_4_10 j).Valid (band 1) 4 10 j := by
  decide +kernel

private def q1_4_11 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_11_ok : ∀ j : Fin 23, (q1_4_11 j).Valid (band 1) 4 11 j := by
  decide +kernel

private def q1_4_12 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_12_ok : ∀ j : Fin 23, (q1_4_12 j).Valid (band 1) 4 12 j := by
  decide +kernel

private def q1_4_13 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_13_ok : ∀ j : Fin 23, (q1_4_13 j).Valid (band 1) 4 13 j := by
  decide +kernel

private def q1_4_14 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨34, 0⟩, some ⟨34, 0⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨34, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨34, 0⟩, none⟩]

private theorem q1_4_14_ok : ∀ j : Fin 23, (q1_4_14 j).Valid (band 1) 4 14 j := by
  decide +kernel

private def q1_4_15 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨35, 0⟩, some ⟨35, 0⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, none⟩]

private theorem q1_4_15_ok : ∀ j : Fin 23, (q1_4_15 j).Valid (band 1) 4 15 j := by
  decide +kernel

private def q1_4_16 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨35, 0⟩, some ⟨35, 0⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, none⟩]

private theorem q1_4_16_ok : ∀ j : Fin 23, (q1_4_16 j).Valid (band 1) 4 16 j := by
  decide +kernel

private def q1_4_17 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨35, 0⟩, some ⟨35, 0⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, none⟩]

private theorem q1_4_17_ok : ∀ j : Fin 23, (q1_4_17 j).Valid (band 1) 4 17 j := by
  decide +kernel

private def q1_4_18 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨35, 0⟩, some ⟨35, 0⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, none⟩]

private theorem q1_4_18_ok : ∀ j : Fin 23, (q1_4_18 j).Valid (band 1) 4 18 j := by
  decide +kernel

private def q1_4_19 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨35, 0⟩, some ⟨35, 0⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, none, some ⟨35, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 1⟩, some ⟨35, 0⟩, none⟩]

private theorem q1_4_19_ok : ∀ j : Fin 23, (q1_4_19 j).Valid (band 1) 4 19 j := by
  decide +kernel

private def q1_4_20 : Fin 23 → Quote :=
  ![⟨.single, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨36, 0⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 0⟩, some ⟨36, 0⟩, none⟩]

private theorem q1_4_20_ok : ∀ j : Fin 23, (q1_4_20 j).Valid (band 1) 4 20 j := by
  decide +kernel

private def q1_4_21 : Fin 23 → Quote :=
  ![⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨36, 0⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 0⟩, some ⟨36, 0⟩, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 0⟩, some ⟨36, 0⟩, none⟩]

private theorem q1_4_21_ok : ∀ j : Fin 23, (q1_4_21 j).Valid (band 1) 4 21 j := by
  decide +kernel

private def q1_4_22 : Fin 23 → Quote :=
  ![⟨.axis, some ⟨36, 0⟩, none, some ⟨36, 0⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨34, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨35, 1⟩⟩,
     ⟨.axis, some ⟨36, 0⟩, none, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 0⟩, none, some ⟨36, 1⟩⟩,
     ⟨.native, some ⟨36, 0⟩, none, none⟩]

private theorem q1_4_22_ok : ∀ j : Fin 23, (q1_4_22 j).Valid (band 1) 4 22 j := by
  decide +kernel

def q1_4 : Fin 23 → Fin 23 → Quote :=
  ![q1_4_0, q1_4_1, q1_4_2, q1_4_3, q1_4_4, q1_4_5, q1_4_6, q1_4_7, q1_4_8, q1_4_9, q1_4_10, q1_4_11, q1_4_12, q1_4_13, q1_4_14, q1_4_15, q1_4_16, q1_4_17, q1_4_18, q1_4_19, q1_4_20, q1_4_21, q1_4_22]

theorem q1_4_ok (i j : Fin 23) : (q1_4 i j).Valid (band 1) 4 i j := by
  fin_cases i
  · exact q1_4_0_ok j
  · exact q1_4_1_ok j
  · exact q1_4_2_ok j
  · exact q1_4_3_ok j
  · exact q1_4_4_ok j
  · exact q1_4_5_ok j
  · exact q1_4_6_ok j
  · exact q1_4_7_ok j
  · exact q1_4_8_ok j
  · exact q1_4_9_ok j
  · exact q1_4_10_ok j
  · exact q1_4_11_ok j
  · exact q1_4_12_ok j
  · exact q1_4_13_ok j
  · exact q1_4_14_ok j
  · exact q1_4_15_ok j
  · exact q1_4_16_ok j
  · exact q1_4_17_ok j
  · exact q1_4_18_ok j
  · exact q1_4_19_ok j
  · exact q1_4_20_ok j
  · exact q1_4_21_ok j
  · exact q1_4_22_ok j

end Research6966.NearLedger
