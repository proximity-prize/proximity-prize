import ProximityPrize.SubmissionLower.R6966ProofNearLedgerApply

set_option Elab.async false

namespace Research6966.NearLedger
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def q1_3_0 : Fin 23 → Quote :=
  ![⟨.fixed, none, none, none⟩,
     ⟨.single, none, some ⟨25, 1⟩, some ⟨25, 1⟩⟩,
     ⟨.single, none, some ⟨25, 1⟩, some ⟨24, 1⟩⟩,
     ⟨.single, none, some ⟨25, 1⟩, some ⟨24, 1⟩⟩,
     ⟨.single, none, some ⟨25, 1⟩, some ⟨24, 1⟩⟩,
     ⟨.single, none, some ⟨25, 1⟩, some ⟨23, 1⟩⟩,
     ⟨.single, none, some ⟨25, 1⟩, some ⟨22, 1⟩⟩,
     ⟨.single, none, some ⟨25, 1⟩, some ⟨22, 1⟩⟩,
     ⟨.single, none, some ⟨25, 1⟩, some ⟨22, 1⟩⟩,
     ⟨.single, none, some ⟨26, 1⟩, some ⟨26, 1⟩⟩,
     ⟨.single, none, some ⟨27, 1⟩, some ⟨27, 1⟩⟩,
     ⟨.single, none, some ⟨27, 1⟩, some ⟨27, 1⟩⟩,
     ⟨.single, none, some ⟨28, 1⟩, some ⟨28, 1⟩⟩,
     ⟨.single, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.single, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.single, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.single, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.single, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.single, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.single, some ⟨30, 1⟩, some ⟨33, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨33, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, none⟩]

private theorem q1_3_0_ok : ∀ j : Fin 23, (q1_3_0 j).Valid (band 1) 3 0 j := by
  decide +kernel

private def q1_3_1 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨25, 0⟩, some ⟨25, 0⟩⟩,
     ⟨.surface, none, some ⟨25, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.surface, none, some ⟨25, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨25, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨25, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨25, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.surface, none, some ⟨25, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨25, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨25, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨25, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨25, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨25, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨25, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨33, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨33, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, none⟩]

private theorem q1_3_1_ok : ∀ j : Fin 23, (q1_3_1 j).Valid (band 1) 3 1 j := by
  decide +kernel

private def q1_3_2 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨24, 0⟩, some ⟨25, 0⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨33, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨33, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, none⟩]

private theorem q1_3_2_ok : ∀ j : Fin 23, (q1_3_2 j).Valid (band 1) 3 2 j := by
  decide +kernel

private def q1_3_3 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨24, 0⟩, some ⟨25, 0⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨33, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨33, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, none⟩]

private theorem q1_3_3_ok : ∀ j : Fin 23, (q1_3_3 j).Valid (band 1) 3 3 j := by
  decide +kernel

private def q1_3_4 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨24, 0⟩, some ⟨25, 0⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨24, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨24, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨33, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨33, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨33, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨33, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨33, 0⟩, none⟩]

private theorem q1_3_4_ok : ∀ j : Fin 23, (q1_3_4 j).Valid (band 1) 3 4 j := by
  decide +kernel

private def q1_3_5 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨23, 0⟩, some ⟨25, 0⟩⟩,
     ⟨.surface, none, some ⟨23, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.surface, none, some ⟨23, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨23, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨23, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨23, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨23, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨23, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨23, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨23, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨23, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨23, 0⟩, none⟩]

private theorem q1_3_5_ok : ∀ j : Fin 23, (q1_3_5 j).Valid (band 1) 3 5 j := by
  decide +kernel

private def q1_3_6 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨22, 0⟩, some ⟨25, 0⟩⟩,
     ⟨.surface, none, some ⟨22, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.surface, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨22, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨22, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨22, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨22, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨22, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨22, 0⟩, none⟩]

private theorem q1_3_6_ok : ∀ j : Fin 23, (q1_3_6 j).Valid (band 1) 3 6 j := by
  decide +kernel

private def q1_3_7 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨22, 0⟩, some ⟨25, 0⟩⟩,
     ⟨.surface, none, some ⟨22, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.surface, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.surface, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨22, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨22, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨22, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨22, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨22, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨22, 0⟩, none⟩]

private theorem q1_3_7_ok : ∀ j : Fin 23, (q1_3_7 j).Valid (band 1) 3 7 j := by
  decide +kernel

private def q1_3_8 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨22, 0⟩, some ⟨25, 0⟩⟩,
     ⟨.surface, none, some ⟨22, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨22, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨22, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨22, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨22, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨22, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨22, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨22, 0⟩, none⟩]

private theorem q1_3_8_ok : ∀ j : Fin 23, (q1_3_8 j).Valid (band 1) 3 8 j := by
  decide +kernel

private def q1_3_9 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨26, 0⟩, some ⟨26, 0⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨26, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨26, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨26, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨26, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨26, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨26, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨26, 0⟩, none⟩]

private theorem q1_3_9_ok : ∀ j : Fin 23, (q1_3_9 j).Valid (band 1) 3 9 j := by
  decide +kernel

private def q1_3_10 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨27, 0⟩, some ⟨27, 0⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨27, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨27, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨27, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨27, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨27, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨27, 0⟩, none⟩]

private theorem q1_3_10_ok : ∀ j : Fin 23, (q1_3_10 j).Valid (band 1) 3 10 j := by
  decide +kernel

private def q1_3_11 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨27, 0⟩, some ⟨27, 0⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨27, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨27, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨27, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨27, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨27, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨27, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨27, 0⟩, none⟩]

private theorem q1_3_11_ok : ∀ j : Fin 23, (q1_3_11 j).Valid (band 1) 3 11 j := by
  decide +kernel

private def q1_3_12 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨28, 0⟩, some ⟨28, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨25, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨24, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨28, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨28, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, none⟩]

private theorem q1_3_12_ok : ∀ j : Fin 23, (q1_3_12 j).Valid (band 1) 3 12 j := by
  decide +kernel

private def q1_3_13 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨28, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨28, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, none⟩]

private theorem q1_3_13_ok : ∀ j : Fin 23, (q1_3_13 j).Valid (band 1) 3 13 j := by
  decide +kernel

private def q1_3_14 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨28, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨28, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, none⟩]

private theorem q1_3_14_ok : ∀ j : Fin 23, (q1_3_14 j).Valid (band 1) 3 14 j := by
  decide +kernel

private def q1_3_15 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨28, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨28, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, none⟩]

private theorem q1_3_15_ok : ∀ j : Fin 23, (q1_3_15 j).Valid (band 1) 3 15 j := by
  decide +kernel

private def q1_3_16 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, none, some ⟨28, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 1⟩, some ⟨28, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨28, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨28, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨28, 0⟩, none⟩]

private theorem q1_3_16_ok : ∀ j : Fin 23, (q1_3_16 j).Valid (band 1) 3 16 j := by
  decide +kernel

private def q1_3_17 : Fin 23 → Quote :=
  ![⟨.single, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨29, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨29, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨29, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨29, 0⟩, none⟩]

private theorem q1_3_17_ok : ∀ j : Fin 23, (q1_3_17 j).Valid (band 1) 3 17 j := by
  decide +kernel

private def q1_3_18 : Fin 23 → Quote :=
  ![⟨.single, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨29, 0⟩, some ⟨29, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 1⟩, some ⟨29, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨29, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨29, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨29, 0⟩, none⟩]

private theorem q1_3_18_ok : ∀ j : Fin 23, (q1_3_18 j).Valid (band 1) 3 18 j := by
  decide +kernel

private def q1_3_19 : Fin 23 → Quote :=
  ![⟨.single, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.axis, some ⟨30, 0⟩, some ⟨30, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 1⟩, some ⟨30, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨30, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨30, 0⟩, none⟩]

private theorem q1_3_19_ok : ∀ j : Fin 23, (q1_3_19 j).Valid (band 1) 3 19 j := by
  decide +kernel

private def q1_3_20 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨32, 0⟩, some ⟨32, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨32, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 1⟩, some ⟨32, 0⟩, none⟩]

private theorem q1_3_20_ok : ∀ j : Fin 23, (q1_3_20 j).Valid (band 1) 3 20 j := by
  decide +kernel

private def q1_3_21 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨23, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨26, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨27, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨29, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, some ⟨31, 0⟩, none⟩]

private theorem q1_3_21_ok : ∀ j : Fin 23, (q1_3_21 j).Valid (band 1) 3 21 j := by
  decide +kernel

private def q1_3_22 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨31, 0⟩, none, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨33, 0⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨23, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨22, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨26, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨27, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨27, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨28, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨29, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨29, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨30, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨32, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, some ⟨31, 1⟩⟩,
     ⟨.degree, some ⟨31, 0⟩, none, none⟩]

private theorem q1_3_22_ok : ∀ j : Fin 23, (q1_3_22 j).Valid (band 1) 3 22 j := by
  decide +kernel

def q1_3 : Fin 23 → Fin 23 → Quote :=
  ![q1_3_0, q1_3_1, q1_3_2, q1_3_3, q1_3_4, q1_3_5, q1_3_6, q1_3_7, q1_3_8, q1_3_9, q1_3_10, q1_3_11, q1_3_12, q1_3_13, q1_3_14, q1_3_15, q1_3_16, q1_3_17, q1_3_18, q1_3_19, q1_3_20, q1_3_21, q1_3_22]

theorem q1_3_ok (i j : Fin 23) : (q1_3 i j).Valid (band 1) 3 i j := by
  fin_cases i
  · exact q1_3_0_ok j
  · exact q1_3_1_ok j
  · exact q1_3_2_ok j
  · exact q1_3_3_ok j
  · exact q1_3_4_ok j
  · exact q1_3_5_ok j
  · exact q1_3_6_ok j
  · exact q1_3_7_ok j
  · exact q1_3_8_ok j
  · exact q1_3_9_ok j
  · exact q1_3_10_ok j
  · exact q1_3_11_ok j
  · exact q1_3_12_ok j
  · exact q1_3_13_ok j
  · exact q1_3_14_ok j
  · exact q1_3_15_ok j
  · exact q1_3_16_ok j
  · exact q1_3_17_ok j
  · exact q1_3_18_ok j
  · exact q1_3_19_ok j
  · exact q1_3_20_ok j
  · exact q1_3_21_ok j
  · exact q1_3_22_ok j

end Research6966.NearLedger
