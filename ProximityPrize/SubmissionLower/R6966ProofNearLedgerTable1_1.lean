import ProximityPrize.SubmissionLower.R6966ProofNearLedgerApply

set_option Elab.async false

namespace Research6966.NearLedger
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def q1_1_0 : Fin 23 → Quote :=
  ![⟨.fixed, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, none, none⟩,
     ⟨.single, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.single, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.single, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.single, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.single, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.single, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_0_ok : ∀ j : Fin 23, (q1_1_0 j).Valid (band 1) 1 0 j := by
  decide +kernel

private def q1_1_1 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_1_ok : ∀ j : Fin 23, (q1_1_1 j).Valid (band 1) 1 1 j := by
  decide +kernel

private def q1_1_2 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_2_ok : ∀ j : Fin 23, (q1_1_2 j).Valid (band 1) 1 2 j := by
  decide +kernel

private def q1_1_3 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_3_ok : ∀ j : Fin 23, (q1_1_3 j).Valid (band 1) 1 3 j := by
  decide +kernel

private def q1_1_4 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_4_ok : ∀ j : Fin 23, (q1_1_4 j).Valid (band 1) 1 4 j := by
  decide +kernel

private def q1_1_5 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_5_ok : ∀ j : Fin 23, (q1_1_5 j).Valid (band 1) 1 5 j := by
  decide +kernel

private def q1_1_6 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_6_ok : ∀ j : Fin 23, (q1_1_6 j).Valid (band 1) 1 6 j := by
  decide +kernel

private def q1_1_7 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_7_ok : ∀ j : Fin 23, (q1_1_7 j).Valid (band 1) 1 7 j := by
  decide +kernel

private def q1_1_8 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.surface, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_8_ok : ∀ j : Fin 23, (q1_1_8 j).Valid (band 1) 1 8 j := by
  decide +kernel

private def q1_1_9 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_9_ok : ∀ j : Fin 23, (q1_1_9 j).Valid (band 1) 1 9 j := by
  decide +kernel

private def q1_1_10 : Fin 23 → Quote :=
  ![⟨.single, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, none, none⟩,
     ⟨.affine, none, some ⟨0, 1⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 1⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 1⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨4, 1⟩, some ⟨4, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨4, 1⟩, some ⟨3, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_10_ok : ∀ j : Fin 23, (q1_1_10 j).Valid (band 1) 1 10 j := by
  decide +kernel

private def q1_1_11 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 0⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨0, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨0, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨7, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨7, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨7, 0⟩, none⟩]

private theorem q1_1_11_ok : ∀ j : Fin 23, (q1_1_11 j).Valid (band 1) 1 11 j := by
  decide +kernel

private def q1_1_12 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 0⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.affine, none, some ⟨1, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨1, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨1, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨1, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨1, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨1, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨1, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨1, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨1, 0⟩, none⟩]

private theorem q1_1_12_ok : ∀ j : Fin 23, (q1_1_12 j).Valid (band 1) 1 12 j := by
  decide +kernel

private def q1_1_13 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 0⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨0, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.affine, none, some ⟨2, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.axis, none, some ⟨2, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨2, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨2, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨2, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨2, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨2, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨2, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨2, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨2, 0⟩, none⟩]

private theorem q1_1_13_ok : ∀ j : Fin 23, (q1_1_13 j).Valid (band 1) 1 13 j := by
  decide +kernel

private def q1_1_14 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.affine, none, some ⟨4, 0⟩, some ⟨0, 1⟩⟩,
     ⟨.axis, none, some ⟨4, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.axis, none, some ⟨4, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.axis, none, some ⟨4, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨4, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.axis, some ⟨3, 1⟩, some ⟨4, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨4, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨4, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨4, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨4, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨4, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨4, 0⟩, none⟩]

private theorem q1_1_14_ok : ∀ j : Fin 23, (q1_1_14 j).Valid (band 1) 1 14 j := by
  decide +kernel

private def q1_1_15 : Fin 23 → Quote :=
  ![⟨.single, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 0⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨0, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨3, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨3, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨3, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨3, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨3, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨3, 0⟩, none⟩]

private theorem q1_1_15_ok : ∀ j : Fin 23, (q1_1_15 j).Valid (band 1) 1 15 j := by
  decide +kernel

private def q1_1_16 : Fin 23 → Quote :=
  ![⟨.single, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.surface, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.axis, some ⟨3, 0⟩, some ⟨3, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨3, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 1⟩, some ⟨3, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨3, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨3, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨3, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨3, 0⟩, none⟩]

private theorem q1_1_16_ok : ∀ j : Fin 23, (q1_1_16 j).Valid (band 1) 1 16 j := by
  decide +kernel

private def q1_1_17 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨5, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨5, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨5, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨5, 0⟩, none⟩]

private theorem q1_1_17_ok : ∀ j : Fin 23, (q1_1_17 j).Valid (band 1) 1 17 j := by
  decide +kernel

private def q1_1_18 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨5, 0⟩, some ⟨5, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨5, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨5, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨5, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 1⟩, some ⟨5, 0⟩, none⟩]

private theorem q1_1_18_ok : ∀ j : Fin 23, (q1_1_18 j).Valid (band 1) 1 18 j := by
  decide +kernel

private def q1_1_19 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, none⟩]

private theorem q1_1_19_ok : ∀ j : Fin 23, (q1_1_19 j).Valid (band 1) 1 19 j := by
  decide +kernel

private def q1_1_20 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, none⟩]

private theorem q1_1_20_ok : ∀ j : Fin 23, (q1_1_20 j).Valid (band 1) 1 20 j := by
  decide +kernel

private def q1_1_21 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨1, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨2, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨4, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, some ⟨6, 0⟩, none⟩]

private theorem q1_1_21_ok : ∀ j : Fin 23, (q1_1_21 j).Valid (band 1) 1 21 j := by
  decide +kernel

private def q1_1_22 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨7, 0⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨1, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨2, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨4, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨3, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨5, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, some ⟨6, 1⟩⟩,
     ⟨.degree, some ⟨6, 0⟩, none, none⟩]

private theorem q1_1_22_ok : ∀ j : Fin 23, (q1_1_22 j).Valid (band 1) 1 22 j := by
  decide +kernel

def q1_1 : Fin 23 → Fin 23 → Quote :=
  ![q1_1_0, q1_1_1, q1_1_2, q1_1_3, q1_1_4, q1_1_5, q1_1_6, q1_1_7, q1_1_8, q1_1_9, q1_1_10, q1_1_11, q1_1_12, q1_1_13, q1_1_14, q1_1_15, q1_1_16, q1_1_17, q1_1_18, q1_1_19, q1_1_20, q1_1_21, q1_1_22]

theorem q1_1_ok (i j : Fin 23) : (q1_1 i j).Valid (band 1) 1 i j := by
  fin_cases i
  · exact q1_1_0_ok j
  · exact q1_1_1_ok j
  · exact q1_1_2_ok j
  · exact q1_1_3_ok j
  · exact q1_1_4_ok j
  · exact q1_1_5_ok j
  · exact q1_1_6_ok j
  · exact q1_1_7_ok j
  · exact q1_1_8_ok j
  · exact q1_1_9_ok j
  · exact q1_1_10_ok j
  · exact q1_1_11_ok j
  · exact q1_1_12_ok j
  · exact q1_1_13_ok j
  · exact q1_1_14_ok j
  · exact q1_1_15_ok j
  · exact q1_1_16_ok j
  · exact q1_1_17_ok j
  · exact q1_1_18_ok j
  · exact q1_1_19_ok j
  · exact q1_1_20_ok j
  · exact q1_1_21_ok j
  · exact q1_1_22_ok j

#print axioms q1_1_ok
end Research6966.NearLedger
