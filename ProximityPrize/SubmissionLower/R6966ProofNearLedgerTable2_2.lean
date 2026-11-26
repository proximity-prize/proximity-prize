import ProximityPrize.SubmissionLower.R6966ProofNearLedgerApply

set_option Elab.async false

namespace Research6966.NearLedger
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def q2_2_0 : Fin 23 → Quote :=
  ![⟨.fixed, none, none, none⟩,
     ⟨.single, none, none, some ⟨9, 1⟩⟩,
     ⟨.single, none, none, some ⟨8, 1⟩⟩,
     ⟨.single, none, none, some ⟨8, 1⟩⟩,
     ⟨.single, none, none, some ⟨11, 1⟩⟩,
     ⟨.single, none, none, some ⟨10, 1⟩⟩,
     ⟨.single, none, none, some ⟨10, 1⟩⟩,
     ⟨.single, none, none, some ⟨10, 1⟩⟩,
     ⟨.single, none, none, some ⟨12, 1⟩⟩,
     ⟨.single, none, none, some ⟨12, 1⟩⟩,
     ⟨.single, none, some ⟨13, 1⟩, some ⟨13, 1⟩⟩,
     ⟨.single, none, some ⟨14, 1⟩, some ⟨14, 1⟩⟩,
     ⟨.single, none, some ⟨20, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.single, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.single, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.single, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.single, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.single, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.single, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_0_ok : ∀ j : Fin 23, (q2_2_0 j).Valid (band 2) 2 0 j := by
  decide +kernel

private def q2_2_1 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨9, 0⟩, none⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨9, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨9, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨9, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨20, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_1_ok : ∀ j : Fin 23, (q2_2_1 j).Valid (band 2) 2 1 j := by
  decide +kernel

private def q2_2_2 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨8, 0⟩, none⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨8, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨8, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨20, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_2_ok : ∀ j : Fin 23, (q2_2_2 j).Valid (band 2) 2 2 j := by
  decide +kernel

private def q2_2_3 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨8, 0⟩, none⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨8, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨8, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨8, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨20, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_3_ok : ∀ j : Fin 23, (q2_2_3 j).Valid (band 2) 2 3 j := by
  decide +kernel

private def q2_2_4 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨11, 0⟩, none⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨11, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨11, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨11, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨11, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_4_ok : ∀ j : Fin 23, (q2_2_4 j).Valid (band 2) 2 4 j := by
  decide +kernel

private def q2_2_5 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨10, 0⟩, none⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_5_ok : ∀ j : Fin 23, (q2_2_5 j).Valid (band 2) 2 5 j := by
  decide +kernel

private def q2_2_6 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨10, 0⟩, none⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_6_ok : ∀ j : Fin 23, (q2_2_6 j).Valid (band 2) 2 6 j := by
  decide +kernel

private def q2_2_7 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨10, 0⟩, none⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨10, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨10, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_7_ok : ∀ j : Fin 23, (q2_2_7 j).Valid (band 2) 2 7 j := by
  decide +kernel

private def q2_2_8 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨12, 0⟩, none⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨12, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨12, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨12, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨12, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨12, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨12, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨12, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨12, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨12, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨12, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨12, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_8_ok : ∀ j : Fin 23, (q2_2_8 j).Valid (band 2) 2 8 j := by
  decide +kernel

private def q2_2_9 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨12, 0⟩, none⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨12, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨12, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨12, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨12, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨21, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨21, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨21, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨19, 1⟩, none⟩]

private theorem q2_2_9_ok : ∀ j : Fin 23, (q2_2_9 j).Valid (band 2) 2 9 j := by
  decide +kernel

private def q2_2_10 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨13, 0⟩, some ⟨13, 0⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨13, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨13, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨13, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨13, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨13, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨13, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨13, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨13, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨13, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨13, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨13, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨13, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨13, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨13, 0⟩, none⟩]

private theorem q2_2_10_ok : ∀ j : Fin 23, (q2_2_10 j).Valid (band 2) 2 10 j := by
  decide +kernel

private def q2_2_11 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨14, 0⟩, some ⟨14, 0⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨9, 1⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨8, 1⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨14, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨14, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨14, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨14, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨14, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨14, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨14, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨14, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨14, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨14, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨14, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨14, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨14, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨14, 0⟩, none⟩]

private theorem q2_2_11_ok : ∀ j : Fin 23, (q2_2_11 j).Valid (band 2) 2 11 j := by
  decide +kernel

private def q2_2_12 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨15, 0⟩, some ⟨20, 0⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨20, 0⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨20, 0⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨20, 0⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨11, 1⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨10, 1⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨15, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, none, some ⟨15, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨15, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨15, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨15, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨15, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨15, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨15, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨15, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨15, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨15, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨15, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨15, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨15, 0⟩, none⟩]

private theorem q2_2_12_ok : ∀ j : Fin 23, (q2_2_12 j).Valid (band 2) 2 12 j := by
  decide +kernel

private def q2_2_13 : Fin 23 → Quote :=
  ![⟨.single, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.surface, none, some ⟨16, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, none, some ⟨16, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, none, some ⟨16, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, none, some ⟨16, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, none, some ⟨16, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨16, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨16, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨16, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨16, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 1⟩, some ⟨16, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨16, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨16, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨16, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨16, 0⟩, none⟩]

private theorem q2_2_13_ok : ∀ j : Fin 23, (q2_2_13 j).Valid (band 2) 2 13 j := by
  decide +kernel

private def q2_2_14 : Fin 23 → Quote :=
  ![⟨.single, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, none⟩]

private theorem q2_2_14_ok : ∀ j : Fin 23, (q2_2_14 j).Valid (band 2) 2 14 j := by
  decide +kernel

private def q2_2_15 : Fin 23 → Quote :=
  ![⟨.single, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, none⟩]

private theorem q2_2_15_ok : ∀ j : Fin 23, (q2_2_15 j).Valid (band 2) 2 15 j := by
  decide +kernel

private def q2_2_16 : Fin 23 → Quote :=
  ![⟨.single, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, none⟩]

private theorem q2_2_16_ok : ∀ j : Fin 23, (q2_2_16 j).Valid (band 2) 2 16 j := by
  decide +kernel

private def q2_2_17 : Fin 23 → Quote :=
  ![⟨.single, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, none⟩]

private theorem q2_2_17_ok : ∀ j : Fin 23, (q2_2_17 j).Valid (band 2) 2 17 j := by
  decide +kernel

private def q2_2_18 : Fin 23 → Quote :=
  ![⟨.single, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.axis, some ⟨17, 0⟩, some ⟨17, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 1⟩, some ⟨17, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨17, 0⟩, none⟩]

private theorem q2_2_18_ok : ∀ j : Fin 23, (q2_2_18 j).Valid (band 2) 2 18 j := by
  decide +kernel

private def q2_2_19 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨18, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨18, 0⟩, none⟩]

private theorem q2_2_19_ok : ∀ j : Fin 23, (q2_2_19 j).Valid (band 2) 2 19 j := by
  decide +kernel

private def q2_2_20 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨12, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨21, 0⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨18, 0⟩, some ⟨18, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨18, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 1⟩, some ⟨18, 0⟩, none⟩]

private theorem q2_2_20_ok : ∀ j : Fin 23, (q2_2_20 j).Valid (band 2) 2 20 j := by
  decide +kernel

private def q2_2_21 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨13, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨14, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨15, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨16, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, some ⟨19, 0⟩, none⟩]

private theorem q2_2_21_ok : ∀ j : Fin 23, (q2_2_21 j).Valid (band 2) 2 21 j := by
  decide +kernel

private def q2_2_22 : Fin 23 → Quote :=
  ![⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 0⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨13, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨14, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨15, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨16, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨17, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨18, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, some ⟨19, 1⟩⟩,
     ⟨.degree, some ⟨19, 0⟩, none, none⟩]

private theorem q2_2_22_ok : ∀ j : Fin 23, (q2_2_22 j).Valid (band 2) 2 22 j := by
  decide +kernel

def q2_2 : Fin 23 → Fin 23 → Quote :=
  ![q2_2_0, q2_2_1, q2_2_2, q2_2_3, q2_2_4, q2_2_5, q2_2_6, q2_2_7, q2_2_8, q2_2_9, q2_2_10, q2_2_11, q2_2_12, q2_2_13, q2_2_14, q2_2_15, q2_2_16, q2_2_17, q2_2_18, q2_2_19, q2_2_20, q2_2_21, q2_2_22]

theorem q2_2_ok (i j : Fin 23) : (q2_2 i j).Valid (band 2) 2 i j := by
  fin_cases i
  · exact q2_2_0_ok j
  · exact q2_2_1_ok j
  · exact q2_2_2_ok j
  · exact q2_2_3_ok j
  · exact q2_2_4_ok j
  · exact q2_2_5_ok j
  · exact q2_2_6_ok j
  · exact q2_2_7_ok j
  · exact q2_2_8_ok j
  · exact q2_2_9_ok j
  · exact q2_2_10_ok j
  · exact q2_2_11_ok j
  · exact q2_2_12_ok j
  · exact q2_2_13_ok j
  · exact q2_2_14_ok j
  · exact q2_2_15_ok j
  · exact q2_2_16_ok j
  · exact q2_2_17_ok j
  · exact q2_2_18_ok j
  · exact q2_2_19_ok j
  · exact q2_2_20_ok j
  · exact q2_2_21_ok j
  · exact q2_2_22_ok j

end Research6966.NearLedger
