/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
/- Derived from Lucieno (PR 618), and BitWonka (PR 581) for additional interpolation profiles.
   New 68.32 source parameters, adaptive schedule, cell assignments and integer receipts. Apache-2.0. -/
import ProximityPrize.SubmissionLower.K6833TerminalPrices

namespace ProximityPrize.SubmissionLower.K6833Residual

abbrev Profiles := Fin 6 × Fin 6 × Fin 6
def jetProfile : Fin 6 → JetProfile :=
  ![⟨120,54,25,164,1742,4,5⟩,
    ⟨107,42,20,145,3305,4,5⟩,
    ⟨107,44,20,146,2737,4,5⟩,
    ⟨128,51,24,174,3232,5,6⟩,
    ⟨128,53,24,174,2883,5,6⟩,
    ⟨146,63,26,198,3234,6,7⟩]
def cellConfig (ids : Profiles) : Fin 3 → JetProfile :=
  ![jetProfile ids.1, jetProfile ids.2.1, jetProfile ids.2.2]
end ProximityPrize.SubmissionLower.K6833Residual
