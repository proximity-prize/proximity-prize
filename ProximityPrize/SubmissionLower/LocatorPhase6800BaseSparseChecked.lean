import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck25
import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck26
import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck27
import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck28

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseChecked

open LocatorPhase6800Oracle LocatorPhase6800BaseDirectAudit
open LocatorPhase6800BaseSparseCore

set_option maxRecDepth 100000

theorem sparse : CachedSparseAll := by
  intro R hR hpos
  have hlt : R < 29 := List.mem_range.mp hR
  interval_cases R <;>
  first
    | exact LocatorPhase6800BaseSparseCheck01.sparse
    | exact LocatorPhase6800BaseSparseCheck02.sparse
    | exact LocatorPhase6800BaseSparseCheck03.sparse
    | exact LocatorPhase6800BaseSparseCheck04.sparse
    | exact LocatorPhase6800BaseSparseCheck05.sparse
    | exact LocatorPhase6800BaseSparseCheck06.sparse
    | exact LocatorPhase6800BaseSparseCheck07.sparse
    | exact LocatorPhase6800BaseSparseCheck08.sparse
    | exact LocatorPhase6800BaseSparseCheck09.sparse
    | exact LocatorPhase6800BaseSparseCheck10.sparse
    | exact LocatorPhase6800BaseSparseCheck11.sparse
    | exact LocatorPhase6800BaseSparseCheck12.sparse
    | exact LocatorPhase6800BaseSparseCheck13.sparse
    | exact LocatorPhase6800BaseSparseCheck14.sparse
    | exact LocatorPhase6800BaseSparseCheck15.sparse
    | exact LocatorPhase6800BaseSparseCheck16.sparse
    | exact LocatorPhase6800BaseSparseCheck17.sparse
    | exact LocatorPhase6800BaseSparseCheck18.sparse
    | exact LocatorPhase6800BaseSparseCheck19.sparse
    | exact LocatorPhase6800BaseSparseCheck20.sparse
    | exact LocatorPhase6800BaseSparseCheck21.sparse
    | exact LocatorPhase6800BaseSparseCheck22.sparse
    | exact LocatorPhase6800BaseSparseCheck23.sparse
    | exact LocatorPhase6800BaseSparseCheck24.sparse
    | exact LocatorPhase6800BaseSparseCheck25.sparse
    | exact LocatorPhase6800BaseSparseCheck26.sparse
    | exact LocatorPhase6800BaseSparseCheck27.sparse
    | exact LocatorPhase6800BaseSparseCheck28.sparse

theorem shape : CachedShapeAll := by
  intro R hR hpos
  have hlt : R < 29 := List.mem_range.mp hR
  interval_cases R <;>
  first
    | exact LocatorPhase6800BaseSparseCheck01.shape
    | exact LocatorPhase6800BaseSparseCheck02.shape
    | exact LocatorPhase6800BaseSparseCheck03.shape
    | exact LocatorPhase6800BaseSparseCheck04.shape
    | exact LocatorPhase6800BaseSparseCheck05.shape
    | exact LocatorPhase6800BaseSparseCheck06.shape
    | exact LocatorPhase6800BaseSparseCheck07.shape
    | exact LocatorPhase6800BaseSparseCheck08.shape
    | exact LocatorPhase6800BaseSparseCheck09.shape
    | exact LocatorPhase6800BaseSparseCheck10.shape
    | exact LocatorPhase6800BaseSparseCheck11.shape
    | exact LocatorPhase6800BaseSparseCheck12.shape
    | exact LocatorPhase6800BaseSparseCheck13.shape
    | exact LocatorPhase6800BaseSparseCheck14.shape
    | exact LocatorPhase6800BaseSparseCheck15.shape
    | exact LocatorPhase6800BaseSparseCheck16.shape
    | exact LocatorPhase6800BaseSparseCheck17.shape
    | exact LocatorPhase6800BaseSparseCheck18.shape
    | exact LocatorPhase6800BaseSparseCheck19.shape
    | exact LocatorPhase6800BaseSparseCheck20.shape
    | exact LocatorPhase6800BaseSparseCheck21.shape
    | exact LocatorPhase6800BaseSparseCheck22.shape
    | exact LocatorPhase6800BaseSparseCheck23.shape
    | exact LocatorPhase6800BaseSparseCheck24.shape
    | exact LocatorPhase6800BaseSparseCheck25.shape
    | exact LocatorPhase6800BaseSparseCheck26.shape
    | exact LocatorPhase6800BaseSparseCheck27.shape
    | exact LocatorPhase6800BaseSparseCheck28.shape

theorem candidatesSound (rows : Array BaseRow) :
    BaseCandidatesSound rows :=
  baseCandidatesSound_of_cached rows shape sparse

/-- State-local soundness for the direct base table. -/
theorem stateLocalSound :
    StateLocalBaseOracleSound
      LocatorPhase6800BaseDirectData.cap := by
  change StateLocalBaseOracleSound
    (LocatorPhase6800BaseDirectAudit.baseTableCap #[])
  exact stateLocalBaseOracleSound_of_candidates #[] (candidatesSound #[])

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseChecked
