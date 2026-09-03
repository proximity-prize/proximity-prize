import ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck29

namespace ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseChecked

open LocatorPhase6802Oracle LocatorPhaseBaseC2 LocatorPhaseBaseSparseCoreC2

set_option autoImplicit false
set_option maxRecDepth 100000

theorem sparse : CachedSparseAll := by
  intro R hR hpos
  have hlt : R < 30 := List.mem_range.mp hR
  interval_cases R <;>
  first
    | exact LocatorPhase6802BaseSparseCheck01.sparse
    | exact LocatorPhase6802BaseSparseCheck02.sparse
    | exact LocatorPhase6802BaseSparseCheck03.sparse
    | exact LocatorPhase6802BaseSparseCheck04.sparse
    | exact LocatorPhase6802BaseSparseCheck05.sparse
    | exact LocatorPhase6802BaseSparseCheck06.sparse
    | exact LocatorPhase6802BaseSparseCheck07.sparse
    | exact LocatorPhase6802BaseSparseCheck08.sparse
    | exact LocatorPhase6802BaseSparseCheck09.sparse
    | exact LocatorPhase6802BaseSparseCheck10.sparse
    | exact LocatorPhase6802BaseSparseCheck11.sparse
    | exact LocatorPhase6802BaseSparseCheck12.sparse
    | exact LocatorPhase6802BaseSparseCheck13.sparse
    | exact LocatorPhase6802BaseSparseCheck14.sparse
    | exact LocatorPhase6802BaseSparseCheck15.sparse
    | exact LocatorPhase6802BaseSparseCheck16.sparse
    | exact LocatorPhase6802BaseSparseCheck17.sparse
    | exact LocatorPhase6802BaseSparseCheck18.sparse
    | exact LocatorPhase6802BaseSparseCheck19.sparse
    | exact LocatorPhase6802BaseSparseCheck20.sparse
    | exact LocatorPhase6802BaseSparseCheck21.sparse
    | exact LocatorPhase6802BaseSparseCheck22.sparse
    | exact LocatorPhase6802BaseSparseCheck23.sparse
    | exact LocatorPhase6802BaseSparseCheck24.sparse
    | exact LocatorPhase6802BaseSparseCheck25.sparse
    | exact LocatorPhase6802BaseSparseCheck26.sparse
    | exact LocatorPhase6802BaseSparseCheck27.sparse
    | exact LocatorPhase6802BaseSparseCheck28.sparse
    | exact LocatorPhase6802BaseSparseCheck29.sparse

theorem shape : CachedShapeAll := by
  intro R hR hpos
  have hlt : R < 30 := List.mem_range.mp hR
  interval_cases R <;>
  first
    | exact LocatorPhase6802BaseSparseCheck01.shape
    | exact LocatorPhase6802BaseSparseCheck02.shape
    | exact LocatorPhase6802BaseSparseCheck03.shape
    | exact LocatorPhase6802BaseSparseCheck04.shape
    | exact LocatorPhase6802BaseSparseCheck05.shape
    | exact LocatorPhase6802BaseSparseCheck06.shape
    | exact LocatorPhase6802BaseSparseCheck07.shape
    | exact LocatorPhase6802BaseSparseCheck08.shape
    | exact LocatorPhase6802BaseSparseCheck09.shape
    | exact LocatorPhase6802BaseSparseCheck10.shape
    | exact LocatorPhase6802BaseSparseCheck11.shape
    | exact LocatorPhase6802BaseSparseCheck12.shape
    | exact LocatorPhase6802BaseSparseCheck13.shape
    | exact LocatorPhase6802BaseSparseCheck14.shape
    | exact LocatorPhase6802BaseSparseCheck15.shape
    | exact LocatorPhase6802BaseSparseCheck16.shape
    | exact LocatorPhase6802BaseSparseCheck17.shape
    | exact LocatorPhase6802BaseSparseCheck18.shape
    | exact LocatorPhase6802BaseSparseCheck19.shape
    | exact LocatorPhase6802BaseSparseCheck20.shape
    | exact LocatorPhase6802BaseSparseCheck21.shape
    | exact LocatorPhase6802BaseSparseCheck22.shape
    | exact LocatorPhase6802BaseSparseCheck23.shape
    | exact LocatorPhase6802BaseSparseCheck24.shape
    | exact LocatorPhase6802BaseSparseCheck25.shape
    | exact LocatorPhase6802BaseSparseCheck26.shape
    | exact LocatorPhase6802BaseSparseCheck27.shape
    | exact LocatorPhase6802BaseSparseCheck28.shape
    | exact LocatorPhase6802BaseSparseCheck29.shape

theorem candidatesSound :
    BaseCandidatesSound LocatorPhase6802BaseDirectData.lookup :=
  baseCandidatesSound_of_cached shape sparse

theorem stateLocalSound :
    StateLocalBaseOracleSound LocatorPhase6802BaseDirectData.cap := by
  change StateLocalBaseOracleSound
    (baseTableCap LocatorPhase6802BaseDirectData.lookup)
  exact stateLocalBaseOracleSound_of_candidates
    LocatorPhase6802BaseDirectData.lookup candidatesSound

#print axioms stateLocalSound

end ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseChecked
