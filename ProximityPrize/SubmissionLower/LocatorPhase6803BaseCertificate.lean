import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck01
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck02
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck03
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck04
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck05
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck06
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck07
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck08
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck09
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck10
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck11
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck12
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck13
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck14
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck15
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck16
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck17
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck18
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck19
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck20
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck21
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck22
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck23
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck24
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck25
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck26
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck27
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck28
import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck29
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptSemantic

namespace ProximityPrize.SubmissionLower.LocatorPhase6803BaseCertificate

open LocatorPhase6803BaseDirectAudit

set_option autoImplicit false

theorem candidateChecks : BaseCandidateChecks #[] := by
  intro R hR hr
  have hR29 : R ≤ 29 := by
    have := List.mem_range.mp hR
    omega
  interval_cases R <;>
    first
    | exact LocatorPhase6803BaseRowCheck01.checked
    | exact LocatorPhase6803BaseRowCheck02.checked
    | exact LocatorPhase6803BaseRowCheck03.checked
    | exact LocatorPhase6803BaseRowCheck04.checked
    | exact LocatorPhase6803BaseRowCheck05.checked
    | exact LocatorPhase6803BaseRowCheck06.checked
    | exact LocatorPhase6803BaseRowCheck07.checked
    | exact LocatorPhase6803BaseRowCheck08.checked
    | exact LocatorPhase6803BaseRowCheck09.checked
    | exact LocatorPhase6803BaseRowCheck10.checked
    | exact LocatorPhase6803BaseRowCheck11.checked
    | exact LocatorPhase6803BaseRowCheck12.checked
    | exact LocatorPhase6803BaseRowCheck13.checked
    | exact LocatorPhase6803BaseRowCheck14.checked
    | exact LocatorPhase6803BaseRowCheck15.checked
    | exact LocatorPhase6803BaseRowCheck16.checked
    | exact LocatorPhase6803BaseRowCheck17.checked
    | exact LocatorPhase6803BaseRowCheck18.checked
    | exact LocatorPhase6803BaseRowCheck19.checked
    | exact LocatorPhase6803BaseRowCheck20.checked
    | exact LocatorPhase6803BaseRowCheck21.checked
    | exact LocatorPhase6803BaseRowCheck22.checked
    | exact LocatorPhase6803BaseRowCheck23.checked
    | exact LocatorPhase6803BaseRowCheck24.checked
    | exact LocatorPhase6803BaseRowCheck25.checked
    | exact LocatorPhase6803BaseRowCheck26.checked
    | exact LocatorPhase6803BaseRowCheck27.checked
    | exact LocatorPhase6803BaseRowCheck28.checked
    | exact LocatorPhase6803BaseRowCheck29.checked

theorem baseSound :
    LocatorPhase6803SemanticOracle.StateLocalBaseOracleSound
      LocatorPhase6803ReceiptSemantic.checkedBaseCap := by
  intro ι inst s p hpositive hrCap hyCap htCap
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi⟩ := hs
    have hiSum : (p i).all ≤ ∑ j ∈ s, (p j).all := by
      exact Finset.single_le_sum
        (f := fun j ↦ (p j).all) (fun _ _ ↦ Nat.zero_le _) hi
    have haggPositive : 1 ≤ (LocatorPhase6800Oracle.sumFlag s p).all := by
      rw [LocatorPhase6800Oracle.sumFlag_all]
      exact (hpositive i hi).trans hiSum
    have hnarrow : LocatorPhase6803ReceiptSemantic.NarrowState
        (LocatorPhase6800Oracle.sumFlag s p) :=
      ⟨haggPositive, hrCap, hyCap, htCap⟩
    rw [LocatorPhase6803ReceiptSemantic.checkedBaseCap_of_narrow hnarrow]
    have h := stateLocalBaseOracleSound_of_candidates #[]
      (baseCandidatesSound_of_checks #[] candidateChecks) s p hpositive
        hrCap hyCap htCap
    generalize hR : (LocatorPhase6800Oracle.sumFlag s p).all = R at h ⊢
    have hRlower : 1 ≤ R := by omega
    have hRupper : R ≤ 29 := by omega
    have hSum : ∑ i ∈ s, (p i).all = R := by
      simpa [LocatorPhase6800Oracle.sumFlag_all] using hR
    interval_cases R <;>
      simpa [hSum, baseTableCap, lookupBaseRow,
        LocatorPhase6803ReceiptSemantic.lookupBase] using h
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [LocatorPhase6803ReceiptSemantic.checkedBaseCap,
      LocatorPhase6803ReceiptSemantic.NarrowState,
      LocatorPhase6800Oracle.sumFlag]

end ProximityPrize.SubmissionLower.LocatorPhase6803BaseCertificate
