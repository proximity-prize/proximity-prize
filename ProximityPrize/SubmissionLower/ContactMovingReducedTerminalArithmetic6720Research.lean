import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRobustFixedMeet6656Research

/-! # Arithmetic reindexing for a terminal residual stage -/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedTerminalArithmetic6720Research

open ContactRobustFixedMeet6656Research

/-- Agreements remaining after descending from degree `p.w` to degree `d`. -/
def terminalAgreements (p : Profile) (d : ℕ) : ℕ :=
  p.agreements - (p.w - d)

/-- All truncated-subtraction identities used to reindex the two global
incidence inequalities at a terminal degree.  Keeping the Presburger step in
this small opaque lemma prevents it from being repeatedly elaborated inside
the dependent outer-fiber proof. -/
theorem terminal_arithmetic_identities
    (p : Profile) (d nodes k : ℕ)
    (hd : d ≤ p.w)
    (hnodes : nodes = p.n - (p.w - d))
    (hwa : p.w < p.agreements)
    (hk : k ≤ d) :
    let total := (p.w - d) + k
    total ≤ p.w ∧
      d < terminalAgreements p d ∧
      terminalAgreements p d - d = p.gap ∧
      p.n - total = nodes - k ∧
      p.w - total = d - k ∧
      p.agreements - total = terminalAgreements p d - k := by
  dsimp only [terminalAgreements, Profile.gap]
  omega

/-- The degree and unit incidence hypotheses after reindexing from the global
degree `p.w` to a terminal descendant of degree `d`. -/
structure TerminalReindexedBounds (p : Profile) (d nodes : ℕ) : Prop where
  degree_lt_agreements : d < terminalAgreements p d
  gap_eq : terminalAgreements p d - d = p.gap
  degree : ∀ k ≤ d,
    (nodes - k) * (terminalAgreements p d - d) * (d - k) ≤
      p.degreeIncidence * (terminalAgreements p d - k)
  unit : ∀ k ≤ d,
    (nodes - k) * (terminalAgreements p d - d) ≤
      p.unitIncidence * (terminalAgreements p d - k)

theorem terminal_reindexed_bounds
    (p : Profile) (d nodes : ℕ)
    (hd : d ≤ p.w)
    (hnodes : nodes = p.n - (p.w - d))
    (hwa : p.w < p.agreements)
    (hdegreeGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap * (p.w - k) ≤
        p.degreeIncidence * (p.agreements - k))
    (hunitGlobal : ∀ k ≤ p.w,
      (p.n - k) * p.gap ≤ p.unitIncidence * (p.agreements - k)) :
    TerminalReindexedBounds p d nodes := by
  have hzero := terminal_arithmetic_identities p d nodes 0 hd hnodes hwa
    (Nat.zero_le d)
  refine ⟨hzero.2.1, hzero.2.2.1, ?_, ?_⟩
  · intro k hk
    let total := (p.w - d) + k
    have ha := terminal_arithmetic_identities p d nodes k hd hnodes hwa hk
    have h := hdegreeGlobal total ha.1
    rw [ha.2.2.1]
    simpa only [total, ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2] using h
  · intro k hk
    let total := (p.w - d) + k
    have ha := terminal_arithmetic_identities p d nodes k hd hnodes hwa hk
    have h := hunitGlobal total ha.1
    rw [ha.2.2.1]
    simpa only [total, ha.2.2.2.1, ha.2.2.2.2.2] using h

end ProximityPrize.SubmissionLower.ContactMovingReducedTerminalArithmetic6720Research
