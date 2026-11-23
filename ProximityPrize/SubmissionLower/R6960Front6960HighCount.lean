import ProximityPrize.SubmissionLower.R6960Front6960PoleChart
import ProximityPrize.SubmissionLower.R6960TerminalMarked

set_option Elab.async false
namespace Lower6960
open Polynomial
open K1 (K)
open K1_14 (Equation atMark)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open KoalaRect (axisDegree)
open RescueGeometry (Model Family)
open scoped Polynomial

abbrev retainedCap : ℕ := 30826479554094836

/-- A bound for the actual family of simple marked sheets left by the high prefix. -/
def RetainedCount : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (_lo : 2339 ≤ M.overhead.toNat) (_hi : M.overhead.toNat ≤ 33561)
    {D : PoleData M.overhead.toNat} (_Crt : CRTLift D)
    (_regular : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (_residues : ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (T : Finset K) (f : Equation), T ⊆ Γ →
      3 ≤ f.natDegree → f.natDegree < 48 → axisDegree f 0 + axisDegree f 1 ≤ 2400 →
      (∀ j : Fin 2, axisDegree f j < (TerminalReceipts.witness f.natDegree).order 1) →
      (∀ γ ∈ T, TerminalMarked.simpleSheet f (M.label γ) (F.scalar γ) ∧
        ∃ q : Equation, Irreducible q ∧ q ∣ f ∧ 3 ≤ q.natDegree ∧
          atMark q (M.label γ) (F.scalar γ) = 0) →
      T.card ≤ retainedCap

theorem high_count_of_retained (retained : RetainedCount)
    {u deleted} (M : Model u deleted) {Γ} (F : Family M Γ)
    (lo : 2339 ≤ M.overhead) (hi : M.overhead ≤ 33561) :
    Γ.card ≤ 266695718139456639 := by
  have hlo : 2339 ≤ M.overhead.toNat := by omega
  have hhi : M.overhead.toNat ≤ 33561 := by omega
  obtain ⟨D, ⟨Crt⟩, regular, residues⟩ := FrontPoleChart.of_family M F
  rcases TerminalMarked.good_remainder F Crt hlo hhi regular residues with
    paid | ⟨T, f, sub, paid, degree, small, axes, grade, marks⟩
  · exact paid.trans (by decide +kernel)
  · exact (paid.trans (Nat.add_le_add_left
      (retained F hlo hhi Crt regular residues T f sub degree small axes grade marks) _)).trans_eq
      (by decide +kernel)

#print axioms high_count_of_retained
end Lower6960
