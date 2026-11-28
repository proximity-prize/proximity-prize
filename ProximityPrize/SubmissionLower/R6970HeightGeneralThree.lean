import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore

set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Research6970.Height2313.Research6969.PairLeaves

open _root_.Research6970.Height2313.Research6969.PairRoute
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open _root_.Research6970.Height2313.Research6969.BookView (mainBook)

theorem threeWithSame {i} (b : Row) (checked : ThreeRule.check b i = true)
    (p : Decision) (pay : PairPrices.sameOK b i p)
    (small : b.off < 64) (mass : (2*b.off-1)*(mainBook i).seedMass < K1.p)
    (wh : Option ℕ) (use : ∀ fee, p.same = .node fee → wh = some p.cutoff) :
    Done i (of_row b wh) := by
  intro s h
  have data := facts h
  obtain ⟨z⟩ := NormalGeometry.geometry s
  by_cases eq : _root_.Research6969.GraphIntersection.determinant (NormalGeometry.nativeHelper s) s.native = 0
  · exact ConfirmedSame.proves s b data z p eq pay small mass (fun fee atNode => h.wh _ (use fee atNode))
  · exact ThreeRule.proves s b data checked z eq

theorem threeImpossible {i} (b : Row) (checked : ThreeRule.check b i = true)
    (impossible : PairPrices.impossible b i) (fits : b.content ≤ b.upperGrade) (wh : Option ℕ) :
    Done i (of_row b wh) := by
  have ⟨guard, _⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨small, mass, _⟩ := of_decide_eq_true guard
  have off : b.off ≤ b.upperGrade := (Nat.sub_le ..).trans fits
  exact threeWithSame b checked ⟨.surface, .whole, .impossible, 0⟩ impossible
    (off.trans_lt small)
    ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 off) 1)).trans_lt mass)
    wh (by intro fee bad; cases bad)

end Research6970.Height2313.Research6969.PairLeaves
