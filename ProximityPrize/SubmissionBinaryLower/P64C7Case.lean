import ProximityPrize.SubmissionBinaryLower.P64C7Retained
import ProximityPrize.SubmissionBinaryLower.P64C6Exceptional

/-!
# Class 7 for a factor separable in the outer variable

Discarding zero-order agreement positions and derivative-zero curves leaves
exactly the hypotheses of the retained-curve estimate.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Case

open Polynomial P64Found P64LineOrder P64Incidence P64C6Coordinates
  P64C6Incidence P64C6Exceptional BCHKSSubstitutionVanish

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

noncomputable def fullLines (R : Tri) (ω : ι ↪ F) (y : ι → F[X]) : Finset ι :=
  Finset.univ.filter fun i => lineOrd R (ω i) (y i) = R.natDegree

theorem separable_card_le (R : Tri) (hirr : Irreducible R) (hh : 3 ≤ R.natDegree)
    (hsep : Polynomial.derivative R ≠ 0) (w q d n : ℕ) (hq : 0 < q)
    (hRw : wd R 1048575 ≤ w) (hRyz : WtLE 0 q 1 d R)
    (hn : Fintype.card ι ≤ n) (hF : 2 * R.natDegree * w < Fintype.card F)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q)
    (hprofile : 2 * (R.natDegree : ℤ) * w - R.natDegree ^ 2 * 1048575 -
      (∑ i, (lineOrd R (ω i) (y i) : ℤ) ^ 2) ≤ 65536 * R.natDegree ^ 2)
    (hfull : (fullLines R ω y).card < 1482911)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ 1048575)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ S, 1482911 ≤ (A z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ A z ↔ (P z).eval (ω i) = (y i).eval z)
    (hsupport : ∀ z ∈ S, w < ∑ i ∈ A z, lineOrd R (ω i) (y i)) :
    S.card ≤ 41 * n * d + 2 * R.natDegree * d := by
  classical
  let good := S.filter fun z => A z ⊆ lam ω y R ∧ derivativeAlong R (P z) z ≠ 0
  let missing := S.filter fun z => ¬ A z ⊆ lam ω y R
  let dead := S.filter fun z => derivativeAlong R (P z) z = 0
  have hqh := P64C6Retained.outer_weight_le R hirr.ne_zero q d hRyz
  have hd : 1 ≤ d := by
    have hp := Nat.mul_pos hq (show 0 < R.natDegree by omega)
    omega
  have hμgood : ∀ z ∈ good, ∀ i ∈ A z, 1 ≤ lineOrd R (ω i) (y i) := by
    intro z hz i hi
    have hline := (Finset.mem_filter.mp hz).2.1 hi
    have hp := (Finset.mem_filter.mp hline).2
    omega
  have hproper : ∀ z ∈ good, ∃ i ∈ A z, lineOrd R (ω i) (y i) < R.natDegree := by
    intro z hz
    by_contra hn
    push_neg at hn
    have hsub : A z ⊆ fullLines R ω y := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, le_antisymm ?_ (hn i hi)⟩
      exact lineOrd_le_natDegree_of_irreducible hirr (by omega) (ω i) (y i)
    have hc := (Finset.card_le_card hsub).trans_lt hfull
    have ha := hcard z (Finset.mem_filter.mp hz).1
    omega
  have hgood : good.card ≤ 40 * n * d := by
    have hc := P64C7Retained.card_le R hirr hh w q d hd hqh hRw hRyz ω y hy hprofile
      good P A (fun z hz => hP z (Finset.mem_filter.mp hz).1)
      (fun z hz => hcurve z (Finset.mem_filter.mp hz).1)
      (fun _ hz => (Finset.mem_filter.mp hz).2.2) hμgood
      (fun z hz => hmatch z (Finset.mem_filter.mp hz).1) hproper
      (fun z hz => hcard z (Finset.mem_filter.mp hz).1)
      (fun z hz => hsupport z (Finset.mem_filter.mp hz).1)
    exact hc.trans (Nat.mul_le_mul_right d (Nat.mul_le_mul_left 40 hn))
  have hmissing : missing.card ≤ n * d := card_missing_le R hirr.ne_zero q d n hRyz hn ω y hy
    S P A hcurve (fun z hz i hi => (hmatch z hz i).mp hi)
  have hdead : dead.card ≤ 2 * R.natDegree * d :=
    card_derivative_zero_le R hirr (by omega) hsep 1048575 w q d hRw hRyz hF S P hcurve
  have hcover : S ⊆ good ∪ missing ∪ dead := by
    intro z hz
    by_cases ha : A z ⊆ lam ω y R
    · by_cases hd : derivativeAlong R (P z) z = 0
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hd⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hz, ha, hd⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, ha⟩))
  calc S.card ≤ (good ∪ missing ∪ dead).card := Finset.card_le_card hcover
    _ ≤ (good ∪ missing).card + dead.card := Finset.card_union_le _ _
    _ ≤ good.card + missing.card + dead.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 40 * n * d + n * d + 2 * R.natDegree * d :=
      Nat.add_le_add (Nat.add_le_add hgood hmissing) hdead
    _ = _ := by ring

end P64C7Case
end ProximityPrize.SubmissionBinaryLower
