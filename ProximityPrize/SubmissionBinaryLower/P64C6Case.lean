import ProximityPrize.SubmissionBinaryLower.P64C6Exceptional

/-!
# Positive-bias bound for an outer-separable factor

Missing agreement positions cost `n*d`, derivative-zero curves cost `2h*d`,
and the remaining curves cost `16n*d`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Case

open Polynomial P64Found P64LineOrder P64Incidence P64Cofactor P64C6Coordinates
  P64C6Geometry P64C6Incidence P64C6Exceptional BCHKSSubstitutionVanish

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

theorem separable_card_le (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (hsep : Polynomial.derivative R ≠ 0) (D w q d n N β : ℕ) (hq : 0 < q)
    (hRw : P64Caps.Weighted.weightedSupportDegree R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (hn : Fintype.card ι ≤ n) (hnlarge : 625 ≤ n) (hN : 0 < N) (hNcap : N ≤ 500000)
    (hβ : 1000 * R.natDegree ≤ β)
    (hF : 2 * R.natDegree * w < Fintype.card F)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q)
    (hβeq : (∑ i, lineOrd R (ω i) (y i)) + β = R.natDegree * (D + N))
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ S, D + N ≤ (A z).card)
    (hmatch : ∀ z ∈ S, ∀ i ∈ A z, (P z).eval (ω i) = (y i).eval z)
    (hsupport : ∀ z ∈ S, w < ∑ i ∈ A z, lineOrd R (ω i) (y i)) :
    S.card ≤ 17 * n * d + 2 * R.natDegree * d := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hS
    let good := S.filter fun z => A z ⊆ lam ω y R ∧ derivativeAlong R (P z) z ≠ 0
    let missing := S.filter fun z => ¬ A z ⊆ lam ω y R
    let dead := S.filter fun z => derivativeAlong R (P z) z = 0
    have hwlow : R.natDegree * D ≤ w := by
      have h := natDegree_mul_le_weightedSupportDegree R hirr.ne_zero D
      nlinarith
    have hβlt := beta_lt (fun i => lineOrd R (ω i) (y i)) (A z₀) R.natDegree D N w β
      hwlow (hsupport z₀ hz₀) hβeq
    have hβN : β ≤ 4 * R.natDegree * N := by nlinarith
    have hμgood : ∀ z ∈ good, ∀ i ∈ A z, 1 ≤ lineOrd R (ω i) (y i) := by
      intro z hz i hi
      have hline := (Finset.mem_filter.mp hz).2.1 hi
      have hp := (Finset.mem_filter.mp hline).2
      omega
    have hgood : good.card ≤ 16 * n * d := by
      apply P64C6Retained.card_le R hirr hh D w q d n N β hq hRw hRyz hn hnlarge hN hNcap
        hβ hβN ω y hy good P A (fun z => (A z).card - (D + N))
        (fun z hz => hP z (Finset.mem_filter.mp hz).1)
        (fun z hz => hcurve z (Finset.mem_filter.mp hz).1)
        (fun _ hz => (Finset.mem_filter.mp hz).2.2) hμgood
        (fun z hz => hmatch z (Finset.mem_filter.mp hz).1)
      · intro z hz
        exact normal_le_excess (fun i => lineOrd R (ω i) (y i)) (A z) w D N
          (hμgood z hz) (hcard z (Finset.mem_filter.mp hz).1)
          (hsupport z (Finset.mem_filter.mp hz).1)
      · intro z hz
        exact bias_leading (fun i => lineOrd R (ω i) (y i)) (A z) R.natDegree D N β
          (hcard z (Finset.mem_filter.mp hz).1) hβeq
    have hmissing : missing.card ≤ n * d :=
      card_missing_le R hirr.ne_zero q d n hRyz hn ω y hy S P A hcurve hmatch
    have hdead : dead.card ≤ 2 * R.natDegree * d :=
      card_derivative_zero_le R hirr (by omega) hsep D w q d hRw hRyz hF S P hcurve
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
      _ ≤ 16 * n * d + n * d + 2 * R.natDegree * d :=
        Nat.add_le_add (Nat.add_le_add hgood hmissing) hdead
      _ = _ := by ring
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [he]

end P64C6Case
end ProximityPrize.SubmissionBinaryLower
