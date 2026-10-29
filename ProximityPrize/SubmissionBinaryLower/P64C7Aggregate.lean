import ProximityPrize.SubmissionBinaryLower.P64C7SingleLine

/-!
# Summing the single-line estimates

The mass is the sum of squared deviations of line orders from agreement.
Matched and missing curves partition each single-line contribution.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Aggregate

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Bessel
  P64C7SingleLine BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F] [Fintype ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

noncomputable def mass (h : ℕ) (μ : ι → ℕ) (A : Finset ι) : ℕ := by
  classical
  exact ∑ i, if i ∈ A then (h - μ i) ^ 2 else μ i ^ 2

theorem weighted_mass_le (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (D w q d C : ℕ) (hd : 1 ≤ d) (hqh : q * R.natDegree ≤ d) (hC : 0 < C)
    (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ j, (y j).natDegree ≤ q)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (τ : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ j ∈ A z, 1 ≤ lineOrd R (ω j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j, j ∈ A z ↔ (P z).eval (ω j) = (y j).eval z)
    (hτ : ∀ z ∈ S, 2 * (τ z : ℤ) * normalDefect R ω y (A z) w D ≤ C) :
    ∑ z ∈ S, τ z * mass R.natDegree (fun i => lineOrd R (ω i) (y i)) (A z) ≤
      10 * C * R.natDegree ^ 2 * Fintype.card ι * d := by
  classical
  let μ : ι → ℕ := fun i => lineOrd R (ω i) (y i)
  have hline : ∀ i, (∑ z ∈ S, τ z *
      (if i ∈ A z then (R.natDegree - μ i) ^ 2 else μ i ^ 2)) ≤
        10 * C * R.natDegree ^ 2 * d := by
    intro i
    let Sm := S.filter fun z => i ∈ A z
    let Su := S.filter fun z => i ∉ A z
    have hm := matched_bound R hirr hh D w q d C hd hqh hC hRw hRyz ω y hy i
      Sm P A τ (fun z hz => hP z (Finset.mem_filter.mp hz).1)
      (fun z hz => hcurve z (Finset.mem_filter.mp hz).1)
      (fun z hz => hderiv z (Finset.mem_filter.mp hz).1)
      (fun z hz => hμ z (Finset.mem_filter.mp hz).1)
      (fun z hz j hj => (hmatch z (Finset.mem_filter.mp hz).1 j).mp hj)
      (fun _ hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hτ z (Finset.mem_filter.mp hz).1)
    have hu := missing_bound R hirr hh D w q d C hd hqh hC hRw hRyz ω y i (hy i)
      Su P A τ (fun z hz => hP z (Finset.mem_filter.mp hz).1)
      (fun z hz => hcurve z (Finset.mem_filter.mp hz).1)
      (fun z hz => hderiv z (Finset.mem_filter.mp hz).1)
      (fun z hz => hμ z (Finset.mem_filter.mp hz).1)
      (fun z hz j hj => (hmatch z (Finset.mem_filter.mp hz).1 j).mp hj)
      (fun z hz he => (Finset.mem_filter.mp hz).2 ((hmatch z (Finset.mem_filter.mp hz).1 i).mpr he))
      (fun z hz => hτ z (Finset.mem_filter.mp hz).1)
    have he : (∑ z ∈ S, τ z * (if i ∈ A z then (R.natDegree - μ i) ^ 2 else μ i ^ 2)) =
        (∑ z ∈ Sm, τ z * (R.natDegree - μ i) ^ 2) + (∑ z ∈ Su, τ z * μ i ^ 2) := by
      simp only [Sm, Su, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> simp_all
    rw [he]
    dsimp only [μ]
    nlinarith only [hm, hu]
  simp only [mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _ : ι, 10 * C * R.natDegree ^ 2 * d := Finset.sum_le_sum (fun i _ => hline i)
    _ = _ := by simp; ring

/-- A matched nonfull line makes the normal defect strictly positive. -/
theorem positive_defect (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (D w q d : ℕ) (hd : 1 ≤ d) (hqh : q * R.natDegree ≤ d)
    (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ j, (y j).natDegree ≤ q)
    (z : F) (P : F[X]) (A : Finset ι) (hP : P.natDegree ≤ D)
    (hcurve : triEval R z P = 0) (hderiv : derivativeAlong R P z ≠ 0)
    (hμ : ∀ j ∈ A, 1 ≤ lineOrd R (ω j) (y j))
    (hmatch : ∀ j ∈ A, P.eval (ω j) = (y j).eval z)
    (i : ι) (hi : i ∈ A) (hnotfull : lineOrd R (ω i) (y i) < R.natDegree) :
    0 < normalDefect R ω y A w D := by
  classical
  by_contra hn
  have hn' : normalDefect R ω y A w D ≤ 0 := le_of_not_gt hn
  let M := 5 * R.natDegree ^ 2 * d + 1
  have hc := matched_bound R hirr hh D w q d 1 hd hqh (by norm_num) hRw hRyz ω y hy i
    ({z} : Finset F) (fun _ => P) (fun _ => A) (fun _ => M)
    (fun _ _ => hP) (fun v hv => by simpa [Finset.mem_singleton.mp hv] using hcurve)
    (fun v hv => by simpa [Finset.mem_singleton.mp hv] using hderiv) (fun _ _ => hμ)
    (fun v hv => by simpa [Finset.mem_singleton.mp hv] using hmatch)
    (fun _ _ => hi) (fun _ _ => ?_)
  · simp only [Finset.sum_singleton, mul_one] at hc
    have ht : 1 ≤ (R.natDegree - lineOrd R (ω i) (y i)) ^ 2 := by
      have hs := Nat.sub_pos_of_lt hnotfull
      nlinarith
    have hm := Nat.mul_le_mul_left M ht
    dsimp [M] at hc hm
    nlinarith
  · have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * (M : ℤ) by positivity) hn'
    omega

end P64C7Aggregate
end ProximityPrize.SubmissionBinaryLower
