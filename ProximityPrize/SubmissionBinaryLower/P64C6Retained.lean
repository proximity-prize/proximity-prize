import ProximityPrize.SubmissionBinaryLower.P64C6Uniform

/-!
# Retained curves in the positive-bias class

This statement allows arbitrary polynomial lines of parameter degree at most
`q`. The excess-agreement variable accounts for the Frobenius-twisted case.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Retained

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Bessel P64C6Uniform
  BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F] [Fintype ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

lemma outer_weight_le (R : Tri) (hR : R ≠ 0) (q d : ℕ) (hw : WtLE 0 q 1 d R) :
    q * R.natDegree ≤ d := by
  have hb : R.coeff R.natDegree ≠ 0 := by simpa using Polynomial.leadingCoeff_ne_zero.mpr hR
  obtain ⟨a, ha⟩ := Polynomial.nonempty_support_iff.mpr hb
  obtain ⟨l, hl⟩ := Polynomial.nonempty_support_iff.mpr (Polynomial.mem_support_iff.mp ha)
  have h := hw a R.natDegree l (Polynomial.mem_support_iff.mp hl)
  omega

theorem card_le (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (D w q d n N β : ℕ) (hq : 0 < q) (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (hlines : Fintype.card ι ≤ n) (hn : 625 ≤ n) (hN : 0 < N) (hNcap : N ≤ 500000)
    (hβ : 1000 * R.natDegree ≤ β) (hβN : β ≤ 4 * R.natDegree * N)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (excess : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ i ∈ A z, 1 ≤ lineOrd R (ω i) (y i))
    (hmatch : ∀ z ∈ S, ∀ i ∈ A z, (P z).eval (ω i) = (y i).eval z)
    (hdefect : ∀ z ∈ S, normalDefect R ω y (A z) w D ≤ N + excess z)
    (hbias : ∀ z ∈ S, (β : ℤ) + 4 * R.natDegree * excess z ≤
      bias (fun _ => 4 * R.natDegree) (A z) (4 * (∑ i, lineOrd R (ω i) (y i)) + β)) :
    S.card ≤ 16 * n * d := by
  classical
  let h := R.natDegree
  let μ : ι → ℕ := fun i => lineOrd R (ω i) (y i)
  let Q := ∑ i, (d - q * μ i)
  let U := 4 * (∑ i, μ i) + β
  let E := parameter h q Q β
  have hqh : q * h ≤ d := outer_weight_le R hirr.ne_zero q d hRyz
  have hqd : ∀ i, q * μ i ≤ d := fun i =>
    (Nat.mul_le_mul_left q (lineOrd_le_natDegree_of_irreducible hirr hh (ω i) (y i))).trans hqh
  have hQ : (Q : ℤ) = ∑ i, ((d : ℤ) - q * μ i) := by
    dsimp only [Q]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (hqd i), Nat.cast_mul]
  have hQle : Q ≤ n * d := by
    calc Q ≤ ∑ _ : ι, d := Finset.sum_le_sum fun i _ => Nat.sub_le _ _
      _ = Fintype.card ι * d := by simp
      _ ≤ n * d := Nat.mul_le_mul_right d hlines
  have hβpos : 0 < β := by dsimp [h] at *; omega
  have hU : 0 < U := by dsimp [U]; omega
  have hb : ∀ z ∈ S, 0 < bias (fun _ => 4 * h) (A z) U := by
    intro z hz
    have hb0 := hbias z hz
    have hx : (0 : ℤ) ≤ 4 * R.natDegree * excess z := by positivity
    have hβ0 : (0 : ℤ) < β := by exact_mod_cast hβpos
    change 0 < bias (fun _ => 4 * R.natDegree) (A z) U
    dsimp [U, μ]
    linarith
  have hslope : ∀ z ∈ S, 2 * (β : ℤ) * normalDefect R ω y (A z) w D ≤
      (2 * N : ℕ) * bias (fun _ => 4 * h) (A z) U := by
    intro z hz
    have hn0 := hdefect z hz
    have hb0 := hbias z hz
    have hβN' : (β : ℤ) ≤ 4 * R.natDegree * N := by exact_mod_cast hβN
    have h1 := mul_le_mul_of_nonneg_left hn0 (show 0 ≤ 2 * (β : ℤ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hβN' (Nat.cast_nonneg (excess z))
    have h3 := mul_le_mul_of_nonneg_left hb0 (show 0 ≤ 2 * (N : ℤ) by positivity)
    dsimp [h, U, μ]
    push_cast
    nlinarith
  have hc := weighted_orders_le R hirr D w q d U E (2 * N) hRw hRyz ω y hy
    (fun _ => 4 * h) hU (parameter_pos h q Q β) (by positivity)
    (fun _ => parameter_weight h q Q β)
    (leading_positive h q d Q β μ (by dsimp [h]; omega) hβpos hQ)
    S P A (fun _ => β) hP hcurve hderiv hμ hmatch hb hslope
  have hc' : S.card * β ≤ h * (2 * N) * E := by simpa using hc
  have hd : 1 ≤ d := by
    have hp : 0 < q * h := Nat.mul_pos hq (by dsimp [h]; omega)
    omega
  exact retained_numerical h q d Q β n N S.card (by dsimp [h]; omega) hβ hd hqh
    hQle hn hNcap hc'

end P64C6Retained
end ProximityPrize.SubmissionBinaryLower
