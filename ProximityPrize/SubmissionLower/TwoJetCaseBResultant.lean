import ProximityPrize.SubmissionLower.CJ0High133721Main
import ProximityPrize.SubmissionLower.TwoJetRescueBridge

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

/-!
# Case-B Sylvester Resultant Box & 6-Small-Rect Consumer (`TwoJetCaseBResultant`)

Connects L4 `TwoJetRescueBridge.caseB_cj0_box_exact` directly to L4
`CJ0High133721Main.caseB_six_rects_card_le_6963`:

1. `sylvester_weightedTotalDegree_le`: for any weight function `w : JetVariable 2 → ℕ` and any
   polynomials `G G₁ : Polynomial (DifferentialPolynomial K 2)` whose coefficients have
   `w`-weighted degree `≤ B` and `≤ D`, their Sylvester resultant `G.resultant G₁ m n` has
   `w`-weighted degree `≤ n * B + m * D`.
2. `resultant_orderTwoHigh`: if `G` (the 1-jet prime) has `(Y₀, Y₁, Y₂)`-degree `≤ j`,
   `indexWeight ≤ 1`, `Y₂`-degree `= 0`, and `G₁` (its prolongation `G^(1)`) has total degree
   `≤ j + 1`, `indexWeight ≤ 2`, `Y₂`-degree `≤ 1`, with `m, n ≤ u`, then any nonzero
   `Q = G.resultant G₁ m n` satisfies `OrderTwoHigh box Q` whenever
   `(2 * j + 1) * u ≤ box.B`, `3 * u ≤ box.J`, `u ≤ box.C`.
3. `resultant_vanishes_on_common_root`: if `G` and `G₁` share a root `z₀` after specializing at `f`,
   then `differentialSpecialization (G.resultant G₁ m n) f = 0`.
4. `caseB_small_rects_card_le_6963`: end-to-end cardinality cap (`≤ 44.89e15`, plus exact per-rect
   caps) for any Case-B pair `(G, G₁)` in any of the 6 small Rescue rectangles at `69.63`
   (`A = 179,798`, `deg < 133,721`).
-/

namespace TwoJetCaseBResultant

noncomputable section

open CJ0 CJ0High133721 TwoJetRescueBridge Polynomial PolynomialDifferential MvPolynomial
open scoped BigOperators

/-- General weighted-degree bound on a Sylvester resultant over `DifferentialPolynomial K 2`. -/
theorem sylvester_weightedTotalDegree_le (w : JetVariable 2 → ℕ)
    (G G₁ : Polynomial (DifferentialPolynomial K 2)) (m n B D : ℕ)
    (hG : ∀ i ≤ m, (G.coeff i).weightedTotalDegree w ≤ B)
    (hG₁ : ∀ i ≤ n, (G₁.coeff i).weightedTotalDegree w ≤ D) :
    (G.resultant G₁ m n).weightedTotalDegree w ≤ n * B + m * D := by
  classical
  let M := Polynomial.sylvester G G₁ m n
  let W : Fin (m + n) → ℕ :=
    Fin.addCases (fun _ : Fin m => D) (fun _ : Fin n => B)
  have hentry (σ : Equiv.Perm (Fin (m + n))) (i : Fin (m + n))
      (hne : M (σ i) i ≠ 0) :
      (M (σ i) i).weightedTotalDegree w ≤ W i := by
    cases i using Fin.addCases with
    | left j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, W] at hne ⊢
      split_ifs at hne ⊢ with h
      · exact hG₁ ((σ (j.castAdd n)).val - j.val) (by have := h.2; omega)
      · exact absurd rfl hne
    | right j =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, W] at hne ⊢
      split_ifs at hne ⊢ with h
      · exact hG ((σ (j.natAdd m)).val - j.val) (by have := h.2; omega)
      · exact absurd rfl hne
  have hW : ∑ i, W i = n * B + m * D := by
    simp only [W, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hterm (σ : Equiv.Perm (Fin (m + n))) :
      (∏ i, M (σ i) i).weightedTotalDegree w ≤ n * B + m * D := by
    by_cases hz : ∃ i, M (σ i) i = 0
    · obtain ⟨i, hi⟩ := hz
      have hp : (∏ k, M (σ k) k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hp, weightedTotalDegree_zero]
      exact Nat.zero_le _
    · simp only [not_exists] at hz
      rw [weightedTotalDegree_prod _ _ _ (fun i _ => hz i)]
      exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hentry σ i (hz i))).trans_eq hW
  change M.det.weightedTotalDegree w ≤ n * B + m * D
  rw [Matrix.det_apply]
  refine AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun σ _ => ?_)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact hterm σ
  · rw [hs, Units.neg_smul, one_smul]
    let P : DifferentialPolynomial K 2 := ∏ i, M (σ i) i
    change (-P).weightedTotalDegree w ≤ n * B + m * D
    have hsup : (-P).weightedTotalDegree w = P.weightedTotalDegree w := by
      simp only [MvPolynomial.weightedTotalDegree, MvPolynomial.support_neg]
    rw [hsup]
    exact hterm σ

/-- Exact `OrderTwoHigh` box certificate for the Sylvester resultant `Res_z(G, G₁)` of a 1-jet
    prime `G` and its prolongation `G₁ = G^(1)`. -/
theorem resultant_orderTwoHigh {j u m n : ℕ} {box : BoxShape}
    (G G₁ : Polynomial (DifferentialPolynomial K 2))
    (hm : m ≤ u) (hn : n ≤ u)
    (hne : G.resultant G₁ m n ≠ 0)
    (hG_tot : ∀ i ≤ m, jetTotalDegree (G.coeff i) ≤ j)
    (hG_idx : ∀ i ≤ m, (G.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 1)
    (hG_top : ∀ i ≤ m, jetDegree (G.coeff i) (Fin.last 2) = 0)
    (hG₁_tot : ∀ i ≤ n, jetTotalDegree (G₁.coeff i) ≤ j + 1)
    (hG₁_idx : ∀ i ≤ n, (G₁.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 2)
    (hG₁_top : ∀ i ≤ n, jetDegree (G₁.coeff i) (Fin.last 2) ≤ 1)
    (hB : (2 * j + 1) * u ≤ box.B) (hJ : 3 * u ≤ box.J) (hC : u ≤ box.C) :
    OrderTwoHigh box (G.resultant G₁ m n) := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · change jetTotalDegree (G.resultant G₁ m n) ≤ box.B
    have h := sylvester_weightedTotalDegree_le jetDegreeWeight G G₁ m n j (j + 1) hG_tot hG₁_tot
    have hmul : n * j + m * (j + 1) ≤ (2 * j + 1) * u := by
      have h1 : n * j ≤ u * j := Nat.mul_le_mul_right j hn
      have h2 : m * (j + 1) ≤ u * (j + 1) := Nat.mul_le_mul_right (j + 1) hm
      have h3 : u * j + u * (j + 1) = (2 * j + 1) * u := by ring
      omega
    exact h.trans (hmul.trans hB)
  · change (G.resultant G₁ m n).weightedTotalDegree CJ0.indexWeight ≤ box.J
    have h := sylvester_weightedTotalDegree_le CJ0.indexWeight G G₁ m n 1 2 hG_idx hG₁_idx
    have hmul : n * 1 + m * 2 ≤ 3 * u := by omega
    exact h.trans (hmul.trans hJ)
  · change jetDegree (G.resultant G₁ m n) (Fin.last 2) ≤ box.C
    let wtop : JetVariable 2 → ℕ := Pi.single (some (Fin.last 2)) 1
    have h := sylvester_weightedTotalDegree_le wtop G G₁ m n 0 1
      (fun i hi => by
        simpa only [wtop, weightedTotalDegree_piSingle, jetDegree] using (hG_top i hi).le)
      (fun i hi => by
        simpa only [wtop, weightedTotalDegree_piSingle, jetDegree] using hG₁_top i hi)
    simp only [wtop, weightedTotalDegree_piSingle, mul_zero, zero_add, mul_one] at h
    exact h.trans (hm.trans hC)

/-- Common root vanishing: if `G` and `G₁` share a seed root `z₀` after specializing at `f`, then
    their Sylvester resultant annihilates `f`. -/
theorem resultant_vanishes_on_common_root
    (G G₁ : Polynomial (DifferentialPolynomial K 2)) (m n : ℕ)
    (hGm : G.natDegree ≤ m) (hG₁n : G₁.natDegree ≤ n) (hsize : m ≠ 0 ∨ n ≠ 0)
    (f z₀ : Polynomial K)
    (hG0 : G.eval₂ (differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0)
    (hG₁0 : G₁.eval₂ (differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0) :
    differentialSpecialization (G.resultant G₁ m n) f = 0 :=
  Sol1.C40Primitives.map_resultant_eq_zero_of_common_root
    (differentialSpecializationHom (d := 2) f).toRingHom G G₁ m n hGm hG₁n hsize z₀ hG0 hG₁0

/-- Exact per-rectangle Case-B budget cap at `69.63` (`A = 179,798`) for the 6 small rectangles. -/
def smallRectCap6963 : RescueRect → ℕ
  | .r0     => 2_000_000_000_000
  | .r1     => 640_000_000_000_000
  | .r2a    => 44_890_000_000_000_000
  | .r3a_j2 => 36_860_000_000_000_000
  | .r3a_j4 => 7_870_000_000_000_000
  | .r3a_j7 => 9_380_000_000_000_000
  | _       => 0

def IsSmallRect : RescueRect → Prop
  | .r0 | .r1 | .r2a | .r3a_j2 | .r3a_j4 | .r3a_j7 => True
  | _ => False

theorem smallRectCap6963_le_max (r : RescueRect) :
    smallRectCap6963 r ≤ 44_890_000_000_000_000 := by
  cases r <;> decide

/-- **End-to-End Case-B Small-Rectangle Rescue Theorem at `69.63` (`A = 179,798`, `deg < 133,721`)**:
    For ANY of the 6 small Rescue rectangles `r ∈ {.r0, .r1, .r2a, .r3a_j2, .r3a_j4, .r3a_j7}` and
    any Case-B pair `(G, G₁)` with `InRect j u r` and nonzero Sylvester resultant
    `G.resultant G₁ m n ≠ 0` (`m, n ≤ u`, `m ≠ 0 ∨ n ≠ 0`), any finite set `T ⊆ closeHigh 179798 w`
    of degree-`< 133,721` polynomials whose marks all admit a common `z₀` root of `(G, G₁)` obeys:
    1. `T.card ≤ smallRectCap6963 r` (exact per-rectangle cap), and
    2. `T.card ≤ 44_890_000_000_000_000` (`44.89e15 < 61.30e15` 4-large-rect Rescue cap). -/
theorem caseB_small_rects_card_le_6963
    {r : RescueRect} (hr : IsSmallRect r) {j u m n : ℕ} (hin : InRect j u r)
    (G G₁ : Polynomial (DifferentialPolynomial K 2))
    (hm : m ≤ u) (hn : n ≤ u) (hGm : G.natDegree ≤ m) (hG₁n : G₁.natDegree ≤ n)
    (hsize : m ≠ 0 ∨ n ≠ 0) (hne : G.resultant G₁ m n ≠ 0)
    (hG_tot : ∀ i ≤ m, jetTotalDegree (G.coeff i) ≤ j)
    (hG_idx : ∀ i ≤ m, (G.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 1)
    (hG_top : ∀ i ≤ m, jetDegree (G.coeff i) (Fin.last 2) = 0)
    (hG₁_tot : ∀ i ≤ n, jetTotalDegree (G₁.coeff i) ≤ j + 1)
    (hG₁_idx : ∀ i ≤ n, (G₁.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 2)
    (hG₁_top : ∀ i ≤ n, jetDegree (G₁.coeff i) (Fin.last 2) ≤ 1)
    (w : Node → K) (T : Finset (Polynomial K))
    (hT : (T : Set (Polynomial K)) ⊆ closeHigh 179798 w)
    (hcommon : ∀ f ∈ T, ∃ z₀ : Polynomial K,
      G.eval₂ (differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0 ∧
      G₁.eval₂ (differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0) :
    T.card ≤ smallRectCap6963 r ∧ T.card ≤ 44_890_000_000_000_000 := by
  have hroots : ∀ f ∈ T, differentialSpecialization (G.resultant G₁ m n) f = 0 := by
    intro f hf
    obtain ⟨z₀, hzG, hzG₁⟩ := hcommon f hf
    exact resultant_vanishes_on_common_root G G₁ m n hGm hG₁n hsize f z₀ hzG hzG₁
  obtain ⟨h0, h1, h2a, h32, h34, h37⟩ := caseB_six_rects_card_le_6963 w T hT
  obtain ⟨b0, b1, b2a, b32, b34, b37⟩ := caseB_cj0_box_exact (j := j) (u := u)
  have hcap : T.card ≤ smallRectCap6963 r := by
    cases r with
    | r0 =>
      obtain ⟨hB, hJ, hC, _⟩ := b0 hin
      exact h0 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r1 =>
      obtain ⟨hB, hJ, hC, _⟩ := b1 hin
      exact h1 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r2a =>
      obtain ⟨hB, hJ, hC, _⟩ := b2a hin
      exact h2a _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r3a_j2 =>
      obtain ⟨hB, hJ, hC, _⟩ := b32 hin
      exact h32 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r3a_j4 =>
      obtain ⟨hB, hJ, hC, _⟩ := b34 hin
      exact h34 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r3a_j7 =>
      obtain ⟨hB, hJ, hC, _⟩ := b37 hin
      exact h37 _ (resultant_orderTwoHigh G G₁ hm hn hne hG_tot hG_idx hG_top hG₁_tot hG₁_idx
        hG₁_top hB hJ hC) hroots
    | r2b => exact hr.elim
    | r3b_j2 => exact hr.elim
    | r3b_j4 => exact hr.elim
    | r3b_j7 => exact hr.elim
  exact ⟨hcap, hcap.trans (smallRectCap6963_le_max r)⟩

end

end TwoJetCaseBResultant

#print axioms TwoJetCaseBResultant.sylvester_weightedTotalDegree_le
#print axioms TwoJetCaseBResultant.resultant_orderTwoHigh
#print axioms TwoJetCaseBResultant.resultant_vanishes_on_common_root
#print axioms TwoJetCaseBResultant.caseB_small_rects_card_le_6963
