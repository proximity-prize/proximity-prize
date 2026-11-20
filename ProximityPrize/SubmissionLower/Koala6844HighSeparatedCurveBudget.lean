import ProximityPrize.SubmissionLower.Koala6844HighSeparatedFactor
import ProximityPrize.SubmissionLower.Koala6844HighSeparatedPersistentCurves
import ProximityPrize.SubmissionLower.Koala6831IntrinsicWeightedLiteral


namespace ProximityPrize.SubmissionLower.Koala6844HighSeparated

open Koala6831Intrinsic Koala6831OrdinaryIncidence
open RCN007 RCN135 RCN136 RCN234 RCN264 RCN341
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4400000

variable {K I : Type} [Field K] [CharP K 2130706433]

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K

theorem long_factor_seed_count
    (F : Carrier K) (hp : Nat.Prime 2130706433) (hF : Irreducible F)
    (hweight : wt ![1, 131071, 0, 0] F < 4000000)
    (hY : wt ![0, 1, 0, 0] F ≤ 22)
    (hT : wt ![0, 1, 1, 0] F ≤ 200)
    (hZ : wt ![0, 0, 0, 1] F ≤ 162)
    (G : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (x : I ↪ K) (u₀ u₁ : I → K) (nodes : Finset I)
    (hAn : 180958 ≤ nodes.card) (haverage : nodeAverage nodes.card 131071 180958 ≤ 3)
    (seeds allSeeds : Finset K) (hsub : seeds ⊆ allSeeds)
    (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ 2130706433) F = 0)
    (hreg : ∀ g ∈ seeds,
      graphSpecialize (selected g) g (g ^ 2130706433) (implicitRegularity F) ≠ 0)
    (hzero : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint 2130706433 selected g) G = 0)
    (hagreements : ∀ g ∈ seeds, 180958 ≤
      (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ 131071 → P₁.natDegree ≤ 131071 →
      (RCN050.pencilSeeds allSeeds selected P₀ P₁).card ≤ 81187) :
    seeds.card ≤ longFactorCharge (G.degreeOf 0) (longMiddleDegree G) (G.degreeOf 2) := by
  classical
  apply long_factor_seed_count_of_persistent_allowance F hp hF hweight hY hT hZ G hG hdiv
    x u₀ u₁ nodes hAn haverage seeds allSeeds hsub selected hdegree hroot hreg hzero hagreements hpencil
  intro proper
  let A := {C : FirstTailComponent F 131071 G // Persistent F 131071 C.1}
  let component (a : A) := a.1
  let charts (a : A) := curveChartData_of_regularComponent F 131071 hF hdiv proper (component a)
  let y := G.degreeOf 0
  let t := longMiddleDegree G
  let z := G.degreeOf 2
  obtain ⟨hy, ht, hz, hyt, htSupport⟩ := long_geometric_factor_caps F hF.ne_zero G hdiv hY hT hZ
  obtain ⟨tailY, tailT, tailZ⟩ := long_first_tail_caps F hY hT hZ
  have caps : LongLiteralSeedCaps G (surfaceMap φ (tailNumerator F 131071)) :=
    ⟨hy, tailY, hz, tailZ, fun d hd => (htSupport d hd).trans ht, tailT⟩
  choose base _ using fun a : A =>
    exists_long_literal_seed_projection F 131071 hdiv hG proper caps (component a)
  let d₀ (a : A) := actualCoordinateDegree Ω (component a).1 1
  let d₁ (a : A) := actualCoordinateDegree Ω (component a).1 2
  have hcount :=
    long_persistent_selected_sum_le_of_degree F G 4000000 81186 (by decide) (by decide)
      (by decide) hweight hT hZ component charts base (fun a => a.2) d₀ d₁
      (fun a => long_literal_seed_degrees_pos F G hdiv hG proper caps (component a))
      (fun a W => by
        simpa only [show longSeedOrder false 0 = 1 by decide] using
          long_literal_pole_le_actual_degree F G hdiv hG proper caps (component a) false W)
      (fun a W => by
        simpa only [show longSeedOrder true 0 = 2 by decide] using
          long_literal_pole_le_actual_degree F G hdiv hG proper caps (component a) true W)
      x u₀ u₁ nodes hAn haverage seeds allSeeds hsub selected hdegree hroot hreg hagreements hpencil
  have weightedZero := intrinsic_literal_weighted_degree_bound F 131071 hp
    hdiv hG proper caps component Subtype.val_injective charts false y t z hyt le_rfl htSupport le_rfl
  have weightedOne := intrinsic_literal_weighted_degree_bound F 131071 hp
    hdiv hG proper caps component Subtype.val_injective charts true y t z hyt le_rfl htSupport le_rfl
  have positive (a : A) : 1 ≤ curveTailOrder F 131071 (component a).1 (charts a) :=
    (curve_intrinsic_tail_dichotomy F 131071 2130706433 hp (component a).1 (charts a)).1
  have leWeighted (f : A → ℕ) :
      (∑ a, f a) ≤ ∑ a, curveTailOrder F 131071 (component a).1 (charts a) * f a := by
    apply Finset.sum_le_sum
    intro a _
    simpa only [one_mul] using Nat.mul_le_mul_right (f a) (positive a)
  have h₀ : (∑ a, d₀ a) ≤ 5505004 * z + y * 42467166 := (leWeighted d₀).trans (by
    simpa only [show longSeedOrder false 0 = 1 by decide, Bool.false_eq_true, ite_false, d₀] using weightedZero)
  have h₁ : (∑ a, d₁ a) ≤ 5505004 * (t - y) + y * 52166458 := by
    apply (leWeighted d₁).trans
    have h := (show (∑ a, curveTailOrder F 131071 (component a).1 (charts a) * d₁ a) ≤
        5505004 * t + y * 52166458 - 5505004 * y from by
      simpa only [show longSeedOrder true 0 = 2 by decide, ite_true, d₁] using weightedOne)
    rw [Nat.mul_sub]
    omega
  exact hcount.trans (Nat.mul_le_mul_left _ (Nat.add_le_add h₀ h₁))

end

end ProximityPrize.SubmissionLower.Koala6844HighSeparated
