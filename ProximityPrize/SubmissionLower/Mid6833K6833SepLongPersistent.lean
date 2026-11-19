/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from the frozen 68.32 submission of Bome2017, building on Lucieno
(PR 618) and BitWonka (PRs 581 and 582). KoalaBear 68.33 long branch, November 18. -/
/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,66 errors, right cap 167 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartPersistentIncidence
import ProximityPrize.SubmissionLower.Koala6831IntrinsicSelectedComponents
import ProximityPrize.SubmissionLower.Mid6833K6833SepLongLiteral

namespace ProximityPrize.SubmissionLower.K6833FactorCount
open Koala6831Intrinsic

open scoped Classical BigOperators Polynomial
open MvPolynomial RCN002 RCN081 RCN135 RCN136 RCN234 RCN341 RCN344
  RCN005 RCN007 RCN042 Koala6831OrdinaryIncidence

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {K I A : Type} [Field K] [CharP K 2130706433] [Fintype A]

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K
local notation "w" => 131071
local notation "p" => 2130706433

theorem long_persistent_selected_sum_le_of_degree_lp32
    (F : Carrier K) (G : MvPolynomial (Fin 3) Ω) (bound e : ℕ)
    (hw : w + 1 ≤ bound) (hchar : bound < p) (he : e ≤ 81085)
    (hweight : wt ![1, w, 0, 0] F < bound)
    (hT : wt ![0, 1, 1, 0] F ≤ 198) (hZ : wt ![0, 0, 0, 1] F ≤ 167)
    (component : A → FirstTailComponent F w G)
    (charts : ∀ i, CurveChartData F w (component i).1)
    (base : ∀ i, SeparableLiteralCoordinate (component i).1)
    (hpersistent : ∀ i j, surfaceMap φ (tailNumerator F (w + j)) ∈ (component i).1)
    (d₀ d₁ : A → ℕ) (hpos : ∀ i, 1 ≤ d₀ i + d₁ i)
    (hd₀ : ∀ i, ∀ W : Finset (Place Ω (CoordinateField Ω (component i).1)),
      (∑ v ∈ W, RCN346.poleOrder Ω (CoordinateField Ω (component i).1) v
        (coordinate Ω (component i).1 1)) ≤ (d₀ i : ℤ))
    (hd₁ : ∀ i, ∀ W : Finset (Place Ω (CoordinateField Ω (component i).1)),
      (∑ v ∈ W, RCN346.poleOrder Ω (CoordinateField Ω (component i).1) v
        (coordinate Ω (component i).1 2)) ≤ (d₁ i : ℤ))
    (x : I ↪ K) (u₀ u₁ : I → K) (nodes : Finset I)
    (hAn : 181059 ≤ nodes.card) (haverage : nodeAverage nodes.card w 181059 ≤ 3)
    (seeds allSeeds : Finset K) (hsub : seeds ⊆ allSeeds)
    (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hgraph : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ p) F = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ p) (implicitRegularity F) ≠ 0)
    (hagreements : ∀ g ∈ seeds, 181059 ≤
      (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (RCN050.pencilSeeds allSeeds selected P₀ P₁).card ≤ e + 1) :
    (∑ i, (selectedComponentPoints F w p G seeds selected (component i)).card) ≤
      81683 * ((∑ i, d₀ i) + ∑ i, d₁ i) := by
  classical
  letI : CharP Ω p := genericField_charP K p
  have hts : ∀ d ∈ F.support, d 2 ≤ 198 := by
    intro d hd
    have hl := (MvPolynomial.le_weightedTotalDegree (![0, 1, 1, 0] : Fin 4 → ℕ) hd).trans hT
    rw [weight_fin4] at hl
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 198 at hl
    simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] at hl
    omega
  have hzs : ∀ d ∈ F.support, d 3 ≤ 167 := by
    intro d hd
    have hl := (MvPolynomial.le_weightedTotalDegree (![0, 0, 0, 1] : Fin 4 → ℕ) hd).trans hZ
    rw [weight_fin4] at hl
    change d 0 * 0 + d 1 * 0 + d 2 * 0 + d 3 * 1 ≤ 167 at hl
    simpa only [Nat.mul_zero, Nat.mul_one, Nat.zero_add] using hl
  have hcount (i : A) : (selectedComponentPoints F w p G seeds selected (component i)).card ≤
      81683 * (d₀ i + d₁ i) := by
    rw [selectedComponentPoints_card]
    let fiber := selectedOnComponent F w p G seeds selected (component i)
    have hmem (g : K) (hg : g ∈ fiber) :
        g ∈ seeds ∧ (component i).1 ≤
          RingHom.ker (MvPolynomial.aeval (selectedGraphPoint p selected g)).toRingHom :=
      Finset.mem_filter.mp hg
    have hlocal :=
      persistent_curve_selected_seed_bound F w bound p 198 167 (component i).1
        (base i) (d₀ i) (d₁ i) (hd₀ i) (hd₁ i) (charts i).carrier_mem
        (charts i).separant_not_mem (hpersistent i) (by omega) hw hchar hweight hts hzs
        x u₀ u₁ nodes 181059 e (by decide) hAn haverage fiber allSeeds
        (fun g hg => hsub (hmem g hg).1) selected (fun g => g ^ p)
        (fun g hg => hdegree g (hmem g hg).1)
        (fun g hg => hgraph g (hmem g hg).1)
        (fun g hg => by
          rw [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
          exact hreg g (hmem g hg).1)
        (fun g hg => (hmem g hg).2)
        (fun g hg => hagreements g (hmem g hg).1) hpencil
    refine hlocal.trans ?_
    have hp := hpos i
    omega
  calc
    _ ≤ ∑ i, 81683 * (d₀ i + d₁ i) := Finset.sum_le_sum fun i _ => hcount i
    _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib]

theorem long_literal_pole_le_actual_degree_lp32
    (F : Carrier K) (G : MvPolynomial (Fin 3) Ω) (hdiv : G ∣ surfaceMap φ F)
    (hG : Irreducible G) (hproper : ¬ G ∣ surfaceMap φ (tailNumerator F w))
    (caps : LongLiteralSeedCaps_lp32 G (surfaceMap φ (tailNumerator F w)))
    (C : FirstTailComponent F w G) (useZ₁ : Bool)
    (W : Finset (Place Ω (CoordinateField Ω C.1))) :
    let idx := longSeedOrder_lp32 useZ₁ 0
    (∑ v ∈ W, RCN346.poleOrder Ω (CoordinateField Ω C.1) v (coordinate Ω C.1 idx)) ≤
      (actualCoordinateDegree Ω C.1 idx : ℤ) := by
  classical
  letI : CharP Ω p := genericField_charP K p
  let idx := longSeedOrder_lp32 useZ₁ 0
  let E := CoordinateField Ω C.1
  let s := coordinate Ω C.1 idx
  have hgate (hs : Transcendental Ω s) :=
    long_literal_projection_gate_lp32 F w hdiv hG hproper caps C useZ₁ hs
  have hd : coordinateDegree Ω E (coordinateOfGate s hgate) = actualCoordinateDegree Ω C.1 idx := by
    by_cases h : Transcendental Ω s
    · rw [coordinateOfGate_degree_of_transcendental s hgate h,
        actualCoordinateDegree_of_transcendental Ω C.1 idx h]
      rfl
    · rw [coordinateOfGate_degree_of_isAlgebraic s hgate (not_not.mp h)]
      simp [actualCoordinateDegree, s, h]
  have hb := finite_sum_coordinate_pole_le_degree Ω E (coordinateOfGate s hgate) W
  have hv : coordinateValue Ω E (coordinateOfGate s hgate) = s :=
    coordinateOfGate_value (K := Ω) (L := E) s hgate
  simpa only [hv, hd] using hb

theorem long_literal_seed_degrees_pos_lp32
    (F : Carrier K) (G : MvPolynomial (Fin 3) Ω) (hdiv : G ∣ surfaceMap φ F)
    (hG : Irreducible G) (hproper : ¬ G ∣ surfaceMap φ (tailNumerator F w))
    (caps : LongLiteralSeedCaps_lp32 G (surfaceMap φ (tailNumerator F w)))
    (C : FirstTailComponent F w G) :
    1 ≤ actualCoordinateDegree Ω C.1 1 + actualCoordinateDegree Ω C.1 2 := by
  letI : CharP Ω p := genericField_charP K p
  obtain ⟨seed, hseed⟩ := exists_long_literal_seed_projection_lp32 F w hdiv hG hproper caps C
  have hdeg : 1 ≤ actualCoordinateDegree Ω C.1 seed.index := by
    rw [actualCoordinateDegree_of_transcendental _ _ _ seed.transcendental]
    letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
      rationalBaseAlgebra Ω C.1 seed.index seed.transcendental
    letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) := seed.finite
    exact Module.finrank_pos
  rcases hseed with h | h
  · rw [h] at hdeg
    exact Nat.le_add_right_of_le hdeg
  · rw [h] at hdeg
    exact Nat.le_add_left_of_le hdeg

end

end ProximityPrize.SubmissionLower.K6833FactorCount

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
