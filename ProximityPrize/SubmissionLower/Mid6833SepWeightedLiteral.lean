/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from the frozen 68.32 submission of Bome2017, building on Lucieno
(PR 618) and BitWonka (PRs 581 and 582). KoalaBear 69.69 long branch, November 18. -/
/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,66 errors, right cap 159 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.Mid6833SepLongLiteral
import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartProjection

namespace ProximityPrize.SubmissionLower.SepCount6969
open Koala6831Intrinsic

open scoped Classical BigOperators
open MvPolynomial RCN002 RCN005 RCN007 RCN042 RCN093 RCN112 RCN113 RCN120 RCN135 RCN136 RCN344

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 350000
set_option Elab.async false

private theorem literal_coordinate_degree_eq_actual_lp32 {L : Type} [Field L] [IsAlgClosed L]
    (P : Ideal (MvPolynomial (Fin 3) L)) [P.IsPrime] (order : Fin 3 ≃ Fin 3)
    (hgate : ∀ hx : Transcendental L (flagEvaluation L P 0 0 0 (MvPolynomial.X (order 0))),
      (letI := flagBaseAlgebra L P 0 0 0 order hx
       FiniteDimensional (RatFunc L) (CoordinateField L P)) ∧
      (letI := flagBaseAlgebra L P 0 0 0 order hx
       Algebra.IsSeparable (RatFunc L) (CoordinateField L P))) :
    coordinateDegree L (CoordinateField L P)
      (coordinateOfGate (flagEvaluation L P 0 0 0 (MvPolynomial.X (order 0))) hgate) =
      actualCoordinateDegree L P (order 0) := by
  let x := flagEvaluation L P 0 0 0 (MvPolynomial.X (order 0))
  by_cases h : Transcendental L (coordinate L P (order 0))
  · have ht : Transcendental L x := by simpa only [x, flagEvaluation_zero_X] using h
    rw [coordinateOfGate_degree_of_transcendental x hgate ht, actualCoordinateDegree_of_transcendental L P _ h]
    change (letI := flagBaseAlgebra L P 0 0 0 order ht
      Module.finrank (RatFunc L) (CoordinateField L P)) = _
    rw [flagBaseAlgebra_zero_eq_lp32 P order ht h]
  · have halg : IsAlgebraic L x := by
      simpa only [x, flagEvaluation_zero_X] using (not_not.mp h)
    rw [coordinateOfGate_degree_of_isAlgebraic x hgate halg, actualCoordinateDegree, dif_neg h]

variable {K A : Type} [Field K] [Fintype A] [CharP K 2130706433]
variable (F : Carrier K) (w : ℕ) (hp : Nat.Prime 2130706433)
variable {G : MvPolynomial (Fin 3) (GenericField K)}

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K
local notation "T" => surfaceMap (polynomialEmbedding K) (tailNumerator F w)

variable (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F) (hG : Irreducible G)
variable (hproper : ¬ G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F w))
variable (caps : LongLiteralSeedCaps_lp32 G (surfaceMap (polynomialEmbedding K) (tailNumerator F w)))
variable (component : A → LongTailRegularComponent_lp32 F w G) (hinj : Function.Injective component)
variable (charts : ∀ a, CurveChartData F w (component a).1)
variable (W : ∀ a, Finset (Place (GenericField K) (CoordinateField (GenericField K) (component a).1)))

include hp hdiv hG hproper caps hinj in

theorem intrinsic_literal_weighted_degree_bound_of_resultant_lp32 (useZ₁ : Bool)
    (budget : ℕ) (hdegree : (flagPlaneResultant (0 : Ω) 0 0 (longSeedOrder_lp32 useZ₁) G T).natDegree ≤ budget) :
    (∑ a, curveTailOrder F w (component a).1 (charts a) *
      actualCoordinateDegree Ω (component a).1 (longSeedOrder_lp32 useZ₁ 0)) ≤ budget := by
  classical
  by_cases hA : Nonempty A
  · obtain ⟨a₀⟩ := hA
    letI : CharP Ω 2130706433 := genericField_charP K 2130706433
    let order := longSeedOrder_lp32 useZ₁
    let E (a : A) := CoordinateField Ω (component a).1
    let u (a : A) := flagEvaluation Ω (component a).1 0 0 0 (MvPolynomial.X (order 0))
    have hgate (a : A) (hx : Transcendental Ω (u a)) :
        (letI := flagBaseAlgebra Ω (component a).1 0 0 0 order hx
         FiniteDimensional (RatFunc Ω) (E a)) ∧
        (letI := flagBaseAlgebra Ω (component a).1 0 0 0 order hx
         Algebra.IsSeparable (RatFunc Ω) (E a)) :=
      long_zero_flag_projection_gate_lp32 F w hdiv hG hproper caps (component a) useZ₁ hx
    let weight (a : A) := curveTailOrder F w (component a).1 (charts a)
    let cost (a : A) := weight a * actualCoordinateDegree Ω (component a).1 (order 0)
    let Active := {a : A // Transcendental Ω (u a)}
    letI : Fintype Active := inferInstanceAs (Fintype {a : A // Transcendental Ω (u a)})
    have hpositive : 0 < (flagPlaneMap Ω 0 0 0 order G).natDegree := by
      simpa only [flagPlaneMap_zero_apply] using
        long_regular_seed_outer_positive_lp32 F w hdiv (component a₀) useZ₁
    have hactive : (∑ a : Active, cost a.1) ≤ budget := by
      have hsub := intrinsic_sum_order_mul_coordinateDegree_le F w 2130706433 hp
        (fun a : Active => component a.1) (fun a => charts a.1) 0 0 0 order
        (fun a => a.2) (fun a => (hgate a.1 a.2).1)
        (fun a => zero_flag_generators_lp32 (component a.1).1 order a.2)
        (hinj.comp Subtype.val_injective) hG hdiv rfl hproper hpositive (fun a => hgate a.1) budget hdegree
      calc
        _ = ∑ a : Active, weight a.1 * coordinateDegree Ω (E a.1)
            (coordinateOfGate (u a.1) (hgate a.1)) := by
          apply Finset.sum_congr rfl
          intro a _
          change weight a.1 * _ = weight a.1 * _
          rw [literal_coordinate_degree_eq_actual_lp32 (component a.1).1 order (hgate a.1)]
        _ ≤ budget := hsub
    show (∑ a : A, cost a) ≤ budget
    calc
      _ = ∑ a ∈ Finset.univ.filter (fun a => Transcendental Ω (u a)), cost a := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hn
        have htrans : ¬ Transcendental Ω (coordinate Ω (component a).1 (order 0)) := by
          intro hx
          apply hn
          exact Finset.mem_filter.mpr ⟨ha, by simpa only [u, flagEvaluation_zero_X] using hx⟩
        simp only [cost, actualCoordinateDegree, dif_neg htrans, mul_zero]
      _ = ∑ a : Active, cost a.1 := by
        simpa only [Active, Finset.subtype_univ] using
          (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset A))
            cost (p := fun a => Transcendental Ω (u a))).symm
      _ ≤ budget := hactive
  · letI : IsEmpty A := not_nonempty_iff.mp hA
    simp

include hdiv hG hproper caps in
private theorem literal_weighted_pole_bound_of_degree_lp32 (useZ₁ : Bool)
    (budget : ℕ) (hdegree : (∑ a, curveTailOrder F w (component a).1 (charts a) *
      actualCoordinateDegree Ω (component a).1 (longSeedOrder_lp32 useZ₁ 0)) ≤ budget) :
    (∑ a, (curveTailOrder F w (component a).1 (charts a) : ℤ) * ∑ v ∈ W a,
      RCN187.poleOrder v.val (coordinate Ω (component a).1 (longSeedOrder_lp32 useZ₁ 0))) ≤ (budget : ℤ) := by
  letI : CharP Ω 2130706433 := genericField_charP K 2130706433
  let order := longSeedOrder_lp32 useZ₁
  calc
    _ ≤ ∑ a, (curveTailOrder F w (component a).1 (charts a) : ℤ) *
        (actualCoordinateDegree Ω (component a).1 (order 0) : ℤ) := by
      apply Finset.sum_le_sum
      intro a _
      let E := CoordinateField Ω (component a).1
      let u := flagEvaluation Ω (component a).1 0 0 0 (MvPolynomial.X (order 0))
      have hgate (hx : Transcendental Ω u) :=
        long_zero_flag_projection_gate_lp32 F w hdiv hG hproper caps (component a) useZ₁ hx
      have hlocal := finite_sum_coordinate_pole_le_degree Ω E (coordinateOfGate u hgate) (W a)
      rw [coordinateOfGate_value, literal_coordinate_degree_eq_actual_lp32 (component a).1 order hgate] at hlocal
      exact mul_le_mul_of_nonneg_left (by simpa only [RCN346.poleOrder, u, flagEvaluation_zero_X]
        using hlocal) (Int.natCast_nonneg _)
    _ ≤ _ := by exact_mod_cast hdegree

include hp hdiv hG hproper caps hinj in

theorem intrinsic_literal_weighted_degree_bound_lp32 (useZ₁ : Bool) (gy gt gz : ℕ)
    (hyt : gy ≤ gt) (hGy : G.degreeOf 0 ≤ gy) (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ gt)
    (hGz : G.degreeOf 2 ≤ gz) :
    (∑ a, curveTailOrder F w (component a).1 (charts a) *
      actualCoordinateDegree Ω (component a).1 (longSeedOrder_lp32 useZ₁ 0)) ≤
      if useZ₁ then 4718575 * gt + gy * 49282885 - 4718575 * gy
      else 4718575 * gz + gy * 41680737 := by
  apply intrinsic_literal_weighted_degree_bound_of_resultant_lp32 F w hp hdiv hG hproper caps
    component hinj charts useZ₁
  rw [flagPlaneResultant_zero_eq_lp32]
  cases useZ₁
  · exact seedZero_resultant_degree_lp32 G T gy 4718575 gz 41680737 hGy caps.Ty hGz caps.Tz
  · have hTne : T ≠ 0 := fun h => hproper (h ▸ dvd_zero G)
    exact seedOne_resultant_degree_lp32 G T gy 4718575 gt 49282885 hyt hTne hGy caps.Ty hGt caps.Tt

include hp hdiv hG hproper caps hinj in

theorem intrinsic_literal_weighted_pole_bound_lp32 (useZ₁ : Bool) (gy gt gz : ℕ)
    (hyt : gy ≤ gt) (hGy : G.degreeOf 0 ≤ gy) (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ gt)
    (hGz : G.degreeOf 2 ≤ gz) :
    (∑ a, (curveTailOrder F w (component a).1 (charts a) : ℤ) * ∑ v ∈ W a,
      RCN187.poleOrder v.val (coordinate Ω (component a).1 (longSeedOrder_lp32 useZ₁ 0))) ≤
      ((if useZ₁ then 4718575 * gt + gy * 49282885 - 4718575 * gy
        else 4718575 * gz + gy * 41680737 : ℕ) : ℤ) :=
  literal_weighted_pole_bound_of_degree_lp32 F w hdiv hG hproper caps component charts W useZ₁ _
    (intrinsic_literal_weighted_degree_bound_lp32 F w hp hdiv hG hproper caps component hinj charts
      useZ₁ gy gt gz hyt hGy hGt hGz)

end

end ProximityPrize.SubmissionLower.SepCount6969

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
