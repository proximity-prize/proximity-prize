import ProximityPrize.SubmissionBinaryLower.B6402OrdinaryLinear
import ProximityPrize.SubmissionBinaryLower.B6402FrobeniusCase

namespace ProximityPrize.SubmissionBinaryLower.B6402LinearSplit
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd
open B6401Params hiding A
open B6402HybridP64 (A BadOn6402)
open B6402PointSurplus B6402FrobeniusCase B6402OrdinaryLinear
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
set_option autoImplicit false
set_option maxHeartbeats 1500000
local notation "K" => BinaryIRSProfile.Field
local notation "I" => BinaryIRSProfile.Index

def HardLinear : Prop :=
  ∀ (u₀ u₁ : I → K) (q : ℕ), (q=1 ∨ q=2) → ∀ (F : ContactPoly (Polynomial K)),
    Irreducible F → contactDeriv F=0 → F.natDegree=1 → (F.coeff 1).natDegree=4 →
    (F.coeff 0).natDegree≤5 → (wdeg wY F:ℚ)/wY<28/5 → wYZ q F≤1811 →
    ∀ (S : Finset K) (P : K → K[X]) (Az : K → Finset I),
      (∀ z∈S,(P z).natDegree≤wY) → (∀ z∈S,evalContact (evalZContact F z) (P z)=0) →
      (∀ z∈S,A≤(Az z).card) → (∀ z∈S,∀ i,i∈Az z ↔ (P z).eval (BinaryIRSProfile.domain i)=u₀ i+z^q*u₁ i) →
      (∀ z∈S,BadOn6402 u₀ u₁ (Az z)) → (S.card:ℚ)≤linearPrice q

theorem linear_of_hard (hard : HardLinear) : LinearFactorBound := by
  intro u₀ u₁ q hq F irr invariant slope hw half hz S P Az deg onF fits matchP bad
  let W := wdeg wY F
  by_cases case4 : (F.coeff 1).natDegree=4 ∧ (F.coeff 0).natDegree≤5 ∧ (W:ℚ)/wY<28/5
  · exact hard u₀ u₁ q hq F irr invariant slope case4.1 case4.2.1 case4.2.2 hz S P Az deg onF fits matchP bad
  obtain ⟨c,he,_⟩ := (mem_kerD_iff_exists_unique_coords (wY:=wY) (W:=W) (s:=1) (by decide) F).mp ⟨invariant,slope.le,le_rfl⟩
  have hW : (W:ℚ)/wY≤51/2 := by
    rw [div_le_iff₀ (by decide : (0:ℚ)<wY)]
    have h : (W:ℚ)≤26689499 := by exact_mod_cast hw
    norm_num [wY]; linarith
  have hq2 (eq : q=2) : (W:ℚ)/wY<13 ∧ 1811≤1811 := by
    refine ⟨(div_lt_iff₀ (by decide : (0:ℚ)<wY)).mpr ?_,le_rfl⟩
    have h : W≤13345478 := half eq
    norm_num [wY]; omega
  have ci := small_linear u₀ u₁ hq hW hq2 c
    (he ▸ B6401Main.irreducible_liftCRat_of_irred irr (by omega))
    (he ▸ slope) (by rw [←he]) (he ▸ hz) S P Az deg (he ▸ onF) fits matchP bad (he ▸ case4)
  rcases hq with rfl|rfl
  · exact ci.trans (by decide +kernel)
  · exact ci.trans (by decide +kernel)

#print axioms linear_of_hard
end ProximityPrize.SubmissionBinaryLower.B6402LinearSplit
