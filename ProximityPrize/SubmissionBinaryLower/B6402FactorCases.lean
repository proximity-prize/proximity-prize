import ProximityPrize.SubmissionBinaryLower.B6402FactorAssembly
import ProximityPrize.SubmissionBinaryLower.B6402FrobeniusCase

/-! The invariant linear family and the quadratic family with a nonzero
middle slope coefficient suffice for every positive-slope factor. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402FactorCases
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6401Main
open B6401Params hiding A
open B6402HybridP64 (A BadOn6402)
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6402FrobeniusCase B6402FactorAssembly
set_option autoImplicit false
set_option maxHeartbeats 1600000
local notation "K" => BinaryIRSProfile.Field
local notation "I" => BinaryIRSProfile.Index

def QuadraticCount : Prop :=
  ∀ (u₀ u₁ : I → K) (F : ContactPoly (Polynomial K)), Irreducible F → contactDeriv F=0 →
    F.natDegree=2 → F.coeff 1≠0 → wdeg wY F≤26689499 → wYZ 1 F≤1811 →
    ∀ (S : Finset K) (P : K → Polynomial K) (Az : K → Finset I),
      (∀ z∈S,(P z).natDegree≤wY ∧ A≤(Az z).card ∧ BadOn6402 u₀ u₁ (Az z)) →
      (∀ z∈S,∀ i,i∈Az z ↔ (P z).eval (BinaryIRSProfile.domain i)=u₀ i+z*u₁ i) →
      (∀ z∈S,evalContact (evalZContact F z) (P z)=0) → S.card≤2*factorCap

theorem positive (linear : LinearFactorBound) (quad : QuadraticCount) : PositiveFactorCount := by
  intro u₀ u₁ Q F hQ hDQ hQdeg hQW hQZ hdiv hirr hpos S P Az hP hmatch onF
  obtain ⟨R,eq⟩ := hdiv
  have hr : R≠0 := fun hz => hQ (by rw [eq,hz,mul_zero])
  have hs := natDegree_mul hirr.ne_zero hr
  have hw := wdeg_mul wY hirr.ne_zero hr
  have hz := wYZ_mul 1 hirr.ne_zero hr
  rw [←eq] at hs hw hz
  have fw : wdeg wY F≤26689499 := by omega
  have fz : wYZ 1 F≤1811 := by omega
  by_cases hD : contactDeriv F=0
  · rcases (show F.natDegree=1 ∨ F.natDegree=2 by omega) with d|d
    · have hl := linear u₀ u₁ 1 (Or.inl rfl) F hirr hD d fw (by intro e; contradiction) fz S P Az
        (fun z h => (hP z h).1) onF (fun z h => (hP z h).2.1)
        (fun z h i => by simpa only [pow_one] using hmatch z h i) (fun z h => (hP z h).2.2)
      rw [d,one_mul]
      exact_mod_cast hl
    · rw [d]
      by_cases h1 : F.coeff 1=0
      · have hh := descended_bound linear u₀ u₁ hD d h1 fw fz S P Az (fun z h => (hP z h).1) onF
          (fun z h => (hP z h).2.1) hmatch (fun z h => (hP z h).2.2)
        have hc : S.card≤linearPrice 2+1000000000000 := by exact_mod_cast hh
        exact hc.trans (by decide)
      · exact quad u₀ u₁ F hirr hD d h1 fw fz S P Az hP hmatch onF
  · have hp : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    have hn : ¬F ∣ contactDeriv F := by rw [dvd_contactDeriv_iff wY (by decide) hirr.ne_zero]; exact hD
    have hprod : contactDeriv F*R+F*contactDeriv R=0 := by rw [←contactDeriv_mul,←eq,hDQ]
    have hfact : F ∣ contactDeriv F*R := ⟨contactDeriv R,by
      have hn2 : F*contactDeriv R+F*contactDeriv R=0 := CharTwo.add_self_eq_zero _
      calc _ = contactDeriv F*R+(F*contactDeriv R+F*contactDeriv R) := by rw [hn2,add_zero]
           _ = (contactDeriv F*R+F*contactDeriv R)+F*contactDeriv R := (add_assoc _ _ _).symm
           _ = _ := by rw [hprod,zero_add]⟩
    obtain ⟨C,hC⟩ := (hp.dvd_or_dvd hfact).resolve_left hn
    have hCne : C≠0 := fun he => hr (by rw [hC,he,mul_zero])
    have rs := natDegree_mul hirr.ne_zero hCne
    have rwgt := wdeg_mul wY hirr.ne_zero hCne
    rw [←hC] at rs rwgt
    have d : F.natDegree=1 := by omega
    have hd := B6402DerivativeFactor.card_le_of_contactDeriv_ne_zero u₀ u₁ (Or.inl rfl) hirr d
      (by omega) (fun k j i => (B6401QuotInterp.natDegree_Z_le_of_wYZ fz k j i).trans (by decide : 1811≤3850)) hD S P Az
      (fun z h => (hP z h).1) onF (fun z h => (hP z h).2.1)
      (fun z h i hi => by simpa only [pow_one] using (hmatch z h i).mp hi) (fun z h => (hP z h).2.2)
    have le : S.card≤10000000000000 := by exact_mod_cast hd
    rw [d,one_mul]
    exact le.trans (by decide)

#print axioms positive
end ProximityPrize.SubmissionBinaryLower.B6402FactorCases
