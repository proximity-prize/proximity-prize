import ProximityPrize.SubmissionLower.Koala6831OrdinaryBenchmark
import ProximityPrize.SubmissionLower.Koala6831OrdinaryCarrierLift
import ProximityPrize.SubmissionLower.Koala6831OrdinaryFullTest
import ProximityPrize.SubmissionLower.Koala6831BenchmarkRetention
import ProximityPrize.SubmissionLower.Koala6831OrdinaryTests

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open Koala6831Intrinsic (implicitRegularity graphSpecialize)
open Koala6831Comparison Koala6831Quotient Koala6831OrdinaryIncidence
open Koala6831BenchmarkPrimitive (Received)
open Koala6831BenchmarkRetention (RetainedComparison retainedSeedBudget)
open ProximityPrize.Benchmark
open RCN136 RCN137 MvPolynomial
open scoped Classical Polynomial BigOperators

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4500000

variable {K E Ω I : Type} [Field K] [Field E] [Field Ω]

private theorem ordinarySurface_rename (φ : Polynomial K →+* E) (F : Carrier K) :
    ordinarySurface φ F = MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (surfaceMap φ F) := rfl

theorem ordinarySurface_comp (φ : Polynomial K →+* E) (ψ : E →+* Ω) (F : Carrier K) :
    ordinarySurface (ψ.comp φ) F = MvPolynomial.map ψ (ordinarySurface φ F) := by
  rw [ordinarySurface_rename, ordinarySurface_rename, MvPolynomial.map_rename]
  change MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (MvPolynomial.map (ψ.comp φ) (collectX K F)) =
    MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (MvPolynomial.map ψ (MvPolynomial.map φ (collectX K F)))
  rw [MvPolynomial.map_map]

theorem ordinarySurface_implicitRegularity (φ : Polynomial K →+* E) (F : Carrier K) :
    ordinarySurface φ (implicitRegularity F) = MvPolynomial.pderiv (1 : Fin 3) (ordinarySurface φ F) := by
  rw [ordinarySurface_rename, ordinarySurface_rename, implicitRegularity]
  have hswap : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
  have h := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 3) 1).injective 0 (surfaceMap φ F)
  rw [hswap, RCN267.surfaceMap_pderiv] at h
  exact h.symm

theorem exists_cleared_ordinary_factor (ψ : RatFunc K →+* Ω) (F : Carrier K) (hF : F ≠ 0)
    (y t : ℕ) (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t)
    (H : MvPolynomial (Fin 3) (RatFunc K))
    (hH : H ∈ normalizedFactorSet (ordinarySurface (algebraMap (Polynomial K) (RatFunc K)) F)) :
    ∃ (L : Carrier K) (c : Ω), c ≠ 0 ∧
      ordinarySurface (ψ.comp (algebraMap (Polynomial K) (RatFunc K))) L = MvPolynomial.C c * MvPolynomial.map ψ H ∧
      ordinarySurface (ψ.comp (algebraMap (Polynomial K) (RatFunc K))) (implicitRegularity L) =
        MvPolynomial.C c * MvPolynomial.pderiv (1 : Fin 3) (MvPolynomial.map ψ H) ∧
      ∀ d ∈ L.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t := by
  let φ := algebraMap (Polynomial K) (RatFunc K)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  obtain ⟨L, D, hD, hclear, hlift⟩ := exists_integral_carrier_lift H
  let c := ψ (φ D)
  have hc : c ≠ 0 := (map_ne_zero ψ).mpr (fun hz => hD (hφ (hz.trans (map_zero φ).symm)))
  have hclearΩ : ordinarySurface (ψ.comp φ) L = MvPolynomial.C c * MvPolynomial.map ψ H := by
    rw [ordinarySurface_comp, hclear, map_mul, MvPolynomial.map_C]
  refine ⟨L, c, hc, hclearΩ, ?_, ?_⟩
  · rw [ordinarySurface_implicitRegularity, hclearΩ, MvPolynomial.pderiv_mul]
    simp
  · let Q := ordinarySurface φ F
    have hQ : Q ≠ 0 := fun hz => hF (ordinarySurface_injective φ hφ (by simpa only [map_zero] using hz))
    obtain ⟨hy, ht⟩ := ordinarySurface_degree_caps φ F y t hcap
    obtain ⟨sumY, sumT⟩ := factor_degree_budgets Q hQ
    have hd : H.degreeOf 1 ≤ y :=
      ((Finset.single_le_sum (fun J _ => Nat.zero_le (J.degreeOf (1 : Fin 3))) hH).trans sumY).trans hy
    have hdt : H.totalDegree ≤ t :=
      ((Finset.single_le_sum (fun J _ => Nat.zero_le J.totalDegree) hH).trans sumT).trans ht
    exact fun d hdL => ⟨((hlift d hdL).1).trans hd, ((hlift d hdL).2).trans hdt⟩

private theorem eval_ordinary_mapped (φ : Polynomial K →+* E) (ψ : E →+* Ω)
    (P : K → Polynomial K) (p : ℕ) (g : K) (H : MvPolynomial (Fin 3) E) :
    MvPolynomial.aeval (ordinaryPoint (ψ.comp φ) P p g) (MvPolynomial.map ψ H) =
      ψ (MvPolynomial.eval (ordinaryPoint φ P p g) H) := by
  have hp : ordinaryPoint (ψ.comp φ) P p g = ψ ∘ ordinaryPoint φ P p g := by
    funext i
    fin_cases i <;> rfl
  rw [MvPolynomial.aeval_eq_eval, hp, MvPolynomial.eval_map, MvPolynomial.eval₂_comp]

private theorem hasOrdinaryAgreementTests [CharP Ω 2130706433]
    (ψ : RatFunc K →+* Ω) (F : Carrier K) (hF : F ≠ 0) (y t : ℕ)
    (hy : 1 ≤ y) (hyt : y ≤ t)
    (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t)
    (x : I ↪ K) (u₀ u₁ : I → K) (P : K → Polynomial K)
    (seeds : Finset K) (nodes : Finset I) (w : ℕ) (hw : w < 2130706433)
    (hdegree : ∀ g ∈ seeds, (P g).natDegree ≤ w) :
    HasOrdinaryAgreementTests (algebraMap (Polynomial K) (RatFunc K)) ψ F x u₀ u₁ P seeds nodes w y t := by
  let φ := algebraMap (Polynomial K) (RatFunc K)
  let ι := ψ.comp φ
  have hinj : Function.Injective ι := ψ.injective.comp (IsFractionRing.injective _ _)
  intro H hH
  obtain ⟨L, c, hc, hsurf, hsep, hL⟩ := exists_cleared_ordinary_factor ψ F hF y t hcap H hH
  obtain ⟨test, hfull⟩ := exists_ordinary_agreement_tests ι hinj L nodes x u₀ u₁ w y t hy hyt hL
  let adapted : ShortenedAgreementTests nodes
      (MvPolynomial.C c * MvPolynomial.pderiv (1 : Fin 3) (MvPolynomial.map ψ H)) w y t := {
    full := test.full
    short := test.short
    correct C isprime reg count i hi := by
      have sep : ordinarySurface ι (implicitRegularity L) =
          MvPolynomial.C c * MvPolynomial.pderiv (1 : Fin 3) (MvPolynomial.map ψ H) := hsep
      have hreg : ordinarySurface ι (implicitRegularity L) ∉ C := sep.symm ▸ reg
      simpa only [sep] using test.correct C isprime hreg count i hi }
  refine ⟨c, hc, adapted, ?_⟩
  intro g hg hroot hregular i hi
  let v := ordinaryPoint ι P 2130706433 g
  have point_eq : (fun j => ψ (ordinaryPoint φ P 2130706433 g j)) = v := by
    funext j
    fin_cases j <;> rfl
  have vanish : MvPolynomial.aeval v (ordinarySurface ι L) = 0 := by
    rw [hsurf, map_mul, eval_ordinary_mapped, hroot, map_zero, mul_zero]
  have graph_zero : graphSpecialize (P g) g (g ^ 2130706433) L = 0 := by
    change MvPolynomial.eval v (ordinarySurface ι L) = 0 at vanish
    rw [eval_ordinarySurface] at vanish
    exact hinj (vanish.trans (map_zero ι).symm)
  have regular : MvPolynomial.aeval v (ordinarySurface ι (implicitRegularity L)) ≠ 0 := by
    rw [hsep, map_mul, MvPolynomial.pderiv_map, eval_ordinary_mapped, MvPolynomial.aeval_C]
    exact mul_ne_zero hc ((map_ne_zero ψ).mpr hregular)
  change MvPolynomial.aeval (fun j => ψ (ordinaryPoint φ P 2130706433 g j)) (test.full i) = 0 ↔ _
  rw [point_eq, hfull]
  exact fullOrdinaryTest_graph_iff ι L P 2130706433 w hw g (x i) (u₀ i) (u₁ i)
    (hdegree g hg) graph_zero regular

theorem ordinary_retained_le_seed_budget [Fintype I] [CharP K 2130706433]
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ 2130706433) (hcard : Fintype.card I = 262144)
    (U : Received K I) (seeds : Finset K) (P : K → Polynomial K) (q : SymbolicRow (SeedRing K))
    (data : RetainedComparison x σ U seeds P q)
    (hδ : 11000 ≤ primitiveExcess 131071 q)
    (hc₂ : 2 ≤ weightDegree totalWeights (primitiveRowLift q))
    (hc₁₀ : weightDegree totalWeights (primitiveRowLift q) ≤ 10) :
    seeds.card ≤ retainedSeedBudget := by
  let E := RatFunc K
  let Ω := AlgebraicClosure E
  let φ := algebraMap (Polynomial K) E
  let ψ := algebraMap E Ω
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  let eChar : CharP E 2130706433 :=
    charP_of_injective_ringHom (f := φ.comp Polynomial.C) (hφ.comp Polynomial.C_injective) _
  let oChar : CharP Ω 2130706433 := charP_of_injective_ringHom (f := ψ) ψ.injective _
  have hδ' : primitiveExcess 131071 q ≤ 31357 := le_trans (Nat.le_add_right _ _) data.excess_bad
  have tests (F : Carrier K) (hF : F ≠ 0) (idx : Fin 9)
      (hcap : ∀ d ∈ F.support, d 1 ≤ (koalaCarrierShape idx).1 ∧ d 1 + d 2 + d 3 ≤ (koalaCarrierShape idx).2) :
      HasOrdinaryAgreementTests φ ψ F x (U 0) (U 1) P seeds Finset.univ 131071
        (koalaCarrierShape idx).1 (koalaCarrierShape idx).2 := by
    have hy : 1 ≤ (koalaCarrierShape idx).1 := by fin_cases idx <;> decide +kernel
    have hyt : (koalaCarrierShape idx).1 ≤ (koalaCarrierShape idx).2 := by fin_cases idx <;> decide +kernel
    exact hasOrdinaryAgreementTests ψ F hF _ _ hy hyt hcap x (U 0) (U 1) P seeds
      Finset.univ 131071 (by decide) data.selection.degree_le
  obtain ⟨idx, price⟩ := ordinary_retained_price φ hφ ψ x σ hfixed hpow hcard U seeds P
    data.selection q data.first_ne data.second_ne data.primitive hδ hδ' hc₂ hc₁₀ data.good tests
  exact price.trans ((Nat.le_add_right _ _).trans ((koala_ordinary_price_le idx).trans (by decide +kernel)))

theorem benchmark_ordinary_retained_le_seed_budget
    (U : Received IRSProfile.Field IRSProfile.Index) (seeds : Finset IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field) (q : SymbolicRow (SeedRing IRSProfile.Field))
    (data : RetainedComparison IRSProfile.domain Koala6831BenchmarkField.frobenius.toRingHom U seeds P q)
    (hδ : 11000 ≤ primitiveExcess 131071 q)
    (hc₂ : 2 ≤ weightDegree totalWeights (primitiveRowLift q))
    (hc₁₀ : weightDegree totalWeights (primitiveRowLift q) ≤ 10) :
    seeds.card ≤ retainedSeedBudget := by
  let hchar := Koala6831BenchmarkField.characteristic
  exact ordinary_retained_le_seed_budget IRSProfile.domain Koala6831BenchmarkField.frobenius.toRingHom
    Koala6831BenchmarkField.domain_fixed Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index
    U seeds P q data hδ hc₂ hc₁₀

end

end ProximityPrize.SubmissionLower.Koala6831Ordinary
