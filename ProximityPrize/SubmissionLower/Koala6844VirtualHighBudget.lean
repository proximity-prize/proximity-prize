import ProximityPrize.SubmissionLower.Koala6844VirtualHighStages
import ProximityPrize.SubmissionLower.Koala6844VirtualHighBenchmarkSources


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh
open Koala6844Normalization RCN132 RCN137 ProximityPrize.Benchmark
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4000

def invariantRate : ℕ := 4*(1018+1+modulus*1018)+1

private theorem mixed_linear (f g h : Rectangle) :
    mixedDegree f g h =
      f.value * (g.first*h.second + g.second*h.first) +
      f.first * (g.value*h.second + h.value*g.second) +
      f.second * (g.value*h.first + h.value*g.first) := by
  unfold mixedDegree
  ring

private theorem sum_residual_price {K : Type} [Field K] (U : Finset (MvPolynomial (Fin 4) K))
    (g h : Rectangle) (hnz : ∀ f ∈ U, f ≠ 0) :
    (∑ f ∈ U, (mixedDegree (integralRectangle f) g h + invariantRate*f.degreeOf 1)) =
      mixedDegree (factorRectangle U) g h + invariantRate*(factorRectangle U).value := by
  have hsum (i : Fin 4) := sum_degree_eq_factorRectangle U i hnz
  simp only [mixed_linear, integralRectangle, factorRectangle, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hsum]

theorem virtual_budget_of_factor_counts {K Seed : Type} [Field K] [Field Seed]
    (embed : Seed →+* RationalCoefficients K) (v : Seed → RationalCoefficients K)
    (A : Finset Seed) (U : Finset (MvPolynomial (Fin 4) K))
    (room adaptiveDone excluded : Finset Seed)
    (cover : A ⊆ room ∪ adaptiveDone ∪ U.biUnion (regularSeeds embed modulus v A) ∪ excluded)
    (hroom : room.card ≤ resultantCharge modulus primaryBox roomBox)
    (hadaptive : adaptiveDone.card ≤ resultantCharge modulus remainingBox adaptiveBox)
    (hexcluded : excluded.card ≤ excludedBudget)
    (hnz : ∀ f ∈ U, f ≠ 0)
    (hcaps : U = ∅ ∨ 1 ≤ (factorRectangle U).value ∧ (factorRectangle U).value ≤ 45 ∧
      (factorRectangle U).first ≤ 1018 ∧ (factorRectangle U).second ≤ 1018 ∧
      adaptiveGap ≤ bandRectangle 6975 133094 (factorRectangle U).value
        (factorRectangle U).first (factorRectangle U).second)
    (hresidual : ∀ f ∈ U, (regularSeeds embed modulus v A f).card ≤
      mixedDegree (integralRectangle f) (tailRectangle 124397 (factorRectangle U))
        (tailRectangle 124398 (factorRectangle U)) + invariantRate*f.degreeOf 1) :
    A.card ≤ 270779581434104148 := by
  have hlast : (U.biUnion (regularSeeds embed modulus v A)).card ≤
      215212585876172700 + invariantSurfaceBudget := by
    rcases hcaps with he | hcap
    · simp [he]
    obtain ⟨hval,hv,hb,hc,hgate⟩ := hcap
    have hmixed := residual_price_le hval hv hb hc hgate
    have hinvariant := (Nat.mul_le_mul_left invariantRate hv).trans
      (by decide +kernel : invariantRate*45 ≤ invariantSurfaceBudget)
    calc
      _ ≤ ∑ f ∈ U, (regularSeeds embed modulus v A f).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum hresidual
      _ = _ := sum_residual_price U _ _ hnz
      _ ≤ _ := Nat.add_le_add hmixed hinvariant
  calc
    _ ≤ (room ∪ adaptiveDone ∪ U.biUnion (regularSeeds embed modulus v A) ∪ excluded).card :=
      Finset.card_le_card cover
    _ ≤ room.card + adaptiveDone.card + (U.biUnion (regularSeeds embed modulus v A)).card +
        excluded.card := by
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)
    _ ≤ _ := by
      rw [← virtual_total_budget]
      have h := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hroom hadaptive) hlast) hexcluded
      simpa only [Nat.add_assoc] using h

variable {nodes : Finset IRSProfile.Index} {excess : ℕ}

def benchmarkFamilyCovers (A : Finset IRSProfile.Field)
    (v : IRSProfile.Field → BenchmarkVirtualFraction) (U : Finset BenchmarkVirtualCarrier)
    (room adaptiveDone excluded : Finset IRSProfile.Field) : Prop :=
  letI : DecidableEq IRSProfile.Field := Classical.decEq _
  A ⊆ room ∪ adaptiveDone ∪ U.biUnion (regularSeeds benchmarkVirtualSeed modulus v A) ∪ excluded

theorem exists_benchmark_virtual_families (D : BenchmarkVirtualFamily nodes excess)
    (sources : BenchmarkVirtualSources D) :
    ∃ U ⊆ primaryFactors sources.primarySource.val,
      ∃ room adaptiveDone excluded : Finset IRSProfile.Field,
      benchmarkFamilyCovers D.seeds (benchmarkSurfaceValue D) U room adaptiveDone excluded ∧
      room.card ≤ resultantCharge modulus primaryBox roomBox ∧
      adaptiveDone.card ≤ resultantCharge modulus remainingBox adaptiveBox ∧
      excluded.card ≤ excludedBudget ∧
      (U = ∅ ∨ 1 ≤ (factorRectangle U).value ∧ (factorRectangle U).value ≤ 45 ∧
        (factorRectangle U).first ≤ 1018 ∧ (factorRectangle U).second ≤ 1018 ∧
        adaptiveGap ≤ bandRectangle 6975 133094 (factorRectangle U).value
          (factorRectangle U).first (factorRectangle U).second) := by
  letI : CharP BenchmarkVirtualField modulus := benchmarkVirtualCharacteristic
  letI : Module.Finite BenchmarkVirtualField (benchmarkVirtualBox D adaptive) := by
    unfold benchmarkVirtualBox
    infer_instance
  letI : Module.Finite BenchmarkVirtualField sources.adaptiveSpace :=
    Module.Finite.of_injective sources.adaptiveSpace.subtype sources.adaptiveSpace.subtype_injective
  have hp : sources.primarySource.val ≠ 0 := fun h => sources.primary_ne (Subtype.ext h)
  have hh : sources.roomSource.val ≠ 0 := fun h => sources.room_ne (Subtype.ext h)
  refine exists_virtual_families (V := ↥sources.adaptiveSpace) _root_.KoalaBear.is_prime benchmarkVirtualSeed
    (benchmarkSurfaceValue D) D.seeds (benchmarkSurfaceValue_injOn D)
    sources.primarySource.val sources.roomSource.val hp hh
    (mappedSourceDegree D.d0.natDegree (affineDegree D.A0)) D.d0.natDegree
    (mappedSourceCutoff primary D.d0.natDegree)
    (mappedSourceCutoff roomSource D.d0.natDegree)
    (mappedSourceCutoff adaptive D.d0.natDegree)
    sources.content_pos sources.primarySource.property sources.roomSource.property
    sources.primary_vanishes ?_ sources.adaptiveMap sources.adaptiveMap_injective
    sources.adaptiveMap_mem sources.adaptive_dim ?_
  · intro i hi k hk
    rcases hi with h | h
    · subst i; exact sources.room_vanishes false k hk
    · subst i; exact sources.room_vanishes true k hk
  · intro v j hj hbox i hi k hk
    rcases hi with h | h
    · subst i; exact sources.adaptive_vanishes v j hj hbox false k hk
    · subst i; exact sources.adaptive_vanishes v j hj hbox true k hk

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

