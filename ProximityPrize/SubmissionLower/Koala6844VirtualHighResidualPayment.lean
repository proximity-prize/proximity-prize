import ProximityPrize.SubmissionLower.Koala6844VirtualHighBudget
import ProximityPrize.SubmissionLower.Koala6844VirtualHighCarrierResidual


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh
open Koala6844Normalization Koala6831OrdinaryIncidence ProximityPrize.Benchmark
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem tailRectangle_mono (j : ℕ) {f g : Rectangle}
    (hy : f.value ≤ g.value) (hb : f.first ≤ g.first) (hc : f.second ≤ g.second) :
    (tailRectangle j f).value ≤ (tailRectangle j g).value ∧
    (tailRectangle j f).first ≤ (tailRectangle j g).first ∧
    (tailRectangle j f).second ≤ (tailRectangle j g).second := by
  unfold tailRectangle tailValue
  exact ⟨Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hy _)) _,
    Nat.add_le_add_right (Nat.mul_le_mul_left _ hb) _,
    Nat.add_le_add_right (Nat.mul_le_mul_left _ hc) _⟩

private theorem mixedDegree_right_mono {f a b c d : Rectangle}
    (hac : a.value ≤ c.value ∧ a.first ≤ c.first ∧ a.second ≤ c.second)
    (hbd : b.value ≤ d.value ∧ b.first ≤ d.first ∧ b.second ≤ d.second) :
    mixedDegree f a b ≤ mixedDegree f c d := by
  obtain ⟨ha₀,ha₁,ha₂⟩ := hac
  obtain ⟨hb₀,hb₁,hb₂⟩ := hbd
  unfold mixedDegree
  gcongr

variable {nodes : Finset IRSProfile.Index} {excess : ℕ}

theorem pay_benchmark_residual_factor (D : BenchmarkVirtualFamily nodes excess)
    (trim : CenteredTrimCarrier D 124396 144396)
    (F : BenchmarkVirtualCarrier) (hirr : Irreducible F) (hy : 0 < F.degreeOf 1)
    (aggregate : Rectangle) (hagg₀ : F.degreeOf 1 ≤ aggregate.value) (hagg₁ : F.degreeOf 2 ≤ aggregate.first)
    (hagg₂ : F.degreeOf 3 ≤ aggregate.second)
    (hymax : aggregate.value ≤ 45) (hbmax : aggregate.first ≤ 1018) (hcmax : aggregate.second ≤ 1018)
    (bound : ℕ) (hbound : 144397 ≤ bound) (hchar : bound < modulus)
    (hweight : RCN234.wt (![1,144396,0,0] : Fin 4 → ℕ) F < bound)
    (hselected : 131071 + D.d0.natDegree - affineDegree D.A0 ≤ 144396)
    (haverage : nodeAverage nodes.card 144396 180958 ≤ 4) :
    (regularSeeds benchmarkVirtualSeed modulus (benchmarkSurfaceValue D) D.seeds F).card ≤
      mixedDegree (integralRectangle F) (tailRectangle 124397 aggregate) (tailRectangle 124398 aggregate) +
        invariantRate*F.degreeOf 1 := by
  letI : CharP BenchmarkVirtualField modulus := benchmarkVirtualCharacteristic
  have hσ (g : IRSProfile.Field) (_hg : g ∈ D.seeds) :
      benchmarkVirtualEmbedding (Koala6844BenchmarkField.frobenius g) =
      (benchmarkVirtualEmbedding g)^modulus := by
    rw [Koala6844BenchmarkField.frobenius_apply,map_pow]
    rfl
  have hfc : F.degreeOf 1 ≤ (integralRectangle F).value ∧ F.degreeOf 2 ≤ (integralRectangle F).first ∧
      F.degreeOf 3 ≤ (integralRectangle F).second := ⟨le_rfl,le_rfl,le_rfl⟩
  let V := MvPolynomial.map benchmarkVirtualEmbedding trim.V
  let W := MvPolynomial.map benchmarkVirtualEmbedding trim.W
  have hsets :
      regularSeeds benchmarkVirtualSeed modulus (benchmarkSurfaceValue D) D.seeds F =
        regularSurfaceSeeds benchmarkVirtualEmbedding modulus D.normalized D.seeds F := rfl
  rw [hsets]
  by_cases hdiv : F ∣ rawTrimmedTail F V W 124396
  · have hcount := mapped_regular_whole_carrier_count D benchmarkVirtualEmbedding modulus 124396 144396 bound
      hσ D.seeds (fun _ h => h) trim F hirr hdiv (integralRectangle F)
      (hagg₀.trans_lt (hymax.trans_lt (by decide +kernel : 45 < modulus)))
      (hagg₂.trans_lt (hcmax.trans_lt (by decide +kernel : 1018 < modulus)))
      hfc (by omega) hbound hchar hweight hselected (by decide +kernel) haverage
    have hrate : 4*((integralRectangle F).first+1+modulus*(integralRectangle F).second)+1 ≤ invariantRate := by
      unfold integralRectangle invariantRate
      dsimp only
      gcongr
      · exact hagg₁.trans hbmax
      · exact hagg₂.trans hcmax
    exact hcount.trans ((Nat.mul_le_mul_right _ hrate).trans (Nat.le_add_left _ _))
  · have hcount := mapped_regular_proper_carrier_count D benchmarkVirtualEmbedding modulus 124396 144396
      124397 bound _root_.KoalaBear.is_prime hσ D.seeds (fun _ h => h) trim F hirr
      (by omega) hdiv (integralRectangle F) hy le_rfl (by decide +kernel)
      hfc (by omega) hbound hchar hweight hselected (by decide +kernel) haverage
    have h := mixedDegree_right_mono
      (f := integralRectangle F)
      (tailRectangle_mono 124397 (f := integralRectangle F) (g := aggregate) hagg₀ hagg₁ hagg₂)
      (tailRectangle_mono 124398 (f := integralRectangle F) (g := aggregate) hagg₀ hagg₁ hagg₂)
    exact (hcount.trans h).trans (Nat.le_add_right _ _)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

