import ProximityPrize.SubmissionLower.BCHKSFrobeniusReceivedTailMatrix6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSReceivedTailCompressionShortRelation6401
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
def tailLaneWidth6401 : Nat := 22508
def tailFourLaneAmbient6401 : Nat := 4 * tailLaneWidth6401
def tailCompressionImageCap6401 : Nat := 2 * tailLaneWidth6401 - 1
def tailCompressionKernelFloor6401 : Nat :=
  tailFourLaneAmbient6401 - tailCompressionImageCap6401
def tailShortLaneSlots6401 : Nat := 11254
def tailHighLaneSlots6401 : Nat :=
  tailLaneWidth6401 - tailShortLaneSlots6401
def tailHighProjectionDimension6401 : Nat := 4 * tailHighLaneSlots6401
def tailCoherenceLaneSlots6401 : Nat := 11265
def tailCoherenceHighLaneSlots6401 : Nat :=
  tailLaneWidth6401 - tailCoherenceLaneSlots6401
def tailCoherenceProjectionDimension6401 : Nat :=
  4 * tailCoherenceHighLaneSlots6401
def tailCoherenceRelationFloor6401 : Nat :=
  tailCompressionKernelFloor6401 - tailCoherenceProjectionDimension6401
theorem tailCompression_shortRelation_arithmetic_exact6401 :
    tailFourLaneAmbient6401 = 90032 ∧
      tailCompressionImageCap6401 = 45015 ∧
      tailCompressionKernelFloor6401 = 45017 ∧
      tailShortLaneSlots6401 = 11254 ∧
      tailHighLaneSlots6401 = 11254 ∧
      tailHighProjectionDimension6401 = 45016 ∧
      tailHighProjectionDimension6401 <
        tailCompressionKernelFloor6401 ∧
      tailCoherenceLaneSlots6401 = 11265 ∧
      tailCoherenceHighLaneSlots6401 = 11243 ∧
      tailCoherenceProjectionDimension6401 = 44972 ∧
      tailCoherenceRelationFloor6401 = 45 := by
  native_decide
abbrev FourLaneTailVector6401 (F : Type*) :=
  Fin 4 → Fin tailLaneWidth6401 → F
abbrev FourLaneHighVector6401 (F : Type*) :=
  Fin 4 → Fin tailHighLaneSlots6401 → F
abbrev FourLaneCoherenceHighVector6401 (F : Type*) :=
  Fin 4 → Fin tailCoherenceHighLaneSlots6401 → F
def fourLaneHighProjection6401
    {F : Type*} [Field F] :
    FourLaneTailVector6401 F →ₗ[F] FourLaneHighVector6401 F where
  toFun v lane j := v lane
    ⟨tailShortLaneSlots6401 + j.1, by
      have hj := j.2
      norm_num [tailLaneWidth6401, tailShortLaneSlots6401,
        tailHighLaneSlots6401] at hj ⊢
      omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def fourLaneCoherenceHighProjection6401
    {F : Type*} [Field F] :
    FourLaneTailVector6401 F →ₗ[F] FourLaneCoherenceHighVector6401 F where
  toFun v lane j := v lane
    ⟨tailCoherenceLaneSlots6401 + j.1, by
      have hj := j.2
      norm_num [tailLaneWidth6401, tailCoherenceLaneSlots6401,
        tailCoherenceHighLaneSlots6401] at hj ⊢
      omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem exists_short_fourLaneRelation_of_range_finrank_le6401
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (T : FourLaneTailVector6401 F →ₗ[F] V)
    (hrank : Module.finrank F (LinearMap.range T) ≤
      tailCompressionImageCap6401) :
    ∃ v : FourLaneTailVector6401 F,
      v ≠ 0 ∧ T v = 0 ∧
        ∀ lane (j : Fin tailHighLaneSlots6401),
          v lane ⟨tailShortLaneSlots6401 + j.1, by
            have hj := j.2
            norm_num [tailLaneWidth6401, tailShortLaneSlots6401,
              tailHighLaneSlots6401] at hj ⊢
            omega⟩ = 0 := by
  let K := LinearMap.ker T
  have hnull := LinearMap.finrank_range_add_finrank_ker T
  have hambient : Module.finrank F (FourLaneTailVector6401 F) =
      tailFourLaneAmbient6401 := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Module.finrank_fin_fun F]
    norm_num [
      FourLaneTailVector6401, tailFourLaneAmbient6401,
      tailLaneWidth6401]
  have hK : tailCompressionKernelFloor6401 ≤ Module.finrank F K := by
    have hsum : Module.finrank F (LinearMap.range T) +
        Module.finrank F K = tailFourLaneAmbient6401 := by
      exact hnull.trans hambient
    have hrank' : Module.finrank F (LinearMap.range T) ≤ 45015 := by
      simpa [tailCompressionImageCap6401, tailLaneWidth6401] using hrank
    have hsum' : Module.finrank F (LinearMap.range T) +
        Module.finrank F K = 90032 := by
      simpa [tailFourLaneAmbient6401, tailLaneWidth6401] using hsum
    change 45017 ≤ Module.finrank F K
    omega
  let H : K →ₗ[F] FourLaneHighVector6401 F :=
    fourLaneHighProjection6401.comp K.subtype
  have htarget : Module.finrank F (FourLaneHighVector6401 F) =
      tailHighProjectionDimension6401 := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Module.finrank_fin_fun F]
    norm_num [
      FourLaneHighVector6401, tailHighProjectionDimension6401,
      tailHighLaneSlots6401]
  have hnotinj : ¬ Function.Injective H := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [htarget] at hle
    exact (not_le_of_gt
      tailCompression_shortRelation_arithmetic_exact6401.2.2.2.2.2.2.1) <|
        hK.trans hle
  have hkerne : LinearMap.ker H ≠ ⊥ := by
    intro hbot
    apply hnotinj
    intro x y hxy
    have hsub : x - y ∈ LinearMap.ker H := by
      rw [LinearMap.mem_ker]
      simpa using sub_eq_zero.mpr hxy
    have hzero : x - y = 0 := by
      have : x - y ∈ (⊥ : Submodule F K) := hbot ▸ hsub
      simpa using this
    exact sub_eq_zero.mp hzero
  obtain ⟨x, hxker, hxne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hkerne
  let v : FourLaneTailVector6401 F := x.1
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    apply hxne
    apply Subtype.ext
    exact hv
  · exact x.2
  · intro lane j
    have hxzero : H x = 0 := LinearMap.mem_ker.mp hxker
    have hentry := congrFun (congrFun hxzero lane) j
    simpa [H, fourLaneHighProjection6401, v] using hentry
theorem short_fourLaneRelationSpace_finrank_ge_45_6401
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (T : FourLaneTailVector6401 F →ₗ[F] V)
    (hrank : Module.finrank F (LinearMap.range T) ≤
      tailCompressionImageCap6401) :
    let K := LinearMap.ker T
    let H : K →ₗ[F] FourLaneCoherenceHighVector6401 F :=
      fourLaneCoherenceHighProjection6401.comp K.subtype
    45 ≤ Module.finrank F (LinearMap.ker H) := by
  dsimp only
  let K := LinearMap.ker T
  let H : K →ₗ[F] FourLaneCoherenceHighVector6401 F :=
    fourLaneCoherenceHighProjection6401.comp K.subtype
  have hnullT := LinearMap.finrank_range_add_finrank_ker T
  have hambient : Module.finrank F (FourLaneTailVector6401 F) = 90032 := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Module.finrank_fin_fun F]
    norm_num [tailLaneWidth6401]
  have hsumT : Module.finrank F (LinearMap.range T) +
      Module.finrank F K = 90032 := by
    exact hnullT.trans hambient
  have hrank' : Module.finrank F (LinearMap.range T) ≤ 45015 := by
    simpa [tailCompressionImageCap6401, tailLaneWidth6401] using hrank
  have hK : 45017 ≤ Module.finrank F K := by omega
  have htarget : Module.finrank F
      (FourLaneCoherenceHighVector6401 F) = 44972 := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Module.finrank_fin_fun F]
    norm_num [tailCoherenceHighLaneSlots6401, tailLaneWidth6401,
      tailCoherenceLaneSlots6401]
  have hrangeH : Module.finrank F (LinearMap.range H) ≤ 44972 := by
    exact (Submodule.finrank_le (LinearMap.range H)).trans_eq htarget
  have hnullH := LinearMap.finrank_range_add_finrank_ker H
  change 45 ≤ Module.finrank F (LinearMap.ker H)
  omega
end BCHKSReceivedTailCompressionShortRelation6401
end ProximityPrize.SubmissionLower
