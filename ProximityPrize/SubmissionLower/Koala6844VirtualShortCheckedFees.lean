import ProximityPrize.SubmissionLower.Koala6844VirtualShortAdaptivePayment
import ProximityPrize.SubmissionLower.Koala6844VirtualShortRoomPayment
import ProximityPrize.SubmissionLower.Koala6844VirtualShortSupport
import Mathlib.FieldTheory.AlgebraicClosure


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort
open scoped Classical
open ProximityPrize.Benchmark
open Koala6844Normalization Koala6844VirtualDispatch Koala6844Receipts Koala6844Terminal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 5000

local instance benchmarkShortCharacteristic : CharP IRSProfile.Field prime :=
  Koala6844BenchmarkField.characteristic

theorem benchmark_short_fees (domain : Finset IRSProfile.Index) (excess : ℕ)
    (data : VirtualFamily domain excess)
    (hpole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth) :
    ShortPhaseFees data (short_benchmark_domain_size domain) hpole := by
  let embed : IRSProfile.Field →+* AlgebraicClosure IRSProfile.Field := algebraMap _ _
  obtain ⟨germ⟩ := exists_active_resultant_germ data embed
  have hσ (g : IRSProfile.Field) (_hg : g ∈ data.seeds) :
      embed (Koala6844BenchmarkField.frobenius g) = (embed g)^prime := by
    rw [Koala6844BenchmarkField.frobenius_apply, map_pow]
    rfl
  have rooms := fixed_room_fee_callbacks data embed germ hσ
  refine ⟨rooms.1,rooms.2,?_,?_⟩
  · intro H A _ hfit pass
    exact adaptive_fee_first data (short_benchmark_domain_size domain) hpole embed germ hσ H A hfit pass
  · intro H A _ hfit first second
    exact adaptive_fee_second data (short_benchmark_domain_size domain) hpole embed germ hσ H A hfit first second

theorem short_support_of_verified_endpoints
    (table : List CertifiedEndpoint) (hTable : AdaptiveEndpointCover table)
    (hTerm : ∀ e ∈ table, terminalMetadata e = true)
    (hRaw : ∀ e ∈ table, intrinsicRawMetadata e = true)
    (margins : ∀ i : Fin contactProfiles.size, sourceMargin contactProfiles[i]) :
    ShortSupportBound :=
  short_support (fun domain excess _ data hpole _ => benchmark_short_fees domain excess data hpole)
    table hTable hTerm hRaw margins

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort

