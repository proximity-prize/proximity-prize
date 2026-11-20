import ProximityPrize.SubmissionLower.Koala6844VirtualShortAssembly
import ProximityPrize.SubmissionLower.Koala6844VirtualDispatch


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical
open ProximityPrize.Benchmark
open Koala6844Normalization Koala6844VirtualDispatch Koala6844Receipts Koala6844Terminal

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1700000

local instance shortSupportCharacteristic : CharP IRSProfile.Field prime :=
  Koala6844BenchmarkField.characteristic

theorem short_benchmark_domain_size (domain : Finset IRSProfile.Index) : domain.card ≤ nodes :=
  (Finset.card_le_univ domain).trans IRSProfile.card_index.le

theorem short_support
    (hFees : ∀ (domain : Finset IRSProfile.Index) (excess : Nat), excess ≤ 9799 →
      ∀ (data : VirtualFamily domain excess)
        (hpole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth),
      (∀ i ∈ domain, (data.A0 1).eval (IRSProfile.domain i) ≠ 0) →
      ShortPhaseFees data (short_benchmark_domain_size domain) hpole)
    (table : List CertifiedEndpoint) (hTable : AdaptiveEndpointCover table)
    (hTerm : ∀ e ∈ table, terminalMetadata e = true)
    (hRaw : ∀ e ∈ table, intrinsicRawMetadata e = true)
    (margins : ∀ i : Fin contactProfiles.size, sourceMargin contactProfiles[i]) :
    ShortSupportBound := by
  intro domain excess hexcess data hpole hLead
  have hσ (g : IRSProfile.Field) (_ : g ∈ data.seeds) :
      Koala6844BenchmarkField.frobenius g = g^2130706433 := Koala6844BenchmarkField.frobenius_apply g
  have hsize : Fintype.card IRSProfile.Index ≤ 262144 := IRSProfile.card_index.le
  have hfield : (185 : ENat) < ENat.card IRSProfile.Field := by
    rw [ENat.card_eq_coe_fintype_card,Koala6844BenchmarkField.field_card]
    decide +kernel
  exact short_centered_support_bound data hσ Finset.univ (Finset.subset_univ _)
    (Finset.card_univ.trans IRSProfile.card_index) hsize hfield hpole hLead
    (hFees domain excess hexcess data hpole hLead) table hTable hTerm hRaw margins

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
