import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingSeedless6732Research
import ProximityPrize.SubmissionLower.ContactSeedlessRankResearch
import ProximityPrize.SubmissionLower.ContactSeedlessPrimeIncidenceResearch
import ProximityPrize.SubmissionLower.ContactSeedlessProperCutResearch
import ProximityPrize.SubmissionLower.ContactSeedlessListBoundResearch

namespace ProximityPrize.SubmissionLower.ContactMovingSeedlessGeometry6732Research

open ProximityPrize.Benchmark
open ContactMovingSeedless6732Research
open ContactSeedlessRankResearch
open ContactSeedlessPrimeIncidenceResearch
open ContactSeedlessProperCutResearch
open ContactSeedlessListBoundResearch

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

def errors : ℕ := 80092

theorem irs_scalar_finite_list_card_le
    (received : IRSProfile.Index → IRSProfile.Field)
    (L : Finset (IRSProfile.Index → IRSProfile.Field))
    (hcode : ∀ c ∈ L, c ∈ IRSProfile.baseCode)
    (hnear : ∀ c ∈ L, agreements ≤
      (Finset.univ.filter (fun i => c i = received i)).card) :
    L.card ≤ listBudget := by
  have hprime : Nat.Prime prime := by
    simpa [prime, ContactParameters6600Research.prime] using
      ContactFrozenAlignment6600Research.challenge_field_prime
  have hchar : CharP IRSProfile.Field prime := by
    simpa [prime, ContactParameters6600Research.prime] using
      ContactFrozenAlignment6600Research.challenge_field_characteristic6600
  have hcard : Fintype.card IRSProfile.Field = prime ^ 6 := by
    simpa [prime, ContactParameters6600Research.prime] using
      ContactFrozenAlignment6600Research.challenge_field_card6600
  have hdom : IRSProfile.domain.injective := IRSProfile.domain.injective
  have hdeg : IRSProfile.baseDimension ≤ w + 1 := by
    norm_num [IRSProfile.baseDimension, w]
  have hcardDom : Fintype.card IRSProfile.Index = n := by
    norm_num [IRSProfile.Index, n]
  have hle : L.card ≤ listNumerator / gap + 1 :=
    seedless_list_size_le IRSProfile.Field IRSProfile.Index
      IRSProfile.baseCode IRSProfile.domain received L
      n w errors multiplicity yTotalCap slopeCap
      agreements gap prime capY capR regularListNumerator singularListCap listNumerator
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hprime hchar hcard hdom hcardDom hdeg
      characteristic_gates.1 characteristic_gates.2.1 characteristic_gates.2.2.1
      characteristic_gates.2.2.2.1 characteristic_gates.2.2.2.2
      list_numeric_values.1 list_numeric_values.2.1 list_numeric_values.2.2.1
      list_numeric_values.2.2.2.1 list_numeric_values.2.2.2.2.1
      exists_seedless_interpolant
      hcode hnear
  have hfit := list_numeric_values.2.2.2.2.2.1
  have hbud := list_numeric_values.2.2.2.2.2.2.2
  omega

end ProximityPrize.SubmissionLower.ContactMovingSeedlessGeometry6732Research
