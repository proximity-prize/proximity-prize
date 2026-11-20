/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Fixed scalar-polynomial to RS codewords conversion adapted from the accepted
68.32 pilot of Bome2017. The selected-no-large-pencil reduction follows
Lucieno's PR 618 and earlier public Proximity Prize reductions. -/
import ProximityPrize.SubmissionLower.Mid6833RetunedScalar
import ProximityPrize.SubmissionLower.Mid6833RetunedProtocol

namespace ProximityPrize.SubmissionLower.RetunedPrice6969
open ProximityPrize.Benchmark
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
local instance mid6833Local_RetunedReduction_12  : DecidableEq IRSProfile.Field := Classical.decEq _
local instance mid6833Local_RetunedReduction_13  : DecidableEq IRSProfile.Index := Classical.decEq _

theorem fixed_scalar_words : ScalarListBound 58903920380032069 := by
  classical
  intro received L hcode hclose
  let codeword (c : ↥L) : IRSProfile.baseCode := ⟨c.1,hcode c.1 c.2⟩
  let selected (c : ↥L) : Polynomial IRSProfile.Field := ReedSolomon.toPolynomial (codeword c)
  let Γ := Finset.univ.image selected
  have hinj : Function.Injective selected := by
    intro c d h
    apply Subtype.ext
    funext i
    have hval := congrArg (fun P : Polynomial IRSProfile.Field => P.eval (IRSProfile.domain i)) h
    exact ReedSolomon.toPolynomial_eval_at_domain.symm.trans
      (hval.trans ReedSolomon.toPolynomial_eval_at_domain)
  have hc : Γ.card = L.card := by
    simp [Γ,Finset.card_image_of_injective _ hinj]
  have sub : (Γ : Set (Polynomial IRSProfile.Field)) ⊆
      ReedSolomon.closePolynomialSet IRSProfile.domain received 131072 179740 := by
    intro f hf
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hf
    constructor
    · exact Polynomial.mem_degreeLT.mp (ReedSolomon.toPolynomial_mem_lt_deg (codeword c))
    · have eqsf : ReedSolomon.polynomialAgreementSet IRSProfile.domain received (selected c) =
          Finset.univ.filter (fun i => c.1 i = received i) := by
        ext i
        simp only [ReedSolomon.mem_polynomialAgreementSet,Finset.mem_filter,Finset.mem_univ,true_and]
        rw [show (selected c).eval (IRSProfile.domain i) = c.1 i from
          ReedSolomon.toPolynomial_eval_at_domain (c:=codeword c) (i:=i)]
      rw [eqsf]
      simpa only [IRSProfile.card_index, errors] using hclose c.1 c.2
  have fin := (ReedSolomon.closePolynomialSet_finite_and_ncard_mul_choose_le
    IRSProfile.domain received (show 131072 ≤ 179740 by decide)).1
  have b := (Set.ncard_le_ncard sub fin).trans
    (Frontier.SeedFreeze.scalar_list_retuned IRSProfile.domain received)
  simpa [Set.ncard_coe_finset,hc] using b

/-- The sole outstanding hypothesis quantifies over every selected scalar
family in which any single degree-bounded pencil occurs at most 82405 times. -/
theorem protocol6969_of_seed_bound (seed : ScalarSeedBound) :
    ProtocolClaim 6969 337530879 1073741824 :=
  protocolClaim_6969_of_bounds seed fixed_scalar_words

#print axioms fixed_scalar_words
#print axioms protocol6969_of_seed_bound
end
end ProximityPrize.SubmissionLower.RetunedPrice6969
