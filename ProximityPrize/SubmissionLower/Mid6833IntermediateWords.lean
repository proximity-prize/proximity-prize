/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833Frontier6842Scalar
import ProximityPrize.SubmissionLower.Mid6833RetunedScalar
import ProximityPrize.SubmissionLower.Mid6833Intermediate6833Scalar
import ProximityPrize.SubmissionLower.Mid6833Intermediate6857Scalar
import ProximityPrize.SubmissionLower.Mid6833Intermediate6882Scalar
import ProximityPrize.SubmissionLower.Mid6833Intermediate6900Scalar
import ProximityPrize.SubmissionLower.Mid6833Intermediate6932Scalar

namespace ProximityPrize.SubmissionLower.IntermediateScalar
open ProximityPrize.Benchmark
noncomputable section
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : DecidableEq IRSProfile.Field := Classical.decEq _

def Words (A B : ℕ) : Prop := ∀ (received : IRSProfile.Index → IRSProfile.Field)
  (L : Finset (IRSProfile.Index → IRSProfile.Field)),
  (∀ c∈L,c∈IRSProfile.baseCode) →
  (∀ c∈L,A ≤ (Finset.univ.filter (fun i => c i=received i)).card) → L.card ≤ B

theorem of_scalar {A B : ℕ} (hA : 131072 ≤ A)
  (cap : ∀ (x : Fin 262144 ↪ KoalaBear.Ext6) (u : Fin 262144 → KoalaBear.Ext6),
    (ReedSolomon.closePolynomialSet x u 131072 A).ncard ≤ B) : Words A B := by
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
      ReedSolomon.closePolynomialSet IRSProfile.domain received 131072 A := by
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
      exact hclose c.1 c.2
  have fin := (ReedSolomon.closePolynomialSet_finite_and_ncard_mul_choose_le
    IRSProfile.domain received hA).1
  have b := (Set.ncard_le_ncard sub fin).trans
    (cap IRSProfile.domain received)
  simpa [Set.ncard_coe_finset,hc] using b


theorem words_6833 : Words 181068 30294781525 := Intermediate6833Scalar.irs_scalar_finite_list_card_le
#print axioms words_6833

theorem words_6842 : Words 180980 87312511777 := Frontier6842Scalar.irs_scalar_finite_list_card_le
#print axioms words_6842

theorem words_6857 : Words 180833 5666707449348552 := of_scalar (by decide) Frontier.SeedFreeze.scalar_list_intermediate6857
#print axioms words_6857

theorem words_6882 : Words 180589 8554486492569142 := of_scalar (by decide) Frontier.SeedFreeze.scalar_list_intermediate6882
#print axioms words_6882

theorem words_6900 : Words 180413 11753781584167015 := of_scalar (by decide) Frontier.SeedFreeze.scalar_list_intermediate6900
#print axioms words_6900

theorem words_6932 : Words 180100 23613711572114596 := of_scalar (by decide) Frontier.SeedFreeze.scalar_list_intermediate6932
#print axioms words_6932

theorem words_6969 : Words 179740 58903920380032069 := of_scalar (by decide) Frontier.SeedFreeze.scalar_list_retuned
#print axioms words_6969
end
end ProximityPrize.SubmissionLower.IntermediateScalar
