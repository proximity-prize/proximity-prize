/- Finite-codeword transport adapted from Bome2017's 68.33 submission,
commit 79fd79818edcb4a3b6e0f4b8c336b7d92f232c17. Apache-2.0. -/
import ProximityPrize.Benchmark.TargetLower
import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList

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

end
end ProximityPrize.SubmissionLower.IntermediateScalar
