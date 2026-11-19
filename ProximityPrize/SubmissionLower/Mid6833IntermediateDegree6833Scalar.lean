/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833SeedFreeze
import ProximityPrize.SubmissionLower.Mid6833CappedWhole
import ProximityPrize.SubmissionLower.Mid6833IntermediateDegree6833Source
namespace Frontier.SeedFreeze
open MvPolynomial PolynomialDifferential ReedSolomon
noncomputable section
local instance mid6833Local_IntermediateDegree6833Scalar_7  : DecidableEq KoalaBear.Ext6 := Classical.decEq _
local instance mid6833Local_IntermediateDegree6833Scalar_8  : CharP KoalaBear.Ext6 2130706433 := charP_of_injective_algebraMap' KoalaBear.Field 2130706433
private theorem all_intermediatedegree6833 (x : Fin 262144 ↪ KoalaBear.Ext6) (u : Fin 262144 → KoalaBear.Ext6)
    (A s U L : ℕ) (agree : 133294≤A)
    (source : ∃ Q : MvPolynomial (Fin 4) KoalaBear.Ext6, Q≠0 ∧ Q.degreeOf 2≤s ∧ weightedTotalDegree wt Q≤U ∧ weightedTotalDegree jetIndexWt Q≤41 ∧
      ∀ f : Polynomial KoalaBear.Ext6, f.natDegree≤133293 → ∀ S : Finset (Fin 262144), A≤S.card →
        (∀ i∈S, f.eval (x i)=u i) → differentialSpecialization (rename slot Q) f=0)
    (count : ∀ (Γ : Finset (Polynomial KoalaBear.Ext6)) (Q : MvPolynomial (Fin 4) KoalaBear.Ext6),
      Q≠0 → Q.degreeOf 2≤s → weightedTotalDegree wt Q≤U → weightedTotalDegree jetIndexWt Q≤41 →
      (∀ f∈Γ, f∈closePolynomialSet x u 133294 A) →
      (∀ f∈Γ, differentialSpecialization (rename slot Q) f=0) → Γ.card≤L) :
    (closePolynomialSet x u 133294 A).ncard ≤ L := by
  classical
  let S := closePolynomialSet x u 133294 A
  have hf : S.Finite := (closePolynomialSet_finite_and_ncard_mul_choose_le x u agree).1
  change S.ncard ≤ _
  rw [Set.ncard_eq_toFinset_card _ hf]
  obtain ⟨Q,hq,ht,hu,hi,van⟩ := source
  apply count _ Q hq ht hu hi (fun f h => hf.mem_toFinset.mp h)
  intro f h
  have mem : f∈closePolynomialSet x u 133294 A := hf.mem_toFinset.mp h
  apply van f _ (polynomialAgreementSet x u f) mem.2
  · intro i hi
    exact (mem_polynomialAgreementSet x u f i).mp hi
  · by_cases hz : f=0
    · simp [hz]
    · have hd : f.natDegree < 133294 := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr mem.1
      omega

theorem scalar_list_intermediatedegree6833
    (x : Fin 262144 ↪ KoalaBear.Ext6) (u : Fin 262144 → KoalaBear.Ext6) :
    (closePolynomialSet x u 133294 181049).ncard ≤ 274460153320229089 := by
  apply all_intermediatedegree6833 x u 181049 19 134 _ (by decide)
  · obtain ⟨Q,hQ,ht,hw,hi,hvan⟩ := intermediatedegree6833_index (by simp) x u
    exact ⟨Q,hQ,ht,hw,hi,fun f hf S hsize => hvan f hf S (by omega)⟩
  · intro Γ Q hQ ht hw hi hclose hvan
    have ch : max (133294-1) ((2*19-1)*134) < ringChar KoalaBear.Ext6 := by
      rw [ringChar.eq KoalaBear.Ext6 2130706433]
      decide
    have b := KoalaFactorResultant.capped_whole (p:=2130706433) (V:=41) (τ:=266581) (c:=10529952) (a:=5264976) (b:=35455274) (by decide) (by decide)
      (by decide) (by decide) (by decide) ch (fun l => by have := l.isLt; change 2*(l.val-2)-1 ≤ 266581; omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) Q hQ ht hw hi x u Γ hclose hvan
    have hu : (Γ.card : ℚ) < 274460153320229090 := b.trans_lt (by decide +kernel)
    have hl : Γ.card < 274460153320229090 := by exact_mod_cast hu
    omega

#print axioms scalar_list_intermediatedegree6833
end
end Frontier.SeedFreeze
