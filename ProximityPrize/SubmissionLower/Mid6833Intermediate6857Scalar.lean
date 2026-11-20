/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833SeedFreeze
import ProximityPrize.SubmissionLower.Mid6833CappedWhole
import ProximityPrize.SubmissionLower.Mid6833Intermediate6857Source
namespace Frontier.SeedFreeze
open MvPolynomial PolynomialDifferential ReedSolomon
noncomputable section
local instance mid6833Local_Intermediate6857Scalar_7  : DecidableEq KoalaBear.Ext6 := Classical.decEq _
local instance mid6833Local_Intermediate6857Scalar_8  : CharP KoalaBear.Ext6 2130706433 := charP_of_injective_algebraMap' KoalaBear.Field 2130706433
private theorem all_intermediate6857 (x : Fin 262144 ↪ KoalaBear.Ext6) (u : Fin 262144 → KoalaBear.Ext6)
    (A s U L : ℕ) (agree : 131072≤A)
    (source : ∃ Q : MvPolynomial (Fin 4) KoalaBear.Ext6, Q≠0 ∧ Q.degreeOf 2≤s ∧ weightedTotalDegree wt Q≤U ∧ weightedTotalDegree jetIndexWt Q≤12 ∧
      ∀ f : Polynomial KoalaBear.Ext6, f.natDegree≤131071 → ∀ S : Finset (Fin 262144), A≤S.card →
        (∀ i∈S, f.eval (x i)=u i) → differentialSpecialization (rename slot Q) f=0)
    (count : ∀ (Γ : Finset (Polynomial KoalaBear.Ext6)) (Q : MvPolynomial (Fin 4) KoalaBear.Ext6),
      Q≠0 → Q.degreeOf 2≤s → weightedTotalDegree wt Q≤U → weightedTotalDegree jetIndexWt Q≤12 →
      (∀ f∈Γ, f∈closePolynomialSet x u 131072 A) →
      (∀ f∈Γ, differentialSpecialization (rename slot Q) f=0) → Γ.card≤L) :
    (closePolynomialSet x u 131072 A).ncard ≤ L := by
  classical
  let S := closePolynomialSet x u 131072 A
  have hf : S.Finite := (closePolynomialSet_finite_and_ncard_mul_choose_le x u agree).1
  change S.ncard ≤ _
  rw [Set.ncard_eq_toFinset_card _ hf]
  obtain ⟨Q,hq,ht,hu,hi,van⟩ := source
  apply count _ Q hq ht hu hi (fun f h => hf.mem_toFinset.mp h)
  intro f h
  have mem : f∈closePolynomialSet x u 131072 A := hf.mem_toFinset.mp h
  apply van f _ (polynomialAgreementSet x u f) mem.2
  · intro i hi
    exact (mem_polynomialAgreementSet x u f i).mp hi
  · by_cases hz : f=0
    · simp [hz]
    · have hd : f.natDegree < 131072 := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr mem.1
      omega

theorem scalar_list_intermediate6857
    (x : Fin 262144 ↪ KoalaBear.Ext6) (u : Fin 262144 → KoalaBear.Ext6) :
    (closePolynomialSet x u 131072 180833).ncard ≤ 5666707449348552 := by
  apply all_intermediate6857 x u 180833 5 41 _ (by decide)
  · obtain ⟨Q,hQ,ht,hw,hi,hvan⟩ := intermediate6857_index (by simp) x u
    exact ⟨Q,hQ,ht,hw,hi,fun f hf S hsize => hvan f hf S (by omega)⟩
  · intro Γ Q hQ ht hw hi hclose hvan
    have ch : max (131072-1) ((2*5-1)*41) < ringChar KoalaBear.Ext6 := by
      rw [ringChar.eq KoalaBear.Ext6 2130706433]
      decide
    have b := KoalaFactorResultant.capped_whole (p:=2130706433) (V:=12) (τ:=262137) (c:=2752441) (a:=1376220) (b:=10485481) (by decide) (by decide)
      (by decide) (by decide) (by decide) ch (fun l => by have := l.isLt; change 2*(l.val-2)-1 ≤ 262137; omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) Q hQ ht hw hi x u Γ hclose hvan
    have hu : (Γ.card : ℚ) < 5666707449348553 := b.trans_lt (by decide +kernel)
    have hl : Γ.card < 5666707449348553 := by exact_mod_cast hu
    omega

#print axioms scalar_list_intermediate6857
end
end Frontier.SeedFreeze
