/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833SingularOnly
import ProximityPrize.SubmissionLower.Mid6833MovingQuotient
import ProximityPrize.SubmissionLower.Mid6833HeadroomScalar

namespace ProximityPrize.SubmissionLower.K6969Global
open Koala6831Comparison Koala6831Separation
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet eval_eq_of_mem_agreementSet badNodes)
open Koala6831BenchmarkField (prime)
open Polynomial ReedSolomon Finset
open scoped Classical Polynomial
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
abbrev K := KoalaBear.Ext6
abbrev I := Fin 262144

local instance : DecidableEq KoalaBear.Ext6 := Classical.decEq _
private theorem list_count (x : I ↪ K) (E : Finset K)
    (ag : K → Finset I) (A : ∀ g∈E, 179740≤(ag g).card)
    (T : E ↪ K[X]) (word : I → K)
    (valid : ∀ g : E, (T g).natDegree≤131543 ∧ ∀ i∈ag g, (T g).eval (x i)=word i) :
    E.card ≤ 214887237245589756 := by
  classical
  let L := closePolynomialSet x word 131544 179740
  have hf : L.Finite := (closePolynomialSet_finite_and_ncard_mul_choose_le x word (show 131544≤179740 by decide)).1
  have sub : (Finset.univ.map T) ⊆ hf.toFinset := by
    intro z hz
    obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hz
    apply hf.mem_toFinset.mpr
    refine ⟨(Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (valid g).1)),
      (A g g.property).trans (Finset.card_le_card ?_)⟩
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(valid g).2 i hi⟩
  have bound := Frontier.SeedFreeze.scalar_list_headroom x word
  change L.ncard ≤ _ at bound
  rw [Set.ncard_eq_toFinset_card _ hf] at bound
  have p := (Finset.card_le_card sub).trans bound
  rw [Finset.card_map,Finset.card_univ,Fintype.card_coe] at p
  exact p

/-- Actual benchmark class of singular rows satisfying a moving determinant
nondivisibility and the relative-degree saving condition. Includes BOTH cleanups. -/
theorem moving_determinant_class (x : I ↪ K) (σ : K →+* K)
    (hpow : ∀ g, σ g=g^prime)
    (U : Received K I) (E : Finset K) (P : SelectionMap K) (q : SymbolicRow (SeedRing K))
    (h : RetainedComparison x σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (nondiv : (¬ N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0) ∨ (¬ N.d₁ ∣ N.B 0*N.D 1-N.B 1*N.D 0) ∨ ¬ IsCoprime N.d₀ N.d₁)
    (save : primitiveExcess 131071 q≤pairDegree N.A+pairDegree N.B+472) :
    E.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1) ≤ budget := by
  classical
  let δ := primitiveExcess 131071 q
  let nodes := (Finset.univ : Finset I) \ badNodes x σ U q
  have hn : nodes.card≤262144 := (Finset.card_le_card (Finset.subset_univ nodes)).trans (by rw [Finset.card_univ,Fintype.card_fin])
  have hδ : δ≤33735 := (Nat.le_add_right _ _).trans h.excess_bad
  have gd : ∀ i∈nodes, q.atNode (MvPolynomial.C (x i)) (Koala6831SeparationFactors.affine 0 (U 0 i) (U 1 i))
      (Koala6831SeparationFactors.affine 1 (σ (U 0 i)) (σ (U 1 i)))=0 := by
    intro i hi
    have orig := Koala6831BenchmarkResidual.good_node_identity (Finset.mem_sdiff.mp hi).2
    simpa only [Koala6831SeparationFactors.affine,mul_comm] using orig
  obtain ⟨S,sub,card,T,word,fit⟩ := _root_.Frontier6969.Moving.normalized_embedding (p:=prime) N σ
    (by change δ<2130706433; omega) nodes x (U 0) (U 1) gd E P h.selection.degree_le
    (fun g hg => (h.good g hg).1) hpow h.primitive nondiv
  have bound := list_count x S (agreementSet x U P) (fun g hg => h.selection.agreement g (sub hg))
    T word (by
      intro g
      obtain ⟨deg,hfit⟩ := fit g
      refine ⟨deg.trans (by omega),?_⟩
      intro i hi
      have ng : i∉badNodes x σ U q := fun hb => (Finset.disjoint_left.mp (h.good g (sub g.property)).2) hi hb
      exact hfit i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ng⟩) (eval_eq_of_mem_agreementSet hi))
  change E.card ≤ S.card+(nodes.card+2+(prime+1)*δ) at card
  change E.card+(33735-δ+1)*6*(prime+1)≤budget
  unfold budget prime at *
  omega

#print axioms list_count
#print axioms moving_determinant_class
end
end ProximityPrize.SubmissionLower.K6969Global
