import ProximityPrize.SubmissionLower.StructuralListDefs
import ProximityPrize.SubmissionLower.StructuralListPrice


namespace StructuralList

open CJ0 Finset Polynomial
open private occupancy from ProximityPrize.SubmissionLower.Fast055

noncomputable section

/-- Positions at which every polynomial in the finite family agrees with the word. -/
def commonSites (w : Node → K) (T : Finset K[X]) : Finset Node :=
  univ.filter fun i => ∀ f ∈ T, f.eval (node i) = w i

theorem mem_commonSites {w : Node → K} {T : Finset K[X]} {i : Node} :
    i ∈ commonSites w T ↔ ∀ f ∈ T, f.eval (node i) = w i := by
  simp [commonSites]

theorem commonSites_card_le {A w} {T : Finset K[X]}
    (hT : (T : Set K[X]) ⊆ close A w) (hsize : 1 < T.card) :
    (commonSites w T).card ≤ N := by
  obtain ⟨f, hf, g, hg, hfg⟩ := one_lt_card.mp hsize
  have hdeg {P : K[X]} (hP : P ∈ T) : P.natDegree ≤ N := by
    by_cases hz : P = 0
    · simp [hz, N]
    · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hz).2 (hT hP).1)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node node.injective (f - g)
    (sub_ne_zero.mpr hfg) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (hdeg hf) (hdeg hg)))
  intro i hi
  change (f-g).eval (node i) = 0
  rw [eval_sub, mem_commonSites.mp hi f hf, mem_commonSites.mp hi g hg, sub_self]

theorem firstMoment {A w} {T : Finset K[X]}
    (hT : (T : Set K[X]) ⊆ close A w) (hS : (commonSites w T).card ≤ A)
    (cap : ℚ) (hcap : ∀ i ∉ commonSites w T,
      ((T.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ cap) :
    ((A - (commonSites w T).card : ℕ) : ℚ) * T.card ≤
      ((n - (commonSites w T).card : ℕ) : ℚ) * cap := by
  classical
  let S := commonSites w T
  let candidates := (univ : Finset Node) \ S
  let hits := fun f : K[X] => univ.filter fun i : Node => f.eval (node i) = w i
  let occ := fun i : Node => (T.filter fun f => f.eval (node i) = w i).card
  have hcard : candidates.card = n - S.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, ProximityPrize.Benchmark.IRSProfile.card_index]
  have hnew (f : K[X]) (hf : f ∈ T) : A - S.card ≤ (hits f \ S).card := by
    have hsub : S ⊆ hits f := fun i hi => mem_filter.mpr ⟨mem_univ _, mem_commonSites.mp hi f hf⟩
    exact (Nat.sub_le_sub_right (hT hf).2 _).trans_eq (card_sdiff_of_subset hsub).symm
  have hsum : ∑ i ∈ candidates, occ i = ∑ f ∈ T, (hits f \ S).card := by
    simp only [occ, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun f _ => ?_
    rw [sum_boole, Nat.cast_id]
    have eqSet : (candidates.filter fun i => f.eval (node i) = w i) = hits f \ S := by
      ext i
      simp [candidates, hits, and_comm]
    rw [eqSet]
  have lower : T.card * (A - S.card) ≤ ∑ i ∈ candidates, occ i := by
    rw [hsum]
    calc
      _ = ∑ f ∈ T, (A - S.card) := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum hnew
  have hlower : (T.card : ℚ) * (A - S.card : ℕ) ≤ ∑ i ∈ candidates, (occ i : ℚ) := by
    exact_mod_cast lower
  calc
    _ = (T.card : ℚ) * (A - S.card : ℕ) := mul_comm _ _
    _ ≤ _ := hlower
    _ ≤ ∑ i ∈ candidates, cap := sum_le_sum fun i hi => hcap i (mem_sdiff.mp hi).2
    _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]

end

end StructuralList
