import ProximityPrize.SubmissionLower.Final50Order

set_option autoImplicit false
set_option Elab.async false

namespace KoalaWeightedCofactor
noncomputable section

open K1_13 (Geom)
open K1_13_3 (Symbol symbolIndex)
open MvPolynomial
open scoped BigOperators
open private index_eq_weighted weighted_pow from ProximityPrize.SubmissionLower.Fast070

theorem width_weight (w : Fin 4 → ℕ) (c : ℕ) (hw : ∀ i, c ≤ w i) (P : Symbol) :
    c*P.totalDegree≤P.weightedTotalDegree w:=by
  by_cases hP:P=0
  · simp [hP,totalDegree_zero,weightedTotalDegree]
  have hne:=support_nonempty.mpr hP
  obtain ⟨m,hm,he⟩:=Finset.exists_mem_eq_sup _ hne (fun m => m.weight (1:Fin 4→ℕ))
  have hconst : m.weight (fun _ : Fin 4 => c) = c * m.weight (1 : Fin 4 → ℕ) := by
    simp only [Finsupp.weight_eq_sum,Finset.sum_mul,Pi.one_apply,smul_eq_mul,mul_one,Nat.mul_comm c]
  have hm' : m.weight (fun _ : Fin 4 => c) ≤ m.weight w := by
    simp only [Finsupp.weight_eq_sum,smul_eq_mul]
    exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hw i)
  rw [← weightedTotalDegree_one,weightedTotalDegree,he, ← hconst]
  exact hm'.trans (le_weightedTotalDegree w hm)

/-- Dividing an independent symbol family by a common nonzero product preserves
independence and debits the width, index, and any selected jet weight. -/
theorem cofactor_weight {n r : ℕ} (w : Fin 4 → ℕ) (c C : ℕ) (hw : ∀ i, c ≤ w i)
    (F:Fin n→Symbol) (a:Fin n→ℕ) (hF : ∀ i,F i≠0)
    (e:Fin r→Symbol) (hi:LinearIndependent Geom e)
    (hcap : ∀ i, (e i).totalDegree ≤ 4012 ∧ symbolIndex (e i) ≤ 1650 ∧
      (e i).weightedTotalDegree w≤C ∧ (∏ j,F j ^ a j) ∣ e i) :
    ∃ Q : Fin r → Symbol, LinearIndependent Geom Q ∧ ∀ i,
      (∑ j,a j*(F j).totalDegree)+(Q i).totalDegree≤4012 ∧
      (∑ j,a j*symbolIndex (F j))+symbolIndex (Q i)≤1650 ∧
      c*(∑ j,a j*(F j).totalDegree)+(Q i).weightedTotalDegree w≤C:=by
  classical
  let P := ∏ j,F j ^ a j
  have hP:P≠0:=Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hF i)
  have hdeg (v : Fin 4 → ℕ) : P.weightedTotalDegree v =
      ∑ i,a i*(F i).weightedTotalDegree v:=by
    rw [MvPolynomial.weightedTotalDegree_prod v Finset.univ _ (fun i _ => pow_ne_zero _ (hF i))]
    exact Finset.sum_congr rfl fun i _ => weighted_pow v (F i) (hF i) (a i)
  have hb : P.totalDegree = ∑ j, a j * (F j).totalDegree := by
    simpa only [weightedTotalDegree_one] using hdeg (1:Fin 4→ℕ)
  have hj : symbolIndex P = ∑ j, a j * symbolIndex (F j) := by
    simpa only [index_eq_weighted] using hdeg Fin.val
  have hwP:=width_weight w c hw P
  rw [hb] at hwP
  choose Q hQ using fun i => (hcap i).2.2.2
  have hn (i : Fin r) : Q i ≠ 0 := by
    intro hz
    exact hi.ne_zero i (by rw [hQ i,hz,mul_zero])
  refine ⟨Q, ?_, ?_⟩
  · apply LinearIndependent.of_comp (LinearMap.mulLeft Geom P)
    have he:(LinearMap.mulLeft Geom P) ∘ Q=e:=funext fun i => (hQ i).symm
    rwa [he]
  · intro i
    obtain ⟨hb', hj', hw', _⟩:=hcap i
    rw [hQ i,totalDegree_mul_of_isDomain hP (hn i),hb] at hb'
    rw [hQ i, index_eq_weighted, weightedTotalDegree_mul _ _ _ hP (hn i),
      ← index_eq_weighted, ← index_eq_weighted,hj] at hj'
    rw [hQ i,weightedTotalDegree_mul _ _ _ hP (hn i)] at hw'
    exact ⟨hb', hj', (Nat.add_le_add_right hwP _).trans hw'⟩

#print axioms cofactor_weight
end
end KoalaWeightedCofactor
