import ProximityPrize.SubmissionLower.CyclicFourFibre

namespace ProximityPrize.SubmissionLower.CyclicFourResidues

open ProximityPrize.Benchmark
open CyclicFourFibre
open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

/-- Collect the coefficients whose exponents have residue `a` modulo four,
dividing those exponents by four. -/
def residuePart {F : Type*} [Field F] (a : Fin 4) (P : Polynomial F) :
    Polynomial F :=
  P.sum fun n c =>
    if n % 4 = a then Polynomial.monomial (n / 4) c else 0

theorem eval_residuePart {F : Type*} [Field F] (a : Fin 4)
    (P : Polynomial F) (x : F) :
    (residuePart a P).eval (x ^ 4) =
      P.sum fun n c => if n % 4 = a then c * (x ^ 4) ^ (n / 4) else 0 := by
  rw [residuePart, Polynomial.eval_sum]
  simp only [Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : n % 4 = a <;> simp [h]

theorem eval_eq_sum_residuePart {F : Type*} [Field F]
    (P : Polynomial F) (x : F) :
    P.eval x = ∑ a : Fin 4, x ^ (a : ℕ) * (residuePart a P).eval (x ^ 4) := by
  rw [Polynomial.eval_eq_sum]
  simp_rw [eval_residuePart]
  simp only [Polynomial.sum_def]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  let a : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩
  rw [Fintype.sum_eq_single a]
  · simp only [a, ↓reduceIte]
    have hx : x ^ n = x ^ (n % 4) * (x ^ 4) ^ (n / 4) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [hx]
    ring
  · intro b hba
    have hne : n % 4 ≠ (b : ℕ) := by
      intro h
      apply hba
      exact Fin.ext h.symm
    simp [hne]

/-- Each residue component has half the dimension of the folded domain. -/
def componentDimension : ℕ := 2 ^ 15

theorem residuePart_natDegree_lt (a : Fin 4)
    (P : Polynomial IRSProfile.Field) (hP : P.natDegree ≤ 131071) :
    (residuePart a P).natDegree < componentDimension := by
  rw [residuePart, Polynomial.sum_def]
  refine (Polynomial.natDegree_sum_le_of_forall_le
    (s := P.support) (n := componentDimension - 1) _ ?_).trans_lt ?_
  · intro n hn
    have hnle : n ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp n hn
    have hncap : n ≤ 131071 := hnle.trans hP
    by_cases hres : n % 4 = a
    · simp only [if_pos hres]
      exact (Polynomial.natDegree_monomial_le _).trans (by
        norm_num [componentDimension]
        omega)
    · simp [hres, componentDimension]
  · norm_num [componentDimension]

/-- The common size-`2^16` evaluation domain seen after the `x ↦ x^4` fold. -/
def foldedDomain : Fin quarterSize ↪ IRSProfile.Field where
  toFun j := foldValue (rootIndex j (0 : Fin 4))
  inj' := by
    intro j k h
    change
      ((CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
        (IRSProfile.baseNttDomain.omega ^ (j : ℕ))) ^ 4 =
      ((CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
        (IRSProfile.baseNttDomain.omega ^ (k : ℕ))) ^ 4 at h
    rw [← map_pow, ← map_pow] at h
    have hbase := (CompPoly.Extension.Ext.ofBaseRingHom
      KoalaBear.ext6Params).injective h
    rw [← pow_mul, ← pow_mul] at hbase
    have hj : (j : ℕ) * 4 < 2 ^ 18 := by
      have := j.isLt
      norm_num [quarterSize] at this ⊢
      omega
    have hk : (k : ℕ) * 4 < 2 ^ 18 := by
      have := k.isLt
      norm_num [quarterSize] at this ⊢
      omega
    have hjk := IRSProfile.baseNttDomain.primitive.pow_inj hj hk hbase
    apply Fin.ext
    omega

@[simp] theorem foldedDomain_apply (j : Fin quarterSize) :
    foldedDomain j = foldValue (rootIndex j (0 : Fin 4)) := rfl

theorem eval_rootIndex_eq_residue_sum (P : Polynomial IRSProfile.Field)
    (j : Fin quarterSize) (t : Fin 4) :
    P.eval (IRSProfile.domain (rootIndex j t)) =
      ∑ a : Fin 4,
        IRSProfile.domain (rootIndex j t) ^ (a : ℕ) *
          (residuePart a P).eval (foldedDomain j) := by
  rw [eval_eq_sum_residuePart]
  apply Fintype.sum_congr
  intro a
  rw [foldedDomain_apply, ← foldValue_rootIndex j t, foldValue]

end

end ProximityPrize.SubmissionLower.CyclicFourResidues
