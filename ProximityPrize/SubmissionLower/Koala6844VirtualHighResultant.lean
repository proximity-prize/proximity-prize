import ProximityPrize.SubmissionLower.Koala6844Comparison



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial Koala6844BivariateSeeds
open scoped BigOperators

variable {K E : Type*} [Field K] [Field E]

theorem resultant_seed_degree_le
    (F G : Polynomial (SeedPolynomial E)) (m n a b : ℕ) (i : Fin 2)
    (hF : ∀ j, (F.coeff j).degreeOf i ≤ a)
    (hG : ∀ j, (G.coeff j).degreeOf i ≤ b) :
    (Polynomial.resultant F G m n).degreeOf i ≤ m*b+n*a := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply']
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans ?_
  apply Finset.sup_le
  intro σ _
  rw [← map_intCast (MvPolynomial.C : E →+* SeedPolynomial E)]
  refine (MvPolynomial.degreeOf_C_mul_le _ _ _).trans ?_
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  rw [Fin.sum_univ_add]
  have left : (∑ j : Fin m,
      ((Polynomial.sylvester F G m n) (σ (Fin.castAdd n j)) (Fin.castAdd n j)).degreeOf i) ≤
      m * b := by
    calc
      _ ≤ ∑ _j : Fin m, b := by
        apply Finset.sum_le_sum
        intro j _
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        split
        · exact hG _
        · simp
      _ = _ := by simp
  have right : (∑ j : Fin n,
      ((Polynomial.sylvester F G m n) (σ (Fin.natAdd m j)) (Fin.natAdd m j)).degreeOf i) ≤
      n * a := by
    calc
      _ ≤ ∑ _j : Fin n, a := by
        apply Finset.sum_le_sum
        intro j _
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        split
        · exact hF _
        · simp
      _ = _ := by simp
  exact Nat.add_le_add left right

private theorem resultant_eval_zero (F G : Polynomial (SeedPolynomial E)) (m n : ℕ)
    (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) (hpos : m ≠ 0 ∨ n ≠ 0)
    (z : Fin 2 → E) (v : E)
    (hf : F.eval₂ (MvPolynomial.eval z) v = 0)
    (hg : G.eval₂ (MvPolynomial.eval z) v = 0) :
    MvPolynomial.eval z (Polynomial.resultant F G m n) = 0 := by
  obtain ⟨U,V,_,_,h⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant F G hF hG hpos
  have he := congrArg (fun P : Polynomial (SeedPolynomial E) =>
    P.eval₂ (MvPolynomial.eval z) v) h
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    hf, hg, zero_mul, mul_zero, zero_add] using he.symm

theorem card_le_of_resolved_pair (embed : K →+* E) (p : ℕ)
    (F G : Polynomial (SeedPolynomial E))
    (hirr : Irreducible F) (hpos : 0 < F.natDegree) (hproper : ¬ F ∣ G)
    (a b : Fin 2 → ℕ)
    (hF : ∀ j i, (F.coeff j).degreeOf i ≤ a i)
    (hG : ∀ j i, (G.coeff j).degreeOf i ≤ b i)
    (hsmall : F.natDegree*b 0 + G.natDegree*a 0 < p)
    (seeds : Finset K) (values : K → E)
    (hf : ∀ g ∈ seeds, F.eval₂ (MvPolynomial.eval
      (coordinates (embed g) ((embed g)^p))) (values g) = 0)
    (hg : ∀ g ∈ seeds, G.eval₂ (MvPolynomial.eval
      (coordinates (embed g) ((embed g)^p))) (values g) = 0) :
    seeds.card ≤ F.natDegree*b 0 + G.natDegree*a 0 +
      p * (F.natDegree*b 1 + G.natDegree*a 1) := by
  classical
  let m := F.natDegree
  let n := G.natDegree
  let R := Polynomial.resultant F G m n
  let cap (i : Fin 2) := m*b i + n*a i
  have hr : R ≠ 0 := RCN290.irreducible_resultant_nonzero F G hirr hpos hproper
  have hdegree (i : Fin 2) : R.degreeOf i ≤ cap i :=
    resultant_seed_degree_le F G m n (a i) (b i) i (fun j => hF j i) (fun j => hG j i)
  have hzero (t : E) (ht : t ∈ seeds.image embed) :
      MvPolynomial.eval (coordinates t (t^p)) R = 0 := by
    obtain ⟨g,hgmem,rfl⟩ := Finset.mem_image.mp ht
    exact resultant_eval_zero F G m n le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpos))
      _ (values g) (hf g hgmem) (hg g hgmem)
  have hcount := card_le_of_vanishing
    (b := cap 0 + 1) (c := cap 1 + 1)
    (Nat.zero_lt_of_lt hsmall) (Nat.succ_le_of_lt hsmall) hr
    ((hdegree 0).trans_lt (Nat.lt_succ_self _))
    ((hdegree 1).trans_lt (Nat.lt_succ_self _))
    (seeds.image embed) hzero
  rw [Finset.card_image_of_injective _ embed.injective] at hcount
  simpa only [Nat.add_sub_cancel, cap, m, n] using hcount

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
