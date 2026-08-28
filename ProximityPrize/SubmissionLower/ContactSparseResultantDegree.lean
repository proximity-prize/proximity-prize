import ProximityPrize.SubmissionLower.BCHKSResultantDegree

/-!
# Trapezoidal-support degree bound for a bivariate resultant

This is the arithmetic core needed to retain the joint `Y + Z` support
constraint in the contact projection.  The ordinary rectangular bound loses
the `n*m` diagonal saving.  In every nonzero Sylvester determinant term, the
sum of the chosen coefficient indices is exactly `n*m`; coefficientwise total
degree caps therefore recover that saving.
-/

namespace ProximityPrize.SubmissionLower.ContactSparseResultantDegree

open Polynomial Polynomial.Bivariate Matrix
open scoped BigOperators

variable {F : Type} [Field F]

/-- If the `k`th outer coefficient has inner degree plus `k` bounded by a
joint cap, the resultant retains both joint caps. -/
theorem bivariate_resultant_natDegree_add_mul_le
    (B A : F[X][Y]) (n m LB LA : ℕ)
    (hmLA : m ≤ LA) (hnLB : n ≤ LB)
    (hA : ∀ k, k ≤ m → (A.coeff k).natDegree + k ≤ LA)
    (hB : ∀ k, k ≤ n → (B.coeff k).natDegree + k ≤ LB) :
    (Polynomial.resultant B A n m).natDegree + n * m ≤
      m * LB + n * LA := by
  classical
  let M : Matrix (Fin (n + m)) (Fin (n + m)) F[X] :=
    Polynomial.sylvester B A n m
  let offset : Fin (n + m) → ℕ :=
    Fin.addCases (fun i : Fin n => i.val) (fun i : Fin m => i.val)
  have hcross :
      (∑ i : Fin (n + m), i.val) =
        (∑ i : Fin n, i.val) + (∑ i : Fin m, i.val) + n * m := by
    rw [Fin.sum_univ_add]
    simp only [Fin.val_castAdd, Fin.val_natAdd, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hoffset :
      (∑ i : Fin (n + m), offset i) =
        (∑ i : Fin n, i.val) + (∑ i : Fin m, i.val) := by
    rw [Fin.sum_univ_add]
    simp [offset]
  have h_term (σ : Equiv.Perm (Fin (n + m))) :
      (Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i).natDegree + n * m ≤
        m * LB + n * LA := by
    by_cases hz : (∏ i : Fin (n + m), M (σ i) i) = 0
    · simp only [hz, smul_zero, natDegree_zero, zero_add]
      exact (Nat.mul_le_mul_left n hmLA).trans (Nat.le_add_left _ _)
    · have hentry_ne : ∀ i : Fin (n + m), M (σ i) i ≠ 0 := by
        intro i
        exact (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
      let index : Fin (n + m) → ℕ := fun i => (σ i).val - offset i
      have hinterval : ∀ i : Fin (n + m),
          offset i ≤ (σ i).val ∧
            (σ i).val ≤ offset i + (Fin.addCases (fun _ : Fin n => m)
              (fun _ : Fin m => n) i) := by
        intro i
        refine Fin.addCases (fun i0 => ?_) (fun i0 => ?_) i
        ·
            have hM : M (σ (.castAdd m i0)) (.castAdd m i0) =
                if ((σ (.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m))
                then A.coeff ((σ (.castAdd m i0) : ℕ) - i0) else 0 := by
              simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
            by_cases h : (σ (.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m)
            · simpa [offset] using h
            · have := hentry_ne (.castAdd m i0)
              simp [hM, h] at this
        ·
            have hM : M (σ (.natAdd n i0)) (.natAdd n i0) =
                if ((σ (.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n))
                then B.coeff ((σ (.natAdd n i0) : ℕ) - i0) else 0 := by
              simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
            by_cases h : (σ (.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n)
            · simpa [offset] using h
            · have := hentry_ne (.natAdd n i0)
              simp [hM, h] at this
      have hindex_offset (i : Fin (n + m)) :
          index i + offset i = (σ i).val := by
        have hi := (hinterval i).1
        dsimp [index]
        omega
      have hindex_sum : (∑ i : Fin (n + m), index i) = n * m := by
        have hperm : (∑ i : Fin (n + m), (σ i).val) =
            ∑ i : Fin (n + m), i.val := Equiv.sum_comp σ (fun i => i.val)
        have hadd : (∑ i : Fin (n + m), (index i + offset i)) =
            ∑ i : Fin (n + m), (σ i).val := by
          apply Fintype.sum_congr
          intro i
          exact hindex_offset i
        rw [Finset.sum_add_distrib, hoffset, hperm, hcross] at hadd
        omega
      have h_entry (i : Fin (n + m)) :
          (M (σ i) i).natDegree + index i ≤
            Fin.addCases (fun _ : Fin n => LA) (fun _ : Fin m => LB) i := by
        refine Fin.addCases (fun i0 => ?_) (fun i0 => ?_) i
        ·
            rcases hinterval (.castAdd m i0) with ⟨hlow, hupp⟩
            have hmem : (σ (.castAdd m i0) : ℕ) ∈
                Set.Icc (i0 : ℕ) ((i0 : ℕ) + m) := by
              simpa [offset] using And.intro hlow hupp
            have hM : M (σ (.castAdd m i0)) (.castAdd m i0) =
                A.coeff ((σ (.castAdd m i0) : ℕ) - i0) := by
              rw [show M (σ (.castAdd m i0)) (.castAdd m i0) =
                  if ((σ (.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m))
                  then A.coeff ((σ (.castAdd m i0) : ℕ) - i0) else 0 by
                simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]]
              exact if_pos hmem
            have hidx : (σ (.castAdd m i0) : ℕ) - (i0 : ℕ) ≤ m := by
              apply (Nat.sub_le_iff_le_add).2
              simpa [Nat.add_comm] using hmem.2
            simpa [hM, index, offset] using
              hA ((σ (.castAdd m i0) : ℕ) - i0) hidx
        ·
            rcases hinterval (.natAdd n i0) with ⟨hlow, hupp⟩
            have hmem : (σ (.natAdd n i0) : ℕ) ∈
                Set.Icc (i0 : ℕ) ((i0 : ℕ) + n) := by
              simpa [offset] using And.intro hlow hupp
            have hM : M (σ (.natAdd n i0)) (.natAdd n i0) =
                B.coeff ((σ (.natAdd n i0) : ℕ) - i0) := by
              rw [show M (σ (.natAdd n i0)) (.natAdd n i0) =
                  if ((σ (.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n))
                  then B.coeff ((σ (.natAdd n i0) : ℕ) - i0) else 0 by
                simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]]
              exact if_pos hmem
            have hidx : (σ (.natAdd n i0) : ℕ) - (i0 : ℕ) ≤ n := by
              apply (Nat.sub_le_iff_le_add).2
              simpa [Nat.add_comm] using hmem.2
            simpa [hM, index, offset] using
              hB ((σ (.natAdd n i0) : ℕ) - i0) hidx
      have hprod : (∏ i : Fin (n + m), M (σ i) i).natDegree ≤
          ∑ i : Fin (n + m), (M (σ i) i).natDegree := by
        simpa using Polynomial.natDegree_prod_le _ (fun i => M (σ i) i)
      have hsum :
          (∑ i : Fin (n + m), ((M (σ i) i).natDegree + index i)) ≤
            n * LA + m * LB := by
        calc
          _ ≤ ∑ i : Fin (n + m),
              (Fin.addCases (fun _ : Fin n => LA) (fun _ : Fin m => LB) i) := by
            apply Finset.sum_le_sum
            intro i _
            exact h_entry i
          _ = _ := by rw [Fin.sum_univ_add]; simp
      have hcore : (∏ i : Fin (n + m), M (σ i) i).natDegree + n * m ≤
          n * LA + m * LB := by
        rw [← hindex_sum]
        calc
          _ ≤ (∑ i, (M (σ i) i).natDegree) + ∑ i, index i :=
            Nat.add_le_add_right hprod _
          _ = ∑ i, ((M (σ i) i).natDegree + index i) := by
            rw [Finset.sum_add_distrib]
          _ ≤ _ := hsum
      exact (Nat.add_le_add_right (Polynomial.natDegree_smul_le _ _) _).trans
        (by simpa [Nat.add_comm, Nat.mul_comm] using hcore)
  have hdet : M.det.natDegree + n * m ≤ m * LB + n * LA := by
    rw [Matrix.det_apply]
    have hbase : n * m ≤ m * LB + n * LA :=
      (Nat.mul_le_mul_left n hmLA).trans (Nat.le_add_left _ _)
    have hsumdeg := Polynomial.natDegree_sum_le_of_forall_le
      (Finset.univ : Finset (Equiv.Perm (Fin (n + m))))
      (fun σ => Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i)
      (fun σ _ => Nat.le_sub_of_add_le (h_term σ))
    omega
  simpa [Polynomial.resultant, M, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdet

end ProximityPrize.SubmissionLower.ContactSparseResultantDegree
