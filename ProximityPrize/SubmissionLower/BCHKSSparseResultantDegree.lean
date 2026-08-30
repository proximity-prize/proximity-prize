import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate Matrix
open scoped BigOperators

variable {F : Type} [Field F]

private theorem natDegree_det_le_of_perm_products_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F[X]) {N : ℕ}
    (h : ∀ σ : Equiv.Perm ι, (∏ i : ι, M (σ i) i).natDegree ≤ N) :
    M.det.natDegree ≤ N := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  exact (Polynomial.natDegree_C_mul_le
    ((Equiv.Perm.sign σ : ℤ) : F) (∏ i : ι, M (σ i) i)).trans (h σ)

theorem bivariate_resultant_natDegree_le_totalDegree
    (B H : F[X][Y]) (n m : ℕ) :
    (Polynomial.resultant B H n m).natDegree ≤
      m * totalDegree B + n * totalDegree H - m * n := by
  classical
  let M : Matrix (Fin (n + m)) (Fin (n + m)) F[X] :=
    Polynomial.sylvester B H n m
  rw [Polynomial.resultant]
  change M.det.natDegree ≤ _
  apply natDegree_det_le_of_perm_products_le (M := M)
  intro σ
  by_cases hzero : ∃ i : Fin (n + m), M (σ i) i = 0
  · rcases hzero with ⟨i, hi⟩
    have hprod : (∏ i : Fin (n + m), M (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    simp [hprod]
  · have hne (i : Fin (n + m)) : M (σ i) i ≠ 0 := by
      intro hi
      exact hzero ⟨i, hi⟩
    let lidx : Fin n → ℕ := fun j =>
      ((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ) - (j : ℕ)
    let ridx : Fin m → ℕ := fun j =>
      ((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ) - (j : ℕ)
    let ldeg : Fin n → ℕ := fun j =>
      (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree
    let rdeg : Fin m → ℕ := fun j =>
      (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree
    have hleft_Icc (j : Fin n) :
        ((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ) ∈
          Set.Icc (j : ℕ) ((j : ℕ) + m) := by
      have hentry : M (σ (Fin.castAdd m j)) (Fin.castAdd m j) =
          if ((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ) ∈
              Set.Icc (j : ℕ) ((j : ℕ) + m)
          then H.coeff (((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      by_contra hc
      exact hne (Fin.castAdd m j) (by simp [hentry, hc])
    have hright_Icc (j : Fin m) :
        ((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ) ∈
          Set.Icc (j : ℕ) ((j : ℕ) + n) := by
      have hentry : M (σ (Fin.natAdd n j)) (Fin.natAdd n j) =
          if ((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ) ∈
              Set.Icc (j : ℕ) ((j : ℕ) + n)
          then B.coeff (((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      by_contra hc
      exact hne (Fin.natAdd n j) (by simp [hentry, hc])
    have hleft (j : Fin n) : lidx j + ldeg j ≤ totalDegree H := by
      have hentry : M (σ (Fin.castAdd m j)) (Fin.castAdd m j) =
          H.coeff (((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ) - (j : ℕ)) := by
        have hh : M (σ (Fin.castAdd m j)) (Fin.castAdd m j) =
            if ((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ) ∈
                Set.Icc (j : ℕ) ((j : ℕ) + m)
            then H.coeff (((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ) - (j : ℕ))
            else 0 := by
          simp [M, Polynomial.sylvester]
        rw [hh, if_pos (hleft_Icc j)]
      have hcoeff : H.coeff (lidx j) ≠ 0 := by
        have hh := hne (Fin.castAdd m j)
        rw [hentry] at hh
        simpa only [lidx] using hh
      have hsupp : lidx j ∈ H.support := Polynomial.mem_support_iff.mpr hcoeff
      have hdegree : ldeg j = (H.coeff (lidx j)).natDegree := by
        dsimp [ldeg]
        rw [hentry]
      rw [hdegree]
      simpa only [Nat.add_comm] using coeff_totalDegree_le H hsupp
    have hright (j : Fin m) : ridx j + rdeg j ≤ totalDegree B := by
      have hentry : M (σ (Fin.natAdd n j)) (Fin.natAdd n j) =
          B.coeff (((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ) - (j : ℕ)) := by
        have hh : M (σ (Fin.natAdd n j)) (Fin.natAdd n j) =
            if ((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ) ∈
                Set.Icc (j : ℕ) ((j : ℕ) + n)
            then B.coeff (((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ) - (j : ℕ))
            else 0 := by
          simp [M, Polynomial.sylvester]
        rw [hh, if_pos (hright_Icc j)]
      have hcoeff : B.coeff (ridx j) ≠ 0 := by
        have hh := hne (Fin.natAdd n j)
        rw [hentry] at hh
        simpa only [ridx] using hh
      have hsupp : ridx j ∈ B.support := Polynomial.mem_support_iff.mpr hcoeff
      have hdegree : rdeg j = (B.coeff (ridx j)).natDegree := by
        dsimp [rdeg]
        rw [hentry]
      rw [hdegree]
      simpa only [Nat.add_comm] using coeff_totalDegree_le B hsupp
    have hleft_sum :
        (∑ j : Fin n, (lidx j + ldeg j)) ≤ n * totalDegree H := by
      calc
        _ ≤ ∑ _j : Fin n, totalDegree H :=
          Finset.sum_le_sum (fun j _ => hleft j)
        _ = n * totalDegree H := by simp
    have hright_sum :
        (∑ j : Fin m, (ridx j + rdeg j)) ≤ m * totalDegree B := by
      calc
        _ ≤ ∑ _j : Fin m, totalDegree B :=
          Finset.sum_le_sum (fun j _ => hright j)
        _ = m * totalDegree B := by simp
    have hidxsum :
        (∑ j : Fin n, lidx j) + (∑ j : Fin m, ridx j) = m * n := by
      have hleft_row (j : Fin n) :
          ((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ) = (j : ℕ) + lidx j := by
        dsimp [lidx]
        have hle := (Set.mem_Icc.mp (hleft_Icc j)).1
        omega
      have hright_row (j : Fin m) :
          ((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ) = (j : ℕ) + ridx j := by
        dsimp [ridx]
        have hle := (Set.mem_Icc.mp (hright_Icc j)).1
        omega
      have hsum_left_rows :
          (∑ j : Fin n, ((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ)) =
            (∑ j : Fin n, (j : ℕ)) + (∑ j : Fin n, lidx j) := by
        calc
          _ = ∑ j : Fin n, ((j : ℕ) + lidx j) :=
            Finset.sum_congr rfl (fun j _ => hleft_row j)
          _ = _ := Finset.sum_add_distrib
      have hsum_right_rows :
          (∑ j : Fin m, ((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ)) =
            (∑ j : Fin m, (j : ℕ)) + (∑ j : Fin m, ridx j) := by
        calc
          _ = ∑ j : Fin m, ((j : ℕ) + ridx j) :=
            Finset.sum_congr rfl (fun j _ => hright_row j)
          _ = _ := Finset.sum_add_distrib
      have hperm_sum :
          (∑ i : Fin (n + m), ((σ i : Fin (n + m)) : ℕ)) =
            ∑ i : Fin (n + m), (i : ℕ) := by
        simpa using (Equiv.sum_comp σ (fun i : Fin (n + m) => (i : ℕ)))
      have hrows_split :
          (∑ i : Fin (n + m), ((σ i : Fin (n + m)) : ℕ)) =
            (∑ j : Fin n, ((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ)) +
              (∑ j : Fin m, ((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ)) := by
        simpa using (Fin.sum_univ_add
          (fun i : Fin (n + m) => ((σ i : Fin (n + m)) : ℕ)))
      have hcols_split :
          (∑ i : Fin (n + m), (i : ℕ)) =
            (∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (n + (j : ℕ))) := by
        simpa using (Fin.sum_univ_add (fun i : Fin (n + m) => (i : ℕ)))
      have hright_cols :
          (∑ j : Fin m, (n + (j : ℕ))) =
            m * n + ∑ j : Fin m, (j : ℕ) := by
        simp [Finset.sum_add_distrib, Finset.sum_const]
      have hmain :
          (∑ j : Fin n, ((σ (Fin.castAdd m j) : Fin (n + m)) : ℕ)) +
              (∑ j : Fin m, ((σ (Fin.natAdd n j) : Fin (n + m)) : ℕ)) =
            (∑ j : Fin n, (j : ℕ)) +
              (m * n + ∑ j : Fin m, (j : ℕ)) := by
        rw [← hrows_split, hperm_sum, hcols_split, hright_cols]
      omega
    have hsum :
        ((∑ j : Fin n, lidx j) + (∑ j : Fin n, ldeg j)) +
            ((∑ j : Fin m, ridx j) + (∑ j : Fin m, rdeg j)) ≤
          n * totalDegree H + m * totalDegree B := by
      simpa only [Finset.sum_add_distrib] using Nat.add_le_add hleft_sum hright_sum
    have hdeg_parts :
        (∑ j : Fin n, ldeg j) + (∑ j : Fin m, rdeg j) ≤
          m * totalDegree B + n * totalDegree H - m * n := by
      omega
    have hsum_deg_split :
        (∑ i : Fin (n + m), (M (σ i) i).natDegree) =
          (∑ j : Fin n, ldeg j) + (∑ j : Fin m, rdeg j) := by
      simpa only [ldeg, rdeg] using
        (Fin.sum_univ_add (fun i : Fin (n + m) => (M (σ i) i).natDegree))
    calc
      (∏ i : Fin (n + m), M (σ i) i).natDegree ≤
          ∑ i : Fin (n + m), (M (σ i) i).natDegree := by
        simpa using Polynomial.natDegree_prod_le Finset.univ
          (fun i : Fin (n + m) => M (σ i) i)
      _ = (∑ j : Fin n, ldeg j) + (∑ j : Fin m, rdeg j) := hsum_deg_split
      _ ≤ _ := hdeg_parts

end ProximityPrize.SubmissionLower
