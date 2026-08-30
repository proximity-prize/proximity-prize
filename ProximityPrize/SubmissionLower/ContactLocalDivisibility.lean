import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.ContactLocalDivisibility

open Polynomial

section LocalRing

variable {F : Type*} [CommRing F]

theorem shifted_power_dvd_iff_taylor_coeff_zero
    (P : F[X]) (x : F) (h : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ h ∣ P ↔
      ∀ j < h, (taylor x P).coeff j = 0 := by
  have hshift : taylor x ((Polynomial.X - Polynomial.C x) ^ h) =
      (Polynomial.X : F[X]) ^ h := by
    rw [taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  have hdiv := map_dvd_iff (taylorEquiv x)
    (a := ((Polynomial.X : F[X]) - Polynomial.C x) ^ h) (b := P)
  change taylor x ((Polynomial.X - Polynomial.C x) ^ h) ∣ taylor x P ↔
    (Polynomial.X - Polynomial.C x) ^ h ∣ P at hdiv
  rw [hshift] at hdiv
  exact hdiv.symm.trans (Polynomial.X_pow_dvd_iff (f := taylor x P) (n := h))

noncomputable def contactResidual (P : F[X]) (x : F) : F[X] :=
  taylor x P - Polynomial.C (P.eval x) -
    Polynomial.X * taylor x P.derivative

theorem X_sq_dvd_contactResidual (P : F[X]) (x : F) :
    (Polynomial.X : F[X]) ^ 2 ∣ contactResidual P x := by
  rw [X_pow_dvd_iff]
  intro j hj
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl
  · simp [contactResidual]
  · simp [contactResidual, coeff_X_mul]

end LocalRing

section GlobalVanishing

variable {F I J : Type*} [Field F] [DecidableEq F] [DecidableEq I]

theorem mul_card_le_natDegree_of_rootMultiplicity
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : Polynomial F) (ω : ι ↪ F) (A : Finset ι) (m : Nat)
    (hmult : ∀ i ∈ A, m ≤ R.rootMultiplicity (ω i)) :
    m * A.card ≤ R.natDegree := by
  let xs : Finset F := A.map ω
  have hselected :
      ∑ x ∈ xs, Multiset.count x R.roots ≤ R.roots.card := by
    let all := xs ∪ R.roots.toFinset
    calc
      ∑ x ∈ xs, Multiset.count x R.roots ≤
          ∑ x ∈ all, Multiset.count x R.roots :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
      _ = ∑ x ∈ R.roots.toFinset, Multiset.count x R.roots := by
        symm
        apply Finset.sum_subset (Finset.subset_union_right)
        intro x hxall hxroots
        exact Multiset.count_eq_zero.mpr (by simpa using hxroots)
      _ = R.roots.card := Multiset.toFinset_sum_count_eq R.roots
  calc
    m * A.card = ∑ i ∈ A, m := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ A, R.rootMultiplicity (ω i) :=
      Finset.sum_le_sum fun i hi => hmult i hi
    _ = ∑ x ∈ xs, R.rootMultiplicity x := by
      symm
      exact Finset.sum_map A ω (fun x => R.rootMultiplicity x)
    _ = ∑ x ∈ xs, Multiset.count x R.roots := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Polynomial.count_roots R).symm
    _ ≤ R.roots.card := hselected
    _ ≤ R.natDegree := Polynomial.card_roots' R

end GlobalVanishing

end ProximityPrize.SubmissionLower.ContactLocalDivisibility
