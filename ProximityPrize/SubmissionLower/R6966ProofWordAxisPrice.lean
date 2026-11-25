import ProximityPrize.SubmissionLower.R6966ProofWordUnconstrainedPrice

set_option Elab.async false

namespace Research6966.WordAxisPrice
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation WordSurfaceMarks
variable {σ τ K ι I : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  [Field K] [Fintype I] [DecidableEq I] [Fintype ι]
noncomputable section
set_option maxHeartbeats 600000

/-- Only the variables used by the nodal rows are needed for their separator
interpolation. Restricting to these variables preserves every hit set. -/
theorem restrict_axes (p : ι → σ → K) (rows : I → Pol σ K) (f : τ ↪ σ)
    (keep : ∀ i j, j ∉ Set.range f → (rows i).degreeOf j = 0) :
    ∃ projected : I → Pol τ K,
      (∀ i j, (projected i).degreeOf j = (rows i).degreeOf (f j)) ∧
      ∀ x, hits (p x ∘ f) projected = hits (p x) rows := by
  classical
  have supported (i : I) : (↑(rows i).vars : Set σ) ⊆ Set.range f := by
    intro j hj
    by_contra hn
    exact (mem_vars_iff_degreeOf_ne_zero.mp hj) (keep i j hn)
  choose projected hr using fun i => exists_rename_eq_of_vars_subset_range (rows i) f f.injective (supported i)
  refine ⟨projected, ?_, ?_⟩
  · intro i j
    rw [← hr i, degreeOf_rename_of_injective f.injective]
  · intro x
    ext i
    rw [hit, hit, ← hr i, eval_rename]

private theorem footprint (p : ι → σ → K) (rows : I → Pol σ K) (h : σ → ℕ) (A d : ℕ)
    (gap : d < A) (height : ∀ i j, (rows i).degreeOf j ≤ h j)
    (enough : ∀ x, A ≤ (hits (p x) rows).card)
    (shared : ∀ x y, x ≠ y → ((hits (p x) rows) ∩ (hits (p y) rows)).card ≤ d) :
    Fintype.card ι * finrank K (Local σ K (A-d)) ≤
      ∏ j, WordSurfacePrice.side (Fintype.card I) A d (h j) := by
  classical
  let k := A-d
  have pos : 0 < k := by dsimp [k]; omega
  obtain ⟨sep, cap, own, other⟩ := separators p rows h height A d 1 enough shared
  simp only [one_mul] at cap other
  have onto := interpolate p k pos _ sep cap own other
  have rank := LinearMap.finrank_le_finrank_of_surjective onto
  rw [Module.finrank_pi_fintype, sum_const, card_univ, smul_eq_mul, rectangle_dimension] at rank
  have scale (j : σ) :
      (Fintype.card I-A)*h j+(k-1)+1 = WordSurfacePrice.side (Fintype.card I) A d (h j) := by
    rw [Nat.add_assoc, Nat.sub_add_cancel pos]
    rfl
  simpa only [scale] using rank

theorem two (p : ι → σ → K) (rows : I → Pol σ K) (f : Fin 2 ↪ σ) (h : Fin 2 → ℕ)
    (A d : ℕ) (gap : d < A) (height : ∀ i j, (rows i).degreeOf (f j) ≤ h j)
    (keep : ∀ i j, j ∉ Set.range f → (rows i).degreeOf j = 0)
    (enough : ∀ x, A ≤ (hits (p x) rows).card)
    (shared : ∀ x y, x ≠ y → ((hits (p x) rows) ∩ (hits (p y) rows)).card ≤ d) :
    Fintype.card ι*(A-d)^2 ≤ 2*WordSurfacePrice.side (Fintype.card I) A d (h 0)*
      WordSurfacePrice.side (Fintype.card I) A d (h 1) := by
  obtain ⟨projected, caps, test⟩ := restrict_axes p rows f keep
  have rank := footprint (fun x => p x ∘ f) projected h A d gap
    (fun i j => (caps i j).le.trans (height i j)) (fun x => (test x) ▸ enough x)
    (fun x y ne => by rw [test x, test y]; exact shared x y ne)
  let k := A-d
  have kp : 0 < k := by dsimp [k]; omega
  have dim : finrank K (Local (Fin 2) K k) = (k+1).choose 2 := by
    have v := local_dimension (σ := Fin 2) (K := K) (k-1)
    rw [Nat.sub_add_cancel kp, Fintype.card_fin] at v
    rwa [show k-1+2=k+1 by omega] at v
  rw [dim, Fin.prod_univ_two] at rank
  have eq := Nat.choose_succ_right_eq (k+1) 1
  rw [Nat.choose_one_right, Nat.add_sub_cancel] at eq
  have lower : k^2 ≤ 2*(k+1).choose 2 := by nlinarith
  refine (Nat.mul_le_mul_left _ lower).trans ?_
  nlinarith only [Nat.mul_le_mul_right 2 rank]

theorem one (p : ι → σ → K) (rows : I → Pol σ K) (f : Fin 1 ↪ σ) (h A d : ℕ)
    (gap : d < A) (height : ∀ i, (rows i).degreeOf (f 0) ≤ h)
    (keep : ∀ i j, j ∉ Set.range f → (rows i).degreeOf j = 0)
    (enough : ∀ x, A ≤ (hits (p x) rows).card)
    (shared : ∀ x y, x ≠ y → ((hits (p x) rows) ∩ (hits (p y) rows)).card ≤ d) :
    Fintype.card ι*(A-d) ≤ WordSurfacePrice.side (Fintype.card I) A d h := by
  obtain ⟨projected, caps, test⟩ := restrict_axes p rows f keep
  have rank := footprint (fun x => p x ∘ f) projected (fun _ => h) A d gap
    (fun i j => by rw [caps, Subsingleton.elim j (0:Fin 1)]; exact height i)
    (fun x => (test x) ▸ enough x)
    (fun x y ne => by rw [test x, test y]; exact shared x y ne)
  let k := A-d
  have kp : 0 < k := by dsimp [k]; omega
  have dim : finrank K (Local (Fin 1) K k) = k := by
    have v := local_dimension (σ := Fin 1) (K := K) (k-1)
    rw [Nat.sub_add_cancel kp, Fintype.card_fin, Nat.choose_one_right] at v
    rwa [Nat.sub_add_cancel kp] at v
  change Fintype.card ι * finrank K (Local (Fin 1) K k) ≤ _ at rank
  simpa only [dim, Fin.prod_univ_one] using rank

#print axioms two
#print axioms one
end
end Research6966.WordAxisPrice
