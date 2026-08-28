import ProximityPrize.SubmissionLower.ActualPlanePositiveOrder
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateCaps
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateDegree
import ProximityPrize.SubmissionLower.ActualCurveProjectionBounds
import ProximityPrize.SubmissionLower.BCHKSResultantDegree
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_MvPolynomial_Homogeneous

open Polynomial.Bivariate Polynomial Matrix
open scoped BigOperators

namespace ProximityPrize.SubmissionLower.ContactSparseResultant

set_option maxHeartbeats 4000000

open ProximityPrize.SubmissionLower
open ProximityPrize.SubmissionLower.TrivariateRationalCollection
open ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
open ProximityPrize.SubmissionLower.ActualPlaneCoordinateCaps
open ProximityPrize.SubmissionLower.ActualPlanePositiveOrder

lemma fin_shift_sum (m n : ℕ) :
    (∑ i : Fin (n + m), (i : ℕ)) -
      ((∑ i : Fin n, (i : ℕ)) + (∑ i : Fin m, (i : ℕ))) = n * m := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (∑ x : Fin n, (x : ℕ)) +
      (m * n + ∑ x : Fin m, (x : ℕ)) -
      ((∑ x : Fin n, (x : ℕ)) + ∑ x : Fin m, (x : ℕ)) = n * m
  have heq : (∑ x : Fin n, (x : ℕ)) +
      (m * n + ∑ x : Fin m, (x : ℕ)) =
      ((∑ x : Fin n, (x : ℕ)) + ∑ x : Fin m, (x : ℕ)) + n * m := by ring
  rw [heq, Nat.add_sub_cancel_left]

/-- A total-degree refinement of `ps_nat_degree_resultant_le`.

`A` has declared outer degree `m` and total cap `d`, while `B` has
declared outer degree `n` and total cap `b`.  Thus the coefficient of
outer degree `k` has inner degree at most the total cap minus `k`.
-/
lemma sparse_natDegree_resultant_add_le {F : Type} [Field F]
    (A B : F[X][Y]) (m n d b : ℕ)
    (hA : ∀ k : ℕ, k ≤ m → (A.coeff k).natDegree + k ≤ d)
    (hB : ∀ k : ℕ, k ≤ n → (B.coeff k).natDegree + k ≤ b) :
    (resultant B A n m).natDegree + m * n ≤ n * d + m * b := by
  classical
  have hmd : m ≤ d := by
    have hh := hA m le_rfl
    omega
  let M : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := sylvester B A n m
  let shift : Fin (n + m) → ℕ :=
    Fin.addCases (fun j : Fin n => (j : ℕ)) (fun j : Fin m => (j : ℕ))
  let cap : Fin (n + m) → ℕ :=
    Fin.addCases (fun _ : Fin n => d) (fun _ : Fin m => b)
  have hcap_sum : (∑ i : Fin (n + m), cap i) = n * d + m * b := by
    simp [cap, Fin.sum_univ_add]
  have hshift_sum : (∑ i : Fin (n + m), shift i) =
      (∑ i : Fin n, (i : ℕ)) + ∑ i : Fin m, (i : ℕ) := by
    simp [shift, Fin.sum_univ_add]
  have hpermsum (σ : Equiv.Perm (Fin (n + m))) :
      (∑ i : Fin (n + m), (σ i : ℕ)) = ∑ i : Fin (n + m), (i : ℕ) := by
    exact Equiv.sum_comp σ (fun i : Fin (n + m) => (i : ℕ))
  have hterm (σ : Equiv.Perm (Fin (n + m))) :
      (Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i).natDegree + m * n ≤
        n * d + m * b := by
    by_cases hz : ∃ i : Fin (n + m), M (σ i) i = 0
    · obtain ⟨i, hi⟩ := hz
      have hp : (∏ j : Fin (n + m), M (σ j) j) = 0 := by
        exact Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hp]
      simp only [smul_zero, natDegree_zero, zero_add]
      have h1 : m * n ≤ n * d := by
        rw [Nat.mul_comm m n]
        exact Nat.mul_le_mul_left n hmd
      exact h1.trans (Nat.le_add_right _ _)
    · push Not at hz
      have hshift_le (i : Fin (n + m)) : shift i ≤ (σ i : ℕ) := by
        cases i using Fin.addCases with
        | «left» i0 =>
            have hM : M (σ (.castAdd m i0)) (.castAdd m i0) =
                if ((σ (.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m))
                then A.coeff ((σ (.castAdd m i0) : ℕ) - i0) else 0 := by
              simp [M, sylvester, Matrix.of_apply, Fin.addCases_left]
            have hi := hz (.castAdd m i0)
            rw [hM] at hi
            by_contra hnot
            have hout : ¬ ((σ (.castAdd m i0) : ℕ) ∈
                Set.Icc (i0 : ℕ) ((i0 : ℕ) + m)) := by
              intro hh
              apply hnot
              simpa [shift] using hh.1
            simp [hout] at hi
        | «right» i0 =>
            have hM : M (σ (.natAdd n i0)) (.natAdd n i0) =
                if ((σ (.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n))
                then B.coeff ((σ (.natAdd n i0) : ℕ) - i0) else 0 := by
              simp [M, sylvester, Matrix.of_apply, Fin.addCases_right]
            have hi := hz (.natAdd n i0)
            rw [hM] at hi
            by_contra hnot
            have hout : ¬ ((σ (.natAdd n i0) : ℕ) ∈
                Set.Icc (i0 : ℕ) ((i0 : ℕ) + n)) := by
              intro hh
              apply hnot
              simpa [shift] using hh.1
            simp [hout] at hi
      have hentry (i : Fin (n + m)) :
          (M (σ i) i).natDegree + ((σ i : ℕ) - shift i) ≤ cap i := by
        cases i using Fin.addCases with
        | «left» i0 =>
            simp only [shift, cap, Fin.addCases_left]
            have hM : M (σ (.castAdd m i0)) (.castAdd m i0) =
                if ((σ (.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m))
                then A.coeff ((σ (.castAdd m i0) : ℕ) - i0) else 0 := by
              simp [M, sylvester, Matrix.of_apply, Fin.addCases_left]
            have hi := hz (.castAdd m i0)
            rw [hM] at hi
            have hin : ((σ (.castAdd m i0) : ℕ) ∈
                Set.Icc (i0 : ℕ) ((i0 : ℕ) + m)) := by
              by_contra hout
              simp [hout] at hi
            rw [hM, if_pos hin]
            apply hA _
            rw [Nat.sub_le_iff_le_add']
            exact hin.2
        | «right» i0 =>
            simp only [shift, cap, Fin.addCases_right]
            have hM : M (σ (.natAdd n i0)) (.natAdd n i0) =
                if ((σ (.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n))
                then B.coeff ((σ (.natAdd n i0) : ℕ) - i0) else 0 := by
              simp [M, sylvester, Matrix.of_apply, Fin.addCases_right]
            have hi := hz (.natAdd n i0)
            rw [hM] at hi
            have hin : ((σ (.natAdd n i0) : ℕ) ∈
                Set.Icc (i0 : ℕ) ((i0 : ℕ) + n)) := by
              by_contra hout
              simp [hout] at hi
            rw [hM, if_pos hin]
            apply hB _
            rw [Nat.sub_le_iff_le_add']
            exact hin.2
      have hindex_sum :
          (∑ i : Fin (n + m), ((σ i : ℕ) - shift i)) = m * n := by
        rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => hshift_le i), hpermsum,
          hshift_sum, fin_shift_sum]
        exact Nat.mul_comm n m
      have hsum :
          (∑ i : Fin (n + m), (M (σ i) i).natDegree) + m * n ≤ n * d + m * b := by
        rw [← hindex_sum, ← Finset.sum_add_distrib, ← hcap_sum]
        exact Finset.sum_le_sum (fun i _ => hentry i)
      have hprod : (∏ i : Fin (n + m), M (σ i) i).natDegree ≤
          ∑ i : Fin (n + m), (M (σ i) i).natDegree := by
        simpa using natDegree_prod_le Finset.univ (fun i => M (σ i) i)
      have hsmul := natDegree_smul_le (Equiv.Perm.sign σ) (∏ i : Fin (n + m), M (σ i) i)
      omega
  have hdet : M.det.natDegree + m * n ≤ n * d + m * b := by
    rw [det_apply]
    have hsum : (∑ σ : Equiv.Perm (Fin (n + m)),
        Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree ≤ n * d + m * b - m * n := by
      apply natDegree_sum_le_of_forall_le
      intro σ _
      have hh := hterm σ
      omega
    have hmn : m * n ≤ n * d + m * b := by
      have h1 : m * n ≤ n * d := by
        rw [Nat.mul_comm m n]
        exact Nat.mul_le_mul_left n hmd
      exact h1.trans (Nat.le_add_right _ _)
    omega
  change (sylvester B A n m).det.natDegree + m * n ≤ n * d + m * b
  simpa [M] using hdet

lemma sparse_natDegree_resultant_le {F : Type} [Field F]
    (A B : F[X][Y]) (m n d b : ℕ)
    (hA : ∀ k : ℕ, k ≤ m → (A.coeff k).natDegree + k ≤ d)
    (hB : ∀ k : ℕ, k ≤ n → (B.coeff k).natDegree + k ≤ b) :
    (resultant B A n m).natDegree ≤ n * d + m * b - m * n := by
  have h := sparse_natDegree_resultant_add_le A B m n d b hA hB
  omega

section PlaneIntegration

noncomputable section

variable (K : Type) [Field K]

/-- Weight zero on the rational-function base coordinate and weight one on
the two coordinates retained by `rationalMap`. -/
def remainingPairWeights (order : Fin 3 ≃ Fin 3) : Fin 3 → ℕ :=
  (Fin.cases 0 (fun _ : Fin 2 => 1)) ∘ order.symm

private theorem firstMap_totalDegree_le_remaining
    {A : Type} [Field A] (φ : Polynomial K →+* A)
    (F : MvPolynomial (Fin 3) K) :
    (firstMap K φ F).totalDegree ≤
      MvPolynomial.weightedTotalDegree (Fin.cases 0 (fun _ : Fin 2 => 1)) F := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_firstMap_subset K φ F he)
  calc
    d.tail.sum (fun _ n => n) = Finsupp.weight
        (Fin.cases 0 (fun _ : Fin 2 => 1)) d := by
      rw [Finsupp.sum_fintype, Finsupp.weight_apply, Finsupp.sum_fintype]
      · simp [Fin.sum_univ_succ, Finsupp.tail_apply]
      · simp
      · simp
    _ ≤ MvPolynomial.weightedTotalDegree
        (Fin.cases 0 (fun _ : Fin 2 => 1)) F :=
      MvPolynomial.le_weightedTotalDegree _ hd

/-- Collection/localization does not increase total degree in the two
remaining variables. This is the arbitrary-order pair-cap adapter. -/
theorem rationalMap_totalDegree_le_remainingPair
    (order : Fin 3 ≃ Fin 3) (F : Original K) :
    (rationalMap K order F).totalDegree ≤
      MvPolynomial.weightedTotalDegree (remainingPairWeights order) F := by
  rw [rationalMap_eq_firstMap]
  calc
    _ ≤ MvPolynomial.weightedTotalDegree
        (Fin.cases 0 (fun _ : Fin 2 => 1)) (MvPolynomial.rename order.symm F) :=
      firstMap_totalDegree_le_remaining K _ _
    _ = MvPolynomial.weightedTotalDegree (remainingPairWeights order) F := by
      exact MvPolynomial.weightedTotalDegree_rename_of_injective order.symm.injective

/-- The coefficient triangle of the nested plane polynomial: inner degree
plus outer index is bounded by any total-degree cap for `rationalMap`. -/
theorem planeMap_coeff_natDegree_add_le
    (order : Fin 3 ≃ Fin 3) (F : Original K) (D k : ℕ)
    (hD : (rationalMap K order F).totalDegree ≤ D)
    (hk : k ≤ (planeMap K order F).natDegree) :
    ((planeMap K order F).coeff k).natDegree + k ≤ D := by
  let f := rationalMap K order F
  change f.totalDegree ≤ D at hD
  let c := (MvPolynomial.finSuccEquiv (RatFunc K) 1 f).coeff k
  have hcoeff_eq : (planeMap K order F).coeff k =
      MvPolynomial.uniqueAlgEquiv (RatFunc K) (Fin 1) c := by
    simp [planeMap, bivariateEquiv, f, c]
  have houter : (planeMap K order F).natDegree ≤ f.totalDegree := by
    change (bivariateEquiv (RatFunc K) f).natDegree ≤ f.totalDegree
    rw [bivariateEquiv_natDegree]
    exact MvPolynomial.degreeOf_le_totalDegree f 0
  by_cases hc : c = 0
  · rw [hcoeff_eq, hc, map_zero, Polynomial.natDegree_zero]
    omega
  · have htriangle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f k hc
    change c.totalDegree + k ≤ f.totalDegree at htriangle
    have hinner : ((planeMap K order F).coeff k).natDegree ≤ c.totalDegree := by
      rw [hcoeff_eq]
      exact (uniqueAlgEquiv_natDegree_le (RatFunc K) c).trans
        (MvPolynomial.degreeOf_le_totalDegree c 0)
    omega

/-- Coefficient triangle using the canonical original pair-weight cap. -/
theorem planeMap_coeff_natDegree_add_le_remainingPair
    (order : Fin 3 ≃ Fin 3) (F : Original K) (k : ℕ)
    (hk : k ≤ (planeMap K order F).natDegree) :
    ((planeMap K order F).coeff k).natDegree + k ≤
      MvPolynomial.weightedTotalDegree (remainingPairWeights order) F := by
  exact planeMap_coeff_natDegree_add_le K order F _ k
    (rationalMap_totalDegree_le_remainingPair K order F) hk

set_option maxHeartbeats 800000

/-- Sparse resultant bound from arbitrary total pair caps. The declared
outer degrees are the actual degrees, so the fixed-degree resultant is the
ordinary resultant used by the projection pipeline. -/
theorem planeMap_sparse_resultant_add_le
    (order : Fin 3 ≃ Fin 3) (G T : Original K) (g t : ℕ)
    (hg : (rationalMap K order G).totalDegree ≤ g)
    (ht : (rationalMap K order T).totalDegree ≤ t) :
    (Polynomial.resultant (planeMap K order G) (planeMap K order T)
        (planeMap K order G).natDegree (planeMap K order T).natDegree).natDegree +
        (planeMap K order T).natDegree * (planeMap K order G).natDegree ≤
      (planeMap K order G).natDegree * t +
        (planeMap K order T).natDegree * g := by
  have hGcoeff : ∀ k : ℕ, k ≤ (planeMap K order G).natDegree →
      ((planeMap K order G).coeff k).natDegree + k ≤ g := by
    intro k hk
    exact planeMap_coeff_natDegree_add_le K order G g k hg hk
  have hTcoeff : ∀ k : ℕ, k ≤ (planeMap K order T).natDegree →
      ((planeMap K order T).coeff k).natDegree + k ≤ t := by
    intro k hk
    exact planeMap_coeff_natDegree_add_le K order T t k ht hk
  exact sparse_natDegree_resultant_add_le (F := RatFunc K)
    (planeMap K order T) (planeMap K order G)
    (planeMap K order T).natDegree (planeMap K order G).natDegree
    t g hTcoeff hGcoeff

theorem planeMap_sparse_resultant_le
    (order : Fin 3 ≃ Fin 3) (G T : Original K) (g t : ℕ)
    (hg : (rationalMap K order G).totalDegree ≤ g)
    (ht : (rationalMap K order T).totalDegree ≤ t) :
    (Polynomial.resultant (planeMap K order G) (planeMap K order T)).natDegree ≤
      (planeMap K order T).natDegree * g +
        (planeMap K order G).natDegree * t -
          (planeMap K order G).natDegree * (planeMap K order T).natDegree := by
  have h := planeMap_sparse_resultant_add_le K order G T g t hg ht
  simp only [Nat.mul_comm (planeMap K order T).natDegree
    (planeMap K order G).natDegree,
    Nat.add_comm ((planeMap K order G).natDegree * t)
      ((planeMap K order T).natDegree * g)] at h
  omega

theorem sparseBound_mono (x y a c b d : ℕ) (hxa : x ≤ a) (hyc : y ≤ c)
    (hab : a ≤ b) (hcd : c ≤ d) :
    x * d + y * b - x * y ≤ a * d + c * b - a * c := by
  have hleft : x * y ≤ x * d + y * b := by
    exact (Nat.mul_le_mul_left x (hyc.trans hcd)).trans (Nat.le_add_right _ _)
  have hright : a * c ≤ a * d + c * b := by
    exact (Nat.mul_le_mul_left a hcd).trans (Nat.le_add_right _ _)
  let A := a - x
  let C := c - y
  let D := d - c
  let B := b - x
  have ha : x + A = a := Nat.add_sub_of_le hxa
  have hc : y + C = c := Nat.add_sub_of_le hyc
  have hd : c + D = d := Nat.add_sub_of_le hcd
  have hb : x + B = b := Nat.add_sub_of_le (hxa.trans hab)
  have hid : a * d + c * b + x * y = x * d + y * b + a * c + A * D + C * B := by
    rw [← hd, ← hb, ← ha, ← hc]
    ring
  have hpoly : x * d + y * b + a * c ≤ a * d + c * b + x * y := by
    calc
      _ ≤ x * d + y * b + a * c + A * D + C * B := by omega
      _ = _ := hid.symm
  omega

/-- Cap-level sparse envelope used by the fixed arithmetic certificate. -/
theorem planeMap_sparse_resultant_le_caps
    (order : Fin 3 ≃ Fin 3) (G T : Original K)
    (gy ty g t : ℕ)
    (hGtotal : (rationalMap K order G).totalDegree ≤ g)
    (hTtotal : (rationalMap K order T).totalDegree ≤ t)
    (hGY : G.degreeOf (order 1) ≤ gy) (hTY : T.degreeOf (order 1) ≤ ty)
    (hyg : gy ≤ g) (hyt : ty ≤ t) :
    (Polynomial.resultant (planeMap K order G) (planeMap K order T)).natDegree ≤
      gy * t + ty * g - gy * ty := by
  let x := (planeMap K order G).natDegree
  let y := (planeMap K order T).natDegree
  have hx : x ≤ gy :=
    (planeMap_natDegree_le K order G).trans hGY
  have hy : y ≤ ty :=
    (planeMap_natDegree_le K order T).trans hTY
  have hmono :
      (planeMap K order T).natDegree * g +
          (planeMap K order G).natDegree * t -
            (planeMap K order G).natDegree * (planeMap K order T).natDegree ≤
        gy * t + ty * g - gy * ty := by
    simpa only [x, y, Nat.add_comm] using
      sparseBound_mono x y gy ty g t hx hy hyg hyt
  exact (planeMap_sparse_resultant_le K order G T g t hGtotal hTtotal).trans hmono

/-- Sparse bound with the canonical original pair weights. -/
theorem planeMap_sparse_resultant_le_remainingPair
    (order : Fin 3 ≃ Fin 3) (G T : Original K) :
    (Polynomial.resultant (planeMap K order G) (planeMap K order T)).natDegree ≤
      (planeMap K order T).natDegree *
          MvPolynomial.weightedTotalDegree (remainingPairWeights order) G +
        (planeMap K order G).natDegree *
          MvPolynomial.weightedTotalDegree (remainingPairWeights order) T -
        (planeMap K order G).natDegree * (planeMap K order T).natDegree := by
  exact planeMap_sparse_resultant_le K order G T _ _
    (rationalMap_totalDegree_le_remainingPair K order G)
    (rationalMap_totalDegree_le_remainingPair K order T)

/-- The preferred base-R order: coefficient variable R, outer Y, inner Z. -/
def rBaseYOuterOrder : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

/-- Same rational base, with Z outer and Y inner. -/
def rBaseZOuterOrder : Fin 3 ≃ Fin 3 := swapOtherOrder rBaseYOuterOrder

def seedPairWeights : Fin 3 → ℕ := ![1, 0, 1]

@[simp] theorem rBaseYOuterOrder_zero : rBaseYOuterOrder 0 = 1 := by
  simp [rBaseYOuterOrder]

@[simp] theorem rBaseYOuterOrder_one : rBaseYOuterOrder 1 = 0 := by
  simp [rBaseYOuterOrder]

@[simp] theorem rBaseYOuterOrder_two : rBaseYOuterOrder 2 = 2 := by
  simp [rBaseYOuterOrder, Equiv.swap_apply_def]

@[simp] theorem rBaseZOuterOrder_zero : rBaseZOuterOrder 0 = 1 := by
  simp [rBaseZOuterOrder]

@[simp] theorem rBaseZOuterOrder_one : rBaseZOuterOrder 1 = 2 := by
  simp [rBaseZOuterOrder]

@[simp] theorem rBaseZOuterOrder_two : rBaseZOuterOrder 2 = 0 := by
  simp [rBaseZOuterOrder]

@[simp] theorem remainingPairWeights_rBaseYOuterOrder :
    remainingPairWeights rBaseYOuterOrder = seedPairWeights := by
  funext i
  fin_cases i <;> decide

@[simp] theorem remainingPairWeights_rBaseZOuterOrder :
    remainingPairWeights rBaseZOuterOrder = seedPairWeights := by
  funext i
  fin_cases i <;> decide

theorem rationalMap_totalDegree_le_seedPair_yOuter (F : Original K) :
    (rationalMap K rBaseYOuterOrder F).totalDegree ≤
      MvPolynomial.weightedTotalDegree seedPairWeights F := by
  simpa using rationalMap_totalDegree_le_remainingPair K rBaseYOuterOrder F

theorem rationalMap_totalDegree_le_seedPair_zOuter (F : Original K) :
    (rationalMap K rBaseZOuterOrder F).totalDegree ≤
      MvPolynomial.weightedTotalDegree seedPairWeights F := by
  simpa using rationalMap_totalDegree_le_remainingPair K rBaseZOuterOrder F

theorem planeMap_coeff_triangle_seedPair_yOuter
    (F : Original K) (k : ℕ) (hk : k ≤ (planeMap K rBaseYOuterOrder F).natDegree) :
    ((planeMap K rBaseYOuterOrder F).coeff k).natDegree + k ≤
      MvPolynomial.weightedTotalDegree seedPairWeights F := by
  simpa using planeMap_coeff_natDegree_add_le_remainingPair K rBaseYOuterOrder F k hk

theorem planeMap_coeff_triangle_seedPair_zOuter
    (F : Original K) (k : ℕ) (hk : k ≤ (planeMap K rBaseZOuterOrder F).natDegree) :
    ((planeMap K rBaseZOuterOrder F).coeff k).natDegree + k ≤
      MvPolynomial.weightedTotalDegree seedPairWeights F := by
  simpa using planeMap_coeff_natDegree_add_le_remainingPair K rBaseZOuterOrder F k hk

/-- Preferred Y-outer sparse gate, still in exact actual outer degrees. -/
theorem planeMap_sparse_resultant_le_seedPair_yOuter (G T : Original K) :
    (Polynomial.resultant (planeMap K rBaseYOuterOrder G)
      (planeMap K rBaseYOuterOrder T)).natDegree ≤
      (planeMap K rBaseYOuterOrder T).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights G +
        (planeMap K rBaseYOuterOrder G).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights T -
        (planeMap K rBaseYOuterOrder G).natDegree *
          (planeMap K rBaseYOuterOrder T).natDegree := by
  simpa using planeMap_sparse_resultant_le_remainingPair K rBaseYOuterOrder G T

theorem planeMap_sparse_resultant_le_seedPair_zOuter (G T : Original K) :
    (Polynomial.resultant (planeMap K rBaseZOuterOrder G)
      (planeMap K rBaseZOuterOrder T)).natDegree ≤
      (planeMap K rBaseZOuterOrder T).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights G +
        (planeMap K rBaseZOuterOrder G).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights T -
        (planeMap K rBaseZOuterOrder G).natDegree *
          (planeMap K rBaseZOuterOrder T).natDegree := by
  simpa using planeMap_sparse_resultant_le_remainingPair K rBaseZOuterOrder G T

/-- When the preferred Y-outer equation has degree zero, Y is a zero-degree
inner coordinate in the swapped Z-outer chart. -/
theorem planeMap_zOuter_degreeX_le_yOuter_natDegree (F : Original K) :
    Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder F) ≤
      (planeMap K rBaseYOuterOrder F).natDegree := by
  calc
    Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder F) ≤
        (rationalMap K rBaseZOuterOrder F).degreeOf 1 :=
      bivariateEquiv_degreeX_le (RatFunc K) _
    _ = (rationalMap K rBaseYOuterOrder F).degreeOf 0 := by
      rw [show rBaseZOuterOrder = swapOtherOrder rBaseYOuterOrder by rfl,
        rationalMap_swapOtherOrder]
      change (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
        (rationalMap K rBaseYOuterOrder F)).degreeOf 1 = _
      simpa only [Equiv.swap_apply_left] using
        (MvPolynomial.degreeOf_rename_of_injective
          (p := rationalMap K rBaseYOuterOrder F)
          (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2))
    _ = (planeMap K rBaseYOuterOrder F).natDegree := by
      rw [show (planeMap K rBaseYOuterOrder F).natDegree =
        (rationalMap K rBaseYOuterOrder F).degreeOf 0 by
          exact bivariateEquiv_natDegree (RatFunc K) _]

/-- Actual Z-outer resultant bound in the zero-Y-outer branch.  This avoids
any need to identify original and localized Y degrees. -/
theorem planeMap_zOuter_resultant_le_of_yOuter_zero
    (G T : Original K) (g ty : ℕ)
    (hYzero : (planeMap K rBaseYOuterOrder G).natDegree = 0)
    (hGtotal : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hTY : T.degreeOf 0 ≤ ty) :
    (Polynomial.resultant (planeMap K rBaseZOuterOrder G)
      (planeMap K rBaseZOuterOrder T)).natDegree ≤ g * ty := by
  have hGX : Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder G) = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (planeMap_zOuter_degreeX_le_yOuter_natDegree K G).trans (le_of_eq hYzero)
  have hGouter : (planeMap K rBaseZOuterOrder G).natDegree ≤ g := by
    calc
      _ = (rationalMap K rBaseZOuterOrder G).degreeOf 0 :=
        bivariateEquiv_natDegree (RatFunc K) _
      _ ≤ (rationalMap K rBaseZOuterOrder G).totalDegree :=
        MvPolynomial.degreeOf_le_totalDegree _ 0
      _ ≤ g := hGtotal
  have hTX : Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder T) ≤ ty :=
    (planeMap_degreeX_le K rBaseZOuterOrder T).trans (by simpa using hTY)
  have hres := bivariate_resultant_natDegree_le
    (planeMap K rBaseZOuterOrder G) (planeMap K rBaseZOuterOrder T)
    (planeMap K rBaseZOuterOrder G).natDegree
    (planeMap K rBaseZOuterOrder T).natDegree
  have hres' :
      (Polynomial.resultant (planeMap K rBaseZOuterOrder G)
        (planeMap K rBaseZOuterOrder T)).natDegree ≤
        (planeMap K rBaseZOuterOrder T).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder G) +
          (planeMap K rBaseZOuterOrder G).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder T) := by
    simpa using hres
  rw [hGX, Nat.mul_zero, zero_add] at hres'
  exact hres'.trans (Nat.mul_le_mul hGouter hTX)

def rectangleResultantBound (order : Fin 3 ≃ Fin 3) (G T : Original K) : ℕ :=
  T.degreeOf (order 1) * G.degreeOf (order 2) +
    G.degreeOf (order 1) * T.degreeOf (order 2)

def sparseResultantBound (order : Fin 3 ≃ Fin 3) (G T : Original K) : ℕ :=
  (planeMap K order T).natDegree *
      MvPolynomial.weightedTotalDegree (remainingPairWeights order) G +
    (planeMap K order G).natDegree *
      MvPolynomial.weightedTotalDegree (remainingPairWeights order) T -
    (planeMap K order G).natDegree * (planeMap K order T).natDegree

def hybridResultantBound (order : Fin 3 ≃ Fin 3) (G T : Original K) : ℕ :=
  min (rectangleResultantBound K order G T) (sparseResultantBound K order G T)

/-- Both the old rectangle and the new total-degree triangle bound are
available, hence their minimum is a certified resultant envelope. -/
theorem planeMap_resultant_natDegree_le_hybrid
    (order : Fin 3 ≃ Fin 3) (G T : Original K) :
    (Polynomial.resultant (planeMap K order G) (planeMap K order T)).natDegree ≤
      hybridResultantBound K order G T := by
  apply le_min
  · exact planeMap_resultant_natDegree_le K order G T
  · exact planeMap_sparse_resultant_le_remainingPair K order G T

theorem hybrid_characteristic_gates
    (order : Fin 3 ≃ Fin 3) (G T : Original K) (p : ℕ)
    (houter : G.degreeOf (order 1) < p)
    (hresultant : hybridResultantBound K order G T < p) :
    (planeMap K order G).natDegree < p ∧
      (Polynomial.resultant (planeMap K order G) (planeMap K order T)).natDegree < p :=
  ⟨(planeMap_natDegree_le K order G).trans_lt houter,
    (planeMap_resultant_natDegree_le_hybrid K order G T).trans_lt hresultant⟩

/-- Preferred positive-Y route using the sparse seed-pair envelope directly. -/
theorem yOuter_sparse_characteristic_gates
    (G T : Original K) (p : ℕ) (hGY : G.degreeOf 0 < p)
    (hsparse :
      (planeMap K rBaseYOuterOrder T).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights G +
        (planeMap K rBaseYOuterOrder G).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights T -
        (planeMap K rBaseYOuterOrder G).natDegree *
          (planeMap K rBaseYOuterOrder T).natDegree < p) :
    (planeMap K rBaseYOuterOrder G).natDegree < p ∧
      (Polynomial.resultant (planeMap K rBaseYOuterOrder G)
        (planeMap K rBaseYOuterOrder T)).natDegree < p :=
  ⟨(planeMap_natDegree_le K rBaseYOuterOrder G).trans_lt (by simpa using hGY),
    (planeMap_sparse_resultant_le_seedPair_yOuter K G T).trans_lt hsparse⟩

/-- If G has no Y degree, the Z-outer rectangle is exactly `G_Z*T_Y`. -/
theorem zOuter_characteristic_gates_of_yDegree_zero
    (G T : Original K) (p : ℕ) (hGY : G.degreeOf 0 = 0)
    (hGZ : G.degreeOf 2 < p)
    (hrectangle : G.degreeOf 2 * T.degreeOf 0 < p) :
    (planeMap K rBaseZOuterOrder G).natDegree < p ∧
      (Polynomial.resultant (planeMap K rBaseZOuterOrder G)
        (planeMap K rBaseZOuterOrder T)).natDegree < p := by
  apply original_characteristic_gates K rBaseZOuterOrder G T p
  · simpa using hGZ
  · simpa [hGY, Nat.mul_comm] using hrectangle

end
end PlaneIntegration

section ProjectionGlue

open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualPlaneCoordinateDegree

noncomputable section

variable (K : Type) [Field K]

/-- Single-component projection theorem in the preferred R-base/Y-outer
chart.  The sparse gate supplies separability, while the existing planar
theorem retains its original rectangular finrank budget. -/
theorem actual_finite_separable_finrank_bound_yOuter_sparse
    (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (rBaseYOuterOrder 0)))
    (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P) (hproper : ¬ G ∣ T)
    (hpositive : 0 < (planeMap K rBaseYOuterOrder G).natDegree)
    (hGY : G.degreeOf 0 < p)
    (hsparse :
      (planeMap K rBaseYOuterOrder T).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights G +
        (planeMap K rBaseYOuterOrder G).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights T -
        (planeMap K rBaseYOuterOrder G).natDegree *
          (planeMap K rBaseYOuterOrder T).natDegree < p) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (rBaseYOuterOrder 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
      Module.finrank (RatFunc K) (CoordinateField K P) ≤
        (planeMap K rBaseYOuterOrder T).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseYOuterOrder G) +
          (planeMap K rBaseYOuterOrder G).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseYOuterOrder T) := by
  obtain ⟨houter, hres⟩ := yOuter_sparse_characteristic_gates K G T p hGY hsparse
  apply actual_finite_separable_finrank_bound K rBaseYOuterOrder P ht p G T
    hG hGmem hTmem hproper hpositive houter
  simpa using hres

/-- Finite-family form used by the summed coordinate-degree ledger. -/
theorem actual_finite_separable_sum_finrank_bound_yOuter_sparse
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (ht : ∀ i, Transcendental K (coordinate K (P i) (rBaseYOuterOrder 0)))
    (hinj : Function.Injective P) (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i) (hTmem : ∀ i, T ∈ P i)
    (hproper : ¬ G ∣ T)
    (hpositive : 0 < (planeMap K rBaseYOuterOrder G).natDegree)
    (hGY : G.degreeOf 0 < p)
    (hsparse :
      (planeMap K rBaseYOuterOrder T).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights G +
        (planeMap K rBaseYOuterOrder G).natDegree *
          MvPolynomial.weightedTotalDegree seedPairWeights T -
        (planeMap K rBaseYOuterOrder G).natDegree *
          (planeMap K rBaseYOuterOrder T).natDegree < p) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i => rationalBaseAlgebra K (P i) (rBaseYOuterOrder 0) (ht i)
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
        (planeMap K rBaseYOuterOrder T).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseYOuterOrder G) +
          (planeMap K rBaseYOuterOrder G).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseYOuterOrder T) := by
  obtain ⟨houter, hres⟩ := yOuter_sparse_characteristic_gates K G T p hGY hsparse
  apply actual_finite_separable_sum_finrank_bound K rBaseYOuterOrder P ht hinj p G T
    hG hGmem hTmem hproper hpositive houter
  simpa using hres

/-- Z-outer fallback when the original surface has zero Y-degree. -/
theorem actual_finite_separable_finrank_bound_zOuter_zeroY
    (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (rBaseZOuterOrder 0)))
    (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P) (hproper : ¬ G ∣ T)
    (hpositive : 0 < (planeMap K rBaseZOuterOrder G).natDegree)
    (hGY : G.degreeOf 0 = 0) (hGZ : G.degreeOf 2 < p)
    (hrectangle : G.degreeOf 2 * T.degreeOf 0 < p) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (rBaseZOuterOrder 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
      Module.finrank (RatFunc K) (CoordinateField K P) ≤
        (planeMap K rBaseZOuterOrder T).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder G) +
          (planeMap K rBaseZOuterOrder G).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder T) := by
  obtain ⟨houter, hres⟩ :=
    zOuter_characteristic_gates_of_yDegree_zero K G T p hGY hGZ hrectangle
  apply actual_finite_separable_finrank_bound K rBaseZOuterOrder P ht p G T
    hG hGmem hTmem hproper hpositive houter
  simpa using hres

/-- Z-outer fallback phrased entirely in actual localized degrees.  This is
the branch paired with `by_cases 0 < natDegree (planeMap ... YOuter G)`. -/
theorem actual_finite_separable_finrank_bound_zOuter_actualZero
    (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (rBaseZOuterOrder 0)))
    (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P) (hproper : ¬ G ∣ T)
    (hpositive : 0 < (planeMap K rBaseZOuterOrder G).natDegree)
    (g ty : ℕ)
    (hYzero : (planeMap K rBaseYOuterOrder G).natDegree = 0)
    (hGtotal : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hTY : T.degreeOf 0 ≤ ty) (hg : g < p) (hprod : g * ty < p) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (rBaseZOuterOrder 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
      Module.finrank (RatFunc K) (CoordinateField K P) ≤
        (planeMap K rBaseZOuterOrder T).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder G) +
          (planeMap K rBaseZOuterOrder G).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder T) := by
  have houter : (planeMap K rBaseZOuterOrder G).natDegree < p := by
    calc
      _ = (rationalMap K rBaseZOuterOrder G).degreeOf 0 :=
        bivariateEquiv_natDegree (RatFunc K) _
      _ ≤ (rationalMap K rBaseZOuterOrder G).totalDegree :=
        MvPolynomial.degreeOf_le_totalDegree _ 0
      _ ≤ g := hGtotal
      _ < p := hg
  have hres := planeMap_zOuter_resultant_le_of_yOuter_zero K G T g ty hYzero hGtotal hTY
  apply actual_finite_separable_finrank_bound K rBaseZOuterOrder P ht p G T
    hG hGmem hTmem hproper hpositive houter
  simpa using hres.trans_lt hprod

theorem actual_finite_separable_sum_finrank_bound_zOuter_actualZero
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (ht : ∀ i, Transcendental K (coordinate K (P i) (rBaseZOuterOrder 0)))
    (hinj : Function.Injective P) (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i) (hTmem : ∀ i, T ∈ P i)
    (hproper : ¬ G ∣ T)
    (hpositive : 0 < (planeMap K rBaseZOuterOrder G).natDegree)
    (g ty : ℕ)
    (hYzero : (planeMap K rBaseYOuterOrder G).natDegree = 0)
    (hGtotal : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hTY : T.degreeOf 0 ≤ ty) (hg : g < p) (hprod : g * ty < p) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i => rationalBaseAlgebra K (P i) (rBaseZOuterOrder 0) (ht i)
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
        (planeMap K rBaseZOuterOrder T).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder G) +
          (planeMap K rBaseZOuterOrder G).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K rBaseZOuterOrder T) := by
  have houter : (planeMap K rBaseZOuterOrder G).natDegree < p := by
    calc
      _ = (rationalMap K rBaseZOuterOrder G).degreeOf 0 :=
        bivariateEquiv_natDegree (RatFunc K) _
      _ ≤ (rationalMap K rBaseZOuterOrder G).totalDegree :=
        MvPolynomial.degreeOf_le_totalDegree _ 0
      _ ≤ g := hGtotal
      _ < p := hg
  have hres := planeMap_zOuter_resultant_le_of_yOuter_zero K G T g ty hYzero hGtotal hTY
  apply actual_finite_separable_sum_finrank_bound K rBaseZOuterOrder P ht hinj p G T
    hG hGmem hTmem hproper hpositive houter
  simpa using hres.trans_lt hprod

end
end ProjectionGlue

section RBaseProjectionGlue

open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualPlaneCoordinateDegree ActualCurveProjectionBounds

noncomputable section

variable (K : Type) [Field K]

/-- The complete base-R projection theorem.  The Y-outer branch uses the
sparse resultant, while an actual zero Y-outer degree switches to Z-outer
and uses the collapsed rectangle.  The conclusion deliberately retains the
old rectangular mixed-degree budget consumed by the counting ledger. -/
theorem original_finite_separable_finrank_bound_rBase_sparse
    (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (rBaseYOuterOrder 0)))
    (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P) (hproper : ¬ G ∣ T)
    (gy ty g t : ℕ)
    (hGY : G.degreeOf 0 ≤ gy) (hTY : T.degreeOf 0 ≤ ty)
    (hGtotalY : (rationalMap K rBaseYOuterOrder G).totalDegree ≤ g)
    (hTtotalY : (rationalMap K rBaseYOuterOrder T).totalDegree ≤ t)
    (hGtotalZ : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hyg : gy ≤ g) (hyt : ty ≤ t)
    (hgy : gy < p) (hg : g < p) (hprod : g * ty < p)
    (hsparse : gy * t + ty * g - gy * ty < p) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (rBaseYOuterOrder 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
      Module.finrank (RatFunc K) (CoordinateField K P) ≤
        originalMixedDegree K rBaseYOuterOrder G T := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    rationalBaseAlgebra K P (rBaseYOuterOrder 0) ht
  by_cases hy : 0 < (planeMap K rBaseYOuterOrder G).natDegree
  · have houter : (planeMap K rBaseYOuterOrder G).natDegree < p :=
      (planeMap_natDegree_le K rBaseYOuterOrder G).trans_lt (hGY.trans_lt hgy)
    have hres := planeMap_sparse_resultant_le_caps K rBaseYOuterOrder G T
      gy ty g t hGtotalY hTtotalY hGY hTY hyg hyt
    have hr := actual_finite_separable_finrank_bound K rBaseYOuterOrder P ht p G T
      hG hGmem hTmem hproper hy houter (by simpa using hres.trans_lt hsparse)
    exact ⟨hr.1, hr.2.1, hr.2.2.trans (plane_budget_le_original K rBaseYOuterOrder G T)⟩
  · have hy0 : (planeMap K rBaseYOuterOrder G).natDegree = 0 := Nat.eq_zero_of_not_pos hy
    obtain ⟨order', hor, hbase, hpos⟩ :=
      exists_positive_outer_order K rBaseYOuterOrder P G hG hGmem ht
    have hzorder : order' = rBaseZOuterOrder := by
      rcases hor with h | h
      · subst order'
        exact (hy hpos).elim
      · exact h
    subst order'
    have htZ : Transcendental K (coordinate K P (rBaseZOuterOrder 0)) := by
      simpa using ht
    have hr := actual_finite_separable_finrank_bound_zOuter_actualZero K P htZ p G T
      hG hGmem hTmem hproper hpos g ty hy0 hGtotalZ hTY hg hprod
    have halg : rationalBaseAlgebra K P (rBaseZOuterOrder 0) htZ =
        rationalBaseAlgebra K P (rBaseYOuterOrder 0) ht := by
      apply rationalBaseAlgebra_congr K P
      simp
    rw [halg] at hr
    refine ⟨hr.1, hr.2.1, hr.2.2.trans ?_⟩
    have hb := plane_budget_le_original K rBaseZOuterOrder G T
    simpa [rBaseZOuterOrder, originalMixedDegree_swap] using hb

/-- Finite-family version; this is the interface used to sum actual
coordinate degrees over all regular minimal components. -/
theorem original_finite_separable_sum_finrank_bound_rBase_sparse
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (ht : ∀ i, Transcendental K (coordinate K (P i) (rBaseYOuterOrder 0)))
    (hinj : Function.Injective P) (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i) (hTmem : ∀ i, T ∈ P i)
    (hproper : ¬ G ∣ T)
    (gy ty g t : ℕ)
    (hGY : G.degreeOf 0 ≤ gy) (hTY : T.degreeOf 0 ≤ ty)
    (hGtotalY : (rationalMap K rBaseYOuterOrder G).totalDegree ≤ g)
    (hTtotalY : (rationalMap K rBaseYOuterOrder T).totalDegree ≤ t)
    (hGtotalZ : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hyg : gy ≤ g) (hyt : ty ≤ t)
    (hgy : gy < p) (hg : g < p) (hprod : g * ty < p)
    (hsparse : gy * t + ty * g - gy * ty < p) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i => rationalBaseAlgebra K (P i) (rBaseYOuterOrder 0) (ht i)
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
        originalMixedDegree K rBaseYOuterOrder G T := by
  classical
  letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
    fun i => rationalBaseAlgebra K (P i) (rBaseYOuterOrder 0) (ht i)
  by_cases hI : Nonempty I
  · let i₀ : I := Classical.choice hI
    by_cases hy : 0 < (planeMap K rBaseYOuterOrder G).natDegree
    · have houter : (planeMap K rBaseYOuterOrder G).natDegree < p :=
        (planeMap_natDegree_le K rBaseYOuterOrder G).trans_lt (hGY.trans_lt hgy)
      have hres := planeMap_sparse_resultant_le_caps K rBaseYOuterOrder G T
        gy ty g t hGtotalY hTtotalY hGY hTY hyg hyt
      have hr := actual_finite_separable_sum_finrank_bound K rBaseYOuterOrder P ht
        hinj p G T hG hGmem hTmem hproper hy houter (by simpa using hres.trans_lt hsparse)
      exact ⟨hr.1, hr.2.trans (plane_budget_le_original K rBaseYOuterOrder G T)⟩
    · have hy0 : (planeMap K rBaseYOuterOrder G).natDegree = 0 := Nat.eq_zero_of_not_pos hy
      obtain ⟨order', hor, hbase, hpos⟩ :=
        exists_positive_outer_order K rBaseYOuterOrder (P i₀) G hG (hGmem i₀) (ht i₀)
      have hzorder : order' = rBaseZOuterOrder := by
        rcases hor with h | h
        · subst order'
          exact (hy hpos).elim
        · exact h
      subst order'
      have htZ : ∀ i, Transcendental K (coordinate K (P i) (rBaseZOuterOrder 0)) := by
        intro i
        simpa using ht i
      have hr := actual_finite_separable_sum_finrank_bound_zOuter_actualZero K P htZ
        hinj p G T hG hGmem hTmem hproper hpos g ty hy0 hGtotalZ hTY hg hprod
      have halg : (fun i => rationalBaseAlgebra K (P i) (rBaseZOuterOrder 0) (htZ i)) =
          (fun i => rationalBaseAlgebra K (P i) (rBaseYOuterOrder 0) (ht i)) := by
        funext i
        apply rationalBaseAlgebra_congr K (P i)
        simp
      rw [halg] at hr
      refine ⟨hr.1, hr.2.trans ?_⟩
      have hb := plane_budget_le_original K rBaseZOuterOrder G T
      simpa [rBaseZOuterOrder, originalMixedDegree_swap] using hb
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    constructor
    · intro i
      exact isEmptyElim i
    · simp

end
end RBaseProjectionGlue

end ProximityPrize.SubmissionLower.ContactSparseResultant

#print axioms ProximityPrize.SubmissionLower.ContactSparseResultant.rationalMap_totalDegree_le_remainingPair
#print axioms ProximityPrize.SubmissionLower.ContactSparseResultant.planeMap_coeff_natDegree_add_le
#print axioms ProximityPrize.SubmissionLower.ContactSparseResultant.planeMap_sparse_resultant_le
#print axioms ProximityPrize.SubmissionLower.ContactSparseResultant.planeMap_resultant_natDegree_le_hybrid
#print axioms ProximityPrize.SubmissionLower.ContactSparseResultant.yOuter_sparse_characteristic_gates
#print axioms ProximityPrize.SubmissionLower.ContactSparseResultant.zOuter_characteristic_gates_of_yDegree_zero

