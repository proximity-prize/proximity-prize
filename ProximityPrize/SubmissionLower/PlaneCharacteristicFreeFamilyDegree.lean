import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneCharacteristicFreeDegree

/-!
# Characteristic-free planar degree for a finite component family

Components are grouped by their first-coordinate minpoly.  CRT charges the
sum of relative degrees inside each group to one residue Sylvester corank;
pairwise-coprime minpolys then charge all groups to one resultant degree.
-/

namespace ProximityPrize.SubmissionLower.PlaneCharacteristicFreeFamilyDegree

open MatrixIrreducibleMultiplicity PlaneSylvesterFieldDegree

noncomputable section

variable {K : Type*} [Field K]
variable {J : Type*} [Fintype J]
variable (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable (A : J → Type*) [∀ j, Field (A j)] [∀ j, Algebra K (A j)]
variable (E : ∀ j, I j → Type*) [∀ j i, Field (E j i)]
variable [∀ j i, Algebra (A j) (E j i)] [∀ j i, Algebra K (E j i)]
variable [∀ j i, IsScalarTower K (A j) (E j i)]
variable [∀ j, FiniteDimensional K (A j)]
variable [∀ j i, FiniteDimensional (A j) (E j i)]
variable [∀ j i, FiniteDimensional K (E j i)]

theorem sum_finrank_le_resultant_natDegree
    (x : ∀ j, A j) (y : ∀ j i, E j i)
    (pbA : ∀ j, PowerBasis K (A j))
    (pbE : ∀ j i, PowerBasis (A j) (E j i))
    (hgenA : ∀ j, (pbA j).gen = x j)
    (hgenE : ∀ j i, (pbE j i).gen = y j i)
    (P Q : Polynomial (Polynomial K)) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n)
    (hbaseCoprime : Pairwise (fun a b =>
      IsCoprime (minpoly K (x a)) (minpoly K (x b))))
    (hrelativeKernels : ∀ j, Function.Injective (fun i => RingHom.ker
      (Polynomial.eval₂RingHom (algebraMap (A j) (E j i)) (y j i))))
    (hrelativeDim : ∀ j, (∑ i, (pbE j i).dim) ≤ m + n)
    (hPy : ∀ j i, Polynomial.eval₂ (algebraMap (A j) (E j i)) (y j i)
      (P.map (Polynomial.eval₂RingHom (algebraMap K (A j)) (x j))) = 0)
    (hQy : ∀ j i, Polynomial.eval₂ (algebraMap (A j) (E j i)) (y j i)
      (Q.map (Polynomial.eval₂RingHom (algebraMap K (A j)) (x j))) = 0)
    (hres : Polynomial.resultant P Q m n ≠ 0) :
    (∑ j, ∑ i, Module.finrank K (E j i)) ≤
      (Polynomial.resultant P Q m n).natDegree := by
  classical
  letI : DecidableEq K := Classical.decEq K
  let f : ∀ j, Polynomial K →+* A j := fun j =>
    Polynomial.eval₂RingHom (algebraMap K (A j)) (x j)
  let mu : J → Polynomial K := fun j => minpoly K (x j)
  have hxint (j : J) : IsIntegral K (x j) := by
    rw [← hgenA j]
    exact (pbA j).isIntegral_gen
  have hmuirr (j : J) : Irreducible (mu j) := minpoly.irreducible (hxint j)
  have hmumonic (j : J) : (mu j).Monic := minpoly.monic (hxint j)
  have hfsurj (j : J) : Function.Surjective (f j) := by
    intro a
    obtain ⟨g, _, hg⟩ := (pbA j).exists_eq_aeval a
    refine ⟨g, ?_⟩
    change (Polynomial.aeval (x j)) g = a
    rw [← hgenA j]
    exact hg.symm
  have hfker (j : J) (g : Polynomial K) : f j g = 0 ↔ mu j ∣ g := by
    change (Polynomial.aeval (x j)) g = 0 ↔ minpoly K (x j) ∣ g
    exact minpoly.dvd_iff.symm
  let p : ∀ j, Polynomial (A j) := fun j => P.map (f j)
  let q : ∀ j, Polynomial (A j) := fun j => Q.map (f j)
  have hpdeg (j : J) : (p j).natDegree ≤ m := Polynomial.natDegree_map_le.trans hP
  have hqdeg (j : J) : (q j).natDegree ≤ n := Polynomial.natDegree_map_le.trans hQ
  have hrelative (j : J) :
      (∑ i, Module.finrank (A j) (E j i)) ≤
        m + n - (Polynomial.sylvester (p j) (q j) m n).rank := by
    apply sum_finrank_le_sylvester_corank_of_powerBases
      (K := A j) (E j) (p j) (q j) m n (y j) (pbE j) (hgenE j)
      (hpdeg j) (hqdeg j) (hrelativeKernels j) (hrelativeDim j)
    · exact hPy j
    · exact hQy j
  let M : Matrix (Fin (m + n)) (Fin (m + n)) (Polynomial K) :=
    Polynomial.sylvester P Q m n
  have hdet : M.det ≠ 0 := by
    simpa [M, Polynomial.resultant] using hres
  have hmatrix (j : J) : Polynomial.sylvester (p j) (q j) m n =
      (f j).mapMatrix M := by
    simpa [p, q, M] using Polynomial.sylvester_map_map P Q m n (f j)
  have hweighted :
      (∑ j, (mu j).natDegree *
        (Fintype.card (Fin (m + n)) - ((f j).mapMatrix M).rank)) ≤
        M.det.natDegree := by
    apply sum_irreducible_coranks_le_natDegree_det
      A mu hmuirr hmumonic hbaseCoprime f hfsurj hfker M hdet
  calc
    (∑ j, ∑ i, Module.finrank K (E j i)) =
        ∑ j, Module.finrank K (A j) *
          (∑ i, Module.finrank (A j) (E j i)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (Module.finrank_mul_finrank K (A j) (E j i)).symm
    _ = ∑ j, (mu j).natDegree *
          (∑ i, Module.finrank (A j) (E j i)) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      rw [(pbA j).finrank]
      simpa [mu, hgenA j] using (pbA j).natDegree_minpoly.symm
    _ ≤ ∑ j, (mu j).natDegree *
          (m + n - (Polynomial.sylvester (p j) (q j) m n).rank) := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_left _ (hrelative j)
    _ = ∑ j, (mu j).natDegree *
          (Fintype.card (Fin (m + n)) - ((f j).mapMatrix M).rank) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.card_fin, hmatrix]
    _ ≤ M.det.natDegree := hweighted
    _ = (Polynomial.resultant P Q m n).natDegree := rfl

end

end ProximityPrize.SubmissionLower.PlaneCharacteristicFreeFamilyDegree

#print axioms ProximityPrize.SubmissionLower.PlaneCharacteristicFreeFamilyDegree.sum_finrank_le_resultant_natDegree
