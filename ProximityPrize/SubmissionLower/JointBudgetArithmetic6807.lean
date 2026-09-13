import ProximityPrize.SubmissionLower.CommonLinearChannels6807
/-
UNCOMPILED. Arithmetic adapter, not a proof of the generic-fiber construction.
The three unit-cut premises below are explicit remaining geometric obligations.
There are no added axioms, admitted goals, or unsafe computation shortcuts.
-/
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.JointBudgetArithmetic6807
open scoped BigOperators
open RCN095 RCN237
set_option autoImplicit false

variable {ι : Type*} [Fintype ι]

theorem scaled_pointwise (d b u n m v : ℕ)
    (hu : 1 ≤ u) (hm : d*m ≤ v) :
    d*(u*n+b*m) ≤ u*(d*n+b*v) := by
  calc
    d*(u*n+b*m) = d*u*n+b*(d*m) := by ring
    _ ≤ d*u*n+b*v := Nat.add_le_add_left (Nat.mul_le_mul_left b hm) _
    _ ≤ d*u*n+u*(b*v) := by
      apply Nat.add_le_add_left
      simpa only [one_mul] using Nat.mul_le_mul_right (b*v) hu
    _ = u*(d*n+b*v) := by ring

theorem joint_scaled (d b bound : ℕ) (u n m v : ι → ℕ)
    (hu : ∀ i, 1 ≤ u i) (hm : ∀ i, d*m i ≤ v i)
    (hcut : d*(∑ i, u i*(d*n i+b*v i)) ≤ bound) :
    d^2*(∑ i, (u i*n i+b*m i)) ≤ bound := by
  have hfirst : d*(∑ i, (u i*n i+b*m i)) ≤
      ∑ i, u i*(d*n i+b*v i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => scaled_pointwise d b (u i) (n i)
      (m i) (v i) (hu i) (hm i))
  calc
    d^2*(∑ i, (u i*n i+b*m i)) = d*(d*(∑ i, (u i*n i+b*m i))) := by ring
    _ ≤ d*(∑ i, u i*(d*n i+b*v i)) := Nat.mul_le_mul_left d hfirst
    _ ≤ bound := hcut

theorem joint_floor (d b bound : ℕ) (hd : 0 < d) (u n m v : ι → ℕ)
    (hu : ∀ i, 1 ≤ u i) (hm : ∀ i, d*m i ≤ v i)
    (hcut : d*(∑ i, u i*(d*n i+b*v i)) ≤ bound) :
    (∑ i, (u i*n i+b*m i)) ≤ bound/(d^2) := by
  apply (Nat.le_div_iff_mul_le (pow_pos hd 2)).mpr
  simpa only [Nat.mul_comm] using joint_scaled d b bound u n m v hu hm hcut

/-- Three scalar projection cuts suffice. This is only their linear combination. -/
theorem three_unit_cuts (d : ℕ) (u zc yc ac : ι → ℕ)
    (p first second : FlagDegree)
    (hz : d*(∑ i, u i*zc i) ≤ flagMixed p first unitZFlag)
    (hy : d*(∑ i, u i*yc i) ≤ flagMixed p first unitYZFlag)
    (ha : d*(∑ i, u i*ac i) ≤ flagMixed p first unitAllFlag) :
    d*(∑ i, u i*(second.zOnly*zc i+second.yz*yc i+second.all*ac i)) ≤
      flagMixed p first second := by
  calc
    d*(∑ i, u i*(second.zOnly*zc i+second.yz*yc i+second.all*ac i)) =
      second.zOnly*(d*(∑ i,u i*zc i)) +
      second.yz*(d*(∑ i,u i*yc i)) +
      second.all*(d*(∑ i,u i*ac i)) := by
        simp only [Nat.mul_add, Finset.sum_add_distrib, Finset.mul_sum,
          Nat.mul_left_comm, Nat.mul_assoc]
    _ ≤ second.zOnly*flagMixed p first unitZFlag +
        second.yz*flagMixed p first unitYZFlag +
        second.all*flagMixed p first unitAllFlag :=
      Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left second.zOnly hz)
        (Nat.mul_le_mul_left second.yz hy))
        (Nat.mul_le_mul_left second.all ha)
    _ = flagMixed p first second :=
      by simp only [flagMixed, unitZFlag, unitYZFlag, unitAllFlag]; ring

/-- A finite, multiplicity-aware form of the remaining generic-slice argument.
`weight` is the actual place zero order; `lift` must be injective on all copies.
Constructing these inputs from the original DVRs is not asserted here. -/
theorem zero_mass_transport {κ : Type*} [Fintype κ]
    (multiplicity : ι → ℕ) (degree : ι → ℕ) (weight : κ → ℕ)
    (lift : (i : ι) × Fin (degree i) → κ)
    (hinj : Function.Injective lift)
    (horder : ∀ i j, multiplicity i ≤ weight (lift ⟨i,j⟩)) :
    (∑ i, multiplicity i*degree i) ≤ ∑ k, weight k := by
  classical
  letI : DecidableEq κ := Classical.decEq κ
  calc
    (∑ i, multiplicity i*degree i) =
        ∑ a : (i : ι) × Fin (degree i), multiplicity a.1 := by
      rw [Fintype.sum_sigma]
      simp [Nat.mul_comm]
    _ ≤ ∑ a : (i : ι) × Fin (degree i), weight (lift a) :=
      Finset.sum_le_sum (fun a _ => horder a.1 a.2)
    _ = ∑ k ∈ Finset.univ.image lift, weight k := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact hinj hab
    _ ≤ ∑ k, weight k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)


/-- A unit-cut bound follows from a concrete slice witness. No final unit-cut
inequality is assumed: the inputs are zero-mass transport, a first-pole bound,
the pointwise source inequality, and the old pure-flag slice budget. -/
theorem first_slice_mass {κ : Type*} [Fintype κ]
    (d w bound : ℕ) (u degree : ι → ℕ) (zeros first moving source : κ → ℕ)
    (htransport : (∑ i,u i*degree i) ≤ ∑ j,zeros j)
    (hpole : ∀ j, zeros j ≤ first j+w*moving j)
    (hsource : ∀ j, d*moving j ≤ source j)
    (hbudget : (∑ j, (d*first j+w*source j)) ≤ bound) :
    d*(∑ i,u i*degree i) ≤ bound := by
  calc
    d*(∑ i,u i*degree i) ≤ d*(∑ j,zeros j) := Nat.mul_le_mul_left d htransport
    _ = ∑ j,d*zeros j := Finset.mul_sum _ _ _
    _ ≤ ∑ j, (d*first j+w*source j) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        d*zeros j ≤ d*(first j+w*moving j) := Nat.mul_le_mul_left d (hpole j)
        _ = d*first j+w*(d*moving j) := by ring
        _ ≤ d*first j+w*source j :=
          Nat.add_le_add_left (Nat.mul_le_mul_left w (hsource j)) _
    _ ≤ bound := hbudget

end ProximityPrize.SubmissionLower.JointBudgetArithmetic6807
