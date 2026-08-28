import ProximityPrize.SubmissionLower.ContactJointSeedCaps
import ProximityPrize.SubmissionLower.ContactSparseResultant

/-!
# Joint seed caps on the actual generic surface

The original contact polynomial uses coordinates `(X,Y,R,Z)`.  Passing to
the generic surface absorbs `X` into the coefficient field and leaves
coordinates `(Y,R,Z)`.  This file proves that the original weighted `Y+Z`
degree is preserved as an upper bound under that passage, and that every
factor of a nonzero surface polynomial inherits the same bound.

The result is then applied to the actual first-tail and agreement
polynomials.  In particular, the sparse base-`R` resultant may use the
joint pair weights `[1,0,1]`, rather than the rectangular sum of separate
`Y`- and `Z`-degree caps.
-/

namespace ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps

open ContactAlignmentParameters ContactFactorCaps
open ContactGenericSurface ContactInterpolation ContactJointSeedCaps
open ContactSparseResultant ContactTaylorNumerators

noncomputable section

variable {K L : Type*} [Field K] [Field L]

local notation:1000 "W4 " P:1000 =>
  MvPolynomial.weightedTotalDegree seedWeights P

local notation:1000 "W3 " P:1000 =>
  MvPolynomial.weightedTotalDegree seedPairWeights P

/-- Reinsert the three surface variables as the last three variables of a
four-variable polynomial.  The missing first variable is the collected
coefficient variable `X`. -/
def restoreSurfaceVariables :
    MvPolynomial (Fin 3) L →+* MvPolynomial (Fin 4) L :=
  (MvPolynomial.rename (R := L) fun i : Fin 3 => i.succ).toRingHom

theorem restoreSurfaceVariables_injective :
    Function.Injective (restoreSurfaceVariables (L := L)) :=
  MvPolynomial.rename_injective _ (Fin.succ_injective 3)

@[simp] theorem seedWeights_comp_succ :
    seedWeights ∘ (fun i : Fin 3 => i.succ) = seedPairWeights := by
  funext i
  fin_cases i <;> rfl

/-- Restoring the omitted `X` variable identifies the two concrete weight
functions exactly. -/
@[simp] theorem weightedTotalDegree_restoreSurfaceVariables
    (P : MvPolynomial (Fin 3) L) :
    W4 (restoreSurfaceVariables P) = W3 P := by
  simpa [restoreSurfaceVariables] using
    (MvPolynomial.weightedTotalDegree_rename_of_injective
      (R := L) (P := P) (w := seedWeights) (Fin.succ_injective 3))

theorem weight_fin3 (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight weights d =
      d 0 * weights 0 + d 1 * weights 1 + d 2 * weights 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i
    fin_cases i <;> simp
  calc
    Finsupp.weight weights d = Finsupp.weight weights
        (Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
          Finsupp.single 2 (d 2)) := congrArg _ hd
    _ = _ := by
      simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, Nat.cast_id]

@[simp] theorem seedPair_weight (d : Fin 3 →₀ ℕ) :
    Finsupp.weight seedPairWeights d = d 0 + d 2 := by
  rw [weight_fin3]
  simp [seedPairWeights]

/-- Dropping the coefficient variable never increases the joint `Y+Z`
weighted degree.  This is the exact geometric bridge from the original
four-variable support to the surface support. -/
theorem surfaceMap_seedPair_weightedTotalDegree_le
    (φ : Polynomial K →+* L) (Q : MvPolynomial (Fin 4) K) :
    W3 (surfaceMap φ Q) ≤ W4 Q := by
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  intro e he
  rw [seedPair_weight]
  apply surfaceMap_joint_seed_cap φ Q (W4 Q) _ e he
  intro d hd
  rw [← seed_weight]
  exact MvPolynomial.le_weightedTotalDegree seedWeights hd

/-- Joint weighted degree is monotone under divisibility for surface
polynomials.  The proof transports divisibility to four variables, where
the already verified arbitrary-weight product theorem applies. -/
theorem seedPair_weightedTotalDegree_le_of_dvd
    (G S : MvPolynomial (Fin 3) L) (hdiv : G ∣ S) (hS : S ≠ 0) :
    W3 G ≤ W3 S := by
  have hdiv' : restoreSurfaceVariables G ∣ restoreSurfaceVariables S :=
    map_dvd restoreSurfaceVariables hdiv
  have hS' : restoreSurfaceVariables S ≠ 0 := by
    intro hzero
    apply hS
    apply restoreSurfaceVariables_injective
    simpa only [map_zero] using hzero
  have h := weightedTotalDegree_le_of_dvd seedWeights
    (restoreSurfaceVariables G) (restoreSurfaceVariables S) hdiv' hS'
  simpa only [weightedTotalDegree_restoreSurfaceVariables] using h

/-- Every divisor of a nonzero actual surface image inherits the original
four-variable joint seed cap. -/
theorem seedPair_weightedTotalDegree_le_of_dvd_surfaceMap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (G : MvPolynomial (Fin 3) L) (hdiv : G ∣ surfaceMap φ F)
    (hsurface : surfaceMap φ F ≠ 0) :
    W3 G ≤ W4 F :=
  (seedPair_weightedTotalDegree_le_of_dvd G (surfaceMap φ F) hdiv hsurface).trans
    (surfaceMap_seedPair_weightedTotalDegree_le φ F)

/-- The actual recurrence numerator on the generic surface has the joint
cap supplied by the joint contact recurrence. -/
theorem surface_numerator_joint_seed_cap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (seedCap b : ℕ) (hF : W4 F ≤ seedCap) :
    W3 (surfaceMap φ (numerator K F b)) ≤ 1 + 2 * b * seedCap :=
  (surfaceMap_seedPair_weightedTotalDegree_le φ (numerator K F b)).trans
    (numerator_joint_wt_le F seedCap hF b)

/-- In particular, the actual first tail uses `b = w+1`. -/
theorem firstTailSurface_joint_seed_cap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (seedCap w : ℕ) (hF : W4 F ≤ seedCap) :
    W3 (surfaceMap φ (numerator K F (w + 1))) ≤
      1 + 2 * (w + 1) * seedCap := by
  exact surface_numerator_joint_seed_cap φ F seedCap (w + 1) hF

/-- The actual agreement polynomial has the matching one-layer-smaller
joint cap. -/
theorem surface_agreementNumerator_joint_seed_cap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (seedCap w : ℕ) (hF : W4 F ≤ seedCap)
    (c : ℕ → K) (x u₀ u₁ : K) :
    W3 (surfaceMap φ (agreementNumerator F w c x u₀ u₁)) ≤
      1 + 2 * w * seedCap :=
  (surfaceMap_seedPair_weightedTotalDegree_le φ
      (agreementNumerator F w c x u₀ u₁)).trans
    (agreementNumerator_joint_wt_le F seedCap w hF c x u₀ u₁)

theorem factorialAgreementSurface_joint_seed_cap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (seedCap w : ℕ) (hF : W4 F ≤ seedCap) (x u₀ u₁ : K) :
    W3 (surfaceMap φ
      (agreementNumerator F w (fun j => (j.factorial : K)⁻¹) x u₀ u₁)) ≤
        1 + 2 * w * seedCap := by
  exact surface_agreementNumerator_joint_seed_cap φ F seedCap w hF
    (fun j => (j.factorial : K)⁻¹) x u₀ u₁

/-- The frozen interpolation box supplies the joint cap used by all fixed
64.62 wrappers below. -/
theorem fixed_original_joint_seed_cap
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    W4 F ≤ seedTotalCap := by
  exact ((mem_globalCoefficientBox_iff F weightedCap w seedTotalCap slopeCap
    (by norm_num [ContactAlignmentParameters.weightedCap,
      ContactAlignmentParameters.multiplicity,
      ContactAlignmentParameters.agreements])).mp hbox).1

theorem fixed_surfaceMap_joint_seed_cap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    W3 (surfaceMap φ F) ≤ seedTotalCap :=
  (surfaceMap_seedPair_weightedTotalDegree_le φ F).trans
    (fixed_original_joint_seed_cap F hbox)

theorem fixed_surface_factor_joint_seed_cap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (G : MvPolynomial (Fin 3) L)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hdiv : G ∣ surfaceMap φ F) (hsurface : surfaceMap φ F ≠ 0) :
    W3 G ≤ seedTotalCap :=
  (seedPair_weightedTotalDegree_le_of_dvd G (surfaceMap φ F) hdiv hsurface).trans
    (fixed_surfaceMap_joint_seed_cap φ F hbox)

theorem fixed_firstTailSurface_joint_seed_cap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    W3 (surfaceMap φ (numerator K F (w + 1))) ≤
      1 + 2 * (w + 1) * seedTotalCap :=
  firstTailSurface_joint_seed_cap φ F seedTotalCap w
    (fixed_original_joint_seed_cap F hbox)

theorem fixed_factorialAgreementSurface_joint_seed_cap
    (φ : Polynomial K →+* L) (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (x u₀ u₁ : K) :
    W3 (surfaceMap φ
      (agreementNumerator F w (fun j => (j.factorial : K)⁻¹) x u₀ u₁)) ≤
        1 + 2 * w * seedTotalCap :=
  factorialAgreementSurface_joint_seed_cap φ F seedTotalCap w
    (fixed_original_joint_seed_cap F hbox) x u₀ u₁

theorem fixed_joint_seed_cap_values :
    1 + 2 * (w + 1) * seedTotalCap = 44564481 ∧
      1 + 2 * w * seedTotalCap = 44564141 := by
  norm_num [w, seedTotalCap]

end

end ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps

#print axioms ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps.surfaceMap_seedPair_weightedTotalDegree_le
#print axioms ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps.seedPair_weightedTotalDegree_le_of_dvd_surfaceMap
#print axioms ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps.firstTailSurface_joint_seed_cap
#print axioms ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps.factorialAgreementSurface_joint_seed_cap
#print axioms ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps.fixed_surface_factor_joint_seed_cap
#print axioms ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps.fixed_firstTailSurface_joint_seed_cap
#print axioms ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps.fixed_factorialAgreementSurface_joint_seed_cap
