import ProximityPrize.SubmissionLower.ContactGeometricFirstTail
import ProximityPrize.SubmissionLower.ContactFactorCaps

/-!
# Joint seed-support inheritance for actual surface factors

An irreducible factor of a nonzero three-variable surface polynomial inherits
the `Y+Z` Newton support cap.  Zero weight on the middle coordinate is handled
by an injective exponent lift retaining all original exponents.
-/

namespace ProximityPrize.SubmissionLower.ContactSurfaceFactorJointSeedCap

open ContactGenericSurface ContactFactorCaps

noncomputable section

def surfacePairWeights : Fin 3 → ℕ := ![1, 0, 1]

def surfaceWeightEmbed (d : Fin 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
    Finsupp.single 2 (d 2) +
      Finsupp.single 3 (Finsupp.weight surfacePairWeights d)

theorem surfaceWeightEmbed_zero : surfaceWeightEmbed 0 = 0 := by
  ext i
  fin_cases i <;> simp [surfaceWeightEmbed]

theorem surfaceWeightEmbed_add (d e : Fin 3 →₀ ℕ) :
    surfaceWeightEmbed (d + e) = surfaceWeightEmbed d + surfaceWeightEmbed e := by
  ext i
  fin_cases i <;> simp [surfaceWeightEmbed, Finsupp.add_apply, map_add]

def surfaceWeightEmbedHom : (Fin 3 →₀ ℕ) →+ (Fin 4 →₀ ℕ) where
  toFun := surfaceWeightEmbed
  map_zero' := surfaceWeightEmbed_zero
  map_add' := surfaceWeightEmbed_add

theorem surfaceWeightEmbed_castSucc (d : Fin 3 →₀ ℕ) (i : Fin 3) :
    surfaceWeightEmbed d i.castSucc = d i := by
  fin_cases i <;> simp [surfaceWeightEmbed]

theorem surfaceWeightEmbed_last (d : Fin 3 →₀ ℕ) :
    surfaceWeightEmbed d (3 : Fin 4) = Finsupp.weight surfacePairWeights d := by
  simp [surfaceWeightEmbed]

theorem surfaceWeightEmbed_injective : Function.Injective surfaceWeightEmbed := by
  intro d e h
  ext i
  have hi := congrArg (fun a : Fin 4 →₀ ℕ => a i.castSucc) h
  simpa only [surfaceWeightEmbed_castSucc] using hi

variable {K : Type*} [Field K]

def surfaceWeightedLift : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 4) K :=
  AddMonoidAlgebra.mapDomainRingHom K surfaceWeightEmbedHom

theorem surfaceWeightedLift_injective : Function.Injective (surfaceWeightedLift (K := K)) :=
  AddMonoidAlgebra.mapDomain_injective surfaceWeightEmbed_injective

theorem surfaceWeightedLift_ne_zero (P : MvPolynomial (Fin 3) K) (hP : P ≠ 0) :
    surfaceWeightedLift P ≠ 0 := by
  intro hz
  apply hP
  apply surfaceWeightedLift_injective
  simpa only [map_zero] using hz

theorem surface_support_weightedLift (P : MvPolynomial (Fin 3) K) :
    (surfaceWeightedLift P).support = P.support.image surfaceWeightEmbed := by
  change (Finsupp.mapDomain surfaceWeightEmbedHom (AddMonoidAlgebra.coeff P)).support =
    Finset.image surfaceWeightEmbed (AddMonoidAlgebra.coeff P).support
  exact Finsupp.mapDomain_support_of_injective surfaceWeightEmbed_injective _

theorem surface_degree_weightedLift (P : MvPolynomial (Fin 3) K) :
    (surfaceWeightedLift P).degreeOf (3 : Fin 4) =
      MvPolynomial.weightedTotalDegree surfacePairWeights P := by
  change (surfaceWeightedLift P).degreeOf (3 : Fin 4) =
    P.support.sup (Finsupp.weight surfacePairWeights)
  rw [MvPolynomial.degreeOf_eq_sup, surface_support_weightedLift, Finset.sup_image]
  apply congrArg (fun f : (Fin 3 →₀ ℕ) → ℕ => P.support.sup f)
  funext d
  exact surfaceWeightEmbed_last d

theorem surface_weightedTotalDegree_mul
    (P Q : MvPolynomial (Fin 3) K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    MvPolynomial.weightedTotalDegree surfacePairWeights (P * Q) =
      MvPolynomial.weightedTotalDegree surfacePairWeights P +
        MvPolynomial.weightedTotalDegree surfacePairWeights Q := by
  calc
    _ = (surfaceWeightedLift (P * Q)).degreeOf (3 : Fin 4) :=
      (surface_degree_weightedLift (P * Q)).symm
    _ = (surfaceWeightedLift P * surfaceWeightedLift Q).degreeOf (3 : Fin 4) := by
      rw [map_mul]
    _ = (surfaceWeightedLift P).degreeOf (3 : Fin 4) +
        (surfaceWeightedLift Q).degreeOf (3 : Fin 4) :=
      MvPolynomial.degreeOf_mul_eq (surfaceWeightedLift_ne_zero P hP)
        (surfaceWeightedLift_ne_zero Q hQ)
    _ = _ := by rw [surface_degree_weightedLift, surface_degree_weightedLift]

theorem surface_weightedTotalDegree_le_of_dvd
    (P Q : MvPolynomial (Fin 3) K) (hdiv : P ∣ Q) (hQ : Q ≠ 0) :
    MvPolynomial.weightedTotalDegree surfacePairWeights P ≤
      MvPolynomial.weightedTotalDegree surfacePairWeights Q := by
  rcases hdiv with ⟨R, rfl⟩
  rcases mul_ne_zero_iff.mp hQ with ⟨hP, hR⟩
  rw [surface_weightedTotalDegree_mul P R hP hR]
  exact Nat.le_add_right _ _

theorem surface_pair_weight (d : Fin 3 →₀ ℕ) :
    Finsupp.weight surfacePairWeights d = d 0 + d 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i
    fin_cases i <;> simp
  rw [hd]
  simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, Nat.cast_id]
  simp [surfacePairWeights]

theorem surface_factor_joint_seed_cap
    {L : Type*} [Field L] (φ : Polynomial K →+* L)
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) L) (cap : ℕ)
    (hφ : Function.Injective φ) (hF : F ≠ 0) (hdiv : G ∣ surfaceMap φ F)
    (hcap : ∀ d ∈ F.support, d 1 + d 3 ≤ cap) :
    ∀ e ∈ G.support, e 0 + e 2 ≤ cap := by
  have hsurface : surfaceMap φ F ≠ 0 := surfaceMap_ne_zero φ hφ F hF
  have hsupp := surfaceMap_joint_seed_cap φ F cap hcap
  have hsurfaceWeight :
      MvPolynomial.weightedTotalDegree surfacePairWeights (surfaceMap φ F) ≤ cap := by
    unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro e he
    rw [surface_pair_weight]
    exact hsupp e he
  have hGWeight := (surface_weightedTotalDegree_le_of_dvd G (surfaceMap φ F)
    hdiv hsurface).trans hsurfaceWeight
  intro e he
  rw [← surface_pair_weight]
  exact (MvPolynomial.le_weightedTotalDegree surfacePairWeights he).trans hGWeight

end

end ProximityPrize.SubmissionLower.ContactSurfaceFactorJointSeedCap

#print axioms ProximityPrize.SubmissionLower.ContactSurfaceFactorJointSeedCap.surface_factor_joint_seed_cap
