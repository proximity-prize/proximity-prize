import ProximityPrize.SubmissionLower.Koala6844Primitive
import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryCarrier



namespace ProximityPrize.SubmissionLower.Koala6844Comparison

open MvPolynomial Koala6844HighOrdinary
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

private def seedCarrierCoordinates : Fin 2 → Fin 4 := ![2, 3]
private def seedOrdinaryCoordinates : Fin 2 → Fin 5 := ![3, 4]

def carrierCoefficientCoordinates : Option (Fin 2) → Fin 4
  | none => 0
  | some i => seedCarrierCoordinates i

def carrierOfSeedCoefficients : SeedCoefficients K →+* Carrier K :=
  (MvPolynomial.rename carrierCoefficientCoordinates).toRingHom.comp
    (MvPolynomial.optionEquivLeft K (Fin 2)).symm.toRingEquiv.toRingHom

def primitiveRowLift (q : SymbolicRow (SeedRing K)) : Koala6844HighOrdinary.Poly K :=
  comparisonRow (carrierOfSeedCoefficients q.beta) (carrierOfSeedCoefficients q.first)
    (carrierOfSeedCoefficients q.second)

theorem primitive_active_at_good_node (q : SymbolicRow (SeedRing K))
    (hq : IsPrimitiveRow q) (x : K) (u v : SeedRing K)
    (hnode : q.atNode (MvPolynomial.C x) u v = 0) :
    q.first.eval (MvPolynomial.C x) ≠ 0 ∨ q.second.eval (MvPolynomial.C x) ≠ 0 := by
  by_contra! hz
  have hb : q.beta.eval (MvPolynomial.C x) = 0 := by
    simpa [SymbolicRow.atNode, hz.1, hz.2] using hnode
  exact Polynomial.not_isUnit_X_sub_C (MvPolynomial.C x)
    (hq _ (Polynomial.dvd_iff_isRoot.mpr hb)
      (Polynomial.dvd_iff_isRoot.mpr hz.1) (Polynomial.dvd_iff_isRoot.mpr hz.2))

private theorem carrierOfSeedCoefficients_C (c : SeedRing K) :
    carrierOfSeedCoefficients (Polynomial.C c) =
      MvPolynomial.rename seedCarrierCoordinates c := by
  have h : carrierOfSeedCoefficients.comp (Polynomial.C : SeedRing K →+* SeedCoefficients K) =
      (MvPolynomial.rename seedCarrierCoordinates).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change MvPolynomial.rename carrierCoefficientCoordinates
        ((MvPolynomial.optionEquivLeft K (Fin 2)).symm (Polynomial.C (MvPolynomial.C a))) = _
      rw [← MvPolynomial.optionEquivLeft_C, AlgEquiv.symm_apply_apply, MvPolynomial.rename_C]
      exact (MvPolynomial.rename_C _ _).symm
    · intro i
      change MvPolynomial.rename carrierCoefficientCoordinates
        ((MvPolynomial.optionEquivLeft K (Fin 2)).symm (Polynomial.C (MvPolynomial.X i))) = _
      rw [← MvPolynomial.optionEquivLeft_X_some, AlgEquiv.symm_apply_apply]
      simp [carrierCoefficientCoordinates]
  exact RingHom.congr_fun h c

private theorem carrierOfSeedCoefficients_X :
    carrierOfSeedCoefficients (Polynomial.X : SeedCoefficients K) = MvPolynomial.X 0 := by
  change MvPolynomial.rename carrierCoefficientCoordinates
    ((MvPolynomial.optionEquivLeft K (Fin 2)).symm Polynomial.X) = _
  rw [← MvPolynomial.optionEquivLeft_X_none, AlgEquiv.symm_apply_apply]
  simp [carrierCoefficientCoordinates]

private theorem specialize_seed_carrier_coeff (P R : Polynomial K) (g₀ g₁ : K)
    (c : SeedRing K) :
    Koala6844HighOrdinaryQuotient.specialize P R g₀ g₁ (retainCarrier (MvPolynomial.rename seedCarrierCoordinates c)) =
      Polynomial.C (MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g₀ g₁) c) := by
  let E := Koala6844HighOrdinaryQuotient.specialize P R g₀ g₁
  have he :
      E.toRingHom.comp (retainCarrier.toRingHom.comp (MvPolynomial.rename seedCarrierCoordinates).toRingHom)
        = Polynomial.C.comp (MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g₀ g₁)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, Koala6844HighOrdinaryQuotient.specialize, retainCarrier]
    · intro i
      fin_cases i <;>
        simp [E, Koala6844HighOrdinaryQuotient.specialize, retainCarrier, carrierCoordinates,
          seedCarrierCoordinates, Koala6844BivariateSeeds.coordinates]
  exact RingHom.congr_fun he c

theorem specialize_lifted_coeff (P R : Polynomial K) (g₀ g₁ : K)
    (c : SeedCoefficients K) :
    Koala6844HighOrdinaryQuotient.specialize P R g₀ g₁ (retainCarrier (carrierOfSeedCoefficients c)) =
      c.map (MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g₀ g₁)) := by
  let E := Koala6844HighOrdinaryQuotient.specialize P R g₀ g₁
  have he : E.toRingHom.comp (retainCarrier.toRingHom.comp carrierOfSeedCoefficients) =
      Polynomial.mapRingHom (MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g₀ g₁)) := by
    apply Polynomial.ringHom_ext
    · intro a
      change E (retainCarrier (carrierOfSeedCoefficients (Polynomial.C a))) = _
      rw [carrierOfSeedCoefficients_C]
      change E (retainCarrier (MvPolynomial.rename seedCarrierCoordinates a)) =
        (Polynomial.C a).map (MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g₀ g₁))
      rw [Polynomial.map_C]
      exact specialize_seed_carrier_coeff P R g₀ g₁ a
    · change E (retainCarrier (carrierOfSeedCoefficients Polynomial.X)) = _
      rw [carrierOfSeedCoefficients_X]
      simp [E, Koala6844HighOrdinaryQuotient.specialize, retainCarrier, carrierCoordinates]
  exact RingHom.congr_fun he c

theorem primitiveRowLift_specializes_eq (σ : K →+* K) (p : ℕ)
    (q : SymbolicRow (SeedRing K)) (selected : K → Polynomial K) (g : K) :
    Koala6844HighOrdinaryQuotient.specialize (selected g) ((selected g).map σ) g (g ^ p)
        (primitiveRowLift q) = primitiveSelected σ p q selected g := by
  simp only [primitiveRowLift, comparisonRow, map_add, map_mul, specialize_lifted_coeff,
    primitiveSelected]
  simp [Koala6844HighOrdinaryQuotient.specialize]

def atCenteredXZero : Koala6844HighOrdinary.Poly K →ₐ[K] Koala6844HighOrdinary.Poly K :=
  MvPolynomial.aeval ![0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4]

def liftSeedWord : SeedRing K →ₐ[K] Koala6844HighOrdinary.Poly K := MvPolynomial.rename seedOrdinaryCoordinates

private theorem center_lifted_coeff_seed (x u₀ v₀ u₁ v₁ : K) (c : SeedRing K) :
    atCenteredXZero (Koala6844HighOrdinaryQuotient.centerAtNode x u₀ v₀ u₁ v₁
        (retainCarrier (MvPolynomial.rename seedCarrierCoordinates c))) = liftSeedWord c := by
  let E := atCenteredXZero.comp (Koala6844HighOrdinaryQuotient.centerAtNode x u₀ v₀ u₁ v₁)
  have he : E.comp (retainCarrier.comp (MvPolynomial.rename seedCarrierCoordinates)) =
      liftSeedWord := by
    ext i
    fin_cases i <;> simp [E, atCenteredXZero, Koala6844HighOrdinaryQuotient.centerAtNode,
      retainCarrier, carrierCoordinates, seedCarrierCoordinates, liftSeedWord,
      seedOrdinaryCoordinates]
  exact DFunLike.congr_fun he c

theorem center_lifted_coeff (x u₀ v₀ u₁ v₁ : K) (c : SeedCoefficients K) :
    atCenteredXZero (Koala6844HighOrdinaryQuotient.centerAtNode x u₀ v₀ u₁ v₁
      (retainCarrier (carrierOfSeedCoefficients c))) =
      liftSeedWord (c.eval (MvPolynomial.C x)) := by
  let E := atCenteredXZero.comp (Koala6844HighOrdinaryQuotient.centerAtNode x u₀ v₀ u₁ v₁)
  have he : E.toRingHom.comp (retainCarrier.toRingHom.comp carrierOfSeedCoefficients) =
      liftSeedWord.toRingHom.comp (Polynomial.evalRingHom (MvPolynomial.C x)) := by
    apply Polynomial.ringHom_ext
    · intro a
      change E (retainCarrier (carrierOfSeedCoefficients (Polynomial.C a))) = _
      rw [carrierOfSeedCoefficients_C]
      simpa [E] using center_lifted_coeff_seed x u₀ v₀ u₁ v₁ a
    · change E (retainCarrier (carrierOfSeedCoefficients Polynomial.X)) = _
      rw [carrierOfSeedCoefficients_X]
      simp [E, atCenteredXZero, Koala6844HighOrdinaryQuotient.centerAtNode, retainCarrier,
        carrierCoordinates, liftSeedWord]
  exact RingHom.congr_fun he c

theorem liftSeedWord_injective : Function.Injective (liftSeedWord (K := K)) := by
  apply MvPolynomial.rename_injective
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [seedOrdinaryCoordinates] at hij)

theorem centered_primitive_row_at_x_zero (x u₀ v₀ u₁ v₁ : K) (q : SymbolicRow (SeedRing K))
    (hnode : q.atNode (MvPolynomial.C x) (MvPolynomial.C u₀ + MvPolynomial.X 0 * MvPolynomial.C v₀)
      (MvPolynomial.C u₁ + MvPolynomial.X 1 * MvPolynomial.C v₁) = 0) :
    atCenteredXZero (Koala6844HighOrdinaryQuotient.centerAtNode x u₀ v₀ u₁ v₁ (primitiveRowLift q)) =
      liftSeedWord (q.first.eval (MvPolynomial.C x)) * MvPolynomial.X 1 +
        liftSeedWord (q.second.eval (MvPolynomial.C x)) * MvPolynomial.X 2 := by
  have h := congrArg (liftSeedWord (K := K)) hnode
  simp only [SymbolicRow.atNode, map_zero, map_add, map_mul] at h
  have hzero (a : K) : liftSeedWord (MvPolynomial.C a) = MvPolynomial.C a := by simp [liftSeedWord]
  have hseed₀ : liftSeedWord (MvPolynomial.X 0 : SeedRing K) = MvPolynomial.X 3 := by
    simp [liftSeedWord, seedOrdinaryCoordinates]
  have hseed₁ : liftSeedWord (MvPolynomial.X 1 : SeedRing K) = MvPolynomial.X 4 := by
    simp [liftSeedWord, seedOrdinaryCoordinates]
  rw [hseed₀, hseed₁] at h
  simp only [hzero] at h
  have hv₀ : atCenteredXZero (Koala6844HighOrdinaryQuotient.centerAtNode x u₀ v₀ u₁ v₁
      (MvPolynomial.X 1 : Koala6844HighOrdinary.Poly K)) =
      MvPolynomial.X 1 + MvPolynomial.C u₀ + MvPolynomial.X 3 * MvPolynomial.C v₀ := by
    simp [atCenteredXZero, Koala6844HighOrdinaryQuotient.centerAtNode]
  have hv₁ : atCenteredXZero (Koala6844HighOrdinaryQuotient.centerAtNode x u₀ v₀ u₁ v₁
      (MvPolynomial.X 2 : Koala6844HighOrdinary.Poly K)) =
      MvPolynomial.X 2 + MvPolynomial.C u₁ + MvPolynomial.X 4 * MvPolynomial.C v₁ := by
    simp [atCenteredXZero, Koala6844HighOrdinaryQuotient.centerAtNode]
  simp only [primitiveRowLift, comparisonRow, map_add, map_mul, center_lifted_coeff, hv₀, hv₁]
  linear_combination h

end

end ProximityPrize.SubmissionLower.Koala6844Comparison
