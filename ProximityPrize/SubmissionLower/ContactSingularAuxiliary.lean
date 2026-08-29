import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularFactorGate



/-! .

















 -/

namespace ProximityPrize.SubmissionLower.ContactSingularAuxiliary

open ContactFactorCover ContactGenericSurface ContactRegularFactorGate

noncomputable section

section GenericResultant

variable {A : Type*} [CommRing A] [IsDomain A] [IsGCDMonoid A]

/-- . -/
theorem primitive_irreducible_dvd_of_resultant_zero
    (P Q : Polynomial A) (hprimitive : P.IsPrimitive) (hP : Irreducible P)
    (hzero : Polynomial.resultant P Q P.natDegree Q.natDegree = 0) : P ∣ Q := by
  classical
  let T := FractionRing A
  let f : A →+* T := algebraMap A T
  have hf : Function.Injective f := IsFractionRing.injective A T
  have hPd : (P.map f).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf P
  have hQd : (Q.map f).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf Q
  have hfixed : Polynomial.resultant (P.map f) (Q.map f)
      P.natDegree Q.natDegree = 0 := by
    rw [Polynomial.resultant_map_map, hzero, map_zero]
  have hres : Polynomial.resultant (P.map f) (Q.map f) = 0 := by
    simpa only [hPd, hQd] using hfixed
  have hnot : ¬ IsCoprime (P.map f) (Q.map f) :=
    (Polynomial.resultant_eq_zero_iff.mp hres).2
  have hi : Irreducible (P.map f) :=
    hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hP
  exact hprimitive.dvd_of_fraction_map_dvd_fraction_map
    ((Irreducible.dvd_iff_not_isCoprime hi).mpr hnot)

theorem irreducible_resultant_nonzero
    (P Q : Polynomial A) (hP : Irreducible P) (hpos : 0 < P.natDegree)
    (hproper : ¬ P ∣ Q) :
    Polynomial.resultant P Q P.natDegree Q.natDegree ≠ 0 := by
  intro hz
  exact hproper (primitive_irreducible_dvd_of_resultant_zero P Q
    (hP.isPrimitive (Nat.ne_of_gt hpos)) hP hz)

end GenericResultant

section Construction

variable {K : Type*} [Field K]

/-- . -/
abbrev RemainingCoordinates := {i : Fin 4 // i ≠ 2}

abbrev CoefficientRing (K : Type*) [Field K] :=
  MvPolynomial RemainingCoordinates K

/-- . -/
def collectR (K : Type*) [Field K] :
    MvPolynomial (Fin 4) K ≃ₐ[K] Polynomial (CoefficientRing K) :=
  (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe (2 : Fin 4)).symm).trans
    (MvPolynomial.optionEquivLeft K RemainingCoordinates)

theorem collectR_natDegree (F : MvPolynomial (Fin 4) K) :
    (collectR K F).natDegree = F.degreeOf 2 := by
  exact (MvPolynomial.degreeOf_eq_natDegree (2 : Fin 4) F).symm

/-- . -/
def eliminateR (F G : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  (collectR K).symm (Polynomial.C
    (Polynomial.resultant (collectR K F) (collectR K G)))

theorem eliminateR_R_degree (F G : MvPolynomial (Fin 4) K) :
    (eliminateR F G).degreeOf 2 = 0 := by
  rw [← collectR_natDegree, eliminateR, AlgEquiv.apply_symm_apply,
    Polynomial.natDegree_C]

theorem eliminateR_nonzero
    (F G : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hpos : 0 < F.degreeOf 2) (hproper : ¬ F ∣ G) : eliminateR F G ≠ 0 := by
  have hi : Irreducible (collectR K F) := (MulEquiv.irreducible_iff (collectR K)).mpr hF
  have hdegree : 0 < (collectR K F).natDegree := by
    rw [collectR_natDegree]
    exact hpos
  have hnot : ¬ collectR K F ∣ collectR K G := by
    intro hd
    apply hproper
    obtain ⟨T, hT⟩ := hd
    refine ⟨(collectR K).symm T, ?_⟩
    apply (collectR K).injective
    simpa only [map_mul, AlgEquiv.apply_symm_apply] using hT
  have hres := irreducible_resultant_nonzero (collectR K F) (collectR K G)
    hi hdegree hnot
  intro hz
  have hh := congrArg (collectR K) hz
  have hc : Polynomial.C (Polynomial.resultant (collectR K F) (collectR K G)) = 0 := by
    simpa only [eliminateR, AlgEquiv.apply_symm_apply, map_zero] using hh
  exact hres (Polynomial.C_eq_zero.mp hc)

/-- . -/
theorem eliminateR_bezout (F G : MvPolynomial (Fin 4) K)
    (hpos : 0 < F.degreeOf 2) :
    ∃ A B : MvPolynomial (Fin 4) K, F * A + G * B = eliminateR F G := by
  obtain ⟨A, B, _, _, hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (collectR K F) (collectR K G) le_rfl le_rfl
      (Or.inl (by rw [collectR_natDegree]; omega))
  refine ⟨(collectR K).symm A, (collectR K).symm B, ?_⟩
  apply (collectR K).injective
  simpa only [map_add, map_mul, AlgEquiv.apply_symm_apply, eliminateR] using hab

/-- . -/
theorem eliminateR_map_zero {A : Type*} [CommRing A]
    (ψ : MvPolynomial (Fin 4) K →+* A)
    (F G : MvPolynomial (Fin 4) K) (hpos : 0 < F.degreeOf 2)
    (hF : ψ F = 0) (hG : ψ G = 0) : ψ (eliminateR F G) = 0 := by
  obtain ⟨U, V, huv⟩ := eliminateR_bezout F G hpos
  rw [← huv, map_add, map_mul, map_mul, hF, hG, zero_mul, zero_mul, zero_add]

def singularContribution (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  if F.degreeOf 2 = 0 then F else eliminateR F (MvPolynomial.pderiv (2 : Fin 4) F)

/-- . -/
def singularAuxiliary (Q : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∏ F ∈ activeFactors Q, singularContribution F

theorem singularContribution_nonzero
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (p : ℕ) [CharP K p]
    (hsmall : F.degreeOf 2 < p) : singularContribution F ≠ 0 := by
  unfold singularContribution
  split_ifs with h
  · exact hF.ne_zero
  · have hp : 0 < F.degreeOf 2 := Nat.pos_of_ne_zero h
    exact eliminateR_nonzero F _ hF hp (equation_not_dvd_R_derivative F p hp hsmall)

theorem singularContribution_R_degree (F : MvPolynomial (Fin 4) K) :
    (singularContribution F).degreeOf 2 = 0 := by
  unfold singularContribution
  split_ifs with h
  · exact h
  · exact eliminateR_R_degree F _

theorem singularAuxiliary_nonzero
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (p : ℕ) [CharP K p]
    (hsmall : Q.degreeOf 2 < p) : singularAuxiliary Q ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro F hF
  have hs := activeFactors_spec Q F hF
  apply singularContribution_nonzero F hs.1 p
  exact (ContactFactorCaps.degreeOf_le_of_dvd (2 : Fin 4) F Q hs.2.1 hQ).trans_lt hsmall

theorem singularAuxiliary_R_degree
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (p : ℕ) [CharP K p]
    (hsmall : Q.degreeOf 2 < p) : (singularAuxiliary Q).degreeOf 2 = 0 := by
  classical
  have hne : ∀ F ∈ activeFactors Q, singularContribution F ≠ 0 := by
    intro F hF
    have hs := activeFactors_spec Q F hF
    exact singularContribution_nonzero F hs.1 p
      ((ContactFactorCaps.degreeOf_le_of_dvd (2 : Fin 4) F Q hs.2.1 hQ).trans_lt hsmall)
  change (∏ F ∈ activeFactors Q, singularContribution F).degreeOf 2 = 0
  rw [MvPolynomial.degreeOf_prod_eq (n := (2 : Fin 4)) _ _ hne]
  simp only [singularContribution_R_degree, Finset.sum_const_zero]

theorem singularContribution_map_zero {A : Type*} [CommRing A]
    (ψ : MvPolynomial (Fin 4) K →+* A) (F : MvPolynomial (Fin 4) K)
    (hF : ψ F = 0) (hsingular : F.degreeOf 2 = 0 ∨ ψ (MvPolynomial.pderiv 2 F) = 0) :
    ψ (singularContribution F) = 0 := by
  unfold singularContribution
  split_ifs with h
  · exact hF
  · exact eliminateR_map_zero ψ F _ (Nat.pos_of_ne_zero h) hF
      (hsingular.resolve_left h)

theorem singularAuxiliary_map_zero {A : Type*} [CommRing A]
    (ψ : MvPolynomial (Fin 4) K →+* A) (Q F : MvPolynomial (Fin 4) K)
    (hmem : F ∈ activeFactors Q) (hF : ψ F = 0)
    (hsingular : F.degreeOf 2 = 0 ∨ ψ (MvPolynomial.pderiv 2 F) = 0) :
    ψ (singularAuxiliary Q) = 0 := by
  classical
  change ψ (∏ G ∈ activeFactors Q, singularContribution G) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero hmem
  exact singularContribution_map_zero ψ F hF hsingular

end Construction

section ActualCoverage

variable {K L : Type*} [Field K] [Field L]

/-- .
 -/
theorem surface_zero_singular_or_regular
    (φ : Polynomial K →+* L) (hφ : Function.Injective φ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (v : Fin 3 → L) (hzero : MvPolynomial.eval v (surfaceMap φ Q) = 0) :
    MvPolynomial.eval v (surfaceMap φ (singularAuxiliary Q)) = 0 ∨
      ∃ F ∈ activeFactors Q, Irreducible F ∧ 0 < F.degreeOf 2 ∧
        MvPolynomial.eval v (surfaceMap φ F) = 0 ∧
        MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv 2 F)) ≠ 0 := by
  classical
  obtain ⟨F, hF, hz⟩ := exists_active_factor_of_surface_zero φ hφ Q hQ v hzero
  by_cases hr : F.degreeOf 2 = 0
  · exact Or.inl (singularAuxiliary_map_zero
      ((MvPolynomial.eval v).comp (surfaceMap φ)) Q F hF hz (Or.inl hr))
  · rcases eq_or_ne (MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv 2 F))) 0 with hh | hh
    · exact Or.inl (singularAuxiliary_map_zero
        ((MvPolynomial.eval v).comp (surfaceMap φ)) Q F hF hz (Or.inr hh))
    · exact Or.inr ⟨F, hF, (activeFactors_spec Q F hF).1, Nat.pos_of_ne_zero hr, hz, hh⟩

end ActualCoverage


end
end ProximityPrize.SubmissionLower.ContactSingularAuxiliary
