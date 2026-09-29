import ProximityPrize.SubmissionLower.MovingSourceNativeFactor6814

/-! Exhaustive algebraic owner split for two actual source polynomials.
The unique-owner arm produces nonvanishing cofactors; the mixed arm
produces genuinely coprime root-owning factors. -/
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerSplit6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN137 WholeSpaceCube6814
open SecondJetCoefficients UniqueCurvatureOwner6814

variable {K E : Type} [Field K] [Field E]
local notation "Poly" => MvPolynomial (Fin 5) K

def UniqueOwner (ev : Poly →+* E) (J P : Poly) : Prop :=
  ∀ D, Irreducible D → D∣P → ev D=0 → Associated D J

theorem unique_owner_remainder (ev : Poly →+* E) (P J : Poly)
    (hP : P≠0) (hJ : Irreducible J) (hu : UniqueOwner ev J P) :
    ∃ e Q, P=J^e*Q ∧ ev Q≠0 := by
  obtain ⟨e,Q,hnot,hEq⟩ := WfDvdMonoid.max_power_factor hP hJ
  have hQ : Q≠0 := by intro hz; apply hP; rw [hEq,hz,mul_zero]
  refine ⟨e,Q,hEq,?_⟩
  intro hz
  obtain ⟨D,hD,hDz⟩ := exists_normalizedFactorSet_zero ev Q hQ hz
  have hd := normalizedFactorSet_spec Q D hD
  have hDP : D∣P := hd.2.trans (by rw [hEq]; exact dvd_mul_left _ _)
  exact hnot (((hu D hd.1 hDP hDz).symm.dvd).trans hd.2)

theorem two_source_owner_split (ev : Poly →+* E) (P Q : Poly)
    (hP : P≠0) (hQ : Q≠0) (hz : ev P=0) :
    ∃ J, Irreducible J ∧ J∣P ∧ ev J=0 ∧
      ((UniqueOwner ev J P ∧ UniqueOwner ev J Q ∧
          (∃ e R, P=J^e*R ∧ ev R≠0) ∧ (∃ e R, Q=J^e*R ∧ ev R≠0)) ∨
        ∃ D, Irreducible D ∧ (D∣P ∨ D∣Q) ∧ ev D=0 ∧ IsRelPrime J D) := by
  classical
  obtain ⟨J,hJ,hJz⟩ := exists_normalizedFactorSet_zero ev P hP hz
  have hj := normalizedFactorSet_spec P J hJ
  refine ⟨J,hj.1,hj.2,hJz,?_⟩
  rcases Classical.em (∃ D, Irreducible D ∧ (D∣P ∨ D∣Q) ∧ ev D=0 ∧ ¬Associated D J) with hex | hex
  · right
    obtain ⟨D,hD,hd,hzD,hnot⟩ := hex
    refine ⟨D,hD,hd,hzD,hj.1.isRelPrime_iff_not_dvd.mpr ?_⟩
    intro hdiv
    exact hnot (hj.1.associated_of_dvd hD hdiv).symm
  · have hp : UniqueOwner ev J P := by
      intro D hD hd hzD
      by_contra hn
      exact hex ⟨D,hD,Or.inl hd,hzD,hn⟩
    have hq : UniqueOwner ev J Q := by
      intro D hD hd hzD
      by_contra hn
      exact hex ⟨D,hD,Or.inr hd,hzD,hn⟩
    exact Or.inl ⟨hp,hq,unique_owner_remainder ev P J hP hj.1 hp,
      unique_owner_remainder ev Q J hQ hj.1 hq⟩

def rootPolynomialMap (phi : MvPolynomial (Fin 4) K →+* E) : Poly →+* Polynomial E :=
  (Polynomial.mapRingHom phi).comp (asS (K:=K)).toRingHom

def rootEvaluation (phi : MvPolynomial (Fin 4) K →+* E) (z : E) : Poly →+* E :=
  (Polynomial.evalRingHom z).comp (rootPolynomialMap phi)

/-- Both the multiplicity charge and every degree charge belong to the
SAME exponent e. No independent degree allocations are substituted. -/
theorem unique_owner_charges
    (phi : MvPolynomial (Fin 4) K →+* E) (z : E) (P J : Poly)
    (hP : P≠0) (hJ : Irreducible J) (hu : UniqueOwner (rootEvaluation phi z) J P)
    (d m : ℕ) (hJne : rootPolynomialMap phi J≠0)
    (hroot : (rootPolynomialMap phi J).rootMultiplicity z=m)
    (hpower : (Polynomial.X-Polynomial.C z)^d ∣ rootPolynomialMap phi P) :
    ∃ e, d≤e*m ∧
      (∀ w : Fin 5 → ℕ, e*weightedTotalDegree w J≤weightedTotalDegree w P) ∧
      e*J.degreeOf 1≤P.degreeOf 1 := by
  obtain ⟨e,Q,hEq,hQroot⟩ := unique_owner_remainder (rootEvaluation phi z) P J hP hJ hu
  have hQ : Q≠0 := by intro hz; apply hQroot; rw [hz,map_zero]
  have hp := hpower
  rw [hEq,map_mul,map_pow] at hp
  have hm := unique_owner_order_le (rootPolynomialMap phi J) (rootPolynomialMap phi Q)
    z d e hJne hQroot hp
  rw [hroot] at hm
  refine ⟨e,hm,?_,?_⟩
  · intro w
    rw [hEq,weight_mul _ _ _ (pow_ne_zero _ hJ.ne_zero) hQ,weight_pow _ _ hJ.ne_zero]
    omega
  · rw [hEq,MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ hJ.ne_zero) hQ,
      MvPolynomial.degreeOf_pow_eq _ _ _ hJ.ne_zero]
    omega

#print axioms two_source_owner_split
#print axioms unique_owner_charges
end
end ProximityPrize.SubmissionLower.MovingSourceOwnerSplit6814
