import ProximityPrize.SubmissionLower.BCHKSRadicalMultiplicityBridge6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSNormalizedCofactorBridge6400
open Polynomial
open BCHKSRadicalMultiplicityBridge6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
theorem erase_powered_cofactor_not_isRoot
    {A iota : Type*} [CommRing A] [IsDomain A] [DecidableEq iota]
    (S : Finset iota) (f : iota -> Polynomial A) (e : iota -> Nat)
    (u : Polynomial A) (p : A)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (hunroot : ¬ u.IsRoot p)
    (q : iota) (hqS : q ∈ S) (hqroot : (f q).IsRoot p)
    (hradDerivative : ¬ (S.prod f).derivative.IsRoot p) :
    ¬ (u * (S.erase q).prod (fun i => f i ^ e i)).IsRoot p := by
  classical
  obtain ⟨-, hother⟩ :=
    radical_factor_root_multiplicities_of_derivative_not_isRoot
      S f p hf q hqS hqroot hradDerivative
  intro hroot
  rcases Polynomial.root_mul.mp hroot with huroot | hprodroot
  · exact hunroot huroot
  · obtain ⟨r, hr, hrroot⟩ :=
      (Polynomial.isRoot_prod (S.erase q) (fun i => f i ^ e i) p).mp hprodroot
    have hrS : r ∈ S := Finset.mem_of_mem_erase hr
    have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
    have hfrroot : (f r).IsRoot p := by
      rw [Polynomial.IsRoot, Polynomial.eval_pow] at hrroot
      rw [Polynomial.IsRoot]
      have her : e r ≠ 0 := by
        intro he
        simp [he] at hrroot
      exact (pow_eq_zero_iff her).mp hrroot
    have hrzero := hother r hrS hrq
    exact (hf r hrS) ((Polynomial.rootMultiplicity_eq_zero_iff.mp hrzero) hfrroot)
theorem powered_product_eq_erased_cofactor_mul
    {A iota : Type*} [CommMonoid A] [DecidableEq iota]
    (S : Finset iota) (f : iota -> A) (e : iota -> Nat)
    (u : A) (q : iota) (hqS : q ∈ S) :
    u * S.prod (fun i => f i ^ e i) =
      (u * (S.erase q).prod (fun i => f i ^ e i)) * f q ^ e q := by
  rw [← Finset.prod_erase_mul S (fun i => f i ^ e i) hqS]
  ac_rfl
theorem exists_normalized_rootfree_cofactor_at_specialization
    {F : Type*} [Field F]
    [NormalizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    [UniqueFactorizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (z : F) (P : Polynomial F)
    (hRadpos : 0 < (positiveNormalizedRadical Q).natDegree)
    (hres : (globalRadicalResultant (positiveNormalizedRadical Q)).map
      (Polynomial.evalRingHom z) ≠ 0)
    (hcontent : BCHKSSubstitutionVanish.specializeZ
      (zeroDegreeNormalizedPart Q) z ≠ 0)
    (q : Polynomial (Polynomial (Polynomial F)))
    (hqS : q ∈ positiveNormalizedFactors Q)
    (hqroot : (BCHKSSubstitutionVanish.specializeZ q z).IsRoot P) :
    ∃ C : Polynomial (Polynomial (Polynomial F)),
      Q = C * q ^ normalizedFactorExponent Q q ∧
      C ≠ 0 ∧ BCHKSSubstitutionVanish.triEval C z P ≠ 0 := by
  classical
  let Rad := positiveNormalizedRadical Q
  let S := positiveNormalizedFactors Q
  let f : Polynomial (Polynomial (Polynomial F)) →
      Polynomial (Polynomial F) := fun H ↦
    BCHKSSubstitutionVanish.specializeZ H z
  let e : Polynomial (Polynomial (Polynomial F)) → ℕ := fun H ↦
    normalizedFactorExponent Q H
  let Φ : Polynomial (Polynomial (Polynomial F)) →+*
      Polynomial (Polynomial F) :=
    Polynomial.mapRingHom
      (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  obtain ⟨v, hfactor, houterZero⟩ :=
    exists_unit_mul_zeroPart_mul_positiveFactors Q hQ
  let Outer : Polynomial (Polynomial (Polynomial F)) :=
    (v : Polynomial (Polynomial (Polynomial F))) * zeroDegreeNormalizedPart Q
  let u : Polynomial (Polynomial F) :=
    BCHKSSubstitutionVanish.specializeZ Outer z
  let C : Polynomial (Polynomial (Polynomial F)) :=
    Outer * (S.erase q).prod (fun H ↦ H ^ e H)
  have hRad : BCHKSSubstitutionVanish.specializeZ Rad z = S.prod f := by
    change Φ (S.prod id) = S.prod f
    rw [map_prod Φ id S]
    rfl
  have hRadZ : BCHKSSubstitutionVanish.specializeZ Rad z ≠ 0 := by
    intro hzero
    have hroot :
        (BCHKSSubstitutionVanish.specializeZ Rad z).IsRoot P := by
      simp [hzero]
    have hnot :=
      specialized_radical_derivative_not_isRoot_of_resultant_ne_zero
        Rad z P hRadpos hres hroot
    apply hnot
    simp [hzero]
  have hf : ∀ H ∈ S, f H ≠ 0 := by
    have hprod : S.prod f ≠ 0 := by simpa [hRad] using hRadZ
    exact Finset.prod_ne_zero_iff.mp hprod
  have hu : u ≠ 0 := by
    change Φ ((v : Polynomial (Polynomial (Polynomial F))) *
      zeroDegreeNormalizedPart Q) ≠ 0
    rw [map_mul]
    apply mul_ne_zero
    · exact (v.isUnit.map Φ).ne_zero
    · simpa [Φ, BCHKSSubstitutionVanish.specializeZ] using hcontent
  have huDegree : u.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Polynomial.natDegree_map_le.trans
      (by simpa [Outer] using houterZero.le)
  have hunroot : ¬ u.IsRoot P := by
    have huC : u = Polynomial.C (u.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero huDegree
    rw [huC]
    apply Polynomial.not_isRoot_C
    intro hcoeff
    apply hu
    rw [huC, hcoeff, Polynomial.C_0]
  have hradroot : (S.prod f).IsRoot P :=
    (Polynomial.isRoot_prod S f P).2 ⟨q, hqS, hqroot⟩
  have hrawDerivative :=
    specialized_radical_derivative_not_isRoot_of_resultant_ne_zero
      Rad z P hRadpos hres (by simpa [hRad] using hradroot)
  have hradDerivative : ¬ (S.prod f).derivative.IsRoot P := by
    intro hder
    apply hrawDerivative
    simpa [hRad] using hder
  have hspecializedC :
      BCHKSSubstitutionVanish.specializeZ C z =
        u * (S.erase q).prod (fun H ↦ f H ^ e H) := by
    change Φ (Outer * (S.erase q).prod (fun H ↦ H ^ e H)) = _
    rw [map_mul, map_prod Φ (fun H ↦ H ^ e H) (S.erase q)]
    congr 1
    apply Finset.prod_congr rfl
    intro H hH
    simp [f, e, Φ, BCHKSSubstitutionVanish.specializeZ]
  have hspecializedCrootfree :
      ¬ (BCHKSSubstitutionVanish.specializeZ C z).IsRoot P := by
    rw [hspecializedC]
    exact erase_powered_cofactor_not_isRoot
      S f e u P hf hunroot q hqS hqroot hradDerivative
  have hQC : Q = C * q ^ normalizedFactorExponent Q q := by
    calc
      Q = Outer * S.prod (fun H ↦ H ^ e H) := by
        simpa [Outer, S, e] using hfactor
      _ = C * q ^ e q := by
        simpa [C] using
          powered_product_eq_erased_cofactor_mul S id e Outer q hqS
      _ = C * q ^ normalizedFactorExponent Q q := by rfl
  refine ⟨C, hQC, ?_, ?_⟩
  · intro hC
    apply hQ
    rw [hQC, hC, zero_mul]
  · intro htri
    apply hspecializedCrootfree
    simpa [Polynomial.IsRoot, BCHKSSubstitutionVanish.triEval] using htri
end BCHKSNormalizedCofactorBridge6400
end ProximityPrize.SubmissionLower
