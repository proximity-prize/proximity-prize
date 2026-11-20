import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast019
import ProximityPrize.SubmissionLower.Fast020
set_option Elab.async false

section PackSource_K1_13_6_1_4Geometry
set_option autoImplicit true
namespace K1_13_6_1_4

noncomputable section

open MvPolynomial K1_13 K1_13_6 K1_13_6_1 K1_13_7_1

private theorem krullDim_of_polynomial_normalization {k R : Type*} [Field k]
    [CommRing R] [IsDomain R] {d : ℕ} [Algebra (MvPolynomial (Fin d) k) R]
    [FaithfulSMul (MvPolynomial (Fin d) k) R] [Module.Finite (MvPolynomial (Fin d) k) R] :
    ringKrullDim R = (d : WithBot ℕ∞) := by
  let B := MvPolynomial (Fin d) k
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [← hB]
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B R))
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (show x.asIdeal < y.asIdeal from hxy)
  · obtain ⟨b, hb, hd⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
    obtain ⟨z, hz⟩ :=
      Algebra.IsIntegral.comap_surjective B R (⟨b, hb⟩ : PrimeSpectrum B)
    have hz' : z.asIdeal.under B = b := congrArg PrimeSpectrum.asIdeal hz
    have hle := Ideal.height_under_le_height (R := B) z.asIdeal
    rw [hz'] at hle
    calc
      ringKrullDim B = (d : WithBot ℕ∞) := hB
      _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hd.trans hle)
      _ ≤ ringKrullDim R := Ideal.height_le_ringKrullDim_of_isPrime

private theorem krullDim_of_finite_hom {k R : Type*} [Field k] [CommRing R] [IsDomain R]
    {d : ℕ} (g : MvPolynomial (Fin d) k →+* R) (hg : Function.Injective g)
    (hgfin : g.Finite) : ringKrullDim R = (d : WithBot ℕ∞) := by
  let algebra := g.toAlgebra
  let := algebra
  let faithful : FaithfulSMul (MvPolynomial (Fin d) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let finite : Module.Finite (MvPolynomial (Fin d) k) R := hgfin
  exact @krullDim_of_polynomial_normalization k R _ _ _ d algebra faithful finite

private theorem dim_eq_Hilbert {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    ringKrullDim (MvPolynomial σ k ⧸ I) =
      ((affineHilbertPolynomial I).natDegree : WithBot ℕ∞) := by
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hH := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgfin hg
  rw [Nat.card_fin] at hH
  rw [hH]
  exact krullDim_of_finite_hom g.toRingHom hg hgfin

/-- A proper complete intersection of two equations in four jets is pure of dimension two. -/
theorem pair_dimension {F G : GeoJets} (hF : F ≠ 0) (hproper : IsRelPrime F G)
    {surface : Ideal GeoJets} (hZ : (pairIdeal F G).IsMinimalPrime surface) :
    ringKrullDim (GeoJets ⧸ surface) = 2 := by
  let := hZ.isPrime
  have hFZ : Ideal.span {F} ≤ surface :=
    le_trans (Ideal.span_mono (by simp)) hZ.le
  obtain ⟨D, hD, hDZ⟩ := Ideal.exists_minimalPrimes_le hFZ
  let := hD.isPrime
  have hD0 : D ≠ ⊥ := fun e =>
    hF (Ideal.mem_bot.mp (e ▸ hD.le (Ideal.subset_span (by simp))))
  have hDh : D.height = 1 :=
    le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ D hD)
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hD0))
  obtain ⟨a, ha, hap⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hD.isPrime hD0
  have heq := Ideal.eq_span_singleton_of_height_eq_one hDh ha hap
  have hGD : G ∉ D := by
    intro hG
    have hFa : a ∣ F := Ideal.mem_span_singleton.mp (heq ▸ hD.le (Ideal.subset_span (by simp)))
    have hGa : a ∣ G := Ideal.mem_span_singleton.mp (heq ▸ hG)
    exact hap.not_isUnit (hproper hFa hGa)
  have hpair : pairIdeal F G ≤ D ⊔ Ideal.span {G} := by
    rw [pairIdeal, Ideal.span_insert]
    exact sup_le (hD.le.trans le_sup_left) le_sup_right
  have hcut : (D ⊔ Ideal.span {G}).IsMinimalPrime surface :=
    ⟨⟨hZ.isPrime, sup_le hDZ ((Ideal.span_mono (by simp)).trans hZ.le)⟩,
      fun J hJ hJZ => hZ.2 ⟨hJ.1, hpair.trans hJ.2⟩ hJZ⟩
  have hDdeg := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
  have hZdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hGD hcut
  rw [Nat.card_fin] at hDdeg
  have hdeg : (affineHilbertPolynomial surface).natDegree = 2 := by omega
  simp [dim_eq_Hilbert surface, hdeg]

theorem curve_of_proper_cut {f P : Row 4} {surface C : Ideal GeoJets}
    (hZ : surface.IsPrime) (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (hf : toGeneric f ∈ surface) (hP : toGeneric P ∉ surface)
    (hC : (divisorIdeal surface P).IsMinimalPrime C) : CurveOnFactor f C := by
  let := hZ
  let := hC.isPrime
  have hZdeg : (affineHilbertPolynomial surface).natDegree = 2 := by
    have hd := (dim_eq_Hilbert surface).symm.trans hdim
    exact_mod_cast hd
  have hCdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hP hC
  have hd : (affineHilbertPolynomial C).natDegree = 1 := by omega
  have hle : surface ≤ C := (show surface ≤ divisorIdeal surface P from le_sup_left).trans hC.le
  exact ⟨hC.isPrime, by simp [dim_eq_Hilbert C, hd], hle hf⟩

end
end K1_13_6_1_4
end PackSource_K1_13_6_1_4Geometry
