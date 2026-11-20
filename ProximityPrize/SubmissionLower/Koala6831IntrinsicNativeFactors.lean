import ProximityPrize.SubmissionLower.Koala6831OrdinaryTestAdapter



namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open Koala6831Ordinary (ordinarySurface ordinarySurface_injective
  ordinarySurface_degree_caps ordinaryPoint eval_ordinarySurface ordinarySurface_implicitRegularity)
open RCN137 MvPolynomial
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4500000

variable {K : Type} [Field K]

theorem native_factor_weight_le (weights : Fin 4 → ℕ) (Q F : Carrier K) (hQ : Q ≠ 0)
    (hF : F ∈ normalizedFactorSet Q) :
    weightedTotalDegree weights F ≤ weightedTotalDegree weights Q :=
  RCN081.weightedTotalDegree_le_of_dvd weights F Q (normalizedFactorSet_spec Q F hF).2 hQ

theorem native_factor_weight_sum_le (weights : Fin 4 → ℕ) (Q : Carrier K) (hQ : Q ≠ 0) :
    (∑ F ∈ normalizedFactorSet Q, weightedTotalDegree weights F) ≤ weightedTotalDegree weights Q := by
  calc
    _ = weightedTotalDegree weights (∏ F ∈ normalizedFactorSet Q, F) := by
      simpa only [id_eq] using (RCN071.weightedTotalDegree_prod_eq weights (normalizedFactorSet Q) id
        (fun F hF => (normalizedFactorSet_spec Q F hF).1.ne_zero)).symm
    _ ≤ _ := RCN081.weightedTotalDegree_le_of_dvd weights _ Q (normalizedFactorSet_product_dvd Q hQ) hQ

private def valueWeights : Fin 4 → ℕ := ![0, 1, 0, 0]

private def totalSurfaceWeights : Fin 4 → ℕ := ![0, 1, 1, 1]

private theorem degree_caps_of_native_weights (F : Carrier K) (y t : ℕ)
    (hy : weightedTotalDegree valueWeights F ≤ y)
    (ht : weightedTotalDegree totalSurfaceWeights F ≤ t) :
    ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t := by
  intro d hd
  have hdy := (MvPolynomial.le_weightedTotalDegree valueWeights hd).trans hy
  have hdt := (MvPolynomial.le_weightedTotalDegree totalSurfaceWeights hd).trans ht
  rw [RCN081.weight_fin4] at hdy hdt
  exact ⟨by simpa [valueWeights] using hdy, by simpa [totalSurfaceWeights, Nat.add_assoc] using hdt⟩

private theorem native_weights_of_degree_caps (F : Carrier K) (y t : ℕ)
    (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t) :
    weightedTotalDegree valueWeights F ≤ y ∧ weightedTotalDegree totalSurfaceWeights F ≤ t := by
  constructor
  · apply (RCN081.weightedTotalDegree_le_iff valueWeights F y).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa [valueWeights] using (hcap d hd).1
  · apply (RCN081.weightedTotalDegree_le_iff totalSurfaceWeights F t).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa [totalSurfaceWeights, Nat.add_assoc] using (hcap d hd).2


private theorem rational_ordinarySurface_irreducible (F : Carrier K) (hirr : Irreducible F)
    (hpos : 0 < (ordinarySurface (algebraMap (Polynomial K) (RCN132.RationalCoefficients K)) F).degreeOf 1) :
    Irreducible (ordinarySurface (algebraMap (Polynomial K) (RCN132.RationalCoefficients K)) F) := by
  let E := RCN132.RationalCoefficients K
  let φ := algebraMap (Polynomial K) E
  have hd (d : Fin 4 →₀ ℕ) (h : d ∈ F.support) : d 1 ≤ F.degreeOf 1 :=
    MvPolynomial.monomial_le_degreeOf 1 h
  have ht (d : Fin 4 →₀ ℕ) (h : d ∈ F.support) :
      d 1 + d 2 + d 3 ≤ weightedTotalDegree totalSurfaceWeights F := by
    have hw := MvPolynomial.le_weightedTotalDegree totalSurfaceWeights h
    rw [RCN081.weight_fin4] at hw
    simpa [totalSurfaceWeights, Nat.add_assoc] using hw
  have hvalue := (ordinarySurface_degree_caps φ F (F.degreeOf 1)
    (weightedTotalDegree totalSurfaceWeights F) (fun d hdF => ⟨hd d hdF, ht d hdF⟩)).1
  have hn : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 :=
    (hpos.trans_le hvalue).trans_le ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hsurface := RCN132.rationalSurfaceMap_irreducible K F hirr hn
  change Irreducible ((MvPolynomial.renameEquiv E (Equiv.swap (0 : Fin 3) 1))
    (RCN132.rationalSurfaceMap K F))
  exact (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv E (Equiv.swap (0 : Fin 3) 1))).mpr hsurface

theorem native_regular_cover_after_singular_discard
    (p : ℕ) [CharP K p] (Q : Carrier K) (hQ : Q ≠ 0) (y t : ℕ)
    (hy : y < p) (ht : t < p) (hSylvester : (2 * y - 1) * t < p)
    (hcap : ∀ d ∈ Q.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hvanish : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ p) Q = 0) :
    ∃ bad : Finset K, bad ⊆ seeds ∧ bad.card ≤ p * (2 * y + 2) * t ∧
      ∀ g ∈ seeds \ bad, ∃ F ∈ normalizedFactorSet Q,
        graphSpecialize (selected g) g (g ^ p) F = 0 ∧
          graphSpecialize (selected g) g (g ^ p) (implicitRegularity F) ≠ 0 := by
  classical
  let E := RCN132.RationalCoefficients K
  let φ := algebraMap (Polynomial K) E
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  let eChar : CharP E p :=
    charP_of_injective_ringHom (f := φ.comp Polynomial.C) (hφ.comp Polynomial.C_injective) _
  obtain ⟨hweightY, hweightT⟩ := native_weights_of_degree_caps Q y t hcap
  let sing (F : Carrier K) := seeds.filter (fun g =>
    graphSpecialize (selected g) g (g ^ p) F = 0 ∧
      graphSpecialize (selected g) g (g ^ p) (implicitRegularity F) = 0)
  have hcount (F : Carrier K) (hF : F ∈ normalizedFactorSet Q) :
      (sing F).card ≤ p * (2 * y + 2) * weightedTotalDegree totalSurfaceWeights F := by
    let G := ordinarySurface φ F
    have hirr := (normalizedFactorSet_spec Q F hF).1
    have hGn : G ≠ 0 := fun hz =>
      hirr.ne_zero (ordinarySurface_injective φ hφ (by simpa only [map_zero] using hz))
    have hFtotal := (native_factor_weight_le totalSurfaceWeights Q F hQ hF).trans hweightT
    have hcF : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ weightedTotalDegree totalSurfaceWeights F :=
      degree_caps_of_native_weights F y _ ((native_factor_weight_le valueWeights Q F hQ hF).trans hweightY) le_rfl
    obtain ⟨hGy, hGt⟩ := ordinarySurface_degree_caps φ F y (weightedTotalDegree totalSurfaceWeights F) hcF
    change G.degreeOf (1 : Fin 3) ≤ y at hGy
    change G.totalDegree ≤ weightedTotalDegree totalSurfaceWeights F at hGt
    let point := ordinaryPoint φ selected p
    have haver (g : K) (D : Carrier K) : MvPolynomial.eval (point g) (ordinarySurface φ D) =
        φ (graphSpecialize (selected g) g (g ^ p) D) :=
      eval_ordinarySurface φ selected p g D
    have hroot (g : K) (hg : g ∈ sing F) : MvPolynomial.eval (point g) G = 0 := by
      rw [show G = ordinarySurface φ F from rfl, haver, (Finset.mem_filter.mp hg).2.1, map_zero]
    have hsing (g : K) (hg : g ∈ sing F) :
        MvPolynomial.eval (point g) (MvPolynomial.pderiv 1 G) = 0 := by
      change MvPolynomial.eval (point g) (MvPolynomial.pderiv 1 (ordinarySurface φ F)) = 0
      rw [← ordinarySurface_implicitRegularity, haver, (Finset.mem_filter.mp hg).2.2, map_zero]
    by_cases h0 : G.degreeOf (1 : Fin 3) = 0
    · have hb := Koala6831OrdinaryFactorExceptions.pure_embedded_seed_card_le
        (p := p) (φ.comp Polynomial.C) G hGn h0 (hGt.trans_lt (hFtotal.trans_lt ht))
        (sing F) (φ ∘ selected) hroot
      have hp : p ≤ p * (2 * y + 2) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left p (show 1 ≤ 2 * y + 2 by omega)
      exact hb.trans (Nat.mul_le_mul hp hGt)
    · have hres : (2 * G.degreeOf 1 - 1) * G.totalDegree ≤ (2 * y - 1) * t :=
        Nat.mul_le_mul (by omega) (hGt.trans hFtotal)
      have hb := Koala6831OrdinaryFactorExceptions.singular_embedded_seed_card_le
        (p := p) (φ.comp Polynomial.C) G (rational_ordinarySurface_irreducible F hirr (Nat.pos_of_ne_zero h0))
        (Nat.pos_of_ne_zero h0) (hGy.trans_lt hy) (hres.trans_lt hSylvester)
        (sing F) (φ ∘ selected) hroot hsing
      rw [← Nat.mul_assoc] at hb
      exact hb.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hGt)
  let bad := (normalizedFactorSet Q).biUnion sing
  refine ⟨bad, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨F, _, hmem⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp hmem).1
  · calc
      bad.card ≤ ∑ F ∈ normalizedFactorSet Q, (sing F).card := Finset.card_biUnion_le
      _ ≤ ∑ F ∈ normalizedFactorSet Q, p * (2 * y + 2) * weightedTotalDegree totalSurfaceWeights F :=
        Finset.sum_le_sum hcount
      _ = p * (2 * y + 2) * (∑ F ∈ normalizedFactorSet Q, weightedTotalDegree totalSurfaceWeights F) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_left _
        ((native_factor_weight_sum_le totalSurfaceWeights Q hQ).trans hweightT)
  · intro g hg
    obtain ⟨hgseed, hgnot⟩ := Finset.mem_sdiff.mp hg
    obtain ⟨F, hF, hz⟩ :=
      exists_normalizedFactorSet_zero (graphSpecialize (selected g) g (g ^ p)) Q hQ (hvanish g hgseed)
    refine ⟨F, hF, hz, fun hsing => hgnot ?_⟩
    exact Finset.mem_biUnion.mpr ⟨F, hF, Finset.mem_filter.mpr ⟨hgseed, hz, hsing⟩⟩

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic

