import ProximityPrize.SubmissionBinaryLower.B6401Main
import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid12
/-! Original-label cost of an irreducible factor with nonzero contact derivative
at 1,482,750 agreements. Adapted from PR 694's derivative resultant. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402DerivativeFactor
open B6401Main
open Polynomial B6401Params B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6401FarkasVerifier B6401HybridP64 B6401IntFarkas
open B6401IntSmallCerts B6401T4Rows B6401T4Grid
open B6401CertsT1 B6401CertsT2 B6401CertsT3 B6401CertsT4a B6401CertsT4b1 B6401CertsT4b2
open B6401SmallAlg B6401ResLineOrd B6401QuotBridge B6401PointSurplus
open B6401Table4Common B6401Table4NonK B6401Table4K B6401ListAndMCA B6401FactorBound
open ReedSolomon ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

lemma card_le_of_contactDeriv_ne_zero
    (u₀ u₁ : Idx → Fld) {q₀ : ℕ} (hq₀ : q₀ = 1 ∨ q₀ = 2)
    {F : ContactPoly (Polynomial Fld)} (hirr : Irreducible F) (hFdeg : F.natDegree = 1)
    (hWF : wdeg wY F ≤ 13345478) (hDZ : ∀ k j i, (((F.coeff k).coeff j).coeff i).natDegree ≤ 3850)
    (hDne : contactDeriv F ≠ 0)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact F z) (P z) = 0)
    (hcard : ∀ z ∈ S, B6402HybridP64.A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, B6402HybridP64.BadOn6402 u₀ u₁ (Az z)) :
    (S.card : ℚ) ≤ (10000000000000 : ℚ) := by
  classical
  have hwY1 : 1 ≤ wY := by norm_num [wY]
  have hndvd : ¬ F ∣ contactDeriv F := by rw [dvd_contactDeriv_iff wY hwY1 hirr.ne_zero]; exact hDne
  let dD := (contactDeriv F).natDegree
  have hdD_le : dD ≤ 2 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro k hk
    rw [coeff_contactDeriv]
    have hk1 : F.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hk2 : F.coeff (k - 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [hk1, hk2, dXBi_zero, Polynomial.derivative_zero, ite_self, add_zero]
  let R_el : BiPoly (Polynomial Fld) := Polynomial.resultant F (contactDeriv F) 1 dD
  have hRel_ne : R_el ≠ 0 := by
    have hprim : F.IsPrimitive := hirr.isPrimitive (by omega)
    let ι : BiPoly (Polynomial Fld) →+* FractionRing (BiPoly (Polynomial Fld)) :=
      algebraMap (BiPoly (Polynomial Fld)) (FractionRing (BiPoly (Polynomial Fld)))
    have hι : Function.Injective ι :=
      IsFractionRing.injective (BiPoly (Polynomial Fld)) (FractionRing (BiPoly (Polynomial Fld)))
    have hirrK : Irreducible (F.map ι) := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
    have hndvdK : ¬ F.map ι ∣ (contactDeriv F).map ι := fun h =>
      hndvd (hprim.dvd_of_fraction_map_dvd_fraction_map h)
    have hcop : IsCoprime (F.map ι) ((contactDeriv F).map ι) := by
      refine EuclideanDomain.isCoprime_of_dvd (x := F.map ι) (y := (contactDeriv F).map ι) (fun h => hirrK.ne_zero h.1) ?_
      intro p hp _ hpF hpD
      rcases hpF with ⟨q, hq⟩
      rcases hirrK.isUnit_or_isUnit hq with hu | hqu
      · exact hp hu
      · rcases hqu with ⟨u, hu⟩
        have hdvd_p : F.map ι ∣ p := ⟨(u⁻¹ : _), by rw [hq, ← hu, mul_assoc, Units.mul_inv, mul_one]⟩
        exact hndvdK (hdvd_p.trans hpD)
    intro h0
    have hresK : Polynomial.resultant (F.map ι) ((contactDeriv F).map ι)
        (F.map ι).natDegree ((contactDeriv F).map ι).natDegree = 0 := by
      rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
        Polynomial.resultant_map_map, hFdeg, show Polynomial.resultant F (contactDeriv F) 1 dD = 0 from h0, map_zero]
    exact Polynomial.resultant_ne_zero _ _ hcop hresK
  have hRel_B : R_el.natDegree ≤ 36 := by
    have hW_D : wdeg wY (contactDeriv F) ≤ 13345478 := by
      have h1 := wdeg_contactDeriv_add_one_le wY hwY1 F hDne; omega
    have hdeg_coeff : ∀ (Q : ContactPoly (Polynomial Fld)), wdeg wY Q ≤ 13345478 → ∀ k, (Q.coeff k).natDegree ≤ 12 := by
      intro Q hWQ k
      by_cases hk : Q.coeff k = 0
      · simp [hk]
      · have h1 := wdegBiDom_le_of_wdeg_coeff hWQ k
        have h2 := wdegBiDom_ge_natDegree_mul wY (Q.coeff k) hk
        have hle := h2.trans h1
        have hw : wY = 1048575 := rfl
        rw [hw] at hle; omega
    unfold R_el Polynomial.resultant
    rw [Matrix.det_apply]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
    dsimp only [Function.comp_apply]
    have hsmul : ∀ (u : ℤˣ) (p : BiPoly (Polynomial Fld)), (u • p).natDegree ≤ p.natDegree := fun u p => by
      rw [Units.smul_def]; rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    refine (hsmul _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
    calc ∑ i : Fin (1 + dD), (Polynomial.sylvester F (contactDeriv F) 1 dD (σ i) i).natDegree
        ≤ ∑ _i : Fin (1 + dD), 12 := by
          apply Finset.sum_le_sum; intro i _
          simp only [Polynomial.sylvester, Matrix.of_apply]
          refine Fin.addCases (fun r => ?_) (fun r => ?_) i
          · simp only [Fin.addCases_left]; split_ifs
            · exact hdeg_coeff _ hW_D _
            · simp
          · simp only [Fin.addCases_right]; split_ifs
            · exact hdeg_coeff F hWF _
            · simp
      _ = (1 + dD) * 12 := by simp
      _ ≤ 36 := by omega
  have hRel_H : ∀ j a, ((R_el.coeff j).coeff a).natDegree ≤ 11550 := fun j a =>
    (degZ_resultant_contact_le F (contactDeriv F) 1 dD 3850 hDZ (degZ_contactDeriv_le hDZ) j a).trans
      (by omega)
  have hcurve : ∀ z ∈ S, triEval R_el z (P z) = 0 := by
    intro z hz
    have hFP := hFvan z hz
    have hDP : evalContact (evalZContact (contactDeriv F) z) (P z) = 0 := by
      rw [evalZContact_contactDeriv, evalContact_contactDeriv, hFP, Polynomial.derivative_zero]
    exact triEval_resultant_eq_zero F (contactDeriv F) 1 dD (le_of_eq hFdeg) le_rfl (by omega) z (P z) hFP hDP
  have hark := B6402HybridP64.card_le_of_biPoly_pow u₀ u₁ q₀ (by rcases hq₀ with rfl | rfl <;> omega)
    R_el 36 11550 hRel_ne hRel_B hRel_H S P Az hP hcurve hcard hmatch hbad
  refine hark.trans (max_le (by norm_num) ?_)
  rcases hq₀ with rfl | rfl <;> (unfold B6402HybridP64.arklibBoundPowQ; norm_num [N, wY, B6402HybridP64.A])


#print axioms card_le_of_contactDeriv_ne_zero
end ProximityPrize.SubmissionBinaryLower.B6402DerivativeFactor
