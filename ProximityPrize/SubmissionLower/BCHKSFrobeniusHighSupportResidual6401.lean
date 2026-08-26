import ProximityPrize.SubmissionLower.BCHKSFrobeniusPrimitiveCleanup6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusSixLanePencilNoGo6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusHighSupportResidual6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusSixLanePencilNoGo6401
open BCHKSTwoFrobeniusModuleAudit6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
def firstUnchargedSupport6401 : Nat := 65537
def paddedPencilSupport6401 (h : Nat) : Nat :=
  max firstUnchargedSupport6401 (keyFirstLaneRows6401 + h + 1)
theorem highSupport_forces_h_add_delta_ge_11255_6401
    (s h delta : Nat)
    (hs : s = keyFirstLaneRows6401 + h + delta)
    (hsupport : firstUnchargedSupport6401 ≤ s) :
    11255 ≤ h + delta := by
  norm_num [firstUnchargedSupport6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401, n6401, ownerDegreeCap6401,
    bchksErrors6401] at hs hsupport ⊢
  omega
theorem highSupport_nonzeroNorm_forces_h_ge_10923_6401
    (s h delta p : Nat)
    (hs : s = keyFirstLaneRows6401 + h + delta)
    (hsupport : firstUnchargedSupport6401 ≤ s)
    (hp : p ≤ h)
    (hcharge : keyFirstLaneRows6401 + delta ≤ 5 * p) :
    10923 ≤ h := by
  have hsum := highSupport_forces_h_add_delta_ge_11255_6401
    s h delta hs hsupport
  norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
    n6401, ownerDegreeCap6401, bchksErrors6401] at hcharge
  omega
theorem nonzeroNorm_cleanup_exception_le_11651_6401
    (h p : Nat) (hh : h ≤ 22508) (hp : 10857 ≤ p) :
    h - p ≤ 11651 := by
  omega
theorem nonzeroNorm_cleanup_good_ge_65140_6401
    (delta p : Nat) (hdelta : 0 < delta) (hp : 10857 ≤ p) :
    65140 ≤ keyFirstLaneRows6401 + delta + p := by
  norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
    n6401, ownerDegreeCap6401, bchksErrors6401]
  omega
theorem polynomial_map_six_eq_self6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (P : Polynomial F) :
    (((((P.map sigma).map sigma).map sigma).map sigma).map sigma).map sigma =
      P := by
  ext n
  simp only [Polynomial.coeff_map]
  exact horder (P.coeff n)
theorem polynomialFrobeniusNormSix_map_eq6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (P : Polynomial F) :
    polynomialFrobeniusNormSix sigma (P.map sigma) =
      polynomialFrobeniusNormSix sigma P := by
  dsimp [polynomialFrobeniusNormSix]
  rw [polynomial_map_six_eq_self6401 sigma horder P]
  ring
theorem paddedPencil_norm_eq6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (h : Nat) (lambda : F) :
    polynomialFrobeniusNormSix sigma (pencilPrimitive F h lambda) =
      polynomialFrobeniusNormSix sigma
        (pencilPrimitive F h (sigma lambda)) := by
  rw [← pencilPrimitive_map sigma h lambda]
  exact (polynomialFrobeniusNormSix_map_eq6401 sigma horder
    (pencilPrimitive F h lambda)).symm
theorem paddedPencilSupport_bounds6401
    (h : Nat) (hhpos : 0 < h) (hh : h ≤ 22507) :
    firstUnchargedSupport6401 ≤ paddedPencilSupport6401 h ∧
      keyFirstLaneRows6401 + h ≤ paddedPencilSupport6401 h ∧
      paddedPencilSupport6401 h ≤ keyErrors6401 ∧
      0 < paddedPencilSupport6401 h - (keyFirstLaneRows6401 + h) := by
  dsimp [paddedPencilSupport6401, firstUnchargedSupport6401]
  norm_num [keyFirstLaneRows6401, keySecondLaneRows6401,
    keyRedundancy6401, keyErrors6401, n6401, ownerDegreeCap6401,
    bchksErrors6401]
  omega
theorem paddedPencil_exactRank_counterprofile6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (h : Nat) (hhpos : 0 < h) (hh : h ≤ 22507)
    (alpha : Fin (paddedPencilSupport6401 h) ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (lambda : F) (hlambda : lambda ≠ sigma lambda) :
    (∀ i, alpha i ^ h + lambda ≠ 0) ∧
      (sixLaneSupportSyndromeMatrix keyFirstLaneRows6401 keyErrors6401 alpha
        (sixFrobeniusErrorProfile sigma (syndromeWeight alpha)
          (fun i => alpha i ^ h + lambda))).rank =
        keyFirstLaneRows6401 + h := by
  have hb := paddedPencilSupport_bounds6401 h hhpos hh
  exact sixFrobeniusPencil_rectangular_counterprofile sigma alpha hfixed
    (syndromeWeight alpha) (fun i => syndromeWeight_ne_zero alpha i)
    (p := h) (rows := keyFirstLaneRows6401) (cols := keyErrors6401)
    (by
      norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
        n6401, ownerDegreeCap6401, bchksErrors6401] at hh ⊢
      omega)
    hb.2.1 hb.2.2.1 lambda hlambda
theorem paddedPencil_genuinePrimitive6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (h : Nat) (lambda : F)
    (hlambda : lambda ≠ sigma lambda) :
    (pencilPrimitive F h lambda).natDegree = h ∧
      (pencilPrimitive F h (sigma lambda)).natDegree = h ∧
      IsCoprime (pencilPrimitive F h lambda)
        (pencilPrimitive F h (sigma lambda)) := by
  exact sixFrobeniusPencil_primitivePair sigma h lambda hlambda
theorem hTwo_highSupport_parameters_exact6401 :
    paddedPencilSupport6401 2 = 65537 ∧
      keyFirstLaneRows6401 + 2 = 54284 ∧
      paddedPencilSupport6401 2 - (keyFirstLaneRows6401 + 2) = 11253 := by
  native_decide
abbrev PaddedSupportIndex6401 := Fin 65536 ⊕ Fin 196608
def paddedSupportCore6401 : Finset PaddedSupportIndex6401 :=
  Finset.univ.map Function.Embedding.inl
def paddedSupportFamily6401 (t : Fin 196608) :
    Finset PaddedSupportIndex6401 :=
  paddedSupportCore6401 ∪ {Sum.inr t}
theorem paddedSupportFamily_card6401 (t : Fin 196608) :
    (paddedSupportFamily6401 t).card = 65537 := by
  classical
  simp [paddedSupportFamily6401, paddedSupportCore6401]
theorem paddedSupportFamily_injective6401 :
    Function.Injective paddedSupportFamily6401 := by
  classical
  intro s t hst
  have hm : Sum.inr s ∈ paddedSupportFamily6401 t := by
    rw [← hst]
    simp [paddedSupportFamily6401]
  simpa [paddedSupportFamily6401, paddedSupportCore6401] using hm
theorem paddedSupportFamily_type_count6401 :
    87023 < Fintype.card (Fin 196608) ∧
      Fintype.card PaddedSupportIndex6401 = n6401 := by
  native_decide
noncomputable def paddedSupportFamilyEmbedding6401 (t : Fin 196608) :
    Fin 65537 ↪ PaddedSupportIndex6401 := by
  let E := paddedSupportFamily6401 t
  have hE : E.card = 65537 := paddedSupportFamily_card6401 t
  let e : Fin 65537 ≃ E := (Finset.equivFinOfCardEq hE).symm
  exact e.toEmbedding.trans (Function.Embedding.subtype _)
theorem everyPaddedSupport_has_hTwo_counterprofile6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (domain : PaddedSupportIndex6401 ↪ F)
    (hfixed : ∀ i, sigma (domain i) = domain i)
    (lambda : F) (hlambda : lambda ≠ sigma lambda) :
    ∀ t : Fin 196608,
      let alpha := (paddedSupportFamilyEmbedding6401 t).trans domain
      (∀ i, alpha i ^ 2 + lambda ≠ 0) ∧
        (sixLaneSupportSyndromeMatrix keyFirstLaneRows6401 keyErrors6401 alpha
          (sixFrobeniusErrorProfile sigma (syndromeWeight alpha)
            (fun i => alpha i ^ 2 + lambda))).rank = 54284 := by
  intro t
  let alpha := (paddedSupportFamilyEmbedding6401 t).trans domain
  have hfixedAlpha : ∀ i, sigma (alpha i) = alpha i := by
    intro i
    exact hfixed _
  have h := sixFrobeniusPencil_rectangular_counterprofile sigma alpha
    hfixedAlpha (syndromeWeight alpha)
    (fun i => syndromeWeight_ne_zero alpha i)
    (p := 2) (rows := keyFirstLaneRows6401) (cols := keyErrors6401)
    (by
      norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
        n6401, ownerDegreeCap6401, bchksErrors6401])
    (by
      norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
        n6401, ownerDegreeCap6401, bchksErrors6401])
    (by
      norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
        n6401, ownerDegreeCap6401, bchksErrors6401])
    lambda hlambda
  simpa [alpha, keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
    n6401, ownerDegreeCap6401, bchksErrors6401] using h
end BCHKSFrobeniusHighSupportResidual6401
end ProximityPrize.SubmissionLower
