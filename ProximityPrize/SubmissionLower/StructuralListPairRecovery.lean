import ProximityPrize.SubmissionLower.StructuralListPairImages
import ProximityPrize.SubmissionLower.ShortenChart

set_option Elab.async false
set_option maxRecDepth 6000

namespace StructuralList

open CJ0 CJ0_4 MvPolynomial
open private chartMap_recover jetForm readJet_eq from ProximityPrize.SubmissionLower.ListProofA

noncomputable section

/-- The new chart has the same input coordinates as the native polynomial jet. -/
theorem input_eq_nativeJet (T : Chart 2) (hT : ChartOK T) (f : Polynomial K)
    (hf : f.degree < k) {y : Fin 3 → Geo} (hy : y ∈ T.locus) (hfy : T.output y = coeffPoint f) :
    y = CJ0_3.nativeJet f := by
  funext i
  rw [← hT.recover y hy i, hfy]
  have hfm : (f.map embed).degree < k := by
    rw [Polynomial.degree_map_eq_of_injective embed.injective]
    exact hf
  change (∑ a : Fin k, (a.val.choose i.val : Geo) * center^(a.val-i.val) * embed (f.coeff a.val)) = _
  simp_rw [← Polynomial.coeff_map]
  exact readJet_eq _ hfm _

/-- Restricting the source ideal preserves the dimension of a chart that recovers its input. -/
theorem componentDimension (T : Chart 2) (hT : ChartOK T) (P : Ideal (InitialRing 2))
    (hP : P.IsPrime) (hE : sourceIdeal T ≤ P) (hD : T.denominator ∉ P) :
    (affineHilbertPolynomial (componentIdeal T P)).natDegree = (affineHilbertPolynomial P).natDegree := by
  let := hP
  let : (sourceIdeal T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  let φ := Ideal.Quotient.liftₐ (sourceIdeal T) (Ideal.Quotient.mkₐ Geo P)
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hE hx))
  let j := IsScalarTower.toAlgHom Geo (InitialRing 2 ⧸ P) (ComponentOpen T P)
  have hunit : IsUnit ((j.comp φ) (Ideal.Quotient.mk (sourceIdeal T) T.denominator)) :=
    IsLocalization.Away.algebraMap_isUnit (S := ComponentOpen T P) (Ideal.Quotient.mk P T.denominator)
  let ψ : ChartOpen T →ₐ[Geo] ComponentOpen T P :=
    IsLocalization.Away.liftAlgHom (f := j.comp φ)
      (Ideal.Quotient.mk (sourceIdeal T) T.denominator) hunit
  have hmap (q : InitialRing 2) : ψ (localize T q) = componentLocalize T P q :=
    IsLocalization.Away.lift_eq (g := (j.comp φ).toRingHom)
      (Ideal.Quotient.mk (sourceIdeal T) T.denominator) hunit (Ideal.Quotient.mk (sourceIdeal T) q)
  have hδ : IsUnit (componentLocalize T P T.denominator) := hunit
  have hInv : ψ (invDenom T) = componentInvDenom T P := by
    have hh := congrArg ψ (denom_mul_inv T)
    rw [map_mul, hmap, map_one] at hh
    exact hδ.mul_left_cancel (hh.trans (componentDenom_mul_inv T P).symm)
  have hcomp : ψ.comp (chartMap T) = componentMap T P := by
    apply MvPolynomial.algHom_ext
    intro i
    change ψ (chartMap T (MvPolynomial.X i)) = componentMap T P (MvPolynomial.X i)
    rw [chartMap, componentMap, aeval_X, aeval_X, map_mul, hmap, hInv]
  have hOrig := chartMap_recover T hT (fun h => hD (hE h))
  have hrec (q : InitialRing 2) : componentMap T P (aeval (fun i : Fin 3 => jetForm i.val) q) = componentLocalize T P q := by
    rw [← hcomp]
    change ψ ((chartMap T) (aeval (fun i : Fin 3 => jetForm i.val) q)) = _
    rw [show chartMap T (aeval (fun i : Fin 3 => jetForm i.val) q) = localize T q from
      DFunLike.congr_fun hOrig q, hmap]
  have hne : Ideal.Quotient.mk P T.denominator ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  have hdim := natDegree_affineHilbertPolynomial_le_of_away_range P T.denominator
    (IsRegular.of_ne_zero hne).1 (componentMap T P) (fun q => ⟨_, hrec q⟩) le_rfl
  exact le_antisymm (componentGeometry T P hP hD).2 hdim

end

end StructuralList
