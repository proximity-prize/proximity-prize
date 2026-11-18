import ProximityPrize.SubmissionLower.Koala6831IntrinsicRegular
import ProximityPrize.SubmissionLower.Koala6831IntrinsicReconstruction

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open MvPolynomial RCN002 RCN065 RCN077 RCN135 RCN136 RCN229 RCN233 RCN234 RCN269 RCN347 RCN348

noncomputable section

set_option maxHeartbeats 2100000
set_option maxRecDepth 15000
set_option linter.style.haveILetI false

variable {K L : Type} [Field K] [Field L]

private def pointEval (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L) : Poly5 K →+* L :=
  MvPolynomial.eval₂Hom coeff (extendPoint v ((MvPolynomial.eval₂Hom coeff v
    (implicitRegularity F))⁻¹))

private theorem pointEval_lift (F P : Carrier K) (coeff : K →+* L) (v : Fin 4 → L) :
    pointEval F coeff v (liftFour K P) = MvPolynomial.eval₂Hom coeff v P :=
  eval_liftFour coeff v _ P

private theorem pointEval_kills (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0) :
    regularIdeal F ≤ RingHom.ker (pointEval F coeff v) := by
  change Ideal.span ({liftFour K F,
    inverseRelation K (liftFour K (implicitRegularity F))} : Set (Poly5 K)) ≤ _
  apply Ideal.span_le.mpr
  intro P hP
  change pointEval F coeff v P = 0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl
  · rwa [pointEval_lift]
  · have hu : pointEval F coeff v (MvPolynomial.X (4 : Fin 5)) =
        (MvPolynomial.eval₂Hom coeff v (implicitRegularity F))⁻¹ := by
      simp only [pointEval, MvPolynomial.eval₂Hom_X', extendPoint_last]
    rw [inverseRelation, map_sub, map_mul, map_one, pointEval_lift, hu,
      mul_inv_cancel₀ hS, sub_self]

private def pointValue (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0) :
    RegularCarrier F →+* L :=
  Ideal.Quotient.lift (regularIdeal F) (pointEval F coeff v)
    (fun _ hP => RingHom.mem_ker.mp (pointEval_kills F coeff v hF hS hP))

private theorem pointValue_image (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0) (P : Carrier K) :
    pointValue F coeff v hF hS (regularImage F P) = MvPolynomial.eval₂Hom coeff v P :=
  pointEval_lift F P coeff v

def pointTaylorPolynomial (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0) (w : ℕ) : Polynomial L :=
  jetPolynomial (regularDerivation F) (pointValue F coeff v hF hS) (w + 1)
    (regularImage F (MvPolynomial.X 1))

theorem pointTaylorPolynomial_natDegree_le (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0) (w : ℕ) :
    (pointTaylorPolynomial F coeff v hF hS w).natDegree ≤ w :=
  jetPolynomial_natDegree_le _ _ _ _

theorem pointTaylorPolynomial_coeff_zero (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0) (w : ℕ) :
    (pointTaylorPolynomial F coeff v hF hS w).coeff 0 = v 1 := by
  simp [pointTaylorPolynomial, jetPolynomial_coeff, jetCoefficient, pointValue_image]

theorem pointTaylorPolynomial_coeff_succ (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0)
    (w j : ℕ) (hj : j + 1 ≤ w) :
    (pointTaylorPolynomial F coeff v hF hS w).coeff (j + 1) =
      (MvPolynomial.eval₂Hom coeff v (tailNumerator F j) /
        (MvPolynomial.eval₂Hom coeff v (implicitRegularity F)) ^ (2 * j + 1)) /
        ((j + 1).factorial : L) := by
  have hclear := congrArg (pointValue F coeff v hF hS) (regularImage_tailNumerator F j)
  simp only [map_mul, map_pow, pointValue_image] at hclear
  rw [pointTaylorPolynomial, jetPolynomial_coeff, ite_eq_left (by omega), jetCoefficient]
  congr 1
  exact (eq_div_iff (pow_ne_zero _ hS)).mpr (by simpa only [mul_comm] using hclear.symm)

private theorem coord_eval_eq_image (F : Carrier K) :
    (MvPolynomial.eval₂Hom (algebraMap K (RegularCarrier F))
      (fun i : Fin 4 => regularImage F (MvPolynomial.X i))) = regularImage F := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [regularImage, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.rename_C]
    rfl
  · intro i
    rw [MvPolynomial.eval₂Hom_X']

theorem pointTaylorPolynomial_relation_of_persistent
    (F : Carrier K) (coeff : K →+* L) (v : Fin 4 → L)
    (w bound p : ℕ) [CharP L p]
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0)
    (htail : ∀ j ≥ w, MvPolynomial.eval₂Hom coeff v (tailNumerator F j) = 0)
    (hbound : 2 ≤ bound) (hw : w + 1 ≤ bound) (hchar : bound < p)
    (hweight : wt (![1, w, 0, 0] : Fin 4 → ℕ) F < bound) :
    MvPolynomial.eval₂Hom (Polynomial.C.comp coeff)
      (centeredGraph v (pointTaylorPolynomial F coeff v hF hS w)) F = 0 := by
  let value := pointValue F coeff v hF hS
  let D := regularDerivation F
  let coord := fun i : Fin 4 => regularImage F (MvPolynomial.X i)
  let P := pointTaylorPolynomial F coeff v hF hS w
  have hcoord (i : Fin 4) : value (coord i) = v i := by
    simp only [value, coord, pointValue_image, MvPolynomial.eval₂Hom_X']
  have hcoeff : value.comp (algebraMap K (RegularCarrier F)) = coeff := by
    apply RingHom.ext
    intro a
    have ha : (algebraMap K (RegularCarrier F)) a = regularImage F (MvPolynomial.C a) := by
      simp only [regularImage, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, MvPolynomial.rename_C]
      rfl
    simp only [RingHom.comp_apply, ha, value, pointValue_image, MvPolynomial.eval₂Hom_C]
  have hP : P.natDegree ≤ w := pointTaylorPolynomial_natDegree_le F coeff v hF hS w
  change MvPolynomial.eval₂Hom (Polynomial.C.comp coeff) (centeredGraph v P) F = 0
  have rel : MvPolynomial.eval₂Hom (Polynomial.C.comp coeff) (centeredGraph v P) F = 0 := by
    have hv (i : Fin 4) :
        jetPolynomial D value bound (coord i) = centeredGraph v P i := by
      fin_cases i
      · change jetPolynomial D value bound (coord 0) = Polynomial.C (v 0) + Polynomial.X
        simpa only [hcoord] using
          jetPolynomial_affine_coordinate D value bound hbound (coord 0) (regularDerivation_X F)
      · change jetPolynomial D value bound (coord 1) = P
        apply jetPolynomial_eq_shorter_of_tails_zero D value _ _ _ hw
        intro j hj _
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        have hz : value (regularImage F (tailNumerator F n)) = 0 := by
          simpa only [value, pointValue_image] using htail n (by omega)
        rw [regularImage_tailNumerator, map_mul, map_pow] at hz
        have hsep : value (regularImage F (implicitRegularity F)) ≠ 0 := by
          simpa only [value, pointValue_image] using hS
        have hDn := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hsep)
        change value ((D : RegularCarrier F → RegularCarrier F)^[n + 1] (coord 1)) = 0 at hDn
        simp only [jetCoefficient, hDn, zero_div]
      · exact (jetPolynomial_of_derivation_eq_zero D value bound (by omega) (coord 2)
          (regularDerivation_seeds F).1).trans (by simp [centeredGraph, hcoord])
      · exact (jetPolynomial_of_derivation_eq_zero D value bound (by omega) (coord 3)
          (regularDerivation_seeds F).2).trans (by simp [centeredGraph, hcoord])
    have hrel : MvPolynomial.eval₂Hom (algebraMap K (RegularCarrier F)) coord F = 0 := by
      rw [show coord = (fun i : Fin 4 => regularImage F (MvPolynomial.X i)) from rfl,
        coord_eval_eq_image, regularImage_carrier_zero]
    have hdeg : (MvPolynomial.eval₂Hom (Polynomial.C.comp
        (value.comp (algebraMap K (RegularCarrier F)))) (centeredGraph v P) F).natDegree < bound := by
      apply (natDegree_eval₂Hom_le_wt (![1, w, 0, 0] : Fin 4 → ℕ) F _ _ ?_).trans_lt hweight
      intro i
      fin_cases i <;> simp [centeredGraph, hP]
    have hz := polynomial_relation_of_taylor_substitution D value bound (by omega)
      (fun j hj => factorial_cast_ne_zero_below_characteristic p j (hj.trans hchar))
      coord (centeredGraph v P) hv F hrel hdeg
    rwa [hcoeff] at hz
  exact rel

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
