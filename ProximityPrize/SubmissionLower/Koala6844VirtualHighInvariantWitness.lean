import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantDerivatives
import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartWitness


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic RCN188 Function

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

theorem persistent_raw_tails_from_trim (F V W S theta : Carrier K)
    (coeff : K →+* L) (x : Fin 4 → L)
    (carrier : MvPolynomial.eval₂Hom coeff x F = 0)
    (regular : MvPolynomial.eval₂Hom coeff x (implicitRegularity F) ≠ 0)
    (divisor_ne : MvPolynomial.eval₂Hom coeff x V ≠ 0)
    (seed_ne : MvPolynomial.eval₂Hom coeff x S ≠ 0)
    (shape : W = S * MvPolynomial.X 1 - theta)
    (fixed : regularDerivation F (regularImage F S) = 0)
    (trimDegree divisorDegree remainderDegree plainDegree : ℕ)
    (hdegree : trimDegree+divisorDegree ≤ plainDegree)
    (hremDegree : remainderDegree ≤ plainDegree)
    (later : ∀ j ≥ trimDegree,
      MvPolynomial.eval₂Hom coeff x (rawTrimmedTail F V W j) = 0)
    (divisorTail : ∀ j > divisorDegree,
      ((regularDerivation F)^[j]) (regularImage F V) = 0)
    (remainderTail : ∀ j > remainderDegree,
      ((regularDerivation F)^[j]) (regularImage F theta) = 0) :
    ∀ j ≥ plainDegree, MvPolynomial.eval₂Hom coeff x (tailNumerator F j) = 0 := by
  let R := RegularCarrier F
  let v : R := regularImage F V
  let A := Localization.Away v
  let base := algebraMap R A
  let φ : Carrier K →+* A := base.comp (regularImage F)
  let D0 := regularDerivation F
  let D : Derivation K A A := localizationDerivation (Submonoid.powers v) D0
  have hD (a : R) : D (base a) = base (D0 a) := localizationDerivation_algebraMap _ _ _
  have hIter (a : R) (j : ℕ) : (D^[j]) (base a) = base ((D0^[j]) a) := by
    induction j with
    | zero => rfl
    | succ j ih => rw [iterate_succ_apply', iterate_succ_apply' D0 j a, ih, hD]
  let ev0 := pointValue F coeff x carrier regular
  have hvunit : IsUnit (ev0 v) := by
    exact (show ev0 v ≠ 0 from by rwa [pointValue_image]).isUnit
  let ev : A →+* L := IsLocalization.Away.lift v hvunit
  have hev (P : Carrier K) : ev (φ P) = MvPolynomial.eval₂Hom coeff x P := by
    change IsLocalization.Away.lift v hvunit (base (regularImage F P)) = _
    rw [IsLocalization.Away.lift_eq]
    exact pointValue_image F coeff x carrier regular P
  have commute (P : Carrier K) :
      φ (trimDerivation F P) = φ (implicitRegularity F) * D (φ P) := by
    change base (regularImage F (trimDerivation F P)) =
      base (regularImage F (implicitRegularity F)) * D (base (regularImage F P))
    rw [trimDerivation_apply, regularImage_clearedImplicit, hD, map_mul]
  have hVunit : IsUnit (φ V) := IsLocalization.Away.algebraMap_isUnit v
  have hSfixed : D (φ S) = 0 := by
    change D (base (regularImage F S)) = 0
    rw [hD, fixed, map_zero]
  have hW : φ W = φ S * φ (MvPolynomial.X 1) - φ theta := by rw [shape, map_sub, map_mul]
  have htail (P : Carrier K) (j : ℕ)
      (hz : ((D0^[j]) (regularImage F P)) = 0) : ev ((D^[j]) (φ P)) = 0 := by
    change ev ((D^[j]) (base (regularImage F P))) = 0
    rw [hIter, hz, map_zero, map_zero]
  intro j hj
  have hz := eval_persistent_trimmed_to_value (trimDerivation F) D φ ev
    (implicitRegularity F) V W (φ S) (φ theta) (φ (MvPolynomial.X 1)) commute hVunit
    (by rwa [hev]) (by rwa [hev]) (by rwa [hev]) hSfixed hW
    trimDegree divisorDegree remainderDegree (j+1)
    (fun i hi => by change ev (φ (rawTrimmedTail F V W i)) = 0; exact (hev _).trans (later i hi))
    (fun i hi => htail V i (divisorTail i hi)) (fun i hi => htail theta i (remainderTail i hi))
    (by omega) (by omega)
  have plain := congrArg (fun a : R => ev (base a)) (regularImage_tailNumerator F j)
  change ev (φ (tailNumerator F j)) = _ at plain
  simp only [map_mul, map_pow] at plain
  rw [← hIter] at plain
  change ev (φ (tailNumerator F j)) =
    (ev (φ (implicitRegularity F)))^(2*j+1) * ev ((D^[j+1]) (φ (MvPolynomial.X 1))) at plain
  rw [hz, mul_zero, hev] at plain
  exact plain


end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
