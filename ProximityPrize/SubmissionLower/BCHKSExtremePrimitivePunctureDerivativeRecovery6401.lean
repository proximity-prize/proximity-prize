import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitivePunctureDerivativeRecovery6401
open Polynomial
open BCHKSSubfieldFrobenius6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section AbstractDerivativeRecovery
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem derivative_eval_fixed_of_map_eq_self6401
    (sigma : F →+* F) (beta : F) (hbeta : sigma beta = beta)
    (P : F[X]) (hP : P.map sigma = P) :
    sigma (P.derivative.eval beta) = P.derivative.eval beta := by
  have hderivative : P.derivative.map sigma = P.derivative := by
    rw [← Polynomial.derivative_map, hP]
  calc
    sigma (P.derivative.eval beta) =
        (P.derivative.map sigma).eval beta :=
      (eval_map_eq_map_eval_of_fixed sigma P.derivative beta hbeta).symm
    _ = P.derivative.eval beta := by rw [hderivative]
theorem fixedErrorDerivative_affine_at_simpleRoot6401
    (L K V0 V1 : F[X]) (Owner E : F → F[X])
    (u0 u1 beta : F) (T : Finset F)
    (hLzero : L.eval beta = 0)
    (hidentity : ∀ z ∈ T,
      L * K * Owner z = V0 + Polynomial.C z * V1 + E z)
    (hagreement : ∀ z ∈ T,
      (Owner z).eval beta = u0 + z * u1) :
    ∀ z ∈ T,
      (E z).derivative.eval beta =
        (L.derivative.eval beta * K.eval beta * u0 -
            V0.derivative.eval beta) +
          z * (L.derivative.eval beta * K.eval beta * u1 -
            V1.derivative.eval beta) := by
  intro z hz
  have hderivative := congrArg Polynomial.derivative (hidentity z hz)
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C_mul] at hderivative
  have heval := congrArg (Polynomial.eval beta) hderivative
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.derivative_C, Polynomial.eval_zero,
    hLzero, zero_mul, add_zero, hagreement z hz] at heval
  linear_combination -heval
theorem dividedDirection_eval_eq_gauge_mul_of_heavyAgreement6401
    (sigma : F →+* F) (beta : F) (hbeta : sigma beta = beta)
    (L K V0 V1 Q1 : F[X]) (Owner E : F → F[X])
    (u0 u1 : F) (T : Finset F)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (hlarge : q6401 < T.card)
    (hLzero : L.eval beta = 0)
    (hLderivative : L.derivative.eval beta ≠ 0)
    (hV1 : V1 = L * Q1)
    (hEfixed : ∀ z ∈ T, (E z).map sigma = E z)
    (hidentity : ∀ z ∈ T,
      L * K * Owner z = V0 + Polynomial.C z * V1 + E z)
    (hagreement : ∀ z ∈ T,
      (Owner z).eval beta = u0 + z * u1) :
    Q1.eval beta = K.eval beta * u1 := by
  let a : F := L.derivative.eval beta * K.eval beta * u0 -
    V0.derivative.eval beta
  let b : F := L.derivative.eval beta * K.eval beta * u1 -
    V1.derivative.eval beta
  have hfixedValues : ∀ z ∈ T,
      sigma (a + z * b) = a + z * b := by
    intro z hz
    have hderivative := fixedErrorDerivative_affine_at_simpleRoot6401
      L K V0 V1 Owner E u0 u1 beta T hLzero hidentity hagreement z hz
    have hfixedDerivative := derivative_eval_fixed_of_map_eq_self6401
      sigma beta hbeta (E z) (hEfixed z hz)
    change (E z).derivative.eval beta = a + z * b at hderivative
    rw [← hderivative]
    exact hfixedDerivative
  have hb : b = 0 :=
    fixedAffineValues_many_forces_slope_zero6401
      sigma T a b hfixedCard hlarge hfixedValues
  have hV1derivative :
      V1.derivative.eval beta =
        L.derivative.eval beta * Q1.eval beta := by
    rw [hV1, Polynomial.derivative_mul]
    simp [hLzero]
  dsimp only [b] at hb
  rw [hV1derivative] at hb
  have hmul :
      L.derivative.eval beta * Q1.eval beta =
        L.derivative.eval beta * (K.eval beta * u1) := by
    linear_combination -hb
  exact mul_left_cancel₀ hLderivative hmul
end AbstractDerivativeRecovery
section SplitLocator
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem twoRowSourcePunctureLocator_derivative_eval_ne_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (i : Fin n6401) (hi : i ∈ twoRowSourceBadCoordinates6401 W) :
    (twoRowSourcePunctureLocator6401 W).derivative.eval (alpha i) ≠ 0 := by
  classical
  let Bad := twoRowSourceBadCoordinates6401 W
  let f : Fin n6401 → F[X] := fun j ↦
    Polynomial.X - Polynomial.C (alpha j)
  let R : F[X] := ∏ j ∈ Bad.erase i, f j
  have hfactor : twoRowSourcePunctureLocator6401 W = f i * R := by
    dsimp only [twoRowSourcePunctureLocator6401, Bad, R, f]
    exact (Finset.mul_prod_erase
      (twoRowSourceBadCoordinates6401 W)
      (fun j ↦ Polynomial.X - Polynomial.C (alpha j)) hi).symm
  have hRvalue : R.eval (alpha i) ≠ 0 := by
    dsimp only [R, f]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr (alpha.injective.ne hji.symm)
  rw [hfactor, Polynomial.derivative_mul]
  simp only [f, Polynomial.derivative_X_sub_C,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_self, zero_mul, add_zero, one_mul]
  exact hRvalue
theorem twoRowSourcePunctureLocator_dvd_of_eval_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (P : F[X])
    (hzero : ∀ i ∈ twoRowSourceBadCoordinates6401 W,
      P.eval (alpha i) = 0) :
    twoRowSourcePunctureLocator6401 W ∣ P := by
  classical
  unfold twoRowSourcePunctureLocator6401
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    have hne : alpha i ≠ alpha j := fun h ↦ hij (alpha.injective h)
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hne).isUnit
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hzero i hi
end SplitLocator
section LowLoadDeletion
variable {Owner Coord : Type*} [DecidableEq Owner] [DecidableEq Coord]
def agreementOwnerFibre6401
    (T : Finset Owner) (A : Owner → Finset Coord) (i : Coord) :
    Finset Owner :=
  T.filter fun z ↦ i ∈ A z
def lowLoadPunctureCoordinates6401
    (T : Finset Owner) (A : Owner → Finset Coord)
    (Bad : Finset Coord) (q : Nat) : Finset Coord :=
  Bad.filter fun i ↦ (agreementOwnerFibre6401 T A i).card ≤ q
def ownersTouchingLowLoadPuncture6401
    (T : Finset Owner) (A : Owner → Finset Coord)
    (Bad : Finset Coord) (q : Nat) : Finset Owner :=
  (lowLoadPunctureCoordinates6401 T A Bad q).biUnion
    (agreementOwnerFibre6401 T A)
def ownersAfterLowLoadPunctureDeletion6401
    (T : Finset Owner) (A : Owner → Finset Coord)
    (Bad : Finset Coord) (q : Nat) : Finset Owner :=
  T \ ownersTouchingLowLoadPuncture6401 T A Bad q
theorem ownersTouchingLowLoadPuncture_subset6401
    (T : Finset Owner) (A : Owner → Finset Coord)
    (Bad : Finset Coord) (q : Nat) :
    ownersTouchingLowLoadPuncture6401 T A Bad q ⊆ T := by
  intro z hz
  obtain ⟨i, _hi, hz⟩ := Finset.mem_biUnion.mp hz
  exact (Finset.mem_filter.mp hz).1
theorem ownersTouchingLowLoadPuncture_card_le6401
    (T : Finset Owner) (A : Owner → Finset Coord)
    (Bad : Finset Coord) (q : Nat) :
    (ownersTouchingLowLoadPuncture6401 T A Bad q).card ≤ Bad.card * q := by
  let Light := lowLoadPunctureCoordinates6401 T A Bad q
  have hfibre : ∀ i ∈ Light,
      (agreementOwnerFibre6401 T A i).card ≤ q := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hlight : Light.card ≤ Bad.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  calc
    (ownersTouchingLowLoadPuncture6401 T A Bad q).card =
        (Light.biUnion (agreementOwnerFibre6401 T A)).card := by rfl
    _ ≤ Light.card * q :=
      Finset.card_biUnion_le_card_mul Light
        (agreementOwnerFibre6401 T A) q hfibre
    _ ≤ Bad.card * q := Nat.mul_le_mul_right q hlight
theorem ownersAfterLowLoadPunctureDeletion_card_ge6401
    (T : Finset Owner) (A : Owner → Finset Coord)
    (Bad : Finset Coord) (q : Nat) :
    T.card - Bad.card * q ≤
      (ownersAfterLowLoadPunctureDeletion6401 T A Bad q).card := by
  have hsubset := ownersTouchingLowLoadPuncture_subset6401 T A Bad q
  have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
  have hcost := ownersTouchingLowLoadPuncture_card_le6401 T A Bad q
  dsimp only [ownersAfterLowLoadPunctureDeletion6401] at hsplit ⊢
  omega
theorem surviving_punctureAgreement_has_heavyFibre6401
    (T : Finset Owner) (A : Owner → Finset Coord)
    (Bad : Finset Coord) (q : Nat)
    (z : Owner)
    (hz : z ∈ ownersAfterLowLoadPunctureDeletion6401 T A Bad q)
    (i : Coord) (hiBad : i ∈ Bad) (hiz : i ∈ A z) :
    q < (agreementOwnerFibre6401 T A i).card := by
  have hzT : z ∈ T := (Finset.mem_sdiff.mp hz).1
  have hznot : z ∉ ownersTouchingLowLoadPuncture6401 T A Bad q :=
    (Finset.mem_sdiff.mp hz).2
  by_contra hnot
  have hle : (agreementOwnerFibre6401 T A i).card ≤ q :=
    Nat.le_of_not_gt hnot
  have hiLight : i ∈ lowLoadPunctureCoordinates6401 T A Bad q :=
    Finset.mem_filter.mpr ⟨hiBad, hle⟩
  apply hznot
  apply Finset.mem_biUnion.mpr
  exact ⟨i, hiLight, Finset.mem_filter.mpr ⟨hzT, hiz⟩⟩
end LowLoadDeletion
end BCHKSExtremePrimitivePunctureDerivativeRecovery6401
end ProximityPrize.SubmissionLower
