import ProximityPrize.SubmissionLower.BCHKSMinimalYReplacement6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSLocalValuation6400
open Polynomial
set_option maxHeartbeats 2000000
noncomputable def diagonalize {A : Type*} [CommSemiring A] :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom
    (Polynomial.mapRingHom (Polynomial.C : A →+* Polynomial A))
    (Polynomial.C Polynomial.X * Polynomial.X)
@[simp]
lemma diagonalize_C {A : Type*} [CommSemiring A] (P : Polynomial A) :
    diagonalize (Polynomial.C P) = P.map Polynomial.C := by
  simp [diagonalize]
@[simp]
lemma diagonalize_X {A : Type*} [CommSemiring A] :
    diagonalize (Polynomial.X : Polynomial (Polynomial A)) =
      Polynomial.C Polynomial.X * Polynomial.X := by
  simp [diagonalize]
@[simp]
lemma diagonalize_monomial {A : Type*} [CommSemiring A]
    (t : ℕ) (P : Polynomial A) :
    diagonalize (Polynomial.monomial t P) =
      P.map Polynomial.C *
        (Polynomial.C Polynomial.X * Polynomial.X) ^ t := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp [diagonalize]
theorem diagonalize_coeff_coeff {A : Type*} [CommSemiring A]
    (Q : Polynomial (Polynomial A)) (d t : ℕ) :
    ((diagonalize Q).coeff d).coeff t =
      if t ≤ d then (Q.coeff t).coeff (d - t) else 0 := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
      simp only [map_add, Polynomial.coeff_add, hQ, hR]
      split <;> simp_all
  | monomial j P =>
      rw [diagonalize_monomial]
      rw [mul_pow, ← mul_assoc, Polynomial.coeff_mul_X_pow']
      by_cases hjd : j ≤ d
      · rw [if_pos hjd]
        simp only [← Polynomial.C_pow, Polynomial.coeff_mul_C,
          Polynomial.coeff_map, Polynomial.coeff_mul_X_pow',
          Polynomial.coeff_monomial]
        by_cases hjt : j = t
        · subst t
          simp [hjd]
        · by_cases hjtle : j ≤ t
          · have hsub : t - j ≠ 0 := by omega
            simp only [hjtle, if_true, hjt]
            rw [Polynomial.coeff_C, if_neg hsub]
            simp
          · simp [hjt, hjtle]
      · rw [if_neg hjd]
        simp only [Polynomial.coeff_zero]
        by_cases htd : t ≤ d
        · rw [if_pos htd]
          have htj : t ≠ j := by omega
          rw [Polynomial.coeff_monomial, if_neg (Ne.symm htj)]
          simp
        · rw [if_neg htd]
theorem diagonalize_injective {A : Type*} [CommSemiring A] :
    Function.Injective (diagonalize :
      Polynomial (Polynomial A) → Polynomial (Polynomial A)) := by
  intro P Q hPQ
  apply Polynomial.ext
  intro t
  apply Polynomial.ext
  intro s
  have hcoeff := congrArg
    (fun E : Polynomial (Polynomial A) => (E.coeff (s + t)).coeff t) hPQ
  simpa [diagonalize_coeff_coeff, Nat.le_add_left,
    Nat.add_sub_cancel_right] using hcoeff
theorem diagonalize_ne_zero {A : Type*} [CommSemiring A]
    {Q : Polynomial (Polynomial A)} (hQ : Q ≠ 0) :
    diagonalize Q ≠ 0 := by
  intro hzero
  apply hQ
  apply diagonalize_injective
  simpa using hzero
def LocalVanish {A : Type*} [CommSemiring A]
    (Q : Polynomial (Polynomial A)) (m : ℕ) : Prop :=
  ∀ s t, s + t < m → (Q.coeff t).coeff s = 0
theorem diagonalize_coeff_eq_zero_of_localVanish
    {A : Type*} [CommSemiring A]
    {Q : Polynomial (Polynomial A)} {m d : ℕ}
    (hQ : LocalVanish Q m) (hd : d < m) :
    (diagonalize Q).coeff d = 0 := by
  apply Polynomial.ext
  intro t
  rw [diagonalize_coeff_coeff]
  by_cases htd : t ≤ d
  · rw [if_pos htd]
    exact hQ (d - t) t (by omega)
  · rw [if_neg htd]
    simp
theorem localVanish_of_diagonalize_coeff_eq_zero
    {A : Type*} [CommSemiring A]
    {Q : Polynomial (Polynomial A)} {m : ℕ}
    (hQ : ∀ d < m, (diagonalize Q).coeff d = 0) :
    LocalVanish Q m := by
  intro s t hst
  have hcoeff := congrArg (fun P : Polynomial A => P.coeff t)
    (hQ (s + t) hst)
  rw [diagonalize_coeff_coeff] at hcoeff
  simpa [Nat.le_add_left, Nat.add_sub_cancel_right] using hcoeff
noncomputable def localOrder {A : Type*} [CommSemiring A]
    (Q : Polynomial (Polynomial A)) : ℕ :=
  (diagonalize Q).natTrailingDegree
theorem localVanish_iff_le_localOrder
    {A : Type*} [CommSemiring A]
    {Q : Polynomial (Polynomial A)} (hQ : Q ≠ 0) (m : ℕ) :
    LocalVanish Q m ↔ m ≤ localOrder Q := by
  constructor
  · intro hvan
    exact Polynomial.le_natTrailingDegree (diagonalize_ne_zero hQ)
      (fun d hd => diagonalize_coeff_eq_zero_of_localVanish hvan hd)
  · intro hle
    apply localVanish_of_diagonalize_coeff_eq_zero
    intro d hd
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      (lt_of_lt_of_le hd hle)
theorem localOrder_mul {A : Type*} [CommSemiring A] [IsDomain A]
    {R C : Polynomial (Polynomial A)} (hR : R ≠ 0) (hC : C ≠ 0) :
    localOrder (R * C) = localOrder R + localOrder C := by
  unfold localOrder
  rw [map_mul, Polynomial.natTrailingDegree_mul
    (diagonalize_ne_zero hR) (diagonalize_ne_zero hC)]
theorem localVanish_mul_replace
    {A : Type*} [CommSemiring A] [IsDomain A]
    {R C S : Polynomial (Polynomial A)} {m ν : ℕ}
    (hR : R ≠ 0) (hC : C ≠ 0) (hS : S ≠ 0)
    (hRC : LocalVanish (R * C) m)
    (hRorder : localOrder R = ν)
    (hSorder : ν ≤ localOrder S) :
    LocalVanish (S * C) m := by
  have hmulRC : R * C ≠ 0 := mul_ne_zero hR hC
  have hmulSC : S * C ≠ 0 := mul_ne_zero hS hC
  have hmRC := (localVanish_iff_le_localOrder hmulRC m).mp hRC
  rw [localOrder_mul hR hC, hRorder] at hmRC
  apply (localVanish_iff_le_localOrder hmulSC m).mpr
  rw [localOrder_mul hS hC]
  omega
theorem localVanish_one_iff_coeff_zero_zero
    {A : Type*} [CommSemiring A]
    {Q : Polynomial (Polynomial A)} :
    LocalVanish Q 1 ↔ (Q.coeff 0).coeff 0 = 0 := by
  constructor
  · intro h
    exact h 0 0 (by norm_num)
  · intro h s t hst
    have hs : s = 0 := by omega
    have ht : t = 0 := by omega
    simpa [hs, ht] using h
theorem localVanish_mul_replace_order_one
    {A : Type*} [CommSemiring A] [IsDomain A]
    {R C S : Polynomial (Polynomial A)} {m : ℕ}
    (hR : R ≠ 0) (hC : C ≠ 0) (hS : S ≠ 0)
    (hRC : LocalVanish (R * C) m)
    (hRorder : localOrder R = 1)
    (hSvan : LocalVanish S 1) :
    LocalVanish (S * C) m := by
  apply localVanish_mul_replace hR hC hS hRC hRorder
  exact (localVanish_iff_le_localOrder hS 1).mp hSvan
open BCHKSMinimalYReplacement6400
theorem scaledReceivedLine_shift_localVanish_one
    {F : Type*} [Field F]
    (G M : Polynomial F) (U W : Fin 2 → Polynomial F) (x : F)
    (hW : ∀ r, W r = (M * U r) %ₘ G)
    (hx : Polynomial.eval x G = 0) :
    LocalVanish
      (Polynomial.Bivariate.shift (scaledReceivedLine M W)
        (Polynomial.C x)
        (Polynomial.C (Polynomial.eval x (U 0)) +
          Polynomial.X * Polynomial.C (Polynomial.eval x (U 1)))) 1 := by
  rw [localVanish_one_iff_coeff_zero_zero]
  exact scaledReceivedLine_local_order_one G M U W x hW hx
theorem scaledReceivedLine_ne_zero
    {F : Type*} [Field F]
    {M : Polynomial F} (W : Fin 2 → Polynomial F) (hM : M ≠ 0) :
    scaledReceivedLine M W ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun S : Polynomial (Polynomial (Polynomial F)) =>
    S.coeff 1) hzero
  rw [scaledReceivedLine_coeff_one] at hcoeff
  simp only [Polynomial.coeff_zero] at hcoeff
  exact hM ((Polynomial.map_eq_zero_iff Polynomial.C_injective).mp hcoeff)
theorem scaledReceivedLine_replaces_simple_factor_at_coordinate
    {F : Type} [Field F]
    (G M : Polynomial F) (U W : Fin 2 → Polynomial F) (x : F)
    (R C : Polynomial (Polynomial (Polynomial F))) (m : ℕ)
    (hW : ∀ r, W r = (M * U r) %ₘ G)
    (hx : Polynomial.eval x G = 0)
    (hM : M ≠ 0) (hR : R ≠ 0) (hC : C ≠ 0)
    (hRC : LocalVanish
      (Polynomial.Bivariate.shift R
          (Polynomial.C x)
          (Polynomial.C (Polynomial.eval x (U 0)) +
            Polynomial.X * Polynomial.C (Polynomial.eval x (U 1))) *
        Polynomial.Bivariate.shift C
          (Polynomial.C x)
          (Polynomial.C (Polynomial.eval x (U 0)) +
            Polynomial.X * Polynomial.C (Polynomial.eval x (U 1)))) m)
    (hRorder : localOrder
      (Polynomial.Bivariate.shift R
        (Polynomial.C x)
        (Polynomial.C (Polynomial.eval x (U 0)) +
          Polynomial.X * Polynomial.C (Polynomial.eval x (U 1)))) = 1) :
    LocalVanish
      (Polynomial.Bivariate.shift (scaledReceivedLine M W)
          (Polynomial.C x)
          (Polynomial.C (Polynomial.eval x (U 0)) +
            Polynomial.X * Polynomial.C (Polynomial.eval x (U 1))) *
        Polynomial.Bivariate.shift C
          (Polynomial.C x)
          (Polynomial.C (Polynomial.eval x (U 0)) +
            Polynomial.X * Polynomial.C (Polynomial.eval x (U 1)))) m := by
  let y : Polynomial F :=
    Polynomial.C (Polynomial.eval x (U 0)) +
      Polynomial.X * Polynomial.C (Polynomial.eval x (U 1))
  have hRshift : Polynomial.Bivariate.shift R (Polynomial.C x) y ≠ 0 :=
    Polynomial.Bivariate.shift_ne_zero R (Polynomial.C x) y hR
  have hCshift : Polynomial.Bivariate.shift C (Polynomial.C x) y ≠ 0 :=
    Polynomial.Bivariate.shift_ne_zero C (Polynomial.C x) y hC
  have hSshift : Polynomial.Bivariate.shift (scaledReceivedLine M W)
      (Polynomial.C x) y ≠ 0 :=
    Polynomial.Bivariate.shift_ne_zero _ (Polynomial.C x) y
      (scaledReceivedLine_ne_zero W hM)
  apply localVanish_mul_replace_order_one hRshift hCshift hSshift hRC hRorder
  exact scaledReceivedLine_shift_localVanish_one G M U W x hW hx
end BCHKSLocalValuation6400
end ProximityPrize.SubmissionLower
