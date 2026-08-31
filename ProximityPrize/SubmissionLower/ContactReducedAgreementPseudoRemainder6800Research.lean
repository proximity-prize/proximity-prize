import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTaylorNumerators
import ProximityPrize.SubmissionLower.ContactFactorCaps

 












namespace ProximityPrize.SubmissionLower
namespace ContactReducedAgreementPseudoRemainder6800Research

open ContactTaylorNumerators
open ContactFactorCaps

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

private abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

abbrev RemainingCoordinates := {i : Fin 4 // i ≠ 2}

abbrev CoefficientRing (K : Type*) [Field K] :=
  MvPolynomial RemainingCoordinates K

 

def collectR (K : Type*) [Field K] :
    MvPolynomial (Fin 4) K ≃ₐ[K] Polynomial (CoefficientRing K) :=
  (MvPolynomial.renameEquiv K
    (Equiv.optionSubtypeNe (2 : Fin 4)).symm).trans
      (MvPolynomial.optionEquivLeft K RemainingCoordinates)

theorem collectR_natDegree (F : Poly4 K) :
    (collectR K F).natDegree = F.degreeOf 2 := by
  exact (MvPolynomial.degreeOf_eq_natDegree (2 : Fin 4) F).symm

def embedCoefficients (K : Type*) [Field K] :
    CoefficientRing K →+* Poly4 K :=
  (collectR K).symm.toRingHom.comp Polynomial.C

theorem collectR_X_other (i : RemainingCoordinates) :
    collectR K (MvPolynomial.X (i : Fin 4)) =
      Polynomial.C (MvPolynomial.X i) := by
  simp [collectR, MvPolynomial.renameEquiv_apply,
    Equiv.optionSubtypeNe_symm_apply, i.property]

theorem collectR_X_R :
    collectR K (MvPolynomial.X (2 : Fin 4)) = Polynomial.X := by
  simp [collectR, MvPolynomial.renameEquiv_apply,
    Equiv.optionSubtypeNe_symm_apply]

theorem collectR_natCast (n : ℕ) :
    collectR K (n : Poly4 K) = (n : Polynomial (CoefficientRing K)) := by
  exact map_natCast (collectR K) n

theorem collectR_rename_remaining (P : CoefficientRing K) :
    collectR K (MvPolynomial.rename Subtype.val P) = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [collectR, MvPolynomial.renameEquiv_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.rename_X, hP, collectR_X_other]

theorem embedCoefficients_eq_rename (P : CoefficientRing K) :
    embedCoefficients K P = MvPolynomial.rename Subtype.val P := by
  apply (collectR K).injective
  rw [collectR_rename_remaining]
  exact (collectR K).apply_symm_apply (Polynomial.C P)

def liftedCoefficient (F : Poly4 K) (n : ℕ) : Poly4 K :=
  embedCoefficients K ((collectR K F).coeff n)

theorem liftedCoefficient_R_degree (F : Poly4 K) (n : ℕ) :
    (liftedCoefficient F n).degreeOf 2 = 0 := by
  rw [← collectR_natDegree]
  change ((collectR K)
    ((collectR K).symm (Polynomial.C ((collectR K F).coeff n)))).natDegree = 0
  rw [AlgEquiv.apply_symm_apply, Polynomial.natDegree_C]

 


theorem numeratorStep_add_source_mul
    (F M Q : Poly4 K) (j : ℕ) :
    numeratorStep K F j (M + F * Q) =
      numeratorStep K F j M + F * numeratorStep K F j Q := by
  unfold numeratorStep clearedStep polyG polyH
  simp only [map_add, MvPolynomial.pderiv_mul]
  ring

 
theorem numeratorStep_sub_dvd_of_sub_dvd
    (F M N : Poly4 K) (j : ℕ)
    (hMN : F ∣ M - N) :
    F ∣ numeratorStep K F j M - numeratorStep K F j N := by
  obtain ⟨Q, hQ⟩ := hMN
  have hM : M = N + F * Q := by
    linear_combination hQ
  refine ⟨numeratorStep K F j Q, ?_⟩
  rw [hM, numeratorStep_add_source_mul]
  ring

 
theorem numerator_succ_sub_step_dvd
    (F M : Poly4 K) (j : ℕ)
    (hM : F ∣ numerator K F j - M) :
    F ∣ numerator K F (j + 1) - numeratorStep K F j M := by
  rw [numerator_succ]
  exact numeratorStep_sub_dvd_of_sub_dvd F (numerator K F j) M j hM

section RCoefficients

theorem optionEquivLeft_coeff_pderiv_some
    {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial (Option σ) K) (i : σ) (n : ℕ) :
    (MvPolynomial.optionEquivLeft K σ
      (MvPolynomial.pderiv (some i) P)).coeff n =
        MvPolynomial.pderiv i
          ((MvPolynomial.optionEquivLeft K σ P).coeff n) := by
  ext d
  rw [MvPolynomial.optionEquivLeft_coeff_coeff,
    MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv,
    MvPolynomial.optionEquivLeft_coeff_coeff]
  have hindex :
      d.optionElim n + Finsupp.single (some i) 1 =
        (d + Finsupp.single i 1).optionElim n := by
    ext o
    cases o with
    | none => simp [Finsupp.add_apply]
    | some k =>
        by_cases hki : k = i
        · subst k
          simp [Finsupp.add_apply]
        · simp [Finsupp.add_apply, hki]
  rw [hindex]
  simp [Finsupp.add_apply]

theorem optionEquivLeft_coeff_pderiv_none
    {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial (Option σ) K) (n : ℕ) :
    (MvPolynomial.optionEquivLeft K σ
      (MvPolynomial.pderiv none P)).coeff n =
        (n + 1 : K) •
          (MvPolynomial.optionEquivLeft K σ P).coeff (n + 1) := by
  ext d
  rw [MvPolynomial.optionEquivLeft_coeff_coeff,
    MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_smul,
    MvPolynomial.optionEquivLeft_coeff_coeff]
  have hindex :
      d.optionElim n + Finsupp.single none 1 =
        d.optionElim (n + 1) := by
    ext o
    cases o <;> simp [Finsupp.add_apply]
  rw [hindex]
  simp [smul_eq_mul, mul_comm]

theorem collectR_coeff_pderiv_other
    (F : Poly4 K) (i : Fin 4) (hi : i ≠ 2) (n : ℕ) :
    (collectR K (MvPolynomial.pderiv i F)).coeff n =
      MvPolynomial.pderiv ⟨i, hi⟩ ((collectR K F).coeff n) := by
  let e := (Equiv.optionSubtypeNe (2 : Fin 4)).symm
  have hei : e i = some ⟨i, hi⟩ := by
    simp [e, Equiv.optionSubtypeNe_symm_apply, hi]
  have hrename := MvPolynomial.pderiv_rename e.injective i F
  change (MvPolynomial.optionEquivLeft K RemainingCoordinates
    (MvPolynomial.rename e (MvPolynomial.pderiv i F))).coeff n = _
  rw [← hrename, hei, optionEquivLeft_coeff_pderiv_some]
  rfl

theorem collectR_pderiv_R (F : Poly4 K) :
    collectR K (MvPolynomial.pderiv (2 : Fin 4) F) =
      (collectR K F).derivative := by
  let e := (Equiv.optionSubtypeNe (2 : Fin 4)).symm
  have heR : e 2 = none := by
    simp [e, Equiv.optionSubtypeNe_symm_apply]
  have hrename := MvPolynomial.pderiv_rename e.injective (2 : Fin 4) F
  ext n d
  change MvPolynomial.coeff d
    ((MvPolynomial.optionEquivLeft K RemainingCoordinates
      (MvPolynomial.rename e (MvPolynomial.pderiv 2 F))).coeff n) = _
  rw [← hrename, heR, optionEquivLeft_coeff_pderiv_none,
    Polynomial.coeff_derivative]
  simp [Algebra.smul_def, mul_comm]
  rfl

theorem liftedCoefficient_pderiv_other
    (F : Poly4 K) (i : Fin 4) (hi : i ≠ 2) (n : ℕ) :
    liftedCoefficient (MvPolynomial.pderiv i F) n =
      MvPolynomial.pderiv i (liftedCoefficient F n) := by
  unfold liftedCoefficient
  rw [collectR_coeff_pderiv_other F i hi n,
    embedCoefficients_eq_rename, embedCoefficients_eq_rename]
  exact (MvPolynomial.pderiv_rename Subtype.val_injective ⟨i, hi⟩
    ((collectR K F).coeff n)).symm

 


theorem coeff_derivative_pred_of_natDegree_le
    (P : Polynomial (CoefficientRing K)) (n : ℕ)
    (hP : P.natDegree ≤ n) :
    P.derivative.coeff (n - 1) = (n : CoefficientRing K) * P.coeff n := by
  cases n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, Nat.zero_sub]
      rw [Polynomial.coeff_derivative]
      have hcoeff : P.coeff 1 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP (by omega))
      rw [hcoeff, zero_mul]
  | succ n =>
      simpa only [Nat.succ_sub_one, Nat.cast_succ, mul_comm] using
        Polynomial.coeff_derivative P n

 

theorem natDegree_collectR_pderiv_other_le
    (F : Poly4 K) (i : Fin 4) (hi : i ≠ 2) (cap : ℕ)
    (hF : F.degreeOf 2 ≤ cap) :
    (collectR K (MvPolynomial.pderiv i F)).natDegree ≤ cap := by
  rw [collectR_natDegree]
  exact pderiv_degree_bound i 2 F cap hF

 
theorem natDegree_collectR_pderiv_R_le
    (F : Poly4 K) (cap : ℕ) (hcap : 1 ≤ cap)
    (hF : F.degreeOf 2 ≤ cap) :
    (collectR K (MvPolynomial.pderiv (2 : Fin 4) F)).natDegree ≤ cap - 1 := by
  rw [collectR_pderiv_R]
  exact (Polynomial.natDegree_derivative_le (collectR K F)).trans (by
    rw [collectR_natDegree]
    omega)

theorem coeff_collectR_polyH_pred
    (F : Poly4 K) (cap : ℕ) (hF : F.degreeOf 2 ≤ cap) :
    (collectR K (polyH K F)).coeff (cap - 1) =
      (cap : CoefficientRing K) * (collectR K F).coeff cap := by
  unfold polyH
  rw [collectR_pderiv_R]
  exact coeff_derivative_pred_of_natDegree_le (collectR K F) cap
    (by simpa only [collectR_natDegree] using hF)

 

theorem coeff_collectR_polyG_succ
    (F : Poly4 K) (cap : ℕ) (hF : F.degreeOf 2 ≤ cap) :
    (collectR K (polyG K F)).coeff (cap + 1) =
      -MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩
        ((collectR K F).coeff cap) := by
  have hFX :
      (collectR K (MvPolynomial.pderiv (0 : Fin 4) F)).natDegree ≤ cap :=
    natDegree_collectR_pderiv_other_le F 0 (by decide) cap hF
  have hFXzero :
      (collectR K (MvPolynomial.pderiv (0 : Fin 4) F)).coeff (cap + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (hFX.trans_lt (Nat.lt_succ_self cap))
  unfold polyG
  simp only [map_neg, map_add, map_mul, collectR_X_R,
    Polynomial.coeff_neg, Polynomial.coeff_add]
  rw [Polynomial.coeff_X_mul, hFXzero, zero_add,
    collectR_coeff_pderiv_other F 1 (by decide) cap]

 

theorem coeff_collectR_pderiv_polyH_pred
    (F : Poly4 K) (i : Fin 4) (hi : i ≠ 2)
    (cap : ℕ) (hF : F.degreeOf 2 ≤ cap) :
    (collectR K (MvPolynomial.pderiv i (polyH K F))).coeff (cap - 1) =
      (cap : CoefficientRing K) *
        MvPolynomial.pderiv ⟨i, hi⟩ ((collectR K F).coeff cap) := by
  rw [collectR_coeff_pderiv_other (polyH K F) i hi (cap - 1),
    coeff_collectR_polyH_pred F cap hF, MvPolynomial.pderiv_mul]
  simp

theorem coeff_mul_three_at_caps
    (P Q S : Polynomial (CoefficientRing K)) (a b c : ℕ)
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ b)
    (hS : S.natDegree ≤ c) :
    (P * Q * S).coeff (a + b + c) =
      P.coeff a * Q.coeff b * S.coeff c := by
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le, 
    Polynomial.coeff_mul_add_eq_of_natDegree_le hP hQ]
  · exact (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP hQ))
  · exact hS

theorem coeff_mul_four_at_caps
    (P Q S T : Polynomial (CoefficientRing K)) (a b c d : ℕ)
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ b)
    (hS : S.natDegree ≤ c) (hT : T.natDegree ≤ d) :
    (P * Q * S * T).coeff (a + b + c + d) =
      P.coeff a * Q.coeff b * S.coeff c * T.coeff d := by
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le,
    coeff_mul_three_at_caps P Q S a b c hP hQ hS]
  · exact (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP hQ)) hS))
  · exact hT

 


theorem coeff_collectR_denominatorTerm_top
    (F : Poly4 K) (cap : ℕ) (hcap : 1 ≤ cap)
    (hF : F.degreeOf 2 ≤ cap) :
    (collectR K
      (polyH K F * MvPolynomial.pderiv (0 : Fin 4) (polyH K F) +
        MvPolynomial.X (2 : Fin 4) * polyH K F *
          MvPolynomial.pderiv (1 : Fin 4) (polyH K F) +
        polyG K F * MvPolynomial.pderiv (2 : Fin 4) (polyH K F))).coeff
        (2 * cap - 1) =
      (cap : CoefficientRing K) * (collectR K F).coeff cap *
        MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩
          ((collectR K F).coeff cap) := by
  let H := polyH K F
  let HX := MvPolynomial.pderiv (0 : Fin 4) H
  let HY := MvPolynomial.pderiv (1 : Fin 4) H
  let HR := MvPolynomial.pderiv (2 : Fin 4) H
  let G := polyG K F
  let L := (collectR K F).coeff cap
  let LY := MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩ L
  have hHmv : H.degreeOf 2 ≤ cap - 1 := by
    exact pderiv_same_degree_bound 2 F cap hF
  have hH : (collectR K H).natDegree ≤ cap - 1 := by
    simpa only [collectR_natDegree] using hHmv
  have hHX : (collectR K HX).natDegree ≤ cap - 1 := by
    exact natDegree_collectR_pderiv_other_le H 0 (by decide) (cap - 1) hHmv
  have hHY : (collectR K HY).natDegree ≤ cap - 1 := by
    exact natDegree_collectR_pderiv_other_le H 1 (by decide) (cap - 1) hHmv
  have hGmv : G.degreeOf 2 ≤ cap + 1 := by
    apply polyG_degree_bound 2 F cap 1 hF
    simp
  have hG : (collectR K G).natDegree ≤ cap + 1 := by
    simpa only [collectR_natDegree] using hGmv
  have hzero :
      (collectR K (H * HX)).coeff (2 * cap - 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc
      (collectR K (H * HX)).natDegree ≤
          (collectR K H).natDegree + (collectR K HX).natDegree := by
        simp only [map_mul]
        exact Polynomial.natDegree_mul_le
      _ ≤ (cap - 1) + (cap - 1) := Nat.add_le_add hH hHX
      _ < 2 * cap - 1 := by omega
  have hmiddle :
      (collectR K (MvPolynomial.X (2 : Fin 4) * H * HY)).coeff
          (2 * cap - 1) =
        (cap : CoefficientRing K) ^ 2 * L * LY := by
    have hindex : 1 + (cap - 1) + (cap - 1) = 2 * cap - 1 := by omega
    rw [map_mul, map_mul, collectR_X_R, ← hindex,
      coeff_mul_three_at_caps Polynomial.X (collectR K H) (collectR K HY)
        1 (cap - 1) (cap - 1) Polynomial.natDegree_X_le hH hHY,
      Polynomial.coeff_X_one]
    change 1 * (collectR K H).coeff (cap - 1) *
        (collectR K HY).coeff (cap - 1) = _
    rw [coeff_collectR_polyH_pred F cap hF,
      coeff_collectR_pderiv_polyH_pred F 1 (by decide) cap hF]
    dsimp only [L, LY]
    ring
  have hlast :
      (collectR K (G * HR)).coeff (2 * cap - 1) =
        -(cap : CoefficientRing K) * (cap - 1 : ℕ) * L * LY := by
    by_cases hc1 : cap = 1
    · subst cap
      have hHRzero : HR = 0 := by
        dsimp only [HR]
        apply pderiv_eq_zero_of_degree_bound_zero 2 H
        simpa using hHmv
      rw [hHRzero, mul_zero, map_zero, Polynomial.coeff_zero]
      simp
    · have hcap2 : 2 ≤ cap := by omega
      have hHR : (collectR K HR).natDegree ≤ cap - 2 := by
        dsimp only [HR]
        rw [collectR_pderiv_R]
        exact (Polynomial.natDegree_derivative_le (collectR K H)).trans (by
          omega)
      have hindex : (cap + 1) + (cap - 2) = 2 * cap - 1 := by omega
      rw [map_mul, ← hindex,
        Polynomial.coeff_mul_add_eq_of_natDegree_le hG hHR]
      change (collectR K G).coeff (cap + 1) *
          (collectR K HR).coeff (cap - 2) = _
      rw [coeff_collectR_polyG_succ F cap hF]
      have hHRcoeff :
          (collectR K HR).coeff (cap - 2) =
            (cap - 1 : ℕ) * (collectR K H).coeff (cap - 1) := by
        dsimp only [HR]
        rw [collectR_pderiv_R]
        simpa only [Nat.sub_sub] using
          coeff_derivative_pred_of_natDegree_le (collectR K H) (cap - 1) hH
      rw [hHRcoeff, coeff_collectR_polyH_pred F cap hF]
      dsimp only [L, LY]
      push_cast
      ring
  change (collectR K (H * HX + MvPolynomial.X 2 * H * HY + G * HR)).coeff
      (2 * cap - 1) = _
  simp only [map_add, Polynomial.coeff_add]
  rw [hzero, hmiddle, hlast]
  dsimp only [L, LY]
  rw [Nat.cast_sub hcap]
  norm_num
  ring

theorem natDegree_collectR_denominatorTerm_le
    (F : Poly4 K) (cap : ℕ) (hcap : 1 ≤ cap)
    (hF : F.degreeOf 2 ≤ cap) :
    (collectR K
      (polyH K F * MvPolynomial.pderiv (0 : Fin 4) (polyH K F) +
        MvPolynomial.X (2 : Fin 4) * polyH K F *
          MvPolynomial.pderiv (1 : Fin 4) (polyH K F) +
        polyG K F * MvPolynomial.pderiv (2 : Fin 4) (polyH K F))).natDegree
      ≤ 2 * cap - 1 := by
  let H := polyH K F
  let HX := MvPolynomial.pderiv (0 : Fin 4) H
  let HY := MvPolynomial.pderiv (1 : Fin 4) H
  let HR := MvPolynomial.pderiv (2 : Fin 4) H
  let G := polyG K F
  have hHmv : H.degreeOf 2 ≤ cap - 1 :=
    pderiv_same_degree_bound 2 F cap hF
  have hH : (collectR K H).natDegree ≤ cap - 1 := by
    simpa only [collectR_natDegree] using hHmv
  have hHX : (collectR K HX).natDegree ≤ cap - 1 :=
    natDegree_collectR_pderiv_other_le H 0 (by decide) (cap - 1) hHmv
  have hHY : (collectR K HY).natDegree ≤ cap - 1 :=
    natDegree_collectR_pderiv_other_le H 1 (by decide) (cap - 1) hHmv
  have hGmv : G.degreeOf 2 ≤ cap + 1 := by
    apply polyG_degree_bound 2 F cap 1 hF
    simp
  have hG : (collectR K G).natDegree ≤ cap + 1 := by
    simpa only [collectR_natDegree] using hGmv
  have hfirst : (collectR K (H * HX)).natDegree ≤ 2 * cap - 1 := by
    calc
      _ ≤ (collectR K H).natDegree + (collectR K HX).natDegree := by
        simp only [map_mul]
        exact Polynomial.natDegree_mul_le
      _ ≤ (cap - 1) + (cap - 1) := Nat.add_le_add hH hHX
      _ ≤ 2 * cap - 1 := by omega
  have hmiddle :
      (collectR K (MvPolynomial.X (2 : Fin 4) * H * HY)).natDegree
        ≤ 2 * cap - 1 := by
    simp only [map_mul, collectR_X_R]
    calc
      (Polynomial.X * collectR K H * collectR K HY).natDegree ≤
          (Polynomial.X * collectR K H).natDegree +
            (collectR K HY).natDegree := Polynomial.natDegree_mul_le
      _ ≤ (Polynomial.X.natDegree + (collectR K H).natDegree) +
            (collectR K HY).natDegree := by gcongr; exact Polynomial.natDegree_mul_le
      _ ≤ (1 + (cap - 1)) + (cap - 1) := by
        exact Nat.add_le_add
          (Nat.add_le_add Polynomial.natDegree_X_le hH) hHY
      _ ≤ 2 * cap - 1 := by omega
  have hlast : (collectR K (G * HR)).natDegree ≤ 2 * cap - 1 := by
    by_cases hc1 : cap = 1
    · subst cap
      have hHRzero : HR = 0 := by
        dsimp only [HR]
        apply pderiv_eq_zero_of_degree_bound_zero 2 H
        simpa using hHmv
      rw [hHRzero, mul_zero, map_zero, Polynomial.natDegree_zero]
      omega
    · have hHR : (collectR K HR).natDegree ≤ cap - 2 := by
        dsimp only [HR]
        rw [collectR_pderiv_R]
        exact (Polynomial.natDegree_derivative_le (collectR K H)).trans (by
          omega)
      calc
        (collectR K (G * HR)).natDegree ≤
            (collectR K G).natDegree + (collectR K HR).natDegree := by
          simp only [map_mul]
          exact Polynomial.natDegree_mul_le
        _ ≤ (cap + 1) + (cap - 2) := Nat.add_le_add hG hHR
        _ ≤ 2 * cap - 1 := by omega
  simp only [map_add]
  exact Polynomial.natDegree_add_le_of_degree_le
    (Polynomial.natDegree_add_le_of_degree_le hfirst hmiddle) hlast

 


theorem coeff_collectR_numeratorStep_top
    (F M : Poly4 K) (j cap D : ℕ)
    (hcap : 1 ≤ cap)
    (hF : F.degreeOf 2 ≤ cap) (hM : M.degreeOf 2 ≤ D)
    (hD : D = 2 * j * (cap - 1)) :
    (collectR K (numeratorStep K F j M)).coeff (D + 2 * cap - 1) =
      (cap : CoefficientRing K) ^ 2 * (collectR K F).coeff cap *
        ((collectR K F).coeff cap *
            MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩
              ((collectR K M).coeff D) -
          (2 * j : ℕ) *
            MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩
              ((collectR K F).coeff cap) *
            (collectR K M).coeff D) := by
  let H := polyH K F
  let G := polyG K F
  let MX := MvPolynomial.pderiv (0 : Fin 4) M
  let MY := MvPolynomial.pderiv (1 : Fin 4) M
  let MR := MvPolynomial.pderiv (2 : Fin 4) M
  let Den :=
    H * MvPolynomial.pderiv (0 : Fin 4) H +
      MvPolynomial.X (2 : Fin 4) * H * MvPolynomial.pderiv (1 : Fin 4) H +
      G * MvPolynomial.pderiv (2 : Fin 4) H
  let L := (collectR K F).coeff cap
  let A := (collectR K M).coeff D
  let LY := MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩ L
  let AY := MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩ A
  have hHmv : H.degreeOf 2 ≤ cap - 1 :=
    pderiv_same_degree_bound 2 F cap hF
  have hH : (collectR K H).natDegree ≤ cap - 1 := by
    simpa only [collectR_natDegree] using hHmv
  have hH2 : ((collectR K H) ^ 2).natDegree ≤ 2 * (cap - 1) :=
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hH)
  have hMX : (collectR K MX).natDegree ≤ D :=
    natDegree_collectR_pderiv_other_le M 0 (by decide) D hM
  have hMY : (collectR K MY).natDegree ≤ D :=
    natDegree_collectR_pderiv_other_le M 1 (by decide) D hM
  have hGmv : G.degreeOf 2 ≤ cap + 1 := by
    apply polyG_degree_bound 2 F cap 1 hF
    simp
  have hG : (collectR K G).natDegree ≤ cap + 1 := by
    simpa only [collectR_natDegree] using hGmv
  have hMcol : (collectR K M).natDegree ≤ D := by
    simpa only [collectR_natDegree] using hM
  have hfirst :
      (collectR K (H ^ 2 * MX)).coeff (D + 2 * cap - 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc
      (collectR K (H ^ 2 * MX)).natDegree ≤
          ((collectR K H) ^ 2).natDegree + (collectR K MX).natDegree := by
        simp only [map_mul, map_pow]
        exact Polynomial.natDegree_mul_le
      _ ≤ 2 * (cap - 1) + D := Nat.add_le_add hH2 hMX
      _ < D + 2 * cap - 1 := by omega
  have hmiddle :
      (collectR K (MvPolynomial.X (2 : Fin 4) * H ^ 2 * MY)).coeff
          (D + 2 * cap - 1) =
        (cap : CoefficientRing K) ^ 2 * L ^ 2 * AY := by
    have hindex :
        1 + 2 * (cap - 1) + D = D + 2 * cap - 1 := by omega
    rw [map_mul, map_mul, map_pow, collectR_X_R, ← hindex,
      coeff_mul_three_at_caps Polynomial.X ((collectR K H) ^ 2)
        (collectR K MY) 1 (2 * (cap - 1)) D
        Polynomial.natDegree_X_le hH2 hMY,
      Polynomial.coeff_X_one,
      Polynomial.coeff_pow_of_natDegree_le (p := collectR K H)
        (m := 2) hH,
      coeff_collectR_polyH_pred F cap hF,
      collectR_coeff_pderiv_other M 1 (by decide) D]
    dsimp only [L, A, AY]
    ring
  have hthird :
      (collectR K (G * H * MR)).coeff (D + 2 * cap - 1) =
        -(cap : CoefficientRing K) * (D : CoefficientRing K) * L * LY * A := by
    by_cases hDz : D = 0
    · have hMzero : M.degreeOf 2 ≤ 0 := by simpa [hDz] using hM
      have hMRzero : MR = 0 := by
        dsimp only [MR]
        exact pderiv_eq_zero_of_degree_bound_zero 2 M hMzero
      rw [hMRzero, mul_zero, map_zero, Polynomial.coeff_zero, hDz]
      simp
    · have hDpos : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hDz
      have hMR : (collectR K MR).natDegree ≤ D - 1 := by
        dsimp only [MR]
        rw [collectR_pderiv_R]
        exact (Polynomial.natDegree_derivative_le (collectR K M)).trans (by
          omega)
      have hindex :
          (cap + 1) + (cap - 1) + (D - 1) =
            D + 2 * cap - 1 := by omega
      rw [map_mul, map_mul, ← hindex,
        coeff_mul_three_at_caps (collectR K G) (collectR K H) (collectR K MR)
          (cap + 1) (cap - 1) (D - 1) hG hH hMR,
        coeff_collectR_polyG_succ F cap hF,
        coeff_collectR_polyH_pred F cap hF]
      have hMRcoeff :
          (collectR K MR).coeff (D - 1) =
            (D : CoefficientRing K) * A := by
        dsimp only [MR]
        rw [collectR_pderiv_R,
          coeff_derivative_pred_of_natDegree_le (collectR K M) D hMcol]
      rw [hMRcoeff]
      dsimp only [L, A, LY]
      ring
  have hDen : (collectR K Den).natDegree ≤ 2 * cap - 1 := by
    exact natDegree_collectR_denominatorTerm_le F cap hcap hF
  have hDenCoeff :
      (collectR K Den).coeff (2 * cap - 1) =
        (cap : CoefficientRing K) * L * LY := by
    exact coeff_collectR_denominatorTerm_top F cap hcap hF
  have hcorrection :
      (collectR K (((2 * j : ℕ) : Poly4 K) * M * Den)).coeff
          (D + 2 * cap - 1) =
        (2 * j : ℕ) * A * ((cap : CoefficientRing K) * L * LY) := by
    have hconst :
        (collectR K ((2 * j : ℕ) : Poly4 K)).natDegree ≤ 0 := by
      rw [collectR_natCast]
      change (Polynomial.C ((2 * j : ℕ) : CoefficientRing K)).natDegree ≤ 0
      rw [Polynomial.natDegree_C]
    have hconstCoeff :
        (collectR K ((2 * j : ℕ) : Poly4 K)).coeff 0 =
          (2 * j : ℕ) := by
      rw [collectR_natCast]
      simp
    have hindex : 0 + D + (2 * cap - 1) = D + 2 * cap - 1 := by omega
    rw [map_mul, map_mul, ← hindex,
      coeff_mul_three_at_caps
        (collectR K ((2 * j : ℕ) : Poly4 K)) (collectR K M) (collectR K Den)
        0 D (2 * cap - 1) hconst hMcol hDen,
      hconstCoeff, hDenCoeff]
  change
    (collectR K (H ^ 2 * MX +
      MvPolynomial.X 2 * H ^ 2 * MY + G * H * MR -
      ((2 * j : ℕ) : Poly4 K) * M * Den)).coeff
        (D + 2 * cap - 1) = _
  simp only [map_sub, map_add, Polynomial.coeff_sub, Polynomial.coeff_add]
  rw [hfirst, hmiddle, hthird, hcorrection]
  dsimp only [L, A, LY, AY]
  have hDcast :
      (D : CoefficientRing K) =
        (2 * j : ℕ) * ((cap : CoefficientRing K) - 1) := by
    rw [hD, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hcap, Nat.cast_one]
  rw [hDcast]
  push_cast
  ring

def stepCorrectionCoefficient
    (F M : Poly4 K) (j cap D : ℕ) : CoefficientRing K :=
  (cap : CoefficientRing K) ^ 2 *
    ((collectR K F).coeff cap *
        MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩
          ((collectR K M).coeff D) -
      (2 * j : ℕ) *
        MvPolynomial.pderiv ⟨(1 : Fin 4), by decide⟩
          ((collectR K F).coeff cap) *
        (collectR K M).coeff D)

def stepCorrection
    (F M : Poly4 K) (j cap D : ℕ) : Poly4 K :=
  embedCoefficients K (stepCorrectionCoefficient F M j cap D) *
    MvPolynomial.X (2 : Fin 4) ^ (D + cap - 1)

def reducedNumeratorStep
    (F M : Poly4 K) (j cap D : ℕ) : Poly4 K :=
  numeratorStep K F j M - F * stepCorrection F M j cap D

theorem collectR_embedCoefficients (P : CoefficientRing K) :
    collectR K (embedCoefficients K P) = Polynomial.C P := by
  exact (collectR K).apply_symm_apply (Polynomial.C P)

theorem collectR_stepCorrection
    (F M : Poly4 K) (j cap D : ℕ) :
    collectR K (stepCorrection F M j cap D) =
      Polynomial.C (stepCorrectionCoefficient F M j cap D) *
        Polynomial.X ^ (D + cap - 1) := by
  simp only [stepCorrection, map_mul, map_pow, collectR_embedCoefficients,
    collectR_X_R]

theorem natDegree_collectR_stepCorrection_le
    (F M : Poly4 K) (j cap D : ℕ) :
    (collectR K (stepCorrection F M j cap D)).natDegree ≤ D + cap - 1 := by
  rw [collectR_stepCorrection]
  calc
    _ ≤ (Polynomial.C (stepCorrectionCoefficient F M j cap D)).natDegree +
        (Polynomial.X ^ (D + cap - 1)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + (D + cap - 1) := by
      gcongr
      · rw [Polynomial.natDegree_C]
      · exact Polynomial.natDegree_X_pow_le (R := CoefficientRing K)
          (D + cap - 1)
    _ = D + cap - 1 := Nat.zero_add _

theorem coeff_collectR_stepCorrection_at_cap
    (F M : Poly4 K) (j cap D : ℕ) :
    (collectR K (stepCorrection F M j cap D)).coeff (D + cap - 1) =
      stepCorrectionCoefficient F M j cap D := by
  rw [collectR_stepCorrection, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_self]
  simp

theorem coeff_collectR_source_mul_stepCorrection_top
    (F M : Poly4 K) (j cap D : ℕ)
    (hcap : 1 ≤ cap) (hF : F.degreeOf 2 ≤ cap) :
    (collectR K (F * stepCorrection F M j cap D)).coeff
        (D + 2 * cap - 1) =
      (collectR K F).coeff cap * stepCorrectionCoefficient F M j cap D := by
  have hFcol : (collectR K F).natDegree ≤ cap := by
    simpa only [collectR_natDegree] using hF
  have hindex : cap + (D + cap - 1) = D + 2 * cap - 1 := by omega
  rw [map_mul, ← hindex,
    Polynomial.coeff_mul_add_eq_of_natDegree_le hFcol
      (natDegree_collectR_stepCorrection_le F M j cap D),
    coeff_collectR_stepCorrection_at_cap]

theorem coeff_collectR_reducedNumeratorStep_top
    (F M : Poly4 K) (j cap D : ℕ)
    (hcap : 1 ≤ cap)
    (hF : F.degreeOf 2 ≤ cap) (hM : M.degreeOf 2 ≤ D)
    (hD : D = 2 * j * (cap - 1)) :
    (collectR K (reducedNumeratorStep F M j cap D)).coeff
        (D + 2 * cap - 1) = 0 := by
  unfold reducedNumeratorStep
  rw [map_sub, Polynomial.coeff_sub,
    coeff_collectR_numeratorStep_top F M j cap D hcap hF hM hD,
    coeff_collectR_source_mul_stepCorrection_top F M j cap D hcap hF]
  unfold stepCorrectionCoefficient
  ring

theorem reducedNumeratorStep_R_degree_le
    (F M : Poly4 K) (j cap D : ℕ)
    (hcap : 1 ≤ cap)
    (hF : F.degreeOf 2 ≤ cap) (hM : M.degreeOf 2 ≤ D)
    (hD : D = 2 * j * (cap - 1)) :
    (reducedNumeratorStep F M j cap D).degreeOf 2 ≤
      2 * (j + 1) * (cap - 1) := by
  have hstep :
      (numeratorStep K F j M).degreeOf 2 ≤ D + (2 * cap - 1) :=
    numeratorStep_R_degree_bound F M j D cap hcap hF hM
  have hcorr :
      (F * stepCorrection F M j cap D).degreeOf 2 ≤
        D + (2 * cap - 1) := by
    rw [← collectR_natDegree]
    simp only [map_mul]
    calc
      _ ≤ (collectR K F).natDegree +
          (collectR K (stepCorrection F M j cap D)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ cap + (D + cap - 1) := Nat.add_le_add
        (by simpa only [collectR_natDegree] using hF)
        (natDegree_collectR_stepCorrection_le F M j cap D)
      _ = D + (2 * cap - 1) := by omega
  have hraw :
      (reducedNumeratorStep F M j cap D).degreeOf 2 ≤
        D + (2 * cap - 1) := by
    unfold reducedNumeratorStep
    exact degree_sub_bound 2 hstep hcorr
  rw [← collectR_natDegree] at hraw ⊢
  have hraw' :
      (collectR K (reducedNumeratorStep F M j cap D)).natDegree ≤
        D + 2 * cap - 1 := by omega
  have hdrop :=
    Polynomial.natDegree_le_pred hraw'
      (coeff_collectR_reducedNumeratorStep_top
        F M j cap D hcap hF hM hD)
  have hlinear :
      (collectR K (reducedNumeratorStep F M j cap D)).natDegree ≤
        D + 2 * (cap - 1) := by omega
  calc
    _ ≤ D + 2 * (cap - 1) := hlinear
    _ = 2 * (j + 1) * (cap - 1) := by rw [hD]; ring

theorem numeratorStep_sub_reducedNumeratorStep_dvd
    (F M : Poly4 K) (j cap D : ℕ) :
    F ∣ numeratorStep K F j M - reducedNumeratorStep F M j cap D := by
  refine ⟨stepCorrection F M j cap D, ?_⟩
  unfold reducedNumeratorStep
  ring

theorem numerator_succ_sub_reducedNumeratorStep_dvd
    (F M : Poly4 K) (j cap D : ℕ)
    (hM : F ∣ numerator K F j - M) :
    F ∣ numerator K F (j + 1) - reducedNumeratorStep F M j cap D := by
  have hfirst := numerator_succ_sub_step_dvd F M j hM
  have hsecond := numeratorStep_sub_reducedNumeratorStep_dvd F M j cap D
  convert dvd_add hfirst hsecond using 1
  ring

def reducedNumerator (F : Poly4 K) (cap : ℕ) : ℕ → Poly4 K
  | 0 => MvPolynomial.X (1 : Fin 4)
  | j + 1 =>
      reducedNumeratorStep F (reducedNumerator F cap j) j cap
        (2 * j * (cap - 1))

@[simp] theorem reducedNumerator_zero (F : Poly4 K) (cap : ℕ) :
    reducedNumerator F cap 0 = MvPolynomial.X (1 : Fin 4) := rfl

@[simp] theorem reducedNumerator_succ (F : Poly4 K) (cap j : ℕ) :
    reducedNumerator F cap (j + 1) =
      reducedNumeratorStep F (reducedNumerator F cap j) j cap
        (2 * j * (cap - 1)) := rfl

theorem numerator_sub_reducedNumerator_dvd
    (F : Poly4 K) (cap j : ℕ) :
    F ∣ numerator K F j - reducedNumerator F cap j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [reducedNumerator_succ]
      exact numerator_succ_sub_reducedNumeratorStep_dvd
        F (reducedNumerator F cap j) j cap (2 * j * (cap - 1)) ih

theorem reducedNumerator_R_degree_le
    (F : Poly4 K) (cap j : ℕ) (hcap : 1 ≤ cap)
    (hF : F.degreeOf 2 ≤ cap) :
    (reducedNumerator F cap j).degreeOf 2 ≤ 2 * j * (cap - 1) := by
  induction j with
  | zero =>
      simp [reducedNumerator_zero, MvPolynomial.degreeOf_X_of_ne]
  | succ j ih =>
      rw [reducedNumerator_succ]
      exact reducedNumeratorStep_R_degree_le
        F (reducedNumerator F cap j) j cap (2 * j * (cap - 1))
          hcap hF ih rfl

section WeightedBounds

def wt (weights : Fin 4 → ℕ) (P : Poly4 K) : ℕ :=
  MvPolynomial.weightedTotalDegree weights P

theorem wt_mul_le (weights : Fin 4 → ℕ) (P Q : Poly4 K) :
    wt weights (P * Q) ≤ wt weights P + wt weights Q := by
  unfold wt
  rw [← degree_weightedLift, map_mul]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_mul_le (4 : Fin 5)
      (weightedLift K weights P) (weightedLift K weights Q)

theorem wt_add_le (weights : Fin 4 → ℕ) (P Q : Poly4 K) :
    wt weights (P + Q) ≤ max (wt weights P) (wt weights Q) := by
  unfold wt
  rw [← degree_weightedLift, map_add]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_add_le (4 : Fin 5)
      (weightedLift K weights P) (weightedLift K weights Q)

theorem wt_sub_le (weights : Fin 4 → ℕ) (P Q : Poly4 K) :
    wt weights (P - Q) ≤ max (wt weights P) (wt weights Q) := by
  unfold wt
  rw [← degree_weightedLift, map_sub]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_sub_le (4 : Fin 5)
      (weightedLift K weights P) (weightedLift K weights Q)

theorem wt_pow_le (weights : Fin 4 → ℕ) (P : Poly4 K) (n : ℕ) :
    wt weights (P ^ n) ≤ n * wt weights P := by
  unfold wt
  rw [← degree_weightedLift, map_pow]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_pow_le (4 : Fin 5) (weightedLift K weights P) n

theorem wt_X (weights : Fin 4 → ℕ) (i : Fin 4) :
    wt weights (MvPolynomial.X i : Poly4 K) = weights i := by
  unfold wt
  simp [MvPolynomial.weightedTotalDegree, MvPolynomial.support_X,
    Finsupp.weight_single]

theorem wt_C (weights : Fin 4 → ℕ) (a : K) :
    wt weights (MvPolynomial.C a : Poly4 K) = 0 := by
  unfold wt MvPolynomial.weightedTotalDegree
  simp

theorem wt_natCast (weights : Fin 4 → ℕ) (n : ℕ) :
    wt weights (n : Poly4 K) = 0 := by
  rw [← map_natCast (MvPolynomial.C : K →+* Poly4 K), wt_C]

theorem wt_pderiv_le
    (weights : Fin 4 → ℕ) (P : Poly4 K) (i : Fin 4) (A : ℕ)
    (hP : wt weights P ≤ A) :
    wt weights (MvPolynomial.pderiv i P) ≤ A - weights i := by
  apply (weightedTotalDegree_le_iff weights _ _).mpr
  intro d hd
  have hh :=
    (MvPolynomial.le_weightedTotalDegree weights
      (support_before_pderiv i P d hd)).trans hP
  simp only [map_add, Finsupp.weight_single, one_nsmul] at hh
  omega

theorem embedCoefficients_pderiv
    (P : CoefficientRing K) (i : RemainingCoordinates) :
    embedCoefficients K (MvPolynomial.pderiv i P) =
      MvPolynomial.pderiv (i : Fin 4) (embedCoefficients K P) := by
  rw [embedCoefficients_eq_rename, embedCoefficients_eq_rename]
  exact (MvPolynomial.pderiv_rename Subtype.val_injective i P).symm

theorem stepCorrection_eq_lifted
    (F M : Poly4 K) (j cap D : ℕ) :
    stepCorrection F M j cap D =
      ((cap : ℕ) : Poly4 K) ^ 2 *
        (liftedCoefficient F cap *
            MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient M D) -
          ((2 * j : ℕ) : Poly4 K) *
            MvPolynomial.pderiv (1 : Fin 4) (liftedCoefficient F cap) *
            liftedCoefficient M D) *
        MvPolynomial.X (2 : Fin 4) ^ (D + cap - 1) := by
  unfold stepCorrection stepCorrectionCoefficient liftedCoefficient
  simp only [map_pow, map_sub, map_mul, map_natCast,
    embedCoefficients_pderiv]

end WeightedBounds

 


theorem liftedCoefficient_support_exact
    (F : Poly4 K) (n : ℕ) (e : Fin 4 →₀ ℕ)
    (he : e ∈ (liftedCoefficient F n).support) :
    ∃ d ∈ F.support,
      d 2 = n ∧ ∀ i : Fin 4, i ≠ 2 → e i = d i := by
  classical
  have heR : e 2 = 0 := by
    have hh := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) he
    rw [liftedCoefficient_R_degree] at hh
    omega
  change e ∈ (embedCoefficients K ((collectR K F).coeff n)).support at he
  rw [embedCoefficients_eq_rename,
    MvPolynomial.support_rename_of_injective Subtype.val_injective] at he
  obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp he
  have hopt : u.optionElim n ∈
      (MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 4)).symm F).support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft (R := K)).mp hu
  rw [MvPolynomial.support_rename_of_injective
    (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective] at hopt
  obtain ⟨d, hd, hdu⟩ := Finset.mem_image.mp hopt
  refine ⟨d, hd, ?_, ?_⟩
  · have h := congrArg
      (fun f : Option RemainingCoordinates →₀ ℕ =>
        f ((Equiv.optionSubtypeNe (2 : Fin 4)).symm 2)) hdu
    rw [Finsupp.mapDomain_apply
      (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective] at h
    simpa [Equiv.optionSubtypeNe_symm_apply] using h
  · intro i hi
    have hev : e i = u ⟨i, hi⟩ := by
      rw [← heu]
      exact Finsupp.mapDomain_apply Subtype.val_injective u ⟨i, hi⟩
    have huv := congrArg
      (fun f : Option RemainingCoordinates →₀ ℕ =>
        f ((Equiv.optionSubtypeNe (2 : Fin 4)).symm i)) hdu
    rw [Finsupp.mapDomain_apply
      (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective] at huv
    have hindex :
        (Equiv.optionSubtypeNe (2 : Fin 4)).symm i = some ⟨i, hi⟩ := by
      simp [Equiv.optionSubtypeNe_symm_apply, hi]
    rw [hindex, Finsupp.optionElim_apply_some] at huv
    exact hev.trans huv.symm

 



theorem liftedCoefficient_weight_le_sub
    (weights : Fin 4 → ℕ) (hR : weights 2 = 1)
    (F : Poly4 K) (n cap : ℕ)
    (hF : MvPolynomial.weightedTotalDegree weights F ≤ cap)
    (hn : n ≤ cap) :
    MvPolynomial.weightedTotalDegree weights (liftedCoefficient F n) ≤
      cap - n := by
  classical
  by_cases hz : liftedCoefficient F n = 0
  · rw [hz, MvPolynomial.weightedTotalDegree_zero]
    exact Nat.zero_le _
  · apply (weightedTotalDegree_le_iff weights _ _).mpr
    intro e he
    obtain ⟨d, hd, hdR, hde⟩ := liftedCoefficient_support_exact F n e he
    have heR : e 2 = 0 := by
      have hh := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) he
      rw [liftedCoefficient_R_degree] at hh
      omega
    have hweight :
        Finsupp.weight weights e + n = Finsupp.weight weights d := by
      rw [weight_fin4, weight_fin4, hR, heR, hdR]
      have h0 := hde 0 (by decide)
      have h1 := hde 1 (by decide)
      have h3 := hde 3 (by decide)
      rw [h0, h1, h3]
      ring
    have hdweight :=
      (MvPolynomial.le_weightedTotalDegree weights hd).trans hF
    rw [← hweight] at hdweight
    omega

section FinalWeightedBounds

theorem wt_neg (weights : Fin 4 → ℕ) (P : Poly4 K) :
    wt weights (-P) = wt weights P := by
  unfold wt
  rw [← degree_weightedLift, map_neg, MvPolynomial.degreeOf_neg,
    degree_weightedLift]

theorem wt_polyG_le_nested
    (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F : Poly4 K) (C : ℕ) (hC : 1 ≤ C)
    (hF : wt weights F ≤ C) :
    wt weights (polyG K F) ≤ C := by
  have hx := wt_pderiv_le weights F 0 C hF
  have hy := wt_pderiv_le weights F 1 C hF
  have hvar : wt weights (MvPolynomial.X (2 : Fin 4) : Poly4 K) = 1 := by
    rw [wt_X, hR]
  have hm := wt_mul_le weights (MvPolynomial.X (2 : Fin 4) : Poly4 K)
    (MvPolynomial.pderiv 1 F)
  have hsum := wt_add_le weights (MvPolynomial.pderiv 0 F)
    (MvPolynomial.X (2 : Fin 4) * MvPolynomial.pderiv 1 F)
  unfold polyG
  rw [wt_neg]
  exact hsum.trans (max_le (by omega) (by omega))

theorem numeratorStep_wt_le_nested
    (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F M : Poly4 K) (j A C : ℕ)
    (hC : 2 ≤ C) (hA : 1 ≤ A)
    (hF : wt weights F ≤ C) (hM : wt weights M ≤ A) :
    wt weights (numeratorStep K F j M) ≤ A + 2 * (C - 1) := by
  let H := polyH K F
  let G := polyG K F
  let R : Poly4 K := MvPolynomial.X (2 : Fin 4)
  let Hcap := C - 1
  have hH : wt weights H ≤ Hcap := by
    dsimp only [H, Hcap]
    unfold polyH
    simpa only [hR] using wt_pderiv_le weights F 2 C hF
  have hG : wt weights G ≤ C := by
    exact wt_polyG_le_nested weights hX hY hR F C (by omega) hF
  have hRwt : wt weights R = 1 := by
    dsimp only [R]
    rw [wt_X, hR]
  have hMX : wt weights (MvPolynomial.pderiv 0 M) ≤ A := by
    have h := wt_pderiv_le weights M 0 A hM
    rw [hX, Nat.sub_zero] at h
    exact h
  have hMY : wt weights (MvPolynomial.pderiv 1 M) ≤ A - 1 := by
    simpa only [hY] using wt_pderiv_le weights M 1 A hM
  have hMR : wt weights (MvPolynomial.pderiv 2 M) ≤ A - 1 := by
    simpa only [hR] using wt_pderiv_le weights M 2 A hM
  have hHX : wt weights (MvPolynomial.pderiv 0 H) ≤ Hcap := by
    have h := wt_pderiv_le weights H 0 Hcap hH
    rw [hX, Nat.sub_zero] at h
    exact h
  have hHY : wt weights (MvPolynomial.pderiv 1 H) ≤ Hcap - 1 := by
    simpa only [hY] using wt_pderiv_le weights H 1 Hcap hH
  have hHR : wt weights (MvPolynomial.pderiv 2 H) ≤ Hcap - 1 := by
    simpa only [hR] using wt_pderiv_le weights H 2 Hcap hH
  have hH2 : wt weights (H ^ 2) ≤ 2 * Hcap :=
    (wt_pow_le weights H 2).trans (Nat.mul_le_mul_left 2 hH)
  have htermX :
      wt weights (H ^ 2 * MvPolynomial.pderiv 0 M) ≤ A + 2 * Hcap := by
    have h := wt_mul_le weights (H ^ 2) (MvPolynomial.pderiv 0 M)
    omega
  have htermY :
      wt weights (R * H ^ 2 * MvPolynomial.pderiv 1 M) ≤
        A + 2 * Hcap := by
    have h1 := wt_mul_le weights R (H ^ 2)
    have h2 := wt_mul_le weights (R * H ^ 2) (MvPolynomial.pderiv 1 M)
    omega
  have htermR :
      wt weights (G * H * MvPolynomial.pderiv 2 M) ≤ A + 2 * Hcap := by
    have h1 := wt_mul_le weights G H
    have h2 := wt_mul_le weights (G * H) (MvPolynomial.pderiv 2 M)
    omega
  have hinnerX :
      wt weights (H * MvPolynomial.pderiv 0 H) ≤ 2 * Hcap := by
    have h := wt_mul_le weights H (MvPolynomial.pderiv 0 H)
    omega
  have hinnerY :
      wt weights (R * H * MvPolynomial.pderiv 1 H) ≤ 2 * Hcap := by
    have h1 := wt_mul_le weights R H
    have h2 := wt_mul_le weights (R * H) (MvPolynomial.pderiv 1 H)
    omega
  have hinnerR :
      wt weights (G * MvPolynomial.pderiv 2 H) ≤ 2 * Hcap := by
    have h := wt_mul_le weights G (MvPolynomial.pderiv 2 H)
    omega
  have hinner :
      wt weights (H * MvPolynomial.pderiv 0 H +
        R * H * MvPolynomial.pderiv 1 H +
        G * MvPolynomial.pderiv 2 H) ≤ 2 * Hcap := by
    exact (wt_add_le weights _ _).trans
      (max_le ((wt_add_le weights _ _).trans
        (max_le hinnerX hinnerY)) hinnerR)
  have hn : wt weights (((2 * j : ℕ) : Poly4 K)) = 0 :=
    wt_natCast weights (2 * j)
  have hnM : wt weights (((2 * j : ℕ) : Poly4 K) * M) ≤ A := by
    have h := wt_mul_le weights (((2 * j : ℕ) : Poly4 K)) M
    omega
  have hlast :
      wt weights (((2 * j : ℕ) : Poly4 K) * M *
        (H * MvPolynomial.pderiv 0 H +
          R * H * MvPolynomial.pderiv 1 H +
          G * MvPolynomial.pderiv 2 H)) ≤ A + 2 * Hcap := by
    have h := wt_mul_le weights (((2 * j : ℕ) : Poly4 K) * M)
      (H * MvPolynomial.pderiv 0 H +
        R * H * MvPolynomial.pderiv 1 H +
        G * MvPolynomial.pderiv 2 H)
    omega
  change wt weights
      (H ^ 2 * MvPolynomial.pderiv 0 M +
        R * H ^ 2 * MvPolynomial.pderiv 1 M +
        G * H * MvPolynomial.pderiv 2 M -
        ((2 * j : ℕ) : Poly4 K) * M *
          (H * MvPolynomial.pderiv 0 H +
            R * H * MvPolynomial.pderiv 1 H +
            G * MvPolynomial.pderiv 2 H)) ≤ A + 2 * Hcap
  exact (wt_sub_le weights _ _).trans
    (max_le ((wt_add_le weights _ _).trans
      (max_le ((wt_add_le weights _ _).trans
        (max_le htermX htermY)) htermR)) hlast)

theorem pderiv_eq_zero_of_wt_zero
    (weights : Fin 4 → ℕ) (i : Fin 4) (hi : weights i = 1)
    (P : Poly4 K) (hP : wt weights P ≤ 0) :
    MvPolynomial.pderiv i P = 0 := by
  apply MvPolynomial.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hh :=
    (MvPolynomial.le_weightedTotalDegree weights
      (support_before_pderiv i P d hd)).trans hP
  simp only [map_add, Finsupp.weight_single, one_nsmul, hi] at hh
  omega

theorem stepCorrection_wt_le_nested
    (weights : Fin 4 → ℕ)
    (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F M : Poly4 K) (j cap D C A : ℕ)
    (hcap : 1 ≤ cap) (hcapC : cap ≤ C) (hDA : D + 1 ≤ A)
    (hF : wt weights F ≤ C) (hM : wt weights M ≤ A) :
    wt weights (stepCorrection F M j cap D) ≤ A + C - 2 := by
  let LF := liftedCoefficient F cap
  let AM := liftedCoefficient M D
  let LY := MvPolynomial.pderiv (1 : Fin 4) LF
  let AY := MvPolynomial.pderiv (1 : Fin 4) AM
  let B := (C - cap) + (A - D) - 1
  have hLF : wt weights LF ≤ C - cap := by
    exact liftedCoefficient_weight_le_sub weights hR F cap C hF hcapC
  have hAM : wt weights AM ≤ A - D := by
    exact liftedCoefficient_weight_le_sub weights hR M D A hM (by omega)
  have hLY : wt weights LY ≤ (C - cap) - 1 := by
    dsimp only [LY]
    simpa only [hY] using wt_pderiv_le weights LF 1 (C - cap) hLF
  have hAY : wt weights AY ≤ (A - D) - 1 := by
    dsimp only [AY]
    simpa only [hY] using wt_pderiv_le weights AM 1 (A - D) hAM
  have hADpos : 1 ≤ A - D := by omega
  have hterm1 : wt weights (LF * AY) ≤ B := by
    have h := wt_mul_le weights LF AY
    dsimp only [B]
    omega
  have hterm2 :
      wt weights (((2 * j : ℕ) : Poly4 K) * LY * AM) ≤ B := by
    by_cases heq : cap = C
    · have hLFzero : wt weights LF ≤ 0 := by
        simpa [heq] using hLF
      have hLYzero : LY = 0 := by
        dsimp only [LY]
        exact pderiv_eq_zero_of_wt_zero weights 1 hY LF hLFzero
      rw [hLYzero, mul_zero, zero_mul]
      unfold wt
      rw [MvPolynomial.weightedTotalDegree_zero]
      exact bot_le
    · have hlt : cap < C := lt_of_le_of_ne hcapC heq
      have hn : wt weights (((2 * j : ℕ) : Poly4 K)) = 0 :=
        wt_natCast weights (2 * j)
      have hmul1 :=
        wt_mul_le weights (((2 * j : ℕ) : Poly4 K)) LY
      have hmul2 :=
        wt_mul_le weights (((2 * j : ℕ) : Poly4 K) * LY) AM
      dsimp only [B]
      omega
  have hinner :
      wt weights (LF * AY - ((2 * j : ℕ) : Poly4 K) * LY * AM) ≤ B :=
    (wt_sub_le weights _ _).trans (max_le hterm1 hterm2)
  have hcapScalar : wt weights (((cap : ℕ) : Poly4 K) ^ 2) ≤ 0 := by
    have hpow := wt_pow_le weights (((cap : ℕ) : Poly4 K)) 2
    rw [wt_natCast] at hpow
    exact hpow
  have hcoeff :
      wt weights (((cap : ℕ) : Poly4 K) ^ 2 *
        (LF * AY - ((2 * j : ℕ) : Poly4 K) * LY * AM)) ≤ B := by
    have h := wt_mul_le weights (((cap : ℕ) : Poly4 K) ^ 2)
      (LF * AY - ((2 * j : ℕ) : Poly4 K) * LY * AM)
    omega
  have hRpow :
      wt weights
        (MvPolynomial.X (2 : Fin 4) ^ (D + cap - 1) : Poly4 K) ≤
          D + cap - 1 := by
    have h := wt_pow_le weights
      (MvPolynomial.X (2 : Fin 4) : Poly4 K) (D + cap - 1)
    rw [wt_X, hR] at h
    simpa using h
  rw [stepCorrection_eq_lifted]
  change wt weights
    ((((cap : ℕ) : Poly4 K) ^ 2 *
      (LF * AY - ((2 * j : ℕ) : Poly4 K) * LY * AM)) *
        MvPolynomial.X (2 : Fin 4) ^ (D + cap - 1)) ≤ A + C - 2
  have hmul := wt_mul_le weights
    (((cap : ℕ) : Poly4 K) ^ 2 *
      (LF * AY - ((2 * j : ℕ) : Poly4 K) * LY * AM))
    (MvPolynomial.X (2 : Fin 4) ^ (D + cap - 1))
  have harith : B + (D + cap - 1) ≤ A + C - 2 := by
    dsimp only [B]
    omega
  exact hmul.trans ((Nat.add_le_add hcoeff hRpow).trans harith)

theorem reducedNumeratorStep_wt_le_nested
    (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F M : Poly4 K) (j cap D C A : ℕ)
    (hcap : 1 ≤ cap) (hcapC : cap ≤ C) (hC : 2 ≤ C)
    (hDA : D + 1 ≤ A)
    (hF : wt weights F ≤ C) (hM : wt weights M ≤ A) :
    wt weights (reducedNumeratorStep F M j cap D) ≤
      A + 2 * (C - 1) := by
  have hraw :=
    numeratorStep_wt_le_nested weights hX hY hR F M j A C hC
      (by omega) hF hM
  have hQ :=
    stepCorrection_wt_le_nested weights hY hR F M j cap D C A
      hcap hcapC hDA hF hM
  have hFQ := wt_mul_le weights F (stepCorrection F M j cap D)
  unfold reducedNumeratorStep
  exact (wt_sub_le weights _ _).trans
    (max_le hraw (hFQ.trans (by omega)))

theorem reducedNumerator_wt_le_nested
    (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F : Poly4 K) (cap C j : ℕ)
    (hcap : 1 ≤ cap) (hcapC : cap ≤ C) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) :
    wt weights (reducedNumerator F cap j) ≤
      1 + 2 * j * (C - 1) := by
  induction j with
  | zero =>
      rw [reducedNumerator_zero, wt_X, hY]
      norm_num
  | succ j ih =>
      rw [reducedNumerator_succ]
      have hsub : cap - 1 ≤ C - 1 := Nat.sub_le_sub_right hcapC 1
      have hDA :
          2 * j * (cap - 1) + 1 ≤ 1 + 2 * j * (C - 1) := by
        have hmul := Nat.mul_le_mul_left (2 * j) hsub
        omega
      have h := reducedNumeratorStep_wt_le_nested weights hX hY hR F
        (reducedNumerator F cap j) j cap (2 * j * (cap - 1)) C
        (1 + 2 * j * (C - 1)) hcap hcapC hC hDA hF ih
      convert h using 1 <;> ring

 


theorem exists_reducedNumerator_three_bounds
    (weights₁ weights₂ : Fin 4 → ℕ)
    (hX₁ : weights₁ 0 = 0) (hY₁ : weights₁ 1 = 1)
    (hR₁ : weights₁ 2 = 1)
    (hX₂ : weights₂ 0 = 0) (hY₂ : weights₂ 1 = 1)
    (hR₂ : weights₂ 2 = 1)
    (F : Poly4 K) (cap C₁ C₂ j : ℕ)
    (hcap : 1 ≤ cap) (hcapC₁ : cap ≤ C₁) (hcapC₂ : cap ≤ C₂)
    (hC₁ : 2 ≤ C₁) (hC₂ : 2 ≤ C₂)
    (hFcap : F.degreeOf 2 ≤ cap)
    (hF₁ : wt weights₁ F ≤ C₁) (hF₂ : wt weights₂ F ≤ C₂) :
    ∃ M : Poly4 K,
      F ∣ numerator K F j - M ∧
      M.degreeOf 2 ≤ 2 * j * (cap - 1) ∧
      wt weights₁ M ≤ 1 + 2 * j * (C₁ - 1) ∧
      wt weights₂ M ≤ 1 + 2 * j * (C₂ - 1) := by
  refine ⟨reducedNumerator F cap j,
    numerator_sub_reducedNumerator_dvd F cap j,
    reducedNumerator_R_degree_le F cap j hcap hFcap,
    reducedNumerator_wt_le_nested weights₁ hX₁ hY₁ hR₁ F cap C₁ j
      hcap hcapC₁ hC₁ hF₁,
    reducedNumerator_wt_le_nested weights₂ hX₂ hY₂ hR₂ F cap C₂ j
      hcap hcapC₂ hC₂ hF₂⟩

def reducedCommonNumeratorTerm
    (F : Poly4 K) (cap w : ℕ) (coeffs : ℕ → K) (x : K) (j : ℕ) :
    Poly4 K :=
  MvPolynomial.C (coeffs j) * reducedNumerator F cap j *
    polyH K F ^ (2 * (w - j)) *
      (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j

def reducedClearedTaylorNumerator
    (F : Poly4 K) (cap w : ℕ) (coeffs : ℕ → K) (x : K) : Poly4 K :=
  ∑ j ∈ Finset.range (w + 1),
    reducedCommonNumeratorTerm F cap w coeffs x j

def reducedAgreementNumerator
    (F : Poly4 K) (cap w : ℕ) (coeffs : ℕ → K)
    (x u₀ u₁ : K) : Poly4 K :=
  reducedClearedTaylorNumerator F cap w coeffs x -
    affineSeedPolynomial u₀ u₁ * polyH K F ^ (2 * w)

theorem commonNumeratorTerm_sub_reduced_dvd
    (F : Poly4 K) (cap w : ℕ) (coeffs : ℕ → K) (x : K) (j : ℕ) :
    F ∣ commonNumeratorTerm F w coeffs x j -
      reducedCommonNumeratorTerm F cap w coeffs x j := by
  obtain ⟨Q, hQ⟩ := numerator_sub_reducedNumerator_dvd F cap j
  refine ⟨MvPolynomial.C (coeffs j) * Q *
    polyH K F ^ (2 * (w - j)) *
      (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j, ?_⟩
  unfold commonNumeratorTerm reducedCommonNumeratorTerm
  linear_combination MvPolynomial.C (coeffs j) *
    polyH K F ^ (2 * (w - j)) *
      (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j * hQ

theorem agreementNumerator_sub_reducedAgreementNumerator_dvd
    (F : Poly4 K) (cap w : ℕ) (coeffs : ℕ → K)
    (x u₀ u₁ : K) :
    F ∣ agreementNumerator F w coeffs x u₀ u₁ -
      reducedAgreementNumerator F cap w coeffs x u₀ u₁ := by
  unfold agreementNumerator clearedTaylorNumerator
    reducedAgreementNumerator reducedClearedTaylorNumerator
  have hsum :
      F ∣ ∑ j ∈ Finset.range (w + 1),
        (commonNumeratorTerm F w coeffs x j -
          reducedCommonNumeratorTerm F cap w coeffs x j) := by
    apply Finset.dvd_sum
    intro j hj
    exact commonNumeratorTerm_sub_reduced_dvd F cap w coeffs x j
  rw [Finset.sum_sub_distrib] at hsum
  convert hsum using 1 <;> ring

theorem reducedCommonNumeratorTerm_R_degree_le
    (F : Poly4 K) (cap w : ℕ) (coeffs : ℕ → K) (x : K) (j : ℕ)
    (hcap : 1 ≤ cap) (hFcap : F.degreeOf 2 ≤ cap) (hj : j ≤ w) :
    (reducedCommonNumeratorTerm F cap w coeffs x j).degreeOf 2 ≤
      2 * w * (cap - 1) := by
  have hM := reducedNumerator_R_degree_le F cap j hcap hFcap
  have hCM :
      (MvPolynomial.C (coeffs j) * reducedNumerator F cap j).degreeOf 2 ≤
        2 * j * (cap - 1) :=
    (MvPolynomial.degreeOf_C_mul_le (reducedNumerator F cap j) 2
      (coeffs j)).trans hM
  have hH : (polyH K F).degreeOf 2 ≤ cap - 1 :=
    pderiv_same_degree_bound 2 F cap hFcap
  have hHP := degree_pow_bound 2 (2 * (w - j)) hH
  have hshift :
      ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) ^ j).degreeOf 2
        ≤ 0 := by
    simpa only [Nat.mul_zero] using degree_pow_bound 2 j
      (shiftedX_degree_bound 2 (by decide) x)
  have hmul₁ := degree_mul_bound 2 hCM hHP
  have hmul₂ := degree_mul_bound 2 hmul₁ hshift
  unfold reducedCommonNumeratorTerm
  apply hmul₂.trans
  have hw : j + (w - j) = w := by omega
  calc
    (2 * j * (cap - 1) + 2 * (w - j) * (cap - 1)) + 0 =
        2 * (j + (w - j)) * (cap - 1) := by ring
    _ ≤ 2 * w * (cap - 1) := by rw [hw]

theorem reducedClearedTaylorNumerator_R_degree_le
    (F : Poly4 K) (cap w : ℕ) (coeffs : ℕ → K) (x : K)
    (hcap : 1 ≤ cap) (hFcap : F.degreeOf 2 ≤ cap) :
    (reducedClearedTaylorNumerator F cap w coeffs x).degreeOf 2 ≤
      2 * w * (cap - 1) := by
  unfold reducedClearedTaylorNumerator
  apply degree_sum_bound 2
  intro j hj
  exact reducedCommonNumeratorTerm_R_degree_le F cap w coeffs x j hcap hFcap
    (by have hh := Finset.mem_range.mp hj; omega)

theorem reducedAgreementNumerator_R_degree_le
    (F : Poly4 K) (cap w : ℕ) (coeffs : ℕ → K)
    (x u₀ u₁ : K) (hcap : 1 ≤ cap) (hFcap : F.degreeOf 2 ≤ cap) :
    (reducedAgreementNumerator F cap w coeffs x u₀ u₁).degreeOf 2 ≤
      2 * w * (cap - 1) := by
  have hleft := reducedClearedTaylorNumerator_R_degree_le F cap w coeffs x
    hcap hFcap
  have hseed : (affineSeedPolynomial u₀ u₁).degreeOf 2 ≤ 0 :=
    affineSeedPolynomial_degree_bound 2 0
      (by simp [MvPolynomial.degreeOf_X_of_ne (by decide : (2 : Fin 4) ≠ 3)])
      u₀ u₁
  have hH : (polyH K F).degreeOf 2 ≤ cap - 1 :=
    pderiv_same_degree_bound 2 F cap hFcap
  have hHP := degree_pow_bound 2 (2 * w) hH
  have hright := degree_mul_bound 2 hseed hHP
  unfold reducedAgreementNumerator
  exact (degree_sub_bound 2 hleft
    (hright.trans (by omega)))

theorem wt_sum_le
    (weights : Fin 4 → ℕ) (I : Finset ℕ) (f : ℕ → Poly4 K) (A : ℕ)
    (hf : ∀ i ∈ I, wt weights (f i) ≤ A) :
    wt weights (∑ i ∈ I, f i) ≤ A := by
  unfold wt
  rw [← degree_weightedLift, map_sum]
  apply (MvPolynomial.degreeOf_sum_le (4 : Fin 5) I
    (fun i ↦ weightedLift K weights (f i))).trans
  apply Finset.sup_le
  intro i hi
  rw [degree_weightedLift]
  exact hf i hi

theorem shiftedX_wt_eq_zero
    (weights : Fin 4 → ℕ) (hX : weights 0 = 0) (x : K) :
    wt weights (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (wt_sub_le weights _ _).trans
  rw [wt_C, wt_X, hX]
  simp

theorem affineSeedPolynomial_wt_le
    (weights : Fin 4 → ℕ) (u₀ u₁ : K) :
    wt weights (affineSeedPolynomial u₀ u₁) ≤ weights 3 := by
  unfold affineSeedPolynomial
  apply (wt_add_le weights _ _).trans
  apply max_le
  · rw [wt_C]
    exact Nat.zero_le _
  · have hm := wt_mul_le weights (MvPolynomial.X (3 : Fin 4) : Poly4 K)
      (MvPolynomial.C u₁)
    rw [wt_X, wt_C, Nat.add_zero] at hm
    exact hm

theorem reducedCommonNumeratorTerm_wt_le_nested
    (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F : Poly4 K) (cap C w : ℕ) (coeffs : ℕ → K) (x : K) (j : ℕ)
    (hcap : 1 ≤ cap) (hcapC : cap ≤ C) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) (hj : j ≤ w) :
    wt weights (reducedCommonNumeratorTerm F cap w coeffs x j) ≤
      1 + 2 * w * (C - 1) := by
  have hM := reducedNumerator_wt_le_nested weights hX hY hR F cap C j
    hcap hcapC hC hF
  have hCM :
      wt weights (MvPolynomial.C (coeffs j) * reducedNumerator F cap j) ≤
        1 + 2 * j * (C - 1) := by
    have hm := wt_mul_le weights (MvPolynomial.C (coeffs j))
      (reducedNumerator F cap j)
    rw [wt_C, Nat.zero_add] at hm
    exact hm.trans hM
  have hH : wt weights (polyH K F) ≤ C - 1 := by
    unfold polyH
    simpa only [hR] using wt_pderiv_le weights F 2 C hF
  have hHP : wt weights (polyH K F ^ (2 * (w - j))) ≤
      2 * (w - j) * (C - 1) :=
    (wt_pow_le weights (polyH K F) (2 * (w - j))).trans
      (Nat.mul_le_mul_left _ hH)
  have hshift0 := shiftedX_wt_eq_zero weights hX x
  have hshift :
      wt weights ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) ^ j)
        ≤ 0 := by
    have hp := wt_pow_le weights
      (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) j
    rw [hshift0, Nat.mul_zero] at hp
    exact hp
  have hmul₁ := wt_mul_le weights
    (MvPolynomial.C (coeffs j) * reducedNumerator F cap j)
    (polyH K F ^ (2 * (w - j)))
  have hmul₂ := wt_mul_le weights
    (MvPolynomial.C (coeffs j) * reducedNumerator F cap j *
      polyH K F ^ (2 * (w - j)))
    ((MvPolynomial.C x - MvPolynomial.X (0 : Fin 4)) ^ j)
  unfold reducedCommonNumeratorTerm
  apply hmul₂.trans
  calc
    wt weights (MvPolynomial.C (coeffs j) * reducedNumerator F cap j *
        polyH K F ^ (2 * (w - j))) +
        wt weights ((MvPolynomial.C x - MvPolynomial.X 0 : Poly4 K) ^ j) ≤
        ((1 + 2 * j * (C - 1)) + 2 * (w - j) * (C - 1)) + 0 :=
      Nat.add_le_add (hmul₁.trans (Nat.add_le_add hCM hHP)) hshift
    _ = 1 + 2 * w * (C - 1) := by
      have hw : j + (w - j) = w := by omega
      calc
        ((1 + 2 * j * (C - 1)) + 2 * (w - j) * (C - 1)) + 0 =
            1 + 2 * (j + (w - j)) * (C - 1) := by ring
        _ = 1 + 2 * w * (C - 1) := by rw [hw]

theorem reducedClearedTaylorNumerator_wt_le_nested
    (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (F : Poly4 K) (cap C w : ℕ) (coeffs : ℕ → K) (x : K)
    (hcap : 1 ≤ cap) (hcapC : cap ≤ C) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) :
    wt weights (reducedClearedTaylorNumerator F cap w coeffs x) ≤
      1 + 2 * w * (C - 1) := by
  unfold reducedClearedTaylorNumerator
  apply wt_sum_le
  intro j hj
  exact reducedCommonNumeratorTerm_wt_le_nested weights hX hY hR F cap C w
    coeffs x j hcap hcapC hC hF
      (by have hh := Finset.mem_range.mp hj; omega)

theorem reducedAgreementNumerator_wt_le_nested
    (weights : Fin 4 → ℕ)
    (hX : weights 0 = 0) (hY : weights 1 = 1) (hR : weights 2 = 1)
    (hZ : weights 3 ≤ 1)
    (F : Poly4 K) (cap C w : ℕ) (coeffs : ℕ → K)
    (x u₀ u₁ : K)
    (hcap : 1 ≤ cap) (hcapC : cap ≤ C) (hC : 2 ≤ C)
    (hF : wt weights F ≤ C) :
    wt weights (reducedAgreementNumerator F cap w coeffs x u₀ u₁) ≤
      1 + 2 * w * (C - 1) := by
  have hleft := reducedClearedTaylorNumerator_wt_le_nested weights hX hY hR
    F cap C w coeffs x hcap hcapC hC hF
  have hseed := affineSeedPolynomial_wt_le weights u₀ u₁
  have hH : wt weights (polyH K F) ≤ C - 1 := by
    unfold polyH
    simpa only [hR] using wt_pderiv_le weights F 2 C hF
  have hHP : wt weights (polyH K F ^ (2 * w)) ≤ 2 * w * (C - 1) :=
    (wt_pow_le weights (polyH K F) (2 * w)).trans
      (Nat.mul_le_mul_left _ hH)
  have hrightMul := wt_mul_le weights (affineSeedPolynomial u₀ u₁)
    (polyH K F ^ (2 * w))
  have hright :
      wt weights (affineSeedPolynomial u₀ u₁ * polyH K F ^ (2 * w)) ≤
        1 + 2 * w * (C - 1) := by
    exact hrightMul.trans (by omega)
  unfold reducedAgreementNumerator
  exact (wt_sub_le weights _ _).trans (max_le hleft hright)

 

theorem exists_reducedAgreement_three_bounds
    (weights₁ weights₂ : Fin 4 → ℕ)
    (hX₁ : weights₁ 0 = 0) (hY₁ : weights₁ 1 = 1)
    (hR₁ : weights₁ 2 = 1) (hZ₁ : weights₁ 3 ≤ 1)
    (hX₂ : weights₂ 0 = 0) (hY₂ : weights₂ 1 = 1)
    (hR₂ : weights₂ 2 = 1) (hZ₂ : weights₂ 3 ≤ 1)
    (F : Poly4 K) (cap C₁ C₂ w : ℕ) (coeffs : ℕ → K)
    (x u₀ u₁ : K)
    (hcap : 1 ≤ cap) (hcapC₁ : cap ≤ C₁) (hcapC₂ : cap ≤ C₂)
    (hC₁ : 2 ≤ C₁) (hC₂ : 2 ≤ C₂)
    (hFcap : F.degreeOf 2 ≤ cap)
    (hF₁ : wt weights₁ F ≤ C₁) (hF₂ : wt weights₂ F ≤ C₂) :
    ∃ M : Poly4 K,
      F ∣ agreementNumerator F w coeffs x u₀ u₁ - M ∧
      M.degreeOf 2 ≤ 2 * w * (cap - 1) ∧
      wt weights₁ M ≤ 1 + 2 * w * (C₁ - 1) ∧
      wt weights₂ M ≤ 1 + 2 * w * (C₂ - 1) := by
  refine ⟨reducedAgreementNumerator F cap w coeffs x u₀ u₁,
    agreementNumerator_sub_reducedAgreementNumerator_dvd F cap w coeffs x u₀ u₁,
    reducedAgreementNumerator_R_degree_le F cap w coeffs x u₀ u₁ hcap hFcap,
    reducedAgreementNumerator_wt_le_nested weights₁ hX₁ hY₁ hR₁ hZ₁
      F cap C₁ w coeffs x u₀ u₁ hcap hcapC₁ hC₁ hF₁,
    reducedAgreementNumerator_wt_le_nested weights₂ hX₂ hY₂ hR₂ hZ₂
      F cap C₂ w coeffs x u₀ u₁ hcap hcapC₂ hC₂ hF₂⟩

end FinalWeightedBounds

end RCoefficients

end

end ContactReducedAgreementPseudoRemainder6800Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactReducedAgreementPseudoRemainder6800Research.numeratorStep_add_source_mul
#print axioms ProximityPrize.SubmissionLower.ContactReducedAgreementPseudoRemainder6800Research.numerator_succ_sub_step_dvd
#print axioms ProximityPrize.SubmissionLower.ContactReducedAgreementPseudoRemainder6800Research.liftedCoefficient_weight_le_sub
#print axioms ProximityPrize.SubmissionLower.ContactReducedAgreementPseudoRemainder6800Research.exists_reducedNumerator_three_bounds
#print axioms ProximityPrize.SubmissionLower.ContactReducedAgreementPseudoRemainder6800Research.exists_reducedAgreement_three_bounds
