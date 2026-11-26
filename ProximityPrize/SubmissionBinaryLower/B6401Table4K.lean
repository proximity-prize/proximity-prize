import ProximityPrize.SubmissionBinaryLower.B6401Table4Common
import ProximityPrize.SubmissionBinaryLower.B6401Table4NonK

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

/-!
# Table 4B (`K ≠ 0`, 84 branches) and Top-Level Table 4 Exhaustive Algebra Dichotomy

Proves:
1. `table4_K_sat`: for any `S : KerD45Syzygy D` with `S.P0 = 0` and `S.M21 ≠ 0`, `D` produces an
   exact `T4BBranch` (`rGt ∈ Bool`, `vCancel ∈ Bool`, `q1Case < 3`, `odeCase < 7`) and an explicit
   nonnegative `x : Fin 49 → ℚ` satisfying ALL rows of `B6401T4Rows.buildT4BRows br`!
2. `table4_algebra_dichotomy`: for ANY `D : KerD45Data`, EITHER `EscapeUZero D`, OR `D` satisfies
   one of the 36 Table 4A branches (`T4ABranch`) OR one of the 84 Table 4B branches (`T4BBranch`)!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401Table4K

open Polynomial B6401Params B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401IntFarkas B6401T4Rows B6401Char2ODE B6401Table4Common B6401Table4NonK
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

private def muSub : Step15Pt → ℕ
  | .k2U | .k3U => 1
  | .k2U_mb | .k3U_mb => 2
  | _ => 0

private lemma sub_zero_nr (n : ℕ) : n - 0 = n := by cases n <;> rfl

/-! ### Part 1: Shared Local Helpers (`rootMultiplicity_comp_X_sq_map`, `minimal_fourth_pow_denom`, `mbad` STEP, Wronskian & Triangle) -/

/-- Over `E = AlgebraicClosure Fld` in char 2, `((f.comp (X^2)).map ι).rootMultiplicity a = 2 * (f.map ι).rootMultiplicity (a^2)`. -/
lemma rootMultiplicity_comp_X_sq_map (f : Fld[X]) (hf : f ≠ 0) (a : AlgebraicClosure Fld) :
    ((f.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a =
      2 * (f.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2) := by
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  have hsq : (X - C a : E[X]) ^ 2 = X ^ 2 - C (a ^ 2) := by
    have h2 : (2 : E[X]) = 0 := CharTwo.two_eq_zero
    simp only [sub_eq_add_neg, CharTwo.neg_eq, map_pow]
    calc (X + C a) ^ 2 = X ^ 2 + 2 * X * C a + C a ^ 2 := by ring
      _ = X ^ 2 + C a ^ 2 := by rw [h2]; ring
  rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  have hfE : f.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hf
  have hfcE : (f.map ι).comp (X ^ 2) ≠ 0 := mt (comp_X_sq_eq_zero_iff _).mp hfE
  have hdvd_iff : ∀ k : ℕ, (X - C a) ^ (2 * k) ∣ (f.map ι).comp (X ^ 2) ↔ (X - C (a ^ 2)) ^ k ∣ f.map ι := by
    intro k; constructor
    · intro hd; rw [pow_mul, hsq] at hd
      have hcomp : ((X - C (a ^ 2)) ^ k).comp (X ^ 2) = (X ^ 2 - C (a ^ 2)) ^ k := by
        simp [pow_comp, sub_comp, X_comp, C_comp]
      rw [← hcomp] at hd; rcases hd with ⟨Q, hQ⟩
      have hQev : Q = (evenPart Q).comp (X ^ 2) := by
        have hdec := evenPart_add_X_oddPart Q
        have hodd : oddPart Q = 0 := by
          have h1 := congrArg Polynomial.derivative hQ
          rw [derivative_comp_X_sq_char2, derivative_mul, derivative_comp_X_sq_char2, zero_mul, zero_add] at h1
          have hQ' : Q.derivative = 0 := (mul_eq_zero.mp h1.symm).resolve_left (by
            rw [hcomp]; exact pow_ne_zero k (by rw [← hsq]; exact pow_ne_zero 2 (X_sub_C_ne_zero a)))
          have h2 := congrArg Polynomial.derivative hdec
          rw [derivative_even_odd_char2, hQ'] at h2; exact (comp_X_sq_eq_zero_iff _).mp h2
        rw [hodd, zero_comp, mul_zero, add_zero] at hdec; exact hdec.symm
      refine ⟨evenPart Q, ?_⟩
      apply sub_eq_zero.mp
      apply (comp_X_sq_eq_zero_iff _).mp; rw [sub_comp, mul_comp, hQ, ← hQev, sub_self]
    · rintro ⟨Q, hQ⟩; exact ⟨Q.comp (X ^ 2), by rw [pow_mul, hsq, hQ, mul_comp, pow_comp, sub_comp, X_comp, C_comp]⟩
  apply le_antisymm
  · have hd := pow_rootMultiplicity_dvd ((f.map ι).comp (X ^ 2)) a
    set r := ((f.map ι).comp (X ^ 2)).rootMultiplicity a
    have hr_ev : r % 2 = 0 := by
      by_contra hodd
      obtain ⟨Q, hQ⟩ := (hdvd_iff (r / 2)).mp ((pow_dvd_pow _ (by omega : 2 * (r / 2) ≤ r)).trans hd)
      have hQcomp : (f.map ι).comp (X ^ 2) = (X - C a) ^ (2 * (r / 2)) * Q.comp (X ^ 2) := by
        rw [hQ, mul_comp, pow_comp, sub_comp, X_comp, C_comp, ← hsq, ← pow_mul]
      have hmul_dvd : (X - C a) ^ (2 * (r / 2) + 1) ∣ (X - C a) ^ (2 * (r / 2)) * Q.comp (X ^ 2) := by
        rw [← hQcomp]; exact (pow_dvd_pow _ (by omega : 2 * (r / 2) + 1 ≤ r)).trans hd
      rw [pow_succ] at hmul_dvd
      have hd1 := (mul_dvd_mul_iff_left (pow_ne_zero _ (X_sub_C_ne_zero a))).mp hmul_dvd
      have hQ0 : Q.eval (a ^ 2) = 0 := by simpa [IsRoot, eval_comp] using dvd_iff_isRoot.mp hd1
      rcases dvd_iff_isRoot.mpr hQ0 with ⟨W, hW⟩
      have hle := (le_rootMultiplicity_iff hfcE).mpr ((hdvd_iff (r / 2 + 1)).mpr ⟨W, by rw [hQ, hW]; ring⟩)
      omega
    have hle := (le_rootMultiplicity_iff hfE).mpr ((hdvd_iff (r / 2)).mp (by rw [show 2 * (r / 2) = r by omega]; exact hd))
    change r ≤ 2 * (f.map ι).rootMultiplicity (a ^ 2)
    omega
  · exact (le_rootMultiplicity_iff hfcE).mpr ((hdvd_iff _).mpr (pow_rootMultiplicity_dvd _ _))

/-- Exact `rootMultiplicity` of `f^n` for any `f ≠ 0`. -/
lemma rootMultiplicity_pow_eq' {E : Type*} [Field E] (f : E[X]) (hf : f ≠ 0) (n : ℕ) (a : E) :
    (f ^ n).rootMultiplicity a = n * f.rootMultiplicity a := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hf) hf), ih]; ring

/-- Over `E = AlgebraicClosure Fld`, `((sqrtPoly f).map ι).rootMultiplicity a = (f.map ι).rootMultiplicity (a^2)`. -/
lemma rootMultiplicity_sqrtPoly_map (f : Fld[X]) (hf : f ≠ 0) (a : AlgebraicClosure Fld) :
    ((sqrtPoly f).map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a =
      (f.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2) := by
  have hsf_ne : sqrtPoly f ≠ 0 := mt (sqrtPoly_eq_zero_iff f).mp hf
  have hsfE : (sqrtPoly f).map (algebraMap Fld (AlgebraicClosure Fld)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap Fld (AlgebraicClosure Fld)).injective).mpr hsf_ne
  have h1 := congrArg (fun g : Fld[X] => (g.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a) (sqrtPoly_sq f)
  rw [Polynomial.map_pow, rootMultiplicity_pow_eq' _ hsfE 2 a, rootMultiplicity_comp_X_sq_map f hf a] at h1
  omega

/-- Minimal polynomial `C0 ∈ Fld[X]` such that `Q_red ∣ C0^4` with exact local order `4 * v_a(C0) = c04Val(v_a(Q_red))`! -/
private lemma exists_min_fourth_pow_cover (Q_red : Fld[X]) (hQ : Q_red ≠ 0) :
    ∃ C0 : Fld[X], C0 ≠ 0 ∧ Q_red ∣ C0 ^ 4 ∧
      ∀ a : AlgebraicClosure Fld,
        4 * (C0.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a =
          Step15Pt.c04Val ((Q_red.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) := by
  classical
  set ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  induction hn : Q_red.natDegree using Nat.strong_induction_on generalizing Q_red with
  | ind d ih =>
      by_cases hu : IsUnit Q_red
      · refine ⟨1, one_ne_zero, hu.dvd, fun a => ?_⟩
        have h0 : (Q_red.map ι).natDegree = 0 := by
          rw [natDegree_map_eq_of_injective ι.injective, natDegree_eq_zero_of_isUnit hu]
        have hne : Q_red.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hQ
        have hrm0 : (Q_red.map ι).rootMultiplicity a = 0 := by
          have := natDegree_le_of_dvd (pow_rootMultiplicity_dvd (Q_red.map ι) a) hne
          rw [natDegree_pow, natDegree_X_sub_C, mul_one, h0] at this; omega
        simp [hrm0, Step15Pt.c04Val]
      · obtain ⟨π, hπ_irr, hπ_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hQ
        have hπ_ne : π ≠ 0 := hπ_irr.ne_zero
        have hπ_pos : 0 < π.natDegree := by
          by_contra h0
          have hC := Polynomial.eq_C_of_natDegree_eq_zero (show π.natDegree = 0 by omega)
          have hc0 : π.coeff 0 ≠ 0 := fun h => hπ_ne (by rwa [h, map_zero] at hC)
          exact hπ_irr.not_isUnit (by rw [hC]; exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
        have hex : ∃ m : ℕ, 1 ≤ m ∧ π ^ m ∣ Q_red ∧ ¬ π ^ (m + 1) ∣ Q_red := by
          have hle_deg : ∀ k, π ^ k ∣ Q_red → k ≤ Q_red.natDegree := fun k hk => by
            have := natDegree_le_of_dvd hk hQ; rw [natDegree_pow] at this; nlinarith
          let S_m := (Finset.range (Q_red.natDegree + 1)).filter fun k => π ^ k ∣ Q_red
          have h1_mem : 1 ∈ S_m := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
            have := hle_deg 1 (by rw [pow_one]; exact hπ_dvd); omega), by rw [pow_one]; exact hπ_dvd⟩
          let m := S_m.max' ⟨1, h1_mem⟩
          have hm_mem := Finset.max'_mem S_m ⟨1, h1_mem⟩
          have hm_ge : 1 ≤ m := Finset.le_max' S_m 1 h1_mem
          have hm_dvd : π ^ m ∣ Q_red := (Finset.mem_filter.mp hm_mem).2
          have hm_not : ¬ π ^ (m + 1) ∣ Q_red := by
            intro h1
            have hmem1 : m + 1 ∈ S_m := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
              have := hle_deg (m + 1) h1; omega), h1⟩
            have := Finset.le_max' S_m (m + 1) hmem1; omega
          exact ⟨m, hm_ge, hm_dvd, hm_not⟩
        obtain ⟨m, hm1, ⟨Q', hQ'⟩, hm_not⟩ := hex
        have hQ'_ne : Q' ≠ 0 := by intro h0; rw [h0, mul_zero] at hQ'; exact hQ hQ'
        have hπ_ndvd : ¬ π ∣ Q' := by
          intro ⟨w, hw⟩; apply hm_not; exact ⟨w, by rw [hQ', hw, pow_succ]; ring⟩
        have hQ'_lt : Q'.natDegree < d := by
          have hdeg := congrArg Polynomial.natDegree hQ'
          rw [natDegree_mul (pow_ne_zero m hπ_ne) hQ'_ne, natDegree_pow] at hdeg; nlinarith
        obtain ⟨C0', hC0'_ne, hQ'_dvd, hC0'_rm⟩ := ih Q'.natDegree hQ'_lt Q' hQ'_ne rfl
        let e : ℕ := (m + 3) / 4
        refine ⟨π ^ e * C0', mul_ne_zero (pow_ne_zero e hπ_ne) hC0'_ne, ?_, ?_⟩
        · rw [hQ', mul_pow, ← pow_mul]
          exact mul_dvd_mul (pow_dvd_pow π (by dsimp [e]; omega)) hQ'_dvd
        · intro a
          have hπ_sf : Squarefree π := hπ_irr.squarefree
          have hπ_rm_le : (π.map ι).rootMultiplicity a ≤ 1 := rootMultiplicity_map_le_one_of_squarefree hπ_sf a
          have hcop : IsCoprime (π.map ι) (Q'.map ι) :=
            (hπ_irr.coprime_iff_not_dvd.mpr hπ_ndvd).map (Polynomial.mapRingHom ι)
          have hπE := (Polynomial.map_ne_zero_iff ι.injective).mpr hπ_ne
          have hQ'E := (Polynomial.map_ne_zero_iff ι.injective).mpr hQ'_ne
          have hC0'E := (Polynomial.map_ne_zero_iff ι.injective).mpr hC0'_ne
          rw [Polynomial.map_mul, Polynomial.map_pow,
            rootMultiplicity_mul (mul_ne_zero (pow_ne_zero e hπE) hC0'E),
            rootMultiplicity_pow_eq' (π.map ι) hπE e a, hQ', Polynomial.map_mul, Polynomial.map_pow,
            rootMultiplicity_mul (mul_ne_zero (pow_ne_zero m hπE) hQ'E),
            rootMultiplicity_pow_eq' (π.map ι) hπE m a]
          by_cases hπa : (π.map ι).rootMultiplicity a = 0
          · rw [hπa, mul_zero, zero_add, mul_zero, zero_add]; exact hC0'_rm a
          · have hπ1 : (π.map ι).rootMultiplicity a = 1 := by omega
            have hQ'a : (Q'.map ι).rootMultiplicity a = 0 := by
              apply rootMultiplicity_eq_zero_iff.mpr; intro hr; exfalso
              have hdπ : X - C a ∣ π.map ι := by
                have := pow_rootMultiplicity_dvd (π.map ι) a; rwa [hπ1, pow_one] at this
              have hu1 := hcop.isUnit_of_dvd' hdπ (dvd_iff_isRoot.mpr hr)
              have h0 := natDegree_eq_zero_of_isUnit hu1; rw [natDegree_X_sub_C] at h0; omega
            have hC0'a : (C0'.map ι).rootMultiplicity a = 0 := by
              have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
              have h := hC0'_rm a; rw [hι] at h hQ'a ⊢; rw [hQ'a, Nat.cast_zero] at h
              have hc04 : Step15Pt.c04Val 0 = 0 := rfl
              rw [hc04] at h; omega
            rw [hπ1, hQ'a, hC0'a, mul_one, add_zero, mul_one, add_zero]
            have hmpos : ¬ ((m : ℤ) ≤ 0) := by omega
            unfold Step15Pt.c04Val; simp only [hmpos, ↓reduceIte, Int.toNat_natCast]
            dsimp [e]; ring

/-- Minimal 4th-power denominator `C0 ∈ Fld[X]` for a rational function `P / Q` (`Q ∣ P * C0^4`). -/
theorem exists_minimal_fourth_pow_denom (P Q : Fld[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ C0 : Fld[X], C0 ≠ 0 ∧ Q ∣ P * C0 ^ 4 ∧
      ∀ a : AlgebraicClosure Fld,
        4 * (C0.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a =
          Step15Pt.c04Val (((Q.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
            ((P.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ)) := by
  set ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  obtain ⟨g, hg_eq⟩ : ∃ g : Fld[X], g = EuclideanDomain.gcd P Q := ⟨_, rfl⟩
  have hg_ne : g ≠ 0 := fun h0 => hP (EuclideanDomain.gcd_eq_zero_iff.mp (hg_eq ▸ h0)).1
  rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_left P Q) with ⟨P', hP'⟩
  rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_right P Q) with ⟨Q', hQ'⟩
  have hP'_ne : P' ≠ 0 := by intro h0; rw [h0, mul_zero] at hP'; exact hP hP'
  have hQ'_ne : Q' ≠ 0 := by intro h0; rw [h0, mul_zero] at hQ'; exact hQ hQ'
  have hcop : IsCoprime P' Q' := by
    have hbez : g = P * EuclideanDomain.gcdA P Q + Q * EuclideanDomain.gcdB P Q :=
      hg_eq.trans (EuclideanDomain.gcd_eq_gcd_ab P Q)
    refine ⟨EuclideanDomain.gcdA P Q, EuclideanDomain.gcdB P Q, ?_⟩
    apply mul_left_cancel₀ hg_ne
    calc g * (EuclideanDomain.gcdA P Q * P' + EuclideanDomain.gcdB P Q * Q')
        = (g * P') * EuclideanDomain.gcdA P Q + (g * Q') * EuclideanDomain.gcdB P Q := by ring
      _ = P * EuclideanDomain.gcdA P Q + Q * EuclideanDomain.gcdB P Q := by rw [← hP', ← hQ']
      _ = g := hbez.symm
      _ = g * 1 := (mul_one g).symm
  obtain ⟨C0, hC0_ne, hQ'_dvd, hC0_rm⟩ := exists_min_fourth_pow_cover Q' hQ'_ne
  refine ⟨C0, hC0_ne, ?_, ?_⟩
  · rcases hQ'_dvd with ⟨W, hW⟩
    exact ⟨P' * W, by rw [hP', hQ', hW]; ring⟩
  · intro a
    rw [hC0_rm a]
    have hgE := (Polynomial.map_ne_zero_iff ι.injective).mpr hg_ne
    have hP'E := (Polynomial.map_ne_zero_iff ι.injective).mpr hP'_ne
    have hQ'E := (Polynomial.map_ne_zero_iff ι.injective).mpr hQ'_ne
    have hdisj : (P'.map ι).rootMultiplicity a = 0 ∨ (Q'.map ι).rootMultiplicity a = 0 := by
      by_contra h; push Not at h
      have hd1 : X - C a ∣ P'.map ι := by
        have := (pow_dvd_pow (X - C a) (by omega : 1 ≤ (P'.map ι).rootMultiplicity a)).trans (pow_rootMultiplicity_dvd _ a)
        rwa [pow_one] at this
      have hd2 : X - C a ∣ Q'.map ι := by
        have := (pow_dvd_pow (X - C a) (by omega : 1 ≤ (Q'.map ι).rootMultiplicity a)).trans (pow_rootMultiplicity_dvd _ a)
        rwa [pow_one] at this
      have hu := (hcop.map (Polynomial.mapRingHom ι)).isUnit_of_dvd' hd1 hd2
      have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
    rw [hP', hQ', Polynomial.map_mul, Polynomial.map_mul,
      rootMultiplicity_mul (mul_ne_zero hgE hP'E), rootMultiplicity_mul (mul_ne_zero hgE hQ'E)]
    rcases hdisj with h0 | h0
    · rw [h0]; congr 1; simp only [ι] at *; omega
    · rw [h0]; simp only [ι] at *; unfold Step15Pt.c04Val; simp

/-- Helper to evaluate `evalRow` of `mkR15` cleanly after `List.filter`. -/
lemma evalRow_filter_nz {nv : ℕ} (x : Fin nv → ℚ) (l : List (Nat × Int)) :
    ((l.filter fun p => p.2 != 0).map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum =
      (l.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      by_cases h0 : a.2 = 0
      · simp [h0, ih]
      · have hne : (a.2 != 0) = true := by simp [h0]
        simp [hne, ih]

lemma rowValid_filter_nz {nv : ℕ} (l : List (Nat × Int)) (num4 : ℤ) (eps : Bool)
    (h : ∀ e ∈ l, e.1 < nv) : RowValid nv (mkStat (l.filter fun p => p.2 != 0) num4 eps) :=
  rowValid_mkStat _ _ _ (fun e he => h e (List.mem_of_mem_filter he))

/-- In char 2, if `N' = C c0` and `N(a) = H(a) = 0`, then `(X - C a)^2 ∣ C c0 * H + N * H'`. -/
lemma wronskian_sq_dvd_of_common_root {E : Type*} [Field E] [CharP E 2]
    {c0 : E} {N H : E[X]} (hN' : N.derivative = C c0) (a : E)
    (hNa : N.eval a = 0) (hHa : H.eval a = 0) :
    (X - C a) ^ 2 ∣ C c0 * H + N * H.derivative := by
  rcases dvd_iff_isRoot.mpr hNa with ⟨N1, hN1⟩
  rcases dvd_iff_isRoot.mpr hHa with ⟨H1, hH1⟩
  have hN1_ev : N1.eval a = c0 := by
    have hd := congrArg Polynomial.derivative hN1
    rw [hN', derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hd
    have hev := congrArg (Polynomial.eval a) hd
    simp only [eval_C, eval_add, eval_mul, eval_sub, eval_X, sub_self, zero_mul, add_zero] at hev
    exact hev.symm
  have hfac : C c0 * H + N * H.derivative =
      (X - C a) * ((C c0 + N1) * H1 + (X - C a) * N1 * H1.derivative) := by
    rw [hN1, hH1, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
    ring
  have hsum_ev : ((C c0 + N1) * H1 + (X - C a) * N1 * H1.derivative).eval a = 0 := by
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero, hN1_ev]
    rw [CharTwo.add_self_eq_zero, zero_mul]
  rcases dvd_iff_isRoot.mpr hsum_ev with ⟨W, hW⟩
  refine ⟨W, ?_⟩
  rw [hfac, hW]; ring

/-- Valuation triangle lemma for a 4-term char-2 identity `T1 + T2 + T3 = T4`. -/
lemma tri_of_four_term_id {E : Type*} [Field E] [CharP E 2]
    {T1 T2 T3 T4 : E[X]} (a : E) (hT3 : T3 ≠ 0) (hT4 : T4 ≠ 0)
    (hid : T1 + T2 + T3 = T4)
    {t1 t2 t3 t4 s : ℕ}
    (h1 : (X - C a) ^ (t1 - s) ∣ T1) (h2 : (X - C a) ^ (t2 - s) ∣ T2)
    (hs1 : s ≤ t1) (hs2 : s ≤ t2) (hs3 : s ≤ t3) (hs4 : s ≤ t4)
    (h3 : T3.rootMultiplicity a = t3 - s) (h4 : T4.rootMultiplicity a = t4 - s) :
    (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4) := by
  have hsum : T1 + T2 = T3 + T4 := by
    have hadd := congrArg (· + T3) hid
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, add_comm T4 T3] at hadd
    exact hadd
  have hdvd_sum : (X - C a) ^ (min (t1 - s) (t2 - s)) ∣ T3 + T4 := by
    rw [← hsum]
    exact dvd_add ((pow_dvd_pow _ (min_le_left _ _)).trans h1)
      ((pow_dvd_pow _ (min_le_right _ _)).trans h2)
  have haux : ∀ {A B : E[X]} (hA : A ≠ 0) (hB : B ≠ 0),
      A.rootMultiplicity a < B.rootMultiplicity a →
      A + B ≠ 0 ∧ (A + B).rootMultiplicity a = A.rootMultiplicity a := by
    intro A B hA hB hlt
    have hAB_ne : A + B ≠ 0 := by
      intro h0
      have hBeq : B = A := by
        have hadd := congrArg (· + A) h0
        rw [add_comm A B, add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at hadd
        exact hadd
      rw [hBeq] at hlt; omega
    refine ⟨hAB_ne, le_antisymm ?_ ?_⟩
    · by_contra hgt
      have hge : A.rootMultiplicity a + 1 ≤ (A + B).rootMultiplicity a := by omega
      have hd1 : (X - C a) ^ (A.rootMultiplicity a + 1) ∣ A + B :=
        (pow_dvd_pow _ hge).trans (pow_rootMultiplicity_dvd (A + B) a)
      have hd2 : (X - C a) ^ (A.rootMultiplicity a + 1) ∣ B :=
        (pow_dvd_pow _ (by omega : A.rootMultiplicity a + 1 ≤ B.rootMultiplicity a)).trans
          (pow_rootMultiplicity_dvd B a)
      have hdA : (X - C a) ^ (A.rootMultiplicity a + 1) ∣ A := by
        have hrew : A = (A + B) + B := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        conv_rhs => rw [hrew]
        exact dvd_add hd1 hd2
      have := (le_rootMultiplicity_iff hA).mpr hdA
      omega
    · apply (le_rootMultiplicity_iff hAB_ne).mpr
      exact dvd_add (pow_rootMultiplicity_dvd A a)
        ((pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd B a))
  constructor
  · intro hgt
    obtain ⟨hne, hrm⟩ := haux hT3 hT4 (by omega)
    have hle := (le_rootMultiplicity_iff hne).mpr hdvd_sum
    rw [hrm, h3] at hle; omega
  · intro hlt
    obtain ⟨hne, hrm⟩ := haux hT4 hT3 (by omega)
    rw [add_comm T4 T3] at hne hrm
    have hle := (le_rootMultiplicity_iff hne).mpr hdvd_sum
    rw [hrm, h4] at hle; omega

/-- Direct `mbad` (`k2U_mb` and `k3U_mb`) STEP inequalities using `mu_ex = v_T(M0s) - 2`! -/
lemma step15_mbad_0A {k3 L0 mu_ex lam g b e1 c : ℕ}
    (hk3 : k3 ≤ 1) (hb : b ≤ 1) (hL0_ev : L0 % 2 = 0)
    (hL0_zero : k3 = 0 → L0 = 0)
    (hmu_k3 : k3 = 1 → 1 + L0 / 2 ≤ mu_ex)
    (hS : g ≤ 1 + lam) (hb1 : b = 1 → g + 2 ≤ 1 + lam)
    (htot : c + e1 + 1 = 2 * g + b) :
    2 * ((c : ℤ) - (e1 : ℤ)) ≤ 4 - 4 * (k3 : ℤ) + 11 * (mu_ex : ℤ) + 6 * (lam : ℤ) - 2 * (L0 : ℤ) := by
  by_cases h3 : k3 = 0
  · have hL := hL0_zero h3; subst h3; subst hL
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · omega
    · have := hb1 rfl; omega
  · have hk1 : k3 = 1 := by omega
    have hm := hmu_k3 hk1; subst hk1
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · omega
    · have := hb1 rfl; omega

lemma step15_mbad_0C_0 {k3 L0 mu_ex lam e1 c : ℕ}
    (hk3 : k3 ≤ 1) (hL0_ev : L0 % 2 = 0)
    (hL0_zero : k3 = 0 → L0 = 0)
    (hmu_k3 : k3 = 1 → 1 + L0 / 2 ≤ mu_ex)
    (htot : c + e1 = 1 + 2 * lam) :
    2 * ((c : ℤ) - (e1 : ℤ)) ≤ 7 - 10 * (k3 : ℤ) + 10 * (mu_ex : ℤ) + 9 * (lam : ℤ) - 5 * (L0 : ℤ) := by
  by_cases h3 : k3 = 0
  · have hL := hL0_zero h3; subst h3; subst hL; omega
  · have hk1 : k3 = 1 := by omega
    have hm := hmu_k3 hk1; subst hk1; omega

lemma step15_mbad_0C_1 {k3 L0 mu_ex lam e1 c : ℕ}
    (hk3 : k3 ≤ 1) (hL0_ev : L0 % 2 = 0)
    (hL0_zero : k3 = 0 → L0 = 0)
    (hmu_k3 : k3 = 1 → 1 + L0 / 2 ≤ mu_ex)
    (htot : c + e1 = 1 + 2 * lam) :
    2 * ((c : ℤ) - (e1 : ℤ)) ≤ 3 - 2 * (k3 : ℤ) + 10 * (mu_ex : ℤ) + 5 * (lam : ℤ) - (L0 : ℤ) := by
  by_cases h3 : k3 = 0
  · have hL := hL0_zero h3; subst h3; subst hL; omega
  · have hk1 : k3 = 1 := by omega
    have hm := hmu_k3 hk1; subst hk1; omega

lemma step15_mbad_C04 {k3 L0 mu_ex lam g b e1 c : ℕ}
    (hk3 : k3 ≤ 1) (hb : b ≤ 1) (hL0_ev : L0 % 2 = 0)
    (hL0_zero : k3 = 0 → L0 = 0)
    (hmu_k3 : k3 = 1 → 1 + L0 / 2 ≤ mu_ex)
    (hS : g ≤ 1 + lam) (hb1 : b = 1 → g + 2 ≤ 1 + lam)
    (htot : c + e1 + 1 = 2 * g + b) :
    (Step15Pt.c04Val ((c : ℤ) - (e1 : ℤ) - 1 - 2 * (mu_ex : ℤ)) : ℤ) ≤
      4 - 4 * (k3 : ℤ) + 4 * (mu_ex : ℤ) + 4 * (lam : ℤ) - 2 * (L0 : ℤ) := by
  set v : ℤ := (c : ℤ) - (e1 : ℤ) - 1 - 2 * (mu_ex : ℤ)
  have hcle : (Step15Pt.c04Val v : ℤ) = 0 ∨ (0 < v ∧ (Step15Pt.c04Val v : ℤ) ≤ v + 3) := by
    unfold Step15Pt.c04Val
    by_cases hv : v ≤ 0
    · left; simp [hv]
    · right
      have hpos : 0 < v := by omega
      simp only [hv, ↓reduceIte]
      have hto : (v.toNat : ℤ) = v := Int.toNat_of_nonneg (by omega)
      refine ⟨hpos, ?_⟩
      push_cast; rw [hto]; omega
  by_cases h3 : k3 = 0
  · have hL := hL0_zero h3; subst h3; subst hL
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · rcases hcle with h0 | ⟨_, hle⟩ <;> omega
    · have := hb1 rfl; rcases hcle with h0 | ⟨_, hle⟩ <;> omega
  · have hk1 : k3 = 1 := by omega
    have hm := hmu_k3 hk1; subst hk1
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · rcases hcle with h0 | ⟨_, hle⟩ <;> omega
    · have := hb1 rfl; rcases hcle with h0 | ⟨_, hle⟩ <;> omega

/-! ### Part 2: Exact `K ≠ 0` Structural Package (`KerD45KData`) -/

/-- Exact algebraic decomposition for `S.P0 = 0 ∧ S.M21 ≠ 0` (works for BOTH `S.R ≠ 0` and `S.R = 0`). -/
structure KerD45KData {D : KerD45Data} (S : KerD45Syzygy D) where
  p1 : Fld[X]
  q1 : Fld[X]
  K1 : Fld[X]
  Lam1 : Fld[X]
  P1s : Fld[X]
  C1s : Fld[X]
  B1s : Fld[X]
  M20s : Fld[X]
  M0s : Fld[X]
  g2t : Fld[X]
  R1 : Fld[X]
  hp_fac : S.p = S.D2 * p1
  hq_fac : S.q = S.D2 * q1
  hp1_ne : p1 ≠ 0
  hp1_q1_cop : IsCoprime p1 q1
  hD2_q1_cop : IsCoprime S.D2 q1
  hK1_ne : K1 ≠ 0
  hLam1_ne : Lam1 ≠ 0
  hP1s : D.Pj 1 = K1 * P1s
  hC1s : D.Cj 1 = K1 * C1s
  hB1s : D.Bj 1 = K1 * B1s
  hstar_cop : ∀ d : Fld[X], d ∣ P1s → d ∣ C1s → d ∣ B1s → IsUnit d
  hM21_fac : S.M21 = S.D2 ^ 2 * p1 ^ 4 * K1 * Lam1
  hM10_fac : S.M10 = q1 ^ 2 * K1 * Lam1
  hM20_fac : S.M20 = Lam1 * M20s
  hM0s_def : M0s = M20s + S.D2 * p1 ^ 2 * q1 * K1
  hM0s_ne : M0s ≠ 0
  hg2t_def : g2t = C1s.comp (X ^ 2) + X * B1s.comp (X ^ 2)
  hg1_fac : D.gj 1 = K1.comp (X ^ 2) * g2t
  hQ2_fac : S.Q2 = (Lam1 * M0s) ^ 2
  hR_fac : S.R = S.D1 * R1
  hR1_sq : R1 ^ 2 = q1.comp (X ^ 2)
  hr21_p : D.Cj 2 * B1s + C1s * D.Bj 2 = S.p * (S.D2 ^ 2 * p1 ^ 4 * Lam1)
  hplucker : S.D2.comp (X ^ 2) ^ 2 * p1.comp (X ^ 2) ^ 4 * D.gj 0 +
      M20s.comp (X ^ 2) * g2t + q1.comp (X ^ 2) ^ 2 * D.gj 2 = 0
  hH1_fac : S.H1 = S.D1 ^ 4 * M0s.comp (X ^ 2) * g2t
  hg2t_ne : g2t ≠ 0
  hg1_ne : D.gj 1 ≠ 0
  hResY_fac : D.ResY = S.D1 ^ 4 * Lam1.comp (X ^ 2) ^ 4 * M0s.comp (X ^ 2) ^ 5 * g2t
  hD1_dvd_g2t : S.D1 ∣ g2t
  hwr_g2t_g2 : (g2t * D.gj 2).derivative = S.D1 ^ 6 * p1.comp (X ^ 2) ^ 5 * Lam1.comp (X ^ 2)
  h4term_y0 : ∀ y0 : Fld,
      let Uy0 := S.p.comp (X ^ 2) * C y0 + S.R
      let U1_y0 := S.D1 * p1.comp (X ^ 2) * C y0 + R1
      M0s.comp (X ^ 2) * g2t +
        S.D1 ^ 4 * p1.comp (X ^ 2) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
        p1.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1 = D.gj 2 * U1_y0 ^ 4
  hLam1_d2_id : ∀ y0 : Fld,
      S.c * (q1 + C (y0 ^ 2) * S.D2 * p1 ^ 2) ^ 2 * Lam1 =
        D.A0sh y0 0 * B1s + (P1s + C y0 * B1s) * D.Bsh y0 0

/-- Construct `KerD45KData S` from `S.P0 = 0` and `S.M21 ≠ 0`! -/
noncomputable def mkKerD45KData {D : KerD45Data} (S : KerD45Syzygy D)
    (hP0 : S.P0 = 0) (hM21 : S.M21 ≠ 0) : KerD45KData S := by
  let p1 : Fld[X] := S.p / S.D2
  let q1 : Fld[X] := S.q / S.D2
  have hp_fac : S.p = S.D2 * p1 := (EuclideanDomain.mul_div_cancel' S.D2_ne_zero S.D2_dvd_p).symm
  have hq_fac : S.q = S.D2 * q1 := (EuclideanDomain.mul_div_cancel' S.D2_ne_zero S.D2_dvd_q).symm
  have hp1_ne : p1 ≠ 0 := by intro h0; rw [h0, mul_zero] at hp_fac; exact S.hp hp_fac
  have hp1_q1_cop : IsCoprime p1 q1 := by
    have hbez := EuclideanDomain.gcd_eq_gcd_ab S.p S.q
    refine ⟨EuclideanDomain.gcdA S.p S.q, EuclideanDomain.gcdB S.p S.q, ?_⟩
    apply mul_left_cancel₀ S.D2_ne_zero
    calc S.D2 * (EuclideanDomain.gcdA S.p S.q * p1 + EuclideanDomain.gcdB S.p S.q * q1)
        = (S.D2 * p1) * EuclideanDomain.gcdA S.p S.q + (S.D2 * q1) * EuclideanDomain.gcdB S.p S.q := by ring
      _ = S.p * EuclideanDomain.gcdA S.p S.q + S.q * EuclideanDomain.gcdB S.p S.q := by rw [← hp_fac, ← hq_fac]
      _ = S.D2 := hbez.symm
      _ = S.D2 * 1 := (mul_one S.D2).symm
  have hD2_q1_cop : IsCoprime S.D2 q1 := S.D2_coprime_q_div_D2
  have hD2p1_q1_cop : IsCoprime (S.D2 ^ 2 * p1 ^ 4) (q1 ^ 2) :=
    (hD2_q1_cop.pow_left.mul_left hp1_q1_cop.pow_left).pow_right
  have hP0_red : S.D2 ^ 2 * p1 ^ 4 * S.M10 = q1 ^ 2 * S.M21 := by
    have h := hP0; unfold KerD45Syzygy.P0 at h
    have hadd := congrArg (· + S.q ^ 2 * S.M21) h
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add, hp_fac, hq_fac] at hadd
    apply mul_left_cancel₀ (pow_ne_zero 2 S.D2_ne_zero)
    calc S.D2 ^ 2 * (S.D2 ^ 2 * p1 ^ 4 * S.M10) = (S.D2 * p1) ^ 4 * S.M10 := by ring
      _ = (S.D2 * q1) ^ 2 * S.M21 := hadd
      _ = S.D2 ^ 2 * (q1 ^ 2 * S.M21) := by ring
  have hK_ex : ∃ K : Fld[X], S.M21 = S.D2 ^ 2 * p1 ^ 4 * K :=
    hD2p1_q1_cop.dvd_of_dvd_mul_left ⟨S.M10, hP0_red.symm⟩
  let K : Fld[X] := Classical.choose hK_ex
  have hM21_K : S.M21 = S.D2 ^ 2 * p1 ^ 4 * K := Classical.choose_spec hK_ex
  have hK_ne : K ≠ 0 := by intro h0; rw [h0, mul_zero] at hM21_K; exact hM21 hM21_K
  have hM10_K : S.M10 = q1 ^ 2 * K := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 hp1_ne))
    rw [hP0_red, hM21_K]; ring
  let K1 : Fld[X] := EuclideanDomain.gcd (D.Pj 1) (EuclideanDomain.gcd (D.Cj 1) (D.Bj 1))
  have hK1_eq : K1 = EuclideanDomain.gcd (D.Pj 1) (EuclideanDomain.gcd (D.Cj 1) (D.Bj 1)) := rfl
  have hK1_ne : K1 ≠ 0 := by
    intro h0; rw [hK1_eq] at h0
    have h1 := EuclideanDomain.gcd_eq_zero_iff.mp h0
    have h2 := EuclideanDomain.gcd_eq_zero_iff.mp h1.2
    have hm := S.p_mul_M21; rw [h2.1, h2.2, mul_zero, zero_mul, add_zero] at hm
    exact mul_ne_zero S.hp hM21 hm
  have hP1s_ex : K1 ∣ D.Pj 1 := by rw [hK1_eq]; exact EuclideanDomain.gcd_dvd_left (D.Pj 1) (EuclideanDomain.gcd (D.Cj 1) (D.Bj 1))
  have hC1s_ex : K1 ∣ D.Cj 1 := by rw [hK1_eq]; exact (EuclideanDomain.gcd_dvd_right (D.Pj 1) (EuclideanDomain.gcd (D.Cj 1) (D.Bj 1))).trans (EuclideanDomain.gcd_dvd_left (D.Cj 1) (D.Bj 1))
  have hB1s_ex : K1 ∣ D.Bj 1 := by rw [hK1_eq]; exact (EuclideanDomain.gcd_dvd_right (D.Pj 1) (EuclideanDomain.gcd (D.Cj 1) (D.Bj 1))).trans (EuclideanDomain.gcd_dvd_right (D.Cj 1) (D.Bj 1))
  let P1s := Classical.choose hP1s_ex
  let C1s := Classical.choose hC1s_ex
  let B1s := Classical.choose hB1s_ex
  have hP1s : D.Pj 1 = K1 * P1s := Classical.choose_spec hP1s_ex
  have hC1s : D.Cj 1 = K1 * C1s := Classical.choose_spec hC1s_ex
  have hB1s : D.Bj 1 = K1 * B1s := Classical.choose_spec hB1s_ex
  have hstar_cop : ∀ d : Fld[X], d ∣ P1s → d ∣ C1s → d ∣ B1s → IsUnit d := by
    intro d h1 h2 h3
    have hd : K1 * d ∣ K1 := by
      conv_rhs => rw [hK1_eq]
      apply EuclideanDomain.dvd_gcd
      · rw [hP1s]; exact mul_dvd_mul_left K1 h1
      · apply EuclideanDomain.dvd_gcd
        · rw [hC1s]; exact mul_dvd_mul_left K1 h2
        · rw [hB1s]; exact mul_dvd_mul_left K1 h3
    rcases hd with ⟨u, hu⟩
    exact isUnit_iff_exists_inv.mpr ⟨u, mul_left_cancel₀ hK1_ne (by calc K1 * (d * u) = K1 * d * u := by ring
      _ = K1 := hu.symm
      _ = K1 * 1 := (mul_one K1).symm)⟩
  have hdvd_of_pcb : ∀ {a W : Fld[X]}, a ∣ S.p * W → a ∣ S.c * W → a ∣ S.b * W → a ∣ W := by
    intro a W h1 h2 h3
    by_cases ha : a = 0
    · subst ha; simp at h1; exact ⟨0, by rw [mul_zero]; exact h1.resolve_left S.hp⟩
    · obtain ⟨g, hg_eq⟩ : ∃ g : Fld[X], g = EuclideanDomain.gcd a W := ⟨_, rfl⟩
      have hg_ne : g ≠ 0 := fun h0 => ha (EuclideanDomain.gcd_eq_zero_iff.mp (hg_eq ▸ h0)).1
      rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_left a W) with ⟨a', ha'⟩
      rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_right a W) with ⟨W', hW'⟩
      have hcop : IsCoprime a' W' := by
        have hbez : g = a * EuclideanDomain.gcdA a W + W * EuclideanDomain.gcdB a W :=
          hg_eq.trans (EuclideanDomain.gcd_eq_gcd_ab a W)
        refine ⟨EuclideanDomain.gcdA a W, EuclideanDomain.gcdB a W, ?_⟩
        apply mul_left_cancel₀ hg_ne
        calc g * (EuclideanDomain.gcdA a W * a' + EuclideanDomain.gcdB a W * W')
            = (g * a') * EuclideanDomain.gcdA a W + (g * W') * EuclideanDomain.gcdB a W := by ring
          _ = a * EuclideanDomain.gcdA a W + W * EuclideanDomain.gcdB a W := by rw [← ha', ← hW']
          _ = g := hbez.symm
          _ = g * 1 := (mul_one g).symm
      have hd_one : ∀ {y : Fld[X]}, a ∣ y * W → a' ∣ y := fun {y} hy => by
        rcases hy with ⟨w, hw⟩
        exact hcop.dvd_of_dvd_mul_right ⟨w, mul_left_cancel₀ hg_ne (by calc g * (y * W') = y * (g * W') := by ring
          _ = y * W := by rw [← hW']
          _ = a * w := hw
          _ = g * (a' * w) := by rw [ha']; ring)⟩
      obtain ⟨u, hu'⟩ := S.hcop a' (hd_one h1) (hd_one h2) (hd_one h3)
      refine ⟨(u⁻¹ : Fld[X]ˣ) * W', ?_⟩
      calc W = g * W' := hW'
        _ = g * (↑u * ↑u⁻¹) * W' := by rw [Units.mul_inv, mul_one]
        _ = (g * ↑u) * (↑u⁻¹ * W') := by ring
        _ = a * (↑u⁻¹ * W') := by rw [hu', ← ha']
  have hK1_dvd_M21 : K1 ∣ S.M21 := hdvd_of_pcb
    (by rw [S.p_mul_M21, hC1s, hB1s]; exact ⟨D.Cj 2 * B1s + C1s * D.Bj 2, by ring⟩)
    (by rw [S.c_mul_M21, hP1s, hB1s]; exact ⟨D.Pj 2 * B1s + P1s * D.Bj 2, by ring⟩)
    (by rw [S.b_mul_M21, hP1s, hC1s]; exact ⟨D.Pj 2 * C1s + P1s * D.Cj 2, by ring⟩)
  have hK1_dvd_M10 : K1 ∣ S.M10 := hdvd_of_pcb
    (by rw [S.p_mul_M10, hC1s, hB1s]; exact ⟨C1s * D.Bj 0 + D.Cj 0 * B1s, by ring⟩)
    (by rw [S.c_mul_M10, hP1s, hB1s]; exact ⟨P1s * D.Bj 0 + D.Pj 0 * B1s, by ring⟩)
    (by rw [S.b_mul_M10, hP1s, hC1s]; exact ⟨P1s * D.Cj 0 + D.Pj 0 * C1s, by ring⟩)
  have hK1_dvd_K : K1 ∣ K := by
    rcases hD2p1_q1_cop with ⟨u, v, huv⟩
    have h1 : K1 ∣ u * S.M21 + v * S.M10 := dvd_add (dvd_mul_of_dvd_right hK1_dvd_M21 u) (dvd_mul_of_dvd_right hK1_dvd_M10 v)
    rw [hM21_K, hM10_K, show u * (S.D2 ^ 2 * p1 ^ 4 * K) + v * (q1 ^ 2 * K) =
      (u * (S.D2 ^ 2 * p1 ^ 4) + v * q1 ^ 2) * K by ring, huv, one_mul] at h1
    exact h1
  let Lam1 := Classical.choose hK1_dvd_K
  have hK_fac : K = K1 * Lam1 := Classical.choose_spec hK1_dvd_K
  have hLam1_ne : Lam1 ≠ 0 := by intro h0; rw [h0, mul_zero] at hK_fac; exact hK_ne hK_fac
  have hM21_fac : S.M21 = S.D2 ^ 2 * p1 ^ 4 * K1 * Lam1 := by rw [hM21_K, hK_fac]; ring
  have hM10_fac : S.M10 = q1 ^ 2 * K1 * Lam1 := by rw [hM10_K, hK_fac]; ring
  have hr21_p : D.Cj 2 * B1s + C1s * D.Bj 2 = S.p * (S.D2 ^ 2 * p1 ^ 4 * Lam1) :=
    mul_left_cancel₀ hK1_ne (by calc K1 * (D.Cj 2 * B1s + C1s * D.Bj 2) = D.Cj 2 * (K1 * B1s) + (K1 * C1s) * D.Bj 2 := by ring
      _ = S.p * S.M21 := by rw [← hB1s, ← hC1s, ← S.p_mul_M21]
      _ = K1 * (S.p * (S.D2 ^ 2 * p1 ^ 4 * Lam1)) := by rw [hM21_fac]; ring)
  have hr21_c : D.Pj 2 * B1s + P1s * D.Bj 2 = S.c * (S.D2 ^ 2 * p1 ^ 4 * Lam1) :=
    mul_left_cancel₀ hK1_ne (by calc K1 * (D.Pj 2 * B1s + P1s * D.Bj 2) = D.Pj 2 * (K1 * B1s) + (K1 * P1s) * D.Bj 2 := by ring
      _ = S.c * S.M21 := by rw [← hB1s, ← hP1s, ← S.c_mul_M21]
      _ = K1 * (S.c * (S.D2 ^ 2 * p1 ^ 4 * Lam1)) := by rw [hM21_fac]; ring)
  have hr21_b : D.Pj 2 * C1s + P1s * D.Cj 2 = S.b * (S.D2 ^ 2 * p1 ^ 4 * Lam1) :=
    mul_left_cancel₀ hK1_ne (by calc K1 * (D.Pj 2 * C1s + P1s * D.Cj 2) = D.Pj 2 * (K1 * C1s) + (K1 * P1s) * D.Cj 2 := by ring
      _ = S.b * S.M21 := by rw [← hC1s, ← hP1s, ← S.b_mul_M21]
      _ = K1 * (S.b * (S.D2 ^ 2 * p1 ^ 4 * Lam1)) := by rw [hM21_fac]; ring)
  have hr10_p : C1s * D.Bj 0 + D.Cj 0 * B1s = S.p * (q1 ^ 2 * Lam1) :=
    mul_left_cancel₀ hK1_ne (by calc K1 * (C1s * D.Bj 0 + D.Cj 0 * B1s) = (K1 * C1s) * D.Bj 0 + D.Cj 0 * (K1 * B1s) := by ring
      _ = S.p * S.M10 := by rw [← hB1s, ← hC1s, ← S.p_mul_M10]
      _ = K1 * (S.p * (q1 ^ 2 * Lam1)) := by rw [hM10_fac]; ring)
  have hr10_c : P1s * D.Bj 0 + D.Pj 0 * B1s = S.c * (q1 ^ 2 * Lam1) :=
    mul_left_cancel₀ hK1_ne (by calc K1 * (P1s * D.Bj 0 + D.Pj 0 * B1s) = (K1 * P1s) * D.Bj 0 + D.Pj 0 * (K1 * B1s) := by ring
      _ = S.c * S.M10 := by rw [← hB1s, ← hP1s, ← S.c_mul_M10]
      _ = K1 * (S.c * (q1 ^ 2 * Lam1)) := by rw [hM10_fac]; ring)
  have hr10_b : P1s * D.Cj 0 + D.Pj 0 * C1s = S.b * (q1 ^ 2 * Lam1) :=
    mul_left_cancel₀ hK1_ne (by calc K1 * (P1s * D.Cj 0 + D.Pj 0 * C1s) = (K1 * P1s) * D.Cj 0 + D.Pj 0 * (K1 * C1s) := by ring
      _ = S.b * S.M10 := by rw [← hC1s, ← hP1s, ← S.b_mul_M10]
      _ = K1 * (S.b * (q1 ^ 2 * Lam1)) := by rw [hM10_fac]; ring)
  have hsyz1s : S.p * P1s + S.c * C1s + S.b * B1s = 0 :=
    mul_left_cancel₀ hK1_ne (by calc K1 * (S.p * P1s + S.c * C1s + S.b * B1s)
        = S.p * (K1 * P1s) + S.c * (K1 * C1s) + S.b * (K1 * B1s) := by ring
      _ = 0 := by rw [← hP1s, ← hC1s, ← hB1s]; exact S.hsyz 1
      _ = K1 * 0 := (mul_zero K1).symm)
  have hLam1_dvd_M20 : Lam1 ∣ S.M20 := by
    have hC : Lam1 ∣ C1s * S.M20 := by
      refine ⟨D.Cj 2 * q1 ^ 2 + D.Cj 0 * (S.D2 ^ 2 * p1 ^ 4), mul_left_cancel₀ S.hp ?_⟩
      have hz := CharTwo.add_self_eq_zero (D.Cj 2 * D.Cj 0 * B1s)
      calc S.p * (C1s * S.M20) = C1s * (S.p * S.M20) := by ring
        _ = C1s * (D.Cj 2 * D.Bj 0 + D.Cj 0 * D.Bj 2) := by rw [S.p_mul_M20]
        _ = D.Cj 2 * (C1s * D.Bj 0 + D.Cj 0 * B1s) + D.Cj 0 * (D.Cj 2 * B1s + C1s * D.Bj 2) := by linear_combination -hz
        _ = S.p * (Lam1 * (D.Cj 2 * q1 ^ 2 + D.Cj 0 * (S.D2 ^ 2 * p1 ^ 4))) := by rw [hr10_p, hr21_p]; ring
    have hB : Lam1 ∣ B1s * S.M20 := by
      refine ⟨D.Bj 2 * q1 ^ 2 + D.Bj 0 * (S.D2 ^ 2 * p1 ^ 4), mul_left_cancel₀ S.hp ?_⟩
      have hz := CharTwo.add_self_eq_zero (C1s * D.Bj 2 * D.Bj 0)
      calc S.p * (B1s * S.M20) = B1s * (S.p * S.M20) := by ring
        _ = B1s * (D.Cj 2 * D.Bj 0 + D.Cj 0 * D.Bj 2) := by rw [S.p_mul_M20]
        _ = D.Bj 0 * (D.Cj 2 * B1s + C1s * D.Bj 2) + D.Bj 2 * (C1s * D.Bj 0 + D.Cj 0 * B1s) := by linear_combination -hz
        _ = S.p * (Lam1 * (D.Bj 2 * q1 ^ 2 + D.Bj 0 * (S.D2 ^ 2 * p1 ^ 4))) := by rw [hr10_p, hr21_p]; ring
    have hP : Lam1 ∣ P1s * S.M20 := by
      apply hdvd_of_pcb
      · have hpP : S.p * P1s = S.c * C1s + S.b * B1s := by
          have hadd := congrArg (· + (S.c * C1s + S.b * B1s)) hsyz1s
          have hz := CharTwo.add_self_eq_zero (S.c * C1s + S.b * B1s)
          linear_combination hadd - hz
        rw [← mul_assoc, hpP, add_mul, mul_assoc, mul_assoc]
        exact dvd_add (dvd_mul_of_dvd_right hC S.c) (dvd_mul_of_dvd_right hB S.b)
      · refine ⟨S.c * (D.Pj 2 * q1 ^ 2 + D.Pj 0 * (S.D2 ^ 2 * p1 ^ 4)), ?_⟩
        have hz := CharTwo.add_self_eq_zero (D.Pj 2 * D.Pj 0 * B1s)
        calc S.c * (P1s * S.M20) = P1s * (S.c * S.M20) := by ring
          _ = P1s * (D.Pj 2 * D.Bj 0 + D.Pj 0 * D.Bj 2) := by rw [S.c_mul_M20]
          _ = D.Pj 2 * (P1s * D.Bj 0 + D.Pj 0 * B1s) + D.Pj 0 * (D.Pj 2 * B1s + P1s * D.Bj 2) := by linear_combination -hz
          _ = Lam1 * (S.c * (D.Pj 2 * q1 ^ 2 + D.Pj 0 * (S.D2 ^ 2 * p1 ^ 4))) := by rw [hr10_c, hr21_c]; ring
      · refine ⟨S.b * (D.Pj 2 * q1 ^ 2 + D.Pj 0 * (S.D2 ^ 2 * p1 ^ 4)), ?_⟩
        have hz := CharTwo.add_self_eq_zero (D.Pj 2 * D.Pj 0 * C1s)
        calc S.b * (P1s * S.M20) = P1s * (S.b * S.M20) := by ring
          _ = P1s * (D.Pj 2 * D.Cj 0 + D.Pj 0 * D.Cj 2) := by rw [S.b_mul_M20]
          _ = D.Pj 2 * (P1s * D.Cj 0 + D.Pj 0 * C1s) + D.Pj 0 * (D.Pj 2 * C1s + P1s * D.Cj 2) := by linear_combination -hz
          _ = Lam1 * (S.b * (D.Pj 2 * q1 ^ 2 + D.Pj 0 * (S.D2 ^ 2 * p1 ^ 4))) := by rw [hr10_b, hr21_b]; ring
    obtain ⟨g, hg_eq⟩ : ∃ g : Fld[X], g = EuclideanDomain.gcd Lam1 S.M20 := ⟨_, rfl⟩
    have hg_ne : g ≠ 0 := fun h0 => hLam1_ne (EuclideanDomain.gcd_eq_zero_iff.mp (hg_eq ▸ h0)).1
    rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_left Lam1 S.M20) with ⟨L', hL'⟩
    rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_right Lam1 S.M20) with ⟨M', hM'⟩
    have hcop : IsCoprime L' M' := by
      have hbez : g = Lam1 * EuclideanDomain.gcdA Lam1 S.M20 + S.M20 * EuclideanDomain.gcdB Lam1 S.M20 :=
        hg_eq.trans (EuclideanDomain.gcd_eq_gcd_ab Lam1 S.M20)
      refine ⟨EuclideanDomain.gcdA Lam1 S.M20, EuclideanDomain.gcdB Lam1 S.M20, ?_⟩
      apply mul_left_cancel₀ hg_ne
      calc g * (EuclideanDomain.gcdA Lam1 S.M20 * L' + EuclideanDomain.gcdB Lam1 S.M20 * M')
          = (g * L') * EuclideanDomain.gcdA Lam1 S.M20 + (g * M') * EuclideanDomain.gcdB Lam1 S.M20 := by ring
        _ = Lam1 * EuclideanDomain.gcdA Lam1 S.M20 + S.M20 * EuclideanDomain.gcdB Lam1 S.M20 := by rw [← hL', ← hM']
        _ = g := hbez.symm
        _ = g * 1 := (mul_one g).symm
    have hd_one : ∀ {y : Fld[X]}, Lam1 ∣ y * S.M20 → L' ∣ y := fun {y} hy => by
      rcases hy with ⟨w, hw⟩
      exact hcop.dvd_of_dvd_mul_right ⟨w, mul_left_cancel₀ hg_ne (by calc g * (y * M') = y * (g * M') := by ring
        _ = y * S.M20 := by rw [← hM']
        _ = Lam1 * w := hw
        _ = g * (L' * w) := by rw [hL']; ring)⟩
    obtain ⟨u, hu⟩ := hstar_cop L' (hd_one hP) (hd_one hC) (hd_one hB)
    refine ⟨(u⁻¹ : Fld[X]ˣ) * M', ?_⟩
    calc S.M20 = g * M' := hM'
      _ = g * (↑u * ↑u⁻¹) * M' := by rw [Units.mul_inv, mul_one]
      _ = (g * ↑u) * (↑u⁻¹ * M') := by ring
      _ = Lam1 * (↑u⁻¹ * M') := by rw [hu, ← hL']
  let M20s := Classical.choose hLam1_dvd_M20
  have hM20_fac : S.M20 = Lam1 * M20s := Classical.choose_spec hLam1_dvd_M20
  let M0s : Fld[X] := M20s + S.D2 * p1 ^ 2 * q1 * K1
  let g2t : Fld[X] := C1s.comp (X ^ 2) + X * B1s.comp (X ^ 2)
  have hg1_fac : D.gj 1 = K1.comp (X ^ 2) * g2t := by
    unfold KerD45Data.gj; dsimp [g2t]; rw [hC1s, hB1s, mul_comp, mul_comp]; ring
  have hQ2_fac : S.Q2 = (Lam1 * M0s) ^ 2 := by
    unfold KerD45Syzygy.Q2; dsimp [M0s]; rw [hM20_fac, hM21_fac, hM10_fac]
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    calc (Lam1 * M20s) ^ 2 + S.D2 ^ 2 * p1 ^ 4 * K1 * Lam1 * (q1 ^ 2 * K1 * Lam1)
        = (Lam1 * M20s) ^ 2 + 2 * (Lam1 * M20s) * (Lam1 * (S.D2 * p1 ^ 2 * q1 * K1)) +
            (Lam1 * (S.D2 * p1 ^ 2 * q1 * K1)) ^ 2 := by rw [h2]; ring
      _ = (Lam1 * (M20s + S.D2 * p1 ^ 2 * q1 * K1)) ^ 2 := by ring
  have hM0s_ne : M0s ≠ 0 := by
    intro h0; apply S.Q2_ne_zero; rw [hQ2_fac, h0, mul_zero, zero_pow (by norm_num)]
  let R1 : Fld[X] := Classical.choose S.D1_dvd_R
  have hR_fac : S.R = S.D1 * R1 := Classical.choose_spec S.D1_dvd_R
  have hR1_sq : R1 ^ 2 = q1.comp (X ^ 2) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 S.D1_ne_zero)
    calc S.D1 ^ 2 * R1 ^ 2 = (S.D1 * R1) ^ 2 := by ring
      _ = S.R ^ 2 := by rw [← hR_fac]
      _ = S.q.comp (X ^ 2) := S.q_comp_X_sq.symm
      _ = S.D2.comp (X ^ 2) * q1.comp (X ^ 2) := by rw [hq_fac, mul_comp]
      _ = S.D1 ^ 2 * q1.comp (X ^ 2) := by rw [S.D1_sq]
  have hplucker : S.D2.comp (X ^ 2) ^ 2 * p1.comp (X ^ 2) ^ 4 * D.gj 0 +
      M20s.comp (X ^ 2) * g2t + q1.comp (X ^ 2) ^ 2 * D.gj 2 = 0 := by
    have hC0 : S.D2 ^ 2 * p1 ^ 4 * D.Cj 0 + M20s * C1s + q1 ^ 2 * D.Cj 2 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero S.hp (mul_ne_zero hK1_ne hLam1_ne))
      rw [mul_zero]
      have hz1 := CharTwo.add_self_eq_zero (D.Cj 2 * D.Cj 0 * D.Bj 1)
      have hz2 := CharTwo.add_self_eq_zero (D.Cj 1 * D.Cj 0 * D.Bj 2)
      have hz3 := CharTwo.add_self_eq_zero (D.Cj 2 * D.Cj 1 * D.Bj 0)
      calc S.p * (K1 * Lam1) * (S.D2 ^ 2 * p1 ^ 4 * D.Cj 0 + M20s * C1s + q1 ^ 2 * D.Cj 2)
          = (S.p * (S.D2 ^ 2 * p1 ^ 4 * K1 * Lam1)) * D.Cj 0 +
            (S.p * (Lam1 * M20s)) * (K1 * C1s) + (S.p * (q1 ^ 2 * K1 * Lam1)) * D.Cj 2 := by ring
        _ = (S.p * S.M21) * D.Cj 0 + (S.p * S.M20) * D.Cj 1 + (S.p * S.M10) * D.Cj 2 := by
            rw [← hM21_fac, ← hM20_fac, ← hC1s, ← hM10_fac]
        _ = (D.Cj 2 * D.Bj 1 + D.Cj 1 * D.Bj 2) * D.Cj 0 +
            (D.Cj 2 * D.Bj 0 + D.Cj 0 * D.Bj 2) * D.Cj 1 +
            (D.Cj 1 * D.Bj 0 + D.Cj 0 * D.Bj 1) * D.Cj 2 := by
            rw [S.p_mul_M21, S.p_mul_M20, S.p_mul_M10]
        _ = 0 := by linear_combination hz1 + hz2 + hz3
    have hB0 : S.D2 ^ 2 * p1 ^ 4 * D.Bj 0 + M20s * B1s + q1 ^ 2 * D.Bj 2 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero S.hp (mul_ne_zero hK1_ne hLam1_ne))
      rw [mul_zero]
      have hz1 := CharTwo.add_self_eq_zero (D.Cj 2 * D.Bj 1 * D.Bj 0)
      have hz2 := CharTwo.add_self_eq_zero (D.Cj 1 * D.Bj 2 * D.Bj 0)
      have hz3 := CharTwo.add_self_eq_zero (D.Cj 0 * D.Bj 2 * D.Bj 1)
      calc S.p * (K1 * Lam1) * (S.D2 ^ 2 * p1 ^ 4 * D.Bj 0 + M20s * B1s + q1 ^ 2 * D.Bj 2)
          = (S.p * (S.D2 ^ 2 * p1 ^ 4 * K1 * Lam1)) * D.Bj 0 +
            (S.p * (Lam1 * M20s)) * (K1 * B1s) + (S.p * (q1 ^ 2 * K1 * Lam1)) * D.Bj 2 := by ring
        _ = (S.p * S.M21) * D.Bj 0 + (S.p * S.M20) * D.Bj 1 + (S.p * S.M10) * D.Bj 2 := by
            rw [← hM21_fac, ← hM20_fac, ← hB1s, ← hM10_fac]
        _ = (D.Cj 2 * D.Bj 1 + D.Cj 1 * D.Bj 2) * D.Bj 0 +
            (D.Cj 2 * D.Bj 0 + D.Cj 0 * D.Bj 2) * D.Bj 1 +
            (D.Cj 1 * D.Bj 0 + D.Cj 0 * D.Bj 1) * D.Bj 2 := by
            rw [S.p_mul_M21, S.p_mul_M20, S.p_mul_M10]
        _ = 0 := by linear_combination hz1 + hz2 + hz3
    have hCc := congrArg (fun f : Fld[X] => f.comp (X ^ 2)) hC0
    have hBc := congrArg (fun f : Fld[X] => f.comp (X ^ 2)) hB0
    simp only [add_comp, mul_comp, pow_comp, zero_comp] at hCc hBc
    unfold KerD45Data.gj; dsimp [g2t]
    linear_combination hCc + X * hBc
  have hH1_fac : S.H1 = S.D1 ^ 4 * M0s.comp (X ^ 2) * g2t := by
    unfold KerD45Syzygy.H1
    have hp_c : S.p.comp (X ^ 2) = S.D1 ^ 2 * p1.comp (X ^ 2) := by
      rw [hp_fac, mul_comp, ← S.D1_sq]
    have hR_c : S.R ^ 2 = S.D1 ^ 2 * q1.comp (X ^ 2) := by
      rw [← S.q_comp_X_sq, hq_fac, mul_comp, ← S.D1_sq]
    have hR4_c : S.R ^ 4 = S.D1 ^ 4 * q1.comp (X ^ 2) ^ 2 := by
      calc S.R ^ 4 = (S.R ^ 2) ^ 2 := by ring
        _ = (S.D1 ^ 2 * q1.comp (X ^ 2)) ^ 2 := by rw [hR_c]
        _ = S.D1 ^ 4 * q1.comp (X ^ 2) ^ 2 := by ring
    have hpl' : S.D1 ^ 4 * p1.comp (X ^ 2) ^ 4 * D.gj 0 + q1.comp (X ^ 2) ^ 2 * D.gj 2 =
        M20s.comp (X ^ 2) * g2t := by
      have hpl := hplucker
      rw [← S.D1_sq] at hpl
      have hadd := congrArg (· + M20s.comp (X ^ 2) * g2t) hpl
      have hz := CharTwo.add_self_eq_zero (M20s.comp (X ^ 2) * g2t)
      linear_combination hadd - hz
    rw [hp_c, hR_c, hR4_c, hg1_fac]
    dsimp [M0s]; simp only [add_comp, mul_comp, pow_comp, ← S.D1_sq]
    calc (S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 4 * D.gj 0 +
          (S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 2 * (S.D1 ^ 2 * q1.comp (X ^ 2)) * (K1.comp (X ^ 2) * g2t) +
          S.D1 ^ 4 * q1.comp (X ^ 2) ^ 2 * D.gj 2
        = S.D1 ^ 4 * (S.D1 ^ 4 * p1.comp (X ^ 2) ^ 4 * D.gj 0 + q1.comp (X ^ 2) ^ 2 * D.gj 2) +
          S.D1 ^ 4 * (S.D1 ^ 2 * p1.comp (X ^ 2) ^ 2 * q1.comp (X ^ 2) * K1.comp (X ^ 2)) * g2t := by ring
      _ = S.D1 ^ 4 * (M20s.comp (X ^ 2) * g2t) +
          S.D1 ^ 4 * (S.D1 ^ 2 * p1.comp (X ^ 2) ^ 2 * q1.comp (X ^ 2) * K1.comp (X ^ 2)) * g2t := by rw [hpl']
      _ = S.D1 ^ 4 * (M20s.comp (X ^ 2) + S.D1 ^ 2 * p1.comp (X ^ 2) ^ 2 * q1.comp (X ^ 2) * K1.comp (X ^ 2)) * g2t := by ring
  have hg2t_ne : g2t ≠ 0 := by intro h0; apply S.H1_ne_zero; rw [hH1_fac, h0, mul_zero]
  have hg1_ne : D.gj 1 ≠ 0 := by
    rw [hg1_fac]; exact mul_ne_zero (mt (comp_X_sq_eq_zero_iff K1).mp hK1_ne) hg2t_ne
  have hResY_fac : D.ResY = S.D1 ^ 4 * Lam1.comp (X ^ 2) ^ 4 * M0s.comp (X ^ 2) ^ 5 * g2t := by
    rw [S.ResY_eq_H1_mul_Q2_sq, hH1_fac, hQ2_fac, pow_comp, mul_comp]; ring
  have hD1_dvd_g2t : S.D1 ∣ g2t := by
    have heq : S.c.comp (X ^ 2) * g2t =
        S.p.comp (X ^ 2) * P1s.comp (X ^ 2) + S.R * B1s.comp (X ^ 2) := by
      have hc := congrArg (fun f : Fld[X] => f.comp (X ^ 2)) hsyz1s
      simp only [add_comp, mul_comp, zero_comp] at hc
      have hadd := congrArg (· + S.c.comp (X ^ 2) * C1s.comp (X ^ 2)) hc
      have hz := CharTwo.add_self_eq_zero (S.c.comp (X ^ 2) * C1s.comp (X ^ 2))
      dsimp [g2t]; unfold KerD45Syzygy.R
      linear_combination -hadd + hz
    have hd : S.D1 ∣ S.c.comp (X ^ 2) * g2t := by
      rw [heq]; apply dvd_add
      · exact ⟨S.D1 * p1.comp (X ^ 2) * P1s.comp (X ^ 2), by rw [hp_fac, mul_comp, ← S.D1_sq]; ring⟩
      · exact dvd_mul_of_dvd_left S.D1_dvd_R _
    exact S.D1_coprime_c_comp_X_sq.dvd_of_dvd_mul_left hd
  have hwr_g2t_g2 : (g2t * D.gj 2).derivative = S.D1 ^ 6 * p1.comp (X ^ 2) ^ 5 * Lam1.comp (X ^ 2) := by
    have hg2t' : g2t.derivative = B1s.comp (X ^ 2) := by dsimp [g2t]; exact derivative_even_odd_char2 C1s B1s
    have hg2' : (D.gj 2).derivative = (D.Bj 2).comp (X ^ 2) := by
      unfold KerD45Data.gj; exact derivative_even_odd_char2 (D.Cj 2) (D.Bj 2)
    rw [derivative_mul, hg2t', hg2']
    have hz := CharTwo.add_self_eq_zero (X * B1s.comp (X ^ 2) * (D.Bj 2).comp (X ^ 2))
    have hc := congrArg (fun f : Fld[X] => f.comp (X ^ 2)) hr21_p
    simp only [add_comp, mul_comp, pow_comp] at hc
    rw [hp_fac, mul_comp, ← S.D1_sq] at hc
    calc B1s.comp (X ^ 2) * D.gj 2 + g2t * (D.Bj 2).comp (X ^ 2)
        = (D.Cj 2).comp (X ^ 2) * B1s.comp (X ^ 2) + C1s.comp (X ^ 2) * (D.Bj 2).comp (X ^ 2) := by
          unfold KerD45Data.gj; dsimp [g2t]; linear_combination hz
      _ = S.D1 ^ 2 * p1.comp (X ^ 2) * ((S.D1 ^ 2) ^ 2 * p1.comp (X ^ 2) ^ 4 * Lam1.comp (X ^ 2)) := hc
      _ = S.D1 ^ 6 * p1.comp (X ^ 2) ^ 5 * Lam1.comp (X ^ 2) := by ring
  have h4term_y0 : ∀ y0 : Fld,
      let Uy0 := S.p.comp (X ^ 2) * C y0 + S.R
      let U1_y0 := S.D1 * p1.comp (X ^ 2) * C y0 + R1
      M0s.comp (X ^ 2) * g2t +
        S.D1 ^ 4 * p1.comp (X ^ 2) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
        p1.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1 = D.gj 2 * U1_y0 ^ 4 := by
    intro y0 Uy0 U1_y0
    have hUfac : Uy0 = S.D1 * U1_y0 := by
      dsimp [Uy0, U1_y0]; rw [hp_fac, mul_comp, ← S.D1_sq, hR_fac]; ring
    have hH1_rew : S.H1 =
        S.p.comp (X ^ 2) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
        S.p.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1 + Uy0 ^ 4 * D.gj 2 := by
      have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
      have hR : S.R = Uy0 + S.p.comp (X ^ 2) * C y0 := by
        dsimp [Uy0]; rw [add_assoc, add_comm S.R, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      have hR2 : S.R ^ 2 = Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2) := by
        rw [hR]; calc (Uy0 + S.p.comp (X ^ 2) * C y0) ^ 2
            = Uy0 ^ 2 + 2 * Uy0 * (S.p.comp (X ^ 2) * C y0) + S.p.comp (X ^ 2) ^ 2 * C y0 ^ 2 := by ring
          _ = Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2) := by rw [h2, ← map_pow]; ring
      have hR4 : S.R ^ 4 = Uy0 ^ 4 + S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 4) := by
        calc S.R ^ 4 = (S.R ^ 2) ^ 2 := by ring
          _ = (Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2)) ^ 2 := by rw [hR2]
          _ = Uy0 ^ 4 + 2 * Uy0 ^ 2 * (S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2)) +
                S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 2) ^ 2 := by ring
          _ = Uy0 ^ 4 + S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 4) := by
                rw [h2, ← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]; ring
      unfold KerD45Syzygy.H1; rw [hR2, hR4]; ring
    have hEq := hH1_fac.symm.trans hH1_rew
    have hadd := congrArg (· + (S.p.comp (X ^ 2) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
        S.p.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1)) hEq
    have hz := CharTwo.add_self_eq_zero
      (S.p.comp (X ^ 2) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
       S.p.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1)
    have hp_c : S.p.comp (X ^ 2) = S.D1 ^ 2 * p1.comp (X ^ 2) := by
      rw [hp_fac, mul_comp, ← S.D1_sq]
    apply mul_left_cancel₀ (pow_ne_zero 4 S.D1_ne_zero)
    rw [hp_c, hUfac] at hadd hz
    rw [show ((S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      (S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 2 * (S.D1 * U1_y0) ^ 2 * D.gj 1 + (S.D1 * U1_y0) ^ 4 * D.gj 2) +
      ((S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      (S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 2 * (S.D1 * U1_y0) ^ 2 * D.gj 1) =
      (((S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      (S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 2 * (S.D1 * U1_y0) ^ 2 * D.gj 1) +
      ((S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      (S.D1 ^ 2 * p1.comp (X ^ 2)) ^ 2 * (S.D1 * U1_y0) ^ 2 * D.gj 1)) + (S.D1 * U1_y0) ^ 4 * D.gj 2 by ring,
      hz, zero_add] at hadd
    rw [hUfac]
    linear_combination hadd
  have hLam1_d2_id : ∀ y0 : Fld,
      S.c * (q1 + C (y0 ^ 2) * S.D2 * p1 ^ 2) ^ 2 * Lam1 =
        D.A0sh y0 0 * B1s + (P1s + C y0 * B1s) * D.Bsh y0 0 := by
    intro y0
    have hM10sh : S.M10sh y0 = (q1 + C (y0 ^ 2) * S.D2 * p1 ^ 2) ^ 2 * K1 * Lam1 := by
      unfold KerD45Syzygy.M10sh; rw [hM10_fac, hM21_fac]
      have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
      have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
      calc q1 ^ 2 * K1 * Lam1 + C (y0 ^ 4) * (S.D2 ^ 2 * p1 ^ 4 * K1 * Lam1)
          = (q1 ^ 2 + 2 * q1 * (C (y0 ^ 2) * S.D2 * p1 ^ 2) + C (y0 ^ 2) ^ 2 * S.D2 ^ 2 * p1 ^ 4) * K1 * Lam1 := by
            rw [h2, hsq]; ring
        _ = (q1 + C (y0 ^ 2) * S.D2 * p1 ^ 2) ^ 2 * K1 * Lam1 := by ring
    have hc10 := (S.shifted_minor_identities 0 y0).2.2.2.1
    rw [hM10sh] at hc10
    have hA0_1 : D.A0sh y0 1 = K1 * (P1s + C y0 * B1s) := by
      simp only [KerD45Data.A0sh, KerD45Data.Bsh, Fin.val_one]; rw [hP1s, hB1s]; ring
    have hB_1 : D.Bsh y0 1 = K1 * B1s := by
      simp only [KerD45Data.Bsh, Fin.val_one]; exact hB1s
    rw [hA0_1, hB_1] at hc10
    apply mul_left_cancel₀ hK1_ne
    linear_combination hc10
  exact {
    p1, q1, K1, Lam1, P1s, C1s, B1s, M20s, M0s, g2t, R1,
    hp_fac, hq_fac, hp1_ne, hp1_q1_cop, hD2_q1_cop,
    hK1_ne, hLam1_ne, hP1s, hC1s, hB1s, hstar_cop,
    hM21_fac, hM10_fac, hM20_fac, hM0s_def := rfl, hM0s_ne,
    hg2t_def := rfl, hg1_fac, hQ2_fac, hR_fac, hR1_sq,
    hr21_p, hplucker, hH1_fac, hg2t_ne, hg1_ne, hResY_fac,
    hD1_dvd_g2t, hwr_g2t_g2, h4term_y0, hLam1_d2_id
  }

namespace KerD45KData

variable {D : KerD45Data} {S : KerD45Syzygy D} (K : KerD45KData S)

/-! #### Local orders, domain subset partition, and all `ubCore` / `eqCore` bounds -/

omit K in
lemma isD1_iff (_K : KerD45KData S) (i : Idx) :
    S.D1.eval (BinaryIRSProfile.domain i) = 0 ↔ S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 := by
  have h := congrArg (Polynomial.eval (BinaryIRSProfile.domain i)) S.D1_sq
  rw [eval_pow, eval_comp, eval_pow, eval_X] at h
  exact ⟨fun h0 => by rw [← h, h0]; simp, fun h0 => sq_eq_zero_iff.mp (h.trans h0)⟩

omit K in
lemma isU0_of_D1_zero (K : KerD45KData S) {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) : S.isU0 i :=
  ((S.D2_eval_eq_zero_iff i).mp ((K.isD1_iff i).mp hD1)).2

lemma g2t_zero_of_D1_zero {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    K.g2t.eval (BinaryIRSProfile.domain i) = 0 := by
  rcases K.hD1_dvd_g2t with ⟨w, hw⟩; rw [hw, eval_mul, hD1, zero_mul]

lemma p1_ne_zero_of_isU0_D1_ne {i : Idx} (hU : S.isU0 i) (hD1 : S.D1.eval (BinaryIRSProfile.domain i) ≠ 0) :
    K.p1.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
  intro hp10
  have hp0 : S.p.eval (BinaryIRSProfile.domain i ^ 2) = 0 := by
    rw [K.hp_fac, eval_mul, hp10, mul_zero]
  exact hD1 ((K.isD1_iff i).mpr ((S.D2_eval_eq_zero_iff i).mpr ⟨hp0, hU⟩))

lemma q1_ne_zero_of_D1_zero {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    K.q1.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
  intro hq10
  have hD20 : S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 := (K.isD1_iff i).mp hD1
  have hu := K.hD2_q1_cop.isUnit_of_dvd' (dvd_iff_isRoot.mpr hD20) (dvd_iff_isRoot.mpr hq10)
  have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega

lemma R1_ne_zero_of_D1_zero {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    K.R1.eval (BinaryIRSProfile.domain i) ≠ 0 := by
  intro hR10
  apply K.q1_ne_zero_of_D1_zero hD1
  have h := congrArg (Polynomial.eval (BinaryIRSProfile.domain i)) K.hR1_sq
  rw [eval_pow, eval_comp, eval_pow, eval_X, hR10, zero_pow (by norm_num)] at h
  exact h.symm

lemma q1_sh_ne_zero_of_D1_zero {i : Idx} (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    (K.q1 + C (D.y i ^ 2) * S.D2 * K.p1 ^ 2).eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
  have hD20 : S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 := (K.isD1_iff i).mp hD1
  simp only [eval_add, eval_mul, eval_C, eval_pow, hD20, mul_zero, zero_mul, add_zero]
  exact K.q1_ne_zero_of_D1_zero hD1

lemma q1_sh_ne_zero_of_not_U0 {i : Idx} (hU : ¬ S.isU0 i) :
    (K.q1 + C (D.y i ^ 2) * S.D2 * K.p1 ^ 2).eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
  intro h0
  set x0 := BinaryIRSProfile.domain i; set t0 := x0 ^ 2; set y0 := D.y i
  have hqsh : (S.q + C (y0 ^ 2) * S.p ^ 2).eval t0 = 0 := by
    have hfac : S.q + C (y0 ^ 2) * S.p ^ 2 = S.D2 * (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) := by
      rw [K.hp_fac, K.hq_fac]; ring
    rw [hfac, eval_mul, h0, mul_zero]
  have hqval : S.q.eval t0 = S.R.eval x0 ^ 2 := by
    have h := congrArg (Polynomial.eval x0) S.q_comp_X_sq
    simpa [eval_comp, eval_pow, eval_X] using h
  have h2 : (2 : Fld) = 0 := CharTwo.two_eq_zero
  have hU2 : S.U_eval i ^ 2 = 0 := by
    unfold KerD45Syzygy.U_eval
    simp only [eval_add, eval_mul, eval_C, eval_pow, hqval] at hqsh
    calc (S.p.eval t0 * y0 + S.R.eval x0) ^ 2
        = S.R.eval x0 ^ 2 + 2 * (S.p.eval t0 * y0) * S.R.eval x0 + y0 ^ 2 * S.p.eval t0 ^ 2 := by ring
      _ = S.R.eval x0 ^ 2 + y0 ^ 2 * S.p.eval t0 ^ 2 := by rw [h2]; ring
      _ = 0 := hqsh
  exact hU (sq_eq_zero_iff.mp hU2)

lemma pow_dvd_K1_all (i : Idx) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - 2) ∣ K.K1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hne : (K.P1s + C y0 * K.B1s).eval t0 ≠ 0 ∨ (K.C1s + C x0 * K.B1s).eval t0 ≠ 0 ∨ K.B1s.eval t0 ≠ 0 := by
    by_contra hall; push Not at hall
    have hdB : X - C t0 ∣ K.B1s := dvd_iff_isRoot.mpr hall.2.2
    have hdP : X - C t0 ∣ K.P1s := by
      have h1 : X - C t0 ∣ K.P1s + C y0 * K.B1s := dvd_iff_isRoot.mpr hall.1
      have hrew : K.P1s = (K.P1s + C y0 * K.B1s) + C y0 * K.B1s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hrew]; exact dvd_add h1 (dvd_mul_of_dvd_right hdB _)
    have hdC : X - C t0 ∣ K.C1s := by
      have h1 : X - C t0 ∣ K.C1s + C x0 * K.B1s := dvd_iff_isRoot.mpr hall.2.1
      have hrew : K.C1s = (K.C1s + C x0 * K.B1s) + C x0 * K.B1s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hrew]; exact dvd_add h1 (dvd_mul_of_dvd_right hdB _)
    have hu := K.hstar_cop (X - C t0) hdP hdC hdB
    have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
  have hloc := D.local_shifted_ords i 1
  have hA0 : D.A0sh y0 1 = K.K1 * (K.P1s + C y0 * K.B1s) := by
    simp only [KerD45Data.A0sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hP1s, K.hB1s]; ring
  have hA1 : D.A1sh x0 y0 1 = K.K1 * (K.C1s + C x0 * K.B1s) := by
    simp only [KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hC1s, K.hB1s]; ring
  have hB : D.Bsh y0 1 = K.K1 * K.B1s := by simp only [KerD45Data.Bsh, Fin.val_one]; exact K.hB1s
  rcases hne with h | h | h
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 2)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hA0]; exact (pow_dvd_pow _ (by omega)).trans hloc.1)
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 2)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hA1]; exact (pow_dvd_pow _ (by omega)).trans hloc.2.1)
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 2)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hB]; exact (pow_dvd_pow _ (by omega : D.k i - 2 ≤ D.k i - 1 - 1)).trans hloc.2.2)

lemma pow_dvd_K1_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - 1) ∣ K.K1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hne : (K.P1s + C y0 * K.B1s).eval t0 ≠ 0 ∨ (K.C1s + C x0 * K.B1s).eval t0 ≠ 0 ∨ K.B1s.eval t0 ≠ 0 := by
    by_contra hall; push Not at hall
    have hdB : X - C t0 ∣ K.B1s := dvd_iff_isRoot.mpr hall.2.2
    have hdP : X - C t0 ∣ K.P1s := by
      have h1 : X - C t0 ∣ K.P1s + C y0 * K.B1s := dvd_iff_isRoot.mpr hall.1
      have hrew : K.P1s = (K.P1s + C y0 * K.B1s) + C y0 * K.B1s := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hrew]; exact dvd_add h1 (dvd_mul_of_dvd_right hdB _)
    have hdC : X - C t0 ∣ K.C1s := by
      have h1 : X - C t0 ∣ K.C1s + C x0 * K.B1s := dvd_iff_isRoot.mpr hall.2.1
      have hrew : K.C1s = (K.C1s + C x0 * K.B1s) + C x0 * K.B1s := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hrew]; exact dvd_add h1 (dvd_mul_of_dvd_right hdB _)
    have hu := K.hstar_cop (X - C t0) hdP hdC hdB
    have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
  have hloc := D.local_shifted_ords i 1
  have hB1 := S.pow_dvd_Bsh_U1 i hU 1
  have hA0 : D.A0sh y0 1 = K.K1 * (K.P1s + C y0 * K.B1s) := by
    simp only [KerD45Data.A0sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hP1s, K.hB1s]; ring
  have hA1 : D.A1sh x0 y0 1 = K.K1 * (K.C1s + C x0 * K.B1s) := by
    simp only [KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hC1s, K.hB1s]; ring
  have hB : D.Bsh y0 1 = K.K1 * K.B1s := by simp only [KerD45Data.Bsh, Fin.val_one]; exact K.hB1s
  rcases hne with h | h | h
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 1)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hA0]; exact hloc.1)
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 1)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hA1]; exact hloc.2.1)
  · have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left (m := D.k i - 1)
    exact hcop.dvd_of_dvd_mul_right (by rw [← hB]; exact hB1)

lemma pow_dvd_K1_mbad (i : Idx) (hmb : K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - 1) ∣ K.K1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hne : (K.C1s + C x0 * K.B1s).eval t0 ≠ 0 := by
    have hev : (K.C1s + C x0 * K.B1s).eval t0 = K.g2t.eval x0 := by
      rw [K.hg2t_def]; simp [t0]
    rwa [hev]
  have hA1 : D.A1sh x0 y0 1 = K.K1 * (K.C1s + C x0 * K.B1s) := by
    simp only [KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one]; rw [K.hC1s, K.hB1s]; ring
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)).pow_left (m := D.k i - 1)
  exact hcop.dvd_of_dvd_mul_right (by rw [← hA1]; exact (D.local_shifted_ords i 1).2.1)

lemma pow_dvd_Lam1_d2 (i : Idx) (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - 1) ∣ K.Lam1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hD20 : S.D2.eval t0 = 0 := (K.isD1_iff i).mp hD1
  have hc_ne : S.c.eval t0 ≠ 0 := by
    intro hc0
    have hu := S.D2_coprime_c.isUnit_of_dvd' (dvd_iff_isRoot.mpr hD20) (dvd_iff_isRoot.mpr hc0)
    have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
  have hq_ne := K.q1_sh_ne_zero_of_D1_zero hD1
  have hfac_ne : (S.c * (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2).eval t0 ≠ 0 := by
    rw [eval_mul, eval_pow]; exact mul_ne_zero hc_ne (pow_ne_zero 2 hq_ne)
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hfac_ne)).pow_left (m := D.k i - 1)
  apply hcop.dvd_of_dvd_mul_left
  rw [K.hLam1_d2_id y0]
  have h0 := D.local_shifted_ords i 0
  exact dvd_add (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega)).trans h0.1) K.B1s)
    (dvd_mul_of_dvd_right (by rw [Fin.val_zero, Nat.sub_zero] at h0; exact h0.2.2) _)

lemma pow_dvd_M0s_mbad (i : Idx) (hU : S.isU0 i) (hmb : K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ D.k i ∣ K.M0s := by
  set x0 := BinaryIRSProfile.domain i; set t0 := x0 ^ 2
  have hD1_ne : S.D1.eval x0 ≠ 0 := fun h0 => hmb (K.g2t_zero_of_D1_zero h0)
  have hH1d := S.pow_dvd_H1_of_isU0 i hU
  rw [K.hH1_fac] at hH1d
  have hcop : IsCoprime ((X - C x0) ^ (2 * D.k i - 1)) (S.D1 ^ 4 * K.g2t) := by
    apply IsCoprime.pow_left
    have hne : (S.D1 ^ 4 * K.g2t).eval x0 ≠ 0 := by
      rw [eval_mul, eval_pow]; exact mul_ne_zero (pow_ne_zero 4 hD1_ne) hmb
    exact (Polynomial.irreducible_X_sub_C x0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
  have hMd : (X - C x0) ^ (2 * D.k i - 1) ∣ K.M0s.comp (X ^ 2) :=
    hcop.dvd_of_dvd_mul_left (by rw [show S.D1 ^ 4 * K.g2t * K.M0s.comp (X ^ 2) = S.D1 ^ 4 * K.M0s.comp (X ^ 2) * K.g2t by ring]; exact hH1d)
  have hrm := (le_rootMultiplicity_iff (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne)).mpr hMd
  have hrm2 : (K.M0s.comp (X ^ 2)).rootMultiplicity x0 = 2 * K.M0s.rootMultiplicity t0 := by
    rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne, ← map_pow, rootMultiplicity_map_eq]
  have hle : D.k i ≤ K.M0s.rootMultiplicity t0 := by omega
  exact (pow_dvd_pow _ hle).trans (pow_rootMultiplicity_dvd K.M0s t0)

lemma pow_dvd_Lam1_mul_M0s (i : Idx) [Decidable (S.isU0 i)] :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^
      (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)
       else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2)) ∣ K.Lam1 * K.M0s := by
  set t0 := BinaryIRSProfile.domain i ^ 2
  have hne : K.Lam1 * K.M0s ≠ 0 := mul_ne_zero K.hLam1_ne K.hM0s_ne
  have hrm_Q2 : S.Q2.rootMultiplicity t0 = 2 * (K.Lam1 * K.M0s).rootMultiplicity t0 := by
    rw [K.hQ2_fac, rootMultiplicity_pow_eq' _ hne 2 t0]
  split_ifs with hU hk1 hk0 hk1'
  · simp
  · have hd := S.pow_dvd_Q2_U0 i; simp only [hk1, ↓reduceIte] at hd
    have hle := (le_rootMultiplicity_iff S.Q2_ne_zero).mpr hd
    rw [hrm_Q2] at hle
    exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd _ t0)
  · simp
  · have hd := S.pow_dvd_Q2_U1 i hU; simp only [hk1', Nat.one_ne_zero, ↓reduceIte] at hd
    have hle := (le_rootMultiplicity_iff S.Q2_ne_zero).mpr hd
    rw [hrm_Q2] at hle
    exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd _ t0)
  · have hd := S.pow_dvd_Q2_U1 i hU; simp only [hk0, hk1', ↓reduceIte] at hd
    have hle := (le_rootMultiplicity_iff S.Q2_ne_zero).mpr hd
    rw [hrm_Q2] at hle
    exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd _ t0)

lemma pow_dvd_g2_din (i : Idx) (hk2 : 2 ≤ D.k i) (hU : S.isU0 i)
    (hg2t : K.g2t.eval (BinaryIRSProfile.domain i) = 0)
    (hM0s : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0)
    (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    (X - C (BinaryIRSProfile.domain i)) ^ 3 ∣ D.gj 2 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  set Uy0 := S.p.comp (X ^ 2) * C y0 + S.R
  set U1_y0 := S.D1 * K.p1.comp (X ^ 2) * C y0 + K.R1
  have hU1_ne : U1_y0.eval x0 ≠ 0 := by
    simp only [U1_y0, eval_add, eval_mul, hD1, zero_mul, zero_add]
    exact K.R1_ne_zero_of_D1_zero hD1
  have hU1_pow_ne : (U1_y0 ^ 4).eval x0 ≠ 0 := by rw [eval_pow]; exact pow_ne_zero 4 hU1_ne
  have hcop := ((Polynomial.irreducible_X_sub_C x0).coprime_iff_not_dvd.mpr
    (mt dvd_iff_isRoot.mp hU1_pow_ne)).pow_left (m := 3)
  apply hcop.dvd_of_dvd_mul_right
  rw [← K.h4term_y0 y0]
  have hd_M0s : (X - C x0) ^ 2 ∣ K.M0s.comp (X ^ 2) :=
    (pow_dvd_comp_X_sq_iff K.M0s x0 1).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hM0s)
  have hd_g2t : X - C x0 ∣ K.g2t := dvd_iff_isRoot.mpr hg2t
  have hd_t1 : (X - C x0) ^ 3 ∣ K.M0s.comp (X ^ 2) * K.g2t := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one]; exact mul_dvd_mul hd_M0s hd_g2t
  have hd_D1 : X - C x0 ∣ S.D1 := dvd_iff_isRoot.mpr hD1
  have hd_t2 : (X - C x0) ^ 3 ∣ S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 4 *
      (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hd_D1 4)) _) _
  have hd_Uy0 : X - C x0 ∣ Uy0 := by
    rw [dvd_iff_isRoot, IsRoot]; simp only [Uy0, eval_add, eval_mul, eval_comp, eval_pow, eval_X, eval_C]; exact hU
  have hd_t3 : (X - C x0) ^ 3 ∣ K.p1.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1 := by
    rw [K.hg1_fac]
    have : (X - C x0) ^ 3 ∣ Uy0 ^ 2 * K.g2t := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hd_Uy0 2) hd_g2t
    exact (this).trans ⟨K.p1.comp (X ^ 2) ^ 2 * K.K1.comp (X ^ 2), by ring⟩
  exact dvd_add (dvd_add hd_t1 hd_t2) hd_t3

omit K in
lemma pow_dvd_g2_U1 (_K : KerD45KData S) (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * (D.k i - 2)) ∣ D.gj 2 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i; set t0 := x0 ^ 2
  have hrew : D.gj 2 = (D.A1sh x0 y0 2).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 2).comp (X ^ 2) := by
    simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_two, add_comp, mul_comp, C_comp,
      sub_eq_add_neg, CharTwo.neg_eq]
    have hz := CharTwo.add_self_eq_zero (C x0 * (D.Bj 2).comp (X ^ 2))
    linear_combination -hz
  rw [hrew]
  apply dvd_add
  · exact (pow_dvd_comp_X_sq_iff _ x0 _).mpr (D.local_shifted_ords i 2).2.1
  · exact dvd_mul_of_dvd_right ((pow_dvd_comp_X_sq_iff _ x0 _).mpr (S.pow_dvd_Bsh_U1 i hU 2)) _

omit K in
lemma pow_dvd_g1_U1 (_K : KerD45KData S) (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * (D.k i - 1)) ∣ D.gj 1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i
  have hrew : D.gj 1 = (D.A1sh x0 y0 1).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 1).comp (X ^ 2) := by
    simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one, add_comp, mul_comp, C_comp,
      sub_eq_add_neg, CharTwo.neg_eq]
    have hz := CharTwo.add_self_eq_zero (C x0 * (D.Bj 1).comp (X ^ 2))
    linear_combination -hz
  rw [hrew]
  apply dvd_add
  · exact (pow_dvd_comp_X_sq_iff _ x0 _).mpr (D.local_shifted_ords i 1).2.1
  · exact dvd_mul_of_dvd_right ((pow_dvd_comp_X_sq_iff _ x0 _).mpr (S.pow_dvd_Bsh_U1 i hU 1)) _

omit K in
lemma pow_dvd_g1_U0 (_K : KerD45KData S) (i : Idx) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 3) ∣ D.gj 1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i
  have hrew : D.gj 1 = (D.A1sh x0 y0 1).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 1).comp (X ^ 2) := by
    simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one, add_comp, mul_comp, C_comp,
      sub_eq_add_neg, CharTwo.neg_eq]
    have hz := CharTwo.add_self_eq_zero (C x0 * (D.Bj 1).comp (X ^ 2))
    linear_combination -hz
  rw [hrew]; have hloc := D.local_shifted_ords i 1
  apply dvd_add
  · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 3 ≤ 2 * (D.k i - 1))).trans ((pow_dvd_comp_X_sq_iff _ x0 _).mpr hloc.2.1)
  · by_cases hk : 2 * D.k i - 3 = 0
    · rw [hk, pow_zero]; exact one_dvd _
    · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 3 ≤ 1 + 2 * (D.k i - 2))).trans
        (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ x0 _).mpr
          ((pow_dvd_pow _ (by omega : D.k i - 2 ≤ D.k i - 1 - 1)).trans hloc.2.2)))

omit K in
lemma pow_dvd_gsh0 (_K : KerD45KData S) (i : Idx) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 1) ∣
      D.gj 0 + C (D.y i ^ 2) * D.gj 1 + C (D.y i ^ 4) * D.gj 2 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i
  have hrew : D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2 =
      (D.A1sh x0 y0 0).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 0).comp (X ^ 2) := by
    simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_zero, add_comp, mul_comp, C_comp,
      sub_eq_add_neg, CharTwo.neg_eq]
    have hz := CharTwo.add_self_eq_zero (C x0 * ((D.Bj 0).comp (X ^ 2) +
      C (y0 ^ 2) * (D.Bj 1).comp (X ^ 2) + C (y0 ^ 4) * (D.Bj 2).comp (X ^ 2)))
    linear_combination -hz
  rw [hrew]; have hloc := D.local_shifted_ords i 0
  apply dvd_add
  · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 2 * D.k i)).trans ((pow_dvd_comp_X_sq_iff _ x0 _).mpr (by rw [Fin.val_zero, Nat.sub_zero] at hloc; exact hloc.2.1))
  · by_cases hk : D.k i = 0
    · simp [hk]
    · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 1 + 2 * (D.k i - 1))).trans
        (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ x0 _).mpr (by rw [Fin.val_zero, Nat.sub_zero] at hloc; exact hloc.2.2)))

omit K in
lemma pow_dvd_H1_U1 (K : KerD45KData S) (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * (D.k i - 2)) ∣ S.H1 := by
  set x0 := BinaryIRSProfile.domain i; set y0 := D.y i
  set Uy0 := S.p.comp (X ^ 2) * C y0 + S.R
  have hH1_rew : S.H1 =
      S.p.comp (X ^ 2) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      S.p.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1 + Uy0 ^ 4 * D.gj 2 := by
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    have hR : S.R = Uy0 + S.p.comp (X ^ 2) * C y0 := by
      dsimp [Uy0]; rw [add_assoc, add_comm S.R, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hR2 : S.R ^ 2 = Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2) := by
      rw [hR]; calc (Uy0 + S.p.comp (X ^ 2) * C y0) ^ 2
          = Uy0 ^ 2 + 2 * Uy0 * (S.p.comp (X ^ 2) * C y0) + S.p.comp (X ^ 2) ^ 2 * C y0 ^ 2 := by ring
        _ = Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2) := by rw [h2, ← map_pow]; ring
    have hR4 : S.R ^ 4 = Uy0 ^ 4 + S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 4) := by
      calc S.R ^ 4 = (S.R ^ 2) ^ 2 := by ring
        _ = (Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2)) ^ 2 := by rw [hR2]
        _ = Uy0 ^ 4 + 2 * Uy0 ^ 2 * (S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2)) +
              S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 2) ^ 2 := by ring
        _ = Uy0 ^ 4 + S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 4) := by
              rw [h2, ← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]; ring
    unfold KerD45Syzygy.H1; rw [hR2, hR4]; ring
  rw [hH1_rew]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 * (D.k i - 2) ≤ 2 * D.k i - 1)).trans (K.pow_dvd_gsh0 i)) _)
    (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 * (D.k i - 2) ≤ 2 * (D.k i - 1))).trans (K.pow_dvd_g1_U1 i hU)) _))
    (dvd_mul_of_dvd_right (K.pow_dvd_g2_U1 i hU) _)

lemma pow_dvd_K_M10sh_d2 (i : Idx) (hD1 : S.D1.eval (BinaryIRSProfile.domain i) = 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) ∣ K.K1 * K.Lam1 := by
  set t0 := BinaryIRSProfile.domain i ^ 2; set y0 := D.y i
  have hM10sh : S.M10sh y0 = (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2 * (K.K1 * K.Lam1) := by
    unfold KerD45Syzygy.M10sh; rw [K.hM10_fac, K.hM21_fac]
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
    calc K.q1 ^ 2 * K.K1 * K.Lam1 + C (y0 ^ 4) * (S.D2 ^ 2 * K.p1 ^ 4 * K.K1 * K.Lam1)
        = (K.q1 ^ 2 + 2 * K.q1 * (C (y0 ^ 2) * S.D2 * K.p1 ^ 2) + C (y0 ^ 2) ^ 2 * S.D2 ^ 2 * K.p1 ^ 4) * (K.K1 * K.Lam1) := by
          rw [h2, hsq]; ring
      _ = (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2 * (K.K1 * K.Lam1) := by ring
  have hq2_ne : ((K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2).eval t0 ≠ 0 := by
    rw [eval_pow]; exact pow_ne_zero 2 (K.q1_sh_ne_zero_of_D1_zero hD1)
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr
    (mt dvd_iff_isRoot.mp hq2_ne)).pow_left
      (m := if D.k i ≤ 1 then 0 else 2 * D.k i - 2)
  exact hcop.dvd_of_dvd_mul_left (by rw [← hM10sh]; exact (S.local_shifted_minor_ords i).1.2.2)

lemma pow_dvd_K_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i = 0 then 0 else 2 * D.k i - 1) ∣ K.K1 * K.Lam1 := by
  set t0 := BinaryIRSProfile.domain i ^ 2; set y0 := D.y i
  have hM10sh : S.M10sh y0 = (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2 * (K.K1 * K.Lam1) := by
    unfold KerD45Syzygy.M10sh; rw [K.hM10_fac, K.hM21_fac]
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
    calc K.q1 ^ 2 * K.K1 * K.Lam1 + C (y0 ^ 4) * (S.D2 ^ 2 * K.p1 ^ 4 * K.K1 * K.Lam1)
        = (K.q1 ^ 2 + 2 * K.q1 * (C (y0 ^ 2) * S.D2 * K.p1 ^ 2) + C (y0 ^ 2) ^ 2 * S.D2 ^ 2 * K.p1 ^ 4) * (K.K1 * K.Lam1) := by
          rw [h2, hsq]; ring
      _ = (K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2 * (K.K1 * K.Lam1) := by ring
  have hq2_ne : ((K.q1 + C (y0 ^ 2) * S.D2 * K.p1 ^ 2) ^ 2).eval t0 ≠ 0 := by
    rw [eval_pow]; exact pow_ne_zero 2 (K.q1_sh_ne_zero_of_not_U0 hU)
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr
    (mt dvd_iff_isRoot.mp hq2_ne)).pow_left
      (m := if D.k i = 0 then 0 else 2 * D.k i - 1)
  exact hcop.dvd_of_dvd_mul_left (by rw [← hM10sh]; exact ((S.local_shifted_minor_ords i).2 hU).2.2)

lemma pow_dvd_K_U0_D1_ne (i : Idx) (hU : S.isU0 i) (hD1 : S.D1.eval (BinaryIRSProfile.domain i) ≠ 0) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (2 * D.k i - 4) ∣ K.K1 * K.Lam1 := by
  set t0 := BinaryIRSProfile.domain i ^ 2
  have hD2_ne : S.D2.eval t0 ≠ 0 := mt (K.isD1_iff i).mpr hD1
  have hp1_ne := K.p1_ne_zero_of_isU0_D1_ne hU hD1
  have hne : (S.D2 ^ 2 * K.p1 ^ 4).eval t0 ≠ 0 := by
    rw [eval_mul, eval_pow, eval_pow]; exact mul_ne_zero (pow_ne_zero 2 hD2_ne) (pow_ne_zero 4 hp1_ne)
  have hcop := ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)).pow_left
    (m := 2 * D.k i - 4)
  exact hcop.dvd_of_dvd_mul_left (by rw [show S.D2 ^ 2 * K.p1 ^ 4 * (K.K1 * K.Lam1) = S.M21 by rw [K.hM21_fac]; ring]; exact (S.local_shifted_minor_ords i).1.1)

/-! #### Domain subsets and exact counts (`col 0..47`) -/

noncomputable def isMbad (i : Idx) : Prop :=
  2 ≤ D.k i ∧ S.isU0 i ∧ K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0

noncomputable def isML (i : Idx) : Prop :=
  2 ≤ D.k i ∧ S.isU0 i ∧ K.g2t.eval (BinaryIRSProfile.domain i) = 0 ∧
    K.M0s.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0

noncomputable def isNorm (i : Idx) : Prop :=
  2 ≤ D.k i ∧ S.isU0 i ∧ K.g2t.eval (BinaryIRSProfile.domain i) = 0 ∧
    K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0

omit K in
noncomputable def isD1 (_K : KerD45KData S) (i : Idx) : Prop := S.D1.eval (BinaryIRSProfile.domain i) = 0

noncomputable def mbadCnt : ℕ := by classical exact (Finset.univ.filter K.isMbad).card
noncomputable def mLCnt : ℕ := by classical exact (Finset.univ.filter K.isML).card
noncomputable def din2Cnt : ℕ := by classical exact (Finset.univ.filter fun i => D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i).card
noncomputable def din3Cnt : ℕ := by classical exact (Finset.univ.filter fun i => 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i).card
noncomputable def dinCnt : ℕ := K.din2Cnt + K.din3Cnt
noncomputable def dmL2Cnt : ℕ := by classical exact (Finset.univ.filter fun i => D.k i = 2 ∧ K.isML i ∧ K.isD1 i).card
noncomputable def dmL3Cnt : ℕ := by classical exact (Finset.univ.filter fun i => 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i).card
noncomputable def dmLCnt : ℕ := K.dmL2Cnt + K.dmL3Cnt
noncomputable def d2k1UCnt : ℕ := by classical exact (Finset.univ.filter fun i => D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i).card
noncomputable def d2k0Cnt : ℕ := by classical exact (Finset.univ.filter fun i => D.k i = 0 ∧ K.isD1 i).card
noncomputable def mu1Cnt : ℕ := by
  classical exact (Finset.univ.filter fun i => D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧
    K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0).card
noncomputable def ntUNorm : ℕ := by classical exact ∑ i : Idx, if K.isNorm i then D.k i - 3 else 0
noncomputable def ntUMbad : ℕ := by classical exact ∑ i : Idx, if K.isMbad i then D.k i - 3 else 0
noncomputable def ntUML : ℕ := by classical exact ∑ i : Idx, if K.isML i then D.k i - 3 else 0
noncomputable def muExK3 : ℕ := by
  classical exact ∑ i : Idx,
    if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
    else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2
    else 0

private lemma card_filter_univ_Z {P : Idx → Prop} (inst1 inst2 : DecidablePred P) :
    ((@Finset.filter Idx P inst1 Finset.univ).card : ℤ) =
      ∑ i : Idx, @ite ℤ (P i) (inst2 i) 1 0 := by
  have hgen : ∀ S0 : Finset Idx,
      ((@Finset.filter Idx P inst1 S0).card : ℤ) = ∑ i ∈ S0, @ite ℤ (P i) (inst2 i) 1 0 := by
    intro S0
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1; apply congrArg Finset.card; ext i
    simp only [Finset.mem_filter]
  exact hgen Finset.univ

private lemma sum_ite_nat_Z {P : Idx → Prop} (g : Idx → ℕ) (inst1 inst2 : DecidablePred P) :
    ((∑ i : Idx, @ite ℕ (P i) (inst1 i) (g i) 0 : ℕ) : ℤ) =
      ∑ i : Idx, @ite ℤ (P i) (inst2 i) ((g i : ℕ) : ℤ) 0 := by
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl; intro i _
  by_cases h : P i <;> simp [h]

lemma n0_Z [DecidablePred fun i : Idx => D.k i = 0] :
    (D.n0 : ℤ) = ∑ i : Idx, (if D.k i = 0 then (1 : ℤ) else 0) := by
  unfold KerD45Data.n0; exact card_filter_univ_Z _ _
lemma n1_Z [DecidablePred fun i : Idx => D.k i = 1] :
    (D.n1 : ℤ) = ∑ i : Idx, (if D.k i = 1 then (1 : ℤ) else 0) := by
  unfold KerD45Data.n1; exact card_filter_univ_Z _ _
lemma n2_Z [DecidablePred fun i : Idx => D.k i = 2] :
    (D.n2 : ℤ) = ∑ i : Idx, (if D.k i = 2 then (1 : ℤ) else 0) := by
  unfold KerD45Data.n2; exact card_filter_univ_Z _ _
lemma n3_Z [DecidablePred fun i : Idx => 3 ≤ D.k i] :
    (D.n3 : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i then (1 : ℤ) else 0) := by
  unfold KerD45Data.n3; exact card_filter_univ_Z _ _
lemma nt_Z : (D.nt : ℤ) = ∑ i : Idx, ((D.k i - 3 : ℕ) : ℤ) := by
  unfold KerD45Data.nt; rw [Nat.cast_sum]
lemma n1U_Z [DecidablePred fun i : Idx => D.k i = 1 ∧ S.isU0 i] :
    (S.n1U : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i then (1 : ℤ) else 0) := by
  unfold KerD45Syzygy.n1U; exact card_filter_univ_Z _ _
lemma n2U_Z [DecidablePred fun i : Idx => D.k i = 2 ∧ S.isU0 i] :
    (S.n2U : ℤ) = ∑ i : Idx, (if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) := by
  unfold KerD45Syzygy.n2U; exact card_filter_univ_Z _ _
lemma n3U_Z [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ S.isU0 i] :
    (S.n3U : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ S.isU0 i then (1 : ℤ) else 0) := by
  unfold KerD45Syzygy.n3U; exact card_filter_univ_Z _ _
lemma mbadCnt_Z [DecidablePred K.isMbad] :
    (K.mbadCnt : ℤ) = ∑ i : Idx, (if K.isMbad i then (1 : ℤ) else 0) := by
  unfold mbadCnt; exact card_filter_univ_Z _ _
lemma mLCnt_Z [DecidablePred K.isML] :
    (K.mLCnt : ℤ) = ∑ i : Idx, (if K.isML i then (1 : ℤ) else 0) := by
  unfold mLCnt; exact card_filter_univ_Z _ _
lemma din2Cnt_Z [DecidablePred fun i : Idx => D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i] :
    (K.din2Cnt : ℤ) = ∑ i : Idx, (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold din2Cnt; exact card_filter_univ_Z _ _
lemma din3Cnt_Z [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i] :
    (K.din3Cnt : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold din3Cnt; exact card_filter_univ_Z _ _
lemma dmL2Cnt_Z [DecidablePred fun i : Idx => D.k i = 2 ∧ K.isML i ∧ K.isD1 i] :
    (K.dmL2Cnt : ℤ) = ∑ i : Idx, (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold dmL2Cnt; exact card_filter_univ_Z _ _
lemma dmL3Cnt_Z [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i] :
    (K.dmL3Cnt : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold dmL3Cnt; exact card_filter_univ_Z _ _
lemma d2k1UCnt_Z [DecidablePred fun i : Idx => D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i] :
    (K.d2k1UCnt : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold d2k1UCnt; exact card_filter_univ_Z _ _
lemma d2k0Cnt_Z [DecidablePred fun i : Idx => D.k i = 0 ∧ K.isD1 i] :
    (K.d2k0Cnt : ℤ) = ∑ i : Idx, (if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) := by
  unfold d2k0Cnt; exact card_filter_univ_Z _ _
lemma mu1Cnt_Z [DecidablePred fun i : Idx => D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0] :
    (K.mu1Cnt : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then (1 : ℤ) else 0) := by
  unfold mu1Cnt; exact card_filter_univ_Z _ _
lemma ntUNorm_Z [DecidablePred K.isNorm] :
    (K.ntUNorm : ℤ) = ∑ i : Idx, (if K.isNorm i then ((D.k i - 3 : ℕ) : ℤ) else 0) := by
  unfold ntUNorm; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
lemma ntUMbad_Z [DecidablePred K.isMbad] :
    (K.ntUMbad : ℤ) = ∑ i : Idx, (if K.isMbad i then ((D.k i - 3 : ℕ) : ℤ) else 0) := by
  unfold ntUMbad; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
lemma ntUML_Z [DecidablePred K.isML] :
    (K.ntUML : ℤ) = ∑ i : Idx, (if K.isML i then ((D.k i - 3 : ℕ) : ℤ) else 0) := by
  unfold ntUML; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
lemma muExK3_Z [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ K.isNorm i] [DecidablePred fun i : Idx => 3 ≤ D.k i ∧ K.isMbad i] :
    (K.muExK3 : ℤ) = ∑ i : Idx, ((if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
      else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2 else 0 : ℕ) : ℤ) := by
  unfold muExK3; rw [Nat.cast_sum]
  apply Finset.sum_congr rfl; intro i _
  by_cases h1 : 3 ≤ D.k i ∧ K.isNorm i <;> by_cases h2 : 3 ≤ D.k i ∧ K.isMbad i <;> simp [h1, h2]

lemma ntU_split : K.ntUNorm + K.ntUMbad + K.ntUML = S.ntU := by
  classical
  unfold ntUNorm ntUMbad ntUML KerD45Syzygy.ntU
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  unfold isNorm isMbad isML
  by_cases hU : S.isU0 i
  · by_cases hk3 : 3 ≤ D.k i
    · have hk2 : 2 ≤ D.k i := by omega
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0
      · by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
        · simp [hU, hk2, hg, hm]
        · simp [hU, hk2, hg, hm]
      · simp [hU, hk2, hg]
    · have h0 : D.k i - 3 = 0 := by omega
      simp [h0]
  · simp [hU]

lemma K1_base_le : (D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt + K.mbadCnt ≤ K.K1.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i ≤ 1 then 0 else if S.isU0 i then (if K.isMbad i then D.k i - 1 else D.k i - 2) else D.k i - 1
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.K1 := fun i _ => by
    dsimp [f]; split_ifs with hk hU hmb
    · simp
    · exact K.pow_dvd_K1_mbad i hmb.2.2
    · exact K.pow_dvd_K1_all i
    · exact K.pow_dvd_K1_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective K.K1 K.hK1_ne f hdvd
  have hU := S.U_counts_ineqs
  have hZ : ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt + K.mbadCnt : ℤ) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) + (K.mbadCnt : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 then (1 : ℤ) else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          2 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          ((D.k i - 3 : ℕ) : ℤ) + (if K.isMbad i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [show ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt + K.mbadCnt : ℤ) =
        ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) + (K.mbadCnt : ℤ) by omega, hrew]
    apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      simp only [isMbad, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma M0s_base_le :
    (S.n2U + S.n3U + K.mbadCnt - K.mLCnt) + K.mu1Cnt + K.muExK3 ≤ K.M0s.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if K.isNorm i then (if 3 ≤ D.k i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) else 1)
    else if K.isMbad i then (if 3 ≤ D.k i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) else 2)
    else if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then 1
    else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.M0s := fun i _ => by
    dsimp [f]; split_ifs with hn hk3 hmb hk3' hmu1
    · exact pow_rootMultiplicity_dvd K.M0s _
    · rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2
    · exact pow_rootMultiplicity_dvd K.M0s _
    · exact (pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2)
    · rw [pow_one]; exact dvd_iff_isRoot.mpr hmu1.2.2.2
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective K.M0s K.hM0s_ne f hdvd
  have hmb_mL : K.mbadCnt + K.mLCnt ≤ S.n2U + S.n3U := by
    have hZ : (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) ≤ (S.n2U : ℤ) + (S.n3U : ℤ) := by
      have h1 : (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) = ∑ i : Idx, ((if K.isMbad i then (1 : ℤ) else 0) + (if K.isML i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.mbadCnt_Z, ← K.mLCnt_Z]
      have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← n2U_Z, ← n3U_Z]
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isMbad, isML, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hZ : ((S.n2U + S.n3U + K.mbadCnt - K.mLCnt) + K.mu1Cnt + K.muExK3 : ℤ) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : ((S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ)) + (K.mu1Cnt : ℤ) + (K.muExK3 : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          (if K.isMbad i then 1 else 0) - (if K.isML i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then 1 else 0) +
          ((if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
            else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2 else 0 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
    rw [show ((S.n2U + S.n3U + K.mbadCnt - K.mLCnt) + K.mu1Cnt + K.muExK3 : ℤ) =
        ((S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ)) + (K.mu1Cnt : ℤ) + (K.muExK3 : ℤ) by omega, hrew]
    apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hn : K.isNorm i
    · have hrm1 : 1 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
        (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
      have hU := hn.2.1; have hg := hn.2.2.1; have hm := hn.2.2.2; have hk2 := hn.1
      simp only [hn, isNorm, isMbad, isML, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte]
      (try split_ifs) <;> omega
    · by_cases hmb : K.isMbad i
      · have hrm2 : 2 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
          (le_rootMultiplicity_iff K.hM0s_ne).mpr ((pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2))
        have hU := hmb.2.1; have hg : ¬ (K.g2t.eval (BinaryIRSProfile.domain i) = 0) := hmb.2.2; have hk2 := hmb.1
        simp only [hn, hmb, isNorm, isMbad, isML, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte]
        (try split_ifs) <;> omega
      · by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
          by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
          by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
          simp only [isNorm, isMbad, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
            and_true, and_false, true_and, false_and, ↓reduceIte] at hn hmb ⊢ <;>
          (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma g2t_extra_le :
    (S.n2U + S.n3U - K.mbadCnt) + K.d2k0Cnt + (S.n1U - K.mu1Cnt) + 2 * (K.mLCnt - K.dmLCnt) ≤ K.g2t.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if K.isNorm i then 1
    else if K.isML i then (if K.isD1 i then 1 else 3)
    else if D.k i = 0 ∧ K.isD1 i then 1
    else if D.k i = 1 ∧ S.isU0 i ∧ (K.isD1 i ∨ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0) then 1
    else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ K.g2t := fun i _ => by
    dsimp [f]; split_ifs with hn hmL hD1 hk0 hk1
    · rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.1
    · rw [pow_one]; exact dvd_iff_isRoot.mpr hmL.2.2.1
    · have hH1d := (pow_dvd_pow (X - C (BinaryIRSProfile.domain i)) (by have := hmL.1; omega : 3 ≤ 2 * D.k i - 1)).trans
        (S.pow_dvd_H1_of_isU0 i hmL.2.1)
      rw [K.hH1_fac] at hH1d
      have hcop : IsCoprime ((X - C (BinaryIRSProfile.domain i)) ^ 3) (S.D1 ^ 4 * K.M0s.comp (X ^ 2)) := by
        apply IsCoprime.pow_left
        have hne : (S.D1 ^ 4 * K.M0s.comp (X ^ 2)).eval (BinaryIRSProfile.domain i) ≠ 0 := by
          rw [eval_mul, eval_pow, eval_comp, eval_pow, eval_X]
          exact mul_ne_zero (pow_ne_zero 4 hD1) hmL.2.2.2
        exact (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
      exact hcop.dvd_of_dvd_mul_left hH1d
    · rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hk0.2)
    · rcases hk1.2.2 with hD1' | hM0'
      · rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1')
      · by_cases hD1' : K.isD1 i
        · rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1')
        · have hH1d : X - C (BinaryIRSProfile.domain i) ∣ S.H1 := by
            have := S.pow_dvd_H1_of_isU0 i hk1.2.1; rwa [hk1.1, pow_one] at this
          rw [K.hH1_fac] at hH1d
          have hcop : IsCoprime (X - C (BinaryIRSProfile.domain i)) (S.D1 ^ 4 * K.M0s.comp (X ^ 2)) := by
            have hne : (S.D1 ^ 4 * K.M0s.comp (X ^ 2)).eval (BinaryIRSProfile.domain i) ≠ 0 := by
              rw [eval_mul, eval_pow, eval_comp, eval_pow, eval_X]
              exact mul_ne_zero (pow_ne_zero 4 hD1') hM0'
            exact (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
          rw [pow_one]; exact hcop.dvd_of_dvd_mul_left hH1d
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    K.g2t K.hg2t_ne f hdvd
  have hmb_le : K.mbadCnt ≤ S.n2U + S.n3U := by
    have hZ : (K.mbadCnt : ℤ) ≤ (S.n2U : ℤ) + (S.n3U : ℤ) := by
      have h1 : (K.mbadCnt : ℤ) = ∑ i : Idx, (if K.isMbad i then (1 : ℤ) else 0) := K.mbadCnt_Z
      have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← n2U_Z, ← n3U_Z]
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        simp only [isMbad, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hmu1_le : K.mu1Cnt ≤ S.n1U := by
    have hZ : (K.mu1Cnt : ℤ) ≤ (S.n1U : ℤ) := by
      rw [K.mu1Cnt_Z, n1U_Z]
      apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [hU, hD1, hm, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hdmL_le : K.dmLCnt ≤ K.mLCnt := by
    have hZ : (K.dmLCnt : ℤ) ≤ (K.mLCnt : ℤ) := by
      have h1 : (K.dmLCnt : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z]; unfold dmLCnt; push_cast; rfl
      have h2 : (K.mLCnt : ℤ) = ∑ i : Idx, (if K.isML i then (1 : ℤ) else 0) := K.mLCnt_Z
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hZ : ((S.n2U + S.n3U - K.mbadCnt) + K.d2k0Cnt + (S.n1U - K.mu1Cnt) + 2 * (K.mLCnt - K.dmLCnt) : ℤ) =
      ∑ i : Idx, (f i : ℤ) := by
    have hrew : ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ)) + (K.d2k0Cnt : ℤ) +
        ((S.n1U : ℤ) - (K.mu1Cnt : ℤ)) + 2 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) =
        ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) -
          (if K.isMbad i then 1 else 0) + (if D.k i = 0 ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i then 1 else 0) -
          (if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then 1 else 0) +
          2 * (if K.isML i then 1 else 0) -
          2 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) -
          2 * (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dmLCnt, Nat.cast_add]; ring
    rw [show ((S.n2U + S.n3U - K.mbadCnt) + K.d2k0Cnt + (S.n1U - K.mu1Cnt) + 2 * (K.mLCnt - K.dmLCnt) : ℤ) =
        ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ)) + (K.d2k0Cnt : ℤ) +
        ((S.n1U : ℤ) - (K.mu1Cnt : ℤ)) + 2 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) by omega, hrew]
    apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, isMbad, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma D1_counts_le : K.dinCnt + K.d2k1UCnt + K.d2k0Cnt + K.dmLCnt ≤ S.D1.natDegree := by
  classical
  let f : Idx → ℕ := fun i => if K.isD1 i then 1 else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ S.D1 := fun i _ => by
    dsimp [f]; split_ifs with h
    · rw [pow_one]; exact dvd_iff_isRoot.mpr h
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    S.D1 S.D1_ne_zero f hdvd
  have hsum : K.dinCnt + K.d2k1UCnt + K.d2k0Cnt + K.dmLCnt ≤ ∑ i : Idx, f i := by
    have hZ : (K.dinCnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) + (K.dmLCnt : ℤ) ≤ ∑ i : Idx, (f i : ℤ) := by
      have hrew : (K.dinCnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) + (K.dmLCnt : ℤ) =
          ∑ i : Idx, ((if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
            (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
            (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
            (if D.k i = 0 ∧ K.isD1 i then 1 else 0) +
            (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
            (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
        simp only [dinCnt, dmLCnt, Nat.cast_add]; ring
      rw [hrew]; apply Finset.sum_le_sum; intro i _; dsimp [f]
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    rw [← Nat.cast_sum] at hZ; omega
  omega

lemma mL_ntUML_le_Lam1 : K.mLCnt + 2 * K.ntUML ≤ K.Lam1.natDegree := by
  classical
  let f : Idx → ℕ := fun i => if K.isML i then 2 * D.k i - 3 else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.Lam1 := fun i _ => by
    dsimp [f]; split_ifs with hmL
    · have hprod := K.pow_dvd_Lam1_mul_M0s i
      simp only [hmL.2.1, show ¬ D.k i ≤ 1 by have := hmL.1; omega, ↓reduceIte] at hprod
      have hcop := ((Polynomial.irreducible_X_sub_C (BinaryIRSProfile.domain i ^ 2)).coprime_iff_not_dvd.mpr
        (mt dvd_iff_isRoot.mp hmL.2.2.2)).pow_left (m := 2 * D.k i - 3)
      exact hcop.dvd_of_dvd_mul_right hprod
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective K.Lam1 K.hLam1_ne f hdvd
  have hsum : K.mLCnt + 2 * K.ntUML ≤ ∑ i : Idx, f i := by
    have hZ : (K.mLCnt : ℤ) + 2 * (K.ntUML : ℤ) ≤ ∑ i : Idx, (f i : ℤ) := by
      have hrew : (K.mLCnt : ℤ) + 2 * (K.ntUML : ℤ) =
          ∑ i : Idx, ((if K.isML i then (1 : ℤ) else 0) + 2 * (if K.isML i then ((D.k i - 3 : ℕ) : ℤ) else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      rw [hrew]; apply Finset.sum_le_sum; intro i _; dsimp [f]
      by_cases hmL : K.isML i
      · have := hmL.1; simp only [hmL, ↓reduceIte]; omega
      · simp only [hmL, ↓reduceIte]; omega
    rw [← Nat.cast_sum] at hZ; omega
  omega

lemma row321_bound :
    2 * (S.n3U : ℤ) - 2 * (K.dinCnt : ℤ) - 2 * (K.dmLCnt : ℤ) - (K.mbadCnt : ℤ) +
      2 * (K.ntUNorm : ℤ) + 2 * (K.ntUML : ℤ) ≤ (K.Lam1.natDegree : ℤ) + (K.muExK3 : ℤ) := by
  classical
  have hsum_lam : ∑ i : Idx, K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) ≤ K.Lam1.natDegree :=
    sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective K.Lam1 K.hLam1_ne _ (fun i _ => pow_rootMultiplicity_dvd K.Lam1 _)
  have hZ : (2 * (S.n3U : ℤ) - 2 * (K.dinCnt : ℤ) - 2 * (K.dmLCnt : ℤ) - (K.mbadCnt : ℤ) +
      2 * (K.ntUNorm : ℤ) + 2 * (K.ntUML : ℤ)) ≤
      ∑ i : Idx, ((K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ) +
        ((if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
          else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2 else 0 : ℕ) : ℤ)) := by
    have hrew : 2 * (S.n3U : ℤ) - 2 * (K.dinCnt : ℤ) - 2 * (K.dmLCnt : ℤ) - (K.mbadCnt : ℤ) +
        2 * (K.ntUNorm : ℤ) + 2 * (K.ntUML : ℤ) =
        ∑ i : Idx, (2 * (if 3 ≤ D.k i ∧ S.isU0 i then (1 : ℤ) else 0) -
          2 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) -
          2 * (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) -
          2 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) -
          2 * (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0) -
          (if K.isMbad i then 1 else 0) +
          2 * (if K.isNorm i then ((D.k i - 3 : ℕ) : ℤ) else 0) +
          2 * (if K.isML i then ((D.k i - 3 : ℕ) : ℤ) else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dinCnt, dmLCnt, Nat.cast_add]; ring
    rw [hrew]; apply Finset.sum_le_sum; intro i _
    have hprod_rm : (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) else 0) ≤
        K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
          K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
      by_cases hU : S.isU0 i
      · have hprod := K.pow_dvd_Lam1_mul_M0s i
        simp only [hU, ↓reduceIte] at hprod ⊢
        have hle := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
        rwa [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne)] at hle
      · simp [hU]
    by_cases hk3 : 3 ≤ D.k i
    · by_cases hU : S.isU0 i
      · by_cases hn : K.isNorm i
        · have hM1 : 1 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
            (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
          have hg := hn.2.2.1; have hm := hn.2.2.2
          by_cases hD1 : K.isD1 i <;>
            simp only [hn, isNorm, isML, isMbad, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
              and_true, and_false, true_and, false_and, ↓reduceIte] at hprod_rm ⊢ <;>
            (try split_ifs at hprod_rm ⊢) <;> omega
        · by_cases hmL : K.isML i
          · have hM0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 :=
              rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
            have hg := hmL.2.2.1; have hm : ¬ (K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0) := hmL.2.2.2
            by_cases hD1 : K.isD1 i <;>
              simp only [hn, hmL, isNorm, isML, isMbad, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, and_false, true_and, false_and, ↓reduceIte] at hprod_rm ⊢ <;>
              (try split_ifs at hprod_rm ⊢) <;> omega
          · have hmb : K.isMbad i := by
              refine ⟨by omega, hU, ?_⟩
              intro hg; by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
              · exact hn ⟨by omega, hU, hg, hm⟩
              · exact hmL ⟨by omega, hU, hg, hm⟩
            have hM2 : 2 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
              (le_rootMultiplicity_iff K.hM0s_ne).mpr ((pow_dvd_pow _ (by omega : 2 ≤ D.k i)).trans (K.pow_dvd_M0s_mbad i hU hmb.2.2))
            have hg : ¬ (K.g2t.eval (BinaryIRSProfile.domain i) = 0) := hmb.2.2
            by_cases hD1 : K.isD1 i <;>
              simp only [hn, hmL, hmb, isNorm, isML, isMbad, hU, hD1, hg, ne_eq, not_true_eq_false, not_false_eq_true,
                and_true, and_false, true_and, false_and, ↓reduceIte] at hprod_rm ⊢ <;>
              (try split_ifs at hprod_rm ⊢) <;> omega
      · by_cases hD1 : K.isD1 i <;>
          simp only [isNorm, isML, isMbad, hU, hD1, ne_eq, not_true_eq_false, not_false_eq_true,
            and_true, and_false, true_and, false_and, ↓reduceIte] <;>
          (try split_ifs) <;> omega
    · by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, isMbad, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
  rw [Finset.sum_add_distrib] at hZ
  have h1 : (∑ i : Idx, (K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ)) ≤ (K.Lam1.natDegree : ℤ) := by
    exact_mod_cast hsum_lam
  have h2 : (∑ i : Idx, ((if 3 ≤ D.k i ∧ K.isNorm i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1
      else if 3 ≤ D.k i ∧ K.isMbad i then K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 2 else 0 : ℕ) : ℤ)) =
      (K.muExK3 : ℤ) := by unfold muExK3; push_cast; rfl
  omega

lemma g1_d2_bound :
    K.d2k0Cnt + K.d2k1UCnt + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt ≤ (D.gj 1).natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i = 0 then (if K.isD1 i then 1 else 0)
    else if D.k i = 1 then (if S.isU0 i ∧ K.isD1 i then 1 else 0)
    else if S.isU0 i then 2 * D.k i - 3
    else 2 * (D.k i - 1)
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ D.gj 1 := fun i _ => by
    dsimp [f]; split_ifs with hk0 hD1 hk1 hD1' hU
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 1)
    · simp
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1'.2).trans (S.D1_dvd_gj 1)
    · simp
    · exact K.pow_dvd_g1_U0 i
    · exact K.pow_dvd_g1_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.gj 1) K.hg1_ne f hdvd
  have hU := S.U_counts_ineqs
  have hZ : ((K.d2k0Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
      (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : (K.d2k0Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
        (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, ((if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          2 * (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          4 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      simp only [hU, hD1, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma g2_din_bound :
    3 * K.dinCnt + K.d2k1UCnt + K.d2k0Cnt + K.dmLCnt ≤ (D.gj 2).natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if K.isNorm i ∧ K.isD1 i then 3
    else if (K.isML i ∧ K.isD1 i) ∨ (D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i) ∨ (D.k i = 0 ∧ K.isD1 i) then 1
    else 0
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ D.gj 2 := fun i _ => by
    dsimp [f]; split_ifs with h1 h2
    · exact K.pow_dvd_g2_din i h1.1.1 h1.1.2.1 h1.1.2.2.1 h1.1.2.2.2 h1.2
    · rw [pow_one]
      have hD1 : K.isD1 i := by
        rcases h2 with h | h | h
        · exact h.2
        · exact h.2.2
        · exact h.2
      exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2)
    · simp
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.gj 2) D.g2_ne_zero f hdvd
  have hZ : (3 * (K.dinCnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) + (K.dmLCnt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 3 * (K.dinCnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) + (K.dmLCnt : ℤ) =
        ∑ i : Idx, (3 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
          3 * (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 0 ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dinCnt, dmLCnt, Nat.cast_add]; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma g2_din2_full_bound :
    3 * K.din2Cnt + K.dmL2Cnt + K.d2k1UCnt + K.d2k0Cnt + (2 * D.n3 - S.n3U) + 2 * D.nt ≤ (D.gj 2).natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i = 0 then (if K.isD1 i then 1 else 0)
    else if D.k i = 1 then (if S.isU0 i ∧ K.isD1 i then 1 else 0)
    else if D.k i = 2 then (if K.isNorm i ∧ K.isD1 i then 3 else if K.isML i ∧ K.isD1 i then 1 else 0)
    else if S.isU0 i then 2 * D.k i - 5
    else 2 * (D.k i - 2)
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ D.gj 2 := fun i _ => by
    dsimp [f]; split_ifs with hk0 hD1 hk1 hD1' hk2 hdin2 hdmL2 hU
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2)
    · simp
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1'.2).trans (S.D1_dvd_gj 2)
    · simp
    · exact K.pow_dvd_g2_din i hdin2.1.1 hdin2.1.2.1 hdin2.1.2.2.1 hdin2.1.2.2.2 hdin2.2
    · rw [pow_one]; exact (dvd_iff_isRoot.mpr hdmL2.2).trans (S.D1_dvd_gj 2)
    · simp
    · exact D.pow_dvd_g2_of_k i
    · exact K.pow_dvd_g2_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.gj 2) D.g2_ne_zero f hdvd
  have hU := S.U_counts_ineqs
  have hZ : (3 * (K.din2Cnt : ℤ) + (K.dmL2Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) +
      (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 3 * (K.din2Cnt : ℤ) + (K.dmL2Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) +
        (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, (3 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 0 ∧ K.isD1 i then 1 else 0) +
          2 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma ResY_uncond_bound :
    4 * K.d2k0Cnt + 3 * K.d2k1UCnt + 12 * K.din2Cnt + 2 * K.dmL2Cnt +
      (4 * D.n1 - 3 * S.n1U) + (16 * D.n2 - 5 * S.n2U) + (34 * D.n3 - 5 * S.n3U) + 18 * D.nt ≤
      D.ResY.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i = 0 ∧ K.isD1 i then 4
    else if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 4
    else if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then 23
    else if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 13
    else if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i)
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ D.ResY := fun i _ => by
    dsimp [f]; split_ifs with h0 h1 h2n h2m hU
    · rw [K.hResY_fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h0.2) 4) _) _) _
    · rw [K.hResY_fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h1.2.2) 4) _) _) _
    · rw [K.hResY_fac]
      have hdD : (X - C (BinaryIRSProfile.domain i)) ^ 4 ∣ S.D1 ^ 4 := pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h2n.2.2) 4
      have hdL : (X - C (BinaryIRSProfile.domain i)) ^ 8 ∣ K.Lam1.comp (X ^ 2) ^ 4 := by
        have hL1 := K.pow_dvd_Lam1_d2 i h2n.2.2; rw [h2n.1] at hL1
        have hL2 := (pow_dvd_comp_X_sq_iff K.Lam1 (BinaryIRSProfile.domain i) 1).mpr hL1
        rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hL2 4
      have hdM : (X - C (BinaryIRSProfile.domain i)) ^ 10 ∣ K.M0s.comp (X ^ 2) ^ 5 := by
        have hM2 := (pow_dvd_comp_X_sq_iff K.M0s (BinaryIRSProfile.domain i) 1).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.1.2.2.2)
        rw [show (10 : ℕ) = 2 * 5 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hM2 5
      have hdg : (X - C (BinaryIRSProfile.domain i)) ^ 1 ∣ K.g2t := by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.1.2.2.1
      rw [show (23 : ℕ) = 4 + 8 + 10 + 1 by rfl, pow_add, pow_add, pow_add]
      exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hdD hdL) hdM) hdg
    · rw [K.hResY_fac]
      have hdD : (X - C (BinaryIRSProfile.domain i)) ^ 4 ∣ S.D1 ^ 4 := pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h2m.2.2) 4
      have hdL : (X - C (BinaryIRSProfile.domain i)) ^ 8 ∣ K.Lam1.comp (X ^ 2) ^ 4 := by
        have hL1 := K.pow_dvd_Lam1_d2 i h2m.2.2; rw [h2m.1] at hL1
        have hL2 := (pow_dvd_comp_X_sq_iff K.Lam1 (BinaryIRSProfile.domain i) 1).mpr hL1
        rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hL2 4
      have hdg : (X - C (BinaryIRSProfile.domain i)) ^ 1 ∣ K.g2t := by rw [pow_one]; exact dvd_iff_isRoot.mpr h2m.2.1.2.2.1
      rw [show (13 : ℕ) = 4 + 8 + 0 + 1 by rfl, pow_add, pow_add, pow_add, pow_zero]
      exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hdD hdL) (one_dvd _)) hdg
    · exact D.pow_dvd_ResY_U0 i
    · exact S.pow_dvd_ResY_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    D.ResY D.ResY_ne_zero f hdvd
  have hU := S.U_counts_ineqs
  have hZ : (4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + 12 * (K.din2Cnt : ℤ) + 2 * (K.dmL2Cnt : ℤ) +
      (4 * (D.n1 : ℤ) - 3 * (S.n1U : ℤ)) + (16 * (D.n2 : ℤ) - 5 * (S.n2U : ℤ)) +
      (34 * (D.n3 : ℤ) - 5 * (S.n3U : ℤ)) + 18 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + 12 * (K.din2Cnt : ℤ) + 2 * (K.dmL2Cnt : ℤ) +
        (4 * (D.n1 : ℤ) - 3 * (S.n1U : ℤ)) + (16 * (D.n2 : ℤ) - 5 * (S.n2U : ℤ)) +
        (34 * (D.n3 : ℤ) - 5 * (S.n3U : ℤ)) + 18 * (D.nt : ℤ) =
        ∑ i : Idx, (4 * (if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) +
          3 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          12 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
          2 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          4 * (if D.k i = 1 then 1 else 0) - 3 * (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
          16 * (if D.k i = 2 then 1 else 0) - 5 * (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          34 * (if 3 ≤ D.k i then 1 else 0) - 5 * (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          18 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, KerD45Data.resOrdU0, KerD45Data.resOrdU1, hU, hD1, hg, hm,
        ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma ResY_eK_bound :
    4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + 20 * (K.din2Cnt : ℤ) + 10 * (K.dmL2Cnt : ℤ) -
      8 * ((K.K1.natDegree - ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt) : ℕ) : ℤ) +
      (4 * (D.n1 : ℤ) - 3 * (S.n1U : ℤ)) + (16 * (D.n2 : ℤ) - 5 * (S.n2U : ℤ)) +
      (34 * (D.n3 : ℤ) - 5 * (S.n3U : ℤ)) + 18 * (D.nt : ℤ) ≤ (D.ResY.natDegree : ℤ) := by
  classical
  have hsum_Res : ∑ i : Idx, D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) ≤ D.ResY.natDegree :=
    sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
      D.ResY D.ResY_ne_zero _ (fun i _ => pow_rootMultiplicity_dvd D.ResY _)
  have hsum_K1 : ∑ i : Idx, K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) ≤ K.K1.natDegree :=
    sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective K.K1 K.hK1_ne _ (fun i _ => pow_rootMultiplicity_dvd K.K1 _)
  let baseK1 : Idx → ℕ := fun i =>
    if D.k i ≤ 1 then 0 else if S.isU0 i then D.k i - 2 else D.k i - 1
  have hbaseK1_le : ∀ i : Idx, baseK1 i ≤ K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := fun i => by
    apply (le_rootMultiplicity_iff K.hK1_ne).mpr
    dsimp [baseK1]; split_ifs with hk hU
    · simp
    · exact K.pow_dvd_K1_all i
    · exact K.pow_dvd_K1_U1 i hU
  have hU := S.U_counts_ineqs
  have hbaseK1_sum : (∑ i : Idx, (baseK1 i : ℤ)) = ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) := by
    have hrew : ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 then (1 : ℤ) else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          2 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) + ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [baseK1]
    by_cases hU : S.isU0 i <;>
      simp only [hU, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  have heK_ge : ∑ i : Idx, ((K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ) - (baseK1 i : ℤ)) ≤
      ((K.K1.natDegree - ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt) : ℕ) : ℤ) := by
    rw [Finset.sum_sub_distrib, hbaseK1_sum]
    have hK1b' : (D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt ≤ K.K1.natDegree :=
      Nat.le_trans (Nat.le_add_right _ _) K.K1_base_le
    have h1 : (∑ i : Idx, (K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ)) ≤ (K.K1.natDegree : ℤ) := by
      exact_mod_cast hsum_K1
    have h2 : S.n2U ≤ D.n2 := hU.2.1
    have h3 : S.n3U ≤ 2 * D.n3 := by have := hU.2.2.1; omega
    simp only [Nat.cast_sub hK1b', Nat.cast_add, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [h1]
  have hpt : ∀ i : Idx,
      4 * (if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) +
      3 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
      20 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
      10 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
      4 * (if D.k i = 1 then 1 else 0) - 3 * (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
      16 * (if D.k i = 2 then 1 else 0) - 5 * (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
      34 * (if 3 ≤ D.k i then 1 else 0) - 5 * (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
      18 * ((D.k i - 3 : ℕ) : ℤ) ≤
      (D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) : ℤ) +
        8 * ((K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ) - (baseK1 i : ℤ)) := by
    intro i
    have hk1_nn : (0 : ℤ) ≤ (K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) : ℤ) - (baseK1 i : ℤ) := by
      have := hbaseK1_le i; omega
    by_cases h2n : D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i
    · have hKL : 2 ≤ K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) + K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
        have hd := K.pow_dvd_K_M10sh_d2 i h2n.2.2
        simp only [h2n.1, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hd
        have hle := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hd
        rwa [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hle
      have hRes_rm : D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) =
          4 * S.D1.rootMultiplicity (BinaryIRSProfile.domain i) +
          8 * K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
          10 * K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
          K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) := by
        have hL_ne := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
        have hM_ne := mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne
        rw [K.hResY_fac,
          rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)) K.hg2t_ne),
          rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)),
          rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)),
          rootMultiplicity_pow_eq' S.D1 S.D1_ne_zero 4 _,
          rootMultiplicity_pow_eq' _ hL_ne 4 _,
          rootMultiplicity_pow_eq' _ hM_ne 5 _,
          show (K.Lam1.comp (X ^ 2)).rootMultiplicity (BinaryIRSProfile.domain i) = 2 * K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) by
            rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne, ← map_pow, rootMultiplicity_map_eq],
          show (K.M0s.comp (X ^ 2)).rootMultiplicity (BinaryIRSProfile.domain i) = 2 * K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) by
            rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne, ← map_pow, rootMultiplicity_map_eq]]
        ring
      have hD1_1 : 1 ≤ S.D1.rootMultiplicity (BinaryIRSProfile.domain i) :=
        (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.2)
      have hM_1 : 1 ≤ K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
        (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.1.2.2.2)
      have hg_1 : 1 ≤ K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) :=
        (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2n.2.1.2.2.1)
      have hb0 : baseK1 i = 0 := by dsimp [baseK1]; rw [if_neg (by omega), if_pos h2n.2.1.2.1]; omega
      have hnML : ¬ K.isML i := fun h => h.2.2.2 h2n.2.1.2.2.2
      simp only [h2n.1, h2n.2.1, h2n.2.2, h2n.2.1.2.1, hnML, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
        show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega), hb0, ↓reduceIte, and_true, false_and, true_and]
      omega
    · by_cases h2m : D.k i = 2 ∧ K.isML i ∧ K.isD1 i
      · have hKL : 2 ≤ K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) + K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
          have hd := K.pow_dvd_K_M10sh_d2 i h2m.2.2
          simp only [h2m.1, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hd
          have hle := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hd
          rwa [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hle
        have hRes_rm : D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) =
            4 * S.D1.rootMultiplicity (BinaryIRSProfile.domain i) +
            8 * K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
            10 * K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) +
            K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) := by
          have hL_ne := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
          have hM_ne := mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne
          rw [K.hResY_fac,
            rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)) K.hg2t_ne),
            rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)),
            rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)),
            rootMultiplicity_pow_eq' S.D1 S.D1_ne_zero 4 _,
            rootMultiplicity_pow_eq' _ hL_ne 4 _,
            rootMultiplicity_pow_eq' _ hM_ne 5 _,
            show (K.Lam1.comp (X ^ 2)).rootMultiplicity (BinaryIRSProfile.domain i) = 2 * K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) by
              rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne, ← map_pow, rootMultiplicity_map_eq],
            show (K.M0s.comp (X ^ 2)).rootMultiplicity (BinaryIRSProfile.domain i) = 2 * K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) by
              rw [← rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne, ← map_pow, rootMultiplicity_map_eq]]
          ring
        have hD1_1 : 1 ≤ S.D1.rootMultiplicity (BinaryIRSProfile.domain i) :=
          (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2m.2.2)
        have hg_1 : 1 ≤ K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) :=
          (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h2m.2.1.2.2.1)
        have hb0 : baseK1 i = 0 := by dsimp [baseK1]; rw [if_neg (by omega), if_pos h2m.2.1.2.1]; omega
        have hnN : ¬ K.isNorm i := fun h => h2m.2.1.2.2.2 h.2.2.2
        simp only [h2m.1, h2m.2.1, h2m.2.2, h2m.2.1.2.1, hnN, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
          show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega), hb0, ↓reduceIte, and_true, false_and, true_and]
        omega
      · have hRes_base : (if D.k i = 0 ∧ K.isD1 i then 4
            else if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 4
            else if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i)) ≤
            D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) := by
          apply (le_rootMultiplicity_iff D.ResY_ne_zero).mpr
          split_ifs with h0 h1 hU
          · rw [K.hResY_fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h0.2) 4) _) _) _
          · rw [K.hResY_fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h1.2.2) 4) _) _) _
          · exact D.pow_dvd_ResY_U0 i
          · exact S.pow_dvd_ResY_U1 i hU
        unfold KerD45Data.resOrdU0 KerD45Data.resOrdU1 at hRes_base
        by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
          by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
          by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
          simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
            and_true, and_false, true_and, false_and, ↓reduceIte] at h2n h2m hRes_base ⊢ <;>
          (try split_ifs at hRes_base ⊢) <;> omega
  have htot := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] at htot
  rw [Finset.sum_sub_distrib] at heK_ge
  have hR_Z : (∑ i : Idx, (D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) : ℤ)) ≤ (D.ResY.natDegree : ℤ) := by
    exact_mod_cast hsum_Res
  linarith [heK_ge, hR_Z]

lemma H1_d2_bound :
    4 * K.d2k0Cnt + 3 * K.d2k1UCnt + S.n1U + 3 * S.n2U + 3 * S.n3U + 2 * D.n3 + 2 * D.nt ≤ S.H1.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i = 0 ∧ K.isD1 i then 4
    else if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 4
    else if S.isU0 i then 2 * D.k i - 1
    else 2 * (D.k i - 2)
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i)) ^ f i ∣ S.H1 := fun i _ => by
    dsimp [f]; split_ifs with h0 h1 hU
    · exact ((pow_dvd_pow _ (by omega : 4 ≤ 5)).trans (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h0.2) 5)).trans S.D1_pow5_dvd_H1
    · exact ((pow_dvd_pow _ (by omega : 4 ≤ 5)).trans (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr h1.2.2) 5)).trans S.D1_pow5_dvd_H1
    · exact S.pow_dvd_H1_of_isU0 i hU
    · exact K.pow_dvd_H1_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    S.H1 S.H1_ne_zero f hdvd
  have hZ : (4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + (S.n1U : ℤ) + 3 * (S.n2U : ℤ) +
      3 * (S.n3U : ℤ) + 2 * (D.n3 : ℤ) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + (S.n1U : ℤ) + 3 * (S.n2U : ℤ) +
        3 * (S.n3U : ℤ) + 2 * (D.n3 : ℤ) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, (4 * (if D.k i = 0 ∧ K.isD1 i then (1 : ℤ) else 0) +
          3 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
          3 * (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          3 * (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * (if 3 ≤ D.k i then 1 else 0) + 2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      simp only [hU, hD1, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma Lam1_M0s_U_bound :
    (D.n1 - S.n1U) + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt ≤ K.Lam1.natDegree + K.M0s.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)
    else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2)
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective (K.Lam1 * K.M0s) (mul_ne_zero K.hLam1_ne K.hM0s_ne) f (fun i _ => K.pow_dvd_Lam1_mul_M0s i)
  rw [natDegree_mul K.hLam1_ne K.hM0s_ne] at hle
  have hU := S.U_counts_ineqs
  have hZ : (((D.n1 : ℤ) - (S.n1U : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
      (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : ((D.n1 : ℤ) - (S.n1U : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
        (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, ((if D.k i = 1 then (1 : ℤ) else 0) - (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
          2 * (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          4 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
    by_cases hU : S.isU0 i <;>
      simp only [hU, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

lemma K_tot_bound :
    2 * K.dinCnt + K.dmLCnt + K.mLCnt + (D.n2 - S.n2U) + (3 * D.n3 - S.n3U) + 2 * D.nt ≤
      K.K1.natDegree + K.Lam1.natDegree := by
  classical
  let f : Idx → ℕ := fun i =>
    if D.k i ≤ 1 then 0
    else if ¬ S.isU0 i then (if D.k i = 2 then 1 else 3 + 2 * (D.k i - 3))
    else if K.isD1 i then (if K.isNorm i ∨ K.isML i then 2 * D.k i - 2 else 0)
    else if K.isML i then (if D.k i = 2 then 1 else 3 + 2 * (D.k i - 3))
    else 2 * D.k i - 4
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.K1 * K.Lam1 := fun i _ => by
    dsimp only [f]
    by_cases hk1 : D.k i ≤ 1
    · simp [hk1]
    · simp only [hk1, ↓reduceIte]
      by_cases hU : S.isU0 i
      · simp only [hU, not_true_eq_false, ↓reduceIte]
        by_cases hD1 : K.isD1 i
        · simp only [hD1, ↓reduceIte]
          by_cases hNM : K.isNorm i ∨ K.isML i
          · simp only [hNM, ↓reduceIte]
            have h := K.pow_dvd_K_M10sh_d2 i hD1; simp only [hk1, ↓reduceIte] at h; exact h
          · simp [hNM]
        · simp only [hD1, ↓reduceIte]
          by_cases hmL : K.isML i
          · simp only [hmL, ↓reduceIte]
            have hK1d := K.pow_dvd_K1_all i
            have hL1d : (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (2 * D.k i - 3) ∣ K.Lam1 := by
              have hprod := K.pow_dvd_Lam1_mul_M0s i
              simp only [hU, hk1, ↓reduceIte] at hprod
              have hcop := ((Polynomial.irreducible_X_sub_C (BinaryIRSProfile.domain i ^ 2)).coprime_iff_not_dvd.mpr
                (mt dvd_iff_isRoot.mp hmL.2.2.2)).pow_left (m := 2 * D.k i - 3)
              exact hcop.dvd_of_dvd_mul_right hprod
            exact (pow_dvd_pow _ (by split_ifs <;> omega : (if D.k i = 2 then 1 else 3 + 2 * (D.k i - 3)) ≤ (D.k i - 2) + (2 * D.k i - 3))).trans
              (by rw [pow_add]; exact mul_dvd_mul hK1d hL1d)
          · simp only [hmL, ↓reduceIte]
            exact K.pow_dvd_K_U0_D1_ne i hU hD1
      · simp only [hU, not_false_eq_true, ↓reduceIte]
        have h := K.pow_dvd_K_U1 i hU; simp only [show D.k i ≠ 0 by omega, ↓reduceIte] at h
        exact (pow_dvd_pow _ (by split_ifs <;> omega : (if D.k i = 2 then 1 else 3 + 2 * (D.k i - 3)) ≤ 2 * D.k i - 1)).trans h
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective (K.K1 * K.Lam1) (mul_ne_zero K.hK1_ne K.hLam1_ne) f hdvd
  rw [natDegree_mul K.hK1_ne K.hLam1_ne] at hle
  have hU := S.U_counts_ineqs
  have hZ : (2 * (K.dinCnt : ℤ) + (K.dmLCnt : ℤ) + (K.mLCnt : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) +
      (3 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
    have hrew : 2 * (K.dinCnt : ℤ) + (K.dmLCnt : ℤ) + (K.mLCnt : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) +
        (3 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
        ∑ i : Idx, (2 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
          2 * (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0) +
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
          (if K.isML i then 1 else 0) +
          (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          3 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          2 * ((D.k i - 3 : ℕ) : ℤ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dinCnt, dmLCnt, Nat.cast_add]; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    dsimp [f]
    by_cases hD1 : K.isD1 i
    · have hU' : S.isU0 i := K.isU0_of_D1_zero hD1
      have hg0 : K.g2t.eval (BinaryIRSProfile.domain i) = 0 := K.g2t_zero_of_D1_zero hD1
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, hD1, hU', hg0, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    · by_cases hU' : S.isU0 i <;> by_cases hg0 : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, hD1, hU', hg0, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or, ↓reduceIte] <;>
        (try split_ifs) <;> omega
  rw [← Nat.cast_sum] at hZ; omega

/-! #### Degree identities and Sylvester / minor degree bounds -/

lemma natDegree_p_eq : S.p.natDegree = S.D1.natDegree + K.p1.natDegree := by
  rw [K.hp_fac, natDegree_mul S.D2_ne_zero K.hp1_ne, ← S.D1_natDegree]

lemma natDegree_g1_eq : (D.gj 1).natDegree = 2 * K.K1.natDegree + K.g2t.natDegree := by
  rw [K.hg1_fac, natDegree_mul (mt (comp_X_sq_eq_zero_iff K.K1).mp K.hK1_ne) K.hg2t_ne, natDegree_comp_X_sq]

lemma natDegree_H1_eq : S.H1.natDegree = 4 * S.D1.natDegree + 2 * K.M0s.natDegree + K.g2t.natDegree := by
  have hM_ne := mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne
  rw [K.hH1_fac, natDegree_mul (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) hM_ne) K.hg2t_ne,
    natDegree_mul (pow_ne_zero 4 S.D1_ne_zero) hM_ne, natDegree_pow, natDegree_comp_X_sq]

lemma natDegree_ResY_eq :
    D.ResY.natDegree = 4 * S.D1.natDegree + 8 * K.Lam1.natDegree + 10 * K.M0s.natDegree + K.g2t.natDegree := by
  have hL_ne := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
  have hM_ne := mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne
  rw [K.hResY_fac,
    natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne)) K.hg2t_ne,
    natDegree_mul (mul_ne_zero (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne)) (pow_ne_zero 5 hM_ne),
    natDegree_mul (pow_ne_zero 4 S.D1_ne_zero) (pow_ne_zero 4 hL_ne),
    natDegree_pow, natDegree_pow, natDegree_pow, natDegree_comp_X_sq, natDegree_comp_X_sq]
  ring

lemma row338_bound :
    2 * (5 * S.p.natDegree - 2 * S.D1.natDegree + K.K1.natDegree + K.Lam1.natDegree) ≤
      (D.gj 2).natDegree + (D.gj 1).natDegree := by
  have hM21_ne : S.M21 ≠ 0 := by
    rw [K.hM21_fac]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne) K.hLam1_ne
  have hdeg_pM21 : (S.p * S.M21).natDegree = 5 * S.p.natDegree - 2 * S.D1.natDegree + K.K1.natDegree + K.Lam1.natDegree := by
    rw [natDegree_mul S.hp hM21_ne, K.hM21_fac,
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne) K.hLam1_ne,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne,
      natDegree_mul (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne),
      natDegree_pow, natDegree_pow, ← S.D1_natDegree]
    have hp := K.natDegree_p_eq; omega
  rw [← hdeg_pM21, S.p_mul_M21]
  have ht1 : 2 * (D.Cj 2 * D.Bj 1).natDegree ≤ (D.gj 2).natDegree + (D.gj 1).natDegree := by
    by_cases h0 : D.Cj 2 = 0 ∨ D.Bj 1 = 0
    · rcases h0 with h | h <;> simp [h]
    · push Not at h0
      have h1 := two_mul_natDegree_le_even_odd (D.Cj 2) (D.Bj 2) h0.1
      have h2 := two_mul_natDegree_add_one_le_even_odd (D.Cj 1) (D.Bj 1) h0.2
      have h3 := natDegree_mul_le (p := D.Cj 2) (q := D.Bj 1)
      unfold KerD45Data.gj at *; omega
  have ht2 : 2 * (D.Cj 1 * D.Bj 2).natDegree ≤ (D.gj 2).natDegree + (D.gj 1).natDegree := by
    by_cases h0 : D.Cj 1 = 0 ∨ D.Bj 2 = 0
    · rcases h0 with h | h <;> simp [h]
    · push Not at h0
      have h1 := two_mul_natDegree_le_even_odd (D.Cj 1) (D.Bj 1) h0.1
      have h2 := two_mul_natDegree_add_one_le_even_odd (D.Cj 2) (D.Bj 2) h0.2
      have h3 := natDegree_mul_le (p := D.Cj 1) (q := D.Bj 2)
      unfold KerD45Data.gj at *; omega
  have hadd := natDegree_add_le (D.Cj 2 * D.Bj 1) (D.Cj 1 * D.Bj 2)
  omega

lemma row339_bound :
    4 * (S.p.natDegree : ℤ) + 4 * (K.K1.natDegree : ℤ) + 4 * (K.Lam1.natDegree : ℤ) +
      8 * (S.R.natDegree : ℤ) - 8 * (S.D1.natDegree : ℤ) - 2 * ((D.gj 1).natDegree : ℤ) ≤
      2 * (D.W_F : ℤ) - 2 * (wY : ℤ) + 2 := by
  by_cases hR0 : S.R = 0
  · have hq0 : S.q = 0 := S.q_eq_zero_iff.mpr hR0
    have hD2_p : S.D1.natDegree = S.p.natDegree := by
      have hp1_u : IsUnit K.p1 := K.hp1_q1_cop.isUnit_of_dvd' dvd_rfl (by
        have hq10 : K.q1 = 0 := (mul_eq_zero.mp (K.hq_fac.symm.trans hq0)).resolve_left S.D2_ne_zero
        rw [hq10]; exact dvd_zero _)
      have hp1_0 := natDegree_eq_zero_of_isUnit hp1_u
      have := K.natDegree_p_eq; omega
    have h338 := K.row338_bound
    have hg2 := D.natDegree_gj_le 2
    have h5 := D.hWF_lo; have hw := D.hwY_pos
    rw [hR0, natDegree_zero]; omega
  · have hq_ne : S.q ≠ 0 := mt S.q_eq_zero_iff.mp hR0
    have hq1_ne : K.q1 ≠ 0 := fun h0 => hq_ne (by rw [K.hq_fac, h0, mul_zero])
    have hM10_ne : S.M10 ≠ 0 := by
      rw [K.hM10_fac]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq1_ne) K.hK1_ne) K.hLam1_ne
    have hq_deg : S.R.natDegree = S.D1.natDegree + K.q1.natDegree := by
      rw [← S.natDegree_q_eq_R, K.hq_fac, natDegree_mul S.D2_ne_zero hq1_ne, ← S.D1_natDegree]
    have hdeg : (S.p * S.M10).natDegree =
        S.p.natDegree + 2 * K.q1.natDegree + K.K1.natDegree + K.Lam1.natDegree := by
      rw [natDegree_mul S.hp hM10_ne, K.hM10_fac,
        natDegree_mul (mul_ne_zero (pow_ne_zero 2 hq1_ne) K.hK1_ne) K.hLam1_ne,
        natDegree_mul (pow_ne_zero 2 hq1_ne) K.hK1_ne, natDegree_pow]; ring
    have h2deg : 2 * (S.p * S.M10).natDegree ≤ D.W_F - wY + (D.gj 1).natDegree := by
      rw [S.p_mul_M10]
      have hB0 := D.two_mul_natDegree_Bj_le 0; have hC0 := D.two_mul_natDegree_Cj_le 0
      have h5 := D.hWF_lo; have hw := D.hwY_pos
      have ht1 : 2 * (D.Cj 1 * D.Bj 0).natDegree ≤ D.W_F - wY + (D.gj 1).natDegree := by
        by_cases hC1 : D.Cj 1 = 0
        · simp [hC1]
        · have := two_mul_natDegree_le_even_odd (D.Cj 1) (D.Bj 1) hC1
          have := natDegree_mul_le (p := D.Cj 1) (q := D.Bj 0)
          unfold KerD45Data.gj at *; omega
      have ht2 : 2 * (D.Cj 0 * D.Bj 1).natDegree ≤ D.W_F - wY + (D.gj 1).natDegree := by
        by_cases hB1 : D.Bj 1 = 0
        · simp [hB1]
        · have := two_mul_natDegree_add_one_le_even_odd (D.Cj 1) (D.Bj 1) hB1
          have := natDegree_mul_le (p := D.Cj 0) (q := D.Bj 1)
          unfold KerD45Data.gj at *; omega
      have hadd := natDegree_add_le (D.Cj 1 * D.Bj 0) (D.Cj 0 * D.Bj 1); omega
    have h5 := D.hWF_lo; have hw := D.hwY_pos; omega

lemma row340_bound :
    5 * (S.R.natDegree : ℤ) + 2 * (K.K1.natDegree : ℤ) + 2 * (K.Lam1.natDegree : ℤ) -
      4 * (S.D1.natDegree : ℤ) ≤ 2 * (D.W_F : ℤ) - 3 * (wY : ℤ) + 1 := by
  by_cases hR0 : S.R = 0
  · have hq0 : S.q = 0 := S.q_eq_zero_iff.mpr hR0
    have hD2_p : S.D1.natDegree = S.p.natDegree := by
      have hp1_u : IsUnit K.p1 := K.hp1_q1_cop.isUnit_of_dvd' dvd_rfl (by
        have hq10 : K.q1 = 0 := (mul_eq_zero.mp (K.hq_fac.symm.trans hq0)).resolve_left S.D2_ne_zero
        rw [hq10]; exact dvd_zero _)
      have hp1_0 := natDegree_eq_zero_of_isUnit hp1_u
      have := K.natDegree_p_eq; omega
    have hM21_ne : S.M21 ≠ 0 := by
      rw [K.hM21_fac]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne) K.hLam1_ne
    have hpM21 := S.natDegree_p_add_M21_le hM21_ne
    have hM21_deg : S.M21.natDegree = 2 * S.D1.natDegree + 4 * K.p1.natDegree + K.K1.natDegree + K.Lam1.natDegree := by
      rw [K.hM21_fac,
        natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne) K.hLam1_ne,
        natDegree_mul (mul_ne_zero (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne)) K.hK1_ne,
        natDegree_mul (pow_ne_zero 2 S.D2_ne_zero) (pow_ne_zero 4 K.hp1_ne),
        natDegree_pow, natDegree_pow, ← S.D1_natDegree]
    have h5 := D.hWF_lo; have hw := D.hwY_pos
    rw [hR0, natDegree_zero]; omega
  · have hq_ne : S.q ≠ 0 := mt S.q_eq_zero_iff.mp hR0
    have hq1_ne : K.q1 ≠ 0 := fun h0 => hq_ne (by rw [K.hq_fac, h0, mul_zero])
    have hM10_ne : S.M10 ≠ 0 := by
      rw [K.hM10_fac]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq1_ne) K.hK1_ne) K.hLam1_ne
    have hq_deg : S.R.natDegree = S.D1.natDegree + K.q1.natDegree := by
      rw [← S.natDegree_q_eq_R, K.hq_fac, natDegree_mul S.D2_ne_zero hq1_ne, ← S.D1_natDegree]
    have hRM10 := S.natDegree_R_mul_M10_le
    rw [natDegree_mul hR0 (mt (comp_X_sq_eq_zero_iff S.M10).mp hM10_ne), natDegree_comp_X_sq,
      K.hM10_fac, natDegree_mul (mul_ne_zero (pow_ne_zero 2 hq1_ne) K.hK1_ne) K.hLam1_ne,
      natDegree_mul (pow_ne_zero 2 hq1_ne) K.hK1_ne, natDegree_pow] at hRM10
    have h5 := D.hWF_lo; have hw := D.hwY_pos; omega

lemma q1_trichotomy :
    (S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1) ∨
    (S.H1.natDegree ≤ 4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree) ∨
    (S.H1.natDegree ≤ 4 * S.R.natDegree + (D.gj 2).natDegree) := by
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hg0 := D.natDegree_gj_le 0
  have hp_sq : (S.p.comp (X ^ 2)).natDegree = 2 * S.p.natDegree := natDegree_comp_X_sq S.p
  have ht1 : (S.p.comp (X ^ 2) ^ 4 * D.gj 0).natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 :=
    natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) hg0) |>.trans (by omega)
  have ht2 : (S.p.comp (X ^ 2) ^ 2 * S.R ^ 2 * D.gj 1).natDegree ≤ 4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) natDegree_pow_le)) le_rfl) |>.trans (by omega)
  have ht3 : (S.R ^ 4 * D.gj 2).natDegree ≤ 4 * S.R.natDegree + (D.gj 2).natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl)
  have hle : S.H1.natDegree ≤ max (max (8 * S.p.natDegree + D.W_F - wY + 1)
      (4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree))
      (4 * S.R.natDegree + (D.gj 2).natDegree) := by
    unfold KerD45Syzygy.H1
    exact (natDegree_add_le _ _).trans (max_le_max ((natDegree_add_le _ _).trans (max_le_max ht1 ht2)) ht3)
  rcases le_max_iff.mp hle with h12 | h3
  · rcases le_max_iff.mp h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-! #### Domain polynomials `M_0, N_1, S_hit3, H_rem, Q, S_g2, g2_rem, M_0_eff, S_K, H_K` -/

noncomputable def linProd (s : Finset Idx) : Fld[X] := ∏ i ∈ s, (X - C (BinaryIRSProfile.domain i))

lemma linProd_monic (s : Finset Idx) : (linProd s).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma linProd_ne (s : Finset Idx) : linProd s ≠ 0 := (linProd_monic s).ne_zero

lemma linProd_natDegree (s : Finset Idx) : (linProd s).natDegree = s.card := by
  unfold linProd; rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]; simp [natDegree_X_sub_C]

open Classical in
lemma linProd_rm (s : Finset Idx) (a : AlgebraicClosure Fld) :
    ((linProd s).map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a =
      if ∃ i ∈ s, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) then 1 else 0 := by
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  have hmap : (linProd s).map ι = ∏ i ∈ s, (X - C (ι (BinaryIRSProfile.domain i))) := by
    unfold linProd; rw [Polynomial.map_prod]; apply Finset.prod_congr rfl; intro i _; simp
  rw [hmap]; split_ifs with h
  · obtain ⟨i, hi, rfl⟩ := h
    rw [← Finset.mul_prod_erase _ _ hi, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr fun _ _ => X_sub_C_ne_zero _)), rootMultiplicity_X_sub_C, if_pos rfl]
    have h0 : (∏ j ∈ s.erase i, (X - C (ι (BinaryIRSProfile.domain j)))).rootMultiplicity
        (ι (BinaryIRSProfile.domain i)) = 0 := by
      apply rootMultiplicity_eq_zero_iff.mpr; intro hr; exfalso
      rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hr
      obtain ⟨j, hj, hje⟩ := hr
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hje
      exact (Finset.mem_erase.mp hj).1 (BinaryIRSProfile.domain.injective (ι.injective hje)).symm
    rw [h0, add_zero]
  · apply rootMultiplicity_eq_zero_iff.mpr; intro hr; exfalso
    rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨i, hi, hie⟩ := hr
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hie
    exact h ⟨i, hi, hie⟩

omit K in
noncomputable def I_M0 (_K : KerD45KData S) : Finset Idx := by
  classical exact Finset.univ.filter fun i => D.k i = 0 ∨ ¬ S.isU0 i
noncomputable def I_N1 : Finset Idx := by
  classical exact Finset.univ.filter fun i => (D.k i = 1 ∧ S.isU0 i) ∨ (K.isML i ∧ K.isD1 i)
noncomputable def I_hit3 : Finset Idx := by
  classical exact Finset.univ.filter fun i => 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ (K.isML i ∧ K.isD1 i)
noncomputable def I_g2 : Finset Idx := by
  classical exact Finset.univ.filter fun i => 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ K.isMbad i
noncomputable def I_M0eff : Finset Idx := by
  classical exact Finset.univ.filter fun i => D.k i ≤ 1 ∨ ¬ S.isU0 i ∨ K.isMbad i

noncomputable def M0 : Fld[X] := linProd K.I_M0
noncomputable def N1 : Fld[X] := linProd K.I_N1
noncomputable def Shit3 : Fld[X] := linProd K.I_hit3
noncomputable def Sg2 : Fld[X] := linProd K.I_g2
noncomputable def M0eff : Fld[X] := linProd K.I_M0eff

lemma M0_ne : K.M0 ≠ 0 := linProd_ne _
lemma N1_ne : K.N1 ≠ 0 := linProd_ne _
lemma Shit3_ne : K.Shit3 ≠ 0 := linProd_ne _
lemma Sg2_ne : K.Sg2 ≠ 0 := linProd_ne _
lemma M0eff_ne : K.M0eff ≠ 0 := linProd_ne _

lemma card_I_M0 : K.I_M0.card = D.n0 + (D.n1 - S.n1U) + (D.n2 - S.n2U) + (D.n3 - S.n3U) := by
  classical
  have hU := S.U_counts_ineqs
  have hZ : (K.I_M0.card : ℤ) = (D.n0 : ℤ) + ((D.n1 : ℤ) - (S.n1U : ℤ)) +
      ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) := by
    have h1 : (K.I_M0.card : ℤ) = ∑ i : Idx, (if D.k i = 0 ∨ ¬ S.isU0 i then (1 : ℤ) else 0) := by unfold I_M0; exact card_filter_univ_Z _ _
    have h2 : (D.n0 : ℤ) + ((D.n1 : ℤ) - (S.n1U : ℤ)) + ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) =
        ∑ i : Idx, ((if D.k i = 0 then (1 : ℤ) else 0) + (if D.k i = 1 then 1 else 0) - (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
          (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, or_true, or_false, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma card_I_N1 : K.I_N1.card = S.n1U + K.dmLCnt := by
  classical
  have hZ : (K.I_N1.card : ℤ) = (S.n1U : ℤ) + (K.dmLCnt : ℤ) := by
    have h1 : (K.I_N1.card : ℤ) = ∑ i : Idx, (if (D.k i = 1 ∧ S.isU0 i) ∨ (K.isML i ∧ K.isD1 i) then (1 : ℤ) else 0) := by unfold I_N1; exact card_filter_univ_Z _ _
    have h2 : (S.n1U : ℤ) + (K.dmLCnt : ℤ) = ∑ i : Idx, ((if D.k i = 1 ∧ S.isU0 i then (1 : ℤ) else 0) +
        (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) + (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dmLCnt, Nat.cast_add]; ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma card_I_hit3 : K.I_hit3.card = S.n2U + S.n3U - K.dmLCnt := by
  classical
  have hZ : (K.I_hit3.card : ℤ) = (S.n2U : ℤ) + (S.n3U : ℤ) - (K.dmLCnt : ℤ) := by
    have h1 : (K.I_hit3.card : ℤ) = ∑ i : Idx, (if 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ (K.isML i ∧ K.isD1 i) then (1 : ℤ) else 0) := by unfold I_hit3; exact card_filter_univ_Z _ _
    have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) - (K.dmLCnt : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) -
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) - (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dmLCnt, Nat.cast_add]; ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma card_I_g2 : K.I_g2.card = S.n2U + S.n3U - K.mbadCnt := by
  classical
  have hZ : (K.I_g2.card : ℤ) = (S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ) := by
    have h1 : (K.I_g2.card : ℤ) = ∑ i : Idx, (if 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ K.isMbad i then (1 : ℤ) else 0) := by unfold I_g2; exact card_filter_univ_Z _ _
    have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) -
          (if K.isMbad i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      simp only [isMbad, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma card_I_M0eff : K.I_M0eff.card = D.n0 + D.n1 + (D.n2 - S.n2U) + (D.n3 - S.n3U) + K.mbadCnt := by
  classical
  have hU := S.U_counts_ineqs
  have hZ : (K.I_M0eff.card : ℤ) = (D.n0 : ℤ) + (D.n1 : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) +
      ((D.n3 : ℤ) - (S.n3U : ℤ)) + (K.mbadCnt : ℤ) := by
    have h1 : (K.I_M0eff.card : ℤ) = ∑ i : Idx, (if D.k i ≤ 1 ∨ ¬ S.isU0 i ∨ K.isMbad i then (1 : ℤ) else 0) := by unfold I_M0eff; exact card_filter_univ_Z _ _
    have h2 : (D.n0 : ℤ) + (D.n1 : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) + (K.mbadCnt : ℤ) =
        ∑ i : Idx, ((if D.k i = 0 then (1 : ℤ) else 0) + (if D.k i = 1 then 1 else 0) +
          (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
          (if K.isMbad i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [h1, h2]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      simp only [isMbad, hU, hg, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  omega

lemma Ndom_eq_M0_N1_Shit3 : Ndom = K.M0 * K.N1 * K.Shit3 := by
  classical
  have hd1 : Disjoint K.I_M0 K.I_N1 := Finset.disjoint_filter.mpr fun i _ h1 h2 => by
    unfold isML at h2; rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> first | omega | exact h1 h2.2 | exact h1 h2.1.2.1
  have hd2 : Disjoint (K.I_M0 ∪ K.I_N1) K.I_hit3 := Finset.disjoint_left.mpr fun i h1 h2 => by
    simp only [I_M0, I_N1, I_hit3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases h1 with (h1 | h1) | (h1 | h1)
    · omega
    · exact h1 h2.2.1
    · omega
    · exact h2.2.2 h1
  have hun : K.I_M0 ∪ K.I_N1 ∪ K.I_hit3 = Finset.univ := by
    ext i; simp only [I_M0, I_N1, I_hit3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases hU : S.isU0 i
    · by_cases hk0 : D.k i = 0
      · left; left; left; exact hk0
      · by_cases hk1 : D.k i = 1
        · left; right; left; exact ⟨hk1, hU⟩
        · by_cases hm : K.isML i ∧ K.isD1 i
          · left; right; right; exact hm
          · right; exact ⟨by omega, hU, hm⟩
    · left; left; right; exact hU
  unfold Ndom M0 N1 Shit3 linProd
  rw [← Finset.prod_union hd1, ← Finset.prod_union hd2, hun]

lemma Ndom_eq_M0eff_Sg2 : Ndom = K.M0eff * K.Sg2 := by
  classical
  have hd : Disjoint K.I_M0eff K.I_g2 := Finset.disjoint_filter.mpr fun i _ h1 h2 => by
    rcases h1 with h1 | h1 | h1
    · omega
    · exact h1 h2.2.1
    · exact h2.2.2 h1
  have hun : K.I_M0eff ∪ K.I_g2 = Finset.univ := by
    ext i; simp only [I_M0eff, I_g2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases hU : S.isU0 i
    · by_cases hk1 : D.k i ≤ 1
      · left; left; exact hk1
      · by_cases hmb : K.isMbad i
        · left; right; right; exact hmb
        · right; exact ⟨by omega, hU, hmb⟩
    · left; right; left; exact hU
  unfold Ndom M0eff Sg2 linProd
  rw [← Finset.prod_union hd, hun]

lemma Sg2_dvd_g2t : K.Sg2 ∣ K.g2t := by
  classical
  unfold Sg2 linProd
  have hpw : Pairwise fun i j : Idx => IsCoprime (X - C (BinaryIRSProfile.domain i)) (X - C (BinaryIRSProfile.domain j)) :=
    fun i j hij => (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr fun hd => by
      have h0 := dvd_iff_isRoot.mp hd; simp [IsRoot] at h0
      exact hij (BinaryIRSProfile.domain.injective (sub_eq_zero.mp h0))
  apply Finset.prod_dvd_of_coprime (fun i _ j _ hij => hpw hij)
  intro i hi
  unfold I_g2 at hi; rw [Finset.mem_filter] at hi; rcases hi with ⟨_, hi⟩
  unfold isMbad at hi
  apply dvd_iff_isRoot.mpr; by_contra hne; exact hi.2.2 ⟨hi.1, hi.2.1, hne⟩

lemma N1_Shit3_cube_dvd_Hraw : K.N1 * K.Shit3 ^ 3 ∣ K.M0s.comp (X ^ 2) * K.g2t := by
  classical
  have hdisj : Disjoint K.I_N1 K.I_hit3 := Finset.disjoint_filter.mpr fun i _ h1 h2 => by
    rcases h1 with ⟨hk1, _⟩ | h1
    · have := h2.1; omega
    · exact h2.2.2 h1
  have hpw : Pairwise fun i j : Idx => IsCoprime (X - C (BinaryIRSProfile.domain i)) (X - C (BinaryIRSProfile.domain j)) :=
    fun i j hij => (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr fun hd => by
      have h0 := dvd_iff_isRoot.mp hd; simp [IsRoot] at h0
      exact hij (BinaryIRSProfile.domain.injective (sub_eq_zero.mp h0))
  have hcop : IsCoprime K.N1 (K.Shit3 ^ 3) := by
    apply IsCoprime.pow_right; unfold N1 Shit3 linProd
    exact IsCoprime.prod_left fun i hi => IsCoprime.prod_right fun j hj =>
      hpw (fun heq => by subst heq; exact Finset.disjoint_left.mp hdisj hi hj)
  apply hcop.mul_dvd
  · unfold N1 linProd
    apply Finset.prod_dvd_of_coprime (fun i _ j _ hij => hpw hij)
    intro i hi
    unfold I_N1 at hi; rw [Finset.mem_filter] at hi; rcases hi with ⟨_, hi⟩
    rcases hi with ⟨hk1, hU⟩ | ⟨hmL, _⟩
    · by_cases hD1 : K.isD1 i
      · exact dvd_mul_of_dvd_right (dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1)) _
      · have hH1d : X - C (BinaryIRSProfile.domain i) ∣ S.H1 := by
          have := S.pow_dvd_H1_of_isU0 i hU; rwa [hk1, pow_one] at this
        rw [K.hH1_fac, mul_assoc] at hH1d
        have hcopD : IsCoprime (X - C (BinaryIRSProfile.domain i)) (S.D1 ^ 4) :=
          ((Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hD1)).pow_right
        exact hcopD.dvd_of_dvd_mul_left hH1d
    · exact dvd_mul_of_dvd_right (dvd_iff_isRoot.mpr hmL.2.2.1) _
  · unfold Shit3 linProd; rw [← Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime (fun i _ j _ hij => (hpw hij).pow)
    intro i hi
    unfold I_hit3 at hi; rw [Finset.mem_filter] at hi; rcases hi with ⟨_, hi⟩
    by_cases hD1 : K.isD1 i
    · have hg0 := K.g2t_zero_of_D1_zero hD1
      have hM0 : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 := by
        by_contra hne; exact hi.2.2 ⟨⟨hi.1, hi.2.1, hg0, hne⟩, hD1⟩
      rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one]
      exact mul_dvd_mul ((pow_dvd_comp_X_sq_iff K.M0s (BinaryIRSProfile.domain i) 1).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hM0))
        (dvd_iff_isRoot.mpr hg0)
    · have hH1d := (pow_dvd_pow (X - C (BinaryIRSProfile.domain i)) (by have := hi.1; omega : 3 ≤ 2 * D.k i - 1)).trans
        (S.pow_dvd_H1_of_isU0 i hi.2.1)
      rw [K.hH1_fac, mul_assoc] at hH1d
      have hcopD : IsCoprime ((X - C (BinaryIRSProfile.domain i)) ^ 3) (S.D1 ^ 4) :=
        (((Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hD1)).pow_left).pow_right
      exact hcopD.dvd_of_dvd_mul_left hH1d

noncomputable def g2rem : Fld[X] := Classical.choose K.Sg2_dvd_g2t
noncomputable def Hrem : Fld[X] := Classical.choose K.N1_Shit3_cube_dvd_Hraw
noncomputable def Qpoly : Fld[X] := K.M0 ^ 3 * K.N1 ^ 2 * D.gj 2

lemma g2t_eq_Sg2_mul_g2rem : K.g2t = K.Sg2 * K.g2rem := Classical.choose_spec K.Sg2_dvd_g2t
lemma Hraw_eq_N1_Shit3_Hrem : K.M0s.comp (X ^ 2) * K.g2t = K.N1 * K.Shit3 ^ 3 * K.Hrem :=
  Classical.choose_spec K.N1_Shit3_cube_dvd_Hraw

lemma g2rem_ne : K.g2rem ≠ 0 := by intro h0; apply K.hg2t_ne; rw [K.g2t_eq_Sg2_mul_g2rem, h0, mul_zero]
lemma Hrem_ne : K.Hrem ≠ 0 := by
  intro h0
  have h1 := K.Hraw_eq_N1_Shit3_Hrem; rw [h0, mul_zero] at h1
  exact mul_ne_zero (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne h1
lemma Qpoly_ne : K.Qpoly ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero 3 K.M0_ne) (pow_ne_zero 2 K.N1_ne)) D.g2_ne_zero

lemma natDegree_g2rem : K.g2rem.natDegree = K.g2t.natDegree - (S.n2U + S.n3U - K.mbadCnt) := by
  have h := congrArg Polynomial.natDegree K.g2t_eq_Sg2_mul_g2rem
  rw [natDegree_mul K.Sg2_ne K.g2rem_ne] at h
  unfold Sg2 at h; rw [linProd_natDegree, K.card_I_g2] at h; omega

lemma natDegree_Hrem :
    K.Hrem.natDegree = 2 * K.M0s.natDegree + K.g2t.natDegree - (S.n1U + K.dmLCnt) - 3 * (S.n2U + S.n3U - K.dmLCnt) := by
  have h := congrArg Polynomial.natDegree K.Hraw_eq_N1_Shit3_Hrem
  rw [natDegree_mul (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne, natDegree_comp_X_sq,
    natDegree_mul (mul_ne_zero K.N1_ne (pow_ne_zero 3 K.Shit3_ne)) K.Hrem_ne,
    natDegree_mul K.N1_ne (pow_ne_zero 3 K.Shit3_ne), natDegree_pow] at h
  unfold N1 Shit3 at h; rw [linProd_natDegree, linProd_natDegree, K.card_I_N1, K.card_I_hit3] at h
  omega

/-- Exact squarefree decomposition `M0eff * D.gj 2 * g2rem = S_K^2 * H_K` with `Squarefree H_K`! -/
noncomputable def sfK :=
  exists_sq_mul_squarefree (K.M0eff * D.gj 2 * K.g2rem)
    (mul_ne_zero (mul_ne_zero K.M0eff_ne D.g2_ne_zero) K.g2rem_ne)

noncomputable def SK : Fld[X] := Classical.choose K.sfK
noncomputable def HK : Fld[X] := Classical.choose (Classical.choose_spec K.sfK)

lemma HK_decomp : K.M0eff * D.gj 2 * K.g2rem = K.SK ^ 2 * K.HK := (Classical.choose_spec (Classical.choose_spec K.sfK)).1
lemma HK_sqfree : Squarefree K.HK := (Classical.choose_spec (Classical.choose_spec K.sfK)).2
lemma SK_ne : K.SK ≠ 0 := by
  intro h0; apply mul_ne_zero (mul_ne_zero K.M0eff_ne D.g2_ne_zero) K.g2rem_ne
  rw [K.HK_decomp, h0, zero_pow (by norm_num), zero_mul]
lemma HK_ne : K.HK ≠ 0 := K.HK_sqfree.ne_zero

/-- Exact Wronskian identity for `H_K`:
`SK^2 * (C c0 * HK + Ndom * HK') = M0eff^2 * D1^6 * p1(X^2)^5 * Lam1(X^2)`! -/
theorem HK_wronskian {c0 : Fld} (hd1 : Ndom.derivative = C c0) :
    K.SK ^ 2 * (C c0 * K.HK + Ndom * K.HK.derivative) =
      K.M0eff ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) := by
  have h1 : Ndom * (K.g2t * D.gj 2) = K.Sg2 ^ 2 * K.SK ^ 2 * K.HK := by
    calc Ndom * (K.g2t * D.gj 2) = (K.M0eff * K.Sg2) * (K.Sg2 * K.g2rem * D.gj 2) := by
          rw [← K.Ndom_eq_M0eff_Sg2, ← K.g2t_eq_Sg2_mul_g2rem]
      _ = K.Sg2 ^ 2 * (K.M0eff * D.gj 2 * K.g2rem) := by ring
      _ = K.Sg2 ^ 2 * K.SK ^ 2 * K.HK := by rw [K.HK_decomp]; ring
  have hdiff := congrArg Polynomial.derivative h1
  rw [derivative_mul, hd1, K.hwr_g2t_g2,
    show K.Sg2 ^ 2 * K.SK ^ 2 * K.HK = (K.Sg2 * K.SK) ^ 2 * K.HK by ring,
    derivative_mul, char2_derivative_sq, zero_mul, zero_add] at hdiff
  have hm := congrArg (· * Ndom) hdiff
  have h2 : C c0 * (K.g2t * D.gj 2) * Ndom = K.Sg2 ^ 2 * K.SK ^ 2 * (C c0 * K.HK) := by
    calc C c0 * (K.g2t * D.gj 2) * Ndom = C c0 * (Ndom * (K.g2t * D.gj 2)) := by ring
      _ = K.Sg2 ^ 2 * K.SK ^ 2 * (C c0 * K.HK) := by rw [h1]; ring
  have h3 : Ndom * (S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2)) * Ndom =
      K.Sg2 ^ 2 * (K.M0eff ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2)) := by
    rw [K.Ndom_eq_M0eff_Sg2]; ring
  apply mul_left_cancel₀ (pow_ne_zero 2 K.Sg2_ne)
  have hz := CharTwo.add_self_eq_zero (K.Sg2 ^ 2 * K.SK ^ 2 * (C c0 * K.HK))
  rw [add_mul, h2, h3] at hm
  linear_combination -hm + hz

/-- Exact bridge `Shit3^4 * (Hrem * Qpoly) = (M0 * sqrtPoly M0s)^2 * Ndom * (g2t * D.gj 2)`
and its Wronskian consequence! -/
theorem Hrem_Q_bridge :
    K.Shit3 ^ 4 * (K.Hrem * K.Qpoly) = (K.M0 * sqrtPoly K.M0s) ^ 2 * Ndom * (K.g2t * D.gj 2) := by
  apply mul_left_cancel₀ K.N1_ne
  have hsq : (sqrtPoly K.M0s) ^ 2 = K.M0s.comp (X ^ 2) := sqrtPoly_sq K.M0s
  calc K.N1 * (K.Shit3 ^ 4 * (K.Hrem * K.Qpoly))
      = (K.N1 * K.Shit3 ^ 3 * K.Hrem) * (K.M0 ^ 3 * K.N1 ^ 2 * K.Shit3 * D.gj 2) := by unfold Qpoly; ring
    _ = (K.M0s.comp (X ^ 2) * K.g2t) * (K.M0 ^ 3 * K.N1 ^ 2 * K.Shit3 * D.gj 2) := by rw [← K.Hraw_eq_N1_Shit3_Hrem]
    _ = K.N1 * ((K.M0 * sqrtPoly K.M0s) ^ 2 * (K.M0 * K.N1 * K.Shit3) * (K.g2t * D.gj 2)) := by rw [← hsq]; ring
    _ = K.N1 * ((K.M0 * sqrtPoly K.M0s) ^ 2 * Ndom * (K.g2t * D.gj 2)) := by rw [← K.Ndom_eq_M0_N1_Shit3]

theorem Hrem_Q_wronskian {c0 : Fld} (hd1 : Ndom.derivative = C c0) :
    K.Shit3 ^ 4 * (Ndom * (K.Hrem.derivative * K.Qpoly + K.Hrem * K.Qpoly.derivative) + C c0 * K.Hrem * K.Qpoly) =
      (K.M0 * sqrtPoly K.M0s * Ndom) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) := by
  have h1 := K.Hrem_Q_bridge
  have hdiff := congrArg Polynomial.derivative h1
  rw [derivative_mul, char2_derivative_pow_four, zero_mul, zero_add, derivative_mul,
    mul_assoc ((K.M0 * sqrtPoly K.M0s) ^ 2), derivative_mul, char2_derivative_sq, zero_mul, zero_add,
    derivative_mul, hd1, K.hwr_g2t_g2] at hdiff
  have hm := congrArg (· * Ndom) hdiff
  have h2 : (K.M0 * sqrtPoly K.M0s) ^ 2 * (C c0 * (K.g2t * D.gj 2)) * Ndom =
      K.Shit3 ^ 4 * (C c0 * K.Hrem * K.Qpoly) := by
    calc (K.M0 * sqrtPoly K.M0s) ^ 2 * (C c0 * (K.g2t * D.gj 2)) * Ndom
        = C c0 * ((K.M0 * sqrtPoly K.M0s) ^ 2 * Ndom * (K.g2t * D.gj 2)) := by ring
      _ = C c0 * (K.Shit3 ^ 4 * (K.Hrem * K.Qpoly)) := by rw [← h1]
      _ = K.Shit3 ^ 4 * (C c0 * K.Hrem * K.Qpoly) := by ring
  have hz := CharTwo.add_self_eq_zero (K.Shit3 ^ 4 * (C c0 * K.Hrem * K.Qpoly))
  simp only [mul_add, add_mul] at hm
  rw [h2] at hm
  linear_combination hm + hz

/-- Exact `ODE_fail` 4-term identity for `(Hrem, Qpoly)` at ANY `y0 : Fld`! -/
theorem Hrem_Q_ode_fail_id (y0 : Fld) :
    let Uy0 := S.p.comp (X ^ 2) * C y0 + S.R
    let U1_y0 := S.D1 * K.p1.comp (X ^ 2) * C y0 + K.R1
    let R_raw := S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 2 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      Uy0 ^ 2 * D.gj 1
    K.Hrem * Ndom ^ 3 + (sqrtPoly K.p1) ^ 4 * (K.M0 ^ 3 * K.N1 ^ 2 * R_raw) = K.Qpoly * U1_y0 ^ 4 := by
  intro Uy0 U1_y0 R_raw
  have hp4 : (sqrtPoly K.p1) ^ 4 = K.p1.comp (X ^ 2) ^ 2 := by
    calc (sqrtPoly K.p1) ^ 4 = ((sqrtPoly K.p1) ^ 2) ^ 2 := by ring
      _ = K.p1.comp (X ^ 2) ^ 2 := by rw [sqrtPoly_sq]
  have h1 := congrArg (· * (K.M0 ^ 3 * K.N1 ^ 2)) (K.h4term_y0 y0)
  have ht1 : K.M0s.comp (X ^ 2) * K.g2t * (K.M0 ^ 3 * K.N1 ^ 2) = K.Hrem * Ndom ^ 3 := by
    rw [K.Hraw_eq_N1_Shit3_Hrem, K.Ndom_eq_M0_N1_Shit3]; ring
  rw [add_mul, add_mul, ht1] at h1
  rw [hp4]; unfold Qpoly; dsimp [R_raw]
  linear_combination h1

end KerD45KData

/-! ### Part 3: Pointwise 15-Column `Step15Pt` Bridge, `B1_0C`, `ODE_holds`, and `ODE_fail` -/

namespace KerD45KData

variable {D : KerD45Data} {S : KerD45Syzygy D} (K : KerD45KData S)

/-- Classify any `a ∈ AlgebraicClosure Fld` into its exact `Step15Pt` type! -/
noncomputable def ptOf (a : AlgebraicClosure Fld) : Step15Pt := by
  classical
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  exact if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then
    let i := Classical.choose h
    if D.k i = 0 then .k0
    else if D.k i = 1 then if S.isU0 i then .k1U else .k0
    else if ¬ S.isU0 i then .k2noU
    else if D.k i = 2 then
      if K.isNorm i then .k2U else if K.isML i then .k2U_mL else .k2U_mb
    else
      if K.isNorm i then .k3U else if K.isML i then .k3U_mL else .k3U_mb
  else .out

open Classical in
lemma ptOf_dom (i : Idx) :
    K.ptOf (algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i)) =
      if D.k i = 0 then .k0
      else if D.k i = 1 then if S.isU0 i then .k1U else .k0
      else if ¬ S.isU0 i then .k2noU
      else if D.k i = 2 then
        if K.isNorm i then .k2U else if K.isML i then .k2U_mL else .k2U_mb
      else
        if K.isNorm i then .k3U else if K.isML i then .k3U_mL else .k3U_mb := by
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  unfold ptOf
  have hex : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j) := ⟨i, rfl⟩
  rw [dif_pos hex]
  have hch : Classical.choose hex = i :=
    BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec hex).symm)
  rw [hch]

lemma ptOf_out {a : AlgebraicClosure Fld}
    (h : ¬ ∃ i : Idx, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i)) :
    K.ptOf a = .out := by
  classical unfold ptOf; rw [dif_neg h]

private lemma ptOf_dom_spec (i : Idx) :
    let pt := K.ptOf (algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i))
    (pt = .k1U → D.k i = 1 ∧ S.isU0 i) ∧
    (pt = .k2noU → 2 ≤ D.k i ∧ ¬ S.isU0 i) ∧
    (pt = .k2U → D.k i = 2 ∧ K.isNorm i) ∧
    (pt = .k2U_mL → D.k i = 2 ∧ K.isML i) ∧
    (pt = .k2U_mb → D.k i = 2 ∧ K.isMbad i) ∧
    (pt = .k3U → 3 ≤ D.k i ∧ K.isNorm i) ∧
    (pt = .k3U_mL → 3 ≤ D.k i ∧ K.isML i) ∧
    (pt = .k3U_mb → 3 ≤ D.k i ∧ K.isMbad i) := by
  classical
  dsimp only; rw [K.ptOf_dom i]
  by_cases hk0 : D.k i = 0
  · simp [hk0]
  · by_cases hk1 : D.k i = 1
    · by_cases hU : S.isU0 i <;> simp [hk0, hk1, hU]
    · by_cases hU : S.isU0 i
      · by_cases hk2 : D.k i = 2
        · by_cases hn : K.isNorm i
          · simp [hk0, hk1, hU, hk2, hn]
          · by_cases hmL : K.isML i
            · simp [hk0, hk1, hU, hk2, hn, hmL]
            · have hmb : K.isMbad i := by
                refine ⟨by omega, hU, ?_⟩
                intro hg; by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
                · exact hn ⟨by omega, hU, hg, hm⟩
                · exact hmL ⟨by omega, hU, hg, hm⟩
              simp [hk0, hk1, hU, hk2, hn, hmL, hmb]
        · have hk3 : 3 ≤ D.k i := by omega
          by_cases hn : K.isNorm i
          · simp [hk0, hk1, hU, hk2, hk3, hn]
          · by_cases hmL : K.isML i
            · simp [hk0, hk1, hU, hk2, hk3, hn, hmL]
            · have hmb : K.isMbad i := by
                refine ⟨by omega, hU, ?_⟩
                intro hg; by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
                · exact hn ⟨by omega, hU, hg, hm⟩
                · exact hmL ⟨by omega, hU, hg, hm⟩
              simp [hk0, hk1, hU, hk2, hk3, hn, hmL, hmb]
      · have hk2 : 2 ≤ D.k i := by omega
        simp [hk0, hk1, hU, hk2]

-- Local 15-column parameter tuple at `a ∈ AlgebraicClosure Fld`.
omit K in
noncomputable def L0_l (_K : KerD45KData S) (a : AlgebraicClosure Fld) : ℕ := by
  classical
  exact if h : ∃ i : Idx, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) then
    let i := Classical.choose h
    if 3 ≤ D.k i ∧ S.isU0 i then 2 * (D.k i - 3) else 0
  else 0

omit K in
noncomputable def LnoU_l (_K : KerD45KData S) (a : AlgebraicClosure Fld) : ℕ := by
  classical
  exact if h : ∃ i : Idx, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) then
    let i := Classical.choose h
    if 3 ≤ D.k i ∧ ¬ S.isU0 i then 2 * (D.k i - 3) else 0
  else 0

noncomputable def a1_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.p1.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2)

omit K in
noncomputable def d2_l (_K : KerD45KData S) (a : AlgebraicClosure Fld) : ℕ :=
  (S.D1.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

noncomputable def muRaw_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.M0s.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2)

noncomputable def muEx_l (a : AlgebraicClosure Fld) : ℕ :=
  K.muRaw_l a - muSub (K.ptOf a)

noncomputable def lam_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.Lam1.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2)

noncomputable def g_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.SK.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

noncomputable def b_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.HK.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

noncomputable def e1_l (a : AlgebraicClosure Fld) : ℕ :=
  (K.g2rem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

omit K in
noncomputable def c_l (_K : KerD45KData S) (a : AlgebraicClosure Fld) : ℕ :=
  ((D.gj 2).map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a

lemma M0eff_rm_eq_mVal (a : AlgebraicClosure Fld) :
    ((K.M0eff.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a) = (K.ptOf a).mVal := by
  classical
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  unfold M0eff; rw [linProd_rm]
  by_cases h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
  · rcases h with ⟨i, rfl⟩
    rw [K.ptOf_dom i]
    have hmem : (∃ j ∈ K.I_M0eff, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) ↔ i ∈ K.I_M0eff := by
      constructor
      · rintro ⟨j, hj, heq⟩; have := BinaryIRSProfile.domain.injective (ι.injective heq); rwa [this]
      · intro hi; exact ⟨i, hi, rfl⟩
    rw [if_congr hmem rfl rfl]
    have hmem2 : i ∈ K.I_M0eff ↔ D.k i ≤ 1 ∨ ¬ S.isU0 i ∨ K.isMbad i := by
      unfold I_M0eff; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
    rw [if_congr hmem2 rfl rfl]
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, isMbad, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, or_true, or_false, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] <;> omega
  · rw [K.ptOf_out h, if_neg (fun h' => by rcases h' with ⟨i, _, hi⟩; exact h ⟨i, hi⟩)]
    rfl

lemma Sg2_rm_eq (a : AlgebraicClosure Fld) :
    ((K.Sg2.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a) = (K.ptOf a).nu - (K.ptOf a).mVal := by
  classical
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  unfold Sg2; rw [linProd_rm]
  by_cases h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
  · rcases h with ⟨i, rfl⟩
    rw [K.ptOf_dom i]
    have hmem : (∃ j ∈ K.I_g2, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) ↔ i ∈ K.I_g2 := by
      constructor
      · rintro ⟨j, hj, heq⟩; have := BinaryIRSProfile.domain.injective (ι.injective heq); rwa [this]
      · intro hi; exact ⟨i, hi, rfl⟩
    rw [if_congr hmem rfl rfl]
    have hmem2 : i ∈ K.I_g2 ↔ 2 ≤ D.k i ∧ S.isU0 i ∧ ¬ K.isMbad i := by
      unfold I_g2; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
    rw [if_congr hmem2 rfl rfl]
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, isMbad, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] <;> omega
  · rw [K.ptOf_out h, if_neg (fun h' => by rcases h' with ⟨i, _, hi⟩; exact h ⟨i, hi⟩)]; rfl

lemma d2_l_le_one (a : AlgebraicClosure Fld) : K.d2_l a ≤ 1 := by
  unfold d2_l KerD45Syzygy.D1
  rw [rootMultiplicity_sqrtPoly_map S.D2 S.D2_ne_zero a]
  exact rootMultiplicity_map_le_one_of_squarefree S.D2_squarefree (a ^ 2)

lemma v_Q_sub_Hrem (a : AlgebraicClosure Fld) :
    ((K.Qpoly.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
    ((K.Hrem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) =
      (K.c_l a : ℤ) - (K.e1_l a : ℤ) + 2 * ((K.ptOf a).nu : ℤ) + ((K.ptOf a).mVal : ℤ) -
        2 * (K.muRaw_l a : ℤ) := by
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  have hQ_rm : (K.Qpoly.map ι).rootMultiplicity a =
      3 * (K.M0.map ι).rootMultiplicity a + 2 * (K.N1.map ι).rootMultiplicity a + K.c_l a := by
    have hM0E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0_ne
    have hN1E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne
    have hg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
    unfold Qpoly c_l
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
      rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hM0E) (pow_ne_zero 2 hN1E)) hg2E),
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 3 hM0E) (pow_ne_zero 2 hN1E)),
      rootMultiplicity_pow_eq' _ hM0E 3 a, rootMultiplicity_pow_eq' _ hN1E 2 a]
  have hH_rm : (K.N1.map ι).rootMultiplicity a + 3 * (K.Shit3.map ι).rootMultiplicity a +
      (K.Hrem.map ι).rootMultiplicity a = 2 * K.muRaw_l a + ((K.ptOf a).nu - (K.ptOf a).mVal) + K.e1_l a := by
    have hN1E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne
    have hS3E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Shit3_ne
    have hHrE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Hrem_ne
    have hMcE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne)
    have hg2tE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.hg2t_ne
    have hSg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Sg2_ne
    have hg2rE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.g2rem_ne
    have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.Hraw_eq_N1_Shit3_Hrem
    simp only [Polynomial.map_mul, Polynomial.map_pow] at h1
    rw [rootMultiplicity_mul (mul_ne_zero hMcE hg2tE),
      rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hN1E (pow_ne_zero 3 hS3E)) hHrE),
      rootMultiplicity_mul (mul_ne_zero hN1E (pow_ne_zero 3 hS3E)),
      rootMultiplicity_pow_eq' _ hS3E 3 a,
      rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne a] at h1
    have h2 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.g2t_eq_Sg2_mul_g2rem
    rw [Polynomial.map_mul, rootMultiplicity_mul (mul_ne_zero hSg2E hg2rE), K.Sg2_rm_eq a] at h2
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [h2] at h1; rw [hι] at h1 ⊢; unfold muRaw_l e1_l; omega
  have hNdom_rm : (K.M0.map ι).rootMultiplicity a + (K.N1.map ι).rootMultiplicity a +
      (K.Shit3.map ι).rootMultiplicity a = (K.ptOf a).nu := by
    have hM0E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0_ne
    have hN1E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne
    have hS3E := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Shit3_ne
    have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.Ndom_eq_M0_N1_Shit3
    simp only [Polynomial.map_mul] at h1
    rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hM0E hN1E) hS3E),
      rootMultiplicity_mul (mul_ne_zero hM0E hN1E)] at h1
    have hN_eq : (Ndom.map ι).rootMultiplicity a = (K.ptOf a).nu := by
      unfold Ndom; rw [show (∏ i : Idx, (X - C (BinaryIRSProfile.domain i))) = linProd Finset.univ from rfl, linProd_rm]
      by_cases h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
      · rcases h with ⟨i, rfl⟩
        rw [if_pos ⟨i, Finset.mem_univ i, rfl⟩, K.ptOf_dom i]
        split_ifs <;> rfl
      · rw [if_neg (fun h' => by rcases h' with ⟨i, _, hi⟩; exact h ⟨i, hi⟩), K.ptOf_out h]; rfl
    omega
  have hm_le_nu : (K.ptOf a).mVal ≤ (K.ptOf a).nu := by cases K.ptOf a <;> decide
  have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
  rw [hι] at hQ_rm hH_rm hNdom_rm
  omega

/-- Master local-hypothesis bundle at `a ∈ AlgebraicClosure Fld` for all 15-col STEP theorems! -/
lemma local_step15_core (a : AlgebraicClosure Fld) :
    let pt := K.ptOf a
    let L0 := K.L0_l a
    let LnoU := K.LnoU_l a
    let a1 := K.a1_l a
    let d2 := K.d2_l a
    let mu := K.muEx_l a
    let lam := K.lam_l a
    let g := K.g_l a
    let b := K.b_l a
    let e1 := K.e1_l a
    let c := K.c_l a
    d2 ≤ 1 ∧ b ≤ 1 ∧ L0 % 2 = 0 ∧ LnoU % 2 = 0 ∧
    (0 < L0 → pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb) ∧
    (0 < LnoU → pt = .k2noU) ∧
    ((pt = .k2noU ∨ pt = .k2U_mb ∨ pt = .k3U_mb) → d2 = 0) ∧
    ((pt = .k2U ∨ pt = .k2U_mL ∨ pt = .k2U_mb ∨ pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb ∨ pt = .k1U) → d2 = 0 → a1 = 0) ∧
    ((pt = .k2U_mL ∨ pt = .k3U_mL) → mu = 0) ∧
    (pt = .k2noU → (LnoU = 0 → 2 ≤ lam + mu) ∧ (0 < LnoU → 4 + LnoU ≤ lam + mu)) ∧
    (pt = .k2U_mL → 1 ≤ lam) ∧
    (pt = .k3U → 2 + L0 ≤ lam + mu) ∧
    (pt = .k3U_mL → 3 + L0 ≤ lam) ∧
    (pt = .k3U_mb → 1 + L0 / 2 ≤ mu) ∧
    (pt = .k1U → (d2 = 1 ∨ mu = 0) → 1 ≤ e1) ∧
    ((pt = .k2U_mL ∨ pt = .k3U_mL) → d2 = 0 → 2 ≤ e1) ∧
    (g ≤ pt.mVal + lam + 3 * d2 + 5 * a1) ∧
    (c + e1 + pt.mVal = 2 * g + b) ∧
    (pt.mbad = 0 → pt.vChat mu e1 c =
      ((K.Qpoly.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
      ((K.Hrem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ)) ∧
    (pt.mbad = 1 → (c : ℤ) - (e1 : ℤ) - 1 - 2 * (mu : ℤ) =
      ((K.Qpoly.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
      ((K.Hrem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ)) ∧
    (1 ≤ a1 ∨ 1 ≤ d2 ∨ pt = .k2noU →
      let t1 := 8 * a1 + 4 * d2 + 3 * pt.mVal + pt.vc0 d2 e1 c L0 LnoU
      let t2 := 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + 3 * pt.mVal + e1
      let t3 := pt.t3 d2 mu e1
      let t4 := c + 3 * pt.mVal
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  obtain ⟨c0, c1, L, hc0, _, _, _, _, hd1, _, _, _⟩ := Ndom_decomp
  intro pt L0 LnoU a1 d2 mu lam g b e1 c
  have hd2_le : d2 ≤ 1 := K.d2_l_le_one a
  have hb_le : b ≤ 1 := rootMultiplicity_map_le_one_of_squarefree K.HK_sqfree a
  have hL0_ev : L0 % 2 = 0 := by dsimp [L0, L0_l]; split_ifs <;> omega
  have hLnoU_ev : LnoU % 2 = 0 := by dsimp [LnoU, LnoU_l]; split_ifs <;> omega
  -- Helper to extract i whenever pt ≠ .out!
  have hdom_of_pt : pt ≠ .out → ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := fun hne => by
    by_contra h; exact hne (K.ptOf_out h)
  -- Helper: evaluate rootMultiplicity at domain i!
  have hrm_dom_D1 : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → (d2 = 0 ↔ ¬ K.isD1 i) := fun i hi => by
    dsimp [d2, d2_l]; rw [hi, rootMultiplicity_map_eq, rootMultiplicity_eq_zero_iff]
    exact ⟨fun h hr => S.D1_ne_zero (h hr), fun h hr => absurd hr h⟩
  have hrm_dom_p1 : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → (a1 = 0 ↔ K.p1.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0) := fun i hi => by
    dsimp [a1, a1_l]; rw [hi, ← map_pow, rootMultiplicity_map_eq, rootMultiplicity_eq_zero_iff]
    exact ⟨fun h hr => K.hp1_ne (h hr), fun h hr => absurd hr h⟩
  have hrm_dom_M0s : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → K.muRaw_l a = K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := fun i hi => by
    dsimp [muRaw_l]; rw [hi, ← map_pow, rootMultiplicity_map_eq]
  have hrm_dom_Lam1 : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → lam = K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := fun i hi => by
    dsimp [lam, lam_l]; rw [hi, ← map_pow, rootMultiplicity_map_eq]
  have hrm_dom_g2t : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) →
      K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) = (pt.nu - pt.mVal) + e1 := fun i hi => by
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.g2t_eq_Sg2_mul_g2rem
    rw [Polynomial.map_mul, rootMultiplicity_mul (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr K.Sg2_ne)
      ((Polynomial.map_ne_zero_iff ι.injective).mpr K.g2rem_ne)), K.Sg2_rm_eq a] at h1
    have hL : (K.g2t.map ι).rootMultiplicity a = K.g2t.rootMultiplicity (BinaryIRSProfile.domain i) := by
      rw [hi, rootMultiplicity_map_eq]
    rw [hL, hι] at h1; exact h1
  -- Exact muRaw_l lower bounds for k2U/k3U/k2U_mb/k3U_mb!
  have hmuRaw_ge1 : (pt = .k2U ∨ pt = .k3U) → 1 ≤ K.muRaw_l a := fun hpt => by
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
    rw [hrm_dom_M0s i hi]
    have hsp := K.ptOf_dom_spec i
    have hn : K.isNorm i := by
      dsimp [pt] at hpt; rw [hi] at hpt
      rcases hpt with h | h
      · exact (hsp.2.2.1 h).2
      · exact (hsp.2.2.2.2.2.1 h).2
    exact (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
  have hmuRaw_mb : (pt = .k2U_mb ∨ pt = .k3U_mb) →
      2 ≤ K.muRaw_l a ∧ (pt = .k3U_mb → 3 + L0 / 2 ≤ K.muRaw_l a) := fun hpt => by
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
    rw [hrm_dom_M0s i hi]
    have hsp := K.ptOf_dom_spec i
    have hL0_i : L0 = if 3 ≤ D.k i ∧ S.isU0 i then 2 * (D.k i - 3) else 0 := by
      dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
      have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
      rw [hch]
    have hmb : K.isMbad i := by
      dsimp [pt] at hpt; rw [hi] at hpt
      rcases hpt with h | h
      · exact (hsp.2.2.2.2.1 h).2
      · exact (hsp.2.2.2.2.2.2.2 h).2
    have hd := K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2
    have hle := (le_rootMultiplicity_iff K.hM0s_ne).mpr hd
    refine ⟨by have := hmb.1; omega, fun h3 => ?_⟩
    have hk3 : 3 ≤ D.k i := by dsimp [pt] at h3; rw [hi] at h3; exact (hsp.2.2.2.2.2.2.2 h3).1
    rw [if_pos ⟨hk3, hmb.2.1⟩] at hL0_i; omega
  -- hS and htot from HK_wronskian & HK_decomp!
  have hS_bound : g ≤ pt.mVal + lam + 3 * d2 + 5 * a1 := by
    have hwr := congrArg (Polynomial.map ι) (K.HK_wronskian hd1)
    simp only [Polynomial.map_mul, Polynomial.map_pow] at hwr
    have hRHS_ne : (K.M0eff.map ι) ^ 2 * (S.D1.map ι) ^ 6 * ((K.p1.comp (X ^ 2)).map ι) ^ 5 *
        ((K.Lam1.comp (X ^ 2)).map ι) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero
        (pow_ne_zero 2 ((Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne))
        (pow_ne_zero 6 ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero)))
        (pow_ne_zero 5 ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne))))
        ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne))
    have hdvd : (K.SK.map ι) ^ 2 ∣ (K.M0eff.map ι) ^ 2 * (S.D1.map ι) ^ 6 *
        ((K.p1.comp (X ^ 2)).map ι) ^ 5 * ((K.Lam1.comp (X ^ 2)).map ι) :=
      ⟨(C c0 * K.HK + Ndom * K.HK.derivative).map ι, hwr.symm⟩
    have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hRHS_ne hdvd a
    have hSKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.SK_ne
    have hME := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne
    have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
    have hp1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne)
    have hLE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne)
    rw [rootMultiplicity_pow_eq' _ hSKE 2 a,
      rootMultiplicity_mul hRHS_ne,
      rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)),
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)),
      rootMultiplicity_pow_eq' _ hME 2 a, rootMultiplicity_pow_eq' _ hD1E 6 a,
      rootMultiplicity_pow_eq' _ hp1E 5 a,
      K.M0eff_rm_eq_mVal a, rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a,
      rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne a] at hle
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [hι] at hle; dsimp [g, lam, d2, a1, g_l, lam_l, d2_l, a1_l, pt] at hle ⊢; omega
  have htot : c + e1 + pt.mVal = 2 * g + b := by
    have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) K.HK_decomp
    simp only [Polynomial.map_mul, Polynomial.map_pow] at h1
    have hME := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne
    have hg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
    have hgrE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.g2rem_ne
    have hSKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.SK_ne
    have hHKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.HK_ne
    rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hME hg2E) hgrE),
      rootMultiplicity_mul (mul_ne_zero hME hg2E),
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hSKE) hHKE),
      rootMultiplicity_pow_eq' _ hSKE 2 a, K.M0eff_rm_eq_mVal a] at h1
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [hι] at h1; dsimp [c, e1, g, b, c_l, e1_l, g_l, b_l, pt] at h1 ⊢; omega
  -- Prove vChat matches v(Q) - v(Hrem)!
  have hvChat_eq : pt.mbad = 0 → pt.vChat mu e1 c =
      ((K.Qpoly.map ι).rootMultiplicity a : ℤ) - ((K.Hrem.map ι).rootMultiplicity a : ℤ) := fun hmb0 => by
    rw [K.v_Q_sub_Hrem a]
    dsimp [mu, muEx_l, pt] at hmb0 ⊢
    cases hpt : K.ptOf a
    · simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]; rw [sub_zero_nr]; push_cast; ring
    · simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]; rw [sub_zero_nr]; push_cast; ring
    · simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]; rw [sub_zero_nr]; push_cast; ring
    · simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]; rw [sub_zero_nr]; push_cast; ring
    · have h1 := hmuRaw_ge1 (Or.inl hpt)
      simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.cast_sub h1]; push_cast; ring
    · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
      rw [hrm_dom_M0s i hi]
      have hmL : K.isML i := ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)).2
      have hm0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 :=
        rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
      simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, ↓reduceIte]
      rw [hm0]; push_cast; ring
    · rw [hpt] at hmb0; exact False.elim (Nat.one_ne_zero hmb0)
    · have h1 := hmuRaw_ge1 (Or.inr hpt)
      simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.cast_sub h1]; push_cast; ring
    · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
      rw [hrm_dom_M0s i hi]
      have hmL : K.isML i := ((K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)).2
      have hm0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 :=
        rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
      simp only [hpt, muSub, Step15Pt.vChat, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, ↓reduceIte]
      rw [hm0]; push_cast; ring
    · rw [hpt] at hmb0; exact False.elim (Nat.one_ne_zero hmb0)
  have hvChat_mb : pt.mbad = 1 → (c : ℤ) - (e1 : ℤ) - 1 - 2 * (mu : ℤ) =
      ((K.Qpoly.map ι).rootMultiplicity a : ℤ) - ((K.Hrem.map ι).rootMultiplicity a : ℤ) := fun hmb1 => by
    rw [K.v_Q_sub_Hrem a]
    dsimp [mu, muEx_l, pt] at hmb1 ⊢
    cases hpt : K.ptOf a
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · have h2 := (hmuRaw_mb (Or.inl hpt)).1
      simp only [hpt, muSub, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2]
      rw [Nat.cast_sub h2]; push_cast; ring
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · rw [hpt] at hmb1; exact False.elim (Nat.zero_ne_one hmb1)
    · have h2 := (hmuRaw_mb (Or.inr hpt)).1
      simp only [hpt, muSub, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2]
      rw [Nat.cast_sub h2]; push_cast; ring
  refine ⟨hd2_le, hb_le, hL0_ev, hLnoU_ev, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hS_bound, htot,
    hvChat_eq, hvChat_mb, ?_⟩
  · -- hL0
    intro hpos; dsimp [L0, L0_l] at hpos; split_ifs at hpos with hex h3
    · have hi := Classical.choose_spec hex; set i := Classical.choose hex
      have hpt' := K.ptOf_dom i; rw [← hi] at hpt'
      have hk0 : D.k i ≠ 0 := by omega
      have hk1 : D.k i ≠ 1 := by omega
      have hk2 : D.k i ≠ 2 := by omega
      dsimp [pt]; rw [hpt']
      simp only [hk0, hk1, hk2, h3.2, not_true_eq_false, ↓reduceIte]
      by_cases hn : K.isNorm i
      · left; simp [hn]
      · by_cases hmL : K.isML i
        · right; left; simp [hn, hmL]
        · right; right; simp [hn, hmL]
    · omega
    · omega
  · -- hLnoU
    intro hpos; dsimp [LnoU, LnoU_l] at hpos; split_ifs at hpos with hex h3
    · have hi := Classical.choose_spec hex; set i := Classical.choose hex
      have hpt' := K.ptOf_dom i; rw [← hi] at hpt'
      have hk0 : D.k i ≠ 0 := by omega
      have hk1 : D.k i ≠ 1 := by omega
      dsimp [pt]; rw [hpt']; simp [hk0, hk1, h3.2]
    · omega
    · omega
  · -- hd2_zero
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h | h <;> simp [h])
    rw [hrm_dom_D1 i hi]
    have hsp := K.ptOf_dom_spec i
    rcases hpt with h | h | h
    · have hnotU : ¬ S.isU0 i := (hsp.2.1 (hi ▸ h)).2
      exact fun hD1 => hnotU (K.isU0_of_D1_zero hD1)
    · have hmb : K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0 := (hsp.2.2.2.2.1 (hi ▸ h)).2.2.2
      exact fun hD1 => hmb (K.g2t_zero_of_D1_zero hD1)
    · have hmb : K.g2t.eval (BinaryIRSProfile.domain i) ≠ 0 := (hsp.2.2.2.2.2.2.2 (hi ▸ h)).2.2.2
      exact fun hD1 => hmb (K.g2t_zero_of_D1_zero hD1)
  · -- ha1_zero
    intro hpt hd0
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h | h | h | h | h | h <;> simp [h])
    rw [hrm_dom_p1 i hi]
    have hD1_ne : ¬ K.isD1 i := (hrm_dom_D1 i hi).mp hd0
    have hsp := K.ptOf_dom_spec i
    have hU : S.isU0 i := by
      rcases hpt with h | h | h | h | h | h | h
      · exact (hsp.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.2.2.2.1 (hi ▸ h)).2.2.1
      · exact (hsp.2.2.2.2.2.2.2 (hi ▸ h)).2.2.1
      · exact (hsp.1 (hi ▸ h)).2
    exact K.p1_ne_zero_of_isU0_D1_ne hU hD1_ne
  · -- hmu_mL
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
    have hsp := K.ptOf_dom_spec i
    have hmL : K.isML i := by
      rcases hpt with h | h
      · exact (hsp.2.2.2.1 (hi ▸ h)).2
      · exact (hsp.2.2.2.2.2.2.1 (hi ▸ h)).2
    dsimp [mu, muEx_l]; rw [hrm_dom_M0s i hi, rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)]; exact Nat.zero_sub _
  · -- hk2noU
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hk2 : 2 ≤ D.k i ∧ ¬ S.isU0 i := (K.ptOf_dom_spec i).2.1 (hi ▸ hpt)
    have hprod := K.pow_dvd_Lam1_mul_M0s i
    simp only [hk2.2, show D.k i ≠ 0 by omega, show D.k i ≠ 1 by omega, ↓reduceIte] at hprod
    have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne)] at hrm
    have hmu_eq : mu = K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
      dsimp [mu, muEx_l]; rw [show K.ptOf a = .k2noU from hpt, hrm_dom_M0s i hi, show muSub .k2noU = 0 from rfl]; exact sub_zero_nr _
    rw [hrm_dom_Lam1 i hi, hmu_eq]
    have hLno_i : LnoU = if 3 ≤ D.k i ∧ ¬ S.isU0 i then 2 * (D.k i - 3) else 0 := by
      dsimp [LnoU, LnoU_l]; rw [dif_pos ⟨i, hi⟩]
      have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
      rw [hch]
    exact ⟨fun _ => by omega, fun hpos => by split_ifs at hLno_i <;> omega⟩
  · -- hk2U_mL
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hmL : D.k i = 2 ∧ K.isML i := (K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)
    have hprod := K.pow_dvd_Lam1_mul_M0s i
    simp only [hmL.2.2.1, hmL.1, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hprod
    have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne),
      rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2.2), add_zero] at hrm
    rw [hrm_dom_Lam1 i hi]; omega
  · -- hk3U
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hk3 : 3 ≤ D.k i ∧ K.isNorm i := (K.ptOf_dom_spec i).2.2.2.2.2.1 (hi ▸ hpt)
    have hprod := K.pow_dvd_Lam1_mul_M0s i
    simp only [hk3.2.2.1, show ¬ D.k i ≤ 1 by omega, ↓reduceIte] at hprod
    have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne)] at hrm
    have hL0_i : L0 = 2 * (D.k i - 3) := by
      dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
      have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
      rw [hch, if_pos ⟨hk3.1, hk3.2.2.1⟩]
    have hmu_eq : mu = K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) - 1 := by
      dsimp [mu, muEx_l]; rw [show K.ptOf a = .k3U from hpt, hrm_dom_M0s i hi]; rfl
    rw [hrm_dom_Lam1 i hi, hmu_eq, hL0_i]; omega
  · -- hk3U_mL
    intro hpt
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hk3 : 3 ≤ D.k i ∧ K.isML i := (K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)
    have hprod := K.pow_dvd_Lam1_mul_M0s i
    simp only [hk3.2.2.1, show ¬ D.k i ≤ 1 by omega, ↓reduceIte] at hprod
    have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hLam1_ne K.hM0s_ne)).mpr hprod
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne),
      rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hk3.2.2.2.2), add_zero] at hrm
    have hL0_i : L0 = 2 * (D.k i - 3) := by
      dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
      have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
      rw [hch, if_pos ⟨hk3.1, hk3.2.2.1⟩]
    rw [hrm_dom_Lam1 i hi, hL0_i]; omega
  · -- hk3U_mb_mu
    intro hpt
    have h := (hmuRaw_mb (Or.inr hpt)).2 hpt
    dsimp [mu, muEx_l]; rw [show K.ptOf a = .k3U_mb from hpt]; dsimp only [muSub]; omega
  · -- he1_k1U
    intro hpt hcond
    obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
    have hk1 : D.k i = 1 ∧ S.isU0 i := (K.ptOf_dom_spec i).1 (hi ▸ hpt)
    have hg2t_eq := hrm_dom_g2t i hi
    rw [show pt = .k1U from hpt] at hg2t_eq; simp [Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] at hg2t_eq
    rcases hcond with hd1' | hmu0
    · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
      have h1 := (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1))
      omega
    · by_cases hD1 : K.isD1 i
      · have h1 := (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr (K.g2t_zero_of_D1_zero hD1))
        omega
      · have hM0 : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
          have hm0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 := by
            dsimp [mu, muEx_l] at hmu0; rw [show K.ptOf a = .k1U from hpt, hrm_dom_M0s i hi, show muSub .k1U = 0 from rfl, sub_zero_nr] at hmu0; exact hmu0
          exact fun hr => K.hM0s_ne ((rootMultiplicity_eq_zero_iff.mp hm0) hr)
        have hH1d : X - C (BinaryIRSProfile.domain i) ∣ S.H1 := by
          have := S.pow_dvd_H1_of_isU0 i hk1.2; rwa [hk1.1, pow_one] at this
        rw [K.hH1_fac] at hH1d
        have hcop : IsCoprime (X - C (BinaryIRSProfile.domain i)) (S.D1 ^ 4 * K.M0s.comp (X ^ 2)) := by
          have hne : (S.D1 ^ 4 * K.M0s.comp (X ^ 2)).eval (BinaryIRSProfile.domain i) ≠ 0 := by
            rw [eval_mul, eval_pow, eval_comp, eval_pow, eval_X]; exact mul_ne_zero (pow_ne_zero 4 hD1) hM0
          exact (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
        have h1 := (le_rootMultiplicity_iff K.hg2t_ne).mpr (by rw [pow_one]; exact hcop.dvd_of_dvd_mul_left hH1d)
        omega
  · -- he1_mL
    intro hpt hd0
    obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
    have hD1 : ¬ K.isD1 i := (hrm_dom_D1 i hi).mp hd0
    have hsp := K.ptOf_dom_spec i
    have hmL : K.isML i := by
      rcases hpt with h | h
      · exact (hsp.2.2.2.1 (hi ▸ h)).2
      · exact (hsp.2.2.2.2.2.2.1 (hi ▸ h)).2
    have hH1d := (pow_dvd_pow (X - C (BinaryIRSProfile.domain i)) (by have := hmL.1; omega : 3 ≤ 2 * D.k i - 1)).trans
      (S.pow_dvd_H1_of_isU0 i hmL.2.1)
    rw [K.hH1_fac] at hH1d
    have hcop : IsCoprime ((X - C (BinaryIRSProfile.domain i)) ^ 3) (S.D1 ^ 4 * K.M0s.comp (X ^ 2)) := by
      apply IsCoprime.pow_left
      have hne : (S.D1 ^ 4 * K.M0s.comp (X ^ 2)).eval (BinaryIRSProfile.domain i) ≠ 0 := by
        rw [eval_mul, eval_pow, eval_comp, eval_pow, eval_X]; exact mul_ne_zero (pow_ne_zero 4 hD1) hmL.2.2.2
      exact (Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
    have h3 := (le_rootMultiplicity_iff K.hg2t_ne).mpr (hcop.dvd_of_dvd_mul_left hH1d)
    have hg2t_eq := hrm_dom_g2t i hi
    rcases hpt with h | h <;> rw [h] at hg2t_eq <;>
      simp [Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] at hg2t_eq <;> omega
  · -- htri: universal 4-term valuation triangle from K.h4term_y0!
    intro hcond
    let y0 : Fld := if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then D.y (Classical.choose h) else 0
    let Uy0 : Fld[X] := S.p.comp (X ^ 2) * C y0 + S.R
    let U1_y0 : Fld[X] := S.D1 * K.p1.comp (X ^ 2) * C y0 + K.R1
    let gsh0 : Fld[X] := D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2
    have hUfac : Uy0 = S.D1 * U1_y0 := by
      dsimp [Uy0, U1_y0]; rw [K.hp_fac, mul_comp, ← S.D1_sq, K.hR_fac]; ring
    -- First show (U1_y0.map ι).eval a ≠ 0!
    have hU1_ev : (U1_y0.map ι).eval a ≠ 0 := by
      have hR1_ev_of_q1 : (K.q1.map ι).eval (a ^ 2) ≠ 0 → (K.R1.map ι).eval a ≠ 0 := fun hq1 hR1 => by
        have h := congrArg (fun f : Fld[X] => (f.map ι).eval a) K.hR1_sq
        simp only [Polynomial.map_pow, Polynomial.map_comp, Polynomial.map_X, eval_pow, eval_comp, eval_X, hR1,
          zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] at h
        exact hq1 h.symm
      rcases hcond with ha1 | hd2' | hk2no
      · by_cases hd0 : d2 = 0
        · have hp10 : (K.p1.map ι).eval (a ^ 2) = 0 := by
            have := (pow_dvd_pow (X - C (a ^ 2)) ha1).trans (pow_rootMultiplicity_dvd (K.p1.map ι) (a ^ 2))
            rw [pow_one] at this; exact dvd_iff_isRoot.mp this
          have hq1_ne : (K.q1.map ι).eval (a ^ 2) ≠ 0 := fun hq10 => by
            have hu := (K.hp1_q1_cop.map (Polynomial.mapRingHom ι)).isUnit_of_dvd' (dvd_iff_isRoot.mpr hp10) (dvd_iff_isRoot.mpr hq10)
            have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
          have hR1_ne := hR1_ev_of_q1 hq1_ne
          dsimp [U1_y0]
          simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
            Polynomial.map_C, eval_add, eval_mul, eval_comp, eval_pow, eval_X, eval_C, hp10, mul_zero, zero_mul, zero_add]
          exact hR1_ne
        · have hD10 : (S.D1.map ι).eval a = 0 := by
            have := (pow_dvd_pow (X - C a) (by omega : 1 ≤ d2)).trans (pow_rootMultiplicity_dvd (S.D1.map ι) a)
            rw [pow_one] at this; exact dvd_iff_isRoot.mp this
          have hD20 : (S.D2.map ι).eval (a ^ 2) = 0 := by
            have h := congrArg (fun f : Fld[X] => (f.map ι).eval a) S.D1_sq
            simp only [Polynomial.map_pow, Polynomial.map_comp, Polynomial.map_X, eval_pow, eval_comp, eval_X, hD10,
              zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] at h
            exact h.symm
          have hq1_ne : (K.q1.map ι).eval (a ^ 2) ≠ 0 := fun hq10 => by
            have hu := (K.hD2_q1_cop.map (Polynomial.mapRingHom ι)).isUnit_of_dvd' (dvd_iff_isRoot.mpr hD20) (dvd_iff_isRoot.mpr hq10)
            have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
          have hR1_ne := hR1_ev_of_q1 hq1_ne
          dsimp [U1_y0]
          simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hD10, zero_mul, zero_add]
          exact hR1_ne
      · have hD10 : (S.D1.map ι).eval a = 0 := by
          have := (pow_dvd_pow (X - C a) hd2').trans (pow_rootMultiplicity_dvd (S.D1.map ι) a)
          rw [pow_one] at this; exact dvd_iff_isRoot.mp this
        have hD20 : (S.D2.map ι).eval (a ^ 2) = 0 := by
          have h := congrArg (fun f : Fld[X] => (f.map ι).eval a) S.D1_sq
          simp only [Polynomial.map_pow, Polynomial.map_comp, Polynomial.map_X, eval_pow, eval_comp, eval_X, hD10,
            zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] at h
          exact h.symm
        have hq1_ne : (K.q1.map ι).eval (a ^ 2) ≠ 0 := fun hq10 => by
          have hu := (K.hD2_q1_cop.map (Polynomial.mapRingHom ι)).isUnit_of_dvd' (dvd_iff_isRoot.mpr hD20) (dvd_iff_isRoot.mpr hq10)
          have h0 := natDegree_eq_zero_of_isUnit hu; rw [natDegree_X_sub_C] at h0; omega
        have hR1_ne := hR1_ev_of_q1 hq1_ne
        dsimp [U1_y0]
        simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hD10, zero_mul, zero_add]
        exact hR1_ne
      · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hk2no])
        have hnotU : ¬ S.isU0 i := ((K.ptOf_dom_spec i).2.1 (hi ▸ hk2no)).2
        have hy0_i : y0 = D.y i := by
          dsimp [y0]; rw [dif_pos ⟨i, hi⟩]
          have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
            BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
          rw [hch]
        have hUy_ne : (Uy0.map ι).eval a ≠ 0 := by
          rw [hi, eval_map_apply]; intro h0; apply hnotU
          have h0' : Uy0.eval (BinaryIRSProfile.domain i) = 0 := ι.injective (by rw [map_zero]; exact h0)
          simpa [Uy0, hy0_i, KerD45Syzygy.isU0, KerD45Syzygy.U_eval] using h0'
        intro hU10; apply hUy_ne; rw [hUfac, Polynomial.map_mul, eval_mul, hU10, mul_zero]
    have hU1_ne : U1_y0.map ι ≠ 0 := fun h0 => hU1_ev (by rw [h0, eval_zero])
    have hU1_rm0 : (U1_y0.map ι).rootMultiplicity a = 0 := rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hU1_ev)
    -- Apply tri_of_four_term_id to K.h4term_y0 y0 mapped to E!
    let T1 : E[X] := ((S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 4 * gsh0).map ι)
    let T2 : E[X] := ((K.p1.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1).map ι)
    let T3 : E[X] := ((K.M0s.comp (X ^ 2) * K.g2t).map ι)
    let T4 : E[X] := ((D.gj 2 * U1_y0 ^ 4).map ι)
    have hT3_ne : T3 ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr
      (mul_ne_zero (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne)
    have hT4_ne : T4 ≠ 0 := by
      dsimp [T4]; rw [Polynomial.map_mul, Polynomial.map_pow]
      exact mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero) (pow_ne_zero 4 hU1_ne)
    have hidE : T1 + T2 + T3 = T4 := by
      have h := congrArg (Polynomial.map ι) (K.h4term_y0 y0)
      dsimp [T1, T2, T3, T4, gsh0, Uy0, U1_y0]
      simp only [Polynomial.map_add] at h
      linear_combination h
    -- Exact valuations of T3 and T4!
    have hT4_rm : T4.rootMultiplicity a = c := by
      dsimp [T4, c, c_l]; rw [Polynomial.map_mul, Polynomial.map_pow,
        rootMultiplicity_mul (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero) (pow_ne_zero 4 hU1_ne)),
        rootMultiplicity_pow_eq' _ hU1_ne 4 a, hU1_rm0, mul_zero, add_zero]
    have hT3_rm : T3.rootMultiplicity a = pt.t3 d2 mu e1 - 3 * pt.mVal := by
      have hMcE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne)
      have hSgE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.Sg2_ne
      have hgrE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.g2rem_ne
      dsimp [T3]; rw [K.g2t_eq_Sg2_mul_g2rem, Polynomial.map_mul, Polynomial.map_mul,
        rootMultiplicity_mul (mul_ne_zero hMcE (mul_ne_zero hSgE hgrE)),
        rootMultiplicity_mul (mul_ne_zero hSgE hgrE),
        rootMultiplicity_comp_X_sq_map K.M0s K.hM0s_ne a, K.Sg2_rm_eq a]
      -- Note mbad cannot occur under hcond (since mbad has d2 = 0 and a1 = 0)!
      have hnmb : pt ≠ .k2U_mb ∧ pt ≠ .k3U_mb := by
        constructor <;> intro hpt
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
          have hmb : K.isMbad i := ((K.ptOf_dom_spec i).2.2.2.2.1 (hi ▸ hpt)).2
          have hd0 : d2 = 0 := (hrm_dom_D1 i hi).mpr (fun hD1 => hmb.2.2 (K.g2t_zero_of_D1_zero hD1))
          have ha0 : a1 = 0 := (hrm_dom_p1 i hi).mpr (K.p1_ne_zero_of_isU0_D1_ne hmb.2.1 ((hrm_dom_D1 i hi).mp hd0))
          rcases hcond with h | h | h
          · omega
          · omega
          · rw [hpt] at h; cases h
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [hpt])
          have hmb : K.isMbad i := ((K.ptOf_dom_spec i).2.2.2.2.2.2.2 (hi ▸ hpt)).2
          have hd0 : d2 = 0 := (hrm_dom_D1 i hi).mpr (fun hD1 => hmb.2.2 (K.g2t_zero_of_D1_zero hD1))
          have ha0 : a1 = 0 := (hrm_dom_p1 i hi).mpr (K.p1_ne_zero_of_isU0_D1_ne hmb.2.1 ((hrm_dom_D1 i hi).mp hd0))
          rcases hcond with h | h | h
          · omega
          · omega
          · rw [hpt] at h; cases h
      have hd1_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → d2 = 1 := fun hpt => by
        by_contra hd0'
        have hd0 : d2 = 0 := by omega
        obtain ⟨i, hi⟩ := hdom_of_pt (by rcases hpt with h | h <;> simp [h])
        have hD1_ne := (hrm_dom_D1 i hi).mp hd0
        have hU : S.isU0 i := by
          rcases hpt with h | h
          · exact ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ h)).2.2.1
          · exact ((K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ h)).2.2.1
        have ha0 : a1 = 0 := (hrm_dom_p1 i hi).mpr (K.p1_ne_zero_of_isU0_D1_ne hU hD1_ne)
        rcases hcond with h | h | h
        · omega
        · omega
        · rcases hpt with hp | hp <;> rw [hp] at h <;> cases h
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      dsimp [mu, muEx_l, muRaw_l, e1, e1_l, pt] at hnmb hd1_mL ⊢; rw [hι]
      cases hpt : K.ptOf a
      · simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; rw [sub_zero_nr]; omega
      · simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; rw [sub_zero_nr]; omega
      · simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; rw [sub_zero_nr]; omega
      · simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; rw [sub_zero_nr]; omega
      · have h1 := hmuRaw_ge1 (Or.inl hpt); dsimp [muRaw_l] at h1
        simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; omega
      · have hd1' := hd1_mL (Or.inl hpt)
        obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
        have hmL : K.isML i := ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)).2
        have hm0 : (K.M0s.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2) = 0 := by
          rw [← hι, hi, ← map_pow, rootMultiplicity_map_eq]; exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
        simp only [hd1', hm0, muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, and_self, ↓reduceIte]; omega
      · exact absurd hpt hnmb.1
      · have h1 := hmuRaw_ge1 (Or.inr hpt); dsimp [muRaw_l] at h1
        simp only [muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, ↓reduceIte]; omega
      · have hd1' := hd1_mL (Or.inr hpt)
        obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
        have hmL : K.isML i := ((K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)).2
        have hm0 : (K.M0s.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2) = 0 := by
          rw [← hι, hi, ← map_pow, rootMultiplicity_map_eq]; exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hmL.2.2.2)
        simp only [hd1', hm0, muSub, Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, and_self, ↓reduceIte]; omega
      · exact absurd hpt hnmb.2
    -- Divisibility bounds on T1 and T2!
    have hd_T1 : (X - C a) ^ (8 * a1 + 4 * d2 + pt.vc0 d2 e1 c L0 LnoU) ∣ T1 := by
      dsimp [T1]; simp only [Polynomial.map_mul, Polynomial.map_pow]
      have hdD : (X - C a) ^ (4 * d2) ∣ (S.D1.map ι) ^ 4 := by
        rw [mul_comm 4 d2, pow_mul]; exact pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd (S.D1.map ι) a) 4
      have hdp : (X - C a) ^ (8 * a1) ∣ ((K.p1.comp (X ^ 2)).map ι) ^ 4 := by
        have h2a := pow_rootMultiplicity_dvd ((K.p1.comp (X ^ 2)).map ι) a
        rw [rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a] at h2a
        rw [show 8 * a1 = (2 * a1) * 4 by ring, pow_mul]; exact pow_dvd_pow_of_dvd h2a 4
      have hdg : (X - C a) ^ (pt.vc0 d2 e1 c L0 LnoU) ∣ gsh0.map ι := by
        have hdom_g : ∀ i : Idx, a = ι (BinaryIRSProfile.domain i) → (X - C a) ^ (2 * D.k i - 1) ∣ gsh0.map ι := fun i hi => by
          have hy0_i : y0 = D.y i := by
            dsimp [y0]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch]
          rcases K.pow_dvd_gsh0 i with ⟨w, hw⟩
          refine ⟨w.map ι, ?_⟩
          have h := congrArg (Polynomial.map ι) hw
          simpa [gsh0, hy0_i, hi] using h
        cases hpt : K.ptOf a
        · rw [show pt = .out from hpt, show Step15Pt.vc0 .out d2 e1 c L0 LnoU = 0 from rfl, pow_zero]; exact one_dvd _
        · rw [show pt = .k0 from hpt, show Step15Pt.vc0 .k0 d2 e1 c L0 LnoU = 0 from rfl, pow_zero]; exact one_dvd _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk1 : D.k i = 1 := ((K.ptOf_dom_spec i).1 (hi ▸ hpt)).1
          rw [show pt = .k1U from hpt, show Step15Pt.vc0 .k1U d2 e1 c L0 LnoU = 1 from rfl]
          have hg := hdom_g i hi; rw [hk1] at hg; exact hg
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : 2 ≤ D.k i ∧ ¬ S.isU0 i := (K.ptOf_dom_spec i).2.1 (hi ▸ hpt)
          have hLno_i : LnoU = if 3 ≤ D.k i ∧ ¬ S.isU0 i then 2 * (D.k i - 3) else 0 := by
            dsimp [LnoU, LnoU_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch]
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k2noU from hpt]; dsimp only [Step15Pt.vc0]
          split_ifs with hpos
          · rw [hLno_i] at hpos ⊢
            split_ifs at hpos ⊢ with h3
            · have h3' := h3.1; generalize D.k i = ki at h3' ⊢; omega
            · exact absurd hpos (by decide)
          · have h2' := hk2.1; generalize D.k i = ki at h2' ⊢; omega
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : D.k i = 2 := ((K.ptOf_dom_spec i).2.2.1 (hi ▸ hpt)).1
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k2U from hpt, hk2]; dsimp only [Step15Pt.vc0]
          split_ifs
          · exact le_rfl
          · exact Nat.min_le_left 3 _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : D.k i = 2 := ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)).1
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k2U_mL from hpt, hk2]; dsimp only [Step15Pt.vc0]
          split_ifs
          · exact le_rfl
          · exact Nat.min_le_left 3 _
        · rw [show pt = .k2U_mb from hpt, show Step15Pt.vc0 .k2U_mb d2 e1 c L0 LnoU = 0 from rfl, pow_zero]; exact one_dvd _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hsp := (K.ptOf_dom_spec i).2.2.2.2.2.1 (hi ▸ hpt)
          have hk3 : 3 ≤ D.k i ∧ S.isU0 i := ⟨hsp.1, hsp.2.2.1⟩
          have hL0_i : L0 = 2 * (D.k i - 3) := by
            dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch, if_pos hk3]
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k3U from hpt]; dsimp only [Step15Pt.vc0]
          split_ifs
          · rw [hL0_i]; have h3' := hk3.1; generalize D.k i = ki at h3' ⊢; omega
          · exact (Nat.min_le_left 3 _).trans (by have h3' := hk3.1; generalize D.k i = ki at h3' ⊢; omega)
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hsp := (K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)
          have hk3 : 3 ≤ D.k i ∧ S.isU0 i := ⟨hsp.1, hsp.2.2.1⟩
          have hL0_i : L0 = 2 * (D.k i - 3) := by
            dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch, if_pos hk3]
          refine (pow_dvd_pow _ ?_).trans (hdom_g i hi)
          rw [show pt = .k3U_mL from hpt]; dsimp only [Step15Pt.vc0]
          split_ifs
          · rw [hL0_i]; have h3' := hk3.1; generalize D.k i = ki at h3' ⊢; omega
          · exact (Nat.min_le_left 3 _).trans (by have h3' := hk3.1; generalize D.k i = ki at h3' ⊢; omega)
        · rw [show pt = .k3U_mb from hpt, show Step15Pt.vc0 .k3U_mb d2 e1 c L0 LnoU = 0 from rfl, pow_zero]; exact one_dvd _
      rw [show 8 * a1 + 4 * d2 + pt.vc0 d2 e1 c L0 LnoU = 4 * d2 + 8 * a1 + pt.vc0 d2 e1 c L0 LnoU by omega,
        pow_add, pow_add]
      exact mul_dvd_mul (mul_dvd_mul hdD hdp) hdg
    have hd_T2 : (X - C a) ^ (4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + e1) ∣ T2 := by
      dsimp [T2]; rw [K.hg1_fac, K.g2t_eq_Sg2_mul_g2rem, hUfac]
      simp only [Polynomial.map_mul, Polynomial.map_pow]
      have hdp : (X - C a) ^ (4 * a1) ∣ ((K.p1.comp (X ^ 2)).map ι) ^ 2 := by
        have h2a := pow_rootMultiplicity_dvd ((K.p1.comp (X ^ 2)).map ι) a
        rw [rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a] at h2a
        rw [show 4 * a1 = (2 * a1) * 2 by ring, pow_mul]; exact pow_dvd_pow_of_dvd h2a 2
      have hdU : (X - C a) ^ (2 * d2) ∣ (S.D1.map ι * U1_y0.map ι) ^ 2 := by
        rw [mul_pow, mul_comm 2 d2, pow_mul]
        exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd (S.D1.map ι) a) 2) _
      have hdK1 : (X - C a) ^ (2 * pt.k1Min d2 lam L0 LnoU) ∣ (K.K1.comp (X ^ 2)).map ι := by
        have h2k := pow_rootMultiplicity_dvd ((K.K1.comp (X ^ 2)).map ι) a
        rw [rootMultiplicity_comp_X_sq_map K.K1 K.hK1_ne a] at h2k
        refine (pow_dvd_pow _ (Nat.mul_le_mul_left 2 ?_)).trans h2k
        cases hpt : K.ptOf a
        · rw [show pt = .out from hpt, show Step15Pt.k1Min .out d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
        · rw [show pt = .k0 from hpt, show Step15Pt.k1Min .k0 d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
        · rw [show pt = .k1U from hpt, show Step15Pt.k1Min .k1U d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : 2 ≤ D.k i ∧ ¬ S.isU0 i := (K.ptOf_dom_spec i).2.1 (hi ▸ hpt)
          have hLno_i : LnoU = if 3 ≤ D.k i ∧ ¬ S.isU0 i then 2 * (D.k i - 3) else 0 := by
            dsimp [LnoU, LnoU_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch]
          have hrm := (le_rootMultiplicity_iff K.hK1_ne).mpr (K.pow_dvd_K1_U1 i hk2.2)
          rw [hi, ← map_pow, rootMultiplicity_map_eq, show pt = .k2noU from hpt]; dsimp only [Step15Pt.k1Min]
          split_ifs with hpos
          · rw [hLno_i] at hpos ⊢
            split_ifs at hpos ⊢ with h3
            · have h3' := h3.1; generalize D.k i = ki at h3' hrm ⊢; generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = rm at hrm ⊢; omega
            · exact absurd hpos (Nat.not_lt_zero 0)
          · have h2' := hk2.1; generalize D.k i = ki at h2' hrm ⊢; generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = rm at hrm ⊢; omega
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : D.k i = 2 := ((K.ptOf_dom_spec i).2.2.1 (hi ▸ hpt)).1
          rw [show pt = .k2U from hpt]; dsimp only [Step15Pt.k1Min]; split_ifs with hd1'
          · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
            have hKL := K.pow_dvd_K_M10sh_d2 i hD1
            simp only [hk2, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hKL
            have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hKL
            rw [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hrm
            rw [hi, ← map_pow, rootMultiplicity_map_eq, hrm_dom_Lam1 i hi]
            generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r1 at hrm ⊢
            generalize K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r2 at hrm ⊢; omega
          · exact Nat.zero_le _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hk2 : D.k i = 2 := ((K.ptOf_dom_spec i).2.2.2.1 (hi ▸ hpt)).1
          rw [show pt = .k2U_mL from hpt]; dsimp only [Step15Pt.k1Min]; split_ifs with hd1'
          · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
            have hKL := K.pow_dvd_K_M10sh_d2 i hD1
            simp only [hk2, show ¬ (2 ≤ 1) by omega, ↓reduceIte] at hKL
            have hrm := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hKL
            rw [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hrm
            rw [hi, ← map_pow, rootMultiplicity_map_eq, hrm_dom_Lam1 i hi]
            generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r1 at hrm ⊢
            generalize K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r2 at hrm ⊢; omega
          · exact Nat.zero_le _
        · rw [show pt = .k2U_mb from hpt, show Step15Pt.k1Min .k2U_mb d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hsp := (K.ptOf_dom_spec i).2.2.2.2.2.1 (hi ▸ hpt)
          have hk3 : 3 ≤ D.k i ∧ S.isU0 i := ⟨hsp.1, hsp.2.2.1⟩
          have hL0_i : L0 = 2 * (D.k i - 3) := by
            dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch, if_pos hk3]
          rw [show pt = .k3U from hpt]; dsimp only [Step15Pt.k1Min]; split_ifs with hd1'
          · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
            have hKL := K.pow_dvd_K_M10sh_d2 i hD1; rw [if_neg (by omega)] at hKL
            have hrm1 := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hKL
            rw [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hrm1
            have hrm2 := (le_rootMultiplicity_iff K.hK1_ne).mpr (K.pow_dvd_K1_all i)
            rw [hi, ← map_pow, rootMultiplicity_map_eq, hrm_dom_Lam1 i hi, hL0_i]
            have h3' := hk3.1; generalize D.k i = ki at h3' hrm1 hrm2 ⊢
            generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r1 at hrm1 hrm2 ⊢
            generalize K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r2 at hrm1 ⊢; omega
          · exact Nat.zero_le _
        · obtain ⟨i, hi⟩ := hdom_of_pt (by simp [pt, hpt])
          have hsp := (K.ptOf_dom_spec i).2.2.2.2.2.2.1 (hi ▸ hpt)
          have hk3 : 3 ≤ D.k i ∧ S.isU0 i := ⟨hsp.1, hsp.2.2.1⟩
          have hL0_i : L0 = 2 * (D.k i - 3) := by
            dsimp [L0, L0_l]; rw [dif_pos ⟨i, hi⟩]
            have hch : Classical.choose (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j)) = i :=
              BinaryIRSProfile.domain.injective (ι.injective ((Classical.choose_spec (⟨i, hi⟩ : ∃ j, a = ι (BinaryIRSProfile.domain j))).symm.trans hi))
            rw [hch, if_pos hk3]
          rw [show pt = .k3U_mL from hpt]; dsimp only [Step15Pt.k1Min]; split_ifs with hd1'
          · have hD1 : K.isD1 i := by by_contra h; have := (hrm_dom_D1 i hi).mpr h; omega
            have hKL := K.pow_dvd_K_M10sh_d2 i hD1; rw [if_neg (by omega)] at hKL
            have hrm1 := (le_rootMultiplicity_iff (mul_ne_zero K.hK1_ne K.hLam1_ne)).mpr hKL
            rw [rootMultiplicity_mul (mul_ne_zero K.hK1_ne K.hLam1_ne)] at hrm1
            have hrm2 := (le_rootMultiplicity_iff K.hK1_ne).mpr (K.pow_dvd_K1_all i)
            rw [hi, ← map_pow, rootMultiplicity_map_eq, hrm_dom_Lam1 i hi, hL0_i]
            have h3' := hk3.1; generalize D.k i = ki at h3' hrm1 hrm2 ⊢
            generalize K.K1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r1 at hrm1 hrm2 ⊢
            generalize K.Lam1.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = r2 at hrm1 ⊢; omega
          · exact Nat.zero_le _
        · rw [show pt = .k3U_mb from hpt, show Step15Pt.k1Min .k3U_mb d2 lam L0 LnoU = 0 from rfl]; exact Nat.zero_le _
      have hdSg : (X - C a) ^ (pt.nu - pt.mVal) ∣ K.Sg2.map ι := by
        rw [← K.Sg2_rm_eq a]; exact pow_rootMultiplicity_dvd _ a
      have hdgr : (X - C a) ^ e1 ∣ K.g2rem.map ι := pow_rootMultiplicity_dvd _ a
      rw [show 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + e1 =
          (4 * a1 + 2 * d2) + (2 * pt.k1Min d2 lam L0 LnoU + ((pt.nu - pt.mVal) + e1)) by omega,
        pow_add, pow_add, pow_add, pow_add]
      exact mul_dvd_mul (mul_dvd_mul hdp hdU) (mul_dvd_mul hdK1 (mul_dvd_mul hdSg hdgr))
    have hs3 : 3 * pt.mVal ≤ pt.t3 d2 mu e1 := by
      dsimp only [pt, d2, mu, e1]
      generalize K.ptOf a = p; generalize K.d2_l a = d; generalize K.muEx_l a = m; generalize K.e1_l a = e
      cases p <;> simp only [Step15Pt.t3, Step15Pt.isML, Step15Pt.nu, Step15Pt.mVal,
        Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2, Bool.false_eq_true, false_and, true_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    exact tri_of_four_term_id a hT3_ne hT4_ne hidE (s := 3 * pt.mVal)
      (by simpa [show 8 * a1 + 4 * d2 + 3 * pt.mVal + pt.vc0 d2 e1 c L0 LnoU - 3 * pt.mVal =
          8 * a1 + 4 * d2 + pt.vc0 d2 e1 c L0 LnoU by omega] using hd_T1)
      (by simpa [show 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + 3 * pt.mVal + e1 - 3 * pt.mVal =
          4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + e1 by omega] using hd_T2)
      (by omega) (by omega) hs3 (by omega) hT3_rm (by simpa using hT4_rm)

-- Universal finite-sum bridge for ALL 15-column `Step15Pt` sums over a large enough `S_fin`!
open Classical in
lemma sum_step15_cols (S_fin : Finset (AlgebraicClosure Fld))
    (hS_dom : ∀ i : Idx, algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) ∈ S_fin)
    (hS_M0s : ((K.M0s.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_Lam1 : ((K.Lam1.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_p1 : ((K.p1.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_D1 : (S.D1.map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_g2r : (K.g2rem.map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_g2 : ((D.gj 2).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin) :
    (∑ a ∈ S_fin, ((K.ptOf a).m0 : ℤ)) = (D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).mbad : ℤ)) = (K.mbadCnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).m1 : ℤ)) = (S.n1U : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).m2 : ℤ)) = (D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).k3 : ℤ)) = (S.n3U : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).mL0 (K.d2_l a) : ℤ)) = (K.mLCnt : ℤ) - (K.dmLCnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ)) = (K.mu1Cnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ)) =
      (K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ) ∧
    (∑ a ∈ S_fin, (K.lam_l a : ℤ)) = (K.Lam1.natDegree : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).din (K.d2_l a) : ℤ)) = (K.dinCnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).dmL (K.d2_l a) : ℤ)) = (K.dmLCnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).d2oth (K.d2_l a) : ℤ)) = (S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ) ∧
    (∑ a ∈ S_fin, (K.L0_l a : ℤ)) = 2 * (S.ntU : ℤ) ∧
    (∑ a ∈ S_fin, (K.a1_l a : ℤ)) = (S.p.natDegree : ℤ) - (S.D1.natDegree : ℤ) ∧
    (∑ a ∈ S_fin, (K.LnoU_l a : ℤ)) = 2 * ((D.nt : ℤ) - (S.ntU : ℤ)) ∧
    (∑ a ∈ S_fin, (K.c_l a : ℤ)) = ((D.gj 2).natDegree : ℤ) ∧
    (∑ a ∈ S_fin, (K.e1_l a : ℤ)) = (K.g2rem.natDegree : ℤ) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  let domImg : Finset E := Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i))
  have hdom_sub : domImg ⊆ S_fin := fun a ha => by
    rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩; exact hS_dom i
  have hsum_dom : ∀ (f : E → ℤ), (∀ a, (¬ ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)) → f a = 0) →
      ∑ a ∈ S_fin, f a = ∑ i : Idx, f (ι (BinaryIRSProfile.domain i)) := fun f hf0 => by
    rw [← Finset.sum_subset hdom_sub (fun a _ hna => hf0 a (fun ⟨i, hi⟩ => hna (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩))),
      Finset.sum_image (fun i _ j _ h => BinaryIRSProfile.domain.injective (ι.injective h))]
  have hD1_sum : (∑ a ∈ S_fin, (K.d2_l a : ℤ)) = (S.D1.natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_map_eq_natDegree S.D1 S.D1_ne_zero S_fin hS_D1
  have hLam_sum : (∑ a ∈ S_fin, (K.lam_l a : ℤ)) = (K.Lam1.natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_sq_map_eq_natDegree K.Lam1 K.hLam1_ne S_fin hS_Lam1
  have hp1_sum : (∑ a ∈ S_fin, (K.a1_l a : ℤ)) = (S.p.natDegree : ℤ) - (S.D1.natDegree : ℤ) := by
    have h1 : ∑ a ∈ S_fin, K.a1_l a = K.p1.natDegree :=
      sum_rootMultiplicity_sq_map_eq_natDegree K.p1 K.hp1_ne S_fin hS_p1
    have hp := K.natDegree_p_eq
    have h1Z : (∑ a ∈ S_fin, (K.a1_l a : ℤ)) = (K.p1.natDegree : ℤ) := by exact_mod_cast h1
    rw [h1Z]; clear h1 h1Z hD1_sum hLam_sum hdom_sub hsum_dom; omega
  have hc_sum : (∑ a ∈ S_fin, (K.c_l a : ℤ)) = ((D.gj 2).natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_map_eq_natDegree (D.gj 2) D.g2_ne_zero S_fin hS_g2
  have he1_sum : (∑ a ∈ S_fin, (K.e1_l a : ℤ)) = (K.g2rem.natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_map_eq_natDegree K.g2rem K.g2rem_ne S_fin hS_g2r
  have hM0s_sum : (∑ a ∈ S_fin, (K.muRaw_l a : ℤ)) = (K.M0s.natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_sq_map_eq_natDegree K.M0s K.hM0s_ne S_fin hS_M0s
  -- Helper for d2_l at domain i:
  have hd2_dom : ∀ i : Idx, K.d2_l (ι (BinaryIRSProfile.domain i)) = if K.isD1 i then 1 else 0 := fun i => by
    have hle := K.d2_l_le_one (ι (BinaryIRSProfile.domain i))
    dsimp [d2_l] at hle ⊢; rw [rootMultiplicity_map_eq] at hle ⊢
    split_ifs with h
    · have hge := (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h); omega
    · exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr h)
  -- Helper for din, dmL, mL0, mu1!
  have hdin_sum : (∑ a ∈ S_fin, ((K.ptOf a).din (K.d2_l a) : ℤ)) = (K.dinCnt : ℤ) := by
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.dinCnt : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
        (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0)) := by
      rw [Finset.sum_add_distrib, ← K.din2Cnt_Z, ← K.din3Cnt_Z]; unfold dinCnt; push_cast; rfl
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    rw [K.ptOf_dom i, hd2_dom i]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.din] <;> omega
  have hdmL_sum : (∑ a ∈ S_fin, ((K.ptOf a).dmL (K.d2_l a) : ℤ)) = (K.dmLCnt : ℤ) := by
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.dmLCnt : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) +
        (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      rw [Finset.sum_add_distrib, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z]; unfold dmLCnt; push_cast; rfl
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    rw [K.ptOf_dom i, hd2_dom i]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.dmL, Step15Pt.isML] <;> omega
  have hmu1_sum : (∑ a ∈ S_fin, ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ)) = (K.mu1Cnt : ℤ) := by
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.mu1Cnt : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then (1 : ℤ) else 0) := K.mu1Cnt_Z
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    have hmu_eq : K.muEx_l (ι (BinaryIRSProfile.domain i)) =
        K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) -
          muSub (K.ptOf (ι (BinaryIRSProfile.domain i))) := by
      unfold muEx_l muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
    rw [hmu_eq, K.ptOf_dom i, hd2_dom i]
    by_cases hk1 : D.k i = 1
    · have hk0 : D.k i ≠ 0 := by omega
      by_cases hU : S.isU0 i
      · by_cases hD1 : K.isD1 i
        · simp only [hk1, hk0, hU, hD1, not_true_eq_false, and_true, and_false, false_and, ↓reduceIte, Step15Pt.mu1, Nat.one_ne_zero, Nat.cast_zero]
        · by_cases hM : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
          · have h1 := (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hM)
            simp only [hk1, Nat.one_ne_zero, hU, hD1, hM, not_false_eq_true, and_true, ↓reduceIte, Step15Pt.mu1, muSub]
            rw [sub_zero_nr]; simp only [h1, and_self, ↓reduceIte, Nat.cast_one]
          · have h0 := rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hM)
            simp only [hk1, Nat.one_ne_zero, hU, hD1, hM, not_false_eq_true, and_true, and_false, ↓reduceIte, Step15Pt.mu1, muSub, h0, Nat.zero_sub, show ¬ (1 ≤ 0) by decide, Nat.cast_zero]
      · simp only [hk1, Nat.one_ne_zero, hU, and_false, false_and, ↓reduceIte, Step15Pt.mu1, Nat.cast_zero]
    · simp only [hk1, ↓reduceIte, false_and]; (try split_ifs) <;> simp only [Step15Pt.mu1, Nat.cast_zero]
  have hmuEx_sum : (∑ a ∈ S_fin, (K.muEx_l a : ℤ)) =
      (K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) := by
    let sub : E → ℤ := fun a => (muSub (K.ptOf a) : ℤ)
    have hpt : ∀ a ∈ S_fin, (K.muEx_l a : ℤ) = (K.muRaw_l a : ℤ) - sub a := fun a _ => by
      dsimp [muEx_l, sub]
      cases hpt : K.ptOf a
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · -- k2U: muRaw_l ≥ 1
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; exact Step15Pt.noConfusion ((K.ptOf_out h).symm.trans hpt)
        rcases hdom with ⟨i, rfl⟩
        have hn : K.isNorm i := ((K.ptOf_dom_spec i).2.2.1 hpt).2
        have h1 : 1 ≤ K.muRaw_l (ι (BinaryIRSProfile.domain i)) := by
          unfold muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
          exact (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
        simp only [muSub]; rw [Nat.cast_sub h1]
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · -- k2U_mb: muRaw_l ≥ 2
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; exact Step15Pt.noConfusion ((K.ptOf_out h).symm.trans hpt)
        rcases hdom with ⟨i, rfl⟩
        have hmb : K.isMbad i := ((K.ptOf_dom_spec i).2.2.2.2.1 hpt).2
        have h2 : 2 ≤ K.muRaw_l (ι (BinaryIRSProfile.domain i)) := by
          unfold muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
          exact (le_rootMultiplicity_iff K.hM0s_ne).mpr ((pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2))
        simp only [muSub]; rw [Nat.cast_sub h2]
      · -- k3U: muRaw_l ≥ 1
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; exact Step15Pt.noConfusion ((K.ptOf_out h).symm.trans hpt)
        rcases hdom with ⟨i, rfl⟩
        have hn : K.isNorm i := ((K.ptOf_dom_spec i).2.2.2.2.2.1 hpt).2
        have h1 : 1 ≤ K.muRaw_l (ι (BinaryIRSProfile.domain i)) := by
          unfold muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
          exact (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
        simp only [muSub]; rw [Nat.cast_sub h1]
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · -- k3U_mb: muRaw_l ≥ 2
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; exact Step15Pt.noConfusion ((K.ptOf_out h).symm.trans hpt)
        rcases hdom with ⟨i, rfl⟩
        have hmb : K.isMbad i := ((K.ptOf_dom_spec i).2.2.2.2.2.2.2 hpt).2
        have h2 : 2 ≤ K.muRaw_l (ι (BinaryIRSProfile.domain i)) := by
          unfold muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
          exact (le_rootMultiplicity_iff K.hM0s_ne).mpr ((pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2))
        simp only [muSub]; rw [Nat.cast_sub h2]
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, hM0s_sum]
    have hsub_sum : ∑ a ∈ S_fin, sub a = (S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ) := by
      rw [hsum_dom sub (fun a h => by dsimp [sub]; rw [K.ptOf_out h]; rfl)]
      have hrew : (S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ) =
          ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
            (if K.isMbad i then 1 else 0) - (if K.isML i then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _
      dsimp [sub]; rw [K.ptOf_dom i]
      by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, isMbad, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> dsimp only [muSub] <;> omega
    rw [hsub_sum]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hmu1_sum, ?_, hLam_sum, hdin_sum, hdmL_sum, ?_, ?_, hp1_sum, ?_, hc_sum, he1_sum⟩
  · -- m0
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ) =
        ∑ i : Idx, ((if D.k i = 0 then (1 : ℤ) else 0) + (if D.k i = 1 then 1 else 0) - (if D.k i = 1 ∧ S.isU0 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.m0] <;> omega
  · -- mbad
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.mbadCnt : ℤ) = ∑ i : Idx, (if K.isMbad i then (1 : ℤ) else 0) := K.mbadCnt_Z
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, isMbad, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.mbad] <;> omega
  · -- m1
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (S.n1U : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i then (1 : ℤ) else 0) := n1U_Z
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.m1] <;> omega
  · -- m2
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 then (1 : ℤ) else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.m2] <;> omega
  · -- k3
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (S.n3U : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ S.isU0 i then (1 : ℤ) else 0) := n3U_Z
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.k3] <;> omega
  · -- mL0
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.mLCnt : ℤ) - (K.dmLCnt : ℤ) =
        ∑ i : Idx, ((if K.isML i then (1 : ℤ) else 0) - (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) -
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dmLCnt, Nat.cast_add]; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i, hd2_dom i]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.mL0, Step15Pt.isML] <;> omega
  · -- muO
    have hsplit : ∀ a ∈ S_fin, ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) =
        (K.muEx_l a : ℤ) - ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ) := fun a _ => by
      generalize K.ptOf a = p; generalize K.d2_l a = d; generalize K.muEx_l a = m
      cases p <;> simp only [Step15Pt.muO, Step15Pt.mu1, ↓reduceIte] <;> (try split_ifs) <;> omega
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hmuEx_sum, hmu1_sum]
  · -- d2oth
    have hsplit : ∀ a ∈ S_fin, ((K.ptOf a).d2oth (K.d2_l a) : ℤ) =
        (K.d2_l a : ℤ) - ((K.ptOf a).din (K.d2_l a) : ℤ) - ((K.ptOf a).dmL (K.d2_l a) : ℤ) := fun a _ => by
      have hd := K.d2_l_le_one a
      generalize K.ptOf a = p; generalize K.d2_l a = d at hd ⊢
      cases p <;> simp only [Step15Pt.d2oth, Step15Pt.din, Step15Pt.dmL, Step15Pt.isML,
        Bool.false_eq_true, false_and, true_and, ↓reduceIte] <;> (try split_ifs) <;> omega
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hD1_sum, hdin_sum, hdmL_sum]
  · -- L0
    rw [hsum_dom _ (fun a h => by unfold L0_l; rw [dif_neg h]; rfl)]
    have hrew : 2 * (S.ntU : ℤ) = ∑ i : Idx, (2 * (if S.isU0 i then ((D.k i - 3 : ℕ) : ℤ) else 0)) := by
      rw [← Finset.mul_sum]; apply congrArg (2 * ·); unfold KerD45Syzygy.ntU; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    unfold L0_l; rw [dif_pos ⟨i, rfl⟩]
    have hch : Classical.choose (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
      BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
    rw [hch]
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> (try split_ifs) <;> omega
  · -- LnoU
    rw [hsum_dom _ (fun a h => by unfold LnoU_l; rw [dif_neg h]; rfl)]
    have hrew : 2 * ((D.nt : ℤ) - (S.ntU : ℤ)) =
        ∑ i : Idx, (2 * (((D.k i - 3 : ℕ) : ℤ) - (if S.isU0 i then ((D.k i - 3 : ℕ) : ℤ) else 0))) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]; apply congrArg (2 * ·)
      have h1 : (D.nt : ℤ) = ∑ i : Idx, ((D.k i - 3 : ℕ) : ℤ) := nt_Z
      have h2 : (S.ntU : ℤ) = ∑ i : Idx, (if S.isU0 i then ((D.k i - 3 : ℕ) : ℤ) else 0) := by
        unfold KerD45Syzygy.ntU; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
      rw [h1, h2]
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    unfold LnoU_l; rw [dif_pos ⟨i, rfl⟩]
    have hch : Classical.choose (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
      BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
    rw [hch]
    by_cases hU : S.isU0 i <;> simp only [hU, not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte] <;> (try split_ifs) <;> omega

/-- Master `B1_holds` (`HK.derivative = 0`, NO ODE needed!): proves the exact degree equality AND both `0C_0` and `0C_1` global bounds! -/
theorem b1_holds_bounds (hHK' : K.HK.derivative = 0) :
    K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree - 4 * S.D1.natDegree =
      (D.gj 2).natDegree + K.g2rem.natDegree ∧
    2 * (((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ)) ≤
      2 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 7 * (K.mbadCnt : ℤ) -
      8 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 10 * (S.n3U : ℤ) -
      13 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) + 2 * (K.mu1Cnt : ℤ) +
      10 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
      9 * (K.Lam1.natDegree : ℤ) + 2 * (K.dinCnt : ℤ) - 16 * (K.dmLCnt : ℤ) +
      2 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
      5 * (2 * (S.ntU : ℤ)) - 5 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ))) ∧
    2 * (((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ)) ≤
      2 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 3 * (K.mbadCnt : ℤ) -
      8 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 2 * (S.n3U : ℤ) -
      9 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) + 2 * (K.mu1Cnt : ℤ) +
      10 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
      5 * (K.Lam1.natDegree : ℤ) + 10 * (K.dinCnt : ℤ) - 16 * (K.dmLCnt : ℤ) +
      2 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
      (2 * (S.ntU : ℤ)) - (2 * ((D.nt : ℤ) - (S.ntU : ℤ))) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  obtain ⟨c0, _, _, hc0, _, _, _, _, hd1, _, _, _⟩ := Ndom_decomp
  obtain ⟨r, hr⟩ := (derivative_eq_zero_iff_sq K.HK).mp hHK'
  have hr_u : IsUnit r := K.HK_sqfree r (by rw [hr, sq])
  have hHK_u : IsUnit K.HK := by rw [hr]; exact hr_u.pow 2
  have hHK_deg : K.HK.natDegree = 0 := natDegree_eq_zero_of_isUnit hHK_u
  have hwr := K.HK_wronskian hd1
  rw [hHK', mul_zero, add_zero] at hwr
  have hdeg_eq : K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree - 4 * S.D1.natDegree =
      (D.gj 2).natDegree + K.g2rem.natDegree := by
    have h1 := congrArg Polynomial.natDegree K.HK_decomp
    rw [natDegree_mul (mul_ne_zero K.M0eff_ne D.g2_ne_zero) K.g2rem_ne,
      natDegree_mul K.M0eff_ne D.g2_ne_zero,
      natDegree_mul (pow_ne_zero 2 K.SK_ne) K.HK_ne, natDegree_pow, hHK_deg, add_zero] at h1
    have h2 := congrArg Polynomial.natDegree hwr
    have hp1c := mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne
    have hLc := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
    rw [natDegree_mul (pow_ne_zero 2 K.SK_ne) (mul_ne_zero (C_ne_zero.mpr hc0) K.HK_ne),
      natDegree_pow, natDegree_mul (C_ne_zero.mpr hc0) K.HK_ne, natDegree_C, hHK_deg,
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c)) hLc,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c),
      natDegree_mul (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero),
      natDegree_pow, natDegree_pow, natDegree_pow, natDegree_comp_X_sq, natDegree_comp_X_sq] at h2
    have hp := K.natDegree_p_eq; omega
  let S_fin : Finset E :=
    Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ∪
    ((K.M0s.comp (X ^ 2)).map ι).roots.toFinset ∪ ((K.Lam1.comp (X ^ 2)).map ι).roots.toFinset ∪
    ((K.p1.comp (X ^ 2)).map ι).roots.toFinset ∪ (S.D1.map ι).roots.toFinset ∪
    (K.g2rem.map ι).roots.toFinset ∪ ((D.gj 2).map ι).roots.toFinset
  have hsums := K.sum_step15_cols S_fin
    (fun i => by simp [S_fin, ι, E])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
  have hpt_0C : ∀ a ∈ S_fin,
      (2 * ((K.c_l a : ℤ) - (K.e1_l a : ℤ)) ≤
        2 * ((K.ptOf a).m0 : ℤ) + 7 * ((K.ptOf a).mbad : ℤ) - 8 * ((K.ptOf a).m2 : ℤ) -
        10 * ((K.ptOf a).k3 : ℤ) - 13 * ((K.ptOf a).mL0 (K.d2_l a) : ℤ) +
        2 * ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ) +
        10 * ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) +
        9 * (K.lam_l a : ℤ) + 2 * ((K.ptOf a).din (K.d2_l a) : ℤ) -
        16 * ((K.ptOf a).dmL (K.d2_l a) : ℤ) + 2 * ((K.ptOf a).d2oth (K.d2_l a) : ℤ) -
        5 * (K.L0_l a : ℤ) - 5 * (K.LnoU_l a : ℤ)) ∧
      (2 * ((K.c_l a : ℤ) - (K.e1_l a : ℤ)) ≤
        2 * ((K.ptOf a).m0 : ℤ) + 3 * ((K.ptOf a).mbad : ℤ) - 8 * ((K.ptOf a).m2 : ℤ) -
        2 * ((K.ptOf a).k3 : ℤ) - 9 * ((K.ptOf a).mL0 (K.d2_l a) : ℤ) +
        2 * ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ) +
        10 * ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) +
        5 * (K.lam_l a : ℤ) + 10 * ((K.ptOf a).din (K.d2_l a) : ℤ) -
        16 * ((K.ptOf a).dmL (K.d2_l a) : ℤ) + 2 * ((K.ptOf a).d2oth (K.d2_l a) : ℤ) -
        (K.L0_l a : ℤ) - (K.LnoU_l a : ℤ)) := fun a _ => by
    have hc := K.local_step15_core a
    have hb0 : K.b_l a = 0 := by
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      have hHKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.HK_ne
      have h0 : (K.HK.map ι).natDegree = 0 := by rw [natDegree_map_eq_of_injective ι.injective, hHK_deg]
      have hle := natDegree_le_of_dvd (pow_rootMultiplicity_dvd (K.HK.map ι) a) hHKE
      rw [natDegree_pow, natDegree_X_sub_C, mul_one, h0, hι] at hle; dsimp [b_l]; omega
    have hg_eq : K.g_l a = (K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a := by
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) hwr
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C] at h1
      have hSKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.SK_ne
      have hHKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.HK_ne
      have hME := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne
      have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
      have hp1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne)
      have hLE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne)
      have hc0E : (C (ι c0) : E[X]) ≠ 0 := C_ne_zero.mpr (by intro h0; exact hc0 (ι.injective (by rw [map_zero]; exact h0)))
      rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hSKE) (mul_ne_zero hc0E hHKE)),
        rootMultiplicity_mul (mul_ne_zero hc0E hHKE), rootMultiplicity_C, zero_add,
        rootMultiplicity_pow_eq' _ hSKE 2 a,
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)) hLE),
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)),
        rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)),
        rootMultiplicity_pow_eq' _ hME 2 a, rootMultiplicity_pow_eq' _ hD1E 6 a,
        rootMultiplicity_pow_eq' _ hp1E 5 a,
        K.M0eff_rm_eq_mVal a, rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a,
        rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne a] at h1
      rw [hι] at h1; dsimp [b_l, g_l, lam_l, d2_l, a1_l] at hb0 h1 ⊢; omega
    have htot_0C : K.c_l a + K.e1_l a = (K.ptOf a).mVal + 2 * K.lam_l a + 6 * K.d2_l a + 10 * K.a1_l a := by
      have := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    by_cases hmb : K.ptOf a = .k2U_mb ∨ K.ptOf a = .k3U_mb
    · have hd0 : K.d2_l a = 0 := hc.2.2.2.2.2.2.1 (Or.inr hmb)
      have ha0 : K.a1_l a = 0 :=
        hc.2.2.2.2.2.2.2.1 (hmb.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hd0
      have hLn0 : K.LnoU_l a = 0 := by by_contra h; have := hc.2.2.2.2.2.1 (by omega); rcases hmb with h' | h' <;> rw [h'] at this <;> cases this
      rcases hmb with hpt | hpt
      · have hL0z : K.L0_l a = 0 := by by_contra h; rcases hc.2.2.2.2.1 (by omega) with h' | h' | h' <;> rw [hpt] at h' <;> cases h'
        have htot' : K.c_l a + K.e1_l a = 1 + 2 * K.lam_l a := by
          rw [hpt, hd0, ha0] at htot_0C; simpa [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] using htot_0C
        have h0 := step15_mbad_0C_0 (k3 := 0) (mu_ex := K.muEx_l a) (by omega) hc.2.2.1 (fun _ => hL0z) (fun h => by omega) htot'
        have h1 := step15_mbad_0C_1 (k3 := 0) (mu_ex := K.muEx_l a) (by omega) hc.2.2.1 (fun _ => hL0z) (fun h => by omega) htot'
        rw [hpt, hd0, hL0z, hLn0]
        rw [hL0z] at h0 h1
        simp only [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Bool.false_eq_true, false_and, ↓reduceIte, sub_zero_nr, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
        exact ⟨by linarith only [h0], by linarith only [h1]⟩
      · have hmu3 := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpt
        have htot' : K.c_l a + K.e1_l a = 1 + 2 * K.lam_l a := by
          rw [hpt, hd0, ha0] at htot_0C; simpa [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] using htot_0C
        have h0 := step15_mbad_0C_0 (k3 := 1) (by omega) hc.2.2.1 (fun h => by omega) (fun _ => hmu3) htot'
        have h1 := step15_mbad_0C_1 (k3 := 1) (by omega) hc.2.2.1 (fun h => by omega) (fun _ => hmu3) htot'
        rw [hpt, hd0, hLn0]
        simp only [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Bool.false_eq_true, false_and, ↓reduceIte, sub_zero_nr, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
        exact ⟨by linarith only [h0], by linarith only [h1]⟩
    · have hk3mb_f : K.ptOf a = .k3U_mb → 1 + K.L0_l a ≤ K.lam_l a + K.muEx_l a := fun h => absurd (Or.inr h) hmb
      exact ⟨step15_0C_0 (K.ptOf a) (K.L0_l a) (K.LnoU_l a) (K.a1_l a) (K.d2_l a) (K.muEx_l a) (K.lam_l a) (K.e1_l a) (K.c_l a)
          hc.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hk3mb_f hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 htot_0C hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
        step15_0C_1 (K.ptOf a) (K.L0_l a) (K.LnoU_l a) (K.a1_l a) (K.d2_l a) (K.muEx_l a) (K.lam_l a) (K.e1_l a) (K.c_l a)
          hc.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hk3mb_f hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 htot_0C hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hs0 := Finset.sum_le_sum (fun a ha => (hpt_0C a ha).1)
  have hs1 := Finset.sum_le_sum (fun a ha => (hpt_0C a ha).2)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs0 hs1
  rw [hsums.1, hsums.2.1, hsums.2.2.2.1, hsums.2.2.2.2.1, hsums.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at hs0 hs1
  exact ⟨hdeg_eq, hs0, hs1⟩

/-- Master `ODE_holds` theorem (`zRaw c0 c1 Hrem Qpoly = 0`): proves `row358`, `row359`, `row0A`, AND under `W2a` proves `W2a1` or `W2a2` with `rowC04`! -/
theorem ode_holds_bounds {c0 c1 : Fld} {L : Fld[X]} (hc0 : c0 ≠ 0)
    (hNdom : Ndom = C c0 * X + C c1 * X ^ 2 + L ^ 4)
    (hNdom_deg : Ndom.natDegree = N) (hL4 : 4 * L.natDegree = N)
    (hd1 : Ndom.derivative = C c0)
    (hz : zRaw c0 c1 K.Hrem K.Qpoly = 0) :
    ((D.n1 - K.d2k1UCnt) + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt ≤ K.Lam1.natDegree + K.M0s.natDegree) ∧
    ((D.n1 : ℤ) - (K.d2k1UCnt : ℤ) + (K.mLCnt : ℤ) ≤
      (K.Lam1.natDegree : ℤ) + ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ))) ∧
    (2 * (((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ)) ≤
      2 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 4 * (K.mbadCnt : ℤ) -
      11 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 4 * (S.n3U : ℤ) -
      10 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) +
      11 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
      6 * (K.Lam1.natDegree : ℤ) + 6 * (K.dinCnt : ℤ) - 4 * (K.dmLCnt : ℤ) +
      ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
      2 * (2 * (S.ntU : ℤ)) - 2 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ)))) ∧
    (K.HK.derivative ≠ 0 →
      (3 * (N : ℤ) + 2 * ((D.gj 2).natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ) - 2 * (K.Lam1.natDegree : ℤ) -
        10 * (S.p.natDegree : ℤ) + 4 * (S.D1.natDegree : ℤ) ≤
        4 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 4 * (K.mbadCnt : ℤ) -
        4 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 4 * (S.n3U : ℤ) -
        4 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) +
        4 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
        4 * (K.Lam1.natDegree : ℤ) + 4 * (K.dinCnt : ℤ) +
        4 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
        2 * (2 * (S.ntU : ℤ)) - 2 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ)))) ∨
      (4 * (N : ℤ) + ((D.gj 2).natDegree : ℤ) - ((D.gj 1).natDegree : ℤ) +
        2 * (K.K1.natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ) ≤
        4 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 4 * (K.mbadCnt : ℤ) -
        4 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 4 * (S.n3U : ℤ) -
        4 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) +
        4 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
        4 * (K.Lam1.natDegree : ℤ) + 4 * (K.dinCnt : ℤ) +
        4 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
        2 * (2 * (S.ntU : ℤ)) - 2 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ))))) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  -- Extract minimal 4th-power denominator C0 and ODE decomposition Hrem * C0^4 = Qpoly * (fA^4 + (c0 X + c1 X^2) fB^4)!
  obtain ⟨C0, hC0_ne, ⟨R_ode, hR_ode⟩, hC0_rm⟩ := exists_minimal_fourth_pow_denom K.Hrem K.Qpoly K.Hrem_ne K.Qpoly_ne
  have hode_R := zRaw_eq_zero_imp_poly_ode K.Qpoly_ne hz hR_ode
  have hpow4_Fld : ∀ x : Fld, ∃ y : Fld, y ^ 4 = x := fun x =>
    ⟨(frobEquiv Fld).symm ((frobEquiv Fld).symm x), by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, frobEquiv_symm_sq, frobEquiv_symm_sq]⟩
  obtain ⟨fA, fB, hfAB⟩ := char2_poly_ode_decomp hc0 hpow4_Fld hode_R
  have hPQ_AB : K.Hrem * C0 ^ 4 = K.Qpoly * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4) := by
    rw [hR_ode, hfAB]
  -- Exact cancelled 4th-power Wronskian-ODE identity:
  -- C c0 * (Ndom * D.gj 2)^2 * (fA + L * fB)^4 = (sqrtPoly M0s)^2 * D1^6 * p1(X^2)^5 * Lam1(X^2) * C0^4!
  have hwr4 : C c0 * (Ndom * D.gj 2) ^ 2 * (fA + L * fB) ^ 4 =
      (sqrtPoly K.M0s) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) * C0 ^ 4 := by
    have h1 := char2_wronskian_ode_fourth_pow hNdom hPQ_AB
    have h2 := congrArg (· * K.Shit3 ^ 4) h1
    have h3 := congrArg (· * C0 ^ 4) (K.Hrem_Q_wronskian hd1)
    have hcomb : C c0 * (K.Shit3 ^ 2 * K.Qpoly) ^ 2 * (fA + L * fB) ^ 4 =
        (K.M0 * sqrtPoly K.M0s * Ndom) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) * C0 ^ 4 := by
      calc C c0 * (K.Shit3 ^ 2 * K.Qpoly) ^ 2 * (fA + L * fB) ^ 4
          = (C c0 * K.Qpoly ^ 2 * (fA + L * fB) ^ 4) * K.Shit3 ^ 4 := by ring
        _ = (Ndom * (K.Hrem.derivative * K.Qpoly + K.Hrem * K.Qpoly.derivative) + C c0 * K.Hrem * K.Qpoly) *
              C0 ^ 4 * K.Shit3 ^ 4 := by rw [← h1]
        _ = K.Shit3 ^ 4 * (Ndom * (K.Hrem.derivative * K.Qpoly + K.Hrem * K.Qpoly.derivative) +
              C c0 * K.Hrem * K.Qpoly) * C0 ^ 4 := by ring
        _ = (K.M0 * sqrtPoly K.M0s * Ndom) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) * C0 ^ 4 := h3
    have hSQ : K.Shit3 ^ 2 * K.Qpoly = K.M0 * Ndom ^ 2 * D.gj 2 := by
      unfold Qpoly; rw [K.Ndom_eq_M0_N1_Shit3]; ring
    rw [hSQ] at hcomb
    have hNdom_ne : Ndom ≠ 0 := by
      obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 K.M0_ne) (pow_ne_zero 2 hNdom_ne))
    linear_combination hcomb
  have hwr4_rhs_ne : (sqrtPoly K.M0s) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) * C0 ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (mt (sqrtPoly_eq_zero_iff K.M0s).mp K.hM0s_ne))
      (pow_ne_zero 6 S.D1_ne_zero))
      (pow_ne_zero 5 (mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne)))
      (mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne))
      (pow_ne_zero 4 hC0_ne)
  have hfAL_ne : fA + L * fB ≠ 0 := by
    intro h0; apply hwr4_rhs_ne; rw [← hwr4, h0, zero_pow (show (4 : ℕ) ≠ 0 by norm_num), mul_zero]
  -- Pointwise hSmod, hb1, and hode at EVERY a ∈ E!
  have hpt_ode_all : ∀ a : E,
      (K.g_l a % 2 = ((K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a) % 2) ∧
      ((K.ptOf a).nu = 1 → K.b_l a = 1 → K.g_l a + 2 ≤ (K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a) ∧
      ((K.ptOf a).mbad = 0 →
        (K.ptOf a).vChat (K.muEx_l a) (K.e1_l a) (K.c_l a) % 4 ≠ 1 ∧
        (K.ptOf a).vChat (K.muEx_l a) (K.e1_l a) (K.c_l a) % 4 ≠ 2) := by
    intro a
    have hc := K.local_step15_core a
    -- Mod-4 valuation of Hrem + 3 * Qpoly!
    have hmod4 : ((K.Hrem.map ι).rootMultiplicity a + 3 * (K.Qpoly.map ι).rootMultiplicity a) % 4 = 0 ∨
        ((K.Hrem.map ι).rootMultiplicity a + 3 * (K.Qpoly.map ι).rootMultiplicity a) % 4 = 1 := by
      have hzE : zRaw (ι c0) (ι c1) (K.Hrem.map ι) (K.Qpoly.map ι) = 0 := by
        rw [zRaw_map, hz, Polynomial.map_zero]
      exact ode_mod4_of_zRaw_zero (by intro h0; exact hc0 (ι.injective (by rw [map_zero]; exact h0)))
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.Hrem_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.Qpoly_ne) hzE a
    -- Exact mod-2 parity of c_l a from hwr4!
    have hc_mod2 : (K.c_l a + (K.ptOf a).nu) % 2 = (K.muRaw_l a + 3 * K.d2_l a + 5 * K.a1_l a + K.lam_l a) % 2 := by
      have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) hwr4
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C] at h1
      have hNdom_ne : Ndom ≠ 0 := by obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
      have hNE := (Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne
      have hg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
      have hfE := (Polynomial.map_ne_zero_iff ι.injective).mpr hfAL_ne
      have hc0E : (C (ι c0) : E[X]) ≠ 0 := C_ne_zero.mpr (by intro h0; exact hc0 (ι.injective (by rw [map_zero]; exact h0)))
      have hsME := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (sqrtPoly_eq_zero_iff K.M0s).mp K.hM0s_ne)
      have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
      have hp1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne)
      have hLE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne)
      have hC0E := (Polynomial.map_ne_zero_iff ι.injective).mpr hC0_ne
      rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hc0E (pow_ne_zero 2 (mul_ne_zero hNE hg2E))) (pow_ne_zero 4 hfE)),
        rootMultiplicity_mul (mul_ne_zero hc0E (pow_ne_zero 2 (mul_ne_zero hNE hg2E))),
        rootMultiplicity_C, zero_add,
        rootMultiplicity_pow_eq' _ (mul_ne_zero hNE hg2E) 2 a,
        rootMultiplicity_mul (mul_ne_zero hNE hg2E),
        rootMultiplicity_pow_eq' _ hfE 4 a,
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)) hLE) (pow_ne_zero 4 hC0E)),
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)) hLE),
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)),
        rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hsME) (pow_ne_zero 6 hD1E)),
        rootMultiplicity_pow_eq' _ hsME 2 a, rootMultiplicity_pow_eq' _ hD1E 6 a,
        rootMultiplicity_pow_eq' _ hp1E 5 a, rootMultiplicity_pow_eq' _ hC0E 4 a,
        rootMultiplicity_sqrtPoly_map K.M0s K.hM0s_ne a,
        rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a,
        rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne a] at h1
      have hN_rm : (Ndom.map ι).rootMultiplicity a = (K.ptOf a).nu := by
        unfold Ndom; rw [show (∏ i : Idx, (X - C (BinaryIRSProfile.domain i))) = linProd Finset.univ from rfl, linProd_rm]
        by_cases h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
        · rcases h with ⟨i, rfl⟩; rw [if_pos ⟨i, Finset.mem_univ i, rfl⟩, K.ptOf_dom i]; split_ifs <;> rfl
        · rw [if_neg (fun ⟨i, _, hi⟩ => h ⟨i, hi⟩), K.ptOf_out h]; rfl
      rw [hN_rm] at h1
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      rw [hι] at h1; dsimp [c_l, muRaw_l, d2_l, a1_l, lam_l] at h1 ⊢; omega
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [hι] at hmod4
    have hvsub := K.v_Q_sub_Hrem a
    have htot := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hb_le := hc.2.1
    have hSmod : K.g_l a % 2 = ((K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a) % 2 := by omega
    have hb1 : (K.ptOf a).nu = 1 → K.b_l a = 1 → K.g_l a + 2 ≤ (K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a := by
      intro hnu1 hb1'
      have hNa : (Ndom.map ι).eval a = 0 := by
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; rw [K.ptOf_out h] at hnu1; cases hnu1
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hev⟩ := Ndom_decomp
        exact (hev a).mpr hdom
      have hHa : (K.HK.map ι).eval a = 0 := by
        have hge1 : 1 ≤ (K.HK.map ι).rootMultiplicity a := by rw [hι]; dsimp [b_l] at hb1'; omega
        have hd := (pow_dvd_pow (X - C a) hge1).trans (pow_rootMultiplicity_dvd (K.HK.map ι) a)
        rw [pow_one] at hd; exact dvd_iff_isRoot.mp hd
      have hd1E : (Ndom.map ι).derivative = C (ι c0) := by rw [derivative_map, hd1, Polynomial.map_C]
      have hsq_dvd := wronskian_sq_dvd_of_common_root hd1E a hNa hHa
      have hwr := congrArg (Polynomial.map ι) (K.HK_wronskian hd1)
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, ← derivative_map] at hwr
      have hRHS_ne : (K.M0eff.map ι) ^ 2 * (S.D1.map ι) ^ 6 * ((K.p1.comp (X ^ 2)).map ι) ^ 5 *
          ((K.Lam1.comp (X ^ 2)).map ι) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero
          (pow_ne_zero 2 ((Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne))
          (pow_ne_zero 6 ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero)))
          (pow_ne_zero 5 ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne))))
          ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne))
      have hd_tot : (X - C a) ^ (2 * K.g_l a + 2) ∣ (K.M0eff.map ι) ^ 2 * (S.D1.map ι) ^ 6 *
          ((K.p1.comp (X ^ 2)).map ι) ^ 5 * ((K.Lam1.comp (X ^ 2)).map ι) := by
        rw [← hwr, pow_add, mul_comm 2 (K.g_l a), pow_mul]
        have hg_eq' : K.g_l a = (K.SK.map ι).rootMultiplicity a := by rw [hι]; rfl
        rw [hg_eq']
        exact mul_dvd_mul (pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd (K.SK.map ι) a) 2) hsq_dvd
      have hle := (le_rootMultiplicity_iff hRHS_ne).mpr hd_tot
      have hME := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne
      have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
      have hp1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne)
      have hLE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne)
      rw [rootMultiplicity_mul hRHS_ne,
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)),
        rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)),
        rootMultiplicity_pow_eq' _ hME 2 a, rootMultiplicity_pow_eq' _ hD1E 6 a,
        rootMultiplicity_pow_eq' _ hp1E 5 a,
        K.M0eff_rm_eq_mVal a, rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a,
        rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne a] at hle
      rw [hι] at hle; dsimp [lam_l, d2_l, a1_l] at hSmod hle ⊢; omega
    have hode_vChat : (K.ptOf a).mbad = 0 →
        (K.ptOf a).vChat (K.muEx_l a) (K.e1_l a) (K.c_l a) % 4 ≠ 1 ∧
        (K.ptOf a).vChat (K.muEx_l a) (K.e1_l a) (K.c_l a) % 4 ≠ 2 := fun hmb0 => by
      rw [hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hmb0]; omega
    exact ⟨hSmod, hb1, hode_vChat⟩
  -- Key ODE_holds bonus: at EVERY k=1, U=0, d2=0 point, 1 ≤ v_T(Lam1 * M0s)!
  have hk1U_bonus : ∀ i : Idx, D.k i = 1 → S.isU0 i → ¬ K.isD1 i →
      1 ≤ (K.Lam1 * K.M0s).rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
    intro i hk1 hU hD1
    by_contra h0
    have hrm0 : (K.Lam1 * K.M0s).rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 := by omega
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne)] at hrm0
    set a := ι (BinaryIRSProfile.domain i)
    have hpt : K.ptOf a = .k1U := by rw [K.ptOf_dom i]; simp [hk1, hU]
    have hd0 : K.d2_l a = 0 := by dsimp [d2_l, a]; rw [rootMultiplicity_map_eq]; exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hD1)
    have hlam0 : K.lam_l a = 0 := by dsimp [lam_l, a]; rw [← map_pow, rootMultiplicity_map_eq]; omega
    have hmu0 : K.muEx_l a = 0 := by
      have hM0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 := (Nat.add_eq_zero.mp hrm0).2
      unfold muEx_l muRaw_l; rw [show a = ι (BinaryIRSProfile.domain i) from rfl, ← map_pow, rootMultiplicity_map_eq, hM0]
      exact Nat.zero_sub _
    have hc := K.local_step15_core a
    have ho := hpt_ode_all a
    have ha0 : K.a1_l a = 0 := hc.2.2.2.2.2.2.2.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpt)))))) hd0
    have he1 : 1 ≤ K.e1_l a := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpt (Or.inr hmu0)
    have hS := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have htot := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hSmod := ho.1
    have hb1 := ho.2.1
    have hode := ho.2.2 (by rw [hpt]; rfl)
    simp only [hpt, hd0, hlam0, hmu0, ha0] at hS htot hSmod hb1 hode
    simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
      Step15Pt.vChat, Step15Pt.isML] at hS htot hSmod hb1 hode
    have hb_le := hc.2.1
    rcases (show K.b_l a = 0 ∨ K.b_l a = 1 by omega) with hb | hb
    · rw [hb] at htot; omega
    · have := hb1 hb; omega
  -- Row 358 and Row 359 from hk1U_bonus!
  have hrow358 : (D.n1 - K.d2k1UCnt) + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt ≤
      K.Lam1.natDegree + K.M0s.natDegree := by
    let f : Idx → ℕ := fun i =>
      if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i then 1
      else if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)
      else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2)
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.Lam1 * K.M0s := fun i _ => by
      dsimp only [f]
      by_cases h1 : D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i
      · simp only [h1, ↓reduceIte]
        exact (pow_dvd_pow _ (hk1U_bonus i h1.1 h1.2.1 h1.2.2)).trans (pow_rootMultiplicity_dvd _ _)
      · simp only [h1, ↓reduceIte]
        exact K.pow_dvd_Lam1_mul_M0s i
    have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective (K.Lam1 * K.M0s) (mul_ne_zero K.hLam1_ne K.hM0s_ne) f hdvd
    rw [natDegree_mul K.hLam1_ne K.hM0s_ne] at hle
    have hU := S.U_counts_ineqs
    have hd2_le_n1 : K.d2k1UCnt ≤ D.n1 := by
      have hZ : (K.d2k1UCnt : ℤ) ≤ (D.n1 : ℤ) := by
        rw [K.d2k1UCnt_Z, n1_Z]
        apply Finset.sum_le_sum; intro i _
        by_cases hU' : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
          simp only [hU', hD1, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
          (try split_ifs) <;> omega
      omega
    have hZ : (((D.n1 : ℤ) - (K.d2k1UCnt : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
        (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
      have hrew : ((D.n1 : ℤ) - (K.d2k1UCnt : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
          (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
          ∑ i : Idx, ((if D.k i = 1 then (1 : ℤ) else 0) - (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
            2 * (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
            4 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
            2 * ((D.k i - 3 : ℕ) : ℤ)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
      by_cases hU' : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        simp only [hU', hD1, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    have hleZ : (∑ i : Idx, (f i : ℤ)) ≤ (K.Lam1.natDegree : ℤ) + (K.M0s.natDegree : ℤ) := by exact_mod_cast hle
    rw [← hZ] at hleZ
    have h2 : S.n2U ≤ 2 * D.n2 := by have := hU.2.1; omega
    have h3 : S.n3U ≤ 4 * D.n3 := by have := hU.2.2.1; omega
    have hgoalZ : (((D.n1 - K.d2k1UCnt) + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt : ℕ) : ℤ) ≤
        ((K.Lam1.natDegree + K.M0s.natDegree : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_sub hd2_le_n1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_mul, Nat.cast_ofNat]
      linarith only [hleZ]
    exact_mod_cast hgoalZ
  have hrow359 : (D.n1 : ℤ) - (K.d2k1UCnt : ℤ) + (K.mLCnt : ℤ) ≤
      (K.Lam1.natDegree : ℤ) + ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ)) := by
    let f : Idx → ℕ := fun i =>
      if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i then 1
      else if D.k i = 1 ∧ ¬ S.isU0 i then 1
      else if K.isMbad i then 2
      else if 2 ≤ D.k i ∧ S.isU0 i then 1
      else 0
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.Lam1 * K.M0s := fun i _ => by
      dsimp [f]; split_ifs with h1 h2 hmb hk2U
      · exact (pow_dvd_pow _ (hk1U_bonus i h1.1 h1.2.1 h1.2.2)).trans (pow_rootMultiplicity_dvd _ _)
      · have h := K.pow_dvd_Lam1_mul_M0s i; simp only [h2.1, h2.2, Nat.one_ne_zero, ↓reduceIte] at h; exact h
      · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2)) K.Lam1
      · have h := K.pow_dvd_Lam1_mul_M0s i
        simp only [hk2U.2, show ¬ D.k i ≤ 1 by have := hk2U.1; omega, ↓reduceIte] at h
        exact (pow_dvd_pow _ (by have := hk2U.1; omega : 1 ≤ 2 * D.k i - 3)).trans h
      · simp
    have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective (K.Lam1 * K.M0s) (mul_ne_zero K.hLam1_ne K.hM0s_ne) f hdvd
    rw [natDegree_mul K.hLam1_ne K.hM0s_ne] at hle
    have hZ : ((D.n1 : ℤ) - (K.d2k1UCnt : ℤ) + (S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
      have hrew : (D.n1 : ℤ) - (K.d2k1UCnt : ℤ) + (S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) =
          ∑ i : Idx, ((if D.k i = 1 then (1 : ℤ) else 0) - (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
            (if D.k i = 2 ∧ S.isU0 i then 1 else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
            (if K.isMbad i then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
      by_cases hU' : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        simp only [isMbad, hU', hD1, hg, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    have hleZ : (∑ i : Idx, (f i : ℤ)) ≤ (K.Lam1.natDegree : ℤ) + (K.M0s.natDegree : ℤ) := by exact_mod_cast hle
    rw [← hZ] at hleZ; linarith only [hleZ]
  -- Global sum of 0A and C04 over S_fin!
  let S_fin : Finset E :=
    Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ∪
    ((K.M0s.comp (X ^ 2)).map ι).roots.toFinset ∪ ((K.Lam1.comp (X ^ 2)).map ι).roots.toFinset ∪
    ((K.p1.comp (X ^ 2)).map ι).roots.toFinset ∪ (S.D1.map ι).roots.toFinset ∪
    (K.g2rem.map ι).roots.toFinset ∪ ((D.gj 2).map ι).roots.toFinset ∪ (C0.map ι).roots.toFinset
  have hsums := K.sum_step15_cols S_fin
    (fun i => by simp [S_fin, ι, E])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
  have hC0_sum : (∑ a ∈ S_fin, ((C0.map ι).rootMultiplicity a : ℤ)) = (C0.natDegree : ℤ) := by
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [hι]
    exact_mod_cast sum_rootMultiplicity_map_eq_natDegree C0 hC0_ne S_fin (fun a ha => by simp [S_fin, ι, E, ha])
  have hpt_0A_C04 : ∀ a ∈ S_fin,
      (2 * ((K.c_l a : ℤ) - (K.e1_l a : ℤ)) ≤
        2 * ((K.ptOf a).m0 : ℤ) + 4 * ((K.ptOf a).mbad : ℤ) - 11 * ((K.ptOf a).m2 : ℤ) -
        4 * ((K.ptOf a).k3 : ℤ) - 10 * ((K.ptOf a).mL0 (K.d2_l a) : ℤ) +
        11 * ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) + 6 * (K.lam_l a : ℤ) +
        6 * ((K.ptOf a).din (K.d2_l a) : ℤ) - 4 * ((K.ptOf a).dmL (K.d2_l a) : ℤ) +
        ((K.ptOf a).d2oth (K.d2_l a) : ℤ) - 2 * (K.L0_l a : ℤ) - 2 * (K.LnoU_l a : ℤ)) ∧
      ((4 * (C0.map ι).rootMultiplicity a : ℤ) ≤
        4 * ((K.ptOf a).m0 : ℤ) + 4 * ((K.ptOf a).mbad : ℤ) - 4 * ((K.ptOf a).m2 : ℤ) -
        4 * ((K.ptOf a).k3 : ℤ) - 4 * ((K.ptOf a).mL0 (K.d2_l a) : ℤ) +
        4 * ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) + 4 * (K.lam_l a : ℤ) +
        4 * ((K.ptOf a).din (K.d2_l a) : ℤ) + 4 * ((K.ptOf a).d2oth (K.d2_l a) : ℤ) -
        2 * (K.L0_l a : ℤ) - 2 * (K.LnoU_l a : ℤ)) := fun a _ => by
    have hc := K.local_step15_core a
    have ho := hpt_ode_all a
    have hC0_a : (4 * (C0.map ι).rootMultiplicity a : ℤ) =
        (Step15Pt.c04Val (((K.Qpoly.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
          ((K.Hrem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ)) : ℤ) := by
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      rw [hι]; exact_mod_cast hC0_rm a
    rw [hC0_a]
    by_cases hmb : K.ptOf a = .k2U_mb ∨ K.ptOf a = .k3U_mb
    · have hd0 : K.d2_l a = 0 := hc.2.2.2.2.2.2.1 (Or.inr hmb)
      have ha0 : K.a1_l a = 0 :=
        hc.2.2.2.2.2.2.2.1 (hmb.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hd0
      have hLn0 : K.LnoU_l a = 0 := by by_contra h; have := hc.2.2.2.2.2.1 (by omega); rcases hmb with h' | h' <;> rw [h'] at this <;> cases this
      have hv := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rcases hmb with h | h <;> rw [h] <;> rfl)
      rw [← hv]
      have hS := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have htot := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hb1 := ho.2.1
      rcases hmb with hpt | hpt
      · have hL0z : K.L0_l a = 0 := by by_contra h; rcases hc.2.2.2.2.1 (by omega) with h' | h' | h' <;> rw [hpt] at h' <;> cases h'
        simp only [hpt, hd0, ha0] at hS htot hb1
        simp only [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] at hS htot hb1
        have h0 := step15_mbad_0A (k3 := 0) (mu_ex := K.muEx_l a) (by omega) hc.2.1 hc.2.2.1 (fun _ => hL0z) (fun h => by omega)
          (by omega) (fun hb' => by have := hb1 trivial hb'; omega) (by omega)
        have h1 := step15_mbad_C04 (k3 := 0) (mu_ex := K.muEx_l a) (by omega) hc.2.1 hc.2.2.1 (fun _ => hL0z) (fun h => by omega)
          (by omega) (fun hb' => by have := hb1 trivial hb'; omega) (by omega)
        rw [hpt, hd0, hL0z, hLn0]
        rw [hL0z] at h0 h1
        simp only [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Bool.false_eq_true, false_and, ↓reduceIte, sub_zero_nr, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
        exact ⟨by linarith only [h0], by linarith only [h1]⟩
      · have hmu3 := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpt
        simp only [hpt, hd0, ha0] at hS htot hb1
        simp only [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] at hS htot hb1
        have h0 := step15_mbad_0A (k3 := 1) (by omega) hc.2.1 hc.2.2.1 (fun h => by omega) (fun _ => hmu3)
          (by omega) (fun hb' => by have := hb1 trivial hb'; omega) (by omega)
        have h1 := step15_mbad_C04 (k3 := 1) (by omega) hc.2.1 hc.2.2.1 (fun h => by omega) (fun _ => hmu3)
          (by omega) (fun hb' => by have := hb1 trivial hb'; omega) (by omega)
        rw [hpt, hd0, hLn0]
        simp only [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Bool.false_eq_true, false_and, ↓reduceIte, sub_zero_nr, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
        exact ⟨by linarith only [h0], by linarith only [h1]⟩
    · have hmb0 : (K.ptOf a).mbad = 0 := by
        cases hpt : K.ptOf a <;> first | rfl | exact absurd (Or.inl hpt) hmb | exact absurd (Or.inr hpt) hmb
      have hv := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hmb0
      rw [← hv]
      have hk3mb_f : K.ptOf a = .k3U_mb → 1 + K.L0_l a ≤ K.lam_l a + K.muEx_l a := fun h => absurd (Or.inr h) hmb
      have hk2mb_f : K.ptOf a = .k2U_mb → 2 ≤ K.muEx_l a := fun h => absurd (Or.inl h) hmb
      have hk3mb_m : K.ptOf a = .k3U_mb → 3 + K.L0_l a / 2 ≤ K.muEx_l a := fun h => absurd (Or.inr h) hmb
      exact ⟨step15_0A (K.ptOf a) (K.L0_l a) (K.LnoU_l a) (K.a1_l a) (K.d2_l a) (K.muEx_l a) (K.lam_l a)
          (K.g_l a) (K.b_l a) (K.e1_l a) (K.c_l a)
          hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hk3mb_f hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho.1 ho.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho.2.2 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
        step15_C04 (K.ptOf a) (K.L0_l a) (K.LnoU_l a) (K.a1_l a) (K.d2_l a) (K.muEx_l a) (K.lam_l a)
          (K.g_l a) (K.b_l a) (K.e1_l a) (K.c_l a)
          hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hk3mb_f hk2mb_f hk3mb_m hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho.1 ho.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho.2.2 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have h0A_sum := Finset.sum_le_sum (fun a ha => (hpt_0A_C04 a ha).1)
  have hC04_sum := Finset.sum_le_sum (fun a ha => (hpt_0A_C04 a ha).2)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h0A_sum hC04_sum
  rw [hsums.1, hsums.2.1, hsums.2.2.2.1, hsums.2.2.2.2.1, hsums.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at h0A_sum
  rw [hC0_sum, hsums.1, hsums.2.1, hsums.2.2.2.1, hsums.2.2.2.2.1, hsums.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hC04_sum
  refine ⟨hrow358, hrow359, h0A_sum, fun hHK'_ne => ?_⟩
  -- Show fB ≠ 0 whenever HK' ≠ 0!
  have hfB_ne : fB ≠ 0 := by
    intro hfB0; apply hHK'_ne
    rw [hfB0, zero_pow (show (4 : ℕ) ≠ 0 by norm_num), mul_zero, add_zero] at hPQ_AB
    have hsq : (K.Shit3 ^ 2 * K.Qpoly * fA ^ 2) ^ 2 = (K.M0 * sqrtPoly K.M0s * K.Sg2 * K.SK * C0 ^ 2) ^ 2 * K.HK := by
      have hbr := K.Hrem_Q_bridge
      have h1 : Ndom * (K.g2t * D.gj 2) = K.Sg2 ^ 2 * K.SK ^ 2 * K.HK := by
        calc Ndom * (K.g2t * D.gj 2) = (K.M0eff * K.Sg2) * (K.Sg2 * K.g2rem * D.gj 2) := by
              rw [← K.Ndom_eq_M0eff_Sg2, ← K.g2t_eq_Sg2_mul_g2rem]
          _ = K.Sg2 ^ 2 * (K.M0eff * D.gj 2 * K.g2rem) := by ring
          _ = K.Sg2 ^ 2 * K.SK ^ 2 * K.HK := by rw [K.HK_decomp]; ring
      rw [mul_assoc _ Ndom, h1] at hbr
      calc (K.Shit3 ^ 2 * K.Qpoly * fA ^ 2) ^ 2
          = K.Shit3 ^ 4 * K.Qpoly * (K.Qpoly * fA ^ 4) := by ring
        _ = K.Shit3 ^ 4 * K.Qpoly * (K.Hrem * C0 ^ 4) := by rw [← hPQ_AB]
        _ = (K.Shit3 ^ 4 * (K.Hrem * K.Qpoly)) * C0 ^ 4 := by ring
        _ = (K.M0 * sqrtPoly K.M0s * K.Sg2 * K.SK * C0 ^ 2) ^ 2 * K.HK := by rw [hbr]; ring
    have hd := congrArg Polynomial.derivative hsq
    rw [char2_derivative_sq, derivative_mul, char2_derivative_sq, zero_mul, zero_add] at hd
    have hfac_ne : (K.M0 * sqrtPoly K.M0s * K.Sg2 * K.SK * C0 ^ 2) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero K.M0_ne
        (mt (sqrtPoly_eq_zero_iff K.M0s).mp K.hM0s_ne)) K.Sg2_ne) K.SK_ne) (pow_ne_zero 2 hC0_ne))
    exact (mul_eq_zero.mp hd.symm).resolve_left hfac_ne
  have hL_ge : 1 ≤ L.natDegree := by
    have hN4 : 4 ≤ N := by norm_num [N]
    omega
  rcases char2_wronskian_ode_W2a_dichotomy hL_ge hfB_ne hC0_ne K.Qpoly_ne hPQ_AB with ⟨_, hW1⟩ | hW2
  · left
    have hNdom_ne : Ndom ≠ 0 := by obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
    have hdeg_wr := congrArg Polynomial.natDegree hwr4
    have hp1c := mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne
    have hLc := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
    have hsM := mt (sqrtPoly_eq_zero_iff K.M0s).mp K.hM0s_ne
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hc0) (pow_ne_zero 2 (mul_ne_zero hNdom_ne D.g2_ne_zero))) (pow_ne_zero 4 hfAL_ne),
      natDegree_mul (C_ne_zero.mpr hc0) (pow_ne_zero 2 (mul_ne_zero hNdom_ne D.g2_ne_zero)),
      natDegree_C, zero_add, natDegree_pow, natDegree_mul hNdom_ne D.g2_ne_zero, hNdom_deg, natDegree_pow,
      natDegree_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsM) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c)) hLc) (pow_ne_zero 4 hC0_ne),
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsM) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c)) hLc,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 hsM) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c),
      natDegree_mul (pow_ne_zero 2 hsM) (pow_ne_zero 6 S.D1_ne_zero),
      natDegree_pow, natDegree_pow, natDegree_pow, natDegree_pow,
      natDegree_sqrtPoly, natDegree_comp_X_sq, natDegree_comp_X_sq] at hdeg_wr
    have hp := K.natDegree_p_eq
    linarith [hC04_sum, show (3 * (N : ℤ) + 2 * ((D.gj 2).natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ) -
      2 * (K.Lam1.natDegree : ℤ) - 10 * (S.p.natDegree : ℤ) + 4 * (S.D1.natDegree : ℤ)) ≤ 4 * (C0.natDegree : ℤ) by omega]
  · right
    have hQdeg : K.Qpoly.natDegree = 3 * K.M0.natDegree + 2 * K.N1.natDegree + (D.gj 2).natDegree := by
      unfold Qpoly
      rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 K.M0_ne) (pow_ne_zero 2 K.N1_ne)) D.g2_ne_zero,
        natDegree_mul (pow_ne_zero 3 K.M0_ne) (pow_ne_zero 2 K.N1_ne), natDegree_pow, natDegree_pow]
    have hNsum : K.M0.natDegree + K.N1.natDegree + K.Shit3.natDegree = N := by
      have h := congrArg Polynomial.natDegree K.Ndom_eq_M0_N1_Shit3
      rw [hNdom_deg, natDegree_mul (mul_ne_zero K.M0_ne K.N1_ne) K.Shit3_ne,
        natDegree_mul K.M0_ne K.N1_ne] at h; exact h.symm
    have hHrdeg : K.N1.natDegree + 3 * K.Shit3.natDegree + K.Hrem.natDegree = 2 * K.M0s.natDegree + K.g2t.natDegree := by
      have h := congrArg Polynomial.natDegree K.Hraw_eq_N1_Shit3_Hrem
      rw [natDegree_mul (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne, natDegree_comp_X_sq,
        natDegree_mul (mul_ne_zero K.N1_ne (pow_ne_zero 3 K.Shit3_ne)) K.Hrem_ne,
        natDegree_mul K.N1_ne (pow_ne_zero 3 K.Shit3_ne), natDegree_pow] at h; omega
    have hg1 := K.natDegree_g1_eq
    linarith [hC04_sum, show (4 * (N : ℤ) + ((D.gj 2).natDegree : ℤ) - ((D.gj 1).natDegree : ℤ) +
      2 * (K.K1.natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ)) ≤ 4 * (C0.natDegree : ℤ) by omega]

/-- Master `ODE_fail` theorem (`zRaw c0 c1 Hrem Qpoly ≠ 0`): proves line 378–380 of `B6401T4Rows`! -/
theorem ode_fail_bound {c0 c1 : Fld} (hd1 : Ndom.derivative = C c0) (hd2 : hasse 2 Ndom = C c1)
    (hz : zRaw c0 c1 K.Hrem K.Qpoly ≠ 0) :
    4 * (S.p.natDegree : ℤ) - 4 * (S.D1.natDegree : ℤ) + 4 * (K.din2Cnt : ℤ) +
      4 * (K.d2k1UCnt : ℤ) + 4 * (K.dmLCnt : ℤ) + 5 * (K.d2k0Cnt : ℤ) -
      2 * (D.n0 : ℤ) - 2 * (D.n1 : ℤ) + 2 * (S.n1U : ℤ) + 2 * (D.n3 : ℤ) + 6 * (D.nt : ℤ) ≤
      (K.Hrem.natDegree : ℤ) + 2 * (K.N1.natDegree : ℤ) + 2 * ((D.gj 2).natDegree : ℤ) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  obtain ⟨Z_ode, hZ_eq⟩ := pow5_mul_sq_dvd_zRaw c0 c1 K.Hrem K.M0 K.N1 (D.gj 2)
  have hZ_ne : Z_ode ≠ 0 := by intro h0; apply hz; unfold Qpoly; rw [hZ_eq, h0, mul_zero]
  have hZ_deg := natDegree_zOde_pow5_le K.M0_ne K.N1_ne D.g2_ne_zero hZ_ne hZ_eq
  -- Sum over S_fin in E = AlgebraicClosure Fld!
  let S_fin : Finset E :=
    Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ∪
    ((sqrtPoly K.p1).map ι).roots.toFinset ∪ (Z_ode.map ι).roots.toFinset
  have hA1_ne : sqrtPoly K.p1 ≠ 0 := mt (sqrtPoly_eq_zero_iff K.p1).mp K.hp1_ne
  have hNdom_ne : Ndom ≠ 0 := by obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
  have hNdom_rm1 : ∀ i : Idx, Ndom.rootMultiplicity (BinaryIRSProfile.domain i) = 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h1, _⟩ := Ndom_decomp; exact h1
  have hNdom_ev : ∀ a : E, (Ndom.map ι).eval a = 0 ↔ ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hev⟩ := Ndom_decomp; exact hev
  have hd1E : (Ndom.map ι).derivative = C (ι c0) := by rw [derivative_map, hd1, Polynomial.map_C]
  have hd2E : hasse 2 (Ndom.map ι) = C (ι c1) := by
    rw [hasse_map_eq, hd2, Polynomial.map_C]
  have hdivE : zRaw (ι c0) (ι c1) (K.Hrem.map ι) ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * ((D.gj 2).map ι)) =
      (K.M0.map ι) ^ 5 * (K.N1.map ι) ^ 2 * (Z_ode.map ι) := by
    rw [show (K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * ((D.gj 2).map ι) = (K.M0 ^ 3 * K.N1 ^ 2 * D.gj 2).map ι by
      simp only [Polynomial.map_mul, Polynomial.map_pow]]
    rw [zRaw_map, hZ_eq]
    simp only [Polynomial.map_mul, Polynomial.map_pow]
  -- Pointwise lower bound on (Z_ode.map ι).rootMultiplicity a - (M0.map ι).rootMultiplicity a!
  let bonus : E → ℤ := fun a =>
    if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then
      let i := Classical.choose h
      4 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
      4 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
      4 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
      4 * (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
      5 * (if D.k i = 0 ∧ K.isD1 i then 1 else 0) -
      2 * (if D.k i = 0 then 1 else 0) -
      2 * (if D.k i = 1 then 1 else 0) +
      2 * (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
      2 * (if 3 ≤ D.k i then 1 else 0) + 6 * ((D.k i - 3 : ℕ) : ℤ)
    else 0
  have hpt : ∀ a ∈ S_fin,
      4 * (((sqrtPoly K.p1).map ι).rootMultiplicity a : ℤ) + bonus a ≤
        ((Z_ode.map ι).rootMultiplicity a : ℤ) - ((K.M0.map ι).rootMultiplicity a : ℤ) := fun a _ => by
    by_cases hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
    · rcases hdom with ⟨i, rfl⟩
      have hch : Classical.choose (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
      dsimp [bonus]; rw [dif_pos ⟨i, rfl⟩, hch]
      set y0 := D.y i
      let Uy0 : Fld[X] := S.p.comp (X ^ 2) * C y0 + S.R
      let U1_y0 : Fld[X] := S.D1 * K.p1.comp (X ^ 2) * C y0 + K.R1
      let R_raw : Fld[X] := S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 2 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
        Uy0 ^ 2 * D.gj 1
      have hid0 : K.Hrem * Ndom ^ 3 + (sqrtPoly K.p1) ^ 4 * (K.M0 ^ 3 * K.N1 ^ 2 * R_raw) = K.Qpoly * U1_y0 ^ 4 :=
        K.Hrem_Q_ode_fail_id y0
      have heqE : (K.Hrem.map ι) * (Ndom.map ι) ^ 3 + ((sqrtPoly K.p1).map ι) ^ 4 *
          ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * (R_raw.map ι)) =
          ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * ((D.gj 2).map ι)) * (U1_y0.map ι) ^ 4 := by
        have h := congrArg (Polynomial.map ι) hid0
        unfold Qpoly at h; simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] at h; exact h
      have hN1a : (Ndom.map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) = 1 := by
        rw [rootMultiplicity_map_eq]; exact hNdom_rm1 i
      have hbound := (rootMultiplicity_zOde_ge
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.M0_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr hZ_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne)
        hd1E hd2E hdivE heqE (ι (BinaryIRSProfile.domain i))).2 hN1a
      have hM0_rm : (K.M0.map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) =
          if D.k i = 0 ∨ ¬ S.isU0 i then 1 else 0 := by
        unfold M0; rw [linProd_rm]
        have hm : (∃ j ∈ K.I_M0, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) ↔ i ∈ K.I_M0 :=
          ⟨fun ⟨j, hj, heq⟩ => by rwa [BinaryIRSProfile.domain.injective (ι.injective heq)], fun hi => ⟨i, hi, rfl⟩⟩
        rw [if_congr hm rfl rfl]
        have hm2 : i ∈ K.I_M0 ↔ D.k i = 0 ∨ ¬ S.isU0 i := by
          unfold I_M0; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
        rw [if_congr hm2 rfl rfl]
      have hN1_rm : (K.N1.map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) =
          if (D.k i = 1 ∧ S.isU0 i) ∨ (K.isML i ∧ K.isD1 i) then 1 else 0 := by
        unfold N1; rw [linProd_rm]
        have hm : (∃ j ∈ K.I_N1, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) ↔ i ∈ K.I_N1 :=
          ⟨fun ⟨j, hj, heq⟩ => by rwa [BinaryIRSProfile.domain.injective (ι.injective heq)], fun hi => ⟨i, hi, rfl⟩⟩
        rw [if_congr hm rfl rfl]
        have hm2 : i ∈ K.I_N1 ↔ (D.k i = 1 ∧ S.isU0 i) ∨ (K.isML i ∧ K.isD1 i) := by
          unfold I_N1; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
        rw [if_congr hm2 rfl rfl]
      have hR_ne : R_raw ≠ 0 := by
        intro h0
        have hid := zRaw_ode_fail_identity hd1 hd2 hid0
        have hz0 : zRaw c0 c1 0 (K.Qpoly * Ndom ^ 3) = 0 := by unfold zRaw hasse; simp
        rw [h0, mul_zero, hz0, mul_zero] at hid
        exact hz ((mul_eq_zero.mp hid).resolve_left (pow_ne_zero 9 hNdom_ne))
      have hR_rm_eq : (R_raw.map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) = R_raw.rootMultiplicity (BinaryIRSProfile.domain i) :=
        rootMultiplicity_map_eq _ _
      have hg2_rm_eq : ((D.gj 2).map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) = (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
        rootMultiplicity_map_eq _ _
      rw [hM0_rm, hN1_rm, hR_rm_eq, hg2_rm_eq] at hbound; rw [hM0_rm]
      have hd_R_of : ∀ m : ℕ, (X - C (BinaryIRSProfile.domain i)) ^ m ∣ R_raw → m ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) :=
        fun m hd => (le_rootMultiplicity_iff hR_ne).mpr hd
      have hd_g2_of : ∀ m : ℕ, (X - C (BinaryIRSProfile.domain i)) ^ m ∣ D.gj 2 → m ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
        fun m hd => (le_rootMultiplicity_iff D.g2_ne_zero).mpr hd
      have hd_Uy : S.isU0 i → X - C (BinaryIRSProfile.domain i) ∣ Uy0 := fun hU => by
        rw [dvd_iff_isRoot, IsRoot]; simpa [Uy0, y0, KerD45Syzygy.isU0, KerD45Syzygy.U_eval] using hU
      -- Case-split on k i = 0, 1, 2, ≥ 3!
      by_cases hk0 : D.k i = 0
      · have hnNorm : ¬ K.isNorm i := fun h => by have := h.1; omega
        have hnML : ¬ K.isML i := fun h => by have := h.1; omega
        by_cases hD1 : K.isD1 i
        · have hR3 : 3 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 3 (by
            have hD1d := dvd_iff_isRoot.mpr hD1
            apply dvd_add
            · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hD1d 4)) _) _
            · rw [pow_succ _ 2]
              exact mul_dvd_mul (pow_dvd_pow_of_dvd (hd_Uy (K.isU0_of_D1_zero hD1)) 2) (hD1d.trans (S.D1_dvd_gj 1)))
          have hg1 : 1 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
            hd_g2_of 1 (by rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2))
          simp only [hk0, hD1, hnNorm, hnML, show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 2 by omega,
            show ¬ (3 ≤ 0) by omega, Nat.sub_eq_zero_of_le (show 0 ≤ 3 by omega),
            true_or, or_true, false_or, or_false, false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
        · simp only [hk0, hD1, hnNorm, hnML, show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 2 by omega,
            show ¬ (3 ≤ 0) by omega, Nat.sub_eq_zero_of_le (show 0 ≤ 3 by omega),
            true_or, or_true, false_or, or_false, false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
      · by_cases hk1 : D.k i = 1
        · have hnNorm : ¬ K.isNorm i := fun h => by have := h.1; omega
          have hnML : ¬ K.isML i := fun h => by have := h.1; omega
          by_cases hU : S.isU0 i
          · by_cases hD1 : K.isD1 i
            · have hR3 : 3 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 3 (by
                have hD1d := dvd_iff_isRoot.mpr hD1
                apply dvd_add
                · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hD1d 4)) _) _
                · rw [pow_succ _ 2]
                  exact mul_dvd_mul (pow_dvd_pow_of_dvd (hd_Uy hU) 2) (hD1d.trans (S.D1_dvd_gj 1)))
              have hg1 : 1 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                hd_g2_of 1 (by rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2))
              simp only [hk1, hU, hD1, hnNorm, hnML, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 2 by omega,
                show ¬ (3 ≤ 1) by omega, Nat.sub_eq_zero_of_le (show 1 ≤ 3 by omega),
                not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
            · have hR1 : 1 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 1 (by
                apply dvd_add
                · exact dvd_mul_of_dvd_right (by have := K.pow_dvd_gsh0 i; rwa [hk1] at this) _
                · exact dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 1 ≤ 2)).trans (pow_dvd_pow_of_dvd (hd_Uy hU) 2)) _)
              simp only [hk1, hU, hD1, hnNorm, hnML, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 2 by omega,
                show ¬ (3 ≤ 1) by omega, Nat.sub_eq_zero_of_le (show 1 ≤ 3 by omega),
                not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
          · simp only [hk1, hU, hnNorm, hnML, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 2 by omega,
              show ¬ (3 ≤ 1) by omega, Nat.sub_eq_zero_of_le (show 1 ≤ 3 by omega),
              not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
              false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
        · by_cases hk2 : D.k i = 2
          · by_cases hU : S.isU0 i
            · by_cases hD1 : K.isD1 i
              · have hR3 : 3 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 3 (by
                  have hD1d := dvd_iff_isRoot.mpr hD1
                  apply dvd_add
                  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hD1d 4)) _) _
                  · rw [pow_succ _ 2]
                    exact mul_dvd_mul (pow_dvd_pow_of_dvd (hd_Uy hU) 2) (hD1d.trans (S.D1_dvd_gj 1)))
                by_cases hn : K.isNorm i
                · have hg3 : 3 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                    hd_g2_of 3 (K.pow_dvd_g2_din i hn.1 hU hn.2.2.1 hn.2.2.2 hD1)
                  have hnML : ¬ K.isML i := fun h => h.2.2.2 hn.2.2.2
                  simp only [hk2, hU, hD1, hn, hnML, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                    show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega),
                    not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                    false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
                · have hmL : K.isML i := by
                    have hg0 := K.g2t_zero_of_D1_zero hD1
                    unfold isNorm at hn; unfold isML; exact ⟨by omega, hU, hg0, fun hM0 => hn ⟨by omega, hU, hg0, hM0⟩⟩
                  have hg1 : 1 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                    hd_g2_of 1 (by rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2))
                  simp only [hk2, hU, hD1, hn, hmL, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                    show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega),
                    not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                    false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
              · -- k=2, U=0, d2=0: p1(t_i) ≠ 0 so sqrtPoly p1 has rootMult 0, and M0 has rootMult 0!
                have ha0 : ((sqrtPoly K.p1).map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) = 0 := by
                  rw [rootMultiplicity_sqrtPoly_map K.p1 K.hp1_ne, ← map_pow, rootMultiplicity_map_eq]
                  exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr (K.p1_ne_zero_of_isU0_D1_ne hU hD1))
                simp only [hk2, hU, hD1, ha0, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                  show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega),
                  not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                  false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
            · have hnNorm : ¬ K.isNorm i := fun h => hU h.2.1
              have hnML : ¬ K.isML i := fun h => hU h.2.1
              have hR2 : 2 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 2 (by
                apply dvd_add
                · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 ≤ 2 * D.k i - 1)).trans (K.pow_dvd_gsh0 i)) _
                · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 ≤ 2 * (D.k i - 1))).trans (K.pow_dvd_g1_U1 i hU)) _)
              simp only [hk2, hU, hnNorm, hnML, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega),
                not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
          · have hk3 : 3 ≤ D.k i := by omega
            by_cases hU : S.isU0 i
            · have hR_ge : 2 * D.k i - 1 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of _ (by
                apply dvd_add
                · exact dvd_mul_of_dvd_right (K.pow_dvd_gsh0 i) _
                · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 2 + (2 * D.k i - 3))).trans
                    (by rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd (hd_Uy hU) 2) (K.pow_dvd_g1_U0 i)))
              have hg_ge : 2 * D.k i - 5 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                hd_g2_of _ (D.pow_dvd_g2_of_k i)
              by_cases hML : K.isML i <;> by_cases hD1 : K.isD1 i <;>
                simp only [hk0, hk1, hk2, hk3, hU, hML, hD1, not_true_eq_false, not_false_eq_true,
                  true_or, or_true, false_or, or_false, false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢ <;>
                omega
            · have hnNorm : ¬ K.isNorm i := fun h => hU h.2.1
              have hnML : ¬ K.isML i := fun h => hU h.2.1
              have hR_ge : 2 * D.k i - 2 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of _ (by
                apply dvd_add
                · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 * D.k i - 2 ≤ 2 * D.k i - 1)).trans (K.pow_dvd_gsh0 i)) _
                · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 * D.k i - 2 ≤ 2 * (D.k i - 1))).trans (K.pow_dvd_g1_U1 i hU)) _)
              have hg_ge : 2 * (D.k i - 2) ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                hd_g2_of _ (K.pow_dvd_g2_U1 i hU)
              simp only [hk0, hk1, hk2, hk3, hU, hnNorm, hnML, not_true_eq_false, not_false_eq_true,
                true_or, or_true, false_or, or_false, false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
    · -- Outside domain: Ndom.eval a ≠ 0, M0.rootMultiplicity a = 0!
      dsimp [bonus]; rw [dif_neg hdom, add_zero]
      have hM0_0 : (K.M0.map ι).rootMultiplicity a = 0 := by
        unfold M0; rw [linProd_rm, if_neg (fun ⟨i, _, hi⟩ => hdom ⟨i, hi⟩)]
      have hNeval : (Ndom.map ι).eval a ≠ 0 := mt (hNdom_ev a).mp hdom
      let Uy0 : Fld[X] := S.p.comp (X ^ 2) * C (0 : Fld) + S.R
      let U1_y0 : Fld[X] := S.D1 * K.p1.comp (X ^ 2) * C (0 : Fld) + K.R1
      let R_raw : Fld[X] := S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 2 * (D.gj 0 + C ((0 : Fld) ^ 2) * D.gj 1 + C ((0 : Fld) ^ 4) * D.gj 2) +
        Uy0 ^ 2 * D.gj 1
      have hid0 : K.Hrem * Ndom ^ 3 + (sqrtPoly K.p1) ^ 4 * (K.M0 ^ 3 * K.N1 ^ 2 * R_raw) = K.Qpoly * U1_y0 ^ 4 :=
        K.Hrem_Q_ode_fail_id 0
      have heqE : (K.Hrem.map ι) * (Ndom.map ι) ^ 3 + ((sqrtPoly K.p1).map ι) ^ 4 *
          ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * (R_raw.map ι)) =
          ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * ((D.gj 2).map ι)) * (U1_y0.map ι) ^ 4 := by
        have h := congrArg (Polynomial.map ι) hid0
        unfold Qpoly at h; simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] at h; exact h
      have hbound := (rootMultiplicity_zOde_ge
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.M0_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr hZ_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne)
        hd1E hd2E hdivE heqE a).1 hNeval
      rw [hM0_0]; omega
  -- Sum hpt over S_fin!
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
  have hA1_sum : (∑ a ∈ S_fin, (((sqrtPoly K.p1).map ι).rootMultiplicity a : ℤ)) = (S.p.natDegree : ℤ) - (S.D1.natDegree : ℤ) := by
    have h1 := sum_rootMultiplicity_map_eq_natDegree (sqrtPoly K.p1) hA1_ne S_fin (fun a ha => by simp [S_fin, ι, E, ha])
    rw [natDegree_sqrtPoly] at h1
    have hp := K.natDegree_p_eq
    have h1Z : (∑ a ∈ S_fin, (((sqrtPoly K.p1).map ι).rootMultiplicity a : ℤ)) = (K.p1.natDegree : ℤ) := by
      rw [hι]; exact_mod_cast h1
    omega
  have hZ_sum : (∑ a ∈ S_fin, ((Z_ode.map ι).rootMultiplicity a : ℤ)) = (Z_ode.natDegree : ℤ) := by
    rw [hι]; exact_mod_cast sum_rootMultiplicity_map_eq_natDegree Z_ode hZ_ne S_fin (fun a ha => by simp [S_fin, ι, E, ha])
  have hM0_sum : (∑ a ∈ S_fin, ((K.M0.map ι).rootMultiplicity a : ℤ)) = (K.M0.natDegree : ℤ) := by
    have hsub : (K.M0.map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin := fun a ha => by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots ((Polynomial.map_ne_zero_iff (algebraMap Fld (AlgebraicClosure Fld)).injective).mpr K.M0_ne)] at ha
      have hrm : (K.M0.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a ≠ 0 :=
        fun h0 => ((Polynomial.map_ne_zero_iff (algebraMap Fld (AlgebraicClosure Fld)).injective).mpr K.M0_ne) ((rootMultiplicity_eq_zero_iff.mp h0) ha)
      unfold M0 at hrm; rw [linProd_rm] at hrm; split_ifs at hrm with h
      · rcases h with ⟨i, _, rfl⟩; simp [S_fin, ι, E]
      · exact absurd rfl hrm
    rw [hι]; exact_mod_cast sum_rootMultiplicity_map_eq_natDegree K.M0 K.M0_ne S_fin hsub
  have hbon_sum : (∑ a ∈ S_fin, bonus a) =
      4 * (K.din2Cnt : ℤ) + 4 * (K.d2k1UCnt : ℤ) + 4 * (K.dmLCnt : ℤ) + 5 * (K.d2k0Cnt : ℤ) -
      2 * (D.n0 : ℤ) - 2 * (D.n1 : ℤ) + 2 * (S.n1U : ℤ) + 2 * (D.n3 : ℤ) + 6 * (D.nt : ℤ) := by
    let domImg : Finset E := Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i))
    have hdom_sub : domImg ⊆ S_fin := fun a ha => by rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩; simp [S_fin]
    rw [← Finset.sum_subset hdom_sub (fun a _ hna => by
      dsimp [bonus]; rw [dif_neg (fun ⟨i, hi⟩ => hna (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩))]),
      Finset.sum_image (fun i _ j _ h => BinaryIRSProfile.domain.injective (ι.injective h))]
    have hterm : ∀ i : Idx, bonus (ι (BinaryIRSProfile.domain i)) =
        4 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
        4 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
        4 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
        4 * (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
        5 * (if D.k i = 0 ∧ K.isD1 i then 1 else 0) -
        2 * (if D.k i = 0 then 1 else 0) -
        2 * (if D.k i = 1 then 1 else 0) +
        2 * (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
        2 * (if 3 ≤ D.k i then 1 else 0) + 6 * ((D.k i - 3 : ℕ) : ℤ) := fun i => by
      dsimp [bonus]; rw [dif_pos ⟨i, rfl⟩]
      have hch : Classical.choose (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
      rw [hch]
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
    simp only [dmLCnt, Nat.cast_add]; ring
  rw [hA1_sum, hbon_sum, hZ_sum, hM0_sum] at hsum
  omega

/-- Wronskian `W2a / W2b` degree bounds when `HK.derivative ≠ 0`! -/
theorem w2_degree_bounds {c0 : Fld} (hc0 : c0 ≠ 0) (hNdom_deg : Ndom.natDegree = N)
    (hd1 : Ndom.derivative = C c0) (hHK' : K.HK.derivative ≠ 0) :
    ((K.HK.natDegree < N + K.HK.derivative.natDegree) →
      N ≤ 2 * K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree - 4 * S.D1.natDegree ∧
      (K.M0eff.natDegree : ℤ) + 2 * (K.Lam1.natDegree : ℤ) + 10 * (S.p.natDegree : ℤ) -
        4 * (S.D1.natDegree : ℤ) - ((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ) ≤ (N : ℤ)) ∧
    ((N + K.HK.derivative.natDegree ≤ K.HK.natDegree) →
      N ≤ K.M0eff.natDegree + (D.gj 2).natDegree + K.g2rem.natDegree ∧
      (K.M0eff.natDegree : ℤ) + 2 * (K.Lam1.natDegree : ℤ) + 10 * (S.p.natDegree : ℤ) -
        4 * (S.D1.natDegree : ℤ) - ((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ) ≤ (N : ℤ)) := by
  have hwr := K.HK_wronskian hd1
  have hp1c := mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne
  have hLc := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
  have hNdom_ne : Ndom ≠ 0 := by obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
  have hRHS_ne : K.M0eff ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero))
      (pow_ne_zero 5 hp1c)) hLc
  have hW_ne : C c0 * K.HK + Ndom * K.HK.derivative ≠ 0 := by
    intro h0; apply hRHS_ne; rw [← hwr, h0, mul_zero]
  have hdeg_LHS : K.M0eff.natDegree + (D.gj 2).natDegree + K.g2rem.natDegree = 2 * K.SK.natDegree + K.HK.natDegree := by
    have h := congrArg Polynomial.natDegree K.HK_decomp
    rw [natDegree_mul (mul_ne_zero K.M0eff_ne D.g2_ne_zero) K.g2rem_ne,
      natDegree_mul K.M0eff_ne D.g2_ne_zero,
      natDegree_mul (pow_ne_zero 2 K.SK_ne) K.HK_ne, natDegree_pow] at h; exact h
  have hdeg_wr : 2 * K.SK.natDegree + (C c0 * K.HK + Ndom * K.HK.derivative).natDegree =
      2 * K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree - 4 * S.D1.natDegree := by
    have h := congrArg Polynomial.natDegree hwr
    rw [natDegree_mul (pow_ne_zero 2 K.SK_ne) hW_ne, natDegree_pow,
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c)) hLc,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c),
      natDegree_mul (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero),
      natDegree_pow, natDegree_pow, natDegree_pow, natDegree_comp_X_sq, natDegree_comp_X_sq] at h
    have hp := K.natDegree_p_eq; omega
  have hC_deg : (C c0 * K.HK).natDegree = K.HK.natDegree := by
    rw [natDegree_C_mul hc0]
  have hNH_deg : (Ndom * K.HK.derivative).natDegree = N + K.HK.derivative.natDegree := by
    rw [natDegree_mul hNdom_ne hHK', hNdom_deg]
  have hH'_lt : K.HK.derivative.natDegree < K.HK.natDegree := by
    have hpos : 0 < K.HK.natDegree := by
      by_contra h0; apply hHK'; rw [Polynomial.eq_C_of_natDegree_eq_zero (p := K.HK) (by omega), derivative_C]
    exact natDegree_derivative_lt (by omega)
  constructor
  · intro hlt
    have hW_deg : (C c0 * K.HK + Ndom * K.HK.derivative).natDegree = N + K.HK.derivative.natDegree := by
      rw [natDegree_add_eq_right_of_natDegree_lt (by rw [hC_deg, hNH_deg]; exact hlt), hNH_deg]
    omega
  · intro hge
    have hW_deg : (C c0 * K.HK + Ndom * K.HK.derivative).natDegree ≤ K.HK.natDegree :=
      (natDegree_add_le _ _).trans (max_le (by omega) (by omega))
    omega

end KerD45KData

/-! ### Part 4: Complete `K ≠ 0` (`T4BBranch`, 84 branches, `nv = 49`) Satisfaction Theorem -/

private lemma row0A_2_vals :
    row0A_2[0]! = 2 ∧ row0A_2[1]! = 4 ∧ row0A_2[2]! = 0 ∧ row0A_2[3]! = -11 ∧ row0A_2[4]! = -4 ∧
    row0A_2[5]! = -10 ∧ row0A_2[6]! = 0 ∧ row0A_2[7]! = 11 ∧ row0A_2[8]! = 6 ∧ row0A_2[9]! = 6 ∧
    row0A_2[10]! = -4 ∧ row0A_2[11]! = 1 ∧ row0A_2[12]! = -2 ∧ row0A_2[13]! = 0 ∧ row0A_2[14]! = -2 := by
  decide

private lemma row0C0_2_vals :
    row0C0_2[0]! = 2 ∧ row0C0_2[1]! = 7 ∧ row0C0_2[2]! = 0 ∧ row0C0_2[3]! = -8 ∧ row0C0_2[4]! = -10 ∧
    row0C0_2[5]! = -13 ∧ row0C0_2[6]! = 2 ∧ row0C0_2[7]! = 10 ∧ row0C0_2[8]! = 9 ∧ row0C0_2[9]! = 2 ∧
    row0C0_2[10]! = -16 ∧ row0C0_2[11]! = 2 ∧ row0C0_2[12]! = -5 ∧ row0C0_2[13]! = 0 ∧ row0C0_2[14]! = -5 := by
  decide

private lemma row0C1_2_vals :
    row0C1_2[0]! = 2 ∧ row0C1_2[1]! = 3 ∧ row0C1_2[2]! = 0 ∧ row0C1_2[3]! = -8 ∧ row0C1_2[4]! = -2 ∧
    row0C1_2[5]! = -9 ∧ row0C1_2[6]! = 2 ∧ row0C1_2[7]! = 10 ∧ row0C1_2[8]! = 5 ∧ row0C1_2[9]! = 10 ∧
    row0C1_2[10]! = -16 ∧ row0C1_2[11]! = 2 ∧ row0C1_2[12]! = -1 ∧ row0C1_2[13]! = 0 ∧ row0C1_2[14]! = -1 := by
  decide

private lemma rowC04_2_vals :
    rowC04_2[0]! = 8 ∧ rowC04_2[1]! = 8 ∧ rowC04_2[2]! = 0 ∧ rowC04_2[3]! = -8 ∧ rowC04_2[4]! = -8 ∧
    rowC04_2[5]! = -8 ∧ rowC04_2[6]! = 0 ∧ rowC04_2[7]! = 8 ∧ rowC04_2[8]! = 8 ∧ rowC04_2[9]! = 8 ∧
    rowC04_2[10]! = 0 ∧ rowC04_2[11]! = 8 ∧ rowC04_2[12]! = -4 ∧ rowC04_2[13]! = 0 ∧ rowC04_2[14]! = -4 := by
  decide

/-- Helper lemma to verify any `mkR15` row (`mode = 0, 1, 2`) from its exact integer bound! -/
private lemma mkR15_eval_base (x : Fin 49 → ℚ) (v : Fin 48 → ℕ)
    (hx : ∀ (j : ℕ) (hj : j < 48), x ⟨j, by omega⟩ = (v ⟨j, hj⟩ : ℚ) / (N : ℚ))
    (am0 amb am1 am2 ak3 amL0 amu1 amuO alam adin admL adoth aL0 aa1 aLnoU : ℤ) :
    let base : List (Nat × Int) := [
      (0, cH (-am0)), (1, cH (-am0)), (18, cH (am0 - am1)), (26, cH (-amb)),
      (2, cH (-am2)), (19, cH am2), (3, cH (-am2)), (20, cH (am2 - ak3)),
      (27, cH (-amL0)), (34, cH (amL0 - admL + adoth)),
      (39, cH (amuO - amu1)), (29, cH (-amuO)),
      (16, cH (-alam)), (31, cH (adoth - adin)), (17, cH (aa1 - adoth)),
      (21, cH (-2 * aL0 + 2 * aLnoU)), (4, cH (-2 * aLnoU)), (9, cQ (-aa1))
    ]
    (base.map fun e => if hj : e.1 < 49 then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum =
      -2 * ((am0 : ℚ) * ((v ⟨0, by decide⟩ : ℚ) + (v ⟨1, by decide⟩ : ℚ) - (v ⟨18, by decide⟩ : ℚ)) +
        (amb : ℚ) * (v ⟨26, by decide⟩ : ℚ) + (am1 : ℚ) * (v ⟨18, by decide⟩ : ℚ) +
        (am2 : ℚ) * ((v ⟨2, by decide⟩ : ℚ) - (v ⟨19, by decide⟩ : ℚ) + (v ⟨3, by decide⟩ : ℚ) - (v ⟨20, by decide⟩ : ℚ)) +
        (ak3 : ℚ) * (v ⟨20, by decide⟩ : ℚ) +
        (amL0 : ℚ) * ((v ⟨27, by decide⟩ : ℚ) - (v ⟨34, by decide⟩ : ℚ)) +
        (amu1 : ℚ) * (v ⟨39, by decide⟩ : ℚ) +
        (amuO : ℚ) * ((v ⟨29, by decide⟩ : ℚ) - (v ⟨39, by decide⟩ : ℚ)) +
        (alam : ℚ) * (v ⟨16, by decide⟩ : ℚ) +
        (adin : ℚ) * (v ⟨31, by decide⟩ : ℚ) + (admL : ℚ) * (v ⟨34, by decide⟩ : ℚ) +
        (adoth : ℚ) * ((v ⟨17, by decide⟩ : ℚ) - (v ⟨31, by decide⟩ : ℚ) - (v ⟨34, by decide⟩ : ℚ)) +
        (aL0 : ℚ) * (2 * (v ⟨21, by decide⟩ : ℚ)) +
        (aa1 : ℚ) * ((v ⟨9, by decide⟩ : ℚ) / 2 - (v ⟨17, by decide⟩ : ℚ)) +
        (aLnoU : ℚ) * (2 * ((v ⟨4, by decide⟩ : ℚ) - (v ⟨21, by decide⟩ : ℚ)))) := by
  intro base
  have h0 := hx 0 (by decide); have h1 := hx 1 (by decide); have h2 := hx 2 (by decide)
  have h3 := hx 3 (by decide); have h4 := hx 4 (by decide); have h9 := hx 9 (by decide)
  have h16 := hx 16 (by decide); have h17 := hx 17 (by decide); have h18 := hx 18 (by decide)
  have h19 := hx 19 (by decide); have h20 := hx 20 (by decide); have h21 := hx 21 (by decide)
  have h26 := hx 26 (by decide); have h27 := hx 27 (by decide); have h29 := hx 29 (by decide)
  have h31 := hx 31 (by decide); have h34 := hx 34 (by decide); have h39 := hx 39 (by decide)
  simp only [base, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    show (0 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega,
    show (3 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
    show (16 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega,
    show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (21 : ℕ) < 49 by omega,
    show (26 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (29 : ℕ) < 49 by omega,
    show (31 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (39 : ℕ) < 49 by omega,
    ↓reduceDIte, h0, h1, h2, h3, h4, h9, h16, h17, h18, h19, h20, h21, h26, h27, h29, h31, h34, h39,
    cH_mul_div_N, cQ_mul_div_N]
  push_cast; ring

private def t4bVec (v : Fin 48 → ℕ) (WF : ℕ) : Fin 49 → ℚ := fun j =>
  if hj : j.val < 48 then (v ⟨j.val, hj⟩ : ℚ) / (N : ℚ) else (WF : ℚ) / (wY : ℚ)

private def r15Rhs (r2 : Array ℤ) (v : Fin 48 → ℕ) : ℤ :=
  r2[0]! * ((v ⟨0, by decide⟩ : ℤ) + (v ⟨1, by decide⟩ : ℤ) - (v ⟨18, by decide⟩ : ℤ)) + r2[1]! * (v ⟨26, by decide⟩ : ℤ) +
  r2[3]! * ((v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ)) + r2[4]! * (v ⟨20, by decide⟩ : ℤ) +
  r2[5]! * ((v ⟨27, by decide⟩ : ℤ) - (v ⟨34, by decide⟩ : ℤ)) + r2[6]! * (v ⟨39, by decide⟩ : ℤ) +
  r2[7]! * ((v ⟨29, by decide⟩ : ℤ) - (v ⟨39, by decide⟩ : ℤ)) + r2[8]! * (v ⟨16, by decide⟩ : ℤ) +
  r2[9]! * (v ⟨31, by decide⟩ : ℤ) + r2[10]! * (v ⟨34, by decide⟩ : ℤ) +
  r2[11]! * ((v ⟨17, by decide⟩ : ℤ) - (v ⟨31, by decide⟩ : ℤ) - (v ⟨34, by decide⟩ : ℤ)) +
  r2[12]! * (2 * (v ⟨21, by decide⟩ : ℤ)) + r2[14]! * (2 * ((v ⟨4, by decide⟩ : ℤ) - (v ⟨21, by decide⟩ : ℤ)))

private theorem table4_K_rows_sat
    (br : T4BBranch) (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (v : Fin 48 → ℕ) (WF : ℕ)
    (hBS : let x := t4bVec v WF
           let (ubB, eqB) := baseT4Rows 48 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
           (∀ r ∈ ubB, RowSatLe x r) ∧ (∀ r ∈ eqB, RowSatEq x r))
    (heq_nat :
      (v ⟨44, by decide⟩ : ℤ) + (v ⟨45, by decide⟩ : ℤ) = (v ⟨31, by decide⟩ : ℤ) ∧
      (v ⟨46, by decide⟩ : ℤ) + (v ⟨47, by decide⟩ : ℤ) = (v ⟨34, by decide⟩ : ℤ) ∧
      (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + (v ⟨4, by decide⟩ : ℤ) + (v ⟨25, by decide⟩ : ℤ) = (v ⟨10, by decide⟩ : ℤ) ∧
      (v ⟨18, by decide⟩ : ℤ) + (v ⟨34, by decide⟩ : ℤ) = (v ⟨35, by decide⟩ : ℤ) ∧
      (v ⟨0, by decide⟩ : ℤ) + (v ⟨1, by decide⟩ : ℤ) - (v ⟨18, by decide⟩ : ℤ) + (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) = (v ⟨28, by decide⟩ : ℤ) ∧
      (v ⟨0, by decide⟩ : ℤ) + (v ⟨1, by decide⟩ : ℤ) + (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + (v ⟨26, by decide⟩ : ℤ) = (v ⟨37, by decide⟩ : ℤ) ∧
      (v ⟨19, by decide⟩ : ℤ) + (v ⟨20, by decide⟩ : ℤ) + (v ⟨26, by decide⟩ : ℤ) - (v ⟨27, by decide⟩ : ℤ) + (v ⟨29, by decide⟩ : ℤ) = (v ⟨13, by decide⟩ : ℤ) ∧
      2 * (v ⟨10, by decide⟩ : ℤ) + (v ⟨19, by decide⟩ : ℤ) + (v ⟨20, by decide⟩ : ℤ) - (v ⟨26, by decide⟩ : ℤ) + (v ⟨30, by decide⟩ : ℤ) = (v ⟨12, by decide⟩ : ℤ) ∧
      (v ⟨12, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) - 3 * (v ⟨19, by decide⟩ : ℤ) - 3 * (v ⟨20, by decide⟩ : ℤ) + 3 * (v ⟨34, by decide⟩ : ℤ) - (v ⟨35, by decide⟩ : ℤ) - (v ⟨36, by decide⟩ : ℤ) = 0 ∧
      (v ⟨33, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) + (v ⟨38, by decide⟩ : ℤ) = (v ⟨11, by decide⟩ : ℤ) ∧
      (v ⟨41, by decide⟩ : ℤ) + (v ⟨42, by decide⟩ : ℤ) + (v ⟨43, by decide⟩ : ℤ) = (v ⟨21, by decide⟩ : ℤ))
    (hub_nat1 :
      (v ⟨44, by decide⟩ : ℤ) + (v ⟨46, by decide⟩ : ℤ) ≤ (v ⟨19, by decide⟩ : ℤ) ∧
      (v ⟨45, by decide⟩ : ℤ) + (v ⟨47, by decide⟩ : ℤ) ≤ (v ⟨20, by decide⟩ : ℤ) ∧
      (v ⟨18, by decide⟩ : ℤ) ≤ (v ⟨1, by decide⟩ : ℤ) ∧
      (v ⟨19, by decide⟩ : ℤ) ≤ (v ⟨2, by decide⟩ : ℤ) ∧
      (v ⟨20, by decide⟩ : ℤ) ≤ (v ⟨3, by decide⟩ : ℤ) ∧
      (v ⟨21, by decide⟩ : ℤ) ≤ (v ⟨4, by decide⟩ : ℤ) ∧
      (v ⟨22, by decide⟩ : ℤ) ≤ (v ⟨18, by decide⟩ : ℤ) ∧
      (v ⟨22, by decide⟩ : ℤ) ≤ (v ⟨6, by decide⟩ : ℤ) ∧
      (v ⟨6, by decide⟩ : ℤ) - (v ⟨22, by decide⟩ : ℤ) - (v ⟨1, by decide⟩ : ℤ) + (v ⟨18, by decide⟩ : ℤ) ≤ 0 ∧
      (v ⟨23, by decide⟩ : ℤ) ≤ (v ⟨19, by decide⟩ : ℤ) ∧
      (v ⟨23, by decide⟩ : ℤ) ≤ (v ⟨7, by decide⟩ : ℤ) ∧
      (v ⟨7, by decide⟩ : ℤ) - (v ⟨23, by decide⟩ : ℤ) - (v ⟨2, by decide⟩ : ℤ) + (v ⟨19, by decide⟩ : ℤ) ≤ 0 ∧
      (v ⟨24, by decide⟩ : ℤ) ≤ (v ⟨20, by decide⟩ : ℤ) ∧
      (v ⟨24, by decide⟩ : ℤ) ≤ (v ⟨8, by decide⟩ : ℤ) ∧
      (v ⟨8, by decide⟩ : ℤ) - (v ⟨24, by decide⟩ : ℤ) - (v ⟨3, by decide⟩ : ℤ) + (v ⟨20, by decide⟩ : ℤ) ≤ 0 ∧
      2 * (v ⟨6, by decide⟩ : ℤ) - (v ⟨22, by decide⟩ : ℤ) + 4 * (v ⟨7, by decide⟩ : ℤ) - (v ⟨23, by decide⟩ : ℤ) + 6 * (v ⟨8, by decide⟩ : ℤ) - (v ⟨24, by decide⟩ : ℤ) ≤ (WF : ℤ) - (wY : ℤ) + 1 ∧
      (v ⟨26, by decide⟩ : ℤ) ≤ (v ⟨25, by decide⟩ : ℤ) ∧
      (v ⟨26, by decide⟩ : ℤ) + (v ⟨27, by decide⟩ : ℤ) ≤ (v ⟨19, by decide⟩ : ℤ) + (v ⟨20, by decide⟩ : ℤ) ∧
      (v ⟨27, by decide⟩ : ℤ) ≤ (v ⟨16, by decide⟩ : ℤ) ∧
      2 * (v ⟨17, by decide⟩ : ℤ) ≤ (v ⟨9, by decide⟩ : ℤ) ∧
      (v ⟨31, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + (v ⟨33, by decide⟩ : ℤ) + (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨17, by decide⟩ : ℤ) ∧
      (v ⟨33, by decide⟩ : ℤ) ≤ (v ⟨0, by decide⟩ : ℤ) ∧
      (v ⟨32, by decide⟩ : ℤ) ≤ (v ⟨18, by decide⟩ : ℤ) ∧
      (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨27, by decide⟩ : ℤ))
    (hub_nat2 :
      (v ⟨27, by decide⟩ : ℤ) + 2 * (v ⟨43, by decide⟩ : ℤ) ≤ (v ⟨16, by decide⟩ : ℤ) ∧
      (v ⟨39, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) ≤ (v ⟨18, by decide⟩ : ℤ) ∧
      (v ⟨39, by decide⟩ : ℤ) + (v ⟨40, by decide⟩ : ℤ) ≤ (v ⟨29, by decide⟩ : ℤ) ∧
      2 * (v ⟨20, by decide⟩ : ℤ) - 2 * (v ⟨31, by decide⟩ : ℤ) - 2 * (v ⟨34, by decide⟩ : ℤ) - (v ⟨26, by decide⟩ : ℤ) + 2 * (v ⟨41, by decide⟩ : ℤ) + 2 * (v ⟨43, by decide⟩ : ℤ) ≤ (v ⟨16, by decide⟩ : ℤ) + (v ⟨40, by decide⟩ : ℤ) ∧
      (v ⟨33, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + 2 * (v ⟨27, by decide⟩ : ℤ) - 2 * (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨30, by decide⟩ : ℤ) ∧
      (v ⟨33, by decide⟩ : ℤ) + (v ⟨18, by decide⟩ : ℤ) - (v ⟨39, by decide⟩ : ℤ) + 2 * (v ⟨27, by decide⟩ : ℤ) - 2 * (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨30, by decide⟩ : ℤ) ∧
      (v ⟨33, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + 2 * (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 4 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) ≤ (v ⟨12, by decide⟩ : ℤ) ∧
      3 * (v ⟨31, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + (v ⟨33, by decide⟩ : ℤ) + (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨11, by decide⟩ : ℤ) ∧
      3 * (v ⟨44, by decide⟩ : ℤ) + (v ⟨46, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + (v ⟨33, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) ≤ (v ⟨11, by decide⟩ : ℤ) ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + 12 * (v ⟨44, by decide⟩ : ℤ) + 2 * (v ⟨46, by decide⟩ : ℤ) + 4 * (v ⟨1, by decide⟩ : ℤ) - 3 * (v ⟨18, by decide⟩ : ℤ) +
        16 * (v ⟨2, by decide⟩ : ℤ) - 5 * (v ⟨19, by decide⟩ : ℤ) + 34 * (v ⟨3, by decide⟩ : ℤ) - 5 * (v ⟨20, by decide⟩ : ℤ) + 18 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) ≤ 8 * (WF : ℤ) - 20 * (wY : ℤ) + 4 ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + 20 * (v ⟨44, by decide⟩ : ℤ) + 10 * (v ⟨46, by decide⟩ : ℤ) - 8 * (v ⟨25, by decide⟩ : ℤ) + 4 * (v ⟨1, by decide⟩ : ℤ) - 3 * (v ⟨18, by decide⟩ : ℤ) +
        16 * (v ⟨2, by decide⟩ : ℤ) - 5 * (v ⟨19, by decide⟩ : ℤ) + 34 * (v ⟨3, by decide⟩ : ℤ) - 5 * (v ⟨20, by decide⟩ : ℤ) + 18 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) ≤ 8 * (WF : ℤ) - 20 * (wY : ℤ) + 4 ∧
      (v ⟨12, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) + 10 * (v ⟨13, by decide⟩ : ℤ) + 8 * (v ⟨16, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) ≤ 8 * (WF : ℤ) - 20 * (wY : ℤ) + 4 ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + 12 * (v ⟨44, by decide⟩ : ℤ) + 2 * (v ⟨46, by decide⟩ : ℤ) + 4 * (v ⟨1, by decide⟩ : ℤ) - 3 * (v ⟨18, by decide⟩ : ℤ) +
        16 * (v ⟨2, by decide⟩ : ℤ) - 5 * (v ⟨19, by decide⟩ : ℤ) + 34 * (v ⟨3, by decide⟩ : ℤ) - 5 * (v ⟨20, by decide⟩ : ℤ) + 18 * (v ⟨4, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) -
        4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨12, by decide⟩ : ℤ) - 8 * (v ⟨16, by decide⟩ : ℤ) - 10 * (v ⟨13, by decide⟩ : ℤ) ≤ 0 ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + 20 * (v ⟨44, by decide⟩ : ℤ) + 10 * (v ⟨46, by decide⟩ : ℤ) - 8 * (v ⟨25, by decide⟩ : ℤ) + 4 * (v ⟨1, by decide⟩ : ℤ) - 3 * (v ⟨18, by decide⟩ : ℤ) +
        16 * (v ⟨2, by decide⟩ : ℤ) - 5 * (v ⟨19, by decide⟩ : ℤ) + 34 * (v ⟨3, by decide⟩ : ℤ) - 5 * (v ⟨20, by decide⟩ : ℤ) + 18 * (v ⟨4, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) -
        4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨12, by decide⟩ : ℤ) - 8 * (v ⟨16, by decide⟩ : ℤ) - 10 * (v ⟨13, by decide⟩ : ℤ) ≤ 0 ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + (v ⟨18, by decide⟩ : ℤ) + 3 * (v ⟨19, by decide⟩ : ℤ) + 3 * (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) +
        2 * (v ⟨10, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨12, by decide⟩ : ℤ) - 2 * (v ⟨13, by decide⟩ : ℤ) ≤ 0 ∧
      (v ⟨1, by decide⟩ : ℤ) - (v ⟨18, by decide⟩ : ℤ) + 2 * (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 4 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨16, by decide⟩ : ℤ) - (v ⟨13, by decide⟩ : ℤ) ≤ 0 ∧
      2 * (v ⟨31, by decide⟩ : ℤ) + (v ⟨34, by decide⟩ : ℤ) + (v ⟨27, by decide⟩ : ℤ) + (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 3 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨10, by decide⟩ : ℤ) - (v ⟨16, by decide⟩ : ℤ) ≤ 0 ∧
      (v ⟨11, by decide⟩ : ℤ) ≤ (WF : ℤ) - 5 * (wY : ℤ) + 1 ∧
      (v ⟨2, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) + (v ⟨4, by decide⟩ : ℤ) + (v ⟨10, by decide⟩ : ℤ) ≤ (v ⟨12, by decide⟩ : ℤ) ∧
      (v ⟨12, by decide⟩ : ℤ) ≤ (WF : ℤ) - 3 * (wY : ℤ) + 1 ∧
      5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) ≤ (v ⟨11, by decide⟩ : ℤ) + (v ⟨12, by decide⟩ : ℤ) ∧
      2 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨10, by decide⟩ : ℤ) + 4 * (v ⟨16, by decide⟩ : ℤ) + 8 * (v ⟨14, by decide⟩ : ℤ) - 8 * (v ⟨17, by decide⟩ : ℤ) - 2 * (v ⟨12, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 2 * (wY : ℤ) + 2 ∧
      5 * (v ⟨14, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 3 * (wY : ℤ) + 1 ∧
      (v ⟨22, by decide⟩ : ℤ) + (v ⟨23, by decide⟩ : ℤ) + (v ⟨24, by decide⟩ : ℤ) ≤ (v ⟨15, by decide⟩ : ℤ))
    (hR_nat :
      (br.rGt = true → (v ⟨9, by decide⟩ : ℤ) + (wY : ℤ) ≤ (v ⟨14, by decide⟩ : ℤ) ∧ (v ⟨15, by decide⟩ : ℤ) = (v ⟨14, by decide⟩ : ℤ)) ∧
      (br.rGt = false → (v ⟨14, by decide⟩ : ℤ) ≤ (v ⟨9, by decide⟩ : ℤ) + (wY : ℤ) ∧ (v ⟨15, by decide⟩ : ℤ) ≤ (v ⟨9, by decide⟩ : ℤ) + (wY : ℤ)))
    (hV_nat :
      (br.vCancel = true → (v ⟨13, by decide⟩ : ℤ) - (v ⟨9, by decide⟩ : ℤ) - (v ⟨10, by decide⟩ : ℤ) - (v ⟨14, by decide⟩ : ℤ) + 2 * (v ⟨17, by decide⟩ : ℤ) = 0) ∧
      (br.vCancel = false →
        (2 * (v ⟨9, by decide⟩ : ℤ) - 2 * (v ⟨11, by decide⟩ : ℤ) + 4 * (v ⟨13, by decide⟩ : ℤ) + 4 * (v ⟨16, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 2 * (wY : ℤ)) ∧
        (2 * (v ⟨13, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + (v ⟨15, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 5 * (wY : ℤ) + 1)))
    (hQ1_nat :
      (br.q1Case = 0 → -4 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + (v ⟨12, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) ≤ (WF : ℤ) - (wY : ℤ) + 1) ∧
      (br.q1Case = 1 → -2 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) - 2 * (v ⟨14, by decide⟩ : ℤ) ≤ 0) ∧
      (br.q1Case ≠ 0 → br.q1Case ≠ 1 → -2 * (v ⟨10, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) + (v ⟨12, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) - 4 * (v ⟨14, by decide⟩ : ℤ) ≤ 0))
    (hODE_nat :
      (br.odeCase < 4 →
        ((v ⟨1, by decide⟩ : ℤ) - (v ⟨32, by decide⟩ : ℤ) + 2 * (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 4 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨16, by decide⟩ : ℤ) - (v ⟨13, by decide⟩ : ℤ) ≤ 0) ∧
        ((v ⟨1, by decide⟩ : ℤ) + (v ⟨27, by decide⟩ : ℤ) - (v ⟨32, by decide⟩ : ℤ) - (v ⟨16, by decide⟩ : ℤ) - (v ⟨29, by decide⟩ : ℤ) ≤ 0) ∧
        (2 * ((v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ)) ≤ r15Rhs row0A_2 v)) ∧
      (¬ br.odeCase < 4 →
        2 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) + 4 * (v ⟨44, by decide⟩ : ℤ) + 4 * (v ⟨32, by decide⟩ : ℤ) + 4 * (v ⟨34, by decide⟩ : ℤ) + 5 * (v ⟨33, by decide⟩ : ℤ) -
          2 * (v ⟨0, by decide⟩ : ℤ) - 2 * (v ⟨1, by decide⟩ : ℤ) + 2 * (v ⟨18, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) + 6 * (v ⟨4, by decide⟩ : ℤ) ≤
          (v ⟨36, by decide⟩ : ℤ) + 2 * (v ⟨35, by decide⟩ : ℤ) + 2 * (v ⟨11, by decide⟩ : ℤ)) ∧
      ((br.odeCase = 0 ∨ br.odeCase = 4) →
        ((v ⟨37, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + 5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ) = 0) ∧
        (2 * ((v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ)) ≤ r15Rhs row0C0_2 v) ∧
        (2 * ((v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ)) ≤ r15Rhs row0C1_2 v)) ∧
      ((br.odeCase = 1 ∨ br.odeCase = 2 ∨ br.odeCase = 5) →
        ((N : ℤ) ≤ 2 * (v ⟨37, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + 5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ)) ∧
        ((v ⟨37, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + 5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ) ≤ (N : ℤ))) ∧
      (br.odeCase = 1 →
        2 * (3 * (N : ℤ) + 2 * (v ⟨11, by decide⟩ : ℤ) - 2 * (v ⟨13, by decide⟩ : ℤ) - 2 * (v ⟨16, by decide⟩ : ℤ) - 5 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ)) ≤ r15Rhs rowC04_2 v) ∧
      (br.odeCase = 2 →
        2 * (4 * (N : ℤ) + (v ⟨11, by decide⟩ : ℤ) - (v ⟨12, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) - 2 * (v ⟨13, by decide⟩ : ℤ)) ≤ r15Rhs rowC04_2 v) ∧
      ((br.odeCase = 3 ∨ br.odeCase = 6) →
        ((N : ℤ) ≤ (v ⟨37, by decide⟩ : ℤ) + (v ⟨11, by decide⟩ : ℤ) + (v ⟨30, by decide⟩ : ℤ)) ∧
        ((v ⟨37, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + 5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ) ≤ (N : ℤ))))
    (hode_lt : br.odeCase < 7) :
    let rows := buildT4BRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    let x := t4bVec v WF
    (∀ r ∈ rows.1.toList, RowValid 49 r ∧ RowSatLe x r) ∧
    (∀ r ∈ rows.2.toList, RowValid 49 r ∧ RowSatEq x r) := by
  let x : Fin 49 → ℚ := t4bVec v WF
  have hx_lt_fn : ∀ (j : ℕ) (hj : j < 48), x ⟨j, by omega⟩ = (v ⟨j, hj⟩ : ℚ) / (N : ℚ) := fun j hj => by
    dsimp [x, t4bVec]; rw [dif_pos hj]
  have hx_lt :
      x ⟨0, by decide⟩ = (v ⟨0, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (v ⟨1, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨2, by decide⟩ = (v ⟨2, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (v ⟨3, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨4, by decide⟩ = (v ⟨4, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨5, by decide⟩ = (v ⟨5, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨6, by decide⟩ = (v ⟨6, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨7, by decide⟩ = (v ⟨7, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨8, by decide⟩ = (v ⟨8, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨9, by decide⟩ = (v ⟨9, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨10, by decide⟩ = (v ⟨10, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨11, by decide⟩ = (v ⟨11, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨12, by decide⟩ = (v ⟨12, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨13, by decide⟩ = (v ⟨13, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨14, by decide⟩ = (v ⟨14, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨15, by decide⟩ = (v ⟨15, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨16, by decide⟩ = (v ⟨16, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨17, by decide⟩ = (v ⟨17, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨18, by decide⟩ = (v ⟨18, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨19, by decide⟩ = (v ⟨19, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨20, by decide⟩ = (v ⟨20, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨21, by decide⟩ = (v ⟨21, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨22, by decide⟩ = (v ⟨22, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨23, by decide⟩ = (v ⟨23, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨24, by decide⟩ = (v ⟨24, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨25, by decide⟩ = (v ⟨25, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨26, by decide⟩ = (v ⟨26, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨27, by decide⟩ = (v ⟨27, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨28, by decide⟩ = (v ⟨28, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨29, by decide⟩ = (v ⟨29, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨30, by decide⟩ = (v ⟨30, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨31, by decide⟩ = (v ⟨31, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨32, by decide⟩ = (v ⟨32, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨33, by decide⟩ = (v ⟨33, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨34, by decide⟩ = (v ⟨34, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨35, by decide⟩ = (v ⟨35, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨36, by decide⟩ = (v ⟨36, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨37, by decide⟩ = (v ⟨37, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨38, by decide⟩ = (v ⟨38, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨39, by decide⟩ = (v ⟨39, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨40, by decide⟩ = (v ⟨40, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨41, by decide⟩ = (v ⟨41, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨42, by decide⟩ = (v ⟨42, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨43, by decide⟩ = (v ⟨43, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨44, by decide⟩ = (v ⟨44, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨45, by decide⟩ = (v ⟨45, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨46, by decide⟩ = (v ⟨46, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨47, by decide⟩ = (v ⟨47, by decide⟩ : ℚ) / (N : ℚ) :=
    ⟨hx_lt_fn 0 (by decide), hx_lt_fn 1 (by decide), hx_lt_fn 2 (by decide), hx_lt_fn 3 (by decide),
     hx_lt_fn 4 (by decide), hx_lt_fn 5 (by decide), hx_lt_fn 6 (by decide), hx_lt_fn 7 (by decide),
     hx_lt_fn 8 (by decide), hx_lt_fn 9 (by decide), hx_lt_fn 10 (by decide), hx_lt_fn 11 (by decide),
     hx_lt_fn 12 (by decide), hx_lt_fn 13 (by decide), hx_lt_fn 14 (by decide), hx_lt_fn 15 (by decide),
     hx_lt_fn 16 (by decide), hx_lt_fn 17 (by decide), hx_lt_fn 18 (by decide), hx_lt_fn 19 (by decide),
     hx_lt_fn 20 (by decide), hx_lt_fn 21 (by decide), hx_lt_fn 22 (by decide), hx_lt_fn 23 (by decide),
     hx_lt_fn 24 (by decide), hx_lt_fn 25 (by decide), hx_lt_fn 26 (by decide), hx_lt_fn 27 (by decide),
     hx_lt_fn 28 (by decide), hx_lt_fn 29 (by decide), hx_lt_fn 30 (by decide), hx_lt_fn 31 (by decide),
     hx_lt_fn 32 (by decide), hx_lt_fn 33 (by decide), hx_lt_fn 34 (by decide), hx_lt_fn 35 (by decide),
     hx_lt_fn 36 (by decide), hx_lt_fn 37 (by decide), hx_lt_fn 38 (by decide), hx_lt_fn 39 (by decide),
     hx_lt_fn 40 (by decide), hx_lt_fn 41 (by decide), hx_lt_fn 42 (by decide), hx_lt_fn 43 (by decide),
     hx_lt_fn 44 (by decide), hx_lt_fn 45 (by decide), hx_lt_fn 46 (by decide), hx_lt_fn 47 (by decide)⟩
  have hx_48 : x ⟨48, by decide⟩ = (WF : ℚ) / (wY : ℚ) := rfl
  have hBV := baseT4Rows_valid (nv := 49) (ic := 48) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hc_nn : (0 : ℚ) ≤ (WF : ℚ) / (wY : ℚ) := by positivity
  have hmkR15_valid : ∀ (r2 : Array ℤ) (mode : ℕ), RowValid 49 (mkR15 r2 mode) := fun r2 mode => by
    unfold mkR15; apply rowValid_filter_nz
    intro e he; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
        rcases h with rfl | rfl | rfl | rfl | rfl <;> omega
  have hmkR15_sat_0 : ∀ (r2 : Array ℤ), r2[2]! = 0 → r2[13]! = 0 →
      2 * ((v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ)) ≤ r15Rhs r2 v → RowSatLe x (mkR15 r2 0) := fun r2 h2z h13z hineq => by
    unfold mkR15; rw [rowSatLe_mkStat_iff, evalRow_filter_nz]
    simp only [BEq.rfl, ↓reduceIte, List.map_append, List.sum_append]
    rw [mkR15_eval_base x v hx_lt_fn]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
    have hQ := (Int.cast_le (R := ℚ)).mpr hineq
    unfold r15Rhs at hQ; rw [h2z, h13z]; push_cast at hQ ⊢; linarith only [hQ]
  have heqCore_sat : ∀ r ∈ [
      mkEq [(44, cI 1), (45, cI 1), (31, cI (-1))],
      mkEq [(46, cI 1), (47, cI 1), (34, cI (-1))],
      mkEq [(2, cI 1), (19, cI (-1)), (3, cI 2), (20, cI (-1)), (4, cI 1), (25, cI 1), (10, cI (-1))],
      mkEq [(18, cI 1), (34, cI 1), (35, cI (-1))],
      mkEq [(0, cI 1), (1, cI 1), (18, cI (-1)), (2, cI 1), (19, cI (-1)), (3, cI 1), (20, cI (-1)), (28, cI (-1))],
      mkEq [(0, cI 1), (1, cI 1), (2, cI 1), (19, cI (-1)), (3, cI 1), (20, cI (-1)), (26, cI 1), (37, cI (-1))],
      mkEq [(19, cI 1), (20, cI 1), (26, cI 1), (27, cI (-1)), (29, cI 1), (13, cI (-1))],
      mkEq [(10, cI 2), (19, cI 1), (20, cI 1), (26, cI (-1)), (30, cI 1), (12, cI (-1))],
      mkEq [(12, cI 1), (10, cI (-2)), (13, cI 2), (19, cI (-3)), (20, cI (-3)), (34, cI 3), (35, cI (-1)), (36, cI (-1))],
      mkEq [(33, cI 1), (32, cI 1), (3, cI 2), (20, cI (-1)), (4, cI 2), (38, cI 1), (11, cI (-1))],
      mkEq [(41, cI 1), (42, cI 1), (43, cI 1), (21, cI (-1))]
    ], RowValid 49 r ∧ RowSatEq x r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (44 : ℕ) < 49 by omega, show (45 : ℕ) < 49 by omega, show (31 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (46 : ℕ) < 49 by omega, show (47 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (25 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (18 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (35 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (0 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (28 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (0 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (26 : ℕ) < 49 by omega, show (37 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (26 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (29 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (10 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (26 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (12 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (35 : ℕ) < 49 by omega, show (36 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (38 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (41 : ℕ) < 49 by omega, show (42 : ℕ) < 49 by omega, show (43 : ℕ) < 49 by omega, show (21 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.2.2.2.2
      push_cast at hQ ⊢; linarith only [hQ]
  have hubCore_sat : ∀ r ∈ ([
      mkStat [(44, cI 1), (46, cI 1), (19, cI (-1))] 0 false,
      mkStat [(45, cI 1), (47, cI 1), (20, cI (-1))] 0 false,
      mkStat [(18, cI 1), (1, cI (-1))] 0 false,
      mkStat [(19, cI 1), (2, cI (-1))] 0 false,
      mkStat [(20, cI 1), (3, cI (-1))] 0 false,
      mkStat [(21, cI 1), (4, cI (-1))] 0 false,
      mkStat [(22, cI 1), (18, cI (-1))] 0 false,
      mkStat [(22, cI 1), (6, cI (-1))] 0 false,
      mkStat [(6, cI 1), (22, cI (-1)), (1, cI (-1)), (18, cI 1)] 0 false,
      mkStat [(23, cI 1), (19, cI (-1))] 0 false,
      mkStat [(23, cI 1), (7, cI (-1))] 0 false,
      mkStat [(7, cI 1), (23, cI (-1)), (2, cI (-1)), (19, cI 1)] 0 false,
      mkStat [(24, cI 1), (20, cI (-1))] 0 false,
      mkStat [(24, cI 1), (8, cI (-1))] 0 false,
      mkStat [(8, cI 1), (24, cI (-1)), (3, cI (-1)), (20, cI 1)] 0 false,
      mkStat [(6, cI 2), (22, cI (-1)), (7, cI 4), (23, cI (-1)), (8, cI 6), (24, cI (-1)), (48, cH (-1))] (-2),
      mkStat [(26, cI 1), (25, cI (-1))] 0 false,
      mkStat [(26, cI 1), (27, cI 1), (19, cI (-1)), (20, cI (-1))] 0 false,
      mkStat [(27, cI 1), (16, cI (-1))] 0,
      mkStat [(17, cI 1), (9, cH (-1))] 0,
      mkStat [(31, cI 1), (32, cI 1), (33, cI 1), (34, cI 1), (17, cI (-1))] 0 false,
      mkStat [(33, cI 1), (0, cI (-1))] 0 false,
      mkStat [(32, cI 1), (18, cI (-1))] 0 false,
      mkStat [(34, cI 1), (27, cI (-1))] 0 false,
      mkStat [(27, cI 1), (43, cI 2), (16, cI (-1))] 0,
      mkStat [(39, cI 1), (32, cI 1), (18, cI (-1))] 0 false,
      mkStat [(39, cI 1), (40, cI 1), (29, cI (-1))] 0 false,
      mkStat [(20, cI 2), (31, cI (-2)), (34, cI (-2)), (26, cI (-1)), (41, cI 2), (43, cI 2), (16, cI (-1)), (40, cI (-1))] 0,
      mkStat [(33, cI 1), (32, cI 1), (27, cI 2), (34, cI (-2)), (30, cI (-1))] 0,
      mkStat [(33, cI 1), (18, cI 1), (39, cI (-1)), (27, cI 2), (34, cI (-2)), (30, cI (-1))] 0,
      mkStat [(33, cI 1), (32, cI 1), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (12, cI (-1))] 0,
      mkStat [(31, cI 3), (32, cI 1), (33, cI 1), (34, cI 1), (11, cI (-1))] 0,
      mkStat [(44, cI 3), (46, cI 1), (32, cI 1), (33, cI 1), (3, cI 2), (20, cI (-1)), (4, cI 2), (11, cI (-1))] 0,
      mkStat [(33, cI 4), (32, cI 3), (44, cI 12), (46, cI 2), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (11, cI (-1)), (48, cI (-4))] (-40),
      mkStat [(33, cI 4), (32, cI 3), (44, cI 20), (46, cI 10), (25, cI (-8)), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (11, cI (-1)), (48, cI (-4))] (-40),
      mkStat [(12, cI 1), (10, cI (-2)), (17, cI 4), (13, cI 10), (16, cI 8), (11, cI (-1)), (48, cI (-4))] (-40),
      mkStat [(33, cI 4), (32, cI 3), (44, cI 12), (46, cI 2), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (16, cI (-8)), (13, cI (-10))] 0,
      mkStat [(33, cI 4), (32, cI 3), (44, cI 20), (46, cI 10), (25, cI (-8)), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (16, cI (-8)), (13, cI (-10))] 0,
      mkStat [(33, cI 4), (32, cI 3), (18, cI 1), (19, cI 3), (20, cI 3), (3, cI 2), (4, cI 2), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (13, cI (-2))] 0,
      mkStat [(1, cI 1), (18, cI (-1)), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (16, cI (-1)), (13, cI (-1))] 0,
      mkStat [(31, cI 2), (34, cI 1), (27, cI 1), (2, cI 1), (19, cI (-1)), (3, cI 3), (20, cI (-1)), (4, cI 2), (10, cI (-1)), (16, cI (-1))] 0,
      mkStat [(11, cI 1), (48, cH (-1))] (-10),
      mkStat [(2, cI 1), (3, cI 2), (4, cI 1), (10, cI 1), (12, cI (-1))] 0,
      mkStat [(12, cI 1), (48, cH (-1))] (-6),
      mkStat [(9, cH 5), (17, cI (-2)), (10, cI 1), (16, cI 1), (11, cH (-1)), (12, cH (-1))] 0,
      mkStat [(9, cH 1), (10, cI 1), (16, cI 1), (14, cI 2), (17, cI (-2)), (12, cH (-1)), (48, cQ (-1))] (-1),
      mkStat [(14, cI 5), (10, cI 2), (16, cI 2), (17, cI (-4)), (48, cI (-1))] (-6),
      mkStat [(22, cI 1), (23, cI 1), (24, cI 1), (15, cI (-1))] 0
    ] : List SparseRow), RowValid 49 r ∧ RowSatLe x r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (45 : ℕ) < 49 by omega, show (47 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (18 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (19 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (20 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (21 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (22 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (22 : ℕ) < 49 by omega, show (6 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (6 : ℕ) < 49 by omega, show (22 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (23 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (23 : ℕ) < 49 by omega, show (7 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (7 : ℕ) < 49 by omega, show (23 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (24 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (24 : ℕ) < 49 by omega, show (8 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (8 : ℕ) < 49 by omega, show (24 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (6 : ℕ) < 49 by omega, show (22 : ℕ) < 49 by omega, show (7 : ℕ) < 49 by omega, show (23 : ℕ) < 49 by omega, show (8 : ℕ) < 49 by omega, show (24 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (26 : ℕ) < 49 by omega, show (25 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (26 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (27 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (17 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N, cH_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (31 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (33 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (0 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (32 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (34 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (27 : ℕ) < 49 by omega, show (43 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (39 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (39 : ℕ) < 49 by omega, show (40 : ℕ) < 49 by omega, show (29 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (20 : ℕ) < 49 by omega, show (31 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (26 : ℕ) < 49 by omega, show (41 : ℕ) < 49 by omega, show (43 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (40 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (39 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (31 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (33 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (33 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (25 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (12 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (25 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (31 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (11 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (2 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (12 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N, cH_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_div_N, cQ_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (14 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (22 : ℕ) < 49 by omega, show (23 : ℕ) < 49 by omega, show (24 : ℕ) < 49 by omega, show (15 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      push_cast at hQ ⊢; linarith only [hQ]
  have hR_sat :
      (∀ r ∈ (if !br.rGt then [mkStat [(9, cI (-1)), (14, cI 1)] 2, mkStat [(9, cI (-1)), (15, cI 1)] 2]
        else [mkStat [(9, cI 1), (14, cI (-1))] (-2)]), RowValid 49 r ∧ RowSatLe x r) ∧
      (∀ r ∈ (if !br.rGt then ([] : List SparseRow) else [mkEq [(14, cI 1), (15, cI (-1))]]), RowValid 49 r ∧ RowSatEq x r) := by
    cases hr : br.rGt
    · have hRf := hR_nat.2 hr
      simp only [Bool.not_false, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro r hrm; rcases hrm with rfl | rfl
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
          have hQ := (Int.cast_le (R := ℚ)).mpr hRf.1
          push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 49 by omega, show (15 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
          have hQ := (Int.cast_le (R := ℚ)).mpr hRf.2
          push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
      · intro _ hrm; cases hrm
    · have hRt := hR_nat.1 hr
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
      constructor
      · intro r hrm; subst hrm
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ := (Int.cast_le (R := ℚ)).mpr hRt.1
        push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
      · intro r hrm; subst hrm
        refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
        rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (14 : ℕ) < 49 by omega, show (15 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) hRt.2
        push_cast at hQ ⊢; linarith only [hQ]
  have hV_sat :
      (∀ r ∈ (if !br.vCancel then
        [mkStat [(9, cH 1), (11, cH (-1)), (13, cI 1), (16, cI 1), (48, cQ (-1))] (-1),
         mkStat [(13, cI 2), (16, cI 2), (15, cI 1), (48, cI (-1))] (-10)]
        else []), RowValid 49 r ∧ RowSatLe x r) ∧
      (∀ r ∈ (if !br.vCancel then ([] : List SparseRow)
        else [mkEq [(13, cI 1), (9, cI (-1)), (10, cI (-1)), (14, cI (-1)), (17, cI 2)]]), RowValid 49 r ∧ RowSatEq x r) := by
    cases hv : br.vCancel
    · have hVf := hV_nat.2 hv
      simp only [Bool.not_false, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨fun r hr => ?_, fun _ hr => False.elim hr⟩
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega,
          show (16 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_div_N, cQ_mul_c_eq]
        have hQ := (Int.cast_le (R := ℚ)).mpr hVf.1
        push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (13 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (15 : ℕ) < 49 by omega,
          show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
        have hQ := (Int.cast_le (R := ℚ)).mpr hVf.2
        push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · have hVt := hV_nat.1 hv
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, List.mem_singleton]
      refine ⟨fun _ hr => False.elim hr, fun r hr => ?_⟩
      subst hr
      refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (13 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega,
        show (14 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) hVt
      push_cast at hQ ⊢; linarith only [hQ]
  have hQ1_sat : ∀ r ∈ (if br.q1Case == 0 then [mkStat [(9, cI (-4)), (17, cI 4), (10, cI (-2)), (12, cI 1), (13, cI 2), (48, cH (-1))] (-2)]
      else if br.q1Case == 1 then [mkStat [(9, cI (-2)), (17, cI 4), (10, cI (-2)), (13, cI 2), (14, cI (-2))] 0]
      else [mkStat [(10, cI (-2)), (17, cI 4), (11, cI (-1)), (12, cI 1), (13, cI 2), (14, cI (-4))] 0]),
      RowValid 49 r ∧ RowSatLe x r := by
    by_cases h0 : br.q1Case = 0
    · intro r hr; simp only [h0, BEq.rfl, ↓reduceIte, List.mem_singleton] at hr; subst hr
      refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega,
        show (13 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr (hQ1_nat.1 h0)
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · by_cases h1 : br.q1Case = 1
      · intro r hr; simp only [h1, show (1 == 0) = false by decide, BEq.rfl, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr; subst hr
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega,
          show (13 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ := (Int.cast_le (R := ℚ)).mpr (hQ1_nat.2.1 h1)
        push_cast at hQ ⊢; linarith only [hQ]
      · intro r hr
        have h0f : (br.q1Case == 0) = false := beq_false_of_ne h0
        have h1f : (br.q1Case == 1) = false := beq_false_of_ne h1
        simp only [h0f, h1f, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr; subst hr
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega,
          show (12 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ := (Int.cast_le (R := ℚ)).mpr (hQ1_nat.2.2 h0 h1)
        push_cast at hQ ⊢; linarith only [hQ]
  have hB1h_eq_sat : br.odeCase = 0 ∨ br.odeCase = 4 →
      RowValid 49 (mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]) ∧
      RowSatEq x (mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]) := fun hor => by
    refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
    rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (37 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
      show (17 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
    have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) (hODE_nat.2.2.1 hor).1
    push_cast at hQ ⊢; linarith only [hQ]
  have hB1_0C_sat : br.odeCase = 0 ∨ br.odeCase = 4 →
      (RowValid 49 (mkR15 row0C0_2 0) ∧ RowSatLe x (mkR15 row0C0_2 0)) ∧
      (RowValid 49 (mkR15 row0C1_2 0) ∧ RowSatLe x (mkR15 row0C1_2 0)) := fun hor =>
    ⟨⟨hmkR15_valid row0C0_2 0, hmkR15_sat_0 row0C0_2 row0C0_2_vals.2.2.1 row0C0_2_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hODE_nat.2.2.1 hor).2.1⟩,
     ⟨hmkR15_valid row0C1_2 0, hmkR15_sat_0 row0C1_2 row0C1_2_vals.2.2.1 row0C1_2_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hODE_nat.2.2.1 hor).2.2⟩⟩
  have hW2a_rows_sat : br.odeCase = 1 ∨ br.odeCase = 2 ∨ br.odeCase = 5 →
      (RowValid 49 (mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4)) ∧
       RowSatLe x (mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4))) ∧
      (RowValid 49 (mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4) ∧
       RowSatLe x (mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4)) := fun hor => by
    have hw2 := hODE_nat.2.2.2.1 hor
    constructor
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (37 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
        show (17 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hw2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (37 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
        show (17 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hw2.2
      push_cast at hQ ⊢; linarith only [hQ]
  have hW2b_rows_sat : br.odeCase = 3 ∨ br.odeCase = 6 →
      (RowValid 49 (mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4)) ∧
       RowSatLe x (mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4))) ∧
      (RowValid 49 (mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4) ∧
       RowSatLe x (mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4)) := fun hor => by
    have hw2 := hODE_nat.2.2.2.2.2.2 hor
    constructor
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (37 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hw2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (37 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
        show (17 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hw2.2
      push_cast at hQ ⊢; linarith only [hQ]
  have hODE_sat :
      let (ubODE, eqODE) :=
        if br.odeCase < 4 then
          let u0 : List SparseRow := [
            mkStat [(1, cI 1), (32, cI (-1)), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (16, cI (-1)), (13, cI (-1))] 0,
            mkStat [(1, cI 1), (27, cI 1), (32, cI (-1)), (16, cI (-1)), (29, cI (-1))] 0,
            mkR15 row0A_2 0
          ]
          if br.odeCase == 0 then
            (u0 ++ [mkR15 row0C0_2 0, mkR15 row0C1_2 0],
             [mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]])
          else if br.odeCase == 1 then
            (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4,
                    mkR15 rowC04_2 1], [])
          else if br.odeCase == 2 then
            (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4,
                    mkR15 rowC04_2 2], [])
          else
            (u0 ++ [mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
        else
          let u0 : List SparseRow := [
            mkStat [(9, cI 2), (17, cI (-4)), (44, cI 4), (32, cI 4), (34, cI 4), (33, cI 5),
                    (0, cI (-2)), (1, cI (-2)), (18, cI 2), (3, cI 2), (4, cI 6),
                    (36, cI (-1)), (35, cI (-2)), (11, cI (-2))] 0
          ]
          if br.odeCase == 4 then
            (u0 ++ [mkR15 row0C0_2 0, mkR15 row0C1_2 0],
             [mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]])
          else if br.odeCase == 5 then
            (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
          else
            (u0 ++ [mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
      (∀ r ∈ ubODE, RowValid 49 r ∧ RowSatLe x r) ∧ (∀ r ∈ eqODE, RowValid 49 r ∧ RowSatEq x r) := by
    by_cases hlt4 : br.odeCase < 4
    · have hoh := hODE_nat.1 hlt4
      have hu0_sat : ∀ r ∈ [
          mkStat [(1, cI 1), (32, cI (-1)), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (16, cI (-1)), (13, cI (-1))] 0,
          mkStat [(1, cI 1), (27, cI 1), (32, cI (-1)), (16, cI (-1)), (29, cI (-1))] 0,
          mkR15 row0A_2 0
        ], RowValid 49 r ∧ RowSatLe x r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (1 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega,
            show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega,
            show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
          have hQ := (Int.cast_le (R := ℚ)).mpr hoh.1
          push_cast at hQ ⊢; linarith only [hQ]
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (1 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega,
            show (16 : ℕ) < 49 by omega, show (29 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
          have hQ := (Int.cast_le (R := ℚ)).mpr hoh.2.1
          push_cast at hQ ⊢; linarith only [hQ]
        · exact ⟨hmkR15_valid row0A_2 0, hmkR15_sat_0 row0A_2 row0A_2_vals.2.2.1 row0A_2_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hoh.2.2⟩
      by_cases hc0 : br.odeCase = 0
      · simp only [hc0, show (0 : ℕ) < 4 by decide, BEq.rfl, ↓reduceIte, List.mem_append]
        refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          · exact (hB1_0C_sat (Or.inl hc0)).1
          · exact (hB1_0C_sat (Or.inl hc0)).2),
          fun r hr => by simp only [List.mem_singleton] at hr; rw [hr]; exact hB1h_eq_sat (Or.inl hc0)⟩
      · by_cases hc1 : br.odeCase = 1
        · simp only [hc1, show (1 : ℕ) < 4 by decide, show (1 == 0) = false by decide, BEq.rfl, Bool.false_eq_true, ↓reduceIte,
            List.mem_append]
          refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl
            · exact (hW2a_rows_sat (Or.inl hc1)).1
            · exact (hW2a_rows_sat (Or.inl hc1)).2
            · refine ⟨hmkR15_valid rowC04_2 1, ?_⟩
              unfold mkR15; rw [rowSatLe_mkStat_iff, evalRow_filter_nz]
              simp only [show (1 == 0) = false by decide, BEq.rfl, Bool.false_eq_true, ↓reduceIte, List.map_append, List.sum_append]
              rw [mkR15_eval_base x v hx_lt_fn]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                show (11 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega,
                show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
              have hQ := (Int.cast_le (R := ℚ)).mpr (hODE_nat.2.2.2.2.1 hc1)
              unfold r15Rhs at hQ; simp only [rowC04_2_vals] at hQ ⊢; push_cast at hQ ⊢; linarith only [hQ]),
            fun _ hr => by cases hr⟩
        · by_cases hc2 : br.odeCase = 2
          · simp only [hc2, show (2 : ℕ) < 4 by decide, show (2 == 0) = false by decide, show (2 == 1) = false by decide,
              BEq.rfl, Bool.false_eq_true, ↓reduceIte, List.mem_append]
            refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl | rfl
              · exact (hW2a_rows_sat (Or.inr (Or.inl hc2))).1
              · exact (hW2a_rows_sat (Or.inr (Or.inl hc2))).2
              · refine ⟨hmkR15_valid rowC04_2 2, ?_⟩
                unfold mkR15; rw [rowSatLe_mkStat_iff, evalRow_filter_nz]
                simp only [show (2 == 0) = false by decide, show (2 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte, List.map_append, List.sum_append]
                rw [mkR15_eval_base x v hx_lt_fn]
                simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  show (11 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega,
                  show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
                have hQ := (Int.cast_le (R := ℚ)).mpr (hODE_nat.2.2.2.2.2.1 hc2)
                unfold r15Rhs at hQ; simp only [rowC04_2_vals] at hQ ⊢; push_cast at hQ ⊢; linarith only [hQ]),
              fun _ hr => by cases hr⟩
          · have hc3 : br.odeCase = 3 := by omega
            simp only [hc3, show (3 : ℕ) < 4 by decide, show (3 == 0) = false by decide, show (3 == 1) = false by decide,
              show (3 == 2) = false by decide, Bool.false_eq_true, ↓reduceIte, List.mem_append]
            refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl
              · exact (hW2b_rows_sat (Or.inl hc3)).1
              · exact (hW2b_rows_sat (Or.inl hc3)).2),
              fun _ hr => by cases hr⟩
    · have hu0_sat : ∀ r ∈ [
          mkStat [(9, cI 2), (17, cI (-4)), (44, cI 4), (32, cI 4), (34, cI 4), (33, cI 5),
                  (0, cI (-2)), (1, cI (-2)), (18, cI 2), (3, cI 2), (4, cI 6),
                  (36, cI (-1)), (35, cI (-2)), (11, cI (-2))] 0
        ], RowValid 49 r ∧ RowSatLe x r := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega,
          show (34 : ℕ) < 49 by omega, show (33 : ℕ) < 49 by omega, show (0 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega,
          show (18 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (36 : ℕ) < 49 by omega,
          show (35 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ := (Int.cast_le (R := ℚ)).mpr (hODE_nat.2.1 hlt4)
        push_cast at hQ ⊢; linarith only [hQ]
      by_cases hc4 : br.odeCase = 4
      · simp only [hc4, show ¬ ((4 : ℕ) < 4) by decide, BEq.rfl, ↓reduceIte, List.mem_append]
        refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          · exact (hB1_0C_sat (Or.inr hc4)).1
          · exact (hB1_0C_sat (Or.inr hc4)).2),
          fun r hr => by simp only [List.mem_singleton] at hr; rw [hr]; exact hB1h_eq_sat (Or.inr hc4)⟩
      · by_cases hc5 : br.odeCase = 5
        · simp only [hc5, show ¬ ((5 : ℕ) < 4) by decide, show (5 == 4) = false by decide, BEq.rfl, Bool.false_eq_true,
            ↓reduceIte, List.mem_append]
          refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact (hW2a_rows_sat (Or.inr (Or.inr hc5))).1
            · exact (hW2a_rows_sat (Or.inr (Or.inr hc5))).2),
            fun _ hr => by cases hr⟩
        · have hc6 : br.odeCase = 6 := by omega
          simp only [hc6, show ¬ ((6 : ℕ) < 4) by decide, show (6 == 4) = false by decide, show (6 == 5) = false by decide,
            Bool.false_eq_true, ↓reduceIte, List.mem_append]
          refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact (hW2b_rows_sat (Or.inr hc6)).1
            · exact (hW2b_rows_sat (Or.inr hc6)).2),
            fun _ hr => by cases hr⟩
  constructor
  · intro r hr
    simp only [buildT4BRows, t4bStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | ((((hr | hr) | hr) | hr) | hr)
    · exact ⟨hBV.1 r hr, hBS.1 r hr⟩
    · exact hubCore_sat r hr
    · simp only [apply_ite Prod.fst] at hr; exact hR_sat.1 r hr
    · simp only [apply_ite Prod.fst] at hr; exact hV_sat.1 r hr
    · exact hQ1_sat r hr
    · exact hODE_sat.1 r hr
  · intro r hr
    simp only [buildT4BRows, t4bStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | (((hr | hr) | hr) | hr)
    · exact ⟨hBV.2 r hr, hBS.2 r hr⟩
    · exact heqCore_sat r hr
    · simp only [apply_ite Prod.snd] at hr; exact hR_sat.2 r hr
    · simp only [apply_ite Prod.snd] at hr; exact hV_sat.2 r hr
    · exact hODE_sat.2 r hr

/-- **Theorem (`T4BBranch`, `K ≠ 0`):** For any `S : KerD45Syzygy D` with `S.P0 = 0` and
`S.M21 ≠ 0`, `D` satisfies all rows of `buildT4BRows br` for an exact `br : T4BBranch`
(`br.q1Case < 3 ∧ br.odeCase < 7`)! -/
theorem table4_K_sat {D : KerD45Data} (S : KerD45Syzygy D) (hP0 : S.P0 = 0) (hM21 : S.M21 ≠ 0)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    ∃ br : T4BBranch, br.q1Case < 3 ∧ br.odeCase < 7 ∧
      let rows := buildT4BRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      ∃ x : Fin 49 → ℚ,
        (∀ j, 0 ≤ x j) ∧
        x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
        x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
        x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨48, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
        (∀ r ∈ rows.1.toList, RowValid 49 r ∧ RowSatLe x r) ∧
        (∀ r ∈ rows.2.toList, RowValid 49 r ∧ RowSatEq x r) := by
  classical
  let K : KerD45KData S := mkKerD45KData S hP0 hM21
  obtain ⟨c0, c1, L, hc0, hNdom_eq, hNdom_deg, hL4, hNdom_ne, hd1, hd2, _, _⟩ := Ndom_decomp
  let eK_cnt : ℕ := K.K1.natDegree - ((D.n2 - S.n2U) + (2 * D.n3 - S.n3U) + D.nt)
  let m_tot : ℕ := D.n0 + (D.n1 - S.n1U) + (D.n2 - S.n2U) + (D.n3 - S.n3U)
  let mu_tot : ℕ := K.M0s.natDegree - (S.n2U + S.n3U + K.mbadCnt - K.mLCnt)
  let e1_tot : ℕ := K.g2rem.natDegree
  let N1_deg : ℕ := S.n1U + K.dmLCnt
  let H_rem_deg : ℕ := K.Hrem.natDegree
  let M0_eff_deg : ℕ := D.n0 + D.n1 + (D.n2 - S.n2U) + (D.n3 - S.n3U) + K.mbadCnt
  let g4_rem : ℕ := (D.gj 2).natDegree - (K.d2k0Cnt + K.d2k1UCnt + (2 * D.n3 - S.n3U) + 2 * D.nt)
  let v : Fin 48 → ℕ := fun j =>
    match j.val with
    | 0 => D.n0 | 1 => D.n1 | 2 => D.n2 | 3 => D.n3 | 4 => D.nt
    | 5 => D.a0 | 6 => D.a1 | 7 => D.a2 | 8 => D.a3
    | 9 => 2 * S.p.natDegree | 10 => K.K1.natDegree | 11 => (D.gj 2).natDegree | 12 => (D.gj 1).natDegree
    | 13 => K.M0s.natDegree | 14 => S.R.natDegree | 15 => S.UP.natDegree | 16 => K.Lam1.natDegree
    | 17 => S.D1.natDegree | 18 => S.n1U | 19 => S.n2U | 20 => S.n3U | 21 => S.ntU
    | 22 => S.a1U | 23 => S.a2U | 24 => S.a3U | 25 => eK_cnt
    | 26 => K.mbadCnt | 27 => K.mLCnt | 28 => m_tot | 29 => mu_tot
    | 30 => e1_tot | 31 => K.dinCnt | 32 => K.d2k1UCnt | 33 => K.d2k0Cnt
    | 34 => K.dmLCnt | 35 => N1_deg | 36 => H_rem_deg | 37 => M0_eff_deg
    | 38 => g4_rem | 39 => K.mu1Cnt | 40 => K.muExK3
    | 41 => K.ntUNorm | 42 => K.ntUMbad | 43 => K.ntUML
    | 44 => K.din2Cnt | 45 => K.din3Cnt | 46 => K.dmL2Cnt | _ => K.dmL3Cnt
  let x : Fin 49 → ℚ := t4bVec v D.W_F
  let rGt : Bool := decide (2 * S.p.natDegree + wY < S.R.natDegree)
  let vCancel : Bool := decide (S.M20 = 0 ∨ S.M20.natDegree < (K.Lam1 * K.M0s).natDegree)
  let q1Case : ℕ :=
    if S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 then 0
    else if S.H1.natDegree ≤ 4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree then 1
    else 2
  have hq1_lt : q1Case < 3 := by dsimp [q1Case]; split_ifs <;> omega
  let odeHolds : Prop := zRaw c0 c1 K.Hrem K.Qpoly = 0
  let isW2a1 : Prop :=
    3 * (N : ℤ) + 2 * ((D.gj 2).natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ) - 2 * (K.Lam1.natDegree : ℤ) -
      10 * (S.p.natDegree : ℤ) + 4 * (S.D1.natDegree : ℤ) ≤
      4 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 4 * (K.mbadCnt : ℤ) -
      4 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 4 * (S.n3U : ℤ) -
      4 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) +
      4 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
      4 * (K.Lam1.natDegree : ℤ) + 4 * (K.dinCnt : ℤ) +
      4 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
      2 * (2 * (S.ntU : ℤ)) - 2 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ)))
  let odeCase : ℕ :=
    if odeHolds then
      if K.HK.derivative = 0 then 0
      else if K.HK.natDegree < N + K.HK.derivative.natDegree then
        if isW2a1 then 1 else 2
      else 3
    else
      if K.HK.derivative = 0 then 4
      else if K.HK.natDegree < N + K.HK.derivative.natDegree then 5
      else 6
  have hode_lt : odeCase < 7 := by dsimp [odeCase]; split_ifs <;> omega
  let br : T4BBranch := ⟨rGt, vCancel, q1Case, odeCase⟩
  refine ⟨br, hq1_lt, hode_lt, x, fun j => by dsimp [x, t4bVec]; split_ifs <;> positivity, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hBS := D.baseT4Rows_sat (nv := 49) (ic := 48) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcLo hcHi hloG hhiG
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hU := S.U_counts_ineqs
  have hK1b := K.K1_base_le
  have hM0sb := K.M0s_base_le
  have hg2tb := K.g2t_extra_le
  have hD1b := K.D1_counts_le
  have hmb_mL : K.mbadCnt + K.mLCnt ≤ S.n2U + S.n3U := by
    have hZ : (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) ≤ (S.n2U : ℤ) + (S.n3U : ℤ) := by
      have h1 : (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) = ∑ i : Idx, ((if K.isMbad i then (1 : ℤ) else 0) + (if K.isML i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.mbadCnt_Z, ← K.mLCnt_Z]
      have h2 : (S.n2U : ℤ) + (S.n3U : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← KerD45KData.n2U_Z, ← KerD45KData.n3U_Z]
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [KerD45KData.isMbad, KerD45KData.isML, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hdin2_dmL2 : K.din2Cnt + K.dmL2Cnt ≤ S.n2U := by
    have hZ : (K.din2Cnt : ℤ) + (K.dmL2Cnt : ℤ) ≤ (S.n2U : ℤ) := by
      have h1 : (K.din2Cnt : ℤ) + (K.dmL2Cnt : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.din2Cnt_Z, ← K.dmL2Cnt_Z]
      have h2 : (S.n2U : ℤ) = ∑ i : Idx, (if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) := KerD45KData.n2U_Z
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [KerD45KData.isNorm, KerD45KData.isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hdin3_dmL3 : K.din3Cnt + K.dmL3Cnt ≤ S.n3U := by
    have hZ : (K.din3Cnt : ℤ) + (K.dmL3Cnt : ℤ) ≤ (S.n3U : ℤ) := by
      have h1 : (K.din3Cnt : ℤ) + (K.dmL3Cnt : ℤ) = ∑ i : Idx, ((if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.din3Cnt_Z, ← K.dmL3Cnt_Z]
      have h2 : (S.n3U : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ S.isU0 i then (1 : ℤ) else 0) := KerD45KData.n3U_Z
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [KerD45KData.isNorm, KerD45KData.isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hd2k0_le : K.d2k0Cnt ≤ D.n0 := by
    have hZ : (K.d2k0Cnt : ℤ) ≤ (D.n0 : ℤ) := by
      rw [K.d2k0Cnt_Z, KerD45KData.n0_Z]
      apply Finset.sum_le_sum; intro i _
      by_cases hD1 : K.isD1 i <;>
        simp only [hD1, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hmu1_d2k1 : K.mu1Cnt + K.d2k1UCnt ≤ S.n1U := by
    have hZ : (K.mu1Cnt : ℤ) + (K.d2k1UCnt : ℤ) ≤ (S.n1U : ℤ) := by
      have h1 : (K.mu1Cnt : ℤ) + (K.d2k1UCnt : ℤ) = ∑ i : Idx,
          ((if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then (1 : ℤ) else 0) +
           (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.mu1Cnt_Z, ← K.d2k1UCnt_Z]
      have h2 : (S.n1U : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i then (1 : ℤ) else 0) := KerD45KData.n1U_Z
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [hU, hD1, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hdmL_le_mL : K.dmLCnt ≤ K.mLCnt := by
    have hZ : (K.dmLCnt : ℤ) ≤ (K.mLCnt : ℤ) := by
      have h1 : (K.dmLCnt : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) +
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z]; unfold KerD45KData.dmLCnt; push_cast; rfl
      have h2 : (K.mLCnt : ℤ) = ∑ i : Idx, (if K.isML i then (1 : ℤ) else 0) := K.mLCnt_Z
      rw [h1, h2]; apply Finset.sum_le_sum; intro i _
      by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [KerD45KData.isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    omega
  have hHrem_eq_sum :
      (D.gj 1).natDegree - 2 * K.K1.natDegree + 2 * K.M0s.natDegree =
        3 * (S.n2U + S.n3U - K.dmLCnt) + N1_deg + H_rem_deg := by
    have hg1 := K.natDegree_g1_eq
    have hHr := K.natDegree_Hrem
    have hmul := congrArg Polynomial.natDegree K.Hraw_eq_N1_Shit3_Hrem
    rw [natDegree_mul (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne, natDegree_comp_X_sq,
      natDegree_mul (mul_ne_zero K.N1_ne (pow_ne_zero 3 K.Shit3_ne)) K.Hrem_ne,
      natDegree_mul K.N1_ne (pow_ne_zero 3 K.Shit3_ne), natDegree_pow] at hmul
    unfold KerD45KData.N1 KerD45KData.Shit3 at hmul
    rw [KerD45KData.linProd_natDegree, KerD45KData.linProd_natDegree, K.card_I_N1, K.card_I_hit3] at hmul
    dsimp [N1_deg, H_rem_deg]; omega
  have hM0eff_deg : K.M0eff.natDegree = M0_eff_deg := by
    unfold KerD45KData.M0eff; rw [KerD45KData.linProd_natDegree, K.card_I_M0eff]
  have hN1_deg_eq : K.N1.natDegree = N1_deg := by
    unfold KerD45KData.N1; rw [KerD45KData.linProd_natDegree, K.card_I_N1]
  have hdD : S.D1.natDegree ≤ S.p.natDegree := S.D1_natDegree.symm ▸ S.D2_natDegree_le_p
  have hg1_eq := K.natDegree_g1_eq
  have hgr_eq := K.natDegree_g2rem
  have hg2b := K.g2_din2_full_bound
  have hH1_eq := K.natDegree_H1_eq
  have hResY_eq := K.natDegree_ResY_eq
  have hResY_hi := D.natDegree_ResY_le_col1
  have hResY_u := K.ResY_uncond_bound
  have hResY_eK := K.ResY_eK_bound
  have h1U_Z : (S.n1U : ℤ) ≤ (D.n1 : ℤ) := Nat.cast_le.mpr hU.1
  have h2U_Z : (S.n2U : ℤ) ≤ (D.n2 : ℤ) := Nat.cast_le.mpr hU.2.1
  have h3U_Z : (S.n3U : ℤ) ≤ (D.n3 : ℤ) := Nat.cast_le.mpr hU.2.2.1
  have h2n3_le : S.n3U ≤ 2 * D.n3 := by linarith only [hU.2.2.1]
  have hw_le_WF : wY ≤ D.W_F := by linarith only [h5, hw]
  have h20w_le : 20 * wY ≤ 8 * D.W_F := by linarith only [h5, hw]
  have h5w_le2 : 5 * wY ≤ 2 * D.W_F := by linarith only [h5, hw]
  have h3w_le1 : 3 * wY ≤ D.W_F + 1 := by linarith only [h5]
  have hmL_le_s : K.mLCnt ≤ S.n2U + S.n3U + K.mbadCnt := by linarith only [hmb_mL]
  have hmb_le_s : K.mbadCnt ≤ S.n2U + S.n3U := by linarith only [hmb_mL]
  have hmu1_le_n1U : K.mu1Cnt ≤ S.n1U := by linarith only [hmu1_d2k1]
  have hd2k1_le_n1 : K.d2k1UCnt ≤ D.n1 := by linarith only [hmu1_d2k1, hU.1]
  have hdmL_le_s : K.dmLCnt ≤ S.n2U + S.n3U := by linarith only [hdmL_le_mL, hmb_mL]
  have h2K1_le_g1 : 2 * K.K1.natDegree ≤ (D.gj 1).natDegree := by linarith only [hg1_eq]
  have hK1b_Z : ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) + (K.mbadCnt : ℤ) ≤ (K.K1.natDegree : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hK1b
    simp only [Nat.cast_add, Nat.cast_sub hU.2.1, Nat.cast_sub h2n3_le, Nat.cast_mul, Nat.cast_ofNat] at h; exact h
  have heK_Z : (eK_cnt : ℤ) = (K.K1.natDegree : ℤ) - ((D.n2 : ℤ) - (S.n2U : ℤ) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ)) := by
    dsimp [eK_cnt]; rw [Nat.cast_sub (by linarith only [hK1b])]
    simp only [Nat.cast_add, Nat.cast_sub hU.2.1, Nat.cast_sub h2n3_le, Nat.cast_mul, Nat.cast_ofNat]
  have hm_Z : (m_tot : ℤ) = (D.n0 : ℤ) + ((D.n1 : ℤ) - (S.n1U : ℤ)) + ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) := by
    dsimp [m_tot]; simp only [Nat.cast_add, Nat.cast_sub hU.1, Nat.cast_sub hU.2.1, Nat.cast_sub hU.2.2.1]
  have hM0eff_Z : (M0_eff_deg : ℤ) = (D.n0 : ℤ) + (D.n1 : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) + (K.mbadCnt : ℤ) := by
    dsimp [M0_eff_deg]; simp only [Nat.cast_add, Nat.cast_sub hU.2.1, Nat.cast_sub hU.2.2.1]
  have hM0sb_Z : ((S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ)) + (K.mu1Cnt : ℤ) + (K.muExK3 : ℤ) ≤ (K.M0s.natDegree : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hM0sb
    simp only [Nat.cast_add, Nat.cast_sub hmL_le_s] at h; exact h
  have hmu_eq_Z : (mu_tot : ℤ) = (K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) := by
    dsimp [mu_tot]; rw [Nat.cast_sub (by linarith only [hM0sb]), Nat.cast_sub hmL_le_s]; push_cast; ring
  have hg2tb_Z : ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ)) + (K.d2k0Cnt : ℤ) + ((S.n1U : ℤ) - (K.mu1Cnt : ℤ)) +
      2 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) ≤ (K.g2t.natDegree : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hg2tb
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hmb_le_s, Nat.cast_sub hmu1_le_n1U, Nat.cast_sub hdmL_le_mL] at h; exact h
  have hgr_Z : (e1_tot : ℤ) = (K.g2t.natDegree : ℤ) - ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ)) := by
    dsimp [e1_tot]; rw [hgr_eq, Nat.cast_sub (by linarith only [hg2tb]), Nat.cast_sub hmb_le_s]; push_cast; ring
  have hg1_Z : ((D.gj 1).natDegree : ℤ) = 2 * (K.K1.natDegree : ℤ) + (K.g2t.natDegree : ℤ) := by exact_mod_cast hg1_eq
  have hH1_Z : (S.H1.natDegree : ℤ) = 4 * (S.D1.natDegree : ℤ) + 2 * (K.M0s.natDegree : ℤ) + (K.g2t.natDegree : ℤ) := by exact_mod_cast hH1_eq
  have hResY_eq_Z : (D.ResY.natDegree : ℤ) = 4 * (S.D1.natDegree : ℤ) + 8 * (K.Lam1.natDegree : ℤ) + 10 * (K.M0s.natDegree : ℤ) + (K.g2t.natDegree : ℤ) := by
    exact_mod_cast hResY_eq
  have hResY_hi_Z : (D.ResY.natDegree : ℤ) ≤ 8 * (D.W_F : ℤ) - 20 * (wY : ℤ) + 4 + ((D.gj 2).natDegree : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hResY_hi
    simp only [Nat.cast_add, Nat.cast_sub h20w_le, Nat.cast_mul, Nat.cast_ofNat] at h; exact h
  have hResY_u_Z : 4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + 12 * (K.din2Cnt : ℤ) + 2 * (K.dmL2Cnt : ℤ) +
      (4 * (D.n1 : ℤ) - 3 * (S.n1U : ℤ)) + (16 * (D.n2 : ℤ) - 5 * (S.n2U : ℤ)) +
      (34 * (D.n3 : ℤ) - 5 * (S.n3U : ℤ)) + 18 * (D.nt : ℤ) ≤ (D.ResY.natDegree : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hResY_u
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (show 3 * S.n1U ≤ 4 * D.n1 by linarith only [hU.1]),
      Nat.cast_sub (show 5 * S.n2U ≤ 16 * D.n2 by linarith only [hU.2.1]),
      Nat.cast_sub (show 5 * S.n3U ≤ 34 * D.n3 by linarith only [hU.2.2.1])] at h; exact h
  have hHrem_Z : ((D.gj 1).natDegree : ℤ) - 2 * (K.K1.natDegree : ℤ) + 2 * (K.M0s.natDegree : ℤ) =
      3 * ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.dmLCnt : ℤ)) + (N1_deg : ℤ) + (H_rem_deg : ℤ) := by
    have h := congrArg (Nat.cast (R := ℤ)) hHrem_eq_sum
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h2K1_le_g1, Nat.cast_sub hdmL_le_s] at h; exact h
  have hg2b_Z : 3 * (K.din2Cnt : ℤ) + (K.dmL2Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) +
      (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) ≤ ((D.gj 2).natDegree : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hg2b
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h2n3_le] at h; exact h
  have hg4rem_Z : (g4_rem : ℤ) = ((D.gj 2).natDegree : ℤ) - ((K.d2k0Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) := by
    dsimp [g4_rem]; rw [Nat.cast_sub (by linarith only [hg2b])]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h2n3_le]
  have hmu1_d2k1_Z : (K.mu1Cnt : ℤ) + (K.d2k1UCnt : ℤ) ≤ (S.n1U : ℤ) := by exact_mod_cast hmu1_d2k1
  exact table4_K_rows_sat br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    hcLoD hcHiD hloGD hhiGD v D.W_F hBS
    (by
      simp only [v]
      have hnt_Z : (K.ntUNorm : ℤ) + (K.ntUMbad : ℤ) + (K.ntUML : ℤ) = (S.ntU : ℤ) := by exact_mod_cast K.ntU_split
      refine ⟨by unfold KerD45KData.dinCnt; push_cast; rfl,
              by unfold KerD45KData.dmLCnt; push_cast; rfl,
              by linarith only [heK_Z],
              by dsimp [N1_deg],
              by linarith only [hm_Z],
              by linarith only [hM0eff_Z],
              by linarith only [hmu_eq_Z],
              by linarith only [hg1_Z, hgr_Z],
              by linarith only [hHrem_Z],
              by linarith only [hg4rem_Z],
              by linarith only [hnt_Z]⟩)
    (by
      simp only [v]
      have hf1_Z : (2 * (D.a1 : ℤ) - (S.a1U : ℤ)) + (4 * (D.a2 : ℤ) - (S.a2U : ℤ)) + (6 * (D.a3 : ℤ) - (S.a3U : ℤ)) ≤ (D.W_F : ℤ) - (wY : ℤ) + 1 := by
        have h := (Nat.cast_le (α := ℤ)).mpr S.f1_eval_P_U_bound
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hw_le_WF,
          Nat.cast_sub (show S.a1U ≤ 2 * D.a1 by linarith only [hU.2.2.2.2.2.2.2.1]),
          Nat.cast_sub (show S.a2U ≤ 4 * D.a2 by linarith only [hU.2.2.2.2.2.2.2.2.1]),
          Nat.cast_sub (show S.a3U ≤ 6 * D.a3 by linarith only [hU.2.2.2.2.2.2.2.2.2.1])] at h; exact h
      have hmL_Z : (K.mLCnt : ℤ) + 2 * (K.ntUML : ℤ) ≤ (K.Lam1.natDegree : ℤ) := by exact_mod_cast K.mL_ntUML_le_Lam1
      have hU11 : (D.a1 : ℤ) + (S.n1U : ℤ) ≤ (D.n1 : ℤ) + (S.a1U : ℤ) := by exact_mod_cast hU.2.2.2.2.2.2.2.2.2.2.1
      have hU12 : (D.a2 : ℤ) + (S.n2U : ℤ) ≤ (D.n2 : ℤ) + (S.a2U : ℤ) := by exact_mod_cast hU.2.2.2.2.2.2.2.2.2.2.2.1
      have hU13 : (D.a3 : ℤ) + (S.n3U : ℤ) ≤ (D.n3 : ℤ) + (S.a3U : ℤ) := by exact_mod_cast hU.2.2.2.2.2.2.2.2.2.2.2.2
      have hdD_Z : (S.D1.natDegree : ℤ) ≤ (S.p.natDegree : ℤ) := Nat.cast_le.mpr hdD
      refine ⟨by exact_mod_cast hdin2_dmL2, by exact_mod_cast hdin3_dmL3,
              h1U_Z, h2U_Z, h3U_Z, Nat.cast_le.mpr hU.2.2.2.1,
              Nat.cast_le.mpr hU.2.2.2.2.1, Nat.cast_le.mpr hU.2.2.2.2.2.2.2.1, by linarith only [hU11],
              Nat.cast_le.mpr hU.2.2.2.2.2.1, Nat.cast_le.mpr hU.2.2.2.2.2.2.2.2.1, by linarith only [hU12],
              Nat.cast_le.mpr hU.2.2.2.2.2.2.1, Nat.cast_le.mpr hU.2.2.2.2.2.2.2.2.2.1, by linarith only [hU13],
              by linarith only [hf1_Z], by linarith only [hK1b_Z, heK_Z],
              by exact_mod_cast hmb_mL, by linarith only [hmL_Z, Nat.cast_nonneg (α := ℤ) K.ntUML],
              by push_cast; linarith only [hdD_Z], by exact_mod_cast hD1b,
              Nat.cast_le.mpr hd2k0_le, by linarith only [hmu1_d2k1_Z, Nat.cast_nonneg (α := ℤ) K.mu1Cnt],
              Nat.cast_le.mpr hdmL_le_mL⟩)
    (by
      simp only [v]
      have hmL_Z : (K.mLCnt : ℤ) + 2 * (K.ntUML : ℤ) ≤ (K.Lam1.natDegree : ℤ) := by exact_mod_cast K.mL_ntUML_le_Lam1
      have h321 := K.row321_bound
      have hg1d_Z : (K.d2k0Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
          (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) ≤ ((D.gj 1).natDegree : ℤ) := by
        have h := (Nat.cast_le (α := ℤ)).mpr K.g1_d2_bound
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_sub (show S.n2U ≤ 2 * D.n2 by linarith only [hU.2.1]),
          Nat.cast_sub (show S.n3U ≤ 4 * D.n3 by linarith only [hU.2.2.1])] at h; exact h
      have hH1d_Z : 4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + (S.n1U : ℤ) + 3 * (S.n2U : ℤ) +
          3 * (S.n3U : ℤ) + 2 * (D.n3 : ℤ) + 2 * (D.nt : ℤ) ≤ (S.H1.natDegree : ℤ) := by exact_mod_cast K.H1_d2_bound
      have hLM_Z : ((D.n1 : ℤ) - (S.n1U : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) + (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) +
          2 * (D.nt : ℤ) ≤ (K.Lam1.natDegree : ℤ) + (K.M0s.natDegree : ℤ) := by
        have h := (Nat.cast_le (α := ℤ)).mpr K.Lam1_M0s_U_bound
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hU.1,
          Nat.cast_sub (show S.n2U ≤ 2 * D.n2 by linarith only [hU.2.1]),
          Nat.cast_sub (show S.n3U ≤ 4 * D.n3 by linarith only [hU.2.2.1])] at h; exact h
      have hKt_Z : 2 * (K.dinCnt : ℤ) + (K.dmLCnt : ℤ) + (K.mLCnt : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) +
          (3 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) ≤ (K.K1.natDegree : ℤ) + (K.Lam1.natDegree : ℤ) := by
        have h := (Nat.cast_le (α := ℤ)).mpr K.K_tot_bound
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hU.2.1,
          Nat.cast_sub (show S.n3U ≤ 3 * D.n3 by linarith only [hU.2.2.1])] at h; exact h
      have hg2l_Z : ((D.gj 2).natDegree : ℤ) ≤ (D.W_F : ℤ) + 1 - 5 * (wY : ℤ) := by
        have h := (Nat.cast_le (α := ℤ)).mpr (D.natDegree_gj_le 2)
        simp only [Fin.val_two, Nat.cast_sub h5, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h; exact h
      have hg1l_Z : ((D.gj 1).natDegree : ℤ) ≤ (D.W_F : ℤ) + 1 - 3 * (wY : ℤ) := by
        have h := (Nat.cast_le (α := ℤ)).mpr (D.natDegree_gj_le 1)
        simp only [Fin.val_one, Nat.cast_sub h3w_le1, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h; exact h
      have h338_Z : 2 * (5 * (S.p.natDegree : ℤ) - 2 * (S.D1.natDegree : ℤ) + (K.K1.natDegree : ℤ) + (K.Lam1.natDegree : ℤ)) ≤
          ((D.gj 2).natDegree : ℤ) + ((D.gj 1).natDegree : ℤ) := by
        have h := (Nat.cast_le (α := ℤ)).mpr K.row338_bound
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_sub (show 2 * S.D1.natDegree ≤ 5 * S.p.natDegree by linarith only [hdD])] at h; exact h
      have h339 := K.row339_bound
      have h340 := K.row340_bound
      have hResY_eK' : 4 * (K.d2k0Cnt : ℤ) + 3 * (K.d2k1UCnt : ℤ) + 20 * (K.din2Cnt : ℤ) + 10 * (K.dmL2Cnt : ℤ) -
          8 * (eK_cnt : ℤ) + (4 * (D.n1 : ℤ) - 3 * (S.n1U : ℤ)) + (16 * (D.n2 : ℤ) - 5 * (S.n2U : ℤ)) +
          (34 * (D.n3 : ℤ) - 5 * (S.n3U : ℤ)) + 18 * (D.nt : ℤ) ≤ (D.ResY.natDegree : ℤ) := hResY_eK
      have hmu1_Z' : (K.mu1Cnt : ℤ) ≤ (S.n1U : ℤ) := Nat.cast_le.mpr hmu1_le_n1U
      have hdmL_Z' : (K.dmLCnt : ℤ) ≤ (K.mLCnt : ℤ) := Nat.cast_le.mpr hdmL_le_mL
      refine ⟨by linarith only [hmL_Z], by linarith only [hmu1_d2k1_Z], by linarith only [hM0sb_Z, hmu_eq_Z],
              by linarith only [h321],
              by linarith only [hg2tb_Z, hgr_Z, hmu1_d2k1_Z],
              by linarith only [hg2tb_Z, hgr_Z],
              by linarith only [hg1d_Z], by exact_mod_cast K.g2_din_bound, by linarith only [hg2b_Z],
              by linarith only [hResY_u_Z, hResY_hi_Z],
              by linarith only [hResY_eK', hResY_hi_Z],
              by linarith only [hResY_eq_Z, hg1_Z, hResY_hi_Z],
              by linarith only [hResY_u_Z, hResY_eq_Z, hg1_Z],
              by linarith only [hResY_eK', hResY_eq_Z, hg1_Z],
              by linarith only [hH1d_Z, hH1_Z, hg1_Z],
              by linarith only [hLM_Z],
              by linarith only [hKt_Z],
              by linarith only [hg2l_Z],
              by linarith only [hg1_Z, hK1b_Z, hg2tb_Z, Nat.cast_nonneg (α := ℤ) K.d2k0Cnt, hmu1_Z', hdmL_Z'],
              by linarith only [hg1l_Z],
              by push_cast; linarith only [h338_Z],
              by push_cast; linarith only [h339],
              by linarith only [h340],
              by exact_mod_cast S.aU_sum_le_UP⟩)
    ⟨fun hrt => by
        have hr : 2 * S.p.natDegree + wY < S.R.natDegree := by simpa [br, rGt] using hrt
        have hUP := S.natDegree_UP_eq_of_gt hr
        dsimp [v]; push_cast
        have h1 : 2 * (S.p.natDegree : ℤ) + (wY : ℤ) < (S.R.natDegree : ℤ) := by exact_mod_cast hr
        have h2 : (S.UP.natDegree : ℤ) = (S.R.natDegree : ℤ) := by exact_mod_cast hUP
        exact ⟨by linarith only [h1], h2⟩,
     fun hrf => by
        have hle : S.R.natDegree ≤ 2 * S.p.natDegree + wY := by
          have : ¬ (2 * S.p.natDegree + wY < S.R.natDegree) := by simpa [br, rGt] using hrf
          exact Nat.le_of_not_lt this
        have hUP := S.natDegree_UP_le_of_le hle
        dsimp [v]; push_cast
        exact ⟨by exact_mod_cast hle, by exact_mod_cast hUP⟩⟩
    ⟨fun hvt => by
        have hvc : S.M20 = 0 ∨ S.M20.natDegree < (K.Lam1 * K.M0s).natDegree := by simpa [br, vCancel] using hvt
        have hsum_M0 : K.Lam1 * K.M0s = S.M20 + S.D2 * K.p1 ^ 2 * K.q1 * K.K1 * K.Lam1 := by
          rw [K.hM0s_def, mul_add, ← K.hM20_fac]; ring
        have hq1_ne : K.q1 ≠ 0 := by
          intro hq0; rw [hq0] at hsum_M0; simp only [mul_zero, zero_mul, add_zero] at hsum_M0
          rcases hvc with h0 | hlt
          · rw [h0] at hsum_M0; exact mul_ne_zero K.hLam1_ne K.hM0s_ne hsum_M0
          · rw [hsum_M0] at hlt; exact lt_irrefl _ hlt
        have hR_deg : S.R.natDegree = S.D1.natDegree + K.q1.natDegree := by
          rw [← S.natDegree_q_eq_R, K.hq_fac, natDegree_mul S.D2_ne_zero hq1_ne, ← S.D1_natDegree]
        have hB_deg : (S.D2 * K.p1 ^ 2 * K.q1 * K.K1 * K.Lam1).natDegree =
            S.D1.natDegree + 2 * K.p1.natDegree + K.q1.natDegree + K.K1.natDegree + K.Lam1.natDegree := by
          rw [natDegree_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero S.D2_ne_zero (pow_ne_zero 2 K.hp1_ne)) hq1_ne) K.hK1_ne) K.hLam1_ne,
            natDegree_mul (mul_ne_zero (mul_ne_zero S.D2_ne_zero (pow_ne_zero 2 K.hp1_ne)) hq1_ne) K.hK1_ne,
            natDegree_mul (mul_ne_zero S.D2_ne_zero (pow_ne_zero 2 K.hp1_ne)) hq1_ne,
            natDegree_mul S.D2_ne_zero (pow_ne_zero 2 K.hp1_ne), natDegree_pow, ← S.D1_natDegree]
        have hdeg_eq : (K.Lam1 * K.M0s).natDegree = (S.D2 * K.p1 ^ 2 * K.q1 * K.K1 * K.Lam1).natDegree := by
          rcases hvc with h0 | hlt
          · rw [hsum_M0, h0, zero_add]
          · have hltB : S.M20.natDegree < (S.D2 * K.p1 ^ 2 * K.q1 * K.K1 * K.Lam1).natDegree := by
              have hle := natDegree_add_le S.M20 (S.D2 * K.p1 ^ 2 * K.q1 * K.K1 * K.Lam1)
              rw [← hsum_M0] at hle
              rcases max_cases S.M20.natDegree (S.D2 * K.p1 ^ 2 * K.q1 * K.K1 * K.Lam1).natDegree with ⟨hm, _⟩ | ⟨hm, _⟩
              · rw [hm] at hle; exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)
              · rw [hm] at hle; exact lt_of_lt_of_le hlt hle
            rw [hsum_M0, natDegree_add_eq_right_of_natDegree_lt hltB]
        rw [natDegree_mul K.hLam1_ne K.hM0s_ne, hB_deg] at hdeg_eq
        have hp_Z : (S.p.natDegree : ℤ) = (S.D1.natDegree : ℤ) + (K.p1.natDegree : ℤ) := by exact_mod_cast K.natDegree_p_eq
        have hR_Z : (S.R.natDegree : ℤ) = (S.D1.natDegree : ℤ) + (K.q1.natDegree : ℤ) := by exact_mod_cast hR_deg
        have hd_Z : (K.Lam1.natDegree : ℤ) + (K.M0s.natDegree : ℤ) =
            (S.D1.natDegree : ℤ) + 2 * (K.p1.natDegree : ℤ) + (K.q1.natDegree : ℤ) + (K.K1.natDegree : ℤ) + (K.Lam1.natDegree : ℤ) := by
          exact_mod_cast hdeg_eq
        dsimp [v]; push_cast; linarith only [hp_Z, hR_Z, hd_Z],
     fun hvf => by
        have hvc : ¬ (S.M20 = 0 ∨ S.M20.natDegree < (K.Lam1 * K.M0s).natDegree) := by simpa [br, vCancel] using hvf
        push Not at hvc
        rw [natDegree_mul K.hLam1_ne K.hM0s_ne] at hvc
        have h20 := S.two_mul_natDegree_p_mul_M20_le_with_g2
        rw [natDegree_mul S.hp hvc.1] at h20
        have hUP := S.natDegree_UP_mul_M20_le
        rw [natDegree_mul S.UP_ne_zero (mt (comp_X_sq_eq_zero_iff S.M20).mp hvc.1), natDegree_comp_X_sq] at hUP
        have hvc_Z : (K.Lam1.natDegree : ℤ) + (K.M0s.natDegree : ℤ) ≤ (S.M20.natDegree : ℤ) := by exact_mod_cast hvc.2
        have h20_Z : 2 * ((S.p.natDegree : ℤ) + (S.M20.natDegree : ℤ)) ≤ (D.W_F : ℤ) - (wY : ℤ) + ((D.gj 2).natDegree : ℤ) := by
          have h := (Nat.cast_le (α := ℤ)).mpr h20
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hw_le_WF] at h; exact h
        have hUP_Z : (S.UP.natDegree : ℤ) + 2 * (S.M20.natDegree : ℤ) ≤ 2 * (D.W_F : ℤ) - 5 * (wY : ℤ) + 1 := by
          have h := (Nat.cast_le (α := ℤ)).mpr hUP
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h5w_le2] at h; exact h
        dsimp [v]; push_cast; exact ⟨by linarith only [hvc_Z, h20_Z], by linarith only [hvc_Z, hUP_Z]⟩⟩
    ⟨fun hq0 => by
        have h0 : S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 := by
          dsimp [br, q1Case] at hq0; split_ifs at hq0 with c1 c2 <;> first | exact c1 | cases hq0
        have h0_Z : (S.H1.natDegree : ℤ) ≤ 8 * (S.p.natDegree : ℤ) + (D.W_F : ℤ) - (wY : ℤ) + 1 := by
          have h := (Nat.cast_le (α := ℤ)).mpr h0
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_sub (show wY ≤ 8 * S.p.natDegree + D.W_F by linarith only [hw_le_WF])] at h; exact h
        dsimp [v]; push_cast; linarith only [h0_Z, hH1_Z, hg1_Z],
     fun hq1 => by
        have h1 : S.H1.natDegree ≤ 4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree := by
          dsimp [br, q1Case] at hq1; split_ifs at hq1 with c1 c2 <;> first | exact c2 | cases hq1
        have h1_Z : (S.H1.natDegree : ℤ) ≤ 4 * (S.p.natDegree : ℤ) + 2 * (S.R.natDegree : ℤ) + ((D.gj 1).natDegree : ℤ) := by
          exact_mod_cast h1
        dsimp [v]; push_cast; linarith only [h1_Z, hH1_Z, hg1_Z],
     fun hq0 hq1 => by
        have h01 : ¬ (S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1) ∧
            ¬ (S.H1.natDegree ≤ 4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree) := by
          dsimp [br, q1Case] at hq0 hq1; split_ifs at hq0 hq1 with c1 c2
          · exact absurd rfl hq0
          · exact absurd rfl hq1
          · exact ⟨c1, c2⟩
        have h2 : S.H1.natDegree ≤ 4 * S.R.natDegree + (D.gj 2).natDegree := by
          rcases KerD45KData.q1_trichotomy (S := S) with ha | hb | hc
          · exact absurd ha h01.1
          · exact absurd hb h01.2
          · exact hc
        have h2_Z : (S.H1.natDegree : ℤ) ≤ 4 * (S.R.natDegree : ℤ) + ((D.gj 2).natDegree : ℤ) := by exact_mod_cast h2
        simp only [v]; push_cast; linarith only [h2_Z, hH1_Z, hg1_Z]⟩
    ⟨fun hlt4 => by
        have hz : odeHolds := by
          by_contra hnz; dsimp [br, odeCase] at hlt4; rw [if_neg hnz] at hlt4; split_ifs at hlt4 <;> norm_num at hlt4
        have hoh := K.ode_holds_bounds hc0 hNdom_eq hNdom_deg hL4 hd1 hz
        have hoh1_Z : ((D.n1 : ℤ) - (K.d2k1UCnt : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) + (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) +
            2 * (D.nt : ℤ) ≤ (K.Lam1.natDegree : ℤ) + (K.M0s.natDegree : ℤ) := by
          have h := (Nat.cast_le (α := ℤ)).mpr hoh.1
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hd2k1_le_n1,
            Nat.cast_sub (show S.n2U ≤ 2 * D.n2 by linarith only [hU.2.1]),
            Nat.cast_sub (show S.n3U ≤ 4 * D.n3 by linarith only [hU.2.2.1])] at h; exact h
        refine ⟨by simp only [v]; linarith only [hoh1_Z], by simp only [v]; linarith only [hoh.2.1, hmu_eq_Z], ?_⟩
        unfold r15Rhs; simp only [v, e1_tot, row0A_2_vals]; push_cast; linarith only [hoh.2.2.1, hmu_eq_Z],
     fun hge4 => by
        have hnz : ¬ odeHolds := by
          intro hz; apply hge4; dsimp [br, odeCase]; rw [if_pos hz]; split_ifs <;> norm_num
        have hfail := K.ode_fail_bound hd1 hd2 hnz
        have hN1_Z : (K.N1.natDegree : ℤ) = (N1_deg : ℤ) := by exact_mod_cast hN1_deg_eq
        simp only [v, H_rem_deg]; push_cast; linarith only [hfail, hN1_Z],
     fun hor => by
        have hHK' : K.HK.derivative = 0 := by
          by_contra hne
          rcases hor with h | h <;>
            (dsimp [br, odeCase] at h; by_cases hz : odeHolds
             · rw [if_pos hz, if_neg hne] at h; split_ifs at h <;> norm_num at h
             · rw [if_neg hz, if_neg hne] at h; split_ifs at h <;> norm_num at h)
        have hb := K.b1_holds_bounds hHK'
        have hb1_Z : (K.M0eff.natDegree : ℤ) + 2 * (K.Lam1.natDegree : ℤ) + 10 * (S.p.natDegree : ℤ) - 4 * (S.D1.natDegree : ℤ) =
            ((D.gj 2).natDegree : ℤ) + (K.g2rem.natDegree : ℤ) := by
          have h := congrArg (Nat.cast (R := ℤ)) hb.1
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_sub (show 4 * S.D1.natDegree ≤ K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree by linarith only [hdD])] at h
          exact h
        have hM0eff_Z' : (K.M0eff.natDegree : ℤ) = (M0_eff_deg : ℤ) := by exact_mod_cast hM0eff_deg
        refine ⟨by simp only [v, e1_tot]; push_cast; linarith only [hb1_Z, hM0eff_Z'], ?_, ?_⟩
        · unfold r15Rhs; simp only [v, e1_tot, row0C0_2_vals]; push_cast; linarith only [hb.2.1, hmu_eq_Z]
        · unfold r15Rhs; simp only [v, e1_tot, row0C1_2_vals]; push_cast; linarith only [hb.2.2, hmu_eq_Z],
     fun hor => by
        have hfl : K.HK.derivative ≠ 0 ∧ K.HK.natDegree < N + K.HK.derivative.natDegree := by
          rcases hor with h | h | h <;>
            (dsimp [br, odeCase] at h; by_cases hz : odeHolds
             · rw [if_pos hz] at h; by_cases hH : K.HK.derivative = 0
               · rw [if_pos hH] at h; norm_num at h
               · rw [if_neg hH] at h; by_cases hlt : K.HK.natDegree < N + K.HK.derivative.natDegree
                 · exact ⟨hH, hlt⟩
                 · rw [if_neg hlt] at h; norm_num at h
             · rw [if_neg hz] at h; by_cases hH : K.HK.derivative = 0
               · rw [if_pos hH] at h; norm_num at h
               · rw [if_neg hH] at h; by_cases hlt : K.HK.natDegree < N + K.HK.derivative.natDegree
                 · exact ⟨hH, hlt⟩
                 · rw [if_neg hlt] at h; norm_num at h)
        have hw2 := (K.w2_degree_bounds hc0 hNdom_deg hd1 hfl.1).1 hfl.2
        have hw21_Z : (N : ℤ) ≤ 2 * (K.M0eff.natDegree : ℤ) + 2 * (K.Lam1.natDegree : ℤ) + 10 * (S.p.natDegree : ℤ) - 4 * (S.D1.natDegree : ℤ) := by
          have h := (Nat.cast_le (α := ℤ)).mpr hw2.1
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_sub (show 4 * S.D1.natDegree ≤ 2 * K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree by linarith only [hdD])] at h
          exact h
        have hM0eff_Z' : (K.M0eff.natDegree : ℤ) = (M0_eff_deg : ℤ) := by exact_mod_cast hM0eff_deg
        simp only [v, e1_tot]; push_cast; exact ⟨by linarith only [hw21_Z, hM0eff_Z'], by linarith only [hw2.2, hM0eff_Z']⟩,
     fun hc1 => by
        have hfl : isW2a1 := by
          by_contra hnw; dsimp [br, odeCase] at hc1
          by_cases hz : odeHolds
          · rw [if_pos hz] at hc1; by_cases hH : K.HK.derivative = 0
            · rw [if_pos hH] at hc1; norm_num at hc1
            · rw [if_neg hH] at hc1; by_cases hlt : K.HK.natDegree < N + K.HK.derivative.natDegree
              · rw [if_pos hlt, if_neg hnw] at hc1; norm_num at hc1
              · rw [if_neg hlt] at hc1; norm_num at hc1
          · rw [if_neg hz] at hc1; split_ifs at hc1 <;> norm_num at hc1
        unfold r15Rhs; simp only [v, rowC04_2_vals]; push_cast; linarith only [hfl, hmu_eq_Z],
     fun hc2 => by
        have hfl : odeHolds ∧ K.HK.derivative ≠ 0 ∧ ¬ isW2a1 := by
          by_contra hbad; dsimp [br, odeCase] at hc2
          by_cases hz : odeHolds
          · rw [if_pos hz] at hc2
            by_cases hH : K.HK.derivative = 0
            · rw [if_pos hH] at hc2; norm_num at hc2
            · rw [if_neg hH] at hc2
              by_cases hlt : K.HK.natDegree < N + K.HK.derivative.natDegree
              · rw [if_pos hlt] at hc2
                by_cases hw1 : isW2a1
                · rw [if_pos hw1] at hc2; norm_num at hc2
                · exact hbad ⟨hz, hH, hw1⟩
              · rw [if_neg hlt] at hc2; norm_num at hc2
          · rw [if_neg hz] at hc2; split_ifs at hc2 <;> norm_num at hc2
        have hoh := K.ode_holds_bounds hc0 hNdom_eq hNdom_deg hL4 hd1 hfl.1
        have hw2 := (hoh.2.2.2 hfl.2.1).resolve_left hfl.2.2
        unfold r15Rhs; simp only [v, rowC04_2_vals]; push_cast; linarith only [hw2, hmu_eq_Z],
     fun hor => by
        have hfl : K.HK.derivative ≠ 0 ∧ N + K.HK.derivative.natDegree ≤ K.HK.natDegree := by
          rcases hor with h | h <;>
            (dsimp [br, odeCase] at h; by_cases hz : odeHolds
             · rw [if_pos hz] at h; by_cases hH : K.HK.derivative = 0
               · rw [if_pos hH] at h; cases h
               · rw [if_neg hH] at h; by_cases hlt : K.HK.natDegree < N + K.HK.derivative.natDegree
                 · rw [if_pos hlt] at h; split_ifs at h <;> cases h
                 · exact ⟨hH, Nat.le_of_not_lt hlt⟩
             · rw [if_neg hz] at h; by_cases hH : K.HK.derivative = 0
               · rw [if_pos hH] at h; cases h
               · rw [if_neg hH] at h; by_cases hlt : K.HK.natDegree < N + K.HK.derivative.natDegree
                 · rw [if_pos hlt] at h; cases h
                 · exact ⟨hH, Nat.le_of_not_lt hlt⟩)
        have hw2 := (K.w2_degree_bounds hc0 hNdom_deg hd1 hfl.1).2 hfl.2
        have hw21_Z : (N : ℤ) ≤ (K.M0eff.natDegree : ℤ) + ((D.gj 2).natDegree : ℤ) + (K.g2rem.natDegree : ℤ) := by exact_mod_cast hw2.1
        have hM0eff_Z' : (K.M0eff.natDegree : ℤ) = (M0_eff_deg : ℤ) := by exact_mod_cast hM0eff_deg
        dsimp [v, e1_tot]; push_cast; exact ⟨by linarith only [hw21_Z, hM0eff_Z'], by linarith only [hw2.2, hM0eff_Z']⟩⟩
    hode_lt

/-! ### Part 5: Top-Level Exhaustive Table 4 Algebra Dichotomy (All 120 Branches + `EscapeUZero`) -/

/-- **Direct Syzygy Table 4 Dispatch (`table4_algebra_of_syzygy`):**
Given an explicit `S : KerD45Syzygy D` (with `S.p ≠ 0` and `U(X, P(X)) ≠ 0` already established),
`D` directly satisfies one of the Table 4A (`p0` / `b1c1`) or Table 4B (`K ≠ 0`) branches, with NO
`EscapeUZero` disjunct! -/
theorem table4_algebra_of_syzygy {D : KerD45Data} (S : KerD45Syzygy D)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    (∃ br : T4ABranch,
      (match br with
       | .det | .p0Zero => True
       | .p0 m21Nz _ p0M10D4 q2M21M10 => m21Nz = false → p0M10D4 = true ∧ q2M21M10 = false
       | .b1c1 _ _ bCase => bCase < 6) ∧
      let rows := buildT4ARows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      ∃ x : Fin (t4aNumVars br) → ℚ,
        (∀ j, 0 ≤ x j) ∧
        x ⟨0, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n0 : ℚ) / (N : ℚ) ∧
        x ⟨1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
        x ⟨2, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n2 : ℚ) / (N : ℚ) ∧
        x ⟨3, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
        x ⟨4, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.nt : ℚ) / (N : ℚ) ∧
        x ⟨t4aNumVars br - 1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
        (∀ r ∈ rows.1.toList, RowValid (t4aNumVars br) r ∧ RowSatLe x r) ∧
        (∀ r ∈ rows.2.toList, RowValid (t4aNumVars br) r ∧ RowSatEq x r)) ∨
    (∃ br : T4BBranch, br.q1Case < 3 ∧ br.odeCase < 7 ∧
      let rows := buildT4BRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      ∃ x : Fin 49 → ℚ,
        (∀ j, 0 ≤ x j) ∧
        x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
        x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
        x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨48, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
        (∀ r ∈ rows.1.toList, RowValid 49 r ∧ RowSatLe x r) ∧
        (∀ r ∈ rows.2.toList, RowValid 49 r ∧ RowSatEq x r)) := by
  by_cases hP0 : S.P0 ≠ 0
  · left
    obtain ⟨m21Nz, rGt, p0M10D4, q2M21M10, hvalid, hx⟩ :=
      table4_p0_sat S hP0 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
        hcLoD hcHiD hloGD hhiGD hcLo hcHi hloG hhiG
    exact ⟨.p0 m21Nz rGt p0M10D4 q2M21M10, hvalid, hx⟩
  · push Not at hP0
    by_cases hM21 : S.M21 = 0
    · left
      obtain ⟨rGt, r4g4, bCase, hbLt, hx⟩ :=
        table4_b1c1_sat S hP0 hM21 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
          hcLoD hcHiD hloGD hhiGD hcLo hcHi hloG hhiG
      exact ⟨.b1c1 rGt r4g4 bCase, hbLt, hx⟩
    · right
      exact table4_K_sat S hP0 hM21 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
        hcLoD hcHiD hloGD hhiGD hcLo hcHi hloG hhiG

/-- **Master Exhaustive Table 4 Theorem:**
For ANY `D : KerD45Data` in bin `[cLo, cHi]` and bucket `[loG, hiG]`, EITHER:
1. `EscapeUZero D` (`U(X, P(X)) = 0` for a coprime syzygy `(p, c, b)` with `p ≠ 0`), OR
2. `D` satisfies one of the 36 valid Table 4A branches (`T4ABranch`: `det`, `p0Zero`, 10 `p0`, 24 `b1c1`), OR
3. `D` satisfies one of the 84 valid Table 4B branches (`T4BBranch`: `q1Case < 3 ∧ odeCase < 7`). -/
theorem table4_algebra_dichotomy (D : KerD45Data)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    EscapeUZero D ∨
    (∃ br : T4ABranch,
      (match br with
       | .det | .p0Zero => True
       | .p0 m21Nz _ p0M10D4 q2M21M10 => m21Nz = false → p0M10D4 = true ∧ q2M21M10 = false
       | .b1c1 _ _ bCase => bCase < 6) ∧
      let rows := buildT4ARows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      ∃ x : Fin (t4aNumVars br) → ℚ,
        (∀ j, 0 ≤ x j) ∧
        x ⟨0, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n0 : ℚ) / (N : ℚ) ∧
        x ⟨1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
        x ⟨2, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n2 : ℚ) / (N : ℚ) ∧
        x ⟨3, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
        x ⟨4, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.nt : ℚ) / (N : ℚ) ∧
        x ⟨t4aNumVars br - 1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
        (∀ r ∈ rows.1.toList, RowValid (t4aNumVars br) r ∧ RowSatLe x r) ∧
        (∀ r ∈ rows.2.toList, RowValid (t4aNumVars br) r ∧ RowSatEq x r)) ∨
    (∃ br : T4BBranch, br.q1Case < 3 ∧ br.odeCase < 7 ∧
      let rows := buildT4BRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      ∃ x : Fin 49 → ℚ,
        (∀ j, 0 ≤ x j) ∧
        x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
        x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
        x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨48, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
        (∀ r ∈ rows.1.toList, RowValid 49 r ∧ RowSatLe x r) ∧
        (∀ r ∈ rows.2.toList, RowValid 49 r ∧ RowSatEq x r)) := by
  by_cases hdet : D.detM ≠ 0
  · right; left
    exact ⟨.det, trivial, D.table4_det_sat hdet cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      hcLoD hcHiD hloGD hhiGD hcLo hcHi hloG hhiG⟩
  · push Not at hdet
    obtain ⟨p, c, b, hne, hcop, hsyz⟩ := D.exists_coprime_syzygy hdet
    by_cases hp : p = 0
    · subst hp
      right; left
      have hne' : c ≠ 0 ∨ b ≠ 0 := hne.resolve_left (not_not.mpr rfl)
      have hcop' : ∀ d : Fld[X], d ∣ c → d ∣ b → IsUnit d := fun d hdc hdb => hcop d (dvd_zero d) hdc hdb
      have hsyz' : ∀ j : Fin 3, c * D.Cj j + b * D.Bj j = 0 := fun j => by
        simpa using hsyz j
      exact ⟨.p0Zero, trivial, D.table4_p0Zero_sat hne' hcop' hsyz'
        cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
        hcLoD hcHiD hloGD hhiGD hcLo hcHi hloG hhiG⟩
    · by_cases hUP : p.comp (X ^ 2) * D.P + b.comp (X ^ 2) + X * c.comp (X ^ 2) = 0
      · left; exact ⟨p, c, b, hp, hcop, hsyz, hUP⟩
      · right
        exact table4_algebra_of_syzygy ⟨p, c, b, hp, hcop, hsyz, hUP⟩
          cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
          hcLoD hcHiD hloGD hhiGD hcLo hcHi hloG hhiG

end B6401Table4K
end ProximityPrize.SubmissionBinaryLower
