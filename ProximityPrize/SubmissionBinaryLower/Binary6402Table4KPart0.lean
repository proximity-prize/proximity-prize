import ProximityPrize.SubmissionBinaryLower.Binary6402Table4Common
import ProximityPrize.SubmissionBinaryLower.Binary6402Table4NonK

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

/-!
# Table 4B (`K ≠ 0`, 84 branches) and Top-Level Table 4 Exhaustive Algebra Dichotomy

Proves:
1. `table4_K_sat`: for any `S : KerD45Syzygy D` with `S.P0 = 0` and `S.M21 ≠ 0`, `D` produces an
   exact `T4BBranch` (`rGt ∈ Bool`, `vCancel ∈ Bool`, `q1Case < 3`, `odeCase < 7`) and an explicit
   nonnegative `x : Fin 49 → ℚ` satisfying ALL rows of `B6402T4Rows.buildT4BRows br`!
2. `table4_algebra_dichotomy`: for ANY `D : KerD45Data`, EITHER `EscapeUZero D`, OR `D` satisfies
   one of the 36 Table 4A branches (`T4ABranch`) OR one of the 84 Table 4B branches (`T4BBranch`)!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402Table4K

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6402IntFarkas B6402T4Rows B6401Char2ODE B6402Table4Common B6402Table4NonK
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

def muSub : Step15Pt → ℕ
  | .k2U | .k3U => 1
  | .k2U_mb | .k3U_mb => 2
  | _ => 0

lemma sub_zero_nr (n : ℕ) : n - 0 = n := by cases n <;> rfl

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
lemma exists_min_fourth_pow_cover (Q_red : Fld[X]) (hQ : Q_red ≠ 0) :
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

end KerD45KData
end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
