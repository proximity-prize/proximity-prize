import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart10
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


open scoped Classical
def conditions_hV_nat (v : Fin 48 → ℕ) (br : T4BBranch) (WF : ℕ) : Prop :=
  (br.vCancel = true → (v ⟨13, by decide⟩ : ℤ) - (v ⟨9, by decide⟩ : ℤ) - (v ⟨10, by decide⟩ : ℤ) - (v ⟨14, by decide⟩ : ℤ) + 2 * (v ⟨17, by decide⟩ : ℤ) = 0) ∧
      (br.vCancel = false →
        (2 * (v ⟨9, by decide⟩ : ℤ) - 2 * (v ⟨11, by decide⟩ : ℤ) + 4 * (v ⟨13, by decide⟩ : ℤ) + 4 * (v ⟨16, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 2 * (wY : ℤ)) ∧
        (2 * (v ⟨13, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + (v ⟨15, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 5 * (wY : ℤ) + 1))
theorem geometry_hV_nat {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S)
    (c0 c1 : Fld) (L : Fld[X]) (hc0 : c0≠0)
    (hNdom_eq : Ndom=C c0*X+C c1*X^2+L^4) (hNdom_deg : Ndom.natDegree=N)
    (hL4 : 4*L.natDegree=N) (hd1 : Ndom.derivative=C c0) :
  conditions_hV_nat (geometryVec S K) (geometryBranch S K c0 c1) D.W_F := by
  classical
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
  let br : T4BBranch := ⟨rGt, vCancel, q1Case, odeCase⟩
  change conditions_hV_nat v br D.W_F
  unfold conditions_hV_nat
  have h5 := D.hWF_lo
  have hw := D.hwY_pos
  have hw_le_WF : wY ≤ D.W_F := by linarith only [h5, hw]
  have h5w_le2 : 5 * wY ≤ 2 * D.W_F := by linarith only [h5, hw]
  exact ⟨fun hvt => by
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

end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
