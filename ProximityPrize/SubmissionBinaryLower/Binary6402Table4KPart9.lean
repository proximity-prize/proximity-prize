import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart8
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
def conditions_hub_nat2 (v : Fin 48 → ℕ) (br : T4BBranch) (WF : ℕ) : Prop :=
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
      (v ⟨22, by decide⟩ : ℤ) + (v ⟨23, by decide⟩ : ℤ) + (v ⟨24, by decide⟩ : ℤ) ≤ (v ⟨15, by decide⟩ : ℤ)
theorem geometry_hub_nat2 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S)
    (c0 c1 : Fld) (L : Fld[X]) (hc0 : c0≠0)
    (hNdom_eq : Ndom=C c0*X+C c1*X^2+L^4) (hNdom_deg : Ndom.natDegree=N)
    (hL4 : 4*L.natDegree=N) (hd1 : Ndom.derivative=C c0) :
  conditions_hub_nat2 (geometryVec S K) (geometryBranch S K c0 c1) D.W_F := by
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
  change conditions_hub_nat2 v br D.W_F
  unfold conditions_hub_nat2
  have h5 := D.hWF_lo
  have hw := D.hwY_pos
  have hU := S.U_counts_ineqs
  have hK1b := K.K1_base_le
  have hM0sb := K.M0s_base_le
  have hg2tb := K.g2t_extra_le
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
  have hdD : S.D1.natDegree ≤ S.p.natDegree := S.D1_natDegree.symm ▸ S.D2_natDegree_le_p
  have hg1_eq := K.natDegree_g1_eq
  have hgr_eq := K.natDegree_g2rem
  have hg2b := K.g2_din2_full_bound
  have hH1_eq := K.natDegree_H1_eq
  have hResY_eq := K.natDegree_ResY_eq
  have hResY_hi := D.natDegree_ResY_le_col1
  have hResY_u := K.ResY_uncond_bound
  have hResY_eK := K.ResY_eK_bound
  have h2n3_le : S.n3U ≤ 2 * D.n3 := by linarith only [hU.2.2.1]
  have h20w_le : 20 * wY ≤ 8 * D.W_F := by linarith only [h5, hw]
  have h3w_le1 : 3 * wY ≤ D.W_F + 1 := by linarith only [h5]
  have hmL_le_s : K.mLCnt ≤ S.n2U + S.n3U + K.mbadCnt := by linarith only [hmb_mL]
  have hmb_le_s : K.mbadCnt ≤ S.n2U + S.n3U := by linarith only [hmb_mL]
  have hmu1_le_n1U : K.mu1Cnt ≤ S.n1U := by linarith only [hmu1_d2k1]
  have hK1b_Z : ((D.n2 : ℤ) - (S.n2U : ℤ)) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ) + (K.mbadCnt : ℤ) ≤ (K.K1.natDegree : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hK1b
    simp only [Nat.cast_add, Nat.cast_sub hU.2.1, Nat.cast_sub h2n3_le, Nat.cast_mul, Nat.cast_ofNat] at h; exact h
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
  have hg2b_Z : 3 * (K.din2Cnt : ℤ) + (K.dmL2Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (K.d2k0Cnt : ℤ) +
      (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) ≤ ((D.gj 2).natDegree : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hg2b
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h2n3_le] at h; exact h
  have hmu1_d2k1_Z : (K.mu1Cnt : ℤ) + (K.d2k1UCnt : ℤ) ≤ (S.n1U : ℤ) := by exact_mod_cast hmu1_d2k1
  exact (by
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

end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
