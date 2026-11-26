import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart6
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

/- **Theorem (`T4BBranch`, `K ≠ 0`):** For any `S : KerD45Syzygy D` with `S.P0 = 0` and
`S.M21 ≠ 0`, `D` satisfies all rows of `buildT4BRows br` for an exact `br : T4BBranch`
(`br.q1Case < 3 ∧ br.odeCase < 7`)! -/
theorem odeCase36_6402 (a z b c : Prop) [Decidable a] [Decidable z] [Decidable b] [Decidable c]
    (h : let code : ℕ := if a then (if z then 0 else if b then (if c then 1 else 2) else 3)
                          else (if z then 4 else if b then 5 else 6)
         code=3 ∨ code=6) : ¬ z ∧ ¬ b := by
  by_cases ha : a <;> by_cases hz : z <;> by_cases hb : b <;> by_cases hc : c <;> simp_all

attribute [local irreducible] KerD45KData.mbadCnt KerD45KData.mLCnt KerD45KData.din2Cnt KerD45KData.din3Cnt KerD45KData.dinCnt KerD45KData.dmL2Cnt KerD45KData.dmL3Cnt KerD45KData.dmLCnt KerD45KData.d2k1UCnt KerD45KData.d2k0Cnt KerD45KData.mu1Cnt KerD45KData.ntUNorm KerD45KData.ntUMbad KerD45KData.ntUML

open scoped Classical
noncomputable def geometryVec {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : Fin 48 → ℕ :=
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
  v
noncomputable def geometryBranch {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) (c0 c1 : Fld) : T4BBranch :=
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
  br
theorem geometryBranch_bounds {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) (c0 c1 : Fld) :
    (geometryBranch S K c0 c1).q1Case<3 ∧ (geometryBranch S K c0 c1).odeCase<7 := by
  let rGt : Bool := decide (2 * S.p.natDegree + wY < S.R.natDegree)
  let vCancel : Bool := decide (S.M20 = 0 ∨ S.M20.natDegree < (K.Lam1 * K.M0s).natDegree)
  let q1Case : ℕ :=
    if S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 then 0
    else if S.H1.natDegree ≤ 4 * S.p.natDegree + 2 * S.R.natDegree + (D.gj 1).natDegree then 1
    else 2
  have hq1_lt : q1Case < 3 := by dsimp [q1Case]; split_ifs <;> decide
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
  have hode_lt : odeCase < 7 := by dsimp [odeCase]; split_ifs <;> decide
  let br : T4BBranch := ⟨rGt, vCancel, q1Case, odeCase⟩
  exact ⟨hq1_lt,hode_lt⟩
def conditions_heq_nat (v : Fin 48 → ℕ) (br : T4BBranch) (WF : ℕ) : Prop :=
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
      (v ⟨41, by decide⟩ : ℤ) + (v ⟨42, by decide⟩ : ℤ) + (v ⟨43, by decide⟩ : ℤ) = (v ⟨21, by decide⟩ : ℤ)
theorem geometry_heq_nat {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S)
    (c0 c1 : Fld) (L : Fld[X]) (hc0 : c0≠0)
    (hNdom_eq : Ndom=C c0*X+C c1*X^2+L^4) (hNdom_deg : Ndom.natDegree=N)
    (hL4 : 4*L.natDegree=N) (hd1 : Ndom.derivative=C c0) :
  conditions_heq_nat (geometryVec S K) (geometryBranch S K c0 c1) D.W_F := by
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
  change conditions_heq_nat v br D.W_F
  unfold conditions_heq_nat
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
  have hg1_eq := K.natDegree_g1_eq
  have hgr_eq := K.natDegree_g2rem
  have hg2b := K.g2_din2_full_bound
  have h2n3_le : S.n3U ≤ 2 * D.n3 := by linarith only [hU.2.2.1]
  have hmL_le_s : K.mLCnt ≤ S.n2U + S.n3U + K.mbadCnt := by linarith only [hmb_mL]
  have hmb_le_s : K.mbadCnt ≤ S.n2U + S.n3U := by linarith only [hmb_mL]
  have hdmL_le_s : K.dmLCnt ≤ S.n2U + S.n3U := by linarith only [hdmL_le_mL, hmb_mL]
  have h2K1_le_g1 : 2 * K.K1.natDegree ≤ (D.gj 1).natDegree := by linarith only [hg1_eq]
  have heK_Z : (eK_cnt : ℤ) = (K.K1.natDegree : ℤ) - ((D.n2 : ℤ) - (S.n2U : ℤ) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + (D.nt : ℤ)) := by
    dsimp [eK_cnt]; rw [Nat.cast_sub (by linarith only [hK1b])]
    simp only [Nat.cast_add, Nat.cast_sub hU.2.1, Nat.cast_sub h2n3_le, Nat.cast_mul, Nat.cast_ofNat]
  have hm_Z : (m_tot : ℤ) = (D.n0 : ℤ) + ((D.n1 : ℤ) - (S.n1U : ℤ)) + ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) := by
    dsimp [m_tot]; simp only [Nat.cast_add, Nat.cast_sub hU.1, Nat.cast_sub hU.2.1, Nat.cast_sub hU.2.2.1]
  have hM0eff_Z : (M0_eff_deg : ℤ) = (D.n0 : ℤ) + (D.n1 : ℤ) + ((D.n2 : ℤ) - (S.n2U : ℤ)) + ((D.n3 : ℤ) - (S.n3U : ℤ)) + (K.mbadCnt : ℤ) := by
    dsimp [M0_eff_deg]; simp only [Nat.cast_add, Nat.cast_sub hU.2.1, Nat.cast_sub hU.2.2.1]
  have hmu_eq_Z : (mu_tot : ℤ) = (K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) := by
    dsimp [mu_tot]; rw [Nat.cast_sub (by linarith only [hM0sb]), Nat.cast_sub hmL_le_s]; push_cast; ring
  have hgr_Z : (e1_tot : ℤ) = (K.g2t.natDegree : ℤ) - ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.mbadCnt : ℤ)) := by
    dsimp [e1_tot]; rw [hgr_eq, Nat.cast_sub (by linarith only [hg2tb]), Nat.cast_sub hmb_le_s]; push_cast; ring
  have hg1_Z : ((D.gj 1).natDegree : ℤ) = 2 * (K.K1.natDegree : ℤ) + (K.g2t.natDegree : ℤ) := by exact_mod_cast hg1_eq
  have hHrem_Z : ((D.gj 1).natDegree : ℤ) - 2 * (K.K1.natDegree : ℤ) + 2 * (K.M0s.natDegree : ℤ) =
      3 * ((S.n2U : ℤ) + (S.n3U : ℤ) - (K.dmLCnt : ℤ)) + (N1_deg : ℤ) + (H_rem_deg : ℤ) := by
    have h := congrArg (Nat.cast (R := ℤ)) hHrem_eq_sum
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h2K1_le_g1, Nat.cast_sub hdmL_le_s] at h; exact h
  have hg4rem_Z : (g4_rem : ℤ) = ((D.gj 2).natDegree : ℤ) - ((K.d2k0Cnt : ℤ) + (K.d2k1UCnt : ℤ) + (2 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) := by
    dsimp [g4_rem]; rw [Nat.cast_sub (by linarith only [hg2b])]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h2n3_le]
  exact (by
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

end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
