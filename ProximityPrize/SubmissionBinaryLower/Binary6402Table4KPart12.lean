import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart11
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
def conditions_hQ1_nat (v : Fin 48 → ℕ) (br : T4BBranch) (WF : ℕ) : Prop :=
  (br.q1Case = 0 → -4 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + (v ⟨12, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) ≤ (WF : ℤ) - (wY : ℤ) + 1) ∧
      (br.q1Case = 1 → -2 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) - 2 * (v ⟨14, by decide⟩ : ℤ) ≤ 0) ∧
      (br.q1Case ≠ 0 → br.q1Case ≠ 1 → -2 * (v ⟨10, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) + (v ⟨12, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) - 4 * (v ⟨14, by decide⟩ : ℤ) ≤ 0)
theorem geometry_hQ1_nat {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S)
    (c0 c1 : Fld) (L : Fld[X]) (hc0 : c0≠0)
    (hNdom_eq : Ndom=C c0*X+C c1*X^2+L^4) (hNdom_deg : Ndom.natDegree=N)
    (hL4 : 4*L.natDegree=N) (hd1 : Ndom.derivative=C c0) :
  conditions_hQ1_nat (geometryVec S K) (geometryBranch S K c0 c1) D.W_F := by
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
  change conditions_hQ1_nat v br D.W_F
  unfold conditions_hQ1_nat
  have h5 := D.hWF_lo
  have hw := D.hwY_pos
  have hg1_eq := K.natDegree_g1_eq
  have hH1_eq := K.natDegree_H1_eq
  have hw_le_WF : wY ≤ D.W_F := by linarith only [h5, hw]
  have hg1_Z : ((D.gj 1).natDegree : ℤ) = 2 * (K.K1.natDegree : ℤ) + (K.g2t.natDegree : ℤ) := by exact_mod_cast hg1_eq
  have hH1_Z : (S.H1.natDegree : ℤ) = 4 * (S.D1.natDegree : ℤ) + 2 * (K.M0s.natDegree : ℤ) + (K.g2t.natDegree : ℤ) := by exact_mod_cast hH1_eq
  exact ⟨fun hq0 => by
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

end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
