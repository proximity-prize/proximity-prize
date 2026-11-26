import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart20
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

theorem valueAt (v : Fin 48 → ℕ) (wf j : ℕ) (hj : j<48) :
    t4bVec v wf ⟨j,by omega⟩=(v ⟨j,hj⟩ : ℚ)/(N : ℚ) := by unfold t4bVec; rw [dif_pos hj]
theorem valueLast (v : Fin 48 → ℕ) (wf : ℕ) : t4bVec v wf ⟨48,by decide⟩=(wf : ℚ)/(wY : ℚ) := by unfold t4bVec; rw [dif_neg (by decide)]
theorem valueNonneg (v : Fin 48 → ℕ) (wf : ℕ) (j : Fin 49) : 0≤t4bVec v wf j := by unfold t4bVec; split_ifs <;> positivity
theorem geometryValue0 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨0,by decide⟩=D.n0 := by simp only [geometryVec]
theorem geometryCoord0 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨0,by decide⟩=(D.n0 : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 0 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue0 S K))
theorem geometryValue1 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨1,by decide⟩=D.n1 := by simp only [geometryVec]
theorem geometryCoord1 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨1,by decide⟩=(D.n1 : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 1 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue1 S K))
theorem geometryValue2 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨2,by decide⟩=D.n2 := by simp only [geometryVec]
theorem geometryCoord2 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨2,by decide⟩=(D.n2 : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 2 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue2 S K))
theorem geometryValue3 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨3,by decide⟩=D.n3 := by simp only [geometryVec]
theorem geometryCoord3 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨3,by decide⟩=(D.n3 : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 3 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue3 S K))
theorem geometryValue4 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨4,by decide⟩=D.nt := by simp only [geometryVec]
theorem geometryCoord4 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨4,by decide⟩=(D.nt : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 4 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue4 S K))
theorem geometryValue5 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨5,by decide⟩=D.a0 := by simp only [geometryVec]
theorem geometryCoord5 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨5,by decide⟩=(D.a0 : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 5 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue5 S K))
theorem geometryValue6 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨6,by decide⟩=D.a1 := by simp only [geometryVec]
theorem geometryCoord6 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨6,by decide⟩=(D.a1 : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 6 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue6 S K))
theorem geometryValue7 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨7,by decide⟩=D.a2 := by simp only [geometryVec]
theorem geometryCoord7 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨7,by decide⟩=(D.a2 : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 7 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue7 S K))
theorem geometryValue8 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : geometryVec S K ⟨8,by decide⟩=D.a3 := by simp only [geometryVec]
theorem geometryCoord8 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨8,by decide⟩=(D.a3 : ℚ)/(N : ℚ) := (valueAt (geometryVec S K) D.W_F 8 (by decide)).trans (congrArg (fun n : ℕ => (n:ℚ)/(N:ℚ)) (geometryValue8 S K))
theorem geometryCoord9 {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) : (t4bVec (geometryVec S K) D.W_F) ⟨48,by decide⟩=(D.W_F : ℚ)/(wY : ℚ) := valueLast (geometryVec S K) D.W_F
theorem geometryNonneg {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S) (j : Fin 49) : 0≤(t4bVec (geometryVec S K) D.W_F) j := valueNonneg _ _ j

end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
