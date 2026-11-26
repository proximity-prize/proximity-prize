import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart23
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


end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
