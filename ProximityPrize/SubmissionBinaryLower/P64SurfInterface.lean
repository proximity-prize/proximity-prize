import ProximityPrize.SubmissionBinaryLower.P64Charging
import ProximityPrize.Benchmark.BinaryTargetLower

/-!
# The surface interface (formal-plan.md section 3, I1)

The surface-theory steps of PROOF.md (Theorems N1, B', F, Lemmas N2 and TW) are not formalised.
They are isolated behind one `Prop`, `SurfaceInterface K1 K2 K3`: a per-factor bound on the
dangerous slopes of an F-irreducible factor (or of its Frobenius twist at scale `e`) that is
neither S_4-good nor AF-light. Every theorem that uses it takes it as a hypothesis.

Parameters (PROOF.md 1.5): `n = 2^21`, `D = 1048575`, `A = 1482911`, `m = 249292`,
`J = 352553`, `DZ = 58589180686`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Surf

open Polynomial P64LineOrder BCHKSSubstitutionVanish
open ProximityPrize.Benchmark

local notation "Fld" => ProximityPrize.Benchmark.BinaryIRSProfile.Field
local notation "Idx" => ProximityPrize.Benchmark.BinaryIRSProfile.Index
local notation "Tri" => Polynomial (Polynomial (Polynomial Fld))

/-- Line `i` at scale `e`: `Y = u0(x_i) + V^(2^e)·u1(x_i)`. `e = 0` is PROOF.md's `l_i`. -/
noncomputable def lineY (U : Fin 2 → Idx → Fld) (e : ℕ) (i : Idx) : Fld[X] :=
  (Polynomial.C (U 0 i) : Polynomial Fld) + Polynomial.X ^ (2 ^ e) * Polynomial.C (U 1 i)

/-- Order of `T` along line `i` at scale `e`. -/
noncomputable def lineOrdS (U : Fin 2 → Idx → Fld) (e : ℕ) (T : Tri) (i : Idx) : ℕ :=
  lineOrd T (BinaryIRSProfile.domain i) (lineY U e i)

/-- `h` of the original factor `R` with twist `T` at scale `e`. -/
noncomputable def hS (e : ℕ) (T : Tri) : ℕ := 2 ^ e * T.natDegree

/-- `w` of the original factor. -/
noncomputable def wS (e : ℕ) (T : Tri) : ℕ :=
  2 ^ e * P64Caps.Weighted.weightedSupportDegree T 1048575

/-- `d` of the original factor. -/
noncomputable def dS (e : ℕ) (T : Tri) : ℕ := P64Caps.YZ.yzSupportDegree T (2 ^ e)

/-- `μ_i` of the original factor. -/
noncomputable def muS (U : Fin 2 → Idx → Fld) (e : ℕ) (T : Tri) (i : Idx) : ℕ :=
  2 ^ e * lineOrdS U e T i

/-- The lines on the factor. -/
noncomputable def Lam (U : Fin 2 → Idx → Fld) (e : ℕ) (T : Tri) : Finset Idx :=
  Finset.univ.filter fun i => 0 < lineOrdS U e T i

/-- The full lines. -/
noncomputable def fullLines (U : Fin 2 → Idx → Fld) (e : ℕ) (T : Tri) : Finset Idx :=
  Finset.univ.filter fun i => lineOrdS U e T i = T.natDegree

/-- Dangerous at scale `e`: `Σ_{i ∈ Az} (μ_i - 1) ≥ w - A + 1`. At `e = 0` this is
`P64Cofactor.Dangerous` at `k = D`, `Agr = A`. -/
def DangerousS (U : Fin 2 → Idx → Fld) (e : ℕ) (T : Tri) (Az : Finset Idx) : Prop :=
  (wS e T : ℤ) - 1482911 + 1 ≤ ∑ i ∈ Az, ((muS U e T i : ℤ) - 1)

/-- `M(W) = #{(a, j) ∈ ℕ² : a + D·j ≤ W}`, in closed form per `j`. -/
def Mbox (W : ℕ) : ℕ := ∑ j ∈ Finset.range (W / 1048575 + 1), (W - 1048575 * j + 1)

/-- (3.2) at `t = 4` for some `1 ≤ q ≤ 4·DZ`. -/
def S4Good (U : Fin 2 → Idx → Fld) (e : ℕ) (T : Tri) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ 4 * 58589180686 ∧
    (q + (4 * wS e T - 1482911) / 1048575) *
        ∑ i ∈ Lam U e T, (4 * muS U e T i - 1) * (4 * muS U e T i) / 2 <
      q * Mbox (4 * wS e T - 1482911)

/-- Lemma AF applies: many full lines, or few lines. -/
def AFLight (U : Fin 2 → Idx → Fld) (e : ℕ) (T : Tri) : Prop :=
  208984 ≤ (fullLines U e T).card ∨ (Lam U e T).card ≤ 208983

/-- **I1**, the coarse surface interface of formal-plan.md section 3. -/
def SurfaceInterface (K1 K2 K3 : ℚ) : Prop :=
  ∀ (U : Fin 2 → Idx → Fld) (e : ℕ) (T : Tri) (Vs : Finset Fld)
    (P : Fld → Fld[X]) (Az : Fld → Finset Idx),
    Irreducible T → derivative T ≠ 0 → 2 ≤ T.natDegree → 4 ≤ hS e T →
    wS e T ≤ 249292 * 1482911 - 1 → dS e T ≤ 58589180686 - 1 →
    ¬ S4Good U e T → ¬ AFLight U e T →
    (∀ v ∈ Vs, (P v).natDegree ≤ 1048575 ∧ 1482911 ≤ (Az v).card ∧
      (∀ i ∈ Az v, (P v).eval (BinaryIRSProfile.domain i) = U 0 i + v ^ (2 ^ e) * U 1 i) ∧
      triEval T v (P v) = 0 ∧ DangerousS U e T (Az v)) →
    (Vs.card : ℚ) ≤ K1 * 2097152 * dS e T + K2 * hS e T * dS e T +
      K3 * 2097152 * (dS e T + hS e T)

end P64Surf
end ProximityPrize.SubmissionBinaryLower
