import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart14
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402T4Rows
import ProximityPrize.SubmissionBinaryLower.P64Resultant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1024

/-!
# Table 4 Common `ker(D)` `(d₁ = 4, d₀ ≤ 5)` Algebra, Resultant Bounds, `det`, and `p0_zero`

Provides the shared algebraic foundation for all 120 Table 4 branches (`B6401Table4NonK` and
`B6401Table4K`), plus complete proofs for `T4ABranch.det` and `T4ABranch.p0Zero`:
1. `SparseRow` / `baseT4Rows` satisfaction bridge matching `B6402IntFarkas.checkT4Bucket_sound`
   and `B6402T4Rows.buildT4ARows` / `buildT4BRows` definitionally.
2. Exact char-2 polynomial helpers (`sqrtPoly`, `evenPart`, `oddPart`, `sum_ord_le_natDegree`).
3. Extraction of `P_j, C_j, B_j, g_j` (`j : Fin 3`) from `f_coord : KerDIdx wY W_F 1 → Fld`
   (`W_F < 6 * wY - 1`), exact degree bounds, and shifted `(A0_j, A1_j, B^{sh}_j)` local orders.
4. Universal formal `(5, 4)` Sylvester resultant theorems:
   - `f1_eval_P_ne_zero`,
   - `natDegree_resultant_5_4_le_sylvester` (`deg_X(Res_Y) ≤ 8 W_F - 20 wY + 4 + deg_X(g_4)`),
   - `pow_dvd_resultant_5_4_U0` (`1, 11, 29 + 18(k - 3)`) and `_U1` (`4, 16, 34 + 18(k - 3)`).
5. `T4ABranch.det` (`det M ≠ 0`) and `T4ABranch.p0Zero` (`det M = 0, p = 0`) satisfaction proofs.
6. `KerD45Syzygy` (`det M = 0, p ≠ 0, U(X, P) ≠ 0`): exact coprime `(p, c, b)`, reduced minors
   `M21, M20, M10`, `Res_Y = H1 * Q2(X^2)^2`, squarefree `D2 = gcd(p, q)` & `D1 = sqrtPoly D2`,
   `D1 ∣ g_j, R, U_P`, `D1^5 ∣ H1`, all shifted local order bounds, and all degree bounds.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402Table4Common

open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401Params hiding A D
open B6402HybridP64 (A)
open B6401KerDOrders B6402IntFarkas B6402T4Rows
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators
local notation (priority := high) "X" => Polynomial.X

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
namespace KerD45Data
variable (D : KerD45Data)

theorem table4_p0Zero_sat {c b : Fld[X]}
    (hne : c ≠ 0 ∨ b ≠ 0)
    (hcop : ∀ d : Fld[X], d ∣ c → d ∣ b → IsUnit d)
    (hsyz : ∀ j : Fin 3, c * D.Cj j + b * D.Bj j = 0)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    let rows := buildT4ARows .p0Zero cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    ∃ x : Fin (t4aNumVars .p0Zero) → ℚ,
      (∀ j, 0 ≤ x j) ∧
      x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
      x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
      x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨9, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
      (∀ r ∈ rows.1.toList, RowValid (t4aNumVars .p0Zero) r ∧ RowSatLe x r) ∧
      (∀ r ∈ rows.2.toList, RowValid (t4aNumVars .p0Zero) r ∧ RowSatEq x r) := by
  -- Extract K_j such that C_j = b * K_j and B_j = c * K_j!
  have hcb_cop : IsCoprime c b := isCoprime_of_forall_dvd_isUnit_poly hcop
  have hK : ∀ j : Fin 3, ∃ K : Fld[X], D.Cj j = b * K ∧ D.Bj j = c * K := by
    intro j
    have heq : c * D.Cj j = b * D.Bj j := by
      have h := hsyz j
      have hadd := congrArg (· + b * D.Bj j) h
      have hc := CharTwo.add_self_eq_zero (b * D.Bj j)
      linear_combination hadd - hc
    by_cases hb0 : b = 0
    · subst hb0
      have hc0 : c ≠ 0 := hne.resolve_right (by simp)
      rw [zero_mul] at heq
      have hC0 : D.Cj j = 0 := (mul_eq_zero.mp heq).resolve_left hc0
      -- c is a unit since gcd(c, 0) = 1!
      have hc_u : IsUnit c := hcop c dvd_rfl (dvd_zero c)
      obtain ⟨u, rfl⟩ := hc_u
      exact ⟨(u⁻¹ : Fld[X]ˣ) * D.Bj j, by rw [hC0, zero_mul], by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
    · have hb_dvd : b ∣ D.Cj j := hcb_cop.symm.dvd_of_dvd_mul_left ⟨D.Bj j, heq⟩
      rcases hb_dvd with ⟨K, hK⟩
      refine ⟨K, hK, ?_⟩
      apply mul_left_cancel₀ hb0
      rw [← heq, hK]; ring
  let Kj : Fin 3 → Fld[X] := fun j => Classical.choose (hK j)
  have hKj : ∀ j : Fin 3, D.Cj j = b * Kj j ∧ D.Bj j = c * Kj j := fun j => Classical.choose_spec (hK j)
  let R : Fld[X] := b.comp (X ^ 2) + X * c.comp (X ^ 2)
  have hR_ne : R ≠ 0 := by
    intro h0; rcases (even_odd_pair_eq_zero_iff b c).mp h0 with ⟨rfl, rfl⟩
    exact hne.elim (fun h => h rfl) (fun h => h rfl)
  have hgj_eq : ∀ j : Fin 3, D.gj j = R * (Kj j).comp (X ^ 2) := by
    intro j; unfold gj R
    rw [(hKj j).1, (hKj j).2, mul_comp, mul_comp]; ring
  have hR_deg : R.natDegree ≤ D.W_F + 1 - 5 * wY := by
    have hg2 : D.gj 2 = R * (Kj 2).comp (X ^ 2) := hgj_eq 2
    have hK2_ne : (Kj 2).comp (X ^ 2) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hg2; exact D.g2_ne_zero hg2
    have hle : R.natDegree ≤ (D.gj 2).natDegree := by
      rw [hg2, natDegree_mul hR_ne hK2_ne]; omega
    exact hle.trans (D.natDegree_gj_le 2)
  let S : Fld[X] := ∑ j : Fin 3, sqrtPoly (Kj j) * D.P ^ j.val
  have hRS_sq : R * D.f1.eval D.P = (R * S) ^ 2 := by
    have hf1_eq : D.f1.eval D.P = R * S ^ 2 := by
      have hev_sum : D.f1.eval D.P = ∑ j : Fin 3, (C (D.gj j) * X ^ (2 * j.val)).eval D.P := by
        rw [D.f1_eq_sum]; exact map_sum (Polynomial.evalRingHom D.P) _ _
      rw [hev_sum]
      have hS2 : S ^ 2 = ∑ j : Fin 3, (Kj j).comp (X ^ 2) * D.P ^ (2 * j.val) := by
        dsimp only [S]
        have h2p : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
        have hfr : ∀ (f : Fin 3 → Fld[X]), (∑ j : Fin 3, f j) ^ 2 = ∑ j : Fin 3, f j ^ 2 := fun f => by
          rw [Fin.sum_univ_three, Fin.sum_univ_three]
          calc (f 0 + f 1 + f 2) ^ 2
              = f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + 2 * (f 0 * f 1 + f 0 * f 2 + f 1 * f 2) := by ring
            _ = f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 := by rw [h2p]; ring
        rw [hfr]; apply Finset.sum_congr rfl; intro j _
        rw [mul_pow, sqrtPoly_sq, ← pow_mul, mul_comm j.val 2]
      rw [hS2, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [eval_mul, eval_C, eval_pow, eval_X, hgj_eq j]; ring
    rw [hf1_eq]; ring
  have hRS_ne : (R * S) ^ 2 ≠ 0 := by rw [← hRS_sq]; exact mul_ne_zero hR_ne D.f1_eval_P_ne_zero
  have hRS_deg : ((R * S) ^ 2).natDegree ≤ 2 * D.W_F - 6 * wY + 2 := by
    rw [← hRS_sq, natDegree_mul hR_ne D.f1_eval_P_ne_zero]
    have h1 := hR_deg; have h2 := D.natDegree_f1_eval_P_le; have h5 := D.hWF_lo
    omega
  have h2a_le : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 ≤ 2 * D.W_F - 6 * wY + 2 := by
    have hdvd_even : ∀ i ∈ D.Az, (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i) ∣ (R * S) ^ 2 := by
      intro i hi
      set x0 := BinaryIRSProfile.domain i
      have hd1 : (X - C x0) ^ (2 * D.k i - 1) ∣ (R * S) ^ 2 := by
        rw [← hRS_sq]; exact dvd_mul_of_dvd_right (D.pow_dvd_f1_eval_P i hi) R
      have hrm1 : 2 * D.k i - 1 ≤ ((R * S) ^ 2).rootMultiplicity x0 :=
        (le_rootMultiplicity_iff hRS_ne).mpr hd1
      have hne_RS : R * S ≠ 0 := fun h0 => hRS_ne (by simp [h0])
      have hrm_ev : ((R * S) ^ 2).rootMultiplicity x0 = 2 * (R * S).rootMultiplicity x0 := by
        rw [sq, rootMultiplicity_mul (mul_ne_zero hne_RS hne_RS)]; omega
      have hrm2 : 2 * D.k i ≤ ((R * S) ^ 2).rootMultiplicity x0 := by omega
      exact (le_rootMultiplicity_iff hRS_ne).mp hrm2
    have hsum : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 ≤ ∑ i ∈ D.Az, (2 * D.k i) := by
      have hrew : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 =
          ∑ i ∈ D.Az, ((if D.k i = 1 then 2 else 0) + (if D.k i = 2 then 4 else 0) + (if 3 ≤ D.k i then 6 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
        unfold a1 a2 a3; ring
      rw [hrew]; apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
    exact hsum.trans ((sum_ord_le_natDegree_of_dvd D.Az BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
      ((R * S) ^ 2) hRS_ne _ hdvd_even).trans hRS_deg)
  -- Assemble x : Fin 10 → ℚ and prove buildT4ARows .p0Zero satisfaction!
  let x := D.detCoordinates6402
  refine ⟨x, fun j => by dsimp only [x,detCoordinates6402,rawDetCoordinates]; split <;> positivity, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only [t4aNumVars]
  have hBV := baseT4Rows_valid (nv := 10) (ic := 9) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
  have hBS := D.baseT4Rows_sat (nv := 10) (ic := 9) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcLo hcHi hloG hhiG
  have hc_nn : (0 : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ) := by positivity
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hResB : D.n1 + 11 * D.n2 + 29 * D.n3 + 18 * D.nt ≤ 9 * D.W_F - 25 * wY + 5 :=
    D.resOrdU0_le_natDegree.trans D.natDegree_ResY_le
  constructor
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact ⟨hBV.1 r hr, hBS.1 r hr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        exact D.detResRow6402
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
        exact pZeroRow6402Numeric D.n0 D.n1 D.n2 D.n3 D.nt D.a0 D.a1 D.a2 D.a3 D.W_F D.hWF_lo h2a_le
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.append_nil] at hr
    exact ⟨hBV.2 r hr, hBS.2 r hr⟩

end KerD45Data

/-! ### Part 7: Exact `det M = 0, p ≠ 0, U(X, P) ≠ 0` Syzygy Package (`KerD45Syzygy`) -/

/-- Exact escape predicate: `U(X, P(X)) = p(X^2) P(X) + b(X^2) + X c(X^2) = 0` for a coprime
syzygy `(p, c, b)` of `M` with `p ≠ 0`. -/
def EscapeUZero (D : KerD45Data) : Prop :=
  ∃ p c b : Fld[X],
    p ≠ 0 ∧ (∀ d : Fld[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d) ∧
    (∀ j : Fin 3, p * D.Pj j + c * D.Cj j + b * D.Bj j = 0) ∧
    p.comp (X ^ 2) * D.P + b.comp (X ^ 2) + X * c.comp (X ^ 2) = 0

/-- Full algebraic package for `det M = 0, p ≠ 0, U(X, P) ≠ 0`, shared by `P0`, `b1c1`, and `K ≠ 0`! -/
structure KerD45Syzygy (D : KerD45Data) where
  p : Fld[X]
  c : Fld[X]
  b : Fld[X]
  hp : p ≠ 0
  hcop : ∀ d : Fld[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d
  hsyz : ∀ j : Fin 3, p * D.Pj j + c * D.Cj j + b * D.Bj j = 0
  hUP_ne : p.comp (X ^ 2) * D.P + b.comp (X ^ 2) + X * c.comp (X ^ 2) ≠ 0

namespace KerD45Syzygy

variable {D : KerD45Data} (S : KerD45Syzygy D)

noncomputable def R : Fld[X] := S.b.comp (X ^ 2) + X * S.c.comp (X ^ 2)
noncomputable def q : Fld[X] := S.b ^ 2 + X * S.c ^ 2
noncomputable def UP : Fld[X] := S.p.comp (X ^ 2) * D.P + S.R

lemma UP_eq : S.UP = S.p.comp (X ^ 2) * D.P + S.b.comp (X ^ 2) + X * S.c.comp (X ^ 2) := by
  unfold UP R; ring

lemma UP_ne_zero : S.UP ≠ 0 := by rw [S.UP_eq]; exact S.hUP_ne

lemma q_comp_X_sq : S.q.comp (X ^ 2) = S.R ^ 2 := by
  unfold q R
  have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
  rw [add_comp, pow_comp, mul_comp, X_comp, pow_comp]
  calc S.b.comp (X ^ 2) ^ 2 + X ^ 2 * S.c.comp (X ^ 2) ^ 2
      = S.b.comp (X ^ 2) ^ 2 + 2 * S.b.comp (X ^ 2) * (X * S.c.comp (X ^ 2)) + (X * S.c.comp (X ^ 2)) ^ 2 := by
        rw [h2]; ring
    _ = (S.b.comp (X ^ 2) + X * S.c.comp (X ^ 2)) ^ 2 := by ring

lemma q_eq_zero_iff : S.q = 0 ↔ S.R = 0 := by
  constructor
  · intro hq
    have h := S.q_comp_X_sq
    rw [hq, zero_comp] at h
    exact sq_eq_zero_iff.mp h.symm
  · intro hR
    have h := S.q_comp_X_sq
    rw [hR, zero_pow (by norm_num)] at h
    exact (comp_X_sq_eq_zero_iff S.q).mp h

lemma natDegree_q_eq_R : S.q.natDegree = S.R.natDegree := by
  have h := congrArg Polynomial.natDegree S.q_comp_X_sq
  rw [natDegree_comp_X_sq, natDegree_pow] at h
  omega

lemma natDegree_UP_le_max : S.UP.natDegree ≤ max (2 * S.p.natDegree + wY) S.R.natDegree := by
  unfold UP
  refine (natDegree_add_le _ _).trans (max_le_max ?_ le_rfl)
  refine natDegree_mul_le.trans ?_
  rw [natDegree_comp_X_sq]
  have := D.hPdeg
  omega

lemma natDegree_UP_le_of_le (h : S.R.natDegree ≤ 2 * S.p.natDegree + wY) :
    S.UP.natDegree ≤ 2 * S.p.natDegree + wY :=
  S.natDegree_UP_le_max.trans (max_le le_rfl h)

lemma natDegree_UP_eq_of_gt (h : 2 * S.p.natDegree + wY < S.R.natDegree) :
    S.UP.natDegree = S.R.natDegree := by
  unfold UP
  apply natDegree_add_eq_right_of_natDegree_lt
  refine lt_of_le_of_lt (natDegree_mul_le.trans ?_) h
  rw [natDegree_comp_X_sq]
  have := D.hPdeg
  omega

/-! #### Reduced minors `M21, M20, M10` and `Res_Y = H1 * Q2(X^2)^2` -/

lemma minorExists (a b : Fin 3) :
    ∃ M : Fld[X],
      S.p * M = D.Cj a * D.Bj b + D.Cj b * D.Bj a ∧
      S.c * M = D.Pj a * D.Bj b + D.Pj b * D.Bj a ∧
      S.b * M = D.Pj a * D.Cj b + D.Pj b * D.Cj a := by
  have hsyz_a := S.hsyz a
  have hsyz_b := S.hsyz b
  set N : Fld[X] := D.Cj a * D.Bj b + D.Cj b * D.Bj a
  have hpc : S.p * (D.Pj a * D.Bj b + D.Pj b * D.Bj a) = S.c * N := by
    have h1 := congrArg (· * D.Bj b) hsyz_a
    have h2 := congrArg (· * D.Bj a) hsyz_b
    have hadd := congrArg₂ (· + ·) h1 h2
    simp only [zero_mul, add_zero] at hadd
    have hz1 := CharTwo.add_self_eq_zero (S.b * D.Bj a * D.Bj b)
    have hz2 := CharTwo.add_self_eq_zero (S.c * N)
    dsimp [N] at hz2 ⊢
    have hadd' := congrArg (· + S.c * (D.Cj a * D.Bj b + D.Cj b * D.Bj a)) hadd
    rw [zero_add] at hadd'
    linear_combination hadd' - hz1 - hz2
  have hpb : S.p * (D.Pj a * D.Cj b + D.Pj b * D.Cj a) = S.b * N := by
    have h1 := congrArg (· * D.Cj b) hsyz_a
    have h2 := congrArg (· * D.Cj a) hsyz_b
    have hadd := congrArg₂ (· + ·) h1 h2
    simp only [zero_mul, add_zero] at hadd
    have hz1 := CharTwo.add_self_eq_zero (S.c * D.Cj a * D.Cj b)
    have hz2 := CharTwo.add_self_eq_zero (S.b * N)
    dsimp [N] at hz2 ⊢
    have hadd' := congrArg (· + S.b * (D.Cj a * D.Bj b + D.Cj b * D.Bj a)) hadd
    rw [zero_add] at hadd'
    linear_combination hadd' - hz1 - hz2
  -- Show S.p ∣ N using S.hcop!
  have hp_dvd : S.p ∣ N := dvd_of_syzygy_coprime_poly S.hp S.hcop hpc hpb
  rcases hp_dvd with ⟨M, hM⟩
  refine ⟨M, hM.symm, ?_, ?_⟩
  · apply mul_left_cancel₀ S.hp
    calc S.p * (S.c * M) = S.c * (S.p * M) := by ring
      _ = S.c * N := by rw [← hM]
      _ = S.p * (D.Pj a * D.Bj b + D.Pj b * D.Bj a) := hpc.symm
  · apply mul_left_cancel₀ S.hp
    calc S.p * (S.b * M) = S.b * (S.p * M) := by ring
      _ = S.b * N := by rw [← hM]
      _ = S.p * (D.Pj a * D.Cj b + D.Pj b * D.Cj a) := hpb.symm

noncomputable def M21 : Fld[X] := Classical.choose (S.minorExists 2 1)
noncomputable def M20 : Fld[X] := Classical.choose (S.minorExists 2 0)
noncomputable def M10 : Fld[X] := Classical.choose (S.minorExists 1 0)

lemma p_mul_M21 : S.p * S.M21 = D.Cj 2 * D.Bj 1 + D.Cj 1 * D.Bj 2 := (Classical.choose_spec (S.minorExists 2 1)).1
lemma c_mul_M21 : S.c * S.M21 = D.Pj 2 * D.Bj 1 + D.Pj 1 * D.Bj 2 := (Classical.choose_spec (S.minorExists 2 1)).2.1
lemma b_mul_M21 : S.b * S.M21 = D.Pj 2 * D.Cj 1 + D.Pj 1 * D.Cj 2 := (Classical.choose_spec (S.minorExists 2 1)).2.2

lemma p_mul_M20 : S.p * S.M20 = D.Cj 2 * D.Bj 0 + D.Cj 0 * D.Bj 2 := (Classical.choose_spec (S.minorExists 2 0)).1
lemma c_mul_M20 : S.c * S.M20 = D.Pj 2 * D.Bj 0 + D.Pj 0 * D.Bj 2 := (Classical.choose_spec (S.minorExists 2 0)).2.1
lemma b_mul_M20 : S.b * S.M20 = D.Pj 2 * D.Cj 0 + D.Pj 0 * D.Cj 2 := (Classical.choose_spec (S.minorExists 2 0)).2.2

lemma p_mul_M10 : S.p * S.M10 = D.Cj 1 * D.Bj 0 + D.Cj 0 * D.Bj 1 := (Classical.choose_spec (S.minorExists 1 0)).1
lemma c_mul_M10 : S.c * S.M10 = D.Pj 1 * D.Bj 0 + D.Pj 0 * D.Bj 1 := (Classical.choose_spec (S.minorExists 1 0)).2.1
lemma b_mul_M10 : S.b * S.M10 = D.Pj 1 * D.Cj 0 + D.Pj 0 * D.Cj 1 := (Classical.choose_spec (S.minorExists 1 0)).2.2

lemma two_mul_natDegree_p_mul_M21_le : 2 * (S.p * S.M21).natDegree ≤ 2 * D.W_F - 8 * wY + 1 := by
  rw [S.p_mul_M21]
  have hC2 := D.two_mul_natDegree_Cj_le 2; have hB1 := D.two_mul_natDegree_Bj_le 1
  have hC1 := D.two_mul_natDegree_Cj_le 1; have hB2 := D.two_mul_natDegree_Bj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have ht1 : 2 * (D.Cj 2 * D.Bj 1).natDegree ≤ 2 * D.W_F - 8 * wY + 1 := by
    have := natDegree_mul_le (p := D.Cj 2) (q := D.Bj 1); omega
  have ht2 : 2 * (D.Cj 1 * D.Bj 2).natDegree ≤ 2 * D.W_F - 8 * wY + 1 := by
    by_cases hB2z : D.Bj 2 = 0
    · simp [hB2z]
    · have h5le := D.five_wY_le_of_Bj2_ne_zero hB2z
      have := natDegree_mul_le (p := D.Cj 1) (q := D.Bj 2); omega
  have hadd := natDegree_add_le (D.Cj 2 * D.Bj 1) (D.Cj 1 * D.Bj 2)
  omega

lemma natDegree_p_add_M21_le (hM : S.M21 ≠ 0) : S.p.natDegree + S.M21.natDegree ≤ D.W_F - 4 * wY := by
  have h := S.two_mul_natDegree_p_mul_M21_le
  rw [natDegree_mul S.hp hM] at h; omega

lemma two_mul_natDegree_p_mul_M20_le : 2 * (S.p * S.M20).natDegree ≤ 2 * D.W_F - 6 * wY + 1 := by
  rw [S.p_mul_M20]
  have hC2 := D.two_mul_natDegree_Cj_le 2; have hB0 := D.two_mul_natDegree_Bj_le 0
  have hC0 := D.two_mul_natDegree_Cj_le 0; have hB2 := D.two_mul_natDegree_Bj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have ht1 : 2 * (D.Cj 2 * D.Bj 0).natDegree ≤ 2 * D.W_F - 6 * wY + 1 := by
    have := natDegree_mul_le (p := D.Cj 2) (q := D.Bj 0); omega
  have ht2 : 2 * (D.Cj 0 * D.Bj 2).natDegree ≤ 2 * D.W_F - 6 * wY + 1 := by
    by_cases hB2z : D.Bj 2 = 0
    · simp [hB2z]
    · have h5le := D.five_wY_le_of_Bj2_ne_zero hB2z
      have := natDegree_mul_le (p := D.Cj 0) (q := D.Bj 2); omega
  have hadd := natDegree_add_le (D.Cj 2 * D.Bj 0) (D.Cj 0 * D.Bj 2)
  omega

lemma natDegree_p_add_M20_le (hM : S.M20 ≠ 0) : S.p.natDegree + S.M20.natDegree ≤ D.W_F - 3 * wY := by
  have h := S.two_mul_natDegree_p_mul_M20_le
  rw [natDegree_mul S.hp hM] at h; omega

lemma two_mul_natDegree_p_mul_M20_le_with_g2 :
    2 * (S.p * S.M20).natDegree ≤ D.W_F - wY + (D.gj 2).natDegree := by
  rw [S.p_mul_M20]
  have hB0 := D.two_mul_natDegree_Bj_le 0; have hC0 := D.two_mul_natDegree_Cj_le 0
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have ht1 : 2 * (D.Cj 2 * D.Bj 0).natDegree ≤ D.W_F - wY + (D.gj 2).natDegree := by
    by_cases hC2 : D.Cj 2 = 0
    · simp [hC2]
    · have hle : 2 * (D.Cj 2).natDegree ≤ (D.gj 2).natDegree :=
        two_mul_natDegree_le_even_odd (D.Cj 2) (D.Bj 2) hC2
      have := natDegree_mul_le (p := D.Cj 2) (q := D.Bj 0); omega
  have ht2 : 2 * (D.Cj 0 * D.Bj 2).natDegree ≤ D.W_F - wY + (D.gj 2).natDegree := by
    by_cases hB2 : D.Bj 2 = 0
    · simp [hB2]
    · have hle : 2 * (D.Bj 2).natDegree + 1 ≤ (D.gj 2).natDegree :=
        two_mul_natDegree_add_one_le_even_odd (D.Cj 2) (D.Bj 2) hB2
      have := natDegree_mul_le (p := D.Cj 0) (q := D.Bj 2); omega
  have hadd := natDegree_add_le (D.Cj 2 * D.Bj 0) (D.Cj 0 * D.Bj 2)
  omega

lemma two_mul_natDegree_p_mul_M10_le : 2 * (S.p * S.M10).natDegree ≤ 2 * D.W_F - 4 * wY + 1 := by
  rw [S.p_mul_M10]
  have hC1 := D.two_mul_natDegree_Cj_le 1; have hB0 := D.two_mul_natDegree_Bj_le 0
  have hC0 := D.two_mul_natDegree_Cj_le 0; have hB1 := D.two_mul_natDegree_Bj_le 1
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have h1 : (D.Cj 1 * D.Bj 0 + D.Cj 0 * D.Bj 1).natDegree ≤
      max ((D.Cj 1).natDegree + (D.Bj 0).natDegree) ((D.Cj 0).natDegree + (D.Bj 1).natDegree) :=
    (natDegree_add_le _ _).trans (max_le_max natDegree_mul_le natDegree_mul_le)
  have hle : (D.Cj 1).natDegree + (D.Bj 0).natDegree ≤ D.W_F - 2 * wY ∧
      (D.Cj 0).natDegree + (D.Bj 1).natDegree ≤ D.W_F - 2 * wY := by omega
  omega

lemma natDegree_p_add_M10_le (hM : S.M10 ≠ 0) : S.p.natDegree + S.M10.natDegree ≤ D.W_F - 2 * wY := by
  have h := S.two_mul_natDegree_p_mul_M10_le
  rw [natDegree_mul S.hp hM] at h; omega

lemma natDegree_R_mul_M21_le : (S.R * S.M21.comp (X ^ 2)).natDegree ≤ 2 * D.W_F - 7 * wY + 1 := by
  have hrew : S.R * S.M21.comp (X ^ 2) =
      (S.b * S.M21).comp (X ^ 2) + X * (S.c * S.M21).comp (X ^ 2) := by
    unfold R; rw [mul_comp, mul_comp]; ring
  rw [hrew]
  have hP2 := D.two_mul_natDegree_Pj_le 2; have hP1 := D.two_mul_natDegree_Pj_le 1
  have hC1 := D.two_mul_natDegree_Cj_le 1; have hC2 := D.two_mul_natDegree_Cj_le 2
  have hB1 := D.two_mul_natDegree_Bj_le 1; have hB2 := D.two_mul_natDegree_Bj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hbM : 2 * (S.b * S.M21).natDegree ≤ 2 * D.W_F - 7 * wY + 1 := by
    rw [S.b_mul_M21]
    have h1 := (natDegree_add_le (D.Pj 2 * D.Cj 1) (D.Pj 1 * D.Cj 2)).trans (max_le_max natDegree_mul_le natDegree_mul_le)
    omega
  have hcM : 2 * (S.c * S.M21).natDegree ≤ 2 * D.W_F - 7 * wY := by
    rw [S.c_mul_M21]
    have ht1 : 2 * (D.Pj 2 * D.Bj 1).natDegree ≤ 2 * D.W_F - 7 * wY := by
      have := natDegree_mul_le (p := D.Pj 2) (q := D.Bj 1); omega
    have ht2 : 2 * (D.Pj 1 * D.Bj 2).natDegree ≤ 2 * D.W_F - 7 * wY := by
      by_cases hB2z : D.Bj 2 = 0
      · simp [hB2z]
      · have h5le := D.five_wY_le_of_Bj2_ne_zero hB2z
        have := natDegree_mul_le (p := D.Pj 1) (q := D.Bj 2); omega
    have hadd := natDegree_add_le (D.Pj 2 * D.Bj 1) (D.Pj 1 * D.Bj 2)
    omega
  have hle := natDegree_even_odd_le (S.b * S.M21) (S.c * S.M21)
  split_ifs at hle <;> omega

lemma natDegree_R_mul_M20_le : (S.R * S.M20.comp (X ^ 2)).natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
  have hrew : S.R * S.M20.comp (X ^ 2) =
      (S.b * S.M20).comp (X ^ 2) + X * (S.c * S.M20).comp (X ^ 2) := by
    unfold R; rw [mul_comp, mul_comp]; ring
  rw [hrew]
  have hP2 := D.two_mul_natDegree_Pj_le 2; have hP0 := D.two_mul_natDegree_Pj_le 0
  have hC0 := D.two_mul_natDegree_Cj_le 0; have hC2 := D.two_mul_natDegree_Cj_le 2
  have hB0 := D.two_mul_natDegree_Bj_le 0; have hB2 := D.two_mul_natDegree_Bj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hbM : 2 * (S.b * S.M20).natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
    rw [S.b_mul_M20]
    have h1 := (natDegree_add_le (D.Pj 2 * D.Cj 0) (D.Pj 0 * D.Cj 2)).trans (max_le_max natDegree_mul_le natDegree_mul_le)
    omega
  have hcM : 2 * (S.c * S.M20).natDegree ≤ 2 * D.W_F - 5 * wY := by
    rw [S.c_mul_M20]
    have ht1 : 2 * (D.Pj 2 * D.Bj 0).natDegree ≤ 2 * D.W_F - 5 * wY := by
      have := natDegree_mul_le (p := D.Pj 2) (q := D.Bj 0); omega
    have ht2 : 2 * (D.Pj 0 * D.Bj 2).natDegree ≤ 2 * D.W_F - 5 * wY := by
      by_cases hB2z : D.Bj 2 = 0
      · simp [hB2z]
      · have h5le := D.five_wY_le_of_Bj2_ne_zero hB2z
        have := natDegree_mul_le (p := D.Pj 0) (q := D.Bj 2); omega
    have hadd := natDegree_add_le (D.Pj 2 * D.Bj 0) (D.Pj 0 * D.Bj 2)
    omega
  have hle := natDegree_even_odd_le (S.b * S.M20) (S.c * S.M20)
  split_ifs at hle <;> omega

lemma natDegree_UP_mul_M20_le : (S.UP * S.M20.comp (X ^ 2)).natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
  have hrew : S.UP * S.M20.comp (X ^ 2) =
      (S.p * S.M20).comp (X ^ 2) * D.P + S.R * S.M20.comp (X ^ 2) := by
    unfold UP; rw [mul_comp]; ring
  rw [hrew]
  refine (natDegree_add_le _ _).trans (max_le ?_ S.natDegree_R_mul_M20_le)
  refine natDegree_mul_le.trans ?_
  rw [natDegree_comp_X_sq]
  have h1 := S.two_mul_natDegree_p_mul_M20_le
  have hP := D.hPdeg; have h5 := D.hWF_lo; have hw := D.hwY_pos
  omega

lemma natDegree_R_mul_M10_le : (S.R * S.M10.comp (X ^ 2)).natDegree ≤ 2 * D.W_F - 3 * wY + 1 := by
  have hrew : S.R * S.M10.comp (X ^ 2) =
      (S.b * S.M10).comp (X ^ 2) + X * (S.c * S.M10).comp (X ^ 2) := by
    unfold R; rw [mul_comp, mul_comp]; ring
  rw [hrew]
  have hP1 := D.two_mul_natDegree_Pj_le 1; have hP0 := D.two_mul_natDegree_Pj_le 0
  have hC0 := D.two_mul_natDegree_Cj_le 0; have hC1 := D.two_mul_natDegree_Cj_le 1
  have hB0 := D.two_mul_natDegree_Bj_le 0; have hB1 := D.two_mul_natDegree_Bj_le 1
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hbM : 2 * (S.b * S.M10).natDegree ≤ 2 * D.W_F - 3 * wY + 1 := by
    rw [S.b_mul_M10]
    have h1 := (natDegree_add_le (D.Pj 1 * D.Cj 0) (D.Pj 0 * D.Cj 1)).trans (max_le_max natDegree_mul_le natDegree_mul_le)
    omega
  have hcM : 2 * (S.c * S.M10).natDegree ≤ 2 * D.W_F - 3 * wY := by
    rw [S.c_mul_M10]
    have h1 := (natDegree_add_le (D.Pj 1 * D.Bj 0) (D.Pj 0 * D.Bj 1)).trans (max_le_max natDegree_mul_le natDegree_mul_le)
    omega
  have hle := natDegree_even_odd_le (S.b * S.M10) (S.c * S.M10)
  split_ifs at hle <;> omega

noncomputable def H1 : Fld[X] :=
  S.p.comp (X ^ 2) ^ 4 * D.gj 0 + S.p.comp (X ^ 2) ^ 2 * S.R ^ 2 * D.gj 1 + S.R ^ 4 * D.gj 2

noncomputable def Q2 : Fld[X] := S.M20 ^ 2 + S.M21 * S.M10

noncomputable def P0 : Fld[X] := S.p ^ 4 * S.M10 + S.q ^ 2 * S.M21

/-- Exact char-2 factorization `Res_Y^{(5, 4)} = H_1(X) * Q_2(X^2)^2`! -/
theorem ResY_eq_H1_mul_Q2_sq : D.ResY = S.H1 * (S.Q2.comp (X ^ 2)) ^ 2 := by
  have hf0_eq : D.f0 =
      (C ((D.Pj 0).comp (X ^ 2)) + C ((D.Pj 1).comp (X ^ 2)) * X + C ((D.Pj 2).comp (X ^ 2)) * X ^ 2).comp (X ^ 2) +
      X * (C ((D.Bj 0).comp (X ^ 2)) + C ((D.Bj 1).comp (X ^ 2)) * X + C ((D.Bj 2).comp (X ^ 2)) * X ^ 2).comp (X ^ 2) := by
    rw [D.f0_eq_sum, Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one, zero_add, pow_one,
      add_comp, mul_comp, C_comp, X_comp, pow_comp]
    ring
  have hf1_eq : D.f1 = (C (D.gj 0) + C (D.gj 1) * X + C (D.gj 2) * X ^ 2).comp (X ^ 2) := by
    rw [D.f1_eq_sum, Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one,
      add_comp, mul_comp, C_comp, X_comp, pow_comp]
    ring
  haveI : CharP (RatFunc Fld) 2 :=
    charP_of_injective_algebraMap (IsFractionRing.injective Fld[X] (RatFunc Fld)) 2
  have hid := syzygy_res_factor_of_inj
    (algebraMap Fld[X] (RatFunc Fld)) (IsFractionRing.injective Fld[X] (RatFunc Fld))
    (D.Pj 0) (D.Pj 1) (D.Pj 2) (D.Cj 0) (D.Cj 1) (D.Cj 2) (D.Bj 0) (D.Bj 1) (D.Bj 2)
    S.p S.c S.b S.M21 S.M20 S.M10 S.hp D.g2_ne_zero
    (S.hsyz 0) (S.hsyz 1) (S.hsyz 2) S.p_mul_M21 S.p_mul_M20 S.p_mul_M10
  unfold KerD45Data.ResY H1 Q2 R
  rw [hf0_eq, hf1_eq]
  exact hid

lemma H1_ne_zero : S.H1 ≠ 0 := by
  intro h0; apply D.ResY_ne_zero; rw [S.ResY_eq_H1_mul_Q2_sq, h0, zero_mul]

lemma Q2_ne_zero : S.Q2 ≠ 0 := by
  intro h0; apply D.ResY_ne_zero; rw [S.ResY_eq_H1_mul_Q2_sq, h0, zero_comp, zero_pow (by norm_num), mul_zero]

lemma natDegree_H1_le_of_le (h : S.R.natDegree ≤ 2 * S.p.natDegree + wY) :
    S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 := by
  unfold H1
  have hg0 := D.natDegree_gj_le 0; have hg1 := D.natDegree_gj_le 1; have hg2 := D.natDegree_gj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hp_sq : (S.p.comp (X ^ 2)).natDegree = 2 * S.p.natDegree := natDegree_comp_X_sq S.p
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) hg0) |>.trans (by omega)
  · refine natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) natDegree_pow_le)) hg1) |>.trans (by omega)
  · refine natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le hg2) |>.trans (by omega)

lemma natDegree_H1_le_of_gt (h : 2 * S.p.natDegree + wY < S.R.natDegree) :
    S.H1.natDegree ≤ 4 * S.R.natDegree + D.W_F - 5 * wY + 1 := by
  unfold H1
  have hg0 := D.natDegree_gj_le 0; have hg1 := D.natDegree_gj_le 1; have hg2 := D.natDegree_gj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hp_sq : (S.p.comp (X ^ 2)).natDegree = 2 * S.p.natDegree := natDegree_comp_X_sq S.p
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) hg0) |>.trans (by omega)
  · refine natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) natDegree_pow_le)) hg1) |>.trans (by omega)
  · refine natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le hg2) |>.trans (by omega)

lemma two_mul_natDegree_p_add_Q2_le : 2 * S.p.natDegree + S.Q2.natDegree ≤ 2 * D.W_F - 6 * wY := by
  have heq : S.p ^ 2 * S.Q2 = (S.p * S.M20) ^ 2 + (S.p * S.M21) * (S.p * S.M10) := by unfold Q2; ring
  have hdeg : (S.p ^ 2 * S.Q2).natDegree = 2 * S.p.natDegree + S.Q2.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 S.hp) S.Q2_ne_zero, natDegree_pow]
  rw [← hdeg, heq]
  have h20 := S.two_mul_natDegree_p_mul_M20_le
  have h21 := S.two_mul_natDegree_p_mul_M21_le
  have h10 := S.two_mul_natDegree_p_mul_M10_le
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  refine (natDegree_add_le _ _).trans (max_le (natDegree_pow_le.trans (by omega)) (natDegree_mul_le.trans (by omega)))

/-! #### Squarefree `D2 = gcd(p, q)` and `D1 = sqrtPoly D2` -/

noncomputable def D2 : Fld[X] := EuclideanDomain.gcd S.p S.q
noncomputable def D1 : Fld[X] := sqrtPoly S.D2

lemma D2_dvd_p : S.D2 ∣ S.p := EuclideanDomain.gcd_dvd_left S.p S.q
lemma D2_dvd_q : S.D2 ∣ S.q := EuclideanDomain.gcd_dvd_right S.p S.q

lemma D2_ne_zero : S.D2 ≠ 0 := fun h0 => S.hp (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
lemma D1_ne_zero : S.D1 ≠ 0 := mt (sqrtPoly_eq_zero_iff S.D2).mp S.D2_ne_zero
lemma D1_sq : S.D1 ^ 2 = S.D2.comp (X ^ 2) := sqrtPoly_sq S.D2
lemma D1_natDegree : S.D1.natDegree = S.D2.natDegree := natDegree_sqrtPoly S.D2
lemma D2_natDegree_le_p : S.D2.natDegree ≤ S.p.natDegree := natDegree_le_of_dvd S.D2_dvd_p S.hp

lemma q_derivative_eq : S.q.derivative = S.c ^ 2 := by
  unfold q
  have hsq : ∀ f : Fld[X], (f ^ 2).derivative = 0 := fun f => (derivative_eq_zero_iff_sq (f ^ 2)).mpr ⟨f, rfl⟩
  rw [derivative_add, hsq S.b, zero_add, derivative_mul, derivative_X, one_mul, hsq S.c, mul_zero, add_zero]

lemma D2_coprime_c : IsCoprime S.D2 S.c := by
  refine isCoprime_of_forall_dvd_isUnit_poly fun d hd_D2 hd_c => ?_
  by_contra hnu
  have hd0 : d ≠ 0 := fun h0 => S.D2_ne_zero (zero_dvd_iff.mp (h0 ▸ hd_D2))
  obtain ⟨π, hπ_irr, hπ_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hd0
  have hπ_p : π ∣ S.p := hπ_dvd.trans (hd_D2.trans S.D2_dvd_p)
  have hπ_c : π ∣ S.c := hπ_dvd.trans hd_c
  have hπ_q : π ∣ S.q := hπ_dvd.trans (hd_D2.trans S.D2_dvd_q)
  have hπ_b2 : π ∣ S.b ^ 2 := by
    have hb2 : S.b ^ 2 = S.q + X * S.c ^ 2 := by
      unfold q; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hb2]
    exact dvd_add hπ_q (dvd_mul_of_dvd_right (dvd_pow hπ_c (by norm_num)) X)
  have hπ_b : π ∣ S.b := hπ_irr.prime.dvd_of_dvd_pow hπ_b2
  exact hπ_irr.not_isUnit (S.hcop π hπ_p hπ_c hπ_b)

lemma D2_coprime_q_derivative : IsCoprime S.D2 S.q.derivative := by
  rw [S.q_derivative_eq]; exact S.D2_coprime_c.pow_right

lemma D2_squarefree : Squarefree S.D2 := by
  intro r hr
  have hr2_q : r ^ 2 ∣ S.q := by rw [sq]; exact hr.trans S.D2_dvd_q
  rcases hr2_q with ⟨w, hw⟩
  have hr_q' : r ∣ S.q.derivative := by
    have hsq : (r ^ 2).derivative = 0 := (derivative_eq_zero_iff_sq (r ^ 2)).mpr ⟨r, rfl⟩
    rw [hw, derivative_mul, hsq, zero_mul, zero_add]
    exact dvd_mul_of_dvd_left ⟨r, sq r⟩ w.derivative
  have hr_D2 : r ∣ S.D2 := (dvd_mul_right r r).trans hr
  exact S.D2_coprime_q_derivative.isUnit_of_dvd' hr_D2 hr_q'

end KerD45Syzygy
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
