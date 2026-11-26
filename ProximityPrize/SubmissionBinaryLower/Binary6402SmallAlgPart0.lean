import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT3
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401KerD2
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402IntSmallCerts
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT1
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT2
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT3
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

/-!
# Tables 1, 2, 3, and 3-2B: Contiguous Certificate Coverage, Char-2 Resultant & UFD Algebra

Provides:
1. `decide`-verified contiguous coverage theorems (`exists_t1Cert`, `exists_t2Cert`, `exists_t3Cert`)
   over `B6402CertsT1`, `B6402CertsT2`, and `B6402CertsT3` (`O(n)` synchronized cover check for T3!).
2. Multiplicativity of `wdegBi` (`wdegBi_mul`) and exact 2D multiplicity `biMult` (`biMult_mul`,
   `biMult_even_of_in_F_X2_Y2`).
3. Resultant shift/cancellation identity (`resultant_add_mul_right_deg`) and char-2 `ker(D)`
   resultant divisibility theorems:
   - `kerD1_resY_ord` (Table 1 `v_ker` + `v_pln`),
   - `kerD2_resY_f0_g_ord` (Table 3 general `v_ker` + `v_pln` and 2B `q, g_1`),
   - `kerD2_resY_f0_g_2A_ord` (Table 3 Subcase 2A `g = q(X) * g_e(X^2, Y^2)`).
4. Char-2 `ker(D)` UFD decomposition for `deg_R = 2` (`kerD2_gcd_decomp` and `kerD2_2A_2B_dichotomy`).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402SmallAlg

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial  B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6402IntFarkas B6402IntSmallCerts
open B6402CertsT1 B6402CertsT2 B6402CertsT3
open scoped BigOperators
local notation (priority := high) "X" => Polynomial.X

/-! ### Part 1: Generic Contiguous Interval Coverage & `decide`-Verified Lookups -/

def checkCoverGo {α : Type*} (lo hi : α → ℕ × ℕ) (endN endD : ℕ) : ℕ → ℕ → List α → Bool
  | curN, curD, [] => decide (endN * curD ≤ curN * endD)
  | curN, curD, c :: cs =>
      (lo c).2 != 0 && (hi c).2 != 0 &&
      decide ((lo c).1 * curD ≤ curN * (lo c).2) &&
      checkCoverGo lo hi endN endD (hi c).1 (hi c).2 cs

def checkCover {α : Type*} (lo hi : α → ℕ × ℕ) (startN startD endN endD : ℕ) : List α → Bool
  | [] => false
  | c :: cs =>
      (lo c).2 != 0 && (hi c).2 != 0 &&
      decide ((lo c).1 * startD ≤ startN * (lo c).2) &&
      checkCoverGo lo hi endN endD (hi c).1 (hi c).2 cs

lemma rat_le_of_cross {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    (a : ℚ) / (b : ℚ) ≤ (c : ℚ) / (d : ℚ) := by
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  rw [div_le_div_iff₀ hbQ hdQ]
  exact_mod_cast h

lemma checkCoverGo_mem {α : Type*} (lo hi : α → ℕ × ℕ) (endN endD : ℕ) (hendD : 0 < endD) :
    ∀ (L : List α) (curN curD : ℕ) (_ : 0 < curD),
      checkCoverGo lo hi endN endD curN curD L = true →
      ∀ x : ℚ, (curN : ℚ) / (curD : ℚ) < x → x ≤ (endN : ℚ) / (endD : ℚ) →
      ∃ c ∈ L, ((lo c).1 : ℚ) / ((lo c).2 : ℚ) ≤ x ∧ x ≤ ((hi c).1 : ℚ) / ((hi c).2 : ℚ) := by
  intro L
  induction L with
  | nil =>
      intro curN curD hcurD hchk x hlt hle
      have h1 : endN * curD ≤ curN * endD := decide_eq_true_eq.mp hchk
      have h2 := rat_le_of_cross hendD hcurD h1
      linarith
  | cons c cs ih =>
      intro curN curD hcurD hchk x hlt hle
      unfold checkCoverGo at hchk
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hchk
      rcases hchk with ⟨⟨⟨hloD0, hhiD0⟩, hcross⟩, hrest⟩
      have hloD : 0 < (lo c).2 := Nat.pos_of_ne_zero hloD0
      have hhiD : 0 < (hi c).2 := Nat.pos_of_ne_zero hhiD0
      have hlo_le : ((lo c).1 : ℚ) / ((lo c).2 : ℚ) ≤ x :=
        (rat_le_of_cross hloD hcurD hcross).trans hlt.le
      rcases le_or_gt x (((hi c).1 : ℚ) / ((hi c).2 : ℚ)) with hx_le | hx_gt
      · exact ⟨c, by simp, hlo_le, hx_le⟩
      · obtain ⟨c', hc', h1, h2⟩ := ih (hi c).1 (hi c).2 hhiD hrest x hx_gt hle
        exact ⟨c', by simp [hc'], h1, h2⟩

theorem exists_mem_of_checkCover {α : Type*} (lo hi : α → ℕ × ℕ)
    (startN startD endN endD : ℕ) (hstartD : 0 < startD) (hendD : 0 < endD)
    (L : List α) (hchk : checkCover lo hi startN startD endN endD L = true)
    (x : ℚ) (hlo : (startN : ℚ) / (startD : ℚ) ≤ x) (hhi : x ≤ (endN : ℚ) / (endD : ℚ)) :
    ∃ c ∈ L, ((lo c).1 : ℚ) / ((lo c).2 : ℚ) ≤ x ∧ x ≤ ((hi c).1 : ℚ) / ((hi c).2 : ℚ) := by
  cases L with
  | nil => simp [checkCover] at hchk
  | cons c cs =>
      unfold checkCover at hchk
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hchk
      rcases hchk with ⟨⟨⟨hloD0, hhiD0⟩, hcross⟩, hrest⟩
      have hloD : 0 < (lo c).2 := Nat.pos_of_ne_zero hloD0
      have hhiD : 0 < (hi c).2 := Nat.pos_of_ne_zero hhiD0
      have hlo_le : ((lo c).1 : ℚ) / ((lo c).2 : ℚ) ≤ x :=
        (rat_le_of_cross hloD hstartD hcross).trans hlo
      rcases le_or_gt x (((hi c).1 : ℚ) / ((hi c).2 : ℚ)) with hx_le | hx_gt
      · exact ⟨c, by simp, hlo_le, hx_le⟩
      · obtain ⟨c', hc', h1, h2⟩ := checkCoverGo_mem lo hi endN endD hendD cs (hi c).1 (hi c).2 hhiD hrest x hx_gt hhi
        exact ⟨c', by simp [hc'], h1, h2⟩

/-- Table 1 expected `(d1, d0Eff)` list. -/
def t1ExpectedKeys : List (ℕ × ℕ) :=
  ((List.range 13).map (2 * ·)).flatMap fun d1 =>
    ((d1 + 1) :: ((List.range 13).map (2 * ·)).filter (d1 + 1 < ·)).map fun d0Eff => (d1, d0Eff)

def t1StartPair (d1 d0Eff : ℕ) : ℕ × ℕ :=
  if d1 == 4 && d0Eff == 5 then (28, 5)
  else if d0Eff == d1 + 1 then (d0Eff * wY - 1, wY)
  else (d0Eff, 1)

def checkT1AllCovers : Bool :=
  t1ExpectedKeys.all fun (d1, d0Eff) =>
    let (sN, sD) := t1StartPair d1 d0Eff
    checkCover (fun c => (c.cLoNum, c.cLoDen)) (fun c => (c.cHiNum, c.cHiDen)) sN sD 51 2
      (certsT1.filter fun c => c.d1 == d1 && c.d0Eff == d0Eff)

theorem t1AllCovers_ok : checkT1AllCovers = true := by decide

theorem exists_t1Cert (d1 d0Eff : ℕ) (hd1_le : d1 ≤ 24) (hd1_even : d1 % 2 = 0)
    (hd0 : d0Eff = d1 + 1 ∨ (d1 + 1 < d0Eff ∧ d0Eff ≤ 24 ∧ d0Eff % 2 = 0))
    (cVal : ℚ)
    (hlo : ((t1StartPair d1 d0Eff).1 : ℚ) / ((t1StartPair d1 d0Eff).2 : ℚ) ≤ cVal)
    (hhi : cVal ≤ 51 / 2) :
    ∃ c ∈ certsT1, c.d1 = d1 ∧ c.d0Eff = d0Eff ∧ checkT1Entry c = true ∧
      (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal ∧ cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ) := by
  have hmem_key : (d1, d0Eff) ∈ t1ExpectedKeys := by
    unfold t1ExpectedKeys
    rw [List.mem_flatMap]
    refine ⟨d1, List.mem_map.mpr ⟨d1 / 2, List.mem_range.mpr (by omega), by omega⟩, ?_⟩
    rw [List.mem_map]
    rcases hd0 with rfl | ⟨hgt, hle, hev⟩
    · exact ⟨d1 + 1, by simp, rfl⟩
    · refine ⟨d0Eff, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨?_, by simp; omega⟩), rfl⟩
      exact List.mem_map.mpr ⟨d0Eff / 2, List.mem_range.mpr (by omega), by omega⟩
  have hcov := List.all_eq_true.mp t1AllCovers_ok (d1, d0Eff) hmem_key
  have hsD : 0 < (t1StartPair d1 d0Eff).2 := by
    unfold t1StartPair; split_ifs <;> norm_num [wY, D]
  obtain ⟨c, hc_filt, hclo, hchi⟩ := exists_mem_of_checkCover
    (fun c : T1Cert => (c.cLoNum, c.cLoDen)) (fun c : T1Cert => (c.cHiNum, c.cHiDen))
    (t1StartPair d1 d0Eff).1 (t1StartPair d1 d0Eff).2 51 2 hsD (by norm_num) _ hcov cVal hlo hhi
  have ⟨hc_mem, hc_eq⟩ := List.mem_filter.mp hc_filt
  simp only [Bool.and_eq_true, beq_iff_eq] at hc_eq
  exact ⟨c, hc_mem, hc_eq.1, hc_eq.2, List.all_eq_true.mp certsT1_ok c hc_mem, hclo, hchi⟩

/-- Table 2 expected `(d1, d2)` list. -/
def t2ExpectedKeys : List (ℕ × ℕ) :=
  ((List.range 12).map (2 * ·)).flatMap fun d2 =>
    ((List.range 25).filter fun d1 => d1 ≤ d2 + 1 || d1 % 2 == 0).map fun d1 => (d1, d2)

def checkT2AllCovers : Bool :=
  t2ExpectedKeys.all fun (d1, d2) =>
    checkCover (fun c => (c.cLoNum, c.cLoDen)) (fun c => (c.cHiNum, c.cHiDen))
      (max (d2 + 2) (d1 + 1) * wY - 2) wY 51 2
      (certsT2.filter fun c => c.d1 == d1 && c.d2 == d2)

theorem t2AllCovers_ok : checkT2AllCovers = true := by decide

theorem exists_t2Cert (d1 d2 : ℕ) (hd2_le : d2 ≤ 22) (hd2_even : d2 % 2 = 0)
    (hd1_le : d1 ≤ 24) (hd1_par : d1 ≤ d2 + 1 ∨ d1 % 2 = 0)
    (cVal : ℚ) (hlo : ((max (d2 + 2) (d1 + 1) * wY - 2 : ℕ) : ℚ) / (wY : ℚ) ≤ cVal) (hhi : cVal ≤ 51 / 2) :
    ∃ c ∈ certsT2, c.d1 = d1 ∧ c.d2 = d2 ∧ checkT2Entry c = true ∧
      (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal ∧ cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ) := by
  have hmem_key : (d1, d2) ∈ t2ExpectedKeys := by
    unfold t2ExpectedKeys
    rw [List.mem_flatMap]
    refine ⟨d2, List.mem_map.mpr ⟨d2 / 2, List.mem_range.mpr (by omega), by omega⟩, ?_⟩
    rw [List.mem_map]
    refine ⟨d1, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, rfl⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]; exact hd1_par
  have hcov := List.all_eq_true.mp t2AllCovers_ok (d1, d2) hmem_key
  obtain ⟨c, hc_filt, hclo, hchi⟩ := exists_mem_of_checkCover
    (fun c : T2Cert => (c.cLoNum, c.cLoDen)) (fun c : T2Cert => (c.cHiNum, c.cHiDen))
    (max (d2 + 2) (d1 + 1) * wY - 2) wY 51 2 (by norm_num [wY, D]) (by norm_num) _ hcov cVal hlo hhi
  have ⟨hc_mem, hc_eq⟩ := List.mem_filter.mp hc_filt
  simp only [Bool.and_eq_true, beq_iff_eq] at hc_eq
  exact ⟨c, hc_mem, hc_eq.1, hc_eq.2, List.all_eq_true.mp certsT2_ok c hc_mem, hclo, hchi⟩

/-- Linear-time `O(1755)` synchronized cover checker for ALL 858 Table 3 `(d2, dg, d1)` triples! -/
def splitLeading {α : Type*} (p : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | x :: xs =>
      if p x then
        let pr := splitLeading p xs
        (x :: pr.1, pr.2)
      else ([], x :: xs)

lemma splitLeading_spec {α : Type*} (p : α → Bool) (L : List α) :
    (∀ x ∈ (splitLeading p L).1, x ∈ L ∧ p x = true) ∧
    (∀ x ∈ (splitLeading p L).2, x ∈ L) := by
  induction L with
  | nil => simp [splitLeading]
  | cons a t ih =>
      unfold splitLeading
      by_cases hp : p a = true
      · rw [if_pos hp]
        refine ⟨fun x hx => ?_, fun x hx => List.mem_cons_of_mem a (ih.2 x hx)⟩
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact ⟨List.mem_cons_self, hp⟩
        · exact ⟨List.mem_cons_of_mem a (ih.1 x hxt).1, (ih.1 x hxt).2⟩
      · rw [if_neg hp]
        exact ⟨fun _ hx => (by cases hx), fun x hx => hx⟩

def t3ExpectedTriples : List (ℕ × ℕ × ℕ) :=
  ((List.range 11).map fun i => 2 * (i + 1)).flatMap fun d2 =>
    (((List.range 11).map fun j => 2 * (j + 1)).filter (· ≤ d2)).flatMap fun dg =>
      ((List.range 25).filter fun d1 => dg ≤ d1 && (d1 ≤ d2 + 1 || d1 % 2 == 0)).map fun d1 => (d2, dg, d1)

def t3ExpectedDStars (m0 : ℕ) : List ℕ :=
  m0 :: ((List.range 13).map (2 * ·)).filter (m0 < ·)

def checkT3Run (d2 dg d1 : ℕ) (run : List T3Cert) : Bool :=
  let m0 := max (d2 + 2) (d1 + 1)
  let noDs := run.filter fun c => !c.hasDStar && c.mode == 0
  if checkCover (fun c => (c.cLoNum, c.cLoDen)) (fun c => (c.cHiNum, c.cHiDen)) (m0 * wY - 2) wY 51 2 noDs then true
  else
    (t3ExpectedDStars m0).all fun ds =>
      if d2 == 8 && dg == 6 && d1 == 10 && ds == 11 then
        let run2A := run.filter fun c => c.hasDStar && c.dStar == 11 && (c.mode == 3 || c.mode == 0)
        let runStd := run.filter fun c => c.hasDStar && c.dStar == 11 && c.mode == 0
        let run2B : List (Sum T3_2BCert T3Cert) := certsT3_2B.map Sum.inl ++ runStd.map Sum.inr
        let loS : Sum T3_2BCert T3Cert → ℕ × ℕ := Sum.elim (fun b => (b.cLoNum, b.cLoDen)) (fun c => (c.cLoNum, c.cLoDen))
        let hiS : Sum T3_2BCert T3Cert → ℕ × ℕ := Sum.elim (fun b => (b.cHiNum, b.cHiDen)) (fun c => (c.cHiNum, c.cHiDen))
        checkCover (fun c => (c.cLoNum, c.cLoDen)) (fun c => (c.cHiNum, c.cHiDen)) (11 * wY - 2) wY 51 2 run2A &&
        checkCover loS hiS (11 * wY - 2) wY 51 2 run2B
      else
        let runDs := run.filter fun c =>
          c.hasDStar && c.dStar == ds &&
          (c.mode == 0 || c.mode == 1 || (d2 == 8 && dg == 8 && d1 == 10 && ds == 11 && c.mode == 3))
        checkCover (fun c => (c.cLoNum, c.cLoDen)) (fun c => (c.cHiNum, c.cHiDen)) (ds * wY - 2) wY 51 2 runDs

def checkT3Sync : List (ℕ × ℕ × ℕ) → List T3Cert → Bool
  | [], _ => true
  | (d2, dg, d1) :: ts, rem =>
      let pr := splitLeading (fun c => c.d2 == d2 && c.dg == dg && c.d1 == d1) rem
      checkT3Run d2 dg d1 pr.1 && checkT3Sync ts pr.2

theorem t3Sync_ok : checkT3Sync t3ExpectedTriples certsT3All = true := by decide

lemma checkT3Sync_mem : ∀ (ts : List (ℕ × ℕ × ℕ)) (rem : List T3Cert),
    checkT3Sync ts rem = true →
    ∀ t ∈ ts, ∃ run : List T3Cert,
      (∀ c ∈ run, c ∈ rem ∧ c.d2 = t.1 ∧ c.dg = t.2.1 ∧ c.d1 = t.2.2) ∧
      checkT3Run t.1 t.2.1 t.2.2 run = true := by
  intro ts
  induction ts with
  | nil => intro _ _ _ ht; cases ht
  | cons a as ih =>
      intro rem hchk t ht
      rcases a with ⟨d2, dg, d1⟩
      unfold checkT3Sync at hchk
      simp only [Bool.and_eq_true] at hchk
      have hsp := splitLeading_spec (fun c : T3Cert => c.d2 == d2 && c.dg == dg && c.d1 == d1) rem
      rcases List.mem_cons.mp ht with rfl | htas
      · refine ⟨(splitLeading (fun c => c.d2 == d2 && c.dg == dg && c.d1 == d1) rem).1, ?_, hchk.1⟩
        intro c hc
        have ⟨hmem, hpred⟩ := hsp.1 c hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
        exact ⟨hmem, hpred.1.1, hpred.1.2, hpred.2⟩
      · obtain ⟨run, hrun_m, hrun_ok⟩ := ih _ hchk.2 t htas
        exact ⟨run, fun c hc => ⟨hsp.2 c (hrun_m c hc).1, (hrun_m c hc).2⟩, hrun_ok⟩

/-- **Exhaustive Table 3 Certificate Lookup Theorem:**
For EVERY valid `(d2, dg, d1, dStar)` and EVERY `cVal ∈ [dStar - 2/wY, 51/2]`:
- Either there exists `c ∈ certsT3All` with `checkT3Entry c = true` covering `cVal` with
  `(c.hasDStar = false ∧ c.mode = 0) ∨ (c.hasDStar = true ∧ c.dStar = dStar ∧ (c.mode = 0 ∨ c.mode = 1 ∨ (d2 = 8 ∧ dg = 8 ∧ d1 = 10 ∧ dStar = 11 ∧ c.mode = 3)))`,
- Or `(d2, dg, d1, dStar) = (8, 6, 10, 11)` AND BOTH:
  - (2A cover) `∃ c ∈ certsT3All` covering `cVal` with `c.hasDStar = true ∧ c.dStar = 11 ∧ (c.mode = 3 ∨ c.mode = 0)`,
  - (2B cover) `(∃ b ∈ certsT3_2B, checkT3_2BEntry b = true ∧ b covers cVal) ∨ (∃ c ∈ certsT3All, c.hasDStar = true ∧ c.dStar = 11 ∧ c.mode = 0 ∧ c covers cVal)`! -/
theorem exists_t3Cert (d2 dg d1 dStar : ℕ)
    (hd2_lo : 2 ≤ d2) (hd2_hi : d2 ≤ 22) (hd2_ev : d2 % 2 = 0)
    (hdg_lo : 2 ≤ dg) (hdg_hi : dg ≤ d2) (hdg_ev : dg % 2 = 0)
    (hd1_lo : dg ≤ d1) (hd1_hi : d1 ≤ 24) (hd1_par : d1 ≤ d2 + 1 ∨ d1 % 2 = 0)
    (hdStar : dStar = max (d2 + 2) (d1 + 1) ∨ (max (d2 + 2) (d1 + 1) < dStar ∧ dStar ≤ 24 ∧ dStar % 2 = 0))
    (cVal : ℚ)
    (hlo : ((dStar * wY - 2 : ℕ) : ℚ) / (wY : ℚ) ≤ cVal) (hhi : cVal ≤ 51 / 2) :
    (∃ c ∈ certsT3All, c.d2 = d2 ∧ c.dg = dg ∧ c.d1 = d1 ∧ checkT3Entry c = true ∧
      ((c.hasDStar = false ∧ c.mode = 0) ∨
       (c.hasDStar = true ∧ c.dStar = dStar ∧
        (c.mode = 0 ∨ c.mode = 1 ∨ (d2 = 8 ∧ dg = 8 ∧ d1 = 10 ∧ dStar = 11 ∧ c.mode = 3)))) ∧
      (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal ∧ cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ)) ∨
    (d2 = 8 ∧ dg = 6 ∧ d1 = 10 ∧ dStar = 11 ∧
      (∃ c ∈ certsT3All, c.d2 = 8 ∧ c.dg = 6 ∧ c.d1 = 10 ∧ checkT3Entry c = true ∧
        c.hasDStar = true ∧ c.dStar = 11 ∧ (c.mode = 3 ∨ c.mode = 0) ∧
        (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal ∧ cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ)) ∧
      ((∃ b ∈ certsT3_2B, checkT3_2BEntry b = true ∧
          (b.cLoNum : ℚ) / (b.cLoDen : ℚ) ≤ cVal ∧ cVal ≤ (b.cHiNum : ℚ) / (b.cHiDen : ℚ)) ∨
       (∃ c ∈ certsT3All, c.d2 = 8 ∧ c.dg = 6 ∧ c.d1 = 10 ∧ checkT3Entry c = true ∧
          c.hasDStar = true ∧ c.dStar = 11 ∧ c.mode = 0 ∧
          (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal ∧ cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ)))) := by
  have hmem_t : (d2, dg, d1) ∈ t3ExpectedTriples := by
    unfold t3ExpectedTriples
    rw [List.mem_flatMap]
    refine ⟨d2, List.mem_map.mpr ⟨d2 / 2 - 1, List.mem_range.mpr (by omega), by omega⟩, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨dg, List.mem_filter.mpr ⟨List.mem_map.mpr ⟨dg / 2 - 1, List.mem_range.mpr (by omega), by omega⟩,
      by simp; omega⟩, ?_⟩
    rw [List.mem_map]
    refine ⟨d1, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, rfl⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hd1_lo, hd1_par⟩
  obtain ⟨run, hrun_m, hrun_ok⟩ := checkT3Sync_mem t3ExpectedTriples certsT3All t3Sync_ok (d2, dg, d1) hmem_t
  unfold checkT3Run at hrun_ok
  dsimp only at hrun_ok
  set m0 : ℕ := max (d2 + 2) (d1 + 1)
  have hm0_le : m0 ≤ dStar := by rcases hdStar with rfl | ⟨hgt, _, _⟩ <;> omega
  have hwY_pos : 0 < wY := by norm_num [wY, D]
  have hlo_m0 : ((m0 * wY - 2 : ℕ) : ℚ) / (wY : ℚ) ≤ cVal := by
    refine le_trans ?_ hlo
    apply div_le_div_of_nonneg_right _ (by exact_mod_cast hwY_pos.le)
    have : m0 * wY - 2 ≤ dStar * wY - 2 := Nat.sub_le_sub_right (Nat.mul_le_mul_right wY hm0_le) 2
    exact_mod_cast this
  split_ifs at hrun_ok with hno
  · obtain ⟨c, hc_f, hclo, hchi⟩ := exists_mem_of_checkCover
      (fun c : T3Cert => (c.cLoNum, c.cLoDen)) (fun c : T3Cert => (c.cHiNum, c.cHiDen))
      (m0 * wY - 2) wY 51 2 hwY_pos (by norm_num) _ hno cVal hlo_m0 hhi
    have ⟨hc_run, hc_p⟩ := List.mem_filter.mp hc_f
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc_p
    have ⟨hc_all, h1, h2, h3⟩ := hrun_m c hc_run
    exact Or.inl ⟨c, hc_all, h1, h2, h3, certsT3All_ok c hc_all, Or.inl hc_p, hclo, hchi⟩
  · have hmem_ds : dStar ∈ t3ExpectedDStars m0 := by
      unfold t3ExpectedDStars
      rcases hdStar with rfl | ⟨hgt, hle, hev⟩
      · exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨?_, by simp; omega⟩)
        exact List.mem_map.mpr ⟨dStar / 2, List.mem_range.mpr (by omega), by omega⟩
    have hds_ok := List.all_eq_true.mp hrun_ok dStar hmem_ds
    split_ifs at hds_ok with hsp
    · simp only [Bool.and_eq_true, beq_iff_eq] at hsp hds_ok
      rcases hsp with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
      rcases hds_ok with ⟨h2A_cov, h2B_cov⟩
      obtain ⟨cA, hcA_f, hAlo, hAhi⟩ := exists_mem_of_checkCover
        (fun c : T3Cert => (c.cLoNum, c.cLoDen)) (fun c : T3Cert => (c.cHiNum, c.cHiDen))
        (11 * wY - 2) wY 51 2 hwY_pos (by norm_num) _ h2A_cov cVal hlo hhi
      have ⟨hcA_run, hcA_p⟩ := List.mem_filter.mp hcA_f
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcA_p
      have ⟨hcA_all, hA1, hA2, hA3⟩ := hrun_m cA hcA_run
      obtain ⟨sB, hsB_mem, hBlo, hBhi⟩ := exists_mem_of_checkCover
        (Sum.elim (fun b : T3_2BCert => (b.cLoNum, b.cLoDen)) (fun c : T3Cert => (c.cLoNum, c.cLoDen)))
        (Sum.elim (fun b : T3_2BCert => (b.cHiNum, b.cHiDen)) (fun c : T3Cert => (c.cHiNum, c.cHiDen)))
        (11 * wY - 2) wY 51 2 hwY_pos (by norm_num) _ h2B_cov cVal hlo hhi
      refine Or.inr ⟨rfl, rfl, rfl, rfl,
        ⟨cA, hcA_all, hA1, hA2, hA3, certsT3All_ok cA hcA_all, hcA_p.1.1, hcA_p.1.2, hcA_p.2, hAlo, hAhi⟩, ?_⟩
      simp only [List.mem_append, List.mem_map] at hsB_mem
      rcases hsB_mem with ⟨b, hb_mem, rfl⟩ | ⟨cS, hcS_f, rfl⟩
      · exact Or.inl ⟨b, hb_mem, List.all_eq_true.mp certsT3_2B_ok b hb_mem, hBlo, hBhi⟩
      · have ⟨hcS_run, hcS_p⟩ := List.mem_filter.mp hcS_f
        simp only [Bool.and_eq_true, beq_iff_eq] at hcS_p
        have ⟨hcS_all, hS1, hS2, hS3⟩ := hrun_m cS hcS_run
        exact Or.inr ⟨cS, hcS_all, hS1, hS2, hS3, certsT3All_ok cS hcS_all, hcS_p.1.1, hcS_p.1.2, hcS_p.2, hBlo, hBhi⟩
    · obtain ⟨c, hc_f, hclo, hchi⟩ := exists_mem_of_checkCover
        (fun c : T3Cert => (c.cLoNum, c.cLoDen)) (fun c : T3Cert => (c.cHiNum, c.cHiDen))
        (dStar * wY - 2) wY 51 2 hwY_pos (by norm_num) _ hds_ok cVal hlo hhi
      have ⟨hc_run, hc_p⟩ := List.mem_filter.mp hc_f
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc_p
      have ⟨hc_all, h1, h2, h3⟩ := hrun_m c hc_run
      refine Or.inl ⟨c, hc_all, h1, h2, h3, certsT3All_ok c hc_all, Or.inr ⟨hc_p.1.1, hc_p.1.2, ?_⟩, hclo, hchi⟩
      rcases hc_p.2 with (hm0 | hm1) | ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hm3⟩
      · exact Or.inl hm0
      · exact Or.inr (Or.inl hm1)
      · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, hm3⟩)

/-! ### Part 2: `wdegBi` Multiplicativity, Exact `biMult`, and Resultant Cancellation -/

section BiPolyAlgebra

variable {A : Type*} [CommRing A] [IsDomain A]

/-- Weighted `(1, wY)` degree over any integral domain `A` (identical to `B6401KerD2.wdegBi` on fields). -/
noncomputable def wdegBiDom (wY : ℕ) (f : BiPoly A) : ℕ :=
  f.support.sup fun j => (f.coeff j).natDegree + j * wY

lemma wdegBiDom_eq_wdegBi {F : Type*} [Field F] (wY : ℕ) (f : BiPoly F) :
    wdegBiDom wY f = wdegBi wY f := rfl

lemma wdegBiDom_le_iff (wY W : ℕ) (f : BiPoly A) :
    wdegBiDom wY f ≤ W ↔ ∀ j i, (f.coeff j).coeff i ≠ 0 → i + j * wY ≤ W := by
  unfold wdegBiDom; rw [Finset.sup_le_iff]
  constructor
  · intro h j i hnz
    have hj : j ∈ f.support := Polynomial.mem_support_iff.mpr fun h0 => hnz (by simp [h0])
    have hi : i ≤ (f.coeff j).natDegree := Polynomial.le_natDegree_of_ne_zero hnz
    have := h j hj; omega
  · intro h j hj
    have hne : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    exact h j _ (Polynomial.leadingCoeff_ne_zero.mpr hne)

lemma wdegBiDom_C (wY : ℕ) (p : Polynomial A) : wdegBiDom wY (C p) = p.natDegree := by
  by_cases hp : p = 0
  · subst hp; simp [wdegBiDom]
  · unfold wdegBiDom; rw [Polynomial.support_C hp]; simp

lemma wdegBiDom_map_le {B : Type*} [CommRing B] [IsDomain B] (φ : A →+* B) (wY : ℕ) (f : BiPoly A) :
    wdegBiDom wY (f.map (Polynomial.mapRingHom φ)) ≤ wdegBiDom wY f := by
  rw [wdegBiDom_le_iff]; intro j i hnz
  simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom] at hnz
  have hnz' : (f.coeff j).coeff i ≠ 0 := fun h => hnz (by simp [h])
  exact (wdegBiDom_le_iff wY (wdegBiDom wY f) f).mp le_rfl j i hnz'

lemma wdegBiDom_map_eq_of_injective {B : Type*} [CommRing B] [IsDomain B]
    (φ : A →+* B) (hφ : Function.Injective φ) (wY : ℕ) (f : BiPoly A) :
    wdegBiDom wY (f.map (Polynomial.mapRingHom φ)) = wdegBiDom wY f := by
  apply le_antisymm (wdegBiDom_map_le φ wY f)
  rw [wdegBiDom_le_iff]; intro j i hnz
  have hnz' : ((f.map (Polynomial.mapRingHom φ)).coeff j).coeff i ≠ 0 := by
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact fun h => hnz (hφ (by rwa [map_zero]))
  exact (wdegBiDom_le_iff wY _ _).mp le_rfl j i hnz'

/-- Exact additivity `wdegBiDom wY (p * q) = wdegBiDom wY p + wdegBiDom wY q` over any domain `A`! -/
theorem wdegBiDom_mul (wY : ℕ) {p q : BiPoly A} (hp : p ≠ 0) (hq : q ≠ 0) :
    wdegBiDom wY (p * q) = wdegBiDom wY p + wdegBiDom wY q := by
  classical
  apply le_antisymm
  · rw [wdegBiDom_le_iff]; intro j i hnz
    rw [Polynomial.coeff_mul, finset_sum_coeff] at hnz
    obtain ⟨⟨j1, j2⟩, hjmem, hjnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    rw [Polynomial.coeff_mul] at hjnz
    obtain ⟨⟨i1, i2⟩, himem, hinz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hjnz
    have hp1 : (p.coeff j1).coeff i1 ≠ 0 := left_ne_zero_of_mul hinz
    have hq2 : (q.coeff j2).coeff i2 ≠ 0 := right_ne_zero_of_mul hinz
    have h1 := (wdegBiDom_le_iff wY (wdegBiDom wY p) p).mp le_rfl j1 i1 hp1
    have h2 := (wdegBiDom_le_iff wY (wdegBiDom wY q) q).mp le_rfl j2 i2 hq2
    have hj_eq : j1 + j2 = j := Finset.mem_antidiagonal.mp hjmem
    have hi_eq : i1 + i2 = i := Finset.mem_antidiagonal.mp himem
    have : i + j * wY = (i1 + j1 * wY) + (i2 + j2 * wY) := by rw [← hi_eq, ← hj_eq]; ring
    omega
  · -- Pick max-weight (j1, i1) in p and max-weight (j2, i2) in q (breaking ties by largest j)!
    have hp_ne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
    have hq_ne : q.support.Nonempty := Polynomial.support_nonempty.mpr hq
    let S1 := p.support.filter fun j => (p.coeff j).natDegree + j * wY = wdegBiDom wY p
    let S2 := q.support.filter fun j => (q.coeff j).natDegree + j * wY = wdegBiDom wY q
    have hS1 : S1.Nonempty := by
      obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup p.support hp_ne (fun j => (p.coeff j).natDegree + j * wY)
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, hmax.symm⟩⟩
    have hS2 : S2.Nonempty := by
      obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup q.support hq_ne (fun j => (q.coeff j).natDegree + j * wY)
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, hmax.symm⟩⟩
    let j1 := S1.max' hS1
    let j2 := S2.max' hS2
    have hj1_m : j1 ∈ S1 := Finset.max'_mem S1 hS1
    have hj2_m : j2 ∈ S2 := Finset.max'_mem S2 hS2
    have hj1_s : j1 ∈ p.support := (Finset.mem_filter.mp hj1_m).1
    have hj2_s : j2 ∈ q.support := (Finset.mem_filter.mp hj2_m).1
    have hj1_w : (p.coeff j1).natDegree + j1 * wY = wdegBiDom wY p := (Finset.mem_filter.mp hj1_m).2
    have hj2_w : (q.coeff j2).natDegree + j2 * wY = wdegBiDom wY q := (Finset.mem_filter.mp hj2_m).2
    let i1 := (p.coeff j1).natDegree
    let i2 := (q.coeff j2).natDegree
    have hnz_prod : ((p * q).coeff (j1 + j2)).coeff (i1 + i2) ≠ 0 := by
      rw [Polynomial.coeff_mul, finset_sum_coeff]
      rw [Finset.sum_eq_single (j1, j2)]
      · rw [Polynomial.coeff_mul, Finset.sum_eq_single (i1, i2)]
        · exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp hj1_s))
            (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp hj2_s))
        · intro ⟨a1, a2⟩ ha hne
          have hsum : a1 + a2 = i1 + i2 := Finset.mem_antidiagonal.mp ha
          by_cases ha1 : i1 < a1
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ha1, zero_mul]
          · have ha2 : i2 < a2 := by
              by_contra hle; apply hne; ext <;> dsimp <;> omega
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt ha2, mul_zero]
        · intro h; simp at h
      · intro ⟨b1, b2⟩ hb hne
        have hsum : b1 + b2 = j1 + j2 := Finset.mem_antidiagonal.mp hb
        rw [Polynomial.coeff_mul]
        apply Finset.sum_eq_zero; intro ⟨a1, a2⟩ ha
        have hasum : a1 + a2 = i1 + i2 := Finset.mem_antidiagonal.mp ha
        by_cases hp0 : (p.coeff b1).coeff a1 = 0
        · rw [hp0, zero_mul]
        · by_cases hq0 : (q.coeff b2).coeff a2 = 0
          · rw [hq0, mul_zero]
          · exfalso
            have hw1 := (wdegBiDom_le_iff wY (wdegBiDom wY p) p).mp le_rfl b1 a1 hp0
            have hw2 := (wdegBiDom_le_iff wY (wdegBiDom wY q) q).mp le_rfl b2 a2 hq0
            have htot : (a1 + b1 * wY) + (a2 + b2 * wY) = wdegBiDom wY p + wdegBiDom wY q := by
              have : (a1 + b1 * wY) + (a2 + b2 * wY) = (i1 + j1 * wY) + (i2 + j2 * wY) := by
                have h1 : a1 + a2 = i1 + i2 := hasum
                have h2 : b1 + b2 = j1 + j2 := hsum
                calc (a1 + b1 * wY) + (a2 + b2 * wY) = (a1 + a2) + (b1 + b2) * wY := by ring
                  _ = (i1 + i2) + (j1 + j2) * wY := by rw [h1, h2]
                  _ = (i1 + j1 * wY) + (i2 + j2 * wY) := by ring
              rw [this, hj1_w, hj2_w]
            have heq1 : a1 + b1 * wY = wdegBiDom wY p := by omega
            have heq2 : a2 + b2 * wY = wdegBiDom wY q := by omega
            have hb1_mem : b1 ∈ S1 := by
              refine Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr fun h => hp0 (by simp [h]), ?_⟩
              have hle_nd : a1 ≤ (p.coeff b1).natDegree := Polynomial.le_natDegree_of_ne_zero hp0
              have hle_w := (wdegBiDom_le_iff wY (wdegBiDom wY p) p).mp le_rfl b1 _
                (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp
                  (Polynomial.mem_support_iff.mpr fun h => hp0 (by simp [h]))))
              omega
            have hb2_mem : b2 ∈ S2 := by
              refine Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr fun h => hq0 (by simp [h]), ?_⟩
              have hle_nd : a2 ≤ (q.coeff b2).natDegree := Polynomial.le_natDegree_of_ne_zero hq0
              have hle_w := (wdegBiDom_le_iff wY (wdegBiDom wY q) q).mp le_rfl b2 _
                (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp
                  (Polynomial.mem_support_iff.mpr fun h => hq0 (by simp [h]))))
              omega
            have hb1_le : b1 ≤ j1 := Finset.le_max' S1 b1 hb1_mem
            have hb2_le : b2 ≤ j2 := Finset.le_max' S2 b2 hb2_mem
            exact hne (by ext <;> dsimp <;> omega)
      · intro h; simp at h
    have hle := (wdegBiDom_le_iff wY (wdegBiDom wY (p * q)) (p * q)).mp le_rfl (j1 + j2) (i1 + i2) hnz_prod
    have hsum_w : (i1 + i2) + (j1 + j2) * wY = wdegBiDom wY p + wdegBiDom wY q := by
      calc (i1 + i2) + (j1 + j2) * wY = (i1 + j1 * wY) + (i2 + j2 * wY) := by ring
        _ = wdegBiDom wY p + wdegBiDom wY q := by rw [hj1_w, hj2_w]
    omega

/-- Exact 2D multiplicity of `f : BiPoly A` at `(x0, y0)` (returns `0` if `f = 0`). -/
noncomputable def biMult (x0 y0 : A) (f : BiPoly A) : ℕ := by
  classical
  let s := shiftBi x0 y0 f
  let degs := s.support.biUnion fun j => (s.coeff j).support.image fun i => i + j
  exact if h : degs.Nonempty then degs.min' h else 0

lemma shiftBi_eq_zero_iff (x0 y0 : A) (f : BiPoly A) : shiftBi x0 y0 f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hinv : shiftBi (-x0) (-y0) (shiftBi x0 y0 f) = f := by
      unfold shiftBi
      rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
        Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
      have hC : (Polynomial.compRingHom (C (-x0) + X)) (C y0) = C y0 := by
        simp [Polynomial.compRingHom]
      rw [hC, show C (C y0) + (C (C (-y0)) + X) = X by rw [← add_assoc, ← map_add, ← map_add]; simp,
        Polynomial.comp_X, Polynomial.map_map]
      have hcomp : (Polynomial.compRingHom (C (-x0) + X)).comp (Polynomial.compRingHom (C x0 + X)) =
          RingHom.id (Polynomial A) := by
        ext
        · simp [Polynomial.compRingHom]
        · simp [Polynomial.compRingHom]
      rw [hcomp, Polynomial.map_id]
    rw [h] at hinv
    have h0 : shiftBi (-x0) (-y0) (0 : BiPoly A) = 0 := by unfold shiftBi; simp
    rw [h0] at hinv; exact hinv.symm
  · rintro rfl; unfold shiftBi; simp

lemma biMultGE_biMult (x0 y0 : A) (f : BiPoly A) : biMultGE x0 y0 f (biMult x0 y0 f) := by
  classical
  intro i j hij
  by_contra hnz
  let s := shiftBi x0 y0 f
  let degs := s.support.biUnion fun j => (s.coeff j).support.image fun i => i + j
  have hmem : i + j ∈ degs := Finset.mem_biUnion.mpr ⟨j,
    Polynomial.mem_support_iff.mpr fun h0 => hnz (by change (s.coeff j).coeff i = 0; rw [h0, Polynomial.coeff_zero]),
    Finset.mem_image.mpr ⟨i, Polynomial.mem_support_iff.mpr hnz, rfl⟩⟩
  have hne : degs.Nonempty := ⟨i + j, hmem⟩
  have hbm : biMult x0 y0 f = degs.min' hne := by unfold biMult; simp only [degs, s, hne, ↓reduceDIte]
  have hle : degs.min' hne ≤ i + j := Finset.min'_le degs (i + j) hmem
  omega

lemma le_biMult_of_biMultGE (x0 y0 : A) {f : BiPoly A} (hf : f ≠ 0) {m : ℕ}
    (hm : biMultGE x0 y0 f m) : m ≤ biMult x0 y0 f := by
  classical
  let s := shiftBi x0 y0 f
  have hs : s ≠ 0 := fun h => hf ((shiftBi_eq_zero_iff x0 y0 f).mp h)
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hs
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj)
  let degs := s.support.biUnion fun j => (s.coeff j).support.image fun i => i + j
  have hne : degs.Nonempty := ⟨i + j, Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩
  have hbm : biMult x0 y0 f = degs.min' hne := by unfold biMult; simp only [degs, s, hne, ↓reduceDIte]
  rw [hbm]
  apply Finset.le_min'; intro d hd
  rcases Finset.mem_biUnion.mp hd with ⟨j', hj', hi'⟩
  rcases Finset.mem_image.mp hi' with ⟨i', hi'm, rfl⟩
  by_contra hlt; push Not at hlt
  exact Polynomial.mem_support_iff.mp hi'm (hm i' j' hlt)

lemma biMultGE_mul (x0 y0 : A) (f g : BiPoly A) (mf mg : ℕ)
    (hf : biMultGE x0 y0 f mf) (hg : biMultGE x0 y0 g mg) :
    biMultGE x0 y0 (f * g) (mf + mg) := by
  intro i j hij
  rw [shiftBi_mul, Polynomial.coeff_mul, finset_sum_coeff]
  apply Finset.sum_eq_zero; intro ⟨j1, j2⟩ hj
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero; intro ⟨i1, i2⟩ hi
  have hj_eq : j1 + j2 = j := Finset.mem_antidiagonal.mp hj
  have hi_eq : i1 + i2 = i := Finset.mem_antidiagonal.mp hi
  by_cases h1 : i1 + j1 < mf
  · rw [hf i1 j1 h1, zero_mul]
  · rw [hg i2 j2 (by omega), mul_zero]

end BiPolyAlgebra
end B6402SmallAlg
end ProximityPrize.SubmissionBinaryLower
