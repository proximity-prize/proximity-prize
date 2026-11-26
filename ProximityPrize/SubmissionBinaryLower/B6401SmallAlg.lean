import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401KerD2
import ProximityPrize.SubmissionBinaryLower.B6401IntFarkas
import ProximityPrize.SubmissionBinaryLower.B6401IntSmallCerts
import ProximityPrize.SubmissionBinaryLower.B6401CertsT1
import ProximityPrize.SubmissionBinaryLower.B6401CertsT2
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3
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
   over `B6401CertsT1`, `B6401CertsT2`, and `B6401CertsT3` (`O(n)` synchronized cover check for T3!).
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
namespace B6401SmallAlg

open Polynomial B6401Params B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6401IntFarkas B6401IntSmallCerts
open B6401CertsT1 B6401CertsT2 B6401CertsT3
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

private lemma rat_le_of_cross {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    (a : ℚ) / (b : ℚ) ≤ (c : ℚ) / (d : ℚ) := by
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  rw [div_le_div_iff₀ hbQ hdQ]
  exact_mod_cast h

private lemma checkCoverGo_mem {α : Type*} (lo hi : α → ℕ × ℕ) (endN endD : ℕ) (hendD : 0 < endD) :
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

private lemma splitLeading_spec {α : Type*} (p : α → Bool) (L : List α) :
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

private lemma checkT3Sync_mem : ∀ (ts : List (ℕ × ℕ × ℕ)) (rem : List T3Cert),
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

private lemma shiftBi_eq_zero_iff (x0 y0 : A) (f : BiPoly A) : shiftBi x0 y0 f = 0 ↔ f = 0 := by
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

/-- Exact additivity `biMult x0 y0 (f * g) = biMult x0 y0 f + biMult x0 y0 g` over any domain `A`! -/
theorem biMult_mul (x0 y0 : A) {f g : BiPoly A} (hf : f ≠ 0) (hg : g ≠ 0) :
    biMult x0 y0 (f * g) = biMult x0 y0 f + biMult x0 y0 g := by
  classical
  apply le_antisymm
  · -- Pick min-j among min-degree nonzero terms of shift f and shift g!
    let sf := shiftBi x0 y0 f
    let sg := shiftBi x0 y0 g
    have hsf : sf ≠ 0 := fun h => hf ((shiftBi_eq_zero_iff x0 y0 f).mp h)
    have hsg : sg ≠ 0 := fun h => hg ((shiftBi_eq_zero_iff x0 y0 g).mp h)
    let mf := biMult x0 y0 f
    let mg := biMult x0 y0 g
    have hmin_pair : ∀ (s : BiPoly A) (hs : s ≠ 0) (m : ℕ),
        (∀ i j, i + j < m → (s.coeff j).coeff i = 0) →
        (∃ i j, i + j = m ∧ (s.coeff j).coeff i ≠ 0) →
        ∃ j0, j0 ≤ m ∧ (s.coeff j0).coeff (m - j0) ≠ 0 ∧
          ∀ j' < j0, (s.coeff j').coeff (m - j') = 0 := by
      intro s _ m _ hex
      let Js := (Finset.range (m + 1)).filter fun j => (s.coeff j).coeff (m - j) ≠ 0
      have hJs : Js.Nonempty := by
        obtain ⟨i, j, hij, hnz⟩ := hex
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rwa [show m - j = i by omega]⟩⟩
      let j0 := Js.min' hJs
      have hj0 := Finset.mem_filter.mp (Finset.min'_mem Js hJs)
      refine ⟨j0, by have := Finset.mem_range.mp hj0.1; omega, hj0.2, fun j' hj' => ?_⟩
      by_contra hnz
      have hmem : j' ∈ Js := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hj0.1; omega), hnz⟩
      have := Finset.min'_le Js j' hmem; omega
    have hex_f : ∃ i j, i + j = mf ∧ (sf.coeff j).coeff i ≠ 0 := by
      let degs := sf.support.biUnion fun j => (sf.coeff j).support.image fun i => i + j
      obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hsf
      obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj)
      have hne : degs.Nonempty := ⟨i + j, Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩
      have hbm : mf = degs.min' hne := by dsimp [mf]; unfold biMult; simp only [degs, sf, hne, ↓reduceDIte]
      have hmem : degs.min' hne ∈ degs := Finset.min'_mem degs hne
      rcases Finset.mem_biUnion.mp hmem with ⟨j', _, hi'⟩
      rcases Finset.mem_image.mp hi' with ⟨i', hi'm, heq⟩
      exact ⟨i', j', heq.trans hbm.symm, Polynomial.mem_support_iff.mp hi'm⟩
    have hex_g : ∃ i j, i + j = mg ∧ (sg.coeff j).coeff i ≠ 0 := by
      let degs := sg.support.biUnion fun j => (sg.coeff j).support.image fun i => i + j
      obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hsg
      obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj)
      have hne : degs.Nonempty := ⟨i + j, Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩
      have hbm : mg = degs.min' hne := by dsimp [mg]; unfold biMult; simp only [degs, sg, hne, ↓reduceDIte]
      have hmem : degs.min' hne ∈ degs := Finset.min'_mem degs hne
      rcases Finset.mem_biUnion.mp hmem with ⟨j', _, hi'⟩
      rcases Finset.mem_image.mp hi' with ⟨i', hi'm, heq⟩
      exact ⟨i', j', heq.trans hbm.symm, Polynomial.mem_support_iff.mp hi'm⟩
    obtain ⟨j1, hj1_le, hj1_nz, hj1_min⟩ := hmin_pair sf hsf mf (biMultGE_biMult x0 y0 f) hex_f
    obtain ⟨j2, hj2_le, hj2_nz, hj2_min⟩ := hmin_pair sg hsg mg (biMultGE_biMult x0 y0 g) hex_g
    have hnz_fg : ((shiftBi x0 y0 (f * g)).coeff (j1 + j2)).coeff ((mf - j1) + (mg - j2)) ≠ 0 := by
      rw [shiftBi_mul, Polynomial.coeff_mul, finset_sum_coeff]
      rw [Finset.sum_eq_single (j1, j2)]
      · rw [Polynomial.coeff_mul, Finset.sum_eq_single (mf - j1, mg - j2)]
        · exact mul_ne_zero hj1_nz hj2_nz
        · intro ⟨i1, i2⟩ hi hne
          have hsum : i1 + i2 = (mf - j1) + (mg - j2) := Finset.mem_antidiagonal.mp hi
          by_cases h1 : i1 + j1 < mf
          · rw [biMultGE_biMult x0 y0 f i1 j1 h1, zero_mul]
          · have h2 : i2 + j2 < mg := by by_contra hge; apply hne; ext <;> dsimp <;> omega
            rw [biMultGE_biMult x0 y0 g i2 j2 h2, mul_zero]
        · intro h; simp at h
      · intro ⟨b1, b2⟩ hb hne
        have hsum : b1 + b2 = j1 + j2 := Finset.mem_antidiagonal.mp hb
        rw [Polynomial.coeff_mul]
        apply Finset.sum_eq_zero; intro ⟨i1, i2⟩ hi
        have hisum : i1 + i2 = (mf - j1) + (mg - j2) := Finset.mem_antidiagonal.mp hi
        by_cases h1 : i1 + b1 < mf
        · rw [biMultGE_biMult x0 y0 f i1 b1 h1, zero_mul]
        · by_cases h2 : i2 + b2 < mg
          · rw [biMultGE_biMult x0 y0 g i2 b2 h2, mul_zero]
          · have heq1 : i1 = mf - b1 := by omega
            have heq2 : i2 = mg - b2 := by omega
            by_cases hb1 : b1 < j1
            · rw [heq1, hj1_min b1 hb1, zero_mul]
            · have hb2 : b2 < j2 := by by_contra hge; apply hne; ext <;> dsimp <;> omega
              rw [heq2, hj2_min b2 hb2, mul_zero]
      · intro h; simp at h
    by_contra hgt; push Not at hgt
    exact hnz_fg (biMultGE_biMult x0 y0 (f * g) ((mf - j1) + (mg - j2)) (j1 + j2) (by omega))
  · exact le_biMult_of_biMultGE x0 y0 (mul_ne_zero hf hg)
      (biMultGE_mul x0 y0 f g _ _ (biMultGE_biMult x0 y0 f) (biMultGE_biMult x0 y0 g))

lemma biMult_map_eq_of_injective {B : Type*} [CommRing B] [IsDomain B]
    (φ : A →+* B) (hφ : Function.Injective φ) (x0 y0 : A) (f : BiPoly A) :
    biMult (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ)) = biMult x0 y0 f := by
  have hsh : shiftBi (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ)) =
      (shiftBi x0 y0 f).map (Polynomial.mapRingHom φ) := by
    unfold shiftBi
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_map, Polynomial.map_map]
    have hcomm : (Polynomial.compRingHom (C (φ x0) + X)).comp (Polynomial.mapRingHom φ) =
        (Polynomial.mapRingHom φ).comp (Polynomial.compRingHom (C x0 + X)) := by
      ext <;> simp [Polynomial.compRingHom]
    rw [hcomm]
  have hcoeff : ∀ j i, ((shiftBi (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ))).coeff j).coeff i =
      φ (((shiftBi x0 y0 f).coeff j).coeff i) := by
    intro j i; rw [hsh, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  by_cases hf : f = 0
  · subst hf; simp [biMult, shiftBi]
  · have hfm : f.map (Polynomial.mapRingHom φ) ≠ 0 := by
      intro h0; apply hf; ext j i
      have := congrArg (fun p : BiPoly B => (p.coeff j).coeff i) h0
      simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero] at this
      exact hφ (by rw [this, Polynomial.coeff_zero, Polynomial.coeff_zero, map_zero])
    apply le_antisymm
    · by_contra hgt; push Not at hgt
      have hge := biMultGE_biMult (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ))
      have hgeA : biMultGE x0 y0 f (biMult (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ))) := by
        intro i j hij; exact hφ (by rw [← hcoeff j i, hge i j hij, map_zero])
      have := le_biMult_of_biMultGE x0 y0 hf hgeA; omega
    · apply le_biMult_of_biMultGE (φ x0) (φ y0) hfm
      intro i j hij; rw [hcoeff j i, biMultGE_biMult x0 y0 f i j hij, map_zero]

lemma biMultGE_map {B : Type*} [CommRing B] [IsDomain B]
    (φ : A →+* B) (x0 y0 : A) (f : BiPoly A) (m : ℕ) (h : biMultGE x0 y0 f m) :
    biMultGE (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ)) m := by
  intro i j hij
  have hsh : shiftBi (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ)) =
      (shiftBi x0 y0 f).map (Polynomial.mapRingHom φ) := by
    unfold shiftBi
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_map, Polynomial.map_map]
    have hcomm : (Polynomial.compRingHom (C (φ x0) + X)).comp (Polynomial.mapRingHom φ) =
        (Polynomial.mapRingHom φ).comp (Polynomial.compRingHom (C x0 + X)) := by
      ext <;> simp [Polynomial.compRingHom]
    rw [hcomm]
  rw [hsh, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map, h i j hij, map_zero]

/-- In characteristic 2, any polynomial `g ∈ A[X^2, Y^2]` has EVEN `biMult x0 y0 g`! -/
lemma biMult_even_of_in_X2_Y2 [CharP A 2] (x0 y0 : A) (g : BiPoly A)
    (heven : ∀ j i, (g.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) :
    biMult x0 y0 g % 2 = 0 := by
  classical
  have hsh_even : ∀ j i, ((shiftBi x0 y0 g).coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    -- Express g as sum of monomials C(C c) * C(X^2)^a * (X^2)^b; shift preserves even (i, j) in char 2!
    have hpow2X : ∀ u v : Polynomial A, (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
      intro u v
      have h2 : (2 : Polynomial A) = 0 := CharTwo.two_eq_zero
      calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
        _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
    have hpow2Y : ∀ u v : BiPoly A, (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
      intro u v
      have h2 : (2 : BiPoly A) = 0 := CharTwo.two_eq_zero
      calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
        _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
    have hsh_monom : ∀ (c : A) (a b : ℕ) (j i : ℕ),
        ((shiftBi x0 y0 (Polynomial.monomial (2 * b) (Polynomial.monomial (2 * a) c))).coeff j).coeff i ≠ 0 →
        i % 2 = 0 ∧ j % 2 = 0 := by
      intro c a b j i hnz
      unfold shiftBi at hnz
      rw [Polynomial.map_monomial, Polynomial.coe_compRingHom] at hnz
      dsimp only at hnz
      rw [Polynomial.monomial_comp, Polynomial.monomial_comp] at hnz
      have hX2 : (C x0 + X : Polynomial A) ^ (2 * a) = (C (x0 ^ 2) + X ^ 2) ^ a := by
        rw [pow_mul, hpow2X, map_pow]
      have hY2 : (C (C y0) + X : BiPoly A) ^ (2 * b) = (C (C (y0 ^ 2)) + X ^ 2) ^ b := by
        rw [pow_mul, hpow2Y, map_pow, map_pow]
      rw [hX2, hY2, add_pow, add_pow, Finset.mul_sum, Finset.mul_sum,
        finset_sum_coeff, finset_sum_coeff] at hnz
      obtain ⟨l, _, hlnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      -- Directly check both j % 2 = 0 and i % 2 = 0 via coeff_mul!
      by_contra hnot
      have hcoeff_ev : ∀ (u : Polynomial A) (k m : ℕ),
          (∀ r, u.coeff r ≠ 0 → r % 2 = 0) →
          (((C u * ((C (C (y0 ^ 2)) ^ k * (X ^ 2) ^ m) * (Nat.choose b k : BiPoly A))).coeff j).coeff i = 0) := by
        intro u k m hu
        have h1 : C u * ((C (C (y0 ^ 2)) ^ k * (X ^ 2) ^ m) * (Nat.choose b k : BiPoly A)) =
            C (u * C (y0 ^ 2) ^ k * (Nat.choose b k : Polynomial A)) * X ^ (2 * m) := by
          simp only [map_mul, map_pow, map_natCast, pow_mul]; ring
        rw [h1, Polynomial.coeff_C_mul_X_pow]
        split_ifs with hjm
        · rw [mul_assoc, ← map_pow C, ← map_natCast C, ← map_mul C, Polynomial.coeff_mul_C]
          by_cases hi_ev : i % 2 = 0
          · exfalso; exact hnot ⟨hi_ev, by omega⟩
          · have : u.coeff i = 0 := by by_contra h; exact hi_ev (hu i h)
            rw [this, zero_mul]
        · simp
      have hu_ev : ∀ r, (C c * ∑ m ∈ Finset.range (a + 1), C (x0 ^ 2) ^ m * (X ^ 2) ^ (a - m) * (Nat.choose a m : Polynomial A)).coeff r ≠ 0 →
          r % 2 = 0 := by
        intro r hr
        rw [Polynomial.coeff_C_mul, finset_sum_coeff] at hr
        have hsum_ne : ∑ m ∈ Finset.range (a + 1), (C (x0 ^ 2) ^ m * (X ^ 2) ^ (a - m) * (Nat.choose a m : Polynomial A)).coeff r ≠ 0 :=
          right_ne_zero_of_mul hr
        obtain ⟨m, _, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
        have hm' : C (x0 ^ 2) ^ m * (X ^ 2) ^ (a - m) * (Nat.choose a m : Polynomial A) =
            C ((x0 ^ 2) ^ m * (Nat.choose a m : A)) * X ^ (2 * (a - m)) := by
          simp only [map_mul, map_pow, map_natCast, pow_mul]; ring
        rw [hm', Polynomial.coeff_C_mul_X_pow] at hm
        split_ifs at hm with hrm
        · omega
        · exact absurd rfl hm
      have hzero := hcoeff_ev _ l (b - l) hu_ev
      rw [Finset.mul_sum] at hzero
      exact hlnz hzero
    -- Sum over g.support and (g.coeff j).support
    intro j i hnz
    have hg_sum : g = ∑ b ∈ g.support, ∑ a ∈ (g.coeff b).support,
        Polynomial.monomial b (Polynomial.monomial a ((g.coeff b).coeff a)) := by
      conv_lhs => rw [g.as_sum_support]
      apply Finset.sum_congr rfl; intro b _
      conv_lhs => rw [(g.coeff b).as_sum_support]
      rw [map_sum]
    have hsh_sum : shiftBi x0 y0 g = ∑ b ∈ g.support, ∑ a ∈ (g.coeff b).support,
        shiftBi x0 y0 (Polynomial.monomial b (Polynomial.monomial a ((g.coeff b).coeff a))) := by
      conv_lhs => rw [hg_sum]
      unfold shiftBi; simp only [Polynomial.map_sum, Polynomial.sum_comp]
    rw [hsh_sum, finset_sum_coeff, finset_sum_coeff] at hnz
    obtain ⟨b, hb, hbnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    rw [finset_sum_coeff, finset_sum_coeff] at hbnz
    obtain ⟨a, ha, hanz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hbnz
    have hpar := heven b a (Polynomial.mem_support_iff.mp ha)
    have hb2 : b = 2 * (b / 2) := by omega
    have ha2 : a = 2 * (a / 2) := by omega
    rw [hb2, ha2] at hanz
    exact hsh_monom _ (a / 2) (b / 2) j i hanz
  by_cases hg : g = 0
  · subst hg; simp [biMult, shiftBi]
  · let s := shiftBi x0 y0 g
    have hs : s ≠ 0 := fun h => hg ((shiftBi_eq_zero_iff x0 y0 g).mp h)
    let degs := s.support.biUnion fun j => (s.coeff j).support.image fun i => i + j
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hs
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj)
    have hne : degs.Nonempty := ⟨i + j, Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩
    have hbm : biMult x0 y0 g = degs.min' hne := by unfold biMult; simp only [degs, s, hne, ↓reduceDIte]
    rw [hbm]
    have hmem := Finset.min'_mem degs hne
    rcases Finset.mem_biUnion.mp hmem with ⟨j', _, hi'⟩
    rcases Finset.mem_image.mp hi' with ⟨i', hi'm, heq⟩
    have hpar := hsh_even j' i' (Polynomial.mem_support_iff.mp hi'm)
    omega

end BiPolyAlgebra

/-! ### Part 3: Resultant Invariance & Char-2 `ker(D)` Resultant Divisibility (`T1`, `T3`, `T3-2A`) -/

section KerDResultants

/-- **Resultant reduction modulo `g`:**
For any polynomials `f, g, q : R[X]` over an integral domain `R` with `f.natDegree ≤ df`,
`(f + q * g).natDegree ≤ df`, and `g.natDegree = dg`:
`Polynomial.resultant (f + q * g) g df dg = Polynomial.resultant f g df dg`! -/
theorem resultant_add_mul_right_deg {R : Type*} [CommRing R] [IsDomain R]
    (f g q : R[X]) (df dg : ℕ)
    (hf : f.natDegree ≤ df) (hfq : (f + q * g).natDegree ≤ df) (hg : g.natDegree = dg) :
    Polynomial.resultant (f + q * g) g df dg = Polynomial.resultant f g df dg := by
  by_cases hg0 : g = 0
  · subst hg0; simp
  let K := FractionRing R
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let gK : K[X] := g.map (algebraMap R K)
  let L := gK.SplittingField
  have hKL : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  let φ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hφ : Function.Injective φ := hKL.comp hRK
  apply hφ
  rw [← Polynomial.resultant_map_map, ← Polynomial.resultant_map_map]
  have hmap_add : (f + q * g).map φ = f.map φ + q.map φ * g.map φ := by
    rw [Polynomial.map_add, Polynomial.map_mul]
  rw [hmap_add]
  have hgL_ne : g.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφ).mpr hg0
  have hgL_deg : (g.map φ).natDegree = dg := by rw [Polynomial.natDegree_map_eq_of_injective hφ, hg]
  have hsplits : (g.map φ).Splits := by
    have heq : g.map φ = gK.map (algebraMap K L) := by simp [φ, gK, Polynomial.map_map]
    rw [heq]; exact Polynomial.SplittingField.splits gK
  have hfac : g.map φ = C (g.map φ).leadingCoeff * ((g.map φ).roots.map fun r => X - C r).prod :=
    hsplits.eq_prod_roots
  have hroots_card : (g.map φ).roots.card = dg := by
    rw [← hgL_deg]; exact hsplits.natDegree_eq_card_roots.symm
  -- Evaluate Res(p, C a * ∏ (X - C r)) = a^df * ∏ p.eval r for BOTH p = f.map φ + q.map φ * g.map φ and p = f.map φ!
  have hres_eval : ∀ (p : L[X]), p.natDegree ≤ df →
      Polynomial.resultant p (g.map φ) df dg =
        (g.map φ).leadingCoeff ^ df * (((-1 : L) ^ df) ^ dg * ((g.map φ).roots.map fun r => p.eval r).prod) := by
    intro p hp
    have hres_prod : ∀ (S : Multiset L),
        Polynomial.resultant p (S.map fun r => X - C r).prod df S.card =
          ((-1 : L) ^ df) ^ S.card * (S.map fun r => p.eval r).prod := by
      intro S
      induction S using Multiset.induction_on with
      | empty => simp [Polynomial.resultant_one_right]
      | cons r T ih =>
          rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons]
          have hT_deg : (T.map fun a => X - C a).prod.natDegree = T.card := by
            rw [Polynomial.natDegree_multiset_prod]
            · simp
            · intro h0; rcases Multiset.mem_map.mp h0 with ⟨a, _, ha⟩; exact Polynomial.X_sub_C_ne_zero a ha
          have hr_deg : (X - C r : L[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C r
          rw [show T.card + 1 = (X - C r : L[X]).natDegree + (T.map fun a => X - C a).prod.natDegree by omega,
            Polynomial.resultant_mul_right p (X - C r) _ df hp, hr_deg, hT_deg,
            Polynomial.resultant_X_sub_C_right p df r hp, ih, pow_add, pow_one]
          ring
    conv_lhs => rw [hfac]
    have hprod_deg : ((g.map φ).roots.map fun r => X - C r).prod.natDegree = dg := by
      rw [Polynomial.natDegree_multiset_prod, ← hroots_card]
      · simp
      · intro h0; rcases Multiset.mem_map.mp h0 with ⟨a, _, ha⟩; exact Polynomial.X_sub_C_ne_zero a ha
    rw [Polynomial.resultant_C_mul_right,
      ← hroots_card, hres_prod (g.map φ).roots]
  rw [hres_eval (f.map φ + q.map φ * g.map φ) (by rw [← hmap_add]; exact Polynomial.natDegree_map_le.trans hfq),
    hres_eval (f.map φ) (Polynomial.natDegree_map_le.trans hf)]
  congr 1; congr 1; congr 1
  apply Multiset.map_congr rfl; intro r hr
  have hroot : (g.map φ).eval r = 0 := (Polynomial.mem_roots hgL_ne).mp hr
  simp [Polynomial.eval_add, Polynomial.eval_mul, hroot]

/-- Nonzero resultant over a field `F` from `IsRelPrime` in `BiPoly F = (F[X])[Y]` (or `(RatFunc F)[Y]`). -/
theorem resultant_ne_zero_of_coprime_ratFunc {F : Type*} [Field F]
    (f g : BiPoly F) (hfnz : f ≠ 0) (hgnz : g ≠ 0)
    (hcop : IsRelPrime (f.map (algebraMap (Polynomial F) (RatFunc F)))
      (g.map (algebraMap (Polynomial F) (RatFunc F)))) :
    Polynomial.resultant f g f.natDegree g.natDegree ≠ 0 := by
  classical
  let ψ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hψ : Function.Injective ψ := IsFractionRing.injective (Polynomial F) (RatFunc F)
  intro h0
  have h0K : Polynomial.resultant (f.map ψ) (g.map ψ) (f.map ψ).natDegree (g.map ψ).natDegree = 0 := by
    rw [Polynomial.natDegree_map_eq_of_injective hψ, Polynomial.natDegree_map_eq_of_injective hψ,
      Polynomial.resultant_map_map, h0, map_zero]
  have hcop' : IsCoprime (f.map ψ) (g.map ψ) := by
    obtain ⟨u, hu⟩ := hcop (EuclideanDomain.gcd_dvd_left (f.map ψ) (g.map ψ))
      (EuclideanDomain.gcd_dvd_right (f.map ψ) (g.map ψ))
    refine ⟨EuclideanDomain.gcdA (f.map ψ) (g.map ψ) * ↑u⁻¹,
            EuclideanDomain.gcdB (f.map ψ) (g.map ψ) * ↑u⁻¹, ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab (f.map ψ) (g.map ψ)
    rw [← hu] at hbez
    calc EuclideanDomain.gcdA (f.map ψ) (g.map ψ) * ↑u⁻¹ * f.map ψ +
          EuclideanDomain.gcdB (f.map ψ) (g.map ψ) * ↑u⁻¹ * g.map ψ
        = (f.map ψ * EuclideanDomain.gcdA (f.map ψ) (g.map ψ) +
            g.map ψ * EuclideanDomain.gcdB (f.map ψ) (g.map ψ)) * ↑u⁻¹ := by ring
      _ = ↑u * ↑u⁻¹ := by rw [← hbez]
      _ = 1 := Units.mul_inv u
  exact Polynomial.resultant_ne_zero (f.map ψ) (g.map ψ) hcop' h0K

/-- Helper: if `f : BiPoly F` has `f.coeff j = 0` for all odd `j`, then `f = Polynomial.expand (Polynomial F) 2 fHalf`! -/
lemma exists_expand2_of_even_Y {R : Type*} [CommRing R] (f : R[X])
    (heven : ∀ j, j % 2 = 1 → f.coeff j = 0) :
    ∃ g : R[X], f = Polynomial.expand R 2 g ∧ 2 * g.natDegree ≤ f.natDegree ∧
      (∀ j, g.coeff j = f.coeff (2 * j)) := by
  let g : R[X] := ∑ j ∈ Finset.range (f.natDegree / 2 + 1), Polynomial.monomial j (f.coeff (2 * j))
  have hg_c : ∀ j, g.coeff j = f.coeff (2 * j) := by
    intro j
    dsimp [g]; rw [finset_sum_coeff]
    by_cases hj : j < f.natDegree / 2 + 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      intro k hk; have := Finset.mem_range.mp hk; simp [Polynomial.coeff_monomial, show k ≠ j by omega]
  have hexp : f = Polynomial.expand R 2 g := by
    ext n
    rw [Polynomial.coeff_expand (by norm_num : 0 < 2)]
    by_cases h2 : 2 ∣ n
    · rw [if_pos h2, hg_c, show 2 * (n / 2) = n by omega]
    · rw [if_neg h2]; exact heven n (by omega)
  have hdeg : 2 * g.natDegree ≤ f.natDegree := by
    have : g.natDegree ≤ f.natDegree / 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
      rw [hg_c]; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    omega
  exact ⟨g, hexp, hdeg, hg_c⟩

private lemma shiftBi_expand2 {F : Type*} [Field F] [CharP F 2] (x0 y0 : F) (g0 : BiPoly F) :
    shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 g0) =
      Polynomial.expand (Polynomial F) 2
        ((g0.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)) := by
  unfold shiftBi
  have h2 : (C (C y0) + X : BiPoly F) ^ 2 = C (C (y0 ^ 2)) + X ^ 2 := by
    have h2bi : (2 : BiPoly F) = 0 := CharTwo.two_eq_zero
    calc (C (C y0) + X : BiPoly F) ^ 2 = C (C y0) ^ 2 + 2 * C (C y0) * X + X ^ 2 := by ring
      _ = C (C (y0 ^ 2)) + X ^ 2 := by rw [h2bi, map_pow, map_pow]; ring
  induction g0 using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add, Polynomial.map_add, Polynomial.add_comp, ha, hb, Polynomial.map_add, Polynomial.add_comp, map_add]
  | monomial n c =>
      rw [Polynomial.expand_monomial, Polynomial.map_monomial, Polynomial.map_monomial,
        Polynomial.monomial_comp, Polynomial.monomial_comp,
        map_mul, map_pow, Polynomial.expand_C, map_add, Polynomial.expand_C, Polynomial.expand_X,
        mul_comm n 2, pow_mul, h2]

private lemma coeff_comp_C_add_X_top {F : Type*} [Field F] (y0 : F) (p : BiPoly F) (n : ℕ)
    (hpn : p.natDegree ≤ n) : (p.comp (C (C y0) + X)).coeff n = p.coeff n := by
  conv_lhs => rw [p.as_sum_range' (n + 1) (by omega)]
  rw [Polynomial.sum_comp, finset_sum_coeff, Finset.sum_eq_single n]
  · rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul, add_comm, add_pow,
      finset_sum_coeff, Finset.sum_eq_single n]
    · simp [Polynomial.coeff_X_pow]
    · intro l _ hne
      have : X ^ l * (C (C y0) : BiPoly F) ^ (n - l) * (Nat.choose n l : BiPoly F) =
          C (C (y0 ^ (n - l) * (Nat.choose n l : F))) * X ^ l := by
        simp only [map_mul, map_pow, map_natCast]; ring
      rw [this, Polynomial.coeff_C_mul_X_pow, if_neg hne.symm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro m hm hne
    have hlt : m < n := by have := Finset.mem_range.mp hm; omega
    rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul]
    have hdeg : ((C (C y0) + X : BiPoly F) ^ m).natDegree ≤ m :=
      Polynomial.natDegree_pow_le.trans (by
        have : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
          (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
        nlinarith only [this])
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := (C (C y0) + X : BiPoly F) ^ m) (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Table 1 Local Resultant Divisibility (`kerD1_resY_ord`):**
For `Fpoly ∈ K_{W_F}(1)` over `[Field F] [CharP F 2]` with `twOrdGE (localShift F) k`,
`d0 = (Fpoly.coeff 0).natDegree`, `d1 = (Fpoly.coeff 1).natDegree` (`2 ≤ d1`), `dp = max d0 (d1 + 1)`:
`(X - C x0) ^ resYKerD1Ord d0 d1 k ∣ (Fpoly.coeff 1).leadingCoeff ^ (dp - d0) * Res_Y(f0, f1; d0, d1)`! -/
theorem kerD1_resY_ord {F : Type*} [Field F] [CharP F 2] {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 y0 : F) (f_coord : KerDIdx wY W_F 1 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k) :
    let Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    let d0 := (Fpoly.coeff 0).natDegree
    let d1 := (Fpoly.coeff 1).natDegree
    let dp := max d0 (d1 + 1)
    2 ≤ d1 →
    (X - C x0) ^ resYKerD1Ord d0 d1 k ∣
      (Fpoly.coeff 1).leadingCoeff ^ (dp - d0) *
        Polynomial.resultant (Fpoly.coeff 0) (Fpoly.coeff 1) d0 d1 := by
  intro Fpoly d0 d1 dp hd1
  by_cases hk0 : k = 0
  · subst hk0; simp [resYKerD1Ord]
  have hk_ne : (k == 0) = false := beq_false_of_ne hk0
  have hdg_ne : (d1 / 2 == 0) = false := beq_false_of_ne (by omega)
  unfold resYKerD1Ord
  simp only [hk_ne, hdg_ne, Bool.false_eq_true, ↓reduceIte, resOrdWeighted2Fast_eq]
  -- Helper: X^a ∣ R ∧ X^b ∣ R → X^(max a b) ∣ R
  have hdvd_max : ∀ (a b : ℕ) (R : Polynomial F),
      (X - C x0) ^ a ∣ R → (X - C x0) ^ b ∣ R → (X - C x0) ^ max a b ∣ R := by
    intro a b R ha hb; rcases le_total a b with h | h
    · rwa [Nat.max_eq_right h]
    · rwa [Nat.max_eq_left h]
  apply hdvd_max
  · -- Branch 1: vKer = resOrdWeighted dp (4*k + 2) (d1 / 2) (2*k - 1) 2 - 2 * (d1 / 2)!
    obtain ⟨_, hbm1⟩ := kerD1_local_ords hwY x0 y0 f_coord hvan
    obtain ⟨Pe, Po, hdecomp, hPe_d, hPo_d, _, _, hP_ord⟩ := kerD1_weighted_decomp hwY x0 y0 f_coord hvan
    -- Show shiftBi x0 y0 (Fpoly.coeff 1) has ONLY even Y-powers (since f_1 ∈ F[X, Y^2])!
    have hf1_ev : ∀ j, j % 2 = 1 → (shiftBi x0 y0 (Fpoly.coeff 1)).coeff j = 0 := by
      have hf1_0 : ∀ j, j % 2 = 1 → (Fpoly.coeff 1).coeff j = 0 := by
        intro j hj
        dsimp [Fpoly]; rw [finset_sum_coeff, finset_sum_coeff]
        apply Finset.sum_eq_zero; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
        have hm := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rcases (show (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) by omega) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [pow_zero, pow_zero, one_mul, one_mul,
            show C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
              simp only [map_mul, map_pow]; ring,
            Polynomial.coeff_C, if_neg (by omega), Polynomial.coeff_zero]
        · rw [pow_one, pow_zero, mul_one,
            show C (C (C (f_coord ⟨(1, 0, b1, a1), he⟩))) * (X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(1, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) * X by
              simp only [map_mul, map_pow]; ring,
            Polynomial.coeff_C_mul_X, if_pos rfl,
            show C (C (f_coord ⟨(1, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 =
              C (C (f_coord ⟨(1, 0, b1, a1), he⟩) * (X ^ 2) ^ a1) * X ^ (2 * b1) by
              simp only [map_mul, map_pow, pow_mul],
            Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
        · rw [pow_zero, pow_one, one_mul,
            show C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
              C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) * X by
              simp only [map_mul, map_pow, map_add]; ring,
            Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add,
            Polynomial.coeff_C_mul_X, if_pos rfl,
            show C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 =
              C (C (f_coord ⟨(0, 1, b1, a1), he⟩) * X * (X ^ 2) ^ a1) * X ^ (2 * b1) by
              simp only [map_mul, map_pow, pow_mul],
            Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      obtain ⟨g0, hg0_eq, _, _⟩ := exists_expand2_of_even_Y (Fpoly.coeff 1) hf1_0
      have hsh_exp : shiftBi x0 y0 (Fpoly.coeff 1) =
          Polynomial.expand (Polynomial F) 2
            ((g0.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)) := by
        rw [hg0_eq, shiftBi_expand2]
      intro j hj
      rw [hsh_exp, Polynomial.coeff_expand (by norm_num : 0 < 2), if_neg (by omega)]
    have hd1_even : d1 % 2 = 0 := by
      have hf1_ne : Fpoly.coeff 1 ≠ 0 := by intro h0; simp [d1, h0] at hd1
      have hsh_deg : (shiftBi x0 y0 (Fpoly.coeff 1)).natDegree = d1 := by
        unfold shiftBi
        have hlc : ((Fpoly.coeff 1).map (Polynomial.compRingHom (C x0 + X))).natDegree = d1 := by
          apply Polynomial.natDegree_map_eq_of_injective
          intro p q hpq
          have := congrArg (fun r => r.comp (X - C x0)) hpq
          simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.comp_X] using this
        have hcomp : ∀ (p : BiPoly F) (c : Polynomial F), (p.comp (C c + X)).natDegree = p.natDegree := by
          intro p c
          apply le_antisymm
          · refine Polynomial.natDegree_comp_le.trans ?_
            have h1 : (C c + X : BiPoly F).natDegree ≤ 1 :=
              (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
            nlinarith only [h1]
          · have hback : ((p.comp (C c + X)).comp (C (-c) + X)).natDegree = p.natDegree := by
              rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
                show C c + (C (-c) + X) = X by rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add],
                Polynomial.comp_X]
            rw [← hback]
            refine Polynomial.natDegree_comp_le.trans ?_
            have h1 : (C (-c) + X : BiPoly F).natDegree ≤ 1 :=
              (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
            nlinarith only [h1]
        rw [hcomp, hlc]
      by_contra hodd
      have hnz : (shiftBi x0 y0 (Fpoly.coeff 1)).coeff d1 ≠ 0 := by
        rw [← hsh_deg]; exact Polynomial.leadingCoeff_ne_zero.mpr
          (fun h => hf1_ne ((shiftBi_eq_zero_iff x0 y0 _).mp h))
      exact hnz (hf1_ev d1 (by omega))
    obtain ⟨g1, hg1_eq, _, hg1_c⟩ := exists_expand2_of_even_Y (shiftBi x0 y0 (Fpoly.coeff 1)) hf1_ev
    have hsh1_deg : (shiftBi x0 y0 (Fpoly.coeff 1)).natDegree = d1 := by
      have hf1_ne : Fpoly.coeff 1 ≠ 0 := by intro h0; simp [d1, h0] at hd1
      unfold shiftBi
      have hinj : Function.Injective (Polynomial.compRingHom (C x0 + X) : Polynomial F →+* Polynomial F) := by
        intro p q hpq; have := congrArg (fun r => r.comp (X - C x0)) hpq
        simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.comp_X] using this
      have h1 : ((Fpoly.coeff 1).map (Polynomial.compRingHom (C x0 + X))).natDegree = d1 :=
        Polynomial.natDegree_map_eq_of_injective hinj _
      have hcomp : ∀ (p : BiPoly F) (c : Polynomial F), (p.comp (C c + X)).natDegree = p.natDegree := by
        intro p c; apply le_antisymm
        · refine Polynomial.natDegree_comp_le.trans ?_
          have h2 : (C c + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [h2]
        · have hb : ((p.comp (C c + X)).comp (C (-c) + X)).natDegree = p.natDegree := by
            rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
              show C c + (C (-c) + X) = X by rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add],
              Polynomial.comp_X]
          rw [← hb]; refine Polynomial.natDegree_comp_le.trans ?_
          have h2 : (C (-c) + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [h2]
      rw [hcomp, h1]
    have hg1_deg : g1.natDegree = d1 / 2 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hg1_eq, hsh1_deg] at h2; omega
    have hg1_ord : weightedOrdGE 2 (2 * k - 1) g1 := by
      intro j; rw [hg1_c j]
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 (Fpoly.coeff 1) (2 * k - 1)).mp hbm1 (2 * j)
    have hPe2 : 2 * Pe.natDegree ≤ dp := by dsimp [dp, d0, d1, Fpoly] at *; omega
    have hPo2 : 2 * Po.natDegree + 1 ≤ dp := by dsimp [dp, d0, d1, Fpoly] at *; omega
    have hres_eq1 : Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0) * C X + shiftBi x0 y0 (Fpoly.coeff 1) * X)
        (shiftBi x0 y0 (Fpoly.coeff 1)) dp d1 =
        Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) g1 dp (d1 / 2) := by
      conv_lhs => rw [hdecomp, hg1_eq, show d1 = 2 * (d1 / 2) by omega]
      exact resultant_expand2 Pe Po g1 dp (d1 / 2) hPe2 hPo2 hg1_deg
    have hsh0_deg : (shiftBi x0 y0 (Fpoly.coeff 0)).natDegree ≤ d0 := by
      unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
      have hm : ((Fpoly.coeff 0).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ d0 := Polynomial.natDegree_map_le
      have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
      nlinarith only [hm, hX]
    have hres_eq2 : Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0) * C X + shiftBi x0 y0 (Fpoly.coeff 1) * X)
        (shiftBi x0 y0 (Fpoly.coeff 1)) dp d1 =
        X ^ d1 * (shiftBi x0 y0 (Fpoly.coeff 1)).leadingCoeff ^ (dp - d0) *
          Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0)) (shiftBi x0 y0 (Fpoly.coeff 1)) d0 d1 := by
      have hdeg_lhs : (shiftBi x0 y0 (Fpoly.coeff 0) * C X).natDegree ≤ dp := by
        refine Polynomial.natDegree_mul_le.trans ?_; simp only [Polynomial.natDegree_C, add_zero]
        exact hsh0_deg.trans (le_max_left _ _)
      have hdeg_sum : (shiftBi x0 y0 (Fpoly.coeff 0) * C X + X * shiftBi x0 y0 (Fpoly.coeff 1)).natDegree ≤ dp := by
        refine (Polynomial.natDegree_add_le _ _).trans (max_le hdeg_lhs ?_)
        refine Polynomial.natDegree_mul_le.trans ?_
        have : (X : BiPoly F).natDegree = 1 := Polynomial.natDegree_X
        rw [this, hsh1_deg]; dsimp [dp]; omega
      have hneg1 : (-1 : Polynomial F) = 1 := CharTwo.neg_eq 1
      conv_lhs =>
        rw [mul_comm (shiftBi x0 y0 (Fpoly.coeff 1)) X,
          resultant_add_mul_right_deg _ _ X dp d1 hdeg_lhs hdeg_sum hsh1_deg,
          mul_comm (shiftBi x0 y0 (Fpoly.coeff 0)) (C X),
          Polynomial.resultant_C_mul_left,
          show dp = d0 + (dp - d0) by dsimp [dp]; omega,
          Polynomial.resultant_add_left_deg _ _ d0 d1 (dp - d0) hsh0_deg,
          show (shiftBi x0 y0 (Fpoly.coeff 1)).coeff d1 = (shiftBi x0 y0 (Fpoly.coeff 1)).leadingCoeff by
            rw [Polynomial.leadingCoeff, hsh1_deg],
          hneg1, one_pow, one_mul]
      ring
    have hdvd_V : X ^ resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2 ∣
        Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) g1 dp (d1 / 2) := by
      apply pow_dvd_resultant_of_weighted_ord X (Pe ^ 2 + X * Po ^ 2) g1 dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact Polynomial.natDegree_pow_le.trans hPe2
        · refine Polynomial.natDegree_mul_le.trans ?_
          rw [Polynomial.natDegree_X]
          have := Polynomial.natDegree_pow_le (p := Po) (n := 2)
          omega
      · exact le_of_eq hg1_deg
      · exact hP_ord
      · exact hg1_ord
    rw [← hres_eq1, hres_eq2] at hdvd_V
    -- Cancel X ^ d1 = X ^ (2 * (d1 / 2))!
    have hdvd_sh : X ^ (resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2 - 2 * (d1 / 2)) ∣
        (shiftBi x0 y0 (Fpoly.coeff 1)).leadingCoeff ^ (dp - d0) *
          Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0)) (shiftBi x0 y0 (Fpoly.coeff 1)) d0 d1 := by
      have hd1_eq : 2 * (d1 / 2) = d1 := by omega
      rw [hd1_eq]
      by_cases hle : d1 ≤ resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2
      · have hsplit : (X : Polynomial F) ^ resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2 =
            (X : Polynomial F) ^ d1 * (X : Polynomial F) ^ (resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2 - d1) := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        rw [hsplit, mul_assoc] at hdvd_V
        exact (mul_dvd_mul_iff_left (pow_ne_zero d1 Polynomial.X_ne_zero)).mp hdvd_V
      · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle), pow_zero]; exact one_dvd _
    -- Identify (shiftBi f1).leadingCoeff = (f1.leadingCoeff).comp (C x0 + X) and shift resultant!
    have hlc_sh : (shiftBi x0 y0 (Fpoly.coeff 1)).leadingCoeff =
        (Fpoly.coeff 1).leadingCoeff.comp (C x0 + X) := by
      rw [Polynomial.leadingCoeff, hsh1_deg]
      unfold shiftBi
      have hmap_deg : ((Fpoly.coeff 1).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ d1 :=
        Polynomial.natDegree_map_le
      rw [coeff_comp_C_add_X_top y0 _ d1 hmap_deg, Polynomial.coeff_map, Polynomial.leadingCoeff]; rfl
    rw [hlc_sh, resultant_shiftBi x0 y0 (Fpoly.coeff 0) (Fpoly.coeff 1) d0 d1 le_rfl le_rfl,
      ← Polynomial.pow_comp, ← Polynomial.mul_comp] at hdvd_sh
    exact X_sub_C_pow_dvd_of_comp_shift x0 _ _ hdvd_sh
  · -- Branch 2: vPln = resOrdExact d0 (2*k - 1) d1 (2*k - 1) + (dp - d0) * (2*k - 1 - d1)!
    obtain ⟨hbm0, hbm1⟩ := kerD1_local_ords hwY x0 y0 f_coord hvan
    have h1 := pow_dvd_leadingCoeff_of_biMultGE x0 y0 (Fpoly.coeff 1) d1 (2 * k - 1) rfl hbm1
    have h1p : (X - C x0) ^ ((dp - d0) * (2 * k - 1 - d1)) ∣ (Fpoly.coeff 1).leadingCoeff ^ (dp - d0) := by
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h1 (dp - d0)
    have h2s := pow_dvd_resultant_of_biMultGE x0 y0 (Fpoly.coeff 0) (Fpoly.coeff 1) d0 (2 * k - 1) d1 (2 * k - 1)
      hbm0 hbm1 le_rfl le_rfl
    rw [resultant_shiftBi x0 y0 (Fpoly.coeff 0) (Fpoly.coeff 1) d0 d1 le_rfl le_rfl] at h2s
    have h2 := X_sub_C_pow_dvd_of_comp_shift x0 _ _ h2s
    rw [add_comm, pow_add]
    exact mul_dvd_mul h1p h2

/-- **Table 3 General Local Resultant Divisibility (`kerD2_resY_f0_g_ord`):**
For `Fpoly ∈ K_{W_F}(2)` with `twOrdGE (localShift F) k`, ANY `g ∈ F[X, Y^2]` (`g = expand 2 gHalf`)
dividing BOTH `Fpoly.coeff 1` and `Fpoly.coeff 2`, with `dg = g.natDegree` even, `r = biMult x0 y0 g`,
and `dStar ≥ max (Fpoly.coeff 0).natDegree (max ((Fpoly.coeff 2).natDegree + 2) ((Fpoly.coeff 1).natDegree + 1))`:
BOTH `v_ker = resOrdWeighted dStar (4*k + 4) (dg / 2) r 2 - 2 * dg` AND
`v_pln = resOrdExact d0 (2*k - 2) dg r + (dStar - d0) * (r - dg)` divide
`g.leadingCoeff ^ (dStar - d0) * Polynomial.resultant (Fpoly.coeff 0) g d0 dg`! -/
theorem kerD2_resY_f0_g_ord {F : Type*} [Field F] [CharP F 2] {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 y0 : F) (f_coord : KerDIdx wY W_F 2 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k)
    (g : BiPoly F) (hg_ne : g ≠ 0) (hg_ev : ∀ j, j % 2 = 1 → g.coeff j = 0)
    (hdvd1 : g ∣ (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1)
    (hdvd2 : g ∣ (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2)
    (dStar : ℕ)
    (hdStar : max ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).natDegree
        (max (((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2).natDegree + 2)
          (((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree + 1)) ≤ dStar) :
    let Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
    let d0 := (Fpoly.coeff 0).natDegree
    let dg := g.natDegree
    let r := biMult x0 y0 g
    (X - C x0) ^ (resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 - 2 * dg) ∣
      g.leadingCoeff ^ (dStar - d0) * Polynomial.resultant (Fpoly.coeff 0) g d0 dg ∧
    (X - C x0) ^ (resOrdExact d0 (2 * k - 2) dg r + (dStar - d0) * (r - dg)) ∣
      g.leadingCoeff ^ (dStar - d0) * Polynomial.resultant (Fpoly.coeff 0) g d0 dg := by
  intro Fpoly d0 dg r
  have hd0_le : d0 ≤ dStar := le_trans (le_max_left _ _) hdStar
  have hd1_le : (Fpoly.coeff 1).natDegree + 1 ≤ dStar :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hdStar
  have hd2_le : (Fpoly.coeff 2).natDegree + 2 ≤ dStar :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hdStar
  obtain ⟨hbm0, _, _, Pe, Po, hdecomp, hPe_d, hPo_d, _, _, hP_ord⟩ := kerD2_local_ords hwY x0 y0 f_coord hvan
  have hbmg : biMultGE x0 y0 g r := biMultGE_biMult x0 y0 g
  constructor
  · -- Branch 1: v_ker!
    obtain ⟨g0, hg0_eq, _, _⟩ := exists_expand2_of_even_Y g hg_ev
    have hsh_exp : shiftBi x0 y0 g =
        Polynomial.expand (Polynomial F) 2
          ((g0.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)) := by
      rw [hg0_eq, shiftBi_expand2]
    set g1 : BiPoly F := (g0.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)
    have hshg_deg : (shiftBi x0 y0 g).natDegree = dg := by
      unfold shiftBi
      have hinj : Function.Injective (Polynomial.compRingHom (C x0 + X) : Polynomial F →+* Polynomial F) := by
        intro p q hpq; have := congrArg (fun r => r.comp (X - C x0)) hpq
        simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.comp_X] using this
      have h1 : (g.map (Polynomial.compRingHom (C x0 + X))).natDegree = dg :=
        Polynomial.natDegree_map_eq_of_injective hinj _
      have hcomp : ∀ (p : BiPoly F) (c : Polynomial F), (p.comp (C c + X)).natDegree = p.natDegree := by
        intro p c; apply le_antisymm
        · refine Polynomial.natDegree_comp_le.trans ?_
          have h2 : (C c + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [h2]
        · have hb : ((p.comp (C c + X)).comp (C (-c) + X)).natDegree = p.natDegree := by
            rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
              show C c + (C (-c) + X) = X by rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add],
              Polynomial.comp_X]
          rw [← hb]; refine Polynomial.natDegree_comp_le.trans ?_
          have h2 : (C (-c) + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [h2]
      rw [hcomp, h1]
    have hdg_ev : dg % 2 = 0 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hsh_exp, hshg_deg] at h2; omega
    have hg1_deg : g1.natDegree = dg / 2 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hsh_exp, hshg_deg] at h2; omega
    have hg1_ord : weightedOrdGE 2 r g1 := by
      intro j
      have hc : (shiftBi x0 y0 g).coeff (2 * j) = g1.coeff j := by
        rw [hsh_exp, Polynomial.coeff_expand (by norm_num : 0 < 2), if_pos ⟨j, rfl⟩,
          Nat.mul_div_cancel_left j (by norm_num)]
      rw [← hc]
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 g r).mp hbmg (2 * j)
    have hPe2 : 2 * Pe.natDegree ≤ dStar := by omega
    have hPo2 : 2 * Po.natDegree + 1 ≤ dStar := by omega
    have hres_eq1 : Polynomial.resultant
        (shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
         shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
         shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2)
        (shiftBi x0 y0 g) dStar dg =
        Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) g1 dStar (dg / 2) := by
      conv_lhs => rw [hdecomp, hsh_exp, show dg = 2 * (dg / 2) by omega]
      exact resultant_expand2 Pe Po g1 dStar (dg / 2) hPe2 hPo2 hg1_deg
    rcases hdvd1 with ⟨h1, hh1⟩
    rcases hdvd2 with ⟨h2, hh2⟩
    have hsh0_deg : (shiftBi x0 y0 (Fpoly.coeff 0)).natDegree ≤ d0 := by
      unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
      have hm : ((Fpoly.coeff 0).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ d0 := Polynomial.natDegree_map_le
      have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
      nlinarith only [hm, hX]
    have hsh1_deg : (shiftBi x0 y0 (Fpoly.coeff 1)).natDegree ≤ (Fpoly.coeff 1).natDegree := by
      unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
      have hm : ((Fpoly.coeff 1).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ (Fpoly.coeff 1).natDegree := Polynomial.natDegree_map_le
      have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
      nlinarith only [hm, hX]
    have hsh2_deg : (shiftBi x0 y0 (Fpoly.coeff 2)).natDegree ≤ (Fpoly.coeff 2).natDegree := by
      unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
      have hm : ((Fpoly.coeff 2).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ (Fpoly.coeff 2).natDegree := Polynomial.natDegree_map_le
      have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
      nlinarith only [hm, hX]
    have hres_eq2 : Polynomial.resultant
        (shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
         shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
         shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2)
        (shiftBi x0 y0 g) dStar dg =
        X ^ (2 * dg) * (shiftBi x0 y0 g).leadingCoeff ^ (dStar - d0) *
          Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0)) (shiftBi x0 y0 g) d0 dg := by
      set qmul : BiPoly F := shiftBi x0 y0 h1 * (C X * X) + shiftBi x0 y0 h2 * X ^ 2
      have hrew : shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
          shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
          shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2 =
          shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) + qmul * shiftBi x0 y0 g := by
        dsimp [qmul]; rw [hh1, hh2, shiftBi_mul, shiftBi_mul]; ring
      have hdeg0 : (shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2)).natDegree ≤ dStar := by
        refine Polynomial.natDegree_mul_le.trans ?_; simp only [Polynomial.natDegree_C, add_zero]; omega
      have hdegS : (shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) + qmul * shiftBi x0 y0 g).natDegree ≤ dStar := by
        rw [← hrew]
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le hdeg0 ?_)) ?_)
        · refine Polynomial.natDegree_mul_le.trans ?_
          have hCX : (C X * X : BiPoly F).natDegree ≤ 1 :=
            Polynomial.natDegree_mul_le.trans (by simp [Polynomial.natDegree_X])
          omega
        · refine Polynomial.natDegree_mul_le.trans ?_
          have hX2 : (X ^ 2 : BiPoly F).natDegree ≤ 2 :=
            Polynomial.natDegree_pow_le.trans (by simp [Polynomial.natDegree_X])
          omega
      have hneg1 : (-1 : Polynomial F) = 1 := CharTwo.neg_eq 1
      conv_lhs =>
        rw [hrew, resultant_add_mul_right_deg _ _ qmul dStar dg hdeg0 hdegS hshg_deg,
          mul_comm (shiftBi x0 y0 (Fpoly.coeff 0)) (C (X ^ 2)),
          Polynomial.resultant_C_mul_left,
          ← pow_mul, show dStar = d0 + (dStar - d0) by omega,
          Polynomial.resultant_add_left_deg _ _ d0 dg (dStar - d0) hsh0_deg,
          show (shiftBi x0 y0 g).coeff dg = (shiftBi x0 y0 g).leadingCoeff by rw [Polynomial.leadingCoeff, hshg_deg],
          hneg1, one_pow, one_mul]
      ring
    have hdvd_V : X ^ resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 ∣
        Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) g1 dStar (dg / 2) := by
      apply pow_dvd_resultant_of_weighted_ord X (Pe ^ 2 + X * Po ^ 2) g1 dStar (4 * k + 4) (dg / 2) r 2
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact Polynomial.natDegree_pow_le.trans hPe2
        · refine Polynomial.natDegree_mul_le.trans ?_
          rw [Polynomial.natDegree_X]
          have := Polynomial.natDegree_pow_le (p := Po) (n := 2)
          omega
      · exact le_of_eq hg1_deg
      · exact hP_ord
      · exact hg1_ord
    rw [← hres_eq1, hres_eq2] at hdvd_V
    have hdvd_sh : X ^ (resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 - 2 * dg) ∣
        (shiftBi x0 y0 g).leadingCoeff ^ (dStar - d0) *
          Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0)) (shiftBi x0 y0 g) d0 dg := by
      by_cases hle : 2 * dg ≤ resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2
      · have hsplit : (X : Polynomial F) ^ resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 =
            (X : Polynomial F) ^ (2 * dg) * (X : Polynomial F) ^ (resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 - 2 * dg) := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        rw [hsplit, mul_assoc] at hdvd_V
        exact (mul_dvd_mul_iff_left (pow_ne_zero (2 * dg) Polynomial.X_ne_zero)).mp hdvd_V
      · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle), pow_zero]; exact one_dvd _
    have hlc_sh : (shiftBi x0 y0 g).leadingCoeff = g.leadingCoeff.comp (C x0 + X) := by
      rw [Polynomial.leadingCoeff, hshg_deg]; unfold shiftBi
      have hmap_deg : (g.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ dg := Polynomial.natDegree_map_le
      rw [coeff_comp_C_add_X_top y0 _ dg hmap_deg, Polynomial.coeff_map, Polynomial.leadingCoeff]; rfl
    rw [hlc_sh, resultant_shiftBi x0 y0 (Fpoly.coeff 0) g d0 dg le_rfl le_rfl,
      ← Polynomial.pow_comp, ← Polynomial.mul_comp] at hdvd_sh
    exact X_sub_C_pow_dvd_of_comp_shift x0 _ _ hdvd_sh
  · -- Branch 2: v_pln!
    have h1 := pow_dvd_leadingCoeff_of_biMultGE x0 y0 g dg r rfl hbmg
    have h1p : (X - C x0) ^ ((dStar - d0) * (r - dg)) ∣ g.leadingCoeff ^ (dStar - d0) := by
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h1 (dStar - d0)
    have h2s := pow_dvd_resultant_of_biMultGE x0 y0 (Fpoly.coeff 0) g d0 (2 * k - 2) dg r hbm0 hbmg le_rfl le_rfl
    rw [resultant_shiftBi x0 y0 (Fpoly.coeff 0) g d0 dg le_rfl le_rfl] at h2s
    have h2 := X_sub_C_pow_dvd_of_comp_shift x0 _ _ h2s
    rw [add_comm, pow_add]
    exact mul_dvd_mul h1p h2

/-- Coefficient-wise `X`-derivative on `BiPoly F = (F[X])[Y]`. -/
private noncomputable def dXBi {F : Type*} [CommRing F] (p : BiPoly F) : BiPoly F :=
  ∑ j ∈ p.support, Polynomial.monomial j (p.coeff j).derivative

private lemma coeff_dXBi {F : Type*} [CommRing F] (p : BiPoly F) (j : ℕ) :
    (dXBi p).coeff j = (p.coeff j).derivative := by
  unfold dXBi; rw [finset_sum_coeff]
  by_cases hj : j ∈ p.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hne; simp [Polynomial.coeff_monomial, hne]
    · intro h; exact absurd hj h
  · rw [Finset.sum_eq_zero, Polynomial.notMem_support_iff.mp hj, map_zero]
    intro k hk; simp [Polynomial.coeff_monomial, show k ≠ j by intro heq; subst heq; exact hj hk]

private lemma dXBi_mul {F : Type*} [CommRing F] (p q : BiPoly F) :
    dXBi (p * q) = dXBi p * q + p * dXBi q := by
  rw [Polynomial.ext_iff]; intro j
  rw [coeff_dXBi, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul, Polynomial.coeff_mul,
    map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ⟨a, b⟩ _
  rw [Polynomial.derivative_mul, coeff_dXBi, coeff_dXBi]

private lemma dXBi_eq_zero_of_xev {F : Type*} [CommRing F] [CharP F 2] (p : BiPoly F)
    (hxev : ∀ j i, i % 2 = 1 → (p.coeff j).coeff i = 0) : dXBi p = 0 := by
  ext j i
  rw [coeff_dXBi, Polynomial.coeff_derivative, Polynomial.coeff_zero, Polynomial.coeff_zero]
  by_cases hi : (i + 1) % 2 = 1
  · rw [hxev j (i + 1) hi, zero_mul]
  · have h2 : ((i : F) + 1) = 0 := by
      have hdiv : i + 1 = 2 * ((i + 1) / 2) := by omega
      have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
      calc (i : F) + 1 = ((i + 1 : ℕ) : F) := by push_cast; rfl
        _ = ((2 * ((i + 1) / 2) : ℕ) : F) := congrArg Nat.cast hdiv
        _ = (2 : F) * (((i + 1) / 2 : ℕ) : F) := by push_cast; rfl
        _ = 0 := by rw [h2F, zero_mul]
    rw [h2, mul_zero]

private lemma natDegree_dXBi_le {F : Type*} [CommRing F] (p : BiPoly F) :
    (dXBi p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
  rw [coeff_dXBi, Polynomial.coeff_eq_zero_of_natDegree_lt hj, map_zero]

private noncomputable def evenPartX {F : Type*} [Semiring F] (p : Polynomial F) : Polynomial F :=
  ∑ i ∈ Finset.range (p.natDegree / 2 + 1), Polynomial.monomial (2 * i) (p.coeff (2 * i))

private lemma coeff_evenPartX {F : Type*} [Semiring F] (p : Polynomial F) (n : ℕ) :
    (evenPartX p).coeff n = if n % 2 = 0 then p.coeff n else 0 := by
  unfold evenPartX; rw [finset_sum_coeff]
  split_ifs with hn
  · by_cases hlt : n / 2 < p.natDegree / 2 + 1
    · rw [Finset.sum_eq_single (n / 2)]
      · simp [Polynomial.coeff_monomial, show 2 * (n / 2) = n by omega]
      · intro k _ hne; simp [Polynomial.coeff_monomial, show 2 * k ≠ n by omega]
      · intro h; exact absurd (Finset.mem_range.mpr hlt) h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      apply Finset.sum_eq_zero; intro k hk
      have := Finset.mem_range.mp hk; simp [Polynomial.coeff_monomial, show 2 * k ≠ n by omega]
  · apply Finset.sum_eq_zero; intro k _
    simp [Polynomial.coeff_monomial, show 2 * k ≠ n by omega]

private lemma evenPartX_mul_of_xev {F : Type*} [CommRing F] (p q : Polynomial F)
    (hp : ∀ i, i % 2 = 1 → p.coeff i = 0) :
    evenPartX (p * q) = p * evenPartX q := by
  ext n
  rw [coeff_evenPartX, Polynomial.coeff_mul]
  split_ifs with hn
  · rw [Polynomial.coeff_mul]
    apply Finset.sum_congr rfl; intro ⟨a, b⟩ hab
    have hsum : a + b = n := Finset.mem_antidiagonal.mp hab
    rw [coeff_evenPartX]
    by_cases hb : b % 2 = 0
    · rw [if_pos hb]
    · rw [if_neg hb, hp a (by omega), zero_mul, zero_mul]
  · symm; rw [Polynomial.coeff_mul]; apply Finset.sum_eq_zero; intro ⟨a, b⟩ hab
    have hsum : a + b = n := Finset.mem_antidiagonal.mp hab
    rw [coeff_evenPartX]
    by_cases hb : b % 2 = 0
    · rw [hp a (by omega), zero_mul]
    · rw [if_neg hb, mul_zero]

private lemma shiftBi_in_X2_Y2 {F : Type*} [Field F] [CharP F 2] (x0 y0 : F) (p : BiPoly F)
    (hp : ∀ j i, (p.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) :
    ∀ j i, ((shiftBi x0 y0 p).coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
  intro j i hnz
  have hpow2X : ∀ u v : Polynomial F, (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
    intro u v
    have h2 : (2 : Polynomial F) = 0 := CharTwo.two_eq_zero
    calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
      _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
  have hpow2Y : ∀ u v : BiPoly F, (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
    intro u v
    have h2 : (2 : BiPoly F) = 0 := CharTwo.two_eq_zero
    calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
      _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
  have hsh_monom : ∀ (c : F) (a b : ℕ) (j' i' : ℕ),
      ((shiftBi x0 y0 (Polynomial.monomial (2 * b) (Polynomial.monomial (2 * a) c))).coeff j').coeff i' ≠ 0 →
      i' % 2 = 0 ∧ j' % 2 = 0 := by
    intro c a b j' i' hnz'
    have hmon : Polynomial.monomial (2 * b) (Polynomial.monomial (2 * a) c) =
        C (C c) * C (X ^ 2) ^ a * (X ^ 2) ^ b := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
        pow_mul, pow_mul, map_mul, map_pow]
    rw [hmon, shiftBi_mul, shiftBi_mul, shiftBi_C, shiftBi_pow, shiftBi_C, shiftBi_pow, shiftBi_pow, shiftBi_X] at hnz'
    simp only [Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, ← map_pow] at hnz'
    rw [hpow2X (C x0) X, hpow2Y (C (C y0)) X,
      add_pow (C x0 ^ 2) (X ^ 2) a, add_pow (C (C y0) ^ 2) (X ^ 2) b] at hnz'
    have hrew : C (C c) * C (∑ l ∈ Finset.range (a + 1), (C x0 ^ 2) ^ l * (X ^ 2) ^ (a - l) * ((a.choose l : ℕ) : Polynomial F)) *
        (∑ m ∈ Finset.range (b + 1), (C (C y0) ^ 2) ^ m * (X ^ 2) ^ (b - m) * ((b.choose m : ℕ) : BiPoly F)) =
        ∑ m ∈ Finset.range (b + 1),
          C (∑ l ∈ Finset.range (a + 1),
            C (c * (x0 ^ 2) ^ l * (a.choose l : F) * ((y0 ^ 2) ^ m * (b.choose m : F))) * X ^ (2 * (a - l))) *
            X ^ (2 * (b - m)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
      have hm_eq : (C (C y0) ^ 2 : BiPoly F) ^ m * (X ^ 2) ^ (b - m) * ((b.choose m : ℕ) : BiPoly F) =
          C (C ((y0 ^ 2) ^ m * (b.choose m : F))) * X ^ (2 * (b - m)) := by
        simp only [map_mul, map_pow, map_natCast, ← pow_mul]; ring
      rw [hm_eq, ← mul_assoc, ← map_mul, ← map_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1; congr 1
      apply Finset.sum_congr rfl; intro l _
      simp only [map_mul, map_pow, map_natCast, ← pow_mul]; ring
    rw [hrew, finset_sum_coeff, finset_sum_coeff] at hnz'
    obtain ⟨m, _, hmnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz'
    rw [Polynomial.coeff_C_mul_X_pow] at hmnz
    split_ifs at hmnz with hjm
    · rw [finset_sum_coeff] at hmnz
      obtain ⟨l, _, hlnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmnz
      rw [Polynomial.coeff_C_mul_X_pow] at hlnz
      split_ifs at hlnz with hil
      · omega
      · exact absurd rfl hlnz
    · simp at hmnz
  have hp_sum : p = ∑ b ∈ p.support, ∑ a ∈ (p.coeff b).support,
      Polynomial.monomial b (Polynomial.monomial a ((p.coeff b).coeff a)) := by
    conv_lhs => rw [p.as_sum_support]
    apply Finset.sum_congr rfl; intro b _
    conv_lhs => rw [(p.coeff b).as_sum_support]
    rw [map_sum]
  rw [hp_sum] at hnz
  have hsh_sum : shiftBi x0 y0 (∑ b ∈ p.support, ∑ a ∈ (p.coeff b).support,
      Polynomial.monomial b (Polynomial.monomial a ((p.coeff b).coeff a))) =
      ∑ b ∈ p.support, ∑ a ∈ (p.coeff b).support,
        shiftBi x0 y0 (Polynomial.monomial b (Polynomial.monomial a ((p.coeff b).coeff a))) := by
    unfold shiftBi; simp only [Polynomial.map_sum, Polynomial.sum_comp]
  rw [hsh_sum, finset_sum_coeff, finset_sum_coeff] at hnz
  obtain ⟨b, _, hbnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  rw [finset_sum_coeff, finset_sum_coeff] at hbnz
  obtain ⟨a, ha, hanz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hbnz
  have hpar := hp b a (Polynomial.mem_support_iff.mp ha)
  have hb2 : b = 2 * (b / 2) := by omega
  have ha2 : a = 2 * (a / 2) := by omega
  rw [hb2, ha2] at hanz
  exact hsh_monom _ (a / 2) (b / 2) j i hanz

private lemma shiftBi_zero_zero {F : Type*} [Field F] (p : BiPoly F) :
    shiftBi (0 : F) 0 p = p := by
  unfold shiftBi
  have hcomp : Polynomial.compRingHom (C (0 : F) + X) = RingHom.id (Polynomial F) := by
    ext <;> simp [Polynomial.compRingHom]
  rw [hcomp, Polynomial.map_id, map_zero, map_zero, zero_add, Polynomial.comp_X]

/-- **Table 3 Subcase 2A Local Resultant Divisibility (`kerD2_resY_f0_g_2A_ord`):**
When `g = C qX * gPrim` with `gPrim ∈ F[X^2, Y^2]` dividing `f1, f2`, let `A0` be the even-`Y` part
of `Fpoly.coeff 0` (`f0 = expand 2 A0 + Y * expand 2 C0`). Then for any even `dStarEff = 2 * halfDs`
with `2 * A0.natDegree ≤ dStarEff`, `(Fpoly.coeff 1).natDegree ≤ dStarEff`, and `(Fpoly.coeff 2).natDegree + 2 ≤ dStarEff`:
`(X - C x0) ^ t3Vrf0Ord 3 g.natDegree dStarEff k (biMult x0 y0 g) ∣ g.leadingCoeff ^ (dStarEff - 2 * A0.natDegree) * Res_Y(expand 2 A0, g)`! -/
theorem kerD2_resY_f0_g_2A_ord {F : Type*} [Field F] [CharP F 2] {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 y0 : F) (f_coord : KerDIdx wY W_F 2 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k)
    (qX : Polynomial F) (gPrim A0 : BiPoly F)
    (hqX_ne : qX ≠ 0) (hgP_ne : gPrim ≠ 0)
    (hgP_X2Y2 : ∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0)
    (hA0_c : ∀ j, A0.coeff j = ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).coeff (2 * j))
    (hdvd1 : gPrim ∣ (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1)
    (hdvd2 : gPrim ∣ (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2)
    (dStarEff : ℕ) (hds_ev : dStarEff % 2 = 0)
    (hA0_d : 2 * A0.natDegree ≤ dStarEff)
    (hf1_d : ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree ≤ dStarEff)
    (hf2_d : ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2).natDegree + 2 ≤ dStarEff) :
    let g : BiPoly F := C qX * gPrim
    let dg := g.natDegree
    let dA := (Polynomial.expand (Polynomial F) 2 A0).natDegree
    (X - C x0) ^ t3Vrf0Ord 3 dg dStarEff k (biMult x0 y0 g) ∣
      g.leadingCoeff ^ (dStarEff - dA) *
        Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) g dA dg := by
  intro g dg dA
  by_cases hk0 : k = 0
  · subst hk0; simp [t3Vrf0Ord]
  set Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
  set rr : ℕ := biMult x0 y0 g
  set rq : ℕ := biMult x0 y0 (C qX)
  set rre : ℕ := biMult x0 y0 gPrim
  have hrr_eq : rr = rq + rre := biMult_mul x0 y0 (Polynomial.C_ne_zero.mpr hqX_ne) hgP_ne
  have hrre_ev : rre % 2 = 0 := biMult_even_of_in_X2_Y2 x0 y0 gPrim hgP_X2Y2
  have hdg_eq : dg = gPrim.natDegree := by
    dsimp [dg, g]; rw [Polynomial.natDegree_C_mul hqX_ne]
  have hdA_eq : dA = 2 * A0.natDegree := by
    dsimp [dA]; rw [Polynomial.natDegree_expand, mul_comm]
  have hfold_le_mem : ∀ (l : List ℕ) (f : ℕ → ℕ) (init x : ℕ), x ∈ l →
      l.foldl (fun acc y => Nat.min acc (f y)) init ≤ f x := by
    intro l f; induction l with
    | nil => intro _ _ hx; cases hx
    | cons a t ih =>
        intro init x hx; simp only [List.foldl_cons, List.mem_cons] at hx ⊢
        rcases hx with rfl | ht
        · have hle : ∀ (l' : List ℕ) (z : ℕ), l'.foldl (fun acc y => Nat.min acc (f y)) z ≤ z := by
            intro l'; induction l' with
            | nil => intro _; exact le_rfl
            | cons b bs ih' => intro z; simp only [List.foldl_cons]; exact (ih' _).trans (Nat.min_le_left _ _)
          exact (hle t _).trans (Nat.min_le_right _ _)
        · exact ih _ x ht
  have hrq_mem : rq ∈ (List.range (rr + 1)).filter (fun q => (rr - q) % 2 == 0) := by
    rw [List.mem_filter]; refine ⟨List.mem_range.mpr (by omega), ?_⟩
    simp only [beq_iff_eq, show rr - rq = rre by omega]; exact hrre_ev
  have hk0b : (k == 0) = false := beq_false_of_ne hk0
  have hle_evalRq : t3Vrf0Ord 3 dg dStarEff k rr ≤
      max ((2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2 - 2 * dg) + dStarEff * rq)
        (((List.range (dStarEff + 1)).map (fun d0 =>
          resOrdExact d0 (2 * k - 2) dg rre + (dStarEff - d0) * (rre - dg))).foldl Nat.min
            (resOrdExact 0 (2 * k - 2) dg rre + dStarEff * (rre - dg)) + dStarEff * rq) := by
    unfold t3Vrf0Ord; simp only [hk0b, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, resOrdWeighted2Fast_eq]
    let evalRqFn : ℕ → ℕ := fun q =>
      max ((2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) (rr - q) 2 - 2 * dg) + dStarEff * q)
        (((List.range (dStarEff + 1)).map (fun d0 =>
          resOrdExact d0 (2 * k - 2) dg (rr - q) + (dStarEff - d0) * ((rr - q) - dg))).foldl Nat.min
            (resOrdExact 0 (2 * k - 2) dg (rr - q) + dStarEff * ((rr - q) - dg)) + dStarEff * q)
    have h := hfold_le_mem ((List.range (rr + 1)).filter (fun q => (rr - q) % 2 == 0))
      evalRqFn (evalRqFn rr) rq hrq_mem
    simpa only [evalRqFn, show rr - rq = rre by omega] using h
  refine (pow_dvd_pow (X - C x0) hle_evalRq).trans ?_
  have hfac_q : g.leadingCoeff ^ (dStarEff - dA) *
      Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) g dA dg =
      qX ^ dStarEff * (gPrim.leadingCoeff ^ (dStarEff - dA) *
        Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg) := by
    have hlc_g : g.leadingCoeff = qX * gPrim.leadingCoeff := by
      dsimp [g]; rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    have hres_g : Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) g dA dg =
        qX ^ dA * Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg := by
      dsimp [g]; rw [Polynomial.resultant_C_mul_right]
    rw [hlc_g, mul_pow, hres_g]
    have hsum_d : (dStarEff - dA) + dA = dStarEff := by omega
    calc qX ^ (dStarEff - dA) * gPrim.leadingCoeff ^ (dStarEff - dA) *
          (qX ^ dA * Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg)
        = (qX ^ (dStarEff - dA) * qX ^ dA) * (gPrim.leadingCoeff ^ (dStarEff - dA) *
            Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg) := by ring
      _ = _ := by rw [← pow_add, hsum_d]
  rw [hfac_q]
  have hqX_dvd : (X - C x0) ^ (dStarEff * rq) ∣ qX ^ dStarEff := by
    have h1 := pow_dvd_leadingCoeff_of_biMultGE x0 y0 (C qX) 0 rq (Polynomial.natDegree_C qX) (biMultGE_biMult x0 y0 (C qX))
    simp only [Nat.sub_zero, Polynomial.leadingCoeff_C] at h1
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h1 dStarEff
  -- Shared setup for BOTH Branch 1 and Branch 2:
  -- Express Fpoly.coeff 0, 1, 2 explicitly from kerDBasisPoly to extract C0 = dXBi(f1) and parities!
  have hf_terms :
      (Fpoly.coeff 0 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 0 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0) ∧
      (Fpoly.coeff 1 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 1 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 1 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0) ∧
      (Fpoly.coeff 2 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 2 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 1 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0) := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · dsimp [Fpoly]; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
      rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      · simp only [true_and, false_and, and_false, zero_ne_one, one_ne_zero,
          show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, show (0:ℕ) ≠ 2 by omega, show (1:ℕ) ≠ 2 by omega, ↓reduceIte]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        first
        | (rw [pow_zero, pow_zero, one_mul, one_mul,
            show C (C (C (f_coord ⟨(0,0,b1,a1),he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(0,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
            Polynomial.coeff_C]; simp)
        | (rw [pow_one, pow_zero, mul_one,
            show C (C (C (f_coord ⟨(1,0,b1,a1),he⟩))) * (X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              X * C (C (C (f_coord ⟨(1,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring];
            first | exact Polynomial.coeff_X_mul_zero _ | (rw [Polynomial.coeff_X_mul, Polynomial.coeff_C]; simp))
        | (rw [pow_zero, mul_one, sq,
            show C (C (C (f_coord ⟨(2,0,b1,a1),he⟩))) * (X * X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              X * (X * C (C (C (f_coord ⟨(2,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)) by simp only [map_mul, map_pow]; ring];
            first | exact Polynomial.coeff_X_mul_zero _
                  | (rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero])
                  | (rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul, Polynomial.coeff_C]; simp))
        | (rw [pow_zero, pow_one, one_mul,
            show C (C (C (f_coord ⟨(0,1,b1,a1),he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
              X * C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow, map_add]; ring,
            Polynomial.coeff_add, Polynomial.coeff_C];
            simp only [Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul, Polynomial.coeff_C,
              one_ne_zero, zero_ne_one, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, ↓reduceIte,
              add_zero, zero_add])
        | (rw [pow_one, pow_one,
            show C (C (C (f_coord ⟨(1,1,b1,a1),he⟩))) * (X * (C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              X * C (C (C (f_coord ⟨(1,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
              X * (X * C (C (C (f_coord ⟨(1,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)) by simp only [map_mul, map_pow, map_add]; ring,
            Polynomial.coeff_add];
            simp only [Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul, Polynomial.coeff_C,
              one_ne_zero, zero_ne_one, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, ↓reduceIte,
              add_zero, zero_add])
  -- Define C0_exp = dXBi (Fpoly.coeff 1) and C1_exp = odd-Y part of Fpoly.coeff 1 = dXBi (Fpoly.coeff 2)!
  set C0_exp : BiPoly F := dXBi (Fpoly.coeff 1)
  have hC0_sum : C0_exp = ∑ e : KerDIdx wY W_F 2,
      if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0 := by
    have hmon_xev : ∀ (c : F) (a1 b1 : ℕ), dXBi (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) = 0 := by
      intro c a1 b1; apply dXBi_eq_zero_of_xev; intro j i hi
      rw [show C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C (C c * X ^ (2 * a1)) * X ^ (2 * b1) by
        simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      · simp
    have hmon_Y_xev : ∀ (c : F) (a1 b1 : ℕ), dXBi (C (C c) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) = 0 := by
      intro c a1 b1; apply dXBi_eq_zero_of_xev; intro j i hi
      rw [show C (C c) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C (C c * X ^ (2 * a1)) * X ^ (2 * b1 + 1) by
        simp only [map_mul, map_pow, ← pow_mul, pow_succ]; ring, Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      · simp
    have hmon_X_dX : ∀ (c : F) (a1 b1 : ℕ),
        dXBi (C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) =
          C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 := by
      intro c a1 b1
      rw [show C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C X * (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by ring,
        dXBi_mul, hmon_xev, mul_zero, add_zero]
      have hdCX : dXBi (C X : BiPoly F) = 1 := by
        rw [Polynomial.ext_iff]; intro j; rw [coeff_dXBi, Polynomial.coeff_C, Polynomial.coeff_one]; split_ifs <;> simp
      rw [hdCX, one_mul]
    rw [Polynomial.ext_iff]; intro j; rw [coeff_dXBi, hf_terms.2.1, finset_sum_coeff, map_sum, finset_sum_coeff]
    apply Finset.sum_congr rfl; intro e _
    by_cases h1 : e.1.1 = 1 ∧ e.1.2.1 = 0
    · rw [if_pos h1, if_neg (by omega), ← coeff_dXBi, hmon_xev, Polynomial.coeff_zero]
    · rw [if_neg h1]
      by_cases h2 : e.1.1 = 0 ∧ e.1.2.1 = 1
      · rw [if_pos h2, if_pos h2, ← coeff_dXBi, hmon_X_dX]
      · rw [if_neg h2, if_neg h2]
        by_cases h3 : e.1.1 = 1 ∧ e.1.2.1 = 1
        · rw [if_pos h3, ← coeff_dXBi, hmon_Y_xev, Polynomial.coeff_zero]
        · rw [if_neg h3, Polynomial.coeff_zero, Polynomial.derivative_zero]
  have hf0_decomp : Fpoly.coeff 0 = Polynomial.expand (Polynomial F) 2 A0 + X * C0_exp := by
    have hA0_sum : Polynomial.expand (Polynomial F) 2 A0 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 0 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0 := by
      rw [Polynomial.ext_iff]; intro j; rw [Polynomial.coeff_expand (by norm_num : 0 < 2)]
      split_ifs with hj
      · rw [hA0_c, show 2 * (j / 2) = j by omega, hf_terms.1, finset_sum_coeff, finset_sum_coeff]
        apply Finset.sum_congr rfl; intro e _
        by_cases he1 : e.1.1 = 0 ∧ e.1.2.1 = 0
        · rw [if_pos he1, if_pos he1]
        · rw [if_neg he1, if_neg he1]
          by_cases he2 : e.1.1 = 0 ∧ e.1.2.1 = 1
          · rw [if_pos he2,
              show C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
                C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1 + 1) by
                simp only [map_mul, map_pow, ← pow_mul, pow_succ]; ring,
              Polynomial.coeff_C_mul_X_pow, if_neg (by omega), Polynomial.coeff_zero]
          · rw [if_neg he2]
      · symm; rw [finset_sum_coeff]; apply Finset.sum_eq_zero; intro e _
        split_ifs
        · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
              C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
              simp only [map_mul, map_pow, ← pow_mul],
            Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
        · simp
    rw [hf_terms.1, hA0_sum, hC0_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    by_cases h1 : e.1.1 = 0 ∧ e.1.2.1 = 0
    · rw [if_pos h1, if_pos h1, if_neg (by omega), mul_zero, add_zero]
    · rw [if_neg h1, if_neg h1, zero_add]
      by_cases h2 : e.1.1 = 0 ∧ e.1.2.1 = 1
      · rw [if_pos h2, if_pos h2]; ring
      · rw [if_neg h2, if_neg h2, mul_zero]
  have hdvd_C0 : gPrim ∣ C0_exp := by
    rcases hdvd1 with ⟨q1, hq1⟩
    refine ⟨dXBi q1, ?_⟩
    dsimp [C0_exp]; rw [hq1, dXBi_mul, dXBi_eq_zero_of_xev gPrim (fun j i hi => by
      by_contra hnz; have := hgP_X2Y2 j i hnz; omega), zero_mul, zero_add]
  have hC0_deg : C0_exp.natDegree ≤ dStarEff := (natDegree_dXBi_le (Fpoly.coeff 1)).trans hf1_d
  have hA0_X2Y2 : ∀ j i, ((Polynomial.expand (Polynomial F) 2 A0).coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro j i hnz
    rw [Polynomial.coeff_expand (by norm_num : 0 < 2)] at hnz
    split_ifs at hnz with hj
    · rw [hA0_c, hf_terms.1, finset_sum_coeff, finset_sum_coeff] at hnz
      obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      split_ifs at henz
      · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
            C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
            simp only [map_mul, map_pow, ← pow_mul],
          Polynomial.coeff_C_mul_X_pow] at henz
        split_ifs at henz
        · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
        · simp at henz
      · rw [show C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
            C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1 + 1) by
            simp only [map_mul, map_pow, ← pow_mul, pow_succ]; ring,
          Polynomial.coeff_C_mul_X_pow, if_neg (by omega)] at henz; simp at henz
      · simp at henz
    · simp at hnz
  have hC0_X2Y2 : ∀ j i, (C0_exp.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro j i hnz
    rw [hC0_sum, finset_sum_coeff, finset_sum_coeff] at hnz
    obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    split_ifs at henz
    · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
          C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
          simp only [map_mul, map_pow, ← pow_mul],
        Polynomial.coeff_C_mul_X_pow] at henz
      split_ifs at henz
      · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
      · simp at henz
    · simp at henz
  -- Define A0_sh_eff = even-t part of shiftBi x0 y0 (Fpoly.coeff 0)!
  set A0_sh_eff : BiPoly F :=
    shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0) + C (C y0) * shiftBi x0 y0 C0_exp
  have hsh0_split : shiftBi x0 y0 (Fpoly.coeff 0) = A0_sh_eff + X * shiftBi x0 y0 C0_exp := by
    dsimp [A0_sh_eff]; rw [hf0_decomp, shiftBi_add, shiftBi_mul, shiftBi_X]; ring
  have hA0sh_X2Y2 : ∀ j i, (A0_sh_eff.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro j i hnz
    dsimp [A0_sh_eff] at hnz
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul] at hnz
    by_cases h1 : ((shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0)).coeff j).coeff i ≠ 0
    · exact shiftBi_in_X2_Y2 x0 y0 _ hA0_X2Y2 j i h1
    · push Not at h1; rw [h1, zero_add] at hnz
      exact shiftBi_in_X2_Y2 x0 y0 _ hC0_X2Y2 j i (right_ne_zero_of_mul hnz)
  have hsh_deg_le : ∀ p : BiPoly F, (shiftBi x0 y0 p).natDegree ≤ p.natDegree := by
    intro p; unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
    have hm : (p.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ p.natDegree := Polynomial.natDegree_map_le
    have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
      (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
    nlinarith only [hm, hX]
  have hshg_deg : (shiftBi x0 y0 gPrim).natDegree = dg := by
    rw [hdg_eq]; unfold shiftBi
    have hinj : Function.Injective (Polynomial.compRingHom (C x0 + X) : Polynomial F →+* Polynomial F) := by
      intro p q hpq; have := congrArg (fun r => r.comp (X - C x0)) hpq
      simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.comp_X] using this
    have h1 : (gPrim.map (Polynomial.compRingHom (C x0 + X))).natDegree = gPrim.natDegree :=
      Polynomial.natDegree_map_eq_of_injective hinj _
    have hcomp : ∀ (p : BiPoly F) (c : Polynomial F), (p.comp (C c + X)).natDegree = p.natDegree := by
      intro p c; apply le_antisymm
      · refine Polynomial.natDegree_comp_le.trans ?_
        have h2 : (C c + X : BiPoly F).natDegree ≤ 1 :=
          (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
        nlinarith only [h2]
      · have hb : ((p.comp (C c + X)).comp (C (-c) + X)).natDegree = p.natDegree := by
          rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
            show C c + (C (-c) + X) = X by rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add],
            Polynomial.comp_X]
        rw [← hb]; refine Polynomial.natDegree_comp_le.trans ?_
        have h2 : (C (-c) + X : BiPoly F).natDegree ≤ 1 :=
          (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
        nlinarith only [h2]
    rw [hcomp, h1]
  have hlc_sh : (shiftBi x0 y0 gPrim).leadingCoeff = gPrim.leadingCoeff.comp (C x0 + X) := by
    rw [Polynomial.leadingCoeff, hshg_deg]; unfold shiftBi
    have hmap_deg : (gPrim.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ dg := by
      rw [hdg_eq]; exact Polynomial.natDegree_map_le
    rw [coeff_comp_C_add_X_top y0 _ dg hmap_deg, Polynomial.coeff_map, Polynomial.leadingCoeff, hdg_eq]; rfl
  have hA0sh_deg : A0_sh_eff.natDegree ≤ dStarEff := by
    dsimp [A0_sh_eff]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (hsh_deg_le _).trans (by omega)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans ((hsh_deg_le _).trans hC0_deg)
  -- Key resultant invariance: Res_t(A0_sh_eff, shiftBi gPrim; dStarEff, dg) = (shiftBi gPrim).lc^(dStarEff - dA) * Res_t(shiftBi(expand 2 A0), shiftBi gPrim; dA, dg)!
  have hres_eff : Polynomial.resultant A0_sh_eff (shiftBi x0 y0 gPrim) dStarEff dg =
      (gPrim.leadingCoeff ^ (dStarEff - dA) *
        Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg).comp (C x0 + X) := by
    rcases hdvd_C0 with ⟨qC, hqC⟩
    have hA0_mod : A0_sh_eff = shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0) +
        (C (C y0) * shiftBi x0 y0 qC) * shiftBi x0 y0 gPrim := by
      dsimp [A0_sh_eff]; rw [hqC, shiftBi_mul]; ring
    have hdeg_shA : (shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0)).natDegree ≤ dStarEff :=
      (hsh_deg_le _).trans (by omega)
    have hneg1 : (-1 : Polynomial F) = 1 := CharTwo.neg_eq 1
    conv_lhs => rw [hA0_mod,
      resultant_add_mul_right_deg _ _ _ dStarEff dg hdeg_shA (by rwa [← hA0_mod]) hshg_deg,
      show dStarEff = dA + (dStarEff - dA) by omega,
      Polynomial.resultant_add_left_deg _ _ dA dg (dStarEff - dA) (hsh_deg_le _),
      show (shiftBi x0 y0 gPrim).coeff dg = (shiftBi x0 y0 gPrim).leadingCoeff by rw [Polynomial.leadingCoeff, hshg_deg],
      hlc_sh, resultant_shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg le_rfl (le_of_eq hdg_eq.symm),
      hneg1, one_pow, one_mul, ← Polynomial.pow_comp, ← Polynomial.mul_comp]
  have hdvd_max : ∀ (a b : ℕ) (R : Polynomial F),
      (X - C x0) ^ a ∣ R → (X - C x0) ^ b ∣ R → (X - C x0) ^ max a b ∣ R := by
    intro a b R ha hb; rcases le_total a b with h | h
    · rwa [Nat.max_eq_right h]
    · rwa [Nat.max_eq_left h]
  obtain ⟨hbm0, _, _, Pe, Po, hdecomp, _, _, hPe_ord, _, _⟩ := kerD2_local_ords hwY x0 y0 f_coord hvan
  apply hdvd_max
  · -- Branch 1: vk_part + dStarEff * rq!
    rw [add_comm, pow_add]; apply mul_dvd_mul hqX_dvd
    apply X_sub_C_pow_dvd_of_comp_shift x0 _ _
    rw [← hres_eff]
    -- Write A0_sh_eff = expand 2 A0_loc and shiftBi gPrim = expand 2 g1!
    obtain ⟨A0_loc, hA0_loc_eq, hA0_loc_deg, hA0_loc_c⟩ :=
      exists_expand2_of_even_Y A0_sh_eff (fun j hj => by ext i; by_contra hnz; have := hA0sh_X2Y2 j i hnz; omega)
    have hgP_sh_X2Y2 := shiftBi_in_X2_Y2 x0 y0 gPrim hgP_X2Y2
    obtain ⟨g1, hg1_eq, _, hg1_c⟩ :=
      exists_expand2_of_even_Y (shiftBi x0 y0 gPrim) (fun j hj => by ext i; by_contra hnz; have := hgP_sh_X2Y2 j i hnz; omega)
    have hdg_ev : dg % 2 = 0 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hg1_eq, hshg_deg] at h2; omega
    have hg1_deg : g1.natDegree = dg / 2 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hg1_eq, hshg_deg] at h2; omega
    have hg1_ord : weightedOrdGE 2 rre g1 := by
      intro j; rw [hg1_c j]
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 gPrim rre).mp (biMultGE_biMult x0 y0 gPrim) (2 * j)
    -- Construct A2_loc = evenPartX of the even-t coefficients of shiftBi f2, and prove g1 ∣ A2_loc!
    have hf2_evY : ∀ j, j % 2 = 1 → (Fpoly.coeff 2).coeff j = 0 := by
      intro j hj; rw [hf_terms.2.2, finset_sum_coeff]
      apply Finset.sum_eq_zero; intro e _; split_ifs
      · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
            C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
            simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      · rw [show C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
            C (C (f_coord e) * X * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
            simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      · simp
    have hshf2_evY : ∀ j, j % 2 = 1 → (shiftBi x0 y0 (Fpoly.coeff 2)).coeff j = 0 := by
      obtain ⟨f2h, hf2h_eq, _, _⟩ := exists_expand2_of_even_Y (Fpoly.coeff 2) hf2_evY
      have hsh_exp : shiftBi x0 y0 (Fpoly.coeff 2) =
          Polynomial.expand (Polynomial F) 2
            ((f2h.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)) := by
        rw [hf2h_eq, shiftBi_expand2]
      intro j hj; rw [hsh_exp, Polynomial.coeff_expand (by norm_num : 0 < 2), if_neg (by omega)]
    obtain ⟨f2_loc, hf2_loc_eq, _, hf2_loc_c⟩ := exists_expand2_of_even_Y (shiftBi x0 y0 (Fpoly.coeff 2)) hshf2_evY
    set A2_loc : BiPoly F := ∑ j ∈ f2_loc.support, Polynomial.monomial j (evenPartX (f2_loc.coeff j))
    have hA2_loc_c : ∀ j, A2_loc.coeff j = evenPartX (f2_loc.coeff j) := by
      intro j; dsimp [A2_loc]; rw [finset_sum_coeff]
      by_cases hj : j ∈ f2_loc.support
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hne; simp [Polynomial.coeff_monomial, hne]
        · intro h; exact absurd hj h
      · rw [Finset.sum_eq_zero, Polynomial.notMem_support_iff.mp hj]
        · ext n; rw [coeff_evenPartX]; split_ifs <;> simp
        · intro k hk; simp [Polynomial.coeff_monomial, show k ≠ j by intro heq; subst heq; exact hj hk]
    have hg1_dvd_A2 : g1 ∣ A2_loc := by
      rcases hdvd2 with ⟨h2, hh2⟩
      have hsh2_eq : shiftBi x0 y0 (Fpoly.coeff 2) = shiftBi x0 y0 gPrim * shiftBi x0 y0 h2 := by
        rw [hh2, shiftBi_mul]
      -- Show shiftBi h2 also has only even Y-powers (since shiftBi gPrim ≠ 0 and shiftBi f2 have only even Y-powers)!
      have hshh2_ev : ∀ j, j % 2 = 1 → (shiftBi x0 y0 h2).coeff j = 0 := by
        by_contra hne; push Not at hne
        let oddS := (shiftBi x0 y0 h2).support.filter fun j => j % 2 = 1
        have hodd_ne : oddS.Nonempty := by
          obtain ⟨j, hj1, hj2⟩ := hne
          exact ⟨j, Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr hj2, hj1⟩⟩
        let jm := oddS.max' hodd_ne
        have hjm_m := Finset.mem_filter.mp (Finset.max'_mem oddS hodd_ne)
        have hjm_nz : (shiftBi x0 y0 h2).coeff jm ≠ 0 := Polynomial.mem_support_iff.mp hjm_m.1
        have hjm_odd : jm % 2 = 1 := hjm_m.2
        have hprod_nz : (shiftBi x0 y0 gPrim * shiftBi x0 y0 h2).coeff (dg + jm) ≠ 0 := by
          rw [Polynomial.coeff_mul, Finset.sum_eq_single (dg, jm)]
          have hlc : (shiftBi x0 y0 gPrim).coeff dg ≠ 0 := by
            rw [← hshg_deg]; exact Polynomial.leadingCoeff_ne_zero.mpr
              (fun h => hgP_ne ((shiftBi_eq_zero_iff x0 y0 gPrim).mp h))
          exact mul_ne_zero hlc hjm_nz
          · intro ⟨a, b⟩ hab hneq
            have hsum : a + b = dg + jm := Finset.mem_antidiagonal.mp hab
            by_cases ha : dg < a
            · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            · by_cases ha_odd : a % 2 = 1
              · have : (shiftBi x0 y0 gPrim).coeff a = 0 := by
                  ext i; by_contra hnz; have := hgP_sh_X2Y2 a i hnz; omega
                rw [this, zero_mul]
              · have hb_gt : jm < b := by by_contra hle; apply hneq; ext <;> dsimp <;> omega
                have hb_odd : b % 2 = 1 := by omega
                have hb_z : (shiftBi x0 y0 h2).coeff b = 0 := by
                  by_contra hbnz
                  have hbm : b ∈ oddS := Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr hbnz, hb_odd⟩
                  have := Finset.le_max' oddS b hbm; omega
                rw [hb_z, mul_zero]
          · intro h; simp at h
        rw [← hsh2_eq] at hprod_nz
        exact hprod_nz (hshf2_evY (dg + jm) (by omega))
      obtain ⟨h2_loc, hh2_loc_eq, _, _⟩ := exists_expand2_of_even_Y (shiftBi x0 y0 h2) hshh2_ev
      have hf2_fac : f2_loc = g1 * h2_loc := by
        have h1 : Polynomial.expand (Polynomial F) 2 f2_loc = Polynomial.expand (Polynomial F) 2 (g1 * h2_loc) := by
          rw [map_mul, ← hf2_loc_eq, ← hg1_eq, ← hh2_loc_eq, hsh2_eq]
        rw [Polynomial.ext_iff]; intro j
        have := congrArg (fun p : BiPoly F => p.coeff (2 * j)) h1
        simp only [Polynomial.coeff_expand (by norm_num : 0 < 2), dvd_mul_right, ↓reduceIte,
          Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at this
        exact this
      refine ⟨∑ j ∈ h2_loc.support, Polynomial.monomial j (evenPartX (h2_loc.coeff j)), ?_⟩
      rw [Polynomial.ext_iff]; intro j
      rw [hA2_loc_c, hf2_fac, Polynomial.coeff_mul, Polynomial.coeff_mul]
      have hlin : ∀ (S : Finset (ℕ × ℕ)) (fn : ℕ × ℕ → Polynomial F),
          evenPartX (∑ x ∈ S, fn x) = ∑ x ∈ S, evenPartX (fn x) := by
        intro S fn; ext n; rw [coeff_evenPartX, finset_sum_coeff, finset_sum_coeff]
        split_ifs with hn
        · apply Finset.sum_congr rfl; intro x _; rw [coeff_evenPartX, if_pos hn]
        · symm; apply Finset.sum_eq_zero; intro x _; rw [coeff_evenPartX, if_neg hn]
      rw [hlin]
      apply Finset.sum_congr rfl; intro ⟨a, b⟩ _
      have hg1_xev : ∀ i, i % 2 = 1 → (g1.coeff a).coeff i = 0 := fun i hi => by
        rw [hg1_c a]; by_contra hnz; have := hgP_sh_X2Y2 (2 * a) i hnz; omega
      rw [evenPartX_mul_of_xev _ _ hg1_xev]
      congr 1; rw [finset_sum_coeff]
      by_cases hb : b ∈ h2_loc.support
      · rw [Finset.sum_eq_single b]
        · simp
        · intro k _ hne; simp [Polynomial.coeff_monomial, hne]
        · intro h; exact absurd hb h
      · rw [Finset.sum_eq_zero, Polynomial.notMem_support_iff.mp hb]
        · ext n; rw [coeff_evenPartX]; split_ifs <;> simp
        · intro k hk; simp [Polynomial.coeff_monomial, show k ≠ b by intro heq; subst heq; exact hb hk]
    -- Prove the EXACT identity Pe = C (X^2) * A0_loc + X * A2_loc directly from hdecomp!
    have hPe_exact : Pe = C (X ^ 2) * A0_loc + X * A2_loc := by
      -- First prove the char-2 cancellation between odd-Y of f1 and odd-X of f2!
      set C1_exp : BiPoly F := dXBi (Fpoly.coeff 2)
      have hC1_sum : C1_exp = ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 1 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0 := by
        have hmon_xev : ∀ (c : F) (a1 b1 : ℕ), dXBi (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) = 0 := by
          intro c a1 b1; apply dXBi_eq_zero_of_xev; intro j i hi
          rw [show C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C (C c * X ^ (2 * a1)) * X ^ (2 * b1) by
            simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow]
          split_ifs; · rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
          · simp
        have hmon_X_dX : ∀ (c : F) (a1 b1 : ℕ),
            dXBi (C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) =
              C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 := by
          intro c a1 b1
          rw [show C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C X * (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by ring,
            dXBi_mul, hmon_xev, mul_zero, add_zero]
          have hdCX : dXBi (C X : BiPoly F) = 1 := by
            rw [Polynomial.ext_iff]; intro j; rw [coeff_dXBi, Polynomial.coeff_C, Polynomial.coeff_one]; split_ifs <;> simp
          rw [hdCX, one_mul]
        rw [Polynomial.ext_iff]; intro j; rw [coeff_dXBi, hf_terms.2.2, finset_sum_coeff, map_sum, finset_sum_coeff]
        apply Finset.sum_congr rfl; intro e _
        by_cases h1 : e.1.1 = 2 ∧ e.1.2.1 = 0
        · rw [if_pos h1, if_neg (by omega), ← coeff_dXBi, hmon_xev, Polynomial.coeff_zero]
        · rw [if_neg h1]
          by_cases h2 : e.1.1 = 1 ∧ e.1.2.1 = 1
          · rw [if_pos h2, if_pos h2, ← coeff_dXBi, hmon_X_dX]
          · rw [if_neg h2, if_neg h2, Polynomial.coeff_zero, Polynomial.derivative_zero]
      have hC1_X2Y2 : ∀ j i, (C1_exp.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
        intro j i hnz
        rw [hC1_sum, finset_sum_coeff, finset_sum_coeff] at hnz
        obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
        split_ifs at henz
        · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
              C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
              simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow] at henz
          split_ifs at henz
          · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
          · simp at henz
        · simp at henz
      have hshC1_X2Y2 := shiftBi_in_X2_Y2 x0 y0 C1_exp hC1_X2Y2
      -- Odd-t part of shiftBi f1 = shiftBi C1_exp, and odd-s part of shiftBi f2 = shiftBi C1_exp!
      have hf1_odd_t : ∀ j i, ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (2 * j + 1)).coeff i =
          ((shiftBi x0 y0 C1_exp).coeff (2 * j)).coeff i := by
        intro j i
        set A1_sum : BiPoly F := ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 1 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0
        have hf1_sp : Fpoly.coeff 1 = A1_sum + C X * C0_exp + X * C1_exp := by
          rw [hf_terms.2.1, hC0_sum, hC1_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e _
          by_cases h1 : e.1.1 = 1 ∧ e.1.2.1 = 0
          · rw [if_pos h1, if_pos h1, if_neg (by omega), if_neg (by omega), mul_zero, mul_zero, add_zero, add_zero]
          · rw [if_neg h1, if_neg h1, zero_add]
            by_cases h2 : e.1.1 = 0 ∧ e.1.2.1 = 1
            · rw [if_pos h2, if_pos h2, if_neg (by omega), mul_zero, add_zero]; ring
            · rw [if_neg h2, if_neg h2, mul_zero, zero_add]
              by_cases h3 : e.1.1 = 1 ∧ e.1.2.1 = 1
              · rw [if_pos h3, if_pos h3]; ring
              · rw [if_neg h3, if_neg h3, mul_zero]
        have hA1_X2Y2 : ∀ j' i', (A1_sum.coeff j').coeff i' ≠ 0 → i' % 2 = 0 ∧ j' % 2 = 0 := by
          intro j' i' hnz
          rw [finset_sum_coeff, finset_sum_coeff] at hnz
          obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
          split_ifs at henz
          · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
                C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
                simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow] at henz
            split_ifs at henz
            · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
            · simp at henz
          · simp at henz
        rw [hf1_sp, shiftBi_add, shiftBi_add, shiftBi_mul, shiftBi_mul, shiftBi_C, Polynomial.X_comp, shiftBi_X,
          add_mul (C (C y0))]
        have hz1 : (shiftBi x0 y0 A1_sum).coeff (2 * j + 1) = 0 := by
          ext i'; by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 A1_sum hA1_X2Y2 (2 * j + 1) i' hnz; omega
        have hz2 : (shiftBi x0 y0 C0_exp).coeff (2 * j + 1) = 0 := by
          ext i'; by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 C0_exp hC0_X2Y2 (2 * j + 1) i' hnz; omega
        have hz3 : (shiftBi x0 y0 C1_exp).coeff (2 * j + 1) = 0 := by
          ext i'; by_contra hnz; have := hshC1_X2Y2 (2 * j + 1) i' hnz; omega
        simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
          hz1, hz2, hz3, mul_zero, zero_add, Polynomial.coeff_zero]
      have hf2_odd_s : ∀ j i, ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff (2 * j)).coeff (2 * i + 1) =
          ((shiftBi x0 y0 C1_exp).coeff (2 * j)).coeff (2 * i) := by
        intro j i
        set A2_sum : BiPoly F := ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 2 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0
        have hf2_sp : Fpoly.coeff 2 = A2_sum + C X * C1_exp := by
          rw [hf_terms.2.2, hC1_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e _
          by_cases h1 : e.1.1 = 2 ∧ e.1.2.1 = 0
          · rw [if_pos h1, if_pos h1, if_neg (by omega), mul_zero, add_zero]
          · rw [if_neg h1, if_neg h1, zero_add]
            by_cases h2 : e.1.1 = 1 ∧ e.1.2.1 = 1
            · rw [if_pos h2, if_pos h2]; ring
            · rw [if_neg h2, if_neg h2, mul_zero]
        have hA2_X2Y2 : ∀ j' i', (A2_sum.coeff j').coeff i' ≠ 0 → i' % 2 = 0 ∧ j' % 2 = 0 := by
          intro j' i' hnz
          rw [finset_sum_coeff, finset_sum_coeff] at hnz
          obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
          split_ifs at henz
          · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
                C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
                simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow] at henz
            split_ifs at henz
            · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
            · simp at henz
          · simp at henz
        rw [hf2_sp, shiftBi_add, shiftBi_mul, shiftBi_C, Polynomial.X_comp, Polynomial.coeff_add,
          Polynomial.coeff_C_mul, add_mul, Polynomial.coeff_add, Polynomial.coeff_add,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
        have hz1 : ((shiftBi x0 y0 A2_sum).coeff (2 * j)).coeff (2 * i + 1) = 0 := by
          by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 A2_sum hA2_X2Y2 (2 * j) (2 * i + 1) hnz; omega
        have hz2 : ((shiftBi x0 y0 C1_exp).coeff (2 * j)).coeff (2 * i + 1) = 0 := by
          by_contra hnz; have := hshC1_X2Y2 (2 * j) (2 * i + 1) hnz; omega
        rw [hz1, hz2, mul_zero, zero_add, zero_add]
      ext j i
      have hc := congrArg (fun p : BiPoly F => (p.coeff (2 * j)).coeff i) hdecomp
      have hRHS_Pe : ((Polynomial.expand (Polynomial F) 2 Pe + X * Polynomial.expand (Polynomial F) 2 Po).coeff (2 * j)).coeff i =
          (Pe.coeff j).coeff i := by
        rw [Polynomial.coeff_add, Polynomial.coeff_expand (by norm_num : 0 < 2), if_pos ⟨j, rfl⟩,
          Nat.mul_div_cancel_left j (by norm_num)]
        have hXPo : (X * Polynomial.expand (Polynomial F) 2 Po).coeff (2 * j) = 0 := by
          cases j with
          | zero => rw [Polynomial.coeff_X_mul_zero]
          | succ j' => rw [show 2 * (j' + 1) = (2 * j' + 1) + 1 by omega, Polynomial.coeff_X_mul,
              Polynomial.coeff_expand (by norm_num : 0 < 2), if_neg (by omega)]
        rw [hXPo, add_zero]
      rw [hRHS_Pe] at hc
      rw [← hc]
      -- Evaluate LHS at (2 * j, i) vs (C (X^2) * A0_loc + X * A2_loc) at (j, i)!
      have hL1 : ((shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2)).coeff (2 * j)).coeff i =
          ((C (X ^ 2) * A0_loc).coeff j).coeff i := by
        rw [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, mul_comm _ (X ^ 2), Polynomial.coeff_X_pow_mul',
          Polynomial.coeff_X_pow_mul']
        split_ifs with hi2
        · rw [hsh0_split, Polynomial.coeff_add, hA0_loc_c j]
          have hXC0 : (X * shiftBi x0 y0 C0_exp).coeff (2 * j) = 0 := by
            cases j with
            | zero => rw [Polynomial.coeff_X_mul_zero]
            | succ j' =>
                rw [show 2 * (j' + 1) = (2 * j' + 1) + 1 by omega, Polynomial.coeff_X_mul]
                ext i'; by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 C0_exp hC0_X2Y2 (2 * j' + 1) i' hnz; omega
          rw [hXC0, add_zero]
        · rfl
      rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.coeff_add, Polynomial.coeff_add, hL1]
      -- Now match (shiftBi f1 * (C X * X) + shiftBi f2 * X^2) at (2*j, i) with (X * A2_loc) at (j, i)!
      cases j with
      | zero =>
          have hz1 : ((shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X)).coeff 0) = 0 := by
            rw [← mul_assoc, Polynomial.coeff_mul_X_zero]
          have hz2 : ((shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2).coeff 0) = 0 := by
            rw [mul_comm, Polynomial.coeff_X_pow_mul']; simp
          rw [mul_zero, hz1, hz2, Polynomial.coeff_X_mul_zero, Polynomial.coeff_zero, add_zero, add_zero]
      | succ j' =>
          have h1 : ((shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X)).coeff (2 * (j' + 1))).coeff i =
              if i = 0 then 0 else ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (2 * j' + 1)).coeff (i - 1) := by
            rw [← mul_assoc, show 2 * (j' + 1) = (2 * j' + 1) + 1 by omega, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
            cases i with
            | zero => rw [Polynomial.coeff_mul_X_zero]; rfl
            | succ i' => rw [Polynomial.coeff_mul_X]; simp
          have h2 : ((shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2).coeff (2 * (j' + 1))).coeff i =
              ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff (2 * j')).coeff i := by
            rw [mul_comm, Polynomial.coeff_X_pow_mul', if_pos (by omega), show 2 * (j' + 1) - 2 = 2 * j' by omega]
          rw [h1, h2, Polynomial.coeff_X_mul, hA2_loc_c, hf2_loc_c, coeff_evenPartX]
          by_cases hi : i % 2 = 0
          · rw [if_pos hi]
            have hf1_z : (if i = 0 then 0 else ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (2 * j' + 1)).coeff (i - 1)) = 0 := by
              split_ifs with hi0
              · rfl
              · rw [hf1_odd_t]; by_contra hnz; have := hshC1_X2Y2 (2 * j') (i - 1) hnz; omega
            rw [hf1_z, add_zero]
          · rw [if_neg hi, add_zero, if_neg (by omega), hf1_odd_t]
            set m := i / 2
            have hi_eq : i = 2 * m + 1 := by omega
            have hi_sub : i - 1 = 2 * m := by omega
            conv_lhs => rw [hi_sub, hi_eq, hf2_odd_s]
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, ← hi_eq]
    -- Now Pe = C (X^2) * A0_loc + X * A2_loc with g1 ∣ A2_loc! Compute Res_V(Pe, g1; dStarEff/2, dg/2)!
    rcases hg1_dvd_A2 with ⟨q2_loc, hq2_loc⟩
    have hPe_mod : Pe = C (X ^ 2) * A0_loc + (X * q2_loc) * g1 := by
      rw [hPe_exact, hq2_loc]; ring
    have hA0_loc_d : A0_loc.natDegree ≤ dStarEff / 2 := by omega
    have hA2_loc_d : A2_loc.natDegree ≤ (Fpoly.coeff 2).natDegree / 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
      rw [hA2_loc_c, hf2_loc_c]
      have hle := hsh_deg_le (Fpoly.coeff 2)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      ext n; rw [coeff_evenPartX]; split_ifs <;> simp
    have hPe_d : Pe.natDegree ≤ dStarEff / 2 := by
      rw [hPe_exact]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C_mul_le _ _).trans hA0_loc_d
      · refine Polynomial.natDegree_mul_le.trans ?_; rw [Polynomial.natDegree_X]; omega
    have hres_V : Polynomial.resultant Pe g1 (dStarEff / 2) (dg / 2) =
        X ^ dg * Polynomial.resultant A0_loc g1 (dStarEff / 2) (dg / 2) := by
      rw [hPe_mod,
        resultant_add_mul_right_deg _ _ _ (dStarEff / 2) (dg / 2)
          ((Polynomial.natDegree_C_mul_le _ _).trans hA0_loc_d) (by rwa [← hPe_mod]) hg1_deg,
        Polynomial.resultant_C_mul_left,
        ← pow_mul, show 2 * (dg / 2) = dg by omega]
    have hdvd_V : X ^ resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2 ∣
        Polynomial.resultant Pe g1 (dStarEff / 2) (dg / 2) :=
      pow_dvd_resultant_of_weighted_ord X Pe g1 (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2
        hPe_d (le_of_eq hg1_deg) hPe_ord hg1_ord
    -- Square BOTH sides and apply resultant_expand2_even!
    have hdvd_sq : X ^ (2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2) ∣
        X ^ (2 * dg) * Polynomial.resultant A0_sh_eff (shiftBi x0 y0 gPrim) dStarEff dg := by
      have hsq := pow_dvd_pow_of_dvd hdvd_V 2
      rw [← pow_mul, mul_comm _ 2, hres_V, mul_pow, ← pow_mul, mul_comm dg 2] at hsq
      have hexp2 := resultant_expand2_even A0_loc g1 (dStarEff / 2) (dg / 2) hA0_loc_d hg1_deg
      rw [← hA0_loc_eq, ← hg1_eq, show 2 * (dStarEff / 2) = dStarEff by omega,
        show 2 * (dg / 2) = dg by omega] at hexp2
      rwa [← hexp2] at hsq
    by_cases hle : 2 * dg ≤ 2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2
    · have hsplit : (X : Polynomial F) ^ (2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2) =
          (X : Polynomial F) ^ (2 * dg) * (X : Polynomial F) ^ (2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2 - 2 * dg) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      rw [hsplit] at hdvd_sq
      exact (mul_dvd_mul_iff_left (pow_ne_zero (2 * dg) Polynomial.X_ne_zero)).mp hdvd_sq
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle), pow_zero]; exact one_dvd _
  · -- Branch 2: vp_part + dStarEff * rq!
    rw [add_comm, pow_add]; apply mul_dvd_mul hqX_dvd
    apply X_sub_C_pow_dvd_of_comp_shift x0 _ _
    rw [← hres_eff]
    set d0' : ℕ := A0_sh_eff.natDegree
    have hd0'_mem : d0' ∈ List.range (dStarEff + 1) := List.mem_range.mpr (by omega)
    have hmin_le : ((List.range (dStarEff + 1)).map (fun d0 =>
        resOrdExact d0 (2 * k - 2) dg rre + (dStarEff - d0) * (rre - dg))).foldl Nat.min
          (resOrdExact 0 (2 * k - 2) dg rre + dStarEff * (rre - dg)) ≤
        resOrdExact d0' (2 * k - 2) dg rre + (dStarEff - d0') * (rre - dg) := by
      have hfold_map : ∀ (l : List ℕ) (f : ℕ → ℕ) (init : ℕ),
          (l.map f).foldl Nat.min init = l.foldl (fun acc y => Nat.min acc (f y)) init := by
        intro l f; induction l with
        | nil => intro _; rfl
        | cons a t ih => intro init; simp only [List.map_cons, List.foldl_cons]; exact ih _
      rw [hfold_map]
      exact hfold_le_mem (List.range (dStarEff + 1)) _ _ d0' hd0'_mem
    refine (pow_dvd_pow X hmin_le).trans ?_
    have hA0sh_bm : biMultGE (0 : F) 0 A0_sh_eff (2 * k - 2) := by
      intro i j hij; rw [shiftBi_zero_zero]
      by_cases hj : j % 2 = 0
      · have heq := congrArg (fun p : BiPoly F => (p.coeff j).coeff i) hsh0_split
        have hXC0 : (X * shiftBi x0 y0 C0_exp).coeff j = 0 := by
          cases j with
          | zero => rw [Polynomial.coeff_X_mul_zero]
          | succ j' =>
              rw [Polynomial.coeff_X_mul]
              ext i'; by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 C0_exp hC0_X2Y2 j' i' hnz; omega
        rw [Polynomial.coeff_add, hXC0, add_zero] at heq
        rw [← heq]; exact hbm0 i j hij
      · by_contra hnz; have := hA0sh_X2Y2 j i hnz; omega
    have hgPsh_bm : biMultGE (0 : F) 0 (shiftBi x0 y0 gPrim) rre := by
      intro i j hij; rw [shiftBi_zero_zero]; exact biMultGE_biMult x0 y0 gPrim i j hij
    have hres_split : Polynomial.resultant A0_sh_eff (shiftBi x0 y0 gPrim) dStarEff dg =
        (shiftBi x0 y0 gPrim).leadingCoeff ^ (dStarEff - d0') *
          Polynomial.resultant A0_sh_eff (shiftBi x0 y0 gPrim) d0' dg := by
      have hneg1 : (-1 : Polynomial F) = 1 := CharTwo.neg_eq 1
      conv_lhs =>
        rw [show dStarEff = d0' + (dStarEff - d0') by omega,
          Polynomial.resultant_add_left_deg _ _ d0' dg (dStarEff - d0') le_rfl,
          show (shiftBi x0 y0 gPrim).coeff dg = (shiftBi x0 y0 gPrim).leadingCoeff by
            rw [Polynomial.leadingCoeff, hshg_deg],
          hneg1, one_pow, one_mul]
    rw [hres_split, add_comm, pow_add]
    apply mul_dvd_mul
    · have hlc_dvd : X ^ (rre - dg) ∣ (shiftBi x0 y0 gPrim).leadingCoeff := by
        have h1 := pow_dvd_leadingCoeff_of_biMultGE (0 : F) 0 (shiftBi x0 y0 gPrim) dg rre hshg_deg hgPsh_bm
        simpa using h1
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hlc_dvd (dStarEff - d0')
    · have h2 := pow_dvd_resultant_of_biMultGE (0 : F) 0 A0_sh_eff (shiftBi x0 y0 gPrim) d0' (2 * k - 2) dg rre
        hA0sh_bm hgPsh_bm le_rfl (le_of_eq hshg_deg)
      rwa [shiftBi_zero_zero, shiftBi_zero_zero] at h2

end KerDResultants

/-! ### Part 4: Char-2 `ker(D)` PDE Parity, Primitive GCD Decomposition & `2A`/`2B` Dichotomy -/

section KerD2UFD

variable {F : Type*} [Field F] [CharP F 2]

lemma deriv_eq_zero_iff_even_coeffs {A : Type*} [CommRing A] [CharP A 2] (p : Polynomial A) :
    p.derivative = 0 ↔ ∀ j, j % 2 = 1 → p.coeff j = 0 := by
  constructor
  · intro h j hj
    have h0 := congrArg (fun q : Polynomial A => q.coeff (j - 1)) h
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, ← Nat.cast_succ, Nat.succ_eq_add_one,
      show j - 1 + 1 = j by omega] at h0
    have hodd : ((j : ℕ) : A) = 1 := by
      have : j = 2 * (j / 2) + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        CharTwo.two_eq_zero, zero_mul, zero_add]
    rwa [hodd, mul_one] at h0
  · intro h; ext n
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, ← Nat.cast_succ]
    by_cases hn : (n + 1) % 2 = 1
    · rw [h (n + 1) hn, zero_mul]
    · have hev : ((n + 1 : ℕ) : A) = 0 := by
        have : n + 1 = 2 * ((n + 1) / 2) := by omega
        rw [this, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul]
      rw [hev, mul_zero]

lemma natDegree_even_of_deriv_eq_zero {A : Type*} [CommRing A] [CharP A 2] {p : Polynomial A}
    (hp : p.derivative = 0) : p.natDegree % 2 = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  · by_contra hne
    have hodd : p.natDegree % 2 = 1 := by omega
    have hz := (deriv_eq_zero_iff_even_coeffs p).mp hp p.natDegree hodd
    exact Polynomial.leadingCoeff_ne_zero.mpr h0 hz

lemma dXBi_eq_zero_iff_even_X (g : BiPoly F) :
    B6401ContactKerD.dXBi g = 0 ↔ ∀ j i, i % 2 = 1 → (g.coeff j).coeff i = 0 := by
  constructor
  · intro h j i hi
    have hj : (g.coeff j).derivative = 0 := by
      have := congrArg (fun p : BiPoly F => p.coeff j) h
      rwa [B6401ContactKerD.coeff_dXBi, Polynomial.coeff_zero] at this
    exact (deriv_eq_zero_iff_even_coeffs (g.coeff j)).mp hj i hi
  · intro h; rw [Polynomial.ext_iff]; intro j
    rw [B6401ContactKerD.coeff_dXBi, Polynomial.coeff_zero]
    exact (deriv_eq_zero_iff_even_coeffs (g.coeff j)).mpr (h j)

lemma dXBi_sq (g : BiPoly F) : B6401ContactKerD.dXBi (g ^ 2) = 0 := by
  rw [sq, B6401ContactKerD.dXBi_mul, mul_comm g (B6401ContactKerD.dXBi g), CharTwo.add_self_eq_zero]

lemma dXBi_pow_two_mul (g : BiPoly F) (k : ℕ) : B6401ContactKerD.dXBi (g ^ (2 * k)) = 0 := by
  rw [mul_comm, pow_mul]; exact dXBi_sq (g ^ k)

lemma dXBi_C (p : Polynomial F) : B6401ContactKerD.dXBi (C p) = C p.derivative := by
  rw [Polynomial.ext_iff]; intro j
  rw [B6401ContactKerD.coeff_dXBi, Polynomial.coeff_C, Polynomial.coeff_C]
  split_ifs <;> simp

lemma natDegree_contact_dXBi_le (g : BiPoly F) : (B6401ContactKerD.dXBi g).natDegree ≤ g.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
  rw [B6401ContactKerD.coeff_dXBi, Polynomial.coeff_eq_zero_of_natDegree_lt hj, Polynomial.derivative_zero]

lemma deriv_pow_two_mul {A : Type*} [CommRing A] [CharP A 2] (p : Polynomial A) (k : ℕ) :
    (p ^ (2 * k)).derivative = 0 := by
  rw [mul_comm, pow_mul, sq, Polynomial.derivative_mul, mul_comm (p ^ k) _, CharTwo.add_self_eq_zero]

lemma natDegree_le_or_even_of_deriv_eq_dXBi (f g : BiPoly F) (h : f.derivative = B6401ContactKerD.dXBi g) :
    f.natDegree ≤ g.natDegree + 1 ∨ f.natDegree % 2 = 0 := by
  by_cases hev : f.natDegree % 2 = 0
  · exact Or.inr hev
  · left
    have hf0 : f ≠ 0 := by intro h0; simp [h0] at hev
    have hodd : f.natDegree % 2 = 1 := by omega
    have hpos : 1 ≤ f.natDegree := by omega
    have hcoeff : (f.derivative).coeff (f.natDegree - 1) ≠ 0 := by
      rw [Polynomial.coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one,
        show f.natDegree - 1 + 1 = f.natDegree by omega]
      have hc1 : ((f.natDegree : ℕ) : Polynomial F) = 1 := by
        have : f.natDegree = 2 * (f.natDegree / 2) + 1 := by omega
        rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
          CharTwo.two_eq_zero, zero_mul, zero_add]
      rw [hc1, mul_one]
      exact Polynomial.leadingCoeff_ne_zero.mpr hf0
    have hle1 : f.natDegree - 1 ≤ (f.derivative).natDegree := Polynomial.le_natDegree_of_ne_zero hcoeff
    have hle2 : (f.derivative).natDegree ≤ g.natDegree := by rw [h]; exact natDegree_contact_dXBi_le g
    omega

/-- **Char-2 `ker(D)` PDE & Parity Facts (`deg_R = 1`):** -/
theorem kerD1_pde_facts {Fpoly : ContactPoly F} (hker : contactDeriv Fpoly = 0) (hdeg : Fpoly.natDegree ≤ 1) :
    (Fpoly.coeff 1).derivative = 0 ∧
    (Fpoly.coeff 1).natDegree % 2 = 0 ∧
    (Fpoly.coeff 0).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 1) ∧
    ((Fpoly.coeff 0).natDegree ≤ (Fpoly.coeff 1).natDegree + 1 ∨ (Fpoly.coeff 0).natDegree % 2 = 0) := by
  have hc2 := congrArg (fun Q : ContactPoly F => Q.coeff 2) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Fpoly.natDegree < 2)] at hc2
  have hd0 : B6401ContactKerD.dXBi (0 : BiPoly F) = 0 := by
    rw [Polynomial.ext_iff]; intro j; simp [B6401ContactKerD.coeff_dXBi]
  rw [hd0, zero_add] at hc2
  simp only [show (2 : ℕ) ≠ 0 by omega, ↓reduceIte, show 2 - 1 = 1 by rfl] at hc2
  have hc1 := congrArg (fun Q : ContactPoly F => Q.coeff 1) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero] at hc1
  simp only [one_ne_zero, ↓reduceIte, Nat.sub_self] at hc1
  have hf0d : (Fpoly.coeff 0).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 1) := by
    have h := congrArg (· + B6401ContactKerD.dXBi (Fpoly.coeff 1)) hc1
    rw [zero_add, add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
    exact h
  exact ⟨hc2, natDegree_even_of_deriv_eq_zero hc2, hf0d,
    natDegree_le_or_even_of_deriv_eq_dXBi _ _ hf0d⟩

/-- **Char-2 `ker(D)` PDE & Parity Facts (`deg_R = 2`):** -/
theorem kerD2_pde_facts {Fpoly : ContactPoly F} (hker : contactDeriv Fpoly = 0) (hdeg : Fpoly.natDegree ≤ 2) :
    (Fpoly.coeff 2).derivative = 0 ∧
    (Fpoly.coeff 2).natDegree % 2 = 0 ∧
    (Fpoly.coeff 1).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 2) ∧
    ((Fpoly.coeff 1).natDegree ≤ (Fpoly.coeff 2).natDegree + 1 ∨ (Fpoly.coeff 1).natDegree % 2 = 0) ∧
    (Fpoly.coeff 0).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 1) ∧
    ((Fpoly.coeff 0).natDegree ≤ (Fpoly.coeff 1).natDegree + 1 ∨ (Fpoly.coeff 0).natDegree % 2 = 0) := by
  have hd0 : B6401ContactKerD.dXBi (0 : BiPoly F) = 0 := by
    rw [Polynomial.ext_iff]; intro j; simp [B6401ContactKerD.coeff_dXBi]
  have hc3 := congrArg (fun Q : ContactPoly F => Q.coeff 3) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Fpoly.natDegree < 3), hd0, zero_add] at hc3
  simp only [show (3 : ℕ) ≠ 0 by omega, ↓reduceIte, show 3 - 1 = 2 by rfl] at hc3
  have hc2 := congrArg (fun Q : ContactPoly F => Q.coeff 2) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero] at hc2
  simp only [show (2 : ℕ) ≠ 0 by omega, ↓reduceIte, show 2 - 1 = 1 by rfl] at hc2
  have hf1d : (Fpoly.coeff 1).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 2) := by
    have h := congrArg (· + B6401ContactKerD.dXBi (Fpoly.coeff 2)) hc2
    rw [zero_add, add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
    exact h
  have hc1 := congrArg (fun Q : ContactPoly F => Q.coeff 1) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero] at hc1
  simp only [one_ne_zero, ↓reduceIte, Nat.sub_self] at hc1
  have hf0d : (Fpoly.coeff 0).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 1) := by
    have h := congrArg (· + B6401ContactKerD.dXBi (Fpoly.coeff 1)) hc1
    rw [zero_add, add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
    exact h
  exact ⟨hc3, natDegree_even_of_deriv_eq_zero hc3, hf1d,
    natDegree_le_or_even_of_deriv_eq_dXBi _ _ hf1d, hf0d,
    natDegree_le_or_even_of_deriv_eq_dXBi _ _ hf0d⟩

private lemma natDegree_pos_of_irred {K : Type*} [Field K] {p : K[X]} (hp : Irreducible p) :
    0 < p.natDegree :=
  Nat.pos_of_ne_zero fun h0 => hp.not_isUnit
    (Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hp.ne_zero, h0]; rfl))

open scoped Classical in
private lemma isPrimitive_pow_bi {p : BiPoly F} (hp : p.IsPrimitive) :
    ∀ n : ℕ, (p ^ n).IsPrimitive
  | 0 => by rw [pow_zero]; exact Polynomial.isPrimitive_one
  | n + 1 => by rw [pow_succ]; exact (isPrimitive_pow_bi hp n).mul hp

/-- Over ANY char-2 field `K`, if `g.derivative ≠ 0`, then `g` has an irreducible factor `p`
with `p.derivative ≠ 0` appearing to an ODD exact multiplicity `2k + 1`! -/
private lemma exists_odd_irred_of_deriv_ne_zero {K : Type*} [Field K] [CharP K 2] :
    ∀ n : ℕ, ∀ g : K[X], g.natDegree ≤ n → g.derivative ≠ 0 →
      ∃ (p r : K[X]) (k : ℕ), Irreducible p ∧ p.derivative ≠ 0 ∧ g = p ^ (2 * k + 1) * r ∧ ¬ p ∣ r := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro g hgn hgd
    have hg0 : g ≠ 0 := by intro h0; subst h0; simp at hgd
    have hgpos : 0 < g.natDegree := by
      by_contra h0
      have hC := Polynomial.eq_C_of_natDegree_eq_zero (p := g) (by omega)
      rw [hC, Polynomial.derivative_C] at hgd; exact hgd rfl
    have hgn_nu : ¬ IsUnit g := fun hu => by
      have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    obtain ⟨p, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hgn_nu hg0
    have hp_prime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irr
    have hp_pos : 0 < p.natDegree := natDegree_pos_of_irred hp_irr
    -- Extract maximal power m ≥ 1 of p dividing g!
    have hex_max : ∃ m : ℕ, 1 ≤ m ∧ p ^ m ∣ g ∧ ¬ p ^ (m + 1) ∣ g := by
      have hfin : ∃ m : ℕ, ¬ p ^ (m + 1) ∣ g := by
        refine ⟨g.natDegree, fun hd => ?_⟩
        have hle := Polynomial.natDegree_le_of_dvd hd hg0
        rw [Polynomial.natDegree_pow] at hle; nlinarith
      let m0 := Nat.find hfin
      have hm0_not : ¬ p ^ (m0 + 1) ∣ g := Nat.find_spec hfin
      have hm0_pos : 1 ≤ m0 := by
        by_contra h0
        have hm0z : m0 = 0 := by omega
        rw [hm0z, zero_add, pow_one] at hm0_not; exact hm0_not hp_dvd
      have hm0_dvd : p ^ m0 ∣ g := by
        have hlt := Nat.find_min hfin (show m0 - 1 < m0 by omega)
        push Not at hlt; rwa [show m0 - 1 + 1 = m0 by omega] at hlt
      exact ⟨m0, hm0_pos, hm0_dvd, hm0_not⟩
    obtain ⟨m, hm1, ⟨r, hr_eq⟩, hnot_succ⟩ := hex_max
    have hndvd_r : ¬ p ∣ r := by
      intro ⟨s, hs⟩; apply hnot_succ; refine ⟨s, ?_⟩
      rw [hr_eq, hs, pow_succ]; ring
    have hr0 : r ≠ 0 := by intro h0; subst h0; rw [mul_zero] at hr_eq; exact hg0 hr_eq
    have hr_lt : r.natDegree < g.natDegree := by
      rw [hr_eq, Polynomial.natDegree_mul (pow_ne_zero m hp_irr.ne_zero) hr0, Polynomial.natDegree_pow]
      nlinarith
    by_cases hpd_odd : p.derivative ≠ 0 ∧ m % 2 = 1
    · exact ⟨p, r, m / 2, hp_irr, hpd_odd.1, by rwa [show 2 * (m / 2) + 1 = m by omega], hndvd_r⟩
    · have hpm_d : (p ^ m).derivative = 0 := by
        by_cases hpd0 : p.derivative = 0
        · rw [Polynomial.derivative_pow, hpd0, mul_zero]
        · have hm_ev : m % 2 ≠ 1 := fun h => hpd_odd ⟨hpd0, h⟩
          have hev : m = 2 * (m / 2) := by omega
          rw [hev]; exact deriv_pow_two_mul p (m / 2)
      have hrd : r.derivative ≠ 0 := by
        intro h0; apply hgd
        rw [hr_eq, Polynomial.derivative_mul, hpm_d, h0, zero_mul, mul_zero, add_zero]
      obtain ⟨p', r', k', hp'_irr, hp'_d, hr'_eq, hp'_ndvd⟩ := ih r.natDegree (by omega) r le_rfl hrd
      have hp'_prime : Prime p' := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp'_irr
      have hndvd_pm : ¬ p' ∣ p ^ m := by
        intro hdiv
        have hp'_dvd_p : p' ∣ p := hp'_prime.dvd_of_dvd_pow hdiv
        have hassoc : Associated p' p := hp'_irr.associated_of_dvd hp_irr hp'_dvd_p
        have hp_dvd_r : p ∣ r := (hassoc.symm.dvd).trans (by rw [hr'_eq]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _)
        exact hndvd_r hp_dvd_r
      have hndvd_prod : ¬ p' ∣ p ^ m * r' := fun h =>
        (hp'_prime.dvd_or_dvd h).elim hndvd_pm hp'_ndvd
      exact ⟨p', p ^ m * r', k', hp'_irr, hp'_d, by rw [hr_eq, hr'_eq]; ring, hndvd_prod⟩

/-- Pull any nonzero `pK : (RatFunc F)[X]` back to a primitive polynomial `p : BiPoly F`
whose image in `(RatFunc F)[X]` is associated to `pK`! -/
private lemma exists_prim_associated_ratFunc (pK : Polynomial (RatFunc F)) (hpK : pK ≠ 0) :
    ∃ p : BiPoly F, p.IsPrimitive ∧ p ≠ 0 ∧ p.natDegree = pK.natDegree ∧
      Associated (p.map (algebraMap (Polynomial F) (RatFunc F))) pK := by
  classical
  let ι : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial F) (RatFunc F)
  -- Clear denominators of all coefficients j ≤ pK.natDegree!
  have hclear : ∀ j : ℕ, ∃ (n d : Polynomial F), d ≠ 0 ∧ pK.coeff j * ι d = ι n := by
    intro j
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial F)) (pK.coeff j)
    exact ⟨n, d, nonZeroDivisors.ne_zero d.2, hd⟩
  choose num den hden_ne hden_eq using hclear
  let D : Polynomial F := ∏ j ∈ Finset.range (pK.natDegree + 1), den j
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hden_ne j
  let q : BiPoly F := ∑ j ∈ Finset.range (pK.natDegree + 1),
    Polynomial.monomial j (num j * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase j, den l)
  have hq_map : q.map ι = C (ι D) * pK := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
    by_cases hj : j < pK.natDegree + 1
    · have hj_mem : j ∈ Finset.range (pK.natDegree + 1) := Finset.mem_range.mpr hj
      dsimp only [q]
      rw [finset_sum_coeff, Finset.sum_eq_single j]
      · rw [Polynomial.coeff_monomial_same, map_mul, map_prod]
        have hD_split : D = den j * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase j, den l :=
          (Finset.mul_prod_erase _ _ hj_mem).symm
        rw [hD_split, map_mul, map_prod, ← hden_eq j]; ring
      · intro l _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro hnot; exact absurd hj_mem hnot
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : pK.natDegree < j), mul_zero]
      dsimp only [q]; rw [finset_sum_coeff]
      have h0 : (∑ x ∈ Finset.range (pK.natDegree + 1),
          (Polynomial.monomial x (num x * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase x, den l)).coeff j) = 0 := by
        apply Finset.sum_eq_zero; intro x hx
        have := Finset.mem_range.mp hx
        simp [Polynomial.coeff_monomial, show x ≠ j by omega]
      rw [h0, map_zero]
  have hq_ne : q ≠ 0 := by
    intro h0; rw [h0, Polynomial.map_zero] at hq_map
    have hDι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hDι) hpK) hq_map.symm
  let p : BiPoly F := q.primPart
  have hp_prim : p.IsPrimitive := q.isPrimitive_primPart
  have hp_ne : p ≠ 0 := q.primPart_ne_zero
  have hcont_ne : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.mpr hq_ne
  have hcont_ι : ι q.content ≠ 0 := fun h => hcont_ne (hι (by rwa [map_zero]))
  have hD_ι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
  have hp_map : p.map ι = C ((ι q.content)⁻¹ * ι D) * pK := by
    have hq_fac := congrArg (Polynomial.map ι) q.eq_C_content_mul_primPart
    rw [Polynomial.map_mul, Polynomial.map_C, hq_map] at hq_fac
    have hm := congrArg (C (ι q.content)⁻¹ * ·) hq_fac
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcont_ι, map_one, one_mul] at hm
    rw [← hm, map_mul, mul_assoc]
  have hu : IsUnit (C ((ι q.content)⁻¹ * ι D) : Polynomial (RatFunc F)) :=
    Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (mul_ne_zero (inv_ne_zero hcont_ι) hD_ι))
  obtain ⟨u, hu_eq⟩ := hu
  refine ⟨p, hp_prim, hp_ne, ?_, ⟨u⁻¹, ?_⟩⟩
  · have h1 := congrArg Polynomial.natDegree hp_map
    rw [Polynomial.natDegree_map_eq_of_injective hι,
      Polynomial.natDegree_C_mul (mul_ne_zero (inv_ne_zero hcont_ι) hD_ι)] at h1
    exact h1
  · rw [hp_map, ← hu_eq, mul_comm (↑u : Polynomial (RatFunc F)) pK, mul_assoc, Units.mul_inv, mul_one]

/-- Exact even multiplicity of any primitive irreducible `p : BiPoly F` (`p.derivative ≠ 0`) in
a nonzero `f : BiPoly F` with `f.derivative = 0`! -/
private lemma even_max_pow_of_deriv_eq_zero {p f : BiPoly F}
    (hp_prim : p.IsPrimitive) (hp_irrK : Irreducible (p.map (algebraMap (Polynomial F) (RatFunc F))))
    (hp_d : p.derivative ≠ 0) (hf0 : f ≠ 0) (hf_d : f.derivative = 0)
    (m : ℕ) (r : BiPoly F) (heq : f = p ^ m * r) (hndvd : ¬ p ∣ r) :
    m % 2 = 0 := by
  classical
  let ι : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial F) (RatFunc F)
  by_contra hodd
  have hm1 : 1 ≤ m := by omega
  have hodd' : ((m : ℕ) : Polynomial F) = 1 := by
    have : m = 2 * (m / 2) + 1 := by omega
    rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      CharTwo.two_eq_zero, zero_mul, zero_add]
  have hd := congrArg Polynomial.derivative heq
  rw [hf_d, Polynomial.derivative_mul, Polynomial.derivative_pow] at hd
  have hm_cast : ((m : ℕ) : BiPoly F) = 1 := by rw [← map_natCast C, hodd', map_one]
  simp only [Polynomial.C_eq_natCast, hm_cast, one_mul] at hd
  have hp_dvd_prod : p ∣ p.derivative * r := by
    have hp_ne : p ^ (m - 1) ≠ 0 := pow_ne_zero _ hp_prim.ne_zero
    have hsplit : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hm1]
    rw [hsplit] at hd
    have hfact : p ^ (m - 1) * (p.derivative * r + p * r.derivative) = 0 := by
      linear_combination -hd
    have hzero : p.derivative * r + p * r.derivative = 0 := (mul_eq_zero.mp hfact).resolve_left hp_ne
    refine ⟨r.derivative, ?_⟩
    have := congrArg (· + p * r.derivative) hzero
    rw [zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero] at this
    exact this
  -- Lift divisibility to (RatFunc F)[X] where p.map ι is prime!
  have hp_dvdK : p.map ι ∣ (p.derivative).map ι * r.map ι := by
    rcases hp_dvd_prod with ⟨q, hq⟩
    exact ⟨q.map ι, by rw [← Polynomial.map_mul, hq, Polynomial.map_mul]⟩
  have hp_primeK : Prime (p.map ι) := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irrK
  rcases hp_primeK.dvd_or_dvd hp_dvdK with hdvd_d | hdvd_r
  · have hd_ne : (p.derivative).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hp_d
    have hle := Polynomial.natDegree_le_of_dvd hdvd_d hd_ne
    rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι] at hle
    have hlt := Polynomial.natDegree_derivative_lt (p := p) (fun h0 =>
      hp_d (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]))
    omega
  · exact hndvd (hp_prim.dvd_of_fraction_map_dvd_fraction_map hdvd_r)

/-- **Master Char-2 `ker(D)` `deg_R = 2` Primitive GCD Decomposition (`kerD2_gcd_decomp`):**
For ANY `Fpoly ∈ ker(D)` of `deg_R = 2` (`f1 ≠ 0, f2 ≠ 0`) over ANY `[Field F] [CharP F 2]`:
extracts `qX : F[X]`, `gPrim, h1, h2 : BiPoly F` with:
- `g = C qX * gPrim`, `f1 = g * h1`, `f2 = g * h2`,
- `gPrim.IsPrimitive`, `IsRelPrime (h1.map ι) (h2.map ι)`,
- `gPrim.derivative = 0`, `g.derivative = 0`, `h2.derivative = 0`, `g.natDegree % 2 = 0`,
- `gPrim ∣ dXBi gPrim * h2`! -/
theorem kerD2_gcd_decomp {Fpoly : ContactPoly F}
    (hker : contactDeriv Fpoly = 0) (hdeg : Fpoly.natDegree ≤ 2)
    (hf1_ne : Fpoly.coeff 1 ≠ 0) (hf2_ne : Fpoly.coeff 2 ≠ 0) :
    let f1 := Fpoly.coeff 1
    let f2 := Fpoly.coeff 2
    let ι : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
    ∃ (qX : Polynomial F) (gPrim h1 h2 : BiPoly F),
      qX ≠ 0 ∧ gPrim.IsPrimitive ∧ gPrim ≠ 0 ∧ h1 ≠ 0 ∧ h2 ≠ 0 ∧
      f1 = C qX * gPrim * h1 ∧
      f2 = C qX * gPrim * h2 ∧
      IsRelPrime (h1.map ι) (h2.map ι) ∧
      gPrim.derivative = 0 ∧
      (C qX * gPrim).derivative = 0 ∧
      h2.derivative = 0 ∧
      (C qX * gPrim).natDegree = gPrim.natDegree ∧
      gPrim.natDegree % 2 = 0 ∧
      gPrim ∣ B6401ContactKerD.dXBi gPrim * h2 := by
  intro f1 f2 ι
  classical
  change f1 ≠ 0 at hf1_ne
  change f2 ≠ 0 at hf2_ne
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial F) (RatFunc F)
  have ⟨hf2_d, _, hf1_d, _, _, _⟩ := kerD2_pde_facts hker hdeg
  set f1K : Polynomial (RatFunc F) := f1.map ι
  set f2K : Polynomial (RatFunc F) := f2.map ι
  have hf1K_ne : f1K ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf1_ne
  have hf2K_ne : f2K ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf2_ne
  let gK : Polynomial (RatFunc F) := EuclideanDomain.gcd f1K f2K
  have hgK_ne : gK ≠ 0 := fun h0 => hf2K_ne (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  obtain ⟨gPrim, hgP_prim, hgP_ne, hgP_deg, hgP_assoc⟩ := exists_prim_associated_ratFunc gK hgK_ne
  have hgP_dvd1 : gPrim ∣ f1 :=
    hgP_prim.dvd_of_fraction_map_dvd_fraction_map (hgP_assoc.dvd.trans (EuclideanDomain.gcd_dvd_left f1K f2K))
  have hgP_dvd2 : gPrim ∣ f2 :=
    hgP_prim.dvd_of_fraction_map_dvd_fraction_map (hgP_assoc.dvd.trans (EuclideanDomain.gcd_dvd_right f1K f2K))
  rcases hgP_dvd1 with ⟨h1_raw, hh1_raw⟩
  rcases hgP_dvd2 with ⟨h2_raw, hh2_raw⟩
  have hh1r_ne : h1_raw ≠ 0 := fun h0 => hf1_ne (by rw [hh1_raw, h0, mul_zero])
  have hh2r_ne : h2_raw ≠ 0 := fun h0 => hf2_ne (by rw [hh2_raw, h0, mul_zero])
  -- Factor out common X-content qX = gcd(h1_raw.content, h2_raw.content)!
  let qX : Polynomial F := EuclideanDomain.gcd h1_raw.content h2_raw.content
  have hqX_ne : qX ≠ 0 := fun h0 =>
    (Polynomial.content_eq_zero_iff.not.mpr hh2r_ne) (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  have hqX_dvd1 : C qX ∣ h1_raw :=
    (_root_.map_dvd C (EuclideanDomain.gcd_dvd_left _ _)).trans h1_raw.C_content_dvd
  have hqX_dvd2 : C qX ∣ h2_raw :=
    (_root_.map_dvd C (EuclideanDomain.gcd_dvd_right _ _)).trans h2_raw.C_content_dvd
  rcases hqX_dvd1 with ⟨h1, hh1⟩
  rcases hqX_dvd2 with ⟨h2, hh2⟩
  have hf1_fac : f1 = C qX * gPrim * h1 := by rw [hh1_raw, hh1]; ring
  have hf2_fac : f2 = C qX * gPrim * h2 := by rw [hh2_raw, hh2]; ring
  have hh1_ne : h1 ≠ 0 := fun h0 => hf1_ne (by rw [hf1_fac, h0, mul_zero])
  have hh2_ne : h2 ≠ 0 := fun h0 => hf2_ne (by rw [hf2_fac, h0, mul_zero])
  -- Prove IsRelPrime (h1.map ι) (h2.map ι) in (RatFunc F)[X]!
  have hrel : IsRelPrime (h1.map ι) (h2.map ι) := by
    intro d hd1 hd2
    have hqι : ι qX ≠ 0 := fun h => hqX_ne (hι (by rwa [map_zero]))
    have hqU : IsUnit (C (ι qX) : Polynomial (RatFunc F)) := Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hqι)
    have h1_eq : f1K = C (ι qX) * gPrim.map ι * h1.map ι := by
      dsimp [f1K]; rw [hf1_fac, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
    have h2_eq : f2K = C (ι qX) * gPrim.map ι * h2.map ι := by
      dsimp [f2K]; rw [hf2_fac, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
    have hd_mul : gPrim.map ι * d ∣ gK := by
      apply EuclideanDomain.dvd_gcd
      · rw [h1_eq]; rcases hd1 with ⟨a, ha⟩; exact ⟨C (ι qX) * a, by rw [ha]; ring⟩
      · rw [h2_eq]; rcases hd2 with ⟨b, hb⟩; exact ⟨C (ι qX) * b, by rw [hb]; ring⟩
    have hd_self : gPrim.map ι * d ∣ gPrim.map ι := hd_mul.trans hgP_assoc.symm.dvd
    rcases hd_self with ⟨w, hw⟩
    have hne : gPrim.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hgP_ne
    have hdw : d * w = 1 := mul_left_cancel₀ hne (by
      calc gPrim.map ι * (d * w) = gPrim.map ι * d * w := by ring
        _ = gPrim.map ι := hw.symm
        _ = gPrim.map ι * 1 := (mul_one _).symm)
    exact isUnit_iff_exists_inv.mpr ⟨w, hdw⟩
  -- Prove gPrim.derivative = 0 using exists_odd_irred_of_deriv_ne_zero + ker(D) PDE!
  have hgP_d : gPrim.derivative = 0 := by
    by_contra hgd
    have hgPK_d : (gPrim.map ι).derivative ≠ 0 := by
      rw [Polynomial.derivative_map]; exact (Polynomial.map_ne_zero_iff hι).mpr hgd
    obtain ⟨pK, rK, k, hpK_irr, hpK_d, hgK_fac, hpK_ndvd_r⟩ :=
      exists_odd_irred_of_deriv_ne_zero (gPrim.map ι).natDegree (gPrim.map ι) le_rfl hgPK_d
    obtain ⟨p, hp_prim, hp_ne, hp_deg, hp_assoc⟩ := exists_prim_associated_ratFunc pK hpK_irr.ne_zero
    have hp_irrK : Irreducible (p.map ι) := hp_assoc.irreducible_iff.mpr hpK_irr
    have hp_d : p.derivative ≠ 0 := by
      intro h0; apply hpK_d
      obtain ⟨u, hu⟩ := hp_assoc
      have hu_c : (u : Polynomial (RatFunc F)).derivative = 0 := by
        have hdu := Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
        rw [Polynomial.eq_C_of_natDegree_eq_zero hdu, Polynomial.derivative_C]
      rw [← hu, Polynomial.derivative_mul, Polynomial.derivative_map, h0, Polynomial.map_zero, hu_c]
      simp
    -- Extract exact max power of p dividing f2 (must be EVEN = 2 * k2)!
    have hex_max : ∀ (q : BiPoly F), q ≠ 0 → ∃ m r, q = p ^ m * r ∧ ¬ p ∣ r := by
      intro q hq0
      have hp_pos : 0 < p.natDegree := by rw [hp_deg]; exact natDegree_pos_of_irred hpK_irr
      have hfin : ∃ m : ℕ, ¬ p ^ (m + 1) ∣ q := by
        refine ⟨q.natDegree, fun hd => ?_⟩
        have hle := Polynomial.natDegree_le_of_dvd hd hq0
        rw [Polynomial.natDegree_pow] at hle; nlinarith
      let m := Nat.find hfin
      have hnot : ¬ p ^ (m + 1) ∣ q := Nat.find_spec hfin
      have hdvd : p ^ m ∣ q := by
        by_cases hm0 : m = 0
        · rw [hm0, pow_zero]; exact one_dvd _
        · have hlt := Nat.find_min hfin (show m - 1 < m by omega)
          push Not at hlt; rwa [show m - 1 + 1 = m by omega] at hlt
      rcases hdvd with ⟨r, hr⟩
      refine ⟨m, r, hr, fun ⟨s, hs⟩ => hnot ⟨s, ?_⟩⟩
      rw [hr, hs, pow_succ]; ring
    obtain ⟨e2, q2, hf2_p, hp_ndvd_q2⟩ := hex_max f2 hf2_ne
    have he2_ev : e2 % 2 = 0 := even_max_pow_of_deriv_eq_zero hp_prim hp_irrK hp_d hf2_ne hf2_d e2 q2 hf2_p hp_ndvd_q2
    obtain ⟨e1, q1, hf1_p, hp_ndvd_q1⟩ := hex_max f1 hf1_ne
    -- Show min(e1, e2) = 2*k + 1!
    have hp_dvd_gP : p ^ (2 * k + 1) ∣ gPrim := by
      refine (isPrimitive_pow_bi hp_prim (2 * k + 1)).dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) ?_
      rw [Polynomial.map_pow, hgK_fac]
      exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hp_assoc.dvd _) _
    have hp_ndvd_gP : ¬ p ^ (2 * k + 2) ∣ gPrim := by
      intro hd
      have hdK : pK ^ (2 * k + 2) ∣ pK ^ (2 * k + 1) * rK := by
        rw [← hgK_fac]
        exact (pow_dvd_pow_of_dvd hp_assoc.symm.dvd _).trans (by
          rcases hd with ⟨s, hs⟩; exact ⟨s.map ι, by rw [hs, Polynomial.map_mul, Polynomial.map_pow]⟩)
      have hpK_dvd_r : pK ∣ rK := by
        rcases hdK with ⟨s, hs⟩
        have h1 : pK ^ (2 * k + 1) * rK = pK ^ (2 * k + 1) * (pK * s) := by
          rw [hs, pow_succ]; ring
        exact ⟨s, mul_left_cancel₀ (pow_ne_zero _ hpK_irr.ne_zero) h1⟩
      exact hpK_ndvd_r hpK_dvd_r
    have hmin_ge : 2 * k + 1 ≤ e1 ∧ 2 * k + 1 ≤ e2 := by
      have hle_of : ∀ (q r : BiPoly F) (e : ℕ), q = p ^ e * r → ¬ p ∣ r → p ^ (2 * k + 1) ∣ q → 2 * k + 1 ≤ e := by
        intro q r e hqr hnd hd
        by_contra hlt
        have hle : e + 1 ≤ 2 * k + 1 := by omega
        have hd1 : p ^ (e + 1) ∣ p ^ e * r := (pow_dvd_pow p hle).trans (hqr ▸ hd)
        rcases hd1 with ⟨s, hs⟩
        have h1 : p ^ e * r = p ^ e * (p * s) := by rw [hs, pow_succ]; ring
        exact hnd ⟨s, mul_left_cancel₀ (pow_ne_zero _ hp_ne) h1⟩
      exact ⟨hle_of f1 q1 e1 hf1_p hp_ndvd_q1 (hp_dvd_gP.trans (by rw [hf1_fac]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)),
             hle_of f2 q2 e2 hf2_p hp_ndvd_q2 (hp_dvd_gP.trans (by rw [hf2_fac]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _))⟩
    -- Since gPrim is associated to gcd(f1, f2) in K[Y], we cannot have BOTH 2*k+2 ≤ e1 and 2*k+2 ≤ e2!
    have he1_eq : e1 = 2 * k + 1 := by
      by_contra hne
      have h1 : 2 * k + 2 ≤ e1 := by omega
      have h2 : 2 * k + 2 ≤ e2 := by omega
      apply hp_ndvd_gP
      refine (isPrimitive_pow_bi hp_prim (2 * k + 2)).dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) ?_
      rw [Polynomial.map_pow]
      refine (EuclideanDomain.dvd_gcd ?_ ?_).trans hgP_assoc.symm.dvd
      · exact (pow_dvd_pow _ h1).trans (by
          dsimp [f1K]; rw [hf1_p, Polynomial.map_mul, Polynomial.map_pow]; exact dvd_mul_right _ _)
      · exact (pow_dvd_pow _ h2).trans (by
          dsimp [f2K]; rw [hf2_p, Polynomial.map_mul, Polynomial.map_pow]; exact dvd_mul_right _ _)
    -- Now e2 = 2 * (e2/2) ≥ 2*k + 2, so p^(2*k+2) ∣ dXBi f2 = f1.derivative, contradicting e1 = 2*k+1!
    have he2_ge : 2 * k + 1 ≤ e2 := hmin_ge.2
    have hpdvd_dXf2 : p ^ e2 ∣ B6401ContactKerD.dXBi f2 := by
      rw [hf2_p, B6401ContactKerD.dXBi_mul, show e2 = 2 * (e2 / 2) by omega, dXBi_pow_two_mul, zero_mul, zero_add]
      exact dvd_mul_right _ _
    have hpdvd_f1d : p ^ (2 * k + 1) ∣ f1.derivative :=
      (pow_dvd_pow p he2_ge).trans (hf1_d.symm ▸ hpdvd_dXf2)
    have hf1d_eq : f1.derivative = p ^ (2 * k) * p.derivative * q1 + p ^ (2 * k + 1) * q1.derivative := by
      rw [hf1_p, he1_eq, Polynomial.derivative_mul, Polynomial.derivative_pow]
      have hodd' : ((2 * k + 1 : ℕ) : Polynomial F) = 1 := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, CharTwo.two_eq_zero, zero_mul, zero_add]
      have hm_cast : ((2 * k + 1 : ℕ) : BiPoly F) = 1 := by rw [← map_natCast C, hodd', map_one]
      simp only [Polynomial.C_eq_natCast, hm_cast, one_mul, show 2 * k + 1 - 1 = 2 * k by omega]
    have hpdvd_term : p ^ (2 * k + 1) ∣ p ^ (2 * k) * p.derivative * q1 := by
      rcases hpdvd_f1d with ⟨s, hs⟩
      refine ⟨s + q1.derivative, ?_⟩
      have h := congrArg (· + p ^ (2 * k + 1) * q1.derivative) (hs.symm.trans hf1d_eq)
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h
      linear_combination -h
    have hp_dvd_pq1 : p ∣ p.derivative * q1 := by
      rcases hpdvd_term with ⟨s, hs⟩
      have h1 : p ^ (2 * k) * (p.derivative * q1) = p ^ (2 * k) * (p * s) := by
        rw [pow_succ] at hs; linear_combination hs
      exact ⟨s, mul_left_cancel₀ (pow_ne_zero _ hp_ne) h1⟩
    have hp_dvdK : p.map ι ∣ (p.derivative).map ι * q1.map ι := by
      rcases hp_dvd_pq1 with ⟨s, hs⟩; exact ⟨s.map ι, by rw [← Polynomial.map_mul, hs, Polynomial.map_mul]⟩
    rcases (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irrK).dvd_or_dvd hp_dvdK with hdvd_d | hdvd_q
    · have hle := Polynomial.natDegree_le_of_dvd hdvd_d ((Polynomial.map_ne_zero_iff hι).mpr hp_d)
      rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι] at hle
      have hlt := Polynomial.natDegree_derivative_lt (p := p) (fun h0 =>
        hp_d (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]))
      omega
    · exact hp_ndvd_q1 (hp_prim.dvd_of_fraction_map_dvd_fraction_map hdvd_q)
  have hg_d : (C qX * gPrim).derivative = 0 := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_C, hgP_d, zero_mul, mul_zero, add_zero]
  have hh2_d : h2.derivative = 0 := by
    have hd := congrArg Polynomial.derivative hf2_fac
    rw [hf2_d, Polynomial.derivative_mul, hg_d, zero_mul, zero_add] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (mul_ne_zero (Polynomial.C_ne_zero.mpr hqX_ne) hgP_ne)
  -- Finally prove gPrim ∣ dXBi gPrim * h2 from f1.derivative = dXBi f2!
  have hdvd_dX : gPrim ∣ B6401ContactKerD.dXBi gPrim * h2 := by
    have heq : (C qX * gPrim) * h1.derivative =
        (C qX.derivative * gPrim + C qX * B6401ContactKerD.dXBi gPrim) * h2 +
          (C qX * gPrim) * B6401ContactKerD.dXBi h2 := by
      have hL : f1.derivative = (C qX * gPrim) * h1.derivative := by
        rw [hf1_fac, Polynomial.derivative_mul, hg_d, zero_mul, zero_add]
      have hR : B6401ContactKerD.dXBi f2 =
          (C qX.derivative * gPrim + C qX * B6401ContactKerD.dXBi gPrim) * h2 +
            (C qX * gPrim) * B6401ContactKerD.dXBi h2 := by
        rw [hf2_fac, B6401ContactKerD.dXBi_mul, B6401ContactKerD.dXBi_mul, dXBi_C]
      rw [← hL, ← hR, hf1_d]
    have hdvd_C : gPrim ∣ C qX * (B6401ContactKerD.dXBi gPrim * h2) := by
      refine ⟨C qX * h1.derivative + C qX * B6401ContactKerD.dXBi h2 + C qX.derivative * h2, ?_⟩
      have h0 : C qX * (B6401ContactKerD.dXBi gPrim * h2) +
          gPrim * (C qX * h1.derivative + C qX * B6401ContactKerD.dXBi h2 + C qX.derivative * h2) = 0 := by
        have hadd := congrArg (· + (C qX * gPrim) * h1.derivative) heq
        rw [CharTwo.add_self_eq_zero] at hadd
        have h2z : ∀ a : BiPoly F, a + a = 0 := CharTwo.add_self_eq_zero
        linear_combination -hadd
      have hfin := congrArg (· + gPrim * (C qX * h1.derivative + C qX * B6401ContactKerD.dXBi h2 + C qX.derivative * h2)) h0
      rw [zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero] at hfin
      exact hfin
    refine hgP_prim.dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) ?_
    rcases hdvd_C with ⟨w, hw⟩
    have hqι : ι qX ≠ 0 := fun h => hqX_ne (hι (h.trans (map_zero ι).symm))
    refine ⟨C (ι qX)⁻¹ * w.map ι, ?_⟩
    have hm := congrArg (Polynomial.map ι) hw
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C] at hm
    have hm' := congrArg (C (ι qX)⁻¹ * ·) hm
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hqι, map_one, one_mul] at hm'
    change (B6401ContactKerD.dXBi gPrim * h2).map ι = gPrim.map ι * (C (ι qX)⁻¹ * w.map ι)
    rw [Polynomial.map_mul, hm', Polynomial.map_mul]; ring
  exact ⟨qX, gPrim, h1, h2, hqX_ne, hgP_prim, hgP_ne, hh1_ne, hh2_ne,
    hf1_fac, hf2_fac, hrel, hgP_d, hg_d, hh2_d, Polynomial.natDegree_C_mul hqX_ne,
    natDegree_even_of_deriv_eq_zero hgP_d, hdvd_dX⟩

/-- Helper: if `gPrim ∣ dXBi gPrim` in `BiPoly F` (`gPrim ≠ 0`), then `dXBi gPrim = 0`! -/
private lemma dXBi_eq_zero_of_dvd_dXBi {gPrim : BiPoly F} (hg : gPrim ≠ 0)
    (hdvd : gPrim ∣ B6401ContactKerD.dXBi gPrim) : B6401ContactKerD.dXBi gPrim = 0 := by
  classical
  rcases hdvd with ⟨c, hc⟩
  by_cases hc0 : c = 0
  · rw [hc, hc0, mul_zero]
  · exfalso
    have hc_deg : c.natDegree = 0 := by
      have h1 := natDegree_contact_dXBi_le gPrim
      rw [hc, Polynomial.natDegree_mul hg hc0] at h1; omega
    have hcC : c = C (c.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hc_deg
    have hc0_ne : c.coeff 0 ≠ 0 := fun h => hc0 (by rw [hcC, h, map_zero])
    -- Pick j0 ∈ gPrim.support maximizing (gPrim.coeff j).natDegree!
    have hsupp : gPrim.support.Nonempty := Polynomial.support_nonempty.mpr hg
    obtain ⟨j0, hj0_mem, hj0_max⟩ := Finset.exists_max_image gPrim.support (fun j => (gPrim.coeff j).natDegree) hsupp
    have hj0_ne : gPrim.coeff j0 ≠ 0 := Polynomial.mem_support_iff.mp hj0_mem
    have hcoeff := congrArg (fun p : BiPoly F => p.coeff j0) hc
    rw [B6401ContactKerD.coeff_dXBi, hcC, Polynomial.coeff_mul_C] at hcoeff
    have hderiv_ne : (gPrim.coeff j0).derivative ≠ 0 := by
      rw [hcoeff]; exact mul_ne_zero hj0_ne hc0_ne
    have hlt := Polynomial.natDegree_derivative_lt (p := gPrim.coeff j0) (fun h0 =>
      hderiv_ne (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]))
    rw [hcoeff, Polynomial.natDegree_mul hj0_ne hc0_ne] at hlt
    omega

/-- **Table 3 Subcase `2A` / `2B` Dichotomy (`kerD2_2A_2B_dichotomy`):**
1. For `h2.natDegree = 0` (`(8, 8, 10, 11)`): ALWAYS Subcase `2A` (`gPrim ∈ F[X^2, Y^2]`)!
2. For `gPrim.natDegree = 6, h2.natDegree = 2` (`(8, 6, 10, 11)`):
   EITHER Subcase `2A` (`gPrim ∈ F[X^2, Y^2]`)
   OR Subcase `2B` (`∃ uX q g1`, `h2 = C uX * q`, `gPrim = q * g1`, `q, g1 ∈ F[X, Y^2]`,
   `q.natDegree = 2`, `g1.natDegree = 4`, `IsRelPrime (h1.map ι) (q.map ι)`)! -/
theorem kerD2_2A_2B_dichotomy {gPrim h1 h2 : BiPoly F}
    (hgP_prim : gPrim.IsPrimitive) (hgP_ne : gPrim ≠ 0) (hh1_ne : h1 ≠ 0) (hh2_ne : h2 ≠ 0)
    (hgP_d : gPrim.derivative = 0) (hh2_d : h2.derivative = 0)
    (hrel : IsRelPrime (h1.map (algebraMap (Polynomial F) (RatFunc F)))
                       (h2.map (algebraMap (Polynomial F) (RatFunc F))))
    (hdvd_dX : gPrim ∣ B6401ContactKerD.dXBi gPrim * h2) :
    (h2.natDegree = 0 → ∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) ∧
    (gPrim.natDegree = 6 → h2.natDegree = 2 →
      (∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) ∨
      ∃ (uX : Polynomial F) (q g1 : BiPoly F),
        uX ≠ 0 ∧ q.IsPrimitive ∧ q ≠ 0 ∧ g1 ≠ 0 ∧
        q.natDegree = 2 ∧ g1.natDegree = 4 ∧
        q.derivative = 0 ∧ g1.derivative = 0 ∧
        h2 = C uX * q ∧ gPrim = q * g1 ∧
        IsRelPrime (h1.map (algebraMap (Polynomial F) (RatFunc F)))
                   (q.map (algebraMap (Polynomial F) (RatFunc F)))) := by
  classical
  let ι : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial F) (RatFunc F)
  have h2A_of_dX0 : B6401ContactKerD.dXBi gPrim = 0 →
      ∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro hdX0 j i hnz
    constructor
    · by_contra hne
      exact hnz ((dXBi_eq_zero_iff_even_X gPrim).mp hdX0 j i (by omega))
    · by_contra hne
      have hj0 := (deriv_eq_zero_iff_even_coeffs gPrim).mp hgP_d j (by omega)
      rw [hj0, Polynomial.coeff_zero] at hnz; exact hnz rfl
  constructor
  · intro hh2_0
    have hh2C : h2 = C (h2.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hh2_0
    have hc0_ne : h2.coeff 0 ≠ 0 := fun h => hh2_ne (by rw [hh2C, h, map_zero])
    have hdvd_self : gPrim ∣ B6401ContactKerD.dXBi gPrim := by
      refine hgP_prim.dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) ?_
      rcases hdvd_dX with ⟨w, hw⟩
      have hcι : ι (h2.coeff 0) ≠ 0 := fun h => hc0_ne (hι (h.trans (map_zero ι).symm))
      refine ⟨C (ι (h2.coeff 0))⁻¹ * w.map ι, ?_⟩
      have hm := congrArg (Polynomial.map ι) hw
      rw [Polynomial.map_mul, Polynomial.map_mul, hh2C, Polynomial.map_C] at hm
      have hm' := congrArg (· * C (ι (h2.coeff 0))⁻¹) hm
      simp only [mul_assoc, ← map_mul, mul_inv_cancel₀ hcι, map_one, mul_one] at hm'
      change (B6401ContactKerD.dXBi gPrim).map ι = gPrim.map ι * (C (ι (h2.coeff 0))⁻¹ * w.map ι)
      rw [hm']; ring
    exact h2A_of_dX0 (dXBi_eq_zero_of_dvd_dXBi hgP_ne hdvd_self)
  · intro hdg6 hh2_2
    let qK : Polynomial (RatFunc F) := EuclideanDomain.gcd (gPrim.map ι) (h2.map ι)
    have hqK_ne : qK ≠ 0 := fun h0 => ((Polynomial.map_ne_zero_iff hι).mpr hgP_ne) (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
    obtain ⟨q, hq_prim, hq_ne, hq_deg, hq_assoc⟩ := exists_prim_associated_ratFunc qK hqK_ne
    have hq_dvd_gP : q ∣ gPrim :=
      hq_prim.dvd_of_fraction_map_dvd_fraction_map (hq_assoc.dvd.trans (EuclideanDomain.gcd_dvd_left _ _))
    have hq_dvd_h2 : q ∣ h2 :=
      hq_prim.dvd_of_fraction_map_dvd_fraction_map (hq_assoc.dvd.trans (EuclideanDomain.gcd_dvd_right _ _))
    -- Prove q.derivative = 0 (since both gPrim.derivative = 0 and h2.derivative = 0, every irreducible
    -- with p.derivative ≠ 0 has even multiplicity in BOTH gPrim and h2, hence in q = gcd!)
    have hq_d : q.derivative = 0 := by
      by_contra hqd
      have hqK_d : (q.map ι).derivative ≠ 0 := by
        rw [Polynomial.derivative_map]; exact (Polynomial.map_ne_zero_iff hι).mpr hqd
      obtain ⟨pK, rK, k, hpK_irr, hpK_d, hqK_fac, hpK_ndvd_r⟩ :=
        exists_odd_irred_of_deriv_ne_zero (q.map ι).natDegree (q.map ι) le_rfl hqK_d
      obtain ⟨p, hp_prim, hp_ne, hp_deg, hp_assoc⟩ := exists_prim_associated_ratFunc pK hpK_irr.ne_zero
      have hp_irrK : Irreducible (p.map ι) := hp_assoc.irreducible_iff.mpr hpK_irr
      have hp_d : p.derivative ≠ 0 := by
        intro h0; apply hpK_d
        obtain ⟨u, hu⟩ := hp_assoc
        have hu_c : (u : Polynomial (RatFunc F)).derivative = 0 := by
          rw [Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit u.isUnit), Polynomial.derivative_C]
        rw [← hu, Polynomial.derivative_mul, Polynomial.derivative_map, h0, Polynomial.map_zero, hu_c]; simp
      have hex_max : ∀ (f : BiPoly F), f ≠ 0 → ∃ m r, f = p ^ m * r ∧ ¬ p ∣ r := by
        intro f hf0
        have hp_pos : 0 < p.natDegree := by rw [hp_deg]; exact natDegree_pos_of_irred hpK_irr
        have hfin : ∃ m : ℕ, ¬ p ^ (m + 1) ∣ f := ⟨f.natDegree, fun hd => by
          have hle := Polynomial.natDegree_le_of_dvd hd hf0; rw [Polynomial.natDegree_pow] at hle; nlinarith⟩
        let m := Nat.find hfin
        have hnot : ¬ p ^ (m + 1) ∣ f := Nat.find_spec hfin
        have hdvd : p ^ m ∣ f := by
          by_cases hm0 : m = 0
          · rw [hm0, pow_zero]; exact one_dvd _
          · have hlt := Nat.find_min hfin (show m - 1 < m by omega)
            push Not at hlt; rwa [show m - 1 + 1 = m by omega] at hlt
        rcases hdvd with ⟨r, hr⟩
        exact ⟨m, r, hr, fun ⟨s, hs⟩ => hnot ⟨s, by rw [hr, hs, pow_succ]; ring⟩⟩
      obtain ⟨e1, r1, hgP_p, hp_ndvd1⟩ := hex_max gPrim hgP_ne
      obtain ⟨e2, r2, hh2_p, hp_ndvd2⟩ := hex_max h2 hh2_ne
      have he1_ev := even_max_pow_of_deriv_eq_zero hp_prim hp_irrK hp_d hgP_ne hgP_d e1 r1 hgP_p hp_ndvd1
      have he2_ev := even_max_pow_of_deriv_eq_zero hp_prim hp_irrK hp_d hh2_ne hh2_d e2 r2 hh2_p hp_ndvd2
      have hp_dvd_q : p ^ (2 * k + 1) ∣ q :=
        (isPrimitive_pow_bi hp_prim (2 * k + 1)).dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) (by
          rw [Polynomial.map_pow, hqK_fac]; exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hp_assoc.dvd _) _)
      have hge1 : 2 * k + 1 ≤ e1 := by
        by_contra hlt
        have hd1 : p ^ (e1 + 1) ∣ p ^ e1 * r1 := (pow_dvd_pow p (by omega)).trans (hgP_p ▸ hp_dvd_q.trans hq_dvd_gP)
        rcases hd1 with ⟨s, hs⟩
        exact hp_ndvd1 ⟨s, mul_left_cancel₀ (pow_ne_zero _ hp_ne) (by rw [hs, pow_succ]; ring)⟩
      have hge2 : 2 * k + 1 ≤ e2 := by
        by_contra hlt
        have hd2 : p ^ (e2 + 1) ∣ p ^ e2 * r2 := (pow_dvd_pow p (by omega)).trans (hh2_p ▸ hp_dvd_q.trans hq_dvd_h2)
        rcases hd2 with ⟨s, hs⟩
        exact hp_ndvd2 ⟨s, mul_left_cancel₀ (pow_ne_zero _ hp_ne) (by rw [hs, pow_succ]; ring)⟩
      have hge1' : 2 * k + 2 ≤ e1 := by omega
      have hge2' : 2 * k + 2 ≤ e2 := by omega
      have hdK : pK ^ (2 * k + 2) ∣ pK ^ (2 * k + 1) * rK := by
        rw [← hqK_fac]
        refine (pow_dvd_pow_of_dvd hp_assoc.symm.dvd _).trans ((EuclideanDomain.dvd_gcd ?_ ?_).trans hq_assoc.symm.dvd)
        · exact (pow_dvd_pow _ hge1').trans (by rw [hgP_p, Polynomial.map_mul, Polynomial.map_pow]; exact dvd_mul_right _ _)
        · exact (pow_dvd_pow _ hge2').trans (by rw [hh2_p, Polynomial.map_mul, Polynomial.map_pow]; exact dvd_mul_right _ _)
      rcases hdK with ⟨s, hs⟩
      exact hpK_ndvd_r ⟨s, mul_left_cancel₀ (pow_ne_zero _ hpK_irr.ne_zero) (by rw [hs, pow_succ]; ring)⟩
    have hq_ev : q.natDegree % 2 = 0 := natDegree_even_of_deriv_eq_zero hq_d
    have hq_le2 : q.natDegree ≤ 2 := (Polynomial.natDegree_le_of_dvd hq_dvd_h2 hh2_ne).trans (le_of_eq hh2_2)
    rcases (show q.natDegree = 0 ∨ q.natDegree = 2 by omega) with hq0 | hq2
    · -- Subcase 2A: gcd_K(gPrim, h2) is a unit => IsRelPrime (gPrim.map ι) (h2.map ι) => gPrim ∣ dXBi gPrim => dXBi gPrim = 0!
      left
      have hqU : IsUnit qK := Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hqK_ne, ← hq_deg, hq0]; rfl)
      have hcop : IsCoprime (gPrim.map ι) (h2.map ι) := by
        obtain ⟨u, hu⟩ := hqU
        refine ⟨EuclideanDomain.gcdA (gPrim.map ι) (h2.map ι) * ↑u⁻¹,
                EuclideanDomain.gcdB (gPrim.map ι) (h2.map ι) * ↑u⁻¹, ?_⟩
        have hbez := EuclideanDomain.gcd_eq_gcd_ab (gPrim.map ι) (h2.map ι)
        change qK = _ at hbez; rw [← hu] at hbez
        calc EuclideanDomain.gcdA (gPrim.map ι) (h2.map ι) * ↑u⁻¹ * gPrim.map ι +
              EuclideanDomain.gcdB (gPrim.map ι) (h2.map ι) * ↑u⁻¹ * h2.map ι
            = (gPrim.map ι * EuclideanDomain.gcdA (gPrim.map ι) (h2.map ι) +
                h2.map ι * EuclideanDomain.gcdB (gPrim.map ι) (h2.map ι)) * ↑u⁻¹ := by ring
          _ = ↑u * ↑u⁻¹ := by rw [← hbez]
          _ = 1 := Units.mul_inv u
      have hdvdK : gPrim.map ι ∣ (B6401ContactKerD.dXBi gPrim).map ι := by
        refine hcop.dvd_of_dvd_mul_right ?_
        rcases hdvd_dX with ⟨w, hw⟩
        exact ⟨w.map ι, by rw [← Polynomial.map_mul, hw, Polynomial.map_mul]⟩
      exact h2A_of_dX0 (dXBi_eq_zero_of_dvd_dXBi hgP_ne (hgP_prim.dvd_of_fraction_map_dvd_fraction_map hdvdK))
    · -- Subcase 2B: deg_Y q = 2 => h2 = C uX * q, gPrim = q * g1!
      right
      rcases hq_dvd_gP with ⟨g1, hg1_eq⟩
      rcases hq_dvd_h2 with ⟨uPoly, hu_eq⟩
      have hg1_ne : g1 ≠ 0 := fun h0 => hgP_ne (by rw [hg1_eq, h0, mul_zero])
      have hu_ne : uPoly ≠ 0 := fun h0 => hh2_ne (by rw [hu_eq, h0, mul_zero])
      have hg1_deg : g1.natDegree = 4 := by
        have h := congrArg Polynomial.natDegree hg1_eq
        rw [hdg6, Polynomial.natDegree_mul hq_ne hg1_ne, hq2] at h; omega
      have hu_deg : uPoly.natDegree = 0 := by
        have h := congrArg Polynomial.natDegree hu_eq
        rw [hh2_2, Polynomial.natDegree_mul hq_ne hu_ne, hq2] at h; omega
      have huC : uPoly = C (uPoly.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hu_deg
      have huX_ne : uPoly.coeff 0 ≠ 0 := fun h => hu_ne (by rw [huC, h, map_zero])
      have hg1_d : g1.derivative = 0 := by
        have hd := congrArg Polynomial.derivative hg1_eq
        rw [hgP_d, Polynomial.derivative_mul, hq_d, zero_mul, zero_add] at hd
        exact (mul_eq_zero.mp hd.symm).resolve_left hq_ne
      have hrel_q : IsRelPrime (h1.map ι) (q.map ι) := by
        intro d hd1 hdq
        exact hrel hd1 (hdq.trans (by rw [hu_eq, Polynomial.map_mul]; exact dvd_mul_right _ _))
      exact ⟨uPoly.coeff 0, q, g1, huX_ne, hq_prim, hq_ne, hg1_ne, hq2, hg1_deg, hq_d, hg1_d,
        by conv_lhs => rw [hu_eq, huC, mul_comm], hg1_eq, hrel_q⟩

end KerD2UFD

end B6401SmallAlg
end ProximityPrize.SubmissionBinaryLower
