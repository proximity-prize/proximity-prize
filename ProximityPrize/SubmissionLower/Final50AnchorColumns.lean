import ProximityPrize.SubmissionLower.Final50RankReceiptBase
import ProximityPrize.SubmissionLower.Final50AnchorSpace
import Mathlib.Algebra.BigOperators.Intervals
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup5
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup10
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup15
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup20
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup25
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup30
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup35
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup40
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup45
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup50
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup55
import ProximityPrize.SubmissionLower.Final50RankBlocks
import ProximityPrize.SubmissionLower.PortLowBase
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Low50Euler2367JetDegree

-- merged module Final50RankReceiptGroup0
section Merged_Final50RankReceiptGroup0
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Final50RankReceipt
open K1_13_1_1 (bandCount)

private def cert0_0 := witnessFinal50 0 0 0 0 0 1 99
  0x0 (by decide +kernel)
private def chunks0 : List (Chunk 0) := [
  cert0_0]
def rows0 := rowsFrom chunks0

theorem good0 : ∀ r ∈ rows0, good 0 r = true := rowsFrom_good chunks0

theorem sorted0 : rows0.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks0 0 (by decide +kernel)).1

theorem mass0 (i : Fin 56) :
    bandCount 0 (i.val : ℤ) 55 14 ≤ (rows0.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks0).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 0 (j : ℤ) 55 14 ≤ mass j chunks0)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total0 : (rows0.map (price 0)).sum = 99 :=
  (total_eq chunks0).trans (by decide +kernel)

private def cert1_0 := witnessFinal50 1 3 0 64 64 1 99
  0x0 (by decide +kernel)
private def cert1_1 := witnessFinal50 1 2 0 10001 10001 1 99
  0x0 (by decide +kernel)
private def cert1_2 := witnessFinal50 1 1 0 20000 20000 1 99
  0x0 (by decide +kernel)
private def cert1_3 := witnessFinal50 1 0 0 30000 30000 1 95
  0x91 (by decide +kernel)
private def chunks1 : List (Chunk 1) := [
  cert1_0,
  cert1_1,
  cert1_2,
  cert1_3]
def rows1 := rowsFrom chunks1

theorem good1 : ∀ r ∈ rows1, good 1 r = true := rowsFrom_good chunks1

theorem sorted1 : rows1.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks1 0 (by decide +kernel)).1

theorem mass1 (i : Fin 56) :
    bandCount 1 (i.val : ℤ) 55 14 ≤ (rows1.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks1).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 1 (j : ℤ) 55 14 ≤ mass j chunks1)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total1 : (rows1.map (price 1)).sum = 392 :=
  (total_eq chunks1).trans (by decide +kernel)

private def cert2_0 := witnessFinal50 2 6 0 128 128 1 99
  0x0 (by decide +kernel)
private def cert2_1 := witnessFinal50 2 5 0 10065 10065 1 99
  0x0 (by decide +kernel)
private def cert2_2 := witnessFinal50 2 4 0 20002 20064 2 198
  0x0 (by decide +kernel)
private def cert2_3 := witnessFinal50 2 3 0 30001 30064 2 194
  0x488 (by decide +kernel)
private def cert2_4 := witnessFinal50 2 2 0 40000 40001 2 194
  0x488 (by decide +kernel)
private def cert2_5 := witnessFinal50 2 1 0 50000 50000 1 95
  0x91 (by decide +kernel)
private def cert2_6 := witnessFinal50 2 0 0 60000 60000 1 91
  0x111 (by decide +kernel)
private def chunks2 : List (Chunk 2) := [
  cert2_0,
  cert2_1,
  cert2_2,
  cert2_3,
  cert2_4,
  cert2_5,
  cert2_6]
def rows2 := rowsFrom chunks2

theorem good2 : ∀ r ∈ rows2, good 2 r = true := rowsFrom_good chunks2

theorem sorted2 : rows2.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks2 0 (by decide +kernel)).1

theorem mass2 (i : Fin 56) :
    bandCount 2 (i.val : ℤ) 55 14 ≤ (rows2.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks2).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 2 (j : ℤ) 55 14 ≤ mass j chunks2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total2 : (rows2.map (price 2)).sum = 970 :=
  (total_eq chunks2).trans (by decide +kernel)

private def cert3_0 := witnessFinal50 3 9 0 192 192 1 99
  0x0 (by decide +kernel)
private def cert3_1 := witnessFinal50 3 8 0 10129 10129 1 99
  0x0 (by decide +kernel)
private def cert3_2 := witnessFinal50 3 7 0 20066 20128 2 198
  0x0 (by decide +kernel)
private def cert3_3 := witnessFinal50 3 6 0 30003 30128 3 293
  0x2440 (by decide +kernel)
private def cert3_4 := witnessFinal50 3 5 0 40002 40065 3 293
  0x2440 (by decide +kernel)
private def cert3_5 := witnessFinal50 3 4 0 50001 50064 3 289
  0x244488 (by decide +kernel)
private def cert3_6 := witnessFinal50 3 3 0 60000 60064 3 285
  0x444488 (by decide +kernel)
private def cert3_7 := witnessFinal50 3 2 0 70000 70001 2 186
  0x88891 (by decide +kernel)
private def cert3_8 := witnessFinal50 3 1 0 80000 80000 1 91
  0x111 (by decide +kernel)
private def cert3_9 := witnessFinal50 3 0 0 90000 90000 1 87
  0x191 (by decide +kernel)
private def chunks3 : List (Chunk 3) := [
  cert3_0,
  cert3_1,
  cert3_2,
  cert3_3,
  cert3_4,
  cert3_5,
  cert3_6,
  cert3_7,
  cert3_8,
  cert3_9]
def rows3 := rowsFrom chunks3

theorem good3 : ∀ r ∈ rows3, good 3 r = true := rowsFrom_good chunks3

theorem sorted3 : rows3.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks3 0 (by decide +kernel)).1

theorem mass3 (i : Fin 56) :
    bandCount 3 (i.val : ℤ) 55 14 ≤ (rows3.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks3).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 3 (j : ℤ) 55 14 ≤ mass j chunks3)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total3 : (rows3.map (price 3)).sum = 1920 :=
  (total_eq chunks3).trans (by decide +kernel)

private def cert4_0 := witnessFinal50 4 12 0 256 256 1 99
  0x0 (by decide +kernel)
private def cert4_1 := witnessFinal50 4 11 0 10193 10193 1 99
  0x0 (by decide +kernel)
private def cert4_2 := witnessFinal50 4 10 0 20130 20192 2 198
  0x0 (by decide +kernel)
private def cert4_3 := witnessFinal50 4 9 0 30067 30192 3 293
  0x2440 (by decide +kernel)
private def cert4_4 := witnessFinal50 4 8 0 40004 40129 4 392
  0x12200 (by decide +kernel)
private def cert4_5 := witnessFinal50 4 7 0 50003 50128 4 388
  0x1222440 (by decide +kernel)
private def cert4_6 := witnessFinal50 4 6 0 60002 60128 5 479
  0x1111220488 (by decide +kernel)
private def cert4_7 := witnessFinal50 4 5 0 70001 70065 4 380
  0x222244488 (by decide +kernel)
private def cert4_8 := witnessFinal50 4 4 0 80000 80064 4 376
  0x222444488 (by decide +kernel)
private def cert4_9 := witnessFinal50 4 3 0 90000 90064 3 273
  0x64488891 (by decide +kernel)
private def cert4_10 := witnessFinal50 4 2 0 100000 100001 2 178
  0xc8911 (by decide +kernel)
private def cert4_11 := witnessFinal50 4 1 0 110000 110000 1 87
  0x191 (by decide +kernel)
private def cert4_12 := witnessFinal50 4 0 0 120000 120000 1 83
  0x211 (by decide +kernel)
private def chunks4 : List (Chunk 4) := [
  cert4_0,
  cert4_1,
  cert4_2,
  cert4_3,
  cert4_4,
  cert4_5,
  cert4_6,
  cert4_7,
  cert4_8,
  cert4_9,
  cert4_10,
  cert4_11,
  cert4_12]
def rows4 := rowsFrom chunks4

theorem good4 : ∀ r ∈ rows4, good 4 r = true := rowsFrom_good chunks4

theorem sorted4 : rows4.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks4 0 (by decide +kernel)).1

theorem mass4 (i : Fin 56) :
    bandCount 4 (i.val : ℤ) 55 14 ≤ (rows4.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks4).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 4 (j : ℤ) 55 14 ≤ mass j chunks4)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total4 : (rows4.map (price 4)).sum = 3325 :=
  (total_eq chunks4).trans (by decide +kernel)

end Final50RankReceipt
end Merged_Final50RankReceiptGroup0

-- merged module Final50RankReceiptSum
section Merged_Final50RankReceiptSum
set_option maxHeartbeats 2000000
namespace Final50RankReceipt
open Final50AnchorSpace (cap cap_le_index)
open Finset
open scoped BigOperators

private theorem triangle_succ (n : ℕ) :
    triangle (n+1) = triangle n + (n+1) := by
  unfold triangle
  have h : (n+1)*(n+1+1) = n*(n+1) + 2*(n+1) := by ring
  rw [h]
  omega

private theorem triangle_diff (x n : ℕ) :
    ∑ j ∈ range n, (x-j) = triangle x - triangle (x-n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases h : x ≤ n
    · have h' : x ≤ n+1 := by omega
      simp [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le h']
    · have hx : x-n = (x-(n+1))+1 := by omega
      have hle : triangle (x-n) ≤ triangle x := by
        apply Nat.div_le_div_right
        exact Nat.mul_le_mul (Nat.sub_le ..) (by omega)
      rw [hx, triangle_succ] at hle
      rw [hx, triangle_succ]
      omega

private def late (d : ℕ) : Finset ℕ :=
  (range (lateHi d - lateLo d)).image (fun s => lateLo d + s)

private def stages (d : ℕ) : Finset ℕ := insert d (late d)

private def inStage (d s : ℕ) : Prop := s = d ∨ lateLo d ≤ s ∧ s < lateHi d
private instance (d s : ℕ) : Decidable (inStage d s) := by unfold inStage; infer_instance

private theorem in_late (d s : ℕ) : s ∈ late d ↔ lateLo d ≤ s ∧ s < lateHi d := by
  unfold late
  rw [mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [mem_range] at hi
    omega
  · intro hs
    exact ⟨s - lateLo d, mem_range.mpr (by omega), by omega⟩

private theorem stage_bounds (d : ℕ) (hd : d < 56) :
    d < lateLo d ∧ lateLo d ≤ lateHi d ∧ lateHi d ≤ 133 := by
  have checks : (List.range 56).all (fun i => decide
      (i < lateLo i ∧ lateLo i ≤ lateHi i ∧ lateHi i ≤ 133)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks d (List.mem_range.mpr hd))

private theorem stages_eq (d : ℕ) (hd : d < 56) :
    (range 133).filter (fun s => cap s = d) = stages d := by
  have checks : (List.range 56).all (fun j =>
      (List.range 133).all (fun s => decide (cap s = j ↔ inStage j s))) = true := by decide +kernel
  ext s
  rw [mem_filter, mem_range, stages, mem_insert, in_late]
  by_cases hs : s < 133
  · have hh := of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp checks d (List.mem_range.mpr hd)) s (List.mem_range.mpr hs))
    simpa only [hs, true_and, inStage] using hh
  · obtain ⟨_, _, hhi⟩ := stage_bounds d hd
    simp [hs]
    omega

private theorem fee_add (s i : ℕ) (r : Row) : fee (s+i) r = fee s r - i := by
  unfold fee
  omega

private theorem sum_stage_fee (d : ℕ) (hd : d < 56) (r : Row) :
    ∑ s ∈ stages d, fee s r = price d r := by
  obtain ⟨hlo, hlen, _⟩ := stage_bounds d hd
  have hmiss : d ∉ late d := fun h => (Nat.not_le_of_gt hlo) ((in_late d d).mp h).1
  have hinj : Set.InjOn (fun s : ℕ => lateLo d+s) (↑(range (lateHi d-lateLo d))) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  rw [stages, sum_insert hmiss, late, sum_image hinj, price]
  simp_rw [fee_add (lateLo d)]
  rw [triangle_diff, ← fee_add, Nat.add_sub_of_le hlen]

private theorem exchange (st : Finset ℕ) (rows : List Row) :
    (∑ s ∈ st, ((rows.map (fee s)).sum)) =
      (rows.map (fun r => ∑ s ∈ st, fee s r)).sum := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem sum_fees (rows : ℕ → List Row) :
    (∑ s : Fin 133, ((rows (cap s)).map (fee s)).sum) =
      ∑ d : Fin 56, ((rows d).map (price d)).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun s => ((rows (cap s)).map (fee s)).sum) 133,
    Fin.sum_univ_eq_sum_range (fun d => ((rows d).map (price d)).sum) 56]
  calc
    _ = ∑ s ∈ range 133, ∑ d ∈ range 56,
          if cap s = d then ((rows d).map (fee s)).sum else 0 := by
        apply sum_congr rfl
        intro s hs
        rw [sum_eq_single (cap s)]
        · simp
        · intro d hd hne
          simp [Ne.symm hne]
        · intro he
          exact (he (mem_range.mpr (Nat.lt_succ_of_le (cap_le_index s)))).elim
    _ = ∑ d ∈ range 56, ((rows d).map (price d)).sum := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d hd
        rw [← sum_filter, stages_eq d (mem_range.mp hd), exchange]
        simp_rw [sum_stage_fee d (mem_range.mp hd)]

end Final50RankReceipt
end Merged_Final50RankReceiptSum

-- merged module Final50RankReceipt
section Merged_Final50RankReceipt
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000

namespace Final50RankReceipt
open scoped BigOperators
open K1_13_1_1 (bandCount)
open Final50AnchorSpace (cap)

def rows : ℕ → List Row
  | 0 => rows0
  | 1 => rows1
  | 2 => rows2
  | 3 => rows3
  | 4 => rows4
  | 5 => rows5
  | 6 => rows6
  | 7 => rows7
  | 8 => rows8
  | 9 => rows9
  | 10 => rows10
  | 11 => rows11
  | 12 => rows12
  | 13 => rows13
  | 14 => rows14
  | 15 => rows15
  | 16 => rows16
  | 17 => rows17
  | 18 => rows18
  | 19 => rows19
  | 20 => rows20
  | 21 => rows21
  | 22 => rows22
  | 23 => rows23
  | 24 => rows24
  | 25 => rows25
  | 26 => rows26
  | 27 => rows27
  | 28 => rows28
  | 29 => rows29
  | 30 => rows30
  | 31 => rows31
  | 32 => rows32
  | 33 => rows33
  | 34 => rows34
  | 35 => rows35
  | 36 => rows36
  | 37 => rows37
  | 38 => rows38
  | 39 => rows39
  | 40 => rows40
  | 41 => rows41
  | 42 => rows42
  | 43 => rows43
  | 44 => rows44
  | 45 => rows45
  | 46 => rows46
  | 47 => rows47
  | 48 => rows48
  | 49 => rows49
  | 50 => rows50
  | 51 => rows51
  | 52 => rows52
  | 53 => rows53
  | 54 => rows54
  | 55 => rows55
  | _ => []

private def expected : ℕ → ℕ
  | 0 => 99
  | 1 => 392
  | 2 => 970
  | 3 => 1920
  | 4 => 3325
  | 5 => 5264
  | 6 => 7812
  | 7 => 11040
  | 8 => 15015
  | 9 => 19800
  | 10 => 25454
  | 11 => 32032
  | 12 => 39585
  | 13 => 48160
  | 14 => 57800
  | 15 => 68460
  | 16 => 80095
  | 17 => 92660
  | 18 => 106110
  | 19 => 120400
  | 20 => 135485
  | 21 => 151242
  | 22 => 167321
  | 23 => 183388
  | 24 => 199125
  | 25 => 214230
  | 26 => 228417
  | 27 => 241416
  | 28 => 252973
  | 29 => 263130
  | 30 => 271929
  | 31 => 279480
  | 32 => 285822
  | 33 => 291060
  | 34 => 295506
  | 35 => 298985
  | 36 => 301762
  | 37 => 303703
  | 38 => 305030
  | 39 => 305646
  | 40 => 305733
  | 41 => 305226
  | 42 => 304271
  | 43 => 302831
  | 44 => 301020
  | 45 => 298826
  | 46 => 296335
  | 47 => 293556
  | 48 => 290551
  | 49 => 287347
  | 50 => 283987
  | 51 => 280510
  | 52 => 276945
  | 53 => 273339
  | 54 => 269711
  | 55 => 6481793
  | _ => 0

theorem rows_good (d : Fin 56) : ∀ r ∈ rows d, good d r = true := by
  fin_cases d
  · exact good0
  · exact good1
  · exact good2
  · exact good3
  · exact good4
  · exact good5
  · exact good6
  · exact good7
  · exact good8
  · exact good9
  · exact good10
  · exact good11
  · exact good12
  · exact good13
  · exact good14
  · exact good15
  · exact good16
  · exact good17
  · exact good18
  · exact good19
  · exact good20
  · exact good21
  · exact good22
  · exact good23
  · exact good24
  · exact good25
  · exact good26
  · exact good27
  · exact good28
  · exact good29
  · exact good30
  · exact good31
  · exact good32
  · exact good33
  · exact good34
  · exact good35
  · exact good36
  · exact good37
  · exact good38
  · exact good39
  · exact good40
  · exact good41
  · exact good42
  · exact good43
  · exact good44
  · exact good45
  · exact good46
  · exact good47
  · exact good48
  · exact good49
  · exact good50
  · exact good51
  · exact good52
  · exact good53
  · exact good54
  · exact good55
theorem rows_sorted (d : Fin 56) : (rows d).Pairwise (fun a b => a.tag < b.tag) := by
  fin_cases d
  · exact sorted0
  · exact sorted1
  · exact sorted2
  · exact sorted3
  · exact sorted4
  · exact sorted5
  · exact sorted6
  · exact sorted7
  · exact sorted8
  · exact sorted9
  · exact sorted10
  · exact sorted11
  · exact sorted12
  · exact sorted13
  · exact sorted14
  · exact sorted15
  · exact sorted16
  · exact sorted17
  · exact sorted18
  · exact sorted19
  · exact sorted20
  · exact sorted21
  · exact sorted22
  · exact sorted23
  · exact sorted24
  · exact sorted25
  · exact sorted26
  · exact sorted27
  · exact sorted28
  · exact sorted29
  · exact sorted30
  · exact sorted31
  · exact sorted32
  · exact sorted33
  · exact sorted34
  · exact sorted35
  · exact sorted36
  · exact sorted37
  · exact sorted38
  · exact sorted39
  · exact sorted40
  · exact sorted41
  · exact sorted42
  · exact sorted43
  · exact sorted44
  · exact sorted45
  · exact sorted46
  · exact sorted47
  · exact sorted48
  · exact sorted49
  · exact sorted50
  · exact sorted51
  · exact sorted52
  · exact sorted53
  · exact sorted54
  · exact sorted55
theorem rows_cover (d i : Fin 56) :
    bandCount d (i.val : ℤ) 55 14 ≤ ((rows d).filter (fun r => decide (i.val ≤ r.index))).length := by
  fin_cases d
  · exact mass0 i
  · exact mass1 i
  · exact mass2 i
  · exact mass3 i
  · exact mass4 i
  · exact mass5 i
  · exact mass6 i
  · exact mass7 i
  · exact mass8 i
  · exact mass9 i
  · exact mass10 i
  · exact mass11 i
  · exact mass12 i
  · exact mass13 i
  · exact mass14 i
  · exact mass15 i
  · exact mass16 i
  · exact mass17 i
  · exact mass18 i
  · exact mass19 i
  · exact mass20 i
  · exact mass21 i
  · exact mass22 i
  · exact mass23 i
  · exact mass24 i
  · exact mass25 i
  · exact mass26 i
  · exact mass27 i
  · exact mass28 i
  · exact mass29 i
  · exact mass30 i
  · exact mass31 i
  · exact mass32 i
  · exact mass33 i
  · exact mass34 i
  · exact mass35 i
  · exact mass36 i
  · exact mass37 i
  · exact mass38 i
  · exact mass39 i
  · exact mass40 i
  · exact mass41 i
  · exact mass42 i
  · exact mass43 i
  · exact mass44 i
  · exact mass45 i
  · exact mass46 i
  · exact mass47 i
  · exact mass48 i
  · exact mass49 i
  · exact mass50 i
  · exact mass51 i
  · exact mass52 i
  · exact mass53 i
  · exact mass54 i
  · exact mass55 i

private theorem rows_price (d : Fin 56) :
    ((rows d).map (price d)).sum = expected d := by
  fin_cases d
  · exact total0
  · exact total1
  · exact total2
  · exact total3
  · exact total4
  · exact total5
  · exact total6
  · exact total7
  · exact total8
  · exact total9
  · exact total10
  · exact total11
  · exact total12
  · exact total13
  · exact total14
  · exact total15
  · exact total16
  · exact total17
  · exact total18
  · exact total19
  · exact total20
  · exact total21
  · exact total22
  · exact total23
  · exact total24
  · exact total25
  · exact total26
  · exact total27
  · exact total28
  · exact total29
  · exact total30
  · exact total31
  · exact total32
  · exact total33
  · exact total34
  · exact total35
  · exact total36
  · exact total37
  · exact total38
  · exact total39
  · exact total40
  · exact total41
  · exact total42
  · exact total43
  · exact total44
  · exact total45
  · exact total46
  · exact total47
  · exact total48
  · exact total49
  · exact total50
  · exact total51
  · exact total52
  · exact total53
  · exact total54
  · exact total55


theorem total_fees :
    (∑ s : Fin 133, ((rows (cap s)).map (fee s)).sum) = 16564024 := by
  rw [sum_fees]
  simp_rw [rows_price]
  rw [Fin.sum_univ_eq_sum_range expected 56]
  decide +kernel

#print axioms rows_good
#print axioms rows_sorted
#print axioms rows_cover
#print axioms total_fees

end Final50RankReceipt
end Merged_Final50RankReceipt

-- merged module Final50Rank
section Merged_Final50Rank
namespace Final50Rank
open K1_13 (Geom InBox Row shape extend atJet)
open K1 (I K node)
open Final50AnchorSpace (cap anchorLocal)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 16564024 := by
  apply Final50RankBlocks.origin_le_blocks.trans
  calc
    _ ≤ ∑ s : Fin 133, Final50RankCore.gradeFee s (Final50RankReceipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d : Fin 56 := ⟨cap s,Nat.lt_succ_of_le (Final50AnchorSpace.cap_le_index s)⟩
      exact Final50RankCore.grade_bound s d (Final50RankReceipt.rows d)
        (Final50RankReceipt.rows_good d) (Final50RankReceipt.rows_sorted d) (Final50RankReceipt.rows_cover d)
    _ = _ := Final50RankReceipt.total_fees

#print axioms origin_rank
end Final50Rank
end Merged_Final50Rank

-- merged module Low50AnchorSpace
section Merged_Low50AnchorSpace
set_option maxHeartbeats 2000000
end Merged_Low50AnchorSpace

-- merged module Low50AnchorDimension
section Merged_Low50AnchorDimension
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
end Merged_Low50AnchorDimension

-- merged module Low50Anchor
section Merged_Low50Anchor
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace Low50Anchor
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
/-- Bound the sum of the total and differentiated degrees at each monomial. -/
def ActiveFits (P : Row 4) (n : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ n
end
end Low50Anchor
end Merged_Low50Anchor

-- merged module Final50AnchorLocal
section Merged_Final50AnchorLocal
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

namespace Final50AnchorLocal
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Final50AnchorSpace (gradeLimit gradeLimit_antitone cap_of_grade cap_active AnchorEligible anchorLocal anchorSpace)
open scoped BigOperators
open private atJet_unflatten from ProximityPrize.SubmissionLower.Fast040
open private exponent_le_of_mem_translation_monomial from ProximityPrize.SubmissionLower.Fast064

abbrev WideEligible := AnchorEligible
abbrev wideSpace := anchorSpace
abbrev wideLocal := anchorLocal

section
open MvPolynomial

private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 99)
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu : 99 ≤ u none) :
    localConstraintAt 99 0 0 (monomial u a) = 0 := by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3) = monomial u a := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul, Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 99 0 0 _).mpr
  intro e he
  rw [map_mul, map_pow, unscaledLocalSubstitution, bind₁_X_right]
  simp only [unscaledLocalImage, MvPolynomial.C_0, zero_add, MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none ≤ e (localT 3) → False
  omega
private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 99 0 0 (truncateX Q) = localConstraintAt 99 0 0 Q := by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 99 then monomial u (Q.coeff u) else 0 := by
    ext v
    rw [truncateX, coeff_filterSupport]
    by_cases h : u = v
    · subst v
      by_cases hx : u none < 99 <;> simp [hx]
    · by_cases hx : u none < 99 <;> simp [hx, MvPolynomial.coeff_monomial, h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero, origin_monomial_zero _ _ (by omega)]

private theorem centered {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : WideEligible u) (hx : v none < 99) :
    AnchorEligible v := by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hi : v.some.weight (fun i => i.val) ≤ u.some.weight (fun i => i.val) := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right j.val (h (some j))
  obtain ⟨hdeg,hidx,ht,htail,_⟩ := hu
  have hsum := add_le_add (add_le_add (h (some 1)) (h (some 2))) (h (some 3))
  refine ⟨hd.trans hdeg,hi.trans hidx,(h _).trans ht,hd.trans (htail.trans (gradeLimit_antitone hsum)),?_⟩
  have hw := Finsupp.weight_le_weight
    (w := fun j : Fin 4 => 133484 - j.val) (w' := fun _ => 133484)
    (fun j => Nat.sub_le _ _) v.some
  have he : v.some.weight (fun _ => 133484) = 133484 * v.some.degree := by
    simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
      Finset.mul_sum, Nat.mul_comm]
  rw [he] at hw
  have hweight : differentialWeight (d := 3) 133484 =
      fun j => j.elim 1 (fun i => 133484 - i.val) := by
    funext j
    cases j <;> rfl
  rw [← Finsupp.optionElim_some v, hweight, Finsupp.weight_optionElim, one_mul]
  calc
    _ ≤ 98 + 133484 * 132 :=
      Nat.add_le_add (Nat.le_of_lt_succ hx)
        (hw.trans (Nat.mul_le_mul_left _ (hd.trans hdeg)))
    _ ≤ _ := by decide
private theorem centered_in_space (x y : Geom) (Q : wideSpace) :
    truncateX (globalPointTranslation x y (Q : DifferentialPolynomial Geom 3)) ∈
      anchorSpace := by
  classical
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn := mem_support_iff.mp hv
  rw [truncateX, coeff_filterSupport] at hn
  split at hn
  · exact centered
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (Q.property hu) (by assumption)
  · exact (hn rfl).elim
theorem rank_at_point_le_origin (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
  have hpositive (j : JetVariable 3) : differentialWeight 133484 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133484 - j.val ≠ 0
      omega
  have : Module.Finite Geom anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let f : wideSpace →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict wideSpace
  let tr : wideSpace →ₗ[Geom] anchorSpace := f.codRestrict _ fun Q =>
    centered_in_space x y Q
  have he : wideLocal x y = (anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 99 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 99 0 0 (truncateX (globalPointTranslation x y Q))
    rw [origin_truncateX,localConstraintAt_eq_zero_globalPointTranslation]
  rw [he]
  exact LinearMap.finrank_range_comp_le_left _ _

end

theorem per_position (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤ 16564024 :=
  (rank_at_point_le_origin x y).trans Final50Rank.origin_rank

theorem finiteWide : Module.Finite Geom wideSpace := by
  have hpositive (j : JetVariable 3) : differentialWeight 133484 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133484 - j.val ≠ 0
      omega
  exact MvPolynomial.restrictSupport_finite <|
    (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2

theorem shape_bound (Q : wideSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨132, 55, 14⟩ := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, WideEligible (m.optionElim i) := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i, hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.degree_apply, Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 14
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1

theorem active_bound (Q : wideSpace) :
    Low50Anchor.ActiveFits (MvPolynomial.optionEquivRight Geom (Fin 4) Q) 165 := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  intro m hm
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hm)
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have h : WideEligible (m.optionElim i) := hQ (MvPolynomial.mem_support_iff.mpr (by
    rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff]))
  have hd := h.1
  have hl := h.2.2.2.1
  have hw := h.2.1
  simp only [Finsupp.optionElim_apply_some] at hl
  rw [Finsupp.some_optionElim] at hd hw
  have hdeg : m.degree = m 0 + m 1 + m 2 + m 3 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have hweight : m.weight (fun i : Fin 4 => i.val) = m 1 + 2 * m 2 + 3 * m 3 := by
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_four]
    simp [Nat.mul_comm, Nat.add_assoc]
  change m.weight (fun i : Fin 4 => i.val) ≤ 55 at hw
  rw [hweight] at hw
  have hc := cap_of_grade (s := m.degree) (t := m 1 + m 2 + m 3)
    (by omega) (by omega) (by simpa [Finsupp.some_optionElim] using hl)
  have hb := cap_active _ hd
  omega

theorem rawWeight (Q : wideSpace) :
    differentialWeightedDegree 133484 (Q : DifferentialPolynomial Geom 3) ≤
      99 * 179886 - 1 + 55 := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  exact fun m hm => (Q.property hm).2.2.2.2

#print axioms per_position
#print axioms shape_bound
#print axioms active_bound

end
end Final50AnchorLocal
end Merged_Final50AnchorLocal


set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open K1 K1_13 K1_13_1_1 PolynomialDifferential ReedSolomon.HiddenDerivative
open MvPolynomial
open scoped BigOperators Polynomial

namespace Final50AnchorColumns
noncomputable section

abbrev Ex := JetVariable 3 →₀ ℕ
abbrev DP := DifferentialPolynomial Geom 3

def jidx (u : Ex) : ℕ := u.some.weight Fin.val
def jdeg (u : Ex) : ℕ := u.some.degree
def jdiff (u : Ex) : ℕ := u (some 1) + u (some 2) + u (some 3)

@[simp] theorem jidx_add (u v : Ex) : jidx (u + v) = jidx u + jidx v := by
  simp [jidx, Finsupp.some_add]
@[simp] theorem jdeg_add (u v : Ex) : jdeg (u + v) = jdeg u + jdeg v := by
  simp [jdeg, Finsupp.some_add]
@[simp] theorem jdiff_add (u v : Ex) : jdiff (u + v) = jdiff u + jdiff v := by
  unfold jdiff
  simp only [Finsupp.add_apply]
  omega

def top (u : Ex) : Ex := u + Finsupp.single none (jidx u)

@[simp] theorem top_add (u v : Ex) : top (u + v) = top u + top v := by
  rw [top, jidx_add, Finsupp.single_add]
  unfold top
  abel

def Related (u v : Ex) : Prop :=
  jdeg v = jdeg u ∧ jidx v ≤ jidx u ∧ jdiff v ≤ jdiff u ∧
    v (some 3) ≤ u (some 3) ∧ v none = u none + jidx v

theorem Related.add {u v a b : Ex} (h : Related u a) (k : Related v b) :
    Related (u+v) (a+b) := by
  obtain ⟨hd,hi,hf,ht,hx⟩ := h
  obtain ⟨kd,ki,kf,kt,kx⟩ := k
  unfold Related
  simp only [jdeg_add, jidx_add, jdiff_add, Finsupp.add_apply]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem top_related (u : Ex) : Related u (top u) := by
  unfold top Related jdeg jidx jdiff
  simp [Finsupp.some_add, Finsupp.some_single_none]

def Bounded (u : Ex) (P : DP) : Prop :=
  ∀ v ∈ P.support, Related u v ∧ jidx v < jidx u

def HasTop (u : Ex) (a : Geom) (P : DP) : Prop :=
  ∃ L, P = monomial (top u) a + L ∧ Bounded u L

private theorem bounded_add {u : Ex} {P Q : DP} (h : Bounded u P) (k : Bounded u Q) :
    Bounded u (P+Q) := by
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim (h v) (k v)

private theorem monomial_related {u : Ex} {a : Geom} {v : Ex}
    (h : v ∈ (monomial (top u) a).support) : Related u v := by
  have hv := Finset.mem_singleton.mp (support_monomial_subset h)
  simpa only [hv] using top_related u

private theorem top_idx (u : Ex) : jidx (top u) = jidx u := by
  unfold jidx top
  simp [Finsupp.some_add, Finsupp.some_single_none]

private theorem bounded_mul_left {u v : Ex} {P Q : DP} (h : Bounded u P)
    (k : ∀ a ∈ Q.support, Related v a) : Bounded (u+v) (P*Q) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hz)
  obtain ⟨hr, hi⟩ := h a ha
  have hk := k b hb
  exact ⟨hr.add hk, by simpa using Nat.add_lt_add_of_lt_of_le hi hk.2.1⟩

private theorem bounded_mul_right {u v : Ex} {P Q : DP} (h : ∀ a ∈ P.support, Related u a)
    (k : Bounded v Q) : Bounded (u+v) (P*Q) := by
  rw [add_comm, mul_comm]
  exact bounded_mul_left k h

theorem HasTop.mul {u v : Ex} {a b : Geom} {P Q : DP} (h : HasTop u a P)
    (k : HasTop v b Q) : HasTop (u+v) (a*b) (P*Q) := by
  obtain ⟨L, rfl, hL⟩ := h
  obtain ⟨M, rfl, hM⟩ := k
  refine ⟨monomial (top u) a * M + L * monomial (top v) b + L*M, ?_, ?_⟩
  · rw [top_add, ← monomial_mul_monomial]
    ring
  · refine bounded_add (bounded_add ?_ ?_) ?_
    · exact bounded_mul_right (fun b hb => monomial_related hb) hM
    · exact bounded_mul_left hL (fun b hb => monomial_related hb)
    · exact bounded_mul_left hL (fun b hb => (hM b hb).1)

theorem HasTop.support {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    ∀ v ∈ P.support, Related u v := by
  obtain ⟨L,rfl,hL⟩ := h
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim (fun h => monomial_related h) (fun h => (hL v h).1)

theorem HasTop.lower {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    ∀ v ∈ P.support, v = top u ∨ jidx v < jidx u := by
  obtain ⟨L,rfl,hL⟩ := h
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim
    (fun h => Or.inl (Finset.mem_singleton.mp (support_monomial_subset h))) (fun h => Or.inr (hL v h).2)

theorem HasTop.coeff {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    P.coeff (top u) = a := by
  obtain ⟨L,rfl,hL⟩ := h
  have hzero : L.coeff (top u) = 0 := by
    apply notMem_support_iff.mp
    intro hz
    have hh := (hL _ hz).2
    rw [top_idx] at hh
    exact (lt_irrefl _) hh
  simp [hzero]

theorem HasTop.pow {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) (n : ℕ) :
    HasTop (n • u) (a^n) (P^n) := by
  induction n with
  | zero =>
    refine ⟨0, ?_, by simp [Bounded]⟩
    simp [top,jidx,monomial_zero']
  | succ n ih =>
    rw [pow_succ, pow_succ, succ_nsmul]
    exact ih.mul h

private def eulTerm (i k : ℕ) (hk : k < 4) : DP :=
  monomial (Finsupp.single none k + Finsupp.single (some ⟨k,hk⟩) 1)
    ((-1 : Geom)^k * (133484-k).choose (i-k))

def eul (i : Fin 4) : DP :=
  ∑ k : Fin (i.val+1), eulTerm i.val k.val (by omega)

private theorem eulTerm_related (i k : Fin 4) (h : k ≤ i) :
    Related (Finsupp.single (some i) 1)
      (Finsupp.single none k.val + Finsupp.single (some k) 1) := by
  have hval : k.val ≤ i.val := h
  simp only [Related, jdeg, jidx, jdiff, Finsupp.some_add, Finsupp.some_single_none,
    zero_add, Finsupp.some_single_some, Finsupp.degree_single, Finsupp.weight_single,
    nsmul_eq_mul, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Option.some.injEq]
  fin_cases k <;> fin_cases i <;> (first | contradiction | decide)


theorem eul_top (i : Fin 4) : HasTop (Finsupp.single (some i) 1) ((-1 : Geom)^i.val) (eul i) := by
  rw [eul, Fin.sum_univ_castSucc]
  let L := ∑ k : Fin i.val, eulTerm i.val k.val (by omega)
  have he : eulTerm i.val i.val i.isLt =
      monomial (top (Finsupp.single (some i) 1)) ((-1 : Geom)^i.val) := by
    simp [eulTerm,top,jidx,Finsupp.some_single_some, Finsupp.weight_single,add_comm]
  refine ⟨L, ?_, ?_⟩
  · rw [add_comm]
    congr 1
  · intro v hv
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp (support_sum hv)
    have hv' := Finset.mem_singleton.mp (support_monomial_subset hk)
    subst v
    refine ⟨eulTerm_related i ⟨k,by omega⟩ (by exact k.isLt.le), ?_⟩
    simp [jidx,Finsupp.some_add,Finsupp.some_single_none,Finsupp.some_single_some,Finsupp.weight_single, k.isLt]


def ColumnEligible (u : Ex) : Prop :=
  jdeg u ≤ 132 ∧ jidx u ≤ 55 ∧ u (some 3) ≤ 14 ∧
    jdeg u ≤ Final50AnchorSpace.gradeLimit (jdiff u) ∧
    u none + 133484*jdeg u < 99*179886 + 2*jidx u

private def orth (u : Ex) : DP :=
  eul 0 ^ u (some 0) * eul 1 ^ u (some 1) *
    eul 2 ^ u (some 2) * eul 3 ^ u (some 3)

private def jetOnly (u : Ex) : Ex := u.some.optionElim 0

private theorem normalized_jet (u : Ex) :
    u (some 0) • Finsupp.single (some (0 : Fin 4)) 1 +
      u (some 1) • Finsupp.single (some (1 : Fin 4)) 1 +
      u (some 2) • Finsupp.single (some (2 : Fin 4)) 1 +
      u (some 3) • Finsupp.single (some (3 : Fin 4)) 1 = jetOnly u := by
  ext k
  cases k with
  | none => simp [jetOnly]
  | some k => fin_cases k <;> simp [jetOnly]

private def sign (u : Ex) : Geom :=
  ((-1 : Geom)^0) ^ u (some 0) * ((-1 : Geom)^1) ^ u (some 1) *
    ((-1 : Geom)^2) ^ u (some 2) * ((-1 : Geom)^3) ^ u (some 3)

private theorem sign_ne_zero (u : Ex) : sign u ≠ 0 := by simp [sign]

private theorem orth_top (u : Ex) : HasTop (jetOnly u) (sign u) (orth u) := by
  rw [← normalized_jet]
  exact ((((eul_top 0).pow _).mul ((eul_top 1).pow _)).mul ((eul_top 2).pow _)).mul ((eul_top 3).pow _)

private theorem single_top (x : ℕ) : HasTop (Finsupp.single none x) 1
    (monomial (Finsupp.single none x) 1) := by
  refine ⟨0, ?_, by simp [Bounded]⟩
  simp [top,jidx,Finsupp.some_single_none]

private def adjusted (u : Ex) : Ex :=
  Finsupp.single none (u none - jidx u) + jetOnly u

private theorem adjusted_idx (u : Ex) : jidx (adjusted u) = jidx u := by
  rw [adjusted,jidx,Finsupp.some_add,Finsupp.some_single_none,zero_add,jetOnly,Finsupp.some_optionElim]
  rfl

private theorem adjusted_top (u : Ex) (h : jidx u ≤ u none) : top (adjusted u) = u := by
  rw [top,adjusted_idx]
  ext k
  cases k with
  | none => simp [adjusted,jetOnly,Nat.sub_add_cancel h]
  | some k => simp [adjusted,jetOnly]

def column (u : Ex) : DP :=
  if u none < jidx u then monomial u 1 else
    monomial (Finsupp.single none (u none - jidx u)) 1 * orth u

private theorem column_hasTop (u : Ex) (h : ¬ u none < jidx u) :
    HasTop (adjusted u) (sign u) (column u) := by
  simpa only [column, ite_eq_right h, one_mul, adjusted] using (single_top _).mul (orth_top u)

theorem column_coeff (u : Ex) : (column u).coeff u ≠ 0 := by
  by_cases h : u none < jidx u
  · simp [column,h]
  · have he := (column_hasTop u h).coeff
    rw [adjusted_top u (Nat.le_of_not_gt h)] at he
    rw [he]
    exact sign_ne_zero u

theorem column_lower (u v : Ex) (h : v ≠ u) (hle : jidx u ≤ jidx v) :
    (column u).coeff v = 0 := by
  apply notMem_support_iff.mp
  intro hv
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut] at hv
    exact h (Finset.mem_singleton.mp (support_monomial_subset hv))
  · obtain he | hl := (column_hasTop u hcut).lower v hv
    · exact h (he.trans (adjusted_top u (Nat.le_of_not_gt hcut)))
    · rw [adjusted_idx] at hl
      omega

private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]

private theorem weight_formula (u : Ex) :
    u.weight (differentialWeight 133484) + jidx u = u none + 133484*jdeg u := by
  have he : differentialWeight (d := 3) 133484 = fun i =>
      i.elim 1 (fun k => 133484 - k.val) := by
    funext i
    cases i <;> rfl
  conv_lhs => enter [1]; rw [← Finsupp.optionElim_some u,he,Finsupp.weight_optionElim,one_mul]
  unfold jidx jdeg
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight, jet_weight]
  change u none + (u.some 0*133484 + u.some 1*133483 + u.some 2*133482 + u.some 3*133481) +
      (u.some 0*0 + u.some 1*1 + u.some 2*2 + u.some 3*3) =
    u none + 133484 * (u.some 0*1 + u.some 1*1 + u.some 2*1 + u.some 3*1)
  omega

private theorem adjusted_shape (u : Ex) :
    jdeg (adjusted u) = jdeg u ∧ jdiff (adjusted u) = jdiff u ∧
      adjusted u (some 3) = u (some 3) ∧ adjusted u none = u none - jidx u := by
  have he : (adjusted u).some = u.some := by
    rw [adjusted,Finsupp.some_add,Finsupp.some_single_none,zero_add,jetOnly,Finsupp.some_optionElim]
  change (adjusted u).some.degree = u.some.degree ∧ _ ∧ _ ∧ _
  rw [he]
  simp [adjusted,jetOnly,jdiff]

theorem column_wide {u : Ex} (h : ColumnEligible u) :
    column u ∈ Final50AnchorLocal.wideSpace := by
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro v hv
  obtain ⟨hd,hi,ht,hf,hw⟩ := h
  have hvw := weight_formula v
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut] at hv
    have he := Finset.mem_singleton.mp (support_monomial_subset hv)
    subst v
    refine ⟨hd,hi,ht,hf,?_⟩
    omega
  · obtain ⟨hvd,hvi,hvf,hvt,hvx⟩ := (column_hasTop u hcut).support v hv
    obtain ⟨had,haf,hat,hax⟩ := adjusted_shape u
    rw [had] at hvd
    rw [adjusted_idx] at hvi
    rw [haf] at hvf
    rw [hat] at hvt
    rw [hax] at hvx
    refine ⟨hvd.le.trans hd,hvi.trans hi,hvt.trans ht,?_ ,?_⟩
    · exact hvd.le.trans (hf.trans (Final50AnchorSpace.gradeLimit_antitone hvf))
    · omega



private theorem spec_eul (S : Geom[X]) (i : Fin 4) :
    differentialSpecializationHom S (eul i) = EulerJetDegree.euler 133484 i.val S := by
  rw [eul, map_sum, EulerJetDegree.euler, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold eulTerm
  rw [monomial_add_single, pow_one, ← MvPolynomial.C_mul_X_pow_eq_monomial,
    map_mul, map_mul, map_pow]
  simp [differentialSpecializationHom, mul_assoc]

private theorem natDegree_prod_bound (S : Geom[X]) (u : Ex) (hS : S.natDegree ≤ 133484) :
    (differentialSpecializationHom S (orth u)).natDegree ≤ 133484*jdeg u - jidx u := by
  rw [orth,map_mul,map_mul,map_mul,map_pow,map_pow,map_pow,map_pow,spec_eul,spec_eul,spec_eul,spec_eul]
  have hh (i : Fin 4) := (Polynomial.natDegree_pow_le
    (p := EulerJetDegree.euler 133484 i.val S) (n := u (some i))).trans
      (Nat.mul_le_mul_left _ (EulerJetDegree.natDegree_euler_le_sub (i := i.val) hS))
  have ha := Polynomial.natDegree_mul_le.trans (Nat.add_le_add
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hh 0) (hh 1))) (hh 2))) (hh 3))
  refine ha.trans ?_
  rw [jdeg, Finsupp.degree_eq_weight_one, jidx, jet_weight, jet_weight]
  change (u (some 0)*133484 + u (some 1)*133483 + u (some 2)*133482 + u (some 3)*133481) ≤
    133484 * (u (some 0)*1+u (some 1)*1+u (some 2)*1+u (some 3)*1) -
    (u (some 0)*0+u (some 1)*1+u (some 2)*2+u (some 3)*3)
  omega

theorem column_eval_degree (S : Geom[X]) {u : Ex} (h : ColumnEligible u)
    (hs : S.natDegree ≤ 133484) :
    (differentialSpecialization (column u) S).natDegree ≤ 99 * 179886 - 1 := by
  obtain ⟨hd,hi,_,_,hw⟩ := h
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut]
    apply (natDegree_differentialSpecialization_le _ _ hs).trans
    rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
    intro v hv
    have he := Finset.mem_singleton.mp (support_monomial_subset hv)
    subst v
    have hf := weight_formula u
    omega
  · change (differentialSpecializationHom S (column u)).natDegree ≤ _
    rw [column,ite_eq_right hcut,map_mul,← MvPolynomial.X_pow_eq_monomial,map_pow]
    have hx : differentialSpecializationHom S (MvPolynomial.X none : DP) = Polynomial.X := by
      simp [differentialSpecializationHom]
    rw [hx]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_X_pow]
    · have hrel := natDegree_prod_bound S u hs
      have hz : jidx u ≤ 133484*jdeg u := by
        have hh := weight_formula u
        have hwnd : u none ≤ u.weight (differentialWeight 133484) := by
          have he : differentialWeight (d := 3) 133484 = fun i =>
              i.elim 1 (fun k => 133484 - k.val) := by
            funext i
            cases i <;> rfl
          rw [← Finsupp.optionElim_some u,he,Finsupp.weight_optionElim,one_mul]
          simp
        omega
      omega

end
end Final50AnchorColumns