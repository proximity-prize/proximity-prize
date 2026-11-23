import ProximityPrize.SubmissionLower.SmallAnchor6960Space
import ProximityPrize.SubmissionLower.Final50RankCore
import ProximityPrize.SubmissionLower.Final50RankReceipt

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

namespace SmallAnchor6960RepricedFees
open Final50RankReceipt (Row rows triangle fee price lateLo lateHi)
open SmallAnchor6960Space (cap cap_le_index)
open Finset
open scoped BigOperators

private theorem triangle_succ (n : ℕ) :
    triangle (n+1)=triangle n+(n+1):=by
  unfold triangle
  have h:(n+1)*(n+1+1)=n*(n+1)+2*(n+1):=by ring
  rw [h]
  omega

private theorem triangle_diff (x n : ℕ) :
    ∑ j ∈ range n,(x-j)=triangle x - triangle (x-n):=by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih]
    by_cases h:x≤n
    · have h' : x ≤ n+1 := by omega
      simp [Nat.sub_eq_zero_of_le h,Nat.sub_eq_zero_of_le h']
    · have hx : x-n = (x-(n+1))+1 := by omega
      have hle : triangle (x-n) ≤ triangle x := by
        apply Nat.div_le_div_right
        exact Nat.mul_le_mul (Nat.sub_le ..) (by omega)
      rw [hx,triangle_succ] at hle
      rw [hx,triangle_succ]
      omega

private def late (d : ℕ) : Finset ℕ :=
  (range (lateHi d - lateLo d)).image (fun s => lateLo d+s)

private def stages (d:ℕ):Finset ℕ:=insert d (late d)

private theorem in_late (d s : ℕ) : s ∈ late d ↔ lateLo d ≤ s ∧ s < lateHi d := by
  unfold late
  rw [mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [mem_range] at hi
    omega
  · intro hs
    exact ⟨s - lateLo d,mem_range.mpr (by omega),by omega⟩

private theorem stage_bounds (d : ℕ) (hd : d < 57) :
    d < lateLo d ∧ lateLo d≤lateHi d ∧ lateHi d≤137:=by
  have checks : (List.range 57).all (fun i => decide
      (i < lateLo i ∧ lateLo i≤lateHi i ∧ lateHi i≤137))=true:=by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks d (List.mem_range.mpr hd))

private def stagePairs : List (Nat × Nat) :=
  ((List.range 57).map fun d => (d, d)) ++
    ((List.range 57).reverse.flatMap fun d =>
      (List.range (lateHi d - lateLo d)).map (fun i => (lateLo d + i, d)))

private theorem stagePairs_eq :
    stagePairs = (List.range 137).map (fun s => (s, cap s)) := by
  decide +kernel

private theorem mem_stagePairs (d s : Nat) (hd : d < 57) :
    (s, d) ∈ stagePairs ↔ s = d ∨ lateLo d ≤ s ∧ s < lateHi d := by
  simp only [stagePairs, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_reverse, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨q, _, hs, hd⟩ | ⟨q, _, i, hi, hs, rfl⟩)
    · exact Or.inl (hs.symm.trans hd)
    · exact Or.inr ⟨by omega, by omega⟩
  · rintro (h | h)
    · exact Or.inl ⟨d, hd, h.symm, rfl⟩
    · exact Or.inr ⟨d, hd, s - lateLo d, by omega, by omega, rfl⟩

private theorem stages_eq (d : Nat) (hd : d < 57) :
    (range 137).filter (fun s => cap s = d) = stages d := by
  ext s
  rw [mem_filter, mem_range, stages, mem_insert, in_late, ← mem_stagePairs d s hd]
  rw [stagePairs_eq]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · exact fun ⟨hs, hc⟩ => ⟨s, hs, rfl, hc⟩
  · rintro ⟨i, hi, rfl, hc⟩
    exact ⟨hi, hc⟩

private theorem fee_add (s i : ℕ) (r : Row) : fee (s+i) r = fee s r - i := by
  unfold fee
  omega

private theorem sum_stage_fee (d : ℕ) (hd : d < 57) (r : Row) :
    ∑ s ∈ stages d,fee s r=price d r:=by
  obtain ⟨hlo,hlen,_⟩:=stage_bounds d hd
  have hmiss:d ∉ late d:=fun h => (Nat.not_le_of_gt hlo) ((in_late d d).mp h).1
  have hinj : Set.InjOn (fun s : ℕ => lateLo d+s) (↑(range (lateHi d-lateLo d))) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  rw [stages,sum_insert hmiss,late,sum_image hinj,price]
  simp_rw [fee_add (lateLo d)]
  rw [triangle_diff, ← fee_add,Nat.add_sub_of_le hlen]

private theorem exchange (st : Finset ℕ) (rows : List Row) :
    (∑ s ∈ st, ((rows.map (fee s)).sum)) =
      (rows.map (fun r => ∑ s ∈ st,fee s r)).sum:=by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

theorem sum_fees (rows : ℕ → List Row) :
    (∑ s : Fin 137, ((rows (cap s)).map (fee s)).sum) =
      ∑ d:Fin 57,((rows d).map (price d)).sum:=by
  rw [Fin.sum_univ_eq_sum_range (fun s => ((rows (cap s)).map (fee s)).sum) 137,
    Fin.sum_univ_eq_sum_range (fun d => ((rows d).map (price d)).sum) 57]
  calc
    _ = ∑ s ∈ range 137, ∑ d ∈ range 57,
          if cap s=d then ((rows d).map (fee s)).sum else 0:=by
        apply sum_congr rfl
        intro s hs
        rw [sum_eq_single (cap s)]
        · simp
        · intro d hd hne
          simp [Ne.symm hne]
        · intro he
          exact (he (mem_range.mpr (Nat.lt_succ_of_le (cap_le_index s)))).elim
    _ = ∑ d ∈ range 57, ((rows d).map (price d)).sum := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d hd
        rw [← sum_filter,stages_eq d (mem_range.mp hd),exchange]
        simp_rw [sum_stage_fee d (mem_range.mp hd)]

private def fees:List ℕ:=[102,404,1000,1980,3430,5432,8064,11400,15510,20460,26312,33124,40950,49840,59840,70905,82990,96050,110040,124915,140630,157140,174160,191338,208338,224840,240540,255150,268398,280101,290376,299265,306880,313260,318512,322672,326792,328055,329408,333221,329716,334830,327240,334528,322422,332665,315672,329578,307371,325591,297869,321017,287487,316169,276515,311354,7411379]

theorem total_fees :
    (∑ s:Fin 137,Final50RankCore.gradeFee s (rows (SmallAnchor6960Space.cap s)))=18553227:=by
  change (∑ s:Fin 137,((rows (cap s)).map (fee s)).sum)=_
  rw [sum_fees]
  calc
    _ = ∑ d : Fin 57, fees[d.val]! := by
      apply sum_congr rfl
      intro d _
      fin_cases d
      · exact Final50RankReceipt.total0
      · exact Final50RankReceipt.total1
      · exact Final50RankReceipt.total2
      · exact Final50RankReceipt.total3
      · exact Final50RankReceipt.total4
      · exact Final50RankReceipt.total5
      · exact Final50RankReceipt.total6
      · exact Final50RankReceipt.total7
      · exact Final50RankReceipt.total8
      · exact Final50RankReceipt.total9
      · exact Final50RankReceipt.total10
      · exact Final50RankReceipt.total11
      · exact Final50RankReceipt.total12
      · exact Final50RankReceipt.total13
      · exact Final50RankReceipt.total14
      · exact Final50RankReceipt.total15
      · exact Final50RankReceipt.total16
      · exact Final50RankReceipt.total17
      · exact Final50RankReceipt.total18
      · exact Final50RankReceipt.total19
      · exact Final50RankReceipt.total20
      · exact Final50RankReceipt.total21
      · exact Final50RankReceipt.total22
      · exact Final50RankReceipt.total23
      · exact Final50RankReceipt.total24
      · exact Final50RankReceipt.total25
      · exact Final50RankReceipt.total26
      · exact Final50RankReceipt.total27
      · exact Final50RankReceipt.total28
      · exact Final50RankReceipt.total29
      · exact Final50RankReceipt.total30
      · exact Final50RankReceipt.total31
      · exact Final50RankReceipt.total32
      · exact Final50RankReceipt.total33
      · exact Final50RankReceipt.total34
      · exact Final50RankReceipt.total35
      · exact Final50RankReceipt.total36
      · exact Final50RankReceipt.total37
      · exact Final50RankReceipt.total38
      · exact Final50RankReceipt.total39
      · exact Final50RankReceipt.total40
      · exact Final50RankReceipt.total41
      · exact Final50RankReceipt.total42
      · exact Final50RankReceipt.total43
      · exact Final50RankReceipt.total44
      · exact Final50RankReceipt.total45
      · exact Final50RankReceipt.total46
      · exact Final50RankReceipt.total47
      · exact Final50RankReceipt.total48
      · exact Final50RankReceipt.total49
      · exact Final50RankReceipt.total50
      · exact Final50RankReceipt.total51
      · exact Final50RankReceipt.total52
      · exact Final50RankReceipt.total53
      · exact Final50RankReceipt.total54
      · exact Final50RankReceipt.total55
      · exact Final50RankReceipt.total56
    _=_:=by decide +kernel

#print axioms total_fees
end SmallAnchor6960RepricedFees
