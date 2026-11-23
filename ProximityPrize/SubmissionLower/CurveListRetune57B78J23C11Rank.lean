import ProximityPrize.SubmissionLower.CurveListRetune57B78J23C11Cells27

import ProximityPrize.SubmissionLower.Wide60ThreeCutSource

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace CurveListRetune57B78J23C11

open scoped BigOperators
open CJ1 (total total_eq_sum)
private def allowance : ℕ → ℕ → ℕ
  | 37,20 => 143
  | 38,19 => 142
  | 39,18 => 140
  | 40,17 => 138
  | 40,18 => 131
  | 41,16 => 135
  | 41,17 => 130
  | 42,15 => 132
  | 42,16 => 128
  | 43,14 => 128
  | 43,15 => 126
  | 43,16 => 120
  | 44,13 => 124
  | 44,14 => 123
  | 44,15 => 119
  | 45,12 => 119
  | 45,13 => 120
  | 45,14 => 117
  | 46,12 => 116
  | 46,13 => 115
  | 46,14 => 109
  | 47,11 => 112
  | 47,12 => 112
  | 47,13 => 108
  | 48,11 => 109
  | 48,12 => 106
  | 49,10 => 105
  | 49,11 => 104
  | 49,12 => 99
  | 50,10 => 101
  | 50,11 => 98
  | 51,9 => 98
  | 51,10 => 96
  | 52,9 => 94
  | 52,10 => 89
  | 53,8 => 90
  | 53,9 => 88
  | 54,8 => 86
  | 55,7 => 82
  | 55,8 => 80
  | 56,7 => 78
  | 57,6 => 73
  | 58,6 => 69
  | 59,5 => 64
  | 59,6 => 63
  | 60,5 => 60
  | 61,4 => 54
  | 61,5 => 54
  | 62,4 => 50
  | 62,5 => 48
  | 63,3 => 44
  | 63,4 => 45
  | 64,3 => 40
  | 64,4 => 40
  | 65,2 => 33
  | 65,3 => 36
  | 65,4 => 35
  | 66,2 => 30
  | 66,3 => 32
  | 67,1 => 22
  | 67,2 => 27
  | 67,3 => 28
  | 68,1 => 20
  | 68,2 => 24
  | 68,3 => 24
  | 69,0 => 11
  | 69,1 => 18
  | 69,2 => 21
  | 70,0 => 10
  | 70,1 => 16
  | 70,2 => 18
  | 71,0 => 9
  | 71,1 => 14
  | 71,2 => 15
  | 72,0 => 8
  | 72,1 => 12
  | 73,0 => 7
  | 73,1 => 10
  | 74,0 => 6
  | 74,1 => 8
  | 75,0 => 5
  | 76,0 => 4
  | 77,0 => 3
  | q,u => nominal q u

private theorem bound (q u : ℕ) :
    (CJ0.blockMatrix source q ((u:ℤ)-23)).rank≤allowance q u:=by
  unfold allowance
  split
  · exact rank_37_20
  · exact rank_38_19
  · exact rank_39_18
  · exact rank_40_17
  · exact rank_40_18
  · exact rank_41_16
  · exact rank_41_17
  · exact rank_42_15
  · exact rank_42_16
  · exact rank_43_14
  · exact rank_43_15
  · exact rank_43_16
  · exact rank_44_13
  · exact rank_44_14
  · exact rank_44_15
  · exact rank_45_12
  · exact rank_45_13
  · exact rank_45_14
  · exact rank_46_12
  · exact rank_46_13
  · exact rank_46_14
  · exact rank_47_11
  · exact rank_47_12
  · exact rank_47_13
  · exact rank_48_11
  · exact rank_48_12
  · exact rank_49_10
  · exact rank_49_11
  · exact rank_49_12
  · exact rank_50_10
  · exact rank_50_11
  · exact rank_51_9
  · exact rank_51_10
  · exact rank_52_9
  · exact rank_52_10
  · exact rank_53_8
  · exact rank_53_9
  · exact rank_54_8
  · exact rank_55_7
  · exact rank_55_8
  · exact rank_56_7
  · exact rank_57_6
  · exact rank_58_6
  · exact rank_59_5
  · exact rank_59_6
  · exact rank_60_5
  · exact rank_61_4
  · exact rank_61_5
  · exact rank_62_4
  · exact rank_62_5
  · exact rank_63_3
  · exact rank_63_4
  · exact rank_64_3
  · exact rank_64_4
  · exact rank_65_2
  · exact rank_65_3
  · exact rank_65_4
  · exact rank_66_2
  · exact rank_66_3
  · exact rank_67_1
  · exact rank_67_2
  · exact rank_67_3
  · exact rank_68_1
  · exact rank_68_2
  · exact rank_68_3
  · exact rank_69_0
  · exact rank_69_1
  · exact rank_69_2
  · exact rank_70_0
  · exact rank_70_1
  · exact rank_70_2
  · exact rank_71_0
  · exact rank_71_1
  · exact rank_71_2
  · exact rank_72_0
  · exact rank_72_1
  · exact rank_73_0
  · exact rank_73_1
  · exact rank_74_0
  · exact rank_74_1
  · exact rank_75_0
  · exact rank_76_0
  · exact rank_77_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def grade (q:ℕ):=total (allowance q) (80-q)
private def gradeTable:Fin 79→ℕ := ![57,168,330,540,795,1092,1428,1800,2205,2640,3102,3588,4050,4444,4773,5040,5248,5400,5499,5548,5550,5508,5425,5304,5148,4992,4836,4680,4524,4368,4212,4056,3900,3744,3588,3433,3279,3126,2975,2826,2679,2535,2394,2256,2122,1992,1866,1744,1627,1513,1404,1299,1198,1101,1009,920,836,756,680,608,541,477,418,363,312,265,223,184,150,120,94,72,54,39,27,18,11,6,3]
private theorem grade_0:grade 0=57:=by decide +kernel
private theorem grade_1:grade 1=168:=by decide +kernel
private theorem grade_2:grade 2=330:=by decide +kernel
private theorem grade_3:grade 3=540:=by decide +kernel
private theorem grade_4:grade 4=795:=by decide +kernel
private theorem grade_5:grade 5=1092:=by decide +kernel
private theorem grade_6:grade 6=1428:=by decide +kernel
private theorem grade_7:grade 7=1800:=by decide +kernel
private theorem grade_8:grade 8=2205:=by decide +kernel
private theorem grade_9:grade 9=2640:=by decide +kernel
private theorem grade_10:grade 10=3102:=by decide +kernel
private theorem grade_11:grade 11=3588:=by decide +kernel
private theorem grade_12:grade 12=4050:=by decide +kernel
private theorem grade_13:grade 13=4444:=by decide +kernel
private theorem grade_14:grade 14=4773:=by decide +kernel
private theorem grade_15:grade 15=5040:=by decide +kernel
private theorem grade_16:grade 16=5248:=by decide +kernel
private theorem grade_17:grade 17=5400:=by decide +kernel
private theorem grade_18:grade 18=5499:=by decide +kernel
private theorem grade_19:grade 19=5548:=by decide +kernel
private theorem grade_20:grade 20=5550:=by decide +kernel
private theorem grade_21:grade 21=5508:=by decide +kernel
private theorem grade_22:grade 22=5425:=by decide +kernel
private theorem grade_23:grade 23=5304:=by decide +kernel
private theorem grade_24:grade 24=5148:=by decide +kernel
private theorem grade_25:grade 25=4992:=by decide +kernel
private theorem grade_26:grade 26=4836:=by decide +kernel
private theorem grade_27:grade 27=4680:=by decide +kernel
private theorem grade_28:grade 28=4524:=by decide +kernel
private theorem grade_29:grade 29=4368:=by decide +kernel
private theorem grade_30:grade 30=4212:=by decide +kernel
private theorem grade_31:grade 31=4056:=by decide +kernel
private theorem grade_32:grade 32=3900:=by decide +kernel
private theorem grade_33:grade 33=3744:=by decide +kernel
private theorem grade_34:grade 34=3588:=by decide +kernel
private theorem grade_35:grade 35=3433:=by decide +kernel
private theorem grade_36:grade 36=3279:=by decide +kernel
private theorem grade_37:grade 37=3126:=by decide +kernel
private theorem grade_38:grade 38=2975:=by decide +kernel
private theorem grade_39:grade 39=2826:=by decide +kernel
private theorem grade_40:grade 40=2679:=by decide +kernel
private theorem grade_41:grade 41=2535:=by decide +kernel
private theorem grade_42:grade 42=2394:=by decide +kernel
private theorem grade_43:grade 43=2256:=by decide +kernel
private theorem grade_44:grade 44=2122:=by decide +kernel
private theorem grade_45:grade 45=1992:=by decide +kernel
private theorem grade_46:grade 46=1866:=by decide +kernel
private theorem grade_47:grade 47=1744:=by decide +kernel
private theorem grade_48:grade 48=1627:=by decide +kernel
private theorem grade_49:grade 49=1513:=by decide +kernel
private theorem grade_50:grade 50=1404:=by decide +kernel
private theorem grade_51:grade 51=1299:=by decide +kernel
private theorem grade_52:grade 52=1198:=by decide +kernel
private theorem grade_53:grade 53=1101:=by decide +kernel
private theorem grade_54:grade 54=1009:=by decide +kernel
private theorem grade_55:grade 55=920:=by decide +kernel
private theorem grade_56:grade 56=836:=by decide +kernel
private theorem grade_57:grade 57=756:=by decide +kernel
private theorem grade_58:grade 58=680:=by decide +kernel
private theorem grade_59:grade 59=608:=by decide +kernel
private theorem grade_60:grade 60=541:=by decide +kernel
private theorem grade_61:grade 61=477:=by decide +kernel
private theorem grade_62:grade 62=418:=by decide +kernel
private theorem grade_63:grade 63=363:=by decide +kernel
private theorem grade_64:grade 64=312:=by decide +kernel
private theorem grade_65:grade 65=265:=by decide +kernel
private theorem grade_66:grade 66=223:=by decide +kernel
private theorem grade_67:grade 67=184:=by decide +kernel
private theorem grade_68:grade 68=150:=by decide +kernel
private theorem grade_69:grade 69=120:=by decide +kernel
private theorem grade_70:grade 70=94:=by decide +kernel
private theorem grade_71:grade 71=72:=by decide +kernel
private theorem grade_72:grade 72=54:=by decide +kernel
private theorem grade_73:grade 73=39:=by decide +kernel
private theorem grade_74:grade 74=27:=by decide +kernel
private theorem grade_75:grade 75=18:=by decide +kernel
private theorem grade_76:grade 76=11:=by decide +kernel
private theorem grade_77:grade 77=6:=by decide +kernel
private theorem grade_78:grade 78=3:=by decide +kernel
private theorem grade_table (q : Fin 79) : grade q.val = gradeTable q := by
  fin_cases q
  · exact grade_0
  · exact grade_1
  · exact grade_2
  · exact grade_3
  · exact grade_4
  · exact grade_5
  · exact grade_6
  · exact grade_7
  · exact grade_8
  · exact grade_9
  · exact grade_10
  · exact grade_11
  · exact grade_12
  · exact grade_13
  · exact grade_14
  · exact grade_15
  · exact grade_16
  · exact grade_17
  · exact grade_18
  · exact grade_19
  · exact grade_20
  · exact grade_21
  · exact grade_22
  · exact grade_23
  · exact grade_24
  · exact grade_25
  · exact grade_26
  · exact grade_27
  · exact grade_28
  · exact grade_29
  · exact grade_30
  · exact grade_31
  · exact grade_32
  · exact grade_33
  · exact grade_34
  · exact grade_35
  · exact grade_36
  · exact grade_37
  · exact grade_38
  · exact grade_39
  · exact grade_40
  · exact grade_41
  · exact grade_42
  · exact grade_43
  · exact grade_44
  · exact grade_45
  · exact grade_46
  · exact grade_47
  · exact grade_48
  · exact grade_49
  · exact grade_50
  · exact grade_51
  · exact grade_52
  · exact grade_53
  · exact grade_54
  · exact grade_55
  · exact grade_56
  · exact grade_57
  · exact grade_58
  · exact grade_59
  · exact grade_60
  · exact grade_61
  · exact grade_62
  · exact grade_63
  · exact grade_64
  · exact grade_65
  · exact grade_66
  · exact grade_67
  · exact grade_68
  · exact grade_69
  · exact grade_70
  · exact grade_71
  · exact grade_72
  · exact grade_73
  · exact grade_74
  · exact grade_75
  · exact grade_76
  · exact grade_77
  · exact grade_78

theorem prefix_bound : CJ0.prefixRank source 79 ≤ 177137 := by
  change (∑ q ∈ Finset.range 79, ∑ u ∈ Finset.range (80-q),
    (CJ0.blockMatrix source q ((u:ℤ)-23)).rank)≤_
  calc
    _ ≤ ∑ q ∈ Finset.range 79, ∑ u ∈ Finset.range (80-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 79, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade,total_eq_sum]
    _ = ∑ q:Fin 79,gradeTable q:=Finset.sum_congr rfl fun q _ => grade_table q
    _=177137:=by decide +kernel
-- The stock witness bounds also bound the ranks after the top columns are removed.
open CJ0 (Jet blockRows blockCols blockMatrix)
private abbrev small:=Wide60ThreeCutSource.supportLow
private def smallLen (q u b:ℕ):ℕ:=min 11 (colHi q b) - colLo u b
private abbrev SmallColumn (q u:ℕ):=(b:Fin (min q 23+1)) × Fin (smallLen q u b)
private def smallCols (q u:ℕ):=total (smallLen q u) (min q 23+1)

private theorem small_bounds (q u c b a : ℕ)
    (hs:(⟨c,b,a⟩:Jet) ∈ blockCols small q ((u:ℤ)-23)) :
    b < min q 23+1 ∧ colLo u b≤c ∧ c < min 11 (colHi q b) ∧ q-(b+c)=a:=by
  change (⟨c,b,a⟩:Jet) ∈ (CJ0.fullBox 78 23 10).filter _ at hs
  rw [Finset.mem_filter,CJ0.mem_fullBox (by decide) (by decide)] at hs
  simp only [Jet.q, Jet.v, Jet.a, Jet.b, Jet.c, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hs
  unfold colLo colHi
  omega

private def smallIndex (q u : ℕ) :
    ↥(blockCols small q ((u:ℤ)-23))→SmallColumn q u
  | ⟨⟨c,b,a⟩, hs⟩ =>
    let H:=small_bounds q u c b a hs
    ⟨⟨b,H.1⟩, ⟨c-colLo u b, by
      change c - colLo u b < min 11 (colHi q b) - colLo u b
      have hlo:=H.2.1
      have hhi:=H.2.2.1
      omega⟩⟩

private theorem smallIndex_recovers (q u : ℕ) (s : ↥(blockCols small q ((u : ℤ)-23))) :
    colAt q u (smallIndex q u s).1 (smallIndex q u s).2=s.val:=by
  rcases s with ⟨⟨c,b,a⟩,hs⟩
  obtain ⟨_,hlo,_,ha⟩:=small_bounds q u c b a hs
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩:Jet)=_
  rw [Nat.add_sub_of_le hlo,ha]

private theorem small_card (q u : ℕ) :
    Fintype.card ↥(blockCols small q ((u:ℤ)-23))≤smallCols q u:=by
  have hinj : Function.Injective (smallIndex q u) := by
    intro x y h
    apply Subtype.ext
    rw [← smallIndex_recovers q u x, ← smallIndex_recovers q u y,h]
  have h:=Fintype.card_le_of_injective _ hinj
  have hc : Fintype.card (SmallColumn q u) = smallCols q u := by
    simp only [SmallColumn, Fintype.card_sigma, Fintype.card_fin, smallCols,
      total_eq_sum,Finset.sum_fin_eq_sum_range]
    exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  exact h.trans_eq hc

private theorem stock_columns_subset (q u : ℕ) :
    blockCols small q ((u:ℤ)-23) ⊆ blockCols source q ((u:ℤ)-23):=by
  intro j hj
  obtain ⟨he,hq⟩:=Finset.mem_filter.mp hj
  have hs:=(CJ0.mem_fullBox (B:=78) (J:=23) (C:=10) (by decide) (by decide) j).mp he
  refine Finset.mem_filter.mpr ⟨?_,hq⟩
  exact (CJ0.mem_fullBox (B := 78) (J := 23) (C := 11) (by decide) (by decide) j).mpr
    ⟨hs.1,hs.2.1,hs.2.2.trans (by decide)⟩

private theorem block_rank_le_of_subcols {s t : CJ0.Source} {q : ℕ} {g : ℤ}
    (row : ↥(blockRows s.m q g) → ↥(blockRows t.m q g))
    (hrow : ∀ i,(row i).val=i.val)
    (hcols:blockCols s q g ⊆ blockCols t q g) :
    (blockMatrix s q g).rank≤(blockMatrix t q g).rank:=by
  let col : ↥(blockCols s q g) → ↥(blockCols t q g):=fun j => ⟨j.val,hcols j.property⟩
  have hcol (j : ↥(blockCols s q g)):(col j).val=j.val:=rfl
  have hb : blockMatrix s q g = (blockMatrix t q g).submatrix row col := by
    funext i j
    rw [Matrix.submatrix_apply]
    change CJ0.blockEntry i.val j.val=CJ0.blockEntry (row i).val (col j).val
    rw [hrow,hcol]
  rw [hb]
  exact Matrix.rank_submatrix_le _ _ _

private def smallAllowance (q u:ℕ):=min (allowance q u) (smallCols q u)
private theorem small_bound (q u : ℕ) :
    (blockMatrix small q ((u:ℤ)-23)).rank≤smallAllowance q u:=by
  have hmono := block_rank_le_of_subcols (s := small) (t := source) id (fun _ => rfl)
    (stock_columns_subset q u)
  exact le_min (hmono.trans (bound q u))
    (((blockMatrix small q ((u:ℤ)-23)).rank_le_card_width).trans (small_card q u))

private def smallGrade (q:ℕ):=total (smallAllowance q) (80-q)
private def smallTable:Fin 79→ℕ := ![57,168,330,540,795,1092,1428,1800,2205,2640,3102,3542,3960,4357,4688,4957,5167,5321,5422,5473,5477,5437,5356,5237,5083,4929,4775,4621,4467,4313,4159,4005,3851,3697,3543,3390,3238,3087,2938,2791,2646,2504,2365,2229,2097,1968,1843,1723,1606,1494,1385,1282,1181,1086,994,907,823,745,669,599,532,470,411,358,307,262,220,183,149,120,94,72,54,39,27,18,11,6,3]
private theorem sg0 (u : Fin 10) :
    smallGrade (u.val+0)=smallTable ⟨u.val+0,by omega⟩:=by
  fin_cases u <;> decide +kernel
private theorem sg1 (u : Fin 10) :
    smallGrade (u.val+10)=smallTable ⟨u.val+10,by omega⟩:=by
  fin_cases u <;> decide +kernel
private theorem sg2 (u : Fin 10) :
    smallGrade (u.val+20)=smallTable ⟨u.val+20,by omega⟩:=by
  fin_cases u <;> decide +kernel
private theorem sg3 (u : Fin 10) :
    smallGrade (u.val+30)=smallTable ⟨u.val+30,by omega⟩:=by
  fin_cases u <;> decide +kernel
private theorem sg4 (u : Fin 10) :
    smallGrade (u.val+40)=smallTable ⟨u.val+40,by omega⟩:=by
  fin_cases u <;> decide +kernel
private theorem sg5 (u : Fin 10) :
    smallGrade (u.val+50)=smallTable ⟨u.val+50,by omega⟩:=by
  fin_cases u <;> decide +kernel
private theorem sg6 (u : Fin 10) :
    smallGrade (u.val+60)=smallTable ⟨u.val+60,by omega⟩:=by
  fin_cases u <;> decide +kernel
private theorem sg7 (u : Fin 9) :
    smallGrade (u.val+70)=smallTable ⟨u.val+70,by omega⟩:=by
  fin_cases u <;> decide +kernel
private theorem small_grade_table (q : Fin 79) : smallGrade q.val = smallTable q := by
  have hq:=q.isLt
  by_cases h0:q.val < 10
  · let u : Fin 10 := ⟨q.val-0,by omega⟩
    have he:u.val+0=q.val:=by dsimp [u]
    have hf:(⟨u.val+0,by omega⟩:Fin 79)=q:=Fin.ext he
    simpa only [he,hf] using sg0 u
  by_cases h1:q.val < 20
  · let u : Fin 10 := ⟨q.val-10,by omega⟩
    have he:u.val+10=q.val:=by dsimp [u]; omega
    have hf:(⟨u.val+10,by omega⟩:Fin 79)=q:=Fin.ext he
    simpa only [he,hf] using sg1 u
  by_cases h2:q.val < 30
  · let u : Fin 10 := ⟨q.val-20,by omega⟩
    have he:u.val+20=q.val:=by dsimp [u]; omega
    have hf:(⟨u.val+20,by omega⟩:Fin 79)=q:=Fin.ext he
    simpa only [he,hf] using sg2 u
  by_cases h3:q.val < 40
  · let u : Fin 10 := ⟨q.val-30,by omega⟩
    have he:u.val+30=q.val:=by dsimp [u]; omega
    have hf:(⟨u.val+30,by omega⟩:Fin 79)=q:=Fin.ext he
    simpa only [he,hf] using sg3 u
  by_cases h4:q.val < 50
  · let u : Fin 10 := ⟨q.val-40,by omega⟩
    have he:u.val+40=q.val:=by dsimp [u]; omega
    have hf:(⟨u.val+40,by omega⟩:Fin 79)=q:=Fin.ext he
    simpa only [he,hf] using sg4 u
  by_cases h5:q.val < 60
  · let u : Fin 10 := ⟨q.val-50,by omega⟩
    have he:u.val+50=q.val:=by dsimp [u]; omega
    have hf:(⟨u.val+50,by omega⟩:Fin 79)=q:=Fin.ext he
    simpa only [he,hf] using sg5 u
  by_cases h6:q.val < 70
  · let u : Fin 10 := ⟨q.val-60,by omega⟩
    have he:u.val+60=q.val:=by dsimp [u]; omega
    have hf:(⟨u.val+60,by omega⟩:Fin 79)=q:=Fin.ext he
    simpa only [he,hf] using sg6 u
  let u:Fin 9:=⟨q.val-70,by omega⟩
  have he:u.val+70=q.val:=by dsimp [u]; omega
  have hf:(⟨u.val+70,by omega⟩:Fin 79)=q:=Fin.ext he
  simpa only [he,hf] using sg7 u
private theorem sum_smallGrades (cut : ℕ) (table : Fin cut → ℕ)
    (h : ∀ q:Fin cut,smallGrade q.val=table q) :
    (∑ q ∈ Finset.range cut,smallGrade q) = ∑ q:Fin cut,table q:=by
  calc
    _ = ∑ q:Fin cut,smallGrade q.val:=by rw [Fin.sum_univ_eq_sum_range]
    _=_:=Finset.sum_congr rfl fun q _ => h q

private theorem small_prefix_le (cut : ℕ) :
    CJ0.prefixRank small cut ≤ ∑ q ∈ Finset.range cut,smallGrade q:=by
  unfold CJ0.prefixRank
  apply Finset.sum_le_sum
  intro q _
  change (∑ u ∈ Finset.range (80-q),(blockMatrix small q ((u:ℤ)-23)).rank)≤smallGrade q
  rw [smallGrade,total_eq_sum]
  exact Finset.sum_le_sum fun u _ => small_bound q u

private theorem small_total:(∑ q:Fin 79,smallTable q)=174920:=by decide +kernel

theorem prefix_bound_low : CJ0.prefixRank Wide60ThreeCutSource.supportLow 79 ≤ 174920 :=
  (small_prefix_le 79).trans_eq ((sum_smallGrades 79 smallTable small_grade_table).trans small_total)

end CurveListRetune57B78J23C11

#print axioms CurveListRetune57B78J23C11.prefix_bound

#print axioms CurveListRetune57B78J23C11.prefix_bound_low
