import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import Mathlib.Data.Int.Interval
set_option Elab.async false
set_option autoImplicit true
section
namespace Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
open ReedSolomon.HiddenDerivative PolynomialDifferential
abbrev Jet := (s : Fin 65) × (e2 : Fin (min s.val 10 + 1)) ×
  Fin (min (s.val - e2.val) (21 - 2 * e2.val) + 1)
def e1 (j : Jet) : ℕ := j.2.2.val
def e2 (j : Jet) : ℕ := j.2.1.val
def e0 (j : Jet) : ℕ := j.1.val - e2 j - e1 j
def width (j : Jet) : ℕ := 48 * 180265 - 131072 * j.1.val + e1 j + 2 * e2 j
abbrev SourceIndex := (j : Jet) × Fin (width j)
def columns (i : SourceIndex) : SourceColumn 2 where
  x := i.2.val
  y₀ := e0 i.1
  higher := ![e1 i.1, e2 i.1]
theorem jet_total (j : Jet) : e0 j + e1 j + e2 j = j.1.val := by
  have h2 := j.2.1.isLt
  have h1 := j.2.2.isLt
  simp only [e0, e1, e2]
  omega
theorem jet_order (j : Jet) : e1 j + 2 * e2 j ≤ 21 := by
  have h1 := j.2.2.isLt
  simp only [e1, e2]
  omega
theorem width_lower (j : Jet) : 264112 ≤ width j := by
  have hs := j.1.isLt
  unfold width
  omega
theorem source_weight_lt (i : SourceIndex) :
    i.2.val + 131072 * e0 i.1 + 131071 * e1 i.1 + 131070 * e2 i.1 < 48 * 180265 := by
  have hs := i.1.1.isLt
  have ht := jet_total i.1
  have hx := i.2.isLt
  unfold width at hx
  omega
theorem columns_injective : Function.Injective columns := by
  rintro ⟨⟨sa, ea, fa⟩, xa⟩ ⟨⟨sb, eb, fb⟩, xb⟩ heq
  have hx := congrArg SourceColumn.x heq
  have h0 := congrArg SourceColumn.y₀ heq
  have h1 := congrArg (fun c : SourceColumn 2 ↦ c.higher 0) heq
  have h2 := congrArg (fun c : SourceColumn 2 ↦ c.higher 1) heq
  have hta := jet_total (⟨sa, ea, fa⟩ : Jet)
  have htb := jet_total (⟨sb, eb, fb⟩ : Jet)
  simp only [columns, e0, e1, e2, Matrix.cons_val_zero, Matrix.cons_val_one] at hx h0 h1 h2 hta htb
  have hs : sa = sb := Fin.ext (by omega)
  subst sb
  have he : ea = eb := Fin.ext h2
  subst eb
  have hf : fa = fb := Fin.ext h1
  subst fb
  have hxx : xa = xb := Fin.ext hx
  subst xb
  rfl
theorem columns_y0_le (i : SourceIndex) : (columns i).y₀ ≤ 64 := by
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  change e0 i.1 ≤ 64
  omega
theorem columns_total_le (i : SourceIndex) : totalJetDegree (columns i).exponent ≤ 64 := by
  rw [SourceColumn.totalJetDegree_exponent]
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  simp [columns, Fin.sum_univ_two]
  omega
theorem columns_weight_lt (i : SourceIndex) :
    Finsupp.weight (differentialWeight 131072) (columns i).exponent < 48 * 180265 := by
  simpa [SourceColumn.weight_exponent, columns, differentialWeight, Fin.sum_univ_two,
    Nat.add_assoc, Nat.mul_comm] using
    source_weight_lt i
def sourceTotal : ℕ := ∑ j : Jet, width j
theorem jet_count : Fintype.card Jet = 7194 := by decide +kernel
theorem source_total : sourceTotal = 27313144144 := by decide +kernel
theorem source_card : Fintype.card SourceIndex = 27313144144 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact source_total
end Sol1.C42
end
section
namespace Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
def columnCount (s : ℕ) (g : ℤ) : ℕ :=
  ∑ e ∈ Finset.range (min s 10 + 1),
    ((min (min ((s : ℤ) - e) (21 - 2 * (e : ℤ))) (47 - g - 2 * e)) -
      max 0 (-g - 2 * e) + 1).toNat
def rowCount (s : ℕ) (g : ℤ) : ℕ :=
  let L : ℤ := 48 - g - s
  let lo : ℤ := max 0 (-g)
  let hi : ℤ := min 21 (47 - g)
  if 0 < L ∧ lo ≤ hi then
    ∑ b ∈ Finset.range (min s ((L - 1) / 2).toNat + 1),
      (((min ((s : ℤ) - b - 1) (L - 1 - 2 * b)) - max 0 (lo - s + b) + 1).toNat +
        if 2 * (b : ℤ) + ((s : ℤ) - b) < L ∧
          2 * ((lo + 1) / 2) ≤ min hi (2 * ((s : ℤ) - b)) then 1 else 0)
  else 0
def blockUpper : ℕ := ∑ s : Fin 65, ∑ gi : Fin 69,
  min (columnCount s.val ((gi.val : ℤ) - 21)) (rowCount s.val ((gi.val : ℤ) - 21))
def pack2BlockUpperRow (s : Fin 65) : ℕ := ∑ gi : Fin 69,
  min (columnCount s.val ((gi.val : ℤ) - 21)) (rowCount s.val ((gi.val : ℤ) - 21))
def pack2BlockUpperTable : Fin 65 → ℕ := ![48,141,276,450,660,903,1176,1476,1800,2145,2508,2849,3132,3360,3536,3663,3744,3782,3780,3741,3668,3564,3432,3300,3168,3036,2904,2772,2641,2511,2383,2257,2134,2013,1893,1777,1665,1555,1448,1346,1246,1150,1060,970,887,806,730,658,590,526,466,410,359,310,268,226,190,158,128,103,81,61,45,33,22]
theorem pack2BlockUpperCheck0 : pack2BlockUpperRow 0 = 48 := by decide +kernel
theorem pack2BlockUpperCheck1 : pack2BlockUpperRow 1 = 141 := by decide +kernel
theorem pack2BlockUpperCheck2 : pack2BlockUpperRow 2 = 276 := by decide +kernel
theorem pack2BlockUpperCheck3 : pack2BlockUpperRow 3 = 450 := by decide +kernel
theorem pack2BlockUpperCheck4 : pack2BlockUpperRow 4 = 660 := by decide +kernel
theorem pack2BlockUpperCheck5 : pack2BlockUpperRow 5 = 903 := by decide +kernel
theorem pack2BlockUpperCheck6 : pack2BlockUpperRow 6 = 1176 := by decide +kernel
theorem pack2BlockUpperCheck7 : pack2BlockUpperRow 7 = 1476 := by decide +kernel
theorem pack2BlockUpperCheck8 : pack2BlockUpperRow 8 = 1800 := by decide +kernel
theorem pack2BlockUpperCheck9 : pack2BlockUpperRow 9 = 2145 := by decide +kernel
theorem pack2BlockUpperCheck10 : pack2BlockUpperRow 10 = 2508 := by decide +kernel
theorem pack2BlockUpperCheck11 : pack2BlockUpperRow 11 = 2849 := by decide +kernel
theorem pack2BlockUpperCheck12 : pack2BlockUpperRow 12 = 3132 := by decide +kernel
theorem pack2BlockUpperCheck13 : pack2BlockUpperRow 13 = 3360 := by decide +kernel
theorem pack2BlockUpperCheck14 : pack2BlockUpperRow 14 = 3536 := by decide +kernel
theorem pack2BlockUpperCheck15 : pack2BlockUpperRow 15 = 3663 := by decide +kernel
theorem pack2BlockUpperCheck16 : pack2BlockUpperRow 16 = 3744 := by decide +kernel
theorem pack2BlockUpperCheck17 : pack2BlockUpperRow 17 = 3782 := by decide +kernel
theorem pack2BlockUpperCheck18 : pack2BlockUpperRow 18 = 3780 := by decide +kernel
theorem pack2BlockUpperCheck19 : pack2BlockUpperRow 19 = 3741 := by decide +kernel
theorem pack2BlockUpperCheck20 : pack2BlockUpperRow 20 = 3668 := by decide +kernel
theorem pack2BlockUpperCheck21 : pack2BlockUpperRow 21 = 3564 := by decide +kernel
theorem pack2BlockUpperCheck22 : pack2BlockUpperRow 22 = 3432 := by decide +kernel
theorem pack2BlockUpperCheck23 : pack2BlockUpperRow 23 = 3300 := by decide +kernel
theorem pack2BlockUpperCheck24 : pack2BlockUpperRow 24 = 3168 := by decide +kernel
theorem pack2BlockUpperCheck25 : pack2BlockUpperRow 25 = 3036 := by decide +kernel
theorem pack2BlockUpperCheck26 : pack2BlockUpperRow 26 = 2904 := by decide +kernel
theorem pack2BlockUpperCheck27 : pack2BlockUpperRow 27 = 2772 := by decide +kernel
theorem pack2BlockUpperCheck28 : pack2BlockUpperRow 28 = 2641 := by decide +kernel
theorem pack2BlockUpperCheck29 : pack2BlockUpperRow 29 = 2511 := by decide +kernel
theorem pack2BlockUpperCheck30 : pack2BlockUpperRow 30 = 2383 := by decide +kernel
theorem pack2BlockUpperCheck31 : pack2BlockUpperRow 31 = 2257 := by decide +kernel
theorem pack2BlockUpperCheck32 : pack2BlockUpperRow 32 = 2134 := by decide +kernel
theorem pack2BlockUpperCheck33 : pack2BlockUpperRow 33 = 2013 := by decide +kernel
theorem pack2BlockUpperCheck34 : pack2BlockUpperRow 34 = 1893 := by decide +kernel
theorem pack2BlockUpperCheck35 : pack2BlockUpperRow 35 = 1777 := by decide +kernel
theorem pack2BlockUpperCheck36 : pack2BlockUpperRow 36 = 1665 := by decide +kernel
theorem pack2BlockUpperCheck37 : pack2BlockUpperRow 37 = 1555 := by decide +kernel
theorem pack2BlockUpperCheck38 : pack2BlockUpperRow 38 = 1448 := by decide +kernel
theorem pack2BlockUpperCheck39 : pack2BlockUpperRow 39 = 1346 := by decide +kernel
theorem pack2BlockUpperCheck40 : pack2BlockUpperRow 40 = 1246 := by decide +kernel
theorem pack2BlockUpperCheck41 : pack2BlockUpperRow 41 = 1150 := by decide +kernel
theorem pack2BlockUpperCheck42 : pack2BlockUpperRow 42 = 1060 := by decide +kernel
theorem pack2BlockUpperCheck43 : pack2BlockUpperRow 43 = 970 := by decide +kernel
theorem pack2BlockUpperCheck44 : pack2BlockUpperRow 44 = 887 := by decide +kernel
theorem pack2BlockUpperCheck45 : pack2BlockUpperRow 45 = 806 := by decide +kernel
theorem pack2BlockUpperCheck46 : pack2BlockUpperRow 46 = 730 := by decide +kernel
theorem pack2BlockUpperCheck47 : pack2BlockUpperRow 47 = 658 := by decide +kernel
theorem pack2BlockUpperCheck48 : pack2BlockUpperRow 48 = 590 := by decide +kernel
theorem pack2BlockUpperCheck49 : pack2BlockUpperRow 49 = 526 := by decide +kernel
theorem pack2BlockUpperCheck50 : pack2BlockUpperRow 50 = 466 := by decide +kernel
theorem pack2BlockUpperCheck51 : pack2BlockUpperRow 51 = 410 := by decide +kernel
theorem pack2BlockUpperCheck52 : pack2BlockUpperRow 52 = 359 := by decide +kernel
theorem pack2BlockUpperCheck53 : pack2BlockUpperRow 53 = 310 := by decide +kernel
theorem pack2BlockUpperCheck54 : pack2BlockUpperRow 54 = 268 := by decide +kernel
theorem pack2BlockUpperCheck55 : pack2BlockUpperRow 55 = 226 := by decide +kernel
theorem pack2BlockUpperCheck56 : pack2BlockUpperRow 56 = 190 := by decide +kernel
theorem pack2BlockUpperCheck57 : pack2BlockUpperRow 57 = 158 := by decide +kernel
theorem pack2BlockUpperCheck58 : pack2BlockUpperRow 58 = 128 := by decide +kernel
theorem pack2BlockUpperCheck59 : pack2BlockUpperRow 59 = 103 := by decide +kernel
theorem pack2BlockUpperCheck60 : pack2BlockUpperRow 60 = 81 := by decide +kernel
theorem pack2BlockUpperCheck61 : pack2BlockUpperRow 61 = 61 := by decide +kernel
theorem pack2BlockUpperCheck62 : pack2BlockUpperRow 62 = 45 := by decide +kernel
theorem pack2BlockUpperCheck63 : pack2BlockUpperRow 63 = 33 := by decide +kernel
theorem pack2BlockUpperCheck64 : pack2BlockUpperRow 64 = 22 := by decide +kernel
theorem pack2BlockUpperRows (s : Fin 65) : pack2BlockUpperRow s = pack2BlockUpperTable s := by
  fin_cases s
  · exact pack2BlockUpperCheck0
  · exact pack2BlockUpperCheck1
  · exact pack2BlockUpperCheck2
  · exact pack2BlockUpperCheck3
  · exact pack2BlockUpperCheck4
  · exact pack2BlockUpperCheck5
  · exact pack2BlockUpperCheck6
  · exact pack2BlockUpperCheck7
  · exact pack2BlockUpperCheck8
  · exact pack2BlockUpperCheck9
  · exact pack2BlockUpperCheck10
  · exact pack2BlockUpperCheck11
  · exact pack2BlockUpperCheck12
  · exact pack2BlockUpperCheck13
  · exact pack2BlockUpperCheck14
  · exact pack2BlockUpperCheck15
  · exact pack2BlockUpperCheck16
  · exact pack2BlockUpperCheck17
  · exact pack2BlockUpperCheck18
  · exact pack2BlockUpperCheck19
  · exact pack2BlockUpperCheck20
  · exact pack2BlockUpperCheck21
  · exact pack2BlockUpperCheck22
  · exact pack2BlockUpperCheck23
  · exact pack2BlockUpperCheck24
  · exact pack2BlockUpperCheck25
  · exact pack2BlockUpperCheck26
  · exact pack2BlockUpperCheck27
  · exact pack2BlockUpperCheck28
  · exact pack2BlockUpperCheck29
  · exact pack2BlockUpperCheck30
  · exact pack2BlockUpperCheck31
  · exact pack2BlockUpperCheck32
  · exact pack2BlockUpperCheck33
  · exact pack2BlockUpperCheck34
  · exact pack2BlockUpperCheck35
  · exact pack2BlockUpperCheck36
  · exact pack2BlockUpperCheck37
  · exact pack2BlockUpperCheck38
  · exact pack2BlockUpperCheck39
  · exact pack2BlockUpperCheck40
  · exact pack2BlockUpperCheck41
  · exact pack2BlockUpperCheck42
  · exact pack2BlockUpperCheck43
  · exact pack2BlockUpperCheck44
  · exact pack2BlockUpperCheck45
  · exact pack2BlockUpperCheck46
  · exact pack2BlockUpperCheck47
  · exact pack2BlockUpperCheck48
  · exact pack2BlockUpperCheck49
  · exact pack2BlockUpperCheck50
  · exact pack2BlockUpperCheck51
  · exact pack2BlockUpperCheck52
  · exact pack2BlockUpperCheck53
  · exact pack2BlockUpperCheck54
  · exact pack2BlockUpperCheck55
  · exact pack2BlockUpperCheck56
  · exact pack2BlockUpperCheck57
  · exact pack2BlockUpperCheck58
  · exact pack2BlockUpperCheck59
  · exact pack2BlockUpperCheck60
  · exact pack2BlockUpperCheck61
  · exact pack2BlockUpperCheck62
  · exact pack2BlockUpperCheck63
  · exact pack2BlockUpperCheck64
theorem block_upper : blockUpper = 104120 := by
  change (∑ s : Fin 65, pack2BlockUpperRow s) = 104120
  simp_rw [pack2BlockUpperRows]
  decide +kernel
theorem strict_source_surplus : 262144 * blockUpper < Fintype.card SourceIndex := by
  rw [block_upper, source_card]
  norm_num
end Sol1.C42
end
section
namespace Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
end Sol1.C42
end
section
namespace Sol1.C42
open ReedSolomon.HiddenDerivative
def Eligible (x a b c : ℕ) : Prop :=
  a + b + c ≤ 64 ∧ b + 2 * c ≤ 21 ∧
    x + 131072 * a + 131071 * b + 131070 * c < 48 * 180265
theorem index_of_eligible (x a b c : ℕ) (h : Eligible x a b c) :
    ∃ i : SourceIndex, columns i = { x := x, y₀ := a, higher := ![b,c] } := by
  obtain ⟨htotal, horder, hweight⟩ := h
  let s : Fin 65 := ⟨a + b + c, by omega⟩
  let f2 : Fin (min s.val 10 + 1) := ⟨c, by dsimp [s]; omega⟩
  let f1 : Fin (min (s.val - f2.val) (21 - 2 * f2.val) + 1) :=
    ⟨b, by dsimp [s, f2]; omega⟩
  let j : Jet := ⟨s, f2, f1⟩
  have h0 : e0 j = a := by dsimp [e0, e1, e2, j, s, f1, f2]; omega
  have h1 : e1 j = b := rfl
  have h2 : e2 j = c := rfl
  have hx : x < width j := by dsimp [width, e1, e2, j, s, f1, f2]; omega
  refine ⟨⟨j, ⟨x, hx⟩⟩, ?_⟩
  change { x := x, y₀ := e0 j, higher := ![e1 j,e2 j] } =
    ({ x := x, y₀ := a, higher := ![b,c] } : SourceColumn 2)
  rw [h0, h1, h2]
end Sol1.C42
end
section
namespace Sol1.C42
open scoped BigOperators
theorem fin_interval_card (N : ℕ) (lo hi : ℤ) :
    (Finset.univ.filter fun x : Fin N ↦ lo ≤ (x.val : ℤ) ∧ (x.val : ℤ) ≤ hi).card =
      (min ((N : ℤ) - 1) hi - max 0 lo + 1).toNat := by
  classical
  have hcard :
      (Finset.univ.filter fun x : Fin N ↦ lo ≤ (x.val : ℤ) ∧ (x.val : ℤ) ≤ hi).card =
        (Finset.Icc (max 0 lo) (min ((N : ℤ) - 1) hi)).card := by
    apply Finset.card_bij (fun x _ ↦ (x.val : ℤ))
    · intro x hx
      have h := (Finset.mem_filter.mp hx).2
      apply Finset.mem_Icc.mpr
      have hN := x.isLt
      omega
    · intro x _ y _ hxy
      apply Fin.ext
      omega
    · intro z hz
      obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hz
      have hzN : z.toNat < N := by omega
      refine ⟨⟨z.toNat,hzN⟩, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change lo ≤ (z.toNat : ℤ) ∧ (z.toNat : ℤ) ≤ hi
        omega
      · change (z.toNat : ℤ) = z
        omega
  rw [hcard, Int.card_Icc]
  congr 1
  omega
def sourceBlockFiberCount (s : ℕ) (g : ℤ) : ℕ :=
  ∑ e ∈ Finset.range (min s 10 + 1),
    (Finset.univ.filter fun a : Fin (min (s - e) (21 - 2 * e) + 1) ↦
      0 ≤ g + a.val + 2 * e ∧ g + a.val + 2 * e < 48).card
theorem sourceBlockFiberCount_eq (s : ℕ) (g : ℤ) :
    sourceBlockFiberCount s g = columnCount s g := by
  classical
  unfold sourceBlockFiberCount columnCount
  apply Finset.sum_congr rfl
  intro e he
  have heS : e ≤ s := by have := Finset.mem_range.mp he; omega
  have heJ : 2 * e ≤ 21 := by have := Finset.mem_range.mp he; omega
  have hfilter :
      (Finset.univ.filter fun a : Fin (min (s - e) (21 - 2 * e) + 1) ↦
        0 ≤ g + a.val + 2 * e ∧ g + a.val + 2 * e < 48) =
      (Finset.univ.filter fun a : Fin (min (s - e) (21 - 2 * e) + 1) ↦
        -g - 2 * e ≤ (a.val : ℤ) ∧ (a.val : ℤ) ≤ 47 - g - 2 * e) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hfilter, fin_interval_card]
  have hupper : ((min (s - e) (21 - 2 * e) + 1 : ℕ) : ℤ) - 1 =
      min ((s : ℤ) - e) (21 - 2 * e) := by omega
  rw [hupper]
end Sol1.C42
end
section
namespace Sol1.C52
open scoped BigOperators
open Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def rowCountEnvelope (s : ℕ) (g : ℤ) : ℕ :=
  ∑ b : Fin (s + 1),
    (min ((s : ℤ) - b.val) (48 - g - s - 1 - 2 * b.val) -
      max 0 (max 0 (-g) - s + b.val) + 1).toNat
def envelopeUpper : ℕ := ∑ s : Fin 65, ∑ gi : Fin 69,
  min (columnCount s.val ((gi.val : ℤ) - 21))
    (rowCountEnvelope s.val ((gi.val : ℤ) - 21))
def gradeUpper (s : ℕ) : ℕ := ∑ gi : Fin 69,
  min (columnCount s ((gi.val : ℤ) - 21)) (rowCountEnvelope s ((gi.val : ℤ) - 21))
theorem grade_0 : gradeUpper 0 = 48 := by decide +kernel
theorem grade_1 : gradeUpper 1 = 141 := by decide +kernel
theorem grade_2 : gradeUpper 2 = 276 := by decide +kernel
theorem grade_3 : gradeUpper 3 = 450 := by decide +kernel
theorem grade_4 : gradeUpper 4 = 660 := by decide +kernel
theorem grade_5 : gradeUpper 5 = 903 := by decide +kernel
theorem grade_6 : gradeUpper 6 = 1176 := by decide +kernel
theorem grade_7 : gradeUpper 7 = 1476 := by decide +kernel
theorem grade_8 : gradeUpper 8 = 1800 := by decide +kernel
theorem grade_9 : gradeUpper 9 = 2145 := by decide +kernel
theorem grade_10 : gradeUpper 10 = 2508 := by decide +kernel
theorem grade_11 : gradeUpper 11 = 2849 := by decide +kernel
theorem grade_12 : gradeUpper 12 = 3132 := by decide +kernel
theorem grade_13 : gradeUpper 13 = 3360 := by decide +kernel
theorem grade_14 : gradeUpper 14 = 3536 := by decide +kernel
theorem grade_15 : gradeUpper 15 = 3663 := by decide +kernel
theorem grade_16 : gradeUpper 16 = 3744 := by decide +kernel
theorem grade_17 : gradeUpper 17 = 3782 := by decide +kernel
theorem grade_18 : gradeUpper 18 = 3780 := by decide +kernel
theorem grade_19 : gradeUpper 19 = 3741 := by decide +kernel
theorem grade_20 : gradeUpper 20 = 3668 := by decide +kernel
theorem grade_21 : gradeUpper 21 = 3564 := by decide +kernel
theorem grade_22 : gradeUpper 22 = 3432 := by decide +kernel
theorem grade_23 : gradeUpper 23 = 3300 := by decide +kernel
theorem grade_24 : gradeUpper 24 = 3168 := by decide +kernel
theorem grade_25 : gradeUpper 25 = 3036 := by decide +kernel
theorem grade_26 : gradeUpper 26 = 2904 := by decide +kernel
theorem grade_27 : gradeUpper 27 = 2772 := by decide +kernel
theorem grade_28 : gradeUpper 28 = 2641 := by decide +kernel
theorem grade_29 : gradeUpper 29 = 2511 := by decide +kernel
theorem grade_30 : gradeUpper 30 = 2383 := by decide +kernel
theorem grade_31 : gradeUpper 31 = 2257 := by decide +kernel
theorem grade_32 : gradeUpper 32 = 2134 := by decide +kernel
theorem grade_33 : gradeUpper 33 = 2013 := by decide +kernel
theorem grade_34 : gradeUpper 34 = 1893 := by decide +kernel
theorem grade_35 : gradeUpper 35 = 1777 := by decide +kernel
theorem grade_36 : gradeUpper 36 = 1665 := by decide +kernel
theorem grade_37 : gradeUpper 37 = 1555 := by decide +kernel
theorem grade_38 : gradeUpper 38 = 1448 := by decide +kernel
theorem grade_39 : gradeUpper 39 = 1346 := by decide +kernel
theorem grade_40 : gradeUpper 40 = 1246 := by decide +kernel
theorem grade_41 : gradeUpper 41 = 1150 := by decide +kernel
theorem grade_42 : gradeUpper 42 = 1060 := by decide +kernel
theorem grade_43 : gradeUpper 43 = 970 := by decide +kernel
theorem grade_44 : gradeUpper 44 = 887 := by decide +kernel
theorem grade_45 : gradeUpper 45 = 806 := by decide +kernel
theorem grade_46 : gradeUpper 46 = 730 := by decide +kernel
theorem grade_47 : gradeUpper 47 = 658 := by decide +kernel
theorem grade_48 : gradeUpper 48 = 590 := by decide +kernel
theorem grade_49 : gradeUpper 49 = 526 := by decide +kernel
theorem grade_50 : gradeUpper 50 = 466 := by decide +kernel
theorem grade_51 : gradeUpper 51 = 410 := by decide +kernel
theorem grade_52 : gradeUpper 52 = 359 := by decide +kernel
theorem grade_53 : gradeUpper 53 = 310 := by decide +kernel
theorem grade_54 : gradeUpper 54 = 268 := by decide +kernel
theorem grade_55 : gradeUpper 55 = 226 := by decide +kernel
theorem grade_56 : gradeUpper 56 = 190 := by decide +kernel
theorem grade_57 : gradeUpper 57 = 158 := by decide +kernel
theorem grade_58 : gradeUpper 58 = 128 := by decide +kernel
theorem grade_59 : gradeUpper 59 = 103 := by decide +kernel
theorem grade_60 : gradeUpper 60 = 81 := by decide +kernel
theorem grade_61 : gradeUpper 61 = 61 := by decide +kernel
theorem grade_62 : gradeUpper 62 = 45 := by decide +kernel
theorem grade_63 : gradeUpper 63 = 33 := by decide +kernel
theorem grade_64 : gradeUpper 64 = 22 := by decide +kernel
theorem grade_table (s : Fin 65) : gradeUpper s.val = ([48,141,276,450,660,903,1176,1476,1800,2145,2508,2849,3132,3360,3536,3663,3744,3782,3780,3741,3668,3564,3432,3300,3168,3036,2904,2772,2641,2511,2383,2257,2134,2013,1893,1777,1665,1555,1448,1346,1246,1150,1060,970,887,806,730,658,590,526,466,410,359,310,268,226,190,158,128,103,81,61,45,33,22] : List ℕ).getD s.val 0 := by
  fin_cases s
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
theorem envelope_upper : envelopeUpper = 104120 := by
  change (∑ s : Fin 65, gradeUpper s.val) = 104120
  simp_rw [grade_table]
  decide +kernel
theorem envelope_upper_eq_block : envelopeUpper = blockUpper := by
  rw [envelope_upper, block_upper]
end Sol1.C52
end
