import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import ProximityPrize.SubmissionLower.Fast003
set_option Elab.async false

section PackSource_C42SourceArithmetic
set_option autoImplicit true
/-! Exact finite source indexing and closed combinatorial arithmetic for C42.
The closed block formulas are not, by themselves, a proof about the polynomial
constraint map's support or rank; that remaining bridge is kept separate. -/

namespace Sol1.C42

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
open ReedSolomon.HiddenDerivative PolynomialDifferential

abbrev Jet := (s : Fin 65) × (e2 : Fin (min s.val 10 + 1)) ×
  Fin (min (s.val - e2.val) (21 - s.val / 62 - 2 * e2.val) + 1)

def e1 (j : Jet) : ℕ := j.2.2.val
def e2 (j : Jet) : ℕ := j.2.1.val
def e0 (j : Jet) : ℕ := j.1.val - e2 j - e1 j
def width (j : Jet) : ℕ := 48 * 180246 - 131072 * j.1.val + e1 j + 2 * e2 j
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

theorem jet_order (j : Jet) : e1 j + 2 * e2 j ≤ 21 - j.1.val / 62 := by
  have h1 := j.2.2.isLt
  simp only [e1, e2]
  omega

theorem width_lower (j : Jet) : 263200 ≤ width j := by
  have hs : j.1.val ≤ 64 := Nat.le_of_lt_succ j.1.isLt
  have hmul : 131072 * j.1.val ≤ 131072 * 64 := Nat.mul_le_mul_left 131072 hs
  have hbase : 48 * 180246 - 131072 * 64 ≤ 48 * 180246 - 131072 * j.1.val :=
    Nat.sub_le_sub_left hmul (48 * 180246)
  have hnum : 48 * 180246 - 131072 * 64 = 263200 := by decide
  unfold width
  exact ((hnum ▸ hbase).trans (Nat.le_add_right _ (e1 j))).trans (Nat.le_add_right _ (2 * e2 j))

theorem source_weight_lt (i : SourceIndex) :
    i.2.val + 131072 * e0 i.1 + 131071 * e1 i.1 + 131070 * e2 i.1 < 48 * 180246 := by
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
    Finsupp.weight (differentialWeight 131072) (columns i).exponent < 48 * 180246 := by
  simpa [SourceColumn.weight_exponent, columns, differentialWeight, Fin.sum_univ_two,
    Nat.add_assoc, Nat.mul_comm] using
    source_weight_lt i

def sourceTotal : ℕ := ∑ j : Jet, width j

theorem jet_count : Fintype.card Jet = 7161 := by decide +kernel
theorem source_total : sourceTotal = 27293571547 := by decide +kernel

/-- Cardinality is a sum over7161 jet triples, never an enumeration of the
27293571547-dimensional full source index. -/
theorem source_card : Fintype.card SourceIndex = 27293571547 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact source_total


end Sol1.C42
end PackSource_C42SourceArithmetic

section PackSource_C42BlockArithmetic
set_option autoImplicit true
/-! Exact evaluations of the closed block-count formulas.
The proof that these count the actual coefficient-map blocks is separate. -/
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

def localColumns : ℕ := ∑ s : Fin 65, ∑ gi : Fin 69, columnCount s.val ((gi.val : ℤ) - 21)
def reachableRows : ℕ := ∑ s : Fin 65, ∑ gi : Fin 69,
  if 0 < columnCount s.val ((gi.val : ℤ) - 21) then rowCount s.val ((gi.val : ℤ) - 21) else 0
def nonzeroBlocks : ℕ := ∑ s : Fin 65, ∑ gi : Fin 69,
  if 0 < columnCount s.val ((gi.val : ℤ) - 21) then 1 else 0

private def pack2BlockUpperRow (s : Fin 65) : ℕ := ∑ gi : Fin 69,
  min (columnCount s.val ((gi.val : ℤ) - 21)) (rowCount s.val ((gi.val : ℤ) - 21))

private def pack2BlockUpperTable : Fin 65 → ℕ := ![48, 141, 276, 450, 660, 903, 1176, 1476, 1800, 2145, 2508, 2849, 3132, 3360, 3536, 3663, 3744, 3782, 3780, 3741, 3668, 3564, 3432, 3300, 3168, 3036, 2904, 2772, 2641, 2511, 2383, 2257, 2134, 2013, 1893, 1777, 1665, 1555, 1448, 1346, 1246, 1150, 1060, 970, 887, 806, 730, 658, 590, 526, 466, 410, 359, 310, 268, 226, 190, 158, 128, 103, 81, 61, 45, 33, 22]

private theorem pack2BlockUpperCheck0 : pack2BlockUpperRow 0 = 48 := by decide +kernel

private theorem pack2BlockUpperCheck1 : pack2BlockUpperRow 1 = 141 := by decide +kernel

private theorem pack2BlockUpperCheck2 : pack2BlockUpperRow 2 = 276 := by decide +kernel

private theorem pack2BlockUpperCheck3 : pack2BlockUpperRow 3 = 450 := by decide +kernel

private theorem pack2BlockUpperCheck4 : pack2BlockUpperRow 4 = 660 := by decide +kernel

private theorem pack2BlockUpperCheck5 : pack2BlockUpperRow 5 = 903 := by decide +kernel

private theorem pack2BlockUpperCheck6 : pack2BlockUpperRow 6 = 1176 := by decide +kernel

private theorem pack2BlockUpperCheck7 : pack2BlockUpperRow 7 = 1476 := by decide +kernel

private theorem pack2BlockUpperCheck8 : pack2BlockUpperRow 8 = 1800 := by decide +kernel

private theorem pack2BlockUpperCheck9 : pack2BlockUpperRow 9 = 2145 := by decide +kernel

private theorem pack2BlockUpperCheck10 : pack2BlockUpperRow 10 = 2508 := by decide +kernel

private theorem pack2BlockUpperCheck11 : pack2BlockUpperRow 11 = 2849 := by decide +kernel

private theorem pack2BlockUpperCheck12 : pack2BlockUpperRow 12 = 3132 := by decide +kernel

private theorem pack2BlockUpperCheck13 : pack2BlockUpperRow 13 = 3360 := by decide +kernel

private theorem pack2BlockUpperCheck14 : pack2BlockUpperRow 14 = 3536 := by decide +kernel

private theorem pack2BlockUpperCheck15 : pack2BlockUpperRow 15 = 3663 := by decide +kernel

private theorem pack2BlockUpperCheck16 : pack2BlockUpperRow 16 = 3744 := by decide +kernel

private theorem pack2BlockUpperCheck17 : pack2BlockUpperRow 17 = 3782 := by decide +kernel

private theorem pack2BlockUpperCheck18 : pack2BlockUpperRow 18 = 3780 := by decide +kernel

private theorem pack2BlockUpperCheck19 : pack2BlockUpperRow 19 = 3741 := by decide +kernel

private theorem pack2BlockUpperCheck20 : pack2BlockUpperRow 20 = 3668 := by decide +kernel

private theorem pack2BlockUpperCheck21 : pack2BlockUpperRow 21 = 3564 := by decide +kernel

private theorem pack2BlockUpperCheck22 : pack2BlockUpperRow 22 = 3432 := by decide +kernel

private theorem pack2BlockUpperCheck23 : pack2BlockUpperRow 23 = 3300 := by decide +kernel

private theorem pack2BlockUpperCheck24 : pack2BlockUpperRow 24 = 3168 := by decide +kernel

private theorem pack2BlockUpperCheck25 : pack2BlockUpperRow 25 = 3036 := by decide +kernel

private theorem pack2BlockUpperCheck26 : pack2BlockUpperRow 26 = 2904 := by decide +kernel

private theorem pack2BlockUpperCheck27 : pack2BlockUpperRow 27 = 2772 := by decide +kernel

private theorem pack2BlockUpperCheck28 : pack2BlockUpperRow 28 = 2641 := by decide +kernel

private theorem pack2BlockUpperCheck29 : pack2BlockUpperRow 29 = 2511 := by decide +kernel

private theorem pack2BlockUpperCheck30 : pack2BlockUpperRow 30 = 2383 := by decide +kernel

private theorem pack2BlockUpperCheck31 : pack2BlockUpperRow 31 = 2257 := by decide +kernel

private theorem pack2BlockUpperCheck32 : pack2BlockUpperRow 32 = 2134 := by decide +kernel

private theorem pack2BlockUpperCheck33 : pack2BlockUpperRow 33 = 2013 := by decide +kernel

private theorem pack2BlockUpperCheck34 : pack2BlockUpperRow 34 = 1893 := by decide +kernel

private theorem pack2BlockUpperCheck35 : pack2BlockUpperRow 35 = 1777 := by decide +kernel

private theorem pack2BlockUpperCheck36 : pack2BlockUpperRow 36 = 1665 := by decide +kernel

private theorem pack2BlockUpperCheck37 : pack2BlockUpperRow 37 = 1555 := by decide +kernel

private theorem pack2BlockUpperCheck38 : pack2BlockUpperRow 38 = 1448 := by decide +kernel

private theorem pack2BlockUpperCheck39 : pack2BlockUpperRow 39 = 1346 := by decide +kernel

private theorem pack2BlockUpperCheck40 : pack2BlockUpperRow 40 = 1246 := by decide +kernel

private theorem pack2BlockUpperCheck41 : pack2BlockUpperRow 41 = 1150 := by decide +kernel

private theorem pack2BlockUpperCheck42 : pack2BlockUpperRow 42 = 1060 := by decide +kernel

private theorem pack2BlockUpperCheck43 : pack2BlockUpperRow 43 = 970 := by decide +kernel

private theorem pack2BlockUpperCheck44 : pack2BlockUpperRow 44 = 887 := by decide +kernel

private theorem pack2BlockUpperCheck45 : pack2BlockUpperRow 45 = 806 := by decide +kernel

private theorem pack2BlockUpperCheck46 : pack2BlockUpperRow 46 = 730 := by decide +kernel

private theorem pack2BlockUpperCheck47 : pack2BlockUpperRow 47 = 658 := by decide +kernel

private theorem pack2BlockUpperCheck48 : pack2BlockUpperRow 48 = 590 := by decide +kernel

private theorem pack2BlockUpperCheck49 : pack2BlockUpperRow 49 = 526 := by decide +kernel

private theorem pack2BlockUpperCheck50 : pack2BlockUpperRow 50 = 466 := by decide +kernel

private theorem pack2BlockUpperCheck51 : pack2BlockUpperRow 51 = 410 := by decide +kernel

private theorem pack2BlockUpperCheck52 : pack2BlockUpperRow 52 = 359 := by decide +kernel

private theorem pack2BlockUpperCheck53 : pack2BlockUpperRow 53 = 310 := by decide +kernel

private theorem pack2BlockUpperCheck54 : pack2BlockUpperRow 54 = 268 := by decide +kernel

private theorem pack2BlockUpperCheck55 : pack2BlockUpperRow 55 = 226 := by decide +kernel

private theorem pack2BlockUpperCheck56 : pack2BlockUpperRow 56 = 190 := by decide +kernel

private theorem pack2BlockUpperCheck57 : pack2BlockUpperRow 57 = 158 := by decide +kernel

private theorem pack2BlockUpperCheck58 : pack2BlockUpperRow 58 = 128 := by decide +kernel

private theorem pack2BlockUpperCheck59 : pack2BlockUpperRow 59 = 103 := by decide +kernel

private theorem pack2BlockUpperCheck60 : pack2BlockUpperRow 60 = 81 := by decide +kernel

private theorem pack2BlockUpperCheck61 : pack2BlockUpperRow 61 = 61 := by decide +kernel

private theorem pack2BlockUpperCheck62 : pack2BlockUpperRow 62 = 45 := by decide +kernel

private theorem pack2BlockUpperCheck63 : pack2BlockUpperRow 63 = 33 := by decide +kernel

private theorem pack2BlockUpperCheck64 : pack2BlockUpperRow 64 = 22 := by decide +kernel

private theorem pack2BlockUpperRows (s : Fin 65) : pack2BlockUpperRow s = pack2BlockUpperTable s := by
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
private def pack2LocalColumnsRow (s : Fin 65) : ℕ := ∑ gi : Fin 69, columnCount s.val ((gi.val : ℤ) - 21)

private def pack2LocalColumnsTable : Fin 65 → ℕ := ![48, 144, 288, 480, 720, 1008, 1344, 1728, 2160, 2640, 3168, 3696, 4176, 4608, 4992, 5328, 5616, 5856, 6048, 6192, 6288, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336, 6336]

private theorem pack2LocalColumnsCheck0 : pack2LocalColumnsRow 0 = 48 := by decide +kernel

private theorem pack2LocalColumnsCheck1 : pack2LocalColumnsRow 1 = 144 := by decide +kernel

private theorem pack2LocalColumnsCheck2 : pack2LocalColumnsRow 2 = 288 := by decide +kernel

private theorem pack2LocalColumnsCheck3 : pack2LocalColumnsRow 3 = 480 := by decide +kernel

private theorem pack2LocalColumnsCheck4 : pack2LocalColumnsRow 4 = 720 := by decide +kernel

private theorem pack2LocalColumnsCheck5 : pack2LocalColumnsRow 5 = 1008 := by decide +kernel

private theorem pack2LocalColumnsCheck6 : pack2LocalColumnsRow 6 = 1344 := by decide +kernel

private theorem pack2LocalColumnsCheck7 : pack2LocalColumnsRow 7 = 1728 := by decide +kernel

private theorem pack2LocalColumnsCheck8 : pack2LocalColumnsRow 8 = 2160 := by decide +kernel

private theorem pack2LocalColumnsCheck9 : pack2LocalColumnsRow 9 = 2640 := by decide +kernel

private theorem pack2LocalColumnsCheck10 : pack2LocalColumnsRow 10 = 3168 := by decide +kernel

private theorem pack2LocalColumnsCheck11 : pack2LocalColumnsRow 11 = 3696 := by decide +kernel

private theorem pack2LocalColumnsCheck12 : pack2LocalColumnsRow 12 = 4176 := by decide +kernel

private theorem pack2LocalColumnsCheck13 : pack2LocalColumnsRow 13 = 4608 := by decide +kernel

private theorem pack2LocalColumnsCheck14 : pack2LocalColumnsRow 14 = 4992 := by decide +kernel

private theorem pack2LocalColumnsCheck15 : pack2LocalColumnsRow 15 = 5328 := by decide +kernel

private theorem pack2LocalColumnsCheck16 : pack2LocalColumnsRow 16 = 5616 := by decide +kernel

private theorem pack2LocalColumnsCheck17 : pack2LocalColumnsRow 17 = 5856 := by decide +kernel

private theorem pack2LocalColumnsCheck18 : pack2LocalColumnsRow 18 = 6048 := by decide +kernel

private theorem pack2LocalColumnsCheck19 : pack2LocalColumnsRow 19 = 6192 := by decide +kernel

private theorem pack2LocalColumnsCheck20 : pack2LocalColumnsRow 20 = 6288 := by decide +kernel

private theorem pack2LocalColumnsCheck21 : pack2LocalColumnsRow 21 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck22 : pack2LocalColumnsRow 22 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck23 : pack2LocalColumnsRow 23 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck24 : pack2LocalColumnsRow 24 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck25 : pack2LocalColumnsRow 25 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck26 : pack2LocalColumnsRow 26 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck27 : pack2LocalColumnsRow 27 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck28 : pack2LocalColumnsRow 28 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck29 : pack2LocalColumnsRow 29 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck30 : pack2LocalColumnsRow 30 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck31 : pack2LocalColumnsRow 31 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck32 : pack2LocalColumnsRow 32 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck33 : pack2LocalColumnsRow 33 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck34 : pack2LocalColumnsRow 34 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck35 : pack2LocalColumnsRow 35 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck36 : pack2LocalColumnsRow 36 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck37 : pack2LocalColumnsRow 37 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck38 : pack2LocalColumnsRow 38 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck39 : pack2LocalColumnsRow 39 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck40 : pack2LocalColumnsRow 40 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck41 : pack2LocalColumnsRow 41 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck42 : pack2LocalColumnsRow 42 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck43 : pack2LocalColumnsRow 43 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck44 : pack2LocalColumnsRow 44 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck45 : pack2LocalColumnsRow 45 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck46 : pack2LocalColumnsRow 46 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck47 : pack2LocalColumnsRow 47 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck48 : pack2LocalColumnsRow 48 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck49 : pack2LocalColumnsRow 49 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck50 : pack2LocalColumnsRow 50 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck51 : pack2LocalColumnsRow 51 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck52 : pack2LocalColumnsRow 52 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck53 : pack2LocalColumnsRow 53 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck54 : pack2LocalColumnsRow 54 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck55 : pack2LocalColumnsRow 55 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck56 : pack2LocalColumnsRow 56 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck57 : pack2LocalColumnsRow 57 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck58 : pack2LocalColumnsRow 58 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck59 : pack2LocalColumnsRow 59 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck60 : pack2LocalColumnsRow 60 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck61 : pack2LocalColumnsRow 61 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck62 : pack2LocalColumnsRow 62 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck63 : pack2LocalColumnsRow 63 = 6336 := by decide +kernel

private theorem pack2LocalColumnsCheck64 : pack2LocalColumnsRow 64 = 6336 := by decide +kernel

private theorem pack2LocalColumnsRows (s : Fin 65) : pack2LocalColumnsRow s = pack2LocalColumnsTable s := by
  fin_cases s
  · exact pack2LocalColumnsCheck0
  · exact pack2LocalColumnsCheck1
  · exact pack2LocalColumnsCheck2
  · exact pack2LocalColumnsCheck3
  · exact pack2LocalColumnsCheck4
  · exact pack2LocalColumnsCheck5
  · exact pack2LocalColumnsCheck6
  · exact pack2LocalColumnsCheck7
  · exact pack2LocalColumnsCheck8
  · exact pack2LocalColumnsCheck9
  · exact pack2LocalColumnsCheck10
  · exact pack2LocalColumnsCheck11
  · exact pack2LocalColumnsCheck12
  · exact pack2LocalColumnsCheck13
  · exact pack2LocalColumnsCheck14
  · exact pack2LocalColumnsCheck15
  · exact pack2LocalColumnsCheck16
  · exact pack2LocalColumnsCheck17
  · exact pack2LocalColumnsCheck18
  · exact pack2LocalColumnsCheck19
  · exact pack2LocalColumnsCheck20
  · exact pack2LocalColumnsCheck21
  · exact pack2LocalColumnsCheck22
  · exact pack2LocalColumnsCheck23
  · exact pack2LocalColumnsCheck24
  · exact pack2LocalColumnsCheck25
  · exact pack2LocalColumnsCheck26
  · exact pack2LocalColumnsCheck27
  · exact pack2LocalColumnsCheck28
  · exact pack2LocalColumnsCheck29
  · exact pack2LocalColumnsCheck30
  · exact pack2LocalColumnsCheck31
  · exact pack2LocalColumnsCheck32
  · exact pack2LocalColumnsCheck33
  · exact pack2LocalColumnsCheck34
  · exact pack2LocalColumnsCheck35
  · exact pack2LocalColumnsCheck36
  · exact pack2LocalColumnsCheck37
  · exact pack2LocalColumnsCheck38
  · exact pack2LocalColumnsCheck39
  · exact pack2LocalColumnsCheck40
  · exact pack2LocalColumnsCheck41
  · exact pack2LocalColumnsCheck42
  · exact pack2LocalColumnsCheck43
  · exact pack2LocalColumnsCheck44
  · exact pack2LocalColumnsCheck45
  · exact pack2LocalColumnsCheck46
  · exact pack2LocalColumnsCheck47
  · exact pack2LocalColumnsCheck48
  · exact pack2LocalColumnsCheck49
  · exact pack2LocalColumnsCheck50
  · exact pack2LocalColumnsCheck51
  · exact pack2LocalColumnsCheck52
  · exact pack2LocalColumnsCheck53
  · exact pack2LocalColumnsCheck54
  · exact pack2LocalColumnsCheck55
  · exact pack2LocalColumnsCheck56
  · exact pack2LocalColumnsCheck57
  · exact pack2LocalColumnsCheck58
  · exact pack2LocalColumnsCheck59
  · exact pack2LocalColumnsCheck60
  · exact pack2LocalColumnsCheck61
  · exact pack2LocalColumnsCheck62
  · exact pack2LocalColumnsCheck63
  · exact pack2LocalColumnsCheck64

theorem local_columns : localColumns = 345312 := by
  change (∑ s : Fin 65, pack2LocalColumnsRow s) = 345312
  simp_rw [pack2LocalColumnsRows]
  decide +kernel
private def pack2ReachableRowsRow (s : Fin 65) : ℕ := ∑ gi : Fin 69,
  if 0 < columnCount s.val ((gi.val : ℤ) - 21) then rowCount s.val ((gi.val : ℤ) - 21) else 0

private def pack2ReachableRowsTable : Fin 65 → ℕ := ![48, 141, 276, 450, 660, 903, 1176, 1476, 1800, 2145, 2508, 2884, 3267, 3650, 4026, 4388, 4729, 5045, 5332, 5586, 5803, 5979, 6110, 6193, 6225, 6203, 6124, 5988, 5799, 5565, 5295, 4998, 4683, 4359, 4035, 3719, 3416, 3128, 2856, 2600, 2360, 2135, 1925, 1729, 1547, 1378, 1222, 1078, 946, 825, 715, 615, 525, 444, 372, 308, 252, 203, 161, 125, 95, 70, 50, 34, 22]

private theorem pack2ReachableRowsCheck0 : pack2ReachableRowsRow 0 = 48 := by decide +kernel

private theorem pack2ReachableRowsCheck1 : pack2ReachableRowsRow 1 = 141 := by decide +kernel

private theorem pack2ReachableRowsCheck2 : pack2ReachableRowsRow 2 = 276 := by decide +kernel

private theorem pack2ReachableRowsCheck3 : pack2ReachableRowsRow 3 = 450 := by decide +kernel

private theorem pack2ReachableRowsCheck4 : pack2ReachableRowsRow 4 = 660 := by decide +kernel

private theorem pack2ReachableRowsCheck5 : pack2ReachableRowsRow 5 = 903 := by decide +kernel

private theorem pack2ReachableRowsCheck6 : pack2ReachableRowsRow 6 = 1176 := by decide +kernel

private theorem pack2ReachableRowsCheck7 : pack2ReachableRowsRow 7 = 1476 := by decide +kernel

private theorem pack2ReachableRowsCheck8 : pack2ReachableRowsRow 8 = 1800 := by decide +kernel

private theorem pack2ReachableRowsCheck9 : pack2ReachableRowsRow 9 = 2145 := by decide +kernel

private theorem pack2ReachableRowsCheck10 : pack2ReachableRowsRow 10 = 2508 := by decide +kernel

private theorem pack2ReachableRowsCheck11 : pack2ReachableRowsRow 11 = 2884 := by decide +kernel

private theorem pack2ReachableRowsCheck12 : pack2ReachableRowsRow 12 = 3267 := by decide +kernel

private theorem pack2ReachableRowsCheck13 : pack2ReachableRowsRow 13 = 3650 := by decide +kernel

private theorem pack2ReachableRowsCheck14 : pack2ReachableRowsRow 14 = 4026 := by decide +kernel

private theorem pack2ReachableRowsCheck15 : pack2ReachableRowsRow 15 = 4388 := by decide +kernel

private theorem pack2ReachableRowsCheck16 : pack2ReachableRowsRow 16 = 4729 := by decide +kernel

private theorem pack2ReachableRowsCheck17 : pack2ReachableRowsRow 17 = 5045 := by decide +kernel

private theorem pack2ReachableRowsCheck18 : pack2ReachableRowsRow 18 = 5332 := by decide +kernel

private theorem pack2ReachableRowsCheck19 : pack2ReachableRowsRow 19 = 5586 := by decide +kernel

private theorem pack2ReachableRowsCheck20 : pack2ReachableRowsRow 20 = 5803 := by decide +kernel

private theorem pack2ReachableRowsCheck21 : pack2ReachableRowsRow 21 = 5979 := by decide +kernel

private theorem pack2ReachableRowsCheck22 : pack2ReachableRowsRow 22 = 6110 := by decide +kernel

private theorem pack2ReachableRowsCheck23 : pack2ReachableRowsRow 23 = 6193 := by decide +kernel

private theorem pack2ReachableRowsCheck24 : pack2ReachableRowsRow 24 = 6225 := by decide +kernel

private theorem pack2ReachableRowsCheck25 : pack2ReachableRowsRow 25 = 6203 := by decide +kernel

private theorem pack2ReachableRowsCheck26 : pack2ReachableRowsRow 26 = 6124 := by decide +kernel

private theorem pack2ReachableRowsCheck27 : pack2ReachableRowsRow 27 = 5988 := by decide +kernel

private theorem pack2ReachableRowsCheck28 : pack2ReachableRowsRow 28 = 5799 := by decide +kernel

private theorem pack2ReachableRowsCheck29 : pack2ReachableRowsRow 29 = 5565 := by decide +kernel

private theorem pack2ReachableRowsCheck30 : pack2ReachableRowsRow 30 = 5295 := by decide +kernel

private theorem pack2ReachableRowsCheck31 : pack2ReachableRowsRow 31 = 4998 := by decide +kernel

private theorem pack2ReachableRowsCheck32 : pack2ReachableRowsRow 32 = 4683 := by decide +kernel

private theorem pack2ReachableRowsCheck33 : pack2ReachableRowsRow 33 = 4359 := by decide +kernel

private theorem pack2ReachableRowsCheck34 : pack2ReachableRowsRow 34 = 4035 := by decide +kernel

private theorem pack2ReachableRowsCheck35 : pack2ReachableRowsRow 35 = 3719 := by decide +kernel

private theorem pack2ReachableRowsCheck36 : pack2ReachableRowsRow 36 = 3416 := by decide +kernel

private theorem pack2ReachableRowsCheck37 : pack2ReachableRowsRow 37 = 3128 := by decide +kernel

private theorem pack2ReachableRowsCheck38 : pack2ReachableRowsRow 38 = 2856 := by decide +kernel

private theorem pack2ReachableRowsCheck39 : pack2ReachableRowsRow 39 = 2600 := by decide +kernel

private theorem pack2ReachableRowsCheck40 : pack2ReachableRowsRow 40 = 2360 := by decide +kernel

private theorem pack2ReachableRowsCheck41 : pack2ReachableRowsRow 41 = 2135 := by decide +kernel

private theorem pack2ReachableRowsCheck42 : pack2ReachableRowsRow 42 = 1925 := by decide +kernel

private theorem pack2ReachableRowsCheck43 : pack2ReachableRowsRow 43 = 1729 := by decide +kernel

private theorem pack2ReachableRowsCheck44 : pack2ReachableRowsRow 44 = 1547 := by decide +kernel

private theorem pack2ReachableRowsCheck45 : pack2ReachableRowsRow 45 = 1378 := by decide +kernel

private theorem pack2ReachableRowsCheck46 : pack2ReachableRowsRow 46 = 1222 := by decide +kernel

private theorem pack2ReachableRowsCheck47 : pack2ReachableRowsRow 47 = 1078 := by decide +kernel

private theorem pack2ReachableRowsCheck48 : pack2ReachableRowsRow 48 = 946 := by decide +kernel

private theorem pack2ReachableRowsCheck49 : pack2ReachableRowsRow 49 = 825 := by decide +kernel

private theorem pack2ReachableRowsCheck50 : pack2ReachableRowsRow 50 = 715 := by decide +kernel

private theorem pack2ReachableRowsCheck51 : pack2ReachableRowsRow 51 = 615 := by decide +kernel

private theorem pack2ReachableRowsCheck52 : pack2ReachableRowsRow 52 = 525 := by decide +kernel

private theorem pack2ReachableRowsCheck53 : pack2ReachableRowsRow 53 = 444 := by decide +kernel

private theorem pack2ReachableRowsCheck54 : pack2ReachableRowsRow 54 = 372 := by decide +kernel

private theorem pack2ReachableRowsCheck55 : pack2ReachableRowsRow 55 = 308 := by decide +kernel

private theorem pack2ReachableRowsCheck56 : pack2ReachableRowsRow 56 = 252 := by decide +kernel

private theorem pack2ReachableRowsCheck57 : pack2ReachableRowsRow 57 = 203 := by decide +kernel

private theorem pack2ReachableRowsCheck58 : pack2ReachableRowsRow 58 = 161 := by decide +kernel

private theorem pack2ReachableRowsCheck59 : pack2ReachableRowsRow 59 = 125 := by decide +kernel

private theorem pack2ReachableRowsCheck60 : pack2ReachableRowsRow 60 = 95 := by decide +kernel

private theorem pack2ReachableRowsCheck61 : pack2ReachableRowsRow 61 = 70 := by decide +kernel

private theorem pack2ReachableRowsCheck62 : pack2ReachableRowsRow 62 = 50 := by decide +kernel

private theorem pack2ReachableRowsCheck63 : pack2ReachableRowsRow 63 = 34 := by decide +kernel

private theorem pack2ReachableRowsCheck64 : pack2ReachableRowsRow 64 = 22 := by decide +kernel

private theorem pack2ReachableRowsRows (s : Fin 65) : pack2ReachableRowsRow s = pack2ReachableRowsTable s := by
  fin_cases s
  · exact pack2ReachableRowsCheck0
  · exact pack2ReachableRowsCheck1
  · exact pack2ReachableRowsCheck2
  · exact pack2ReachableRowsCheck3
  · exact pack2ReachableRowsCheck4
  · exact pack2ReachableRowsCheck5
  · exact pack2ReachableRowsCheck6
  · exact pack2ReachableRowsCheck7
  · exact pack2ReachableRowsCheck8
  · exact pack2ReachableRowsCheck9
  · exact pack2ReachableRowsCheck10
  · exact pack2ReachableRowsCheck11
  · exact pack2ReachableRowsCheck12
  · exact pack2ReachableRowsCheck13
  · exact pack2ReachableRowsCheck14
  · exact pack2ReachableRowsCheck15
  · exact pack2ReachableRowsCheck16
  · exact pack2ReachableRowsCheck17
  · exact pack2ReachableRowsCheck18
  · exact pack2ReachableRowsCheck19
  · exact pack2ReachableRowsCheck20
  · exact pack2ReachableRowsCheck21
  · exact pack2ReachableRowsCheck22
  · exact pack2ReachableRowsCheck23
  · exact pack2ReachableRowsCheck24
  · exact pack2ReachableRowsCheck25
  · exact pack2ReachableRowsCheck26
  · exact pack2ReachableRowsCheck27
  · exact pack2ReachableRowsCheck28
  · exact pack2ReachableRowsCheck29
  · exact pack2ReachableRowsCheck30
  · exact pack2ReachableRowsCheck31
  · exact pack2ReachableRowsCheck32
  · exact pack2ReachableRowsCheck33
  · exact pack2ReachableRowsCheck34
  · exact pack2ReachableRowsCheck35
  · exact pack2ReachableRowsCheck36
  · exact pack2ReachableRowsCheck37
  · exact pack2ReachableRowsCheck38
  · exact pack2ReachableRowsCheck39
  · exact pack2ReachableRowsCheck40
  · exact pack2ReachableRowsCheck41
  · exact pack2ReachableRowsCheck42
  · exact pack2ReachableRowsCheck43
  · exact pack2ReachableRowsCheck44
  · exact pack2ReachableRowsCheck45
  · exact pack2ReachableRowsCheck46
  · exact pack2ReachableRowsCheck47
  · exact pack2ReachableRowsCheck48
  · exact pack2ReachableRowsCheck49
  · exact pack2ReachableRowsCheck50
  · exact pack2ReachableRowsCheck51
  · exact pack2ReachableRowsCheck52
  · exact pack2ReachableRowsCheck53
  · exact pack2ReachableRowsCheck54
  · exact pack2ReachableRowsCheck55
  · exact pack2ReachableRowsCheck56
  · exact pack2ReachableRowsCheck57
  · exact pack2ReachableRowsCheck58
  · exact pack2ReachableRowsCheck59
  · exact pack2ReachableRowsCheck60
  · exact pack2ReachableRowsCheck61
  · exact pack2ReachableRowsCheck62
  · exact pack2ReachableRowsCheck63
  · exact pack2ReachableRowsCheck64

theorem reachable_rows : reachableRows = 168704 := by
  change (∑ s : Fin 65, pack2ReachableRowsRow s) = 168704
  simp_rw [pack2ReachableRowsRows]
  decide +kernel
private def pack2NonzeroBlocksRow (s : Fin 65) : ℕ := ∑ gi : Fin 69,
  if 0 < columnCount s.val ((gi.val : ℤ) - 21) then 1 else 0

private def pack2NonzeroBlocksTable : Fin 65 → ℕ := ![48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69]

private theorem pack2NonzeroBlocksCheck0 : pack2NonzeroBlocksRow 0 = 48 := by decide +kernel

private theorem pack2NonzeroBlocksCheck1 : pack2NonzeroBlocksRow 1 = 50 := by decide +kernel

private theorem pack2NonzeroBlocksCheck2 : pack2NonzeroBlocksRow 2 = 52 := by decide +kernel

private theorem pack2NonzeroBlocksCheck3 : pack2NonzeroBlocksRow 3 = 54 := by decide +kernel

private theorem pack2NonzeroBlocksCheck4 : pack2NonzeroBlocksRow 4 = 56 := by decide +kernel

private theorem pack2NonzeroBlocksCheck5 : pack2NonzeroBlocksRow 5 = 58 := by decide +kernel

private theorem pack2NonzeroBlocksCheck6 : pack2NonzeroBlocksRow 6 = 60 := by decide +kernel

private theorem pack2NonzeroBlocksCheck7 : pack2NonzeroBlocksRow 7 = 62 := by decide +kernel

private theorem pack2NonzeroBlocksCheck8 : pack2NonzeroBlocksRow 8 = 64 := by decide +kernel

private theorem pack2NonzeroBlocksCheck9 : pack2NonzeroBlocksRow 9 = 66 := by decide +kernel

private theorem pack2NonzeroBlocksCheck10 : pack2NonzeroBlocksRow 10 = 68 := by decide +kernel

private theorem pack2NonzeroBlocksCheck11 : pack2NonzeroBlocksRow 11 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck12 : pack2NonzeroBlocksRow 12 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck13 : pack2NonzeroBlocksRow 13 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck14 : pack2NonzeroBlocksRow 14 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck15 : pack2NonzeroBlocksRow 15 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck16 : pack2NonzeroBlocksRow 16 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck17 : pack2NonzeroBlocksRow 17 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck18 : pack2NonzeroBlocksRow 18 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck19 : pack2NonzeroBlocksRow 19 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck20 : pack2NonzeroBlocksRow 20 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck21 : pack2NonzeroBlocksRow 21 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck22 : pack2NonzeroBlocksRow 22 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck23 : pack2NonzeroBlocksRow 23 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck24 : pack2NonzeroBlocksRow 24 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck25 : pack2NonzeroBlocksRow 25 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck26 : pack2NonzeroBlocksRow 26 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck27 : pack2NonzeroBlocksRow 27 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck28 : pack2NonzeroBlocksRow 28 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck29 : pack2NonzeroBlocksRow 29 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck30 : pack2NonzeroBlocksRow 30 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck31 : pack2NonzeroBlocksRow 31 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck32 : pack2NonzeroBlocksRow 32 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck33 : pack2NonzeroBlocksRow 33 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck34 : pack2NonzeroBlocksRow 34 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck35 : pack2NonzeroBlocksRow 35 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck36 : pack2NonzeroBlocksRow 36 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck37 : pack2NonzeroBlocksRow 37 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck38 : pack2NonzeroBlocksRow 38 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck39 : pack2NonzeroBlocksRow 39 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck40 : pack2NonzeroBlocksRow 40 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck41 : pack2NonzeroBlocksRow 41 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck42 : pack2NonzeroBlocksRow 42 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck43 : pack2NonzeroBlocksRow 43 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck44 : pack2NonzeroBlocksRow 44 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck45 : pack2NonzeroBlocksRow 45 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck46 : pack2NonzeroBlocksRow 46 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck47 : pack2NonzeroBlocksRow 47 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck48 : pack2NonzeroBlocksRow 48 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck49 : pack2NonzeroBlocksRow 49 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck50 : pack2NonzeroBlocksRow 50 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck51 : pack2NonzeroBlocksRow 51 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck52 : pack2NonzeroBlocksRow 52 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck53 : pack2NonzeroBlocksRow 53 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck54 : pack2NonzeroBlocksRow 54 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck55 : pack2NonzeroBlocksRow 55 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck56 : pack2NonzeroBlocksRow 56 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck57 : pack2NonzeroBlocksRow 57 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck58 : pack2NonzeroBlocksRow 58 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck59 : pack2NonzeroBlocksRow 59 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck60 : pack2NonzeroBlocksRow 60 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck61 : pack2NonzeroBlocksRow 61 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck62 : pack2NonzeroBlocksRow 62 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck63 : pack2NonzeroBlocksRow 63 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksCheck64 : pack2NonzeroBlocksRow 64 = 69 := by decide +kernel

private theorem pack2NonzeroBlocksRows (s : Fin 65) : pack2NonzeroBlocksRow s = pack2NonzeroBlocksTable s := by
  fin_cases s
  · exact pack2NonzeroBlocksCheck0
  · exact pack2NonzeroBlocksCheck1
  · exact pack2NonzeroBlocksCheck2
  · exact pack2NonzeroBlocksCheck3
  · exact pack2NonzeroBlocksCheck4
  · exact pack2NonzeroBlocksCheck5
  · exact pack2NonzeroBlocksCheck6
  · exact pack2NonzeroBlocksCheck7
  · exact pack2NonzeroBlocksCheck8
  · exact pack2NonzeroBlocksCheck9
  · exact pack2NonzeroBlocksCheck10
  · exact pack2NonzeroBlocksCheck11
  · exact pack2NonzeroBlocksCheck12
  · exact pack2NonzeroBlocksCheck13
  · exact pack2NonzeroBlocksCheck14
  · exact pack2NonzeroBlocksCheck15
  · exact pack2NonzeroBlocksCheck16
  · exact pack2NonzeroBlocksCheck17
  · exact pack2NonzeroBlocksCheck18
  · exact pack2NonzeroBlocksCheck19
  · exact pack2NonzeroBlocksCheck20
  · exact pack2NonzeroBlocksCheck21
  · exact pack2NonzeroBlocksCheck22
  · exact pack2NonzeroBlocksCheck23
  · exact pack2NonzeroBlocksCheck24
  · exact pack2NonzeroBlocksCheck25
  · exact pack2NonzeroBlocksCheck26
  · exact pack2NonzeroBlocksCheck27
  · exact pack2NonzeroBlocksCheck28
  · exact pack2NonzeroBlocksCheck29
  · exact pack2NonzeroBlocksCheck30
  · exact pack2NonzeroBlocksCheck31
  · exact pack2NonzeroBlocksCheck32
  · exact pack2NonzeroBlocksCheck33
  · exact pack2NonzeroBlocksCheck34
  · exact pack2NonzeroBlocksCheck35
  · exact pack2NonzeroBlocksCheck36
  · exact pack2NonzeroBlocksCheck37
  · exact pack2NonzeroBlocksCheck38
  · exact pack2NonzeroBlocksCheck39
  · exact pack2NonzeroBlocksCheck40
  · exact pack2NonzeroBlocksCheck41
  · exact pack2NonzeroBlocksCheck42
  · exact pack2NonzeroBlocksCheck43
  · exact pack2NonzeroBlocksCheck44
  · exact pack2NonzeroBlocksCheck45
  · exact pack2NonzeroBlocksCheck46
  · exact pack2NonzeroBlocksCheck47
  · exact pack2NonzeroBlocksCheck48
  · exact pack2NonzeroBlocksCheck49
  · exact pack2NonzeroBlocksCheck50
  · exact pack2NonzeroBlocksCheck51
  · exact pack2NonzeroBlocksCheck52
  · exact pack2NonzeroBlocksCheck53
  · exact pack2NonzeroBlocksCheck54
  · exact pack2NonzeroBlocksCheck55
  · exact pack2NonzeroBlocksCheck56
  · exact pack2NonzeroBlocksCheck57
  · exact pack2NonzeroBlocksCheck58
  · exact pack2NonzeroBlocksCheck59
  · exact pack2NonzeroBlocksCheck60
  · exact pack2NonzeroBlocksCheck61
  · exact pack2NonzeroBlocksCheck62
  · exact pack2NonzeroBlocksCheck63
  · exact pack2NonzeroBlocksCheck64

theorem nonzero_blocks : nonzeroBlocks = 4364 := by
  change (∑ s : Fin 65, pack2NonzeroBlocksRow s) = 4364
  simp_rw [pack2NonzeroBlocksRows]
  decide +kernel
theorem local_columns_per_jet : localColumns = 345312 := by
  rw [local_columns]

theorem global_rank_allowance : (262144 : ℕ) * blockUpper = 27294433280 := by
  rw [block_upper]

-- source_surplus / strict_source_surplus (blockUpper = 104120) do not hold at A = 180246; the list
-- interpolation uses Sol1.C52.strict_source_surplusT (exact-fibre bound 104088, Fast010).


end Sol1.C42
end PackSource_C42BlockArithmetic

section PackSource_C42CoarseBlockArithmetic
set_option autoImplicit true
/-! A parity-free row overestimate gives exactly the same final min-block sum.
Its applicability to the coefficient map is a separate structural proof. -/
namespace Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators

def rowCountCoarse (s : ℕ) (g : ℤ) : ℕ :=
  let L : ℤ := 48 - g - s
  let lo : ℤ := max 0 (-g)
  let hi : ℤ := min 21 (47 - g)
  if 0 < L ∧ lo ≤ hi then
    ∑ b ∈ Finset.range (min s ((L - 1) / 2).toNat + 1),
      (((min ((s : ℤ) - b - 1) (L - 1 - 2 * b)) - max 0 (lo - s + b) + 1).toNat +
        if 2 * (b : ℤ) + ((s : ℤ) - b) < L ∧ lo ≤ 2 * ((s : ℤ) - b) then 1 else 0)
  else 0

def coarseUpper : ℕ := ∑ s : Fin 65, ∑ gi : Fin 69,
  min (columnCount s.val ((gi.val : ℤ) - 21)) (rowCountCoarse s.val ((gi.val : ℤ) - 21))

private def pack2CoarseUpperRow (s : Fin 65) : ℕ := ∑ gi : Fin 69,
  min (columnCount s.val ((gi.val : ℤ) - 21)) (rowCountCoarse s.val ((gi.val : ℤ) - 21))

private def pack2CoarseUpperTable : Fin 65 → ℕ := ![48, 141, 276, 450, 660, 903, 1176, 1476, 1800, 2145, 2508, 2849, 3132, 3360, 3536, 3663, 3744, 3782, 3780, 3741, 3668, 3564, 3432, 3300, 3168, 3036, 2904, 2772, 2641, 2511, 2383, 2257, 2134, 2013, 1893, 1777, 1665, 1555, 1448, 1346, 1246, 1150, 1060, 970, 887, 806, 730, 658, 590, 526, 466, 410, 359, 310, 268, 226, 190, 158, 128, 103, 81, 61, 45, 33, 22]

private theorem pack2CoarseUpperCheck0 : pack2CoarseUpperRow 0 = 48 := by decide +kernel

private theorem pack2CoarseUpperCheck1 : pack2CoarseUpperRow 1 = 141 := by decide +kernel

private theorem pack2CoarseUpperCheck2 : pack2CoarseUpperRow 2 = 276 := by decide +kernel

private theorem pack2CoarseUpperCheck3 : pack2CoarseUpperRow 3 = 450 := by decide +kernel

private theorem pack2CoarseUpperCheck4 : pack2CoarseUpperRow 4 = 660 := by decide +kernel

private theorem pack2CoarseUpperCheck5 : pack2CoarseUpperRow 5 = 903 := by decide +kernel

private theorem pack2CoarseUpperCheck6 : pack2CoarseUpperRow 6 = 1176 := by decide +kernel

private theorem pack2CoarseUpperCheck7 : pack2CoarseUpperRow 7 = 1476 := by decide +kernel

private theorem pack2CoarseUpperCheck8 : pack2CoarseUpperRow 8 = 1800 := by decide +kernel

private theorem pack2CoarseUpperCheck9 : pack2CoarseUpperRow 9 = 2145 := by decide +kernel

private theorem pack2CoarseUpperCheck10 : pack2CoarseUpperRow 10 = 2508 := by decide +kernel

private theorem pack2CoarseUpperCheck11 : pack2CoarseUpperRow 11 = 2849 := by decide +kernel

private theorem pack2CoarseUpperCheck12 : pack2CoarseUpperRow 12 = 3132 := by decide +kernel

private theorem pack2CoarseUpperCheck13 : pack2CoarseUpperRow 13 = 3360 := by decide +kernel

private theorem pack2CoarseUpperCheck14 : pack2CoarseUpperRow 14 = 3536 := by decide +kernel

private theorem pack2CoarseUpperCheck15 : pack2CoarseUpperRow 15 = 3663 := by decide +kernel

private theorem pack2CoarseUpperCheck16 : pack2CoarseUpperRow 16 = 3744 := by decide +kernel

private theorem pack2CoarseUpperCheck17 : pack2CoarseUpperRow 17 = 3782 := by decide +kernel

private theorem pack2CoarseUpperCheck18 : pack2CoarseUpperRow 18 = 3780 := by decide +kernel

private theorem pack2CoarseUpperCheck19 : pack2CoarseUpperRow 19 = 3741 := by decide +kernel

private theorem pack2CoarseUpperCheck20 : pack2CoarseUpperRow 20 = 3668 := by decide +kernel

private theorem pack2CoarseUpperCheck21 : pack2CoarseUpperRow 21 = 3564 := by decide +kernel

private theorem pack2CoarseUpperCheck22 : pack2CoarseUpperRow 22 = 3432 := by decide +kernel

private theorem pack2CoarseUpperCheck23 : pack2CoarseUpperRow 23 = 3300 := by decide +kernel

private theorem pack2CoarseUpperCheck24 : pack2CoarseUpperRow 24 = 3168 := by decide +kernel

private theorem pack2CoarseUpperCheck25 : pack2CoarseUpperRow 25 = 3036 := by decide +kernel

private theorem pack2CoarseUpperCheck26 : pack2CoarseUpperRow 26 = 2904 := by decide +kernel

private theorem pack2CoarseUpperCheck27 : pack2CoarseUpperRow 27 = 2772 := by decide +kernel

private theorem pack2CoarseUpperCheck28 : pack2CoarseUpperRow 28 = 2641 := by decide +kernel

private theorem pack2CoarseUpperCheck29 : pack2CoarseUpperRow 29 = 2511 := by decide +kernel

private theorem pack2CoarseUpperCheck30 : pack2CoarseUpperRow 30 = 2383 := by decide +kernel

private theorem pack2CoarseUpperCheck31 : pack2CoarseUpperRow 31 = 2257 := by decide +kernel

private theorem pack2CoarseUpperCheck32 : pack2CoarseUpperRow 32 = 2134 := by decide +kernel

private theorem pack2CoarseUpperCheck33 : pack2CoarseUpperRow 33 = 2013 := by decide +kernel

private theorem pack2CoarseUpperCheck34 : pack2CoarseUpperRow 34 = 1893 := by decide +kernel

private theorem pack2CoarseUpperCheck35 : pack2CoarseUpperRow 35 = 1777 := by decide +kernel

private theorem pack2CoarseUpperCheck36 : pack2CoarseUpperRow 36 = 1665 := by decide +kernel

private theorem pack2CoarseUpperCheck37 : pack2CoarseUpperRow 37 = 1555 := by decide +kernel

private theorem pack2CoarseUpperCheck38 : pack2CoarseUpperRow 38 = 1448 := by decide +kernel

private theorem pack2CoarseUpperCheck39 : pack2CoarseUpperRow 39 = 1346 := by decide +kernel

private theorem pack2CoarseUpperCheck40 : pack2CoarseUpperRow 40 = 1246 := by decide +kernel

private theorem pack2CoarseUpperCheck41 : pack2CoarseUpperRow 41 = 1150 := by decide +kernel

private theorem pack2CoarseUpperCheck42 : pack2CoarseUpperRow 42 = 1060 := by decide +kernel

private theorem pack2CoarseUpperCheck43 : pack2CoarseUpperRow 43 = 970 := by decide +kernel

private theorem pack2CoarseUpperCheck44 : pack2CoarseUpperRow 44 = 887 := by decide +kernel

private theorem pack2CoarseUpperCheck45 : pack2CoarseUpperRow 45 = 806 := by decide +kernel

private theorem pack2CoarseUpperCheck46 : pack2CoarseUpperRow 46 = 730 := by decide +kernel

private theorem pack2CoarseUpperCheck47 : pack2CoarseUpperRow 47 = 658 := by decide +kernel

private theorem pack2CoarseUpperCheck48 : pack2CoarseUpperRow 48 = 590 := by decide +kernel

private theorem pack2CoarseUpperCheck49 : pack2CoarseUpperRow 49 = 526 := by decide +kernel

private theorem pack2CoarseUpperCheck50 : pack2CoarseUpperRow 50 = 466 := by decide +kernel

private theorem pack2CoarseUpperCheck51 : pack2CoarseUpperRow 51 = 410 := by decide +kernel

private theorem pack2CoarseUpperCheck52 : pack2CoarseUpperRow 52 = 359 := by decide +kernel

private theorem pack2CoarseUpperCheck53 : pack2CoarseUpperRow 53 = 310 := by decide +kernel

private theorem pack2CoarseUpperCheck54 : pack2CoarseUpperRow 54 = 268 := by decide +kernel

private theorem pack2CoarseUpperCheck55 : pack2CoarseUpperRow 55 = 226 := by decide +kernel

private theorem pack2CoarseUpperCheck56 : pack2CoarseUpperRow 56 = 190 := by decide +kernel

private theorem pack2CoarseUpperCheck57 : pack2CoarseUpperRow 57 = 158 := by decide +kernel

private theorem pack2CoarseUpperCheck58 : pack2CoarseUpperRow 58 = 128 := by decide +kernel

private theorem pack2CoarseUpperCheck59 : pack2CoarseUpperRow 59 = 103 := by decide +kernel

private theorem pack2CoarseUpperCheck60 : pack2CoarseUpperRow 60 = 81 := by decide +kernel

private theorem pack2CoarseUpperCheck61 : pack2CoarseUpperRow 61 = 61 := by decide +kernel

private theorem pack2CoarseUpperCheck62 : pack2CoarseUpperRow 62 = 45 := by decide +kernel

private theorem pack2CoarseUpperCheck63 : pack2CoarseUpperRow 63 = 33 := by decide +kernel

private theorem pack2CoarseUpperCheck64 : pack2CoarseUpperRow 64 = 22 := by decide +kernel

private theorem pack2CoarseUpperRows (s : Fin 65) : pack2CoarseUpperRow s = pack2CoarseUpperTable s := by
  fin_cases s
  · exact pack2CoarseUpperCheck0
  · exact pack2CoarseUpperCheck1
  · exact pack2CoarseUpperCheck2
  · exact pack2CoarseUpperCheck3
  · exact pack2CoarseUpperCheck4
  · exact pack2CoarseUpperCheck5
  · exact pack2CoarseUpperCheck6
  · exact pack2CoarseUpperCheck7
  · exact pack2CoarseUpperCheck8
  · exact pack2CoarseUpperCheck9
  · exact pack2CoarseUpperCheck10
  · exact pack2CoarseUpperCheck11
  · exact pack2CoarseUpperCheck12
  · exact pack2CoarseUpperCheck13
  · exact pack2CoarseUpperCheck14
  · exact pack2CoarseUpperCheck15
  · exact pack2CoarseUpperCheck16
  · exact pack2CoarseUpperCheck17
  · exact pack2CoarseUpperCheck18
  · exact pack2CoarseUpperCheck19
  · exact pack2CoarseUpperCheck20
  · exact pack2CoarseUpperCheck21
  · exact pack2CoarseUpperCheck22
  · exact pack2CoarseUpperCheck23
  · exact pack2CoarseUpperCheck24
  · exact pack2CoarseUpperCheck25
  · exact pack2CoarseUpperCheck26
  · exact pack2CoarseUpperCheck27
  · exact pack2CoarseUpperCheck28
  · exact pack2CoarseUpperCheck29
  · exact pack2CoarseUpperCheck30
  · exact pack2CoarseUpperCheck31
  · exact pack2CoarseUpperCheck32
  · exact pack2CoarseUpperCheck33
  · exact pack2CoarseUpperCheck34
  · exact pack2CoarseUpperCheck35
  · exact pack2CoarseUpperCheck36
  · exact pack2CoarseUpperCheck37
  · exact pack2CoarseUpperCheck38
  · exact pack2CoarseUpperCheck39
  · exact pack2CoarseUpperCheck40
  · exact pack2CoarseUpperCheck41
  · exact pack2CoarseUpperCheck42
  · exact pack2CoarseUpperCheck43
  · exact pack2CoarseUpperCheck44
  · exact pack2CoarseUpperCheck45
  · exact pack2CoarseUpperCheck46
  · exact pack2CoarseUpperCheck47
  · exact pack2CoarseUpperCheck48
  · exact pack2CoarseUpperCheck49
  · exact pack2CoarseUpperCheck50
  · exact pack2CoarseUpperCheck51
  · exact pack2CoarseUpperCheck52
  · exact pack2CoarseUpperCheck53
  · exact pack2CoarseUpperCheck54
  · exact pack2CoarseUpperCheck55
  · exact pack2CoarseUpperCheck56
  · exact pack2CoarseUpperCheck57
  · exact pack2CoarseUpperCheck58
  · exact pack2CoarseUpperCheck59
  · exact pack2CoarseUpperCheck60
  · exact pack2CoarseUpperCheck61
  · exact pack2CoarseUpperCheck62
  · exact pack2CoarseUpperCheck63
  · exact pack2CoarseUpperCheck64

theorem coarse_upper : coarseUpper = 104120 := by
  change (∑ s : Fin 65, pack2CoarseUpperRow s) = 104120
  simp_rw [pack2CoarseUpperRows]
  decide +kernel
theorem coarse_upper_eq_exact : coarseUpper = blockUpper := by rw [coarse_upper, block_upper]

end Sol1.C42
end PackSource_C42CoarseBlockArithmetic

section PackSource_C42SourceClosure
set_option autoImplicit true
/-! Exact source-family coverage/downward closure and the elementary
bounded-derivative-weight interval lemmas behind the closed row formula.
No actual coefficient-map rank bound is asserted here. -/
namespace Sol1.C42

open ReedSolomon.HiddenDerivative

def Eligible (x a b c : ℕ) : Prop :=
  a + b + c ≤ 64 ∧ b + 2 * c ≤ 21 - (a + b + c) / 62 ∧
    x + 131072 * a + 131071 * b + 131070 * c < 48 * 180246

theorem columns_eligible (i : SourceIndex) :
    Eligible (columns i).x (columns i).y₀ ((columns i).higher 0) ((columns i).higher 1) := by
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  have ho := jet_order i.1
  have hw := source_weight_lt i
  simp only [Eligible, columns, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- Every monomial in the stated finite weighted support has an index in the
actual Sigma-Fin source family; no monomials are lost by the indexing scheme. -/
theorem index_of_eligible (x a b c : ℕ) (h : Eligible x a b c) :
    ∃ i : SourceIndex, columns i = { x := x, y₀ := a, higher := ![b,c] } := by
  obtain ⟨htotal, horder, hweight⟩ := h
  let s : Fin 65 := ⟨a + b + c, by omega⟩
  let f2 : Fin (min s.val 10 + 1) := ⟨c, by dsimp [s]; omega⟩
  let f1 : Fin (min (s.val - f2.val) (21 - s.val / 62 - 2 * f2.val) + 1) :=
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

theorem eligible_lower_X {x a b c x' : ℕ} (h : Eligible x a b c) (hx : x' ≤ x) :
    Eligible x' a b c := by unfold Eligible at *; omega

theorem eligible_lower_Y0 {x a b c a' : ℕ} (h : Eligible x a b c) (ha : a' ≤ a) :
    Eligible x a' b c := by unfold Eligible at *; omega

/-- The complete interval supplied by [0,c]+2[0,d] when c>=1. -/
theorem bounded_jet_weight_iff (c d w : ℕ) (hc : 1 ≤ c) :
    (∃ a b : ℕ, a ≤ c ∧ b ≤ d ∧ a + 2 * b = w) ↔ w ≤ c + 2 * d := by
  constructor
  · rintro ⟨a,b,ha,hb,heq⟩
    omega
  · intro hw
    by_cases hsmall : w ≤ 2 * d
    · refine ⟨w % 2, w / 2, ?_, ?_, ?_⟩ <;> omega
    · refine ⟨w - 2 * d, d, ?_, le_rfl, ?_⟩ <;> omega

theorem bounded_even_weight_iff (d w : ℕ) :
    (∃ b : ℕ, b ≤ d ∧ 2 * b = w) ↔ w % 2 = 0 ∧ w ≤ 2 * d := by
  constructor
  · rintro ⟨b,hb,heq⟩
    omega
  · rintro ⟨heven,hw⟩
    exact ⟨w / 2, by omega, by omega⟩

/-- Nonempty intersection with the reachable derivative-weight interval. -/
theorem derivative_interval_iff (c d lo hi : ℕ) (hc : 1 ≤ c) :
    (∃ a b : ℕ, a ≤ c ∧ b ≤ d ∧ lo ≤ a + 2 * b ∧ a + 2 * b ≤ hi) ↔
      lo ≤ hi ∧ lo ≤ c + 2 * d := by
  constructor
  · rintro ⟨a,b,ha,hb,hl,hh⟩
    omega
  · rintro ⟨hlh,hl⟩
    obtain ⟨a,b,ha,hb,heq⟩ := (bounded_jet_weight_iff c d lo hc).mpr hl
    exact ⟨a,b,ha,hb,by omega,by omega⟩

/-- The c=0 parity exception uses the first even integer above lo. -/
theorem even_interval_iff (d lo hi : ℕ) :
    (∃ b : ℕ, b ≤ d ∧ lo ≤ 2 * b ∧ 2 * b ≤ hi) ↔
      2 * ((lo + 1) / 2) ≤ min hi (2 * d) := by
  constructor
  · rintro ⟨b,hb,hlo,hhi⟩
    omega
  · intro h
    exact ⟨(lo + 1) / 2, by omega, by omega, by omega⟩

def ReachableDerivativeChoice (c f : ℕ) (g : ℤ) : Prop :=
  ∃ a d : ℕ, a ≤ c ∧ d ≤ f ∧ 0 ≤ g + a + 2 * d ∧
    g + a + 2 * d < 48 ∧ a + 2 * d ≤ 21

/-- When c>=1, the original bounded source derivative exponents exist
exactly under the interval criterion used by the row-count formula. -/
theorem reachable_derivative_choice_iff (c f : ℕ) (g : ℤ) (hc : 1 ≤ c) :
    ReachableDerivativeChoice c f g ↔
      max 0 (-g) ≤ min 21 (47 - g) ∧ max 0 (-g) ≤ (c : ℤ) + 2 * f := by
  constructor
  · rintro ⟨a,d,ha,hd,hzero,hsmall,hord⟩
    omega
  · rintro ⟨hinterval,hbound⟩
    let lo : ℤ := max 0 (-g)
    let hi : ℤ := min 21 (47 - g)
    have hlo : 0 ≤ lo := by dsimp [lo]; omega
    have hhi : 0 ≤ hi := by dsimp [lo,hi] at *; omega
    have hnat : lo.toNat ≤ hi.toNat ∧ lo.toNat ≤ c + 2 * f := by
      dsimp [lo,hi] at *
      omega
    obtain ⟨a,d,ha,hd,hl,hu⟩ := (derivative_interval_iff c f lo.toNat hi.toNat hc).mpr hnat
    refine ⟨a,d,ha,hd,?_,?_,?_⟩ <;> dsimp [lo,hi] at * <;> omega

/-- The c=0 boundary is exactly the even-weight exception. -/
theorem reachable_even_choice_iff (f : ℕ) (g : ℤ) :
    ReachableDerivativeChoice 0 f g ↔
      max 0 (-g) ≤ min 21 (47 - g) ∧
        2 * ((max 0 (-g) + 1) / 2) ≤ min (min 21 (47 - g)) (2 * (f : ℤ)) := by
  constructor
  · rintro ⟨a,d,ha,hd,hzero,hsmall,hord⟩
    omega
  · rintro ⟨hinterval,hbound⟩
    let lo : ℤ := max 0 (-g)
    let hi : ℤ := min 21 (47 - g)
    have hlo : 0 ≤ lo := by dsimp [lo]; omega
    have hhi : 0 ≤ hi := by dsimp [lo,hi] at *; omega
    have hnat : 2 * ((lo.toNat + 1) / 2) ≤ min hi.toNat (2 * f) := by
      dsimp [lo,hi] at *
      omega
    obtain ⟨d,hd,hl,hu⟩ := (even_interval_iff f lo.toNat hi.toNat).mpr hnat
    refine ⟨0,d,by omega,hd,?_,?_,?_⟩ <;> dsimp [lo,hi] at * <;> omega


end Sol1.C42
end PackSource_C42SourceClosure

section PackSource_C42FiniteBlockCounts
set_option autoImplicit true
/-! Semantic finite-fiber counts behind the closed c(s,g), r(s,g) arithmetic.
The remaining coefficient-map/rank transport is not asserted by this module. -/
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

/-- c(s,g) counts the exact legal e1/e2 choices with x=g+e1+2e2 in[0,47]. -/
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

def rowBlockFiberCount (s : ℕ) (g : ℤ) : ℕ :=
  let L : ℤ := 48 - g - s
  let lo : ℤ := max 0 (-g)
  let hi : ℤ := min 21 (47 - g)
  if 0 < L ∧ lo ≤ hi then
    ∑ b ∈ Finset.range (min s ((L - 1) / 2).toNat + 1),
      ((Finset.univ.filter fun f : Fin (s - b) ↦
        lo ≤ (s : ℤ) - b + f.val ∧ 2 * (b : ℤ) + f.val < L).card +
        if 2 * (b : ℤ) + ((s : ℤ) - b) < L ∧
          2 * ((lo + 1) / 2) ≤ min hi (2 * ((s : ℤ) - b)) then 1 else 0)
  else 0

/-- The r formula counts the legal c>=1 finite fibers plus its one c=0
parity case. SourceClosure proves the underlying derivative-weight interval facts. -/
theorem rowBlockFiberCount_eq (s : ℕ) (g : ℤ) : rowBlockFiberCount s g = rowCount s g := by
  classical
  unfold rowBlockFiberCount rowCount
  dsimp only
  split_ifs with h
  · apply Finset.sum_congr rfl
    intro b hb
    have hbS : b ≤ s := by have := Finset.mem_range.mp hb; omega
    congr 1
    have hfilter :
        (Finset.univ.filter fun f : Fin (s - b) ↦
          max 0 (-g) ≤ (s : ℤ) - b + f.val ∧ 2 * (b : ℤ) + f.val < 48 - g - s) =
        (Finset.univ.filter fun f : Fin (s - b) ↦
          max 0 (-g) - s + b ≤ (f.val : ℤ) ∧
          (f.val : ℤ) ≤ (48 - g - s) - 1 - 2 * b) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hfilter, fin_interval_card]
    have heq : ((s - b : ℕ) : ℤ) - 1 = (s : ℤ) - b - 1 := by omega
    rw [heq]
  · rfl


end Sol1.C42
end PackSource_C42FiniteBlockCounts

section PackSource_C52EnvelopeArithmetic
set_option autoImplicit true
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

theorem grade_table (s : Fin 65) : gradeUpper s.val = ([48, 141, 276, 450, 660, 903, 1176, 1476, 1800, 2145, 2508, 2849, 3132, 3360, 3536, 3663, 3744, 3782, 3780, 3741, 3668, 3564, 3432, 3300, 3168, 3036, 2904, 2772, 2641, 2511, 2383, 2257, 2134, 2013, 1893, 1777, 1665, 1555, 1448, 1346, 1246, 1150, 1060, 970, 887, 806, 730, 658, 590, 526, 466, 410, 359, 310, 268, 226, 190, 158, 128, 103, 81, 61, 45, 33, 22] : List ℕ).getD s.val 0 := by
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
end PackSource_C52EnvelopeArithmetic
