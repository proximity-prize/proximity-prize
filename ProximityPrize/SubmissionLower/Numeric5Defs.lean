import ProximityPrize.SubmissionLower.FiltrationLift
import ProximityPrize.SubmissionLower.Numeric6Defs
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_8
open CJ6 (VectorDots belowSucc belowZero block_rank_le rank_of_dots)
open CJ6.Fast
set_option maxRecDepth 4096
private def zeros (lo n : ℕ) : List Lane :=
  (List.range' lo n).map fun a => ⟨a,0,0,0,0⟩
local notation "v!" side "," q "," b "," l =>
  CJ6.Fast.vector b (buckets side q l) rfl rfl rfl (id (α := good side q l b) rfl)
private def cap (q u r : ℕ) : Prop :=
  (CJ0.blockMatrix CJ6.source q ((u : ℤ)-20)).rank ≤ r
private theorem checked (q u : ℕ) (z : CJ1.Block) (hg : CJ6.Guard q u z)
    (hd : CJ6.Dots q u z) : cap q u z.cap :=
  (block_rank_le q u).trans (rank_of_dots hg hd)
private def l1v0 : List Lane := zeros 42 10 ++ [⟨52,1,1,1,1⟩]
private def l1v1 : List Lane := zeros 42 9 ++ [⟨51,2,1,1,1⟩,⟨52,0,0,0,0⟩]
def l1v2 : List Lane := zeros 42 8 ++ [⟨50,4,1,1,1⟩,⟨51,3,1,31,0x7f000000⟩,⟨52,0,0,0,0⟩]
def l1v3 : List Lane := zeros 42 7 ++ [⟨49,6,1,1,1⟩,⟨50,5,1,31,0x7f000000⟩,⟨51,3,1,31,0x7f000000⟩,⟨52,0,0,0,0⟩]
private def z1 : CJ1.Block :=
  ⟨.rightHigh, 16, [(1,0),(2,0),(4,0),(6,0)], [l1v0,l1v1,l1v2,l1v3].map (vectorData false 62 1)⟩
private def b1 := bands [(0,54,9),(1,55,7),(2,56,5),(3,57,3),(4,58,1)]
private theorem v1j0 : VectorDots 62 1 z1 0 := v! false, 62, b1, l1v0
private theorem v1j1 : VectorDots 62 1 z1 1 := v! false, 62, b1, l1v1
theorem v1j2 : VectorDots 62 1 z1 2 := v! false, 62, b1, l1v2
theorem v1j3 : VectorDots 62 1 z1 3 := v! false, 62, b1, l1v3
private theorem r1 : cap 62 1 16 :=
  checked 62 1 z1 (by decide) (belowSucc (belowSucc (belowSucc (belowSucc belowZero v1j0) v1j1) v1j2) v1j3)
private def l2v0 : List Lane := [⟨3,4,1,1,1⟩,⟨2,2,2,31,0x3f7fffeb7effffaf⟩,⟨1,1,2,12,3878385⟩,⟨0,0,2,31,0x3f7fe449fefec999⟩]
private def l2v1 : List Lane := [⟨3,3,1,1,1⟩,⟨2,2,1,31,0x7effffd7⟩,⟨1,1,1,10,903⟩,⟨0,0,1,31,0x7effcc45⟩]
private def z2 : CJ1.Block :=
  ⟨.leftHigh, 18, [(3,0),(3,1)], [l2v0,l2v1].map (vectorData true 62 2)⟩
private def b2 := bands [(53,62,1),(52,60,2),(51,58,3),(50,56,3),(49,54,3),(48,52,3),(47,50,3),(46,48,3),(45,46,3),(44,44,3),(43,43,2),(42,42,1)]
private theorem v2j0 : VectorDots 62 2 z2 0 := v! true, 62, b2, l2v0
private theorem v2j1 : VectorDots 62 2 z2 1 := v! true, 62, b2, l2v1
private theorem r2 : cap 62 2 18 :=
  checked 62 2 z2 (by decide) (belowSucc (belowSucc belowZero v2j0) v2j1)
private def l3v0 : List Lane := zeros 43 9 ++ [⟨52,2,1,1,1⟩]
private def z3 : CJ1.Block :=
  ⟨.rightHigh, 9, [(2,0)], [l3v0].map (vectorData false 63 0)⟩
private def b3 := bands [(0,55,9),(1,56,7),(2,57,5),(3,58,3),(4,59,1)]
private theorem v3j0 : VectorDots 63 0 z3 0 := v! false, 63, b3, l3v0
private theorem r3 : cap 63 0 9 :=
  checked 63 0 z3 (by decide) (belowSucc belowZero v3j0)
def l4v0 : List Lane := zeros 43 10 ++ [⟨53,1,1,1,1⟩]
def l4v1 : List Lane := zeros 43 9 ++ [⟨52,2,1,1,1⟩,⟨53,0,0,0,0⟩]
def l4v2 : List Lane := zeros 43 9 ++ [⟨52,3,1,1,1⟩,⟨53,0,0,0,0⟩]
def l4v3 : List Lane := zeros 43 8 ++ [⟨51,4,1,1,1⟩,⟨52,0,0,0,0⟩,⟨53,0,0,0,0⟩]
def l4v4 : List Lane := zeros 43 7 ++ [⟨50,6,1,1,1⟩,⟨51,5,1,31,0x7f000000⟩,⟨52,0,0,0,0⟩,⟨53,0,0,0,0⟩]
def l4v5 : List Lane := zeros 43 6 ++ [⟨49,8,1,1,1⟩,⟨50,7,1,31,0x7f000000⟩,⟨51,5,1,31,0x7f000000⟩,⟨52,0,0,0,0⟩,⟨53,0,0,0,0⟩]
def z4 : CJ1.Block :=
  ⟨.rightHigh, 14, [(1,0),(2,0),(3,0),(4,0),(6,0),(8,0)], [l4v0,l4v1,l4v2,l4v3,l4v4,l4v5].map (vectorData false 63 1)⟩
def b4 := bands [(0,56,8),(1,57,6),(2,58,4),(3,59,2)]
theorem v4j0 : VectorDots 63 1 z4 0 := v! false, 63, b4, l4v0
theorem v4j1 : VectorDots 63 1 z4 1 := v! false, 63, b4, l4v1
theorem v4j2 : VectorDots 63 1 z4 2 := v! false, 63, b4, l4v2
theorem v4j3 : VectorDots 63 1 z4 3 := v! false, 63, b4, l4v3
theorem v4j4 : VectorDots 63 1 z4 4 := v! false, 63, b4, l4v4
theorem v4j5 : VectorDots 63 1 z4 5 := v! false, 63, b4, l4v5
private theorem r4 : cap 63 1 14 :=
  checked 63 1 z4 (by decide) (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc belowZero v4j0) v4j1) v4j2) v4j3) v4j4) v4j5)
def l5v0 : List Lane := [⟨3,3,1,1,1⟩,⟨2,2,1,31,0x7effffd6⟩,⟨1,1,1,10,946⟩,⟨0,0,1,31,0x7effc893⟩]
def z5 : CJ1.Block :=
  ⟨.leftHigh, 15, [(3,0)], [l5v0].map (vectorData true 63 2)⟩
def b5 := bands [(54,63,1),(53,61,2),(52,59,3),(51,57,3),(50,55,3),(49,53,3),(48,51,3),(47,49,3),(46,47,3),(45,45,3),(44,44,2),(43,43,1)]
theorem v5j0 : VectorDots 63 2 z5 0 := v! true, 63, b5, l5v0
private theorem r5 : cap 63 2 15 :=
  checked 63 2 z5 (by decide) (belowSucc belowZero v5j0)
def l6v0 : List Lane := zeros 44 9 ++ [⟨53,2,1,1,1⟩]
def l6v1 : List Lane := zeros 44 8 ++ [⟨52,4,1,1,1⟩,⟨53,0,0,0,0⟩]
def z6 : CJ1.Block :=
  ⟨.rightHigh, 8, [(2,0),(4,0)], [l6v0,l6v1].map (vectorData false 64 0)⟩
def b6 := bands [(0,57,8),(1,58,6),(2,59,4),(3,60,2)]
theorem v6j0 : VectorDots 64 0 z6 0 := v! false, 64, b6, l6v0
theorem v6j1 : VectorDots 64 0 z6 1 := v! false, 64, b6, l6v1
private theorem r6 : cap 64 0 8 :=
  checked 64 0 z6 (by decide) (belowSucc (belowSucc belowZero v6j0) v6j1)
def l7v0 : List Lane := [⟨3,0,0,0,0⟩,⟨2,4,1,1,1⟩,⟨1,1,3,31,0x1fbffff4ff7fffd47effff55⟩,⟨0,0,3,14,0x43940b2e68⟩]
def l7v1 : List Lane := [⟨3,0,0,0,0⟩,⟨2,3,1,1,1⟩,⟨1,1,2,31,0x3f7fffea7effffaa⟩,⟨0,0,2,12,4243320⟩]
def l7v2 : List Lane := [⟨3,0,0,0,0⟩,⟨2,2,1,1,1⟩,⟨1,1,1,31,0x7effffd5⟩,⟨0,0,1,10,990⟩]
def l7v3 : List Lane := [⟨3,3,1,1,1⟩,⟨2,0,0,0,0⟩,⟨1,1,1,31,0x7efffc4f⟩,⟨0,0,1,15,28380⟩]
def z7 : CJ1.Block :=
  ⟨.leftHigh, 12, [(2,0),(2,1),(2,2),(3,0)], [l7v0,l7v1,l7v2,l7v3].map (vectorData true 64 1)⟩
def b7 := bands [(54,63,1),(53,61,2),(52,59,2),(51,57,2),(50,55,2),(49,53,2),(48,51,2),(47,49,2),(46,47,2),(45,45,2),(44,44,1)]
theorem v7j0 : VectorDots 64 1 z7 0 := v! true, 64, b7, l7v0
theorem v7j1 : VectorDots 64 1 z7 1 := v! true, 64, b7, l7v1
theorem v7j2 : VectorDots 64 1 z7 2 := v! true, 64, b7, l7v2
theorem v7j3 : VectorDots 64 1 z7 3 := v! true, 64, b7, l7v3
private theorem r7 : cap 64 1 12 :=
  checked 64 1 z7 (by decide) (belowSucc (belowSucc (belowSucc (belowSucc belowZero v7j0) v7j1) v7j2) v7j3)
def l8v0 : List Lane := zeros 45 9 ++ [⟨54,2,1,1,1⟩]
def l8v1 : List Lane := zeros 45 8 ++ [⟨53,4,1,1,1⟩,⟨54,0,0,0,0⟩]
def l8v2 : List Lane := zeros 45 7 ++ [⟨52,6,1,1,1⟩,⟨53,0,0,0,0⟩,⟨54,0,0,0,0⟩]
def z8 : CJ1.Block :=
  ⟨.rightHigh, 7, [(2,0),(4,0),(6,0)], [l8v0,l8v1,l8v2].map (vectorData false 65 0)⟩
def b8 := bands [(0,59,7),(1,60,5),(2,61,3),(3,62,1)]
theorem v8j0 : VectorDots 65 0 z8 0 := v! false, 65, b8, l8v0
theorem v8j1 : VectorDots 65 0 z8 1 := v! false, 65, b8, l8v1
theorem v8j2 : VectorDots 65 0 z8 2 := v! false, 65, b8, l8v2
private theorem r8 : cap 65 0 7 :=
  checked 65 0 z8 (by decide) (belowSucc (belowSucc (belowSucc belowZero v8j0) v8j1) v8j2)
def l9v0 : List Lane := [⟨2,3,1,1,1⟩,⟨1,1,2,31,0x3f7fffe9feffffa8⟩,⟨0,0,2,13,8859692⟩]
def l9v1 : List Lane := [⟨2,2,1,1,1⟩,⟨1,1,1,31,0x7effffd4⟩,⟨0,0,1,11,1035⟩]
def z9 : CJ1.Block :=
  ⟨.leftHigh, 10, [(2,0),(2,1)], [l9v0,l9v1].map (vectorData true 65 1)⟩
def b9 := bands [(55,64,1),(54,62,2),(53,60,2),(52,58,2),(51,56,2),(50,54,2),(49,52,2),(48,50,2),(47,48,2),(46,46,2),(45,45,1)]
theorem v9j0 : VectorDots 65 1 z9 0 := v! true, 65, b9, l9v0
theorem v9j1 : VectorDots 65 1 z9 1 := v! true, 65, b9, l9v1
private theorem r9 : cap 65 1 10 :=
  checked 65 1 z9 (by decide) (belowSucc (belowSucc belowZero v9j0) v9j1)
def l10v0 : List Lane := zeros 46 9 ++ [⟨55,2,1,1,1⟩]
def l10v1 : List Lane := zeros 46 8 ++ [⟨54,4,1,1,1⟩,⟨55,0,0,0,0⟩]
def l10v2 : List Lane := zeros 46 7 ++ [⟨53,6,1,1,1⟩,⟨54,0,0,0,0⟩,⟨55,0,0,0,0⟩]
def l10v3 : List Lane := zeros 46 6 ++ [⟨52,8,1,1,1⟩] ++ zeros 53 3
def z10 : CJ1.Block :=
  ⟨.rightHigh, 6, [(2,0),(4,0),(6,0),(8,0)], [l10v0,l10v1,l10v2,l10v3].map (vectorData false 66 0)⟩
def b10 := bands [(0,61,6),(1,62,4),(2,63,2)]
theorem v10j0 : VectorDots 66 0 z10 0 := v! false, 66, b10, l10v0
theorem v10j1 : VectorDots 66 0 z10 1 := v! false, 66, b10, l10v1
theorem v10j2 : VectorDots 66 0 z10 2 := v! false, 66, b10, l10v2
theorem v10j3 : VectorDots 66 0 z10 3 := v! false, 66, b10, l10v3
private theorem r10 : cap 66 0 6 :=
  checked 66 0 z10 (by decide) (belowSucc (belowSucc (belowSucc (belowSucc belowZero v10j0) v10j1) v10j2) v10j3)
def l11v0 : List Lane := [⟨2,2,1,1,1⟩,⟨1,1,1,31,0x7effffd3⟩,⟨0,0,1,11,1081⟩]
def z11 : CJ1.Block :=
  ⟨.leftHigh, 8, [(2,0)], [l11v0].map (vectorData true 66 1)⟩
def b11 := bands [(56,65,1),(55,63,2),(54,61,2),(53,59,2),(52,57,2),(51,55,2),(50,53,2),(49,51,2),(48,49,2),(47,47,2),(46,46,1)]
theorem v11j0 : VectorDots 66 1 z11 0 := v! true, 66, b11, l11v0
private theorem r11 : cap 66 1 8 :=
  checked 66 1 z11 (by decide) (belowSucc belowZero v11j0)
def l12v0 : List Lane := [⟨2,0,0,0,0⟩,⟨1,3,1,1,1⟩,⟨0,0,3,31,0x1fbffff43f7fffd0feffff45⟩]
def l12v1 : List Lane := [⟨2,0,0,0,0⟩,⟨1,2,1,1,1⟩,⟨0,0,2,31,0x3f7fffe8feffffa3⟩]
def l12v2 : List Lane := [⟨2,0,0,0,0⟩,⟨1,1,1,1,1⟩,⟨0,0,1,31,0x7effffd2⟩]
def l12v3 : List Lane := [⟨2,2,1,1,1⟩,⟨1,0,0,0,0⟩,⟨0,0,1,31,0x7efffbc8⟩]
def z12 : CJ1.Block :=
  ⟨.leftHigh, 5, [(1,0),(1,1),(1,2),(2,0)], [l12v0,l12v1,l12v2,l12v3].map (vectorData true 67 0)⟩
def b12 := bands [(56,65,1),(55,63,1),(54,61,1),(53,59,1),(52,57,1),(51,55,1),(50,53,1),(49,51,1),(48,49,1),(47,47,1)]
theorem v12j0 : VectorDots 67 0 z12 0 := v! true, 67, b12, l12v0
theorem v12j1 : VectorDots 67 0 z12 1 := v! true, 67, b12, l12v1
theorem v12j2 : VectorDots 67 0 z12 2 := v! true, 67, b12, l12v2
theorem v12j3 : VectorDots 67 0 z12 3 := v! true, 67, b12, l12v3
private theorem r12 : cap 67 0 5 :=
  checked 67 0 z12 (by decide) (belowSucc (belowSucc (belowSucc (belowSucc belowZero v12j0) v12j1) v12j2) v12j3)
def l13v0 : List Lane := [⟨1,2,1,1,1⟩,⟨0,0,2,31,0x3f7fffe87effffa1⟩]
def l13v1 : List Lane := [⟨1,1,1,1,1⟩,⟨0,0,1,31,0x7effffd1⟩]
def z13 : CJ1.Block :=
  ⟨.leftHigh, 4, [(1,0),(1,1)], [l13v0,l13v1].map (vectorData true 68 0)⟩
def b13 := bands [(57,66,1),(56,64,1),(55,62,1),(54,60,1),(53,58,1),(52,56,1),(51,54,1),(50,52,1),(49,50,1),(48,48,1)]
theorem v13j0 : VectorDots 68 0 z13 0 := v! true, 68, b13, l13v0
theorem v13j1 : VectorDots 68 0 z13 1 := v! true, 68, b13, l13v1
private theorem r13 : cap 68 0 4 :=
  checked 68 0 z13 (by decide) (belowSucc (belowSucc belowZero v13j0) v13j1)
def l14v0 : List Lane := [⟨1,1,1,1,1⟩,⟨0,0,1,31,0x7effffd0⟩]
def z14 : CJ1.Block :=
  ⟨.leftHigh, 3, [(1,0)], [l14v0].map (vectorData true 69 0)⟩
def b14 := bands [(58,67,1),(57,65,1),(56,63,1),(55,61,1),(54,59,1),(53,57,1),(52,55,1),(51,53,1),(50,51,1),(49,49,1)]
theorem v14j0 : VectorDots 69 0 z14 0 := v! true, 69, b14, l14v0
private theorem r14 : cap 69 0 3 :=
  checked 69 0 z14 (by decide) (belowSucc belowZero v14j0)
theorem proof : CJ6.c8 := ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, trivial⟩
end CJ6_8
end
section
namespace K1_13_2_3_5
open K1_13_2 K1_13_2_3
def shifted (F : Flag) (p : Powers) : Flag :=
  ⟨F.degree - ((p.value : ℤ) + p.top + 3 * p.cubic),
    F.lower - (3 * (p.top : ℤ) + 2 * p.cubic),
    F.upper - (3 * (p.top : ℤ) + 3 * p.cubic),
    F.cap - ((p.top : ℤ) + p.cubic),
    F.order - (2 * (p.top : ℤ) + 3 * p.cubic)⟩
theorem shifted_eq (F : Flag) (p : Powers) :
    shifted F p = residualFlag F p.expand :=
  (residualFlag_expand F p).symm
def discounted (s j : ℕ) (p : Powers) : ℕ :=
  let F : Flag := ⟨1650, 1650 - j, 1650, 550, 4650 - s - j⟩
  let full := oldCount F
  let starting := kernelLower F
  (full - max 0 starting).toNat -
    (full - max 0 (max starting (kernelLower (shifted F p)))).toNat
theorem discounted_eq (i : BlockIndex) (p : Powers) (hi : w2.Contains i) :
    discounted i.1.val i.2.val p = savings i p := by
  have hb : 2008 ≤ i.1.val ∧ i.1.val < 3012 ∧
      322 ≤ i.2.val ∧ i.2.val ≤ 1062 ∧
      3000 ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ 3419 := hi
  have hf : initialFlag i = ⟨1650, 1650 - i.2.val, 1650, 550,
      4650 - i.1.val - i.2.val⟩ := by
    unfold initialFlag offset
    rw [min_eq_right (show (1650 : ℤ) ≤ i.1.val by omega)]
    congr 1 <;> omega
  have ho : ¬ (initialFlag i).order ≤ 0 := by rw [hf]; dsimp; omega
  have hu : min (initialFlag i).upper (2999 - offset i) = (initialFlag i).upper := by
    rw [min_eq_left]
    rw [hf, offset]
    dsimp
    omega
  have hr : residualFlag (initialFlag i) (fun _ => 0) = initialFlag i := by
    cases initialFlag i
    simp [residualFlag]
  unfold savings baseline blockBound
  simp only [ho, ite_false, hu, hr, max_self]
  unfold discounted
  rw [← hf]
  dsimp only
  rw [shifted_eq]
  rw [min_eq_right (sub_le_self _ (le_max_left _ _)),
    min_eq_right (sub_le_self _ (le_max_left _ _))]
def denFast (u : ℕ) : ℕ :=
  if u == 0 then 0 else
    let q := (u - 1) / 6
    let r := (u - 1) % 6
    (q * (q * (12*q+21+6*r) + 11+r*(7+r)) + 2+r*(r+1)) / 2
def cumFast (d u : ℕ) : ℕ :=
  if u ≤ d+1 then denFast u else
    let u := min u (3*d+1)
    (denFast u + denFast (u-(2*d+3)) + denFast (u-(2*d+4)) + denFast (u-(2*d+5))) -
      (denFast (u-(d+1)) + denFast (u-(d+2)) + denFast (u-(d+3)))
def cutFast (d u r : ℕ) : ℕ :=
  if d < r then 0 else cumFast (d-r) u
def kFast (d l u o r : ℕ) : ℕ :=
  (cumFast d u + cutFast d (o - 3*r) r) - (cumFast d o + cutFast d l r)
def originalK (s j : ℕ) : ℕ :=
  let o := 4650 - (s+j)
  let r := (4649-s)/4+1
  (125576826 + cutFast 1650 (o-3*r) r) -
    (denFast o + cutFast 1650 (1650-j) r)
def certifiedSaving (s j : ℕ) (p : Powers) : ℕ :=
  let a := p.value
  let b := p.top
  let c := p.cubic
  if 1650 < a+b+3*c || 550 < b+c || j+1 < c || 4649 < s+a+4*c then 0 else
  let d := 1650-(a+b+3*c)
  let l := 1650-(j+3*b+2*c)
  let u := 1651-3*(b+c)
  let o := 4650-(s+j+2*b+3*c)
  let r := min d ((4649-(s+a+4*c))/4)+1
  min 30000000 (kFast d l u o r) - originalK s j
private theorem twice_half (n : ℤ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  have h : (2 : ℤ) ∣ n * (n - 1) := by
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ n) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ n - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem denFast_correct (n : ℕ) :
    (denFast n : ℤ) = denominator ((n : ℤ) - 1) := by
  cases n with
  | zero => decide
  | succ n =>
    rw [denFast, ite_eq_right (by simp), Nat.succ_sub_one]
    push_cast
    rw [show (n : ℤ) + 1 - 1 = n by omega, denominator, ite_eq_right (by omega)]
    let q := (n : ℤ) / 6
    let r := (n : ℤ) % 6
    change (q * (q * (12*q+21+6*r) + 11+r*(7+r)) + 2+r*(r+1)) / 2 =
      1 + r*(r+1)/2 + q*(22+7*r+r*(r-1)/2) +
        (57+6*r)*(q*(q-1)/2) + 6*q*(q-1)*(q-2)
    have h := twice_half (r+1)
    rw [show (r+1)*(r+1-1) = r*(r+1) by ring] at h
    have heq : q * (q * (12*q+21+6*r) + 11+r*(7+r)) + 2+r*(r+1) =
        2 * (1 + r*(r+1)/2 + q*(22+7*r+r*(r-1)/2) +
          (57+6*r)*(q*(q-1)/2) + 6*q*(q-1)*(q-2)) := by
      linear_combination -h - q * twice_half r - (57+6*r) * twice_half q
    rw [heq]
    omega
theorem denFast_sub (n k : ℕ) :
    (denFast (n - k) : ℤ) = denominator ((n : ℤ) - 1 - k) := by
  rw [denFast_correct]
  by_cases h : k ≤ n
  · rw [Int.ofNat_sub h]
    congr 1
    omega
  · have hz : n - k = 0 := by omega
    simp [hz, denominator, show (n : ℤ) - 1 - k < 0 by omega]
private theorem cumulative_nonneg (d : ℕ) (u : ℤ) : 0 ≤ cumulative (d : ℤ) u := by
  by_cases h : u < 0
  · simp [cumulative, h]
  · have hm := cumulative_mono d (show (-1 : ℤ) ≤ u by omega)
    simpa [cumulative] using hm
theorem cumFast_correct (d u : ℕ) :
    (cumFast d u : ℤ) = cumulative (d : ℤ) ((u : ℤ) - 1) := by
  by_cases h0 : u = 0
  · subst u
    simp [cumFast, denFast, cumulative]
  let n := min u (3*d+1)
  have hv : min ((u : ℤ) - 1) (3 * d) = (n : ℤ) - 1 := by
    simp only [n, min_def]
    split <;> split <;> omega
  have hd0 : ¬ (d : ℤ) < 0 := by omega
  have hu0 : ¬ (u : ℤ) - 1 < 0 := by omega
  rw [cumFast]
  by_cases h : u ≤ d+1
  · rw [ite_eq_left h, denFast_correct]
    have hn : n = u := min_eq_left (by omega)
    have hz (z : ℤ) (hz : z < 0) : denominator z = 0 := by simp [denominator, hz]
    simp (disch := omega) only [cumulative, hd0, hu0, decide_false, Bool.false_or,
      Bool.false_eq_true, ite_false, hv, hn, hz, sub_zero, add_zero]
  · rw [ite_eq_right h]
    let pos := denFast n + denFast (n-(2*d+3)) + denFast (n-(2*d+4)) + denFast (n-(2*d+5))
    let neg := denFast (n-(d+1)) + denFast (n-(d+2)) + denFast (n-(d+3))
    change ((pos - neg : ℕ) : ℤ) = _
    have hn : n ≤ 3*d+1 := min_le_right _ _
    have hlast : denominator ((n : ℤ) - 1 - 3*d - 6) = 0 := by
      simp [denominator, show (n : ℤ) - 1 - 3*d - 6 < 0 by omega]
    have he : (pos : ℤ) - neg = cumulative d ((u : ℤ) - 1) := by
      simp only [pos, neg, Nat.cast_add, denFast_sub, Nat.cast_mul, Nat.cast_ofNat]
      rw [denFast_correct]
      simp only [cumulative, hd0, hu0, decide_false, Bool.false_or, Bool.false_eq_true,
        ite_false, hv, hlast, sub_zero]
      ring_nf
    have hpos : 0 ≤ (pos : ℤ) - neg := he ▸ cumulative_nonneg d _
    rwa [← Int.toNat_sub, Int.toNat_of_nonneg hpos]
private theorem cumFast_clipped (d : ℕ) (u : ℤ) :
    (cumFast d u.toNat : ℤ) = cumulative d (u - 1) := by
  rw [cumFast_correct]
  by_cases h : 0 ≤ u
  · rw [Int.toNat_of_nonneg h]
  · simp [Int.toNat_of_nonpos (by omega : u ≤ 0), cumulative, show u - 1 < 0 by omega]
theorem cutFast_correct (d r : ℕ) (u : ℤ) :
    (cutFast d u.toNat r : ℤ) = cumulative ((d : ℤ) - r) (u - 1) := by
  unfold cutFast
  by_cases h : d < r
  · simp [h, cumulative, show (d : ℤ) - r < 0 by omega]
  · rw [ite_eq_right h, cumFast_clipped, Int.ofNat_sub (by omega : r ≤ d)]
private def balance (F : Flag) : ℤ := F.order - 1 - F.lower + F.degree
theorem capped_eq (d u f : ℤ) (hf : 0 ≤ f) (hu : u ≤ 3*f) :
    cappedCount d u f = cumulative d u := by
  simp [cappedCount, not_lt.mpr hf, cumulative, show u - 3*(f+1) < 0 by omega]
theorem kernel_formula (F : Flag) (hd : 0 ≤ F.degree) (hu : 0 ≤ F.upper)
    (hc : 0 ≤ F.cap) (hcap : F.upper ≤ 3*F.cap) (hl : F.lower - 1 ≤ F.upper)
    (hb : 0 ≤ balance F) :
    let r := min F.degree (balance F / 4) + 1
    kernelLower F =
      cumulative F.degree F.upper + cumulative (F.degree - r) (F.order - 1 - 3*r) -
        (cumulative F.degree (F.order - 1) + cumulative (F.degree - r) (F.lower - 1)) := by
  unfold kernelLower oldCount targetCount
  simp only [not_lt.mpr hd, not_lt.mpr hu, not_lt.mpr hc, decide_false, Bool.false_or, Bool.false_eq_true, ite_false, min_eq_right hl]
  have hb' : ¬ F.order - 1 - F.lower + F.degree < 0 := not_lt.mpr hb
  simp only [hb', ite_false]
  rw [capped_eq _ _ _ hc hcap, capped_eq _ _ _ hc (hl.trans hcap)]
  simp only [balance]
  ring
private theorem kFast_correct (F : Flag) (d u r : ℕ) (hd : F.degree = d)
    (hu : F.upper = (u : ℤ) - 1) (hu0 : 0 ≤ F.upper) (hc : 0 ≤ F.cap)
    (hcap : F.upper ≤ 3*F.cap) (hl : F.lower - 1 ≤ F.upper) (hb : 0 ≤ balance F)
    (hr : (r : ℤ) = min F.degree (balance F / 4) + 1) :
    kFast d F.lower.toNat u F.order.toNat r = (kernelLower F).toNat := by
  rw [kernel_formula F (by omega) hu0 hc hcap hl hb, ← hr, hd, hu]
  unfold kFast
  rw [← Int.toNat_sub]
  push_cast
  rw [cumFast_correct, cumFast_clipped, cutFast_correct]
  have ht : F.order.toNat - 3*r = (F.order - 3*(r : ℤ)).toNat := by omega
  rw [ht, cutFast_correct]
  rw [show F.order - 3*(r : ℤ) - 1 = F.order - 1 - 3*r by ring]
def fullFlag (s j : ℕ) : Flag := ⟨1650, 1650 - j, 1650, 550, 4650 - s - j⟩
theorem originalK_correct (s j : ℕ) (_hs : 2008 ≤ s) (hsj : s+j ≤ 3419)
    (hdiag : 3000 ≤ s+j) (hj : j ≤ 1062) :
    originalK s j = (kernelLower (fullFlag s j)).toNat := by
  let r := (4649-s)/4+1
  have h := kFast_correct (fullFlag s j) 1650 1651 r rfl rfl (by change 0 ≤ (1650 : ℤ); decide)
    (by change 0 ≤ (550 : ℤ); decide) (by change (1650 : ℤ) ≤ 3*550; decide) (by simp [fullFlag]; omega) (by simp [balance, fullFlag]; omega) (by
      simp only [r, fullFlag, balance, Nat.cast_add, Nat.cast_one, Int.natCast_ediv, Nat.cast_ofNat,
        Int.ofNat_sub (show s ≤ 4649 by omega)]
      have hmin : min (1650 : ℤ) ((4649 - (s : ℤ)) / 4) = (4649 - (s : ℤ)) / 4 :=
        min_eq_right (by omega)
      rw [show (4650 : ℤ) - s - j - 1 - (1650 - j) + 1650 = 4649 - s by ring, hmin])
  rw [← h]
  have hl : (fullFlag s j).lower.toNat = 1650-j := by simp [fullFlag]
  have ho : (fullFlag s j).order.toNat = 4650-(s+j) := by simp [fullFlag]; omega
  have hd : cumFast 1650 (4650-(s+j)) = denFast (4650-(s+j)) := by
    rw [cumFast, ite_eq_left (by omega)]
  simp only [originalK, kFast, hl, ho, hd, r, show cumFast 1650 1651 = 125576826 by decide]
theorem full_enough (s j : ℕ) (hj : 322 ≤ j) :
    30000000 ≤ oldCount (fullFlag s j) := by
  simp only [oldCount, fullFlag, min_eq_right (show (1650 : ℤ) - j - 1 ≤ 1650 by omega)]
  rw [capped_eq _ _ _ (by decide) (by decide),
    capped_eq _ _ _ (by decide) (by omega)]
  have hm := cumulative_mono 1650 (show (1650 : ℤ) - j - 1 ≤ 1327 by omega)
  change cumulative (1650 : ℤ) (1650 - j - 1) ≤ cumulative (1650 : ℤ) 1327 at hm
  have hn : (30000000 : ℤ) ≤ cumulative 1650 1650 - cumulative 1650 1327 := by decide
  omega
theorem saving_arithmetic (full k k' : ℤ) (hf : 30000000 ≤ full) :
    min 30000000 k'.toNat - k.toNat ≤
      (full - max 0 k).toNat - (full - max 0 (max k k')).toNat := by
  let m := min 30000000 k'.toNat
  have hm₁ : (m : ℤ) ≤ 30000000 := by exact_mod_cast (min_le_left 30000000 k'.toNat)
  have hm₂ : (m : ℤ) ≤ (k'.toNat : ℤ) := by exact_mod_cast (min_le_right 30000000 k'.toNat)
  have hm₃ : (m : ℤ) ≤ max 0 (max k k') := by
    rw [Int.toNat_eq_max, max_comm k' 0] at hm₂
    exact hm₂.trans (max_le_max_left _ (le_max_right _ _))
  have h₁ : full - (k.toNat : ℤ) ≤ ((full - max 0 k).toNat : ℤ) := by
    rw [Int.toNat_eq_max k, max_comm k 0]
    exact Int.self_le_toNat _
  have h₂ : ((full - max 0 (max k k')).toNat : ℤ) ≤ full - (m : ℤ) := by
    rw [Int.toNat_eq_max]
    exact max_le (sub_le_sub_left hm₃ _) (by omega)
  change m - k.toNat ≤ _
  omega
theorem certifiedSaving_le (i : BlockIndex) (p : Powers) (hi : w2.Contains i) :
    certifiedSaving i.1.val i.2.val p ≤ savings i p := by
  have hdata := hi
  obtain ⟨hs, _, hj, hj', hdiag, hdiag'⟩ := hdata
  change 2008 ≤ i.1.val at hs
  change 322 ≤ i.2.val at hj
  change i.2.val ≤ 1062 at hj'
  change 3000 ≤ i.1.val + i.2.val at hdiag
  change i.1.val + i.2.val ≤ 3419 at hdiag'
  let s := i.1.val
  let j := i.2.val
  let a := p.value
  let b := p.top
  let c := p.cubic
  change 2008 ≤ s at hs
  change 322 ≤ j at hj
  change j ≤ 1062 at hj'
  change 3000 ≤ s+j at hdiag
  change s+j ≤ 3419 at hdiag'
  rw [← discounted_eq i p hi]
  change certifiedSaving s j p ≤ discounted s j p
  unfold certifiedSaving
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i hg
    change ¬ (1650 < a+b+3*c || 550 < b+c || j+1 < c || 4649 < s+a+4*c) = true at hg
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hg
    obtain ⟨⟨⟨hd, hc⟩, hl⟩, hb⟩ := hg
    let F := shifted (fullFlag s j) p
    let d := 1650-(a+b+3*c)
    let u := 1651-3*(b+c)
    let r := min d ((4649-(s+a+4*c))/4)+1
    have hd' : F.degree = d := by
      change (1650 : ℤ) - (a+b+3*c) = ((1650-(a+b+3*c) : ℕ) : ℤ)
      push_cast [Int.ofNat_sub hd]
      rfl
    have hu' : F.upper = (u : ℤ) - 1 := by
      change (1650 : ℤ) - (3*b+3*c) = ((1651-3*(b+c) : ℕ) : ℤ) - 1
      rw [Int.ofNat_sub (by omega : 3*(b+c) ≤ 1651)]
      push_cast
      ring
    have hb' : balance F = 4649 - ((s : ℤ)+a+4*c) := by
      simp only [balance, F, shifted, fullFlag, a, c]
      ring
    have hr' : (r : ℤ) = min F.degree (balance F / 4) + 1 := by
      rw [hd', hb']
      simp only [r, Nat.cast_add, Nat.cast_one, Nat.cast_min, Int.natCast_ediv, Nat.cast_ofNat,
        Int.ofNat_sub hb, Nat.cast_mul]
    have hk := kFast_correct F d u r hd' hu'
      (by change 0 ≤ (1650 : ℤ) - (3*b+3*c); omega)
      (by change 0 ≤ (550 : ℤ) - (b+c); omega)
      (by change (1650 : ℤ) - (3*b+3*c) ≤ 3*(550-(b+c)); omega)
      (by change (1650 : ℤ) - j - (3*b+2*c) - 1 ≤ 1650 - (3*b+3*c); omega)
      (by rw [hb']; omega) hr'
    have hL : F.lower.toNat = 1650-(j+3*b+2*c) := by
      change ((1650 : ℤ) - j - (3*b+2*c)).toNat = _
      omega
    have hO : F.order.toNat = 4650-(s+j+2*b+3*c) := by
      change ((4650 : ℤ) - s - j - (2*b+3*c)).toNat = _
      omega
    change min 30000000 (kFast d _ u _ r) - originalK s j ≤ _
    rw [originalK_correct _ _ hs hdiag' hdiag hj', ← hL, ← hO, hk]
    exact saving_arithmetic _ _ _ (full_enough s j hj)
end K1_13_2_3_5
end
