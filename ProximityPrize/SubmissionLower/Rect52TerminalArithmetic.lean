import ProximityPrize.SubmissionLower.Rect52TerminalCapacity
import ProximityPrize.SubmissionLower.High52TerminalArithmetic

set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 18000
namespace Rect52Terminal
open Finset
open K1_14 (Shape shapeSum)
open High52 (agreement)
open High52TerminalArithmetic
  (width width_cast widthOrigin colEnd edgeShift innerQuad outerQuad twice_width_interval width_sum)
open P1_7_6 (Quad yStart linearEnd lt_linearEnd intervalProduct intervalProduct_eq)
open scoped BigOperators
open private rise_of_convex sum_range_guard diagonal yStart_eq sum_clipped lt_seedEnd
  from ProximityPrize.SubmissionLower.UpperBranch6
open private High52TerminalArithmetic.weighted_convex High52TerminalArithmetic.innerQuad_eq
  High52TerminalArithmetic.outerQuad_eq from ProximityPrize.SubmissionLower.High52TerminalArithmetic

abbrev bank : High52.Bank := ⟨⟨6220,8648,1834,341710⟩,7102499896688640,150928392143200⟩

def cap (e : ℕ) : ℕ :=
  ([414,410,406,402,396,392,386,382,376,370,365,360,353,346,334,322,290,243,191,136,77,14] : List ℕ)[e-1]?.getD 0

def short (e : ℕ) : ℕ := if e ≤ 13 then 51256 else if e ≤ 16 then 68342 else 170855

def long (e : ℕ) : ℕ := bank.shape.U - short e

def rectangleDebit (h : ℕ) (u v : ℕ) : ℕ :=
  (u+1)*(v+1)*bank.nodeRows + h*(u+v+2)*bank.poleMoment

def rectangleSurplus (h E u v x y : ℕ) : ℤ :=
  (jointGain h bank.shape E (slots u v x y) : ℤ) - rectangleDebit h u v

private theorem gain_convex (s : Shape) (h E : ℕ) (c : ℕ → ℕ) (hh : h+2 ≤ 131071) :
    let f := fun h => (jointGain h s E c : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  simp only [jointGain, shapeSum, Nat.cast_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro j _
  let g := (q-j)/E
  let raw := fun k a => s.m*agreement+j-q*(131071-k)-2*k*(j+a)
  let A := fun k => (↑(∑ a ∈ range g, (c a - c (a+1))*raw k a : ℕ) : ℤ)
  let B := fun k => (↑(c g*raw k g : ℕ) : ℤ)
  simp only [Nat.cast_add]
  change A (h+1) + B (h+1) + (A (h+1) + B (h+1)) ≤ A h + B h + (A (h+2) + B (h+2))
  rw [add_add_add_comm (A (h+1)), add_add_add_comm (A h)]
  apply add_le_add
  · simp only [A, Nat.cast_sum]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro a _
    exact High52TerminalArithmetic.weighted_convex s h q j (j+a) (c a - c (a+1)) hh
  · exact High52TerminalArithmetic.weighted_convex s h q j (j+(q-j)/E) (c ((q-j)/E)) hh

theorem rectangle_strict_of_first_difference {h E u v x y : ℕ}
    (hl : 2391 ≤ h) (hh : h < 131071)
    (hp : 0 < rectangleSurplus 2391 E u v x y)
    (hr : rectangleSurplus 2391 E u v x y ≤ rectangleSurplus 2392 E u v x y) :
    rectangleDebit h u v < jointGain h bank.shape E (slots u v x y) := by
  have conv (n : ℕ) (hn : n+2 ≤ 131071) :
      rectangleSurplus (n+1) E u v x y + rectangleSurplus (n+1) E u v x y ≤
        rectangleSurplus n E u v x y + rectangleSurplus (n+2) E u v x y := by
    have hg := gain_convex bank.shape n E (slots u v x y) hn
    have hd : (rectangleDebit (n+1) u v : ℤ) + rectangleDebit (n+1) u v =
        (rectangleDebit n u v : ℤ) + rectangleDebit (n+2) u v := by
      simp only [rectangleDebit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    dsimp only at hg
    change (jointGain (n+1) bank.shape E (slots u v x y) : ℤ) +
        jointGain (n+1) bank.shape E (slots u v x y) ≤
        jointGain n bank.shape E (slots u v x y) +
        jointGain (n+2) bank.shape E (slots u v x y) at hg
    unfold rectangleSurplus
    omega
  have hmono := rise_of_convex (f := fun n => rectangleSurplus n E u v x y)
    (fun n hn => conv n (by omega)) hl hr
  have hs := hp.trans_le hmono.1
  unfold rectangleSurplus at hs
  omega

def seedLimit (m d : ℕ) : ℕ := if d=0 then 8648 else m/d

def orderEnd (s : Shape) (E u v x y : ℕ) : ℕ :=
  min (s.B/E) (min (seedLimit u x) (seedLimit v y)) + 1

private theorem slots_zero_out {s : Shape} (hB : s.B ≤ 8648) {E u v x y a d g : ℕ}
    (ha : orderEnd s E u v x y ≤ a) (hg : a+d ≤ g) (hcap : g ≤ s.B/E) :
    slots u v x y (a+d) = 0 := by
  by_cases h₁ : (a+d)*x ≤ u <;> by_cases h₂ : (a+d)*y ≤ v
  · have hx : a+d ≤ seedLimit u x := by
      unfold seedLimit
      split
      · exact hg.trans (hcap.trans ((Nat.div_le_self _ _).trans hB))
      · exact (Nat.le_div_iff_mul_le (by omega)).2 h₁
    have hy : a+d ≤ seedLimit v y := by
      unfold seedLimit
      split
      · exact hg.trans (hcap.trans ((Nat.div_le_self _ _).trans hB))
      · exact (Nat.le_div_iff_mul_le (by omega)).2 h₂
    have hm := le_min (hg.trans hcap) (le_min hx hy)
    unfold orderEnd at ha
    omega
  · unfold slots
    rw [Nat.sub_eq_zero_of_le (by omega : v+1 ≤ (a+d)*y), Nat.mul_zero]
  · unfold slots
    rw [Nat.sub_eq_zero_of_le (by omega : u+1 ≤ (a+d)*x), Nat.zero_mul]
  · unfold slots
    rw [Nat.sub_eq_zero_of_le (by omega : u+1 ≤ (a+d)*x), Nat.zero_mul]

def phase (s : Shape) (h E u v x y d : ℕ) : ℤ :=
  ∑ t ∈ range (s.J + orderEnd s E u v x y), ∑ a ∈ Ico (t-s.J) (min t (orderEnd s E u v x y-1)+1),
    (slots u v x y (a+d) : ℤ) *
      ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)
private theorem position_phases (s : Shape) (h E u v x y q j : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (hB : s.B ≤ 8648) (hq : q ≤ s.B) (hj : j ≤ q) :
    let c := fun a => slots u v x y a
    let w0 := s.m*agreement+j-q*(131071-h)
    let g := (q-j)/E
    let f := fun d a => (c (a+d) : ℤ)*max 0 (width s h q j (j+a))
    (↑((∑ a ∈ range g, (c a - c (a+1))*(w0-2*h*(j+a))) + c g*(w0-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (orderEnd s E u v x y), if j+E*(a+0) ≤ q then f 0 a else 0) -
      (∑ a ∈ range (orderEnd s E u v x y), if j+E*(a+1) ≤ q then f 1 a else 0) := by
  dsimp only
  let g := (q-j)/E
  let f := fun d a => (slots u v x y (a+d) : ℤ)*max 0 (width s h q j (j+a))
  have step (a : ℕ) : slots u v x y (a+1) ≤ slots u v x y a :=
    slots_antitone u v x y (by omega)
  have hdiff :
      (↑((∑ a ∈ range g, (slots u v x y a - slots u v x y (a+1)) *
          (s.m*agreement+j-q*(131071-h)-2*h*(j+a))) +
        slots u v x y g*(s.m*agreement+j-q*(131071-h)-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (g+1), f 0 a) - ∑ a ∈ range g, f 1 a := by
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sum]
    rw [show (∑ a ∈ range g, f 0 a) + f 0 g - (∑ a ∈ range g, f 1 a) =
        ((∑ a ∈ range g, f 0 a) - (∑ a ∈ range g, f 1 a)) + f 0 g by ring,
      ← sum_sub_distrib]
    simp only [Nat.cast_mul, width_cast s h _ _ _ hh, f, Nat.add_zero]
    have hs (a : ℕ) :
        (↑(slots u v x y a - slots u v x y (a+1) : ℕ) : ℤ) =
          (slots u v x y a : ℤ) - slots u v x y (a+1) := Int.ofNat_sub (step a)
    simp only [hs, sub_mul]
  rw [hdiff]
  have hz (d a : ℕ) (ha : orderEnd s E u v x y ≤ a) (hg : a+d ≤ g) : f d a = 0 := by
    have hcap : g ≤ s.B/E := Nat.div_le_div_right (by omega)
    have hz := slots_zero_out hB ha hg hcap
    simp [f, hz]
  have hdiv (a d : ℕ) : j+E*(a+d) ≤ q ↔ a+d ≤ g := by
    rw [Nat.le_div_iff_mul_le he, Nat.mul_comm (a+d) E]
    omega
  rw [sum_range_guard (g+1) _ (fun a ha hb => hz 0 a ha (by omega)),
    sum_range_guard g _ (fun a ha hb => hz 1 a ha (by omega))]
  have hzero (a : ℕ) : j+E*a ≤ q ↔ a ≤ g := by simpa using hdiv a 0
  simp only [hzero, Nat.add_zero, Nat.lt_succ_iff, Nat.add_one_le_iff, f]
private def phaseQ (s : Shape) (h E u v x y d : ℕ) : ℤ :=
  ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E u v x y),
    if j + E*(a+d) ≤ q then
      (slots u v x y (a+d) : ℤ) * max 0 (width s h q j (j+a)) else 0
private theorem phaseQ_expand (s : Shape) (h E u v x y d q : ℕ) :
    (∑ j ∈ range (min q s.J+1), ∑ a ∈ range (orderEnd s E u v x y),
      if j+E*(a+d) ≤ q then (slots u v x y (a+d) : ℤ)*max 0 (width s h q j (j+a)) else 0) =
    ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E u v x y),
      if j+E*(a+d) ≤ q then (slots u v x y (a+d) : ℤ)*max 0 (width s h q j (j+a)) else 0 := by
  apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
  intro j hj hnot
  simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
  apply sum_eq_zero
  intro a _
  rw [ite_eq_right (by omega)]
private theorem gain_eq_phaseQ (s : Shape) (h E u v x y : ℕ) (hh : h ≤ 131071) (he : 0 < E) (hB : s.B ≤ 8648) :
    (jointGain h s E (slots u v x y) : ℤ) = phaseQ s h E u v x y 0 - phaseQ s h E u v x y 1 := by
  unfold jointGain shapeSum phaseQ
  push_cast only [Nat.cast_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  rw [← phaseQ_expand s h E u v x y 0 q, ← phaseQ_expand s h E u v x y 1 q, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [mem_range, Nat.lt_succ_iff] at hq hj
  exact position_phases s h E u v x y q j hh he hB hq (hj.trans (min_le_left _ _))
private theorem phaseQ_eq (s : Shape) (h E u v x y d : ℕ) : phaseQ s h E u v x y d = phase s h E u v x y d := by
  have hR : orderEnd s E u v x y-1+1 = orderEnd s E u v x y := by
    apply Nat.sub_add_cancel
    exact Nat.succ_pos _
  unfold phaseQ phase
  rw [sum_comm]
  conv_lhs =>
    enter [2, j]
    rw [sum_comm]
  conv_lhs =>
    rw [← hR]
    rw [diagonal]
  rw [Nat.add_assoc, hR]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro a ha
  have hta : t-a+a = t := Nat.sub_add_cancel (by have := (mem_Ico.mp ha).2; omega)
  rw [mul_sum, ← sum_filter]
  have hf : (range (s.B+1)).filter (fun q => t-a+E*(a+d) ≤ q) =
      Ico (t-a+E*(a+d)) (s.B+1) := by
    ext q
    simp only [mem_range, mem_filter, mem_Ico]
    tauto
  rw [hf, hta]
theorem gain_eq_phases (s : Shape) (h E u v x y : ℕ) (hh : h ≤ 131071) (he : 0 < E) (hB : s.B ≤ 8648) :
    (jointGain h s E (slots u v x y) : ℤ) = phase s h E u v x y 0 - phase s h E u v x y 1 := by
  rw [gain_eq_phaseQ s h E u v x y hh he hB, phaseQ_eq, phaseQ_eq]

private def sideEnd (u v x y d R : ℕ) : ℕ :=
  min (P1_7_6.seedEnd ⟨0,0,0,u⟩ x d R) (P1_7_6.seedEnd ⟨0,0,0,v⟩ y d R)

private theorem lt_sideEnd (u v x y d R a : ℕ) :
    a < sideEnd u v x y d R ↔ a < R ∧ ((a+d)*x ≤ u ∧ (a+d)*y ≤ v) := by
  simp only [sideEnd, lt_min_iff, lt_seedEnd]
  aesop

private def innerEnd (s : Shape) (h E u v x y d t R : ℕ) : ℕ :=
  linearEnd (yStart E d t) (E-1) (colEnd s h t) (sideEnd u v x y d R)

private def outerEnd (s : Shape) (h E u v x y d t R : ℕ) : ℕ :=
  min (t+1-edgeShift s h t)
    (linearEnd (yStart E d t) (E-1) (colEnd s h t+1) (sideEnd u v x y d R))

private def seedQuad (u v x y d : ℕ) : Quad :=
  Quad.ofLines ((u : ℤ)+1-(x : ℤ)*d) (-(x : ℤ)) ((v : ℤ)+1-(y : ℤ)*d) (-(y : ℤ))

def phaseBlock (s : Shape) (h E u v x y d t : ℕ) : ℤ :=
  let L := t-s.J
  let R := min t (orderEnd s E u v x y-1)+1
  let c := seedQuad u v x y d
  intervalProduct c (innerQuad s h E d t) L (innerEnd s h E u v x y d t R) +
    if colEnd s h t < s.B+1 then
      intervalProduct c (outerQuad s h t) L (outerEnd s h E u v x y d t R)
    else 0

private theorem seedQuad_eq (u v x y d a : ℕ) (ha : (a+d)*x ≤ u ∧ (a+d)*y ≤ v) :
    (seedQuad u v x y d).eval a = (slots u v x y (a+d) : ℤ) := by
  have hx : (a+d)*x ≤ u+1 := ha.1.trans (Nat.le_succ _)
  have hy : (a+d)*y ≤ v+1 := ha.2.trans (Nat.le_succ _)
  simp only [seedQuad, Quad.eval_ofLines, slots, Nat.cast_mul, Nat.cast_sub hx, Nat.cast_sub hy,
    Nat.cast_add, Nat.cast_one]
  ring

private theorem slots_zero_of_not {u v x y a d : ℕ}
    (h : ¬ ((a+d)*x ≤ u ∧ (a+d)*y ≤ v)) : slots u v x y (a+d) = 0 := by
  unfold slots
  by_cases hx : (a+d)*x ≤ u
  · have hy : v+1 ≤ (a+d)*y := by omega
    rw [Nat.sub_eq_zero_of_le hy, Nat.mul_zero]
  · rw [Nat.sub_eq_zero_of_le (by omega : u+1≤(a+d)*x), Nat.zero_mul]

theorem phaseBlock_eq (s : Shape) (h E u v x y d t : ℕ)
    (hh : h ≤ 131071) (hj : s.J ≤ 131071-h) (he : 0 < E) :
    120*(∑ a ∈ Ico (t-s.J) (min t (orderEnd s E u v x y-1)+1),
      (slots u v x y (a+d) : ℤ) *
        ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)) =
      phaseBlock s h E u v x y d t := by
  let L := t-s.J
  let R := min t (orderEnd s E u v x y-1)+1
  let k := colEnd s h t
  let l := fun a => t-a+E*(a+d)
  let c := fun a => (slots u v x y (a+d) : ℤ)
  let inner := fun a => ∑ q ∈ Ico (l a) k, width s h q (t-a) t
  let outer := fun a =>
    if k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a then width s h k (t-a) t else 0
  let R₁ := innerEnd s h E u v x y d t R
  let R₂ := outerEnd s h E u v x y d t R
  have ht (a : ℕ) (ha : a < R) : a ≤ t :=
    (Nat.le_of_lt_succ ha).trans (min_le_left _ _)
  have hcore (a : ℕ) : a < R₁ ↔ a < R ∧ ((a+d)*x ≤ u ∧ (a+d)*y ≤ v) ∧ l a < k := by
    simp only [R₁, innerEnd, lt_linearEnd, lt_sideEnd]
    constructor
    · rintro ⟨⟨ha,hv⟩,hk⟩
      exact ⟨ha,hv,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
    · rintro ⟨ha,hv,hk⟩
      exact ⟨⟨ha,hv⟩,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
  have hedge (a : ℕ) :
      a < R₂ ↔ a < R ∧ ((a+d)*x ≤ u ∧ (a+d)*y ≤ v) ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a := by
    simp only [R₂, outerEnd, lt_min_iff, lt_linearEnd, lt_sideEnd]
    constructor
    · rintro ⟨hs,⟨ha,hv⟩,hk⟩
      refine ⟨ha,hv,?_,by omega⟩
      simpa only [l,yStart_eq E d t a he (ht a ha), Nat.lt_succ_iff] using hk
    · rintro ⟨ha,hv,hk,hs⟩
      refine ⟨by have := ht a ha; omega,⟨ha,hv⟩,?_⟩
      simpa only [l,yStart_eq E d t a he (ht a ha), Nat.lt_succ_iff] using hk
  have hw (a : ℕ) (ha : a ∈ Ico L R) :
      (∑ q ∈ Ico (l a) (s.B+1), max 0 (width s h q (t-a) t)) = inner a + outer a := by
    obtain ⟨ha₀,_⟩ := mem_Ico.mp ha
    exact width_sum s h t (t-a) (l a) hh ((by dsimp [L] at ha₀; omega : t-a ≤ s.J).trans hj)
  have hsplit :
      (∑ a ∈ Ico L R, c a * ∑ q ∈ Ico (l a) (s.B+1), max 0 (width s h q (t-a) t)) =
        (∑ a ∈ Ico L R, c a * inner a) + (∑ a ∈ Ico L R, c a * outer a) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun a ha => by rw [hw a ha, mul_add])
  have normalize (x y : ℤ) : 2*(x*y) = x*(2*y) := by ring
  have hi :
      2*(∑ a ∈ Ico L R, c a * inner a) =
        ∑ a ∈ Ico L R₁, (seedQuad u v x y d).eval a * (innerQuad s h E d t).eval a := by
    rw [mul_sum]
    apply sum_clipped (fun a ha => ((hcore a).mp ha).1)
    · intro a ha hn
      have haR := (mem_Ico.mp ha).2
      by_cases hv : ((a+d)*x ≤ u ∧ (a+d)*y ≤ v)
      · have hl : k ≤ l a := by
          by_contra! hl
          exact (Nat.not_lt_of_ge hn) ((hcore a).mpr ⟨haR,hv,hl⟩)
        simp [inner, Ico_eq_empty_of_le hl]
      · simp [c, slots_zero_of_not hv]
    · intro a ha
      obtain ⟨haR,hv,hl⟩ := (hcore a).mp (mem_Ico.mp ha).2
      rw [normalize, seedQuad_eq u v x y d a hv, ← High52TerminalArithmetic.innerQuad_eq s h E d t a hh he (ht a haR) hl.le]
  have ho :
      120*(∑ a ∈ Ico L R, c a * outer a) =
        if k < s.B+1 then intervalProduct (seedQuad u v x y d) (outerQuad s h t) L R₂ else 0 := by
    by_cases hk : k < s.B+1
    · rw [ite_eq_left hk, ← intervalProduct_eq, show (120 : ℤ) = 60*2 by decide, mul_assoc, mul_sum]
      congr 1
      apply sum_clipped (fun a ha => ((hedge a).mp ha).1)
      · intro a ha hn
        have haR := (mem_Ico.mp ha).2
        by_cases hv : ((a+d)*x ≤ u ∧ (a+d)*y ≤ v)
        · have hbound : ¬(k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a) :=
            fun ⟨_,hl,hs⟩ => (Nat.not_lt_of_ge hn) ((hedge a).mpr ⟨haR,hv,hl,hs⟩)
          simp only [outer, ite_eq_right hbound, mul_zero]
        · simp [c, slots_zero_of_not hv]
      · intro a ha
        obtain ⟨haR,hv,hl,hs⟩ := (hedge a).mp (mem_Ico.mp ha).2
        rw [normalize, seedQuad_eq u v x y d a hv, ← High52TerminalArithmetic.outerQuad_eq s h t a hh (ht a haR)]
        simp only [outer, hk, hl, hs, and_self, ite_true]
        rfl
    · simp [outer, hk]
  change _ = intervalProduct _ _ L R₁ + if k < s.B+1 then intervalProduct _ _ L R₂ else 0
  rw [hsplit, mul_add, ho, ← intervalProduct_eq (seedQuad u v x y d) (innerQuad s h E d t), ← hi]
  ring

def blockTerm (s : Shape) (h E u v x y t : ℕ) : ℤ :=
  phaseBlock s h E u v x y 0 t - phaseBlock s h E u v x y 1 t

theorem block_sum (s : Shape) (h E u v x y : ℕ)
    (hh : h ≤ 131071) (hj : s.J ≤ 131071-h) (he : 0 < E) (hB : s.B ≤ 8648) :
    (∑ t ∈ range (s.J+orderEnd s E u v x y), blockTerm s h E u v x y t) =
      120 * (jointGain h s E (slots u v x y) : ℤ) := by
  rw [gain_eq_phases s h E u v x y hh he hB, mul_sub, phase, phase, mul_sum, mul_sum,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  rw [phaseBlock_eq s h E u v x y 0 t hh hj he, phaseBlock_eq s h E u v x y 1 t hh hj he]
  rfl

end Rect52Terminal
