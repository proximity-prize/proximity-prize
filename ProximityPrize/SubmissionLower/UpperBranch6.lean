import ProximityPrize.SubmissionLower.UpperBranch7
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_6
open Finset
open K1_14 (Shape triangle)
open P1 (HighBand agreement)
open P1_7 (Bank Test debit jointGain tested threshold seedThreshold)
def orderEnd (s : Shape) (E v : ℕ) : ℕ :=
  if v = 0 then s.B/E+1 else min (s.B/E+1) (s.U/v+1)
def linearEnd (base step bound cap : ℕ) : ℕ :=
  if base < bound then
    if step = 0 then cap else min cap ((bound - 1 - base)/step + 1)
  else 0
structure Quad where
  constant : ℤ
  linear : ℤ
  square : ℤ
def Quad.eval (p : Quad) (a : ℤ) : ℤ :=
  p.constant + p.linear*a + p.square*a*a
def Quad.ofLines (x y z w : ℤ) : Quad :=
  ⟨x*z, x*w+y*z, y*w⟩
def prefixProduct (p q : Quad) (n : ℕ) : ℤ :=
  let x : ℤ := n
  let t := x*(x-1)
  let u := t*(2*x-1)
  60*x*(p.constant*q.constant) +
    30*t*(p.constant*q.linear+p.linear*q.constant) +
    10*u*(p.constant*q.square+p.linear*q.linear+p.square*q.constant) +
    15*t*t*(p.linear*q.square+p.square*q.linear) +
    2*u*(3*t-1)*(p.square*q.square)
def intervalProduct (p q : Quad) (L R : ℕ) : ℤ :=
  if L < R then prefixProduct p q R - prefixProduct p q L else 0
def seedEnd (s : Shape) (v d R : ℕ) : ℕ :=
  if v = 0 then R else min R (s.U/v+1-d)
def yStart (E d t : ℕ) := t+E*d
def seedQuad (s : Shape) (v d : ℕ) : Quad :=
  let u : ℤ := (s.U : ℤ) - (v : ℤ)*d
  Quad.ofLines (u+1) (-(v : ℤ)) (u+2) (-(v : ℤ))
def scaledDebit (s : Shape) (N P h : ℕ) : ℤ :=
  240*((triangle s.U : ℤ)*N + 2*(h : ℤ)*(s.U+1)*P)
end P1_7_6
end
section
namespace P1_7_6
open Finset
open K1_14 (Shape shapeSum slots)
open P1 (agreement)
open P1_7 (Bank debit jointGain)
private theorem rise_of_convex {f : ℕ → ℤ} {lo h : ℕ}
    (hc : ∀ n < h, f (n+1) + f (n+1) ≤ f n + f (n+2))
    (hl : lo ≤ h) (hf : f lo ≤ f (lo+1)) :
    f lo ≤ f h ∧ f h ≤ f (h+1) := by
  induction h with
  | zero =>
    have he : lo = 0 := by omega
    subst lo
    exact ⟨le_rfl, hf⟩
  | succ h ih =>
    rcases Nat.lt_or_eq_of_le hl with hlt | he
    · obtain ⟨hh, hs⟩ := ih (fun n hn => hc n (by omega)) (by omega)
      have ht := hc h (by omega)
      exact ⟨hh.trans hs, by rw [show h+1+1 = h+2 by omega]; omega⟩
    · subst lo
      exact ⟨le_rfl, hf⟩
end P1_7_6
end
section
namespace P1_7_6
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P1_7 (jointGain)
private theorem slots_anti (U : ℕ) : Antitone (slots U) := by
  intro a b hab
  unfold slots
  split_ifs with ha hb hb
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul (by omega) (by omega)
  all_goals omega
private theorem sum_range_guard {f : ℕ → ℤ} (L R : ℕ)
    (hz : ∀ a, R ≤ a → a < L → f a = 0) :
    ∑ a ∈ range L, f a = ∑ a ∈ range R, if a < L then f a else 0 := by
  have hf : (range R).filter (· < L) = range (min L R) := by
    ext a
    simp only [mem_range, mem_filter, lt_min_iff]
    tauto
  rw [← sum_filter, hf]
  symm
  apply sum_subset (range_mono (min_le_left _ _))
  intro a ha hnot
  simp only [mem_range, lt_min_iff] at ha hnot
  exact hz a (by omega) ha
private theorem diagonal (J R : ℕ) (f : ℕ → ℕ → ℤ) :
    (∑ j ∈ range (J+1), ∑ a ∈ range (R+1), f j a) =
      ∑ t ∈ range (J+R+1), ∑ a ∈ Ico (t-J) (min t R+1), f (t-a) a := by
  calc
    _ = ∑ a ∈ range (R+1), ∑ j ∈ range (J+1), f j a := sum_comm
    _ = ∑ a ∈ range (R+1), ∑ t ∈ Ico a (a+(J+1)), f (t-a) a := by
      apply sum_congr rfl
      intro a _
      rw [sum_Ico_eq_sum_range]
      simp
    _ = ∑ a ∈ range (R+1), ∑ t ∈ range (J+R+1),
        if a ≤ t ∧ t-a ≤ J then f (t-a) a else 0 := by
      apply sum_congr rfl
      intro a ha
      have ha' := mem_range.mp ha
      rw [← sum_filter]
      congr 1
      ext t
      simp only [mem_Ico, mem_filter, mem_range]
      omega
    _ = ∑ t ∈ range (J+R+1), ∑ a ∈ range (R+1),
        if a ≤ t ∧ t-a ≤ J then f (t-a) a else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [← sum_filter]
      congr 1
      ext a
      simp only [mem_Ico, mem_filter, mem_range, Nat.lt_succ_iff, le_min_iff]
      omega
end P1_7_6
end
section
namespace P1_7_6
open Finset
open P1 (agreement)
open K1_14 (Shape)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
theorem lt_linearEnd (base step bound cap i : ℕ) :
    i < linearEnd base step bound cap ↔ i < cap ∧ base + step*i < bound := by
  unfold linearEnd
  by_cases hb : base < bound
  · rw [ite_eq_left hb]
    by_cases hs : step = 0
    · simp [hs, hb]
    · rw [ite_eq_right hs, lt_min_iff, Nat.lt_succ_iff,
        Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hs), Nat.mul_comm i step]
      omega
  · rw [ite_eq_right hb]
    omega
end P1_7_6
end
section
namespace P1_7_6
open Finset
theorem Quad.eval_ofLines (x y z w a : ℤ) :
    (Quad.ofLines x y z w).eval a = (x+y*a)*(z+w*a) := by
  unfold Quad.ofLines Quad.eval
  dsimp only
  ring
private theorem prefix_eq (p q : Quad) (n : ℕ) :
    60 * (∑ a ∈ range n, p.eval a * q.eval a) = prefixProduct p q n := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [prefixProduct, Quad.eval, Nat.cast_succ]
    ring
theorem intervalProduct_eq (p q : Quad) (L R : ℕ) :
    60 * (∑ a ∈ Ico L R, p.eval a * q.eval a) = intervalProduct p q L R := by
  unfold intervalProduct
  by_cases h : L < R
  · rw [ite_eq_left h, sum_Ico_eq_sub _ h.le, mul_sub, prefix_eq, prefix_eq]
  · rw [ite_eq_right h, Ico_eq_empty_of_le (Nat.le_of_not_gt h), sum_empty, mul_zero]
end P1_7_6
end
section
namespace P1_7_6_4
open Finset
open P1_7_6 (Quad)
structure Line where
  base : ℤ
  slope : ℤ
def Line.at (l : Line) (a : ℤ) : ℤ := l.base+l.slope*a
def Line.sub (l r : Line) : Line := ⟨l.base-r.base,l.slope-r.slope⟩
def Line.addConst (l : Line) (c : ℤ) : Line := ⟨l.base+c,l.slope⟩
def Line.scale (l : Line) (c : ℤ) : Line := ⟨c*l.base,c*l.slope⟩
def Line.shift (l r : Line) (c : ℤ) : Line := ⟨l.base+c*r.base,l.slope+c*r.slope⟩
structure Cubic where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
def Cubic.at (p : Cubic) (a : ℤ) : ℤ := p.c0+p.c1*a+p.c2*a^2+p.c3*a^3
def Cubic.lines (x y z : Line) : Cubic :=
  let q := Quad.ofLines x.base x.slope y.base y.slope
  ⟨q.constant*z.base, q.constant*z.slope+q.linear*z.base,
    q.linear*z.slope+q.square*z.base, q.square*z.slope⟩
theorem Cubic.lines_at (x y z : Line) (a : ℤ) :
    (Cubic.lines x y z).at a = x.at a * y.at a * z.at a := by
  simp only [Cubic.lines, Cubic.at, Quad.ofLines, Line.at]
  ring
def windowCubic (L R xLine yLine : Line) (b d : ℤ) : Cubic :=
  let n := R.sub L
  let x := xLine.shift L b
  let y := yLine.shift L d
  let m := n.addConst (-1)
  let w := (n.scale 2).addConst (-1)
  let f := Cubic.lines n x y
  let g := Cubic.lines n m (x.scale d |>.shift y b)
  let k := Cubic.lines n m w
  ⟨6*f.c0+3*g.c0+b*d*k.c0, 6*f.c1+3*g.c1+b*d*k.c1,
    6*f.c2+3*g.c2+b*d*k.c2, 6*f.c3+3*g.c3+b*d*k.c3⟩
private theorem windowCubic_at (L R xLine yLine : Line) (b d a : ℤ) :
    (windowCubic L R xLine yLine b d).at a =
      let n := R.at a-L.at a
      let x := xLine.at a+b*L.at a
      let y := yLine.at a+d*L.at a
      6*n*x*y+3*n*(n-1)*(d*x+b*y)+b*d*n*(n-1)*(2*n-1) := by
  simp only [windowCubic, Cubic.at]
  let f := Cubic.lines (R.sub L) (xLine.shift L b) (yLine.shift L d)
  let g := Cubic.lines (R.sub L) ((R.sub L).addConst (-1))
    (((xLine.shift L b).scale d).shift (yLine.shift L d) b)
  let k := Cubic.lines (R.sub L) ((R.sub L).addConst (-1)) (((R.sub L).scale 2).addConst (-1))
  change (6*f.c0+3*g.c0+b*d*k.c0) + (6*f.c1+3*g.c1+b*d*k.c1)*a +
    (6*f.c2+3*g.c2+b*d*k.c2)*a^2 + (6*f.c3+3*g.c3+b*d*k.c3)*a^3 = _
  trans 6*f.at a+3*g.at a+b*d*k.at a
  · unfold Cubic.at
    ring
  simp only [f, g, k, Cubic.lines_at, Line.at, Line.sub, Line.shift, Line.addConst, Line.scale]
  ring
private theorem linePair_range (x y b d : ℤ) (n : ℕ) :
    6*(∑ t ∈ range n, (x+b*t)*(y+d*t)) =
      6*(n : ℤ)*x*y+3*n*(n-1)*(d*x+b*y)+b*d*n*(n-1)*(2*n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
    ring
theorem windowCubic_eq (L R xLine yLine : Line) (b d a : ℤ) (l r : ℕ)
    (hl : L.at a = l) (hr : R.at a = r) (hle : l ≤ r) :
    (windowCubic L R xLine yLine b d).at a =
      6*(∑ t ∈ Ico l r, (xLine.at a+b*t)*(yLine.at a+d*t)) := by
  rw [windowCubic_at, hl, hr, sum_Ico_eq_sum_range]
  have hs : (∑ t ∈ range (r-l), (xLine.at a+b*(↑(l+t) : ℤ))*(yLine.at a+d*(↑(l+t) : ℤ))) =
      ∑ t ∈ range (r-l), ((xLine.at a+b*l)+b*t)*((yLine.at a+d*l)+d*t) := by
    apply sum_congr rfl
    intro t _
    push_cast
    ring
  rw [hs, linePair_range, Nat.cast_sub hle]
def prefixCubic (p : Quad) (q : Cubic) (n : ℕ) : ℤ :=
  let x : ℤ := n
  let t := x*(x-1)
  let u := t*(2*x-1)
  60*x*(p.constant*q.c0) +
    30*t*(p.constant*q.c1+p.linear*q.c0) +
    10*u*(p.constant*q.c2+p.linear*q.c1+p.square*q.c0) +
    15*t*t*(p.constant*q.c3+p.linear*q.c2+p.square*q.c1) +
    2*u*(3*t-1)*(p.linear*q.c3+p.square*q.c2) +
    5*t*t*(2*t-1)*(p.square*q.c3)
theorem prefix_eq (p : Quad) (q : Cubic) (n : ℕ) :
    prefixCubic p q n = 60*(∑ a ∈ range n, p.eval a * q.at a) := by
  induction n with
  | zero => simp [prefixCubic]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← ih]
    simp only [prefixCubic, Quad.eval, Cubic.at, Nat.cast_succ]
    ring
end P1_7_6_4
end
section
namespace P1_7_6_4
open Finset
open K1_14 (Shape)
open P1 (agreement)
open P1_7_6
structure Core where
  column : ℕ
  offset : ℕ
  step : ℕ
  cap : ℕ
  seed : Quad
  countLine : Line
  widthLine : Line
  widthSlope : ℤ
def Core.term (C : Core) (a t : ℕ) : ℤ :=
  (C.countLine.at a-t)*(C.widthLine.at a+C.widthSlope*t)
def Core.slice (C : Core) (x c a : ℕ) : Finset ℕ :=
  Ico (a+c) (min x (C.column-(C.offset+C.step*a)))
def Core.nonemptyEnd (C : Core) (x c : ℕ) : ℕ :=
  linearEnd (c+C.offset) (C.step+1) C.column (min C.cap (x-c))
def Core.switchEnd (C : Core) (x c : ℕ) : ℕ :=
  linearEnd (x+C.offset) C.step (C.column+1) (C.nonemptyEnd x c)
private theorem lt_nonemptyEnd (C : Core) (x c a : ℕ) :
    a < C.nonemptyEnd x c ↔ a < C.cap ∧ a+c < min x (C.column-(C.offset+C.step*a)) := by
  rw [Core.nonemptyEnd, lt_linearEnd, lt_min_iff, lt_min_iff, Nat.add_mul, Nat.one_mul]
  omega
private theorem lt_switchEnd (C : Core) (x c a : ℕ) :
    a < C.switchEnd x c ↔ a < C.nonemptyEnd x c ∧ x+C.offset+C.step*a ≤ C.column := by
  rw [Core.switchEnd, lt_linearEnd, Nat.lt_succ_iff]
def cubicInterval (p : Quad) (q : Cubic) (l r : ℕ) : ℤ :=
  if l < r then prefixCubic p q r - if l = 0 then 0 else prefixCubic p q l else 0
private theorem cubicInterval_eq (p : Quad) (q : Cubic) (l r : ℕ) :
    cubicInterval p q l r = 60*(∑ a ∈ Ico l r, p.eval a*q.at a) := by
  unfold cubicInterval
  by_cases h : l < r
  · rw [ite_eq_left h, sum_Ico_eq_sub _ h.le, mul_sub, ← prefix_eq, ← prefix_eq]
    split
    · subst l
      simp [prefixCubic]
    · rfl
  · rw [ite_eq_right h, Ico_eq_empty_of_le (by omega), sum_empty, mul_zero]
def Core.window (C : Core) (x c : ℕ) : ℤ :=
  let b := C.switchEnd x c
  let n := C.nonemptyEnd x c
  let L : Line := ⟨c,1⟩
  let fixed : Line := ⟨x,0⟩
  let falling : Line := ⟨(C.column : ℤ)-C.offset,-(C.step : ℤ)⟩
  let f := fun R => windowCubic L R C.countLine C.widthLine (-1) C.widthSlope
  cubicInterval C.seed (f fixed) 0 b + cubicInterval C.seed (f falling) b n
theorem Core.window_eq (C : Core) (x c : ℕ) :
    C.window x c = 360*(∑ a ∈ range C.cap, C.seed.eval a * ∑ t ∈ C.slice x c a, C.term a t) := by
  let n := C.nonemptyEnd x c
  let b := C.switchEnd x c
  let f := fun a : ℕ => C.seed.eval a * ∑ t ∈ C.slice x c a, C.term a t
  have hb : b ≤ n := Nat.le_of_not_gt fun h => (Nat.lt_irrefl _) ((lt_switchEnd C x c n).mp h).1
  have hn : n ≤ C.cap := Nat.le_of_not_gt fun h => (Nat.lt_irrefl _) ((lt_nonemptyEnd C x c C.cap).mp h).1
  have hs : (∑ a ∈ range n, f a) = ∑ a ∈ range C.cap, f a := by
    apply sum_subset (range_subset_range.mpr hn)
    intro a ha ha'
    have ha := mem_range.mp ha
    have hz : min x (C.column-(C.offset+C.step*a)) ≤ a+c := by
      by_contra! h
      exact ha' (mem_range.mpr ((lt_nonemptyEnd C x c a).mpr ⟨ha,h⟩))
    simp [f, Core.slice, Ico_eq_empty_of_le hz]
  rw [← hs, ← sum_range_add_sum_Ico f hb, mul_add]
  simp only [Core.window, ← Nat.Ico_zero_eq_range b, cubicInterval_eq]
  change 60*(∑ a ∈ Ico 0 b, _) + 60*(∑ a ∈ Ico b n, _) =
    360*(∑ a ∈ Ico 0 b, f a) + 360*(∑ a ∈ Ico b n, f a)
  have hmul : (360 : ℤ) = 60*6 := rfl
  rw [hmul]
  simp only [mul_assoc, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro a ha
    have hab := (mem_Ico.mp ha).2
    obtain ⟨han,hfix⟩ := (lt_switchEnd C x c a).mp hab
    have hav := ((lt_nonemptyEnd C x c a).mp han).2
    rw [show min x (C.column-(C.offset+C.step*a)) = x by omega] at hav
    have hv := windowCubic_eq ⟨(c : ℤ),1⟩ ⟨(x : ℤ),0⟩ C.countLine C.widthLine (-1)
      C.widthSlope a (a+c) x (by simp [Line.at, add_comm]) (by simp [Line.at]) hav.le
    rw [hv]
    simp only [f, Core.slice, min_eq_left (by omega : x ≤ C.column-(C.offset+C.step*a)), Core.term]
    simp only [neg_one_mul, ← sub_eq_add_neg]
    ring
  · apply sum_congr rfl
    intro a ha
    obtain ⟨ha₁,ha₂⟩ := mem_Ico.mp ha
    have hav := ((lt_nonemptyEnd C x c a).mp ha₂).2
    have hfall : C.column-(C.offset+C.step*a) ≤ x := by
      by_contra! h
      exact (not_lt_of_ge ha₁) ((lt_switchEnd C x c a).mpr ⟨ha₂,by omega⟩)
    have hle : C.offset+C.step*a ≤ C.column := by omega
    rw [min_eq_right hfall] at hav
    have hv := windowCubic_eq ⟨(c : ℤ),1⟩
      ⟨(C.column : ℤ)-C.offset,-(C.step : ℤ)⟩ C.countLine C.widthLine (-1)
      C.widthSlope a (a+c) (C.column-(C.offset+C.step*a))
      (by simp [Line.at, add_comm])
      (by simp only [Line.at, Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]; ring) hav.le
    rw [hv]
    simp only [f, Core.slice, min_eq_right hfall, Core.term]
    simp only [neg_one_mul, ← sub_eq_add_neg]
    ring
theorem Core.prefix_eq (C : Core) (x J : ℕ) :
    C.window x 0 - C.window x (J+1) =
      360*(∑ t ∈ range x, ∑ a ∈ range C.cap,
        if a ≤ t ∧ t < a+(J+1) ∧ t+(C.offset+C.step*a) < C.column
        then C.seed.eval a*C.term a t else 0) := by
  rw [Core.window_eq, Core.window_eq, ← mul_sub, sum_comm (s := range x), ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro a _
  have hfilter (c : ℕ) :
      C.slice x c a = (range x).filter
        (fun t => a+c ≤ t ∧ t+(C.offset+C.step*a) < C.column) := by
    ext t
    simp only [Core.slice, mem_Ico, lt_min_iff, mem_filter, mem_range]
    omega
  simp_rw [hfilter, mul_sum, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  by_cases hl : a ≤ t <;> by_cases hu : t < a+(J+1) <;>
    by_cases hk : t+(C.offset+C.step*a) < C.column <;>
    have hu' : a+(J+1) ≤ t ↔ ¬t < a+(J+1) := by omega
  all_goals omega
end P1_7_6_4
end
section
namespace P1_7_6
open Finset
open P1 (agreement)
open K1_14 (Shape slots triangle)
open P1_7 (debit)
private theorem lt_seedEnd (s : Shape) (v d R a : ℕ) :
    a < seedEnd s v d R ↔ a < R ∧ (a+d)*v ≤ s.U := by
  unfold seedEnd
  by_cases hv : v = 0
  · simp [hv]
  · rw [ite_eq_right hv, lt_min_iff, ← Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)]
    omega
private theorem yStart_eq (E d t a : ℕ) (he : 0 < E) (ha : a ≤ t) :
    t-a+E*(a+d) = yStart E d t + (E-1)*a := by
  apply Int.ofNat_inj.mp
  simp only [yStart, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ha, Nat.cast_sub he, Nat.cast_one]
  ring
private theorem seedQuad_eq (s : Shape) (v d a : ℕ) (ha : (a+d)*v ≤ s.U) :
    (seedQuad s v d).eval a = 2*(slots s.U ((a+d)*v) : ℤ) := by
  let n := s.U-(a+d)*v
  have hc : (n : ℤ) = (s.U : ℤ)-((a : ℤ)+d)*v := by
    simp only [n, Nat.cast_sub ha, Nat.cast_add, Nat.cast_mul]
  have hp : ((n : ℤ)+1)*((n : ℤ)+2) = 2*(triangle n : ℤ) := by
    have ht := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self (n+1)))
    change (n+1)*(n+2)/2*2 = (n+1)*(n+2) at ht
    have hz := congrArg (fun k : ℕ => (k : ℤ)) ht
    change (↑(triangle n*2 : ℕ) : ℤ) = (↑((n+1)*(n+2) : ℕ) : ℤ) at hz
    push_cast at hz
    linarith
  rw [slots, ite_eq_left ha]
  change _ = 2*(triangle n : ℤ)
  rw [← hp, hc, seedQuad, Quad.eval_ofLines]
  ring
private theorem sum_clipped {f g : ℕ → ℤ} {L R T : ℕ}
    (hr : ∀ a, a < T → a < R)
    (hz : ∀ a ∈ Ico L R, T ≤ a → f a = 0)
    (he : ∀ a ∈ Ico L T, f a = g a) :
    (∑ a ∈ Ico L R, f a) = ∑ a ∈ Ico L T, g a := by
  calc
    _ = ∑ a ∈ Ico L T, f a := by
      symm
      apply sum_subset
      · intro a ha
        exact mem_Ico.mpr ⟨(mem_Ico.mp ha).1, hr a (mem_Ico.mp ha).2⟩
      · intro a ha hn
        exact hz a ha (le_of_not_gt fun h => hn (mem_Ico.mpr ⟨(mem_Ico.mp ha).1,h⟩))
    _ = _ := sum_congr rfl he
end P1_7_6
end
section
namespace P1_7_6_4
open Finset
open K1_14 (Shape)
open P1 (agreement)
open P1_7_6
open P1_7_6 (lt_seedEnd)
def diagonalCore (C : Core) (J t : ℕ) : ℤ :=
  ∑ a ∈ range C.cap,
    if a ≤ t ∧ t < a+(J+1) ∧ t+(C.offset+C.step*a) < C.column
    then C.seed.eval a*C.term a t else 0
def corePrefix (C : Core) (J x : ℕ) : ℤ := C.window x 0 - C.window x (J+1)
end P1_7_6_4
end
