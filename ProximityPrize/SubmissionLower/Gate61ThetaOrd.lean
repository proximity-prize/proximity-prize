import ProximityPrize.SubmissionLower.Gate61GateT

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option Elab.async false

namespace Gate61Bilinear

open K1_13

def No (z1 z2 z3 w1 w2 w3 x1 x2 x3 y1 y2 y3 : ℤ) : ℤ :=
  (0) * x1 * y1
  + (16*(w2*z3 + w3*z2 - 3*w3*z3)) * x1 * y2
  + (16*(w2 - 3*w3)*(z2 - 3*z3)) * x1 * y3
  + (16*(w2*z3 + w3*z2 - 3*w3*z3)) * x2 * y1
  + (8*(2*w1*z3 - 3*w2*z3 + 2*w3*z1 - 3*w3*z2 + 7*w3*z3)) * x2 * y2
  + (8*(2*w1*z2 - 6*w1*z3 + 2*w2*z1 - 3*w2*z2 + 7*w2*z3 - 6*w3*z1 + 7*w3*z2 - 15*w3*z3)) * x2 * y3
  + (16*(w2 - 3*w3)*(z2 - 3*z3)) * x3 * y1
  + (8*(2*w1*z2 - 6*w1*z3 + 2*w2*z1 - 3*w2*z2 + 7*w2*z3 - 6*w3*z1 + 7*w3*z2 - 15*w3*z3)) * x3 * y2
  + (-8*(6*w1*z2 - 18*w1*z3 + 6*w2*z1 - 7*w2*z2 + 15*w2*z3 - 18*w3*z1 + 15*w3*z2 - 27*w3*z3)) * x3 * y3

theorem mixed32_formula (x y z w : Shape) :
    mixed32 x y z w = (No z.b z.j z.t w.b w.j w.t x.b x.j x.t y.b y.j y.t).toNat := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  obtain ⟨z1, z2, z3⟩ := z
  obtain ⟨w1, w2, w3⟩ := w
  unfold mixed32
  congr 1
  simp only [difference, volume32, Shape.plus, No]
  push_cast
  ring

structure OP where
  z1 : ℤ
  z2 : ℤ
  z3 : ℤ
  w1 : ℤ
  w2 : ℤ
  w3 : ℤ

def OP.cone (P : OP) (c1 c2 c3 d1 d2 d3 : ℤ) : ℤ :=
  No P.z1 P.z2 P.z3 P.w1 P.w2 P.w3 (c1 + c2 + 3*c3) (c2 + 3*c3) c3 (d1 + d2 + 3*d3) (d2 + 3*d3) d3

def OP.ray (P : OP) (i k : Fin 3) : ℤ :=
  P.cone (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0)
    (if k = 0 then 1 else 0) (if k = 1 then 1 else 0) (if k = 2 then 1 else 0)

theorem ocone_expand (P : OP) (c1 c2 c3 d1 d2 d3 : ℤ) :
    P.cone c1 c2 c3 d1 d2 d3 =
      c1*d1 * P.ray 0 0 + c1*d2 * P.ray 0 1 + c1*d3 * P.ray 0 2 +
      c2*d1 * P.ray 1 0 + c2*d2 * P.ray 1 1 + c2*d3 * P.ray 1 2 +
      c3*d1 * P.ray 2 0 + c3*d2 * P.ray 2 1 + c3*d3 * P.ray 2 2 := by
  simp only [OP.ray, OP.cone, No]
  simp
  ring

theorem otheta_cone (Px Ph : OP) (num den : ℤ)
    (h : ∀ i k : Fin 3, den * Px.ray i k ≤ num * Ph.ray i k)
    (c1 c2 c3 d1 d2 d3 : ℤ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) :
    den * Px.cone c1 c2 c3 d1 d2 d3 ≤ num * Ph.cone c1 c2 c3 d1 d2 d3 := by
  rw [ocone_expand, ocone_expand]
  have key : ∀ (a b : ℤ) (i k : Fin 3), 0 ≤ a → 0 ≤ b →
      den * ((a*b) * Px.ray i k) ≤ num * ((a*b) * Ph.ray i k) := by
    intro a b i k ha hb
    have := mul_le_mul_of_nonneg_left (h i k) (mul_nonneg ha hb)
    linarith
  have := key c1 d1 0 0 hc1 hd1
  have := key c1 d2 0 1 hc1 hd2
  have := key c1 d3 0 2 hc1 hd3
  have := key c2 d1 1 0 hc2 hd1
  have := key c2 d2 1 1 hc2 hd2
  have := key c2 d3 1 2 hc2 hd3
  have := key c3 d1 2 0 hc3 hd1
  have := key c3 d2 2 1 hc3 hd2
  have := key c3 d3 2 2 hc3 hd3
  linarith

def opOf (z w : Shape) : OP := ⟨z.b, z.j, z.t, w.b, w.j, w.t⟩

theorem mixed32_cone (z w q1 q2 : Shape)
    (h1c : q1.j ≤ q1.b) (h1t : 3 * q1.t ≤ q1.j) (h2c : q2.j ≤ q2.b) (h2t : 3 * q2.t ≤ q2.j) :
    mixed32 q1 q2 z w =
      ((opOf z w).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t).toNat := by
  rw [mixed32_formula]
  congr 1
  simp only [OP.cone, opOf]
  congr 1 <;> push_cast [Nat.cast_sub h1c, Nat.cast_sub h1t, Nat.cast_sub h2c, Nat.cast_sub h2t] <;> ring_nf

theorem mixed32_theta (zx wx zh wh q1 q2 : Shape) (num den : ℕ)
    (h : ∀ i k : Fin 3, (den : ℤ) * (opOf zx wx).ray i k ≤ num * (opOf zh wh).ray i k)
    (h1c : q1.j ≤ q1.b) (h1t : 3 * q1.t ≤ q1.j) (h2c : q2.j ≤ q2.b) (h2t : 3 * q2.t ≤ q2.j) :
    den * mixed32 q1 q2 zx wx ≤ num * mixed32 q1 q2 zh wh := by
  rw [mixed32_cone zx wx q1 q2 h1c h1t h2c h2t, mixed32_cone zh wh q1 q2 h1c h1t h2c h2t]
  have := otheta_cone _ _ (num : ℤ) (den : ℤ) h
    ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
    ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  generalize (opOf zx wx).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t = A at this ⊢
  generalize (opOf zh wh).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t = B at this ⊢
  have hn : (0:ℤ) ≤ num := by positivity
  have hd : (0:ℤ) ≤ den := by positivity
  have eA : (A.toNat : ℤ) = max A 0 := Int.toNat_eq_max A
  have eB : (B.toNat : ℤ) = max B 0 := Int.toNat_eq_max B
  have : ((den * A.toNat : ℕ) : ℤ) ≤ ((num * B.toNat : ℕ) : ℤ) := by
    push_cast
    rw [eA, eB]
    rcases le_total 0 A with hA | hA <;> rcases le_total 0 B with hB | hB
    · rw [max_eq_left hA, max_eq_left hB]; exact this
    · rw [max_eq_left hA, max_eq_right hB]; nlinarith
    · rw [max_eq_right hA, max_eq_left hB]; nlinarith
    · rw [max_eq_right hA, max_eq_right hB]; simp
  exact_mod_cast this

end Gate61Bilinear
