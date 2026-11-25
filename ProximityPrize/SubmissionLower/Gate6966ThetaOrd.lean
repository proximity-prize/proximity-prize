import ProximityPrize.SubmissionLower.Gate6966Bilinear
import ProximityPrize.SubmissionLower.Gate6966Tail
import ProximityPrize.SubmissionLower.Gate6966Assm
import ProximityPrize.SubmissionLower.Gate6966Amb
import ProximityPrize.SubmissionLower.Low6966WeightedCut

set_option Elab.async false

-- merged module Gate6966GateT
section Merged_Gate6966GateT

-- merged module Gate6966Theta
section Merged_Gate6966Theta

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option Elab.async false

namespace Gate6966Bilinear

open Low6966Prices K1_13

structure TP where
  B1 : ℤ
  J2 : ℤ
  t : ℤ
  k : ℤ
  h1 : ℤ
  h2 : ℤ

def TP.eval (P : TP) (x1 x2 x3 y1 y2 y3 : ℤ) : ℤ :=
  Nt P.B1 P.J2 P.t P.k P.h1 P.h2 x1 x2 x3 y1 y2 y3

def TP.cone (P : TP) (c1 c2 c3 d1 d2 d3 : ℤ) : ℤ :=
  P.eval (c1 + c2 + 3*c3) (c2 + 3*c3) c3 (d1 + d2 + 3*d3) (d2 + 3*d3) d3

def TP.ray (P : TP) (i k : Fin 3) : ℤ :=
  P.cone (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0)
    (if k = 0 then 1 else 0) (if k = 1 then 1 else 0) (if k = 2 then 1 else 0)

theorem cone_expand (P : TP) (c1 c2 c3 d1 d2 d3 : ℤ) :
    P.cone c1 c2 c3 d1 d2 d3 =
      c1*d1 * P.ray 0 0 + c1*d2 * P.ray 0 1 + c1*d3 * P.ray 0 2 +
      c2*d1 * P.ray 1 0 + c2*d2 * P.ray 1 1 + c2*d3 * P.ray 1 2 +
      c3*d1 * P.ray 2 0 + c3*d2 * P.ray 2 1 + c3*d3 * P.ray 2 2 := by
  simp only [TP.ray, TP.cone, TP.eval, Nt]
  simp
  ring

theorem theta_cone (Px Ph : TP) (num den : ℤ)
    (h : ∀ i k : Fin 3, den * Px.ray i k ≤ num * Ph.ray i k)
    (c1 c2 c3 d1 d2 d3 : ℤ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) :
    den * Px.cone c1 c2 c3 d1 d2 d3 ≤ num * Ph.cone c1 c2 c3 d1 d2 d3 := by
  rw [cone_expand, cone_expand]
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

def tpOf (p : Shape) (k h1 h2 : ℕ) : TP :=
  ⟨((p.b - 1 : ℕ) : ℤ), ((p.j - 2 : ℕ) : ℤ), p.t, k, h1, h2⟩

theorem tiltedPair_cone (p q1 q2 : Shape) (hb : p.j + 1 ≤ p.b) (hj : 2 ≤ p.j) (k h1 h2 : ℕ)
    (hk : Low6966Prices.taylorLength - 4 = k) (hh1 : (bentLift k p).2 = h1)
    (hh2 : (bentLift (k + 1) p).2 = h2)
    (h1c : q1.j ≤ q1.b) (h1t : 3 * q1.t ≤ q1.j) (h2c : q2.j ≤ q2.b) (h2t : 3 * q2.t ≤ q2.j) :
    Gate6966.tiltedPair p q1 q2 =
      ((tpOf p k h1 h2).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t).toNat := by
  rw [tiltedPair_formula p q1 q2 hb hj k h1 h2 hk hh1 hh2]
  congr 1
  simp only [TP.cone, TP.eval, tpOf]
  congr 1 <;> push_cast [Nat.cast_sub h1c, Nat.cast_sub h1t, Nat.cast_sub h2c, Nat.cast_sub h2t] <;> ring_nf

theorem tiltedPair_theta (px ph q1 q2 : Shape) (num den : ℕ)
    (hbx : px.j + 1 ≤ px.b) (hjx : 2 ≤ px.j) (hbh : ph.j + 1 ≤ ph.b) (hjh : 2 ≤ ph.j)
    (k hx1 hx2 hh1 hh2 : ℕ) (hk : Low6966Prices.taylorLength - 4 = k)
    (hx1' : (bentLift k px).2 = hx1) (hx2' : (bentLift (k + 1) px).2 = hx2)
    (hh1' : (bentLift k ph).2 = hh1) (hh2' : (bentLift (k + 1) ph).2 = hh2)
    (h : ∀ i k' : Fin 3, (den : ℤ) * (tpOf px k hx1 hx2).ray i k' ≤ num * (tpOf ph k hh1 hh2).ray i k')
    (h1c : q1.j ≤ q1.b) (h1t : 3 * q1.t ≤ q1.j) (h2c : q2.j ≤ q2.b) (h2t : 3 * q2.t ≤ q2.j) :
    den * Gate6966.tiltedPair px q1 q2 ≤ num * Gate6966.tiltedPair ph q1 q2 := by
  rw [tiltedPair_cone px q1 q2 hbx hjx k hx1 hx2 hk hx1' hx2' h1c h1t h2c h2t,
    tiltedPair_cone ph q1 q2 hbh hjh k hh1 hh2 hk hh1' hh2' h1c h1t h2c h2t]
  have := theta_cone _ _ (num : ℤ) (den : ℤ) h
    ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
    ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  generalize (tpOf px k hx1 hx2).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t = A at this ⊢
  generalize (tpOf ph k hh1 hh2).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
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

example : ∀ i k : Fin 3, (10000 : ℤ) * (TP.mk 119 48 12 133505 133506 133507).ray i k ≤
    7614 * (TP.mk 136 55 14 133505 133506 133507).ray i k := by
  decide +kernel

end Gate6966Bilinear

end Merged_Gate6966Theta

-- merged module Gate6966GlueT
section Merged_Gate6966GlueT

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Gate6966Cell
open Gate6966FreeCard (mx mn mx_eq mn_eq)
open K1_13 (Row Shape shape InBox)
open Gate6966Bilinear (tpOf TP)
open Low6966SharedPrice (coord)

def Gt.mat (G : Gt) (i k : Fin 3) : ℤ :=
  ![![(G.m00 : ℤ), G.m01, G.m02], ![(G.m01 : ℤ), G.m11, G.m12], ![(G.m02 : ℤ), G.m12, G.m22]] i k

theorem Tp_eq (G : Gt) (ph q1 q2 : Shape) (hb : ph.j + 1 ≤ ph.b) (hj : 2 ≤ ph.j) (k h1 h2 : ℕ)
    (hk : Low6966Prices.taylorLength - 4 = k) (hh1 : (Low6966Prices.bentLift k ph).2 = h1)
    (hh2 : (Low6966Prices.bentLift (k + 1) ph).2 = h2)
    (hM : ∀ i k', (tpOf ph k h1 h2).ray i k' = G.mat i k')
    (c1 : q1.j ≤ q1.b ∧ 3 * q1.t ≤ q1.j) (c2 : q2.j ≤ q2.b ∧ 3 * q2.t ≤ q2.j) :
    Gate6966.tiltedPair ph q1 q2 = TT G q1.b q1.j q1.t q2.b q2.j q2.t := by
  rw [Gate6966Bilinear.tiltedPair_cone ph q1 q2 hb hj k h1 h2 hk hh1 hh2 c1.1 c1.2 c2.1 c2.2,
    Gate6966Bilinear.cone_expand]
  have e := fun i k' => hM i k'
  simp only [e, Gt.mat]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  symm
  rw [← Int.toNat_natCast (TT G q1.b q1.j q1.t q2.b q2.j q2.t)]
  congr 1
  unfold TT
  push_cast
  ring


open K1_13 (Shape)
open Gate6966Bilinear (TP tpOf)

/-- A gate matrix can be certified on a different upper chart. The priced
factor only needs its own chart formula and the nine cross-chart inequalities. -/
theorem tilted_le_saved_matrix (G : Gt) (px q1 q2 : Shape) (num den : ℕ) (hd : 0<den)
    (hbx : px.j+1≤px.b) (hjx : 2≤px.j) (k hx1 hx2 : ℕ)
    (hk : Low6966Prices.taylorLength-4=k)
    (hh1 : (Low6966Prices.bentLift k px).2=hx1)
    (hh2 : (Low6966Prices.bentLift (k+1) px).2=hx2)
    (upper : TP) (matrix : ∀ i j,upper.ray i j=G.mat i j)
    (rays : ∀ i j,(den:ℤ)*(tpOf px k hx1 hx2).ray i j≤num*upper.ray i j)
    (c1 : q1.j≤q1.b ∧ 3*q1.t≤q1.j) (c2 : q2.j≤q2.b ∧ 3*q2.t≤q2.j) :
    (Gate6966.tiltedPair px q1 q2:ℚ)≤(num:ℚ)/den*(TT G q1.b q1.j q1.t q2.b q2.j q2.t:ℚ) := by
  let a : ℤ := (q1.b-q1.j:ℕ)
  let b : ℤ := (q1.j-3*q1.t:ℕ)
  let d : ℤ := (q2.b-q2.j:ℕ)
  let e : ℤ := (q2.j-3*q2.t:ℕ)
  have price : upper.cone a b q1.t d e q2.t=(TT G q1.b q1.j q1.t q2.b q2.j q2.t:ℤ) := by
    rw [Gate6966Bilinear.cone_expand]
    simp only [matrix,Gt.mat,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.isValue]
    unfold TT a b d e
    push_cast
    ring
  have compare:=Gate6966Bilinear.theta_cone _ upper num den rays a b q1.t d e q2.t
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [price] at compare
  rw [Gate6966Bilinear.tiltedPair_cone px q1 q2 hbx hjx k hx1 hx2 hk hh1 hh2 c1.1 c1.2 c2.1 c2.2]
  let x:ℤ:=(tpOf px k hx1 hx2).cone a b q1.t d e q2.t
  let y:=TT G q1.b q1.j q1.t q2.b q2.j q2.t
  change (x.toNat:ℚ)≤(num:ℚ)/den*y
  change (den:ℤ)*x≤num*(y:ℤ) at compare
  rw [div_mul_eq_mul_div,le_div_iff₀ (by exact_mod_cast hd : (0:ℚ)<den)]
  by_cases hx : 0≤x
  · have xi : (x.toNat:ℤ)=x:=Int.toNat_of_nonneg hx
    have cost : (x.toNat:ℤ)*den≤num*(y:ℤ) := by simpa only [xi,mul_comm x] using compare
    exact_mod_cast cost
  · simpa only [Int.toNat_eq_zero.mpr (by omega : x≤0),Nat.cast_zero,zero_mul] using
      (mul_nonneg (Nat.cast_nonneg num : (0:ℚ)≤num) (Nat.cast_nonneg y))


theorem Tt_le (G : Gt) (ph px q1 q2 : Shape) (num den : ℕ) (hden : 0 < den)
    (hbh : ph.j + 1 ≤ ph.b) (hjh : 2 ≤ ph.j) (hbx : px.j + 1 ≤ px.b) (hjx : 2 ≤ px.j) (k h1 h2 hx1 hx2 : ℕ)
    (hk : Low6966Prices.taylorLength - 4 = k) (hh1 : (Low6966Prices.bentLift 133446 ph).2 = h1)
    (hh2 : (Low6966Prices.bentLift 133447 ph).2 = h2) (hx1' : (Low6966Prices.bentLift k px).2 = hx1)
    (hx2' : (Low6966Prices.bentLift (k + 1) px).2 = hx2)
    (hM : ∀ i k', (tpOf ph 133446 h1 h2).ray i k' = G.mat i k')
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (tpOf px k hx1 hx2).ray i k' ≤ num * (tpOf ph 133446 h1 h2).ray i k')
    (c1 : q1.j ≤ q1.b ∧ 3 * q1.t ≤ q1.j) (c2 : q2.j ≤ q2.b ∧ 3 * q2.t ≤ q2.j) :
    (Gate6966.tiltedPair px q1 q2 : ℚ) ≤ (num : ℚ) / den * (TT G q1.b q1.j q1.t q2.b q2.j q2.t : ℚ) := by
  exact tilted_le_saved_matrix G px q1 q2 num den hden hbx hjx k hx1 hx2 hk hx1' hx2'
    (tpOf ph 133446 h1 h2) hM hθ c1 c2

theorem alg (tp1 tp2 tp3 tp4 tp5 T1 T2 Txe TXe Txq TXq Txs ts N cc ρ v AA AX : ℚ)
    (hc0 : 0 ≤ cc) (hc1 : cc ≤ 1) (hρ : 0 ≤ ρ) (hv : 0 ≤ v) (hN : 0 ≤ N)
    (t1 : tp1 ≤ N * T1) (t2 : tp2 ≤ N * T2) (t3 : tp3 ≤ N * Txe) (t4 : tp4 ≤ N * Txq) (t5 : tp5 ≤ N * Txs)
    (m3 : Txe ≤ TXe) (m4 : Txq ≤ TXq) (m5 : Txs ≤ ts)
    (core : (1 - cc) * T1 + T2 + ρ * TXe + cc * ρ * TXq + v * ρ ^ 2 * ts ≤ 1920 * AA * ρ ^ 2)
    (hA : N * AA ≤ AX) :
    (1 - cc) * (tp1 / 1920) + tp2 / 1920 + ρ * (tp3 / 1920) + cc * ρ * (tp4 / 1920) + v * ρ ^ 2 * (tp5 / 1920) ≤ AX * ρ ^ 2 := by
  have u1 := mul_le_mul_of_nonneg_left t1 (sub_nonneg.mpr hc1)
  have u3 := mul_le_mul_of_nonneg_left t3 hρ
  have u4 := mul_le_mul_of_nonneg_left t4 (mul_nonneg hc0 hρ)
  have u5 := mul_le_mul_of_nonneg_left t5 (mul_nonneg hv (sq_nonneg ρ))
  have w3 := mul_le_mul_of_nonneg_left m3 (mul_nonneg hN hρ)
  have w4 := mul_le_mul_of_nonneg_left m4 (mul_nonneg hN (mul_nonneg hc0 hρ))
  have w5 := mul_le_mul_of_nonneg_left m5 (mul_nonneg hN (mul_nonneg hv (sq_nonneg ρ)))
  have hc := mul_le_mul_of_nonneg_left core hN
  have hA' := mul_le_mul_of_nonneg_right hA (sq_nonneg ρ)
  nlinarith [u1, u3, u4, u5, w3, w4, w5, hc, hA', t2]

theorem rhs_le_tilted (f : Row 4) (G : Gt) (hG : G.Ok) (hlift : G.lift = false) (hsc : G.sc = 1920)
    (hxt : 3 * G.xt ≤ G.xj) (hbh : G.xj + 1 ≤ G.xb) (hjh : 2 ≤ G.xj)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (htf : 3 * (shape f).t + 3 ≤ (shape f).j ∧ (shape f).j + 1 ≤ (shape f).b)
    (k h1 h2 hx1 hx2 : ℕ) (hk : Low6966Prices.taylorLength - 4 = k)
    (hh1 : (Low6966Prices.bentLift 133446 ⟨G.xb, G.xj, G.xt⟩).2 = h1)
    (hh2 : (Low6966Prices.bentLift 133447 ⟨G.xb, G.xj, G.xt⟩).2 = h2)
    (hx1' : (Low6966Prices.bentLift k (shape f)).2 = hx1) (hx2' : (Low6966Prices.bentLift (k + 1) (shape f)).2 = hx2)
    (hM : ∀ i k', (tpOf ⟨G.xb, G.xj, G.xt⟩ 133446 h1 h2).ray i k' = G.mat i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (tpOf (shape f) k hx1 hx2).ray i k' ≤ num * (tpOf ⟨G.xb, G.xj, G.xt⟩ 133446 h1 h2).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (qs : Shape) (hqs : qs = ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩)
    (r a cn vn W : ℕ) (B η : Fin 3 → ℕ) (hρ : a < r) (hcn : cn ≤ 2 * (r - a))
    (hI : lhsV (mkPr G r a cn vn W (B 0) (B 1) (B 2)) (B 0 - a * G.lb - η 0) (B 1 - a * G.lj - η 1)
      (B 2 - a * G.lt - η 2) (η 0) (η 1) (η 2) ≤ (mkPr G r a cn vn W (B 0) (B 1) (B 2)).rhs) :
    Gate6966Final.rhs f qs r a ((cn : ℚ) / (2 * ((r - a : ℕ) : ℚ))) ((vn : ℚ) / 10000000) B η ≤
      (Ax : ℚ) * ((r - a : ℕ) : ℚ) ^ 2 := by
  have hpx : (shape f).chamber = shape f := by
    have : max (shape f).b (shape f).j = (shape f).b := max_eq_left (by omega)
    cases hsh : shape f with
    | mk b j t => simp only [hsh] at this htf ⊢; simp only [K1_13.Shape.chamber, this]
  set Yb : Fin 3 → ℕ := fun i => B i - (a * coord (shape f) i + η i) with hYb
  have hy0 : Yb 0 ≤ B 0 - a * G.lb - η 0 := by
    show B 0 - (a * (shape f).b + η 0) ≤ _
    have := Nat.mul_le_mul_left a hlo.1; omega
  have hy1 : Yb 1 ≤ B 1 - a * G.lj - η 1 := by
    show B 1 - (a * (shape f).j + η 1) ≤ _
    have := Nat.mul_le_mul_left a hlo.2.1; omega
  have hy2 : Yb 2 ≤ B 2 - a * G.lt - η 2 := by
    show B 2 - (a * (shape f).t + η 2) ≤ _
    have := Nat.mul_le_mul_left a hlo.2.2; omega
  have core := core G hG hxt r a cn vn W (B 0) (B 1) (B 2) hρ hcn hy0 hy1 hy2 hI
  rw [hlift] at core
  simp only [hB, hJ, hT, Bool.cond_false, mx_eq, mn_eq] at core
  unfold Gate6966Final.rhs Gate6966Final.Tt
  simp only [hpx]
  have hq : Gate6966Final.boxOf Yb = ⟨max (Yb 0) (Yb 1), Yb 1, min (Yb 2) (Yb 1 / 3)⟩ := rfl
  have he : Gate6966Final.boxOf η = ⟨max (η 0) (η 1), η 1, min (η 2) (η 1 / 3)⟩ := rfl
  have cq := Gate6966Final.boxOf_chamber Yb
  have ce := Gate6966Final.boxOf_chamber η
  have cqs : qs.j ≤ qs.b ∧ 3 * qs.t ≤ qs.j := by
    subst hqs
    simp only [Gt.sep, hlift, hB, hJ, hT, Bool.cond_false, mx_eq, mn_eq]
    refine ⟨le_max_right _ _, ?_⟩
    have := Nat.min_le_right (G.xt - 1) ((G.xj - 3) / 3)
    omega
  have hρpos : (0 : ℚ) ≤ ((r - a : ℕ) : ℚ) := Nat.cast_nonneg _
  have hcc0 : (0 : ℚ) ≤ (cn : ℚ) / (2 * ((r - a : ℕ) : ℚ)) := by positivity
  have hcc1 : (cn : ℚ) / (2 * ((r - a : ℕ) : ℚ)) ≤ 1 := by
    have hpos : (0 : ℚ) < 2 * ((r - a : ℕ) : ℚ) := by
      have : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hρ
      linarith
    rw [div_le_one hpos]; exact_mod_cast hcn
  have hv0 : (0 : ℚ) ≤ (vn : ℚ) / 10000000 := by positivity
  have T := fun (q1 q2 : Shape) (c1 : q1.j ≤ q1.b ∧ 3 * q1.t ≤ q1.j) (c2 : q2.j ≤ q2.b ∧ 3 * q2.t ≤ q2.j) =>
    Tt_le G ⟨G.xb, G.xj, G.xt⟩ (shape f) q1 q2 num den hden hbh hjh (by omega) (by omega) k h1 h2 hx1 hx2 hk hh1 hh2
      hx1' hx2' hM hθ c1 c2
  have cx : (shape f).j ≤ (shape f).b ∧ 3 * (shape f).t ≤ (shape f).j := ⟨by omega, by omega⟩
  have cX : Cone (mx G.xb G.xj) G.xj G.xt := ⟨by rw [mx_eq]; exact le_max_right _ _, hxt⟩
  have cxC : Cone (shape f).b (shape f).j (shape f).t := cx
  have mxle : (shape f).b ≤ mx G.xb G.xj := by rw [mx_eq]; exact hhi.1.trans (le_max_left _ _)
  have t1 := T _ _ ⟨cq.1, cq.2.1⟩ ⟨cq.1, cq.2.1⟩
  have t2 := T _ _ ⟨ce.1, ce.2.1⟩ ⟨cq.1, cq.2.1⟩
  have t3 := T _ _ cx ⟨ce.1, ce.2.1⟩
  have t4 := T _ _ cx ⟨cq.1, cq.2.1⟩
  have t5 := T _ _ cx cqs
  have m3 : TT G (shape f).b (shape f).j (shape f).t (Gate6966Final.boxOf η).b (Gate6966Final.boxOf η).j (Gate6966Final.boxOf η).t ≤
      TT G (mx G.xb G.xj) G.xj G.xt (Gate6966Final.boxOf η).b (Gate6966Final.boxOf η).j (Gate6966Final.boxOf η).t :=
    TT_mono_left G hG cxC cX ⟨ce.1, ce.2.1⟩ mxle hhi.2.1 hhi.2.2
  have m4 : TT G (shape f).b (shape f).j (shape f).t (Gate6966Final.boxOf Yb).b (Gate6966Final.boxOf Yb).j (Gate6966Final.boxOf Yb).t ≤
      TT G (mx G.xb G.xj) G.xj G.xt (Gate6966Final.boxOf Yb).b (Gate6966Final.boxOf Yb).j (Gate6966Final.boxOf Yb).t :=
    TT_mono_left G hG cxC cX ⟨cq.1, cq.2.1⟩ mxle hhi.2.1 hhi.2.2
  have m5 : TT G (shape f).b (shape f).j (shape f).t qs.b qs.j qs.t ≤ G.tsep := by
    subst hqs
    exact TT_mono_left G hG cxC cX cqs mxle hhi.2.1 hhi.2.2
  have hN : (0 : ℚ) ≤ (num : ℚ) / den := by positivity
  simp only [Gate6966Final.boxOf] at t1 t2 t3 t4 t5 m3 m4 ⊢
  have hA' : (num : ℚ) / den * G.A ≤ Ax := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast (by linarith [hA] : num * G.A ≤ Ax * den)
  rw [hsc] at core
  push_cast at core
  simp only [hYb] at t1 t2 t4 m4 core
  simp only [mx_eq] at m3 m4
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcc0 hcc1 hρpos hv0 hN t1 t2 t3 t4 t5
    (Nat.cast_le.mpr m3) (Nat.cast_le.mpr m4) (Nat.cast_le.mpr m5) core hA'

end Gate6966Cell

end Merged_Gate6966GlueT

-- merged module Gate6966GateT
section Merged_Gate6966GateT

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Gate6966Cell
open P3 (K)
open K1_13 (Row Shape shape InBox)
open Gate6966Bilinear (tpOf)
open Gate6966FreeCard (mx)
open Low6966SharedPrice (coord)
open Gate6966CertCF (cvOf cvOf_le certF certF_bounds certF_class)
open scoped Polynomial BigOperators

theorem sum_tail (lv : Lv) (n : ℕ) (hn : n = lv.length) (L : ℕ) (hL : n ≤ L) (F : ℕ → ℕ)
    (hF : ∀ i, n ≤ i → F i = 0) : ∑ i ∈ Finset.range L, F i = ∑ i ∈ Finset.range n, F i := by
  symm
  apply Finset.sum_subset (Finset.range_mono hL)
  intro i _ hi
  exact hF i (by simpa using hi)

theorem hI_of_free (G : Gt) (hG : G.Ok) (hx : 3 * G.xt ≤ G.xj) (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt)
    (r0 : ℕ) (ws : List ℕ) (lv : Lv) (n : ℕ) (hn : n = lv.length) (hr0 : r0 + ws.length ≤ n + 1)
    (hall : allOK G r0 ws lv 0 n = true)
    (ρ0 amax : ℕ) (hρ0 : 0 < ρ0) (hru : ρ0 + amax ≤ n + 1)
    (hamax : ∀ a, a * G.lb ≤ 4012 → a * G.lj ≤ 1650 → a * G.lt ≤ 550 → a ≤ amax)
    (hS0 : G.tsep ≤ G.sc * G.A * VD)
    (hS1 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 ≤ (G.sc * G.A * VD - G.tsep) * ρ0)
    (hS2 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 * ρ0 +
        VD * (2 * TT G 4012 1650 550 4012 1650 550 + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ0 * ρ0))
    (i : ℕ) (x : Fin 3 → ℕ) (hxl : G.lb ≤ x 0 ∧ G.lj ≤ x 1 ∧ G.lt ≤ x 2) (a : ℕ) (η : Fin 3 → ℕ)
    (hfit : ∀ k, a * x k + η k ≤ Bof lv i k) (hv : η 2 ≤ η 0 ∧ 3 * η 2 ≤ η 1 ∧ η 1 ≤ 2 * η 0 + η 2)
    (hfree : Wof lv i < Gate6966Shape.free (fun k => Bof lv i k - (a * x k + η k))) :
    a < i + 1 ∧ lhsV (mkPr G (i + 1) a (cvOf r0 ws (i + 1) a).1 (cvOf r0 ws (i + 1) a).2 (Wof lv i)
        (Bof lv i 0) (Bof lv i 1) (Bof lv i 2)) (Bof lv i 0 - a * G.lb - η 0) (Bof lv i 1 - a * G.lj - η 1)
        (Bof lv i 2 - a * G.lt - η 2) (η 0) (η 1) (η 2) ≤
      (mkPr G (i + 1) a (cvOf r0 ws (i + 1) a).1 (cvOf r0 ws (i + 1) a).2 (Wof lv i)
        (Bof lv i 0) (Bof lv i 1) (Bof lv i 2)).rhs := by
  by_cases hi : i < n
  · have hok := allOK_get G r0 ws lv n hall i hi
    unfold okAt at hok
    have hB0 : Bof lv i 0 = (lv.getD i dflt).1 := rfl
    have hB1 : Bof lv i 1 = (lv.getD i dflt).2.1 := rfl
    have hB2 : Bof lv i 2 = (lv.getD i dflt).2.2.1 := rfl
    have hfree' : (lv.getD i dflt).2.2.2 < Gate6966Shape.free
        (fun k => ![(lv.getD i dflt).1, (lv.getD i dflt).2.1, (lv.getD i dflt).2.2.1] k - (a * x k + η k)) := hfree
    have hfit' : ∀ k, a * x k + η k ≤ ![(lv.getD i dflt).1, (lv.getD i dflt).2.1, (lv.getD i dflt).2.2.1] k := hfit
    obtain ⟨hlt, c, hc, hle⟩ := level_sound G hG hx hpos (i + 1) _ _ _ _ 80 (fun a => some (cvOf r0 ws (i + 1) a))
      (fun a c hc => by simp only [Option.some.injEq] at hc; subst hc; exact cvOf_le r0 ws (i + 1) a) hok x hxl a η
      hfit' hv hfree'
    simp only [Option.some.injEq] at hc
    subst hc
    exact ⟨hlt, by simpa [Wof, hB0, hB1, hB2] using hle⟩
  · have hge : n ≤ i := by omega
    have hd : lv.getD i dflt = dflt := by
      rw [List.getD_eq_default]; omega
    have hB0 : Bof lv i 0 = 4012 := by unfold Bof; simp only [hd]; rfl
    have hB1 : Bof lv i 1 = 1650 := by unfold Bof; simp only [hd]; rfl
    have hB2 : Bof lv i 2 = 550 := by unfold Bof; simp only [hd]; rfl
    have hW0 : Wof lv i = 0 := by unfold Wof; simp only [hd]; rfl
    have f0 := hfit 0
    have f1 := hfit 1
    have f2 := hfit 2
    rw [hB0] at f0
    rw [hB1] at f1
    rw [hB2] at f2
    have l0 := Nat.mul_le_mul_left a hxl.1
    have l1 := Nat.mul_le_mul_left a hxl.2.1
    have l2 := Nat.mul_le_mul_left a hxl.2.2
    have ha : a ≤ amax := hamax a (by nlinarith) (by nlinarith) (by nlinarith)
    have hlt : a < i + 1 := by omega
    refine ⟨hlt, ?_⟩
    rw [hB0, hB1, hB2, hW0]
    have hρ : ρ0 ≤ i + 1 - a := by omega
    have key := tail_ok G hG hx (i + 1 - a) (cvOf r0 ws (i + 1) a).1 (cvOf r0 ws (i + 1) a).2 a amax ρ0 hρ hρ0
      (by have := cvOf_le r0 ws (i + 1) a; omega)
      (cvOf_tail r0 ws (i + 1) a amax (by omega) ha hlt) ha hS0 hS1 hS2
      (yb := 4012 - a * G.lb - η 0) (yj := 1650 - a * G.lj - η 1) (yt := 550 - a * G.lt - η 2)
      (hb := η 0) (hj := η 1) (ht := η 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [lhsV_eq]
    exact key

theorem hsum_of (lv : Lv) (n : ℕ) (hn : n = lv.length) (hL : n ≤ Gate6966Final.levelCount)
    (hs : (∑ i ∈ Finset.range n, lsum lv i) < Low6966Prices.layerNeed) :
    ∑ i ∈ Finset.range Gate6966Final.levelCount,
      (Low6966Prices.symbolCount - Gate6966Box.ambCount (Bof lv i 0) (Bof lv i 1) (Bof lv i 2) + Wof lv i) <
      Low6966Prices.layerNeed := by
  rw [sum_tail lv n hn _ hL]
  · have : ((∑ i ∈ Finset.range n, (Low6966Prices.symbolCount - Gate6966Box.ambCount (Bof lv i 0) (Bof lv i 1)
        (Bof lv i 2) + Wof lv i) : ℕ) : ℤ) ≤ ∑ i ∈ Finset.range n, ((Low6966Prices.symbolCount : ℤ) -
        ambLB (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 + (Wof lv i : ℤ)) := by
      push_cast
      apply Finset.sum_le_sum
      intro i _
      have h1 := ambLB_le (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1
      have h2 := Gate6966Amb.amb_le (Bof lv i 0) (Bof lv i 1) (Bof lv i 2)
      have e : Gate6966Box.ambCount (Bof lv i 0) (Bof lv i 1) (Bof lv i 2) =
          Gate6966Box.ambCount (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 := rfl
      rw [e] at h2 ⊢
      push_cast [Nat.cast_sub h2]
      linarith
    have h3 := lt_of_le_of_lt this hs
    exact_mod_cast h3
  · intro i hi
    have hd : lv.getD i dflt = dflt := by rw [List.getD_eq_default]; omega
    have hB0 : Bof lv i 0 = 4012 := by unfold Bof; simp only [hd]; rfl
    have hB1 : Bof lv i 1 = 1650 := by unfold Bof; simp only [hd]; rfl
    have hB2 : Bof lv i 2 = 550 := by unfold Bof; simp only [hd]; rfl
    have hW0 : Wof lv i = 0 := by unfold Wof; simp only [hd]; rfl
    rw [hB0, hB1, hB2, hW0, Gate6966Amb.amb_full 4012 1650 550 le_rfl le_rfl le_rfl]
    simp

theorem price_T {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f : Row 4} {l : ℕ}
    (hm : Low6966Prices.Messages w Γ s) (hf : Low6966Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6966Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (htf : 3 * (shape f).t + 3 ≤ (shape f).j ∧ (shape f).j + 1 ≤ (shape f).b)
    (G : Gt) (hG : G.Ok) (hlift : G.lift = false) (hsc : G.sc = 1920)
    (hxt : 3 * G.xt ≤ G.xj) (hbh : G.xj + 1 ≤ G.xb) (hjh : 2 ≤ G.xj)
    (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (k h1 h2 hx1 hx2 : ℕ) (hk : Low6966Prices.taylorLength - 4 = k)
    (hh1 : (Low6966Prices.bentLift 133446 ⟨G.xb, G.xj, G.xt⟩).2 = h1)
    (hh2 : (Low6966Prices.bentLift 133447 ⟨G.xb, G.xj, G.xt⟩).2 = h2)
    (hx1' : (Low6966Prices.bentLift k (shape f)).2 = hx1) (hx2' : (Low6966Prices.bentLift (k + 1) (shape f)).2 = hx2)
    (hM : ∀ i k', (tpOf ⟨G.xb, G.xj, G.xt⟩ 133446 h1 h2).ray i k' = G.mat i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (tpOf (shape f) k hx1 hx2).ray i k' ≤ num * (tpOf ⟨G.xb, G.xj, G.xt⟩ 133446 h1 h2).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (r0 : ℕ) (ws : List ℕ) (ht : Gate6966ClassTable.tableOK r0 ws = true) (lv : Lv) (n : ℕ) (hn : n = lv.length)
    (hr0 : r0 + ws.length ≤ n + 1) (hL : n ≤ Gate6966Final.levelCount)
    (hall : allOK G r0 ws lv 0 n = true)
    (ρ0 amax : ℕ) (hρ0 : 0 < ρ0) (hru : ρ0 + amax ≤ n + 1)
    (hamax : ∀ a, a * G.lb ≤ 4012 → a * G.lj ≤ 1650 → a * G.lt ≤ 550 → a ≤ amax)
    (hS0 : G.tsep ≤ G.sc * G.A * VD)
    (hS1 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 ≤ (G.sc * G.A * VD - G.tsep) * ρ0)
    (hS2 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 * ρ0 +
        VD * (2 * TT G 4012 1650 550 4012 1650 550 + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ0 * ρ0))
    (hs : (∑ i ∈ Finset.range n, lsum lv i) < Low6966Prices.layerNeed) :
    Γ.card ≤ Ax + Low6966SharedPrice.additiveBase (shape f) l + Low6966SharedPrice.nonsharedFee (shape f) l := by
  have hf0 : f ≠ 0 := hf.1.ne_zero
  have htpos : 0 < f.degreeOf 3 := by
    have : (shape f).t = f.degreeOf 3 := rfl
    omega
  have hnd : ¬ f ∣ K1_13_6.separant f := KoalaFarBridge.separant_proper hf0 htpos hchar
  have sb := KoalaFarBridge.separant_box f
  set qs : Shape := ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩ with hqs
  have hsep : G.sep = (mx (G.xb - 1) (G.xj - 3), G.xj - 3, Gate6966FreeCard.mn (G.xt - 1) ((G.xj - 3) / 3)) := by
    simp only [Gt.sep, hlift, hB, hJ, hT, Bool.cond_false]
  have hbs : InBox (shape (K1_13_6.separant f)) qs := by
    refine ⟨?_, ?_, ?_⟩
    · have := sb.1
      simp only [hqs, hsep, Gate6966FreeCard.mx_eq]
      exact this.trans ((Nat.sub_le_sub_right hhi.1 1).trans (le_max_left _ _))
    · have := sb.2.1
      simp only [hqs, hsep]
      exact this.trans (Nat.sub_le_sub_right hhi.2.1 3)
    · have := sb.2.2
      simp only [hqs, hsep, Gate6966FreeCard.mn_eq]
      refine this.trans (le_min (Nat.sub_le_sub_right hhi.2.2 1) ?_)
      refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
      have h5 := htf.1; have h6 := hhi.2.1; show ((shape f).t - 1) * 3 ≤ G.xj - 3; omega
  have hcs : Low48BentLattice.Chamber (qs, 0) := by
    refine ⟨?_, ?_, Nat.zero_le _⟩
    · simp only [hqs, hsep, Gate6966FreeCard.mx_eq]; exact le_max_right _ _
    · simp only [hqs, hsep, Gate6966FreeCard.mn_eq]
      have := Nat.min_le_right (G.xt - 1) ((G.xj - 3) / 3)
      omega
  have hxl : G.lb ≤ coord (shape f) 0 ∧ G.lj ≤ coord (shape f) 1 ∧ G.lt ≤ coord (shape f) 2 := hlo
  have hsum := hsum_of lv n hn hL hs
  refine Gate6966Final.two_cut_price_tilted hm hf hon hl hproper (by exact ⟨htf.1, htf.2⟩) qs hbs hcs hnd Ax (Bof lv) (Wof lv)
    (certF r0 ws) (fun r a => (certF_bounds r0 ws r a).1) (fun r a => (certF_bounds r0 ws r a).2.1)
    (fun r a => (certF_bounds r0 ws r a).2.2) ?_ hsum
  intro i _ a η hfit hv hng
  by_contra hfree
  push_neg at hfree
  obtain ⟨hlt, hI⟩ := hI_of_free G hG hxt hpos r0 ws lv n hn hr0 hall ρ0 amax hρ0 hru hamax hS0 hS1 hS2 i
    (fun k => coord (shape f) k) hxl a η hfit hv hfree
  have hc : (cvOf r0 ws (i + 1) a).1 ≤ 2 * (i + 1 - a) := cvOf_le r0 ws (i + 1) a
  have hr := rhs_le_tilted f G hG hlift hsc hxt hbh hjh hlo hhi htf k h1 h2 hx1 hx2 hk hh1 hh2 hx1' hx2' hM num den Ax hden
    hθ hA qs hqs (i + 1) a _ _ (Wof lv i) (Bof lv i) η hlt hc hI
  exact hng ⟨hlt, certF_class ht hlt, hr⟩

end Gate6966Cell

end Merged_Gate6966GateT

end Merged_Gate6966GateT

-- merged module Gate6966ThetaOrd
section Merged_Gate6966ThetaOrd

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option Elab.async false

namespace Gate6966Bilinear

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

end Gate6966Bilinear

end Merged_Gate6966ThetaOrd
