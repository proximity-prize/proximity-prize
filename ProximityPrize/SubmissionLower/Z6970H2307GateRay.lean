import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.Gate6966Tail

set_option autoImplicit false
set_option Elab.async false

namespace Low6969GateBilinear
open K1_13

def Nt (B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 : ℤ) : ℤ :=
  (-960*(2*J2*h1*h2 - 2*J2*h1*k*t + J2*h1*k - 2*J2*h1*t - J2*h1 - 2*J2*h2*k*t + J2*h2*k - 2*J2*h2 - 2*J2*k^2*t - 2*J2*k*t - 4*J2*k - 2*J2 - 2*h1*h2*t + 3*h1*k*t^2 - 2*h1*k*t + 3*h1*t^2 + 3*h2*k*t^2 - 2*h2*k*t + 2*h2*t + 3*k^2*t^2 + 3*k*t^2 + 4*k*t + 2*t - 4)) * x1 * y2
  + (960*(J2^2*h1*k + J2^2*h1 + J2^2*h2*k + J2^2*k^2 + J2^2*k + 2*J2*h1*h2 - 6*J2*h1*k*t + 2*J2*h1*k - 6*J2*h1*t - 6*J2*h2*k*t + 2*J2*h2*k - 2*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 4*J2*k - 2*J2 - 6*h1*h2*t + 4*h1*h2 + 9*h1*k*t^2 - 6*h1*k*t + 9*h1*t^2 - 4*h1 + 9*h2*k*t^2 - 6*h2*k*t + 6*h2*t - 4*h2 + 9*k^2*t^2 + 9*k*t^2 + 12*k*t + 6*t + 4)) * x1 * y3
  + (-960*(2*J2*h1*h2 - 2*J2*h1*k*t + J2*h1*k - 2*J2*h1*t - J2*h1 - 2*J2*h2*k*t + J2*h2*k - 2*J2*h2 - 2*J2*k^2*t - 2*J2*k*t - 4*J2*k - 2*J2 - 2*h1*h2*t + 3*h1*k*t^2 - 2*h1*k*t + 3*h1*t^2 + 3*h2*k*t^2 - 2*h2*k*t + 2*h2*t + 3*k^2*t^2 + 3*k*t^2 + 4*k*t + 2*t - 4)) * x2 * y1
  + (480*(-4*B1*h1*h2 + 4*B1*h1*k*t - 2*B1*h1*k + 4*B1*h1*t + 2*B1*h1 + 4*B1*h2*k*t - 2*B1*h2*k + 4*B1*h2 + 4*B1*k^2*t + 4*B1*k*t + 8*B1*k + 4*B1 + 6*J2*h1*h2 - 6*J2*h1*k*t + 3*J2*h1*k - 6*J2*h1*t - 3*J2*h1 - 6*J2*h2*k*t + 3*J2*h2*k - 6*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 12*J2*k - 6*J2 - 4*h1*h2*t - 2*h1*h2 + 7*h1*k*t^2 - 4*h1*k*t + 7*h1*t^2 + 2*h1 + 7*h2*k*t^2 - 4*h2*k*t + 4*h2*t + 2*h2 + 7*k^2*t^2 + 7*k*t^2 + 8*k*t + 4*t - 12)) * x2 * y2
  + (-480*(-4*B1*J2*h1*k - 4*B1*J2*h1 - 4*B1*J2*h2*k - 4*B1*J2*k^2 - 4*B1*J2*k - 4*B1*h1*h2 + 12*B1*h1*k*t - 4*B1*h1*k + 12*B1*h1*t + 12*B1*h2*k*t - 4*B1*h2*k + 4*B1*h2 + 12*B1*k^2*t + 12*B1*k*t + 8*B1*k + 4*B1 + 3*J2^2*h1*k + 3*J2^2*h1 + 3*J2^2*h2*k + 3*J2^2*k^2 + 3*J2^2*k + 4*J2*h1*h2 - 14*J2*h1*k*t + 4*J2*h1*k - 14*J2*h1*t - 14*J2*h2*k*t + 4*J2*h2*k - 4*J2*h2 - 14*J2*k^2*t - 14*J2*k*t - 8*J2*k - 4*J2 - 8*h1*h2*t + 4*h1*h2 + 15*h1*k*t^2 - 8*h1*k*t + 15*h1*t^2 - 4*h1 + 15*h2*k*t^2 - 8*h2*k*t + 8*h2*t - 4*h2 + 15*k^2*t^2 + 15*k*t^2 + 16*k*t + 8*t + 4)) * x2 * y3
  + (960*(J2^2*h1*k + J2^2*h1 + J2^2*h2*k + J2^2*k^2 + J2^2*k + 2*J2*h1*h2 - 6*J2*h1*k*t + 2*J2*h1*k - 6*J2*h1*t - 6*J2*h2*k*t + 2*J2*h2*k - 2*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 4*J2*k - 2*J2 - 6*h1*h2*t + 4*h1*h2 + 9*h1*k*t^2 - 6*h1*k*t + 9*h1*t^2 - 4*h1 + 9*h2*k*t^2 - 6*h2*k*t + 6*h2*t - 4*h2 + 9*k^2*t^2 + 9*k*t^2 + 12*k*t + 6*t + 4)) * x3 * y1
  + (-480*(-4*B1*J2*h1*k - 4*B1*J2*h1 - 4*B1*J2*h2*k - 4*B1*J2*k^2 - 4*B1*J2*k - 4*B1*h1*h2 + 12*B1*h1*k*t - 4*B1*h1*k + 12*B1*h1*t + 12*B1*h2*k*t - 4*B1*h2*k + 4*B1*h2 + 12*B1*k^2*t + 12*B1*k*t + 8*B1*k + 4*B1 + 3*J2^2*h1*k + 3*J2^2*h1 + 3*J2^2*h2*k + 3*J2^2*k^2 + 3*J2^2*k + 4*J2*h1*h2 - 14*J2*h1*k*t + 4*J2*h1*k - 14*J2*h1*t - 14*J2*h2*k*t + 4*J2*h2*k - 4*J2*h2 - 14*J2*k^2*t - 14*J2*k*t - 8*J2*k - 4*J2 - 8*h1*h2*t + 4*h1*h2 + 15*h1*k*t^2 - 8*h1*k*t + 15*h1*t^2 - 4*h1 + 15*h2*k*t^2 - 8*h2*k*t + 8*h2*t - 4*h2 + 15*k^2*t^2 + 15*k*t^2 + 16*k*t + 8*t + 4)) * x3 * y2
  + (480*(-12*B1*J2*h1*k - 12*B1*J2*h1 - 12*B1*J2*h2*k - 12*B1*J2*k^2 - 12*B1*J2*k - 12*B1*h1*h2 + 36*B1*h1*k*t - 12*B1*h1*k + 36*B1*h1*t + 36*B1*h2*k*t - 12*B1*h2*k + 12*B1*h2 + 36*B1*k^2*t + 36*B1*k*t + 24*B1*k + 12*B1 + 7*J2^2*h1*k + 7*J2^2*h1 + 7*J2^2*h2*k + 7*J2^2*k^2 + 7*J2^2*k + 8*J2*h1*h2 - 30*J2*h1*k*t + 8*J2*h1*k - 30*J2*h1*t - 30*J2*h2*k*t + 8*J2*h2*k - 8*J2*h2 - 30*J2*k^2*t - 30*J2*k*t - 16*J2*k - 8*J2 - 12*h1*h2*t + 4*h1*h2 + 27*h1*k*t^2 - 12*h1*k*t + 27*h1*t^2 - 4*h1 + 27*h2*k*t^2 - 12*h2*k*t + 12*h2*t - 4*h2 + 27*k^2*t^2 + 27*k*t^2 + 24*k*t + 12*t + 4)) * x3 * y3

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

def tpOf (p : Shape) (k h1 h2 : ℕ) : TP :=
  ⟨((p.b - 1 : ℕ) : ℤ), ((p.j - 2 : ℕ) : ℤ), p.t, k, h1, h2⟩

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

def opOf (z w : Shape) : OP := ⟨z.b, z.j, z.t, w.b, w.j, w.t⟩

end Low6969GateBilinear

namespace Low6969GateCell
export Gate6966Cell (Gt)

def Gt.mat (G : Gt) (i k : Fin 3) : ℤ :=
  ![![(G.m00 : ℤ), G.m01, G.m02], ![(G.m01 : ℤ), G.m11, G.m12], ![(G.m02 : ℤ), G.m12, G.m22]] i k

end Low6969GateCell
