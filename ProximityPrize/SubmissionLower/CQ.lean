import ProximityPrize.SubmissionLower.O
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option autoImplicit true
section
namespace aSg
noncomputable section
open Polynomial P0
private theorem gBm (q:ℕ) (a :K[X]) (β:Fin 2→K[X]) :
  NJ q a β=Aj.NJ q a β:= by
 delta NJ Aj.NJ P0.jH K1.jH P0.seed K1.seed P0.twist K1.twist P0.p K1.p
  P0.nC K1.nC P0.K K1.K
 rfl
private theorem fVQ (q:ℕ) (u:e9) (S:Finset I) (U V W:nC) :
  ad9 q u S U V W=Aj.ad9 q u S U V W:= by
 delta ad9 Aj.ad9 P0.node K1.node P0.e9 K1.e9 P0.I K1.I
  P0.nC K1.nC P0.K K1.K
 rfl
private theorem dNF (q:ℕ) (U V:nC) :
  ajp q U V=Aj.ajp q U V:= by
 delta ajp Aj.ajp P0.seed K1.seed P0.sZ K1.sZ
  P0.nC K1.nC P0.kB K1.kB P0.K K1.K
 rfl
open private Aj.aQO from ProximityPrize.SubmissionLower.B
private theorem eEw :
  NJ P0.p=(P0.JO:K[X]→(Fin 2→K[X])→nC) := by
 unfold NJ P0.JO
 rfl
theorem bxJ (a :K[X]) (β:Fin 2→K[X]) :
  P0.JO a β=K1.JO a β:= by
 calc
  P0.JO a β=NJ P0.p a β:=congrFun (congrFun eEw.symm a) β
  _=Aj.NJ P0.p a β:=gBm P0.p a β
  _=Aj.NJ K1.p a β:=congrArg (fun q=>Aj.NJ q a β) (show P0.p=K1.p from rfl)
  _=K1.JO a β:=congrFun (congrFun Aj.aQO a) β
theorem c73 (u:e9) (S:Finset I) (U V W:nC) :
  ake u S U V W=Aj.ad9 K1.p u S U V W:= by
 calc
  _=ad9 P0.p u S U V W:= by delta P0.ake ad9; rfl
  _=Aj.ad9 P0.p u S U V W:=fVQ P0.p u S U V W
  _=Aj.ad9 K1.p u S U V W :=
    congrArg (fun q=>Aj.ad9 q u S U V W) (show P0.p=K1.p from rfl)
theorem bC4 (U V:nC) :Xb U V=K1.Xb U V:= by
 calc
  _=ajp P0.p U V:= by delta P0.Xb ajp; rfl
  _=Aj.ajp P0.p U V:=dNF P0.p U V
  _=Aj.ajp K1.p U V:=congrArg (fun q=>Aj.ajp q U V) (show P0.p=K1.p from rfl)
  _ = _:= by delta Aj.ajp K1.Xb; rfl
end
end aSg
end
section
set_option backward.isDefEq.respectTransparency false
namespace aSg
noncomputable section
open Polynomial P0 gR ProximityPrize.Benchmark

private theorem db1 (U V P Q:nC) :
  Z4 U V P Q=K1.Z4 U V P Q:= by
 delta P0.Z4 K1.Z4
 rfl
private theorem cti (b:K[X]) (α:Fin 2→K[X]) :
  J9 b α=K1.J9 b α:= by
 delta P0.J9 K1.J9 P0.jH K1.jH P0.seed K1.seed
 rfl
end
end aSg
end
section
namespace dnH
open P0 Finset
open wT (V)
private def po (B s t i:ℕ) :ℕ :=
 ∑ j∈range (B+1 - i),(s+1 - i)*(t+1 - j)
private def oN (B s t i:ℕ) :ℕ :=
 ∑ j∈range (B+1 - i),(i+j)*((s+1 - i)*(t+1 - j))
private def count (B s t:ℕ) :ℕ := ∑ i∈range (B+1),po B s t i
private def cV (B s t:ℕ) :ℕ := ∑ i∈range (B+1),oN B s t i
private def xq (m s t i:ℕ) :ℕ :=
 ∑ j∈range (m - i),(m - i - j)*(s+1 - i)*(t+1 - j)
private theorem bTL (D w B s t:ℕ) (hB:w*B≤D + 1) :
  V D w B s t+w*cV B s t=(D + 1)*count B s t:= by
 unfold V count cV po oN
 simp only [Finset.mul_sum,← Finset.sum_add_distrib]
 refine sum_congr rfl fun i hi=>sum_congr rfl fun j hj => ?_
 have hij:i+j≤B:= by
  simp only [mem_range] at hi hj
  omega
 have hw:=(Nat.mul_le_mul_left w hij).trans hB
 calc
  _=((D + 1 - w*(i+j))+w*(i+j))*((s+1 - i)*(t+1 - j)) := by ring
  _ = _:= by rw [Nat.sub_add_cancel hw]
private theorem c6V (E M exceptionFee limit a b:ℕ) (hb:0<b)
  (h:exceptionFee*b^2+5*E*(a*M)^2≤limit*b^2) :
  (exceptionFee :ℚ)+5*((E :ℚ)*(((a :ℚ)/b)*M)^2)≤limit := by
 have hb' : 0<(b:ℚ) := by exact_mod_cast hb
 have h' : (exceptionFee :ℚ)*(b:ℚ)^2+5*(E :ℚ)*((a :ℚ)*M)^2 ≤
    (limit :ℚ)*(b:ℚ)^2 := by exact_mod_cast h
 refine le_of_mul_le_mul_right ?_ (pow_pos hb' 2)
 calc
  _=(exceptionFee :ℚ)*(b:ℚ)^2+5*(E :ℚ)*((a :ℚ)*M)^2 := by
    field_simp
  _≤_:=h'
end dnH
end
