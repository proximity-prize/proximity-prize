import ProximityPrize.SubmissionLower.B6
set_option Elab.async false
set_option maxRecDepth 12000
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace P4
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I e9 node p blockLength k kB nC aB8 ayo
 sZ aiE vn seed jH twist uO Ox Xb
 JO J9 Z4 ake)
abbrev a08:=P1.a08
abbrev target :a08:=⟨179925,0x1412b9bf,0x40000000,2388,0x3a8027d1a253b7d,0x1e2ff3df26f7ba⟩
abbrev dw:=target.dw
abbrev ajO:ℤ:=target.aou
abbrev t:ℕ:=blockLength - dw
abbrev L:ℕ:=dw - k
abbrev DY:ℕ:=t+1 - L - 2
def So (u:e9) :=AI p node (u 0) (u 1) L t
def R5 (u:e9) :=Bx.ay6 (So u)
structure qo (u:e9) where
 a :ℕ
 b:ℕ
 c:ℕ
 ab:a≤b
 active :b≤t
 inactive :t<c
 top:c≤k
 degreeSum:a+b+c=2*k+2
 nullitySum:R5 u+a+b=2*(t+1)
 level :kL.aKl
   (fun s j=>algebraMap K[X] kB (Principal.P8 p node (u 0) (u 1) s j))
   k a b c
def qo.height {u:e9} (T:qo u) :=(k+1) - T.c
abbrev FJ:=P1.FJ
abbrev FJ.iF := @P1.FJ.iF
abbrev FJ.label := @P1.FJ.label
abbrev jG:=FJ DY
abbrev jG.iF {u deleted} (M:jG u deleted) :=FJ.iF M
abbrev jG.label {u deleted} (M:jG u deleted) :=FJ.label M
end
end P4
end
section
namespace Ds
noncomputable section
open Polynomial
open P1 (k dw)
open aR (ao af Shape cK wU qE)
open scoped BigOperators
abbrev gZ:ℕ:=k - 1+P1.ajO.toNat
abbrev bf :ℕ:=gZ+1
def wD {ι:Type*} (a :ι→Shape) (T:Finset ι) :Shape :=
 ⟨∑ i∈T,(a i).b,∑ i∈T,(a i).j,∑ i∈T,(a i).t⟩
abbrev Valid :=FI.Valid
abbrev oL:=FI.oL
inductive Bank where
 | ag
 | dB
 deriving DecidableEq
def Bank.m:Bank→ℕ
 | .ag=>2320
 | .dB=>3600
def Bank.box :Bank→Shape
 | .ag=>⟨3096,1295, 378⟩
 | .dB=>⟨4788,2052,595⟩
def Bank.cutoff (b:Bank) :ℕ:=b.m*dw - 1
def symbols (c:Shape) :ℕ :=
  ∑ z∈Finset.range (min c.t (min c.b (c.j/3))+1),
    ∑ y∈Finset.range (min (c.b - z) ((c.j-3*z)/2)+1),
      ∑ x∈Finset.range (min (c.b - z - y) (c.j-3*z - 2*y)+1),
        (c.b - z - y - x+1)
structure aw1 where
 common :af 3
 residual:af 3
 common_ne :common≠0
 residual_ne :residual≠0
 common_total:common.totalDegree≤3284
 common_index :qE common≤1120
 residual_total:residual.totalDegree≤409200000
 residual_index :qE residual≤129000000
def aw1.bqU (E :aw1) (S:ao[X]) :Prop :=
 cK E.common S=0∨wU E.residual S 40517
def wP (p q r s :Shape) :ℤ :=
 let Δ:=aR.gI
 Δ (Δ (Δ (Δ aR.Dn p) q) r) s oL
def LN (L:ℕ) (p:Shape) :Shape :=
 let j:=2+(L-4)*(p.j+2)
 ⟨1+(L-4)*p.b,j,min (1+(L-4)*(p.t+2)) (j/2)⟩
end
end Ds
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace dnM
noncomputable section
open Polynomial Matrix gR P1
open ProximityPrize.Benchmark
private theorem a3F (P:nC) (a γ:K) :
  (vn P γ).eval a=(P.eval (C a)).eval γ:= by
 simpa only [vn,Polynomial.coe_evalRingHom,Polynomial.eval_C] using
  (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (C a) (p:=P))
private theorem duL (G:K[X]) (γ:K) :
  vn (G.map C) γ=G:= by
 rw [vn,Polynomial.map_map]
 have h: (Polynomial.evalRingHom γ).comp C=RingHom.id K:= by
  ext a
  simp
 rw [h,Polynomial.map_id]
private theorem cG9 (U V:K[X]) (hV:V≠0) (S:Finset I)
  (hroots : ∀ i∈S,(GCDMonoid.gcd U V).eval (node i)=0)
  (hcard:S.card=(GCDMonoid.gcd U V).natDegree) :
  aiE (mL node S) U V:= by
 have hG:GCDMonoid.gcd U V≠0:=gcd_ne_zero_of_right hV
 have hdiv :=kL.bsf node IRSProfile.domain.injective S _ hroots
 have hassoc:=Polynomial.associated_of_dvd_of_natDegree_le hdiv hG
  (by rw [ZQ,hcard])
 exact ⟨(S8 node S).ne_zero,hdiv.trans (gcd_dvd_left U V),
  hdiv.trans (gcd_dvd_right U V),fun H hHU hHV=>(dvd_gcd hHU hHV).trans hassoc.dvd'⟩
private theorem b7E {P:nC} {G:K[X]} (γ:K) (h:G.map C∣P) :
  G∣vn P γ:= by
 have h' := map_dvd (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) h
 change vn (G.map C) γ∣vn P γ at h'
 rwa [duL] at h'
end
end dnM
end
