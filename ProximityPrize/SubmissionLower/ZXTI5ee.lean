import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.DB
import ProximityPrize.SubmissionLower.ZNBvygc
import ProximityPrize.SubmissionLower.Z5KYTEa
import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.Zc9uAjc
import ProximityPrize.SubmissionLower.ZTqYzLd
import ProximityPrize.SubmissionLower.Zytxfqb
set_option Elab.async false
section
section
set_option autoImplicit true
namespace qPPBzNd
def value {α:Type} (f :α→ℕ) (xs :List α) (cap:ℕ) :ℕ :=
 xs.foldl (fun n x=>min n (f x)) cap
end qPPBzNd
end
end
section
section
set_option autoImplicit true
namespace q6fWcbc
noncomputable section
open Polynomial MvPolynomial



open dN (GeoField j8)


open scoped BigOperators


local notation "W" => MvPolynomial.weightedTotalDegree
private def center :GeoField :=
 j8 Polynomial.X
end
end q6fWcbc
end
end
section
section
set_option autoImplicit true
namespace qaySLPd
noncomputable section
open Polynomial Finset
open P5 (K p twist)

open P5_7_1
open cu (L FX aZ Jet Equation kr)

open Qv (S4 lX)
open scoped BigOperators
def orient (i:Fin 2) (Q:TopRow) :TopRow :=
 if i=0 then Q else topConjugate Q
def topLabel (i:Fin 2) (z :K) :K :=
 if i=0 then z else twist z
def omitted (i:Fin 2) :Fin 2 :=if i=0 then 1 else 0
def pad (f :Jet) (i:Fin 2) (c:ℕ) (T:TopRow) :Jet :=
  let Q:=topLift (orient i T)
  let vel:Jet:=Polynomial.X
  let ord:Jet:=Polynomial.C (Polynomial.X:Equation)
  let seed :Jet:=Polynomial.C (Polynomial.C (MvPolynomial.X i))
  let num := -(S4 lX f +
    vel*S4 Polynomial.derivative f)
  let sep:=(2 :Jet)*f.derivative
  ∑ e∈Q.support,algebraMap FX Jet (Q.coeff e) *
    seed^(e 0)*ord^(e 1)*vel^(e 2)*num^(e 3)*sep^(c-e 3)
def SupportCaps (B J C U:ℕ) (T:TopRow) :Prop :=
 ∀ e∈T.support,e 1+e 2+e 3≤B∧e 2+2*e 3≤J∧e 3≤C∧e 0≤U
def RS (f :Jet) (S:K[X]) :aZ :=
  f.eval₂ (Polynomial.evalRingHom (MvPolynomial.C (kr S)))
    (MvPolynomial.C (kr S.derivative))
abbrev pe :=MvPolynomial (Fin 2) L
def ConstantFibre (f :Jet) (z :K) (S:K[X]) :Prop :=
  RS f S=0 ∨ ∃ q:pe,Irreducible q ∧
    MvPolynomial.map (algebraMap L FX) q∣RS f S ∧
    MvPolynomial.eval ![algebraMap K L z,(algebraMap K L z)^p] q=0
end
end qaySLPd
end
end
section
set_option autoImplicit true
namespace P6_7_4
noncomputable section
open P6 (I K jG)
open P5_7_2 (A Aux fO ChosenRow NodeUnits jX row terminal O2)
open qMNIwTb (Filed CJ)
open cu (L vP)
open DP (jF zG)
open qQ (zI N5)
def wordLift {u del} (M:jG u del) :I→L:= fun i=>algebraMap K L (M.word i)
structure bkU (b:fO) {u del} (M:jG u del) {Γ}
    (F:P1.bje A M Γ) (rows :vP) where
  gH :Finset K
  paid_bound:gH.card≤(row b).prefixFee
  parents :Finset zI
  geometric : ∀ q∈parents,N5 q
  terminal_pass : ∀ q∈parents,∀ P∈rows (terminal b).shape (O2 (terminal b).shape),
    P∈q.asIdeal
  Eh : ∀ γ∈Γ,γ∈gH ∨ ∃ q∈parents,P6_7.axy M F q γ
def PaddedFree :Prop :=
  ∀ (b:fO),2≤b.val → ∀ (h:ℕ),(jX b).lo≤h→h≤(jX b).hi →
    ∀ (a :Aux),Filed b false a→CJ b false a →
      ∀ (D:jF h),NodeUnits D → ∀ (Crt:zG D) (word:I→L),
        Nonempty (ChosenRow Crt word a.dI a.shape)
end
end P6_7_4
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d:=0x15f3700000dc20000d00004ed94300031a90002f80003ecd6080027f350026e0001ff709500149cf401478000d367bb0008aa65008ce0004d5d6270033c510035f8001a1a7e88011e15c0132e00084d7b14005d74280677800283e652801d28b40216c
local notation "q!" k:arg n:arg=>block 136 30 (128+8*k) n=unpack (d >>> (90*k))
private theorem tE {x y:qKlO94b.Totals} (h:(x.r.beq y.r&&x.m.beq y.m&&x.e.beq y.e)=true) :x=y:= by
 simp only [Bool.and_eq_true] at h
 cases x; cases y; simp only [qKlO94b.Totals.mk.injEq]
 exact ⟨Nat.eq_of_beq_eq_true h.1.1,Nat.eq_of_beq_eq_true h.1.2,Nat.eq_of_beq_eq_true h.2⟩
set_option quotPrecheck false in
local notation "qk!"=>tE (by decide +kernel)
private theorem b0:q! 0 8:=qk!
private theorem b1 :q! 1 8:=qk!
private theorem b2 :q! 2 8:=qk!
private theorem b3:q! 3 8:=qk!
private theorem b4 :q! 4 8:=qk!
private theorem b5:q! 5 8:=qk!
private theorem b6:q! 6 8:=qk!
private theorem b7:q! 7 8:=qk!
private theorem b8:q! 8 4 :=qk!
theorem p1_2 :block 136 30 128 68=sumPacked d 9:=join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (b8))))))))
end qKlO94b
end
