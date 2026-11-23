import ProximityPrize.SubmissionLower.CJ
set_option Elab.async false
open _root_ renaming Bool.cond_eq_ite→nq,Nat.add→aU,Nat.blt→lJ,Nat.div→lV,Nat.mul→c9,Nat.sub→cy
set_option autoImplicit true
section
namespace abF.Compact
open GI
open private unpack Xy aph from ProximityPrize.SubmissionLower.CJ
private def ajv (x :Nat) :Nat :=
 let q:=aU (c9 2 x) 15
 let t:=aU (c9 q x) 30
 lV (aU (c9 t x) 25) 72
private theorem bde (y z k :Nat) (hk :k<36) (h:z=36*y+k) :y/2=z/72 := by omega
private theorem dV5 (q r :Nat) (hr :r<6) :
   (q*(q*(12*q+21+6*r)+11+r*(7+r))+2+r*(r+1))/2 =
     ajv (6*q+r+1) := by
 change _=(((2*(6*q+r+1)+15)*(6*q+r+1)+30)*(6*q+r+1)+25)/72
 interval_cases r
 · apply bde _ _ 0 (by decide); ring
 · apply bde _ _ 17 (by decide); ring
 · apply bde _ _ 16 (by decide); ring
 · apply bde _ _ 9 (by decide); ring
 · apply bde _ _ 8 (by decide); ring
 · apply bde _ _ 25 (by decide); ring
private theorem boX (u:Nat) :CY u=ajv u:= by
 cases u with
 | zero=>rfl
 | succ n =>
   simp only [CY,Nat.beq_eq_true_eq,Nat.succ_ne_zero,ite_false,Nat.succ_sub_one]
   have e :6*(n/6)+n%6+1=n+1 := by omega
   simpa only [e] using dV5 (n/6) (n%6) (Nat.mod_lt _ (by decide))
private theorem ab0 (a b:Nat) :cy a (cy a b)=min a b :=
 Nat.sub_sub_eq_min a b
private def aaj (d u:Nat) :Nat :=
 bif Nat.ble u (aU d 1) then ajv u else
  let v :=cy u (cy u (aU (c9 3 d) 1))
  let twoD:=c9 2 d
  let first:=aU (ajv v) (ajv (cy v (aU twoD 3)))
  let second:=aU first (ajv (cy v (aU twoD 4)))
  let pos :=aU second (ajv (cy v (aU twoD 5)))
  let lower :=aU (ajv (cy v (aU d 1))) (ajv (cy v (aU d 2)))
  let neg:=aU lower (ajv (cy v (aU d 3)))
  cy pos neg
private theorem agY (d u:Nat) :JY d u=aaj d u:= by
 simp only [aaj,nq,Nat.ble_eq,ab0]
 change JY d u=if u≤d+1 then ajv u else
  let v :=min u (3*d+1)
  (ajv v+ajv (v-(2*d+3))+ajv (v-(2*d+4))+ajv (v-(2*d+5))) -
    (ajv (v-(d+1))+ajv (v-(d+2))+ajv (v-(d+3)))
 simp (disch:=omega) only [JY,boX]
private def Zb (d u r :Nat) :Nat :=
 bif lJ d r then 0 else aaj (cy d r) u
private theorem am7 (d u r :Nat) :RL d u r=Zb d u r := by
 simp only [RL,Zb,agY,nq,Nat.blt_eq]
 rfl
private def anq (s j a b c:Nat) :Nat :=
 let weight:=aU (aU a b) (c9 3 c)
 let bc:=aU b c
 let sc:=aU (aU s a) (c9 4 c)
 bif ((lJ 1650 weight) || (lJ 550 bc) || (lJ (aU j 1) c) || (lJ 4649 sc)) then 0 else
 let d:=cy 1650 weight
 let l:=cy 1650 (aU (aU j (c9 3 b)) (c9 2 c))
 let u:=cy 1651 (c9 3 bc)
 let o:=cy 4650 (aU (aU (aU s j) (c9 2 b)) (c9 3 c))
 let r :=aU (cy d (cy d (lV (cy 4649 sc) 4))) 1
 let origO:=cy 4650 (aU s j)
 let rr :=aU (lV (cy 4649 s) 4) 1
 let basePos :=aU 125576826 (Zb 1650 (cy origO (c9 3 rr)) rr)
 let baseNeg:=aU (ajv origO) (Zb 1650 (cy 1650 j) rr)
 let base :=cy basePos baseNeg
 let pos :=aU (aaj d u) (Zb d (cy o (c9 3 r)) r)
 let neg:=aU (aaj d o) (Zb d l r)
 let k :=cy pos neg
 cy (cy 30000000 (cy 30000000 k)) base
private theorem cLk (s j a b c:Nat)  :
  afm s j ⟨a,b,c⟩=anq s j a b c:= by
 simp (disch:=omega) only [afm,aD6,Yp,anq,boX,agY,am7,nq,
  Bool.or_eq_true,Nat.blt_eq,decide_eq_true_eq,ab0]
 rfl
private def ag8 (s :Nat) :Nat→Nat→Nat→Nat
 | 0,_,_=>0
 | n+1,j,p =>
   let a :=Nat.mod p 512
   let b:=Nat.mod (lV p 512) 512
   let c:=Nat.mod (lV p 262144) 1024
   aU (anq s j a b c) (ag8 s n (aU j 1) (lV p 268435456))
private theorem fbP (s n j p:Nat) :Xy s n j p=ag8 s n j p:= by
 induction n generalizing j p with
 | zero=>rfl
 | succ n ih =>
   rw [ Xy,ag8,unpack,cLk _ _ _ _ _,ih _ _]
   rfl
private def strict {α:Sort _} (n:Nat) (f :Nat→α) :α :=
 match n with
 | 0=>f 0
 | k+1=>f (Nat.succ k)
private theorem iW {α:Sort _} (n:Nat) (f :Nat→α) :strict n f=f n:= by
 cases n <;> rfl
private def abN (s :Nat) (r :af) :Nat :=
 if 2008≤ s∧s<3012∧322≤ r.first∧r.first+r.count≤1063 ∧
  3000≤ s+r.first∧s+r.first+r.count≤3420
 then strict r.packed (ag8 s r.count r.first)
 else 0
def ada :Nat→List af→Nat
 | _,[]=>0
 | s,r :: rs=>Nat.add (abN s r) (ada (Nat.add s 1) rs)
theorem score (s :Nat) (rs :List af) (t:Nat) (h:ada s rs=t) :
   fD s rs=t:= by
 suffices e :fD s rs=ada s rs from e.trans h
 clear h
 induction rs generalizing s with
 | nil=>rfl
 | cons r rs ih =>
   rw [fD,ada,ih]
   congr 1
   unfold aph abN
   split
   · rw [iW,fbP]
   · rfl
end abF.Compact
end
