import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZTOdMMe
import ProximityPrize.SubmissionLower.ZLt6kU
set_option Elab.async false
section
set_option autoImplicit true
namespace qMNIwTb
open P5 (I)
open P5_7_2 (A Aux fO introduction stages)
open cu (L FX Jet Shape triangle)
open DP (jF zG VY)
open Finset
def Filed (b:fO) (moving:Bool) (a :Aux) :Prop :=
  (moving=false∧a∈introduction b) ∨
    ∃ s∈stages b,a=⟨s.dI,if moving then s.moving else s.free⟩
def CJ (b:fO) (moving:Bool) (a :Aux) :Prop :=
  if moving then b.val=0 else b.val<7 ∧
    ((a.dI=6∧a.shape.m=98)∨(a.dI=10∧a.shape.m=123) ∨
      (a.dI=24∧(a.shape.m=235∨a.shape.m=233)))
def Mq (h:ℕ) (a :Aux) :ℕ:=a.shape.m*A-2*h*a.dI
def aL4 (h:ℕ) (a :Aux) :Prop :=
 a.shape.B*(131071-h)<Mq h a
abbrev fullCap (s :Shape) (q:ℕ) :ℕ:=min q s.J
def trimCap (a :Aux) (q:ℕ) :ℕ :=
  if a.dI=24∧q=3228 then 101 else
    min (fullCap a.shape q) ((Mq 2533 a-q*(131071-2533)-1)/(2*2533-1))
def capSum (s :Shape) (d:ℕ→ℕ) (f :ℕ→ℕ→ℕ) :ℕ :=
 ∑ q∈range (s.B+1),∑ j∈range (d q+1),f q j
def O3 (h:ℕ) (a :Aux) (d:ℕ→ℕ) (moving:Bool) :ℕ :=
  triangle a.shape.U*capSum a.shape d (fun q j =>
    Mq h a+j-q*(131071-h)-(if moving then 2*h*j else 0))
def eligible (h N W q j:ℕ) :Prop :=
 q*(131071-h)≤W+j∧N≤W+2*h*j
instance (h N W q j:ℕ) :Decidable (eligible h N W q j) :=
 inferInstanceAs (Decidable (_∧_))
def Xq (h:ℕ) (a :Aux) (d:ℕ→ℕ) (W:ℕ) :ℕ :=
 capSum a.shape d (fun q j=>if eligible h (Mq h a) W q j then 1 else 0)
def aMH (h:ℕ) (a :Aux) (d:ℕ→ℕ) :ℕ :=
 triangle a.shape.U * ∑ W∈range (Mq h a),Xq h a d W
noncomputable def rankSum (N :ℕ) (V:ℕ→Submodule FX Jet) :ℕ :=
 ∑ W∈range N,Module.finrank FX (V W)
structure LayeredBank {h:ℕ} {D:jF h} (Crt:zG D) (word:I→L)
   (a :Aux) (d:ℕ→ℕ) (V:ℕ→Submodule FX Jet) :Prop where
 cfw:0<Mq h a
 cap_le : ∀ q,d q≤fullCap a.shape q
 incl : ∀ W,V W≤VY Crt word a.shape W
 support : ∀ W,∀ P∈V W,∀ j i,(P.coeff j).coeff i≠0→j≤d (i+j)
 DG:aMH h a d< rankSum (Mq h a) V
end qMNIwTb
end
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def r0:=p2! 1134 234 0xa3c8f6183 34 6 0xf922f20c213c7a2a3aed59578cae0080af13402009ee0b6c4
private def r1 :=p2! 1140 235 0xa723cee72 34 6 0x13912360cdcd2ddea83f4b78f9af4cb00b0ecb2c009fe6b3d9
private def r2 :=p2! 1160 242 0xb4d72a74c 34 6 0x294af178fdf57a2dba43e5d57d65c9780b89a65e00a354aa6c
private def r3:=p2! 1270 264 0x102ee64ad0 35 6 0x2fb3a47023c95e51e8df470cb13e94db001b9855c1d0b5e77240
private def r4 :=p2! 1345 278 0x1442899e20 35 7 0x11f76d1075d460a8b5cc54437b249f9a0172bef3401eae28c0a0c28d0b40
private def r5:=p2! 1350 281 0x14acf4e78f 35 7 0x1750cd207dd2be0d37884a6e3b5e06570178488ae01efb62c050c364e240
private def r6:=p2! 1387 287 0x16ed52c18e 35 7 0x4759a94caf096d0f419a43f35c84d41001922682002078f8a540c9a21940
private def r7:=p2! 1388 287 0x16faec823e 35 7 0x48ecd248b04e62cc41d96abccc8b72500192b24a002081724040c9cd4440
private def r8:=p2! 1422 296 0x1971d848fb 35 7 0xa42b48ecea32e23dcc8e6eaa3dc2612001ae6fa4002208456b10cf88fa40
private def r9:=p2! 1434 299 0x1a5909872a 35 7 0xd095397500787a5e507447000e30cbe601b82efcc0228fef7e88d18efe40
private def dz :=p2! 1435 299 0x1a68289886 35 7 0xd3d5c70d02076ea550b8beaace37a2ae01b8bed5c022988c3c68d1ba2940
private def dD:=p2! 1621 338 0x2afe01e630 36 8 0x24ac4aa41f6e96cb759ef9696c938466c00a8dec6c0093d926c0054e961a290f1176740
def dataD:Array aqm := #[
 r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,dz,dD
]
end qpECY2d
end
