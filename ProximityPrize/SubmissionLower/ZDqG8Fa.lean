import ProximityPrize.SubmissionLower.ZFO2WXb
import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZTOdMMe
set_option Elab.async false
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def r0:=p! 854 192 0x3872fa96a 33 5 0xde36f26f75c9fd2d869632ff52cc006e280130
private def r1 :=p! 864 194 0x3b132c18f 33 5 0x3036db2c578c64d764636ef15957f006ff724b0
private def r2 :=p! 911 189 0x44a1de7ca 33 5 0x2065eae436b13b0678e9cdb75755b900775c11cf
private def r3:=p! 915 190 0x45e442b21 33 5 0x2728475466ebe22e9944d12f610c9000781cae1c
private def r4 :=p! 992 206 0x607de052f 34 5 0x187603fa46146856a4533508082f2942008618bedb
private def r5:=p! 997 207 0x626ef17da 34 5 0x1b1f234848c27893a4ff8740084741d00086fd2a44
private def r6:=p! 1028 211 0x6e3c8588b 34 5 0x2ec48d89597b13abe8eb11d008d00c74008c634253
private def r7:=p! 1043 235 0x7d9526018 34 5 0x4c93af5f6c9f2c972e4452700999bc9c008f8db05d
private def r8:=p! 1044 235 0x7df876992 34 5 0x4d8596f36d2f19d1ae6274b0099d952c008fb8d559
private def r9:=p! 1073 239 0x8b6437628 34 6 0xca1da070bca47b801cec9672719bc00a2486f00094a51fec
private def dz :=p! 1075 216 0x8198261fa 34 6 0xa84e45b3308e97540899faedc9668099c099a00947ec45a
private def dD:=p! 1092 226 0x8d33cde30 34 6 0x1508b6479a9c3148497431df27dba180a1d72860097a9a8cc
private def dK:=p! 1093 226 0x8d9e309f3 34 6 0x16af7107af030238531a673f29af6000a2135800097d4c23d
private def e8:=p! 1108 231 0x96813b22f 34 6 0x4c0fce895766c90914015f4f53624200a7a5908009a742a92
private def gD:=p! 1120 239 0x9ffef4558 34 6 0xb3a6e10b28bccce9d9fb57ab80c64c00adaf930009c916f1c
private def gx :=p! 1125 230 0x9d827c7f4 34 6 0x9b275ecadaa56509b6753f9770074300ab47d0c009d4cfe44
def dataC:Array aqm := #[
 r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,dz,dD,dK,e8,gD,gx
]
end qpECY2d
end
section
namespace qQCEOid
noncomputable section
open Polynomial
open cu (Shape ku)
open DP (CI)
open Ge (Gm)
open aeL (Offset Lh Pivot a2N input)
open scoped BigOperators Polynomial
abbrev SeedCol (s :Shape) (t:Offset s) (u:ℕ) :=Lh s t×Fin (u+1)
abbrev VP (s :Shape) (t:Offset s) (u:ℕ) :=Pivot s t×Fin (u+s.B+1)
def clearedEntry {F:Type} [Field F] {s :Shape} {t:Offset s}
    (a b c:F) (r :Pivot s t) (v :Lh s t) :F[X] :=
  let j:=a2N v
  if r.1.val≤v.1.val∧j≤ r.1.val then
    C ((j.choose r.2.val :F)*((v.1.val-j).choose (r.1.val-j) :F)) *
      (C a*Polynomial.X (R:=F))^(v.1.val-r.1.val) *
      (C b+C c*Polynomial.X (R:=F))^(s.B-v.1.val)
  else 0
def seedMatrix {F:Type} [Field F] (s :Shape) (t:Offset s) (u:ℕ)
    (a b c:F) :Matrix (VP s t u) (SeedCol s t u) F :=
  fun r v=>(clearedEntry a b c r.1 v.1).coeff (r.2.val-v.2.val) *
    if v.2.val≤ r.2.val then 1 else 0
def sourceVector {F:Type} [Field F] {s :Shape} {t:Offset s}
    (α:F) (side :Fin 2) (r :Fin (s.U+1)) :
    Gm F →ₗ[F] (SeedCol s t (s.U-r.val)→F) :=
  LinearMap.pi fun v =>
    (MvPolynomial.lcoeff F
      (Finsupp.single side v.2.val+Finsupp.single (CI side) r.val)).comp
        (input α v.1)
abbrev WindowCol (s :Shape) (t:Offset s) (u k :ℕ) :=
 {v :Lh s t // v.1.val≤k∧k≤v.1.val+u}
def windowMatrix (F:Type) [Field F] (s :Shape) (t:Offset s) (u k :ℕ) :
    Matrix (Pivot s t) (WindowCol s t u k) F :=
  (aeL.Pa s t (1 :F)).submatrix id Subtype.val
def windowBudget (s :Shape) (t:Offset s) (u k :ℕ) :ℕ :=
  ku s fun q j =>
    if s.J-j≤t.val∧t.val<s.B+2*s.J-(q+min q s.J)+j ∧
      q-j≤u∧q≤k∧k≤ s.B+u-(q-j) then 1 else 0
def seedBudget (s :Shape) (t:Offset s) (u:ℕ) :ℕ :=
 ∑ k∈Finset.range (s.B+u+1),windowBudget s t u k
end
end qQCEOid
end
