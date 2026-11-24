import ProximityPrize.SubmissionLower.Zqb2cFb
import ProximityPrize.SubmissionLower.ZZZuA2c
import ProximityPrize.SubmissionLower.ZW31ykd
set_option Elab.async false
section
set_option autoImplicit true
namespace qMHqmcc
open P5_7_2 (fO Test)
def c2 :Prop := ∀ b:fO,2≤b.val→b.val<4 → ∀ x :Test b,cL b x
def c3:Prop := ∀ b:fO,4≤b.val→b.val<6 → ∀ x :Test b,cL b x
def c4 :Prop := ∀ b:fO,6≤b.val→b.val<8 → ∀ x :Test b,cL b x
def c5:Prop := ∀ b:fO,8≤b.val→b.val<10 → ∀ x :Test b,cL b x
def c6:Prop := ∀ b:fO,10≤b.val→b.val<12 → ∀ x :Test b,cL b x
def c7:Prop := ∀ b:fO,12≤b.val → ∀ x :Test b,cL b x
end qMHqmcc
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
private abbrev kA:fO:=⟨7,by decide⟩
set_option quotPrecheck false in
local notation "kU" => receipt 2542 rfl (by decide +kernel) (by decide +kernel)
private theorem OL:GG kA 60 3:=⟨kU,kU,kU,True.intro⟩
private theorem Vd:GG kA 63 3:=⟨kU,kU,kU,True.intro⟩
private theorem r66:GG kA 66 3:=⟨kU,kU,kU,True.intro⟩
private theorem r69:GG kA 69 3:=⟨kU,kU,kU,True.intro⟩
theorem o:GG kA 60 12 :=
 appendGrades (appendGrades (appendGrades OL Vd) r66) r69
end qyV6B3d
end
section
set_option autoImplicit true
namespace qMFKljd
open Finset P5_8_2 qxVnKgd
private def cost (k e :ℤ) :ℤ:=k*(k+1)+e*(k+1)
private def part (k e :ℤ) :ℤ:=k*(k+1)*(4*k-1)+6*e*k*(k+1)
private def nY (k e a r b s :ℤ) :ℤ :=
 (2*b+s-(2*a+r))*(5768280-6*cost k e) - part b s+part a r
private def row (p l b:ℤ) :ℤ:=nY (p/2) (p%2) (l/2) (l%2) (b/2) (b%2)
private def f (i:ℕ) :ℤ :=
 let p:ℤ:=1+i
 row p (max 1 (p-1651)) (min (3919-2*p) ((3919-p)/2)+1)
end qMFKljd
end
