import ProximityPrize.SubmissionLower.RelativeFastRecordCover6814
import ProximityPrize.SubmissionLower.RelativeCertR15B46T3519To3672Fast

/-! Saved witness SHA256: ccbbea8270e1ed3913d077e4de49fcb0ea68de7057936f851dd18c2e12c7d807.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR18B19T3871To3955Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def band : Band := ⟨18,19,3871,3955,1359136408997686⟩

def p1 (l h x y u:Nat):Rectangle:=⟨l,h,4134,1,1270,x,y,u⟩
def p2 (l h x y u:Nat):Rectangle:=⟨l,h,8268,2,2540,x,y,u⟩
def r0:=p1 2490331 3011070 9663 9794 5698
def r1:=p1 3011071 3531810 9923 10061 5694
def r2:=p1 3531811 4052550 10103 10246 5690
def r3:=p1 4052551 4573290 10234 10381 5686
def r4:=p1 4573291 5094030 10304 10485 5682
def r5:=p1 5094031 5354400 10202 10349 5678
def r6:=p1 5354401 5614770 10246 10395 5676
def r7:=p1 5614771 5875140 10286 10436 5674
def r8:=p1 5875141 6135510 10323 10474 5672
def r9:=p1 6135511 6395880 10356 10508 5671
def r10:=p2 6395881 6656250 16696 16949 11338

def b0 : List (Rectangle × FastWitness) := [(r0,⟨37,1,1⟩),(r1,⟨37,1,1⟩),(r2,⟨37,1,1⟩),(r3,⟨37,1,1⟩),(r4,⟨37,37,37⟩),(r5,⟨37,1,1⟩),(r6,⟨37,1,1⟩),(r7,⟨37,4,28⟩)]
theorem checked0 : fastCheckList band b0=true := by decide +kernel

def b1 : List (Rectangle × FastWitness) := [(r8,⟨37,37,37⟩),(r9,⟨37,37,37⟩),(r10,⟨37,37,37⟩)]
theorem checked1 : fastCheckList band b1=true := by decide +kernel

def witnessedRows : List (Rectangle × FastWitness) := b0++b1
def rows : List Rectangle := witnessedRows.map Prod.fst
theorem all_fast_checked : fastCheckList band witnessedRows=true := by
  simp only [witnessedRows,fastCheckList_append,checked0,checked1,Bool.true_and]
theorem all_checked : checkList band rows=true := fastCheckList_sound band witnessedRows all_fast_checked
theorem tiled : covers (minimumWeight band) (tail band) rows=true := by decide +kernel
theorem verified : VerifiedCover band rows :=
  ⟨all_checked,tiled,by decide +kernel⟩

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K

theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 18)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 18≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤19)
    (hT0 : 3871≤T) (hT1 : T≤3955) (hnu : 2490331≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤1359136408997686 :=
  regular_count_of_cover K I band rows verified F hbox hcode htotal hslope hB hT0 hT1 hnu
    nodes u0 u1 hcard selected Gamma hdegree hagreement hno

#print axioms regular_count
end
end ProximityPrize.SubmissionLower.RelativeCertR18B19T3871To3955Fast
