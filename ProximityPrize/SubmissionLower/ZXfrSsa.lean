import ProximityPrize.SubmissionLower.Zqby9gc
import ProximityPrize.SubmissionLower.ZLcmX9d
set_option Elab.async false
set_option autoImplicit true
namespace q1yhP8b
open Finset
open aR (Shape)
open NR (ay8)
open qFAh60c (Bank width)
open qzLARrc (oneDebit windowBudget)
open scoped BigOperators
private def mass (a :Shape) (n:ℕ) :ℕ :=
  ∑ q∈range n,(a.b+a.j - q)*ay8 a q
private theorem row (a :Shape) (i n:ℕ) {s t:ℕ} (hs :mass a i=s)
    (ht: (∑ j∈range n,(a.b+a.j-(i+j))*ay8 a (i+j))=t) :
    mass a (i+n)=s+t:= by
  unfold mass at hs ⊢
  rw [sum_range_add,hs,ht]
local notation "az" a:arg i:arg n:arg ans:arg h:arg=>row a i n (t:=ans) h rfl
private abbrev A:=qlc9qed.Bank.cheap.box
private abbrev B:=qlc9qed.Bank.strong.box
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
private theorem slope_cheap:slope A=991536:= by
  have r0:mass A 0=0:=rfl
  have r1 :mass A 12=38493:=az A 0 12 38493 r0
  have r2 :mass A 24=213679:=az A 12 12 175186 r1
  have r3:mass A 36=423696:=az A 24 12 210017 r2
  have r4 :mass A 48=604656:=az A 36 12 180960 r3
  have r5:mass A 60=755664 :=az A 48 12 151008 r4
  have r6:mass A 72=876720:=az A 60 12 121056 r5
  have r7:mass A 84=967824 :=az A 72 12 91104 r6
  exact az A 84 4 23712 r7
private theorem slope_strong:slope B=10745120:= by
  have r0:mass B 0=0:=rfl
  have r1 :mass B 12=74893:=az B 0 12 74893 r0
  have r2 :mass B 24=507715:=az B 12 12 432822 r1
  have r3:mass B 36=1431140:=az B 24 12 923425 r2
  have r4 :mass B 48=2658743:=az B 36 12 1227603 r3
  have r5:mass B 60=3890720:=az B 48 12 1231977 r4
  have r6:mass B 72=5031200:=az B 60 12 1140480 r5
  have r7:mass B 84=6079520:=az B 72 12 1048320 r6
  have r8:mass B 96=7035680:=az B 84 12 956160 r7
  have r9:mass B 108=7899680:=az B 96 12 864000 r8
  have dz :mass B 120=8671520:=az B 108 12 771840 r9
  have dD:mass B 132=9351200:=az B 120 12 679680 dz
  have dK:mass B 144=9938720:=az B 132 12 587520 dD
  have e8:mass B 156=10434080:=az B 144 12 495360 dK
  exact az B 156 9 311040 e8
theorem width_ge_box (b:Bank) :b.box.b≤width b:= by cases b <;> decide
theorem resized_budget (b:Bank) (h:windowBudget b.box b.U≤oneDebit b) :
    windowBudget b.box (width b)≤(width b+1)*b.basePole+b.poleExcess := by
  have hs :slope b.box=b.basePole := by
    cases b
    · exact slope_cheap
    · exact slope_strong
  have hw:width b≤b.U:= by cases b <;> decide
  let d:=b.U - width b
  have hu:width b+d=b.U:= by dsimp [d]; omega
  have hd:oneDebit b=(width b+1)*b.basePole+b.poleExcess+d*b.basePole := by
    unfold oneDebit
    rw [← hu,show width b+d+1=(width b+1)+d by omega,Nat.add_mul,Nat.add_right_comm]
  rw [← hu,bP5 _ _ _ (width_ge_box b),hs,hd] at h
  exact Nat.le_of_add_le_add_right h
end q1yhP8b
