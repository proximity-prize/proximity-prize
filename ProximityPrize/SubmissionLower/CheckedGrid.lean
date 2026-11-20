/- Apache-2.0. Kernel-checked packed prices imply additive fees for every physical partition. -/
import ProximityPrize.SubmissionLower.GridProof
import ProximityPrize.SubmissionLower.Night6836Checks
namespace Koala6836.Bound
open Koala6835.Packed Koala6835.Partition
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000
def table : KoalaNight.Grid.Table := ⟨14,94,8191,Grid.oneRow,Grid.allRow,Grid.compRow⟩
def q : ℕ := 770000000000000
def one (r e k:ℕ) := KoalaNight.Grid.single table r e k*q
def all (r e k:ℕ) := KoalaNight.Grid.overall table r e k*q
def many (r e k:ℕ) := KoalaNight.Grid.multiple table r e k*q

private theorem fast_pack (b n:ℕ) (f:ℕ→ℕ) : Fast.pack b n f=pack b n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [Fast.pack,pack,ih]
private theorem rep_eq : Fast.rep=pack (2^14) 94 (fun _=>1) := by decide +kernel
private theorem rep_rows_eq : Fast.repRows=pack ((2^14)^94) 94 (fun _=>1) := by decide +kernel
private theorem xa (x:ℕ) : Fast.xBlock x=rowA 14 94 x := by
  unfold Fast.xBlock rowA
  rw [fast_pack,rep_eq]
  rfl
private theorem ya (x:ℕ) : Fast.yBlock x=rowB 14 94 x := by
  unfold Fast.yBlock rowB
  rw [rep_rows_eq]
private theorem ca (x:ℕ) : Fast.cBlock x=rowC 14 94 x := by
  unfold Fast.cBlock rowC
  rw [fast_pack]
  rfl
private theorem mask_eq : Fast.blockMask=rowB 14 94 (mask 14 94 8191) := by
  unfold Fast.blockMask rowB mask
  rw [rep_eq,rep_rows_eq,pack_const_mul (2^14) 94 8191]
  rfl
private theorem split_eq (r e a m:ℕ) : Fast.checkSplit r e a m=KoalaNight.Grid.check table r e a m := by
  unfold Fast.checkSplit KoalaNight.Grid.check passes
  rw [xa,ya,ca,mask_eq]
  rfl
theorem physical_certificate
    (valid:∀r e:ℕ,1≤r → r≤18 → r+e≤76 → Fast.dataOK r e=true ∧ Fast.checks r e=true) :
    Certificate one all many 18 76 9352 100 := by
  apply KoalaNight.Grid.certificate table 4095 q 18 76 9352 100 (by decide)
  · intro r e k _ hk
    change k<94
    omega
  · intro r e hr hm hy
    obtain ⟨d,c⟩ := valid r e hr hm hy
    refine ⟨d,?_⟩
    simpa only [Fast.checks,KoalaNight.Grid.checks,split_eq] using c
theorem one_round (r e k:ℕ) (checked:Fast.rounded r e=true) (hk:k<94) :
    Tables.oneUnits r e k*10000000000000 ≤ one r e k := by
  have base := of_decide_eq_true (List.all_eq_true.mp checked k (List.mem_range.mpr hk))
  change Tables.oneUnits r e k≤77*(digit 14 (Grid.oneRow r e) k) at base
  change _≤digit 14 (Grid.oneRow r e) k*770000000000000
  omega
#print axioms physical_certificate
#print axioms one_round
end Koala6836.Bound
