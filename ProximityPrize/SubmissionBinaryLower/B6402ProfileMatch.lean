import ProximityPrize.SubmissionBinaryLower.B6402SelectedPlan
import ProximityPrize.SubmissionBinaryLower.B6402BucketBudget
import ProximityPrize.SubmissionBinaryLower.B6401FactorBound

namespace ProximityPrize.SubmissionBinaryLower.B6402ProfileMatch
open B6401Params B6402Table4Common B6402GridRouting B6402OrderProfile B6402ResidualGap
open B6401FactorBound (G_val)
open scoped BigOperators Classical
set_option autoImplicit false
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
local notation "I" => BinaryIRSProfile.Index

private theorem counted {ι : Type*} [Fintype ι] (k : ι → ℕ) (p : ι → Prop) [DecidablePred p]
    (j : ℕ) (hp : ∀ i,p i ↔ min (k i) 3=j) : (Finset.univ.filter p).card=count k j := by
  unfold count
  exact congrArg Finset.card (Finset.filter_congr fun i _ => hp i)

private theorem count0 (D : KerD45Data) : D.n0=count D.k 0 := by
  unfold KerD45Data.n0 count
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  omega

private theorem count1 (D : KerD45Data) : D.n1=count D.k 1 := by
  unfold KerD45Data.n1 count
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  omega

private theorem count2 (D : KerD45Data) : D.n2=count D.k 2 := by
  unfold KerD45Data.n2 count
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  omega

private theorem count3 (D : KerD45Data) : D.n3=count D.k 3 := by
  unfold KerD45Data.n3 count
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  omega

private theorem excess_count (D : KerD45Data) : D.nt=totalExcess D.k := by
  unfold KerD45Data.nt totalExcess
  rfl

theorem counts (D : KerD45Data) : D.n0=count D.k 0 ∧ D.n1=count D.k 1 ∧ D.n2=count D.k 2 ∧
    D.n3=count D.k 3 ∧ D.nt=totalExcess D.k := ⟨count0 D,count1 D,count2 D,count3 D,excess_count D⟩

private theorem sum_test (S : Finset I) (p : I → Prop) [DecidablePred p] (a : ℤ) :
    (∑ i ∈ S,if p i then a else 0)=(S.filter p).card*a := by
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]

theorem charge_gap (W : ℕ) (k : I → ℕ) (S : Finset I) :
    (W:ℤ)-(wY-1:ℕ)-(∑ i∈S,charge (k i))=G_val W k S := by
  have term (i:I) : charge (k i)=(if k i=0 then (-1:ℤ) else 0)+(if k i=1 then 1 else 0)+
      (if k i=2 then 3 else 0)+(if 3≤k i then 5 else 0) := by
    unfold charge; split_ifs <;> omega
  simp only [term,Finset.sum_add_distrib,sum_test,G_val]
  push_cast; ring

theorem gap_eq (D : KerD45Data) : GapValue D=G_val D.W_F D.k D.Az := by
  unfold GapValue G_val KerD45Data.a0 KerD45Data.a1 KerD45Data.a2 KerD45Data.a3
  rfl

theorem nonneg (D : KerD45Data) : 0≤G_val D.W_F D.k D.Az := by
  rw [←gap_eq]; unfold GapValue
  have h := D.a1_3a2_5a3_le
  have w := D.hWF_lo
  have hw : wY-1≤D.W_F := by omega
  have h' := Int.ofNat_le.mpr h
  push_cast [Nat.cast_sub (by omega : wY≤D.W_F)] at h'
  have h1 : wY=1048575 := rfl
  omega

#print axioms counts
#print axioms charge_gap
end ProximityPrize.SubmissionBinaryLower.B6402ProfileMatch
