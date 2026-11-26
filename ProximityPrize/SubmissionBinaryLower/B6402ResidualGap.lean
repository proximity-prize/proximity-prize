import ProximityPrize.SubmissionBinaryLower.B6402HardAuxiliary
import ProximityPrize.SubmissionBinaryLower.B6402LocatorOrder

/-! Removing the regular-site locator gives the gap charged to the native
P64 label theorem. The remaining debit is only 2b per exceptional site. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ResidualGap
open Polynomial B6401ContactKerD P64LineOrder P64Caps.Weighted
open B6402HardAuxiliary B6402LocatorDivision B6402LocatorOrder
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {K : Type} [Field K] [CharP K 2] {I : Type*} [DecidableEq I] [Fintype I]

def charge (k : ℕ) : ℤ := 2*(min k 3:ℕ)-1

theorem point (m b s k : ℕ) (hb : b≤m) (good : Prop) [Decidable good] (hk : good → k=2)
    (before after : ℕ)
    (h1 : (if k=0 then 2*mi m b k-s else 2*mi m b k+s*(2*k-1))≤before)
    (h2 : before≤(if good then 2*b else 0)+after) :
    2*(m-b:ℕ)+(s:ℤ)*charge k≤(after:ℤ) := by
  by_cases ze : k=0
  · subst k
    have no : ¬good := by intro h; have := hk h; omega
    simp [mi,no,charge] at h1 h2 ⊢
    omega
  · have hkmin : 2*min k 3-1≤2*k-1 := by omega
    have pos : 1≤min k 3 := by omega
    have hk0 : 1≤2*min k 3 := by omega
    have hc := Nat.mul_le_mul_left s hkmin
    have ec : ((2*min k 3-1 : ℕ):ℤ)=charge k := by unfold charge; rw [Nat.cast_sub hk0]; push_cast; rfl
    by_cases g : good
    · have ek := hk g; subst k
      simp [mi,g] at h1 h2
      norm_num [charge]
      omega
    · rw [if_neg ze] at h1; simp [g] at h2
      have lower : m-b≤mi m b k := by unfold mi; split <;> omega
      have h : 2*(m-b)+s*(2*min k 3-1)≤after := by omega
      rw [←ec]; exact_mod_cast h

theorem cleaned_gap (x : I ↪ K) (y : I → K[X]) (k : I → ℕ) (F : ContactPoly (Polynomial K))
    (p r : BiPoly (Polynomial K)) (hr : r≠0) (m b s w A W WF D : ℕ)
    (hb : b≤m) (hw : 1≤w) (hwF : w-1≤WF)
    (edge : p=locator x (regular k x F) b*r) (fits : Finset I)
    (ord : ∀ i,OrdGE p (x i) (y i) (if k i=0 then 2*mi m b (k i)-s else 2*mi m b (k i)+s*(2*k i-1)))
    (weight : weightedSupportDegree p w≤W+s*(WF-(w-1)))
    (load : W<2*((m-b)*A+b*(marked k).card))
    (gap : (s:ℤ)*((WF:ℤ)-(w-1:ℕ)-(∑ i∈fits,charge (k i)))≤D) :
    (weightedSupportDegree r w:ℤ)-(∑ i∈fits,(lineOrd r (x i) (y i):ℤ))+
      2*(m-b:ℕ)*((fits.card:ℤ)-A)≤(D:ℤ)+2*(b:ℤ)*(exceptional k x F).card := by
  classical
  have hpart : (regular k x F).card+(exceptional k x F).card=(marked k).card := by
    unfold regular exceptional
    simpa only [not_ne_iff] using Finset.card_filter_add_card_filter_not (s:=marked k) (p:=fun i => evalXAt (F.coeff 1) (x i)≠0)
  have hp : p≠0 := edge ▸ mul_ne_zero (loc_ne x _ _) hr
  have line (i : I) : 2*(m-b:ℕ)+(s:ℤ)*charge (k i)≤(lineOrd r (x i) (y i):ℤ) :=
    point m b s (k i) hb (i∈regular k x F) (fun hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2) _ _
      ((ordGE_iff hp _ _ _).mp (ord i)) (residual_line x (regular k x F) b i (y i) p r hr edge)
  have sumOrd := Finset.sum_le_sum (fun i (_:i∈fits) => line i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at sumOrd
  rw [edge,weightedSupportDegree_mul _ _ _ (loc_ne x _ _) hr,weighted_locator] at weight
  have hwQ := Int.ofNat_le.mpr weight
  have hload := Int.ofNat_lt.mpr load
  have hparts := congrArg (fun n : ℕ => (n:ℤ)) hpart
  push_cast [Nat.cast_sub hwF] at hwQ
  push_cast at hload hparts
  nlinarith only [hwQ,hload,sumOrd,gap,congrArg (fun t:ℤ => 2*(b:ℤ)*t) hparts]

#print axioms cleaned_gap
end ProximityPrize.SubmissionBinaryLower.B6402ResidualGap
