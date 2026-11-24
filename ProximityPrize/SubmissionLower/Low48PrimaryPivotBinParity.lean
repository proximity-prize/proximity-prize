import ProximityPrize.SubmissionLower.Low48PrimaryPivotSectionSum

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Low48PrimaryPivot
open Finset KoalaLinearWindow KoalaPiecewiseTriangle
open scoped BigOperators
open Low48PrimaryPivot (paritySpan widthLine countTree countTree_at)

private theorem sum_by_parity (m : ℤ) (f : ℤ → ℤ) :
    (∑ a ∈ Ico (0:ℤ) (m+1), f a) =
      (∑ u ∈ (paritySpan m 0).finset, f (2*u)) +
        ∑ u ∈ (paritySpan m 1).finset, f (2*u+1) := by
  let idx (r : ℤ) := (paritySpan m r).finset
  have htwo : Ico (0:ℤ) 2 = {0,1} := by decide
  have hsum : (∑ r ∈ Ico (0:ℤ) 2, ∑ u ∈ idx r, f (2*u+r)) =
      (∑ u ∈ idx 0, f (2*u)) + (∑ u ∈ idx 1, f (2*u+1)) := by
    rw [htwo]
    simp
  rw [← hsum, Finset.sum_sigma']
  refine sum_bij (fun a _ => (⟨a%2,a/2⟩ : Sigma (fun _ : ℤ => ℤ))) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_sigma,mem_Ico,idx,Span.finset,paritySpan] at ha ⊢
    omega
  · intro a _ b _ he
    have hmod := congrArg Sigma.fst he
    have hdiv := congrArg (fun p : Sigma (fun _ : ℤ => ℤ) => p.snd) he
    change a%2 = b%2 at hmod
    change a/2 = b/2 at hdiv
    omega
  · rintro ⟨r,u⟩ hx
    simp only [mem_sigma,mem_Ico,idx,Span.finset,paritySpan] at hx
    refine ⟨2*u+r,mem_Ico.mpr (by omega),?_⟩
    have hm : (2*u+r)%2 = r := by omega
    have hd : (2*u+r)/2 = u := by omega
    simp [hm,hd]
  · intro a _
    change f a = f (2*(a/2)+a%2)
    congr 1
    omega

theorem totalAtIndex_eq (j : ℤ) :
    totalAtIndex j = ∑ f ∈ Ico (0:ℤ) (j/3+1), ((j-3*f)/2+1) := by
  rw [sum_by_parity]
  unfold totalAtIndex
  simp only [Span.sumLine_eq,widthLine,Line.at]
  congr 1 <;> apply sum_congr rfl <;> intro u _ <;> omega

theorem uncharged_eq (j q : ℤ) :
    uncharged j q = ∑ f ∈ Ico (0:ℤ) (min (j/3) (1650-q)+1),
      max 0 ((j-3*f)/2+1 -
        max 0 (max (3*q-9900+5*j-3*f)
          (max (q-4950+3*j-2*f) (2*q-4950+2*j-f)))) := by
  rw [sum_by_parity]
  simp only [uncharged,ReceiptTree.sumPositive_eq,countTree_at,add_zero]

#print axioms totalAtIndex_eq
#print axioms uncharged_eq
end Low48PrimaryPivot
