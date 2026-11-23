import ProximityPrize.SubmissionLower.ZT8CHOb
set_option Elab.async false
set_option autoImplicit true
namespace P5_7_1_7_4_3_4
noncomputable section
open Polynomial Finset qNu3xvc


open cu (L)
open E7 (CurvePlace)

open scoped Classical WithZero
private theorem rate {E :Type} [Field E] [Algebra L E] (A:Equation E) (hd:2≤A.d) :
    elimDegree A=polarRate A:= by
  have h1 :1≤A.d:= by omega
  have h2 :2≤6*A.d:= by omega
  have h3:1≤3*A.d*A.d:=Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
  have h4 :1≤2*A.d:= by omega
  unfold elimDegree pairDegree polarRate
  zify [h1,h2,h3,h4]
  ring
private theorem same_center {E :Type} [Field E] [Algebra L E] {A:Equation E}
    {r s :Bool} {v :GraphVal A r} {v' : GraphVal A s} {w:CurvePlace L E} {x y :L}
    (hx :Over v w x) (hy :Over v' w y) (h:v.val=v'.val) :x=y := by
  by_contra hn
  have hval :=v.constants (y-x) (sub_ne_zero.mpr (Ne.symm hn))
  have he :constant A (y-x) =
      (amm A - constant A x)-(amm A - constant A y) := by
    unfold constant
    rw [map_sub,map_sub]
    abel
  rw [he] at hval
  have hlt:=lt_of_le_of_lt (v.val.map_sub _ _)
    (max_lt hx.2.1 (h.symm ▸ hy.2.1))
  rw [hval] at hlt
  exact (lt_irrefl _ hlt)
private theorem sum_le_all {α:Type} (f :α→ℕ) (hf :f.HasFiniteSupport) (s :Finset α) :
    ∑ i∈s,f i ≤ ∑ᶠ i,f i:= by
  rw [finsum_eq_finsetSum_of_support_subset f (s :=hf.toFinset∪s) (by
    intro i hi
    exact mem_union_left _ (hf.mem_toFinset.mpr hi))]
  exact sum_le_sum_of_subset subset_union_right
end
end P5_7_1_7_4_3_4
