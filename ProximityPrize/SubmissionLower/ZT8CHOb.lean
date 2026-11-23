import ProximityPrize.SubmissionLower.Z62SyBc
set_option Elab.async false
namespace P5_7_1_7_4_3_4
noncomputable section
open Polynomial Finset qNu3xvc
open P5 (p)
open qFD8jve (aFA sheetPole)
open cu (L)
open E7 (CurvePlace KB)

open scoped Classical WithZero
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d→A.d<p →
    ∀ (ι:Type) [Fintype ι] (w:ι→CurvePlace L E) (x :ι→L) (r :ι→Bool)
      (v : ∀ i,GraphVal A (r i)),(∀ i,Over (v i) (w i) (x i)) →
      ∃ C:Pencil A,(∀ i,(v i).val (relativePolar C)=(v i).val (polar A (r i))) ∧
        ∀ i,∃ n:ℕ,0<n ∧ ∀ g:E[X],
          (v i).val (C.base (algebraMap E[X] (RatFunc E) g))=adG (w i).value g^n
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d → ∀ C:Pencil A,
    ∃ P:E[X][X],P.coeff 0≠0 ∧
      bix C.base (relativePolar C) C.finite ∣
        P.map (algebraMap E[X] (RatFunc E)) ∧
      ∀ w:CurvePlace L E,aFA w.value P (elimDegree A*sheetPole w.value A.f)
def c3:Prop :=
  ∀ {E F:Type} [Field E] [Algebra L E] [Field F] (w:CurvePlace L E)
    (m:RatFunc E →+* F) (q:F),
    ∀ (hf :letI:=m.toAlgebra; Module.Finite (RatFunc E) F),
    (letI:=m.toAlgebra; Algebra.IsSeparable (RatFunc E) F) →
    q≠0 → ∀ P:E[X][X],P.coeff 0≠0→ aFA w.value P 0 →
    bix m q hf∣P.map (algebraMap E[X] (RatFunc E)) →
    ∀ {ι:Type} (S:Finset ι) (v :ι→Valuation F ℤᵐ⁰),
      Set.InjOn v (S:Set ι)→(∀ i∈S,Function.Surjective (v i)) →
      (∀ i∈S,∃ n:ℕ,0<n ∧ ∀ g:E[X],
        v i (m (algebraMap E[X] (RatFunc E) g))=adG w.value g^n) →
      (∑ i∈S,KB (v i) q)≤(-WithZero.log (adG w.value (P.coeff 0))).toNat
private theorem same_center {E :Type} [Field E] [Algebra L E] {A:Equation E}
   {r s :Bool} {v :GraphVal A r} {v' : GraphVal A s} {w:CurvePlace L E} {x y :L}
   (hx :Over v w x) (hy :Over v' w y) (h:v.val=v'.val) :x=y := by
 by_contra hn
 have q0:=v.constants (y-x) (sub_ne_zero.mpr (Ne.symm hn))
 have he :constant A (y-x) =
     (amm A - constant A x)-(amm A - constant A y) := by
   unfold constant
   rw [map_sub,map_sub]
   abel
 rw [he] at q0
 have hlt:=lt_of_le_of_lt (v.val.map_sub _ _)
   (max_lt hx.2.1 (h.symm ▸ hy.2.1))
 rw [q0] at hlt
 exact (lt_irrefl _ hlt)
private theorem sum_le_all {α:Type} (f :α→ℕ) (hf :f.HasFiniteSupport) (s :Finset α) :
  ∑ i∈s,f i ≤ ∑ᶠ i,f i:= by
 rw [finsum_eq_finsetSum_of_support_subset f (s :=hf.toFinset∪s) (by
  intro i hi
  exact mem_union_left _ (hf.mem_toFinset.mpr hi))]
 exact sum_le_sum_of_subset subset_union_right
end
end P5_7_1_7_4_3_4
