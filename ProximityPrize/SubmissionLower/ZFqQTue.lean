import ProximityPrize.SubmissionLower.ZpWrDCd
set_option Elab.async false
namespace qLXroAb
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K p)
open cu (L)
open E7 (CurvePlace poleOrder KB)


open qb0hmCe (CurveModel)
open q1kuFjb (principal)
open qFD8jve (aFA sheetPole)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation)
open qxPDCsa (UnitAt)
open private pole_sum from ProximityPrize.SubmissionLower.Zay1XCa
def c1 :Prop :=qxPDCsa.c1
def c2 :Prop :=qxPDCsa.c2
def c3:Prop :=qxPDCsa.c5
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
def c4 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (V:Variation F),3≤F.d→F.d<p →
    ∃ A:Pencil F,∀ γ (hγ:γ∈V.marks),Nonempty (Chart A γ (V.Bp hγ) (V.den γ))
def c5:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (A:Pencil F) (D W:ℕ),
    3≤F.d→0<D→D <p→F.d*D ≤W→F.weight D W →
    ∃ R:Cq.E[X][X],R≠0 ∧
      (∀ w:CurvePlace L Cq.E,aFA w.value R (D*bw D F.d W*sheetPole w.value F.f)) ∧
      A.polarPoly ^D ∣R.map (algebraMap Cq.E[X] (tu Cq.E))
def c6:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (V:Variation F) (A:Pencil F),
    F.d<p→F.f.discr≠0→F.f.discr.natDegree<p →
    ∀ γ (hγ:γ∈V.marks),UnitAt F γ F.f.discr.leadingCoeff →
      Chart A γ (V.Bp hγ) (V.den γ)→RootCharge A (F.place γ) (V.den γ)
def c7:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (A:Pencil F) (w:CurvePlace L Cq.E) (B:L[X])
    (R:Cq.E[X][X]) (k :ℕ),B≠0→R≠0→aFA w.value R 0 →
    A.polarPoly ^k∣R.map (algebraMap Cq.E[X] (tu Cq.E))→RootCharge A w B →
    k*B.natDegree≤KB w.value (chargeCoeff R)
private theorem sum_charge (F:Sheet Cq z S) {g:Cq.E} (hg:g≠0)
   {T:Finset K} (hT:T⊆F.marks) {k :ℕ}
   (h : ∀ w:CurvePlace L Cq.E,w.value g≤WithZero.exp ((k*sheetPole w.value F.f :ℕ) :ℤ)) :
   ∑ γ∈T,KB (F.place γ).value g≤k*F.h:= by
 let Ju (w:CurvePlace L Cq.E) :=KB w.value g
 have hf :=(principal Cq g).2.1
 calc
   _ = ∑ w∈T.image F.place,Ju w:= by rw [sum_image (F.distinct.mono hT)]
   _ ≤ ∑ w∈hf.toFinset∪T.image F.place,Ju w :=
     sum_le_sum_of_subset_of_nonneg subset_union_right fun _ _ _=>Nat.zero_le _
   _ = ∑ᶠ w,Ju w:=(finsum_eq_finsetSum_of_support_subset Ju
     (s :=hf.toFinset∪T.image F.place) (fun w hw=>mem_union_left _ (hf.mem_toFinset.mpr hw))).symm
   _ = ∑ᶠ w:CurvePlace L Cq.E,poleOrder w.value g:=(principal Cq g).2.2.1.symm
   _≤_:=pole_sum F hg h
end
end qLXroAb
