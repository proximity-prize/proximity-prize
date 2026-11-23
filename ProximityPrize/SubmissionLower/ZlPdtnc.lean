import ProximityPrize.SubmissionLower.ZIbuJkc
import ProximityPrize.SubmissionLower.ZfWgThc
set_option Elab.async false
namespace P5_7_3_5_2
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (K I p blockLength)
open P5_7 (midAgreement)
open qkgz7gb (PlaneCurve SmoothAt rV CurveOK LowWeight UJ branchDegree smoothRate ceilDiv)
open qb0hmCe (CurveModel SiteTarget)
open P5_7_7 (base hit)
open cu (L Equation vm yq j9)
open Dt (Reduced)
def c1 :Prop :=
  ∀ (D e u W:ℕ) (T:Finset K) (z :K→K) (S:K→K[X]),
    Set.InjOn z (T:Set K) → ∀ f :Equation,Reduced f→f.natDegree≤e→vm f u →
      LowWeight D W f→(∀ γ∈T,yq f (z γ) (S γ)=0) →
      ∀ q:PlaneCurve,Irreducible q →
        Nonempty (Prepared q z S (T.filter fun γ=>SmoothAt q (rV z γ)) D e W u)
def c2 :Prop :=
  ∀ {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet C z S} (V:Variation F),F.d<p → ∀ R:SiteTarget,
      (V.marks.filter (exception V R)).card≤2*F.d*(F.h+F.d*R.height q)
def c3:Prop :=
  ∀ {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet C z S) (D e W v :ℕ),CurveOK D e W (.symmetric v) →
      F.d≤e→F.weight D W→(∀ γ∈F.marks,(S γ).natDegree≤D) →
      BranchBudget F D (2*e) (2*e*(2*branchDegree D e W (.symmetric v)-1))
def c4 :Prop :=
  ∀ {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet C z S) (D e W v₁ v₂:ℕ),CurveOK D e W (.asymmetric v₁ v₂) →
      F.d≤e→F.weight D W→(∀ γ∈F.marks,(S γ).natDegree≤D) →
      BranchBudget F D (6+2*e) ((2*e-2)*(2*branchDegree D e W (.asymmetric v₁ v₂)-1)+4*W)
private theorem word_budget (local_test :c2) {w:I→K}
  {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
  {F:Sheet C z S} (V:Variation F) (hp:F.d<p) (i:I) :
  (V.marks.filter fun γ=>hit w S γ i∧(V.num γ).eval (base i)≠0).card≤2*F.d*F.h:= by
 let R:SiteTarget :=⟨base i,0,algebraMap K L (w i),0,1,0⟩
 have h:=local_test V hp R
 have h0:R.height q=0:= by simp [SiteTarget.height,R]
 rw [h0,Nat.mul_zero,Nat.add_zero] at h
 refine (card_le_card ?_).trans h
 intro γ hγ
 obtain ⟨hV,hm,hn⟩:=mem_filter.mp hγ
 change (S γ).eval (P5.node i)=w i at hm
 have he : (j9 (S γ)).eval (base i)=algebraMap K L (w i) := by
  rw [j9,base,Polynomial.eval_map,Polynomial.eval₂_hom,hm]
 have hmatch :targetHit R z S γ:= by simp [targetHit,R,he]
 exact mem_filter.mpr ⟨hV,hmatch,fun hh=>hn (hh.mpr (Or.inl (by simp [SiteTarget.det,R])))⟩
private theorem primary_budget (local_test :c2) {T:Finset K}
   {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
   {F:Sheet C z S} (V:Variation F) (hp:F.d<p) (R:Starts T z S) (hT:V.marks⊆T) :
   (V.marks.filter fun γ=>V.num γ=0).card≤4*F.d*(F.h+F.d*q.totalDegree) := by
 let bad (i:Fin 2) :=V.marks.filter (exception V (R.target i))
 have hb (i:Fin 2) : (bad i).card≤2*F.d*(F.h+F.d*q.totalDegree) := by
   have hh: (R.target i).height q≤q.totalDegree := by unfold SiteTarget.height; split <;> omega
   exact (local_test V hp (R.target i)).trans (by gcongr)
 have hc:V.marks.filter (fun γ=>V.num γ=0)⊆bad 0∪bad 1 := by
   intro γ hγ
   obtain ⟨hV,hn⟩:=mem_filter.mp hγ
   have hF:=V.Bp hV
   obtain ⟨a,ha,_,i,hi⟩:=F.arc γ hF
   have hd:F.direction γ (R.target i).coord≠0:= by
     rw [R.coordinate,Sheet.direction,dite_eq_left hF,ha i]
     exact fun hz=>hi ((LaurentSeries.coeff_coe_powerSeries (a i) 1).symm.trans hz)
   have hr :γ∈bad i:=mem_filter.mpr ⟨hV,R.lg γ (hT hV) i,fun hh =>
     ((hh.mp (by simp [hn])).elim (R.invertible i) hd)⟩
   fin_cases i
   · exact mem_union_left _ hr
   · exact mem_union_right _ hr
 exact ((card_le_card hc).trans (card_union_le _ _)).trans
   ((Nat.add_le_add (hb 0) (hb 1)).trans_eq (by ring))
private theorem sheet_count (local_test :c2) {T:Finset K} {w:I→K} {D:ℕ}
   {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
   (m:UJ D w T z S) (R:Starts T z S) {F:Sheet C z S} (hT:F.marks⊆T)
   {e except poles :ℕ} (hd:F.d≤e) (hp:e<p) (hV:BranchBudget F D except poles) :
   gap D *F.marks.card ≤
     ((except+4*e)*gap D+2*e*blockLength+poles)*F.h+(4*e*gap D*q.totalDegree)*F.d:= by
 obtain ⟨V,ho,hv⟩:=hV
 have hsub:=V.Bp.trans hT
 have hn (i:I) :=word_budget local_test (w:=w) V (hd.trans_lt hp) i
 have ha :=primary_budget local_test V (hd.trans_lt hp) R hsub
 have hg:=incidence m V hsub _ _ _ hn hv ha
 rw [← card_sdiff_add_card_eq_card V.Bp,Nat.mul_add]
 calc
   _≤gap D*(except*F.h)+(blockLength*(2*F.d*F.h)+poles*F.h+gap D*(4*F.d*(F.h+F.d*q.totalDegree))) :=
     Nat.add_le_add (Nat.mul_le_mul_left _ ho) hg
   _≤gap D*(except*F.h)+(blockLength*(2*e*F.h)+poles*F.h+gap D*(4*e*(F.h+F.d*q.totalDegree))) := by
     gcongr
   _ = _:= by ring
private theorem prepared_count (local_test :c2) {T U:Finset K} {w:I→K} {D:ℕ}
    {q:PlaneCurve} {z :K→K} {S:K→K[X]} (m:UJ D w T z S) (hU:U⊆T)
    {e W u except poles :ℕ} (Q:Prepared q z S U D e W u)
    (hD:D < midAgreement) (hp:e<p)
    (branches : ∀ j,BranchBudget (Q.part j) D except poles) :
    U.card≤((1+except+4*e)*u+ceilDiv (u*(2*e*blockLength+poles)) (gap D)+4*e*e)*q.totalDegree := by
  obtain ⟨R⟩:=starts m
  let g:=gap D
  let Δ:=q.totalDegree
  let V:=univ.biUnion fun j=>(Q.part j).marks
  let pole :=2*e*blockLength+poles
  let bw:=(except+4*e)*g+pole
  have hsub:V⊆U:= fun γ hγ=> by
    obtain ⟨j,_,hj⟩:=mem_biUnion.mp hγ
    exact Q.inside j hj
  have hsum : ∑ j,g*(Q.part j).marks.card≤bw*(∑ j,(Q.part j).h)+(4*e*g*Δ)*(∑ j,(Q.part j).d) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    have hd:=(single_le_sum (fun i _=>Nat.zero_le (Q.part i).d) hj).trans Q.degree
    simpa only [bw,pole,add_assoc] using
      sheet_count local_test m R ((Q.inside j).trans hU) hd hp (branches j)
  have hcard:V.card ≤ ∑ j,(Q.part j).marks.card:=card_biUnion_le
  have hg:0<g:=Nat.sub_pos_of_lt hD
  have hc:u*pole≤g*ceilDiv (u*pole) g:=ceil_mul hg
  apply Nat.le_of_mul_le_mul_left _ hg
  calc
    g*U.card=g*(U \ V).card+g*V.card:= by
      rw [← Nat.mul_add,card_sdiff_add_card_eq_card hsub]
    _≤g*(U \ V).card + ∑ j,g*(Q.part j).marks.card:= by
      rw [← mul_sum]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hcard) _
    _≤g*(u*Δ)+(bw*(u*Δ)+(4*e*g*Δ)*e) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ Q.zJ)
        (hsum.trans (Nat.add_le_add (Nat.mul_le_mul_left _ Q.height) (Nat.mul_le_mul_left _ Q.degree)))
    _=g*((1+except+4*e)*u+4*e*e)*Δ+(u*pole)*Δ:= by dsimp only [bw]; ring
    _≤g*((1+except+4*e)*u+4*e*e)*Δ+(g*ceilDiv (u*pole) g)*Δ :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _
    _ = _:= by change _=g*(((1+except+4*e)*u+ceilDiv (u*pole) g+4*e*e)*Δ); ring
theorem of_children (prep:c1) (local_test :c2) (symmetric:c3) (asymmetric:c4) :qkgz7gb.c2 := by
 intro D e u W s hok w T z S M f hf he hu hw hr q hq
 obtain ⟨Q⟩:=prep D e u W T z S M.Kw f hf he hu hw hr q hq
 have hd (j:Fin Q.n) : (Q.part j).d≤e :=
   (single_le_sum (fun i _=>Nat.zero_le (Q.part i).d) (mem_univ j)).trans Q.degree
 have hs : (T.filter fun γ=>SmoothAt q (rV z γ))⊆T:=filter_subset _ _
 have hn (j:Fin Q.n) : ∀ γ∈(Q.part j).marks,(S γ).natDegree≤D :=
   fun γ hγ=>M.degree γ (hs (Q.inside j hγ))
 cases s with
 | symmetric v =>
   have h:=prepared_count local_test M hs Q hok.2.1 hok.2.2.2.1
     (fun j=>symmetric (Q.part j) D e W v hok (hd j) (Q.weight j) (hn j))
   simpa only [smoothRate,gap,show 1+2*e+4*e=1+6*e by ring] using h
 | asymmetric v₁ v₂ =>
   have h:=prepared_count local_test M hs Q hok.2.1 hok.2.2.2.1
     (fun j=>asymmetric (Q.part j) D e W v₁ v₂ hok (hd j) (Q.weight j) (hn j))
   simpa only [smoothRate,gap,show 1+(6+2*e)+4*e=7+6*e by ring] using h
end
end P5_7_3_5_2
