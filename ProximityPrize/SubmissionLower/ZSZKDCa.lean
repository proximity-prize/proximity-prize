import ProximityPrize.SubmissionLower.ZJb37yc
import ProximityPrize.SubmissionLower.Zl7U3sa
set_option Elab.async false
namespace P5_7_3_5_2_1
noncomputable section
open Polynomial Finset
open P5 (K)
open qkgz7gb (PlaneCurve SmoothAt rV Weighted LowWeight)
open qt5AtZa (HeightLE)
open P5_7_3_5_2 (Sheet atPolynomial)
open qb0hmCe (CurveModel cLN)
open q1kuFjb
open cu (L FX Equation yq qD kr)
open Qt (gY Qc acG)
open E7 (CurvePlace Gb)
open Y3 (Dg embed constant)
open scoped Classical WithZero
def c1 :Prop :=
  ∀ q:PlaneCurve,Irreducible q →
    ∃ Cq:CurveModel q,Gb L Cq.E Cq.seed≤q.totalDegree
def c2 :Prop :=
  ∀ {q:PlaneCurve},Irreducible q → ∀ (Cq:CurveModel q) (s :Fin 2→L),
    SmoothAt q s→Nonempty (AtSite Cq s)
def c3:Prop :=
  ∀ {q:PlaneCurve} (Cq:CurveModel q),
    Gb L Cq.E Cq.seed≤q.totalDegree →
    ∀ (Q:Dg) (D W:ℕ),restrict Cq Q≠0→HeightLE D W Q →
      ∃ B:Factors Cq Q Q.natDegree 0 D W,
        ∀ v :CurvePlace L Cq.E,coeffIntegral v.value (restrict Cq Q) →
          ¬ v.value (headScalar (restrict Cq Q))<1 →
          coeffIntegral v.value (C B.amm) ∧ ∀ j,coeffIntegral v.value (B.f j)
private structure Sites {q:PlaneCurve} (Cq:CurveModel q) (z :K→K) (M:Finset K) where
 atSite : ∀ γ∈M,AtSite Cq (rV z γ)
 place :K→CurvePlace L Cq.E
 agrees : ∀ γ (hγ:γ∈M),place γ=(atSite γ hγ).place
 distinct :Set.InjOn place (M:Set K)
private def Sites.sheet {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {M:Finset K}
   (I:Sites Cq z M) (S:K→K[X]) (g:Cq.E[X][X]) (hi:Irreducible g)
   (hd:0<g.natDegree) (hn:headScalar g=1)
   (N :Finset K) (hN :N⊆M)
   (ok : ∀ γ (h:γ∈N),coeffIntegral (I.place γ).value g ∧
     atPolynomial (cLN (I.atSite γ (hN h)).map 0 g) (S γ)=0) :Sheet Cq z S where
 f :=g
 irreducible :=hi
 positive :=hd
 normalized:=hn
 marks :=N
 atPlace := fun γ h=>(I.atSite γ (hN h)).map
 place :=I.place
 distinct :=I.distinct.mono hN
 value := fun γ h c=> by rw [I.agrees γ (hN h),(I.atSite γ (hN h)).value c]
 arc := fun γ h=>(I.atSite γ (hN h)).arc
 integral:= fun γ h=>(ok γ h).1
 root := fun γ h=>(ok γ h).2
private structure Cover {q:PlaneCurve} (Cq:CurveModel q) (z :K→K) (S:K→K[X])
   (T:Finset K) (D W e u:ℕ) where
 n:ℕ
 part:Fin n→Sheet Cq z S
 inside : ∀ j,(part j).marks⊆T
 zJ: (T \ univ.biUnion (fun j=>(part j).marks)).card≤u*q.totalDegree
 degree : ∑ j,(part j).d≤e
 height : ∑ j,(part j).h≤u*q.totalDegree
 weight : ∀ j,(part j).weight D W
private def Cover.empty {q:PlaneCurve} (Cq:CurveModel q) (z :K→K) (S:K→K[X])
   (D W e u:ℕ) :Cover Cq z S ∅ D W e u :=
 ⟨0,Fin.elim0,fun j=>j.elim0,by simp,by simp,by simp,fun j=>j.elim0⟩
private theorem sum_cases {α:Type} {n m:ℕ} (f :Fin n→α) (g:Fin m→α) (w:α→ℕ) :
  (∑ i:Fin (n+m),w (i.addCases f g))=(∑ i,w (f i)) + ∑ i,w (g i) := by
 rw [Fin.sum_univ_add]
 simp only [Fin.addCases_left,Fin.addCases_right]
private def Cover.append {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {T₁ T₂:Finset K} {D W e₁ e₂ u₁ u₂:ℕ}
    (a :Cover Cq z S T₁ D W e₁ u₁) (b:Cover Cq z S T₂ D W e₂ u₂) :
    Cover Cq z S (T₁∪T₂) D W (e₁+e₂) (u₁+u₂) := by
  let part:Fin (a.n+b.n)→Sheet Cq z S:=Fin.addCases a.part b.part
  refine ⟨a.n+b.n,part,?_,?_,?_,?_,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left j=>simp only [part,Fin.addCases_left]; exact (a.inside j).trans subset_union_left
    | right j=>simp only [part,Fin.addCases_right]; exact (b.inside j).trans subset_union_right
  · let A:=univ.biUnion fun j=>(a.part j).marks
    let B:=univ.biUnion fun j=>(b.part j).marks
    let U:=univ.biUnion fun j=>(part j).marks
    have hA:A⊆U:= by
      intro γ hγ
      obtain ⟨j,_,hj⟩:=mem_biUnion.mp hγ
      exact mem_biUnion.mpr ⟨j.castAdd b.n,mem_univ _,by simpa [part] using hj⟩
    have hB:B⊆U:= by
      intro γ hγ
      obtain ⟨j,_,hj⟩:=mem_biUnion.mp hγ
      exact mem_biUnion.mpr ⟨j.natAdd a.n,mem_univ _,by simpa [part] using hj⟩
    have hsub: (T₁∪T₂) \ U⊆(T₁ \ A)∪(T₂ \ B) := by
      intro γ hγ
      obtain ⟨h,hn⟩:=mem_sdiff.mp hγ
      exact mem_union.mpr ((mem_union.mp h).imp
        (fun h₁=>mem_sdiff.mpr ⟨h₁,fun ha=>hn (hA ha)⟩)
        (fun h₂=>mem_sdiff.mpr ⟨h₂,fun hb=>hn (hB hb)⟩))
    exact ((card_le_card hsub).trans (card_union_le _ _)).trans
      ((Nat.add_le_add a.zJ b.zJ).trans_eq (Nat.add_mul ..).symm)
  · exact (sum_cases a.part b.part Sheet.d).le.trans (Nat.add_le_add a.degree b.degree)
  · exact (sum_cases a.part b.part Sheet.h).le.trans
      ((Nat.add_le_add a.height b.height).trans_eq (Nat.add_mul ..).symm)
  · intro i
    induction i using Fin.addCases with
    | left j=>simpa only [part,Fin.addCases_left] using a.weight j
    | right j=>simpa only [part,Fin.addCases_right] using b.weight j
private def evalMark (z :K→K) (S:K→K[X]) (γ:K) :Equation →+* FX :=
 eval₂RingHom (qD (z γ)) (kr (S γ))
private theorem single (factor :c3) {q:PlaneCurve} (hq:Irreducible q) {Cq:CurveModel q}
    (hpole :Gb L Cq.E Cq.seed≤q.totalDegree)
    {z :K→K} {S:K→K[X]} {M T:Finset K} (I:Sites Cq z M) (hT:T⊆M)
    {D W:ℕ} {f :Equation} (hf :Irreducible f) (hp:f.IsPrimitive)
    (hw:Weighted D W f) (hr : ∀ γ∈T,yq f (z γ) (S γ)=0) :
    Nonempty (Cover Cq z S T D W f.natDegree (gY f)) := by
  obtain ⟨Q,a,ha,hQ,hW⟩:=hw
  have haU:IsUnit (constant a) :=ha.isUnit.map constant
  have hQp: (embed Q).IsPrimitive := by
    apply isPrimitive_of_dvd hp
    refine ⟨constant a⁻¹,?_⟩
    rw [hQ,mul_right_comm,← map_mul,mul_inv_cancel₀ ha,map_one,one_mul]
  have hQd:Q.natDegree=f.natDegree := by
    have h:=congrArg natDegree hQ
    change (qQ9yWTb.embed Q).natDegree=(C (MvPolynomial.C a)*f).natDegree at h
    rwa [qVXVW4b.embed_degree,natDegree_C_mul (MvPolynomial.C_ne_zero.mpr ha)] at h
  have hQh:qQ9yWTb.height Q=gY f := by
    change gY (embed Q)=gY f
    rw [hQ,acG haU.ne_zero hf.ne_zero,qVXVW4b.constant_height,zero_add]
  have hQr (γ:K) (hγ:γ∈T) :yq (embed Q) (z γ) (S γ)=0:= by
    change evalMark z S γ (embed Q)=0
    rw [hQ,map_mul,show evalMark z S γ f=0 from hr γ hγ,mul_zero]
  obtain ⟨B,hB⟩:=factor Cq hpole Q D W (restrict_ne hq Cq hQp) hW
  let ec:=headScalar (restrict Cq Q)
  let E :=T.filter fun γ=>(I.place γ).value ec<1
  let N (j:Fin B.n) :=(T \ E).filter fun γ =>
    ∃ h:γ∈M,atPolynomial (cLN (I.atSite γ h).map 0 (B.f j)) (S γ)=0
  have hN (j:Fin B.n) :N j⊆T:=(filter_subset _ _).trans sdiff_subset
  have good (γ:K) (hγ:γ∈T) (hn:γ∉E) :
      let A:=I.atSite γ (hT hγ)
      ¬ A.place.value ec<1 ∧
        coeffIntegral A.place.value (C B.amm) ∧ ∀ j,coeffIntegral A.place.value (B.f j) := by
    let A:=I.atSite γ (hT hγ)
    have he : ¬ A.place.value ec<1 := fun h =>
      hn (mem_filter.mpr ⟨hγ,(I.agrees γ (hT hγ)).symm ▸ h⟩)
    exact ⟨he,hB _ (integral_at A Q) he⟩
  let part (j:Fin B.n) :=I.sheet S (B.f j) (B.irreducible j) (B.positive j)
    (B.normalized j) (N j) ((hN j).trans hT) fun γ hγ=> by
      obtain ⟨hs,_,hr⟩:=mem_filter.mp hγ
      obtain ⟨hγT,he⟩:=mem_sdiff.mp hs
      refine ⟨?_,hr⟩
      rw [I.agrees γ (hT hγT)]
      exact (good γ hγT he).2.2 j
  refine ⟨⟨B.n,part,hN,?_,?_,?_,?_⟩⟩
  · have hsub:T \ univ.biUnion (fun j=>(part j).marks)⊆E := by
      intro γ hγ
      obtain ⟨hγT,hn⟩:=mem_sdiff.mp hγ
      by_contra he
      obtain ⟨hs,hp,hf⟩:=good γ hγT he
      obtain ⟨j,hj⟩:=factor_root (I.atSite γ (hT hγT)) B (hQr γ hγT) hs hp hf
      exact hn (mem_biUnion.mpr ⟨j,mem_univ _,
        mem_filter.mpr ⟨mem_sdiff.mpr ⟨hγT,he⟩,hT hγT,hj⟩⟩)
    exact (card_le_card hsub).trans ((zero_budget T I.place (I.distinct.mono hT) B.scalar_ne).trans
      (B.scalar_height.trans_eq (congrArg (· * q.totalDegree) hQh)))
  · exact B.degree.trans_eq hQd
  · exact (Nat.le_add_left _ _).trans
      (B.height_le.trans_eq (congrArg (· * q.totalDegree) hQh))
  · intro j i hi
    have h: ((B.f j).coeff i).natDegree+i*D ≤W∨(B.f j).coeff i=0:= by
      simpa only [Nat.mul_zero,Nat.add_zero] using B.weight j i
    exact h.resolve_right hi
private theorem allocate (factor :c3) {q:PlaneCurve} (hq:Irreducible q) {Cq:CurveModel q}
    (hpole :Gb L Cq.E Cq.seed≤q.totalDegree)
    {z :K→K} {S:K→K[X]} {M:Finset K} (I:Sites Cq z M)
    {D W:ℕ} (f :Equation) (hp:f.IsPrimitive) (hw:LowWeight D W f)
    (T:Finset K) (hT:T⊆M) (hr : ∀ γ∈T,yq f (z γ) (S γ)=0) :
    Nonempty (Cover Cq z S T D W f.natDegree (gY f)) := by
  revert hp hw T
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro hp
    exact (hp.ne_zero rfl).elim
  | unit f hf =>
    intro _ _ T _ hr
    have h:T = ∅ := eq_empty_iff_forall_notMem.mpr fun γ hγ =>
      (hf.map (evalMark z S γ)).ne_zero (hr γ hγ)
    subst T
    exact ⟨Cover.empty Cq z S D W _ _⟩
  | mul a i ha hi ih =>
    intro hp hw T hT hr
    have hdi:=dvd_mul_right i a
    have hda :=dvd_mul_left a i
    let T₁:=T.filter fun γ=>yq i (z γ) (S γ)=0
    let T₂:=T \ T₁
    have h₁:T₁⊆T:=filter_subset _ _
    have h₂:T₂⊆T:=sdiff_subset
    obtain ⟨A⟩:=single factor hq hpole I (h₁.trans hT) hi
      (isPrimitive_of_dvd hp hdi) (hw i hi hdi) (fun _ h=>(mem_filter.mp h).2)
    obtain ⟨B⟩:=ih (isPrimitive_of_dvd hp hda) (fun j hj hd=>hw j hj (hd.trans hda))
      T₂ (h₂.trans hT) fun γ hγ=> by
        have h:evalMark z S γ (i*a)=0:=hr γ (h₂ hγ)
        rw [map_mul] at h
        exact (mul_eq_zero.mp h).resolve_left
          (fun he=>(mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨h₂ hγ,he⟩))
    rw [natDegree_mul hi.ne_zero ha,acG hi.ne_zero ha,← union_sdiff_of_subset h₁]
    exact ⟨A.append B⟩
theorem of_children (curve :c1) (arc :c2) (factor :c3) :P5_7_3_5_2.c1 := by
 intro D e u W T z S hz f hf he hs hw hr q hq
 obtain ⟨Cq,hpole⟩:=curve q hq
 let M:=T.filter fun γ=>SmoothAt q (rV z γ)
 have hT:M⊆T:=filter_subset _ _
 by_cases hM:M.Nonempty
 swap
 · rw [show T.filter (fun γ=>SmoothAt q (rV z γ)) = ∅ from not_nonempty_iff_eq_empty.mp hM]
   exact ⟨⟨Cq,0,Fin.elim0,fun j=>j.elim0,by simp,by simp,by simp,fun j=>j.elim0⟩⟩
 let A (γ:K) (h:γ∈M) :=Classical.choice (arc hq Cq (rV z γ) (mem_filter.mp h).2)
 let v (γ:K) :=if h:γ∈M then (A γ h).place else (A hM.choose hM.choose_spec).place
 have hv (γ:K) (h:γ∈M) :v γ=(A γ h).place :=dite_eq_left h
 have hi:Set.InjOn v (M:Set K) := by
   intro γ hγ δ hδ heq
   rw [hv γ hγ,hv δ hδ] at heq
   have h:=congrFun ((A γ hγ).site_eq_of_place (A δ hδ) heq) 0
   exact hz (hT hγ) (hT hδ) ((algebraMap K L).injective h)
 obtain ⟨R⟩:=allocate factor hq hpole ⟨A,v,hv,hi⟩ f hf.2.1 hw M Subset.rfl
   (fun γ hγ=>hr γ (hT hγ))
 have hh:=Nat.mul_le_mul_right q.totalDegree ((Qc f u).mpr hs)
 exact ⟨⟨Cq,R.n,R.part,R.inside,R.zJ.trans hh,R.degree.trans he,
   R.height.trans hh,R.weight⟩⟩
end
end P5_7_3_5_2_1
