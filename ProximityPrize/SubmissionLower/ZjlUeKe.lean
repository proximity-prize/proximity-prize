import ProximityPrize.SubmissionLower.ZfbLZnc
import ProximityPrize.SubmissionLower.Z9wTuDc
import ProximityPrize.SubmissionLower.Z8rcaBc
import ProximityPrize.SubmissionLower.ZJBzH3c
import ProximityPrize.SubmissionLower.Z9vQBQe
import ProximityPrize.SubmissionLower.ZXdt6vc
import ProximityPrize.SubmissionLower.ZTeGCOe
import ProximityPrize.SubmissionLower.ZKUXhzd
import ProximityPrize.SubmissionLower.ZO7Azpb
set_option Elab.async false
open _root_ renaming Finset → zJe, IsFractionRing.injective → zxb, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.cast_zero → zQq, Nat.mul_add → zws, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.zero_le → zD0, Polynomial.X → z7y, PowerSeries → zpm, PowerSeries.C → zMG, RingHom.comp_apply → zQb
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qkBU02c
noncomputable section
open Polynomial Finset
open P6 (K I p dw blockLength)
open P6_7_1 (Input degree)
open q9scLLa (Zk site weight slope polar lowNumerator variation_room)
open qHEUR1a (Raw embed height threshold)
open qQ9yWTb (Curve Usable)
open qb0hmCe (CurveModel)
open q1kuFjb (AtSite)
open qkgz7gb (UJ Weighted rV)
open P5_7_3_5_2 (Prepared Sheet Starts Variation BranchBudget starts)
open P5_7_7 (base base_injective hit index_card)
open cu (L)
open private Sites Sites.mk Cover.n Cover.part Cover.inside Cover.zJ Cover.degree Cover.height Cover.weight single from ProximityPrize.SubmissionLower.ZSZKDCa
open private word_budget primary_budget from ProximityPrize.SubmissionLower.ZlPdtnc
open scoped Classical BigOperators
def c1 :Prop :=P5_7_3_5_2.c2
def c2 :Prop :=qXmh4Jb.c3
private theorem prepare (x :Input) (T:zJe K) (F:Raw) (hF:q9scLLa.Sheet F)
    (hW:weight F≤threshold) (hr : ∀ γ∈T,Zk x (embed F) γ)
    (q:Curve) (hq:Irreducible q) :
    Nonempty (Prepared q x.M.label x.F.scalar (T.filter fun γ=>Usable q (site x γ))
      degree F.natDegree threshold (height F)) := by
  obtain ⟨Cq,hpole⟩:=q9Dxm8d.proof q hq
  let M:=T.filter fun γ=>Usable q (site x γ)
  change Nonempty (Prepared q x.M.label x.F.scalar M degree F.natDegree threshold (height F))
  by_cases hM:M.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hM]
    exact ⟨⟨Cq,0,Fin.elim0,fun j=>j.elim0,by simp,by simp,by simp,fun j=>j.elim0⟩⟩
  let A (γ:K) (h:γ∈M) :AtSite Cq (rV x.M.label γ) :=
    Classical.choice (qqpP4De.proof hq Cq (site x γ) (mem_filter.mp h).2)
  let v (γ:K) :=if h:γ∈M then (A γ h).place else (A hM.choose hM.choose_spec).place
  have hv (γ:K) (h:γ∈M) :v γ=(A γ h).place :=dite_eq_left h
  have hi:Set.InjOn v (M:Set K) := by
    intro γ hγ δ hδ h
    rw [hv γ hγ,hv δ hδ] at h
    have he :=congrFun ((A γ hγ).site_eq_of_place (A δ hδ) h) 0
    change algebraMap K L (x.M.label γ)=algebraMap K L (x.M.label δ) at he
    exact sub_left_inj.mp ((algebraMap K L).injective he)
  have hw:Weighted degree threshold (embed F) := by
    refine ⟨F,1,one_ne_zero,by rw [map_one,one_mul],?_⟩
    intro j m hm
    have hj:j∈F.support :=mem_support_iff.mpr fun h=>hm (by simp [h])
    have hs :=MvPolynomial.mem_support_iff.mpr hm
    exact ((Finset.le_sup (f := fun a=>((F.coeff j).coeff a).natDegree+j*degree) hs).trans
      (Finset.le_sup (f := fun i=>(F.coeff i).support.sup fun a =>
        ((F.coeff i).coeff a).natDegree+i*degree) hj)).trans hW
  have hd: (embed F).natDegree=F.natDegree :=qVXVW4b.embed_degree F
  have hp: (embed F).IsPrimitive :=hF.2.1.isPrimitive (by
    rw [hd]
    exact Nat.ne_of_gt hF.2.2.1)
  let Q:Sites Cq x.M.label M:=Sites.mk A v hv hi
  obtain ⟨R⟩:=single qkLfS5c.proof hq hpole Q Subset.rfl hF.2.1 hp hw
    (fun γ hγ=>hr γ (mem_filter.mp hγ).1)
  exact ⟨⟨Cq,Cover.n R,Cover.part R,Cover.inside R,Cover.zJ R,
    (Cover.degree R).trans_eq hd,Cover.height R,Cover.weight R⟩⟩
private theorem marks (x :Input) (T:zJe K) (hT:T⊆x.Γ) :
    UJ degree x.M.word T x.M.label x.F.scalar := by
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,?_,?_,?_⟩
  · intro γ hγ
    exact (P6_7.aic x.F (hT hγ)).trans
      (z3b (qFAh60c.emz x).2 _)
  · intro γ hγ
    let m:=x.F.mark γ (hT hγ)
    exact ⟨m.bad.support,(show P5_7.midAgreement≤dw by decide).trans m.bad.dw,
      m.scalar_hits⟩
  · obtain ⟨P,_,_,_,hP⟩:=P6_7.bW4 x.M x.F x.H x.bY
    exact ⟨x.h,(show 0<P6_7_1.packetLo by decide).trans_le (qFAh60c.emz x).1,
      P,fun γ hγ=>hP γ (hT hγ)⟩
private theorem incidence {A D:ℕ} {w:I→K} {z :K→K} {s :K→K[X]}
    {q:Curve} {C:CurveModel q} {F:Sheet C z s} (V:Variation F)
    (lg : ∀ γ∈V.marks,∃ J:zJe I,A≤J.card ∧ ∀ i∈J,hit w s γ i)
    (n v a :ℕ)
    (hn : ∀ i:I,(V.marks.filter fun γ=>hit w s γ i∧(V.num γ).eval (base i)≠0).card≤n)
    (hv : ∑ γ∈V.marks,V.DG D γ≤v)
    (ha : (V.marks.filter fun γ=>V.num γ=0).card≤a) :
    (A-D)*V.marks.card≤blockLength*n+v+(A-D)*a := by
  let good:=V.marks.filter fun γ=>V.num γ≠0
  let bad (γ:K) :=univ.filter fun i:I=>hit w s γ i∧(V.num γ).eval (base i)≠0
  have each (γ:K) (hm:γ∈good) :A-D ≤(bad γ).card+V.DG D γ:= by
    have hg:=mem_filter.mp hm
    obtain ⟨J,hJ,hr⟩:=lg γ hg.1
    let U:=J.filter fun i=>(V.num γ).eval (base i)≠0
    let zeroSites :=J.filter fun i => ¬ (V.num γ).eval (base i)≠0
    have hbad:U.card≤(bad γ).card:=card_le_card fun i hi =>
      mem_filter.mpr ⟨mem_univ _,hr i (mem_filter.mp hi).1,(mem_filter.mp hi).2⟩
    have hzero :=gR.kL.agd base base_injective
      (V.num γ) hg.2 zeroSites (fun _ hi=>not_ne_iff.mp (mem_filter.mp hi).2)
    have hsum:U.card+zeroSites.card=J.card:=card_filter_add_card_filter_not _
    have hdeg: (V.num γ).natDegree-D ≤V.DG D γ:=le_max_right _ _
    omega
  have hswap : ∑ γ∈good,(bad γ).card =
      ∑ i:I,(good.filter fun γ=>hit w s γ i∧(V.num γ).eval (base i)≠0).card:= by
    simp only [bad,card_filter]
    rw [sum_comm]
  have hb : ∑ γ∈good,(bad γ).card≤blockLength*n:= by
    rw [hswap,← index_card,← card_univ,← sum_const_nat (s :=(univ :zJe I))
      (f := fun _=>n) (fun _ _=>rfl)]
    exact sum_le_sum fun i _=>(card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hn i)
  have hs : ∑ γ∈good,V.DG D γ≤v :=
    (sum_le_sum_of_subset (filter_subset _ _)).trans hv
  have hg: (A-D)*good.card≤blockLength*n+v := by
    rw [Nat.mul_comm (A-D),← sum_const_nat (s :=good) (f := fun _=>A-D) (fun _ _=>rfl)]
    exact (sum_le_sum each).trans (sum_add_distrib.trans_le (z9f hb hs))
  have hp:=card_filter_add_card_filter_not (s :=V.marks) (fun γ=>V.num γ=0)
  change (V.marks.filter fun γ=>V.num γ=0).card+good.card=V.marks.card at hp
  rw [← hp,zws]
  exact (z9f (zBI _ ha) hg).trans_eq (by ac_rfl)
private abbrev gap:=dw-degree
private theorem sheet_count (local_test :c1) {x :Input} {T:zJe K} (hT:T⊆x.Γ)
    {q:Curve} {C:CurveModel q} {F:Sheet C x.M.label x.F.scalar}
    (R:Starts T x.M.label x.F.scalar) (hF:F.marks⊆T)
    {e except poles :ℕ} (hd:F.d≤e) (hp:e<p) (hV:BranchBudget F degree except poles) :
    gap*F.marks.card ≤
      ((except+4*e)*gap+2*e*blockLength+poles)*F.h+(4*e*gap*q.totalDegree)*F.d:= by
  obtain ⟨V,ho,hv⟩:=hV
  have hhits (γ:K) (hγ:γ∈V.marks) :
      ∃ J:zJe I,dw≤J.card ∧ ∀ i∈J,hit x.M.word x.F.scalar γ i:= by
    let m:=x.F.mark γ (hT (hF (V.Bp hγ)))
    exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
  have hn (i:I) :=word_budget local_test (w:=x.M.word) V (hd.trans_lt hp) i
  have ha :=primary_budget local_test V (hd.trans_lt hp) R (V.Bp.trans hF)
  have hg:=incidence (D:=degree) V hhits _ _ _ hn hv ha
  rw [← card_sdiff_add_card_eq_card V.Bp,zws]
  calc
    _≤gap*(except*F.h)+(blockLength*(2*F.d*F.h)+poles*F.h+gap*(4*F.d*(F.h+F.d*q.totalDegree))) :=
      z9f (zBI _ ho) hg
    _≤gap*(except*F.h)+(blockLength*(2*e*F.h)+poles*F.h+gap*(4*e*(F.h+F.d*q.totalDegree))) := by
      gcongr
    _ = _:= by ring
theorem of_children (local_test :c1) (nonlinear :c2) :q9scLLa.c1 := by
  intro x T hT F hF hW hroot q hq
  let U:=T.filter fun γ=>Usable q (site x γ)
  let e :=F.natDegree
  let H :=height F
  let Δ:=q.totalDegree
  let bw:=(6+2*e+4*e)*gap+2*e*blockLength+polar e
  let cIY:=4*e*gap*Δ
  have he :1≤e :=hF.2.2.1
  have hE :e≤12 :=hF.2.2.2.1
  have hH :1≤H :=hF.2.2.2.2.1
  obtain ⟨heD,hp,hchar,_,hlinear,hroom⟩:=variation_room he hE
  obtain ⟨P⟩:=prepare x T F hF hW hroot q hq
  let V:=univ.biUnion fun j=>(P.part j).marks
  let m:=marks x T hT
  obtain ⟨R⟩:=starts m
  have hU:U⊆T:=filter_subset _ _
  have hV:V⊆U:= by
    intro γ hγ
    obtain ⟨j,_,hj⟩:=mem_biUnion.mp hγ
    exact P.inside j hj
  have hb (j:Fin P.n) :BranchBudget (P.part j) degree (6+2*e) (polar e) := by
    let S:=P.part j
    have hd:S.d≤e :=
      (single_le_sum (fun i _=>zD0 (P.part i).d) (mem_univ j)).trans P.degree
    have hdeg : ∀ γ∈S.marks,(x.F.scalar γ).natDegree≤degree :=
      fun γ hγ=>m.degree γ (hU (P.inside j hγ))
    by_cases h:2≤S.d
    · exact nonlinear S degree e threshold (by decide) h hd hp heD hchar (P.weight j) hdeg
    · have h1 :S.d = 1 :=le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge h)) S.positive
      obtain ⟨B,ho,hv⟩:=qOdV5gc.proof S degree threshold (by decide) (by decide) h1
        (P.weight j) hdeg
      exact ⟨B,ho.trans (ztf _ (zD0 _)),
        hv.trans (ztf _ hlinear)⟩
  have hs : ∑ j,gap*(P.part j).marks.card ≤
      bw*(∑ j,(P.part j).h)+cIY*(∑ j,(P.part j).d) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    refine sum_le_sum fun j hj => ?_
    have hd:=(single_le_sum (fun i _=>zD0 (P.part i).d) hj).trans P.degree
    exact sheet_count local_test hT R ((P.inside j).trans hU) hd hp (hb j)
  have hc:gap*U.card≤lowNumerator e*H*Δ+(4*e^2*gap)*Δ:= calc
    _=gap*(U \ V).card+gap*V.card:= by rw [← zws,card_sdiff_add_card_eq_card hV]
    _≤gap*(U \ V).card + ∑ j,gap*(P.part j).marks.card:= by
      rw [← mul_sum]
      exact z3b (zBI _ card_biUnion_le) _
    _≤gap*(H*Δ)+(bw*(H*Δ)+cIY*e) :=
      z9f (zBI _ P.zJ)
        (hs.trans (z9f (zBI _ P.height) (zBI _ P.degree)))
    _ = _:= by
      dsimp only [bw,cIY,lowNumerator]
      change gap*(H*Δ)+(((6+2*e+4*e)*gap+2*e*blockLength+polar e)*(H*Δ)+(4*e*gap*Δ)*e) =
        ((7+6*e)*gap+2*e*blockLength+polar e)*H*Δ+(4*e^2*gap)*Δ
      ring
  have hbase : (4*e^2*gap)*Δ≤((4*e^2+1)*gap)*H*Δ:= by
    simpa only [Nat.mul_one] using
      ztf Δ (Nat.mul_le_mul (ztf gap
        (Nat.le_add_right (4*e^2) 1)) hH)
  have hnat :U.card≤ slope*H*Δ:= by
    apply Nat.le_of_mul_le_mul_left _ (show 0<gap by decide)
    calc
      gap*U.card≤lowNumerator e*H*Δ+((4*e^2+1)*gap)*H*Δ :=
        hc.trans (z3b hbase _)
      _=(lowNumerator e+(4*e^2+1)*gap)*H*Δ:= by ring
      _≤(slope*gap)*H*Δ:=ztf Δ (ztf H hroom)
      _=gap*(slope*H*Δ) := by ring
  exact_mod_cast hnat
end
end qkBU02c
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P5_7_1_7Q5
theorem proof :qQ9yWTb.c5:=qVkUX6a.proof
end P5_7_1_7Q5
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qnNqoXa
theorem proof :q9scLLa.c2 :=P5_7_1_7Q5.proof
end qnNqoXa
end
section
set_option autoImplicit true
namespace q5ibYGb
open P6_7_2 qigFtUb
private theorem allGrades :Prefix .tailOne 0 75 :=
  prefix_add (prefix_add (prefix_add (prefix_add batch1 batch2) batch3) batch4) batch5
theorem proof :qigFtUb.c2 := by
  rintro ⟨j,hj⟩ h hlo hhi
  have hj' : j<75:=hj
  have hc:=prefix_get allGrades hj'
  rw [Nat.zero_add,gradeTest_eq hj] at hc
  exact checked .tailOne _ _ _ (Nat.succ_pos _) hc h hlo hhi
end q5ibYGb
end
section
set_option autoImplicit true
namespace qdtleod
open P6_7_2 qigFtUb
private theorem rows :Prefix .tailTwo 0 75 :=
  prefix_add (prefix_add (prefix_add (prefix_add agi aec) acE) YE) apj
theorem proof :qigFtUb.c3:= by
  intro i h hlo hhi
  have hi:i.val<75:=i.isLt
  have ht:gradeTest .tailTwo i.val=true := by
    simpa only [Nat.zero_add] using prefix_get rows hi
  have hc:check .tailTwo (Lc i 0) (i.val+1) (seedCap i+1)=true := by
    rcases i with ⟨j,hj⟩
    rw [← gradeTest_eq hj]
    exact ht
  exact checked .tailTwo (Lc i 0) _ _ (Nat.succ_pos _) hc h hlo hhi
end qdtleod
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qjlUeKe
noncomputable section
open Polynomial
open qQ9yWTb (Curve)
open qb0hmCe (CurveModel SiteTarget cLN specialize zD)
open qFD8jve (aFA sheetPole seedPole Vanishes polarResultant)
open qbnx7gb (targetA targetB)
open P6 (K p)
open P6_7_3 (Input)
open qy95ATd (WordChart site)
open qH2fULd (Sheet targetMatch exception)
open cu (L FX)
open E7 (CurvePlace)
open P5_7_7 (phys)
open qwGrtCa (transform transform_irred)
open private coprime_eval scale reduced_test from ProximityPrize.SubmissionLower.Z66Jm5b
open private top from ProximityPrize.SubmissionLower.ZvFqJTb
open private chart_bound from ProximityPrize.SubmissionLower.ZKUXhzd
open private result_nonzero from ProximityPrize.SubmissionLower.ZEy78Hb
open private const_bound target_bound from ProximityPrize.SubmissionLower.ZlnMfEd
variable {x :Input} {U:zJe K} {J:WordChart x U} {q:Curve} {C₀:CurveModel q}
def resA (R:SiteTarget) (x :Input) (γ:K) :L :=
  R.a+R.b*site x γ R.coord
def resB (R:SiteTarget) (x :Input) (γ:K) :L :=
  R.c+R.d*site x γ R.coord
def Km (S:Sheet J C₀) (R:SiteTarget) :C₀.E[X] :=
  S.f.map (evalRingHom (algebraMap L C₀.E R.center))
structure Complement (S:Sheet J C₀) (R:SiteTarget) (t:L) :Prop where
  leading: (Km S R).eval (algebraMap L C₀.E t)≠0
  avoids : ∀ γ∈S.marks,targetMatch R J γ→t*resB R x γ - resA R x γ≠0
def changed (S:Sheet J C₀) (R:SiteTarget) (t:L) :C₀.E[X][X] :=
  transform (C (algebraMap L C₀.E t)) (C (targetA C₀ R)) 1 (C (targetB C₀ R))
    S.d (S.f.map (taylorAlgHom (algebraMap L C₀.E R.center)).toRingHom)
def markP (J:WordChart x U) (R:SiteTarget) (γ:K) :L[X] :=
  C (resB R x γ)*taylor R.center (J.P γ) - C (resA R x γ)*taylor R.center (J.Q γ)
def markQ (J:WordChart x U) (R:SiteTarget) (t:L) (γ:K) :L[X] :=
  C t*taylor R.center (J.Q γ) - taylor R.center (J.P γ)
def correction (S:Sheet J C₀) (R:SiteTarget) (t:L) (γ:K) :L[X] :=
  C (S.direction γ R.coord) *
    (C R.d*taylor R.center (J.P γ) - C R.b*taylor R.center (J.Q γ))*markQ J R t γ
private theorem atPhysical_ne (S:Sheet J C₀) (R:SiteTarget) :Km S R≠0:= by
  intro hz
  let c:=algebraMap L C₀.E R.center
  have hd:C (z7y (R:=C₀.E) - C c)∣S.f := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    apply dvd_iff_isRoot.mpr
    simpa only [Km,coeff_map,coe_evalRingHom,coeff_zero,IsRoot,c] using
      congrArg (fun f :C₀.E[X]=>f.coeff i) hz
  obtain ⟨f,hf⟩:=hd
  rcases S.irreducible.isUnit_or_isUnit hf with h | h
  · exact (irreducible_X_sub_C c).not_isUnit (isUnit_C.mp h)
  · have hp: (C (z7y (R:=C₀.E) - C c)*f).natDegree ≤
        (C (z7y (R:=C₀.E) - C c) :C₀.E[X][X]).natDegree+f.natDegree :=natDegree_mul_le
    rw [← hf,natDegree_C,natDegree_eq_zero_of_isUnit h,zero_add] at hp
    exact (not_lt_of_ge hp) S.positive
private theorem exists_complement (S:Sheet J C₀) (R:SiteTarget) : ∃ t,Complement S R t:= by
  classical
  let a :=algebraMap L C₀.E
  let B:=S.marks.image fun γ=>resA R x γ/resB R x γ
  have hroot : (a ⁻¹' {z | (Km S R).IsRoot z}).Finite :=
    (finite_setOfPred_isRoot (atPhysical_ne S R)).preimage a.injective.injOn
  obtain ⟨t,_,ht⟩:=(Set.infinite_univ : (Set.univ :Set L).Infinite).exists_notMem_finite
    (hroot.union B.finite_toSet)
  refine ⟨t,⟨fun hz=>ht (Or.inl hz),?_⟩⟩
  intro γ hγ hm hd
  have hn:resB R x γ≠0:= by
    intro hz
    have ha :resA R x γ=0:= by simpa [hz] using hd
    exact (hm.1.resolve_right (fun hn=>hn hz)) ha
  exact ht (Or.inr (Finset.mem_image.mpr ⟨γ,hγ,((eq_div_iff hn).mpr (sub_eq_zero.mp hd)).symm⟩))
private theorem mark_scale (S:Sheet J C₀) (R:SiteTarget) {γ:K}
    (hγ:γ∈S.marks) (hm:targetMatch R J γ) :
    ∃ k :L,k≠0∧(J.P γ).eval R.center=k*resA R x γ ∧
      (J.Q γ).eval R.center=k*resB R x γ:= by
  refine scale hm.1 ?_ hm.2
  by_cases h: (J.Q γ).eval R.center=0
  · exact Or.inl (coprime_eval (J.coprime γ (S.Bp hγ)) R.center h)
  · exact Or.inr h
private theorem mark_zero (S:Sheet J C₀) (R:SiteTarget) {t:L} (ht:Complement S R t)
    {γ:K} (hγ:γ∈S.marks) (hm:targetMatch R J γ) :
    (markP J R γ).coeff 0=0∧(markQ J R t γ).coeff 0≠0:= by
  constructor
  · simp only [markP,coeff_sub,coeff_C_mul,taylor_coeff_zero]
    exact sub_eq_zero.mpr (by simpa only [resA,resB,mul_comm] using hm.2)
  · obtain ⟨k,hk,hP,hQ⟩:=mark_scale S R hγ hm
    simp only [markQ,coeff_sub,coeff_C_mul,taylor_coeff_zero,hP,hQ]
    rw [show t*(k*resB R x γ) - k*resA R x γ =
        k*(t*resB R x γ - resA R x γ) by ring]
    exact mul_ne_zero hk (ht.avoids γ hγ hm)
private theorem transfer (S:Sheet J C₀) (R:SiteTarget) {t:L} (ht:Complement S R t)
    {γ:K} (hγ:γ∈S.marks) (hm:targetMatch R J γ)
    (hv :Vanishes (phys (C (t*resB R x γ - resA R x γ)) *
      (phys (taylor R.center (S.num γ))/phys (taylor R.center (S.den γ))) +
      phys (correction S R t γ))) :
    ¬ exception R S γ:= by
  have hd:taylor R.center (S.den γ)≠0:= fun h =>
    S.den_ne γ hγ ((taylor_eq_zero _ _).mp h)
  have hc:=(S.reduced γ hγ).map (taylorAlgHom R.center).toRingHom
  have h:=reduced_test hd hc (ht.avoids γ hγ hm) hv
  change (taylor R.center (S.num γ)).coeff 0=0↔_ at h
  rw [taylor_coeff_zero] at h
  obtain ⟨k,hk,hP,hQ⟩:=mark_scale S R hγ hm
  have hT: (correction S R t γ).coeff 0 =
      (k*k*(t*resB R x γ - resA R x γ))*(R.det*S.direction γ R.coord) := by
    simp only [correction,markQ,mul_coeff_zero,coeff_C_zero,coeff_sub,taylor_coeff_zero,
      hP,hQ,SiteTarget.det,resA,resB]
    ring
  intro he
  apply he.2
  rw [h,hT]
  simp only [mul_eq_zero,mul_ne_zero (mul_ne_zero hk hk) (ht.avoids γ hγ hm),false_or]
private theorem proof_bnd (S:Sheet J C₀) (R:SiteTarget) (t:L) :
    (∀ v :CurvePlace L C₀.E,
      aFA v.value (changed S R t) (sheetPole v.value S.f+S.d*seedPole C₀ R v.value)) ∧
    (∀ γ∈S.marks,aFA (S.place γ).value (changed S R t) 0) := by
  constructor
  · intro v
    apply chart_bound v S.f R.center t (targetA C₀ R) (targetB C₀ R) S.d
      (qrezXJe.sheet_bound v.value S.f)
    all_goals
      by_cases hz :R.b=0∧R.d=0
      · rw [seedPole,ite_eq_left hz]
        simpa only [targetA,targetB,hz.1,hz.2,map_zero,
          zero_mul,add_zero,zQq,WithZero.exp_zero] using const_bound v _
      · apply target_bound
        rw [seedPole,ite_eq_right hz]
        exact WithZero.le_exp_of_log_le (Int.self_le_toNat _)
  · intro γ hγ
    let v :=S.place γ
    obtain ⟨arc,ha,_,_⟩:=S.arc γ hγ
    have hseed :v.value (C₀.seed R.coord)≤WithZero.exp (0:ℤ) := by
      rw [WithZero.exp_zero,S.value γ hγ,ha]
      exact (LaurentSeries.val_le_one_iff_eq_coe L _).mpr ⟨arc R.coord,rfl⟩
    have hf :aFA v.value S.f 0:= by
      simpa only [aFA,zQq,WithZero.exp_zero,v] using S.integral γ hγ
    have h:aFA v.value (changed S R t) (0+S.d*0) :=
      chart_bound v S.f R.center t (targetA C₀ R) (targetB C₀ R) S.d hf
        (target_bound v hseed R.a R.b) (target_bound v hseed R.c R.d)
    simpa only [Nat.mul_zero,Nat.add_zero] using h
set_option backward.isDefEq.respectTransparency false in
private theorem determinant (S:Sheet J C₀) (R:SiteTarget) {t:L} (ht:Complement S R t)
    {γ:K} (hγ:γ∈S.marks) (hr :targetMatch R J γ) :
    algebraMap L C₀.E t*targetB C₀ R - targetA C₀ R≠0:= by
  intro hz
  obtain ⟨g,hg,hres,_⟩:=S.arc γ hγ
  let a :=S.atPlace γ hγ
  have hseed :a (C₀.seed R.coord)=(g R.coord:LaurentSeries L) :=hg _
  let A:=zMG R.a+PowerSeries.C R.b*g R.coord
  let B:=zMG R.c+PowerSeries.C R.d*g R.coord
  have he : ((zMG t*B - A:zpm L) :LaurentSeries L)=0:= by
    have hh:=congrArg a hz
    simpa only [A,B,targetA,targetB,map_zero,map_sub,map_add,map_mul,a.commutes,
      hseed,PowerSeries.coe_add,PowerSeries.coe_mul,PowerSeries.coe_sub,PowerSeries.coe_C,
      LaurentSeries.algebraMap_apply] using hh
  have h:=congrArg PowerSeries.constantCoeff (HahnSeries.ofPowerSeries_injective (by
    simpa only [PowerSeries.coe_zero] using he :
      ((zMG t*B - A:zpm L) :LaurentSeries L) =
        ((0:zpm L) :LaurentSeries L)))
  apply ht.avoids γ hγ hr
  simpa only [A,B,resA,resB,map_zero,map_sub,map_mul,map_add,
    PowerSeries.constantCoeff_C,hres] using h
set_option backward.isDefEq.respectTransparency false in
private theorem shape (S:Sheet J C₀) (R:SiteTarget) {t:L} (hp:S.d<p)
    (hm : ∃ γ∈S.marks,targetMatch R J γ) (ht:Complement S R t) :
    (changed S R t).natDegree=S.d∧(changed S R t).leadingCoeff.coeff 0≠0 ∧
      polarResultant (changed S R t)≠0:= by
  let m:=algebraMap L C₀.E
  let e :=(taylorEquiv (m R.center)).toRingEquiv
  let f :=S.f.map e.toRingHom
  let F:=changed S R t
  have hf :f.natDegree=S.d:=natDegree_map_eq_of_injective e.injective _
  have hF:F=transform (C (m t)) (C (targetA C₀ R)) 1 (C (targetB C₀ R)) f.natDegree f := by
    rw [hf]
    rfl
  obtain ⟨hle,htop⟩:=top (C (m t)) (C (targetA C₀ R)) (C (targetB C₀ R)) _ f le_rfl
  have hz : (F.coeff S.d).coeff 0≠0:= by
    rw [hF,← hf,htop,coeff_zero_eq_eval_zero]
    let v :=evalRingHom (0:C₀.E)
    have he :f.map v=Km S R:= by
      ext i
      simp only [f,Km,coeff_map,RingEquiv.toRingHom_eq_coe,v,coe_evalRingHom]
      change (taylor (m R.center) (S.f.coeff i)).eval 0= _
      rw [← coeff_zero_eq_eval_zero,taylor_coeff_zero]
    have hvt:v (C (m t))=m t:=eval_C
    change v (f.eval (C (m t)))≠0
    rw [← eval_map_apply,he,hvt]
    exact ht.leading
  have hdegree :F.natDegree=S.d:= by
    refine le_antisymm (by rw [hF,← hf]; exact hle) (le_natDegree_of_ne_zero fun h => ?_)
    exact hz (by rw [h,coeff_zero])
  have hleading:F.leadingCoeff.coeff 0≠0:= by simpa only [leadingCoeff,hdegree] using hz
  let i:C₀.E[X] →+* FractionRing C₀.E[X] :=algebraMap _ _
  have hi:=zxb C₀.E[X] (FractionRing C₀.E[X])
  have hdeg: (F.map i).natDegree=S.d:=(natDegree_map_eq_of_injective hi _).trans hdegree
  have hpos :0<(F.map i).natDegree :=hdeg ▸ S.positive
  have hir :Irreducible (F.map i) := by
    by_cases h:2≤S.d
    · obtain ⟨γ,hγ,hr⟩:=hm
      let D:=m t*targetB C₀ R - targetA C₀ R
      have hdet:D ≠0:=determinant S R ht hγ hr
      have hu:C D⁻¹*(C (m t)*C (targetB C₀ R) - C (targetA C₀ R)*1)=1 := by
        simpa only [map_mul,map_sub,map_one,mul_one,D] using
          congrArg (C:C₀.E →+* C₀.E[X]) (inv_mul_cancel₀ hdet)
      have hir' : Irreducible f :=(MulEquiv.irreducible_iff (Polynomial.mapEquiv e).toMulEquiv).mpr S.irreducible
      have hFirr :Irreducible F:=hF ▸ (transform_irred _ _ _ _ _ hu hir' (hf ▸ h)).1
      have hFp:0<F.natDegree :=hdegree ▸ S.positive
      exact ((hFirr.isPrimitive hFp.ne').irreducible_iff_irreducible_map_fraction_map
        (K:=FractionRing C₀.E[X])).mp hFirr
    · apply irreducible_of_degree_eq_one
      rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hpos),hdeg]
      have :=S.positive
      exact_mod_cast (show S.d = 1 by omega)
  exact ⟨hdegree,hleading,result_nonzero F (hdegree ▸ S.positive) (hdegree ▸ hp) hir⟩
section loc
open TrivSqZeroExt
open qFe6O4d (lift_change eval_change constant_coe eval_phys center_specialize change_denominator parameter_change first_order)
open q1kuFjb (IntSeries Ua mapTwice map_liftAt)
open qJai0ob (pair scalar seriesJet evalAt eval_seriesJet)
open private constant τ center center_poly jet_constant jet_linear from ProximityPrize.SubmissionLower.ZFdiUYb
private theorem phys_ne {g:L[X]} (h:g≠0) :phys g≠0 :=
  (map_ne_zero_iff _ (zxb L[X] FX)).mpr h
private theorem proof_loc (S:Sheet J C₀) (R:SiteTarget) (t:L) (ht:Complement S R t)
    (γ:K) (hγ:γ∈S.marks) (hr :targetMatch R J γ) :
    let F:=changed S R t
    let a :=S.atPlace γ hγ
    let P:=markP J R γ
    let Q:=markQ J R t γ
    aFA (S.place γ).value F 0 →
    specialize (cLN a 0 F) P Q=0 ∧
    specialize (cLN a 0 F).derivative P Q≠0 ∧
    zD a F P Q =
      phys (C (t*resB R x γ - resA R x γ)) *
        (phys (taylor R.center (S.num γ))/phys (taylor R.center (S.den γ))) +
      phys (correction S R t γ) := by
  let a :=S.atPlace γ hγ
  let F:=changed S R t
  let P:=markP J R γ
  let Q:=markQ J R t γ
  change aFA (S.place γ).value F 0 →
    specialize (cLN a 0 F) P Q=0 ∧
    specialize (cLN a 0 F).derivative P Q≠0 ∧
    zD a F P Q =
      phys (C (t*resB R x γ - resA R x γ)) *
        (phys (taylor R.center (S.num γ))/phys (taylor R.center (S.den γ))) +
      phys (correction S R t γ)
  intro hInt
  let hF i j:=(S.value γ hγ ((F.coeff i).coeff j)).symm.trans_le
    (show (S.place γ).value ((F.coeff i).coeff j)≤1 by
      simpa only [zQq,WithZero.exp_zero] using hInt i j)
  let hf i j:=(S.value γ hγ _).symm.trans_le (S.integral γ hγ i j)
  let p₀:=phys (taylor R.center (J.P γ))
  let q₀:=phys (taylor R.center (J.Q γ))
  let a₀:=scalar (resA R x γ)
  let b₀:=scalar (resB R x γ)
  let a₁:=scalar (R.b*S.direction γ R.coord)
  let b₁:=scalar (R.d*S.direction γ R.coord)
  let T:=scalar t
  let m:=T*q₀-p₀
  let D:=T*b₀-a₀
  let k :=(b₁*p₀-a₁*q₀)*m
  let w:=(b₀*p₀-a₀*q₀)/m
  let y :=p₀/q₀
  have hq:q₀≠0 :=
    phys_ne (fun h=>J.denominator γ (S.Bp hγ) ((taylor_eq_zero R.center _).mp h))
  have hM:phys Q=m:= by
    simp only [Q,markQ,m,T,p₀,q₀,scalar,zQb,map_mul,map_sub]
  have hP:phys P=b₀*p₀-a₀*q₀:= by
    simp only [P,markP,a₀,b₀,p₀,q₀,scalar,zQb,map_mul,map_sub]
  have hm:m≠0:=hM ▸ phys_ne (fun h=>(mark_zero S R ht hγ hr).2
    (by change Q.coeff 0=0; rw [h,coeff_zero]))
  have hDmap :phys (C (t*resB R x γ-resA R x γ))=D:= by
    simp only [D,a₀,b₀,T,← map_mul,← map_sub,scalar,zQb]
  have hD:D ≠0:=hDmap ▸ phys_ne (C_ne_zero.mpr (ht.avoids γ hγ hr))
  have hz :b₀+w≠0:= by
    change b₀+(b₀*p₀-a₀*q₀)/(T*q₀-p₀)≠0
    rw [change_denominator p₀ q₀ a₀ b₀ T hm]
    exact div_ne_zero (mul_ne_zero hD hq) hm
  obtain ⟨g,hg,hg₀,_⟩:=S.arc γ hγ
  have hg₁ :PowerSeries.coeff 1 (g R.coord)=S.direction γ R.coord:= by
    rw [Sheet.direction,dite_eq_left hγ,hg]
    exact (LaurentSeries.coeff_coe_powerSeries (g R.coord) 1).symm
  let g' := (LaurentSeries.powerSeriesEquivSubring L) (g R.coord)
  let A:=constant R.a+constant R.b*g'
  let B:=constant R.c+constant R.d*g'
  have hA: (A:LaurentSeries L)=a (targetA C₀ R) := by
    simp only [A,g',targetA,Subring.coe_add,Subring.coe_mul,constant_coe a,
      LaurentSeries.powerSeriesEquivSubring_coe_apply,a,hg,map_add,map_mul]
  have hB: (B:LaurentSeries L)=a (targetB C₀ R) := by
    simp only [B,g',targetB,Subring.coe_add,Subring.coe_mul,constant_coe a,
      LaurentSeries.powerSeriesEquivSubring_coe_apply,a,hg,map_add,map_mul]
  have hAj:seriesJet A=pair a₀ a₁:= by
    simpa only [A,g',a₀,a₁,resA,hg₀,hg₁] using jet_linear (g R.coord) R.a R.b
  have hBj:seriesJet B=pair b₀ b₁:= by
    simpa only [B,g',b₀,b₁,resB,hg₀,hg₁] using jet_linear (g R.coord) R.c R.d
  have hLift:=lift_change a S.f hf (algebraMap L C₀.E R.center) (algebraMap L C₀.E t)
    (targetA C₀ R) (targetB C₀ R) (constant R.center) (constant t) A B S.d
    (constant_coe a _) (constant_coe a _) hA hB hF
  have hdeg: (Ua a S.f hf).natDegree≤S.d:= by
    have hi:=Polynomial.map_injective (f :=IntSeries.subtype) Subtype.val_injective
    have h:=natDegree_map_eq_of_injective (f :=mapRingHom IntSeries.subtype) hi (Ua a S.f hf)
    change (mapTwice IntSeries.subtype (Ua a S.f hf)).natDegree= _ at h
    rw [map_liftAt] at h
    rw [← h]
    exact natDegree_map_le
  let ev₀:=eval₂RingHom scalar (τ+scalar R.center)
  let J₀ (i:ℤ) :=(cLN a i S.f).eval₂ ev₀ y
  let j:=(cLN a 0 S.f).derivative.eval₂ ev₀ y
  let ev₁:=eval₂RingHom scalar τ
  let I₀ (i:ℤ) :=(cLN a i F).eval₂ ev₁ w
  let i:=(cLN a 0 F).derivative.eval₂ ev₁ w
  let φ:=phys (taylor R.center (S.num γ))/phys (taylor R.center (S.den γ))
  have hj₀:J₀ 0=0:= by
    simpa only [J₀,a,ev₀,y,p₀,q₀,center_specialize,map_zero] using
      congrArg (center R.center) (S.root γ hγ)
  have hj:j≠0:= by
    simpa only [j,a,ev₀,y,p₀,q₀,center_specialize,map_zero] using
      (center R.center).injective.ne (S.simple γ hγ)
  have hφ:φ = -(J₀ 1/j)*q₀^2 := by
    simpa only [φ,a,J₀,j,ev₀,y,p₀,q₀,zD,map_mul,map_neg,map_div₀,map_pow,
      center_poly,center_specialize] using congrArg (center R.center) (S.formula γ hγ)
  have he (u:FX) :
      pair (I₀ 0) (I₀ 1+u*i) =
        (pair b₀ b₁+pair w u)^S.d*pair 0 (J₀ 1+((m^2*u-k)/(D*q₀^2))*j) := by
    let W:=pair w u
    let Y' := pair y ((m^2*u-k)/(D*q₀^2))
    have h:=parameter_change p₀ q₀ a₀ b₀ a₁ b₁ T u hq hm hD
    have heval :seriesJet A+seriesJet (constant t)*W=(seriesJet B+W)*Y' := by
      rw [hAj,hBj,jet_constant]
      exact h
    have h' := congrArg (evalAt seriesJet (inl τ) W) hLift
    change evalAt seriesJet (inl τ) W (Ua a F hF)= _ at h'
    rw [eval_change seriesJet (inl τ) W Y' _ hdeg _ _ _ _ heval,
      jet_constant,← inl_add] at h'
    dsimp only [W,Y'] at h'
    rw [eval_seriesJet,eval_seriesJet,hBj] at h'
    change pair (I₀ 0) (I₀ 1+u*i) =
      (pair b₀ b₁+pair w u)^S.d*pair (J₀ 0) (J₀ 1+((m^2*u-k)/(D*q₀^2))*j) at h'
    simpa only [hj₀] using h'
  obtain ⟨hi₀,hi,htan⟩:=first_order S.d b₀ b₁ w q₀ m D k φ (J₀ 1) j (I₀ 0) (I₀ 1) i
    hz hq hm hD hj hφ he
  have hw:w=phys P/phys Q:= by rw [hP,hM]
  have hk :phys (correction S R t γ)=k := by
    dsimp only [correction,k,a₁,b₁,p₀,q₀]
    rw [map_mul,map_mul,map_sub,map_mul,map_mul,hM]
    simp only [map_mul,scalar,zQb]
    ring
  refine ⟨?_,?_,?_⟩
  · simpa only [I₀,ev₁,eval_phys,hw,specialize] using hi₀
  · simpa only [i,ev₁,eval_phys,hw,specialize] using hi
  · simpa only [i,I₀,φ,ev₁,eval_phys,hw,← hM,← hDmap,← hk,zD,specialize] using htan
end loc
theorem proof :qylJznc.c1 := by
  intro x U J q C₀ S hp R hm
  obtain ⟨t,ht⟩:=exists_complement S R
  obtain ⟨hdegree,hleading,hseparant⟩:=shape S R hp hm ht
  obtain ⟨hbound,hintegral⟩:=proof_bnd S R t
  refine ⟨⟨changed S R t,hdegree,hleading,hseparant,hbound,hintegral,?_⟩⟩
  intro γ hγ hr
  obtain ⟨hP,hQ⟩:=mark_zero S R ht hγ hr
  obtain ⟨hroot,hsimple,htangent⟩:=proof_loc S R t ht γ hγ hr (hintegral γ hγ)
  refine ⟨markP J R γ,markQ J R t γ,hP,hQ,hroot,hsimple,?_⟩
  rw [htangent]
  exact transfer S R ht hγ hr
end
end qjlUeKe
end
