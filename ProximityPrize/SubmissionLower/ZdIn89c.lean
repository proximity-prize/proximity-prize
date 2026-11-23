import ProximityPrize.SubmissionLower.ZPahZ1a
import ProximityPrize.SubmissionLower.ZRtQEca
import ProximityPrize.SubmissionLower.ZalmDpd
import ProximityPrize.SubmissionLower.Zt62ONe
import ProximityPrize.SubmissionLower.ZnGdvBe
import ProximityPrize.SubmissionLower.ZKgVGSb
import ProximityPrize.SubmissionLower.ZDbTvLe
import ProximityPrize.SubmissionLower.ZRYXIua
import ProximityPrize.SubmissionLower.ZflC1Fd
import ProximityPrize.SubmissionLower.ZPKTqyb
import ProximityPrize.SubmissionLower.Z32V4rd
import ProximityPrize.SubmissionLower.ZiH02Bd
import ProximityPrize.SubmissionLower.ZAJiURc
import ProximityPrize.SubmissionLower.ZLWPQ5c
import ProximityPrize.SubmissionLower.ZEe4bHc
import ProximityPrize.SubmissionLower.ZAZ7Tec
import ProximityPrize.SubmissionLower.ZKtTCEc
import ProximityPrize.SubmissionLower.ZoOOLsc
import ProximityPrize.SubmissionLower.ZvIni8b
set_option Elab.async false
section
set_option autoImplicit true
namespace qQY9Ybc
theorem proof :qpDASwe.c2 :=
  qvWbALd.of_children q9aDOab.proof qmpFDTd.proof
end qQY9Ybc
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace q5KzNpb
noncomputable section
open Polynomial Finset
open P6 (K p)
open qZfVj1b (pivot)
open qK3TPae (regular)
open quN7Z4a (Sheet physicalWeight)
open qRoCwuc (dSG)
open qkgz7gb (rV)
open q1kuFjb (AtSite)
open Cu
open scoped Classical WithZero
open private curve b5S normal_degree normal_irreducible normal_monic pivot_ne at_normal from ProximityPrize.SubmissionLower.ZPaaHRd
attribute [local instance] qZfVj1b.gRK
private theorem normal_weight {Q:sQ} [Fact (Irreducible Q)] {J e H T z s}
    (S:Sheet Q J e H T z s) {W:ℕ} (hw:physicalWeight P6_7_3.degree S.root.equation≤W) :
    ∀ i,(qZfVj1b.normalize S.root.equation).coeff i≠0 →
      ((qZfVj1b.normalize S.root.equation).coeff i).natDegree+i*P6_7_3.degree≤W:= by
  intro i hi
  simp only [qZfVj1b.normalize,coeff_C_mul] at hi ⊢
  rw [natDegree_C_mul (inv_ne_zero (b5S S))]
  exact (Finset.le_sup (f := fun i=>(S.root.equation.coeff i).natDegree+i*P6_7_3.degree)
    (mem_support_iff.mpr (right_ne_zero_of_mul hi))).trans hw
theorem proof :qvCjzac.c2 := by
  intro Q _ J T z s e H W S hz he hpe hw
  have hp:Q.totalDegree<p:=(Nat.le_mul_of_pos_right _ he).trans_lt hpe
  obtain ⟨v,hc,hh⟩:=P5_7_1_5Q.c4321 Q hp
  let Cq:=curve hc hh
  let U:=regular Q z T
  have hU:U⊆T:=filter_subset _ _
  let G:=U.filter fun γ=>MvPolynomial.eval (S.parameter γ) (pivot S)≠0
  have hG:G⊆U:=filter_subset _ _
  have hcut: (U \ G).card≤H := by
    have hb:=dSG S hz (pivot S) (pivot_ne S) (U \ G)
      (fun _ hg=>hU (mem_sdiff.mp hg).1) (fun γ hg=> by
        by_contra hn
        exact (mem_sdiff.mp hg).2 (mem_filter.mpr ⟨(mem_sdiff.mp hg).1,hn⟩))
    simpa only [one_mul] using hb.trans (Nat.mul_le_mul_right H (S.bY.degree.2 _ _))
  let lift (γ:K) (hγ:γ∈G) :=
    Classical.choice (quwKLBd.proof S.bY hp hc (z γ) (S.parameter γ)
      (S.onBase γ (hU (hG hγ))))
  let A (γ:K) (hγ:γ∈G) :AtSite Cq (rV z γ) := by
    let B:=lift γ hγ
    refine ⟨B.map,B.place,B.value,?_⟩
    let b (i:Fin 2) :=B.series (qBajpRb.cls S.bY (MvPolynomial.X (Sum.inl i)))
    have hb (i:Fin 2) :B.map (Cq.seed i)=(b i:LaurentSeries cu.L) := by
      rw [B.lift_eq,qBajpRb.incl_cls]
      simp [qBajpRb.ek,Cq,curve]
    have hres (i:Fin 2) :PowerSeries.constantCoeff (b i)=rV z γ i:= by
      rw [B.reduce,qBajpRb.atMark_cls,MvPolynomial.eval_X]
      rfl
    exact ⟨b,hb,hres,qyEseja.proof _ hp (S.onSeed γ (hU (hG hγ)))
      (mem_filter.mp (hG hγ)).2 B.place B.map B.value b hb hres⟩
  let place (γ:K) :E7.CurvePlace cu.L Cq.E :=if hγ:γ∈G then (A γ hγ).place else v
  have hplace (γ:K) (hγ:γ∈G) :place γ=(A γ hγ).place :=dite_eq_left hγ
  have hd:=normal_degree S
  let F:P5_7_3_5_2.Sheet Cq z s := {
    f :=qZfVj1b.normalize S.root.equation
    irreducible :=normal_irreducible S
    positive :=hd.symm ▸ he
    normalized:=normal_monic S
    marks :=G
    atPlace := fun γ hγ=>(A γ hγ).map
    place :=place
    distinct := by
      intro γ hγ δ hδ hh
      rw [hplace γ hγ,hplace δ hδ] at hh
      exact hz (hU (hG hγ)) (hU (hG hδ))
        ((algebraMap K cu.L).injective (congrFun ((A γ hγ).site_eq_of_place (A δ hδ) hh) 0))
    value := fun γ hγ c =>
      (congrArg (fun w:E7.CurvePlace cu.L Cq.E=>w.value c) (hplace γ hγ)).trans
      ((A γ hγ).value c)
    arc := fun γ hγ=>(A γ hγ).arc
    integral:= fun γ hγ i j=> by
      exact (congrArg (fun w:E7.CurvePlace cu.L Cq.E =>
        w.value (((qZfVj1b.normalize S.root.equation).coeff i).coeff j)) (hplace γ hγ)).trans_le
          ((at_normal S (hγ:=hU (hG hγ)) (lift γ hγ) (mem_filter.mp hγ).2).1 i j)
    root := fun γ hγ=>(at_normal S (hγ:=hU (hG hγ)) (lift γ hγ) (mem_filter.mp hγ).2).2 }
  exact ⟨Cq,F,hd,P5_7_1_5Q.c4322 S.bY hc S.height,normal_weight S hw,hG,hcut⟩
end
end q5KzNpb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qdirDXc
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K p)

open E7 (KB)
open P6_7_3 (degree)
open qvCjzac (polarDegree poleFee)
open qb0hmCe (CurveModel)

open qFD8jve (aFA)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qxPDCsa (discDegree Good)
open qLXroAb (chargeCoeff)
open private choose_variation restrict zJ height_zero from ProximityPrize.SubmissionLower.Zay1XCa
open private sum_charge from ProximityPrize.SubmissionLower.ZFqQTue
theorem children :
    qLXroAb.c1∧qLXroAb.c2∧qLXroAb.c3∧qLXroAb.c4 ∧
    qLXroAb.c5∧qLXroAb.c6∧qLXroAb.c7 :=
  ⟨qTLMB9a.proof,qoyAGrd.proof,
   qb1WXKc.of_children qB4SPFa.proof qvlURsa.proof,
   q9uVqha.of_children qGnKhWc.proof qralmib.proof
     qBMP0Kd.proof qi87Bgb.proof q2ANK6b.proof
     qk9SLHb.proof,
   qfzuawb.of_children
     (qHJDQEb.of_children qK8v0ue.proof qIPidRd.proof
       q1XnGpd.proof)
     (qnSUPza.of_children P5_7_1_5Q.c434521 P5_7_1_5Q.c434522)
     qkEA7Vd.proof,
   qZn79Eb.of_children qOHrlse.proof qydrhVa.proof
     qi1t4Ta.proof P5_7_1_5Q.c43464,
   qXARP7c.proof⟩
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
  {F:Sheet Cq z S}
private theorem disc_le {e W:ℕ} (he :0<e) (hW:e*degree≤W) :
    discDegree degree e W≤polarDegree e W:= by
  have h₁: (2*e-1)*W=(2*e-2)*W+W:= by
    rw [← Nat.add_one_mul,show 2*e-2+1=2*e-1 by omega]
  have h₂:e*e*degree=e*(e-1)*degree+e*degree := calc
    _=e*(e-1+1)*degree := by rw [Nat.sub_add_cancel he]
    _ = _:= by ring
  rw [qxPDCsa.discDegree,polarDegree,h₁,h₂]
  omega
theorem proof :qvCjzac.c4 := by
  obtain ⟨disc,refs,infty,bY,elim,orders,norm⟩:=children
  intro q Cq z S F e W hd he hp hW hguard hw hS
  have he' : 3≤F.d:=hd ▸ he
  have hp' : F.d<p:=hd ▸ hp
  obtain ⟨hδ,hδd,hδb,hsimple⟩:=disc F degree W hp' hw
  have hδp:F.f.discr.natDegree<p :=
    (hδd.trans (hd.symm ▸ disc_le (by omega) hW)).trans_lt hguard
  obtain ⟨V,hV⟩:=choose_variation F hsimple
  obtain ⟨A⟩:=refs V degree W hw
  let T:=F.marks.filter (Good A)
  have hT:T⊆F.marks :=filter_subset _ _
  have ht:T⊆V.marks := by
    rw [hV]
    exact fun γ hγ=>mem_filter.mpr ⟨hT hγ,(mem_filter.mp hγ).2.1⟩
  let U:=restrict V ht
  obtain ⟨P,hchart⟩:=bY U he' hp'
  have hD:0<degree := by decide
  obtain ⟨R,hR,hb,hdiv⟩:=elim P degree W he' hD (by decide) (hd ▸ hW) hw
  have hc:chargeCoeff R≠0:=leadingCoeff_ne_zero.mpr (trailingCoeff_nonzero_iff_nonzero.mpr hR)
  have hbound:=sum_charge F hc hT (fun w=>hb w R.natTrailingDegree R.trailingCoeff.natDegree)
  have hlocal (γ:K) (hγ:γ∈T) :degree*U.DG degree γ ≤
      KB (F.place γ).value (chargeCoeff R) := by
    have hg:=(mem_filter.mp hγ).2
    have hi:=infty A hp' hw γ (ht hγ) hg (hS γ (hT hγ))
    have hv :=orders U P hp' hδ hδp γ hγ hg.1 (hchart γ hγ).some
    have hbr :aFA (F.place γ).value R 0:= by
      simpa only [height_zero (hT hγ),Nat.mul_zero] using hb (F.place γ)
    have hn:=norm P (F.place γ) (U.den γ) R degree (U.den_ne γ hγ) hR hbr hdiv hv
    change degree*max (U.den γ).natDegree ((U.num γ).natDegree-degree)≤_
    rw [max_eq_left (by change (V.num γ).natDegree-degree≤(V.den γ).natDegree; omega)]
    exact hn
  refine ⟨U,(zJ A hδ hδb).trans (Nat.mul_le_mul_right _ (by omega)),?_⟩
  apply Nat.le_of_mul_le_mul_left _ hD
  change degree*(∑ γ∈T,U.DG degree γ)≤degree*(poleFee e W*F.h)
  rw [mul_sum]
  refine (sum_le_sum hlocal).trans (hbound.trans_eq ?_)
  rw [hd]
  exact mul_assoc degree (poleFee e W) F.h
end
end qdirDXc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qeIf6Za
theorem aP5_7_2_3_3_1_3_1 :qSHe4ub.c1 :=qdVnFpc.proof
theorem aP5_7_2_3_3_1_3_2 :qSHe4ub.c2 :=qBTeXSd.proof
theorem aP5_7_1_7_4_3_3_4 :qoCymac.c4 :=q6hv5Ed.proof
theorem aP5_7_1_7_4_3_3_6:qoCymac.c6:=qIGP9Qa.proof
theorem aP5_7_2_3_3_1_3_3:qSHe4ub.c3:=qbqCJve.of_children aP5_7_1_7_4_3_3_4 aP5_7_1_7_4_3_3_6
theorem aP5_7_1_4_2_2_3_4_1 :qdpQ3Rb.c1 :=qqBEMJa.proof
theorem aP5_7_1_4_2_2_3_4_2_1 :qThdpma.c1 :=qNm1sVb.proof
theorem aP5_7_1_4_2_2_3_4_2_2 :qThdpma.c2 :=qty7P2c.proof
theorem aP5_7_1_4_2_2_3_4_2 :qdpQ3Rb.c2 :=qThdpma.of_children aP5_7_1_4_2_2_3_4_2_1 aP5_7_1_4_2_2_3_4_2_2
theorem aP5_7_1_7_4_3_4_3:P5_7_1_7_4_3_4.c3:=P5_7_1_7Q434.proof
theorem aP5_7_2_3_3_1_3_4 :qSHe4ub.c4 :=qqI700a.of_children aP5_7_1_4_2_2_3_4_1 aP5_7_1_4_2_2_3_4_2 aP5_7_1_7_4_3_4_3
theorem aP5_7_1_4_2_2_3_5_1 :qAW6lac.c1 :=q5vjhGc.proof
theorem aP5_7_1_4_2_2_3_5_2_1 :qYVN5fe.c1 :=qFBRuya.proof
theorem aP5_7_1_4_2_2_3_5_2_2 :qYVN5fe.c2 :=q9bKVmc.proof
theorem aP5_7_1_4_2_2_3_5_2_3:qYVN5fe.c3:=qrtGZca.proof
theorem aP5_7_1_4_2_2_3_5_2 :qAW6lac.c2 :=qYVN5fe.of_children aP5_7_1_4_2_2_3_5_2_1 aP5_7_1_4_2_2_3_5_2_2 aP5_7_1_4_2_2_3_5_2_3
theorem aP5_7_1_4_2_2_3_5_3_1 :qpVvmab.c1 :=q4XZUmd.proof
theorem aP5_7_1_4_2_2_3_5_3_2 :qpVvmab.c2 :=qNL8tLd.proof
theorem aP5_7_1_4_2_2_3_5_3:qAW6lac.c3:=qpVvmab.of_children aP5_7_1_4_2_2_3_5_3_1 aP5_7_1_4_2_2_3_5_3_2
theorem aP5_7_2_3_3_1_3_5:qSHe4ub.c5:=qR80KYd.of_children aP5_7_1_4_2_2_3_5_1 aP5_7_1_4_2_2_3_5_2 aP5_7_1_4_2_2_3_5_3
theorem aP5_7_2_3_3_1_3:qPY5jQe.c3:=qSHe4ub.of_children aP5_7_2_3_3_1_3_1 aP5_7_2_3_3_1_3_2 aP5_7_2_3_3_1_3_3 aP5_7_2_3_3_1_3_4 aP5_7_2_3_3_1_3_5
theorem proof :q49VXnc.c2 :=aP5_7_2_3_3_1_3
end qeIf6Za
end
