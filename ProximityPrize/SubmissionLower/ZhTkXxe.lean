import ProximityPrize.SubmissionLower.ZOb5aoe
import ProximityPrize.SubmissionLower.Z5cOcra
import ProximityPrize.SubmissionLower.ZK8GpQb
import ProximityPrize.SubmissionLower.ZXLxXWd
import ProximityPrize.SubmissionLower.ZAJiURc
import ProximityPrize.SubmissionLower.Z3lRrWc
import ProximityPrize.SubmissionLower.ZDbTvLe
import ProximityPrize.SubmissionLower.ZAZ7Tec
import ProximityPrize.SubmissionLower.ZKtTCEc
import ProximityPrize.SubmissionLower.ZKgVGSb
import ProximityPrize.SubmissionLower.ZoOOLsc
import ProximityPrize.SubmissionLower.ZvIni8b
import ProximityPrize.SubmissionLower.ZjlUeKe
import ProximityPrize.SubmissionLower.ZBgX9Tc
import ProximityPrize.SubmissionLower.ZyrKS8a
import ProximityPrize.SubmissionLower.ZqtxWkc
set_option Elab.async false
section
set_option autoImplicit true
namespace P5_7_1_4_2_2_3_4_3
theorem proof :qdpQ3Rb.c3:=q9r9FBa.proof
end P5_7_1_4_2_2_3_4_3
end
section
set_option autoImplicit true
namespace P5_7_1_4_2_2_3_2
def c1 :Prop :=qypA4Sc.c1
def c2 :Prop :=qypA4Sc.c2
def c3:Prop :=qypA4Sc.c3
theorem of_children (QI:c1) (residue :c2) (derivation :c3) :
    qZV9OWb.c2 :=
  qypA4Sc.of_children QI residue derivation
end P5_7_1_4_2_2_3_2
end
section
set_option autoImplicit true
namespace qEqhDIe
theorem proof :quQsorc.c2 :=
  qZV9OWb.of_children q89Irde.proof
    (P5_7_1_4_2_2_3_2.of_children qWnROxa.proof qlcyGcd.proof
      qrrOjma.proof)
    (q53i3jb.of_children q5eiIAb.proof qvOlzpd.proof
      q6hv5Ed.proof qpI7nyd.proof qIGP9Qa.proof)
    (qdpQ3Rb.of_children qqBEMJa.proof
      (qThdpma.of_children qNm1sVb.proof qty7P2c.proof)
      P5_7_1_4_2_2_3_4_3.proof)
    (qAW6lac.of_children q5vjhGc.proof
      (qYVN5fe.of_children qFBRuya.proof q9bKVmc.proof
        qrtGZca.proof)
      (qpVvmab.of_children q4XZUmd.proof qNL8tLd.proof))
end qEqhDIe
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qhTkXxe
theorem proof :qkBU02c.c2 :=qEqhDIe.proof
end qhTkXxe
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qxbXAQb
noncomputable section
section product
open MvPolynomial
open P6_7 (RectTail)
open P6_7_2 (TopPair Input)
open qNRjwze (emE)
open P5_7_1 (TopRow topLift topConjugate)
open qaySLPd (omitted pad)
open cu (FX Jet)
open bjF (view)
open private top_relation lift_conjugate conjugate_degree conjugate TopBound from ProximityPrize.SubmissionLower.ZXiQNLd
theorem height_small {b:RectTail} (x :Input b) :x.h≤2406 :=
  (emE x).trans (by cases b <;> decide)
theorem cheap_weighted {b:RectTail} {x :Input b} (top:TopPair x) :
    qCQTZAc.Weighted qCQTZAc.degreeBound qCQTZAc.cheapHeight top.cheap:= by
  intro e he
  obtain ⟨hb,_,_,_,hw⟩:=top.cheap_caps e he
  have hh:=height_small x
  let d:=e 1+e 2+e 3
  have hm:=Nat.mul_le_mul_left (2703-x.h) (show d≤87 from hb)
  have hdeg:133774*d=(131071+x.h)*d+(2703-x.h)*d:= by
    rw [← Nat.add_mul,show 131071+x.h+(2703-x.h)=133774 by omega]
  change (top.cheap.coeff e).natDegree+133774*e 1+133773*e 2+133772*e 3≤11811957
  change (top.cheap.coeff e).natDegree+(131071+x.h)*d≤11508927+114*x.h+e 2+2*e 3 at hw
  change 133774*(e 1+e 2+e 3)= _ at hdeg
  omega
theorem contraction {b:RectTail} {x :Input b} (top:TopPair x) {B:TopRow}
    (hB:qCQTZAc.FixedData B) (hcontains :qCQTZAc.ContainsFixed top.cheap B)
    {f :Jet} {i:Fin 2} (hf :Irreducible f) (hsep : ¬ f∣f.derivative)
    (hdep:0<(view (omitted i) f).natDegree)
    (hc:f∣pad f i 12 top.cheap) (hs :f∣pad f i 19 top.strong) :
    f∣pad f i 12 B:= by
  have cb:TopBound 12 top.cheap:= fun a ha=>(top.cheap_caps a ha).2.2.1
  have sb:TopBound 19 top.strong:= fun a ha=>(top.strong_caps a ha).2.2.1
  obtain ⟨Q,hQ,ht,hrel⟩:=top_relation hf hsep hdep top.cheap_ne cb hc
  apply (hrel (S:=B) (c' := 12) (fun a ha=>(hB.support a ha).2.2.1)).mpr
  have hdC:=(hrel cb).mp hc
  have hdS:=(hrel sb).mp hs
  fin_cases i
  · exact hcontains Q hQ ht (top.no_moving Q hQ ht hdC hdS) hdC
  · change Q∣topLift (topConjugate B)
    rw [lift_conjugate]
    have undo (S:TopRow) (hS:Q∣topLift (topConjugate S)) :
        conjugate.symm Q∣topLift S:= by
      rw [lift_conjugate] at hS
      simpa only [RingEquiv.symm_apply_apply] using map_dvd conjugate.symm hS
    have hQ' := hQ.map conjugate.symm
    have ht' : 0<(conjugate.symm Q).degreeOf 3:=(conjugate_degree Q 3).symm ▸ ht
    have hc' := undo top.cheap hdC
    have hfix :=top.no_moving _ hQ' ht' hc' (undo top.strong hdS)
    simpa only [RingEquiv.apply_symm_apply] using map_dvd conjugate (hcontains _ hQ' ht' hfix hc')
end product
open Polynomial Finset
open P6 (K p)
open P6_7 (RectTail)
open P6_7_2
open P6_7_2_3 (introCap last topCut)
open qNRjwze (Mark LastCut)
open P5_7_1 (TopRow atTop wD)
open qaySLPd (SupportCaps orient omitted pad topLabel)

open cu (FX Jet Equation rD jz)
open pI (oU)
open bjF (view b2m)
open scoped Classical
open private b0u from ProximityPrize.SubmissionLower.A3
open private separantCaps nonzero_seed from ProximityPrize.SubmissionLower.ZFKrBre
private theorem supportOfTopCaps {h m B J C U:ℕ} {T:TopRow}
    (hT:TopCaps h m B J C U T) :SupportCaps B J C U T :=
  fun e he=>⟨(hT e he).1,(hT e he).2.1,(hT e he).2.2.1,(hT e he).2.2.2.1⟩
private theorem colour {b:RectTail} {x :Input b} (t:TopPair x) (i:Fin 2) (γ:K) (hγ:γ∈x.Γ) :
    atTop (orient i t.cheap) (topLabel i (x.M.label γ)) (x.F.scalar γ)=0 ∧
    atTop (orient i t.strong) (topLabel i (x.M.label γ)) (x.F.scalar γ)=0:= by
  obtain ⟨hc,hs,hc',hs'⟩:=t.necessary γ hγ
  fin_cases i
  · simpa [orient,topLabel] using And.intro hc hs
  · simpa [orient,topLabel] using And.intro hc' hs'
private theorem aby {b:RectTail} {f g:Jet}
    (h:oU g ⟨0,87+12*(wD f 0-1),27+12*(wD f 1-1),cheapWidth b+12*wD f 2⟩) :
    oU g (topCut b (wD f)) := by
  intro j k hj
  obtain ⟨hb,hv,hu⟩:=h j k hj
  change k+j≤164+19*(wD f 0-1)∧j≤50+19*(wD f 1-1) ∧
    ((g.coeff j).coeff k).totalDegree≤ strongWidth b+19*wD f 2
  change k+j≤87+12*(wD f 0-1) at hb
  change j≤27+12*(wD f 1-1) at hv
  change ((g.coeff j).coeff k).totalDegree≤ cheapWidth b+12*wD f 2 at hu
  have hw:cheapWidth b≤ strongWidth b:= by cases b <;> decide
  omega
private theorem cutOfPad {b:RectTail} {x :Input b} {gH :Finset K} {f g:Jet}
    (hp : ¬ f∣g) (hc:oU g (topCut b (wD f)))
    (hz : ∀ γ∈x.Γ,Mark x f γ→Mark x g γ) :Nonempty (LastCut x gH f) :=
  ⟨⟨g,hp,false,0,hc,by simp,by simp,by simp,fun γ hγ h=>Or.inr (Or.inl (hz γ hγ h))⟩⟩
private theorem ref_lift {b:RectTail} {x :Input b} {P:Poles x} (R:qNRjwze.Reference P) {f :Jet}
    (hf :Irreducible f) (hd:f∣DP.U4 R.raw) :
    qCQTZAc.LiftAt qCQTZAc.degreeBound qCQTZAc.liftHeight f := by
  have hshape : (auxiliary b 9).m=83∧(auxiliary b 9).B=115∧(auxiliary b 9).J=25:= by
    cases b <;> decide
  refine qKVjhPa.lift_of_raw ((height_small x).trans (by decide)) R.nonzero (fun j i a e hc => ?_) hf hd
  have hamb:R.raw∈DP.Aw x.h (auxiliary b 9) (cutoff x.h 0 (auxiliary b 9)) :=R.mem.1.1
  have hel:DP.awN x.h (auxiliary b 9) (cutoff x.h 0 (auxiliary b 9)) j i a e := by
    by_contra hn
    exact hc (hamb j i a e hn)
  have hw:=hel.2.2.2
  simp only [cutoff,Nat.mul_zero,Nat.sub_zero,hshape.1,hshape.2.1,hshape.2.2] at hw
  exact ⟨hel.1.trans_eq hshape.2.1,hw⟩
theorem proof :qNRjwze.c2 := by
  intro b x P top R D hD hvel hmass
  obtain ⟨B,hB,hcontains⟩ :=
    qCQTZAc.fixed_product top.cheap_ne (supportOfTopCaps top.cheap_caps) (cheap_weighted top)
  let gH :=x.Γ.filter (fun γ=>qCQTZAc.Singular B (x.M.label γ) (x.F.scalar γ))
  have hsub:gH⊆x.Γ:=filter_subset _ _
  refine ⟨gH,(qLKC7de.proof B hB gH
    x.M.label x.F.scalar (x.F.distinct.mono hsub) (fun γ hγ=>⟨(P6_7.aic x.F (hsub hγ)).trans
      (Nat.add_le_add_left ((height_small x).trans (by decide :2406≤2703)) 131071),
      (x.F.mark γ (hsub hγ)).scalar_fixed,(mem_filter.mp hγ).2⟩)).trans (by decide),?_⟩
  intro f hf
  obtain ⟨hi,hd,hseed,_,_⟩:=hD.factors f hf
  have individual (j:Fin 3) :wD f j≤ introCap b last j :=
    (single_le_sum (f := fun g=>wD g j) (fun _ _=>Nat.zero_le _) hf).trans (hmass j)
  have hsmallV:f.natDegree<p:=(individual 1).trans_lt (by cases b <;> decide)
  let:CharP FX p:=charP_of_injective_ringHom jz.injective p
  let:CharP (cu.aZ) p:=charP_of_injective_ringHom
    (MvPolynomial.C_injective (Fin 2) FX) p
  let:CharP Equation p:=charP_of_injective_ringHom Polynomial.C_injective p
  have hproper :=b0u (A:=Equation) (q:=p) f (hvel f hf) hsmallV
  obtain ⟨j,hj⟩:=b2m f hseed
  let i:=omitted j
  have hdep:0<(view (omitted i) f).natDegree := by
    have he :omitted i=j:= by fin_cases j <;> decide
    simpa only [he] using hj
  obtain ⟨hc,hec⟩:=qT3dOZa.proof f i top.cheap 87 27 12 (cheapWidth b) (supportOfTopCaps top.cheap_caps)
  obtain ⟨hs,hes⟩:=qT3dOZa.proof f i top.strong 164 50 19 (strongWidth b) (supportOfTopCaps top.strong_caps)
  by_cases hpc:f∣pad f i 12 top.cheap
  swap
  · exact cutOfPad hpc (aby hc) (fun γ hγ hz=> by
      rw [Mark,hec _ _ hz,(colour top i γ hγ).1,mul_zero])
  by_cases hps :f∣pad f i 19 top.strong
  swap
  · exact cutOfPad hps hs (fun γ hγ hz=> by
      rw [Mark,hes _ _ hz,(colour top i γ hγ).2,mul_zero])
  have hdB:=contraction top hB hcontains hi hproper hdep hpc hps
  have hLift:=ref_lift R hi hd
  obtain ⟨_,heB⟩:=qT3dOZa.proof f i B 87 27 12 0 hB.support
  let T:=x.Γ.filter (fun γ=>γ∉gH∧Mark x f γ ∧ ¬ Mark x f.derivative γ)
  obtain ⟨row,hr,hline⟩:=qKVjhPa.line_of_scalars x.M.label x.F.scalar f T (by
    intro γ hγ
    obtain ⟨hγ,hnot,hz,hv⟩:=mem_filter.mp hγ
    change rD f (x.M.label γ) (x.F.scalar γ)=0 at hz
    have hEval :=map_dvd (XY.vf (x.M.label γ) (x.F.scalar γ)) hdB
    change rD f (x.M.label γ) (x.F.scalar γ) ∣
      rD (pad f i 12 B) (x.M.label γ) (x.F.scalar γ) at hEval
    rw [hz,zero_dvd_iff,heB _ _ hz] at hEval
    have htwo: (2 :FX)≠0:= fun hz =>
      (by decide : ¬ p∣2) ((CharP.cast_eq_zero_iff FX p 2).mp hz)
    have hzero :=(mul_eq_zero.mp hEval).resolve_left (pow_ne_zero _ (mul_ne_zero htwo hv))
    have hregular :atTop (MvPolynomial.pderiv 3 (orient i B))
        (topLabel i (x.M.label γ)) (x.F.scalar γ)≠0 :=
      fun he=>hnot (mem_filter.mpr ⟨hγ,⟨i,hzero,he⟩⟩)
    have hdeg:=(P6_7.aic x.F hγ).trans
      (Nat.add_le_add_left ((height_small x).trans (by decide :2406≤2703)) 131071)
    exact ⟨hv,qZ4UNdb.proof f B i _ _ hB.support hLift
      ((individual 2).trans_lt (by cases b <;> decide)) hdeg hdB hz hv hzero hregular⟩)
  refine ⟨⟨f.derivative,hproper,true,row,separantCaps f,fun _=>rfl,
    fun _=>hr,fun _=>nonzero_seed hseed,?_⟩⟩
  intro γ hγ hz
  by_cases hp:γ∈gH
  · exact Or.inl hp
  by_cases hv :Mark x f.derivative γ
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr ⟨rfl,hline γ (mem_filter.mpr ⟨hγ,hp,hz,hv⟩)⟩)
end
end qxbXAQb
end
