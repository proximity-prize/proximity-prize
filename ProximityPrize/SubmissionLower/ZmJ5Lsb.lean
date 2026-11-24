import ProximityPrize.SubmissionLower.ZBgX9Tc
import ProximityPrize.SubmissionLower.ZasomWd
import ProximityPrize.SubmissionLower.ZqtxWkc
import ProximityPrize.SubmissionLower.ZXLxXWd
import ProximityPrize.SubmissionLower.Zc6ZBRc
import ProximityPrize.SubmissionLower.Zzatq8a
set_option Elab.async false
open _root_ renaming Algebra.FiniteType → zUK, Algebra.FiniteType.quotient → zrZ, Fin.sum_univ_four → zmL, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.mk → zVv, Ideal.span → zye, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.map_X → z7N, Nat.add_le_add_left → z3b, Nat.add_mul → zNE, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qmJ5Lsb
noncomputable section
open Polynomial Finset
open P6 (K p)
open P6_7_1
open qBPZs8a
open P5_7_1 (TopRow atTop topLift topConjugate)
open qaySLPd (SupportCaps orient omitted pad topLabel)
open cu (FX Jet Equation rD jz)
open pI (oU)
open bjF (view b2m)
open scoped Classical
open private b0u from ProximityPrize.SubmissionLower.A3
open private separantCaps nonzero_seed from ProximityPrize.SubmissionLower.ZFKrBre
open private top_relation lift_conjugate conjugate_degree conjugate TopBound from ProximityPrize.SubmissionLower.ZXiQNLd
private theorem deg_le {x :Input} {γ:K} (hγ:γ∈x.Γ) :
    (x.F.scalar γ).natDegree≤qCQTZAc.degreeBound :=
  (P6_7.aic x.F hγ).trans (z3b ((heights x).2.trans (by decide)) 131071)
private theorem supportOfTopCaps {h m B J C U:ℕ} {T:TopRow}
    (hT:TopCaps h m B J C U T) :SupportCaps B J C U T :=
  fun e he=>⟨(hT e he).1,(hT e he).2.1,(hT e he).2.2.1,(hT e he).2.2.2.1⟩
private theorem cheap_weighted {x :Input} (top:TopPair x) :
    qCQTZAc.Weighted qCQTZAc.degreeBound qCQTZAc.cheapHeight top.cheap:= by
  intro e he
  obtain ⟨hb,_,_,_,hw⟩:=top.cheap_caps e he
  have hh:x.h≤2369:=(heights x).2
  let d:=e 1+e 2+e 3
  have hm:=zBI (2703-x.h) (show d≤87 from hb)
  have hdeg:133774*d=(131071+x.h)*d+(2703-x.h)*d:= by
    rw [← zNE,show 131071+x.h+(2703-x.h)=133774 by omega]
  change (top.cheap.coeff e).natDegree+133774*e 1+133773*e 2+133772*e 3≤11811957
  change (top.cheap.coeff e).natDegree+(131071+x.h)*d ≤
    64*P6.dw-1+114*x.h+e 2+2*e 3 at hw
  change _≤11508927+114*x.h+e 2+2*e 3 at hw
  change 133774*(e 1+e 2+e 3)= _ at hdeg
  omega
private theorem contraction {x :Input} (top:TopPair x) {B:TopRow}
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
private theorem colour {x :Input} (t:TopPair x) (i:Fin 2) (γ:K) (hγ:γ∈x.Γ) :
    atTop (orient i t.cheap) (topLabel i (x.M.label γ)) (x.F.scalar γ)=0 ∧
    atTop (orient i t.strong) (topLabel i (x.M.label γ)) (x.F.scalar γ)=0:= by
  obtain ⟨hc,hs,hc',hs'⟩:=t.necessary γ hγ
  fin_cases i
  · simpa [orient,topLabel] using And.intro hc hs
  · simpa [orient,topLabel] using And.intro hc' hs'
private theorem aby {f g:Jet}
    (h:oU g ⟨0,87+12*(wD f 0-1),27+12*(wD f 1-1),249+12*wD f 2⟩) :
    oU g (aOm f) := by
  intro j k hj
  obtain ⟨hb,hv,hu⟩:=h j k hj
  change k+j≤164+19*(wD f 0-1)∧j≤50+19*(wD f 1-1) ∧
    ((g.coeff j).coeff k).totalDegree≤490+19*wD f 2
  change k+j≤87+12*(wD f 0-1) at hb
  change j≤27+12*(wD f 1-1) at hv
  change ((g.coeff j).coeff k).totalDegree≤249+12*wD f 2 at hu
  omega
private theorem cutOfPad {x :Input} {gH :Finset K} {f g:Jet}
    (hp : ¬ f∣g) (hc:oU g (aOm f))
    (hz : ∀ γ∈x.Γ,Mark x f γ→Mark x g γ) :Nonempty (LastCut x gH f) :=
  ⟨⟨g,hp,false,0,hc,by simp,by simp,by simp,fun γ hγ h=>Or.inr (Or.inl (hz γ hγ h))⟩⟩
private theorem ref_lift {x :Input} {P:Poles x} (R:Reference x P) {f :Jet}
    (hf :Irreducible f) (hd:f∣DP.U4 R.raw) :
    qCQTZAc.LiftAt qCQTZAc.degreeBound qCQTZAc.liftHeight f := by
  refine qKVjhPa.lift_of_raw ((heights x).2.trans (by decide)) R.nonzero (fun j i a e hc => ?_) hf hd
  have hamb:R.raw∈DP.Aw x.h (shape referenceIndex) (cutoff (shape referenceIndex)) :=
    R.mem.1.1
  have hel:DP.awN x.h (shape referenceIndex) (cutoff (shape referenceIndex)) j i a e := by
    by_contra hn
    exact hc (hamb j i a e hn)
  exact ⟨hel.1,hel.2.2.2⟩
theorem proof :qBPZs8a.c3:= by
  intro x P R top D hD hvel hmass
  obtain ⟨B,hB,hcontains⟩ :=
    qCQTZAc.fixed_product top.cheap_ne (supportOfTopCaps top.cheap_caps) (cheap_weighted top)
  let gH :=x.Γ.filter (fun γ=>qCQTZAc.Singular B (x.M.label γ) (x.F.scalar γ))
  have hsub:gH⊆x.Γ:=filter_subset _ _
  refine ⟨gH,(qLKC7de.proof B hB gH
    x.M.label x.F.scalar (x.F.distinct.mono hsub) (fun γ hγ=>⟨deg_le (hsub hγ),
      (x.F.mark γ (hsub hγ)).scalar_fixed,(mem_filter.mp hγ).2⟩)).trans (by decide),?_⟩
  intro f hf
  obtain ⟨hi,hd,hseed,_,_⟩:=hD.factors f hf
  have individual (j:Fin 3) :wD f j≤ introCap last j :=
    (single_le_sum (f := fun g=>wD g j) (fun _ _=>Nat.zero_le _) hf).trans (hmass j)
  have hsmallV:f.natDegree<p:=(individual 1).trans_lt (by decide)
  have hsmallSeed :wD f 2<p:=(individual 2).trans_lt (by decide)
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
  obtain ⟨hc,hec⟩:=qT3dOZa.proof f i top.cheap 87 27 12 249 (supportOfTopCaps top.cheap_caps)
  obtain ⟨hs,hes⟩:=qT3dOZa.proof f i top.strong 164 50 19 490 (supportOfTopCaps top.strong_caps)
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
    exact ⟨hv,qZ4UNdb.proof f B i _ _ hB.support hLift hsmallSeed
      (deg_le hγ) hdB hz hv hzero hregular⟩)
  refine ⟨⟨f.derivative,hproper,true,row,separantCaps f,fun _=>rfl,
    fun _=>hr,fun _=>nonzero_seed hseed,?_⟩⟩
  intro γ hγ hz
  by_cases hp:γ∈gH
  · exact Or.inl hp
  by_cases hv :Mark x f.derivative γ
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr ⟨rfl,hline γ (mem_filter.mpr ⟨hγ,hp,hz,hv⟩)⟩)
end
end qmJ5Lsb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace q6lL8Za
theorem proof :qBPZs8a.c4 := fun x f g hj hu _ hc =>
  qXLxXWd.count (D:=P6_7_1.degree) (by decide) (by decide) (by decide) (by decide) x.F
    (fun _ hγ=>(P6_7.aic x.F hγ).trans (Nat.add_le_add_left (P6_7_1.heights x).2 _))
    f g hj hu hc
end q6lL8Za
end
section
set_option autoImplicit true
namespace qPP0zte
noncomputable section
open cu (Shape)
open gT (aQ B4 Pp)
open OH (N8 Q6)
open P6_7_2_3 (sectionMass Tl)
open TD (FP)
def direction (k :Fin 3) :N8 :=
  ![Pp 1,Pp 0,B4 0 1] k
abbrev slice (k :Fin 3) (I:znc gT.Ambient) :=
  I.map Q6 ⊔ zye {direction k}
abbrev bR (k :Fin 3) (Q:znc gT.Ambient) (f :gT.Ambient) :=
  slice k Q ⊔ zye {Q6 f}
abbrev length (I:znc N8) :=zsE aQ (N8 ⧸ I)
def budget (s :Shape) (Q:znc gT.Ambient) (k :Fin 3) :ℚ :=
  FP (Tl (if k=2 then 2*s.U else s.U) s) (sectionMass Q)
end
end qPP0zte
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qB9rgvd
noncomputable section

open P6_7 (RectTail)
open P6_7_2 (Input)
open P6_7_2_3 (marks)
open qu56FMb (dmO curveMass rowPrice)
open TD (FP)
open cu (FX Shape jz)
open gT (Ambient gk aQ aci)
open ac4 (CS arW Cl)
open K1_14_2_2_7_3_3 (bbe coord c5o eOy)
open baB (TY a3W cRS eKX gLa)
open aeF (FZ ajJ toFunction)
open private c4F cca from ProximityPrize.SubmissionLower.Y
open private b8K ezr from ProximityPrize.SubmissionLower.U
open scoped BigOperators Classical
section FibreDegrees
variable {k :Type} [Field k]
private abbrev verticalDegree (I:znc (z3y (Fin 4) k)) [I.IsPrime] (i:Fin 4) :=
  FZ k (toFunction (coord I i))
private abbrev jetDegree (I:znc (z3y (Fin 4) k)) [I.IsPrime] :=
  ajJ k (toFunction (coord I 2)) (toFunction (coord I 3))
private theorem axis_degree (I:znc (z3y (Fin 4) k)) [I.IsPrime] (i:Fin 4) :
    zsE (CS k) (gk
      (I.map (Cl k) ⊔ zye {z9v i-MvPolynomial.C (arW k 1)})) =
    verticalDegree I i:= by
  have he :TY I (z9v i) 0 =
      I.map (Cl k) ⊔ zye {z9v i-MvPolynomial.C (arW k 1)} := by
    simp only [TY,a3W,z7N,map_zero,mul_zero,add_zero]
  have h:=(cRS I (z9v i) 0).trans (gLa I (z9v i))
  rw [he] at h
  exact h
private theorem jet_degree (I:znc (z3y (Fin 4) k)) [I.IsPrime] :
    zsE (CS k) (gk
      (I.map (Cl k) ⊔ zye {z9v 2 +
        MvPolynomial.C (arW k 0)*z9v 3-MvPolynomial.C (arW k 1)})) =
    jetDegree I:= by
  have he :TY I (z9v 2) (z9v 3)=I.map (Cl k) ⊔
      zye {z9v 2+MvPolynomial.C (arW k 0)*z9v 3 -
        MvPolynomial.C (arW k 1)} := by
    simp only [TY,a3W,z7N]
  have h:=(cRS I (z9v 2) (z9v 3)).trans
    (eKX I (z9v 2) (z9v 3))
  rw [he] at h
  exact h
private abbrev Supported (S:Shape) (G:z3y (Fin 4) k) :Prop :=
  ∀ a∈G.support,a 0≤S.U∧a 1≤S.U∧a 2+a 3≤S.B∧a 3≤S.J
private theorem avh {B J i j a b:ℕ} (hB:i+j≤B) (hJ:j≤J) :
    i*a+j*b≤(B-J)*a+J*max a b:= by
  have hi:i≤(B-J)+(J - j) := by omega
  calc
    _≤((B-J)+(J - j))*a+j*b :=
      Nat.add_le_add_right (ztf _ hi) _
    _=(B-J)*a+((J - j)*a+j*b) := by simp only [zNE,Nat.add_assoc]
    _≤(B-J)*a+((J - j)*max a b+j*max a b) :=
      z3b (Nat.add_le_add (zBI _ (le_max_left _ _))
        (zBI _ (le_max_right _ _))) _
    _ = _:= by rw [← zNE,Nat.sub_add_cancel hJ]
private theorem fZu (I:znc (z3y (Fin 4) k)) [I.IsPrime]
    (D:bbe k (gk I) (coord I 2) (coord I 3))
    (q:Fin D.places) {S:Shape} {G:z3y (Fin 4) k} (hG:Supported S G) :
    D.order q (zVv I G)≤S.U*D.order q (coord I 1) +
      S.U*D.order q (coord I 0)+(S.B - S.J)*D.order q (coord I 2) +
      S.J*max (D.order q (coord I 2)) (D.order q (coord I 3)) := by
  let o (i:Fin 4) :=D.order q (coord I i)
  have hprod (a :Fin 4 →₀ ℕ) (T:Finset (Fin 4)) :
      D.order q (∏ i∈T,coord I i^a i) ≤ ∑ i∈T,a i*o i:= by
    induction T using Finset.induction_on with
    | empty=>simpa using (D.scalar q (1 :k)).le
    | insert i T hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi]
      exact (D.mul q _ _).trans (Nat.add_le_add (cca D q _ _) ih)
  conv_lhs=>rw [G.as_sum,map_sum]
  apply c4F D q
  intro a ha
  conv_lhs=>rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),
    map_mul,map_prod,← MvPolynomial.algebraMap_eq,Ideal.Quotient.mk_algebraMap]
  simp only [map_pow]
  refine (D.mul q _ _).trans ?_
  rw [D.scalar,zero_add]
  refine (hprod a Finset.univ).trans ?_
  rw [zmL]
  obtain ⟨h0,h1,hB,hJ⟩:=hG a ha
  have ht:=avh (a :=o 2) (b:=o 3) hB hJ
  have h0' := ztf (o 0) h0
  have h1' := ztf (o 1) h1
  change _≤S.U*o 1+S.U*o 0+(S.B - S.J)*o 2+S.J*max (o 2) (o 3)
  omega
private theorem row_degree_le (I:znc (z3y (Fin 4) k)) [I.IsPrime]
    (hI:ringKrullDim (gk I)=1) {S:Shape} {G:z3y (Fin 4) k} (hG:Supported S G) :
    FZ k (toFunction (zVv I G)) ≤
      S.U*verticalDegree I 1+S.U*verticalDegree I 0 +
        (S.B - S.J)*verticalDegree I 2+S.J*jetDegree I:= by
  let:zUK k (gk I) :=zrZ k I
  have hpoles :K1_14_2_2_7_3_3.c1 :=axk.of_children
    czd.proof cze.proof
    czf.proof czg.proof
  obtain ⟨D⟩:=hpoles k (gk I) hI (coord I 2) (coord I 3)
  unfold verticalDegree jetDegree
  rw [← D.degree_eq (zVv I G),← D.degree_eq (coord I 1),
    ← D.degree_eq (coord I 0),← D.degree_eq (coord I 2),← D.pencil_eq]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  simpa only [Nat.mul_add,Nat.mul_left_comm (D.weight q)] using
    zBI (D.weight q) (fZu I D q hG)
end FibreDegrees
private theorem card_evaluations_le_length {k R ι:Type} [Field k] [CommRing R] [Algebra k R]
    [Fintype ι] (f a :R) [zAa k (R ⧸ zye {f})]
    (e :ι→R →ₐ[k] k) (hf : ∀ i,e i f=0) (ha :zq4 (fun i=>e i a)) :
    Fintype.card ι≤zsE k (R ⧸ zye {f}) := by
  let M (i:ι) :=RingHom.ker (e i)
  apply WJ.dFu (zye {f}) M
  · intro i
    exact RingHom.ker_isMaximal_of_surjective (e i)
      (fun c=>⟨algebraMap k R c,by simp⟩)
  · intro i
    exact (Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hf i))
  · intro i j he
    apply ha
    let z :=a-algebraMap k R (e i a)
    have hi:z∈M i:=RingHom.mem_ker.mpr (by simp [z])
    have hj:z∈M j:=he ▸ hi
    have hz :e j z=0:=RingHom.mem_ker.mp hj
    exact (sub_eq_zero.mp (by
      simpa only [z,map_sub,AlgHom.commutes,Algebra.algebraMap_self_apply] using hz)).symm
private theorem marks_le_length {b:RectTail} (x :Input b) (I:znc Ambient)
    (G:Ambient) [zAa FX (gk I ⧸ zye {zVv I G})]
    (hG : ∀ γ∈marks x I,aci (x.M.label γ) (x.F.scalar γ) G=0) :
    (marks x I).card≤zsE FX (gk I ⧸ zye {zVv I G}) := by
  let e (γ:marks x I) :gk I →ₐ[FX] FX :=
    b8K (Finset.mem_filter.mp γ.property).2
  have hfirst (γ:marks x I) :e γ (coord I 0)=jz (x.M.label γ) :=
    ezr (Finset.mem_filter.mp γ.property).2
  have hinj:zq4 (fun γ=>e γ (coord I 0)) := by
    intro γ δ he
    change e γ (coord I 0)=e δ (coord I 0) at he
    rw [hfirst,hfirst] at he
    exact Subtype.ext (sub_left_inj.mp (jz.injective he))
  exact (Fintype.card_coe (marks x I)).symm.trans_le
    (card_evaluations_le_length (k :=FX) (R:=gk I)
      (zVv I G) (coord I 0) e (fun γ=>hG γ γ.property) hinj)
theorem proof :qu56FMb.c3:= by
  intro b x I hI _ G hcaps hproper hzeros
  let:I.IsPrime :=hI.1
  let:zUK FX (gk I) :=zrZ FX I
  have hne :zVv I G≠0 :=
    fun hz=>hproper (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  let:zAa FX (gk I ⧸ zye {zVv I G}) :=
    c5o (k :=FX) (A:=gk I) hI.2.1 hne
  have hm:=(marks_le_length x I G hzeros).trans
    ((eOy (k :=FX) (A:=gk I) hI.2.1 hne).trans (row_degree_le I hI.2.1 hcaps))
  have h0:zsE aQ (dmO I 0)=verticalDegree I 1 :=axis_degree I 1
  have h1 :zsE aQ (dmO I 1)=verticalDegree I 0:=axis_degree I 0
  have h2 :zsE aQ (dmO I 2)=verticalDegree I 2 :=axis_degree I 2
  have h3:zsE aQ (dmO I 3)=jetDegree I:=jet_degree I
  rw [← h0,← h1,← h2,← h3] at hm
  simpa [FP,zmL,rowPrice,curveMass,Nat.cast_add,Nat.cast_mul] using
    (Nat.cast_le.mpr hm: ((marks x I).card:ℚ)≤(_:ℕ))
end
end qB9rgvd
end
section
set_option autoImplicit true
namespace qSn9O8a
open Finset (filter_subset mem_filter)
open P6_7_2_3 (marks)
open YY (Si a9E)
open private cag from ProximityPrize.SubmissionLower.G
theorem proof :qu56FMb.c6:= by
  classical
  intro b x I C g hD hp
  have hm:q6hAhQd.DescendedMarks x (marks x I) (Si I) C g (a9E I) :=
    ⟨filter_subset _ _,hD.root,hD.irreducible,hD.projection,hD.plane_pos,hp,
      fun _ hγ=>cag (mem_filter.mp hγ).2⟩
  refine ⟨q6hAhQd.persistent hD.positive hm,?_⟩
  intro hg
  subst g
  exact q6hAhQd.linear hm
end qSn9O8a
end
