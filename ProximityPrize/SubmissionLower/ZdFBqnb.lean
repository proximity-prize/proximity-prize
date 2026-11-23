import ProximityPrize.SubmissionLower.ZNKYOve
import ProximityPrize.SubmissionLower.ZRtQEca
import ProximityPrize.SubmissionLower.ZalmDpd
import ProximityPrize.SubmissionLower.Q
import ProximityPrize.SubmissionLower.ZKfhfIb
import ProximityPrize.SubmissionLower.ZyrKS8a
import ProximityPrize.SubmissionLower.Z0sgnhc
import ProximityPrize.SubmissionLower.Zc6ZBRc
set_option Elab.async false
section
set_option autoImplicit true
namespace q3zj1ie
theorem proof :qRpGGpd.c1 :=q978Lma.proof
end q3zj1ie
end
section
set_option autoImplicit true
namespace qVBNDvb
theorem proof :qRpGGpd.c3 :=
  qmpFDTd.proof
end qVBNDvb
end
section
set_option autoImplicit true
namespace qLjvSEb
theorem proof :qRpGGpd.c2 :=q9aDOab.proof
end qLjvSEb
end
section
set_option autoImplicit true
namespace qhFFwmd
theorem proof :qlVncRd.c2 :=
  qvWbALd.of_children q9aDOab.proof qmpFDTd.proof
end qhFFwmd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace czF
noncomputable section
open cu qQ XY Polynomial
open scoped BigOperators
private def moveJet (R:Type*) [CommSemiring R] :
    Polynomial (MvPolynomial (Fin 2) R) ≃ₐ[R] MvPolynomial (Fin 2) (Polynomial R) :=
  (MvPolynomial.optionEquivLeft R (Fin 2)).symm.trans (MvPolynomial.optionEquivRight R (Fin 2))
private theorem moveJet_coeff {R:Type*} [CommSemiring R]
    (P:Polynomial (MvPolynomial (Fin 2) R)) (d:Fin 2 →₀ ℕ) (i:ℕ) :
    ((moveJet R P).coeff d).coeff i=(P.coeff i).coeff d:= by
  change ((MvPolynomial.optionEquivRight R (Fin 2) ((MvPolynomial.optionEquivLeft R
    (Fin 2)).symm P)).coeff d).coeff i= _
  rw [MvPolynomial.optionEquivRight_coeff_coeff,← MvPolynomial.optionEquivLeft_coeff_coeff]
  simp
private def AV:Jet →+* MvPolynomial (Fin 2) IW :=
  (moveJet (Polynomial FX)).toRingHom.comp
    (Polynomial.mapRingHom (moveJet FX).toRingHom)
private theorem bNI (P:Jet) (d:Fin 2 →₀ ℕ) (v y :ℕ) :
    (((AV P).coeff d).coeff v).coeff y=((P.coeff v).coeff y).coeff d:= by
  change (((moveJet (Polynomial FX) (P.map (moveJet FX).toRingHom)).coeff d).coeff v).coeff y= _
  rw [moveJet_coeff,Polynomial.coeff_map]
  exact moveJet_coeff (P.coeff v) d y
def gY (P:Jet) :ℕ:=(AV P).totalDegree
theorem Qc (P:Jet) (u:ℕ) :
    gY P≤u ↔ ∀ v y,((P.coeff v).coeff y).totalDegree≤u:= by
  simp only [gY,MvPolynomial.totalDegree,Finset.sup_le_iff,
    MvPolynomial.mem_support_iff]
  constructor
  · intro h v y d hd
    apply h d
    intro hz
    exact hd (by rw [← bNI,hz,Polynomial.coeff_zero,Polynomial.coeff_zero])
  · intro h d hd
    obtain ⟨v,hv⟩:=Polynomial.support_nonempty.mpr hd
    obtain ⟨y,hy⟩:=Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hv)
    apply h v y d
    rwa [← bNI,← Polynomial.mem_support_iff]
theorem acG {P Q:Jet} (hP:P≠0) (hQ:Q≠0) :
    gY (P*Q)=gY P+gY Q:= by
  have hi:Function.Injective AV :=
    (moveJet (Polynomial FX)).injective.comp (Polynomial.map_injective _ (moveJet FX).injective)
  have hP' : AV P≠0:= by simpa only [map_zero] using hi.ne hP
  have hQ' : AV Q≠0:= by simpa only [map_zero] using hi.ne hQ
  unfold gY
  rw [map_mul,MvPolynomial.totalDegree_mul_of_isDomain hP' hQ']
theorem bg3 (f :Equation) :gY (C f)=My f := by
  apply le_antisymm
  · apply (Qc _ _).mpr
    intro v y
    by_cases hv :v=0
    · subst v
      rw [coeff_C_zero]
      by_cases hy :f.coeff y=0
      · simp [hy]
      · exact Finset.le_sup (f := fun i=>(f.coeff i).totalDegree) (mem_support_iff.mpr hy)
    · simp [coeff_C,hv]
  · apply Finset.sup_le
    intro y _
    simpa only [coeff_C_zero] using (Qc (C f) _).mp le_rfl 0 y
theorem ordinarySeedDegree_mul {f g:Equation} (hf :f≠0) (hg:g≠0) :
    My (f * g)=My f+My g:= by
  simp only [← bg3,map_mul]
  exact acG (C_ne_zero.mpr hf) (C_ne_zero.mpr hg)
theorem ordinarySeedDegree_prod (F:Finset Equation) (hF : ∀ f∈F,f≠0) :
    My (∏ f∈F,f) = ∑ f∈F,My f := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty,Finset.sum_empty,My]
    change (C (1 :aZ)).support.sup (fun i=>((C (1 :aZ)).coeff i).totalDegree)=0
    rw [support_C (one_ne_zero : (1 :aZ)≠0),Finset.sup_singleton,coeff_C_zero,
      MvPolynomial.totalDegree_one]
  | @insert f F hf ih =>
    have hrest : ∀ g∈F,g≠0:= fun g hg=>hF g (Finset.mem_insert_of_mem hg)
    rw [Finset.prod_insert hf,Finset.sum_insert hf,
      ordinarySeedDegree_mul (hF f (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr hrest),ih hrest]
end
end czF
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000
namespace qdFBqnb
noncomputable section
open Finset Polynomial
open scoped Classical BigOperators
open P6 (K p dw)
open P6_7 (RectTail)
open P6_7_2 (Bs)

open qNRjwze (eHB)
open qcuQADa (degree)
open qXdgDRd (gap width Guards PoleBound StrongMarks)
open P5_7_7 (sites mem_sites)
open qGnV2ac (Sections)
open q7kdBxd (Input horizontalDegree polarBudget finitePoles)
open qrKC9pb (NoHorizontalPole GraphPrime Over polarOrder)
open cu (L Equation vm yq qD kr rD)
open XY (My)
open atc (bri bg3)
open akZ (ajz)
open private emz from ProximityPrize.SubmissionLower.ZUkTKja
open private rate witness checked increases from ProximityPrize.SubmissionLower.ZuFhpOb
open private budgets from ProximityPrize.SubmissionLower.ZATKiYa
open private b6E from ProximityPrize.SubmissionLower.T
def c1 :Prop :=
  ∀ J:Input,J.l≤12→horizontalDegree J<p→NoHorizontalPole J
def c2 :Prop :=
  ∀ (J:Input) (S:Sections J.F),J.l≤12→NoHorizontalPole J →
    ∀ γ∈S.CF,∀ x∈(S.B γ).roots.toFinset,
      ∃ (r :Bool) (D:GraphPrime J r),
        Over J D (algebraMap K L (S.seed γ)) x ∧
          (S.B γ).rootMultiplicity x≤polarOrder D
def c3:Prop :=
  ∀ (J:Input),J.l≤12 → ∀ (ι:Type) [Fintype ι] (a x :ι→L) (r :ι→Bool)
    (D : ∀ i,GraphPrime J (r i)),
    Function.Injective (fun i=>(a i,x i))→(∀ i,Over J (D i) (a i) (x i)) →
      (∑ i,polarOrder (D i))≤polarBudget J
private theorem finite_budget (charge :c2) (order :c3) (J:Input) (hl:J.l≤12)
    (S:Sections J.F) (hor :NoHorizontalPole J) :finitePoles S≤polarBudget J:= by
  let U:=S.CF.sigma fun γ=>(S.B γ).roots.toFinset
  let a (i : ↥U) :=algebraMap K L (S.seed i.val.1)
  let x (i : ↥U) :=i.val.2
  have ha :Function.Injective (fun i=>(a i,x i)) := by
    intro i j h
    have hz :=(algebraMap K L).injective (congrArg Prod.fst h)
    have hi:=(mem_sigma.mp i.prop).1
    have hj:=(mem_sigma.mp j.prop).1
    exact Subtype.ext (Sigma.ext (S.injective hi hj hz) (heq_of_eq (congrArg Prod.snd h)))
  have hc (i : ↥U) :
      ∃ (r :Bool) (D:GraphPrime J r),Over J D (a i) (x i) ∧
        (S.B i.val.1).rootMultiplicity (x i)≤polarOrder D:= by
    obtain ⟨hγ,hx⟩:=mem_sigma.mp i.prop
    exact charge J S hl hor _ hγ _ hx
  choose r D hD hle using hc
  calc
    finitePoles S = ∑ i : ↥U,(S.B i.val.1).rootMultiplicity (x i) := by
      change finitePoles S = ∑ i∈U.attach,(S.B i.val.1).rootMultiplicity i.val.2
      rw [sum_attach U (fun i=>(S.B i.1).rootMultiplicity i.2)]
      unfold U finitePoles
      rw [sum_sigma]
      refine sum_congr rfl fun γ _ => ?_
      rw [← IsAlgClosed.card_roots_eq_natDegree,← Multiset.toFinset_sum_count_eq]
      exact sum_congr rfl fun _ _=>Polynomial.count_roots _
    _ ≤ ∑ i,polarOrder (D i) :=sum_le_sum fun i _=>hle i
    _≤polarBudget J:=order J hl _ a x r D ha hD
private theorem c4y (Oj:c1) (charge :c2) (order :c3) (B:ℕ) :
    PoleBound B 12 := by
  intro F l h u s W hle H hw hW hf hchar S
  obtain ⟨hb,hm,hn⟩:=budgets l u s B W H.two_le hw hW
  let J:Input :=⟨F,l,h,s,W-l*u-l*s,H,hb.symm ▸ hf⟩
  have hJ:horizontalDegree J<p:= by
    change (2*l-2)*(W-l*u-l*s)+l*(l-1)*s<p
    rwa [hm]
  obtain ⟨G,T,hl,hh,hs,hb',ht⟩:=qWIOgVd.proof J S
  have hm' : horizontalDegree G=horizontalDegree J:= by
    simp only [horizontalDegree,hl,hs,hb']
  have hn' : polarBudget G=polarBudget J:= by
    simp only [polarBudget,hl,hh,hs,hb']
  have hlG:G.l≤12 :=hl.trans_le hle
  have hB:=finite_budget charge order G hlG T (Oj G hlG (hm'.symm ▸ hJ))
  rw [hn'] at hB
  exact ht.trans (hB.trans (Nat.mul_le_mul_right h hn))
private def ash:RectTail→ℕ
  | .pruned=>139
  | .tailOne=>136
  | .tailTwo=>134
  | .tailThree=>132
private def rootFee (b:RectTail) :ℕ:=eHB b - p*ash b
private theorem guard (b:RectTail) :Guards (degree b) 12 (rate b 12) := by
  have hcap:12≤(Bs b).ordinateCap:= by cases b <;> decide
  refine ⟨increases b (l:=0) (Nat.zero_le _) hcap,?_⟩
  intro l hl hle
  cases l with
  | zero=>omega
  | succ j =>
    refine ⟨witness b (j+1),(checked b j (hle.trans hcap)).2.1,?_⟩
    simpa only [rate,ite_eq_right (Nat.succ_ne_zero j)] using increases b hle hcap
private theorem budget (b:RectTail) :
    gap (degree b)*12+rate b 12*((p+1)*ash b)≤gap (degree b)*(rootFee b-1) := by
  cases b <;> decide
theorem of_children (Oj:c1) (charge :c2) (order :c3) :qNRjwze.c1 := by
  intro b x G D hD hv hcap
  have hC (f) (hf :f∈D) :C (f.coeff 0)=f :=(eq_C_of_natDegree_eq_zero (hv f hf)).symm
  let Q:=D.image (fun f=>f.coeff 0)
  let F:Equation := ∏ f∈Q,f
  have hi:Set.InjOn (fun f=>f.coeff 0) (D:Set cu.Jet) :=
    fun f hf g hg eq=>(hC f hf).symm.trans ((congrArg C eq).trans (hC g hg))
  have hn (f) (hf :f∈Q) :f≠0:= by
    obtain ⟨g,hg,rfl⟩:=mem_image.mp hf
    exact C_ne_zero.mp ((hC g hg).symm ▸ (hD.factors g hg).1.ne_zero)
  have hF:F≠0:=prod_ne_zero_iff.mpr hn
  have hY:F.natDegree≤12 := calc
    _ = ∑ f∈Q,f.natDegree :=natDegree_prod Q id hn
    _=ajz D 0:= by
      rw [show Q=D.image (fun f=>f.coeff 0) from rfl,sum_image hi,ajz]
      exact sum_congr rfl fun f hf=>(bri _).symm.trans
        (congrArg atc.jetDegree (hC f hf))
    _≤12 :=(hcap 0).trans_eq (by cases b <;> decide)
  have hU:My F≤ash b:= calc
    _ = ∑ f∈Q,My f :=czF.ordinarySeedDegree_prod Q hn
    _=ajz D 2 := by
      rw [show Q=D.image (fun f=>f.coeff 0) from rfl,sum_image hi,ajz]
      exact sum_congr rfl fun f hf=>(bg3 _).symm.trans
        (congrArg atc.gY (hC f hf))
    _≤ash b:=(hcap 2).trans_eq (by cases b <;> decide)
  have hseed :vm F (ash b) := by
    intro i
    by_cases hm:i∈F.support
    · exact (Finset.le_sup (f := fun j=>(F.coeff j).totalDegree) hm).trans hU
    · simp [notMem_support_iff.mp hm]
  obtain ⟨g,hg,hgY,hgU,hgraph⟩ :=
    P5_7.native_restriction hF (by cases b <;> decide :ash b<p) hseed
  let gH :=x.Γ.filter fun γ=>yq F (x.M.label γ) (x.F.scalar γ)=0
  have hpaid :gH⊆x.Γ:=filter_subset _ _
  have hit (γ) (hγ:γ∈gH) :dw≤(sites x.M.word x.F.scalar γ).card:= by
    let m:=x.F.mark γ (hpaid hγ)
    exact m.bad.dw.trans (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi))
  have marks :StrongMarks (degree b) x.M.word gH x.M.label x.F.scalar :=
    ⟨⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hpaid,
      fun γ hγ=>(P6_7.aic x.F (hpaid hγ)).trans
        (Nat.add_le_add_left (emz x).2 _),
      fun γ hγ=>(by decide :P5_7.farAgreement≤dw).trans (hit γ hγ)⟩,hit⟩
  have hc:=qXdgDRd.native_count (guard b)
    (by cases b <;> decide) (by cases b <;> decide) (by decide)
    (by cases b <;> decide) (by cases b <;> decide) (budget b)
    (fun F l h _=>q4atxtd.node_bound F l h)
    (c4y Oj charge order (width (degree b))) marks g hg (hgY.trans hY) hgU
    (fun γ hγ=>(hgraph _ _).trans (mem_filter.mp hγ).2)
  refine ⟨gH,hc.trans (Nat.sub_le _ _),fun f hf γ hγ hm=>mem_filter.mpr ⟨hγ,?_⟩⟩
  let ev :=eval₂RingHom (qD (x.M.label γ)) (kr (x.F.scalar γ))
  change ev (∏ g∈Q,g)=0
  rw [map_prod]
  apply Finset.prod_eq_zero (mem_image_of_mem _ hf)
  change rD f (x.M.label γ) (x.F.scalar γ)=0 at hm
  rwa [← hC f hf,b6E] at hm
theorem proof :qNRjwze.c1 := by
  refine of_children (fun J _ hJ r D =>qazuAoe.proof J hJ r D) ?_
    (fun J _ ι _ a x r D hi ho=>qj0Yp9c.of_children (qO4AyGb.of_children
      qWz9F7b.proof qW0d9ye.proof) qBTXDtb.proof J ι a x r D hi ho)
  intro J S _ hor γ hγ x hx
  exact qyUzJvd.of_children qnCt0Qc.proof
    qc2iTLd.proof q6lciJe.proof J S hor γ hγ x hx
end
end qdFBqnb
end
section
set_option autoImplicit true
namespace qWiv2ja
theorem proof :qlVncRd.c1 :=
  q6CrDDe.of_children q978Lma.proof P5_7_1_5_4_2_1_2.proof
end qWiv2ja
end
section
set_option autoImplicit true
namespace qV3aOCd
noncomputable section
open Finset
open P6_7_2_3 (marks)
open YY (Si a9E)
open private cag from ProximityPrize.SubmissionLower.G
open scoped Classical
def c1 :Prop :=qlVncRd.c1
def c2 :Prop :=qlVncRd.c2
theorem of_children (h1 :c1) (h2 :c2) :qu56FMb.c7:= by
  intro b x I C A hp
  have hm:q6hAhQd.DescendedMarks x (marks x I) (Si I) C 2 (a9E I) :=
    ⟨filter_subset _ _,A.root,A.irreducible,A.projection,A.plane_pos,hp,
      fun _ hγ=>cag (mem_filter.mp hγ).2⟩
  simpa only [mul_comm (2 :ℚ) (C.totalDegree :ℚ)] using
    qlVncRd.of_children h1 h2 hm
end
end qV3aOCd
end
