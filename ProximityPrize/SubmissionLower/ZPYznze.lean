import ProximityPrize.SubmissionLower.A
import ProximityPrize.SubmissionLower.B3
import ProximityPrize.SubmissionLower.P6Front
import ProximityPrize.SubmissionLower.Z9wruub
import ProximityPrize.SubmissionLower.CC
import ProximityPrize.SubmissionLower.P6Split
import ProximityPrize.SubmissionLower.Z92xlve
set_option Elab.async false
open _root_ renaming Fin.sum_univ_three → zCj, Fin.sum_univ_two → zs1, Finset → zJe, Finset.card_union_le → z2s, Fintype.sum_sum_type → zbt, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.optionEquivLeft → zpj, Nat.add_le_add_left → z3b, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.map_mul → zNl, Polynomial.map_ne_zero_iff → zeI
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
section
namespace uk
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P1 (K I node dw)


structure OF (w:I→K) (T:zJe K) (s :K→K[X]) (d:ℕ) :Prop where
 distinct :Set.InjOn s (T:Set K)
 degree : ∀ γ∈T,(s γ).natDegree≤d
 lg : ∀ γ∈T,∃ B:zJe I,dw≤B.card ∧ ∀ i∈B,(s γ).eval (node i)=w i
theorem OF.mono {w T s d} (h:OF w T s d) {U:zJe K} (hU:U⊆T) :
   OF w U s d :=
 ⟨h.distinct.mono hU,fun γ hγ=>h.degree γ (hU hγ),fun γ hγ=>h.lg γ (hU hγ)⟩


end
end uk
end
section
namespace uk
noncomputable section
open Polynomial Finset
open P1 (K I e9 jG mJ p dw)
open Dt (Reduced YQ apb wX Er acK)
open cu (L FX aZ Equation vm j9 yq)
open Qt (gY)
open MN (Ai)
open vq (Dx flatten BA separant)
open scoped BigOperators
structure Input where
 words :e9
 deleted:zJe I
 model :jG words deleted
 CF:zJe K
 family :mJ model CF
 shift_out:model.shift∉CF
 block :L[X]
 bY:YQ model family block
 marks :zJe K
 marks_sub:marks⊆CF
 f :Equation
 regular : ∀ γ∈marks,apb f (model.label γ) (family.scalar γ)
 reduced:Reduced f
 sheets :3≤f.natDegree
 seed_pos :0<gY f
 v :ℕ
 agm:vm f v
 lo:ℕ
 hi:ℕ
 lower :lo≤ model.iF.toNat
 upper :model.iF.toNat≤hi
 positive :0< model.iF.toNat
 quotient_pos :0<Er model.iF.toNat
 agreement_gap:wX hi<dw
 factorial_guard :wX hi+1<p
 separant_guard :acK f.natDegree v<p
 flat_guard :f.natDegree*wX hi+v<p
abbrev Input.w (J:Input) :ℕ:=J.model.iF.toNat
abbrev Input.ell (J:Input) :ℕ:=Er J.w
abbrev Input.e (J:Input) :ℕ:=J.f.natDegree
def Input.awm (J:Input) :L[X] :=J.block.map (frobenius L p)
def Input.HV (J:Input) :L[X] :=J.block*J.awm
abbrev pe :=MvPolynomial (Fin 2) L
def ar8 (_J:Input) (i:Fin 2) (g:K[X]) :pe[X] :=
 ((j9 g).map (if i=0 then RingHom.id L else frobenius L p)).map znf
def adn (J:Input) (i:Fin 2) :L[X] :=
 if i=0 then J.block else J.awm
def aPT (J:Input) (i:Fin 2) :pe[X] :=
  ar8 J i (J.model.factor*J.model.A₀) +
    C (z9v i)*ar8 J i (J.model.factor*J.model.A₁)
def zU (z :K) :pe →+* L :=
 MvPolynomial.eval ![algebraMap K L z,(algebraMap K L z)^p]
structure j7 (J:Input) where
 denominator :pe
 numerator :pe[X]
 ayD:denominator≠0
 bc6:denominator.totalDegree≤2*J.w
 af0 : ∀ j,(numerator.coeff j).totalDegree≤2*J.w
 numerator_width :numerator.natDegree<2*J.w
 congruences : ∀ i:Fin 2,(adn J i).map znf ∣
  aPT J i*numerator +
   C (z9v i*denominator)*ar8 J i J.model.Q
 unit_at_marks : ∀ γ∈J.CF,zU (J.model.label γ) denominator≠0
def gA:L →+* FX :=
 (algebraMap L[X] FX).comp z1z
def wZ:pe →+* aZ:=MvPolynomial.map gA
def Tk :pe →+* Ai :=
 (MvPolynomial.rename (R:=FX) (some :Fin 2→Option (Fin 2))).toRingHom.comp wZ
def center :FX:=algebraMap L[X] FX z7y
def adW (P:pe[X]) (i:ℕ) :Ai :=
 (Polynomial.taylor (znf center) (P.map Tk)).coeff i
def a4K (J:Input) (i:ℕ) :FX :=
  (i.factorial:FX)⁻¹ *
    (Dx^[i]) ((algebraMap L[X] FX J.HV)⁻¹)
def af2 (f :Equation) (r :ℕ) :ℕ→Ai
 | 0=>separant (flatten f)^(2*r-1)*MvPolynomial.X none
 | i+1=>MvPolynomial.C (((i+1).factorial:FX)⁻¹) *
     (separant (flatten f)^((2*r-1)-(2*i+1))*BA (flatten f) i)
def aj5 (J:Input) (B:j7 J) (r :ℕ) :Ai :=
  ∑ i∈range (r+1),znf (a4K J (r-i)) *
    (Tk B.denominator*af2 J.f r i -
      separant (flatten J.f)^(2*r-1)*adW B.numerator i)
def cutoff (J:Input) (B:j7 J) :Equation :=
 zpj FX (Fin 2) (aj5 J B (J.ell+1))
abbrev aQ:=FractionRing aZ
def ek (q:Equation) :aQ[X] :=q.map (algebraMap aZ aQ)
def aeR (J:Input) (q:Equation) (γ:K) :Prop :=
 yq q (J.model.label γ) (J.family.scalar γ)=0
structure Factors (J:Input) (B:j7 J) where
 proper :Equation
 count:ℕ
 flat :Fin count→Equation
 product :J.f=proper * ∏ j,flat j
 cutoff_at_marks : ∀ γ∈J.marks,aeR J (cutoff J B) γ
 proper_coprime :IsCoprime (ek proper) (ek (cutoff J B))
 flat_reduced : ∀ j,Reduced (flat j)
 flat_irred : ∀ j,Irreducible (ek (flat j))
 flat_cutoff : ∀ j,ek (flat j)∣ek (cutoff J B)
 sheets :count≤J.e
 degree_each : ∀ j,(flat j).natDegree≤J.e
 seed_sum : ∑ j,gY (flat j)≤J.v
abbrev HR:=AlgebraicClosure aQ
end
end uk
end
section
namespace yW
noncomputable section

open uk (Input j7 Factors)
open cu (FX Equation)
open vq (D6 flatten)

abbrev cO:=Polynomial Equation
instance brh:CommRing cO := @Polynomial.commRing Equation inferInstance
abbrev Degree :=ℕ×ℕ×ℕ
abbrev Qk :=Fin 2 ⊕ (Fin 2 ⊕ Fin 3)
abbrev Bw:=MvPolynomial Qk FX
def h₀:Qk := .inl 0
def h₁:Qk := .inl 1
def v₀:Qk := .inr (.inl 0)
def v₁:Qk := .inr (.inl 1)
def uw (i:Fin 3) :Qk := .inr (.inr i)
def lu:Qk→Degree
 | .inl _=>(1,0,0)
 | .inr (.inl i)=>(2*i.val,1,0)
 | .inr (.inr _)=>(0,0,1)
def jU:cO:=z1z z7y
def Ov (i:Fin 2) :cO :=
 z1z (z1z (z9v i))
def GQ:Qk→cO
 | .inl i=>if i=0 then 1 else jU
 | .inr (.inl i)=>if i=0 then 1 else Polynomial.X
 | .inr (.inr i)=>if hi:i.val<2 then Ov ⟨i.val,hi⟩ else 1
def ew:Bw →ₐ[FX] cO:=MvPolynomial.aeval GQ
def Fk (Q:Ideal cO) (d:Degree) :Submodule FX (cO ⧸ Q) :=
  (MvPolynomial.weightedHomogeneousSubmodule FX lu d).map
    (((Ideal.Quotient.mkₐ FX Q).comp ew).toLinearMap)
def Aq (f :Equation) :cO :=
  z1z (zpj FX (Fin 2) (D6 (flatten f))) +
    z7y*z1z f.derivative
def Uk {J:Input} (B:j7 J) :cO :=
 z1z (z1z (uk.wZ B.denominator))
def uf (J:Input) (B:j7 J) :cO :=
 Uk B*z1z J.f.derivative
def saturate (Q:Ideal cO) (g:cO) :Ideal cO where
  carrier := {f | ∃ n:ℕ,g^n*f∈Q}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro f h ⟨m,hm⟩ ⟨n,hn⟩
    refine ⟨m+n,?_⟩
    rw [mul_add,pow_add]
    have hf :g^m*g^n*f=g^n*(g^m*f) := by ring
    have hh:g^m*g^n*h=g^m*(g^n*h) := by ring
    rw [hf,hh]
    exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
  smul_mem' := by
    rintro a f ⟨n,hn⟩
    refine ⟨n,?_⟩
    change g^n*(a*f)∈Q
    rw [show g^n*(a*f)=a*(g^n*f) by ring]
    exact Q.mul_mem_left _ hn
def rP (J:Input) (B:j7 J) (D:Factors J B) :Ideal cO :=
 saturate (Ideal.span {z1z D.proper,Aq J.f}) (uf J B)
open scoped BigOperators
end
end yW
end
section
namespace yW
noncomputable section
open cu (FX)

open MvPolynomial
open scoped BigOperators
theorem aYh (m:Qk →₀ ℕ) :
   Finsupp.weight lu m =
     (m h₀+m h₁+2*m v₁,m v₀+m v₁,m (uw 0)+m (uw 1)+m (uw 2)) := by
 rw [Finsupp.weight_eq_sum,zbt,zbt,
   zs1,zs1,zCj]
 simp [lu,h₀,h₁,v₀,v₁,uw,Prod.mk_add_mk,Prod.smul_mk,
   Nat.mul_comm,Nat.add_assoc]
private theorem bDw (d:Degree) :
  Module.Finite FX (weightedHomogeneousSubmodule FX lu d) := by
 have hle :weightedHomogeneousSubmodule FX lu d ≤
   restrictTotalDegree Qk FX (d.1+d.2.1+d.2.2) := by
  intro p hp
  apply (mem_restrictTotalDegree _ _ _).mpr
  apply Finset.sup_le
  intro m hm
  have h:=hp (mem_support_iff.mp hm)
  rw [aYh] at h
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl),zbt,zbt,
   zs1,zs1,zCj]
  change m h₀+m h₁+(m v₀+m v₁+(m (uw 0)+m (uw 1)+m (uw 2)))≤_
  rw [← h]
  change _≤(m h₀+m h₁+2*m v₁)+(m v₀+m v₁) +
   (m (uw 0)+m (uw 1)+m (uw 2))
  omega
 exact Submodule.finiteDimensional_of_le hle
instance gP4 (Q:Ideal cO) (d:Degree) :
  Module.Finite FX (Fk Q d) := by
 have :=bDw d
 unfold Fk
 infer_instance
end
end yW
end
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6_5
noncomputable section
open Polynomial P6 gR
open private column bC7 bcH bcI bGK bOU bOV bN1 bLh outputs bJJ from ProximityPrize.SubmissionLower.B3
private def afT {u T R D} (B:KJ u T R D) (l:Fin 2) :K[X] :=
  B.a*(B.β l).map twist
private def aeb {u T R D} (B:KJ u T R D) (j:Fin 2) :K[X] :=
  -(B.b*B.α j)
private theorem azo {u T R D} (B:KJ u T R D) :
    JO B.a B.β=column p (afT B) := by
  rw [bOU]
  exact (bGK p B.a B.β).trans (congrArg (column p)
    (show (fun j=>B.a*(B.β j).map twist)=afT B by rfl))
private theorem az7 {u T R D} (B:KJ u T R D) :
    J9 B.b B.α=column 1 (aeb B) := by
  simp only [J9,aeb,column,jH,seed,zNl,Polynomial.map_neg,pow_one]
  ring
private theorem cbU {u:e9} {T:qo u} {R:Relation T}
    {D:Reduction u T R} (B:KJ u T R D) :
    Nonempty (BN.lK u (pJ R) D.height (afT B) (aeb B)) := by
  let U:=afT B
  let V:=aeb B
  have amp_ne (v :Fin 2→K[X]) (hv :IsCoprime (v 0) (v 1)) : ∃ j,v j≠0:= by
    by_contra! hz
    obtain ⟨a,b,hab⟩:=hv
    simp [hz] at hab
  obtain ⟨l,hl⟩:=amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩:=amp_ne B.α B.α_primitive
  have hU : ∃ l,U l≠0 :=
    ⟨l,mul_ne_zero B.a_ne ((zeI twist.injective).mpr hl)⟩
  have hV : ∃ j,V j≠0:=⟨j,neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
  have hu:uO (U 0) (U 1)≤D.height:= by
    unfold uO
    apply max_le
    all_goals
      apply natDegree_mul_le.trans
      apply le_trans _ B.first_degree
      apply z3b
      rw [natDegree_map_eq_of_injective twist.injective]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hv :uO (V 0) (V 1)≤D.height:= by
    unfold uO
    apply max_le
    all_goals
      simp only [V,aeb,natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply z3b
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ:=algebraMap K[X] kB
  have hinj:Function.Injective φ:=IsFractionRing.injective K[X] kB
  have hd (P:nC) : (sZ P).natDegree=P.natDegree :=natDegree_map_eq_of_injective hinj _
  have hn {P:nC} (hp:P≠0) :sZ P≠0:=(zeI hinj).mpr hp
  have hdir :=B.same_direction
  rw [Z4,azo,az7] at hdir
  have he :=congrArg (Polynomial.map φ) hdir
  simp only [zNl] at he
  have hdom:=max_le_max (bcH p U) (bcH 1 V)
  obtain ⟨htight,hcp⟩:=bOV (sZ D.U) (sZ D.V)
    (sZ (column p U)) (sZ (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (bC7 (by decide :p≠0) hU)) D.coprime he
    (by simp only [hd,D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd,D.max_degree] at htight
  refine ⟨⟨outputs p B.output,hU,hV,?_,?_,?_,?_⟩⟩
  · exact le_antisymm (max_le hu hv) (htight ▸ hdom)
  · intro f hfU hfV
    have hunit :=hcp.isUnit_of_dvd'
      ((mapRingHom φ).map_dvd (bcI p U f hfU))
      ((mapRingHom φ).map_dvd (bcI 1 V f hfV))
    apply isUnit_iff_degree_eq_zero.mpr
    change IsUnit ((f.map z1z).map φ) at hunit
    simpa only [degree_map_eq_of_injective hinj,
      degree_map_eq_of_injective Polynomial.C_injective] using isUnit_iff_degree_eq_zero.mp hunit
  · intro j l
    apply degree_le_natDegree.trans_lt
    have ht:B.output.natDegree<k+D.height:= by
      by_cases hz :B.output=0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (bN1 B.output _).trans_lt ht
  · apply bJJ p (by decide) u (pJ R) U V B.output
    have h:=B.nodes
    rwa [bLh,azo,az7] at h
private theorem dPY {u T R D} (B:KJ u T R D)
    (P:BN.lK u (pJ R) D.height (afT B) (aeb B)) :
    IsCoprime B.a B.b:= by
  apply (gcd_isUnit_iff _ _).mp
  apply P.primitive
  · intro i
    exact (gcd_dvd_left B.a B.b).trans (dvd_mul_right _ _)
  · intro j
    rw [aeb,dvd_neg]
    exact (gcd_dvd_right B.a B.b).trans (dvd_mul_right _ _)
private theorem eLS {u T R D} (B:KJ u T R D)
    (P:BN.lK u (pJ R) D.height (afT B) (aeb B))
    (par :Parallel B) (hdeg:B.b.natDegree=B.a.natDegree) :
    D.height=B.a.natDegree+uO (B.α 0) (B.α 1) := by
  let s :=uO (B.α 0) (B.α 1)
  have hA (i:Fin 2) : (B.α i).natDegree≤ s := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hL (i:Fin 2) : (afT B i).natDegree≤B.a.natDegree+s := by
    change B.α=B.β at par
    unfold afT
    rw [← par]
    exact natDegree_mul_le_of_le le_rfl (natDegree_map_le.trans (hA i))
  have hR (j:Fin 2) : (aeb B j).natDegree≤B.a.natDegree+s := by
    rw [aeb,natDegree_neg,← hdeg]
    exact natDegree_mul_le_of_le le_rfl (hA j)
  have hmax :=max_le (max_le (hL 0) (hL 1)) (max_le (hR 0) (hR 1))
  exact le_antisymm (P.height_eq ▸ hmax) (hdeg ▸ B.second_degree)
private theorem eLW {u T R D} (B:KJ u T R D)
    (P:BN.lK u (pJ R) D.height (afT B) (aeb B))
    (par :Parallel B) (x :I) (hx :x∉pJ R) (i j:Fin 2) :
    (P.output j i).eval (node x) =
      B.a.eval (node x)*((B.α i).map twist).eval (node x)*u j x -
      B.b.eval (node x)*(B.α j).eval (node x)*twist (u i x) := by
  change B.α=B.β at par
  simpa only [afT,aeb,eval_mul,eval_neg,neg_mul,
    ← sub_eq_add_neg,← par,twist,frobenius_def] using (P.nodes x hx j i).symm
theorem dXi {u T R D} (hu:abC u)
    (B:KJ u T R D) (par :Parallel B) (hnorm:aSM B) :
    Nonempty (Direction DY u (pJ R)) := by
  obtain ⟨P⟩:=cbU B
  change K1.Ox B.a=K1.Ox B.b at hnorm
  obtain ⟨den,hden,hphase,hnodes⟩:=cxN.denominator B.b_ne hnorm
  have hden' : den.map twist≠0:=(zeI twist.injective).mpr hden
  have hdeg:=congrArg (fun Q:K[X]=>Q.natDegree) hphase
  change (B.a*den.map twist).natDegree=(B.b*den).natDegree at hdeg
  rw [natDegree_mul B.a_ne hden',natDegree_mul B.b_ne hden,
    natDegree_map_eq_of_injective twist.injective] at hdeg
  have hdeg' : B.b.natDegree=B.a.natDegree := by omega
  have hcop:=dPY B P
  have hheight:=eLS B P par hdeg'
  have hdvd:B.a∣den:=hcop.dvd_of_dvd_mul_left
    (hphase ▸ dvd_mul_right B.a (den.map twist))
  have hbudget:=aEz hu T
  exact ⟨{
    den:=den
    U:=B.a
    V:=B.b
    A:=B.α
    out:= fun i j=>P.output j i
    den_nodes :=hnodes
    U_ne :=B.a_ne
    V_ne :=B.b_ne
    U_dvd:=hdvd
    coprime :=hcop
    phase :=hphase
    degrees_eq :=hdeg'
    primitive :=B.α_primitive
    height:= by rwa [← hheight,D.height_eq]
    out_degree := by
      intro i j
      simpa only [hheight,← Nat.add_assoc] using P.output_degree j i
    nodes :=eLW B P par
  }⟩
end
end P6_5
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6_5
noncomputable section
open Polynomial P6
open ProximityPrize.Benchmark
open scoped BigOperators
open private b0b same_label from ProximityPrize.SubmissionLower.CC
variable {cap:ℕ} {u:e9} {deleted:zJe I}
private theorem dPX (F:Direction cap u deleted) {γ δ:K} (hne :γ≠δ) :
    IsCoprime (F.amp γ) (F.amp δ) := by
  have hd:F.amp δ-F.amp γ*1=C (δ-γ)*F.A 1 := by
    simp only [Direction.amp,mul_one,map_sub]
    ring
  have hunit :IsUnit (C (δ-γ)) :=
    isUnit_C.mpr (sub_ne_zero.mpr hne.symm).isUnit
  apply (IsCoprime.sub_mul_left_right_iff (x :=F.amp γ) (y :=F.amp δ) (z :=1)).mp
  rw [hd,isCoprime_mul_unit_left_right hunit]
  exact F.primitive.add_mul_right_left _
private theorem card_of_failed_coprime (F:Direction cap u deleted) (S:zJe K)
    (Q:K→K[X]) {P:K[X]} (hP:P≠0)
    (hbad : ∀ γ∈S,¬ IsCoprime (F.amp γ) (Q γ))
    (hdiv : ∀ γ∈S,GCDMonoid.gcd (F.amp γ) (Q γ)∣P) :
    S.card≤P.natDegree := by
  classical
  let g (γ:K) :=GCDMonoid.gcd (F.amp γ) (Q γ)
  have hne (γ:K) (hγ:γ∈S) :g γ≠0:= by
    intro hz
    obtain ⟨H,hH⟩:=hdiv γ hγ
    change P=g γ*H at hH
    exact hP (by simpa only [hz,zero_mul] using hH)
  have hpos (γ:K) (hγ:γ∈S) :1≤(g γ).natDegree := by
    by_contra! h
    have hd: (g γ).natDegree=0:= by omega
    have hu:IsUnit (g γ) :=isUnit_iff_degree_eq_zero.mpr (by
      rw [degree_eq_natDegree (hne γ hγ),hd]
      rfl)
    exact hbad γ hγ ((gcd_isUnit_iff _ _).mp hu)
  have hpairs : (S:Set K).Pairwise (fun γ δ=>IsCoprime (g γ) (g δ)) := by
    intro γ _ δ _ hne
    exact (dPX F hne).mono (gcd_dvd_left _ _) (gcd_dvd_left _ _)
  have hprod: (∏ γ∈S,g γ)∣P:=Finset.prod_dvd_of_coprime hpairs hdiv
  calc
    S.card = ∑ γ∈S,(1 :ℕ) := by simp
    _ ≤ ∑ γ∈S,(g γ).natDegree :=Finset.sum_le_sum hpos
    _=(∏ γ∈S,g γ).natDegree :=(natDegree_prod S g hne).symm
    _≤P.natDegree :=natDegree_le_of_dvd hprod hP
private def QI (F:Direction cap u deleted) (q:ℕ) (σ:K →+* K) :K[X] :=
  ((F.A 0).map σ)*F.A 1^q-(F.A 0^q)*((F.A 1).map σ)
private theorem gcd_dvd_eliminant (F:Direction cap u deleted) (q:ℕ) [ExpChar K q]
    (σ:K →+* K) (hσ : ∀ γ,σ γ=γ^q) (hq:q≠0) (γ:K) :
    GCDMonoid.gcd (F.amp γ) ((F.amp γ).map σ)∣QI F q σ:= by
  have hpow: (F.amp γ)^q=F.A 0^q+C (σ γ)*F.A 1^q:= by
    rw [Direction.amp,add_pow_expChar _ _ q,mul_pow,← C_pow,← hσ γ]
  have heq :QI F q σ =
      ((F.amp γ).map σ)*F.A 1^q-(F.amp γ)^q*((F.A 1).map σ) := by
    rw [hpow]
    simp only [QI,Direction.amp,Polynomial.map_add,zNl,map_C]
    ring
  have hd:GCDMonoid.gcd (F.amp γ) ((F.amp γ).map σ)∣F.amp γ :=
    gcd_dvd_left _ _
  rw [heq]
  exact dvd_sub ((gcd_dvd_right _ _).mul_right _)
    ((hd.trans (dvd_pow_self _ hq)).mul_right _)
private theorem eliminant_ne (F:Direction cap u deleted) {q:ℕ} (hq:2≤q)
    (σ:K →+* K) (hs :F.s≠0) :QI F q σ≠0:= by
  intro hz
  have hcross : ((F.A 0).map σ)*F.A 1^q=F.A 0^q*((F.A 1).map σ) :=
    sub_eq_zero.mp hz
  have hp:IsCoprime (F.A 0^q) (F.A 1^q) :=F.primitive.pow
  have h0:F.A 0^q∣(F.A 0).map σ:=hp.dvd_of_dvd_mul_right
    (by rw [hcross]; exact dvd_mul_right _ _)
  have h1 :F.A 1^q∣(F.A 1).map σ:=hp.symm.dvd_of_dvd_mul_left
    (by rw [← hcross]; exact dvd_mul_left _ _)
  exact hs (by simp [Direction.s,uO,b0b hq h0,
    b0b hq h1])
private theorem eliminant_degree (F:Direction cap u deleted) (q:ℕ) (σ:K →+* K) :
    (QI F q σ).natDegree≤(q+1)*F.s := by
  have h0: (F.A 0).natDegree≤F.s :=le_max_left _ _
  have h1 : (F.A 1).natDegree≤F.s :=le_max_right _ _
  rw [QI,Nat.add_mul,one_mul]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [add_comm]
    exact natDegree_mul_le_of_le (natDegree_map_le.trans h0) (natDegree_pow_le_of_le q h1)
  · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le q h0) (natDegree_map_le.trans h1)
private theorem top_pair (F:Direction cap u deleted) :
    (F.A 0).coeff F.s≠0∨(F.A 1).coeff F.s≠0:= by
  have bbO (P:K[X]) (hp:P≠0) (hd:P.natDegree=F.s) :
      P.coeff F.s≠0:= by
    rw [← hd,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  by_cases h0:F.A 0=0
  · exact Or.inr (bbO _ (F.primitive.ne_zero_or_ne_zero.resolve_left (by simp [h0]))
      (by simp [Direction.s,uO,h0]))
  by_cases h1 :F.A 1=0
  · exact Or.inl (bbO _ h0 (by simp [Direction.s,uO,h1]))
  rcases le_total (F.A 0).natDegree (F.A 1).natDegree with h | h
  · exact Or.inr (bbO _ h1 (max_eq_right h).symm)
  · exact Or.inl (bbO _ h0 (max_eq_left h).symm)
private theorem amp_degree_le (F:Direction cap u deleted) (γ:K) :
    (F.amp γ).natDegree≤F.s :=
  natDegree_add_le_of_degree_le (le_max_left _ _)
    ((natDegree_C_mul_le _ _).trans (le_max_right _ _))
private theorem card_node_failures (F:Direction cap u deleted) (S:zJe K)
    (hS : ∀ γ∈S,∃ i:I,(F.amp γ).eval (node i)=0) :S.card≤blockLength:= by
  classical
  choose f hf using fun γ:S=>hS γ γ.property
  rw [blockLength,← IRSProfile.card_index,← Fintype.card_coe]
  apply Fintype.card_le_of_injective f
  intro γ δ he
  apply Subtype.ext
  have hγ:=hf γ
  have hδ:=hf δ
  rw [← he] at hδ
  exact same_label
    ((F.primitive.map (evalRingHom (node (f γ)))).ne_zero_or_ne_zero)
    (by simpa [Direction.amp] using hγ)
    (by simpa [Direction.amp] using hδ)
theorem excluded_card_le (F:Direction cap u deleted) (Γ:zJe K) :
    (excluded F Γ).card≤(p+1)*F.s+F.U.natDegree+blockLength+1 := by
  classical
  let A:=Γ.filter (fun γ=>F.amp γ≠0 ∧ ¬ IsCoprime (F.amp γ) ((F.amp γ).map twist))
  let U:=Γ.filter (fun γ => ¬ IsCoprime (F.amp γ) F.U)
  let N :=Γ.filter (fun γ => ∃ i:I,(F.amp γ).eval (node i)=0)
  let L:=Γ.filter (fun γ=>(F.amp γ).coeff F.s=0)
  have ha :A.card≤(p+1)*F.s := by
    by_cases hs :F.s=0
    · have hempty :A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro γ hγ
        obtain ⟨hamp,hbad⟩:=(Finset.mem_filter.mp hγ).2
        have hd:=amp_degree_le F γ
        rw [hs,Nat.le_zero] at hd
        have hunit :IsUnit (F.amp γ) :=isUnit_iff_degree_eq_zero.mpr (by
          rw [degree_eq_natDegree hamp,hd]
          rfl)
        exact hbad (by simpa only [mul_one] using
          (isCoprime_mul_unit_left_left hunit 1 _).mpr isCoprime_one_left)
      simp [hempty]
    · exact (card_of_failed_coprime F A (fun γ=>(F.amp γ).map twist)
        (eliminant_ne F (by decide :2≤p) twist hs)
        (fun _ hγ=>(Finset.mem_filter.mp hγ).2.2)
        (fun γ _=>gcd_dvd_eliminant F p twist (fun _=>rfl) (by decide) γ)).trans
          (eliminant_degree F p twist)
  have hu:U.card≤F.U.natDegree :=
    card_of_failed_coprime F U (fun _=>F.U) F.U_ne
      (fun _ hγ=>(Finset.mem_filter.mp hγ).2) (fun _ _=>gcd_dvd_right _ _)
  have hn:N.card≤blockLength :=
    card_node_failures F N (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
  have hl:L.card≤1 := by
    apply Finset.card_le_one.mpr
    intro γ hγ δ hδ
    exact same_label (top_pair F)
      (by simpa only [Direction.amp,coeff_add,coeff_C_mul] using (Finset.mem_filter.mp hγ).2)
      (by simpa only [Direction.amp,coeff_add,coeff_C_mul] using (Finset.mem_filter.mp hδ).2)
  have hsub:excluded F Γ⊆((A∪U)∪N)∪L:= by
    intro γ hγ
    obtain ⟨hΓ,hbad⟩:=Finset.mem_filter.mp hγ
    by_contra h
    simp only [Finset.mem_union,A,U,N,L,Finset.mem_filter,hΓ,true_and,
      not_or] at h
    obtain ⟨⟨⟨hA,hU⟩,hN⟩,hL⟩:=h
    have hne :F.amp γ≠0:= by
      intro hz
      exact hL (by simp [hz])
    exact hbad ⟨hne,natDegree_eq_of_le_of_coeff_ne_zero (amp_degree_le F γ) hL,
      not_not.mp (fun hbadA=>hA ⟨hne,hbadA⟩),not_not.mp hU,
      fun i _ hi=>hN ⟨i,hi⟩⟩
  have hcount:=Finset.card_le_card hsub
  have hAU:=z2s A U
  have hAUN :=z2s (A∪U) N
  have hAUNL:=z2s ((A∪U)∪N) L
  omega
end
end P6_5
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6_5
noncomputable section
open Polynomial P6 gR
private theorem eIm {A cap u deleted} {M:FJ cap u deleted} {γ δ:K} {S:K[X]}
    (m:P1.bjQ (A:=A) M γ S) (n:P1.bjQ (A:=A) M δ S) (i:I) (hi:i∈m.bad.support) :
    n.bad.decoder.eval (node i)=u 0 i+δ*u 1 i:= by
  have hd:=Finset.disjoint_left.mp m.avoids_deleted hi
  have h0:=M.first_word i hd
  have h1 :=M.second_word i hd
  have h:=congrArg (eval (node i)) n.identity
  simp only [P1.FJ.decoder,P1.FJ.wK,P1.FJ.label,eval_sub,
    eval_mul,eval_C,eval_add,m.scalar_hits i hi] at h
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show M.E.eval (node i)*_=0 from ?_)).resolve_left (M.aFF i)
  linear_combination h - h0-(δ-M.shift)*h1
private theorem glw {A cap u deleted} {M:FJ cap u deleted} {γ δ:K} {S:K[X]}
    (m:P1.bjQ (A:=A) M γ S) (n:P1.bjQ (A:=A) M δ S) :γ=δ:= by
  by_contra hne
  let V:=(δ-γ)⁻¹•(n.bad.decoder - m.bad.decoder)
  have hd:δ-γ≠0:=sub_ne_zero.mpr (Ne.symm hne)
  have hV:V.degree<k :=Principal.aNc _
    (Principal.degree_sub_lt n.bad.degree m.bad.degree)
  have hv (i:I) (hi:i∈m.bad.support) :V.eval (node i)=u 1 i:= by
    simp only [V,eval_smul,eval_sub,smul_eq_mul,eIm m n i hi,m.bad.lg i hi]
    field_simp [hd]
    ring
  apply m.bad.nonjoint
  refine ⟨⟨m.bad.decoder-γ•V,Principal.degree_sub_lt m.bad.degree
    (Principal.aNc _ hV),?_⟩,⟨V,hV,hv⟩⟩
  intro i hi
  simp only [eval_sub,eval_smul,smul_eq_mul,m.bad.lg i hi,hv i hi]
  ring
theorem proof :P6.c5:= by
  classical
  intro u hu T R D B _ par unit Γ bad normal
  by_cases hsmall:Γ.card≤aCe
  · exact Or.inl hsmall
  right
  obtain ⟨F⟩:=dXi hu B par unit
  let book :=excluded F Γ
  have hbook :book⊆Γ:=Finset.filter_subset _ _
  have hcard:book.card≤(p+1)*F.s+F.U.natDegree+blockLength+1 :=
    excluded_card_le F Γ
  have hbudget:book.card+1≤aCe := by
    have height:=F.height
    change F.U.natDegree+F.s+(pJ R).card≤DY at height
    have hprod:=Nat.mul_le_mul_left p (show F.s≤DY by omega)
    rw [Nat.add_mul,one_mul] at hcard
    rw [← dtf]
    omega
  let Δ:=Γ \ book
  have hbig:1<Δ.card:= by
    have hpart:=Finset.card_sdiff_add_card_eq_card hbook
    change Δ.card+book.card=Γ.card at hpart
    omega
  have regular (δ:K) (hd:δ∈Δ) :Regular F δ:= by
    obtain ⟨hin,hout⟩:=Finset.mem_sdiff.mp hd
    by_contra h
    exact hout (Finset.mem_filter.mpr ⟨hin,h⟩)
  let m (g:Δ) :=Classical.choice (aCl u Γ bad g.val (Finset.mem_sdiff.mp g.property).1)
  have avoid (g:Δ) :Disjoint (m g).support (pJ R) := by
    apply Finset.disjoint_left.mpr
    intro i hi hid
    exact (D.deleted_error g.val (normal g.val (Finset.mem_sdiff.mp g.property).1) (m g) i hid)
      ((m g).lg i hi)
  obtain ⟨η,hη,ζ,hζ,hne⟩:=Finset.one_lt_card.mp hbig
  let a :Δ:=⟨η,hη⟩
  let b:Δ:=⟨ζ,hζ⟩
  have hag:k+DY≤dw:= by
    change 164633≤179827
    decide
  obtain ⟨lift⟩:=dRB F (by change 231755≤262144; decide)
  obtain ⟨O⟩:=eF9 F lift hag (by change 198194≤262144; decide)
    (m a) (avoid a) (regular η hη)
  obtain ⟨M,S,marks,_⟩:=normalize F hag Δ regular m avoid a b hne.symm O
  let scalar (γ:K) :K[X] :=if h:γ∈Δ then S ⟨γ,h⟩ else 0
  have hmarked (γ:K) (hγ:γ∈Δ) :awT M γ (scalar γ) := by
    simpa only [scalar,dite_eq_left hγ] using marks ⟨γ,hγ⟩
  refine ⟨book,hbook,by omega,M,⟨⟨scalar,hmarked,?_⟩⟩⟩
  intro γ hγ δ hδ he
  exact glw (hmarked γ hγ) (he ▸ hmarked δ hδ)
end
end P6_5
end
