import ProximityPrize.SubmissionLower.E
import ProximityPrize.SubmissionLower.B5
set_option Elab.async false
open _root_ renaming Algebra.algebraMap→p5,B8.Exponent→ oy,Fin.append→pQ,Fin.append_right→zi,Fin.last→pU,Fin.sum_const→t5,Fin.sum_univ_add→uh,Fin.sum_univ_eq_sum_range→t7,Finset→lJ,Finset.mem_singleton→yJ,Finset.mul_sum→u8,Finset.sum_add_distrib→ oY,Finset.sum_congr→lI,Finset.sum_eq_single→t9,Finset.sum_eq_zero→vG,Finset.sum_le_sum→qx,Finset.univ→v8,Finsupp.add_apply→zf,Finsupp.finsetSum_apply→zh,Finsupp.induction_linear→xL,Finsupp.single→ oq,Finsupp.single_apply→zR,Finsupp.single_eq_of_ne→x7,Finsupp.weight→nI,Finsupp.weight_apply→xW,Finsupp.weight_single→pC,Fintype→p7,Fintype.card→t8,Fintype.card_fin→v9,Fintype.card_sigma→zg,Function.Surjective→wB,Function.iterate_succ_apply'→yL,Ideal→c9,Ideal.Quotient.mk→t4,Ideal.Quotient.mkₐ→u5,Ideal.mem_homogeneousCore_of_homogeneous_of_mem→yl,Ideal.mem_span_singleton_self→qM,Ideal.mem_sup_right→z8,Ideal.quotientMap_injective→zE,Ideal.quotientMapₐ→Aa,Ideal.span→nX,Ideal.span_singleton_le_iff_mem→xu,Ideal.toIdeal_homogeneousCore_le→sS,IsLeftRegular→t6,IsLeftRegular.pow→yU,IsLocalization.Away.lift→z9
open _root_ renaming Jq.Represents→uz,Jq.squarefree→uW,Module.finrank→uJ,MvPolynomial→vi,MvPolynomial.C→ oj,MvPolynomial.X→ ox,MvPolynomial.affineHilbertPolynomial→lV,MvPolynomial.eq_affineHilbertPolynomial_of_eval_eq→zS,MvPolynomial.eval→pG,MvPolynomial.eval₂Hom→y5,MvPolynomial.isWeightedHomogeneous_monomial→zm,MvPolynomial.mem_iff_weightedHomogeneousComponent_mem→xI,MvPolynomial.monomial→nq,MvPolynomial.monomialMap→mD,MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective→yo,MvPolynomial.restrictSupport→pz,MvPolynomial.restrictSupport_eq_span→t3,MvPolynomial.restrictTotalDegree→qG,MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported→ze,Nat.add_zero→vw,Nat.cast_one→vj,Nat.cast_sub→ oz,Nat.cast_zero→zd,Nat.le_add_right→vk,Nat.le_mul_of_pos_right→zk,Nat.mul_le_mul_left→sH,Nat.mul_left_comm→vZ,Nat.mul_zero→xm,Polynomial→n5,Polynomial.C→qJ,Polynomial.X→p6,Polynomial.derivative→qz,Set.mem_fintype_sum→vh,Set.mem_zero→wA,Submodule.map_le_iff_le_comap→zc,Submodule.span_le→th,aR.Shape→aU,aR.Shape.scale→ oZ,add_zero→u9,agM.diagonal→qU,dN.GeoField→cy,dN.separant→lz,ite_eq_left→vH,ite_eq_right→p9
open _root_ renaming le_antisymm→vl,le_rfl→pL,le_sup_left→qm,le_sup_right→wY,map_sum→ oK,one_smul→sI,smul_eq_mul→wR,zero_add→ oD
set_option autoImplicit true
section
namespace ac7
noncomputable section
open Polynomial

open Ds (bf)
open aR (af bY)
open dN (bC su AX oA GeoJets kC YR Invariant pK)
open vS (oe g9)
open scoped BigOperators
def vU (g:af 4) :af 4 :=su g bf
def ZV (g:af 4) :af 4 :=su g (bf+1)
structure Branch (f Q:af 4) (l:ℕ) where
 aI:c9 GeoJets
 r :ℕ
 base : (kC f Q).IsMinimalPrime aI
 high: (l:ℕ∞)≤oA (kC f Q) aI base.isPrime
 bY:YR f aI r
 invariant:Invariant ((lz^[r]) f) aI
 proper :bC (vU ((lz^[r]) f))∉aI
 curve :c9 GeoJets
 divisor : (AX aI (vU ((lz^[r]) f))).IsMinimalPrime curve
 regularCurve :bC (lz ((lz^[r]) f))∉curve
 terminal :
   oA (AX aI (vU ((lz^[r]) f))) curve
     divisor.isPrime≠1∨bC (ZV ((lz^[r]) f))∉curve
namespace Branch
variable {f Q:af 4} {l:ℕ} (b:Branch f Q l)
def g:af 4 :=(lz^[b.r]) f
def sigma :GeoJets :=bC (lz b.g)
def member :GeoJets :=bC (vU b.g)
def next:GeoJets :=bC (ZV b.g)
def Simple :Prop :=oA (AX b.aI (vU b.g))
 b.curve b.divisor.isPrime=1
def weight:ℕ:= by classical exact if b.Simple then 1 else 2
def dY (p:oe) :Prop :=
 b.curve≤RingHom.ker (pG p)∧pG p b.sigma≠0
abbrev Local:=Localization.Away b.sigma
def vN :GeoJets →+* b.Local:=p5 GeoJets b.Local
def yu:g9 →+* b.Local :=
  y5 (b.vN.comp oj)
    (Fin.lastCases
      (b.vN (oj (-(4 :cy)⁻¹)*bC (pK b.g)) *
        IsLocalization.Away.invSelf b.sigma)
      (fun i=>b.vN (ox i)))
def a5x :c9 b.Local:=b.curve.map b.vN
end Branch
def Sx (a :aU) (z :ℕ) (m:Fin 5 →₀ ℕ) :Prop :=
  let t:=m (pU 4)
  ((∑ i:Fin 4,m i.castSucc)+t≤a.b) ∧
    ((∑ i:Fin 4,i.val*m i.castSucc)+4*t≤a.j) ∧
    (m ((3:Fin 4).castSucc)+2*t≤a.t)∧t≤z
def FH (a :aU) (z :ℕ) (D:g9) :Prop :=
 ∀ m∈D.support,Sx a z m
end
end ac7
end
section
namespace ac7
noncomputable section
open Polynomial MvPolynomial
open aR (af)
open dN (j8 bC)
open vS (g9 agB)
open aKq (Chart incl)
open scoped BigOperators
variable {f Q:af 4} {l:ℕ}
@[simp] theorem cad (b:Branch f Q l) (a :cy) :
   b.yu (oj a)=b.vN (oj a) := by
  simp [Branch.yu]
private def aAy (b:Branch f Q l) :Chart b.g →+* b.Local :=
 z9 (lz b.g)
  (g:=b.vN.comp (MvPolynomial.map j8))
  (IsLocalization.Away.algebraMap_isUnit b.sigma)
@[simp] private theorem a87 (b:Branch f Q l) (P:af 4) :
   aAy b (incl b.g P)=b.vN (bC P) :=
  IsLocalization.Away.lift_eq _ _ _
local notation "aeq" => MvPolynomial.weightedTotalDegree
theorem FH.ctq {a :aU} {z :ℕ} {D:g9}
    (h:FH a z D) :agB ⟨a.b,a.j,min a.t (a.j/3)⟩ z D:= by
  constructor
  · intro m hm
    obtain ⟨hb,hj,ht,_⟩:=h m hm
    have hIndex :=(vk _ _).trans hj
    have hThree :3*m ((3:Fin 4).castSucc) ≤ ∑ i:Fin 4,i.val*m i.castSucc :=
      Finset.single_le_sum (f := fun i:Fin 4=>i.val*m i.castSucc)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ (3:Fin 4))
    refine ⟨(vk _ _).trans hb,hIndex,le_min ((vk _ _).trans ht) ?_⟩
    exact (Nat.le_div_iff_mul_le (by decide :0<3)).mpr
      (by simpa only [Nat.mul_comm] using hThree.trans hIndex)
  · exact fun m hm=>(h m hm).2.2.2
end
end ac7
end
section
namespace bAm
noncomputable section
open Polynomial
open aR (af ao shape aO cK Dd)
open dN (GeoJets YR bC Ch)
open BO (m6 Ue)
open akM (bc7)
open private ur bO1 bFv bxU from ProximityPrize.SubmissionLower.AF
theorem bmF {f :af 4} {aI:c9 GeoJets} {S:ao[X]}
    (htop: (shape f).t<K1.p) (hon :Dd f S)
    (hfmem:bC f∈aI) (hmark :aI≤Ch S) :
    ∃ r,YR f aI r ∧
      aO (shape (lz ((lz^[r]) f))) (m6 f) := by
  classical
  let t:=(shape f).t
  let P:=ur S f
  have hdeg:P.natDegree≤t:=Polynomial.natDegree_map_le.trans_eq
    (Ex.aQU f)
  have hnz : (qz^[t] P).coeff 0≠0:= by
    rw [coeff_iterate_derivative,Nat.zero_add,Nat.descFactorial_self,nsmul_eq_mul]
    change (t.factorial:ao[X])*P.coeff t≠0
    rw [← map_natCast (qJ:ao →+* ao[X])]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      (lB.ahA htop))
      (by simpa only [P,t,bO1] using hon.2)
  have hc:qz^[t] P=qJ ((qz^[t] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans
      (by omega :P.natDegree - t≤0))
  have he (k :ℕ) :cK ((lz^[k]) f) S =
      (qz^[k] P).eval (aR.jet S (3:Fin 4)) := by
    rw [← bFv]
    congr 1
    induction k with
    | zero=>rfl
    | succ k ih =>
      simp only [yL]
      change (Ex.YN (lz ((lz^[k]) f))).map
        (pG (aR.jet S))= _
      rw [bxU,← derivative_map]
      exact congrArg qz ih
  have htSurface :bC ((lz^[t]) f)∉aI:= by
    intro hm
    have hv :=Ue.mp (hmark hm)
    rw [he,hc,Polynomial.eval_C] at hv
    exact hnz hv
  have hex : ∃ i,bC ((lz^[i]) f)∉aI:=⟨t,htSurface⟩
  let n:=Nat.find hex
  have hn:bC ((lz^[n]) f)∉aI:=Nat.find_spec hex
  have hnt:n≤(shape f).t:=Nat.find_min' hex htSurface
  have hn0:n≠0:= by
    intro h
    exact hn (by simpa only [h,Function.iterate_zero_apply] using hfmem)
  have hstep: (n - 1).succ=n:= by omega
  have hsep:lz ((lz^[n - 1]) f)=(lz^[n]) f := by
    rw [← yL lz (n - 1) f,hstep]
  refine ⟨n - 1,⟨by omega,?_,?_⟩,?_⟩
  · intro i hi
    by_contra h
    exact Nat.find_min hex (show i<n by omega) h
  · rwa [hsep]
  · rw [hsep]
    exact bc7 f n
end
end bAm
end
section
namespace NU
noncomputable section
open ac7 (Sx)


open vS (g9)
open B8 (lS bF Exponent TB Component)
open scoped BigOperators
def agJ (a :aU×ℕ) :Prop :=
 bF a.1∧2*a.2≤a.1.t
def LJ (a :aU×ℕ) :Set Exponent :=
 {m | Sx (a.1.scale 2) (2*a.2) m}
instance gQh (a :aU×ℕ) :Finite (LJ a) := by
 apply Set.Finite.to_subtype
 refine (Finsupp.finite_of_degree_le (2*a.1.b)).subset ?_
 intro m hm
 change m.degree≤_
 rw [Finsupp.degree_eq_sum,Fin.sum_univ_castSucc]
 exact hm.1
def Admissible (B:lS) :Prop :=
  (∀ i,agJ (B i)) ∧
    (∀ v :Fin 5,Sx (B 4).1 (B 4).2 (oq v 1))
def D0 (B:lS) (t:Fin 5→ℕ) :Set Exponent :=
  {m | ∃ u: (i:Fin 5)→Fin (t i)→ oy ,
    (∀ i j,u i j∈LJ (B i))∧m = ∑ i,∑ j,u i j}
instance gQg (B:lS) (t:Fin 5→ℕ) :
   Finite (D0 B t) := by
 let addExponents (u: (i:Fin 5)→Fin (t i)→LJ (B i)) :Exponent :=
   ∑ i,∑ j,(u i j).val
 have heq :D0 B t=Set.range addExponents := by
   ext m
   constructor
   · rintro ⟨u,hu,rfl⟩
     exact ⟨fun i j=>⟨u i j,hu i j⟩,rfl⟩
   · rintro ⟨u,rfl⟩
     exact ⟨fun i j=>(u i j).val,fun i j=>(u i j).property,rfl⟩
 rw [heq]
 exact (Set.finite_range _).to_subtype
def RW (B:lS) (P:c9 g9) (I:lJ (Fin 5)) :ℚ :=
  (∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) *
    (lV (Ideal.comap
      (mD cy
        (D0 B (qU J))) P)).coeff I.card)/(2 :ℚ)^I.card
def aYC:Prop :=
  ∀ (B:lS),Admissible B →
    ∀ (P:c9 g9) (I:lJ (Fin 5)) (i:Fin 5),
      P.IsPrime→i∉I→TB P (I.card+1) →
      ∀ (D:g9),ac7.FH (B i).1 (B i).2 D→D∉P →
        ∀ {ι:Type} (S:lJ ι) (C:ι→ c9 g9) (w:ι→ℕ),
          Set.InjOn C (S:Set ι)→(∀ a∈S,Component P D (C a) (w a)) →
          (∑ a∈S,(w a :ℚ)*RW B (C a) I)≤RW B P (insert i I)
def hvol (x :ℚ×ℚ×ℚ) :ℚ :=
 let b:=x.1
 let j:=x.2.1
 let f :=x.2.2
 8*b*j^2*f - 24*b*j*f^2+24*b*f^3-4*j^3*f+14*j^2*f^2 - 20*j*f^3+9*f^4
def aD (a :aU) :ℚ×ℚ×ℚ:=(a.b,a.j,a.t)
def direction :ℚ×ℚ×ℚ:=(1,4, 2)
def ic (r :ℚ) (a :aU×ℕ) :ℚ×ℚ×ℚ :=
 aD a.1-(r*(a.2 :ℚ))•direction
def azm (a :aU×ℕ) :ℚ :=
  ((7/90)*hvol (ic 0 a)+(32/90)*hvol (ic (1/4) a) +
    (12/90)*hvol (ic (1 / 2) a)+(32/90)*hvol (ic (3/4) a) +
    (7/90)*hvol (ic 1 a))*(a.2 :ℚ)
end
end NU
end
section
namespace NU
noncomputable section
open ac7 (Sx FH)
open aR (shape aO af)
open dN (bC)
open vS (g9)
open B8 (lS TB oF qK)
open scoped BigOperators
open private eval_surjective a6D cb3 bdx
 from ProximityPrize.SubmissionLower.BI
theorem b99 {P:af 4} {p:aU} (hP:aO (shape P) p) :
  FH p 0 (qK (bC P)) := by
 intro m hm
 have h:=(B8.bms (a :=(p,0))).mp (B8.bJT hP) m hm
 have hz :m (pU 4)=0:=Nat.eq_zero_of_le_zero h.2.2.2
 simpa only [Sx,B8.Qj,hz,xm,vw] using h
private theorem cH7 {a :aU} {z :ℕ}
   (h:1≤a.b∧4≤a.j∧2≤a.t∧1≤z) (v :Fin 5) :
   Sx a z (oq v 1) := by
 obtain ⟨hb,hj,ht,hz⟩:=h
 by_cases hv :v=pU 4
 · subst v
   have hzero (i:Fin 4) :oq (pU 4) 1 i.castSucc=(0:ℕ) :=
     x7 (Fin.castSucc_ne_last i)
   simpa only [Sx,hzero,Finset.sum_const_zero,xm,vw ,oD,
     Finsupp.single_eq_same,Nat.mul_one]
     using And.intro hb (And.intro hj (And.intro ht hz))
 · have hzero :oq v 1 (pU 4)=(0:ℕ) :=
     x7 (Ne.symm hv)
   have hj' : 3≤a.j:= by omega
   have ht' : 1≤a.t:= by omega
   have hbox :=B8.blp (a :=(a,z)) ⟨hb,hj',ht',hz⟩ v
   simpa only [Sx,B8.Qj,hzero,xm,vw] using hbox
private theorem cHP (a :aU×ℕ) (s :cy) :
   FH a.1 a.2 (oj s) := by
 classical
 intro m hm
 by_cases hs :s=0
 · simp [hs] at hm
 · rw [MvPolynomial.support_C,p9 hs,yJ] at hm
   subst m
   simp [Sx]
private theorem bYM {B:lS} (hB:Admissible B)
   (z :Fin 5→cy) (i:Fin 5) :
   FH (B 4).1 (B 4).2 (ox i-MvPolynomial.C (z i)) := by
 intro m hm
 rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ hm) with hX | hC
 · rw [MvPolynomial.support_X,yJ] at hX
   exact hX ▸ hB.2 i
 · exact cHP (B 4) (z i) m hC
private theorem bge (B:lS) (z :Fin 5→cy) :
  RW B (oF z) ∅ = 1 := by
 let A:=D0 B (fun _=>1)
 let φ:=(MvPolynomial.aeval z).comp (mD cy A)
 have hφ:wB φ:= fun a=>⟨oj a,φ.commutes a⟩
 have heq : (oF z).comap (mD cy A)=RingHom.ker φ:=rfl
 let e :=Ideal.quotientKerAlgEquivOfSurjective hφ
 let:=Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
 unfold RW
 simp only [Finset.powerset_empty,Finset.sum_singleton,Finset.card_empty,tsub_self,
  pow_zero,one_mul,div_one]
 change (lV
  ((oF z).comap (mD cy A))).coeff 0=1
 rw [heq,MvPolynomial.affineHilbertPolynomial_eq_C_finrank,Polynomial.coeff_C_zero,
  e.toLinearEquiv.finrank_eq,Module.finrank_self,vj]
private theorem btG (H :aYC) (B:lS) (hB:Admissible B)
    (C:c9 g9) (hprime :C.IsPrime) (hdim:TB C 1)
    (U:lJ (Fin 5→cy)) (hU : ∀ z∈U,C≤oF z)
    (hslice :U.card≤1 ∨
      ∃ D,FH (B 4).1 (B 4).2 D ∧D∉C ∧ ∀ z∈U,pG z D =0) :
    (U.card:ℚ)≤RW B C {4} := by
  classical
  have aM7 (D:g9) (hBox :FH (B 4).1 (B 4).2 D) (hproper :D∉C)
      (hD : ∀ z∈U,pG z D =0) : (U.card:ℚ)≤RW B C {4} := by
    have hb:=H B hB C ∅ 4 hprime (by simp) hdim D hBox hproper U oF (fun _=>1)
      a6D.injOn (fun z hz=>cb3 hprime hdim (hU z hz) hproper (hD z hz))
    simpa [bge] using hb
  rcases hslice with hone | ⟨D,hD,hp,hz⟩
  · by_cases hempty :U = ∅
    · apply aM7 (oj 1) (cHP (B 4) 1)
      · rw [map_one]
        exact (Ideal.ne_top_iff_one C).mp hprime.ne_top
      · simp [hempty]
    obtain ⟨z,hz⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
    have hlt:C<oF z := by
      refine lt_of_le_of_ne (hU z hz) ?_
      intro h
      rw [h,TB,oF] at hdim
      have e :=(pG z).quotientKerEquivOfSurjective (eval_surjective z)
      rw [e.ringKrullDim,ringKrullDim_eq_zero_of_field] at hdim
      exact (by decide : (0:WithBot ℕ∞)≠1) hdim
    obtain ⟨i,hi⟩:=bdx hlt
    apply aM7 _ (bYM hB z i) hi
    intro y hy
    have hyz :=Finset.card_le_one.mp hone y hy z hz
    subst y
    simp
  · exact aM7 D hD hp hz
end
end NU
end
section
namespace NU
open ac7 (Sx)
open aR (Shape)
open B8 (lS Exponent)
open agM (Vw agj bOu)
open scoped BigOperators Pointwise
private theorem aOj (a :aU×ℕ) (e :oy) :
  e∈LJ a ↔
    e 0+e 1+e 2+e 3+e 4≤2*a.1.b ∧
    e 1+2*e 2 + 3*e 3+4*e 4≤2*a.1.j ∧
    e 3+2*e 4≤2*a.1.t∧e 4≤2*a.2 := by
 change Sx (a.1.scale 2) (2*a.2) e↔_
 simp only [Sx,Fin.sum_univ_four,oZ]
 change (_∧(0*e 0+1*e 1+2*e 2 + 3*e 3+4*e 4≤_)∧_∧_)↔_
 simp
private theorem eqk (p q:aU) (r s :ℕ)
    (hp:agJ (p,r)) (hq:agJ (q,s)) :
    LJ (p,r)+LJ (q,s)=LJ (p.plus q,r+s) := by
  ext e
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    simp only [aOj,Shape.plus,zf] at *
    omega
  · rintro he
    obtain ⟨⟨hpb,hpj⟩,hpr⟩:=hp
    obtain ⟨⟨hqb,hqj⟩,hqs⟩:=hq
    change 2*r≤p.t at hpr
    change 2*s≤q.t at hqs
    simp only [aOj,Shape.plus] at he
    let v :=min (e 4) (2*r)
    let v' := e 4 - v
    have hv :v+v' = e 4∧v≤2*r∧v' ≤ 2*s := by dsimp [v,v']; omega
    let bp:=2*p.b - v
    let jp:=2*p.j-4*v
    let tp:=2*p.t - 2*v
    let bq:=2*q.b - v'
    let jq:=2*q.j-4*v'
    let tq:=2*q.t - 2*v'
    have hP:bp+v=2*p.b∧jp+4*v=2*p.j∧tp+2*v=2*p.t ∧
        jp≤bp∧3*tp≤jp∧jp % 2=0∧tp % 2=0:= by
      change p.j≤p.b at hpb
      change 3*p.t≤p.j at hpj
      dsimp [bp,jp,tp]
      omega
    have hQ:bq+v' = 2*q.b∧jq+4*v' = 2*q.j∧tq+2*v' = 2*q.t ∧
        jq≤bq∧3*tq≤jq∧jq % 2=0∧tq % 2=0:= by
      change q.j≤q.b at hqb
      change 3*q.t≤q.j at hqj
      dsimp [bq,jq,tq]
      omega
    let z :=min (e 3) tp
    let z' := e 3 - z
    have hz :z+z' = e 3∧z≤tp∧z' ≤ tq:= by dsimp [z,z']; omega
    let w:=jp-3*z
    let w' := jq-3*z'
    have hw:w+3*z=jp∧w' + 3*z' = jq:= by dsimp [w,w']; omega
    have hhalf : (w+w')/2=w/2+w' / 2 := by
      by_cases h:e 3≤tp
      · have hz' : z' = 0:= by dsimp [z,z']; omega
        omega
      · have hze :z=tp:=min_eq_right (by omega)
        omega
    let y :=min (e 2) (w/2)
    let y' := e 2 - y
    have hy :y+y' = e 2∧2*y≤w∧2*y' ≤ w' := by dsimp [y,y']; omega
    let x :=min (e 1) (w - 2*y)
    let x' := e 1 - x
    have hx :x + x' = e 1∧x+2*y≤w∧x' + 2*y' ≤ w' := by
      dsimp [x,x']
      omega
    let u:=min (e 0) (bp-(x+y+z))
    let u' := e 0 - u
    have hu:u+u' = e 0∧u + x+y+z≤bp∧u' + x' + y' + z' ≤ bq:= by
      dsimp [u,u']
      omega
    let a :Exponent:=Finsupp.equivFunOnFinite.symm ![u,x,y,z,v]
    let b:Exponent:=Finsupp.equivFunOnFinite.symm ![u',x',y',z',v']
    refine ⟨a,(aOj (p,r) a).2 ?_,b,
      (aOj (q,s) b).2 ?_,?_⟩
    · change u + x+y+z+v≤2*p.b∧x+2*y+3*z+4*v≤2*p.j ∧
        z+2*v≤2*p.t∧v≤2*r
      omega
    · change u' + x' + y' + z' + v' ≤ 2*q.b∧x' + 2*y' + 3*z' + 4*v' ≤ 2*q.j ∧
        z' + 2*v' ≤ 2*q.t∧v' ≤ 2*s
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
      · exact hv.1
private theorem eql:LJ (⟨0,0,0⟩,0)=0:= by
 ext e
 rw [aOj,wA]
 constructor
 · rintro ⟨h,_,_,_⟩
   change e 0+e 1+e 2+e 3+e 4≤0 at h
   have h0:e 0=0:= by omega
   have h1 :e 1=0:= by omega
   have h2 :e 2=0:= by omega
   have h3:e 3=0:= by omega
   have h4 :e 4=0:= by omega
   ext i
   fin_cases i
   · exact h0
   · exact h1
   · exact h2
   · exact h3
   · exact h4
 · rintro rfl
   simp
private theorem df0 {ι:Type*} (I:lJ ι) (A:ι→aU×ℕ)
    (hA : ∀ i,agJ (A i)) :
    (∑ i∈I,LJ (A i))=LJ
      (⟨∑ i∈I,(A i).1.b,∑ i∈I,(A i).1.j,∑ i∈I,(A i).1.t⟩,∑ i∈I,(A i).2) := by
  classical
  induction I using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,eql]
  | insert i I hi ih =>
    have hI:agJ
        (⟨∑ k∈I,(A k).1.b,∑ k∈I,(A k).1.j,∑ k∈I,(A k).1.t⟩,∑ k∈I,(A k).2) := by
      refine ⟨⟨qx (fun k _=>(hA k).1.1),?_⟩,?_⟩
      · change 3*(∑ k∈I,(A k).1.t) ≤ ∑ k∈I,(A k).1.j
        rw [u8]
        exact qx fun k _=>(hA k).1.2
      · change 2*(∑ k∈I,(A k).2) ≤ ∑ k∈I,(A k).1.t
        rw [u8]
        exact qx fun k _=>(hA k).2
    simp only [Finset.sum_insert hi]
    rw [ih,eqk _ _ _ _ (hA i) hI]
    rfl
private theorem c1P (a :aU×ℕ) (ha :agJ a) (n:ℕ) :
  n•LJ a=LJ (agj a n) := by
 simpa only [Finset.sum_const,Finset.card_univ,v9,Nat.nsmul_eq_mul,
  agj,oZ] using
  df0 (v8 :lJ (Fin n)) (fun _=>a) (fun _=>ha)
private theorem BP (a :aU×ℕ) (ha :agJ a) (n:ℕ) :
   agJ (agj a n) := by
 refine ⟨⟨sH n ha.1.1,?_⟩,?_⟩
 · change 3*(n*a.1.t)≤n*a.1.j
   rw [vZ 3 n]
   exact sH n ha.1.2
 · change 2*(n*a.2)≤n*a.1.t
   rw [vZ 2 n]
   exact sH n ha.2
private theorem b0y (B:lS) (t:Fin 5→ℕ) :
    D0 B t = ∑ i,∑ _j:Fin (t i),LJ (B i) := by
  classical
  ext e
  rw [vh]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨fun i => ∑ j,u i j,fun i=>(vh _ _).2 ⟨u i,hu i,rfl⟩,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    have h (i:Fin 5) : ∃ u:Fin (t i)→ oy ,
        (∀ j,u j∈LJ (B i)) ∧ ∑ j,u j=v i:= by
      obtain ⟨u,hu,hs⟩:=(vh _ _).1 (hv i)
      exact ⟨u,hu,hs⟩
    choose u hu hs using h
    exact ⟨u,hu,by simp only [hs]⟩
theorem cru (B:lS) (hB : ∀ i,agJ (B i)) (t:Fin 5→ℕ) :
  agJ (Vw B t) := by
 refine ⟨bOu B (fun i=>(hB i).1) t,?_⟩
 change 2*(∑ i,t i*(B i).2) ≤ ∑ i,t i*(B i).1.t
 rw [u8]
 exact qx fun i _=> by
  simpa only [vZ] using sH (t i) (hB i).2
theorem c3l (B:lS) (hB : ∀ i,agJ (B i)) (t:Fin 5→ℕ) (n:ℕ) :
    n•D0 B t=LJ (agj (Vw B t) n) := by
  have hdiag:D0 B t=LJ (Vw B t) := calc
    _ = ∑ i,∑ _j:Fin (t i),LJ (B i) :=b0y B t
    _ = ∑ i,LJ (agj (B i) (t i)) := by
      apply lI rfl
      intro i _
      simpa only [Finset.sum_const,Finset.card_univ,v9] using
        c1P (B i) (hB i) (t i)
    _=LJ (Vw B t) :=
      df0 v8 (fun i=>agj (B i) (t i))
        (fun i=>BP (B i) (hB i) (t i))
  rw [hdiag]
  exact c1P (Vw B t) (cru B hB t) n
theorem byT (B:lS) (t:Fin 5→ℕ) :0∈D0 B t :=
 ⟨fun _ _=>0,fun i _=>(aOj (B i) 0).2 (by simp),by simp⟩
end NU
end
section
namespace NU
noncomputable section
open Ds (wP)
open aR (Shape Dn gI)
open agM (a1Z)
open scoped BigOperators
open private DB bB8 bB9 from ProximityPrize.SubmissionLower.BI
private abbrev Coordinates :=ℚ×ℚ×ℚ
private def translate (a :Coordinates) (F:Coordinates→ℚ) (x :Coordinates) :ℚ :=
 F (x+a)
private def diff (a :Coordinates) (F:Coordinates→ℚ) (x :Coordinates) :ℚ :=
 F (x+a)-F x
private def polar (p q r s :Coordinates) :ℚ :=
 diff s (diff r (diff q (diff p hvol))) 0
private theorem dWS (a b:Coordinates) (F:Coordinates→ℚ) :
  diff b (translate a F)=translate a (diff b F) := by
 funext x
 simp only [diff,translate,add_right_comm x b a]
private theorem dWJ (a b:Coordinates) (F:Coordinates→ℚ) :
  diff a (diff b F)=diff b (diff a F) := by
 funext x
 simp only [diff,add_right_comm x a b]
 ring
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 4096 in
private theorem bGV (p q r s :Coordinates) :
  diff s (diff r (diff q (diff p hvol)))=fun _=>polar p q r s := by
 funext x
 simp only [diff,polar,hvol,Prod.fst_add,Prod.snd_add,Prod.fst_zero,Prod.snd_zero]
 ring
private theorem btK (p q r s :Coordinates) :polar p q r s=polar p q s r := by
 unfold polar
 rw [dWJ s r]
private def cb7 (p q r :Coordinates) :Coordinates →+ ℚ where
 toFun:=polar p q r
 map_zero' := by simp [polar,diff]
 map_add' := by
  intro s t
  let F:=diff r (diff q (diff p hvol))
  have hh:F (s+t)-F s=F t - F 0:= by
   have h:=congrFun (bGV p q r t) s
   simpa only [diff,polar,oD,F] using h
  change diff (s+t) F 0=diff s F 0+diff t F 0
  simp only [diff,oD]
  linarith only [hh]
private theorem c4u (p q a b d:Coordinates) (v :ℚ) :
  polar p q a (b - v•d)=polar p q a b - v*polar p q a d:= by
 change cb7 p q a (b - v•d)=cb7 p q a b - v*cb7 p q a d
 rw [map_sub,map_rat_smul,wR]
private theorem eMB (p q a b d:Coordinates) (v :ℚ) :
  polar p q (a - v•d) b=polar p q a b - v*polar p q d b:= by
 rw [btK p q (a-_) b,c4u,btK p q b a,btK p q b d]
private theorem cIb (a b:aU) :
  aD (a.plus b)=aD a+aD b:= by
 simp [aD,Shape.plus,Nat.cast_add]
private theorem dd1 (r :ℚ) (a b:aU×ℕ) :
  ic r (a1Z a b)=ic r a+ic r b:= by
 simp only [ic,a1Z,cIb,Nat.cast_add,mul_add,add_smul]
 abel
private theorem gqJ (r :ℚ) (a :aU) :
 ic r (a,0)=aD a := by simp [ic]
private def ayr (r :ℚ) (F:Coordinates→ℚ) (x :aU×ℕ) :ℚ :=
 F (ic r x)
private def ahP (r :ℚ) (F:Coordinates→ℚ) (x :aU×ℕ) :ℚ :=
 F (ic r x)*x.2
private theorem dWK (a :aU) (d:ℕ) (r :ℚ) (F:Coordinates→ℚ) :
  DB (a,d) (ayr r F)=ayr r (diff (ic r (a,d)) F) := by
 funext x
 simp only [DB,ayr,dd1,diff]
private theorem dWL (a :aU) (d:ℕ) (r :ℚ) (F:Coordinates→ℚ) :
    DB (a,d) (ahP r F) =
      fun x=>ahP r (diff (ic r (a,d)) F) x +
        (d:ℚ)*ayr r (translate (ic r (a,d)) F) x := by
  funext x
  simp only [DB,ahP,ayr,diff,translate,dd1]
  change _ *((x.2+d:ℕ) :ℚ)-_ = _
  push_cast
  ring
private theorem glC (p q g a b:aU) (u v :ℕ) (r :ℚ) (x :aU×ℕ) :
    DB (b,v) (DB (a,u) (DB (g,1) (DB (q,0)
      (DB (p,0) (ahP r hvol))))) x =
      polar (aD p) (aD q) (ic r (a,u)) (ic r (b,v)) +
        (u:ℚ)*polar (aD p) (aD q) (ic r (g,1)) (ic r (b,v)) +
        (v :ℚ)*polar (aD p) (aD q) (ic r (g,1)) (ic r (a,u)) := by
  simp only [dWL,bB8,bB9,dWK,
    zd ,zero_mul,u9,gqJ,dWS,bGV]
  simp only [ahP,ayr,translate,diff,sub_self,zero_mul,
    oD,vj,one_mul]
  ring
private theorem glD (p q g a b:aU) (u v :ℕ) (r :ℚ) (x :aU×ℕ) :
    let V:=polar (aD p) (aD q)
    let G:=aD g
    let A:=aD a
    let B:=aD b
    DB (b,v) (DB (a,u) (DB (g,1) (DB (q,0)
      (DB (p,0) (ahP r hvol))))) x =
      V A B+(u:ℚ)*V G B+(v :ℚ)*V G A -
        2*r*((u:ℚ)*V direction B+(v :ℚ)*V direction A +
          (u:ℚ)*(v :ℚ)*V direction G) +
        3*r^2*(u:ℚ)*(v :ℚ)*V direction direction := by
  dsimp only
  rw [glC]
  simp only [ic,eMB,c4u,vj,mul_one,
    btK _ _ (aD a) direction,btK _ _ (aD g) direction]
  ring
private theorem dju (p q g a b:aU) (u v :ℕ) (x :aU×ℕ) :
    let V:=polar (aD p) (aD q)
    let G:=aD g
    let A:=aD a
    let B:=aD b
    DB (b,v) (DB (a,u) (DB (g,1) (DB (q,0)
      (DB (p,0) azm)))) x =
      V A B+(u:ℚ)*V G B+(v :ℚ)*V G A -
        ((u:ℚ)*V direction B+(v :ℚ)*V direction A +
          (u:ℚ)*(v :ℚ)*(V direction G-V direction direction)) := by
  have hvols :azm=fun x=>(7/90)*ahP 0 hvol x +
      (32/90)*ahP (1/4) hvol x+(12/90)*ahP (1 / 2) hvol x +
      (32/90)*ahP (3/4) hvol x+(7/90)*ahP 1 hvol x := by
    funext x
    unfold azm ahP
    ring
  rw [hvols]
  simp only [bB8,bB9,glD]
  ring
private theorem eny (a :aU) :hvol (aD a)=(Dn a :ℚ) := by
 simp only [hvol,aD,Dn]
 push_cast
 rfl
private theorem bEe (a :aU) {F:Coordinates→ℚ} {G:aU→ℤ}
  (h : ∀ x,F (aD x)=(G x :ℚ)) (x :aU) :
  diff (aD a) F (aD x)=(gI G a x :ℚ) := by
 rw [diff,← cIb,h,h,gI,Int.cast_sub]
private theorem c4r (p q r s :aU) :
  polar (aD p) (aD q) (aD r) (aD s) =
   (wP p q r s :ℚ) :=
 bEe s (bEe r (bEe q (bEe p eny))) ⟨0,0,0⟩
end
end NU
end
section
namespace aKL
noncomputable section
open NU (LJ D0)

open vS (g9)
open B8 (lS)
open Jq (jJ dO)
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
abbrev Generator (B:lS) :=(i:Fin 5)×LJ (B i)
abbrev vJ (B:lS) :=vi (Generator B) cy
instance (B:lS) :Finite (Generator B) := by
 infer_instance
def slot (B:lS) :Generator B→Fin 5:=Sigma.fst
def DM (B:lS) :vJ B →ₐ[cy] g9 :=
 aeval fun v=>nq v.2.val 1
def x8 (B:lS) (P:c9 g9) :c9 (vJ B) :=
 ((P.comap (DM B)).homogeneousCore (dO (slot B))).toIdeal
def RM (B:lS) (P:c9 g9) (t:jJ) :=
 P.comap (mD cy (D0 B t))
theorem afL (B:lS) (P:c9 g9) :
   (x8 B P).IsHomogeneous (dO (slot B)) :=
 ((P.comap (DM B)).homogeneousCore (dO (slot B))).isHomogeneous
theorem bqJ (B:lS) {P Q:c9 g9} (h:P≤Q) :
  x8 B P≤x8 B Q :=
 Ideal.homogeneousCore_mono _ (Ideal.comap_mono h)
theorem avx {B:lS} {P:c9 g9} {a :vJ B}
   {t:jJ} (ha :a∈dO (slot B) t) :
   a∈x8 B P↔DM B a∈P:= by
 constructor
 · intro h
   exact sS (dO (slot B)) (P.comap (DM B)) h
 · intro h
   exact yl ⟨t,ha⟩ h
end
end aKL
end
section
namespace aZB
noncomputable section

open vS (g9)
open B8 (lS Exponent MH)
open Jq (jJ zY jT dO KQ)
open NU (Admissible LJ D0)
open MvPolynomial
open scoped Pointwise
open private affine_image aWH from ProximityPrize.SubmissionLower.M
attribute [local instance] MvPolynomial.weightedGradedAlgebra
abbrev Generator (B:lS) :=(i:Fin 5)×LJ (B i)
abbrev vJ (B:lS) :=vi (Generator B) cy
def slot (B:lS) :Generator B→Fin 5:=Sigma.fst
def DM (B:lS) :vJ B →ₐ[cy] g9 :=
 aeval fun v=>nq v.2.val 1
def x8 (B:lS) (P:c9 g9) :c9 (vJ B) :=
 ((P.comap (DM B)).homogeneousCore (dO (slot B))).toIdeal
theorem afL (B:lS) (P:c9 g9) :
   (x8 B P).IsHomogeneous (dO (slot B)) :=
 ((P.comap (DM B)).homogeneousCore (dO (slot B))).isHomogeneous
private theorem avx {B:lS} {P:c9 g9} {a :vJ B}
   {t:jJ} (ha :a∈dO (slot B) t) :
   a∈x8 B P↔DM B a∈P:= by
 constructor
 · intro h
   exact sS (dO (slot B)) (P.comap (DM B)) h
 · intro h
   exact yl ⟨t,ha⟩ h
abbrev RM (B:lS) (P:c9 g9) (t:jJ) :=
 P.comap (mD cy (D0 B t))
private theorem asK (B:lS) (i:Fin 5) :0∈LJ (B i) :=
 by simp [LJ,ac7.Sx]
private theorem a9G (B:lS) (t:Fin 5→ℕ) :0∈D0 B t :=
 ⟨fun _ _=>0,fun i _=>asK B i,by simp⟩
theorem bEd {B:lS} (hB:Admissible B) {t:Fin 5→ℕ}
    (ht:0<t 4) :wB (mD cy (D0 B t)) := by
  classical
  apply monomialMap_surjective
  intro v
  have hv :oq v 1∈LJ (B 4) := by
    obtain ⟨hb,hj,hf,hz⟩:=hB.2 v
    change ac7.Sx ((B 4).1.scale 2) (2*(B 4).2) _
    simp only [ac7.Sx,oZ]
    exact ⟨by omega,by omega,by omega,by omega⟩
  let j₀:Fin (t 4) :=⟨0,ht⟩
  let u (i:Fin 5) (j:Fin (t i)) :Exponent :=
    if h:i=4 then if h ▸ j=j₀ then oq v 1 else 0 else 0
  refine ⟨u,?_,?_⟩
  · intro i j
    by_cases hi:i=4
    · subst i
      by_cases hj:j=j₀
      · simpa [u,hj] using hv
      · simpa [u,hj] using asK B 4
    · simpa [u,hi] using asK B i
  · rw [t9 (4 :Fin 5)]
    · rw [t9 j₀]
      · simp [u]
      · intro j _ hj
        simp [u,hj]
      · simp
    · intro i _ hi
      simp [u,hi]
    · simp
theorem aNi (B:lS) (P:c9 g9) (t:Fin 5→ℕ) {d:ℕ}
  (hd:MH P d) :
  (lV (P.comap (mD cy (D0 B t)))).natDegree≤d:= by
 let f :=mD cy (D0 B t)
 let g:=Aa P f pL
 exact (yo g zE).trans
  (axg.beu hd)
private theorem diagonal_add (B:lS) (s t:jJ) :
    D0 B (s+t:jJ)=D0 B s+D0 B t:= by
  ext m
  constructor
  · rintro ⟨u,hu,rfl⟩
    let v (i:Fin 5) (j:Fin (s i)) :=u i (Fin.castAdd (t i) j)
    let w (i:Fin 5) (j:Fin (t i)) :=u i (Fin.natAdd (s i) j)
    refine ⟨∑ i,∑ j,v i j,⟨v,fun i j=>hu i _,rfl⟩,
      ∑ i,∑ j,w i j,⟨w,fun i j=>hu i _,rfl⟩,?_⟩
    simp only [v,w,← oY]
    exact lI rfl (fun i _=>(uh (u i)).symm)
  · rintro ⟨a,⟨v,hv,rfl⟩,b,⟨w,hw,rfl⟩,rfl⟩
    refine ⟨fun i=>pQ (v i) (w i),?_,?_⟩
    · intro i
      exact Fin.addCases (fun j=> by simpa only [Fin.append_left] using hv i j)
        (fun j=> by simpa only [zi ] using hw i j)
    · change (∑ i,∑ j,v i j)+(∑ i,∑ j,w i j) =
          ∑ i,∑ j:Fin (s i+t i),pQ (v i) (w i) j
      rw [← oY]
      refine lI rfl fun i _ => ?_
      simpa only [Fin.append_left,zi] using
        (uh (pQ (v i) (w i))).symm
private theorem diagonal_zero (B:lS) :D0 B (0:jJ)=0:= by
 ext m
 rw [wA]
 constructor
 · rintro ⟨u,_,rfl⟩
   simp
 · rintro rfl
   exact ⟨fun _ j=>j.elim0,fun _ j=>j.elim0,by simp⟩
private theorem aHz (B:lS) (t:jJ) (n:ℕ) :
   D0 B (n•t:jJ)=n•D0 B t:= by
 induction n with
 | zero=>simpa only [zero_smul] using diagonal_zero B
 | succ n ih=>simp only [succ_nsmul,diagonal_add,ih]
private theorem bqy {B:lS} (v :Generator B) :
    v.2.val∈D0 B (jT (slot B) v) := by
  classical
  let a (i:Fin 5) :Exponent:=if i=v.1 then v.2.val else 0
  refine ⟨fun i _=>a i,?_,?_⟩
  · intro i _
    by_cases h:i=v.1
    · subst i
      simpa only [a,vH rfl] using v.2.property
    · simpa only [a,p9 h] using asK B i
  · symm
    calc
      (∑ i,∑ _j:Fin (jT (slot B) v i),a i) =
          ∑ i,(jT (slot B) v i)•a i :=
        lI rfl fun i _=>t5 _ _
      _=v.2.val := by
        change (∑ i,(oq v.1 (1 :ℕ) i)•a i)= _
        refine (t9 v.1 ?_ ?_).trans ?_
        · intro i _ h
          simp [a,h]
        · simp
        · simp [a]
private theorem aX1 (B:lS) (d:Generator B →₀ ℕ) (c:cy) :
   DM B (nq d c) =
     nq (nI (fun v :Generator B=>v.2.val) d) c:= by
 rw [DM,aeval_monomial,Finsupp.prod,xW,Finsupp.sum]
 simp only [monomial_pow,one_pow,← monomial_sum_one,algebraMap_eq,C_mul_monomial,mul_one]
private theorem bxq (B:lS) (d:Generator B →₀ ℕ) :
    nI (fun v :Generator B=>v.2.val) d ∈
      D0 B (nI (jT (slot B)) d) := by
  induction d using xL with
  | zero=>simpa only [map_zero] using a9G B (0:jJ)
  | add a b ha hb=>simpa only [map_add,diagonal_add] using Set.add_mem_add ha hb
  | single v n =>
      have hmem:n•v.2.val∈n•D0 B (jT (slot B) v) := by
        induction n with
        | zero=>simp
        | succ n ih =>
            simpa only [succ_nsmul] using Set.add_mem_add ih (bqy v)
      simpa only [pC,aHz] using hmem
private theorem bxt {B:lS} {g:jJ} {m:oy}
  (hm:m∈D0 B g) :
  ∃ a :vJ B,a∈dO (slot B) g∧DM B a=nq m 1 := by
 classical
 obtain ⟨u,hu,rfl⟩:=hm
 let v (i:Fin 5) (j:Fin (g i)) :Generator B:=⟨i,⟨u i j,hu i j⟩⟩
 let d:Generator B →₀ ℕ := ∑ i,∑ j,oq (v i j) 1
 have hg:nI (jT (slot B)) d=g:= by
  simp only [d,oK,pC,sI,jT,slot,v,t5]
  ext i
  rw [zh]
  simp [zY,zR]
 refine ⟨nq d 1,zm _ _ _ hg,?_⟩
 simp only [aX1,d,oK,pC,sI,v]
private theorem bxr (B:lS) (g:jJ) :
    (dO (slot B) g).map (DM B).toLinearMap =
      pz cy (D0 B g) := by
  apply vl
  · have hpiece :dO (slot B) g =
        pz cy {d | nI (jT (slot B)) d=g} :=
      ze _ _ _
    rw [zc,hpiece,t3 ,th]
    rintro _ ⟨d,hd,rfl⟩
    change DM B (nq d 1)∈pz cy (D0 B g)
    rw [aX1,monomial_mem_restrictSupport]
    exact Or.inl ((show nI (jT (slot B)) d=g from hd) ▸
      bxq B d)
  · rw [t3 ,th]
    rintro _ ⟨m,hm,rfl⟩
    obtain ⟨a,ha,heq⟩:=bxt hm
    exact ⟨a,ha,heq⟩
theorem b0z (B:lS) (P:c9 g9) (t:jJ) (n:ℕ) :
    KQ (slot B) (x8 B P) (n•t) =
      affineHilbertFunction (RM B P t) n:= by
  let S:=D0 B t
  change uJ cy
      ((dO (slot B) (n•t)).map (u5 cy (x8 B P)).toLinearMap) =
    uJ cy
      ((qG S cy n).map
        (u5 cy (RM B P t)).toLinearMap)
  have hle :x8 B P≤P.comap (DM B) :=
    sS (dO (slot B)) _
  have hgraded:=aWH (dO (slot B) (n•t)) (x8 B P) P
    (DM B) hle (fun _ ha=>(avx ha).mpr)
  have haffine :=aWH (qG S cy n) (RM B P t) P
    (mD cy S) pL (fun _ _ h=>h)
  rw [hgraded,haffine,bxr B (n•t),affine_image S (a9G B t) n,
    aHz]
end
end aZB
end
section
namespace bAn
noncomputable section

open NU (agJ LJ)
open Finset (range sum_range_succ mem_range)
open scoped BigOperators
open NU (aOj)
open private slice cpR ayN aOY sum_pair pair aPc cbf
 from ProximityPrize.SubmissionLower.BI
private def bae (c j f :ℕ) :=
 Σ r :Fin (2*f+1),Σ y :Fin ((2*j-3*r.val)/2+1),
   Σ x :Fin (2*j-3*r.val - 2*y.val+1),
     Fin (c-(r.val+y.val + x.val)+1)
private instance (c j f :ℕ) :p7 (bae c j f) := by
 unfold bae
 infer_instance
private def a9e (a :aU×ℕ) (v :ℕ) :ℕ:=2*a.1.b - v
private def aDp (a :aU×ℕ) (v :ℕ) :ℕ:=a.1.j - 2*v
private def ur (a :aU×ℕ) (v :ℕ) :ℕ:=a.1.t - v
private theorem deq {a :aU×ℕ} (ha :agJ a) {v :ℕ} (hv :v≤2*a.2) :
  2*v≤a.1.j∧v≤a.1.t∧v≤2*a.1.b ∧
    3 * ur a v≤aDp a v∧2*aDp a v≤a9e a v := by
 have hj:=ha.1.1
 have ht:=ha.1.2
 have hz :=ha.2
 unfold a9e aDp ur
 omega
private def eqm (a :aU×ℕ) (ha :agJ a) :
  LJ a ≃ Σ v :Fin (2*a.2+1),
   bae (a9e a v.val) (aDp a v.val) (ur a v.val) where
 toFun e := by
  have h:=(aOj a e.val).mp e.property
  have hb:=h.1
  have hj:=h.2.1
  have ht:=h.2.2.1
  have hv :=h.2.2.2
  let v :Fin (2*a.2+1) :=⟨e.val 4,by omega⟩
  let r :Fin (2*ur a v.val+1) :=⟨e.val 3,by dsimp [v,ur]; omega⟩
  let y :Fin ((2*aDp a v.val-3*r.val)/2+1) :=
   ⟨e.val 2,by dsimp [v,r,aDp]; omega⟩
  let x :Fin (2*aDp a v.val-3*r.val - 2*y.val+1) :=
   ⟨e.val 1,by dsimp [v,r,y,aDp]; omega⟩
  exact ⟨v,r,y,x,⟨e.val 0,by dsimp [v,r,y,x,a9e]; omega⟩⟩
 invFun e := by
  rcases e with ⟨v,r,y,x,u⟩
  have hv :=v.isLt
  have hr :=r.isLt
  have hy :=y.isLt
  have hx :=x.isLt
  have hu:=u.isLt
  have h:=deq ha (show v.val≤2*a.2 by omega)
  have hVj:=h.1
  have hVt:=h.2.1
  have hVb:=h.2.2.1
  have ht:=h.2.2.2.1
  have hj:=h.2.2.2.2
  refine ⟨Finsupp.equivFunOnFinite.symm ![u.val,x.val,y.val,r.val,v.val],
   (aOj a _).mpr ?_⟩
  change u.val + x.val+y.val+r.val+v.val≤2*a.1.b ∧
   x.val+2*y.val+3*r.val+4*v.val≤2*a.1.j ∧
   r.val+2*v.val≤2*a.1.t∧v.val≤2*a.2
  unfold a9e aDp ur at *
  omega
 left_inv e := by
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl
 right_inv e := by
  rcases e with ⟨⟨v,hv⟩,⟨r,hr⟩,⟨y,hy⟩,⟨x,hx⟩,⟨u,hu⟩⟩
  rfl
private theorem enr (c j f :ℕ) (hj:2*j≤ c) :
   (t8 (bae c j f) :ℚ) =
     ∑ r∈range (2*f+1),slice (2*j-3*r) (c - r) := by
 classical
 change (t8 (Σ r :Fin (2*f+1),Σ y :Fin ((2*j-3*r.val)/2+1),
   Σ x :Fin (2*j-3*r.val - 2*y.val+1),
     Fin (c-(r.val+y.val + x.val)+1)) :ℚ)= _
 simp only [zg ,v9,Nat.cast_sum]
 rw [t7 (fun r => ∑ y :Fin ((2*j-3*r)/2+1),
   ∑ x :Fin (2*j-3*r - 2*y.val+1),((c-(r+y.val + x.val)+1 :ℕ) :ℚ))]
 apply lI rfl
 intro r _
 rw [← cpR _ _ (show 2*j-3*r≤ c - r by omega)]
 rw [t7 (fun y => ∑ x :Fin (2*j-3*r - 2*y+1),
   ((c-(r+y + x.val)+1 :ℕ) :ℚ))]
 apply lI rfl
 intro y _
 rw [t7 (fun x=>((c-(r+y + x)+1 :ℕ) :ℚ))]
 simp only [Nat.sub_sub,Nat.add_assoc]
private theorem bwz (c j i:ℕ) (hi:3*i≤j) (hj:2*j≤ c) :
  slice (2*j-3*(2*i)) (c - 2*i)=ayN ((c:ℚ)/2) j i:= by
 have hW:2*j-3*(2*i)=2*(j-3*i) := by omega
 have hC:2*i≤ c:= by omega
 rw [hW]
 simp only [slice,ayN,Nat.mul_div_cancel_left _ (by decide :0<2),
  Nat.mul_mod_right,zd ,u9 ]
 push_cast [oz hi,oz hC]
 ring
private theorem cpT (c j i:ℕ) (hi:3*i+3≤j) (hj:2*j≤ c) :
  slice (2*j-3*(2*i+1)) (c-(2*i+1))=aOY ((c:ℚ)/2) j i:= by
 have hW:3*(2*i+1)≤2*j:= by omega
 have hC:2*i+1≤ c:= by omega
 have hdiv : (2*j-3*(2*i+1))/2=j-(3*i+2) := by omega
 have hmod: (2*j-3*(2*i+1)) % 2=1 := by omega
 simp only [slice,aOY,hdiv,hmod]
 push_cast [oz hW,oz hC,oz (show 3*i+2≤j by omega)]
 ring
private theorem ee1 (c j f :ℕ) (ht:3*f≤j) (hj:2*j≤ c) :
   (t8 (bae c j f) :ℚ) =
     aPc ((c:ℚ)/2) j f+ayN ((c:ℚ)/2) j f := by
 rw [enr _ _ _ hj,sum_range_succ,sum_pair,bwz _ _ _ ht hj,← cbf]
 congr 1
 apply lI rfl
 intro i hi
 have hi' := mem_range.mp hi
 rw [bwz _ _ _ (by omega) hj,cpT _ _ _ (by omega) hj]
 rfl
def Oj {R:Type} [CommRing R] (q:ℚ→R) (b j f :R) :R :=
 (4*b*j^2*f - 12*b*j*f^2+12*b*f^3 - 2*j^3*f+7*j^2*f^2 - 10*j*f^3+q (9/2)*f^4) +
 (2*b*j^2+2*b*j*f-3*b*f^2 - j^3+q (3/2)*j^2*f - q (11/2)*j*f^2+q (13/2)*f^3) +
 (4*b*j - b*f - j^2+2*j*f - q (5/2)*f^2) +
 (2*b+j - q (1/2)*f)+1
private theorem d48 (b j f :ℚ) :
  aPc b j f+ayN b j f=Oj id b j f := by
 dsimp [aPc,pair,ayN,aOY,Oj]
 ring
theorem eqr (a :aU×ℕ) (ha :agJ a) :
    ((LJ a).ncard:ℚ) =
      ∑ v∈range (2*a.2+1),
        Oj id ((a.1.b:ℚ)-(v :ℚ)/2)
          ((a.1.j:ℚ) - 2*v) ((a.1.t:ℚ) - v) := by
  classical
  rw [← Nat.card_coe_set_eq,Nat.card_congr (eqm a ha),Nat.card_eq_fintype_card]
  simp only [zg ,Nat.cast_sum]
  rw [t7 (fun v =>
    (t8 (bae (a9e a v) (aDp a v) (ur a v)) :ℚ))]
  apply lI rfl
  intro v hv
  obtain ⟨hVj,hVt,hVb,ht,hj⟩:=deq ha (show v≤2*a.2 by
    have :=mem_range.mp hv
    omega)
  rw [ee1 _ _ _ ht hj,d48]
  unfold a9e aDp ur
  push_cast [oz hVb,oz hVj,oz hVt]
  congr 1
  ring
end
end bAn
end
section
namespace NU
noncomputable section
open ac7 (FH)

open vS (g9)
open B8 (lS MH Ro i9)
open agM (agj)
open scoped BigOperators Pointwise
def c1 :Prop :=
  ∀ (B:lS),Admissible B →
    ∀ (P:c9 g9) (I:lJ (Fin 5)) (i:Fin 5),
      i∉I→MH P (I.card+1) →
      ∀ (D:g9),FH (B i).1 (B i).2 D→ t6 (t4 P D) →
        RW B (i9 P D) I≤RW B P (insert i I)
def c2 :Prop :=
  ∀ (B:lS),Admissible B →
    ∀ (J:c9 g9) (I:lJ (Fin 5)),MH J I.card →
      ∀ {ι:Type} (S:lJ ι) (C:ι→ c9 g9) (w:ι→ℕ),
        Set.InjOn C (S:Set ι) →
        (∀ a∈S,∃ h:J.IsMinimalPrime (C a),(w a :ℕ∞)≤Ro J (C a) h.isPrime) →
        (∑ a∈S,(w a :ℚ)*RW B (C a) I)≤RW B J I
def c3:Prop :=
  ∀ (a :aU×ℕ),agJ a →
    ∃ H :n5 ℚ,H.natDegree≤5∧H.coeff 5=azm a ∧
      ∀ n:ℕ,H.eval (n:ℚ)=(LJ (agj a n)).ncard
end
end NU
end
section
namespace aKL
noncomputable section
open NU (LJ)
open ac7 (Sx FH)


open vS (g9)
open B8 (lS i9)
open Jq (jJ dO jT zY)
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open private bqX bLe bwV from ProximityPrize.SubmissionLower.BI
private theorem bqI {B:lS} {P Q:c9 g9} {g:vJ B}
   {e :jJ} (hg:g∈dO (slot B) e)
   (h : ∀ a :g9,a*DM B g∈P↔a∈Q) :
   (x8 B P).colon {g} = x8 B Q:= by
 ext a
 rw [xI _ _
     (bqX (slot B) (afL B P) hg),
   xI _ _ (afL B Q)]
 apply forall_congr'
 intro t
 let z :=weightedHomogeneousComponent (jT (slot B)) t a
 have hz :z∈dO (slot B) t:=weightedHomogeneousComponent_mem _ _ _
 have hg' : g.IsWeightedHomogeneous (jT (slot B)) e :=hg
 have hzg:z*g∈dO (slot B) (t+e) :=
   (weightedHomogeneousComponent_isWeightedHomogeneous t a).mul hg'
 change z∈(x8 B P).colon {g} ↔ z∈x8 B Q
 rw [Submodule.mem_colon_singleton,wR,avx hzg,
   avx hz,map_mul,h]
private theorem bT7 {a :aU×ℕ} {m:oy}
  (h:Sx a.1 a.2 m) :m∈LJ a := by
 obtain ⟨h₁,h₂,h₃,h₄⟩:=h
 change Sx (a.1.scale 2) (2*a.2) m
 simp only [Sx,oZ]
 exact ⟨by omega,by omega,by omega,by omega⟩
private theorem bT6 {a :aU×ℕ} {m n:oy}
  (hm:Sx a.1 a.2 m) (hn:Sx a.1 a.2 n) :
  m+n∈LJ a := by
 obtain ⟨hm₁,hm₂,hm₃,hm₄⟩:=hm
 obtain ⟨hn₁,hn₂,hn₃,hn₄⟩:=hn
 change Sx (a.1.scale 2) (2*a.2) (m+n)
 simp only [Sx,oZ,zf ,Nat.mul_add,oY]
 exact ⟨by omega,by omega,by omega,by omega⟩
private theorem a3P (B:lS) (i:Fin 5) (D:g9)
    (hD : ∀ m∈D.support,m∈LJ (B i)) :
    ∃ g:vJ B,g∈dO (slot B) (zY i)∧DM B g=D:= by
  classical
  let gen (m:D.support) :Generator B:=⟨i,⟨m,hD m m.property⟩⟩
  refine ⟨∑ m:D.support,C (D.coeff m)*ox (gen m),?_,?_⟩
  · apply Submodule.sum_mem
    intro m _
    have hc: (C (D.coeff m) :vJ B).IsWeightedHomogeneous (jT (slot B)) 0 :=
      isWeightedHomogeneous_C _ _
    have hx : (ox (gen m) :vJ B).IsWeightedHomogeneous
        (jT (slot B)) (zY i) :=
      isWeightedHomogeneous_X cy (jT (slot B)) (gen m)
    rw [mem_weightedHomogeneousSubmodule]
    simpa only [oD] using hc.mul hx
  · simp only [oK,map_mul,DM,aeval_C,algebraMap_eq,aeval_X,
      C_mul_monomial,mul_one,gen]
    rw [Finset.sum_coe_sort D.support (fun m=>nq m (D.coeff m))]
    exact D.support_sum_monomial_coeff
theorem b2l (B:lS) (P:c9 g9) (i:Fin 5) (D:g9)
    (hD:FH (B i).1 (B i).2 D) (hr :t6 (t4 P D)) :
    ∃ f g:vJ B,
      f∈dO (slot B) (zY i)∧g∈dO (slot B) (zY i) ∧
      (x8 B P).colon {f} = x8 B P ∧
      x8 B P ⊔ nX {f} ≤ x8 B (i9 P (D^2)) ∧
      (x8 B (i9 P (D^2))).colon {g} = x8 B (i9 P D) ∧
      x8 B (i9 P (D^2)) ⊔ nX {g} ≤ x8 B (i9 P D) := by
  classical
  have hs₂ (m:oy) (hm:m∈(D^2).support) :m∈LJ (B i) := by
    rw [pow_two] at hm
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (support_mul D D hm)
    exact bT6 (hD a ha) (hD b hb)
  obtain ⟨f,hf,hfmap⟩:=a3P B i (D^2) hs₂
  obtain ⟨g,hg,hgmap⟩:=a3P B i D (fun m hm=>bT7 (hD m hm))
  refine ⟨f,g,hf,hg,?_,?_,?_,?_⟩
  · apply bqI hf
    intro a
    rw [hfmap]
    have h:t6 (t4 P (D^2)) := by
      rw [map_pow]
      exact yU 2 hr
    exact bLe h a
  · refine sup_le (bqJ B qm) ((xu _).mpr ?_)
    rw [avx hf,hfmap]
    exact (wY:nX {D^2} ≤ i9 P (D^2))
      (qM _)
  · apply bqI hg
    intro a
    rw [hgmap]
    exact bwV hr a
  · refine sup_le (bqJ B (sup_le qm ?_))
      ((xu _).mpr ?_)
    · exact ((xu _).mpr
        (Ideal.mem_span_singleton'.mpr ⟨D,(pow_two D).symm⟩)).trans wY
    · rw [avx hg,hgmap]
      exact (wY:nX {D} ≤ i9 P D) (qM _)
end
end aKL
end
section
namespace aKL
noncomputable section
open NU (LJ D0 byT)
open ac7 (Sx)

open vS (g9)
open B8 (lS Exponent)
open Jq (jJ dO jT zY KQ)
open MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open private affine_image aWH from ProximityPrize.SubmissionLower.M
private theorem diagonal_add (B:lS) (s t:jJ) :
    D0 B (s+t:jJ)=D0 B s+D0 B t:= by
  ext m
  constructor
  · rintro ⟨u,hu,rfl⟩
    let v (i:Fin 5) (j:Fin (s i)) :=u i (Fin.castAdd (t i) j)
    let w (i:Fin 5) (j:Fin (t i)) :=u i (Fin.natAdd (s i) j)
    refine ⟨∑ i,∑ j,v i j,⟨v,fun i j=>hu i _,rfl⟩,
      ∑ i,∑ j,w i j,⟨w,fun i j=>hu i _,rfl⟩,?_⟩
    simp only [v,w,← oY]
    exact lI rfl (fun i _=>(uh (u i)).symm)
  · rintro ⟨a,⟨v,hv,rfl⟩,b,⟨w,hw,rfl⟩,rfl⟩
    refine ⟨fun i=>pQ (v i) (w i),?_,?_⟩
    · intro i
      exact Fin.addCases (fun j=> by simpa only [Fin.append_left] using hv i j)
        (fun j=> by simpa only [zi ] using hw i j)
    · change (∑ i,∑ j,v i j)+(∑ i,∑ j,w i j) =
          ∑ i,∑ j:Fin (s i+t i),pQ (v i) (w i) j
      rw [← oY]
      refine lI rfl fun i _ => ?_
      simpa only [Fin.append_left,zi] using
        (uh (pQ (v i) (w i))).symm
private theorem diagonal_zero (B:lS) :D0 B (0:jJ)=0:= by
 ext m
 rw [wA]
 constructor
 · rintro ⟨u,_,rfl⟩
   simp
 · rintro rfl
   exact ⟨fun _ j=>j.elim0,fun _ j=>j.elim0,by simp⟩
private theorem aHz (B:lS) (t:jJ) (n:ℕ) :
   D0 B (n•t:jJ)=n•D0 B t:= by
 induction n with
 | zero=>simpa only [zero_smul] using diagonal_zero B
 | succ n ih=>simp only [succ_nsmul,diagonal_add,ih]
private theorem asK (B:lS) (i:Fin 5) :0∈LJ (B i) := by
 change Sx ((B i).1.scale 2) (2*(B i).2) 0
 simp [Sx]
private theorem bqy {B:lS} (v :Generator B) :
    v.2.val∈D0 B (jT (slot B) v) := by
  classical
  let a (i:Fin 5) :Exponent:=if i=v.1 then v.2.val else 0
  refine ⟨fun i _=>a i,?_,?_⟩
  · intro i _
    by_cases h:i=v.1
    · subst i
      simpa only [a,vH rfl] using v.2.property
    · simpa only [a,p9 h] using asK B i
  · symm
    calc
      (∑ i,∑ _j:Fin (jT (slot B) v i),a i) =
          ∑ i,(jT (slot B) v i)•a i :=
        lI rfl fun i _=>t5 _ _
      _=v.2.val := by
        change (∑ i,(oq v.1 (1 :ℕ) i)•a i)= _
        refine (t9 v.1 ?_ ?_).trans ?_
        · intro i _ h
          simp [a,h]
        · simp
        · simp [a]
private theorem aX1 (B:lS) (d:Generator B →₀ ℕ) (c:cy) :
   DM B (nq d c) =
     nq (nI (fun v :Generator B=>v.2.val) d) c:= by
 rw [DM,aeval_monomial,Finsupp.prod,xW,Finsupp.sum]
 simp only [monomial_pow,one_pow,← monomial_sum_one,algebraMap_eq,C_mul_monomial,mul_one]
private theorem bxq (B:lS) (d:Generator B →₀ ℕ) :
    nI (fun v :Generator B=>v.2.val) d ∈
      D0 B (nI (jT (slot B)) d) := by
  induction d using xL with
  | zero=>simpa only [map_zero] using byT B (0:jJ)
  | add a b ha hb=>simpa only [map_add,diagonal_add] using Set.add_mem_add ha hb
  | single v n =>
      have hmem:n•v.2.val∈n•D0 B (jT (slot B) v) := by
        induction n with
        | zero=>simp
        | succ n ih =>
            simpa only [succ_nsmul] using Set.add_mem_add ih (bqy v)
      simpa only [pC,aHz] using hmem
private theorem bxt {B:lS} {g:jJ} {m:oy}
  (hm:m∈D0 B g) :
  ∃ a :vJ B,a∈dO (slot B) g∧DM B a=nq m 1 := by
 classical
 obtain ⟨u,hu,rfl⟩:=hm
 let v (i:Fin 5) (j:Fin (g i)) :Generator B:=⟨i,⟨u i j,hu i j⟩⟩
 let d:Generator B →₀ ℕ := ∑ i,∑ j,oq (v i j) 1
 have hg:nI (jT (slot B)) d=g:= by
  simp only [d,oK,pC,sI,jT,slot,v,t5]
  ext i
  rw [zh]
  simp [zY,zR]
 refine ⟨nq d 1,zm _ _ _ hg,?_⟩
 simp only [aX1,d,oK,pC,sI,v]
private theorem bxr (B:lS) (g:jJ) :
    (dO (slot B) g).map (DM B).toLinearMap =
      pz cy (D0 B g) := by
  apply vl
  · have hpiece :dO (slot B) g =
        pz cy {d | nI (jT (slot B)) d=g} :=
      ze _ _ _
    rw [zc,hpiece,t3 ,th]
    rintro _ ⟨d,hd,rfl⟩
    change DM B (nq d 1)∈pz cy (D0 B g)
    rw [aX1,monomial_mem_restrictSupport]
    exact Or.inl ((show nI (jT (slot B)) d=g from hd) ▸
      bxq B d)
  · rw [t3 ,th]
    rintro _ ⟨m,hm,rfl⟩
    obtain ⟨a,ha,heq⟩:=bxt hm
    exact ⟨a,ha,heq⟩
theorem dWE (B:lS) (P:c9 g9) (t:jJ) (n:ℕ) :
    KQ (slot B) (x8 B P) (n•t) =
      affineHilbertFunction (RM B P t) n:= by
  let S:=D0 B t
  change uJ cy
      ((dO (slot B) (n•t)).map (u5 cy (x8 B P)).toLinearMap) =
    uJ cy
      ((qG S cy n).map
        (u5 cy (RM B P t)).toLinearMap)
  have hle :x8 B P≤P.comap (DM B) :=
    sS (dO (slot B)) _
  have hgraded:=aWH (dO (slot B) (n•t)) (x8 B P) P
    (DM B) hle (fun _ ha=>(avx ha).mpr)
  have haffine :=aWH (qG S cy n) (RM B P t) P
    (mD cy S) pL (fun _ _ h=>h)
  rw [hgraded,haffine,bxr B (n•t),affine_image S (byT B t) n,
    aHz]
end
end aKL
end
section
namespace aZB
noncomputable section
open vS (g9)
open B8 (lS MH)
open Jq (jJ Form OQ KQ zJ DL a8M aJC line a5u a9f aoL bgh bn8)
open as5 (Ax ayh bO6 bCn)
open NU (RW)
open MvPolynomial
open private bLk from ProximityPrize.SubmissionLower.M
open private b26 from ProximityPrize.SubmissionLower.J
private theorem em8 (B:lS) (P:c9 g9) :
   ∃ p:Form,uz p (fun t=>KQ (slot B) (x8 B P) t) ∧
     OQ p:= by
 classical
 let σ:=Generator B
 let _:=Fintype.ofFinite σ
 let m:=b26 σ
 obtain ⟨A,hA⟩:=m.exists_finset_standardExponents_iff (x8 B P)
 have he :m.standardExponents (x8 B P)=zJ A:=Set.ext hA
 let b:=A.sup id
 have hcount (t:jJ) :KQ (slot B) (x8 B P) t =
     DL (slot B) A t:= by
   rw [a8M (slot B) m _ (afL B P),he]
   rfl
 have hle : ∀ a∈A,a≤b:= fun a ha=>Finset.le_sup (f :=id) ha
 refine ⟨∑ u∈Ax (b:=b) A,ayh (slot B) u,?_,
   bO6 _ _ (fun u _=>bCn (slot B) u)⟩
 simpa only [hcount] using (bLk (slot B) b A hle)
theorem cWq (B:lS) (P:c9 g9) (I:lJ (Fin 5))
    (hd:MH P I.card) :0≤RW B P I:= by
  classical
  obtain ⟨p,⟨N₀,hN₀⟩,hp⟩:=em8 B P
  have hline (t:jJ) (ht : ∀ j,0<t j) :
      line t p=lV (RM B P t) := by
    refine zS (N₀:=N₀) fun N hN => ?_
    rw [a5u,hN₀ _ (fun j=>hN.trans (zk N (ht j)))]
    exact congrArg (fun n:ℕ=>(n:ℚ)) (b0z B P t N)
  have hdeg:p.totalDegree≤I.card:= by
    apply a9f
    intro t ht
    rw [hline t ht]
    exact aNi B P t hd
  have hcoeff (J:lJ (Fin 5)) :
      line (aoL J) p=lV
        (RM B P (aoL J)) :=
    hline _ (fun j=> by rw [bgh]; split <;> decide)
  change 0≤(∑ J∈I.powerset,(-1 :ℚ)^(I.card-J.card) *
    (lV (RM B P (aoL J))).coeff I.card) /
    (2 :ℚ)^I.card
  simp_rw [← hcoeff]
  rw [bn8]
  exact div_nonneg (hp _ (by rwa [aJC])) (by positivity)
end
end aZB
end
section
namespace bAn
noncomputable section

open agM (agj)
open NU (hvol ic azm)
open Polynomial Finset
open scoped BigOperators
open NU (BP)
private def a1R {R:Type} [CommRing R] (q:ℚ→R) (F:ℚ→R) :R :=
 q (7/90)*F 0+q (32/90)*F (1/4)+q (12/90)*F (1/2) +
   q (32/90)*F (3/4)+q (7/90)*F 1
private def a3C {R:Type} [CommRing R] (q:ℚ→R) (F₀ F₁:ℚ→R) :R :=
 q (1/2)*(F₀ 0+F₁ 0) +
   q (41/720)*(F₁ 1-F₁ (-1)-F₀ 1+F₀ (-1)) -
   q (11/1440)*(F₁ 2 - F₁ (-2)-F₀ 2+F₀ (-2))
private def aSW (b j f v :ℚ) :ℚ :=
 Oj id (b - v/2) (j - 2*v) (f - v)
private def bw4 (b j f L:ℚ) :ℚ :=
 let F:=aSW b j f
 L*a1R id (fun r=>F (r*L))+a3C id F (fun s=>F (L+s))
private theorem gwP (b j f :ℚ) (n:ℕ) :
   (∑ v∈range (n+1),aSW b j f (v :ℚ))=bw4 b j f (n:ℚ) := by
 induction n with
 | zero =>
   rw [sum_range_one,zd]
   simp only [bw4,zero_mul,oD,a3C,id_eq]
   ring
 | succ n ih =>
   rw [sum_range_succ,ih]
   simp only [Nat.cast_succ]
   dsimp [bw4,a1R,a3C,aSW,Oj]
   ring
private def BZ (x :ℚ×ℚ×ℚ) (s :ℚ) :n5 ℚ :=
 Oj (R:=n5 ℚ) C
  (C x.1*(p6:n5 ℚ) - C (s/2))
  (C x.2.1*(p6:n5 ℚ) - C (2*s))
  (C x.2.2*(p6:n5 ℚ) - C s)
private theorem c7l (x :ℚ×ℚ×ℚ) (s :ℚ) : (BZ x s).natDegree≤4 := by
 unfold BZ Oj
 compute_degree!
private theorem bgD (x :ℚ×ℚ×ℚ) : (BZ x 0).coeff 4=hvol x/2 := by
 unfold BZ Oj hvol
 simp only [zero_div,mul_zero,map_zero,sub_zero]
 compute_degree!
 ring
private theorem bgE (x :ℚ×ℚ×ℚ) (s n:ℚ) :
  (BZ x s).eval n=aSW (x.1*n) (x.2.1*n) (x.2.2*n) s := by
 simp only [BZ,aSW,Oj,eval_add,eval_sub,eval_mul,eval_pow,
  eval_C,eval_X,eval_ofNat,eval_one,id_eq]
private theorem fUb (a :aU×ℕ) (r s n:ℚ) :
    (BZ (ic r a) s).eval n =
      aSW ((a.1.b:ℚ)*n) ((a.1.j:ℚ)*n) ((a.1.t:ℚ)*n)
        (r*(2*n*(a.2 :ℚ))+s) := by
  rw [bgE]
  unfold aSW
  congr 1 <;> simp [ic,NU.aD,NU.direction,wR] <;> ring
private def a4P (a :aU×ℕ) :n5 ℚ :=
 (p6:n5 ℚ)*(C (2*(a.2 :ℚ))*a1R C (fun r=>BZ (ic r a) 0)) +
   a3C C (BZ (ic 0 a)) (BZ (ic 1 a))
private theorem aSP {P Q:n5 ℚ} (hP:P.natDegree≤4) (hQ:Q.natDegree≤4) :
  (P+Q).natDegree≤4 := by
 simpa only [max_self] using natDegree_add_le_of_le hP hQ
private theorem bw1 {P Q:n5 ℚ} (hP:P.natDegree≤4) (hQ:Q.natDegree≤4) :
  (P-Q).natDegree≤4 := by
 simpa only [max_self] using natDegree_sub_le_of_le hP hQ
private theorem aic (x :ℚ) (P:n5 ℚ) (h:P.natDegree≤4) :
   (C x*P).natDegree≤4 :=
 (natDegree_C_mul_le x P).trans h
private theorem eoE (a :aU×ℕ) :
  (C (2*(a.2 :ℚ))*a1R C (fun r=>BZ (ic r a) 0)).natDegree≤4 := by
 unfold a1R
 apply aic
 refine aSP (aSP (aSP (aSP ?_ ?_) ?_) ?_) ?_
 all_goals exact aic _ _ (c7l _ _)
private theorem cLJ (a :aU×ℕ) :
  (a3C C (BZ (ic 0 a)) (BZ (ic 1 a))).natDegree≤4 := by
 unfold a3C
 refine bw1
  (aSP (aic _ _ (aSP ?_ ?_))
    (aic _ _ (aSP (bw1 (bw1 ?_ ?_) ?_) ?_)))
  (aic _ _ (aSP (bw1 (bw1 ?_ ?_) ?_) ?_))
 all_goals exact c7l _ _
private theorem eqt (a :aU×ℕ) : (a4P a).natDegree≤5:= by
 unfold a4P
 have h:=natDegree_mul_le_of_le (natDegree_X (R:=ℚ)).le (eoE a)
 exact (natDegree_add_le_of_le h (cLJ a)).trans (by decide)
private theorem eqq (a :aU×ℕ) : (a4P a).coeff 5=azm a := by
 unfold a4P
 have h:=coeff_eq_zero_of_natDegree_lt ((cLJ a).trans_lt (by decide :4<5))
 rw [coeff_add,h,u9,coeff_X_mul,coeff_C_mul]
 simp only [a1R,coeff_add,coeff_C_mul,bgD,azm]
 ring
private theorem eqw (a :aU×ℕ) (n:ℚ) :
  (a4P a).eval n =
    bw4 ((a.1.b:ℚ)*n) ((a.1.j:ℚ)*n) ((a.1.t:ℚ)*n) (2*n*(a.2 :ℚ)) := by
 simp only [a4P,bw4,a1R,a3C,eval_add,eval_sub,eval_mul,eval_C,
  eval_X,fUb,id_eq,zero_mul,one_mul,u9,oD]
 ring
theorem proof :NU.c3:= by
 intro a ha
 refine ⟨a4P a,eqt a,eqq a,?_⟩
 intro n
 rw [eqr (agj a n) (BP a ha n),eqw]
 simp only [agj,oZ,Nat.cast_mul]
 have h:=gwP ((a.1.b:ℚ)*n) ((a.1.j:ℚ)*n) ((a.1.t:ℚ)*n) (2*(n*a.2))
 rw [← show ((2*(n*a.2) :ℕ) :ℚ)=2*(n:ℚ)*(a.2 :ℚ) by push_cast; ring,← h]
 apply lI rfl
 intro v _
 unfold aSW
 congr 1 <;> ring
end
end bAn
end
section
namespace aKL
noncomputable section
open NU (D0 RW)

open vS (g9)
open B8 (lS MH i9 aC0)
open Jq (jJ Form KQ line a5u a9f aJC bn8 aoL bgh a4h a4I bpq auj blI blH previous ccz bKH)
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open private bxV from ProximityPrize.SubmissionLower.M
private theorem brY (B:lS) (P:c9 g9) {p:Form}
  (hp:uz p (fun t=>KQ (slot B) (x8 B P) t))
  (t:jJ) (ht : ∀ j,0<t j) :
  line t p=lV (RM B P t) := by
 obtain ⟨N₀,hN₀⟩:=hp
 refine zS (N₀:=N₀) fun N hN => ?_
 rw [a5u,hN₀ _ (fun j=>hN.trans (zk N (ht j)))]
 exact congrArg (fun n:ℕ=>(n:ℚ)) (dWE B P t N)
private theorem aNi (B:lS) (P:c9 g9) (t:jJ) {d:ℕ}
  (hd:MH P d) : (lV (RM B P t)).natDegree≤d:= by
 let f :=mD cy (D0 B t)
 let φ:=Aa P f pL
 exact (yo φ zE).trans
  (axg.beu hd)
private theorem a4y (B:lS) (P:c9 g9) {d:ℕ} (hd:MH P d)
  {p:Form} (hp:uz p (fun t=>KQ (slot B) (x8 B P) t)) :
  p.totalDegree≤d:= by
 apply a9f
 intro t ht
 rw [brY B P hp t ht]
 exact aNi B P t hd
private theorem cWp (B:lS) (P:c9 g9) (I:lJ (Fin 5)) {p:Form}
  (hp:uz p (fun t=>KQ (slot B) (x8 B P) t)) :
  RW B P I=p.coeff (uW I)/(2 :ℚ)^I.card:= by
 unfold RW
 rw [← bn8 I p]
 congr 1
 refine lI rfl fun J _ => ?_
 have ht (j:Fin 5) :0<aoL J j:= by
  rw [bgh]
  split <;> decide
 have he :=brY B P hp (aoL J) ht
 rw [he]
 rfl
theorem proof :NU.c1 := by
 intro B _ P I i hi hdim D hbox hreg
 let P₁:=i9 P D
 let P₂:=i9 P (D^2)
 obtain ⟨f,g,hf,hg,hcf,hle₁,hcg,hle₂⟩:=b2l B P i D hbox hreg
 obtain ⟨hhom₁,hex₁⟩:=a4I (slot B) (x8 B P)
  (afL B P) i f hf
 obtain ⟨hhom₂,hex₂⟩:=a4I (slot B) (x8 B P₂)
  (afL B P₂) i g hg
 rw [hcf] at hex₁
 rw [hcg] at hex₂
 obtain ⟨p,_,hp,_,_⟩:=a4h as5.proof (Generator B) (slot B)
  (x8 B P) (x8 B P)
  (afL B P) (afL B P) pL
 obtain ⟨q,p₂,hq,hp₂,hpos₂⟩:=a4h as5.proof (Generator B) (slot B)
  (x8 B P ⊔ nX {f}) (x8 B P₂) hhom₁
  (afL B P₂) hle₁
 obtain ⟨r,p₁,hr,hp₁,hpos₁⟩:=a4h as5.proof (Generator B) (slot B)
  (x8 B P₂ ⊔ nX {g}) (x8 B P₁) hhom₂
  (afL B P₁) hle₂
 have hqeq :q=auj i p:=bpq i hq hp hp hex₁
 have hreq :r=p₂ - previous i p₁:=bpq i hr hp₂ hp₁ hex₂
 have hreg₂ :t6 (t4 P (D^2)) := by
  rw [map_pow]
  exact yU 2 hreg
 have hdp:=a4y B P hdim hp
 have hdp₁:=a4y B P₁ (aC0 hreg hdim) hp₁
 have hdp₂:=a4y B P₂ (aC0 hreg₂ hdim) hp₂
 have hdq:q.totalDegree≤I.card:= by
  rw [hqeq]
  exact blI i hdp
 have hdr :r.totalDegree≤I.card:= by
  rw [hreq]
  exact (totalDegree_sub _ _).trans (max_le hdp₂ (ccz i hdp₁))
 have hdeg:=aJC I
 have hm₂:=bxV (hdq.trans_eq hdeg.symm) (hdp₂.trans_eq hdeg.symm) hpos₂
 have hm₁:=bxV (hdr.trans_eq hdeg.symm) (hdp₁.trans_eq hdeg.symm) hpos₁
 rw [hqeq,blH i hi hdp] at hm₂
 rw [hreq,coeff_sub,bKH i (uW I) (hdp₁.trans_eq hdeg.symm)] at hm₁
 have hscaled:2*p₁.coeff (uW I)≤p.coeff (uW (insert i I)) := by
  linarith only [hm₁,hm₂]
 rw [cWp B P₁ I hp₁,cWp B P (insert i I) hp]
 rw [Finset.card_insert_of_notMem hi,pow_succ]
 refine (div_le_div_iff₀ (pow_pos (by norm_num : (0:ℚ)<2) I.card)
  (mul_pos (pow_pos (by norm_num : (0:ℚ)<2) I.card) (by norm_num))).mpr ?_
 convert mul_le_mul_of_nonneg_right hscaled
  (pow_nonneg (by norm_num : (0:ℚ)≤2) I.card) using 1
 all_goals ring
end
end aKL
end
section
namespace aZB
noncomputable section

open vS (g9)
open B8 (lS MH Ro i9)

open NU (Admissible D0 RW)
open MvPolynomial
open private a3w b8a weight VB length_top from ProximityPrize.SubmissionLower.J
private theorem eqz {B:lS} (hB:Admissible B) {I:lJ (Fin 5)}
    {J Q:c9 g9} (hJ:MH J I.card) {a :g9}
    (ha : ∀ x,x*a∈J↔x∈Q) :
    RW B J I=RW B (i9 J a) I+RW B Q I:= by
  classical
  have hdiag (U:lJ (Fin 5)) :
      let f :=mD cy (D0 B (qU U))
      (lV (J.comap f)).coeff I.card =
        (lV ((i9 J a).comap f)).coeff I.card +
          (lV (Q.comap f)).coeff I.card:= by
    let t:=qU U
    have ht:0<t 4 := by
      by_cases h: (4 :Fin 5)∈U <;> simp [t,qU,h]
    let f :=mD cy (D0 B t)
    have hf :wB f :=bEd hB ht
    obtain ⟨A,hA⟩:=hf a
    change (lV (J.comap f)).coeff I.card =
      (lV ((i9 J a).comap f)).coeff I.card +
        (lV (Q.comap f)).coeff I.card
    have hsection : (i9 J a).comap f=J.comap f ⊔ nX {A} := by
      have hk :J.comap f ⊔ nX {A} =
          (J.comap f ⊔ nX {A}) ⊔ Ideal.comap f ⊥ :=
        (sup_eq_left.mpr ((Ideal.comap_mono bot_le).trans qm)).symm
      calc
        (i9 J a).comap f=((J.comap f ⊔ nX {A}).map f).comap f := by
          rw [Ideal.map_sup,Ideal.map_comap_of_surjective f hf,Ideal.map_span,
            Set.image_singleton,hA,i9]
        _=J.comap f ⊔ nX {A} :=
          (Ideal.comap_map_of_surjective f hf _).trans hk.symm
    have hAann (x :vi (D0 B t) cy) :
        x*A∈J.comap f↔x∈Q.comap f := by
      simp only [Ideal.mem_comap,map_mul,hA,ha]
    have hd:=aNi B J t hJ
    have hlow:=ML.a4G
      (J:=J.comap f) (K:=J.comap f ⊔ nX {A})
      qm (z8 (qM A)) hAann hd
    rw [hsection]
    exact vl (bzC.proof _ _ A hAann _ hd) hlow
  unfold RW
  rw [← add_div,← oY]
  congr 1
  apply lI rfl
  intro U _
  rw [hdiag U,mul_add]
private theorem bZA {B:lS} (hB:Admissible B)
    {H :c9 g9} {I:lJ (Fin 5)} (hH :MH H I.card)
    {ι:Type} (S:lJ ι) {C:ι→ c9 g9}
    (hinj:Set.InjOn C (S:Set ι)) (hp : ∀ a∈S,H.IsMinimalPrime (C a))
    (J:c9 g9) (hHJ:H≤J) :
    (∀ a (ha :a∈S),Ro J (C a) (hp a ha).isPrime ≠ ⊤) ∧
      (∑ a∈S,(weight J (C a) :ℚ)*RW B (C a) I)≤RW B J I:= by
  classical
  let D (P:c9 g9) :=RW B P I
  change _∧(∑ a∈S,(weight J (C a) :ℚ)*D (C a))≤D J
  revert hHJ
  induction J using WellFounded.induction (wellFounded_gt (α:=c9 g9)) with
  | h J ih =>
    intro hHJ
    by_cases hJ:J = ⊤
    · subst J
      have hz (a :ι) (ha :a∈S) :Ro ⊤ (C a) (hp a ha).isPrime=0 :=
        length_top _ (hp a ha).isPrime
      constructor
      · intro a ha
        simp [hz a ha]
      · have hs : (∑ a∈S,(weight ⊤ (C a) :ℚ)*D (C a))=0:= by
          apply vG
          intro a ha
          simp [VB (hp a ha).isPrime,hz a ha]
        rw [hs]
        simp [D,RW,affineHilbertPolynomial_top]
    obtain ⟨a,Q,haJ,hQ,hann⟩:=ML.bdz hJ
    let K:=i9 J a
    have hJK:J≤K:=qm
    have haK:a∈K:=z8 (qM a)
    have hlt:J<K:=lt_of_le_of_ne hJK fun he=>haJ (he ▸ haK)
    have hHQ:H≤Q:= fun x hx=>(hann x).mp (J.mul_mem_right _ (hHJ hx))
    obtain ⟨hfinK,hboundK⟩:=ih K hlt (hHJ.trans hJK)
    have hstep (i:ι) (hi:i∈S) :
        Ro J (C i) (hp i hi).isPrime =
          (if Q=C i then 1 else 0)+Ro K (C i) (hp i hi).isPrime :=
      b8a hHJ hQ hann (hp i hi)
    have hDQ:0≤D Q:=cWq B Q I (a3w hHQ hH)
    have hweight (i:ι) (hi:i∈S) :
        (weight J (C i) :ℚ)=(weight K (C i) :ℚ)+(if Q=C i then 1 else 0) := by
      rw [VB (hp i hi).isPrime,VB (J:=K) (hp i hi).isPrime,hstep i hi]
      split_ifs with hEq
      · rw [ENat.toNat_add (by simp) (hfinK i hi)]
        simp [add_comm]
      · simp
    refine ⟨fun i hi => ?_,?_⟩
    · rw [hstep i hi]
      have hfinite : (if Q=C i then 1 else 0:ℕ∞) ≠ ⊤ := by
        split_ifs <;> simp
      exact WithTop.add_ne_top.mpr ⟨hfinite,hfinK i hi⟩
    · have hindicator : (∑ i∈S,if Q=C i then D Q else 0)≤D Q:= by
        by_cases hex : ∃ i∈S,Q=C i
        · obtain ⟨i,hi,he⟩:=hex
          rw [Finset.sum_eq_single_of_mem i hi,vH he]
          intro j hj hji
          exact p9 fun hjQ=>hji (hinj hj hi (hjQ.symm.trans he))
        · rw [vG (fun i hi=>p9 (fun h=>hex ⟨i,hi,h⟩))]
          exact hDQ
      calc
        _=(∑ i∈S,(weight K (C i) :ℚ)*D (C i)) +
            (∑ i∈S,if Q=C i then D Q else 0) := by
          rw [← oY]
          apply lI rfl
          intro i hi
          rw [hweight i hi,add_mul]
          split_ifs with he
          · rw [← he,one_mul]
          · rw [zero_mul]
        _≤D K+D Q:=add_le_add hboundK hindicator
        _=D J:=(eqz hB (a3w hHJ hH) hann).symm
theorem proof :NU.c2 := by
 intro B hB J I hJ ι S C w hinj h
 have hp (a :ι) (ha :a∈S) :J.IsMinimalPrime (C a) :=Exists.choose (h a ha)
 obtain ⟨hfin,hbudget⟩:=bZA hB hJ S hinj hp J pL
 refine le_trans (qx fun a ha => ?_) hbudget
 have hlen: (w a :ℕ∞)≤Ro J (C a) (hp a ha).isPrime :=Exists.choose_spec (h a ha)
 have hw:w a≤weight J (C a) := by
  rw [VB (hp a ha).isPrime]
  exact ENat.toNat_le_toNat hlen (hfin a ha)
 exact mul_le_mul_of_nonneg_right (by exact_mod_cast hw)
  (cWq B (C a) I (a3w (hp a ha).le hJ))
end
end aZB
end
