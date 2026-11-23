import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import ProximityPrize.SubmissionLower.AZ
set_option Elab.async false
open _root_ renaming Derivation.leibniz→LQ,Fin.prod_univ_four→JM,Finset.induction_on→Lf,Finset.mem_insert_of_mem→JQ,Finset.mem_insert_self→Kv,Finset.mem_singleton→Bf,Finset.mul_sum→xm,Finset.prod_eq_zero→G7,Finset.sum_congr→p9,Finset.sum_eq_single→zm,Finsupp.add_apply→u8,Finsupp.prod_fintype→t5,Finsupp.single→lz,Finsupp.single_eq_same→FU,Finsupp.single_zero→G3,Finsupp.tsub_apply→u5,Finsupp.weight_single→zg,KoalaBear.is_prime→pQ,LinearMap.id→G9,Matrix.cons_val_two→G5
open _root_ renaming Matrix.tail_cons→Du,MulZeroClass.mul_zero→p6,MvPolynomial→uJ,MvPolynomial.C→vi,MvPolynomial.C_mem_restrictWeightedDegree→z9,MvPolynomial.X→cy,MvPolynomial.X_mem_restrictWeightAtMost→Dv,MvPolynomial.X_mem_restrictWeightedDegree→qy,MvPolynomial.X_pow_eq_monomial→z7,MvPolynomial.bind₁→ ov,MvPolynomial.bind₁_X_right→xL,MvPolynomial.coeff_divMonomial→GB,MvPolynomial.coeff_monomial→vG,MvPolynomial.induction_on'→Cy,MvPolynomial.isHomogeneous_X→yJ,MvPolynomial.mem_support_iff→G8,MvPolynomial.monomial→nq,MvPolynomial.mul_mem_restrictWeightedDegree→vZ,MvPolynomial.pderiv→p5,MvPolynomial.restrictWeightedDegree→pG,MvPolynomial.restrictWeightedDegree_mono→t6,MvPolynomial.smul_eq_C_mul→vh
open _root_ renaming Nat.Prime→pU,Nat.add_assoc→Gk,Nat.cast_add→Aa,Nat.cast_one→ Il,Nat.cast_succ→G2,Nat.choose→Fa,Nat.choose_eq_zero_of_lt→Ef,Nat.factorial_succ→MS,Nat.lt_of_not_ge→zS,Nat.mod_eq_of_lt→G6,Nat.mul_comm→pz,Nat.sub_le→EK,Nat.zero_le→v8,Polynomial→lV,Polynomial.C→n5,Polynomial.X→nI,Polynomial.coeff_C_mul→t9,Polynomial.coeff_C_mul_X_pow→Dw,Polynomial.coeff_X_pow→Gj,Polynomial.coeff_X_pow_mul'→yl,Polynomial.coeff_X_zero→G1,Polynomial.coeff_derivative→J4,Polynomial.coeff_monomial→Gi,Polynomial.coeff_sub→yQ,Polynomial.derivative→uh,Polynomial.derivative_X→ IU,Polynomial.derivative_one→LR,Polynomial.derivative_pow_succ→MK,Polynomial.monomial→G0,Polynomial.mul_coeff_one→Kc
open _root_ renaming Submodule.add_mem→GR,Submodule.sub_mem→qM,Submodule.sum_mem→G4,add_comm→C5,add_sub_cancel_right→Gr,add_zero→vH,congrArg→ oj,ite_eq_left→qG,le_rfl→nX,map_add→mD,map_mul→lI,map_neg→ oK,map_one→ oz,map_pow→lJ,map_prod→zf,map_sub→ oq,map_sum→ oD,mul_assoc→uz,mul_ne_zero→FQ,mul_one→vj,mul_pow→vl,one_mul→ oY,pow_add→qx,pow_ne_zero→zR,pow_succ→t7,pow_zero→pL,smul_eq_mul→wY,sub_eq_add_neg→FR,sub_mul→vw,vF.Exponent→c9,vF.Ground→aU,zero_add→uW,zero_sub→Av
set_option autoImplicit true
section
namespace GN
open vF MvPolynomial
noncomputable section
abbrev Interpolant:=uJ (Fin 3) aU
def weights (j:Fin 3) :ℕ:=j.val+1
def ord (e :c9) :ℕ:=3*e 0+e 2+2*e 3
def b9 (e :c9) :Interpolant →ₐ[aU] Ground :=
 MvPolynomial.aeval fun j=>(e j.succ:aU)
abbrev Form:=uJ (Fin 4) aU
def wc:Fin 4→Form :=
  ![cy 0+MvPolynomial.X 1+MvPolynomial.X 2+MvPolynomial.X 3,
    -MvPolynomial.X 0-MvPolynomial.X 2 - cy 3,
    -MvPolynomial.X 0-MvPolynomial.X 3,-MvPolynomial.X 0]
end
end GN
end
section
namespace axE
open vF
open fP (m9)
open MvPolynomial
noncomputable section
abbrev Form:=uJ (Fin 4) aU
def raw:Fin 4→Form:=
 ![cy 0,cy 0+MvPolynomial.X 1,cy 0+MvPolynomial.X 2,cy 0+MvPolynomial.X 3]
def aqX:Fin 4→Form:=
 ![cy 3-MvPolynomial.X 0,cy 1,cy 1-MvPolynomial.X 2,cy 2 - cy 3]
def basis:Fin 4→Form:=
 ![cy 3,cy 0+MvPolynomial.X 1,cy 1-MvPolynomial.X 2,cy 2 - cy 3]
def inverse:Fin 4→Form:=
 ![cy 1-MvPolynomial.X 2 - cy 3-MvPolynomial.X 0,cy 2+MvPolynomial.X 3+MvPolynomial.X 0,cy 3+MvPolynomial.X 0,cy 0]
def adB:Form →ₐ[aU] Form:=ov inverse
def Md (m:c9):Prop:=
 m.weight m9≤49∧m 0≤14
structure Term where
 i:ℕ
 j:ℕ
 k:ℕ
 scalar:ℤ
def b9H (i j k:ℕ):Exponent:=
 Finsupp.equivFunOnFinite.symm ![49-(i+j+k),i,j,k]
@[simp] theorem gRf (i j k:ℕ) (m:Fin 4) :
   b9H i j k m = ![49-(i+j+k),i,j,k] m:=by
  simp [b9H]
local notation "G0" v:max=>(⟨0,0,0,v⟩:Term)
local notation "G1" v:max=>(⟨1,0,0,v⟩:Term)
local notation "G2" v:max=>(⟨0,1,0,v⟩:Term)
local notation "G3" v:max=>(⟨2,0,0,v⟩:Term)
local notation "G4" v:max=>(⟨0,0,1,v⟩:Term)
local notation "G5" v:max=>(⟨1,1,0,v⟩:Term)
local notation "G6" v:max=>(⟨0,2,0,v⟩:Term)
local notation "G7" v:max=>(⟨1,0,1,v⟩:Term)
local notation "G8" v:max=>(⟨0,1,1,v⟩:Term)
local notation "G9" v:max=>(⟨0,0,2,v⟩:Term)
local notation "Av" v:max=>(⟨3,0,0,v⟩:Term)
local notation "AD" v:max=>(⟨2,1,0,v⟩:Term)
local notation "AM" v:max=>(⟨1,2,0,v⟩:Term)
local notation "AP" v:max=>(⟨2,0,1,v⟩:Term)
local notation "AQ" v:max=>(⟨1,1,1,v⟩:Term)
local notation "AW" v:max=>(⟨1,0,2,v⟩:Term)
local notation "Du" v:max=>(⟨0,3,0,v⟩:Term)
local notation "Dv" v:max=>(⟨0,2,1,v⟩:Term)
local notation "Dw" v:max=>(⟨0,1,2,v⟩:Term)
local notation "FQ" v:max=>(⟨4,0,0,v⟩:Term)
local notation "FR" v:max=>(⟨3,1,0,v⟩:Term)
local notation "Gi" v:max=>(⟨2,2,0,v⟩:Term)
local notation "Gj" v:max=>(⟨3,0,1,v⟩:Term)
local notation "Gr" v:max=>(⟨2,1,1,v⟩:Term)
local notation "GB" v:max=>(⟨2,0,2,v⟩:Term)
local notation "JM" v:max=>(⟨1,3,0,v⟩:Term)
local notation "JQ" v:max=>(⟨1,2,1,v⟩:Term)
local notation "Kc" v:max=>(⟨1,1,2,v⟩:Term)
local notation "SC" v:max=>(⟨5,0,0,v⟩:Term)
local notation "SD" v:max=>(⟨4,1,0,v⟩:Term)
local notation "SM" v:max=>(⟨3,2,0,v⟩:Term)
local notation "SW" v:max=>(⟨4,0,1,v⟩:Term)
local notation "S1" v:max=>(⟨3,1,1,v⟩:Term)
local notation "S2" v:max=>(⟨3,0,2,v⟩:Term)
local notation "Vq" v:max=>(⟨2,3,0,v⟩:Term)
local notation "VC" v:max=>(⟨2,2,1,v⟩:Term)
local notation "VH" v:max=>(⟨2,1,2,v⟩:Term)
local notation "Xp" v:max=>(⟨0,4,0,v⟩:Term)
local notation "Xu" v:max=>(⟨0,0,3,v⟩:Term)
local notation "Xx" v:max=>(⟨0,3,1,v⟩:Term)
local notation "XG" v:max=>(⟨0,2,2,v⟩:Term)
local notation "Y4" v:max=>(⟨1,0,3,v⟩:Term)
end
end axE
end
section
namespace GN
open vF MvPolynomial

open scoped BigOperators
set_option maxHeartbeats 600000
noncomputable section
local instance :Fact (pU P1.p) :=⟨pQ⟩
@[simp] theorem mC (e :c9) (r :aU) :b9 e (C r)=r :=
  by simp [b9]
@[simp] theorem BD (e :c9) (j:Fin 3) :
   b9 e (cy j)=(e j.succ:aU) :=
  by simp [b9]
private def nY (Q:lV aU) (n:ℕ) :Ground :=
 (n.factorial:aU)*Q.coeff n
private theorem bqx (s u:ℕ) :
    let Q:lV Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
    (1-Polynomial.X^2)*uh Q =
      (n5 ((s :aU) - u)-Polynomial.C ((s :aU)+u)*nI)*Q:= by
  dsimp only
  have hplus : (1-Polynomial.X^2 :lV aU) *
      uh ((1+Polynomial.X)^s) =
      n5 (s :aU)*(1-Polynomial.X)*(1+Polynomial.X)^s := by
    cases s with
    | zero=>simp
    | succ s =>
      rw [MK]
      simp only [Polynomial.derivative_add,LR,IU,
        uW,vj,t7,G2]
      ring
  have hminus : (1-Polynomial.X^2 :lV aU) *
      uh ((1-Polynomial.X)^u) =
      -Polynomial.C (u:aU)*(1+Polynomial.X)*(1-Polynomial.X)^u:= by
    cases u with
    | zero=>simp
    | succ u =>
      rw [MK]
      simp only [Polynomial.derivative_sub,LR,IU,
        Av,t7,G2]
      ring
  let x :lV Ground :=nI
  change (1-x^2)*uh ((1+x)^s*(1-x)^u) =
    (n5 ((s :aU)-u)-Polynomial.C ((s :aU)+u)*x)*((1+x)^s*(1-x)^u)
  rw [Polynomial.derivative_mul]
  calc
    _=((1-x^2)*uh ((1+x)^s))*(1-x)^u +
        (1+x)^s*((1-x^2)*uh ((1-x)^u)) := by ring
    _ = _:= by dsimp only [x]; rw [hplus,hminus,oq,mD]; ring
private theorem a8i (s u n:ℕ) :
    let Q:lV Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
    nY Q (n+2)=((s :aU) - u)*nY Q (n+1) +
      ((n:aU)-((s :aU)+u))*(n+1)*nY Q n:= by
  let Q:lV Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
  change nY Q (n+2)= _
  have h:=oj (fun P:lV aU=>P.coeff (n+1)) (bqx s u)
  change ((1-Polynomial.X^2)*uh Q).coeff (n+1) =
    ((_-_ *nI)*Q).coeff (n+1) at h
  have hx (P:lV aU) :
      (nI*P).coeff (n+1)=P.coeff n :=
    Polynomial.coeff_X_mul P n
  have hx2 : (nI ^2*uh Q).coeff (n+1) =
      Q.coeff n*(n:aU) := by
    cases n with
    | zero=>simp [Polynomial.coeff_X_pow_mul']
    | succ n =>
      rw [show n+1+1=n+2 by omega,Polynomial.coeff_X_pow_mul,
        J4 ,Aa ,Il ]
  rw [vw ,vw ,yQ,yQ,oY ,
    hx2,uz ,t9,t9,hx,
    J4] at h
  simp only [Aa ,Il] at h
  simp only [nY,MS ,Nat.cast_mul,Aa ,Il]
  linear_combination (n.factorial:aU)*((n:aU)+1)*h
private theorem aP5 (s u:ℕ) :
   let Q:lV Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
   nY Q 0=1∧nY Q 1=(s :aU) - u:= by
 let Q:lV Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
 change nY Q 0=1∧nY Q 1= _
 have h:=oj (fun P:lV aU=>P.coeff 0) (bqx s u)
 change ((1-Polynomial.X^2)*uh Q).coeff 0 =
   ((_-_ *nI)*Q).coeff 0 at h
 have h0:Q.coeff 0=1 := by simp [Q,Polynomial.coeff_zero_eq_eval_zero]
 constructor
 · simpa [nY] using h0
 · rw [vw ,vw ,yQ,yQ,oY ,uz ,
     t9,t9,yl,
     Polynomial.coeff_X_mul_zero,J4 ,h0] at h
   simpa [nY] using h
private def sO (A B:Interpolant) :ℕ→ Interpolant
 | 0=>1
 | 1=>A
 | n+2=>A*sO A B (n+1) +
     C ((n:aU)+1)*(C (n:aU) - B)*sO A B n
private abbrev Bounded (d:ℕ) :=pG (R:=aU) weights d
private theorem const_mem (d:ℕ) (x :aU) :C x∈Bounded d :=
 z9 _ _ _
private theorem mul_bounded {p q:Interpolant} {d e :ℕ}
  (hp:p∈Bounded d) (hq:q∈Bounded e) :p*q∈Bounded (d+e) :=
 vZ hp hq
private theorem B0 {A B:Interpolant} (hA:A∈Bounded 1) (hB:B∈Bounded 2) :
    ∀ n,sO A B n∈Bounded n
  | 0=> by simpa [sO] using const_mem 0 1
  | 1=>hA
  | n+2=> by
    apply (Bounded (n+2)).add_mem
    · simpa only [Nat.add_comm 1 (n+1),Gk] using
        mul_bounded hA (B0 hA hB (n+1))
    · have h:=mul_bounded (mul_bounded (const_mem 0 ((n:aU)+1))
          ((Bounded 2).sub_mem (const_mem 2 n) hB)) (B0 hA hB n)
      simpa only [Nat.zero_add,Nat.add_comm 2 n] using h
private theorem y4 (A B:Interpolant) (e :c9) (s u:ℕ)
   (hA:b9 e A=(s :aU) - u) (hB:b9 e B=(s :aU)+u) :
   ∀ n,b9 e (sO A B n) =
     nY ((1+Polynomial.X)^s*(1-Polynomial.X)^u) n
 | 0=> by simpa [sO] using (aP5 s u).1.symm
 | 1=>hA.trans (aP5 s u).2.symm
 | n+2=> by
   rw [sO,mD,lI,lI,lI,oq,mC,mC,
     hA,hB,y4 A B e s u hA hB (n+1),y4 A B e s u hA hB n,
     a8i s u n]
   ring
private def B:Interpolant:=cy 0
private def C₂:Interpolant:=cy 1
private def F:Interpolant:=cy 2
private theorem lU :
  B∈Bounded 1∧C₂∈Bounded 2∧F∈Bounded 3:= by
 exact ⟨X_mem_restrictWeightedDegree weights 1 0 (by decide),
  qy  weights 2 1 (by decide),
  qy  weights 3 2 (by decide)⟩
private theorem abl (n:ℕ) {p:Interpolant} {d:ℕ} (h:p∈Bounded d) :
  (n:Interpolant)*p∈Bounded d:= by
 simpa using mul_bounded (const_mem 0 (n:aU)) h
private theorem aEi {ι:Type*} (d:ℕ) (s :Finset ι) (p:ι→ Interpolant)
   (h : ∀ i∈s,p i∈Bounded d) : ∏ i∈s,p i∈Bounded (s.card*d) := by
 classical
 induction s using Lf with
 | empty=>simpa using const_mem 0 1
 | insert i s hi ih =>
   rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul,C5]
   exact mul_bounded (h i (Kv _ _))
     (ih fun j hj=>h j (JQ hj))
end
end GN
end
section
namespace axE
open vF
open fP (lP m9 oG)
open MvPolynomial
open scoped BigOperators Pointwise
noncomputable section
theorem a1y (F:Form) :ov basis F=ov raw (ov aqX F) := by
 have h: (ov raw).comp (ov aqX)=ov basis := by
  rw [bind₁_comp_bind₁]
  congr 1
  funext j
  fin_cases j <;> simp [raw,aqX,basis,xL]
 exact (AlgHom.congr_fun h F).symm
theorem a1z (F:Form) :ov basis (adB F)=F:= by
 have h: (ov basis).comp adB=AlgHom.id aU Form:= by
  rw [adB,bind₁_comp_bind₁,← bind₁_X_left]
  congr 1
  funext j
  fin_cases j <;> simp [inverse,basis,xL]
  ring
 exact AlgHom.congr_fun h F
theorem a1D (f :Fin 4→Form) (m:c9) (z :aU) :
  ov f (nq m z)=vi z*(f 0^m 0*f 1^m 1*f 2^m 2*f 3^m 3) := by
 rw [bind₁_monomial]
 change vi z*m.prod (fun i n=>f i^n)= _
 rw [t5 _ _ (fun _=>pL _),JM]
private theorem monomial_mul (m n:c9) (x y :aU) :
  (nq m x :Form)*nq n y=nq (m+n) (x*y) :=
 monomial_mul_monomial
private theorem support_mono {m n:c9} {z :aU}
  (h:n∈(nq m z :Form).support) :n=m :=
 Finset.mem_singleton.mp (support_monomial_subset h)
private theorem dgg {F G:Form} {m:c9} (h:m∈(F+G).support) :
  m∈F.support∨m∈G.support :=
 Finset.mem_union.mp (support_add h)
private theorem dgh {F G:Form} {m:c9} (h:m∈(F*G).support) :
  ∃ x∈F.support,∃ y∈G.support,x+y=m :=
 Finset.mem_add.mp (support_mul F G h)
def Jm (m:c9) (F:Form) :Prop :=
 ∀ n∈F.support,n.degree=m.degree∧n.weight m9< m.weight m9
private theorem bBw {m:c9} {F G:Form} (hF:Jm m F) (hG:Jm m G) :
  Jm m (F+G) := by
 intro n hn
 exact (dgg hn).elim (hF n) (hG n)
private theorem bVy {m m' : c9} {F G:Form}
  (hF:Jm m F)
  (hG : ∀ n∈G.support,n.degree=m'.degree∧n.weight m9≤ m'.weight m9) :
  Jm (m+m') (F*G) := by
 intro n hn
 obtain ⟨x,hx,y,hy,rfl⟩:=dgh hn
 obtain ⟨hdx,hwx⟩:=hF x hx
 obtain ⟨hdy,hwy⟩:=hG y hy
 simp only [mD]
 exact ⟨by omega,by omega⟩
private theorem cDj (m:c9) (z :aU) :
   ∀ n∈(nq m z :Form).support,
     n.degree=m.degree∧n.weight m9≤ m.weight m9:= by
 intro n hn
 rw [support_mono hn]
 exact ⟨rfl,nX⟩
private theorem dyT {m:c9} {F:Form} (h:Jm m F) :
  ∀ n∈F.support,n.degree=m.degree∧n.weight m9≤ m.weight m9 :=
 fun n hn=>⟨(h n hn).1,(h n hn).2.le⟩
def ax1 (m:c9) (F:Form) :Prop :=
 ∃ z :aU,z≠0 ∧ ∃ G:Form,Jm m G∧F=nq m z+G
local instance :Fact (pU P1.p) :=⟨pQ⟩
private theorem dhZ (m:c9) {z :aU} (hz :z≠0) :
   ax1 m (nq m z) :=
 ⟨z,hz,0,by simp [Jm],by simp⟩
private theorem bPe {m n:c9} {F G:Form} (hF:ax1 m F) (hG:ax1 n G) :
   ax1 (m+n) (F*G) := by
 obtain ⟨x,hx,P,hP,rfl⟩:=hF
 obtain ⟨y,hy,Q,hQ,rfl⟩:=hG
 refine ⟨x*y,FQ hx hy,P*nq n y+Q*nq m x+P*Q,?_,?_⟩
 · apply bBw
   · apply bBw (bVy hP (cDj n y))
     rw [C5 m n]
     exact bVy hQ (cDj m x)
   · exact bVy hP (dyT hQ)
 · rw [← monomial_mul]
   ring
private theorem bPf (i:Fin 4) {F:Form} (hF:ax1 (lz i 1) F)
   (n:ℕ) :ax1 (lz i n) (F^n) := by
 induction n with
 | zero=>simpa using (dhZ (0:Exponent) (z :=1) one_ne_zero)
 | succ n ih =>
   rw [t7,Finsupp.single_add]
   exact bPe ih hF
private theorem cub (i j:Fin 4) (h:m9 i< m9 j) :
   ax1 (lz j 1) ((cy i:Form)-MvPolynomial.X j) := by
 refine ⟨-1,neg_ne_zero.mpr one_ne_zero,cy i,?_,?_⟩
 · intro n hn
   rw [support_X,Bf] at hn
   subst n
   simpa [zg] using h
 · have hs : (nq (lz j 1) (-1) :Form) = - cy j:= by
    rw [oK]
    rfl
   rw [hs]
   abel
theorem aTx (m:c9) :
   ax1 m (ov aqX (nq m 1)) := by
 have h0:ax1 (lz 0 1) (aqX 0) :=
   cub 3 0 (by decide)
 have h1 :ax1 (lz 1 1) (aqX 1) :=
   dhZ _ one_ne_zero
 have h2 :ax1 (lz 2 1) (aqX 2) :=
   cub 1 2 (by decide)
 have h3:ax1 (lz 3 1) (aqX 3) :=
   cub 2 3 (by decide)
 rw [a1D,oz ,oY]
 have hm:lz 0 (m 0)+Finsupp.single 1 (m 1) +
     lz 2 (m 2)+Finsupp.single 3 (m 3)=m:= by
   ext j
   fin_cases j <;> simp [Fin.reduceFinMk]
 have h:=bPe (bPe (bPe (bPf _ h0 (m 0)) (bPf _ h1 (m 1)))
   (bPf _ h2 (m 2))) (bPf _ h3 (m 3))
 rwa [hm] at h
private def axz (w a :ℕ) (F:Form) :Prop :=
 ∀ n∈F.support,w≤n.weight lP∧a≤n 3
private theorem bJB {w u a b:ℕ} {F G:Form} (hF:axz w a F)
  (hG:axz u b G) :axz (w+u) (a+b) (F*G) := by
 intro n hn
 obtain ⟨x,hx,y,hy,rfl⟩:=dgh hn
 obtain ⟨hwx,hax⟩:=hF x hx
 obtain ⟨hwy,hay⟩:=hG y hy
 simp only [mD,u8]
 omega
private theorem bJC {w a :ℕ} {F:Form} (hF:axz w a F) (n:ℕ) :
   axz (n*w) (n*a) (F^n) := by
 induction n with
 | zero=>simp [axz]
 | succ n ih =>
   rw [t7,Nat.succ_mul,Nat.succ_mul]
   exact bJB ih hF
theorem blP (m:c9) :
   ∀ n∈(ov basis (nq m 1)).support,
     m.weight m9≤n.weight lP∧m 0≤n 3:= by
 have h0:axz 3 1 (basis 0) := by
   intro n hn
   change n∈(cy 3:Form).support at hn
   rw [support_X,Bf] at hn
   subst n
   simp [zg ,lP]
 have h1 :axz 0 0 (basis 1) := by
   intro n _
   exact ⟨v8 _,v8 _⟩
 have hsub (i j:Fin 4) (w:ℕ) (hi:w≤lP i) (hj:w≤lP j) :
     axz w 0 ((cy i:Form)-MvPolynomial.X j) := by
   intro n hn
   rw [FR] at hn
   rcases dgg hn with h | h
   · rw [support_X,Bf] at h
     subst n
     exact ⟨by simpa [zg] using hi,v8 _⟩
   · rw [show -(cy j:Form)=nq (lz j 1) (-1) by
         rw [oK]; rfl] at h
     rw [support_mono h]
     exact ⟨by simpa [zg] using hj,v8 _⟩
 have h2 :axz 1 0 (basis 2) :=hsub 1 2 1 (by decide) (by decide)
 have h3:axz 2 0 (basis 3) :=hsub 2 3 2 (by decide) (by decide)
 have h:=bJB (bJB (bJB (bJC h0 (m 0))
   (bJC h1 (m 1))) (bJC h2 (m 2))) (bJC h3 (m 3))
 rw [a1D,oz ,oY ,oG]
 simpa [axz,pz ,Gk] using h
end
end axE
end
section
namespace axE
open vF
open fP (cF)
open MvPolynomial
open scoped BigOperators Pointwise
noncomputable section
private abbrev Ce :Fin 4→Form:=cy
private def axA (j:Fin 4) (F:Form) :Prop :=
 ∀ m∈F.support,m j=0
private theorem bfK {i j:Fin 4} (h:i≠j) :axA j (Ce i) := by
 intro m hm
 rw [support_X,Bf] at hm
 subst m
 simp [h]
private theorem bsX {j:Fin 4} {F G:Form} (hF:axA j F) (hG:axA j G) :
  axA j (F*G) := by
 intro n hn
 obtain ⟨x,hx,y,hy,rfl⟩:=Finset.mem_add.mp (support_mul F G hn)
 simp only [u8 ,hF x hx,hG y hy,vH]
private theorem b9M {j:Fin 4} {F:Form} (hF:axA j F) (r :ℕ) :
   axA j (F^r) := by
 induction r with
 | zero=>simp [axA]
 | succ k ih=>rw [pow_succ]; exact bsX ih hF
private theorem eEQ {j:Fin 4} {F:Form} (hF:axA j F) {m:c9}
  (hm:m j≠0) :F.coeff m=0 :=
 notMem_support_iff.mp (fun h=>hm (hF m h))
private theorem d1x (m:c9) (j:Fin 4) :
   m-Finsupp.single j (m j)=m.erase j:= by
 ext k
 by_cases h:k=j
 · subst k
   simp [u5]
 · simp [u5 ,h]
private theorem bXG (j:Fin 4) (F G:Form) (d:ℕ) (m:c9)
    (hF:axA j F) (hG:axA j G) :
    (F*(Ce j+G)^d).coeff m =
      (d.choose (m j) :aU)*(F*G^(d - m j)).coeff (m.erase j) := by
  have term (i:ℕ) :
      (F*(Ce j^i*G^(d - i)*(d.choose i:Form))).coeff m =
        if lz j i≤ m then
          (d.choose i:aU)*(F*G^(d - i)).coeff (m-Finsupp.single j i)
        else 0:= by
    rw [show F*(Ce j^i*G^(d - i)*(d.choose i:Form)) =
        vi (d.choose i:aU)*((F*G^(d - i))*Ce j^i) by
          rw [map_natCast]
          ac_rfl]
    rw [coeff_C_mul,z7,coeff_mul_monomial']
    split <;> simp
  have zero (i:ℕ) (hi:i≠m j) :
      (F*(Ce j^i*G^(d - i)*(d.choose i:Form))).coeff m=0:= by
    rw [term]
    split
    · rename_i h
      have hle :=Finsupp.single_le_iff.mp h
      have hrem: (m-Finsupp.single j i) j≠0:= by
        simp only [u5 ,FU]
        omega
      rw [eEQ (bsX hF (b9M hG _)) hrem,p6]
    · rfl
  rw [add_pow,xm,coeff_sum,zm (m j)]
  · rw [term,qG (Finsupp.single_le_iff.mpr nX),d1x]
  · exact fun i _ h=>zero i h
  · intro h
    have hd:d< m j:= by simpa using h
    rw [Ef hd]
    simp
theorem ao9 (e m:c9) (hd:e.degree=m.degree) :
    (ov raw (nq e 1)).coeff m =
      (Fa (e 1) (m 1) :aU)*(Fa (e 2) (m 2) :aU) *
        (Fa (e 3) (m 3) :aU) := by
  rw [a1D,oz ,oY]
  change (Ce 0^e 0*(Ce 0+Ce 1)^e 1*(Ce 0+Ce 2)^e 2*(Ce 0+Ce 3)^e 3).coeff m= _
  have base (j:Fin 4) (hj: (0:Fin 4)≠j) (r :ℕ) :axA j (Ce 0^r) :=
    b9M (bfK hj) r
  have plus (j k :Fin 4) (hj: (0:Fin 4)≠j) (hk :k≠j) (r :ℕ) :
      axA j ((Ce 0+Ce k)^r) := by
    apply b9M
    intro n hn
    rcases Finset.mem_union.mp (support_add hn) with h | h
    · exact bfK hj n h
    · exact bfK hk n h
  rw [C5 (Ce 0:Form) (Ce 3),bXG 3 _ _ _ _
    (bsX (bsX (base 3 (by decide) _) (plus 3 1 (by decide) (by decide) _))
      (plus 3 2 (by decide) (by decide) _)) (bfK (by decide))]
  have heq2 :Ce 0^e 0*(Ce 0+Ce 1)^e 1*(Ce 0+Ce 2)^e 2*Ce 0^(e 3 - m 3) =
      Ce 0^(e 0+(e 3 - m 3))*(Ce 0+Ce 1)^e 1*(Ce 2+Ce 0)^e 2 := by
    ring
  rw [heq2,bXG 2 _ _ _ _
    (bsX (base 2 (by decide) _) (plus 2 1 (by decide) (by decide) _))
    (bfK (by decide))]
  have heq1 (n:ℕ) :Ce 0^(e 0+(e 3 - m 3))*(Ce 0+Ce 1)^e 1*Ce 0^n =
      Ce 0^(e 0+(e 3 - m 3)+n)*(Ce 1+Ce 0)^e 1 := by
    ring
  rw [heq1,bXG 1 _ _ _ _ (base 1 (by decide) _) (bfK (by decide))]
  have h1 : (m.erase 3 |>.erase 2) 1=m 1 := by simp
  have h2 : (m.erase 3) 2=m 2 := by simp
  rw [h1,h2,← qx ,z7,vG]
  by_cases h₁:m 1≤e 1
  · by_cases h₂:m 2≤e 2
    · by_cases h₃:m 3≤e 3
      · have h0:m 0=e 0+(e 3 - m 3)+(e 2 - m 2)+(e 1 - m 1) := by
          rw [cF,cF] at hd
          omega
        have hmono:lz 0 (e 0+(e 3 - m 3)+(e 2 - m 2)+(e 1 - m 1)) =
            ((m.erase 3).erase 2).erase 1 := by
          ext j
          fin_cases j <;> simp [h0]
        rw [qG hmono]
        simp
        ac_rfl
      · simp [Ef (zS h₃)]
    · simp [Ef (zS h₂)]
  · simp [Ef (zS h₁)]
end
end axE
end
section
namespace czV
open vF GN MvPolynomial
open fP (lP)
noncomputable section
private def biP:Fin 3→Form :=
 ![cy 0+MvPolynomial.X 1,cy 2 - cy 1,cy 3-MvPolynomial.X 2]
private def a7a :Fin 3→Derivation aU Form Form :=
 ![p5 0,p5 0 - p5 1,p5 0 - p5 1 - p5 2]
private theorem cDc (j:Fin 3) :ov wc (biP j)=cy j.succ:= by
 fin_cases j <;> simp [biP,wc,xL,Fin.succ]
private theorem dWk (j:Fin 3) (i:Fin 4) :
  p5 j.succ (wc i)=ov wc (a7a j (cy i)) := by
 fin_cases j <;> fin_cases i <;>
  simp [wc,a7a,Derivation.sub_apply,pderiv_X,Fin.succ]
private theorem cKq (j:Fin 3) (Q:Form) :
   p5 j.succ (ov wc Q)=ov wc (a7a j Q) := by
 induction Q using MvPolynomial.induction_on with
 | C a=>simp [derivation_C]
 | add Q R hQ hR=>simp only [map_add,hQ,hR]
 | mul_X Q i hQ =>
   simp only [lI,LQ,wY ,mD,xL,
     ← hQ,← dWk j i]
private theorem bnm (j:Fin 4) (Q:Form) (v :c9) :
   (cy j*p5 j Q).coeff v=(v j:aU)*Q.coeff v := by
 induction Q using Cy with
 | monomial m a =>
   rw [MvPolynomial.X_mul_pderiv_monomial,coeff_smul,vG]
   split
   · rename_i h
     subst m
     rw [nsmul_eq_mul]
   · simp
 | add Q R hQ hR =>
   simp [mul_add,hQ,hR]
private theorem dmk (j:Fin 3) : (biP j).IsHomogeneous 1 := by
 fin_cases j
 · exact (yJ _ _).add (yJ _ _)
 · exact (yJ _ _).sub (yJ _ _)
 · exact (yJ _ _).sub (yJ _ _)
private theorem dmj (j:Fin 3) :
   biP j∈pG lP (weights j) := by
 have hx (i:Fin 4) (d:ℕ) (hi:lP i≤d) :
    (cy i:Form)∈pG lP d :=
   qy _ _ _ hi
 fin_cases j
 · exact GR _ (hx 0 1 (by decide)) (hx 1 1 (by decide))
 · exact qM _ (hx 2 2 (by decide)) (hx 1 2 (by decide))
 · exact qM _ (hx 3 3 (by decide)) (hx 2 3 (by decide))
private theorem c5Q (j:Fin 3) {d:ℕ} {Q:Form}
   (hQ:Q∈pG lP d) :
   a7a j Q∈pG lP d:= by
 have hd (i:Fin 4) :p5 i Q∈pG lP d :=
   t6 _ (EK _ _) (pderiv_mem_restrictWeightedDegree i hQ)
 fin_cases j
 · exact hd 0
 · exact qM _ (hd 0) (hd 1)
 · exact qM _ (qM _ (hd 0) (hd 1)) (hd 2)
end
end czV
end
section
namespace dnQ
open vF GN MvPolynomial
open axE (inverse adB Md)
open scoped BigOperators
noncomputable section
local instance :Fact (pU P1.p) :=⟨pQ⟩
local instance (m:c9) :Decidable (Md m) := by
 unfold Md
 infer_instance
private def sign (i:Fin 4) :Ground :=if i=1 then 1 else -1
private def flip (i:Fin 4) :Form:=sign i•cy i
private def scale (m:c9) :Ground := ∏ i∈m.support,sign i^m i
private theorem bg1 (m:c9) :scale m≠0:= by
 apply Finset.prod_ne_zero_iff.mpr
 intro i _
 apply zR
 unfold sign
 split <;> simp
private theorem bqi (m:c9) (a :aU) :
  ov flip (nq m a)=nq m (scale m*a) := by
 rw [bind₁_monomial,monomial_eq,Finsupp.prod]
 simp only [flip,vh,vl,Finset.prod_mul_distrib,← lJ,← zf ,
  scale,lI]
 ac_rfl
private theorem b3E (P:Form) (m:c9) :
   (ov flip P).coeff m=scale m*P.coeff m:= by
 classical
 conv_lhs=>rw [P.as_sum]
 rw [oD,coeff_sum]
 conv_rhs=>rw [P.as_sum,coeff_sum,xm]
 apply p9 rfl
 intro s _
 by_cases h:s=m
 · subst s
   simp [bqi,vG]
 · simp [h,bqi,vG]
private theorem aNF (Q:Form) (m:c9) :
   (adB Q).coeff m=scale m*(ov wc Q).coeff m:= by
 have h: (fun i=>ov flip (wc i))=inverse := by
   funext i
   fin_cases i <;>
     simp [wc,flip,sign,inverse,xL] <;> ring
 rw [← b3E,bind₁_bind₁,h]
 rfl
end
end dnQ
end
