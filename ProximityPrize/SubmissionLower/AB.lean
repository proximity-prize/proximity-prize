import ProximityPrize.SubmissionLower.L
import ProximityPrize.SubmissionLower.O
set_option Elab.async false
open _root_ renaming Finset.range→lI,MvPolynomial.C→cy,MvPolynomial.X→aU,MvPolynomial.coeff_C_mul→nI,MvPolynomial.coeff_map→ ox,MvPolynomial.eval₂Hom→ oq,MvPolynomial.mem_support_iff→lJ,Polynomial→mD,Polynomial.C→lz,Polynomial.X→lV,Polynomial.coeff_map→n5,Polynomial.constantCoeff→nq,Polynomial.mapRingHom→ oy
set_option autoImplicit true
section
namespace VJ
noncomputable section
open Polynomial
open P0 (k)
open aR (af Shape)
open scoped BigOperators
abbrev gZ:ℕ:=k - 1+P0.ajO.toNat
abbrev Wk :Shape :=⟨4012,1650,550⟩
def tB {n:ℕ} (P:af n) (D:ℕ) :Prop :=
  ∀ m∈P.support,(P.coeff m).natDegree +
    m.sum (fun i a=>(gZ - i.val)*a)≤D
end
end VJ
end
section
namespace bjW
noncomputable section
open P0 (I K)
open VJ (tB Wk)
open aR (af aO shape Contact)
def Pq (w:I→K) (T:ℕ) (P:af 4) :Prop :=
 aO (shape P) Wk∧tB P T∧Contact w P
end
end bjW
end
section
namespace bjW
noncomputable section
open Polynomial
open P0 (I K)
open VJ (tB gZ)
open aR (ao af aO shape qE Contact jet cK)
open aiI (Symbol LY)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent:=Fin 4 →₀ ℕ
private def kO (m:Exponent) :ℕ :=
 m.sum (fun i a=>(gZ - i.val)*a)
private theorem aaG {w:I→K} {T:ℕ} {P:af 4} :
    Pq w T P ↔
      (∀ m∈P.support,m.sum (fun _ a=>a)≤4012 ∧
        m.sum (fun i a=>i.val*a)≤1650∧m 3≤550 ∧
        (P.coeff m).natDegree+kO m≤T)∧Contact w P:= by
  simp only [Pq,aO,shape,qE,MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff,Finset.sup_le_iff,tB]
  constructor
  · rintro ⟨⟨hb,hj,ht⟩,hT,hc⟩
    exact ⟨fun m hm=>⟨hb m hm,hj m hm,ht m hm,hT m hm⟩,hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨⟨fun m hm=>(h m hm).1,fun m hm=>(h m hm).2.1,fun m hm=>(h m hm).2.2.1⟩,
      fun m hm=>(h m hm).2.2.2,hc⟩
private def yZ (S:ao[X]) :af 4 →ₗ[ao] ao[X] :=
 (MvPolynomial.aeval (jet S)).toLinearMap.restrictScalars ao
private theorem ajI (S:ao[X]) (P:af 4) :yZ S P=cK P S:= by
 rfl
private theorem bpc (d P:ao[X]) (c:ao) (h:d∣P) :
  d∣c•P:= by
 rw [Polynomial.smul_eq_C_mul]
 exact h.mul_left _
private def aV (w:I→K) (T:ℕ) :Submodule ao (af 4) where
  carrier := {P | Pq w T P}
  zero_mem' := by
    apply aaG.mpr
    simp [Contact,cK]
  add_mem' {P Q} hP hQ:= by
    obtain ⟨hP,hp⟩:=aaG.mp hP
    obtain ⟨hQ,hq⟩:=aaG.mp hQ
    apply aaG.mpr
    constructor
    · intro m hm
      have hor :=Finset.mem_union.mp (MvPolynomial.support_add hm)
      have Ca :
          m.sum (fun _ a=>a)≤4012∧m.sum (fun i a=>i.val*a)≤1650 ∧
            m 3≤550∧kO m≤T:= by
        rcases hor with h | h
        · obtain ⟨hb,hj,ht,hw⟩:=hP m h
          exact ⟨hb,hj,ht,by omega⟩
        · obtain ⟨hb,hj,ht,hw⟩:=hQ m h
          exact ⟨hb,hj,ht,by omega⟩
      obtain ⟨hb,hj,ht,hw⟩:=Ca
      refine ⟨hb,hj,ht,?_⟩
      have hsum: ((P+Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m)+(Q.coeff m)).natDegree≤_
        exact natDegree_add_le _ _
      have hdegree (R:af 4) (hR:m∈R.support→(R.coeff m).natDegree+kO m≤T) :
          (R.coeff m).natDegree≤T - kO m:= by
        by_cases h:m∈R.support
        · have :=hR h
          omega
        · have hz :R.coeff m=0:= by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz,natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h=>(hP m h).2.2.2)
      have hq' := hdegree Q (fun h=>(hQ m h).2.2.2)
      have :=hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← ajI,map_add,ajI,ajI]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP:= by
    obtain ⟨hP,hp⟩:=aaG.mp hP
    apply aaG.mpr
    constructor
    · intro m hm
      obtain ⟨hb,hj,ht,hw⟩:=hP m (MvPolynomial.support_smul hm)
      refine ⟨hb,hj,ht,?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h:yZ S (c•P)=c•yZ S P:=(yZ S).map_smul c P
      rw [ajI,ajI] at h
      rw [h]
      exact bpc _ _ c (hp i S hS)
private def bnp (T:ℕ) :
    af 4 →ₗ[ao] (((Fin 4→Fin 4013)×Fin (T+1))→ao) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff ao u.2.val).comp
      ((MvPolynomial.lcoeff ao[X] (Finsupp.equivFunOnFinite.symm (fun i=>(u.1 i).val))
        : af 4 →ₗ[ao[X]] ao[X]).restrictScalars ao)
private instance bqa (w:I→K) (T:ℕ) :Module.Finite ao (aV w T) := by
  classical
  let f :aV w T →ₗ[ao] (((Fin 4→Fin 4013)×Fin (T+1))→ao) :=
    (bnp T).comp (aV w T).subtype
  have hzero (Q:aV w T) (hQ:f Q=0) :Q=0:= by
    obtain ⟨P,hP⟩:= Q
    change Pq w T P at hP
    apply Subtype.ext
    change P=0
    apply MvPolynomial.ext
    intro m
    change _=0
    by_contra hnz
    have hm:=MvPolynomial.mem_support_iff.mpr hnz
    have hT: (P.coeff m).natDegree≤T:=(Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u:Fin 4→Fin 4013:= fun i=>⟨m i,Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk :k<T+1
    · have hval :=congrFun hQ (u,⟨k,hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i=>(u i).val))).coeff k=0 at hval
      have heq :Finsupp.equivFunOnFinite.symm (fun i=>(u i).val)=m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz :=f.map_sub P Q
  rw [h,sub_self] at hz
  exact hzero (P-Q) hz
private def dgt (x :ao) :af 4 →ₗ[ao] Symbol :=
  ({ LY x with
      commutes' := by
        intro a
        change MvPolynomial.map (evalRingHom x) (cy (lz a)) =
         cy a
        simp } : af 4 →ₐ[ao] Symbol).toLinearMap
private def linearFactor (x :ao) :ao[X] :=(lV:ao[X])-Polynomial.C x
private theorem br2 (x :ao) :linearFactor x≠0:=X_sub_C_ne_zero x
private theorem b7U (x :ao) : (linearFactor x).natDegree=1 :=
 natDegree_X_sub_C x
private theorem b03 (P:af 4) (x :ao) (hP:LY x P=0) :
  ∃ Q:af 4,cy (linearFactor x)*Q=P:= by
 let Q:af 4 :=AddMonoidAlgebra.ofCoeff
  (Finsupp.mapRange.linearMap (divByMonicHom (linearFactor x)) (AddMonoidAlgebra.coeff P))
 refine ⟨Q,MvPolynomial.ext _ _ fun m => ?_⟩
 have hroot : (P.coeff m).eval x=0:= by
  have h:=congrArg (fun B:Symbol=>B.coeff m) hP
  change (LY x P).coeff m=(0:Symbol).coeff m at h
  rw [LY,ox] at h
  exact h
 rw [nI]
 change (linearFactor x)*((P.coeff m) /ₘ (linearFactor x))=P.coeff m
 exact mul_divByMonic_eq_iff_isRoot.mpr hroot
private theorem crW (x :ao) (P:af 4) :
  (cy (linearFactor x)*P).support=P.support := by
 ext m
 rw [lJ,lJ,nI]
 exact mul_ne_zero_iff.trans (and_iff_right (br2 x))
end
end bjW
end
section
namespace bjW
noncomputable section
open Polynomial
open P0 (I node)

open aR (ao embed af)
open aiI (LY)
open scoped BigOperators
private theorem b2h {n:ℕ} (f :Fin n→af 4) :
   ∃ x :ao,(∀ i:I,x≠embed (node i)) ∧
     ∀ i,(LY x (f i)).support=(f i).support := by
 classical
 let nodes :Finset ao:=Finset.univ.image (fun i:I=>embed (node i))
 let roots :Finset ao:=Finset.univ.biUnion (fun i:Fin n =>
   (f i).support.biUnion (fun m=>((f i).coeff m).roots.toFinset))
 obtain ⟨x,hx⟩:=Infinite.exists_notMem_finset (nodes∪roots)
 rw [Finset.mem_union,not_or] at hx
 refine ⟨x,?_,fun i=>Finset.Subset.antisymm (MvPolynomial.support_map_subset _ _) ?_⟩
 · intro i h
   exact hx.1 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h.symm⟩)
 · intro m hm
   rw [lJ] at ⊢
   change (MvPolynomial.map (evalRingHom x) (f i)).coeff m≠0
   rw [ox]
   intro heval
   have hroot :x∈((f i).coeff m).roots :=
     (Polynomial.mem_roots (MvPolynomial.mem_support_iff.mp hm)).mpr heval
   exact hx.2 (Finset.mem_biUnion.mpr
     ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨m,hm,Multiset.mem_toFinset.mpr hroot⟩⟩)
private theorem crB (W E :ℕ) (hE :0<E) (cost:ℕ→ℕ) :
    (∑ T∈lI (W+1),cost ((W - T)/E)) ≤
      E * ∑ k∈lI (1+W/E),cost k := by
  let S:=lI (W+1)
  let R:=lI (1+W/E)
  let U:=lI E
  let pair (T:ℕ) :ℕ×ℕ:=((W - T)/E,(W - T) % E)
  have hmem : ∀ T∈S,pair T∈R ×ˢ U:= by
    intro T _
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (by
        change (W - T)/E<1+W/E
        have h: (W - T)/E≤W/E :=Nat.div_le_div_right (Nat.sub_le W T)
        omega),
      Finset.mem_range.mpr (Nat.mod_lt _ hE)⟩
  have hinj:Set.InjOn pair (↑S:Set ℕ) := by
    intro T hT V hV h
    have hT' : T<W+1 :=Finset.mem_range.mp hT
    have hV' : V<W+1 :=Finset.mem_range.mp hV
    have he :W - T=W-V:= by
      have ht:=Nat.mod_add_div (W - T) E
      have hv :=Nat.mod_add_div (W-V) E
      have hfst:=congrArg Prod.fst h
      have hsnd:=congrArg Prod.snd h
      change (W - T)/E=(W-V)/E at hfst
      change (W - T) % E=(W-V) % E at hsnd
      rw [hsnd,hfst,hv] at ht
      exact ht.symm
    omega
  calc
    _ ≤ ∑ p∈R ×ˢ U,cost p.1 := by
      refine Finset.sum_le_sum_of_injOn pair hinj ?_ (fun _ _=>le_rfl) (fun _ _ _=>Nat.zero_le _)
      intro p hp
      obtain ⟨T,hT,rfl⟩:=Finset.mem_image.mp hp
      exact hmem T hT
    _ = _:= by rw [Finset.sum_product,Finset.mul_sum]; simp [U,R]
end
end bjW
end
section
namespace dnI
noncomputable section
open Polynomial

open aR (ao af jet)
private def IM (S:ao[X]) :af 4 →+* af 4 :=
 oq cy (fun i=>aU i+MvPolynomial.C (jet S i))
private theorem dMh {R:Type*} [CommSemiring R]
    (V W:mD R) (a :ℕ) :
    ((lV*V)^a*W).coeff a=(V.coeff 0)^a*W.coeff 0:= by
  rw [mul_pow,mul_assoc]
  calc
    _=(V^a*W).coeff 0:= by
      simpa only [zero_add] using Polynomial.coeff_X_pow_mul (V^a*W) a 0
    _ = _:= by
      change nq (V^a*W) =
        nq V^a*nq W
      rw [map_mul,map_pow]
private theorem cNq {R:Type*} [CommRing R]
    (T:R →+* mD R) (T0 : ∀ G,(T G).coeff 0=G)
    (f P:R) (a :ℕ) (hf :Prime f) (hsep : ¬ f∣(T f).coeff 1)
    (hdiv :f^a∣P) (hexact : ¬ f^(a+1)∣P) : ¬ f∣(T P).coeff a := by
  obtain ⟨U,rfl⟩:=hdiv
  have hu : ¬ f∣U:= by
    rintro ⟨V,rfl⟩
    exact hexact ⟨V,by rw [pow_succ,mul_assoc]⟩
  let J:=Ideal.span ({f} : Set R)
  have :J.IsPrime :=Ideal.isPrime_span_singleton_of_prime hf
  let reduce :=Ideal.Quotient.mk J
  let tr :=(oy reduce).comp T
  have hzero (G:R) :reduce G=0↔f∣G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hcoeff (G:R) (n:ℕ) : (tr G).coeff n=reduce ((T G).coeff n) :=
    n5 _ _
  have hconstant (G:R) : (tr G).coeff 0=reduce G:= by rw [hcoeff,T0]
  obtain ⟨V,hV⟩:=Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0=0 by rw [hconstant]; exact (hzero _).mpr dvd_rfl)
  have hfirst:V.coeff 0=reduce ((T f).coeff 1) := by
    rw [← hcoeff,hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr :reduce ((T (f^a*U)).coeff a)=reduce ((T f).coeff 1)^a*reduce U:= by
    calc
      _=(tr (f^a*U)).coeff a :=(hcoeff _ _).symm
      _=(V.coeff 0)^a*(tr U).coeff 0:= by
        rw [map_mul,map_pow,hV]
        exact dMh V (tr U) a
      _ = _:= by rw [hfirst,hconstant]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hzero _).not.mpr hsep))
    ((hzero _).not.mpr hu)) (hr.symm.trans ((hzero _).mpr h))
end
end dnI
end
