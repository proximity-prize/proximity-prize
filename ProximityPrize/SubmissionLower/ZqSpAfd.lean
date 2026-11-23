import ProximityPrize.SubmissionLower.ZkL5N7c
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qThdpma
noncomputable section
open Polynomial Finset
open cu (L)
open qNu3xvc (Equation seed amm jU)

open qdpQ3Rb (AffinePencil numerator)
open qZu9hjc (atPair)
open qrGSFbd (specializeCoeff)
open scoped Classical
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (D:AffinePencil A),
    cutJac (seed A) (amm A) (jU A false) (D.base RatFunc.X)
      A.f (numerator A D.a D.b D.c)≠0 →
    ∃ M:FibreModel RatFunc.C RatFunc.X D,M.value=D.polynomial
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] {A:Equation E} {D:AffinePencil A}
    (M:FibreModel RatFunc.C RatFunc.X D),
    ∃ (d:E[X]) (hd:d≠0) (S:FibreModel (bfj d) (localParameter d) D),
      S.value.map (qY hd)=M.value
variable {E :Type} [Field E] [Algebra L E] {d:E[X]}
private def specializeAt (z :L) (h:d.eval (algebraMap L E z)≠0) :
  Localization.Away d →+* E :=
 IsLocalization.Away.lift d (g:=eval₂RingHom (RingHom.id E) (algebraMap L E z))
  (by simpa only [coe_eval₂RingHom,eval₂_id] using h.isUnit)
private theorem specializeAt_poly (z :L) (h:d.eval (algebraMap L E z)≠0) (b:E[X]) :
  specializeAt z h (algebraMap E[X] (Localization.Away d) b)=b.eval (algebraMap L E z) := by
 simp [specializeAt]
omit [Algebra L E] in
private theorem genericCoeff_poly (hd:d≠0) (b:E[X]) :
  qY hd (algebraMap E[X] (Localization.Away d) b)=algebraMap E[X] (RatFunc E) b:= by
 simp [qY]
private theorem coeff_match (hd:d≠0) (z :L) (h:d.eval (algebraMap L E z)≠0)
   (a :Localization.Away d) :specializeAt z h a=specializeCoeff z (qY hd a) := by
 obtain ⟨n,b,hb⟩:=IsLocalization.Away.surj d a
 have hg:=congrArg (qY hd) hb
 have hs :=congrArg (specializeAt z h) hb
 simp only [map_mul,map_pow,genericCoeff_poly] at hg
 simp only [map_mul,map_pow,specializeAt_poly] at hs
 rw [← map_pow] at hg
 let t:=qY hd a
 have he :t=algebraMap E[X] (RatFunc E) b/algebraMap E[X] (RatFunc E) (d^n) :=
   (eq_div_iff (RatFunc.algebraMap_ne_zero (pow_ne_zero n hd))).mpr hg
 have hn:t.denom.eval (algebraMap L E z)≠0:= by
   have hdvd:t.denom∣d^n:= by rw [he]; exact RatFunc.denom_div_dvd b _
   intro hz
   have hzero :=eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id E) (algebraMap L E z)
     hdvd (by simpa only [eval₂_id] using hz)
   exact (pow_ne_zero n h) (by simpa only [eval₂_id,eval_pow] using hzero)
 have hcross :=congrArg (fun p:E[X]=>p.eval (algebraMap L E z))
   ((RatFunc.num_mul_eq_mul_denom_iff (pow_ne_zero n hd)).mpr he)
 simp only [eval_mul,eval_pow] at hcross
 change _=t.num.eval₂ (RingHom.id E) _/t.denom.eval₂ (RingHom.id E) _
 simp only [eval₂_id]
 rw [eq_div_iff hn]
 apply mul_right_cancel₀ (pow_ne_zero n h)
 rw [mul_right_comm,hs,hcross]
private theorem matrix_map {R S:Type} [CommRing R] [CommRing S]
  (f :R →+* S) (n:ℕ) (P Q:R[X]) (hP:P.Monic) :
  (multMatrix n P Q).map f=multMatrix n (P.map f) (Q.map f) := by
 ext i j
 simp [multMatrix,← coeff_map,map_modByMonic f hP,Polynomial.map_mul,Polynomial.map_pow]
theorem of_children (h1 :c1) (h2 :c2) :qdpQ3Rb.c2 := by
 intro E _ _ A D
 obtain ⟨M,hM⟩:=h1 A D (generic_jac D)
 obtain ⟨d,hd,S,hS⟩:=h2 M
 let zMap:=algebraMap L E
 refine ⟨d.roots.toFinset.preimage zMap zMap.injective.injOn,?_⟩
 intro z hz hzBound
 have hz' : d.eval (zMap z)≠0:= fun h =>
   hz (Finset.mem_preimage.mpr (Multiset.mem_toFinset.mpr ((mem_roots hd).mpr h)))
 let s :=specializeAt z hz'
 let P:=S.P.map s
 let Q:=S.polar.map s
 let Ω:=AlgebraicClosure E
 let k :=algebraMap E Ω
 have hdeg:P.natDegree=S.P.natDegree :=S.monic.natDegree_map s
 obtain ⟨r,hinj,hr,hpoly⟩:=companion_product P Q (S.monic.map s) S.separable.map
 let ev (i:Fin P.natDegree) : (Localization.Away d)[X] →+* Ω :=
   eval₂RingHom (k.comp s) (r i)
 let x (i:Fin P.natDegree) :=ev i S.x
 let y (i:Fin P.natDegree) :=ev i S.y
 have hCoe (i:Fin P.natDegree) : (ev i).comp Polynomial.C=k.comp s := by
   apply RingHom.ext
   intro a
   simp [ev]
 have hC (i:Fin P.natDegree) :
     (ev i).comp (Polynomial.C.comp (bfj d))=k := by
   rw [← RingHom.comp_assoc,hCoe]
   apply RingHom.ext
   intro a
   change k (specializeAt z hz' (algebraMap E[X] (Localization.Away d) (Polynomial.C a)))=k a
   rw [specializeAt_poly,eval_C]
 have hU (i:Fin P.natDegree) :ev i (Polynomial.C (localParameter d))=k (zMap z) := by
   simp [ev,localParameter,s,specializeAt_poly,zMap]
 have hE (i:Fin P.natDegree) (f :E[X][X]) :
     ev i (pairHom (Polynomial.C.comp (bfj d)) S.x S.y f) =
     atPair k (x i) (y i) f := by
   rw [pair_map,hC i]
   rfl
 have hzero (i:Fin P.natDegree) {f : (Localization.Away d)[X]} (hf :S.P∣f) :
     ev i f=0:= by
   obtain ⟨g,rfl⟩:=hf
   have h:ev i S.P=0:= by
     simpa only [P,eval₂_map,ev,coe_eval₂RingHom,k] using hr i
   rw [map_mul,h,zero_mul]
 have hpol (i:Fin P.natDegree) :
     (Q.eval₂ k (r i))=atPair k (x i) (y i) A.f.derivative := by
   rw [show Q.eval₂ k (r i)=ev i S.polar by simp [Q,ev,eval₂_map]]
   exact hE i _
 have hpol_ne (i:Fin P.natDegree) :atPair k (x i) (y i) A.f.derivative≠0:= by
   have h:=hzero i S.polar_dvd
   rw [map_sub,map_mul,map_one,hE,sub_eq_zero] at h
   exact left_ne_zero_of_mul_eq_one h
 let N :=(multMatrix P.natDegree P Q).charpoly
 have hN :N=S.value.map s := by
   unfold FibreModel.value
   rw [← Matrix.charpoly_map,matrix_map _ _ _ _ S.monic]
   exact congrArg (fun n=>(multMatrix n P Q).charpoly) hdeg
 have hproduct :N.map k = ∏ i,((Polynomial.X:Polynomial Ω) -
     C (atPair k (x i) (y i) A.f.derivative)) := by
   change N.map k = ∏ i,((Polynomial.X:Polynomial Ω) - C (Q.eval₂ k (r i))) at hpoly
   rw [hpoly]
   simp only [hpol]
 refine ⟨{ g:=D.cut z
           degree :=hzBound.1
           weight:=hzBound.2.1
           common :=hzBound.2.2
           size :=P.natDegree
           point := fun i=>(x i,y i)
           distinct := ?_
           f_zero := fun i=>(hE i A.f).symm.trans (hzero i S.f_dvd)
           g_zero := ?_
           simple := ?_
           N :=N
           monic:=Matrix.charpoly_monic _
           constant_ne := ?_
           product :=hproduct },rfl,?_⟩
 · intro i j hij
   have hx :x i=x j:=congrArg Prod.fst hij
   have hy :y i=y j:=congrArg Prod.snd hij
   have hrec (i:Fin P.natDegree) :pairHom (k.comp s) (x i) (y i) S.recover=r i:= by
     have h:=hzero i S.recover_dvd
     rw [map_sub,pair_map,hCoe,sub_eq_zero] at h
     change pairHom (k.comp s) (x i) (y i) S.recover=ev i Polynomial.X at h
     exact h.trans (by simp [ev])
   apply hinj
   rw [← hrec i,← hrec j,hx,hy]
 · intro i
   have h:=hzero i S.cut_dvd
   rw [map_sub,map_mul,hU,hE,hE,sub_eq_zero] at h
   change pairHom k (x i) (y i) (D.cut z)=0
   change pairHom k (x i) (y i) (numerator A D.a D.b D.c) =
     k (zMap z)*pairHom k (x i) (y i) A.f.derivative at h
   have hc:pairHom k (x i) (y i) (C (C (zMap z)))=k (zMap z) := by
     simp [pairHom]
   rw [ab6,map_sub,map_mul,hc,h,sub_self]
 · intro i
   have h:=hzero i S.jac_dvd
   rw [map_sub,map_mul,map_one,jac_map,hC,hU,sub_eq_zero] at h
   rw [jac_cut]
   exact left_ne_zero_of_mul_eq_one h
 · intro h
   have he :=congrArg (fun f :Polynomial Ω=>f.coeff 0) hproduct
   simp only [coeff_map,coeff_zero_prod,coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub,
     h,map_zero] at he
   exact (Finset.prod_ne_zero_iff.mpr (fun i _=>neg_ne_zero.mpr (hpol_ne i))) he.symm
 · intro i
   change N.coeff i=specializeCoeff z (D.polynomial.coeff i)
   rw [hN,coeff_map,← hM,← hS,coeff_map]
   exact coeff_match hd z hz' _
end
end qThdpma
