import ProximityPrize.SubmissionLower.ZZZuA2c
import ProximityPrize.SubmissionLower.Zqb2cFb
import ProximityPrize.SubmissionLower.Zz5zkKe
set_option Elab.async false
set_option maxHeartbeats 12000000
open _root_ renaming Algebra.algebraMap→cy,Fin.sum_univ_eq_sum_range→ oY,Finset→aU,Finset.sum_add_distrib→ ov,Function.Injective→pz,Lagrange.nodal→n5,LinearMap.pi→nI,Nat.add_mul→ oj,Nat.add_sub_cancel→nq,Nat.add_sub_of_le→ oZ,Nat.le_of_not_ge→ oz,Nat.le_of_not_gt→ ox,Nat.lt_succ_of_le→ oD,Nat.mul_comm→lI,Nat.mul_le_mul_left→nX,Nat.mul_le_mul_right→lV,P5_7_7.nativeEval→c9,Polynomial.ext→ oq,Polynomial.natDegree_sum_le_of_forall_le→ oK,Polynomial.ofFn_coeff_eq_val_of_lt→lz,Polynomial.ofFn_coeff_eq_zero_of_ge→ oy,True.intro→lJ,mul_assoc→mD
section
set_option autoImplicit true
set_option maxRecDepth 20000
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
private abbrev kA:fO:=⟨7,by decide⟩
set_option quotPrecheck false in
local notation "kU" => receipt 2542 rfl (by decide +kernel) (by decide +kernel)
private theorem Vo:GG kA 72 3:=⟨kU,kU,kU,lJ⟩
private theorem r75:GG kA 75 3:=⟨kU,kU,kU,lJ⟩
private theorem r78:GG kA 78 3:=⟨kU,kU,kU,lJ⟩
private theorem r81 :GG kA 81 3:=⟨kU,kU,kU,lJ⟩
theorem p:GG kA 72 12 :=
 appendGrades (appendGrades (appendGrades Vo r75) r78) r81
end qyV6B3d
end
section
set_option autoImplicit true
namespace qWdRihc
noncomputable section
open Polynomial
open P5 (I K p node)
open cu (L j9)
abbrev d:ℕ:=133774
abbrev seedCap:ℕ:=4095
abbrev extra :ℕ:=256
abbrev modulus :ℕ:=0x3f800000
abbrev height:ℕ:=(p+1)*(seedCap+extra)
abbrev i5:=L[X]
abbrev nC:=i5[X]
def Bounded (f :nC) (h:ℕ) :Prop :=
 ∀ i,(f.coeff i).natDegree≤h
def specialize (z :L) :nC →+* L[X] :=
 mapRingHom (evalRingHom z)
def ek (f :nC) : (FractionRing i5)[X] :=
 f.map (cy i5 (FractionRing i5))
structure UJ where
 CF:aU K
 z :K→L
 scalar :K→K[X]
 word:I→K
 seed_injective :Set.InjOn z (CF:Set K)
 scalar_injective :Set.InjOn scalar (CF:Set K)
 degree : ∀ γ∈CF,(scalar γ).natDegree≤d
 lg : ∀ γ∈CF,∃ s :aU I,P5_7_2.A≤ s.card ∧
   ∀ j∈s,(scalar γ).eval (node j)=word j
def UJ.restrict (J:UJ) (T:aU K) (hT:T⊆J.CF) :UJ :=
  ⟨T,J.z,J.scalar,J.word,J.seed_injective.mono hT,J.scalar_injective.mono hT,
    fun γ hγ=>J.degree γ (hT hγ),fun γ hγ=>J.lg γ (hT hγ)⟩
def UJ.hit (J:UJ) (γ:K) (i:I) :Prop :=
 (J.scalar γ).eval (node i)=J.word i
instance (J:UJ) (γ:K) (i:I) :Decidable (J.hit γ i) :=
 inferInstanceAs (Decidable ((J.scalar γ).eval (node i)=J.word i))
def asT (J:UJ) (T:aU K) (B:ℕ) :Prop :=
  ∀ i:I,(T.filter (fun γ=>J.hit γ i)).card≤B ∨
    (T.filter (fun γ => ¬ J.hit γ i)).card≤B
def discriminant (a b c:nC) :nC:=b^2-4*a*c
def Zk (J:UJ) (a b c:nC) (γ:K) :Prop :=
  let S:=j9 (J.scalar γ)
  specialize (J.z γ) a*S^2+specialize (J.z γ) b*S +
    specialize (J.z γ) c=0
end
end qWdRihc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_7R
noncomputable section
open Polynomial Finset
open P5 (K)
open P5_7 (farAgreement)
open P5_7_7
open cu (L jz)
private def BA (G:Dg) (E :ℕ) (z :K) (P Q:L[X]) :L[X] :=
 ∑ i∈range (E+1),(G.coeff i).eval (C (cy K L z))*P^i*Q^(E-i)
private theorem phys_injective :pz phys :=
 IsFractionRing.injective _ _
private theorem cZl {G:Dg} {E :ℕ} (hG:G.natDegree≤E)
   (z :K) (P Q:L[X]) (hQ:Q≠0) :
   phys (BA G E z P Q)=c9 z (phys P/phys Q) (embed G)*phys Q^E := by
 have he : (embed G).natDegree<E+1 :=
   (natDegree_map_le.trans hG).trans_lt (Nat.lt_succ_self _)
 have hz (b:L[X][X]) :
     phys (b.eval (C (cy K L z)))=(b.map phys).eval (jz z) := by
   rw [eval_map]
   exact (eval₂_hom (p:=b) phys (C (cy K L z))).symm
 simp only [BA,map_sum,map_mul,map_pow,c9,coe_eval₂RingHom]
 rw [eval₂_eq_sum_range' _ he,sum_mul]
 refine sum_congr rfl fun i hi => ?_
 have hpow:phys Q^E=phys Q^i*phys Q^(E-i) := by
   rw [← pow_add,oZ (Nat.lt_succ_iff.mp (mem_range.mp hi))]
 have hqi:phys Q^i≠0:=pow_ne_zero _ (map_ne_zero_iff _ phys_injective |>.2 hQ)
 rw [hz,hpow,div_pow]
 simp only [embed,coe_mapRingHom,coeff_map,coe_evalRingHom]
 let b:=((G.coeff i).map phys).eval (jz z)
 change b*phys P^i*phys Q^(E-i) =
   b*(phys P^i/phys Q^i)*(phys Q^i*phys Q^(E-i))
 rw [mD b (_/_) _,← mD (_/_) _ _,div_mul_cancel₀ _ hqi,mD]
private theorem dLK {G:Dg} {E u s M:ℕ} (hM:0<M)
   (hG:atm G E u s M) (z :K) {P Q:L[X]}
   (hP:P.natDegree≤u+s) (hQ:Q.natDegree≤u) :
   (BA G E z P Q).natDegree<M:= by
 apply Nat.lt_of_le_pred hM
 unfold BA
 apply oK
 intro i hi
 have hi' : i≤E :=Nat.lt_succ_iff.mp (mem_range.mp hi)
 rw [eval_eq_sum_range,sum_mul,sum_mul]
 apply oK
 intro j _
 by_cases hn: (G.coeff i).coeff j=0
 · simp [hn]
 have hP' : (P^i).natDegree≤ i*(u+s) :=
   natDegree_pow_le.trans (nX _ hP)
 have hQ' : (Q^(E-i)).natDegree≤(E-i)*u :=
   natDegree_pow_le.trans (nX _ hQ)
 have hC: (((G.coeff i).coeff j)*C (cy K L z)^j).natDegree ≤
     ((G.coeff i).coeff j).natDegree := by
   rw [← map_pow]
   exact natDegree_mul_C_le _ _
 have hw:i*(u+s)+(E-i)*u=E*u+i*s := by
   rw [Nat.mul_add,add_right_comm,← oj,oZ hi']
 apply (natDegree_mul_le_of_le (natDegree_mul_le_of_le hC hP') hQ').trans
 rw [add_assoc,hw]
 simpa only [add_assoc] using Nat.le_pred_of_lt (hG i j hn)
theorem transfer {D w U S} (J:DualWord D w U S) {F H G B:Dg}
   {E M:ℕ} (hM:0<M) (a :L)
   (hrel :H*F=G+C (C (((Polynomial.X:L[X]) - C a)^M))*B)
   (hG:G.natDegree≤E) (hB:B.natDegree≤E)
   (hnarrow:atm G E J.u₀ (J.u₁-J.u₀) M)
   {γ:K} (hγ:γ∈U) (z :K) (hag:farAgreement≤(sites w S γ).card)
   (hr :atDual J F z γ=0) :c9 z (dualValue J γ) (embed G)=0:= by
 let d:=((Polynomial.X:L[X]) - C a)^M
 let ev :=(c9 z (dualValue J γ)).comp embed
 let P:=J.P γ
 let Q:=J.Q γ
 have hQ:Q≠0:=J.denominator γ hγ
 have hv :ev (C (C d))=phys d:= by
   simp [ev,embed,c9,phys]
 have hcong:=congrArg ev hrel
 rw [map_mul,map_add,map_mul,hv] at hcong
 change ev H*atDual J F z γ=ev G+phys d*ev B at hcong
 rw [hr,mul_zero] at hcong
 have hmapped:=congrArg (· * phys Q^E) hcong
 simp only [zero_mul,add_mul,mD] at hmapped
 have heq :0=BA G E z P Q+d*BA B E z P Q:= by
   apply phys_injective
   simp only [map_zero,map_add,map_mul,cZl hG z P Q hQ,
     cZl hB z P Q hQ]
   exact hmapped
 have hdvd:d∣BA G E z P Q:= by
   refine ⟨-BA B E z P Q,?_⟩
   rw [mul_neg]
   exact eq_neg_of_add_eq_zero_left heq.symm
 obtain ⟨_,hden,hnum⟩:=J.degree γ hγ
 have hs :=J.order
 have hd:=dLK hM hnarrow z (P:=P) (Q:= Q)
   (by dsimp only [P]; omega) (by dsimp only [Q]; omega)
 have hzero :BA G E z P Q=0:= by
   by_contra hn
   have hb:=natDegree_le_of_dvd hdvd hn
   have hdm:d.natDegree=M:= by
     simp only [d,(monic_X_sub_C a).natDegree_pow,natDegree_X_sub_C,mul_one]
   exact hd.not_ge (hdm ▸ hb)
 have hroot :=cZl hG z P Q hQ
 rw [hzero,map_zero] at hroot
 exact (mul_eq_zero.mp hroot.symm).resolve_right
   (pow_ne_zero _ (map_ne_zero_iff _ phys_injective |>.2 hQ))
end
end P5_7_7R
end
section
set_option autoImplicit true
namespace qZCRTge
noncomputable section
open Polynomial
open scoped Classical
open cu (L)
open P5_7_7 (Dg)
abbrev cf (F:Dg) (i j k :ℕ) :L:=((F.coeff i).coeff j).coeff k
def Boxed (F:Dg) (e h:ℕ) (cut:ℕ→ℕ) :Prop :=
 ∀ i j k,cf F i j k≠0→i≤e∧j≤h∧k<cut i
abbrev ax0 (e h:ℕ) (cut:ℕ→ℕ) :=
 (Σ i:Fin (e+1),Fin (cut i))×Fin (h+1)
def pack (e h:ℕ) (cut:ℕ→ℕ) : (ax0 e h cut→L) →ₗ[L] Dg :=
  ((ofFn (e+1)).restrictScalars L).comp (nI fun i =>
    ((ofFn (h+1)).restrictScalars L).comp (nI fun j =>
      (ofFn (cut i)).comp (nI fun k=>LinearMap.proj (⟨i,k⟩,j))))
private theorem pack_val {e h:ℕ} {cut:ℕ→ℕ} (v :ax0 e h cut→L) :
 pack e h cut v=ofFn (e+1) (fun i =>
  ofFn (h+1) (fun j=>ofFn (cut i) (fun k=>v (⟨i,k⟩,j)))) :=rfl
theorem coeff_pack {e h:ℕ} {cut:ℕ→ℕ} (v :ax0 e h cut→L)
  (k :ax0 e h cut) :cf (pack e h cut v) k.1.1 k.2 k.1.2=v k := by
 simp only [cf,pack_val]
 rw [lz _ k.1.1.isLt,
  lz _ k.2.isLt,lz _ k.1.2.isLt]
theorem boxed_pack {e h:ℕ} {cut:ℕ→ℕ} (v :ax0 e h cut→L) :
   Boxed (pack e h cut v) e h cut:= by
 intro i j k hn
 simp only [cf,pack_val] at hn
 by_cases hi:i<e+1
 · rw [lz _ hi] at hn
   by_cases hj:j<h+1
   · rw [lz _ hj] at hn
     refine ⟨by omega,by omega,?_⟩
     by_contra hk
     exact hn (oy _ (ox hk))
   · rw [oy _ (ox hj),coeff_zero] at hn
     contradiction
 · rw [oy _ (ox hi),coeff_zero,coeff_zero] at hn
   contradiction
theorem exists_pack {F:Dg} {e h:ℕ} {cut:ℕ→ℕ} (hb:Boxed F e h cut) :
   ∃ v,pack e h cut v=F:= by
 refine ⟨fun k=>cf F k.1.1 k.2 k.1.2,?_⟩
 apply oq; intro i
 apply oq; intro j
 apply oq; intro k
 by_cases hv :i≤e∧j≤h∧k<cut i
 · let w:ax0 e h cut:=(⟨⟨i,oD hv.1⟩,⟨k,hv.2.2⟩⟩,
     ⟨j,oD hv.2.1⟩)
   exact coeff_pack _ w
 · exact (not_ne_iff.mp (fun hn=>hv (boxed_pack _ _ _ _ hn))).trans
     (not_ne_iff.mp (fun hn=>hv (hb _ _ _ hn))).symm
def cF0 (i j k :ℕ) :Dg →ₗ[L] L :=
  (lcoeff L k).comp (((lcoeff (L[X]) j).restrictScalars L).comp
    ((lcoeff (L[X][X]) i).restrictScalars L))
theorem slot_rank (e h:ℕ) (cut:ℕ→ℕ) :
  Module.finrank L (ax0 e h cut→L)=(∑ i:Fin (e+1),cut i)*(h+1) := by
 simp [Module.finrank_fintype_fun_eq_card,Fintype.card_prod,Fintype.card_sigma]
end
end qZCRTge
end
section
namespace qZCRTge
open Finset
private theorem triangle (n:ℕ) : (∑ i:Fin (n+1),(i:ℕ))*2=n*(n+1) := by
 rw [oY (fun i:ℕ=>i),sum_range_id_mul_two,nq,lI n]
theorem top_count (e u s :ℕ) :
   (∑ i:Fin (e+1),(e*u+(i:ℕ)*s))=(2*u+s)*e*(e+1)/2 := by
 have hm: (∑ i:Fin (e+1),(i:ℕ))*s =
     ∑ i:Fin (e+1),((i:ℕ)*s) :=sum_mul _ _ _
 have hsum: (∑ i:Fin (e+1),(e*u+(i:ℕ)*s)) =
     e*u*(e+1)+(∑ i:Fin (e+1),(i:ℕ))*s := by
   rw [ov,← hm]
   simp only [sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]
   ac_rfl
 rw [hsum]
 have he : (2*u+s)*e*(e+1)=(e*u*(e+1)+(∑ i:Fin (e+1),(i:ℕ))*s)*2 := by
   calc
     _=e*u*(e+1)*2+(e*(e+1))*s := by ring
     _ = _:= by rw [← triangle e]; ring
 rw [he,Nat.mul_div_cancel _ (by decide :0<2)]
private theorem reflect (g:ℕ) (f :Fin (g+1)→ℕ) :
 (∑ i:Fin (g+1),f i.rev) = ∑ i:Fin (g+1),f i:=Equiv.sum_comp Fin.revPerm f
private theorem tail_sum (g j:ℕ) (hj:j≤g) :
  ∑ i:Fin (g+1),(j-(i:ℕ))=j*(j+1)/2 := by
 rw [oY (fun i=>j-i)]
 have hr :=sum_range_add_sum_Ico (fun i:ℕ=>j-i) (show j+1≤g+1 by omega)
 have hz : (∑ i∈Ico (j+1) (g+1),(j-i))=0:= by
  apply sum_eq_zero
  intro i hi
  have :=(mem_Ico.mp hi).1
  omega
 rw [hz,add_zero] at hr
 rw [← hr]
 have hh:=sum_range_reflect (fun i:ℕ=>i) (j+1)
 rw [nq] at hh
 rw [hh,sum_range_id,nq,lI j]
theorem tail_count (g j u s :ℕ) (hj:j≤g) :
   (∑ i:Fin (g+1),(j*(2*u+s)-(g*u+(i:ℕ)*s)))≤(2*u+s)*j*(j+1)/2 := by
 let d:=2*u+s
 let f (i:Fin (g+1)) :=j*d-(g*u+(i:ℕ)*s)
 let z (i:Fin (g+1)) :=j*d-(i:ℕ)*d
 have hb (i:Fin (g+1)) :f i+f i.rev≤z i+z i.rev := by
   have hi: (i:ℕ)+(i.rev :ℕ)=g:= by
     rw [Fin.val_rev]; omega
   have hm:=congrArg (fun n:ℕ=>n*u) hi
   simp only [oj] at hm
   have hsplit (n:ℕ) :n*d=n*u+n*u+n*s := by dsimp [d]; ring
   change _≤(j*d-(i:ℕ)*d)+(j*d-(i.rev :ℕ)*d)
   rw [hsplit i,hsplit i.rev]
   dsimp only [f]
   by_cases he : (i:ℕ)≤ i.rev
   · have hu:=lV u he
     have hv :=lV s he
     omega
   · have hu:=lV u (oz he)
     have hv :=lV s (oz he)
     omega
 have hs :=sum_le_sum fun i (_:i∈(univ :aU (Fin (g+1))))=>hb i
 rw [ov,ov,reflect g f,reflect g z] at hs
 have hz : (∑ i,z i)=d*j*(j+1)/2 := by
   simp only [z,← Nat.sub_mul,← sum_mul,tail_sum g j hj]
   have hd:2∣j*(j+1) :=⟨∑ i:Fin (j+1),(i:ℕ),by
     rw [← triangle j,lI]⟩
   rw [Nat.mul_assoc,Nat.mul_div_assoc _ hd,lI]
 change (∑ i,f i)≤d*j*(j+1)/2
 omega
theorem scale_surplus (a b c h:ℕ) (hh:0<h)
  (hs : (c+1)*b<c*a) :b*((c+1)*h+1)<a*(c*h+1) := by
 have h₁: ((c+1)*b)*h<(c*a)*h:=Nat.mul_lt_mul_of_pos_right hs hh
 have hab:b≤a := by
  by_contra hn
  have h₂:=nX c (oz hn:a≤b)
  rw [oj,one_mul] at hs
  omega
 calc
  b*((c+1)*h+1)=((c+1)*b)*h+b:= by ring
  _<(c*a)*h+a :=Nat.add_lt_add_of_lt_of_le h₁ hab
  _=a*(c*h+1) := by ring
end qZCRTge
end
section
set_option autoImplicit true
namespace q20JTGa
noncomputable section
open Polynomial Finset P5_7_7
open P5 (I)
open cu (L)
open scoped Classical
theorem locator_ne (s :aU I) :mL s≠0 :=
 Lagrange.nodal_ne_zero
theorem locator_degree (s :aU I) : (mL s).natDegree=s.card :=
 Lagrange.natDegree_nodal
theorem nodal_dvd {ι F:Type*} [Field F] {s :aU ι} {f :F[X]} {x :ι→F}
   (hx :pz x) (h : ∀ i∈s,f.eval (x i)=0) :
   n5 s x∣f := by
 unfold n5
 apply Finset.prod_dvd_of_coprime
 · intro i _ j _ hij
   exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx.ne hij)).isUnit
 · exact fun i hi=>dvd_iff_isRoot.mpr (h i hi)
theorem ex4 {s :aU I} {f :L[X]}
  (h : ∀ i∈s,f.eval (base i)=0) :mL s∣f :=
 nodal_dvd base_injective h
theorem nodal_eq_locator (s :aU I) :n5 s base=mL s :=rfl
end
end q20JTGa
end
