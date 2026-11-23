import ProximityPrize.SubmissionLower.ZFO2WXb
import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZGCzLxb
import ProximityPrize.SubmissionLower.Za7Od9d
import ProximityPrize.SubmissionLower.ZzCHpGc
import ProximityPrize.SubmissionLower.ZTV7u3a
set_option Elab.async false
open _root_ renaming Finset.sum_range_succ → zpB, Function.Injective → zq4, Function.Surjective → zpX, Ideal.Quotient.mk → zVv, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, LinearMap.finrank_le_finrank_of_surjective → zs6, Module.Finite → zAa, Module.finrank → zsE, Module.finrank_fintype_fun_eq_card → zvt, MvPolynomial.X → z9v, Nat.mul_le_mul_left → zBI, Polynomial → zM1, Polynomial.X → z7y, Polynomial.aeval → zEU
section
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def d0_0:=s! 2390 495 495 38 8 0x5ce102aa2de45eb2c00863f0cb0020f99b2c00720dccb00142d4b2c0024420983f0172c39240
private def d0_1 :=s! 2390 495 2543 36 4 0x41a679517edb076069a485433e67e068f3
private def r0:=j! 2390 495 0xc9c0aca5e2 [d0_0,d0_1]
private def d1_0:=s! 2412 504 504 38 8 0x629db8ed19fa8cdfb008b3697ec022007dfb00750557ec014902dfb0024a98c4ff8176794440
private def d1_1 :=s! 2412 504 2552 36 4 0xc4922331f16302c0784591ab6fa9127239
private def r1 :=j! 2412 504 0xd2bbd82c66 [d1_0,d1_1]
private def d2_0:=s! 2622 547 547 38 8 0x9674686402b5eec1900b362f86402a0a9019008bd188640179719141f2882832900199e28a40
private def d2_1 :=s! 2622 547 2595 37 5 0xc3b3ea2109bfa6b020c1c5fb9e2be1c618dbfe0f18b0
private def r2 :=j! 2622 547 0x125d29c39fe [d2_0,d2_1]
private def d3_0:=s! 2806 583 583 38 8 0xc84fe82803669ce0a00d8be882803165760a00a02d282801a2935f59a2be17ec9001b8e97240
private def d3_1 :=s! 2806 583 2631 38 6 0xd782ae01a73310e01eaf5a038116078a9be74c9bc0282932ccc103
private def r3:=j! 2806 583 0x18014c553f3 [d3_0,d3_1]
private def d4_0:=s! 2893 602 602 38 8 0xe1dfe31803c0e9ac600ebbcf31803519dec600aa3a031801b5e37af4b2d79893d001c7950f40
private def d4_1 :=s! 2893 602 2650 38 6 0x10b970b503bd37f4802ef1c62391701c137f78fa5c520cb02b5c0c97
private def r4 :=j! 2893 602 0x1b2757cb8c3 [d4_0,d4_1]
private def d5_0:=s! 3014 630 630 39 8 0x83c4e5fb01115beff6020eec27ec03a760dfd805c412dfb007415f22f4c5f621512001dbfc6240
private def d5_1 :=s! 3014 630 2678 38 7 0x372efc707110369008458eba404bbbbf8f26036d8f3e6b99258940fa7fe9fd80
private def r5:=j! 3014 630 0x20192e0024c [d5_0,d5_1]
def dataF:Array aqm := #[
 r0,r1,r2,r3,r4,r5
]
end qpECY2d
end
end
section
section
set_option autoImplicit true
namespace qLUrYJc
open P5 (K)
open cu (L)
open qe6nVeb (SeedPlane)
open q7YMR4d (SmoothAt)
open MvPolynomial Finset
private theorem twice_finrank (d:ℕ) :
  2*zsE L (restrictTotalDegree (Fin 2) L d)=(d+1)*(d+2) := by
 rw [restrictTotalDegree,Module.finrank_eq_nat_card_basis (basisRestrictSupport L _),
  Nat.card_coe_set_eq]
 change 2 * {e :Fin 2 →₀ ℕ | e.degree≤d}.ncard= _
 rw [Finsupp.ncard_setOf_degree_le,Nat.card_fin]
 simpa only [Nat.descFactorial_succ _ 1,Nat.descFactorial_one,Nat.factorial_two,
  show d+2-1=d+1 by omega] using (Nat.descFactorial_eq_factorial_mul_choose (d+2) 2).symm
private theorem select_marks (z :K→Fin 2→L) (T:Finset K) (d:ℕ)
    (hT : ∀ q:SeedPlane,q.totalDegree≤d→(∀ γ∈T,eval (z γ) q=0)→q=0) :
    ∃ S:Finset K,S⊆T∧(d+1)*(d+2)≤2*S.card ∧
      ∀ i:S,∃ p:SeedPlane,p.totalDegree≤d∧eval (z i) p≠0 ∧
        ∀ j:S,j≠i→eval (z j) p=0:= by
  classical
  let good (S:Finset K) := ∀ p:SeedPlane,p.totalDegree≤d →
    (∀ γ∈S,eval (z γ) p=0)→p=0
  have hex : ∃ n:ℕ,∃ S:Finset K,S⊆T∧good S∧S.card=n :=
    ⟨T.card,T,Subset.rfl,hT,rfl⟩
  obtain ⟨S,hST,hs,hcard⟩:=Nat.find_spec hex
  let V:=restrictTotalDegree (Fin 2) L d
  let E :V →ₗ[L] (S→L) :=
    LinearMap.pi fun i=>(aeval (z i)).toLinearMap.comp V.subtype
  have hE :zq4 E :=(injective_iff_map_eq_zero E).mpr fun p hp=> by
    apply Subtype.ext
    exact hs p ((mem_restrictTotalDegree _ _ _).mp p.prop)
      (fun i hi=>congrFun hp ⟨i,hi⟩)
  have hr :=LinearMap.finrank_le_finrank_of_injective hE
  rw [zvt,Fintype.card_coe] at hr
  refine ⟨S,hST,(twice_finrank d).symm.trans_le (zBI 2 hr),?_⟩
  intro i
  have hn : ¬ good (S.erase i) := fun hg =>
    Nat.find_min hex (hcard ▸ card_erase_lt_of_mem i.prop)
      ⟨S.erase i,(erase_subset _ _).trans hST,hg,rfl⟩
  change ¬ (∀ p:SeedPlane,p.totalDegree≤d →
    (∀ γ∈S.erase i,eval (z γ) p=0)→p=0) at hn
  push Not at hn
  obtain ⟨p,hd,hp,hne⟩:=hn
  refine ⟨p,hd,fun hi=>hne (hs p hd ?_),fun j hj=>hp j ?_⟩
  · intro j hj
    by_cases hji:j=(i:K)
    · simpa only [hji] using hi
    · exact hp j (mem_erase.mpr ⟨hji,hj⟩)
  · exact mem_erase.mpr ⟨fun he=>hj (Subtype.ext he),j.prop⟩
theorem proof :q7YMR4d.c2 := by
 classical
 intro z T d _ hT
 obtain ⟨S,hST,hcard,hp⟩:=select_marks z T d hT
 choose p hd hn hv using hp
 let line (i:S) :SeedPlane :=z9v 0 - C (z i 0)
 let f (i:S) :=p i*line i
 have hf (i j:S) :eval (z i) (f j)=0:= by
   change eval (z i) (p j*line j)=0
   rw [map_mul]
   by_cases h:i=j
   · subst j
     simp [line,eval_X,eval_C]
   · rw [hv j i h,zero_mul]
 have hdf (i:S) : (f i).totalDegree≤d+1 :=
   (totalDegree_mul _ _).trans (Nat.add_le_add (hd i)
     ((totalDegree_sub_C_le _ _).trans_eq (totalDegree_X 0)))
 have hg (i:S) :eval (z i) (pderiv 0 (f i))≠0:= by
   simpa [f,line,pderiv_mul,pderiv_C,eval_X,eval_C] using hn i
 let G (i:S) :MvPolynomial S L :=
   ∑ j:S,z9v j*C (eval (z i) (pderiv 0 (f j)))
 have hG (i:S) :G i≠0:= by
   intro h
   have he :=congrArg (eval (fun j:S=>if j=i then (1 :L) else 0)) h
   exact hg i (by simpa [G,map_sum,eval_X,eval_C,ite_mul] using he)
 obtain ⟨a,ha⟩ : ∃ a :S→L,eval a (∏ i:S,G i)≠0:= by
   by_contra! h
   exact (Finset.prod_ne_zero_iff.mpr fun i _=>hG i)
     (MvPolynomial.funext fun a=>(h a).trans (map_zero (eval a)).symm)
 have ha' (i:S) :eval a (G i)≠0:= by
   rw [map_prod] at ha
   exact fun h=>ha (Finset.prod_eq_zero (mem_univ i) h)
 let q:SeedPlane := ∑ j:S,C (a j)*f j
 have hq (i:S) :SmoothAt q (z i) := by
   refine ⟨?_,0,?_⟩
   · simp only [q,map_sum,map_mul,hf,mul_zero,sum_const_zero]
   · simpa only [G,q,map_sum,map_mul,eval_X,eval_C,pderiv_C_mul] using ha' i
 have hS:S.Nonempty :=card_pos.mp (by
   have hpos :0<(d+1)*(d+2) := by positivity
   omega)
 refine ⟨q,?_,?_,hcard.trans (zBI 2 (card_le_card ?_))⟩
 · obtain ⟨i,hi⟩:=hS
   obtain ⟨_,j,hj⟩:=hq ⟨i,hi⟩
   intro h
   exact hj (by simp [h])
 · apply totalDegree_finsetSum_le
   intro i _
   exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hdf i)
 · exact fun i hi=>mem_filter.mpr ⟨hST hi,hq ⟨i,hi⟩⟩
end qLUrYJc
end
section
set_option autoImplicit true
namespace qGzrWfb
noncomputable section
open MvPolynomial Finsupp
open cu (L)
open qe6nVeb (SeedPlane)
open q7YMR4d (ke oF)
private def exponent (i:Fin 3) :Fin 2 →₀ ℕ := ![0,single 0 1,single 1 1] i
private theorem first_jet (J:Ideal SeedPlane) [zAa L (SeedPlane ⧸ J)]
  (hJ:J≤ m^2) :3≤zsE L (SeedPlane ⧸ J) := by
 let F:SeedPlane →ₗ[L] (Fin 3→L) :=LinearMap.pi fun i=>lcoeff L (exponent i)
 have hker :J.restrictScalars L≤LinearMap.ker F:= by
  intro q hq
  ext i
  exact (mem_pow_idealOfVars_iff' 2 q).mp (hJ hq) (exponent i) (by fin_cases i <;> simp [exponent])
 let G: (SeedPlane ⧸ J) →ₗ[L] (Fin 3→L) :=(J.restrictScalars L).liftQ F hker
 have hinj:zq4 exponent:= by
  intro a b h
  have h0:=congrArg (fun d:Fin 2 →₀ ℕ=>d 0) h
  have h1 :=congrArg (fun d:Fin 2 →₀ ℕ=>d 1) h
  fin_cases a <;> fin_cases b <;> simp [exponent] at h0 h1 ⊢
 have hG:zpX G:= by
  intro u
  refine ⟨zVv J (∑ i,monomial (exponent i) (u i)),?_⟩
  funext i
  change (∑ j,monomial (exponent j) (u j)).coeff (exponent i)=u i
  simp [coeff_monomial,hinj.eq_iff]
 simpa only [zvt,Fintype.card_fin] using
  zs6 hG
private abbrev P:Ideal (zM1 L) :=zye {(z7y:zM1 L)^3}
private abbrev YS:=zM1 L ⧸ P
private def ε:YS:=zVv P z7y
private theorem ε_cube :ε^3=0:= by
 rw [ε,← map_pow,Ideal.Quotient.eq_zero_iff_mem]
 exact Ideal.mem_span_singleton_self _
private theorem cubic_jet (q g:SeedPlane) (j k :Fin 2) (hjk :j≠k) (r a b:L)
   (hb:b≠0) (hq:q - homogeneousComponent 2 q∈m^3)
   (hQ:homogeneousComponent 2 q=C a*zD j k r^2)
   (hg:g-(homogeneousComponent 1 g+homogeneousComponent 2 g)∈m^3)
   (hlin:homogeneousComponent 1 g=C b*zD j k r) :
   3≤zsE L (SeedPlane ⧸ (ke q g ⊔ m^3)) := by
 let A:=algebraMap L YS
 let d (s :Fin 2) :L:=if s=k then 1 else r
 let c:=eval d (homogeneousComponent 2 g)
 let t := -c/b
 let w (s :Fin 2) :L:=if s=k then 0 else t
 let v (s :Fin 2) :=A (d s)* ε+A (w s)* ε^2
 let F:SeedPlane →ₐ[L] YS:=aeval v
 have hmap :m≤(zye {ε}).comap F.toRingHom:= by
   rw [Ideal.span_le]
   rintro _ ⟨s,rfl⟩
   change F (z9v s)∈zye {ε}
   rw [show F (z9v s)=v s from aeval_X _ _]
   rw [Ideal.mem_span_singleton]
   refine ⟨A (d s)+A (w s)*ε,?_⟩
   dsimp [v]
   ring
 have hpow:m^3≤RingHom.ker F.toRingHom:= by
   have hh:=(pow_le_pow_left' hmap 3).trans
     (Ideal.le_comap_pow (K:=zye {ε}) F.toRingHom 3)
   rwa [Ideal.span_singleton_pow,ε_cube,Ideal.span_singleton_zero] at hh
 have ht:F (zD j k r)=A t* ε^2 := by
   simp [F,zD,v,d,w,hjk,A]
 have hqF:F q=0:= by
   have hz :=hpow hq
   change F (q - homogeneousComponent 2 q)=0 at hz
   rw [map_sub,sub_eq_zero] at hz
   have hε: (ε^2)^2=0:= by linear_combination ε* ε_cube
   rw [hz,hQ,map_mul,map_pow,ht,mul_pow,hε,mul_zero,mul_zero]
 have hprod (s z :Fin 2) :v s*v z=A (d s*d z)* ε^2 := by
   simp only [v,map_mul]
   linear_combination
     (A (d s)*A (w z)+A (w s)*A (d z)+A (w s)*A (w z)* ε)* ε_cube
 have hquad:F (homogeneousComponent 2 g)=A c* ε^2 := by
   obtain ⟨l,u,z,he⟩:=binary_form _ (homogeneousComponent_isHomogeneous 2 g)
   dsimp only [c]
   rw [he]
   simp only [F,map_add,map_mul,aeval_X,aeval_C,eval_X,eval_C,pow_two,mul_assoc]
   rw [hprod 0 0,hprod 0 1,hprod 1 1]
   simp only [A,map_mul]
   ring
 have hgF:F g=0:= by
   have hz :=hpow hg
   change F (g-(homogeneousComponent 1 g+homogeneousComponent 2 g))=0 at hz
   rw [map_sub,sub_eq_zero] at hz
   have hc:b*t+c=0:= by
     dsimp [t]
     field_simp
     ring
   rw [hz,map_add,hlin,map_mul,ht,hquad]
   rw [show F (C b)=A b from aeval_C _ _]
   rw [← mul_assoc,← map_mul,← add_mul,← map_add,hc,map_zero,zero_mul]
 let J:=ke q g ⊔ m^3
 have hker :J≤RingHom.ker F.toRingHom:= by
   refine sup_le (sup_le ?_ ?_) hpow
   · exact (zvl _).mpr hqF
   · exact (zvl _).mpr hgF
 let G:=Ideal.Quotient.liftₐ J F (fun _ hx=>hker hx)
 have hcomp:F.comp (zEU (z9v k :SeedPlane)) =
     Ideal.Quotient.mkₐ L P:= by
   apply Polynomial.algHom_ext
   change F (zEU (z9v k :SeedPlane) z7y)=ε
   simp [F,v,d,w,A]
 have hG:zpX G:= by
   intro x
   obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective x
   refine ⟨zVv J (zEU (z9v k :SeedPlane) f),?_⟩
   exact DFunLike.congr_fun hcomp f
 let:zAa L (SeedPlane ⧸ J) :=finite_jet J le_sup_right
 have hdim:zsE L YS=3:= by
   rw [finrank_quotient_span_eq_natDegree,Polynomial.natDegree_X_pow]
 simpa only [hdim] using zs6 (f :=G.toLinearMap) hG
private theorem at_origin (q:SeedPlane) (i:Fin 2)
   (hq:eval 0 q=0) (hd : ∀ j,eval 0 (pderiv j q)=0)
   (h : ¬ ∃ z :Fin 2→L,(∃ j,z j≠0) ∧
     q7YMR4d.SmoothAt (homogeneousComponent 2 q) z) :
   3≤zsE L (SeedPlane ⧸ (ke q (pderiv i q) ⊔ m^3)) := by
 let g:=pderiv i q
 let J:=ke q g ⊔ m^3
 let:zAa L (SeedPlane ⧸ J) :=finite_jet J le_sup_right
 have h0:=constant_zero hq
 have h1 :=linear_zero hd
 have hg0:homogeneousComponent 0 g=0:=constant_zero (hd i)
 obtain ⟨j,k,r,a,hjk,hQ⟩ :=
   square_tangent _ (homogeneousComponent_isHomogeneous 2 q) h
 let b:=2*a*((if j=i then 1 else 0) - r*(if k=i then 1 else 0))
 have hlin:homogeneousComponent 1 g=C b*zD j k r := by
   dsimp only [g]
   rw [c4t,hQ,tangent_polar]
 by_cases hb:b=0
 · have hg1 :homogeneousComponent 1 g=0:= by simp [hlin,hb]
   apply first_jet J
   apply sup_le (sup_le ?_ ?_) (Ideal.pow_le_pow_right (by decide))
   · exact (Ideal.span_singleton_le_iff_mem _).mpr (mem_square h0 h1)
   · exact (Ideal.span_singleton_le_iff_mem _).mpr (mem_square hg0 hg1)
 · refine cubic_jet q g j k hjk r a b hb ?_ hQ ?_ hlin
   · simpa [zpB,h0,h1] using sub_low q 3
   · simpa only [zpB,Finset.sum_range_zero,hg0,zero_add] using sub_low g 3
theorem proof :q7YMR4d.c3:= by
  intro q a i hq hd h
  let q' := shift a q
  let J:=ke q' (pderiv i q') ⊔ m^3
  let e : (SeedPlane ⧸ (ke q (pderiv i q) ⊔ oF a^3)) ≃ₐ[L]
      (SeedPlane ⧸ J) :=Ideal.quotientEquivAlg _ J (shiftEquiv a) (by
        change J=(ke q (pderiv i q) ⊔ oF a^3).map (shift a).toRingHom
        simp only [J,ke,Ideal.map_sup,Ideal.map_pow,shift_point,Ideal.map_span,
          Set.image_singleton,q']
        exact congrArg (fun p=>zye {shift a q} ⊔ zye {p} ⊔ m^3)
          (shift_pderiv a i q))
  rw [e.toLinearEquiv.finrank_eq]
  exact at_origin q' i ((cNb a q).trans hq)
    (fun j=> by
      change eval 0 (pderiv j (shift a q))=0
      rw [shift_pderiv,cNb]
      exact hd j) h
end
end qGzrWfb
end
end
