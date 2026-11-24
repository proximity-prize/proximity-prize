import ProximityPrize.SubmissionLower.ZNc08Oa
set_option Elab.async false
open _root_ renaming FaithfulSMul.algebraMap_injective→nq,Finset.card_filter_add_card_filter_not→ oq,Finset.sum_const_nat→lI,Finset.sum_le_sum→lJ,Function.Injective→nX,IsFractionRing.injective→ ov,Nat.mul_comm→n5,Nat.mul_le_mul→nI,P0.blockLength→c9,P5_7.NativeSeedBound→mD,P5_7.OneSeedEquation→cy,P5_7.atNative→lz,P5_7_7.sites→aU,Polynomial.evalRingHom→lV,Polynomial.induction_on'→ oj
section
set_option autoImplicit true
namespace P5_7_7
noncomputable section
open Polynomial Finset
open P5 (K)

open cu (L FX kr jz)
private theorem bOH (f :cy) (i j:ℕ) :
   ((Bivariate.swap f).coeff j).coeff i=(f.coeff i).coeff j:= by
 induction f using oj with
 | add a b ha hb=>simp only [map_add,coeff_add,ha,hb]
 | monomial n a =>
   induction a using oj with
   | add a b ha hb=>simp only [map_add,coeff_add,ha,hb]
   | monomial m a =>
     rw [Bivariate.swap_monomial_monomial]
     simp only [coeff_monomial]
     by_cases hi:n=i <;> by_cases hj:m=j <;> simp [coeff_monomial,hi,hj]
theorem bv9 (f :cy) (h:ℕ) :
   gY f≤h↔mD f h:= by
 unfold gY mD
 simp only [natDegree_le_iff_coeff_eq_zero]
 constructor
 · intro hh i j hj
   simpa only [← bOH f i j,coeff_zero] using congrArg (fun q:FX[X]=>q.coeff i) (hh j hj)
 · intro hh j hj
   ext i
   simp only [bOH,coeff_zero]
   exact hh i j hj
theorem acG {a b:cy} (ha :a≠0) (hb:b≠0) :
  gY (a*b)=gY a+gY b:= by
 unfold gY
 have hn (f :cy) (hf :f≠0) :Bivariate.swap f≠0 :=
  fun hz=>hf (Bivariate.swap.injective (hz.trans (map_zero Bivariate.swap).symm))
 rw [map_mul,natDegree_mul (hn a ha) (hn b hb)]
def nativeEval (z :K) (y :FX) :cy →+* FX :=
 eval₂RingHom (lV (jz z)) y
theorem atNative_mul (a b:cy) (z :K) (s :K[X]) :
  lz (a*b) z s=lz a z s*lz b z s :=
 map_mul (nativeEval z (kr s)) a b
theorem countRoots {α:Type*} (A:Finset α) (t:α→FX)
  (ht:Set.InjOn t (A:Set α)) (q:FX[X]) (hq:q≠0)
  (hr : ∀ γ∈A,q.eval (t γ)=0) :A.card≤q.natDegree := by
 classical
 rw [← card_image_of_injOn ht]
 apply card_le_degree_of_subset_roots
 intro a ha
 obtain ⟨γ,hγ,rfl⟩:=mem_image.mp (Finset.mem_def.mpr ha)
 exact (mem_roots hq).mpr (hr γ hγ)
theorem seedEmbedding_injective :nX jz :=
 (ov L[X] FX).comp (C_injective.comp (nq K L))
theorem atX_injective :nX kr :=
 (ov _ _).comp
   (Polynomial.map_injective _ (nq _ _))
theorem degree_zero_count {T:Finset K} {z :K→K} {S:K→K[X]}
    (hz :Set.InjOn z (T:Set K)) {f :cy} (hf :f≠0)
    (he :f.natDegree=0) (hr : ∀ γ∈T,lz f (z γ) (S γ)=0) :
    T.card≤gY f := by
  have hconst:=eq_C_of_natDegree_eq_zero he
  have hq:f.coeff 0≠0:= fun h=>hf (by rw [hconst,h,C_0])
  have hd:=(bv9 f _).mp le_rfl 0
  exact (countRoots T (jz ∘ z) (seedEmbedding_injective.comp_injOn hz)
      (f.coeff 0) hq (fun γ hγ=> by
        have h:=hr γ hγ
        rwa [lz ,hconst,eval₂_C,coe_evalRingHom] at h)).trans hd
theorem seed_zero_count {T:Finset K} {z :K→K} {S:K→K[X]}
   (hS:Set.InjOn S (T:Set K)) {f :cy} (hf :f≠0)
   (hs :mD f 0) (hr : ∀ γ∈T,lz f (z γ) (S γ)=0) :
   T.card≤f.natDegree := by
 have hc (i:ℕ) :=eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (hs i))
 have hcoeff (x :FX) (i:ℕ) :
     (f.map (lV x)).coeff i=(f.coeff i).coeff 0:= by
   rw [coeff_map,coe_evalRingHom]
   conv=>lhs; rw [hc i,eval_C]
 let q:=f.map (lV (0:FX))
 have hq:q≠0:= by
   intro h
   apply hf
   apply Polynomial.ext
   intro i
   have hz :=congrArg (fun q:FX[X]=>q.coeff i) h
   change (f.map (lV (0:FX))).coeff i=(0:FX[X]).coeff i at hz
   rw [hcoeff,coeff_zero] at hz
   rw [hc i,hz,C_0,coeff_zero]
 refine (countRoots T (kr ∘ S) (atX_injective.comp_injOn hS) q hq ?_).trans natDegree_map_le
 intro γ hγ
 have he :q=f.map (lV (jz (z γ))) := by
   ext i
   simp only [q,hcoeff]
 rw [he,eval_map]
 exact hr γ hγ
end
end P5_7_7
end
section
set_option autoImplicit true
namespace P5_7_7
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P5 (K I node blockLength)
open P5_7 (farAgreement gap)
open scoped Classical
theorem mem_sites {w:I→K} {S:K→K[X]} {γ:K} {i:I} :
 i∈aU w S γ↔hit w S γ i:= by simp [aU]
theorem index_card:Fintype.card I=blockLength:=IRSProfile.card_index
theorem base_injective :nX base :=
 (nq _ _).comp IRSProfile.domain.injective
private theorem hitmiss_pair {D w T z S} (M:UJ D w T z S) {a b:K}
  (ha :a∈T) (hb:b∈T) (hab:a≠b) :
  gap D ≤(aU w S a \ aU w S b).card:= by
 have hne :S a - S b≠0 :=
  sub_ne_zero.mpr fun h=>hab (M.sections ha hb h)
 have hp:=gR.kL.agd node IRSProfile.domain.injective
  (S a - S b) hne (aU w S a∩aU w S b) (by
    intro i hi
    have h₁:=mem_sites.mp (mem_inter.mp hi).1
    have h₂:=mem_sites.mp (mem_inter.mp hi).2
    change (S a).eval (node i)=w i at h₁
    change (S b).eval (node i)=w i at h₂
    rw [eval_sub,h₁,h₂,sub_self])
 have hd:=(natDegree_sub_le (S a) (S b)).trans (max_le (M.degree a ha) (M.degree b hb))
 have hsum:=card_sdiff_add_card_inter (aU w S a) (aU w S b)
 have hA:=M.dw a ha
 unfold gap
 omega
theorem linear_count {D w T z S h} (M:UJ D w T z S) (hh:0<h)
    (hgap:gap D ≤ c9)
    (hsite : ∀ i,(T.filter fun γ=>hit w S γ i).card≤h ∨
      (T.filter fun γ => ¬ hit w S γ i).card≤h) :
    gap D *T.card≤ c9*h:= by
  by_cases hsmall:T.card≤1
  · exact (nI hgap (hsmall.trans hh))
  let H (i:I) :=(T.filter fun γ=>hit w S γ i).card
  let N (i:I) :=(T.filter fun γ => ¬ hit w S γ i).card
  have hpair_count : ∑ i:I,H i*N i =
      ∑ a∈T,∑ b∈T,(aU w S a \ aU w S b).card:= by
    simp only [H,N,card_filter]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    have eq (i:I) : (if hit w S a i then 1 else 0:ℕ) *
        (if ¬ hit w S b i then 1 else 0)=if i∈aU w S a \ aU w S b then 1 else 0:= by
      simp only [mem_sdiff,mem_sites]
      by_cases ha :hit w S a i <;> by_cases hb:hit w S b i <;> simp [ha,hb]
    simp_rw [eq]
    rw [sum_boole,Nat.cast_id,filter_mem_eq_inter,univ_inter]
  have hlower :T.card*((T.card-1)*gap D) ≤
      ∑ a∈T,∑ b∈T,(aU w S a \ aU w S b).card:= by
    rw [← lI (s :=T) (f := fun _=>(T.card-1)*gap D) (fun _ _=>rfl)]
    refine lJ fun a ha => ?_
    have hz : (aU w S a \ aU w S a).card=0:= by rw [sdiff_self]; rfl
    rw [← add_sum_erase T _ ha,hz,zero_add,← card_erase_of_mem ha]
    rw [← lI (s :=T.erase a) (f := fun _=>gap D) (fun _ _=>rfl)]
    exact lJ fun b hb =>
      hitmiss_pair M ha (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm
  have hupper : ∑ i:I,H i*N i≤ c9*(h*(T.card-1)) := by
    rw [← index_card,← card_univ,← lI
      (s :=(univ :Finset I)) (f := fun _=>h*(T.card-1)) (fun _ _=>rfl)]
    refine lJ fun i _ => ?_
    have hsum:H i+N i=T.card:=oq (hit w S · i)
    by_cases ha :H i=0
    · simp [ha]
    by_cases hb:N i=0
    · simp [hb]
    rcases hsite i with hH | hN
    · exact nI hH (by omega)
    · rw [n5 (H i)]
      exact nI hN (by omega)
  have hh' := (hlower.trans_eq hpair_count.symm).trans hupper
  have hpos :0<T.card-1 := by omega
  exact Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,
    n5 ] using hh') hpos
theorem variation_count {D w U z S T F l h pole} (J:DualWord D w U S)
    (M:UJ D w U z S) (hD:D ≤farAgreement) (ht:T⊆U) (A:Variation J T z F l h pole) :
    gap D *T.card≤(exclusions l*gap D + nodeRate l*c9+pole)*h:= by
  let bad (γ:K) :=univ.filter fun i:I =>
    ¬ hit w S γ i∧(A.A γ).eval (base i)≠0
  let ν (γ:K) :=max (A.B γ).natDegree ((A.A γ).natDegree-relativeDegree J γ)
  have hγ (γ:K) (hm:γ∈A.good) :gap D ≤(bad γ).card+ν γ:= by
    let miss :=univ \ aU w S γ
    have hcard:miss.card=c9-(aU w S γ).card:= by
      change (univ \ aU w S γ).card= _
      rw [card_sdiff_of_subset (subset_univ _),card_univ,index_card]
    have heq :miss.filter (fun i=>(A.A γ).eval (base i)≠0)=bad γ:= by
      ext i
      simp [miss,bad,mem_sites]
    have hsum:=oq
      (s :=miss) (fun i=>(A.A γ).eval (base i)≠0)
    rw [heq,hcard] at hsum
    have hzero :=gR.kL.agd base base_injective
      (A.A γ) (A.nonzero γ hm) (miss.filter (fun i => ¬ (A.A γ).eval (base i)≠0))
      (fun _ hi=>not_ne_iff.mp (mem_filter.mp hi).2)
    have hU:=ht (A.Bp hm)
    have ⟨ha,hq,hp⟩:=J.degree γ hU
    have horder :=J.order
    have hwidth :=J.gMz
    have hAgr :=M.dw γ hU
    have hN : (aU w S γ).card≤blockLength:= by
      simpa only [card_univ,index_card] using card_le_card (subset_univ (aU w S γ))
    have hmax :max (J.Q γ).natDegree ((J.P γ).natDegree-(J.u₁-J.u₀)) ≤
        farAgreement+J.u₀-(aU w S γ).card:=max_le hq (by omega)
    have hrel :relativeDegree J γ+(aU w S γ).card+gap D ≤blockLength:= by
      simp only [relativeDegree,gap]
      omega
    unfold ν
    omega
  have hswap : ∑ γ∈A.good,(bad γ).card =
      ∑ i:I,(A.good.filter fun γ => ¬ hit w S γ i∧(A.A γ).eval (base i)≠0).card:= by
    simp only [bad,card_filter]
    rw [sum_comm]
  have hb : ∑ γ∈A.good,(bad γ).card≤ c9*(nodeRate l*h) := by
    rw [hswap,← index_card,← card_univ,← lI (s :=(univ :Finset I))
      (f := fun _=>nodeRate l*h) (fun _ _=>rfl)]
    exact lJ fun i _=>A.node_budget i
  have hgood:A.good.card*gap D ≤ c9*(nodeRate l*h)+pole*h:= by
    rw [← lI (s :=A.good) (f := fun _=>gap D) (fun _ _=>rfl)]
    exact (lJ fun γ hmem=>hγ γ hmem).trans
      (sum_add_distrib.trans_le (Nat.add_le_add hb A.pole_budget))
  have hz :=(card_sdiff_add_card_eq_card A.Bp).symm
  rw [hz,Nat.mul_add]
  calc
    _≤gap D *(exclusions l*h)+(c9*(nodeRate l*h)+pole*h) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ A.zJ) (by simpa only [n5 _ (gap D)] using hgood)
    _ = _:= by ring
end
end P5_7_7
end
section
set_option autoImplicit true
namespace P5_7_7R
open Polynomial
open P5_7_7 (Dg)
def atm (G:Dg) (E u s M:ℕ) :Prop :=
  ∀ i j,(G.coeff i).coeff j≠0 →
    ((G.coeff i).coeff j).natDegree+E*u+i*s<M
end P5_7_7R
end
section
set_option autoImplicit true
namespace qyWKMud
noncomputable section
open Polynomial Finset

open P5_7 (OneSeedEquation)
open cu (L FX)
open P5_7_7 (Dg DualWord embed phys gY)
def linear (a b:L[X]) :OneSeedEquation :=
 C (C (phys a))+C (C (phys b))*Polynomial.X (R:=FX[X])
def changed {D w U S} (J:DualWord D w U S) (f :cy) :OneSeedEquation :=
  ∑ i∈range (f.natDegree+1),C (f.coeff i) *
    linear (-J.b₁) J.b₀^i*linear J.a₁ (-J.a₀)^(f.natDegree-i)
structure Changed {D w U S} (J:DualWord D w U S) (f :cy) where
 F:Dg
 irred:Irreducible F
 generic_irred:Irreducible (embed F)
 repr : ∃ a :FX,a≠0∧embed F=C (C a)*changed J f
 jU:F.natDegree=f.natDegree
 height:gY (embed F)=gY f
 raw_height : ∀ i,(F.coeff i).natDegree≤gY f
end
end qyWKMud
end
