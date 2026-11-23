import ProximityPrize.SubmissionLower.ZJb37yc
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.C3
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.ZXTI5ee
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.ZDqG8Fa
import ProximityPrize.SubmissionLower.ZAcMpba
import ProximityPrize.SubmissionLower.ZTbQzvb
import ProximityPrize.SubmissionLower.ZqY5s9b
import ProximityPrize.SubmissionLower.Zm5KYKd
import ProximityPrize.SubmissionLower.ZbbSEle
import ProximityPrize.SubmissionLower.ZlfuKwd
set_option Elab.async false
open _root_ renaming Finset → zJe, Function.Injective → zq4, LinearMap.ker → z83, LinearMap.range → zWl, Module.finrank → zsE, MvPolynomial.map → zDK, Nat.mul_le_mul_left → zBI, Polynomial.C → z1z
section
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace quN7Z4a
noncomputable section
open Polynomial
open P5 (K I node p blockLength)
open P5_7 (midAgreement)
open P5_7_3 (fO)
open qAxtVye (HorizontalBand wX gap branchDegree)
open cu (L FX j9 kr jz)
open gT (kM bbt aSf abX aQ pZ)
open DQ (specialize)
open Cu
open private cK1 cK2 cK3 from ProximityPrize.SubmissionLower.CR
open private d2Q from ProximityPrize.SubmissionLower.G
open scoped BigOperators
structure OF (T:zJe K) (s :K→K[X]) (w:I→K) (D:ℕ) :Prop where
 distinct :Set.InjOn s (T:Set K)
 degree : ∀ γ∈T,(s γ).natDegree≤D
 lg : ∀ γ∈T,∃ U:zJe I,midAgreement≤U.card ∧ ∀ i∈U,(s γ).eval (node i)=w i
theorem degree_lt {b:fO} (hb:HorizontalBand b) :wX b< midAgreement:= by
 rcases hb with rfl | rfl <;> decide
abbrev Z7:=DP.Z7
def Smooth (C₀:sQ) (t:Fin 2→L) :Prop :=
 ∃ i:Fin 2,(MvPolynomial.pderiv i C₀).eval t≠0
private theorem constant_seed_zero (z :K) (n:ℕ) (v :FX) (C₀:sQ)
   (h:MvPolynomial.eval ![jz z,(jz z)^n,v]
     (pZ (zDK ((algebraMap L[X] FX).comp z1z) C₀))=0) :
   C₀.eval ![algebraMap K L z,(algebraMap K L z)^n]=0:= by
 let e :L →+* FX:=(algebraMap L[X] FX).comp z1z
 rw [d2Q,MvPolynomial.eval_map] at h
 have hpt:e ∘ (![algebraMap K L z,(algebraMap K L z)^n] :Fin 2→L) =
     ![jz z,(jz z)^n] := by
   funext i
   fin_cases i
   · rfl
   · exact map_pow e (algebraMap K L z) n
 rw [← hpt,← MvPolynomial.eval₂_comp,← map_zero e] at h
 exact e.injective h
private theorem seed_zero {C₀:sQ} {J:Ideal kM} {z :K} {S:K[X]}
  (he :J.comap pZ=BI C₀) (hm:aSf J z S) :
  C₀.eval (Z7 z)=0:= by
 have hz :pZ (zDK ((algebraMap L[X] FX).comp z1z) C₀)∈J:= by
  change zDK _ C₀∈J.comap pZ
  rw [he]
  exact Ideal.mem_span_singleton_self _
 exact constant_seed_zero z K1.p (kr S) C₀ (RingHom.mem_ker.mp (hm hz))
structure Sheet (C₀:sQ) [Fact (Irreducible C₀)] (J:Ideal kM)
   (g H :ℕ) (T:zJe K) (z :K→K) (s :K→K[X]) where
 root :wJ C₀ J g
 n:ℕ
 bY:yI root n
 parameter :K→Fin n→L
 onSeed : ∀ γ∈T,C₀.eval (Z7 (z γ))=0
 onBase : ∀ γ∈T,aCn (z γ) (parameter γ)∈MvPolynomial.zeroLocus FX (EF bY)
 identity : ∀ γ∈T,(specialize bY.equation (parameter γ)).eval (j9 (s γ))=0
 height:a9K (EF bY) H
theorem sheet {J:Ideal kM} {g d H :ℕ} {T:zJe K} {z s}
   (hg:0<g) (hc:bbt J g H)
   (hlen:zsE aQ (abX J)=d*g)
   (hm : ∀ γ∈T,aSf J (z γ) (s γ)) :
   ∃ (C₀:sQ) (hC₀:Irreducible C₀),C₀.totalDegree=d ∧
     Nonempty (@Sheet C₀ ⟨hC₀⟩ J g H T z s) := by
 obtain ⟨hJ,C₀,hC₀,hseed,hsf,hs,hyf,hy⟩:=hc
 let:Fact (Irreducible C₀) :=⟨hC₀⟩
 obtain ⟨R⟩:=cK1 C₀ J g hJ hseed hsf hs hg
 obtain ⟨n,A,t,hbase,_,hroots⟩:=cK2 C₀ J g R T z s hm
 exact ⟨C₀,hC₀,Nat.eq_of_mul_eq_mul_right hg (hs.symm.trans hlen),
   ⟨⟨R,n,A,t,fun γ hγ=>seed_zero hseed (hm γ hγ),hbase,hroots,cK3 C₀ J g H n R A hg hyf hy⟩⟩⟩
structure PoleStarts (T:zJe K) (z :K→K) (s :K→K[X]) where
 x :Fin 2→L
 distinct :zq4 x
 zJ : ∀ i j,x i≠algebraMap K L (node j)
 a :Fin 2→L
 b:Fin 2→L
 c:Fin 2→L
 a_ne : ∀ i,a i≠0
 c_ne : ∀ i,c i≠0
 den_ne : ∀ γ∈T,∀ i,a i+Z7 (z γ) i*b i≠0
 value : ∀ γ∈T,∀ i,
   (a i+Z7 (z γ) i*b i)*(j9 (s γ)).eval (x i) =
     c i*Z7 (z γ) i
def physicalWeight {C₀:sQ} (D:ℕ)
    (f : ((oO C₀)[X])[X]) :ℕ :=
  f.support.sup fun i=>(f.coeff i).natDegree+i*D
def compressionWidth (D g:ℕ) :ℕ:=2*D*g*(g+1)
def standardUnit (b:fO) (g:ℕ) :ℚ :=
 8+6*(g:ℚ)+((2*g*blockLength+2*g*(2*branchDegree b g-1) :ℕ) :ℚ)/gap b
def quadraticUnit (b:fO) :ℚ:=13+8*(blockLength:ℚ)/gap b
structure VariationBudget (U:zJe K) (s :K→K[X]) (w:I→K)
  (b:fO) (g d H :ℕ) where
 good:zJe K
 subset :good⊆U
 exceptional: (U \ good).card≤(8+6*g)*H+4*g*g*d
 zeroNodes :K→zJe I
 finitePoles :K→ℕ
 Ju : ∀ γ∈good,(zeroNodes γ).card≤wX b+finitePoles γ
 poles : ∑ γ∈good,finitePoles γ≤2*g*(2*branchDegree b g-1)*H
 lg : ∀ i,(good.filter (fun γ =>
  (s γ).eval (node i)=w i∧i∉zeroNodes γ)).card≤2*g*H
end
end quN7Z4a
end
end
section
section
set_option autoImplicit true
namespace qm7o3Fa
noncomputable section
open aR (ao)
open Rj (lK adf kJ yE Jd m5)
open baj (alQ aIL aJM aT5
 a9V bAa bqh cJ1 ezV ec2)
open P5_7_2 (TopRow)
open qSxbgdc
open qPQ4nYa (cappedCumulative)
open Finset MvPolynomial
open scoped BigOperators
open private aEg c0e cEi exponent cxO.exponent_injective eLR eLT from ProximityPrize.SubmissionLower.A3
open private gGU diD eQh eQi from ProximityPrize.SubmissionLower.C
open private product b2K d5V cN8 cEp aIu from ProximityPrize.SubmissionLower.C
private def HX (d C:ℕ) (w:ℤ) :zJe (ℕ×ℕ) :=
 (aEg d w).filter fun p=>p.1≤C
private theorem aVQ (d C:ℕ) (w:ℤ) (p:ℕ×ℕ) :
  p∈HX d C w↔(p.1+p.2≤d∧(p.2 :ℤ)+2*p.1≤w)∧p.1≤C:= by
 simp only [HX,mem_filter,c0e]
private theorem cEd (d C:ℕ) (w:ℤ) :
    ((HX d C w).card:ℤ)=cappedCumulative d C w:= by
  by_cases hC:C<d
  · let shift:ℕ×ℕ→ℕ×ℕ:= fun p=>(p.1+(C+1),p.2)
    have hi:zq4 shift:= by
      intro p r h
      have h₁:=congrArg Prod.fst h
      have h₂:=congrArg Prod.snd h
      exact Prod.ext (Nat.add_right_cancel h₁) h₂
    have hx : ((aEg d w).filter fun p => ¬ p.1≤C) =
        (aEg (d-(C+1)) (w - 2*((C:ℤ)+1))).image shift:= by
      ext p
      simp only [mem_filter,mem_image,c0e]
      constructor
      · intro hp
        refine ⟨(p.1-(C+1),p.2),?_,?_⟩
        · dsimp
          omega
        · apply Prod.ext
          · dsimp [shift]
            omega
          · rfl
      · rintro ⟨r,hr,rfl⟩
        dsimp [shift]
        omega
    have h:=congrArg (fun n:ℕ=>(n:ℤ))
      (card_filter_add_card_filter_not (s :=aEg d w) fun p=>p.1≤C)
    simp only [Nat.cast_add,hx,card_image_of_injective _ hi,cEi] at h
    simpa only [HX,cappedCumulative,hC,ite_true] using eq_sub_of_add_eq h
  · have h:HX d C w=aEg d w:= by
      ext p
      simp only [aVQ,c0e]
      omega
    simp [h,cappedCumulative,hC,cEi]
private def vo (d C:ℕ) (J g:ℤ) :zJe (ℕ×ℕ) :=
 HX d C J \ HX d C (min J (-g - 1))
private theorem dFD (d C:ℕ) (J g:ℤ) :
  ((vo d C J g).card:ℤ)=cappedCumulative d C J - cappedCumulative d C (min J (-g - 1)) := by
 have hs :HX d C (min J (-g - 1))⊆HX d C J:= by
  intro p hp
  rw [aVQ] at hp ⊢
  omega
 have h:=congrArg (fun n:ℕ=>(n:ℤ)) (card_sdiff_add_card_eq_card hs)
 simp only [Nat.cast_add] at h
 have h' : ((vo d C J g).card:ℤ) =
    ((HX d C J).card:ℤ)-((HX d C (min J (-g - 1))).card:ℤ) :=eq_sub_of_add_eq h
 simpa only [cEd] using h'
variable (b:TopRow)
private theorem bnD (q:ℕ) (g:ℤ) :
   (↑((vo (iO b q) b.YM b.shape.J g).image (exponent (iO b q))) :
     Set adf)=cbQ b q g:= by
 ext e
 simp only [mem_coe,mem_image,vo,mem_sdiff,aVQ,cbQ,
   Set.mem_ofPred_eq,eLR,eLT]
 constructor
 · rintro ⟨p,hp,rfl⟩
   simp [exponent]
   omega
 · intro he
   refine ⟨(e 2,e 1),?_,?_⟩
   · dsimp
     omega
   · ext j
     fin_cases j <;> simp [exponent]
     omega
private theorem gte (q:ℕ) (g:ℤ) :
  (zsE ao (aqz b q g) :ℤ)=Bb b q g:= by
 unfold aqz Bb
 rw [← bnD b q g,finrank_restrictSupport_finset,
  card_image_of_injective _ (cxO.exponent_injective _),dFD]
private theorem eIi {q:ℕ} {g:ℤ} {f :lK}
  (hd:f.IsWeightedHomogeneous alQ (iO b q))
  (hf :bAa (pT b q g) f) :
  ∃ hsrc :f∈aqz b q g,(⟨f,hsrc⟩:aqz b q g) ∈
    z83 (aPi b q g) := by
 have hP:f∈restrictWeightedOrder Fin.val (-g).toNat := by
  rw [← gGU f]
  apply bind₁_mem_restrictWeightedOrder _ (hf 0).2
  intro i
  fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
 have hQo:f∈restrictWeightedOrder eQh ((iO b q:ℤ) - b.YM).toNat := by
  rw [← diD f]
  apply bind₁_mem_restrictWeightedOrder _ (hf 1).1
  intro i
  fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
 have hQw:f∈restrictWeightedOrder eQi (2*(iO b q:ℤ) - b.shape.J).toNat := by
  rw [← diD f]
  apply bind₁_mem_restrictWeightedOrder _ (hf 1).2
  intro i
  fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
 have hsrc :f∈aqz b q g:= by
  apply (mem_restrictSupport_iff ao).mpr
  intro e he
  have hdeg:=hd (mem_support_iff.mp he)
  have hn:=mem_restrictWeightedOrder.mp hP e he
  have ho:=mem_restrictWeightedOrder.mp hQo e he
  have hw:=mem_restrictWeightedOrder.mp hQw e he
  change e.weight alQ=iO b q ∧ -g≤(e.weight Fin.val :ℤ) ∧
    e.weight Fin.val≤b.shape.J∧e 2≤b.YM
  rw [aT5] at hdeg
  simp [Finsupp.weight_eq_sum,Fin.sum_univ_three,smul_eq_mul,Nat.mul_comm] at hn ho hw ⊢
  omega
 refine ⟨hsrc,LinearMap.mem_ker.mpr ?_⟩
 apply (weightedTruncation_eq_zero_iff _ _ _).mpr
 exact (hf 2).2
private theorem eO0 (q:ℕ) (p:kJ) {f :lK}
   (hn:0≤K6 b q p)
   (hf :f.IsWeightedHomogeneous alQ (K6 b q p).toNat) :
   (product p*f).IsWeightedHomogeneous alQ (iO b q) := by
 have hp: (product p).IsWeightedHomogeneous alQ (∑ j,p j*(yE j).toNat) := by
   apply IsWeightedHomogeneous.prod
   intro j _
   simpa only [Nat.nsmul_eq_mul] using (d5V j).pow (p j)
 have hc:=cEp p yE (by intro j; unfold yE; split <;> decide)
 have hsum: (∑ j,p j*(yE j).toNat)+(K6 b q p).toNat =
     iO b q:= by
   unfold K6 at hn ⊢
   omega
 rw [← hsum]
 exact hp.mul hf
private theorem eO1 (q:ℕ) (g:ℤ) (p:kJ) {f :lK}
  (hf :bAa (D8 b q g p) f) :bAa (pT b q g) (product p*f) := by
 intro i
 exact ⟨aIu p i aIL (pT b q g i).iy
    (fun j=>(Jd j i).iy)
    (by intro j; fin_cases j <;> fin_cases i <;> decide)
    (fun j=>(cN8 j i).1) (hf i).1,
  aIu p i aJM (pT b q g i).HE
    (fun j=>(Jd j i).HE)
    (by intro j; fin_cases j <;> fin_cases i <;> decide)
    (fun j=>(cN8 j i).2) (hf i).2⟩
private theorem ewc (q:ℕ) (g:ℤ) (p:kJ) (hn:0≤K6 b q p) :
   zsE ao (z83 (bqh (K6 b q p).toNat (D8 b q g p))) ≤
     zsE ao (z83 (aPi b q g)) := by
 let S:=z83 (bqh (K6 b q p).toNat (D8 b q g p))
 have h (f :S) :=eIi b (q:=q) (g:=g)
   (eO0 b q p hn (cJ1 f.val))
   (eO1 b q g p (ezV f))
 let L:S →ₗ[ao] lK :=
   (LinearMap.mulLeft ao (product p)).comp
     (((a9V (K6 b q p).toNat).subtype).comp S.subtype)
 let M:=L.codRestrict (aqz b q g) (fun f=>(h f).choose)
 let N :=M.codRestrict (z83 (aPi b q g)) (fun f=>(h f).choose_spec)
 apply LinearMap.finrank_le_finrank_of_injective (f :=N)
 intro f f' hff'
 apply Subtype.ext
 apply Subtype.ext
 have hp:product p≠0 :=
   Finset.prod_ne_zero_iff.mpr fun j _=>pow_ne_zero _ (b2K j)
 exact mul_left_cancel₀ hp (congrArg (fun a=>(a.val :lK)) hff')
private theorem plane_kernel_lower (q:ℕ) (g:ℤ) (p:kJ) :
   m5 (K6 b q p) (D8 b q g p) ≤
     (zsE ao (z83 (aPi b q g)) :ℤ) := by
 let d:=K6 b q p
 by_cases hn:K6 b q p<0
 · simp [m5,hn]
 have hnonneg:0≤d:=le_of_not_gt hn
 have hres :=ec2 d.toNat (D8 b q g p)
 rw [Int.toNat_of_nonneg hnonneg] at hres
 have hl:=ewc b q g p hnonneg
 simp only [m5,hn,ite_false]
 exact hres.trans (by exact_mod_cast hl)
private theorem c4g (q k :ℕ) (p:kJ) :
   zsE ao (zWl (aPi b q (offset b k)))≤xR b q (offset b k) p:= by
 let f :=aPi b q (offset b k)
 by_cases hcut:Ic b q (offset b k)≤0
 · have hz :f=0:= by
     ext L:1
     simp [f,aPi,Int.toNat_of_nonpos hcut,weightedTruncation_eq_zero_iff]
   change zsE ao (zWl f)≤_
   simp [hz,xR,hcut]
 have hdim:=f.finrank_range_add_finrank_ker
 have hcols :=gte b q (offset b k)
 have hshift:=plane_kernel_lower b q (offset b k) p
 have hbase :=plane_kernel_lower b q (offset b k) (fun _=>0)
 have hdeg:K6 b q (fun _=>0)=iO b q:= by simp [K6]
 have hflag:D8 b q (offset b k) (fun _=>0)=pT b q (offset b k) := by
   funext i
   simp only [D8,Nat.cast_zero,zero_mul,Finset.sum_const_zero,sub_zero]
 rw [hdeg,hflag] at hbase
 change _≤(zsE ao (z83 f) :ℤ) at hshift hbase
 have hlower :=max_le (Int.natCast_nonneg (zsE ao (z83 f)))
   (max_le hbase hshift)
 change zsE ao (zWl f)≤_
 simp only [xR,hcut,ite_false]
 change (zsE ao f.range :ℤ).toNat≤_
 exact Int.toNat_le_toNat (by omega)
theorem rank_le (b:TopRow) (q k :ℕ) (p:kJ) :
   zsE ao (zWl (af3 b q k))≤xR b q (offset b k) p :=
 (fTp b q k).trans (c4g b q k p)
end
end qm7o3Fa
end
section
set_option autoImplicit true
theorem qzM5sEd.proof :qPQ4nYa.c1 := fun b q k _ _ p =>
 qm7o3Fa.rank_le (qPQ4nYa.top b) q k p
end
section
set_option autoImplicit true
namespace qSxbgdc
noncomputable section
open aR (ao)
open Rj (kJ)
open P5_7_2 (topDonors)
open q7IA62d (profile cutoff)
open qlc9qed (Bank)
def c1 :Prop :=
  ∀ q≤T8.shape.B,∀ k<T8.shape.m+T8.shape.J,∀ p:kJ,
    zsE ao (zWl (af3 T8 q k)) ≤
      xR T8 q (offset T8 k) p
def c2 :Prop := ∃ p:ℕ→ℕ→kJ,rankBudget T8 p≤T8.avF
private theorem near_rank (b:Bank) :
  zsE ao (qPQ4nYa.originRange b)≤b.contactRank := by
 have h : ∃ p:ℕ→ℕ→kJ,qPQ4nYa.rankBudget b p≤b.contactRank := by
  cases b
  · exact P5_7_2_3Q1322.proof
  · exact P5_7_2_3Q132.proof
 obtain ⟨p,hp⟩:=h
 exact (qPQ4nYa.originRange_le_sum b p
  (fun q hq k hk=>qzM5sEd.proof b q k hq hk (p q k))).trans hp
theorem of_children (h1 :c1) (h2 :c2) :q7IA62d.c2 := by
  intro b e h x v
  change _≤((profile b e).shape.U + 1)*(profile b e).avF
  refine (codim_le_origin (profile b e) x v h (cutoff (profile b e))).trans
    (zBI _ ?_)
  cases e with
  | false =>
    rw [show profile b false=(topDonors b).1 from rfl,topDonors]
    by_cases hb:b.val<7
    · rw [if_pos hb]
      exact near_rank .cheap
    · rw [if_neg hb]
      exact near_rank .cheap
  | true =>
    rw [show profile b true=(topDonors b).2 from rfl,topDonors]
    by_cases hb:b.val<7
    · rw [if_pos hb]
      exact near_rank .strong
    · rw [if_neg hb]
      obtain ⟨p,hp⟩:=h2
      exact (originRange_le_sum T8 p (fun q hq k hk =>
        h1 q (Nat.lt_succ_iff.mp hq) k hk (p q k))).trans hp
end
end qSxbgdc
end
end
section
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2708 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2708) 2708 e ((((P5_7_3.fO.h2708).schedule.gw).drop a).take 1)
theorem yQg0:gZ! 6 5:=⟨r! 93865 6 809 69 71 23 4 1 3 0x289039f4565b504,trivial⟩
theorem yQg1:gZ! 7 6:=⟨r! 94523 7 800 69 71 23 4 1 3 0x809070665672b02,trivial⟩
theorem yQg2:gZ! 8 7:=⟨r! 95116 8 790 66 71 26 4 1 3 0x21624284442b43fd60,trivial⟩
theorem yQg3:gZ! 9 8:=⟨r! 96040 9 781 69 71 23 4 1 3 0x1e090f07956a90d8,trivial⟩
theorem yQg4:gZ! 10 9:=⟨r! 96940 10 771 69 71 23 4 1 3 0x300913e2856c99e2,trivial⟩
theorem yQg5:gZ! 11 10:=⟨r! 97843 11 760 67 71 25 4 1 3 0x1188918ca5d5baa752,trivial⟩
theorem grades2708B:GradeSigns (terminal .h2708) 2708 6 ((((P5_7_3.fO.h2708).schedule.gw).drop 5).take 6) :=⟨yQg0.1,yQg1.1,yQg2.1,yQg3.1,yQg4.1,yQg5.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2708 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2708) 2708 e ((((P5_7_3.fO.h2708).schedule.gw).drop a).take 1)
theorem yQg6:gZ! 12 11:=⟨r! 98993 12 749 67 71 25 4 1 3 0x182891f32295c5397a,trivial⟩
theorem yQg7:gZ! 13 12:=⟨r! 100468 13 738 69 71 23 4 2 3 0x7f89279e8574ba9e,trivial⟩
theorem yQg8:gZ! 14 13:=⟨r! 101918 14 725 66 71 26 4 2 3 0x139e24c007cabc12842,trivial⟩
theorem yQg9:gZ! 15 14:=⟨r! 103948 15 712 68 71 24 4 2 3 0x5d624f074ccf9fab2,trivial⟩
theorem yQg10:gZ! 16 15:=⟨r! 106614 16 698 69 71 24 4 2 3 0x34e2299092c837b18,trivial⟩
theorem yQg11:gZ! 17 16:=⟨r! 110239 17 682 69 72 24 3 3 3 0xe28163b0b68c8bea,trivial⟩
theorem grades2708C:GradeSigns (terminal .h2708) 2708 12 ((((P5_7_3.fO.h2708).schedule.gw).drop 11).take 6) :=⟨yQg6.1,yQg7.1,yQg8.1,yQg9.1,yQg10.1,yQg11.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2708 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2708) 2708 e ((((P5_7_3.fO.h2708).schedule.gw).drop a).take 1)
theorem yQg12:gZ! 18 17:=⟨r! 115964 18 663 67 72 26 3 3 3 0x39c818a3fdda6dbc7e,trivial⟩
theorem yQg13:gZ! 19 18:=⟨r! 127365 19 640 69 72 24 4 3 3 0x3c223bb3448bb3b48,trivial⟩
theorem yQg14:gZ! 20 19:=⟨r! 153519 20 607 69 72 25 4 3 3 0x11208aefce590f394c,trivial⟩
theorem yQg15:gZ! 21 20:=⟨r! 153600 21 563 68 72 26 4 2 3 0x36422bacedb21f82b4,trivial⟩
theorem yQg16:gZ! 22 21:=⟨r! 153600 22 516 69 72 25 4 2 3 0x1908ae3cad90ffe30,trivial⟩
theorem yQg17:gZ! 23 22:=⟨r! 153600 23 465 65 72 29 4 2 3 0xe08adcc66991036aca,trivial⟩
theorem grades2708D:GradeSigns (terminal .h2708) 2708 18 ((((P5_7_3.fO.h2708).schedule.gw).drop 17).take 6) :=⟨yQg12.1,yQg13.1,yQg14.1,yQg15.1,yQg16.1,yQg17.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2708 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2708) 2708 e ((((P5_7_3.fO.h2708).schedule.gw).drop a).take 1)
theorem yQg18:gZ! 24 23:=⟨r! 153600 24 411 67 72 27 4 2 3 0x8ad60366441b32a,trivial⟩
theorem yQg19:gZ! 25 24:=⟨r! 153600 25 354 69 72 25 4 1 3 0x8acf8bd910a090,trivial⟩
theorem yQg20:gZ! 26 25:=⟨r! 153600 26 293 69 72 25 4 1 3 0x8ac98b5910d092,trivial⟩
theorem yQg21:gZ! 27 26:=⟨r! 153600 27 228 65 72 29 4 1 3 0x8ac3f889910fd1f0,trivial⟩
theorem yQg22:gZ! 28 27:=⟨r! 153600 28 161 69 72 25 4 1 3 0x8abe7a99112916,trivial⟩
theorem yQg23:gZ! 29 28:=⟨r! 153600 29 90 68 72 26 4 1 3 0x22ae58a3222a3ac,trivial⟩
theorem grades2708E:GradeSigns (terminal .h2708) 2708 24 ((((P5_7_3.fO.h2708).schedule.gw).drop 23).take 6) :=⟨yQg18.1,yQg19.1,yQg20.1,yQg21.1,yQg22.1,yQg23.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qWKyASa
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2708 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .h2708) 2708 e ((((P5_7_3.fO.h2708).schedule.gw).drop a).take 1)
theorem yQg24:gZ! 30 29:=⟨r! 153600 30 16 69 73 25 3 12 2 0x55a41ed1178ca,trivial⟩
theorem grades2708F:GradeSigns (terminal .h2708) 2708 30 (((P5_7_3.fO.h2708).schedule.gw).drop 29) :=⟨yQg24.1,trivial⟩
end qWKyASa
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (Signs GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2715 e v k l b d z n x
theorem ordinary2715:Signs (terminal .daC) 2715 30 0 :=
 r! 153600 30 0 75 73 19 3 12 2 0x5457b44b1e
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daC) 2715 e ((((P5_7_3.fO.daC).schedule.gw).drop a).take 1)
theorem yQg25:gZ! 1 0:=⟨r! 89547 1 819 68 71 24 4 12 2 0x3aa1dc8b994c8,trivial⟩
theorem yQg26:gZ! 2 1:=⟨r! 89946 2 811 66 71 26 4 12 2 0x3b1818a2ed3276,trivial⟩
theorem yQg27:gZ! 3 2:=⟨r! 90406 3 803 62 71 30 4 12 2 0x3ba387e22f51ea52,trivial⟩
theorem yQg28:gZ! 4 3:=⟨r! 90940 4 795 66 71 26 4 12 2 0x3c4901a2fe5342,trivial⟩
theorem yQg29:gZ! 5 4:=⟨r! 91558 5 787 68 71 24 4 1 3 0x23d0c588c2405e,trivial⟩
theorem yQg30:gZ! 6 5:=⟨r! 92092 6 778 65 71 27 4 1 3 0x1a88f6caab4624b15a,trivial⟩
theorem grades2715A:GradeSigns (terminal .daC) 2715 1 (((P5_7_3.fO.daC).schedule.gw).take 6) :=⟨yQg25.1,yQg26.1,yQg27.1,yQg28.1,yQg29.1,yQg30.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2715 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daC) 2715 e ((((P5_7_3.fO.daC).schedule.gw).drop a).take 1)
theorem yQg31:gZ! 7 6:=⟨r! 92917 7 770 69 71 23 4 1 3 0x588fb02056416d2,trivial⟩
theorem yQg32:gZ! 8 7:=⟨r! 93497 8 760 66 71 26 4 1 3 0x1a623f7852ab2b003c,trivial⟩
theorem yQg33:gZ! 9 8:=⟨r! 94411 9 751 69 71 23 4 1 3 0x190902a1f56764f0,trivial⟩
theorem yQg34:gZ! 10 9:=⟨r! 95308 10 741 68 71 24 4 1 3 0x14e241d48aad2cb66,trivial⟩
theorem yQg35:gZ! 11 10:=⟨r! 96213 11 730 63 71 29 4 1 3 0xf8f090c163715adc0a24,trivial⟩
theorem yQg36:gZ! 12 11:=⟨r! 97597 12 720 69 71 23 4 1 3 0x588913a6756e92d2,trivial⟩
theorem grades2715B:GradeSigns (terminal .daC) 2715 7 ((((P5_7_3.fO.daC).schedule.gw).drop 6).take 6) :=⟨yQg31.1,yQg32.1,yQg33.1,yQg34.1,yQg35.1,yQg36.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2715 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daC) 2715 e ((((P5_7_3.fO.daC).schedule.gw).drop a).take 1)
theorem yQg37:gZ! 13 12:=⟨r! 98894 13 708 68 71 24 4 2 3 0x3a2246b344ae31cf0,trivial⟩
theorem yQg38:gZ! 14 13:=⟨r! 100651 14 696 69 71 23 4 2 3 0x920924c5d575a4e4,trivial⟩
theorem yQg39:gZ! 15 14:=⟨r! 102833 15 683 69 71 23 4 2 3 0xad893180567acf04,trivial⟩
theorem yQg40:gZ! 16 15:=⟨r! 105514 16 668 68 71 25 4 2 3 0x18188a0d0fd902956e,trivial⟩
theorem yQg41:gZ! 17 16:=⟨r! 109753 17 652 69 71 24 4 3 3 0x32e22b895ac8bd892,trivial⟩
theorem yQg42:gZ! 18 17:=⟨r! 116689 18 632 67 72 26 3 3 3 0x333818aa5b9a77d01a,trivial⟩
theorem grades2715C:GradeSigns (terminal .daC) 2715 13 ((((P5_7_3.fO.daC).schedule.gw).drop 12).take 6) :=⟨yQg37.1,yQg38.1,yQg39.1,yQg40.1,yQg41.1,yQg42.1,trivial⟩
end qNKxb0a
end
end
section
section
set_option autoImplicit true
namespace qWKyASa
open qqf9uAa (GradeSigns)
theorem proof :qqf9uAa.c1 := by
 intro b _ hlo
 cases b
 case h2704 =>
  exact ⟨ordinary2704,
   GradeSigns.append grades2704A
   (GradeSigns.append grades2704B
   (GradeSigns.append grades2704C
   (GradeSigns.append grades2704D
   grades2704E)))⟩
 case h2708 =>
  exact ⟨ordinary2708,
   GradeSigns.append grades2708A
   (GradeSigns.append grades2708B
   (GradeSigns.append grades2708C
   (GradeSigns.append grades2708D
   (GradeSigns.append grades2708E
   grades2708F))))⟩
 all_goals exact ((Nat.not_lt_of_ge (by decide)) hlo).elim
end qWKyASa
end
section
set_option autoImplicit true
namespace qNKxb0a
open qqf9uAa (BandSigns GradeSigns)
private theorem sign2715:BandSigns .daC :=
 ⟨ordinary2715,GradeSigns.append grades2715A (GradeSigns.append grades2715B
   (GradeSigns.append grades2715C (GradeSigns.append grades2715D grades2715E)))⟩
private theorem sign2725:BandSigns .daF :=
 ⟨ordinary2725,GradeSigns.append grades2725A (GradeSigns.append grades2725B
   (GradeSigns.append grades2725C (GradeSigns.append grades2725D grades2725E)))⟩
theorem proof :qqf9uAa.c2 := by
 intro b hlo hhi
 cases b
 case daC=>exact sign2715
 case daF=>exact sign2725
 all_goals
  first
  | exact (Nat.not_le_of_lt (by decide) hlo).elim
  | exact (Nat.not_lt_of_ge (by decide) hhi).elim
end qNKxb0a
end
section
set_option autoImplicit true
namespace qsX8Fva
open qqf9uAa
private theorem signs2980:BandSigns .tI :=
 ⟨ordinary2980,GradeSigns.append grades2980A
   (GradeSigns.append grades2980B (GradeSigns.append grades2980C grades2980D))⟩
private theorem signs3000:BandSigns .s6 :=
 ⟨ordinary3000,GradeSigns.append grades3000A
   (GradeSigns.append grades3000B (GradeSigns.append grades3000C grades3000D))⟩
private theorem signs3050:BandSigns .tT :=
 ⟨ordinary3050,GradeSigns.append grades3050A
   (GradeSigns.append grades3050B (GradeSigns.append grades3050C grades3050D))⟩
theorem proof :qqf9uAa.c6:= by
 intro b hl hh
 cases b
 case tI=>exact signs2980
 case s6=>exact signs3000
 case tT=>exact signs3050
 all_goals first
  | exact ((Nat.not_le_of_lt (by decide)) hl).elim
  | exact ((Nat.not_lt_of_ge (by decide)) hh).elim
end qsX8Fva
end
section
namespace P5_7_3_5_2
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (K I blockLength)
open qkgz7gb (PlaneCurve UJ rV ceilDiv)
open qb0hmCe (CurveModel SiteTarget)
open P5_7_7 (base base_injective hit index_card)
open cu (L)
open DP (Tj Z7)
private theorem no_common_root {f g:L[X]} (h:IsCoprime f g) {y :L}
  (hg:g.eval y=0) :f.eval y≠0:= by
 intro hf
 obtain ⟨a,b,hab⟩:=h
 have he :=congrArg (fun p:L[X]=>p.eval y) hab
 simp only [eval_add,eval_mul,hf,hg,mul_zero,add_zero,eval_one,zero_ne_one] at he
theorem starts {D:ℕ} {w:I→K} {T:zJe K} {z :K→K} {S:K→K[X]}
   (m:UJ D w T z S) :Nonempty (Starts T z S) := by
 obtain ⟨h,hh,P,hP⟩:=m.poles
 have hex (i:Fin 2) : ∃ y,(P.block i).eval y=0:= by
   apply IsAlgClosed.exists_root
   rw [degree_eq_natDegree (P.monic i).ne_zero,P.degree]
   exact_mod_cast hh.ne'
 choose y hy using hex
 let R (i:Fin 2) :SiteTarget :=
   ⟨y i,i,0,-(P.offset i).eval (y i),(P.constant i).eval (y i),(P.slope i).eval (y i)⟩
 refine ⟨⟨R,?_,fun _=>rfl,?_,?_⟩⟩
 · intro he
   change y 0=y 1 at he
   exact no_common_root P.coprime (hy 1) (he ▸ hy 0)
 · intro i
   simpa only [R,SiteTarget.det,zero_mul,neg_mul,zero_sub,neg_neg,eval_mul] using
     no_common_root (P.determinant i) (hy i)
 · intro γ hγ i
   obtain ⟨hc,hd⟩:=hP γ hγ i
   have hn:=no_common_root hc (hy i)
   have hr :=eval_eq_zero_of_dvd_of_eval_eq_zero hd (hy i)
   have hseed :Z7 (z γ) i=rV z γ i:=rfl
   simp only [Tj,eval_add,eval_mul,eval_C,hseed] at hn hr
   refine ⟨?_,?_⟩
   · simpa only [R,mul_comm] using hn
   · dsimp only [R]
     linear_combination hr
theorem ceil_mul {a g:ℕ} (hg:0<g) :a≤g*ceilDiv a g:= by
 have h₁:=Nat.mod_lt (a+g-1) hg
 have h₂:=Nat.mod_add_div (a+g-1) g
 unfold ceilDiv
 omega
theorem incidence {D:ℕ} {w:I→K} {T:zJe K} {z :K→K} {S:K→K[X]}
   (m:UJ D w T z S) {q:PlaneCurve} {C:CurveModel q}
   {F:Sheet C z S} (V:Variation F) (hT:V.marks⊆T) (n v a :ℕ)
   (hn : ∀ i:I,(V.marks.filter fun γ=>hit w S γ i∧(V.num γ).eval (base i)≠0).card≤n)
   (hv : ∑ γ∈V.marks,V.DG D γ≤v)
   (ha : (V.marks.filter fun γ=>V.num γ=0).card≤a) :
   gap D *V.marks.card≤blockLength*n+v+gap D*a := by
 let good:=V.marks.filter fun γ=>V.num γ≠0
 let bad (γ:K) :=univ.filter fun i:I=>hit w S γ i∧(V.num γ).eval (base i)≠0
 have each (γ:K) (hm:γ∈good) :gap D ≤(bad γ).card+V.DG D γ:= by
   have hg:=mem_filter.mp hm
   obtain ⟨J,hJ,hr⟩:=m.dw γ (hT hg.1)
   let A:=J.filter fun i=>(V.num γ).eval (base i)≠0
   let B:=J.filter fun i => ¬ (V.num γ).eval (base i)≠0
   have hbad:A.card≤(bad γ).card:=card_le_card fun i hi =>
     mem_filter.mpr ⟨mem_univ _,hr i (mem_filter.mp hi).1,(mem_filter.mp hi).2⟩
   have hzero :=gR.kL.agd base base_injective
     (V.num γ) hg.2 B (fun _ hi=>not_ne_iff.mp (mem_filter.mp hi).2)
   have hsum:A.card+B.card=J.card:=card_filter_add_card_filter_not _
   have hdeg:=le_max_right (V.den γ).natDegree ((V.num γ).natDegree-D)
   change (V.num γ).natDegree-D ≤V.DG D γ at hdeg
   unfold gap
   omega
 have hswap : ∑ γ∈good,(bad γ).card =
     ∑ i:I,(good.filter fun γ=>hit w S γ i∧(V.num γ).eval (base i)≠0).card:= by
   simp only [bad,card_filter]
   rw [sum_comm]
 have hb : ∑ γ∈good,(bad γ).card≤blockLength*n:= by
   rw [hswap,← index_card,← card_univ,← sum_const_nat (s :=(univ :zJe I))
     (f := fun _=>n) (fun _ _=>rfl)]
   exact sum_le_sum fun i _=>(card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hn i)
 have hs : ∑ γ∈good,V.DG D γ≤v :=
   (sum_le_sum_of_subset (filter_subset _ _)).trans hv
 have hgood:gap D *good.card≤blockLength*n+v := by
   rw [Nat.mul_comm (gap D),← sum_const_nat (s :=good) (f := fun _=>gap D) (fun _ _=>rfl)]
   exact (sum_le_sum fun γ hm=>each γ hm).trans
     (sum_add_distrib.trans_le (Nat.add_le_add hb hs))
 have hp:=card_filter_add_card_filter_not (s :=V.marks) (fun γ=>V.num γ=0)
 change (V.marks.filter fun γ=>V.num γ=0).card+good.card=V.marks.card at hp
 rw [← hp,Nat.mul_add]
 exact (Nat.add_le_add (zBI _ ha) hgood).trans_eq (by ac_rfl)
end
end P5_7_3_5_2
end
section
namespace qxPDCsa
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open cu (L)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation)
open qb0hmCe (CurveModel cLN)
open qFD8jve (sheetPole)
open E7 (CurvePlace)
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
def BoundedAt {E :Type} [Field E] (v :Valuation E ℤᵐ⁰) (g:E[X]) (b:ℤᵐ⁰) :Prop :=
 ∀ j,v (g.coeff j)≤b
def Bound (F:Sheet Cq z S) (g:Cq.E[X]) (n:ℕ) :Prop :=
 ∀ v :CurvePlace L Cq.E,BoundedAt v.value g (WithZero.exp ((n*sheetPole v.value F.f :ℕ) :ℤ))
def reduce {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] LaurentSeries L) (g:E[X]) :L[X] :=
 (cLN a 0 (z1z g)).coeff 0
def specialize (F:Sheet Cq z S) {γ:K} (h:γ∈F.marks) :L[X][X] :=
 cLN (F.atPlace γ h) 0 F.f
def contentAt (F:Sheet Cq z S) {γ:K} (h:γ∈F.marks) :L[X] :=
 (specialize F h).content
def discDegree (D d W:ℕ) :ℕ:=(2*d-2)*W-d*(d-1)*D
def finiteRef (F:Sheet Cq z S) (a :L) :Cq.E[X] :=
 F.f.eval (z1z (algebraMap L Cq.E a))
def Zq (F:Sheet Cq z S) (D:ℕ) :Cq.E[X][X] :=
 let w:=F.f.support.sup fun i=>(F.f.coeff i).natDegree+i*D
 F.f.sum fun i g=>monomial i (g.reflect (w-i*D))
def infinityRef (F:Sheet Cq z S) (D:ℕ) (a :L) :Cq.E[X] :=
 (Zq F D).eval (z1z (algebraMap L Cq.E a))
structure References {F:Sheet Cq z S} (V:Variation F) (D W:ℕ) where
 a :Fin 2→L
 b:Fin 2→L
 finite_distinct :zq4 a
 infinity_distinct :zq4 b
 finite_ne : ∀ i,finiteRef F (a i)≠0
 finite_degree : ∀ i,(finiteRef F (a i)).natDegree≤W
 finite_bound : ∀ i,Bound F (finiteRef F (a i)) 1
 infinity_ne : ∀ i,(infinityRef F D (b i)).coeff 0≠0
 infinity_bound : ∀ i,Bound F (infinityRef F D (b i)) 1
 avoids : ∀ γ∈V.marks,∀ i,cu.j9 (S γ)≠z1z (a i)
 content_order : ∀ γ (hγ:γ∈V.marks) x,(V.den γ).eval x=0 → ∀ i,
   (reduce (F.atPlace γ (V.Bp hγ)) (finiteRef F (a i))).rootMultiplicity x =
     (contentAt F (V.Bp hγ)).rootMultiplicity x
structure RadicalOf {E :Type} [Field E] (g r :E[X]) :Prop where
 leading:r.leadingCoeff=g.leadingCoeff
 separable :r.Separable
 dvd:r∣g
 power : ∃ n:ℕ,g∣r^n
 bound : ∀ (v :Valuation E ℤᵐ⁰) (b:ℤᵐ⁰),BoundedAt v g b→BoundedAt v r b
def UnitAt (F:Sheet Cq z S) (γ:K) (c:Cq.E) :Prop :=
 (F.place γ).value c=1
def Good {F:Sheet Cq z S} {V:Variation F} {D W:ℕ}
    (A:References V D W) (γ:K) :Prop :=
  UnitAt F γ F.f.discr.leadingCoeff ∧
    (∀ i,UnitAt F γ (finiteRef F (A.a i)).leadingCoeff) ∧
    (∀ i,UnitAt F γ ((infinityRef F D (A.b i)).coeff 0))
def gcdDegree (a b:L[X]) :ℕ:=(GCDMonoid.gcd a b).natDegree
end
end qxPDCsa
end
end
