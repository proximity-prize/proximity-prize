import ProximityPrize.SubmissionLower.ZfNZDra
import ProximityPrize.SubmissionLower.ZhlCjsa
import ProximityPrize.SubmissionLower.ZgKNZbc
import ProximityPrize.SubmissionLower.ZK8GpQb
import ProximityPrize.SubmissionLower.ZQBQYdc
import ProximityPrize.SubmissionLower.ZfSxMva
set_option Elab.async false
open _root_ renaming Algebra → zZE, Field → zrb, Function.Surjective → zpX, IsFractionRing.injective → zxb, Nat.lt_succ_of_le → zB1, Nat.sub_zero → zPv, Polynomial.map_dvd → z36, Polynomial.map_injective → zTo, Polynomial.map_mul → zNl, PowerSeries.C → zMG, PowerSeries.constantCoeff → zbO
section
section
set_option backward.isDefEq.respectTransparency false
namespace q85rTDe
noncomputable section
open TrivSqZeroExt Polynomial

open q2TwyLa (PhysicalField)
private abbrev Dual (E :Type) [zrb E] :=TrivSqZeroExt E E
private def aug (E :Type) [zrb E] :Dual E →+* E :=(fstHom ℤ E E).toRingHom
private def Xm {F E :Type} [zrb F] [zrb E] [zZE ℤ F] [zZE F E]
  (D:Derivation ℤ F F) :F →+* Dual E where
 toFun a :=⟨algebraMap F E a,algebraMap F E (D a)⟩
 map_one' := by ext <;> simp
 map_zero' := by ext <;> simp
 map_add' a b:= by ext <;> simp
 map_mul' a b:= by ext <;> simp [D.leibniz,smul_eq_mul,mul_comm]
theorem extend_derivation {F E :Type} [zrb F] [zrb E] [zZE ℤ F] [zZE F E]
   [Algebra.IsSeparable F E] (D:Derivation ℤ F F) :
   ∃ d:Derivation ℤ E E,∀ a :F,d (algebraMap F E a)=algebraMap F E (D a) := by
 let b:=Xm (E :=E) D
 let:zZE F (Dual E) :=b.toAlgebra
 let π:Dual E →ₐ[F] E := { aug E with commutes' := fun _=>rfl }
 have hs :zpX π:= fun a=>⟨inl a,rfl⟩
 have hk :IsNilpotent (RingHom.ker π.toRingHom) := by
   refine ⟨2,?_⟩
   let I:=RingHom.ker π.toRingHom
   change I ^(2 :ℕ) = ⊥
   refine (pow_two I).trans (le_antisymm (Ideal.mul_le.mpr ?_) bot_le)
   intro a ha b hb
   change a.fst=0 at ha
   change b.fst=0 at hb
   rw [Ideal.mem_bot]
   ext <;> simp [ha,hb]
 let:Algebra.FormallyEtale F E :=Algebra.FormallyEtale.of_isSeparable _ _
 let f :=Algebra.FormallySmooth.liftOfSurjective (AlgHom.id F E) π hs hk
 have hf (a :E) : (f a).fst=a :=
   Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id F E) π hs hk a
 let d:E →+ E :=
   { toFun:= fun a=>(f a).snd
     map_zero' := by simp
     map_add' := fun a b=> by simp }
 refine ⟨{ toFun:=d,map_add' := d.map_add,map_smul' := fun n a=>d.map_zsmul n a
           map_one_eq_zero' := by change (f 1).snd=0; simp
           leibniz' := fun a b=> by
             change (f (a*b)).snd=a•(f b).snd+b•(f a).snd
             simp [hf,mul_comm] },?_⟩
 intro a
 exact congrArg snd (f.commutes a)
theorem aNu {R E :Type} [CommRing R] [zrb E] (D:Derivation ℤ E E)
   (f :R →+* E) (a :E) (P Q:R[X])
   (hc : ∀ i,D (f (P.coeff i))=f (Q.coeff i)) :
   D (P.eval₂ f a)= Q.eval₂ f a+P.derivative.eval₂ f a*D a := by
 let n:=max P.natDegree Q.natDegree+1
 have hP:P.natDegree<n:=zB1 (le_max_left _ _)
 have hQ:Q.natDegree<n:=zB1 (le_max_right _ _)
 have hd:P.derivative.eval₂ f a =
     ∑ i∈Finset.range n,f (P.coeff i)*(i:E)*a^(i-1) := by
   simp_rw [derivative_apply,eval₂_sum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,map_mul,map_natCast]
   exact P.sum_over_range' (fun i=> by simp) n hP
 rw [eval₂_eq_sum_range' f hP,eval₂_eq_sum_range' f hQ,hd,map_sum,
   Finset.sum_mul,← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro i _
 rw [D.leibniz,D.leibniz_pow,hc]
 simp only [smul_eq_mul,nsmul_eq_mul]
 ring
variable (B:SeedData) {E :Type} [zrb E] [zZE PhysicalField E]
local instance :zZE B.constants E :=constantsAlgebra B E
end
end q85rTDe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qn3rrcc
noncomputable section
open Polynomial Finset qNu3xvc
open cu (L)
open P5 (K)
open qgbTAnb
open qb0hmCe (cLN)
open qFD8jve (sheetPole)
open E7 (CurvePlace axV poleOrder KB)
open private sum_le_all finite_tuple from ProximityPrize.SubmissionLower.ZG9rwXd
open private resultant_le from ProximityPrize.SubmissionLower.ZexDIsb
open private expansion_linear from ProximityPrize.SubmissionLower.Z4uF8Nb
open private primitive_pair from ProximityPrize.SubmissionLower.ZhlCjsa
open scoped Classical WithZero
variable {E :Type} [zrb E] [zZE L E]
private theorem mark (A:Equation E) (S:Sections A) (hd:A.d = 1)
   (γ:K) (hγ:γ∈S.marks) :
   (S.den γ).natDegree ≤
     KB (S.place γ).value (resultant (A.f.coeff 1) (A.f.coeff 0)) := by
 let ι:=S.atPlace γ hγ
 let a :=A.f.coeff 1
 let b:=A.f.coeff 0
 let a₀:=slice ι 0 a
 let b₀:=slice ι 0 b
 let P:=S.P γ
 let Q:=S.Q γ
 have hQ:=S.denom γ hγ
 have ha :a₀≠0:= by
   intro hz
   have hh:=S.degree γ hγ
   change (cLN ι 0 A.f).natDegree=A.d at hh
   rw [expansion_linear ι 0 hd.le,show slice ι 0 (A.f.coeff 1)=0 from hz,
     map_zero,zero_mul,zero_add,natDegree_C,hd] at hh
   exact Nat.zero_ne_one hh
 have hz :a₀*P+b₀*Q=0:=linear_root ι hd.le hQ (S.root γ hγ)
 have he :a₀*P = -(b₀*Q) :=eq_neg_of_add_eq_zero_left hz
 obtain ⟨G,hGQ⟩:Q∣a₀:=(S.coprime γ hγ).symm.dvd_of_dvd_mul_right
   (he.symm ▸ dvd_neg.mpr (dvd_mul_left Q b₀))
 have hG:G≠0:= fun h=>ha (by simp [hGQ,h])
 have hg:a₀=G*Q:=hGQ.trans (mul_comm _ _)
 have hb:b₀ = -(G*P) := by
   apply mul_right_cancel₀ hQ
   calc
     b₀*Q = -(a₀*P) :=eq_neg_of_add_eq_zero_right hz
     _ = -(G*P)*Q:= by rw [hg,neg_mul,mul_right_comm G Q P]
 have hden:=(fraction_degrees (S.den_ne γ hγ) hG (S.reduced γ hγ)
   ((S.formula γ hγ).trans (linear_tangent ι hd.le hQ hG hg))).1
 let F:=liftSeries ι a
 let H :=liftSeries ι b
 have hF:F.map zbO=a₀:=fWX ι a
 have hH :H.map zbO=b₀:=fWX ι b
 have hdeg:G.natDegree≤a.natDegree :=
   (natDegree_le_of_dvd ⟨Q,hg⟩ ha).trans (degree_extract (by simp) a)
 have hnorm: (normalize G).natDegree=G.natDegree :=natDegree_normalize
 have hdiv :PowerSeries.X^G.natDegree∣resultant F H a.natDegree b.natDegree := by
   simpa only [hnorm,Nat.add_zero] using padded_order F H
     (degree_lift ι a) (degree_lift ι b) (Nat.zero_le _) (Nat.zero_le _)
     (monic_normalize hG) (by rw [hnorm,zPv]; omega)
     (by rw [hF,hg]; exact normalize_dvd_iff.mpr (dvd_mul_right G Q))
     (by rw [hH,hb]; exact dvd_neg.mpr (normalize_dvd_iff.mpr (dvd_mul_right G P)))
     (by simpa only [zPv] using natDegree_map_le.trans (degree_lift ι a))
     (by simpa only [zPv] using natDegree_map_le.trans (degree_lift ι b))
 let g:=resultant a b
 let R:=resultant F H a.natDegree b.natDegree
 have hR:algebraMap (PowerSeries L) (LaurentSeries L) R=ι g:= by
   rw [show R= _ from rfl,← resultant_map_map,
     map_lift ι a (fun i=>(S.value γ hγ _).symm.trans_le ((S.regular γ hγ).1 1 i)),
     map_lift ι b (fun i=>(S.value γ hγ _).symm.trans_le ((S.regular γ hγ).1 0 i)),
     resultant_map_map]
   rfl
 have hv : (S.place γ).value g≤WithZero.exp (-(↑G.natDegree :ℤ)) := by
   rw [S.value γ hγ,← hR]
   exact (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero L R).mpr
     (PowerSeries.X_pow_dvd_iff.mp hdiv)
 have hne :g≠0:=resultant_ne_zero _ _ (primitive_pair A.irreducible hd)
 have hlog:=(WithZero.log_le_iff_le_exp (by simpa using hne)).mpr hv
 change (S.den γ).natDegree≤KB (S.place γ).value g
 unfold KB
 omega
theorem proof :qNu3xvc.c5:= by
 intro E _ _ A S hc hd
 let a :=A.f.coeff 1
 let b:=A.f.coeff 0
 let g:=resultant a b
 let H (v :CurvePlace L E) :=sheetPole v.value A.f
 let P (v :CurvePlace L E) :=poleOrder v.value g
 let zord (v :CurvePlace L E) :=KB v.value g
 have hne :g≠0:=resultant_ne_zero _ _ (primitive_pair A.irreducible hd)
 have divs :axV L E :=aFU.of_children
   bRt.proof bRu.proof L E hc
 obtain ⟨hp,hz,he,_⟩:=divs g
 have hH :H.HasFiniteSupport:=finite_tuple divs _
 have hb (v :CurvePlace L E) :P v≤(a.natDegree+b.natDegree)*H v :=
   Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (by simpa using hne)).2
     (resultant_le v.value A.f a.natDegree b.natDegree))
 have hdeg:a.natDegree+b.natDegree≤2*A.b+A.s := by
   have ha :a≠0:= by
     change A.f.coeff 1≠0
     rw [← hd,← leadingCoeff]
     exact leadingCoeff_ne_zero.mpr A.irreducible.ne_zero
   have h₁:=(A.weight 1).resolve_right ha
   simp only [hd,one_mul] at h₁
   change a.natDegree+A.s≤A.b+A.s at h₁
   rcases A.weight 0 with h₀ | h₀
   · simp only [hd,zero_mul,add_zero,one_mul] at h₀
     change b.natDegree≤A.b+A.s at h₀
     omega
   · have :b.natDegree=0:= by simp [b,h₀]
     omega
 calc
   finitePoles S ≤ ∑ γ∈S.marks,zord (S.place γ) :=sum_le_sum (mark A S hd)
   _ = ∑ v∈S.marks.image S.place,zord v :=(sum_image S.distinct).symm
   _ ≤ ∑ᶠ v,zord v :=sum_le_all _ hz _
   _ = ∑ᶠ v,P v :=he.symm
   _ = ∑ v∈hp.toFinset,P v :=finsum_eq_finsetSum_of_support_subset _
     (fun _ hv=>(Set.Finite.mem_toFinset _).mpr hv)
   _ ≤ ∑ v∈hp.toFinset,(a.natDegree+b.natDegree)*H v :=sum_le_sum fun v _=>hb v
   _≤(a.natDegree+b.natDegree)*A.h:= by
     rw [← mul_sum]
     exact Nat.mul_le_mul_left _ (sum_le_all H hH _)
   _≤(2*A.b+A.s)*A.h:=Nat.mul_le_mul_right _ hdeg
end
end qn3rrcc
end
end
section
section
namespace qoGY3we
noncomputable section
open Polynomial
open cu (L FX)
open P5 (p)
open P5_7_7 (phys)
open qrezXJe (rootEval)
open q2TwyLa (i5 aQ polar diff)
open scoped WithZero
abbrev Series :=PowerSeries FX
abbrev a8p:i5 →+* aQ:=algebraMap _ _
abbrev reduce :i5[X] →+* L[X] :=mapRingHom zbO
def bY (infty :Bool) :i5[X] →+* Series :=
  eval₂RingHom (PowerSeries.map (algebraMap L FX))
    (zMG (if infty then (phys (Polynomial.X:L[X]))⁻¹ else phys Polynomial.X))
def branchPoly (f :i5[X][X]) (r :L) :i5[X] :=
 polar f*f.eval (C (zMG r))
structure Cover where
 f :i5[X][X]
 r :L
 g:i5[X]
 positive :0<f.natDegree
 small:f.natDegree<p
 branch_ne :branchPoly f r≠0
 branch_unit :IsUnit (branchPoly f r).leadingCoeff
 radical_unit :IsUnit g.leadingCoeff
 radical_sep: (g.map a8p).Separable
 radical_dvd:g.map a8p∣(branchPoly f r).map a8p
 radical_pow : ∃ n:ℕ,(branchPoly f r).map a8p∣(g.map a8p)^n
 radical_small:g.natDegree<p
abbrev Away (A:Cover) :=Localization.Away A.g.reverse
def physDiff (f :i5[X][X]) :i5[X][X] :=
 f.sum fun i b=>monomial i b.derivative
def seedTangent (f :i5[X][X]) (P:L[X]) :FX :=
 -(rootEval ((diff f).map reduce) P/rootEval (f.map reduce).derivative P)
structure LocalRoot (f :i5[X][X]) (r :L) (P:L[X]) where
 y :Series
 root :f.eval₂ (bY false) y=0
 reduce_y :zbO y=phys P
 simple :IsUnit (f.derivative.eval₂ (bY false) y)
 ref_unit :IsUnit (y-PowerSeries.C (phys (C r)))
 logSeed :Series
 logPhys :Series
 seed_eq :logSeed*(y-PowerSeries.C (phys (C r)))*f.derivative.eval₂ (bY false) y =
   -((diff f).eval₂ (bY false) y)
 phys_eq :logPhys*(y-PowerSeries.C (phys (C r)))*f.derivative.eval₂ (bY false) y =
   -((physDiff f).eval₂ (bY false) y)
 seed_res :zbO logSeed*phys (P - C r)=seedTangent f P
 phys_res :zbO logPhys*phys (P - C r)=phys P.derivative
def TameLog:Prop :=
  ∀ {K M:Type} [zrb K] [zrb M] [zZE K M] [Module.Finite K M] [CharP K p],
    Module.finrank K M<p →
    ∀ (v :Valuation K ℤᵐ⁰) (w:Valuation M ℤᵐ⁰) (e :ℕ)
      (δ₀:Derivation ℤ K K) (δ:Derivation ℤ M M),
      zpX v→zpX w →
      0<e→(∀ z,w (algebraMap K M z)=v z^e) →
      (∀ z,δ (algebraMap K M z)=algebraMap K M (δ₀ z)) →
      (∀ z,v z≤1→v (δ₀ z)≤1) →
      ∀ u:M,u≠0 →
      ((∀ z,v z<1→v (δ₀ z)<1)∨(e=1∧w u=1)) →
      w (δ u/u)≤1
end
end qoGY3we
end
section
set_option backward.isDefEq.respectTransparency false
namespace qoGY3we
noncomputable section
open Polynomial
open cu (L FX)
open P5 (p)
open P5_7_7 (phys)
open qrezXJe (branch residuePoly rootEval)
open qb0hmCe (cLN)
open q2TwyLa (i5 aQ lift integral polar polar_map diff)
open scoped WithZero
open private cXH lift_map seed_reduce from ProximityPrize.SubmissionLower.ZQBQYdc
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
private theorem lifted_lc {E :Type} [zrb E] [zZE L E]
  (a :E →ₐ[L] aQ) {F:i5[X]} {f :E[X]}
  (h:F.map a8p=f.map a.toRingHom) :
  a8p F.leadingCoeff=a f.leadingCoeff := by
 change (algebraMap i5 aQ) F.leadingCoeff=a.toRingHom f.leadingCoeff
 simpa only [leadingCoeff_map_of_injective (zxb i5 aQ),
  leadingCoeff_map_of_injective a.injective] using congrArg leadingCoeff h
private theorem unit_of_value {u:i5} (h: (Valued.v :Valuation aQ ℤᵐ⁰) (a8p u)=1) :
  IsUnit u:= by
 apply PowerSeries.isUnit_iff_constantCoeff.mpr
 apply isUnit_iff_ne_zero.mpr
 intro hz
 have hl:=(q1kuFjb.small_valuation u).2 hz
 change (Valued.v :Valuation aQ ℤᵐ⁰) (a8p u)≤WithZero.exp (-1) at hl
 rw [h,← WithZero.exp_zero,WithZero.exp_le_exp] at hl
 omega
theorem cover {E :Type} [zrb E] [zZE L E]
    (a :E →ₐ[L] aQ) (f :E[X][X]) (r :L) (G:E[X])
    (hf :integral a f) (hG : ∀ j,(Valued.v :Valuation aQ ℤᵐ⁰) (a (G.coeff j))≤1)
    (hp:0<f.natDegree) (hd:f.natDegree<p) (hb:branch f r≠0)
    (hl:G.leadingCoeff=(branch f r).leadingCoeff) (hs :G.Separable)
    (hg:G∣branch f r) (hn : ∃ n:ℕ,branch f r∣G^n) (hm:G.natDegree<p)
    (hu: (Valued.v :Valuation aQ ℤᵐ⁰) (a G.leadingCoeff)=1) :
    ∃ A:Cover,A.r=r∧A.f.map reduce=cLN a 0 f ∧
      (diff A.f).map reduce=cLN a 1 f∧reduce A.g=residuePoly a G:= by
  let F:=lift a f hf
  have hC:integral a (C G) := by
    intro i j
    by_cases hi:i=0
    · simpa [hi] using hG j
    · simp [coeff_C,hi]
  let H :=lift a (C G) hC
  let g:=H.coeff 0
  have hFm:F.map (mapRingHom a8p)=f.map (mapRingHom a.toRingHom) :=lift_map a f hf
  have hgm:g.map a8p=G.map a.toRingHom:= by
    simpa only [g,coeff_map,coe_mapRingHom,coeff_C_zero] using
      congrArg (fun q:aQ[X][X]=>q.coeff 0) (lift_map a (C G) hC)
  have hbmap : (branchPoly F r).map a8p=(branch f r).map a.toRingHom:= by
    rw [branchPoly,branch,zNl,zNl]
    congr 1
    · rw [polar_map _ (zxb i5 aQ),hFm]
      exact (polar_map a.toRingHom a.injective f).symm
    · have heval {R S:Type} [CommRing R] [CommRing S] (k :R →+* S)
          (q:R[X][X]) (z :R[X]) :
          (q.eval z).map k=(q.map (mapRingHom k)).eval (z.map k) := by
        rw [eval_map]
        exact (eval₂_hom (f :=mapRingHom k) (p:=q) z).symm
      rw [heval,heval,hFm]
      congr 1
      simp only [map_C]
      congr 1
      change a8p (zMG r)=a (algebraMap L E r)
      rw [a.commutes r,LaurentSeries.algebraMap_apply]
      exact PowerSeries.coe_C r
  have hFd:F.natDegree=f.natDegree := calc
    _=(F.map (mapRingHom a8p)).natDegree :=
      (natDegree_map_eq_of_injective (zTo _ (zxb i5 aQ)) F).symm
    _ = _:=hFm ▸ natDegree_map_eq_of_injective (zTo _ a.injective) f
  have hdg:g.natDegree=G.natDegree := calc
    _=(g.map a8p).natDegree :=(natDegree_map_eq_of_injective (zxb i5 aQ) g).symm
    _ = _:=hgm ▸ natDegree_map_eq_of_injective a.injective G
  have hgu:IsUnit g.leadingCoeff :=
    unit_of_value ((congrArg Valued.v (lifted_lc a hgm)).trans hu)
  have hbu:IsUnit (branchPoly F r).leadingCoeff :=
    unit_of_value ((congrArg Valued.v (lifted_lc a hbmap)).trans (hl ▸ hu))
  have hB:branchPoly F r≠0 :=
    fun hz=>hb ((zTo _ a.injective) (by simpa [hz] using hbmap.symm))
  refine ⟨⟨F,r,g,hFd ▸ hp,hFd ▸ hd,hB,hbu,hgu,hgm ▸ hs.map,?_,?_,hdg ▸ hm⟩,
    rfl,(seed_reduce a f hf).1,(seed_reduce a f hf).2,?_⟩
  · rw [hgm,hbmap]
    exact z36 _ hg
  · obtain ⟨n,hn⟩:=hn
    exact ⟨n,by simpa only [hbmap,hgm,Polynomial.map_pow] using z36 a.toRingHom hn⟩
  · apply Polynomial.ext
    intro j
    simp only [reduce,coe_mapRingHom,coeff_map]
    rw [residuePoly,sum_coeff _ (by simp)]
    have h:=cXH a (C G) hC 0 j
    rw [coeff_C_zero] at h
    exact (q1kuFjb.power_residue _ _ h.symm).symm
theorem radical_coeff (A:Cover) : (reduce A.g.reverse).coeff 0≠0:= by
 rw [coe_mapRingHom,coeff_map,coeff_zero_reverse]
 exact (A.radical_unit.map zbO).ne_zero
private theorem branch_reduce_ne (A:Cover) :reduce (branchPoly A.f A.r)≠0:= by
 intro hz
 have h:=congrArg (fun q:L[X]=>q.coeff (branchPoly A.f A.r).natDegree) hz
 have hu:=(A.branch_unit.map zbO).ne_zero
 simp only [reduce,coe_mapRingHom,coeff_map,coeff_natDegree,coeff_zero] at h
 exact hu h
theorem mark_guards (A:Cover) (P:L[X]) (hroot :rootEval (A.f.map reduce) P=0) :
   rootEval (A.f.map reduce).derivative P≠0∧P - C A.r≠0:= by
 let k :=phys.comp reduce
 have hb:k (branchPoly A.f A.r)≠0 :=
   (map_ne_zero_iff phys (zxb L[X] FX)).2 (branch_reduce_ne A)
 have hb' : k (polar A.f)*k (A.f.eval (C (zMG A.r)))≠0:= by
   simpa only [branchPoly,map_mul] using hb
 have hr :A.f.eval₂ k (phys P)=0:= by
   simpa only [rootEval,eval₂_map] using hroot
 constructor
 · intro hs
   have hd:A.f.derivative.eval₂ k (phys P)=0:= by
     simpa only [rootEval,derivative_map,eval₂_map] using hs
   obtain ⟨a,b,_,_,he⟩:=exists_mul_add_mul_eq_C_resultant A.f A.f.derivative
     (m:=A.f.natDegree) (n:=A.f.natDegree - 1) le_rfl (by have :=natDegree_derivative_lt A.positive.ne'; omega) (Or.inl A.positive.ne')
   have hh:=congrArg (eval₂RingHom k (phys P)) he
   exact (mul_ne_zero_iff.mp hb').1 (by
     simpa only [coe_eval₂RingHom,map_add,map_mul,eval₂_C,hr,hd,zero_mul,zero_add,polar] using hh.symm)
 · intro hp
   have hh:=sub_eq_zero.mp hp
   rw [hh,← show k (C (zMG A.r))=phys (C A.r) by simp [k,reduce],eval₂_hom] at hr
   exact (mul_ne_zero_iff.mp hb').2 hr
end
end qoGY3we
end
end
