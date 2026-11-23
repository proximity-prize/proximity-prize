import ProximityPrize.SubmissionLower.ZvFqJTb
import ProximityPrize.SubmissionLower.Z55PrLe
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qZhm2wb
noncomputable section
open Polynomial Finset q82zwcd
open P5 (K I)
open cu (L FX)
open DP (Z7)
open Cu (sQ)
open qK3TPae (regular)
open qb0hmCe (cLN zD)
open q1kuFjb (AtSite coeffIntegral expansion_coeff integralSeries residue fWQ reduced_pair)
open P5_7_7 (phys)
open scoped Classical WithZero
open private reduced_degree from ProximityPrize.SubmissionLower.ZvFqJTb
private theorem scale_expansion {E :Type} [Field E] [Algebra L E]
   (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (u:E)
   (hu: (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a u)≤1)
   (hf : ∀ i j,(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
     (a ((f.coeff i).coeff j))≤1) :
   cLN a 0 (C (C u)*f)=C (C ((a u).coeff 0))*cLN a 0 f := by
 apply Polynomial.ext
 intro i
 apply Polynomial.ext
 intro j
 simp only [expansion_coeff,coeff_C_mul,map_mul]
 let b:=integralSeries (a u) hu
 let c:=integralSeries (a ((f.coeff i).coeff j)) (hf i j)
 have h:=map_mul residue b c
 simp only [fWQ,Subring.coe_mul] at h
 exact h
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
 {q:sQ} {z :K→K} {J:WordChart D w U s}
private def site (F:DualSheet J q z) (γ:K) (hγ:γ∈regular q z U) :
  AtSite F.curve (Z7 (z γ)) where
 map :=F.atPlace γ (mem_filter.mp hγ).1
 place :=F.place γ
 value :=F.value γ (mem_filter.mp hγ).1
 arc := by
  obtain ⟨a,ha,hs,hd⟩:=F.arc γ (mem_filter.mp hγ).1
  exact ⟨a,ha,hs,hd (mem_filter.mp hγ).2⟩
private theorem scaled_good (F:DualSheet J q z) (γ:K) (hγ:γ∈U)
   (hf :coeffIntegral (F.place γ).value F.f)
   (hs : ((cLN (F.atPlace γ hγ) 0 F.f).map phys).Separable) :
   let f :=cLN (F.atPlace γ hγ) 0 (C (C (F.scale γ:F.curve.E))*F.f)
   f.natDegree=F.d∧(f.map phys).Separable := by
 let a :=F.atPlace γ hγ
 let u:F.curve.E :=F.scale γ
 have hu:=F.integral γ hγ F.d (F.f.coeff F.d).natDegree
 rw [coeff_natDegree,F.normalized,mul_one,F.value γ hγ] at hu
 let b:=(a u).coeff 0
 let g:=cLN a 0 F.f
 have h:=scale_expansion a F.f u hu (fun i j=>(F.value γ hγ _).symm.trans_le (hf i j))
 have hb:b≠0:= by
   intro hzero
   apply F.reduction_ne γ hγ
   rw [h,show (a u).coeff 0=0 from hzero,C_0,C_0,zero_mul]
 have hdeg:g.natDegree=F.d :=
   (natDegree_map_eq_of_injective (IsFractionRing.injective L[X] FX) g).symm.trans
     (reduced_degree a F.normalized)
 change (cLN a 0 (C (C u)*F.f)).natDegree=F.d ∧
   ((cLN a 0 (C (C u)*F.f)).map phys).Separable
 rw [h,natDegree_C_mul (C_ne_zero.mpr hb),hdeg,Polynomial.map_mul,map_C]
 exact ⟨rfl,hs.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
   ((map_ne_zero_iff phys (IsFractionRing.injective L[X] FX)).mpr (C_ne_zero.mpr hb))))⟩
theorem proof :q82zwcd.c3:= by
 intro D w U s z q J F hd hp
 let R:=regular q z U
 let A (i:R) :=site F i i.property
 let viable (i:R) :Prop :=
   coeffIntegral (A i).place.value F.f∧((cLN (A i).map 0 F.f).map phys).Separable
 let bad:=(univ :Finset R).filter fun i => ¬ viable i
 let good:=R.filter fun γ => ∃ h:γ∈R,viable ⟨γ,h⟩
 have hkept:good⊆R:=filter_subset _ _
 have hU (γ:K) (hγ:γ∈good) :γ∈U:=(mem_filter.mp (hkept hγ)).1
 have hirr :Irreducible F.f :=
   (F.primitive.irreducible_iff_irreducible_map_fraction_map (K:=FractionRing F.curve.E[X])).mpr
     F.irreducible
 have hdistinct :Set.InjOn (fun i:R=>(A i).place) ((univ :Finset R) :Set R) :=
   fun i _ j _ h=>Subtype.ext (F.distinct (mem_filter.mp i.property).1
     (mem_filter.mp j.property).1 h)
 have hpos :0<F.d:=Nat.lt_of_lt_of_le (by decide :0<3) hd
 have hbad:bad.card≤2*F.d*F.h :=
   qb2k8ya.proof F.curve univ (fun i:R=>Z7 (z i)) A hdistinct
     F.f hirr hpos hp F.normalized
 have hcover :R \ good⊆bad.map (Function.Embedding.subtype _) := by
   intro γ hγ
   obtain ⟨hR,hng⟩:=mem_sdiff.mp hγ
   exact mem_map.mpr ⟨⟨γ,hR⟩,mem_filter.mpr
     ⟨mem_univ _,fun hv=>hng (mem_filter.mpr ⟨hR,hR,hv⟩)⟩,rfl⟩
 have hsep (γ:K) (hγ:γ∈good) :
     let f :=cLN (F.atPlace γ (hU γ hγ)) 0 (C (C (F.scale γ:F.curve.E))*F.f)
     f.natDegree=F.d∧(f.map phys).Separable := by
   obtain ⟨_,hR,hv⟩:=mem_filter.mp hγ
   exact scaled_good F γ (hU γ hγ) hv.1 hv.2
 let τ (γ:K) :FX:=if hγ:γ∈good then
   zD (F.atPlace γ (hU γ hγ)) (C (C (F.scale γ:F.curve.E))*F.f) (J.P γ) (J.Q γ)
   else 0
 choose num den hden hred hfrac using fun γ=>reduced_pair (τ γ)
 refine ⟨{
   good:=good,Bp:=hkept,num :=num,den:=den,
   den_ne := fun γ _=>hden γ,reduced:= fun γ _=>hred γ,
   separable :=hsep,simple := ?_,formula := ?_},?_⟩
 · intro γ hγ
   let f :=cLN (F.atPlace γ (hU γ hγ)) 0 (C (C (F.scale γ:F.curve.E))*F.f)
   have hr : (f.map phys).eval (phys (J.P γ)/phys (J.Q γ))=0:= by
     rw [eval_map]
     exact F.root γ (hU γ hγ)
   have h:=(hsep γ hγ).2.eval₂_derivative_ne_zero (RingHom.id FX)
     (by simpa only [eval₂_id] using hr)
   rw [eval₂_id,derivative_map,eval_map] at h
   exact h
 · intro γ hγ
   exact (hfrac γ).trans (dite_eq_left hγ)
 · exact (card_le_card hcover).trans (by
     rw [card_map]
     exact hbad.trans (Nat.mul_le_mul_right _ (by omega)))
end
end qZhm2wb
