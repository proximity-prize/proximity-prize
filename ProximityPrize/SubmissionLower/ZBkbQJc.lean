import ProximityPrize.SubmissionLower.Z62SyBc
set_option Elab.async false
namespace q1kuFjb
noncomputable section
open Polynomial Finset qQ9yWTb qb0hmCe


open cu (L)
open E7 (CurvePlace axV poleOrder KB Tq Gb)
open agN (a6F b27)
open scoped Classical WithZero
theorem principal {q:Curve} (Cq:CurveModel q) :axV L Cq.E :=
 aFU.of_children bRt.proof
  bRu.proof L Cq.E Cq.curve
theorem AtSite.site_eq_of_place {q:Curve} {Cq:CurveModel q} {s t:Fin 2→L}
   (A:AtSite Cq s) (B:AtSite Cq t) (h:A.place=B.place) :s=t:= by
 funext i
 obtain ⟨a,ha,hsa,_⟩:=A.arc
 obtain ⟨b,hb,hsb,_⟩:=B.arc
 let c:=Cq.seed i-algebraMap L Cq.E (s i)
 have he (W:Cq.E →ₐ[L] LaurentSeries L) (v :PowerSeries L)
     (hv :W (Cq.seed i)=(v :LaurentSeries L)) :
     W c=((v-PowerSeries.C (s i) :PowerSeries L) :LaurentSeries L) := by
   rw [show c=Cq.seed i-algebraMap L Cq.E (s i) from rfl,map_sub,hv,
     W.commutes,PowerSeries.coe_sub,PowerSeries.coe_C,LaurentSeries.algebraMap_apply]
 have hz :A.place.value c≤WithZero.exp (-1) := by
   rw [A.value,he A.map (a i) (ha i),small_valuation,map_sub,hsa,
     PowerSeries.constantCoeff_C,sub_self]
 rw [h,B.value,he B.map (b i) (hb i),small_valuation,map_sub,hsb,
   PowerSeries.constantCoeff_C,sub_eq_zero] at hz
 exact hz.symm
private theorem card_support {ι V:Type} (I:Finset ι) (v :ι→V) (f :V→ℕ)
   (hi:Set.InjOn v (I:Set ι)) (hf :f.HasFiniteSupport)
   (hp : ∀ i∈I,0<f (v i)) :I.card ≤ ∑ᶠ a,f a := by
 classical
 rw [← card_image_of_injOn hi,finsum_eq_sum_of_support_subset _ (s :=hf.toFinset)
   (fun _ ha=>hf.mem_toFinset.mpr ha)]
 have hsub:I.image v⊆hf.toFinset := by
   intro a ha
   obtain ⟨i,hI,rfl⟩:=mem_image.mp ha
   exact hf.mem_toFinset.mpr (Nat.ne_of_gt (hp i hI))
 calc
   _ = ∑ a∈I.image v,1 := by simp
   _ ≤ ∑ a∈I.image v,f a :=sum_le_sum fun a ha=> by
     obtain ⟨i,hI,rfl⟩:=mem_image.mp ha
     exact hp i hI
   _≤_:=sum_le_sum_of_subset hsub
theorem zero_budget {q:Curve} {Cq:CurveModel q} {ι:Type}
  (I:Finset ι) (v :ι→CurvePlace L Cq.E)
  (hv :Set.InjOn v (I:Set ι)) {c:Cq.E} (hc:c≠0) :
  (I.filter fun i=>(v i).value c<1).card ≤ ∑ᶠ w:CurvePlace L Cq.E,poleOrder w.value c:= by
 obtain ⟨_,hz,hp,_⟩:=principal Cq c
 rw [hp]
 refine card_support _ v (fun w=>KB w.value c)
  (hv.mono (fun _ hi=>(mem_filter.mp hi).1)) hz ?_
 intro i hi
 have hlt:=(mem_filter.mp hi).2
 have he :=(WithZero.log_lt_log ((v i).value.ne_zero_iff.mpr hc) one_ne_zero).mpr hlt
 rw [WithZero.log_one] at he
 have hs :0 < -WithZero.log ((v i).value c) := by omega
 change 0<(-WithZero.log ((v i).value c)).toNat
 omega
theorem integral_budget {q:Curve} {Cq:CurveModel q} {ι:Type}
  (I:Finset ι) (v :ι→CurvePlace L Cq.E)
  (hv :Set.InjOn v (I:Set ι)) (f :Cq.E[X][X]) :
  (I.filter fun i => ¬ coeffIntegral (v i).value f).card≤ coeffHeight f := by
 let c (ij:Fin (f.natDegree+1)×Fin ((f.support.sup fun i=>(f.coeff i).natDegree)+1)) :=
  (f.coeff ij.1).coeff ij.2
 change _≤Gb L Cq.E c
 refine card_support _ v (fun w=>Tq w.value c)
  (hv.mono (fun _ hi=>(mem_filter.mp hi).1)) (b27 (principal Cq) c) ?_
 intro a ha
 have hn:=(mem_filter.mp ha).2
 unfold coeffIntegral at hn
 push Not at hn
 obtain ⟨i,j,hij⟩:=hn
 have hne : (f.coeff i).coeff j≠0:= fun hz=> by
  simp [hz] at hij
 have hi:i∈f.support :=mem_support_iff.mpr fun hz=>hne (by simp [hz])
 have hi' : i<f.natDegree+1 :=Nat.lt_succ_of_le (le_natDegree_of_ne_zero (mem_support_iff.mp hi))
 have hj' : j<(f.support.sup fun k=>(f.coeff k).natDegree)+1 :=
  Nat.lt_succ_of_le ((le_natDegree_of_ne_zero hne).trans (le_sup (f := fun k=>(f.coeff k).natDegree) hi))
 have hp:0<poleOrder (v a).value ((f.coeff i).coeff j) :=
  Nat.pos_of_ne_zero fun hz=>(not_le_of_gt hij) ((a6F _ _).mp hz)
 exact hp.trans_le (Finset.le_sup (f := fun k=>poleOrder (v a).value (c k))
  (mem_univ (⟨i,hi'⟩,⟨j,hj'⟩)))
end
end q1kuFjb
