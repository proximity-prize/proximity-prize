import ProximityPrize.SubmissionLower.AZ
namespace ProximityPrize.SubmissionLower.AlignmentScalarListBridge
noncomputable section Proofs
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
def ZeroCoordinateBound (C:LinearCode ι F) (w:ℕ):Prop:=
 ∀ c:ι → F,c∈C → c≠0 →
   (Finset.univ.filter (fun i => c i=0)).card ≤ w
theorem eq_of_agreement_on_large_support
   (C:LinearCode ι F) (w:ℕ) (hzero:ZeroCoordinateBound C w)
   (c d:ι → F) (hc:c∈C) (hd:d∈C)
   (A:Finset ι) (hA:w < A.card)
   (hagree:∀ i∈A,c i=d i):c=d:=by
 classical
 by_contra hne
 have hbound:=hzero (c-d) (C.sub_mem hc hd) (sub_ne_zero.mpr hne)
 have hsub:A ⊆ Finset.univ.filter (fun i => (c-d) i=0):=by
   intro i hi
   refine Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
   change c i-d i=0
   exact sub_eq_zero.mpr (hagree i hi)
 have hcard:=Finset.card_le_card hsub
 omega
theorem seed_indexed_list_card_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (u:ι → F) (S:Finset F) (selected:F → ι → F)
   (A:F → Finset ι)
   (hinj:Set.InjOn selected S)
   (hcode:∀ seed∈S,selected seed∈C)
   (hcard:∀ seed∈S,Fintype.card ι-e ≤ (A seed).card)
   (hagree:∀ seed∈S,∀ i∈A seed,selected seed i=u i):
   S.card ≤ B:=by
 classical
 by_contra hnot
 have hlarge:B < S.card:=Nat.lt_of_not_ge hnot
 let U:Fin 2 → ι → F:=![u,0]
 have hprojected:∀ seed∈S,
     LinearCode.projectedWord (fun i => U 0 i+seed*U 1 i) (A seed)∈
       LinearCode.projectedCodeSubmod C (A seed):=by
   intro seed hseed
   rw [LinearCode.mem_projectedCodeSubmod_iff]
   refine ⟨selected seed,hcode seed hseed,?_⟩
   funext i
   change u i.1+seed*0=selected seed i.1
   simpa only [mul_zero,add_zero] using (hagree seed hseed i.1 i.2).symm
 obtain ⟨p,hp,T,hTS,hTcard,heq⟩:=
   halign U S A hlarge hcard hprojected
 obtain ⟨seed,hseed,hcommon⟩:=
   ProximityPrize.SubmissionLower.exists_common_affine_set U p T A e hTcard
     (fun z hz => hcard z (hTS hz)) heq
 have hdir:p 1=0:=by
   apply eq_of_agreement_on_large_support C w hzero (p 1) 0 (hp 1) C.zero_mem
     (A seed) (hgap.trans_le (hcard seed (hTS hseed)))
   intro i hi
   have hv:=(hcommon i hi).2
   change 0=p 1 i at hv
   exact hv.symm
 have hselected:∀ z∈T,selected z=p 0:=by
   intro z hz
   apply eq_of_agreement_on_large_support C w hzero (selected z) (p 0)
     (hcode z (hTS hz)) (hp 0) (A z) (hgap.trans_le (hcard z (hTS hz)))
   intro i hi
   have hv:=heq z hz i hi
   change u i+z*0=p 0 i+z*p 1 i at hv
   have hdi:p 1 i=0:=congrFun hdir i
   have huv:u i=p 0 i:=by
     simpa only [hdi,mul_zero,add_zero] using hv
   exact (hagree z (hTS hz) i hi).trans huv
 have hsmall:T.card ≤ 1:=by
   apply Finset.card_le_one.mpr
   intro z hz t ht
   exact hinj (hTS hz) (hTS ht) ((hselected z hz).trans (hselected t ht).symm)
 omega
theorem finite_list_card_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (u:ι → F) (L:Finset (ι → F))
   (hcode:∀ c∈L,c∈C)
   (hclose:∀ c∈L,
     Fintype.card ι-e ≤ (Finset.univ.filter (fun i => c i=u i)).card):
   L.card ≤ B:=by
 classical
 letI:DecidableEq (ι → F):=Classical.decEq (ι → F)
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩:=
   Finset.exists_subset_card_eq (show B+1 ≤ L.card by omega)
 have hsize:Fintype.card ↥D ≤ Fintype.card F:=by
   rw [Fintype.card_coe,hDcard]
   omega
 let toSeed:↥D → F:=fun d =>
   (Fintype.equivFin F).symm
     ⟨(Fintype.equivFin ↥D d).val,
       lt_of_lt_of_le (Fintype.equivFin ↥D d).isLt hsize⟩
 have htoSeed:Function.Injective toSeed:=by
   intro c d heq
   apply (Fintype.equivFin ↥D).injective
   apply Fin.ext
   have hfin:=(Fintype.equivFin F).symm.injective heq
   exact congrArg (fun z:Fin (Fintype.card F) => z.val) hfin
 let S:Finset F:=Finset.univ.image toSeed
 have hScard:S.card=D.card:=by
   change (Finset.univ.image toSeed).card=D.card
   rw [Finset.card_image_of_injective _ htoSeed,Finset.card_univ,
     Fintype.card_coe]
 have hex (seed:F) (hseed:seed∈S):∃ d:↥D,toSeed d=seed:=by
   obtain ⟨d,_,hd⟩:=Finset.mem_image.mp hseed
   exact ⟨d,hd⟩
 let chosen:(seed:F) → seed∈S → ↥D:=
   fun seed hseed => Classical.choose (hex seed hseed)
 have hchosen (seed:F) (hseed:seed∈S):
     toSeed (chosen seed hseed)=seed:=Classical.choose_spec (hex seed hseed)
 let selected:F → ι → F:=fun seed =>
   if hseed:seed∈S then (chosen seed hseed).val else 0
 have hselected (seed:F) (hseed:seed∈S):
     selected seed=(chosen seed hseed).val:=by
   dsimp only [selected]
   exact dif_pos hseed
 have hmem (seed:F) (hseed:seed∈S):selected seed∈L:=by
   have hh:=hDL (chosen seed hseed).property
   simpa only [selected,dif_pos hseed] using hh
 have hinj:Set.InjOn selected S:=by
   intro seed hseed other hother heq
   have hd:chosen seed hseed=chosen other hother:=by
     apply Subtype.ext
     exact (hselected seed hseed).symm.trans (heq.trans (hselected other hother))
   exact (hchosen seed hseed).symm.trans
     ((congrArg toSeed hd).trans (hchosen other hother))
 let A:F → Finset ι:=fun seed =>
   Finset.univ.filter (fun i => selected seed i=u i)
 have hbounded:S.card ≤ B:=seed_indexed_list_card_le C e w B hzero hgap
   halign u S selected A hinj
   (fun seed hseed => hcode _ (hmem seed hseed))
   (fun seed hseed => hclose _ (hmem seed hseed))
   (fun seed _ i hi => (Finset.mem_filter.mp hi).2)
 rw [hScard,hDcard] at hbounded
 omega
def scalarList (C:LinearCode ι F) (u:ι → F) (e:ℕ):
   Finset (ι → F):=by
 classical
 exact Finset.univ.filter (fun c => c∈C∧
   Fintype.card ι-e ≤ (Finset.univ.filter (fun i => c i=u i)).card)
theorem scalarList_card_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F) (u:ι → F):
   (scalarList C u e).card ≤ B:=by
 classical
 apply finite_list_card_le C e w B hzero hgap halign hfield u (scalarList C u e)
 · intro c hc
   exact (Finset.mem_filter.mp hc).2.1
 · intro c hc
   exact (Finset.mem_filter.mp hc).2.2
end Proofs
end ProximityPrize.SubmissionLower.AlignmentScalarListBridge
