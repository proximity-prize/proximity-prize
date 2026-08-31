import ProximityPrize.SubmissionLower.H6
namespace ProximityPrize.SubmissionLower.RCN018
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section DraftProofs
section RadiusCell
variable {ι A:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [DecidableEq A]
theorem agreement_card_ge_of_closeCodewordsRel
   (C:Set (ι → A)) (y c:ι → A) (δ:ℝ) (e:ℕ)
   (hcell:δ*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ))
   (hc:c∈Code.closeCodewordsRel C y δ):
   Fintype.card ι-e ≤
     (Finset.univ.filter (fun i => c i=y i)).card:=by
 classical
 have hball:=(Code.mem_closeCodewordsRel_iff.mp hc).2
 simp only [Code.relHammingDist_coe] at hball
 have hn:(0:ℝ) < (Fintype.card ι:ℝ):=by
   exact_mod_cast Fintype.card_pos
 have hdistR:(hammingDist y c:ℝ) < ((e+1:ℕ):ℝ):=
   ((div_le_iff₀ hn).mp hball).trans_lt hcell
 have hdist:hammingDist y c ≤ e:=by
   have hlt:hammingDist y c < e+1:=by exact_mod_cast hdistR
   omega
 have hagree:Code.agree c y+hammingDist y c=Fintype.card ι:=by
   rw [hammingDist_comm]
   exact Code.agree_add_hammingDist (u:=c) (v:=y)
 change Fintype.card ι-e ≤ Code.agree c y
 omega
end RadiusCell
theorem radius_cell_of_floor_le (δ:ℝ) (n e:ℕ)
   (hfloor:⌊δ*(n:ℝ)⌋₊ ≤ e):
   δ*(n:ℝ) < ((e+1:ℕ):ℝ):=by
 have hf:(⌊δ*(n:ℝ)⌋₊:ℝ) ≤ (e:ℝ):=by exact_mod_cast hfloor
 calc
   δ*(n:ℝ) < (⌊δ*(n:ℝ)⌋₊:ℝ)+1:=Nat.lt_floor_add_one _
   _ ≤ (e:ℝ)+1:=by linarith
   _=((e+1:ℕ):ℝ):=by simp only [Nat.cast_add,Nat.cast_one]
theorem rational_radius_cell (num den n e:ℕ) (hden:0 < den)
   (hcross:num*n < (e+1)*den):
   ((num:ℝ)/(den:ℝ))*(n:ℝ) < ((e+1:ℕ):ℝ):=by
 have hdenR:(0:ℝ) < (den:ℝ):=by exact_mod_cast hden
 calc
   ((num:ℝ)/(den:ℝ))*(n:ℝ)=
       ((num*n:ℕ):ℝ)/(den:ℝ):=by push_cast;ring
   _ < ((e+1:ℕ):ℝ):=(div_lt_iff₀ hdenR).mpr (by exact_mod_cast hcross)
section GenericCode
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
theorem interleaved_lambda_le
   (C:LinearCode ι F) (r e w B:ℕ)
   (hzero:RCN020.ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (hseparation:(r-1)*(B+1).choose 2 < Fintype.card F)
   (δ:ℝ)
   (hcell:δ*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     ((C^⋈ (Fin r):ModuleCode ι F (Fin r → F)):Set (ι → Fin r → F))
     δ ≤ (B:ℕ∞):=by
 classical
 apply Code.Lambda_le_of_forall_finset_card_le
 intro y T hT
 apply RCN019.interleaved_finite_list_card_le
   C e w B hzero hgap halign hfield hseparation y T
 · intro c hc j
   have hcode:=(Code.mem_closeCodewordsRel_iff.mp (hT c hc)).1
   exact (Code.mem_moduleInterleavedCode_iff F F (Fin r) ι C c).mp hcode j
 · intro c hc
   exact agreement_card_ge_of_closeCodewordsRel _ y c δ e hcell (hT c hc)
def sixteenIndexEquiv:Fin 2 × Fin 8 ≃ Fin 16:=finProdFinEquiv
def flattenSymbol (v:Fin 2 → Fin 8 → F) (j:Fin 16):F:=
 v (sixteenIndexEquiv.symm j).1 (sixteenIndexEquiv.symm j).2
def unflattenSymbol (v:Fin 16 → F) (a:Fin 2) (b:Fin 8):F:=
 v (sixteenIndexEquiv (a,b))
theorem unflatten_flattenSymbol (v:Fin 2 → Fin 8 → F):
   unflattenSymbol (flattenSymbol v)=v:=by
 funext a b
 simp only [unflattenSymbol,flattenSymbol,Equiv.symm_apply_apply]
theorem flatten_unflattenSymbol (v:Fin 16 → F):
   flattenSymbol (unflattenSymbol v)=v:=by
 funext j
 change v (sixteenIndexEquiv (sixteenIndexEquiv.symm j))=v j
 rw [Equiv.apply_symm_apply]
def squaredEightSymbolEquiv:(Fin 2 → Fin 8 → F) ≃ (Fin 16 → F) where
 toFun:=flattenSymbol
 invFun:=unflattenSymbol
 left_inv:=unflatten_flattenSymbol
 right_inv:=flatten_unflattenSymbol
def flattenWord (v:ι → Fin 2 → Fin 8 → F):ι → Fin 16 → F:=
 fun i => squaredEightSymbolEquiv (v i)
theorem flattenWord_injective:
   Function.Injective (flattenWord:(ι → Fin 2 → Fin 8 → F) → ι → Fin 16 → F):=by
 intro v u h
 funext i
 exact squaredEightSymbolEquiv.injective (congrFun h i)
theorem flattenWord_agreement_iff
   (v u:ι → Fin 2 → Fin 8 → F) (i:ι):
   flattenWord v i=flattenWord u i ↔ v i=u i:=by
 constructor
 · intro hh
   change (squaredEightSymbolEquiv (F:=F)) (v i)=
     (squaredEightSymbolEquiv (F:=F)) (u i) at hh
   exact (squaredEightSymbolEquiv (F:=F)).injective hh
 · intro hh
   change (squaredEightSymbolEquiv (F:=F)) (v i)=
     (squaredEightSymbolEquiv (F:=F)) (u i)
   exact congrArg (squaredEightSymbolEquiv (F:=F)) hh
theorem flattenWord_agreement_card (v u:ι → Fin 2 → Fin 8 → F):
   (Finset.univ.filter (fun i => flattenWord v i=flattenWord u i)).card=
     (Finset.univ.filter (fun i => v i=u i)).card:=by
 classical
 congr 1
 ext i
 simp only [Finset.mem_filter,flattenWord_agreement_iff]
theorem squared_eight_rows
   (C:LinearCode ι F) (v:ι → Fin 2 → Fin 8 → F)
   (hv:v∈((C^⋈ (Fin 8))^⋈ (Fin 2):
     ModuleCode ι F (Fin 2 → Fin 8 → F))):
   ∀ a:Fin 2,∀ b:Fin 8,(fun i => v i a b)∈C:=by
 intro a b
 have houter:=
   (Code.mem_moduleInterleavedCode_iff F (Fin 8 → F) (Fin 2) ι
     (C^⋈ (Fin 8)) v).mp hv a
 exact (Code.mem_moduleInterleavedCode_iff F F (Fin 8) ι C _).mp houter b
theorem squared_eight_lambda_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:RCN020.ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (hseparation:15*(B+1).choose 2 < Fintype.card F)
   (δ:ℝ)
   (hcell:δ*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     (((C^⋈ (Fin 8))^⋈ (Fin 2):ModuleCode ι F (Fin 2 → Fin 8 → F)):
       Set (ι → Fin 2 → Fin 8 → F)) δ ≤ (B:ℕ∞):=by
 classical
 letI:DecidableEq (ι → Fin 2 → Fin 8 → F):=Classical.decEq _
 letI:DecidableEq (ι → Fin 16 → F):=Classical.decEq _
 apply Code.Lambda_le_of_forall_finset_card_le
 intro y T hT
 let projected:Finset (ι → Fin 16 → F):=T.image flattenWord
 have hinj:Set.InjOn flattenWord (T:Set (ι → Fin 2 → Fin 8 → F)):=
   fun _ _ _ _ hh => flattenWord_injective hh
 have hcard:projected.card=T.card:=Finset.card_image_of_injOn hinj
 have hrows:∀ v∈projected,∀ j:Fin 16,(fun i => v i j)∈C:=by
   intro v hv j
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   have hcode:=(Code.mem_closeCodewordsRel_iff.mp (hT c hc)).1
   change (fun i => c i (sixteenIndexEquiv.symm j).1
     (sixteenIndexEquiv.symm j).2)∈C
   exact squared_eight_rows C c hcode _ _
 have hclose:∀ v∈projected,
     Fintype.card ι-e ≤
       (Finset.univ.filter (fun i => v i=flattenWord y i)).card:=by
   intro v hv
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   rw [flattenWord_agreement_card]
   exact agreement_card_ge_of_closeCodewordsRel _ y c δ e hcell (hT c hc)
 have hbound:=RCN019.interleaved_finite_list_card_le
   (r:=16) C e w B hzero hgap halign hfield hseparation
   (flattenWord y) projected hrows hclose
 rwa [hcard] at hbound
theorem squared_eight_lambda_le_of_floor
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:RCN020.ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (hseparation:15*(B+1).choose 2 < Fintype.card F)
   (δ:ℝ) (hfloor:⌊δ*(Fintype.card ι:ℝ)⌋₊ ≤ e):
   Code.Lambda
     (((C^⋈ (Fin 8))^⋈ (Fin 2):ModuleCode ι F (Fin 2 → Fin 8 → F)):
       Set (ι → Fin 2 → Fin 8 → F)) δ ≤ (B:ℕ∞):=
 squared_eight_lambda_le C e w B hzero hgap halign hfield hseparation δ
   (radius_cell_of_floor_le δ (Fintype.card ι) e hfloor)
end GenericCode
theorem irs_zeroCoordinateBound:
   RCN020.ZeroCoordinateBound IRSProfile.baseCode 131071:=by
 classical
 intro c hc hne
 have hdist:=Code.minDist_le_dist
   (C:=(IRSProfile.baseCode:Set (IRSProfile.Index → IRSProfile.Field)))
   hc IRSProfile.baseCode.zero_mem hne
 rw [IRSProfile.baseMinDistance] at hdist
 have hagree:=Code.agree_add_hammingDist
   (u:=c) (v:=(0:IRSProfile.Index → IRSProfile.Field))
 have hn:Fintype.card IRSProfile.Index=262144:=by
   norm_num [IRSProfile.Index]
 rw [hn] at hagree
 have hz:(Finset.univ.filter (fun i => c i=0)).card ≤ 131071:=by
   change Code.agree c (0:IRSProfile.Index → IRSProfile.Field) ≤ 131071
   omega
 exact hz
theorem irs_code_mem_iff_rows
   (v:IRSProfile.Index → Fin IRSProfile.interleaving → IRSProfile.Field):
   v∈IRSProfile.code ↔
     ∀ b:Fin IRSProfile.interleaving,(fun i => v i b)∈IRSProfile.baseCode:=by
 change (∀ b:Fin IRSProfile.interleaving,
   (fun i => v i b)∈ReedSolomon.code IRSProfile.domain
     (IRSProfile.totalDimension/IRSProfile.interleaving)) ↔ _
 rw [IRSProfile.totalDimension_div_interleaving]
 rfl
theorem irs_squared_carrier_eq:
   (((IRSProfile.code^⋈ (Fin 2):
     ModuleCode IRSProfile.Index IRSProfile.Field
       (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
     Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)))=
   ((((IRSProfile.baseCode^⋈ (Fin 8))^⋈ (Fin 2):
     ModuleCode IRSProfile.Index IRSProfile.Field (Fin 2 → Fin 8 → IRSProfile.Field)):
     Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))):=by
 ext v
 change (∀ a:Fin 2,(fun i => v i a)∈IRSProfile.code) ↔
   ∀ a:Fin 2,∀ b:Fin 8,(fun i => v i a b)∈IRSProfile.baseCode
 constructor
 · intro hv a b
   exact (irs_code_mem_iff_rows _).mp (hv a) b
 · intro hv a
   exact (irs_code_mem_iff_rows _).mpr (hv a)
theorem irs_squared_lambda_le
   (e B:ℕ) (δ:ℝ≥0)
   (hgap:131071 < Fintype.card IRSProfile.Index-e)
   (halign:AffineLineAlignmentBound IRSProfile.baseCode e B)
   (hfield:B < Fintype.card IRSProfile.Field)
   (hseparation:15*(B+1).choose 2 < Fintype.card IRSProfile.Field)
   (hcell:(δ:ℝ)*(Fintype.card IRSProfile.Index:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (δ:ℝ) ≤ (B:ℕ∞):=by
 classical
 rw [irs_squared_carrier_eq]
 exact squared_eight_lambda_le IRSProfile.baseCode e 131071 B
   irs_zeroCoordinateBound hgap halign hfield hseparation (δ:ℝ) hcell
theorem irs_squared_claimedRadius_lambda_le
   (num den e B:ℕ) (hden:0 < den)
   (hcross:num*Fintype.card IRSProfile.Index < (e+1)*den)
   (hgap:131071 < Fintype.card IRSProfile.Index-e)
   (halign:AffineLineAlignmentBound IRSProfile.baseCode e B)
   (hfield:B < Fintype.card IRSProfile.Field)
   (hseparation:15*(B+1).choose 2 < Fintype.card IRSProfile.Field):
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (claimedRadius num den:ℝ) ≤ (B:ℕ∞):=by
 apply irs_squared_lambda_le e B (claimedRadius num den) hgap halign hfield hseparation
 simpa only [claimedRadius,NNReal.coe_div,NNReal.coe_natCast] using
   rational_radius_cell num den (Fintype.card IRSProfile.Index) e hden hcross
theorem irs_squared_lambda_toNat_le
   (e B:ℕ) (δ:ℝ≥0)
   (hgap:131071 < Fintype.card IRSProfile.Index-e)
   (halign:AffineLineAlignmentBound IRSProfile.baseCode e B)
   (hfield:B < Fintype.card IRSProfile.Field)
   (hseparation:15*(B+1).choose 2 < Fintype.card IRSProfile.Field)
   (hcell:(δ:ℝ)*(Fintype.card IRSProfile.Index:ℝ) < ((e+1:ℕ):ℝ)):
   (Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (δ:ℝ)).toNat ≤ B:=
 ENat.toNat_le_of_le_coe
   (irs_squared_lambda_le e B δ hgap halign hfield hseparation hcell)
end DraftProofs
end ProximityPrize.SubmissionLower.RCN018
