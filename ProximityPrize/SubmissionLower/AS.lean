import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A
section ProximityFlatProofPort
open IsLocalRing LinearMap Module Submodule TensorProduct AlgebraTensorModule
variable {A B M:Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
 [IsLocalHom (algebraMap A B)] [AddCommGroup M] [Module A M]
section tower
variable [Module B M] [IsScalarTower A B M]
variable (A) in
theorem CovBy.length_restrictScalars {p q:Submodule B M} (h:p ⋖ q):
   length A q=Module.length A p+Module.length (ResidueField A) (ResidueField B):=by
 let f:p →ₗ[B] q:=inclusion h.le
 have key:IsSimpleModule B (q ⧸ f.range):=by
   rwa [range_inclusion, ←covBy_iff_quot_is_simple h.le]
 obtain ⟨m,hm,⟨e⟩⟩:=isSimpleModule_iff_quot_maximal.mp key
 rw [eq_maximalIdeal hm] at e
 let g:q →ₗ[B] ResidueField B:=e.comp f.range.mkQ
 have:Function.Injective f:=inclusion_injective _
 have:Function.Surjective g:=e.surjective.comp f.range.mkQ_surjective
 have:Function.Exact f g:=exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
 rw [length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A)
   (by simpa) (by simpa) (by simpa),Module.length_eq_of_surjective (M:=ResidueField B)
     (residue_surjective (R:=A)),Module.length_eq_rank]
variable (A B M) in
theorem IsLocalRing.length_restrictScalars:
   length A M=length B M*Module.length (ResidueField A) (ResidueField B):=by
 by_cases h:IsFiniteLength B M
 · obtain ⟨s,hs_bot,hs_top⟩:=isFiniteLength_iff_exists_compositionSeries.mp h
   rw [←length_compositionSeries s hs_bot hs_top]
   suffices ∀ k,length A (s k)=k*Module.length (ResidueField A) (ResidueField B) by
     rw [←Fin.val_last s.length, ←this, ←RelSeries.last,hs_top]
     exact length_top.symm
   intro k
   induction k using Fin.induction with
   | zero => rw [←RelSeries.head,hs_bot];simp
   | succ i hi => simpa [hi,add_one_mul] using (s.step i).length_restrictScalars A
 · have:¬ IsFiniteLength A M:=by
     contrapose! h
     rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
     exact h.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
   rw [←length_ne_top_iff,not_ne_iff] at h this
   have ne:length (ResidueField A) (ResidueField B)≠0:=by
     simpa [pos_iff_ne_zero] using Module.length_pos
   rw [h,this,ENat.top_mul ne]
end tower
section flat
variable [Flat A B]
variable (B) in
theorem CovBy.length_baseChange {p q:Submodule A M} (h:p ⋖ q):
   length B (q.baseChange B)=
     length B (p.baseChange B)+length B (B ⧸ (maximalIdeal A).map (algebraMap A B)):=by
 have hp:length B (B ⊗[A] p)=length B (p.baseChange B):=
   (toBaseChange.toLinearEquiv B p).length_eq
 have hq:length B (B ⊗[A] q)=length B (q.baseChange B):=
   (toBaseChange.toLinearEquiv B q).length_eq
 rw [←hp, ←hq]
 let f:p →ₗ[A] q:=inclusion h.le
 have key:IsSimpleModule A (q ⧸ f.range):=by
   rwa [range_inclusion, ←covBy_iff_quot_is_simple h.le]
 obtain ⟨m,hm,⟨e⟩⟩:=isSimpleModule_iff_quot_maximal.mp key
 obtain rfl:=eq_maximalIdeal hm
 let g:=e.comp f.range.mkQ
 have:Function.Injective f:=inclusion_injective _
 have:Function.Surjective g:=e.surjective.comp f.range.mkQ_surjective
 have:Function.Exact f g:=exact_iff.mpr (by simp [f,g])
 have:FaithfullyFlat A B:=FaithfullyFlat.of_flat_of_isLocalHom
 rw [length_eq_add_of_exact (lTensor B B f) (lTensor B B g) (by simpa) (by simpa) (by simpa),
   (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toLinearEquiv.length_eq]
variable (A B M) in
theorem IsLocalRing.length_baseChange:
   length B (B ⊗[A] M)=length A M*length B (B ⧸ (maximalIdeal A).map (algebraMap A B)):=by
 by_cases h:IsFiniteLength A M
 · obtain ⟨s,hs_bot,hs_top⟩:=isFiniteLength_iff_exists_compositionSeries.mp h
   rw [←length_compositionSeries s hs_bot hs_top]
   suffices ∀ k,length B ((s k).baseChange B)=
       k*length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) by
     rw [←Fin.val_last s.length, ←this, ←RelSeries.last,hs_top,baseChange_top,length_top]
   intro k
   induction k using Fin.induction with
   | zero => rw [←RelSeries.head,hs_bot,baseChange_bot];simp
   | succ i hi => simpa [hi,add_one_mul] using (s.step i).length_baseChange B
 · have:¬ IsFiniteLength B (B ⊗[A] M):=by
     contrapose! h
     rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
     have:FaithfullyFlat A B:=FaithfullyFlat.of_flat_of_isLocalHom
     exact h.imp IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
       IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat
   rw [←length_ne_top_iff,not_ne_iff] at h this
   have ne:length B (B ⧸ (maximalIdeal A).map (algebraMap A B))≠0:=by
     simpa [←pos_iff_ne_zero,length_pos_iff] using (map_maximalIdeal_lt_top (algebraMap A B)).ne
   rw [h,this,ENat.top_mul ne]
end flat
