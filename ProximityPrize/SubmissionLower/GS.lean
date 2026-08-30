import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.RCN321
noncomputable section
variable {k B E:Type} [Field k] [Field B] [Field E]
variable [Algebra k B] [Algebra B E] [Algebra k E] [IsScalarTower k B E]
theorem trdeg_le_one_of_tower
   (hE:Algebra.trdeg k E ≤ 2) (htrans:Algebra.Transcendental B E):
   Algebra.trdeg k B ≤ 1:=by
 letI:Algebra.Transcendental B E:=htrans
 have hb:0 < Algebra.trdeg B E:=trdeg_pos B E
 have hsum:Algebra.trdeg k B+Algebra.trdeg B E=Algebra.trdeg k E:=
   trdeg_add_eq k B
 have hab:Algebra.trdeg k B+Algebra.trdeg B E ≤ 2:=by
   rw [hsum]
   exact hE
 by_contra hnot
 have ha:(1:Cardinal) < Algebra.trdeg k B:=lt_of_not_ge hnot
 have htwo:(2:Cardinal) ≤ Algebra.trdeg k B:=by
   have h:=Cardinal.add_one_le_of_lt ha
   norm_num at h
   exact h
 have hbone:(1:Cardinal) ≤ Algebra.trdeg B E:=Cardinal.one_le_iff_pos.mpr hb
 have hthree:(3:Cardinal) ≤ Algebra.trdeg k B+Algebra.trdeg B E:=by
   calc
     (3:Cardinal)=2+1:=by norm_num
     _ ≤ _:=add_le_add htwo hbone
 have:(3:Cardinal) ≤ 2:=hthree.trans hab
 norm_num at this
section RationalExtension
variable {k L:Type} [Field k] [Field L] [Algebra k L]
theorem coefficient_trdeg_le_one_of_rational_extension
   (B:IntermediateField k L) (E:IntermediateField k (RatFunc L))
   (hmap:B.map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤ E)
   (hX:(RatFunc.X:RatFunc L)∈E)
   (hE:Algebra.trdeg k E ≤ 2):Algebra.trdeg k B ≤ 1:=by
 let f:L →ₐ[k] RatFunc L:=IsScalarTower.toAlgHom k L (RatFunc L)
 let bToE:B →ₐ[k] E:=
   (IntermediateField.inclusion hmap).comp (B.equivMap f).toAlgHom
 letI:Algebra B E:=bToE.toRingHom.toAlgebra
 letI:IsScalarTower k B E:=IsScalarTower.of_algebraMap_eq fun c => by
   change bToE (algebraMap k B c)=algebraMap k E c
   exact bToE.commutes c
 let xE:E:=⟨RatFunc.X,hX⟩
 have hcomp:RingHom.comp (algebraMap L (RatFunc L)) B.val=
     RingHom.comp E.val (algebraMap B E):=by
   ext b
   rfl
 have hxE:Transcendental B xE:=
   (show Transcendental L (RatFunc.X:RatFunc L) from RatFunc.transcendental_X).of_ringHom_of_comp_eq
     B.val E.val B.val.injective hcomp
 exact trdeg_le_one_of_tower hE ⟨xE,hxE⟩
end RationalExtension
end
end ProximityPrize.SubmissionLower.RCN321
