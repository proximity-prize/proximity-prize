import ProximityPrize.SubmissionLower.Zg1hxlb
import ProximityPrize.SubmissionLower.Z32V4rd
import ProximityPrize.SubmissionLower.Z3R7Dac
import ProximityPrize.SubmissionLower.Znw9tNe
import ProximityPrize.SubmissionLower.ZLrBvqe
import ProximityPrize.SubmissionLower.ZGtcxMc
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.FormallySmooth → ziC, Algebra.IsSeparable → zw7, Function.Injective → zq4, IsFractionRing → z0o, IsFractionRing.injective → zxb, Module.Finite.of_surjective → zIU, Polynomial.X → z7y, Polynomial.map_ne_zero_iff → zeI, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, Set.singleton_union → z1f
section
section
set_option backward.isDefEq.respectTransparency false
namespace qi1t4Ta
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)
open qb0hmCe (CurveModel)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (Pencil evalXY)
open qZn79Eb (TrivialSeed a8p)
open scoped WithZero
open private normalize from ProximityPrize.SubmissionLower.Ze903db
open private separable_of_small_root separable_tower from ProximityPrize.SubmissionLower.Z3R7Dac
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S} (A:Pencil F)
private abbrev Physical:=IntermediateField.adjoin Cq.E ({A.x} : Set A.M)
private theorem ordinate_degree :
   ∃ _:Module.Finite (Physical A) A.M,Module.finrank (Physical A) A.M≤F.d:= by
 let P:=Physical A
 let e :Cq.E[X] →ₐ[Cq.E] P:=aeval (IntermediateField.AdjoinSimple.gen Cq.E A.x)
 have he (g:Cq.E[X]) : (e g:A.M)=aeval A.x g:= by
   exact (aeval_algHom_apply P.val (IntermediateField.AdjoinSimple.gen Cq.E A.x) g).symm
 have hinj:zq4 e := fun a b h =>
   (transcendental_iff_injective.mp A.independent) ((he a).symm.trans
     ((congrArg (fun c:P=>(c:A.M)) h).trans (he b)))
 let g:=F.f.map e.toRingHom
 have hg:g≠0:=(zeI hinj).mpr F.irreducible.ne_zero
 have hroot :aeval A.y g=0:= by
   rw [aeval_def,eval₂_map,show (algebraMap P A.M).comp e.toRingHom =
     eval₂RingHom (algebraMap Cq.E A.M) A.x from RingHom.ext (he)]
   exact A.equation
 have hy :IsIntegral P A.y :=IsAlgebraic.isIntegral ⟨g,hg,hroot⟩
 have hT:IntermediateField.adjoin P ({A.y} : Set A.M) = ⊤ := by
   apply (IntermediateField.restrictScalars_eq_top_iff (K:=Cq.E)).mp
   change (IntermediateField.adjoin (IntermediateField.adjoin Cq.E ({A.x} : Set A.M))
     ({A.y} : Set A.M)).restrictScalars Cq.E = ⊤
   rw [IntermediateField.adjoin_adjoin_left,z1f]
   exact A.generates
 have hF:=IntermediateField.adjoin.finiteDimensional hy
 rw [hT] at hF
 refine ⟨zIU
   (IntermediateField.topEquiv (F:=P) (E :=A.M)).toLinearMap
   (IntermediateField.topEquiv (F:=P) (E :=A.M)).surjective,?_⟩
 have h:=IntermediateField.adjoin.finrank hy
 rw [hT,IntermediateField.finrank_top'] at h
 rw [h]
 exact (natDegree_le_of_dvd (minpoly.dvd P A.y hroot) hg).trans_eq
   (natDegree_map_eq_of_injective hinj F.f)
variable {A} (v :Valuation A.M ℤᵐ⁰) (h:TrivialSeed A v) (hx :v A.x≤1)
private abbrev Residue :=IsLocalRing.ResidueField v.valuationSubring
private abbrev resAlgebra :zZE Cq.E (Residue v) :=
 ((IsLocalRing.residue _).comp (a8p A v h)).toAlgebra
private def xInt:v.valuationSubring :=⟨A.x,hx⟩
private abbrev xRes :Residue v :=IsLocalRing.residue _ (xInt v hx)
private abbrev ResPhys :=
 letI:=resAlgebra v h
 IntermediateField.adjoin Cq.E ({xRes v hx} : Set (Residue v))
private def polyInt:Cq.E[X] →+* v.valuationSubring :=eval₂RingHom (a8p A v h) (xInt v hx)
private theorem polyInt_root :v.valuationSubring.subtype.comp (polyInt v h hx) =
   eval₂RingHom (algebraMap Cq.E A.M) A.x := by
 apply z86
 · intro c
   simp only [polyInt,zQb,coe_eval₂RingHom,eval₂_C]
   rfl
 · simp only [polyInt,zQb,coe_eval₂RingHom,eval₂_X]
   rfl
private theorem polyInt_res (g:Cq.E[X]) :
  letI:=resAlgebra v h
  IsLocalRing.residue _ (polyInt v h hx g)=aeval (xRes v hx) g:= by
 dsimp only [polyInt,coe_eval₂RingHom]
 rw [hom_eval₂]
 rfl
private abbrev baseVal:=v.comap (Physical A).val.toRingHom
private def baseToRing: (baseVal v).valuationSubring →+* v.valuationSubring :=
 ((Physical A).val.toRingHom.comp (baseVal v).valuationSubring.subtype).codRestrict _
   (fun a=>a.property)
private theorem base_residue (a : (baseVal v).valuationSubring) :
   IsLocalRing.residue _ (baseToRing v a)∈ResPhys v h hx := by
 let:=resAlgebra v h
 let ρ:=IsLocalRing.residue v.valuationSubring
 let e :=polyInt v h hx
 let ψ:=RatFunc.algEquivOfTranscendental A.x A.independent
 let t:=ψ.symm a.val
 have hd:aeval A.x t.denom≠0:= fun hz =>
   t.denom_ne_zero ((transcendental_iff_injective.mp A.independent) (hz.trans (map_zero _).symm))
 have hfrac: (a.val :A.M)=aeval A.x t.num/aeval A.x t.denom:= by
   rw [← RatFunc.algEquivOfTranscendental_apply A.x A.independent t]
   exact congrArg (fun c:Physical A=>(c:A.M)) (ψ.apply_symm_apply a.val).symm
 have he :baseToRing v a*e t.denom=e t.num :=Subtype.ext (by
   change (a.val :A.M)*(v.valuationSubring.subtype.comp e) t.denom =
     (v.valuationSubring.subtype.comp e) t.num
   rw [polyInt_root v h hx]
   change (a.val :A.M)*aeval A.x t.denom=aeval A.x t.num
   rw [hfrac,div_mul_cancel₀ _ hd])
 have hr :ρ (baseToRing v a)*ρ (e t.denom)=ρ (e t.num) := by rw [← map_mul,he]
 have hden:ρ (e t.denom)≠0:= by
   intro hz
   have hn:ρ (e t.num)=0:= by rw [← hr,hz,mul_zero]
   obtain ⟨b,c,hc⟩:=t.isCoprime_num_denom
   have hh:=congrArg (ρ.comp e) hc
   simp only [map_add,map_mul,zQb,map_one,hn,hz,mul_zero,add_zero] at hh
   exact zero_ne_one hh
 have hm (g:Cq.E[X]) :ρ (e g)∈ResPhys v h hx := by
   rw [polyInt_res v h hx]
   exact Algebra.adjoin_le (IntermediateField.subset_adjoin Cq.E _) <|
     Polynomial.aeval_mem_adjoin_singleton Cq.E (xRes v hx)
 exact ((eq_div_iff_mul_eq hden).mpr hr).symm ▸ (ResPhys v h hx).div_mem (hm _) (hm _)
private theorem residue_annihilator (a :Residue v) :
   letI:=resAlgebra v h
   ∃ g: (ResPhys v h hx)[X],g≠0∧g.natDegree≤F.d ∧
     g.eval₂ (ResPhys v h hx).val.toRingHom a=0:= by
 let:=resAlgebra v h
 obtain ⟨hfin,hdeg⟩:=ordinate_degree A
 let:=hfin
 obtain ⟨b,rfl⟩:=IsLocalRing.residue_surjective (R:=v.valuationSubring) a
 let P:=Physical A
 let f :=minpoly P (b:A.M)
 have hf :f≠0:=minpoly.ne_zero (IsIntegral.of_finite P _)
 have hd:f.natDegree≤F.d:=(minpoly.natDegree_le (A:=P) (b:A.M)).trans hdeg
 let w:=baseVal v
 let ι:=w.valuationSubring.subtype
 obtain ⟨c,g,i,hg,hi⟩:=normalize w hf
 let e :w.valuationSubring →+* ResPhys v h hx :=
   ((IsLocalRing.residue _).comp (baseToRing v)).codRestrict _ (base_residue v h hx)
 refine ⟨g.map e,?_,?_,?_⟩
 · intro hz
   have he :=congrArg (fun f : (ResPhys v h hx)[X]=>f.coeff i) hz
   rw [coeff_map,hi,map_one,coeff_zero] at he
   exact one_ne_zero he
 · refine natDegree_map_le.trans ?_
   rw [← natDegree_map_eq_of_injective (f :=ι) Subtype.val_injective g,hg]
   exact (natDegree_C_mul_le _ _).trans hd
 · have hv :g.eval₂ (baseToRing v) b=0:= by
     apply Subtype.val_injective
     change v.valuationSubring.subtype _=v.valuationSubring.subtype 0
     rw [map_zero,hom_eval₂]
     change g.eval₂ ((algebraMap P A.M).comp ι) (b:A.M)=0
     rw [← eval₂_map,hg,eval₂_mul,eval₂_C,← aeval_def,minpoly.aeval,mul_zero]
   rw [eval₂_map]
   change g.eval₂ ((IsLocalRing.residue _).comp (baseToRing v)) (IsLocalRing.residue _ b)=0
   rw [← hom_eval₂,hv,map_zero]
theorem proof :qZn79Eb.c3:= by
 intro q Cq z S F A hd hδ hδp v h _ hx hy hp
 let:=resAlgebra v h
 change zw7 Cq.E (Residue v)
 let O:=v.valuationSubring
 let π:=IsLocalRing.residue O
 let j:=polyInt v h hx
 let y :O:=⟨A.y,hy⟩
 have hv (g:Cq.E[X][X]) : ((g.eval₂ j y :O) :A.M)=evalXY g A.x A.y := by
   change O.subtype (g.eval₂ j y)= _
   rw [hom_eval₂,polyInt_root v h hx]
   rfl
 have hr (g:Cq.E[X][X]) :g.eval₂ (π.comp j) (π y)=0↔v (evalXY g A.x A.y)<1 := by
   rw [← hom_eval₂,IsLocalRing.residue_eq_zero_iff,v.mem_maximalIdeal_iff,hv]
 have hzero :aeval (xRes v hx) F.f.discr=0:= by
   rw [← polyInt_res v h hx]
   exact discr_of_common_root (π.comp j) F.f F.irreducible F.positive (π y)
     ((hr F.f).mpr (by rw [A.equation,map_zero]; exact zero_lt_one))
     ((hr F.f.derivative).mpr hp)
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP Cq.E p:=charP_of_injective_ringHom (algebraMap L Cq.E).injective p
 have hF:zw7 Cq.E (ResPhys v h hx) :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable Cq.E (Residue v)).mpr
     (separable_of_small_root hδ hδp hzero)
 let:CharP (ResPhys v h hx) p :=
   charP_of_injective_ringHom (algebraMap Cq.E (ResPhys v h hx)).injective p
 have hE :zw7 (ResPhys v h hx) (Residue v) :=⟨fun a=> by
   obtain ⟨g,hg,hdegree,hzero⟩:=residue_annihilator v h hx a
   change aeval a g=0 at hzero
   exact separable_of_small_root hg (hdegree.trans_lt hd) hzero⟩
 exact separable_tower (ResPhys v h hx) hF hE
end
end qi1t4Ta
end
section
set_option autoImplicit true
namespace q43OGpb
theorem proof :qeBKasb.c3 :=
 qi1t4Ta.proof
end q43OGpb
end
end
section
section
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000
set_option backward.isDefEq.respectTransparency false
namespace qGnKhWc
noncomputable section
open Polynomial TrivSqZeroExt qLXroAb
open P5 (K p)
open cu (L)
open q9uVqha (Generic)
open private separable_of_small_root from ProximityPrize.SubmissionLower.Z3R7Dac
private theorem derivation {E M:Type} [Field E] [Field M] [zZE E M]
   [zZE E[X] M] [ziC E[X] M]
   (hc : ∀ c:E,algebraMap E[X] M (C c)=algebraMap E M c) :
   ∃ D:Derivation E M M,D (algebraMap E[X] M z7y)=1 := by
 let j:=algebraMap E[X] M
 let A:=TrivSqZeroExt M M
 let b:E[X] →+* A :=
   eval₂RingHom ((inlHom M M).comp (algebraMap E M)) (inl (j z7y)+inr 1)
 let π₀:A →+* M:=(fstHom ℤ M M).toRingHom
 have hb:π₀.comp b=j:= by
   apply z86
   · intro c
     simp only [zQb,b,coe_eval₂RingHom,eval₂_C]
     exact (hc c).symm
   · simp only [zQb,b,coe_eval₂RingHom,eval₂_X]
     change (inl (j z7y)+inr (1 :M) :A).fst=j z7y
     rw [fst_add,fst_inl,fst_inr,add_zero]
 let:zZE E[X] A:=b.toAlgebra
 let π:A →ₐ[E[X]] M := { π₀ with commutes' := zLs hb }
 have hs :Function.Surjective π:= fun a=>⟨inl a,rfl⟩
 have hk :IsNilpotent (RingHom.ker π.toRingHom) := by
   refine ⟨2,?_⟩
   let I:=RingHom.ker π.toRingHom
   change I ^(2 :ℕ) = ⊥
   refine (pow_two I).trans (le_antisymm (Ideal.mul_le.mpr ?_) bot_le)
   intro a ha b hb
   change a.fst=0 at ha
   change b.fst=0 at hb
   rw [Ideal.mem_bot]
   apply TrivSqZeroExt.ext
   · change a.fst*b.fst=0
     rw [ha,zero_mul]
   · change a.fst•b.snd+MulOpposite.op b.fst•a.snd=0
     simp [ha,hb]
 let f :=Algebra.FormallySmooth.liftOfSurjective (AlgHom.id E[X] M) π hs hk
 have hf (a :M) : (f a).fst=a :=
   Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id E[X] M) π hs hk a
 have h (a :E[X]) :f (j a)=b a :=f.commutes a
 have hconst (c:E) : (f (algebraMap E M c)).snd=0:= by
   rw [← hc,h]
   simp only [b,coe_eval₂RingHom,eval₂_C]
   rfl
 refine ⟨{ toFun:= fun a=>(f a).snd
           map_add' := fun a b=> by
             change (f (a+b)).snd= _
             rw [map_add]
             exact snd_add (f a) (f b)
           map_smul' := fun c a => ?_
           map_one_eq_zero' := by change (f 1).snd=0; simp
           leibniz' := fun a b => ?_ },?_⟩
 · change (f (c•a)).snd=c•(f a).snd
   rw [Algebra.smul_def,map_mul,snd_mul,hf,hconst]
   simp [Algebra.smul_def]
 · change (f (a*b)).snd=a•(f b).snd+b•(f a).snd
   rw [map_mul,snd_mul,hf,hf,op_smul_eq_smul]
 · change (f (j z7y)).snd = 1
   rw [h]
   simp only [b,coe_eval₂RingHom,eval₂_X]
   change (0:M)+1=1
   exact zero_add _
private def abscissaEval {E M:Type} [Field E] [Field M] [zZE E M] (x :M) :
  E[X] →ₐ[E] IntermediateField.adjoin E ({x} : Set M) :=
 aeval (IntermediateField.AdjoinSimple.gen E x)
open scoped IntermediateField.algebraAdjoinAdjoin in
private theorem abscissaFraction {E M:Type} [Field E] [Field M] [zZE E M]
  {x :M} (hx :Transcendental E x) :
  let _:=(abscissaEval (E :=E) x).toRingHom.toAlgebra
  z0o E[X] (IntermediateField.adjoin E ({x} : Set M)) := by
 let:=(abscissaEval (E :=E) x).toRingHom.toAlgebra
 refine IsFractionRing.of_ringEquiv_left (algEquivOfTranscendental E x hx).toRingEquiv ?_
 intro b
 apply Subtype.val_injective
 change (abscissaEval (E :=E) x b:M)=(algEquivOfTranscendental E x hx b:M)
 rw [algEquivOfTranscendental_apply]
 change (IntermediateField.adjoin E {x}).val (aeval (IntermediateField.AdjoinSimple.gen E x) b) =
  (Algebra.adjoin E {x}).val (aeval ⟨x,Algebra.self_mem_adjoin_singleton E x⟩ b)
 rw [← aeval_algHom_apply,← aeval_algHom_apply]
 rfl
private theorem build {q:qkgz7gb.PlaneCurve} {Cq:qb0hmCe.CurveModel q}
   {z :K→K} {S:K→K[X]} (F:P5_7_3_5_2.Sheet Cq z S)
   (M:Type) [Field M] [IsDomain (AdjoinRoot F.f)] [zZE (AdjoinRoot F.f) M]
   [z0o (AdjoinRoot F.f) M] (hthree :3≤F.d) (hsmall:F.d<p) :
   Nonempty (Generic F) := by
 let E :=Cq.E
 let Q:=AdjoinRoot F.f
 let r :E[X][X] →+* M:=(algebraMap Q M).comp (AdjoinRoot.mk F.f)
 let i:E[X] →+* M:=r.comp C
 let:zZE E M:=(i.comp C).toAlgebra
 let x :=i z7y
 let y :=r z7y
 have hi:zq4 i :=
   (zxb Q M).comp (AdjoinRoot.of.injective_of_degree_ne_zero (fun h=> by
     rw [degree_eq_natDegree F.irreducible.ne_zero,Nat.cast_eq_zero] at h
     exact F.positive.ne' h))
 have hix :eval₂RingHom (algebraMap E M) x=i:= by
   apply z86
   · intro c
     exact eval₂_C _ _
   · exact eval₂_X _ _
 have hr :eval₂RingHom i y=r := by
   apply z86
   · intro c
     exact eval₂_C _ _
   · exact eval₂_X _ _
 have ev (g:E[X][X]) :evalXY g x y=r g:= by
   change eval₂RingHom (eval₂RingHom (algebraMap E M) x) y g=r g
   rw [hix,hr]
 have ker (g:E[X][X]) :evalXY g x y=0↔F.f∣g:= by
   rw [ev]
   exact (map_eq_zero_iff _ (zxb Q M)).trans AdjoinRoot.mk_eq_zero
 have hx :Transcendental E x := by
   apply transcendental_iff_injective.mpr
   change zq4 (eval₂RingHom (algebraMap E M) x)
   rw [hix]
   exact hi
 let P:=IntermediateField.adjoin E ({x} : Set M)
 let a :E[X] →ₐ[E] P:=abscissaEval (E :=E) x
 have ha :P.val.toRingHom.comp a.toRingHom=i:= by
   have h:P.val.comp a=aeval x :=
     (aeval_algHom P.val (IntermediateField.AdjoinSimple.gen E x)).symm
   exact (congrArg AlgHom.toRingHom h).trans hix
 have hainj:zq4 a := by
   intro u v huv
   apply hi
   rw [← ha]
   exact congrArg P.val huv
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
 let:CharP P p:=charP_of_injective_ringHom (algebraMap E P).injective p
 let g:=F.f.map a.toRingHom
 have gd:g.natDegree=F.d:=natDegree_map_eq_of_injective hainj _
 have evg (b:E[X][X]) :aeval y (b.map a.toRingHom)=r b:= by
   rw [aeval_def,eval₂_map]
   change b.eval₂ (P.val.toRingHom.comp a.toRingHom) y=r b
   rw [ha]
   exact zLs hr b
 have hroot :aeval y g=0:=(evg _).trans (by
   change algebraMap Q M (AdjoinRoot.mk F.f F.f)=0
   rw [AdjoinRoot.mk_self,map_zero])
 have hy :IsSeparable P y :=separable_of_small_root
   (zeI hainj |>.mpr F.irreducible.ne_zero) (gd.trans_lt hsmall) hroot
 have hT:IntermediateField.adjoin P ({y} : Set M) = ⊤ := by
   let T:=IntermediateField.adjoin P ({y} : Set M)
   apply eq_top_iff.mpr
   intro t _
   have hp (b:Q) :algebraMap Q M b∈T:= by
     obtain ⟨b,rfl⟩:=AdjoinRoot.mk_surjective b
     change r b∈T
     rw [← evg]
     exact IntermediateField.algebra_adjoin_le_adjoin P _ (aeval_mem_adjoin_singleton P y)
   obtain ⟨b,c,_,rfl⟩:=IsFractionRing.div_surjective Q t
   exact T.div_mem (hp b) (hp c)
 have hgen:IntermediateField.adjoin E ({x,y} : Set M) = ⊤ := by
   have h:=congrArg (IntermediateField.restrictScalars E) hT
   simpa only [P,IntermediateField.adjoin_adjoin_left,z1f,
     IntermediateField.restrictScalars_top] using h
 let T:=IntermediateField.adjoin P ({y} : Set M)
 let e :T ≃ₐ[P] M:=(IntermediateField.equivOfEq hT).trans IntermediateField.topEquiv
 have hfin:Module.Finite P M :=
   let:=IntermediateField.adjoin.finiteDimensional hy.isIntegral
   zIU e.toLinearMap e.surjective
 let:zw7 P T :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable P M).mpr hy
 let:zw7 P M:=AlgEquiv.Algebra.isSeparable e
 let:zZE E[X] P:=a.toRingHom.toAlgebra
 let:zZE E[X] M:=i.toAlgebra
 let:IsScalarTower E[X] P M :=
   IsScalarTower.of_algebraMap_eq fun c=>(zLs ha c).symm
 let:z0o E[X] P:=abscissaFraction hx
 let:ziC E[X] P :=
   Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors E[X])
 let:Algebra.FormallyEtale P M:=Algebra.FormallyEtale.of_isSeparable P M
 let:ziC E[X] M:=Algebra.FormallySmooth.comp E[X] P M
 obtain ⟨D,hD⟩:=derivation (E :=E) (M:=M) (fun _=>rfl)
 have hdg:g.derivative.natDegree=F.d - 1 :=
   (qrezXJe.bD9 (gd.symm ▸ F.positive) (gd.trans_lt hsmall)).trans
     (congrArg (· - 1) gd)
 have hder :F.f.derivative≠0:= by
   intro hz
   have hzg:g.derivative=0:= by rw [show g= _ from rfl,derivative_map,hz,Polynomial.map_zero]
   rw [hzg,natDegree_zero] at hdg
   omega
 refine ⟨{ M:=M,x :=x,y :=y,independent:=hx,kernel:=ker,generates :=hgen
           polar_ne := ?_,y_ne := ?_,finite :=hfin,separable :=inferInstance
           deriv :=D,deriv_x :=hD }⟩
 · intro h
   have hd:=natDegree_le_of_dvd ((ker _).mp h) hder
   exact (Nat.not_le_of_lt (natDegree_derivative_lt F.positive.ne')) hd
 · intro h
   have hd:=natDegree_le_of_dvd ((ker z7y).mp ((ev _).trans h)) Polynomial.X_ne_zero
   rw [natDegree_X] at hd
   change 3≤F.f.natDegree at hthree
   omega
theorem proof :q9uVqha.c1 := by
 intro q Cq z S F hthree hsmall
 let:IsDomain (AdjoinRoot F.f) :=AdjoinRoot.isDomain_of_prime
  ((UniqueFactorizationMonoid.irreducible_iff_prime (α:=Cq.E[X][X])).mp F.irreducible)
 exact build F (FractionRing (AdjoinRoot F.f)) hthree hsmall
end
end qGnKhWc
end
section
set_option autoImplicit true
namespace qDcYfMc
theorem proof :qJh2f6d.c1 :=
 qGnKhWc.proof
end qDcYfMc
end
section
namespace qF6fTmd
theorem proof :qJh2f6d.c6:=qk9SLHb.proof
end qF6fTmd
end
section
namespace qQ1s08b
theorem proof :qJh2f6d.c3 :=
 qBMP0Kd.proof
end qQ1s08b
end
section
set_option autoImplicit true
namespace qPq7Shb
theorem proof :qJh2f6d.c5:=q2ANK6b.proof
end qPq7Shb
end
end
