import ProximityPrize.SubmissionLower.PortHighFinish
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Fast056

set_option Elab.async false

-- Source: Research6969.CurveSliceTransport
section Z6969Source0618
set_option autoImplicit true
namespace Research6969.CurveSliceTransport
noncomputable section
open K1_14 (FX Seeds)
open K1_14_2 (Ambient RootAmbient SeedField generic RootSeedSection RootYSection JetSeedSection JetYSection)
open K1_14_2_2 (CurveGeometry)
open K1_14_2_3 (rootImage seedLength yLength)
open K1_14_2_4 (SourceRing SliceField sliceVariable)
open MvPolynomial
open scoped Classical
set_option maxRecDepth 6000

/-- Projection preserves the actual two finite slice bounds used in a discarded-curve invoice. -/
theorem root_slices (Q:Ideal Ambient) (geom:CurveGeometry Q) :
    Module.Finite SeedField (RootSeedSection (rootImage Q)) ∧
    Module.finrank SeedField (RootSeedSection (rootImage Q))≤seedLength Q ∧
    Module.Finite SeedField (RootYSection (rootImage Q)) ∧
    Module.finrank SeedField (RootYSection (rootImage Q))≤yLength Q := by
  have : Module.Finite SeedField (JetSeedSection Q):=geom.2.2.1
  have : Module.Finite SeedField (JetYSection Q):=geom.2.2.2.2
  have nt:Nontrivial (JetSeedSection Q):=Module.nontrivial_of_finrank_pos geom.2.2.2.1
  obtain ⟨_,_,s,_,si⟩:=K1_14_2_3_2_1.proof Q geom.1 nt
  obtain ⟨y,yi⟩:=K1_14_2_3_2_2.proof Q
  exact ⟨Module.Finite.of_injective s.toLinearMap si,LinearMap.finrank_le_finrank_of_injective (f:=s.toLinearMap) si,
    Module.Finite.of_injective y.toLinearMap yi,LinearMap.finrank_le_finrank_of_injective (f:=y.toLinearMap) yi⟩

private abbrev R:=SourceRing 2
private abbrev E:=SliceField 2
private def c:R:=MvPolynomial.X (some (0:Fin 2))
private def xy (i:Fin 2):R:=![MvPolynomial.X (some (1:Fin 2)),MvPolynomial.X (none:Option (Fin 2))] i
private abbrev Loc:=Localization.Away c
private def spec:R→+*Seeds:=(aeval (R:=FX) (fun z:Option (Fin 2)=>
  z.elim (MvPolynomial.X (1:Fin 2):Seeds) (fun i=>(![1,MvPolynomial.X (0:Fin 2)]:Fin 2→Seeds) i))).toRingHom
private def natMap:Seeds→+*Loc := eval₂Hom ((algebraMap R Loc).comp MvPolynomial.C)
  (fun i=>algebraMap R Loc (xy i)*IsLocalization.Away.invSelf (S:=Loc) c)

private theorem spec_c : spec c=1:=by simp [spec,c]
private theorem spec_xy (i:Fin 2) : spec (xy i)=MvPolynomial.X i:=by fin_cases i <;> simp [spec,xy]
private theorem nat_injective:Function.Injective natMap:=by
  let j:Loc→+*Seeds:=IsLocalization.Away.lift c (g:=spec) (by rw [spec_c];exact isUnit_one)
  have base (r:R):j (algebraMap R Loc r)=spec r:=IsLocalization.Away.lift_eq ..
  have inv:j (IsLocalization.Away.invSelf (S:=Loc) c)=1:=by
    have h:=congrArg j (IsLocalization.Away.mul_invSelf (S:=Loc) c)
    simpa only [map_mul,base,spec_c,one_mul,map_one] using h
  have id:j.comp natMap=RingHom.id Seeds:=by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [natMap,base,spec]
    · intro i
      simp [natMap,base,inv,spec_xy]
  exact (fun x y eq=>by
    have h:=congrArg j eq
    change (j.comp natMap) x=(j.comp natMap) y at h
    simpa only [id,RingHom.id_apply] using h)

private def liftLoc:Loc→+*E:=IsLocalization.Away.lift c (g:=algebraMap R E)
  (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R E)).mpr (MvPolynomial.X_ne_zero _)))
private theorem lift_base (z:R):liftLoc (algebraMap R Loc z)=algebraMap R E z :=
  IsLocalization.Away.lift_eq ..
private theorem lift_injective:Function.Injective liftLoc:=by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers c) liftLoc).mpr
  intro a b
  constructor
  · exact congrArg liftLoc
  · intro eq
    rw [lift_base,lift_base] at eq
    exact congrArg (algebraMap R Loc) (IsFractionRing.injective R E eq)

private def seedMap:Seeds→+*E:=liftLoc.comp natMap
private theorem seedMap_injective : Function.Injective seedMap:=lift_injective.comp nat_injective
def parameterField:SeedField→+*E:=IsFractionRing.lift (g:=seedMap) seedMap_injective
private theorem on_polynomial (x:Seeds):parameterField (algebraMap Seeds SeedField x)=seedMap x :=
  IsFractionRing.lift_algebraMap (g:=seedMap) seedMap_injective x

theorem parameter_scalars (x:FX) :
    parameterField (algebraMap FX SeedField x)=algebraMap FX E x := by
  change parameterField (algebraMap Seeds SeedField (MvPolynomial.C x))=_
  rw [on_polynomial]
  simp only [seedMap,RingHom.comp_apply,natMap,eval₂Hom_C,lift_base]
  rfl

/-- Multiplying the normalized seed line by its leading coefficient gives the
fully generic line used in the bidegree embedding. -/
theorem parameter_coordinates (i:Fin 2) :
    parameterField (generic i)*sliceVariable (some (0:Fin 2))=algebraMap R E (xy i) := by
  change parameterField (algebraMap Seeds SeedField (MvPolynomial.X i))*algebraMap R E c=_
  rw [on_polynomial]
  have m:=congrArg liftLoc (IsLocalization.Away.mul_invSelf (S:=Loc) c)
  rw [map_mul,lift_base,map_one] at m
  simp only [seedMap,RingHom.comp_apply,natMap,eval₂Hom_X',map_mul,lift_base]
  rw [mul_assoc,mul_comm (liftLoc (IsLocalization.Away.invSelf (S:=Loc) c)),m,mul_one]

private def ordIndex : Fin 2 → Option (Fin 2) := ![some 0,none]
private theorem ordInject : Function.Injective ordIndex := by decide
private def ordMap:Seeds→+*E :=
  (algebraMap R E).comp (MvPolynomial.rename ordIndex).toRingHom
private theorem ordMap_injective : Function.Injective ordMap :=
  (IsFractionRing.injective R E).comp (MvPolynomial.rename_injective _ ordInject)
def ordinateField:SeedField→+*E:=IsFractionRing.lift (g:=ordMap) ordMap_injective

theorem ordinate_scalars (x:FX) : ordinateField (algebraMap FX SeedField x)=algebraMap FX E x := by
  change ordinateField (algebraMap Seeds SeedField (MvPolynomial.C x))=_
  rw [show ordinateField (algebraMap Seeds SeedField (MvPolynomial.C x))=ordMap (MvPolynomial.C x) from
    IsFractionRing.lift_algebraMap (g:=ordMap) ordMap_injective _]
  simp [ordMap]
  rfl

theorem ordinate_coordinate : ordinateField (generic 1)=sliceVariable (n:=2) none := by
  change ordinateField (algebraMap Seeds SeedField (MvPolynomial.X 1))=_
  rw [show ordinateField (algebraMap Seeds SeedField (MvPolynomial.X 1))=ordMap (MvPolynomial.X 1) from
    IsFractionRing.lift_algebraMap (g:=ordMap) ordMap_injective _]
  simp [ordMap,ordIndex,sliceVariable]

theorem parameter_slope : parameterField (generic 0)*sliceVariable (some (0:Fin 2))=
    sliceVariable (some (1:Fin 2)) := parameter_coordinates 0
theorem parameter_offset : parameterField (generic 1)*sliceVariable (some (0:Fin 2))=
    sliceVariable (n:=2) none := parameter_coordinates 1

end
end Research6969.CurveSliceTransport
end Z6969Source0618

-- Source: Research6969.SliceExtension
section Z6969Source0619
set_option autoImplicit true
namespace Research6969.SliceExtension
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {k E σ τ:Type*} [Field k] [Field E] [Algebra k E]

private def coefficients (J:Ideal (MvPolynomial σ k)) :
    E ⊗[k] (MvPolynomial σ k ⧸ J) ≃ₐ[E]
      (MvPolynomial σ E ⧸ J.map (MvPolynomial.map (algebraMap k E))) := by
  let R:=MvPolynomial σ k
  let e : E ⊗[k] R ≃ₐ[E] MvPolynomial σ E:=MvPolynomial.algebraTensorAlgEquiv k E
  let inc:R→+*E⊗[k]R:=(Algebra.TensorProduct.includeRight (A:=E) (R:=k)).toRingHom
  have eq:e.toAlgHom.toRingHom.comp inc=MvPolynomial.map (algebraMap k E) := by
    apply RingHom.ext
    intro q
    change e (1⊗ₜ[k]q)=MvPolynomial.map (algebraMap k E) q
    simpa only [e,one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul k E 1 q
  have ideal:J.map (MvPolynomial.map (algebraMap k E))=(J.map inc).map e.toAlgHom.toRingHom := by
    rw [Ideal.map_map,eq]
  exact (Algebra.TensorProduct.tensorQuotientEquiv E R E J).trans
    (Ideal.quotientEquivAlg _ _ e ideal)

def move (v:σ≃τ) : MvPolynomial σ k →+* MvPolynomial τ E :=
  (MvPolynomial.rename v).toRingHom.comp (MvPolynomial.map (algebraMap k E))

theorem length_le (J:Ideal (MvPolynomial σ k)) (Q:Ideal (MvPolynomial τ E))
    [Module.Finite k (MvPolynomial σ k ⧸ J)] (v:σ≃τ) (inc:J.map (move v)≤Q) :
    Module.Finite E (MvPolynomial τ E ⧸ Q) ∧
    Module.finrank E (MvPolynomial τ E ⧸ Q)≤Module.finrank k (MvPolynomial σ k ⧸ J) := by
  let e:=MvPolynomial.renameEquiv E v
  let base:=J.map (MvPolynomial.map (algebraMap k E))
  let changeVars:=Ideal.quotientEquivAlg base (base.map e.toAlgHom.toRingHom) e rfl
  let full: E ⊗[k] (MvPolynomial σ k ⧸ J) ≃ₐ[E]
      MvPolynomial τ E ⧸ base.map e.toAlgHom.toRingHom := (coefficients J).trans changeVars
  have rename_eq : e.toAlgHom.toRingHom=(MvPolynomial.rename v).toRingHom := by
    ext a <;> simp [e]
  have contains:base.map e.toAlgHom.toRingHom≤Q:=by
    dsimp only [base]
    rw [Ideal.map_map,rename_eq]
    exact inc
  let f: E ⊗[k] (MvPolynomial σ k ⧸ J) →ₐ[E] MvPolynomial τ E ⧸ Q :=
    (Ideal.Quotient.factorₐ E contains).comp full.toAlgHom
  have onto:Function.Surjective f:=(Ideal.Quotient.factor_surjective contains).comp full.surjective
  exact ⟨Module.Finite.of_surjective f.toLinearMap onto,
    (LinearMap.finrank_le_finrank_of_surjective (f:=f.toLinearMap) onto).trans_eq Module.finrank_baseChange⟩

end
end Research6969.SliceExtension
end Z6969Source0619

-- Source: Research6969.NativeCurveSlices
section Z6969Source0620
set_option autoImplicit true
namespace Research6969.NativeCurveSlices
noncomputable section
open MvPolynomial
open K1_14 (FX)
open K1_14_2 (RootAmbient Ambient SeedField generic seedLine ySection RootSeedSection RootYSection)
open K1_14_2_2 (CurveGeometry)
open K1_14_2_3 (rootImage seedLength yLength)
open K1_14_2_4 (SourceRing SliceField sliceVariable SectionRing parameterCut ordinateCut SliceBounds)
open CurveSliceTransport
open scoped Classical
set_option maxRecDepth 6000

def index : Fin 3≃Option (Fin 2) where
  toFun i:=(![some 0,some 1,none]:Fin 3→Option (Fin 2)) i
  invFun i:=i.elim 2 (fun j=>j.castSucc)
  left_inv i:=by fin_cases i <;> rfl
  right_inv i:=by cases i with
    | none => rfl
    | some i => fin_cases i <;> rfl

def source (P:Ideal RootAmbient) : Ideal (SourceRing 2) := P.map (MvPolynomial.rename index).toRingHom
private abbrev E:=SliceField 2
private def transport (j:SeedField→+*E) : MvPolynomial (Fin 3) SeedField →+* MvPolynomial (Option (Fin 2)) E :=
  (MvPolynomial.rename index).toRingHom.comp (MvPolynomial.map j)

private theorem commutes (j:SeedField→+*E) (scalar:∀ a:FX,j (algebraMap FX SeedField a)=algebraMap FX E a) :
    (transport j).comp (MvPolynomial.map (algebraMap FX SeedField)) =
      (MvPolynomial.map (algebraMap FX E)).comp (MvPolynomial.rename index).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c;simp [transport,scalar]
  · intro i;simp [transport]

private theorem compare (P:Ideal RootAmbient) (q:MvPolynomial (Fin 3) SeedField)
    (s:MvPolynomial (Option (Fin 2)) E) (j:SeedField→+*E)
    (scalar:∀ a:FX,j (algebraMap FX SeedField a)=algebraMap FX E a)
    (cut:transport j q∈Ideal.span {s})
    [Module.Finite SeedField (MvPolynomial (Fin 3) SeedField ⧸
      (P.map (MvPolynomial.map (algebraMap FX SeedField))⊔Ideal.span {q}))] :
    Module.Finite E (SectionRing (source P) s) ∧ Module.finrank E (SectionRing (source P) s) ≤
      Module.finrank SeedField (MvPolynomial (Fin 3) SeedField ⧸
        (P.map (MvPolynomial.map (algebraMap FX SeedField))⊔Ideal.span {q})) := by
  letI : Algebra SeedField E:=j.toAlgebra
  apply SliceExtension.length_le _ _ index
  change Ideal.map (transport j) _≤_
  rw [Ideal.map_sup,Ideal.map_map,commutes j scalar,Ideal.map_span,Set.image_singleton]
  apply sup_le
  · rw [←Ideal.map_map]
    exact le_sup_left
  · exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_right cut)

private theorem param_cut : transport parameterField (seedLine (n:=3) 0 1)∈Ideal.span {parameterCut 2} := by
  let c:=sliceVariable (some (0:Fin 2))
  have nz:c≠0:= (map_ne_zero_iff _ (IsFractionRing.injective (SourceRing 2) E)).mpr (MvPolynomial.X_ne_zero _)
  have mx (i:Fin 3):(MvPolynomial.rename index).toRingHom (MvPolynomial.X i:MvPolynomial (Fin 3) E)=
      MvPolynomial.X (index i) := MvPolynomial.rename_X _ _
  have mc (t:E):(MvPolynomial.rename index).toRingHom (MvPolynomial.C t:MvPolynomial (Fin 3) E)=
      MvPolynomial.C t := MvPolynomial.rename_C _ _
  have prod : MvPolynomial.C c * transport parameterField (seedLine (n:=3) 0 1) = parameterCut 2 := by
    simp only [transport,RingHom.comp_apply,seedLine,parameterCut,Fin.sum_univ_two,
      map_sub,map_add,map_mul,MvPolynomial.map_C,MvPolynomial.map_X,mc,mx]
    change MvPolynomial.C c*(MvPolynomial.X (some (0:Fin 2))+MvPolynomial.C (parameterField (generic 0))*MvPolynomial.X (some (1:Fin 2))-
      MvPolynomial.C (parameterField (generic 1)))=_
    calc _ = MvPolynomial.C c*MvPolynomial.X (some (0:Fin 2))+
          MvPolynomial.C (parameterField (generic 0)*c)*MvPolynomial.X (some (1:Fin 2))-
          MvPolynomial.C (parameterField (generic 1)*c) := by simp only [map_mul];ring
      _ = _ := by rw [show parameterField (generic 0)*c=_ from parameter_slope,
                          show parameterField (generic 1)*c=_ from parameter_offset]
  have eq : transport parameterField (seedLine (n:=3) 0 1)=MvPolynomial.C c⁻¹*parameterCut 2 := by
    rw [←prod,←mul_assoc,←map_mul,inv_mul_cancel₀ nz,map_one,one_mul]
  rw [eq]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem ord_cut : transport ordinateField (ySection (n:=3) 2)∈Ideal.span {ordinateCut 2} := by
  have eq:transport ordinateField (ySection (n:=3) 2)=ordinateCut 2 := by
    simp [transport,ySection,ordinateCut,ordinate_coordinate,index]
  rw [eq]
  exact Ideal.mem_span_singleton_self _

/-- The two generic slice hypotheses of the lower-track bidegree cut are
supplied by the actual section lengths of every packet curve. -/
theorem slices (Q:Ideal Ambient) (geom:CurveGeometry Q) :
    SliceBounds (source (rootImage Q)) (seedLength Q) (yLength Q) := by
  obtain ⟨fs,bs,fy,by'⟩:=root_slices Q geom
  let _ : Module.Finite SeedField (RootSeedSection (rootImage Q)):=fs
  let _ : Module.Finite SeedField (RootYSection (rootImage Q)):=fy
  have s:=compare (rootImage Q) (seedLine (n:=3) 0 1) (parameterCut 2) parameterField parameter_scalars param_cut
  have y:=compare (rootImage Q) (ySection (n:=3) 2) (ordinateCut 2) ordinateField ordinate_scalars ord_cut
  exact ⟨s.1,s.2.trans bs,y.1,y.2.trans by'⟩

end
end Research6969.NativeCurveSlices
end Z6969Source0620

-- Source: Research6969.NativeLostCurve
section Z6969Source0621
set_option autoImplicit true
namespace Research6969.NativeLostCurve
noncomputable section
open K1 (K I node p)
open K1_14 (FX atX seedEmbedding)
open K1_14_2 (Ambient RootAmbient OnJet OnRoot rootIncl)
open K1_14_2_2 (CurveGeometry)
open K1_14_2_3 (rootImage seedLength yLength)
open K1_14_2_4 (SourceRing linearIdeal)
open NativeCurveSlices (source index)
open Research6966
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open MvPolynomial Finset
open scoped Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

private theorem curve_dimension (Q:Ideal Ambient) (geom:CurveGeometry Q) :
    (affineHilbertPolynomial Q).natDegree≤1 := by
  let _ : Q.IsPrime:=geom.1
  let A:=Ambient ⧸ Q
  obtain ⟨k,hk,t⟩:=K1_13_6_1_4_2_1_2_2.affineDimension FX A
  have eq:k=1:=by exact_mod_cast hk.symm.trans geom.2.1
  obtain ⟨n,f,hf,finite⟩:=exists_finite_inj_algHom_of_fg FX A
  have dim:(affineHilbertPolynomial Q).natDegree=n:=by
    simpa [Nat.card_fin] using natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective f finite hf
  have nt : Algebra.trdeg FX (MvPolynomial (Fin n) FX)≤Algebra.trdeg FX A := by
    apply trdeg_le_of_injective (R:=FX) (A:=MvPolynomial (Fin n) FX) (A':=A) f
    exact hf
  rw [t] at nt
  have card : (n:Cardinal.{0})≤k := by simpa [Cardinal.mk_fin] using nt
  have ne:n≤k:=by exact_mod_cast card
  exact dim.le.trans (ne.trans_eq eq)

private theorem source_comap (P:Ideal RootAmbient) :
    source P=P.comap (MvPolynomial.renameEquiv FX index).symm.toRingHom := by
  let e:=MvPolynomial.renameEquiv FX index
  have ident:e.toRingEquiv.toRingHom=(MvPolynomial.rename index).toRingHom:=by ext a <;>simp [e]
  calc source P = P.map e.toRingEquiv.toRingHom := congrArg (fun f=>P.map f) ident.symm
    _ = _ := (Ideal.comap_symm (I:=P) e.toRingEquiv).symm

theorem prime_dimension (Q:Ideal Ambient) (geom:CurveGeometry Q) :
    (source (rootImage Q)).IsPrime ∧ (affineHilbertPolynomial (source (rootImage Q))).natDegree≤1 := by
  let e:=MvPolynomial.renameEquiv FX index
  have pr:(rootImage Q).IsPrime:=geom.1.comap rootIncl
  rw [source_comap]
  refine ⟨pr.comap _,?_⟩
  let g:=MvPolynomial.rename (R:=FX) (Fin.castLE (by decide:3≤4))
  let f:(RootAmbient ⧸ rootImage Q)→ₐ[FX](Ambient ⧸ Q):=Ideal.quotientMapₐ Q g le_rfl
  exact (natDegree_affineHilbertPolynomial_comap_of_surjective e.symm.toAlgHom e.symm.surjective
    (rootImage Q)).le.trans ((natDegree_affineHilbertPolynomial_le_of_injective f
    Ideal.quotientMap_injective).trans (curve_dimension Q geom))

abbrev seed:=NativeSurfaceCount.label

private theorem reindex (z₀ z₁ y:FX) :
    OdeEmbedding.point (![z₀,z₁]:Fin 2→FX) y ∘ index=(![z₀,z₁,y]:Fin 3→FX) := by
  funext i;fin_cases i <;> rfl

/-- The actual packet mark lies in the projected curve in the coordinates
of the shortened differential equation. -/
theorem point_on {Q:Ideal Ambient} {z:K} {word:Polynomial K} (mark:OnJet Q z word) :
    OdeEmbedding.point (seed z) (atX word) ∈ zeroLocus FX (source (rootImage Q)) := by
  have root:=K1_14_2_3.on_root mark
  apply mem_zeroLocus_iff_le_ker_aeval.mpr
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  have zero:=RingHom.mem_ker.mp (root hf)
  apply RingHom.mem_ker.mpr
  change MvPolynomial.eval (OdeEmbedding.point (seed z) (atX word)) (MvPolynomial.rename index f)=0
  rw [MvPolynomial.eval_rename]
  have coords : OdeEmbedding.point (seed z) (atX word) ∘ index =
      (![seedEmbedding z,seedEmbedding z^p,atX word]:Fin 3→FX) := reindex _ _ _
  rw [coords]
  exact zero


private theorem rational_points_at_zero {σ:Type*} [Finite σ] {P:Ideal (MvPolynomial σ FX)}
    [P.IsPrime] (dim:(affineHilbertPolynomial P).natDegree=0) (W:Finset (σ→FX))
    (on:∀ x∈W,x∈zeroLocus FX P) : W.card≤1 := by
  have : Module.Finite FX (MvPolynomial σ FX ⧸ P):=natDegree_affineHilbertPolynomial_eq_zero_iff.mp dim
  have mx:P.IsMaximal:=Ideal.Quotient.maximal_of_isField P (IsField.of_isDomain_of_finite FX (MvPolynomial σ FX ⧸ P))
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have exactIdeal (z:σ→FX) (hz:z∈W) : P=RingHom.ker (MvPolynomial.aeval (R:=FX) z) :=
    mx.eq_of_le (RingHom.ker_isPrime _).ne_top (mem_zeroLocus_iff_le_ker_aeval.mp (on z hz))
  funext j
  have atx : MvPolynomial.X j-MvPolynomial.C (x j)∈RingHom.ker (MvPolynomial.aeval (R:=FX) x) :=
    RingHom.mem_ker.mpr (by simp)
  rw [←exactIdeal x hx,exactIdeal y hy] at atx
  have eq:=RingHom.mem_ker.mp atx
  simpa [sub_eq_zero,eq_comm] using eq

/-- The regular marks on one of the actual discarded curves cost its native
seed and ordinate section lengths, with the shortened ODE coefficients. -/
theorem regular_count {u₀:P1.Words} {deleted:Finset I} {maxHeight a d r U:ℕ}
    {M:P1.ModelAt maxHeight u₀ deleted} {Γ T:Finset K} (F:P1.FamilyAt a M Γ) (sub:T⊆Γ)
    (Q:Ideal Ambient) (geom:CurveGeometry Q) (marks:∀z∈T,OnJet Q (M.label z) (F.scalar z))
    (rp:1≤r) (up:0<U) (dp:0<d) (gap:d<a) (possible:a≤Fintype.card I) (tame:d<p)
    (A B:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:cap (fun _=>1) U A) (bz:cap (fun _=>1) U B)
    (deg:∀z∈T,(F.scalar z).natDegree≤d)
    (law:∀ z∈T,evaluate (seed (M.label z)) (atX (F.scalar z)) A * atX (F.scalar z).derivative =
      evaluate (seed (M.label z)) (atX (F.scalar z)) B)
    (regular:∀ z∈T,evaluate (seed (M.label z)) (atX (F.scalar z)) A≠0) :
    (T.card:ℚ)≤((U*seedLength Q+r*yLength Q:ℕ):ℚ)*MarkedAdaptive.price (Fintype.card I) d a := by
  classical
  let J:=source (rootImage Q)
  let P:=linearIdeal r U J
  have ⟨prim,dim⟩:=prime_dimension Q geom
  change (affineHilbertPolynomial J).natDegree≤1 at dim
  have : P.IsPrime:=prim.comap (bidegreeMap (Fin 2) FX r U)
  have projdim : (affineHilbertPolynomial P).natDegree=(affineHilbertPolynomial J).natDegree :=
    natDegree_affineHilbertPolynomial_comap_bidegreeMap rp up _
  let encode (z:K):MarkedAdaptive.Coordinates r U:=monomialPoint (bidegreeExponents (Fin 2) r U)
    (OdeEmbedding.point (seed (M.label z)) (atX (F.scalar z)))
  have inject:Function.Injective encode:=by
    intro x y same
    have eq:=monomialPoint_injective (fun i=>single_mem_bidegreeExponents rp up i) (show encode x=encode y from same)
    have e:M.label x=M.label y:=seedEmbedding.injective (congrFun eq (some 0))
    exact sub_left_injective (b:=M.shift) e
  let W:=T.image encode
  let back:=Function.invFun encode
  have inverse (z:K):back (encode z)=z:=Function.leftInverse_invFun inject z
  have selected {x} (hx:x∈W):back x∈T ∧ encode (back x)=x := by
    obtain ⟨z,mem,rfl⟩:=mem_image.mp hx
    rw [inverse];exact ⟨mem,rfl⟩
  have on {x} (hx:x∈W):x∈zeroLocus FX P:=by
    intro f hf
    obtain ⟨z,mem,rfl⟩:=mem_image.mp hx
    change aeval (monomialPoint _ _) f=0
    rw [aeval_monomialPoint,←bidegreeMap_eq_monomialMap r U]
    exact point_on (marks z mem) _ hf
  have one:1≤MarkedAdaptive.price (Fintype.card I) d a:=by
    rw [MarkedAdaptive.price,le_div_iff₀ (by exact_mod_cast dp.trans gap : (0:ℚ)<a),one_mul]
    exact_mod_cast (show a≤2*Fintype.card I*d from
      possible.trans ((Nat.le_mul_of_pos_left _ (by decide:0<2)).trans (Nat.le_mul_of_pos_right _ dp)))
  rw [←show W.card=T.card from card_image_of_injective _ inject]
  by_cases zero:(affineHilbertPolynomial P).natDegree=0
  · have only:=rational_points_at_zero zero W (fun _ hx=>on hx)
    have pos:0<U*seedLength Q := Nat.mul_pos up geom.2.2.2.1
    have fee:1≤U*seedLength Q+r*yLength Q := by omega
    exact (by exact_mod_cast only : (W.card:ℚ)≤1).trans (by
      simpa using mul_le_mul (by exact_mod_cast fee : (1:ℚ)≤_) one (by norm_num) (by positivity))
  have hdim:(affineHilbertPolynomial J).natDegree=1:=by omega
  have bound:=P0_10R.Bridge.root_embedding 2 r U (seedLength Q) (yLength Q) rp up J prim hdim (NativeCurveSlices.slices Q geom)
  have report:=MarkedAdaptive.supplies_tests rp dp gap tame A B ay byDeg az bz W
    (fun x=>F.scalar (back x)) (fun x=>seed (M.label (back x))) M.word (fun _ h=>(selected h).2.symm)
    (by intro x hx y hy eq
        exact (selected hx).2.symm.trans ((congrArg encode (F.distinct (sub (selected hx).1)
          (sub (selected hy).1) eq)).trans (selected hy).2))
    (fun _ hx=>deg _ (selected hx).1) (fun _ _=>NativeSurfaceCount.label_fixed _)
    (fun _ hx=>law _ (selected hx).1) (fun _ hx=>regular _ (selected hx).1) (by
      intro x hx
      let m:=F.mark _ (sub (selected hx).1)
      refine m.bad.agreement.trans (card_le_card ?_)
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _,m.scalar_hits i hi⟩)
  have total:=AdaptiveIncidence.prime_count W one report P W (fun _ h=>h) (fun _ hx=>on hx)
  rw [projdim,hdim,pow_one] at total
  exact total.trans (mul_le_mul_of_nonneg_right bound (zero_le_one.trans one))

end
end Research6969.NativeLostCurve
end Z6969Source0621

-- Source: Research6969.NativeLostCut
section Z6969Source0622
set_option autoImplicit true
namespace Research6969.NativeLostCurve
noncomputable section
open K1 (K I p)
open K1_14 (FX atX)
open K1_14_2 (Ambient OnJet)
open K1_14_2_2 (CutCover)
open K1_14_2_3 (seedLength yLength union_card_le)
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open Finset
open scoped Classical Differential
attribute [local instance] Research6966.GenericPhysicalCentre.physical Research6966.GenericPhysicalCentre.seeds

/-- Price all regular discarded-curve marks in one actual prefix cut,
including a mark when it belongs to more than one component. -/
theorem cut_count {u₀:P1.Words} {deleted:Finset I} {maxHeight a d r U:ℕ}
    {M:P1.ModelAt maxHeight u₀ deleted} {Γ T:Finset K} (F:P1.FamilyAt a M Γ) (sub:T⊆Γ)
    (C:CutCover) (cover:∀ z∈T, ∃ Q∈C.curves, OnJet Q (M.label z) (F.scalar z))
    (rp:1≤r) (up:0<U) (dp:0<d) (gap:d<a) (possible:a≤Fintype.card I) (tame:d<p)
    (A B:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:cap (fun _=>1) U A) (bz:cap (fun _=>1) U B)
    (deg:∀z∈T,(F.scalar z).natDegree≤d)
    (law:∀z∈T,evaluate (seed (M.label z)) (atX (F.scalar z)) A * atX (F.scalar z).derivative =
      evaluate (seed (M.label z)) (atX (F.scalar z)) B)
    (regular:∀z∈T,evaluate (seed (M.label z)) (atX (F.scalar z)) A≠0) :
    (T.card:ℚ)≤((U*C.cost 0+r*C.cost 1:ℕ):ℚ)*MarkedAdaptive.price (Fintype.card I) d a := by
  classical
  let S (Q:Ideal Ambient):=T.filter fun z=>OnJet Q (M.label z) (F.scalar z)
  have inside:T ⊆ C.curves.biUnion S:=by
    intro z hz
    obtain ⟨Q,hQ,hit⟩:=cover z hz
    exact mem_biUnion.mpr ⟨Q,hQ,mem_filter.mpr ⟨hz,hit⟩⟩
  have localFee (Q:Ideal Ambient) (hQ:Q∈C.curves) :
      ((S Q).card:ℚ)≤((U*seedLength Q+r*yLength Q:ℕ):ℚ)*MarkedAdaptive.price (Fintype.card I) d a := by
    have part:S Q⊆T:=filter_subset _ _
    exact regular_count F (part.trans sub) Q (C.geometric Q hQ) (fun _ hz=>(mem_filter.mp hz).2)
      rp up dp gap possible tame A B ay byDeg az bz (fun _ hz=>deg _ (part hz))
      (fun _ hz=>law _ (part hz)) (fun _ hz=>regular _ (part hz))
  calc
    (T.card:ℚ) ≤ ((C.curves.biUnion S).card:ℚ) := by exact_mod_cast card_le_card inside
    _ ≤ _ := union_card_le _ _
    _ ≤ ∑ Q∈C.curves, ((U*seedLength Q+r*yLength Q:ℕ):ℚ)*MarkedAdaptive.price (Fintype.card I) d a :=
      sum_le_sum localFee
    _ = _ := by
      rw [←sum_mul]
      congr 1
      push_cast
      simp only [sum_add_distrib,←mul_sum,←Nat.cast_sum]
      rfl

end
end Research6969.NativeLostCurve
end Z6969Source0622
