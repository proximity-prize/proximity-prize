import ProximityPrize.SubmissionLower.ZcWZWSa
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, Function.Injective → zq4, Function.Surjective → zpX, Ideal.Quotient.lift → zP2, Ideal.Quotient.mk → zVv, IsFractionRing.div_surjective → zJC, IsFractionRing.injective → zxb, IsScalarTower.algebraMap_apply → zG3, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom_C → zTv, Polynomial → zM1, Polynomial.C → z1z, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, RingHom.map_add → z9O, RingHom.map_mul → zsF
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qnwFNhd
noncomputable section
open cu (FX aZ)
open gT (Ambient aQ gk ek B4)
open YY (aef)
open P6 (p)
open qcYgGze
open private B6 i9 extend parameters c3E cbp eJ7 bd9 aH0 eJ9 from ProximityPrize.SubmissionLower.U
theorem sep_small {F E :Type} [Field F] [Field E] [zZE F E] {q:ℕ} [CharP F q]
    [zAa F E] (hsize :zsE F E<q) :zw7 F E := by
  refine ⟨fun a => ?_⟩
  have ha :IsIntegral F a :=Algebra.IsIntegral.isIntegral a
  let pp:=minpoly F a
  have hpos :0<pp.natDegree :=minpoly.natDegree_pos ha
  have hlt:pp.natDegree<q:=(minpoly.natDegree_le a).trans_lt hsize
  have hcast: (pp.natDegree :F)≠0:= by
    intro hz
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff F q _).mp hz))
  change pp.Separable
  apply (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible ha)).2
  intro hzero
  obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hcoeff :=congrArg (fun r :zM1 F=>r.coeff n) hzero
  change pp.derivative.coeff n=(0:zM1 F).coeff n at hcoeff
  have hmonic:pp.coeff pp.natDegree=1 :=(minpoly.monic ha).leadingCoeff
  rw [hn] at hmonic
  rw [Polynomial.coeff_derivative,Polynomial.coeff_zero,← Nat.cast_succ,
    ← hn,hmonic,one_mul] at hcoeff
  exact hcast hcoeff
theorem abstract_range {S E J:Type} [Field S] [Field E] [CommRing J] [zZE S J]
    [zAa S J] (σ:S →+* E) (φ:J →+* E) (hφ : ∀ s,φ (algebraMap S J s)=σ s) :
    ∀ e∈φ.range,e⁻¹∈φ.range := by
  letI:zZE S E :=σ.toAlgebra
  let φA:J →ₐ[S] E := { φ with commutes' := hφ }
  intro e he
  obtain ⟨j,rfl⟩:=he
  have hint :IsIntegral S (φ j) :=
    ((Algebra.IsIntegral.of_finite S J).isIntegral j).map φA
  have :=(φA.range).inv_mem_of_algebraic (x :=⟨φ j,j,rfl⟩) hint.isAlgebraic
  obtain ⟨k,hk⟩:=this
  exact ⟨k,hk⟩
theorem abstract_sep {q:ℕ} {FX S E J:Type} [Field FX] [Field S] [Field E] [CommRing J]
    [zZE FX S] [zZE FX E] [zZE S J] [zAa S J] [CharP FX q]
    (σ:S →ₐ[FX] E) (φ:J →+* E) (hφ : ∀ s,φ (algebraMap S J s)=σ s)
    (hsurj:zpX φ) (hlt:zsE S J<q) :
    zw7 σ.fieldRange E := by
  letI:zZE S E :=σ.toRingHom.toAlgebra
  let φA:J →ₐ[S] E := { φ with commutes' := hφ }
  have hEfin:zAa S E :=Module.Finite.of_surjective φA.toLinearMap hsurj
  have hle :zsE S E≤zsE S J :=
    LinearMap.finrank_le_finrank_of_surjective (f :=φA.toLinearMap) hsurj
  let e :S ≃ₐ[FX] σ.fieldRange :=AlgEquiv.ofInjectiveField σ
  have hrank :zsE S E=zsE σ.fieldRange E := by
    unfold zsE
    rw [rank_eq_of_equiv_equiv e (AddEquiv.refl E) e.bijective (fun r m=>rfl)]
  have hpos :0<zsE S E :=Module.finrank_pos
  haveI:zAa σ.fieldRange E :=Module.finite_of_finrank_pos (hrank ▸ hpos)
  haveI:CharP σ.fieldRange q:=charP_of_injective_algebraMap (algebraMap FX σ.fieldRange).injective q
  exact sep_small (hrank ▸ (hle.trans_lt hlt))
section
variable (I:Ideal Ambient) [I.IsPrime]
def ιb:gk I →+* CurveResidue I :=
  zP2 I (algebraMap Ambient (CurveResidue I))
    (fun _ ha=>Ideal.algebraMap_residueField_eq_zero.mpr ha)
theorem ιb_inj:zq4 (ιb I) :=
  Ideal.injective_algebraMap_quotient_residueField I
def πm:zM1 (gk I) →+* SlopedResidue I :=
  (algebraMap (zM1 (CurveResidue I)) (SlopedResidue I)).comp
    (Polynomial.mapRingHom (ιb I))
theorem πm_inj:zq4 (πm I) :=
  (zxb (zM1 (CurveResidue I)) (SlopedResidue I)).comp
    (Polynomial.map_injective _ (ιb_inj I))
theorem πm_C (x :gk I) :πm I (z1z x) =
    algebraMap (zM1 (CurveResidue I)) (SlopedResidue I) (z1z (ιb I x)) := by
  simp [πm]
theorem πm_X:πm I Polynomial.X=qcYgGze.slope I:= by
  simp [πm,qcYgGze.slope]
theorem seedValue_eq (i:Fin 2) :seedValue I i =
    ιb I (zVv I (z9v (Fin.castAdd 2 i))) :=rfl
abbrev fm:aZ →ₐ[FX] zM1 (gk I) :=
  parameters (zVv I (z9v 0)) (zVv I (z9v 1))
theorem πm_y :πm I (fm I (z9v 1)) =
    algebraMap (zM1 (CurveResidue I)) (SlopedResidue I) (seedOnSlope I) := by
  have h0:seedValue I 0=ιb I (zVv I (z9v 0)) :=seedValue_eq I 0
  have h1 :seedValue I 1=ιb I (zVv I (z9v 1)) :=seedValue_eq I 1
  rw [fm,cbp,(πm I).map_add,(πm I).map_mul,πm_C,πm_C,πm_X]
  change _=algebraMap (zM1 (CurveResidue I)) (SlopedResidue I)
    (z1z (seedValue I 0)+Polynomial.X*z1z (seedValue I 1))
  rw [z9O,zsF,h0,h1]
  rfl
theorem πm_x :πm I (fm I (z9v 0))=slope I:= by
  rw [fm,c3E,πm_X]
theorem tau_inj (hnt:Nontrivial (B6 I (z9v 0) (z9v 1))) :
    zq4 ((πm I).comp (fm I).toRingHom) := by
  intro x y hxy
  have h1 :=πm_inj I hxy
  have h2 :=congrArg (aH0 I (z9v 0) (z9v 1)) h1
  have hc:=zLs (eJ9 I (z9v 0) (z9v 1)) x
  have hc' := zLs (eJ9 I (z9v 0) (z9v 1)) y
  have h3:=(algebraMap aQ (B6 I (z9v 0) (z9v 1))).injective
    (hc.symm.trans (h2.trans hc'))
  exact zxb aZ aQ h3
variable (hinj:zq4 ((πm I).comp (fm I).toRingHom))
def sg:aQ →+* SlopedResidue I:=IsFractionRing.lift hinj
theorem sg_alg (d:aZ) :sg I hinj (algebraMap aZ aQ d)=πm I (fm I d) :=
  IsFractionRing.lift_algebraMap _ d
def ev :MvPolynomial (Fin 4) aQ →+* SlopedResidue I :=
  MvPolynomial.eval₂Hom (sg I hinj)
    (fun i=>πm I (z1z (zVv I (z9v i))))
theorem ev_extend: (ev I hinj).comp extend =
    ((πm I).comp z1z).comp (zVv I) := by
  apply MvPolynomial.ringHom_ext
  · intro d
    have hd:algebraMap FX aQ d=algebraMap aZ aQ (znf d) :=rfl
    simp only [ev,zQb,MvPolynomial.map_C,zTv,hd,
      sg_alg]
    exact congrArg (πm I) ((fm I).commutes d)
  · intro i
    simp only [ev,zQb,MvPolynomial.map_X,MvPolynomial.eval₂Hom_X']
theorem ev_ker :i9 I (z9v 0) (z9v 1)≤RingHom.ker (ev I hinj) := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
  · intro r hr
    change (ev I hinj).comp extend r=0
    rw [ev_extend]
    change πm I (z1z (zVv I r))=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr,map_zero,map_zero]
  · intro r hr
    obtain rfl :=Set.mem_singleton_iff.mp hr
    apply (RingHom.sub_mem_ker_iff _).mpr
    have hu:=zLs (ev_extend I hinj) (z9v 0)
    have hv :=zLs (ev_extend I hinj) (z9v 1)
    change ev I hinj (extend (z9v 0)) =
      πm I (z1z (zVv I (z9v 0))) at hu
    change ev I hinj (extend (z9v 1)) =
      πm I (z1z (zVv I (z9v 1))) at hv
    have hC (i:Fin 2) :ev I hinj (znf (ek i))=πm I (fm I (z9v i)) :=
      (zTv _ _ _).trans (sg_alg I hinj _)
    rw [z9O,zsF,hu,hv,hC 0,hC 1]
    have e0:fm I (z9v 0)=Polynomial.X:=c3E _ _
    have e1 :=cbp (zVv I (z9v 0))
      (zVv I (z9v 1))
    change fm I (z9v 1)= _ at e1
    rw [e0,e1,(πm I).map_add,(πm I).map_mul,πm_X]
def phi:B6 I (z9v 0) (z9v 1) →+* SlopedResidue I :=
  zP2 _ (ev I hinj) (fun _ ha=>ev_ker I hinj ha)
theorem phi_base (x :gk I) :phi I hinj
    (bd9 I (z9v 0) (z9v 1) x)=πm I (z1z x) := by
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  have h:bd9 I (z9v 0) (z9v 1) (zVv I a) =
    zVv _ (extend a) :=Ideal.quotientMap_mk
  rw [h]
  exact zLs (ev_extend I hinj) a
theorem phi_alg (s :aQ) :phi I hinj
    (algebraMap aQ (B6 I (z9v 0) (z9v 1)) s)=sg I hinj s := by
  rw [← Ideal.Quotient.mk_algebraMap]
  exact zTv _ _ s
theorem ιb_mk (a :Ambient) :ιb I (zVv I a) =
    IsLocalRing.residue (Localization.AtPrime I) (algebraMap Ambient (Localization.AtPrime I) a) :=
  rfl
theorem ιb_frac (c:CurveResidue I) :
    ∃ x y :gk I,ιb I y≠0∧c*ιb I y=ιb I x := by
  obtain ⟨z,rfl⟩:=IsLocalRing.residue_surjective c
  obtain ⟨x,⟨s,hs⟩,rfl⟩:=IsLocalization.exists_mk'_eq I.primeCompl z
  refine ⟨zVv I x,zVv I s,?_,?_⟩
  · rw [ιb_mk,Ne,IsLocalRing.residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime I) I]
    exact hs
  · rw [ιb_mk,ιb_mk,← zsF,IsLocalization.mk'_spec]
theorem ιb_alg (c:FX) :
    ιb I (algebraMap FX (gk I) c)=algebraMap FX (CurveResidue I) c:= by
  rw [zG3 FX Ambient (CurveResidue I)]
  rfl
theorem tau_C (c:FX) :πm I (fm I (znf c))=algebraMap FX (SlopedResidue I) c:= by
  have h1 :fm I (znf c)=z1z (algebraMap FX (gk I) c) :=
    eJ7 _ _ c
  rw [h1,πm_C,ιb_alg,zG3 FX (zM1 (CurveResidue I))
    (SlopedResidue I),Polynomial.algebraMap_apply]
theorem tau_mem (a :aZ) :πm I (fm I a)∈SeedParameterField I:= by
  have hx (i:Fin 2) :πm I (fm I (z9v i))∈SeedParameterField I:= by
    obtain rfl | rfl :i=0∨i=1 := by fin_cases i <;> decide
    · rw [πm_x]
      exact IntermediateField.subset_adjoin FX _ ⟨0,rfl⟩
    · rw [πm_y]
      exact IntermediateField.subset_adjoin FX _ ⟨1,rfl⟩
  induction a using MvPolynomial.induction_on with
  | C c=>rw [tau_C]; exact IntermediateField.algebraMap_mem _ c
  | add p q hp hq=>rw [map_add (fm I),(πm I).map_add]; exact add_mem hp hq
  | mul_X p i hp=>rw [map_mul (fm I),(πm I).map_mul]; exact mul_mem hp (hx i)
theorem sg_FX (c:FX) :sg I hinj (algebraMap FX aQ c)=algebraMap FX (SlopedResidue I) c:= by
  have hd:algebraMap FX aQ c=algebraMap aZ aQ (znf c) :=rfl
  rw [hd,sg_alg,tau_C]
theorem sg_gen0:sg I hinj (ek 0)=slope I :=
  (sg_alg I hinj (z9v 0)).trans (πm_x I)
theorem sg_gen1 :sg I hinj (ek 1) =
    algebraMap (zM1 (CurveResidue I)) (SlopedResidue I) (seedOnSlope I) :=
  (sg_alg I hinj (z9v 1)).trans (πm_y I)
theorem core (hnt:Nontrivial (B6 I (z9v 0) (z9v 1)))
    (hfin:zAa aQ (B6 I (z9v 0) (z9v 1)))
    (hlt:zsE aQ (B6 I (z9v 0) (z9v 1))<p) :
    zw7 (SeedParameterField I) (SlopedResidue I) := by
  have hinj:=tau_inj I hnt
  have hinv :=abstract_range (J:=B6 I (z9v 0) (z9v 1))
    (sg I hinj) (phi I hinj) (phi_alg I hinj)
  let K:Subfield (SlopedResidue I) := { (phi I hinj).range with inv_mem' := fun e he=>hinv e he }
  have hbase (x :gk I) :πm I (z1z x)∈K :=
    ⟨bd9 I _ _ x,phi_base I hinj x⟩
  have ht:slope I∈K:=⟨algebraMap aQ _ (ek 0),
    (phi_alg I hinj (ek 0)).trans (sg_gen0 I hinj)⟩
  have hκ (c:CurveResidue I) :
      algebraMap (zM1 (CurveResidue I)) (SlopedResidue I) (z1z c)∈K:= by
    obtain ⟨x,y,hy,hxy⟩:=ιb_frac I c
    have hy' : πm I (z1z y)≠0:= fun h=> by
      have h1 :z1z y=0:=πm_inj I (h.trans (πm I).map_zero.symm)
      apply hy
      rw [Polynomial.C_eq_zero.mp h1,RingHom.map_zero]
    have key :algebraMap (zM1 (CurveResidue I)) (SlopedResidue I) (z1z c) *
        πm I (z1z y)=πm I (z1z x) := by
      rw [πm_C,πm_C,← zsF,← Polynomial.C_mul,hxy]
    rw [(eq_mul_inv_iff_mul_eq₀ hy').mpr key]
    exact mul_mem (hbase x) (inv_mem (hbase y))
  have hpoly (q:zM1 (CurveResidue I)) :
      algebraMap (zM1 (CurveResidue I)) (SlopedResidue I) q∈K:= by
    refine Polynomial.induction_on' q (fun p q hp hq => ?_) (fun n a => ?_)
    · rw [z9O]
      exact add_mem hp hq
    · rw [← Polynomial.C_mul_X_pow_eq_monomial,zsF,RingHom.map_pow]
      exact mul_mem (hκ a) (pow_mem (show algebraMap (zM1 (CurveResidue I))
        (SlopedResidue I) Polynomial.X∈K from ht) n)
  have hsurj:zpX (phi I hinj) := fun e=> by
    obtain ⟨a,b,hb,rfl⟩:=zJC (A:=zM1 (CurveResidue I)) e
    exact div_mem (hpoly a) (hpoly b)
  let gA:aQ →ₐ[FX] SlopedResidue I := { sg I hinj with commutes' := sg_FX I hinj }
  have hF:SeedParameterField I=gA.fieldRange := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i,rfl⟩
      obtain rfl | rfl :i=0∨i=1 := by fin_cases i <;> decide
      · exact ⟨ek 0,sg_gen0 I hinj⟩
      · exact ⟨ek 1,sg_gen1 I hinj⟩
    · intro x hx
      obtain ⟨s,rfl⟩:=(AlgHom.mem_fieldRange).mp hx
      obtain ⟨a,b,hb,rfl⟩:=zJC (A:=aZ) s
      change sg I hinj _∈_
      rw [map_div₀,sg_alg,sg_alg]
      exact div_mem (tau_mem I a) (tau_mem I b)
  rw [hF]
  haveI:=hfin
  haveI:CharP FX p:=charP_of_injective_ringHom cu.jz.injective p
  exact abstract_sep (J:=B6 I (z9v 0) (z9v 1)) gA (phi I hinj) (phi_alg I hinj) hsurj hlt
end
theorem proof :qcYgGze.c1 := by
  intro I hI hdim hMove hlt
  obtain ⟨hSfin,hSpos,-⟩:=cy6.proof I hI hdim hMove
  have hseed :i9 I (z9v 0) (z9v 1) =
      I.map extend ⊔ Ideal.span {B4 0 1} := by
    simp [i9,B4]
  have hfin:zAa aQ (B6 I (z9v 0) (z9v 1)) := by
    change zAa aQ (_ ⧸ i9 I (z9v 0) (z9v 1))
    rw [hseed]
    exact hSfin
  have hrank :zsE aQ (B6 I (z9v 0) (z9v 1)) =
      aef I:= by
    change zsE aQ (_ ⧸ i9 I (z9v 0) (z9v 1)) =
      zsE aQ (_ ⧸ (I.map extend ⊔ Ideal.span {B4 0 1}))
    rw [hseed]
  have hnt:Nontrivial (B6 I (z9v 0) (z9v 1)) :=
    Module.nontrivial_of_finrank_pos (R:=aQ) (hrank ▸ hSpos)
  exact core I hnt hfin (hrank ▸ hlt)
end
end qnwFNhd
