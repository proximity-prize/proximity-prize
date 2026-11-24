import ProximityPrize.SubmissionLower.R6960ChartIntegrality
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import ProximityPrize.SubmissionLower.R6960CollisionTameDiscriminant
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.Polynomial.Bivariate

-- merged module R6960CollisionTameFrames
section Merged_R6960CollisionTameFrames
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Module Submodule
open scoped Polynomial Pointwise BigOperators
section Lifts
variable {A K M N ι : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A]
  [CommRing K] [Nontrivial K] [AddCommGroup M] [Module A M] [Module.Finite A M]
  [Module.IsTorsionFree A M] [AddCommGroup N] [Module K N] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem lift_fibre_frame (a : A) (an : a≠0) (j : A→+*K) (jon : Function.Surjective j)
    (jker : ∀ u,j u=0 ↔ a∣u) (red : M→+N) (redon : Function.Surjective red)
    (redker : ∀ x,red x=0 ↔ ∃ y,x=a • y)
    (redsmul : ∀ r x,red (r • x)=j r • red x) (b : Basis ι K N) :
    ∃ (u : ι→M) (g : A) (f : (ι→A)→ₗ[A]M),
      (∀ i,red (u i)=b i) ∧ (∀ t,f t=∑ i,t i • u i) ∧
      Function.Injective f ∧ j g=1 ∧ ∀ x : M,∃ t,f t=g • x := by
  classical
  choose u hu using fun i=>redon (b i)
  let B := Pi.basisFun A ι
  let f := B.constr A u
  have sum (t : ι→A) : f t=∑ i,t i • u i := by
    rw [show f=B.constr A u from rfl,Basis.constr_apply_fintype]
    rfl
  have reduce (t : ι→A) : red (f t)=∑ i,j (t i) • b i := by
    rw [sum,map_sum]
    exact Finset.sum_congr rfl fun i _=>by rw [redsmul,hu]
  have aj : j a=0 := (jker a).mpr (dvd_refl a)
  have nonunit : ¬IsUnit a := fun u=>not_isUnit_zero (aj ▸ u.map j)
  have ker (t : ι→A) (ft : f t=0) : ∀ i,a∣t i := by
    have zero := reduce t
    rw [ft,map_zero] at zero
    exact fun i=>(jker _).mp (Fintype.linearIndependent_iff.mp b.linearIndependent _ zero.symm i)
  have inj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro t ft
    have divisibility (n : ℕ) : ∃ v : ι→A, t=a^n • v ∧ f v=0 := by
      induction n with
      | zero => exact ⟨t,by simp,ft⟩
      | succ n ih =>
        obtain ⟨v,tv,fv⟩ := ih
        choose w hw using ker v fv
        have eq : v=a • w := funext hw
        have fw : f w=0 := by
          rw [eq,f.map_smul] at fv
          exact (smul_eq_zero_iff_right an).mp fv
        exact ⟨w,by rw [tv,eq,smul_smul,pow_succ],fw⟩
    funext i
    by_contra ni
    obtain ⟨n,nf⟩ := FiniteMultiplicity.of_not_isUnit nonunit ni
    obtain ⟨v,tv,_⟩ := divisibility (n+1)
    exact nf ⟨v i,congrFun tv i⟩
  have generates : (⊤ : Submodule A M)≤f.range⊔Ideal.span {a} • (⊤ : Submodule A M) := by
    intro x _
    choose c hc using fun i=>jon (b.equivFun (red x) i)
    have rep := b.equivFun.symm_apply_apply (red x)
    rw [Basis.equivFun_symm_apply] at rep
    have eq : red (f c)=red x := by
      rw [reduce]
      exact (Finset.sum_congr rfl fun i _=>by rw [hc]).trans rep
    obtain ⟨y,hy⟩ := (redker (x-f c)).mp (by rw [map_sub,eq,sub_self])
    refine Submodule.mem_sup.mpr ⟨f c,⟨c,rfl⟩,a • y,?_,?_⟩
    · rw [Submodule.ideal_span_singleton_smul]
      exact Submodule.smul_mem_pointwise_smul y a ⊤ Submodule.mem_top
    · rw [←hy]; abel
  have fg : (⊤ : Submodule A M).FG := Module.finite_def.mp inferInstance
  obtain ⟨g,gone,clear⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup fg le_rfl generates
  have eg : j g=1 := by
    have zero := (jker (g-1)).mpr (Ideal.mem_span_singleton.mp gone)
    rwa [map_sub,map_one,sub_eq_zero] at zero
  refine ⟨u,g,f,hu,sum,inj,eg,?_⟩
  intro x
  exact clear (Submodule.smul_mem_pointwise_smul x g ⊤ Submodule.mem_top)
end Lifts
section Localization
variable {A R M P ι : Type*} [CommRing A] [CommRing R] [Algebra A R]
  [AddCommMonoid M] [Module A M] [AddCommMonoid P] [Module A P] [Module R P]
  [IsScalarTower A R P] [Fintype ι] [DecidableEq ι]
theorem localized_fibre_frame (S : Submonoid A) [IsLocalization S R]
    (j : M→ₗ[A]P) [IsLocalizedModule S j] (jinj : Function.Injective j)
    (f : (ι→A)→ₗ[A]M) (finj : Function.Injective f) (g : S)
    (clear : ∀ x : M,∃ t,f t=(g:A) • x) :
    ∃ b : Basis ι R P,∀ i,b i=j (f (Pi.single i 1)) := by
  let h := j.comp f
  let : IsLocalizedModule S h := {
    map_units := IsLocalizedModule.map_units j
    surj := fun y=>by
      obtain ⟨⟨x,s⟩,hy⟩ := IsLocalizedModule.surj S j y
      obtain ⟨t,ht⟩ := clear x
      refine ⟨⟨t,g*s⟩,?_⟩
      change ((g:A)*(s:A)) • y=j (f t)
      rw [mul_smul,ht,map_smul]
      exact congrArg ((g:A) • ·) hy
    exists_of_eq := fun eq=>⟨1,congrArg (fun x : ι→A=>(1:A) • x) (finj (jinj eq))⟩ }
  let b := (Pi.basisFun A ι).ofIsLocalizedModule R S h
  refine ⟨b,fun i=>?_⟩
  rw [show b=(Pi.basisFun A ι).ofIsLocalizedModule R S h from rfl,
    Basis.ofIsLocalizedModule_apply,Pi.basisFun_apply]
  rfl
end Localization
section Actual
open Lower6960.NormalizedFiber (specialize)
open Polynomial NormalizedFiber
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]
theorem scalar_fibre_frame (z : k) :
    let : Module (Polynomial k) (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
    ∃ (n : ℕ) (b : Basis (Fin n) (Polynomial k) (Fiber E z)) (u : Fin n→Order k E) (g : Plane k)
      (f : (Fin n→Plane k) →ₗ[Plane k] Order k E),
      (∀ i,quotientMap E z (u i)=b i) ∧ (∀ t,f t=∑ i,t i • u i) ∧
      Function.Injective f ∧ g.eval (C z)=1 ∧ ∀ x : Order k E,∃ t,f t=g • x := by
  classical
  let : Module (Polynomial k) (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
  obtain ⟨fin,free⟩ := NormalizedFiber.finite_free E z
  let b := Module.finBasis (Polynomial k) (Fiber E z)
  let A := Plane k
  let M := Order k E
  let a : A := Polynomial.X-C (C z)
  let j : A→+*(Polynomial k) := evalRingHom (C z)
  have an : a≠0 := X_sub_C_ne_zero _
  have onto : Function.Surjective j := fun q=>⟨C q,eval_C⟩
  have jker (p : A) : j p=0 ↔ a∣p := by
    exact dvd_iff_isRoot.symm
  have redon := quotientMap_surjective E z
  have redker (x : M) : quotientMap E z x=0 ↔ ∃ y,x=a • y := by
    change (Ideal.Quotient.mk (sliceIdeal E z) x=0) ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change x∈Ideal.span {algebraMap A M a} ↔ _
    rw [Ideal.mem_span_singleton]
    simp only [dvd_def,Algebra.smul_def]
  have sc (r : A) (x : M) : quotientMap E z (r • x)=j r • quotientMap E z x := by
    rw [Algebra.smul_def,map_mul]
    change quotientMap E z (algebraMap A M r)*quotientMap E z x=baseMap E z (r.eval (C z))*quotientMap E z x
    exact congrArg (·*quotientMap E z x) (Lower6960.NormalizedFiber.specialize E z r)
  let : Module.Finite A M :=
    IsIntegralClosure.finite A (FractionRing A) E M
  have inj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) E]
    exact (algebraMap (FractionRing A) E).injective.comp (IsFractionRing.injective A (FractionRing A))
  let : Module.IsTorsionFree A E := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r x eq
    rw [Algebra.smul_def,mul_eq_zero] at eq
    exact eq.imp (fun hr=>inj (hr.trans (map_zero _).symm)) id
  let : Module.IsTorsionFree A M := inferInstanceAs (Module.IsTorsionFree (Plane k) (Order k E))
  obtain ⟨u,g,f,h1,h2,h3,h4,h5⟩ := lift_fibre_frame (M:=M) (N:=Fiber E z) a an j onto jker (quotientMap E z).toAddMonoidHom
    redon redker sc b
  exact ⟨_,b,u,g,f,h1,h2,h3,h4,h5⟩
theorem scalar_fibre_away_basis (z : k) :
    ∃ (g : Plane k) (n : ℕ) (u : Fin n→Order k E)
      (b : Basis (Fin n) (Localization.Away g) (LocalizedModule.Away g (Order k E))),
      g.eval (C z)=1 ∧
      ∀ i,b i=LocalizedModule.mkLinearMap (Submonoid.powers g) (Order k E) (u i) := by
  classical
  let : Module (Polynomial k) (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
  obtain ⟨n,_,u,g,f,_,sum,inj,one,clear⟩ := scalar_fibre_frame (E:=E) z
  let A := Plane k
  let B := Order k E
  let S := Submonoid.powers g
  let j := LocalizedModule.mkLinearMap S B
  have gn : g≠0 := by
    intro zero
    rw [zero,eval_zero] at one
    exact zero_ne_one one
  have baseInj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) E]
    exact (algebraMap (FractionRing A) E).injective.comp (IsFractionRing.injective A _)
  have jinj : Function.Injective j := by
    apply (IsLocalizedModule.injective_iff_isRegular S j).mpr
    rintro ⟨_,m,rfl⟩ x y same
    apply Subtype.ext
    have mne : algebraMap A E (g^m)≠0 := (map_ne_zero_iff _ baseInj).mpr (pow_ne_zero _ gn)
    simp only [Submonoid.smul_def] at same
    have eq := congrArg Subtype.val same
    simp only [Algebra.smul_def] at eq
    change algebraMap A E (g^m)*(x:E)=algebraMap A E (g^m)*(y:E) at eq
    exact mul_left_cancel₀ mne eq
  obtain ⟨b,hb⟩ := localized_fibre_frame (A:=A) (R:=Localization S) (M:=Order k E)
    (P:=LocalizedModule S (Order k E)) (ι:=Fin n) S j jinj f inj ⟨g,⟨1,pow_one g⟩⟩ clear
  refine ⟨g,n,u,b,one,fun i=>?_⟩
  rw [hb]
  congr 1
  rw [sum,Finset.sum_eq_single i]
  · simp
  · intro l _ neq
    simp [Ne.symm neq]
    exact zero_smul (Plane k) (u l)
  · simp
theorem scalar_fibre_frames (z : k) :
    let A := Plane k
    let F := FractionRing A
    let ι := Fin (finrank F E)
    let : Module (Polynomial k) (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
    ∃ (b : Basis ι (Polynomial k) (Fiber E z)) (bf : Basis ι F E)
      (u : ι→Order k E) (g : A),
      (∀ i,quotientMap E z (u i)=b i) ∧ (∀ i,bf i=(u i:E)) ∧
      g.eval (C z)=1 ∧ ∀ x : Order k E,∃ t : ι→A,(∑ i,t i • u i)=g • x := by
  classical
  let : Module (Polynomial k) (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
  obtain ⟨n,b,u,g,f,red,sum,inj,one,clear⟩ := scalar_fibre_frame (E:=E) z
  let A := Plane k
  let F := FractionRing A
  let B := Order k E
  let S := nonZeroDivisors A
  let : IsLocalization (Algebra.algebraMapSubmonoid B S) E :=
    IsIntegralClosure.isLocalization A F E B
  let j : B→ₗ[A]E := (IsScalarTower.toAlgHom A B E).toLinearMap
  let : IsLocalizedModule S j := inferInstanceAs
    (IsLocalizedModule S (IsScalarTower.toAlgHom A B E).toLinearMap)
  have gn : g≠0 := by
    intro zero
    rw [zero,eval_zero] at one
    exact zero_ne_one one
  obtain ⟨bf,hbf⟩ := localized_fibre_frame (A:=A) (R:=F) (M:=B) (P:=E) (ι:=Fin n) S j
    Subtype.val_injective f inj ⟨g,mem_nonZeroDivisors_iff_ne_zero.mpr gn⟩ clear
  have n_eq : n=finrank F E := (Fintype.card_fin n).symm.trans (finrank_eq_card_basis bf).symm
  change n=finrank (FractionRing (Plane k)) E at n_eq
  subst n
  refine ⟨b,bf,u,g,red,?_,one,fun x=>?_⟩
  · intro i
    have single : f (Pi.single i 1)=u i := by
      rw [sum,Finset.sum_eq_single i]
      · simp
      · intro l _ neq
        simp [Ne.symm neq]
        exact zero_smul (Plane k) (u l)
      · simp
    rw [hbf,single]
    rfl
  · obtain ⟨t,h⟩ := clear x
    exact ⟨t,(sum t).symm.trans h⟩
theorem scalar_fibre_ranked_lifts (z : k) :
    ∃ (u : Fin (finrank (FractionRing (Plane k)) E)→Order k E) (g : Plane k),
      g.eval (C z)=1 ∧ ∀ x : Order k E,∃ t : Fin (finrank (FractionRing (Plane k)) E)→Plane k,
        (∑ i,t i • u i)=g • x := by
  obtain ⟨_,_,u,g,_,_,one,clear⟩ := scalar_fibre_frames (E:=E) z
  exact ⟨u,g,one,clear⟩
#print axioms lift_fibre_frame
#print axioms scalar_fibre_frame
#print axioms scalar_fibre_away_basis
#print axioms scalar_fibre_ranked_lifts
end Actual
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameFrames

-- merged module R6960CollisionTamePlaneDiscriminant
section Merged_R6960CollisionTamePlaneDiscriminant
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Module Matrix
open scoped Polynomial Matrix BigOperators
section FieldTrace
variable {A E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  [Field E] [Algebra A E]
variable (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
omit [IsIntegrallyClosed A] [IsNoetherianRing A] in
theorem integralClosure_torsionFree (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F E] [IsScalarTower A F E] : Module.IsTorsionFree A (integralClosure A E) := by
  have inj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  let : Module.IsTorsionFree A E := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a x eq
    rw [Algebra.smul_def,mul_eq_zero] at eq
    exact eq.imp (fun h=>inj (h.trans (map_zero _).symm)) id
  infer_instance
def integralTraceForm (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] : LinearMap.BilinForm A (integralClosure A E) := by
  let B := integralClosure A E
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let : Module.IsTorsionFree A B := integralClosure_torsionFree (E:=E) F
  let : Module.Finite A B := IsIntegralClosure.finite A F E B
  exact LinearMap.compr₂ (Algebra.lmul A B).toLinearMap (Algebra.intTrace A B)
theorem integralTraceForm_map (x y : integralClosure A E) :
    algebraMap A F (integralTraceForm (A:=A) (E:=E) F x y)=Algebra.trace F E ((x:E)*(y:E)) := by
  let B := integralClosure A E
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let : Module.IsTorsionFree A B := integralClosure_torsionFree (E:=E) F
  let : Module.Finite A B := IsIntegralClosure.finite A F E B
  change algebraMap A F (Algebra.intTrace A B (x*y))=Algebra.trace F E ((x:E)*(y:E))
  exact Algebra.algebraMap_intTrace (K:=F) (L:=E) (x*y)
def normalizationDiscriminant (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] : Ideal A :=
  gramIdeal (ι:=Fin (finrank F E)) (integralTraceForm (A:=A) (E:=E) F)
theorem normalizationDiscriminant_basis
    (b : Basis (Fin (finrank F E)) A (integralClosure A E)) :
    normalizationDiscriminant (A:=A) (E:=E) F=Ideal.span {(Algebra.traceMatrix A b).det} := by
  let B := integralClosure A E
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let : Module.IsTorsionFree A B := integralClosure_torsionFree (E:=E) F
  let : Module.Finite A B := IsIntegralClosure.finite A F E B
  let : Module.Free A B := Module.Free.of_basis b
  have matrix : tupleGram (integralTraceForm (A:=A) (E:=E) F) b=Algebra.traceMatrix A b := by
    apply Matrix.ext
    intro i j
    change Algebra.intTrace A B (b i*b j)=Algebra.trace A B (b i*b j)
    rw [Algebra.intTrace_eq_trace]
  change gramIdeal (ι:=Fin (finrank F E)) (integralTraceForm (A:=A) (E:=E) F)=_
  rw [gramIdeal_basis _ b,matrix]
theorem normalizationDiscriminant_ne_bot : normalizationDiscriminant (A:=A) (E:=E) F≠⊥ := by
  classical
  obtain ⟨I,b,h⟩ := FiniteDimensional.exists_is_basis_integral A F E
  let e : I ≃ Fin (finrank F E) := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let be := b.reindex e
  let u (i : Fin (finrank F E)): integralClosure A E := ⟨be i,by
    change IsIntegral A (be i)
    simpa only [be,Basis.reindex_apply] using h (e.symm i)⟩
  have map_eq : (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).map (algebraMap A F)=
      (Algebra.traceForm F E).toMatrix be := by
    apply Matrix.ext
    intro i j
    change algebraMap A F (integralTraceForm (A:=A) (E:=E) F (u i) (u j))=(Algebra.traceForm F E).toMatrix be i j
    rw [integralTraceForm_map,LinearMap.BilinForm.toMatrix_apply,Algebra.traceForm_apply]
  have right : ((Algebra.traceForm F E).toMatrix be).det≠0 :=
    det_traceForm_ne_zero be
  intro bot
  have mem := gramIdeal_mem (integralTraceForm (A:=A) (E:=E) F) u
  change (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).det∈normalizationDiscriminant (A:=A) (E:=E) F at mem
  rw [bot,Ideal.mem_bot] at mem
  apply right
  have dm : ((tupleGram (integralTraceForm (A:=A) (E:=E) F) u).map (algebraMap A F)).det =
      algebraMap A F (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).det :=
    ((algebraMap A F).map_det (tupleGram (integralTraceForm (A:=A) (E:=E) F) u)).symm
  rw [←map_eq,dm,mem,map_zero]
end FieldTrace
section Plane
open NormalizedFiber
variable {k E : Type} [Field k] [IsAlgClosed k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]
theorem maximal_contains_scalar (P : Ideal (Plane k)) (hp : P.IsMaximal) :
    ∃ z : k, (Polynomial.X-C (C z) : Plane k)∈P := by
  let e := Bivariate.equivMvPolynomial k
  let Q := P.map e.toRingHom
  have hQ : Q.IsMaximal := hp.map_bijective _ e.bijective
  obtain ⟨x,hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hQ
  refine ⟨x 1,?_⟩
  have inside : e (Polynomial.X-C (C (x 1)))∈Q := by
    rw [hx,MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp [e,Bivariate.equivMvPolynomial_X,Bivariate.equivMvPolynomial_C_C]
  change (Polynomial.X-C (C (x 1)) : Plane k)∈Q.comap e.toRingHom at inside
  rwa [show Q.comap e.toRingHom=P from Ideal.comap_map_of_bijective _ e.bijective] at inside
private theorem plane_form_principal (tr : LinearMap.BilinForm (Plane k) (Order k E)) :
    (gramIdeal (A:=Plane k) (M:=Order k E) (ι:=Fin (finrank (FractionRing (Plane k)) E)) tr).IsPrincipal := by
  let A := Plane k
  let n := finrank (FractionRing A) E
  refine principal_of_clears (gramIdeal (ι:=Fin n) tr) fun P hp=>?_
  obtain ⟨z,cut⟩ := maximal_contains_scalar P hp
  obtain ⟨u,g,one,clears⟩ := scalar_fibre_ranked_lifts (E:=E) z
  have gn : g∉P := by
    intro inside
    have dvd : (Polynomial.X-C (C z))∣g-1 := dvd_iff_isRoot.mpr (by
      rw [IsRoot,eval_sub,one,eval_one,sub_self])
    obtain ⟨r,hr⟩ := dvd
    have diff : g-1∈P := hr.symm ▸ P.mul_mem_right r cut
    have uno : (1:A)∈P := by simpa only [sub_sub_cancel] using P.sub_mem inside diff
    apply hp.ne_top
    rw [Ideal.eq_top_iff_one]
    exact uno
  have patch : ∀ a∈gramIdeal (ι:=Fin n) tr, (tupleGram tr u).det∣g^(2*Fintype.card (Fin n))*a :=
    gramIdeal_clear tr u g clears
  exact ⟨g,(tupleGram tr u).det,2*Fintype.card (Fin n),gn,gramIdeal_mem tr u,patch⟩
theorem plane_discriminant_principal :
    (normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))).IsPrincipal :=
  plane_form_principal (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)))
end Plane
#print axioms normalizationDiscriminant_ne_bot
#print axioms plane_discriminant_principal
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTamePlaneDiscriminant
