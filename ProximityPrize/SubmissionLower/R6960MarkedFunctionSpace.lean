import ProximityPrize.SubmissionLower.R6960MarkedPoleFamily

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections MonicChartLaurent RetainedRestrictionTorus RetainedSurfaceClass
open RetainedTwistedRestriction Module Submodule LinearMap Algebra Polynomial Finset
open scoped Polynomial Lower6960.RetainedSurfaceClass Lower6960.MarkedEvaluation BigOperators
open private Lower6960.MarkedEvaluation.denom_integral Lower6960.MarkedEvaluation.denom_zero from ProximityPrize.SubmissionLower.R6960MarkedPoleFamily
open private Lower6960.RetainedSurfaceClass.finite_along from ProximityPrize.SubmissionLower.R6960RetainedAxisCharts
variable {E:Type} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

/-- The conditions used on each column of the evaluation matrix. After clearing
the marked parameters, a non-word ordinate annihilates the residue at each mark. -/
def Column (i:ℕ) (T:Finset L) (ordinate:Tor E) (word:L→Tor E) (v:E) : Prop :=
  controlled E i T v ∧ ∃ u:Tor E,u.val=(denominator E T:E)*v ∧
    ∀z∈T, cut E true z∣(ordinate-word z)*u

private def xpow (n:ℕ) : Tor E := (torVar E false false)^n

private theorem xpow_control (T:Finset L) {j i:ℕ} (degree : j ≤ i) : controlled E i T (xpow (E:=E) j:E) := by
  intro s
  have mem:chartCoordinate s.1 RatFunc.X∈baseChart s := Subring.subset_closure (Or.inr (Or.inl rfl))
  let Xv:E:=ι RatFunc.X
  have nn:Xv≠0:=(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr RatFunc.X_ne_zero
  have ordinary:IsIntegral (baseChart s) ((fr s:E)⁻¹^i*Xv^j) := by
    by_cases h:s.1=true
    · have z:IsIntegral (baseChart s) Xv⁻¹ := by
        have p:IsIntegral (baseChart s) (ι (chartCoordinate s.1 RatFunc.X):E) :=
          isIntegral_algebraMap (x:=(⟨_,mem⟩:baseChart s))
        simpa only [h,chartCoordinate,ite_true,map_inv₀] using p
      have eq:(fr s:E)=Xv := by simp [fr,localFrame,axisBit,coordinate,h,Xv]
      rw [eq,←Nat.sub_add_cancel degree,pow_add,mul_assoc,←mul_pow,inv_mul_cancel₀ nn,one_pow,mul_one]
      exact z.pow _
    · have eq:(fr s:E)=1 := by simp [fr,localFrame,axisBit,coordinate,h]
      rw [eq,inv_one,one_pow,one_mul]
      have p:IsIntegral (baseChart s) (ι (chartCoordinate s.1 RatFunc.X):E) :=
        isIntegral_algebraMap (x:=(⟨_,mem⟩:baseChart s))
      exact (show IsIntegral (baseChart s) Xv by simpa [chartCoordinate,h,Xv] using p).pow _
  change IsIntegral _ ((fr s)⁻¹^i*(chartDenom E T s*Xv^j))
  rw [mul_left_comm];exact (Lower6960.MarkedEvaluation.denom_integral E T s).mul ordinary

private theorem xpow_independent (a:ℕ) : LinearIndependent L (fun j:Fin a=>(xpow (E:=E) j.val:E)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coeff eq j
  let P:L[X]:=∑h:Fin a,Polynomial.monomial h.val (coeff h)
  let eval: L[X]→+*E := (algebraMap ChartField E).comp ((MonicChartProbes.planeMap (false,false)).comp
    (Polynomial.mapRingHom (C:L→+*L[X])))
  have injective:Function.Injective eval := (algebraMap ChartField E).injective.comp
    ((MonicChartProbes.planeMap_injective _).comp (Polynomial.map_injective _ C_injective))
  have zero:eval P=0 := by
    rw [show eval P=∑h,eval (Polynomial.monomial h.val (coeff h)) from map_sum ..]
    apply Eq.trans _ eq
    apply Finset.sum_congr rfl; intro h _
    rw [←C_mul_X_pow_eq_monomial,map_mul,map_pow]
    change ι (MonicChartProbes.planeMap (false,false) ((C (coeff h)).map C)) *
      ι (MonicChartProbes.planeMap (false,false) ((Polynomial.X:L[X]).map C))^h.val=_
    rw [Polynomial.map_C,map_X,MonicChartProbes.planeMap_constants,MonicChartProbes.planeMap_abscissa]
    rfl
  have poly := (map_eq_zero_iff _ injective).mp zero
  have c:=congrArg (fun p:L[X]=>p.coeff j.val) poly
  simpa [P,Polynomial.finsetSum_coeff,coeff_monomial,←Fin.ext_iff] using c

theorem family_from_fibres [FiniteDimensional ChartField E] (i n:ℕ) (budget:Budget E i n)
    (T:Finset L) (nz:∀z∈T,z≠0) (J:T→Type) [∀z,Fintype (J z)]
    (v:∀z:T,J z→Axis E true z.val) (regular:∀(z:T)(j:J z),FibreSection (E:=E) i z.val (v z j))
    (independent:∀z,LinearIndependent L (v z))
    (ordinate:Tor E) (word:L→Tor E)
    (sheet:∀(z:T)(j:J z), red E true z.val (ordinate-word z.val)*v z j=0) :
    ∃ m:ℕ, ∃ functions:Fin m→E, LinearIndependent L functions ∧
      (∀j,Column i T ordinate word (functions j)) ∧
      (∑z:T,Fintype.card (J z))+(i+1)≤n+m := by
  classical
  obtain ⟨D,lift,size,regularLift,poles,residue⟩:=lift_fibres E i n budget T nz J v regular independent
  let B:=Module.finBasis L D
  have indep:LinearIndependent L (fun j=>lift (B j)) :=
    B.linearIndependent.map' lift (LinearMap.ker_eq_bot'.mpr (fun d h=>poles d (h ▸ isIntegral_zero)))
  let a:=i+1
  let u (j:Fin a) : E:=(xpow (E:=E) j.val:E)
  let f:=Sum.elim u (fun j=>lift (B j))
  have li:LinearIndependent L f := by
    apply LinearIndependent.sum_type (xpow_independent a) indep
    rw [Submodule.disjoint_def]
    intro w ordinary lifted
    have int:IsIntegral torus w := by
      clear lifted
      induction ordinary using Submodule.span_induction with
      | mem v h=>obtain ⟨j,rfl⟩:=h;exact (xpow (E:=E) j.val).property
      | zero=>exact isIntegral_zero
      | add _ _ _ _ h q=>exact h.add q
      | smul c v _ h=>
        have sc:IsIntegral torus (ι (constants c):E):=isIntegral_algebraMap (x:=(⟨_,
          base_torus (false,false) (chart_constant _ c)⟩:torus))
        exact sc.mul h
    have le: Submodule.span L (Set.range (fun j=>lift (B j)))≤lift.range :=
      Submodule.span_le.mpr (fun _ ⟨j,eq⟩=>⟨B j,eq⟩)
    obtain ⟨d,rfl⟩:=le lifted
    rw [poles d int,map_zero]
  have on (j) : Column i T ordinate word (f j) := by
    cases j with
    | inl j =>
      refine ⟨xpow_control T (show j.val ≤ i by have := j.isLt;dsimp [a] at this;omega),
        denominator E T*xpow j.val,rfl,?_⟩
      intro z hz
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.eq_zero_iff_mem (I:=axisIdeal E true z)).mp
      rw [map_mul,map_mul,Lower6960.MarkedEvaluation.denom_zero E T z hz,zero_mul,mul_zero]
    | inr j =>
      obtain ⟨w,eq,redW⟩:=residue (B j)
      refine ⟨regularLift (B j),w,eq,?_⟩
      intro z hz
      let zz:T:=⟨z,hz⟩
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.eq_zero_iff_mem (I:=axisIdeal E true z)).mp
      rw [map_mul]
      change red E true z (ordinate-word z)*red E true z w=0
      rw [redW zz,mul_smul_comm,Finset.mul_sum]
      have sumzero : (∑ l:J zz,red E true z (ordinate-word z)*((B j).val ⟨zz,l⟩ • v zz l))=0 := by
        apply Finset.sum_eq_zero; intro l _
        rw [mul_smul_comm];change _ • (red E true zz.val (ordinate-word zz.val)*v zz l)=0
        rw [sheet zz l,smul_zero]
      rw [sumzero,smul_zero]
  let index:=Fintype.equivFin ((Fin a)⊕(Fin (finrank L D)))
  refine ⟨_,fun i=>f (index.symm i),li.comp _ index.symm.injective,fun i=>on _,?_⟩
  simp only [Fintype.card_sum,Fintype.card_fin]
  exact (Nat.add_le_add_right size a).trans_eq (by omega)

#print axioms family_from_fibres
end Lower6960.MarkedEvaluation
