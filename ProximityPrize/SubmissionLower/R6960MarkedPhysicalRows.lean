import ProximityPrize.SubmissionLower.R6960MarkedWordResidues
import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace
import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm

set_option Elab.async false

-- merged module R6960MarkedPoleFamily
section Merged_R6960MarkedPoleFamily
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open RetainedSurfaceClass RetainedTwistedRestriction Module Submodule LinearMap Algebra Polynomial Finset
open scoped Polynomial Lower6960.RetainedSurfaceClass Lower6960.MarkedEvaluation BigOperators
local instance : DecidableEq L := Classical.decEq _
variable (E:Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def denominator (T:Finset L) : Tor E:=∏z∈T,cut E true z
def chartDenom (T:Finset L) (s:Chart) : E:=∏z∈T,algebraMap (baseChart s) E (zcut s z)
def controlled (i:ℕ) (T:Finset L) (v:E) : Prop :=
  ∀s,Regular s i (chartDenom E T s*v)

theorem denom_integral (T:Finset L) (s:Chart) : IsIntegral (baseChart s) (chartDenom E T s) := by
  unfold chartDenom
  rw [←map_prod];exact isIntegral_algebraMap

private theorem eval_cut (z y:L) : red E true z (cut E true y)=algebraMap L (Axis E true z) (z-y) := by
  let π:=Ideal.Quotient.mk (axisIdeal E true z)
  have src:cut E true y=torVar E true false-algebraMap L (Tor E) y := by
    apply Subtype.ext;exact map_sub (algebraMap ChartField E) _ _
  change π _=_
  have fixed:π (torVar E true false)=algebraMap L _ z := fixed_value E true z
  rw [src,map_sub,fixed,map_sub];rfl

private theorem denom_value (T:Finset L) (z:L) :
    Ideal.Quotient.mk (axisIdeal E true z) (denominator E T)=algebraMap L (Axis E true z) (∏y∈T,(z-y)) := by
  rw [denominator,map_prod,map_prod]
  exact Finset.prod_congr rfl (fun y _=>eval_cut E z y)

theorem denom_zero (T:Finset L) (z:L) (hz:z∈T) :
    Ideal.Quotient.mk (axisIdeal E true z) (denominator E T)=0 := by
  rw [denom_value,Finset.prod_eq_zero (f:=fun u:L=>z-u) hz (sub_self z),map_zero]

private theorem cancel_one {T:Finset L} {z:L} (mem:z∈T) (v:E) :
    ((denominator E T:E))*(v/ι (divisor true z))=(denominator E (T.erase z):E)*v := by
  have dn : (ι (divisor true z):E)≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne true z)
  rw [show denominator E T=cut E true z*denominator E (T.erase z) from (Finset.mul_prod_erase _ _ mem).symm]
  change (ι (divisor true z)*(denominator E (T.erase z):E))*(v/ι (divisor true z))=_
  field_simp

private theorem cleared_charts (i:ℕ) {T:Finset L} {z:L} (mem:z∈T) (s:Chart) (v:E)
    (reg:Regular s i v) : Regular s i (chartDenom E T s*(v/ι (divisor true z))) := by
  let F:=localFrame s true
  have dn : (ι (divisor true z):E)≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne true z)
  have atBase:F⁻¹∈baseChart s := by
    have h:chartCoordinate s.2 scalarCoordinate∈baseChart s:=Subring.subset_closure (Or.inr (Or.inr rfl))
    by_cases ht:s.2=true <;> simp [F,localFrame,axisBit,coordinate,ht,chartCoordinate] at * <;> assumption
  have inv:IsIntegral (baseChart s) (ι (F⁻¹):E) := isIntegral_algebraMap (x:=(⟨_,atBase⟩:baseChart s))
  have eq:chartDenom E T s=ι (divisor true z)/ι F*chartDenom E (T.erase z) s := by
    rw [show chartDenom E T s=algebraMap (baseChart s) E (zcut s z)*chartDenom E (T.erase z) s from
      (Finset.mul_prod_erase _ _ mem).symm]
    change ι (zcut s z:ChartField)*_=_
    rw [zcut_value,map_div₀]
  change IsIntegral _ ((fr s)⁻¹^i*(chartDenom E T s*(v/ι (divisor true z))))
  rw [eq]
  have algebra : (fr s)⁻¹^i*(ι (divisor true z)/ι F*chartDenom E (T.erase z) s*(v/ι (divisor true z)))=
      chartDenom E (T.erase z) s*ι F⁻¹*((fr s)⁻¹^i*v) := by
    rw [map_inv₀]; field_simp [dn,(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s true)] <;> ring
  rw [algebra];exact ((denom_integral E _ _).mul inv).mul reg

private theorem scaled_sum {J:Type} [Fintype J] (p:J→Chart→E) (s:Chart) (d:J→L) :
    principalValue p s d=∑j,(ι (constants (d j)))*p j s := by
  classical
  simp [principalValue,Basis.constr_apply_fintype,Algebra.smul_def];rfl

/-- Lift actual marked fibre sections jointly. A nonzero lifted function has a
genuine scalar pole, so the lifted space is independent of every ordinary
abscissa polynomial. -/
theorem lift_fibres [FiniteDimensional ChartField E] (i n:ℕ) (budget:Budget E i n)
    (T:Finset L) (nz:∀z∈T,z≠0) (J:T→Type) [∀z,Fintype (J z)]
    (v:∀z:T,J z→Axis E true z.val)
    (regular:∀ (z:T) (j:J z),FibreSection (E:=E) i z.val (v z j)) (independent:∀z,LinearIndependent L (v z)) :
    ∃ D:Submodule L ((Σz:T,J z)→L), ∃ lift:D→ₗ[L]E,
      (∑z:T,Fintype.card (J z))≤n+finrank L D ∧ (∀d,controlled E i T (lift d)) ∧
      (∀ d, IsIntegral torus (lift d) → d=0) ∧
      ∀d:D,∃w:Tor E, w.val=(denominator E T:E)*lift d ∧
        ∀z:T,red E true z.val w=(∏ y∈T.erase z.val,(z.val-y)) • (∑j:J z,(d.val ⟨z,j⟩) • v z j) := by
  classical
  let Id:=Σz:T,J z
  choose W reg values compat using fun u:Id=>word_principal_parts (E:=E) i u.1.val (nz _ u.1.property) (v u.1 u.2) (regular u.1 u.2)
  let p (j:Id) (s:Chart):E:=(W j s:E)/ι (divisor true j.1.val)
  obtain ⟨D,lift,dim,part⟩:=lift_principal_parts (J:=Id) (E:=E) i n budget p compat
  have controls (d:D) (s:Chart): Regular s i (chartDenom E T s*lift d) := by
    let M:=chartDenom E T s
    let P:=principalValue p s d.val
    have hc : IsIntegral (baseChart s) ((fr s)⁻¹^i*(P-lift d)):=part d s
    have total : Regular s i (M*P) := by
      change IsIntegral _ ((fr s)⁻¹^i*(M*principalValue p s d.val))
      rw [scaled_sum,Finset.mul_sum,Finset.mul_sum]
      apply IsIntegral.sum;intro j _
      have sc:IsIntegral (baseChart s) (ι (constants (d.val j)):E) :=
        isIntegral_algebraMap (x:=(⟨_,chart_constant s (d.val j)⟩:baseChart s))
      have term:=sc.mul (cleared_charts E i j.1.property s (W j s:E) (reg j s))
      convert term using 1 <;> ring
    convert total.sub ((denom_integral E T s).mul hc) using 1 <;> ring
  have residues (d:D) : ∃w:Tor E,w.val=(denominator E T:E)*lift d ∧
      ∀z:T,red E true z.val w=(∏y∈T.erase z.val,(z.val-y)) • (∑j:J z,(d.val ⟨z,j⟩) • v z j) := by
    let a:Chart:=(false,false)
    let rem := principalValue p a d.val-lift d
    have remInt : IsIntegral torus rem := order_mono (base_torus a) (by
      simpa [a,Regular,fr,localFrame,axisBit] using part d a)
    let R:Tor E:=⟨rem,remInt⟩
    let w:Tor E:=(∑j:Id,d.val j • (denominator E (T.erase j.1.val)*W j a))-denominator E T*R
    have sum_eq : (denominator E T:E)*principalValue p a d.val =
        ((∑j:Id,d.val j • (denominator E (T.erase j.1.val)*W j a):Tor E):E) := by
      rw [scaled_sum,Finset.mul_sum]
      have castSum (f:Id→Tor E) : ((∑j,f j : Tor E):E)=∑j,(f j:E) := map_sum (Tor E).val f Finset.univ
      rw [castSum]
      apply Finset.sum_congr rfl;intro j _
      change (denominator E T:E)*(ι (constants (d.val j))*p j a)=ι (constants (d.val j))*(_*_)
      rw [mul_left_comm];exact congrArg (ι (constants (d.val j))*·) (cancel_one E j.1.property _)
    refine ⟨w,?_,fun z=>?_⟩
    · change ((∑j:Id,d.val j • (denominator E (T.erase j.1.val)*W j a):Tor E):E)-(denominator E T:E)*rem=_
      rw [←sum_eq];dsimp [rem];ring
    · let π:=Ideal.Quotient.mk (axisIdeal E true z.val)
      have vanish : π (denominator E T)=0 := denom_zero E T z.val z.property
      change π w=_
      simp only [w,map_sub,map_mul,map_sum,vanish,zero_mul,sub_zero]
      rw [Fintype.sum_sigma (fun j:Σz:T,J z=>π (d.val j • (denominator E (T.erase j.1.val)*W j a)))]
      rw [Finset.sum_eq_single z]
      · rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        change (red E true z.val) (d.val ⟨z,j⟩ • (denominator E (T.erase z.val)*W ⟨z,j⟩ a))=_
        rw [map_smul]
        change _ • (π (denominator E (T.erase z.val)*W ⟨z,j⟩ a))=_
        rw [map_mul,show π (W ⟨z,j⟩ a)=v z j from values ⟨z,j⟩ a]
        have weight := denom_value E (T.erase z.val) z.val
        change π (denominator E (T.erase z.val))=_ at weight
        rw [weight,←Algebra.smul_def,smul_comm]
      · intro other _ ne
        apply Finset.sum_eq_zero;intro j _
        change red E true z.val (_ • (denominator E (T.erase other.val)*W ⟨other,j⟩ a))=0
        rw [map_smul];change _ • π (_*_) = 0
        have vz : π (denominator E (T.erase other.val))=0 :=
          denom_zero E _ _ (Finset.mem_erase.mpr ⟨Ne.symm (Subtype.val_injective.ne ne),z.property⟩)
        rw [map_mul,vz,zero_mul,smul_zero]
      · simp
  refine ⟨D,lift,by simpa only [Id,Fintype.card_sigma] using dim,controls,?_,residues⟩
  intro d noPole
  obtain ⟨w,eq,test⟩:=residues d
  have exactValue : w=denominator E T*(⟨lift d,noPole⟩:Tor E) := Subtype.ext eq
  apply Subtype.ext
  funext j
  obtain ⟨z,j⟩:=j
  have weight:(∏y∈T.erase z.val,(z.val-y))≠0 := Finset.prod_ne_zero_iff.mpr (fun y hy=>sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm)
  have zero:=test z
  rw [exactValue] at zero
  change Ideal.Quotient.mk _ (_*_)=_ at zero
  rw [map_mul,denom_zero E T z.val z.property,zero_mul] at zero
  let c:=∏y∈T.erase z.val,(z.val-y)
  have cleared:=congrArg (fun a:Axis E true z.val=>c⁻¹ • a) zero.symm
  change c⁻¹ • (c • (∑j:J z,d.val ⟨z,j⟩ • v z j))=c⁻¹ • 0 at cleared
  rw [smul_smul,inv_mul_cancel₀ weight,one_smul,smul_zero] at cleared
  exact Fintype.linearIndependent_iff.mp (independent z) _ cleared j

end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedPoleFamily

-- merged module R6960MarkedFunctionSpace
section Merged_R6960MarkedFunctionSpace
set_option synthInstance.maxHeartbeats 200000

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
open Lower6960.MarkedEvaluation (denom_integral denom_zero)
open Lower6960.RetainedSurfaceClass (finite_along)
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
  let P:(Polynomial L):=∑h:Fin a,Polynomial.monomial h.val (coeff h)
  let eval: (Polynomial L)→+*E := (algebraMap ChartField E).comp ((MonicChartProbes.planeMap (false,false)).comp
    (Polynomial.mapRingHom (C:L→+*(Polynomial L))))
  have injective:Function.Injective eval := (algebraMap ChartField E).injective.comp
    ((MonicChartProbes.planeMap_injective _).comp (Polynomial.map_injective _ C_injective))
  have zero:eval P=0 := by
    rw [show eval P=∑h,eval (Polynomial.monomial h.val (coeff h)) from map_sum ..]
    apply Eq.trans _ eq
    apply Finset.sum_congr rfl; intro h _
    rw [←C_mul_X_pow_eq_monomial,map_mul,map_pow]
    change ι (MonicChartProbes.planeMap (false,false) ((C (coeff h)).map C)) *
      ι (MonicChartProbes.planeMap (false,false) ((Polynomial.X:(Polynomial L)).map C))^h.val=_
    rw [Polynomial.map_C,map_X,MonicChartProbes.planeMap_constants,MonicChartProbes.planeMap_abscissa]
    rfl
  have poly := (map_eq_zero_iff _ injective).mp zero
  have c:=congrArg (fun p:(Polynomial L)=>p.coeff j.val) poly
  simpa [P,Polynomial.finsetSum_coeff,coeff_monomial,Finsupp.single_apply,←Fin.ext_iff] using c

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

end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedFunctionSpace

-- merged module R6960MarkedColumnPlace
section Merged_R6960MarkedColumnPlace
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open MonicFourChartDescent ChartOverlapTests RetainedRestrictionTorus RetainedSurfaceClass RetainedTwistedRestriction
open Polynomial Finset Algebra
open scoped Polynomial BigOperators Lower6960.RetainedSurfaceClass Lower6960.MarkedEvaluation
open scoped Lower6960.MonicChart
local instance : DecidableEq Scalar := Classical.decEq _
local instance : DecidableEq ChartField := Classical.decEq _
local instance (priority := 2200) : Algebra (Polynomial Scalar) ChartField :=
  inferInstanceAs (Algebra (Polynomial Scalar) (RatFunc Scalar))
local instance (priority := 2200) : SMul (Polynomial Scalar) ChartField :=
  (inferInstance : Algebra (Polynomial Scalar) ChartField).toSMul
open Lower6960.MarkedEvaluation (leading_unit integral_infty)
variable {E Ω:Type} [Field E] [Field Ω] [Algebra ChartField E] [Algebra ChartField Ω]
variable [Algebra (Polynomial Scalar) Ω] [IsScalarTower (Polynomial Scalar) ChartField Ω]
local notation "ι" => algebraMap ChartField Ω
local notation "poly" => algebraMap (Polynomial Scalar) ChartField
local notation "jo" => algebraMap (Polynomial Scalar) Ω
variable (c:L) (ev:E→+*Ω) (base:∀a,ev (algebraMap ChartField E a)=algebraMap ChartField Ω (rowBase c a))

private theorem row_cut (z:L) : rowBase c (divisor true z)=poly (Polynomial.X-C (inner z)) := by
  change rowBase c (scalarCoordinate-constants z)=_
  rw [map_sub,row_parameter,row_constant,map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C];rfl

private theorem pole_image (T:Finset L) :
    polePolynomial (T.image inner)=∏z∈T,(Polynomial.X-C (inner z)) := by
  classical
  exact Finset.prod_image (f:=fun z:Scalar=>Polynomial.X-C z) (fun _ _ _ _ h=>inner.injective h)

include base in
theorem mapped_denom (T:Finset L) (b:Bool) :
    ev (chartDenom E T (false,b))=jo (polePolynomial (T.image inner))/
      (if b then ι RatFunc.X else 1)^T.card := by
  classical
  rw [chartDenom,map_prod,pole_image,map_prod,←Finset.prod_const,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl;intro z _
  change ev (algebraMap ChartField E (zcut (false,b) z:ChartField))=_
  rw [base,zcut_value,map_div₀,map_div₀,row_cut,←IsScalarTower.algebraMap_apply]
  cases b <;> simp [localFrame,axisBit,coordinate,row_parameter]

include base in
theorem mapped_finite {i:ℕ} {T:Finset L} {v:E} (reg:controlled E i T v) :
    IsIntegral (Polynomial Scalar) (jo (polePolynomial (T.image inner))*ev v) := by
  have h:IsIntegral (baseChart (false,false)) (chartDenom E T (false,false)*v) := by
    simpa [Regular,fr,localFrame,axisBit] using reg (false,false)
  have v':=integral_section c _ ev base (IsFractionRing.injective (Polynomial Scalar) ChartField) (fun _ h=>finite_base c h) h
  simpa only [map_mul,mapped_denom c ev base,Bool.false_eq_true,ite_false,one_pow,div_one] using v'

include base in
theorem mapped_infty [FiniteDimensional ChartField Ω]
    [Algebra (SheetNorm.Infinity Scalar) Ω] [IsScalarTower (SheetNorm.Infinity Scalar) ChartField Ω]
    {i:ℕ} {T:Finset L} {v:E} (reg:controlled E i T v) :
    IsIntegral (SheetNorm.Infinity Scalar) (ev v) := by
  classical
  let D:=polePolynomial (T.image inner)
  have d:D.natDegree=T.card := (polePolynomial_degree _).trans (card_image_of_injective _ inner.injective)
  have h:IsIntegral (baseChart (false,true)) (chartDenom E T (false,true)*v) := by
    simpa [Regular,fr,localFrame,axisBit] using reg (false,true)
  have v':=integral_section c _ ev base (show Function.Injective (algebraMap (SheetNorm.Infinity Scalar) ChartField)
    from Subtype.val_injective) (fun _ h=>infinity_base c h) h
  rw [map_mul,mapped_denom c ev base,if_pos rfl] at v'
  have u:=Lower6960.MarkedEvaluation.leading_unit (K:=Scalar) D (polePolynomial_monic _).ne_zero
  have inv:=Lower6960.MarkedEvaluation.integral_infty (E:=Ω) u.2
  rw [map_inv₀,map_div₀,←IsScalarTower.algebraMap_apply,map_pow,d] at inv
  have nz:jo D/(ι RatFunc.X)^T.card≠0 := by
    refine div_ne_zero ?_ (pow_ne_zero _ ((map_ne_zero_iff _ (algebraMap ChartField Ω).injective).mpr RatFunc.X_ne_zero))
    rw [IsScalarTower.algebraMap_apply (Polynomial Scalar) ChartField Ω]
    exact (map_ne_zero_iff _ (algebraMap ChartField Ω).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (polePolynomial_monic _).ne_zero)
  change IsIntegral (SheetNorm.Infinity Scalar) ((jo D/(ι RatFunc.X)^T.card)*ev v) at v'
  have t:=inv.mul v';rwa [←mul_assoc,inv_mul_cancel₀ nz,one_mul] at t

private def boundaryPolynomial (c:L) : (Polynomial Scalar) := C (algebraMap (Polynomial L) Scalar Polynomial.X+inner c)*Polynomial.X
private theorem row_boundary : rowBase c (boundary (false,false) (true,true))=poly (boundaryPolynomial c) := by
  change rowBase c (RatFunc.X*scalarCoordinate)=_
  rw [map_mul,row_abscissa,row_parameter,boundaryPolynomial,map_mul,RatFunc.algebraMap_X,RatFunc.algebraMap_C,map_add]
  rfl

include base in
theorem torus_mem {z:Scalar} (P:MarkPlace Scalar Ω z) (nz:z≠0) (v:Tor E) : ev (v:E)∈P.V := by
  classical
  obtain ⟨n,regular⟩:=clear_torus (false,false) (v:E) v.property
  have fd:=integral_section c _ ev base (IsFractionRing.injective (Polynomial Scalar) ChartField) (fun _ h=>finite_base c h) regular
  let p:=boundaryPolynomial c
  have hn: (algebraMap (Polynomial L) Scalar Polynomial.X+inner c)≠0 := by
    change algebraMap (Polynomial L) Scalar Polynomial.X+algebraMap (Polynomial L) Scalar (C c)≠0
    rw [←map_add];exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_add_C_ne_zero _)
  have unit:IsUnit (P.lift p) := P.lift_unit (by simpa [p,boundaryPolynomial] using mul_ne_zero hn nz)
  have scaled:=P.integral_mem fd
  rw [map_mul,map_pow,base,show opposite (false,false)=(true,true) from rfl,row_boundary,←P.value] at scaled
  obtain ⟨u,hu⟩:=unit
  let undo: P.V:=↑(u⁻¹)^n
  have val:((undo:P.V):Ω)*(P.lift p:Ω)^n=1 := by
    rw [←hu];change ((↑(u⁻¹):P.V):Ω)^n*((↑u:P.V):Ω)^n=1
    have iu : ((↑(u⁻¹):P.V):Ω)*((↑u:P.V):Ω)=1 := congrArg (fun w:P.V=>(w:Ω)) u.inv_mul
    rw [←mul_pow,iu,one_pow]
  change (P.lift p:Ω)^n * ev (v:E)∈P.V at scaled
  have m:=P.V.toSubring.mul_mem undo.property scaled
  rw [←mul_assoc,val,one_mul] at m
  exact m

def mapped_torus (c:L) (ev:E→+*Ω) (base:∀a,ev (algebraMap ChartField E a)=ι (rowBase c a))
    (z:Scalar) (P:MarkPlace Scalar Ω z) (nz:z≠0) : Tor E→+*P.V :=
  (ev.comp (Tor E).val.toRingHom).codRestrict P.V.toSubring (torus_mem c ev base P nz)

include base in
theorem local_cut (z:L) (P:MarkPlace Scalar Ω (inner z)) (nz:inner z≠0) :
    mapped_torus c ev base _ P nz (cut E true z)=P.pi := by
  apply Subtype.ext
  change ev (algebraMap ChartField E (divisor true z))=(P.lift (Polynomial.X-C (inner z)):Ω)
  rw [base,row_cut,P.value]

include base in
theorem local_annihilation (z:L) (P:MarkPlace Scalar Ω (inner z)) (nz:inner z≠0)
    (u o w:Tor E) (killed:cut E true z∣(o-w)*u) :
    P.pi∣(mapped_torus c ev base _ P nz o-mapped_torus c ev base _ P nz w)*mapped_torus c ev base _ P nz u := by
  have h:=map_dvd (mapped_torus c ev base _ P nz) killed
  rwa [local_cut,map_mul,map_sub] at h

end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedColumnPlace

-- merged module R6960MarkedPhysicalRows
section Merged_R6960MarkedPhysicalRows
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open MonicFourChartDescent RetainedRestrictionTorus RetainedSurfaceClass RetainedTwistedRestriction
open Polynomial Finset Algebra Module
open scoped Polynomial BigOperators Lower6960.RetainedSurfaceClass Lower6960.MarkedEvaluation
local instance : DecidableEq Scalar := Classical.decEq _
local instance : DecidableEq ChartField := Classical.decEq _
local instance (priority := 2200) : SMul (Polynomial Scalar) ChartField :=
  (inferInstance : Algebra (Polynomial Scalar) ChartField).toSMul
variable {E Ω I J:Type} [Field E] [Field Ω] [Algebra ChartField E] [Algebra ChartField Ω]
  [Algebra (Polynomial Scalar) Ω] [IsScalarTower (Polynomial Scalar) ChartField Ω] [FiniteDimensional ChartField Ω] [IsGalois ChartField Ω]
  [Fintype I] [DecidableEq I]
local notation "G" => SheetNorm.Aut Scalar Ω
local notation "ι" => algebraMap ChartField Ω
local notation "jΩ" => algebraMap (Polynomial Scalar) Ω

private theorem same_denominator (T:Finset L) : (denominator E T:E)=chartDenom E T (false,false) := by
  change (Tor E).val (∏z∈T,cut E true z)=_
  rw [map_prod,chartDenom];apply Finset.prod_congr rfl;intro z _
  change algebraMap ChartField E (divisor true z)=algebraMap ChartField E (zcut (false,false) z:ChartField)
  rw [zcut_value,show localFrame (false,false) true=1 from rfl,div_one]

theorem actual_place_rows (T:Finset L) (i e:ℕ) (v:J→E) (o:Tor E) (word:L→Tor E)
    (cols:∀j,Column i T o word (v j))
    (c:I→L) (ev:I→(E→+*Ω)) (base:∀i a,ev i (algebraMap ChartField E a)=ι (rowBase (c i) a))
    (deg:∀i,(minpoly ChartField (ev i (o:E))).natDegree=e)
    (q:I→(Polynomial (Polynomial Scalar))) (root:∀i,(q i).eval₂ (algebraMap (Polynomial Scalar) Ω) (ev i (o:E))=0)
    (z:L) (hz:z∈T) (nz:inner z≠0) (place:MarkPlace Scalar Ω (inner z))
    (sep:∀i,((q i).map (evalRingHom (inner z))).Separable)
    (fixed:∀(g:G) i,g (ev i (word z:E))=ev i (word z:E)) :
    ∃ (A:G→Matrix I J place.V) (row:G→Finset I),
      (∀g i j,(A g i j:Ω)=g (jΩ (polePolynomial (T.image inner))*ev i (v j))) ∧
      (∀g,∀i∈row g,∀j,place.pi∣A g i j) ∧
      e*(∑g:G,(row g).card)=Fintype.card G*((e-1)*Fintype.card I) := by
  classical
  let emb (g:G) (i:I):=g.toRingHom.comp (ev i)
  have overBase (g:G) (i:I) (a:ChartField) : emb g i (algebraMap ChartField E a)=ι (rowBase (c i) a) :=
    (congrArg g (base i a)).trans (g.commutes _)
  let loc (g:G) (i:I):Tor E→+*place.V:=mapped_torus (c i) (emb g i) (overBase g i) _ place nz
  choose u val ann using fun j=>(cols j).2
  let A (g:G) : Matrix I J place.V:=fun i j=>loc g i (u j)
  have realized (g:G) (i:I) (j:J) : (A g i j:Ω)=g (jΩ (polePolynomial (T.image inner))*ev i (v j)) := by
    change g (ev i (u j:E))=_
    rw [val,same_denominator,map_mul,mapped_denom (c i) (ev i) (base i)]
    simp
  let y (i:I):Ω:=ev i (o:E)
  have locmem (i:I) (a:MulAction.orbit G (y i)) : a.val∈place.V := by
    obtain ⟨g,eq⟩:=a.property
    rw [←eq]
    exact (loc g i o).property
  let ys (i:I) (a:MulAction.orbit G (y i)):place.V:=⟨a.val,locmem i a⟩
  let qs (i:I):=(q i).map place.lift
  have vanish (i:I) (a:MulAction.orbit G (y i)) : (qs i).eval (ys i a)=0 := by
    apply Subtype.val_injective (p:=fun t:Ω=>t∈place.V)
    change place.V.subtype ((qs i).eval (ys i a))=0
    rw [←Polynomial.eval₂_at_apply,show qs i=(q i).map place.lift from rfl,eval₂_map]
    have maps:place.V.subtype.comp place.lift=jΩ := RingHom.ext (fun r=>
      (place.value r).trans (IsScalarTower.algebraMap_apply (Polynomial Scalar) ChartField Ω r).symm)
    rw [maps]
    obtain ⟨g,eq⟩:=a.property
    change (q i).eval₂ jΩ a.val=0
    rw [←eq]
    have coeff:g.toRingHom.comp jΩ=jΩ := RingHom.ext (fun r=>by
      change g (jΩ r)=jΩ r;rw [IsScalarTower.algebraMap_apply (Polynomial Scalar) ChartField Ω,g.commutes])
    have evq:=congrArg g.toRingHom (root i)
    rw [Polynomial.hom_eval₂,coeff,map_zero] at evq
    exact evq
  let words (i:I):place.V:=loc 1 i (word z)
  obtain ⟨row,off,count⟩:=actual_unmarked_rows e y deg place.V.subtype Subtype.val_injective qs
    (fun i=>place.separable (sep i)) ys (fun _ _=>rfl) vanish words place.pi A (by
      intro g i j
      have eq:words i=loc g i (word z) := Subtype.ext (fixed g i).symm
      rw [eq]
      exact local_annihilation (c i) (emb g i) (overBase g i) z place nz (u j) o (word z) (ann j z hz))
  exact ⟨A,row,realized,off,count⟩

end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedPhysicalRows
