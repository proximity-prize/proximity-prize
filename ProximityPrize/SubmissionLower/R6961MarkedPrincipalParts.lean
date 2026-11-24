import ProximityPrize.SubmissionLower.R6961RetainedTwistedBudget

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open RetainedTwistedRestriction RetainedSurfaceClass Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass
open Lower6961.RetainedRestrictionTorus (frame_integral)
variable {E:Type} [Field E] [Algebra ChartField E] {J:Type} [Fintype J]
local notation "ι" => algebraMap ChartField E

scoped instance constantFieldAlgebra (E:Type) [Field E] [Algebra ChartField E] : Algebra L E :=
  ((algebraMap ChartField E).comp constants).toAlgebra
open scoped Lower6961.MarkedEvaluation

def principalValue (p:J→Chart→E) (s:Chart) : (J→L) →ₗ[L] E :=
  (Pi.basisFun L J).constr L (fun j=>p j s)

private def regularSpace (i:ℕ) (s:Chart) : Submodule L E where
  carrier:={v|Regular s i v}
  zero_mem':=by simpa [Regular] using (isIntegral_zero (R:=baseChart s) (B:=E))
  add_mem' {u v} a b:=by change IsIntegral _ (_*(u+v)); rw [mul_add];exact a.add b
  smul_mem' r v a:=by
    have ci:IsIntegral (baseChart s) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,chart_constant s r⟩:baseChart s))
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*v))
    rw [mul_left_comm]; exact ci.mul a

private theorem anchored (i:ℕ) (p:J→Chart→E)
    (compatible:∀ j s t,Over s t i (p j s-p j t)) :
    ∃ family : (J→L) →ₗ[L] charts E i, ∀ v s,
      ((family v).val s:E)=principalValue p s v-principalValue p (false,false) v := by
  classical
  let a:Chart:=(false,false)
  have regular (j:J) (s:Chart) : IsIntegral torus (p j s-p j a) := by
    have m:=order_mono (to_torus s a) (compatible j s a)
    have inv:= (Lower6961.RetainedRestrictionTorus.frame_integral (E:=E) s false).1.pow i
    have h:=inv.mul m
    change IsIntegral torus (fr s^i*((fr s)⁻¹^i*(p j s-p j a))) at h
    simpa only [←mul_assoc,←mul_pow,mul_inv_cancel₀
      ((map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s false)),one_pow,one_mul,fr] using h
  let transition (j:J) : charts E i := ⟨fun s=>⟨_,regular j s⟩,fun s t=>by
    change Over s t i ((p j s-p j a)-(p j t-p j a)); rw [sub_sub_sub_cancel_right]; exact compatible j s t⟩
  let family:=(Pi.basisFun L J).constr L transition
  let ev (s:Chart) : charts E i→ₗ[L]E :=
    {toFun:=fun v=>(v.val s:E),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
  have identity (s:Chart) : (ev s).comp family=principalValue p s-principalValue p a := by
    apply (Pi.basisFun L J).ext
    intro j
    rw [LinearMap.comp_apply,LinearMap.sub_apply]
    change ev s (((Pi.basisFun L J).constr L transition) _) =
      ((Pi.basisFun L J).constr L (fun j=>p j s)) _ - ((Pi.basisFun L J).constr L (fun j=>p j a)) _
    simp only [Basis.constr_basis];rfl
  exact ⟨family,fun v s=>LinearMap.congr_fun (identity s) v⟩

private theorem linear_choices {k V U I:Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (eval:I→U→ₗ[k]V) (S:I→Submodule k V) (works:∀u,∃v,∀s,eval s u-v∈S s) :
    ∃ value:U→ₗ[k]V,∀ u s,eval s u-value u∈S s := by
  classical
  let B:=Module.finBasis k U
  choose lift localReg using fun j=>works (B j)
  let value:=B.constr k lift
  refine ⟨value,fun u s=>?_⟩
  let diff:=eval s-value
  have into (j) : diff (B j)∈S s := by
    change eval s (B j)-value (B j)∈S s
    rw [show value (B j)=lift j from B.constr_basis ..]
    exact localReg j s
  change diff u∈S s
  have m : diff (∑ j,B.repr u j • B j) ∈ S s := by
    rw [map_sum]
    exact (S s).sum_mem (fun j _=>by rw [map_smul]; exact (S s).smul_mem _ (into j))
  rwa [B.sum_repr] at m

/-- From local principal parts on the actual surface, construct honest meromorphic
functions in its root field. At most the surface codimension is lost. -/
theorem lift_principal_parts (i n:ℕ) (budget:Budget E i n) (p:J→Chart→E)
    (compatible:∀ j s t,Over s t i (p j s-p j t)) :
    ∃ D:Submodule L (J→L), ∃ value:D→ₗ[L]E,
      Fintype.card J≤n+finrank L D ∧ ∀ (v:D) s,Regular s i (principalValue p s v.val-value v) := by
  classical
  let a:Chart:=(false,false)
  obtain ⟨family,coord⟩:=anchored i p compatible
  obtain ⟨D,count,corr⟩:=budget_subspace E i n budget family
  have works (v:D) : ∃ c:E,∀s,Regular s i (principalValue p s v.val-c) := by
    have hv : ∃ c:E,∀s,Regular s i (((family v.val).val s:E)-c):=corr v
    obtain ⟨c,hc⟩:=hv
    refine ⟨principalValue p a v.val+c,fun s=>?_⟩
    have h:Regular s i (((family v.val).val s:E)-c):=hc s
    rw [coord] at h
    rwa [sub_add_eq_sub_sub]
  have finD : FiniteDimensional L D := FiniteDimensional.of_injective
    (D.subtype : D→ₗ[L](J→L)) Subtype.val_injective
  obtain ⟨value,ok⟩:=linear_choices (k:=L) (U:=↥D) (V:=E) (I:=Chart)
    (fun s=>(principalValue p s).comp D.subtype) (regularSpace i) works
  refine ⟨D,value,?_,?_⟩
  · simpa only [Module.finrank_pi] using count
  · exact fun v s=>ok v s

#print axioms lift_principal_parts
end Lower6961.MarkedEvaluation
