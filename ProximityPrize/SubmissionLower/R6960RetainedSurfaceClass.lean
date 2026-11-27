import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import ProximityPrize.SubmissionLower.R6960RetainedPairedResidues

set_option Elab.async false

-- merged module R6960RetainedNodalIndex
section Merged_R6960RetainedNodalIndex
noncomputable section
set_option Elab.async false
namespace Lower6960.RetainedNodalIndex
open Module LinearMap Submodule
variable {k M N U V C : Type*} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V] [AddCommGroup C] [Module k C]
def boundaries (d₁ : M→ₗ[k]U) (d₂ : N→ₗ[k]V) (x : M→ₗ[k]C) (z : N→ₗ[k]C) :
    Submodule k (U×V) :=
  (LinearMap.ker (x.coprod (-z))).map (d₁.prodMap d₂)
private theorem representative (d : M→ₗ[k]U) :
    ∃ p : U→ₗ[k]M, ∀ x∈d.range, d (p x)=x := by
  obtain ⟨r,hr⟩:=d.rangeRestrict.exists_rightInverse_of_surjective d.range_rangeRestrict
  obtain ⟨q,hq⟩:=d.range.exists_isCompl
  refine ⟨r.comp (d.range.projectionOnto q hq),fun x hx=>?_⟩
  have l:=LinearMap.congr_fun hr (⟨x,hx⟩ : d.range)
  rw [comp_apply,projectionOnto_apply_of_mem_left hq hx]
  exact congrArg Subtype.val l
theorem dimension (d₁ : M→ₗ[k]U) (d₂ : N→ₗ[k]V) (x : M→ₗ[k]C) (z : N→ₗ[k]C)
    [FiniteDimensional k (U ⧸ d₁.range)] [FiniteDimensional k (V ⧸ d₂.range)] [FiniteDimensional k C] :
    let B := boundaries d₁ d₂ x z
    let W := d₁.ker.map x ⊔ d₂.ker.map z
    FiniteDimensional k ((U×V) ⧸ B) ∧
      finrank k ((U×V) ⧸ B)+finrank k W ≤
        finrank k (U ⧸ d₁.range)+finrank k (V ⧸ d₂.range)+finrank k C := by
  let B:=boundaries d₁ d₂ x z
  let W:=d₁.ker.map x ⊔ d₂.ker.map z
  let J:=x.coprod (-z)
  obtain ⟨p,hp⟩:=representative d₁
  obtain ⟨q,hq⟩:=representative d₂
  let pick:=p.prodMap q
  let h: (U×V) →ₗ[k] ((U ⧸ d₁.range)×(V ⧸ d₂.range))×(C ⧸ W) :=
    (d₁.range.mkQ.prodMap d₂.range.mkQ).prod (W.mkQ.comp (J.comp pick))
  have kernel : h.ker=B := by
    ext e
    rcases e with ⟨u,v⟩
    have calc_ker : (u,v)∈h.ker ↔ u∈d₁.range ∧ v∈d₂.range ∧ x (p u)-z (q v)∈W := by
      change ((d₁.range.mkQ u,d₂.range.mkQ v),W.mkQ (x (p u)+ -z (q v)))=0 ↔ _
      simp only [Prod.mk_eq_zero,←sub_eq_add_neg,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,and_assoc]
    rw [calc_ker]
    constructor
    · rintro ⟨hu,hv,hj⟩
      obtain ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,eq⟩:=Submodule.mem_sup.mp hj
      refine ⟨(p u-a,q v+b),?_,?_⟩
      · change x (p u-a)+(-z) (q v+b)=0
        rw [map_sub,LinearMap.neg_apply,map_add]
        calc _ = (x (p u)-z (q v))-(x a+z b) := by abel
             _ = 0 := sub_eq_zero.mpr eq.symm
      · change (d₁ (p u-a),d₂ (q v+b))=(u,v)
        rw [map_sub,map_add,mem_ker.mp ha,mem_ker.mp hb,hp u hu,hq v hv,sub_zero,add_zero]
    · rintro ⟨⟨a,b⟩,join,eq⟩
      obtain ⟨rfl,rfl⟩: d₁ a=u ∧ d₂ b=v :=
        ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
      change x a+(-z) b=0 at join
      have ju : x a=z b := sub_eq_zero.mp (by simpa only [LinearMap.neg_apply,←sub_eq_add_neg] using join)
      have h₁ : p (d₁ a)-a∈d₁.ker := by rw [mem_ker,map_sub,hp _ ⟨a,rfl⟩,sub_self]
      have h₂ : b-q (d₂ b)∈d₂.ker := by rw [mem_ker,map_sub,hq _ ⟨b,rfl⟩,sub_self]
      refine ⟨⟨a,rfl⟩,⟨b,rfl⟩,Submodule.mem_sup.mpr ⟨_,⟨_,h₁,rfl⟩,_,⟨_,h₂,rfl⟩,?_⟩⟩
      rw [map_sub,map_sub,ju]; abel
  let e:=((Submodule.quotEquivOfEq B h.ker kernel.symm).trans h.quotKerEquivRange)
  have : FiniteDimensional k ((U×V) ⧸ B) := FiniteDimensional.of_injective e.toLinearMap e.injective
  have bound:=Submodule.finrank_le h.range
  rw [←e.finrank_eq,Module.finrank_prod,Module.finrank_prod] at bound
  refine ⟨inferInstance,?_⟩
  change finrank k ((U×V) ⧸ B)+finrank k W ≤ _
  have eq:=W.finrank_quotient_add_finrank
  omega
end Lower6960.RetainedNodalIndex

end
end Merged_R6960RetainedNodalIndex

-- merged module R6960RetainedSurfaceClass
section Merged_R6960RetainedSurfaceClass

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedSurfaceClass
open ChartSections (Chart)
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6960.MonicChartLaurent

variable (E : Type) [Field E] [Algebra ChartField E]
abbrev Tor := integralClosure torus E

private def constantsTor : L →+* Tor E :=
  ((algebraMap (↥torus) (Tor E)).comp (constants.codRestrict torus
    (fun c=>base_torus (false,false) (chart_constant _ c))))
scoped instance constantAlgebra : Algebra L (Tor E) := (constantsTor E).toAlgebra
open scoped Lower6960.RetainedSurfaceClass

private def scalar (a:ChartField) (reg:a∈torus) : Tor E :=
  algebraMap (↥torus) (Tor E) ⟨a,reg⟩

def cut (j : Bool) (c:L) : Tor E := scalar E (divisor j c) (torus.sub_mem
  (torus_coordinate j false) (base_torus (false,false) (chart_constant _ c)))

def axisIdeal (j:Bool) (c:L) : Ideal (Tor E) := Ideal.span {cut E j c}
abbrev Axis (j:Bool) (c:L) := (Tor E) ⧸ axisIdeal E j c
abbrev Crossing (x z:L) := Tor E ⧸ (axisIdeal E false x ⊔ axisIdeal E true z)
abbrev red (j:Bool) (c:L) : Tor E →ₗ[L] Axis E j c :=
  (Ideal.Quotient.mkₐ L (axisIdeal E j c)).toLinearMap

def crossingX (x z:L) : Axis E false x →ₗ[L] Crossing E x z :=
  (Ideal.Quotient.factorₐ L (show axisIdeal E false x ≤ axisIdeal E false x ⊔ axisIdeal E true z from le_sup_left)).toLinearMap
def crossingZ (x z:L) : Axis E true z →ₗ[L] Crossing E x z :=
  (Ideal.Quotient.factorₐ L (show axisIdeal E true z ≤ axisIdeal E false x ⊔ axisIdeal E true z from le_sup_right)).toLinearMap

def chartSpace (s:Chart) : Submodule L (Tor E) where
  carrier:={u | IsIntegral (baseChart s) (u:E)}
  zero_mem' := isIntegral_zero
  add_mem' a b:=a.add b
  smul_mem' r _ hu:=
    (isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant s r⟩:baseChart s))).mul hu

def chartImage (j:Bool) (c:L) (bit:Bool) :=
  (chartSpace E (reference j bit)).map (red E j c)

def difference (j:Bool) (c:L) :
    (chartImage E j c false × chartImage E j c true) →ₗ[L] Axis E j c :=
  (chartImage E j c false).subtype.coprod (-(chartImage E j c true).subtype)

def evalX (x z:L) := (crossingX E x z).comp
  ((chartImage E false x false).subtype.comp (LinearMap.fst L (chartImage E false x false) (chartImage E false x true)))
def evalZ (x z:L) := (crossingZ E x z).comp
  ((chartImage E true z false).subtype.comp (LinearMap.fst L (chartImage E true z false) (chartImage E true z true)))
abbrev Paired (x z:L) := (Axis E false x × Axis E true z) ⧸
  RetainedNodalIndex.boundaries (difference E false x) (difference E true z) (evalX E x z) (evalZ E x z)

def potentials : Submodule L (Chart→Tor E) where
  carrier := {u | ∀ s t, IsIntegral (overlapRing s t) ((u s:E)-(u t:E))}
  zero_mem' := fun s t=>by simpa using (isIntegral_zero (B:=E) (R:=overlapRing s t))
  add_mem' {u v} hu hv s t := by
    change IsIntegral _ (((u s:E)+v s)-((u t:E)+v t))
    convert (hu s t).add (hv s t) using 1 <;> abel
  smul_mem' r u hu s t := by
    change IsIntegral _ ((algebraMap ChartField E (constants r))*(u s:E)-(algebraMap ChartField E (constants r))*(u t:E))
    rw [←mul_sub]
    exact (isIntegral_algebraMap (A:=E) (x:=(⟨constants r,into_cleared _ (edge s t) (chart_constant s r)⟩:overlapRing s t))).mul (hu s t)

def coboundaries : Submodule L (potentials E) where
  carrier := {u | ∃ c:E, ∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)}
  zero_mem' := ⟨0,fun s=>by simpa using (isIntegral_zero (B:=E) (R:=baseChart s))⟩
  add_mem' {u v} hu hv := by
    obtain ⟨c,hc⟩:=hu; obtain ⟨d,hd⟩:=hv
    refine ⟨c+d,fun s=>?_⟩
    change IsIntegral _ (((u.1 s:E)+v.1 s)-(c+d))
    convert (hc s).add (hd s) using 1 <;> abel
  smul_mem' r u hu := by
    obtain ⟨c,hc⟩:=hu
    let scalar:=algebraMap ChartField E (constants r)
    refine ⟨scalar*c,fun s=>?_⟩
    change IsIntegral _ (scalar*(u.1 s:E)-scalar*c)
    rw [←mul_sub]
    exact (isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant s r⟩:baseChart s))).mul (hc s)

private def atChart (s:Chart) : potentials E→ₗ[L]Tor E :=
  (LinearMap.proj s).comp (potentials E).subtype
def rawMap (x z:L) : potentials E →ₗ[L] Paired E x z :=
  let lines:=(red E false x ∘ₗ (atChart E (false,false)-atChart E (reference false true))).prod
    (red E true z ∘ₗ (atChart E (false,false)-atChart E (reference true true)))
  (RetainedNodalIndex.boundaries (difference E false x) (difference E true z) (evalX E x z) (evalZ E x z)).mkQ.comp lines















































theorem congr_of_eq (j c) (a b:Tor E) (eq : red E j c a=red E j c b) :
    Congruent j c (a:E) (b:E) := by
  obtain ⟨r,hr⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp eq)
  exact ⟨r,r.property,congrArg Subtype.val hr⟩









open RetainedCompression (Curve ordinate view height heightCap)































end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedSurfaceClass
