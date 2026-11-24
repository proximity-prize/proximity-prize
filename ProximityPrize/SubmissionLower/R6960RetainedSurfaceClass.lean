import ProximityPrize.SubmissionLower.R6960RetainedPairedResidues
import ProximityPrize.SubmissionLower.R6960RetainedNodalIndex

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

private theorem raw_zero (x z:L) (u:potentials E) : rawMap E x z u=0 ↔
    ∃ v:Bool→Tor E, ∃ w:Bool→Tor E,
      (∀ b,IsIntegral (baseChart (reference false b)) (v b:E)) ∧
      (∀ b,IsIntegral (baseChart (reference true b)) (w b:E)) ∧
      red E false x (u.1 (false,false)-u.1 (reference false true))=red E false x (v false-v true) ∧
      red E true z (u.1 (false,false)-u.1 (reference true true))=red E true z (w false-w true) ∧
      (Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z)) (v false) =
        Ideal.Quotient.mk _ (w false) := by
  rw [show rawMap E x z u=0 ↔ _ from Submodule.Quotient.mk_eq_zero _]
  constructor
  · rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,eq,edge⟩
    obtain ⟨v0,iv0,h0⟩:=a.property
    obtain ⟨v1,iv1,h1⟩:=b.property
    obtain ⟨w0,iw0,g0⟩:=c.property
    obtain ⟨w1,iw1,g1⟩:=d.property
    let v (i:Bool):Tor E:=if i then v1 else v0
    let w (i:Bool):Tor E:=if i then w1 else w0
    refine ⟨v,w,(fun i=>by cases i <;> first | exact iv0 | exact iv1),
      (fun i=>by cases i <;> first | exact iw0 | exact iw1),?_,?_,?_⟩
    · change _=red E false x (v0-v1)
      rw [map_sub (red E false x) v0 v1,h0,h1]
      have e:= (congrArg Prod.fst edge).symm
      change red E false x (u.1 (false,false)-u.1 (reference false true))=a.1+ -b.1 at e
      simpa only [sub_eq_add_neg] using e
    · change _=red E true z (w0-w1)
      rw [map_sub (red E true z) w0 w1,g0,g1]
      have e:= (congrArg Prod.snd edge).symm
      change red E true z (u.1 (false,false)-u.1 (reference true true))=c.1+ -d.1 at e
      simpa only [sub_eq_add_neg] using e
    · change crossingX E x z a.1+ -(crossingZ E x z c.1)=0 at eq
      rw [←h0,←g0] at eq
      change (Ideal.Quotient.mk _ v0)+ -(Ideal.Quotient.mk _ w0)=0 at eq
      rw [←sub_eq_add_neg] at eq
      exact sub_eq_zero.mp eq
  · rintro ⟨v,w,iv,iw,ex,ez,node⟩
    let a (i:Bool): chartImage E false x i:=⟨_,⟨v i,iv i,rfl⟩⟩
    let b (i:Bool): chartImage E true z i:=⟨_,⟨w i,iw i,rfl⟩⟩
    refine ⟨((a false,a true),(b false,b true)),?_,?_⟩
    · change Ideal.Quotient.mk _ (v false)+ -Ideal.Quotient.mk _ (w false)=0
      rw [node,add_neg_cancel]
    · apply Prod.ext
      · change red E false x (v false)+ -(red E false x (v true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ex.symm
      · change red E true z (w false)+ -(red E true z (w true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ez.symm

theorem congr_of_eq (j c) (a b:Tor E) (eq : red E j c a=red E j c b) :
    Congruent j c (a:E) (b:E) := by
  obtain ⟨r,hr⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp eq)
  exact ⟨r,r.property,congrArg Subtype.val hr⟩

private theorem matched_of_eq (x z:L) (a b:Tor E)
    (eq : Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z) a=Ideal.Quotient.mk _ b) :
    Matched x z (a:E) (b:E) := by
  obtain ⟨u,hu,v,hv,l⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq.mp eq)
  obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨t,rfl⟩:=Ideal.mem_span_singleton.mp hv
  exact ⟨r,t,r.property,t.property,congrArg Subtype.val l.symm⟩

open RetainedCompression (Curve ordinate view height heightCap wordDegree)

/-- The actual bounded cover's untwisted obstruction space embeds in the quotient
formed by the two torus fibres and a single shared crossing. -/
theorem restriction_kernel (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) :
    (rawMap E x z).ker=coboundaries E := by
    ext u
    change rawMap E x z u=0 ↔ ∃ c:E,∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)
    rw [raw_zero]
    constructor
    · rintro ⟨v,w,iv,iw,ex,ez,node⟩
      have r:=split_of_paired_data f ir lo hi bounded basis root x z nx nz
        (fun s=>(u.1 s:E)) u.property (fun b=>(v b:E)) (fun b=>(w b:E))
        ⟨iv,congr_of_eq E false x _ _ ex⟩ ⟨iw,congr_of_eq E true z _ _ ez⟩
        (matched_of_eq E x z _ _ node)
      obtain ⟨c,hc⟩:=r
      exact ⟨c,fun s=>by simpa [frame] using hc s⟩
    · rintro ⟨c,hc⟩
      have ic : IsIntegral torus c := by
        have ii:=(u.1 (false,false)).property.sub (order_mono (base_torus (false,false)) (hc (false,false)))
        simpa only [sub_sub_cancel] using ii
      let ct : Tor E:=⟨c,ic⟩
      let v (j b:Bool):Tor E:=u.1 (reference j b)-ct
      have start (j:Bool) : reference j false=(false,false) := by cases j <;> rfl
      refine ⟨v false,v true,(fun b=>hc _),(fun b=>hc _),?_,?_,?_⟩
      · apply congrArg (red E false x); simp only [v,start]; abel
      · apply congrArg (red E true z); simp only [v,start]; abel
      · rfl
#print axioms restriction_kernel
end Lower6960.RetainedSurfaceClass
