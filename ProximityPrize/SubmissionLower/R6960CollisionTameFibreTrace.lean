import ProximityPrize.SubmissionLower.R6960CollisionTamePlaneDiscriminant

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Module NormalizedFiber
open scoped Polynomial Matrix BigOperators
open private Lower6960.NormalizedFiber.specialize from ProximityPrize.SubmissionLower.R6960NormalizedFiber

variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]

local instance fibreRing (z : k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)

local instance fibreAlgebra (z : k) : Algebra k[X] (Fiber E z) :=
  @RingHom.toAlgebra k[X] (Fiber E z) _ (fibreRing (E:=E) z).toCommSemiring (baseMap E z)

private abbrev FieldDegree (k E : Type) [Field k] [Field E] [Algebra (FractionRing (Plane k)) E] :=
  Fin (finrank (FractionRing (Plane k)) E)

omit [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E] in
private theorem quotient_smul (z : k) (a : Plane k) (x : Order k E) :
    quotientMap E z (a • x)=a.eval (C z) • quotientMap E z x := by
  rw [Algebra.smul_def,map_mul,Algebra.smul_def]
  change quotientMap E z (algebraMap (Plane k) (Order k E) a)*quotientMap E z x=
    baseMap E z (a.eval (C z))*quotientMap E z x
  exact congrArg (· * quotientMap E z x) (Lower6960.NormalizedFiber.specialize E z a)

/-- The restricted generic trace specializes to the actual fibre trace.
The calculation uses the common lift basis and clears the multiplication
columns by a scalar that becomes one on the fibre. -/
theorem trace_reduces_on_fibre (z : k) (b : Basis (FieldDegree k E) k[X] (Fiber E z))
    (bf : Basis (FieldDegree k E) (FractionRing (Plane k)) E)
    (u : FieldDegree k E→Order k E) (g : Plane k)
    (red : ∀ i,quotientMap E z (u i)=b i) (gen : ∀ i,bf i=(u i:E))
    (one : g.eval (C z)=1)
    (patch : ∀ w : Order k E,∃ t : FieldDegree k E→Plane k,(∑ i,t i • u i)=g • w)
    (x : Order k E) :
    (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)) x 1).eval (C z)=
      Algebra.trace k[X] (Fiber E z) (quotientMap E z x) := by
  let A := Plane k
  let F := FractionRing A
  let j := algebraMap A F
  let ev := evalRingHom (C z)
  choose c hc using fun i=>patch (x*u i)
  have sumF (i : FieldDegree k E) :
      (∑ l,j (c i l) • bf l)=((g • x:Order k E):E)*bf i := by
    calc
      _ = ((∑ l,c i l • u l : Order k E):E) := by
        rw [show (((∑ l,c i l • u l : Order k E)):E) = ∑ l,((c i l • u l : Order k E):E)
          from (map_sum (Order k E).val _ _)]
        apply Finset.sum_congr rfl
        intro l _
        rw [gen,Subalgebra.coe_smul,IsScalarTower.algebraMap_smul]
      _ = _ := by
        rw [hc,gen]
        change g • ((x:E)*(u i:E))=(g • (x:E))*(u i:E)
        rw [smul_mul_assoc]
  have sumk (i : FieldDegree k E) :
      (∑ l,ev (c i l) • b l)=quotientMap E z x*b i := by
    calc
      _ = quotientMap E z (∑ l,c i l • u l) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun l _=>by rw [quotient_smul,red]; rfl
      _ = _ := by rw [hc,quotient_smul,one,one_smul,map_mul,red]
  have eq : integralTraceForm (A:=A) (E:=E) F (g • x) 1=∑ i,c i i := by
    apply IsFractionRing.injective A F
    rw [integralTraceForm_map,Subalgebra.coe_one,mul_one,map_sum,Algebra.trace_eq_matrix_trace bf]
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply,Algebra.leftMulMatrix_eq_repr_mul,←sumF i,bf.repr_sum_self]
  have fromA := congrArg ev eq
  rw [(integralTraceForm (A:=A) (E:=E) F).map_smul,LinearMap.smul_apply,smul_eq_mul,map_mul,map_sum] at fromA
  change g.eval (C z)*(integralTraceForm (A:=A) (E:=E) F x 1).eval (C z)=∑ i,ev (c i i) at fromA
  rw [one,one_mul] at fromA
  rw [fromA,Algebra.trace_eq_matrix_trace b]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply,Algebra.leftMulMatrix_eq_repr_mul,←sumk i,b.repr_sum_self]

/-- Literal trace-matrix agreement between the integral coefficients on
the plane and the free basis on the scalar fibre. -/
theorem gram_reduces_on_fibre (z : k) (b : Basis (FieldDegree k E) k[X] (Fiber E z))
    (bf : Basis (FieldDegree k E) (FractionRing (Plane k)) E)
    (u : FieldDegree k E→Order k E) (g : Plane k)
    (red : ∀ i,quotientMap E z (u i)=b i) (gen : ∀ i,bf i=(u i:E))
    (one : g.eval (C z)=1)
    (patch : ∀ w : Order k E,∃ t : FieldDegree k E→Plane k,(∑ i,t i • u i)=g • w) :
    (tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u).map (evalRingHom (C z))=
      Algebra.traceMatrix k[X] b := by
  apply Matrix.ext
  intro i j
  have same : integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)) (u i) (u j)=
      integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)) (u i*u j) 1 := by
    apply IsFractionRing.injective (Plane k) (FractionRing (Plane k))
    rw [integralTraceForm_map,integralTraceForm_map,Subalgebra.coe_mul,Subalgebra.coe_one,mul_one]
  change (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k)) (u i) (u j)).eval (C z)=_
  rw [same,trace_reduces_on_fibre z b bf u g red gen one patch,map_mul,red,red,
    Algebra.traceMatrix_apply,Algebra.traceForm_apply]

/-- A principal plane discriminant generator specializes to the actual
trace determinant of the scalar fibre up to a unit. The denominator of
the chosen frame disappears since it is one on the whole fibre. -/
theorem fibre_trace_det_associated (δ : Plane k)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    (z : k) :
    ∃ b : Basis (FieldDegree k E) k[X] (Fiber E z),
      Associated (Algebra.traceMatrix k[X] b).det (δ.eval (C z)) := by
  obtain ⟨b,bf,u,g,red,gen,one,patch⟩ := scalar_fibre_frames (E:=E) z
  let tr := integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))
  let n := Fintype.card (FieldDegree k E)
  let D := (tupleGram tr u).det
  let j := evalRingHom (C z)
  have divides : δ∣D := by
    have mem : D∈normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k)) :=
      gramIdeal_mem tr u
    rw [principal,Ideal.mem_span_singleton] at mem
    exact mem
  have δmem : δ∈normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k)) := by
    rw [principal]; exact Ideal.subset_span (Set.mem_singleton δ)
  have clear : D∣g^(2*n)*δ := gramIdeal_clear tr u g patch δ δmem
  have rev : j D∣j δ := by
    have d := map_dvd j clear
    rw [map_mul,map_pow,show j g=1 from one,one_pow,one_mul] at d
    exact d
  have eq := congrArg Matrix.det (gram_reduces_on_fibre z b bf u g red gen one patch)
  have det : j D=(Algebra.traceMatrix k[X] b).det := (RingHom.map_det j _).trans eq
  exact ⟨b,det ▸ (dvd_dvd_iff_associated.mp ⟨rev,map_dvd j divides⟩)⟩

#print axioms trace_reduces_on_fibre
#print axioms gram_reduces_on_fibre
#print axioms fibre_trace_det_associated
end
end Lower6960.CollisionTame
