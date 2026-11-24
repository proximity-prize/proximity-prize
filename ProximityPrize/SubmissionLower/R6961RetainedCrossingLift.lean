import ProximityPrize.SubmissionLower.R6961RetainedRestrictionTorus

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedRestrictionTorus
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.ChartSections (Chart)
open MonicFourChartDescent MonicChartProbes ChartOverlapTests Polynomial
open scoped Polynomial
open Lower6961.RetainedRestrictionTorus (linear)

private def cx (s : Chart) : baseChart s := planeEquiv s Polynomial.X
private def cz (s : Chart) : baseChart s := planeEquiv s (C Polynomial.X)
private def kc (s : Chart) : L→+*baseChart s := (planeEquiv s).toRingHom.comp (C.comp C)

private theorem shapeX (s : Chart) (x:L) : xcut s x =
    if s.1 then 1-kc s x*cx s else cx s-kc s x := by
  unfold xcut Lower6961.RetainedRestrictionTorus.linear
  split <;> simp [kc,cx,map_sub,map_one,map_mul]

private theorem shapeZ (s : Chart) (z:L) : zcut s z =
    if s.2 then 1-kc s z*cz s else cz s-kc s z := by
  unfold zcut Lower6961.RetainedRestrictionTorus.linear
  split <;> simp [kc,cz,map_sub,map_one,map_mul]

private theorem edge_eq (s : Chart) : edge s (opposite s)=cx s*cz s := by
  apply Subtype.ext
  change boundary s (opposite s)=planeMap s Polynomial.X*planeMap s (C Polynomial.X)
  rw [planeMap_abscissa,planeMap_scalar]
  rcases s with ⟨i,j⟩; cases i <;> cases j <;> simp [boundary,opposite]

private theorem unit_at_node {R : Type*} [CommRing R] (π : L→+*R) (b : Bool) (c : L) (nc:c≠0)
    (v:R) (zero : (if b then 1-π c*v else v-π c)=0) : IsUnit v := by
  cases b with
  | false =>
    change v-π c=0 at zero
    exact (sub_eq_zero.mp zero) ▸ nc.isUnit.map π
  | true =>
    change 1-π c*v=0 at zero
    exact ⟨⟨v,π c,(mul_comm ..).trans (sub_eq_zero.mp zero).symm,(sub_eq_zero.mp zero).symm⟩,rfl⟩

variable {E : Type*} [Field E] [Algebra ChartField E]

/-- Local line representatives matching at the crossing on the torus have one
representative on the whole normalized affine chart. This includes the boundary
of the chart, where its two coordinate functions need not be units. -/
theorem lift_on_chart (s : Chart) (x z : L) (nx:x≠0) (nz:z≠0) (u v : E)
    (hu:IsIntegral (baseChart s) u) (hv:IsIntegral (baseChart s) v)
    (matchPoint : ∃ a b:E,IsIntegral torus a ∧ IsIntegral torus b ∧
      u-v=algebraMap (baseChart s) E (xcut s x)*a+algebraMap (baseChart s) E (zcut s z)*b) :
    ∃ y a b:E,IsIntegral (baseChart s) y ∧ IsIntegral (baseChart s) a ∧
      IsIntegral (baseChart s) b ∧ u-y=algebraMap (baseChart s) E (xcut s x)*a ∧
      y-v=algebraMap (baseChart s) E (zcut s z)*b := by
  let A:=baseChart s
  let S:=integralClosure A E
  let ι:=algebraMap A S
  let p:=ι (xcut s x)
  let q:=ι (zcut s z)
  let I:=Ideal.span ({p}:Set S)⊔Ideal.span {q}
  let π:=Ideal.Quotient.mk I
  let g:=edge s (opposite s)
  have pzero : π p=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton p)))
  have qzero : π q=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton q)))
  have ux : IsUnit (π (ι (cx s))) := by
    apply unit_at_node (R:=↥S ⧸ I) ((π.comp ι).comp (kc s)) s.1 x nx (π (ι (cx s)))
    change π (ι (xcut s x))=0 at pzero
    rw [shapeX] at pzero
    by_cases hs:s.1=true <;> simpa [hs] using pzero
  have uz : IsUnit (π (ι (cz s))) := by
    apply unit_at_node (R:=↥S ⧸ I) ((π.comp ι).comp (kc s)) s.2 z nz (π (ι (cz s)))
    change π (ι (zcut s z))=0 at qzero
    rw [shapeZ] at qzero
    by_cases hs:s.2=true <;> simpa [hs] using qzero
  have unit : IsUnit (π (ι g)) := by
    change IsUnit (π (ι (edge s (opposite s))))
    rw [edge_eq,map_mul,map_mul]; exact ux.mul uz
  obtain ⟨a,b,ia,ib,eq⟩:=matchPoint
  obtain ⟨m,cm⟩:=clear_torus s _ ia
  obtain ⟨n,cn⟩:=clear_torus s _ ib
  let U:S:=⟨u,hu⟩
  let V:S:=⟨v,hv⟩
  let G:=algebraMap A E g
  let ca:S:=⟨G^m*a,cm⟩
  let cb:S:=⟨G^n*b,cn⟩
  have cleared : (ι g)^(m+n)*(U-V)=p*((ι g)^n*ca)+q*((ι g)^m*cb) := by
    apply Subtype.ext
    change G^(m+n)*(u-v)=algebraMap A E (xcut s x)*(G^n*(G^m*a))+
      algebraMap A E (zcut s z)*(G^m*(G^n*b))
    rw [eq,pow_add]; ring
  have zero : π (U-V)=0 := by
    apply (unit.pow (m+n)).mul_right_inj.mp
    rw [mul_zero,←map_pow,←map_mul,cleared,map_add,map_mul,pzero,zero_mul,map_mul,qzero,zero_mul,add_zero]
  obtain ⟨_,hp,_,hq,sum⟩:=Submodule.mem_sup.mp (show U-V ∈ I from Ideal.Quotient.eq_zero_iff_mem.mp zero)
  obtain ⟨a',rfl⟩:=Ideal.mem_span_singleton.mp hp
  obtain ⟨b',rfl⟩:=Ideal.mem_span_singleton.mp hq
  let y:=U-p*a'
  refine ⟨y,a',b',y.property,a'.property,b'.property,?_,?_⟩
  · exact congrArg Subtype.val (show U-y=p*a' from sub_sub_cancel ..)
  · have lift : y-V=q*b' := by
      change U-p*a'-V=q*b'
      calc _ = U-V-p*a' := by abel
           _ = _ := by rw [←sum,add_sub_cancel_left]
    exact congrArg (fun w:S=>(w:E)) lift

#print axioms lift_on_chart
end Lower6961.RetainedRestrictionTorus
