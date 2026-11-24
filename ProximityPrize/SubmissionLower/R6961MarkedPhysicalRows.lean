import ProximityPrize.SubmissionLower.R6961MarkedColumnPlace
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField Scalar)
open MonicFourChartDescent RetainedRestrictionTorus RetainedSurfaceClass RetainedTwistedRestriction
open Polynomial Finset Algebra Module
open scoped Polynomial BigOperators Lower6961.RetainedSurfaceClass Lower6961.MarkedEvaluation
local instance : DecidableEq Scalar := Classical.decEq _
local instance : DecidableEq ChartField := Classical.decEq _
local instance (priority := 2200) : SMul (Polynomial Scalar) ChartField :=
  (inferInstance : Algebra (Polynomial Scalar) ChartField).toSMul
variable {E Ω I J:Type} [Field E] [Field Ω] [Algebra ChartField E] [Algebra ChartField Ω]
  [Algebra (Polynomial Scalar) Ω] [IsScalarTower (Polynomial Scalar) ChartField Ω] [FiniteDimensional ChartField Ω] [IsGalois ChartField Ω]
  [Fintype I] [DecidableEq I]
local notation "G" => Lower6960.SheetNorm.Aut Scalar Ω
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

#print axioms actual_place_rows
end Lower6961.MarkedEvaluation
