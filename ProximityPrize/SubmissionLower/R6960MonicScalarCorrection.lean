import ProximityPrize.SubmissionLower.R6960MonicChartLaurent

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.MonicScalarCorrection
noncomputable section
open MonicChart (ChartField)
open MonicFourChartDescent (baseChart frame frame_scale constants)
open MonicChartLaurent
open ChartSections (Chart Exponent overlap allowed)

/-- The differences of chart potentials are integral on the actual
normalized overlaps in the source chart's frame. -/
def Compatible {E : Type*} [Field E] [Algebra ChartField E]
    (a b : ℕ) (u : Chart → E) : Prop :=
  ∀ s t, IsIntegral (overlapRing s t) (algebraMap ChartField E (frame a b s)*(u s-u t))

/-- Scalar compatibility uses membership in the actual overlap subring. -/
def ScalarCompatible (a b : ℕ) (u : Chart → ChartField) : Prop :=
  ∀ s t, frame a b s*(u s-u t) ∈ overlapRing s t

/-- Before expanding, remove an arbitrary common potential. The resulting
coefficients record exactly the support conditions on all six overlaps. -/
theorem scalar_coefficients (a b : ℕ) (u : Chart → ChartField) (h : ScalarCompatible a b u)
    (anchor : Chart) : ∃ q : Chart → Coefficients,
      (∀ s,eval (q s)=u s-u anchor) ∧
      ∀ s t m,¬overlap a b s t m → q s m=q t m := by
  classical
  have exists_laurent (s : Chart) : ∃ q : Coefficients,eval q=u s-u anchor := by
    obtain ⟨v,hv,_⟩ := (mem_overlap_iff s anchor _).mp (h s anchor)
    let m := frameExponent a b s
    have cancel : monomial (-m)*monomial m=1 := by
      rw [←monomial_add,neg_add_cancel,monomial_zero]
    refine ⟨translate (-m) v,?_⟩
    rw [eval_translate,hv,frame_eq_monomial,←mul_assoc,cancel,one_mul]
  choose q eq using exists_laurent
  refine ⟨q,eq,?_⟩
  intro s t m forbidden
  have diff : eval (q s-q t)=u s-u t := by
    rw [map_sub,eq,eq]
    ring
  have support : ∀ n∈(q s-q t).support,overlap a b s t n :=
    (frame_eval_mem_overlap_iff a b s t (q s-q t)).mp (by simpa only [diff] using h s t)
  exact sub_eq_zero.mp (Finsupp.notMem_support_iff.mp (fun hm=>forbidden (support m hm)))

/-- Compatible scalar potentials for a twist negative in both directions
have a common correction in the actual rational function field. -/
theorem scalar_correction (a b : ℕ) (ha : 0<a) (hb : 0<b) (u : Chart → ChartField)
    (h : ScalarCompatible a b u) :
    ∃ c : ChartField,∀ s,frame a b s*(u s-c)∈baseChart s := by
  let anchor : Chart := (false,false)
  obtain ⟨q,eq,condition⟩ := scalar_coefficients a b u h anchor
  obtain ⟨v,hv⟩ := ChartSections.negative_correction a b ha hb q condition
  refine ⟨eval v+u anchor,fun s=>?_⟩
  have diff : eval (q s-v)=u s-(eval v+u anchor) := by
    rw [map_sub,eq]
    ring
  rw [←diff,frame_eval_mem_baseChart_iff]
  intro m hm
  by_contra bad
  exact Finsupp.mem_support_iff.mp hm (hv s m bad)

/-- Compatibility on the actual overlaps is preserved by every iterate
of Frobenius with the corresponding rescaled twist. -/
theorem compatible_iterate {E : Type*} [Field E] [Algebra ChartField E]
    (a b : ℕ) (u : Chart → E) (h : Compatible a b u) (n : ℕ) :
    Compatible (a*K1.p^n) (b*K1.p^n) (fun s=>u s^(K1.p^n)) := by
  let : Fact K1.p.Prime := ⟨KoalaBear.is_prime⟩
  let : CharP E K1.p := charP_of_injective_ringHom ((algebraMap ChartField E).comp constants).injective K1.p
  intro s t
  have subpow : (u s-u t)^(K1.p^n)=u s^(K1.p^n)-u t^(K1.p^n) :=
    map_sub (iterateFrobenius E K1.p n) (u s) (u t)
  have powered := (h s t).pow (K1.p^n)
  rw [mul_pow,subpow,←map_pow,←frame_scale] at powered
  exact powered

#print axioms scalar_coefficients
#print axioms scalar_correction
#print axioms compatible_iterate
end
end Lower6960.MonicScalarCorrection
