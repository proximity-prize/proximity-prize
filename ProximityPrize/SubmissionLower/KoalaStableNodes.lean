import ProximityPrize.SubmissionLower.KoalaOpenChart
import ProximityPrize.SubmissionLower.KoalaCompressionMarks

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.Compression
noncomputable section

open Polynomial HighCore82258Upper HighCore82258Upper_3
open HighCore82258Upper_4 (point modelValue origin blocks)
open HighCore82258Upper_3_1_2 (seedMap)
open K1_14 (L FX Equation atMark seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant markEval)
open P1 (K I node p)
open StableFlow LocalModel
open private HighCore82258Upper_3_1_2.eval_coefficient HighCore82258Upper_3_2.mark_C
  HighCore82258Upper_3.seedBiform_image HighCore82258Upper_3_3_1.mark_biform
  HighCore82258Upper_3_3.rootInJet_flatten
  HighCore82258Upper_2.seed_at_mark HighCore82258Upper_2.factorial_ne_zero HighCore82258Upper_5_2.charFX
  from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry

private theorem seed_fit {e v w : ℕ} (g : SeedConstants)
    (hv : g.degreeOf 0 ≤ v) (hw : g.degreeOf 1 ≤ w) :
    seedBiform g ∈ BoxDegree.space FX e v w := by
  have he : seedBiform g = flatten (C (liftSeeds g)) := by
    apply (MvPolynomial.optionEquivLeft FX (Fin 2)).injective
    rw [HighCore82258Upper_3.seedBiform_image]
    exact ((MvPolynomial.optionEquivLeft FX (Fin 2)).apply_symm_apply _).symm
  rw [he]
  apply SplitCut.Raw.root (by simp : (C (liftSeeds g)).natDegree ≤ e)
  intro i
  cases i with
  | zero =>
    rw [Polynomial.coeff_C_zero]
    have h (k : Fin 2) : (liftSeeds g).degreeOf k ≤ g.degreeOf k := by
      simp only [liftSeeds, MvPolynomial.degreeOf_eq_sup]
      exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    exact ⟨(h 0).trans hv,(h 1).trans hw⟩
  | succ i => simp

private theorem mark_seed_projection {J : Input} {B : ResidueLift J} {P : Ideal JetRing}
    (γ : K) (ψ : Chart J B P →+* FX) (hψ : ψ.comp (chartPoint J B P) = (markPoint J γ).toRingHom) :
    ψ.comp (chartSeed J B P) = constantAbscissa.comp (evalSeedConstants (J.model.label γ)) := by
  apply RingHom.ext
  intro g
  change ψ (chartPoint J B P (rootInJet (seedBiform g))) = _
  calc
    _ = markPoint J γ (rootInJet (seedBiform g)) := RingHom.congr_fun hψ _
    _ = markEval (J.model.label γ) (J.family.scalar γ) (seedBiform g) :=
      HighCore82258Upper_3_3_1.mark_biform J γ _
    _ = _ := RingHom.congr_fun (HighCore82258Upper_2.seed_at_mark (J.model.label γ) (J.family.scalar γ)) g

private theorem center_zero_on_curve {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C₀ : CurveMarks J B D) (G : FreshEquation L)
    (hs : ∀ q ∈ C₀.prime, action J.f q ∈ C₀.prime) (hG : C (centerEquation G) ∈ C₀.prime)
    (hw : G.natDegree + J.e*P1_7.degreeAt J.hi < p)
    (hY : ∀ i, (G.coeff i).natDegree ≤ J.e) :
    StableNode.substitute (chartModel J B C₀.prime) (G.map (mapRingHom (chartSeed J B C₀.prime))) = 0 := by
  let P := C₀.prime
  let _ : P.IsPrime := C₀.isPrime
  let E := CurveField P
  let φ := curveMap P
  let ev := φ.comp rootInJet.toRingHom
  let y := φ ordinate
  have hopen : φ (openFactor J B) ≠ 0 := curve_map_nonzero P C₀.regular
  have hnon : ev (seedBiform B.denominator) ≠ 0 ∧ ev (separant (flatten J.f)) ≠ 0 := by
    apply mul_ne_zero_iff.mp
    rwa [chartProduct φ]
  have hsep : HighCore82258Upper_3_1.jetSeparant J.f ∉ P := fun h =>
    C₀.regular (P.mul_mem_left _ h)
  obtain ⟨T, hT⟩ := differential_curve J.f P hsep hs
  have hpoint : ev = point T.ι y := by rw [hT]; exact root_point φ
  have zero (q : JetRing) (hq : q ∈ P) : φ q = 0 := by
    change algebraMap (JetRing ⧸ P) E (Ideal.Quotient.mk P q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  have hf : point T.ι y (flatten J.f) = 0 := by
    rw [← hpoint]
    change φ (rootInJet (flatten J.f)) = 0
    rw [HighCore82258Upper_3_3.rootInJet_flatten]
    have hprod : (C J.f : JetRing) = C D.proper * C (∏ j, D.flat j) :=
      (congrArg (fun q : Equation => (C q : JetRing)) D.product).trans (map_mul C _ _)
    rw [hprod]
    exact zero _ (P.mul_mem_right _ (C₀.onGraph (proper_mem_graph J B D)))
  have ha : T.ι (liftSeeds B.denominator) ≠ 0 := by
    change (T.ι.comp liftSeeds) B.denominator ≠ 0
    rw [← RingHom.congr_fun (JetTaylor.point_seed T y) B.denominator, ← hpoint]
    exact hnon.1
  have hsep' : point T.ι y (separant (flatten J.f)) ≠ 0 := by
    rw [← hpoint]
    exact hnon.2
  have hcut : point T.ι y (quotientNumerator J B (J.ell+1)) = 0 := by
    rw [← hpoint]
    exact zero _ C₀.onCutoff
  have hfac (r : ℕ) (hr : r ≤ J.ell+1) : (r.factorial : E) ≠ 0 := by
    have h := J.factorial_guard
    change 131071+J.hi+1 < p at h
    change r ≤ 131071 - J.w + 1 at hr
    have hh := HighCore82258Upper_2.factorial_ne_zero (show r < p by omega)
    simpa only [map_natCast, map_zero] using T.embed.injective.ne hh
  have hb : (blocks T.ι J).eval (origin T.ι) ≠ 0 := by
    rw [JetTaylor.eval_blocks T]
    have hb' : J.blockProduct ≠ 0 := mul_ne_zero J.chart.1.ne_zero J.chart.2.2.2.1.ne_zero
    exact (map_ne_zero_iff T.embed T.embed.injective).mpr
      ((map_ne_zero_iff (algebraMap L[X] FX) (IsFractionRing.injective L[X] FX)).mpr hb')
  let : CharP FX p := HighCore82258Upper_5_2.charFX
  let : CharP E p := charP_of_injective_ringHom T.embed.injective p
  let S := modelValue T.ι B y
  have hconst := JetTaylor.model_constant T J B y hf ha hsep' hfac hcut
  have hcenter := JetTaylor.model_center T J B y hf ha hsep' hb
  have hroot : (G.map (mapRingHom (T.ι.comp liftSeeds))).eval₂ (evalRingHom (S.eval (origin T.ι)))
      (origin T.ι) = 0 := by
    change (G.map (mapRingHom (T.ι.comp liftSeeds))).eval₂ (evalRingHom ((modelValue T.ι B y).eval (origin T.ι))) _ = _
    rw [hcenter]
    change (G.map (mapRingHom (T.ι.comp liftSeeds))).eval₂ (evalRingHom y) (T.ι (MvPolynomial.C center)) = 0
    rw [← center_eval, hT]
    change (centerEquation G).eval₂ (seedMap φ) (φ ordinate) = 0
    rw [← HighCore82258Upper_3_1_2.eval_coefficient φ]
    exact zero _ hG
  have hz := FreshRoot.root_at_fresh_variable p (T.ι.comp liftSeeds) T.δ (origin T.ι)
    G S T.center_one T.frozen hconst hY (HighCore82258Upper_4.model_width _ _ _ _) hw hroot
  obtain ⟨ψ, hψ, hp, hmodel⟩ := chart_to_curve J B P C₀.regular T hT
  have hseed : ψ.comp (chartSeed J B P) = T.ι.comp liftSeeds := by
    rw [chartSeed, chartBiform, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hp,
      seed_lift_point, hT]
  have hmap : (mapRingHom ψ).comp (mapRingHom (chartSeed J B P)) =
      mapRingHom (T.ι.comp liftSeeds) := by
    apply RingHom.ext
    intro Q
    rw [RingHom.comp_apply, coe_mapRingHom, coe_mapRingHom, map_map, hseed, coe_mapRingHom]
  apply Polynomial.map_injective ψ hψ
  rw [FreshRoot.map_substitute, hmodel, map_map, hmap, Polynomial.map_zero]
  exact hz

theorem stable_node {J : Input} {v w : ℕ} (M : MarkCompression J v w)
    (B : ResidueLift J) (D : Factors J B) (C₀ : CurveMarks J B D) (hgood : C₀.marks ⊆ M.good)
    (hstable : ∀ q ∈ C₀.prime, action J.f q ∈ C₀.prime) (x : I)
    (hfailing : ∃ γ ∈ C₀.marks, (J.family.scalar γ).eval (node x) ≠ J.model.word x) :
    ∃ g : Biform, g ∈ BoxDegree.space FX J.e (v+128) (w+128) ∧ rootInJet g ∉ C₀.prime ∧
      ∀ γ ∈ C₀.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
        markPoint J γ (rootInJet g) = 0 := by
  classical
  let P := C₀.prime
  let _ : P.IsPrime := C₀.isPrime
  by_cases hroot : Polynomial.C (centerEquation M.G) ∈ P
  · let A := Chart J B P
    let θ := chartSeed J B P
    let S := chartModel J B P
    let _ : IsDomain A := chart_domain J B P C₀.regular
    obtain ⟨γ,hγ,hfail⟩ := hfailing
    obtain ⟨ψ,hψ,hspec⟩ := chart_at_mark C₀ γ hγ
    have hgoodγ := (MarkCompression.mem_good M).mp (hgood hγ)
    have hseed := mark_seed_projection γ ψ hψ
    have hneq : ψ (θ M.witness) ≠ 0 := by
      change (ψ.comp θ) M.witness ≠ 0
      rw [hseed]
      have hinj : Function.Injective (constantAbscissa : L →+* FX) :=
        (IsFractionRing.injective L[X] FX).comp Polynomial.C_injective
      exact (map_ne_zero_iff constantAbscissa hinj).mpr hgoodγ.2
    have hGn : M.G.map (mapRingHom θ) ≠ 0 := by
      intro h
      have hz := congrArg (fun G : Polynomial A[X] => (G.coeff M.i).coeff M.j) h
      rw [coeff_map, Polynomial.coeff_zero] at hz
      change ((M.G.coeff M.i).map θ).coeff M.j = 0 at hz
      rw [coeff_map] at hz
      change θ M.witness = 0 at hz
      exact hneq (by rw [hz, map_zero])
    have hfail' : S.eval (θ (MvPolynomial.C (algebraMap K L (node x)))) ≠
        θ (MvPolynomial.C (algebraMap K L (J.model.word x))) := by
      intro h
      have hh := congrArg ψ h
      rw [hspec x] at hh
      change _ = (ψ.comp θ) (MvPolynomial.C (algebraMap K L (J.model.word x))) at hh
      rw [hseed] at hh
      apply hfail
      apply seedEmbedding.injective
      rw [RingHom.comp_apply, evalSeedConstants, MvPolynomial.eval_C] at hh
      exact hh
    have hz := center_zero_on_curve C₀ M.G hstable hroot M.width M.yBound
    obtain ⟨i,j,hn,hcuts⟩ := StableNode.translated_coefficient θ M.G S
      (MvPolynomial.C (algebraMap K L (node x))) (MvPolynomial.C (algebraMap K L (J.model.word x)))
      hGn hz hfail'
    let H := StableNode.translate (MvPolynomial.C (algebraMap K L (node x)))
      (MvPolynomial.C (algebraMap K L (J.model.word x))) M.G
    let g := (H.coeff i).coeff j
    refine ⟨seedBiform g, seed_fit g ?_ ?_, ?_, ?_⟩
    · exact translated_seed_bound M.G _ _ 0 _ (fun m n => (M.axes m n).1) i j
    · exact translated_seed_bound M.G _ _ 1 _ (fun m n => (M.axes m n).2) i j
    · intro hg
      apply hn
      change algebraMap (JetRing ⧸ P) A (Ideal.Quotient.mk P (rootInJet (seedBiform g))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
    · intro η hη hhit
      obtain ⟨ρ,hρ,hev⟩ := chart_at_mark C₀ η hη
      have hseed := mark_seed_projection η ρ hρ
      have h := hcuts ρ (by
        rw [hev x, hhit]
        change _ = (ρ.comp θ) (MvPolynomial.C (algebraMap K L (J.model.word x)))
        rw [hseed]
        simp only [RingHom.comp_apply, evalSeedConstants, MvPolynomial.eval_C]
        rfl)
      exact (RingHom.congr_fun hρ (rootInJet (seedBiform g))).symm.trans h
  · refine ⟨flatten (centerEquation M.G), SplitCut.Raw.root (center_y_bound _ _ M.yBound) ?_, ?_, ?_⟩
    · intro i
      exact ⟨center_axis_bound _ 0 _ (fun j k => (M.axes j k).1) i,
        center_axis_bound _ 1 _ (fun j k => (M.axes j k).2) i⟩
    · rw [HighCore82258Upper_3_3.rootInJet_flatten]
      exact hroot
    · intro γ hγ _
      rw [HighCore82258Upper_3_3.rootInJet_flatten]
      exact (HighCore82258Upper_3_2.mark_C J γ _).trans (M.atMarks γ (C₀.sub hγ))

theorem compress_good (J : Input) (v w : ℕ) (_he : 7 ≤ J.e) (he : J.e ≤ 21)
    (hv : v ≤ 445) (hw : w ≤ 445) (hhi : J.hi ≤ 2535)
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w) :
    ∃ U : Finset K, U ⊆ J.marks ∧ (J.marks \ U).card ≤ (p+1)*(v+w+256) ∧
      ∀ (B : ResidueLift J) (D : Factors J B) (C₀ : CurveMarks J B D), C₀.marks ⊆ U →
        (∀ q ∈ C₀.prime, action J.f q ∈ C₀.prime) → ∀ x : I,
        (∃ γ ∈ C₀.marks, (J.family.scalar γ).eval (node x) ≠ J.model.word x) →
        ∃ g : Biform, g ∈ BoxDegree.space FX J.e (v+128) (w+128) ∧ rootInJet g ∉ C₀.prime ∧
          ∀ γ ∈ C₀.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
            markPoint J γ (rootInJet g) = 0 := by
  obtain ⟨M⟩ := compress_marks J v w he hv hw hhi haxis
  exact ⟨M.good, fun _ hγ => ((MarkCompression.mem_good M).mp hγ).1, M.bad_bound hv, stable_node M⟩

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compress_good
