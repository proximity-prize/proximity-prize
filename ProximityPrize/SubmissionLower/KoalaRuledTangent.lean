import ProximityPrize.SubmissionLower.KoalaRuledGraph
import ProximityPrize.SubmissionLower.KoalaRawBounds
import ProximityPrize.SubmissionLower.KoalaRectJetCoords

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.Rect
noncomputable section
open MvPolynomial
open K1_14 (FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten partialX separant)
open HighCore82219Upper (Input ResidueLift Factors)
open HighCore82219Upper_3
open HighCore82219Upper_3_1 (velocity)
open KoalaRectTaylor
open private HighCore82219Upper_3.inversePart HighCore82219Upper_3.inversePart_bound
  HighCore82219Upper_3.tangent_glue from ProximityPrize.SubmissionLower.HighCore82219UpperGeometry

abbrev noVelocity (p : Biform) : Ring FX := rename (fun i => jetAxes (some i)) p

theorem embed_biform {p : Biform} {e v w : ℕ}
    (hp : p ∈ SplitCut.BoxDegree.space FX e v w) : noVelocity p ∈ space FX ⟨e,0,v,w⟩ := by
  classical
  let f : Option (Fin 2) → Fin 4 := fun i => jetAxes (some i)
  have hinj : Function.Injective f := fun _ _ h =>
    Option.some.inj (jetAxes.injective h)
  have hv : (1 : Fin 4) ∉ Set.range f := by
    rintro ⟨i,hi⟩
    cases i with
    | none => exact (by decide : f none ≠ 1) hi
    | some i => fin_cases i <;> exact (by decide : f (some _) ≠ 1) hi
  intro m hm
  change m ∈ (rename f p).support at hm
  rw [support_rename_of_injective hinj] at hm
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
  have h1 := Finsupp.mapDomain_of_notMem_range j (1 : Fin 4) hv
  have h0 : (j.mapDomain f) 0 = j none := Finsupp.mapDomain_apply_of_injective hinj j none
  have h2 : (j.mapDomain f) 2 = j (some 0) := Finsupp.mapDomain_apply_of_injective hinj j (some 0)
  have h3 : (j.mapDomain f) 3 = j (some 1) := Finsupp.mapDomain_apply_of_injective hinj j (some 1)
  change _ ≤ 0 ∧ _ + 2*_ ≤ e+2*0 ∧ _ ≤ v ∧ _ ≤ w
  obtain ⟨he,hv,hw⟩ := hp hj
  exact ⟨h1.le, by simpa [h0,h1] using he, h2.le.trans hv, h3.le.trans hw⟩

theorem add_velocity {p : Ring FX} {e v w : ℕ} (hp : p ∈ space FX ⟨e,0,v,w⟩) :
    MvPolynomial.X (1 : Fin 4)*p ∈ space FX ⟨e,1,v,w⟩ := by
  classical
  intro m hm
  obtain ⟨i,hi,j,hj,rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
  rw [support_X, Finset.mem_singleton] at hi
  subst i
  obtain ⟨h1,h0,h2,h3⟩ := hp hj
  change j 1 ≤ 0 at h1
  change j 0 + 2*j 1 ≤ e+2*0 at h0
  change j 2 ≤ v at h2
  change j 3 ≤ w at h3
  change _ ≤ 1 ∧ _ ≤ e+2*1 ∧ _ ≤ v ∧ _ ≤ w
  simp only [Finsupp.add_apply, Finsupp.single_apply, show (1:Fin 4) ≠ 0 by decide,
    show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, if_true, if_false,
    Nat.zero_add]
  omega

theorem pad_velocity {p : Ring FX} {e v w : ℕ} (hp : p ∈ space FX ⟨e+2,0,v,w⟩) :
    p ∈ space FX ⟨e,1,v,w⟩ := by
  intro m hm
  obtain ⟨h1,h0,h2,h3⟩ := hp hm
  exact ⟨h1.trans (Nat.zero_le 1), h0, h2, h3⟩

theorem inverse_axes (J : Input) {u v : ℕ}
    (h : ∀ i, (J.f.coeff i).degreeOf 0 ≤ u ∧ (J.f.coeff i).degreeOf 1 ≤ v) :
    ∀ i, ((HighCore82219Upper_3.inversePart J).coeff i).degreeOf 0 ≤ u ∧
      ((HighCore82219Upper_3.inversePart J).coeff i).degreeOf 1 ≤ v := by
  intro i
  have hcoeff : (HighCore82219Upper_3.inversePart J).coeff i =
      MvPolynomial.C ((i : FX)-(J.e : FX)) * J.f.coeff i := by
    rw [map_sub, map_natCast, map_natCast]
    cases i with
    | zero => simp [HighCore82219Upper_3.inversePart, neg_mul]
    | succ n =>
      simp only [HighCore82219Upper_3.inversePart, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
      ring
  rw [hcoeff]
  constructor
  · refine (degreeOf_mul_le (0 : Fin 2) _ _).trans ?_
    simpa only [degreeOf_C, Nat.zero_add] using (h i).1
  · refine (degreeOf_mul_le (1 : Fin 2) _ _).trans ?_
    simpa only [degreeOf_C, Nat.zero_add] using (h i).2

abbrev rectRoot {J : Input} {B : ResidueLift J} (D : Factors J B) : Ring FX :=
  jetToRect (Polynomial.C D.proper)

abbrev tangentBox (J : Input) (v w : ℕ) : Box := ⟨J.e-2,1,v,w⟩

/-- The finite tangent and its inverse-ordinate representative have the same two seed caps. -/
theorem tangent_section_rect (J : Input) {B : ResidueLift J} (D : Factors J B) {v w : ℕ}
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w) :
    ∃ S : Section (Ideal.span {rectRoot D}) (tangentBox J v w),
      S.order = 1 ∧ S.finite = jetToRect (tangentEquation J.f) := by
  let dx := (optionEquivLeft FX (Fin 2)) (partialX (flatten J.f))
  let dy := J.f.derivative
  let p := (Polynomial.C dx : JetRing) + velocity * Polynomial.C dy
  let q := ordinate * (Polynomial.C dx : JetRing) +
    velocity * Polynomial.C (HighCore82219Upper_3.inversePart J)
  have hpos : 3 ≤ J.e := J.sheets
  have hf : flatten J.f ∈ SplitCut.BoxDegree.space FX J.e v w := SplitCut.Raw.root le_rfl haxis
  have hx : flatten dx = partialX (flatten J.f) := by simp [dx,flatten]
  have hy : flatten dy = separant (flatten J.f) := by
    apply (optionEquivLeft FX (Fin 2)).injective
    simp only [dy, flatten, separant, optionEquivLeft_pderiv_none, AlgEquiv.apply_symm_apply]
  have e1 : J.e-2+1 = J.e-1 := by omega
  have e2 : J.e-1+2 = J.e+1 := by omega
  have hx₀ : jetToRect (Polynomial.C dx) ∈ space FX ⟨J.e+1,0,v,w⟩ := by
    rw [jetToRect_C, hx]
    exact embed_biform (SplitCut.Raw.grow (Nat.le_succ _) le_rfl le_rfl (SplitCut.Raw.dx hf))
  have hx₁ : jetToRect (ordinate * Polynomial.C dx) ∈ space FX ⟨J.e+1,0,v,w⟩ := by
    rw [map_mul, jetToRect_ordinate, jetToRect_C, hx]
    have hY : (MvPolynomial.X none : Biform) ∈ SplitCut.BoxDegree.space FX 1 0 0 := by
      simp [SplitCut.Raw.fit, degreeOf_X]
    have hXY := SplitCut.BoxDegree.mul_box hY (SplitCut.Raw.dx hf)
    have h := embed_biform hXY
    simpa only [noVelocity, map_mul, rename_X, show jetAxes (some none) = 0 from rfl,
      Nat.add_comm 1, Nat.zero_add] using h
  have hy₀ : jetToRect (Polynomial.C dy) ∈ space FX ⟨J.e-1,0,v,w⟩ := by
    rw [jetToRect_C, hy]
    exact embed_biform (SplitCut.Raw.sep hf)
  have hy₁ : jetToRect (Polynomial.C (HighCore82219Upper_3.inversePart J)) ∈
      space FX ⟨J.e-1,0,v,w⟩ := by
    rw [jetToRect_C]
    exact embed_biform (SplitCut.Raw.root (HighCore82219Upper_3.inversePart_bound J).1 (inverse_axes J haxis))
  refine ⟨⟨1, jetToRect p, jetToRect q, ?_, ?_, ?_⟩, rfl, rfl⟩
  · change jetToRect p ∈ space FX ⟨J.e-2+1,1,v,w⟩
    rw [e1]
    simp only [p, map_add, map_mul, jetToRect_velocity]
    exact Submodule.add_mem _ (pad_velocity (e2.symm ▸ hx₀)) (add_velocity hy₀)
  · change jetToRect q ∈ space FX ⟨J.e-2+1,1,v,w⟩
    rw [e1]
    have hq : jetToRect q = jetToRect (ordinate * Polynomial.C dx) +
        MvPolynomial.X (1 : Fin 4)*jetToRect (Polynomial.C (HighCore82219Upper_3.inversePart J)) := by
      simp only [q, map_add, map_mul, jetToRect_ordinate, jetToRect_velocity]
    rw [hq]
    exact Submodule.add_mem _ (pad_velocity (e2.symm ▸ hx₁)) (add_velocity hy₁)
  · rw [pow_one, ← jetToRect_ordinate, ← map_mul, ← map_sub]
    have he : ordinate * p - q =
        velocity * (Polynomial.C (Polynomial.C (J.e : Seeds)) * Polynomial.C J.f) := by
      exact HighCore82219Upper_3.tangent_glue (A:=Equation) (B:=JetRing)
        (Polynomial.C : Equation →+* JetRing) (Polynomial.X : Equation)
        (Polynomial.C (J.e : Seeds)) J.f dy velocity (Polynomial.C dx)
    rw [he, map_mul, map_mul]
    apply Ideal.mul_mem_left
    apply Ideal.mul_mem_left
    apply Ideal.mem_span_singleton.mpr
    exact map_dvd jetToRect.toRingHom (map_dvd Polynomial.C ⟨_,D.product⟩)

#print axioms tangent_section_rect
end
end SplitCut.Rect
