import ProximityPrize.SubmissionLower.KoalaJetTaylor
import ProximityPrize.SubmissionLower.HighCore82258UpperCertificates
import ProximityPrize.SubmissionLower.PortLow6

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.StableFlow
noncomputable section

open Polynomial HighCore82258Upper HighCore82258Upper_3 HighCore82258Upper_3_1
open HighCore82258Upper_3_1_2 (seedMap sepAlong)
open HighCore82258Upper_4 (SplitField geomRoots coeffDx point)
open K1_14 (FX Seeds Equation)
open K1_14_6_1 (flatten separant)
open private HighCore82258Upper_3_1_1.flow HighCore82258Upper_3_1_1.flow_mul
  HighCore82258Upper_3_1_1.flow_C HighCore82258Upper_3_1_1.coeffDiff_derivative
  HighCore82258Upper_3_2_1.clear_velocity HighCore82258Upper_4_1.intDerivation
  HighCore82258Upper_4_1.transportIntAlgebra HighCore82258Upper_4_1.transportIntAlgebra_apply
  HighCore82258Upper_4_2.point_flatten HighCore82258Upper_2.factorial_ne_zero
  from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
open private HighCore82258GeometryCert_1.firstJet HighCore82258GeometryCert_1.firstJet_graph
  HighCore82258GeometryCert_1.derivationOfJet HighCore82258GeometryCert_1.coeffDiff_C
  HighCore82258GeometryCert_1.root_chain HighCore82258GeometryCert_1.jet_chain
  HighCore82258GeometryCert_1.deriv_mul
  from ProximityPrize.SubmissionLower.HighCore82258UpperCertificates
open private P0_9_6_3.stable_of_simple_cut from ProximityPrize.SubmissionLower.PortLow6
open private lift_derivation from ProximityPrize.SubmissionLower.Fast073

abbrev action (f : Equation) : JetRing →+ JetRing := HighCore82258Upper_3_1_1.flow f

theorem flow_mem_graph (J : Input) (B : ResidueLift J) (D : Factors J B) :
    ∀ N ∈ graphIdeal J B D, action J.f N ∈ graphIdeal J B D := by
  let Q := graphIdeal J B D
  let q := Ideal.Quotient.mk Q
  let g := q (openFactor J B)
  let A := Localization.Away g
  let ψ : JetRing →+* A := (algebraMap (JetRing ⧸ Q) A).comp q
  have hker (N : JetRing) : ψ N = 0 ↔ N ∈ Q := by
    constructor
    · intro hN
      obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff
        (Submonoid.powers g) A (q N)).mp hN
      obtain ⟨n, hn⟩ := c.property
      rw [← hn] at hc
      change q (openFactor J B)^n * q N = 0 at hc
      rw [← map_pow, ← map_mul] at hc
      obtain ⟨m, hm⟩ := (Ideal.Quotient.eq_zero_iff_mem.mp hc : (openFactor J B)^n * N ∈ Q)
      exact ⟨m+n, by rwa [pow_add, mul_assoc]⟩
    · intro hN
      change algebraMap (JetRing ⧸ Q) A (q N) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hN, map_zero]
  have hg : IsUnit (ψ (openFactor J B)) := IsLocalization.Away.algebraMap_isUnit g
  have hs : IsUnit (ψ (jetSeparant J.f)) := by
    apply isUnit_of_dvd_unit _ hg
    exact map_dvd ψ ⟨residueInJet B, mul_comm _ _⟩
  have hp := (hker _).mpr (proper_mem_graph J B D)
  have ht := (hker _).mpr (le_saturate _ _ (Ideal.subset_span (by simp)) :
    tangentEquation J.f ∈ Q)
  intro N hN
  apply (hker _).mp
  exact congrArg TrivSqZeroExt.snd
    (HighCore82258GeometryCert_1.firstJet_graph J B D ψ hp ht hs hg N hN)

private def derivation (f : Equation) :=
  HighCore82258Upper_4_1.intDerivation (action f) (fun x y => by
    rw [HighCore82258Upper_3_1_1.flow_mul, mul_comm y])

/-- Two consecutive zero cutoffs make a component of generic length one invariant. -/
theorem stable_of_step {J : Input} {B : ResidueLift J} {D : Factors J B}
    (P : Ideal JetRing) [P.IsPrime] (hG : graphIdeal J B D ≤ P)
    (hsep : jetSeparant J.f ∉ P) (r : ℕ)
    (h₁ : oldNumerator J B r ∈ P) (h₂ : oldNumerator J B (r+1) ∈ P)
    (hsimple : ∀ x ∈ P, ∃ t ∉ P, t*x ∈ graphIdeal J B D ⊔ Ideal.span {oldNumerator J B r})
    (hstep : jetSeparant J.f * action J.f (oldNumerator J B r) -
      ((r+1 : ℕ) : JetRing) * oldNumerator J B (r+1) -
      ((2*r-1 : ℕ) : JetRing) * jetSeparant J.f * sepAlong J.f * oldNumerator J B r ∈
        graphIdeal J B D) : ∀ N ∈ P, action J.f N ∈ P := by
  have h : jetSeparant J.f * action J.f (oldNumerator J B r) ∈ P := by
    have he := P.add_mem (P.add_mem (hG hstep)
      (P.mul_mem_left (((2*r-1 : ℕ) : JetRing) * jetSeparant J.f * sepAlong J.f) h₁))
        (P.mul_mem_left (((r+1 : ℕ) : JetRing)) h₂)
    simpa only [sub_add_cancel] using he
  exact P0_9_6_3.stable_of_simple_cut _ _ hG (derivation J.f) (flow_mem_graph J B D)
    h₁ ((‹P.IsPrime›.mem_or_mem h).resolve_left hsep) hsimple

theorem simple_transfer {J : Input} {B : ResidueLift J} {D : Factors J B}
    (P : Ideal JetRing) [P.IsPrime] {u n d c : JetRing} (hd : d ∉ P)
    (h : d*c - n*u ∈ graphIdeal J B D)
    (hc : ∀ x ∈ P, ∃ t ∉ P, t*x ∈ graphIdeal J B D ⊔ Ideal.span {c}) :
    ∀ x ∈ P, ∃ t ∉ P, t*x ∈ graphIdeal J B D ⊔ Ideal.span {n} := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := hc x hx
  refine ⟨d*t, fun hm => (‹P.IsPrime›.mem_or_mem hm).elim hd ht, ?_⟩
  let G := graphIdeal J B D
  let I := G ⊔ Ideal.span {n}
  have hdc : d*c ∈ I := by
    have hn : n*u ∈ I := Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨u, rfl⟩)
    simpa only [sub_add_cancel] using I.add_mem (Ideal.mem_sup_left h) hn
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hb
  rw [mul_assoc, ← hab, mul_add]
  refine I.add_mem (Ideal.mem_sup_left (G.mul_mem_left _ ha)) ?_
  rw [hv, show d*(c*v) = v*(d*c) by ring]
  exact I.mul_mem_left _ hdc

abbrev CurveField (P : Ideal JetRing) := FractionRing (JetRing ⧸ P)
abbrev curveMap (P : Ideal JetRing) : JetRing →+* CurveField P :=
  (algebraMap (JetRing ⧸ P) (CurveField P)).comp (Ideal.Quotient.mk P)

private def scaledDerivation {E : Type} [Field E] (a : E) (d : E →+ E)
    (hd : ∀ x y, d (x*y) = x*d y + y*d x) : Derivation ℤ E E := by
  let d' : E →+ E := ⟨⟨fun x => a*d x, by rw [map_zero, mul_zero]⟩,
    fun x y => by
      change a * d (x+y) = a*d x+a*d y
      rw [map_add, mul_add]⟩
  refine Derivation.mk' d'.toIntLinearMap (fun x y => ?_)
  change a*d (x*y) = x*(a*d y)+y*(a*d x)
  rw [hd]
  ring

/-- The stable quotient carries the genuine, unscaled graph differentiation. -/
theorem differential_curve (f : Equation) (P : Ideal JetRing) [P.IsPrime]
    (hsep : jetSeparant f ∉ P) (hstable : ∀ q ∈ P, action f q ∈ P) :
    ∃ T : JetTaylor.Data (CurveField P), T.ι = seedMap (curveMap P) := by
  let A := JetRing ⧸ P
  let E := CurveField P
  let q := Ideal.Quotient.mk P
  let ε := HighCore82258GeometryCert_1.firstJet f q
  let G := Ideal.Quotient.lift P ε (fun a ha => TrivSqZeroExt.ext
    (Ideal.Quotient.eq_zero_iff_mem.mpr ha) (Ideal.Quotient.eq_zero_iff_mem.mpr (hstable a ha)))
  have hG (a : A) : (G a).fst = a := by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  let d := HighCore82258GeometryCert_1.derivationOfJet G hG 1
  let _ : Algebra.FormallyEtale A E := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  obtain ⟨D, hD⟩ := lift_derivation (A := A) (B := E) d
  let ev := curveMap P
  have hD' (a : JetRing) : D (ev a) = ev (action f a) := by
    rw [show ev a = algebraMap A E (q a) from rfl, hD]
    change algebraMap A E (1 * q (action f a)) = ev (action f a)
    rw [one_mul]
    rfl
  have hsn : ev (jetSeparant f) ≠ 0 := by
    intro hh
    exact hsep (Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective A E) (hh.trans (map_zero _).symm)))
  letI : Algebra ℤ E := Ring.toIntAlgebra E
  refine ⟨⟨seedMap ev, scaledDerivation (ev (jetSeparant f))⁻¹ D.toLinearMap.toAddMonoidHom
    (fun x y => by
      change D (x*y) = x*D y + y*D x
      exact D.leibniz x y), ?_⟩, rfl⟩
  intro s
  change (ev (jetSeparant f))⁻¹ * D (ev (C (C s))) = ev (C (C (coeffDx s)))
  rw [hD', HighCore82258Upper_3_1_1.flow_C, HighCore82258GeometryCert_1.coeffDiff_C,
    Polynomial.derivative_C, map_zero, mul_zero, add_zero, map_mul, inv_mul_cancel_left₀ hsn]

private def jetPoint {E : Type} [Field E] (T : JetTaylor.Data E) (y : E) : JetRing →+* E :=
  eval₂RingHom (eval₂RingHom T.ι y) (T.δ y)

private theorem jetPoint_C {E : Type} [Field E] (T : JetTaylor.Data E) (y : E) (q : Equation) :
    jetPoint T y (C q) = q.eval₂ T.ι y := eval₂_C _ _

private theorem point_flatten_eval {E : Type} [Field E] (ι : Seeds →+* E) (y : E) (q : Equation) :
    point ι y (flatten q) = q.eval₂ ι y := by
  change eval₂ ι y ((MvPolynomial.optionEquivLeft FX (Fin 2))
    ((MvPolynomial.optionEquivLeft FX (Fin 2)).symm q)) = _
  rw [AlgEquiv.apply_symm_apply]

private theorem jetPoint_chain {E : Type} [Field E] (T : JetTaylor.Data E) (y : E)
    (f : Equation) (hf : jetPoint T y (C f) = 0) :
    jetPoint T y (tangentEquation f) = 0 ∧
    (∀ p, jetPoint T y (jetSeparant f) * T.δ (jetPoint T y p) = jetPoint T y (action f p)) ∧
    T.δ (jetPoint T y (jetSeparant f)) = jetPoint T y (sepAlong f) := by
  let ev := jetPoint T y
  have hC (q : Equation) : T.δ (ev (C q)) =
      ev (C (coefficientDerivative q)) + ev velocity * ev (C q.derivative) := by
    have hh := HighCore82258GeometryCert_1.root_chain T.δ (eval₂RingHom T.ι y)
      (fun s => by simpa only [coe_eval₂RingHom, eval₂_C] using T.compatible s) q
    simpa only [jetPoint_C, show ev velocity = T.δ y from eval₂_X _ _,
      coe_eval₂RingHom, eval₂_X, ev] using hh
  have ht : ev (tangentEquation f) = 0 := by
    change ev (C (coefficientDerivative f) + velocity * C f.derivative) = 0
    rw [map_add, map_mul, ← hC, hf, map_zero]
  have hs : T.δ (ev (jetSeparant f)) = ev (sepAlong f) := by
    rw [sepAlong, map_add, map_mul]
    exact hC f.derivative
  have hx : ev (jetSeparant f) * T.δ (ev velocity) = -ev (secondAlongVelocity f) := by
    have he : ev (C (coefficientDerivative f)) + ev velocity * ev (C f.derivative) = 0 := by
      rw [← hC, hf, map_zero]
    have h := congrArg T.δ he
    simp only [map_add, map_zero, HighCore82258GeometryCert_1.deriv_mul, hC,
      HighCore82258Upper_3_1_1.coeffDiff_derivative] at h
    simp only [secondAlongVelocity, map_add, map_mul, map_pow, map_ofNat]
    rw [HighCore82258Upper_3_1_1.coeffDiff_derivative]
    linear_combination h
  exact ⟨ht, HighCore82258GeometryCert_1.jet_chain T.δ ev f hC hx, hs⟩

private theorem root_data (J : Input) (B : ResidueLift J) (D : Factors J B) :
    (generic D.proper).Separable ∧ D.proper.IsPrimitive := by
  have hd : D.proper ∣ J.f := ⟨_, D.product⟩
  exact ⟨J.reduced.2.2.of_dvd (Polynomial.map_dvd _ hd), isPrimitive_of_dvd J.reduced.2.1 hd⟩

private theorem graph_mem_of_roots (J : Input) (B : ResidueLift J) (D : Factors J B)
    (T : JetTaylor.Data (SplitField D.proper)) (hι : T.ι = HighCore82258Upper_4.splitMap D.proper)
    (N : JetRing) (hroot : ∀ y ∈ geomRoots D.proper, jetPoint T y (C J.f) = 0)
    (hN : ∀ y ∈ geomRoots D.proper, jetPoint T y N = 0) : N ∈ graphIdeal J B D := by
  classical
  let a := J.f.derivative
  let b := coefficientDerivative J.f
  let q := (N.scaleRoots a).eval (-b)
  let I : Ideal JetRing := Ideal.span {C D.proper, tangentEquation J.f}
  have hzero (y : SplitField D.proper) (hy : y ∈ geomRoots D.proper) : (generic q).aeval y = 0 := by
    let ev := jetPoint T y
    have ht : ev (C b + Polynomial.X*C a) = 0 := (jetPoint_chain T y J.f (hroot y hy)).1
    have h := HighCore82258Upper_3_2_1.clear_velocity ev a b N ht
    rw [map_mul, hN y hy, mul_zero] at h
    change (0 : SplitField D.proper) = jetPoint T y (C q) at h
    rw [jetPoint_C, hι] at h
    rw [generic, aeval_def, eval₂_map]
    exact h.symm
  obtain ⟨hsep, hprim⟩ := root_data J B D
  let i := algebraMap SeedField (SplitField D.proper)
  have hdiv : generic D.proper ∣ generic q := by
    apply (Polynomial.map_dvd_map' i).mp
    by_cases hz : (generic q).map i = 0
    · rw [hz]; exact dvd_zero _
    have hsep' : ((generic D.proper).map i).Separable := hsep.map
    apply (IsSplittingField.splits (SplitField D.proper) (generic D.proper)).dvd_of_roots_le_roots hsep'.ne_zero
    apply (Multiset.le_iff_subset (nodup_roots hsep')).mpr
    intro y hy
    apply (Polynomial.mem_roots hz).mpr
    have hy' : y ∈ geomRoots D.proper := Multiset.mem_toFinset.mpr hy
    simpa only [Polynomial.IsRoot, aeval_def, eval_map] using hzero y hy'
  have hq : D.proper ∣ q := (hprim.dvd_iff_fraction_map_dvd_fraction_map SeedField).mpr hdiv
  have hCr : C q ∈ I := by
    obtain ⟨z, hz⟩ := hq
    rw [hz, map_mul, mul_comm]
    exact I.mul_mem_left _ (Ideal.subset_span (by simp))
  have ht : Ideal.Quotient.mk I (C b + Polynomial.X*C a) = 0 := by
    change Ideal.Quotient.mk I (tangentEquation J.f) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hx := Ideal.Quotient.eq_zero_iff_mem.mp
    ((HighCore82258Upper_3_2_1.clear_velocity (Ideal.Quotient.mk I) a b N ht).trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr hCr))
  refine ⟨N.natDegree, ?_⟩
  rw [openFactor, mul_pow, mul_assoc]
  exact I.mul_mem_left _ hx

/-- The consecutive Taylor relation holds in the whole graph ideal, including
    specializations onto seed curves where no derivation has yet descended. -/
theorem graph_derivative_step (J : Input) (B : ResidueLift J) (D : Factors J B) {r : ℕ}
    (hr : 0 < r) (hp : r+1 < P1.p) :
    jetSeparant J.f * action J.f (oldNumerator J B r) -
      ((r+1 : ℕ) : JetRing) * oldNumerator J B (r+1) -
      ((2*r-1 : ℕ) : JetRing) * jetSeparant J.f * sepAlong J.f * oldNumerator J B r ∈
        graphIdeal J B D := by
  classical
  obtain ⟨d⟩ := HighCore82258Upper_4_1.proof D.proper (root_data J B D).1
  let ι := HighCore82258Upper_4.splitMap D.proper
  let T : JetTaylor.Data (SplitField D.proper) :=
    ⟨ι, d.split, fun s => by
      change d.split (algebraMap SeedField (SplitField D.proper) (algebraMap Seeds SeedField s)) = _
      rw [d.extends_base, d.extends_seed]
      rfl⟩
  have hf (y : SplitField D.proper) (hy : y ∈ geomRoots D.proper) : jetPoint T y (C J.f) = 0 := by
    have hz : (generic D.proper).aeval y = 0 := by
      apply aeval_eq_zero_of_mem_rootSet
      rwa [rootSet_def]
    rw [jetPoint_C]
    change J.f.eval₂ ι y = 0
    rw [← point_flatten_eval]
    rw [HighCore82258Upper_4_2.point_flatten, D.product, generic, Polynomial.map_mul, map_mul]
    exact mul_eq_zero.mpr (Or.inl hz)
  apply graph_mem_of_roots J B D T rfl _ hf
  intro y hy
  let ev := jetPoint T y
  have hchain := (jetPoint_chain T y J.f (hf y hy)).2
  have ha : T.ι (liftSeeds B.denominator) ≠ 0 := by
    have hψ : Function.Injective constantAbscissa :=
      (IsFractionRing.injective K1_14.L[X] FX).comp Polynomial.C_injective
    have hι : Function.Injective T.ι :=
      (algebraMap SeedField (SplitField D.proper)).injective.comp (IsFractionRing.injective _ _)
    have hmap : Function.Injective (T.ι.comp liftSeeds) := hι.comp (MvPolynomial.map_injective _ hψ)
    exact (map_ne_zero_iff _ hmap).mpr B.denominator_ne
  have hfac (i : ℕ) (hi : i ≤ r+1) : (i.factorial : SplitField D.proper) ≠ 0 := by
    have h := HighCore82258Upper_2.factorial_ne_zero (hi.trans_lt hp)
    simpa only [map_natCast, map_zero] using (T.embed.injective.ne h)
  have hn (n : ℕ) : ev (oldNumerator J B n) = point T.ι y (quotientNumerator J B n) := by
    exact jetPoint_C T y _
  have hs : ev (jetSeparant J.f) = point T.ι y (separant (flatten J.f)) := by
    rw [separant, flatten]
    change _ = (MvPolynomial.optionEquivLeft FX (Fin 2)
      (MvPolynomial.pderiv none ((MvPolynomial.optionEquivLeft FX (Fin 2)).symm J.f))).eval₂ T.ι y
    rw [MvPolynomial.optionEquivLeft_pderiv_none, AlgEquiv.apply_symm_apply]
    exact jetPoint_C T y _
  have hJ : point T.ι y (flatten J.f) = 0 := by
    rw [point_flatten_eval]
    exact (jetPoint_C T y J.f).symm.trans (hf y hy)
  have step := JetTaylor.derivative_step T J B y r hr hJ ha hfac
  simp only at step
  rw [← hn, ← hn, ← hs, hchain.2] at step
  simp only [map_sub, map_mul, map_natCast, ← hchain.1, ev]
  change ev (jetSeparant J.f) * (ev (jetSeparant J.f) * T.δ (ev (oldNumerator J B r))) - _ - _ = 0
  linear_combination step

end
end SplitCut.StableFlow

#print axioms SplitCut.StableFlow.flow_mem_graph
#print axioms SplitCut.StableFlow.stable_of_step
#print axioms SplitCut.StableFlow.differential_curve
#print axioms SplitCut.StableFlow.graph_derivative_step
