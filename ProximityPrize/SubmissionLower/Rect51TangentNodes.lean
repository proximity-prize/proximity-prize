import ProximityPrize.SubmissionLower.Rect51TangentTaylor

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000

namespace Rect51Tangent
noncomputable section
open P1 (K I)
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3 (JetRing CurveMarks graphIdeal jetDenominator openFactor
  residueInJet oldDenominator oldNumerator markPoint)
open HighCore82706Tangent_3_3 (wordAt residueAtNode residueCut prefixIndex prefixLength
  sectionIndex curveValue canonicalJet residueValue FixedWeights)
open K1_14 (FX seedEmbedding)
open scoped BigOperators
open private oldDenominator_eq denominator_nonzero residue_degree
  from ProximityPrize.SubmissionLower.HighCore82706TangentDeps
open private pure_denominator from ProximityPrize.SubmissionLower.Rect51TangentTaylor

structure NodeSections {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C : CurveMarks J B D) (v : Axes) where
  persistent : Finset I
  hits : ∀ γ ∈ C.marks, ∀ x ∈ persistent,
    (J.family.scalar γ).eval (P1.node x) = J.model.word x
  cuts : ∀ x ∉ persistent,
    let r := J.ell - persistent.card
    ∃ S : Section C.prime (baseDegree J r) r (taylorAxis J v r),
      S.affine ∉ C.prime ∧
      ∀ γ ∈ C.marks, (J.family.scalar γ).eval (P1.node x) = J.model.word x →
        markPoint J γ S.affine = 0

private theorem residue_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) (r : ℕ) (x : I) :
    Represented (graphIdeal J B D) (baseDegree J r) r (taylorAxis J v r) (residueCut J B r x) := by
  have hR := seed_section (Q := graphIdeal J B D) (residue_degree B x)
  have hD := pure_denominator J B D hf r
  change Represented (graphIdeal J B D) (baseDegree J r) r (taylorAxis J v r)
    (Polynomial.C (Polynomial.C (HighCore82706Tangent.liftSeeds (residueAtNode B x))) *
      HighCore82706Tangent_3_1.pureDen J r)
  simpa only [Nat.zero_add, taylorAxis, add_comm (fun _ : Fin 2 => 2*J.w) (r • v)] using hR.mul hD

private theorem normalize_residue {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) {J : Input} {B : ResidueLift J} {D : Factors J B} {r : ℕ} {v : Axes}
    (T : TaylorSections J B D v r) (hu : φ (openFactor J B) ≠ 0) (x : I) :
    φ (residueCut J B r x) / φ T.denominator.affine = residueValue φ B x := by
  have hden := denominator_nonzero φ J B hu
  rw [T.den_eq, jetDenominator, residueValue]
  apply (div_eq_div_iff (hden _) (by simpa only [pow_zero, mul_one] using hden 0)).2
  simp only [residueCut, map_mul, map_pow]
  ring
private theorem normalize_jet {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) {J : Input} {B : ResidueLift J} {D : Factors J B} {v : Axes}
    (sites : Finset I) (T : TaylorSections J B D v (J.ell - sites.card))
    (hu : φ (openFactor J B) ≠ 0) (hz : ∀ q ∈ graphIdeal J B D, φ q = 0)
    (j : Fin (prefixLength J sites)) :
    φ (T.numerator (sectionIndex J sites j)).affine / φ T.denominator.affine =
      canonicalJet φ J B (prefixIndex J sites j) := by
  have hden := denominator_nonzero φ J B hu
  unfold canonicalJet
  have h₁ : φ T.denominator.affine ≠ 0 := by rw [T.den_eq, jetDenominator]; exact hden _
  have h₂ : φ (oldDenominator J B (prefixIndex J sites j).val) ≠ 0 := by
    rw [oldDenominator_eq]; exact hden _
  apply (div_eq_div_iff h₁ h₂).2
  have h := hz _ (T.agrees (sectionIndex J sites j))
  rw [map_sub, map_mul, map_mul, sub_eq_zero, mul_comm (φ (oldDenominator J B _))] at h
  exact h
private def cut {J : Input} {B : ResidueLift J} {D : Factors J B} {v : Axes} (sites : Finset I)
    (T : TaylorSections J B D v (J.ell - sites.card)) (x : I)
    (b : I → FX) (a : Fin (prefixLength J sites) → FX) : JetRing :=
  let r := J.ell - sites.card
  let d := T.denominator.affine
  (residueCut J B r x - wordAt J x • d) +
    (∑ i ∈ sites, b i • (wordAt J i • d - residueCut J B r i)) +
    ∑ j, a j • (T.numerator (sectionIndex J sites j)).affine
private theorem normalize_cut {E : Type} [Field E] [Algebra FX E]
    (φ : JetRing →ₐ[FX] E) {J : Input} {B : ResidueLift J} {D : Factors J B} {v : Axes}
    (sites : Finset I) (T : TaylorSections J B D v (J.ell - sites.card))
    (hu : φ (openFactor J B) ≠ 0) (hz : ∀ q ∈ graphIdeal J B D, φ q = 0)
    (x : I) (b : I → FX) (a : Fin (prefixLength J sites) → FX) :
    φ (cut sites T x b a) / φ T.denominator.affine =
      (residueValue φ B x - algebraMap FX E (wordAt J x)) +
      (∑ i ∈ sites, algebraMap FX E (b i) * (algebraMap FX E (wordAt J i) - residueValue φ B i)) +
      ∑ j, algebraMap FX E (a j) * canonicalJet φ J B (prefixIndex J sites j) := by
  classical
  have hden : φ T.denominator.affine ≠ 0 := by
    rw [T.den_eq, jetDenominator]
    exact denominator_nonzero φ J B hu _
  have heval (a : FX) (q : JetRing) : φ (a • q) = algebraMap FX E a * φ q := by
    rw [Algebra.smul_def, map_mul, AlgHom.commutes]
  simp only [cut, map_add, map_sub, map_sum, heval, add_div, sub_div, Finset.sum_div,
    mul_div_assoc, div_self hden, mul_one, normalize_residue φ T hu,
    normalize_jet φ sites T hu hz]
set_option maxHeartbeats 500000 in
theorem node_sections (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) (C : CurveMarks J B D) : Nonempty (NodeSections C v) := by
  classical
  let specialize := HighCore82706Tangent_3_3_1.proof
  let weights := HighCore82706Tangent_3_3_2.proof
  let tuple (r : ℕ) (h : r ≤ J.ell+1) := Classical.choice (taylor_sections J B D hf r h)
  let _ : C.prime.IsPrime := C.isPrime
  let R := JetRing ⧸ C.prime
  let E := FractionRing R
  let q : JetRing →+* E := (algebraMap R E).comp (Ideal.Quotient.mk C.prime)
  let curveAlgebra : Algebra FX E := (q.comp (algebraMap FX JetRing)).toAlgebra
  let _ : Algebra FX E := curveAlgebra
  let φ : JetRing →ₐ[FX] E := ⟨q, fun _ => rfl⟩
  have hvanish (f : JetRing) : φ f = 0 ↔ f ∈ C.prime := by
    change algebraMap R E (Ideal.Quotient.mk C.prime f) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective R E), Ideal.Quotient.eq_zero_iff_mem]
  have hφopen : φ (openFactor J B) ≠ 0 := fun h => C.regular ((hvanish _).mp h)
  have hφgraph : ∀ f ∈ graphIdeal J B D, φ f = 0 :=
    fun f hf => (hvanish f).mpr (C.onGraph hf)
  let sites := Finset.univ.filter fun i : I => curveValue φ J B i = algebraMap FX E (wordAt J i)
  have hsites (i : I) :
      i ∈ sites ↔ curveValue φ J B i = algebraMap FX E (wordAt J i) := by
    simp [sites]
  let r := J.ell - sites.card
  have hr : r ≤ J.ell := Nat.sub_le _ _
  let T := tuple r (hr.trans (Nat.le_succ _))
  let V := Represented (graphIdeal J B D) (baseDegree J r) r (taylorAxis J v r)
  have hres (i : I) : V (residueCut J B r i) := residue_section J B D hf r i
  have hden : V T.denominator.affine := ⟨T.denominator,rfl⟩
  have hmarkzero (γ : K) (hγ : γ ∈ C.marks) (f : JetRing)
      (hf : f ∈ graphIdeal J B D) : markPoint J γ f = 0 :=
    C.liesOn γ hγ (C.onGraph hf)
  have eval_cut {E' : Type} [Field E'] [Algebra FX E']
      (ψ : JetRing →ₐ[FX] E') (S : Finset I) (U : TaylorSections J B D v (J.ell - S.card))
      (ho : ψ (openFactor J B) ≠ 0) (hg : ∀ f ∈ graphIdeal J B D, ψ f = 0)
      (x : I) (b : I → FX) (a : Fin (prefixLength J S) → FX)
      (hw : FixedWeights J S x b a)
      (hs : ∀ i ∈ S, curveValue ψ J B i = algebraMap FX E' (wordAt J i)) :
      ψ (cut S U x b a) / ψ U.denominator.affine =
        curveValue ψ J B x - algebraMap FX E' (wordAt J x) :=
    (normalize_cut ψ S U ho hg x b a).trans
      (hw E' (residueValue ψ B) (canonicalJet ψ J B) hs).symm
  have hresolved (γ : K) (hγ : γ ∈ C.marks) (i : I) (hi : i ∈ sites) :
      curveValue (markPoint J γ) J B i = wordAt J i := by
    let empty : Finset I := ∅
    let U := tuple (J.ell - empty.card) ((Nat.sub_le _ _).trans (Nat.le_succ _))
    obtain ⟨b, a, hw⟩ := weights J empty i
    have hn : φ U.denominator.affine ≠ 0 := by
      rw [U.den_eq, jetDenominator]
      exact denominator_nonzero φ J B hφopen _
    have hg := eval_cut φ empty U hφopen hφgraph i b a hw (by simp [empty])
    rw [(hsites i).mp hi, sub_self] at hg
    have hmem := (hvanish _).mp ((div_eq_zero_iff.mp hg).resolve_right hn)
    have hpt : markPoint J γ (cut empty U i b a) = 0 := C.liesOn γ hγ hmem
    have hm := eval_cut (markPoint J γ) empty U
      (specialize J B γ (C.sub hγ)).1 (hmarkzero γ hγ) i b a hw (by simp [empty])
    rw [hpt, zero_div, eq_comm, sub_eq_zero] at hm
    simpa using hm
  refine ⟨⟨sites, ?_, ?_⟩⟩
  · intro γ hγ x hx
    have he := hresolved γ hγ x hx
    rw [(specialize J B γ (C.sub hγ)).2 x] at he
    exact seedEmbedding.injective he
  · intro x hx
    obtain ⟨b, a, hw⟩ := weights J sites x
    have hc : V (cut sites T x b a) := by
      change Represented _ _ _ _ (cut sites T x b a)
      unfold cut
      simp_rw [Algebra.smul_def]
      apply Represented.add
      · apply Represented.add
        · exact (hres x).sub (Represented.smul _ hden)
        · apply Represented.sum
          intro i _
          exact Represented.smul _ ((Represented.smul _ hden).sub (hres i))
      · apply Represented.sum
        intro j _
        exact Represented.smul _ ⟨T.numerator (sectionIndex J sites j),rfl⟩
    obtain ⟨S, hS⟩ := hc
    refine ⟨S.restrict C.onGraph, ?_, ?_⟩
    · change S.affine ∉ C.prime
      rw [hS]
      intro h
      have he := eval_cut φ sites T hφopen hφgraph x b a hw (fun i => (hsites i).mp)
      rw [(hvanish _).mpr h, zero_div, eq_comm, sub_eq_zero] at he
      exact hx ((hsites x).mpr he)
    · intro γ hγ hhit
      change markPoint J γ S.affine = 0
      rw [hS]
      have hs : ∀ i ∈ sites,
          curveValue (markPoint J γ) J B i = algebraMap FX FX (wordAt J i) :=
        fun i hi => by simpa using hresolved γ hγ i hi
      have he := eval_cut (markPoint J γ) sites T (specialize J B γ (C.sub hγ)).1
        (hmarkzero γ hγ) x b a hw hs
      have hv := (specialize J B γ (C.sub hγ)).2 x
      rw [hhit] at hv
      rw [hv, Algebra.algebraMap_self, RingHom.id_apply, wordAt, sub_self] at he
      exact (div_eq_zero_iff.mp he).resolve_right (by
        rw [T.den_eq, jetDenominator]
        exact denominator_nonzero _ J B (specialize J B γ (C.sub hγ)).1 _)

#print axioms node_sections
end
end Rect51Tangent
