import ProximityPrize.SubmissionLower.Koala6831MovingExceptionsNormalForm

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open Koala6831Comparison (SymbolicRow primitiveSelected)
open Koala6831Separation (NormalForm Seeds pairDegree)
open scoped Classical

noncomputable section
variable {K I : Type*} [Field K]

def rightFlowData {q : SymbolicRow (Seeds K)} {w delta : ℕ} (N : NormalForm q w delta) :
    FlowData K := ⟨N.d₁, N.B 0, N.B 1, -N.D 0, -N.D 1⟩

private theorem minor_degree_le (a c : Fin 2 → Polynomial K) :
    (a 1 * c 0 - a 0 * c 1).natDegree ≤ pairDegree a + pairDegree c := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add (le_max_right _ _) (le_max_left _ _)))
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add (le_max_left _ _) (le_max_right _ _)))

theorem leftFlowData_degree_bounds {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (h : pairDegree N.A ≤ pairDegree N.B) :
    let B := leftFlowData N
    B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ delta ∧
      (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ w + delta := by
  change N.d₀.natDegree + pairDegree N.A ≤ delta ∧
    (N.A 1 * N.C 0 - N.A 0 * N.C 1).natDegree ≤ w + delta
  exact ⟨(Nat.add_le_add_left h _).trans N.first_degree,
    (minor_degree_le N.A N.C).trans ((Nat.add_le_add_right h _).trans N.left_degree)⟩

theorem rightFlowData_degree_bounds {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (h : pairDegree N.B ≤ pairDegree N.A) :
    let B := rightFlowData N
    B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ delta ∧
      (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ w + delta := by
  change N.d₁.natDegree + pairDegree N.B ≤ delta ∧
    (N.B 1 * -N.D 0 - N.B 0 * -N.D 1).natDegree ≤ w + delta
  refine ⟨(Nat.add_le_add_left h _).trans N.second_degree, ?_⟩
  have hdeg := minor_degree_le N.B (fun i => -N.D i)
  simp only [pairDegree, Polynomial.natDegree_neg] at hdeg
  exact hdeg.trans ((Nat.add_le_add_right h _).trans N.right_degree)

private theorem right_seedOffset {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (g : K) :
    (rightFlowData N).seedOffset g = -affineDenominator (N.D 0) (N.D 1) g := by
  unfold FlowData.seedOffset rightFlowData affineDenominator
  ring

private theorem right_seedDenominator {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (g : K) :
    (rightFlowData N).seedDenominator g = affineDenominator (N.B 0) (N.B 1) g := rfl

private theorem right_scale {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) : (rightFlowData N).d0 = N.d₁ := rfl

private theorem exists_right_pole_cleanup (nodes : Finset I) (x : I → K)
    (b₀ b₁ : Polynomial K) (hB : IsCoprime b₀ b₁)
    (σ : K ≃+* K) (seeds : Finset K) :
    ∃ good ⊆ seeds, seeds.card ≤ good.card + (nodes.card + 1) ∧
      ∀ g ∈ good, affineDenominator b₀ b₁ (σ g) ≠ 0 ∧
        ∀ i ∈ nodes, (affineDenominator b₀ b₁ (σ g)).eval (x i) ≠ 0 := by
  classical
  let valid (g : K) := affineDenominator b₀ b₁ (σ g) ≠ 0 ∧
    ∀ i ∈ nodes, (affineDenominator b₀ b₁ (σ g)).eval (x i) ≠ 0
  let good := seeds.filter valid
  let bad := seeds.filter (fun g => ¬ valid g)
  let zeroSeeds := seeds.filter fun g => affineDenominator b₀ b₁ (σ g) = 0
  let poleSeeds := seeds.filter fun g => ∃ i ∈ nodes, (affineDenominator b₀ b₁ (σ g)).eval (x i) = 0
  have hz : zeroSeeds.card ≤ 1 := by
    rw [← Finset.card_image_of_injective zeroSeeds σ.injective]
    apply zero_affine_denominator_seeds_card_le b₀ b₁ hB
    rintro _ h
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hg).2
  have hp : poleSeeds.card ≤ nodes.card := by
    rw [← Finset.card_image_of_injective poleSeeds σ.injective]
    apply node_pole_seeds_card_le nodes x b₀ b₁ hB
    rintro _ h
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hg).2
  have hsub : bad ⊆ zeroSeeds ∪ poleSeeds := by
    intro g hg
    obtain ⟨hseed, hbad⟩ := Finset.mem_filter.mp hg
    by_cases hzero : affineDenominator b₀ b₁ (σ g) = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hseed, hzero⟩)
    have hf : ¬ ∀ i ∈ nodes, (affineDenominator b₀ b₁ (σ g)).eval (x i) ≠ 0 :=
      fun h => hbad ⟨hzero, h⟩
    push Not at hf
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hseed, hf⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le zeroSeeds poleSeeds)
  have hsplit : good.card + bad.card = seeds.card := Finset.card_filter_add_card_filter_not _
  exact ⟨good, Finset.filter_subset _ _, by omega, fun _ hg => (Finset.mem_filter.mp hg).2⟩

theorem normalForm_exists_retained_right_words {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (σ : K ≃+* K) (p : ℕ) (hσ : ∀ g, σ g = g ^ p)
    (hdelta : delta < p) (nodes : Finset I) (x : I → K) (u₀ u₁ : I → K)
    (hnode : ∀ i ∈ nodes, σ (x i) = x i)
    (hgood : ∀ i ∈ nodes,
      q.atNode (MvPolynomial.C (x i)) (Koala6831SeparationFactors.affine 0 (u₀ i) (u₁ i))
        (Koala6831SeparationFactors.affine 1 (σ (u₀ i)) (σ (u₁ i))) = 0)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hselected : ∀ g ∈ seeds, primitiveSelected σ.toRingHom p q selected g = 0) :
    ∃ retained ⊆ seeds,
      seeds.card ≤ retained.card + (2 * nodes.card + 2 + (p + 1) * delta) ∧
      ∃ fixed : I → K, ∃ normalized : K → Polynomial K,
        (∀ i ∈ nodes, N.d₁.eval (x i) * σ (u₀ i) - (N.D 0).eval (x i) = (N.B 0).eval (x i) * fixed i ∧
          N.d₁.eval (x i) * σ (u₁ i) - (N.D 1).eval (x i) = (N.B 1).eval (x i) * fixed i) ∧
        ∀ g ∈ retained, (normalized g).natDegree ≤ w + delta ∧
          N.d₁ * (selected g).map σ.toRingHom - affineDenominator (N.D 0) (N.D 1) (σ g) =
            affineDenominator (N.B 0) (N.B 1) (σ g) * normalized g ∧
          ∀ i ∈ nodes, (selected g).eval (x i) = u₀ i + g * u₁ i →
            (normalized g).eval (x i) = fixed i := by
  classical
  obtain ⟨remainder, hsub, hcard, hden⟩ := exists_retained_affine_seeds nodes x
    (N.A 0) (N.A 1) (N.B 0) (N.B 1) p delta N.A_coprime N.B_coprime
    (by simpa only [pairDegree] using (Nat.le_of_add_left_le N.second_degree))
    (by simpa only [pairDegree] using (Nat.le_of_add_left_le N.first_degree)) hdelta seeds
  obtain ⟨retained, hkeep, hcard', hpoles⟩ := exists_right_pole_cleanup nodes x (N.B 0) (N.B 1)
    N.B_coprime σ remainder
  have hsubset := hkeep.trans hsub
  let B := rightFlowData N
  have hex (g : ↥retained) : ∃ poly : Polynomial K, poly.natDegree ≤ w + delta ∧
      N.d₁ * (selected g.1).map σ.toRingHom - affineDenominator (N.D 0) (N.D 1) (σ g.1) =
        affineDenominator (N.B 0) (N.B 1) (σ g.1) * poly := by
    have hd₀ := (le_max_left (N.D 0).natDegree (N.D 1).natDegree).trans
      (Nat.le_of_add_left_le N.right_degree)
    have hd₁ := (le_max_right (N.D 0).natDegree (N.D 1).natDegree).trans
      (Nat.le_of_add_left_le N.right_degree)
    have hcop : IsRelPrime (B.seedDenominator (σ g.1)) (affineDenominator (N.A 0) (N.A 1) g.1) := by
      simpa only [B, right_seedDenominator, hσ] using
        (hden g.1 (hkeep g.2)).2.1.symm
    have hcompat := normalForm_specialized_compatibility N σ.toRingHom p selected g.1
      (hselected g.1 (hsubset g.2))
    rw [← hσ g.1] at hcompat
    obtain ⟨Q, hQ, hQeq⟩ := B.exists_normalized_selected_word (σ g.1) ((selected g.1).map σ.toRingHom)
      (affineDenominator (N.A 0) (N.A 1) g.1)
      (N.d₀ * selected g.1 + affineDenominator (N.C 0) (N.C 1) g.1) w delta
      (Polynomial.natDegree_map_le.trans (hdegree g.1 (hsubset g.2)))
      (Nat.le_of_add_right_le N.second_degree) (by simpa [B, rightFlowData] using hd₀)
      (by simpa [B, rightFlowData] using hd₁) hcop
      (by simpa only [B, right_seedDenominator, right_scale, right_seedOffset, sub_eq_add_neg]
        using hcompat.symm)
    exact ⟨Q, hQ, by
      simpa only [B, right_seedDenominator, right_scale, right_seedOffset, sub_eq_add_neg] using hQeq⟩
  choose chosen hnormDegree hnormIdentity using hex
  let normalized (g : K) : Polynomial K := if hg : g ∈ retained then chosen ⟨g, hg⟩ else 0
  have hin (i : ↥nodes) : ∃ u : K,
      N.d₁.eval (x i.1) * σ (u₀ i.1) - (N.D 0).eval (x i.1) = (N.B 0).eval (x i.1) * u ∧
      N.d₁.eval (x i.1) * σ (u₁ i.1) - (N.D 1).eval (x i.1) = (N.B 1).eval (x i.1) * u := by
    let received : Fin 2 → K := ![u₀ i.1, u₁ i.1]
    obtain ⟨u, _, hr⟩ := N.fixedWord (x i.1) received (σ ∘ received) (hgood i.1 i.2)
    exact ⟨u, by simpa [received, mul_comm] using hr 0, by simpa [received, mul_comm] using hr 1⟩
  choose chosenValue hvalues using hin
  let fixed (i : I) : K := if hi : i ∈ nodes then chosenValue ⟨i, hi⟩ else 0
  refine ⟨retained, hsubset, by omega, fixed, normalized, ?_, ?_⟩
  · intro i hi
    simpa only [fixed, dite_eq_left hi] using hvalues ⟨i, hi⟩
  · intro g hg
    have hnorm := hnormIdentity ⟨g, hg⟩
    have hnorm' : N.d₁ * (selected g).map σ.toRingHom - affineDenominator (N.D 0) (N.D 1) (σ g) =
        affineDenominator (N.B 0) (N.B 1) (σ g) * normalized g := by
      simpa only [normalized, dite_eq_left hg] using hnorm
    refine ⟨by simpa only [normalized, dite_eq_left hg] using hnormDegree ⟨g, hg⟩, hnorm', ?_⟩
    intro i hi hagree
    have hare : ((selected g).map σ.toRingHom).eval (x i) = σ (u₀ i) + σ g * σ (u₁ i) := by
      rw [← hnode i hi]
      change ((selected g).map σ.toRingHom).eval (σ.toRingHom (x i)) = _
      rw [Polynomial.eval_map_apply, hagree, map_add, map_mul]
      rfl
    have hvalue := hvalues ⟨i, hi⟩
    exact B.normalized_agrees_at _ _ (x i) (σ g) (σ (u₀ i)) (σ (u₁ i)) (fixed i)
      hare (by simpa only [B, rightFlowData, Polynomial.eval_neg, fixed, dite_eq_left hi, sub_eq_add_neg]
        using hvalue.1)
      (by simpa only [B, rightFlowData, Polynomial.eval_neg, fixed, dite_eq_left hi, sub_eq_add_neg]
        using hvalue.2) ((hpoles g hg).2 i hi)
      (by simpa only [B, right_seedDenominator, right_scale, right_seedOffset, sub_eq_add_neg]
        using hnorm')

theorem noLargeSelectedPencil_conjugate {L : Type} [Field L] (σ : L ≃+* L)
    (selected : L → Polynomial L) (seeds : Finset L) (w e : ℕ)
    (hpencil : RCN238.NoLargeSelectedPencil selected seeds w e) :
    RCN238.NoLargeSelectedPencil (fun g => (selected (σ.symm g)).map σ.toRingHom)
      (seeds.image (fun g => σ g)) w e := by
  classical
  intro P₀ P₁ h₀ h₁
  have hcomp : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id L :=
    RingHom.ext (fun x => σ.symm_apply_apply x)
  let fiber := seeds.filter fun g => selected g =
    P₀.map σ.symm.toRingHom + Polynomial.C g * P₁.map σ.symm.toRingHom
  have hcount : fiber.card ≤ e + 1 :=
    hpencil (P₀.map σ.symm.toRingHom) (P₁.map σ.symm.toRingHom)
      (Polynomial.natDegree_map_le.trans h₀) (Polynomial.natDegree_map_le.trans h₁)
  apply le_trans _ hcount
  apply Finset.card_le_card_of_injOn (fun z => σ.symm z) _ (fun _ _ _ _ h => σ.symm.injective h)
  intro g hg
  have hmem := (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).1
  have hpoly : (selected (σ.symm g)).map σ.toRingHom = P₀ + Polynomial.C g * P₁ :=
    (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2
  obtain ⟨a, ha, hga⟩ := Finset.mem_image.mp hmem
  have hback : σ.symm g = a := by rw [← hga, σ.symm_apply_apply]
  apply Finset.mem_coe.mpr
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · change σ.symm g ∈ seeds
    rw [hback]
    exact ha
  have h := congrArg (Polynomial.map σ.symm.toRingHom) hpoly
  have hσg : σ.symm.toRingHom g = σ.symm g := rfl
  simpa only [Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, hσg] using h

end

end ProximityPrize.SubmissionLower.Koala6831Moving
