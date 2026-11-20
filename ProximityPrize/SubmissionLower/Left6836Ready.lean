/- Apache-2.0. Bome2017, price one live seed per normalized polynomial using the full hard-case hypotheses. -/
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the independent full-domain primary proof of Bome2017 after Lucieno (PR 618) and BitWonka. Exact 68.33 constants and physical hypotheses are new. -/
import ProximityPrize.SubmissionLower.Aligned
import ProximityPrize.SubmissionLower.Koala6831BenchmarkRetention
import ProximityPrize.SubmissionLower.Koala6831MovingExceptionsOrientation
import ProximityPrize.SubmissionLower.Koala6831MovingPrimaryRoute
import ProximityPrize.SubmissionLower.Mid6833GenuineResidual

namespace ProximityPrize.SubmissionLower.Left6836Ready

open scoped Classical
open Koala6831BenchmarkField (prime)
open Koala6831BenchmarkPrimitive Koala6831BenchmarkRetention
open Koala6831Comparison Koala6831Moving
open Koala6831Separation (NormalForm pairDegree)

noncomputable section

variable {K I : Type} [Field K] [Fintype I]

def normalizationBudget : ℕ := 20484612180767

structure Ready (x : I ↪ K) (original : Finset K) where
  flow : FlowData K
  u₀ : I → K
  u₁ : I → K
  word : I → K
  good : Finset I
  seeds : Finset K
  selected : K → Polynomial K
  normalized : K → Polynomial K
  nodes_card : Fintype.card I = 262144
  count : original.card ≤ seeds.card + normalizationBudget
  degree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071
  agreement : ∀ g ∈ seeds, 181039 ≤
    (Finset.univ.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card
  agree_good : ∀ g ∈ seeds, ∀ i,
    (selected g).eval (x i) = u₀ i + g * u₁ i → i ∈ good
  pencil : RCN238.NoLargeSelectedPencil selected seeds 131071 81105
  nondivisible : ¬ flow.d0 ∣ flow.a0*flow.c1-flow.a1*flow.c0
  scale_ne : flow.d0 ≠ 0
  affine_ne : flow.A ≠ 0
  denominator_ne : ∀ g ∈ seeds, flow.seedDenominator g ≠ 0
  normalization : ∀ g ∈ seeds,
    flow.d0 * selected g + flow.seedOffset g = flow.seedDenominator g * normalized g
  normalized_degree : ∀ g ∈ seeds, (normalized g).natDegree ≤ 140685
  normalized_agreement : ∀ g ∈ seeds, 181039 ≤
    (Finset.univ.filter (fun i => (normalized g).eval (x i) = word i)).card
  fixedWord : ∀ i ∈ good,
    flow.d0.eval (x i) * u₀ i + flow.c0.eval (x i) = flow.a0.eval (x i) * word i ∧
    flow.d0.eval (x i) * u₁ i + flow.c1.eval (x i) = flow.a1.eval (x i) * word i
  denominator_degree : flow.d0.natDegree + max flow.a0.natDegree flow.a1.natDegree ≤ 9614
  minor_degree : (flow.a1 * flow.c0 - flow.a0 * flow.c1).natDegree ≤ 131071 + 9614

private theorem specialize_affine (B : FlowData K) (g : K) :
    RCN319.specialization K 0 g B.A = B.seedDenominator g := by
  have hlift (f : Polynomial K) : RCN319.specialization K 0 g (liftX f) = f := by
    have h : (RCN319.specialization K 0 g).comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 4))) =
        AlgHom.id K (Polynomial K) := by
      apply Polynomial.algHom_ext
      simp [AlgHom.comp_apply, RCN319.specialization]
    exact DFunLike.congr_fun h f
  rw [FlowData.A, affine, map_add, map_mul, hlift, hlift, FlowData.seedDenominator]
  congr 2 <;> simp [RCN319.specialization]

private theorem affine_ne_of_coprime (B : FlowData K) (hcop : IsCoprime B.a0 B.a1) : B.A ≠ 0 := by
  intro hz
  have h (g : K) : B.seedDenominator g = 0 := by rw [← specialize_affine, hz, map_zero]
  have h₀ : B.a0 = 0 := by simpa [FlowData.seedDenominator] using h 0
  have h₁ : B.a1 = 0 := by simpa [FlowData.seedDenominator, h₀] using h 1
  obtain ⟨L, R, hsum⟩ := hcop
  simp [h₀, h₁] at hsum

private theorem ready_of_normalization
    (x : I ↪ K) (hcard : Fintype.card I = 262144) (original oriented : Finset K)
    (hcount : original.card ≤ oriented.card + (normalizationBudget - 1))
    (B : FlowData K) (nondiv : ¬ B.d0 ∣ B.a0*B.c1-B.a1*B.c0) (hd0 : B.d0 ≠ 0) (hcop : IsCoprime B.a0 B.a1)
    (hdenDegree : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ 9614)
    (hminorDegree : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ 131071 + 9614)
    (u₀ u₁ word : I → K) (good : Finset I) (selected normalized : K → Polynomial K)
    (hdegree : ∀ g ∈ oriented, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ oriented, 181039 ≤
      (Finset.univ.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hgood : ∀ g ∈ oriented, ∀ i,
      (selected g).eval (x i) = u₀ i + g * u₁ i → i ∈ good)
    (hpencil : RCN238.NoLargeSelectedPencil selected oriented 131071 81105)
    (hfixed : ∀ i ∈ good,
      B.d0.eval (x i) * u₀ i + B.c0.eval (x i) = B.a0.eval (x i) * word i ∧
      B.d0.eval (x i) * u₁ i + B.c1.eval (x i) = B.a1.eval (x i) * word i)
    (hnorm : ∀ g ∈ oriented, (normalized g).natDegree ≤ 140685 ∧
      B.d0 * selected g + B.seedOffset g = B.seedDenominator g * normalized g ∧
      ∀ i ∈ good, (selected g).eval (x i) = u₀ i + g * u₁ i →
        (normalized g).eval (x i) = word i) : Nonempty (Ready x original) := by
  let seeds := oriented.filter (fun g => B.seedDenominator g ≠ 0)
  let zeroSeeds := oriented.filter (fun g => B.seedDenominator g = 0)
  have hzero : zeroSeeds.card ≤ 1 := zero_affine_denominator_seeds_card_le B.a0 B.a1 hcop
    zeroSeeds (fun g hg => (Finset.mem_filter.mp hg).2)
  have hsplit : seeds.card + zeroSeeds.card = oriented.card := by
    simpa only [not_ne_iff] using Finset.card_filter_add_card_filter_not
      (s := oriented) (fun g => B.seedDenominator g ≠ 0)
  have hsub : seeds ⊆ oriented := Finset.filter_subset _ _
  refine ⟨{
    flow := B
    u₀ := u₀
    u₁ := u₁
    word := word
    good := good
    seeds := seeds
    selected := selected
    normalized := normalized
    nodes_card := hcard
    count := ?_
    degree := fun g hg => hdegree g (hsub hg)
    agreement := fun g hg => hagreement g (hsub hg)
    agree_good := fun g hg => hgood g (hsub hg)
    pencil := RCN243.noLargeSelectedPencil_mono selected oriented seeds 131071 81105 hsub hpencil
    nondivisible := nondiv
    scale_ne := hd0
    affine_ne := affine_ne_of_coprime B hcop
    denominator_ne := fun g hg => (Finset.mem_filter.mp hg).2
    normalization := fun g hg => (hnorm g (hsub hg)).2.1
    normalized_degree := fun g hg => (hnorm g (hsub hg)).1
    normalized_agreement := ?_
    fixedWord := hfixed
    denominator_degree := hdenDegree
    minor_degree := hminorDegree }⟩
  · unfold normalizationBudget at hcount ⊢
    omega
  · intro g hg
    refine (hagreement g (hsub hg)).trans (Finset.card_le_card ?_)
    intro i hi
    have he := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hnorm g (hsub hg)).2.2 i (hgood g (hsub hg) i he) he⟩

theorem ready_of_hard (x : I ↪ K) (σ : K ≃+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hpower : ∀ g : K, σ g = g ^ prime)
    (hcard : Fintype.card I = 262144) (u : Received K I) (Γ : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)) (hret : K6969Global.RetainedComparison x σ.toRingHom u Γ selected q)
    (enough : ∀g∈Γ,181039≤(agreementSet x u selected g).card)
    (pencil : RCN238.NoLargeSelectedPencil selected Γ 131071 81105)
    (delta : ℕ) (hdelta : delta ≤ 9614) (N : NormalForm q 131071 delta)
    (tw : Frontier6969.GenuineMoving.twist σ.toRingHom N.A N.B=0)
    (nondiv : ¬N.d₀ ∣ N.A 0 * N.C 1 - N.A 1 * N.C 0) :
    Nonempty (Ready x Γ) := by
  let good : Finset I := Finset.univ \ badNodes x σ.toRingHom u q
  have hgoodCard : good.card ≤ 262144 := (Finset.card_le_univ _).trans_eq hcard
  have hgood (i : I) (hi : i ∈ good) :
      q.atNode (MvPolynomial.C (x i)) (Koala6831SeparationFactors.affine 0 (u 0 i) (u 1 i))
        (Koala6831SeparationFactors.affine 1 (σ (u 0 i)) (σ (u 1 i))) = 0 := by
    have hn := (Finset.mem_sdiff.mp hi).2
    apply not_ne_iff.mp
    intro he
    apply hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hn₀ : affineSeedWord (conjugateWord σ.toRingHom (u 0))
        (conjugateWord σ.toRingHom (u 1)) 0 i = Koala6831SeparationFactors.affine 0 (u 0 i) (u 1 i) := by
      simp only [affineSeedWord, conjugateWord, ite_true, Koala6831SeparationFactors.affine,
        mul_comm (MvPolynomial.X (0 : Fin 2))]
    have hn₁ : affineSeedWord (conjugateWord σ.toRingHom (u 0))
        (conjugateWord σ.toRingHom (u 1)) 1 i = Koala6831SeparationFactors.affine 1 (σ (u 0 i)) (σ (u 1 i)) := by
      simp only [affineSeedWord, conjugateWord, ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
        Koala6831SeparationFactors.affine, mul_comm (MvPolynomial.X (1 : Fin 2))] <;> rfl
    change q.atNode (MvPolynomial.C (x i)) _ _ ≠ 0
    rwa [hn₀, hn₁]
  have ha (g : K) (hg : g ∈ Γ) (i : I)
      (hi : (selected g).eval (x i) = u 0 i + g * u 1 i) : i ∈ good := by
    have hmem : i ∈ agreementSet x u selected g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    exact fun hb => Finset.disjoint_left.mp (hret.good g hg).2 hmem hb
  have hpencil : RCN238.NoLargeSelectedPencil selected Γ 131071 81105 := pencil
  have hsmall : delta < prime := hdelta.trans_lt (by decide)
  have hfee : 2 * good.card + 2 + (prime + 1) * delta ≤ normalizationBudget - 1 := by
    calc
      _ ≤ 2 * 262144 + 2 + (prime + 1) * 9614 :=
        Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hgoodCard) 2)
          (Nat.mul_le_mul_left (prime + 1) hdelta)
      _ ≤ _ := by decide
  have horient := KoalaNight.Aligned.left_degree σ.toRingHom N.A N.B N.A_coprime N.B_coprime tw
  obtain ⟨seeds, hsub, hcost, word, normalized, hword, hnorm⟩ :=
    normalForm_exists_retained_normalized_words N σ.toRingHom prime hsmall good x (u 0) (u 1)
      hgood Γ selected hret.selection.degree_le (fun g hg => (hret.good g hg).1)
  obtain ⟨hden, hminor⟩ := leftFlowData_degree_bounds N horient
  exact ready_of_normalization x hcard Γ seeds (hcost.trans (Nat.add_le_add_left (by omega) _))
    (leftFlowData N) nondiv N.d₀_ne N.A_coprime (hden.trans hdelta)
    (hminor.trans (Nat.add_le_add_left hdelta _)) (u 0) (u 1) word good selected normalized
    (fun g hg => hret.selection.degree_le g (hsub hg))
    (fun g hg => enough g (hsub hg)) (fun g hg => ha g (hsub hg))
    (RCN243.noLargeSelectedPencil_mono selected Γ seeds 131071 81105 hsub hpencil) hword
    (fun g hg => ⟨((hnorm g hg).1).trans (by omega), (hnorm g hg).2⟩)

end

end ProximityPrize.SubmissionLower.Left6836Ready





#print axioms ProximityPrize.SubmissionLower.Left6836Ready.ready_of_hard
