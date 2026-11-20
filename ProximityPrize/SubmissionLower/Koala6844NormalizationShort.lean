import ProximityPrize.SubmissionLower.Koala6844Inactive
import ProximityPrize.SubmissionLower.Koala6844NormalizationClassify
import ProximityPrize.SubmissionLower.Koala6844NormalizationConjugateCase
import ProximityPrize.SubmissionLower.Koala6844NormalizationContent
import ProximityPrize.SubmissionLower.Koala6844NormalizationWedge


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open ProximityPrize.Benchmark Polynomial
open Koala6844BenchmarkCases (ReceivedWords agreementSet)
open Koala6844BenchmarkField (frobenius frobenius_apply domain_fixed prime)
open Koala6844Comparison (SymbolicRow SeedRing primitiveExcess)
open Koala6844BenchmarkRetention (RetainedComparison badNodes)
open Koala6844Separation (NormalForm)
open scoped Classical

noncomputable section

set_option maxHeartbeats 850000
set_option maxRecDepth 18000

local notation "K" => IRSProfile.Field
local notation "I" => IRSProfile.Index
local notation "x" => IRSProfile.domain

private theorem isCoprime_scale_left (c : K) (hc : c ≠ 0) {P Q : Polynomial K}
    (h : IsCoprime P Q) : IsCoprime (C c * P) Q := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨C c⁻¹ * a, b, ?_⟩
  have hInv : C c⁻¹ * C c = (1 : Polynomial K) := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  convert hab using 1
  calc
    C c⁻¹ * a * (C c * P) + b * Q = (C c⁻¹ * C c) * (a * P) + b * Q := by ring
    _ = a * P + b * Q := by rw [hInv, one_mul]

private theorem isCoprime_scale_pair (c : K) (hc : c ≠ 0) {P Q : Polynomial K}
    (h : IsCoprime P Q) : IsCoprime (C c * P) (C c * Q) :=
  (isCoprime_scale_left c hc ((isCoprime_scale_left c hc h).symm)).symm

private theorem pencil_bound_on_subset {F : Type} [Field F]
    (seeds retained : Finset F) (hsub : seeds ⊆ retained)
    (selected : F → Polynomial F) (P0 P1 : Polynomial F)
    (hBound : (RCN050.pencilSeeds retained selected P0 P1).card ≤ 81185)
    (dec : DecidablePred (fun g => selected g = P0 + C g * P1)) :
    (@Finset.filter F (fun g => selected g = P0 + C g * P1) dec seeds).card ≤ 81185 := by
  have hsubset : @Finset.filter F (fun g => selected g = P0 + C g * P1) dec seeds ⊆
      RCN050.pencilSeeds retained selected P0 P1 := by
    intro g hg
    simp only [Finset.mem_filter] at hg
    simp only [RCN050.pencilSeeds, Finset.mem_filter]
    exact ⟨hsub hg.1, hg.2⟩
  exact (Finset.card_le_card hsubset).trans hBound

theorem prepare_retained_short
    {received : ReceivedWords} {retained : Finset K} {selected : K → Polynomial K}
    {q : SymbolicRow (SeedRing K)}
    (h : RetainedComparison received retained selected q)
    (hShort : primitiveExcess 131071 q ≤ 9799)
    (N : NormalForm q 131071 (primitiveExcess 131071 q)) :
    retained.card ≤ 11*10^15 ∨
    ∃ data : CenteredVirtualData x (goodNodes received q) frobenius 131071 180960 81184
        (primitiveExcess 131071 q), retained.card ≤ data.seeds.card + 20878792628510 := by
  classical
  let δ := primitiveExcess 131071 q
  let nodes := goodNodes received q
  have hδ : δ ≤ 9799 := hShort
  by_cases hContent : IsCoprime N.d₀ N.d₁
  swap
  · exact Or.inl ((common_content_card_le (p := 2130706433) (by decide) N h.primitive
      frobenius.toRingHom retained selected (fun g hg => (h.good g hg).1) hContent).trans (by decide))
  have hGood (i : I) (hi : i ∈ nodes) :
      q.atNode (MvPolynomial.C (x i))
        (Koala6844SeparationFactors.affine 0 (received 0 i) (received 1 i))
        (Koala6844SeparationFactors.affine 1 (frobenius (received 0 i)) (frobenius (received 1 i))) = 0 := by
    simpa only [Koala6844SeparationFactors.affine, mul_comm] using good_node_identity hi
  obtain ⟨seeds, hsub, hCount, fixed, normalized, hWord, hWitness⟩ :=
    Koala6844Moving.normalForm_exists_retained_normalized_words N frobenius.toRingHom 2130706433
      (by omega) nodes x (received 0) (received 1) hGood retained selected h.selection.degree_le
      (fun g hg => (h.good g hg).1)
  have hNodes : nodes.card = 262144 - (badNodes received q).card :=
    goodNodes_card (received := received) (q := q)
  have hExcess : δ + (badNodes received q).card ≤ 31608 := h.excess_bad
  have hNodeSmall : 131071 + 2 * δ < nodes.card := by omega
  have hPrep : nodes.card + 1 + (2130706433 + 1) * δ ≤ 21000000000000 := by omega
  have hSubPencil (P0 P1 : Polynomial K) (h0 : P0.natDegree ≤ 131071)
      (h1 : P1.natDegree ≤ 131071) :
      (seeds.filter fun g => selected g = P0 + C g * P1).card ≤ 81185 := by
    exact pencil_bound_on_subset seeds retained hsub selected P0 P1
      (h.selection.pencil P0 P1 h0 h1) _
  have hSubAgr (g : K) (hg : g ∈ seeds) :
      180960 ≤ (nodes.filter fun i =>
        (selected g).eval (x i) = received 0 i + g * received 1 i).card := by
    refine (h.selection.agreement g (hsub hg)).trans (Finset.card_le_card ?_)
    intro i hi
    have hAvoid : i ∉ badNodes received q :=
      Finset.disjoint_left.mp (h.good g (hsub hg)).2 hi
    have hAgree : (selected g).eval (x i) = received 0 i + g * received 1 i := by
      simp only [agreementSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi
    refine Finset.mem_filter.mpr ⟨?_, hAgree⟩
    change i ∈ goodNodes received q
    rw [goodNodes_eq_sdiff]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hAvoid⟩
  have hSubNorm (g : K) (hg : g ∈ seeds) :
      180960 ≤ (nodes.filter fun i => (normalized g).eval (x i) = fixed i).card := by
    refine (hSubAgr g hg).trans (Finset.card_le_card ?_)
    intro i hi
    have ⟨hin, hfit⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hin, (hWitness g hg).2.2.2.2.2 i hin hfit⟩
  have hU (i : I) (j : Fin 2) :
      (![received 0 i, received 1 i] : Fin 2 → K) j = received j i := by
    fin_cases j <;> rfl
  have hLeft (i : I) (hi : i ∈ nodes) (j : Fin 2) :
      N.d₀.eval (x i) * received j i + (N.C j).eval (x i) = fixed i * (N.A j).eval (x i) := by
    simpa only [hU] using (hWord i hi).1 j
  have hRight (i : I) (hi : i ∈ nodes) (j : Fin 2) :
      N.d₁.eval (x i) * frobenius (received j i) - (N.D j).eval (x i) =
        fixed i * (N.B j).eval (x i) := by
    have hNode := (hWord i hi).2 j
    rw [hU] at hNode
    change N.d₁.eval (x i) * frobenius (received j i) - (N.D j).eval (x i) =
      fixed i * (N.B j).eval (x i) at hNode
    exact hNode
  let back (j : Fin 2) := (N.B j).map frobenius.symm.toRingHom
  by_cases hW : affineWedge N.A back = 0
  swap
  · have hSmall := nonconjugate_card_le frobenius x nodes seeds selected received fixed N.A N.B N.C
      N.D N.d₀ N.d₁ 131071 180960 81184 δ N.d₀_ne N.d₁_ne N.first_degree N.second_degree
      N.left_degree N.right_degree hW (fun i _ => domain_fixed i) (by omega)
      hLeft hRight (fun g hg => h.selection.degree_le g (hsub hg)) hSubAgr hSubPencil
    exact Or.inl (by omega)
  have hBack : IsCoprime (back 0) (back 1) :=
    N.B_coprime.map (mapRingHom frobenius.symm.toRingHom)
  obtain ⟨scalar, hs, hProp⟩ := affineWedge_zero_proportional N.A_coprime hBack hW
  let A (j : Fin 2) := C scalar * N.A j
  let C0 (j : Fin 2) := C scalar * N.C j
  let d0 := C scalar * N.d₀
  have hComp : frobenius.toRingHom.comp frobenius.symm.toRingHom = RingHom.id K := by
    apply RingHom.ext
    intro t
    change frobenius (frobenius.symm t) = t
    exact RingEquiv.apply_symm_apply frobenius t
  have hB (j : Fin 2) : N.B j = (A j).map frobenius.toRingHom := by
    have hmap := congrArg (Polynomial.map frobenius.toRingHom) (hProp j)
    change ((N.B j).map frobenius.symm.toRingHom).map frobenius.toRingHom =
      (A j).map frobenius.toRingHom at hmap
    simpa only [Polynomial.map_map, hComp, Polynomial.map_id] using hmap
  have hAff (U : Fin 2 → Polynomial K) (g : K) :
      specializeAffine (fun j => C scalar * U j) g = C scalar * specializeAffine U g := by
    unfold specializeAffine
    ring
  have hLeft' (i : I) (hi : i ∈ nodes) (j : Fin 2) :
      d0.eval (x i) * received j i + (C0 j).eval (x i) = fixed i * (A j).eval (x i) := by
    simp only [A, C0, d0, eval_mul, eval_C]
    linear_combination scalar * hLeft i hi j
  have hRight' (i : I) (hi : i ∈ nodes) (j : Fin 2) :
      N.d₁.eval (x i) * frobenius (received j i) - (N.D j).eval (x i) =
        fixed i * ((A j).map frobenius.toRingHom).eval (x i) := by
    rw [← hB j]
    exact hRight i hi j
  have hL (g : K) (hg : g ∈ seeds) :
      specializeAffine A g * normalized g = d0 * selected g + specializeAffine C0 g := by
    have hw := (hWitness g hg).2.2.1
    change N.d₀ * selected g + specializeAffine N.C g = specializeAffine N.A g * normalized g at hw
    rw [show A = (fun j => C scalar * N.A j) from rfl, hAff,
      show C0 = (fun j => C scalar * N.C j) from rfl, hAff]
    unfold d0
    linear_combination -C scalar * hw
  have hR (g : K) (hg : g ∈ seeds) :
      (specializeAffine A g).map frobenius.toRingHom * normalized g =
        N.d₁ * (selected g).map frobenius.toRingHom - specializeAffine N.D (frobenius g) := by
    have hMap := specializeAffine_map frobenius.toRingHom A g
    have he : (fun j => (A j).map frobenius.toRingHom) = N.B := funext fun j => (hB j).symm
    rw [hMap, he]
    change specializeAffine N.B (frobenius g) * normalized g =
      N.d₁ * (selected g).map frobenius.toRingHom - specializeAffine N.D (frobenius g)
    rw [frobenius_apply]
    simpa only [prime, specializeAffine, Koala6844Moving.affineDenominator]
      using (hWitness g hg).2.2.2.1.symm
  have hDen0 (g : K) (hg : g ∈ seeds) : specializeAffine A g ≠ 0 := by
    rw [show A = (fun j => C scalar * N.A j) from rfl, hAff]
    exact mul_ne_zero (C_ne_zero.mpr hs) (hWitness g hg).1
  have hDen (g : K) (hg : g ∈ seeds) (i : I) (hi : i ∈ nodes) :
      (specializeAffine A g).eval (x i) ≠ 0 := by
    rw [show A = (fun j => C scalar * N.A j) from rfl, hAff, eval_mul, eval_C]
    exact mul_ne_zero hs ((hWitness g hg).2.2.2.2.1 i hi)
  have hAdeg : affineDegree A = affineDegree N.A := by
    simp only [affineDegree, A, natDegree_C_mul hs]
  have hCdeg : affineDegree C0 = affineDegree N.C := by
    simp only [affineDegree, C0, natDegree_C_mul hs]
  have hd0deg : d0.natDegree = N.d₀.natDegree := natDegree_C_mul hs
  have hBdeg : affineDegree N.B = affineDegree A := by
    simp only [affineDegree, hB, natDegree_map]
  have h0cap : d0.natDegree + affineDegree A ≤ δ := by
    rw [hd0deg, ← hBdeg]
    exact N.first_degree
  have h1cap : N.d₁.natDegree + affineDegree A ≤ δ := by
    rw [hAdeg]
    exact N.second_degree
  have hCcap : affineDegree A + affineDegree C0 ≤ 131071 + δ := by
    rw [← hBdeg, hCdeg]
    exact N.left_degree
  have hDcap : affineDegree A + affineDegree N.D ≤ 131071 + δ := by
    rw [hAdeg]
    exact N.right_degree
  have hv := center_conjugate_koalabear x frobenius frobenius_apply nodes seeds selected normalized received
    fixed d0 N.d₁ A C0 N.D δ (mul_ne_zero (C_ne_zero.mpr hs) N.d₀_ne) N.d₁_ne
    (isCoprime_scale_left scalar hs hContent) (isCoprime_scale_pair scalar hs N.A_coprime)
    (fun i _ => domain_fixed i) hNodeSmall (by omega) h0cap h1cap hCcap hDcap hDen0 hDen
    hLeft' hRight' hL hR (fun g hg => h.selection.degree_le g (hsub hg)) hSubAgr hSubNorm hSubPencil
    (fun S P Q V B C1 D1 =>
      Koala6844Inactive.card_le_of_inactive frobenius S P Q nodes V B d0 N.d₁ C1 D1
        (mul_ne_zero (C_ne_zero.mpr hs) N.d₀_ne) N.d₁_ne (isCoprime_scale_left scalar hs hContent))
  rcases hv with hsmall | ⟨data, hd⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨data, by omega⟩

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
