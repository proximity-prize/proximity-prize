import ProximityPrize.SubmissionBinaryLower.P64Incidence
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement

/-!
# Lemma SH (shortening) and A2 (PROOF.md 2.6)

Bad slopes whose agreement sets contain a fixed set `Λ*` of `λ*` lines are MCA-bad slopes of a
shortened Reed-Solomon code on `L \ Λ*` of degree `D - λ*` at agreement `A - λ*`. ArkLib's weighted
Johnson exact correlated agreement (A2, `exists_weightedJohnson_line_exactCorrelatedPair`) bounds
them by `johnsonWeightedRefinedExceptionCount`. The two instances of PROOF.md (2.6) follow.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Shorten

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- A polynomial vanishing on the nodes of `s` is a multiple of the nodal polynomial. -/
lemma nodal_mul_divByMonic (s : Finset ι) (ω : ι ↪ F) (f : F[X])
    (hf : ∀ i ∈ s, f.eval (ω i) = 0) :
    Lagrange.nodal s ω * (f /ₘ Lagrange.nodal s ω) = f := by
  have hmon := Lagrange.nodal_monic (s := s) (v := ω)
  have hr : f %ₘ Lagrange.nodal s ω = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (s := s) (v := ω)
      (ω.injective.injOn)
    · rw [← Lagrange.degree_nodal (s := s) (v := ω)]
      exact degree_modByMonic_lt _ hmon
    · intro i hi
      have h := modByMonic_add_div f (Lagrange.nodal s ω)
      have he := congrArg (eval (ω i)) h
      rw [eval_add, eval_mul, Lagrange.eval_nodal_at_node hi, zero_mul, add_zero, hf i hi] at he
      exact he
  have h := modByMonic_add_div f (Lagrange.nodal s ω)
  rw [hr, zero_add] at h
  exact h

omit [DecidableEq F] [Fintype ι] [DecidableEq ι] in
lemma natDegree_le_of_degree_lt_nat {p : F[X]} {c D : ℕ} (h : p.degree < c) (hc : c ≤ D + 1) :
    p.natDegree ≤ D := by
  by_cases hp : p = 0
  · simp [hp]
  · have := (natDegree_lt_iff_degree_lt hp).mpr h
    omega

/-- **Lemma SH with A2.** -/
theorem card_filter_subset_le (ω : ι ↪ F) (u₀ u₁ : ι → F) (Λs : Finset ι)
    (D A n' D' A' m B H : ℕ) (hn' : (Finset.univ \ Λs).card = n') (hD' : D' + Λs.card = D)
    (hA' : A' + Λs.card ≤ A)
    (hcert : IsJohnsonWeightedCertificate n' D' A' m B H) (hD1 : 1 ≤ D') (hDA : D' + 1 ≤ A')
    (hAn : A' ≤ n') (hB : B ≤ 2 * D' + 1)
    (Vs : Finset F) (P : F → F[X]) (Az : F → Finset ι)
    (hdeg : ∀ z ∈ Vs, (P z).natDegree ≤ D) (hAz : ∀ z ∈ Vs, A ≤ (Az z).card)
    (hag : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (ω i) = u₀ i + z * u₁ i)
    (hbad : ∀ z ∈ Vs, ¬ ∃ p₀ p₁ : F[X], p₀.natDegree ≤ D ∧ p₁.natDegree ≤ D ∧
      ∀ i ∈ Az z, p₀.eval (ω i) = u₀ i ∧ p₁.eval (ω i) = u₁ i) :
    ((Vs.filter fun z => Λs ⊆ Az z).card : ℚ) ≤
      johnsonWeightedRefinedExceptionCount n' D' A' B H := by
  classical
  set Lc := Finset.univ \ Λs
  let e : Fin n' ≃ Lc := (Lc.equivFin.trans (finCongr hn')).symm
  let idx : Fin n' → ι := fun k => (e k).1
  have hidx_inj : Function.Injective idx := fun a b h => e.injective (Subtype.ext h)
  have hidx_mem : ∀ k, idx k ∉ Λs := fun k => by
    have := (e k).2
    simp only [Lc, Finset.mem_sdiff, Finset.mem_univ, true_and] at this
    exact this
  have hidx_surj : ∀ i, i ∉ Λs → ∃ k, idx k = i := fun i hi =>
    ⟨e.symm ⟨i, by simp [Lc, hi]⟩, by simp [idx]⟩
  let dom : Fin n' ↪ F := ⟨fun k => ω (idx k), ω.injective.comp hidx_inj⟩
  let G := Lagrange.nodal Λs ω
  have hGmon : G.Monic := Lagrange.nodal_monic
  have hGdeg : G.natDegree = Λs.card := Lagrange.natDegree_nodal
  have hGne : ∀ i, i ∉ Λs → G.eval (ω i) ≠ 0 := by
    intro i hi
    rw [Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun j hj h => hi (by
      have := ω.injective (sub_eq_zero.mp h)
      exact this ▸ hj)
  let p₀ := Lagrange.interpolate Λs ω u₀
  let p₁ := Lagrange.interpolate Λs ω u₁
  have hinj : Set.InjOn ω Λs := ω.injective.injOn
  have hp₀ : ∀ i ∈ Λs, p₀.eval (ω i) = u₀ i := fun i hi =>
    Lagrange.eval_interpolate_at_node u₀ hinj hi
  have hp₁ : ∀ i ∈ Λs, p₁.eval (ω i) = u₁ i := fun i hi =>
    Lagrange.eval_interpolate_at_node u₁ hinj hi
  have hp₀deg : p₀.degree < Λs.card := Lagrange.degree_interpolate_lt u₀ hinj
  have hp₁deg : p₁.degree < Λs.card := Lagrange.degree_interpolate_lt u₁ hinj
  let f : Fin n' → F := fun k => (u₀ (idx k) - p₀.eval (ω (idx k))) / G.eval (ω (idx k))
  let g : Fin n' → F := fun k => (u₁ (idx k) - p₁.eval (ω (idx k))) / G.eval (ω (idx k))
  obtain ⟨ex, hexcard, hex⟩ :=
    exists_weightedJohnson_line_exactCorrelatedPair dom f g hcert hD1 hDA hAn hB
  refine le_trans ?_ hexcard
  have hsub : (Vs.filter fun z => Λs ⊆ Az z) ⊆ ex := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzV, hΛ⟩ := hz
    by_contra hzex
    let Δ : F[X] := P z - p₀ - C z * p₁
    have hΔ : ∀ i ∈ Λs, Δ.eval (ω i) = 0 := by
      intro i hi
      simp only [Δ, eval_sub, eval_mul, eval_C, hag z hzV i (hΛ hi), hp₀ i hi, hp₁ i hi]
      ring
    let v : F[X] := Δ /ₘ G
    have hGv : G * v = Δ := nodal_mul_divByMonic Λs ω Δ hΔ
    have hΔdeg : Δ.natDegree ≤ D := by
      have h0 : p₀.natDegree ≤ D :=
        natDegree_le_of_degree_lt_nat hp₀deg (by omega)
      have h1 : (C z * p₁).natDegree ≤ D := by
        exact (natDegree_C_mul_le z p₁).trans (natDegree_le_of_degree_lt_nat hp₁deg (by omega))
      simpa using natDegree_sub_le_of_le (natDegree_sub_le_of_le (hdeg z hzV) h0) h1
    have hvdeg : v.degree < (D' + 1 : ℕ) := by
      have : v.natDegree ≤ D' := by
        simp only [v]
        rw [natDegree_divByMonic _ hGmon, hGdeg]
        omega
      exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le this)
    have hveval : ∀ k, idx k ∈ Az z → v.eval (dom k) = f k + z * g k := by
      intro k hk
      have hG0 := hGne (idx k) (hidx_mem k)
      have h := congrArg (eval (ω (idx k))) hGv
      rw [eval_mul] at h
      have hΔx : Δ.eval (ω (idx k)) = (u₀ (idx k) - p₀.eval (ω (idx k))) +
          z * (u₁ (idx k) - p₁.eval (ω (idx k))) := by
        simp only [Δ, eval_sub, eval_mul, eval_C, hag z hzV _ hk]
        ring
      have hx : v.eval (ω (idx k)) = ((u₀ (idx k) - p₀.eval (ω (idx k))) +
          z * (u₁ (idx k) - p₁.eval (ω (idx k)))) / G.eval (ω (idx k)) := by
        rw [eq_div_iff hG0, mul_comm, h, hΔx]
      simp only [dom, Function.Embedding.coeFn_mk, f, g]
      rw [hx, add_div, mul_div_assoc]
    have hagree : A' ≤ (polynomialAgreementSet dom (fun k => f k + z * g k) v).card := by
      have hcardsd : A' ≤ (Az z \ Λs).card := by
        have := Finset.le_card_sdiff Λs (Az z)
        have := hAz z hzV
        omega
      calc A' ≤ (Az z \ Λs).card := hcardsd
        _ = ((Finset.univ.filter fun k => idx k ∈ Az z)).card := by
          symm
          apply Finset.card_bij (fun k _ => idx k)
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            exact Finset.mem_sdiff.mpr ⟨hk, hidx_mem k⟩
          · intro a _ b _ h
            exact hidx_inj h
          · intro i hi
            rw [Finset.mem_sdiff] at hi
            obtain ⟨k, hk⟩ := hidx_surj i hi.2
            exact ⟨k, by simp [hk, hi.1], hk⟩
        _ ≤ _ := by
          apply Finset.card_le_card
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hveval k hk
    obtain ⟨pair, hq₀, hq₁, hveq, hagset⟩ := hex z hzex v hvdeg (by convert hagree)
    apply hbad z hzV
    refine ⟨p₀ + G * pair.1, p₁ + G * pair.2, ?_, ?_, ?_⟩
    · have h0 : p₀.natDegree ≤ D :=
        natDegree_le_of_degree_lt_nat hp₀deg (by omega)
      have h1 : pair.1.natDegree ≤ D' :=
        natDegree_le_of_degree_lt_nat hq₀ (by omega)
      refine natDegree_add_le_of_degree_le h0 ?_
      exact natDegree_mul_le.trans (by omega)
    · have h0 : p₁.natDegree ≤ D :=
        natDegree_le_of_degree_lt_nat hp₁deg (by omega)
      have h1 : pair.2.natDegree ≤ D' :=
        natDegree_le_of_degree_lt_nat hq₁ (by omega)
      refine natDegree_add_le_of_degree_le h0 ?_
      exact natDegree_mul_le.trans (by omega)
    · intro i hi
      by_cases hiΛ : i ∈ Λs
      · simp [eval_add, eval_mul, Lagrange.eval_nodal_at_node hiΛ, G, hp₀ i hiΛ, hp₁ i hiΛ]
      · obtain ⟨k, rfl⟩ := hidx_surj i hiΛ
        have hmem := Finset.ext_iff.mp hagset k
        simp only [polynomialAgreementSet, commonPolynomialAgreementSet, Finset.mem_filter,
          Finset.mem_univ, true_and] at hmem
        have hk := hmem.mp (by simpa using hveval k hi)
        have hG0 := hGne (idx k) (hidx_mem k)
        simp only [dom, Function.Embedding.coeFn_mk, f, g, Function.Embedding.trans_apply] at hk
        simp only [eval_add, eval_mul, hk.1, hk.2]
        constructor <;> field_simp <;> ring
  exact_mod_cast Finset.card_le_card hsub

/-! ### The two instances of PROOF.md (2.6) -/

theorem cert208984 : IsJohnsonWeightedCertificate 1888168 839591 1273927 20 30 480 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · simp only [johnsonWeightedR, johnsonWeightedU, johnsonWeightedN, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
  · simp only [johnsonWeightedHeight, johnsonWeightedHeightInt, johnsonWeightedMoment,
      johnsonWeightedSlope, johnsonWeightedR, johnsonWeightedU, johnsonWeightedN,
      johnsonWeightedW, johnsonWeightedT, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num

theorem count208984 :
    johnsonWeightedRefinedExceptionCount 1888168 839591 1273927 30 480 ≤ 117013736431 := by
  simp only [johnsonWeightedRefinedExceptionCount]
  norm_num

theorem cert89952 : IsJohnsonWeightedCertificate 2007200 958623 1392959 54 78 3007 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · simp only [johnsonWeightedR, johnsonWeightedU, johnsonWeightedN, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
  · simp only [johnsonWeightedHeight, johnsonWeightedHeightInt, johnsonWeightedMoment,
      johnsonWeightedSlope, johnsonWeightedR, johnsonWeightedU, johnsonWeightedN,
      johnsonWeightedW, johnsonWeightedT, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num

theorem count89952 :
    johnsonWeightedRefinedExceptionCount 2007200 958623 1392959 78 3007 ≤ 2172022111004 := by
  simp only [johnsonWeightedRefinedExceptionCount]
  norm_num

/-- (2.6) at `λ* = 208984`. -/
theorem card_filter_subset_le_208984 (ω : ι ↪ F) (hn : Fintype.card ι = 2097152)
    (u₀ u₁ : ι → F) (Λs : Finset ι) (hΛ : Λs.card = 208984)
    (Vs : Finset F) (P : F → F[X]) (Az : F → Finset ι)
    (hdeg : ∀ z ∈ Vs, (P z).natDegree ≤ 1048575) (hAz : ∀ z ∈ Vs, 1482911 ≤ (Az z).card)
    (hag : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (ω i) = u₀ i + z * u₁ i)
    (hbad : ∀ z ∈ Vs, ¬ ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 1048575 ∧ p₁.natDegree ≤ 1048575 ∧
      ∀ i ∈ Az z, p₀.eval (ω i) = u₀ i ∧ p₁.eval (ω i) = u₁ i) :
    (Vs.filter fun z => Λs ⊆ Az z).card ≤ 117013736431 := by
  have hn' : (Finset.univ \ Λs).card = 1888168 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn, hΛ]
  have h := card_filter_subset_le ω u₀ u₁ Λs 1048575 1482911 1888168 839591 1273927 20 30 480
    hn' (by omega) (by omega) cert208984 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Vs P Az hdeg hAz hag hbad
  have h2 := h.trans count208984
  exact_mod_cast h2

/-- (2.6) at `λ* = 89952`. -/
theorem card_filter_subset_le_89952 (ω : ι ↪ F) (hn : Fintype.card ι = 2097152)
    (u₀ u₁ : ι → F) (Λs : Finset ι) (hΛ : Λs.card = 89952)
    (Vs : Finset F) (P : F → F[X]) (Az : F → Finset ι)
    (hdeg : ∀ z ∈ Vs, (P z).natDegree ≤ 1048575) (hAz : ∀ z ∈ Vs, 1482911 ≤ (Az z).card)
    (hag : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (ω i) = u₀ i + z * u₁ i)
    (hbad : ∀ z ∈ Vs, ¬ ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 1048575 ∧ p₁.natDegree ≤ 1048575 ∧
      ∀ i ∈ Az z, p₀.eval (ω i) = u₀ i ∧ p₁.eval (ω i) = u₁ i) :
    (Vs.filter fun z => Λs ⊆ Az z).card ≤ 2172022111004 := by
  have hn' : (Finset.univ \ Λs).card = 2007200 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn, hΛ]
  have h := card_filter_subset_le ω u₀ u₁ Λs 1048575 1482911 2007200 958623 1392959 54 78 3007
    hn' (by omega) (by omega) cert89952 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Vs P Az hdeg hAz hag hbad
  have h2 := h.trans count89952
  exact_mod_cast h2

end P64Shorten
end ProximityPrize.SubmissionBinaryLower
