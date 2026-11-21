import ProximityPrize.SubmissionLower.Low48GeometryCover
import ProximityPrize.SubmissionLower.Low48Order

set_option Elab.async false
namespace Low48Geometry
noncomputable section
open P3 (I K node)
open K1_13 (Geom embed extend Row Shape shape OnFactor atJet)
open Low48Price (Messages lowerCap ProperCut LayerBudget Holds)
open scoped BigOperators Polynomial
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative

theorem pole_of_anchor {cap u D Γ} (M : P1.ModelAt cap u D) (F : P1.FamilyAt 179915 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2355) :
    ∃ P : K1_13.PoleData Γ F.scalar, P.H.natDegree ≤ 2355 := by
  have hmax : M.overhead.toNat ≤ (extend M.E).natDegree := by
    rw [Polynomial.natDegree_map]
    change M.overhead.toNat ≤ M.E.natDegree
    unfold P1.ModelAt.overhead
    omega
  obtain ⟨H, hm, hd, hdiv⟩ := K1_13.trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : K[X]} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ : K) : extend (M.amplitude γ) = extend M.A₀ + C (z γ) * extend M.A₁ := by
    simp [P1.ModelAt.amplitude, z]
  refine ⟨⟨H, hm, ?_, ?_, ?_, z, ?_, extend M.factor, extend M.Q, extend M.A₀,
    extend M.A₁, unit M.coprime_factor.symm, unit M.offset_reduced,
    unit M.first_amplitude_unit, ?_, ?_⟩, ?_⟩
  · rw [hd]
    exact ⟨by omega, by omega⟩
  · intro i hz
    obtain ⟨U, hU⟩ := hdiv
    have he : (extend M.E).eval (embed (node i)) ≠ 0 := by
      rw [Polynomial.eval_map_apply]
      exact (map_ne_zero embed).mpr (M.E_nodes i)
    apply he
    change (M.E.map embed).eval _ = 0
    rw [hU, Polynomial.eval_mul, hz, zero_mul]
  · intro γ hγ
    rw [hd]
    rcases (F.mark γ hγ).scalar_degree with h | h
    · simp [h]
    · change ((F.scalar γ).natDegree : ℤ) ≤ (131072 : ℤ) - 1 + M.overhead at h
      change (F.scalar γ).natDegree ≤ 131071 + M.overhead.toNat
      omega
  · intro a b hab
    exact sub_left_inj.mp (embed.injective hab)
  · intro γ hγ
    rw [← amp]
    exact unit (F.mark γ hγ).pole_unit
  · intro γ hγ
    have eqn := (F.mark γ hγ).identity
    have orig : M.factor * M.amplitude γ * F.scalar γ + C (M.label γ) * M.Q =
        M.E * M.decoder (F.mark γ hγ).bad := by rw [← eqn]; ring
    have mapped := congrArg (Polynomial.map embed) orig
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at mapped
    rw [← amp]
    exact mapped ▸ hdiv.trans (dvd_mul_right _ _)
  · change H.natDegree ≤ 2355
    rw [hd]
    omega

private theorem restrict_cut {f Γ s l Δ} (h : ProperCut f Γ s l) (hΔ : Δ ⊆ Γ) :
    ProperCut f Δ s l := by
  obtain ⟨Q, hf, hb, hw, hQ⟩ := h
  exact ⟨Q, hf, hb, hw, fun γ hγ => hQ γ (hΔ hγ)⟩

/-- Count an ordinary low-height family from its anchor, primary cuts and fat equations. -/
theorem count_of_data {w Γ s} (hmsg : Messages w Γ s)
    (P : Row 4) (hP : P ≠ 0) (hbox : K1_13.InBox (shape P) ⟨123, 50, 13⟩)
    (hw : Low48Price.TrueWeightLE P Low48Price.anchorCutoff)
    (hz : ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0)
    (lower : ∀ top ≤ 13, Low48Price.c5 top)
    (proper : Low48Price.c6) (fat : Low48Price.c7)
    (ledger : ∀ top ≤ 13, ∀ (n : ℕ) (a : Fin n → Shape) (l cost : Fin n → ℕ),
      Low48Price.Fits top a → LayerBudget a l →
      (∀ i, 0 < l i → cost i ≤ Low48Price.physicalPrice (a i) (l i)) →
      (∀ i, K1_13.FatEligible (a i) → cost i ≤ Low48Price.fatPrice (a i)) →
      lowerCap top + (∑ i, cost i) ≤ 268265986140016442)
    (book : Finset K) (E : Low48Price.FatEquations) (booked : book.card ≤ 140000)
    (hE : ∀ γ ∈ Γ, γ ∉ book → Holds E (extend (s γ))) :
    Γ.card ≤ 268265986140156442 := by
  classical
  obtain ⟨top, n, g, f, htop, cover⟩ := Low48GeometryCover.cover_of_anchor P hP hbox hw hz
  have hm : Low48Order.Messages w Γ s := ⟨hmsg.degree, hmsg.hits⟩
  obtain ⟨l, layers, cut⟩ := Low48Order.proper_layers (f := f) hm
    (fun i => (cover.factors i).1) (fun i => (cover.factors i).2.1)
    (fun i => (cover.factors i).2.2.1.2.2.trans_lt (by decide : 13 < K1.p)) cover.different
  have hbudget : LayerBudget (fun i => shape (f i)) l := layers
  have hcut (i : Fin n) (hi : 0 < l i) : ProperCut (f i) Γ s (l i) := cut i hi
  let low := Γ.filter (fun γ => atJet g (extend (s γ)) = 0)
  have low_bound : low.card ≤ lowerCap top :=
    lower top htop _ _ _ (hmsg.mono (Finset.filter_subset _ _)) _ cover.lower
      (fun _ h => (Finset.mem_filter.mp h).2)
  let pieces (i : Fin n) := Γ.filter (fun γ => γ ∉ book ∧ OnFactor (f i) (extend (s γ)))
  have part_sub (i) : pieces i ⊆ Γ := Finset.filter_subset _ _
  have on_part i : ∀ γ ∈ pieces i, OnFactor (f i) (extend (s γ)) :=
    fun _ h => (Finset.mem_filter.mp h).2.2
  have total := ledger top htop n (fun i => shape (f i)) l (fun i => (pieces i).card) cover.fits hbudget
    (fun i h => proper _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) _ h
      (restrict_cut (hcut i h) (part_sub i)))
    (fun i h => fat _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) h E
      (fun γ hγ => hE γ (part_sub i hγ) (Finset.mem_filter.mp hγ).2.1))
  have covers : Γ ⊆ book ∪ low ∪ Finset.univ.biUnion pieces := by
    intro γ hγ
    by_cases hb : γ ∈ book
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    rcases cover.covers γ hγ with hg | ⟨i, hfi⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hg⟩))
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hb, hfi⟩⟩
  calc
    Γ.card ≤ _ := Finset.card_le_card covers
    _ ≤ (book.card + low.card) + ∑ i, (pieces i).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le)
    _ = book.card + (low.card + ∑ i, (pieces i).card) := Nat.add_assoc _ _ _
    _ ≤ 140000 + (lowerCap top + ∑ i, (pieces i).card) :=
      Nat.add_le_add booked (Nat.add_le_add_right low_bound _)
    _ ≤ 268265986140156442 := Nat.add_le_add_left total _

#print axioms count_of_data
end
end Low48Geometry
