import ProximityPrize.SubmissionLower.LowFat82190
import ProximityPrize.SubmissionLower.LowFatCount82190
import ProximityPrize.SubmissionLower.LowCutCount82190
import ProximityPrize.SubmissionLower.LowRows82190
import ProximityPrize.SubmissionLower.LowFactorCount82190

set_option Elab.async false
namespace LowFamily82190
noncomputable section
open P3 (I K node)
open K1_13 (Geom embed extend Row Shape shape OnFactor atJet)
open LowCaps82190 (Tier topCap)
open scoped BigOperators Polynomial
open Polynomial
private theorem pole_of_anchor {cap u D Γ} (M : P1.ModelAt cap u D) (F : P1.FamilyAt 179954 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2348) :
    ∃ P : K1_13.PoleData Γ F.scalar, P.H.natDegree ≤ 2348 := by
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
  · change H.natDegree ≤ 2348
    rw [hd]
    omega

private theorem restrict_cut {f Γ s l Δ} (h : LowLayers82190.ProperCut f Γ s l) (hΔ : Δ ⊆ Γ) :
    LowLayers82190.ProperCut f Δ s l := by
  obtain ⟨Q, hf, hb, hw, hQ⟩ := h
  exact ⟨Q, hf, hb, hw, fun γ hγ => hQ γ (hΔ hγ)⟩

/-- Size of any anchored family with positive overhead at most 2,348. -/
theorem count {cap u D Γ} (M : P1.ModelAt cap u D) (F : P1.FamilyAt 179954 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2348) : Γ.card ≤ 266765102638335029 := by
  classical
  let s := F.scalar
  have hmsg := LowPriceData82190.of_family M F hi
  obtain ⟨pole, hpole⟩ := pole_of_anchor M F lo hi
  obtain ⟨n,g,f,l,cover,layers,cut⟩ := LowLayers82190.cover_and_layers M F hi
  obtain ⟨book,E,booked,hE⟩ := LowFat82190.fat_equations M.word Γ s
    ⟨hmsg.degree,hmsg.hits⟩ pole hpole
  let low := Γ.filter (fun γ => atJet g (extend (s γ)) = 0)
  have low_sub : low ⊆ Γ := Finset.filter_subset _ _
  have low_vanish : ∀ γ ∈ low, atJet g (extend (s γ)) = 0 :=
    fun _ h => (Finset.mem_filter.mp h).2
  let pieces (i : Fin n) := Γ.filter (fun γ => γ ∉ book ∧ OnFactor (f i) (extend (s γ)))
  have part_sub (i) : pieces i ⊆ Γ := Finset.filter_subset _ _
  have on_part i : ∀ γ ∈ pieces i, OnFactor (f i) (extend (s γ)) :=
    fun _ h => (Finset.mem_filter.mp h).2.2
  have total (tier : Tier) (htop : (∑ i, (shape (f i)).t) ≤ topCap tier) :=
    LowFactorCount82190.total tier n (fun i => shape (f i)) l (fun i => (pieces i).card) cover.fits htop layers
    (fun i h => LowCutCount82190.proof _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) _ h
      (restrict_cut (cut i h) (part_sub i)))
    (fun i h => LowFatCount82190.proof _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) h E
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
    _ ≤ 266765102638335029 := by
      rcases cover.split with htop | hnarrow
      · have hlow : low.card ≤ 18443086149371809 :=
          LowRows82190.count _ _ _ (hmsg.mono low_sub) _ cover.lower low_vanish
        exact (Nat.add_le_add (Nat.add_le_add booked hlow) (total .small htop)).trans (by decide)
      · have hlow : low.card ≤ 11922706877484426 :=
          LowRows82190.count_narrow _ _ _ (hmsg.mono low_sub) _ cover.lower hnarrow low_vanish
        exact (Nat.add_le_add (Nat.add_le_add booked hlow) (total .large cover.fits.2.2.2)).trans
          (by decide)

#print axioms count
end
end LowFamily82190
