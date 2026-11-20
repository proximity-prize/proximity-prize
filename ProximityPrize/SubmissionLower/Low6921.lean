import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.LowAnchor6921
import ProximityPrize.SubmissionLower.LowPrimary6921
import ProximityPrize.SubmissionLower.LowPrice6921Lower
import ProximityPrize.SubmissionLower.LowPrice6921Fat
import ProximityPrize.SubmissionLower.LowPrice6921Relaxed
import ProximityPrize.SubmissionLower.Fast075
import ProximityPrize.SubmissionLower.Fast076
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace Low6921
noncomputable section
open K21 Polynomial K1_13
open scoped BigOperators
theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ : K) (hγ : γ ∈ Γ) : (F.scalar γ).natDegree ≤ 131071 + M.overhead.toNat := by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · omega

theorem messages_of_anchor {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (hw : M.overhead ≤ 2447) : LowFat6921.Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    have := degree_at_height M F γ hγ
    omega
  · intro γ hγ
    let m := F.mark γ hγ
    exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩

theorem pole_of_anchor {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2447) : ∃ pole : PoleData Γ F.scalar, pole.H.natDegree ≤ 2447 := by
  have hmax : M.overhead.toNat ≤ (extend M.E).natDegree := by
    rw [Polynomial.natDegree_map]
    unfold AnchorModel.overhead
    omega
  obtain ⟨H, hm, hd, hdiv⟩ := trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : K[X]} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ : K) : extend (M.amplitude γ) = extend M.A₀ + C (z γ) * extend M.A₁ := by
    simp [AnchorModel.amplitude, z]
  refine ⟨⟨H, hm, ?_, ?_, ?_, z, ?_, extend M.factor, extend M.Q, extend M.A₀,
    extend M.A₁, unit M.coprime_factor.symm, unit M.offset_reduced,
    unit M.first_amplitude_unit, ?_, ?_⟩, ?_⟩
  · rw [hd]
    omega
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
    exact degree_at_height M F γ hγ
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

  · change H.natDegree ≤ 2447
    omega


private theorem submessages {w Γ s Δ} (h : LowFat6921.Messages w Γ s) (hΔ : Δ ⊆ Γ) :
    LowFat6921.Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩

private theorem subcut {f Γ s l Δ} (h : LowPrice6921.RelaxedProperCut f Γ s l) (hs : Δ ⊆ Γ) :
    LowPrice6921.RelaxedProperCut f Δ s l := by
  obtain ⟨Q, hp, hb, hw, ht⟩ := h
  exact ⟨Q, hp, hb, hw, fun z hz => ht z (hs hz)⟩

private theorem h8 : K1_13.c8 := K1_13_8.of_children K1_13_8_1.proof K1_13_8_2.proof
  K1_13_8_3.proof K1_13_8_4.proof

theorem count : K21.c13 := by
  classical
  intro u D M Γ F lo hi
  let s := F.scalar
  have hmsg : LowFat6921.Messages M.word Γ s := messages_of_anchor M F hi
  obtain ⟨pole, hpole⟩ := pole_of_anchor M F lo hi
  obtain ⟨n, g, f, cover⟩ := LowAnchor6921.cover _ hmsg
  obtain ⟨l, layers, cut⟩ := LowPrimary6921.layer_budget _ hmsg g f cover
  obtain ⟨book, E, booked, hE⟩ := LowFat6921.fat_equations _ hmsg pole hpole
  let low := Γ.filter (fun γ => atJet g (extend (s γ)) = 0)
  have low_bound : low.card ≤ 18512789806000648 :=
    LowPrice6921.lower_count _ (submessages hmsg (Finset.filter_subset _ _)) _ cover.lower
      (fun _ h => (Finset.mem_filter.mp h).2)
  let pieces (i : Fin n) := Γ.filter (fun γ => γ ∉ book ∧ OnFactor (f i) (extend (s γ)))
  have part_sub (i) : pieces i ⊆ Γ := Finset.filter_subset _ _
  have on_part i : ∀ γ ∈ pieces i, OnFactor (f i) (extend (s γ)) :=
    fun _ h => (Finset.mem_filter.mp h).2.2
  have total := h8 n (fun i => shape (f i)) l (fun i => (pieces i).card) cover.fits layers
    (fun i h => LowPrice6921.physical_count_relaxed _ (submessages hmsg (part_sub i)) _ (cover.factors i) (on_part i) _ h
      (subcut (cut i h) (part_sub i)))
    (fun i h => LowPrice6921.fat_count _ (submessages hmsg (part_sub i)) _ (cover.factors i) (on_part i) h E
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
    _ ≤ _ := by omega

end
end Low6921
