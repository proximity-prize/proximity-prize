import ProximityPrize.SubmissionLower.LowFat82170
import ProximityPrize.SubmissionLower.LowFatCount82170
import ProximityPrize.SubmissionLower.LowFactorCount82170

set_option Elab.async false
namespace LowFamily82170
noncomputable section
open P3 (I K node)
open K1_13 (Geom embed extend Row Shape shape OnFactor atJet)
open LowPriceData82170 (Messages lowerCap)
open LowCaps82170 (factorCap)
open scoped BigOperators Polynomial
open Polynomial
private theorem pole_of_anchor {cap u D Γ} (M : P1.ModelAt cap u D) (F : P1.FamilyAt 179974 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2296) :
    ∃ P : K1_13.PoleData Γ F.scalar, P.H.natDegree ≤ 2296 := by
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
  · change H.natDegree ≤ 2296
    rw [hd]
    omega

private theorem gateLowRows82170_1_1_1 : LowRows82170_1_1.c1 := LowRows82170_1_1_1.proof
private theorem gateLowRows82170_1_1_2 : LowRows82170_1_1.c2 := LowRows82170_1_1_2.proof
private theorem gateLowRows82170_1_1_3 : LowRows82170_1_1.c3 := LowRows82170_1_1_3.proof
private theorem gateLowRows82170_1_1 : LowRows82170_1.c1 := LowRows82170_1_1.of_children gateLowRows82170_1_1_1 gateLowRows82170_1_1_2 gateLowRows82170_1_1_3
private theorem gateLowRows82170_1_2 : LowRows82170_1.c2 := LowRows82170_1_2.proof
private theorem gateLowRows82170_1_3 : LowRows82170_1.c3 := LowRows82170_1_3.proof
private theorem gateLowRows82170_1 : LowRows82170.c1 := LowRows82170_1.of_children gateLowRows82170_1_1 gateLowRows82170_1_2 gateLowRows82170_1_3
private theorem gateLowRows82170_2 : LowRows82170.c2 := LowRows82170_2.proof
private theorem gateLowRows82170 : LowPriceData82170.c5 := LowRows82170.of_children gateLowRows82170_1 gateLowRows82170_2
private theorem gateLowCutCount82170_1 : LowCutCount82170.c1 := LowCutCount82170_1.proof
private theorem gateLowCutCount82170_2_1 : LowCutCount82170_2.c1 := LowCutCount82170_2_1.proof
private theorem gateLowCutCount82170_2_2 : LowCutCount82170_2.c2 := LowCutCount82170_2_2.proof
private theorem gateLowCutCount82170_2_3_1 : LowCutCount82170_2_3.c1 := LowCutCount82170_2_3_1.proof
private theorem gateLowCutCount82170_2_3_2 : LowCutCount82170_2_3.c2 := LowCutCount82170_2_3_2.proof
private theorem gateLowCutCount82170_2_3 : LowCutCount82170_2.c3 := LowCutCount82170_2_3.of_children gateLowCutCount82170_2_3_1 gateLowCutCount82170_2_3_2
private theorem gateLowCutCount82170_2 : LowCutCount82170.c2 := LowCutCount82170_2.of_children gateLowCutCount82170_2_1 gateLowCutCount82170_2_2 gateLowCutCount82170_2_3
private theorem gateLowCutCount82170_3_1 : LowCutCount82170_3.c1 := LowCutCount82170_3_1.proof
private theorem gateLowCutCount82170_3_2 : LowCutCount82170_3.c2 := LowCutCount82170_3_2.proof
private theorem gateLowCutCount82170_3 : LowCutCount82170.c3 := LowCutCount82170_3.of_children gateLowCutCount82170_3_1 gateLowCutCount82170_3_2
private theorem gateLowCutCount82170 : LowPriceData82170.c6 := LowCutCount82170.of_children gateLowCutCount82170_1 gateLowCutCount82170_2 gateLowCutCount82170_3
private theorem gateLowFatCount82170_1 : LowFatCount82170.c1 := LowFatCount82170_1.proof
private theorem gateLowFatCount82170_2_1 : LowFatCount82170_2.c1 := LowFatCount82170_2_1.proof
private theorem gateLowFatCount82170_2_2 : LowFatCount82170_2.c2 := LowFatCount82170_2_2.proof
private theorem gateLowFatCount82170_2_3_1 : LowFatCount82170_2_3.c1 := LowFatCount82170_2_3_1.proof
private theorem gateLowFatCount82170_2_3_2 : LowFatCount82170_2_3.c2 := LowFatCount82170_2_3_2.proof
private theorem gateLowFatCount82170_2_3_3 : LowFatCount82170_2_3.c3 := LowFatCount82170_2_3_3.proof
private theorem gateLowFatCount82170_2_3 : LowFatCount82170_2.c3 := LowFatCount82170_2_3.of_children gateLowFatCount82170_2_3_1 gateLowFatCount82170_2_3_2 gateLowFatCount82170_2_3_3
private theorem gateLowFatCount82170_2 : LowFatCount82170.c2 := LowFatCount82170_2.of_children gateLowFatCount82170_2_1 gateLowFatCount82170_2_2 gateLowFatCount82170_2_3
private theorem gateLowFatCount82170_3 : LowFatCount82170.c3 := LowFatCount82170_3.proof
private theorem gateLowFatCount82170 : LowPriceData82170.c7 := LowFatCount82170.of_children gateLowFatCount82170_1 gateLowFatCount82170_2 gateLowFatCount82170_3
private theorem restrict_cut {f Γ s l Δ} (h : LowLayers82170.ProperCut f Γ s l) (hΔ : Δ ⊆ Γ) :
    LowLayers82170.ProperCut f Δ s l := by
  obtain ⟨Q, hf, hb, hw, hQ⟩ := h
  exact ⟨Q, hf, hb, hw, fun γ hγ => hQ γ (hΔ hγ)⟩

/-- Size of any anchored family with positive overhead at most 2,296. -/
theorem count {cap u D Γ} (M : P1.ModelAt cap u D) (F : P1.FamilyAt 179974 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2296) : Γ.card ≤ 266428705926712637 := by
  classical
  let s := F.scalar
  have hmsg := LowPriceData82170.of_family M F hi
  obtain ⟨pole, hpole⟩ := pole_of_anchor M F lo hi
  obtain ⟨n,g,f,l,cover,layers,cut⟩ := LowLayers82170.cover_and_layers M F hi
  obtain ⟨book,E,booked,hE⟩ := LowFat82170.fat_equations M.word Γ s
    ⟨hmsg.degree,hmsg.hits⟩ pole hpole
  let low := Γ.filter (fun γ => atJet g (extend (s γ)) = 0)
  have low_bound : low.card ≤ lowerCap :=
    gateLowRows82170 _ _ _ (hmsg.mono (Finset.filter_subset _ _)) _ cover.lower
      (fun _ h => (Finset.mem_filter.mp h).2)
  let pieces (i : Fin n) := Γ.filter (fun γ => γ ∉ book ∧ OnFactor (f i) (extend (s γ)))
  have part_sub (i) : pieces i ⊆ Γ := Finset.filter_subset _ _
  have on_part i : ∀ γ ∈ pieces i, OnFactor (f i) (extend (s γ)) :=
    fun _ h => (Finset.mem_filter.mp h).2.2
  have total := LowFactorCount82170.total n (fun i => shape (f i)) l (fun i => (pieces i).card) cover.fits layers
    (fun i h => gateLowCutCount82170 _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) _ h
      (restrict_cut (cut i h) (part_sub i)))
    (fun i h => gateLowFatCount82170 _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) h E
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
    _ ≤ 140000 + lowerCap + factorCap := Nat.add_le_add (Nat.add_le_add booked low_bound) total
    _ = 266428705926712637 := by decide

#print axioms count
end
end LowFamily82170
