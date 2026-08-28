import ProximityPrize.SubmissionLower.BCHKSLocatorCramerSelection6400

/-!
# Selecting a Cramer circuit from a rank drop

For a finite family in a finite-dimensional space and a linear high-part
map, a strict drop from full-span rank to high-image rank selects a high-image
basis together with one additional generator outside the full span of that
basis.  The resulting `q+1` full vectors are independent, while the last high
image lies in the span of the first `q`.  This is the exact circuit shape
consumed by the locator Cramer obstruction.
-/

namespace ProximityPrize.SubmissionLower

open Module Submodule

set_option autoImplicit false

theorem exists_fullIndependent_highBasis_with_extra
    {K I V W : Type} [Field K] [Fintype I]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (full : I → V) (H : V →ₗ[K] W)
    (hrank : Module.finrank K
        (Submodule.span K (Set.range (H ∘ full))) <
      Module.finrank K (Submodule.span K (Set.range full))) :
    ∃ (q : ℕ) (idx : Fin (q + 1) → I),
      q = Module.finrank K
        (Submodule.span K (Set.range (H ∘ full))) ∧
      LinearIndependent K (fun j => full (idx j)) ∧
      LinearIndependent K
        (fun j : Fin q => H (full (idx j.castSucc))) ∧
      H (full (idx (Fin.last q))) ∈
        Submodule.span K (Set.range
          (fun j : Fin q => H (full (idx j.castSucc)))) := by
  classical
  let high : I → W := H ∘ full
  let Q : Submodule K W := Submodule.span K (Set.range high)
  let q := Module.finrank K Q
  haveI : Module.Finite K Q := by infer_instance
  obtain ⟨b, hbmem, hbspan, hbli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range high)
  have hexistsIdx : ∀ j : Fin q, ∃ i : I, high i = b j := by
    intro j
    exact hbmem j
  choose idx₀ hidx₀ using hexistsIdx
  have hhighLI : LinearIndependent K
      (fun j : Fin q => H (full (idx₀ j))) := by
    convert hbli using 1
    funext j
    simpa [high] using hidx₀ j
  have hbaseLI : LinearIndependent K (fun j : Fin q => full (idx₀ j)) := by
    apply LinearIndependent.of_comp H
    simpa [Function.comp_def] using hhighLI
  have hselectedHighSpan :
      Submodule.span K (Set.range
        (fun j : Fin q => H (full (idx₀ j)))) = Q := by
    calc
      Submodule.span K (Set.range
          (fun j : Fin q => H (full (idx₀ j)))) =
          Submodule.span K (Set.range b) := by
            congr 1
            ext x
            constructor
            · rintro ⟨j, rfl⟩
              exact ⟨j, (hidx₀ j).symm⟩
            · rintro ⟨j, rfl⟩
              exact ⟨j, hidx₀ j⟩
      _ = Q := hbspan
  have hextra : ∃ i₀ : I,
      full i₀ ∉ Submodule.span K
        (Set.range (fun j : Fin q => full (idx₀ j))) := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    have hle : Submodule.span K (Set.range full) ≤
        Submodule.span K (Set.range (fun j : Fin q => full (idx₀ j))) := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact hno i
    have hrankle := Submodule.finrank_mono hle
    have hbaseRank : Module.finrank K
        (Submodule.span K (Set.range (fun j : Fin q => full (idx₀ j)))) = q := by
      simpa [q] using finrank_span_eq_card hbaseLI
    have hQrank : Module.finrank K
        (Submodule.span K (Set.range (H ∘ full))) = q := by
      rfl
    rw [hbaseRank] at hrankle
    rw [hQrank] at hrank
    omega
  obtain ⟨i₀, hi₀⟩ := hextra
  let idx : Fin (q + 1) → I := Fin.snoc idx₀ i₀
  refine ⟨q, idx, rfl, ?_, ?_, ?_⟩
  · have hfamily : (fun j => full (idx j)) =
        Fin.snoc (fun j => full (idx₀ j)) (full i₀) := by
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [idx]
      · simp [idx]
    rw [hfamily]
    exact linearIndependent_finSnoc.mpr ⟨hbaseLI, hi₀⟩
  · simpa [idx] using hhighLI
  · have hiQ : H (full i₀) ∈ Q := by
      exact Submodule.subset_span (Set.mem_range_self i₀)
    rw [← hselectedHighSpan] at hiQ
    simpa [idx] using hiQ

/-- A nonzero vector in the full candidate span which the high-part map kills
forces a strict rank drop.  The proof selects a basis from the original
finite family; the nonzero kernel vector gives a nontrivial dependence among
its high images.  This avoids any rank-nullity instance conversion. -/
theorem finrank_highSpan_lt_fullSpan_of_nonzero_mem_ker
    {K I V W : Type} [Field K] [Fintype I]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (full : I → V) (H : V →ₗ[K] W) (x : V)
    (hxspan : x ∈ Submodule.span K (Set.range full))
    (hxne : x ≠ 0) (hxker : H x = 0) :
    Module.finrank K
        (Submodule.span K (Set.range (H ∘ full))) <
      Module.finrank K (Submodule.span K (Set.range full)) := by
  classical
  let P : Submodule K V := Submodule.span K (Set.range full)
  haveI : Module.Finite K P := by
    exact Module.Finite.span_of_finite K (Set.finite_range full)
  obtain ⟨b, hbmem, hbspan, hbli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range full)
  have hxmem : x ∈ Submodule.span K (Set.range b) := by
    rw [hbspan]
    exact hxspan
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).mp hxmem
  have hcne : ∃ j, c j ≠ 0 := by
    by_contra hzero
    simp only [not_exists, not_not] at hzero
    have hc0 : c = 0 := funext hzero
    rw [hc0] at hc
    simp at hc
    exact hxne hc.symm
  have himagezero : ∑ j, c j • H (b j) = 0 := by
    have hmap := congrArg H hc
    simpa [map_sum, hxker] using hmap
  have himageDependent :
      ¬ LinearIndependent K (fun j => H (b j)) := by
    intro hli
    obtain ⟨j, hj⟩ := hcne
    exact hj ((Fintype.linearIndependent_iff.mp hli c himagezero) j)
  let m := Module.finrank K P
  have himageLe : Module.finrank K
      (Submodule.span K (Set.range (fun j => H (b j)))) ≤ m := by
    have hle := finrank_range_le_card (R := K) (b := fun j => H (b j))
    change Module.finrank K
      (Submodule.span K (Set.range (fun j => H (b j)))) ≤
        Fintype.card (Fin (Module.finrank K P)) at hle
    simpa [m] using hle
  have himageNe : Module.finrank K
      (Submodule.span K (Set.range (fun j => H (b j)))) ≠ m := by
    intro heq
    apply himageDependent
    apply (linearIndependent_iff_card_eq_finrank_span).mpr
    change Fintype.card (Fin (Module.finrank K P)) =
      Module.finrank K
        (Submodule.span K (Set.range (fun j => H (b j))))
    simpa [m] using heq.symm
  have himageLt : Module.finrank K
      (Submodule.span K (Set.range (fun j => H (b j)))) < m := by
    omega
  have hhighSpan : Submodule.span K (Set.range (H ∘ full)) =
      Submodule.span K (Set.range (fun j => H (b j))) := by
    rw [Set.range_comp]
    rw [show (fun j => H (b j)) = H ∘ b by rfl, Set.range_comp]
    rw [← Submodule.map_span, ← Submodule.map_span]
    exact congrArg (Submodule.map H) hbspan.symm
  rw [hhighSpan]
  simpa [P, m] using himageLt

end ProximityPrize.SubmissionLower
