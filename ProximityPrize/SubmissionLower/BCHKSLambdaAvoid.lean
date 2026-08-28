import ProximityPrize.Benchmark.TargetLower

open Polynomial

 theorem lambdaAvoid
    {F K J : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    [DecidableEq J]
    (G : Finset K[X]) (c : J → K[X])
    (hirr : ∀ g ∈ G, Irreducible g)
    (hnc : ∀ g ∈ G, g.degree ≠ 0)
    (hwit : ∀ g ∈ G, ∃ j, ¬ g ∣ c j)
    (hcard : G.card < Fintype.card F) :
    ∃ h : K[X], h ∈ Submodule.span F (Set.range c) ∧ ∀ g ∈ G, ¬ g ∣ h := by
  classical
  induction G using Finset.induction_on with
  | empty =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp
  | @insert g s hgs ih =>
      have hsirr : ∀ q ∈ s, Irreducible q := by aesop
      have hsnc : ∀ q ∈ s, q.degree ≠ 0 := by aesop
      have hswit : ∀ q ∈ s, ∃ j, ¬q ∣ c j := by aesop
      have hscard : s.card < Fintype.card F :=
        lt_of_le_of_lt (Finset.card_le_card (Finset.subset_insert g s)) hcard
      obtain ⟨h, hhspan, hh⟩ := ih hsirr hsnc hswit hscard
      obtain ⟨j, hj⟩ := hwit g (by simp)
      let badRoot : K[X] → F := fun q =>
        if hex : ∃ a : F, q ∣ h + a • c j then Classical.choose hex else 0
      let forbidden : Finset F := (insert g s).image badRoot
      have hforbcard : forbidden.card < Fintype.card F := by
        calc
          forbidden.card ≤ (insert g s).card := Finset.card_image_le
          _ < Fintype.card F := hcard
      have hexlam : ∃ a : F, a ∉ forbidden := by
        by_contra hn
        push_neg at hn
        have hu : (Finset.univ : Finset F) ⊆ forbidden := by
          intro x hx
          exact hn x
        have := Finset.card_le_card hu
        simp only [Finset.card_univ] at this
        omega
      obtain ⟨a, ha⟩ := hexlam
      refine ⟨h + a • c j, (Submodule.span F (Set.range c)).add_mem hhspan (Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_range_self j))), ?_⟩
      intro q hq hd
      have hex : ∃ b : F, q ∣ h + b • c j := ⟨a, hd⟩
      have hroot : q ∣ h + badRoot q • c j := by
        simp only [badRoot, dif_pos hex]
        exact Classical.choose_spec hex
      have haeq : a = badRoot q := by
        by_contra hne
        have hdif : q ∣ (a - badRoot q) • c j := by
          simpa [sub_smul] using dvd_sub hd hroot
        rw [Algebra.smul_def] at hdif
        have hneF : a - badRoot q ≠ 0 := sub_ne_zero.mpr hne
        have hneK : algebraMap F K (a - badRoot q) ≠ 0 := by
          simpa using (FaithfulSMul.algebraMap_injective F K).ne hneF
        have hu : IsUnit (algebraMap F K (a - badRoot q)) := isUnit_iff_ne_zero.mpr hneK
        have hqc : q ∣ c j := (hu.map Polynomial.C).dvd_mul_left.mp hdif
        rcases Finset.mem_insert.mp hq with rfl | hqs
        · exact hj hqc
        · have hac : q ∣ a • c j := by
            rcases hqc with ⟨d, hdq⟩
            refine ⟨a • d, ?_⟩
            rw [hdq]
            simp [Algebra.smul_def, mul_assoc, mul_left_comm]
          have hqh : q ∣ h := by simpa using dvd_sub hd hac
          exact hh q hqs hqh
      apply ha
      exact Finset.mem_image.mpr ⟨q, hq, haeq.symm⟩
