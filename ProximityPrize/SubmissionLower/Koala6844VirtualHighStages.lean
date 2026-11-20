import ProximityPrize.SubmissionLower.Koala6844VirtualHighInitialBudget


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open RCN132 RCN137
open scoped Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {K Seed : Type} [Field K] [Field Seed]
local notation "R" => MvPolynomial (Fin 4) K
local notation "E" => RationalCoefficients K

theorem exists_virtual_families [CharP K modulus]
    (hp : modulus.Prime) (embed : Seed →+* E) (v : Seed → E)
    (A : Finset Seed) (hinj : Set.InjOn v (↑A : Set Seed))
    (P H : R) (hP : P ≠ 0) (hH : H ≠ 0) (w gain Dp Dr Da : ℕ) (hgain : 0 < gain)
    (primaryMem : P ∈ globalBox K Dp w 179 3800 3800)
    (roomMem : H ∈ globalBox K Dr w 1451 32586 32586)
    (primaryEval : ∀ g ∈ A, MvPolynomial.eval (seedPoint embed modulus v g)
      (rationalSurfaceMap K P) = 0)
    (roomEval : ∀ i : Fin 4, (i = 2 ∨ i = 3) → ∀ k ≤ 31, ∀ g ∈ A,
      MvPolynomial.eval (seedPoint embed modulus v g)
        (rationalSurfaceMap K (((MvPolynomial.pderiv i : R → R)^[k]) H)) = 0)
    {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (r : V →ₗ[K] R) (hr : Function.Injective r)
    (adaptiveMem : ∀ a, r a ∈ globalBox K Da w 6975 133094 133094)
    (adaptiveDim : gain * adaptiveGap ≤ Module.finrank K V)
    (adaptiveEval : ∀ a, ∀ j ≤ 6975,
      r a ∈ globalBox K (Da-j*gain) w 6975 133094 133094 →
      ∀ i : Fin 4, (i = 2 ∨ i = 3) → ∀ k ≤ j, ∀ g ∈ A,
        MvPolynomial.eval (seedPoint embed modulus v g)
          (rationalSurfaceMap K (((MvPolynomial.pderiv i : R → R)^[k]) (r a))) = 0) :
    ∃ U ⊆ primaryFactors P, ∃ resolvedRoom resolvedAdaptive excluded : Finset Seed,
      A ⊆ resolvedRoom ∪ resolvedAdaptive ∪
        U.biUnion (regularSeeds embed modulus v A) ∪ excluded ∧
      resolvedRoom.card ≤ resultantCharge modulus primaryBox roomBox ∧
      resolvedAdaptive.card ≤ resultantCharge modulus remainingBox adaptiveBox ∧
      excluded.card ≤ excludedBudget ∧
      (U = ∅ ∨
        1 ≤ (factorRectangle U).value ∧ (factorRectangle U).value ≤ 45 ∧
        (factorRectangle U).first ≤ 1018 ∧ (factorRectangle U).second ≤ 1018 ∧
        adaptiveGap ≤ bandRectangle 6975 133094 (factorRectangle U).value
          (factorRectangle U).first (factorRectangle U).second) := by
  classical
  let F := primaryFactors P
  obtain ⟨_,hpy,hpb,hpc⟩ := wall_of_mem_globalBox hP primaryMem
  have hfac (f : R) (hf : f ∈ F) := (Finset.mem_filter.mp hf)
  have hnorm (f : R) (hf : f ∈ F) := normalizedFactorSet_spec P f (hfac f hf).1
  have hprime (f : R) (hf : f ∈ F) : Prime f := (hnorm f hf).1.prime
  have hnon (f : R) (hf : f ∈ F) (g : R) (hg : g ∈ F) (hne : f ≠ g) :=
    primary_nonassociate P (hfac f hf).1 (hfac g hg).1 hne
  have haxis (f : R) (hf : f ∈ F) :
      ∃ i : Fin 4, (i = 2 ∨ i = 3) ∧ 0 < f.degreeOf i ∧ f.degreeOf i < modulus := by
    have hb := coordinate_degree_le_of_dvd 2 f P (hnorm f hf).2 hP
    have hc := coordinate_degree_le_of_dvd 3 f P (hnorm f hf).2 hP
    have hpos := (hfac f hf).2.2
    by_cases h : 0 < f.degreeOf 2
    · exact ⟨2,Or.inl rfl,h,(hb.trans hpb).trans_lt (by decide +kernel)⟩
    · exact ⟨3,Or.inr rfl,by omega,(hc.trans hpc).trans_lt (by decide +kernel)⟩
  obtain ⟨B,hBF,hBcap,hroom⟩ := room_factor_partition hp (by decide +kernel : 31 < modulus)
    H hH roomMem F hprime hnon haxis
  obtain ⟨hby,hbb,hbc⟩ := residual_caps_of_room hBcap.1 hBcap.2.1 hBcap.2.2
  obtain ⟨U,hUB,hstop,hadapt⟩ := adaptive_factor_partition hp w gain Da 6975 133094
    (by decide +kernel) r hr adaptiveMem B
    (fun f hf => hprime f (hBF hf))
    (fun f hf g hg => hnon f (hBF hf) g (hBF hg))
    (fun f hf => haxis f (hBF hf))
    (fun f hf => (hfac f (hBF hf)).2.1)
  let room := (F\B).biUnion (regularSeeds embed modulus v A)
  let adaptive := (B\U).biUnion (regularSeeds embed modulus v A)
  let excluded := initialExceptional embed modulus v A P
  refine ⟨U,hUB.trans hBF,room,adaptive,excluded,?_,?_,?_,
    card_initialExceptional embed v A hinj P hP hpy hpb hpc,?_⟩
  · intro g hg
    rcases Finset.mem_union.mp (primary_seeds_cover embed modulus v A P hP primaryEval hg) with he | ha
    · exact Finset.mem_union_right _ he
    obtain ⟨f,hf,hgf⟩ := Finset.mem_biUnion.mp ha
    apply Finset.mem_union_left
    by_cases hB : f ∈ B
    · by_cases hU : f ∈ U
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨f,hU,hgf⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨f,Finset.mem_sdiff.mpr ⟨hB,hU⟩,hgf⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨f,Finset.mem_sdiff.mpr ⟨hf,hB⟩,hgf⟩))
  · have hs : F \ B ⊆ normalizedFactorSet P := fun f hf =>
      (hfac f (Finset.mem_sdiff.mp hf).1).1
    apply card_resolved_family embed modulus v A (F\B) primaryBox roomBox
      ((family_degree_bounds P hP _ hs 1).trans hpy)
      ((family_degree_bounds P hP _ hs 2).trans hpb)
      ((family_degree_bounds P hP _ hs 3).trans hpc) room_digit_lt_modulus
    · exact fun f hf => ⟨(hnorm f (Finset.mem_sdiff.mp hf).1).1,
        (hfac f (Finset.mem_sdiff.mp hf).1).2.1⟩
    · intro f hf
      obtain ⟨i,k,hk,hi,hdiv⟩ := hroom f hf
      have hmem := rectangle_partner_mem i hi k roomMem
      have hb := wall_of_mem_globalBox (by intro hz; apply hdiv; rw [hz]; exact dvd_zero _) hmem
      exact ⟨_,hdiv,hb.2.1,hb.2.2.1,hb.2.2.2,roomEval i hi k hk⟩
  · have hsum (i : Fin 4) :
        (∑ f ∈ B\U, f.degreeOf i) ≤ (∏ f ∈ B, f).degreeOf i :=
      (Finset.sum_le_sum_of_subset Finset.sdiff_subset).trans
        (sum_degree_eq_factorRectangle B i (fun f hf => (hprime f (hBF hf)).ne_zero)).le
    apply card_resolved_family embed modulus v A (B\U) remainingBox adaptiveBox
      ((hsum 1).trans hby) ((hsum 2).trans hbb) ((hsum 3).trans hbc) adaptive_digit_lt_modulus
    · exact fun f hf => ⟨(hnorm f (hBF (Finset.mem_sdiff.mp hf).1)).1,
        (hfac f (hBF (Finset.mem_sdiff.mp hf).1)).2.1⟩
    · intro f hf
      obtain ⟨a,i,j,hj,k,hk,hi,hdiv,hbox⟩ := hadapt f hf
      have hmem := rectangle_partner_mem i hi k hbox
      have hb := wall_of_mem_globalBox (by intro hz; apply hdiv; rw [hz]; exact dvd_zero _) hmem
      exact ⟨_,hdiv,hb.2.1,hb.2.2.1,hb.2.2.2,adaptiveEval a j hj hbox i hi k hk⟩
  · rcases hstop with he | hg
    · exact Or.inl he
    right
    have hUpos : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro hz
      rw [hz] at hg
      simp [factorRectangle,bandRectangle,bandFuel] at hg
      have hd := Nat.mul_pos hgain (by decide +kernel : 0 < adaptiveGap)
      omega)
    obtain ⟨f,hf⟩ := hUpos
    have hsum (i : Fin 4) :
        (∑ f ∈ U, f.degreeOf i) = (∏ f ∈ U, f).degreeOf i :=
      sum_degree_eq_factorRectangle U i (fun f hf => (hprime f (hBF (hUB hf))).ne_zero)
    have hsub (i : Fin 4) : (∏ f ∈ U, f).degreeOf i ≤ (∏ f ∈ B, f).degreeOf i :=
      (hsum i).ge.trans ((Finset.sum_le_sum_of_subset hUB).trans
        (sum_degree_eq_factorRectangle B i (fun f hf => (hprime f (hBF hf)).ne_zero)).le)
    refine ⟨?_,(hsub 1).trans hby,(hsub 2).trans hbb,(hsub 3).trans hbc,?_⟩
    · exact (hfac f (hBF (hUB hf))).2.1.trans_le
        ((Finset.single_le_sum (f := fun f : R => f.degreeOf 1) (fun _ _ => Nat.zero_le _) hf).trans (hsum 1).le)
    · exact Nat.le_of_mul_le_mul_left (adaptiveDim.trans hg) hgain

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

