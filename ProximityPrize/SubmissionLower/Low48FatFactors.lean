import ProximityPrize.SubmissionLower.Low48FatDefs

set_option Elab.async false
section
namespace Low48FatFactors
noncomputable section
open Polynomial K1 K1_13
open K1_13_4 (ResidueChart PhysicalRow GenericX GenericRow HasRank Source secondBox toGeneric)
open K1_13_4_4 (layerSpan)
open K1_13_4_4_1 (Exponent)
open Low48Fat (secondCut bankRank)
open scoped BigOperators
open private bank bankEval mem_bank K1_13_4_4_1.kernel_le boundary below_boundary independent_generic
  from ProximityPrize.SubmissionLower.Fast050
open private K1_13_4_4_1.endpoint from ProximityPrize.SubmissionLower.Fast074
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem telescope (w : I → K) (Γ : Finset K) (s : K → K[X]) (P : PoleData Γ s)
    (L : ResidueChart P) (hr : HasRank w P L secondBox secondCut bankRank) :
    ∃ r : ℕ → ℕ, bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t ∧
      ∀ t ≤ secondCut, ∃ e : Fin (r t) → GenericRow,
        LinearIndependent GenericX e ∧ ∀ i, e i ∈ layerSpan w P L t := by
  classical
  let r (t : ℕ) := Module.finrank Geom (bankEval w P L t).range
  refine ⟨r, ?_, fun t _ => ?_⟩
  · have hzero : (bankEval w P L 0).ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro F hz
      have hsrc := (mem_bank w P L _ _).mp F.property
      refine Subtype.ext (K1_13_4_4_1.endpoint Γ s P L F.val (fun m hm => ?_) hsrc.2.2.2)
      simpa only [Nat.zero_add] using below_boundary hsrc.2.1 hz m hm
    have hsum (t : ℕ) : Module.finrank Geom (bank w P L t) ≤
        ∑ v ∈ Finset.range (t + 1), r v := by
      induction t with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w P L 0) (V₂ := Exponent → Geom) (bankEval w P L 0)
        rw [hzero, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.ge
      | succ t ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w P L (t + 1)) (V₂ := Exponent → Geom) (bankEval w P L (t + 1))
        rw [Finset.sum_range_succ, ← h, add_comm]
        exact Nat.add_le_add (le_trans (K1_13_4_4_1.kernel_le w P L t) ih) le_rfl
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom
        (fun i => (⟨e i, (mem_bank w P L _ _).mpr (hmem i)⟩ : bank w P L secondCut)) :=
      LinearIndependent.of_comp (bank w P L secondCut).subtype he
    exact (by simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank :
      bankRank ≤ Module.finrank Geom (bank w P L secondCut)).trans (hsum secondCut)
  · let b := Module.finBasis Geom (bankEval w P L t).range
    choose e he using fun i : Fin (r t) => LinearMap.mem_range.mp (b i).property
    have hsrc (i : Fin (r t)) : Source w P L secondBox t (e i).val :=
      (mem_bank w P L _ _).mp (e i).property
    refine ⟨fun i => toGeneric (e i).val,
      independent_generic (fun i => (e i).val) (fun i => (hsrc i).2.1) ?_,
      fun i => Submodule.subset_span ⟨(e i).val, hsrc i, rfl⟩⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (bankEval w P L t).range.subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => boundary P.H.natDegree t (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end Low48FatFactors
end
section
namespace Low48FatFactors
noncomputable section
open K1_13_4 hiding mixedWeight secondCut
open K1_13_4_4 (FactorsFor factorProduct mixedHasse_zero toGeneric_caps topSlots cutoff_sum_le slot_constants)
open Low48Fat (mixedWeight secondCut bankRank)
open scoped Polynomial BigOperators
open private line line_zero line_toGeneric transverse pow_dvd_of_coeff positive_jet_degree
  from ProximityPrize.SubmissionLower.Fast076
def reserveCost (moving : Bool) : ℕ := if moving then 7098 else 48875
def layerPower (e t : ℕ) : ℕ := 1 + (secondCut - t) / e
private theorem choose_coordinate {moving : Bool} {A : Finset GenericRow}
    (hA : FactorsFor moving A) {F f : GenericRow} (hF : F ≠ 0) (hcap : Caps secondBox F)
    (hf : f ∈ A) (hd : f ∣ F) :
    ∃ i : SeedVar, (∀ n, mixedWeight (Finsupp.single i n) = n * reserveCost moving) ∧
      ¬ f ∣ (line i f).coeff 1 := by
  classical
  cases moving with
  | false =>
    obtain ⟨j, hj⟩ := positive_jet_degree (hA.jets f hf)
    have hjet : jetTotal f ≤ 6820 :=
      (MvPolynomial.weightedTotalDegree_le_of_dvd _ hd hF).trans hcap.1
    have hdeg : f.degreeOf (some j) ≤ jetTotal f :=
      MvPolynomial.degreeOf_le_weightedTotalDegree
        (fun i : SeedVar => i.elim 0 (fun _ => 1)) (some j) Nat.one_pos f
    refine ⟨some j, ?_, transverse hj (hdeg.trans_lt (hjet.trans_lt (by decide)))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]
  | true =>
    have hs : 0 < seedDegree f := hA.seed f hf
    have hdeg : seedDegree f ≤ 70000 := by
      simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
        (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hd hF).trans
          (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hcap.2.2.2)
    refine ⟨none, ?_, transverse hs (hdeg.trans_lt (by decide))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]
theorem factor_power (moving : Bool) (A : Finset GenericRow) (F : PhysicalRow) (t : ℕ)
    (hA : FactorsFor moving A) (hcap : Caps secondBox F) (ht : t ≤ secondCut)
    (htest : ∀ f ∈ A, ∀ a, t + mixedWeight a ≤ secondCut → f ∣ toGeneric (mixedHasse a F)) :
    factorProduct A ^ layerPower (reserveCost moving) t ∣ toGeneric F := by
  classical
  by_cases hF : toGeneric F = 0
  · rw [hF]
    exact dvd_zero _
  unfold factorProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro f hf g hg hfg
    refine IsRelPrime.pow ((hA.irreducible f hf).isRelPrime_iff_not_dvd.mpr ?_)
    intro hd
    exact hA.different hf hg hfg ((hA.irreducible f hf).associated_of_dvd (hA.irreducible g hg) hd)
  · intro f hf
    have hdiv : f ∣ toGeneric F := by
      simpa [mixedWeight, mixedHasse_zero] using htest f hf 0 (by simpa [mixedWeight] using ht)
    obtain ⟨i, hi, hsep⟩ := choose_coordinate hA hF (toGeneric_caps hcap) hf hdiv
    apply pow_dvd_of_coeff (line i) (line_zero i)
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hA.irreducible f hf)) hsep
    intro a ha
    rw [line_toGeneric]
    apply htest f hf
    rw [hi]
    have ha' : a ≤ (secondCut - t) / reserveCost moving := by
      unfold layerPower at ha
      omega
    have hm := (Nat.mul_le_mul_right (reserveCost moving) ha').trans
      (Nat.div_mul_le_self (secondCut - t) (reserveCost moving))
    omega
set_option maxRecDepth 1024
theorem factor_arithmetic :
    let T := 0x1de50d7332f37
    48875 * 6820 * T / bankRank = 121 ∧ 48875 * 2300 * T / bankRank = 40 ∧
      7098 * 6820 * T / bankRank = 17 ∧ 7098 * 2300 * T / bankRank = 5 ∧
      7098 * 70000 * T / bankRank = 180 := by decide
theorem resource_bound {e V d : ℕ} (he : 0 < e) (r : ℕ → ℕ)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hcap : ∀ t ≤ secondCut, r t ≤ topSlots 0)
    (hspend : ∀ t ≤ secondCut, r t ≠ 0 → layerPower e t * d ≤ V) :
    d ≤ e * V * topSlots 0 / bankRank := by
  by_cases hd : d = 0
  · simp [hd]
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  let q (k : ℕ) := if k < V / d then topSlots 0 else 0
  have hb := cutoff_sum_le (W := secondCut) (n := V / d) he r q
    (fun t ht => by
      by_cases hn : r t = 0
      · simp [hn]
      have hle := (Nat.le_div_iff_mul_le hd').mpr (hspend t ht hn)
      have hlt : (secondCut - t) / e < V / d := by
        unfold layerPower at hle
        omega
      simpa [q, hlt] using hcap t ht)
    (fun k hk => ite_eq_right (Nat.not_lt.mpr hk))
  have hc : (∑ k ∈ Finset.range (V / d), q k) = (V / d) * topSlots 0 := by
    have hsum : (∑ k ∈ Finset.range (V / d), q k) =
        ∑ _ ∈ Finset.range (V / d), topSlots 0 :=
      Finset.sum_congr rfl fun k hk => ite_eq_left (Finset.mem_range.mp hk)
    rw [hsum]
    simp
  rw [hc] at hb
  apply (Nat.le_div_iff_mul_le (by decide : 0 < bankRank)).mpr
  calc
    d * bankRank ≤ d * (e * (V / d * topSlots 0)) :=
      Nat.mul_le_mul_left d (hr.trans hb)
    _ = (e * topSlots 0) * (V / d * d) := by ring
    _ ≤ (e * topSlots 0) * V := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = e * V * topSlots 0 := by ring
theorem top_exclusion (r : ℕ → ℕ)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (h : ∀ t ≤ secondCut, r t ≤ topSlots (layerPower 7098 t)) : False := by
  have hb := cutoff_sum_le (W := secondCut) (n := 1150) (by decide : 0 < 7098)
    r (fun k => topSlots (1 + k)) h (fun k hk => by
      have hk' : 1151 - (1 + k) = 0 := by omega
      simp [topSlots, hk'])
  have hs := congrArg (fun n : ℕ => n / 7800) slot_constants.2
  change 7800 * (∑ k ∈ Finset.range 1150, topSlots (1 + k)) / 7800 =
    0x5535180af365254238 / 7800 at hs
  rw [Nat.mul_div_cancel_left _ (by decide : 0 < 7800)] at hs
  rw [hs] at hb
  exact (not_le_of_gt (by decide : 7098 * (0x5535180af365254238 / 7800) < bankRank)) (hr.trans hb)
end
end Low48FatFactors
end
section
namespace Low48FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (layerSpan FactorsFor factorProduct topSlots slot_constants rowMap
  capSpace mem_capSpace mixedHasse_zero toGeneric_ne_zero toGeneric_caps mixedHasse_caps layerSpan_caps)
open Low48Fat (Necessary mixedWeight secondCut bankRank)
open scoped BigOperators
open private multiples mem_multiples count_layer weighted_pow from ProximityPrize.SubmissionLower.Fast050
set_option maxRecDepth 1024
private theorem has_nonzero_necessary {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} (hr : HasRank w P L secondBox secondCut bankRank) :
    ∃ G : Necessary w P L, G ≠ 0 := by
  obtain ⟨e, he, hs⟩ := hr
  let i : Fin bankRank := ⟨0, by decide⟩
  have hmem : e i ∈ Necessary w P L := by
    apply Submodule.subset_span
    exact ⟨secondCut, e i, 0, hs i, by simp [mixedWeight], (mixedHasse_zero _).symm⟩
  refine ⟨⟨e i, hmem⟩, fun h => he.ne_zero i ?_⟩
  exact congrArg (fun Q : Necessary w P L => Q.val) h
private theorem necessary_caps {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {Q : PhysicalRow} (hQ : Q ∈ Necessary w P L) :
    Caps secondBox (toGeneric Q) := by
  have hle : Necessary w P L ≤ ((capSpace secondBox).restrictScalars Geom).comap rowMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, F, a, hF, _, rfl⟩
    exact mem_capSpace.mpr (toGeneric_caps (mixedHasse_caps a F hF.1))
  exact mem_capSpace.mp (hle hQ)
private theorem select_row {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {F : PhysicalRow} (hF : F ≠ 0) (hr : HasRank w P L secondBox secondCut bankRank) :
    ∃ G, G ∈ Necessary w P L ∧ G ≠ 0 ∧
      ∀ f : GenericRow, Irreducible f → f ∣ toGeneric F → f ∣ toGeneric G →
        ∀ Q ∈ Necessary w P L, f ∣ toGeneric Q := by
  classical
  let N := Necessary w P L
  let _ : StrongNormalizationMonoid GenericRow :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let bad := (UniqueFactorizationMonoid.normalizedFactors (toGeneric F)).toFinset.filter
    (fun f => ∃ Q ∈ N, ¬ f ∣ toGeneric Q)
  let sub : Option ↥bad → Submodule Geom N
    | none => ⊥
    | some f => ((multiples f.val).restrictScalars Geom).comap (rowMap.comp N.subtype)
  have hproper (i : Option ↥bad) : sub i ≠ ⊤ := by
    cases i with
    | none =>
      obtain ⟨Q, hQ⟩ := has_nonzero_necessary hr
      intro h
      have hm : Q ∈ sub none := h ▸ Submodule.mem_top
      exact hQ ((Submodule.mem_bot Geom).mp hm)
    | some f =>
      obtain ⟨Q, hQ, hnd⟩ := (Finset.mem_filter.mp f.property).2
      intro h
      have hm : (⟨Q, hQ⟩ : N) ∈ sub (some f) := h ▸ Submodule.mem_top
      exact hnd (mem_multiples.mp hm)
  obtain ⟨G, hG⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := Option ↥bad) (K := Geom) (M := N) sub hproper
  refine ⟨G.val, G.property, ?_, fun f hf hdf hdg Q hQ => ?_⟩
  · intro h
    exact hG none ((Submodule.mem_bot Geom).mpr (Subtype.ext h))
  · by_contra hn
    obtain ⟨p, hp, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd (toGeneric_ne_zero hF) hf hdf
    have hp' : p ∈ bad := Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hp, Q, hQ, fun h => hn (hassoc.dvd_iff_dvd_left.mpr h)⟩
    exact hG (some ⟨p, hp'⟩) (mem_multiples.mpr (hassoc.dvd_iff_dvd_left.mp hdg))
private theorem layer_divides {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {moving : Bool} {A : Finset GenericRow} (hA : FactorsFor moving A)
    (hcommon : ∀ f ∈ A, ∀ Q ∈ Necessary w P L, f ∣ toGeneric Q)
    {t : ℕ} (ht : t ≤ secondCut) :
    layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower (reserveCost moving) t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨F, hF, rfl⟩
  apply mem_multiples.mpr (factor_power moving A F t hA hF.1 ht ?_)
  intro f hf a ha
  exact hcommon f hf _ (Submodule.subset_span ⟨t, F, a, hF, ha, rfl⟩)
private theorem product_ne_zero {moving : Bool} {A : Finset GenericRow} (hA : FactorsFor moving A) :
    factorProduct A ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun f hf => (hA.irreducible f hf).ne_zero
private theorem weighted_resource {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {e : ℕ} (he : 0 < e) {r : ℕ → ℕ} {D : GenericRow} (hD : D ≠ 0)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow, LinearIndependent GenericX u ∧
      ∀ i, u i ∈ layerSpan w P L t)
    (hcount : ∀ t ≤ secondCut, r t ≤ topSlots 0)
    (hdvd : ∀ t ≤ secondCut, layerSpan w P L t ≤ multiples (D ^ layerPower e t))
    (v : SeedVar → ℕ) (V : ℕ)
    (hcap : ∀ R : GenericRow, Caps secondBox R → R.weightedTotalDegree v ≤ V) :
    D.weightedTotalDegree v ≤ e * V * topSlots 0 / bankRank := by
  apply resource_bound he r hr hcount
  intro t ht hne
  obtain ⟨u, hu, hs⟩ := hb t ht
  let i : Fin (r t) := ⟨0, Nat.pos_of_ne_zero hne⟩
  have hm := MvPolynomial.weightedTotalDegree_le_of_dvd v
    (mem_multiples.mp (hdvd t ht (hs i))) (hu.ne_zero i)
  rw [weighted_pow _ _ hD] at hm
  exact hm.trans (hcap (u i) (layerSpan_caps (hs i)))
private theorem excludes_top {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {r : ℕ → ℕ} {A : Finset GenericRow} (hA : FactorsFor true A)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow,
      LinearIndependent GenericX u ∧ ∀ i, u i ∈ layerSpan w P L t)
    (hdvd : ∀ t ≤ secondCut,
      layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower 7098 t)) :
    ∀ f ∈ A, f.degreeOf (some 2) = 0 := by
  classical
  let v : SeedVar → ℕ := Pi.single (some 2) 1
  have hzero : (factorProduct A).weightedTotalDegree v = 0 := by
    by_contra hn
    apply top_exclusion r hr
    intro t ht
    apply count_layer (hb t ht)
    intro R hR hRne
    have h := MvPolynomial.weightedTotalDegree_le_of_dvd v
      (mem_multiples.mp (hdvd t ht hR)) hRne
    rw [weighted_pow _ _ (product_ne_zero hA)] at h
    have hle := Nat.mul_le_mul_left (layerPower 7098 t) (Nat.pos_of_ne_zero hn)
    rw [Nat.mul_one] at hle
    simpa only [v, MvPolynomial.weightedTotalDegree_piSingle] using hle.trans h
  intro f hf
  have hfd : f ∣ factorProduct A := Finset.dvd_prod_of_mem id hf
  have h := (MvPolynomial.weightedTotalDegree_le_of_dvd v hfd (product_ne_zero hA)).trans_eq hzero
  simpa only [v, MvPolynomial.weightedTotalDegree_piSingle, Nat.le_zero] using h
theorem proof : Low48Fat.c2 := by
  classical
  intro w Γ s P L F hF hFCaps hRank
  obtain ⟨r, hr, hb⟩ := telescope w Γ s P L hRank
  have hcount : ∀ t ≤ secondCut, r t ≤ topSlots 0 := fun t ht =>
    count_layer (hb t ht) (fun _ _ _ => Nat.zero_le _)
  obtain ⟨G, hG, hGne, hchoose⟩ := select_row hF hRank
  have hdiv (moving : Bool) (A : Finset GenericRow) (hA : FactorsFor moving A)
      (hcomm : ∀ f ∈ A, f ∣ toGeneric F ∧ f ∣ toGeneric G) :
      ∀ t ≤ secondCut, layerSpan w P L t ≤
        multiples (factorProduct A ^ layerPower (reserveCost moving) t) :=
    fun _ ht => layer_divides hA
      (fun f hf => hchoose f (hA.irreducible f hf) (hcomm f hf).1 (hcomm f hf).2) ht
  have hbound (moving : Bool) (A : Finset GenericRow) (hA : FactorsFor moving A)
      (hcomm : ∀ f ∈ A, f ∣ toGeneric F ∧ f ∣ toGeneric G)
      (v : SeedVar → ℕ) (V : ℕ)
      (hc : ∀ R : GenericRow, Caps secondBox R → R.weightedTotalDegree v ≤ V) :
      (factorProduct A).weightedTotalDegree v ≤ reserveCost moving * V * topSlots 0 / bankRank :=
    weighted_resource (by cases moving <;> decide) (product_ne_zero hA) hr hb hcount
      (hdiv moving A hA hcomm) v V hc
  have hbcap (R : GenericRow) (h : Caps secondBox R) : jetTotal R ≤ 6820 := h.1
  have hjcap (R : GenericRow) (h : Caps secondBox R) : jetIndex R ≤ 2300 := h.2.1
  have hscap (R : GenericRow) (h : Caps secondBox R) :
      R.weightedTotalDegree (Pi.single (none : SeedVar) 1) ≤ 70000 := by
    rw [MvPolynomial.weightedTotalDegree_piSingle]
    exact h.2.2.2
  obtain ⟨bF, jF, bM, jM, sM⟩ := factor_arithmetic
  refine ⟨G, hG, P3_6_4_2.factor_pair _ _ (toGeneric_ne_zero hF) (toGeneric_ne_zero hGne)
    (toGeneric_caps hFCaps) (necessary_caps hG) ?_ ?_⟩
  · intro A hA hcomm
    have hbt := hbound false A hA hcomm _ _ hbcap
    have hji := hbound false A hA hcomm _ _ hjcap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    have hbt' : jetTotal (factorProduct A) ≤ 125 := by
      simp only [reserveCost, Bool.false_eq_true, ite_false, slot_constants.1, bF] at hbt
      exact hbt.trans (by decide)
    have hji' : jetIndex (factorProduct A) ≤ 42 := by
      simp only [reserveCost, Bool.false_eq_true, ite_false, slot_constants.1, jF] at hji
      exact hji.trans (by decide)
    exact ⟨hbt', hji'⟩
  · intro A hA hcomm
    have hbt := hbound true A hA hcomm _ _ hbcap
    have hji := hbound true A hA hcomm _ _ hjcap
    have hse := hbound true A hA hcomm _ _ hscap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    rw [MvPolynomial.weightedTotalDegree_piSingle] at hse
    have hbt' : jetTotal (factorProduct A) ≤ 17 := by
      simpa only [reserveCost, ite_true, slot_constants.1, bM] using hbt
    have hji' : jetIndex (factorProduct A) ≤ 5 := by
      simpa only [reserveCost, ite_true, slot_constants.1, jM] using hji
    have hse' : seedDegree (factorProduct A) ≤ 180 := by
      simpa only [seedDegree, reserveCost, ite_true, slot_constants.1, sM] using hse
    exact ⟨hbt', hji', hse', excludes_top hA hr hb (hdiv true A hA hcomm)⟩
end
end Low48FatFactors
end

#print axioms Low48FatFactors.proof
