import ProximityPrize.SubmissionLower.R6960Low6960FatBanks

-- merged module R6960Low6960FatSlots
section Merged_R6960Low6960FatSlots

set_option Elab.async false
/-! Low-specific copies of the seed-cap dependent slot count of `Fast050` (K1_13_4_4),
at seed degree at most 27,000, i.e. 27,001 seed slots. -/
section
namespace Low6960FatSlots
noncomputable section
open K1 K1_13 K1_13_4
open K1_13_4_4 (capSpace mem_capSpace toGeneric_caps toGeneric_injective)
open Low6960Fat (Caps27 Source27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 1024
open K1_13_4_4 (Exponent slotExponent sum_value_choices sum_index_choices sum_odds rank_le_coeffs sum_squares)
def topSlots (a : ℕ) : ℕ := 27001 * 5671 * (1151 - a)^2
def capSpace27 (a : Shape) : Submodule GenericX GenericRow :=
  capSpace a ⊓
  MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) 27000
theorem mem_capSpace27 {a : Shape} {F : GenericRow} : F ∈ capSpace27 a ↔ Caps27 a F := by
  classical
  simp only [capSpace27, Submodule.mem_inf, mem_capSpace,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, Caps27, Low6960Fat.seedCap, seedDegree]
theorem seedDegree_toGeneric (F : PhysicalRow) : seedDegree (toGeneric F) = seedDegree F := by
  have hs : (toGeneric F).support = F.support :=
    MvPolynomial.support_map_of_injective F (IsFractionRing.injective (Polynomial Geom) GenericX)
  simp only [seedDegree, MvPolynomial.degreeOf_eq_sup, hs]
theorem toGeneric_caps27 {a : Shape} {F : PhysicalRow} (h : Caps27 a F) :
    Caps27 a (toGeneric F) :=
  ⟨toGeneric_caps h.1, by rw [seedDegree_toGeneric]; exact h.2⟩
def layerSpan {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) : Submodule GenericX GenericRow :=
  Submodule.span GenericX {R | ∃ F, Source27 w P L secondBox t F ∧ toGeneric F = R}
theorem layerSpan_caps {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {t : ℕ} {F : GenericRow} (hF : F ∈ layerSpan w P L t) : Caps27 secondBox F := by
  apply mem_capSpace27.mp
  apply (Submodule.span_le.mpr ?_) hF
  rintro _ ⟨Q, hQ, rfl⟩
  exact mem_capSpace27.mpr (toGeneric_caps27 ⟨hQ.1.1, hQ.2⟩)
private def slotTuples (a : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Ico a 1151).biUnion (fun k =>
    (Finset.range (2301 - 2*k)).biUnion (fun j =>
      (Finset.range (6821 - k - j)).biUnion (fun i =>
        (Finset.range 27001).image (fun z => (k, j, i, z)))))
private theorem tuples_card (a : ℕ) : (slotTuples a).card ≤ topSlots a := by
  unfold slotTuples
  calc
    _ ≤ ∑ k ∈ Finset.Ico a 1151, ∑ j ∈ Finset.range (2301 - 2*k),
        ∑ _ ∈ Finset.range (6821 - k - j), 27001 := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
      exact Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = topSlots a := by
      unfold topSlots
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      calc
        _ = ∑ k ∈ Finset.Ico a 1151, (27001 * 5671) * (2301 - 2*k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ 1150 := by have h := (Finset.mem_Ico.mp hk).2; omega
          rw [← Finset.sum_mul, sum_value_choices hk']
          ring
        _ = _ := by rw [← Finset.mul_sum, sum_index_choices]
private theorem exponent_mem {a : ℕ} {R : GenericRow} (hR : Caps27 secondBox R)
    {m : Exponent} (hm : m ∈ R.support) (ha : a ≤ m (some 2)) :
    m ∈ (slotTuples a).image slotExponent := by
  classical
  have ht := (MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 (fun _ => 1)) hm).trans hR.1.1
  have hj := (MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 Fin.val) hm).trans hR.1.2.1
  have hz := (MvPolynomial.le_degreeOf_of_mem_support (none : SeedVar) hm).trans hR.2
  have hk := (MvPolynomial.le_degreeOf_of_mem_support (some 2 : SeedVar) hm).trans hR.1.2.2.1
  have htotal : m (some 0) + m (some 1) + m (some 2) ≤ 6820 := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, secondBox, Nat.add_assoc] using ht
  have hindex : m (some 1) + 2 * m (some 2) ≤ 2300 := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, secondBox, Nat.mul_comm] using hj
  change m (some 2) ≤ 1150 at hk
  change m none ≤ 27000 at hz
  refine Finset.mem_image.mpr ⟨(m (some 2), m (some 1), m (some 0), m none), ?_, ?_⟩
  · simp only [slotTuples, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_range,
      Finset.mem_image]
    exact ⟨m (some 2), ⟨ha, by omega⟩, m (some 1), by omega, m (some 0), by omega,
      m none, by omega, rfl⟩
  · ext i
    cases i with
    | none => simp [slotExponent]
    | some i => fin_cases i <;> simp [slotExponent]
theorem count_symbols (a r : ℕ) (e : Fin r → GenericRow) (he : LinearIndependent GenericX e)
    (h : ∀ R ∈ Submodule.span GenericX (Set.range e),
      Caps27 secondBox R ∧ (R ≠ 0 → a ≤ R.degreeOf (some 2))) :
    r ≤ topSlots a := by
  have hc := rank_le_coeffs ((slotTuples a).image slotExponent) e he (by
    intro R hR hn
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup R.support
      (MvPolynomial.support_nonempty.mpr hn) (fun u => u (some 2))
    have hdeg := (h R hR).2 hn
    rw [MvPolynomial.degreeOf_eq_sup, hmax] at hdeg
    exact ⟨m, exponent_mem (h R hR).1 hm hdeg, MvPolynomial.mem_support_iff.mp hm⟩)
  exact hc.trans (Finset.card_image_le.trans (tuples_card a))
theorem count_layer {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {a r t : ℕ}
    (hb : ∃ e : Fin r → GenericRow, LinearIndependent GenericX e ∧
      ∀ i, e i ∈ layerSpan w P L t)
    (hdeg : ∀ R ∈ layerSpan w P L t, R ≠ 0 → a ≤ R.degreeOf (some 2)) :
    r ≤ topSlots a := by
  obtain ⟨e, he, hs⟩ := hb
  have hspan : Submodule.span GenericX (Set.range e) ≤ layerSpan w P L t :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hs i)
  exact count_symbols a r e he (fun R hR => ⟨layerSpan_caps (hspan hR), hdeg R (hspan hR)⟩)
theorem slot_zero : topSlots 0 = 202857067663471 := by decide
theorem slot_sum : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) = 77728095800419025 := by
  have hs : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) =
      (27001 * 5671) * ∑ k ∈ Finset.range 1150, (1150 - k)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hk : 1151 - (1 + k) = 1150 - k := by omega
    rw [topSlots, hk]
  rw [hs]
  have hsquare : (∑ k ∈ Finset.range 1150, (1150 - k)^2) = 507619775 := by
    have h := sum_squares 1150
    omega
  rw [hsquare]
end
end Low6960FatSlots
end

end Merged_R6960Low6960FatSlots

-- merged module R6960Low6960FatFactors
section Merged_R6960Low6960FatFactors

set_option Elab.async false
section
namespace Low6960FatFactors
noncomputable section
open Polynomial K1 K1_13
open K1_13_4 (ResidueChart PhysicalRow GenericX GenericRow HasRank Source secondBox toGeneric)
open K1_13_4_4_1 (Exponent polePower weight)
open K1_13_4 (SeedVar seedDegree)
open Low6960Fat (secondCut bankRank)
open scoped BigOperators
open K1_13_4_4_1 (bank bankEval mem_bank kernel_le boundary below_boundary independent_generic)
open K1_13_4_4_1 (endpoint)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def seedSpace : Submodule Geom PhysicalRow :=
  (MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) 27000).restrictScalars Geom
theorem mem_seedSpace {F : PhysicalRow} : F ∈ seedSpace ↔ seedDegree F ≤ 27000 := by
  simp only [seedSpace, Submodule.restrictScalars_mem,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, seedDegree]
private def bank27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Submodule Geom PhysicalRow := bank w P L t ⊓ seedSpace
private theorem mem_bank27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) (F : PhysicalRow) : F ∈ bank27 w P L t ↔ Low6960Fat.Source27 w P L secondBox t F := by
  rw [bank27, Submodule.mem_inf, mem_bank, mem_seedSpace]
  rfl
private instance finite27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Module.Finite Geom (bank27 w P L t) :=
  Submodule.finiteDimensional_of_le (inf_le_left : bank27 w P L t ≤ bank w P L t)
private def bankEval27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    bank27 w P L t →ₗ[Geom] (K1_13_4_4_1.Exponent → Geom) :=
  (boundary P.H.natDegree t).comp (bank27 w P L t).subtype
private theorem kernel_le27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Module.finrank Geom (bankEval27 w P L (t + 1)).ker ≤
      Module.finrank Geom (bank27 w P L t) := by
  let f := (bank27 w P L (t + 1)).subtype.comp (bankEval27 w P L (t + 1)).ker.subtype
  have hm (F : (bankEval27 w P L (t + 1)).ker) : f F ∈ bank27 w P L t := by
    obtain ⟨⟨hc, hcut, hphys, hpole⟩, hseed⟩ := (mem_bank27 w P L _ _).mp F.val.property
    have hz : boundary P.H.natDegree (t + 1) F.val.val = 0 := LinearMap.mem_ker.mp F.property
    apply (mem_bank27 w P L _ _).mpr
    refine ⟨⟨hc, fun m hm => ?_, hphys, hpole⟩, hseed⟩
    have h := below_boundary hcut hz m hm
    change ((F.val.val).coeff m).natDegree + weight P.H.natDegree m ≤ t + polePower * P.H.natDegree
    omega
  apply LinearMap.finrank_le_finrank_of_injective (f := f.codRestrict _ hm)
  intro F G he
  have heq := congrArg (fun Q : bank27 w P L t => Q.val) he
  exact Subtype.ext (Subtype.ext heq)
theorem telescope (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) (P : PoleData Γ s)
    (L : ResidueChart P) (hr : Low6960Fat.HasRank27 w P L secondBox secondCut bankRank) :
    ∃ r : ℕ → ℕ, bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t ∧
      ∀ t ≤ secondCut, ∃ e : Fin (r t) → GenericRow,
        LinearIndependent GenericX e ∧ ∀ i, e i ∈ Low6960FatSlots.layerSpan w P L t := by
  classical
  let r (t : ℕ) := Module.finrank Geom (bankEval27 w P L t).range
  refine ⟨r, ?_, fun t _ => ?_⟩
  · have hzero : (bankEval27 w P L 0).ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro F hz
      have hsrc := ((mem_bank27 w P L _ _).mp F.property).1
      refine Subtype.ext (K1_13_4_4_1.endpoint Γ s P L F.val (fun m hm => ?_) hsrc.2.2.2)
      simpa only [Nat.zero_add] using below_boundary hsrc.2.1 hz m hm
    have hsum (t : ℕ) : Module.finrank Geom (bank27 w P L t) ≤
        ∑ v ∈ Finset.range (t + 1), r v := by
      induction t with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank27 w P L 0) (V₂ := Exponent → Geom) (bankEval27 w P L 0)
        rw [hzero, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.ge
      | succ t ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank27 w P L (t + 1)) (V₂ := Exponent → Geom) (bankEval27 w P L (t + 1))
        rw [Finset.sum_range_succ, ← h, add_comm]
        exact Nat.add_le_add (le_trans (kernel_le27 w P L t) ih) le_rfl
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom
        (fun i => (⟨e i, (mem_bank27 w P L _ _).mpr (hmem i)⟩ : bank27 w P L secondCut)) :=
      LinearIndependent.of_comp (bank27 w P L secondCut).subtype he
    exact (by simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank :
      bankRank ≤ Module.finrank Geom (bank27 w P L secondCut)).trans (hsum secondCut)
  · let b := Module.finBasis Geom (bankEval27 w P L t).range
    choose e he using fun i : Fin (r t) => LinearMap.mem_range.mp (b i).property
    have hsrc (i : Fin (r t)) : Low6960Fat.Source27 w P L secondBox t (e i).val :=
      (mem_bank27 w P L _ _).mp (e i).property
    refine ⟨fun i => toGeneric (e i).val,
      independent_generic (fun i => (e i).val) (fun i => (hsrc i).1.2.1) ?_,
      fun i => Submodule.subset_span ⟨(e i).val, hsrc i, rfl⟩⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (bankEval27 w P L t).range.subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => boundary P.H.natDegree t (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end Low6960FatFactors
end
section
namespace Low6960FatFactors
noncomputable section
open K1_13_4 hiding mixedWeight secondCut
open K1_13_4_4 (FactorsFor factorProduct mixedHasse_zero toGeneric_caps cutoff_sum_le)
open Low6960FatSlots (topSlots)
open Low6960Fat (mixedWeight secondCut bankRank)
open scoped Polynomial BigOperators
open K1_13_4_4_2 (line line_zero line_toGeneric transverse pow_dvd_of_coeff positive_jet_degree)
def reserveCost (moving : Bool) : ℕ := if moving then 7134 else 48739
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
    let T := 202857067663471
    48739 * 6820 * T / bankRank = 121 ∧ 48739 * 2300 * T / bankRank = 40 ∧
      7134 * 6820 * T / bankRank = 17 ∧ 7134 * 2300 * T / bankRank = 5 ∧
      7134 * 27000 * T / bankRank = 70 := by decide
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
    (h : ∀ t ≤ secondCut, r t ≤ topSlots (layerPower 7134 t)) : False := by
  have hb := cutoff_sum_le (W := secondCut) (n := 1150) (by decide : 0 < 7134)
    r (fun k => topSlots (1 + k)) h (fun k hk => by
      have hk' : 1151 - (1 + k) = 0 := by omega
      simp [topSlots, hk'])
  rw [Low6960FatSlots.slot_sum] at hb
  exact (not_le_of_gt (by decide : 7134 * 77728095800419025 < bankRank)) (hr.trans hb)
end
end Low6960FatFactors
end
section
namespace Low6960FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (FactorsFor factorProduct)
open Low6960Fat (CommonPair Caps27)
open scoped Polynomial BigOperators
open K1_13_4_4 (pureEval pureEval_section pure_degree_le caps_of_dvd)
private theorem seed_of_dvd {F Q : GenericRow} (hF : F ≠ 0) (hs : seedDegree F ≤ 27000)
    (hQ : Q ∣ F) : seedDegree Q ≤ 27000 := by
  simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
    (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hQ hF).trans
      (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hs)
theorem factor_pair27
    (F G : GenericRow) (hF : F ≠ 0) (hG : G ≠ 0)
    (hFCap : Caps27 firstBox F) (hGCap : Caps27 secondBox G)
    (hfixed : ∀ A, FactorsFor false A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 121 ∧ jetIndex (factorProduct A) ≤ 40)
    (hmoving : ∀ A, FactorsFor true A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 17 ∧ jetIndex (factorProduct A) ≤ 5 ∧
      seedDegree (factorProduct A) ≤ 70 ∧ ∀ f ∈ A, f.degreeOf (some 2) = 0) :
    Nonempty (CommonPair F G) := by
  classical
  let _ : StrongNormalizationMonoid GenericRow :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : GCDMonoid GenericRow := UniqueFactorizationMonoid.toGCDMonoid GenericRow
  let g := gcd F G
  have hg : g ≠ 0 := gcd_ne_zero_of_left hF
  let N := UniqueFactorizationMonoid.normalizedFactors g
  let A := N.toFinset
  let pureFactors := A.filter (fun f => jetTotal f = 0)
  let jetFactors := A.filter (fun f => ¬ jetTotal f = 0)
  let fixed := jetFactors.filter (fun f => seedDegree f = 0)
  let moving := jetFactors.filter (fun f => ¬ seedDegree f = 0)
  let powCount : GenericRow → ℕ := N.count
  let pure : (Polynomial GenericX) := ∏ f ∈ pureFactors, (pureEval f) ^ powCount f
  have hpure : pureSeed pure = ∏ f ∈ pureFactors, f ^ powCount f := by
    let φ : (Polynomial GenericX) →+* GenericRow :=
      Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none)
    change φ (∏ f ∈ pureFactors, (pureEval f) ^ powCount f) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun f hf => ?_
    rw [map_pow]
    exact congrArg (fun R => R ^ powCount f)
      (pureEval_section (Finset.mem_filter.mp hf).2)
  let D := pureSeed pure * (∏ f ∈ fixed, f ^ powCount f) * (∏ f ∈ moving, f ^ powCount f)
  have hD : Associated D g := by
    suffices D = N.prod by
      rw [this]
      exact UniqueFactorizationMonoid.prod_normalizedFactors hg
    change pureSeed pure * (∏ f ∈ fixed, f ^ powCount f) *
      (∏ f ∈ moving, f ^ powCount f) = _
    rw [hpure, mul_assoc]
    unfold fixed moving
    rw [Finset.prod_filter_mul_prod_filter_not]
    unfold pureFactors jetFactors
    rw [Finset.prod_filter_mul_prod_filter_not]
    exact (Finset.prod_multiset_count N).symm
  have hDne : D ≠ 0 := ne_zero_of_dvd_ne_zero hg hD.dvd
  have hDF : D ∣ F := hD.dvd.trans (gcd_dvd_left F G)
  have hDG : D ∣ G := hD.dvd.trans (gcd_dvd_right F G)
  obtain ⟨F', hF'⟩ := hDF
  obtain ⟨G', hG'⟩ := hDG
  have hl : F' ≠ 0 := right_ne_zero_of_mul (hF' ▸ hF)
  have hr : G' ≠ 0 := right_ne_zero_of_mul (hG' ▸ hG)
  have hrel : IsRelPrime F' G' := by
    intro d hdF hdG
    have hdF' : D * d ∣ F := hF' ▸ mul_dvd_mul_left D hdF
    have hdG' : D * d ∣ G := hG' ▸ mul_dvd_mul_left D hdG
    have hd := (dvd_gcd hdF' hdG').trans hD.symm.dvd
    apply isUnit_of_dvd_one
    exact (mul_dvd_mul_iff_left hDne).mp (by simpa only [mul_one] using hd)
  have hcommon (f : GenericRow) (hf : f ∈ A) : f ∣ F ∧ f ∣ G := by
    have hfg : f ∣ g := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hf)
    exact ⟨hfg.trans (gcd_dvd_left F G), hfg.trans (gcd_dvd_right F G)⟩
  have hmake (b : Bool) (B : Finset GenericRow) (hBA : B ⊆ A)
      (hj : ∀ f ∈ B, 0 < jetTotal f)
      (hs : ∀ f ∈ B, if b then 0 < seedDegree f else seedDegree f = 0) :
      FactorsFor b B := by
    refine ⟨?_, ?_, hj, hs⟩
    · intro f hf q hq hne hassoc
      exact hne (UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
        (Multiset.mem_toFinset.mp (hBA hf)) (Multiset.mem_toFinset.mp (hBA hq)) hassoc)
    · intro f hf
      exact UniqueFactorizationMonoid.irreducible_of_normalized_factor _
        (Multiset.mem_toFinset.mp (hBA hf))
  have hfixedA : fixed ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmovingA : moving ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hfix := hmake false fixed hfixedA
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf => (Finset.mem_filter.mp hf).2)
  have hmov := hmake true moving hmovingA
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp hf).2)
  obtain ⟨hft, hfi⟩ := hfixed fixed hfix (fun f hf => hcommon f (hfixedA hf))
  obtain ⟨hmt, hmi, hms, hlow⟩ := hmoving moving hmov (fun f hf => hcommon f (hmovingA hf))
  have hpureF : pureSeed pure ∣ F :=
    (show pureSeed pure ∣ D by
      exact ⟨_, mul_assoc _ _ _⟩).trans ⟨F', hF'⟩
  have hpure_ne : pure ≠ 0 := by
    intro hz
    apply hDne
    simp [D, hz, pureSeed]
  refine ⟨{
    fixed := fixed
    moving := moving
    pure := pure
    exponent := powCount
    left := F'
    right := G'
    pure_ne := hpure_ne
    pure_degree := (pure_degree_le hF hpureF).trans (hFCap.2.trans (by decide))
    fixed_kind := fun f hf => ⟨hfix.irreducible f hf, hfix.jets f hf, hfix.seed f hf⟩
    moving_kind := fun f hf => ⟨hmov.irreducible f hf, hmov.jets f hf, hmov.seed f hf, hlow f hf⟩
    fixed_total := hft
    fixed_index := hfi
    moving_total := hmt
    moving_index := hmi
    moving_seed := hms
    left_eq := hF'
    right_eq := hG'
    left_ne := hl
    right_ne := hr
    proper := hrel
    left_caps := ⟨caps_of_dvd hF hFCap.1 ⟨D, hF'.trans (mul_comm _ _)⟩, seed_of_dvd hF hFCap.2 ⟨D, hF'.trans (mul_comm _ _)⟩⟩
    right_caps := ⟨caps_of_dvd hG hGCap.1 ⟨D, hG'.trans (mul_comm _ _)⟩, seed_of_dvd hG hGCap.2 ⟨D, hG'.trans (mul_comm _ _)⟩⟩
  }⟩
end
end Low6960FatFactors
end
section
namespace Low6960FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (FactorsFor factorProduct rowMap
  capSpace mem_capSpace mixedHasse_zero toGeneric_ne_zero toGeneric_caps mixedHasse_caps)
open Low6960FatSlots (topSlots layerSpan layerSpan_caps count_layer capSpace27 mem_capSpace27
  toGeneric_caps27)
open Low6960Fat (Caps27 HasRank27)
open Low6960Fat (Necessary mixedWeight secondCut bankRank)
open scoped BigOperators
open K1_13_4_4 (multiples mem_multiples weighted_pow)
set_option maxRecDepth 1024
private theorem mixedHasse_seed27 (a : SeedVar →₀ ℕ) (F : PhysicalRow)
    (hs : seedDegree F ≤ 27000) : seedDegree (mixedHasse a F) ≤ 27000 := by
  classical
  simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
    (K1_13_4_4.mixedHasse_weightedDegree_le (Pi.single (none : SeedVar) 1) a F).trans
      (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hs)
private theorem has_nonzero_necessary {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} (hr : HasRank27 w P L secondBox secondCut bankRank) :
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
    Caps27 secondBox (toGeneric Q) := by
  have hle : Necessary w P L ≤ ((capSpace27 secondBox).restrictScalars Geom).comap rowMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, F, a, hF, _, rfl⟩
    exact mem_capSpace27.mpr (toGeneric_caps27 ⟨mixedHasse_caps a F hF.1.1, mixedHasse_seed27 a F hF.2⟩)
  exact mem_capSpace27.mp (hle hQ)
private theorem select_row {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {F : PhysicalRow} (hF : F ≠ 0) (hr : HasRank27 w P L secondBox secondCut bankRank) :
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
  apply mem_multiples.mpr (factor_power moving A F t hA hF.1.1 ht ?_)
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
    (hcap : ∀ R : GenericRow, Caps27 secondBox R → R.weightedTotalDegree v ≤ V) :
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
      layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower 7134 t)) :
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
    have hle := Nat.mul_le_mul_left (layerPower 7134 t) (Nat.pos_of_ne_zero hn)
    rw [Nat.mul_one] at hle
    simpa only [v, MvPolynomial.weightedTotalDegree_piSingle] using hle.trans h
  intro f hf
  have hfd : f ∣ factorProduct A := Finset.dvd_prod_of_mem id hf
  have h := (MvPolynomial.weightedTotalDegree_le_of_dvd v hfd (product_ne_zero hA)).trans_eq hzero
  simpa only [v, MvPolynomial.weightedTotalDegree_piSingle, Nat.le_zero] using h
theorem proof : Low6960Fat.c2 := by
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
      (hc : ∀ R : GenericRow, Caps27 secondBox R → R.weightedTotalDegree v ≤ V) :
      (factorProduct A).weightedTotalDegree v ≤ reserveCost moving * V * topSlots 0 / bankRank :=
    weighted_resource (by cases moving <;> decide) (product_ne_zero hA) hr hb hcount
      (hdiv moving A hA hcomm) v V hc
  have hbcap (R : GenericRow) (h : Caps27 secondBox R) : jetTotal R ≤ 6820 := h.1.1
  have hjcap (R : GenericRow) (h : Caps27 secondBox R) : jetIndex R ≤ 2300 := h.1.2.1
  have hscap (R : GenericRow) (h : Caps27 secondBox R) :
      R.weightedTotalDegree (Pi.single (none : SeedVar) 1) ≤ 27000 := by
    rw [MvPolynomial.weightedTotalDegree_piSingle]
    exact h.2
  obtain ⟨bF, jF, bM, jM, sM⟩ := factor_arithmetic
  refine ⟨G, hG, factor_pair27 _ _ (toGeneric_ne_zero hF) (toGeneric_ne_zero hGne)
    (toGeneric_caps27 hFCaps) (necessary_caps hG) ?_ ?_⟩
  · intro A hA hcomm
    have hbt := hbound false A hA hcomm _ _ hbcap
    have hji := hbound false A hA hcomm _ _ hjcap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    have hbt' : jetTotal (factorProduct A) ≤ 121 := by
      simp only [reserveCost, Bool.false_eq_true, ite_false, Low6960FatSlots.slot_zero, bF] at hbt
      exact hbt.trans (by decide)
    have hji' : jetIndex (factorProduct A) ≤ 40 := by
      simp only [reserveCost, Bool.false_eq_true, ite_false, Low6960FatSlots.slot_zero, jF] at hji
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
      simpa only [reserveCost, ite_true, Low6960FatSlots.slot_zero, bM] using hbt
    have hji' : jetIndex (factorProduct A) ≤ 5 := by
      simpa only [reserveCost, ite_true, Low6960FatSlots.slot_zero, jM] using hji
    have hse' : seedDegree (factorProduct A) ≤ 70 := by
      simp only [reserveCost, ite_true, Low6960FatSlots.slot_zero, sM] at hse
      exact hse.trans (by decide)
    exact ⟨hbt', hji', hse', excludes_top hA hr hb (hdiv true A hA hcomm)⟩
end
end Low6960FatFactors
end

#print axioms Low6960FatFactors.proof

end Merged_R6960Low6960FatFactors
