import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import ProximityPrize.SubmissionLower.Fat6966Bank24000
import ProximityPrize.SubmissionLower.Fat6966Bank32000
import ProximityPrize.SubmissionLower.KoalaTaperTransferReceipt

section Merged6967_Fat6966Factors
set_option Elab.async false




set_option Elab.async false

-- merged module Fat6966Banks
section Merged_Fat6966Banks

namespace Low6966FatBanks
theorem proof : Low6966Fat.c1 := by
  intro w Γ s P L h
  exact ⟨(Fat6966Bank24000Banks.proof w Γ s P L h).1,
    (Fat6966Bank32000Banks.proof w Γ s P L h).2⟩
end Low6966FatBanks
#print axioms Low6966FatBanks.proof

end Merged_Fat6966Banks

-- merged module Fat6966Factors
section Merged_Fat6966Factors

-- merged module R6960Low6966FatSlots
section Merged_R6960Low6966FatSlots

set_option Elab.async false
/-! Low-specific copies of the seed-cap dependent slot count of `Fast050` (K1_13_4_4),
at seed degree at most 27,0, i.e. 27,1 seed slots. -/
section
namespace Low6966FatSlots
noncomputable section
open K1 K1_13 K1_13_4
open K1_13_4_4 (capSpace mem_capSpace toGeneric_caps toGeneric_injective)
open Low6966Fat (Caps27 Source27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 1024
open K1_13_4_4 (Exponent slotExponent sum_value_choices sum_index_choices sum_odds rank_le_coeffs sum_squares)
def topSlots (a : ℕ) : ℕ := 32001 * 5671 * (1151 - a)^2
def capSpace27 (a : Shape) : Submodule GenericX GenericRow :=
  capSpace a ⊓
  MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) (Low6966Fat.seedCap a)
theorem mem_capSpace27 {a : Shape} {F : GenericRow} : F ∈ capSpace27 a ↔ Caps27 a F := by
  classical
  simp only [capSpace27, Submodule.mem_inf, mem_capSpace,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, Caps27, Low6966Fat.seedCap, seedDegree]
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
        (Finset.range 32001).image (fun z => (k, j, i, z)))))
private theorem tuples_card (a : ℕ) : (slotTuples a).card ≤ topSlots a := by
  unfold slotTuples
  calc
    _ ≤ ∑ k ∈ Finset.Ico a 1151, ∑ j ∈ Finset.range (2301 - 2*k),
        ∑ _ ∈ Finset.range (6821 - k - j), 32001 := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
      exact Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = topSlots a := by
      unfold topSlots
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      calc
        _ = ∑ k ∈ Finset.Ico a 1151, (32001 * 5671) * (2301 - 2*k) := by
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
  change m none ≤ 32000 at hz
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
def seedSlots (a : ℕ) := (32001-a) * 5671 * 1151^2
@[irreducible] private def seedTuples (lo a : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Ico lo 1151).biUnion (fun k =>
    (Finset.range (2301 - 2*k)).biUnion (fun j =>
      (Finset.range (6821 - k - j)).biUnion (fun i =>
        (Finset.Ico a 32001).image (fun z => (k, j, i, z)))))
private theorem seed_card (a : ℕ) : (seedTuples 0 a).card ≤ seedSlots a := by
  unfold seedTuples
  calc
    _ ≤ ∑ k ∈ Finset.Ico 0 1151, ∑ j ∈ Finset.range (2301 - 2*k),
        ∑ _ ∈ Finset.range (6821 - k - j), (32001-a) := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
      exact Finset.card_image_le.trans_eq (Nat.card_Ico _ _)
    _ = seedSlots a := by
      unfold seedSlots
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      calc
        _ = ∑ k ∈ Finset.Ico 0 1151, ((32001-a) * 5671) * (2301 - 2*k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ 1150 := by have h := (Finset.mem_Ico.mp hk).2; omega
          rw [← Finset.sum_mul, sum_value_choices hk']
          ring
        _ = _ := by rw [← Finset.mul_sum, sum_index_choices]
private theorem seed_mem {lo a : ℕ} {R : GenericRow} (hR : Caps27 secondBox R)
    {m : Exponent} (hm : m ∈ R.support) (hlo : lo ≤ m (some 2)) (ha : a ≤ m none) :
    m ∈ (seedTuples lo a).image slotExponent := by
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
  change m none ≤ 32000 at hz
  refine Finset.mem_image.mpr ⟨(m (some 2), m (some 1), m (some 0), m none), ?_, ?_⟩
  · unfold seedTuples
    refine Finset.mem_biUnion.mpr ⟨m (some 2), Finset.mem_Ico.mpr ⟨hlo, by omega⟩, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨m (some 1), Finset.mem_range.mpr (by omega), ?_⟩
    refine Finset.mem_biUnion.mpr ⟨m (some 0), Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_image.mpr ⟨m none, Finset.mem_Ico.mpr ⟨ha, by omega⟩, rfl⟩
  · ext i
    cases i with
    | none => simp [slotExponent]
    | some i => fin_cases i <;> simp [slotExponent]
theorem seed_symbols (a r : ℕ) (e : Fin r → GenericRow) (he : LinearIndependent GenericX e)
    (h : ∀ R ∈ Submodule.span GenericX (Set.range e),
      Caps27 secondBox R ∧ (R ≠ 0 → a ≤ R.degreeOf none)) :
    r ≤ seedSlots a := by
  have hc := rank_le_coeffs ((seedTuples 0 a).image slotExponent) e he (by
    intro R hR hn
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup R.support
      (MvPolynomial.support_nonempty.mpr hn) (fun u => u none)
    have hdeg := (h R hR).2 hn
    rw [MvPolynomial.degreeOf_eq_sup, hmax] at hdeg
    exact ⟨m, seed_mem (h R hR).1 hm (Nat.zero_le _) hdeg, MvPolynomial.mem_support_iff.mp hm⟩)
  exact hc.trans (Finset.card_image_le.trans (seed_card a))
theorem seed_layer {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {a r t : ℕ}
    (hb : ∃ e : Fin r → GenericRow, LinearIndependent GenericX e ∧
      ∀ i, e i ∈ layerSpan w P L t)
    (hdeg : ∀ R ∈ layerSpan w P L t, R ≠ 0 → a ≤ R.degreeOf none) :
    r ≤ seedSlots a := by
  obtain ⟨e, he, hs⟩ := hb
  have hspan : Submodule.span GenericX (Set.range e) ≤ layerSpan w P L t :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hs i)
  exact seed_symbols a r e he (fun R hR => ⟨layerSpan_caps (hspan hR), hdeg R (hspan hR)⟩)
theorem slot_zero : topSlots 0 = 240421800018471 := by decide
theorem slot_sum : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) = 92121654520544025 := by
  have hs : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) =
      (32001 * 5671) * ∑ k ∈ Finset.range 1150, (1150 - k)^2 := by
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
end Low6966FatSlots
end

end Merged_R6960Low6966FatSlots

-- merged module R6960Low6966FatFactors
section Merged_R6960Low6966FatFactors

set_option Elab.async false
section
namespace Low6966FatFactors
noncomputable section
open Polynomial K1 K1_13
open K1_13_4 (ResidueChart PhysicalRow GenericX GenericRow HasRank Source secondBox toGeneric)
open K1_13_4_4_1 (Exponent polePower weight)
open K1_13_4 (SeedVar seedDegree)
open Low6966Fat (secondCut bankRank)
open scoped BigOperators
open K1_13_4_4_1 (bank bankEval mem_bank kernel_le boundary below_boundary independent_generic)
open K1_13_4_4_1 (endpoint)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def seedSpace : Submodule Geom PhysicalRow :=
  (MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) 32000).restrictScalars Geom
theorem mem_seedSpace {F : PhysicalRow} : F ∈ seedSpace ↔ seedDegree F ≤ 32000 := by
  simp only [seedSpace, Submodule.restrictScalars_mem,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, seedDegree]
private def bank27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Submodule Geom PhysicalRow := bank w P L t ⊓ seedSpace
private theorem mem_bank27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) (F : PhysicalRow) : F ∈ bank27 w P L t ↔ Low6966Fat.Source27 w P L secondBox t F := by
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
    (L : ResidueChart P) (hr : Low6966Fat.HasRank27 w P L secondBox secondCut bankRank) :
    ∃ r : ℕ → ℕ, bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t ∧
      ∀ t ≤ secondCut, ∃ e : Fin (r t) → GenericRow,
        LinearIndependent GenericX e ∧ ∀ i, e i ∈ Low6966FatSlots.layerSpan w P L t := by
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
    have hsrc (i : Fin (r t)) : Low6966Fat.Source27 w P L secondBox t (e i).val :=
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
end Low6966FatFactors
end
section
namespace Low6966FatFactors
noncomputable section
open K1_13_4 hiding mixedWeight secondCut
open K1_13_4_4 (FactorsFor factorProduct mixedHasse_zero toGeneric_caps cutoff_sum_le)
open Low6966FatSlots (topSlots)
open Low6966Fat (mixedWeight secondCut bankRank)
open scoped Polynomial BigOperators
open K1_13_4_4_2 (line line_zero line_toGeneric transverse pow_dvd_of_coeff positive_jet_degree)
def reserveCost (moving : Bool) : ℕ := if moving then 6948 else 48690
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
    let T := 240421800018471
    48690 * 6820 * T / bankRank = 123 ∧ 48690 * 2300 * T / bankRank = 41 ∧
      6948 * 6820 * T / bankRank = 17 ∧ 6948 * 2300 * T / bankRank = 5 ∧
      6948 * 32000 * T / bankRank = 83 := by decide
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
    (h : ∀ t ≤ secondCut, r t ≤ topSlots (layerPower 6948 t)) : False := by
  have hb := cutoff_sum_le (W := secondCut) (n := 1150) (by decide : 0 < 6948)
    r (fun k => topSlots (1 + k)) h (fun k hk => by
      have hk' : 1151 - (1 + k) = 0 := by omega
      simp [topSlots, hk'])
  rw [Low6966FatSlots.slot_sum] at hb
  exact (not_le_of_gt (by decide : 6948 * 92121654520544025 < bankRank)) (hr.trans hb)
end
end Low6966FatFactors
end
section
namespace Low6966FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (FactorsFor factorProduct)
open Low6966Fat (CommonPair Caps27)
open scoped Polynomial BigOperators
open K1_13_4_4 (pureEval pureEval_section pure_degree_le caps_of_dvd)
private theorem seed_of_dvd {F Q : GenericRow} {cap : ℕ} (hF : F ≠ 0) (hs : seedDegree F ≤ cap)
    (hQ : Q ∣ F) : seedDegree Q ≤ cap := by
  simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
    (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hQ hF).trans
      (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hs)
theorem factor_pair27
    (F G : GenericRow) (hF : F ≠ 0) (hG : G ≠ 0)
    (hFCap : Caps27 firstBox F) (hGCap : Caps27 secondBox G)
    (hfixed : ∀ A, FactorsFor false A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 123 ∧ jetIndex (factorProduct A) ≤ 41)
    (hmoving : ∀ A, FactorsFor true A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 17 ∧ jetIndex (factorProduct A) ≤ 5 ∧
      seedDegree (factorProduct A) ≤ 41 ∧ ∀ f ∈ A, f.degreeOf (some 2) = 0) :
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
end Low6966FatFactors
end
section
namespace Low6966FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (FactorsFor factorProduct rowMap
  capSpace mem_capSpace mixedHasse_zero toGeneric_ne_zero toGeneric_caps mixedHasse_caps)
open Low6966FatSlots (topSlots layerSpan layerSpan_caps count_layer capSpace27 mem_capSpace27
  toGeneric_caps27)
open Low6966Fat (Caps27 HasRank27)
open Low6966Fat (Necessary mixedWeight secondCut bankRank)
open scoped BigOperators
open K1_13_4_4 (multiples mem_multiples weighted_pow)
set_option maxRecDepth 1024
private theorem mixedHasse_seed27 (a : SeedVar →₀ ℕ) (F : PhysicalRow)
    (hs : seedDegree F ≤ 32000) : seedDegree (mixedHasse a F) ≤ 32000 := by
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
      layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower 6948 t)) :
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
    have hle := Nat.mul_le_mul_left (layerPower 6948 t) (Nat.pos_of_ne_zero hn)
    rw [Nat.mul_one] at hle
    simpa only [v, MvPolynomial.weightedTotalDegree_piSingle] using hle.trans h
  intro f hf
  have hfd : f ∣ factorProduct A := Finset.dvd_prod_of_mem id hf
  have h := (MvPolynomial.weightedTotalDegree_le_of_dvd v hfd (product_ne_zero hA)).trans_eq hzero
  simpa only [v, MvPolynomial.weightedTotalDegree_piSingle, Nat.le_zero] using h
private theorem seed_bound {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {r : ℕ → ℕ} {D : GenericRow} (hn : D ≠ 0)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow, LinearIndependent GenericX u ∧
      ∀ i, u i ∈ layerSpan w P L t)
    (hdvd : ∀ t ≤ secondCut, layerSpan w P L t ≤ multiples (D ^ layerPower 6948 t)) :
    seedDegree D ≤ 41 := by
  by_contra! h
  have upper (t : ℕ) (ht : t ≤ secondCut) :
      r t ≤ Low6966FatSlots.seedSlots (42 * layerPower 6948 t) := by
    apply Low6966FatSlots.seed_layer (hb t ht)
    intro R hR hne
    let v : SeedVar → ℕ := Pi.single none 1
    have hm := MvPolynomial.weightedTotalDegree_le_of_dvd v
      (mem_multiples.mp (hdvd t ht hR)) hne
    rw [weighted_pow _ _ hn] at hm
    simp only [v, MvPolynomial.weightedTotalDegree_piSingle] at hm
    rw [Nat.mul_comm 42]
    exact (Nat.mul_le_mul_left _ (show 42 ≤ D.degreeOf none from h)).trans hm
  let q (k : ℕ) := Low6966FatSlots.seedSlots (42 * (1+k))
  have cap := K1_13_4_4.cutoff_sum_le (W := secondCut) (n := 762) (by decide : 0 < 6948) r q
    (fun t ht => upper t ht) (fun k hk => by
      have hz : 32001 - 42 * (1+k) = 0 := by omega
      simp [q, Low6966FatSlots.seedSlots,hz])
  have stop : 6948 * (∑ k ∈ Finset.range 762, q k) < bankRank := by
    dsimp only [q]
    decide +kernel
  omega

theorem proof : Low6966Fat.c2 := by
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
      R.weightedTotalDegree (Pi.single (none : SeedVar) 1) ≤ 32000 := by
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
    have hbt' : jetTotal (factorProduct A) ≤ 123 := by
      simp only [reserveCost, Bool.false_eq_true, ite_false, Low6966FatSlots.slot_zero, bF] at hbt
      exact hbt.trans (by decide)
    have hji' : jetIndex (factorProduct A) ≤ 41 := by
      simp only [reserveCost, Bool.false_eq_true, ite_false, Low6966FatSlots.slot_zero, jF] at hji
      exact hji.trans (by decide)
    exact ⟨hbt', hji'⟩
  · intro A hA hcomm
    have hbt := hbound true A hA hcomm _ _ hbcap
    have hji := hbound true A hA hcomm _ _ hjcap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    have hbt' : jetTotal (factorProduct A) ≤ 17 := by
      simpa only [reserveCost, ite_true, Low6966FatSlots.slot_zero, bM] using hbt
    have hji' : jetIndex (factorProduct A) ≤ 5 := by
      simpa only [reserveCost, ite_true, Low6966FatSlots.slot_zero, jM] using hji
    have hse' := seed_bound (product_ne_zero hA) hr hb (hdiv true A hA hcomm)
    exact ⟨hbt', hji', hse', excludes_top hA hr hb (hdiv true A hA hcomm)⟩
end
end Low6966FatFactors
end

#print axioms Low6966FatFactors.proof

end Merged_R6960Low6966FatFactors

end Merged_Fat6966Factors

end Merged6967_Fat6966Factors

section Merged6967_Final50Price
set_option Elab.async false


set_option Elab.async false
namespace Final50Price
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement : ℕ := 179886
abbrev errors : ℕ := 82258
abbrev physicalDegree : ℕ := 133484
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev incidenceGap : ℕ := agreement - physicalDegree
abbrev anchorCutoff : ℕ := 99 * agreement - 1 + 55
abbrev primaryCutoff : ℕ := 3000 * agreement - 1
abbrev primaryBox : Shape := ⟨4012, 1650, 550⟩
abbrev layerNeed : ℕ := 21410054907182
abbrev layerWidth : ℕ := agreement - physicalDegree + 3
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
def fullCap (top : ℕ) : Shape := ⟨132, 55, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 132 ∧ (∑ i, (a i).j) ≤ 55 ∧
    (∑ i, (a i).t) ≤ top
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) (fullCap 14) ∧ TrueWeightLE f anchorCutoff
def ActiveFits (f : Row 4) (K : ℕ) : Prop :=
  ∀ m ∈ f.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ K

def ProperCut (f : Row 4) (Γ : Finset K) (s : K → (Polynomial K)) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    ActiveFits Q 5164 ∧ ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
abbrev symbolCount : ℕ := 406807694511

/-- Bound a layer by the tapered ambient count and the residual rectangular count. -/
def remaining (b j : ℕ) : ℕ := min symbolCount (K1_13.remaining b j)

def LayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  layerNeed ≤ ∑ r ∈ Finset.range (1 + primaryCutoff / layerWidth),
    remaining (∑ i, (r + 1 - l i) * (a i).b) (∑ i, (r + 1 - l i) * (a i).j)
abbrev FatEquations := P3_6.FatEquations
abbrev fatOrder : ℕ := 49090
abbrev divisorOrder : ℕ := 44377
abbrev isolatedOrder : ℕ := 527
abbrev commonBox := P3_6.commonBox
abbrev resultantBox := P3_6.resultantBox
def lowerCap : ℕ → ℕ
  | 0 => 26246384522076207
  | 1 => 23627465960775710
  | 2 => 21133596615821611
  | 3 => 18767433911909189
  | 4 => 16530693501056613
  | 5 => 14425923827562914
  | 6 => 12454942720323126
  | 7 => 10620202125823606
  | 8 => 8923609362806183
  | 9 => 7367532771421102
  | 10 => 5953956064333931
  | 11 => 4685177275728358
  | 12 => 3563243007377633
  | 13 => 2590394696761443
  | 14 => 1768727921051672
  | _ => 0
def Holds (E : FatEquations) (S : (Polynomial Geom)) : Prop :=
  atJet E.common S = 0 ∨ OrderAt E.residual S fatOrder

structure Messages (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩

def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPriceOld (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
abbrev BentCap := Shape × ℕ

def bentGraph (p : Shape) : BentCap := (⟨max p.b (p.j + 1), p.j + 1, p.t + 1⟩, 1)

def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))

def bentIntegral (B J T H : ℤ) : ℤ :=
  -576 * H ^ 5 + 160 * T ^ 2 * H ^ 3 - 480 * T ^ 3 * H ^ 2 + 540 * T ^ 4 * H
  + 960 * J * H ^ 4 - 320 * J * T * H ^ 3 + 960 * J * T ^ 2 * H ^ 2 - 1200 * J * T ^ 3 * H
  - 480 * J ^ 2 * H ^ 3 - 480 * J ^ 2 * T * H ^ 2 + 840 * J ^ 2 * T ^ 2 * H
  + 240 * J ^ 3 * H ^ 2 - 240 * J ^ 3 * T * H - 960 * B * H ^ 4 + 640 * B * T * H ^ 3
  - 1440 * B * T ^ 2 * H ^ 2 + 1440 * B * T ^ 3 * H + 640 * B * J * H ^ 3
  + 960 * B * J * T * H ^ 2 - 1440 * B * J * T ^ 2 * H - 480 * B * J ^ 2 * H ^ 2
  + 480 * B * J ^ 2 * T * H

def addBent (p q : BentCap) : BentCap := (p.1.plus q.1, p.2 + q.2)

def ambientMix (caps : List BentCap) : ℕ :=
  (caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) *
      bentIntegral s.1.b s.1.j s.1.t s.2) 0).toNat

def tiltedSurface (p q : Shape) : ℕ :=
  ambientMix [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]

def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]

def activeLoss (cs : List (ℕ × ℕ)) : ℕ :=
  480 * ((cs.map Prod.snd).prod - (cs.map (fun x => x.2 - 2*x.1)).prod)

def tiltedSurfaceActive (p q : Shape) (K : ℕ) : ℕ :=
  tiltedSurface p q - activeLoss (activeClips p K)

def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))

def physicalPriceWith (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceTilted (x : Shape) (l : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurface x.chamber primaryBox)

def physicalPriceActive (x : Shape) (l K : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurfaceActive x.chamber primaryBox K)

def physicalPrice (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOld x l) (physicalPriceTilted x l)
    if activeFitsPrice x K then min base (physicalPriceActive x l K) else base
  else physicalPriceOld x l

def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (errors * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (errors * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated


end
end Final50Price

end Merged6967_Final50Price

section Merged6967_UpperBranch1
set_option Elab.async false

set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_1
open K1_14 (Shape shapeSum)
open scoped BigOperators
def poleRows (s : Shape) : ℕ :=
  shapeSum s (fun q _ => s.B + s.J - q)
def nodeRows (s : Shape) : ℕ :=
  262144 * shapeSum s (fun q j => s.m + min q s.J - (q + 2*j))
def columnCount (B J t q : ℕ) : ℕ :=
  let low := J - t
  let high := min J (B + 2*J - 1 - t)
  min q high + 1 - low
def pivotCount (B J t q : ℕ) : ℕ :=
  min (columnCount B J t q) (B + 2*J - (t + q))
def largestGradeSum (B J t R : ℕ) : ℕ :=
  (Finset.range (B+1)).inf' Finset.nonempty_range_add_one fun k =>
    R*k + ∑ q ∈ Finset.range (B+1), (q-k) * columnCount B J t q
def offsetMoment (B J t : ℕ) : ℕ :=
  let R := ∑ q ∈ Finset.range (B+1), pivotCount B J t q
  largestGradeSum B J t R - ∑ q ∈ Finset.range (B+1), q * pivotCount B J t q
def groupedPoleMoment (B J : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (B+2*J), offsetMoment B J t
end P1_7_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P1_7_1
noncomputable section
open K1 (I)
open K1_14 (L FX Shape)
open K1_14_1 Polynomial
open scoped Polynomial BigOperators
open K1_14_1_8 (leading_forward)
open K1_14_1_8 (boundaryMap boundary_rank_le strict_of_ker ker_step_le)
theorem zero_of_strict_cutoff {h} (hhi : h ≤ 131070) {D : PoleData h}
    (Crt : CRTLift D) (s : Shape) (P : Source) (hp : P ∈ poleSpace Crt s)
    (hs : ∀ j i a e, coeffAt P j i a e ≠ 0 →
      a+(i+j)*(131071+h) < (s.B+s.J)*(2*h)+j) : P = 0 := by
  by_contra hP
  let j := P.natDegree
  let i := P.leadingCoeff.natDegree
  let g := P.leadingCoeff.leadingCoeff
  have hg : g ≠ 0 := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  obtain ⟨e, he⟩ : ∃ e, g.leadingCoeff.coeff e ≠ 0 := by
    by_contra! hh
    exact (leadingCoeff_ne_zero.mpr hg) (MvPolynomial.eq_zero_iff.mpr hh)
  have hcoeff : coeffAt P j i g.natDegree e ≠ 0 := by
    simpa [coeffAt, j, i, g, coeff_natDegree] using he
  have hlt := hs j i g.natDegree e hcoeff
  let H := rawBlock D
  have hm : H.Monic := ((D.monic 0).mul (D.monic 1)).map _
  have hd : H.natDegree = 2*h := K1_14_1_4.rawBlock_degree D
  have hinj : Function.Injective (algebraMap SeedPoly SeedField) :=
    IsFractionRing.injective SeedPoly SeedField
  have hg' : genericCoefficients g ≠ 0 := Polynomial.map_ne_zero_iff hinj |>.2 hg
  have hdeg : (genericCoefficients g).natDegree = g.natDegree := Polynomial.natDegree_map_eq_of_injective hinj g
  obtain ⟨Q, hQ⟩ := hp
  have hdvd : H^(s.B+s.J) ∣ genericCoefficients g * H^(i+j) := by
    refine ⟨(Q.coeff j).coeff i, ?_⟩
    have hc := congrArg (fun R : RawSource => (R.coeff j).coeff i) hQ
    change ((forward Crt P).coeff j).coeff i = _ at hc
    have hlead := leading_forward Crt P
    dsimp only at hlead
    rw [show j = P.natDegree from rfl, show i = P.leadingCoeff.natDegree from rfl, hlead] at hc
    simpa only [jetConstant, RingHom.comp_apply, coeff_C_mul, H, i, j, g] using hc
  have hlo := natDegree_le_of_dvd hdvd (mul_ne_zero hg' (pow_ne_zero _ hm.ne_zero))
  rw [natDegree_mul hg' (pow_ne_zero _ hm.ne_zero), hdeg, natDegree_pow, natDegree_pow, hd] at hlo
  have hweights : (i+j)*(131071+h) = (i+j)*(2*h) + (i+j)*(131071-h) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hj : j ≤ (i+j)*(131071-h) := (Nat.le_add_left j i).trans
    (by simpa using Nat.mul_le_mul_left (i+j) (show 1 ≤ 131071-h by omega))
  rw [hweights] at hlt
  omega
private theorem ker_zero {h} (hhi : h ≤ 131070) {D : PoleData h} (Crt : CRTLift D)
    (word : I → L) (s : Shape) : (boundaryMap Crt word s 0).ker = ⊥ := by
  apply bot_unique
  intro P hP
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply zero_of_strict_cutoff hhi Crt s P P.property.2
  intro j i a e hn
  simpa only [zero_add] using strict_of_ker ⟨P, hP⟩ hn
theorem telescope {h : ℕ} (hraw : h ≤ 131070) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ) :
    Module.finrank L (complete Crt word s W) ≤
      ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t) := by
  induction W with
  | zero =>
    have hr := (boundaryMap Crt word s 0).finrank_range_add_finrank_ker
    rw [ker_zero hraw Crt word s, finrank_bot, add_zero] at hr
    simpa [← hr] using boundary_rank_le Crt word s 0
  | succ W ih =>
    rw [Finset.sum_range_succ]
    have hr := (boundaryMap Crt word s (W+1)).finrank_range_add_finrank_ker
    have ha := boundary_rank_le Crt word s (W+1)
    have hb := ker_step_le Crt word s W
    omega
end
end P1_7_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P1_7_1
noncomputable section
open Polynomial
open K1_14 (L FX Shape liftPoly triangle)
open K1_14_1 K1_14_1_7 K1_14_1_7_3
open P1 (K I)
open scoped BigOperators Polynomial
open K1_14_1_7 (poleTest_of_local)
open P0_10_1_1 (regular_deformation)
def c1 : Prop :=
  ∀ (F : Type) [Field F] [CharP F K1.p] (s : Shape),
    s.B < K1.p →
    ∀ (H : (Polynomial F)) (lift : (Polynomial (SeedFrac F)))
      (α : F) (side : Fin 2) (a b c : F),
      H.eval α = 0 → H.derivative.eval α ≠ 0 → b ≠ 0 →
      lift.eval (algebraMap F (SeedFrac F) α) = residue side a b c →
      ∃ d : Fin (poleRows s) → ℕ,
        (∑ r, d r) ≤ groupedPoleMoment s.B s.J ∧
        ∃ tests : Fin (poleRows s) → TrueSource F →ₗ[F] Seed F,
          (∀ r P, Shaped s P → SeedWindow s.U (d r) side (tests r P)) ∧
          ∀ P, Shaped s P → (∀ r, tests r P = 0) →
            (jetConstant ((Polynomial.X (R := SeedFrac F) -
                Polynomial.C (algebraMap F (SeedFrac F) α)) ^ (s.B+s.J)) :
              JetPolys (SeedFrac F)) ∣ forward H lift P
private abbrev ScalarRow {h : ℕ} (s : Shape) (d : Fin (2*h) → Fin (poleRows s) → ℕ) :=
  Σ t : Fin (2*h), Σ r : Fin (poleRows s), Fin (triangle s.U + (s.U+1)*d t r)
private theorem scalarRow_card_le {h : ℕ} (s : Shape)
    (d : Fin (2*h) → Fin (poleRows s) → ℕ) (hd : ∀ t, (∑ r, d t r) ≤ groupedPoleMoment s.B s.J) :
    Fintype.card (ScalarRow s d) ≤ poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J := by
  classical
  simp only [ScalarRow, Fintype.card_sigma, Fintype.card_fin]
  calc
    (∑ t : Fin (2*h), ∑ r : Fin (poleRows s), (triangle s.U + (s.U+1)*d t r)) ≤
        ∑ _ : Fin (2*h), (poleRows s * triangle s.U + (s.U+1)*groupedPoleMoment s.B s.J) := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hd t)) _
    _ = poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (2*h)*(poleRows s * triangle s.U + (s.U+1)*groupedPoleMoment s.B s.J) = _
      unfold poleCredit poleRows
      ring
private theorem simple_rank_le (hlocal : c1)
    {F ι : Type} [Field F] [CharP F K1.p] [Fintype ι] {h : ℕ}
    {H : (Polynomial F)} {lift : (Polynomial (SeedFrac F))}
    (G : SimplePoles h H lift) (s : Shape) (hs : s.B < K1.p) (P : ι → TrueSource F)
    (hP : ∀ k, Shaped s (P k)) {n : ℕ} (M : Matrix (Fin n) ι F)
    (hM : ∀ v, M.mulVec v = 0 ↔ PoleTest s H lift (Fintype.linearCombination F P v)) :
    M.rank ≤ poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J := by
  classical
  have ht (t : Fin (2*h)) := hlocal F s hs H lift (G.root t) (G.side t) (G.a t) (G.b t) (G.c t)
    (G.vanishes t) (G.simple t) (G.b_ne t) (G.centre t)
  choose d hd tests hwindow htest using ht
  have hread (t : Fin (2*h)) (r : Fin (poleRows s)) := seedWindow_read F s.U (d t r) (G.side t)
  choose read hread using hread
  let f : (ι → F) →ₗ[F] (ScalarRow s d → F) :=
    LinearMap.pi fun r =>
      ((LinearMap.proj r.2.2).comp (read r.1 r.2.1)).comp
        ((tests r.1 r.2.1).comp (Fintype.linearCombination F P))
  have hker : LinearMap.ker f ≤ LinearMap.ker M.mulVecLin := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply poleTest_of_local s G
    intro t
    have hv' := shaped_combination hP v
    apply htest t _ hv'
    intro r
    apply hread t r _ (hwindow t r _ hv')
    funext k
    exact congrFun (LinearMap.mem_ker.mp hv) ⟨t, r, k⟩
  have hn := Submodule.finrank_mono hker
  have hr : Module.finrank F (LinearMap.range f) ≤
      poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J := by
    refine (LinearMap.range f).finrank_le.trans ?_
    rw [Module.finrank_pi]
    exact scalarRow_card_le s d hd
  have hf := f.finrank_range_add_finrank_ker
  have hm := M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega
theorem pole_bound (hlocal : c1) {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape) (hs : s.B < K1.p) (W : ℕ) :
    Module.finrank L (contacted h word s W) ≤
      poleCredit h s + 2*h*(s.U+1)*groupedPoleMoment s.B s.J +
        Module.finrank L (complete Crt word s W) := by
  classical
  obtain ⟨E⟩ := regular_deformation hpos hchar D Crt
  let A := contacted h word s W
  let _ : Module.Finite L A := contacted_finite h word s W
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source := fun k => basis k
  have hP (k : Fin d) : Shaped s (P k) := contacted_shaped (basis k).property
  obtain ⟨n, M, hspecial, hg⟩ := K1_14_1_7_4.proof E s (Fin d) P hP
  let embed := genericPoint.comp (Polynomial.C (R := L))
  let _ : CharP L K1.p := charP_of_injective_ringHom (algebraMap K L).injective K1.p
  let _ : CharP GenericField K1.p :=
    charP_of_injective_ringHom (f := embed) (generic_injective.comp Polynomial.C_injective) K1.p
  have hgen := simple_rank_le hlocal E.genericPoles s hs _
    (fun k => shaped_map embed (hP k)) _ hg
  have hrank := (specialization_rank_le M).trans hgen
  let f := (M.map specialPoint).mulVecLin
  have hf : ∀ v : Fin d → L,
      Fintype.linearCombination L P v = ((basis.equivFun.symm v : A) : Source) := by
    intro v
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul, Submodule.subtype_apply, P] using
      map_sum A.subtype (fun k => v k • basis k) Finset.univ
  have hk (v : LinearMap.ker f) :
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source) ∈ complete Crt word s W := by
    have hv := (hspecial v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property, hv⟩
  let g : LinearMap.ker f →ₗ[L] complete Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  let _ : Module.Finite L (complete Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : complete Crt word s W => (x : Source)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ _
  omega
end
end P1_7_1
end
section
set_option autoImplicit false
namespace P1_7_1_1
noncomputable section
open Polynomial
open K1_14 (Shape)
open K1_14_1_7 K1_14_1_7_2
open P1_7_1 (columnCount pivotCount)
open scoped BigOperators Polynomial
abbrev Offset (s : Shape) := Fin (s.B + 2*s.J)
def firstJet (s : Shape) (t : Offset s) : ℕ := s.J - t.val
def outputLength (s : Shape) (t : Offset s) (q : Grade s) : ℕ :=
  s.B + 2*s.J - (t.val + q.val)
abbrev Column (s : Shape) (t : Offset s) :=
  Σ q : Grade s, Fin (columnCount s.B s.J t.val q.val)
abbrev Pivot (s : Shape) (t : Offset s) :=
  Σ q : Grade s, Fin (pivotCount s.B s.J t.val q.val)
def columnJet {s : Shape} {t : Offset s} (u : Column s t) : ℕ :=
  firstJet s t + u.2.val
def columnOrder {s : Shape} {t : Offset s} (u : Column s t) : ℕ :=
  t.val + columnJet u - s.J
def pascal {R : Type} [Semiring R] (l n h : ℕ) :
    Matrix (Fin (min n h)) (Fin n) R :=
  fun i j => ((l + j.val).choose i.val : R)
def PascalSpans (F : Type) [Field F] (l n h : ℕ) : Prop :=
  ∀ i < h, ∃ w : Fin (min n h) → F, ∀ j : Fin n,
    ((l + j.val).choose i : F) = ∑ r, w r * pascal l n h r j
def PascalMinor (F : Type) [Field F] (l n h : ℕ) : Prop :=
  ∃ e : Fin (min n h) ↪ Fin n,
    ((pascal (R := F) l n h).submatrix id e).det ≠ 0
def poleMatrix {R : Type} [CommSemiring R] (s : Shape) (t : Offset s) (z : R) :
    Matrix (Pivot s t) (Column s t) R :=
  fun r u =>
    let j := columnJet u
    if r.1.val ≤ u.1.val ∧ j ≤ r.1.val then
      ((j.choose r.2.val : R) * ((u.1.val - j).choose (r.1.val - j) : R)) *
        z ^ (u.1.val - r.1.val)
    else 0
def input {F : Type} [Field F] (α : F) {s : Shape} {t : Offset s} (u : Column s t) :
    TrueSource F →ₗ[F] Seed F :=
  inputTaylorCoeff α (columnJet u) (u.1.val - columnJet u) (columnOrder u)
abbrev OneSeedFrac (F : Type) [Field F] := FractionRing (Polynomial F)
def oneResidue {F : Type} [Field F] (a b c : F) : OneSeedFrac F :=
  let z := algebraMap (Polynomial F) (OneSeedFrac F) Polynomial.X
  algebraMap F (OneSeedFrac F) a * z /
    (algebraMap F (OneSeedFrac F) b + algebraMap F (OneSeedFrac F) c * z)
def BoundedMinors {F ι κ : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι κ (OneSeedFrac F)) (D : ℕ) : Prop :=
  (∃ e : ι ↪ κ, (M.submatrix id e).det ≠ 0) ∧
  ∃ scale : OneSeedFrac F, scale ≠ 0 ∧
    ∀ e : ι ↪ κ, ∃ g : (Polynomial F), g.natDegree ≤ D ∧
      algebraMap (Polynomial F) (OneSeedFrac F) g = scale * (M.submatrix id e).det
end
end P1_7_1_1
end
section
set_option autoImplicit false
namespace P1_7_1_1
noncomputable section
open K1_14 (Shape shapeSum)
open K1_14_1_7 (Grade GradeSlot LocalRow)
open P1_7_1 (columnCount pivotCount poleRows groupedPoleMoment)
open scoped BigOperators
theorem jet_bounds (s : Shape) (t : Offset s) (q : Grade s) (i : ℕ)
    (hi : i < columnCount s.B s.J t.val q.val) :
    firstJet s t + i ≤ min q.val s.J ∧
      t.val + (firstJet s t + i) - s.J < s.B + s.J := by
  change i < min q.val (min s.J (s.B + 2*s.J - 1 - t.val)) + 1 -
    (s.J - t.val) at hi
  have hq : min q.val (min s.J (s.B + 2*s.J - 1 - t.val)) ≤ q.val := min_le_left ..
  have hj := (min_le_right q.val _).trans (min_le_left s.J (s.B + 2*s.J - 1 - t.val))
  have ht := (min_le_right q.val _).trans (min_le_right s.J (s.B + 2*s.J - 1 - t.val))
  have htl : t.val < s.B + 2*s.J := t.isLt
  unfold firstJet
  rw [le_min_iff]
  omega
private abbrev AllPivots (s : Shape) := Σ t : Offset s, Pivot s t
private abbrev AllLocalRows (s : Shape) := Σ q : Grade s, LocalRow s q.val
private def toLocal (s : Shape) (r : AllPivots s) : AllLocalRows s :=
  let t := r.1
  let q := r.2.1
  let i := r.2.2.val
  let j := firstJet s t + i
  let x := t.val + j - s.J
  have hi : i < min (columnCount s.B s.J t.val q.val) (outputLength s t q) := r.2.2.isLt
  have hj := (jet_bounds s t q i (hi.trans_le (min_le_left ..))).1
  have hrow : x < s.B + s.J - q.val := by
    have h := hi.trans_le (min_le_right _ _)
    have hjJ := hj.trans (min_le_right _ _)
    have hq := q.isLt
    dsimp [x, j, firstJet, outputLength] at *
    omega
  ⟨q, ⟨x, hrow⟩, ⟨j, Nat.lt_succ_of_le hj⟩⟩
private theorem toLocal_injective (s : Shape) : Function.Injective (toLocal s) := by
  rintro ⟨t, q, i⟩ ⟨t', q', i'⟩ h
  have hq : q = q' := congrArg Sigma.fst h
  have hx := congrArg (fun y : AllLocalRows s => y.2.1.val) h
  have hj := congrArg (fun y : AllLocalRows s => y.2.2.val) h
  change t.val + (firstJet s t + i.val) - s.J =
    t'.val + (firstJet s t' + i'.val) - s.J at hx
  change firstJet s t + i.val = firstJet s t' + i'.val at hj
  have ht : t = t' := by
    apply Fin.ext
    unfold firstJet at hx hj
    omega
  subst t'
  subst q'
  have hi : i = i' := Fin.ext (by omega)
  subst i'
  rfl
private theorem toLocal_surjective (s : Shape) : Function.Surjective (toLocal s) := by
  rintro ⟨q, x, j⟩
  have hq := q.isLt
  have hx := x.isLt
  have hj : j.val ≤ min q.val s.J := Nat.lt_succ_iff.mp j.isLt
  have hjq := hj.trans (min_le_left _ _)
  have hjJ := hj.trans (min_le_right _ _)
  let t : Offset s := ⟨x.val + s.J - j.val, by omega⟩
  have ht : t.val + j.val = x.val + s.J := by dsimp [t]; omega
  have hfirst : firstJet s t ≤ j.val := by unfold firstJet; omega
  let i := j.val - firstJet s t
  have hji : firstJet s t + i = j.val := by dsimp [i]; omega
  have hhigh : j.val ≤ s.B + 2*s.J - 1 - t.val := by omega
  have hcol : i < columnCount s.B s.J t.val q.val := by
    unfold columnCount
    change i < min q.val (min s.J (s.B + 2*s.J - 1 - t.val)) + 1 - firstJet s t
    have hmin := le_min hjq (le_min hjJ hhigh)
    omega
  have hrow : i < outputLength s t q := by
    unfold outputLength
    unfold firstJet at hji
    omega
  let r : AllPivots s := ⟨t, q, ⟨i, lt_min hcol hrow⟩⟩
  refine ⟨r, Sigma.ext rfl (heq_of_eq (Prod.ext (Fin.ext ?_) (Fin.ext ?_)))⟩
  · change t.val + (firstJet s t + i) - s.J = x.val
    omega
  · exact hji
private theorem allPivots_card (s : Shape) :
    Fintype.card (AllPivots s) = poleRows s := by
  classical
  rw [Fintype.card_congr (Equiv.ofBijective _ ⟨toLocal_injective s, toLocal_surjective s⟩)]
  simp only [AllLocalRows, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    poleRows, shapeSum]
  rw [Fin.sum_univ_eq_sum_range (fun q => (s.B + s.J - q) * (min q s.J + 1)) (s.B+1)]
  apply Finset.sum_congr rfl
  intro q _
  simp [Nat.mul_comm]
def rowIndex (s : Shape) : Fin (poleRows s) ≃ AllPivots s :=
  (Fintype.equivFinOfCardEq (allPivots_card s)).symm
theorem rowIndex_sum (s : Shape) (d : ∀ t : Offset s, Pivot s t → ℕ)
    (hd : ∀ t, (∑ r, d t r) ≤ P1_7_1.offsetMoment s.B s.J t.val) :
    (∑ k, d (rowIndex s k).1 (rowIndex s k).2) ≤ groupedPoleMoment s.B s.J := by
  calc
    _ = ∑ k : AllPivots s, d k.1 k.2 :=
      Fintype.sum_equiv (rowIndex s) _ _ (fun _ => rfl)
    _ = ∑ t : Offset s, ∑ r, d t r := Fintype.sum_sigma _
    _ ≤ ∑ t : Offset s, P1_7_1.offsetMoment s.B s.J t.val :=
      Finset.sum_le_sum fun t _ => hd t
    _ = _ := Fin.sum_univ_eq_sum_range _ _
end
end P1_7_1_1
end
section
set_option autoImplicit false
namespace P1_7_1_1
noncomputable section
open Matrix
open scoped BigOperators Matrix
private def consecutive {R : Type} [Semiring R] (l m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j => ((l + j.val).choose i.val : R)
private theorem consecutive_det {R : Type} [CommRing R] (l m : ℕ) :
    (consecutive (R := R) l m).det = 1 := by
  let L : Matrix (Fin m) (Fin m) R := fun i k =>
    if k.val ≤ i.val then (l.choose (i.val - k.val) : R) else 0
  let U : Matrix (Fin m) (Fin m) R := fun k j => (j.val.choose k.val : R)
  have hLU : consecutive l m = L * U := by
    ext i j
    rw [Matrix.mul_apply]
    change ((l + j.val).choose i.val : R) =
      ∑ k : Fin m,
        (if k.val ≤ i.val then (l.choose (i.val - k.val) : R) else 0) *
          (j.val.choose k.val : R)
    rw [Nat.add_comm l j.val, Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.cast_sum,
      Fin.sum_univ_eq_sum_range (fun k =>
        (if k ≤ i.val then (l.choose (i.val - k) : R) else 0) * (j.val.choose k : R)) m]
    calc
      _ = ∑ k ∈ Finset.range (i.val + 1),
          (if k ≤ i.val then (l.choose (i.val - k) : R) else 0) * (j.val.choose k : R) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), mul_comm]
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt i.isLt))
        intro k _ hk
        have hki : ¬ k ≤ i.val := fun h => hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
        simp [hki]
  have hL : L.IsLowerTriangular := by
    intro i k hik
    change (if k.val ≤ i.val then (l.choose (i.val - k.val) : R) else 0) = 0
    exact ite_eq_right (not_le_of_gt (show i.val < k.val from hik))
  have hU : U.IsUpperTriangular := by
    intro i j hij
    change (j.val.choose i.val : R) = 0
    rw [Nat.choose_eq_zero_of_lt (show j.val < i.val from hij), Nat.cast_zero]
  rw [hLU, Matrix.det_mul, Matrix.det_of_isLowerTriangular L hL, Matrix.det_of_isUpperTriangular hU]
  simp [L, U]
theorem pascal_minor (F : Type) [Field F] (l n h : ℕ) : PascalMinor F l n h := by
  let e : Fin (min n h) ↪ Fin n := Fin.castLEEmb (min_le_left n h)
  refine ⟨e, ?_⟩
  change (consecutive (R := F) l (min n h)).det ≠ 0
  rw [consecutive_det]
  exact one_ne_zero
theorem pascal_spans (F : Type) [Field F] (l n h : ℕ) : PascalSpans F l n h := by
  classical
  intro i hi
  unfold pascal
  by_cases hle : h ≤ n
  · rw [min_eq_right hle]
    let k : Fin h := ⟨i, hi⟩
    refine ⟨fun r => if r = k then 1 else 0, fun j => ?_⟩
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · simp [k]
    · intro r _ hne
      simp [hne]
  · rw [min_eq_left (le_of_not_ge hle)]
    let B := consecutive (R := F) l n
    have hB : B.det = 1 := consecutive_det l n
    let : Invertible B := B.invertibleOfIsUnitDet (hB.symm ▸ isUnit_one)
    let v : Fin n → F := fun j => ((l + j.val).choose i : F)
    refine ⟨v ᵥ* ⅟B, fun j => ?_⟩
    change v j = ((v ᵥ* ⅟B) ᵥ* B) j
    rw [Matrix.vecMul_vecMul, invOf_mul_self, Matrix.vecMul_one]
end
end P1_7_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1
noncomputable section
open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1_7 (Grade)
open P1_7_1 (columnCount pivotCount largestGradeSum offsetMoment)
open scoped BigOperators Matrix Polynomial
private def minorGrade {s : Shape} {t : Offset s} (e : Pivot s t ↪ Column s t) : ℕ :=
  (∑ r, (e r).1.val) - ∑ r : Pivot s t, r.1.val
private theorem minorGrade_le {s : Shape} {t : Offset s} (e : Pivot s t ↪ Column s t) :
    minorGrade e ≤ offsetMoment s.B s.J t.val := by
  classical
  have hpivot : (∑ r : Pivot s t, r.1.val) =
      ∑ q ∈ Finset.range (s.B+1), q * pivotCount s.B s.J t.val q := by
    simp only [Pivot, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id]
    rw [Fin.sum_univ_eq_sum_range (fun q => pivotCount s.B s.J t.val q * q) (s.B+1)]
    simp only [Nat.mul_comm (pivotCount s.B s.J t.val _) _]
  unfold minorGrade offsetMoment
  rw [hpivot]
  apply Nat.sub_le_sub_right
  unfold largestGradeSum
  apply Finset.le_inf'
  intro k _
  have hexcess :
      (∑ r, ((e r).1.val - k)) ≤ ∑ u : Column s t, (u.1.val - k) := by
    calc
      _ = ∑ u ∈ Finset.univ.map e, (u.1.val - k) :=
        (Finset.sum_map (Finset.univ : Finset (Pivot s t)) e (fun u => u.1.val - k)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intros
        positivity)
  calc
    (∑ r, (e r).1.val) ≤ ∑ r, (k + ((e r).1.val - k)) :=
      Finset.sum_le_sum fun r _ => by omega
    _ ≤ Fintype.card (Pivot s t) * k + ∑ u : Column s t, (u.1.val - k) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact Nat.add_le_add_left hexcess _
    _ = _ := by
      simp only [Pivot, Column, Fintype.sum_sigma, Fintype.card_sigma, Fintype.card_fin,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      rw [Fin.sum_univ_eq_sum_range (fun q => pivotCount s.B s.J t.val q) (s.B+1),
        Fin.sum_univ_eq_sum_range (fun q => columnCount s.B s.J t.val q * (q-k)) (s.B+1)]
      simp only [Nat.mul_comm (columnCount s.B s.J t.val _) (_ - _)]
private theorem minor_power {R : Type} [CommRing R] {s : Shape} {t : Offset s}
    (e : Pivot s t ↪ Column s t) (z : R) :
    ((poleMatrix s t z).submatrix id e).det =
      ((poleMatrix s t (1 : R)).submatrix id e).det * z ^ minorGrade e := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.submatrix_apply, id_eq, mul_assoc]
  congr 1
  by_cases hgood : ∀ i, (σ i).1.val ≤ (e i).1.val
  · have he (i : Pivot s t) :
        poleMatrix s t z (σ i) (e i) = poleMatrix s t (1 : R) (σ i) (e i) *
          z ^ ((e i).1.val - (σ i).1.val) := by
      by_cases hj : columnJet (e i) ≤ (σ i).1.val <;> simp [poleMatrix, hgood i, hj]
    have hw : (∑ i, ((e i).1.val - (σ i).1.val)) = minorGrade e := by
      rw [Finset.sum_tsub_distrib _ (fun i _ => hgood i), minorGrade,
        Equiv.sum_comp σ (fun r : Pivot s t => r.1.val)]
    simp only [he, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hw]
  · push Not at hgood
    obtain ⟨i, hi⟩ := hgood
    have hz (v : R) : poleMatrix s t v (σ i) (e i) = 0 := by
      simp [poleMatrix, not_le_of_gt hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hz z),
      Finset.prod_eq_zero (Finset.mem_univ i) (hz 1), zero_mul]
private theorem nonzero_minor {R : Type} [Field R] (s : Shape) (t : Offset s) (z : R) :
    ∃ e : Pivot s t ↪ Column s t, ((poleMatrix s t z).submatrix id e).det ≠ 0 := by
  classical
  have h (q : Grade s) := pascal_minor R (firstJet s t) (columnCount s.B s.J t.val q.val)
    (outputLength s t q)
  choose eq hEq using h
  let e : Pivot s t ↪ Column s t := ⟨fun r => ⟨r.1, eq r.1 r.2⟩, by
    rintro ⟨q, i⟩ ⟨q', j⟩ hh
    have hq : q = q' := congrArg Sigma.fst hh
    subst q'
    have heq : eq q i = eq q j := eq_of_heq ((Sigma.mk.inj_iff.mp hh).2)
    exact congrArg (Sigma.mk q) ((eq q).injective heq)⟩
  let A := (poleMatrix s t z).submatrix id e
  have htri : A.BlockTriangular (fun r => r.1) := by
    intro i j hij
    change poleMatrix s t z i (e j) = 0
    have hlt : (e j).1.val < i.1.val := hij
    simp [poleMatrix, not_le_of_gt hlt]
  refine ⟨e, ?_⟩
  change A.det ≠ 0
  rw [htri.det_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro q _
  let f : Fin (pivotCount s.B s.J t.val q.val) ≃ {r : Pivot s t // r.1 = q} :=
    Equiv.ofBijective (fun j => ⟨⟨q, j⟩, rfl⟩) (by
      constructor
      · intro i j hh
        exact eq_of_heq ((Sigma.mk.inj_iff.mp (congrArg Subtype.val hh)).2)
      · rintro ⟨⟨q', j⟩, hq⟩
        change q' = q at hq
        subst q'
        exact ⟨j, rfl⟩)
  rw [← Matrix.det_submatrix_equiv_self f]
  have hblock : ((A.toSquareBlock (fun r => r.1) q).submatrix f f) =
      (pascal (R := R) (firstJet s t) (columnCount s.B s.J t.val q.val)
        (outputLength s t q)).submatrix id (eq q) := by
    ext i j
    have hj := ((jet_bounds s t q (eq q j).val (eq q j).isLt).1).trans (min_le_left _ _)
    change poleMatrix s t z ⟨q, i⟩ ⟨q, eq q j⟩ =
      ((firstJet s t + (eq q j).val).choose i.val : R)
    simp [poleMatrix, columnJet, hj]
  rw [hblock]
  exact hEq q
set_option maxHeartbeats 600000 in
theorem bounded_pole_minors (F : Type) [Field F] (s : Shape) (t : Offset s) (a b c : F)
    (hb : b ≠ 0) :
    BoundedMinors (poleMatrix s t (oneResidue a b c)) (offsetMoment s.B s.J t.val) := by
  let δ := offsetMoment s.B s.J t.val
  let N : (Polynomial F) := C a * Polynomial.X
  let D : (Polynomial F) := C b + C c * Polynomial.X
  let f := algebraMap (Polynomial F) (OneSeedFrac F)
  have hc (u : F) : f (C u) = algebraMap F (OneSeedFrac F) u :=
    (IsScalarTower.algebraMap_apply F (Polynomial F) (OneSeedFrac F) u).symm
  have hD : D ≠ 0 := by
    intro hz
    apply hb
    simpa [D] using congrArg (fun p : (Polynomial F) => p.coeff 0) hz
  have hDf : f D ≠ 0 := by
    simpa only [f, map_zero] using (IsFractionRing.injective (Polynomial F) (OneSeedFrac F)).ne hD
  have hz : oneResidue a b c = f N / f D := by
    simp only [oneResidue, N, D, map_mul, map_add, hc]
    rfl
  have hNdeg : N.natDegree ≤ 1 :=
    (Polynomial.natDegree_mul_le (p := C a) (q := Polynomial.X)).trans (by simp)
  have hDdeg : D.natDegree ≤ 1 := by
    unfold D
    rw [Polynomial.natDegree_C_add]
    exact Polynomial.natDegree_mul_le.trans (by simp)
  refine ⟨nonzero_minor s t _, f D ^ δ, pow_ne_zero _ hDf, ?_⟩
  intro e
  let d := minorGrade e
  let m := ((poleMatrix s t (1 : F)).submatrix id e).det
  have hd : d ≤ δ := minorGrade_le e
  let g := C m * N ^ d * D ^ (δ-d)
  refine ⟨g, ?_, ?_⟩
  · have hNd : (N ^ d).natDegree ≤ d :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left d hNdeg)
    have hDd : (D ^ (δ-d)).natDegree ≤ δ-d :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (δ-d) hDdeg)
    have hg := Polynomial.natDegree_mul_le (p := C m * N ^ d) (q := D ^ (δ-d))
    have hm := Polynomial.natDegree_mul_le (p := C m) (q := N ^ d)
    rw [Polynomial.natDegree_C, zero_add] at hm
    change (C m * N ^ d * D ^ (δ-d)).natDegree ≤ δ
    omega
  · have hmapped : ((poleMatrix s t (1 : F)).submatrix id e).map (algebraMap F (OneSeedFrac F)) =
        (poleMatrix s t (1 : OneSeedFrac F)).submatrix id e := by
      ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, poleMatrix, apply_ite, map_zero,
        map_mul, map_natCast, map_pow, map_one]
      split_ifs <;> rfl
    have hm : f (C m) = ((poleMatrix s t (1 : OneSeedFrac F)).submatrix id e).det := by
      rw [hc]
      change (algebraMap F (OneSeedFrac F)) ((poleMatrix s t (1 : F)).submatrix id e).det = _
      rw [RingHom.map_det]
      exact congrArg Matrix.det hmapped
    have hpow : f D ^ δ * (f N / f D) ^ d = f N ^ d * f D ^ (δ-d) := by
      calc
        _ = f N ^ d * (f D ^ δ / f D ^ d) := by rw [div_pow]; ring
        _ = _ := by
          congr 1
          apply (div_eq_iff (pow_ne_zero _ hDf)).2
          rw [← pow_add, Nat.sub_add_cancel hd]
    rw [minor_power, hz]
    change f (C m * N ^ d * D ^ (δ-d)) =
      f D ^ δ * (((poleMatrix s t (1 : OneSeedFrac F)).submatrix id e).det * (f N / f D) ^ d)
    rw [map_mul, map_mul, map_pow, map_pow, hm, mul_left_comm (f D ^ δ), hpow]
    ac_rfl
end
end P1_7_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1
noncomputable section
open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1 (otherBlock)
open K1_14_1_7 K1_14_1_7_2
open scoped BigOperators Matrix Polynomial
open K1_14_1_7_2 (taylor_seed_degree seedWeight_add window_sum)
private def seedMap (F : Type) [Field F] (side : Fin 2) : (Polynomial F) →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (Polynomial.toMvPolynomial side).toRingHom
private def fractionSeedMap (F : Type) [Field F] (side : Fin 2) :
    OneSeedFrac F →+* SeedFrac F :=
  IsFractionRing.lift (g := seedMap F side)
    ((IsFractionRing.injective (Seed F) (SeedFrac F)).comp
      (Polynomial.toMvPolynomial_injective side))
private theorem fractionSeedMap_polynomial {F : Type} [Field F] (side : Fin 2) (g : (Polynomial F)) :
    fractionSeedMap F side (algebraMap (Polynomial F) (OneSeedFrac F) g) =
      algebraMap (Seed F) (SeedFrac F) (g.toMvPolynomial side) := by
  rw [fractionSeedMap, IsFractionRing.lift_algebraMap]
  rfl
private theorem fractionSeedMap_scalar {F : Type} [Field F] (side : Fin 2) (a : F) :
    fractionSeedMap F side (algebraMap F (OneSeedFrac F) a) =
      algebraMap F (SeedFrac F) a := by
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) (OneSeedFrac F), fractionSeedMap_polynomial]
  change algebraMap (Seed F) (SeedFrac F) ((Polynomial.C a).toMvPolynomial side) = _
  rw [Polynomial.toMvPolynomial_C]
  exact (IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F) a).symm
private theorem fractionSeedMap_residue {F : Type} [Field F] (side : Fin 2) (a b c : F) :
    fractionSeedMap F side (oneResidue a b c) = residue side a b c := by
  simp only [oneResidue, residue, map_div₀, map_add, map_mul, fractionSeedMap_scalar,
    fractionSeedMap_polynomial, Polynomial.toMvPolynomial_X]
def polynomialTest {F : Type} [Field F] {s : Shape} {t : Offset s}
    (α : F) (side : Fin 2) (v : Column s t → (Polynomial F)) : TrueSource F →ₗ[F] Seed F :=
  ∑ u, (v u).toMvPolynomial side • input α u
theorem polynomialTest_apply {F : Type} [Field F] {s : Shape} {t : Offset s}
    (α : F) (side : Fin 2) (v : Column s t → (Polynomial F)) (P : TrueSource F) :
    polynomialTest α side v P = ∑ u, (v u).toMvPolynomial side * input α u P := by
  simp only [polynomialTest, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
theorem side_degrees {F : Type} [Field F] (side : Fin 2) (p : (Polynomial F)) :
    (p.toMvPolynomial side).degreeOf (otherBlock side) ≤ 0 ∧
    (p.toMvPolynomial side).totalDegree ≤ p.natDegree := by
  classical
  have hsum : p.toMvPolynomial side =
      ∑ k ∈ p.support, MvPolynomial.C (p.coeff k) * MvPolynomial.X side ^ k := by
    conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
    simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
      Polynomial.toMvPolynomial_X]
  have hne : otherBlock side ≠ side := by fin_cases side <;> decide
  rw [hsum]
  constructor
  · refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    simpa [MvPolynomial.degreeOf_X_of_ne hne] using
      MvPolynomial.degreeOf_pow_le (otherBlock side) (MvPolynomial.X (R := F) side) k
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact ((MvPolynomial.totalDegree_pow (MvPolynomial.X (R := F) side) k).trans
      (by simp)).trans (Polynomial.le_natDegree_of_mem_supp k hk)
theorem polynomialTest_window {F : Type} [Field F] {s : Shape} {t : Offset s}
    (α : F) (side : Fin 2) (v : Column s t → (Polynomial F)) {d : ℕ}
    (hd : ∀ u, (v u).natDegree ≤ d) {P : TrueSource F} (hP : Shaped s P) :
    SeedWindow s.U d side (polynomialTest α side v P) := by
  rw [polynomialTest_apply]
  apply window_sum
  intro u
  let f := (v u).toMvPolynomial side
  let g := input α u P
  have hf := side_degrees side (v u)
  have hg : g.totalDegree ≤ s.U := taylor_seed_degree s α P hP _ _ _
  have hother : (f * g).degreeOf (otherBlock side) ≤ s.U := by
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    exact (Nat.add_le_add hf.1 ((MvPolynomial.degreeOf_le_totalDegree g _).trans hg)).trans_eq
      (Nat.zero_add _)
  have htotal : (f * g).totalDegree ≤ s.U + d :=
    (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add (hf.2.trans (hd u)) hg).trans_eq (Nat.add_comm _ _))
  intro e he
  have hMem : e ∈ (f * g).support := MvPolynomial.mem_support_iff.mpr he
  refine ⟨(MvPolynomial.le_degreeOf_of_mem_support _ hMem).trans hother, ?_⟩
  rw [← seedWeight_add side e]
  exact (show K1_14_1.seedWeight e ≤ _ from MvPolynomial.le_totalDegree hMem).trans htotal
theorem polynomialTests_to_poleMatrix {F : Type} [Field F] {s : Shape} (t : Offset s)
    (α : F) (side : Fin 2) (a b c : F) (P : TrueSource F)
    (Q : Matrix (Pivot s t) (Column s t) (Polynomial F))
    (L : Matrix (Pivot s t) (Pivot s t) (OneSeedFrac F))
    (hL : poleMatrix s t (oneResidue a b c) = L * Q.map (algebraMap (Polynomial F) (OneSeedFrac F)))
    (hz : ∀ r, polynomialTest α side (Q r) P = 0) :
    poleMatrix s t (residue side a b c) *ᵥ
      (fun u => algebraMap (Seed F) (SeedFrac F) (input α u P)) = 0 := by
  let f := fractionSeedMap F side
  let V : Column s t → SeedFrac F := fun u => algebraMap (Seed F) (SeedFrac F) (input α u P)
  let Q' : Matrix (Pivot s t) (Column s t) (SeedFrac F) := Q.map (seedMap F side)
  have hM : (poleMatrix s t (oneResidue a b c)).map f = poleMatrix s t (residue side a b c) := by
    ext r u
    simp only [Matrix.map_apply, poleMatrix, f, apply_ite, map_zero, map_mul, map_natCast,
      map_pow, fractionSeedMap_residue]
    split_ifs <;> rfl
  have hQ : (Q.map (algebraMap (Polynomial F) (OneSeedFrac F))).map f = Q' := by
    ext r u
    exact fractionSeedMap_polynomial side (Q r u)
  have hV : Q' *ᵥ V = 0 := by
    funext r
    change (∑ u, algebraMap (Seed F) (SeedFrac F) ((Q r u).toMvPolynomial side) *
      algebraMap (Seed F) (SeedFrac F) (input α u P)) = 0
    have hh := congrArg (algebraMap (Seed F) (SeedFrac F)) (hz r)
    simpa only [polynomialTest_apply, map_sum, map_mul, map_zero] using hh
  change poleMatrix s t (residue side a b c) *ᵥ V = 0
  rw [← hM, hL, Matrix.map_mul, hQ, ← Matrix.mulVec_mulVec, hV, Matrix.mulVec_zero]
end
end P1_7_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1
noncomputable section
open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1_7 K1_14_1_7_2
open P1_7_1 (columnCount)
open scoped BigOperators Matrix Polynomial
def c1 : Prop :=
  ∀ (F : Type) [Field F] (s : Shape) (α : F) (z : SeedFrac F),
    (∀ (t : Offset s) (q : Grade s),
      PascalSpans (SeedFrac F) (firstJet s t) (columnCount s.B s.J t.val q.val)
        (outputLength s t q)) →
    ∀ P : TrueSource F, Shaped s P →
      (∀ t : Offset s, poleMatrix s t z *ᵥ
        (fun u => algebraMap (Seed F) (SeedFrac F) (input α u P)) = 0) →
      ∀ (q : Grade s) (k : GradeSlot s q.val),
        (Polynomial.X (R := SeedFrac F)) ^ (s.B+s.J) ∣
          zeroGrade s q.val (localSlots s α z P q) k
def c2 : Prop :=
  ∀ (F ι κ : Type) [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix ι κ (OneSeedFrac F)) (D : ℕ), BoundedMinors M D →
    ∃ (Q : Matrix ι κ (Polynomial F)) (L : Matrix ι ι (OneSeedFrac F)) (d : ι → ℕ),
      M = L * Q.map (algebraMap (Polynomial F) (OneSeedFrac F)) ∧
      (∀ r u, (Q r u).natDegree ≤ d r) ∧ (∑ r, d r) ≤ D
theorem of_children (hLocal : c1) (hBasis : c2) :
    P1_7_1.c1 := by
  classical
  intro F _ _ s _ H lift α side a b c hH _ hb hz
  have hRows (t : Offset s) :=
    hBasis F (Pivot s t) (Column s t) _ _ (bounded_pole_minors F s t a b c hb)
  choose Q L d hL hdeg hsum using hRows
  let tests (t : Offset s) (r : Pivot s t) := polynomialTest α side (Q t r)
  let e := rowIndex s
  refine ⟨fun k => d (e k).1 (e k).2, rowIndex_sum s d hsum,
    fun k => tests (e k).1 (e k).2, ?_, ?_⟩
  · intro k P hP
    exact polynomialTest_window α side _ (hdeg _ _) hP
  · intro P hP hzero
    have ht (t : Offset s) (r : Pivot s t) : tests t r P = 0 := by
      let testAt (k : Σ t : Offset s, Pivot s t) := tests k.1 k.2 P
      have hk : testAt (e (e.symm ⟨t, r⟩)) = 0 := hzero (e.symm ⟨t, r⟩)
      rw [e.apply_symm_apply] at hk
      exact hk
    let z := residue side a b c
    have hslots := hLocal F s α z
      (fun t q => pascal_spans (SeedFrac F) (firstJet s t)
        (columnCount s.B s.J t.val q.val) (outputLength s t q)) P hP
      (fun t => polynomialTests_to_poleMatrix t α side a b c P (Q t) (L t) (hL t) (ht t))
    have hd := K1_14_1_7_2_2.proof F s (localSlots s α z P) hslots
    rw [← K1_14_1_7_2_1.proof F s α z P hP] at hd
    exact transfer_dvd H lift α z (s.B+s.J) P hH hz
      (linear_pole_dvd α z (s.B+s.J) P hd)
end
end P1_7_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1_1
noncomputable section
open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1_7 K1_14_1_7_2 P1_7_1_1
open P1_7_1 (columnCount pivotCount)
open scoped BigOperators Matrix Polynomial
open K1_14_1_7_1 (coeff_zeroGrade)
private abbrev JetIndex (s : Shape) (t : Offset s) (q : Grade s) :=
  Fin (columnCount s.B s.J t.val q.val)
private theorem sum_embedding {A D M : Type} [Fintype A] [Fintype D] [AddCommMonoid M]
    (e : A ↪ D) (f : D → M) (h : ∀ d, (∀ a, e a ≠ d) → f d = 0) :
    ∑ d, f d = ∑ a, f (e a) := by
  classical
  rw [← Finset.sum_map Finset.univ e]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  exact h d fun a ha => hd (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, ha⟩)
private theorem column_index (s : Shape) (t : Offset s) (q : Grade s) (j : ℕ)
    (hj : j ≤ min q.val s.J) (hfirst : firstJet s t ≤ j)
    (hx : t.val + j - s.J < s.B + s.J) :
    j - firstJet s t < columnCount s.B s.J t.val q.val := by
  have ht := t.isLt
  have hhigh : j ≤ s.B + 2*s.J - 1 - t.val := by omega
  have hmin := le_min (hj.trans (min_le_left _ _))
    (le_min (hj.trans (min_le_right _ _)) hhigh)
  change j - firstJet s t < min q.val (min s.J (s.B + 2*s.J - 1 - t.val)) + 1 -
    firstJet s t
  omega
private theorem columnCount_le (s : Shape) (t : Offset s) {q q' : Grade s}
    (h : q.val ≤ q'.val) :
    columnCount s.B s.J t.val q.val ≤ columnCount s.B s.J t.val q'.val := by
  unfold columnCount
  exact Nat.sub_le_sub_right (Nat.add_le_add_right (min_le_min_right _ h) 1) _
private def gradeShift (s : Shape) (q : Grade s) : Shift s q ↪ Grade s where
  toFun p := ⟨q.val + p.val, by
    have hq := q.isLt
    have hp := p.isLt
    omega⟩
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
private def slotEmbedding (s : Shape) (t : Offset s) (q : Grade s) :
    JetIndex s t q ↪ GradeSlot s q.val where
  toFun a := ⟨firstJet s t + a.val,
    Nat.lt_succ_of_le (jet_bounds s t q a.val a.isLt).1⟩
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
private def translatedCoeff {F : Type} [Field F] {s : Shape}
    (α : F) (z : SeedFrac F) (P : TrueSource F) (q : Grade s) (j x : ℕ) : SeedFrac F :=
  ∑ p : Shift s q,
    (((q.val - j + p.val).choose (q.val - j) : SeedFrac F) * z ^ p.val) *
      algebraMap (Seed F) (SeedFrac F) (inputTaylorCoeff α j (q.val - j + p.val) x P)
private theorem localSlots_coeff {F : Type} [Field F] (s : Shape)
    (α : F) (z : SeedFrac F) (P : TrueSource F) (q : Grade s) (j : GradeSlot s q.val)
    (x : ℕ) :
    (localSlots s α z P q j).coeff x = translatedCoeff α z P q j.val x := by
  simp only [localSlots, finsetSum_coeff, coeff_C_mul, coeff_map, inputOrdinate,
    translatedCoeff, inputTaylorCoeff_apply]
private theorem pivot_read {F : Type} [Field F] (s : Shape) (t : Offset s)
    (α : F) (z : SeedFrac F) (P : TrueSource F) (q : Grade s)
    (i : Fin (pivotCount s.B s.J t.val q.val)) :
    (poleMatrix s t z *ᵥ
        (fun u => algebraMap (Seed F) (SeedFrac F) (input α u P))) ⟨q, i⟩ =
      ∑ a : JetIndex s t q, ((firstJet s t + a.val).choose i.val : SeedFrac F) *
        translatedCoeff α z P q (firstJet s t + a.val)
          (t.val + (firstJet s t + a.val) - s.J) := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  let f (q' : Grade s) (a : JetIndex s t q') :=
    poleMatrix s t z ⟨q, i⟩ ⟨q', a⟩ *
      algebraMap (Seed F) (SeedFrac F) (input α ⟨q', a⟩ P)
  change (∑ q', ∑ a, f q' a) = _
  rw [sum_embedding (gradeShift s q) (fun q' => ∑ a, f q' a)]
  · simp only [translatedCoeff, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    let q' := gradeShift s q p
    have hqq : q.val ≤ q'.val := Nat.le_add_right _ _
    let e : JetIndex s t q ↪ JetIndex s t q' :=
      Fin.castLEEmb (columnCount_le s t hqq)
    change (∑ a, f q' a) = _
    rw [sum_embedding e (f q')]
    · apply Finset.sum_congr rfl
      intro a _
      let j := firstJet s t + a.val
      have hj : j ≤ q.val := (jet_bounds s t q a.val a.isLt).1.trans (min_le_left _ _)
      have hp : q'.val - q.val = p.val := by
        change q.val + p.val - q.val = p.val
        omega
      have hOrd : q'.val - j = q.val - j + p.val := by
        change q.val + p.val - j = q.val - j + p.val
        omega
      change (if q.val ≤ q'.val ∧ j ≤ q.val then
        ((j.choose i.val : SeedFrac F) * ((q'.val - j).choose (q.val - j) : SeedFrac F)) *
          z ^ (q'.val - q.val) else 0) *
          algebraMap (Seed F) (SeedFrac F)
            (inputTaylorCoeff α j (q'.val - j) (t.val + j - s.J) P) = _
      rw [ite_eq_left ⟨hqq, hj⟩, hp, hOrd]
      simp only [j, mul_assoc]
    · intro a ha
      have hj : ¬ firstJet s t + a.val ≤ q.val := by
        intro hj
        have hb := jet_bounds s t q' a.val a.isLt
        have hi := column_index s t q (firstJet s t + a.val)
          (le_min hj (hb.1.trans (min_le_right _ _))) (Nat.le_add_right _ _) hb.2
        have ha' : a.val < columnCount s.B s.J t.val q.val := by omega
        exact ha ⟨a.val, ha'⟩ (Fin.ext rfl)
      simp [f, poleMatrix, columnJet, hj]
  · intro q' h
    have hl : ¬ q.val ≤ q'.val := by
      intro hqq
      have hq' := q'.isLt
      let p : Shift s q := ⟨q'.val - q.val, by omega⟩
      exact h p (Fin.ext (by change q.val + (q'.val - q.val) = q'.val; omega))
    apply Finset.sum_eq_zero
    intro a _
    have hz : poleMatrix s t z ⟨q, i⟩ ⟨q', a⟩ = 0 := by
      unfold poleMatrix
      exact ite_eq_right (fun h => hl h.1)
    simp only [f, hz, zero_mul]
private theorem coeff_read {F : Type} [Field F] (s : Shape) (t : Offset s)
    (α : F) (z : SeedFrac F) (P : TrueSource F) (q : Grade s)
    (k : GradeSlot s q.val) (l : ℕ) (hl : l < s.B + s.J)
    (ht : t.val + q.val + k.val = l + s.J) :
    (zeroGrade s q.val (localSlots s α z P q) k).coeff l =
      ∑ a : JetIndex s t q, ((firstJet s t + a.val).choose k.val : SeedFrac F) *
        translatedCoeff α z P q (firstJet s t + a.val)
          (t.val + (firstJet s t + a.val) - s.J) := by
  classical
  rw [coeff_zeroGrade, sum_embedding (slotEmbedding s t q)]
  · apply Finset.sum_congr rfl
    intro a _
    let j := firstJet s t + a.val
    have hj := (jet_bounds s t q a.val a.isLt).1.trans (min_le_left _ _)
    have hshift : q.val - j + k.val ≤ l := by
      have hfirst : s.J ≤ t.val + j := by
        dsimp [j, firstJet]
        omega
      omega
    have hx : l - (q.val - j + k.val) = t.val + j - s.J := by omega
    change (if k.val ≤ j ∧ q.val - j + k.val ≤ l then
      (j.choose k.val : SeedFrac F) * (localSlots s α z P q (slotEmbedding s t q a)).coeff
        (l - (q.val - j + k.val)) else 0) = _
    by_cases hk : k.val ≤ j
    · rw [ite_eq_left ⟨hk, hshift⟩, hx, localSlots_coeff]
      rfl
    · change _ = (j.choose k.val : SeedFrac F) *
        translatedCoeff α z P q j (t.val + j - s.J)
      rw [ite_eq_right (fun h => hk h.1), Nat.choose_eq_zero_of_lt (lt_of_not_ge hk),
        Nat.cast_zero, zero_mul]
  · intro j hj
    split_ifs with h
    · exfalso
      have hjmin : j.val ≤ min q.val s.J := Nat.lt_succ_iff.mp j.isLt
      have hjq := hjmin.trans (min_le_left _ _)
      have hshift := h.2
      have hfirst : firstJet s t ≤ j.val := by unfold firstJet; omega
      have hx : t.val + j.val - s.J < s.B + s.J := by omega
      let a : JetIndex s t q := ⟨j.val - firstJet s t, column_index s t q j.val hjmin hfirst hx⟩
      apply hj a
      apply Fin.ext
      change firstJet s t + (j.val - firstJet s t) = j.val
      omega
    · rfl
private theorem pascal_sum_zero {E : Type} [Field E] {a n h : ℕ}
    (hs : PascalSpans E a n h) (v : Fin n → E)
    (hv : ∀ r, (∑ j, pascal a n h r j * v j) = 0) (k : ℕ) (hk : k < h) :
    (∑ j : Fin n, ((a + j.val).choose k : E) * v j) = 0 := by
  obtain ⟨w, hw⟩ := hs k hk
  simp only [hw, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hv, mul_zero, Finset.sum_const_zero]
theorem proof : P1_7_1_1.c1 := by
  intro F _ s α z hs P _ hm q k
  apply Polynomial.X_pow_dvd_iff.mpr
  intro l hl
  by_cases ht : q.val + k.val ≤ l + s.J
  · let t : Offset s := ⟨l + s.J - (q.val + k.val), by omega⟩
    have ht' : t.val + q.val + k.val = l + s.J := by dsimp [t]; omega
    have hk : k.val < outputLength s t q := by unfold outputLength; omega
    rw [coeff_read s t α z P q k l hl ht']
    let v (j : JetIndex s t q) :=
      translatedCoeff α z P q (firstJet s t + j.val) (t.val + (firstJet s t + j.val) - s.J)
    apply pascal_sum_zero (hs t q) v _ k.val hk
    intro r
    have hr := congrFun (hm t) (⟨q, r⟩ : Pivot s t)
    rw [pivot_read] at hr
    exact hr
  · rw [coeff_zeroGrade]
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val ≤ min q.val s.J := Nat.lt_succ_iff.mp j.isLt
    have hjq := hj.trans (min_le_left _ _)
    have hjJ := hj.trans (min_le_right _ _)
    have hn : ¬ q.val - j.val + k.val ≤ l := by omega
    simp [hn]
end
end P1_7_1_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1_2
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "K" => P1_7_1_1.OneSeedFrac F
local notation "φ" => algebraMap (Polynomial F) K
private theorem clear_denominators (M : Matrix ι κ K) (e : ι ↪ κ)
    (he : (M.submatrix id e).det ≠ 0) :
    ∃ (A : Matrix ι κ (Polynomial F)) (b : K), b ≠ 0 ∧ A.map φ = b • M ∧
      (A.submatrix id e).det ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial F)) (fun p : ι × κ => M p.1 p.2)
  choose a ha using hb
  let A : Matrix ι κ (Polynomial F) := fun i j => a (i, j)
  have hmap : A.map φ = φ b • M := by
    apply Matrix.ext
    intro i j
    change φ (a (i, j)) = φ b * M i j
    simpa only [Algebra.smul_def] using ha (i, j)
  have hb0 : φ b ≠ 0 :=
    fun h => (nonZeroDivisors.ne_zero b.property)
      (IsFractionRing.injective (Polynomial F) K (h.trans (map_zero φ).symm))
  refine ⟨A, φ b, hb0, hmap, ?_⟩
  intro h
  have hdet : φ (A.submatrix id e).det = (φ b • M.submatrix id e).det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det (congrArg (fun B : Matrix ι κ K => B.submatrix id e) hmap)
  rw [h, map_zero, Matrix.det_smul] at hdet
  exact (mul_ne_zero (pow_ne_zero _ hb0) he) hdet.symm
theorem exists_split_rows (M : Matrix ι κ K)
    (hM : ∃ e : ι ↪ κ, (M.submatrix id e).det ≠ 0) :
    ∃ (Q : Matrix ι κ (Polynomial F)) (T : Matrix κ ι (Polynomial F)) (L : Matrix ι ι K),
      Q * T = 1 ∧ M = L * Q.map φ := by
  classical
  obtain ⟨e, he⟩ := hM
  obtain ⟨A, b, hb, hA, hminor⟩ := clear_denominators M e he
  let N := LinearMap.range A.vecMulLinear
  have hAi : Function.Injective A.vecMulLinear := by
    intro x y hxy
    apply Matrix.vecMul_injective_iff.mpr (Matrix.linearIndependent_rows_of_det_ne_zero hminor)
    exact funext fun j => congrFun hxy (e j)
  have hN : Module.finrank (Polynomial F) N = Fintype.card ι := by
    rw [LinearMap.finrank_range_of_inj hAi, Module.finrank_pi]
  obtain ⟨n, S⟩ := N.smithNormalForm (Pi.basisFun (Polynomial F) κ)
  let re : ι ≃ Fin n := Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis S.bN, hN])
  let Q : Matrix ι κ (Polynomial F) := fun i => S.bM (S.f (re i))
  let T : Matrix κ ι (Polynomial F) := fun j i => S.bM.coord (S.f (re i)) (Pi.single j 1)
  have hQT : Q * T = 1 := by
    apply Matrix.ext
    intro i j
    have hsum : (∑ k : κ, Q i k • (Pi.single k 1 : κ → (Polynomial F))) = Q i := by
      funext k
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
    have hcoord := congrArg (S.bM.coord (S.f (re j))) hsum
    simp only [map_sum, map_smul, smul_eq_mul] at hcoord
    change (∑ k : κ, Q i k * S.bM.coord (S.f (re j)) (Pi.single k 1)) = _
    rw [hcoord]
    change S.bM.coord (S.f (re j)) (S.bM (S.f (re i))) = _
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq]
  have hrow (i : ι) : A i ∈ N := by
    refine ⟨Pi.single i 1, ?_⟩
    exact Matrix.single_one_vecMul i A
  let W : Matrix ι ι (Polynomial F) := fun i j => S.bN.repr ⟨A i, hrow i⟩ (re j) * S.a (re j)
  have hW : W * Q = A := by
    apply Matrix.ext
    intro i j
    have hsum := S.bN.sum_repr ⟨A i, hrow i⟩
    let l : N →ₗ[(Polynomial F)] (Polynomial F) := (LinearMap.proj j).comp N.subtype
    have hc := congrArg l hsum
    rw [Matrix.mul_apply, ← Equiv.sum_comp re.symm]
    simpa only [l, map_sum, map_smul, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply, W, Q, S.snf, Equiv.apply_symm_apply, ← mul_assoc,
      Pi.smul_apply, smul_eq_mul] using hc
  refine ⟨Q, T, b⁻¹ • W.map φ, hQT, ?_⟩
  have h := congrArg (fun B : Matrix ι κ (Polynomial F) => B.map φ) hW
  rw [Matrix.map_mul, hA] at h
  rw [Matrix.smul_mul, h, smul_smul, inv_mul_cancel₀ hb, one_smul]
end
end P1_7_1_1_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1_2
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "K" => P1_7_1_1.OneSeedFrac F
local notation "φ" => algebraMap (Polynomial F) K
def leadingRows (Q : Matrix ι κ (Polynomial F)) (d : ι → ℕ) : Matrix ι κ F :=
  fun i j => (Q i j).coeff (d i)
omit [Fintype ι] in
private theorem no_zero_row {Q : Matrix ι κ (Polynomial F)} {T : Matrix κ ι (Polynomial F)}
    (h : Q * T = 1) (p : ι) : Q p ≠ 0 := by
  intro hp
  have hpp := congrFun (congrFun h p) p
  rw [Matrix.mul_apply, hp] at hpp
  simp at hpp
private theorem reduce_step (Q : Matrix ι κ (Polynomial F)) (T : Matrix κ ι (Polynomial F)) (d : ι → ℕ)
    (hQT : Q * T = 1) (hdeg : ∀ r u, (Q r u).natDegree ≤ d r)
    (hbad : ¬ LinearIndependent F (leadingRows Q d).row) :
    ∃ (E : Matrix ι ι (Polynomial F)) (d' : ι → ℕ), IsUnit E.det ∧
      (∀ r u, ((E * Q) r u).natDegree ≤ d' r) ∧ (∑ r, d' r) < ∑ r, d r := by
  classical
  rw [Fintype.linearIndependent_iff] at hbad
  push Not at hbad
  obtain ⟨a, ha, i, hi⟩ := hbad
  let s := Finset.univ.filter (fun i => a i ≠ 0)
  have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨p, hp, hmax⟩ := s.exists_max_image d hs
  have hap : a p ≠ 0 := (Finset.mem_filter.mp hp).2
  have hle (r : ι) (hr : a r ≠ 0) : d r ≤ d p :=
    hmax r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
  let c (r : ι) : (Polynomial F) := C (a r) * (Polynomial.X (R := F)) ^ (d p - d r)
  let E := (1 : Matrix ι ι (Polynomial F)).updateRow p c
  have hc : c p = C (a p) := by simp [c]
  have hE : IsUnit E.det := by
    have hrow : (∑ k, c k • (1 : Matrix ι ι (Polynomial F)) k) = c := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_one]
    change IsUnit ((1 : Matrix ι ι (Polynomial F)).updateRow p c).det
    rw [← hrow, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one, hc]
    exact (isUnit_iff_ne_zero.mpr hap).map C
  have hform : E * Q = Q.updateRow p (∑ r, c r • Q r) := by
    change (1 : Matrix ι ι (Polynomial F)).updateRow p c * Q = _
    rw [Matrix.updateRow_mul, Matrix.one_mul, Matrix.vecMul_eq_sum]
  have hbound (u : κ) : ((E * Q) p u).natDegree ≤ d p := by
    rw [hform, Matrix.updateRow_self, Finset.sum_apply]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r _
    by_cases hz : a r = 0
    · simp [c, hz]
    · have hr := hle r hz
      change ((C (a r) * (Polynomial.X (R := F)) ^ (d p - d r)) * Q r u).natDegree ≤ _
      rw [mul_assoc]
      have hm : ((Polynomial.X (R := F)) ^ (d p - d r) * Q r u).natDegree ≤
          (d p - d r) + d r :=
        Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_X_pow_le _) (hdeg r u)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (hm.trans (by omega))
  have hcoeff (u : κ) : ((E * Q) p u).coeff (d p) = 0 := by
    rw [hform, Matrix.updateRow_self, Finset.sum_apply, Polynomial.finsetSum_coeff]
    have hA := congrFun ha u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hA
    rw [← hA]
    apply Finset.sum_congr rfl
    intro r _
    change ((C (a r) * (Polynomial.X (R := F)) ^ (d p - d r)) * Q r u).coeff (d p) =
      a r * (Q r u).coeff (d r)
    rw [mul_assoc, Polynomial.coeff_C_mul]
    by_cases hz : a r = 0
    · simp [hz]
    · congr 1
      have hr := hle r hz
      have heq : d r + (d p - d r) = d p := by omega
      exact (congrArg (((Polynomial.X (R := F)) ^ (d p - d r) * Q r u).coeff) heq.symm).trans
        (Polynomial.coeff_X_pow_mul _ _ _)
  have hpos : 0 < d p := by
    by_contra! hp0
    have heq : d p = 0 := Nat.eq_zero_of_le_zero hp0
    have hright : (E * Q) * (T * E⁻¹) = 1 := by
      rw [Matrix.mul_assoc E, ← Matrix.mul_assoc Q, hQT, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ hE]
    apply no_zero_row hright p
    funext u
    have hdeg0 : ((E * Q) p u).natDegree ≤ 0 := heq ▸ hbound u
    have hz : ((E * Q) p u).coeff 0 = 0 := heq ▸ hcoeff u
    change ((E * Q) p u) = 0
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg0, hz, map_zero]
  let d' := Function.update d p (d p - 1)
  refine ⟨E, d', hE, ?_, ?_⟩
  · intro r u
    by_cases hr : r = p
    · subst r
      change ((E * Q) p u).natDegree ≤ Function.update d p (d p - 1) p
      rw [Function.update_self]
      exact Polynomial.natDegree_le_pred (hbound u) (hcoeff u)
    · rw [hform, Matrix.updateRow_ne hr]
      change (Q r u).natDegree ≤ Function.update d p (d p - 1) r
      rw [Function.update_of_ne hr]
      exact hdeg r u
  · apply Finset.sum_lt_sum
    · intro r _
      by_cases hr : r = p
      · simp [d', hr]
      · simp [d', Function.update_of_ne hr]
    · exact ⟨p, Finset.mem_univ p, by simpa [d'] using Nat.sub_lt hpos (by decide : 0 < 1)⟩
theorem exists_reduced_rows (M : Matrix ι κ K)
    (hM : ∃ (Q : Matrix ι κ (Polynomial F)) (T : Matrix κ ι (Polynomial F)) (L : Matrix ι ι K),
      Q * T = 1 ∧ M = L * Q.map φ) :
    ∃ (Q : Matrix ι κ (Polynomial F)) (T : Matrix κ ι (Polynomial F)) (L : Matrix ι ι K) (d : ι → ℕ),
      Q * T = 1 ∧ M = L * Q.map φ ∧
      (∀ r u, (Q r u).natDegree ≤ d r) ∧ LinearIndependent F (leadingRows Q d).row := by
  classical
  let P (n : ℕ) :=
    ∃ (Q : Matrix ι κ (Polynomial F)) (T : Matrix κ ι (Polynomial F)) (L : Matrix ι ι K) (d : ι → ℕ),
      Q * T = 1 ∧ M = L * Q.map φ ∧ (∀ r u, (Q r u).natDegree ≤ d r) ∧ (∑ r, d r) = n
  have hP : ∃ n, P n := by
    obtain ⟨Q, T, L, hQT, hL⟩ := hM
    let d (i : ι) := Finset.univ.sup (fun u : κ => (Q i u).natDegree)
    exact ⟨_, Q, T, L, d, hQT, hL, fun r u => Finset.le_sup (f := fun v : κ => (Q r v).natDegree) (Finset.mem_univ u), rfl⟩
  obtain ⟨Q, T, L, d, hQT, hL, hdeg, hn⟩ := Nat.find_spec hP
  refine ⟨Q, T, L, d, hQT, hL, hdeg, ?_⟩
  by_contra hbad
  obtain ⟨E, d', hE, hdeg', hlt⟩ := reduce_step Q T d hQT hdeg hbad
  let V := E⁻¹
  have hEV : E * V = 1 := Matrix.mul_nonsing_inv _ hE
  have hVE : V * E = 1 := Matrix.nonsing_inv_mul _ hE
  have hnew : P (∑ i, d' i) := by
    refine ⟨E * Q, T * V, L * V.map φ, d', ?_, ?_, hdeg', rfl⟩
    · rw [Matrix.mul_assoc E, ← Matrix.mul_assoc Q, hQT, Matrix.one_mul, hEV]
    · rw [Matrix.map_mul, Matrix.mul_assoc L, ← Matrix.mul_assoc (V.map φ),
        ← Matrix.map_mul, hVE, Matrix.map_one _ (map_zero φ) (map_one φ),
        Matrix.one_mul, hL]
  exact (not_lt_of_ge (Nat.find_min' hP hnew)) (hn ▸ hlt)
end
end P1_7_1_1_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P1_7_1_1_2
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "K" => P1_7_1_1.OneSeedFrac F
local notation "φ" => algebraMap (Polynomial F) K
omit [Fintype ι] in
private theorem coeff_weighted_prod {s : Finset ι} (p : ι → (Polynomial F)) (d : ι → ℕ)
    (h : ∀ i ∈ s, (p i).natDegree ≤ d i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (p i).coeff (d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self _ _))]
    · exact congrArg ((p i).coeff (d i) * ·) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    · exact (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem exists_full_minor (B : Matrix ι κ F) (hB : LinearIndependent F B.row) :
    ∃ e : ι ↪ κ, (B.submatrix id e).det ≠ 0 := by
  classical
  have hr : B.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hB]
  obtain ⟨α, a, ha, hspan, hli⟩ := exists_linearIndependent' F B.col
  let : Finite α := Finite.of_injective a ha
  let : Fintype α := Fintype.ofFinite α
  have hc : Fintype.card ι = Fintype.card α := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hr]
  let u := Fintype.equivOfCardEq hc
  let e : ι ↪ κ := u.toEmbedding.trans ⟨a, ha⟩
  have hli' : LinearIndependent F (B.submatrix id e).col := hli.comp u u.injective
  exact ⟨e, ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hli')).ne_zero⟩
theorem exists_minor_of_degree_sum (Q : Matrix ι κ (Polynomial F)) (d : ι → ℕ)
    (hdeg : ∀ r u, (Q r u).natDegree ≤ d r)
    (hlead : LinearIndependent F (leadingRows Q d).row) :
    ∃ e : ι ↪ κ, (Q.submatrix id e).det ≠ 0 ∧ (∑ r, d r) ≤ (Q.submatrix id e).det.natDegree := by
  obtain ⟨e, he⟩ := exists_full_minor (leadingRows Q d) hlead
  have hcoeff :
      (Q.submatrix id e).det.coeff (∑ r, d r) = ((leadingRows Q d).submatrix id e).det := by
    rw [← Matrix.det_transpose (Q.submatrix id e), ← Matrix.det_transpose ((leadingRows Q d).submatrix id e),
      Matrix.det_apply', Matrix.det_apply', Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← map_intCast (C : F →+* (Polynomial F)), Polynomial.coeff_C_mul]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, leadingRows]
    rw [coeff_weighted_prod _ d (fun i _ => hdeg i (e (σ i)))]
  have hne : (Q.submatrix id e).det.coeff (∑ r, d r) ≠ 0 := hcoeff.trans_ne he
  exact ⟨e, fun hz => hne (by rw [hz, Polynomial.coeff_zero]), Polynomial.le_natDegree_of_ne_zero hne⟩
private theorem det_rectangular_mul {R : Type} [CommRing R]
    (Q : Matrix ι κ R) (T : Matrix κ ι R) :
    (Q * T).det = ∑ f : ι → κ, (∏ j, T (f j) j) * (Q.submatrix id f).det := by
  classical
  calc
    (Q * T).det = ∑ f : ι → κ, ∑ σ : Equiv.Perm ι,
        (↑↑(Equiv.Perm.sign σ) : R) * ∏ i, Q (σ i) (f i) * T (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [Matrix.det_apply', Finset.mul_sum, Matrix.submatrix_apply, id_eq,
        Finset.prod_mul_distrib, mul_comm, mul_assoc]
private theorem scale_polynomial (Q : Matrix ι κ (Polynomial F)) (T : Matrix κ ι (Polynomial F))
    (hQT : Q * T = 1) (t : K)
    (h : ∀ f : ι → κ, ∃ g : (Polynomial F), φ g = t * φ (Q.submatrix id f).det) :
    ∃ g : (Polynomial F), φ g = t := by
  classical
  choose g hg using h
  refine ⟨∑ f : ι → κ, (∏ j, T (f j) j) * g f, ?_⟩
  have hh := det_rectangular_mul Q T
  rw [hQT, Matrix.det_one] at hh
  have he := congrArg φ hh
  simp only [map_one, map_sum, map_mul] at he
  simp only [map_sum, map_mul, hg]
  calc
    _ = t * ∑ f : ι → κ, φ (∏ j, T (f j) j) * φ (Q.submatrix id f).det := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun f _ => mul_left_comm _ _ _
    _ = t := by rw [← he, mul_one]
theorem minor_degree_le (M : Matrix ι κ K) (D : ℕ)
    (Q : Matrix ι κ (Polynomial F)) (T : Matrix κ ι (Polynomial F)) (L : Matrix ι ι K)
    (hQT : Q * T = 1) (hM : M = L * Q.map φ) (hb : P1_7_1_1.BoundedMinors M D)
    (e : ι ↪ κ) (he : (Q.submatrix id e).det ≠ 0) :
    (Q.submatrix id e).det.natDegree ≤ D := by
  classical
  obtain ⟨⟨e₀, he₀⟩, scale, hscale, hminors⟩ := hb
  have hdet (f : ι → κ) :
      (M.submatrix id f).det = L.det * φ (Q.submatrix id f).det := by
    rw [hM, Matrix.submatrix_mul _ _ id id f Function.bijective_id,
      Matrix.submatrix_id_id, Matrix.det_mul, RingHom.map_det]
    rfl
  have hL : L.det ≠ 0 := by
    intro hz
    exact he₀ (by rw [hdet, hz, zero_mul])
  have hall (f : ι → κ) : ∃ g : (Polynomial F), φ g = (scale * L.det) * φ (Q.submatrix id f).det := by
    by_cases hf : Function.Injective f
    · let e' : ι ↪ κ := ⟨f, hf⟩
      obtain ⟨g, _, hg⟩ := hminors e'
      change φ g = scale * (M.submatrix id f).det at hg
      rw [hdet, ← mul_assoc] at hg
      exact ⟨g, hg⟩
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
      have hz : (Q.submatrix id f).det = 0 :=
        Matrix.det_zero_of_column_eq hne (fun u => congrArg (Q u) hij)
      exact ⟨0, by rw [hz, map_zero, mul_zero]⟩
  obtain ⟨p, hp⟩ := scale_polynomial Q T hQT (scale * L.det) hall
  have hp0 : p ≠ 0 := by
    intro hz
    exact (mul_ne_zero hscale hL) (by rw [← hp, hz, map_zero])
  obtain ⟨g, hg, hge⟩ := hminors e
  have hmul : g = p * (Q.submatrix id e).det := by
    apply IsFractionRing.injective (Polynomial F) K
    rw [hge, hdet, map_mul, hp, mul_assoc]
  rw [hmul, Polynomial.natDegree_mul hp0 he] at hg
  exact (Nat.le_add_left _ _).trans hg
end
end P1_7_1_1_2
end
section
set_option autoImplicit false
namespace P1_7_1_1_2
open scoped BigOperators
theorem proof : P1_7_1_1.c2 := by
  intro F ι κ _ _ _ _ M D hM
  obtain ⟨Q, T, L, d, hQT, hL, hdeg, hlead⟩ :=
    exists_reduced_rows M (exists_split_rows M hM.1)
  obtain ⟨e, he, hd⟩ := exists_minor_of_degree_sum Q d hdeg hlead
  exact ⟨Q, L, d, hL, hdeg, hd.trans (minor_degree_le M D Q T L hQT hL hM e he)⟩
end P1_7_1_1_2
end
section
namespace P1_7_1_2
open Finset
open K1_14 (Shape shapeSum)
open P1_7_1 (nodeRows)
open scoped BigOperators
open K1_14_5 (shape_sum_flip)
private def atNode (m J q j : ℕ) : ℕ := m + min q J - (q + 2*j)
private def twiceGrade (k i : ℕ) : ℕ :=
  k*(k+1) + (6*k+2)*i + 8*i*i
def sixPerNode (k J : ℕ) : ℕ :=
  3*(J+1)*k*(k+1) + 3*(3*k+1)*J*(J+1) + 4*J*(J+1)*(2*J+1)
private theorem twice_descending (d : ℕ) :
    2 * (∑ i ∈ range d, (d-i)) = d*(d+1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, mul_add, ih]
    ring
private theorem three_grade_sum (k J : ℕ) :
    3 * (∑ i ∈ range (J+1), twiceGrade k i) = sixPerNode k J := by
  induction J with
  | zero => simp [twiceGrade, sixPerNode, mul_assoc]
  | succ J ih =>
    rw [sum_range_succ, mul_add, ih]
    unfold twiceGrade sixPerNode
    ring
private theorem twice_at_derivative {m B J j : ℕ} (hm : 2*J ≤ m)
    (hB : m+J ≤ B+1) (hj : j ≤ J) :
    2 * (∑ q ∈ Ico j (B+1), atNode m J q j) = twiceGrade (m-2*J) (J-j) := by
  let d := m - 2*j
  have hhead : (∑ q ∈ Ico j J, atNode m J q j) = (J-j)*d := by
    calc
      _ = ∑ _q ∈ Ico j J, d := by
        apply sum_congr rfl
        intro q hq
        unfold atNode
        rw [min_eq_left (mem_Ico.mp hq).2.le]
        dsimp [d]
        omega
      _ = _ := by simp [Nat.card_Ico]
  have htail : (∑ q ∈ Ico J (B+1), atNode m J q j) =
      ∑ i ∈ range d, (d-i) := by
    rw [sum_Ico_eq_sum_range]
    calc
      _ = ∑ i ∈ range (B+1-J), (d-i) := by
        apply sum_congr rfl
        intro i _
        unfold atNode
        rw [min_eq_right (by omega : J ≤ J+i)]
        dsimp [d]
        omega
      _ = _ := by
        symm
        apply sum_subset (range_mono (show d ≤ B+1-J by dsimp [d]; omega))
        intro i _ hi
        have hdi : d ≤ i := by simpa only [mem_range, not_lt] using hi
        exact Nat.sub_eq_zero_of_le hdi
  rw [← sum_Ico_consecutive (atNode m J · j) hj (show J ≤ B+1 by omega),
    hhead, htail, mul_add, twice_descending]
  have hd : d = (m-2*J) + 2*(J-j) := by dsimp [d]; omega
  rw [hd]
  unfold twiceGrade
  ring
theorem six_nodeRows (s : Shape) (hm : 2*s.J ≤ s.m) (hB : s.m+s.J ≤ s.B+1) :
    6 * nodeRows s = 262144 * sixPerNode (s.m-2*s.J) s.J := by
  change 6 * (262144 * shapeSum s (fun q j => atNode s.m s.J q j)) = _
  unfold shapeSum
  rw [shape_sum_flip]
  let f (j : ℕ) := ∑ q ∈ Ico j (s.B+1), atNode s.m s.J q j
  let k := s.m-2*s.J
  change 6 * (262144 * (∑ j ∈ range (s.J+1), f j)) = 262144 * sixPerNode k s.J
  calc
    _ = 262144 * (3 * (2 * ∑ j ∈ range (s.J+1), f j)) := by ring
    _ = 262144 * (3 * ∑ j ∈ range (s.J+1), twiceGrade k (s.J-j)) := by
      rw [mul_sum]
      refine congrArg (fun n : ℕ => 262144 * (3*n)) (sum_congr rfl fun j hj => ?_)
      exact twice_at_derivative hm hB (Nat.lt_succ_iff.mp (mem_range.mp hj))
    _ = _ := by
      have hreflect : (∑ j ∈ range (s.J+1), twiceGrade k (s.J-j)) =
          ∑ j ∈ range (s.J+1), twiceGrade k j := by
        simpa only [Nat.add_sub_cancel] using sum_range_reflect (twiceGrade k) (s.J+1)
      rw [hreflect, three_grade_sum]
end P1_7_1_2
end
section
namespace P1_7_1_3
open P1 (HighBand)
open P1_7 (Bank terminal stages)
def ramp (a q : ℕ) : ℕ := q + 1 - a
def low (J t : ℕ) : ℕ := J - t
def high (B J t : ℕ) : ℕ := min J (B + 2*J - 1 - t)
def width (B J t : ℕ) : ℕ := high B J t + 1 - low J t
def edge (B J t : ℕ) : ℕ := B + 2*J - t
def peak (B J t : ℕ) : ℕ :=
  min (width B J t) ((edge B J t - low J t + 1) / 2)
def productSum6 (n a b : ℕ) : ℕ :=
  6*n*a*b + 3*(a+b)*n*(n-1) + n*(n-1)*(2*(n-1)+1)
def rampCount6 (N a : ℕ) : ℕ :=
  let n := N-a
  3*n*(n+1)
def rampWeight6 (N a : ℕ) : ℕ := productSum6 (N-a) a 1
def rampExcess6 (N k a : ℕ) : ℕ :=
  let s := max (k+1) a
  productSum6 (N-s) (s-k) (s+1-a)
def pivotVolume6 (B J t : ℕ) (stat : ℕ → ℕ) : ℕ :=
  let a := low J t
  let e := edge B J t
  let h := peak B J t
  stat a + stat (e+1) - (stat (a+h) + stat (e+1-h))
def columnVolume6 (B J t : ℕ) (stat : ℕ → ℕ) : ℕ :=
  let a := low J t
  stat a - stat (a + width B J t)
def pivotRank6 (B J t : ℕ) : ℕ := pivotVolume6 B J t (rampCount6 (B+1))
def pivotWeight6 (B J t : ℕ) : ℕ := pivotVolume6 B J t (rampWeight6 (B+1))
def excess6 (B J t k : ℕ) : ℕ := columnVolume6 B J t (rampExcess6 (B+1) k)
def triangularCut (omitted : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo+1 < hi then
      let mid := (lo+hi)/2
      if mid*(mid+1) ≤ 2*omitted then triangularCut omitted fuel mid hi
      else triangularCut omitted fuel lo mid
    else lo
def threshold (B J t : ℕ) : ℕ :=
  let R := pivotRank6 B J t / 6
  let w := width B J t
  let h := high B J t
  if R ≤ w * (B+1-h) then B - (R-1)/w else
    let omitted := columnVolume6 B J t (rampCount6 (B+1)) / 6 - R
    min B (low J t + triangularCut omitted 16 0 (w+1))
def offsetEstimate (B J t : ℕ) : ℕ :=
  let k := threshold B J t
  (pivotRank6 B J t * k + excess6 B J t k - pivotWeight6 B J t) / 6
def evaluate (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => evaluate f n + f n
def blockEstimate (B J start length : ℕ) : ℕ :=
  evaluate (fun i => offsetEstimate B J (start+i)) length
def momentEstimate (B J : ℕ) : ℕ := blockEstimate B J J (B+J)
end P1_7_1_3
end
section
namespace P1_7_1_3
open Finset P1_7_1
private theorem product_sum (n a b : ℕ) :
    6 * (∑ i ∈ range n, (a+i)*(b+i)) = productSum6 n a b := by
  induction n with
  | zero => simp [productSum6]
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add, ih]
    cases n with
    | zero => simp [productSum6, Nat.mul_assoc]
    | succ m => simp only [productSum6, Nat.succ_sub_one]; ring
private theorem count_sum (n : ℕ) :
    6 * (∑ i ∈ range n, (i+1)) = 3*n*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, Nat.mul_add, ih]; ring
theorem sum_after (f : ℕ → ℕ) (N s : ℕ) (hz : ∀ q < s, f q = 0) :
    (∑ q ∈ range N, f q) = ∑ i ∈ range (N-s), f (s+i) := by
  by_cases h : s ≤ N
  · conv_lhs => rw [← Nat.add_sub_of_le h, sum_range_add]
    rw [sum_eq_zero (fun q hq => hz q (mem_range.mp hq)), zero_add]
  · rw [Nat.sub_eq_zero_of_le (by omega : N ≤ s), sum_range_zero]
    exact sum_eq_zero fun q hq => hz q (by have := mem_range.mp hq; omega)
theorem ramp_count (N a : ℕ) :
    6 * (∑ q ∈ range N, ramp a q) = rampCount6 N a := by
  rw [sum_after (ramp a) N a (fun q hq => by unfold ramp; omega)]
  unfold rampCount6
  rw [← count_sum]
  congr 1
  exact sum_congr rfl fun i _ => by unfold ramp; omega
private theorem ramp_weight (N a : ℕ) :
    6 * (∑ q ∈ range N, q * ramp a q) = rampWeight6 N a := by
  rw [sum_after (fun q => q * ramp a q) N a
    (fun q hq => by rw [show ramp a q = 0 by unfold ramp; omega, mul_zero])]
  unfold rampWeight6
  rw [← product_sum]
  congr 1
  exact sum_congr rfl fun i _ => by
    rw [show ramp a (a+i) = 1+i by unfold ramp; omega]
private theorem ramp_excess (N k a : ℕ) :
    6 * (∑ q ∈ range N, (q-k) * ramp a q) = rampExcess6 N k a := by
  let s := max (k+1) a
  have hs₁ : k+1 ≤ s := le_max_left _ _
  have hs₂ : a ≤ s := le_max_right _ _
  have hz (q : ℕ) (hq : q < s) : (q-k) * ramp a q = 0 := by
    by_cases h : q ≤ k
    · rw [Nat.sub_eq_zero_of_le h, zero_mul]
    · rw [show ramp a q = 0 by dsimp [s, ramp] at *; omega, mul_zero]
  rw [sum_after _ N s hz]
  change _ = productSum6 (N-s) (s-k) (s+1-a)
  rw [← product_sum]
  congr 1
  exact sum_congr rfl fun i _ => by
    rw [show s+i-k = s-k+i by omega, show ramp a (s+i) = s+1-a+i by unfold ramp; omega]
private theorem column_row (B J t q : ℕ) :
    columnCount B J t q + ramp (low J t + width B J t) q = ramp (low J t) q := by
  unfold columnCount ramp width low high
  dsimp only
  omega
private theorem pivot_row (B J t q : ℕ) :
    pivotCount B J t q + ramp (low J t + peak B J t) q +
      ramp (edge B J t + 1 - peak B J t) q =
        ramp (low J t) q + ramp (edge B J t + 1) q := by
  have hc := column_row B J t q
  let a := low J t
  let e := edge B J t
  let w := width B J t
  let h := peak B J t
  change columnCount B J t q + ramp (a+w) q = ramp a q at hc
  have hae : a ≤ e := by dsimp [a, e, low, edge]; omega
  have hh : h = min w ((e-a+1)/2) := rfl
  have hp : pivotCount B J t q = min (columnCount B J t q) (e-q) := by
    unfold pivotCount
    rw [show B + 2*J - (t+q) = e-q by dsimp [e, edge]; omega]
  change pivotCount B J t q + ramp (a+h) q + ramp (e+1-h) q =
    ramp a q + ramp (e+1) q
  simp only [ramp] at hc ⊢
  by_cases hq : q < a+h
  · omega
  · by_cases hq' : q < e+1-h
    · omega
    · omega
private theorem pivot_volume (B J t : ℕ) (f stat : ℕ → ℕ)
    (hs : ∀ a, stat a = 6 * (∑ q ∈ range (B+1), f q * ramp a q)) :
    6 * (∑ q ∈ range (B+1), f q * pivotCount B J t q) = pivotVolume6 B J t stat := by
  unfold pivotVolume6
  simp only [hs]
  have heq :
      (∑ q ∈ range (B+1), (f q * pivotCount B J t q + f q * ramp (low J t + peak B J t) q +
        f q * ramp (edge B J t + 1 - peak B J t) q)) =
      ∑ q ∈ range (B+1), (f q * ramp (low J t) q + f q * ramp (edge B J t + 1) q) := by
    apply sum_congr rfl
    intro q _
    simp only [← Nat.mul_add, pivot_row]
  simp only [sum_add_distrib] at heq
  omega
theorem column_volume (B J t : ℕ) (f stat : ℕ → ℕ)
    (hs : ∀ a, stat a = 6 * (∑ q ∈ range (B+1), f q * ramp a q)) :
    6 * (∑ q ∈ range (B+1), f q * columnCount B J t q) = columnVolume6 B J t stat := by
  unfold columnVolume6
  simp only [hs]
  have heq :
      (∑ q ∈ range (B+1), (f q * columnCount B J t q + f q * ramp (low J t + width B J t) q)) =
      ∑ q ∈ range (B+1), f q * ramp (low J t) q := by
    apply sum_congr rfl
    intro q _
    rw [← Nat.mul_add, column_row]
  simp only [sum_add_distrib] at heq
  omega
theorem pivot_rank (B J t : ℕ) :
    6 * (∑ q ∈ range (B+1), pivotCount B J t q) = pivotRank6 B J t := by
  simpa only [one_mul, pivotRank6] using
    pivot_volume B J t (fun _ => 1) (rampCount6 (B+1))
      (fun a => by simpa only [one_mul] using (ramp_count (B+1) a).symm)
theorem pivot_weight (B J t : ℕ) :
    6 * (∑ q ∈ range (B+1), q * pivotCount B J t q) = pivotWeight6 B J t :=
  pivot_volume B J t id (rampWeight6 (B+1)) (fun a => (ramp_weight (B+1) a).symm)
theorem column_excess (B J t k : ℕ) :
    6 * (∑ q ∈ range (B+1), (q-k) * columnCount B J t q) = excess6 B J t k :=
  column_volume B J t (fun q => q-k) (rampExcess6 (B+1) k)
    (fun a => (ramp_excess (B+1) k a).symm)
private theorem threshold_le (B J t : ℕ) : threshold B J t ≤ B := by
  dsimp only [threshold]
  split
  · exact Nat.sub_le _ _
  · exact min_le_left _ _
theorem offset_bound (B J t : ℕ) : offsetMoment B J t ≤ offsetEstimate B J t := by
  let k := threshold B J t
  let R := ∑ q ∈ range (B+1), pivotCount B J t q
  let W := ∑ q ∈ range (B+1), q * pivotCount B J t q
  let E := ∑ q ∈ range (B+1), (q-k) * columnCount B J t q
  have hk : k ∈ range (B+1) := mem_range.mpr (Nat.lt_succ_of_le (threshold_le B J t))
  have htop : largestGradeSum B J t R ≤ R*k + E := by
    unfold largestGradeSum
    exact inf'_le _ hk
  change largestGradeSum B J t R - W ≤
    (pivotRank6 B J t * k + excess6 B J t k - pivotWeight6 B J t) / 6
  rw [← pivot_rank, ← pivot_weight, ← column_excess]
  change largestGradeSum B J t R - W ≤ (6*R*k + 6*E - 6*W) / 6
  rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_sub_left_distrib, Nat.mul_div_cancel_left _ (by decide)]
  exact Nat.sub_le_sub_right htop W
theorem evaluate_eq (f : ℕ → ℕ) (n : ℕ) : evaluate f n = ∑ t ∈ range n, f t := by
  induction n with
  | zero => simp [evaluate]
  | succ n ih => rw [evaluate, sum_range_succ, ih]
private theorem offset_zero (B J t : ℕ) (ht : t < J) : offsetMoment B J t = 0 := by
  have hp (q : ℕ) (hq : q ∈ range (B+1)) : pivotCount B J t q = columnCount B J t q := by
    have hq' := mem_range.mp hq
    have hc : columnCount B J t q ≤ t+1 := by
      dsimp only [columnCount]
      omega
    exact min_eq_left (hc.trans (by omega))
  unfold offsetMoment
  dsimp only
  apply Nat.sub_eq_zero_of_le
  calc
    _ ≤ (∑ q ∈ range (B+1), pivotCount B J t q)*0 +
        ∑ q ∈ range (B+1), (q-0) * columnCount B J t q := by
      unfold largestGradeSum
      exact inf'_le _ (mem_range.mpr (Nat.zero_lt_succ B))
    _ = _ := by
      simp only [mul_zero, Nat.sub_zero, zero_add]
      exact sum_congr rfl fun q hq => congrArg (q * ·) (hp q hq).symm
theorem grouped_bound (B J : ℕ) : groupedPoleMoment B J ≤ momentEstimate B J := by
  rw [momentEstimate, blockEstimate, evaluate_eq, groupedPoleMoment,
    show B+2*J = J+(B+J) by omega, sum_range_add,
    sum_eq_zero (fun t ht => offset_zero B J t (mem_range.mp ht)), zero_add]
  exact sum_le_sum fun t _ => offset_bound B J (J+t)
theorem evaluate_append {f : ℕ → ℕ} {a b n x y z : ℕ}
    (ha : evaluate f a = x) (hb : evaluate (fun t => f (a+t)) b = y)
    (hn : a+b = n) (hz : x+y = z) : evaluate f n = z := by
  rw [← hn, ← hz]
  have h := sum_range_add f a b
  simp only [← evaluate_eq] at h
  exact h.trans (congrArg₂ (· + ·) ha hb)
theorem block_append {B J start next a b n x y z : ℕ}
    (ha : blockEstimate B J start a = x) (hb : blockEstimate B J next b = y)
    (hs : start+a = next) (hn : a+b = n) (hz : x+y = z) :
    blockEstimate B J start n = z := by
  unfold blockEstimate at *
  rw [← hs] at hb
  exact evaluate_append ha (by simpa only [Nat.add_assoc] using hb) hn hz
end P1_7_1_3
end
section
namespace P1_7_1_3_2
open P1_7_1_3 (blockEstimate block_append momentEstimate)
def CheckedBlocks (B J : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | start, (length, total) :: rest =>
    blockEstimate B J start length = total ∧ CheckedBlocks B J (start + length) rest
private theorem block_total {B J : ℕ} (blocks : List (ℕ × ℕ)) (start : ℕ)
    (checked : CheckedBlocks B J start blocks) :
    blockEstimate B J start (blocks.map Prod.fst).sum = (blocks.map Prod.snd).sum := by
  induction blocks generalizing start with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨length, total⟩ := head
    exact block_append checked.1 (ih _ checked.2) rfl rfl rfl
theorem moment_from_blocks {B J total : ℕ} (blocks : List (ℕ × ℕ))
    (checked : CheckedBlocks B J J blocks)
    (length_eq : (blocks.map Prod.fst).sum = B + J)
    (total_eq : (blocks.map Prod.snd).sum = total) :
    momentEstimate B J = total := by
  rw [momentEstimate, ← length_eq, ← total_eq]
  exact block_total blocks J checked
class ExactMoment (B J total : ℕ) : Prop where
  eq_moment : momentEstimate B J = total
end P1_7_1_3_2
end
section
namespace P1_7_1_3_2
set_option maxRecDepth 4096
scoped instance : ExactMoment 500 105 1700679003 where
  eq_moment := by
    refine moment_from_blocks
      [(128,144037782),(128,567478208),(128,637814720),(128,319210721),
      (93,32137572)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 501 105 1711611949 where
  eq_moment := by
    refine moment_from_blocks
      [(128,144393518),(128,569377728),(128,641450944),(128,323182467),
      (94,33207292)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 521 117 2110154682 where
  eq_moment := by
    refine moment_from_blocks
      [(128,152229145),(128,646266176),(128,776764736),(128,455019674),
      (126,79874951)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 523 117 2136298939 where
  eq_moment := by
    refine moment_from_blocks
      [(128,152944225),(128,650314048),(128,784679232),(128,464485709),
      (128,83875725)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 535 112 2221379895 where
  eq_moment := by
    refine moment_from_blocks
      [(128,157045140),(128,658437440),(128,804697408),(128,501243104),
      (128,99930187),(7,26616)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 546 113 2387645191 where
  eq_moment := by
    refine moment_from_blocks
      [(128,161023860),(128,683587776),(128,852621504),(128,560448099),
      (128,129579472),(19,384480)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 547 109 2335147916 where
  eq_moment := by
    refine moment_from_blocks
      [(128,161134435),(128,671528000),(128,832828480),(128,546827594),
      (128,122589587),(16,239820)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 552 116 2523691858 where
  eq_moment := by
    refine moment_from_blocks
      [(128,163284615),(128,705699072),(128,893558016),(128,605669194),
      (128,154329076),(28,1151885)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 572 120 2904427648 where
  eq_moment := by
    refine moment_from_blocks
      [(128,170524574),(128,759701888),(128,997597568),(128,735310082),
      (128,234301265),(52,6992271)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 577 129 3158702492 where
  eq_moment := by
    refine moment_from_blocks
      [(128,172350880),(128,798366400),(128,1074191040),(128,813443001),
      (128,286344633),(66,14006538)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 578 117 2944634929 where
  eq_moment := by
    refine moment_from_blocks
      [(128,172608925),(128,761630528),(128,1002327872),(128,752644119),
      (128,247118139),(55,8305346)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 578 129 3176332897 where
  eq_moment := by
    refine moment_from_blocks
      [(128,172708640),(128,800496320),(128,1078450880),(128,819433681),
      (128,290590600),(67,14652776)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 580 119 3017027973 where
  eq_moment := by
    refine moment_from_blocks
      [(128,173369590),(128,772688640),(128,1023363840),(128,775246907),
      (128,262158826),(59,10200170)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 591 124 3308696108 where
  eq_moment := by
    refine moment_from_blocks
      [(128,177354875),(128,812312000),(128,1101080000),(128,868637578),
      (128,328555618),(75,20756037)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 597 126 3460443224 where
  eq_moment := by
    refine moment_from_blocks
      [(128,179505610),(128,831445632),(128,1139399296),(128,916997523),
      (128,365008090),(83,28087073)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 598 125 3457603226 where
  eq_moment := by
    refine moment_from_blocks
      [(128,179861955),(128,830265408),(128,1136826432),(128,916910704),
      (128,365601387),(83,28137340)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 607 139 3938005884 where
  eq_moment := by
    refine moment_from_blocks
      [(128,183083680),(128,891468085),(128,1268686720),(128,1061576997),
      (128,475434639),(106,57755763)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 609 128 3734056387 where
  eq_moment := by
    refine moment_from_blocks
      [(128,183799200),(128,863305152),(128,1203584448),(128,1003805395),
      (128,434638067),(97,44924125)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
end P1_7_1_3_2
end
section
namespace P1_7_1_3_2
set_option maxRecDepth 4096
scoped instance : ExactMoment 612 121 3630535593 where
  eq_moment := by
    refine moment_from_blocks
      [(128,184845250),(128,845461952),(128,1166277056),(128,975711462),
      (128,418227357),(93,40012516)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 613 121 3649568203 where
  eq_moment := by
    refine moment_from_blocks
      [(128,185202954),(128,847523264),(128,1170337216),(128,981727130),
      (128,423442731),(94,41334908)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 617 127 3870016120 where
  eq_moment := by
    refine moment_from_blocks
      [(128,186661280),(128,876941312),(128,1230311424),(128,1047177034),
      (128,473263516),(104,55661554)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 621 139 4237643334 where
  eq_moment := by
    refine moment_from_blocks
      [(128,188092320),(128,922329405),(128,1331657600),(128,1154779018),
      (128,556283521),(120,84501470)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 634 132 4351456177 where
  eq_moment := by
    refine moment_from_blocks
      [(128,192743200),(128,929702719),(128,1339363200),(128,1191222484),
      (128,599015438),(126,99409136)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 662 139 5203785784 where
  eq_moment := by
    refine moment_from_blocks
      [(128,202760480),(128,1012708985),(128,1516072320),(128,1432350080),
      (128,830129570),(128,207552923),(33,2211426)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 662 149 5491466699 where
  eq_moment := by
    refine moment_from_blocks
      [(128,202760480),(128,1040567045),(128,1591483200),(128,1514068800),
      (128,893654100),(128,244219046),(43,4714028)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 665 139 5279846034 where
  eq_moment := by
    refine moment_from_blocks
      [(128,203833760),(128,1019322125),(128,1529566080),(128,1452725120),
      (128,852255965),(128,219295492),(36,2847492)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 674 140 5543427992 where
  eq_moment := by
    refine moment_from_blocks
      [(128,207053600),(128,1042265009),(128,1578062976),(128,1522619520),
      (128,926834473),(128,260764188),(46,5828226)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 675 140 5569859382 where
  eq_moment := by
    refine moment_from_blocks
      [(128,207411360),(128,1044476175),(128,1582584000),(128,1529450688),
      (128,934549636),(128,265178067),(47,6209456)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 686 138 5800691370 where
  eq_moment := by
    refine moment_from_blocks
      [(128,211346720),(128,1062371996),(128,1615682624),(128,1586076736),
      (128,1007022200),(128,307734158),(56,10456936)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 726 153 7540240839 where
  eq_moment := by
    refine moment_from_blocks
      [(128,225657120),(128,1196811466),(128,1928242624),(128,2015290816),
      (128,1469051275),(128,625151582),(111,80035956)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 734 165 8281195601 where
  eq_moment := by
    refine moment_from_blocks
      [(128,228519200),(128,1244003969),(128,2067127616),(128,2199035200),
      (128,1649353090),(128,762657762),(128,130493632),(3,5132)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 740 167 8580372579 where
  eq_moment := by
    refine moment_from_blocks
      [(128,230665760),(128,1262245730),(128,2113698048),(128,2266462464),
      (128,1726864884),(128,824321763),(128,155995520),(11,118410)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 776 163 9809476816 where
  eq_moment := by
    refine moment_from_blocks
      [(128,243545120),(128,1337858951),(128,2261641344),(128,2502125696),
      (128,2055573998),(128,1110845387),(128,292335874),(43,5550446)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 779 173 10401501082 where
  eq_moment := by
    refine moment_from_blocks
      [(128,244618400),(128,1366300947),(128,2364345408),(128,2642299968),
      (128,2192053949),(128,1223114534),(128,356838378),(56,11929498)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 781 178 10721014375 where
  eq_moment := by
    refine moment_from_blocks
      [(128,245333920),(128,1380003801),(128,2416574464),(128,2715713536),
      (128,2266117448),(128,1285945362),(128,394514228),(63,16811616)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 782 178 10765253509 where
  eq_moment := by
    refine moment_from_blocks
      [(128,245691680),(128,1382396018),(128,2421878592),(128,2723950400),
      (128,2277127269),(128,1296134164),(128,400457082),(64,17618304)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
end P1_7_1_3_2
end
section
namespace P1_7_1_3_2
set_option maxRecDepth 4096
scoped instance : ExactMoment 783 165 10192726271 where
  eq_moment := by
    refine moment_from_blocks
      [(128,246049440),(128,1358944053),(128,2314921792),(128,2580096832),
      (128,2149468958),(128,1194949591),(128,338612451),(52,9683154)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 784 164 10186247915 where
  eq_moment := by
    refine moment_from_blocks
      [(128,246407200),(128,1358949795),(128,2310908160),(128,2575837440),
      (128,2149048385),(128,1196318864),(128,339082164),(52,9695907)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 792 167 10673329627 where
  eq_moment := by
    refine moment_from_blocks
      [(128,249269280),(128,1384644162),(128,2378713344),(128,2674608384),
      (128,2266006484),(128,1302457939),(128,400572546),(63,17057488)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 808 165 11274483946 where
  eq_moment := by
    refine moment_from_blocks
      [(128,254993440),(128,1417586953),(128,2441347392),(128,2774516032),
      (128,2411430208),(128,1452816319),(128,490659052),(77,31134550)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 821 188 13132884772 where
  eq_moment := by
    refine moment_from_blocks
      [(128,259644320),(128,1491434191),(128,2714935104),(128,3170131776),
      (128,2832620376),(128,1824571448),(128,743401218),(113,96146339)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 822 188 13184443531 where
  eq_moment := by
    refine moment_from_blocks
      [(128,260002080),(128,1493853093),(128,2720414592),(128,3178707840),
      (128,2844287584),(128,1836656028),(128,751766439),(114,98755875)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 825 173 12507204741 where
  eq_moment := by
    refine moment_from_blocks
      [(128,261075360),(128,1475597499),(128,2604081216),(128,3013173312),
      (128,2692456512),(128,1721466865),(128,667497478),(102,71856499)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 828 189 13552061015 where
  eq_moment := by
    refine moment_from_blocks
      [(128,262148640),(128,1509721915),(128,2761675840),(128,3242628160),
      (128,2926662720),(128,1920285208),(128,810698549),(121,118239983)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 853 192 15095933357 where
  eq_moment := by
    refine moment_from_blocks
      [(128,271092640),(128,1574237488),(128,2925089472),(128,3497431744),
      (128,3260273344),(128,2274160185),(128,1071003387),(128,221846864),
      (21,798233)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 856 174 14142442253 where
  eq_moment := by
    refine moment_from_blocks
      [(128,272165920),(128,1551390955),(128,2775528000),(128,3277288000),
      (128,3045044800),(128,2111237198),(128,945222943),(128,164535408),
      (6,29029)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 882 186 16399828679 where
  eq_moment := by
    refine moment_from_blocks
      [(128,281467680),(128,1635894932),(128,3030381376),(128,3664589632),
      (128,3514463040),(128,2598697640),(128,1325282868),(128,342290592),
      (44,6760919)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 883 197 17210339526 where
  eq_moment := by
    refine moment_from_blocks
      [(128,281825440),(128,1653196253),(128,3135857472),(128,3828458304),
      (128,3690586944),(128,2749316070),(128,1446953881),(128,410568928),
      (56,13576234)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 912 194 18868434791 where
  eq_moment := by
    refine moment_from_blocks
      [(128,292200480),(128,1720155840),(128,3271220160),(128,4041186240),
      (128,3993263040),(128,3133663239),(128,1774996188),(128,599346999),
      (82,42402605)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 926 195 19894196946 where
  eq_moment := by
    refine moment_from_blocks
      [(128,297209120),(128,1755504711),(128,3358888064),(128,4179366016),
      (128,4177760384),(128,3356603776),(128,1974410087),(128,724289538),
      (97,70165250)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 958 195 22186492210 where
  eq_moment := by
    refine moment_from_blocks
      [(128,308657440),(128,1833375943),(128,3537916032),(128,4461154432),
      (128,4562309248),(128,3841387932),(128,2439290735),(128,1036067666),
      (128,166331824),(1,958)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 960 205 23224363038 where
  eq_moment := by
    refine moment_from_blocks
      [(128,309372960),(128,1849612615),(128,3645738560),(128,4639706688),
      (128,4769648192),(128,4035677606),(128,2602917483),(128,1155992984),
      (128,215455408),(13,240542)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 968 204 23761225895 where
  eq_moment := by
    refine moment_from_blocks
      [(128,312235040),(128,1868238645),(128,3682311680),(128,4696645120),
      (128,4851146240),(128,4145818989),(128,2716742287),(128,1237702419),
      (128,249594080),(20,791395)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
scoped instance : ExactMoment 996 207 26338011946 where
  eq_moment := by
    refine moment_from_blocks
      [(128,322252320),(128,1939676596),(128,3872068096),(128,5001777664),
      (128,5259072000),(128,4643951104),(128,3228690796),(128,1623238100),
      (128,435562624),(51,11722646)] ?_ rfl rfl
    exact ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), True.intro⟩
end P1_7_1_3_2
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate block_append)
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
end P1_7_1_3_3
end
section
namespace P1_7_1_3_3
open P1_7_1_3 (blockEstimate momentEstimate)
set_option maxRecDepth 4000
end P1_7_1_3_3
end
section
namespace P1_7_1_3_5
open P1_7_1_3 (blockEstimate block_append momentEstimate)
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
end P1_7_1_3_5
end
section
namespace P1_7_1_3_5
open P1_7_1_3 (blockEstimate block_append momentEstimate)
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
end P1_7_1_3_5
end
section
namespace P1_7_1_3_5
open P1_7_1_3 (blockEstimate block_append momentEstimate)
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
end P1_7_1_3_5
end
section
namespace P1_7_1_3_6
open P1_7_1_3 (blockEstimate block_append)
end P1_7_1_3_6
end
section
namespace P1_7_1_3_6
open P1_7_1_3 (blockEstimate block_append momentEstimate)
set_option maxRecDepth 8000
end P1_7_1_3_6
end

end Merged6967_UpperBranch1

section Merged6967_UpperBranch6
set_option Elab.async false

set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_6
open Finset
open K1_14 (Shape triangle)
open P1 (HighBand agreement)
open P1_7 (Bank Test debit  tested  )
def width (s : Shape) (h q j t : ℕ) : ℤ :=
  (s.m * agreement : ℕ) + (j : ℤ) - (131071 - (h : ℤ)) * q - 2 * (h : ℤ) * t
def orderEnd (s : Shape) (E v : ℕ) : ℕ :=
  if v = 0 then s.B/E+1 else min (s.B/E+1) (s.U/v+1)
def linearEnd (base step bound cap : ℕ) : ℕ :=
  if base < bound then
    if step = 0 then cap else min cap ((bound - 1 - base)/step + 1)
  else 0
structure Quad where
  constant : ℤ
  linear : ℤ
  square : ℤ
def Quad.eval (p : Quad) (a : ℤ) : ℤ :=
  p.constant + p.linear*a + p.square*a*a
def Quad.ofLines (x y z w : ℤ) : Quad :=
  ⟨x*z, x*w+y*z, y*w⟩
def prefixProduct (p q : Quad) (n : ℕ) : ℤ :=
  let x : ℤ := n
  let t := x*(x-1)
  let u := t*(2*x-1)
  60*x*(p.constant*q.constant) +
    30*t*(p.constant*q.linear+p.linear*q.constant) +
    10*u*(p.constant*q.square+p.linear*q.linear+p.square*q.constant) +
    15*t*t*(p.linear*q.square+p.square*q.linear) +
    2*u*(3*t-1)*(p.square*q.square)
def intervalProduct (p q : Quad) (L R : ℕ) : ℤ :=
  if L < R then prefixProduct p q R - prefixProduct p q L else 0
def seedEnd (s : Shape) (v d R : ℕ) : ℕ :=
  if v = 0 then R else min R (s.U/v+1-d)
def yStart (E d t : ℕ) := t+E*d
def seedQuad (s : Shape) (v d : ℕ) : Quad :=
  let u : ℤ := (s.U : ℤ) - (v : ℤ)*d
  Quad.ofLines (u+1) (-(v : ℤ)) (u+2) (-(v : ℤ))
def scaledDebit (s : Shape) (N P h : ℕ) : ℤ :=
  240*((triangle s.U : ℤ)*N + 2*(h : ℤ)*(s.U+1)*P)
end P1_7_6
end
section
namespace P1_7_6
open Finset
open K1_14 (Shape shapeSum slots)
open P1 (agreement)
open P1_7 (Bank debit )
theorem width_cast (s : Shape) (h q j t : ℕ) (hh : h ≤ 131071) :
    (↑(s.m * agreement + j - q * (131071-h) - 2*h*t : ℕ) : ℤ) =
      max 0 (width s h q j t) := by
  rw [Nat.sub_sub]
  have hd : (↑(131071-h : ℕ) : ℤ) = 131071 - h := Nat.cast_sub hh
  have he : (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(q*(131071-h)+2*h*t : ℕ) : ℤ) =
      width s h q j t := by
    simp only [width, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hd]
    ring
  generalize s.m*agreement+j = x at *
  generalize q*(131071-h)+2*h*t = y at *
  by_cases hxy : y ≤ x
  · rw [Int.ofNat_sub hxy, he, max_eq_right (by omega)]
  · have hz : x-y = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, Int.ofNat_zero, max_eq_left (by omega)]
theorem rise_of_convex {f : ℕ → ℤ} {lo h : ℕ}
    (hc : ∀ n < h, f (n+1) + f (n+1) ≤ f n + f (n+2))
    (hl : lo ≤ h) (hf : f lo ≤ f (lo+1)) :
    f lo ≤ f h ∧ f h ≤ f (h+1) := by
  induction h with
  | zero =>
    have he : lo = 0 := by omega
    subst lo
    exact ⟨le_rfl, hf⟩
  | succ h ih =>
    rcases Nat.lt_or_eq_of_le hl with hlt | he
    · obtain ⟨hh, hs⟩ := ih (fun n hn => hc n (by omega)) (by omega)
      have ht := hc h (by omega)
      exact ⟨hh.trans hs, by rw [show h+1+1 = h+2 by omega]; omega⟩
    · subst lo
      exact ⟨le_rfl, hf⟩
end P1_7_6
end
section
namespace P1_7_6
open Finset
open K1_14 (Shape shapeSum slots triangle)
theorem slots_anti (U : ℕ) : Antitone (slots U) := by
  intro a b hab
  unfold slots
  split_ifs with ha hb hb
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul (by omega) (by omega)
  all_goals omega
theorem sum_range_guard {f : ℕ → ℤ} (L R : ℕ)
    (hz : ∀ a, R ≤ a → a < L → f a = 0) :
    ∑ a ∈ range L, f a = ∑ a ∈ range R, if a < L then f a else 0 := by
  have hf : (range R).filter (· < L) = range (min L R) := by
    ext a
    simp only [mem_range, mem_filter, lt_min_iff]
    tauto
  rw [← sum_filter, hf]
  symm
  apply sum_subset (range_mono (min_le_left _ _))
  intro a ha hnot
  simp only [mem_range, lt_min_iff] at ha hnot
  exact hz a (by omega) ha
private theorem position_phases (s : Shape) (h E v q j : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (hq : q ≤ s.B) (hj : j ≤ q) :
    let c := fun a => slots s.U (a*v)
    let x := s.m*P1.agreement+j-q*(131071-h)
    let g := (q-j)/E
    let f := fun d a => (c (a+d) : ℤ)*max 0 (width s h q j (j+a))
    (↑((∑ a ∈ range g, (c a - c (a+1))*(x-2*h*(j+a))) + c g*(x-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+0) ≤ q then f 0 a else 0) -
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+1) ≤ q then f 1 a else 0) := by
  dsimp only
  let g := (q-j)/E
  let f := fun d a => (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a))
  have step (a : ℕ) : slots s.U ((a+1)*v) ≤ slots s.U (a*v) :=
    slots_anti _ (Nat.mul_le_mul_right v (by omega))
  have hdiff :
      (↑((∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v)) *
          (s.m*P1.agreement+j-q*(131071-h)-2*h*(j+a))) +
        slots s.U (g*v)*(s.m*P1.agreement+j-q*(131071-h)-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (g+1), f 0 a) - ∑ a ∈ range g, f 1 a := by
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sum]
    rw [show (∑ a ∈ range g, f 0 a) + f 0 g - (∑ a ∈ range g, f 1 a) =
        ((∑ a ∈ range g, f 0 a) - (∑ a ∈ range g, f 1 a)) + f 0 g by ring,
      ← sum_sub_distrib]
    simp only [Nat.cast_mul, width_cast s h _ _ _ hh, f, Nat.add_zero]
    have hs (a : ℕ) :
        (↑(slots s.U (a*v) - slots s.U ((a+1)*v) : ℕ) : ℤ) =
          (slots s.U (a*v) : ℤ) - slots s.U ((a+1)*v) := Int.ofNat_sub (step a)
    simp only [hs, sub_mul]
  rw [hdiff]
  have hz (d a : ℕ) (ha : orderEnd s E v ≤ a) (hg : a+d ≤ g) : f d a = 0 := by
    have hcap : g ≤ s.B/E := Nat.div_le_div_right (by omega)
    have hab : a < s.B/E+1 := by omega
    unfold orderEnd at ha
    split at ha
    · omega
    · rename_i hv
      have hlarge : s.U/v < a+d := by omega
      have hout : s.U < (a+d)*v := by
        by_contra! hm
        exact (Nat.not_le_of_lt hlarge) ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)).2 hm)
      simp [f, slots, Nat.not_le_of_lt hout]
  have hdiv (a d : ℕ) : j+E*(a+d) ≤ q ↔ a+d ≤ g := by
    rw [Nat.le_div_iff_mul_le he, Nat.mul_comm (a+d) E]
    omega
  rw [sum_range_guard (g+1) _ (fun a ha hb => hz 0 a ha (by omega)),
    sum_range_guard g _ (fun a ha hb => hz 1 a ha (by omega))]
  have hzero (a : ℕ) : j+E*a ≤ q ↔ a ≤ g := by simpa using hdiv a 0
  simp only [hzero, Nat.add_zero, Nat.lt_succ_iff, Nat.add_one_le_iff, f]
private theorem phaseQ_expand (s : Shape) (h E v d q : ℕ) :
    (∑ j ∈ range (min q s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a)) else 0) =
    ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a)) else 0 := by
  apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
  intro j hj hnot
  simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
  apply sum_eq_zero
  intro a _
  rw [ite_eq_right (by omega)]
theorem diagonal (J R : ℕ) (f : ℕ → ℕ → ℤ) :
    (∑ j ∈ range (J+1), ∑ a ∈ range (R+1), f j a) =
      ∑ t ∈ range (J+R+1), ∑ a ∈ Ico (t-J) (min t R+1), f (t-a) a := by
  calc
    _ = ∑ a ∈ range (R+1), ∑ j ∈ range (J+1), f j a := sum_comm
    _ = ∑ a ∈ range (R+1), ∑ t ∈ Ico a (a+(J+1)), f (t-a) a := by
      apply sum_congr rfl
      intro a _
      rw [sum_Ico_eq_sum_range]
      simp
    _ = ∑ a ∈ range (R+1), ∑ t ∈ range (J+R+1),
        if a ≤ t ∧ t-a ≤ J then f (t-a) a else 0 := by
      apply sum_congr rfl
      intro a ha
      have ha' := mem_range.mp ha
      rw [← sum_filter]
      congr 1
      ext t
      simp only [mem_Ico, mem_filter, mem_range]
      omega
    _ = ∑ t ∈ range (J+R+1), ∑ a ∈ range (R+1),
        if a ≤ t ∧ t-a ≤ J then f (t-a) a else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [← sum_filter]
      congr 1
      ext a
      simp only [mem_Ico, mem_filter, mem_range, Nat.lt_succ_iff, le_min_iff]
      omega
end P1_7_6
end
section
namespace P1_7_6
open Finset
open P1 (agreement)
open K1_14 (Shape)
open K1_14_2_1 (twice_sum_linear)
theorem lt_linearEnd (base step bound cap i : ℕ) :
    i < linearEnd base step bound cap ↔ i < cap ∧ base + step*i < bound := by
  unfold linearEnd
  by_cases hb : base < bound
  · rw [ite_eq_left hb]
    by_cases hs : step = 0
    · simp [hs, hb]
    · rw [ite_eq_right hs, lt_min_iff, Nat.lt_succ_iff,
        Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hs), Nat.mul_comm i step]
      omega
  · rw [ite_eq_right hb]
    omega
end P1_7_6
end
section
namespace P1_7_6
open Finset
theorem Quad.eval_ofLines (x y z w a : ℤ) :
    (Quad.ofLines x y z w).eval a = (x+y*a)*(z+w*a) := by
  unfold Quad.ofLines Quad.eval
  dsimp only
  ring
private theorem prefix_eq (p q : Quad) (n : ℕ) :
    60 * (∑ a ∈ range n, p.eval a * q.eval a) = prefixProduct p q n := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [prefixProduct, Quad.eval, Nat.cast_succ]
    ring
theorem intervalProduct_eq (p q : Quad) (L R : ℕ) :
    60 * (∑ a ∈ Ico L R, p.eval a * q.eval a) = intervalProduct p q L R := by
  unfold intervalProduct
  by_cases h : L < R
  · rw [ite_eq_left h, sum_Ico_eq_sub _ h.le, mul_sub, prefix_eq, prefix_eq]
  · rw [ite_eq_right h, Ico_eq_empty_of_le (Nat.le_of_not_gt h), sum_empty, mul_zero]
end P1_7_6
end
section
namespace P1_7_6_4
open Finset
open P1_7_6 (Quad)
structure Line where
  base : ℤ
  slope : ℤ
def Line.at (l : Line) (a : ℤ) : ℤ := l.base+l.slope*a
def Line.sub (l r : Line) : Line := ⟨l.base-r.base,l.slope-r.slope⟩
def Line.addConst (l : Line) (c : ℤ) : Line := ⟨l.base+c,l.slope⟩
def Line.scale (l : Line) (c : ℤ) : Line := ⟨c*l.base,c*l.slope⟩
def Line.shift (l r : Line) (c : ℤ) : Line := ⟨l.base+c*r.base,l.slope+c*r.slope⟩
structure Cubic where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
def Cubic.at (p : Cubic) (a : ℤ) : ℤ := p.c0+p.c1*a+p.c2*a^2+p.c3*a^3
def Cubic.lines (x y z : Line) : Cubic :=
  let q := Quad.ofLines x.base x.slope y.base y.slope
  ⟨q.constant*z.base, q.constant*z.slope+q.linear*z.base,
    q.linear*z.slope+q.square*z.base, q.square*z.slope⟩
theorem Cubic.lines_at (x y z : Line) (a : ℤ) :
    (Cubic.lines x y z).at a = x.at a * y.at a * z.at a := by
  simp only [Cubic.lines, Cubic.at, Quad.ofLines, Line.at]
  ring
def windowCubic (L R xLine yLine : Line) (b d : ℤ) : Cubic :=
  let n := R.sub L
  let x := xLine.shift L b
  let y := yLine.shift L d
  let m := n.addConst (-1)
  let w := (n.scale 2).addConst (-1)
  let f := Cubic.lines n x y
  let g := Cubic.lines n m (x.scale d |>.shift y b)
  let k := Cubic.lines n m w
  ⟨6*f.c0+3*g.c0+b*d*k.c0, 6*f.c1+3*g.c1+b*d*k.c1,
    6*f.c2+3*g.c2+b*d*k.c2, 6*f.c3+3*g.c3+b*d*k.c3⟩
private theorem windowCubic_at (L R xLine yLine : Line) (b d a : ℤ) :
    (windowCubic L R xLine yLine b d).at a =
      let n := R.at a-L.at a
      let x := xLine.at a+b*L.at a
      let y := yLine.at a+d*L.at a
      6*n*x*y+3*n*(n-1)*(d*x+b*y)+b*d*n*(n-1)*(2*n-1) := by
  simp only [windowCubic, Cubic.at]
  let f := Cubic.lines (R.sub L) (xLine.shift L b) (yLine.shift L d)
  let g := Cubic.lines (R.sub L) ((R.sub L).addConst (-1))
    (((xLine.shift L b).scale d).shift (yLine.shift L d) b)
  let k := Cubic.lines (R.sub L) ((R.sub L).addConst (-1)) (((R.sub L).scale 2).addConst (-1))
  change (6*f.c0+3*g.c0+b*d*k.c0) + (6*f.c1+3*g.c1+b*d*k.c1)*a +
    (6*f.c2+3*g.c2+b*d*k.c2)*a^2 + (6*f.c3+3*g.c3+b*d*k.c3)*a^3 = _
  trans 6*f.at a+3*g.at a+b*d*k.at a
  · unfold Cubic.at
    ring
  simp only [f, g, k, Cubic.lines_at, Line.at, Line.sub, Line.shift, Line.addConst, Line.scale]
  ring
private theorem linePair_range (x y b d : ℤ) (n : ℕ) :
    6*(∑ t ∈ range n, (x+b*t)*(y+d*t)) =
      6*(n : ℤ)*x*y+3*n*(n-1)*(d*x+b*y)+b*d*n*(n-1)*(2*n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
    ring
theorem windowCubic_eq (L R xLine yLine : Line) (b d a : ℤ) (l r : ℕ)
    (hl : L.at a = l) (hr : R.at a = r) (hle : l ≤ r) :
    (windowCubic L R xLine yLine b d).at a =
      6*(∑ t ∈ Ico l r, (xLine.at a+b*t)*(yLine.at a+d*t)) := by
  rw [windowCubic_at, hl, hr, sum_Ico_eq_sum_range]
  have hs : (∑ t ∈ range (r-l), (xLine.at a+b*(↑(l+t) : ℤ))*(yLine.at a+d*(↑(l+t) : ℤ))) =
      ∑ t ∈ range (r-l), ((xLine.at a+b*l)+b*t)*((yLine.at a+d*l)+d*t) := by
    apply sum_congr rfl
    intro t _
    push_cast
    ring
  rw [hs, linePair_range, Nat.cast_sub hle]
def prefixCubic (p : Quad) (q : Cubic) (n : ℕ) : ℤ :=
  let x : ℤ := n
  let t := x*(x-1)
  let u := t*(2*x-1)
  60*x*(p.constant*q.c0) +
    30*t*(p.constant*q.c1+p.linear*q.c0) +
    10*u*(p.constant*q.c2+p.linear*q.c1+p.square*q.c0) +
    15*t*t*(p.constant*q.c3+p.linear*q.c2+p.square*q.c1) +
    2*u*(3*t-1)*(p.linear*q.c3+p.square*q.c2) +
    5*t*t*(2*t-1)*(p.square*q.c3)
theorem prefix_eq (p : Quad) (q : Cubic) (n : ℕ) :
    prefixCubic p q n = 60*(∑ a ∈ range n, p.eval a * q.at a) := by
  induction n with
  | zero => simp [prefixCubic]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← ih]
    simp only [prefixCubic, Quad.eval, Cubic.at, Nat.cast_succ]
    ring
end P1_7_6_4
end
section
namespace P1_7_6_4
open Finset
open K1_14 (Shape)
open P1 (agreement)
open P1_7_6
structure Core where
  column : ℕ
  offset : ℕ
  step : ℕ
  cap : ℕ
  seed : Quad
  countLine : Line
  widthLine : Line
  widthSlope : ℤ
def Core.term (C : Core) (a t : ℕ) : ℤ :=
  (C.countLine.at a-t)*(C.widthLine.at a+C.widthSlope*t)
def Core.slice (C : Core) (x c a : ℕ) : Finset ℕ :=
  Ico (a+c) (min x (C.column-(C.offset+C.step*a)))
def Core.nonemptyEnd (C : Core) (x c : ℕ) : ℕ :=
  linearEnd (c+C.offset) (C.step+1) C.column (min C.cap (x-c))
def Core.switchEnd (C : Core) (x c : ℕ) : ℕ :=
  linearEnd (x+C.offset) C.step (C.column+1) (C.nonemptyEnd x c)
private theorem lt_nonemptyEnd (C : Core) (x c a : ℕ) :
    a < C.nonemptyEnd x c ↔ a < C.cap ∧ a+c < min x (C.column-(C.offset+C.step*a)) := by
  rw [Core.nonemptyEnd, lt_linearEnd, lt_min_iff, lt_min_iff, Nat.add_mul, Nat.one_mul]
  omega
private theorem lt_switchEnd (C : Core) (x c a : ℕ) :
    a < C.switchEnd x c ↔ a < C.nonemptyEnd x c ∧ x+C.offset+C.step*a ≤ C.column := by
  rw [Core.switchEnd, lt_linearEnd, Nat.lt_succ_iff]
def cubicInterval (p : Quad) (q : Cubic) (l r : ℕ) : ℤ :=
  if l < r then prefixCubic p q r - if l = 0 then 0 else prefixCubic p q l else 0
private theorem cubicInterval_eq (p : Quad) (q : Cubic) (l r : ℕ) :
    cubicInterval p q l r = 60*(∑ a ∈ Ico l r, p.eval a*q.at a) := by
  unfold cubicInterval
  by_cases h : l < r
  · rw [ite_eq_left h, sum_Ico_eq_sub _ h.le, mul_sub, ← prefix_eq, ← prefix_eq]
    split
    · subst l
      simp [prefixCubic]
    · rfl
  · rw [ite_eq_right h, Ico_eq_empty_of_le (by omega), sum_empty, mul_zero]
def Core.window (C : Core) (x c : ℕ) : ℤ :=
  let b := C.switchEnd x c
  let n := C.nonemptyEnd x c
  let L : Line := ⟨c,1⟩
  let fixed : Line := ⟨x,0⟩
  let falling : Line := ⟨(C.column : ℤ)-C.offset,-(C.step : ℤ)⟩
  let f := fun R => windowCubic L R C.countLine C.widthLine (-1) C.widthSlope
  cubicInterval C.seed (f fixed) 0 b + cubicInterval C.seed (f falling) b n
theorem Core.window_eq (C : Core) (x c : ℕ) :
    C.window x c = 360*(∑ a ∈ range C.cap, C.seed.eval a * ∑ t ∈ C.slice x c a, C.term a t) := by
  let n := C.nonemptyEnd x c
  let b := C.switchEnd x c
  let f := fun a : ℕ => C.seed.eval a * ∑ t ∈ C.slice x c a, C.term a t
  have hb : b ≤ n := Nat.le_of_not_gt fun h => (Nat.lt_irrefl _) ((lt_switchEnd C x c n).mp h).1
  have hn : n ≤ C.cap := Nat.le_of_not_gt fun h => (Nat.lt_irrefl _) ((lt_nonemptyEnd C x c C.cap).mp h).1
  have hs : (∑ a ∈ range n, f a) = ∑ a ∈ range C.cap, f a := by
    apply sum_subset (range_subset_range.mpr hn)
    intro a ha ha'
    have ha := mem_range.mp ha
    have hz : min x (C.column-(C.offset+C.step*a)) ≤ a+c := by
      by_contra! h
      exact ha' (mem_range.mpr ((lt_nonemptyEnd C x c a).mpr ⟨ha,h⟩))
    simp [f, Core.slice, Ico_eq_empty_of_le hz]
  rw [← hs, ← sum_range_add_sum_Ico f hb, mul_add]
  simp only [Core.window, ← Nat.Ico_zero_eq_range b, cubicInterval_eq]
  change 60*(∑ a ∈ Ico 0 b, _) + 60*(∑ a ∈ Ico b n, _) =
    360*(∑ a ∈ Ico 0 b, f a) + 360*(∑ a ∈ Ico b n, f a)
  have hmul : (360 : ℤ) = 60*6 := rfl
  rw [hmul]
  simp only [mul_assoc, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro a ha
    have hab := (mem_Ico.mp ha).2
    obtain ⟨han,hfix⟩ := (lt_switchEnd C x c a).mp hab
    have hav := ((lt_nonemptyEnd C x c a).mp han).2
    rw [show min x (C.column-(C.offset+C.step*a)) = x by omega] at hav
    have hv := windowCubic_eq ⟨(c : ℤ),1⟩ ⟨(x : ℤ),0⟩ C.countLine C.widthLine (-1)
      C.widthSlope a (a+c) x (by simp [Line.at, add_comm]) (by simp [Line.at]) hav.le
    rw [hv]
    simp only [f, Core.slice, min_eq_left (by omega : x ≤ C.column-(C.offset+C.step*a)), Core.term]
    simp only [neg_one_mul, ← sub_eq_add_neg]
    ring
  · apply sum_congr rfl
    intro a ha
    obtain ⟨ha₁,ha₂⟩ := mem_Ico.mp ha
    have hav := ((lt_nonemptyEnd C x c a).mp ha₂).2
    have hfall : C.column-(C.offset+C.step*a) ≤ x := by
      by_contra! h
      exact (not_lt_of_ge ha₁) ((lt_switchEnd C x c a).mpr ⟨ha₂,by omega⟩)
    have hle : C.offset+C.step*a ≤ C.column := by omega
    rw [min_eq_right hfall] at hav
    have hv := windowCubic_eq ⟨(c : ℤ),1⟩
      ⟨(C.column : ℤ)-C.offset,-(C.step : ℤ)⟩ C.countLine C.widthLine (-1)
      C.widthSlope a (a+c) (C.column-(C.offset+C.step*a))
      (by simp [Line.at, add_comm])
      (by simp only [Line.at, Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]; ring) hav.le
    rw [hv]
    simp only [f, Core.slice, min_eq_right hfall, Core.term]
    simp only [neg_one_mul, ← sub_eq_add_neg]
    ring
theorem Core.prefix_eq (C : Core) (x J : ℕ) :
    C.window x 0 - C.window x (J+1) =
      360*(∑ t ∈ range x, ∑ a ∈ range C.cap,
        if a ≤ t ∧ t < a+(J+1) ∧ t+(C.offset+C.step*a) < C.column
        then C.seed.eval a*C.term a t else 0) := by
  rw [Core.window_eq, Core.window_eq, ← mul_sub, sum_comm (s := range x), ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro a _
  have hfilter (c : ℕ) :
      C.slice x c a = (range x).filter
        (fun t => a+c ≤ t ∧ t+(C.offset+C.step*a) < C.column) := by
    ext t
    simp only [Core.slice, mem_Ico, lt_min_iff, mem_filter, mem_range]
    omega
  simp_rw [hfilter, mul_sum, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  by_cases hl : a ≤ t <;> by_cases hu : t < a+(J+1) <;>
    by_cases hk : t+(C.offset+C.step*a) < C.column <;>
    have hu' : a+(J+1) ≤ t ↔ ¬t < a+(J+1) := by omega
  all_goals omega
end P1_7_6_4
end
section
namespace P1_7_6
open Finset
open P1 (agreement)
open K1_14 (Shape slots triangle)
open P1_7 (debit)
theorem lt_seedEnd (s : Shape) (v d R a : ℕ) :
    a < seedEnd s v d R ↔ a < R ∧ (a+d)*v ≤ s.U := by
  unfold seedEnd
  by_cases hv : v = 0
  · simp [hv]
  · rw [ite_eq_right hv, lt_min_iff, ← Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)]
    omega
theorem yStart_eq (E d t a : ℕ) (he : 0 < E) (ha : a ≤ t) :
    t-a+E*(a+d) = yStart E d t + (E-1)*a := by
  apply Int.ofNat_inj.mp
  simp only [yStart, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ha, Nat.cast_sub he, Nat.cast_one]
  ring
theorem seedQuad_eq (s : Shape) (v d a : ℕ) (ha : (a+d)*v ≤ s.U) :
    (seedQuad s v d).eval a = 2*(slots s.U ((a+d)*v) : ℤ) := by
  let n := s.U-(a+d)*v
  have hc : (n : ℤ) = (s.U : ℤ)-((a : ℤ)+d)*v := by
    simp only [n, Nat.cast_sub ha, Nat.cast_add, Nat.cast_mul]
  have hp : ((n : ℤ)+1)*((n : ℤ)+2) = 2*(triangle n : ℤ) := by
    have ht := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self (n+1)))
    change (n+1)*(n+2)/2*2 = (n+1)*(n+2) at ht
    have hz := congrArg (fun k : ℕ => (k : ℤ)) ht
    change (↑(triangle n*2 : ℕ) : ℤ) = (↑((n+1)*(n+2) : ℕ) : ℤ) at hz
    push_cast at hz
    linarith
  rw [slots, ite_eq_left ha]
  change _ = 2*(triangle n : ℤ)
  rw [← hp, hc, seedQuad, Quad.eval_ofLines]
  ring
theorem sum_clipped {f g : ℕ → ℤ} {L R T : ℕ}
    (hr : ∀ a, a < T → a < R)
    (hz : ∀ a ∈ Ico L R, T ≤ a → f a = 0)
    (he : ∀ a ∈ Ico L T, f a = g a) :
    (∑ a ∈ Ico L R, f a) = ∑ a ∈ Ico L T, g a := by
  calc
    _ = ∑ a ∈ Ico L T, f a := by
      symm
      apply sum_subset
      · intro a ha
        exact mem_Ico.mpr ⟨(mem_Ico.mp ha).1, hr a (mem_Ico.mp ha).2⟩
      · intro a ha hn
        exact hz a ha (le_of_not_gt fun h => hn (mem_Ico.mpr ⟨(mem_Ico.mp ha).1,h⟩))
    _ = _ := sum_congr rfl he
end P1_7_6
end
section
namespace P1_7_6_4
open Finset
open K1_14 (Shape)
open P1 (agreement)
open P1_7_6
open P1_7_6 (lt_seedEnd)
def diagonalCore (C : Core) (J t : ℕ) : ℤ :=
  ∑ a ∈ range C.cap,
    if a ≤ t ∧ t < a+(J+1) ∧ t+(C.offset+C.step*a) < C.column
    then C.seed.eval a*C.term a t else 0
def corePrefix (C : Core) (J x : ℕ) : ℤ := C.window x 0 - C.window x (J+1)
end P1_7_6_4
end

end Merged6967_UpperBranch6

section Merged6967_Wide50EulerPrimaryFamily
set_option Elab.async false




set_option Elab.async false

-- merged module PrimaryTaperMoments
section Merged_PrimaryTaperMoments

set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace TaperMoments

open K1_13_2 (denominator cumulative)
open K1_13_2_2 (cumulativeColumns oldWeight CumulativeCount)
open TaperBudget (cap)
open Finset
open scoped BigOperators

open K1_13_2_3 (scaled_denominator polyDen denominator_of_neg)

/-- Twenty-four times the sum of the denominator counts at indices strictly below `n`. -/
def denPrefix (n : ℤ) : ℤ :=
  if n < 0 then 0 else
    let q := n / 6
    let r := n % 6
    984*q + 3084*q*(q-1) + 1728*q*(q-1)*(q-2) + 216*q*(q-1)*(q-2)*(q-3) +
      24*r + 4*r*(r-1)*(r+1) + 12*q*(44*r + 7*r*(r-1)) +
      4*q*r*(r-1)*(r-2) + 12*q*(q-1)*(57*r + 3*r*(r-1)) +
      144*r*q*(q-1)*(q-2)

theorem denPrefix_succ (n : ℤ) :
    denPrefix (n+1) = denPrefix n + 24 * denominator n := by
  by_cases hn : n < 0
  · rw [denominator_of_neg _ hn, show denPrefix n = 0 by simp [denPrefix, hn]]
    by_cases h : n + 1 < 0
    · simp [denPrefix, h]
    · have he : n + 1 = 0 := by omega
      rw [he]
      rfl
  have hn₁ : ¬ n + 1 < 0 := by omega
  have hden := scaled_denominator n (by omega)
  let q := n / 6
  let r := n % 6
  have hq : n / 6 = q := rfl
  have hr : n % 6 = r := rfl
  simp only [denPrefix, ite_eq_right hn, ite_eq_right hn₁, hq, hr]
  rw [hq, hr] at hden
  unfold polyDen at hden
  by_cases hf : r = 5
  · have hq₁ : (n+1)/6 = q+1 := by dsimp [q, r] at *; omega
    have hr₁ : (n+1)%6 = 0 := by dsimp [r] at *; omega
    rw [hq₁, hr₁, hf]
    rw [hf] at hden
    linear_combination -12*hden
  · have hq₁ : (n+1)/6 = q := by dsimp [q, r] at *; omega
    have hr₁ : (n+1)%6 = r+1 := by dsimp [r] at *; omega
    rw [hq₁, hr₁]
    linear_combination -12*hden

private theorem shift_succ (n a : ℤ) :
    denPrefix ((n+1)-a) = denPrefix (n-a) + 24 * denominator (n-a) := by
  rw [show n+1-a = (n-a)+1 by ring, denPrefix_succ]

def basePrefix (d u : ℤ) : ℤ :=
  denPrefix u - denPrefix (u-(d+1)) - denPrefix (u-(d+2)) - denPrefix (u-(d+3)) +
  denPrefix (u-(2*d+3)) + denPrefix (u-(2*d+4)) + denPrefix (u-(2*d+5)) -
  denPrefix (u-(3*d+6))

def cumPrefix (d n : ℕ) : ℤ :=
  let u := min n (3*d+1)
  basePrefix d u + 24 * ((n-u : ℕ) : ℤ) * cumulative d (3*d)

private theorem basePrefix_succ (d n : ℕ) (hn : n ≤ 3*d) :
    basePrefix d ((n : ℤ)+1) = basePrefix d n + 24 * cumulative d n := by
  have hzn : ¬ (n : ℤ) < 0 := by omega
  have hzd : ¬ (d : ℤ) < 0 := by omega
  have hnd : (n : ℤ) ≤ 3*d := by omega
  simp only [basePrefix, denPrefix_succ n, shift_succ, cumulative, hzn, hzd,
    Bool.false_or, decide_false, Bool.false_eq_true, ite_false, min_eq_left hnd]
  ring

theorem cumPrefix_succ (d n : ℕ) :
    cumPrefix d (n+1) = cumPrefix d n + 24 * cumulative d n := by
  by_cases h : n ≤ 3*d
  · simp only [cumPrefix, min_eq_left (show n+1 ≤ 3*d+1 by omega),
      min_eq_left (show n ≤ 3*d+1 by omega), Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul,
      add_zero, Nat.cast_add, Nat.cast_one, basePrefix_succ d n h]
  · have hcast : (3*d+1 : ℕ) ≤ n := by omega
    have hn : (3 : ℤ) * d ≤ n := by omega
    have he : cumulative d n = cumulative d (3*d) := by
      simp [cumulative, show ¬ (d : ℤ) < 0 by omega, show ¬ (n : ℤ) < 0 by omega,
        show ¬ (3 : ℤ)*d < 0 by omega, min_eq_right hn]
    simp only [cumPrefix, min_eq_right hcast,
      min_eq_right (show 3*d+1 ≤ n+1 by omega), he]
    have hsub : (n+1-(3*d+1) : ℕ) = n-(3*d+1)+1 := by omega
    simp only [hsub, Nat.cast_add, Nat.cast_one]
    ring

theorem cumulative_prefix (d n : ℕ) :
    24 * (∑ u ∈ range n, cumulative d (u : ℤ)) = cumPrefix d n := by
  induction n with
  | zero =>
      have hz (v : ℤ) (hv : v ≤ 0) : denPrefix v = 0 := by
        rcases lt_or_eq_of_le hv with h | rfl
        · simp [denPrefix, h]
        · rfl
      simp only [sum_range_zero, mul_zero, cumPrefix, zero_min, Nat.sub_zero, Nat.cast_zero,
        zero_mul, add_zero, basePrefix]
      symm
      simp only [hz 0 (le_refl _), hz (0-((d : ℤ)+1)) (by omega),
        hz (0-((d : ℤ)+2)) (by omega), hz (0-((d : ℤ)+3)) (by omega),
        hz (0-(2*(d : ℤ)+3)) (by omega), hz (0-(2*(d : ℤ)+4)) (by omega),
        hz (0-(2*(d : ℤ)+5)) (by omega), hz (0-(3*(d : ℤ)+6)) (by omega),
        sub_zero, add_zero]
  | succ n ih => rw [sum_range_succ, mul_add, ih, cumPrefix_succ d n]

/-- Weighted-index sum of the retained jets, scaled by 24. -/
def indexMoment (d : ℕ) : ℤ :=
  24 * 1650 * cumulative d 1650 - cumPrefix d 1650

private theorem count_range_ge (v j : ℕ) :
    (∑ u ∈ range j, if v ≤ u then (1 : ℕ) else 0) = j-v := by
  have hset : (range j).filter (fun u => v ≤ u) = Ico v j := by
    ext x
    simp [and_comm]
  rw [← sum_filter, ← card_eq_sum_ones, hset, Nat.card_Ico]

theorem indexMoment_eq (hc : CumulativeCount) (d : ℕ) :
    indexMoment d = 24 * ∑ e ∈ cumulativeColumns d 1650, (e.weight oldWeight : ℤ) := by
  let F := cumulativeColumns d 1650
  have hfilter (u : ℕ) (hu : u < 1650) :
      cumulativeColumns d u = F.filter (fun m => m.weight oldWeight ≤ u) := by
    ext m
    simp only [F, mem_filter, K1_13_2_2.mem_cumulativeColumns]
    change ((m.weight K1_13_2_2.gradeWeight : ℤ) = d ∧ (m.weight oldWeight : ℤ) ≤ u) ↔
      (((m.weight K1_13_2_2.gradeWeight : ℤ) = d ∧ (m.weight oldWeight : ℤ) ≤ 1650) ∧
        m.weight oldWeight ≤ u)
    omega
  have hswap : (∑ u ∈ range 1650, (cumulativeColumns d u).card) =
      ∑ e ∈ F, (1650 - e.weight oldWeight) := by
    calc
      _ = ∑ u ∈ range 1650, ∑ e ∈ F, if e.weight oldWeight ≤ u then 1 else 0 := by
        apply sum_congr rfl
        intro u hu
        rw [hfilter u (mem_range.mp hu), card_eq_sum_ones, sum_filter]
      _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun e _ => count_range_ge _ _
  have hcast : (∑ u ∈ range 1650, cumulative d (u : ℤ)) =
      ∑ e ∈ F, (1650 - (e.weight oldWeight : ℤ)) := by
    have hu (u : ℕ) := hc (d : ℤ) (u : ℤ)
    simp_rw [← hu]
    rw [← Nat.cast_sum, hswap, Nat.cast_sum]
    apply sum_congr rfl
    intro e he
    have h := (K1_13_2_2.mem_cumulativeColumns.mp he).2
    rw [Nat.cast_sub (by exact_mod_cast h), Nat.cast_ofNat]
  unfold indexMoment
  rw [← cumulative_prefix, hcast, ← hc d 1650]
  have hF : (cumulativeColumns d 1650).card = F.card := rfl
  rw [hF, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul]
  ring

open TaperNormalize (differentiated Eligible)
open K1_13 (Geom)
open K1_13_2 (SourceExponent SourcePolynomial)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finsupp

def gradeCap (q : ℕ) : ℕ := min q (cap q)

def sourceCount : ℤ := ∑ q ∈ range 4013, cumulative (gradeCap q) 1650

def sourceDegree : ℤ := ∑ q ∈ range 4013, (q : ℤ) * cumulative (gradeCap q) 1650

def sourceIndex24 : ℤ := ∑ q ∈ range 4013, indexMoment (gradeCap q)

end TaperMoments

end Merged_PrimaryTaperMoments

-- merged module PrimaryTaperColumns
section Merged_PrimaryTaperColumns

set_option Elab.async false
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

namespace TaperColumns

noncomputable section

open K1_13 (Geom)
open K1_13_2 (SourceExponent SourcePolynomial topWeight cumulative)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeColumns CumulativeCount)
open TaperMoments
open TaperBudget (cap)
open PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial Finset
open scoped BigOperators

def Eligible (A D : ℕ) (e : SourceExponent) : Prop :=
  TaperNormalize.Eligible cap e ∧ e.weight (differentialWeight D) ≤ 3000 * A - 1

def exponents (A D : ℕ) : Set SourceExponent := {e | Eligible A D e}

theorem finite_exponents (A D : ℕ) (hD : 3 < D) : (exponents A D).Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) D) ?_
    (3000 * A - 1)).subset (fun e he => he.2)
  intro v
  cases v with
  | none => change 1 ≠ (0 : ℕ); decide
  | some j => exact (differentialWeight_some_pos_of_order_lt_degree hD j).ne'

noncomputable def columns (A D : ℕ) (hD : 3 < D) : Finset SourceExponent :=
  (finite_exponents A D hD).toFinset

noncomputable def Source (A D : ℕ) : Submodule Geom SourcePolynomial :=
  restrictSupport Geom (exponents A D)

instance (A D : ℕ) [Fact (3 < D)] : Module.Finite Geom (Source A D) :=
  restrictSupport_finite (finite_exponents A D Fact.out)

theorem finrank_source (A D : ℕ) (hD : 3 < D) :
    Module.finrank Geom (Source A D) = (columns A D hD).card := by
  have h : (↑(columns A D hD) : Set SourceExponent) = exponents A D :=
    Set.Finite.coe_toFinset (finite_exponents A D hD)
  rw [Source, ← h]
  exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) (columns A D hD)

private abbrev vectors := Σ _ : ℕ, Σ _ : JetExp, ℕ

private def width (A D q : ℕ) (m : JetExp) : ℕ :=
  3000*A + m.weight oldWeight - D*q

private noncomputable def tuples (A D : ℕ) : Finset vectors :=
  (range 4013).sigma fun q =>
    (cumulativeColumns (gradeCap q) 1650).sigma fun m => range (width A D q m)

private def jetOf (e : SourceExponent) : JetExp := e.some

private def jetCount (e : SourceExponent) : ℕ := e.weight jetDegreeWeight

private def fill (q : ℕ) (m : JetExp) : JetExp := m + Finsupp.single 0 (q-gradeCap q)

private def trim (q : ℕ) (m : JetExp) : JetExp :=
  Finsupp.equivFunOnFinite.symm ![m 0 - (q-gradeCap q),m 1,m 2,m 3]

private def encode (u : vectors) : SourceExponent :=
  (fill u.1 u.2.1).optionElim u.2.2

private def decode (e : SourceExponent) : vectors :=
  ⟨jetCount e, trim (jetCount e) (jetOf e), e none⟩

theorem sumCount (e : SourceExponent) :
    e.weight jetDegreeWeight = e (some 0) + e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four]

theorem sumIndex (e : SourceExponent) :
    e.weight jetDerivativeWeight = e (some 1) + 2 * e (some 2) + 3 * e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, jetDerivativeWeight,
    smul_eq_mul, Nat.mul_comm]

theorem sumDifferentiated (e : SourceExponent) :
    e.weight TaperNormalize.differentiated = e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, TaperNormalize.differentiated]

private theorem sumTop (e : SourceExponent) : e.weight topWeight = e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, topWeight,
    Pi.single_apply, smul_eq_mul]

theorem sumOld (m : JetExp) : m.weight oldWeight = m 1 + 2*m 2 + 3*m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, oldWeight, smul_eq_mul, Nat.mul_comm]

theorem sumGrade (m : JetExp) : m.weight gradeWeight = m 0 + m 1 + m 2 + m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, gradeWeight, smul_eq_mul]

private theorem weight_add (D : ℕ) (hD : 3 < D) (e : SourceExponent) :
    e.weight (differentialWeight D) + e.weight jetDerivativeWeight =
      e none + D * (e.weight jetDegreeWeight) := by
  rw [sumIndex, sumCount]
  have hs (j a : ℕ) (hj : j ≤ D) : (D-j)*a + j*a = D*a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hj]
  simp only [Finsupp.weight_eq_sum, Fintype.sum_option, differentialWeight, smul_eq_mul, Nat.mul_one]
  rw [Fin.sum_univ_four]
  change e none + (e (some 0) * D + e (some 1) * (D-1) + e (some 2) * (D-2) +
    e (some 3) * (D-3)) + (e (some 1) + 2 * e (some 2) + 3 * e (some 3)) =
      e none + D * (e (some 0) + e (some 1) + e (some 2) + e (some 3))
  rw [Nat.mul_comm (e (some 0)) D, Nat.mul_comm (e (some 1)) (D-1), Nat.mul_comm (e (some 2)) (D-2),
    Nat.mul_comm (e (some 3)) (D-3)]
  simp only [Nat.mul_add]
  have h₁ := hs 1 (e (some 1)) (by omega)
  have h₂ := hs 2 (e (some 2)) (by omega)
  have h₃ := hs 3 (e (some 3)) (by omega)
  omega

private theorem eligible_iff (A D : ℕ) (hA : 0 < A) (hD : 3 < D) (e : SourceExponent) :
    Eligible A D e ↔
      e.weight jetDegreeWeight ≤ 4012 ∧ e.weight jetDerivativeWeight ≤ 1650 ∧
      e.weight TaperNormalize.differentiated ≤ cap (e.weight jetDegreeWeight) ∧
      e none < 3000*A + e.weight jetDerivativeWeight - D*(e.weight jetDegreeWeight) := by
  unfold Eligible TaperNormalize.Eligible
  have hw := weight_add D hD e
  have hj := sumIndex e
  have ht := sumTop e
  omega

private theorem fill_succ (q : ℕ) (m : JetExp) (i : Fin 4) (hi : i ≠ 0) : fill q m i = m i := by
  simp [fill, Finsupp.single_eq_of_ne hi]

private theorem fill_zero (q : ℕ) (m : JetExp) : fill q m 0 = m 0 + (q-gradeCap q) := by
  simp [fill]

private theorem trim_succ (q : ℕ) (m : JetExp) (i : Fin 4) (hi : i ≠ 0) : trim q m i = m i := by
  fin_cases i <;> simp_all [trim]

private theorem trim_zero (q : ℕ) (m : JetExp) : trim q m 0 = m 0 - (q-gradeCap q) := by
  simp [trim]

private theorem jetOf_some (e : SourceExponent) (i : Fin 4) : jetOf e i = e (some i) := by
  rfl

private theorem encode_some (u : vectors) (i : Fin 4) : encode u (some i) = fill u.1 u.2.1 i := by
  simp [encode]

private theorem encode_none (u : vectors) : encode u none = u.2.2 := by simp [encode]

private theorem encode_grade (q : ℕ) (m : JetExp) (x : ℕ)
    (hm : m.weight gradeWeight = gradeCap q) :
    (encode ⟨q,m,x⟩).weight jetDegreeWeight = q := by
  rw [sumGrade] at hm
  rw [sumCount, encode_some, encode_some, encode_some, encode_some,
    fill_zero, fill_succ _ _ 1 (by decide), fill_succ _ _ 2 (by decide), fill_succ _ _ 3 (by decide)]
  change (m 0+(q-gradeCap q))+m 1+m 2+m 3 = q
  have hq : gradeCap q ≤ q := min_le_left _ _
  omega

private theorem encode_index (q : ℕ) (m : JetExp) (x : ℕ) :
    (encode ⟨q,m,x⟩).weight jetDerivativeWeight = m.weight oldWeight := by
  rw [sumIndex, sumOld, encode_some, encode_some, encode_some,
    fill_succ _ _ 1 (by decide), fill_succ _ _ 2 (by decide), fill_succ _ _ 3 (by decide)]

private theorem decode_mem (A D : ℕ) (hA : 0 < A) (hD : 3 < D) (e : SourceExponent)
    (he : e ∈ columns A D hD) : decode e ∈ tuples A D := by
  have he' : Eligible A D e := by
    change e ∈ exponents A D
    simpa only [columns, Set.Finite.mem_toFinset] using he
  obtain ⟨hq, hj, hd, hx⟩ := (eligible_iff A D hA hD e).mp he'
  let q := jetCount e
  let m := trim q (jetOf e)
  change ⟨q,m,e none⟩ ∈ tuples A D
  have hv : e (some 1) + e (some 2) + e (some 3) ≤ gradeCap q := by
    rw [sumDifferentiated] at hd
    have h := sumCount e
    exact le_min (by unfold q jetCount; omega) hd
  have hdeg : m.weight gradeWeight = gradeCap q := by
    rw [sumGrade, show m = trim q (jetOf e) by rfl, trim_zero,
      trim_succ _ _ 1 (by decide), trim_succ _ _ 2 (by decide), trim_succ _ _ 3 (by decide)]
    simp only [jetOf_some]
    have h := sumCount e
    change q = _ at h
    have hcap : gradeCap q ≤ q := min_le_left _ _
    omega
  have hidx : m.weight oldWeight = e.weight jetDerivativeWeight := by
    rw [sumOld, sumIndex, show m = trim q (jetOf e) by rfl,
      trim_succ _ _ 1 (by decide), trim_succ _ _ 2 (by decide), trim_succ _ _ 3 (by decide)]
    simp only [jetOf_some]
  have hq' : q ∈ range 4013 := mem_range.mpr (Nat.lt_succ_of_le hq)
  refine mem_sigma.mpr ⟨hq', mem_sigma.mpr ⟨?_,?_⟩⟩
  · exact K1_13_2_2.mem_cumulativeColumns.mpr ⟨by exact_mod_cast hdeg, by exact_mod_cast hidx.trans_le hj⟩
  · exact mem_range.mpr (by rwa [width, hidx])

private theorem encode_mem (A D : ℕ) (hA : 0 < A) (hD : 3 < D) (u : vectors)
    (hu : u ∈ tuples A D) : encode u ∈ columns A D hD := by
  obtain ⟨q,m,x⟩ := u
  obtain ⟨hq, hm, hx⟩ := by simpa only [tuples, mem_sigma, mem_range] using hu
  have hme := K1_13_2_2.mem_cumulativeColumns.mp hm
  have hgrade : m.weight gradeWeight = gradeCap q := by exact_mod_cast hme.1
  have hidx : m.weight oldWeight ≤ 1650 := by exact_mod_cast hme.2
  rw [columns, Set.Finite.mem_toFinset]
  change Eligible A D (encode ⟨q,m,x⟩)
  apply (eligible_iff A D hA hD _).mpr
  rw [encode_grade _ _ _ hgrade, encode_index, encode_none]
  refine ⟨by omega, hidx, ?_, hx⟩
  rw [sumDifferentiated, encode_some, encode_some, encode_some,
    fill_succ _ _ 1 (by decide), fill_succ _ _ 2 (by decide), fill_succ _ _ 3 (by decide)]
  rw [sumGrade] at hgrade
  have := min_le_right q (cap q)
  unfold gradeCap at hgrade
  change m 1+m 2+m 3 ≤ cap q
  omega

private theorem encode_decode (A D : ℕ) (hA : 0 < A) (hD : 3 < D)
    (e : SourceExponent) (he : e ∈ columns A D hD) : encode (decode e) = e := by
  have he' : Eligible A D e := by
    change e ∈ exponents A D
    simpa only [columns, Set.Finite.mem_toFinset] using he
  obtain ⟨_, _, hd, _⟩ := (eligible_iff A D hA hD e).mp he'
  have hv : e (some 1) + e (some 2) + e (some 3) ≤ gradeCap (jetCount e) := by
    rw [sumDifferentiated] at hd
    have h := sumCount e
    exact le_min (by unfold jetCount; omega) hd
  ext v
  cases v with
  | none => rw [encode_none]; rfl
  | some i =>
    rw [encode_some]
    change fill (jetCount e) (trim (jetCount e) (jetOf e)) i = _
    by_cases hi : i = 0
    · subst i
      rw [fill_zero, trim_zero, jetOf_some, Nat.sub_add_cancel]
      have h := sumCount e
      change jetCount e = _ at h
      omega
    · rw [fill_succ _ _ _ hi, trim_succ _ _ _ hi, jetOf_some]

private theorem decode_encode (A D : ℕ) (u : vectors) (hu : u ∈ tuples A D) :
    decode (encode u) = u := by
  obtain ⟨q,m,x⟩ := u
  obtain ⟨_, hm, _⟩ := by simpa only [tuples, mem_sigma, mem_range] using hu
  have hgrade : m.weight gradeWeight = gradeCap q :=
    by exact_mod_cast (K1_13_2_2.mem_cumulativeColumns.mp hm).1
  have hq : jetCount (encode ⟨q,m,x⟩) = q := encode_grade _ _ _ hgrade
  have hm' : trim q (jetOf (encode ⟨q,m,x⟩)) = m := by
    ext i
    by_cases hi : i = 0
    · subst i
      rw [trim_zero, jetOf_some, encode_some, fill_zero, Nat.add_sub_cancel]
    · rw [trim_succ _ _ _ hi, jetOf_some, encode_some, fill_succ _ _ _ hi]
  simp [decode, hq, hm', encode_none]

theorem card_columns (A D : ℕ) (hA : 0 < A) (hD : 3 < D) :
    (columns A D hD).card = (tuples A D).card := by
  exact Finset.card_bij' (fun e _ => decode e) (fun u _ => encode u)
    (decode_mem A D hA hD) (encode_mem A D hA hD) (encode_decode A D hA hD) (decode_encode A D)


private theorem scaled_grade_columns (hc : CumulativeCount) (A D q : ℕ)
    (hb : D*q ≤ 3000*A) :
    24 * (∑ e ∈ cumulativeColumns (gradeCap q) 1650, (width A D q e : ℤ)) =
      (24 * (3000*(A : ℤ) - (D : ℤ)*q)) * cumulative (gradeCap q) 1650 +
        indexMoment (gradeCap q) := by
  let d := gradeCap q
  have hwidth (e : JetExp) :
      (width A D q e : ℤ) = ((3000 : ℤ)*A - D*q) + e.weight oldWeight := by
    have hsub : D*q ≤ 3000*A + e.weight oldWeight := by omega
    simp only [width, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  simp_rw [hwidth]
  rw [Finset.sum_add_distrib, mul_add]
  rw [indexMoment_eq hc, ← hc (gradeCap q : ℤ) 1650]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem scaled_columns (A D : ℕ) (hA : 0<A) (hD : 3<D) (hb : D*4012 ≤ 3000*A) :
    24 * ((columns A D hD).card : ℤ) =
      24*(3000*(A : ℤ))*sourceCount - (24*(D : ℤ))*sourceDegree + sourceIndex24 := by
  rw [card_columns A D hA hD]
  simp only [tuples, card_sigma, card_range, Nat.cast_sum]
  rw [mul_sum]
  have hsum : (∑ q ∈ range 4013,
      24 * (∑ e ∈ cumulativeColumns (gradeCap q) 1650, (width A D q e : ℤ))) =
      ∑ q ∈ range 4013,
        (24*(3000*(A : ℤ))*cumulative (gradeCap q) 1650 -
          (24*(D : ℤ))*((q : ℤ)*cumulative (gradeCap q) 1650) + indexMoment (gradeCap q)) := by
    apply sum_congr rfl
    intro q hq
    have hq' : q ≤ 4012 := by have := mem_range.mp hq; omega
    rw [scaled_grade_columns K1_13_2_2_2.proof A D q
      ((Nat.mul_le_mul_left D hq').trans hb)]
    ring
  rw [hsum, sum_add_distrib, sum_sub_distrib]
  simp only [sourceCount, sourceDegree, sourceIndex24, mul_sum]


def jetExponents : Set JetExp :=
  {m | m.weight gradeWeight ≤ 4012 ∧ m.weight oldWeight ≤ 1650 ∧
    m 1 + m 2 + m 3 ≤ cap (m.weight gradeWeight)}

theorem jetExponents_finite : jetExponents.Finite :=
  (Finsupp.finite_of_nat_weight_le gradeWeight (fun j => by simp [gradeWeight]) 4012).subset
    (fun _ h => h.1)

noncomputable def jetColumns : Finset JetExp := jetExponents_finite.toFinset

private noncomputable def jetTuples : Finset (Σ _ : ℕ, JetExp) :=
  (range 4013).sigma fun q => cumulativeColumns (gradeCap q) 1650

private theorem jet_mem_source_zero (m : JetExp) :
    (m.optionElim 0) ∈ columns 1000000 4 (by decide) ↔ m ∈ jetExponents := by
  rw [columns, Set.Finite.mem_toFinset]
  change Eligible 1000000 4 (m.optionElim 0) ↔ _
  rw [eligible_iff _ _ (by decide) (by decide), sumCount, sumIndex, sumDifferentiated]
  simp only [Finsupp.optionElim_apply_some, Finsupp.optionElim_apply_none]
  change m 0 + m 1 + m 2 + m 3 ≤ 4012 ∧ m 1 + 2*m 2 + 3*m 3 ≤ 1650 ∧
      m 1 + m 2 + m 3 ≤ cap (m 0 + m 1 + m 2 + m 3) ∧
      0 < 3000*1000000 + (m 1+2*m 2+3*m 3) - 4*(m 0+m 1+m 2+m 3) ↔
    m.weight gradeWeight ≤ 4012 ∧ m.weight oldWeight ≤ 1650 ∧
      m 1+m 2+m 3 ≤ cap (m.weight gradeWeight)
  rw [sumGrade, sumOld]
  omega

theorem jet_card_eq : (jetColumns.card : ℤ) = sourceCount := by
  have h : jetColumns.card = jetTuples.card := by
    refine card_bij' (fun m _ => ⟨m.weight gradeWeight, trim (m.weight gradeWeight) m⟩)
      (fun u _ => fill u.1 u.2) ?_ ?_ ?_ ?_
    · intro m hm
      have hmem : m ∈ jetExponents := by simpa only [jetColumns, Set.Finite.mem_toFinset] using hm
      have he := (jet_mem_source_zero m).mpr hmem
      have ht := decode_mem 1000000 4 (by decide) (by decide) (m.optionElim 0) he
      have hg : jetCount (m.optionElim 0) = m.weight gradeWeight := by
        rw [jetCount, sumCount, sumGrade]
        simp only [Finsupp.optionElim_apply_some]
      have hj : jetOf (m.optionElim 0) = m := by ext i; rw [jetOf_some, Finsupp.optionElim_apply_some]
      change decode (m.optionElim 0) ∈ tuples 1000000 4 at ht
      simp only [decode, hg, hj, tuples, mem_sigma] at ht
      exact mem_sigma.mpr ⟨ht.1, ht.2.1⟩
    · rintro ⟨q,m⟩ hm
      have hq : q ∈ range 4013 := (mem_sigma.mp hm).1
      have hJ : m ∈ cumulativeColumns (gradeCap q) 1650 := (mem_sigma.mp hm).2
      have hwidth : 0 < width 1000000 4 q m := by
        have := mem_range.mp hq
        unfold width
        omega
      have h := encode_mem 1000000 4 (by decide) (by decide) ⟨q,m,0⟩
        (mem_sigma.mpr ⟨hq, mem_sigma.mpr ⟨hJ, mem_range.mpr hwidth⟩⟩)
      simpa only [jetColumns, Set.Finite.mem_toFinset] using (jet_mem_source_zero (fill q m)).mp h
    · intro m hm
      have h := encode_decode 1000000 4 (by decide) (by decide) (m.optionElim 0)
        ((jet_mem_source_zero m).mpr (by simpa only [jetColumns, Set.Finite.mem_toFinset] using hm))
      have hg : jetCount (m.optionElim 0) = m.weight gradeWeight := by
        rw [jetCount, sumCount, sumGrade]
        simp only [Finsupp.optionElim_apply_some]
      have hj : jetOf (m.optionElim 0) = m := by ext i; rw [jetOf_some, Finsupp.optionElim_apply_some]
      ext i
      have hi := congrArg (fun e : SourceExponent => e (some i)) h
      simpa only [decode, encode_some, hg, hj, Finsupp.optionElim_apply_some] using hi
    · rintro ⟨q,m⟩ hm
      have hq : q ∈ range 4013 := (mem_sigma.mp hm).1
      have hJ : m ∈ cumulativeColumns (gradeCap q) 1650 := (mem_sigma.mp hm).2
      have hwidth : 0 < width 1000000 4 q m := by
        have := mem_range.mp hq
        unfold width
        omega
      have h := decode_encode 1000000 4 ⟨q,m,0⟩
        (mem_sigma.mpr ⟨hq, mem_sigma.mpr ⟨hJ, mem_range.mpr hwidth⟩⟩)
      have hg : jetCount (encode ⟨q,m,0⟩) = (fill q m).weight gradeWeight := by
        rw [jetCount, sumCount, sumGrade]
        simp only [encode_some]
      have hj : jetOf (encode ⟨q,m,0⟩) = fill q m := by ext i; rw [jetOf_some, encode_some]
      simpa only [decode, hg, hj] using congrArg (fun u : vectors => (⟨u.1, u.2.1⟩ : Σ _ : ℕ, JetExp)) h
  rw [h, jetTuples, card_sigma, Nat.cast_sum, sourceCount]
  apply sum_congr rfl
  intro q _
  exact K1_13_2_2_2.proof _ _

end
end TaperColumns

end Merged_PrimaryTaperColumns

-- merged module PrimaryTaperColumnData
section Merged_PrimaryTaperColumnData
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace TaperColumns
open K1_13_2 (cumulative)
open TaperMoments
open Finset
open scoped BigOperators
private abbrev Moments := ℤ × ℤ × ℤ
private def combine (a b : Moments) : Moments := (a.1+b.1, a.2.1+b.2.1, a.2.2+b.2.2)
open K1_13_2 (denominator)
open TaperMoments (basePrefix)
private theorem upper_den : denominator 1650 = 125576826 := by decide +kernel
private theorem upper_prefix : denPrefix 1650 = 1244339514000 := by decide +kernel
private def fastCount (d : ℕ) : ℤ :=
  if 824 ≤ d then
    125576826 - denominator (1650-d-1) - denominator (1650-d-2) -
      denominator (1650-d-3)
  else cumulative d 1650
private def fastPrefix (d : ℕ) : ℤ :=
  if 824 ≤ d then
    1244339514000 - denPrefix (1650-(d+1)) - denPrefix (1650-(d+2)) -
      denPrefix (1650-(d+3))
  else cumPrefix d 1650
private theorem fastCount_eq (d : ℕ) : fastCount d = cumulative d 1650 := by
  by_cases hd : 824 ≤ d
  · have hz : ¬ (d : ℤ) < 0 := by omega
    have hmin : (1650 : ℤ) ≤ 3*d := by omega
    have h1 : (1650 : ℤ) - 2*d - 3 < 0 := by omega
    have h2 : (1650 : ℤ) - 2*d - 4 < 0 := by omega
    have h3 : (1650 : ℤ) - 2*d - 5 < 0 := by omega
    have h4 : (1650 : ℤ) - 3*d - 6 < 0 := by omega
    simp only [fastCount, if_pos hd, cumulative, hz, not_lt.mpr (by decide : (0 : ℤ) ≤ 1650),
      decide_false, Bool.false_or, Bool.false_eq_true, ite_false, min_eq_left hmin]
    have hn (u : ℤ) (hu : u < 0) : denominator u = 0 := by simp [denominator, hu]
    rw [hn _ h1, hn _ h2, hn _ h3, hn _ h4, upper_den]
    simp
  · simp [fastCount, hd]
private theorem fastPrefix_eq (d : ℕ) : fastPrefix d = cumPrefix d 1650 := by
  by_cases hd : 824 ≤ d
  · have hmin : 1650 ≤ 3*d+1 := by omega
    have h1 : (1650 : ℤ) - (2*d+3) < 0 := by omega
    have h2 : (1650 : ℤ) - (2*d+4) < 0 := by omega
    have h3 : (1650 : ℤ) - (2*d+5) < 0 := by omega
    have h4 : (1650 : ℤ) - (3*d+6) < 0 := by omega
    have hn (u : ℤ) (hu : u < 0) : denPrefix u = 0 := by simp [denPrefix, hu]
    simp only [fastPrefix, if_pos hd, cumPrefix, min_eq_left hmin, Nat.sub_self,
      Nat.cast_zero, mul_zero, zero_mul, add_zero, basePrefix, Nat.cast_ofNat,
      hn _ h1, hn _ h2, hn _ h3, hn _ h4, upper_prefix, sub_zero]
  · simp [fastPrefix, hd]
private def oneRow (q : ℕ) : Moments :=
  let d := gradeCap q
  let n := fastCount d
  (n, (q : ℤ)*n, fastPrefix d)
private def moments (lo : ℕ) : ℕ → Moments
  | 0 => (0,0,0)
  | n+1 => combine (moments lo n) (oneRow (lo+n))
private def twiceDenN (n : ℕ) : ℕ :=
  let q := n / 6
  let r := n % 6
  2 + r * (r + 1) + q * (11 + r * (7 + r) + q * (21 + 6 * r + 12 * q))
private def denPrefixN (n : ℕ) : ℕ :=
  let q := n / 6
  let r := n % 6
  r * (20 + 4 * r * r) +
    q * (60 + r * (92 + r * (36 + 4 * r)) +
      q * (276 + r * (216 + 36 * r) + q * (432 + 144 * r + 216 * q)))
private def fden : ℤ → ℤ
  | Int.ofNat n => Int.ofNat (twiceDenN n / 2)
  | Int.negSucc _ => 0
private def fpre : ℤ → ℤ
  | Int.ofNat n => Int.ofNat (denPrefixN n)
  | Int.negSucc _ => 0
private theorem twice_pred (q : ℤ) : 2 * (q * (q - 1) / 2) = q * (q - 1) := by
  have h : (2 : ℤ) ∣ q * (q - 1) := by
    rcases Int.emod_two_eq_zero_or_one q with h | h
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ q) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ q - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem twice_succ (q : ℤ) : 2 * (q * (q + 1) / 2) = q * (q + 1) := by
  have h : (2 : ℤ) ∣ q * (q + 1) := by
    rcases Int.emod_two_eq_zero_or_one q with h | h
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ q) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ q + 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem den_nat (n : ℕ) : 2 * K1_13_2.denominator (n : ℤ) = (twiceDenN n : ℤ) := by
  have hn : ¬ (n : ℤ) < 0 := by omega
  have h1 := twice_succ ((n : ℤ) % 6)
  have h2 := twice_pred ((n : ℤ) % 6)
  have h3 := twice_pred ((n : ℤ) / 6)
  simp only [K1_13_2.denominator, hn, ite_false]
  unfold twiceDenN
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.natCast_mod]
  linear_combination h1 + ((n : ℤ) / 6) * h2 + (57 + 6 * ((n : ℤ) % 6)) * h3
private theorem fden_eq (u : ℤ) : fden u = K1_13_2.denominator u := by
  rcases u with n | m
  · show ((twiceDenN n / 2 : ℕ) : ℤ) = K1_13_2.denominator (n : ℤ)
    have h := den_nat n
    omega
  · show (0 : ℤ) = K1_13_2.denominator (Int.negSucc m)
    simp [K1_13_2.denominator, Int.negSucc_lt_zero]
private theorem pre_nat (n : ℕ) : TaperMoments.denPrefix (n : ℤ) = (denPrefixN n : ℤ) := by
  have hn : ¬ (n : ℤ) < 0 := by omega
  simp only [TaperMoments.denPrefix, hn, ite_false]
  unfold denPrefixN
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.natCast_mod]
  ring
private theorem fpre_eq (u : ℤ) : fpre u = TaperMoments.denPrefix u := by
  rcases u with n | m
  · show ((denPrefixN n : ℕ) : ℤ) = TaperMoments.denPrefix (n : ℤ)
    exact (pre_nat n).symm
  · show (0 : ℤ) = TaperMoments.denPrefix (Int.negSucc m)
    simp [TaperMoments.denPrefix, Int.negSucc_lt_zero]
private def fcum (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    fden v - fden (v - d - 1) - fden (v - d - 2) -
      fden (v - d - 3) + fden (v - 2 * d - 3) +
      fden (v - 2 * d - 4) + fden (v - 2 * d - 5) -
      fden (v - 3 * d - 6)
private theorem fcum_eq (d u : ℤ) : fcum d u = cumulative d u := by
  unfold fcum cumulative
  rw [show fden = K1_13_2.denominator from funext fden_eq]
private def fbase (d u : ℤ) : ℤ :=
  fpre u - fpre (u-(d+1)) - fpre (u-(d+2)) - fpre (u-(d+3)) +
  fpre (u-(2*d+3)) + fpre (u-(2*d+4)) + fpre (u-(2*d+5)) -
  fpre (u-(3*d+6))
private theorem fbase_eq (d u : ℤ) : fbase d u = basePrefix d u := by
  unfold fbase basePrefix
  rw [show fpre = TaperMoments.denPrefix from funext fpre_eq]
private def fcumPrefix (d n : ℕ) : ℤ :=
  let u := min n (3*d+1)
  fbase d u + 24 * ((n-u : ℕ) : ℤ) * fcum d (3*d)
private theorem fcumPrefix_eq (d n : ℕ) : fcumPrefix d n = cumPrefix d n := by
  unfold fcumPrefix cumPrefix
  rw [show fbase = basePrefix from funext₂ fbase_eq, show fcum = cumulative from funext₂ fcum_eq]
private def ffastCount (d : ℕ) : ℤ :=
  if 824 ≤ d then
    125576826 - fden (1650-d-1) - fden (1650-d-2) -
      fden (1650-d-3)
  else fcum d 1650
private theorem ffastCount_eq (d : ℕ) : ffastCount d = fastCount d := by
  unfold ffastCount fastCount
  simp only [fden_eq, fcum_eq]
private def ffastPrefix (d : ℕ) : ℤ :=
  if 824 ≤ d then
    1244339514000 - fpre (1650-(d+1)) - fpre (1650-(d+2)) -
      fpre (1650-(d+3))
  else fcumPrefix d 1650
private theorem ffastPrefix_eq (d : ℕ) : ffastPrefix d = fastPrefix d := by
  unfold ffastPrefix fastPrefix
  simp only [fpre_eq, fcumPrefix_eq]
private def foneRow (q : ℕ) : Moments :=
  let d := gradeCap q
  let n := ffastCount d
  (n, (q : ℤ)*n, ffastPrefix d)
private theorem foneRow_eq (q : ℕ) : foneRow q = oneRow q := by
  unfold foneRow oneRow
  simp only [ffastCount_eq, ffastPrefix_eq]
private def fmoments (lo : ℕ) : ℕ → Moments
  | 0 => (0,0,0)
  | n+1 => combine (fmoments lo n) (foneRow (lo+n))
private theorem moments_fast (lo n : ℕ) : moments lo n = fmoments lo n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [moments, fmoments, ih, foneRow_eq]
private theorem moments_split (lo a b : ℕ) :
    moments lo (a+b) = combine (moments lo a) (moments (lo+a) b) := by
  induction b with
  | zero => simp [moments, combine]
  | succ b ih => rw [Nat.add_succ, moments, moments, ih, Nat.add_assoc]
                 simp only [combine, Int.add_assoc]
private theorem moments_eq (n : ℕ) :
    moments 0 n =
      (∑ q ∈ range n, cumulative (gradeCap q) 1650,
       ∑ q ∈ range n, (q : ℤ)*cumulative (gradeCap q) 1650,
       ∑ q ∈ range n, cumPrefix (gradeCap q) 1650) := by
  induction n with
  | zero => simp [moments]
  | succ n ih => simp only [moments, ih, sum_range_succ, oneRow, combine, Nat.zero_add, fastCount_eq, fastPrefix_eq]
private theorem plateau_count : cumulative ((1650 : ℕ) : ℤ) 1650 = 125576826 := by decide +kernel
private theorem plateau_prefix : cumPrefix 1650 1650 = 1244339514000 := by decide +kernel
private theorem plateau_row (q : ℕ) (lo : 1650 ≤ q) (hi : q < 3514) :
    oneRow q = (125576826, (q : ℤ) * 125576826, 1244339514000) := by
  have hcap : gradeCap q = 1650 := by
    simp only [gradeCap, TaperBudget.cap, if_pos hi, min_eq_right lo]
  simp only [oneRow, hcap, fastCount_eq, fastPrefix_eq, plateau_count, plateau_prefix]
private theorem plateau_components (lo n : ℕ) (start : 1650 ≤ lo) (finish : lo + n ≤ 3514) :
    (moments lo n).1 = (n : ℤ) * 125576826 ∧
    2 * (moments lo n).2.1 = (2 * (lo : ℤ) + (n : ℤ) - 1) * (n : ℤ) * 125576826 ∧
    (moments lo n).2.2 = (n : ℤ) * 1244339514000 := by
  induction n with
  | zero => norm_num [moments]
  | succ n ih =>
    obtain ⟨hc, hd, hj⟩ := ih (by omega)
    have hr := plateau_row (lo + n) (by omega) (by omega)
    simp only [moments, hr, combine, Nat.cast_succ, Nat.cast_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]
      ring
    · rw [mul_add, hd]
      ring
    · rw [hj]
      ring
private theorem plateau_value (lo n : ℕ) (s : ℤ) (start : 1650 ≤ lo)
    (finish : lo + n ≤ 3514)
    (mid : 2 * s = (2 * (lo : ℤ) + (n : ℤ) - 1) * (n : ℤ) * 125576826) :
    moments lo n = ((n : ℤ) * 125576826, s, (n : ℤ) * 1244339514000) := by
  obtain ⟨hc, hd, hj⟩ := plateau_components lo n start finish
  have hs : (moments lo n).2.1 = s := by linarith only [hd, mid]
  exact Prod.ext hc (Prod.ext hs hj)
private theorem chunk0 : moments 0 64 = (766480, 38630592, 28961906688) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk64 : moments 64 64 = (10950160, 1151780032, 392162254848) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk128 : moments 128 64 = (46692880, 7734564032, 1570593742848) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk192 : moments 192 64 = (124771856, 28444026048, 3916980559872) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk256 : moments 256 64 = (261964304, 76232176832, 7629428072448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk320 : moments 320 64 = (475047440, 168345994432, 12751422824448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk384 : moments 384 64 = (780798480, 326327424192, 19171832537088) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk448 : moments 448 64 = (1195994640, 576013378752, 26624906108928) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk512 : moments 512 64 = (1737323150, 947484425540, 34690308784824) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk576 : moments 576 64 = (2409438080, 1467615274816, 42809297555328) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk640 : moments 640 64 = (3172139904, 2134302060352, 50424594575232) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk704 : moments 704 64 = (3967085440, 2922016831296, 57144114876288) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk768 : moments 768 64 = (4735554768, 3790003814602, 62768847096768) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk832 : moments 832 64 = (5423001088, 4686152908112, 67290168195456) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk896 : moments 896 64 = (6008952320, 5576166392144, 70835420387712) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk960 : moments 960 64 = (6500007424, 6447136851280, 73555743947136) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1024 : moments 1024 64 = (6904555008, 7289698404688, 75590356212096) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1088 : moments 1088 64 = (7230983680, 8096632655184, 77065589619072) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1152 : moments 1152 64 = (7487682048, 8862868689232, 78094891702656) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1216 : moments 1216 64 = (7683038720, 9585483076944, 78778825095552) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1280 : moments 1280 64 = (7825442304, 10263699872080, 79205067528576) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1344 : moments 1344 64 = (7923281408, 10898890612048, 79448411830656) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1408 : moments 1408 64 = (7984944640, 11494574317904, 79570765928832) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1472 : moments 1472 64 = (8018820608, 12056417494352, 79621152848256) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1536 : moments 1536 64 = (8033297920, 12592234129744, 79635710712192) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1600 : moments 1600 50 = (6278689200, 10199732826645, 62216939575080) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1650 : moments 1650 1864 = (234075203664, 604265138258616, 2319448854096000) :=
  plateau_value 1650 1864 604265138258616 (by decide) (by decide) (by decide)
private theorem chunk3514 : moments 3514 6 = (753368160, 2649219120421, 7466006383320) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3520 : moments 3520 64 = (8032072282, 28525854344641, 79634768477448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3584 : moments 3584 64 = (8014274720, 28975464060405, 79615399984032) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3648 : moments 3648 64 = (7973908122, 29339703821282, 79551178982208) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3712 : moments 3712 64 = (7901339158, 29578175247143, 79398146595168) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3776 : moments 3776 64 = (7787486114, 29650119438357, 79098473674512) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3840 : moments 3840 64 = (7622412918, 29509140942244, 78577078832208) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3904 : moments 3904 64 = (7397254232, 29110514169461, 77746943352288) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3968 : moments 3968 45 = (5029151191, 20065722297522, 53950645283400) := by
  rw [moments_fast]
  decide +kernel
private theorem join (lo n m next full : ℕ) (a b result : Moments)
    (hLen : n+m = full) (hStart : lo+n = next) (hValue : combine a b = result)
    (ha : moments lo n = a) (hb : moments next m = b) :
    moments lo full = result := by
  rw [← hLen, moments_split, ha, hStart, hb]
  exact hValue
private theorem checked : moments 0 4013 = (406807694511, 962164450311967, 4235319990139464) := by
  have tail3968 := chunk3968
  have tail3904 : moments 3904 109 = (12426405423, 49176236466983, 131697588635688) :=
    join 3904 64 45 3968 109 (7397254232, 29110514169461, 77746943352288) (5029151191, 20065722297522, 53950645283400) (12426405423, 49176236466983, 131697588635688) (by decide) (by decide) (by decide) chunk3904 tail3968
  have tail3840 : moments 3840 173 = (20048818341, 78685377409227, 210274667467896) :=
    join 3840 64 109 3904 173 (7622412918, 29509140942244, 78577078832208) (12426405423, 49176236466983, 131697588635688) (20048818341, 78685377409227, 210274667467896) (by decide) (by decide) (by decide) chunk3840 tail3904
  have tail3776 : moments 3776 237 = (27836304455, 108335496847584, 289373141142408) :=
    join 3776 64 173 3840 237 (7787486114, 29650119438357, 79098473674512) (20048818341, 78685377409227, 210274667467896) (27836304455, 108335496847584, 289373141142408) (by decide) (by decide) (by decide) chunk3776 tail3840
  have tail3712 : moments 3712 301 = (35737643613, 137913672094727, 368771287737576) :=
    join 3712 64 237 3776 301 (7901339158, 29578175247143, 79398146595168) (27836304455, 108335496847584, 289373141142408) (35737643613, 137913672094727, 368771287737576) (by decide) (by decide) (by decide) chunk3712 tail3776
  have tail3648 : moments 3648 365 = (43711551735, 167253375916009, 448322466719784) :=
    join 3648 64 301 3712 365 (7973908122, 29339703821282, 79551178982208) (35737643613, 137913672094727, 368771287737576) (43711551735, 167253375916009, 448322466719784) (by decide) (by decide) (by decide) chunk3648 tail3712
  have tail3584 : moments 3584 429 = (51725826455, 196228839976414, 527937866703816) :=
    join 3584 64 365 3648 429 (8014274720, 28975464060405, 79615399984032) (43711551735, 167253375916009, 448322466719784) (51725826455, 196228839976414, 527937866703816) (by decide) (by decide) (by decide) chunk3584 tail3648
  have tail3520 : moments 3520 493 = (59757898737, 224754694321055, 607572635181264) :=
    join 3520 64 429 3584 493 (8032072282, 28525854344641, 79634768477448) (51725826455, 196228839976414, 527937866703816) (59757898737, 224754694321055, 607572635181264) (by decide) (by decide) (by decide) chunk3520 tail3584
  have tail3514 : moments 3514 499 = (60511266897, 227403913441476, 615038641564584) :=
    join 3514 6 493 3520 499 (753368160, 2649219120421, 7466006383320) (59757898737, 224754694321055, 607572635181264) (60511266897, 227403913441476, 615038641564584) (by decide) (by decide) (by decide) chunk3514 tail3520
  have tail1650 : moments 1650 2363 = (294586470561, 831669051700092, 2934487495660584) :=
    join 1650 1864 499 3514 2363 (234075203664, 604265138258616, 2319448854096000) (60511266897, 227403913441476, 615038641564584) (294586470561, 831669051700092, 2934487495660584) (by decide) (by decide) (by decide) chunk1650 tail3514
  have tail1600 : moments 1600 2413 = (300865159761, 841868784526737, 2996704435235664) :=
    join 1600 50 2363 1650 2413 (6278689200, 10199732826645, 62216939575080) (294586470561, 831669051700092, 2934487495660584) (300865159761, 841868784526737, 2996704435235664) (by decide) (by decide) (by decide) chunk1600 tail1650
  have tail1536 : moments 1536 2477 = (308898457681, 854461018656481, 3076340145947856) :=
    join 1536 64 2413 1600 2477 (8033297920, 12592234129744, 79635710712192) (300865159761, 841868784526737, 2996704435235664) (308898457681, 854461018656481, 3076340145947856) (by decide) (by decide) (by decide) chunk1536 tail1600
  have tail1472 : moments 1472 2541 = (316917278289, 866517436150833, 3155961298796112) :=
    join 1472 64 2477 1536 2541 (8018820608, 12056417494352, 79621152848256) (308898457681, 854461018656481, 3076340145947856) (316917278289, 866517436150833, 3155961298796112) (by decide) (by decide) (by decide) chunk1472 tail1536
  have tail1408 : moments 1408 2605 = (324902222929, 878012010468737, 3235532064724944) :=
    join 1408 64 2541 1472 2605 (7984944640, 11494574317904, 79570765928832) (316917278289, 866517436150833, 3155961298796112) (324902222929, 878012010468737, 3235532064724944) (by decide) (by decide) (by decide) chunk1408 tail1472
  have tail1344 : moments 1344 2669 = (332825504337, 888910901080785, 3314980476555600) :=
    join 1344 64 2605 1408 2669 (7923281408, 10898890612048, 79448411830656) (324902222929, 878012010468737, 3235532064724944) (332825504337, 888910901080785, 3314980476555600) (by decide) (by decide) (by decide) chunk1344 tail1408
  have tail1280 : moments 1280 2733 = (340650946641, 899174600952865, 3394185544084176) :=
    join 1280 64 2669 1344 2733 (7825442304, 10263699872080, 79205067528576) (332825504337, 888910901080785, 3314980476555600) (340650946641, 899174600952865, 3394185544084176) (by decide) (by decide) (by decide) chunk1280 tail1344
  have tail1216 : moments 1216 2797 = (348333985361, 908760084029809, 3472964369179728) :=
    join 1216 64 2733 1280 2797 (7683038720, 9585483076944, 78778825095552) (340650946641, 899174600952865, 3394185544084176) (348333985361, 908760084029809, 3472964369179728) (by decide) (by decide) (by decide) chunk1216 tail1280
  have tail1152 : moments 1152 2861 = (355821667409, 917622952719041, 3551059260882384) :=
    join 1152 64 2797 1216 2861 (7487682048, 8862868689232, 78094891702656) (348333985361, 908760084029809, 3472964369179728) (355821667409, 917622952719041, 3551059260882384) (by decide) (by decide) (by decide) chunk1152 tail1216
  have tail1088 : moments 1088 2925 = (363052651089, 925719585374225, 3628124850501456) :=
    join 1088 64 2861 1152 2925 (7230983680, 8096632655184, 77065589619072) (355821667409, 917622952719041, 3551059260882384) (363052651089, 925719585374225, 3628124850501456) (by decide) (by decide) (by decide) chunk1088 tail1152
  have tail1024 : moments 1024 2989 = (369957206097, 933009283778913, 3703715206713552) :=
    join 1024 64 2925 1088 2989 (6904555008, 7289698404688, 75590356212096) (363052651089, 925719585374225, 3628124850501456) (369957206097, 933009283778913, 3703715206713552) (by decide) (by decide) (by decide) chunk1024 tail1088
  have tail960 : moments 960 3053 = (376457213521, 939456420630193, 3777270950660688) :=
    join 960 64 2989 1024 3053 (6500007424, 6447136851280, 73555743947136) (369957206097, 933009283778913, 3703715206713552) (376457213521, 939456420630193, 3777270950660688) (by decide) (by decide) (by decide) chunk960 tail1024
  have tail896 : moments 896 3117 = (382466165841, 945032587022337, 3848106371048400) :=
    join 896 64 3053 960 3117 (6008952320, 5576166392144, 70835420387712) (376457213521, 939456420630193, 3777270950660688) (382466165841, 945032587022337, 3848106371048400) (by decide) (by decide) (by decide) chunk896 tail960
  have tail832 : moments 832 3181 = (387889166929, 949718739930449, 3915396539243856) :=
    join 832 64 3117 896 3181 (5423001088, 4686152908112, 67290168195456) (382466165841, 945032587022337, 3848106371048400) (387889166929, 949718739930449, 3915396539243856) (by decide) (by decide) (by decide) chunk832 tail896
  have tail768 : moments 768 3245 = (392624721697, 953508743745051, 3978165386340624) :=
    join 768 64 3181 832 3245 (4735554768, 3790003814602, 62768847096768) (387889166929, 949718739930449, 3915396539243856) (392624721697, 953508743745051, 3978165386340624) (by decide) (by decide) (by decide) chunk768 tail832
  have tail704 : moments 704 3309 = (396591807137, 956430760576347, 4035309501216912) :=
    join 704 64 3245 768 3309 (3967085440, 2922016831296, 57144114876288) (392624721697, 953508743745051, 3978165386340624) (396591807137, 956430760576347, 4035309501216912) (by decide) (by decide) (by decide) chunk704 tail768
  have tail640 : moments 640 3373 = (399763947041, 958565062636699, 4085734095792144) :=
    join 640 64 3309 704 3373 (3172139904, 2134302060352, 50424594575232) (396591807137, 956430760576347, 4035309501216912) (399763947041, 958565062636699, 4085734095792144) (by decide) (by decide) (by decide) chunk640 tail704
  have tail576 : moments 576 3437 = (402173385121, 960032677911515, 4128543393347472) :=
    join 576 64 3373 640 3437 (2409438080, 1467615274816, 42809297555328) (399763947041, 958565062636699, 4085734095792144) (402173385121, 960032677911515, 4128543393347472) (by decide) (by decide) (by decide) chunk576 tail640
  have tail512 : moments 512 3501 = (403910708271, 960980162337055, 4163233702132296) :=
    join 512 64 3437 576 3501 (1737323150, 947484425540, 34690308784824) (402173385121, 960032677911515, 4128543393347472) (403910708271, 960980162337055, 4163233702132296) (by decide) (by decide) (by decide) chunk512 tail576
  have tail448 : moments 448 3565 = (405106702911, 961556175715807, 4189858608241224) :=
    join 448 64 3501 512 3565 (1195994640, 576013378752, 26624906108928) (403910708271, 960980162337055, 4163233702132296) (405106702911, 961556175715807, 4189858608241224) (by decide) (by decide) (by decide) chunk448 tail512
  have tail384 : moments 384 3629 = (405887501391, 961882503139999, 4209030440778312) :=
    join 384 64 3565 448 3629 (780798480, 326327424192, 19171832537088) (405106702911, 961556175715807, 4189858608241224) (405887501391, 961882503139999, 4209030440778312) (by decide) (by decide) (by decide) chunk384 tail448
  have tail320 : moments 320 3693 = (406362548831, 962050849134431, 4221781863602760) :=
    join 320 64 3629 384 3693 (475047440, 168345994432, 12751422824448) (405887501391, 961882503139999, 4209030440778312) (406362548831, 962050849134431, 4221781863602760) (by decide) (by decide) (by decide) chunk320 tail384
  have tail256 : moments 256 3757 = (406624513135, 962127081311263, 4229411291675208) :=
    join 256 64 3693 320 3757 (261964304, 76232176832, 7629428072448) (406362548831, 962050849134431, 4221781863602760) (406624513135, 962127081311263, 4229411291675208) (by decide) (by decide) (by decide) chunk256 tail320
  have tail192 : moments 192 3821 = (406749284991, 962155525337311, 4233328272235080) :=
    join 192 64 3757 256 3821 (124771856, 28444026048, 3916980559872) (406624513135, 962127081311263, 4229411291675208) (406749284991, 962155525337311, 4233328272235080) (by decide) (by decide) (by decide) chunk192 tail256
  have tail128 : moments 128 3885 = (406795977871, 962163259901343, 4234898865977928) :=
    join 128 64 3821 192 3885 (46692880, 7734564032, 1570593742848) (406749284991, 962155525337311, 4233328272235080) (406795977871, 962163259901343, 4234898865977928) (by decide) (by decide) (by decide) chunk128 tail192
  have tail64 : moments 64 3949 = (406806928031, 962164411681375, 4235291028232776) :=
    join 64 64 3885 128 3949 (10950160, 1151780032, 392162254848) (406795977871, 962163259901343, 4234898865977928) (406806928031, 962164411681375, 4235291028232776) (by decide) (by decide) (by decide) chunk64 tail128
  have tail0 : moments 0 4013 = (406807694511, 962164450311967, 4235319990139464) :=
    join 0 64 3949 64 4013 (766480, 38630592, 28961906688) (406806928031, 962164411681375, 4235291028232776) (406807694511, 962164450311967, 4235319990139464) (by decide) (by decide) (by decide) chunk0 tail64
  exact tail0
theorem sourceCount_eq : sourceCount = 406807694511 := by
  have e := (moments_eq 4013).symm.trans checked
  have h := Prod.mk.inj e
  rw [sourceCount]; exact h.1
theorem sourceDegree_eq : sourceDegree = 962164450311967 := by
  have e := (moments_eq 4013).symm.trans checked
  have h := Prod.mk.inj (Prod.mk.inj e).2
  rw [sourceDegree]; exact h.1
theorem sourceIndex24_eq : sourceIndex24 = 11874264712496136 := by
  have hp := congrArg (fun x : Moments => x.2.2) ((moments_eq 4013).symm.trans checked)
  change (∑ q ∈ range 4013, cumPrefix (gradeCap q) 1650) = 4235319990139464 at hp
  unfold sourceIndex24
  simp only [indexMoment, sum_sub_distrib, ← mul_sum]
  change (24 * 1650) * sourceCount - (∑ q ∈ range 4013, cumPrefix (gradeCap q) 1650) = _
  rw [sourceCount_eq, hp]
  decide
def compactCount (A D : ℕ) : ℕ :=
  3000*A*406807694511 + 494761029687339 - D*962164450311967
theorem exact_columns (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A) :
    (columns A D hD).card = compactCount A D := by
  have h := scaled_columns A D hA hD hBudget
  rw [sourceCount_eq, sourceDegree_eq, sourceIndex24_eq] at h
  unfold compactCount
  push_cast at h
  omega
#print axioms exact_columns
end TaperColumns

end Merged_PrimaryTaperColumnData

-- merged module PrimaryTaperFamily
section Merged_PrimaryTaperFamily

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace PrimaryTaper

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open MvPolynomial (mem_support_iff monomial)
open TaperColumns
open TaperBudget (cap)
open scoped BigOperators

open P0_9_2 (weight_eq_sum map_independent_family pointContact high_monomial_vanishes)
open TaperColumns (sumCount sumIndex sumDifferentiated sumGrade sumOld)

def primaryBox : Shape := ⟨4012, 1650, 550⟩

def TrueWeightLE {n : ℕ} (D : ℕ) (P : Row n) (T : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree + m.sum (fun i a => (D - i.val) * a) ≤ T

def JetsBounded (P : Row 4) : Prop := ∀ m ∈ P.support, m ∈ jetExponents

theorem row_bounds {A D : ℕ} (Q : Source A D) :
    InBox (shape (toRow Q.1)) primaryBox ∧
    TrueWeightLE D (toRow Q.1) (3000*A-1) ∧ JetsBounded (toRow Q.1) := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4012 ∧
      m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
      ((toRow Q.1).coeff m).natDegree + m.sum (fun i a => (D - i.val) * a) ≤ 3000*A-1 ∧
      m ∈ jetExponents := by
    let n := ((toRow Q.1).coeff m).natDegree
    have hc : (Q.1).coeff (m.optionElim n) ≠ 0 := by
      rw [← MvPolynomial.optionEquivRight_coeff_coeff]
      change ((toRow Q.1).coeff m).coeff n ≠ 0
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact mem_support_iff.mp hm
    have supportBound : ∀ e ∈ Q.1.support, Eligible A D e := Q.2
    obtain ⟨⟨hb, hj, ht, hcap⟩, hw⟩ := supportBound _ (mem_support_iff.mpr hc)
    have hmem : m ∈ jetExponents := by
      change m.weight K1_13_2_2.gradeWeight ≤ 4012 ∧ m.weight K1_13_2_2.oldWeight ≤ 1650 ∧
        m 1+m 2+m 3 ≤ cap (m.weight K1_13_2_2.gradeWeight)
      rw [sumGrade, sumOld]
      rw [sumCount] at hb
      rw [sumIndex] at hj
      rw [sumDifferentiated, sumCount] at hcap
      simpa only [Finsupp.optionElim_apply_some] using And.intro hb (And.intro hj hcap)
    have jb : jetDegreeWeight (d := 3) = (fun v => v.elim 0 (fun _ => 1)) := by
      funext v; cases v <;> rfl
    have ji : jetDerivativeWeight (d := 3) = (fun v => v.elim 0 (fun i => i.val)) := by
      funext v; cases v <;> rfl
    have jw : differentialWeight (d := 3) D =
        (fun v => v.elim 1 (fun i => D - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 550 at ht
    simp only [Finsupp.weight_optionElim, zero_mul, zero_add, one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _ => 1)] at hb
    rw [weight_eq_sum m (fun i => i.val)] at hj
    rw [weight_eq_sum m (fun i => D - i.val)] at hw
    exact ⟨by simpa only [one_mul] using hb, hj, ht, hw, hmem⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Finset.sup_le fun m hm => (h m hm).1
  · exact Finset.sup_le fun m hm => (h m hm).2.1
  · exact MvPolynomial.degreeOf_le_iff.mpr fun m hm => (h m hm).2.2.1
  · exact fun m hm => (h m hm).2.2.2.1
  · exact fun m hm => (h m hm).2.2.2.2

def nodeMap {A D : ℕ} (x y : Geom) : Source A D →ₗ[Geom] Local :=
  (localConstraintAt 3000 x y).domRestrict (Source A D)

def wordMap (A D : ℕ) (w : I → K) : Source A D →ₗ[Geom] (I → Local) :=
  LinearMap.pi fun i => nodeMap (embed (node i)) (embed (w i))

theorem contact_of_word_kernel {A D : ℕ} (w : I → K) (Q : Source A D) (hQ : wordMap A D w Q = 0) :
    Contact w (toRow Q.1) := by
  intro i S hS
  rw [K1_13_2.atJet_toRow]
  have hi : SatisfiesLocalConstraints (d := 3) 3000 (embed (node i)) (embed (w i)) Q.1 := congrFun hQ i
  have hd := pointContact (embed (node i)) (embed (w i)) Q.1 S hS hi
  with_reducible exact hd

theorem local_range_finite (x y : Geom) :
    Module.Finite Geom (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
      (TaperNormalize.space cap))) := by
  have hsub :
      LinearMap.range ((localConstraintAt 3000 x y).domRestrict (TaperNormalize.space cap)) ≤
        LinearMap.range (K1_13_2.nodeMap 0 0) := by
    rintro _ ⟨Q, rfl⟩
    let R := globalPointTranslation x y Q.1
    have hR : R ∈ TaperNormalize.space cap := TaperNormalize.translate TaperBudget.cap_antitone x y Q
    change localConstraintAt 3000 x y Q.1 ∈ _
    rw [localConstraintAt_eq_zero_globalPointTranslation]
    change localConstraintAt 3000 0 0 R ∈ _
    rw [congrArg (localConstraintAt 3000 0 0) R.as_sum, map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    by_cases hx : e none < 3000
    · obtain ⟨hg, hj, ht, _⟩ := hR he
      have hw := weight_le_add_mul_totalJetDegree 133671 e
      change e.weight (differentialWeight 133671) ≤ e none + 133671 * e.weight jetDegreeWeight at hw
      have hOld : K1_13_2.SourceEligible e := ⟨hg,hj,ht,by omega⟩
      have hMono : monomial e (R.coeff e) ∈ K1_13_2.SourceSpace :=
        (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hOld)
      exact ⟨⟨_, hMono⟩, rfl⟩
    · rw [high_monomial_vanishes _ _ (Nat.le_of_not_gt hx)]
      exact Submodule.zero_mem _
  exact Module.Finite.of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)









theorem symbol_rank {n : ℕ} (x : Geom) (e : Fin n → Row 4)
    (he : ∀ i, JetsBounded (e i))
    (hli : LinearIndependent Geom (fun i => K1_13_3.symbolAt x (e i))) :
    n ≤ 406807694511 := by
  let V := MvPolynomial.restrictSupport Geom jetExponents
  let v : Fin n → V := fun i =>
    ⟨K1_13_3.symbolAt x (e i), fun m hm => he i m (MvPolynomial.support_map_subset _ _ hm)⟩
  letI : Module.Finite Geom V := MvPolynomial.restrictSupport_finite jetExponents_finite
  have hv : LinearIndependent Geom v := LinearIndependent.of_comp V.subtype hli
  have hd : Module.finrank Geom V = jetColumns.card := by
    change Module.finrank Geom (MvPolynomial.restrictSupport Geom jetExponents) = _
    rw [← jetExponents_finite.coe_toFinset]
    exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) jetColumns
  have hn : jetColumns.card = 406807694511 := by
    exact_mod_cast jet_card_eq.trans sourceCount_eq
  simpa only [Fintype.card_fin, hd, hn] using hv.fintype_card_le_finrank

#print axioms symbol_rank
end
end PrimaryTaper

end Merged_PrimaryTaperFamily

-- merged module Wide50EulerPrimaryFamily
section Merged_Wide50EulerPrimaryFamily

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace Wide50EulerPrimary

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (Local toRow)
open P3 (I K node)
open PrimaryTaper (nodeMap wordMap row_bounds primaryBox TrueWeightLE JetsBounded contact_of_word_kernel)
open TaperColumns
open KoalaTaperTransfer
open scoped BigOperators
open PrimaryTaper (local_range_finite)
open P0_9_2 (map_independent_family)

private theorem rank_at_position {A D : ℕ} (x y : Geom) :
    Module.finrank Geom (LinearMap.range (nodeMap (A:=A) (D:=D) x y)) ≤ KoalaTaperTransfer.localRank := by
  letI := local_range_finite x y
  apply (Submodule.finrank_mono ?_).trans (KoalaTaperTransfer.node_rank x y)
  rintro _ ⟨Q, rfl⟩
  exact ⟨⟨Q.1, fun e he => (Q.2 he).1⟩, rfl⟩

theorem word_rank (A D : ℕ) (hD : 3<D) (w : I → K) :
    Module.finrank Geom (LinearMap.range (wordMap A D w)) ≤ 262144 * KoalaTaperTransfer.localRank := by
  letI : Fact (3<D) := ⟨hD⟩
  let nmap (i : I) := nodeMap (A:=A) (D:=D) (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : Source A D →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap A D w = g.comp f := rfl
  rw [hw]
  calc
    _ ≤ Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, KoalaTaperTransfer.localRank := Finset.sum_le_sum fun i _ => rank_at_position _ _
    _ = _ := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]

def sourceRank (A D : ℕ) : ℕ := compactCount A D - 262144 * KoalaTaperTransfer.localRank

def layerNeed (A D : ℕ) : ℕ := sourceRank A D / (A-D+3) + 1

theorem primary_family (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A)
    (w : I → K) {n : ℕ} (hn : n ≤ sourceRank A D) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE D (e i) (3000*A-1) ∧
        JetsBounded (e i) ∧ Contact w (e i) := by
  letI : Fact (3<D) := ⟨hD⟩
  let lift : LinearMap.ker (wordMap A D w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp ((Source A D).subtype.comp (LinearMap.ker (wordMap A D w)).subtype)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  have hdim := (wordMap A D w).finrank_range_add_finrank_ker
  have hcols := (finrank_source A D hD).trans (exact_columns A D hA hD hBudget)
  have hr := word_rank A D hD w
  have hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap A D w)) := by
    unfold sourceRank at hn
    omega
  let admissible (P : Row 4) :=
    InBox (shape P) primaryBox ∧ TrueWeightLE D P (3000*A-1) ∧ JetsBounded P ∧ Contact w P
  refine map_independent_family (V := LinearMap.ker (wordMap A D w)) (W := Row 4)
    (n := n) lift hinj admissible ?_ hker
  intro Q
  obtain ⟨hbox,hweight,hJets⟩ := row_bounds Q.1
  exact ⟨hbox,hweight,hJets,contact_of_word_kernel w Q.1 (LinearMap.mem_ker.mp Q.2)⟩




#print axioms primary_family
end
end Wide50EulerPrimary

end Merged_Wide50EulerPrimaryFamily

end Merged6967_Wide50EulerPrimaryFamily
