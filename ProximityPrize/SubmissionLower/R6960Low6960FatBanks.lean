import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.RingHomShortcuts

-- merged module R6960Low6960FatDefs
section Merged_R6960Low6960FatDefs

set_option Elab.async false
section
namespace Low6960Fat
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
abbrev firstOrder : ℕ := 4499363
abbrev secondOrder : ℕ := 1782313
abbrev firstCut : ℕ := 5000 * 179808 - firstOrder
abbrev secondCut : ℕ := 5000 * 179808 - secondOrder
abbrev bankRank : ℕ := 548208823042247212444
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  7035 * a none + 48739 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
/-- The low fat chain works with rows whose seed degree is at most 27,000. -/
abbrev seedCap : ℕ := 27000
def Caps27 {R : Type*} [CommSemiring R] (a : K1_13.Shape) (F : SeedRow R) : Prop :=
  Caps a F ∧ seedDegree F ≤ seedCap
def Source27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Source w P L a t F ∧ seedDegree F ≤ seedCap
def HasRank27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧ ∀ i, Source27 w P L a t (e i)
abbrev commonBox : K1_13.Shape := ⟨2502, 811, 0⟩
abbrev resultantBox : K1_13.Shape := ⟨367443000, 124200000, 0⟩
structure FatEquations where
  common : K1_13.Row 3
  residual : K1_13.Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ commonBox.b
  common_index : K1_13.indexDegree common ≤ commonBox.j
  residual_total : residual.totalDegree ≤ resultantBox.b
  residual_index : K1_13.indexDegree residual ≤ resultantBox.j
structure CommonPair (F G : GenericRow) where
  fixed : Finset GenericRow
  moving : Finset GenericRow
  pure : (Polynomial GenericX)
  exponent : GenericRow → ℕ
  left : GenericRow
  right : GenericRow
  pure_ne : pure ≠ 0
  pure_degree : pure.natDegree ≤ 140000
  fixed_kind : ∀ f ∈ fixed, Irreducible f ∧ 0 < jetTotal f ∧ seedDegree f = 0
  moving_kind : ∀ f ∈ moving, Irreducible f ∧ 0 < jetTotal f ∧
    0 < seedDegree f ∧ f.degreeOf (some 2) = 0
  fixed_total : jetTotal (∏ f ∈ fixed, f) ≤ 122
  fixed_index : jetIndex (∏ f ∈ fixed, f) ≤ 41
  moving_total : jetTotal (∏ f ∈ moving, f) ≤ 17
  moving_index : jetIndex (∏ f ∈ moving, f) ≤ 5
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 70
  left_eq : F = (pureSeed pure * (∏ f ∈ fixed, f ^ exponent f) *
    (∏ f ∈ moving, f ^ exponent f)) * left
  right_eq : G = (pureSeed pure * (∏ f ∈ fixed, f ^ exponent f) *
    (∏ f ∈ moving, f ^ exponent f)) * right
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  proper : IsRelPrime left right
  left_caps : Caps27 firstBox left
  right_caps : Caps27 secondBox right
def Necessary {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P) :
    Submodule Geom PhysicalRow :=
  Submodule.span Geom {Q | ∃ t F a, Source27 w P L secondBox t F ∧
    t + mixedWeight a ≤ secondCut ∧ Q = mixedHasse a F}
def MixedOrder (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ) : Prop :=
  ∀ a ∈ (translate (atPoint z y) F).support, d ≤ mixedWeight a
def PairOrders (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) : Prop :=
  MixedOrder F z y firstOrder ∧ MixedOrder G z y secondOrder
end
end Low6960Fat
end
section
namespace Low6960Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
structure Messages (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) : Prop where
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 179808 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2345 →
    (∃ F, F ≠ 0 ∧ Source27 w P L firstBox firstCut F) ∧
    HasRank27 w P L secondBox secondCut bankRank
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow),
    F ≠ 0 → Caps27 firstBox F → HasRank27 w P L secondBox secondCut bankRank →
    ∃ G, G ∈ Necessary w P L ∧ Nonempty (CommonPair (toGeneric F) (toGeneric G))
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∀ (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2345 →
      (∀ F, Source27 w P L firstBox firstCut F → ∀ γ ∈ Γ,
        MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstOrder) ∧
      (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
        MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondOrder)

abbrev fatOrder : ℕ := 23389
def Holds (E : FatEquations) (S : (Polynomial K1_13.Geom)) : Prop :=
  K1_13.atJet E.common S = 0 ∨ K1_13.OrderAt E.residual S fatOrder

def Equations : Prop :=
  ∀ (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)),
    (∀ γ ∈ Γ, (s γ).natDegree ≤ 133416) →
    (∀ γ ∈ Γ, ∃ T : Finset I, 179808 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i) →
    ∀ P : K1_13.PoleData Γ s, P.H.natDegree ≤ 2345 →
    ∃ (book : Finset K1.K) (E : FatEquations), book.card ≤ 140000 ∧
      ∀ γ ∈ Γ, γ ∉ book → Holds E (K1_13.extend (s γ))
end
end Low6960Fat
end

end Merged_R6960Low6960FatDefs

-- merged module R6960Low6960FatSeed
section Merged_R6960Low6960FatSeed
set_option Elab.async false
section
namespace Low6960FatSeed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_2
open MvPolynomial
open Low6960Fat (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_2 (seedView seedCoeff flatCoeff coeff_mem_capped normalize normalize_mem_capped node_coeff toRow contactWeight_eq)
private theorem seedCoeff_eq_zero27 {F : PhysicalRow} (hS : seedDegree F ≤ 27000)
    {n : ℕ} (hn : 27000 < n) : seedCoeff n F = 0 := by
  have hdeg : (seedView F).natDegree ≤ 27000 := by
    simpa only [seedView, natDegree_optionEquivLeft, seedDegree] using hS
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hn)
private theorem mem_contact_of_origin_eq_zero27 {x v : Geom} {F : PhysicalRow}
    (hS : seedDegree F ≤ 27000)
    (h : ∀ n : Fin 27001, origin (normalize x v (flatCoeff n F)) = 0) :
    F ∈ contactAt x v := by
  apply (mem_contactAt x v F).mpr
  intro e
  let P := (backwardShift x v F).coeff (e.some.optionElim (e none))
  let E := Polynomial.taylorEquiv x
  have hE : E ((Polynomial.X - Polynomial.C x) ^ (5000 - 3 * e (some 0))) =
      Polynomial.X ^ (5000 - 3 * e (some 0)) := by
    have hX : E (Polynomial.X - Polynomial.C x) = Polynomial.X := by
      rw [map_sub]
      change Polynomial.taylor x Polynomial.X - Polynomial.taylor x (Polynomial.C x) = _
      simp
    rw [map_pow, hX]
  have hP : P = (backwardShift x v F).coeff e := by simp [P]
  rw [← hP, ← map_dvd_iff E, hE, Polynomial.X_pow_dvd_iff]
  intro i hi
  have hcoeff : E P =
      (toRow (shear (normalize x v (flatCoeff (e none) F)))).coeff e.some :=
    (node_coeff x v F (e none) e.some).symm
  rw [hcoeff]
  change ((optionEquivRight Geom (Fin 3) _).coeff e.some).coeff i = 0
  rw [optionEquivRight_coeff_coeff]
  by_cases hn : e none < 27001
  · have hz := congrArg (fun Q : Flat => Q.coeff (e.some.optionElim i)) (h ⟨e none, hn⟩)
    change (weightedTruncation contactWeight 5000
      (shear (normalize x v (flatCoeff (e none) F)))).coeff (e.some.optionElim i) = 0 at hz
    have hlt : (e.some.optionElim i).weight contactWeight < 5000 := by
      rw [contactWeight_eq]
      change i + 3 * e (some 0) < 5000
      omega
    rw [coeff_weightedTruncation] at hz
    simpa only [hlt, ite_true] using hz
  · have hz := seedCoeff_eq_zero27 hS (n := e none) (by omega)
    have hz' : flatCoeff (e none) F = 0 := by
      change toRow.symm (seedCoeff (e none) F) = 0
      rw [hz, map_zero]
    simp [hz']
private def nodeInput (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps27 b.box F) (n : Fin 27001) : V →ₗ[Geom] Capped b.box.b :=
  ((normalize x v).toLinearMap ∘ₗ flatCoeff n ∘ₗ V.subtype).codRestrict _
    (fun F => normalize_mem_capped (coeff_mem_capped (hcap F F.2).1 n) x v)
private def nodeMap (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps27 b.box F) : V →ₗ[Geom] (Fin 27001 → cappedRange b.box.b) :=
  LinearMap.pi fun n =>
    (origin.domRestrict (Capped b.box.b)).rangeRestrict ∘ₗ nodeInput b x v V hcap n
theorem codim_le_cappedRange27 (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    [Module.Finite Geom V] (hcap : ∀ F ∈ V, Caps27 b.box F) :
    codimIn V (contactAt x v) ≤ 27001 * Module.finrank Geom (cappedRange b.box.b) := by
  let A := nodeMap b x v V hcap
  have hzero (F : A.ker) : (F.1 : PhysicalRow) ∈ contactAt x v := by
    apply mem_contact_of_origin_eq_zero27 (hcap F.1 F.1.2).2
    intro n
    have h := congrFun (LinearMap.mem_ker.mp F.2) n
    have hval := congrArg (fun z : cappedRange b.box.b => z.val) h
    change origin (normalize x v (flatCoeff n F.1.1)) = 0 at hval
    exact hval
  let f : A.ker →ₗ[Geom] ↥(V ⊓ contactAt x v) :=
    (V.subtype ∘ₗ A.ker.subtype).codRestrict _ fun F => Submodule.mem_inf.mpr ⟨F.1.2, hzero F⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg (fun s : ↥(V ⊓ contactAt x v) => (s : PhysicalRow)) h
    exact he
  have hk := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hr := Submodule.finrank_le A.range
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr
  have hnull := LinearMap.finrank_range_add_finrank_ker (K := Geom)
    (V := ↥V) (V₂ := Fin 27001 → cappedRange b.box.b) A
  unfold codimIn
  omega
end
end Low6960FatSeed
end
section
namespace Low6960FatSeed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_2
open Low6960Fat (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_2 (bank_bound plane_rank_le)
theorem contact_bound27 : ∀ (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow),
    Module.Finite Geom V → (∀ F ∈ V, Caps27 b.box F) →
    codimIn V (contactAt x v) ≤ 27001 * b.nodeRank := by
  intro b x v V hV hcap
  let : Module.Finite Geom V := hV
  obtain ⟨p, hp⟩ := bank_bound K1_13_4_2_2_3.proof K1_13_4_2_2_4.proof
    K1_13_4_2_2_5.proof K1_13_4_2_2_6.proof b
  apply (codim_le_cappedRange27 b x v V hcap).trans
  apply Nat.mul_le_mul_left
  apply (cappedRange_le_sum b.box.b (fun q k => blockBound q (offset k) (p q k)) ?_).trans hp
  intro q hq k hk
  have hB : b.box.b + 1 ≤ 6821 := by cases b <;> decide
  exact (rank_originBlock_le_plane q k).trans
    (plane_rank_le K1_13_4_2_2_1.proof K1_13_4_2_2_2.proof (hq.trans_le hB) hk (p q k))
end
end Low6960FatSeed
end
section
namespace Low6960FatSeed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3
open Low6960Fat (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3 (clearedTest clearedTest_apply codim_le_test_finrank)
open K1_13_4_2 (codim_inf_le codim_finset_inf_le codim_antitone dimension_of_debits)
def poleDebit27 (a : Shape) : ℕ :=
  ∑ q ∈ Finset.range (a.b + 1),
    (a.b + a.j - q) * gradeCount a q * (27001 + (a.b - q))
abbrev SeedCoeff27 (a : Shape) (q : ℕ) := Fin (27001 + (a.b - q))
def c2_27 : Prop :=
  ∀ (a : Shape) (α : Geom) (N D : (Polynomial Geom)), D ≠ 0 →
    N.natDegree ≤ 1 → D.natDegree ≤ 1 →
    let z₀ : GenericSeed := algebraMap (Polynomial Geom) GenericSeed N / algebraMap (Polynomial Geom) GenericSeed D
    ∃ p : ∀ q : Fin (a.b + 1), PhysicalRow →ₗ[Geom] (JetCoeff a q.val → (Polynomial Geom)),
      ∀ F : PhysicalRow, Caps27 a F →
        (∀ e ∈ (centered z₀ F).support, admissible a e) ∧
        ∀ (q : Fin (a.b + 1)) (c : JetCoeff a q.val),
          (p q F c).natDegree ≤ 27000 + (a.b - q.val) ∧
          algebraMap (Polynomial Geom) GenericSeed (p q F c) =
            (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q.val) *
              localCoeff a α q.val c (centered z₀ F)
end
end Low6960FatSeed
end
section
namespace Low6960FatSeed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3 K1_13_4_2_3_2
open Low6960Fat (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3_2 (cleared cleared_apply clearedFactor support_bounds grade_sub centered_admissible map_cleared seedMap grade)
private theorem cleared_degree27 {a : Shape} {α : Geom} {N D : (Polynomial Geom)}
    (hN : N.natDegree ≤ 1) (hD : D.natDegree ≤ 1) {F : PhysicalRow} (hF : Caps27 a F)
    (q : Fin (a.b + 1)) (c : JetCoeff a q.val) :
    (cleared a α N D q F c).natDegree ≤ 27000 + (a.b - q.val) := by
  classical
  rw [cleared_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  split
  next he =>
    apply (Polynomial.natDegree_smul_le _ _).trans
    obtain ⟨hB, _, _, _⟩ := support_bounds hF.1 hm
    have hU : m none ≤ 27000 :=
      (MvPolynomial.le_degreeOf_of_mem_support none hm).trans hF.2
    have hq := grade_sub hB (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) he
    have hn : (N ^ (m (some 0) - k)).natDegree ≤ m (some 0) - k :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hN)
    have hd : (D ^ (a.b - grade m)).natDegree ≤ a.b - grade m :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hD)
    calc
      _ ≤ (m none + (m (some 0) - k)) + (a.b - grade m) := by
        unfold clearedFactor
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hd
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hn
        exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
      _ ≤ _ := by omega
  next => simp
theorem proof27 : c2_27 := by
  intro a α N D hD hNdeg hDdeg
  have hD' : seedMap D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)).2 hD
  refine ⟨cleared a α N D, fun F hF => ⟨centered_admissible _ hF.1, ?_⟩⟩
  intro q c
  exact ⟨cleared_degree27 hNdeg hDdeg hF q c, map_cleared hD' hF.1 q c⟩
end
end Low6960FatSeed
end
section
namespace Low6960FatSeed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3 K1_13_4_2_1 Finset
open Low6960Fat (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3 (clearedTest clearedTest_apply codim_le_test_finrank)
open K1_13_4_2 (codim_inf_le codim_finset_inf_le codim_antitone)
open K1_13_4_2_1 (credit extra grade_sum moment)
def c3_27 : Prop :=
  ∀ (Γ : Finset K) (s : K → (Polynomial K)) (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (α : Geom) (V : Submodule Geom PhysicalRow), Module.Finite Geom V →
    (∀ F ∈ V, Caps27 a F) → P.H.IsRoot α → P.H.derivative.eval α ≠ 0 →
    codimIn V (poleCondition P L a (localPole α)) ≤ poleDebit27 a
private theorem coeff_test_zero_iff27 {a : Shape} {q : ℕ} {α : Geom}
    {F : PhysicalRow} {G : RawRow} {D : (Polynomial Geom)} (hD : D ≠ 0)
    (w : JetCoeff a q → Geom) (p : PhysicalRow →ₗ[Geom] (JetCoeff a q → (Polynomial Geom)))
    (hp : ∀ c, (p F c).natDegree ≤ 27000 + (a.b - q) ∧
      algebraMap (Polynomial Geom) GenericSeed (p F c) =
        (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q) * localCoeff a α q c G) :
    (∀ k : SeedCoeff27 a q, (clearedTest w p F).coeff k.val = 0) ↔ dot a α q w G = 0 := by
  have hdeg : (clearedTest w p F).natDegree ≤ 27000 + (a.b - q) := by
    rw [clearedTest_apply]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ =>
      (Polynomial.natDegree_smul_le _ _).trans (hp c).1
  have hz : (∀ k : SeedCoeff27 a q, (clearedTest w p F).coeff k.val = 0) ↔
      clearedTest w p F = 0 := by
    refine ⟨fun h => Polynomial.ext fun n => ?_, by intro h k; rw [h, Polynomial.coeff_zero]⟩
    rw [Polynomial.coeff_zero]
    by_cases hn : n < 27001 + (a.b - q)
    · exact h ⟨n, hn⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hmap : algebraMap (Polynomial Geom) GenericSeed (clearedTest w p F) =
      (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q) * dot a α q w G := by
    rw [clearedTest_apply, dot, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Algebra.smul_def, map_mul, (hp c).2, IsScalarTower.algebraMap_apply Geom (Polynomial Geom) GenericSeed]
    ring
  rw [hz, ← (map_eq_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)), hmap]
  have hne : algebraMap (Polynomial Geom) GenericSeed D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)).2 hD
  simp [pow_ne_zero _ hne]
theorem simple_pole27 (h2 : c2_27) : c3_27 := by
  classical
  intro Γ s P L a α V hV hcap hroot hsimple
  obtain ⟨N, D, hD, hNdeg, hDdeg, hnorm⟩ := normalization P L α hroot hsimple
  obtain ⟨w, hw⟩ := K1_13_4_2_3_1.proof a α
  obtain ⟨p, hp⟩ := h2 a α N D hD hNdeg hDdeg
  let E := ∀ q : Fin (a.b + 1), (Test a q.val × SeedCoeff27 a q.val) → Geom
  let f : V →ₗ[Geom] E :=
    LinearMap.pi fun q => LinearMap.pi fun ij =>
      (Polynomial.lcoeff Geom ij.2.val).comp ((clearedTest (w q ij.1) (p q)).comp V.subtype)
  have hker : LinearMap.ker f = (poleCondition P L a (localPole α)).comap V.subtype := by
    ext F
    have h := hp F.val (hcap F.val F.property)
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    simp only [Submodule.subtype_apply, hnorm, hw _ h.1]
    constructor
    · intro hf q i
      apply (coeff_test_zero_iff27 hD (w q i) (p q) (h.2 q)).mp
      intro k
      exact congrFun (congrFun hf q) (i, k)
    · intro hf
      funext q ij
      exact (coeff_test_zero_iff27 hD (w q ij.1) (p q) (h.2 q)).mpr (hf q ij.1) ij.2
  have hdim : Module.finrank Geom E = poleDebit27 a := by
    unfold E poleDebit27
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range
      (fun q => (a.b + a.j - q) * gradeCount a q * (27001 + (a.b - q))) (a.b + 1)
  exact (codim_le_test_finrank _ _ f hker).trans hdim.le
theorem separable_rank27 (h3 : c3_27) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (V : Submodule Geom PhysicalRow) [hV : Module.Finite Geom V]
    (hcap : ∀ F ∈ V, Caps27 a F) (hsep : P.H.Separable) :
    codimIn V (poleCondition P L a (liftX P.H)) ≤ P.H.natDegree * poleDebit27 a := by
  classical
  let T : Finset Geom := ⟨P.H.roots, Polynomial.nodup_roots hsep⟩
  have hcard : T.card = P.H.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot (α : Geom) (hα : α ∈ T) : P.H.IsRoot α :=
    (Polynomial.mem_roots P.monic.ne_zero).mp hα
  have hprod : (∏ α ∈ T, localPole α) = liftX P.H := by
    have he : (∏ α ∈ T, (Polynomial.X - Polynomial.C α)) = P.H :=
      ((IsAlgClosed.splits P.H).eq_prod_roots_of_monic P.monic).symm
    change _ = Polynomial.mapRingHom (algebraMap Geom GenericSeed) P.H
    rw [← he, map_prod]
    simp [localPole]
  let W : Geom → Submodule Geom PhysicalRow := fun α => poleCondition P L a (localPole α)
  have hlocal (α : Geom) (hα : α ∈ T) : codimIn V (W α) ≤ poleDebit27 a := by
    apply h3 Γ s P L a α V hV hcap (hroot α hα)
    exact hsep.eval₂_derivative_ne_zero (RingHom.id Geom) (hroot α hα)
  have hsub : T.inf W ≤ poleCondition P L a (liftX P.H) := by
    intro F hF
    have hd (α : Geom) (hα : α ∈ T) :
        (MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j) ∣ restore P L F := by
      have hle : T.inf W ≤ W α := Finset.inf_le hα
      exact (mem_poleCondition P L a _ _).mp (hle hF)
    have hcop (α β : Geom) (hne : α ≠ β) :
        IsCoprime ((MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j))
          ((MvPolynomial.C (localPole β) : RawRow) ^ (a.b + a.j)) := by
      apply IsCoprime.pow
      apply IsCoprime.map (f := MvPolynomial.C)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr ((FaithfulSMul.algebraMap_injective Geom GenericSeed).ne hne)).isUnit
    have h := Finset.prod_dvd_of_coprime (t := T) (fun α _ β _ hne => hcop α β hne) hd
    rw [Finset.prod_pow, ← map_prod (MvPolynomial.C : Polynomial GenericSeed →+* RawRow), hprod] at h
    exact (mem_poleCondition P L a _ _).mpr h
  have hdim := codim_finset_inf_le V T W (poleDebit27 a) hlocal
  rw [hcard] at hdim
  exact (codim_antitone V hsub).trans hdim
theorem pole_eq27 (b : Bank) : poleDebit27 b.box = 27001 * credit b.box.b + extra b.box.b := by
  have hb : b.box = ⟨b.box.b, 2300, 1150⟩ := by cases b <;> rfl
  have hgrade (q : ℕ) : gradeCount b.box q = gradeCount ⟨b.box.b, 2300, 1150⟩ q :=
    congrArg (fun a => gradeCount a q) hb
  calc
    _ = jetSum b.box.b (fun q _ _ => (2300 + (b.box.b - q)) * (27001 + (b.box.b - q))) := by
      rw [grade_sum, poleDebit27]
      apply sum_congr rfl
      intro q hq
      have hq' := mem_range.mp hq
      have he : b.box.b + b.box.j - q = 2300 + (b.box.b - q) := by
        rw [box_index]
        omega
      rw [hgrade, he]
      ring
    _ = _ := by
      simp only [credit, extra, moment, jetSum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
      ring
end
end Low6960FatSeed
end

end Merged_R6960Low6960FatSeed

-- merged module R6960Low6960FatBanks
section Merged_R6960Low6960FatBanks

set_option Elab.async false
section
namespace Low6960FatBanks
open K1_13_4_2 (Bank)
def cut : Bank → ℕ
  | .first => Low6960Fat.firstCut
  | .second => Low6960Fat.secondCut
def targetRank : Bank → ℕ
  | .first => 1
  | .second => Low6960Fat.bankRank
theorem cut_large (b : Bank) : 131071 * b.box.b ≤ cut b + 1 := by
  cases b <;> decide
def rawBase (b : Bank) : ℕ := cut b + 1 - 131071 * b.box.b
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h
end Low6960FatBanks
end
section
namespace Low6960FatBanks
open K1_13 (Geom)
open K1_13_4 K1_13_4_2
open K1_13_4_2_1 (jetSum)
open Function
open scoped BigOperators Polynomial
noncomputable section
open P0_9_4_1 (Column colExp colX column column_li coordinate coordinate_column column_bounds space space_bounds)
open P0_9_4_1 (exponent_none)
open Low6960Fat (Caps27)
private abbrev NewColumn (b : Bank) (h : ℕ) :=
  Σ q : Fin (b.box.b + 1), Σ k : Fin (min q.val 1150 + 1),
    Σ l : Fin (min (q.val - k.val) (2300 - 2 * k.val) + 1),
      Fin (width b h q.val k.val l.val) × Fin 27001
private def offset (b : Bank) : ℕ := P0_9_4_1.cut b - cut b
private theorem cut_shift (b : Bank) : cut b + offset b = P0_9_4_1.cut b := by
  have h : cut b ≤ P0_9_4_1.cut b := by cases b <;> decide
  unfold offset
  omega
private theorem width_shift (b : Bank) (h q k l : ℕ) :
    width b h q k l + offset b = P0_9_4_1.width b h q k l := by
  have hc := cut_shift b
  have hl := cut_large b
  unfold width P0_9_4_1.width rawBase P0_9_4_1.rawBase
  omega
private def inOld (b : Bank) (h d : ℕ) (hd : d ≤ offset b) : NewColumn b h ↪ Column b h :=
  (Embedding.refl _).sigmaMap fun q =>
    (Embedding.refl _).sigmaMap fun k =>
      (Embedding.refl _).sigmaMap fun l =>
        ((Fin.addNatEmb d).trans (Fin.castLEEmb
          ((Nat.add_le_add_left hd _).trans_eq (width_shift b h q.val k.val l.val)))).prodMap
          (Fin.castLEEmb (by decide : 27001 ≤ 70001))
private abbrev base (b : Bank) (h : ℕ) := inOld b h 0 (Nat.zero_le _)
private def newSpace (b : Bank) (h : ℕ) : Submodule Geom PhysicalRow :=
  Submodule.span Geom (Set.range (column ∘ base b h))
private theorem occurs {b : Bank} {h : ℕ} {F : PhysicalRow}
    (hF : F ∈ newSpace b h) {e : SeedVar →₀ ℕ} {x : ℕ} (hne : (F.coeff e).coeff x ≠ 0) :
    ∃ c : NewColumn b h, colExp (base b h c) = e ∧ colX (base b h c) = x := by
  classical
  by_contra! hn
  have hle : newSpace b h ≤ LinearMap.ker (coordinate e x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change coordinate e x (column (base b h c)) = 0
    rw [coordinate_column, ite_eq_right]
    exact fun hc => (hn c hc.1 hc.2).elim
  exact hne (LinearMap.mem_ker.mp (hle hF))
private theorem seed_fits (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ newSpace b h) :
    seedDegree F ≤ 27000 := by
  unfold seedDegree
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  obtain ⟨c, hc, _⟩ := occurs hF (x := (F.coeff m).natDegree) (by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp hm)
  rcases c with ⟨q,k,l,x,u⟩
  have hu := u.isLt
  have h0 : colExp (base b h ⟨q,k,l,x,u⟩) none = u.val := by
    simp only [colExp, exponent_none]
    rfl
  rw [← hc, h0]
  omega
private theorem fits (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ newSpace b h) :
    Caps27 b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F := by
  have hle : newSpace b h ≤ space b h := Submodule.span_mono (by
    rintro _ ⟨c, rfl⟩
    exact ⟨base b h c, rfl⟩)
  refine ⟨⟨(space_bounds b h F (hle hF)).1, seed_fits b h F hF⟩, ?_⟩
  intro e he
  obtain ⟨c, hc, hx⟩ := occurs hF (by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp he)
  rcases c with ⟨q,k,l,x,u⟩
  let shifted := inOld b h (offset b) le_rfl ⟨q,k,l,x,u⟩
  have hw := (column_bounds shifted).2.2.2.2
  have he' : colExp shifted = e := hc
  have hx' : colX shifted = (F.coeff e).natDegree + offset b :=
    congrArg (· + offset b) hx
  rw [he', hx'] at hw
  have hs := cut_shift b
  omega
theorem ambient (b : Bank) (h : ℕ) :
    ∃ V : Submodule Geom PhysicalRow, Module.Finite Geom V ∧
      (∀ F ∈ V, Caps27 b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F) ∧
      Module.finrank Geom V = 27001 * jetSum b.box.b (width b h) := by
  refine ⟨newSpace b h, Module.Finite.span_of_finite _ (Set.finite_range _), fits b h, ?_⟩
  rw [newSpace, finrank_span_eq_card ((column_li b h).comp _ (base b h).injective)]
  simp only [NewColumn, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_comm _ 27001]
  unfold jetSum
  simp only [Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Fin.sum_univ_eq_sum_range]
end
end Low6960FatBanks
end
section
namespace Low6960FatBanks
open K1_13_4_2 (Bank poleDebit)
open K1_13_4_2_1 (jetSum)
open Finset
open scoped BigOperators
open K1_13_4_2_1 (moment moment_eq slice antidifference credit extra pole_eq bank_moments)
private def rawVolume (b : Bank) : ℕ := moment b.box.b (rawBase b) 1 131071 0
private theorem volume_eq (b : Bank) (h : ℕ) :
    jetSum b.box.b (width b h) = rawVolume b + credit b.box.b * h := by
  simp only [width, rawVolume, moment, credit, jetSum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring
private theorem first_raw : rawVolume .first = 2815563711416738340 := by
  change moment 6789 4699619 1 131071 0 = _
  exact moment_eq 6789 4699619 1 131071 0 _ (by decide) (by decide +kernel)
private theorem second_raw : rawVolume .second = 2836083706525644938 := by
  change moment 6820 3353468 1 131071 0 = _
  exact moment_eq 6820 3353468 1 131071 0 _ (by decide) (by decide +kernel)
private theorem endpoint (b : Bank) :
    targetRank b + 262144 * (27001 * b.nodeRank) + 2345 * extra b.box.b ≤
      27001 * rawVolume b := by
  obtain ⟨_, _, hfirst, hsecond⟩ := bank_moments
  cases b
  · have he : extra Bank.first.box.b = 0x1cc973f372d9cdc := hfirst
    have ha : (1 : ℕ) + 262144 * (27001 * 0x9bab8f5dfb7) + 2345 * 0x1cc973f372d9cdc ≤
        27001 * 2815563711416738340 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.first + 262144 * (27001 * Bank.first.nodeRank) + 2345 * x ≤ 27001 * y)
      he first_raw).mpr ha
  · have he : extra Bank.second.box.b = 0x1d32fca954a0ef7 := hsecond
    have ha : (548208823042247212444 : ℕ) + 262144 * (27001 * 0x9bac59312df) +
        2345 * 0x1d32fca954a0ef7 ≤ 27001 * 2836083706525644938 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.second + 262144 * (27001 * Bank.second.nodeRank) + 2345 * x ≤ 27001 * y)
      he second_raw).mpr ha
theorem budget (b : Bank) (h : ℕ) (hh : h ≤ 2345) :
    targetRank b + 262144 * (27001 * b.nodeRank) + h * Low6960FatSeed.poleDebit27 b.box ≤
      27001 * jetSum b.box.b (width b h) := by
  have he := endpoint b
  have hm := Nat.mul_le_mul_right (extra b.box.b) hh
  rw [Low6960FatSeed.pole_eq27, volume_eq, Nat.mul_add, Nat.mul_add]
  have hc : h * (27001 * credit b.box.b) = 27001 * (credit b.box.b * h) := by ring
  omega
end Low6960FatBanks
end
section
namespace Low6960FatBanks
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2
open Low6960Fat (Caps27)
open scoped Polynomial BigOperators
open K1_13_4_2 (codim_inf_le codim_finset_inf_le separable_rank dimension_of_debits)
private theorem simple_pole_bound : Low6960FatSeed.c3_27 :=
  Low6960FatSeed.simple_pole27 Low6960FatSeed.proof27
private theorem deformation_bound : K1_13_4_2.c4 :=
  K1_13_4_2_4.of_children K1_13_4_2_4_1.proof K1_13_4_2_4_2.proof
private theorem rank_of_bounds (b : Bank) (w : I → K) {Γ s}
    (P : PoleData Γ s) (L : ResidueChart P) (hh : P.H.natDegree ≤ 2345) :
    Low6960Fat.HasRank27 w P L b.box (cut b) (targetRank b) := by
  classical
  obtain ⟨V, hV, hbox, hdimV⟩ := ambient b P.H.natDegree
  have hsize := (budget b P.H.natDegree hh).trans_eq hdimV.symm
  let : Module.Finite Geom V := hV
  have hcap : ∀ F ∈ V, Caps27 b.box F := fun F hF => (hbox F hF).1
  let A : I → Submodule Geom PhysicalRow := fun i => contactAt (embed (node i)) (embed (w i))
  let U : Submodule Geom PhysicalRow := ⨅ i, A i
  let W : Submodule Geom PhysicalRow := poleCondition P L b.box (liftX P.H)
  have hU : codimIn V U ≤ 262144 * (27001 * b.nodeRank) := by
    have hA (i : I) (_ : i ∈ Finset.univ) : codimIn V (A i) ≤ 27001 * b.nodeRank :=
      Low6960FatSeed.contact_bound27 b (embed (node i)) (embed (w i)) V hV hcap
    have h := codim_finset_inf_le V (Finset.univ : Finset I) A (27001 * b.nodeRank) hA
    have hc : (Finset.univ : Finset I).card = 262144 := Fintype.card_fin (2 ^ 18)
    rw [hc, Finset.inf_univ_eq_iInf] at h
    exact h
  have hW : codimIn V W ≤ P.H.natDegree * Low6960FatSeed.poleDebit27 b.box := by
    apply deformation_bound Γ s P L b.box V _ hV
    intro P' L' _ hdeg hsep
    rw [← hdeg]
    exact Low6960FatSeed.separable_rank27 simple_pole_bound P' L' b.box V hcap hsep
  have hdebit := (codim_inf_le V U W).trans (Nat.add_le_add hU hW)
  let S : Submodule Geom PhysicalRow := V ⊓ (U ⊓ W)
  have hdim : targetRank b ≤ Module.finrank Geom S := dimension_of_debits hsize hdebit
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Geom) (M := ↥S) hdim
  let e : Fin (targetRank b) → PhysicalRow := fun i => (f i).val
  refine ⟨e, hf.map_injOn S.subtype Subtype.val_injective.injOn, ?_⟩
  intro i
  have hm := Submodule.mem_inf.mp (f i).property
  have hUW : e i ∈ U ⊓ W := hm.2
  have hb := hbox (e i) hm.1
  refine ⟨⟨hb.1.1, hb.2, ?_, (mem_poleCondition P L b.box _ _).mp (Submodule.mem_inf.mp hUW).2⟩, hb.1.2⟩
  intro j
  have hmem : e i ∈ A j := (Submodule.mem_iInf A).mp (Submodule.mem_inf.mp hUW).1 j
  exact (mem_contactAt (embed (node j)) (embed (w j)) (e i)).mp hmem
theorem proof : Low6960Fat.c1 := by
  intro w Γ s P L hh
  refine ⟨?_, rank_of_bounds .second w P L hh⟩
  obtain ⟨e, he, hsource⟩ := rank_of_bounds .first w P L hh
  let i : Fin (targetRank Bank.first) := ⟨0, by decide⟩
  exact ⟨e i, he.ne_zero i, hsource i⟩
end
end Low6960FatBanks
end

#print axioms Low6960FatBanks.proof

end Merged_R6960Low6960FatBanks
