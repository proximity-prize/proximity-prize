import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.FrontBranch12
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile
import ProximityPrize.SubmissionLower.UpperBranch3
import ProximityPrize.SubmissionLower.UpperBranch5

section Merged6967_Fat6966Bank24000
set_option Elab.async false



set_option Elab.async false

-- merged module R6960Fat6966Bank24000Defs
section Merged_R6960Fat6966Bank24000Defs

set_option Elab.async false
section
namespace Fat6966Bank24000
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
abbrev firstOrder : ℕ := 4086972
abbrev secondOrder : ℕ := 1814603
abbrev firstCut : ℕ := 5000 * 179759 - firstOrder
abbrev secondCut : ℕ := 5000 * 179759 - secondOrder
abbrev bankRank : ℕ := 1
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  6948 * a none + 48690 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
/-- The low fat chain works with rows whose seed degree is at most 24,0. -/
abbrev seedCap : ℕ := 24000
def Caps27 {R : Type*} [CommSemiring R] (a : K1_13.Shape) (F : SeedRow R) : Prop :=
  Caps a F ∧ seedDegree F ≤ seedCap
def Source27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Source w P L a t F ∧ seedDegree F ≤ seedCap
def HasRank27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧ ∀ i, Source27 w P L a t (e i)
open K1_13 (PoleData)
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2316 →
    (∃ F, F ≠ 0 ∧ Source27 w P L firstBox firstCut F) ∧
    HasRank27 w P L secondBox secondCut bankRank
end
end Fat6966Bank24000
end
end Merged_R6960Fat6966Bank24000Defs

-- merged module R6960Fat6966Bank24000Seed
section Merged_R6960Fat6966Bank24000Seed
set_option Elab.async false
section
namespace Fat6966Bank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_2
open MvPolynomial
open Fat6966Bank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_2 (seedView seedCoeff flatCoeff coeff_mem_capped normalize normalize_mem_capped node_coeff toRow contactWeight_eq)
private theorem seedCoeff_eq_zero27 {F : PhysicalRow} (hS : seedDegree F ≤ 24000)
    {n : ℕ} (hn : 24000 < n) : seedCoeff n F = 0 := by
  have hdeg : (seedView F).natDegree ≤ 24000 := by
    simpa only [seedView, natDegree_optionEquivLeft, seedDegree] using hS
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hn)
private theorem mem_contact_of_origin_eq_zero27 {x v : Geom} {F : PhysicalRow}
    (hS : seedDegree F ≤ 24000)
    (h : ∀ n : Fin 24001, origin (normalize x v (flatCoeff n F)) = 0) :
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
  by_cases hn : e none < 24001
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
    (hcap : ∀ F ∈ V, Caps27 b.box F) (n : Fin 24001) : V →ₗ[Geom] Capped b.box.b :=
  ((normalize x v).toLinearMap ∘ₗ flatCoeff n ∘ₗ V.subtype).codRestrict _
    (fun F => normalize_mem_capped (coeff_mem_capped (hcap F F.2).1 n) x v)
private def nodeMap (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps27 b.box F) : V →ₗ[Geom] (Fin 24001 → cappedRange b.box.b) :=
  LinearMap.pi fun n =>
    (origin.domRestrict (Capped b.box.b)).rangeRestrict ∘ₗ nodeInput b x v V hcap n
theorem codim_le_cappedRange27 (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    [Module.Finite Geom V] (hcap : ∀ F ∈ V, Caps27 b.box F) :
    codimIn V (contactAt x v) ≤ 24001 * Module.finrank Geom (cappedRange b.box.b) := by
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
    (V := ↥V) (V₂ := Fin 24001 → cappedRange b.box.b) A
  unfold codimIn
  omega
end
end Fat6966Bank24000Seed
end
section
namespace Fat6966Bank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_2
open Fat6966Bank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_2 (bank_bound plane_rank_le)
theorem contact_bound27 : ∀ (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow),
    Module.Finite Geom V → (∀ F ∈ V, Caps27 b.box F) →
    codimIn V (contactAt x v) ≤ 24001 * b.nodeRank := by
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
end Fat6966Bank24000Seed
end
section
namespace Fat6966Bank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3
open Fat6966Bank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3 (clearedTest clearedTest_apply codim_le_test_finrank)
open K1_13_4_2 (codim_inf_le codim_finset_inf_le codim_antitone dimension_of_debits)
def poleDebit27 (a : Shape) : ℕ :=
  ∑ q ∈ Finset.range (a.b + 1),
    (a.b + a.j - q) * gradeCount a q * (24001 + (a.b - q))
abbrev SeedCoeff27 (a : Shape) (q : ℕ) := Fin (24001 + (a.b - q))
def c2_27 : Prop :=
  ∀ (a : Shape) (α : Geom) (N D : (Polynomial Geom)), D ≠ 0 →
    N.natDegree ≤ 1 → D.natDegree ≤ 1 →
    let z₀ : GenericSeed := algebraMap (Polynomial Geom) GenericSeed N / algebraMap (Polynomial Geom) GenericSeed D
    ∃ p : ∀ q : Fin (a.b + 1), PhysicalRow →ₗ[Geom] (JetCoeff a q.val → (Polynomial Geom)),
      ∀ F : PhysicalRow, Caps27 a F →
        (∀ e ∈ (centered z₀ F).support, admissible a e) ∧
        ∀ (q : Fin (a.b + 1)) (c : JetCoeff a q.val),
          (p q F c).natDegree ≤ 24000 + (a.b - q.val) ∧
          algebraMap (Polynomial Geom) GenericSeed (p q F c) =
            (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q.val) *
              localCoeff a α q.val c (centered z₀ F)
end
end Fat6966Bank24000Seed
end
section
namespace Fat6966Bank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3 K1_13_4_2_3_2
open Fat6966Bank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3_2 (cleared cleared_apply clearedFactor support_bounds grade_sub centered_admissible map_cleared seedMap grade)
private theorem cleared_degree27 {a : Shape} {α : Geom} {N D : (Polynomial Geom)}
    (hN : N.natDegree ≤ 1) (hD : D.natDegree ≤ 1) {F : PhysicalRow} (hF : Caps27 a F)
    (q : Fin (a.b + 1)) (c : JetCoeff a q.val) :
    (cleared a α N D q F c).natDegree ≤ 24000 + (a.b - q.val) := by
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
    have hU : m none ≤ 24000 :=
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
end Fat6966Bank24000Seed
end
section
namespace Fat6966Bank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3 K1_13_4_2_1 Finset
open Fat6966Bank24000 (Caps27)
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
    (hp : ∀ c, (p F c).natDegree ≤ 24000 + (a.b - q) ∧
      algebraMap (Polynomial Geom) GenericSeed (p F c) =
        (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q) * localCoeff a α q c G) :
    (∀ k : SeedCoeff27 a q, (clearedTest w p F).coeff k.val = 0) ↔ dot a α q w G = 0 := by
  have hdeg : (clearedTest w p F).natDegree ≤ 24000 + (a.b - q) := by
    rw [clearedTest_apply]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ =>
      (Polynomial.natDegree_smul_le _ _).trans (hp c).1
  have hz : (∀ k : SeedCoeff27 a q, (clearedTest w p F).coeff k.val = 0) ↔
      clearedTest w p F = 0 := by
    refine ⟨fun h => Polynomial.ext fun n => ?_, by intro h k; rw [h, Polynomial.coeff_zero]⟩
    rw [Polynomial.coeff_zero]
    by_cases hn : n < 24001 + (a.b - q)
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
      (fun q => (a.b + a.j - q) * gradeCount a q * (24001 + (a.b - q))) (a.b + 1)
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
theorem pole_eq27 (b : Bank) : poleDebit27 b.box = 24001 * credit b.box.b + extra b.box.b := by
  have hb : b.box = ⟨b.box.b, 2300, 1150⟩ := by cases b <;> rfl
  have hgrade (q : ℕ) : gradeCount b.box q = gradeCount ⟨b.box.b, 2300, 1150⟩ q :=
    congrArg (fun a => gradeCount a q) hb
  calc
    _ = jetSum b.box.b (fun q _ _ => (2300 + (b.box.b - q)) * (24001 + (b.box.b - q))) := by
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
end Fat6966Bank24000Seed
end

end Merged_R6960Fat6966Bank24000Seed

-- merged module R6960Fat6966Bank24000Banks
section Merged_R6960Fat6966Bank24000Banks

set_option Elab.async false
section
namespace Fat6966Bank24000Banks
open K1_13_4_2 (Bank)
def cut : Bank → ℕ
  | .first => Fat6966Bank24000.firstCut
  | .second => Fat6966Bank24000.secondCut
def targetRank : Bank → ℕ
  | .first => 1
  | .second => Fat6966Bank24000.bankRank
theorem cut_large (b : Bank) : 131071 * b.box.b ≤ cut b + 1 := by
  cases b <;> decide
def rawBase (b : Bank) : ℕ := cut b + 1 - 131071 * b.box.b
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h
end Fat6966Bank24000Banks
end
section
namespace Fat6966Bank24000Banks
open K1_13 (Geom)
open K1_13_4 K1_13_4_2
open K1_13_4_2_1 (jetSum)
open Function
open scoped BigOperators Polynomial
noncomputable section
open P0_9_4_1 (Column colExp colX column column_li coordinate coordinate_column column_bounds space space_bounds)
open P0_9_4_1 (exponent_none)
open Fat6966Bank24000 (Caps27)
private abbrev NewColumn (b : Bank) (h : ℕ) :=
  Σ q : Fin (b.box.b + 1), Σ k : Fin (min q.val 1150 + 1),
    Σ l : Fin (min (q.val - k.val) (2300 - 2 * k.val) + 1),
      Fin (width b h q.val k.val l.val) × Fin 24001
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
          (Fin.castLEEmb (by decide : 24001 ≤ 70001))
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
    seedDegree F ≤ 24000 := by
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
      Module.finrank Geom V = 24001 * jetSum b.box.b (width b h) := by
  refine ⟨newSpace b h, Module.Finite.span_of_finite _ (Set.finite_range _), fits b h, ?_⟩
  rw [newSpace, finrank_span_eq_card ((column_li b h).comp _ (base b h).injective)]
  simp only [NewColumn, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_comm _ 24001]
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
end Fat6966Bank24000Banks
end
section
namespace Fat6966Bank24000Banks
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
private theorem first_raw : rawVolume .first = 2816814436486775580 := by
  change moment 6789 4867010 1 131071 0 = _
  exact moment_eq 6789 4867010 1 131071 0 _ (by decide) (by decide +kernel)
private theorem second_raw : rawVolume .second = 2834000441598701348 := by
  change moment 6820 3076178 1 131071 0 = _
  exact moment_eq 6820 3076178 1 131071 0 _ (by decide) (by decide +kernel)
private theorem endpoint (b : Bank) :
    targetRank b + 262144 * (24001 * b.nodeRank) + 2316 * extra b.box.b ≤
      24001 * rawVolume b := by
  obtain ⟨_, _, hfirst, hsecond⟩ := bank_moments
  cases b
  · have he : extra Bank.first.box.b = 0x1cc973f372d9cdc := hfirst
    have ha : (1 : ℕ) + 262144 * (24001 * 0x9bab8f5dfb7) + 2316 * 0x1cc973f372d9cdc ≤
        24001 * 2816814436486775580 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.first + 262144 * (24001 * Bank.first.nodeRank) + 2316 * x ≤ 24001 * y)
      he first_raw).mpr ha
  · have he : extra Bank.second.box.b = 0x1d32fca954a0ef7 := hsecond
    have ha : (1 : ℕ) + 262144 * (24001 * 0x9bac59312df) +
        2316 * 0x1d32fca954a0ef7 ≤ 24001 * 2834000441598701348 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.second + 262144 * (24001 * Bank.second.nodeRank) + 2316 * x ≤ 24001 * y)
      he second_raw).mpr ha
theorem budget (b : Bank) (h : ℕ) (hh : h ≤ 2316) :
    targetRank b + 262144 * (24001 * b.nodeRank) + h * Fat6966Bank24000Seed.poleDebit27 b.box ≤
      24001 * jetSum b.box.b (width b h) := by
  have he := endpoint b
  have hm := Nat.mul_le_mul_right (extra b.box.b) hh
  rw [Fat6966Bank24000Seed.pole_eq27, volume_eq, Nat.mul_add, Nat.mul_add]
  have hc : h * (24001 * credit b.box.b) = 24001 * (credit b.box.b * h) := by ring
  omega
end Fat6966Bank24000Banks
end
section
namespace Fat6966Bank24000Banks
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2
open Fat6966Bank24000 (Caps27)
open scoped Polynomial BigOperators
open K1_13_4_2 (codim_inf_le codim_finset_inf_le separable_rank dimension_of_debits)
private theorem simple_pole_bound : Fat6966Bank24000Seed.c3_27 :=
  Fat6966Bank24000Seed.simple_pole27 Fat6966Bank24000Seed.proof27
private theorem deformation_bound : K1_13_4_2.c4 :=
  K1_13_4_2_4.of_children K1_13_4_2_4_1.proof K1_13_4_2_4_2.proof
private theorem rank_of_bounds (b : Bank) (w : I → K) {Γ s}
    (P : PoleData Γ s) (L : ResidueChart P) (hh : P.H.natDegree ≤ 2316) :
    Fat6966Bank24000.HasRank27 w P L b.box (cut b) (targetRank b) := by
  classical
  obtain ⟨V, hV, hbox, hdimV⟩ := ambient b P.H.natDegree
  have hsize := (budget b P.H.natDegree hh).trans_eq hdimV.symm
  let : Module.Finite Geom V := hV
  have hcap : ∀ F ∈ V, Caps27 b.box F := fun F hF => (hbox F hF).1
  let A : I → Submodule Geom PhysicalRow := fun i => contactAt (embed (node i)) (embed (w i))
  let U : Submodule Geom PhysicalRow := ⨅ i, A i
  let W : Submodule Geom PhysicalRow := poleCondition P L b.box (liftX P.H)
  have hU : codimIn V U ≤ 262144 * (24001 * b.nodeRank) := by
    have hA (i : I) (_ : i ∈ Finset.univ) : codimIn V (A i) ≤ 24001 * b.nodeRank :=
      Fat6966Bank24000Seed.contact_bound27 b (embed (node i)) (embed (w i)) V hV hcap
    have h := codim_finset_inf_le V (Finset.univ : Finset I) A (24001 * b.nodeRank) hA
    have hc : (Finset.univ : Finset I).card = 262144 := Fintype.card_fin (2 ^ 18)
    rw [hc, Finset.inf_univ_eq_iInf] at h
    exact h
  have hW : codimIn V W ≤ P.H.natDegree * Fat6966Bank24000Seed.poleDebit27 b.box := by
    apply deformation_bound Γ s P L b.box V _ hV
    intro P' L' _ hdeg hsep
    rw [← hdeg]
    exact Fat6966Bank24000Seed.separable_rank27 simple_pole_bound P' L' b.box V hcap hsep
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
theorem proof : Fat6966Bank24000.c1 := by
  intro w Γ s P L hh
  refine ⟨?_, rank_of_bounds .second w P L hh⟩
  obtain ⟨e, he, hsource⟩ := rank_of_bounds .first w P L hh
  let i : Fin (targetRank Bank.first) := ⟨0, by decide⟩
  exact ⟨e i, he.ne_zero i, hsource i⟩
end
end Fat6966Bank24000Banks
end

#print axioms Fat6966Bank24000Banks.proof

end Merged_R6960Fat6966Bank24000Banks

end Merged6967_Fat6966Bank24000

section Merged6967_Fat6966Defs
set_option Elab.async false



set_option Elab.async false

-- merged module R6960Low6966FatDefs
section Merged_R6960Low6966FatDefs

set_option Elab.async false
section
namespace Low6966Fat
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
abbrev firstOrder : ℕ := 4086972
abbrev secondOrder : ℕ := 1814603
abbrev firstCut : ℕ := 5000 * 179759 - firstOrder
abbrev secondCut : ℕ := 5000 * 179759 - secondOrder
abbrev bankRank : ℕ := 643975827135108623227
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  6948 * a none + 48690 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
/-- The low fat chain works with rows whose seed degree is at most 24,0 in the first bank and 32,0 in the second. -/
abbrev seedCap (a : K1_13.Shape) : ℕ := if a.b = 6789 then 24000 else 32000
def Caps27 {R : Type*} [CommSemiring R] (a : K1_13.Shape) (F : SeedRow R) : Prop :=
  Caps a F ∧ seedDegree F ≤ seedCap a
def Source27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Source w P L a t F ∧ seedDegree F ≤ seedCap a
def HasRank27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧ ∀ i, Source27 w P L a t (e i)
abbrev commonBox : K1_13.Shape := ⟨1517, 492, 0⟩
abbrev resultantBox : K1_13.Shape := ⟨380928000, 128800000, 0⟩
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
  pure_degree : pure.natDegree ≤ 56000
  fixed_kind : ∀ f ∈ fixed, Irreducible f ∧ 0 < jetTotal f ∧ seedDegree f = 0
  moving_kind : ∀ f ∈ moving, Irreducible f ∧ 0 < jetTotal f ∧
    0 < seedDegree f ∧ f.degreeOf (some 2) = 0
  fixed_total : jetTotal (∏ f ∈ fixed, f) ≤ 123
  fixed_index : jetIndex (∏ f ∈ fixed, f) ≤ 41
  moving_total : jetTotal (∏ f ∈ moving, f) ≤ 17
  moving_index : jetIndex (∏ f ∈ moving, f) ≤ 5
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 41
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
end Low6966Fat
end
section
namespace Low6966Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
structure Messages (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) : Prop where
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 179759 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2316 →
    (∃ F, F ≠ 0 ∧ Source27 w P L firstBox firstCut F) ∧
    HasRank27 w P L secondBox secondCut bankRank
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow),
    F ≠ 0 → Caps27 firstBox F → HasRank27 w P L secondBox secondCut bankRank →
    ∃ G, G ∈ Necessary w P L ∧ Nonempty (CommonPair (toGeneric F) (toGeneric G))
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∀ (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2316 →
      (∀ F, Source27 w P L firstBox firstCut F → ∀ γ ∈ Γ,
        MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstOrder) ∧
      (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
        MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondOrder)

abbrev fatOrder : ℕ := 21923
def Holds (E : FatEquations) (S : (Polynomial K1_13.Geom)) : Prop :=
  K1_13.atJet E.common S = 0 ∨ K1_13.OrderAt E.residual S fatOrder

def Equations : Prop :=
  ∀ (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)),
    (∀ γ ∈ Γ, (s γ).natDegree ≤ 133387) →
    (∀ γ ∈ Γ, ∃ T : Finset I, 179759 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i) →
    ∀ P : K1_13.PoleData Γ s, P.H.natDegree ≤ 2316 →
    ∃ (book : Finset K1.K) (E : FatEquations), book.card ≤ 56000 ∧
      ∀ γ ∈ Γ, γ ∉ book → Holds E (K1_13.extend (s γ))
end
end Low6966Fat
end

end Merged_R6960Low6966FatDefs


end Merged6967_Fat6966Defs

section Merged6967_FrontCore82258Model
set_option Elab.async false




set_option Elab.async false

-- merged module GoldBranch6N5
section Merged_GoldBranch6N5
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_5
noncomputable section
open P3 (K I)
open P3_6 (TrueWeightLE  taylorLength)
open K1_13 (Row indexDegree)
open K1_13_5 (NodeFamily lowBox liftedBox graphBox mixed3)
open scoped BigOperators Polynomial
def Whole (f : Row 3) : Prop :=
  f ∣ K1_13_5.compatibilityNumerator f (taylorLength - 3)
def mixedBudget : ℕ :=
  let a := liftedBox (taylorLength + 1)
  let b := liftedBox (taylorLength + 2)
  mixed3 lowBox a b + (taylorLength - 1) * mixed3 lowBox graphBox b +
    taylorLength * mixed3 lowBox graphBox a
def invariantBudget : ℕ :=
  lowBox.b * (1 + (2 * (taylorLength + 1) - 7) * (lowBox.b - 1))
structure ProperCover (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget
  fresh : invariant.totalCap ≤ invariantBudget
  components : multiple.n + invariant.n ≤ 2 * invariantBudget
end
end P3_6_5
end
section
namespace P3_6_5_1
noncomputable section
open K1_13 (Geom Row Shape atJet)
open K1_13_5 (RegularAt compatibilityNumerator graphBox liftedBox separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericRow graph graphPoint
  InLiftedBox RepresentsOnGraph jetPoint regularLocus extendedAtJet)
open P3_6 (taylorLength physicalDegree)
open P3_6_5 (Whole mixedBudget)
open Polynomial
open scoped BigOperators
abbrev Coefficients := Fin taylorLength → GeometricX
abbrev CoefficientIdeal := Ideal (GeoRow taylorLength)
abbrev CurveIndex (n : ℕ) := Fin n × Ideal (GeoRow 3)
def coefficientPoint (S : (Polynomial Geom)) : Coefficients :=
  fun j => algebraMap Geom GeometricX (S.coeff j)
def oldCut (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 3)
def oldNext (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 2)
open K1_13_5_4_1 (compatibility_degree)
def oldCutIdeal (f : Row 3) : Ideal (GeoRow 3) :=
  Ideal.span {genericRow f, genericRow (oldCut f)}
def properComponents {n : ℕ} (f : Fin n → Row 3) : Finset (CurveIndex n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Whole (f i) then ∅ else
      ((oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i)))).image
        (fun P => (i, P))
def componentLength (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ∞ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let A := Localization.AtPrime P
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A))
  else 0
def nextCutLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ regularLocus f P ∧ MvPolynomial.eval y (genericRow (oldNext f)) = 0}
def reconstruct (f : Row 3) (numerator : Fin taylorLength → GeoRow 4)
    (y : Fin 3 → GeometricX) : Coefficients :=
  fun i => MvPolynomial.eval (graphPoint f y) (numerator i) /
    MvPolynomial.eval y (genericRow (separant f)) ^ (taylorLength - 4)
structure LiftedChart (f : Row 3) where
  cut : GeoRow 4
  next : GeoRow 4
  numerator : Fin taylorLength → GeoRow 4
  graph_box : InLiftedBox (graph f) graphBox 1
  cut_box : InLiftedBox cut (liftedBox (taylorLength + 1)) (taylorLength - 1)
  next_box : InLiftedBox next (liftedBox (taylorLength + 2)) taylorLength
  coefficient_box : ∀ i, InLiftedBox (numerator i) (liftedBox taylorLength) (taylorLength - 2)
  cut_represents : RepresentsOnGraph f (oldCut f) cut
  next_represents : RepresentsOnGraph f (oldNext f) next
  actual : ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S
structure MixedSections {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart (f i)) where
  length : CurveIndex n → ℕ
  degree : CurveIndex n → ℕ
  length_eq : ∀ a ∈ properComponents f, (length a : ℕ∞) = componentLength (f a.1) a.2
  length_pos : ∀ a ∈ properComponents f, 0 < length a
  total : (∑ a ∈ properComponents f, length a * degree a) ≤ mixedBudget
  points : ∀ a ∈ properComponents f, genericRow (oldNext (f a.1)) ∉ a.2 →
    (nextCutLocus (f a.1) a.2).Finite ∧ (nextCutLocus (f a.1) a.2).ncard ≤ degree a
  curves : ∀ a ∈ properComponents f, 2 ≤ length a →
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      0 < degree a ∧ MvPolynomial.affineDegree Q ≤ (degree a : ℚ) ∧
      ∀ y ∈ regularLocus (f a.1) a.2,
        reconstruct (f a.1) (T a.1).numerator y ∈ MvPolynomial.zeroLocus GeometricX Q
end
end P3_6_5_1
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace P3_6_5
noncomputable section
open P3 (I K node)
open K1_13_5 (NodeCapacity NodeFamily)
open Polynomial ProximityPrize.Benchmark
open scoped BigOperators
end
end P3_6_5
end
section
namespace P3_6_5_1
noncomputable section
open P3_6 (physicalDegree taylorLength)
open K1_13 (Geom Row atJet indexDegree)
open K1_13_5 (RegularAt separant graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow InLiftedBox RepresentsOnGraph graph genericCoeff genericRow jetPoint)
open K1_13_5_4_1 (liftRaw liftSep graphRaw thirdVelocityNumerator thirdNumerator
  padJet jetNumerator centre partialFlow_lift generic_graph eval_genericRow graphPoint_of_actual)
open K1_13_7_1 (weight_const_mul_le weight_X_le)
open MvPolynomial
open Polynomial (hasseDeriv)
open scoped BigOperators Polynomial
open K1_13_5_4_1_1 (mul_bound partialFlow_bound liftSep_eq liftedStep_bound generic_bound totalWeight indexWeight topWeight heightWeight lift_weight fits fits_lifted)
open K1_13_5_4_1_2 (represents)
open K1_13_5_4_1 (atJet_padJet taylor_coefficients_aux genericCoeff_ne_zero third_atJet_zero actual_zero_of_represents)
local notation "W" => weightedTotalDegree
end
end P3_6_5_1
end
section
namespace P3_6_5
noncomputable section
open P3 (K)
open P3_6 ( taylorLength )
open K1_13 (Row Geom embed extend atJet)
open K1_13_5 (FirstRow RegularAt NodeFamily mixed3 lowBox graphBox liftedBox)
open Polynomial
open scoped BigOperators
end
end P3_6_5
end
section
set_option autoImplicit false
namespace P3_6_5_1_1
noncomputable section
open K1_13 (Row)
open K1_13_5 (graphBox liftedBox separant)
open K1_13_5_4 (InLiftedBox GeoRow GeometricX genericRow)
open K1_13_5_4_2 (JetPoint ExponentSpace boxExponents graphLocus graphCurve capBody mixedVolume4)
open P3_6 (taylorLength)
open P3_6_5 (Whole)
open P3_6_5_1 (oldCutIdeal)
open MvPolynomial
def factorCurves (f : Row 3) : Finset (Ideal (GeoRow 3)) := by
  classical
  exact if Whole f then ∅ else
    (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))
abbrev lastBox := liftedBox (taylorLength + 2)
abbrev lastExponents := boxExponents lastBox taylorLength
abbrev lastMap := monomialMap GeometricX lastExponents
def sectionIdeal (f : Row 3) (P : Ideal (GeoRow 3)) :
    Ideal (MvPolynomial lastExponents GeometricX) :=
  (graphCurve f P).comap lastMap
def sectionDegree (f : Row 3) (P : Ideal (GeoRow 3)) : ℚ :=
  affineDegree (sectionIdeal f P)
structure GenericSection (f : Row 3) where
  polynomial : GeoRow 4
  support : InLiftedBox polynomial lastBox taylorLength
  points : Ideal (GeoRow 3) → Finset JetPoint
  card_eq : ∀ P ∈ factorCurves f, ((points P).card : ℚ) = sectionDegree f P
  proper : ∀ P ∈ factorCurves f, polynomial ∉ graphCurve f P
  roots : ∀ P ∈ factorCurves f, ∀ y ∈ points P,
    y ∈ graphLocus f P ∧ eval y polynomial = 0
  off_other_curves : ∀ P ∈ factorCurves f, ∀ P' ∈ factorCurves f, P ≠ P' →
    ∀ y ∈ points P, y ∉ graphLocus f P'
end
end P3_6_5_1_1
end
section
set_option autoImplicit false
namespace P3_6_5_1_1
noncomputable section
open K1_13 (Row Geom Shape)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericCoeff_injective genericRow
  liftRow regularLocus graphPoint)
open K1_13_5_4_2 (boxExponents graphCurve eval_represents_iff)
open P3_6 (taylorLength)
open P3_6_5 (Whole)
open P3_6_5_1 (oldCut oldCutIdeal properComponents CurveIndex componentLength nextCutLocus
  oldNext LiftedChart)
open MvPolynomial RingTheory.Sequence
open scoped BigOperators Polynomial
open K1_13_5_4_2_1 (quotient_regular_iff graph_dimension)
open K1_13_5_4_2 (graphPoint_injective)
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end P3_6_5_1_1
end
section
set_option autoImplicit false
namespace P3_6_5_1_1_2
noncomputable section
open K1_13 (Row)
open K1_13_5 (lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow graph graphIdeal)
open P3_6_5_1 (LiftedChart oldCutIdeal)
open K1_13_5_4_2_3 (OpenRing onOpen onOpen_kills onOpen_isUnit onOpen_hom_ext
  openLift openLift_onOpen sep liftedSep)
open MvPolynomial
open K1_13_5_4_2_3 (three_isUnit graph_coord_unique represents_vanish)
def threeCut (f : Row 3) (T : LiftedChart f) : Ideal (GeoRow 4) :=
  graphIdeal f ⊔ Ideal.span {T.cut}
abbrev OldOpen (f : Row 3) := OpenRing (oldCutIdeal f) (sep f)
abbrev GraphOpen (f : Row 3) (T : LiftedChart f) := OpenRing (threeCut f T) (liftedSep f)
abbrev oldMap (f : Row 3) := onOpen (oldCutIdeal f) (sep f)
abbrev graphMap (f : Row 3) (T : LiftedChart f) := onOpen (threeCut f T) (liftedSep f)
private def newJet (f : Row 3) : OldOpen f :=
  -oldMap f (genericRow (lowerTangent f)) *
    ↑(((three_isUnit ((oldMap f).comp C)).mul (onOpen_isUnit (oldCutIdeal f) (sep f))).unit⁻¹)
private theorem newJet_eq (f : Row 3) :
    oldMap f (genericRow (lowerTangent f)) + 3 * newJet f * oldMap f (sep f) = 0 := by
  let a := oldMap f (genericRow (lowerTangent f))
  let s := oldMap f (sep f)
  let u := ((three_isUnit ((oldMap f).comp C)).mul (onOpen_isUnit (oldCutIdeal f) (sep f))).unit
  have hu : (u : OldOpen f) = 3 * s := IsUnit.unit_spec _
  change a + 3 * (-a * (↑u⁻¹ : OldOpen f)) * s = 0
  calc
    _ = a + -a * ((↑u⁻¹ : OldOpen f) * (u : OldOpen f)) := by rw [hu]; ring
    _ = 0 := by simp
private def substitute (f : Row 3) : GeoRow 4 →+* OldOpen f :=
  eval₂Hom ((oldMap f).comp C) (Fin.snoc (fun i => oldMap f (MvPolynomial.X i)) (newJet f))
@[simp] private theorem substitute_lift (f : Row 3) (p : GeoRow 3) :
    substitute f (liftRow p) = oldMap f p := by
  rw [substitute, liftRow, eval₂Hom_rename, Fin.snoc_comp_castSucc]
  have h : eval₂Hom ((oldMap f).comp C) (fun i : Fin 3 => oldMap f (MvPolynomial.X i)) = oldMap f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  rw [h]
private theorem substitute_last (f : Row 3) :
    substitute f (MvPolynomial.X (Fin.last 3)) = newJet f := by
  rw [substitute, eval₂Hom_X']
  exact Fin.snoc_last _ _
private theorem substitute_graph (f : Row 3) : substitute f (graph f) = 0 := by
  rw [graph, map_add, map_mul, map_mul, map_ofNat, substitute_lift, substitute_lift,
    show (3 : Fin 4) = Fin.last 3 from rfl, substitute_last]
  exact newJet_eq f
private theorem substitute_kills (f : Row 3) (T : LiftedChart f) :
    threeCut f T ≤ RingHom.ker (substitute f) := by
  have hG : graphIdeal f ≤ RingHom.ker (substitute f) := by
    rw [graphIdeal, Ideal.span_insert, sup_le_iff, Ideal.span_singleton_le_iff_mem,
      Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, RingHom.mem_ker]
    refine ⟨?_, substitute_graph f⟩
    rw [substitute_lift]
    exact onOpen_kills (Ideal.subset_span (by simp))
  have hs : IsUnit (substitute f (liftedSep f)) := by
    rw [substitute_lift]
    exact onOpen_isUnit _ _
  refine sup_le hG ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr ?_))
  apply (represents_vanish T.cut_represents _ hG hs).mpr
  rw [substitute_lift]
  exact onOpen_kills (Ideal.subset_span (by simp))
private def graphToOld (f : Row 3) (T : LiftedChart f) : GraphOpen f T →+* OldOpen f :=
  openLift _ _ (substitute f) (substitute_kills f T)
    (by rw [substitute_lift]; exact onOpen_isUnit _ _)
private theorem graphToOld_on (f : Row 3) (T : LiftedChart f) (b : GeoRow 4) :
    graphToOld f T (graphMap f T b) = substitute f b := by
  rw [graphToOld, openLift_onOpen]
private theorem oldToGraph_kills (f : Row 3) (T : LiftedChart f) :
    oldCutIdeal f ≤ RingHom.ker ((graphMap f T).comp (rename Fin.castSucc).toRingHom) := by
  let b := (graphMap f T).comp (rename Fin.castSucc).toRingHom
  have hG : graphIdeal f ≤ RingHom.ker (graphMap f T) := fun u hu =>
    RingHom.mem_ker.mpr (onOpen_kills (show u ∈ threeCut f T from Ideal.mem_sup_left hu))
  change oldCutIdeal f ≤ RingHom.ker b
  rw [oldCutIdeal, Ideal.span_insert, sup_le_iff]
  rw [Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_le_iff_mem]
  refine ⟨hG (show liftRow (genericRow f) ∈ graphIdeal f from
    Ideal.subset_span (by simp)), RingHom.mem_ker.mpr ?_⟩
  exact (represents_vanish T.cut_represents _ hG (onOpen_isUnit _ _)).mp
    (onOpen_kills (show T.cut ∈ threeCut f T from
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
private def oldToGraph (f : Row 3) (T : LiftedChart f) : OldOpen f →+* GraphOpen f T :=
  openLift _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f))
@[simp] private theorem oldToGraph_on (f : Row 3) (T : LiftedChart f) (a : GeoRow 3) :
    oldToGraph f T (oldMap f a) = graphMap f T (liftRow a) :=
  openLift_onOpen _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f)) a
def graphEquiv (f : Row 3) (T : LiftedChart f) : OldOpen f ≃+* GraphOpen f T := by
  refine RingEquiv.ofRingHom (oldToGraph f T) (graphToOld f T) ?_ ?_
  · apply onOpen_hom_ext
    have hcomp : (graphToOld f T).comp (graphMap f T) = substitute f :=
      RingHom.ext (graphToOld_on f T)
    rw [RingHom.comp_assoc, RingHom.id_comp, hcomp]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [substitute, liftRow]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hG : graphMap f T (graph f) = 0 :=
          onOpen_kills (Ideal.mem_sup_left (Ideal.subset_span (by simp)))
        have he := DFunLike.congr_arg (oldToGraph f T) (newJet_eq f)
        rw [map_add, map_mul, map_mul, map_ofNat, map_zero, oldToGraph_on, oldToGraph_on] at he
        have h := graph_coord_unique f (graphMap f T) (onOpen_isUnit _ _) hG he
        rw [RingHom.comp_apply, substitute_last]
        exact h.symm
      · simp [substitute, liftRow]
  · apply onOpen_hom_ext
    apply RingHom.ext
    intro a
    simp [graphToOld_on]
@[simp] theorem graphEquiv_on (f : Row 3) (T : LiftedChart f) (a : GeoRow 3) :
    graphEquiv f T (oldMap f a) = graphMap f T (liftRow a) :=
  oldToGraph_on f T a
end
end P3_6_5_1_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace P3_6_5_1_2
noncomputable section
open K1_13 (Row)
open K1_13_5 (compatibilityNumerator separant tangentNumerator)
open K1_13_5_4 (GeoRow genericRow genericCoeff genericCoeff_injective)
open K1_13_5_4_3 (TangentStable)
open K1_13_5_4_3_1 (tangentNumerator_add tangentNumerator_mul)
open P3_6 (taylorLength)
open P3_6_5 (Whole)
open P3_6_5_1 (oldCut oldNext oldCutIdeal componentLength )
open Polynomial
open K1_13_5_4_3_1 (flat_rowToGeo rowToGeo_eq tangent_self)
open K1_13_5_4_3_3 (generic_cut_regular)
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end P3_6_5_1_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P3_6_5_2
noncomputable section
open K1_13 (Geom)
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open P3_6 (physicalDegree)
open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_5_5_2_1 (monic_chart_aux)
open K1_13_5_5_2_1 (commonFactor_monic trimmedValue_monic trimmedValue_dvd)
open P0_9_5_2 (eval_divisions)
end
end P3_6_5_2
end

end Merged_GoldBranch6N5

-- merged module UpperBranch7
section Merged_UpperBranch7
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_7
noncomputable section
open Polynomial MvPolynomial
open P1 (I K node p)
open K1_14 (FX L seedEmbedding)
open K1_14_6 (Biform ClosedField rootPoint)
abbrev box (a b : ℕ) := restrictBidegree (Fin 2) FX a b
structure CRTChart (w : ℕ) where
  denominator : Biform
  numerator : (Polynomial Biform)
  degree_numerator : numerator.natDegree < 2 * w
  bound_denominator : denominator ∈ box 0 (2 * w)
  bound_numerator : ∀ j, numerator.coeff j ∈ box 0 (2 * w)
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open P1 (K I node agreement blockLength)
open K1_14 (FX)
open K1_14_6 (Biform ClosedField rootPoint)
open K1_14_6 (card_le_sum_cover)
open K1_14_6_2 (closedPoint eval_extend)
end
end P1_7_7
end
section
namespace P1_7_7
open P1 (HighBand agreement blockLength)
open P1_7 (degreeAt   quotientOrder   ceilRatio )
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
open P1 (K)
open P1_7 (regularRoot)
open K1_14 (Equation FX SeedBound atMark)
open K1_14_6 (ClosedField)
open K1_14_6_2 (closedPoint)
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open MvPolynomial
open K1_14_6 (ClosedField)
open scoped BigOperators
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open Polynomial MvPolynomial
open P1 (AnchorModel AnchoredFamily HighBand I K agreement node p)
open P1_7 (AdjacentChart GradeIndex  Reduced regularRoot grades )
open K1_14 (Equation FX L SeedBound seedEmbedding)
open scoped BigOperators
end
end P1_7_7
end
section
namespace P1_7_7_1
noncomputable section
open Polynomial Module K1_14_1
open K1_14 (L)
open scoped Polynomial BigOperators
open K1_14_1_1 (quotientBasis mulMatrix mulMatrix_entry mulMatrix_specialize mulMatrix_det_ne_zero eval_map_constants)
end
end P1_7_7_1
end
section
namespace P1_7_7_1
noncomputable section
open P1 (AnchorModel AnchoredFamily K p)
open P1_7 (AdjacentChart)
open K1_14 (L FX liftPoly seedEmbedding)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open K1_14_6 (Biform rootPoint)
open P1_7_7 (CRTChart box)
open MvPolynomial (mem_restrictBidegree mem_restrictBidegree_mono mul_mem_restrictBidegree)
open Polynomial
open scoped Polynomial BigOperators
end
end P1_7_7_1
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open Polynomial
open scoped BigOperators
end
end P1_7_7_2
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open P1 (K p)
open K1_14 (Equation FX SeedBound seedEmbedding atX liftPoly)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant     cleared
  markEval eval_cleared derivativeAt)
open P1_7_7 (box)
open MvPolynomial
open scoped Polynomial
local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))
end
end P1_7_7_2
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open P1 (I K node p)
open P1_7 (regularRoot)
open P1_7_7 (CRTChart box  )
open K1_14 (L FX seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant   markEval eval_flatten )
open Polynomial MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
end
end P1_7_7_2
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial
open scoped BigOperators
end
end P1_7_7_3
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial Filter
variable {k σ : Type*} [Field k]
end
end P1_7_7_3
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial
open scoped BigOperators
end
end P1_7_7_3
end

end Merged_UpperBranch7

-- merged module GoldBranch7
section Merged_GoldBranch7
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7
open P3 (HighBand)
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
def terminal : HighBand → Bank
  | .h2274 => ⟨⟨6600,9172,1952,211000⟩,0x1e372113d00000,0xae27f29bc6cc⟩
  | .h2294 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,946⟩,0xc4fd80000,22832869⟩
def stages : HighBand → List Stage
  | .h2274 =>
    [⟨0, ⟨⟨76,105,23,862⟩,0x345100000,3635193⟩, ⟨⟨359,499,105,11883⟩,0x14006680000,0x64b8343e⟩⟩,
     ⟨1, ⟨⟨80,111,24,1024⟩,0x3c7300000,4477423⟩, ⟨⟨356,495,104,14432⟩,0x137d3580000,0x616d5567⟩⟩,
     ⟨2, ⟨⟨90,125,27,1032⟩,0x558480000,7136131⟩, ⟨⟨391,543,114,15483⟩,0x19c04900000,0x8cc85625⟩⟩,
     ⟨3, ⟨⟨99,137,30,1063⟩,0x722180000,10343855⟩, ⟨⟨429,596,126,16288⟩,0x222a41c0000,0xcd26d8f5⟩⟩,
     ⟨4, ⟨⟨106,147,32,1146⟩,0x8b45c0000,13594640⟩, ⟨⟨483,671,142,16629⟩,0x30bbe980000,0x14954ceae⟩⟩,
     ⟨5, ⟨⟨115,159,35,1187⟩,0xb24d00000,18685854⟩, ⟨⟨521,724,153,17608⟩,0x3d118e80000,0x1bd78704c⟩⟩,
     ⟨6, ⟨⟨114,158,34,1481⟩,0xab2c00000,17916156⟩, ⟨⟨585,813,172,18018⟩,0x56714d40000,0x2c405b86b⟩⟩,
     ⟨10, ⟨⟨142,197,43,1768⟩,0x14bde80000,43318982⟩, ⟨⟨666,926,195,23938⟩,0x7f04c380000,0x4a1c95ad2⟩⟩,
     ⟨16, ⟨⟨195,270,60,1985⟩,0x35dfb80000,0x921d91e⟩, ⟨⟨869,1208,255,30502⟩,0x11a29c000000,0xd6957b128⟩⟩,
     ⟨18, ⟨⟨236,327,73,1859⟩,0x5f7bb40000,0x139cbdb4⟩, ⟨⟨1028,1429,302,30599⟩,0x1d31d5640000,0x1a41f86f48⟩⟩,
     ⟨24, ⟨⟨234,324,73,2988⟩,0x5daf840000,0x130a6f27⟩, ⟨⟨1267,1761,373,36637⟩,0x36b2a6f80000,0x3c9863ad3c⟩⟩,
     ⟨32, ⟨⟨261,362,81,5153⟩,0x813b280000,0x1d6fb003⟩, ⟨⟨1466,2038,431,46668⟩,0x54997c200000,0x6c7e6759da⟩⟩,
     ⟨36, ⟨⟨250,347,75,47631⟩,0x6ece680000,0x18392b4c⟩, ⟨⟨1215,1689,356,84012⟩,0x3011c0200000,0x33175ef1d6⟩⟩,
     ⟨54, ⟨⟨444,615,137,5303⟩,0x274cf340000,0xf2191e37⟩, ⟨⟨2194,3050,645,71333⟩,0x11b429fac0000,0x21f78372cbf⟩⟩,
     ⟨81, ⟨⟨680,942,212,6492⟩,0x8dc48280000,0x538e63a35⟩, ⟨⟨3385,4705,995,96391⟩,0x40f5ebab00000,0xc029d47a706⟩⟩,
     ⟨135, ⟨⟨998,1383,310,11820⟩,0x1bdf3ba00000,0x181eba870b⟩, ⟨⟨5282,7341,1556,154211⟩,0xf7195a1840000,0x4741ba66013a⟩⟩]
  | .h2294 =>
    [⟨0, ⟨⟨73,101,22,878⟩,0x2e5640000,3108650⟩, ⟨⟨352,489,103,10763⟩,0x12dda700000,0x5cfd94a5⟩⟩,
     ⟨1, ⟨⟨78,108,24,1006⟩,0x392740000,4103823⟩, ⟨⟨345,480,101,13083⟩,0x11c61f80000,0x564a51c0⟩⟩,
     ⟨2, ⟨⟨86,119,26,1061⟩,0x4b3780000,5931589⟩, ⟨⟨385,535,112,13830⟩,0x188bf840000,0x84679137⟩⟩,
     ⟨3, ⟨⟨94,130,29,1105⟩,0x633bc0000,8531244⟩, ⟨⟨411,572,120,15084⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
     ⟨4, ⟨⟨102,141,31,1166⟩,0x7cec00000,11621252⟩, ⟨⟨438,609,128,16326⟩,0x2436d340000,0xde912dc3⟩⟩,
     ⟨5, ⟨⟨108,150,33,1260⟩,0x948040000,14840297⟩, ⟨⟨522,726,153,15779⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
     ⟨6, ⟨⟨108,149,33,1589⟩,0x948040000,14526868⟩, ⟨⟨570,792,167,16543⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
     ⟨10, ⟨⟨142,197,43,1679⟩,0x14bde80000,43318982⟩, ⟨⟨696,968,204,20721⟩,0x910a3980000,0x5884788a7⟩⟩,
     ⟨16, ⟨⟨163,226,50,3079⟩,0x1f8a780000,75401397⟩, ⟨⟨851,1183,249,27859⟩,0x108708880000,0xc4f2a7606⟩⟩,
     ⟨18, ⟨⟨221,306,68,1918⟩,0x4e346c0000,0xf032b8c⟩, ⟨⟨952,1324,279,29044⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
     ⟨24, ⟨⟨212,294,65,3972⟩,0x44e9c40000,0xcc1a54f⟩, ⟨⟨1115,1550,329,35921⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
     ⟨32, ⟨⟨261,362,82,4794⟩,0x826c0c0000,0x1db6eefa⟩, ⟨⟨1463,2034,430,42399⟩,0x54106e900000,0x6b9d823520⟩⟩,
     ⟨36, ⟨⟨246,341,75,46786⟩,0x6ae4280000,0x16e7d3b2⟩, ⟨⟨1220,1696,357,67968⟩,0x309db61c0000,0x33e3754396⟩⟩,
     ⟨42, ⟨⟨279,386,85,43857⟩,0x9b80980000,0x25892b87⟩, ⟨⟨1240,1725,359,125646⟩,0x32a0cb700000,0x370899d961⟩⟩,
     ⟨54, ⟨⟨534,740,167,4011⟩,0x44f1df00000,0x1ff6e1863⟩, ⟨⟨2252,3131,661,63840⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
     ⟨81, ⟨⟨637,883,197,7007⟩,0x73e2ad80000,0x401d0f0c6⟩, ⟨⟨3474,4830,1019,88004⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8364⟩,0xcf60ca00000,0x8af950b98⟩, ⟨⟨4170,5798,1223,106403⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10486⟩,0x201c60040000,0x1cf53a5560⟩, ⟨⟨5487,7630,1607,140227⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 =>
    [⟨0, ⟨⟨11,15,3,125⟩,55574528,2194⟩, ⟨⟨20,28,4,256⟩,0xdc00000,17031⟩⟩,
     ⟨2, ⟨⟨21,29,6,151⟩,0x13cc0000,24733⟩, ⟨⟨38,53,9,375⟩,0x5d840000,211909⟩⟩,
     ⟨5, ⟨⟨34,47,10,230⟩,0x4f100000,156979⟩, ⟨⟨64,89,15,587⟩,0x1a3600000,1564938⟩⟩,
     ⟨10, ⟨⟨54,75,16,378⟩,0x12f140000,957077⟩, ⟨⟨101,141,24,985⟩,0x64f3c0000,9562298⟩⟩]
end P3_7
end
section
namespace P3_7
open P3 (HighBand agreement p blockLength)
abbrev degreeAt := P1_7.degreeAt
abbrev quotientOrder := P1_7.quotientOrder
def gap (hi : ℕ) := agreement - degreeAt hi
def scale (hi : ℕ) := agreement * gap hi
def muNum (hi : ℕ) := agreement * (blockLength - degreeAt hi)
def lambdaNum (hi : ℕ) := blockLength * gap hi
abbrev ceilRatio := P1_7.ceilRatio
abbrev singularDegree := P1_7.singularDegree
abbrev singularFee := P1_7.singularFee
def persistentFee (lo hi e v : ℕ) : ℕ :=
  let t := lambdaNum hi * quotientOrder lo
  let a := muNum hi + 2 * t * (e - 1)
  let b := 2 * hi * muNum hi + 2 * t * v
  ceilRatio (e * b^2 + 2 * v * a * b) ((scale hi)^2) + e
def properFee (lo hi e v : ℕ) : ℕ :=
  let bc := quotientOrder lo + 1
  let ac := 1 + bc * (e - 1)
  let cc := bc * v + 2 * hi
  let bn := lambdaNum hi * quotientOrder lo
  let an := muNum hi + bn * (e - 1)
  let cn := bn * v + 2 * hi * muNum hi
  ceilRatio (e * cc * cn +
    v * (cn * ((2*e-2)*bc + ac) + cc * ((2*e-2)*bn + an)) +
    v^2 * ((ac - 2*bc) * bn + an * bc)) (scale hi)
def flatFee (hi v : ℕ) : ℕ := ceilRatio (P3.t * (p+1) * v) (gap hi)
def tangentFee (lo hi e v : ℕ) : ℕ := properFee lo hi e v + flatFee hi v + e
def wholePrice (lo hi e v : ℕ) : ℕ :=
  if v = 0 then e else singularFee e v +
    if e ≤ 2 then persistentFee lo hi e v else tangentFee lo hi e v
structure GradeOK (lo hi fullU cap e : ℕ) (g : Grade) : Prop where
  sub : g.slots ≤ fullU
  separant : singularDegree e g.seedCap < p
  flat : e * degreeAt hi + g.seedCap < p
  fee : wholePrice lo hi e g.seedCap ≤ cap
theorem grade_of_literals {lo hi fullU cap e v U D m price : ℕ}
    (hU : U ≤ fullU) (hD : singularDegree e v = D) (hDp : D < p)
    (hm : e * degreeAt hi + v = m) (hmp : m < p)
    (hprice : wholePrice lo hi e v = price) (hle : price ≤ cap) :
    GradeOK lo hi fullU cap e ⟨v,U⟩ :=
  ⟨hU, hD.le.trans_lt hDp, hm.le.trans_lt hmp, hprice.le.trans hle⟩
end P3_7
end
section
namespace P3_7
open P3 (K HighBand)
abbrev PrefixFees := P1_7.PrefixFees
def fees : HighBand → PrefixFees
  | .h2274 => ⟨0xc904390c91470f, 0x17d3980110, 0x2ff61282b53d4, 0x509cd82b45d562, 0x198fe0fe4a37, 0x77b6ff61e2a14⟩
  | .h2294 => ⟨0xb8a9a55071628c, 0x19d622fd92, 0x2e2cc452ad45f, 0x4de68be1bd94f6, 0x241721d0f19c, 0x94c0f66257b34⟩
  | .h7773 => ⟨0x25f3ecf8e7b30, 15469025, 0xe395400f361, 0x766d97f5fb4, 0x28950a2d5, 0x7d0bf001f82⟩
structure PrefixBooks (b : HighBand) where
  loss : Finset K
  point : Finset K
  lowSeed : Finset K
  lowJet : Finset K
  fixedODE : Finset K
  content : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  lowSeed_le : lowSeed.card ≤ (fees b).lowSeed
  lowJet_le : lowJet.card ≤ (fees b).lowJet
  fixedODE_le : fixedODE.card ≤ (fees b).fixedODE
  content_le : content.card ≤ (fees b).content
noncomputable def PrefixBooks.union {b} (B : PrefixBooks b) : Finset K := by
  classical exact B.loss ∪ B.point ∪ B.lowSeed ∪ B.lowJet ∪ B.fixedODE ∪ B.content
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial
open P3 (HighBand AnchorModel AnchoredFamily K p node twist agreement)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_3 (Surface Parent)
open scoped BigOperators
def asP1Model {u del} (M : AnchorModel u del) : P1.AnchorModel u del :=
  { M with height_bound := M.height_bound.trans (by decide : P3.heightCap ≤ P1.heightCap) }
def fullCutoff (s : Shape) := s.m * agreement - 1
def buffered (h r : ℕ) (s : Shape) := fullCutoff s - 2*h*r
abbrev debit := P1_7.debit
structure BufferedPair (h : ℕ) (rows : Banks) (s : Stage) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows s.free.shape (buffered h s.reserve s.free.shape)
  moving_mem : moving ∈ rows s.moving.shape (buffered h s.reserve s.moving.shape)
  no_moving : K1_14_3.NoMovingCommon free moving
abbrev Pairs (b : HighBand) (h : ℕ) (rows : Banks) :=
  ∀ s ∈ stages b, BufferedPair h rows s
def BankPass (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {h rows s} (pair : BufferedPair h rows s) (q : Surface) : Prop :=
  BankPass rows s.free.shape q ∧ BankPass rows s.moving.shape q ∧
    K1_14_3R.compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
structure PrefixInventory (b : HighBand) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) {rows : Banks} (pairs : Pairs b M.overhead.toNat rows) where
  books : PrefixBooks b
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  stage_pass : ∀ q ∈ parents, ∀ s (hs : s ∈ stages b), 0 < s.reserve →
    PairPass (pairs s hs) q
  terminal_pass : ∀ q ∈ parents, BankPass rows (terminal b).shape q
  covers : ∀ γ ∈ Γ, γ ∈ books.union ∨ ∃ q ∈ parents, MarkOn M F q γ
def curveUnit (hi g : ℕ) : ℚ :=
  let d := degreeAt hi
  (2*(g : ℚ)-1) * (1 + 2*((P3.blockLength : ℚ)/agreement)*d) +
    ((P3.blockLength - d : ℕ) : ℚ) / gap hi
def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*agreement+j - q*(131071-h)
    let c := fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))
end
end P3_7
end
section
namespace P3_7
open P3 (HighBand agreement p)
local notation "r!" x "," y "," z => grade_of_literals (D := x) (m := y) (price := z)
  (by decide) rfl (by decide) rfl (by decide) rfl (by decide)
private theorem guard {lo hi m B top edge : ℕ}
    (hl : 0 < lo) (hh : hi ≤ 33249) (ht : m*agreement = top) (hp : 0 < top)
    (hc : top < p) (hw : B*(131071-lo) = edge) (he : edge ≤ top) :
    0 < lo ∧ hi ≤ 33249 ∧ 0 < m*agreement ∧ m*agreement < p ∧ B*(131071-lo) ≤ m*agreement :=
  ⟨hl, hh, ht.symm ▸ hp, ht.symm ▸ hc, hw.le.trans (he.trans ht.ge)⟩
local notation "g!" t "," w => guard (top := t) (edge := w) (by decide) (by decide) rfl
  (by decide) (by decide) rfl (by decide)
end P3_7
end
section
namespace P3_7
noncomputable section
open P3 (K I node p agreement blockLength AnchorModel AnchoredFamily)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open Finset Polynomial ProximityPrize.Benchmark
end
end P3_7
end
section
namespace P3_7
noncomputable section
open Polynomial
open P3 (HighBand AnchorModel AnchoredFamily agreement p)
open K1_14 (Banks Jet Equation SeedBound)
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open K1_14_4 (seedDegree seedDegree_le_iff)
end
end P3_7
end

end Merged_GoldBranch7

-- merged module HighCore82258Data
section Merged_HighCore82258Data

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258

abbrev agreement : ℕ := 179886
abbrev heightCap : ℕ := 33443
abbrev Bank := P1_7.Bank
abbrev Stage := P1_7.Stage
abbrev Grade := P1_7.Grade
abbrev debit := P1_7.debit

inductive Band where
  | h2367 | h2395 | h7773
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2367 => 2414
  | .h2395 => 2536
  | .h7773 => 7773
def finish : Band → ℕ
  | .h2367 => 2535
  | .h2395 => 7772
  | .h7773 => 33443
def terminal : Band → Bank
  | .h2367 => ⟨⟨4500,6256,1323,315000⟩,0x98969fb680000,0x2586075c1890⟩
  | .h2395 => ⟨⟨7550,10506,2218,180000⟩,0x2cfea55aa80000,0x129e297a45c0c⟩
  | .h7773 => ⟨⟨124,173,32,900⟩,0xc4fd80000,0x15c66e5⟩
def grades : Band → List Grade
  | .h2367 => []
  | .h2395 => [⟨338,172349⟩, ⟨333,173304⟩, ⟨327,179574⟩, ⟨322,177387⟩, ⟨317,175478⟩, ⟨311,176977⟩, ⟨305,177384⟩, ⟨299,176903⟩, ⟨292,178309⟩, ⟨285,178543⟩, ⟨277,179864⟩, ⟨269,179838⟩, ⟨261,178760⟩, ⟨251,179370⟩, ⟨240,179648⟩, ⟨228,179554⟩, ⟨214,179916⟩, ⟨199,179883⟩, ⟨183,179596⟩, ⟨165,179633⟩, ⟨145,179890⟩, ⟨124,179925⟩, ⟨102,179808⟩, ⟨78,179897⟩, ⟨53,179864⟩, ⟨26,180000⟩]
  | .h7773 => [⟨26,821⟩, ⟨25,771⟩, ⟨23,796⟩, ⟨20,855⟩, ⟨16,879⟩, ⟨10,900⟩, ⟨3,899⟩]
def stages : Band → List Stage
  | .h2367 => [⟨0,⟨⟨76,105,23,876⟩,0x345100000,0x3777f9⟩,⟨⟨437,608,128,16460⟩,0x2407b5c0000,0xdd657d32⟩⟩,
    ⟨1,⟨⟨83,115,25,972⟩,0x439080000,0x4ed4ac⟩,⟨⟨436,606,128,19573⟩,0x23d8b880000,0xdb115372⟩⟩,
    ⟨2,⟨⟨92,127,28,1030⟩,0x5c3600000,0x75b415⟩,⟨⟨508,706,149,20147⟩,0x389233c0000,0x19280bd7d⟩⟩,
    ⟨3,⟨⟨99,137,30,1121⟩,0x722180000,0x9dd5af⟩,⟨⟨492,686,144,24446⟩,0x33533580000,0x1656b0db4⟩⟩,
    ⟨4,⟨⟨107,148,33,1188⟩,0x917680000,0xd8f2fa⟩,⟨⟨525,731,154,26591⟩,0x3e6d7fc0000,0x1cdc7da38⟩⟩,
    ⟨5,⟨⟨116,161,35,1260⟩,0xb5c380000,0x128bb48⟩,⟨⟨642,892,188,24982⟩,0x71d1af40000,0x3fe068fa5⟩⟩,
    ⟨7,⟨⟨126,175,39,1507⟩,0xec9f00000,0x1a458a5⟩,⟨⟨685,952,201,29660⟩,0x8a677880000,0x52f0bdb9b⟩⟩,
    ⟨10,⟨⟨142,197,43,1969⟩,0x14bde80000,0x294fec6⟩,⟨⟨865,1202,254,33015⟩,0x1166fe340000,0xd28832ce8⟩⟩,
    ⟨16,⟨⟨171,237,50,3693⟩,0x2316e80000,0x53b7f45⟩,⟨⟨1014,1412,298,46747⟩,0x1c0729180000,0x1901657cf3⟩⟩,
    ⟨10,⟨⟨178,247,55,1414⟩,0x2932d00000,0x66c8fdf⟩,⟨⟨792,1101,233,35460⟩,0xd623cb40000,0x947787094⟩⟩,
    ⟨20,⟨⟨250,347,78,2205⟩,0x721cb80000,0x18f6d6a4⟩,⟨⟨1302,1815,383,49376⟩,0x3b50b1000000,0x442ac5ba92⟩⟩,
    ⟨32,⟨⟨261,362,81,6745⟩,0x813b280000,0x1d6fb003⟩,⟨⟨1459,2035,429,91138⟩,0x536744d80000,0x6b96ecc888⟩⟩,
    ⟨31,⟨⟨345,478,108,2963⟩,0x12b1e340000,0x59a98629⟩,⟨⟨1604,2235,472,73350⟩,0x6edb04b80000,0x9cb2a062f8⟩⟩,
    ⟨44,⟨⟨376,522,118,5271⟩,0x183833c0000,0x7f6275d9⟩,⟨⟨2253,3142,664,91136⟩,0x1334cd7ac0000,0x263b0eab16b⟩⟩,
    ⟨73,⟨⟨599,831,188,7362⟩,0x617b2300000,0x32de21d13⟩,⟨⟨3486,4863,1027,139347⟩,0x4711f2a780000,0xdb0e8041cee⟩⟩,
    ⟨76,⟨⟨498,692,155,26786⟩,0x37c11c80000,0x185234383⟩,⟨⟨2760,3850,812,234277⟩,0x233f7cff80000,0x5601e71ab3f⟩⟩,
    ⟨103,⟨⟨809,1126,252,10214⟩,0xee4ed940000,0xa99a27482⟩,⟨⟨4774,6667,1405,189434⟩,0xb6532fbfc0000,0x304357eb723c⟩⟩]
  | .h2395 => [⟨0,⟨⟨73,101,22,686⟩,0x2e5640000,0x2f6f2a⟩,⟨⟨352,489,103,9578⟩,0x12dda700000,0x5cfd94a5⟩⟩,
    ⟨1,⟨⟨78,108,24,786⟩,0x392740000,0x3e9e8f⟩,⟨⟨345,480,101,11294⟩,0x11c61f80000,0x564a51c0⟩⟩,
    ⟨2,⟨⟨86,119,26,855⟩,0x4b3780000,0x5a8245⟩,⟨⟨385,535,112,12199⟩,0x188bf840000,0x84679137⟩⟩,
    ⟨3,⟨⟨94,130,29,913⟩,0x633bc0000,0x822d2c⟩,⟨⟨411,572,120,13413⟩,0x1dec1a80000,0xad1e0c80⟩⟩,
    ⟨4,⟨⟨102,141,31,983⟩,0x7cec00000,0xb15384⟩,⟨⟨438,609,128,14645⟩,0x2436d340000,0xde912dc3⟩⟩,
    ⟨5,⟨⟨108,150,33,1068⟩,0x948040000,0xe271e9⟩,⟨⟨522,726,153,14724⟩,0x3d548e40000,0x1c16ef1c7⟩⟩,
    ⟨6,⟨⟨108,149,33,1296⟩,0x948040000,0xdda994⟩,⟨⟨570,792,167,15613⟩,0x4fc3e700000,0x27c2e15db⟩⟩,
    ⟨10,⟨⟨142,197,43,1481⟩,0x14bde80000,0x294fec6⟩,⟨⟨696,968,204,19837⟩,0x910a3980000,0x5884788a7⟩⟩,
    ⟨16,⟨⟨163,226,50,2605⟩,0x1f8a780000,0x47e88b5⟩,⟨⟨851,1183,249,26947⟩,0x108708880000,0xc4f2a7606⟩⟩,
    ⟨18,⟨⟨221,306,68,1813⟩,0x4e346c0000,0xf032b8c⟩,⟨⟨952,1324,279,28359⟩,0x17270e900000,0x1350bb1fb5⟩⟩,
    ⟨24,⟨⟨212,294,65,3510⟩,0x44e9c40000,0xcc1a54f⟩,⟨⟨1115,1550,329,35496⟩,0x255cff880000,0x2473d5ffe4⟩⟩,
    ⟨32,⟨⟨261,362,82,4355⟩,0x826c0c0000,0x1db6eefa⟩,⟨⟨1463,2034,430,42333⟩,0x54106e900000,0x6b9d823520⟩⟩,
    ⟨36,⟨⟨246,341,75,22227⟩,0x6ae4280000,0x16e7d3b2⟩,⟨⟨1220,1696,357,66559⟩,0x309db61c0000,0x33e3754396⟩⟩,
    ⟨42,⟨⟨279,386,85,24816⟩,0x9b80980000,0x25892b87⟩,⟨⟨1240,1725,359,118401⟩,0x32a0cb700000,0x370899d961⟩⟩,
    ⟨54,⟨⟨534,740,167,3960⟩,0x44f1df00000,0x1ff6e1863⟩,⟨⟨2252,3131,661,64497⟩,0x131ef423c0000,0x25ab1ba8825⟩⟩,
    ⟨81,⟨⟨637,883,197,6921⟩,0x73e2ad80000,0x401d0f0c6⟩,⟨⟨3474,4830,1019,89437⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
    ⟨100,⟨⟨774,1072,239,8313⟩,0xcf60ca00000,0x8af950b98⟩,⟨⟨4170,5798,1223,108383⟩,0x7934721300000,0x1ba1a89b2ba1⟩⟩,
    ⟨135,⟨⟨1042,1443,329,10485⟩,0x201c60040000,0x1cf53a5560⟩,⟨⟨5487,7630,1607,143115⟩,0x113c22e7a00000,0x52bdbe618ec3⟩⟩]
  | .h7773 => [⟨0,⟨⟨11,15,3,134⟩,0x3500000,0x892⟩,⟨⟨20,28,4,277⟩,0xdc00000,0x4287⟩⟩,
    ⟨2,⟨⟨21,29,6,158⟩,0x13cc0000,0x609d⟩,⟨⟨38,53,9,400⟩,0x5d840000,0x33bc5⟩⟩,
    ⟨5,⟨⟨34,47,10,240⟩,0x4f100000,0x26533⟩,⟨⟨64,89,15,625⟩,0x1a3600000,0x17e10a⟩⟩,
    ⟨10,⟨⟨54,75,16,397⟩,0x12f140000,0xe9a95⟩,⟨⟨101,141,24,1052⟩,0x64f3c0000,0x91e8ba⟩⟩]
def fees : Band → P1_7.PrefixFees
  | .h2367 => ⟨0x17995391305d9d6,0x266971f131,0x38b9c7c36389b,0x1cf1,0xfb231c85bab,0x219848008770⟩
  | .h2395 => ⟨0x972cf6daf77844,0x111c043902,0x26c37cc20d2f5,0x36aeb2322a567a,0x14c52d2e35e9,0x13e3e8005030⟩
  | .h7773 => ⟨0x288871cb28934,0x1104ece,0xf529d0114e8,0x89c424f27e8,0x16e313bf1,0xcbe5000336⟩
def retainedCap : Band → ℕ
  | .h2367 => 0x233b95fa21d83e5
  | .h2395 => 0x271956e092a65d7
  | .h7773 => 0x13aee2ace4cdc
def highBound : Band → ℕ
  | .h2367 => 0x3b10ba614948794
  | .h2395 => 0x3420609139fc6a6
  | .h7773 => 0x3dc317b12a0d6

def subbank (b : Band) (g : Grade) : Bank :=
  let t := terminal b
  { t with shape := { t.shape with U := g.slots } }

abbrev GradeIndex (b : Band) := Fin (grades b).length

def Listed (b : Band) (t : Bank) : Prop :=
  t = terminal b ∨ (∃ s ∈ stages b, t = s.free ∨ t = s.moving) ∨
    ∃ i : GradeIndex b, t = subbank b ((grades b).get i)

abbrev Test (b : Band) := Option (GradeIndex b)

def tested (b : Band) : Test b → Bank
  | none => terminal b
  | some i => subbank b ((grades b).get i)

def threshold (b : Band) : Test b → ℕ
  | none => (grades b).length + 1
  | some i => i.val + 1

def seedThreshold (b : Band) : Test b → ℕ
  | none => 0
  | some i => ((grades b).get i).seedCap + 1

def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*agreement+j - q*(131071-h)
    let c := fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))

def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * agreement - 2 * h * r

def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)


def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => rawWidth h r s q j - mode * (2 * h * j))


theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE + (fees b).content + retainedCap b + 1 = highBound b ∧
       highBound b ≤ 267872462194200158 := by
  cases b <;> decide +kernel

end HighCore82258

end Merged_HighCore82258Data

-- merged module FrontCore82258Model
section Merged_FrontCore82258Model

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option backward.isDefEq.respectTransparency false

namespace FrontCore82258

noncomputable section

open Polynomial
open P1 (K I node twist p)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum seedEmbedding)
open K1_14_1 (PoleData MarkResidues nodeL)
open P1_7 (Reduced singularDegree singularFee)
open scoped BigOperators Polynomial

abbrev AnchorModel (u : P1.Words) (D : Finset I) := P1.ModelAt HighCore82258.heightCap u D
abbrev AnchoredFamily {u D} (M : AnchorModel u D) (Γ : Finset K) :=
  P1.FamilyAt HighCore82258.agreement M Γ

def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ

end
end FrontCore82258

end Merged_FrontCore82258Model

end Merged6967_FrontCore82258Model

section Merged6967_GoldBranch6N8
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_2
noncomputable section
open K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open MvPolynomial (mem_support_iff)
open P0_9_2 (weight_eq_sum pointContact)
def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133344) ≤ 3000 * 179983 - 1
def sourceExponents : Set SourceExponent := { e | SourceEligible e }
theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133344)
    ?_ (3000 * 179983 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133344) j).ne'
def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents
instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite
end
end P3_6_2
end
section
namespace P3_6_2
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourceExponent Local toRow)
open P3 (I K node)
open scoped BigOperators
open P0_9_2 (high_monomial_vanishes map_independent_family)
end
end P3_6_2
end
section
namespace P3_6_3
noncomputable section
open P3 (I K)
open P3_6 (TrueWeightLE primaryBox  )
open K1_13 (Row InBox shape Contact)
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ Contact w P
end
end P3_6_3
end
section
namespace P3_6_3_3
noncomputable section
open Polynomial
open P3 (I K node)
open P3_6 (TrueWeightLE physicalDegree )
open P3_6_3 (BankRow)
open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open P0_9_3 (jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor linearFactor_ne linearFactor_degree divide_specialization support_linear_mul)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2, hc⟩
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw⟩ := hP m h
          exact ⟨hb, hj, ht, by omega⟩
        · obtain ⟨hb, hj, ht, hw⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega⟩
      obtain ⟨hb, hj, ht, hw⟩ := bounds
      refine ⟨hb, hj, ht, ?_⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
end
end P3_6_3_3
end
section
namespace P3_6_8
open K1_13 (Shape)
open K1_13_8_2 (Threshold orderFor)
abbrev oneReserve : ℕ := 0x572a200a42ce14
abbrev twoReserve : ℕ := 0xf915c8e214a19b
abbrev twoOrder : ℕ := 72
def emptyThresholds : List Threshold :=
  [⟨107, 46, 56⟩, ⟨14, 41, 53⟩, ⟨61, 31, 52⟩, ⟨8, 13, 32⟩,
    ⟨9, 7, 9⟩, ⟨22, 4, 8⟩, ⟨3, 7, 4⟩, ⟨4, 10, 22⟩,
    ⟨10, 28, 48⟩]
def emptyOrder (a : Shape) : ℕ := orderFor a.b a.j emptyThresholds
end P3_6_8
end
section
namespace P3_6_8
open K1_13 (Shape Fits InBox FatEligible remaining)
open K1_13_8 (Valid zeroShape  zeroMass availableMass layerTerm layerCount)
open K1_13_8_2 (orderFor)
open P0_9_8 (oneStart twoStart oneOrder indexBudget symbol_count availableMass_anti_prefix
  orderFor_select orderFor_mono  )
open P3_6 (factorCap)
open scoped BigOperators
def shapeSum {ι : Type*} (a : ι → Shape) (s : Finset ι) : Shape :=
  ⟨∑ i ∈ s, (a i).b, ∑ i ∈ s, (a i).j, ∑ i ∈ s, (a i).t⟩
theorem shapeSum_empty {ι : Type*} (a : ι → Shape) :
    shapeSum a ∅ = zeroShape := by simp [shapeSum, zeroShape]
theorem shapeSum_insert {ι : Type*} [DecidableEq ι] (a : ι → Shape)
    {i : ι} {s : Finset ι} (hi : i ∉ s) :
    shapeSum a (insert i s) = (shapeSum a s).plus (a i) := by
  simp [shapeSum, Shape.plus, Finset.sum_insert hi, Nat.add_comm]
theorem shapeSum_union {ι : Type*} [DecidableEq ι] (a : ι → Shape)
    {s t : Finset ι} (h : Disjoint s t) :
    shapeSum a (s ∪ t) = (shapeSum a s).plus (shapeSum a t) := by
  simp [shapeSum, Shape.plus, Finset.sum_union h]
theorem shapeSum_mono {ι : Type*} (a : ι → Shape) {s t : Finset ι}
    (h : s ⊆ t) : InBox (shapeSum a s) (shapeSum a t) :=
  ⟨Finset.sum_le_sum_of_subset h, Finset.sum_le_sum_of_subset h, Finset.sum_le_sum_of_subset h⟩
theorem inBox_trans {a b c : Shape} (hab : InBox a b) (hbc : InBox b c) :
    InBox a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩
theorem inBox_shapeSum {ι : Type*} (a : ι → Shape) {i : ι} {s : Finset ι}
    (hi : i ∈ s) : InBox (a i) (shapeSum a s) :=
  ⟨Finset.single_le_sum (f := fun i => (a i).b) (fun _ _ => Nat.zero_le _) hi,
    Finset.single_le_sum (f := fun i => (a i).j) (fun _ _ => Nat.zero_le _) hi,
    Finset.single_le_sum (f := fun i => (a i).t) (fun _ _ => Nat.zero_le _) hi⟩
theorem shapeSum_valid_or_empty {ι : Type*} {a : ι → Shape}
    (ha : ∀ i, Valid (a i)) (s : Finset ι) :
    s = ∅ ∨ Valid (shapeSum a s) := by
  by_cases he : s.Nonempty
  · obtain ⟨i, hi⟩ := he
    refine Or.inr ⟨(ha i).1.trans (inBox_shapeSum a hi).2.2, ?_, ?_⟩
    · change 3 * (∑ i ∈ s, (a i).t) ≤ ∑ i ∈ s, (a i).j
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (ha i).2.1
    · change (∑ i ∈ s, (a i).j) ≤ 3 * ∑ i ∈ s, (a i).b
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (ha i).2.2
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp he)
theorem spend_le {ι : Type*} [DecidableEq ι] [Fintype ι] {l : ι → ℕ}
    (f : ι → ℕ) {z s : Finset ι} {q d L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L) (hdisj : Disjoint z s)
    (hq : q ≤ ∑ i ∈ z, f i) :
    d * q + (d - L) * (∑ i ∈ s, f i) ≤ ∑ i, (d - l i) * f i := by
  calc
    _ ≤ d * (∑ i ∈ z, f i) + (d - L) * (∑ i ∈ s, f i) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) _
    _ = (∑ i ∈ z, d * f i) + ∑ i ∈ s, (d - L) * f i := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (∑ i ∈ z, (d - l i) * f i) + ∑ i ∈ s, (d - l i) * f i := by
      apply Nat.add_le_add
      · exact Finset.sum_le_sum fun i hi => by rw [hz i hi, Nat.sub_zero]
      · exact Finset.sum_le_sum fun i hi =>
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (hs i hi) _)
    _ = ∑ i ∈ z ∪ s, (d - l i) * f i := (Finset.sum_union hdisj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
end P3_6_8
end
section
namespace P3_6_8_1
open K1_13_8 (fastRemaining zeroMass)
open scoped BigOperators
def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n
theorem sumBelow_eq (f : ℕ → ℕ) (n : ℕ) :
    sumBelow f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow, Finset.sum_range_succ, ih]
theorem sumBelow_add (f : ℕ → ℕ) (m n : ℕ) :
    sumBelow f (m + n) = sumBelow f m + sumBelow (fun k => f (m + k)) n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    change sumBelow f (m + n) + f (m + n) =
      sumBelow f m + (sumBelow (fun k => f (m + k)) n + f (m + n))
    rw [ih, Nat.add_assoc]
def term (b j k : ℕ) : ℕ :=
  fastRemaining ((k + 1) * b) ((k + 1) * j)
theorem mass_eq {b j m : ℕ} (hm : m ≤ 1650 / j)
    (hb : 4012 < (m + 1) * b ∨ m = 1650 / j) :
    zeroMass b j = sumBelow (term b j) m := by
  unfold zeroMass
  rw [sumBelow_eq]
  rcases hb with hb | h
  · apply K1_13_8.sum_range_truncate _ hm
    intro k hk
    have h := hb.trans_le (Nat.mul_le_mul_right b (Nat.succ_le_succ hk))
    simp [term, fastRemaining, Nat.not_le_of_gt h]
  · rw [h] <;> rfl
theorem extend {f : ℕ → ℕ} {m n N x y total : ℕ}
    (hleft : sumBelow f m = x)
    (hright : sumBelow (fun k => f (m + k)) n = y)
    (hlen : m + n = N) (hvalue : x + y = total) :
    sumBelow f N = total := by
  rw [← hlen, sumBelow_add, hleft, hright, hvalue]
local notation "row!" h "," len "," nxt "," v "," z =>
  extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl
end P3_6_8_1
end
section
namespace P3_6_8_2
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open P3_6 (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)
open P3_6_8 ( oneReserve twoReserve)
private def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
private abbrev divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
private theorem shape_eq {x y : Shape}
    (hb : x.b = y.b) (hj : x.j = y.j) (ht : x.t = y.t) : x = y := by
  cases x
  cases y
  simp_all
local notation "shape!" => shape_eq (by decide) (by decide) (by decide)
private theorem divisorBox_eq : divisorBox = ⟨22994,7683,0⟩ := shape!
private def divisorCut (h : Shape) : Shape :=
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
private def divisorFee (p h : Shape) (md mp : ℕ) : ℕ :=
  ceilDiv (P3.t * md) (32 * incidenceGap) + ceilDiv mp 32 +
    20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
private def singularFee (x : Shape) (ms : ℕ) : ℕ :=
  if 1 < x.t then ceilDiv (4 * x.t * ms) 32 + x.t * x.b ^ 2 + 1 else 0
private def curveFee (mc mq : ℕ) : ℕ :=
  let length := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  ceilDiv (P3.t * mc + incidenceGap * mq) (32 * incidenceGap * length)
private def isolatedFee : ℕ :=
  ceilDiv (3 * resultantBox.j ^ 2 * (2 * resultantBox.b - resultantBox.j))
    (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
private theorem fatPrice_expand (x : Shape) :
    fatPrice x =
      divisorFee x.chamber (fatChart x)
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) (fatChart x))
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) x.chamber) +
      singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) +
      curveFee (mixed32 x.chamber resultantBox resultantBox (fatChart x))
        (mixed32 x.chamber resultantBox resultantBox x.chamber) + isolatedFee := rfl
private def fromSlack (p : Shape) : Shape :=
  ⟨p.b + p.j + 3 * p.t, p.j + 3 * p.t, p.t⟩
private def degreeCoeff (p q r : Shape) : ℕ :=
  16 * (p.j * q.j * r.t + p.j * q.t * r.j + p.t * q.j * r.j) +
  48 * (p.j * q.t * r.t + p.t * q.j * r.t + p.t * q.t * r.j) + 144 * p.t * q.t * r.t
private def degreePart (p q r s : Shape) : ℕ :=
  p.b * degreeCoeff q r s + q.b * degreeCoeff p r s +
  r.b * degreeCoeff p q s + s.b * degreeCoeff p q r
private def indexPart (p q r s : Shape) : ℕ :=
  24 * (p.j * q.j * r.j * s.t + p.j * q.j * r.t * s.j +
    p.j * q.t * r.j * s.j + p.t * q.j * r.j * s.j) +
  104 * (p.j * q.j * r.t * s.t + (p.j * q.t + p.t * q.j) * (r.j * s.t + r.t * s.j) +
    p.t * q.t * r.j * s.j) +
  312 * ((p.j * q.t + p.t * q.j) * r.t * s.t + p.t * q.t * (r.j * s.t + r.t * s.j)) +
  936 * p.t * q.t * r.t * s.t
set_option maxHeartbeats 2000000 in
private theorem mixed_from_parts (p q r s : Shape) (d i : ℕ)
    (hd : degreePart p q r s = d) (hi : indexPart p q r s = i) :
    mixed32 (fromSlack p) (fromSlack q) (fromSlack r) (fromSlack s) = d + i := by
  have h :
      K1_13.difference (K1_13.difference (K1_13.difference
        (K1_13.difference K1_13.volume32 (fromSlack p)) (fromSlack q)) (fromSlack r))
        (fromSlack s) ⟨0,0,0⟩ = (↑(degreePart p q r s + indexPart p q r s) : ℤ) := by
    simp only [K1_13.difference, K1_13.volume32, Shape.plus, fromSlack,
      degreePart, degreeCoeff, indexPart, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, Nat.cast_ofNat]
    ring
  unfold mixed32
  rw [h, Int.toNat_natCast, hd, hi]
private abbrev divisorSlack : Shape := ⟨15311,7683,0⟩
private abbrev resultantSlack : Shape := ⟨0x2596a670,0x13315480,0⟩
private theorem isolated_value : isolatedFee = 0x4a9107dde10a := by decide
private theorem fee_of_parts {x h : Shape} {md mp mc mq divs singular curves cap : ℕ}
    (hx : x.chamber = x) (hh : fatChart x = h) (hc : divisorCut h = h)
    (hd : mixed32 x ⟨22994,7683,0⟩ h h = md)
    (hp : mixed32 x ⟨22994,7683,0⟩ h x = mp)
    (hcurve : mixed32 x resultantBox resultantBox h = mc)
    (hpoint : mixed32 x resultantBox resultantBox x = mq)
    (hdivs : divisorFee x h md mp = divs)
    (hsingular : singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) = singular)
    (hcurves : curveFee mc mq = curves) (hcap : divs + singular + curves + 0x4a9107dde10a ≤ cap) :
    fatPrice x ≤ cap := by
  rw [fatPrice_expand, hsingular, hx, hh, hc, divisorBox_eq, hd, hp,
    hcurve, hpoint, hdivs, hcurves, isolated_value]
  exact hcap
local notation "mix!" p "," q "," r "," s "," d "," i =>
  mixed_from_parts p q r s d i (by decide) (by decide)
local notation "row!" p "," w "," limit "," sf "," sg "," dv "," cv ","
    dd "," di "," pd "," pi "," cd "," ci "," qd "," qi =>
  fee_of_parts (x := fromSlack p) (h := fromSlack w) (cap := limit)
    (divs := dv) (singular := sf) (curves := cv) rfl shape! shape!
    (mix! p, divisorSlack, w, w, dd, di) (mix! p, divisorSlack, w, p, pd, pi)
    (mix! p, resultantSlack, resultantSlack, w, cd, ci)
    (mix! p, resultantSlack, resultantSlack, p, qd, qi)
    (by decide) sg (by decide) (by decide)
end P3_6_8_2
end
section
namespace P3_6_8_3
open K1_13_8 (zeroShape availableMass zeroMass fastRemaining)
open K1_13_8_2 (Threshold)
open scoped BigOperators
private def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n
private theorem sumBelow_add (f : ℕ → ℕ) (m n : ℕ) :
    sumBelow f (m + n) = sumBelow f m + sumBelow (fun k => f (m + k)) n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    change sumBelow f (m + n) + f (m + n) =
      sumBelow f m + (sumBelow (fun k => f (m + k)) n + f (m + n))
    rw [ih, Nat.add_assoc]
private theorem extend {f : ℕ → ℕ} {m n N x total : ℕ}
    (hleft : sumBelow f m = x)
    (hright : sumBelow (fun k => f (m + k)) n = total - x)
    (hlen : m + n = N) (hle : x ≤ total) :
    sumBelow f N = total := by
  rw [← hlen, sumBelow_add, hleft, hright, Nat.add_sub_of_le hle]
local notation "block!" h "," len "," k "," t =>
  extend h (n := len) (N := k) (total := t) rfl rfl (by decide)
end P3_6_8_3
end
section
namespace P3_6_8_4
open K1_13 (Shape chart mixed32 ceilDiv)
open K1_13_8 (zeroShape)
open P0_9_8 (indexBudget)
open P3_6_8 (emptyOrder)
open P3_6 (physicalPrice physicalDegree incidenceGap primaryBox surfaceNumerator32 taylorLength factorCap)
def peak (b j : ℕ) : Shape := ⟨b, j, min 10 (j / 3)⟩
private def mainFee (x : Shape) : ℕ :=
  ceilDiv (surfaceNumerator32 x.chamber primaryBox) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * primaryBox.b *
      (chart (taylorLength + 1) x.chamber).b) incidenceGap
private def auxFee (x : Shape) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let z := q.plus (p.scale 4)
  let curves := mixed32 p q z h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q z p + 2 * x.t * mixed32 p p p p
  2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
private theorem price_eq (x : Shape) (l : ℕ) :
    physicalPrice x l = ceilDiv (mainFee x) l + auxFee x := by
  simp only [physicalPrice, mainFee, auxFee, Nat.add_assoc]
private abbrev RowBound (b j : ℕ) : Prop :=
  physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j
private theorem row (b j l main aux : ℕ)
    (horder : emptyOrder (peak b j) = l) (hmain : mainFee (peak b j) = main)
    (haux : auxFee (peak b j) = aux)
    (hle : ceilDiv main l + aux ≤ indexBudget zeroShape factorCap j) :
    RowBound b j := by
  change physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j
  rwa [price_eq, horder, hmain, haux]
local notation "row!" b "," j "," l "," m "," a => row b j l m a rfl rfl rfl (by decide)
end P3_6_8_4
end
section
namespace P3_6_8_5
open K1_13 (Shape)
open K1_13_8 (availableMass availableMass_eq_sum availableMass_mono fastRemaining
  remaining_anti)
open P0_9_8 (availableMass_anti_prefix oneOrder oneStart symbol_count)
open scoped BigOperators
private def capacity (j L k : ℕ) : ℕ :=
  fastRemaining (k + 1) ((k + 1) * 3 + (k + 1 - L) * j)
private theorem capacity_anti (j L : ℕ) : Antitone (capacity j L) := by
  intro a b hab
  simp only [capacity, ← symbol_count]
  exact remaining_anti (by omega) <|
    Nat.add_le_add (Nat.mul_le_mul_right 3 (by omega))
      (Nat.mul_le_mul_right j (by omega))
private def layerMass (j L s n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, capacity j L (s + k)
private theorem add_block (width count rest : ℕ) {j L s n cap : ℕ}
    (hw : width ≤ n) (hcount : capacity j L s ≤ count)
    (hrest : layerMass j L (s + width) (n - width) ≤ rest)
    (htotal : width * count + rest ≤ cap) : layerMass j L s n ≤ cap := by
  have hsplit : layerMass j L s n =
      layerMass j L s width + layerMass j L (s + width) (n - width) := by
    conv_lhs => rw [layerMass, ← Nat.add_sub_of_le hw, Finset.sum_range_add]
    simp only [layerMass, Nat.add_assoc]
  have hblock : layerMass j L s width ≤ width * count := by
    calc
      _ ≤ ∑ _k ∈ Finset.range width, count :=
        Finset.sum_le_sum fun k _ =>
          ((capacity_anti j L) (Nat.le_add_right s k)).trans hcount
      _ = _ := by simp
  rw [hsplit]
  exact (Nat.add_le_add hblock hrest).trans htotal
private theorem bounded_block (width rest : ℕ) {j L s n cap : ℕ}
    (hw : width ≤ n) (hr : rest ≤ cap)
    (hcount : capacity j L s ≤ (cap - rest) / width)
    (hrest : layerMass j L (s + width) (n - width) ≤ rest) :
    layerMass j L s n ≤ cap := by
  refine add_block width _ rest hw hcount hrest ?_
  calc
    width * ((cap - rest) / width) + rest ≤ (cap - rest) + rest := by
      rw [Nat.mul_comm width]
      exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    _ = cap := Nat.sub_add_cancel hr
local notation "row!" w "," r => bounded_block w r (by decide) (by decide) (by decide) ?_
end P3_6_8_5
end
section
namespace P3_6_8_6
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open P0_9_8 (oneStart oneOrder indexBudget)
open P3_6 (physicalPrice physicalDegree incidenceGap primaryBox taylorLength surfaceNumerator32)
open P3_6_8 (oneReserve)
private def peak (j : ℕ) : Shape := ⟨119, j, min 9 (j / 3)⟩
private def budget (j : ℕ) : ℕ := indexBudget oneStart (P3_6.factorCap - oneReserve) j
private abbrev PeakBound (j : ℕ) : Prop :=
  physicalPrice (peak j) (oneOrder (peak j)) ≤ budget j
private def mainFee (x : Shape) : ℕ :=
  ceilDiv (surfaceNumerator32 x.chamber primaryBox) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * primaryBox.b *
      (chart (taylorLength + 1) x.chamber).b) incidenceGap
private def auxFee (x : Shape) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let z := q.plus (p.scale 4)
  let curves := mixed32 p q z h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q z p + 2 * x.t * mixed32 p p p p
  2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
private theorem price_eq (x : Shape) (l : ℕ) :
    physicalPrice x l = ceilDiv (mainFee x) l + auxFee x := by
  simp only [physicalPrice, mainFee, auxFee, Nat.add_assoc]
private theorem row (j l main aux fee allowance : ℕ)
    (horder : oneOrder (peak j) = l) (hmain : mainFee (peak j) = main)
    (haux : auxFee (peak j) = aux) (hfee : ceilDiv main l + aux = fee)
    (hbudget : budget j = allowance) (hle : fee ≤ allowance) : PeakBound j := by
  change physicalPrice (peak j) (oneOrder (peak j)) ≤ budget j
  rw [price_eq, horder, hmain, haux, hfee, hbudget]
  exact hle
local notation "paid[" j "," l "," main "," aux "," fee "," cap "]" =>
  row j l main aux fee cap rfl rfl rfl rfl rfl (by decide)
section
set_option maxRecDepth 4096
end
end P3_6_8_6
end
section
namespace P3_6_8_8
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
end P3_6_8_8
end
section
namespace P3_6_8_8
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8 (Valid )
open P0_9_8 (twoStart indexBudget)
open P3_6_8 (twoOrder twoReserve)
open P3_6 (physicalPrice factorCap)
private def budget (j : ℕ) : ℕ := indexBudget twoStart (factorCap - twoReserve) j
private def priceFromParts (f m₀ m₁ m₂ c₀ c₁ p₀ p₁ : ℕ) : ℕ :=
  ceilDiv (ceilDiv (m₀ + 133346 * m₁ + 133347 * m₂) 32 +
    ceilDiv ((82161 + 2 * 46639) * 118 * 4012 * 31202965) 46639) 72 +
  2 * 133344 * 118 * 4012 +
  ceilDiv (82161 * (c₀ + 2 * f * c₁) + 93278 * (p₀ + 2 * f * p₁)) 1492448
private theorem row_le (lo j f m₀ m₁ m₂ c₀ c₁ p₀ p₁ price allowance : ℕ) :
    let a : Shape := ⟨118, j, f⟩
    let p := a.chamber
    let q := P3_6.primaryBox
    let L := P3_6.taylorLength
    let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
    let e₁ := liftedChart (L + 1) p
    let e₂ := liftedChart (L + 2) p
    let h := chart L p
    let z := q.plus (p.scale 4)
    mixed32 p q e₁ e₂ = m₀ → mixed32 p q g e₂ = m₁ → mixed32 p q g e₁ = m₂ →
    mixed32 p q z h = c₀ → mixed32 p p p h = c₁ →
    mixed32 p q z p = p₀ → mixed32 p p p p = p₁ →
    (chart (L + 1) p).b = 31202965 →
    priceFromParts f m₀ m₁ m₂ c₀ c₁ p₀ p₁ = price → budget lo = allowance →
    price ≤ allowance → P3_6.physicalPrice a twoOrder ≤ budget lo := by
  intro a p q L g e₁ e₂ h z hm₀ hm₁ hm₂ hc₀ hc₁ hp₀ hp₁ hb hprice hbudget hle
  have hsurface : P3_6.surfaceNumerator32 p q ≤ m₀ + 133346 * m₁ + 133347 * m₂ := by
    unfold P3_6.surfaceNumerator32
    change min _ (mixed32 p q e₁ e₂ + 133346 * mixed32 p q g e₂ +
      133347 * mixed32 p q g e₁) ≤ _
    rw [hm₀, hm₁, hm₂]
    exact min_le_right _ _
  have hpaid : P3_6.physicalPrice a twoOrder ≤ priceFromParts f m₀ m₁ m₂ c₀ c₁ p₀ p₁ := by
    unfold P3_6.physicalPrice priceFromParts
    change ceilDiv (ceilDiv (P3_6.surfaceNumerator32 p q) 32 +
          ceilDiv ((82161 + 2 * 46639) * 118 * 4012 * (chart (L + 1) p).b) 46639) 72 +
        2 * 133344 * 118 * 4012 +
        ceilDiv (82161 * (mixed32 p q z h + 2 * f * mixed32 p p p h) +
          93278 * (mixed32 p q z p + 2 * f * mixed32 p p p p)) 1492448 ≤ _
    rw [hb, hc₀, hc₁, hp₀, hp₁]
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (ceil_mono (Nat.add_le_add_right (ceil_mono hsurface _) _) _) _) _
  rw [← hprice] at hle
  rw [hbudget]
  exact hpaid.trans hle
section
set_option maxRecDepth 4096
local notation "row!" lo "," hi "," f "," m₀ "," m₁ "," m₂ "," c₀ "," c₁ "," p₀ "," p₁
    "," price "," allowance =>
  row_le lo hi f m₀ m₁ m₂ c₀ c₁ p₀ p₁ price allowance
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
end
end P3_6_8_8
end

end Merged6967_GoldBranch6N8
