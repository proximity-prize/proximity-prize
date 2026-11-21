import ProximityPrize.SubmissionLower.GoldBranch6N4

set_option Elab.async false
section
namespace Final50Fat
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
abbrev firstOrder : ℕ := 5958043
abbrev secondOrder : ℕ := 3221537
abbrev firstCut : ℕ := 5000 * 179915 - firstOrder
abbrev secondCut : ℕ := 5000 * 179915 - secondOrder
abbrev bankRank : ℕ := 1435744580951965830001
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  7059 * a none + 48846 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
def Necessary {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P) :
    Submodule Geom PhysicalRow :=
  Submodule.span Geom {Q | ∃ t F a, Source w P L secondBox t F ∧
    t + mixedWeight a ≤ secondCut ∧ Q = mixedHasse a F}
def MixedOrder (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ) : Prop :=
  ∀ a ∈ (translate (atPoint z y) F).support, d ≤ mixedWeight a
def PairOrders (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) : Prop :=
  MixedOrder F z y firstOrder ∧ MixedOrder G z y secondOrder
abbrev CommonPair := P3_6_4.CommonPair
end
end Final50Fat
end
section
namespace Final50Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 179915 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2353 →
    (∃ F, F ≠ 0 ∧ Source w P L firstBox firstCut F) ∧
    HasRank w P L secondBox secondCut bankRank
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow),
    F ≠ 0 → Caps firstBox F → HasRank w P L secondBox secondCut bankRank →
    ∃ G, G ∈ Necessary w P L ∧ Nonempty (CommonPair (toGeneric F) (toGeneric G))
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∀ (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2353 →
      (∀ F, Source w P L firstBox firstCut F → ∀ γ ∈ Γ,
        MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstOrder) ∧
      (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
        MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondOrder)

abbrev fatOrder : ℕ := 55667
def Holds (E : P3_6.FatEquations) (S : K1_13.Geom[X]) : Prop :=
  K1_13.atJet E.common S = 0 ∨ K1_13.OrderAt E.residual S fatOrder

def Equations : Prop :=
  ∀ (w : I → K) (Γ : Finset K) (s : K → K[X]),
    (∀ γ ∈ Γ, (s γ).natDegree ≤ 133424) →
    (∀ γ ∈ Γ, ∃ T : Finset I, 179915 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i) →
    ∀ P : K1_13.PoleData Γ s, P.H.natDegree ≤ 2353 →
    ∃ (book : Finset K1.K) (E : P3_6.FatEquations), book.card ≤ 140000 ∧
      ∀ γ ∈ Γ, γ ∉ book → Holds E (K1_13.extend (s γ))
end
end Final50Fat
end
