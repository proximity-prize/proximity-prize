import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.RingHomShortcuts

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
abbrev firstOrder : ℕ := 4127574
abbrev secondOrder : ℕ := 1857492
abbrev firstCut : ℕ := 5000 * 179769 - firstOrder
abbrev secondCut : ℕ := 5000 * 179769 - secondOrder
abbrev bankRank : ℕ := 643975827135108623227
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  6987 * a none + 48700 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
/-- The low fat chain works with rows whose seed degree is at most 24,000 in the first bank and 32,000 in the second. -/
abbrev seedCap (a : K1_13.Shape) : ℕ := if a.b = 6789 then 24000 else 32000
def Caps27 {R : Type*} [CommSemiring R] (a : K1_13.Shape) (F : SeedRow R) : Prop :=
  Caps a F ∧ seedDegree F ≤ seedCap a
def Source27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Source w P L a t F ∧ seedDegree F ≤ seedCap a
def HasRank27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧ ∀ i, Source27 w P L a t (e i)
abbrev commonBox : K1_13.Shape := ⟨2945, 954, 0⟩
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
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 83
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
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 179769 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2329 →
    (∃ F, F ≠ 0 ∧ Source27 w P L firstBox firstCut F) ∧
    HasRank27 w P L secondBox secondCut bankRank
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow),
    F ≠ 0 → Caps27 firstBox F → HasRank27 w P L secondBox secondCut bankRank →
    ∃ G, G ∈ Necessary w P L ∧ Nonempty (CommonPair (toGeneric F) (toGeneric G))
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∀ (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2329 →
      (∀ F, Source27 w P L firstBox firstCut F → ∀ γ ∈ Γ,
        MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstOrder) ∧
      (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
        MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondOrder)

abbrev fatOrder : ℕ := 22533
def Holds (E : FatEquations) (S : (Polynomial K1_13.Geom)) : Prop :=
  K1_13.atJet E.common S = 0 ∨ K1_13.OrderAt E.residual S fatOrder

def Equations : Prop :=
  ∀ (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)),
    (∀ γ ∈ Γ, (s γ).natDegree ≤ 133400) →
    (∀ γ ∈ Γ, ∃ T : Finset I, 179769 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i) →
    ∀ P : K1_13.PoleData Γ s, P.H.natDegree ≤ 2329 →
    ∃ (book : Finset K1.K) (E : FatEquations), book.card ≤ 56000 ∧
      ∀ γ ∈ Γ, γ ∉ book → Holds E (K1_13.extend (s γ))
end
end Low6966Fat
end

end Merged_R6960Low6966FatDefs

