import ProximityPrize.SubmissionLower.LowerGeometry


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical BigOperators Matrix
open RCN081 RCN082 RCN156 RCN167 RCN234 LocatorDerivativeChain

noncomputable section

set_option maxHeartbeats 2600000

variable {K : Type} [Field K]

abbrev ShortCarrier (K : Type) [Field K] := MvPolynomial (Fin 4) K

def DirectGermCount (pool : Finset K) (selected : K → Polynomial K) : Prop :=
  ∀ (J : MvPolynomial (Fin 3) K) (A : Finset K), A ⊆ pool → J ≠ 0 →
    ∀ y t : ℕ, J.degreeOf 1 ≤ y → J.weightedTotalDegree ![0,1,1] ≤ t →
      t < 2130706433 →
      (∀ g ∈ A, MvPolynomial.eval₂Hom Polynomial.C
        ![Polynomial.X,selected g,Polynomial.C g] J = 0) →
      A.card ≤ t+2130706433*y

def shortFactorSeeds (A : Finset K) (selected : K → Polynomial K) (F : ShortCarrier K) : Finset K :=
  A.filter fun g => RCN319.specialization K (selected g) g F = 0

def shortSingularSeeds (A : Finset K) (selected : K → Polynomial K) (F : ShortCarrier K) : Finset K :=
  (shortFactorSeeds A selected F).filter fun g =>
    RCN319.specialization K (selected g) g (MvPolynomial.pderiv 2 F) = 0

def shortRegularSeeds (A : Finset K) (selected : K → Polynomial K) (F : ShortCarrier K) : Finset K :=
  (shortFactorSeeds A selected F).filter fun g =>
    RCN319.specialization K (selected g) g (MvPolynomial.pderiv 2 F) ≠ 0

def tangentFactors (H : ShortCarrier K) (D : ShortCarrier K → ShortCarrier K) :
    Finset (ShortCarrier K) :=
  (positiveRFactors H).filter (fun F => F ∣ D F)

def transverseFactors (H : ShortCarrier K) (D : ShortCarrier K → ShortCarrier K) :
    Finset (ShortCarrier K) :=
  (positiveRFactors H).filter (fun F => ¬ F ∣ D F)

def shortPrimaryExcluded (A : Finset K) (selected : K → Polynomial K)
    (H : ShortCarrier K) (D : ShortCarrier K → ShortCarrier K) : Finset K :=
  shortFactorSeeds A selected (rfreeProduct H) ∪
    (positiveRFactors H).biUnion (shortSingularSeeds A selected) ∪
    (tangentFactors H D).biUnion (shortFactorSeeds A selected)

theorem short_primary_regular_cover (H : ShortCarrier K) (hH : H ≠ 0)
    (A : Finset K) (selected : K → Polynomial K) (D : ShortCarrier K → ShortCarrier K)
    (hzero : ∀ g ∈ A, RCN319.specialization K (selected g) g H = 0) :
    A ⊆ shortPrimaryExcluded A selected H D ∪
      (transverseFactors H D).biUnion (shortRegularSeeds A selected) := by
  intro g hg
  obtain ⟨F,hF,hsol⟩ := exists_active_factor_of_solution H hH (selected g) g (hzero g hg)
  have withF : g ∈ shortFactorSeeds A selected F := Finset.mem_filter.mpr ⟨hg,hsol⟩
  by_cases hr : F.degreeOf 2 = 0
  · have dvd : F ∣ rfreeProduct H := Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hF,hr⟩)
    obtain ⟨G,hG⟩ := dvd
    have hz : RCN319.specialization K (selected g) g (rfreeProduct H) = 0 := by
      rw [hG,map_mul,hsol,zero_mul]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hg,hz⟩)))
  have hpos : F ∈ positiveRFactors H := Finset.mem_filter.mpr ⟨hF,Nat.pos_of_ne_zero hr⟩
  by_cases hfold : RCN319.specialization K (selected g) g (MvPolynomial.pderiv 2 F) = 0
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨F,hpos,Finset.mem_filter.mpr ⟨withF,hfold⟩⟩)))
  by_cases ht : F ∣ D F
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨F,Finset.mem_filter.mpr ⟨hpos,ht⟩,withF⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨F,Finset.mem_filter.mpr ⟨hpos,ht⟩,Finset.mem_filter.mpr ⟨withF,hfold⟩⟩)

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
