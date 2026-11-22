import ProximityPrize.SubmissionLower.Low53At2389SharedShapeRank
import ProximityPrize.SubmissionLower.Shared50ChooseCut
import ProximityPrize.SubmissionLower.Low53At2389SharedPrice
set_option Elab.async false
set_option linter.style.haveILetI false
set_option maxRecDepth 12000

namespace Low53At2389SharedChooseCut
noncomputable section

open K1_13 (Geom Row Shape shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height cycleLength_ge_order)
open MvPolynomial
open Low53At2389SharedPrice (slope coord)
open Shared50ChooseCut (SuitableSurface)
open private valuation_factorization minimal_pair mem_of_order weight_coord
  from ProximityPrize.SubmissionLower.Shared50ChooseCut

private theorem cap_coords {Q : Row 4} {r : ℕ}
    (hQ : ∀ m ∈ Q.support, Low53At2389ShapeGate.fits r m) (i : Fin 3) :
    coord (shape Q) i ≤ r*coord slope i := by
  change Final50SharedPrice.coord (shape Q) i ≤ _
  rw [weight_coord]
  apply Finset.sup_le
  intro m hm
  have hs := hQ m hm
  fin_cases i
  · exact hs.1
  · exact hs.2.1
  · simpa [Finsupp.weight_eq_sum, Finsupp.sum_fintype, Low53At2389SharedPrice.coord,
      Low53At2389SharedPrice.slope, Pi.single_apply] using hs.2.2

/-- The same independent cut has positive residual order at every selected surface. -/
theorem exists_cut {w Γ s} (hm : Low53At2389Price.Messages w Γ s) (hprimary : Low53At2389Order.PrimaryRank w)
    (f : Row 4) (hf : Irreducible f) (hpos : 0<f.totalDegree)
    (multiplicityCap : ℕ) (pivot : Fin 3)
    (hguard : multiplicityCap*coord slope pivot < coord (shape f) pivot)
    (surfaces : Finset (Ideal GeoJets))
    (hp : ∀ P ∈ surfaces, Shared50Persistent.Persistent Γ s P)
    (hh : ∀ P ∈ surfaces, SuitableSurface f multiplicityCap P) :
    ∃ r a : ℕ, 0<r ∧ 0<r-multiplicityCap*a ∧ ∃ G : Row 4, G≠0 ∧ ¬f∣G ∧
      (∀ i, a*coord (shape f) i + coord (shape G) i ≤ r*coord slope i) ∧
      ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f G).IsMinimalPrime P,
        @VanishesTo _ _ P h.isPrime (toGeneric G) (r-multiplicityCap*a) ∧
        ((r-multiplicityCap*a : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) P h.isPrime := by
  obtain ⟨r,hr,Q,hQ,hs,ho⟩ := Low53At2389SharedShapeRank.exists_polynomial hm hprimary surfaces hp
  obtain ⟨a,G,hfac,hG,hind⟩ := valuation_factorization hf.ne_zero hpos hQ
  have hbound (i : Fin 3) : a*coord (shape f) i+coord (shape G) i ≤ r*coord slope i := by
    have hshape := Shared50ChooseCut.shape_product hf.ne_zero hG hfac i
    change coord (shape Q) i = a*coord (shape f) i+coord (shape G) i at hshape
    rw [← hshape]
    exact cap_coords hs i
  have hres : 0<r-multiplicityCap*a := Shared50ShapeRankBase.residual_order_pos hr hguard
    ((Nat.le_add_right _ _).trans (hbound pivot))
  refine ⟨r,a,hr,hres,G,hG,hind,hbound,?_⟩
  intro P hP
  have hdata := hh P hP
  letI := hdata.prime
  have hmap : toGeneric Q = (toGeneric f)^a*toGeneric G := by
    simp [hfac,toGeneric,map_mul,map_pow]
  have hGo : VanishesTo P (toGeneric G) (r-multiplicityCap*a) := by
    apply Shared50OrderDivision.vanishesTo_of_pow_mul_hasse P hdata.low
    rw [← hmap]
    exact ho P hP
  have hmin := minimal_pair hf hind hdata.height hdata.contains (mem_of_order hres hGo)
  exact ⟨hmin,hGo,cycleLength_ge_order hdata.height hdata.contains hGo⟩

#print axioms exists_cut
end
end Low53At2389SharedChooseCut
