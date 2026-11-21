import ProximityPrize.SubmissionLower.Final50ActiveCyclePrice
import ProximityPrize.SubmissionLower.Final50ActiveCycleChart
set_option Elab.async false
namespace Shared50BentCaps
noncomputable section

open K1_13 (Shape Row shape)
open K1_13_6 (GeoField)
open Final50Price (taylorLength)
open Final50ActiveCycle (Doubled Chart)
open Low48BentLattice (Cap Allowed Chamber latticePoints)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily capSum ambient_cap integral mixedDegree)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators
open private slots ambient_list from ProximityPrize.SubmissionLower.Low48BentCyclePrice

def caps (p q : Shape) : Fin 5 → Cap :=
  ![(p, 0), (q, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]

theorem caps_chamber {p q : Shape} (hb : p.j ≤ p.b) (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j) (hq : Chamber (q,0)) :
    ∀ i, Chamber (caps p q i) := by
  intro i
  fin_cases i
  · change Chamber (p, 0)
    exact ⟨hb, show 3 * p.t ≤ p.j by omega, Nat.zero_le _⟩
  · exact hq
  · exact Low48BentSupport.graph_chamber ht hj
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 4)
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 3)

private theorem last_allowed {p q : Shape}
    (v : Fin 5) : Allowed (caps p q 4) (Finsupp.single v 1) := by
  let k := taylorLength - 3
  have hb' : 1 ≤ 1 + k * (p.b - 1) := by omega
  have hj' : 4 ≤ 4 + k * (p.j - 2) := by omega
  have ht' : 2 ≤ 2 + k * p.t := by omega
  have hd' : 1 ≤ min (1 + k) ((2 + k * p.t) / 2) := by omega
  fin_cases v <;> simp [caps, lifted, Allowed, ← show k = taylorLength - 3 from rfl] <;> omega

theorem ordinary_doubled {p q : Shape} :
    Doubled (rawFamily (caps p q)) (capFamily (caps p q)) where
  zero_mem i := by simp [rawFamily, Allowed]
  pair_mem _ _ ha _ hb := Low48BentSupport.raw_add ha hb
  last_coordinate := last_allowed

private def integr (a : Cap) : ℚ := integral a

private def signed (p q : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps p q))

private theorem base_signed (p q : Shape) :
    Final50Price.tiltedSurface p q = (signed p q).toNat := by
  change Low48Price.ambientMix (slots.map (caps p q)) = _
  exact ambient_list (caps p q)

private theorem base_normalize (p q : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (capSum (caps p q) (positiveDiagonal J))) = (signed p q : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps p q)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr (capSum (caps p q) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (Low48BentLattice.Sum J (caps p q)) from H]
  unfold signed
  push_cast
  rfl

private theorem ordinary_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget {p q : Shape} (h : ∀ i, Chamber (caps p q i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps p q)) ⊥ Finset.univ ≤
      (Final50Price.tiltedSurface p q : ℚ) := by
  rw [mul_assoc, ambient_cap (caps p q) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize, base_signed]
  exact_mod_cast (show signed p q ≤ ((signed p q).toNat : ℤ) by omega)


theorem chart {f Q : Row 4} {l : ℕ} (q : Shape) (ht : 1 ≤ (shape f).t)
    (b : Final50GeometryCut_2.Branch f Q l) :
    Chart (rawFamily (caps (shape f).chamber q)) b := by
  have h := Final50ActiveCycle.ordinary_chart ht b
  exact h

#print axioms ordinary_budget
#print axioms chart

end
end Shared50BentCaps
