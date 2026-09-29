import ProximityPrize.SubmissionLower.MovingSourceWeightedPairFamily6814

/-! Convert the proved weighted pair certificate to actual isolated-point
counts, retaining the better old Z-source estimate on the SAME family. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWeightedPairPoints6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN002 RCN046 RCN072 RCN084 RCN095 RCN237 RCN264 RCN338 RCN341 RCN344
open MovingSourceRegularRestriction6814 MovingSourceHybridCount6814 MovingFiberThreeSources6811

private theorem sum_pullback_le {I J : Type} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (v : J → ℕ) :
    (∑ i, v (f i))≤∑ j, v j := by
  classical
  letI : DecidableEq J := Classical.decEq J
  calc
    _=∑ j∈Finset.univ.image f, v j := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _≤_ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

private theorem hybrid_arithmetic {I : Type} [Fintype I]
    (z u v : I → ℕ) (a b c n d count zCap uCap vCap : ℕ)
    (hcount : count≤∑ i, (a*z i+b*u i+c*v i))
    (hz : n*(∑ i, z i)≤zCap) (hu : (∑ i, d*u i)≤uCap) (hv : (∑ i, d*v i)≤vCap) :
    n*d*count≤d*a*zCap+n*(b*uCap+c*vCap) := by
  have he : n*d*(∑ i, (a*z i+b*u i+c*v i))=
      d*a*(n*∑ i, z i)+n*(b*(∑ i, d*u i)+c*(∑ i, d*v i)) := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    ring
  exact (Nat.mul_le_mul_left (n*d) hcount).trans (he.le.trans
    (Nat.add_le_add (Nat.mul_le_mul_left (d*a) hz)
      (Nat.mul_le_mul_left n (Nat.add_le_add (Nat.mul_le_mul_left b hu) (Nat.mul_le_mul_left c hv)))))

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable {G M R : MvPolynomial (Fin 3) Ω} {p q : FlagDegree}

def restrict_weighted_certificate
    (base : ∀ V : RegularComponent Ω G M R, SeparableLiteralCoordinate V.1)
    (unit : AdaptiveUnitProjectionFamily base p q) (d : ℕ)
    (cert : RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d))
    (L : MvPolynomial (Fin 3) Ω) :
    RegularComponentWeightedInertiaResultantCertificate
      (restrict_projection_family base p q unit L).toPrimeFlagBudgetFamily (fun _ => d) where
  z := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun V => d*unit.toPrimeFlagBudgetFamily.zCost V)).trans cert.z
  yz := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun V => d*unit.toPrimeFlagBudgetFamily.yzCost V)).trans cert.yz
  all := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun V => d*unit.toPrimeFlagBudgetFamily.allCost V)).trans cert.all

theorem weighted_hybrid_isolated_points
    (base : ∀ V : RegularComponent Ω G M R, SeparableLiteralCoordinate V.1)
    (unit : AdaptiveUnitProjectionFamily base p q) (d : ℕ)
    (cert : RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d))
    (n zCap : ℕ)
    (hZ : n*(∑ V : RegularComponent Ω G M R, unit.toPrimeFlagBudgetFamily.zCost V)≤zCap)
    (W : FlagDegree) (cut : MvPolynomial (Fin 3) Ω) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → Ω))
    (hG : ∀ x∈points, MvPolynomial.eval x G=0)
    (hM : ∀ x∈points, MvPolynomial.eval x M=0)
    (hR : ∀ x∈points, MvPolynomial.eval x R≠0)
    (hzero : ∀ x∈points, MvPolynomial.aeval x cut=0)
    (hisolated : ∀ x∈points, IsolatedPoint G M cut x) :
    n*d*points.card≤d*W.zOnly*zCap+n*(W.yz*flagMixed p q unitYZFlag+W.all*flagMixed p q unitAllFlag) := by
  let budget := unit.toPrimeFlagBudgetFamily
  have hcard : points.card≤∑ V : RegularComponent Ω G M R, budget.weightedCost W V := by
    apply (card_le_sum_componentSeeds Ω G M R points id hG hM hR).trans
    apply Finset.sum_le_sum
    intro V _
    by_cases he : (componentSeeds Ω G M R points id V).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxS := componentSeeds_subset Ω G M R points id V hx
      have hxV := componentSeeds_on_prime Ω G M R points id V x hx
      apply (budget.primeBudget V).zero_le W cut hcut
        (hisolated x hxS V.1 inferInstance (regularComponent_ne_point Ω G M R V)
          hxV (regularComponent_G_mem Ω G M R V) (regularComponent_T_mem Ω G M R V))
      · intro y hy
        exact componentSeeds_on_prime Ω G M R points id V y hy
      · intro y hy
        exact hzero y (componentSeeds_subset Ω G M R points id V hy)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  exact hybrid_arithmetic budget.zCost budget.yzCost budget.allCost W.zOnly W.yz W.all n d
    points.card zCap (flagMixed p q unitYZFlag) (flagMixed p q unitAllFlag) hcard hZ cert.yz cert.all

open RCN136 RCN207
theorem restricted_weighted_source_point_count
    {K : Type} [Field K]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) (S : Source F)
    (carrier : MvPolynomial (Fin 3) Ω) (pOld : FlagDegree)
    (hcarrier : carrier≠0) (hcarrierF : carrier∣surfaceMap phi F) (hp : PolynomialInFlag pOld carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(pOld.zOnly+pOld.yz+pOld.all)<c)
    (h2 : (2 : Ω)≠0) (hfact : (S.k.factorial : Ω)≠0)
    (Q A : MvPolynomial (Fin 3) Ω) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (R : MvPolynomial (Fin 3) Ω) (hHdiv : surfaceMap phi (RCN313.polyH K F)∣R)
    (base : ∀ V : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      SeparableLiteralCoordinate V.1)
    (unit : AdaptiveUnitProjectionFamily base p q) (d : ℕ)
    (cert : RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d))
    (W : FlagDegree) (cut : MvPolynomial (Fin 3) Ω) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → Ω))
    (hG : ∀ v∈points, MvPolynomial.eval v carrier=0)
    (hM : ∀ v∈points, MvPolynomial.eval v
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target)=0)
    (hR : ∀ v∈points, MvPolynomial.eval v (R*S.leading phi)≠0)
    (hzero : ∀ v∈points, MvPolynomial.aeval v cut=0)
    (hisolated : ∀ v∈points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) cut v) :
    S.d*d*points.card≤d*W.zOnly*flagMixed pOld unitZFlag S.flag+
      S.d*(W.yz*flagMixed p q unitYZFlag+W.all*flagMixed p q unitAllFlag) := by
  let M := movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target
  let base' := fun V : RegularComponent Ω carrier M (R*S.leading phi) => base (forgetExtra (S.leading phi) V)
  let unit' := restrict_projection_family base p q unit (S.leading phi)
  let cert' := restrict_weighted_certificate base unit d cert (S.leading phi)
  have hH (V : RegularComponent Ω carrier M (R*S.leading phi)) : surfaceMap phi (RCN313.polyH K F)∉V.1 := by
    intro hh
    exact regularComponent_H_not_mem Ω carrier M (R*S.leading phi) V
      (V.1.mem_of_dvd (dvd_mul_of_dvd_left hHdiv _) hh)
  have hZ := old_z_bound_on_new_projections phi F S carrier pOld hcarrier hcarrierF hp
    c hunit h2 hfact Q A target hQ hA (R*S.leading phi)
    hH (extra_not_mem (S.leading phi)) base' p q unit'
  exact weighted_hybrid_isolated_points base' unit' d cert' S.d (flagMixed pOld unitZFlag S.flag)
    hZ W cut hcut points hG hM hR hzero hisolated

#print axioms weighted_hybrid_isolated_points
#print axioms restricted_weighted_source_point_count
end
end ProximityPrize.SubmissionLower.MovingSourceWeightedPairPoints6814
