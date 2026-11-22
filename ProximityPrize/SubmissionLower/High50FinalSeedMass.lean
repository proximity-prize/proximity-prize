import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.PortHighFinish

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace High50FinalSeedMass
noncomputable section
open K1_14 K1_14_3 Polynomial
open K1_14_2 (Ambient mapGenericSeed OverSeeds)
open K1_14_2_2 (Active)
open P0_10R.Bridge (surfaceOf)
open scoped Polynomial BigOperators
open private fibreHom seedMap seedPoint seed_chart from ProximityPrize.SubmissionLower.Fast069
open private K1_14_3_7.toSeed K1_14_3_7.toClosure K1_14_3_7.toSeed_injective
  K1_14_3_7.primitive_model K1_14_3_7.eval_at_fibre_C K1_14_3_7.fibre_leading_dvd
  K1_14_3_7.minpoly_pow_dvd K1_14_3_7.seedGCD from ProximityPrize.SubmissionLower.Fast053

/-- A seed fibre can use a root whose degree is bounded by its section mass. -/
theorem seed_side_of_active {I : Ideal Ambient} (hI : Active I) :
    ∃ y v, OnSeedFibre (surfaceOf I hI.prime) y v ∧ IsSeparable SeedField y ∧
      IsSeparable SeedField v ∧ (minpoly SeedField y).natDegree ≤ Module.finrank SeedField (OverSeeds I) := by
  obtain ⟨f, hf, hsep⟩ := @fibreHom mapGenericSeed _ seedMap I hI.prime
    hI.seed_finite hI.seed_size.1 hI.seed_size.2
  refine ⟨f (MvPolynomial.X 0), f (MvPolynomial.X 1), ?_, hsep _, hsep _, ?_⟩
  · unfold OnSeedFibre
    rw [← seed_chart, ← RingHom.comap_ker, seedPoint, hf]
    rfl
  · let J := I.map mapGenericSeed
    have hJ : J ≤ RingHom.ker f.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      rw [RingHom.comap_ker, hf]
    let g := Ideal.Quotient.liftₐ J f (fun x hx => RingHom.mem_ker.mp (hJ hx))
    let B := OverSeeds I
    let _ : Module.Finite SeedField B := hI.seed_finite
    let y : B := Ideal.Quotient.mk J (MvPolynomial.X 0)
    have hgy : g y = f (MvPolynomial.X 0) := rfl
    have hmin : minpoly SeedField (g y) ∣ minpoly SeedField y := by
      apply minpoly.dvd
      rw [aeval_algHom_apply, minpoly.aeval, map_zero]
    rw [← hgy]
    exact (natDegree_le_of_dvd hmin (minpoly.ne_zero (Algebra.IsIntegral.isIntegral y))).trans
      (minpoly.natDegree_le y)

private theorem sum_image_bound {σ τ : Type*} [DecidableEq τ] (S : Finset σ) (m : σ → τ) (w : τ → ℕ) :
    (∑ u ∈ S.image m, w u) ≤ ∑ q ∈ S, w (m q) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hm : m a ∈ s.image m
    · rw [Finset.insert_eq_of_mem hm]
      exact ih.trans (Nat.le_add_left _ _)
    · rw [Finset.sum_insert hm]
      exact Nat.add_le_add_left ih _

theorem bounded_product (qs : Finset Surface) (hqs : qs.Nonempty)
    (cap : ↥qs → ℕ) (hside : ∀ q : ↥qs, ∃ y v, OnSeedFibre q y v ∧
      IsSeparable SeedField y ∧ IsSeparable SeedField v ∧ (minpoly SeedField y).natDegree ≤ cap q) :
    ∃ f, ProjectedProduct qs f ∧ f.natDegree ≤ ∑ q ∈ qs.attach, cap q := by
  classical
  choose y v hpoint hy _hv hcap using hside
  let m (q : ↥qs) := minpoly SeedField (y q)
  let factors : Finset (SeedField[X]) := qs.attach.image m
  have hmem (q : ↥qs) : m q ∈ factors :=
    Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩
  have hpre {u : SeedField[X]} (hu : u ∈ factors) : ∃ q : ↥qs, m q = u := by
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hu
    exact ⟨q, hq⟩
  have hmonic (u : SeedField[X]) (hu : u ∈ factors) : u.Monic := by
    obtain ⟨q, rfl⟩ := hpre hu
    exact minpoly.monic (hy q).isIntegral
  have hirr (u : SeedField[X]) (hu : u ∈ factors) : Irreducible u := by
    obtain ⟨q, rfl⟩ := hpre hu
    exact minpoly.irreducible (hy q).isIntegral
  have hpair (u : SeedField[X]) (hu : u ∈ factors) (w : SeedField[X]) (hw : w ∈ factors)
      (hne : u ≠ w) : IsCoprime u w := by
    apply (hirr u hu).coprime_iff_not_dvd.mpr
    intro hd
    exact hne (eq_of_monic_of_associated (hmonic u hu) (hmonic w hw)
      (associated_of_dvd_dvd hd ((hirr u hu).dvd_symm (hirr w hw) hd)))
  let g : SeedField[X] := ∏ u ∈ factors, u
  have hg : g ≠ 0 := (monic_prod_of_monic _ _ hmonic).ne_zero
  have hsep : g.Separable := by
    apply separable_prod' hpair
    intro u hu
    obtain ⟨q, rfl⟩ := hpre hu
    exact hy q
  have hm_dvd (q : ↥qs) : m q ∣ g := Finset.dvd_prod_of_mem id (hmem q)
  obtain ⟨f, hprim, hassoc⟩ := K1_14_3_7.primitive_model g hg
  have hfmap : f.map K1_14_3_7.toSeed ≠ 0 :=
    (Polynomial.map_ne_zero_iff K1_14_3_7.toSeed_injective).mpr hprim.ne_zero
  refine ⟨f, ⟨?_, hprim, hsep.of_dvd hassoc.dvd, ?_, ?_⟩, ?_⟩
  · obtain ⟨q, hq⟩ := hqs
    have hdeg := natDegree_le_of_dvd ((hm_dvd ⟨q, hq⟩).trans hassoc.dvd') hfmap
    rw [natDegree_map_eq_of_injective K1_14_3_7.toSeed_injective] at hdeg
    exact (hirr _ (hmem ⟨q, hq⟩)).natDegree_pos.trans_le hdeg
  · intro q hq
    let q' : ↥qs := ⟨q, hq⟩
    rw [← hpoint q', RingHom.mem_ker, K1_14_3_7.eval_at_fibre_C]
    exact minpoly.dvd_iff.mp ((hm_dvd q').trans hassoc.dvd')
  · intro P k _ horder
    let n := k - P.natDegree
    have hdiv : g ^ n ∣ P.leadingCoeff.map K1_14_3_7.toSeed := by
      rw [show g ^ n = ∏ u ∈ factors, u ^ n from (Finset.prod_pow factors n id).symm]
      apply Finset.prod_dvd_of_coprime
      · intro u hu w hw hne
        exact (hpair u hu w hw hne).pow
      · intro u hu
        obtain ⟨q, rfl⟩ := hpre hu
        have hc := K1_14_3_7.fibre_leading_dvd (hpoint q) (horder q q.property)
        rw [show seedGeneric = K1_14_3_7.toClosure.comp K1_14_3_7.toSeed from rfl, ← Polynomial.map_map] at hc
        exact K1_14_3_7.minpoly_pow_dvd (hy q) hc
    let := K1_14_3_7.seedGCD
    have hpow (e : ℕ) : (f ^ e).IsPrimitive := by
      induction e with
      | zero => simpa only [pow_zero] using (isPrimitive_one : (1 : Equation).IsPrimitive)
      | succ e ih => rw [pow_succ]; exact ih.mul hprim
    apply (hpow n).dvd_of_fraction_map_dvd_fraction_map (K := SeedField)
    rw [Polynomial.map_pow]
    exact hassoc.pow_pow.dvd.trans hdiv
  · have hdeg := natDegree_le_of_dvd hassoc.dvd hg
    rw [natDegree_map_eq_of_injective K1_14_3_7.toSeed_injective] at hdeg
    refine hdeg.trans ?_
    rw [show g.natDegree = ∑ u ∈ factors, u.natDegree from natDegree_prod_of_monic _ _ hmonic]
    exact (sum_image_bound qs.attach m fun u => u.natDegree).trans
      (Finset.sum_le_sum (fun q _ => hcap q))

#print axioms seed_side_of_active
#print axioms bounded_product
end
end High50FinalSeedMass
