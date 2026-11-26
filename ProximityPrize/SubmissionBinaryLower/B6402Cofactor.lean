import ProximityPrize.SubmissionBinaryLower.B6401ResLineOrd
import ProximityPrize.SubmissionBinaryLower.B6402MixedDegree

/-! Removing true polynomial multiples in the original seed.
The clearing-denominators construction follows PR 694's irreducibility proof. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402Cofactor
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402MixedDegree
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {Fld : Type*} [Field Fld]

theorem clear_seed_denominators (R : ContactPoly (RatFunc Fld)) :
    ∃ d : Polynomial Fld, ∃ H : ContactPoly (Polynomial Fld), d ≠ 0 ∧
      cC (algebraMap (Polynomial Fld) (RatFunc Fld) d) * R = liftCRat H := by
  classical
  let alg : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have halg_inj : Function.Injective alg := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have clearAll : ∀ R : ContactPoly (RatFunc Fld),
      ∃ (d : Polynomial Fld) (R' : ContactPoly (Polynomial Fld)), d ≠ 0 ∧ cC (alg d) * R = liftCRat R' := by
    intro R
    let coords : Finset (ℕ × ℕ × ℕ) :=
      R.support.biUnion fun k => (R.coeff k).support.biUnion fun j =>
        ((R.coeff k).coeff j).support.image fun i => (k, j, i)
    have hsurj : ∀ c : ℕ × ℕ × ℕ, ∃ (n d : Polynomial Fld), d ≠ 0 ∧
        alg d * (((R.coeff c.1).coeff c.2.1).coeff c.2.2) = alg n := fun c => by
      obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial Fld)) (((R.coeff c.1).coeff c.2.1).coeff c.2.2)
      exact ⟨n, d, nonZeroDivisors.ne_zero d.2, by simpa [mul_comm] using hd⟩
    choose nC dC hdC_ne hndC using hsurj
    let d : Polynomial Fld := ∏ c ∈ coords, dC c
    have hd_ne : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hdC_ne c
    have hnum : ∀ k j i, ∃ p : Polynomial Fld, alg d * (((R.coeff k).coeff j).coeff i) = alg p := by
      intro k j i
      by_cases hnz : ((R.coeff k).coeff j).coeff i = 0
      · exact ⟨0, by simp [hnz]⟩
      · have hmem : (k, j, i) ∈ coords := by
          simp only [coords, Finset.mem_biUnion, Finset.mem_image, Polynomial.mem_support_iff, Prod.mk.injEq]
          exact ⟨k, fun h => hnz (by simp [h]), j, fun h => hnz (by simp [h]), i, hnz, rfl, rfl, rfl⟩
        refine ⟨(∏ c ∈ coords.erase (k, j, i), dC c) * nC (k, j, i), ?_⟩
        have hd_eq : d = (∏ c ∈ coords.erase (k, j, i), dC c) * dC (k, j, i) :=
          (Finset.mul_prod_erase coords dC hmem).symm.trans (mul_comm _ _)
        rw [hd_eq, map_mul, map_mul, mul_assoc, hndC (k, j, i)]
    choose pC hpC using hnum
    let R' : ContactPoly (Polynomial Fld) :=
      ∑ k ∈ R.support, Polynomial.monomial k (∑ j ∈ (R.coeff k).support,
        Polynomial.monomial j (∑ i ∈ ((R.coeff k).coeff j).support, Polynomial.monomial i (pC k j i)))
    refine ⟨d, R', hd_ne, ?_⟩
    apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
    have hL : (((cC (alg d) * R).coeff k).coeff j).coeff i = alg d * (((R.coeff k).coeff j).coeff i) := by
      unfold cC; simp [Polynomial.coeff_C_mul]
    rw [hL, hpC k j i]
    have hR : (((liftCRat R').coeff k).coeff j).coeff i = alg (((R'.coeff k).coeff j).coeff i) := by
      dsimp only [alg]; simp [liftCRat, liftBiRat]
    rw [hR]; congr 1
    dsimp only [R']; rw [finset_sum_coeff]
    by_cases hk : k ∈ R.support
    · rw [Finset.sum_eq_single k]
      · rw [Polynomial.coeff_monomial_same, finset_sum_coeff]
        by_cases hj : j ∈ (R.coeff k).support
        · rw [Finset.sum_eq_single j]
          · rw [Polynomial.coeff_monomial_same, finset_sum_coeff]
            by_cases hi : i ∈ ((R.coeff k).coeff j).support
            · rw [Finset.sum_eq_single i]
              · rw [Polynomial.coeff_monomial_same]
              · intro i' _ hne; simp [Polynomial.coeff_monomial, hne]
              · intro h; exact absurd hi h
            · rw [Finset.sum_eq_zero]
              · apply halg_inj; rw [← hpC, map_zero, not_not.mp (Polynomial.mem_support_iff.not.mp hi), mul_zero]
              · intro i' hi'; simp [Polynomial.coeff_monomial, show i' ≠ i from fun h => hi (h ▸ hi')]
          · intro j' _ hne; simp [Polynomial.coeff_monomial, hne]
          · intro h; exact absurd hj h
        · rw [Finset.sum_eq_zero]
          · rw [Polynomial.coeff_zero]; apply halg_inj
            rw [← hpC, map_zero, not_not.mp (Polynomial.mem_support_iff.not.mp hj), Polynomial.coeff_zero, mul_zero]
          · intro j' hj'; simp [Polynomial.coeff_monomial, show j' ≠ j from fun h => hj (h ▸ hj')]
      · intro k' _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd hk h
    · rw [Finset.sum_eq_zero]
      · rw [Polynomial.coeff_zero, Polynomial.coeff_zero]; apply halg_inj
        rw [← hpC, map_zero, not_not.mp (Polynomial.mem_support_iff.not.mp hk), Polynomial.coeff_zero, Polynomial.coeff_zero, mul_zero]
      · intro k' hk'; simp [Polynomial.coeff_monomial, show k' ≠ k from fun h => hk (h ▸ hk')]
  exact clearAll R

theorem true_polynomial_multiple {F G : ContactPoly (Polynomial Fld)} (hirr : Irreducible F)
    (hR : 0<F.natDegree) (hdiv : liftCRat F ∣ liftCRat G) : F ∣ G := by
  obtain ⟨C,hC⟩ := hdiv
  obtain ⟨d,H,hd,h⟩ := clear_seed_denominators C
  have hmap : liftCRat (cC d) = cC (algebraMap (Polynomial Fld) (RatFunc Fld) d) := by
    unfold liftCRat liftBiRat cC; simp [Polynomial.map_C]
  have he : cC d * G = F * H := by
    apply liftCRat_injective
    rw [map_mul,map_mul,hmap,hC,←h]; ring
  have hp : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have no : ¬F ∣ cC d := by
    intro hh
    have hn : (cC d : ContactPoly (Polynomial Fld)) ≠ 0 := by
      unfold cC; exact C_ne_zero.mpr (C_ne_zero.mpr (C_ne_zero.mpr hd))
    have hl := natDegree_le_of_dvd hh hn
    simp [cC] at hl
    omega
  exact (hp.dvd_or_dvd (show F ∣ cC d*G from ⟨H,he⟩)).resolve_left no

/-- A multiple in the generic seed field consumes the seed degree of F
in the actual polynomial space used by the dimension argument. -/
theorem bounded_cofactor {F G : ContactPoly (Polynomial Fld)} (hirr : Irreducible F)
    (hR : 0<F.natDegree) (hn : G≠0) (dF : contactDeriv F=0) (dG : contactDeriv G=0)
    (q T w W s : ℕ) (hs : G.natDegree≤s) (hw : wdeg w G≤W) (hm : mixed q G≤T)
    (hdiv : liftCRat F ∣ liftCRat G) :
    ∃ H, G=F*H ∧ contactDeriv H=0 ∧ H.natDegree≤s-F.natDegree ∧
      wdeg w H≤W-wdeg w F ∧ mixed q H≤T-mixed q F := by
  obtain ⟨H,rfl⟩ := true_polynomial_multiple hirr hR hdiv
  have hH : H≠0 := right_ne_zero_of_mul hn
  rw [contactDeriv_mul,dF,zero_mul,zero_add] at dG
  rw [natDegree_mul hirr.ne_zero hH] at hs
  rw [wdeg_mul w hirr.ne_zero hH] at hw
  exact ⟨H,rfl,(mul_eq_zero.mp dG).resolve_left hirr.ne_zero,by omega,by omega,
    cofactor_cap q T hirr.ne_zero hH hm⟩

#print axioms bounded_cofactor
end ProximityPrize.SubmissionBinaryLower.B6402Cofactor
