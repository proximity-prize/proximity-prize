import ProximityPrize.SubmissionBinaryLower.B6402ProductJets

/-! The refined number of seed coefficients suffices for the full primary
local congruence. Adapted from the normal-form argument in PR 694. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402PrimaryContact
open Polynomial B6401ContactKerD B6401QuotInterp B6402FilteredJets B6402ProductJets
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {K : Type*} [Field K] [CharP K 2]

theorem congruence_of_filtered_rows {wY W W_F d m s k dy H T : ℕ}
    (hwY : 0<wY) (hd : d≤s) (x : K) (y : K[X]) (hy : y.natDegree≤dy) (ht : H≤T)
    (f_coord : KerDIdx wY W_F d → K[X]) (g : KerDIdx wY W s → K[X])
    (v : LocalBasisIdx (m-k) (s-d) → K[X])
    (hf : B6402MixedDegree.mixed dy (∑ e : KerDIdx wY W_F d, cC (f_coord e)*kerDBasisPoly e.1) ≤ H)
    (hg : ∀ e : KerDIdx wY W s, Fits (g e) (dy*(2*e.1.2.2.1+e.1.2.1+e.1.1)) T)
    (hv : ∀ i, Fits (v i) (dy*localWeight i.1) (T-H))
    (tested : ∀ idx : LocalBasisIdx m s, ∀ n, n + dy*localWeight idx.1 ≤ T →
       ((∑ e : KerDIdx wY W s, g e*kerDLocalNF m s (C x) y e.1 idx) -
         ∑ j : LocalBasisIdx (m-k) (s-d), v j*prodLocalNF (C x) y f_coord j.1 idx).coeff n = 0) :
    twOrdGE ((∑ e : KerDIdx wY W s, locC (g e) * kerDLocalPoly (C x) y e.1) -
        (∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (C x) y e.1) *
        (∑ j : LocalBasisIdx (m-k) (s-d), locC (v j)*localBasisElem j.1)) m := by
  classical
  have hNF_zero (idx : LocalBasisIdx m s) :
      (∑ e : KerDIdx wY W s, g e*kerDLocalNF m s (C x) y e.1 idx) -
        (∑ j : LocalBasisIdx (m-k) (s-d), v j*prodLocalNF (C x) y f_coord j.1 idx) = 0 := by
    by_contra hn
    have cap := primary_row_degree hwY x y hy ht f_coord g v hf hg hv idx hn
    have hz := tested idx _ cap
    rw [coeff_natDegree] at hz
    exact (leadingCoeff_ne_zero.mpr hn) hz
  have h1 : twOrdGE ((∑ e : KerDIdx wY W s, locC (g e) * kerDLocalPoly (C x) y e.1) -
      ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s, g e * kerDLocalNF m s (C x) y e.1 idx) *
        localBasisElem idx.1) m := by
    have hrew : (∑ e : KerDIdx wY W s, locC (g e) * kerDLocalPoly (C x) y e.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s, g e * kerDLocalNF m s (C x) y e.1 idx) *
          localBasisElem idx.1 =
        ∑ e : KerDIdx wY W s, locC (g e) *
          (kerDLocalPoly (C x) y e.1 -
            ∑ idx : LocalBasisIdx m s, locC (kerDLocalNF m s (C x) y e.1 idx) * localBasisElem idx.1) := by
      simp_rw [locC, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm, ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial K))]
      apply Finset.sum_congr rfl; intro e _
      have hms : ∀ a b c : LocalPoly (Polynomial K), a * (b - c) = a * b - a * c := fun a b c =>
        eq_sub_of_add_eq (G := LocalPoly (Polynomial K)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial K))])
      rw [hms]; congr 1
      refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
      simp only [map_mul, mul_assoc]
    rw [hrew]; apply twOrdGE_sum; intro e _
    have hmem := (mem_kerDIdxFinset_iff wY W s (by omega) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    simpa using twOrdGE_mul (twOrdGE_zero _)
      (twOrdGE_kerDLocalPoly_sub_NF m s (C x) y e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)
  have h2 : twOrdGE ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C x) y e1.1) *
      (∑ b : LocalBasisIdx (m - k) (s - d), locC (v b) * localBasisElem b.1) -
      ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k) (s - d),
        v b * prodLocalNF (C x) y f_coord b.1 idx) * localBasisElem idx.1) m := by
    have hrew : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C x) y e1.1) *
        (∑ b : LocalBasisIdx (m - k) (s - d), locC (v b) * localBasisElem b.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k) (s - d),
          v b * prodLocalNF (C x) y f_coord b.1 idx) * localBasisElem idx.1 =
        ∑ b : LocalBasisIdx (m - k) (s - d), locC (v b) *
          ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C x) y e1.1) * localBasisElem b.1 -
            ∑ idx : LocalBasisIdx m s, locC (prodLocalNF (C x) y f_coord b.1 idx) * localBasisElem idx.1) := by
      have h2a : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C x) y e1.1) *
          (∑ b : LocalBasisIdx (m - k) (s - d), locC (v b) * localBasisElem b.1) =
          ∑ b : LocalBasisIdx (m - k) (s - d),
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C x) y e1.1) *
            (locC (v b) * localBasisElem b.1) := Finset.mul_sum _ _ _
      have h2b : (∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k) (s - d),
            v b * prodLocalNF (C x) y f_coord b.1 idx) * localBasisElem idx.1) =
          ∑ b : LocalBasisIdx (m - k) (s - d), ∑ idx : LocalBasisIdx m s,
            locC (v b * prodLocalNF (C x) y f_coord b.1 idx) * localBasisElem idx.1 := by
        trans ∑ idx : LocalBasisIdx m s, ∑ b : LocalBasisIdx (m - k) (s - d),
            locC (v b * prodLocalNF (C x) y f_coord b.1 idx) * localBasisElem idx.1
        · apply Finset.sum_congr rfl; intro idx _; unfold locC; simp only [map_sum, Finset.sum_mul]
        · exact Finset.sum_comm
      rw [h2a, h2b, ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial K))]
      apply Finset.sum_congr rfl; intro b _
      have hms : ∀ a b' c : LocalPoly (Polynomial K), a * (b' - c) = a * b' - a * c := fun a b' c =>
        eq_sub_of_add_eq (G := LocalPoly (Polynomial K)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial K))])
      rw [hms]
      refine congrArg₂ (· - ·) (by rw [← mul_assoc, mul_comm _ (locC (v b)), mul_assoc]) ?_
      refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
      unfold locC; simp only [map_mul, mul_assoc]
    rw [hrew]; apply twOrdGE_sum; intro b _
    have hb := ((mem_localBasisFinset_iff (m - k) (s - d) _ _ _ _).mp b.2).1
    simpa using twOrdGE_mul (twOrdGE_zero _)
      (twOrdGE_prodLocal_sub_NF (by omega) hd (C x) y f_coord b.1 hb)
  have hNF_eq : (∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s,
      g e * kerDLocalNF m s (C x) y e.1 idx) * localBasisElem idx.1) =
      ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k) (s - d),
        v b * prodLocalNF (C x) y f_coord b.1 idx) * localBasisElem idx.1 := by
    apply Finset.sum_congr rfl; intro idx _; rw [sub_eq_zero.mp (hNF_zero idx)]
  have hcomb := twOrdGE_sub h1 h2
  rwa [hNF_eq, sub_sub_sub_cancel_right] at hcomb

/-- On the primary kernel the local multiplier is unique. This prevents
the local variables alone from accounting for a strict surplus. -/
theorem multiplier_unique {A : Type*} [CommRing A] [IsDomain A] {F : LocalPoly A}
    {m k s d : ℕ} (v : LocalBasisIdx (m-k) (s-d) → A)
    (hF : twOrdGE F k) (hexact : ∃ i j, i+j=k ∧ twCoeff F i j ≠ 0)
    (hprod : twOrdGE (F*(∑ j : LocalBasisIdx (m-k) (s-d), locC (v j)*localBasisElem j.1)) m) :
    ∀ j, v j=0 := by
  by_cases hk : k<m
  · apply localBasis_linearIndependent_mod (m-k) (s-d) v
    by_contra hn
    have bad := not_twOrdGE_mul_of_exact_ord hF hexact hn
    rw [Nat.add_sub_cancel' hk.le] at bad
    exact bad hprod
  · intro j
    have hm : m-k=0 := by omega
    have h := ((mem_localBasisFinset_iff (m-k) (s-d) _ _ _ _).mp j.2).2.1
    omega

#print axioms congruence_of_filtered_rows
#print axioms multiplier_unique
end ProximityPrize.SubmissionBinaryLower.B6402PrimaryContact
