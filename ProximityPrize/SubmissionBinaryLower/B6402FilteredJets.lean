import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp

/-! Refine the global interpolation of PR 694 by retaining the seed degree of
each local normal-form coefficient. All polynomial spaces below are the ones
in the promoted binary submission, with its original Lean 4.36 toolchain. -/

namespace ProximityPrize.SubmissionBinaryLower.B6402FilteredJets

open Polynomial B6401ContactKerD B6401QuotInterp
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

def localWeight (e : ℕ × ℕ × ℕ × ℕ) : ℕ := e.1 + e.2.1 + 2*e.2.2.2

theorem reduction_preserves_weight (m s q j a b : ℕ) (idx : LocalBasisIdx m s)
    (hn : reduceMonomialCoords m s q j a b idx ≠ 0) :
    localWeight idx.1 = q+j+2*b := by
  induction a generalizing q j b with
  | zero =>
    simp only [reduceMonomialCoords] at hn
    split at hn
    · rename_i h; rw [h]; rfl
    · contradiction
  | succ a ih =>
    simp only [reduceMonomialCoords] at hn
    split at hn
    · contradiction
    · split at hn
      · dsimp only at hn
        split at hn
        · rename_i h; rw [h]; rfl
        · contradiction
      · dsimp only at hn
        by_cases h : reduceMonomialCoords m s q (j-2) a (b+1) idx = 0
        · rw [h, zero_add] at hn
          have := ih _ _ _ hn
          omega
        · have := ih _ _ _ h
          omega

private theorem graded_tail {F : Type*} [Field F] (m s k r a' b' : ℕ)
    (idx : LocalBasisIdx m s) (x0 : F) (y0 : Polynomial F) (hy : y0.natDegree ≤ 1)
    (hr : r < 2) :
    let t : Polynomial F := if r = 0 then
        ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : Polynomial F)
      else y0 * ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : Polynomial F) +
        C x0 * ((reduceMonomialCoords m s 0 (k+1) a' b' idx : ℕ) : Polynomial F) +
        ((reduceMonomialCoords m s 1 k a' b' idx : ℕ) : Polynomial F)
    t ≠ 0 → t.natDegree + localWeight idx.1 ≤ k+r+2*b' := by
  dsimp only
  have hconst (n : ℕ) : ((n : ℕ) : Polynomial F).natDegree = 0 := natDegree_natCast n
  by_cases h0 : r = 0
  · simp only [h0, ↓reduceIte]
    intro hn
    have hn' : reduceMonomialCoords m s 0 k a' b' idx ≠ 0 := by
      intro h; simp [h] at hn
    rw [hconst, reduction_preserves_weight _ _ _ _ _ _ _ hn']
    omega
  · simp only [h0, ↓reduceIte]
    intro hn
    by_cases h : reduceMonomialCoords m s 0 k a' b' idx = 0
    · rw [h] at hn ⊢
      simp only [Nat.cast_zero, mul_zero, zero_add] at hn ⊢
      have hw : localWeight idx.1 = k+1+2*b' := by
        by_cases h' : reduceMonomialCoords m s 0 (k+1) a' b' idx = 0
        · rw [h'] at hn
          simp only [Nat.cast_zero, mul_zero, zero_add] at hn
          have hh : reduceMonomialCoords m s 1 k a' b' idx ≠ 0 := by
            intro hh; simp [hh] at hn
          have := reduction_preserves_weight _ _ _ _ _ _ _ hh
          omega
        · simpa using reduction_preserves_weight _ _ _ _ _ _ _ h'
      have hdeg := natDegree_add_le
        (C x0 * (reduceMonomialCoords m s 0 (k+1) a' b' idx : Polynomial F))
        (reduceMonomialCoords m s 1 k a' b' idx : Polynomial F)
      have hmul := natDegree_mul_le (p := C x0)
        (q := (reduceMonomialCoords m s 0 (k+1) a' b' idx : Polynomial F))
      simp only [natDegree_C, natDegree_natCast, zero_add, Nat.max_zero] at hdeg hmul
      omega
    · have hw := reduction_preserves_weight _ _ _ _ _ _ _ h
      have hd : (y0 * (reduceMonomialCoords m s 0 k a' b' idx : Polynomial F) +
          C x0 * (reduceMonomialCoords m s 0 (k+1) a' b' idx : Polynomial F) +
          (reduceMonomialCoords m s 1 k a' b' idx : Polynomial F)).natDegree ≤ 1 := by
        refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
          · exact natDegree_mul_le.trans (by simp_all)
          · exact natDegree_mul_le.trans (by simp)
        · simp
      omega

theorem localNF_degree {F : Type*} [Field F] {wY W s m : ℕ} (hwY : 1 ≤ wY)
    (x0 : F) (y0 : Polynomial F) (hy : y0.natDegree ≤ 1)
    (e : KerDIdx wY W s) (idx : LocalBasisIdx m s)
    (hne : kerDLocalNF m s (C x0) y0 e.1 idx ≠ 0) :
    (kerDLocalNF m s (C x0) y0 e.1 idx).natDegree + (localWeight idx.1 - s)
      ≤ 2*e.1.2.2.1+e.1.2.1 := by
  have plain := natDegree_kerDLocalNF_le_exact (dy := 1) hwY x0 y0 hy e idx
  simp only [one_mul] at plain
  by_cases hsmall : localWeight idx.1 ≤ s
  · omega
  rcases e with ⟨⟨k,r,b,a⟩, hem⟩
  have hm := (mem_kerDIdxFinset_iff wY W s hwY k r b a).mp hem
  dsimp only at plain ⊢
  let term (i j : ℕ) := (Nat.choose a i : Polynomial F) * (C x0 ^ 2) ^ (a-i) *
    ((Nat.choose b j : Polynomial F) * (y0^2)^(b-j)) *
    (if r = 0 then ((reduceMonomialCoords m s 0 k i j idx : ℕ) : Polynomial F)
     else y0 * ((reduceMonomialCoords m s 0 k i j idx : ℕ) : Polynomial F) +
       C x0 * ((reduceMonomialCoords m s 0 (k+1) i j idx : ℕ) : Polynomial F) +
       ((reduceMonomialCoords m s 1 k i j idx : ℕ) : Polynomial F))
  change (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1), term i j) ≠ 0 at hne
  change (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1), term i j).natDegree + _ ≤ _
  have ht (i j : ℕ) (hj : j ≤ b) (hn : term i j ≠ 0) :
      (term i j).natDegree + localWeight idx.1 ≤ k+r+2*b := by
    unfold term at hn ⊢
    have htail := graded_tail m s k r i j idx x0 y0 hy hm.1 (right_ne_zero_of_mul hn)
    have hC : (((a.choose i : Polynomial F) * (C x0 ^ 2) ^ (a-i))).natDegree = 0 := by
      have heq : ((a.choose i : Polynomial F) * (C x0 ^ 2) ^ (a-i)) =
          C ((a.choose i : F) * (x0 ^ 2) ^ (a-i)) := by simp
      rw [heq,natDegree_C]
    have hy' : ((b.choose j : Polynomial F) * (y0^2)^(b-j)).natDegree ≤ 2*(b-j) := by
      apply natDegree_mul_le.trans
      simp only [natDegree_natCast, zero_add]
      apply natDegree_pow_le.trans
      have hh := natDegree_pow_le (p := y0) (n := 2)
      nlinarith [Nat.mul_le_mul_left (b-j) (show (y0^2).natDegree ≤ 2 by omega)]
    have hp := natDegree_mul_le (p := (a.choose i : Polynomial F) * (C x0 ^ 2) ^ (a-i))
      (q := (b.choose j : Polynomial F) * (y0^2)^(b-j))
    exact (Nat.add_le_add_right natDegree_mul_le _).trans (by omega)
  obtain ⟨i,hi,his⟩ : ∃ i ∈ Finset.range (a+1), (∑ j ∈ Finset.range (b+1), term i j) ≠ 0 := by
    by_contra! hn; exact hne (Finset.sum_eq_zero hn)
  obtain ⟨j,hj,hjs⟩ : ∃ j ∈ Finset.range (b+1), term i j ≠ 0 := by
    by_contra! hn; exact his (Finset.sum_eq_zero hn)
  have one := ht i j (by simpa using hj) hjs
  have hsum : (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1), term i j).natDegree ≤
      k+r+2*b-localWeight idx.1 := by
    refine (natDegree_sum_le _ _).trans (Finset.sup_le fun x _ => ?_)
    refine (natDegree_sum_le _ _).trans (Finset.sup_le fun y hy' => ?_)
    by_cases hn : term x y = 0
    · simp [hn]
    · have := ht x y (by simpa using hy') hn
      dsimp only [Function.comp_apply]
      omega
  omega

/-- Adapted from PR 694's weighted interpolation theorem. Each local coordinate
only contributes coefficients up to its own possible seed degree. -/
theorem exists_global_contact_interpolant_filtered {F ι : Type*} [Field F] [CharP F 2] [Fintype ι]
    (x : ι → F) (y : ι → Polynomial F) {wY W0 s0 m0 D_ZF : ℕ}
    (hwY : 1 ≤ wY) (hy : ∀ i, (y i).natDegree ≤ 1)
    (hD_ge : W0 / wY ≤ D_ZF)
    (hloc : ∀ idx : LocalBasisIdx m0 s0, localWeight idx.1 - s0 ≤ D_ZF)
    (hsurplus : Fintype.card ι * (∑ idx ∈ localBasisFinset m0 s0, (D_ZF+1-(localWeight idx-s0))) + yWeightSum wY W0 s0 <
      varsKerDExact wY W0 s0 * (D_ZF + 1)) :
    ∃ (Q : ContactPoly (Polynomial F)) (f_coord : KerDIdx wY W0 s0 → Polynomial F),
      Q = ∑ e : KerDIdx wY W0 s0, cC (f_coord e) * kerDBasisPoly e.1 ∧
      Q ≠ 0 ∧ contactDeriv Q = 0 ∧ Q.natDegree ≤ s0 ∧ wdeg wY Q ≤ W0 ∧
      wYZ 1 Q ≤ D_ZF ∧
      (∀ e : KerDIdx wY W0 s0, (f_coord e).natDegree + (2 * e.1.2.2.1 + e.1.2.1) ≤ D_ZF) ∧
      ∀ i : ι, twOrdGE (∑ e : KerDIdx wY W0 s0, locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1) m0 := by
  classical
  let cap (e : KerDIdx wY W0 s0) : ℕ := D_ZF + 1 - (2 * e.1.2.2.1 + e.1.2.1)
  have hbr_le : ∀ e : KerDIdx wY W0 s0, (2 * e.1.2.2.1 + e.1.2.1) ≤ D_ZF := by
    intro ⟨⟨k, r, b, a⟩, he⟩
    have hmem := (mem_kerDIdxFinset_iff wY W0 s0 (by omega) k r b a).mp he
    have h1 : (2 * b + r) * wY ≤ W0 := by nlinarith [hmem.2.2]
    have h2 : 2 * b + r ≤ W0 / wY := (Nat.le_div_iff_mul_le (by omega : 0 < wY)).mpr h1
    exact h2.trans hD_ge
  let I := Σ e : KerDIdx wY W0 s0, Fin (cap e)
  let rowCap (idx : LocalBasisIdx m0 s0) := D_ZF + 1 - (localWeight idx.1 - s0)
  let J := ι × (Σ idx : LocalBasisIdx m0 s0, Fin (rowCap idx))
  let cPoly (v : I → F) (e : KerDIdx wY W0 s0) : Polynomial F :=
    ∑ t : Fin (cap e), C (v ⟨e, t⟩) * X ^ t.val
  let L : (I → F) →ₗ[F] (J → F) :=
    { toFun := fun v j =>
        let i := j.1
        let idx := j.2.1
        let t := j.2.2
        (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx).coeff t.val
      map_add' := by
        intro v1 v2; funext ⟨i, idx, t⟩
        have hc : ∀ e, cPoly (v1 + v2) e = cPoly v1 e + cPoly v2 e := fun e => by
          dsimp [cPoly]; simp [add_mul, Finset.sum_add_distrib]
        simp only [hc, add_mul, Finset.sum_add_distrib, coeff_add, finset_sum_coeff, Pi.add_apply]
      map_smul' := by
        intro a v; funext ⟨i, idx, t⟩
        have hc : ∀ e, cPoly (a • v) e = C a * cPoly v e := fun e => by
          dsimp [cPoly]; simp [Finset.mul_sum, mul_assoc]
        simp only [hc, mul_assoc, ← Finset.mul_sum, finset_sum_coeff, coeff_C_mul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply] }
  have hcard : Fintype.card J < Fintype.card I := by
    have hI_eq : Fintype.card I + yWeightSum wY W0 s0 = varsKerDExact wY W0 s0 * (D_ZF + 1) := by
      simp only [I, Fintype.card_sigma, Fintype.card_fin]
      have hsum_y : yWeightSum wY W0 s0 = ∑ e : KerDIdx wY W0 s0, (2 * e.1.2.2.1 + e.1.2.1) := by
        unfold yWeightSum; rw [← Finset.sum_coe_sort]
      rw [hsum_y, ← Finset.sum_add_distrib]
      trans ∑ _e : KerDIdx wY W0 s0, (D_ZF + 1)
      · apply Finset.sum_congr rfl; intro e _
        have hle := hbr_le e
        dsimp [cap]; omega
      · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_kerDIdx wY W0 s0 (by omega)]
    have hJ : Fintype.card J = Fintype.card ι *
        (∑ idx ∈ localBasisFinset m0 s0, (D_ZF+1-(localWeight idx-s0))) := by
      simp only [J, Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin, rowCap]
      exact congrArg (Fintype.card ι * ·) (Finset.sum_coe_sort (localBasisFinset m0 s0) (fun idx => D_ZF+1-(localWeight idx-s0)))
    omega
  obtain ⟨v, hv_ne, hLv⟩ := exists_ne_zero_ker_linearMap L hcard
  let Q : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W0 s0, cC (cPoly v e) * kerDBasisPoly e.1
  have hQne : Q ≠ 0 := by
    intro hQ0; apply hv_ne; funext ⟨e, t⟩
    have hc0 : cPoly v e = 0 := by
      rcases e with ⟨⟨k, r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) k r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b)).coeff (2 * a)) hQ0
        dsimp only [Q] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_zero, coeff_zero, coeff_zero] at h
        simpa [he] using h
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b + 1)).coeff (2 * a)) hQ0
        dsimp only [Q] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_zero, coeff_zero, coeff_zero] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h
    have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc0
    dsimp only [cPoly] at ht; rw [finset_sum_coeff, coeff_zero, Finset.sum_eq_single t] at ht
    · simpa [coeff_C_mul, coeff_X_pow] using ht
    · intro t' _ hne; have : t'.val ≠ t.val := fun h => hne (Fin.ext h)
      simp [coeff_C_mul, coeff_X_pow, this.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQmem : contactDeriv Q = 0 ∧ Q.natDegree ≤ s0 ∧ wdeg wY Q ≤ W0 := by
    refine (mem_kerD_iff_exists_unique_coords hwY Q).mpr ⟨cPoly v, rfl, ?_⟩
    intro c' hc'; funext ⟨⟨k, r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) k r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b)).coeff (2 * a)) hc'
      dsimp only [Q] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      simpa [he] using h.symm
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b + 1)).coeff (2 * a)) hc'
      dsimp only [Q] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h.symm
  have hc_wtd : ∀ e : KerDIdx wY W0 s0, (cPoly v e).natDegree + (2 * e.1.2.2.1 + e.1.2.1) ≤ D_ZF := by
    intro e
    have hle := hbr_le e
    have hdeg : (cPoly v e).natDegree ≤ D_ZF - (2 * e.1.2.2.1 + e.1.2.1) := by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ => ?_)
      have ht := t.isLt; dsimp [cap] at ht
      exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    omega
  have hwQ : wYZ 1 Q ≤ D_ZF := wYZ_sum_kerDBasisPoly_le (by omega) (cPoly v) (fun e _ => by simpa using hc_wtd e)
  refine ⟨Q, cPoly v, rfl, hQne, hQmem.1, hQmem.2.1, hQmem.2.2, hwQ, hc_wtd, ?_⟩
  intro i
  have hNF0 : ∀ idx : LocalBasisIdx m0 s0,
      (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) = 0 := by
    intro idx
    have hdeg : (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx).natDegree ≤
        D_ZF - (localWeight idx.1 - s0) := by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
      dsimp only [Function.comp_apply]
      by_cases hn : kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx = 0
      · simp [hn]
      · have h1 := hc_wtd e
        have h2 := localNF_degree hwY (x i) (y i) (hy i) e idx hn
        exact natDegree_mul_le.trans (by omega)
    ext t; rw [coeff_zero]
    by_cases ht : t < rowCap idx
    · exact congrFun hLv (i, ⟨idx, ⟨t, ht⟩⟩)
    · have := hloc idx; dsimp only [rowCap] at ht
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hEq : (∑ e : KerDIdx wY W0 s0, locC (cPoly v e) * kerDLocalPoly (C (x i)) (y i) e.1) =
      ∑ e : KerDIdx wY W0 s0, locC (cPoly v e) *
        (kerDLocalPoly (C (x i)) (y i) e.1 -
          ∑ idx : LocalBasisIdx m0 s0, locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) := by
    have hzero : (∑ e : KerDIdx wY W0 s0, locC (cPoly v e) *
        ∑ idx : LocalBasisIdx m0 s0, locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) = 0 := by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro idx _
      have hsum : (∑ e : KerDIdx wY W0 s0, locC (cPoly v e) *
            (locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1)) =
          locC (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) *
            localBasisElem idx.1 := by
        rw [show locC (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) =
              ∑ e : KerDIdx wY W0 s0, locC (cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx)
              from by unfold locC; simp [map_sum], Finset.sum_mul]
        apply Finset.sum_congr rfl; intro e _; unfold locC; simp [map_mul, mul_assoc]
      rw [hsum, hNF0 idx]; simp [locC]
    rw [← sub_zero (G := LocalPoly (Polynomial F)) (∑ e : KerDIdx wY W0 s0, _), ← hzero,
      ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
    apply Finset.sum_congr rfl; intro e _
    have hms : ∀ a b c : LocalPoly (Polynomial F), a * (b - c) = a * b - a * c := fun a b c =>
      eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
    exact (hms _ _ _).symm
  rw [hEq]; apply twOrdGE_sum; intro e _
  have hmem := (mem_kerDIdxFinset_iff wY W0 s0 (by omega) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
  simpa using twOrdGE_mul (twOrdGE_zero _)
    (twOrdGE_kerDLocalPoly_sub_NF m0 s0 (C (x i)) (y i) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)


theorem seed1811_surplus :
    2097152 * (∑ idx ∈ localBasisFinset 9 2, (1811+1-(localWeight idx-2))) +
      yWeightSum 1048575 (2*1482750*9-1) 2 <
      varsKerDExact 1048575 (2*1482750*9-1) 2 * (1811+1) := by
  rw [yWeightSum_eq_closed 1048575 (2*1482750*9-1) 2 (by decide)]
  have rows : (∑ idx ∈ localBasisFinset 9 2, (1811+1-(localWeight idx-2))) = 359724 := by decide
  rw [rows]
  norm_num [varsKerDExact,yWeightSumClosed,yWeightSumBlock,Finset.sum_range_succ,Finset.sum_range_zero]

/-- One global polynomial for every receiver, including all legal witnesses with
at least 1,482,750 matches. The source and target use the promoted formal basis. -/
theorem initial_interpolant_6402 {F ι : Type*} [Field F] [CharP F 2] [Fintype ι] [DecidableEq ι]
    (hN : Fintype.card ι = 2097152) (x : ι ↪ F) (y : ι → Polynomial F)
    (hy : ∀ i, (y i).natDegree ≤ 1) :
    ∃ Q : ContactPoly (Polynomial F), Q ≠ 0 ∧ contactDeriv Q = 0 ∧
      Q.natDegree ≤ 2 ∧ wdeg 1048575 Q ≤ 26689499 ∧ wYZ 1 Q ≤ 1811 ∧
      ∀ (z : F) (P : Polynomial F) (S : Finset ι), P.natDegree ≤ 1048575 →
        1482750 ≤ S.card → (∀ i ∈ S, P.eval (x i) = (y i).eval z) →
        evalContact (evalZContact Q z) P = 0 := by
  have localCap (idx : LocalBasisIdx 9 2) : localWeight idx.1-2 ≤ 1811 := by
    rcases idx with ⟨⟨q,j,a,b⟩,h⟩
    have hh := (mem_localBasisFinset_iff 9 2 q j a b).mp h
    dsimp [localWeight]
    omega
  obtain ⟨Q,c,hQ,hn,hD,hR,hW,hYZ,_,hv⟩ :=
    exists_global_contact_interpolant_filtered (wY := 1048575) (W0 := 2*1482750*9-1) (D_ZF := 1811)
      (s0 := 2) (m0 := 9) x y (by decide) hy (by decide) localCap (by simpa only [hN] using seed1811_surplus)
  refine ⟨Q,hn,hD,hR,hW,hYZ,?_⟩
  intro z P S hP hS hfit
  rw [hQ]
  exact evalContact_eq_zero_of_global_coords x y (by decide) (by decide : 26689499 < 2*1482750*9)
    c hv z P hP S hS hfit

#print axioms initial_interpolant_6402
end ProximityPrize.SubmissionBinaryLower.B6402FilteredJets
