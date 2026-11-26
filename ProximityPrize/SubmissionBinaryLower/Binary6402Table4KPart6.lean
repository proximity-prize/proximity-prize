import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart5
import ProximityPrize.SubmissionBinaryLower.Binary6402Table4Common
import ProximityPrize.SubmissionBinaryLower.Binary6402Table4NonK

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

/-!
# Table 4B (`K ≠ 0`, 84 branches) and Top-Level Table 4 Exhaustive Algebra Dichotomy

Proves:
1. `table4_K_sat`: for any `S : KerD45Syzygy D` with `S.P0 = 0` and `S.M21 ≠ 0`, `D` produces an
   exact `T4BBranch` (`rGt ∈ Bool`, `vCancel ∈ Bool`, `q1Case < 3`, `odeCase < 7`) and an explicit
   nonnegative `x : Fin 49 → ℚ` satisfying ALL rows of `B6402T4Rows.buildT4BRows br`!
2. `table4_algebra_dichotomy`: for ANY `D : KerD45Data`, EITHER `EscapeUZero D`, OR `D` satisfies
   one of the 36 Table 4A branches (`T4ABranch`) OR one of the 84 Table 4B branches (`T4BBranch`)!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402Table4K

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6402IntFarkas B6402T4Rows B6401Char2ODE B6402Table4Common B6402Table4NonK
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
namespace KerD45KData
variable {D : KerD45Data} {S : KerD45Syzygy D} (K : KerD45KData S)

/-- Master `ODE_fail` theorem (`zRaw c0 c1 Hrem Qpoly ≠ 0`): proves line 378–380 of `B6402T4Rows`! -/
theorem ode_fail_bound {c0 c1 : Fld} (hd1 : Ndom.derivative = C c0) (hd2 : hasse 2 Ndom = C c1)
    (hz : zRaw c0 c1 K.Hrem K.Qpoly ≠ 0) :
    4 * (S.p.natDegree : ℤ) - 4 * (S.D1.natDegree : ℤ) + 4 * (K.din2Cnt : ℤ) +
      4 * (K.d2k1UCnt : ℤ) + 4 * (K.dmLCnt : ℤ) + 5 * (K.d2k0Cnt : ℤ) -
      2 * (D.n0 : ℤ) - 2 * (D.n1 : ℤ) + 2 * (S.n1U : ℤ) + 2 * (D.n3 : ℤ) + 6 * (D.nt : ℤ) ≤
      (K.Hrem.natDegree : ℤ) + 2 * (K.N1.natDegree : ℤ) + 2 * ((D.gj 2).natDegree : ℤ) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  obtain ⟨Z_ode, hZ_eq⟩ := pow5_mul_sq_dvd_zRaw c0 c1 K.Hrem K.M0 K.N1 (D.gj 2)
  have hZ_ne : Z_ode ≠ 0 := by intro h0; apply hz; unfold Qpoly; rw [hZ_eq, h0, mul_zero]
  have hZ_deg := natDegree_zOde_pow5_le K.M0_ne K.N1_ne D.g2_ne_zero hZ_ne hZ_eq
  -- Sum over S_fin in E = AlgebraicClosure Fld!
  let S_fin : Finset E :=
    Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ∪
    ((sqrtPoly K.p1).map ι).roots.toFinset ∪ (Z_ode.map ι).roots.toFinset
  have hA1_ne : sqrtPoly K.p1 ≠ 0 := mt (sqrtPoly_eq_zero_iff K.p1).mp K.hp1_ne
  have hNdom_ne : Ndom ≠ 0 := by obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
  have hNdom_rm1 : ∀ i : Idx, Ndom.rootMultiplicity (BinaryIRSProfile.domain i) = 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h1, _⟩ := Ndom_decomp; exact h1
  have hNdom_ev : ∀ a : E, (Ndom.map ι).eval a = 0 ↔ ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hev⟩ := Ndom_decomp; exact hev
  have hd1E : (Ndom.map ι).derivative = C (ι c0) := by rw [derivative_map, hd1, Polynomial.map_C]
  have hd2E : hasse 2 (Ndom.map ι) = C (ι c1) := by
    rw [hasse_map_eq, hd2, Polynomial.map_C]
  have hdivE : zRaw (ι c0) (ι c1) (K.Hrem.map ι) ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * ((D.gj 2).map ι)) =
      (K.M0.map ι) ^ 5 * (K.N1.map ι) ^ 2 * (Z_ode.map ι) := by
    rw [show (K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * ((D.gj 2).map ι) = (K.M0 ^ 3 * K.N1 ^ 2 * D.gj 2).map ι by
      simp only [Polynomial.map_mul, Polynomial.map_pow]]
    rw [zRaw_map, hZ_eq]
    simp only [Polynomial.map_mul, Polynomial.map_pow]
  -- Pointwise lower bound on (Z_ode.map ι).rootMultiplicity a - (M0.map ι).rootMultiplicity a!
  let bonus : E → ℤ := fun a =>
    if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then
      let i := Classical.choose h
      4 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
      4 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
      4 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
      4 * (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
      5 * (if D.k i = 0 ∧ K.isD1 i then 1 else 0) -
      2 * (if D.k i = 0 then 1 else 0) -
      2 * (if D.k i = 1 then 1 else 0) +
      2 * (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
      2 * (if 3 ≤ D.k i then 1 else 0) + 6 * ((D.k i - 3 : ℕ) : ℤ)
    else 0
  have hpt : ∀ a ∈ S_fin,
      4 * (((sqrtPoly K.p1).map ι).rootMultiplicity a : ℤ) + bonus a ≤
        ((Z_ode.map ι).rootMultiplicity a : ℤ) - ((K.M0.map ι).rootMultiplicity a : ℤ) := fun a _ => by
    by_cases hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
    · rcases hdom with ⟨i, rfl⟩
      have hch : Classical.choose (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
      dsimp [bonus]; rw [dif_pos ⟨i, rfl⟩, hch]
      set y0 := D.y i
      let Uy0 : Fld[X] := S.p.comp (X ^ 2) * C y0 + S.R
      let U1_y0 : Fld[X] := S.D1 * K.p1.comp (X ^ 2) * C y0 + K.R1
      let R_raw : Fld[X] := S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 2 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
        Uy0 ^ 2 * D.gj 1
      have hid0 : K.Hrem * Ndom ^ 3 + (sqrtPoly K.p1) ^ 4 * (K.M0 ^ 3 * K.N1 ^ 2 * R_raw) = K.Qpoly * U1_y0 ^ 4 :=
        K.Hrem_Q_ode_fail_id y0
      have heqE : (K.Hrem.map ι) * (Ndom.map ι) ^ 3 + ((sqrtPoly K.p1).map ι) ^ 4 *
          ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * (R_raw.map ι)) =
          ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * ((D.gj 2).map ι)) * (U1_y0.map ι) ^ 4 := by
        have h := congrArg (Polynomial.map ι) hid0
        unfold Qpoly at h; simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] at h; exact h
      have hN1a : (Ndom.map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) = 1 := by
        rw [rootMultiplicity_map_eq]; exact hNdom_rm1 i
      have hbound := (rootMultiplicity_zOde_ge
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.M0_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr hZ_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne)
        hd1E hd2E hdivE heqE (ι (BinaryIRSProfile.domain i))).2 hN1a
      have hM0_rm : (K.M0.map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) =
          if D.k i = 0 ∨ ¬ S.isU0 i then 1 else 0 := by
        unfold M0; rw [linProd_rm]
        have hm : (∃ j ∈ K.I_M0, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) ↔ i ∈ K.I_M0 :=
          ⟨fun ⟨j, hj, heq⟩ => by rwa [BinaryIRSProfile.domain.injective (ι.injective heq)], fun hi => ⟨i, hi, rfl⟩⟩
        rw [if_congr hm rfl rfl]
        have hm2 : i ∈ K.I_M0 ↔ D.k i = 0 ∨ ¬ S.isU0 i := by
          unfold I_M0; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
        rw [if_congr hm2 rfl rfl]
      have hN1_rm : (K.N1.map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) =
          if (D.k i = 1 ∧ S.isU0 i) ∨ (K.isML i ∧ K.isD1 i) then 1 else 0 := by
        unfold N1; rw [linProd_rm]
        have hm : (∃ j ∈ K.I_N1, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) ↔ i ∈ K.I_N1 :=
          ⟨fun ⟨j, hj, heq⟩ => by rwa [BinaryIRSProfile.domain.injective (ι.injective heq)], fun hi => ⟨i, hi, rfl⟩⟩
        rw [if_congr hm rfl rfl]
        have hm2 : i ∈ K.I_N1 ↔ (D.k i = 1 ∧ S.isU0 i) ∨ (K.isML i ∧ K.isD1 i) := by
          unfold I_N1; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
        rw [if_congr hm2 rfl rfl]
      have hR_ne : R_raw ≠ 0 := by
        intro h0
        have hid := zRaw_ode_fail_identity hd1 hd2 hid0
        have hz0 : zRaw c0 c1 0 (K.Qpoly * Ndom ^ 3) = 0 := by unfold zRaw hasse; simp
        rw [h0, mul_zero, hz0, mul_zero] at hid
        exact hz ((mul_eq_zero.mp hid).resolve_left (pow_ne_zero 9 hNdom_ne))
      have hR_rm_eq : (R_raw.map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) = R_raw.rootMultiplicity (BinaryIRSProfile.domain i) :=
        rootMultiplicity_map_eq _ _
      have hg2_rm_eq : ((D.gj 2).map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) = (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
        rootMultiplicity_map_eq _ _
      rw [hM0_rm, hN1_rm, hR_rm_eq, hg2_rm_eq] at hbound; rw [hM0_rm]
      have hd_R_of : ∀ m : ℕ, (X - C (BinaryIRSProfile.domain i)) ^ m ∣ R_raw → m ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) :=
        fun m hd => (le_rootMultiplicity_iff hR_ne).mpr hd
      have hd_g2_of : ∀ m : ℕ, (X - C (BinaryIRSProfile.domain i)) ^ m ∣ D.gj 2 → m ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
        fun m hd => (le_rootMultiplicity_iff D.g2_ne_zero).mpr hd
      have hd_Uy : S.isU0 i → X - C (BinaryIRSProfile.domain i) ∣ Uy0 := fun hU => by
        rw [dvd_iff_isRoot, IsRoot]; simpa [Uy0, y0, KerD45Syzygy.isU0, KerD45Syzygy.U_eval] using hU
      -- Case-split on k i = 0, 1, 2, ≥ 3!
      by_cases hk0 : D.k i = 0
      · have hnNorm : ¬ K.isNorm i := fun h => by have := h.1; omega
        have hnML : ¬ K.isML i := fun h => by have := h.1; omega
        by_cases hD1 : K.isD1 i
        · have hR3 : 3 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 3 (by
            have hD1d := dvd_iff_isRoot.mpr hD1
            apply dvd_add
            · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hD1d 4)) _) _
            · rw [pow_succ _ 2]
              exact mul_dvd_mul (pow_dvd_pow_of_dvd (hd_Uy (K.isU0_of_D1_zero hD1)) 2) (hD1d.trans (S.D1_dvd_gj 1)))
          have hg1 : 1 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
            hd_g2_of 1 (by rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2))
          simp only [hk0, hD1, hnNorm, hnML, show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 2 by omega,
            show ¬ (3 ≤ 0) by omega, Nat.sub_eq_zero_of_le (show 0 ≤ 3 by omega),
            true_or, or_true, false_or, or_false, false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
        · simp only [hk0, hD1, hnNorm, hnML, show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 2 by omega,
            show ¬ (3 ≤ 0) by omega, Nat.sub_eq_zero_of_le (show 0 ≤ 3 by omega),
            true_or, or_true, false_or, or_false, false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
      · by_cases hk1 : D.k i = 1
        · have hnNorm : ¬ K.isNorm i := fun h => by have := h.1; omega
          have hnML : ¬ K.isML i := fun h => by have := h.1; omega
          by_cases hU : S.isU0 i
          · by_cases hD1 : K.isD1 i
            · have hR3 : 3 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 3 (by
                have hD1d := dvd_iff_isRoot.mpr hD1
                apply dvd_add
                · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hD1d 4)) _) _
                · rw [pow_succ _ 2]
                  exact mul_dvd_mul (pow_dvd_pow_of_dvd (hd_Uy hU) 2) (hD1d.trans (S.D1_dvd_gj 1)))
              have hg1 : 1 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                hd_g2_of 1 (by rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2))
              simp only [hk1, hU, hD1, hnNorm, hnML, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 2 by omega,
                show ¬ (3 ≤ 1) by omega, Nat.sub_eq_zero_of_le (show 1 ≤ 3 by omega),
                not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
            · have hR1 : 1 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 1 (by
                apply dvd_add
                · exact dvd_mul_of_dvd_right (by have := K.pow_dvd_gsh0 i; rwa [hk1] at this) _
                · exact dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 1 ≤ 2)).trans (pow_dvd_pow_of_dvd (hd_Uy hU) 2)) _)
              simp only [hk1, hU, hD1, hnNorm, hnML, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 2 by omega,
                show ¬ (3 ≤ 1) by omega, Nat.sub_eq_zero_of_le (show 1 ≤ 3 by omega),
                not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
          · simp only [hk1, hU, hnNorm, hnML, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 2 by omega,
              show ¬ (3 ≤ 1) by omega, Nat.sub_eq_zero_of_le (show 1 ≤ 3 by omega),
              not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
              false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
        · by_cases hk2 : D.k i = 2
          · by_cases hU : S.isU0 i
            · by_cases hD1 : K.isD1 i
              · have hR3 : 3 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 3 (by
                  have hD1d := dvd_iff_isRoot.mpr hD1
                  apply dvd_add
                  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ (by omega : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hD1d 4)) _) _
                  · rw [pow_succ _ 2]
                    exact mul_dvd_mul (pow_dvd_pow_of_dvd (hd_Uy hU) 2) (hD1d.trans (S.D1_dvd_gj 1)))
                by_cases hn : K.isNorm i
                · have hg3 : 3 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                    hd_g2_of 3 (K.pow_dvd_g2_din i hn.1 hU hn.2.2.1 hn.2.2.2 hD1)
                  have hnML : ¬ K.isML i := fun h => h.2.2.2 hn.2.2.2
                  simp only [hk2, hU, hD1, hn, hnML, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                    show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega),
                    not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                    false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
                · have hmL : K.isML i := by
                    have hg0 := K.g2t_zero_of_D1_zero hD1
                    unfold isNorm at hn; unfold isML; exact ⟨by omega, hU, hg0, fun hM0 => hn ⟨by omega, hU, hg0, hM0⟩⟩
                  have hg1 : 1 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                    hd_g2_of 1 (by rw [pow_one]; exact (dvd_iff_isRoot.mpr hD1).trans (S.D1_dvd_gj 2))
                  simp only [hk2, hU, hD1, hn, hmL, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                    show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega),
                    not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                    false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
              · -- k=2, U=0, d2=0: p1(t_i) ≠ 0 so sqrtPoly p1 has rootMult 0, and M0 has rootMult 0!
                have ha0 : ((sqrtPoly K.p1).map ι).rootMultiplicity (ι (BinaryIRSProfile.domain i)) = 0 := by
                  rw [rootMultiplicity_sqrtPoly_map K.p1 K.hp1_ne, ← map_pow, rootMultiplicity_map_eq]
                  exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr (K.p1_ne_zero_of_isU0_D1_ne hU hD1))
                simp only [hk2, hU, hD1, ha0, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                  show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega),
                  not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                  false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
            · have hnNorm : ¬ K.isNorm i := fun h => hU h.2.1
              have hnML : ¬ K.isML i := fun h => hU h.2.1
              have hR2 : 2 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of 2 (by
                apply dvd_add
                · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 ≤ 2 * D.k i - 1)).trans (K.pow_dvd_gsh0 i)) _
                · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 ≤ 2 * (D.k i - 1))).trans (K.pow_dvd_g1_U1 i hU)) _)
              simp only [hk2, hU, hnNorm, hnML, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                show ¬ (3 ≤ 2) by omega, Nat.sub_eq_zero_of_le (show 2 ≤ 3 by omega),
                not_true_eq_false, not_false_eq_true, true_or, or_true, false_or, or_false,
                false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
          · have hk3 : 3 ≤ D.k i := by omega
            by_cases hU : S.isU0 i
            · have hR_ge : 2 * D.k i - 1 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of _ (by
                apply dvd_add
                · exact dvd_mul_of_dvd_right (K.pow_dvd_gsh0 i) _
                · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 2 + (2 * D.k i - 3))).trans
                    (by rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd (hd_Uy hU) 2) (K.pow_dvd_g1_U0 i)))
              have hg_ge : 2 * D.k i - 5 ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                hd_g2_of _ (D.pow_dvd_g2_of_k i)
              by_cases hML : K.isML i <;> by_cases hD1 : K.isD1 i <;>
                simp only [hk0, hk1, hk2, hk3, hU, hML, hD1, not_true_eq_false, not_false_eq_true,
                  true_or, or_true, false_or, or_false, false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢ <;>
                omega
            · have hnNorm : ¬ K.isNorm i := fun h => hU h.2.1
              have hnML : ¬ K.isML i := fun h => hU h.2.1
              have hR_ge : 2 * D.k i - 2 ≤ R_raw.rootMultiplicity (BinaryIRSProfile.domain i) := hd_R_of _ (by
                apply dvd_add
                · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 * D.k i - 2 ≤ 2 * D.k i - 1)).trans (K.pow_dvd_gsh0 i)) _
                · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : 2 * D.k i - 2 ≤ 2 * (D.k i - 1))).trans (K.pow_dvd_g1_U1 i hU)) _)
              have hg_ge : 2 * (D.k i - 2) ≤ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) :=
                hd_g2_of _ (K.pow_dvd_g2_U1 i hU)
              simp only [hk0, hk1, hk2, hk3, hU, hnNorm, hnML, not_true_eq_false, not_false_eq_true,
                true_or, or_true, false_or, or_false, false_and, and_false, and_true, true_and, ↓reduceIte] at hbound ⊢; omega
    · -- Outside domain: Ndom.eval a ≠ 0, M0.rootMultiplicity a = 0!
      dsimp [bonus]; rw [dif_neg hdom, add_zero]
      have hM0_0 : (K.M0.map ι).rootMultiplicity a = 0 := by
        unfold M0; rw [linProd_rm, if_neg (fun ⟨i, _, hi⟩ => hdom ⟨i, hi⟩)]
      have hNeval : (Ndom.map ι).eval a ≠ 0 := mt (hNdom_ev a).mp hdom
      let Uy0 : Fld[X] := S.p.comp (X ^ 2) * C (0 : Fld) + S.R
      let U1_y0 : Fld[X] := S.D1 * K.p1.comp (X ^ 2) * C (0 : Fld) + K.R1
      let R_raw : Fld[X] := S.D1 ^ 4 * K.p1.comp (X ^ 2) ^ 2 * (D.gj 0 + C ((0 : Fld) ^ 2) * D.gj 1 + C ((0 : Fld) ^ 4) * D.gj 2) +
        Uy0 ^ 2 * D.gj 1
      have hid0 : K.Hrem * Ndom ^ 3 + (sqrtPoly K.p1) ^ 4 * (K.M0 ^ 3 * K.N1 ^ 2 * R_raw) = K.Qpoly * U1_y0 ^ 4 :=
        K.Hrem_Q_ode_fail_id 0
      have heqE : (K.Hrem.map ι) * (Ndom.map ι) ^ 3 + ((sqrtPoly K.p1).map ι) ^ 4 *
          ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * (R_raw.map ι)) =
          ((K.M0.map ι) ^ 3 * (K.N1.map ι) ^ 2 * ((D.gj 2).map ι)) * (U1_y0.map ι) ^ 4 := by
        have h := congrArg (Polynomial.map ι) hid0
        unfold Qpoly at h; simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] at h; exact h
      have hbound := (rootMultiplicity_zOde_ge
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.M0_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.N1_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr hZ_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne)
        hd1E hd2E hdivE heqE a).1 hNeval
      rw [hM0_0]; omega
  -- Sum hpt over S_fin!
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
  have hA1_sum : (∑ a ∈ S_fin, (((sqrtPoly K.p1).map ι).rootMultiplicity a : ℤ)) = (S.p.natDegree : ℤ) - (S.D1.natDegree : ℤ) := by
    have h1 := sum_rootMultiplicity_map_eq_natDegree (sqrtPoly K.p1) hA1_ne S_fin (fun a ha => by simp [S_fin, ι, E, ha])
    rw [natDegree_sqrtPoly] at h1
    have hp := K.natDegree_p_eq
    have h1Z : (∑ a ∈ S_fin, (((sqrtPoly K.p1).map ι).rootMultiplicity a : ℤ)) = (K.p1.natDegree : ℤ) := by
      rw [hι]; exact_mod_cast h1
    omega
  have hZ_sum : (∑ a ∈ S_fin, ((Z_ode.map ι).rootMultiplicity a : ℤ)) = (Z_ode.natDegree : ℤ) := by
    rw [hι]; exact_mod_cast sum_rootMultiplicity_map_eq_natDegree Z_ode hZ_ne S_fin (fun a ha => by simp [S_fin, ι, E, ha])
  have hM0_sum : (∑ a ∈ S_fin, ((K.M0.map ι).rootMultiplicity a : ℤ)) = (K.M0.natDegree : ℤ) := by
    have hsub : (K.M0.map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin := fun a ha => by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots ((Polynomial.map_ne_zero_iff (algebraMap Fld (AlgebraicClosure Fld)).injective).mpr K.M0_ne)] at ha
      have hrm : (K.M0.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a ≠ 0 :=
        fun h0 => ((Polynomial.map_ne_zero_iff (algebraMap Fld (AlgebraicClosure Fld)).injective).mpr K.M0_ne) ((rootMultiplicity_eq_zero_iff.mp h0) ha)
      unfold M0 at hrm; rw [linProd_rm] at hrm; split_ifs at hrm with h
      · rcases h with ⟨i, _, rfl⟩; simp [S_fin, ι, E]
      · exact absurd rfl hrm
    rw [hι]; exact_mod_cast sum_rootMultiplicity_map_eq_natDegree K.M0 K.M0_ne S_fin hsub
  have hbon_sum : (∑ a ∈ S_fin, bonus a) =
      4 * (K.din2Cnt : ℤ) + 4 * (K.d2k1UCnt : ℤ) + 4 * (K.dmLCnt : ℤ) + 5 * (K.d2k0Cnt : ℤ) -
      2 * (D.n0 : ℤ) - 2 * (D.n1 : ℤ) + 2 * (S.n1U : ℤ) + 2 * (D.n3 : ℤ) + 6 * (D.nt : ℤ) := by
    let domImg : Finset E := Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i))
    have hdom_sub : domImg ⊆ S_fin := fun a ha => by rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩; simp [S_fin]
    rw [← Finset.sum_subset hdom_sub (fun a _ hna => by
      dsimp [bonus]; rw [dif_neg (fun ⟨i, hi⟩ => hna (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩))]),
      Finset.sum_image (fun i _ j _ h => BinaryIRSProfile.domain.injective (ι.injective h))]
    have hterm : ∀ i : Idx, bonus (ι (BinaryIRSProfile.domain i)) =
        4 * (if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
        4 * (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
        4 * (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
        4 * (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0) +
        5 * (if D.k i = 0 ∧ K.isD1 i then 1 else 0) -
        2 * (if D.k i = 0 then 1 else 0) -
        2 * (if D.k i = 1 then 1 else 0) +
        2 * (if D.k i = 1 ∧ S.isU0 i then 1 else 0) +
        2 * (if 3 ≤ D.k i then 1 else 0) + 6 * ((D.k i - 3 : ℕ) : ℤ) := fun i => by
      dsimp [bonus]; rw [dif_pos ⟨i, rfl⟩]
      have hch : Classical.choose (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
        BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
      rw [hch]
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
    simp only [dmLCnt, Nat.cast_add]; ring
  rw [hA1_sum, hbon_sum, hZ_sum, hM0_sum] at hsum
  omega

/-- Wronskian `W2a / W2b` degree bounds when `HK.derivative ≠ 0`! -/
theorem w2_degree_bounds {c0 : Fld} (hc0 : c0 ≠ 0) (hNdom_deg : Ndom.natDegree = N)
    (hd1 : Ndom.derivative = C c0) (hHK' : K.HK.derivative ≠ 0) :
    ((K.HK.natDegree < N + K.HK.derivative.natDegree) →
      N ≤ 2 * K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree - 4 * S.D1.natDegree ∧
      (K.M0eff.natDegree : ℤ) + 2 * (K.Lam1.natDegree : ℤ) + 10 * (S.p.natDegree : ℤ) -
        4 * (S.D1.natDegree : ℤ) - ((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ) ≤ (N : ℤ)) ∧
    ((N + K.HK.derivative.natDegree ≤ K.HK.natDegree) →
      N ≤ K.M0eff.natDegree + (D.gj 2).natDegree + K.g2rem.natDegree ∧
      (K.M0eff.natDegree : ℤ) + 2 * (K.Lam1.natDegree : ℤ) + 10 * (S.p.natDegree : ℤ) -
        4 * (S.D1.natDegree : ℤ) - ((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ) ≤ (N : ℤ)) := by
  have hwr := K.HK_wronskian hd1
  have hp1c := mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne
  have hLc := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
  have hNdom_ne : Ndom ≠ 0 := by obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
  have hRHS_ne : K.M0eff ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero))
      (pow_ne_zero 5 hp1c)) hLc
  have hW_ne : C c0 * K.HK + Ndom * K.HK.derivative ≠ 0 := by
    intro h0; apply hRHS_ne; rw [← hwr, h0, mul_zero]
  have hdeg_LHS : K.M0eff.natDegree + (D.gj 2).natDegree + K.g2rem.natDegree = 2 * K.SK.natDegree + K.HK.natDegree := by
    have h := congrArg Polynomial.natDegree K.HK_decomp
    rw [natDegree_mul (mul_ne_zero K.M0eff_ne D.g2_ne_zero) K.g2rem_ne,
      natDegree_mul K.M0eff_ne D.g2_ne_zero,
      natDegree_mul (pow_ne_zero 2 K.SK_ne) K.HK_ne, natDegree_pow] at h; exact h
  have hdeg_wr : 2 * K.SK.natDegree + (C c0 * K.HK + Ndom * K.HK.derivative).natDegree =
      2 * K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree - 4 * S.D1.natDegree := by
    have h := congrArg Polynomial.natDegree hwr
    rw [natDegree_mul (pow_ne_zero 2 K.SK_ne) hW_ne, natDegree_pow,
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c)) hLc,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c),
      natDegree_mul (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero),
      natDegree_pow, natDegree_pow, natDegree_pow, natDegree_comp_X_sq, natDegree_comp_X_sq] at h
    have hp := K.natDegree_p_eq; omega
  have hC_deg : (C c0 * K.HK).natDegree = K.HK.natDegree := by
    rw [natDegree_C_mul hc0]
  have hNH_deg : (Ndom * K.HK.derivative).natDegree = N + K.HK.derivative.natDegree := by
    rw [natDegree_mul hNdom_ne hHK', hNdom_deg]
  have hH'_lt : K.HK.derivative.natDegree < K.HK.natDegree := by
    have hpos : 0 < K.HK.natDegree := by
      by_contra h0; apply hHK'; rw [Polynomial.eq_C_of_natDegree_eq_zero (p := K.HK) (by omega), derivative_C]
    exact natDegree_derivative_lt (by omega)
  constructor
  · intro hlt
    have hW_deg : (C c0 * K.HK + Ndom * K.HK.derivative).natDegree = N + K.HK.derivative.natDegree := by
      rw [natDegree_add_eq_right_of_natDegree_lt (by rw [hC_deg, hNH_deg]; exact hlt), hNH_deg]
    omega
  · intro hge
    have hW_deg : (C c0 * K.HK + Ndom * K.HK.derivative).natDegree ≤ K.HK.natDegree :=
      (natDegree_add_le _ _).trans (max_le (by omega) (by omega))
    omega

end KerD45KData

/-! ### Part 4: Complete `K ≠ 0` (`T4BBranch`, 84 branches, `nv = 49`) Satisfaction Theorem -/

lemma row0A_2_vals :
    row0A_2[0]! = 2 ∧ row0A_2[1]! = 4 ∧ row0A_2[2]! = 0 ∧ row0A_2[3]! = -11 ∧ row0A_2[4]! = -4 ∧
    row0A_2[5]! = -10 ∧ row0A_2[6]! = 0 ∧ row0A_2[7]! = 11 ∧ row0A_2[8]! = 6 ∧ row0A_2[9]! = 6 ∧
    row0A_2[10]! = -4 ∧ row0A_2[11]! = 1 ∧ row0A_2[12]! = -2 ∧ row0A_2[13]! = 0 ∧ row0A_2[14]! = -2 := by
  decide

lemma row0C0_2_vals :
    row0C0_2[0]! = 2 ∧ row0C0_2[1]! = 7 ∧ row0C0_2[2]! = 0 ∧ row0C0_2[3]! = -8 ∧ row0C0_2[4]! = -10 ∧
    row0C0_2[5]! = -13 ∧ row0C0_2[6]! = 2 ∧ row0C0_2[7]! = 10 ∧ row0C0_2[8]! = 9 ∧ row0C0_2[9]! = 2 ∧
    row0C0_2[10]! = -16 ∧ row0C0_2[11]! = 2 ∧ row0C0_2[12]! = -5 ∧ row0C0_2[13]! = 0 ∧ row0C0_2[14]! = -5 := by
  decide

lemma row0C1_2_vals :
    row0C1_2[0]! = 2 ∧ row0C1_2[1]! = 3 ∧ row0C1_2[2]! = 0 ∧ row0C1_2[3]! = -8 ∧ row0C1_2[4]! = -2 ∧
    row0C1_2[5]! = -9 ∧ row0C1_2[6]! = 2 ∧ row0C1_2[7]! = 10 ∧ row0C1_2[8]! = 5 ∧ row0C1_2[9]! = 10 ∧
    row0C1_2[10]! = -16 ∧ row0C1_2[11]! = 2 ∧ row0C1_2[12]! = -1 ∧ row0C1_2[13]! = 0 ∧ row0C1_2[14]! = -1 := by
  decide

lemma rowC04_2_vals :
    rowC04_2[0]! = 8 ∧ rowC04_2[1]! = 8 ∧ rowC04_2[2]! = 0 ∧ rowC04_2[3]! = -8 ∧ rowC04_2[4]! = -8 ∧
    rowC04_2[5]! = -8 ∧ rowC04_2[6]! = 0 ∧ rowC04_2[7]! = 8 ∧ rowC04_2[8]! = 8 ∧ rowC04_2[9]! = 8 ∧
    rowC04_2[10]! = 0 ∧ rowC04_2[11]! = 8 ∧ rowC04_2[12]! = -4 ∧ rowC04_2[13]! = 0 ∧ rowC04_2[14]! = -4 := by
  decide

/-- Helper lemma to verify any `mkR15` row (`mode = 0, 1, 2`) from its exact integer bound! -/
lemma mkR15_eval_base (x : Fin 49 → ℚ) (v : Fin 48 → ℕ)
    (hx : ∀ (j : ℕ) (hj : j < 48), x ⟨j, by omega⟩ = (v ⟨j, hj⟩ : ℚ) / (N : ℚ))
    (am0 amb am1 am2 ak3 amL0 amu1 amuO alam adin admL adoth aL0 aa1 aLnoU : ℤ) :
    let base : List (Nat × Int) := [
      (0, cH (-am0)), (1, cH (-am0)), (18, cH (am0 - am1)), (26, cH (-amb)),
      (2, cH (-am2)), (19, cH am2), (3, cH (-am2)), (20, cH (am2 - ak3)),
      (27, cH (-amL0)), (34, cH (amL0 - admL + adoth)),
      (39, cH (amuO - amu1)), (29, cH (-amuO)),
      (16, cH (-alam)), (31, cH (adoth - adin)), (17, cH (aa1 - adoth)),
      (21, cH (-2 * aL0 + 2 * aLnoU)), (4, cH (-2 * aLnoU)), (9, cQ (-aa1))
    ]
    (base.map fun e => if hj : e.1 < 49 then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum =
      -2 * ((am0 : ℚ) * ((v ⟨0, by decide⟩ : ℚ) + (v ⟨1, by decide⟩ : ℚ) - (v ⟨18, by decide⟩ : ℚ)) +
        (amb : ℚ) * (v ⟨26, by decide⟩ : ℚ) + (am1 : ℚ) * (v ⟨18, by decide⟩ : ℚ) +
        (am2 : ℚ) * ((v ⟨2, by decide⟩ : ℚ) - (v ⟨19, by decide⟩ : ℚ) + (v ⟨3, by decide⟩ : ℚ) - (v ⟨20, by decide⟩ : ℚ)) +
        (ak3 : ℚ) * (v ⟨20, by decide⟩ : ℚ) +
        (amL0 : ℚ) * ((v ⟨27, by decide⟩ : ℚ) - (v ⟨34, by decide⟩ : ℚ)) +
        (amu1 : ℚ) * (v ⟨39, by decide⟩ : ℚ) +
        (amuO : ℚ) * ((v ⟨29, by decide⟩ : ℚ) - (v ⟨39, by decide⟩ : ℚ)) +
        (alam : ℚ) * (v ⟨16, by decide⟩ : ℚ) +
        (adin : ℚ) * (v ⟨31, by decide⟩ : ℚ) + (admL : ℚ) * (v ⟨34, by decide⟩ : ℚ) +
        (adoth : ℚ) * ((v ⟨17, by decide⟩ : ℚ) - (v ⟨31, by decide⟩ : ℚ) - (v ⟨34, by decide⟩ : ℚ)) +
        (aL0 : ℚ) * (2 * (v ⟨21, by decide⟩ : ℚ)) +
        (aa1 : ℚ) * ((v ⟨9, by decide⟩ : ℚ) / 2 - (v ⟨17, by decide⟩ : ℚ)) +
        (aLnoU : ℚ) * (2 * ((v ⟨4, by decide⟩ : ℚ) - (v ⟨21, by decide⟩ : ℚ)))) := by
  intro base
  have h0 := hx 0 (by decide); have h1 := hx 1 (by decide); have h2 := hx 2 (by decide)
  have h3 := hx 3 (by decide); have h4 := hx 4 (by decide); have h9 := hx 9 (by decide)
  have h16 := hx 16 (by decide); have h17 := hx 17 (by decide); have h18 := hx 18 (by decide)
  have h19 := hx 19 (by decide); have h20 := hx 20 (by decide); have h21 := hx 21 (by decide)
  have h26 := hx 26 (by decide); have h27 := hx 27 (by decide); have h29 := hx 29 (by decide)
  have h31 := hx 31 (by decide); have h34 := hx 34 (by decide); have h39 := hx 39 (by decide)
  simp only [base, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    show (0 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega,
    show (3 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
    show (16 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega,
    show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (21 : ℕ) < 49 by omega,
    show (26 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (29 : ℕ) < 49 by omega,
    show (31 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (39 : ℕ) < 49 by omega,
    ↓reduceDIte, h0, h1, h2, h3, h4, h9, h16, h17, h18, h19, h20, h21, h26, h27, h29, h31, h34, h39,
    cH_mul_div_N, cQ_mul_div_N]
  push_cast; ring

def t4bVec (v : Fin 48 → ℕ) (WF : ℕ) : Fin 49 → ℚ := fun j =>
  if hj : j.val < 48 then (v ⟨j.val, hj⟩ : ℚ) / (N : ℚ) else (WF : ℚ) / (wY : ℚ)

def r15Rhs (r2 : Array ℤ) (v : Fin 48 → ℕ) : ℤ :=
  r2[0]! * ((v ⟨0, by decide⟩ : ℤ) + (v ⟨1, by decide⟩ : ℤ) - (v ⟨18, by decide⟩ : ℤ)) + r2[1]! * (v ⟨26, by decide⟩ : ℤ) +
  r2[3]! * ((v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ)) + r2[4]! * (v ⟨20, by decide⟩ : ℤ) +
  r2[5]! * ((v ⟨27, by decide⟩ : ℤ) - (v ⟨34, by decide⟩ : ℤ)) + r2[6]! * (v ⟨39, by decide⟩ : ℤ) +
  r2[7]! * ((v ⟨29, by decide⟩ : ℤ) - (v ⟨39, by decide⟩ : ℤ)) + r2[8]! * (v ⟨16, by decide⟩ : ℤ) +
  r2[9]! * (v ⟨31, by decide⟩ : ℤ) + r2[10]! * (v ⟨34, by decide⟩ : ℤ) +
  r2[11]! * ((v ⟨17, by decide⟩ : ℤ) - (v ⟨31, by decide⟩ : ℤ) - (v ⟨34, by decide⟩ : ℤ)) +
  r2[12]! * (2 * (v ⟨21, by decide⟩ : ℤ)) + r2[14]! * (2 * ((v ⟨4, by decide⟩ : ℤ) - (v ⟨21, by decide⟩ : ℤ)))

theorem table4_K_rows_sat
    (br : T4BBranch) (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (v : Fin 48 → ℕ) (WF : ℕ)
    (hBS : let x := t4bVec v WF
           let (ubB, eqB) := baseT4Rows 48 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
           (∀ r ∈ ubB, RowSatLe x r) ∧ (∀ r ∈ eqB, RowSatEq x r))
    (heq_nat :
      (v ⟨44, by decide⟩ : ℤ) + (v ⟨45, by decide⟩ : ℤ) = (v ⟨31, by decide⟩ : ℤ) ∧
      (v ⟨46, by decide⟩ : ℤ) + (v ⟨47, by decide⟩ : ℤ) = (v ⟨34, by decide⟩ : ℤ) ∧
      (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + (v ⟨4, by decide⟩ : ℤ) + (v ⟨25, by decide⟩ : ℤ) = (v ⟨10, by decide⟩ : ℤ) ∧
      (v ⟨18, by decide⟩ : ℤ) + (v ⟨34, by decide⟩ : ℤ) = (v ⟨35, by decide⟩ : ℤ) ∧
      (v ⟨0, by decide⟩ : ℤ) + (v ⟨1, by decide⟩ : ℤ) - (v ⟨18, by decide⟩ : ℤ) + (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) = (v ⟨28, by decide⟩ : ℤ) ∧
      (v ⟨0, by decide⟩ : ℤ) + (v ⟨1, by decide⟩ : ℤ) + (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + (v ⟨26, by decide⟩ : ℤ) = (v ⟨37, by decide⟩ : ℤ) ∧
      (v ⟨19, by decide⟩ : ℤ) + (v ⟨20, by decide⟩ : ℤ) + (v ⟨26, by decide⟩ : ℤ) - (v ⟨27, by decide⟩ : ℤ) + (v ⟨29, by decide⟩ : ℤ) = (v ⟨13, by decide⟩ : ℤ) ∧
      2 * (v ⟨10, by decide⟩ : ℤ) + (v ⟨19, by decide⟩ : ℤ) + (v ⟨20, by decide⟩ : ℤ) - (v ⟨26, by decide⟩ : ℤ) + (v ⟨30, by decide⟩ : ℤ) = (v ⟨12, by decide⟩ : ℤ) ∧
      (v ⟨12, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) - 3 * (v ⟨19, by decide⟩ : ℤ) - 3 * (v ⟨20, by decide⟩ : ℤ) + 3 * (v ⟨34, by decide⟩ : ℤ) - (v ⟨35, by decide⟩ : ℤ) - (v ⟨36, by decide⟩ : ℤ) = 0 ∧
      (v ⟨33, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) + (v ⟨38, by decide⟩ : ℤ) = (v ⟨11, by decide⟩ : ℤ) ∧
      (v ⟨41, by decide⟩ : ℤ) + (v ⟨42, by decide⟩ : ℤ) + (v ⟨43, by decide⟩ : ℤ) = (v ⟨21, by decide⟩ : ℤ))
    (hub_nat1 :
      (v ⟨44, by decide⟩ : ℤ) + (v ⟨46, by decide⟩ : ℤ) ≤ (v ⟨19, by decide⟩ : ℤ) ∧
      (v ⟨45, by decide⟩ : ℤ) + (v ⟨47, by decide⟩ : ℤ) ≤ (v ⟨20, by decide⟩ : ℤ) ∧
      (v ⟨18, by decide⟩ : ℤ) ≤ (v ⟨1, by decide⟩ : ℤ) ∧
      (v ⟨19, by decide⟩ : ℤ) ≤ (v ⟨2, by decide⟩ : ℤ) ∧
      (v ⟨20, by decide⟩ : ℤ) ≤ (v ⟨3, by decide⟩ : ℤ) ∧
      (v ⟨21, by decide⟩ : ℤ) ≤ (v ⟨4, by decide⟩ : ℤ) ∧
      (v ⟨22, by decide⟩ : ℤ) ≤ (v ⟨18, by decide⟩ : ℤ) ∧
      (v ⟨22, by decide⟩ : ℤ) ≤ (v ⟨6, by decide⟩ : ℤ) ∧
      (v ⟨6, by decide⟩ : ℤ) - (v ⟨22, by decide⟩ : ℤ) - (v ⟨1, by decide⟩ : ℤ) + (v ⟨18, by decide⟩ : ℤ) ≤ 0 ∧
      (v ⟨23, by decide⟩ : ℤ) ≤ (v ⟨19, by decide⟩ : ℤ) ∧
      (v ⟨23, by decide⟩ : ℤ) ≤ (v ⟨7, by decide⟩ : ℤ) ∧
      (v ⟨7, by decide⟩ : ℤ) - (v ⟨23, by decide⟩ : ℤ) - (v ⟨2, by decide⟩ : ℤ) + (v ⟨19, by decide⟩ : ℤ) ≤ 0 ∧
      (v ⟨24, by decide⟩ : ℤ) ≤ (v ⟨20, by decide⟩ : ℤ) ∧
      (v ⟨24, by decide⟩ : ℤ) ≤ (v ⟨8, by decide⟩ : ℤ) ∧
      (v ⟨8, by decide⟩ : ℤ) - (v ⟨24, by decide⟩ : ℤ) - (v ⟨3, by decide⟩ : ℤ) + (v ⟨20, by decide⟩ : ℤ) ≤ 0 ∧
      2 * (v ⟨6, by decide⟩ : ℤ) - (v ⟨22, by decide⟩ : ℤ) + 4 * (v ⟨7, by decide⟩ : ℤ) - (v ⟨23, by decide⟩ : ℤ) + 6 * (v ⟨8, by decide⟩ : ℤ) - (v ⟨24, by decide⟩ : ℤ) ≤ (WF : ℤ) - (wY : ℤ) + 1 ∧
      (v ⟨26, by decide⟩ : ℤ) ≤ (v ⟨25, by decide⟩ : ℤ) ∧
      (v ⟨26, by decide⟩ : ℤ) + (v ⟨27, by decide⟩ : ℤ) ≤ (v ⟨19, by decide⟩ : ℤ) + (v ⟨20, by decide⟩ : ℤ) ∧
      (v ⟨27, by decide⟩ : ℤ) ≤ (v ⟨16, by decide⟩ : ℤ) ∧
      2 * (v ⟨17, by decide⟩ : ℤ) ≤ (v ⟨9, by decide⟩ : ℤ) ∧
      (v ⟨31, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + (v ⟨33, by decide⟩ : ℤ) + (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨17, by decide⟩ : ℤ) ∧
      (v ⟨33, by decide⟩ : ℤ) ≤ (v ⟨0, by decide⟩ : ℤ) ∧
      (v ⟨32, by decide⟩ : ℤ) ≤ (v ⟨18, by decide⟩ : ℤ) ∧
      (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨27, by decide⟩ : ℤ))
    (hub_nat2 :
      (v ⟨27, by decide⟩ : ℤ) + 2 * (v ⟨43, by decide⟩ : ℤ) ≤ (v ⟨16, by decide⟩ : ℤ) ∧
      (v ⟨39, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) ≤ (v ⟨18, by decide⟩ : ℤ) ∧
      (v ⟨39, by decide⟩ : ℤ) + (v ⟨40, by decide⟩ : ℤ) ≤ (v ⟨29, by decide⟩ : ℤ) ∧
      2 * (v ⟨20, by decide⟩ : ℤ) - 2 * (v ⟨31, by decide⟩ : ℤ) - 2 * (v ⟨34, by decide⟩ : ℤ) - (v ⟨26, by decide⟩ : ℤ) + 2 * (v ⟨41, by decide⟩ : ℤ) + 2 * (v ⟨43, by decide⟩ : ℤ) ≤ (v ⟨16, by decide⟩ : ℤ) + (v ⟨40, by decide⟩ : ℤ) ∧
      (v ⟨33, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + 2 * (v ⟨27, by decide⟩ : ℤ) - 2 * (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨30, by decide⟩ : ℤ) ∧
      (v ⟨33, by decide⟩ : ℤ) + (v ⟨18, by decide⟩ : ℤ) - (v ⟨39, by decide⟩ : ℤ) + 2 * (v ⟨27, by decide⟩ : ℤ) - 2 * (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨30, by decide⟩ : ℤ) ∧
      (v ⟨33, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + 2 * (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 4 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) ≤ (v ⟨12, by decide⟩ : ℤ) ∧
      3 * (v ⟨31, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + (v ⟨33, by decide⟩ : ℤ) + (v ⟨34, by decide⟩ : ℤ) ≤ (v ⟨11, by decide⟩ : ℤ) ∧
      3 * (v ⟨44, by decide⟩ : ℤ) + (v ⟨46, by decide⟩ : ℤ) + (v ⟨32, by decide⟩ : ℤ) + (v ⟨33, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) ≤ (v ⟨11, by decide⟩ : ℤ) ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + 12 * (v ⟨44, by decide⟩ : ℤ) + 2 * (v ⟨46, by decide⟩ : ℤ) + 4 * (v ⟨1, by decide⟩ : ℤ) - 3 * (v ⟨18, by decide⟩ : ℤ) +
        16 * (v ⟨2, by decide⟩ : ℤ) - 5 * (v ⟨19, by decide⟩ : ℤ) + 34 * (v ⟨3, by decide⟩ : ℤ) - 5 * (v ⟨20, by decide⟩ : ℤ) + 18 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) ≤ 8 * (WF : ℤ) - 20 * (wY : ℤ) + 4 ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + 20 * (v ⟨44, by decide⟩ : ℤ) + 10 * (v ⟨46, by decide⟩ : ℤ) - 8 * (v ⟨25, by decide⟩ : ℤ) + 4 * (v ⟨1, by decide⟩ : ℤ) - 3 * (v ⟨18, by decide⟩ : ℤ) +
        16 * (v ⟨2, by decide⟩ : ℤ) - 5 * (v ⟨19, by decide⟩ : ℤ) + 34 * (v ⟨3, by decide⟩ : ℤ) - 5 * (v ⟨20, by decide⟩ : ℤ) + 18 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) ≤ 8 * (WF : ℤ) - 20 * (wY : ℤ) + 4 ∧
      (v ⟨12, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) + 10 * (v ⟨13, by decide⟩ : ℤ) + 8 * (v ⟨16, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) ≤ 8 * (WF : ℤ) - 20 * (wY : ℤ) + 4 ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + 12 * (v ⟨44, by decide⟩ : ℤ) + 2 * (v ⟨46, by decide⟩ : ℤ) + 4 * (v ⟨1, by decide⟩ : ℤ) - 3 * (v ⟨18, by decide⟩ : ℤ) +
        16 * (v ⟨2, by decide⟩ : ℤ) - 5 * (v ⟨19, by decide⟩ : ℤ) + 34 * (v ⟨3, by decide⟩ : ℤ) - 5 * (v ⟨20, by decide⟩ : ℤ) + 18 * (v ⟨4, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) -
        4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨12, by decide⟩ : ℤ) - 8 * (v ⟨16, by decide⟩ : ℤ) - 10 * (v ⟨13, by decide⟩ : ℤ) ≤ 0 ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + 20 * (v ⟨44, by decide⟩ : ℤ) + 10 * (v ⟨46, by decide⟩ : ℤ) - 8 * (v ⟨25, by decide⟩ : ℤ) + 4 * (v ⟨1, by decide⟩ : ℤ) - 3 * (v ⟨18, by decide⟩ : ℤ) +
        16 * (v ⟨2, by decide⟩ : ℤ) - 5 * (v ⟨19, by decide⟩ : ℤ) + 34 * (v ⟨3, by decide⟩ : ℤ) - 5 * (v ⟨20, by decide⟩ : ℤ) + 18 * (v ⟨4, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) -
        4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨12, by decide⟩ : ℤ) - 8 * (v ⟨16, by decide⟩ : ℤ) - 10 * (v ⟨13, by decide⟩ : ℤ) ≤ 0 ∧
      4 * (v ⟨33, by decide⟩ : ℤ) + 3 * (v ⟨32, by decide⟩ : ℤ) + (v ⟨18, by decide⟩ : ℤ) + 3 * (v ⟨19, by decide⟩ : ℤ) + 3 * (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) +
        2 * (v ⟨10, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨12, by decide⟩ : ℤ) - 2 * (v ⟨13, by decide⟩ : ℤ) ≤ 0 ∧
      (v ⟨1, by decide⟩ : ℤ) - (v ⟨18, by decide⟩ : ℤ) + 2 * (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 4 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨16, by decide⟩ : ℤ) - (v ⟨13, by decide⟩ : ℤ) ≤ 0 ∧
      2 * (v ⟨31, by decide⟩ : ℤ) + (v ⟨34, by decide⟩ : ℤ) + (v ⟨27, by decide⟩ : ℤ) + (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 3 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨10, by decide⟩ : ℤ) - (v ⟨16, by decide⟩ : ℤ) ≤ 0 ∧
      (v ⟨11, by decide⟩ : ℤ) ≤ (WF : ℤ) - 5 * (wY : ℤ) + 1 ∧
      (v ⟨2, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) + (v ⟨4, by decide⟩ : ℤ) + (v ⟨10, by decide⟩ : ℤ) ≤ (v ⟨12, by decide⟩ : ℤ) ∧
      (v ⟨12, by decide⟩ : ℤ) ≤ (WF : ℤ) - 3 * (wY : ℤ) + 1 ∧
      5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) ≤ (v ⟨11, by decide⟩ : ℤ) + (v ⟨12, by decide⟩ : ℤ) ∧
      2 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨10, by decide⟩ : ℤ) + 4 * (v ⟨16, by decide⟩ : ℤ) + 8 * (v ⟨14, by decide⟩ : ℤ) - 8 * (v ⟨17, by decide⟩ : ℤ) - 2 * (v ⟨12, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 2 * (wY : ℤ) + 2 ∧
      5 * (v ⟨14, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 3 * (wY : ℤ) + 1 ∧
      (v ⟨22, by decide⟩ : ℤ) + (v ⟨23, by decide⟩ : ℤ) + (v ⟨24, by decide⟩ : ℤ) ≤ (v ⟨15, by decide⟩ : ℤ))
    (hR_nat :
      (br.rGt = true → (v ⟨9, by decide⟩ : ℤ) + (wY : ℤ) ≤ (v ⟨14, by decide⟩ : ℤ) ∧ (v ⟨15, by decide⟩ : ℤ) = (v ⟨14, by decide⟩ : ℤ)) ∧
      (br.rGt = false → (v ⟨14, by decide⟩ : ℤ) ≤ (v ⟨9, by decide⟩ : ℤ) + (wY : ℤ) ∧ (v ⟨15, by decide⟩ : ℤ) ≤ (v ⟨9, by decide⟩ : ℤ) + (wY : ℤ)))
    (hV_nat :
      (br.vCancel = true → (v ⟨13, by decide⟩ : ℤ) - (v ⟨9, by decide⟩ : ℤ) - (v ⟨10, by decide⟩ : ℤ) - (v ⟨14, by decide⟩ : ℤ) + 2 * (v ⟨17, by decide⟩ : ℤ) = 0) ∧
      (br.vCancel = false →
        (2 * (v ⟨9, by decide⟩ : ℤ) - 2 * (v ⟨11, by decide⟩ : ℤ) + 4 * (v ⟨13, by decide⟩ : ℤ) + 4 * (v ⟨16, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 2 * (wY : ℤ)) ∧
        (2 * (v ⟨13, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + (v ⟨15, by decide⟩ : ℤ) ≤ 2 * (WF : ℤ) - 5 * (wY : ℤ) + 1)))
    (hQ1_nat :
      (br.q1Case = 0 → -4 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + (v ⟨12, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) ≤ (WF : ℤ) - (wY : ℤ) + 1) ∧
      (br.q1Case = 1 → -2 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - 2 * (v ⟨10, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) - 2 * (v ⟨14, by decide⟩ : ℤ) ≤ 0) ∧
      (br.q1Case ≠ 0 → br.q1Case ≠ 1 → -2 * (v ⟨10, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) + (v ⟨12, by decide⟩ : ℤ) + 2 * (v ⟨13, by decide⟩ : ℤ) - 4 * (v ⟨14, by decide⟩ : ℤ) ≤ 0))
    (hODE_nat :
      (br.odeCase < 4 →
        ((v ⟨1, by decide⟩ : ℤ) - (v ⟨32, by decide⟩ : ℤ) + 2 * (v ⟨2, by decide⟩ : ℤ) - (v ⟨19, by decide⟩ : ℤ) + 4 * (v ⟨3, by decide⟩ : ℤ) - (v ⟨20, by decide⟩ : ℤ) + 2 * (v ⟨4, by decide⟩ : ℤ) - (v ⟨16, by decide⟩ : ℤ) - (v ⟨13, by decide⟩ : ℤ) ≤ 0) ∧
        ((v ⟨1, by decide⟩ : ℤ) + (v ⟨27, by decide⟩ : ℤ) - (v ⟨32, by decide⟩ : ℤ) - (v ⟨16, by decide⟩ : ℤ) - (v ⟨29, by decide⟩ : ℤ) ≤ 0) ∧
        (2 * ((v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ)) ≤ r15Rhs row0A_2 v)) ∧
      (¬ br.odeCase < 4 →
        2 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) + 4 * (v ⟨44, by decide⟩ : ℤ) + 4 * (v ⟨32, by decide⟩ : ℤ) + 4 * (v ⟨34, by decide⟩ : ℤ) + 5 * (v ⟨33, by decide⟩ : ℤ) -
          2 * (v ⟨0, by decide⟩ : ℤ) - 2 * (v ⟨1, by decide⟩ : ℤ) + 2 * (v ⟨18, by decide⟩ : ℤ) + 2 * (v ⟨3, by decide⟩ : ℤ) + 6 * (v ⟨4, by decide⟩ : ℤ) ≤
          (v ⟨36, by decide⟩ : ℤ) + 2 * (v ⟨35, by decide⟩ : ℤ) + 2 * (v ⟨11, by decide⟩ : ℤ)) ∧
      ((br.odeCase = 0 ∨ br.odeCase = 4) →
        ((v ⟨37, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + 5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ) = 0) ∧
        (2 * ((v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ)) ≤ r15Rhs row0C0_2 v) ∧
        (2 * ((v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ)) ≤ r15Rhs row0C1_2 v)) ∧
      ((br.odeCase = 1 ∨ br.odeCase = 2 ∨ br.odeCase = 5) →
        ((N : ℤ) ≤ 2 * (v ⟨37, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + 5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ)) ∧
        ((v ⟨37, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + 5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ) ≤ (N : ℤ))) ∧
      (br.odeCase = 1 →
        2 * (3 * (N : ℤ) + 2 * (v ⟨11, by decide⟩ : ℤ) - 2 * (v ⟨13, by decide⟩ : ℤ) - 2 * (v ⟨16, by decide⟩ : ℤ) - 5 * (v ⟨9, by decide⟩ : ℤ) + 4 * (v ⟨17, by decide⟩ : ℤ)) ≤ r15Rhs rowC04_2 v) ∧
      (br.odeCase = 2 →
        2 * (4 * (N : ℤ) + (v ⟨11, by decide⟩ : ℤ) - (v ⟨12, by decide⟩ : ℤ) + 2 * (v ⟨10, by decide⟩ : ℤ) - 2 * (v ⟨13, by decide⟩ : ℤ)) ≤ r15Rhs rowC04_2 v) ∧
      ((br.odeCase = 3 ∨ br.odeCase = 6) →
        ((N : ℤ) ≤ (v ⟨37, by decide⟩ : ℤ) + (v ⟨11, by decide⟩ : ℤ) + (v ⟨30, by decide⟩ : ℤ)) ∧
        ((v ⟨37, by decide⟩ : ℤ) + 2 * (v ⟨16, by decide⟩ : ℤ) + 5 * (v ⟨9, by decide⟩ : ℤ) - 4 * (v ⟨17, by decide⟩ : ℤ) - (v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ) ≤ (N : ℤ))))
    (hode_lt : br.odeCase < 7) :
    let rows := buildT4BRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    let x := t4bVec v WF
    (∀ r ∈ rows.1.toList, RowValid 49 r ∧ RowSatLe x r) ∧
    (∀ r ∈ rows.2.toList, RowValid 49 r ∧ RowSatEq x r) := by
  let x : Fin 49 → ℚ := t4bVec v WF
  have hx_lt_fn : ∀ (j : ℕ) (hj : j < 48), x ⟨j, by omega⟩ = (v ⟨j, hj⟩ : ℚ) / (N : ℚ) := fun j hj => by
    dsimp [x, t4bVec]; rw [dif_pos hj]
  have hx_lt :
      x ⟨0, by decide⟩ = (v ⟨0, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (v ⟨1, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨2, by decide⟩ = (v ⟨2, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (v ⟨3, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨4, by decide⟩ = (v ⟨4, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨5, by decide⟩ = (v ⟨5, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨6, by decide⟩ = (v ⟨6, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨7, by decide⟩ = (v ⟨7, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨8, by decide⟩ = (v ⟨8, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨9, by decide⟩ = (v ⟨9, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨10, by decide⟩ = (v ⟨10, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨11, by decide⟩ = (v ⟨11, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨12, by decide⟩ = (v ⟨12, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨13, by decide⟩ = (v ⟨13, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨14, by decide⟩ = (v ⟨14, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨15, by decide⟩ = (v ⟨15, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨16, by decide⟩ = (v ⟨16, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨17, by decide⟩ = (v ⟨17, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨18, by decide⟩ = (v ⟨18, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨19, by decide⟩ = (v ⟨19, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨20, by decide⟩ = (v ⟨20, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨21, by decide⟩ = (v ⟨21, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨22, by decide⟩ = (v ⟨22, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨23, by decide⟩ = (v ⟨23, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨24, by decide⟩ = (v ⟨24, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨25, by decide⟩ = (v ⟨25, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨26, by decide⟩ = (v ⟨26, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨27, by decide⟩ = (v ⟨27, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨28, by decide⟩ = (v ⟨28, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨29, by decide⟩ = (v ⟨29, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨30, by decide⟩ = (v ⟨30, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨31, by decide⟩ = (v ⟨31, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨32, by decide⟩ = (v ⟨32, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨33, by decide⟩ = (v ⟨33, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨34, by decide⟩ = (v ⟨34, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨35, by decide⟩ = (v ⟨35, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨36, by decide⟩ = (v ⟨36, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨37, by decide⟩ = (v ⟨37, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨38, by decide⟩ = (v ⟨38, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨39, by decide⟩ = (v ⟨39, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨40, by decide⟩ = (v ⟨40, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨41, by decide⟩ = (v ⟨41, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨42, by decide⟩ = (v ⟨42, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨43, by decide⟩ = (v ⟨43, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨44, by decide⟩ = (v ⟨44, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨45, by decide⟩ = (v ⟨45, by decide⟩ : ℚ) / (N : ℚ) ∧
      x ⟨46, by decide⟩ = (v ⟨46, by decide⟩ : ℚ) / (N : ℚ) ∧ x ⟨47, by decide⟩ = (v ⟨47, by decide⟩ : ℚ) / (N : ℚ) :=
    ⟨hx_lt_fn 0 (by decide), hx_lt_fn 1 (by decide), hx_lt_fn 2 (by decide), hx_lt_fn 3 (by decide),
     hx_lt_fn 4 (by decide), hx_lt_fn 5 (by decide), hx_lt_fn 6 (by decide), hx_lt_fn 7 (by decide),
     hx_lt_fn 8 (by decide), hx_lt_fn 9 (by decide), hx_lt_fn 10 (by decide), hx_lt_fn 11 (by decide),
     hx_lt_fn 12 (by decide), hx_lt_fn 13 (by decide), hx_lt_fn 14 (by decide), hx_lt_fn 15 (by decide),
     hx_lt_fn 16 (by decide), hx_lt_fn 17 (by decide), hx_lt_fn 18 (by decide), hx_lt_fn 19 (by decide),
     hx_lt_fn 20 (by decide), hx_lt_fn 21 (by decide), hx_lt_fn 22 (by decide), hx_lt_fn 23 (by decide),
     hx_lt_fn 24 (by decide), hx_lt_fn 25 (by decide), hx_lt_fn 26 (by decide), hx_lt_fn 27 (by decide),
     hx_lt_fn 28 (by decide), hx_lt_fn 29 (by decide), hx_lt_fn 30 (by decide), hx_lt_fn 31 (by decide),
     hx_lt_fn 32 (by decide), hx_lt_fn 33 (by decide), hx_lt_fn 34 (by decide), hx_lt_fn 35 (by decide),
     hx_lt_fn 36 (by decide), hx_lt_fn 37 (by decide), hx_lt_fn 38 (by decide), hx_lt_fn 39 (by decide),
     hx_lt_fn 40 (by decide), hx_lt_fn 41 (by decide), hx_lt_fn 42 (by decide), hx_lt_fn 43 (by decide),
     hx_lt_fn 44 (by decide), hx_lt_fn 45 (by decide), hx_lt_fn 46 (by decide), hx_lt_fn 47 (by decide)⟩
  have hx_48 : x ⟨48, by decide⟩ = (WF : ℚ) / (wY : ℚ) := rfl
  have hBV := baseT4Rows_valid (nv := 49) (ic := 48) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hc_nn : (0 : ℚ) ≤ (WF : ℚ) / (wY : ℚ) := by positivity
  have hmkR15_valid : ∀ (r2 : Array ℤ) (mode : ℕ), RowValid 49 (mkR15 r2 mode) := fun r2 mode => by
    unfold mkR15; apply rowValid_filter_nz
    intro e he; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
        rcases h with rfl | rfl | rfl | rfl | rfl <;> omega
  have hmkR15_sat_0 : ∀ (r2 : Array ℤ), r2[2]! = 0 → r2[13]! = 0 →
      2 * ((v ⟨11, by decide⟩ : ℤ) - (v ⟨30, by decide⟩ : ℤ)) ≤ r15Rhs r2 v → RowSatLe x (mkR15 r2 0) := fun r2 h2z h13z hineq => by
    unfold mkR15; rw [rowSatLe_mkStat_iff, evalRow_filter_nz]
    simp only [BEq.rfl, ↓reduceIte, List.map_append, List.sum_append]
    rw [mkR15_eval_base x v hx_lt_fn]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
    have hQ := (Int.cast_le (R := ℚ)).mpr hineq
    unfold r15Rhs at hQ; rw [h2z, h13z]; push_cast at hQ ⊢; linarith only [hQ]
  have heqCore_sat : ∀ r ∈ [
      mkEq [(44, cI 1), (45, cI 1), (31, cI (-1))],
      mkEq [(46, cI 1), (47, cI 1), (34, cI (-1))],
      mkEq [(2, cI 1), (19, cI (-1)), (3, cI 2), (20, cI (-1)), (4, cI 1), (25, cI 1), (10, cI (-1))],
      mkEq [(18, cI 1), (34, cI 1), (35, cI (-1))],
      mkEq [(0, cI 1), (1, cI 1), (18, cI (-1)), (2, cI 1), (19, cI (-1)), (3, cI 1), (20, cI (-1)), (28, cI (-1))],
      mkEq [(0, cI 1), (1, cI 1), (2, cI 1), (19, cI (-1)), (3, cI 1), (20, cI (-1)), (26, cI 1), (37, cI (-1))],
      mkEq [(19, cI 1), (20, cI 1), (26, cI 1), (27, cI (-1)), (29, cI 1), (13, cI (-1))],
      mkEq [(10, cI 2), (19, cI 1), (20, cI 1), (26, cI (-1)), (30, cI 1), (12, cI (-1))],
      mkEq [(12, cI 1), (10, cI (-2)), (13, cI 2), (19, cI (-3)), (20, cI (-3)), (34, cI 3), (35, cI (-1)), (36, cI (-1))],
      mkEq [(33, cI 1), (32, cI 1), (3, cI 2), (20, cI (-1)), (4, cI 2), (38, cI 1), (11, cI (-1))],
      mkEq [(41, cI 1), (42, cI 1), (43, cI 1), (21, cI (-1))]
    ], RowValid 49 r ∧ RowSatEq x r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (44 : ℕ) < 49 by omega, show (45 : ℕ) < 49 by omega, show (31 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (46 : ℕ) < 49 by omega, show (47 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (25 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (18 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (35 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (0 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (28 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (0 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (26 : ℕ) < 49 by omega, show (37 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (26 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (29 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (10 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (26 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (12 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (35 : ℕ) < 49 by omega, show (36 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (38 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (41 : ℕ) < 49 by omega, show (42 : ℕ) < 49 by omega, show (43 : ℕ) < 49 by omega, show (21 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) heq_nat.2.2.2.2.2.2.2.2.2.2
      push_cast at hQ ⊢; linarith only [hQ]
  have hubCore_sat : ∀ r ∈ ([
      mkStat [(44, cI 1), (46, cI 1), (19, cI (-1))] 0 false,
      mkStat [(45, cI 1), (47, cI 1), (20, cI (-1))] 0 false,
      mkStat [(18, cI 1), (1, cI (-1))] 0 false,
      mkStat [(19, cI 1), (2, cI (-1))] 0 false,
      mkStat [(20, cI 1), (3, cI (-1))] 0 false,
      mkStat [(21, cI 1), (4, cI (-1))] 0 false,
      mkStat [(22, cI 1), (18, cI (-1))] 0 false,
      mkStat [(22, cI 1), (6, cI (-1))] 0 false,
      mkStat [(6, cI 1), (22, cI (-1)), (1, cI (-1)), (18, cI 1)] 0 false,
      mkStat [(23, cI 1), (19, cI (-1))] 0 false,
      mkStat [(23, cI 1), (7, cI (-1))] 0 false,
      mkStat [(7, cI 1), (23, cI (-1)), (2, cI (-1)), (19, cI 1)] 0 false,
      mkStat [(24, cI 1), (20, cI (-1))] 0 false,
      mkStat [(24, cI 1), (8, cI (-1))] 0 false,
      mkStat [(8, cI 1), (24, cI (-1)), (3, cI (-1)), (20, cI 1)] 0 false,
      mkStat [(6, cI 2), (22, cI (-1)), (7, cI 4), (23, cI (-1)), (8, cI 6), (24, cI (-1)), (48, cH (-1))] (-2),
      mkStat [(26, cI 1), (25, cI (-1))] 0 false,
      mkStat [(26, cI 1), (27, cI 1), (19, cI (-1)), (20, cI (-1))] 0 false,
      mkStat [(27, cI 1), (16, cI (-1))] 0,
      mkStat [(17, cI 1), (9, cH (-1))] 0,
      mkStat [(31, cI 1), (32, cI 1), (33, cI 1), (34, cI 1), (17, cI (-1))] 0 false,
      mkStat [(33, cI 1), (0, cI (-1))] 0 false,
      mkStat [(32, cI 1), (18, cI (-1))] 0 false,
      mkStat [(34, cI 1), (27, cI (-1))] 0 false,
      mkStat [(27, cI 1), (43, cI 2), (16, cI (-1))] 0,
      mkStat [(39, cI 1), (32, cI 1), (18, cI (-1))] 0 false,
      mkStat [(39, cI 1), (40, cI 1), (29, cI (-1))] 0 false,
      mkStat [(20, cI 2), (31, cI (-2)), (34, cI (-2)), (26, cI (-1)), (41, cI 2), (43, cI 2), (16, cI (-1)), (40, cI (-1))] 0,
      mkStat [(33, cI 1), (32, cI 1), (27, cI 2), (34, cI (-2)), (30, cI (-1))] 0,
      mkStat [(33, cI 1), (18, cI 1), (39, cI (-1)), (27, cI 2), (34, cI (-2)), (30, cI (-1))] 0,
      mkStat [(33, cI 1), (32, cI 1), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (12, cI (-1))] 0,
      mkStat [(31, cI 3), (32, cI 1), (33, cI 1), (34, cI 1), (11, cI (-1))] 0,
      mkStat [(44, cI 3), (46, cI 1), (32, cI 1), (33, cI 1), (3, cI 2), (20, cI (-1)), (4, cI 2), (11, cI (-1))] 0,
      mkStat [(33, cI 4), (32, cI 3), (44, cI 12), (46, cI 2), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (11, cI (-1)), (48, cI (-4))] (-40),
      mkStat [(33, cI 4), (32, cI 3), (44, cI 20), (46, cI 10), (25, cI (-8)), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (11, cI (-1)), (48, cI (-4))] (-40),
      mkStat [(12, cI 1), (10, cI (-2)), (17, cI 4), (13, cI 10), (16, cI 8), (11, cI (-1)), (48, cI (-4))] (-40),
      mkStat [(33, cI 4), (32, cI 3), (44, cI 12), (46, cI 2), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (16, cI (-8)), (13, cI (-10))] 0,
      mkStat [(33, cI 4), (32, cI 3), (44, cI 20), (46, cI 10), (25, cI (-8)), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (16, cI (-8)), (13, cI (-10))] 0,
      mkStat [(33, cI 4), (32, cI 3), (18, cI 1), (19, cI 3), (20, cI 3), (3, cI 2), (4, cI 2), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (13, cI (-2))] 0,
      mkStat [(1, cI 1), (18, cI (-1)), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (16, cI (-1)), (13, cI (-1))] 0,
      mkStat [(31, cI 2), (34, cI 1), (27, cI 1), (2, cI 1), (19, cI (-1)), (3, cI 3), (20, cI (-1)), (4, cI 2), (10, cI (-1)), (16, cI (-1))] 0,
      mkStat [(11, cI 1), (48, cH (-1))] (-10),
      mkStat [(2, cI 1), (3, cI 2), (4, cI 1), (10, cI 1), (12, cI (-1))] 0,
      mkStat [(12, cI 1), (48, cH (-1))] (-6),
      mkStat [(9, cH 5), (17, cI (-2)), (10, cI 1), (16, cI 1), (11, cH (-1)), (12, cH (-1))] 0,
      mkStat [(9, cH 1), (10, cI 1), (16, cI 1), (14, cI 2), (17, cI (-2)), (12, cH (-1)), (48, cQ (-1))] (-1),
      mkStat [(14, cI 5), (10, cI 2), (16, cI 2), (17, cI (-4)), (48, cI (-1))] (-6),
      mkStat [(22, cI 1), (23, cI 1), (24, cI 1), (15, cI (-1))] 0
    ] : List SparseRow), RowValid 49 r ∧ RowSatLe x r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (45 : ℕ) < 49 by omega, show (47 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (18 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (19 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (20 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (21 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (22 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (22 : ℕ) < 49 by omega, show (6 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (6 : ℕ) < 49 by omega, show (22 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (23 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (23 : ℕ) < 49 by omega, show (7 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (7 : ℕ) < 49 by omega, show (23 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (24 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (24 : ℕ) < 49 by omega, show (8 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (8 : ℕ) < 49 by omega, show (24 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (6 : ℕ) < 49 by omega, show (22 : ℕ) < 49 by omega, show (7 : ℕ) < 49 by omega, show (23 : ℕ) < 49 by omega, show (8 : ℕ) < 49 by omega, show (24 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (26 : ℕ) < 49 by omega, show (25 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (26 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (27 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (17 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N, cH_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (31 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (33 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (0 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (32 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (34 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (27 : ℕ) < 49 by omega, show (43 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (39 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (39 : ℕ) < 49 by omega, show (40 : ℕ) < 49 by omega, show (29 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (20 : ℕ) < 49 by omega, show (31 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (26 : ℕ) < 49 by omega, show (41 : ℕ) < 49 by omega, show (43 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (40 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (39 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (31 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (33 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (33 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (25 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (12 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (46 : ℕ) < 49 by omega, show (25 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (33 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 49 by omega, show (18 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (31 : ℕ) < 49 by omega, show (34 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (11 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (2 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (12 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N, cH_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_div_N, cQ_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (14 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (22 : ℕ) < 49 by omega, show (23 : ℕ) < 49 by omega, show (24 : ℕ) < 49 by omega, show (15 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hub_nat2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      push_cast at hQ ⊢; linarith only [hQ]
  have hR_sat :
      (∀ r ∈ (if !br.rGt then [mkStat [(9, cI (-1)), (14, cI 1)] 2, mkStat [(9, cI (-1)), (15, cI 1)] 2]
        else [mkStat [(9, cI 1), (14, cI (-1))] (-2)]), RowValid 49 r ∧ RowSatLe x r) ∧
      (∀ r ∈ (if !br.rGt then ([] : List SparseRow) else [mkEq [(14, cI 1), (15, cI (-1))]]), RowValid 49 r ∧ RowSatEq x r) := by
    cases hr : br.rGt
    · have hRf := hR_nat.2 hr
      simp only [Bool.not_false, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro r hrm; rcases hrm with rfl | rfl
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
          have hQ := (Int.cast_le (R := ℚ)).mpr hRf.1
          push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 49 by omega, show (15 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
          have hQ := (Int.cast_le (R := ℚ)).mpr hRf.2
          push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
      · intro _ hrm; cases hrm
    · have hRt := hR_nat.1 hr
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
      constructor
      · intro r hrm; subst hrm
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ := (Int.cast_le (R := ℚ)).mpr hRt.1
        push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
      · intro r hrm; subst hrm
        refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
        rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (14 : ℕ) < 49 by omega, show (15 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) hRt.2
        push_cast at hQ ⊢; linarith only [hQ]
  have hV_sat :
      (∀ r ∈ (if !br.vCancel then
        [mkStat [(9, cH 1), (11, cH (-1)), (13, cI 1), (16, cI 1), (48, cQ (-1))] (-1),
         mkStat [(13, cI 2), (16, cI 2), (15, cI 1), (48, cI (-1))] (-10)]
        else []), RowValid 49 r ∧ RowSatLe x r) ∧
      (∀ r ∈ (if !br.vCancel then ([] : List SparseRow)
        else [mkEq [(13, cI 1), (9, cI (-1)), (10, cI (-1)), (14, cI (-1)), (17, cI 2)]]), RowValid 49 r ∧ RowSatEq x r) := by
    cases hv : br.vCancel
    · have hVf := hV_nat.2 hv
      simp only [Bool.not_false, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨fun r hr => ?_, fun _ hr => False.elim hr⟩
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega,
          show (16 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_div_N, cQ_mul_c_eq]
        have hQ := (Int.cast_le (R := ℚ)).mpr hVf.1
        push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (13 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (15 : ℕ) < 49 by omega,
          show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cI_mul_c_eq]
        have hQ := (Int.cast_le (R := ℚ)).mpr hVf.2
        push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · have hVt := hV_nat.1 hv
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, List.mem_singleton]
      refine ⟨fun _ hr => False.elim hr, fun r hr => ?_⟩
      subst hr
      refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (13 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega,
        show (14 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) hVt
      push_cast at hQ ⊢; linarith only [hQ]
  have hQ1_sat : ∀ r ∈ (if br.q1Case == 0 then [mkStat [(9, cI (-4)), (17, cI 4), (10, cI (-2)), (12, cI 1), (13, cI 2), (48, cH (-1))] (-2)]
      else if br.q1Case == 1 then [mkStat [(9, cI (-2)), (17, cI 4), (10, cI (-2)), (13, cI 2), (14, cI (-2))] 0]
      else [mkStat [(10, cI (-2)), (17, cI 4), (11, cI (-1)), (12, cI 1), (13, cI 2), (14, cI (-4))] 0]),
      RowValid 49 r ∧ RowSatLe x r := by
    by_cases h0 : br.q1Case = 0
    · intro r hr; simp only [h0, BEq.rfl, ↓reduceIte, List.mem_singleton] at hr; subst hr
      refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega,
        show (13 : ℕ) < 49 by omega, show (48 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, hx_48, cI_mul_div_N, cH_mul_c_eq]
      have hQ := (Int.cast_le (R := ℚ)).mpr (hQ1_nat.1 h0)
      push_cast at hQ ⊢; linarith only [hQ, hN_eq, hc_nn]
    · by_cases h1 : br.q1Case = 1
      · intro r hr; simp only [h1, show (1 == 0) = false by decide, BEq.rfl, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr; subst hr
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega,
          show (13 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ := (Int.cast_le (R := ℚ)).mpr (hQ1_nat.2.1 h1)
        push_cast at hQ ⊢; linarith only [hQ]
      · intro r hr
        have h0f : (br.q1Case == 0) = false := beq_false_of_ne h0
        have h1f : (br.q1Case == 1) = false := beq_false_of_ne h1
        simp only [h0f, h1f, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr; subst hr
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (10 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega,
          show (12 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, show (14 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ := (Int.cast_le (R := ℚ)).mpr (hQ1_nat.2.2 h0 h1)
        push_cast at hQ ⊢; linarith only [hQ]
  have hB1h_eq_sat : br.odeCase = 0 ∨ br.odeCase = 4 →
      RowValid 49 (mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]) ∧
      RowSatEq x (mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]) := fun hor => by
    refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
    rw [rowSatEq_mkEq_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (37 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
      show (17 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
    have hQ : _ = _ := congrArg (Int.cast : ℤ → ℚ) (hODE_nat.2.2.1 hor).1
    push_cast at hQ ⊢; linarith only [hQ]
  have hB1_0C_sat : br.odeCase = 0 ∨ br.odeCase = 4 →
      (RowValid 49 (mkR15 row0C0_2 0) ∧ RowSatLe x (mkR15 row0C0_2 0)) ∧
      (RowValid 49 (mkR15 row0C1_2 0) ∧ RowSatLe x (mkR15 row0C1_2 0)) := fun hor =>
    ⟨⟨hmkR15_valid row0C0_2 0, hmkR15_sat_0 row0C0_2 row0C0_2_vals.2.2.1 row0C0_2_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hODE_nat.2.2.1 hor).2.1⟩,
     ⟨hmkR15_valid row0C1_2 0, hmkR15_sat_0 row0C1_2 row0C1_2_vals.2.2.1 row0C1_2_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hODE_nat.2.2.1 hor).2.2⟩⟩
  have hW2a_rows_sat : br.odeCase = 1 ∨ br.odeCase = 2 ∨ br.odeCase = 5 →
      (RowValid 49 (mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4)) ∧
       RowSatLe x (mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4))) ∧
      (RowValid 49 (mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4) ∧
       RowSatLe x (mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4)) := fun hor => by
    have hw2 := hODE_nat.2.2.2.1 hor
    constructor
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (37 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
        show (17 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hw2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (37 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
        show (17 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hw2.2
      push_cast at hQ ⊢; linarith only [hQ]
  have hW2b_rows_sat : br.odeCase = 3 ∨ br.odeCase = 6 →
      (RowValid 49 (mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4)) ∧
       RowSatLe x (mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4))) ∧
      (RowValid 49 (mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4) ∧
       RowSatLe x (mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4)) := fun hor => by
    have hw2 := hODE_nat.2.2.2.2.2.2 hor
    constructor
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (37 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hw2.1
      push_cast at hQ ⊢; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (37 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega, show (9 : ℕ) < 49 by omega,
        show (17 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, show (30 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
      have hQ := (Int.cast_le (R := ℚ)).mpr hw2.2
      push_cast at hQ ⊢; linarith only [hQ]
  have hODE_sat :
      let (ubODE, eqODE) :=
        if br.odeCase < 4 then
          let u0 : List SparseRow := [
            mkStat [(1, cI 1), (32, cI (-1)), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (16, cI (-1)), (13, cI (-1))] 0,
            mkStat [(1, cI 1), (27, cI 1), (32, cI (-1)), (16, cI (-1)), (29, cI (-1))] 0,
            mkR15 row0A_2 0
          ]
          if br.odeCase == 0 then
            (u0 ++ [mkR15 row0C0_2 0, mkR15 row0C1_2 0],
             [mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]])
          else if br.odeCase == 1 then
            (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4,
                    mkR15 rowC04_2 1], [])
          else if br.odeCase == 2 then
            (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4,
                    mkR15 rowC04_2 2], [])
          else
            (u0 ++ [mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
        else
          let u0 : List SparseRow := [
            mkStat [(9, cI 2), (17, cI (-4)), (44, cI 4), (32, cI 4), (34, cI 4), (33, cI 5),
                    (0, cI (-2)), (1, cI (-2)), (18, cI 2), (3, cI 2), (4, cI 6),
                    (36, cI (-1)), (35, cI (-2)), (11, cI (-2))] 0
          ]
          if br.odeCase == 4 then
            (u0 ++ [mkR15 row0C0_2 0, mkR15 row0C1_2 0],
             [mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]])
          else if br.odeCase == 5 then
            (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
          else
            (u0 ++ [mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4),
                    mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
      (∀ r ∈ ubODE, RowValid 49 r ∧ RowSatLe x r) ∧ (∀ r ∈ eqODE, RowValid 49 r ∧ RowSatEq x r) := by
    by_cases hlt4 : br.odeCase < 4
    · have hoh := hODE_nat.1 hlt4
      have hu0_sat : ∀ r ∈ [
          mkStat [(1, cI 1), (32, cI (-1)), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (16, cI (-1)), (13, cI (-1))] 0,
          mkStat [(1, cI 1), (27, cI 1), (32, cI (-1)), (16, cI (-1)), (29, cI (-1))] 0,
          mkR15 row0A_2 0
        ], RowValid 49 r ∧ RowSatLe x r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (1 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega, show (2 : ℕ) < 49 by omega, show (19 : ℕ) < 49 by omega,
            show (3 : ℕ) < 49 by omega, show (20 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega,
            show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
          have hQ := (Int.cast_le (R := ℚ)).mpr hoh.1
          push_cast at hQ ⊢; linarith only [hQ]
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (1 : ℕ) < 49 by omega, show (27 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega,
            show (16 : ℕ) < 49 by omega, show (29 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
          have hQ := (Int.cast_le (R := ℚ)).mpr hoh.2.1
          push_cast at hQ ⊢; linarith only [hQ]
        · exact ⟨hmkR15_valid row0A_2 0, hmkR15_sat_0 row0A_2 row0A_2_vals.2.2.1 row0A_2_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hoh.2.2⟩
      by_cases hc0 : br.odeCase = 0
      · simp only [hc0, show (0 : ℕ) < 4 by decide, BEq.rfl, ↓reduceIte, List.mem_append]
        refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          · exact (hB1_0C_sat (Or.inl hc0)).1
          · exact (hB1_0C_sat (Or.inl hc0)).2),
          fun r hr => by simp only [List.mem_singleton] at hr; rw [hr]; exact hB1h_eq_sat (Or.inl hc0)⟩
      · by_cases hc1 : br.odeCase = 1
        · simp only [hc1, show (1 : ℕ) < 4 by decide, show (1 == 0) = false by decide, BEq.rfl, Bool.false_eq_true, ↓reduceIte,
            List.mem_append]
          refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl
            · exact (hW2a_rows_sat (Or.inl hc1)).1
            · exact (hW2a_rows_sat (Or.inl hc1)).2
            · refine ⟨hmkR15_valid rowC04_2 1, ?_⟩
              unfold mkR15; rw [rowSatLe_mkStat_iff, evalRow_filter_nz]
              simp only [show (1 == 0) = false by decide, BEq.rfl, Bool.false_eq_true, ↓reduceIte, List.map_append, List.sum_append]
              rw [mkR15_eval_base x v hx_lt_fn]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                show (11 : ℕ) < 49 by omega, show (13 : ℕ) < 49 by omega, show (16 : ℕ) < 49 by omega,
                show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
              have hQ := (Int.cast_le (R := ℚ)).mpr (hODE_nat.2.2.2.2.1 hc1)
              unfold r15Rhs at hQ; simp only [rowC04_2_vals] at hQ ⊢; push_cast at hQ ⊢; linarith only [hQ]),
            fun _ hr => by cases hr⟩
        · by_cases hc2 : br.odeCase = 2
          · simp only [hc2, show (2 : ℕ) < 4 by decide, show (2 == 0) = false by decide, show (2 == 1) = false by decide,
              BEq.rfl, Bool.false_eq_true, ↓reduceIte, List.mem_append]
            refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl | rfl
              · exact (hW2a_rows_sat (Or.inr (Or.inl hc2))).1
              · exact (hW2a_rows_sat (Or.inr (Or.inl hc2))).2
              · refine ⟨hmkR15_valid rowC04_2 2, ?_⟩
                unfold mkR15; rw [rowSatLe_mkStat_iff, evalRow_filter_nz]
                simp only [show (2 == 0) = false by decide, show (2 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte, List.map_append, List.sum_append]
                rw [mkR15_eval_base x v hx_lt_fn]
                simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  show (11 : ℕ) < 49 by omega, show (12 : ℕ) < 49 by omega, show (10 : ℕ) < 49 by omega,
                  show (13 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
                have hQ := (Int.cast_le (R := ℚ)).mpr (hODE_nat.2.2.2.2.2.1 hc2)
                unfold r15Rhs at hQ; simp only [rowC04_2_vals] at hQ ⊢; push_cast at hQ ⊢; linarith only [hQ]),
              fun _ hr => by cases hr⟩
          · have hc3 : br.odeCase = 3 := by omega
            simp only [hc3, show (3 : ℕ) < 4 by decide, show (3 == 0) = false by decide, show (3 == 1) = false by decide,
              show (3 == 2) = false by decide, Bool.false_eq_true, ↓reduceIte, List.mem_append]
            refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl
              · exact (hW2b_rows_sat (Or.inl hc3)).1
              · exact (hW2b_rows_sat (Or.inl hc3)).2),
              fun _ hr => by cases hr⟩
    · have hu0_sat : ∀ r ∈ [
          mkStat [(9, cI 2), (17, cI (-4)), (44, cI 4), (32, cI 4), (34, cI 4), (33, cI 5),
                  (0, cI (-2)), (1, cI (-2)), (18, cI 2), (3, cI 2), (4, cI 6),
                  (36, cI (-1)), (35, cI (-2)), (11, cI (-2))] 0
        ], RowValid 49 r ∧ RowSatLe x r := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]; simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 49 by omega, show (17 : ℕ) < 49 by omega, show (44 : ℕ) < 49 by omega, show (32 : ℕ) < 49 by omega,
          show (34 : ℕ) < 49 by omega, show (33 : ℕ) < 49 by omega, show (0 : ℕ) < 49 by omega, show (1 : ℕ) < 49 by omega,
          show (18 : ℕ) < 49 by omega, show (3 : ℕ) < 49 by omega, show (4 : ℕ) < 49 by omega, show (36 : ℕ) < 49 by omega,
          show (35 : ℕ) < 49 by omega, show (11 : ℕ) < 49 by omega, ↓reduceDIte, hx_lt, cI_mul_div_N]
        have hQ := (Int.cast_le (R := ℚ)).mpr (hODE_nat.2.1 hlt4)
        push_cast at hQ ⊢; linarith only [hQ]
      by_cases hc4 : br.odeCase = 4
      · simp only [hc4, show ¬ ((4 : ℕ) < 4) by decide, BEq.rfl, ↓reduceIte, List.mem_append]
        refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          · exact (hB1_0C_sat (Or.inr hc4)).1
          · exact (hB1_0C_sat (Or.inr hc4)).2),
          fun r hr => by simp only [List.mem_singleton] at hr; rw [hr]; exact hB1h_eq_sat (Or.inr hc4)⟩
      · by_cases hc5 : br.odeCase = 5
        · simp only [hc5, show ¬ ((5 : ℕ) < 4) by decide, show (5 == 4) = false by decide, BEq.rfl, Bool.false_eq_true,
            ↓reduceIte, List.mem_append]
          refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact (hW2a_rows_sat (Or.inr (Or.inr hc5))).1
            · exact (hW2a_rows_sat (Or.inr (Or.inr hc5))).2),
            fun _ hr => by cases hr⟩
        · have hc6 : br.odeCase = 6 := by omega
          simp only [hc6, show ¬ ((6 : ℕ) < 4) by decide, show (6 == 4) = false by decide, show (6 == 5) = false by decide,
            Bool.false_eq_true, ↓reduceIte, List.mem_append]
          refine ⟨fun r hr => hr.elim (hu0_sat r) (fun h => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact (hW2b_rows_sat (Or.inr hc6)).1
            · exact (hW2b_rows_sat (Or.inr hc6)).2),
            fun _ hr => by cases hr⟩
  constructor
  · intro r hr
    simp only [buildT4BRows, t4bStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | ((((hr | hr) | hr) | hr) | hr)
    · exact ⟨hBV.1 r hr, hBS.1 r hr⟩
    · exact hubCore_sat r hr
    · simp only [apply_ite Prod.fst] at hr; exact hR_sat.1 r hr
    · simp only [apply_ite Prod.fst] at hr; exact hV_sat.1 r hr
    · exact hQ1_sat r hr
    · exact hODE_sat.1 r hr
  · intro r hr
    simp only [buildT4BRows, t4bStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | (((hr | hr) | hr) | hr)
    · exact ⟨hBV.2 r hr, hBS.2 r hr⟩
    · exact heqCore_sat r hr
    · simp only [apply_ite Prod.snd] at hr; exact hR_sat.2 r hr
    · simp only [apply_ite Prod.snd] at hr; exact hV_sat.2 r hr
    · exact hODE_sat.2 r hr

end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
