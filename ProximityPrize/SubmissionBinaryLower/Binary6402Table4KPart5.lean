import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart4
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
open Classical in
lemma sum_step15_cols (S_fin : Finset (AlgebraicClosure Fld))
    (hS_dom : ∀ i : Idx, algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) ∈ S_fin)
    (hS_M0s : ((K.M0s.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_Lam1 : ((K.Lam1.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_p1 : ((K.p1.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_D1 : (S.D1.map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_g2r : (K.g2rem.map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin)
    (hS_g2 : ((D.gj 2).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin) :
    (∑ a ∈ S_fin, ((K.ptOf a).m0 : ℤ)) = (D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).mbad : ℤ)) = (K.mbadCnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).m1 : ℤ)) = (S.n1U : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).m2 : ℤ)) = (D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).k3 : ℤ)) = (S.n3U : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).mL0 (K.d2_l a) : ℤ)) = (K.mLCnt : ℤ) - (K.dmLCnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ)) = (K.mu1Cnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ)) =
      (K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ) ∧
    (∑ a ∈ S_fin, (K.lam_l a : ℤ)) = (K.Lam1.natDegree : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).din (K.d2_l a) : ℤ)) = (K.dinCnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).dmL (K.d2_l a) : ℤ)) = (K.dmLCnt : ℤ) ∧
    (∑ a ∈ S_fin, ((K.ptOf a).d2oth (K.d2_l a) : ℤ)) = (S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ) ∧
    (∑ a ∈ S_fin, (K.L0_l a : ℤ)) = 2 * (S.ntU : ℤ) ∧
    (∑ a ∈ S_fin, (K.a1_l a : ℤ)) = (S.p.natDegree : ℤ) - (S.D1.natDegree : ℤ) ∧
    (∑ a ∈ S_fin, (K.LnoU_l a : ℤ)) = 2 * ((D.nt : ℤ) - (S.ntU : ℤ)) ∧
    (∑ a ∈ S_fin, (K.c_l a : ℤ)) = ((D.gj 2).natDegree : ℤ) ∧
    (∑ a ∈ S_fin, (K.e1_l a : ℤ)) = (K.g2rem.natDegree : ℤ) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  let domImg : Finset E := Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i))
  have hdom_sub : domImg ⊆ S_fin := fun a ha => by
    rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩; exact hS_dom i
  have hsum_dom : ∀ (f : E → ℤ), (∀ a, (¬ ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)) → f a = 0) →
      ∑ a ∈ S_fin, f a = ∑ i : Idx, f (ι (BinaryIRSProfile.domain i)) := fun f hf0 => by
    rw [← Finset.sum_subset hdom_sub (fun a _ hna => hf0 a (fun ⟨i, hi⟩ => hna (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩))),
      Finset.sum_image (fun i _ j _ h => BinaryIRSProfile.domain.injective (ι.injective h))]
  have hD1_sum : (∑ a ∈ S_fin, (K.d2_l a : ℤ)) = (S.D1.natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_map_eq_natDegree S.D1 S.D1_ne_zero S_fin hS_D1
  have hLam_sum : (∑ a ∈ S_fin, (K.lam_l a : ℤ)) = (K.Lam1.natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_sq_map_eq_natDegree K.Lam1 K.hLam1_ne S_fin hS_Lam1
  have hp1_sum : (∑ a ∈ S_fin, (K.a1_l a : ℤ)) = (S.p.natDegree : ℤ) - (S.D1.natDegree : ℤ) := by
    have h1 : ∑ a ∈ S_fin, K.a1_l a = K.p1.natDegree :=
      sum_rootMultiplicity_sq_map_eq_natDegree K.p1 K.hp1_ne S_fin hS_p1
    have hp := K.natDegree_p_eq
    have h1Z : (∑ a ∈ S_fin, (K.a1_l a : ℤ)) = (K.p1.natDegree : ℤ) := by exact_mod_cast h1
    rw [h1Z]; clear h1 h1Z hD1_sum hLam_sum hdom_sub hsum_dom; omega
  have hc_sum : (∑ a ∈ S_fin, (K.c_l a : ℤ)) = ((D.gj 2).natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_map_eq_natDegree (D.gj 2) D.g2_ne_zero S_fin hS_g2
  have he1_sum : (∑ a ∈ S_fin, (K.e1_l a : ℤ)) = (K.g2rem.natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_map_eq_natDegree K.g2rem K.g2rem_ne S_fin hS_g2r
  have hM0s_sum : (∑ a ∈ S_fin, (K.muRaw_l a : ℤ)) = (K.M0s.natDegree : ℤ) := by
    exact_mod_cast sum_rootMultiplicity_sq_map_eq_natDegree K.M0s K.hM0s_ne S_fin hS_M0s
  -- Helper for d2_l at domain i:
  have hd2_dom : ∀ i : Idx, K.d2_l (ι (BinaryIRSProfile.domain i)) = if K.isD1 i then 1 else 0 := fun i => by
    have hle := K.d2_l_le_one (ι (BinaryIRSProfile.domain i))
    dsimp [d2_l] at hle ⊢; rw [rootMultiplicity_map_eq] at hle ⊢
    split_ifs with h
    · have hge := (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h); omega
    · exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr h)
  -- Helper for din, dmL, mL0, mu1!
  have hdin_sum : (∑ a ∈ S_fin, ((K.ptOf a).din (K.d2_l a) : ℤ)) = (K.dinCnt : ℤ) := by
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.dinCnt : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ K.isNorm i ∧ K.isD1 i then (1 : ℤ) else 0) +
        (if 3 ≤ D.k i ∧ K.isNorm i ∧ K.isD1 i then 1 else 0)) := by
      rw [Finset.sum_add_distrib, ← K.din2Cnt_Z, ← K.din3Cnt_Z]; unfold dinCnt; push_cast; rfl
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    rw [K.ptOf_dom i, hd2_dom i]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.din] <;> omega
  have hdmL_sum : (∑ a ∈ S_fin, ((K.ptOf a).dmL (K.d2_l a) : ℤ)) = (K.dmLCnt : ℤ) := by
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.dmLCnt : ℤ) = ∑ i : Idx, ((if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then (1 : ℤ) else 0) +
        (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      rw [Finset.sum_add_distrib, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z]; unfold dmLCnt; push_cast; rfl
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    rw [K.ptOf_dom i, hd2_dom i]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.dmL, Step15Pt.isML] <;> omega
  have hmu1_sum : (∑ a ∈ S_fin, ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ)) = (K.mu1Cnt : ℤ) := by
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.mu1Cnt : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i ∧ K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 then (1 : ℤ) else 0) := K.mu1Cnt_Z
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    have hmu_eq : K.muEx_l (ι (BinaryIRSProfile.domain i)) =
        K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) -
          muSub (K.ptOf (ι (BinaryIRSProfile.domain i))) := by
      unfold muEx_l muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
    rw [hmu_eq, K.ptOf_dom i, hd2_dom i]
    by_cases hk1 : D.k i = 1
    · have hk0 : D.k i ≠ 0 := by omega
      by_cases hU : S.isU0 i
      · by_cases hD1 : K.isD1 i
        · simp only [hk1, hk0, hU, hD1, not_true_eq_false, and_true, and_false, false_and, ↓reduceIte, Step15Pt.mu1, Nat.one_ne_zero, Nat.cast_zero]
        · by_cases hM : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0
          · have h1 := (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hM)
            simp only [hk1, Nat.one_ne_zero, hU, hD1, hM, not_false_eq_true, and_true, ↓reduceIte, Step15Pt.mu1, muSub]
            rw [sub_zero_nr]; simp only [h1, and_self, ↓reduceIte, Nat.cast_one]
          · have h0 := rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hM)
            simp only [hk1, Nat.one_ne_zero, hU, hD1, hM, not_false_eq_true, and_true, and_false, ↓reduceIte, Step15Pt.mu1, muSub, h0, Nat.zero_sub, show ¬ (1 ≤ 0) by decide, Nat.cast_zero]
      · simp only [hk1, Nat.one_ne_zero, hU, and_false, false_and, ↓reduceIte, Step15Pt.mu1, Nat.cast_zero]
    · simp only [hk1, ↓reduceIte, false_and]; (try split_ifs) <;> simp only [Step15Pt.mu1, Nat.cast_zero]
  have hmuEx_sum : (∑ a ∈ S_fin, (K.muEx_l a : ℤ)) =
      (K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) := by
    let sub : E → ℤ := fun a => (muSub (K.ptOf a) : ℤ)
    have hpt : ∀ a ∈ S_fin, (K.muEx_l a : ℤ) = (K.muRaw_l a : ℤ) - sub a := fun a _ => by
      dsimp [muEx_l, sub]
      cases hpt : K.ptOf a
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · -- k2U: muRaw_l ≥ 1
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; exact Step15Pt.noConfusion ((K.ptOf_out h).symm.trans hpt)
        rcases hdom with ⟨i, rfl⟩
        have hn : K.isNorm i := ((K.ptOf_dom_spec i).2.2.1 hpt).2
        have h1 : 1 ≤ K.muRaw_l (ι (BinaryIRSProfile.domain i)) := by
          unfold muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
          exact (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
        simp only [muSub]; rw [Nat.cast_sub h1]
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · -- k2U_mb: muRaw_l ≥ 2
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; exact Step15Pt.noConfusion ((K.ptOf_out h).symm.trans hpt)
        rcases hdom with ⟨i, rfl⟩
        have hmb : K.isMbad i := ((K.ptOf_dom_spec i).2.2.2.2.1 hpt).2
        have h2 : 2 ≤ K.muRaw_l (ι (BinaryIRSProfile.domain i)) := by
          unfold muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
          exact (le_rootMultiplicity_iff K.hM0s_ne).mpr ((pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2))
        simp only [muSub]; rw [Nat.cast_sub h2]
      · -- k3U: muRaw_l ≥ 1
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; exact Step15Pt.noConfusion ((K.ptOf_out h).symm.trans hpt)
        rcases hdom with ⟨i, rfl⟩
        have hn : K.isNorm i := ((K.ptOf_dom_spec i).2.2.2.2.2.1 hpt).2
        have h1 : 1 ≤ K.muRaw_l (ι (BinaryIRSProfile.domain i)) := by
          unfold muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
          exact (le_rootMultiplicity_iff K.hM0s_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hn.2.2.2)
        simp only [muSub]; rw [Nat.cast_sub h1]
      · simp only [muSub]; rw [sub_zero_nr]; push_cast; ring
      · -- k3U_mb: muRaw_l ≥ 2
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; exact Step15Pt.noConfusion ((K.ptOf_out h).symm.trans hpt)
        rcases hdom with ⟨i, rfl⟩
        have hmb : K.isMbad i := ((K.ptOf_dom_spec i).2.2.2.2.2.2.2 hpt).2
        have h2 : 2 ≤ K.muRaw_l (ι (BinaryIRSProfile.domain i)) := by
          unfold muRaw_l; rw [← map_pow, rootMultiplicity_map_eq]
          exact (le_rootMultiplicity_iff K.hM0s_ne).mpr ((pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2))
        simp only [muSub]; rw [Nat.cast_sub h2]
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, hM0s_sum]
    have hsub_sum : ∑ a ∈ S_fin, sub a = (S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ) := by
      rw [hsum_dom sub (fun a h => by dsimp [sub]; rw [K.ptOf_out h]; rfl)]
      have hrew : (S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) - (K.mLCnt : ℤ) =
          ∑ i : Idx, ((if D.k i = 2 ∧ S.isU0 i then (1 : ℤ) else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
            (if K.isMbad i then 1 else 0) - (if K.isML i then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _
      dsimp [sub]; rw [K.ptOf_dom i]
      by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
        simp only [isNorm, isML, isMbad, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> dsimp only [muSub] <;> omega
    rw [hsub_sum]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hmu1_sum, ?_, hLam_sum, hdin_sum, hdmL_sum, ?_, ?_, hp1_sum, ?_, hc_sum, he1_sum⟩
  · -- m0
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ) =
        ∑ i : Idx, ((if D.k i = 0 then (1 : ℤ) else 0) + (if D.k i = 1 then 1 else 0) - (if D.k i = 1 ∧ S.isU0 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.m0] <;> omega
  · -- mbad
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.mbadCnt : ℤ) = ∑ i : Idx, (if K.isMbad i then (1 : ℤ) else 0) := K.mbadCnt_Z
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;> by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, isMbad, hU, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.mbad] <;> omega
  · -- m1
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (S.n1U : ℤ) = ∑ i : Idx, (if D.k i = 1 ∧ S.isU0 i then (1 : ℤ) else 0) := n1U_Z
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.m1] <;> omega
  · -- m2
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ) =
        ∑ i : Idx, ((if D.k i = 2 then (1 : ℤ) else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.m2] <;> omega
  · -- k3
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (S.n3U : ℤ) = ∑ i : Idx, (if 3 ≤ D.k i ∧ S.isU0 i then (1 : ℤ) else 0) := n3U_Z
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i]
    by_cases hU : S.isU0 i <;>
      simp only [hU, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.k3] <;> omega
  · -- mL0
    rw [hsum_dom _ (fun a h => by rw [K.ptOf_out h]; rfl)]
    have hrew : (K.mLCnt : ℤ) - (K.dmLCnt : ℤ) =
        ∑ i : Idx, ((if K.isML i then (1 : ℤ) else 0) - (if D.k i = 2 ∧ K.isML i ∧ K.isD1 i then 1 else 0) -
          (if 3 ≤ D.k i ∧ K.isML i ∧ K.isD1 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z]
      simp only [dmLCnt, Nat.cast_add]; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; rw [K.ptOf_dom i, hd2_dom i]
    by_cases hU : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
      by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
      by_cases hm : K.M0s.eval (BinaryIRSProfile.domain i ^ 2) = 0 <;>
      simp only [isNorm, isML, hU, hD1, hg, hm, ne_eq, not_true_eq_false, not_false_eq_true,
        and_true, and_false, true_and, false_and, ↓reduceIte] <;>
      (try split_ifs) <;> simp [Step15Pt.mL0, Step15Pt.isML] <;> omega
  · -- muO
    have hsplit : ∀ a ∈ S_fin, ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) =
        (K.muEx_l a : ℤ) - ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ) := fun a _ => by
      generalize K.ptOf a = p; generalize K.d2_l a = d; generalize K.muEx_l a = m
      cases p <;> simp only [Step15Pt.muO, Step15Pt.mu1, ↓reduceIte] <;> (try split_ifs) <;> omega
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hmuEx_sum, hmu1_sum]
  · -- d2oth
    have hsplit : ∀ a ∈ S_fin, ((K.ptOf a).d2oth (K.d2_l a) : ℤ) =
        (K.d2_l a : ℤ) - ((K.ptOf a).din (K.d2_l a) : ℤ) - ((K.ptOf a).dmL (K.d2_l a) : ℤ) := fun a _ => by
      have hd := K.d2_l_le_one a
      generalize K.ptOf a = p; generalize K.d2_l a = d at hd ⊢
      cases p <;> simp only [Step15Pt.d2oth, Step15Pt.din, Step15Pt.dmL, Step15Pt.isML,
        Bool.false_eq_true, false_and, true_and, ↓reduceIte] <;> (try split_ifs) <;> omega
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hD1_sum, hdin_sum, hdmL_sum]
  · -- L0
    rw [hsum_dom _ (fun a h => by unfold L0_l; rw [dif_neg h]; rfl)]
    have hrew : 2 * (S.ntU : ℤ) = ∑ i : Idx, (2 * (if S.isU0 i then ((D.k i - 3 : ℕ) : ℤ) else 0)) := by
      rw [← Finset.mul_sum]; apply congrArg (2 * ·); unfold KerD45Syzygy.ntU; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    unfold L0_l; rw [dif_pos ⟨i, rfl⟩]
    have hch : Classical.choose (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
      BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
    rw [hch]
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> (try split_ifs) <;> omega
  · -- LnoU
    rw [hsum_dom _ (fun a h => by unfold LnoU_l; rw [dif_neg h]; rfl)]
    have hrew : 2 * ((D.nt : ℤ) - (S.ntU : ℤ)) =
        ∑ i : Idx, (2 * (((D.k i - 3 : ℕ) : ℤ) - (if S.isU0 i then ((D.k i - 3 : ℕ) : ℤ) else 0))) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]; apply congrArg (2 * ·)
      have h1 : (D.nt : ℤ) = ∑ i : Idx, ((D.k i - 3 : ℕ) : ℤ) := nt_Z
      have h2 : (S.ntU : ℤ) = ∑ i : Idx, (if S.isU0 i then ((D.k i - 3 : ℕ) : ℤ) else 0) := by
        unfold KerD45Syzygy.ntU; exact sum_ite_nat_Z (fun i => D.k i - 3) _ _
      rw [h1, h2]
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    unfold LnoU_l; rw [dif_pos ⟨i, rfl⟩]
    have hch : Classical.choose (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
      BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
    rw [hch]
    by_cases hU : S.isU0 i <;> simp only [hU, not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte] <;> (try split_ifs) <;> omega

/-- Master `B1_holds` (`HK.derivative = 0`, NO ODE needed!): proves the exact degree equality AND both `0C_0` and `0C_1` global bounds! -/
theorem b1_holds_bounds (hHK' : K.HK.derivative = 0) :
    K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree - 4 * S.D1.natDegree =
      (D.gj 2).natDegree + K.g2rem.natDegree ∧
    2 * (((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ)) ≤
      2 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 7 * (K.mbadCnt : ℤ) -
      8 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 10 * (S.n3U : ℤ) -
      13 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) + 2 * (K.mu1Cnt : ℤ) +
      10 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
      9 * (K.Lam1.natDegree : ℤ) + 2 * (K.dinCnt : ℤ) - 16 * (K.dmLCnt : ℤ) +
      2 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
      5 * (2 * (S.ntU : ℤ)) - 5 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ))) ∧
    2 * (((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ)) ≤
      2 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 3 * (K.mbadCnt : ℤ) -
      8 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 2 * (S.n3U : ℤ) -
      9 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) + 2 * (K.mu1Cnt : ℤ) +
      10 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
      5 * (K.Lam1.natDegree : ℤ) + 10 * (K.dinCnt : ℤ) - 16 * (K.dmLCnt : ℤ) +
      2 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
      (2 * (S.ntU : ℤ)) - (2 * ((D.nt : ℤ) - (S.ntU : ℤ))) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  obtain ⟨c0, _, _, hc0, _, _, _, _, hd1, _, _, _⟩ := Ndom_decomp
  obtain ⟨r, hr⟩ := (derivative_eq_zero_iff_sq K.HK).mp hHK'
  have hr_u : IsUnit r := K.HK_sqfree r (by rw [hr, sq])
  have hHK_u : IsUnit K.HK := by rw [hr]; exact hr_u.pow 2
  have hHK_deg : K.HK.natDegree = 0 := natDegree_eq_zero_of_isUnit hHK_u
  have hwr := K.HK_wronskian hd1
  rw [hHK', mul_zero, add_zero] at hwr
  have hdeg_eq : K.M0eff.natDegree + 2 * K.Lam1.natDegree + 10 * S.p.natDegree - 4 * S.D1.natDegree =
      (D.gj 2).natDegree + K.g2rem.natDegree := by
    have h1 := congrArg Polynomial.natDegree K.HK_decomp
    rw [natDegree_mul (mul_ne_zero K.M0eff_ne D.g2_ne_zero) K.g2rem_ne,
      natDegree_mul K.M0eff_ne D.g2_ne_zero,
      natDegree_mul (pow_ne_zero 2 K.SK_ne) K.HK_ne, natDegree_pow, hHK_deg, add_zero] at h1
    have h2 := congrArg Polynomial.natDegree hwr
    have hp1c := mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne
    have hLc := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
    rw [natDegree_mul (pow_ne_zero 2 K.SK_ne) (mul_ne_zero (C_ne_zero.mpr hc0) K.HK_ne),
      natDegree_pow, natDegree_mul (C_ne_zero.mpr hc0) K.HK_ne, natDegree_C, hHK_deg,
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c)) hLc,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c),
      natDegree_mul (pow_ne_zero 2 K.M0eff_ne) (pow_ne_zero 6 S.D1_ne_zero),
      natDegree_pow, natDegree_pow, natDegree_pow, natDegree_comp_X_sq, natDegree_comp_X_sq] at h2
    have hp := K.natDegree_p_eq; omega
  let S_fin : Finset E :=
    Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ∪
    ((K.M0s.comp (X ^ 2)).map ι).roots.toFinset ∪ ((K.Lam1.comp (X ^ 2)).map ι).roots.toFinset ∪
    ((K.p1.comp (X ^ 2)).map ι).roots.toFinset ∪ (S.D1.map ι).roots.toFinset ∪
    (K.g2rem.map ι).roots.toFinset ∪ ((D.gj 2).map ι).roots.toFinset
  have hsums := K.sum_step15_cols S_fin
    (fun i => by simp [S_fin, ι, E])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
  have hpt_0C : ∀ a ∈ S_fin,
      (2 * ((K.c_l a : ℤ) - (K.e1_l a : ℤ)) ≤
        2 * ((K.ptOf a).m0 : ℤ) + 7 * ((K.ptOf a).mbad : ℤ) - 8 * ((K.ptOf a).m2 : ℤ) -
        10 * ((K.ptOf a).k3 : ℤ) - 13 * ((K.ptOf a).mL0 (K.d2_l a) : ℤ) +
        2 * ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ) +
        10 * ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) +
        9 * (K.lam_l a : ℤ) + 2 * ((K.ptOf a).din (K.d2_l a) : ℤ) -
        16 * ((K.ptOf a).dmL (K.d2_l a) : ℤ) + 2 * ((K.ptOf a).d2oth (K.d2_l a) : ℤ) -
        5 * (K.L0_l a : ℤ) - 5 * (K.LnoU_l a : ℤ)) ∧
      (2 * ((K.c_l a : ℤ) - (K.e1_l a : ℤ)) ≤
        2 * ((K.ptOf a).m0 : ℤ) + 3 * ((K.ptOf a).mbad : ℤ) - 8 * ((K.ptOf a).m2 : ℤ) -
        2 * ((K.ptOf a).k3 : ℤ) - 9 * ((K.ptOf a).mL0 (K.d2_l a) : ℤ) +
        2 * ((K.ptOf a).mu1 (K.d2_l a) (K.muEx_l a) : ℤ) +
        10 * ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) +
        5 * (K.lam_l a : ℤ) + 10 * ((K.ptOf a).din (K.d2_l a) : ℤ) -
        16 * ((K.ptOf a).dmL (K.d2_l a) : ℤ) + 2 * ((K.ptOf a).d2oth (K.d2_l a) : ℤ) -
        (K.L0_l a : ℤ) - (K.LnoU_l a : ℤ)) := fun a _ => by
    have hc := K.local_step15_core a
    have hb0 : K.b_l a = 0 := by
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      have hHKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.HK_ne
      have h0 : (K.HK.map ι).natDegree = 0 := by rw [natDegree_map_eq_of_injective ι.injective, hHK_deg]
      have hle := natDegree_le_of_dvd (pow_rootMultiplicity_dvd (K.HK.map ι) a) hHKE
      rw [natDegree_pow, natDegree_X_sub_C, mul_one, h0, hι] at hle; dsimp [b_l]; omega
    have hg_eq : K.g_l a = (K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a := by
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) hwr
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C] at h1
      have hSKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.SK_ne
      have hHKE := (Polynomial.map_ne_zero_iff ι.injective).mpr K.HK_ne
      have hME := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne
      have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
      have hp1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne)
      have hLE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne)
      have hc0E : (C (ι c0) : E[X]) ≠ 0 := C_ne_zero.mpr (by intro h0; exact hc0 (ι.injective (by rw [map_zero]; exact h0)))
      rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hSKE) (mul_ne_zero hc0E hHKE)),
        rootMultiplicity_mul (mul_ne_zero hc0E hHKE), rootMultiplicity_C, zero_add,
        rootMultiplicity_pow_eq' _ hSKE 2 a,
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)) hLE),
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)),
        rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)),
        rootMultiplicity_pow_eq' _ hME 2 a, rootMultiplicity_pow_eq' _ hD1E 6 a,
        rootMultiplicity_pow_eq' _ hp1E 5 a,
        K.M0eff_rm_eq_mVal a, rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a,
        rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne a] at h1
      rw [hι] at h1; dsimp [b_l, g_l, lam_l, d2_l, a1_l] at hb0 h1 ⊢; omega
    have htot_0C : K.c_l a + K.e1_l a = (K.ptOf a).mVal + 2 * K.lam_l a + 6 * K.d2_l a + 10 * K.a1_l a := by
      have := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    by_cases hmb : K.ptOf a = .k2U_mb ∨ K.ptOf a = .k3U_mb
    · have hd0 : K.d2_l a = 0 := hc.2.2.2.2.2.2.1 (Or.inr hmb)
      have ha0 : K.a1_l a = 0 :=
        hc.2.2.2.2.2.2.2.1 (hmb.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hd0
      have hLn0 : K.LnoU_l a = 0 := by by_contra h; have := hc.2.2.2.2.2.1 (by omega); rcases hmb with h' | h' <;> rw [h'] at this <;> cases this
      rcases hmb with hpt | hpt
      · have hL0z : K.L0_l a = 0 := by by_contra h; rcases hc.2.2.2.2.1 (by omega) with h' | h' | h' <;> rw [hpt] at h' <;> cases h'
        have htot' : K.c_l a + K.e1_l a = 1 + 2 * K.lam_l a := by
          rw [hpt, hd0, ha0] at htot_0C; simpa [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] using htot_0C
        have h0 := step15_mbad_0C_0 (k3 := 0) (mu_ex := K.muEx_l a) (by omega) hc.2.2.1 (fun _ => hL0z) (fun h => by omega) htot'
        have h1 := step15_mbad_0C_1 (k3 := 0) (mu_ex := K.muEx_l a) (by omega) hc.2.2.1 (fun _ => hL0z) (fun h => by omega) htot'
        rw [hpt, hd0, hL0z, hLn0]
        rw [hL0z] at h0 h1
        simp only [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Bool.false_eq_true, false_and, ↓reduceIte, sub_zero_nr, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
        exact ⟨by linarith only [h0], by linarith only [h1]⟩
      · have hmu3 := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpt
        have htot' : K.c_l a + K.e1_l a = 1 + 2 * K.lam_l a := by
          rw [hpt, hd0, ha0] at htot_0C; simpa [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] using htot_0C
        have h0 := step15_mbad_0C_0 (k3 := 1) (by omega) hc.2.2.1 (fun h => by omega) (fun _ => hmu3) htot'
        have h1 := step15_mbad_0C_1 (k3 := 1) (by omega) hc.2.2.1 (fun h => by omega) (fun _ => hmu3) htot'
        rw [hpt, hd0, hLn0]
        simp only [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Bool.false_eq_true, false_and, ↓reduceIte, sub_zero_nr, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
        exact ⟨by linarith only [h0], by linarith only [h1]⟩
    · have hk3mb_f : K.ptOf a = .k3U_mb → 1 + K.L0_l a ≤ K.lam_l a + K.muEx_l a := fun h => absurd (Or.inr h) hmb
      exact ⟨step15_0C_0 (K.ptOf a) (K.L0_l a) (K.LnoU_l a) (K.a1_l a) (K.d2_l a) (K.muEx_l a) (K.lam_l a) (K.e1_l a) (K.c_l a)
          hc.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hk3mb_f hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 htot_0C hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
        step15_0C_1 (K.ptOf a) (K.L0_l a) (K.LnoU_l a) (K.a1_l a) (K.d2_l a) (K.muEx_l a) (K.lam_l a) (K.e1_l a) (K.c_l a)
          hc.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hk3mb_f hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 htot_0C hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hs0 := Finset.sum_le_sum (fun a ha => (hpt_0C a ha).1)
  have hs1 := Finset.sum_le_sum (fun a ha => (hpt_0C a ha).2)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs0 hs1
  rw [hsums.1, hsums.2.1, hsums.2.2.2.1, hsums.2.2.2.2.1, hsums.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at hs0 hs1
  exact ⟨hdeg_eq, hs0, hs1⟩

/-- Master `ODE_holds` theorem (`zRaw c0 c1 Hrem Qpoly = 0`): proves `row358`, `row359`, `row0A`, AND under `W2a` proves `W2a1` or `W2a2` with `rowC04`! -/
theorem ode_holds_bounds {c0 c1 : Fld} {L : Fld[X]} (hc0 : c0 ≠ 0)
    (hNdom : Ndom = C c0 * X + C c1 * X ^ 2 + L ^ 4)
    (hNdom_deg : Ndom.natDegree = N) (hL4 : 4 * L.natDegree = N)
    (hd1 : Ndom.derivative = C c0)
    (hz : zRaw c0 c1 K.Hrem K.Qpoly = 0) :
    ((D.n1 - K.d2k1UCnt) + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt ≤ K.Lam1.natDegree + K.M0s.natDegree) ∧
    ((D.n1 : ℤ) - (K.d2k1UCnt : ℤ) + (K.mLCnt : ℤ) ≤
      (K.Lam1.natDegree : ℤ) + ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ))) ∧
    (2 * (((D.gj 2).natDegree : ℤ) - (K.g2rem.natDegree : ℤ)) ≤
      2 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 4 * (K.mbadCnt : ℤ) -
      11 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 4 * (S.n3U : ℤ) -
      10 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) +
      11 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
      6 * (K.Lam1.natDegree : ℤ) + 6 * (K.dinCnt : ℤ) - 4 * (K.dmLCnt : ℤ) +
      ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
      2 * (2 * (S.ntU : ℤ)) - 2 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ)))) ∧
    (K.HK.derivative ≠ 0 →
      (3 * (N : ℤ) + 2 * ((D.gj 2).natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ) - 2 * (K.Lam1.natDegree : ℤ) -
        10 * (S.p.natDegree : ℤ) + 4 * (S.D1.natDegree : ℤ) ≤
        4 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 4 * (K.mbadCnt : ℤ) -
        4 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 4 * (S.n3U : ℤ) -
        4 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) +
        4 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
        4 * (K.Lam1.natDegree : ℤ) + 4 * (K.dinCnt : ℤ) +
        4 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
        2 * (2 * (S.ntU : ℤ)) - 2 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ)))) ∨
      (4 * (N : ℤ) + ((D.gj 2).natDegree : ℤ) - ((D.gj 1).natDegree : ℤ) +
        2 * (K.K1.natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ) ≤
        4 * ((D.n0 : ℤ) + (D.n1 : ℤ) - (S.n1U : ℤ)) + 4 * (K.mbadCnt : ℤ) -
        4 * ((D.n2 : ℤ) - (S.n2U : ℤ) + (D.n3 : ℤ) - (S.n3U : ℤ)) - 4 * (S.n3U : ℤ) -
        4 * ((K.mLCnt : ℤ) - (K.dmLCnt : ℤ)) +
        4 * ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ) - (K.mu1Cnt : ℤ)) +
        4 * (K.Lam1.natDegree : ℤ) + 4 * (K.dinCnt : ℤ) +
        4 * ((S.D1.natDegree : ℤ) - (K.dinCnt : ℤ) - (K.dmLCnt : ℤ)) -
        2 * (2 * (S.ntU : ℤ)) - 2 * (2 * ((D.nt : ℤ) - (S.ntU : ℤ))))) := by
  classical
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  -- Extract minimal 4th-power denominator C0 and ODE decomposition Hrem * C0^4 = Qpoly * (fA^4 + (c0 X + c1 X^2) fB^4)!
  obtain ⟨C0, hC0_ne, ⟨R_ode, hR_ode⟩, hC0_rm⟩ := exists_minimal_fourth_pow_denom K.Hrem K.Qpoly K.Hrem_ne K.Qpoly_ne
  have hode_R := zRaw_eq_zero_imp_poly_ode K.Qpoly_ne hz hR_ode
  have hpow4_Fld : ∀ x : Fld, ∃ y : Fld, y ^ 4 = x := fun x =>
    ⟨(frobEquiv Fld).symm ((frobEquiv Fld).symm x), by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, frobEquiv_symm_sq, frobEquiv_symm_sq]⟩
  obtain ⟨fA, fB, hfAB⟩ := char2_poly_ode_decomp hc0 hpow4_Fld hode_R
  have hPQ_AB : K.Hrem * C0 ^ 4 = K.Qpoly * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4) := by
    rw [hR_ode, hfAB]
  -- Exact cancelled 4th-power Wronskian-ODE identity:
  -- C c0 * (Ndom * D.gj 2)^2 * (fA + L * fB)^4 = (sqrtPoly M0s)^2 * D1^6 * p1(X^2)^5 * Lam1(X^2) * C0^4!
  have hwr4 : C c0 * (Ndom * D.gj 2) ^ 2 * (fA + L * fB) ^ 4 =
      (sqrtPoly K.M0s) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) * C0 ^ 4 := by
    have h1 := char2_wronskian_ode_fourth_pow hNdom hPQ_AB
    have h2 := congrArg (· * K.Shit3 ^ 4) h1
    have h3 := congrArg (· * C0 ^ 4) (K.Hrem_Q_wronskian hd1)
    have hcomb : C c0 * (K.Shit3 ^ 2 * K.Qpoly) ^ 2 * (fA + L * fB) ^ 4 =
        (K.M0 * sqrtPoly K.M0s * Ndom) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) * C0 ^ 4 := by
      calc C c0 * (K.Shit3 ^ 2 * K.Qpoly) ^ 2 * (fA + L * fB) ^ 4
          = (C c0 * K.Qpoly ^ 2 * (fA + L * fB) ^ 4) * K.Shit3 ^ 4 := by ring
        _ = (Ndom * (K.Hrem.derivative * K.Qpoly + K.Hrem * K.Qpoly.derivative) + C c0 * K.Hrem * K.Qpoly) *
              C0 ^ 4 * K.Shit3 ^ 4 := by rw [← h1]
        _ = K.Shit3 ^ 4 * (Ndom * (K.Hrem.derivative * K.Qpoly + K.Hrem * K.Qpoly.derivative) +
              C c0 * K.Hrem * K.Qpoly) * C0 ^ 4 := by ring
        _ = (K.M0 * sqrtPoly K.M0s * Ndom) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) * C0 ^ 4 := h3
    have hSQ : K.Shit3 ^ 2 * K.Qpoly = K.M0 * Ndom ^ 2 * D.gj 2 := by
      unfold Qpoly; rw [K.Ndom_eq_M0_N1_Shit3]; ring
    rw [hSQ] at hcomb
    have hNdom_ne : Ndom ≠ 0 := by
      obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 K.M0_ne) (pow_ne_zero 2 hNdom_ne))
    linear_combination hcomb
  have hwr4_rhs_ne : (sqrtPoly K.M0s) ^ 2 * S.D1 ^ 6 * K.p1.comp (X ^ 2) ^ 5 * K.Lam1.comp (X ^ 2) * C0 ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (mt (sqrtPoly_eq_zero_iff K.M0s).mp K.hM0s_ne))
      (pow_ne_zero 6 S.D1_ne_zero))
      (pow_ne_zero 5 (mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne)))
      (mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne))
      (pow_ne_zero 4 hC0_ne)
  have hfAL_ne : fA + L * fB ≠ 0 := by
    intro h0; apply hwr4_rhs_ne; rw [← hwr4, h0, zero_pow (show (4 : ℕ) ≠ 0 by norm_num), mul_zero]
  -- Pointwise hSmod, hb1, and hode at EVERY a ∈ E!
  have hpt_ode_all : ∀ a : E,
      (K.g_l a % 2 = ((K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a) % 2) ∧
      ((K.ptOf a).nu = 1 → K.b_l a = 1 → K.g_l a + 2 ≤ (K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a) ∧
      ((K.ptOf a).mbad = 0 →
        (K.ptOf a).vChat (K.muEx_l a) (K.e1_l a) (K.c_l a) % 4 ≠ 1 ∧
        (K.ptOf a).vChat (K.muEx_l a) (K.e1_l a) (K.c_l a) % 4 ≠ 2) := by
    intro a
    have hc := K.local_step15_core a
    -- Mod-4 valuation of Hrem + 3 * Qpoly!
    have hmod4 : ((K.Hrem.map ι).rootMultiplicity a + 3 * (K.Qpoly.map ι).rootMultiplicity a) % 4 = 0 ∨
        ((K.Hrem.map ι).rootMultiplicity a + 3 * (K.Qpoly.map ι).rootMultiplicity a) % 4 = 1 := by
      have hzE : zRaw (ι c0) (ι c1) (K.Hrem.map ι) (K.Qpoly.map ι) = 0 := by
        rw [zRaw_map, hz, Polynomial.map_zero]
      exact ode_mod4_of_zRaw_zero (by intro h0; exact hc0 (ι.injective (by rw [map_zero]; exact h0)))
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.Hrem_ne)
        ((Polynomial.map_ne_zero_iff ι.injective).mpr K.Qpoly_ne) hzE a
    -- Exact mod-2 parity of c_l a from hwr4!
    have hc_mod2 : (K.c_l a + (K.ptOf a).nu) % 2 = (K.muRaw_l a + 3 * K.d2_l a + 5 * K.a1_l a + K.lam_l a) % 2 := by
      have h1 := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) hwr4
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C] at h1
      have hNdom_ne : Ndom ≠ 0 := by obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
      have hNE := (Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne
      have hg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
      have hfE := (Polynomial.map_ne_zero_iff ι.injective).mpr hfAL_ne
      have hc0E : (C (ι c0) : E[X]) ≠ 0 := C_ne_zero.mpr (by intro h0; exact hc0 (ι.injective (by rw [map_zero]; exact h0)))
      have hsME := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (sqrtPoly_eq_zero_iff K.M0s).mp K.hM0s_ne)
      have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
      have hp1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne)
      have hLE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne)
      have hC0E := (Polynomial.map_ne_zero_iff ι.injective).mpr hC0_ne
      rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hc0E (pow_ne_zero 2 (mul_ne_zero hNE hg2E))) (pow_ne_zero 4 hfE)),
        rootMultiplicity_mul (mul_ne_zero hc0E (pow_ne_zero 2 (mul_ne_zero hNE hg2E))),
        rootMultiplicity_C, zero_add,
        rootMultiplicity_pow_eq' _ (mul_ne_zero hNE hg2E) 2 a,
        rootMultiplicity_mul (mul_ne_zero hNE hg2E),
        rootMultiplicity_pow_eq' _ hfE 4 a,
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)) hLE) (pow_ne_zero 4 hC0E)),
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)) hLE),
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)),
        rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hsME) (pow_ne_zero 6 hD1E)),
        rootMultiplicity_pow_eq' _ hsME 2 a, rootMultiplicity_pow_eq' _ hD1E 6 a,
        rootMultiplicity_pow_eq' _ hp1E 5 a, rootMultiplicity_pow_eq' _ hC0E 4 a,
        rootMultiplicity_sqrtPoly_map K.M0s K.hM0s_ne a,
        rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a,
        rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne a] at h1
      have hN_rm : (Ndom.map ι).rootMultiplicity a = (K.ptOf a).nu := by
        unfold Ndom; rw [show (∏ i : Idx, (X - C (BinaryIRSProfile.domain i))) = linProd Finset.univ from rfl, linProd_rm]
        by_cases h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
        · rcases h with ⟨i, rfl⟩; rw [if_pos ⟨i, Finset.mem_univ i, rfl⟩, K.ptOf_dom i]; split_ifs <;> rfl
        · rw [if_neg (fun ⟨i, _, hi⟩ => h ⟨i, hi⟩), K.ptOf_out h]; rfl
      rw [hN_rm] at h1
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      rw [hι] at h1; dsimp [c_l, muRaw_l, d2_l, a1_l, lam_l] at h1 ⊢; omega
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [hι] at hmod4
    have hvsub := K.v_Q_sub_Hrem a
    have htot := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hb_le := hc.2.1
    have hSmod : K.g_l a % 2 = ((K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a) % 2 := by omega
    have hb1 : (K.ptOf a).nu = 1 → K.b_l a = 1 → K.g_l a + 2 ≤ (K.ptOf a).mVal + K.lam_l a + 3 * K.d2_l a + 5 * K.a1_l a := by
      intro hnu1 hb1'
      have hNa : (Ndom.map ι).eval a = 0 := by
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h; rw [K.ptOf_out h] at hnu1; cases hnu1
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hev⟩ := Ndom_decomp
        exact (hev a).mpr hdom
      have hHa : (K.HK.map ι).eval a = 0 := by
        have hge1 : 1 ≤ (K.HK.map ι).rootMultiplicity a := by rw [hι]; dsimp [b_l] at hb1'; omega
        have hd := (pow_dvd_pow (X - C a) hge1).trans (pow_rootMultiplicity_dvd (K.HK.map ι) a)
        rw [pow_one] at hd; exact dvd_iff_isRoot.mp hd
      have hd1E : (Ndom.map ι).derivative = C (ι c0) := by rw [derivative_map, hd1, Polynomial.map_C]
      have hsq_dvd := wronskian_sq_dvd_of_common_root hd1E a hNa hHa
      have hwr := congrArg (Polynomial.map ι) (K.HK_wronskian hd1)
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, ← derivative_map] at hwr
      have hRHS_ne : (K.M0eff.map ι) ^ 2 * (S.D1.map ι) ^ 6 * ((K.p1.comp (X ^ 2)).map ι) ^ 5 *
          ((K.Lam1.comp (X ^ 2)).map ι) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero
          (pow_ne_zero 2 ((Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne))
          (pow_ne_zero 6 ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero)))
          (pow_ne_zero 5 ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne))))
          ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne))
      have hd_tot : (X - C a) ^ (2 * K.g_l a + 2) ∣ (K.M0eff.map ι) ^ 2 * (S.D1.map ι) ^ 6 *
          ((K.p1.comp (X ^ 2)).map ι) ^ 5 * ((K.Lam1.comp (X ^ 2)).map ι) := by
        rw [← hwr, pow_add, mul_comm 2 (K.g_l a), pow_mul]
        have hg_eq' : K.g_l a = (K.SK.map ι).rootMultiplicity a := by rw [hι]; rfl
        rw [hg_eq']
        exact mul_dvd_mul (pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd (K.SK.map ι) a) 2) hsq_dvd
      have hle := (le_rootMultiplicity_iff hRHS_ne).mpr hd_tot
      have hME := (Polynomial.map_ne_zero_iff ι.injective).mpr K.M0eff_ne
      have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
      have hp1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hp1_ne)
      have hLE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp K.hLam1_ne)
      rw [rootMultiplicity_mul hRHS_ne,
        rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)) (pow_ne_zero 5 hp1E)),
        rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hME) (pow_ne_zero 6 hD1E)),
        rootMultiplicity_pow_eq' _ hME 2 a, rootMultiplicity_pow_eq' _ hD1E 6 a,
        rootMultiplicity_pow_eq' _ hp1E 5 a,
        K.M0eff_rm_eq_mVal a, rootMultiplicity_comp_X_sq_map K.p1 K.hp1_ne a,
        rootMultiplicity_comp_X_sq_map K.Lam1 K.hLam1_ne a] at hle
      rw [hι] at hle; dsimp [lam_l, d2_l, a1_l] at hSmod hle ⊢; omega
    have hode_vChat : (K.ptOf a).mbad = 0 →
        (K.ptOf a).vChat (K.muEx_l a) (K.e1_l a) (K.c_l a) % 4 ≠ 1 ∧
        (K.ptOf a).vChat (K.muEx_l a) (K.e1_l a) (K.c_l a) % 4 ≠ 2 := fun hmb0 => by
      rw [hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hmb0]; omega
    exact ⟨hSmod, hb1, hode_vChat⟩
  -- Key ODE_holds bonus: at EVERY k=1, U=0, d2=0 point, 1 ≤ v_T(Lam1 * M0s)!
  have hk1U_bonus : ∀ i : Idx, D.k i = 1 → S.isU0 i → ¬ K.isD1 i →
      1 ≤ (K.Lam1 * K.M0s).rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
    intro i hk1 hU hD1
    by_contra h0
    have hrm0 : (K.Lam1 * K.M0s).rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 := by omega
    rw [rootMultiplicity_mul (mul_ne_zero K.hLam1_ne K.hM0s_ne)] at hrm0
    set a := ι (BinaryIRSProfile.domain i)
    have hpt : K.ptOf a = .k1U := by rw [K.ptOf_dom i]; simp [hk1, hU]
    have hd0 : K.d2_l a = 0 := by dsimp [d2_l, a]; rw [rootMultiplicity_map_eq]; exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hD1)
    have hlam0 : K.lam_l a = 0 := by dsimp [lam_l, a]; rw [← map_pow, rootMultiplicity_map_eq]; omega
    have hmu0 : K.muEx_l a = 0 := by
      have hM0 : K.M0s.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = 0 := (Nat.add_eq_zero.mp hrm0).2
      unfold muEx_l muRaw_l; rw [show a = ι (BinaryIRSProfile.domain i) from rfl, ← map_pow, rootMultiplicity_map_eq, hM0]
      exact Nat.zero_sub _
    have hc := K.local_step15_core a
    have ho := hpt_ode_all a
    have ha0 : K.a1_l a = 0 := hc.2.2.2.2.2.2.2.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpt)))))) hd0
    have he1 : 1 ≤ K.e1_l a := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpt (Or.inr hmu0)
    have hS := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have htot := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hSmod := ho.1
    have hb1 := ho.2.1
    have hode := ho.2.2 (by rw [hpt]; rfl)
    simp only [hpt, hd0, hlam0, hmu0, ha0] at hS htot hSmod hb1 hode
    simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
      Step15Pt.vChat, Step15Pt.isML] at hS htot hSmod hb1 hode
    have hb_le := hc.2.1
    rcases (show K.b_l a = 0 ∨ K.b_l a = 1 by omega) with hb | hb
    · rw [hb] at htot; omega
    · have := hb1 hb; omega
  -- Row 358 and Row 359 from hk1U_bonus!
  have hrow358 : (D.n1 - K.d2k1UCnt) + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt ≤
      K.Lam1.natDegree + K.M0s.natDegree := by
    let f : Idx → ℕ := fun i =>
      if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i then 1
      else if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)
      else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2)
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.Lam1 * K.M0s := fun i _ => by
      dsimp only [f]
      by_cases h1 : D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i
      · simp only [h1, ↓reduceIte]
        exact (pow_dvd_pow _ (hk1U_bonus i h1.1 h1.2.1 h1.2.2)).trans (pow_rootMultiplicity_dvd _ _)
      · simp only [h1, ↓reduceIte]
        exact K.pow_dvd_Lam1_mul_M0s i
    have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective (K.Lam1 * K.M0s) (mul_ne_zero K.hLam1_ne K.hM0s_ne) f hdvd
    rw [natDegree_mul K.hLam1_ne K.hM0s_ne] at hle
    have hU := S.U_counts_ineqs
    have hd2_le_n1 : K.d2k1UCnt ≤ D.n1 := by
      have hZ : (K.d2k1UCnt : ℤ) ≤ (D.n1 : ℤ) := by
        rw [K.d2k1UCnt_Z, n1_Z]
        apply Finset.sum_le_sum; intro i _
        by_cases hU' : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
          simp only [hU', hD1, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
          (try split_ifs) <;> omega
      omega
    have hZ : (((D.n1 : ℤ) - (K.d2k1UCnt : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
        (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
      have hrew : ((D.n1 : ℤ) - (K.d2k1UCnt : ℤ)) + (2 * (D.n2 : ℤ) - (S.n2U : ℤ)) +
          (4 * (D.n3 : ℤ) - (S.n3U : ℤ)) + 2 * (D.nt : ℤ) =
          ∑ i : Idx, ((if D.k i = 1 then (1 : ℤ) else 0) - (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
            2 * (if D.k i = 2 then 1 else 0) - (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
            4 * (if 3 ≤ D.k i then 1 else 0) - (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
            2 * ((D.k i - 3 : ℕ) : ℤ)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
      by_cases hU' : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        simp only [hU', hD1, ne_eq, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    have hleZ : (∑ i : Idx, (f i : ℤ)) ≤ (K.Lam1.natDegree : ℤ) + (K.M0s.natDegree : ℤ) := by exact_mod_cast hle
    rw [← hZ] at hleZ
    have h2 : S.n2U ≤ 2 * D.n2 := by have := hU.2.1; omega
    have h3 : S.n3U ≤ 4 * D.n3 := by have := hU.2.2.1; omega
    have hgoalZ : (((D.n1 - K.d2k1UCnt) + (2 * D.n2 - S.n2U) + (4 * D.n3 - S.n3U) + 2 * D.nt : ℕ) : ℤ) ≤
        ((K.Lam1.natDegree + K.M0s.natDegree : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_sub hd2_le_n1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_mul, Nat.cast_ofNat]
      linarith only [hleZ]
    exact_mod_cast hgoalZ
  have hrow359 : (D.n1 : ℤ) - (K.d2k1UCnt : ℤ) + (K.mLCnt : ℤ) ≤
      (K.Lam1.natDegree : ℤ) + ((K.M0s.natDegree : ℤ) - (S.n2U : ℤ) - (S.n3U : ℤ) - (K.mbadCnt : ℤ) + (K.mLCnt : ℤ)) := by
    let f : Idx → ℕ := fun i =>
      if D.k i = 1 ∧ S.isU0 i ∧ ¬ K.isD1 i then 1
      else if D.k i = 1 ∧ ¬ S.isU0 i then 1
      else if K.isMbad i then 2
      else if 2 ≤ D.k i ∧ S.isU0 i then 1
      else 0
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx), (X - C (BinaryIRSProfile.domain i ^ 2)) ^ f i ∣ K.Lam1 * K.M0s := fun i _ => by
      dsimp [f]; split_ifs with h1 h2 hmb hk2U
      · exact (pow_dvd_pow _ (hk1U_bonus i h1.1 h1.2.1 h1.2.2)).trans (pow_rootMultiplicity_dvd _ _)
      · have h := K.pow_dvd_Lam1_mul_M0s i; simp only [h2.1, h2.2, Nat.one_ne_zero, ↓reduceIte] at h; exact h
      · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hmb.1).trans (K.pow_dvd_M0s_mbad i hmb.2.1 hmb.2.2)) K.Lam1
      · have h := K.pow_dvd_Lam1_mul_M0s i
        simp only [hk2U.2, show ¬ D.k i ≤ 1 by have := hk2U.1; omega, ↓reduceIte] at h
        exact (pow_dvd_pow _ (by have := hk2U.1; omega : 1 ≤ 2 * D.k i - 3)).trans h
      · simp
    have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective (K.Lam1 * K.M0s) (mul_ne_zero K.hLam1_ne K.hM0s_ne) f hdvd
    rw [natDegree_mul K.hLam1_ne K.hM0s_ne] at hle
    have hZ : ((D.n1 : ℤ) - (K.d2k1UCnt : ℤ) + (S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ)) = ∑ i : Idx, (f i : ℤ) := by
      have hrew : (D.n1 : ℤ) - (K.d2k1UCnt : ℤ) + (S.n2U : ℤ) + (S.n3U : ℤ) + (K.mbadCnt : ℤ) =
          ∑ i : Idx, ((if D.k i = 1 then (1 : ℤ) else 0) - (if D.k i = 1 ∧ S.isU0 i ∧ K.isD1 i then 1 else 0) +
            (if D.k i = 2 ∧ S.isU0 i then 1 else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) +
            (if K.isMbad i then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← n0_Z, ← n1_Z, ← n2_Z, ← n3_Z, ← nt_Z, ← n1U_Z, ← n2U_Z, ← n3U_Z,
        ← K.mbadCnt_Z, ← K.mLCnt_Z, ← K.din2Cnt_Z, ← K.din3Cnt_Z, ← K.dmL2Cnt_Z, ← K.dmL3Cnt_Z,
        ← K.d2k1UCnt_Z, ← K.d2k0Cnt_Z, ← K.mu1Cnt_Z, ← K.ntUNorm_Z, ← K.ntUMbad_Z, ← K.ntUML_Z, ← K.muExK3_Z] <;> ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [f]
      by_cases hU' : S.isU0 i <;> by_cases hD1 : K.isD1 i <;>
        by_cases hg : K.g2t.eval (BinaryIRSProfile.domain i) = 0 <;>
        simp only [isMbad, hU', hD1, hg, ne_eq, not_true_eq_false, not_false_eq_true,
          and_true, and_false, true_and, false_and, ↓reduceIte] <;>
        (try split_ifs) <;> omega
    have hleZ : (∑ i : Idx, (f i : ℤ)) ≤ (K.Lam1.natDegree : ℤ) + (K.M0s.natDegree : ℤ) := by exact_mod_cast hle
    rw [← hZ] at hleZ; linarith only [hleZ]
  -- Global sum of 0A and C04 over S_fin!
  let S_fin : Finset E :=
    Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ∪
    ((K.M0s.comp (X ^ 2)).map ι).roots.toFinset ∪ ((K.Lam1.comp (X ^ 2)).map ι).roots.toFinset ∪
    ((K.p1.comp (X ^ 2)).map ι).roots.toFinset ∪ (S.D1.map ι).roots.toFinset ∪
    (K.g2rem.map ι).roots.toFinset ∪ ((D.gj 2).map ι).roots.toFinset ∪ (C0.map ι).roots.toFinset
  have hsums := K.sum_step15_cols S_fin
    (fun i => by simp [S_fin, ι, E])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
    (fun a ha => by simp [S_fin, ι, E, ha]) (fun a ha => by simp [S_fin, ι, E, ha])
  have hC0_sum : (∑ a ∈ S_fin, ((C0.map ι).rootMultiplicity a : ℤ)) = (C0.natDegree : ℤ) := by
    have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
    rw [hι]
    exact_mod_cast sum_rootMultiplicity_map_eq_natDegree C0 hC0_ne S_fin (fun a ha => by simp [S_fin, ι, E, ha])
  have hpt_0A_C04 : ∀ a ∈ S_fin,
      (2 * ((K.c_l a : ℤ) - (K.e1_l a : ℤ)) ≤
        2 * ((K.ptOf a).m0 : ℤ) + 4 * ((K.ptOf a).mbad : ℤ) - 11 * ((K.ptOf a).m2 : ℤ) -
        4 * ((K.ptOf a).k3 : ℤ) - 10 * ((K.ptOf a).mL0 (K.d2_l a) : ℤ) +
        11 * ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) + 6 * (K.lam_l a : ℤ) +
        6 * ((K.ptOf a).din (K.d2_l a) : ℤ) - 4 * ((K.ptOf a).dmL (K.d2_l a) : ℤ) +
        ((K.ptOf a).d2oth (K.d2_l a) : ℤ) - 2 * (K.L0_l a : ℤ) - 2 * (K.LnoU_l a : ℤ)) ∧
      ((4 * (C0.map ι).rootMultiplicity a : ℤ) ≤
        4 * ((K.ptOf a).m0 : ℤ) + 4 * ((K.ptOf a).mbad : ℤ) - 4 * ((K.ptOf a).m2 : ℤ) -
        4 * ((K.ptOf a).k3 : ℤ) - 4 * ((K.ptOf a).mL0 (K.d2_l a) : ℤ) +
        4 * ((K.ptOf a).muO (K.d2_l a) (K.muEx_l a) : ℤ) + 4 * (K.lam_l a : ℤ) +
        4 * ((K.ptOf a).din (K.d2_l a) : ℤ) + 4 * ((K.ptOf a).d2oth (K.d2_l a) : ℤ) -
        2 * (K.L0_l a : ℤ) - 2 * (K.LnoU_l a : ℤ)) := fun a _ => by
    have hc := K.local_step15_core a
    have ho := hpt_ode_all a
    have hC0_a : (4 * (C0.map ι).rootMultiplicity a : ℤ) =
        (Step15Pt.c04Val (((K.Qpoly.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ) -
          ((K.Hrem.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a : ℤ)) : ℤ) := by
      have hι : ι = algebraMap Fld (AlgebraicClosure Fld) := rfl
      rw [hι]; exact_mod_cast hC0_rm a
    rw [hC0_a]
    by_cases hmb : K.ptOf a = .k2U_mb ∨ K.ptOf a = .k3U_mb
    · have hd0 : K.d2_l a = 0 := hc.2.2.2.2.2.2.1 (Or.inr hmb)
      have ha0 : K.a1_l a = 0 :=
        hc.2.2.2.2.2.2.2.1 (hmb.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hd0
      have hLn0 : K.LnoU_l a = 0 := by by_contra h; have := hc.2.2.2.2.2.1 (by omega); rcases hmb with h' | h' <;> rw [h'] at this <;> cases this
      have hv := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rcases hmb with h | h <;> rw [h] <;> rfl)
      rw [← hv]
      have hS := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have htot := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hb1 := ho.2.1
      rcases hmb with hpt | hpt
      · have hL0z : K.L0_l a = 0 := by by_contra h; rcases hc.2.2.2.2.1 (by omega) with h' | h' | h' <;> rw [hpt] at h' <;> cases h'
        simp only [hpt, hd0, ha0] at hS htot hb1
        simp only [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] at hS htot hb1
        have h0 := step15_mbad_0A (k3 := 0) (mu_ex := K.muEx_l a) (by omega) hc.2.1 hc.2.2.1 (fun _ => hL0z) (fun h => by omega)
          (by omega) (fun hb' => by have := hb1 trivial hb'; omega) (by omega)
        have h1 := step15_mbad_C04 (k3 := 0) (mu_ex := K.muEx_l a) (by omega) hc.2.1 hc.2.2.1 (fun _ => hL0z) (fun h => by omega)
          (by omega) (fun hb' => by have := hb1 trivial hb'; omega) (by omega)
        rw [hpt, hd0, hL0z, hLn0]
        rw [hL0z] at h0 h1
        simp only [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Bool.false_eq_true, false_and, ↓reduceIte, sub_zero_nr, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
        exact ⟨by linarith only [h0], by linarith only [h1]⟩
      · have hmu3 := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpt
        simp only [hpt, hd0, ha0] at hS htot hb1
        simp only [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2] at hS htot hb1
        have h0 := step15_mbad_0A (k3 := 1) (by omega) hc.2.1 hc.2.2.1 (fun h => by omega) (fun _ => hmu3)
          (by omega) (fun hb' => by have := hb1 trivial hb'; omega) (by omega)
        have h1 := step15_mbad_C04 (k3 := 1) (by omega) hc.2.1 hc.2.2.1 (fun h => by omega) (fun _ => hmu3)
          (by omega) (fun hb' => by have := hb1 trivial hb'; omega) (by omega)
        rw [hpt, hd0, hLn0]
        simp only [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Bool.false_eq_true, false_and, ↓reduceIte, sub_zero_nr, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
        exact ⟨by linarith only [h0], by linarith only [h1]⟩
    · have hmb0 : (K.ptOf a).mbad = 0 := by
        cases hpt : K.ptOf a <;> first | rfl | exact absurd (Or.inl hpt) hmb | exact absurd (Or.inr hpt) hmb
      have hv := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hmb0
      rw [← hv]
      have hk3mb_f : K.ptOf a = .k3U_mb → 1 + K.L0_l a ≤ K.lam_l a + K.muEx_l a := fun h => absurd (Or.inr h) hmb
      have hk2mb_f : K.ptOf a = .k2U_mb → 2 ≤ K.muEx_l a := fun h => absurd (Or.inl h) hmb
      have hk3mb_m : K.ptOf a = .k3U_mb → 3 + K.L0_l a / 2 ≤ K.muEx_l a := fun h => absurd (Or.inr h) hmb
      exact ⟨step15_0A (K.ptOf a) (K.L0_l a) (K.LnoU_l a) (K.a1_l a) (K.d2_l a) (K.muEx_l a) (K.lam_l a)
          (K.g_l a) (K.b_l a) (K.e1_l a) (K.c_l a)
          hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hk3mb_f hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho.1 ho.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho.2.2 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
        step15_C04 (K.ptOf a) (K.L0_l a) (K.LnoU_l a) (K.a1_l a) (K.d2_l a) (K.muEx_l a) (K.lam_l a)
          (K.g_l a) (K.b_l a) (K.e1_l a) (K.c_l a)
          hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hk3mb_f hk2mb_f hk3mb_m hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho.1 ho.2.1
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ho.2.2 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have h0A_sum := Finset.sum_le_sum (fun a ha => (hpt_0A_C04 a ha).1)
  have hC04_sum := Finset.sum_le_sum (fun a ha => (hpt_0A_C04 a ha).2)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h0A_sum hC04_sum
  rw [hsums.1, hsums.2.1, hsums.2.2.2.1, hsums.2.2.2.2.1, hsums.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at h0A_sum
  rw [hC0_sum, hsums.1, hsums.2.1, hsums.2.2.2.1, hsums.2.2.2.2.1, hsums.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.1, hsums.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsums.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hC04_sum
  refine ⟨hrow358, hrow359, h0A_sum, fun hHK'_ne => ?_⟩
  -- Show fB ≠ 0 whenever HK' ≠ 0!
  have hfB_ne : fB ≠ 0 := by
    intro hfB0; apply hHK'_ne
    rw [hfB0, zero_pow (show (4 : ℕ) ≠ 0 by norm_num), mul_zero, add_zero] at hPQ_AB
    have hsq : (K.Shit3 ^ 2 * K.Qpoly * fA ^ 2) ^ 2 = (K.M0 * sqrtPoly K.M0s * K.Sg2 * K.SK * C0 ^ 2) ^ 2 * K.HK := by
      have hbr := K.Hrem_Q_bridge
      have h1 : Ndom * (K.g2t * D.gj 2) = K.Sg2 ^ 2 * K.SK ^ 2 * K.HK := by
        calc Ndom * (K.g2t * D.gj 2) = (K.M0eff * K.Sg2) * (K.Sg2 * K.g2rem * D.gj 2) := by
              rw [← K.Ndom_eq_M0eff_Sg2, ← K.g2t_eq_Sg2_mul_g2rem]
          _ = K.Sg2 ^ 2 * (K.M0eff * D.gj 2 * K.g2rem) := by ring
          _ = K.Sg2 ^ 2 * K.SK ^ 2 * K.HK := by rw [K.HK_decomp]; ring
      rw [mul_assoc _ Ndom, h1] at hbr
      calc (K.Shit3 ^ 2 * K.Qpoly * fA ^ 2) ^ 2
          = K.Shit3 ^ 4 * K.Qpoly * (K.Qpoly * fA ^ 4) := by ring
        _ = K.Shit3 ^ 4 * K.Qpoly * (K.Hrem * C0 ^ 4) := by rw [← hPQ_AB]
        _ = (K.Shit3 ^ 4 * (K.Hrem * K.Qpoly)) * C0 ^ 4 := by ring
        _ = (K.M0 * sqrtPoly K.M0s * K.Sg2 * K.SK * C0 ^ 2) ^ 2 * K.HK := by rw [hbr]; ring
    have hd := congrArg Polynomial.derivative hsq
    rw [char2_derivative_sq, derivative_mul, char2_derivative_sq, zero_mul, zero_add] at hd
    have hfac_ne : (K.M0 * sqrtPoly K.M0s * K.Sg2 * K.SK * C0 ^ 2) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero K.M0_ne
        (mt (sqrtPoly_eq_zero_iff K.M0s).mp K.hM0s_ne)) K.Sg2_ne) K.SK_ne) (pow_ne_zero 2 hC0_ne))
    exact (mul_eq_zero.mp hd.symm).resolve_left hfac_ne
  have hL_ge : 1 ≤ L.natDegree := by
    have hN4 : 4 ≤ N := by norm_num [N]
    omega
  rcases char2_wronskian_ode_W2a_dichotomy hL_ge hfB_ne hC0_ne K.Qpoly_ne hPQ_AB with ⟨_, hW1⟩ | hW2
  · left
    have hNdom_ne : Ndom ≠ 0 := by obtain ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩ := Ndom_decomp; exact hne
    have hdeg_wr := congrArg Polynomial.natDegree hwr4
    have hp1c := mt (comp_X_sq_eq_zero_iff K.p1).mp K.hp1_ne
    have hLc := mt (comp_X_sq_eq_zero_iff K.Lam1).mp K.hLam1_ne
    have hsM := mt (sqrtPoly_eq_zero_iff K.M0s).mp K.hM0s_ne
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hc0) (pow_ne_zero 2 (mul_ne_zero hNdom_ne D.g2_ne_zero))) (pow_ne_zero 4 hfAL_ne),
      natDegree_mul (C_ne_zero.mpr hc0) (pow_ne_zero 2 (mul_ne_zero hNdom_ne D.g2_ne_zero)),
      natDegree_C, zero_add, natDegree_pow, natDegree_mul hNdom_ne D.g2_ne_zero, hNdom_deg, natDegree_pow,
      natDegree_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsM) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c)) hLc) (pow_ne_zero 4 hC0_ne),
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hsM) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c)) hLc,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 hsM) (pow_ne_zero 6 S.D1_ne_zero)) (pow_ne_zero 5 hp1c),
      natDegree_mul (pow_ne_zero 2 hsM) (pow_ne_zero 6 S.D1_ne_zero),
      natDegree_pow, natDegree_pow, natDegree_pow, natDegree_pow,
      natDegree_sqrtPoly, natDegree_comp_X_sq, natDegree_comp_X_sq] at hdeg_wr
    have hp := K.natDegree_p_eq
    linarith [hC04_sum, show (3 * (N : ℤ) + 2 * ((D.gj 2).natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ) -
      2 * (K.Lam1.natDegree : ℤ) - 10 * (S.p.natDegree : ℤ) + 4 * (S.D1.natDegree : ℤ)) ≤ 4 * (C0.natDegree : ℤ) by omega]
  · right
    have hQdeg : K.Qpoly.natDegree = 3 * K.M0.natDegree + 2 * K.N1.natDegree + (D.gj 2).natDegree := by
      unfold Qpoly
      rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 K.M0_ne) (pow_ne_zero 2 K.N1_ne)) D.g2_ne_zero,
        natDegree_mul (pow_ne_zero 3 K.M0_ne) (pow_ne_zero 2 K.N1_ne), natDegree_pow, natDegree_pow]
    have hNsum : K.M0.natDegree + K.N1.natDegree + K.Shit3.natDegree = N := by
      have h := congrArg Polynomial.natDegree K.Ndom_eq_M0_N1_Shit3
      rw [hNdom_deg, natDegree_mul (mul_ne_zero K.M0_ne K.N1_ne) K.Shit3_ne,
        natDegree_mul K.M0_ne K.N1_ne] at h; exact h.symm
    have hHrdeg : K.N1.natDegree + 3 * K.Shit3.natDegree + K.Hrem.natDegree = 2 * K.M0s.natDegree + K.g2t.natDegree := by
      have h := congrArg Polynomial.natDegree K.Hraw_eq_N1_Shit3_Hrem
      rw [natDegree_mul (mt (comp_X_sq_eq_zero_iff K.M0s).mp K.hM0s_ne) K.hg2t_ne, natDegree_comp_X_sq,
        natDegree_mul (mul_ne_zero K.N1_ne (pow_ne_zero 3 K.Shit3_ne)) K.Hrem_ne,
        natDegree_mul K.N1_ne (pow_ne_zero 3 K.Shit3_ne), natDegree_pow] at h; omega
    have hg1 := K.natDegree_g1_eq
    linarith [hC04_sum, show (4 * (N : ℤ) + ((D.gj 2).natDegree : ℤ) - ((D.gj 1).natDegree : ℤ) +
      2 * (K.K1.natDegree : ℤ) - 2 * (K.M0s.natDegree : ℤ)) ≤ 4 * (C0.natDegree : ℤ) by omega]

end KerD45KData
end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
