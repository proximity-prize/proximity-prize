import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401KerD2
import ProximityPrize.SubmissionBinaryLower.B6401FarkasVerifier
import ProximityPrize.SubmissionBinaryLower.B6401HybridP64
import ProximityPrize.SubmissionBinaryLower.B6401IntFarkas
import ProximityPrize.SubmissionBinaryLower.B6401IntSmallCerts
import ProximityPrize.SubmissionBinaryLower.B6401T4Rows
import ProximityPrize.SubmissionBinaryLower.B6401T4Grid
import ProximityPrize.SubmissionBinaryLower.B6401CertsT1
import ProximityPrize.SubmissionBinaryLower.B6401CertsT2
import ProximityPrize.SubmissionBinaryLower.B6401CertsT3
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4a
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4b1
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4b2
import ProximityPrize.SubmissionBinaryLower.B6401SmallAlg
import ProximityPrize.SubmissionBinaryLower.B6401ResLineOrd
import ProximityPrize.SubmissionBinaryLower.B6401QuotBridge
import ProximityPrize.SubmissionBinaryLower.B6401ListAndMCA
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

/-!
# Exact Local Orders, Global Resultant Non-Vanishing, & Single-Point Surplus (`B6401PointSurplus`)

Provides the foundation for `B6401FactorBound`:
1. Fast `decide` side-bounds on certificate tables (`certsT1_linear_caps`, `*_ms_bound`).
2. Left-inverse local hom `invLocalHom`, unconditional `localShift_ne_zero`, and exact `(t, w)`-order `exactTwOrd`.
3. Monotonicity of `resOrdWeighted2Fast`, `resOrdExact`, `t3Vrf0Ord`, `t3_2BVrf0Sub`.
4. Global resultant non-vanishing over `Fld[Z][X]` (`resY_f0_f1_ne_zero_of_irred_deg1`,
   `exists_t_resY_ne_zero_of_irred_deg2`) and `evalZ` root counting.
5. Single-point surplus theorems `t1_surplus_of_point` (Table 1) and `t23_surplus_of_point`
   (Tables 2, 3, 2A, and 2B).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401PointSurplus

open Polynomial B6401Params B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6401FarkasVerifier B6401HybridP64 B6401IntFarkas
open B6401IntSmallCerts B6401T4Rows B6401T4Grid
open B6401CertsT1 B6401CertsT2 B6401CertsT3 B6401CertsT4a B6401CertsT4b1 B6401CertsT4b2
open B6401SmallAlg B6401ResLineOrd B6401QuotBridge B6401ListAndMCA
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

/-! ### Part 0: Fast `decide` Side-Bounds on Certificate Tables -/

theorem certsT1_linear_caps :
    certsT1.all (fun c =>
      c.m ≤ 3000 && c.s ≤ 300 &&
      (c.m == 0 ||
        (c.cap1.c1Bkt ≤ T4_C1_SUM && c.cap1.c0Bkt ≤ T4_C0_SUM &&
         (!c.hasCap2 || c.cap2.c1Bkt * 3850 + c.cap2.c0Bkt ≤ T4_Q2_SUM)))) = true := by
  decide

theorem certsT2_ms_bound :
    certsT2.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide

theorem certsT3_2B_ms_bound :
    certsT3_2B.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide

theorem certsT3All_ms_bound :
    ∀ c ∈ certsT3All, c.m ≤ 3000 ∧ c.s ≤ 300 := by
  have h0 : B6401CertsT3Part0.certsT3_0.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h1 : B6401CertsT3Part1.certsT3_1.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h2 : B6401CertsT3Part2.certsT3_2.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h3 : B6401CertsT3Part3.certsT3_3.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h4 : B6401CertsT3Part4.certsT3_4.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h5 : B6401CertsT3Part5.certsT3_5.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h6 : B6401CertsT3Part6.certsT3_6.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h7 : B6401CertsT3Part7.certsT3_7.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h8 : B6401CertsT3Part8.certsT3_8.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h9 : B6401CertsT3Part9.certsT3_9.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  intro c hc
  simp only [certsT3All, List.mem_append] at hc
  have hdec : ∀ {L : List T3Cert}, L.all (fun x => x.m ≤ 3000 && x.s ≤ 300) = true → c ∈ L →
      c.m ≤ 3000 ∧ c.s ≤ 300 := by
    intro L hL hm
    have := List.all_eq_true.mp hL c hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this
  rcases hc with (((((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc)
  · exact hdec h0 hc
  · exact hdec h1 hc
  · exact hdec h2 hc
  · exact hdec h3 hc
  · exact hdec h4 hc
  · exact hdec h5 hc
  · exact hdec h6 hc
  · exact hdec h7 hc
  · exact hdec h8 hc
  · exact hdec h9 hc

def binMsBound (bin : T4BinCert) : Bool :=
  bin.buckets.all fun b => b.m ≤ 3000 && b.s ≤ 300

theorem t4a_ms_bound (br : T4ABranch)
    (hvalid : match br with
      | .det | .p0Zero => True
      | .p0 m21Nz _ p0M10D4 q2M21M10 => m21Nz = false → p0M10D4 = true ∧ q2M21M10 = false
      | .b1c1 _ _ bCase => bCase < 6) :
    (t4aBins br).all binMsBound = true := by
  cases br with
  | det => decide
  | p0Zero => decide
  | p0 m21Nz rGt p0M10D4 q2M21M10 =>
      cases m21Nz <;> cases rGt <;> cases p0M10D4 <;> cases q2M21M10
      all_goals first | decide | (exfalso; have := hvalid rfl; simp at this)
  | b1c1 rGt r4g4 bCase =>
      cases rGt <;> cases r4g4 <;>
        (rcases (show bCase = 0 ∨ bCase = 1 ∨ bCase = 2 ∨ bCase = 3 ∨ bCase = 4 ∨ bCase = 5 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem t4b1_ms_bound (br : T4BBranch) (hr : br.rGt = false) (hq1 : br.q1Case < 3) (hode : br.odeCase < 7) :
    (t4b1Bins br).all binMsBound = true := by
  rcases br with ⟨rGt, vCan, q1Case, odeCase⟩
  dsimp only at hr hq1 hode; subst hr
  cases vCan <;>
    (rcases (show q1Case = 0 ∨ q1Case = 1 ∨ q1Case = 2 by omega) with rfl | rfl | rfl) <;>
    (rcases (show odeCase = 0 ∨ odeCase = 1 ∨ odeCase = 2 ∨ odeCase = 3 ∨ odeCase = 4 ∨ odeCase = 5 ∨ odeCase = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem t4b2_ms_bound (br : T4BBranch) (hr : br.rGt = true) (hq1 : br.q1Case < 3) (hode : br.odeCase < 7) :
    (t4b2Bins br).all binMsBound = true := by
  rcases br with ⟨rGt, vCan, q1Case, odeCase⟩
  dsimp only at hr hq1 hode; subst hr
  cases vCan <;>
    (rcases (show q1Case = 0 ∨ q1Case = 1 ∨ q1Case = 2 by omega) with rfl | rfl | rfl) <;>
    (rcases (show odeCase = 0 ∨ odeCase = 1 ∨ odeCase = 2 ∨ odeCase = 3 ∨ odeCase = 4 ∨ odeCase = 5 ∨ odeCase = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

/-! ### Part 1: Inverse Local Hom, `exactTwOrd`, & Monotonicity -/

private lemma char2_inv_w {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x0 y0 xv yv rv : R) :
    y0 + x0 * rv + (yv + y0 + (xv + x0) * rv) = yv + xv * rv := by
  linear_combination (y0 + x0 * rv) * h2

private lemma char2_inv_t {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x0 xv : R) :
    x0 ^ 2 + (xv ^ 2 + x0 ^ 2) = xv ^ 2 := by
  linear_combination x0 ^ 2 * h2

private lemma char2_inv_u {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x0 y0 xv yv rv : R) :
    y0 ^ 2 + ((yv + y0 + (xv + x0) * rv) ^ 2 + (xv ^ 2 + x0 ^ 2) * rv ^ 2) = yv ^ 2 := by
  linear_combination (y0 ^ 2 + yv * y0 + (yv + y0) * (xv + x0) * rv + (xv ^ 2 + xv * x0 + x0 ^ 2) * rv ^ 2) * h2

/-- Left-inverse ring hom `LocalPoly A →+* ContactPoly A` to `kerDLocalPoly x0 y0` in char 2. -/
noncomputable def invLocalHom {A : Type*} [CommRing A] (x0 y0 : A) :
    LocalPoly A →+* ContactPoly A :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (Polynomial.C.comp (Polynomial.C.comp Polynomial.C)) cR)
      (cY + cC y0 + (cX + cC x0) * cR))
    (cX ^ 2 + cC (x0 ^ 2))

lemma invLocalHom_locC {A : Type*} [CommRing A] (x0 y0 c : A) :
    invLocalHom x0 y0 (locC c) = cC c := by
  simp [invLocalHom, locC, cC]

lemma invLocalHom_kerDLocalPoly {A : Type*} [CommRing A] [CharP A 2] (x0 y0 : A)
    (e : ℕ × ℕ × ℕ × ℕ) :
    invLocalHom x0 y0 (kerDLocalPoly x0 y0 e) = kerDBasisPoly e := by
  have h2C : (2 : ContactPoly A) = 0 := by
    have h2A : (2 : A) = 0 := CharTwo.two_eq_zero
    have h1 : (2 : ContactPoly A) = cC (2 : A) := by
      unfold cC; simp [show (2 : A) = 1 + 1 by norm_num, show (2 : ContactPoly A) = 1 + 1 by norm_num]
    rw [h1, h2A]; simp [cC]
  have hR : invLocalHom x0 y0 locR = cR := by simp [invLocalHom, locR]
  have hW : invLocalHom x0 y0 locW = cY + cC y0 + (cX + cC x0) * cR := by simp [invLocalHom, locW]
  have hT : invLocalHom x0 y0 locT = cX ^ 2 + cC (x0 ^ 2) := by simp [invLocalHom, locT]
  have hU : invLocalHom x0 y0 localU =
      (cY + cC y0 + (cX + cC x0) * cR) ^ 2 + (cX ^ 2 + cC (x0 ^ 2)) * cR ^ 2 := by
    unfold localU; rw [map_add, map_pow, map_mul, map_pow, hW, hT, hR]
  unfold kerDLocalPoly kerDBasisPoly
  simp only [map_mul, map_pow, map_add, invLocalHom_locC, hR, hW, hT, hU]
  have hw : cC y0 + cC x0 * cR + (cY + cC y0 + (cX + cC x0) * cR) = cY + cX * cR :=
    char2_inv_w h2C (cC x0) (cC y0) cX cY cR
  have ht : cC (x0 ^ 2) + (cX ^ 2 + cC (x0 ^ 2)) = cX ^ 2 := by
    have : cC (x0 ^ 2) = cC x0 ^ 2 := by unfold cC; simp [map_pow]
    rw [this]; exact char2_inv_t h2C (cC x0) cX
  have hu : cC (y0 ^ 2) + ((cY + cC y0 + (cX + cC x0) * cR) ^ 2 + (cX ^ 2 + cC (x0 ^ 2)) * cR ^ 2) = cY ^ 2 := by
    have hx : cC (x0 ^ 2) = cC x0 ^ 2 := by unfold cC; simp [map_pow]
    have hy : cC (y0 ^ 2) = cC y0 ^ 2 := by unfold cC; simp [map_pow]
    rw [hx, hy]; exact char2_inv_u h2C (cC x0) (cC y0) cX cY cR
  rw [hw, ht, hu]

theorem localShift_ne_zero {A : Type*} [CommRing A] [CharP A 2] {wY W d : ℕ}
    (x0 y0 : A) (f_coord : KerDIdx wY W d → A)
    (hFne : (∑ e : KerDIdx wY W d, cC (f_coord e) * kerDBasisPoly e.1) ≠ 0) :
    (∑ e : KerDIdx wY W d, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) ≠ 0 := by
  intro h0
  apply hFne
  have h1 := congrArg (invLocalHom x0 y0) h0
  rw [map_sum, map_zero] at h1
  convert h1 using 1
  apply Finset.sum_congr rfl; intro e _
  rw [map_mul, invLocalHom_locC, invLocalHom_kerDLocalPoly]

/-- Exact `(t, w)`-valuation of any `L : LocalPoly A` (exact whenever `L ≠ 0`). -/
noncomputable def exactTwOrd {A : Type*} [CommRing A] (L : LocalPoly A) : ℕ := by
  classical
  exact if h : ∃ n, ∃ p q, p + q = n ∧ twCoeff L p q ≠ 0 then Nat.find h else 0

lemma exists_twCoeff_ne_zero_of_ne_zero {A : Type*} [CommRing A] {L : LocalPoly A} (hL : L ≠ 0) :
    ∃ n, ∃ p q, p + q = n ∧ twCoeff L p q ≠ 0 := by
  have hp : ∃ p, L.coeff p ≠ 0 := by
    by_contra hall; push Not at hall; apply hL; rw [Polynomial.ext_iff]; intro p; exact hall p
  obtain ⟨p, hp⟩ := hp
  have hq : ∃ q, (L.coeff p).coeff q ≠ 0 := by
    by_contra hall; push Not at hall; apply hp; rw [Polynomial.ext_iff]; intro q; exact hall q
  obtain ⟨q, hq⟩ := hq
  exact ⟨p + q, p, q, rfl, hq⟩

theorem twOrdGE_exactTwOrd {A : Type*} [CommRing A] {L : LocalPoly A} (hL : L ≠ 0) :
    twOrdGE L (exactTwOrd L) := by
  classical
  have hex := exists_twCoeff_ne_zero_of_ne_zero hL
  unfold exactTwOrd; rw [dif_pos hex]
  intro p q hpq
  by_contra hnz
  exact Nat.find_min hex hpq ⟨p, q, rfl, hnz⟩

theorem exists_twCoeff_exactTwOrd {A : Type*} [CommRing A] {L : LocalPoly A} (hL : L ≠ 0) :
    ∃ p q, p + q = exactTwOrd L ∧ twCoeff L p q ≠ 0 := by
  classical
  have hex := exists_twCoeff_ne_zero_of_ne_zero hL
  unfold exactTwOrd; rw [dif_pos hex]
  exact Nat.find_spec hex

lemma twOrdGE_evalZLocal_sum {F : Type*} [Field F] {wY W d k : ℕ}
    (x0 : F) (y0 : Polynomial F) (f_coord : KerDIdx wY W d → Polynomial F) (z : F)
    (h : twOrdGE (∑ e : KerDIdx wY W d, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) k) :
    twOrdGE (∑ e : KerDIdx wY W d, locC ((f_coord e).eval z) * kerDLocalPoly x0 (y0.eval z) e.1) k := by
  have hev := twOrdGE_evalZLocal h z
  have hsum : evalZLocal (∑ e : KerDIdx wY W d, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) z =
      ∑ e : KerDIdx wY W d, locC ((f_coord e).eval z) * kerDLocalPoly x0 (y0.eval z) e.1 := by
    unfold evalZLocal; simp only [Polynomial.map_sum]
    apply Finset.sum_congr rfl; intro e _
    change evalZLocal (locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) z = _
    rw [evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly]
  rwa [hsum] at hev

lemma evalZContact_sum_kerD {F : Type*} [Field F] {wY W d : ℕ}
    (f_coord : KerDIdx wY W d → Polynomial F) (z : F) :
    evalZContact (∑ e : KerDIdx wY W d, cC (f_coord e) * kerDBasisPoly e.1) z =
      ∑ e : KerDIdx wY W d, cC ((f_coord e).eval z) * kerDBasisPoly e.1 := by
  unfold evalZContact; simp only [Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro e _
  change evalZContact (cC (f_coord e) * kerDBasisPoly e.1) z = _
  rw [show evalZContact (cC (f_coord e) * kerDBasisPoly e.1) z =
      evalZContact (cC (f_coord e)) z * evalZContact (kerDBasisPoly e.1) z
      from by unfold evalZContact; simp [Polynomial.map_mul],
    evalZContact_cC, evalZContact_kerDBasisPoly]

lemma resOrdWeighted2Fast_mono_mg_step (df mf dg mg : ℕ) :
    resOrdWeighted2Fast df mf dg mg ≤ resOrdWeighted2Fast df mf dg (mg + 1) := by
  unfold resOrdWeighted2Fast
  by_cases hdf : df = 0
  · subst hdf; simp
  by_cases hdg : dg = 0
  · subst hdg; simp only [zero_mul, Nat.zero_eq, beq_self_eq_true, Bool.or_true, ↓reduceIte,
      Nat.min_zero, Nat.not_lt_zero, Bool.and_false, Nat.sub_zero, add_zero, zero_add]
    split_ifs <;> nlinarith
  have hdf_b : (df == 0) = false := beq_false_of_ne hdf
  have hdg_b : (dg == 0) = false := beq_false_of_ne hdg
  simp only [hdf_b, hdg_b, Bool.false_eq_true, ↓reduceIte]
  set k := df * dg
  set a2 := dg * min df (mf / 2)
  set a1 := if mf % 2 == 1 && mf / 2 < df then dg else 0
  set b2 := df * min dg (mg / 2)
  set b1 := if mg % 2 == 1 && mg / 2 < dg then df else 0
  set b2' := df * min dg ((mg + 1) / 2)
  set b1' := if (mg + 1) % 2 == 1 && (mg + 1) / 2 < dg then df else 0
  have hstep : (b2' = b2 ∧ b1' ≤ b1 + df) ∨ (b2' = b2 + df ∧ b1 = df ∧ b1' = 0) := by
    by_cases hev : mg % 2 = 0
    · left
      have hd : (mg + 1) / 2 = mg / 2 := by omega
      dsimp only [b2', b2, b1', b1]; rw [hd]
      refine ⟨rfl, ?_⟩
      split_ifs <;> omega
    · have hodd : mg % 2 = 1 := by omega
      have hd : (mg + 1) / 2 = mg / 2 + 1 := by omega
      have hev1 : (mg + 1) % 2 = 0 := by omega
      by_cases hlt : mg / 2 < dg
      · right
        have hm1 : min dg (mg / 2) = mg / 2 := Nat.min_eq_right (by omega)
        have hm2 : min dg ((mg + 1) / 2) = mg / 2 + 1 := by rw [hd]; exact Nat.min_eq_right (by omega)
        dsimp only [b2', b2, b1', b1]
        rw [hm1, hm2]
        have h1 : ((mg % 2 == 1 && mg / 2 < dg) : Bool) = true := by simp [hodd, hlt]
        have h2 : (((mg + 1) % 2 == 1 && (mg + 1) / 2 < dg) : Bool) = false := by simp [hev1]
        rw [if_pos h1, if_neg (by simp [h2])]
        exact ⟨by ring, rfl, rfl⟩
      · left
        have hm1 : min dg (mg / 2) = dg := Nat.min_eq_left (by omega)
        have hm2 : min dg ((mg + 1) / 2) = dg := by rw [hd]; exact Nat.min_eq_left (by omega)
        dsimp only [b2', b2, b1', b1]
        rw [hm1, hm2]
        have h2 : (((mg + 1) % 2 == 1 && (mg + 1) / 2 < dg) : Bool) = false := by simp [hev1]
        rw [if_neg (by simp [h2])]
        exact ⟨rfl, by omega⟩
  set t2 := min k (a2 + b2)
  set t1 := min (k - t2) (a1 + b1)
  set t2' := min k (a2 + b2')
  set t1' := min (k - t2') (a1 + b1')
  have hgain : 2 * t2' + t1' ≤ 2 * t2 + t1 + df := by
    rcases hstep with ⟨h2eq, h1le⟩ | ⟨h2eq, hb1, hb1'⟩
    · have ht2 : t2' = t2 := by dsimp [t2', t2]; rw [h2eq]
      rw [ht2]; dsimp only [t1', t1]; omega
    · by_cases hfull : k ≤ a2 + b2
      · have h1 : t2 = k := Nat.min_eq_left hfull
        have h2 : t2' = k := Nat.min_eq_left (by omega)
        have h3 : t1 = 0 := by dsimp [t1]; rw [h1]; simp
        have h4 : t1' = 0 := by dsimp [t1']; rw [h2]; simp
        omega
      · have h1 : t2 = a2 + b2 := Nat.min_eq_right (by omega)
        have ht2_ge : t2 ≤ t2' := by dsimp [t2', t2]; rw [h2eq]; omega
        have ht2_le : t2' ≤ t2 + df := by dsimp [t2', t2]; rw [h2eq]; omega
        dsimp only [t1', t1]
        rw [hb1, hb1', add_zero]
        omega
  have hmul : df * (mg + 1) = df * mg + df := by ring
  rw [hmul]; omega

theorem resOrdWeighted2Fast_mono_mg (df mf dg : ℕ) {mg1 mg2 : ℕ} (h : mg1 ≤ mg2) :
    resOrdWeighted2Fast df mf dg mg1 ≤ resOrdWeighted2Fast df mf dg mg2 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (resOrdWeighted2Fast_mono_mg_step df mf dg _)

theorem resOrdExact_mono_mg (df mf dg : ℕ) {mg1 mg2 : ℕ} (h : mg1 ≤ mg2) :
    resOrdExact df mf dg mg1 ≤ resOrdExact df mf dg mg2 := by
  unfold resOrdExact
  split_ifs with h1 h2
  · exact le_rfl
  · exact Nat.mul_le_mul_left df h
  · have hstep : ∀ a b : ℕ, a ≤ b → df * a + (df - mf) * (dg - a) ≤ df * b + (df - mf) * (dg - b) := by
      intro a b hab
      induction hab with
      | refl => exact le_rfl
      | @step m _ ih =>
          refine ih.trans ?_
          have hle : df - mf ≤ df := Nat.sub_le _ _
          by_cases hmd : m < dg
          · have hsub : dg - m = (dg - (m + 1)) + 1 := by omega
            rw [Nat.succ_eq_add_one, hsub, mul_add, mul_one, mul_add, mul_one]; omega
          · have h0 : dg - m = 0 := by omega
            have h0' : dg - (m + 1) = 0 := by omega
            rw [Nat.succ_eq_add_one, h0, h0', mul_zero, add_zero, add_zero]; nlinarith
    have := hstep mg1 mg2 h; omega

private lemma foldl_min_le_foldl_min {α : Type*} (f g : α → ℕ) (l : List α)
    (hfg : ∀ x ∈ l, f x ≤ g x) (a b : ℕ) (hab : a ≤ b) :
    (l.map f).foldl Nat.min a ≤ (l.map g).foldl Nat.min b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (fun y hy => hfg y (List.mem_cons_of_mem _ hy)) _ _
        (min_le_min hab (hfg x List.mem_cons_self))

private lemma foldl_min_le_mem {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) (x : α) (hx : x ∈ l) :
    l.foldl (fun acc y => Nat.min acc (f y)) init ≤ f x := by
  induction l generalizing init with
  | nil => cases hx
  | cons a t ih =>
      simp only [List.foldl_cons, List.mem_cons] at hx ⊢
      rcases hx with rfl | ht
      · have hle : ∀ (l' : List α) (z : ℕ), l'.foldl (fun acc y => Nat.min acc (f y)) z ≤ z := by
          intro l'; induction l' with
          | nil => intro _; exact le_rfl
          | cons b bs ih' => intro z; simp only [List.foldl_cons]; exact (ih' _).trans (Nat.min_le_left _ _)
        exact (hle t _).trans (Nat.min_le_right _ _)
      · exact ih _ ht

private lemma foldl_map_min_le_mem {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) (x : α) (hx : x ∈ l) :
    (l.map f).foldl Nat.min init ≤ f x := by
  have hrew : ∀ (l' : List α) (z : ℕ), (l'.map f).foldl Nat.min z = l'.foldl (fun acc y => Nat.min acc (f y)) z := by
    intro l'; induction l' with
    | nil => intro _; rfl
    | cons a t ih => intro z; simp only [List.map_cons, List.foldl_cons]; exact ih _
  rw [hrew]; exact foldl_min_le_mem f l init x hx

theorem t3_2BVrf0Sub_mono (dSub k : ℕ) {r1 r2 : ℕ} (h : r1 ≤ r2) :
    t3_2BVrf0Sub dSub k r1 ≤ t3_2BVrf0Sub dSub k r2 := by
  unfold t3_2BVrf0Sub
  split_ifs
  · exact le_rfl
  · apply max_le_max
    · exact Nat.sub_le_sub_right (resOrdWeighted2Fast_mono_mg 11 (4 * k + 4) (dSub / 2) h) _
    · exact foldl_min_le_foldl_min _ _ _
        (fun d0 _ => Nat.add_le_add (resOrdExact_mono_mg d0 (2 * k - 2) dSub h)
          (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h _)))
        _ _ (Nat.add_le_add (resOrdExact_mono_mg 0 (2 * k - 2) dSub h)
          (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h _)))

theorem t3Vrf0Ord_mono_std (mode dg dStarEff k : ℕ) (hmode : mode ≠ 3) {r1 r2 : ℕ} (h : r1 ≤ r2) :
    t3Vrf0Ord mode dg dStarEff k r1 ≤ t3Vrf0Ord mode dg dStarEff k r2 := by
  unfold t3Vrf0Ord
  have hm3 : (mode == 3) = false := beq_false_of_ne hmode
  simp only [hm3, Bool.false_eq_true, ↓reduceIte]
  split_ifs
  · exact le_rfl
  · apply max_le_max
    · exact Nat.sub_le_sub_right (resOrdWeighted2Fast_mono_mg dStarEff (4 * k + 4) (dg / 2) h) _
    · exact foldl_min_le_foldl_min _ _ _
        (fun d0 _ => Nat.add_le_add (resOrdExact_mono_mg d0 (2 * k - 2) dg h)
          (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h _)))
        _ _ (Nat.add_le_add (resOrdExact_mono_mg 0 (2 * k - 2) dg h)
          (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h _)))
  · exact Nat.sub_le_sub_right (resOrdWeighted2Fast_mono_mg dStarEff (4 * k + 4) (dg / 2) h) _

theorem t3Vrf0Ord_mode3_le_min_two_mul (dg dStarEff k r_true : ℕ) :
    t3Vrf0Ord 3 dg dStarEff k (min (2 * k) r_true) ≤ t3Vrf0Ord 3 dg dStarEff k r_true := by
  by_cases hle : r_true ≤ 2 * k
  · rw [Nat.min_eq_right hle]
  · rw [Nat.min_eq_left (le_of_not_ge hle)]
    by_cases hk0 : k = 0
    · subst hk0; simp [t3Vrf0Ord]
    have hk0b : (k == 0) = false := beq_false_of_ne hk0
    unfold t3Vrf0Ord
    simp only [hk0b, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    let evalRq (tot rq : ℕ) : ℕ :=
      let rre := tot - rq
      let vk := (2 * resOrdWeighted2Fast (dStarEff / 2) (2 * k + 2) (dg / 2) rre - 2 * dg) + dStarEff * rq
      let vp0 := resOrdExact 0 (2 * k - 2) dg rre + dStarEff * (rre - dg)
      let vp := ((List.range (dStarEff + 1)).map (fun d0 =>
        resOrdExact d0 (2 * k - 2) dg rre + (dStarEff - d0) * (rre - dg))).foldl Nat.min vp0 + dStarEff * rq
      max vk vp
    have hmono_eval : ∀ rq1 rre1 rq2 rre2, rq1 ≤ rq2 → rre1 ≤ rre2 →
        evalRq (rq1 + rre1) rq1 ≤ evalRq (rq2 + rre2) rq2 := by
      intro rq1 rre1 rq2 rre2 hq hr
      dsimp only [evalRq]
      rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
      apply max_le_max
      · exact Nat.add_le_add
          (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 (resOrdWeighted2Fast_mono_mg _ _ _ hr)) _)
          (Nat.mul_le_mul_left _ hq)
      · exact Nat.add_le_add
          (foldl_min_le_foldl_min _ _ _
            (fun d0 _ => Nat.add_le_add (resOrdExact_mono_mg d0 _ dg hr)
              (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hr _)))
            _ _ (Nat.add_le_add (resOrdExact_mono_mg 0 _ dg hr)
              (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hr _))))
          (Nat.mul_le_mul_left _ hq)
    have hfold_ge : ∀ (l : List ℕ) (init : ℕ),
        (∀ rq2 ∈ l, rq2 ≤ r_true ∧ (r_true - rq2) % 2 = 0) →
        ((List.range (2 * k + 1)).filter (fun rq => (2 * k - rq) % 2 == 0)).foldl
            (fun acc rq => Nat.min acc (evalRq (2 * k) rq)) (evalRq (2 * k) (2 * k)) ≤ init →
        ((List.range (2 * k + 1)).filter (fun rq => (2 * k - rq) % 2 == 0)).foldl
            (fun acc rq => Nat.min acc (evalRq (2 * k) rq)) (evalRq (2 * k) (2 * k)) ≤
          l.foldl (fun acc rq => Nat.min acc (evalRq r_true rq)) init := by
      intro l
      induction l with
      | nil => intro init _ hinit; exact hinit
      | cons rq2 t ih =>
          intro init hl hinit
          simp only [List.foldl_cons]
          apply ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
          apply le_min hinit
          have ⟨hq2_le, hpar2⟩ := hl rq2 List.mem_cons_self
          set rre2 := r_true - rq2
          set rre1 := min (2 * k) rre2
          set rq1 := 2 * k - rre1
          have hmem1 : rq1 ∈ (List.range (2 * k + 1)).filter (fun rq => (2 * k - rq) % 2 == 0) := by
            rw [List.mem_filter]; refine ⟨List.mem_range.mpr (by omega), ?_⟩
            simp only [beq_iff_eq]
            have : 2 * k - rq1 = rre1 := by omega
            rw [this]; dsimp [rre1]; by_cases h2k : 2 * k ≤ rre2
            · rw [Nat.min_eq_left h2k]; omega
            · rw [Nat.min_eq_right (le_of_not_ge h2k)]; exact hpar2
          have h1 := foldl_min_le_mem (evalRq (2 * k)) _ (evalRq (2 * k) (2 * k)) rq1 hmem1
          have h2 : evalRq (2 * k) rq1 ≤ evalRq r_true rq2 := by
            have heq1 : rq1 + rre1 = 2 * k := by omega
            have heq2 : rq2 + rre2 = r_true := by omega
            rw [← heq1, ← heq2]
            exact hmono_eval rq1 rre1 rq2 rre2 (by dsimp [rq1, rre1, rre2]; omega) (Nat.min_le_right _ _)
          exact h1.trans h2
    apply hfold_ge
    · intro rq2 hrq2
      rw [List.mem_filter, List.mem_range] at hrq2
      simp only [beq_iff_eq] at hrq2
      exact ⟨by omega, hrq2.2⟩
    · have hle_init : ((List.range (2 * k + 1)).filter (fun rq => (2 * k - rq) % 2 == 0)).foldl
          (fun acc rq => Nat.min acc (evalRq (2 * k) rq)) (evalRq (2 * k) (2 * k)) ≤ evalRq (2 * k) (2 * k) := by
        have hmem : 2 * k ∈ (List.range (2 * k + 1)).filter (fun rq => (2 * k - rq) % 2 == 0) := by
          rw [List.mem_filter]; exact ⟨List.mem_range.mpr (by omega), by simp⟩
        exact foldl_min_le_mem (evalRq (2 * k)) _ _ (2 * k) hmem
      refine hle_init.trans ?_
      have h2 := hmono_eval (2 * k) 0 r_true 0 (by omega) le_rfl
      simpa only [add_zero] using h2

/-! ### Part 2: `evalZ` Root Counting & Global Resultant Non-Vanishing -/

lemma card_filter_eval_eq_zero_le (S : Finset Fld) (p : Polynomial Fld) (hp : p ≠ 0) :
    (S.filter fun z => p.eval z = 0).card ≤ p.natDegree := by
  have hsub : S.filter (fun z => p.eval z = 0) ⊆ p.roots.toFinset := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    exact hz.2
  exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))

lemma card_filter_evalZPoly_eq_zero_le (S : Finset Fld) (f : Polynomial (Polynomial Fld))
    {H : ℕ} (hf : f ≠ 0) (hH : ∀ i, (f.coeff i).natDegree ≤ H) :
    (S.filter fun z => f.map (Polynomial.evalRingHom z) = 0).card ≤ H := by
  have hex : ∃ i, f.coeff i ≠ 0 := by
    by_contra hall; push Not at hall; exact hf (Polynomial.ext hall)
  obtain ⟨i, hi⟩ := hex
  have hsub : S.filter (fun z => f.map (Polynomial.evalRingHom z) = 0) ⊆
      S.filter (fun z => (f.coeff i).eval z = 0) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    have hc := congrArg (fun p : Polynomial Fld => p.coeff i) hz.2
    simpa [Polynomial.coeff_map] using hc
  exact (Finset.card_le_card hsub).trans ((card_filter_eval_eq_zero_le S (f.coeff i) hi).trans (hH i))

lemma card_filter_evalZBiPoly_eq_zero_le (S : Finset Fld) (f : BiPoly (Polynomial Fld))
    {H : ℕ} (hf : f ≠ 0) (hH : ∀ j i, ((f.coeff j).coeff i).natDegree ≤ H) :
    (S.filter fun z => evalZBiPoly f z = 0).card ≤ H := by
  have hex : ∃ j, f.coeff j ≠ 0 := by
    by_contra hall; push Not at hall; exact hf (Polynomial.ext hall)
  obtain ⟨j, hj⟩ := hex
  have hsub : S.filter (fun z => evalZBiPoly f z = 0) ⊆
      S.filter (fun z => (f.coeff j).map (Polynomial.evalRingHom z) = 0) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    have hc := congrArg (fun p : BiPoly Fld => p.coeff j) hz.2
    simpa [evalZBiPoly, Polynomial.coeff_map] using hc
  exact (Finset.card_le_card hsub).trans (card_filter_evalZPoly_eq_zero_le S (f.coeff j) hj (hH j))

lemma wdegBi_coeff_le_of_wdeg {F : Type*} [Field F] {wY W : ℕ} {Fpoly : ContactPoly F}
    (hW : wdeg wY Fpoly ≤ W) (k : ℕ) (hne : Fpoly.coeff k ≠ 0) :
    wdegBi wY (Fpoly.coeff k) + k * (wY - 1) ≤ W := by
  have hsupp : (Fpoly.coeff k).support.Nonempty := Polynomial.support_nonempty.mpr hne
  have hle : wdegBi wY (Fpoly.coeff k) ≤ W - k * (wY - 1) := by
    rw [wdegBi_le_iff]; intro j i hnz
    have := (wdeg_le_iff wY W Fpoly).mp hW k j i hnz; omega
  have hkw : k * (wY - 1) ≤ W := by
    obtain ⟨j, hj⟩ := hsupp
    have hne_j : (Fpoly.coeff k).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have := (wdeg_le_iff wY W Fpoly).mp hW k j _ (Polynomial.leadingCoeff_ne_zero.mpr hne_j)
    omega
  omega

lemma wdegBi_le_of_wdeg_coeff {F : Type*} [Field F] {wY W : ℕ} {Fpoly : ContactPoly F}
    (hW : wdeg wY Fpoly ≤ W) (k : ℕ) :
    wdegBi wY (Fpoly.coeff k) ≤ W - k * (wY - 1) := by
  rw [wdegBi_le_iff]; intro j i hnz
  have := (wdeg_le_iff wY W Fpoly).mp hW k j i hnz; omega

lemma degZ_resultant_biPoly_le (f g : BiPoly (Polynomial Fld)) (df dg H : ℕ)
    (hf : ∀ j i, ((f.coeff j).coeff i).natDegree ≤ H)
    (hg : ∀ j i, ((g.coeff j).coeff i).natDegree ≤ H) :
    ∀ a, ((Polynomial.resultant f g df dg).coeff a).natDegree ≤ (df + dg) * H := by
  have hdeg_le : ∀ (p q : Polynomial (Polynomial Fld)) (d1 d2 : ℕ),
      (∀ i, (p.coeff i).natDegree ≤ d1) → (∀ i, (q.coeff i).natDegree ≤ d2) →
      ∀ i, ((p * q).coeff i).natDegree ≤ d1 + d2 := by
    intro p q d1 d2 hp hq i
    rw [Polynomial.coeff_mul]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun ab _ => ?_)
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hp ab.1) (hq ab.2))
  have hprod_le : ∀ (s : Finset (Fin (df + dg))) (u : Fin (df + dg) → Polynomial (Polynomial Fld)),
      (∀ x ∈ s, ∀ i, ((u x).coeff i).natDegree ≤ H) →
      ∀ i, ((∏ x ∈ s, u x).coeff i).natDegree ≤ s.card * H := by
    intro s u hu
    classical
    induction s using Finset.induction_on with
    | empty => intro i; simp [Polynomial.coeff_one]; split_ifs <;> simp
    | insert a s ha ih =>
        intro i
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.succ_mul, add_comm (s.card * H) H]
        exact hdeg_le _ _ H (s.card * H) (hu a (Finset.mem_insert_self _ _))
          (ih fun x hx => hu x (Finset.mem_insert_of_mem hx)) i
  intro a
  rw [Polynomial.resultant, Matrix.det_apply, finset_sum_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
  dsimp only [Function.comp_apply]
  rw [Units.smul_def, zsmul_eq_mul]
  have hsign : ∀ p : Polynomial (Polynomial Fld),
      ((((Equiv.Perm.sign σ : ℤ) : Polynomial (Polynomial Fld)) * p).coeff a).natDegree ≤ (p.coeff a).natDegree := by
    intro p
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
    · rw [h1]; simp
    · have hval : (Equiv.Perm.sign σ : ℤ) = -1 := by rw [h1]; rfl
      have hmul : ((-1 : ℤ) : Polynomial (Polynomial Fld)) * p = -p := by
        rw [Int.cast_neg, Int.cast_one]; ring
      rw [hval, hmul, Polynomial.coeff_neg, Polynomial.natDegree_neg]
  refine (hsign _).trans ?_
  refine (hprod_le Finset.univ (fun j => Polynomial.sylvester f g df dg (σ j) j) ?_ a).trans (by simp)
  intro j _ i
  simp only [Polynomial.sylvester, Matrix.of_apply]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) j
  · simp only [Fin.addCases_left]; split_ifs
    · exact hg _ i
    · simp
  · simp only [Fin.addCases_right]; split_ifs
    · exact hf _ i
    · simp

lemma evalZ_resultant_biPoly (f g : BiPoly (Polynomial Fld)) (df dg : ℕ) (z : Fld) :
    (Polynomial.resultant f g df dg).map (Polynomial.evalRingHom z) =
      Polynomial.resultant (evalZBiPoly f z) (evalZBiPoly g z) df dg := by
  have h := Polynomial.resultant_map_map f g df dg (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  simpa only [evalZBiPoly, Polynomial.coe_mapRingHom] using h.symm

private lemma exists_prim_associated_ratFunc_gen {K : Type*} [Field K]
    (pK : Polynomial (RatFunc K)) (hpK : pK ≠ 0) :
    ∃ p : BiPoly K, p.IsPrimitive ∧ p ≠ 0 ∧ p.natDegree = pK.natDegree ∧
      Associated (p.map (algebraMap (Polynomial K) (RatFunc K))) pK := by
  classical
  let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial K) (RatFunc K)
  have hclear : ∀ j : ℕ, ∃ (n d : Polynomial K), d ≠ 0 ∧ pK.coeff j * ι d = ι n := by
    intro j
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial K)) (pK.coeff j)
    exact ⟨n, d, nonZeroDivisors.ne_zero d.2, hd⟩
  choose num den hden_ne hden_eq using hclear
  let D : Polynomial K := ∏ j ∈ Finset.range (pK.natDegree + 1), den j
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hden_ne j
  let q : BiPoly K := ∑ j ∈ Finset.range (pK.natDegree + 1),
    Polynomial.monomial j (num j * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase j, den l)
  have hq_map : q.map ι = C (ι D) * pK := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
    by_cases hj : j < pK.natDegree + 1
    · have hj_mem : j ∈ Finset.range (pK.natDegree + 1) := Finset.mem_range.mpr hj
      dsimp only [q]
      rw [finset_sum_coeff, Finset.sum_eq_single j]
      · rw [Polynomial.coeff_monomial_same, map_mul, map_prod]
        have hD_split : D = den j * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase j, den l :=
          (Finset.mul_prod_erase _ _ hj_mem).symm
        rw [hD_split, map_mul, map_prod, ← hden_eq j]; ring
      · intro l _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro hnot; exact absurd hj_mem hnot
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : pK.natDegree < j), mul_zero]
      dsimp only [q]; rw [finset_sum_coeff]
      have h0 : (∑ x ∈ Finset.range (pK.natDegree + 1),
          (Polynomial.monomial x (num x * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase x, den l)).coeff j) = 0 := by
        apply Finset.sum_eq_zero; intro x hx
        have := Finset.mem_range.mp hx
        simp [Polynomial.coeff_monomial, show x ≠ j by omega]
      rw [h0, map_zero]
  have hq_ne : q ≠ 0 := by
    intro h0; rw [h0, Polynomial.map_zero] at hq_map
    have hDι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hDι) hpK) hq_map.symm
  let p : BiPoly K := q.primPart
  have hp_prim : p.IsPrimitive := q.isPrimitive_primPart
  have hp_ne : p ≠ 0 := q.primPart_ne_zero
  have hc_ne : q.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hq_ne
  have hq_eq : q = C q.content * p := q.eq_C_content_mul_primPart
  have hp_map : p.map ι = C (ι D * (ι q.content)⁻¹) * pK := by
    have hcι : ι q.content ≠ 0 := fun h => hc_ne (hι (by rwa [map_zero]))
    have hm := congrArg (Polynomial.map ι) hq_eq
    rw [hq_map, Polynomial.map_mul, Polynomial.map_C] at hm
    have hm' := congrArg (C (ι q.content)⁻¹ * ·) hm
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcι, map_one, one_mul] at hm'
    rw [← hm', mul_comm (ι D)]
  have hu : IsUnit (C (ι D * (ι q.content)⁻¹) : Polynomial (RatFunc K)) := by
    have hDι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
    have hcι : ι q.content ≠ 0 := fun h => hc_ne (hι (by rwa [map_zero]))
    exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (mul_ne_zero hDι (inv_ne_zero hcι)))
  obtain ⟨u, hu_eq⟩ := hu
  have hassoc : Associated (p.map ι) pK :=
    ⟨u⁻¹, by rw [hp_map, ← hu_eq, mul_comm (↑u : Polynomial (RatFunc K)) pK, mul_assoc, Units.mul_inv, mul_one]⟩
  have hdeg : p.natDegree = pK.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective hι, hp_map]
    exact Polynomial.natDegree_C_mul (by
      have hDι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
      have hcι : ι q.content ≠ 0 := fun h => hc_ne (hι (by rwa [map_zero]))
      exact mul_ne_zero hDι (inv_ne_zero hcι))
  exact ⟨p, hp_prim, hp_ne, hdeg, hassoc⟩

/-- If `F : ContactPoly K` is irreducible with `F.natDegree ≥ 1`, its `R`-coefficients have no
common non-unit divisor in `(RatFunc K)[Y]`! -/
theorem no_common_irred_factor_of_irred {K : Type*} [Field K] {F : ContactPoly K}
    (hirr : Irreducible F) (hdeg : 1 ≤ F.natDegree) :
    let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
    ∀ p : Polynomial (RatFunc K), (∀ k, p ∣ (F.coeff k).map ι) → IsUnit p := by
  classical
  intro ι p hp
  by_contra hnu
  have hp_ne : p ≠ 0 := by
    intro h0; subst h0
    have hF0 : F = 0 := by
      rw [Polynomial.ext_iff]; intro k
      have hk := zero_dvd_iff.mp (hp k)
      exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective (Polynomial K) (RatFunc K))).mp hk
    exact hirr.ne_zero hF0
  obtain ⟨q, hq_prim, hq_ne, hq_deg, hq_assoc⟩ := exists_prim_associated_ratFunc_gen p hp_ne
  have hq_pos : 0 < q.natDegree := by
    rw [hq_deg]
    by_contra h0
    have hd0 : p.natDegree = 0 := by omega
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hc0 : p.coeff 0 ≠ 0 := fun h => hp_ne (by rw [hC, h, map_zero])
    exact hnu (by rw [hC]; exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hc0))
  have hq_dvd : ∀ k, q ∣ F.coeff k := fun k =>
    hq_prim.dvd_of_fraction_map_dvd_fraction_map (hq_assoc.dvd.trans (hp k))
  choose c hc using hq_dvd
  let G : ContactPoly K := ∑ k ∈ Finset.range (F.natDegree + 1), Polynomial.monomial k (c k)
  have hF_eq : F = Polynomial.C q * G := by
    rw [Polynomial.ext_iff]; intro k
    rw [Polynomial.coeff_C_mul]
    dsimp only [G]; rw [finset_sum_coeff]
    by_cases hk : k < F.natDegree + 1
    · rw [Finset.sum_eq_single k]
      · simp [hc k]
      · intro l _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    · rw [Finset.sum_eq_zero, mul_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      intro l hl; have := Finset.mem_range.mp hl; simp [Polynomial.coeff_monomial, show l ≠ k by omega]
  rcases hirr.isUnit_or_isUnit hF_eq with huq | huG
  · have hqU : IsUnit q := by
      rcases huq with ⟨u, hu⟩
      have h1 := congrArg (fun r : ContactPoly K => r.coeff 0) u.mul_inv
      rw [hu, Polynomial.coeff_C_mul, Polynomial.coeff_one_zero] at h1
      exact isUnit_iff_exists_inv.mpr ⟨(↑u⁻¹ : ContactPoly K).coeff 0, h1⟩
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hqU
    omega
  · have hG0 := Polynomial.natDegree_eq_zero_of_isUnit huG
    have hF0 : F.natDegree = 0 := by
      rw [hF_eq, Polynomial.natDegree_C_mul hq_ne, hG0]
    omega

private theorem resY_f0_f1_ne_zero_of_irred_deg1_aux {K : Type*} [Field K]
    (F : ContactPoly K) (hirr : Irreducible F) (hdeg : F.natDegree = 1)
    (hd1 : 1 ≤ (F.coeff 1).natDegree) :
    F.coeff 0 ≠ 0 ∧ F.coeff 1 ≠ 0 ∧
    Polynomial.resultant (F.coeff 0) (F.coeff 1) (F.coeff 0).natDegree (F.coeff 1).natDegree ≠ 0 := by
  classical
  let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial K) (RatFunc K)
  have hFne : F ≠ 0 := hirr.ne_zero
  have hf1_ne : F.coeff 1 ≠ 0 := by
    rw [← hdeg, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hFne
  have hnoc := no_common_irred_factor_of_irred hirr (by omega)
  have hcop : IsCoprime ((F.coeff 0).map ι) ((F.coeff 1).map ι) := by
    refine EuclideanDomain.isCoprime_of_dvd ?_ ?_
    · rintro ⟨_, h1⟩; exact ((Polynomial.map_ne_zero_iff hι).mpr hf1_ne) h1
    · intro p hp _ hp0 hp1
      apply hp
      apply hnoc p
      intro k
      rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
      · exact hp0
      · exact hp1
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.map_zero]; exact dvd_zero p
  have hf0_ne : F.coeff 0 ≠ 0 := by
    intro h0
    have h1 : IsUnit ((F.coeff 1).map ι) := by
      rcases hcop with ⟨a, b, hab⟩
      rw [h0, Polynomial.map_zero, mul_zero, zero_add] at hab
      exact isUnit_iff_exists_inv.mpr ⟨b, by rw [mul_comm]; exact hab⟩
    have hd0 := Polynomial.natDegree_eq_zero_of_isUnit h1
    rw [Polynomial.natDegree_map_eq_of_injective hι] at hd0
    omega
  refine ⟨hf0_ne, hf1_ne, ?_⟩
  intro hres0
  have hresL : Polynomial.resultant ((F.coeff 0).map ι) ((F.coeff 1).map ι)
      ((F.coeff 0).map ι).natDegree ((F.coeff 1).map ι).natDegree = 0 := by
    rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
      Polynomial.resultant_map_map, hres0, map_zero]
  exact Polynomial.resultant_ne_zero _ _ hcop hresL

/-- For irreducible `F ∈ ContactPoly (Polynomial Fld)` of `deg_R = 1` with `1 ≤ (F.coeff 1).natDegree`:
`f0 ≠ 0`, `f1 ≠ 0`, AND `Res_Y(f0, f1; d0, d1) ≠ 0` in `Fld[Z][X]`! -/
theorem resY_f0_f1_ne_zero_of_irred_deg1 (Fpoly : ContactPoly (Polynomial Fld))
    (hirr : Irreducible (liftCRat Fpoly)) (hdeg : Fpoly.natDegree = 1)
    (hd1 : 1 ≤ (Fpoly.coeff 1).natDegree) :
    let f0 := Fpoly.coeff 0
    let f1 := Fpoly.coeff 1
    f0 ≠ 0 ∧ f1 ≠ 0 ∧
    Polynomial.resultant f0 f1 f0.natDegree f1.natDegree ≠ 0 := by
  intro f0 f1
  let alg : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have halg : Function.Injective alg := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have hmap_alg : Function.Injective (Polynomial.mapRingHom alg) := Polynomial.map_injective alg halg
  have hlift_bi : Function.Injective (liftBiRat (F := Fld)) :=
    Polynomial.map_injective _ hmap_alg
  have hdeg_rat : (liftCRat Fpoly).natDegree = 1 := by
    rw [liftCRat, Polynomial.coe_mapRingHom, Polynomial.natDegree_map_eq_of_injective hlift_bi, hdeg]
  have hcoeff : ∀ k, (liftCRat Fpoly).coeff k = (Fpoly.coeff k).map (Polynomial.mapRingHom alg) := fun k => by
    simp only [liftCRat, liftBiRat, Polynomial.coe_mapRingHom, Polynomial.coeff_map]; rfl
  have hd1_rat : 1 ≤ ((liftCRat Fpoly).coeff 1).natDegree := by
    rw [hcoeff 1, Polynomial.natDegree_map_eq_of_injective hmap_alg]; exact hd1
  have ⟨hf0_rat, hf1_rat, hres_rat⟩ := resY_f0_f1_ne_zero_of_irred_deg1_aux (liftCRat Fpoly) hirr hdeg_rat hd1_rat
  refine ⟨fun h0 => hf0_rat (by rw [hcoeff 0, show Fpoly.coeff 0 = 0 from h0, Polynomial.map_zero]),
    fun h1 => hf1_rat (by rw [hcoeff 1, show Fpoly.coeff 1 = 0 from h1, Polynomial.map_zero]),
    fun hres0 => hres_rat ?_⟩
  rw [hcoeff 0, hcoeff 1, Polynomial.natDegree_map_eq_of_injective hmap_alg,
    Polynomial.natDegree_map_eq_of_injective hmap_alg, Polynomial.resultant_map_map, hres0, map_zero]

private theorem exists_t_resY_ne_zero_of_irred_deg2_aux {K : Type*} [Field K]
    (cEmb0 : Fld →+* K) (hcEmb0 : Function.Injective cEmb0)
    (F : ContactPoly K) (hirr : Irreducible F) (hdeg : F.natDegree = 2)
    (hf1_ne : F.coeff 1 ≠ 0) (hf2_ne : F.coeff 2 ≠ 0)
    (hd0_le : (F.coeff 0).natDegree ≤ 25) :
    F.coeff 0 ≠ 0 ∧ ∃ t : Fld,
      let ht := F.coeff 1 + Polynomial.C (Polynomial.C (cEmb0 t)) * F.coeff 2
      ht ≠ 0 ∧ Polynomial.resultant (F.coeff 0) ht (F.coeff 0).natDegree ht.natDegree ≠ 0 := by
  classical
  let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial K) (RatFunc K)
  have hf0_ne : F.coeff 0 ≠ 0 := by
    intro h0
    have hFfac : F = Polynomial.X * (Polynomial.C (F.coeff 1) + Polynomial.C (F.coeff 2) * Polynomial.X) := by
      rw [Polynomial.ext_iff]; intro k
      cases k with
      | zero => simp [h0]
      | succ k' =>
          cases k' with
          | zero => simp
          | succ k'' =>
              cases k'' with
              | zero => simp
              | succ k''' =>
                  rw [Polynomial.coeff_X_mul, Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega),
                    zero_add, Polynomial.coeff_mul_X, Polynomial.coeff_C, if_neg (by omega),
                    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    rcases hirr.isUnit_or_isUnit hFfac with hX | hQ
    · have := Polynomial.natDegree_eq_zero_of_isUnit hX; simp at this
    · have hQdeg : (Polynomial.C (F.coeff 1) + Polynomial.C (F.coeff 2) * Polynomial.X).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hQ
      have h1 := congrArg (fun p : ContactPoly K => p.coeff 1)
        (Polynomial.eq_C_of_natDegree_eq_zero hQdeg)
      simp only [Polynomial.coeff_add, Polynomial.coeff_C, one_ne_zero, ↓reduceIte, zero_add,
        Polynomial.coeff_mul_X] at h1
      exact hf2_ne h1
  have hnoc := no_common_irred_factor_of_irred hirr (by omega)
  let f0L : Polynomial (RatFunc K) := (F.coeff 0).map ι
  let f1L : Polynomial (RatFunc K) := (F.coeff 1).map ι
  let f2L : Polynomial (RatFunc K) := (F.coeff 2).map ι
  have hf0L_ne : f0L ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf0_ne
  have hf1L_ne : f1L ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf1_ne
  have hf2L_ne : f2L ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf2_ne
  let cEmb : Fld →+* RatFunc K := ι.comp (Polynomial.C.comp cEmb0)
  have hcEmb_inj : Function.Injective cEmb :=
    hι.comp (Polynomial.C_injective.comp hcEmb0)
  let ts : Fin 27 → Fld := fun i => BinaryIRSProfile.domain ⟨i.val, lt_trans i.isLt (by norm_num)⟩
  have hts_inj : Function.Injective ts := fun i j hij => by
    have := BinaryIRSProfile.domain.injective hij
    exact Fin.ext (by simpa using congrArg Fin.val this)
  let facs : Finset (Polynomial (RatFunc K)) := (UniqueFactorizationMonoid.normalizedFactors f0L).toFinset
  have hbad_le1 : ∀ p ∈ facs, (Finset.univ.filter fun j : Fin 27 => p ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L).card ≤ 1 := by
    intro p hp
    have hp_mem : p ∈ UniqueFactorizationMonoid.normalizedFactors f0L := Multiset.mem_toFinset.mp hp
    have hp_irr : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp_mem
    have hp_dvd0 : p ∣ f0L := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp_mem
    refine Finset.card_le_one.mpr fun j1 hj1 j2 hj2 => ?_
    by_contra hne
    have hne_t : ts j1 ≠ ts j2 := fun h => hne (hts_inj h)
    have hd1 : p ∣ f1L + Polynomial.C (cEmb (ts j1)) * f2L := (Finset.mem_filter.mp hj1).2
    have hd2 : p ∣ f1L + Polynomial.C (cEmb (ts j2)) * f2L := (Finset.mem_filter.mp hj2).2
    have hsub : p ∣ Polynomial.C (cEmb (ts j1 - ts j2)) * f2L := by
      have h := dvd_sub hd1 hd2
      have heq : (f1L + Polynomial.C (cEmb (ts j1)) * f2L) - (f1L + Polynomial.C (cEmb (ts j2)) * f2L) =
          Polynomial.C (cEmb (ts j1 - ts j2)) * f2L := by
        rw [map_sub, map_sub]; ring
      rwa [heq] at h
    have hc_ne : cEmb (ts j1 - ts j2) ≠ 0 := fun h0 => sub_ne_zero.mpr hne_t (hcEmb_inj (h0.trans (map_zero cEmb).symm))
    have hp_dvd2 : p ∣ f2L := by
      rcases hsub with ⟨w, hw⟩
      refine ⟨Polynomial.C (cEmb (ts j1 - ts j2))⁻¹ * w, ?_⟩
      have h1 := congrArg (Polynomial.C (cEmb (ts j1 - ts j2))⁻¹ * ·) hw
      simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc_ne, map_one, one_mul] at h1
      rw [h1]; ring
    have hp_dvd1 : p ∣ f1L := by
      have h := dvd_sub hd1 (dvd_mul_of_dvd_right hp_dvd2 (Polynomial.C (cEmb (ts j1))))
      simpa using h
    apply hp_irr.not_isUnit
    apply hnoc p
    intro k
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · exact hp_dvd0
    · exact hp_dvd1
    · exact hp_dvd2
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.map_zero]; exact dvd_zero p
  have hbad_zero : (Finset.univ.filter fun j : Fin 27 => f1L + Polynomial.C (cEmb (ts j)) * f2L = 0).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun j1 hj1 j2 hj2 => ?_
    by_contra hne
    have hne_t : ts j1 ≠ ts j2 := fun h => hne (hts_inj h)
    have h1 := (Finset.mem_filter.mp hj1).2
    have h2 := (Finset.mem_filter.mp hj2).2
    have hdiff : Polynomial.C (cEmb (ts j1 - ts j2)) * f2L = 0 := by
      have := congrArg₂ (· - ·) h1 h2
      rw [sub_self] at this
      have heq : (f1L + Polynomial.C (cEmb (ts j1)) * f2L) - (f1L + Polynomial.C (cEmb (ts j2)) * f2L) =
          Polynomial.C (cEmb (ts j1 - ts j2)) * f2L := by rw [map_sub, map_sub]; ring
      rwa [heq] at this
    have hc_ne : cEmb (ts j1 - ts j2) ≠ 0 := fun h0 => sub_ne_zero.mpr hne_t (hcEmb_inj (h0.trans (map_zero cEmb).symm))
    exact hf2L_ne ((mul_eq_zero.mp hdiff).resolve_left (Polynomial.C_ne_zero.mpr hc_ne))
  have hfacs_card : facs.card ≤ 25 := by
    have h1 : facs.card ≤ (UniqueFactorizationMonoid.normalizedFactors f0L).card := Multiset.toFinset_card_le _
    have h2 : (UniqueFactorizationMonoid.normalizedFactors f0L).card ≤ f0L.natDegree := by
      have hprod := UniqueFactorizationMonoid.prod_normalizedFactors hf0L_ne
      obtain ⟨u, hu⟩ := hprod
      have hdeg_eq : ((UniqueFactorizationMonoid.normalizedFactors f0L).prod).natDegree = f0L.natDegree := by
        have hu0 : (u : Polynomial (RatFunc K)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
        have hpne : (UniqueFactorizationMonoid.normalizedFactors f0L).prod ≠ 0 := fun h0 =>
          hf0L_ne (by rw [← hu, h0, zero_mul])
        conv_rhs => rw [← hu]
        rw [Polynomial.natDegree_mul hpne u.ne_zero, hu0, add_zero]
      have hsum : ∀ (m : Multiset (Polynomial (RatFunc K))),
          (∀ p ∈ m, Irreducible p) → m.card ≤ m.prod.natDegree := by
        intro m
        induction m using Multiset.induction_on with
        | empty => intro _; simp
        | cons a s ih =>
            intro h
            have ha_irr : Irreducible a := h a (Multiset.mem_cons_self a s)
            have hs_irr : ∀ p ∈ s, Irreducible p := fun p hp => h p (Multiset.mem_cons_of_mem hp)
            have ha_pos : 1 ≤ a.natDegree :=
              Nat.pos_of_ne_zero fun h0 => ha_irr.not_isUnit
                (Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree ha_irr.ne_zero, h0]; rfl))
            have hs_ne : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => (hs_irr 0 h0).ne_zero rfl
            rw [Multiset.card_cons, Multiset.prod_cons, Polynomial.natDegree_mul ha_irr.ne_zero hs_ne]
            have := ih hs_irr; omega
      exact (hsum _ fun p hp => UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp).trans (le_of_eq hdeg_eq)
    have h3 : f0L.natDegree = (F.coeff 0).natDegree := Polynomial.natDegree_map_eq_of_injective hι (F.coeff 0)
    omega
  let allBad : Finset (Fin 27) :=
    (Finset.univ.filter fun j : Fin 27 => f1L + Polynomial.C (cEmb (ts j)) * f2L = 0) ∪
    facs.biUnion (fun p => Finset.univ.filter fun j : Fin 27 => p ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L)
  have hallBad_lt : allBad.card < (Finset.univ : Finset (Fin 27)).card := by
    have h1 : allBad.card ≤ 1 + facs.card := by
      calc allBad.card
          ≤ (Finset.univ.filter fun j : Fin 27 => f1L + Polynomial.C (cEmb (ts j)) * f2L = 0).card +
            (facs.biUnion (fun p => Finset.univ.filter fun j : Fin 27 => p ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L)).card :=
            Finset.card_union_le _ _
        _ ≤ 1 + ∑ p ∈ facs, (Finset.univ.filter fun j : Fin 27 => p ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L).card :=
            Nat.add_le_add hbad_zero Finset.card_biUnion_le
        _ ≤ 1 + ∑ _p ∈ facs, 1 := Nat.add_le_add_left (Finset.sum_le_sum hbad_le1) 1
        _ = 1 + facs.card := by simp
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hex_j : ∃ j : Fin 27, j ∉ allBad := by
    by_contra hall; push Not at hall
    have hle := Finset.card_le_card (show (Finset.univ : Finset (Fin 27)) ⊆ allBad from fun j _ => hall j)
    omega
  obtain ⟨j, hj⟩ := hex_j
  refine ⟨hf0_ne, ts j, ?_⟩
  set ht_poly : BiPoly K := F.coeff 1 + Polynomial.C (Polynomial.C (cEmb0 (ts j))) * F.coeff 2
  have hht_map : ht_poly.map ι = f1L + Polynomial.C (cEmb (ts j)) * f2L := by
    simp [ht_poly, f1L, f2L, cEmb, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  have hhtL_ne : ht_poly.map ι ≠ 0 := by
    rw [hht_map]; intro h0; apply hj
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
  have hht_ne : ht_poly ≠ 0 := fun h0 => hhtL_ne (by rw [h0, Polynomial.map_zero])
  have hcop : IsCoprime f0L (ht_poly.map ι) := by
    refine EuclideanDomain.isCoprime_of_dvd (fun h => hf0L_ne h.1) ?_
    intro p hp hp_ne hp0 hp1
    obtain ⟨p', hp'_irr, hp'_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hp hp_ne
    obtain ⟨q, hq_mem, hq_assoc⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf0L_ne hp'_irr (hp'_dvd.trans hp0)
    have hq_facs : q ∈ facs := Multiset.mem_toFinset.mpr hq_mem
    have hq_dvd1 : q ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L := by
      rw [← hht_map]; exact hq_assoc.symm.dvd.trans (hp'_dvd.trans hp1)
    apply hj
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq_facs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_dvd1⟩⟩)
  refine ⟨hht_ne, ?_⟩
  intro hres0
  have hresL : Polynomial.resultant f0L (ht_poly.map ι) f0L.natDegree (ht_poly.map ι).natDegree = 0 := by
    dsimp only [f0L]
    rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
      Polynomial.resultant_map_map, hres0, map_zero]
  exact Polynomial.resultant_ne_zero _ _ hcop hresL

/-- For irreducible `F ∈ ContactPoly (Polynomial Fld)` of `deg_R = 2` (`f1 ≠ 0, f2 ≠ 0, d0 ≤ 25`):
there exists `t ∈ Fld` such that `Res_Y(f0, f1 + t * f2; d0, dh) ≠ 0` in `Fld[Z][X]`! -/
theorem exists_t_resY_ne_zero_of_irred_deg2 (Fpoly : ContactPoly (Polynomial Fld))
    (hirr : Irreducible (liftCRat Fpoly)) (hdeg : Fpoly.natDegree = 2)
    (hf1_ne : Fpoly.coeff 1 ≠ 0) (hf2_ne : Fpoly.coeff 2 ≠ 0)
    (hd0_le : (Fpoly.coeff 0).natDegree ≤ 25) :
    let f0 := Fpoly.coeff 0
    let f1 := Fpoly.coeff 1
    let f2 := Fpoly.coeff 2
    f0 ≠ 0 ∧ ∃ t : Fld,
      let ht := f1 + Polynomial.C (Polynomial.C (Polynomial.C t)) * f2
      ht ≠ 0 ∧ Polynomial.resultant f0 ht f0.natDegree ht.natDegree ≠ 0 := by
  intro f0 f1 f2
  let alg : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have halg : Function.Injective alg := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have hmap_alg : Function.Injective (Polynomial.mapRingHom alg) := Polynomial.map_injective alg halg
  have hlift_bi : Function.Injective (liftBiRat (F := Fld)) :=
    Polynomial.map_injective _ hmap_alg
  have hdeg_rat : (liftCRat Fpoly).natDegree = 2 := by
    rw [liftCRat, Polynomial.coe_mapRingHom, Polynomial.natDegree_map_eq_of_injective hlift_bi, hdeg]
  have hcoeff : ∀ k, (liftCRat Fpoly).coeff k = (Fpoly.coeff k).map (Polynomial.mapRingHom alg) := fun k => by
    simp only [liftCRat, liftBiRat, Polynomial.coe_mapRingHom, Polynomial.coeff_map]; rfl
  let cEmb0 : Fld →+* RatFunc Fld := alg.comp Polynomial.C
  have hcEmb0 : Function.Injective cEmb0 := halg.comp Polynomial.C_injective
  have hf1_rat : (liftCRat Fpoly).coeff 1 ≠ 0 := by
    rw [hcoeff 1]; exact (Polynomial.map_ne_zero_iff hmap_alg).mpr hf1_ne
  have hf2_rat : (liftCRat Fpoly).coeff 2 ≠ 0 := by
    rw [hcoeff 2]; exact (Polynomial.map_ne_zero_iff hmap_alg).mpr hf2_ne
  have hd0_rat : ((liftCRat Fpoly).coeff 0).natDegree ≤ 25 := by
    rw [hcoeff 0, Polynomial.natDegree_map_eq_of_injective hmap_alg]; exact hd0_le
  obtain ⟨hf0_rat, t, hht_rat, hres_rat⟩ :=
    exists_t_resY_ne_zero_of_irred_deg2_aux cEmb0 hcEmb0 (liftCRat Fpoly) hirr hdeg_rat hf1_rat hf2_rat hd0_rat
  refine ⟨fun h0 => hf0_rat (by rw [hcoeff 0, show Fpoly.coeff 0 = 0 from h0, Polynomial.map_zero]), t, ?_⟩
  set ht : BiPoly (Polynomial Fld) := f1 + Polynomial.C (Polynomial.C (Polynomial.C t)) * f2
  have hht_map : ht.map (Polynomial.mapRingHom alg) =
      (liftCRat Fpoly).coeff 1 + Polynomial.C (Polynomial.C (cEmb0 t)) * (liftCRat Fpoly).coeff 2 := by
    rw [hcoeff 1, hcoeff 2]
    simp only [ht, f1, f2, cEmb0, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.coe_mapRingHom, RingHom.comp_apply]
  refine ⟨fun h0 => hht_rat (by rw [← hht_map, h0, Polynomial.map_zero]), fun hres0 => hres_rat ?_⟩
  rw [hcoeff 0, ← hht_map, Polynomial.natDegree_map_eq_of_injective hmap_alg,
    Polynomial.natDegree_map_eq_of_injective hmap_alg, Polynomial.resultant_map_map, hres0, map_zero]

/-! ### Part 3: Single-Point Surplus Theorems (`t1_surplus_of_point` & `t23_surplus_of_point`) -/

private lemma X_sub_C_pow_dvd_resultant_of_biMultGE {F : Type*} [Field F]
    (x0 y0 : F) (f g : BiPoly F) (df mf dg mg : ℕ)
    (hf : biMultGE x0 y0 f mf) (hg : biMultGE x0 y0 g mg)
    (hdf : f.natDegree ≤ df) (hdg : g.natDegree ≤ dg) :
    (X - C x0) ^ resOrdExact df mf dg mg ∣ Polynomial.resultant f g df dg := by
  have h := pow_dvd_resultant_of_biMultGE x0 y0 f g df mf dg mg hf hg hdf hdg
  rw [resultant_shiftBi x0 y0 f g df dg hdf hdg] at h
  exact X_sub_C_pow_dvd_of_comp_shift x0 _ _ h

private lemma eval_resultant_eq_zero_of_common_root {F : Type*} [Field F]
    (f g : BiPoly F) (df dg : ℕ) (hf : f.natDegree ≤ df) (hg : g.natDegree ≤ dg)
    (P : Polynomial F) (hPf : f.eval P = 0) (hPg : g.eval P = 0) (hpos : 0 < df + dg) :
    Polynomial.resultant f g df dg = 0 := by
  let ψ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hψ : Function.Injective ψ := IsFractionRing.injective (Polynomial F) (RatFunc F)
  apply hψ; rw [map_zero, ← Polynomial.resultant_map_map]
  have hroot_f : (f.map ψ).IsRoot (ψ P) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_apply, hPf, map_zero]
  have hroot_g : (g.map ψ).IsRoot (ψ P) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_apply, hPg, map_zero]
  have hdf : (f.map ψ).natDegree ≤ df := Polynomial.natDegree_map_le.trans hf
  have hdg : (g.map ψ).natDegree ≤ dg := Polynomial.natDegree_map_le.trans hg
  by_cases hfn : f.map ψ = 0
  · rw [hfn, Polynomial.resultant_zero_left]
    by_cases hdg0 : dg = 0
    · subst hdg0
      have hgn : g.map ψ = 0 := by
        have hgd0 : (g.map ψ).natDegree = 0 := Nat.eq_zero_of_le_zero hdg
        have hC := Polynomial.eq_C_of_natDegree_eq_zero hgd0
        rw [hC, Polynomial.IsRoot.def, Polynomial.eval_C] at hroot_g
        rw [hC, hroot_g, map_zero]
      rw [hgn, Polynomial.coeff_zero, zero_pow (by omega : df ≠ 0), mul_zero]
    · rw [zero_pow hdg0, zero_mul]
  · by_cases hgn : g.map ψ = 0
    · rw [hgn, Polynomial.resultant_zero_right]
      by_cases hdf0 : df = 0
      · subst hdf0
        have hfn' : f.map ψ = 0 := by
          have hfd0 : (f.map ψ).natDegree = 0 := Nat.eq_zero_of_le_zero hdf
          have hC := Polynomial.eq_C_of_natDegree_eq_zero hfd0
          rw [hC, Polynomial.IsRoot.def, Polynomial.eval_C] at hroot_f
          rw [hC, hroot_f, map_zero]
        exact absurd hfn' hfn
      · rw [zero_pow hdf0, zero_mul]
    · rcases Polynomial.dvd_iff_isRoot.mpr hroot_f with ⟨f', hf'⟩
      have hf'_ne : f' ≠ 0 := fun h0 => hfn (by rw [hf', h0, mul_zero])
      have hdf_eq : (f.map ψ).natDegree = 1 + f'.natDegree := by
        rw [hf', Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hf'_ne, Polynomial.natDegree_X_sub_C]
      have hres_nat : Polynomial.resultant (f.map ψ) (g.map ψ) (f.map ψ).natDegree (g.map ψ).natDegree = 0 := by
        rw [hdf_eq, hf']
        have h1 := Polynomial.resultant_mul_left (Polynomial.X - Polynomial.C (ψ P)) f' (g.map ψ)
          (g.map ψ).natDegree le_rfl
        rw [Polynomial.natDegree_X_sub_C] at h1
        rw [h1]
        have hlin := Polynomial.resultant_X_sub_C_left (g.map ψ) (g.map ψ).natDegree (ψ P) le_rfl
        rw [hlin, Polynomial.IsRoot.def.mp hroot_g, zero_mul]
      rw [show df = (f.map ψ).natDegree + (df - (f.map ψ).natDegree) by omega,
        Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl,
        show dg = (g.map ψ).natDegree + (dg - (g.map ψ).natDegree) by omega,
        Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, hres_nat]
      ring

private lemma resYKerD1Fn_le_ord (d0 d1 k : ℕ) (hd0 : d0 ≤ max d0 (d1 + 1)) :
    resYKerD1Fn d1 (max d0 (d1 + 1)) k ≤ resYKerD1Ord d0 d1 k := by
  unfold resYKerD1Fn
  by_cases hle : d0 ≤ d1 + 1
  · have hmax : max d0 (d1 + 1) = d1 + 1 := Nat.max_eq_right hle
    rw [hmax]; simp only [beq_self_eq_true, ↓reduceIte]
    unfold resYKerD1MinLe
    exact foldl_map_min_le_mem (fun d => resYKerD1Ord d d1 k) (List.range (d1 + 2))
      (resYKerD1Ord 0 d1 k) d0 (List.mem_range.mpr (by omega))
  · have hmax : max d0 (d1 + 1) = d0 := Nat.max_eq_left (by omega)
    rw [hmax]
    have hne : (d0 == d1 + 1) = false := beq_false_of_ne (by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact le_rfl

/-- **Table 1 Single-Point Surplus Theorem (`t1_surplus_of_point`):**
For ANY `F ∈ K_{W_F}(1)` over `Fld` outside Table 4 (`¬ (d1 = 4 ∧ d0 ≤ 5 ∧ W_F/wY < 28/5)`),
any point `(y, P, Az)` with `evalContact F P = 0`, `|Az| ≥ A`, `twOrdGE (localShift i) (k i)`,
produces a verified `c ∈ certsT1` giving strict quotient-interpolation surplus on `k`! -/
theorem t1_surplus_of_point {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Fld)
    (y : Idx → Fld) (k : Idx → ℕ)
    (hvan : ∀ i : Idx, twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (y i) e.1) (k i))
    (P : Polynomial Fld) (hPdeg : P.natDegree ≤ wY)
    (Az : Finset Idx) (hAz : A ≤ Az.card)
    (hagree : ∀ i ∈ Az, P.eval (BinaryIRSProfile.domain i) = y i)
    (hFvan : evalContact (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) P = 0)
    (hf1_ne : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hRes_ne : 2 ≤ ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree →
      Polynomial.resultant
        ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 0)
        ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1)
        ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).natDegree
        ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree ≠ 0)
    (hnotT4 : ¬ (((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree = 4 ∧
      ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).natDegree ≤ 5 ∧
      (W_F : ℚ) / (wY : ℚ) < 28 / 5)) :
    ∃ c ∈ certsT1, checkT1Entry c = true ∧ 0 < c.m ∧ c.m ≤ 3000 ∧ c.s ≤ 300 ∧
      (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) ∧
      (W_F : ℚ) / (wY : ℚ) ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ) ∧
      (c.δNum : ℚ) / (c.δDen : ℚ) <
        vquotLbQ 1 c.m c.s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 c.m c.s (k i)) / (N : ℚ) ∧
      checkCapWitness 1 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap1 = true ∧
      c.cap1.c1Bkt ≤ T4_C1_SUM ∧ c.cap1.c0Bkt ≤ T4_C0_SUM ∧
      ((W_F : ℚ) / (wY : ℚ) < 13 →
        checkCapWitness 1 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 2 c.cap2 = true ∧
        c.cap2.c1Bkt * 3850 + c.cap2.c0Bkt ≤ T4_Q2_SUM) := by
  set Fpoly : ContactPoly Fld := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
  set f0 : BiPoly Fld := Fpoly.coeff 0
  set f1 : BiPoly Fld := Fpoly.coeff 1
  set d0 : ℕ := f0.natDegree
  set d1 : ℕ := f1.natDegree
  set d0Eff : ℕ := max d0 (d1 + 1)
  have hwYpos : 0 < wY := by norm_num [wY]
  have hwYQ : (0 : ℚ) < (wY : ℚ) := by exact_mod_cast hwYpos
  have hFmem : contactDeriv Fpoly = 0 ∧ Fpoly.natDegree ≤ 1 ∧ wdeg wY Fpoly ≤ W_F :=
    (mem_kerD_iff_exists_unique_coords (by norm_num [wY]) Fpoly).mpr ⟨f_coord, rfl, fun c' hc' => by
      funext ⟨⟨k', r', b', a'⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W_F 1 hwYpos k' r' b' a').mp he).1
      rcases (show r' = 0 ∨ r' = 1 by omega) with rfl | rfl
      · have h := congrArg (fun Q : ContactPoly Fld => ((Q.coeff k').coeff (2 * b')).coeff (2 * a')) hc'
        dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
        simpa [he] using h.symm
      · have h := congrArg (fun Q : ContactPoly Fld => ((Q.coeff k').coeff (2 * b' + 1)).coeff (2 * a')) hc'
        dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
        have h1 : (2 * b' + 1) % 2 = 1 := by omega
        have h2 : (2 * a') % 2 = 0 := by omega
        have h3 : (2 * b' + 1) / 2 = b' := by omega
        have h4 : (2 * a') / 2 = a' := by omega
        simpa [h1, h2, h3, h4, he] using h.symm⟩
  have ⟨_, hd1_ev, _, hd0_par⟩ := kerD1_pde_facts hFmem.1 hFmem.2.1
  have hWf1 : wdegBi wY f1 + (wY - 1) ≤ W_F := by
    simpa only [one_mul] using wdegBi_coeff_le_of_wdeg hFmem.2.2 1 hf1_ne
  have hWf0 : wdegBi wY f0 ≤ W_F := by simpa using wdegBi_le_of_wdeg_coeff hFmem.2.2 0
  have hd1_wY : d1 * wY ≤ wdegBi wY f1 := by
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hf1_ne
    have hle := (wdegBi_le_iff wY (wdegBi wY f1) f1).mp le_rfl d1 _ (Polynomial.leadingCoeff_ne_zero.mpr hlc)
    omega
  have hWF_le_nat : 2 * W_F ≤ 51 * wY := by
    have : 2 * (W_F : ℚ) ≤ 51 * (wY : ℚ) := by
      have := (div_le_div_iff₀ hwYQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi; linarith
    exact_mod_cast this
  have hWf1' : wdegBi wY f1 + 1048574 ≤ W_F := hWf1
  have hd1_wY' : d1 * 1048575 ≤ wdegBi wY f1 := hd1_wY
  have hWF_le' : 2 * W_F ≤ 51 * 1048575 := hWF_le_nat
  have hd1_le24 : d1 ≤ 24 := by omega
  have hd0_eff_spec : d0Eff = d1 + 1 ∨ (d1 + 1 < d0Eff ∧ d0Eff ≤ 24 ∧ d0Eff % 2 = 0) := by
    by_cases hle : d0 ≤ d1 + 1
    · exact Or.inl (Nat.max_eq_right hle)
    · right
      have heq : d0Eff = d0 := Nat.max_eq_left (by omega)
      have hev : d0 % 2 = 0 := hd0_par.resolve_left hle
      have hf0_ne : f0 ≠ 0 := by intro h0; simp [d0, h0] at hle
      have hd0_wY : d0 * 1048575 ≤ W_F := by
        have hlc := Polynomial.leadingCoeff_ne_zero.mpr hf0_ne
        have hle' := (wdegBi_le_iff wY W_F f0).mp hWf0 d0 _ (Polynomial.leadingCoeff_ne_zero.mpr hlc)
        exact (Nat.le_add_left (d0 * wY) _).trans hle'
      refine ⟨by omega, by omega, by omega⟩
  have hlo_t1 : ((t1StartPair d1 d0Eff).1 : ℚ) / ((t1StartPair d1 d0Eff).2 : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) := by
    unfold t1StartPair
    by_cases h45 : d1 = 4 ∧ d0Eff = 5
    · have hb : (d1 == 4 && d0Eff == 5) = true := by simp [h45.1, h45.2]
      rw [if_pos hb]
      by_contra hlt; push Not at hlt
      exact hnotT4 ⟨h45.1, by omega, hlt⟩
    · have hb : (d1 == 4 && d0Eff == 5) = false := by
        rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
        by_cases h1 : d1 = 4
        · exact Or.inr fun h2 => h45 ⟨h1, h2⟩
        · exact Or.inl h1
      rw [if_neg (by simp [hb])]
      by_cases heq : d0Eff = d1 + 1
      · simp only [heq, beq_self_eq_true, ↓reduceIte]
        apply div_le_div_of_nonneg_right _ hwYQ.le
        have h1 : (d1 + 1) * wY - 1 ≤ W_F := by change (d1 + 1) * 1048575 - 1 ≤ W_F; omega
        exact_mod_cast h1
      · have hne : (d0Eff == d1 + 1) = false := beq_false_of_ne heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Nat.cast_one, div_one]
        have hd0_gt : d1 + 1 < d0 := by omega
        have hf0_ne : f0 ≠ 0 := by intro h0; simp [d0, h0] at hd0_gt
        have hd0_wY : d0 * wY ≤ W_F := by
          have hlc := Polynomial.leadingCoeff_ne_zero.mpr hf0_ne
          have hle' := (wdegBi_le_iff wY W_F f0).mp hWf0 d0 _ (Polynomial.leadingCoeff_ne_zero.mpr hlc)
          omega
        rw [le_div_iff₀ hwYQ]
        have : d0Eff = d0 := Nat.max_eq_left (by omega)
        rw [this]; exact_mod_cast hd0_wY
  obtain ⟨c, hc_mem, hcd1, hcd0, hc_entry, hc_lo, hc_hi⟩ :=
    exists_t1Cert d1 d0Eff hd1_le24 hd1_ev hd0_eff_spec ((W_F : ℚ) / (wY : ℚ)) hlo_t1 hWF_hi
  have hchk : checkT1Cert c = true := (Bool.and_eq_true _ _).mp hc_entry |>.1
  -- Prove f1.eval P ≠ 0!
  have hf1_P_ne : f1.eval P ≠ 0 := by
    intro h0
    by_cases hd1_0 : d1 = 0
    · have hC := Polynomial.eq_C_of_natDegree_eq_zero hd1_0
      rw [hC, Polynomial.eval_C] at h0
      exact hf1_ne (by rw [hC, h0, map_zero])
    · have hd1_2 : 2 ≤ d1 := by change d1 % 2 = 0 at hd1_ev; omega
      have hf0_P : f0.eval P = 0 := by
        have hFexp : Fpoly = Polynomial.C f0 + Polynomial.C f1 * Polynomial.X := by
          rw [Polynomial.ext_iff]; intro r; cases r with
          | zero => simp [f0]
          | succ r' => cases r' with
            | zero => simp [f1]
            | succ r'' =>
                rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Fpoly.natDegree < r''.succ.succ)]
                simp [Polynomial.coeff_C, Polynomial.coeff_mul_X]
        have hev := hFvan
        change evalContact Fpoly P = 0 at hev
        rw [hFexp] at hev; unfold evalContact at hev
        simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, h0] using hev
      exact hRes_ne hd1_2 (eval_resultant_eq_zero_of_common_root f0 f1 d0 d1 le_rfl le_rfl P hf0_P h0 (by omega))
  -- Prove the 3 sum bounds for checkT1Cert_sound!
  have hbm1 : ∀ i : Idx, biMultGE (BinaryIRSProfile.domain i) (y i) f1 (2 * k i - 1) :=
    fun i => (kerD1_local_ords hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)).2
  have hf1_sum : (∑ i ∈ Az, ((2 * k i - 1 : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 1) * (wY : ℚ) + 1 := by
    have hnat : ∑ i ∈ Az, (2 * k i - 1) ≤ W_F - (wY - 1) :=
      sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - (wY - 1)) f1 P (fun i => 2 * k i - 1)
        hPdeg (by omega) hf1_P_ne (fun i hi => by rw [hagree i hi]; exact hbm1 i)
    have hQ : ((∑ i ∈ Az, (2 * k i - 1) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) : ℕ) : ℚ) := by exact_mod_cast hnat
    rw [Nat.cast_sum] at hQ
    have h1 : wY - 1 ≤ W_F := by omega
    have h2 : 1 ≤ wY := by norm_num [wY]
    rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_one] at hQ
    have heq : ((W_F : ℚ) / (wY : ℚ) - 1) * (wY : ℚ) + 1 = (W_F : ℚ) - ((wY : ℚ) - 1) := by
      field_simp [hwYQ.ne']; ring
    linarith
  have hlc1_sum : (∑ i : Idx, ((2 * k i - 1 - c.d1 : ℕ) : ℚ)) ≤
      ((W_F : ℚ) / (wY : ℚ) - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1 := by
    rw [hcd1]
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
        (X - C (BinaryIRSProfile.domain i)) ^ (2 * k i - 1 - d1) ∣ f1.leadingCoeff := fun i _ =>
      pow_dvd_leadingCoeff_of_biMultGE (BinaryIRSProfile.domain i) (y i) f1 d1 (2 * k i - 1) rfl (hbm1 i)
    have hdeg_lc : f1.leadingCoeff.natDegree ≤ W_F - (wY - 1) - d1 * wY := by
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hf1_ne)
      have hle := (wdegBi_le_iff wY (W_F - (wY - 1)) f1).mp (by omega) d1 _ hnz
      omega
    have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ f1.leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr hf1_ne) _ hdvd).trans hdeg_lc
    have hQ : ((∑ i : Idx, (2 * k i - 1 - d1) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) - d1 * wY : ℕ) : ℚ) := by
      exact_mod_cast hnat
    rw [Nat.cast_sum] at hQ
    have h1 : wY - 1 + d1 * wY ≤ W_F := by omega
    have h2 : 1 ≤ wY := by norm_num [wY]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub h2, Nat.cast_mul, Nat.cast_one] at hQ
    have heq : ((W_F : ℚ) / (wY : ℚ) - 1 - (d1 : ℚ)) * (wY : ℚ) + 1 =
        (W_F : ℚ) - ((wY : ℚ) - 1) - (d1 : ℚ) * (wY : ℚ) := by
      field_simp [hwYQ.ne']; ring
    linarith
  have hres_sum : 2 ≤ c.d1 →
      (∑ i : Idx, (resYKerD1Fn c.d1 c.d0Eff (k i) : ℚ)) ≤
        ((c.d1 : ℚ) * ((W_F : ℚ) / (wY : ℚ)) +
          ((max c.d0Eff (c.d1 + 1) : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1 - (c.d1 : ℚ))) * (wY : ℚ) +
          ((max c.d0Eff (c.d1 + 1) : ℕ) : ℚ) := by
    rw [hcd1, hcd0]; intro hd1_2
    have hdp_eq : max d0Eff (d1 + 1) = d0Eff := Nat.max_eq_left (by omega)
    rw [hdp_eq]
    set R : Polynomial Fld := f1.leadingCoeff ^ (d0Eff - d0) * Polynomial.resultant f0 f1 d0 d1
    have hRne : R ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hf1_ne)) (hRes_ne hd1_2)
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
        (X - C (BinaryIRSProfile.domain i)) ^ resYKerD1Fn d1 d0Eff (k i) ∣ R := fun i _ =>
      (pow_dvd_pow _ (resYKerD1Fn_le_ord d0 d1 (k i) (le_max_left _ _))).trans
        (kerD1_resY_ord hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i) hd1_2)
    have hdeg_lc : f1.leadingCoeff.natDegree ≤ W_F - (wY - 1) - d1 * wY := by
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hf1_ne)
      have hle := (wdegBi_le_iff wY (W_F - (wY - 1)) f1).mp (by omega) d1 _ hnz; omega
    have hdeg_res : (Polynomial.resultant f0 f1 d0 d1).natDegree ≤
        d1 * W_F + d0 * (W_F - (wY - 1)) - d0 * d1 * wY :=
      natDegree_resultant_le_wdegBi wY W_F (W_F - (wY - 1)) d0 d1 f0 f1 hWf0 (by omega) le_rfl le_rfl
    have hdeg_R : R.natDegree ≤ d1 * W_F + d0Eff * (W_F - (wY - 1) - d1 * wY) := by
      have h1 : R.natDegree ≤ (d0Eff - d0) * f1.leadingCoeff.natDegree + (Polynomial.resultant f0 f1 d0 d1).natDegree :=
        Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_pow_le _)
      have h2 : (d0Eff - d0) * f1.leadingCoeff.natDegree ≤ (d0Eff - d0) * (W_F - (wY - 1) - d1 * wY) :=
        Nat.mul_le_mul_left _ hdeg_lc
      have hd0_le_eff : d0 ≤ d0Eff := le_max_left _ _
      have hmul_le : d0 * d1 * wY ≤ d0 * (W_F - (wY - 1)) := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left d0 (by omega)
      have hsub_eq : d0 * (W_F - (wY - 1)) - d0 * d1 * wY = d0 * (W_F - (wY - 1) - d1 * wY) := by
        rw [mul_assoc d0 d1 wY, ← Nat.mul_sub]
      have hsum_eq : (d0Eff - d0) * (W_F - (wY - 1) - d1 * wY) + d0 * (W_F - (wY - 1) - d1 * wY) =
          d0Eff * (W_F - (wY - 1) - d1 * wY) := by
        rw [← add_mul, Nat.sub_add_cancel hd0_le_eff]
      omega
    have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ R hRne _ hdvd).trans hdeg_R
    have hQ : ((∑ i : Idx, resYKerD1Fn d1 d0Eff (k i) : ℕ) : ℚ) ≤
        ((d1 * W_F + d0Eff * (W_F - (wY - 1) - d1 * wY) : ℕ) : ℚ) := by exact_mod_cast hnat
    rw [Nat.cast_sum] at hQ
    have h1 : wY - 1 + d1 * wY ≤ W_F := by omega
    have h2 : 1 ≤ wY := by norm_num [wY]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
      Nat.cast_sub h2, Nat.cast_mul, Nat.cast_one] at hQ
    have heq : ((d1 : ℚ) * ((W_F : ℚ) / (wY : ℚ)) + (d0Eff : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1 - (d1 : ℚ))) * (wY : ℚ) +
        (d0Eff : ℚ) = (d1 : ℚ) * (W_F : ℚ) + (d0Eff : ℚ) * ((W_F : ℚ) - ((wY : ℚ) - 1) - (d1 : ℚ) * (wY : ℚ)) := by
      field_simp [hwYQ.ne']; ring
    linarith
  have ⟨hm0, hsurp_fn⟩ := checkT1Cert_sound c hchk ((W_F : ℚ) / (wY : ℚ)) hc_lo hc_hi Az hAz k hf1_sum hlc1_sum hres_sum
  have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
  have ⟨hsurp, hcap1, hcap2_fn⟩ := hsurp_fn hmpos
  have hlin := List.all_eq_true.mp certsT1_linear_caps c hc_mem
  have hmne : (c.m == 0) = false := beq_false_of_ne hm0
  simp only [hmne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at hlin
  refine ⟨c, hc_mem, hc_entry, hmpos, hlin.1.1, hlin.1.2, hc_lo, hc_hi, hsurp, hcap1,
    hlin.2.1.1, hlin.2.1.2, fun hlt13 => ?_⟩
  have hcLoD : 0 < c.cLoDen := by
    by_contra h0; unfold checkT1Cert at hchk
    simp [show c.cLoDen = 0 by omega] at hchk
  have hcLo_lt13 : c.cLoNum < 13 * c.cLoDen := by
    have h1 : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) < 13 := lt_of_le_of_lt hc_lo hlt13
    have hcLoDQ : (0 : ℚ) < (c.cLoDen : ℚ) := by exact_mod_cast hcLoD
    have h2 : (c.cLoNum : ℚ) < 13 * (c.cLoDen : ℚ) := (div_lt_iff₀ hcLoDQ).mp h1
    exact_mod_cast h2
  have hcap2_ok : c.hasCap2 = true ∧ c.cap2.c1Bkt * 3850 + c.cap2.c0Bkt ≤ T1_CAP_BOUND := by
    unfold checkT1Entry at hc_entry
    simp only [hmne, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hc_entry
    rcases hc_entry.2.2 with hnot | hok
    · exact absurd hcLo_lt13 (decide_eq_false_iff_not.mp hnot)
    · exact hok
  refine ⟨hcap2_fn hcap2_ok.1, ?_⟩
  rcases hlin.2.2 with hf | hle
  · rw [hcap2_ok.1] at hf; cases hf
  · exact hle

/-- Helper: in char 2, `f0 = expand 2 A0 + Y * f0.derivative` where `A0.coeff j = f0.coeff (2 * j)`. -/
private lemma char2_biPoly_eq_expand2_add_X_deriv {F : Type*} [Field F] [CharP F 2] (f0 : BiPoly F) :
    let A0 : BiPoly F := ∑ j ∈ Finset.range (f0.natDegree / 2 + 1), Polynomial.monomial j (f0.coeff (2 * j))
    (∀ j, A0.coeff j = f0.coeff (2 * j)) ∧
    f0 = Polynomial.expand (Polynomial F) 2 A0 + Polynomial.X * f0.derivative := by
  intro A0
  have hA0_c : ∀ j, A0.coeff j = f0.coeff (2 * j) := by
    intro j; dsimp [A0]; rw [finset_sum_coeff]
    by_cases hj : j < f0.natDegree / 2 + 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      intro l hl; have := Finset.mem_range.mp hl; simp [Polynomial.coeff_monomial, show l ≠ j by omega]
  refine ⟨hA0_c, ?_⟩
  rw [Polynomial.ext_iff]; intro n
  rw [Polynomial.coeff_add, Polynomial.coeff_expand (by norm_num : 0 < 2)]
  cases n with
  | zero => simp [hA0_c 0]
  | succ m =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, ← Nat.cast_succ]
      by_cases hev : 2 ∣ m + 1
      · rw [if_pos hev, hA0_c, show 2 * ((m + 1) / 2) = m + 1 by omega]
        have hm0 : ((m + 1 : ℕ) : Polynomial F) = 0 := by
          obtain ⟨q, hq⟩ := hev; rw [hq, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul]
        rw [hm0, mul_zero, add_zero]
      · rw [if_neg hev, zero_add]
        have hm1 : ((m + 1 : ℕ) : Polynomial F) = 1 := by
          have : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
          rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
            CharTwo.two_eq_zero, zero_mul, zero_add]
        rw [hm1, mul_one]

private lemma biMultGE_mono {F : Type*} [Field F] {x0 y0 : F} {f : BiPoly F} {m1 m2 : ℕ}
    (hle : m1 ≤ m2) (h : biMultGE x0 y0 f m2) : biMultGE x0 y0 f m1 :=
  fun i j hij => h i j (lt_of_lt_of_le hij hle)

/-- **Tables 2, 3, 2A, and 2B Unified Single-Point Surplus Theorem (`t23_surplus_of_point`):** -/
theorem t23_surplus_of_point {W_F : ℕ} (f_coord : KerDIdx wY W_F 2 → Fld)
    (y : Idx → Fld) (k : Idx → ℕ)
    (hvan : ∀ i : Idx, twOrdGE (∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (y i) e.1) (k i))
    (P : Polynomial Fld) (hPdeg : P.natDegree ≤ wY)
    (Az : Finset Idx) (hAz : A ≤ Az.card)
    (hagree : ∀ i ∈ Az, P.eval (BinaryIRSProfile.domain i) = y i)
    (hf1_ne : (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0)
    (hf2_ne : (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2 ≠ 0)
    (hf1_P_ne : ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).eval P ≠ 0)
    (hf2_P_ne : ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2).eval P ≠ 0)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hcop_all : ∀ p : Polynomial (RatFunc Fld),
      p ∣ ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
      p ∣ ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
      p ∣ ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
      IsUnit p) :
    ∃ (m s cHiNum cHiDen δNum δDen : ℕ) (w : CapWitness),
      0 < m ∧ m ≤ 3000 ∧ 2 ≤ s ∧ s ≤ 300 ∧ 0 < cHiDen ∧ 0 < δNum ∧ 0 < δDen ∧
      (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ) ∧
      (δNum : ℚ) / (δDen : ℚ) <
        vquotLbQ 2 m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 2 m s (k i)) / (N : ℚ) ∧
      checkCapWitness 2 m s cHiNum cHiDen δNum δDen 1 1 1 w = true ∧
      w.c1Bkt * 3850 + w.c0Bkt ≤ T3_CAP_BOUND := by
  set Fpoly : ContactPoly Fld := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
  set f0 : BiPoly Fld := Fpoly.coeff 0
  set f1 : BiPoly Fld := Fpoly.coeff 1
  set f2 : BiPoly Fld := Fpoly.coeff 2
  set d0 : ℕ := f0.natDegree
  set d1 : ℕ := f1.natDegree
  set d2 : ℕ := f2.natDegree
  let ι : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have hwYpos : 0 < wY := by norm_num [wY]
  have hwYQ : (0 : ℚ) < (wY : ℚ) := by exact_mod_cast hwYpos
  have hFmem : contactDeriv Fpoly = 0 ∧ Fpoly.natDegree ≤ 2 ∧ wdeg wY Fpoly ≤ W_F :=
    (mem_kerD_iff_exists_unique_coords (by norm_num [wY]) Fpoly).mpr ⟨f_coord, rfl, fun c' hc' => by
      funext ⟨⟨k', r', b', a'⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W_F 2 hwYpos k' r' b' a').mp he).1
      rcases (show r' = 0 ∨ r' = 1 by omega) with rfl | rfl
      · have h := congrArg (fun Q : ContactPoly Fld => ((Q.coeff k').coeff (2 * b')).coeff (2 * a')) hc'
        dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
        simpa [he] using h.symm
      · have h := congrArg (fun Q : ContactPoly Fld => ((Q.coeff k').coeff (2 * b' + 1)).coeff (2 * a')) hc'
        dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
        have h1 : (2 * b' + 1) % 2 = 1 := by omega
        have h2 : (2 * a') % 2 = 0 := by omega
        have h3 : (2 * b' + 1) / 2 = b' := by omega
        have h4 : (2 * a') / 2 = a' := by omega
        simpa [h1, h2, h3, h4, he] using h.symm⟩
  have ⟨_, hd2_ev, _, hd1_par, hf0_d, hd0_par⟩ := kerD2_pde_facts hFmem.1 hFmem.2.1
  have hWf0 : wdegBi wY f0 ≤ W_F := by simpa using wdegBi_le_of_wdeg_coeff hFmem.2.2 0
  have hWf1 : wdegBi wY f1 + (wY - 1) ≤ W_F := by
    simpa only [one_mul] using wdegBi_coeff_le_of_wdeg hFmem.2.2 1 hf1_ne
  have hWf2 : wdegBi wY f2 + 2 * (wY - 1) ≤ W_F := wdegBi_coeff_le_of_wdeg hFmem.2.2 2 hf2_ne
  have hWF_le_nat : 2 * W_F ≤ 51 * wY := by
    have : 2 * (W_F : ℚ) ≤ 51 * (wY : ℚ) := by
      have := (div_le_div_iff₀ hwYQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi; linarith
    exact_mod_cast this
  have hd_wdeg : ∀ h : BiPoly Fld, h ≠ 0 → h.natDegree * wY ≤ wdegBi wY h := fun h hne => by
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hne
    have hle := (wdegBi_le_iff wY (wdegBi wY h) h).mp le_rfl h.natDegree _ (Polynomial.leadingCoeff_ne_zero.mpr hlc)
    omega
  have hd1_wY : d1 * wY ≤ wdegBi wY f1 := hd_wdeg f1 hf1_ne
  have hd2_wY : d2 * wY ≤ wdegBi wY f2 := hd_wdeg f2 hf2_ne
  have hWf1' : wdegBi wY f1 + 1048574 ≤ W_F := hWf1
  have hWf2' : wdegBi wY f2 + 2 * 1048574 ≤ W_F := hWf2
  have hd1_wY' : d1 * 1048575 ≤ wdegBi wY f1 := hd1_wY
  have hd2_wY' : d2 * 1048575 ≤ wdegBi wY f2 := hd2_wY
  have hWF_le' : 2 * W_F ≤ 51 * 1048575 := hWF_le_nat
  change d2 % 2 = 0 at hd2_ev
  have hd2_le22 : d2 ≤ 22 := by omega
  have hd1_le24 : d1 ≤ 24 := by omega
  have hords_all : ∀ i : Idx,
      biMultGE (BinaryIRSProfile.domain i) (y i) f1 (2 * k i - 1) ∧
      biMultGE (BinaryIRSProfile.domain i) (y i) f2 (2 * k i - 2) := fun i => by
    have h := kerD2_local_ords hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)
    exact ⟨h.2.1, h.2.2.1⟩
  obtain ⟨qX, gPrim, h1, h2, hqX_ne, hgP_prim, hgP_ne, hh1_ne, hh2_ne,
    hf1_fac, hf2_fac, hrel_h, hgP_d, hg_d, hh2_d, hdg_eq, hdg_ev, hdvd_dX⟩ :=
    kerD2_gcd_decomp hFmem.1 hFmem.2.1 hf1_ne hf2_ne
  set g : BiPoly Fld := C qX * gPrim
  change f1 = g * h1 at hf1_fac
  change f2 = g * h2 at hf2_fac
  change f0.derivative = B6401ContactKerD.dXBi f1 at hf0_d
  set dg : ℕ := gPrim.natDegree
  have hg_ne : g ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hqX_ne) hgP_ne
  have hdg_g : g.natDegree = dg := hdg_eq
  have hd1_eq : d1 = dg + h1.natDegree := by
    dsimp [d1]; rw [hf1_fac, Polynomial.natDegree_mul hg_ne hh1_ne, hdg_g]
  have hd2_eq : d2 = dg + h2.natDegree := by
    dsimp [d2]; rw [hf2_fac, Polynomial.natDegree_mul hg_ne hh2_ne, hdg_g]
  -- Helper: sum of lc orders for any nonzero h : BiPoly Fld
  have hsum_lc : ∀ (h : BiPoly Fld) (hne : h ≠ 0) (W_h : ℕ) (hWh : wdegBi wY h ≤ W_h) (r : Idx → ℕ),
      (∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) h (r i)) →
      ∑ i : Idx, (r i - h.natDegree) ≤ W_h - h.natDegree * wY := by
    intro h hne W_h hWh r hr
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
        (X - C (BinaryIRSProfile.domain i)) ^ (r i - h.natDegree) ∣ h.leadingCoeff := fun i _ =>
      pow_dvd_leadingCoeff_of_biMultGE (BinaryIRSProfile.domain i) (y i) h h.natDegree (r i) rfl (hr i)
    have hdeg_lc : h.leadingCoeff.natDegree ≤ W_h - h.natDegree * wY := by
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hne)
      have hle := (wdegBi_le_iff wY W_h h).mp hWh h.natDegree _ hnz; omega
    exact (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ h.leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr hne) _ hdvd).trans hdeg_lc
  by_cases hdg0 : dg = 0
  · -- TABLE 2 (`dg = 0`, so `f1` and `f2` are coprime in `(RatFunc Fld)[Y]`)!
    have hlo_t2 : ((max (d2 + 2) (d1 + 1) * wY - 2 : ℕ) : ℚ) / (wY : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) := by
      apply div_le_div_of_nonneg_right _ hwYQ.le
      have h1 : (d2 + 2) * wY - 2 ≤ W_F := by change (d2 + 2) * 1048575 - 2 ≤ W_F; omega
      have h2 : (d1 + 1) * wY - 2 ≤ W_F := by change (d1 + 1) * 1048575 - 2 ≤ W_F; omega
      have h3 : max (d2 + 2) (d1 + 1) * wY - 2 ≤ W_F := by
        rcases le_total (d2 + 2) (d1 + 1) with hle | hle
        · rw [Nat.max_eq_right hle]; exact h2
        · rw [Nat.max_eq_left hle]; exact h1
      exact_mod_cast h3
    obtain ⟨c, hc_mem, hcd1, hcd2, hc_entry, hc_lo, hc_hi⟩ :=
      exists_t2Cert d1 d2 hd2_le22 hd2_ev hd1_le24 hd1_par ((W_F : ℚ) / (wY : ℚ)) hlo_t2 hWF_hi
    have hchk : checkT2Cert c = true := (Bool.and_eq_true _ _).mp hc_entry |>.1
    have hf1_sum : (∑ i ∈ Az, ((2 * k i - 1 : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 1) * (wY : ℚ) + 1 := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - (wY - 1)) f1 P
        (fun i => 2 * k i - 1) hPdeg (by omega) hf1_P_ne (fun i hi => by rw [hagree i hi]; exact (hords_all i).1)
      have hQ : ((∑ i ∈ Az, (2 * k i - 1) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one] at hQ
      have heq : ((W_F : ℚ) / (wY : ℚ) - 1) * (wY : ℚ) + 1 = (W_F : ℚ) - ((wY : ℚ) - 1) := by
        field_simp [hwYQ.ne']; ring
      linarith
    have hf2_sum : (∑ i ∈ Az, ((2 * k i - 2 : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 2) * (wY : ℚ) + 2 := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - 2 * (wY - 1)) f2 P
        (fun i => 2 * k i - 2) hPdeg (by omega) hf2_P_ne (fun i hi => by rw [hagree i hi]; exact (hords_all i).2)
      have hQ : ((∑ i ∈ Az, (2 * k i - 2) : ℕ) : ℚ) ≤ ((W_F - 2 * (wY - 1) : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_ofNat, Nat.cast_one] at hQ
      have heq : ((W_F : ℚ) / (wY : ℚ) - 2) * (wY : ℚ) + 2 = (W_F : ℚ) - 2 * ((wY : ℚ) - 1) := by
        field_simp [hwYQ.ne']; ring
      linarith
    have hlc1_sum : (∑ i : Idx, ((2 * k i - 1 - c.d1 : ℕ) : ℚ)) ≤
        ((W_F : ℚ) / (wY : ℚ) - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1 := by
      rw [hcd1]
      have hnat := hsum_lc f1 hf1_ne (W_F - (wY - 1)) (by omega) (fun i => 2 * k i - 1) (fun i => (hords_all i).1)
      have hQ : ((∑ i : Idx, (2 * k i - 1 - d1) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) - d1 * wY : ℕ) : ℚ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        Nat.cast_mul, Nat.cast_one] at hQ
      have heq : ((W_F : ℚ) / (wY : ℚ) - 1 - (d1 : ℚ)) * (wY : ℚ) + 1 =
          (W_F : ℚ) - ((wY : ℚ) - 1) - (d1 : ℚ) * (wY : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith
    have hlc2_sum : (∑ i : Idx, ((2 * k i - 2 - c.d2 : ℕ) : ℚ)) ≤
        ((W_F : ℚ) / (wY : ℚ) - 2 - (c.d2 : ℚ)) * (wY : ℚ) + 2 := by
      rw [hcd2]
      have hnat := hsum_lc f2 hf2_ne (W_F - 2 * (wY - 1)) (by omega) (fun i => 2 * k i - 2) (fun i => (hords_all i).2)
      have hQ : ((∑ i : Idx, (2 * k i - 2 - d2) : ℕ) : ℚ) ≤ ((W_F - 2 * (wY - 1) - d2 * wY : ℕ) : ℚ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul,
        Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hQ
      have heq : ((W_F : ℚ) / (wY : ℚ) - 2 - (d2 : ℚ)) * (wY : ℚ) + 2 =
          (W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (d2 : ℚ) * (wY : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith
    have hres_sum : 1 ≤ c.d1 ∧ 2 ≤ c.d2 →
        (∑ i : Idx, (resOrdExact c.d1 (2 * k i - 1) c.d2 (2 * k i - 2) : ℚ)) ≤
          ((c.d2 : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1) + (c.d1 : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 2) -
            (c.d1 : ℚ) * (c.d2 : ℚ)) * (wY : ℚ) + ((c.d2 : ℚ) + 2 * (c.d1 : ℚ)) := by
      rw [hcd1, hcd2]; intro _
      have hgU : IsUnit (g.map ι) := by
        have hgd0 : (g.map ι).natDegree = 0 := by
          rw [Polynomial.natDegree_map_eq_of_injective hι, hdg_g, hdg0]
        have hC := Polynomial.eq_C_of_natDegree_eq_zero hgd0
        have hc0 : (g.map ι).coeff 0 ≠ 0 := fun h0 =>
          ((Polynomial.map_ne_zero_iff hι).mpr hg_ne) (by rw [hC, h0, map_zero])
        rw [hC]; exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hc0)
      have hrel_f : IsRelPrime (f1.map ι) (f2.map ι) := by
        intro p hp1 hp2
        have h1 : p ∣ h1.map ι := by
          rw [hf1_fac, Polynomial.map_mul] at hp1
          rcases hgU with ⟨u, hu⟩; rw [← hu] at hp1
          rcases hp1 with ⟨w, hw⟩
          exact ⟨(↑u⁻¹ : Polynomial (RatFunc Fld)) * w, by
            have := congrArg ((↑u⁻¹ : Polynomial (RatFunc Fld)) * ·) hw
            simp only [← mul_assoc, Units.inv_mul, one_mul] at this
            rw [this]; ring⟩
        have h2 : p ∣ h2.map ι := by
          rw [hf2_fac, Polynomial.map_mul] at hp2
          rcases hgU with ⟨u, hu⟩; rw [← hu] at hp2
          rcases hp2 with ⟨w, hw⟩
          exact ⟨(↑u⁻¹ : Polynomial (RatFunc Fld)) * w, by
            have := congrArg ((↑u⁻¹ : Polynomial (RatFunc Fld)) * ·) hw
            simp only [← mul_assoc, Units.inv_mul, one_mul] at this
            rw [this]; ring⟩
        exact hrel_h h1 h2
      have hRne : Polynomial.resultant f1 f2 d1 d2 ≠ 0 :=
        resultant_ne_zero_of_coprime_ratFunc f1 f2 hf1_ne hf2_ne hrel_f
      have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
          (X - C (BinaryIRSProfile.domain i)) ^ resOrdExact d1 (2 * k i - 1) d2 (2 * k i - 2) ∣
            Polynomial.resultant f1 f2 d1 d2 := fun i _ =>
        X_sub_C_pow_dvd_resultant_of_biMultGE (BinaryIRSProfile.domain i) (y i) f1 f2 d1 (2 * k i - 1) d2 (2 * k i - 2)
          (hords_all i).1 (hords_all i).2 le_rfl le_rfl
      have hdeg_R := natDegree_resultant_le_wdegBi wY (W_F - (wY - 1)) (W_F - 2 * (wY - 1)) d1 d2 f1 f2
        (by omega) (by omega) le_rfl le_rfl
      have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ _ hRne _ hdvd).trans hdeg_R
      have hQ : ((∑ i : Idx, resOrdExact d1 (2 * k i - 1) d2 (2 * k i - 2) : ℕ) : ℚ) ≤
          ((d2 * (W_F - (wY - 1)) + d1 * (W_F - 2 * (wY - 1)) - d1 * d2 * wY : ℕ) : ℚ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sum] at hQ
      have hsub_ge : d1 * d2 * wY ≤ d2 * (W_F - (wY - 1)) + d1 * (W_F - 2 * (wY - 1)) :=
        calc d1 * d2 * wY = d2 * (d1 * wY) := by ring
          _ ≤ d2 * (W_F - (wY - 1)) := Nat.mul_le_mul_left d2 (by omega)
          _ ≤ _ := Nat.le_add_right _ _
      rw [Nat.cast_sub hsub_ge, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub (by omega : wY - 1 ≤ W_F), Nat.cast_sub (by omega : 2 * (wY - 1) ≤ W_F), Nat.cast_mul,
        Nat.cast_sub (by omega : 1 ≤ wY), Nat.cast_one, show ((2 : ℕ) : ℚ) = 2 by norm_num] at hQ
      have heq : ((d2 : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1) + (d1 : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 2) -
          (d1 : ℚ) * (d2 : ℚ)) * (wY : ℚ) + ((d2 : ℚ) + 2 * (d1 : ℚ)) =
          (d2 : ℚ) * ((W_F : ℚ) - ((wY : ℚ) - 1)) + (d1 : ℚ) * ((W_F : ℚ) - 2 * ((wY : ℚ) - 1)) -
            (d1 : ℚ) * (d2 : ℚ) * (wY : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith [hQ, heq]
    have ⟨hm0, hsurp_fn⟩ := checkT2Cert_sound c hchk ((W_F : ℚ) / (wY : ℚ)) hc_lo hc_hi Az hAz k
      hf1_sum hf2_sum hlc1_sum hlc2_sum hres_sum
    have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
    have ⟨hsurp, hcap⟩ := hsurp_fn hmpos
    have hms := List.all_eq_true.mp certsT2_ms_bound c hc_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
    have hpars : 2 ≤ c.s ∧ 0 < c.cHiDen ∧ 0 < c.δNum ∧ 0 < c.δDen := by
      unfold checkT2Cert at hchk
      have hmne : (c.m != 0) = true := bne_iff_ne.mpr hm0
      by_contra hbad
      push Not at hbad
      have hfail : (c.cLoDen == 0 || c.cHiDen == 0) = true ∨
          (c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0)) = true := by
        rcases lt_or_ge c.s 2 with hs | hs
        · exact Or.inr (by simp [hmne, hs])
        · rcases Nat.eq_zero_or_pos c.cHiDen with hd | hd
          · exact Or.inl (by simp [hd])
          · rcases Nat.eq_zero_or_pos c.δNum with hdn | hdn
            · exact Or.inr (by simp [hmne, hdn])
            · rcases Nat.eq_zero_or_pos c.δDen with hdd | hdd
              · exact Or.inr (by simp [hmne, hdd])
              · exfalso; have := hbad hs hd hdn; omega
      rcases hfail with hf | hf
      · simp [hf] at hchk
      · split_ifs at hchk <;> simp_all
    have hcap_bd : c.cap.c1Bkt * 3850 + c.cap.c0Bkt ≤ T3_CAP_BOUND := by
      unfold checkT2Entry at hc_entry
      have hmne : (c.m == 0) = false := beq_false_of_ne hm0
      simp only [hmne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc_entry
      have h1 : T2_CAP_BOUND ≤ T3_CAP_BOUND := by norm_num [T2_CAP_BOUND, T3_CAP_BOUND]
      omega
    exact ⟨c.m, c.s, c.cHiNum, c.cHiDen, c.δNum, c.δDen, c.cap, hmpos, hms.1, hpars.1, hms.2,
      hpars.2.1, hpars.2.2.1, hpars.2.2.2, hc_hi, hsurp, hcap, hcap_bd⟩
  · -- TABLE 3 (`2 ≤ dg`)!
    have hdg_lo : 2 ≤ dg := by omega
    have hf0_ne : f0 ≠ 0 := by
      intro h0
      have hg_nu : ¬ IsUnit (g.map ι) := by
        intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu
        rw [Polynomial.natDegree_map_eq_of_injective hι, hdg_g] at this; omega
      exact hg_nu (hcop_all (g.map ι) (by rw [h0, Polynomial.map_zero]; exact dvd_zero _)
        ⟨h1.map ι, by rw [hf1_fac, Polynomial.map_mul]⟩
        ⟨h2.map ι, by rw [hf2_fac, Polynomial.map_mul]⟩)
    set dStar : ℕ := max d0 (max (d2 + 2) (d1 + 1))
    have hdStar_spec : dStar = max (d2 + 2) (d1 + 1) ∨
        (max (d2 + 2) (d1 + 1) < dStar ∧ dStar ≤ 24 ∧ dStar % 2 = 0) := by
      by_cases hle : d0 ≤ max (d2 + 2) (d1 + 1)
      · exact Or.inl (Nat.max_eq_right hle)
      · right
        have heq : dStar = d0 := Nat.max_eq_left (by omega)
        change d0 ≤ d1 + 1 ∨ d0 % 2 = 0 at hd0_par
        have hd0_ev : d0 % 2 = 0 := hd0_par.resolve_left (by omega)
        have hd0_wY : d0 * 1048575 ≤ W_F := (hd_wdeg f0 hf0_ne).trans hWf0
        exact ⟨by omega, by omega, by omega⟩
    have hlo_t3 : ((dStar * wY - 2 : ℕ) : ℚ) / (wY : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) := by
      apply div_le_div_of_nonneg_right _ hwYQ.le
      have h1 : (d2 + 2) * wY - 2 ≤ W_F := by change (d2 + 2) * 1048575 - 2 ≤ W_F; omega
      have h2 : (d1 + 1) * wY - 2 ≤ W_F := by change (d1 + 1) * 1048575 - 2 ≤ W_F; omega
      have h0 : d0 * wY - 2 ≤ W_F := by
        have h := (hd_wdeg f0 hf0_ne).trans hWf0; change d0 * wY ≤ W_F at h; omega
      have h3 : dStar * wY - 2 ≤ W_F := by
        rcases le_total d0 (max (d2 + 2) (d1 + 1)) with hle | hle
        · rw [show dStar = max (d2 + 2) (d1 + 1) from Nat.max_eq_right hle]
          rcases le_total (d2 + 2) (d1 + 1) with h' | h'
          · rw [Nat.max_eq_right h']; exact h2
          · rw [Nat.max_eq_left h']; exact h1
        · rw [show dStar = d0 from Nat.max_eq_left hle]; exact h0
      exact_mod_cast h3
    -- Shared T3 weight & order facts!
    set W_g : ℕ := wdegBi wY g
    set cgVal : ℚ := (W_g : ℚ) / (wY : ℚ)
    have hg_P_ne : g.eval P ≠ 0 := by
      intro h0; apply hf1_P_ne; rw [hf1_fac, Polynomial.eval_mul, h0, zero_mul]
    have hh1_P_ne : h1.eval P ≠ 0 := by
      intro h0; apply hf1_P_ne; rw [hf1_fac, Polynomial.eval_mul, h0, mul_zero]
    have hh2_P_ne : h2.eval P ≠ 0 := by
      intro h0; apply hf2_P_ne; rw [hf2_fac, Polynomial.eval_mul, h0, mul_zero]
    have hWf1_eq : wdegBi wY f1 = W_g + wdegBi wY h1 := by
      rw [hf1_fac]; exact wdegBiDom_mul wY hg_ne hh1_ne
    have hWf2_eq : wdegBi wY f2 = W_g + wdegBi wY h2 := by
      rw [hf2_fac]; exact wdegBiDom_mul wY hg_ne hh2_ne
    have hWg_lo : dg * wY ≤ W_g := by rw [← hdg_g]; exact hd_wdeg g hg_ne
    have hWh1_lo : (d1 - dg) * wY ≤ wdegBi wY h1 := by
      rw [show d1 - dg = h1.natDegree by omega]; exact hd_wdeg h1 hh1_ne
    have hWh2_lo : (d2 - dg) * wY ≤ wdegBi wY h2 := by
      rw [show d2 - dg = h2.natDegree by omega]; exact hd_wdeg h2 hh2_ne
    have hWh1_lo' : (d1 - dg) * 1048575 ≤ wdegBi wY h1 := hWh1_lo
    have hWh2_lo' : (d2 - dg) * 1048575 ≤ wdegBi wY h2 := hWh2_lo
    have hcg_lo : (dg : ℚ) ≤ cgVal := by
      dsimp [cgVal]; rw [le_div_iff₀ hwYQ]; exact_mod_cast hWg_lo
    have hcg_hi : cgVal ≤ max (dg : ℚ) ((W_F : ℚ) / (wY : ℚ) -
        ((max (2 + (d2 - dg)) (1 + (d1 - dg)) : ℕ) : ℚ) + 2 / (wY : ℚ)) := by
      refine le_max_of_le_right ?_
      have h1 : W_g + (2 + (d2 - dg)) * wY ≤ W_F + 2 := by
        change W_g + (2 + (d2 - dg)) * 1048575 ≤ W_F + 2; omega
      have h2 : W_g + (1 + (d1 - dg)) * wY ≤ W_F + 2 := by
        change W_g + (1 + (d1 - dg)) * 1048575 ≤ W_F + 2; omega
      have h3 : W_g + max (2 + (d2 - dg)) (1 + (d1 - dg)) * wY ≤ W_F + 2 := by
        rcases le_total (2 + (d2 - dg)) (1 + (d1 - dg)) with hle | hle
        · rw [Nat.max_eq_right hle]; exact h2
        · rw [Nat.max_eq_left hle]; exact h1
      have hQ : (W_g : ℚ) + ((max (2 + (d2 - dg)) (1 + (d1 - dg)) : ℕ) : ℚ) * (wY : ℚ) ≤ (W_F : ℚ) + 2 := by
        exact_mod_cast h3
      dsimp [cgVal]
      have heq : (W_F : ℚ) / (wY : ℚ) - ((max (2 + (d2 - dg)) (1 + (d1 - dg)) : ℕ) : ℚ) + 2 / (wY : ℚ) =
          ((W_F : ℚ) + 2 - ((max (2 + (d2 - dg)) (1 + (d1 - dg)) : ℕ) : ℚ) * (wY : ℚ)) / (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      rw [heq]; exact div_le_div_of_nonneg_right (by linarith) hwYQ.le
    set rr : Idx → ℕ := fun i => min (2 * k i) (biMult (BinaryIRSProfile.domain i) (y i) g)
    have hrr_le : ∀ i, rr i ≤ 2 * k i := fun i => Nat.min_le_left _ _
    have hbm_g : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) g (rr i) := fun i =>
      biMultGE_mono (Nat.min_le_right _ _) (biMultGE_biMult _ _ g)
    have hbm_h1 : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) h1 (2 * k i - 1 - rr i) := fun i => by
      have hmul := biMult_mul (BinaryIRSProfile.domain i) (y i) hg_ne hh1_ne
      rw [← hf1_fac] at hmul
      have hge := le_biMult_of_biMultGE (BinaryIRSProfile.domain i) (y i) hf1_ne (hords_all i).1
      exact biMultGE_mono (by dsimp [rr]; omega) (biMultGE_biMult _ _ h1)
    have hbm_h2 : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) h2 (2 * k i - 2 - rr i) := fun i => by
      have hmul := biMult_mul (BinaryIRSProfile.domain i) (y i) hg_ne hh2_ne
      rw [← hf2_fac] at hmul
      have hge := le_biMult_of_biMultGE (BinaryIRSProfile.domain i) (y i) hf2_ne (hords_all i).2
      exact biMultGE_mono (by dsimp [rr]; omega) (biMultGE_biMult _ _ h2)
    have hg_sum : (∑ i ∈ Az, (rr i : ℚ)) ≤ cgVal * (wY : ℚ) := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY W_g g P rr hPdeg le_rfl hg_P_ne
        (fun i hi => by rw [hagree i hi]; exact hbm_g i)
      have hQ : ((∑ i ∈ Az, rr i : ℕ) : ℚ) ≤ (W_g : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum] at hQ; dsimp [cgVal]; rw [div_mul_cancel₀ _ hwYQ.ne']; exact hQ
    have hh1_sum : (∑ i ∈ Az, ((2 * k i - 1 - rr i : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 1 - cgVal) * (wY : ℚ) + 1 := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - (wY - 1) - W_g) h1 P
        (fun i => 2 * k i - 1 - rr i) hPdeg (by omega) hh1_P_ne
        (fun i hi => by rw [hagree i hi]; exact hbm_h1 i)
      have hQ : ((∑ i ∈ Az, (2 * k i - 1 - rr i) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) - W_g : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one] at hQ
      dsimp [cgVal]
      have heq : ((W_F : ℚ) / (wY : ℚ) - 1 - (W_g : ℚ) / (wY : ℚ)) * (wY : ℚ) + 1 =
          (W_F : ℚ) - ((wY : ℚ) - 1) - (W_g : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith
    have hh2_sum : (∑ i ∈ Az, ((2 * k i - 2 - rr i : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 2 - cgVal) * (wY : ℚ) + 2 := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - 2 * (wY - 1) - W_g) h2 P
        (fun i => 2 * k i - 2 - rr i) hPdeg (by omega) hh2_P_ne
        (fun i hi => by rw [hagree i hi]; exact hbm_h2 i)
      have hQ : ((∑ i ∈ Az, (2 * k i - 2 - rr i) : ℕ) : ℚ) ≤ ((W_F - 2 * (wY - 1) - W_g : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul,
        Nat.cast_sub (by omega), Nat.cast_ofNat, Nat.cast_one] at hQ
      dsimp [cgVal]
      have heq : ((W_F : ℚ) / (wY : ℚ) - 2 - (W_g : ℚ) / (wY : ℚ)) * (wY : ℚ) + 2 =
          (W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (W_g : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith
    have hlcg_sum : (∑ i : Idx, ((rr i - dg : ℕ) : ℚ)) ≤ (cgVal - (dg : ℚ)) * (wY : ℚ) := by
      have hnat := hsum_lc g hg_ne W_g le_rfl rr hbm_g
      rw [hdg_g] at hnat
      have hQ : ((∑ i : Idx, (rr i - dg) : ℕ) : ℚ) ≤ ((W_g - dg * wY : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub hWg_lo, Nat.cast_mul] at hQ
      dsimp [cgVal]; have heq : ((W_g : ℚ) / (wY : ℚ) - (dg : ℚ)) * (wY : ℚ) = (W_g : ℚ) - (dg : ℚ) * (wY : ℚ) := by
        field_simp [hwYQ.ne']
      linarith
    have hlch1_sum : (∑ i : Idx, ((2 * k i - 1 - rr i - (d1 - dg) : ℕ) : ℚ)) ≤
        ((W_F : ℚ) / (wY : ℚ) - 1 - cgVal - ((d1 - dg : ℕ) : ℚ)) * (wY : ℚ) + 1 := by
      have hnat := hsum_lc h1 hh1_ne (W_F - (wY - 1) - W_g) (by omega) (fun i => 2 * k i - 1 - rr i) hbm_h1
      rw [show h1.natDegree = d1 - dg by omega] at hnat
      have hQ : ((∑ i : Idx, (2 * k i - 1 - rr i - (d1 - dg)) : ℕ) : ℚ) ≤
          ((W_F - (wY - 1) - W_g - (d1 - dg) * wY : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_one] at hQ
      dsimp [cgVal]
      have heq : ((W_F : ℚ) / (wY : ℚ) - 1 - (W_g : ℚ) / (wY : ℚ) - ((d1 - dg : ℕ) : ℚ)) * (wY : ℚ) + 1 =
          (W_F : ℚ) - ((wY : ℚ) - 1) - (W_g : ℚ) - ((d1 - dg : ℕ) : ℚ) * (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      linarith
    have hlch2_sum : (∑ i : Idx, ((2 * k i - 2 - rr i - (d2 - dg) : ℕ) : ℚ)) ≤
        ((W_F : ℚ) / (wY : ℚ) - 2 - cgVal - ((d2 - dg : ℕ) : ℚ)) * (wY : ℚ) + 2 := by
      have hnat := hsum_lc h2 hh2_ne (W_F - 2 * (wY - 1) - W_g) (by omega) (fun i => 2 * k i - 2 - rr i) hbm_h2
      rw [show h2.natDegree = d2 - dg by omega] at hnat
      have hQ : ((∑ i : Idx, (2 * k i - 2 - rr i - (d2 - dg)) : ℕ) : ℚ) ≤
          ((W_F - 2 * (wY - 1) - W_g - (d2 - dg) * wY : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hQ
      dsimp [cgVal]
      have heq : ((W_F : ℚ) / (wY : ℚ) - 2 - (W_g : ℚ) / (wY : ℚ) - ((d2 - dg : ℕ) : ℚ)) * (wY : ℚ) + 2 =
          (W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (W_g : ℚ) - ((d2 - dg : ℕ) : ℚ) * (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      linarith
    have hrh_sum : 1 ≤ d1 - dg ∧ 2 ≤ d2 - dg →
        (∑ i : Idx, (resOrdExact (d1 - dg) (2 * k i - 1 - rr i) (d2 - dg) (2 * k i - 2 - rr i) : ℚ)) ≤
          (((d2 - dg : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1 - cgVal) +
            ((d1 - dg : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 2 - cgVal) -
            ((d1 - dg : ℕ) : ℚ) * ((d2 - dg : ℕ) : ℚ)) * (wY : ℚ) +
            (((d2 - dg : ℕ) : ℚ) + 2 * ((d1 - dg : ℕ) : ℚ)) := by
      intro _
      have hRne : Polynomial.resultant h1 h2 (d1 - dg) (d2 - dg) ≠ 0 := by
        rw [show d1 - dg = h1.natDegree by omega, show d2 - dg = h2.natDegree by omega]
        exact resultant_ne_zero_of_coprime_ratFunc h1 h2 hh1_ne hh2_ne hrel_h
      have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
          (X - C (BinaryIRSProfile.domain i)) ^
            resOrdExact (d1 - dg) (2 * k i - 1 - rr i) (d2 - dg) (2 * k i - 2 - rr i) ∣
            Polynomial.resultant h1 h2 (d1 - dg) (d2 - dg) := fun i _ =>
        X_sub_C_pow_dvd_resultant_of_biMultGE (BinaryIRSProfile.domain i) (y i) h1 h2
          (d1 - dg) (2 * k i - 1 - rr i) (d2 - dg) (2 * k i - 2 - rr i)
          (hbm_h1 i) (hbm_h2 i) (by omega) (by omega)
      have hdeg_R := natDegree_resultant_le_wdegBi wY (W_F - (wY - 1) - W_g) (W_F - 2 * (wY - 1) - W_g)
        (d1 - dg) (d2 - dg) h1 h2 (by omega) (by omega) (by omega) (by omega)
      have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ _ hRne _ hdvd).trans hdeg_R
      have hQ : ((∑ i : Idx, resOrdExact (d1 - dg) (2 * k i - 1 - rr i) (d2 - dg) (2 * k i - 2 - rr i) : ℕ) : ℚ) ≤
          (((d2 - dg) * (W_F - (wY - 1) - W_g) + (d1 - dg) * (W_F - 2 * (wY - 1) - W_g) -
            (d1 - dg) * (d2 - dg) * wY : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum] at hQ
      have hsub_ge : (d1 - dg) * (d2 - dg) * wY ≤
          (d2 - dg) * (W_F - (wY - 1) - W_g) + (d1 - dg) * (W_F - 2 * (wY - 1) - W_g) :=
        calc (d1 - dg) * (d2 - dg) * wY = (d2 - dg) * ((d1 - dg) * wY) := by ring
          _ ≤ (d2 - dg) * (W_F - (wY - 1) - W_g) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ _ := Nat.le_add_right _ _
      rw [Nat.cast_sub hsub_ge, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub (by omega : W_g ≤ W_F - (wY - 1)), Nat.cast_sub (by omega : wY - 1 ≤ W_F),
        Nat.cast_sub (by omega : W_g ≤ W_F - 2 * (wY - 1)), Nat.cast_sub (by omega : 2 * (wY - 1) ≤ W_F),
        Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ wY), Nat.cast_one, show ((2 : ℕ) : ℚ) = 2 by norm_num] at hQ
      dsimp [cgVal]
      have heq : (((d2 - dg : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1 - (W_g : ℚ) / (wY : ℚ)) +
          ((d1 - dg : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 2 - (W_g : ℚ) / (wY : ℚ)) -
          ((d1 - dg : ℕ) : ℚ) * ((d2 - dg : ℕ) : ℚ)) * (wY : ℚ) +
          (((d2 - dg : ℕ) : ℚ) + 2 * ((d1 - dg : ℕ) : ℚ)) =
          ((d2 - dg : ℕ) : ℚ) * ((W_F : ℚ) - ((wY : ℚ) - 1) - (W_g : ℚ)) +
          ((d1 - dg : ℕ) : ℚ) * ((W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (W_g : ℚ)) -
          ((d1 - dg : ℕ) : ℚ) * ((d2 - dg : ℕ) : ℚ) * (wY : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith [hQ, heq]
    -- Shared helper for mode ∈ {0, 1} hrf0 bound!
    have hrf0_std : ∀ (mode : ℕ), mode = 0 ∨ mode = 1 →
        (∑ i : Idx, (t3Vrf0Ord mode dg dStar (k i) (rr i) : ℚ)) ≤
          ((dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - (dStar : ℚ)) + (dStar : ℚ) * cgVal) * (wY : ℚ) := by
      intro mode hmode
      have hrel_f0g : IsRelPrime (f0.map ι) (g.map ι) := fun p hp0 hpg =>
        hcop_all p hp0 (hpg.trans ⟨h1.map ι, by rw [hf1_fac, Polynomial.map_mul]⟩)
          (hpg.trans ⟨h2.map ι, by rw [hf2_fac, Polynomial.map_mul]⟩)
      set R : Polynomial Fld := g.leadingCoeff ^ (dStar - d0) * Polynomial.resultant f0 g d0 dg
      have hRne : R ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hg_ne))
        (by rw [← hdg_g]; exact resultant_ne_zero_of_coprime_ratFunc f0 g hf0_ne hg_ne hrel_f0g)
      have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
          (X - C (BinaryIRSProfile.domain i)) ^ t3Vrf0Ord mode dg dStar (k i) (rr i) ∣ R := by
        intro i _
        have hmono := t3Vrf0Ord_mono_std mode dg dStar (k i) (by omega)
          (Nat.min_le_right (2 * k i) (biMult (BinaryIRSProfile.domain i) (y i) g))
        refine (pow_dvd_pow _ hmono).trans ?_
        have hg_ev : ∀ j, j % 2 = 1 → g.coeff j = 0 := (deriv_eq_zero_iff_even_coeffs g).mp hg_d
        have ⟨hvk, hvp⟩ := kerD2_resY_f0_g_ord hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)
          g hg_ne hg_ev (by change g ∣ f1; rw [hf1_fac]; exact dvd_mul_right _ _)
          (by change g ∣ f2; rw [hf2_fac]; exact dvd_mul_right _ _)
          dStar le_rfl
        rw [hdg_g] at hvk hvp
        by_cases hk0 : k i = 0
        · simp [t3Vrf0Ord, hk0]
        · have hk0b : (k i == 0) = false := beq_false_of_ne hk0
          rcases hmode with rfl | rfl
          · unfold t3Vrf0Ord; simp only [hk0b, Bool.false_eq_true, ↓reduceIte,
              show (0 == 3) = false by decide, show (0 == 1 || 0 == 2) = false by decide, resOrdWeighted2Fast_eq]
            exact hvk
          · unfold t3Vrf0Ord; simp only [hk0b, Bool.false_eq_true, ↓reduceIte,
              show (1 == 3) = false by decide, show (1 == 1 || 1 == 2) = true by decide, resOrdWeighted2Fast_eq]
            rcases le_total (resOrdWeighted dStar (4 * k i + 4) (dg / 2) (biMult (BinaryIRSProfile.domain i) (y i) g) 2 - 2 * dg)
                (((List.range (dStar + 1)).map (fun d0' =>
                  resOrdExact d0' (2 * k i - 2) dg (biMult (BinaryIRSProfile.domain i) (y i) g) +
                    (dStar - d0') * (biMult (BinaryIRSProfile.domain i) (y i) g - dg))).foldl Nat.min
                      (resOrdExact 0 (2 * k i - 2) dg (biMult (BinaryIRSProfile.domain i) (y i) g) +
                        dStar * (biMult (BinaryIRSProfile.domain i) (y i) g - dg))) with hle | hle
            · rw [Nat.max_eq_right hle]
              refine (pow_dvd_pow _ (foldl_map_min_le_mem _ (List.range (dStar + 1)) _ d0
                (List.mem_range.mpr (by omega)))).trans hvp
            · rw [Nat.max_eq_left hle]; exact hvk
      have hdeg_lc : g.leadingCoeff.natDegree ≤ W_g - dg * wY := by
        have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg_ne)
        have hle := (wdegBi_le_iff wY W_g g).mp le_rfl dg _ (by rwa [← hdg_g]); omega
      have hdeg_res := natDegree_resultant_le_wdegBi wY W_F W_g d0 dg f0 g hWf0 le_rfl le_rfl (le_of_eq hdg_g)
      have hdeg_R : R.natDegree + dg * dStar * wY ≤ dg * W_F + dStar * W_g := by
        have h1 : R.natDegree ≤ (dStar - d0) * g.leadingCoeff.natDegree + (Polynomial.resultant f0 g d0 dg).natDegree :=
          Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_pow_le _)
        have h2 : (dStar - d0) * g.leadingCoeff.natDegree ≤ (dStar - d0) * (W_g - dg * wY) :=
          Nat.mul_le_mul_left _ hdeg_lc
        have hd0_le : d0 ≤ dStar := le_max_left _ _
        have hmul_le : d0 * dg * wY ≤ d0 * W_g := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left d0 hWg_lo
        have hsub1 : (dStar - d0) * (W_g - dg * wY) + (dStar - d0) * (dg * wY) = (dStar - d0) * W_g := by
          rw [← mul_add, Nat.sub_add_cancel hWg_lo]
        have hsum_d : (dStar - d0) * W_g + d0 * W_g = dStar * W_g := by
          rw [← add_mul, Nat.sub_add_cancel hd0_le]
        have hsum_w : (dStar - d0) * (dg * wY) + d0 * dg * wY = dg * dStar * wY := by
          rw [mul_assoc d0, ← add_mul, Nat.sub_add_cancel hd0_le]; ring
        omega
      have hnat := sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ R hRne _ hdvd
      have hQ : ((∑ i : Idx, t3Vrf0Ord mode dg dStar (k i) (rr i) : ℕ) : ℚ) + (dg : ℚ) * (dStar : ℚ) * (wY : ℚ) ≤
          (dg : ℚ) * (W_F : ℚ) + (dStar : ℚ) * (W_g : ℚ) := by
        have htot : (∑ i : Idx, t3Vrf0Ord mode dg dStar (k i) (rr i)) + dg * dStar * wY ≤ dg * W_F + dStar * W_g := by omega
        have htotQ : (((∑ i : Idx, t3Vrf0Ord mode dg dStar (k i) (rr i)) + dg * dStar * wY : ℕ) : ℚ) ≤
            ((dg * W_F + dStar * W_g : ℕ) : ℚ) := by exact_mod_cast htot
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at htotQ
        exact htotQ
      rw [Nat.cast_sum] at hQ
      dsimp [cgVal]
      have heq : ((dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - (dStar : ℚ)) + (dStar : ℚ) * ((W_g : ℚ) / (wY : ℚ))) * (wY : ℚ) =
          (dg : ℚ) * (W_F : ℚ) + (dStar : ℚ) * (W_g : ℚ) - (dg : ℚ) * (dStar : ℚ) * (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      linarith
    -- Shared helper for mode = 3 (Subcase 2A, dStar = 11, dStarEff = 10)!
    have hrf0_2A : (∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) →
        dStar = 11 →
        (∑ i : Idx, (t3Vrf0Ord 3 dg 10 (k i) (rr i) : ℚ)) ≤
          ((dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - (10 : ℚ)) + (10 : ℚ) * cgVal) * (wY : ℚ) := by
      intro hgP_X2Y2 hdStar11
      set A0 : BiPoly Fld := ∑ j ∈ Finset.range (f0.natDegree / 2 + 1), Polynomial.monomial j (f0.coeff (2 * j))
      have ⟨hA0_c, hf0_sp⟩ := char2_biPoly_eq_expand2_add_X_deriv f0
      set A0exp : BiPoly Fld := Polynomial.expand (Polynomial Fld) 2 A0
      have hA0_deg : 2 * A0.natDegree ≤ 10 := by
        have hle : A0.natDegree ≤ f0.natDegree / 2 := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
          rw [hA0_c]; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have hd0_le11 : d0 ≤ 11 := by have : d0 ≤ dStar := le_max_left _ _; omega
        omega
      have hdA_eq : A0exp.natDegree = 2 * A0.natDegree := by
        dsimp [A0exp]; rw [Polynomial.natDegree_expand, mul_comm]
      have hWA0 : wdegBi wY A0exp ≤ W_F := by
        rw [wdegBi_le_iff]; intro j i hnz
        dsimp [A0exp] at hnz
        rw [Polynomial.coeff_expand (by norm_num : 0 < 2)] at hnz
        split_ifs at hnz with hj
        · rw [hA0_c, show 2 * (j / 2) = j by omega] at hnz
          exact (wdegBi_le_iff wY W_F f0).mp hWf0 j i hnz
        · simp at hnz
      have hgP_dvd_dX : gPrim ∣ f0.derivative := by
        rw [hf0_d, hf1_fac]; dsimp only [g]
        rw [mul_assoc, B6401ContactKerD.dXBi_mul]
        have hdX_gP : B6401ContactKerD.dXBi gPrim = 0 :=
          (dXBi_eq_zero_iff_even_X gPrim).mpr fun j i hi => by
            by_contra hnz; have := hgP_X2Y2 j i hnz; omega
        rw [B6401ContactKerD.dXBi_mul, hdX_gP, zero_mul, zero_add]
        exact dvd_add ⟨B6401ContactKerD.dXBi (C qX) * h1, by ring⟩ ⟨C qX * B6401ContactKerD.dXBi h1, by ring⟩
      have hrel_A0g : IsRelPrime (A0exp.map ι) (g.map ι) := by
        intro p hpA hpg
        have hqU : IsUnit (C (ι qX) : Polynomial (RatFunc Fld)) :=
          Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (fun h => hqX_ne (hι (h.trans (map_zero ι).symm))))
        have hpgP : p ∣ gPrim.map ι := by
          dsimp [g] at hpg; rw [Polynomial.map_mul, Polynomial.map_C] at hpg
          rcases hqU with ⟨u, hu⟩; rw [← hu] at hpg
          rcases hpg with ⟨w, hw⟩
          exact ⟨(↑u⁻¹ : Polynomial (RatFunc Fld)) * w, by
            have := congrArg ((↑u⁻¹ : Polynomial (RatFunc Fld)) * ·) hw
            simp only [← mul_assoc, Units.inv_mul, one_mul] at this
            rw [this]; ring⟩
        have hp_f0 : p ∣ f0.map ι := by
          rw [hf0_sp, Polynomial.map_add, Polynomial.map_mul]
          refine dvd_add hpA (dvd_mul_of_dvd_right (hpgP.trans ?_) _)
          rcases hgP_dvd_dX with ⟨w, hw⟩; exact ⟨w.map ι, by rw [hw, Polynomial.map_mul]⟩
        exact hcop_all p hp_f0
          (hpg.trans ⟨h1.map ι, by rw [hf1_fac, Polynomial.map_mul]⟩)
          (hpg.trans ⟨h2.map ι, by rw [hf2_fac, Polynomial.map_mul]⟩)
      have hA0_ne : A0exp ≠ 0 := by
        intro h0
        have hg_nu : ¬ IsUnit (g.map ι) := by
          intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu
          rw [Polynomial.natDegree_map_eq_of_injective hι, hdg_g] at this; omega
        exact hg_nu (hrel_A0g (by rw [h0, Polynomial.map_zero]; exact dvd_zero _) dvd_rfl)
      set R : Polynomial Fld := g.leadingCoeff ^ (10 - A0exp.natDegree) * Polynomial.resultant A0exp g A0exp.natDegree dg
      have hRne : R ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hg_ne))
        (by rw [← hdg_g]; exact resultant_ne_zero_of_coprime_ratFunc A0exp g hA0_ne hg_ne hrel_A0g)
      have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
          (X - C (BinaryIRSProfile.domain i)) ^ t3Vrf0Ord 3 dg 10 (k i) (rr i) ∣ R := by
        intro i _
        refine (pow_dvd_pow _ (t3Vrf0Ord_mode3_le_min_two_mul dg 10 (k i) _)).trans ?_
        have hord := kerD2_resY_f0_g_2A_ord hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)
          qX gPrim A0 hqX_ne hgP_ne hgP_X2Y2 hA0_c
          (by change gPrim ∣ f1; rw [hf1_fac]; dsimp only [g]; exact ⟨C qX * h1, by ring⟩)
          (by change gPrim ∣ f2; rw [hf2_fac]; dsimp only [g]; exact ⟨C qX * h2, by ring⟩)
          10 (by decide) hA0_deg
          (by change d1 ≤ 10; have : d1 + 1 ≤ dStar := le_trans (le_max_right _ _) (le_max_right _ _); omega)
          (by change d2 + 2 ≤ 10; have : d2 + 2 ≤ dStar := le_trans (le_max_left _ _) (le_max_right _ _); omega)
        simpa only [g, dg, A0exp, hdg_g] using hord
      have hdeg_lc : g.leadingCoeff.natDegree ≤ W_g - dg * wY := by
        have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg_ne)
        have hle := (wdegBi_le_iff wY W_g g).mp le_rfl dg _ (by rwa [← hdg_g]); omega
      have hdeg_res := natDegree_resultant_le_wdegBi wY W_F W_g A0exp.natDegree dg A0exp g hWA0 le_rfl le_rfl (le_of_eq hdg_g)
      have hdeg_R : R.natDegree + dg * 10 * wY ≤ dg * W_F + 10 * W_g := by
        have h1 : R.natDegree ≤ (10 - A0exp.natDegree) * g.leadingCoeff.natDegree +
            (Polynomial.resultant A0exp g A0exp.natDegree dg).natDegree :=
          Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_pow_le _)
        have h2 : (10 - A0exp.natDegree) * g.leadingCoeff.natDegree ≤ (10 - A0exp.natDegree) * (W_g - dg * wY) :=
          Nat.mul_le_mul_left _ hdeg_lc
        have hdA_le : A0exp.natDegree ≤ 10 := by omega
        have hmul_le : A0exp.natDegree * dg * wY ≤ A0exp.natDegree * W_g := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left A0exp.natDegree hWg_lo
        have hsub1 : (10 - A0exp.natDegree) * (W_g - dg * wY) + (10 - A0exp.natDegree) * (dg * wY) =
            (10 - A0exp.natDegree) * W_g := by rw [← mul_add, Nat.sub_add_cancel hWg_lo]
        have hsum_d : (10 - A0exp.natDegree) * W_g + A0exp.natDegree * W_g = 10 * W_g := by
          rw [← add_mul, Nat.sub_add_cancel hdA_le]
        have hsum_w : (10 - A0exp.natDegree) * (dg * wY) + A0exp.natDegree * dg * wY = dg * 10 * wY := by
          rw [mul_assoc A0exp.natDegree, ← add_mul, Nat.sub_add_cancel hdA_le]; ring
        omega
      have hnat := sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ R hRne _ hdvd
      have htot : (∑ i : Idx, t3Vrf0Ord 3 dg 10 (k i) (rr i)) + dg * 10 * wY ≤ dg * W_F + 10 * W_g := by omega
      have hQ : ((∑ i : Idx, t3Vrf0Ord 3 dg 10 (k i) (rr i) : ℕ) : ℚ) + (dg : ℚ) * 10 * (wY : ℚ) ≤
          (dg : ℚ) * (W_F : ℚ) + 10 * (W_g : ℚ) := by
        have htotQ : (((∑ i : Idx, t3Vrf0Ord 3 dg 10 (k i) (rr i)) + dg * 10 * wY : ℕ) : ℚ) ≤
            ((dg * W_F + 10 * W_g : ℕ) : ℚ) := by exact_mod_cast htot
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat] at htotQ
        exact htotQ
      rw [Nat.cast_sum] at hQ
      dsimp [cgVal]
      have heq : ((dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 10) + 10 * ((W_g : ℚ) / (wY : ℚ))) * (wY : ℚ) =
          (dg : ℚ) * (W_F : ℚ) + 10 * (W_g : ℚ) - (dg : ℚ) * 10 * (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      linarith
    -- Shared helper to conclude from any T3Cert `c ∈ certsT3All` with `checkT3Entry c = true`!
    have hfinish_t3 : ∀ c ∈ certsT3All, c.d2 = d2 → c.dg = dg → c.d1 = d1 → checkT3Entry c = true →
        (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) →
        (W_F : ℚ) / (wY : ℚ) ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ) →
        c.mode ≠ 2 →
        (c.hasDStar = true →
          let dStarEff : ℕ := if c.mode == 3 then c.dStar - 1 else c.dStar
          (∑ i : Idx, (t3Vrf0Ord c.mode c.dg dStarEff (k i) (rr i) : ℚ)) ≤
            ((c.dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - (dStarEff : ℚ)) + (dStarEff : ℚ) * cgVal) * (wY : ℚ)) →
        ∃ (m s cHiNum cHiDen δNum δDen : ℕ) (w : CapWitness),
          0 < m ∧ m ≤ 3000 ∧ 2 ≤ s ∧ s ≤ 300 ∧ 0 < cHiDen ∧ 0 < δNum ∧ 0 < δDen ∧
          (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ) ∧
          (δNum : ℚ) / (δDen : ℚ) <
            vquotLbQ 2 m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 2 m s (k i)) / (N : ℚ) ∧
          checkCapWitness 2 m s cHiNum cHiDen δNum δDen 1 1 1 w = true ∧
          w.c1Bkt * 3850 + w.c0Bkt ≤ T3_CAP_BOUND := by
      intro c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi hmode2 hrf0
      have hchk : checkT3Cert c = true := (Bool.and_eq_true _ _).mp hc_entry |>.1
      have ⟨hm0, hsurp_fn⟩ := checkT3Cert_sound c hchk ((W_F : ℚ) / (wY : ℚ)) cgVal hc_lo hc_hi
        (by rw [hcdg]; exact hcg_lo) (by rw [hcd2, hcd1, hcdg]; exact hcg_hi)
        Az hAz k rr hrr_le hg_sum hh1_sum hh2_sum
        (by rw [hcdg]; exact hlcg_sum) (by rw [hcd1, hcdg]; exact hlch1_sum)
        (by rw [hcd2, hcdg]; exact hlch2_sum) (by rw [hcd1, hcd2, hcdg]; exact hrh_sum)
        hrf0 (fun h2 => absurd h2 hmode2)
      have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
      have ⟨hsurp, hcap⟩ := hsurp_fn hmpos
      have ⟨hmle, hsle⟩ := certsT3All_ms_bound c hc_mem
      have hpars : 2 ≤ c.s ∧ 0 < c.cHiDen ∧ 0 < c.δNum ∧ 0 < c.δDen := by
        unfold checkT3Cert at hchk
        have hmne : (c.m != 0) = true := bne_iff_ne.mpr hm0
        by_contra hbad; push Not at hbad
        have hfail : (c.cLoDen == 0 || c.cHiDen == 0 || c.dg == 0 || c.dg > c.d1 || c.dg > c.d2) = true ∨
            (c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0)) = true := by
          rcases lt_or_ge c.s 2 with hs | hs
          · exact Or.inr (by simp [hmne, hs])
          · rcases Nat.eq_zero_or_pos c.cHiDen with hd | hd
            · exact Or.inl (by simp [hd])
            · rcases Nat.eq_zero_or_pos c.δNum with hdn | hdn
              · exact Or.inr (by simp [hmne, hdn])
              · rcases Nat.eq_zero_or_pos c.δDen with hdd | hdd
                · exact Or.inr (by simp [hmne, hdd])
                · exfalso; have := hbad hs hd hdn; omega
        rcases hfail with hf | hf
        · simp [hf] at hchk
        · split_ifs at hchk <;> simp_all
      have hcap_bd : c.cap.c1Bkt * 3850 + c.cap.c0Bkt ≤ T3_CAP_BOUND := by
        unfold checkT3Entry at hc_entry
        have hmne : (c.m == 0) = false := beq_false_of_ne hm0
        simp only [hmne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc_entry
        exact hc_entry.2
      exact ⟨c.m, c.s, c.cHiNum, c.cHiDen, c.δNum, c.δDen, c.cap, hmpos, hmle, hpars.1, hsle,
        hpars.2.1, hpars.2.2.1, hpars.2.2.2, hc_hi, hsurp, hcap, hcap_bd⟩
    -- Dispatch via `exists_t3Cert`!
    rcases exists_t3Cert d2 dg d1 dStar (by omega) hd2_le22 hd2_ev hdg_lo (by omega) hdg_ev
        (by omega) hd1_le24 hd1_par hdStar_spec ((W_F : ℚ) / (wY : ℚ)) hlo_t3 hWF_hi with
      ⟨c, hc_mem, hcd2, hcdg, hcd1, hc_entry, hmode_cases, hc_lo, hc_hi⟩ |
      ⟨hd2_8, hdg_6, hd1_10, hdStar_11, ⟨cA, hcA_mem, hA2, hAg, hA1, hcA_entry, hA_hd, hA_ds, hA_m, hA_lo, hA_hi⟩, h2B_cov⟩
    · rcases hmode_cases with ⟨hno, hm0⟩ | ⟨hhas, hcds, hm_cases⟩
      · exact hfinish_t3 c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi (by omega) (fun h => by rw [hno] at h; cases h)
      · rcases hm_cases with hm0 | hm1 | ⟨hd2_8, hdg_8, hd1_10, hds_11, hm3⟩
        · refine hfinish_t3 c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi (by omega) (fun _ => ?_)
          dsimp only; rw [hm0, hcds, hcdg]; simp only [show (0 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hrf0_std 0 (Or.inl rfl)
        · refine hfinish_t3 c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi (by omega) (fun _ => ?_)
          dsimp only; rw [hm1, hcds, hcdg]; simp only [show (1 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hrf0_std 1 (Or.inr rfl)
        · have hh2_0 : h2.natDegree = 0 := by omega
          have hgP_X2Y2 := (kerD2_2A_2B_dichotomy hgP_prim hgP_ne hh1_ne hh2_ne hgP_d hh2_d hrel_h hdvd_dX).1 hh2_0
          refine hfinish_t3 c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi (by omega) (fun _ => ?_)
          dsimp only; rw [hm3, hcds, hcdg, hds_11]
          simp only [beq_self_eq_true, ↓reduceIte]
          exact hrf0_2A hgP_X2Y2 hds_11
    · -- Special case `(d2, dg, d1, dStar) = (8, 6, 10, 11)`: 2A / 2B dichotomy!
      have hgP6 : gPrim.natDegree = 6 := hdg_6
      have hh2_2 : h2.natDegree = 2 := by omega
      rcases (kerD2_2A_2B_dichotomy hgP_prim hgP_ne hh1_ne hh2_ne hgP_d hh2_d hrel_h hdvd_dX).2 hgP6 hh2_2 with
        hgP_X2Y2 | ⟨uX, q, g1, huX_ne, hq_prim, hq_ne, hg1_ne, hq_deg, hg1_deg, hq_d, hg1_d, hh2_eq, hgP_eq, hrel_q⟩
      · -- Subcase 2A!
        refine hfinish_t3 cA hcA_mem (by omega) (by omega) (by omega) hcA_entry hA_lo hA_hi (by omega) (fun _ => ?_)
        dsimp only
        rcases hA_m with hm3 | hm0
        · rw [hm3, hA_ds, hAg, ← hdg_6]
          simp only [beq_self_eq_true, ↓reduceIte]
          exact hrf0_2A hgP_X2Y2 hdStar_11
        · rw [hm0, hA_ds, hAg, ← hdg_6, ← hdStar_11]
          simp only [show (0 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hrf0_std 0 (Or.inl rfl)
      · -- Subcase 2B!
        rcases h2B_cov with ⟨b, hb_mem, hb_entry, hb_lo, hb_hi⟩ |
            ⟨cS, hcS_mem, hS2, hSg, hS1, hcS_entry, hS_hd, hS_ds, hS_m, hS_lo, hS_hi⟩
        · -- Apply `checkT3_2BCert_sound b`!
          have hchk_b : checkT3_2BCert b = true := (Bool.and_eq_true _ _).mp hb_entry |>.1
          set g1' : BiPoly Fld := C qX * g1
          have hg1'_ne : g1' ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hqX_ne) hg1_ne
          have hg_fac : g = q * g1' := by dsimp [g, g1']; rw [hgP_eq]; ring
          have hg1'_deg : g1'.natDegree = 4 := by dsimp [g1']; rw [Polynomial.natDegree_C_mul hqX_ne, hg1_deg]
          have hg1'_d : g1'.derivative = 0 := by
            dsimp [g1']; rw [Polynomial.derivative_mul, Polynomial.derivative_C, hg1_d, zero_mul, mul_zero, add_zero]
          set W_q : ℕ := wdegBi wY q
          set W_g1' : ℕ := wdegBi wY g1'
          set cqVal : ℚ := (W_q : ℚ) / (wY : ℚ)
          have hWg_split : W_g = W_q + W_g1' := by
            dsimp only [W_g, W_q, W_g1']; rw [hg_fac]; exact wdegBiDom_mul wY hq_ne hg1'_ne
          have hWq_lo : 2 * wY ≤ W_q := by rw [← hq_deg]; exact hd_wdeg q hq_ne
          have hWg1'_lo : 4 * wY ≤ W_g1' := by rw [← hg1'_deg]; exact hd_wdeg g1' hg1'_ne
          have hWq_lo' : 2 * 1048575 ≤ W_q := hWq_lo
          have hcq_lo : (2 : ℚ) ≤ cqVal := by dsimp [cqVal]; rw [le_div_iff₀ hwYQ]; exact_mod_cast hWq_lo
          have hcg_lo_2B : cqVal + 4 ≤ cgVal := by
            dsimp [cqVal, cgVal]
            have h1 : W_q + 4 * wY ≤ W_g := by omega
            have hQ : (W_q : ℚ) + 4 * (wY : ℚ) ≤ (W_g : ℚ) := by exact_mod_cast h1
            have heq : (W_q : ℚ) / (wY : ℚ) + 4 = ((W_q : ℚ) + 4 * (wY : ℚ)) / (wY : ℚ) := by field_simp [hwYQ.ne']
            rw [heq]; exact div_le_div_of_nonneg_right hQ hwYQ.le
          have hcg_hi1 : cgVal ≤ (W_F : ℚ) / (wY : ℚ) - 5 + 2 / (wY : ℚ) := by
            have h1 : W_g + 5 * wY ≤ W_F + 2 := by
              have hwh1 : 4 * 1048575 ≤ wdegBi wY h1 := by
                have : d1 - dg = 4 := by omega
                simpa [this] using hWh1_lo'
              change W_g + 5 * 1048575 ≤ W_F + 2; omega
            have hQ : (W_g : ℚ) + 5 * (wY : ℚ) ≤ (W_F : ℚ) + 2 := by exact_mod_cast h1
            dsimp [cgVal]
            have heq : (W_F : ℚ) / (wY : ℚ) - 5 + 2 / (wY : ℚ) = ((W_F : ℚ) + 2 - 5 * (wY : ℚ)) / (wY : ℚ) := by
              field_simp [hwYQ.ne']; ring
            rw [heq]; exact div_le_div_of_nonneg_right (by linarith) hwYQ.le
          set rq : Idx → ℕ := fun i => min (rr i) (biMult (BinaryIRSProfile.domain i) (y i) q)
          have hrq_le : ∀ i, rq i ≤ rr i := fun i => Nat.min_le_left _ _
          have hbm_q : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) q (rq i) := fun i =>
            biMultGE_mono (Nat.min_le_right _ _) (biMultGE_biMult _ _ q)
          have hbm_g1' : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) g1' (rr i - rq i) := fun i => by
            have hmul := biMult_mul (BinaryIRSProfile.domain i) (y i) hq_ne hg1'_ne
            rw [← hg_fac] at hmul
            have hle : rr i - rq i ≤ biMult (BinaryIRSProfile.domain i) (y i) g1' := by
              dsimp [rq, rr]; omega
            exact biMultGE_mono hle (biMultGE_biMult _ _ g1')
          have hbm_uX : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) (C uX) (2 * k i - 2 - rr i - rq i) := fun i => by
            have hmul1 := biMult_mul (BinaryIRSProfile.domain i) (y i) hg_ne hh2_ne
            rw [← hf2_fac] at hmul1
            have hmul2 := biMult_mul (BinaryIRSProfile.domain i) (y i) (Polynomial.C_ne_zero.mpr huX_ne) hq_ne
            rw [← hh2_eq] at hmul2
            have hmul3 := biMult_mul (BinaryIRSProfile.domain i) (y i) hq_ne hg1'_ne
            rw [← hg_fac] at hmul3
            have hge := le_biMult_of_biMultGE (BinaryIRSProfile.domain i) (y i) hf2_ne (hords_all i).2
            have hle : 2 * k i - 2 - rr i - rq i ≤ biMult (BinaryIRSProfile.domain i) (y i) (C uX) := by
              dsimp [rq, rr]; omega
            exact biMultGE_mono hle (biMultGE_biMult _ _ (C uX))
          have hq_P_ne : q.eval P ≠ 0 := by
            intro h0; apply hg_P_ne; rw [hg_fac, Polynomial.eval_mul, h0, zero_mul]
          have hg1'_P_ne : g1'.eval P ≠ 0 := by
            intro h0; apply hg_P_ne; rw [hg_fac, Polynomial.eval_mul, h0, mul_zero]
          have hq_sum : (∑ i ∈ Az, (rq i : ℚ)) ≤ cqVal * (wY : ℚ) := by
            have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY W_q q P rq hPdeg le_rfl hq_P_ne
              (fun i hi => by rw [hagree i hi]; exact hbm_q i)
            have hQ : ((∑ i ∈ Az, rq i : ℕ) : ℚ) ≤ (W_q : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum] at hQ; dsimp [cqVal]; rw [div_mul_cancel₀ _ hwYQ.ne']; exact hQ
          have hg1'_sum : (∑ i ∈ Az, ((rr i - rq i : ℕ) : ℚ)) ≤ (cgVal - cqVal) * (wY : ℚ) := by
            have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY W_g1' g1' P (fun i => rr i - rq i)
              hPdeg le_rfl hg1'_P_ne (fun i hi => by rw [hagree i hi]; exact hbm_g1' i)
            have hQ : ((∑ i ∈ Az, (rr i - rq i) : ℕ) : ℚ) ≤ (W_g1' : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum] at hQ; dsimp [cgVal, cqVal]
            have heq : ((W_g : ℚ) / (wY : ℚ) - (W_q : ℚ) / (wY : ℚ)) * (wY : ℚ) = (W_g1' : ℚ) := by
              rw [hWg_split, Nat.cast_add]; field_simp [hwYQ.ne']; ring
            linarith
          have hu_sum : (∑ i : Idx, ((2 * k i - 2 - rr i - rq i : ℕ) : ℚ)) ≤
              ((W_F : ℚ) / (wY : ℚ) - 2 - cgVal - cqVal) * (wY : ℚ) + 2 := by
            have hWh2_eq : wdegBi wY h2 = uX.natDegree + W_q := by
              rw [hh2_eq]
              have h1 := wdegBiDom_mul wY (Polynomial.C_ne_zero.mpr huX_ne) hq_ne
              rwa [wdegBiDom_C] at h1
            have hnat := hsum_lc (C uX) (Polynomial.C_ne_zero.mpr huX_ne) uX.natDegree
              (by rw [show wdegBi wY (C uX) = uX.natDegree from wdegBiDom_C wY uX])
              (fun i => 2 * k i - 2 - rr i - rq i) hbm_uX
            simp only [Polynomial.natDegree_C, Nat.sub_zero, zero_mul] at hnat
            have hle_uX : uX.natDegree ≤ W_F - 2 * (wY - 1) - W_g - W_q := by omega
            have hQ : ((∑ i : Idx, (2 * k i - 2 - rr i - rq i) : ℕ) : ℚ) ≤
                ((W_F - 2 * (wY - 1) - W_g - W_q : ℕ) : ℚ) := by exact_mod_cast (hnat.trans hle_uX)
            rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
              Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_ofNat, Nat.cast_one] at hQ
            dsimp [cgVal, cqVal]
            have heq : ((W_F : ℚ) / (wY : ℚ) - 2 - (W_g : ℚ) / (wY : ℚ) - (W_q : ℚ) / (wY : ℚ)) * (wY : ℚ) + 2 =
                (W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (W_g : ℚ) - (W_q : ℚ) := by field_simp [hwYQ.ne']; ring
            linarith
          have hlcq_sum : (∑ i : Idx, ((rq i - 2 : ℕ) : ℚ)) ≤ (cqVal - 2) * (wY : ℚ) := by
            have hnat := hsum_lc q hq_ne W_q le_rfl rq hbm_q
            rw [hq_deg] at hnat
            have hQ : ((∑ i : Idx, (rq i - 2) : ℕ) : ℚ) ≤ ((W_q - 2 * wY : ℕ) : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum, Nat.cast_sub hWq_lo, Nat.cast_mul, Nat.cast_ofNat] at hQ
            dsimp [cqVal]; have heq : ((W_q : ℚ) / (wY : ℚ) - 2) * (wY : ℚ) = (W_q : ℚ) - 2 * (wY : ℚ) := by
              field_simp [hwYQ.ne']
            linarith
          have hlcg1_sum : (∑ i : Idx, ((rr i - rq i - 4 : ℕ) : ℚ)) ≤ (cgVal - cqVal - 4) * (wY : ℚ) := by
            have hnat := hsum_lc g1' hg1'_ne W_g1' le_rfl (fun i => rr i - rq i) hbm_g1'
            rw [hg1'_deg] at hnat
            have hQ : ((∑ i : Idx, (rr i - rq i - 4) : ℕ) : ℚ) ≤ ((W_g1' - 4 * wY : ℕ) : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum, Nat.cast_sub hWg1'_lo, Nat.cast_mul, Nat.cast_ofNat] at hQ
            dsimp [cgVal, cqVal]
            have heq : ((W_g : ℚ) / (wY : ℚ) - (W_q : ℚ) / (wY : ℚ) - 4) * (wY : ℚ) = (W_g1' : ℚ) - 4 * (wY : ℚ) := by
              rw [hWg_split, Nat.cast_add]; field_simp [hwYQ.ne']; ring
            linarith
          have hlch1_2B : (∑ i : Idx, ((2 * k i - 1 - rr i - 4 : ℕ) : ℚ)) ≤
              ((W_F : ℚ) / (wY : ℚ) - 5 - cgVal) * (wY : ℚ) + 1 := by
            have h1 := hlch1_sum; rw [show d1 - dg = 4 by omega] at h1
            have : (W_F : ℚ) / (wY : ℚ) - 1 - cgVal - ((4 : ℕ) : ℚ) = (W_F : ℚ) / (wY : ℚ) - 5 - cgVal := by
              push_cast; ring
            rwa [this] at h1
          have hrq_res : (∑ i : Idx, (resOrdExact 4 (2 * k i - 1 - rr i) 2 (rq i) : ℚ)) ≤
              (2 * ((W_F : ℚ) / (wY : ℚ) - 1 - cgVal) + 4 * cqVal - 8) * (wY : ℚ) + 2 := by
            have hh1_4 : h1.natDegree = 4 := by omega
            have hRne : Polynomial.resultant h1 q 4 2 ≠ 0 := by
              rw [← hh1_4, ← hq_deg]; exact resultant_ne_zero_of_coprime_ratFunc h1 q hh1_ne hq_ne hrel_q
            have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
                (X - C (BinaryIRSProfile.domain i)) ^ resOrdExact 4 (2 * k i - 1 - rr i) 2 (rq i) ∣
                  Polynomial.resultant h1 q 4 2 := fun i _ =>
              X_sub_C_pow_dvd_resultant_of_biMultGE (BinaryIRSProfile.domain i) (y i) h1 q
                4 (2 * k i - 1 - rr i) 2 (rq i) (hbm_h1 i) (hbm_q i) (by omega) (by omega)
            have hdeg_R := natDegree_resultant_le_wdegBi wY (W_F - (wY - 1) - W_g) W_q 4 2 h1 q
              (by omega) le_rfl (by omega) (by omega)
            have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ _ hRne _ hdvd).trans hdeg_R
            have hsub_ge : 4 * 2 * wY ≤ 2 * (W_F - (wY - 1) - W_g) + 4 * W_q := by
              have h1 : 4 * wY ≤ W_F - (wY - 1) - W_g := by
                have := hWh1_lo; rw [show d1 - dg = 4 by omega] at this; omega
              have h2 : 2 * (4 * wY) ≤ 2 * (W_F - (wY - 1) - W_g) := Nat.mul_le_mul_left 2 h1
              omega
            have hQ : ((∑ i : Idx, resOrdExact 4 (2 * k i - 1 - rr i) 2 (rq i) : ℕ) : ℚ) ≤
                ((2 * (W_F - (wY - 1) - W_g) + 4 * W_q - 4 * 2 * wY : ℕ) : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum, Nat.cast_sub hsub_ge, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
              Nat.cast_sub (by omega : W_g ≤ W_F - (wY - 1)), Nat.cast_sub (by omega : wY - 1 ≤ W_F),
              Nat.cast_sub (by omega : 1 ≤ wY), Nat.cast_mul, Nat.cast_one,
              show ((4 * 2 : ℕ) : ℚ) = 4 * 2 by norm_num,
              show ((2 : ℕ) : ℚ) = 2 by norm_num, show ((4 : ℕ) : ℚ) = 4 by norm_num] at hQ
            dsimp [cgVal, cqVal]
            have heq : (2 * ((W_F : ℚ) / (wY : ℚ) - 1 - (W_g : ℚ) / (wY : ℚ)) + 4 * ((W_q : ℚ) / (wY : ℚ)) - 8) * (wY : ℚ) + 2 =
                2 * ((W_F : ℚ) - ((wY : ℚ) - 1) - (W_g : ℚ)) + 4 * (W_q : ℚ) - 4 * 2 * (wY : ℚ) := by
              field_simp [hwYQ.ne']; ring
            linarith [hQ, heq]
          -- Shared helper for Res_Y(f0, sub) with sub ∈ {q, g1'}!
          have hrf0_sub : ∀ (sub : BiPoly Fld) (dSub W_sub : ℕ) (rSub : Idx → ℕ),
              sub ≠ 0 → sub.natDegree = dSub → sub.derivative = 0 → sub ∣ g → wdegBi wY sub = W_sub →
              (∀ i, rSub i ≤ biMult (BinaryIRSProfile.domain i) (y i) sub) →
              (∑ i : Idx, (t3_2BVrf0Sub dSub (k i) (rSub i) : ℚ)) ≤
                ((dSub : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 11) + 11 * ((W_sub : ℚ) / (wY : ℚ))) * (wY : ℚ) := by
            intro sub dSub W_sub rSub hsub_ne hsub_deg hsub_d hsub_dvd hWsub hrSub
            have hrel_s : IsRelPrime (f0.map ι) (sub.map ι) := fun p hp0 hps => by
              have hpg : p ∣ g.map ι := hps.trans (by rcases hsub_dvd with ⟨w, hw⟩; exact ⟨w.map ι, by rw [hw, Polynomial.map_mul]⟩)
              exact hcop_all p hp0 (hpg.trans ⟨h1.map ι, by rw [hf1_fac, Polynomial.map_mul]⟩)
                (hpg.trans ⟨h2.map ι, by rw [hf2_fac, Polynomial.map_mul]⟩)
            set R : Polynomial Fld := sub.leadingCoeff ^ (11 - d0) * Polynomial.resultant f0 sub d0 dSub
            have hRne : R ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hsub_ne))
              (by rw [← hsub_deg]; exact resultant_ne_zero_of_coprime_ratFunc f0 sub hf0_ne hsub_ne hrel_s)
            have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
                (X - C (BinaryIRSProfile.domain i)) ^ t3_2BVrf0Sub dSub (k i) (rSub i) ∣ R := by
              intro i _
              refine (pow_dvd_pow _ (t3_2BVrf0Sub_mono dSub (k i) (hrSub i))).trans ?_
              have hsub_ev : ∀ j, j % 2 = 1 → sub.coeff j = 0 := (deriv_eq_zero_iff_even_coeffs sub).mp hsub_d
              have ⟨hvk, hvp⟩ := kerD2_resY_f0_g_ord hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)
                sub hsub_ne hsub_ev
                (hsub_dvd.trans (by change g ∣ f1; rw [hf1_fac]; exact dvd_mul_right _ _))
                (hsub_dvd.trans (by change g ∣ f2; rw [hf2_fac]; exact dvd_mul_right _ _))
                11 (by change max d0 (max (d2 + 2) (d1 + 1)) ≤ 11; omega)
              rw [hsub_deg] at hvk hvp
              by_cases hk0 : k i = 0
              · simp [t3_2BVrf0Sub, hk0]
              · have hk0b : (k i == 0) = false := beq_false_of_ne hk0
                unfold t3_2BVrf0Sub; simp only [hk0b, Bool.false_eq_true, ↓reduceIte, resOrdWeighted2Fast_eq]
                rcases le_total (resOrdWeighted 11 (4 * k i + 4) (dSub / 2) (biMult (BinaryIRSProfile.domain i) (y i) sub) 2 - 2 * dSub)
                    (((List.range 12).map (fun d0' =>
                      resOrdExact d0' (2 * k i - 2) dSub (biMult (BinaryIRSProfile.domain i) (y i) sub) +
                        (11 - d0') * (biMult (BinaryIRSProfile.domain i) (y i) sub - dSub))).foldl Nat.min
                          (resOrdExact 0 (2 * k i - 2) dSub (biMult (BinaryIRSProfile.domain i) (y i) sub) +
                            11 * (biMult (BinaryIRSProfile.domain i) (y i) sub - dSub))) with hle | hle
                · rw [Nat.max_eq_right hle]
                  refine (pow_dvd_pow _ (foldl_map_min_le_mem _ (List.range 12) _ d0
                    (List.mem_range.mpr (by have : d0 ≤ dStar := le_max_left _ _; omega)))).trans hvp
                · rw [Nat.max_eq_left hle]; exact hvk
            have hWsub_lo : dSub * wY ≤ W_sub := by rw [← hWsub, ← hsub_deg]; exact hd_wdeg sub hsub_ne
            have hdeg_lc : sub.leadingCoeff.natDegree ≤ W_sub - dSub * wY := by
              have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hsub_ne)
              have hle := (wdegBi_le_iff wY W_sub sub).mp (le_of_eq hWsub) dSub _ (by rwa [← hsub_deg]); omega
            have hdeg_res := natDegree_resultant_le_wdegBi wY W_F W_sub d0 dSub f0 sub hWf0 (le_of_eq hWsub) le_rfl (le_of_eq hsub_deg)
            have hdeg_R : R.natDegree + dSub * 11 * wY ≤ dSub * W_F + 11 * W_sub := by
              have h1 : R.natDegree ≤ (11 - d0) * sub.leadingCoeff.natDegree + (Polynomial.resultant f0 sub d0 dSub).natDegree :=
                Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_pow_le _)
              have h2 : (11 - d0) * sub.leadingCoeff.natDegree ≤ (11 - d0) * (W_sub - dSub * wY) :=
                Nat.mul_le_mul_left _ hdeg_lc
              have hd0_le : d0 ≤ 11 := by have : d0 ≤ dStar := le_max_left _ _; omega
              have hmul_le : d0 * dSub * wY ≤ d0 * W_sub := by
                rw [mul_assoc]; exact Nat.mul_le_mul_left d0 hWsub_lo
              have hsub1 : (11 - d0) * (W_sub - dSub * wY) + (11 - d0) * (dSub * wY) = (11 - d0) * W_sub := by
                rw [← mul_add, Nat.sub_add_cancel hWsub_lo]
              have hsum_d : (11 - d0) * W_sub + d0 * W_sub = 11 * W_sub := by
                rw [← add_mul, Nat.sub_add_cancel hd0_le]
              have hsum_w : (11 - d0) * (dSub * wY) + d0 * dSub * wY = dSub * 11 * wY := by
                rw [mul_assoc d0, ← add_mul, Nat.sub_add_cancel hd0_le]; ring
              omega
            have hnat := sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ R hRne _ hdvd
            have htot : (∑ i : Idx, t3_2BVrf0Sub dSub (k i) (rSub i)) + dSub * 11 * wY ≤ dSub * W_F + 11 * W_sub := by omega
            have hQ : ((∑ i : Idx, t3_2BVrf0Sub dSub (k i) (rSub i) : ℕ) : ℚ) + (dSub : ℚ) * 11 * (wY : ℚ) ≤
                (dSub : ℚ) * (W_F : ℚ) + 11 * (W_sub : ℚ) := by
              have htotQ : (((∑ i : Idx, t3_2BVrf0Sub dSub (k i) (rSub i)) + dSub * 11 * wY : ℕ) : ℚ) ≤
                  ((dSub * W_F + 11 * W_sub : ℕ) : ℚ) := by exact_mod_cast htot
              rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
                show ((11 : ℕ) : ℚ) = 11 by norm_num] at htotQ
              exact htotQ
            rw [Nat.cast_sum] at hQ
            have heq : ((dSub : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 11) + 11 * ((W_sub : ℚ) / (wY : ℚ))) * (wY : ℚ) =
                (dSub : ℚ) * (W_F : ℚ) + 11 * (W_sub : ℚ) - (dSub : ℚ) * 11 * (wY : ℚ) := by
              field_simp [hwYQ.ne']; ring
            linarith [hQ, heq]
          have hrf0q := hrf0_sub q 2 W_q rq hq_ne hq_deg hq_d (by rw [hg_fac]; exact dvd_mul_right _ _) rfl
            (fun i => Nat.min_le_right _ _)
          have hrf0g1 : (∑ i : Idx, (t3_2BVrf0Sub 4 (k i) (rr i - rq i) : ℚ)) ≤
              (4 * ((W_F : ℚ) / (wY : ℚ) - 11) + 11 * (cgVal - cqVal)) * (wY : ℚ) := by
            have h1 := hrf0_sub g1' 4 W_g1' (fun i => rr i - rq i) hg1'_ne hg1'_deg hg1'_d
              (by rw [hg_fac]; exact dvd_mul_left _ _) rfl (fun i => by
                have hmul := biMult_mul (BinaryIRSProfile.domain i) (y i) hq_ne hg1'_ne
                rw [← hg_fac] at hmul; dsimp [rq, rr]; omega)
            have heq : cgVal - cqVal = (W_g1' : ℚ) / (wY : ℚ) := by
              dsimp [cgVal, cqVal]; rw [hWg_split, Nat.cast_add, add_div]; ring
            rwa [heq]
          have ⟨hm0, hsurp_fn⟩ := checkT3_2BCert_sound b hchk_b ((W_F : ℚ) / (wY : ℚ)) cgVal cqVal
            hb_lo hb_hi hcq_lo hcg_lo_2B hcg_hi1 Az hAz k rr rq hrr_le hrq_le
            hq_sum hg1'_sum hh1_sum hu_sum hlcq_sum hlcg1_sum hlch1_2B hrq_res
            (by simpa [cqVal] using hrf0q) hrf0g1
          have hmpos : 0 < b.m := Nat.pos_of_ne_zero hm0
          have ⟨hsurp, hcap⟩ := hsurp_fn hmpos
          have hms := List.all_eq_true.mp certsT3_2B_ms_bound b hb_mem
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
          have hpars : 2 ≤ b.s ∧ 0 < b.cHiDen ∧ 0 < b.δNum ∧ 0 < b.δDen := by
            unfold checkT3_2BCert at hchk_b
            have hmne : (b.m != 0) = true := bne_iff_ne.mpr hm0
            by_contra hbad; push Not at hbad
            have hfail : (b.cLoDen == 0 || b.cHiDen == 0) = true ∨
                (b.m != 0 && (b.s < 2 || b.vx == 0 || b.δNum == 0 || b.δDen == 0)) = true := by
              rcases lt_or_ge b.s 2 with hs | hs
              · exact Or.inr (by simp [hmne, hs])
              · rcases Nat.eq_zero_or_pos b.cHiDen with hd | hd
                · exact Or.inl (by simp [hd])
                · rcases Nat.eq_zero_or_pos b.δNum with hdn | hdn
                  · exact Or.inr (by simp [hmne, hdn])
                  · rcases Nat.eq_zero_or_pos b.δDen with hdd | hdd
                    · exact Or.inr (by simp [hmne, hdd])
                    · exfalso; have := hbad hs hd hdn; omega
            rcases hfail with hf | hf
            · simp [hf] at hchk_b
            · split_ifs at hchk_b <;> simp_all
          have hcap_bd : b.cap.c1Bkt * 3850 + b.cap.c0Bkt ≤ T3_CAP_BOUND := by
            unfold checkT3_2BEntry at hb_entry
            have hmne : (b.m == 0) = false := beq_false_of_ne hm0
            simp only [hmne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hb_entry
            exact hb_entry.2
          exact ⟨b.m, b.s, b.cHiNum, b.cHiDen, b.δNum, b.δDen, b.cap, hmpos, hms.1, hpars.1, hms.2,
            hpars.2.1, hpars.2.2.1, hpars.2.2.2, hb_hi, hsurp, hcap, hcap_bd⟩
        · -- Standard `mode = 0` certificate `cS`!
          refine hfinish_t3 cS hcS_mem (by omega) (by omega) (by omega) hcS_entry hS_lo hS_hi (by omega) (fun _ => ?_)
          dsimp only; rw [hS_m, hS_ds, hSg, ← hdg_6, ← hdStar_11]
          simp only [show (0 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hrf0_std 0 (Or.inl rfl)

end B6401PointSurplus
end ProximityPrize.SubmissionBinaryLower
