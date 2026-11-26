import ProximityPrize.SubmissionBinaryLower.Binary6402QuotBridge
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401KerD2
import ProximityPrize.SubmissionBinaryLower.Binary6402FarkasVerifier
import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid12
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402IntSmallCerts
import ProximityPrize.SubmissionBinaryLower.B6401T4Rows
import ProximityPrize.SubmissionBinaryLower.B6401T4Grid
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT1
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT2
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT3
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4a
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4b1
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4b2
import ProximityPrize.SubmissionBinaryLower.Binary6402SmallAlg
import ProximityPrize.SubmissionBinaryLower.B6401ResLineOrd
import ProximityPrize.SubmissionBinaryLower.Binary6402QuotBridge
import ProximityPrize.SubmissionBinaryLower.B6401ListAndMCA
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

/-!
# Exact Local Orders, Global Resultant Non-Vanishing, & Single-Point Surplus (`B6402PointSurplus`)

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
namespace B6402PointSurplus

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial  B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6402FarkasVerifier B6402HybridP64 B6402IntFarkas
open B6402IntSmallCerts B6401T4Rows B6401T4Grid
open B6402CertsT1 B6402CertsT2 B6402CertsT3 B6401CertsT4a B6401CertsT4b1 B6401CertsT4b2
open B6402SmallAlg B6401ResLineOrd B6402QuotBridge B6401ListAndMCA
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

/-! ### Part 0: Fast `decide` Side-Bounds on Certificate Tables -/

def linearSlopeCap : ℕ := 318940398363099
def linearConstantCap : ℕ := 24726797309604631
def linearPowerCap : ℕ := 700000000000000000

theorem certsT1_linear_caps :
    certsT1.all (fun c =>
      c.m ≤ 3000 && c.s ≤ 300 &&
      (c.m == 0 ||
        (c.cap1.c1Bkt ≤ linearSlopeCap && c.cap1.c0Bkt ≤ linearConstantCap &&
         (!c.hasCap2 || c.cap2.c1Bkt * 1811 + c.cap2.c0Bkt ≤ linearPowerCap)))) = true := by
  decide

theorem certsT2_ms_bound :
    certsT2.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide

theorem certsT3_2B_ms_bound :
    certsT3_2B.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide

theorem certsT3All_ms_bound :
    ∀ c ∈ certsT3All, c.m ≤ 3000 ∧ c.s ≤ 300 := by
  have h0 : B6402CertsT3Part0.certsT3_0.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h1 : B6402CertsT3Part1.certsT3_1.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h2 : B6402CertsT3Part2.certsT3_2.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h3 : B6402CertsT3Part3.certsT3_3.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h4 : B6402CertsT3Part4.certsT3_4.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h5 : B6402CertsT3Part5.certsT3_5.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h6 : B6402CertsT3Part6.certsT3_6.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h7 : B6402CertsT3Part7.certsT3_7.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h8 : B6402CertsT3Part8.certsT3_8.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
  have h9 : B6402CertsT3Part9.certsT3_9.all (fun c => c.m ≤ 3000 && c.s ≤ 300) = true := by decide
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

lemma char2_inv_w {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x0 y0 xv yv rv : R) :
    y0 + x0 * rv + (yv + y0 + (xv + x0) * rv) = yv + xv * rv := by
  linear_combination (y0 + x0 * rv) * h2

lemma char2_inv_t {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x0 xv : R) :
    x0 ^ 2 + (xv ^ 2 + x0 ^ 2) = xv ^ 2 := by
  linear_combination x0 ^ 2 * h2

lemma char2_inv_u {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x0 y0 xv yv rv : R) :
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

lemma foldl_min_le_foldl_min {α : Type*} (f g : α → ℕ) (l : List α)
    (hfg : ∀ x ∈ l, f x ≤ g x) (a b : ℕ) (hab : a ≤ b) :
    (l.map f).foldl Nat.min a ≤ (l.map g).foldl Nat.min b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (fun y hy => hfg y (List.mem_cons_of_mem _ hy)) _ _
        (min_le_min hab (hfg x List.mem_cons_self))

lemma foldl_min_le_mem {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) (x : α) (hx : x ∈ l) :
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

lemma foldl_map_min_le_mem {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) (x : α) (hx : x ∈ l) :
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

end B6402PointSurplus
end ProximityPrize.SubmissionBinaryLower
