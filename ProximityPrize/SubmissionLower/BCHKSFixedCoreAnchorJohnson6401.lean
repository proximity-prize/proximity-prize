import ProximityPrize.SubmissionLower.BCHKSCorrectionCurveAtlas6401
import ProximityPrize.SubmissionLower.BCHKSWeightedSecantAudit6400

/-!
# Fixed-core anchor--Johnson compiler at score 64.01

Suppose one correction component has a fixed identity core of size `g` and,
after deleting that core and dividing its locator, all secants from one
anchor are degree-at-most `d = k-1-g` polynomials around one fixed received
word.  A Cauchy anchor retains a positive fraction of the owners above a
chosen intersection threshold `b`; the ordinary fixed-word Johnson bound
then controls the number of distinct secants, while weak-curve failure caps
each secant fibre by `1182`.

At the benchmark row the first useful fixed-core size is exactly `126197`.
With the inclusive Johnson threshold `b = 25742`, the sharp anchor surplus is

`A^2 - N*(b-1) = 138922`.

The theorems below make the set-family anchor and final component compiler
unconditional.  The remaining geometric integration premise is that a
positive-dimensional rank-flat/clone component actually has one common
locator of this size and one fixed affine base after shortening.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFixedCoreAnchorJohnson6401

open scoped BigOperators
open Polynomial
open BCHKSFiveOwnerCorrectionGeometry6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSGlobalAffineResidualNormalSpace6401
open BCHKSResidualFlatBasisCount6401

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

section SetFamily

variable {Coord Owner : Type*} [DecidableEq Coord] [DecidableEq Owner]

/-- Number of owner supports containing one coordinate. -/
def familyLoad6401 (S : Finset Owner) (A : Owner → Finset Coord)
    (x : Coord) : Nat :=
  (S.filter fun z ↦ x ∈ A z).card

/-- Incidence swap for a support family contained in `U`. -/
theorem sum_familyLoad_eq_sum_card6401
    (U : Finset Coord) (S : Finset Owner) (A : Owner → Finset Coord)
    (hsub : ∀ z ∈ S, A z ⊆ U) :
    ∑ x ∈ U, familyLoad6401 S A x = ∑ z ∈ S, (A z).card := by
  classical
  calc
    ∑ x ∈ U, familyLoad6401 S A x =
        ∑ x ∈ U, ∑ z ∈ S, if x ∈ A z then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [familyLoad6401]
    _ = ∑ z ∈ S, ∑ x ∈ U, if x ∈ A z then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z ∈ S, (A z).card := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [← Finset.card_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact And.right
      · intro hx
        exact ⟨hsub z hz hx, hx⟩

/-- The ordered-pair intersection sum is the second moment of coordinate
loads. -/
theorem sum_intersections_eq_sum_load_sq6401
    (U : Finset Coord) (S : Finset Owner) (A : Owner → Finset Coord)
    (hsub : ∀ z ∈ S, A z ⊆ U) :
    ∑ r ∈ S, ∑ z ∈ S, ((A r ∩ A z).card : ℝ) =
      ∑ x ∈ U, (familyLoad6401 S A x : ℝ) ^ 2 := by
  classical
  calc
    ∑ r ∈ S, ∑ z ∈ S, ((A r ∩ A z).card : ℝ) =
        ∑ r ∈ S, ∑ z ∈ S, ∑ x ∈ U,
          if x ∈ A r ∩ A z then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro z hz
      have heq : U.filter (fun x ↦ x ∈ A r ∩ A z) = A r ∩ A z := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_inter]
        constructor
        · intro hx
          exact hx.2
        · intro hx
          exact ⟨hsub r hr hx.1, hx⟩
      symm
      simpa only [heq] using
        (Finset.sum_boole (R := ℝ) (fun x ↦ x ∈ A r ∩ A z) U)
    _ = ∑ r ∈ S, ∑ x ∈ U, ∑ z ∈ S,
          if x ∈ A r ∩ A z then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ = ∑ x ∈ U, ∑ r ∈ S, ∑ z ∈ S,
          if x ∈ A r ∩ A z then (1 : ℝ) else 0 := by
      exact Finset.sum_comm
    _ = ∑ x ∈ U, (familyLoad6401 S A x : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [familyLoad6401, Finset.mem_inter]
      rw [show ((S.filter fun z ↦ x ∈ A z).card : ℝ) =
          ∑ z ∈ S, if x ∈ A z then 1 else 0 by simp]
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hrx : x ∈ A r <;> by_cases hzx : x ∈ A z <;>
        simp [hrx, hzx]

/-- Cauchy chooses an anchor whose total overlap is at least the family
average `|S| * a^2 / |U|`.  This is division-free and works for supports of
cardinality at least `a`. -/
theorem exists_anchor_scaled_intersection6401
    (U : Finset Coord) (S : Finset Owner) (A : Owner → Finset Coord)
    (a : Nat) (hSne : S.Nonempty)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hcard : ∀ z ∈ S, a ≤ (A z).card) :
    ∃ r ∈ S,
      (S.card : ℝ) * a ^ 2 ≤
        U.card * ∑ z ∈ S, ((A r ∩ A z).card : ℝ) := by
  classical
  let load : Coord → ℝ := fun x ↦ familyLoad6401 S A x
  have hinc : (S.card : ℝ) * a ≤ ∑ x ∈ U, load x := by
    rw [show ∑ x ∈ U, load x = ∑ z ∈ S, ((A z).card : ℝ) by
      simpa only [load, Nat.cast_sum] using congrArg (fun m : Nat ↦ (m : ℝ))
        (sum_familyLoad_eq_sum_card6401 U S A hsub)]
    calc
      (S.card : ℝ) * a = ∑ _z ∈ S, (a : ℝ) := by simp
      _ ≤ ∑ z ∈ S, ((A z).card : ℝ) := by
        exact Finset.sum_le_sum fun z hz ↦ by exact_mod_cast hcard z hz
  have hcauchy : (∑ x ∈ U, load x) ^ 2 ≤
      U.card * ∑ x ∈ U, (load x) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := U) (f := load))
  have hnonneg : 0 ≤ (S.card : ℝ) * a := by positivity
  have hsquare : ((S.card : ℝ) * a) ^ 2 ≤
      U.card * ∑ x ∈ U, (load x) ^ 2 :=
    (pow_le_pow_left₀ hnonneg hinc 2).trans hcauchy
  have hpairs : ((S.card : ℝ) * a) ^ 2 ≤
      U.card * ∑ r ∈ S, ∑ z ∈ S,
        ((A r ∩ A z).card : ℝ) := by
    rw [sum_intersections_eq_sum_load_sq6401 U S A hsub]
    exact hsquare
  have hscaled : ∑ r ∈ S, ((S.card : ℝ) * a ^ 2) ≤
      ∑ r ∈ S,
        (U.card * ∑ z ∈ S, ((A r ∩ A z).card : ℝ)) := by
    convert hpairs using 1 <;>
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum] <;> ring
  exact Finset.exists_le_of_sum_le hSne hscaled

end SetFamily

section Retention

variable {Coord Owner : Type*} [DecidableEq Coord] [DecidableEq Owner]

/-- Owners retained above overlap threshold `b` with one anchor. -/
def anchorRichOwners6401 (S : Finset Owner) (A : Owner → Finset Coord)
    (r : Owner) (b : Nat) : Finset Owner :=
  S.filter fun z ↦ b ≤ (A r ∩ A z).card

/-- The exact anchor-retention inequality

`|S|(a^2-N(b-1)) <= N |H| (a-b+1)`.

The supports are trimmed to exact cardinality `a`, which is harmless before
the anchor step and makes `a` a uniform upper bound on every intersection. -/
theorem anchorRichOwners_retention6401
    (U : Finset Coord) (S : Finset Owner) (A : Owner → Finset Coord)
    (r : Owner) (a b : Nat)
    (hr : r ∈ S) (hsub : ∀ z ∈ S, A z ⊆ U)
    (hcard : ∀ z ∈ S, (A z).card = a)
    (hanchor : (S.card : ℝ) * a ^ 2 ≤
      U.card * ∑ z ∈ S, ((A r ∩ A z).card : ℝ))
    (hbpos : 0 < b) (hba : b ≤ a) :
    (S.card : ℝ) * (a ^ 2 - U.card * (b - 1)) ≤
      U.card * (anchorRichOwners6401 S A r b).card * (a - b + 1) := by
  classical
  let H := anchorRichOwners6401 S A r b
  have hbcast : (((b - 1 : Nat) : ℝ)) = (b : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hbpos))]
    norm_num
  have hinter : ∀ z ∈ S,
      ((A r ∩ A z).card : ℝ) ≤
        if z ∈ H then (a : ℝ) else ((b - 1 : Nat) : ℝ) := by
    intro z hz
    by_cases hzH : z ∈ H
    · simp only [hzH, if_true]
      exact_mod_cast (Finset.card_le_card Finset.inter_subset_left).trans_eq
        (hcard r hr)
    · simp only [hzH, if_false]
      have hnot : ¬ b ≤ (A r ∩ A z).card := by
        intro hle
        exact hzH (Finset.mem_filter.mpr ⟨hz, hle⟩)
      have hlt : (A r ∩ A z).card < b := Nat.lt_of_not_ge hnot
      exact_mod_cast Nat.le_sub_one_of_lt hlt
  have hsum : ∑ z ∈ S, ((A r ∩ A z).card : ℝ) ≤
      (H.card : ℝ) * a +
        (S.card - H.card : Nat) * ((b : ℝ) - 1) := by
    calc
      _ ≤ ∑ z ∈ S, if z ∈ H then (a : ℝ) else ((b - 1 : Nat) : ℝ) :=
        Finset.sum_le_sum hinter
      _ = (H.card : ℝ) * a +
          (S.card - H.card : Nat) * (b - 1) := by
        have hHsub : H ⊆ S := fun z hz ↦ (Finset.mem_filter.mp hz).1
        rw [Finset.sum_ite]
        have hyes : S.filter (fun z ↦ z ∈ H) = H := by
          ext z
          simp only [Finset.mem_filter]
          constructor
          · exact And.right
          · intro hz
            exact ⟨hHsub hz, hz⟩
        have hno : S.filter (fun z ↦ ¬z ∈ H) = S \ H := by
          ext z
          simp
        rw [hyes, hno]
        simp [Finset.card_sdiff_of_subset hHsub, hbcast]
        ring
  have hHsub : H.card ≤ S.card := Finset.card_le_card fun z hz ↦
    (Finset.mem_filter.mp hz).1
  have hcastsub : ((S.card - H.card : Nat) : ℝ) =
      (S.card : ℝ) - H.card := by
    rw [Nat.cast_sub hHsub]
  rw [hcastsub] at hsum
  change (S.card : ℝ) * (a ^ 2 - U.card * ((b : ℝ) - 1)) ≤
    U.card * (H.card : ℝ) * ((a : ℝ) - b + 1)
  nlinarith

end Retention

section FixedCardJohnson

variable {Coord Owner : Type*} [DecidableEq Coord] [DecidableEq Owner]

/-- Ordinary fixed-word Johnson, in the exact form used after shortening.
Every agreement set is first trimmed to exactly `b` points.  Distinct words
then have pair intersection at most `d`. -/
theorem fixedCardJohnson_scalar6401
    (U : Finset Coord) (T : Finset Owner) (B : Owner → Finset Coord)
    (b d : Nat) (hTne : T.Nonempty)
    (hsub : ∀ z ∈ T, B z ⊆ U)
    (hcard : ∀ z ∈ T, (B z).card = b)
    (hpair : ∀ r ∈ T, ∀ z ∈ T, r ≠ z →
      (B r ∩ B z).card ≤ d) :
    (T.card : ℝ) * (b ^ 2 - U.card * d) ≤ U.card * (b - d) := by
  classical
  let L : ℝ := T.card
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Finset.card_pos.mpr hTne
  have hloadsum :
      ∑ x ∈ U, (familyLoad6401 T B x : ℝ) = L * b := by
    calc
      ∑ x ∈ U, (familyLoad6401 T B x : ℝ) =
          ∑ z ∈ T, ((B z).card : ℝ) := by
        simpa only [Nat.cast_sum] using congrArg (fun m : Nat ↦ (m : ℝ))
          (sum_familyLoad_eq_sum_card6401 U T B hsub)
      _ = ∑ _z ∈ T, (b : ℝ) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact_mod_cast hcard z hz
      _ = L * b := by
        simp [L]
  have hrow : ∀ r ∈ T,
      ∑ z ∈ T, ((B r ∩ B z).card : ℝ) ≤
        b + (L - 1) * d := by
    intro r hr
    have hsplit : ∑ z ∈ T, ((B r ∩ B z).card : ℝ) =
        ((B r ∩ B r).card : ℝ) +
          ∑ z ∈ T.erase r, ((B r ∩ B z).card : ℝ) :=
      (Finset.add_sum_erase T
        (fun z ↦ ((B r ∩ B z).card : ℝ)) hr).symm
    have herase : ∑ z ∈ T.erase r, ((B r ∩ B z).card : ℝ) ≤
        (L - 1) * d := by
      have heach : ∀ z ∈ T.erase r,
          ((B r ∩ B z).card : ℝ) ≤ d := by
        intro z hz
        exact_mod_cast hpair r hr z (Finset.mem_of_mem_erase hz)
          (Ne.symm (Finset.ne_of_mem_erase hz))
      have hcarderase : ((T.erase r).card : ℝ) = L - 1 := by
        rw [Finset.card_erase_of_mem hr]
        have hpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨r, hr⟩
        rw [Nat.cast_sub hpos]
        simp [L]
      calc
        _ ≤ ∑ _z ∈ T.erase r, (d : ℝ) := Finset.sum_le_sum heach
        _ = (L - 1) * d := by
          rw [Finset.sum_const, nsmul_eq_mul, hcarderase]
    calc
      _ = ((B r ∩ B r).card : ℝ) +
          ∑ z ∈ T.erase r, ((B r ∩ B z).card : ℝ) := hsplit
      _ ≤ ((B r ∩ B r).card : ℝ) + (L - 1) * d :=
        add_le_add_right herase _
      _ = b + (L - 1) * d := by simp [hcard r hr]
  have hpairs :
      ∑ r ∈ T, ∑ z ∈ T, ((B r ∩ B z).card : ℝ) ≤
        L * b + L * (L - 1) * d := by
    calc
      _ ≤ ∑ _r ∈ T, ((b : ℝ) + (L - 1) * d) :=
        Finset.sum_le_sum hrow
      _ = L * b + L * (L - 1) * d := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [L]
        ring
  have hcauchyLoad :
      (∑ x ∈ U, (familyLoad6401 T B x : ℝ)) ^ 2 ≤
        U.card * ∑ x ∈ U, (familyLoad6401 T B x : ℝ) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := U) (f := fun x ↦ (familyLoad6401 T B x : ℝ)))
  have hcauchyPairs :
      (L * b) ^ 2 ≤ U.card *
        ∑ r ∈ T, ∑ z ∈ T, ((B r ∩ B z).card : ℝ) := by
    rw [← hloadsum]
    rw [sum_intersections_eq_sum_load_sq6401 U T B hsub]
    exact hcauchyLoad
  have hcauchy :
      (L * b) ^ 2 ≤
        U.card * (L * b + L * (L - 1) * d) :=
    hcauchyPairs.trans (mul_le_mul_of_nonneg_left hpairs (by positivity))
  simpa [L] using
    (BCHKSWeightedSecantAudit6400.weightedJohnson_scalar
      L U.card b d hLpos hcauchy)

end FixedCardJohnson

section CommonAffineChart

variable {F I : Type*} [Field F] [DecidableEq I]

/-- A shared prefix does not need to consist of received-agreement
coordinates common to every owner.  If all owner residuals vanish on the
prefix, then they vanish on its whole evaluation-normal flat.  Consequently
all owner polynomials restrict there to the same affine chart
`p0 + z*p1`. -/
theorem commonAffineChart_on_normalFlat6401
    (alpha : I → F) (W : Submodule F F[X])
    (Uset : Finset I) (S : Finset F)
    (P : F → F[X]) (p0 p1 : F[X])
    {ell : Nat} (f : Fin ell → I)
    (hmem : ∀ z ∈ S, globalAffineResidual6401 P p0 p1 z ∈ W)
    (hprefix : ∀ z ∈ S, ∀ j,
      (globalAffineResidual6401 P p0 p1 z).eval (alpha (f j)) = 0) :
    ∀ z ∈ S, ∀ i ∈ normalSpanFlat (F := F) Uset
        (residualEvalNormal6401 alpha W) f,
      (P z).eval (alpha i) = p0.eval (alpha i) + z * p1.eval (alpha i) := by
  classical
  intro z hz i hi
  let Q : W := ⟨globalAffineResidual6401 P p0 p1 z, hmem z hz⟩
  let Phi : Submodule F (Module.Dual F W) :=
    Submodule.span F
      (Set.range (residualEvalNormal6401 alpha W ∘ f))
  have hQprefix : ∀ j,
      residualEvalNormal6401 alpha W (f j) Q = 0 := by
    intro j
    exact hprefix z hz j
  have hannihilate : ∀ L : Module.Dual F W, L ∈ Phi → L Q = 0 := by
    intro L hL
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hL
    · rintro L ⟨j, rfl⟩
      exact hQprefix j
    · exact LinearMap.zero_apply _
    · intro L M _hL _hM hLzero hMzero
      simp [hLzero, hMzero]
    · intro c L _hL hLzero
      simp [hLzero]
  have hiPhi : residualEvalNormal6401 alpha W i ∈ Phi := by
    simpa [Phi, normalSpanFlat] using (Finset.mem_filter.mp hi).2
  have hiZero : (globalAffineResidual6401 P p0 p1 z).eval (alpha i) = 0 := by
    exact hannihilate (residualEvalNormal6401 alpha W i) hiPhi
  simpa only [globalAffineResidual6401, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    sub_eq_zero] using hiZero

/-- Deleting a common chart of size `g` leaves every owner with at least
`a-g` agreement coordinates.  This is the exact set-theoretic shortening
interface used before the anchor argument. -/
theorem ownerResidual_card_ge_after_delete_chart6401
    (A B : Finset I) (a g : Nat)
    (hA : a ≤ A.card) (hB : B.card ≤ g) :
    a - g ≤ (A \ B).card := by
  have hinter : (B ∩ A).card ≤ g :=
    (Finset.card_le_card Finset.inter_subset_left).trans hB
  rw [Finset.card_sdiff]
  omega

/-- The generalized-weight equality case supplies the required chart size.
The equality/minimal-support premise is essential: the RS generalized-weight
bound by itself points in the opposite direction and only upper-bounds a
common zero set. -/
theorem extremalRankFlat_core_card_ge_126197_6401
    (g q : Nat)
    (hequality : g + q = ownerDegreeCap6401 + 1)
    (hq : q ≤ 4875) :
    126197 ≤ g := by
  norm_num [ownerDegreeCap6401] at hequality ⊢
  omega

end CommonAffineChart

section SecantFibres

/-- Nonanchor owners carried by one fixed anchored secant. -/
noncomputable def anchoredSecantOwners6401
    {F : Type*} [Field F] [DecidableEq F]
    (S : Finset F) (P : F → F[X]) (r : F) (Q : F[X]) : Finset F :=
  S.filter fun z ↦ z ≠ r ∧
    P z = P r + Polynomial.C (z - r) * Q

/-- Under weak-curve failure, one anchored secant carries at most `1181`
nonanchor owners.  The off-by-one is load-bearing: `1182` equal secants plus
the anchor itself produce the required `1183` affine owners. -/
theorem anchoredSecantOwners_card_le_1181_6401
    {F : Type*} [Field F] [DecidableEq F]
    (S : Finset F) (P : F → F[X]) (r : F) (Q : F[X])
    (hr : r ∈ S)
    (hPr : (P r).natDegree ≤ ownerDegreeCap6401)
    (hQ : Q.natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    (anchoredSecantOwners6401 S P r Q).card ≤ 1181 := by
  classical
  by_contra hnot
  let T := anchoredSecantOwners6401 S P r Q
  have hTcard : 1182 ≤ T.card := by
    dsimp [T]
    omega
  apply hfail
  let p0 : F[X] := P r - Polynomial.C r * Q
  have hp0 : p0.natDegree ≤ ownerDegreeCap6401 := by
    dsimp [p0]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hPr ((Polynomial.natDegree_C_mul_le r Q).trans hQ))
  have hrnot : r ∉ T := by
    simp [T, anchoredSecantOwners6401]
  refine ⟨p0, Q, hp0, hQ, insert r T, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hr
    · exact (Finset.mem_filter.mp hz).1
  · rw [Finset.card_insert_of_notMem hrnot]
    have hout : weakCurveOutput6401 = 1183 := by native_decide
    rw [hout]
    omega
  · intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · dsimp [p0]
      ring
    · have heq := (Finset.mem_filter.mp hz).2.2
      dsimp [p0]
      rw [heq, map_sub]
      ring

/-- If fewer than `L` secant labels occur and every label fibre has size at
most `1181`, then the rich set, including its anchor, has size at most
`1181*L+1`. -/
theorem richOwners_card_le_of_secantFibres6401
    {Owner Label : Type*} [DecidableEq Owner] [DecidableEq Label]
    (H : Finset Owner) (r : Owner) (label : Owner → Label) (L : Nat)
    (hr : r ∈ H)
    (hlabels : ((H.erase r).image label).card < L)
    (hfibre : ∀ q ∈ (H.erase r).image label,
      ((H.erase r).filter fun z ↦ label z = q).card ≤ 1181) :
    H.card ≤ 1181 * L + 1 := by
  classical
  let E := H.erase r
  let Q := E.image label
  have hmaps : ∀ z ∈ E, label z ∈ Q := by
    intro z hz
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hcount : ∑ q ∈ Q,
      ((E.filter fun z ↦ label z = q).card) = E.card := by
    convert (Finset.sum_fiberwise_of_maps_to hmaps
      (fun _z ↦ (1 : Nat))) using 1 <;> simp
  have hEcap : E.card ≤ Q.card * 1181 := by
    rw [← hcount]
    calc
      _ ≤ ∑ _q ∈ Q, 1181 := by
        apply Finset.sum_le_sum
        intro q hq
        exact hfibre q hq
      _ = Q.card * 1181 := by simp
  have hQcard : Q.card ≤ L := Nat.le_of_lt (by simpa [Q, E] using hlabels)
  have hErase : E.card + 1 = H.card := by
    simpa [E] using Finset.card_erase_add_one hr
  omega

end SecantFibres

/-! ## Exact score-6401 fixed-core parameters -/

def fixedCoreAnchorThreshold6401 : Nat := 126197
def shortenedDomainAtThreshold6401 : Nat := n6401 - fixedCoreAnchorThreshold6401
def shortenedDegreeAtThreshold6401 : Nat :=
  ownerDegreeCap6401 - fixedCoreAnchorThreshold6401
def shortenedAgreementAtThreshold6401 : Nat :=
  a6401 - fixedCoreAnchorThreshold6401
def anchorJohnsonAgreement6401 : Nat := 25742
def anchorJohnsonListCap6401 : Nat := 63203
def anchorJohnsonContradictionSize6401 : Nat := 63204

theorem fixedCoreAnchor_parameters_exact6401 :
    shortenedDomainAtThreshold6401 = 135947 ∧
      shortenedDegreeAtThreshold6401 = 4874 ∧
      shortenedAgreementAtThreshold6401 = 59157 ∧
      Nat.sqrt (shortenedDomainAtThreshold6401 *
        shortenedDegreeAtThreshold6401) = 25741 ∧
      anchorJohnsonAgreement6401 =
        Nat.sqrt (shortenedDomainAtThreshold6401 *
          shortenedDegreeAtThreshold6401) + 1 ∧
      anchorJohnsonAgreement6401 ^ 2 -
        shortenedDomainAtThreshold6401 *
          shortenedDegreeAtThreshold6401 = 44886 ∧
      shortenedDomainAtThreshold6401 *
          (anchorJohnsonAgreement6401 - shortenedDegreeAtThreshold6401) =
        2836941996 ∧
      shortenedAgreementAtThreshold6401 ^ 2 -
        shortenedDomainAtThreshold6401 *
          (anchorJohnsonAgreement6401 - 1) = 138922 ∧
      shortenedDomainAtThreshold6401 *
          (shortenedAgreementAtThreshold6401 -
            anchorJohnsonAgreement6401 + 1) = 4542804952 ∧
      shortenedDomainAtThreshold6401 *
          (anchorJohnsonAgreement6401 - shortenedDegreeAtThreshold6401) /
        (anchorJohnsonAgreement6401 ^ 2 -
          shortenedDomainAtThreshold6401 *
            shortenedDegreeAtThreshold6401) = anchorJohnsonListCap6401 ∧
      anchorJohnsonContradictionSize6401 = anchorJohnsonListCap6401 + 1 := by
  native_decide

/-- At the shortened benchmark parameters, `63204` distinct secants are
impossible.  Equivalently, the fixed-word list has cardinality at most
`63203`.  The proof invokes the formal set-family Johnson inequality rather
than only checking the displayed quotient. -/
theorem shortenedFixedWordJohnson_card_lt_63204_6401
    {Coord Owner : Type*} [DecidableEq Coord] [DecidableEq Owner]
    (U : Finset Coord) (T : Finset Owner) (B : Owner → Finset Coord)
    (hUcard : U.card = shortenedDomainAtThreshold6401)
    (hsub : ∀ z ∈ T, B z ⊆ U)
    (hcard : ∀ z ∈ T, (B z).card = anchorJohnsonAgreement6401)
    (hpair : ∀ r ∈ T, ∀ z ∈ T, r ≠ z →
      (B r ∩ B z).card ≤ shortenedDegreeAtThreshold6401) :
    T.card < anchorJohnsonContradictionSize6401 := by
  classical
  by_cases hT : T.Nonempty
  · have hJ := fixedCardJohnson_scalar6401 U T B
      anchorJohnsonAgreement6401 shortenedDegreeAtThreshold6401
      hT hsub hcard hpair
    rw [hUcard] at hJ
    by_contra hnot
    have hlarge : anchorJohnsonContradictionSize6401 ≤ T.card :=
      Nat.le_of_not_gt hnot
    norm_num [anchorJohnsonContradictionSize6401,
      anchorJohnsonAgreement6401, shortenedDomainAtThreshold6401,
      shortenedDegreeAtThreshold6401, fixedCoreAnchorThreshold6401,
      n6401, ownerDegreeCap6401] at hJ
    have hlargeR : (63204 : ℝ) ≤ (T.card : ℝ) := by
      exact_mod_cast hlarge
    have hscaled := mul_le_mul_of_nonneg_right hlargeR
      (show (0 : ℝ) ≤ 44886 by norm_num)
    norm_num at hscaled
    linarith
  · simp only [Finset.not_nonempty_iff_eq_empty] at hT
    simp [hT, anchorJohnsonContradictionSize6401]

/-- The preceding core size is the first one for which the anchor numerator
is positive at the integer Johnson threshold. -/
theorem fixedCoreAnchor_first_positive_exact6401 :
    (a6401 - (fixedCoreAnchorThreshold6401 - 1)) ^ 2 ≤
        (n6401 - (fixedCoreAnchorThreshold6401 - 1)) *
          Nat.sqrt
            ((n6401 - (fixedCoreAnchorThreshold6401 - 1)) *
              (ownerDegreeCap6401 -
                (fixedCoreAnchorThreshold6401 - 1))) ∧
      (n6401 - fixedCoreAnchorThreshold6401) *
          Nat.sqrt
            ((n6401 - fixedCoreAnchorThreshold6401) *
              (ownerDegreeCap6401 - fixedCoreAnchorThreshold6401)) <
        (a6401 - fixedCoreAnchorThreshold6401) ^ 2 := by
  native_decide

/-- Exact owner capacities in the fixed-core compiler.  The anchor step
retains at least `8366600768326` owners from the retained high-mass family.
The Johnson contradiction size is `63204`; using the conservative cap of
`1181*63204+1` rich owners bounds the whole component by
`2440886196043`, far below the retained owner mass. -/
theorem fixedCoreAnchor_owner_capacity_exact6401 :
    BCHKSMultiPinRankAccumulation6401.multiPinOwnerMass6401 * 138922 /
        4542804952 = 8366600768326 ∧
      1181 * anchorJohnsonContradictionSize6401 + 1 = 74643925 ∧
      shortenedDomainAtThreshold6401 *
          (shortenedAgreementAtThreshold6401 -
            anchorJohnsonAgreement6401 + 1) *
          (1181 * anchorJohnsonContradictionSize6401 + 1) =
        339092792126716600 ∧
      339092792126716600 / 138922 = 2440886196043 ∧
      339092792126716600 <
        BCHKSMultiPinRankAccumulation6401.multiPinOwnerMass6401 * 138922 := by
  native_decide

/-- Abstract division-free endpoint for one fixed-core component.  Once the
anchor-rich set has at most `1181*L+1` owners (the extra one is the anchor),
the component has the displayed cap.  The fixed-word Johnson/secant layer is
responsible only for supplying `hRich`; all Cauchy and retention accounting
is internal. -/
theorem fixedCoreComponent_card_mul_surplus_le6401
    {Coord Owner : Type*} [DecidableEq Coord] [DecidableEq Owner]
    (U : Finset Coord) (S : Finset Owner) (A : Owner → Finset Coord)
    (r : Owner) (a b listThreshold : Nat)
    (hr : r ∈ S) (hsub : ∀ z ∈ S, A z ⊆ U)
    (hcard : ∀ z ∈ S, (A z).card = a)
    (hanchor : (S.card : ℝ) * a ^ 2 ≤
      U.card * ∑ z ∈ S, ((A r ∩ A z).card : ℝ))
    (hbpos : 0 < b) (hba : b ≤ a)
    (hRich : (anchorRichOwners6401 S A r b).card ≤
      1181 * listThreshold + 1) :
    (S.card : ℝ) * (a ^ 2 - U.card * (b - 1)) ≤
      U.card * (1181 * listThreshold + 1) * (a - b + 1) := by
  have hret := anchorRichOwners_retention6401
    U S A r a b hr hsub hcard hanchor hbpos hba
  have hnonnegU : (0 : ℝ) ≤ U.card := by positivity
  have hnonnegGap : (0 : ℝ) ≤ (a : ℝ) - b + 1 := by
    have hab : (b : ℝ) ≤ a := by exact_mod_cast hba
    linarith
  calc
    (S.card : ℝ) * (a ^ 2 - U.card * ((b : ℝ) - 1)) ≤
        (U.card : ℝ) * (anchorRichOwners6401 S A r b).card *
          ((a : ℝ) - b + 1) := hret
    _ ≤ (U.card : ℝ) * (1181 * listThreshold + 1) *
          ((a : ℝ) - b + 1) := by
      gcongr
      exact_mod_cast hRich

end BCHKSFixedCoreAnchorJohnson6401
end ProximityPrize.SubmissionLower
