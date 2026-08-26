import ProximityPrize.SubmissionLower.BCHKSNonproperAugmentedResidualAudit6401
import ProximityPrize.SubmissionLower.BCHKSLinearSelectedCore

/-!
# A degree-four correction-curve atlas at score 64.01

This file isolates the exact local-to-global statement available in the
nonproper augmented-determinant branch.

* Two coordinatewise polynomial correction curves of challenge degree at
  most four which contain the same five challenge-owner points are equal.
* Four common points are not enough.  A concrete example over `ZMod 7`
  gives arbitrarily different scalar multiples of one split quartic through
  the same four points.
* Consequently, an atlas with a fixed five-point hub globalizes to one
  correction curve.
* A nonaffine global correction curve whose identity-coordinate set has RS
  size at most `k - 1` contains at most nine rich owners.  The tenth owner
  misses by exactly `18538` root incidences.

The five-point overlap premise is genuinely load-bearing.  Mere connectedness
of an atlas under four-point overlaps cannot route its local curves to one
global curve, as the finite-field example shows.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSCorrectionCurveAtlas6401

open Polynomial
open BCHKSFiveOwnerCorrectionGeometry6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSResidualFlatBasisCount6401
open BCHKSGlobalAffineResidualNormalSpace6401

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

/-! ## Five common challenge-owner points force equality -/

/-- The common challenge set of two coordinatewise polynomial curves. -/
def commonCorrectionChallenges6401
    {F Coord : Type*} [Field F] [DecidableEq F]
    [Fintype Coord] [DecidableEq Coord]
    (S : Finset F) (C D : Coord → F[X]) : Finset F :=
  S.filter fun z ↦ ∀ i, Polynomial.eval z (C i) = Polynomial.eval z (D i)

/-- Distinct coordinatewise degree-four correction curves have at most four
common challenge-owner points.  One differing coordinate polynomial is a
degree-at-most-four obstruction for the whole common set. -/
theorem distinctCorrectionCurves_common_card_le_four6401
    {F Coord : Type*} [Field F] [DecidableEq F]
    [Fintype Coord] [DecidableEq Coord]
    (S : Finset F) (C D : Coord → F[X])
    (hCdegree : ∀ i, (C i).natDegree ≤ correctionSlopeDegree6401)
    (hDdegree : ∀ i, (D i).natDegree ≤ correctionSlopeDegree6401)
    (hne : C ≠ D) :
    (commonCorrectionChallenges6401 S C D).card ≤
      correctionSlopeDegree6401 := by
  classical
  have hcoord : ∃ i, C i ≠ D i := by
    by_contra hnot
    apply hne
    funext i
    by_contra hi
    exact hnot ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hcoord
  let Q : F[X] := C i - D i
  have hQne : Q ≠ 0 := by
    simpa [Q, sub_eq_zero] using hi
  have hQdegree : Q.natDegree ≤ correctionSlopeDegree6401 := by
    exact (Polynomial.natDegree_sub_le (C i) (D i)).trans
      (max_le (hCdegree i) (hDdegree i))
  have hsub : commonCorrectionChallenges6401 S C D ⊆ Q.roots.toFinset := by
    intro z hz
    have hzcommon := (Finset.mem_filter.mp hz).2 i
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hQne).2
    simpa [Q, Polynomial.eval_sub] using sub_eq_zero.mpr hzcommon
  calc
    (commonCorrectionChallenges6401 S C D).card ≤
        Q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Q.roots.card := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' Q
    _ ≤ correctionSlopeDegree6401 := hQdegree

/-- Five common challenge-owner points are the exact interpolation threshold
for coordinatewise degree-four correction curves. -/
theorem correctionCurves_eq_of_five_common_owner_points6401
    {F Coord : Type*} [Field F] [DecidableEq F]
    [Fintype Coord] [DecidableEq Coord]
    (T : Finset F) (C D : Coord → F[X])
    (hTcard : correctionSlopeDegree6401 < T.card)
    (hCdegree : ∀ i, (C i).natDegree ≤ correctionSlopeDegree6401)
    (hDdegree : ∀ i, (D i).natDegree ≤ correctionSlopeDegree6401)
    (hcommon : ∀ z ∈ T, ∀ i,
      Polynomial.eval z (C i) = Polynomial.eval z (D i)) :
    C = D := by
  classical
  by_contra hne
  have hsub : T ⊆ commonCorrectionChallenges6401 T C D := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨hz, hcommon z hz⟩
  have hle := distinctCorrectionCurves_common_card_le_four6401
    T C D hCdegree hDdegree hne
  have hcard := Finset.card_le_card hsub
  omega

/-! ## A five-point hub globalizes an atlas -/

/-- If every local chart through an owner also passes through one fixed
five-point hub, all local charts equal the hub chart.  This is a compact
local-to-global interface for a correction-component routing theorem: the
remaining combinatorial task is precisely to produce the common hub. -/
theorem correctionAtlas_globalizes_from_fivePointHub6401
    {F Coord : Type*} [Field F] [DecidableEq F]
    [Fintype Coord] [DecidableEq Coord]
    (S Hub : Finset F) (owner : F → Coord → F)
    (C₀ : Coord → F[X])
    (hHubcard : correctionSlopeDegree6401 < Hub.card)
    (hC₀degree : ∀ i, (C₀ i).natDegree ≤ correctionSlopeDegree6401)
    (hC₀fit : ∀ z ∈ Hub, ∀ i,
      Polynomial.eval z (C₀ i) = owner z i)
    (hloc : ∀ z ∈ S, ∃ C : Coord → F[X],
      (∀ i, (C i).natDegree ≤ correctionSlopeDegree6401) ∧
      (∀ w ∈ insert z Hub, ∀ i,
        Polynomial.eval w (C i) = owner w i)) :
    ∀ z ∈ S, ∀ i, Polynomial.eval z (C₀ i) = owner z i := by
  classical
  intro z hz i
  obtain ⟨C, hCdegree, hCfit⟩ := hloc z hz
  have hCC₀ : C = C₀ := by
    apply correctionCurves_eq_of_five_common_owner_points6401
      Hub C C₀ hHubcard hCdegree hC₀degree
    intro w hw j
    rw [hCfit w (Finset.mem_insert_of_mem hw) j, hC₀fit w hw j]
  rw [← hCC₀]
  exact hCfit z (Finset.mem_insert_self z Hub) i

/-! ## Four-point overlap is sharply insufficient, already over `F_7` -/

/-- The split quartic with roots `0,1,2,3` over `F_7`. -/
noncomputable def fourPointVanishingQuartic6401 : (ZMod 7)[X] :=
  (Polynomial.X : (ZMod 7)[X]) *
      ((Polynomial.X : (ZMod 7)[X]) - Polynomial.C (1 : ZMod 7)) *
    ((Polynomial.X : (ZMod 7)[X]) - Polynomial.C (2 : ZMod 7)) *
      ((Polynomial.X : (ZMod 7)[X]) - Polynomial.C (3 : ZMod 7))

/-- A one-parameter atlas of mutually different quartics through the same
four challenge-owner points. -/
noncomputable def fourPointAtlasMember6401 (a : ZMod 7) : (ZMod 7)[X] :=
  Polynomial.C a * fourPointVanishingQuartic6401

/-- Four common points cannot replace the five-point hub premise.  The two
displayed curves agree at `0,1,2,3` but differ at `4`. -/
theorem fourPointOverlap_counterexample_F7_6401 :
    (∀ z ∈ ({0, 1, 2, 3} : Finset (ZMod 7)),
      Polynomial.eval z (fourPointAtlasMember6401 1) =
        Polynomial.eval z (fourPointAtlasMember6401 2)) ∧
    fourPointAtlasMember6401 1 ≠ fourPointAtlasMember6401 2 := by
  constructor
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      norm_num [fourPointAtlasMember6401, fourPointVanishingQuartic6401]
  · intro h
    have h4 := congrArg (Polynomial.eval (4 : ZMod 7)) h
    norm_num [fourPointAtlasMember6401, fourPointVanishingQuartic6401] at h4
    exact (by native_decide : (24 : ZMod 7) ≠ 48) h4

/-! ## One nonaffine global clone curve carries at most nine owners -/

/-- Root-incidence form of the exact clone-curve multiplicity bound.  The
fixed coordinates are those on which the curve agrees identically.  If that
identity set has at most the RS root cap `k-1`, ten rich owners would require
`542830` outside roots while degree four supplies only `524292`. -/
theorem nonaffineDegreeFourCorrectionCurve_ownerCard_le_nine6401
    {F Coord : Type} [Field F] [DecidableEq F]
    [Fintype Coord] [DecidableEq Coord]
    (S : Finset F) (A : F → Finset Coord) (G : Coord → F[X])
    (hCoord : Fintype.card Coord = n6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hroot : ∀ z ∈ S, ∀ i ∈ A z, Polynomial.eval z (G i) = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ correctionSlopeDegree6401)
    (hfixed : (fixedLocatorCoordinates G).card ≤ ownerDegreeCap6401) :
    S.card ≤ 9 := by
  have hinc := locator_root_incidence S A G a6401
    correctionSlopeDegree6401 hrow hroot hdegree
  rw [hCoord] at hinc
  by_contra hnot
  have hten : 10 ≤ S.card := by omega
  have hlower :
      10 * (a6401 - (fixedLocatorCoordinates G).card) ≤
        S.card * (a6401 - (fixedLocatorCoordinates G).card) :=
    Nat.mul_le_mul_right _ hten
  have hle :
      10 * (a6401 - (fixedLocatorCoordinates G).card) ≤
        (n6401 - (fixedLocatorCoordinates G).card) *
          correctionSlopeDegree6401 := hlower.trans hinc
  norm_num [a6401, n6401, ownerDegreeCap6401,
    correctionSlopeDegree6401] at hfixed hle
  omega

/-- Exact arithmetic showing that nine is the sharp integer supplied by
degree-four root capacity at the worst allowed clone size. -/
theorem cloneCurve_nine_vs_ten_exact6401 :
    a6401 - ownerDegreeCap6401 = 54283 ∧
      n6401 - ownerDegreeCap6401 = 131073 ∧
      9 * (a6401 - ownerDegreeCap6401) = 488547 ∧
      correctionSlopeDegree6401 *
          (n6401 - ownerDegreeCap6401) = 524292 ∧
      9 * (a6401 - ownerDegreeCap6401) ≤
        correctionSlopeDegree6401 *
          (n6401 - ownerDegreeCap6401) ∧
      correctionSlopeDegree6401 *
          (n6401 - ownerDegreeCap6401) <
        10 * (a6401 - ownerDegreeCap6401) ∧
      10 * (a6401 - ownerDegreeCap6401) -
        correctionSlopeDegree6401 *
          (n6401 - ownerDegreeCap6401) = 18538 := by
  native_decide

/-- Nine owners on one degree-four clone curve force an identity set of at
least `123922` coordinates.  Thus the extremal nine-fibre branch is not a
generic clone: it contains a giant common coordinate core. -/
theorem nineOwners_force_identityCard_ge_123922_6401
    {F Coord : Type} [Field F] [DecidableEq F]
    [Fintype Coord] [DecidableEq Coord]
    (S : Finset F) (A : F → Finset Coord) (G : Coord → F[X])
    (hCoord : Fintype.card Coord = n6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hroot : ∀ z ∈ S, ∀ i ∈ A z, Polynomial.eval z (G i) = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ correctionSlopeDegree6401)
    (hnine : 9 ≤ S.card) :
    123922 ≤ (fixedLocatorCoordinates G).card := by
  have hinc := locator_root_incidence S A G a6401
    correctionSlopeDegree6401 hrow hroot hdegree
  rw [hCoord] at hinc
  have hlower :
      9 * (a6401 - (fixedLocatorCoordinates G).card) ≤
        S.card * (a6401 - (fixedLocatorCoordinates G).card) :=
    Nat.mul_le_mul_right _ hnine
  have hle := hlower.trans hinc
  norm_num [a6401, n6401, correctionSlopeDegree6401] at hle ⊢
  omega

/-- Below the giant-core threshold the fibre improves from nine to eight. -/
theorem degreeFourCorrectionCurve_ownerCard_le_eight_of_smallIdentity6401
    {F Coord : Type} [Field F] [DecidableEq F]
    [Fintype Coord] [DecidableEq Coord]
    (S : Finset F) (A : F → Finset Coord) (G : Coord → F[X])
    (hCoord : Fintype.card Coord = n6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hroot : ∀ z ∈ S, ∀ i ∈ A z, Polynomial.eval z (G i) = 0)
    (hdegree : ∀ i, (G i).natDegree ≤ correctionSlopeDegree6401)
    (hsmall : (fixedLocatorCoordinates G).card < 123922) :
    S.card ≤ 8 := by
  by_contra hnot
  have hnine : 9 ≤ S.card := by omega
  have hlarge := nineOwners_force_identityCard_ge_123922_6401
    S A G hCoord hrow hroot hdegree hnine
  omega

/-! ## Generalized-weight flat cap for polynomial evaluation normals -/

/-- Evaluation on a finite coordinate set, restricted to polynomials of
degree below `k`. -/
noncomputable def evalDegreeLTOn6401
    {F I : Type*} [Field F]
    (alpha : I → F) (B : Finset I) (k : Nat) :
    Polynomial.degreeLT F k →ₗ[F] (B → F) where
  toFun Q i := Polynomial.eval (alpha i.1) Q.1
  map_add' _ _ := by
    funext i
    simp
  map_smul' _ _ := by
    funext i
    simp

/-- Lagrange interpolation makes the finite evaluation map surjective as
soon as the degree window contains the coordinate set. -/
theorem evalDegreeLTOn_surjective6401
    {F I : Type*} [Field F] [DecidableEq I]
    (alpha : I ↪ F) (B : Finset I) (k : Nat) (hBk : B.card ≤ k) :
    Function.Surjective (evalDegreeLTOn6401 (alpha : I → F) B k) := by
  classical
  intro y
  have hinj : Set.InjOn (alpha : I → F) B := fun _ _ _ _ h ↦ alpha.injective h
  let e := Lagrange.funEquivDegreeLT (v := (alpha : I → F)) hinj
  let small : Polynomial.degreeLT F B.card := e.symm y
  let large : Polynomial.degreeLT F k :=
    ⟨small.1, Polynomial.degreeLT_mono hBk small.2⟩
  refine ⟨large, ?_⟩
  funext i
  have he := e.apply_symm_apply y
  exact congrFun he i

/-- Generalized RS weight in common-zero form.  An `r`-dimensional
polynomial space of degree below `k` has at most `k-r` common evaluation
zeros on an injective domain. -/
theorem commonZeros_card_add_finrank_le_degreeWindow6401
    {F I : Type*} [Field F] [DecidableEq I]
    (alpha : I ↪ F) (K : Submodule F F[X]) [FiniteDimensional F K]
    (k : Nat) (hK : K ≤ Polynomial.degreeLT F k)
    (B : Finset I)
    (hKpos : 0 < Module.finrank F K)
    (hzero : ∀ Q : K, ∀ i ∈ B, Polynomial.eval (alpha i) Q.1 = 0) :
    B.card + Module.finrank F K ≤ k := by
  classical
  by_cases hBk : B.card ≤ k
  · let ev := evalDegreeLTOn6401 (alpha : I → F) B k
    have hevsurj : Function.Surjective ev :=
      evalDegreeLTOn_surjective6401 alpha B k hBk
    let toKer : K →ₗ[F] LinearMap.ker ev := {
      toFun := fun Q ↦ ⟨⟨Q.1, hK Q.2⟩, by
        ext i
        exact hzero Q i.1 i.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    have htoKer : Function.Injective toKer := by
      intro Q R h
      apply Subtype.ext
      exact congrArg (fun T : LinearMap.ker ev ↦ T.1.1) h
    have hdimle : Module.finrank F K ≤
        Module.finrank F (LinearMap.ker ev) :=
      toKer.finrank_le_finrank_of_injective htoKer
    have hrange : LinearMap.range ev = ⊤ := LinearMap.range_eq_top.mpr hevsurj
    have hranknull := LinearMap.finrank_range_add_finrank_ker ev
    have hdom : Module.finrank F (Polynomial.degreeLT F k) = k := by
      rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F k)]
      simp
    have hcod : Module.finrank F (B → F) = B.card := by simp
    rw [hrange, finrank_top, hcod, hdom] at hranknull
    omega
  · have hlarge : k < B.card := Nat.lt_of_not_ge hBk
    have hzeroSpace : K = ⊥ := by
      apply (Submodule.eq_bot_iff K).mpr
      intro Q hQ
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        Q (B.map alpha)
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
        exact hzero ⟨Q, hQ⟩ i hi
      · rw [Finset.card_map]
        by_cases hQzero : Q = 0
        · simpa [hQzero] using
            (lt_of_le_of_lt (Nat.zero_le k) hlarge)
        · have hdegree : Q.natDegree < k := by
            have hmem := hK hQ
            rw [Polynomial.mem_degreeLT] at hmem
            simpa [Polynomial.degree_eq_natDegree hQzero] using hmem
          exact hdegree.trans hlarge
    rw [hzeroSpace, finrank_bot] at hKpos
    omega

/-- Rank-sensitive version of the residual evaluation-flat cap.  If `W` has
dimension `D` and a prefix spans rank `s < D`, its flat has at most
`k-D+s` coordinates.  This is the generalized-Hamming-weight sharpening of
the coarse `k-1` single-polynomial cap. -/
theorem residualEvalNormal_flat_card_add_codim_le_degreeWindow6401
    {F I : Type*} [Field F] [DecidableEq I]
    (alpha : I ↪ F) (W : Submodule F F[X]) [FiniteDimensional F W]
    (k : Nat) (hW : W ≤ Polynomial.degreeLT F k)
    (A : Finset I) {ell : Nat} (f : Fin ell → I)
    (hproper : Submodule.span F
      (Set.range (residualEvalNormal6401 alpha W ∘ f)) ≠ ⊤) :
    (normalSpanFlat (F := F) A
        (residualEvalNormal6401 alpha W) f).card +
      (Module.finrank F W -
        Module.finrank F (Submodule.span F
          (Set.range (residualEvalNormal6401 alpha W ∘ f)))) ≤ k := by
  classical
  let Phi : Submodule F (Module.Dual F W) :=
    Submodule.span F
      (Set.range (residualEvalNormal6401 alpha W ∘ f))
  let K : Submodule F W := Phi.dualCoannihilator
  let Kpoly : Submodule F F[X] := K.map W.subtype
  have hsum : Module.finrank F Phi + Module.finrank F K =
      Module.finrank F W := by
    exact Subspace.finrank_add_finrank_dualCoannihilator_eq Phi
  have hPhiproper : Phi ≠ ⊤ := by simpa [Phi] using hproper
  have hKpos : 0 < Module.finrank F K := by
    have hPhiLt : Module.finrank F Phi < Module.finrank F W := by
      have hlt := Submodule.finrank_lt hPhiproper
      rw [Subspace.dual_finrank_eq] at hlt
      exact hlt
    omega
  have hKpolyDegree : Kpoly ≤ Polynomial.degreeLT F k := by
    rintro Q ⟨q, hq, rfl⟩
    exact hW q.2
  have hKpolyPos : 0 < Module.finrank F Kpoly := by
    simpa [Kpoly, K] using hKpos
  have hcommonZero : ∀ Q : Kpoly,
      ∀ i ∈ normalSpanFlat (F := F) A
        (residualEvalNormal6401 alpha W) f,
        Polynomial.eval (alpha i) Q.1 = 0 := by
    intro Q i hi
    obtain ⟨q, hqK, hqeq⟩ := Q.2
    have hiPhi : residualEvalNormal6401 alpha W i ∈ Phi := by
      simpa [Phi, normalSpanFlat] using (Finset.mem_filter.mp hi).2
    have hvanish : residualEvalNormal6401 alpha W i q = 0 :=
      (Submodule.mem_dualCoannihilator q).mp hqK
        (residualEvalNormal6401 alpha W i) hiPhi
    change Polynomial.eval (alpha i) Q.1 = 0
    rw [← hqeq]
    exact hvanish
  have hzeros := commonZeros_card_add_finrank_le_degreeWindow6401
    alpha Kpoly k hKpolyDegree
      (normalSpanFlat (F := F) A
        (residualEvalNormal6401 alpha W) f)
      hKpolyPos hcommonZero
  have hKdim : Module.finrank F Kpoly =
      Module.finrank F W - Module.finrank F Phi := by
    have hmap : Module.finrank F Kpoly = Module.finrank F K := by
      simp [Kpoly]
    omega
  simpa [Phi, hKdim] using hzeros

/-- Convenient isolated-cardinality form of the preceding generalized
weight inequality. -/
theorem residualEvalNormal_flat_card_le_rankSensitive6401
    {F I : Type*} [Field F] [DecidableEq I]
    (alpha : I ↪ F) (W : Submodule F F[X]) [FiniteDimensional F W]
    (k : Nat) (hW : W ≤ Polynomial.degreeLT F k)
    (A : Finset I) {ell : Nat} (f : Fin ell → I)
    (hproper : Submodule.span F
      (Set.range (residualEvalNormal6401 alpha W ∘ f)) ≠ ⊤) :
    (normalSpanFlat (F := F) A
        (residualEvalNormal6401 alpha W) f).card ≤
      k - (Module.finrank F W -
        Module.finrank F (Submodule.span F
          (Set.range (residualEvalNormal6401 alpha W ∘ f)))) := by
  have h := residualEvalNormal_flat_card_add_codim_le_degreeWindow6401
    alpha W k hW A f hproper
  omega

/-! ## What the nine-fibre and one-step atlas ledgers buy -/

def uniformNineFibreLastPaidDimension6401 : Nat := 108
def mixedAtlasLastPaidDimension6401 : Nat := 109

/-- A uniform nine-owner cap on every full-rank nonproper coordinate tuple
pays correction dimension `108`. -/
theorem uniformNineFibre_dimension108_paid6401 :
    9 * Nat.choose n6401 (uniformNineFibreLastPaidDimension6401 + 1) ≤
      weakCurveSeedCap6401 *
        Nat.choose a6401 (uniformNineFibreLastPaidDimension6401 + 1) := by
  native_decide

/-- Dimension `109` is the first failure of the bare uniform-nine-fibre
compiler. -/
theorem uniformNineFibre_dimension109_misses6401 :
    weakCurveSeedCap6401 *
        Nat.choose a6401 (uniformNineFibreLastPaidDimension6401 + 2) <
      9 * Nat.choose n6401
        (uniformNineFibreLastPaidDimension6401 + 2) := by
  native_decide

/-- For one basis `B` of size `s`, extending by one coordinate costs at most

`4 * (n-s) + 5 * ((k-1)-s)`:

four owners off the clone set and nine on it.  If all size-`s` subsets in an
owner row are evaluation bases, this mixed one-step compiler pays `s=109`.
The theorem records the exact division-free comparison; producing this basis
density, or charging its rank-flat failures, is the remaining hypothesis. -/
theorem mixedProperClone_dimension109_paid6401 :
    Nat.choose n6401 mixedAtlasLastPaidDimension6401 *
        (correctionSlopeDegree6401 *
            (n6401 - mixedAtlasLastPaidDimension6401) +
          (9 - correctionSlopeDegree6401) *
            (ownerDegreeCap6401 - mixedAtlasLastPaidDimension6401)) ≤
      weakCurveSeedCap6401 *
        (Nat.choose a6401 mixedAtlasLastPaidDimension6401 *
          (a6401 - mixedAtlasLastPaidDimension6401)) := by
  native_decide

/-- The same one-step compiler misses at dimension `110`; its exact quotient
is `336315618709927949`, above the retained high-owner mass by
`62724427957117010`. -/
theorem mixedProperClone_dimension110_misses6401 :
    weakCurveSeedCap6401 *
        (Nat.choose a6401 (mixedAtlasLastPaidDimension6401 + 1) *
          (a6401 - (mixedAtlasLastPaidDimension6401 + 1))) <
      Nat.choose n6401 (mixedAtlasLastPaidDimension6401 + 1) *
        (correctionSlopeDegree6401 *
            (n6401 - (mixedAtlasLastPaidDimension6401 + 1)) +
          (9 - correctionSlopeDegree6401) *
            (ownerDegreeCap6401 -
              (mixedAtlasLastPaidDimension6401 + 1))) := by
  native_decide

theorem mixedProperClone_exact_quotients6401 :
    (Nat.choose n6401 mixedAtlasLastPaidDimension6401 *
        (correctionSlopeDegree6401 *
            (n6401 - mixedAtlasLastPaidDimension6401) +
          (9 - correctionSlopeDegree6401) *
            (ownerDegreeCap6401 - mixedAtlasLastPaidDimension6401))) /
      (Nat.choose a6401 mixedAtlasLastPaidDimension6401 *
        (a6401 - mixedAtlasLastPaidDimension6401)) =
        237757474110720925 ∧
      (Nat.choose n6401 (mixedAtlasLastPaidDimension6401 + 1) *
        (correctionSlopeDegree6401 *
            (n6401 - (mixedAtlasLastPaidDimension6401 + 1)) +
          (9 - correctionSlopeDegree6401) *
            (ownerDegreeCap6401 -
              (mixedAtlasLastPaidDimension6401 + 1)))) /
      (Nat.choose a6401 (mixedAtlasLastPaidDimension6401 + 1) *
        (a6401 - (mixedAtlasLastPaidDimension6401 + 1))) =
        336315618709927949 := by
  native_decide

end BCHKSCorrectionCurveAtlas6401
end ProximityPrize.SubmissionLower
