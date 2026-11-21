import ProximityPrize.SubmissionLower.Bridge6925Defs
import ProximityPrize.SubmissionLower.Fast076
set_option Elab.async false
section PackSource_P0_10RDefs
set_option autoImplicit true
namespace P0_10R

noncomputable section

open P0 (AnchorModel AnchoredFamily K highPrefix)
open P0_10 (BufferedPair BankVanishes freeShape movingShape fullShape MarkOn band TerminalDivisibility)
open K1_14 (Banks Equation)
open K1_14_3 (Surface Parent ProjectedProduct)

/-- Both full banks vanish and every common positive-ordinate factor passes
the constant-seed chain-rule test in the outer derivative variable. -/
def SurfacePass {w : ℤ} {rows : Banks} {i : Fin 3} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ K1_14_3R.compatible pair.free pair.moving q

/-- The prefix pays losses on this input. Surviving labels are covered by
the same tested parents whose reduced distinct-Y product serves the subbank. -/
structure RetainedCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 3, BufferedPair M.overhead rows i) where
  kept : Finset K
  subset : kept ⊆ Γ
  paid : (Γ \ kept).card ≤ highPrefix M.overhead
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, (pairs 0).free ∈ q.asIdeal ∧ (pairs 0).moving ∈ q.asIdeal
  survives : ∀ q ∈ parents, SurfacePass (pairs 1) q
  terminal : ∀ q ∈ parents, BankVanishes rows (fullShape M.overhead) q
  covers : ∀ γ ∈ kept, ∃ q ∈ parents, MarkOn M F q γ
  equation : Equation
  projected : ProjectedProduct parents equation
  y_bound : equation.natDegree ≤ (band M.overhead).yBound
  divides : TerminalDivisibility M.overhead rows equation

def PrefixCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 3, BufferedPair M.overhead rows i) : Prop :=
  Γ.card ≤ highPrefix M.overhead ∨ Nonempty (RetainedCover M F pairs)

end
end P0_10R

namespace P0_10R.Bridge

noncomputable section

open P0 (AnchorModel AnchoredFamily agreement p K t)
open P0_10 (BufferedPair)
open K1_14 (Banks Equation Jet Shape)
open K1_14_2 (Ambient ODE OnJet SmallRootCurve OnRoot endpointDegree)
open K1_14_2_2 (Active Fits)
open Polynomial

def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)

def BankPass (rows : Banks) (s : Shape) (I : Ideal Ambient) : Prop :=
  ∀ P ∈ rows s (P0_10.fullCutoff s), K1_14_2.toJet P ∈ I

def PairPass {w rows i} (pair : BufferedPair w rows i) (I : Ideal Ambient) : Prop :=
  BankPass rows (P0_10.freeShape w i) I ∧ BankPass rows (P0_10.movingShape w i) I ∧
    ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ pair.free → C f ∣ pair.moving →
      K1_14_2.toJet (C f) ∈ I → ∀ g a, K1_14_3.IsClearing f g a →
        K1_14_2.toJet (K1_14_3R.chainCutter g) ∈ I

/-- Integral section lengths use the floors of the rational mass bounds. -/
def initialCap : Fin 4 → ℕ := ![6312, 173392, 828372, 9420720]

def reserveFiveCap : Fin 4 → ℕ := ![358, 9306, 85921, 910022]

/-- The conservative initial cap pays low-seed and constant-image exits. -/
def initialE₀ : ℕ := 10494016

def initialFee : ℕ := (p+1)*828372 + initialE₀ + 6312 + (p+1)*(1360+6927)

structure InitialCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (P Q : Jet) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  initial : ∀ I ∈ parents, K1_14_2.toJet P ∈ I ∧ K1_14_2.toJet Q ∈ I
  masses : Fits parents initialCap
  direct : Finset K
  paid : direct.card ≤ initialFee
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ

/-- The stage caps for proper failed tests, in chronological order. -/
def stageFiveShape : Shape := ⟨266, 369, 77, 10980⟩
def terminalFullShape : Shape := ⟨2048, 2845, 600, 75000⟩

def stageLateShape : Shape := ⟨600,837,168,25162⟩
def lateCap : Fin 4 → ℕ := ![169,4062,35223,281939]
def lossSeedCap : ℕ := 230165867
def lossYCap : ℕ := 3168268898
def constantFee : ℕ := 157297219649
def curveFee : ℕ := 77552671119557230

def beta : ℚ := (82014 : ℚ) / 45505

def rootPrice (g H : ℕ) : ℚ :=
  let s : ℚ := 2 * (g : ℚ) - 1
  (s + beta * (((2 * endpointDegree - 1 : ℕ) : ℚ)*s+1)) * H + g

def RootTariff : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    M.overhead ≤ 3554 → ∀ T ⊆ Γ, ∀ I g H, 0 < g → g ≤ 8 →
    SmallRootCurve I g H →
    (∀ γ ∈ T, OnRoot I (M.label γ) (F.scalar γ)) →
    (T.card : ℚ) ≤ rootPrice g H

def fixedPrice (B J : ℕ) : ℕ :=
  let d := endpointDegree
  let e := 2*d-3
  let a := 1+e*(B-1)
  let v := min a (e*(J-1)+d)
  let gap := agreement-d
  (t*((B-J)*v+J*a)+(gap-1))/gap+B^2

def contactPower (w : ℤ) (s : Shape) (W : ℕ) : ℕ :=
  1 + (P0_10.fullCutoff s - W) / (2*w.toNat)

def FullDivisibility (w : ℤ) (rows : Banks) (f : Equation) : Prop :=
  let s := P0_10.fullShape w
  ∀ W < s.m * agreement, ∀ P ∈ rows s W, P ≠ 0 →
    f ^ (contactPower w s W - P.natDegree) ∣ P.leadingCoeff

end
end P0_10R.Bridge

end PackSource_P0_10RDefs
section PackSource_P0_10R_1Prepare
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 900000

namespace P0_10R_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial
open K1_14_2_2_2 (afterGcd)
open K1_14_2_2_2_1 (extractSeed extractOrdinary seedDegree_seed seedDegree_C)
open K1_14_3 (NoMovingCommon)
open scoped BigOperators
open private divisor_caps seedContent_cap gcd_caps multiset_prod_ne_zero
  distinct_le_degree seed_degree_mul atMark_prod_eq_zero row_at_mark from ProximityPrize.SubmissionLower.Fast051

def freeZero : Shape := ⟨55, 76, 16, 1360⟩
def movingZero : Shape := ⟨160, 222, 46, 6927⟩

/-- Residual rows and their common ordinary factors, with divisibility into
the original rows retained for both kinds of component. -/
structure Prepared (P Q : Jet) (G H : ODE) where
  seedContent : Seeds
  free : Jet
  moving : Jet
  ordinary : Finset Equation
  gcdSeed : ℕ
  gcdY : ℕ
  seedContent_ne : seedContent ≠ 0
  seedContent_degree : seedContent.totalDegree ≤ 1360 + 6927
  gcdSeed_le : gcdSeed ≤ 1360
  gcdY_le : gcdY ≤ 76
  free_caps : RowCaps free (afterGcd freeZero gcdSeed gcdY)
  moving_caps : RowCaps moving (afterGcd movingZero gcdSeed gcdY)
  proper : ProperPair free moving
  free_dvd : free ∣ P
  moving_dvd : moving ∣ Q
  ordinary_factors : ∀ f ∈ ordinary, Irreducible f ∧ 0 < f.natDegree
  ordinary_dvd : ∀ f ∈ ordinary, C f ∣ P ∧ C f ∣ Q
  ordinary_seed : ∑ f ∈ ordinary, ordinarySeedDegree f ≤ gcdSeed
  ordinary_y : ∑ f ∈ ordinary, f.natDegree ≤ gcdY
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    fixedAt G S = 0 ∨ fixedAt H S = 0 ∨ graphEval z seedContent = 0 ∨
    (jetAt free z S = 0 ∧ jetAt moving z S = 0) ∨ ∃ f ∈ ordinary, atMark f z S = 0

/-- Strip the two fixed parts and seed contents before spending the full
ordinary gcd in both residual shapes. -/
theorem prepare {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPc : RowCaps P freeZero) (hQc : RowCaps Q movingZero) (hnc : NoMovingCommon P Q)
    (A : FixedPart P freeZero) (B : FixedPart Q movingZero) :
    Nonempty (Prepared P Q A.equation B.equation) := by
  classical
  have hpr : A.residual ≠ 0 := fun hz => hP (by rw [A.factorization, hz, mul_zero])
  have hqr : B.residual ≠ 0 := fun hz => hQ (by rw [B.factorization, hz, mul_zero])
  have hAr : A.residual ∣ P := ⟨_, A.factorization.trans (mul_comm _ _)⟩
  have hBr : B.residual ∣ Q := ⟨_, B.factorization.trans (mul_comm _ _)⟩
  obtain ⟨a, P', ha, hpa⟩ := extractSeed A.residual hpr
  obtain ⟨b, Q', hb, _⟩ := extractSeed B.residual hqr
  have hpa0 : (C (C a) * P' : Jet) ≠ 0 := ha ▸ hpr
  have hqb0 : (C (C b) * Q' : Jet) ≠ 0 := hb ▸ hqr
  have hP' : P' ∣ A.residual := ⟨_, ha.trans (mul_comm _ _)⟩
  have hQ' : Q' ∣ B.residual := ⟨_, hb.trans (mul_comm _ _)⟩
  have hord (D : Jet) (hD : Irreducible D) (hdP : D ∣ P') (hdQ : D ∣ Q') :
      D.natDegree = 0 := by
    by_contra hpos
    obtain ⟨G, rfl⟩ := hnc D hD (hdP.trans (hP'.trans hAr)) (hdQ.trans (hQ'.trans hBr))
      (Nat.pos_of_ne_zero hpos)
    exact A.stripped G hD (hdP.trans hP')
  obtain ⟨M, L, T, hL, hT, hproper, hM⟩ := extractOrdinary P' Q'
    (right_ne_zero_of_mul hpa0) (right_ne_zero_of_mul hqb0) hpa hord
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at hpa0
  have hb0 : b ≠ 0 := by intro hz; simp [hz] at hqb0
  have hau : a.totalDegree ≤ 1360 := seedContent_cap hP hPc (Dvd.dvd.trans ⟨P', ha⟩ hAr)
  have hbu : b.totalDegree ≤ 6927 := seedContent_cap hQ hQc (Dvd.dvd.trans ⟨Q', hb⟩ hBr)
  have hp : P = fixedIncl A.equation * (C (C a) * (C M.prod * L)) :=
    A.factorization.trans (by rw [ha, hL])
  have hq : Q = fixedIncl B.equation * (C (C b) * (C M.prod * T)) :=
    B.factorization.trans (by rw [hb, hT])
  have hl : C M.prod * L ∣ P := by rw [← hL]; exact hP'.trans hAr
  have ht : C M.prod * T ∣ Q := by rw [← hT]; exact hQ'.trans hBr
  have hM0 : ∀ f ∈ M, f ≠ 0 := fun f hf => (hM f hf).1.ne_zero
  have hF := multiset_prod_ne_zero M hM0
  obtain ⟨hx, hy, hc⟩ := gcd_caps hF hproper.left_ne (divisor_caps hP hPc hl)
  have htCaps := (gcd_caps hF hproper.right_ne (divisor_caps hQ hQc ht)).2.2
  have hs1 : ordinarySeedDegree (1 : Equation) = 0 := by
    rw [← seedDegree_C]
    simpa only [C_1, MvPolynomial.totalDegree_one] using seedDegree_seed (1 : Seeds)
  refine ⟨{
    seedContent := a*b
    free := L
    moving := T
    ordinary := M.toFinset
    gcdSeed := ordinarySeedDegree M.prod
    gcdY := M.prod.natDegree
    seedContent_ne := mul_ne_zero ha0 hb0
    seedContent_degree := (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hau hbu)
    gcdSeed_le := hx
    gcdY_le := hy
    free_caps := hc
    moving_caps := htCaps
    proper := hproper
    free_dvd := (dvd_mul_left _ _).trans hl
    moving_dvd := (dvd_mul_left _ _).trans ht
    ordinary_factors := fun f hf => hM f (Multiset.mem_toFinset.mp hf)
    ordinary_dvd := ?_
    ordinary_seed := distinct_le_degree ordinarySeedDegree hs1 (fun hf hg => seed_degree_mul hf hg) M hM0
    ordinary_y := distinct_le_degree natDegree natDegree_one (fun hf hg => natDegree_mul hf hg) M hM0
    cover := ?_ }⟩
  · intro f hf
    have hdiv : f ∣ M.prod := Multiset.dvd_prod (Multiset.mem_toFinset.mp hf)
    have hd := map_dvd (C : Equation →+* Jet) hdiv
    exact ⟨hd.trans ((dvd_mul_right _ _).trans hl), hd.trans ((dvd_mul_right _ _).trans ht)⟩
  · intro z S hzP hzQ
    by_cases h1 : fixedAt A.equation S = 0
    · exact Or.inl h1
    by_cases h2 : fixedAt B.equation S = 0
    · exact Or.inr (Or.inl h2)
    by_cases h3 : graphEval z (a*b) = 0
    · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4 : atMark M.prod z S = 0
    · obtain ⟨f, hf, hzero⟩ := atMark_prod_eq_zero h4
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f, Multiset.mem_toFinset.mpr hf, hzero⟩)))
    · rw [map_mul] at h3
      rw [row_at_mark hp, mul_eq_zero, mul_eq_zero, mul_eq_zero] at hzP
      rw [row_at_mark hq, mul_eq_zero, mul_eq_zero, mul_eq_zero] at hzQ
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨((hzP.resolve_left h1).resolve_left (left_ne_zero_of_mul h3)).resolve_left h4,
         ((hzQ.resolve_left h2).resolve_left (right_ne_zero_of_mul h3)).resolve_left h4⟩)))

end
end P0_10R_1
end PackSource_P0_10R_1Prepare
section PackSource_P0_10R_1Budget
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace P0_10R_1

open K1_14_2_2_2 (afterGcd residualBudget ordinaryBudget)
open P0_10R.Bridge (initialCap)

private theorem split_mul {u x b a d : ℕ} (hx : x ≤ u) (ha : a ≤ b) (hd : d ≤ b) :
    (u-x)*a + x*d ≤ u*b := by
  calc
    _ ≤ (u-x)*b + x*b :=
      Nat.add_le_add (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hd)
    _ = _ := by rw [← Nat.add_mul, Nat.sub_add_cancel hx]

/-- Shared-gcd accounting for the four initial bridge section lengths. -/
theorem ledger (x y : ℕ) (hx : x ≤ 1360) (hy : y ≤ 76) (k : Fin 4) :
    residualBudget (afterGcd freeZero x y) (afterGcd movingZero x y) k +
      ordinaryBudget x y k ≤ initialCap k := by
  have h := PriceReceipt6925.initial_cap k x y hx hy
  rw [Nat.add_comm]
  exact h
end P0_10R_1
end PackSource_P0_10R_1Budget
