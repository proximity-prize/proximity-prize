import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.PortHighBase
import ProximityPrize.SubmissionLower.PortLow8
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_10R
noncomputable section
open P0 (AnchorModel AnchoredFamily K highPrefix)
open P0_10 (BufferedPair BankVanishes freeShape movingShape fullShape MarkOn band TerminalDivisibility)
open K1_14 (Banks Equation)
open K1_14_3 (Surface Parent ProjectedProduct)
def SurfacePass {w : ℤ} {rows : Banks} {i : Fin 2} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ K1_14_3R.compatible pair.free pair.moving q
structure RetainedCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) where
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
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) : Prop :=
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
def initialCap : Fin 4 → ℕ := ![5548, 125234, 577116, 5169640]
def reserveFiveCap : Fin 4 → ℕ := ![337, 7944, 82782, 640800]
def initialE₀ : ℕ := 6242936
def initialFee : ℕ := (p+1)*577116 + initialE₀ + 5548 + (p+1)*(1036+4990)
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
def stageFiveShape : Shape := ⟨203, 282, 58, 7726⟩
def terminalFullShape : Shape := ⟨1024, 1422, 290, 141471⟩
def lossSeedCap : ℕ := 175962087
def lossYCap : ℕ := 2478622105
def constantFee : ℕ := 90522632628
def curveFee : ℕ := 59646678368515881
def beta : ℚ := (81927 : ℚ) / 45592
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
namespace P0_10R.Later
noncomputable section
open Polynomial
open P0 (agreement)
open K1_14 (Jet Shape atX jetAt)
open K1_14_3 (Surface Parent MassCap mass JetPlane JetCaps SeedCover fixedAt)
open K1_14_3_2 (AtSurface)
def freeZero : Shape := ⟨34, 47, 10, 515⟩
def movingZero : Shape := ⟨67, 93, 18, 1857⟩
def freeFive : Shape := ⟨58, 80, 17, 940⟩
def movingFive : Shape := ⟨124, 172, 35, 3138⟩
def laterTerminal : Shape := ⟨582, 809, 165, 59515⟩
def contactPower (h : ℕ) (s : Shape) (W : ℕ) : ℕ :=
  1 + (s.m * agreement - 1 - W) / (2 * h)
structure InitialCover (P Q : Jet) where
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, P ∈ q.asIdeal ∧ Q ∈ q.asIdeal
  masses : MassCap parents 1643 28355 183584
  jetMass : mass parents .jets ≤ 1221580
  seeds : SeedCover
  seedDegree : seeds.curve.totalDegree ≤ 183584 + 515 + 1857
  seedPoints : seeds.points.card ≤ 1221580
  ordinates : Finset K1_14.FX
  ordinateCount : ordinates.card ≤ 1643
  lowJet : JetPlane
  fixedFree : JetPlane
  fixedMoving : JetPlane
  lowJet_ne : lowJet ≠ 0
  fixedFree_ne : fixedFree ≠ 0
  fixedMoving_ne : fixedMoving ≠ 0
  lowJet_caps : JetCaps lowJet 183584 28355
  fixedFree_caps : JetCaps fixedFree 47 10
  fixedMoving_caps : JetCaps fixedMoving 93 18
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    seeds.Covers z ∨ atX S ∈ ordinates ∨ fixedAt lowJet S = 0 ∨
    fixedAt fixedFree S = 0 ∨ fixedAt fixedMoving S = 0 ∨
    ∃ q ∈ parents, AtSurface q z S
def odePrice (d b j : ℕ) : ℕ :=
  let T := 2 * d - 3
  let a := 1 + T * (b - 1)
  let v := min a (T * (j - 1) + d)
  let gap := agreement - d
  ((262144 - d) * ((b - j) * v + j * a) + (gap - 1)) / gap + b * (b - 1) + b
end
end P0_10R.Later
end
section
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
def freeZero : Shape := ⟨55, 76, 17, 1036⟩
def movingZero : Shape := ⟨138, 191, 39, 4990⟩
structure Prepared (P Q : Jet) (G H : ODE) where
  seedContent : Seeds
  free : Jet
  moving : Jet
  ordinary : Finset Equation
  gcdSeed : ℕ
  gcdY : ℕ
  seedContent_ne : seedContent ≠ 0
  seedContent_degree : seedContent.totalDegree ≤ 1036 + 4990
  gcdSeed_le : gcdSeed ≤ 1036
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
  have hau : a.totalDegree ≤ 1036 := seedContent_cap hP hPc (Dvd.dvd.trans ⟨P', ha⟩ hAr)
  have hbu : b.totalDegree ≤ 4990 := seedContent_cap hQ hQc (Dvd.dvd.trans ⟨Q', hb⟩ hBr)
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
end
section
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
theorem ledger (x y : ℕ) (hx : x ≤ 1036) (hy : y ≤ 76) (k : Fin 4) :
    residualBudget (afterGcd freeZero x y) (afterGcd movingZero x y) k +
      ordinaryBudget x y k ≤ initialCap k := by
  have hj : min 39 (191-y) = 39 := min_eq_left (by omega)
  fin_cases k
  · change ((76-y)*min 39 (191-y) + (191-y)*min 17 (76-y) -
        min 17 (76-y)*min 39 (191-y)) + y ≤ 5548
    rw [hj]
    by_cases h : y ≤ 59
    · rw [min_eq_left (show 17 ≤ 76-y by omega)]
      omega
    · have hs : 76-y ≤ 17 := by omega
      rw [min_eq_right hs]
      have hm : (191-y)*(76-y) ≤ 191*17 := Nat.mul_le_mul (Nat.sub_le _ _) hs
      omega
  · change (1036-x)*min 39 (191-y) + (4990-x)*min 17 (76-y) + x ≤ 125234
    rw [hj]
    have hm := Nat.mul_le_mul_left (4990-x) (min_le_left 17 (76-y))
    omega
  · change (1036-x)*(191-y) + (4990-x)*(76-y) + 2*x*y ≤ 577116
    have h₁ : (1036-x)*(191-y) + x*y ≤ 1036*191 :=
      split_mul hx (Nat.sub_le _ _) (by omega)
    have h₂ : (4990-x)*(76-y) + x*y ≤ 4990*76 :=
      split_mul (by omega) (Nat.sub_le _ _) hy
    calc
      _ = ((1036-x)*(191-y) + x*y) + ((4990-x)*(76-y) + x*y) := by ring
      _ ≤ 1036*191 + 4990*76 := Nat.add_le_add h₁ h₂
      _ = _ := by decide
  · change (1036-x)*(4990-x) + x*x ≤ 5169640
    exact (split_mul hx (Nat.sub_le _ _) (by omega : x ≤ 4990)).trans (by decide)
end P0_10R_1
end
section
namespace P0_10R.Bridge
noncomputable section
open Polynomial
open P0 (K AnchorModel AnchoredFamily p agreement lowCutoff)
open P0_10 (BufferedPair JetSource freeShape movingShape fullShape scheduled reserveCutoff fullCutoff)
open K1_14 (Jet Shape Banks jetAt)
open K1_14_2 (Ambient toJet eval_toJet)
open K1_14_2_2 (RowCaps Active dual orderOn sectionDegree)
open K1_14_2_2_3
open private specialize_shiftedWord shift_word from ProximityPrize.SubmissionLower.Fast052
theorem free_scheduled (w : ℤ) (i : Fin 2) : freeShape w i ∈ scheduled w := by
  fin_cases i <;> simp [scheduled]
theorem moving_scheduled (w : ℤ) (i : Fin 2) : movingShape w i ∈ scheduled w := by
  fin_cases i <;> simp [scheduled]
theorem full_scheduled (w : ℤ) : fullShape w ∈ scheduled w := by simp [scheduled]
theorem full_bridge (w : ℤ) (hw : w ≤ 3554) : fullShape w = terminalFullShape := by
  simp only [fullShape, P0_10.terminalShape, P0_10.band, ite_eq_left hw]
  rfl
theorem moving_five (w : ℤ) (hw : w ≤ 3554) : movingShape w 1 = stageFiveShape := by
  rw [movingShape, ite_eq_left hw]
  rfl
theorem bridge_five_buffer (w : ℤ) (hw : w ≤ 3554) (s : Shape)
    (hs : s = freeShape w 1 ∨ s = movingShape w 1) :
    reserveCutoff w s 1 + 2*w.toNat*5 ≤ fullCutoff s := by
  have h : w.toNat ≤ 3554 := by omega
  have hcut : 35540 ≤ fullCutoff s := by
    rcases hs with rfl | rfl
    · simp only [freeShape, ite_eq_left hw]
      decide
    · rw [moving_five w hw]
      decide
  have hspend : 2*w.toNat*5 ≤ 35540 := by omega
  change fullCutoff s - 2*w.toNat*5 + 2*w.toNat*5 ≤ fullCutoff s
  omega
theorem bank_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) {s : Shape} (hs : s ∈ scheduled M.overhead)
    (hm : 0 < s.m) {P : Jet} {W : ℕ} (hW : W ≤ fullCutoff s) (hP : P ∈ rows s W) :
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 :=
  src.necessary s hs W (by
    have : 0 < s.m * agreement := Nat.mul_pos hm (by decide)
    unfold fullCutoff at hW
    omega) P hP
theorem buffered_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    (i : Fin 2) (pair : BufferedPair M.overhead rows i) :
    ∀ γ ∈ Γ, jetAt pair.free (M.label γ) (F.scalar γ) = 0 ∧
      jetAt pair.moving (M.label γ) (F.scalar γ) = 0 := by
  have hf : 0 < (freeShape M.overhead i).m := by
    rw [freeShape, ite_eq_left hw]
    fin_cases i <;> decide
  have hq : 0 < (movingShape M.overhead i).m := by
    rw [movingShape, ite_eq_left hw]
    fin_cases i <;> decide
  intro γ hγ
  exact ⟨bank_zero src (free_scheduled _ _) hf (Nat.sub_le _ _) pair.free_mem γ hγ,
    bank_zero src (moving_scheduled _ _) hq (Nat.sub_le _ _) pair.moving_mem γ hγ⟩
theorem failed_bank {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) {s : Shape}
    (hs : s ∈ scheduled M.overhead) (hm : 0 < s.m) {I : Ideal Ambient}
    (hf : ¬ BankPass rows s I) :
    ∃ P : Jet, RowCaps P s ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  unfold BankPass at hf
  push Not at hf
  obtain ⟨P, hP, hprop⟩ := hf
  exact ⟨P, src.shape s hs _ P hP, hprop, bank_zero src hs hm le_rfl hP⟩
theorem failed_pair {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    (pair : BufferedPair M.overhead rows 1) {I : Ideal Ambient} (hf : ¬ PairPass pair I) :
    ∃ P : Jet, RowCaps P stageFiveShape ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  have hc : freeShape M.overhead 1 = ⟨82, 113, 25, 1601⟩ := by
    rw [freeShape, ite_eq_left hw]
    rfl
  have hm := moving_five M.overhead hw
  have hfreePos : 0 < (freeShape M.overhead 1).m := by rw [hc]; decide
  have hmovePos : 0 < (movingShape M.overhead 1).m := by rw [hm]; decide
  by_cases hP : BankPass rows (freeShape M.overhead 1) I
  · by_cases hQ : BankPass rows (movingShape M.overhead 1) I
    · have htest : ¬ (∀ f : K1_14.Equation, Irreducible f → 0 < f.natDegree →
          C f ∣ pair.free → C f ∣ pair.moving → toJet (C f) ∈ I →
          ∀ g a, K1_14_3.IsClearing f g a → toJet (K1_14_3R.chainCutter g) ∈ I) :=
        fun h => hf ⟨hP, hQ, h⟩
      push Not at htest
      obtain ⟨f, _, _, _, hdiv, hmem, g, a, hclear, hproper⟩ := htest
      have hcaps := src.shape _ (moving_scheduled _ _) _ _ pair.moving_mem
      have hj : 1 ≤ (movingShape M.overhead 1).J := by rw [hm]; decide
      have hG := K1_14_3R.chainCutter_caps_of_dvd pair.moving_ne hcaps hj hdiv hclear
      rw [hm] at hG
      refine ⟨K1_14_3R.chainCutter g, hG, hproper, ?_⟩
      intro γ _ hγ
      apply K1_14_3R.chainCutter_zero hclear
      have hz := RingHom.mem_ker.mp (hγ hmem)
      simpa only [eval_toJet, jetAt, eval₂_C, coe_eval₂RingHom, K1_14.atMark] using hz
    · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (moving_scheduled _ _) hmovePos hQ
      rw [hm] at hcaps
      exact ⟨P, hcaps, hproper, fun γ hγ _ => hzero γ hγ⟩
  · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (free_scheduled _ _) hfreePos hP
    rw [hc] at hcaps
    refine ⟨P, ?_, hproper, fun γ hγ _ => hzero γ hγ⟩
    intro j i h
    obtain ⟨hb, hj, hu⟩ := hcaps j i h
    exact ⟨hb.trans (by decide), hj.trans (by decide), hu.trans (by decide)⟩
theorem failed_terminal {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    {I : Ideal Ambient} (hf : ¬ BankPass rows (fullShape M.overhead) I) :
    ∃ P : Jet, RowCaps P terminalFullShape ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
  have hm : 0 < (fullShape M.overhead).m := by rw [full_bridge _ hw]; decide
  obtain ⟨P, hc, hp, hz⟩ := failed_bank src (full_scheduled _) hm hf
  rw [full_bridge _ hw] at hc
  exact ⟨P, hc, hp, fun γ hγ _ => hz γ hγ⟩
private theorem shifted_contact {A : Type*} [CommRing A] (a : K1_14.Seeds →+* A)
    {rows : Banks} {s : Shape} {I : Ideal Ambient} {h W r : ℕ} {P : Jet}
    (hn : ∀ W W', W ≤ W' → rows s W ≤ rows s W')
    (hs : K1_14_3.SeedShift h rows s) (hv : BankPass rows s I)
    (hcut : W + 2*h*r ≤ fullCutoff s) (hP : P ∈ rows s W) :
    fibreContact (I.map (specializeJets a)) (specializeJets a (toJet P)) r := by
  intro t ht
  rw [← specialize_shiftedWord]
  apply Ideal.mem_map_of_mem
  exact hv _ (hn _ _ ((Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _).trans hcut)
    (shift_word hs hP t))
theorem buffered_order {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    {s : Shape} (hpair : s = freeShape M.overhead 1 ∨ s = movingShape M.overhead 1)
    {I : Ideal Ambient} (hactive : Active I) (hv : BankPass rows s I)
    {P : Jet} (hP : P ∈ rows s (reserveCutoff M.overhead s 1)) :
    orderOn I P 6 := by
  classical
  have hs : s ∈ scheduled M.overhead := by
    rcases hpair with rfl | rfl
    · exact free_scheduled _ _
    · exact moving_scheduled _ _
  have hn := src.nested s hs s hs rfl rfl rfl le_rfl
  have hcut := bridge_five_buffer M.overhead hw s hpair
  have ht : (5 : ℕ) < p := by decide
  by_cases hd : dual I
  · have hc := shifted_contact (algebraMap K1_14.Seeds K1_14_2.SeedField) hn
      (src.shift s hs) hv hcut hP
    rw [← mapGenericJets_eq] at hc
    exact clear_dual hd (K1_14_2_2_3_1.proof I hactive.prime hactive.jet_finite
      hd hactive.jet_lt _ 5 ht hc)
  · obtain ⟨g, hg, hdeg, he⟩ := K1_14_2_2_3_2.proof I hactive hd
    let _ : I.IsPrime := hactive.prime
    let _ : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
    let _ : CharP K1_14.FX p := charP_of_injective_ringHom K1_14.seedEmbedding.injective p
    let _ : CharP (JetImageField I) p :=
      charP_of_injective_ringHom ((jetImageMap I).comp MvPolynomial.C).injective p
    apply clear_rank_one hactive.prime hd
    have hc := shifted_contact (jetImageMap I) hn (src.shift s hs) hv hcut hP
    change fibreContact (I.map (imageFibreMap I)) (imageFibreMap I (toJet P)) 5 at hc
    rw [he] at hc ⊢
    exact divisor_contact hg hdeg ht hc
end
end P0_10R.Bridge
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 900000
namespace P0_10R.Bridge
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily agreement p lowCutoff)
open P0_10 (JetSource scheduled terminalShape fullShape fullCutoff)
open K1_14 (Banks Shape Jet Equation Seeds FX seedHasse)
open K1_14_2 (Ambient toJet FibreRing mapGenericSeed mapGenericJets eval_toJet generic)
open K1_14_2_2 (Active dual)
open K1_14_3 (Surface Parent SeedClosure SeedField JetField JetClosure JetPlane seedFibreEval
  seedGeneric jetGeneric fixedEmbedding OrderAt ProjectedProduct)
open K1_14_2_6 (genericSeedPoint genericJetPoint)
open private ambientToJet toJet_equiv from ProximityPrize.SubmissionLower.Fast071
open private fibreHom seedMap jetMap seedPoint jetPoint from ProximityPrize.SubmissionLower.Fast069
open private seed_chart toJet_C toJet_y toJet_v toJet_seed jetCoordinates fractionCoordinates
  generic_C generic_Y generic_V seedGeneric_C from ProximityPrize.SubmissionLower.Fast069
def surfaceOf (I : Ideal Ambient) (hI : I.IsPrime) : Surface :=
  ⟨I.comap toJet, hI.comap _⟩
theorem on_surface {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} (hI : I.IsPrime) {γ : P0.K} (hm : OnParent F I γ) :
    P0_10.MarkOn M F (surfaceOf I hI) γ := by
  intro P hP
  apply RingHom.mem_ker.mpr
  change K1_14.jetAt P (M.label γ) (F.scalar γ) = 0
  rw [← eval_toJet]
  exact RingHom.mem_ker.mp (hm hP)
theorem surface_pass {w : ℤ} {rows : Banks} {i : Fin 2}
    {pair : P0_10.BufferedPair w rows i} {I : Ideal Ambient}
    (hI : I.IsPrime) (ht : PairPass pair I) :
    P0_10R.SurfacePass pair (surfaceOf I hI) := by
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro f hirr hdeg hP hQ hmem g a hclear
  exact ht.2.2 f hirr hdeg hP hQ hmem g a hclear
private theorem fixed_chart (a b : SeedClosure) :
    (genericJetPoint a b).comp (toJet.comp fixedEmbedding) =
      seedGeneric.comp jetCoordinates.symm.toRingHom := by
  have hV : ((genericJetPoint a b).comp (toJet.comp fixedEmbedding)) (Polynomial.X (R := FX[X])) =
      (seedGeneric.comp jetCoordinates.symm.toRingHom) Polynomial.X := by
    simp [fixedEmbedding, generic_V, toJet_v, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hV
  have hY : (((genericJetPoint a b).comp (toJet.comp fixedEmbedding)).comp C)
      (Polynomial.X (R := FX)) =
      ((seedGeneric.comp jetCoordinates.symm.toRingHom).comp C) Polynomial.X := by
    simp [fixedEmbedding, generic_Y, toJet_y, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hY
  ext x
  simp [fixedEmbedding, generic_C, toJet_C, genericJetPoint, seedGeneric_C]
private theorem surface_height {I : Ideal Ambient} (hI : I.IsPrime) (hh : I.height = 2) :
    (surfaceOf I hI).asIdeal.height = 2 := by
  change (I.comap toJet).height = 2
  rw [toJet_equiv]
  exact (ambientToJet.symm.height_comap I).trans hh
private theorem seed_side_of_active {I : Ideal Ambient} (hI : Active I) :
    ∃ y v, K1_14_3.OnSeedFibre (surfaceOf I hI.prime) y v ∧
      IsSeparable SeedField y ∧ IsSeparable SeedField v := by
  obtain ⟨f, hf, hsep⟩ := @fibreHom mapGenericSeed _ seedMap I hI.prime
    hI.seed_finite hI.seed_size.1 hI.seed_size.2
  refine ⟨f (MvPolynomial.X 0), f (MvPolynomial.X 1), ?_, hsep _, hsep _⟩
  unfold K1_14_3.OnSeedFibre
  rw [← seed_chart, ← RingHom.comap_ker, seedPoint, hf]
  rfl
private theorem jet_side_transport {I : Ideal Ambient} (hI : I.IsPrime)
    (a b : SeedClosure) (hjker : RingHom.ker (genericJetPoint a b) = I)
    (ha : IsSeparable SeedField a) (hb : IsSeparable SeedField b) :
    ∃ g : Jet →+* JetClosure,
      g.comp fixedEmbedding = jetGeneric ∧ RingHom.ker g = (surfaceOf I hI).asIdeal ∧
      ∀ i : Fin 2, IsSeparable JetField (g (C (C (MvPolynomial.X i)))) := by
  let e := fractionCoordinates.symm
  let top : JetField →+* JetClosure := algebraMap JetField JetClosure
  let : Algebra SeedField JetClosure := (top.comp e.toRingHom).toAlgebra
  let l : SeedClosure →ₐ[SeedField] JetClosure :=
    IsAlgClosed.lift (R := SeedField) (S := SeedClosure) (M := JetClosure)
  let F := l.toRingHom.comp ((genericJetPoint a b).comp toJet)
  have hscalar (x : SeedField) :
      l (algebraMap SeedField SeedClosure x) = algebraMap JetField JetClosure (e x) := by
    exact l.commutes x
  refine ⟨F, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change l ((genericJetPoint a b).comp (toJet.comp fixedEmbedding) x) = _
    rw [fixed_chart, RingHom.comp_apply]
    change l (algebraMap SeedField SeedClosure (algebraMap Seeds SeedField
      (jetCoordinates.symm x))) = _
    rw [hscalar]
    change top (e (algebraMap Seeds SeedField (jetCoordinates.symm x))) =
      top (algebraMap JetPlane JetField x)
    apply congrArg top
    apply fractionCoordinates.injective
    rw [RingEquiv.apply_symm_apply]
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (A := JetPlane)
      (K := JetField) (B := Seeds) (L := SeedField) jetCoordinates.symm x).symm
  · change RingHom.ker (l.toRingHom.comp ((genericJetPoint a b).comp toJet)) = _
    rw [RingHom.ker_comp_of_injective _ l.injective, ← RingHom.comap_ker, hjker]
    rfl
  · have hs (x : SeedClosure) (hx : IsSeparable SeedField x) : IsSeparable JetField (l x) := by
      have hx' : (minpoly SeedField x).Separable := hx
      apply (hx'.map (f := e.toRingHom)).of_dvd
      apply minpoly.dvd
      rw [aeval_def, Polynomial.eval₂_map]
      change (minpoly SeedField x).eval₂ (algebraMap SeedField JetClosure) (l x) = 0
      rw [← aeval_def, aeval_algHom_apply l, minpoly.aeval, map_zero]
    intro i
    fin_cases i
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 0))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs a ha
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 1))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs b hb
theorem parent_of_dual {I : Ideal Ambient} (hI : Active I) (hh : I.height = 2) (hj : dual I) :
    Parent (surfaceOf I hI.prime) := by
  obtain ⟨g, hg, hsep⟩ := @fibreHom mapGenericJets _ jetMap I hI.prime hI.jet_finite hj hI.jet_lt
  have hker : RingHom.ker (genericJetPoint (g (MvPolynomial.X 0)) (g (MvPolynomial.X 1))) = I := by
    rw [jetPoint, hg]
  exact ⟨surface_height hI.prime hh, seed_side_of_active hI,
    jet_side_transport hI.prime _ _ hker (hsep _) (hsep _)⟩
private theorem terminal_order {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows)
    (hlo : lowCutoff + 1 ≤ M.overhead) (hhi : M.overhead ≤ 3554)
    {q : Surface} (hq : Parent q) (hv : P0_10.BankVanishes rows (fullShape M.overhead) q)
    {s : Shape} (hs : s ∈ scheduled M.overhead) (hm : s.m = (fullShape M.overhead).m)
    (hb : s.B = (fullShape M.overhead).B) (hj : s.J = (fullShape M.overhead).J)
    (hu : s.U ≤ (fullShape M.overhead).U) {W : ℕ} (hw : W < s.m * agreement)
    {P : Jet} (hp : P ∈ rows s W) : OrderAt q P (contactPower M.overhead s W) := by
  let h := M.overhead.toNat
  apply K1_14_3R_1.proof _ _ _ hq
  · have hchar : s.m * agreement < p := by rw [hm, full_bridge _ hhi]; decide
    have := Nat.div_le_self (fullCutoff s - W) (2*h)
    change 1 + (fullCutoff s - W) / (2*h) < p
    unfold fullCutoff at *
    omega
  intro a b hab
  change a + b < 1 + (fullCutoff s - W) / (2*h) at hab
  have hh : 0 < 2*h := by
    change 2481 ≤ M.overhead at hlo
    dsimp only [h]
    omega
  have hcost := (Nat.le_div_iff_mul_le hh).mp
    (show a+b ≤ (fullCutoff s - W) / (2*h) by omega)
  rw [Nat.mul_comm (a+b), Nat.mul_add] at hcost
  have hle : W + 2*h*a + 2*h*b ≤ fullCutoff (fullShape M.overhead) := by
    unfold fullCutoff at *
    rw [hm] at hcost hw
    omega
  have hA := src.shift s hs W P hp 0 a
  have hB := src.shift s hs _ _ hA 1 b
  exact hv _ (src.nested s hs _ (full_scheduled _) hm hb hj hu _ _ hle hB)
theorem terminal_product {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows)
    (hlo : lowCutoff + 1 ≤ M.overhead) (hhi : M.overhead ≤ 3554)
    (Q : Finset Surface) (hne : Q.Nonempty)
    (hQ : ∀ q ∈ Q, Parent q)
    (hv : ∀ q ∈ Q, P0_10.BankVanishes rows (fullShape M.overhead) q) :
    ∃ f : Equation, ProjectedProduct Q f ∧ FullDivisibility M.overhead rows f ∧
      P0_10.TerminalDivisibility M.overhead rows f := by
  obtain ⟨f, hf⟩ := K1_14_3_7.proof Q hne hQ
  refine ⟨f, hf, ?_, ?_⟩
  · intro W hW P hP hn
    exact hf.divides_leading P _ hn
      (fun q hq => terminal_order src hlo hhi (hQ q hq) (hv q hq) (full_scheduled _)
        rfl rfl rfl le_rfl hW hP)
  · let s := terminalShape M.overhead
    have hs : s ∈ scheduled M.overhead := by simp [s, scheduled]
    have hu : s.U ≤ (fullShape M.overhead).U := by
      simp only [s, terminalShape, P0_10.band, ite_eq_left hhi, full_bridge _ hhi]
      decide
    intro W hW P hP hn
    suffices horder : ∀ q ∈ Q, OrderAt q P (contactPower M.overhead s W) by
      exact hf.divides_leading P _ hn horder
    intro q hq
    exact terminal_order src hlo hhi (hQ q hq) (hv q hq) hs rfl rfl rfl hu hW hP
end
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
private theorem donor_2_1 : K1_14_2_2_7_2.c1 :=
  K1_14_2_2_7_2_1.proof
private theorem donor_2_2_1 : K1_14_2_2_7_2_2.c1 :=
  K1_14_2_2_7_2_2_1.proof
private theorem donor_2_2_2 : K1_14_2_2_7_2_2.c2 :=
  K1_14_2_2_7_2_2_2.proof
private theorem donor_2_2_3 : K1_14_2_2_7_2_2.c3 :=
  K1_14_2_2_7_2_2_3.proof
private theorem donor_2_2 : K1_14_2_2_7_2.c2 :=
  K1_14_2_2_7_2_2.of_children donor_2_2_1 donor_2_2_2 donor_2_2_3
private theorem donor_2_3 : K1_14_2_2_7_2.c3 :=
  K1_14_2_2_7_2_3.proof
private theorem donor_2_4 : K1_14_2_2_7_2.c4 :=
  K1_14_2_2_7_2_4.proof
private theorem donor_2_5 : K1_14_2_2_7_2.c5 :=
  K1_14_2_2_7_2_5.proof
theorem cut_seed_mass : K1_14_2_2_7.c2 :=
  K1_14_2_2_7_2.of_children donor_2_1 donor_2_2 donor_2_3 donor_2_4 donor_2_5
private theorem donor_3_1 : K1_14_2_2_7_3.c1 :=
  K1_14_2_2_7_3_1.proof
private theorem donor_3_2 : K1_14_2_2_7_3.c2 :=
  K1_14_2_2_7_3_2.proof
private theorem donor_3_3_1_1 : K1_14_2_2_7_3_3_1.c1 :=
  K1_14_2_2_7_3_3_1_1.proof
private theorem donor_3_3_1_2 : K1_14_2_2_7_3_3_1.c2 :=
  K1_14_2_2_7_3_3_1_2.proof
private theorem donor_3_3_1_3 : K1_14_2_2_7_3_3_1.c3 :=
  K1_14_2_2_7_3_3_1_3.proof
private theorem donor_3_3_1_4 : K1_14_2_2_7_3_3_1.c4 :=
  K1_14_2_2_7_3_3_1_4.proof
private theorem donor_3_3_1 : K1_14_2_2_7_3_3.c1 :=
  K1_14_2_2_7_3_3_1.of_children donor_3_3_1_1 donor_3_3_1_2 donor_3_3_1_3 donor_3_3_1_4
private theorem donor_3_3_2 : K1_14_2_2_7_3_3.c2 :=
  K1_14_2_2_7_3_3_2.proof
private theorem donor_3_3 : K1_14_2_2_7_3.c3 :=
  K1_14_2_2_7_3_3.of_children donor_3_3_1 donor_3_3_2
theorem cut_ordinate_mass : K1_14_2_2_7.c3 :=
  K1_14_2_2_7_3.of_children donor_3_1 donor_3_2 donor_3_3
private theorem donor_4_1 : K1_14_2_2_7_4.c1 :=
  K1_14_2_2_7_4_1.proof
private theorem donor_4_2 : K1_14_2_2_7_4.c2 :=
  K1_14_2_2_7_4_2.proof
private theorem donor_4_3 : K1_14_2_2_7_4.c3 :=
  K1_14_2_2_7_4_3.proof
private theorem donor_4_4_1 : K1_14_2_2_7_4_4.c1 :=
  K1_14_2_2_7_4_4_1.proof
private theorem donor_4_4_2 : K1_14_2_2_7_4_4.c2 :=
  K1_14_2_2_7_4_4_2.proof
private theorem donor_4_4_3 : K1_14_2_2_7_4_4.c3 :=
  K1_14_2_2_7_4_4_3.proof
private theorem donor_4_4_4 : K1_14_2_2_7_4_4.c4 :=
  K1_14_2_2_7_4_4_4.proof
private theorem donor_4_4_5 : K1_14_2_2_7_4_4.c5 :=
  K1_14_2_2_7_4_4_5.proof
private theorem donor_4_4_6 : K1_14_2_2_7_4_4.c6 :=
  K1_14_2_2_7_4_4_6.proof
private theorem donor_4_4_7_1 : K1_14_2_2_7_4_4_7.c1 :=
  K1_14_2_2_7_4_4_7_1.proof
private theorem donor_4_4_7_2 : K1_14_2_2_7_4_4_7.c2 :=
  K1_14_2_2_7_4_4_7_2.proof
private theorem donor_4_4_7 : K1_14_2_2_7_4_4.c7 :=
  K1_14_2_2_7_4_4_7.of_children donor_4_4_7_1 donor_4_4_7_2
private theorem donor_4_4_8 : K1_14_2_2_7_4_4.c8 :=
  K1_14_2_2_7_4_4_8.proof
private theorem donor_4_4 : K1_14_2_2_7_4.c4 :=
  K1_14_2_2_7_4_4.of_children
    donor_4_4_1 donor_4_4_2 donor_4_4_3 donor_4_4_4 donor_4_4_5 donor_4_4_6 donor_4_4_7 donor_4_4_8
theorem cut_constant_count : K1_14_2_2_7.c4 :=
  K1_14_2_2_7_4.of_children donor_4_1 donor_4_2 donor_4_3 donor_4_4
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
noncomputable section
open P0 (AnchorModel AnchoredFamily K)
open K1_14 (Jet Shape jetAt seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField JetSeedSection
  JetYSection)
open K1_14_2_2 (Active CutCover RowCaps sectionDegree weight dot joinCuts joinCuts_cost
  sum_dot emptyCut mass)
open K1_14_2_2_7
open private seed_value_eq from ProximityPrize.SubmissionLower.Fast052
open scoped Classical BigOperators
private theorem mark_on_cut {I : Ideal Ambient} {P : Jet} {z : K} {S : Polynomial K}
    (hI : OnJet I z S) (hzero : jetAt P z S = 0) :
    ∃ Q ∈ cutComponents I P, OnJet Q z S := by
  let e := jetMarkHom z S
  have hle : I ⊔ Ideal.span {toJet P} ≤ RingHom.ker e := by
    apply sup_le hI
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans hzero))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, hQ, hmark⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr hQ, hmark⟩
theorem proper_cut {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (s : Shape) {I : Ideal Ambient} {P : Jet} (hs : s.J ≤ s.B) (hI : Active I)
    (hcaps : RowCaps P s) (hprop : toJet P ∉ I) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 →
        γ ∈ C.direct ∨ ∃ Q ∈ C.curves, OnParent F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnParent F Q)
  let direct := (constantComponents I P).biUnion marked
  have hcard : direct.card ≤ (constantComponents I P).card := by
    have hsingle (Q : Ideal Ambient) (hQ : Q ∈ constantComponents I P) :
        (marked Q).card ≤ 1 := by
      obtain ⟨hcomp, hconst⟩ := Finset.mem_filter.mp hQ
      let _ : Q.IsPrime := (cutComponent_curve hI hprop hcomp).1
      apply Finset.card_le_one.mpr
      intro γ hγ δ hδ
      apply sub_left_inj.mp
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq hconst (Finset.mem_filter.mp hγ).2).trans
        (seed_value_eq hconst (Finset.mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q ∈ constantComponents I P, (marked Q).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ constantComponents I P, 1 := Finset.sum_le_sum hsingle
      _ = _ := by simp
  let C : CutCover :=
    ⟨direct, movingComponents I P, by
      intro Q hQ
      obtain ⟨hcomp, hmov⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hp, hdim⟩ := cutComponent_curve hI hprop hcomp
      exact ⟨hp, hdim, K1_14_2_2_7_1.proof Q hp hdim hmov⟩⟩
  refine ⟨C, ?_, ?_⟩
  · intro fee
    fin_cases fee
    · exact cut_seed_mass s I P hs hI hcaps hprop
    · exact cut_ordinate_mass s I P hs hI hcaps hprop
    · exact hcard.trans (cut_constant_count s I P hs hI hcaps hprop)
  · intro γ hγ hmark hzero
    obtain ⟨Q, hQ, hQmark⟩ := mark_on_cut hmark hzero
    by_cases ht : ConstantSeed Q
    · exact Or.inl (Finset.mem_biUnion.mpr
        ⟨Q, Finset.mem_filter.mpr ⟨hQ, ht⟩, Finset.mem_filter.mpr ⟨hγ, hQmark⟩⟩)
    · exact Or.inr ⟨Q, Finset.mem_filter.mpr ⟨hQ, ht⟩, hQmark⟩
theorem combined_cuts {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (A : Finset (Ideal Ambient)) (s : Shape) (hs : s.J ≤ s.B)
    (ha : ∀ I ∈ A, Active I)
    (hcut : ∀ I ∈ A, ∃ P : Jet, RowCaps P s ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (mass A)) ∧
      ∀ γ ∈ Γ, (∃ I ∈ A, OnParent F I γ) →
        γ ∈ C.direct ∨ ∃ I ∈ C.curves, OnParent F I γ := by
  have hex (I : Ideal Ambient) (hI : I ∈ A) :
      ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
        ∀ γ ∈ Γ, OnParent F I γ → γ ∈ C.direct ∨ ∃ Q ∈ C.curves, OnParent F Q γ := by
    obtain ⟨P, hp, hprop, hzero⟩ := hcut I hI
    obtain ⟨C, hc, hmarks⟩ := proper_cut F s hs (ha I hI) hp hprop
    exact ⟨C, hc, fun γ hγ hm => hmarks γ hγ hm (hzero γ hγ hm)⟩
  let C (I : Ideal Ambient) : CutCover :=
    if hI : I ∈ A then Classical.choose (hex I hI) else emptyCut
  have hC (I : Ideal Ambient) (hI : I ∈ A) :
      (∀ fee, (C I).cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent F I γ → γ ∈ (C I).direct ∨ ∃ Q ∈ (C I).curves, OnParent F Q γ := by
    simpa only [C, dite_eq_left hI] using Classical.choose_spec (hex I hI)
  refine ⟨joinCuts A C, ?_, ?_⟩
  · intro fee
    calc
      _ ≤ ∑ I ∈ A, (C I).cost fee := joinCuts_cost A C fee
      _ ≤ ∑ I ∈ A, dot (weight s fee) (sectionDegree I) :=
        Finset.sum_le_sum (fun I hI => (hC I hI).1 fee)
      _ = _ := sum_dot _ _
  · rintro γ hγ ⟨I, hI, hmark⟩
    rcases (hC I hI).2 γ hγ hmark with hd | ⟨Q, hQ, hmark⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨I, hI, hd⟩)
    · exact Or.inr ⟨Q, Finset.mem_biUnion.mpr ⟨I, hI, hQ⟩, hmark⟩
end
end P0_10R.Bridge
end
section
set_option maxRecDepth 4000
namespace P0_10R.Bridge
noncomputable section
open P0 (AnchorModel AnchoredFamily K I p node)
open K1_13 K1_13_5
open K1_13_5_3 hiding exponent exponent_sufficient chartTotal chartTop
open K1_14_2 (endpointDegree)
open K1_14_2_5
open Polynomial PolynomialDifferential
open scoped BigOperators
open private nodeCut nodeCut_vanishes nodeCut_capped from ProximityPrize.SubmissionLower.Fast070
theorem bridge_word {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hw : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ) :
    P0_10.FixedWord M.word T F.scalar endpointDegree := by
  refine ⟨F.distinct.mono hT, ?_, ?_⟩
  · intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with hz | hd
    · simp [hz]
    · have hc : ((F.scalar γ).natDegree : ℤ) ≤ (endpointDegree : ℤ) := by
        change ((F.scalar γ).natDegree : ℤ) ≤ 134625
        change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hd
        omega
      exact_mod_cast hc
  · intro γ hγ
    let mark := F.mark γ (hT hγ)
    exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
private theorem regular_count {w T s} (h : P0_10.FixedWord w T s 134625) (f : Row 2)
    (hf : Irreducible f) (hp : 0 < f.degreeOf 1) {B J : ℕ} (hB : f.totalDegree ≤ B)
    (hJ : f.degreeOf 1 ≤ J) (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    45592 * T.card ≤ 81927 * MvPolynomial.cappedDegreeMixedVolume f.totalDegree
      (f.degreeOf 1) (chartTotal B) (chartTop B J) + 45592 := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := by
    intro γ hγ η hη heq
    exact h.distinct hγ hη (Polynomial.map_injective embed embed.injective (marked_injective heq))
  have hxg : ∀ γ ∈ T, MvPolynomial.aeval (x γ) (plane f) = 0 := by
    intro γ hγ
    change MvPolynomial.aeval (marked (extend (s γ))) (plane f) = 0
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hxe (γ : K) (hγ : γ ∈ T) (i : I) :
      MvPolynomial.aeval (x γ) (nodeCut w f i) = 0 ↔ (s γ).eval (node i) = w i :=
    nodeCut_vanishes (hreg γ hγ) (h.degree γ hγ) i
  apply P0_10.section_capacity h (by decide)
  rintro i ⟨η, hη, hmiss⟩
  have hproper : nodeCut w f i ∉ Ideal.span {plane f} := by
    intro hcut
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hcut
    exact hmiss ((hxe η hη i).mp (by rw [hq, map_mul, hxg η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hcap := capped_cut_card (show 0 < chartTotal B by simp [chartTotal])
    (show 0 < chartTop B J by simp [chartTop, chartTotal, K1_14_2.endpointDegree])
    (plane_ne_zero hf.ne_zero) (plane_prime hf hp)
    hplane
    (nodeCut_capped w f hB hJ (hp.trans_le hJ) i) hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hγ
      exact ⟨hxg γ hm, (hxe γ hm i).mpr hh⟩)
  rw [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hcap
  exact hcap
theorem fixed_count {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hw : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ)
    (B J : ℕ) (hB : 2 ≤ B) (hchar : B < p) (hJB : J ≤ B)
    (hG : ∃ G : K1_14_2.ODE, K1_14_2_2.ODECaps G B J ∧
      ∀ γ ∈ T, K1_14_2.fixedAt G (F.scalar γ) = 0) :
    T.card ≤ fixedPrice B J := by
  classical
  obtain ⟨G, ⟨hG0, hGJ, hGB⟩, hg⟩ := hG
  obtain ⟨q, hq, hqb, hqj, hsolve⟩ := clear_equation G hG0 hGJ hGB
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ := factor_cover q hq hB hchar hqb hqj
  have word := bridge_word M F hw T hT
  let ordinary := T.filter fun γ => R.eval (extend (F.scalar γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (F.scalar γ))
  have ordinary_bound : ordinary.card ≤ B * (B - 1) := by
    let s (γ : K) := extend (F.scalar γ)
    have hinj : Set.InjOn s (ordinary : Set K) := fun _ ha _ hb he =>
      word.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hroot : (ordinary.image s).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hroot
    exact hroot.trans hRd
  have hs : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hg γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  let a := chartTotal B
  let v := chartTop B J
  have hn : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (g : Row 2) (hg : g ∈ A) :
      45592 * (reg g).card ≤ 81927 * (g.totalDegree * v + g.degreeOf 1 * (a - v)) + 45592 := by
    have hb := (Finset.single_le_sum (fun x _ => Nat.zero_le x.totalDegree) hg).trans hAb
    have hj := (Finset.single_le_sum (fun x _ => Nat.zero_le (x.degreeOf 1)) hg).trans hAj
    exact regular_count (word.mono (Finset.filter_subset _ _)) g (hA g hg).1 (hA g hg).2
      hb hj (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hr : 45592 * (∑ g ∈ A, (reg g).card) ≤
      81927 * (B*v + J*(a-v)) + 45592 * B := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, smul_eq_mul]
    have hn' := Nat.mul_le_mul_left 45592 hn
    rw [Nat.mul_comm 45592 A.card] at hn'
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add
      (Nat.mul_le_mul_right _ hAb) (Nat.mul_le_mul_right _ hAj))) hn'
  have hcost : B*v + J*(a-v) = (B-J)*v + J*a := by
    have hva : v ≤ a := min_le_left _ _
    calc
      B*v + J*(a-v) = ((B-J)+J)*v + J*(a-v) := by rw [Nat.sub_add_cancel hJB]
      _ = (B-J)*v + J*((a-v)+v) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hva]
  have hbox : B * (B - 1) + B = B * B := by
    calc
      _ = B * ((B - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ B)]
  let num := 81927 * ((B-J)*v + J*a)
  have htotal := Nat.mul_le_mul_left 45592 hs
  rw [Nat.mul_add] at htotal
  have ho := Nat.mul_le_mul_left 45592 ordinary_bound
  rw [hcost] at hr
  have hcount : 45592 * T.card ≤ num + 45592 * (B*B) := by
    rw [← hbox, Nat.mul_add]
    dsimp only [num]
    omega
  have hmod := Nat.mod_add_div num 45592
  have hlt := Nat.mod_lt num (by decide : 0 < 45592)
  have hround : T.card ≤ num / 45592 + B*B := by omega
  change T.card ≤ (num + 45592 - 1) / 45592 + B^2
  rw [pow_two]
  exact hround.trans (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) _)
end
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
noncomputable section
open P0 (AnchorModel AnchoredFamily K)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (Active ODECaps mass sectionDegree fixedOn eval_fixed)
open K1_14_2_2_5 (product_caps product_fixedOn)
open private parent_caps from ProximityPrize.SubmissionLower.Fast052
open scoped BigOperators Classical
theorem rank_equation (S : Finset (Ideal Ambient))
    (hS : ∀ I ∈ S, Active I ∧ ¬ K1_14_2_2.dual I)
    (hord : mass S 1 ≤ 47668) (hmix : mass S 2 ≤ 264904) :
    ∃ G : ODE, ODECaps G 264904 47668 ∧ ∀ I ∈ S, fixedOn G I := by
  have hchoose (I : Ideal Ambient) :
      ∃ G : ODE, I ∈ S → ODECaps G (sectionDegree I 2) (sectionDegree I 1) ∧ fixedOn G I := by
    by_cases hI : I ∈ S
    · obtain ⟨G, hg⟩ := parent_caps K1_14_2_2_5_1.proof K1_14_2_2_5_2.proof
        (hS I hI).1 (hS I hI).2
      exact ⟨G, fun _ => hg⟩
    · exact ⟨1, fun h => (hI h).elim⟩
  choose G hG using hchoose
  have hp : ODECaps (∏ I ∈ S, G I) (mass S 2) (mass S 1) :=
    product_caps S G (fun I => sectionDegree I 2) (fun I => sectionDegree I 1)
      (fun I hI => (hG I hI).1)
  exact ⟨∏ I ∈ S, G I, ⟨hp.1, hp.2.1.trans hord, fun j i h => (hp.2.2 j i h).trans hmix⟩,
    fun I hI => product_fixedOn hI G (hG I hI).2⟩
theorem fixed_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} {G : ODE} {γ : K} (hm : OnParent F I γ) (hG : fixedOn G I) :
    fixedAt G (F.scalar γ) = 0 := by
  simpa only [eval_fixed] using RingHom.mem_ker.mp (hm hG)
end
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
noncomputable section
open K1_14_2 (Ambient)
open K1_14_2_2 (Fits mass dot weight dot_mono dot_mass_sdiff mass_mono)
open scoped BigOperators
private def firstWeight (fee : Fin 3) := weight stageFiveShape fee
private def lastWeight (fee : Fin 3) := weight terminalFullShape fee
private def increment (fee : Fin 3) (j : Fin 4) := lastWeight fee j - firstWeight fee j
private theorem weights_increase (fee : Fin 3) (j : Fin 4) :
    firstWeight fee j ≤ lastWeight fee j := by
  fin_cases fee <;> fin_cases j <;> decide
private theorem dot_split (fee : Fin 3) (v : Fin 4 → ℕ) :
    dot (lastWeight fee) v = dot (firstWeight fee) v + dot (increment fee) v := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Nat.add_mul, show firstWeight fee j + increment fee j =
    lastWeight fee j from Nat.add_sub_of_le (weights_increase fee j)]
private theorem telescope (A B U V : Finset (Ideal Ambient)) (hB : B ⊆ A)
    (hU : U ⊆ A \ B) (hV : V ⊆ B) (fee : Fin 3) :
    dot (firstWeight fee) (mass U) + dot (lastWeight fee) (mass V) ≤
      dot (firstWeight fee) (mass A) + dot (increment fee) (mass B) := by
  calc
    _ ≤ dot (firstWeight fee) (mass (A \ B)) + dot (lastWeight fee) (mass B) :=
      Nat.add_le_add (dot_mono _ _ _ (mass_mono hU)) (dot_mono _ _ _ (mass_mono hV))
    _ = _ := by
      rw [dot_split, ← Nat.add_assoc, dot_mass_sdiff hB]
private theorem dot4 (w v : Fin 4 → ℕ) :
    dot w v = w 0*v 0 + (w 1*v 1 + (w 2*v 2 + (w 3*v 3 + 0))) := by
  simp only [dot, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl
private theorem first_seed_weights : firstWeight 0 = ![7726,224,58,0] := by
  funext i
  fin_cases i <;> rfl
private theorem seed_increments : increment 0 = ![133745,908,232,0] := by
  funext i
  fin_cases i <;> rfl
private theorem first_ordinate_weights : firstWeight 1 = ![0,7726,0,58] := by
  funext i
  fin_cases i <;> rfl
private theorem ordinate_increments : increment 1 = ![0,133745,0,232] := by
  funext i
  fin_cases i <;> rfl
private theorem seed_ledger :
    dot (firstWeight 0) initialCap + dot (increment 0) reserveFiveCap ≤ lossSeedCap := by
  rw [first_seed_weights, seed_increments, dot4, dot4]
  decide
private theorem ordinate_ledger :
    dot (firstWeight 1) initialCap + dot (increment 1) reserveFiveCap ≤ lossYCap := by
  rw [first_ordinate_weights, ordinate_increments, dot4, dot4]
  decide
private theorem constant_ledger :
    dot (lastWeight 2) (![5548,125234,577116,initialE₀] : Fin 4 → ℕ) ≤ constantFee := by
  rw [dot4]
  change 0*5548 + (0*125234 + (141471*577116 + (1422*6242936 + 0))) ≤ 90522632628
  decide
theorem loss_bounds (A B U V : Finset (Ideal Ambient)) (hB : B ⊆ A)
    (hU : U ⊆ A \ B) (hV : V ⊆ B) (hA : Fits A initialCap) (hBc : Fits B reserveFiveCap) :
    dot (weight stageFiveShape 0) (mass U) + dot (weight terminalFullShape 0) (mass V) ≤ lossSeedCap ∧
    dot (weight stageFiveShape 1) (mass U) + dot (weight terminalFullShape 1) (mass V) ≤ lossYCap ∧
    dot (weight stageFiveShape 2) (mass U) + dot (weight terminalFullShape 2) (mass V) ≤ constantFee := by
  have hpay (fee : Fin 3) :
      dot (firstWeight fee) (mass U) + dot (lastWeight fee) (mass V) ≤
        dot (firstWeight fee) initialCap + dot (increment fee) reserveFiveCap :=
    (telescope A B U V hB hU hV fee).trans
      (Nat.add_le_add (dot_mono _ _ _ hA) (dot_mono _ _ _ hBc))
  refine ⟨(hpay 0).trans seed_ledger, (hpay 1).trans ordinate_ledger, ?_⟩
  have hV' : V ⊆ B := hV
  have hconst : mass A 3 ≤ initialE₀ := (hA 3).trans (by decide)
  have hcoarse : ∀ j : Fin 4, mass A j ≤ (![5548,125234,577116,initialE₀] : Fin 4 → ℕ) j := by
    intro j
    fin_cases j
    · exact hA 0
    · exact hA 1
    · exact hA 2
    · exact hconst
  change dot (firstWeight 2) (mass U) + dot (lastWeight 2) (mass V) ≤ constantFee
  calc
    _ ≤ dot (lastWeight 2) (mass (A \ B)) + dot (lastWeight 2) (mass B) := by
      apply Nat.add_le_add _ (dot_mono _ _ _ (mass_mono hV'))
      apply le_trans _ (dot_mono _ _ _ (mass_mono hU))
      exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right _ (weights_increase 2 j))
    _ = dot (lastWeight 2) (mass A) := dot_mass_sdiff hB _
    _ ≤ _ := (dot_mono _ _ _ hcoarse).trans constant_ledger
private theorem fixed_price_row (B J a v mixed num quotient price : ℕ)
    (ha : 1 + 269247 * (B - 1) = a) (hv : min a (269247 * (J - 1) + 134625) = v)
    (hm : (B - J) * v + J * a = mixed) (hn : 81927 * mixed + 45591 = num)
    (hq : num / 45592 = quotient) (hprice : quotient + B ^ 2 = price) :
    fixedPrice B J = price := by
  change (81927 * ((B - J) * min (1 + 269247 * (B - 1)) (269247 * (J - 1) + 134625) +
    J * (1 + 269247 * (B - 1))) + 45591) / 45592 + B ^ 2 = price
  rw [ha, hv, hm, hn, hq, hprice]
private theorem rank_price : fixedPrice 264904 47668 = 11119599951001550 := by
  apply fixed_price_row 264904 47668 71324338042 12834331374
    6187967356148320 506961601587163458231 11119529776872334 <;> decide
private theorem free_zero_price : fixedPrice 76 17 = 1087888923 := by
  apply fixed_price_row 76 17 20193526 4442577
    605401985 49598768470686 1087883147 <;> decide
private theorem moving_zero_price : fixedPrice 191 39 = 6416538530 := by
  apply fixed_price_row 191 39 51156931 10366011
    3570753981 292541161446978 6416502049 <;> decide
private theorem free_five_price : fixedPrice 113 25 = 2397855140 := by
  apply fixed_price_row 113 25 30155665 6596553
    1334388289 109322429398494 2397842371 <;> decide
private theorem moving_five_price : fixedPrice 282 58 = 14117157806 := by
  apply fixed_price_row 282 58 75658408 15481704
    7856089360 643625833042311 14117078282 <;> decide
private theorem terminal_price : fixedPrice 1422 290 = 357938500294 := by
  apply fixed_price_row 1422 290 382599988 77947008
    199190009576 16319039914578543 357936478210 <;> decide
private theorem initial_price : initialFee = 1242504417584112 := by decide
theorem prefix_ledger (w : ℤ) (hw : w ≤ 3554) :
    initialFee + fixedPrice 76 17 + fixedPrice 191 39 +
      fixedPrice 113 25 + fixedPrice 282 58 + fixedPrice 264904 47668 +
      constantFee + curveFee ≤ P0.highPrefix w := by
  let spent := initialFee + fixedPrice 76 17 + fixedPrice 191 39 +
    fixedPrice 113 25 + fixedPrice 282 58 + fixedPrice 264904 47668 +
    constantFee + curveFee
  change spent ≤ P0.highPrefix w
  calc
    _ ≤ spent + fixedPrice 1422 290 + (P0.p+1)*(1601+7726+141471) :=
      (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    _ = _ := by
      unfold spent
      rw [initial_price, free_zero_price, moving_zero_price, free_five_price, moving_five_price,
        rank_price, terminal_price, P0.highPrefix, ite_eq_left hw]
      have hcontents : (P0.p+1)*(1601+7726+141471) = 321306268834332 := by decide
      rw [hcontents]
      exact (show
        1242504417584112 + 1087888923 + 6416538530 + 2397855140 + 14117157806 +
          11119599951001550 + 90522632628 + 59646678368515881 + 357938500294 +
          321306268834332 = 72330561486509196 by decide)
end
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
private theorem donor_1_1_1 : K1_14_2_4_1_1.c1 :=
  K1_14_2_4_1_1_1.proof
private theorem donor_1_1_2 : K1_14_2_4_1_1.c2 :=
  K1_14_2_4_1_1_2.proof
private theorem donor_1_1 : K1_14_2_4_1.c1 :=
  K1_14_2_4_1_1.of_children donor_1_1_1 donor_1_1_2
private theorem donor_1_2_1 : K1_14_2_4_1_2.c1 :=
  K1_14_2_4_1_2_1.proof
private theorem donor_1_2_2 : K1_14_2_4_1_2.c2 :=
  K1_14_2_4_1_2_2.proof
private theorem donor_1_2 : K1_14_2_4_1.c2 :=
  K1_14_2_4_1_2.of_children donor_1_2_1 donor_1_2_2
private theorem donor_1_3_1 : K1_14_2_4_1_3.c1 :=
  K1_14_2_4_1_3_1.proof
private theorem donor_1_3_2_1 : K1_14_2_4_1_3_2.c1 :=
  K1_14_2_4_1_3_2_1.proof
private theorem donor_1_3_2_2 : K1_14_2_4_1_3_2.c2 :=
  K1_14_2_4_1_3_2_2.proof
private theorem donor_1_3_2 : K1_14_2_4_1_3.c2 :=
  K1_14_2_4_1_3_2.of_children donor_1_3_2_1 donor_1_3_2_2
private theorem donor_1_3_3_1 : K1_14_2_4_1_3_3.c1 :=
  K1_14_2_4_1_3_3_1.proof
private theorem donor_1_3_3_2 : K1_14_2_4_1_3_3.c2 :=
  K1_14_2_4_1_3_3_2.proof
private theorem donor_1_3_3_3 : K1_14_2_4_1_3_3.c3 :=
  K1_14_2_4_1_3_3_3.proof
private theorem donor_1_3_3 : K1_14_2_4_1_3.c3 :=
  K1_14_2_4_1_3_3.of_children donor_1_3_3_1 donor_1_3_3_2 donor_1_3_3_3
private theorem donor_1_3 : K1_14_2_4_1.c3 :=
  K1_14_2_4_1_3.of_children donor_1_3_1 donor_1_3_2 donor_1_3_3
private theorem donor_1_4_1 : K1_14_2_4_1_4.c1 :=
  K1_14_2_4_1_4_1.proof
private theorem donor_1_4_2 : K1_14_2_4_1_4.c2 :=
  K1_14_2_4_1_4_2.proof
private theorem donor_1_4_3 : K1_14_2_4_1_4.c3 :=
  K1_14_2_4_1_4_3.proof
private theorem donor_1_4 : K1_14_2_4_1.c4 :=
  K1_14_2_4_1_4.of_children donor_1_4_1 donor_1_4_2 donor_1_4_3
private theorem donor_1_5_1 : K1_14_2_4_1_5.c1 :=
  K1_14_2_4_1_5_1.proof
private theorem donor_1_5_2 : K1_14_2_4_1_5.c2 :=
  K1_14_2_4_1_5_2.proof
private theorem donor_1_5 : K1_14_2_4_1.c5 :=
  K1_14_2_4_1_5.of_children donor_1_5_1 donor_1_5_2
theorem root_chart : K1_14_2_4.c1 :=
  K1_14_2_4_1.of_children donor_1_1 donor_1_2 donor_1_3 donor_1_4 donor_1_5
theorem root_taylor : K1_14_2_4.c2 :=
  K1_14_2_4_2.proof
private theorem donor_3_1_1 : K1_14_2_4_3_1.c1 :=
  K1_14_2_4_3_1_1.proof
private theorem donor_3_1_2 : K1_14_2_4_3_1.c2 :=
  K1_14_2_4_3_1_2.proof
private theorem donor_3_1_P0_10RBridgeRootDonors : K1_14_2_4_3.c1 :=
  K1_14_2_4_3_1.of_children donor_3_1_1 donor_3_1_2
private theorem donor_3_2_1 : K1_14_2_4_3_2.c1 :=
  K1_14_2_4_3_2_1.proof
private theorem donor_3_2_2 : K1_14_2_4_3_2.c2 :=
  K1_14_2_4_3_2_2.proof
private theorem donor_3_2_P0_10RBridgeRootDonors : K1_14_2_4_3.c2 :=
  K1_14_2_4_3_2.of_children donor_3_2_1 donor_3_2_2
theorem root_embedding : K1_14_2_4.c3 :=
  K1_14_2_4_3.of_children donor_3_1_P0_10RBridgeRootDonors donor_3_2_P0_10RBridgeRootDonors
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
noncomputable section
open P0 (K I node p)
open K1_14 (FX L seedEmbedding)
open K1_14_2 (endpointDegree)
open K1_14_2_4 hiding specialize
open Polynomial MvPolynomial Finset
open scoped BigOperators
open private proper_section_card from ProximityPrize.SubmissionLower.Fast055
private theorem regular_count_P0_10RBridgeRoot {n U s g H w} (A : RegularChart U s g H n)
    (hw : P0_10.FixedWord w U s endpointDegree)
    (C : TaylorForms n (ordinateBound endpointDegree g) (taylorPower endpointDegree))
    (hrec : ∀ γ ∈ U, C.Recovers (A.parameter γ) (s γ)) (hdegree : c3) :
    (U.card : ℚ) ≤
      beta * ((taylorPower endpointDegree * (g * H) +
        ordinateBound endpointDegree g * H : ℕ) : ℚ) + 1 := by
  classical
  let a := ordinateBound endpointDegree g
  let b := taylorPower endpointDegree
  let D := b * (g * H) + a * H
  have ha : 0 < a := by simp [a, ordinateBound]
  have hb : 0 < b := by decide
  let P := linearIdeal a b A.source
  let M := bidegreeMap (Fin n) FX a b
  let v (γ : K) := markedPoint (A.parameter γ) (s γ)
  let point (γ : K) := monomialPoint (bidegreeExponents (Fin n) a b) (v γ)
  have hP : P.IsPrime := A.source_prime.comap M
  let _ : P.IsPrime := hP
  have hdim_eq : (affineHilbertPolynomial P).natDegree =
      (affineHilbertPolynomial A.source).natDegree :=
    natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb _
  have hdim := hdim_eq.trans_le A.source_dim
  have hdeg (h : (affineHilbertPolynomial P).natDegree = 1) : affineDegree P ≤ (D : ℚ) :=
    hdegree n a b (g * H) H ha hb A.source A.source_prime (hdim_eq.symm.trans h) A.slices
  have eval_linear (γ : K) (F : LinearRing n a b) :
      MvPolynomial.aeval (point γ) F = MvPolynomial.aeval (v γ) (M F) := by
    rw [show M = monomialMap FX (bidegreeExponents (Fin n) a b) from
      bidegreeMap_eq_monomialMap a b]
    exact aeval_monomialPoint _ _
  have hpoints (γ : K) (hγ : γ ∈ U) : point γ ∈ zeroLocus FX P := by
    intro F hF
    rw [eval_linear]
    exact A.lies_on γ hγ _ hF
  have hinj : Set.InjOn point (U : Set K) := by
    intro γ hγ η hη heq
    have hv := (monomialPoint_injective (fun i =>
      single_mem_bidegreeExponents ha hb i) : Function.Injective
      (monomialPoint (E := FX) (bidegreeExponents (Fin n) a b))) heq
    exact hw.distinct hγ hη (Polynomial.map_injective _ (algebraMap K L).injective
      (IsFractionRing.injective L[X] FX (congrFun hv none)))
  have hsection (i : I) (hmiss : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D := by
    let x := node i
    let y := w i
    let q := C.numerator x - MvPolynomial.C (seedEmbedding y) * C.denominator
    have hq : q ∈ restrictBidegree (Fin n) FX a b := by
      refine Submodule.sub_mem _ (C.numerator_bound x) ?_
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ C.denominator_bound
    let Q := bidegreeLift q hq
    have hcut (γ : K) (hγ : γ ∈ U) :
        MvPolynomial.aeval (point γ) Q = 0 ↔ (s γ).eval x = y := by
      have hr := hrec γ hγ
      change MvPolynomial.aeval (v γ) C.denominator ≠ 0 ∧
        (∀ x, MvPolynomial.aeval (v γ) (C.numerator x) =
          MvPolynomial.aeval (v γ) C.denominator * seedEmbedding ((s γ).eval x)) at hr
      rw [eval_linear, show M Q = q from bidegreeMap_bidegreeLift q hq]
      dsimp only [q]
      rw [map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, hr.2 x,
        sub_eq_zero, mul_comm (seedEmbedding y), mul_right_inj' hr.1]
      exact seedEmbedding.injective.eq_iff
    have hproper : Q ∉ P := by
      obtain ⟨γ, hγ, hγmiss⟩ := hmiss
      exact fun hQ => hγmiss ((hcut γ hγ).mp (hpoints γ hγ Q hQ))
    refine proper_section_card _ point (hinj.mono (filter_subset _ _)) hproper
      (totalDegree_bidegreeLift_le_one q hq) (fun γ hγ => ?_) hdim hdeg
    obtain ⟨hγU, hγhit⟩ := mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU, (hcut γ hγU).mpr hγhit⟩
  have hcount := P0_10.section_capacity hw (by decide) D hsection
  change 45592 * U.card ≤ 81927 * D + 45592 at hcount
  have hcountQ : (45592 : ℚ) * (U.card : ℚ) ≤ 81927 * (D : ℚ) + 45592 := by
    exact_mod_cast hcount
  change (U.card : ℚ) ≤ beta * (D : ℚ) + 1
  unfold beta
  linarith only [hcountQ]
set_option maxHeartbeats 800000 in
theorem root_tariff : RootTariff := by
  intro u del M Γ F hM T hT J g H hg h8 hcurve hmarks
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨U, hU, hexc, n, ⟨A⟩⟩ :=
    root_chart T M.label F.scalar J g H hg h8 hcurve hlabel hmarks
  have hw := bridge_word M F hM U (hU.trans hT)
  obtain ⟨C, hreconstruct⟩ :=
    root_taylor n endpointDegree g (by decide) (by decide) hg A.equation A.equation_degree
  have hregular := regular_count_P0_10RBridgeRoot A hw C
    (fun γ hγ => hreconstruct _ _ (hw.degree γ hγ) (A.root γ hγ) (A.simple γ hγ)) root_embedding
  let b := taylorPower endpointDegree
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hmixed : b * (g * H) + ordinateBound endpointDegree g * H =
      (b * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [ordinateBound, b]
    ring
  rw [hmixed] at hregular
  have hcast : (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
    unfold taylorPower
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hgQ : (1 : ℚ) ≤ (g : ℚ) := by exact_mod_cast hg
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ) + (U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ ((taylorPower g * H : ℕ) : ℚ) +
        (beta * (((b * taylorPower g + 1) * H : ℕ) : ℚ) + 1) :=
      add_le_add (Nat.cast_le.mpr hexc) hregular
    _ ≤ ((taylorPower g * H : ℕ) : ℚ) +
        (beta * (((b * taylorPower g + 1) * H : ℕ) : ℚ) + g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = rootPrice g H := by
      unfold rootPrice
      push_cast
      rw [hcast]
      dsimp only [b, taylorPower]
      ring
end
end P0_10R.Bridge
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace P0_10R.Bridge
noncomputable section
open P0 (AnchorModel AnchoredFamily K p)
open K1_14 (Seeds L graphEval)
open K1_14_2 (Ambient SeedField JetYSection OnJet OnRoot SmallRootCurve endpointDegree)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength
  yLength)
open private on_root on_seed moving_graph_count seed_graph_count equal_image_degree
  union_card_le from ProximityPrize.SubmissionLower.Fast062
open scoped BigOperators Classical
private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private def seedRate : ℚ := ((p + 1 : ℕ) : ℚ) / 9
private def yRate : ℚ := 15 + beta * (((2 * endpointDegree - 1 : ℕ) : ℚ)*15+1)
private theorem root_price_bound (g H : ℕ) (hg : g ≤ 8) :
    rootPrice g H ≤ yRate * (H : ℚ) + (g : ℚ) := by
  have hgq : (g : ℚ) ≤ 8 := by exact_mod_cast hg
  have ht : 2 * (g : ℚ) - 1 ≤ 15 := by linarith
  have hd : 0 ≤ ((2 * endpointDegree - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
  have hb : 0 ≤ beta := by unfold beta; positivity
  exact add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add ht (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left ht hd) (le_refl (1 : ℚ))) hb))
    (Nat.cast_nonneg H)) (le_refl (g : ℚ))
private theorem seedRate_nonneg : 0 ≤ seedRate := by unfold seedRate; positivity
private theorem yRate_nonneg : 0 ≤ yRate := by unfold yRate beta; positivity
private theorem seedCap_lt_p : lossSeedCap < p := by decide
private theorem seedCap_le_rate : (lossSeedCap : ℚ) ≤ seedRate := by
  have h : lossSeedCap * 9 ≤ p + 1 := by decide
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 9)).mpr (by exact_mod_cast h)
private theorem linear_rate (r a b c : ℕ) (hb : (b : ℚ) ≠ 0) :
    (r : ℚ) + ((a : ℚ)/b)*((c : ℚ)*15+1) =
      ((r*b+a*(c*15+1) : ℕ) : ℚ)/b := by
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  field_simp
private theorem yRate_eq : yRate = ((330882208152 : ℕ) : ℚ) / 45592 := by
  unfold yRate beta
  have h := linear_rate 15 81927 45592 (2*endpointDegree-1) (by norm_num : (45592 : ℚ) ≠ 0)
  have hn : (15 : ℕ) * 45592 + 81927 * ((2*endpointDegree-1)*15+1) = 330882208152 := by decide
  rw [hn] at h
  exact h
private theorem tariff_fraction (a b d h c m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hc : a*d*n + b*h*m + d*(m*n) ≤ c*(m*n)) :
    ((a : ℚ)/m)*d + ((b : ℚ)/n)*h + d ≤ c := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  apply le_of_mul_le_mul_right _ (mul_pos hm' hn')
  have hq : (a : ℚ)*d*n + (b : ℚ)*h*m + (d : ℚ)*((m : ℚ)*n) ≤
      (c : ℚ)*((m : ℚ)*n) := by exact_mod_cast hc
  convert hq using 1
  all_goals field_simp
private theorem tariff_ledger :
    seedRate * (lossSeedCap : ℚ) + yRate * (lossYCap : ℚ) + (lossSeedCap : ℚ) ≤
      (curveFee : ℚ) := by
  rw [yRate_eq]
  exact tariff_fraction (p+1) 330882208152 lossSeedCap lossYCap curveFee 9 45592
    (by decide) (by decide) (by decide)
private theorem group_price {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hhi : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ)
    (tariff : RootTariff)
    (P : Ideal Seeds) (s : Finset (Ideal Ambient))
    (hne : s.Nonempty) (himage : ∀ I ∈ s, seedImage I = P)
    (hslice : ∀ I ∈ s, SeedSlice I ∧ Module.Finite SeedField (JetYSection I))
    (hcap : (∑ I ∈ s, seedLength I) ≤ lossSeedCap) :
    let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
    ((s.biUnion W).card : ℚ) ≤
      seedRate * (∑ I ∈ s, (seedLength I : ℚ)) +
      yRate * (∑ I ∈ s, (yLength I : ℚ)) + ∑ I ∈ s, (seedLength I : ℚ) := by
  classical
  let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
  let U := s.biUnion W
  let D : ℕ := ∑ I ∈ s, seedLength I
  let H : ℕ := ∑ I ∈ s, yLength I
  change (U.card : ℚ) ≤ seedRate * (∑ I ∈ s, (seedLength I : ℚ)) +
    yRate * (∑ I ∈ s, (yLength I : ℚ)) + ∑ I ∈ s, (seedLength I : ℚ)
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  change (U.card : ℚ) ≤ seedRate * (D : ℚ) + yRate * (H : ℚ) + (D : ℚ)
  have extend_seed (h : (U.card : ℚ) ≤ seedRate * (D : ℚ)) :
      (U.card : ℚ) ≤ seedRate * (D : ℚ) + yRate * (H : ℚ) + (D : ℚ) := by
    exact h.trans (le_add_of_nonneg_right (mul_nonneg yRate_nonneg (Nat.cast_nonneg H)) |>.trans
      (le_add_of_nonneg_right (Nat.cast_nonneg D)))
  obtain ⟨J, hJ⟩ := hne
  obtain ⟨C, hC, hJproj, hCpos, hCbound⟩ := K1_14_2_3_1.proof J (hslice J hJ).1
  have hP : P = Ideal.span {C} := (himage J hJ).symm.trans hJproj
  have hCD : C.totalDegree ≤ D :=
    hCbound.trans (Finset.single_le_sum (f := seedLength) (fun _ _ => Nat.zero_le _) hJ)
  have hlabels : ∀ z ∈ U.image M.label, graphEval z C = 0 := by
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨I, hI, hγI⟩ := Finset.mem_biUnion.mp hγ
    refine on_seed (Finset.mem_filter.mp hγI).2 ?_
    rw [himage I hI, hP]
    exact Ideal.mem_span_singleton_self C
  have hcard : (U.image M.label).card = U.card :=
    Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
  by_cases hlarge : 9 * C.totalDegree ≤ D
  · have hc := seed_graph_count C hC.ne_zero ((hCD.trans hcap).trans_lt seedCap_lt_p)
      (U.image M.label) hlabels
    rw [hcard] at hc
    have hcq : (U.card : ℚ) ≤ ((p+1 : ℕ) : ℚ) * (C.totalDegree : ℚ) := by exact_mod_cast hc
    have hdq : (9 : ℚ) * (C.totalDegree : ℚ) ≤ (D : ℚ) := by exact_mod_cast hlarge
    apply extend_seed
    calc
      _ ≤ ((p+1 : ℕ) : ℚ) * (C.totalDegree : ℚ) := hcq
      _ = seedRate * (9 * (C.totalDegree : ℚ)) := by unfold seedRate; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdq seedRate_nonneg
  by_cases hconst : DefinedOverConstants P
  · obtain ⟨Q, hQ, hQproj⟩ := hconst
    have hdeg : C.totalDegree = Q.totalDegree := equal_image_degree C hC.ne_zero Q
      (hP.symm.trans hQproj)
    have hsbound (I : Ideal Ambient) (hI : I ∈ s) :
        ((W I).card : ℚ) ≤ yRate * (yLength I : ℚ) + (seedLength I : ℚ) := by
      obtain ⟨g, hg, hroot, hgD⟩ :=
        projected_curve I Q (hslice I hI).1 (hslice I hI).2 hQ ((himage I hI).trans hQproj)
      have hgi : g ≤ 8 := by
        by_contra! hbad
        have hsuccess := (Nat.mul_le_mul_left Q.totalDegree hbad).trans
          (hgD.trans (Finset.single_le_sum (f := seedLength) (fun _ _ => Nat.zero_le _) hI))
        exact hlarge (by simpa [hdeg, Nat.mul_comm 9] using hsuccess)
      have hgcap : g ≤ seedLength I :=
        (Nat.le_mul_of_pos_left g (hdeg ▸ hCpos)).trans hgD
      have hsub : W I ⊆ Γ := (Finset.filter_subset _ _).trans hT
      have ht := tariff u del M Γ F hhi (W I) hsub (rootImage I) g (yLength I) hg hgi hroot
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
      have hgcapq : (g : ℚ) ≤ (seedLength I : ℚ) := by exact_mod_cast hgcap
      exact ht.trans ((root_price_bound g (yLength I) hgi).trans (add_le_add le_rfl hgcapq))
    calc
      (U.card : ℚ) ≤ ∑ I ∈ s, ((W I).card : ℚ) := union_card_le s W
      _ ≤ ∑ I ∈ s, (yRate * (yLength I : ℚ) + (seedLength I : ℚ)) := Finset.sum_le_sum hsbound
      _ = yRate * (H : ℚ) + (D : ℚ) := by
        simp only [H, D, Finset.sum_add_distrib, Finset.mul_sum, Nat.cast_sum]
      _ ≤ _ := by
        rw [add_assoc]
        exact le_add_of_nonneg_left (mul_nonneg seedRate_nonneg (Nat.cast_nonneg D))
  · have hc := moving_graph_count p C hC (hP ▸ hconst) (U.image M.label) hlabels
    rw [hcard] at hc
    have hq : (U.card : ℚ) ≤ (C.totalDegree : ℚ) ^ 2 := by exact_mod_cast hc
    have hCq : (C.totalDegree : ℚ) ≤ (D : ℚ) := by exact_mod_cast hCD
    have hCr : (C.totalDegree : ℚ) ≤ seedRate :=
      (by exact_mod_cast (hCD.trans hcap) : (C.totalDegree : ℚ) ≤ (lossSeedCap : ℚ)).trans
        seedCap_le_rate
    exact extend_seed (hq.trans (by
      rw [pow_two]
      exact mul_le_mul hCr hCq (Nat.cast_nonneg C.totalDegree) seedRate_nonneg))
theorem curve_count (tariff : RootTariff) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (hhi : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ)
    (cs : Finset (Ideal Ambient)) (hs : ∀ I ∈ cs, K1_14_2_2.CurveGeometry I)
    (hD : K1_14_2_2.curveSeedMass cs ≤ lossSeedCap)
    (hH : K1_14_2_2.curveYMass cs ≤ lossYCap)
    (hcover : ∀ γ ∈ T, ∃ I ∈ cs, OnJet I (M.label γ) (F.scalar γ)) :
    T.card ≤ curveFee := by
  classical
  let images := cs.image seedImage
  let group (P : Ideal Seeds) := cs.filter (fun I => seedImage I = P)
  let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
  let covered (P : Ideal Seeds) := (group P).biUnion W
  have hsubset : T ⊆ images.biUnion covered := by
    intro γ hγ
    obtain ⟨I, hi, hz⟩ := hcover γ hγ
    refine Finset.mem_biUnion.mpr ⟨seedImage I, Finset.mem_image_of_mem _ hi, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_filter.mpr ⟨hi, rfl⟩,
      Finset.mem_filter.mpr ⟨hγ, hz⟩⟩
  have hgroup (P : Ideal Seeds) (hP : P ∈ images) :
      ((covered P).card : ℚ) ≤
        seedRate * (∑ I ∈ group P, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ group P, (yLength I : ℚ)) + ∑ I ∈ group P, (seedLength I : ℚ) := by
    obtain ⟨I, hi, he⟩ := Finset.mem_image.mp hP
    refine group_price M F hhi T hT tariff P (group P)
      ⟨I, Finset.mem_filter.mpr ⟨hi, he⟩⟩
      (fun _ hJ => (Finset.mem_filter.mp hJ).2) (fun J hJ => ?_) ?_
    · obtain ⟨hp, hdim, hf, hpos, hy⟩ := hs J (Finset.mem_filter.mp hJ).1
      exact ⟨⟨hp, hdim, hf, hpos⟩, hy⟩
    · exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hD
  have hsum (f : Ideal Ambient → ℚ) :
      (∑ P ∈ images, ∑ I ∈ group P, f I) = ∑ I ∈ cs, f I :=
    Finset.sum_fiberwise_of_maps_to (fun _ hI => Finset.mem_image_of_mem seedImage hI) f
  have hDq : (∑ I ∈ cs, (seedLength I : ℚ)) ≤ (lossSeedCap : ℚ) := by
    exact_mod_cast hD
  have hHq : (∑ I ∈ cs, (yLength I : ℚ)) ≤ (lossYCap : ℚ) := by
    exact_mod_cast hH
  have hbound : (T.card : ℚ) ≤ (curveFee : ℚ) := calc
    (T.card : ℚ) ≤ ((images.biUnion covered).card : ℚ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ P ∈ images, ((covered P).card : ℚ) := union_card_le images covered
    _ ≤ ∑ P ∈ images, (seedRate * (∑ I ∈ group P, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ group P, (yLength I : ℚ)) + ∑ I ∈ group P, (seedLength I : ℚ)) :=
      Finset.sum_le_sum hgroup
    _ = seedRate * (∑ I ∈ cs, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ cs, (yLength I : ℚ)) + ∑ I ∈ cs, (seedLength I : ℚ) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    _ ≤ seedRate * (lossSeedCap : ℚ) + yRate * (lossYCap : ℚ) + (lossSeedCap : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hDq seedRate_nonneg)
        (mul_le_mul_of_nonneg_left hHq yRate_nonneg)) hDq
    _ ≤ _ := tariff_ledger
  exact_mod_cast hbound
end
end P0_10R.Bridge
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace P0_10R.Later
noncomputable section
open P0 (AnchorModel AnchoredFamily agreement p heightCap)
open P0_10 (JetSource BufferedPair BankVanishes fullCutoff reserveCutoff MarkOn
  freeShape movingShape fullShape terminalShape scheduled band reserve)
open K1_14 (Shape Jet Banks seedHasse jetAt atMark)
open K1_14_3 (Surface Parent RowCaps OrderAt)
open K1_14_3R (compatible chainCutter chainCutter_caps_of_dvd chainCutter_zero)
open Polynomial
theorem later_free_zero {w : ℤ} (hw : 3555 ≤ w) : freeShape w 0 = freeZero := by
  simp [freeShape, show ¬ w ≤ 3554 by omega, freeZero]
theorem later_moving_zero {w : ℤ} (hw : 3555 ≤ w) : movingShape w 0 = movingZero := by
  simp [movingShape, show ¬ w ≤ 3554 by omega, movingZero]
theorem later_free_five {w : ℤ} (hw : 3555 ≤ w) : freeShape w 1 = freeFive := by
  simp [freeShape, show ¬ w ≤ 3554 by omega, freeFive]
theorem later_moving_five {w : ℤ} (hw : 3555 ≤ w) : movingShape w 1 = movingFive := by
  simp [movingShape, show ¬ w ≤ 3554 by omega, movingFive]
theorem later_full {w : ℤ} (hw : 3555 ≤ w) : fullShape w = laterTerminal := by
  have hn : ¬ w ≤ 3554 := by omega
  unfold fullShape terminalShape band
  simp only [hn, ite_false]
  split_ifs <;> rfl
theorem terminal_shape_data {w : ℤ} (hw : 3555 ≤ w) :
    (terminalShape w).m = (fullShape w).m ∧
    (terminalShape w).B = (fullShape w).B ∧
    (terminalShape w).J = (fullShape w).J ∧
    (terminalShape w).U ≤ (fullShape w).U ∧ (band w).yBound = 4 := by
  rw [later_full hw]
  have hn : ¬ w ≤ 3554 := by omega
  unfold terminalShape band
  simp only [hn, ite_false]
  split_ifs <;> decide
theorem order_of_source {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) {s : Shape} (hs : s ∈ scheduled M.overhead)
    (hh : 0 < M.overhead.toNat) (hchar : s.m * agreement < p) {q : Surface}
    (hq : Parent q) (hv : BankVanishes rows s q) (W : ℕ) (hw : W < s.m * agreement)
    (P : Jet) (hP : P ∈ rows s W) :
    OrderAt q P (contactPower M.overhead.toNat s W) := by
  let h := M.overhead.toNat
  apply K1_14_3R_1.proof _ _ _ hq
  · have := Nat.div_le_self (s.m * agreement - 1 - W) (2 * h)
    change 1 + (s.m * agreement - 1 - W) / (2 * h) < p
    omega
  intro a b hab
  change a + b < 1 + (s.m * agreement - 1 - W) / (2 * h) at hab
  have hd : 0 < 2 * h := by dsimp [h]; omega
  have hl := (Nat.le_div_iff_mul_le hd).mp
    (show a + b ≤ (s.m * agreement - 1 - W) / (2 * h) by omega)
  rw [Nat.mul_comm (a + b), Nat.mul_add] at hl
  have hle : W + 2 * h * a + 2 * h * b ≤ s.m * agreement - 1 := by omega
  have hA := src.shift s hs W P hP 0 a
  have hB := src.shift s hs _ _ hA 1 b
  exact hv _ (src.nested s hs s hs rfl rfl rfl le_rfl _ _ hle hB)
theorem buffered_lt {w : ℤ} {s : Shape} (i : Fin 2) (hm : 0 < s.m) :
    reserveCutoff w s i < s.m * agreement := by
  have hprod := Nat.mul_pos hm (by decide : 0 < agreement)
  unfold reserveCutoff fullCutoff
  omega
theorem buffered_five_power {w : ℤ} {s : Shape} (hh : 0 < w.toNat)
    (hfit : 2 * w.toNat * 5 ≤ fullCutoff s) :
    contactPower w.toNat s (reserveCutoff w s 1) = 6 := by
  have hdiff : fullCutoff s - reserveCutoff w s 1 = 2 * w.toNat * 5 := by
    change fullCutoff s - (fullCutoff s - 2 * w.toNat * 5) = 2 * w.toNat * 5
    omega
  change 1 + (fullCutoff s - reserveCutoff w s 1) / (2 * w.toNat) = 6
  rw [hdiff, Nat.mul_div_cancel_left _ (by omega)]
theorem bank_cutter {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) {s : Shape} (hs : s ∈ scheduled M.overhead)
    (hm : 0 < s.m) (q : Surface) (hn : ¬ BankVanishes rows s q) :
    ∃ P : Jet, P ∉ q.asIdeal ∧ RowCaps P s ∧
      ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 := by
  unfold BankVanishes at hn
  push Not at hn
  obtain ⟨P, hP, hp⟩ := hn
  have hprod := Nat.mul_pos hm (by decide : 0 < agreement)
  have hw : fullCutoff s < s.m * agreement := by unfold fullCutoff; omega
  exact ⟨P, hp, src.shape s hs _ P hP, src.necessary s hs _ hw P hP⟩
theorem five_cutter {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hl : 3555 ≤ M.overhead)
    (pair : BufferedPair M.overhead rows 1) (q : Surface) (hn : ¬ SurfacePass pair q) :
    ∃ P : Jet, P ∉ q.asIdeal ∧ RowCaps P movingFive ∧
      ∀ γ ∈ Γ, MarkOn M F q γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
  have hf := later_free_five hl
  have hg := later_moving_five hl
  have hs : freeShape M.overhead 1 ∈ scheduled M.overhead := by simp [scheduled]
  have ht : movingShape M.overhead 1 ∈ scheduled M.overhead := by simp [scheduled]
  have hfm : 0 < (freeShape M.overhead 1).m := by rw [hf]; decide
  have hgm : 0 < (movingShape M.overhead 1).m := by rw [hg]; decide
  by_cases hfree : BankVanishes rows (freeShape M.overhead 1) q
  · by_cases hmoving : BankVanishes rows (movingShape M.overhead 1) q
    · have hco : ¬ compatible pair.free pair.moving q := fun h => hn ⟨hfree, hmoving, h⟩
      unfold compatible at hco
      push Not at hco
      obtain ⟨f, _, _, _, hdiv, hfq, g, a, hclear, hproper⟩ := hco
      have hcaps : RowCaps pair.moving movingFive := by
        simpa only [hg] using src.shape _ ht _ _ pair.moving_mem
      have hj : 1 ≤ movingFive.J := by decide
      have hchain : RowCaps (chainCutter g) movingFive :=
        chainCutter_caps_of_dvd pair.moving_ne hcaps hj hdiv hclear
      refine ⟨chainCutter g, hproper, hchain, ?_⟩
      intro γ _ hmark
      apply chainCutter_zero hclear
      have hz := RingHom.mem_ker.mp (hmark hfq)
      change jetAt (C f) (M.label γ) (F.scalar γ) = 0 at hz
      simpa only [jetAt, eval₂_C, coe_eval₂RingHom, atMark] using hz
    · obtain ⟨P, hproper, hcap, hzero⟩ := bank_cutter src ht hgm q hmoving
      rw [hg] at hcap
      exact ⟨P, hproper, hcap, fun γ hγ _ => hzero γ hγ⟩
  · obtain ⟨P, hproper, hcap, hzero⟩ := bank_cutter src hs hfm q hfree
    rw [hf] at hcap
    have hwiden : RowCaps P movingFive := by
      intro v y hy
      obtain ⟨hb, hj, hu⟩ := hcap v y hy
      exact ⟨hb.trans (by decide), hj.trans (by decide), hu.trans (by decide)⟩
    exact ⟨P, hproper, hwiden, fun γ hγ _ => hzero γ hγ⟩
end
end P0_10R.Later
end
section
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace P0_10R.Later
noncomputable section
open K1 (p)
open K1_14 K1_14_3 K1_14_3_2 K1_14_3R K1_14_3R_2 Polynomial
open scoped Classical BigOperators
open private graphCap mass_split mass_mono mass_le_biUnion_sum sum_graph_cap
  weighted_mass ordinary_graph_mass from ProximityPrize.SubmissionLower.Fast067
private theorem high_mass (h3 : K1_14_3R_2.c3) (h4 : K1_14_3R_2.c4) {P Q : Jet}
    (D : FullGcd P Q freeFive movingFive)
    (qs : Finset Surface) (hg : OrdinaryGraphs P Q qs)
    (hp : ∀ q ∈ qs, Parent q) (r : ℕ) (hr : 0 < r) (k : Fin 3) :
    mass (qs.filter (HighOn D.ordinary r)) (countedSlice k) ≤
      graphCap ((freeFive.U : ℚ) / r) ((freeFive.B : ℚ) / r) k := by
  obtain ⟨fs, hf, hc, hb, hu⟩ := highFactors D.ordinary r D.ordinary_ne hr
  let T := fun f : Equation => qs.filter fun q => (C f : Jet) ∈ q.asIdeal
  have hcover : qs.filter (HighOn D.ordinary r) ⊆ fs.biUnion T := by
    intro q hq
    obtain ⟨hm, f, hi, hd, hdiv, hmem⟩ := Finset.mem_filter.mp hq
    obtain ⟨g, hg, v, hv⟩ := hc f hi hd hdiv
    rw [Finset.mem_biUnion]
    refine ⟨g, hg, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
    rw [hv, map_mul]
    exact q.asIdeal.mul_mem_right _ hmem
  have hDvdP : (C D.ordinary : Jet) ∣ P := by
    exact ⟨fixedEmbedding D.fixed * D.left, D.left_factor.trans (mul_left_comm _ _ _)⟩
  have hDvdQ : (C D.ordinary : Jet) ∣ Q := by
    exact ⟨fixedEmbedding D.fixed * D.right, D.right_factor.trans (mul_left_comm _ _ _)⟩
  have hBp : freeFive.B < p := by decide
  have hrc : (0 : ℚ) < r := by exact_mod_cast hr
  have hBoundB : (∑ f ∈ fs, (f.natDegree : ℚ)) ≤ (freeFive.B : ℚ) / r := by
    apply (le_div_iff₀ hrc).mpr
    rw [mul_comm, ← Nat.cast_sum, ← Nat.cast_mul]
    exact_mod_cast hb.trans D.ordinary_y
  have hBoundU : (∑ f ∈ fs, (ordinarySeedDegree f : ℚ)) ≤ (freeFive.U : ℚ) / r := by
    apply (le_div_iff₀ hrc).mpr
    rw [mul_comm, ← Nat.cast_sum, ← Nat.cast_mul]
    exact_mod_cast hu.trans D.ordinary_seed
  calc
    _ ≤ mass (fs.biUnion T) (countedSlice k) := mass_mono hcover _
    _ ≤ ∑ f ∈ fs, mass (T f) (countedSlice k) := mass_le_biUnion_sum fs T _
    _ ≤ ∑ f ∈ fs, graphCap (ordinarySeedDegree f) f.natDegree k := by
      apply Finset.sum_le_sum
      intro f hmem
      obtain ⟨hi, hpos, hpow⟩ := hf f hmem
      have hdiv : f ∣ D.ordinary := (dvd_pow_self _ hr.ne').trans hpow
      have hdeg := (natDegree_le_of_dvd hdiv D.ordinary_ne).trans_lt (D.ordinary_y.trans_lt hBp)
      have hdiv' := map_dvd (C : Equation →+* Jet) hdiv
      obtain ⟨g, a, ha, hproper, hmemGraph⟩ :=
        hg f hi hpos hdeg (hdiv'.trans hDvdP) (hdiv'.trans hDvdQ)
      apply ordinary_graph_mass h3 h4 f g a (T f) hpos ha hproper k
      intro q hq
      have h := Finset.mem_filter.mp hq
      exact ⟨(hp q h.1).height_two, h.2, hmemGraph q h.1 h.2⟩
    _ ≤ _ := sum_graph_cap fs k _ _ hBoundU hBoundB
private theorem residual_mass (h1 : K1_14_3R_2.c1) (h2 : K1_14_3R_2.c2) (h3 : K1_14_3R_2.c3) (h4 : K1_14_3R_2.c4) {P Q : Jet} (D : FullGcd P Q freeFive movingFive)
    (qs : Finset Surface) (m r : ℕ) (hr : 0 < r) (hrm : r ≤ m)
    (hp : ∀ q ∈ qs, Parent q ∧ OrderAt q P m ∧ OrderAt q Q m) (k : Fin 3) :
    mass (qs.filter fun q => ¬ HighOn D.ordinary r q) (countedSlice k) ≤
      (pairCap freeFive movingFive k : ℚ) / ((m + 1 - r) ^ 2 : ℕ) := by
  let n := m + 1 - r
  let S := qs.filter fun q => ¬ HighOn D.ordinary r q
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < n ^ 2 := pow_pos hn _
  have hBp : freeFive.B < p := by decide
  have hHp := D.ordinary_y.trans_lt hBp
  have hparts : ∀ q ∈ S, q.asIdeal.height = 2 ∧ D.left ∈ q.asIdeal ∧
      D.right ∈ q.asIdeal ∧ (↑(n ^ 2 : ℕ) : ℕ∞) ≤ localLength D.left D.right q := by
    intro q hq
    obtain ⟨hm, hlow⟩ := Finset.mem_filter.mp hq
    obtain ⟨hPar, hP, hQ⟩ := hp q hm
    rw [D.left_factor] at hP
    rw [D.right_factor] at hQ
    exact ⟨hPar.height_two, h2 D.left D.right q n D.proper hPar hn
      (h1 D.fixed D.ordinary D.left q m r D.fixed_ne D.ordinary_ne hHp hPar hr hrm hlow hP)
      (h1 D.fixed D.ordinary D.right q m r D.fixed_ne D.ordinary_ne hHp hPar hr hrm hlow hQ)⟩
  have hcJ : freeFive.J ≤ freeFive.B := by decide
  have htJ : movingFive.J ≤ movingFive.B := by decide
  have hlength := weighted_mass h3 h4 D.left D.right freeFive movingFive S k
    (n ^ 2) D.proper hcJ htJ D.left_caps D.right_caps hd (by
      intro q hq
      obtain ⟨hh, hP, hQ, _⟩ := hparts q hq
      exact ⟨hh, hP, hQ⟩) (fun q hq => (hparts q hq).2.2.2)
  have hdc : (0 : ℚ) < (n ^ 2 : ℕ) := by exact_mod_cast hd
  exact (le_div_iff₀ hdc).mpr (by simpa only [mul_comm] using hlength)
private def threshold (k : Fin 3) : ℕ := ![1, 1, 3] k
private def stageCap (k : Fin 3) : ℚ := ![8009 / 36, 60043 / 18, 382555 / 9] k
private theorem add_fraction_row (a m b n c d : ℕ) (hm : 0 < m) (hn : 0 < n) (hd : 0 < d)
    (h : (a * n + b * m) * d = c * (m * n)) :
    (a : ℚ) / m + (b : ℚ) / n = (c : ℚ) / d := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ((a : ℚ) * n + b * m) * d = c * ((m : ℚ) * n) := by exact_mod_cast h
  field_simp [hm', hn', hd']
  linear_combination he
private theorem mixed_graph_fraction (u b r : ℕ) (hr : 0 < r) :
    2 * ((u : ℚ) / r) * ((b : ℚ) / r) =
      ((2 * u * b : ℕ) : ℚ) / ((r * r : ℕ) : ℚ) := by
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp [hr']
private theorem stage_arithmetic (k : Fin 3) :
    let r := threshold k
    let n := 6 + 1 - r
    graphCap ((freeFive.U : ℚ) / r) ((freeFive.B : ℚ) / r) k +
      (pairCap freeFive movingFive k : ℚ) / (n ^ 2 : ℕ) = stageCap k := by
  fin_cases k
  · exact add_fraction_row 80 1 5129 36 8009 36 (by decide) (by decide) (by decide) (by decide)
  · exact add_fraction_row 940 1 86246 36 60043 18 (by decide) (by decide) (by decide) (by decide)
  · change 2 * ((940 : ℚ) / 3) * (80 / 3) + 412720 / 16 = 382555 / 9
    have hg : 2 * ((940 : ℚ) / 3) * (80 / 3) = 150400 / 9 :=
      mixed_graph_fraction 940 80 3 (by decide)
    rw [hg]
    exact add_fraction_row 150400 9 412720 16 382555 9 (by decide) (by decide) (by decide) (by decide)
theorem reserveFive_mass (P Q : Jet) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPs : RowCaps P freeFive) (hQs : RowCaps Q movingFive) (hno : NoMovingCommon P Q)
    (qs : Finset Surface) (hgraphs : OrdinaryGraphs P Q qs)
    (hpass : ∀ q ∈ qs, Parent q ∧ OrderAt q P 6 ∧ OrderAt q Q 6) :
    MassCap qs (8009 / 36) (60043 / 18) (382555 / 9) := by
  obtain ⟨D⟩ := fullGcd P Q freeFive movingFive hP hQ hPs hQs hno
  have hstage (k : Fin 3) : mass qs (countedSlice k) ≤ stageCap k := by
    let r := threshold k
    have range : 0 < threshold k ∧ threshold k ≤ 6 := by fin_cases k <;> decide
    rw [← mass_split D.ordinary r qs (countedSlice k), ← stage_arithmetic k]
    exact add_le_add
      (high_mass K1_14_3R_2_3.proof K1_14_3R_2_4.proof D qs hgraphs
        (fun q hq => (hpass q hq).1) r range.1 k)
      (residual_mass K1_14_3R_2_1.proof K1_14_3R_2_2.proof
        K1_14_3R_2_3.proof K1_14_3R_2_4.proof D qs 6 r range.1 range.2 hpass k)
  exact ⟨hstage 0, hstage 1, hstage 2⟩
end
end P0_10R.Later
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace P0_10R.Later
noncomputable section
open K1_14_3_2 (AtSurface)
open K1_14 K1_14_3 K1_14_3R_3 Polynomial
open scoped BigOperators
open private seedIdeal_ne_bot markEval_seed seedPoint_unique seedProjection from ProximityPrize.SubmissionLower.Fast057
section Seed
open K1_14_3R_3_1
open private cutter_degree_bound quotientCutterEquiv from ProximityPrize.SubmissionLower.Fast057
private theorem seed_slice (q : Surface) (P : Jet) (s : Shape) (hq : Parent q)
    (hP : RowCaps P s) (hJ : s.J ≤ s.B) (hproper : P ∉ q.asIdeal) :
    FiniteDimensional SectionField (LineSection (cutIdeal q P) .seed) ∧
      (lineLength (cutIdeal q P) .seed : ℚ) ≤ cutDegree s {q} := by
  have h1 := K1_14_3R_3_1_1.proof
  have h2 := K1_14_3R_3_1_2.of_children K1_14_3R_3_1_2_1.proof K1_14_3R_3_1_2_2.proof
    K1_14_3R_3_1_2_3.proof
  have h3 := K1_14_3R_3_1_3.of_children K1_14_3R_3_1_3_1.proof K1_14_3R_3_1_3_2.proof
    K1_14_3R_3_1_3_3.proof K1_14_3R_3_1_3_4.proof K1_14_3R_3_1_3_5.proof
  have h4 := K1_14_3R_3_1_4.proof
  classical
  obtain ⟨hD, hgen, hsep, hne⟩ := h1 q hq
  let _ : IsDomain (Curve q) := hD
  obtain ⟨ha, hc, hz⟩ := h2 q hq hsep
  obtain ⟨D⟩ := h3 SectionField (Curve q) _ _ _ hgen hsep
  obtain ⟨hfin, hlength⟩ := h4 SectionField (Curve q) _ _ hsep (hne P hproper)
  have hbound := hlength.trans (cutter_degree_bound q D hP hJ)
  rw [ha, hc, hz] at hbound
  let e := (quotientCutterEquiv q P).toLinearEquiv
  let _ : FiniteDimensional SectionField (Curve q ⧸ Ideal.span {cutter q P}) := hfin
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [lineLength, ← e.finrank_eq]
  simpa only [cutDegree, mass, Finset.sum_singleton, Nat.cast_add, Nat.cast_mul] using
    (Nat.cast_le (α := ℚ)).mpr hbound
end Seed
section JetSlice
open K1_14_3R_3_2
open private cutLength_le from ProximityPrize.SubmissionLower.Fast057
private theorem jet_slice (q : Surface) (P : Jet) (s : Shape) (hq : Parent q)
    (hP : RowCaps P s) (ha : 0 < s.B) (hb : 0 < s.U) (hproper : P ∉ q.asIdeal) :
    FiniteDimensional SectionField (LineSection (cutIdeal q P) .jet) ∧
      (lineLength (cutIdeal q P) .jet : ℚ) ≤ constantDegree s {q} := by
  classical
  have h1 := K1_14_3R_3_2_1.proof
  have h2 := K1_14_3R_3_2_2.proof
  have h3 := K1_14_3R_3_2_3.of_children K1_14_3R_3_2_3_1.proof K1_14_3R_3_2_3_2.proof
  have h4 := K1_14_3R_3_2_4.proof
  let I := curveIdeal q
  let f := rowOnLine P
  obtain ⟨hprime, hdim, hcontraction⟩ := h1 q hq
  have hf : f ∉ I := by
    intro h
    exact hproper (hcontraction ▸ (show P ∈ I.comap rowOnLine from h))
  obtain ⟨hpfin, hplen, hvfin, hvlen⟩ := h2 q hq hprime hdim
  have hdegree := linearIdeal_degree I ha hb hdim
    (h3 q hq hprime hdim) (h4 q hq hprime hdim) hpfin hplen hvfin hvlen
  obtain ⟨hfinite, hlength⟩ := cutLength_le ha hb hprime hdim hf (rowOnLine_mem P s hP)
  have hmap : (cutIdeal q P).map rowOnLine = I ⊔ Ideal.span {f} := by
    simp [cutIdeal, I, f, curveIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have : Module.Finite JetLineField (CurveAmbient ⧸ (cutIdeal q P).map rowOnLine) :=
    by rw [hmap]; exact hfinite
  obtain ⟨hsec, hsecLen⟩ := lineSection_length (cutIdeal q P)
  refine ⟨hsec, ?_⟩
  rw [hsecLen, hmap]
  have hbound := hlength.trans hdegree
  simpa only [constantDegree, mass, Finset.sum_singleton, Nat.cast_add, Nat.cast_mul] using hbound
end JetSlice
theorem cut_cover (q : Surface) (P : Jet) (s : Shape) (hq : Parent q)
    (hcaps : RowCaps P s) (hj : s.J ≤ s.B) (hb : 0 < s.B) (hu : 0 < s.U)
    (hP : P ∉ q.asIdeal) :
    ∃ C : SeedCover, (C.curve.totalDegree : ℚ) ≤ cutDegree s {q} ∧
      (C.points.card : ℚ) ≤ constantDegree s {q} ∧
      ∀ z S, AtSurface q z S → jetAt P z S = 0 → C.Covers z := by
  classical
  let I := cutIdeal q P
  let T := I.minimalPrimesFinset
  let A := T.filter (fun R => ∃ f, HasSeedEquation R f)
  let B := T.filter (fun R => ∃ t, HasSeedPoint R t)
  let f (R : Ideal Jet) := if h : ∃ f, HasSeedEquation R f then Classical.choose h else 1
  let t (R : Ideal Jet) := if h : ∃ t, HasSeedPoint R t then Classical.choose h else (0, 0)
  have hA (R) (hR : R ∈ A) : I ≤ R ∧ IsCutCurve R ∧ HasSeedEquation R (f R) := by
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hR
    have hmin := Ideal.mem_minimalPrimesFinset.mp hm
    exact ⟨hmin.le, cutCurve hq.height_two hP hmin,
      by simpa only [f, dite_eq_left he] using Classical.choose_spec he⟩
  have hB (R) (hR : R ∈ B) : I ≤ R ∧ IsCutCurve R ∧ HasSeedPoint R (t R) := by
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hR
    have hmin := Ideal.mem_minimalPrimesFinset.mp hm
    exact ⟨hmin.le, cutCurve hq.height_two hP hmin,
      by simpa only [t, dite_eq_left he] using Classical.choose_spec he⟩
  obtain ⟨hfs, hds⟩ := seed_slice q P s hq hcaps hj hP
  obtain ⟨hfj, hdj⟩ := jet_slice q P s hq hcaps hb hu hP
  let C : SeedCover :=
    ⟨∏ R ∈ A, f R, Finset.prod_ne_zero_iff.mpr (fun R hr => (hA R hr).2.2.1),
      B.image t⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · exact (show (C.curve.totalDegree : ℚ) ≤ lineLength I .seed by
      exact_mod_cast (MvPolynomial.totalDegree_finsetProd A f).trans (K1_14_3R_3_3.proof I A f hfs hA)).trans hds
  · exact (show (C.points.card : ℚ) ≤ lineLength I .jet by
      exact_mod_cast (Finset.card_image_le (f := t) (s := B)).trans (K1_14_3R_3_4.proof I B t hfj hB)).trans hdj
  intro z S hmark hz
  let e := K1_14_3_2.markEval z S
  let : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  have hI : I ≤ RingHom.ker e :=
    sup_le hmark ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr hz))
  obtain ⟨R, hR, hRe⟩ := Ideal.exists_minimalPrimes_le hI
  have hRT : R ∈ T := Ideal.mem_minimalPrimesFinset.mpr hR
  rcases seedProjection hR.isPrime (seedIdeal_ne_bot hq hP hR.le) hRe with he | hp
  · have hRA : R ∈ A := Finset.mem_filter.mpr ⟨hRT, he⟩
    have hf : f R ∈ seedIdeal R :=
      (hA R hRA).2.2.2.symm ▸ Ideal.mem_span_singleton_self (f R)
    have hfz : graphEval z (f R) = 0 :=
      (markEval_seed z S (f R)).symm.trans (RingHom.mem_ker.mp (hRe hf))
    left
    change graphEval z (∏ R ∈ A, f R) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero hRA hfz
  · have hRB : R ∈ B := Finset.mem_filter.mpr ⟨hRT, ⟨markPoint z, hp⟩⟩
    right
    exact Finset.mem_image.mpr ⟨R, hRB, seedPoint_unique (hB R hRB).2.2 hp⟩
theorem combine_cut_covers {u del} (M : P0.AnchorModel u del) {Γ} (F : P0.AnchoredFamily M Γ)
    (s : Shape) (lost : Finset Surface)
    (hcut : ∀ q ∈ lost, ∃ C : SeedCover,
      (C.curve.totalDegree : ℚ) ≤ cutDegree s {q} ∧
      (C.points.card : ℚ) ≤ constantDegree s {q} ∧
      ∀ γ ∈ Γ, P0_10.MarkOn M F q γ → C.Covers (M.label γ)) :
    ∃ C : SeedCover, (C.curve.totalDegree : ℚ) ≤ cutDegree s lost ∧
      (C.points.card : ℚ) ≤ constantDegree s lost ∧
      ∀ γ ∈ Γ, (∃ q ∈ lost, P0_10.MarkOn M F q γ) → C.Covers (M.label γ) := by
  classical
  let C (q : Surface) : SeedCover :=
    if hq : q ∈ lost then Classical.choose (hcut q hq) else ⟨1, one_ne_zero, ∅⟩
  have hC (q) (hq : q ∈ lost) :
      ((C q).curve.totalDegree : ℚ) ≤ cutDegree s {q} ∧
      ((C q).points.card : ℚ) ≤ constantDegree s {q} ∧
      ∀ γ ∈ Γ, P0_10.MarkOn M F q γ → (C q).Covers (M.label γ) := by
    simpa only [C, dite_eq_left hq] using Classical.choose_spec (hcut q hq)
  refine ⟨joinCovers lost C, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ q ∈ lost, ((C q).curve.totalDegree : ℚ) := by
        exact_mod_cast joinCovers_degree lost C
      _ ≤ ∑ q ∈ lost, cutDegree s {q} := Finset.sum_le_sum (fun q hq => (hC q hq).1)
      _ = _ := by simp [cutDegree, mass, Finset.sum_add_distrib, Finset.mul_sum]
  · calc
      _ ≤ ∑ q ∈ lost, ((C q).points.card : ℚ) := by
        exact_mod_cast joinCovers_points lost C
      _ ≤ ∑ q ∈ lost, constantDegree s {q} := Finset.sum_le_sum (fun q hq => (hC q hq).2.1)
      _ = _ := by simp [constantDegree, mass, Finset.sum_add_distrib, Finset.mul_sum]
  · rintro γ hγ ⟨q, hq, hqγ⟩
    exact joinCovers_covers hq ((hC q hq).2.2 γ hγ hqγ)
end
end P0_10R.Later
end
section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace P0_10R.Later
noncomputable section
open K1 (K I node p)
open P0 (agreement)
open P0_10 (FixedWord section_capacity)
open K1_14 (FX)
open K1_14_3 (JetPlane JetCaps fixedAt)
open K1_14_3_6 K1_13_5_3 Polynomial
open scoped BigOperators
private theorem regular_count (hclear : c1) (hchart : c2)
    {w T s d} (h : FixedWord w T s d) (hd₀ : 2 ≤ d) (hd : d < agreement)
    {g : JetPlane} (hg : Irreducible g) {b j : ℕ}
    (ht : total g ≤ b) (hr : g.natDegree ≤ j)
    (hreg : ∀ γ ∈ T, atScalar (s γ) g = 0 ∧ atScalar (s γ) g.derivative ≠ 0) :
    (agreement-d) * T.card ≤
      P0.t * (total g * topCap d b j + g.natDegree * (totalCap d b - topCap d b j)) +
        (agreement-d) := by
  classical
  by_cases hempty : T = ∅
  · simp [hempty]
  obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hpos : 0 < g.natDegree := by
    by_contra! hn
    exact (hreg γ hγ).2 (by rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hn),
      derivative_C, map_zero])
  obtain ⟨f, hft, hfr, hfne, hprime, hf⟩ := hclear g hg hpos
  obtain ⟨C⟩ := hchart f d b j hd₀ (hd.trans (by decide : agreement < 180265)) (hpos.trans_le hr) (hft.trans ht) (hfr.trans hr)
  let x (γ : K) := marked (K1_13.extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    h.distinct ha hb (Polynomial.map_injective _ K1_13.embed.injective (marked_injective heq))
  have hroot : ∀ γ ∈ T, MvPolynomial.aeval (x γ) (plane f) = 0 := by
    intro γ hγ
    change MvPolynomial.aeval (marked (K1_13.extend (s γ))) (plane f) = 0
    rw [aeval_plane, (hf _ (hreg γ hγ).1 (hreg γ hγ).2).1, map_zero]
  let cut (i : I) := C.cut (node i) (w i)
  have heval : ∀ γ ∈ T, ∀ i, MvPolynomial.aeval (x γ) (cut i) = 0 ↔
      (s γ).eval (node i) = w i :=
    fun γ hγ i => C.agrees _ (h.degree γ hγ) (hf _ (hreg γ hγ).1 (hreg γ hγ).2) _ _
  have hsupp : (plane f).support = f.support :=
    MvPolynomial.support_map_of_injective f toCenter_inj
  have hgcap := mem_capped (plane f)
    (show (plane f).totalDegree ≤ total g from by
      unfold MvPolynomial.totalDegree
      rw [hsupp]
      exact hft)
    (show (plane f).degreeOf 1 ≤ g.natDegree from by
      simpa only [MvPolynomial.degreeOf_eq_sup, hsupp] using hfr)
  apply section_capacity h hd
  intro i hi
  have hproper : cut i ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hi
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη i).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hcard := capped_cut_card
    (by simp [totalCap] : 0 < totalCap d b)
    (lt_min (by simp [totalCap]) (by omega) : 0 < topCap d b j)
    hfne hprime hgcap (mem_capped (cut i) (C.total_bound _ _) (C.top_bound _ _))
    hproper (hits.image x) (by
      intro z hz
      obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hηT, hηi⟩ := Finset.mem_filter.mp hη
      exact ⟨hroot η hηT, (heval η hηT i).mpr hηi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _)),
    MvPolynomial.cappedDegreeMixedVolume] at hcard
private theorem total_pos {g : JetPlane} (hg : Irreducible g) : 0 < total g := by
  by_contra! ht
  have hr := Nat.eq_zero_of_le_zero ((outer_le_total g).trans ht)
  have hc : g.coeff 0 ≠ 0 := by
    have h := leadingCoeff_ne_zero.mpr hg.ne_zero
    change g.coeff g.natDegree ≠ 0 at h
    rwa [hr] at h
  have hdeg : (g.coeff 0).natDegree ≤ total g := by
    simpa only [Nat.add_zero] using Bivariate.coeff_totalDegree_le g (mem_support_iff.mpr hc)
  have h0 := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (hdeg.trans ht))
  have h1 : (g.coeff 0).coeff 0 ≠ 0 := fun h => hc (h0.trans (by rw [h, map_zero]))
  have hform := (eq_C_of_natDegree_eq_zero hr).trans (congrArg C h0)
  apply hg.not_isUnit
  rw [hform]
  exact (isUnit_iff_ne_zero.mpr h1).map ((C : FX[X] →+* JetPlane).comp C)
private theorem factor_count (hc1 : c1) (hc2 : c2) {w T s d} (h : FixedWord w T s d) (hd₀ : 2 ≤ d) (hd : d < agreement)
    {g : JetPlane} (hg : Irreducible g) {b j : ℕ} (hb : 2 ≤ b) (hbp : b < p)
    (ht : total g ≤ b) (hr : g.natDegree ≤ j)
    (hroot : ∀ γ ∈ T, atScalar (s γ) g = 0) :
    let gap := agreement - d
    let mass := total g * topCap d b j + g.natDegree * (totalCap d b - topCap d b j)
    gap * T.card ≤ P0.t * mass + gap * (total g * (b-1) + 1) := by
  classical
  let good := fun γ => atScalar (s γ) g.derivative ≠ 0
  let R := T.filter good
  let E := T.filter fun γ => ¬ good γ
  have hRsub : R ⊆ T := Finset.filter_subset _ _
  have hEsub : E ⊆ T := Finset.filter_subset _ _
  have hR := regular_count hc1 hc2 (h.mono hRsub) hd₀ hd hg ht hr
    (fun γ hγ => ⟨hroot γ (hRsub hγ), (Finset.mem_filter.mp hγ).2⟩)
  have hE : E.card ≤ total g * (b-1) := by
    have hne := exception_ne_zero hg ((outer_le_total g).trans_lt (ht.trans_lt hbp))
    apply (root_count (h.mono hEsub).distinct hne ?_).trans (exception_degree hb ht)
    intro γ hγ
    exact exception_root (hroot γ (hEsub hγ))
      (Or.inr (not_ne_iff.mp (Finset.mem_filter.mp hγ).2))
  have hpartition : R.card + E.card = T.card :=
    Finset.card_filter_add_card_filter_not (s := T) good
  dsimp only
  rw [← hpartition, Nat.mul_add]
  refine (Nat.add_le_add hR (Nat.mul_le_mul_left (agreement - d) hE)).trans_eq ?_
  ring
theorem fixed_count {u del} (M : P0.AnchorModel u del) {Γ}
    (F : P0.AnchoredFamily M Γ) (d b j : ℕ)
    (hd₀ : 2 ≤ d) (hd : d < agreement) (hb : 2 ≤ b) (hbp : b < p)
    (hj : j ≤ b) (hD : ∀ γ ∈ Γ, (F.scalar γ).natDegree ≤ d)
    (G : JetPlane) (hG : G ≠ 0) (hcaps : JetCaps G b j)
    (T : Finset K) (hT : T ⊆ Γ) (hroot : ∀ γ ∈ T, fixedAt G (F.scalar γ) = 0) :
    T.card ≤ odePrice d b j := by
  classical
  have h1 := K1_14_3_6_1.proof
  have h2 := K1_14_3_6_2.proof
  let gap := agreement - d
  let a := totalCap d b
  let v := topCap d b j
  have hv : v ≤ a := min_le_left _ _
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  have hW : FixedWord M.word T F.scalar d :=
    ⟨F.distinct.mono hT, fun γ hγ => hD γ (hT hγ), fun γ hγ =>
      let m := F.mark γ (hT hγ)
      ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩⟩
  obtain ⟨fs, hF, htotal, htop, hcover⟩ := factor_cover G hG
  obtain ⟨hbG, hjG⟩ := caps_degree hcaps
  have hB := htotal.trans hbG
  have hJ := htop.trans hjG
  let S (g : JetPlane) := T.filter fun γ => atScalar (F.scalar γ) g = 0
  have hcov : T ⊆ fs.biUnion S := by
    intro γ hγ
    obtain ⟨g, hg, h⟩ := hcover _ (hroot γ hγ)
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
  have hnumber : fs.card ≤ b := by
    calc
      fs.card = ∑ _ ∈ fs, 1 := by simp
      _ ≤ ∑ g ∈ fs, total g := Finset.sum_le_sum fun g hg => total_pos (hF g hg)
      _ ≤ b := hB
  have hcount (g : JetPlane) (hg : g ∈ fs) :
      gap * (S g).card ≤
        P0.t * (total g * v + g.natDegree * (a-v)) + gap * (total g * (b-1) + 1) :=
    factor_count h1 h2 (hW.mono (Finset.filter_subset _ T)) hd₀ hd (hF g hg) hb hbp
      ((Finset.single_le_sum (fun z _ => Nat.zero_le (total z)) hg).trans hB)
      ((Finset.single_le_sum (fun z _ => Nat.zero_le z.natDegree) hg).trans hJ)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  let mass := (b-j)*v + j*a
  have hmass : b*v + j*(a-v) = mass := by
    dsimp only [mass]
    zify [hj, hv]
    ring
  have hcount' : gap * T.card ≤ P0.t*mass + gap*(b*(b-1) + b) := by
    calc
      _ ≤ gap * ∑ g ∈ fs, (S g).card := Nat.mul_le_mul_left _
        ((Finset.card_le_card hcov).trans Finset.card_biUnion_le)
      _ = ∑ g ∈ fs, gap * (S g).card := Finset.mul_sum _ _ _
      _ ≤ ∑ g ∈ fs, (P0.t * (total g * v + g.natDegree * (a-v)) +
          gap * (total g * (b-1) + 1)) := Finset.sum_le_sum hcount
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          Finset.sum_const, smul_eq_mul, mul_one]
        rw [← hmass]
        gcongr
  let charge := ((262144-d)*mass + (gap-1)) / gap
  have hceil : (262144-d)*mass ≤ gap * charge := by
    have hmod := Nat.mod_add_div ((262144-d)*mass + (gap-1)) gap
    have hlt := Nat.mod_lt ((262144-d)*mass + (gap-1)) hgap
    dsimp only [charge]
    omega
  have herrors : P0.t ≤ 262144 - d := by
    change 81927 ≤ 262144 - d
    change d < 180217 at hd
    omega
  have hpay := (Nat.mul_le_mul_right mass herrors).trans hceil
  have hbound : gap * T.card ≤ gap * (charge + b*(b-1) + b) := by
    calc
      _ ≤ _ := hcount'
      _ ≤ gap * charge + gap * (b*(b-1) + b) := Nat.add_le_add_right hpay _
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hbound hgap
end
end P0_10R.Later
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P0_10R.Later
noncomputable section
open P0 (K p agreement AnchorModel AnchoredFamily heightCap highPrefix)
open P0_10 (band MarkOn)
open K1_14 (Jet atX jetAt)
open K1_14_3 (MassCap Slice Surface mass mass_sdiff mass_nonneg cutDegree constantDegree
  SeedCover JetPlane JetCaps fixedAt seed_count scalar_atX_injective)
open scoped Classical BigOperators
theorem moving_loss_bound {S₀ S₁ S₂ : Finset Surface}
    (h₁ : S₁ ⊆ S₀) (h₂ : S₂ ⊆ S₁)
    (m₀ : MassCap S₀ 1643 28355 183584)
    (m₁ : MassCap S₁ (8009 / 36) (60043 / 18) (382555 / 9)) :
    cutDegree movingFive (S₀ \ S₁) + cutDegree laterTerminal (S₁ \ S₂) ≤ 422701573 / 12 := by
  rcases m₀ with ⟨a₀, c₀, z₀⟩
  rcases m₁ with ⟨a₁, c₁, z₁⟩
  have a₂ := mass_nonneg S₂ .seed
  have c₂ := mass_nonneg S₂ .ordinate
  have z₂ := mass_nonneg S₂ .mixed
  norm_num [cutDegree, movingFive, laterTerminal, mass_sdiff h₁, mass_sdiff h₂]
  linarith only [a₀, c₀, z₀, a₁, c₁, z₁, a₂, c₂, z₂]
theorem constant_loss_bound {S₀ S₁ S₂ : Finset Surface}
    (h₁ : S₁ ⊆ S₀) (h₂ : S₂ ⊆ S₁)
    (z₀ : mass S₀ .mixed ≤ 183584) (e₀ : mass S₀ .jets ≤ 1221580) :
    constantDegree movingFive (S₀ \ S₁) + constantDegree laterTerminal (S₁ \ S₂) ≤
      11914259980 := by
  have z₁ := mass_nonneg (S₀ \ S₁) .mixed
  have z₂ := mass_nonneg S₂ .mixed
  have e₁ := mass_nonneg (S₀ \ S₁) .jets
  have e₂ := mass_nonneg S₂ .jets
  norm_num [constantDegree, movingFive, laterTerminal, mass_sdiff h₁, mass_sdiff h₂]
    at z₁ e₁ ⊢
  linarith only [z₀, z₁, z₂, e₀, e₁, e₂]
theorem endpoint_range (w : ℤ) (hlo : 3555 ≤ w) (hhi : w ≤ (heightCap : ℤ)) :
    w ≤ (band w).endpoint ∧ 8249 ≤ (band w).endpoint ∧ (band w).endpoint ≤ 32766 := by
  unfold band
  split_ifs <;> norm_num at * <;> omega
private theorem initial_seed_fee :
    (p + 1) * (183584 + 515 + 1857) + 1221580 = 396217646862484 := rfl
private theorem first_loss_fee :
    (p + 1) * 35225131 + 11914259980 = 75054425174452834 := rfl
private theorem ode_price_row (d b j gap t a v mixed num quotient price : ℕ)
    (hg : agreement - d = gap) (ht : 2 * d - 3 = t) (ha : 1 + t * (b - 1) = a)
    (hv : min a (t * (j - 1) + d) = v) (hm : (b - j) * v + j * a = mixed)
    (hn : (262144 - d) * mixed + (gap - 1) = num)
    (hq : num / gap = quotient) (hp : quotient + b * (b - 1) + b = price) :
    odePrice d b j = price := by
  unfold odePrice
  dsimp only
  rw [hg, ht, ha, hv, hm, hn, hq, hp]
private theorem endpoint_8249_fees :
    odePrice 139320 183584 28355 = 8039283025342136 ∧
    odePrice 139320 47 10 = 679079522 ∧ odePrice 139320 93 18 = 2484100744 := by
  refine ⟨?_, ?_, ?_⟩
  · apply ode_price_row 139320 183584 28355 40897 278637 51153016372 7900612818
      2676848006353382 328781179532347831664 8039249322257080 <;> decide
  · apply ode_price_row 139320 47 10 40897 278637 12817303 2647053
      226113991 27772224871480 679077313 <;> decide
  · apply ode_price_row 139320 93 18 40897 278637 25634605 4876149
      827134065 101591914440456 2484092095 <;> decide
private theorem endpoint_23999_fees :
    odePrice 155070 183584 28355 = 12686373909283030 ∧
    odePrice 155070 47 10 = 1071620368 ∧ odePrice 155070 93 18 = 3920030986 := by
  refine ⟨?_, ?_, ?_⟩
  · apply ode_price_row 155070 183584 28355 25147 310137 56935880872 8793779568
      2979466510686632 319023397165260459914 12686340206197974 <;> decide
  · apply ode_price_row 155070 47 10 25147 310137 14266303 2946303
      251676241 26947981853980 1071618159 <;> decide
  · apply ode_price_row 155070 93 18 25147 310137 28532605 5427399
      920641815 98576801724456 3920022337 <;> decide
private theorem endpoint_32766_fees :
    odePrice 163837 183584 28355 = 18892709800175331 ∧
    odePrice 163837 47 10 = 1595871007 ∧ odePrice 163837 93 18 = 5837760951 := by
  refine ⟨?_, ?_, ?_⟩
  · apply ode_price_row 163837 183584 28355 16380 327671 60154825194 9290947371
      3147914537828829 309462034470338708882 18892676097090275 <;> decide
  · apply ode_price_row 163837 47 10 16380 327671 15072867 3112876
      265905082 26140330912553 1595868798 <;> decide
  · apply ode_price_row 163837 93 18 16380 327671 30145733 5734244
      972691494 95622382717037 5837752302 <;> decide
private theorem endpoint_fees (w : ℤ) (hlo : 3555 ≤ w) :
    (p+1)*(183584+515+1857) + 1221580 + 1643 +
      odePrice (131071 + (band w).endpoint) 183584 28355 +
      odePrice (131071 + (band w).endpoint) 47 10 +
      odePrice (131071 + (band w).endpoint) 93 18 +
      ((p+1)*35225131 + 11914259980) ≤ highPrefix w := by
  have hnot : ¬ w ≤ 3554 := by omega
  rw [initial_seed_fee, first_loss_fee]
  unfold band highPrefix
  simp only [hnot, ite_false]
  split_ifs
  · change 396217646862484 + 1643 + odePrice 139320 183584 28355 +
       odePrice 139320 47 10 + odePrice 139320 93 18 + 75054425174452834 ≤ 83625638374831363
    rw [endpoint_8249_fees.1, endpoint_8249_fees.2.1, endpoint_8249_fees.2.2]
    decide
  · change 396217646862484 + 1643 + odePrice 155070 183584 28355 +
       odePrice 155070 47 10 + odePrice 155070 93 18 + 75054425174452834 ≤ 88272853155571659
    rw [endpoint_23999_fees.1, endpoint_23999_fees.2.1, endpoint_23999_fees.2.2]
    decide
  · change 396217646862484 + 1643 + odePrice 163837 183584 28355 +
       odePrice 163837 47 10 + odePrice 163837 93 18 + 75054425174452834 ≤ 94479354514532614
    rw [endpoint_32766_fees.1, endpoint_32766_fees.2.1, endpoint_32766_fees.2.2]
    decide
theorem paid_complement {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (hl : 3555 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) {P Q : Jet}
    (initial : InitialCover P Q) (lost : SeedCover)
    (hrows : ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ) = 0)
    (hd : lost.curve.totalDegree ≤ 35225131) (he : lost.points.card ≤ 11914259980)
    (kept : Finset K)
    (hcover : ∀ γ ∈ Γ, (∃ q ∈ initial.parents, MarkOn M F q γ) →
      γ ∈ kept ∨ lost.Covers (M.label γ)) :
    (Γ \ kept).card ≤ highPrefix M.overhead := by
  classical
  have hlabel : Function.Injective M.label := fun _ _ h => sub_left_inj.mp h
  let T := Γ \ kept
  let book : Fin 6 → Finset K :=
    ![T.filter (fun γ => initial.seeds.Covers (M.label γ)),
      T.filter (fun γ => atX (F.scalar γ) ∈ initial.ordinates),
      T.filter (fun γ => fixedAt initial.lowJet (F.scalar γ) = 0),
      T.filter (fun γ => fixedAt initial.fixedFree (F.scalar γ) = 0),
      T.filter (fun γ => fixedAt initial.fixedMoving (F.scalar γ) = 0),
      T.filter (fun γ => lost.Covers (M.label γ))]
  have hbook : T ⊆ Finset.univ.biUnion book := by
    intro γ hγ
    have hΓ : γ ∈ Γ := (Finset.mem_sdiff.mp hγ).1
    obtain ⟨hP, hQ⟩ := hrows γ hΓ
    rcases initial.cover (M.label γ) (F.scalar γ) hP hQ with h | h | h | h | h | h
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨3, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨4, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · have hh := (hcover γ hΓ h).resolve_left (Finset.mem_sdiff.mp hγ).2
      exact Finset.mem_biUnion.mpr ⟨5, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hh⟩⟩
  have hzero : (book 0).card ≤ (p+1)*(183584+515+1857) + 1221580 := by
    apply (seed_count hlabel.injOn initial.seeds _
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)).trans
    · exact Nat.add_le_add (Nat.mul_le_mul_left _ initial.seedDegree) initial.seedPoints
    · exact initial.seedDegree.trans_lt (by decide)
  have hconst : (book 1).card ≤ 1643 := by
    refine (Finset.card_le_card_of_injOn (fun γ => atX (F.scalar γ)) ?_ ?_).trans initial.ordinateCount
    · intro γ hγ
      exact (Finset.mem_filter.mp hγ).2
    · intro x hx y hy h
      exact F.distinct (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).1 (scalar_atX_injective h)
  let d := 131071 + (band M.overhead).endpoint
  obtain ⟨hw, hlo, hhi⟩ := endpoint_range M.overhead hl hu
  have hdeg : ∀ γ ∈ Γ, (F.scalar γ).natDegree ≤ d := by
    intro γ hγ
    rcases (F.mark γ hγ).scalar_degree with h | h
    · simp [h]
    · have hcast : ((F.scalar γ).natDegree : ℤ) ≤ (d : ℤ) := by
        change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
        dsimp only [d]
        push_cast
        omega
      exact_mod_cast hcast
  have hode (G : JetPlane) (b j : ℕ) (hb : 2 ≤ b) (hbp : b < p) (hjb : j ≤ b)
      (hn : G ≠ 0) (hcap : JetCaps G b j) :
      (T.filter (fun γ => fixedAt G (F.scalar γ) = 0)).card ≤ odePrice d b j :=
    fixed_count M F d b j (by dsimp [d]; omega) (by change d < 180217; dsimp [d]; omega)
      hb hbp hjb hdeg G hn hcap _
      (fun _ hγ => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hγ).1).1)
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hlow : (book 2).card ≤ odePrice d 183584 28355 :=
    hode _ _ _ (by decide) (by decide) (by decide) initial.lowJet_ne initial.lowJet_caps
  have hfree : (book 3).card ≤ odePrice d 47 10 :=
    hode _ _ _ (by decide) (by decide) (by decide) initial.fixedFree_ne initial.fixedFree_caps
  have hmoving : (book 4).card ≤ odePrice d 93 18 :=
    hode _ _ _ (by decide) (by decide) (by decide) initial.fixedMoving_ne initial.fixedMoving_caps
  have hloss : (book 5).card ≤ (p+1)*35225131 + 11914259980 :=
    (seed_count hlabel.injOn lost (hd.trans_lt (by decide))
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)).trans
      (Nat.add_le_add (Nat.mul_le_mul_left _ hd) he)
  calc
    T.card ≤ (Finset.univ.biUnion book).card := Finset.card_le_card hbook
    _ ≤ ∑ i : Fin 6, (book i).card := Finset.card_biUnion_le
    _ ≤ _ := by
      rw [Fin.sum_univ_six]
      dsimp only [d] at hlow hfree hmoving
      have hf := endpoint_fees M.overhead hl
      change _ ≤ highPrefix M.overhead
      omega
end
end P0_10R.Later
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 8
namespace P0_10R
noncomputable section
section
open Bridge
open P0 (AnchorModel AnchoredFamily K lowCutoff highPrefix)
open P0_10 (BufferedPair JetSource freeShape movingShape fullShape)
open K1_14 (Banks Jet Equation jetAt)
open K1_14_2 (Ambient ODE toJet fixedAt)
open K1_14_2_2 (Active FixedPart Fits mass dual fixedOn orderOn RowCaps)
open K1_14_3 (Surface Parent NoMovingCommon)
open scoped Classical
def c1 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ 3554 → M.shift ∉ Γ →
    ∀ P Q : Jet, P ≠ 0 → Q ≠ 0 → RowCaps P (freeShape M.overhead 0) →
    RowCaps Q (movingShape M.overhead 0) → NoMovingCommon P Q →
    ∀ A : FixedPart P (freeShape M.overhead 0), ∀ B : FixedPart Q (movingShape M.overhead 0),
    (∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ) = 0) →
    Nonempty (InitialCover F P Q A.equation B.equation)
def c2 : Prop :=
  ∀ (w : ℤ), lowCutoff + 1 ≤ w → w ≤ 3554 →
    ∀ (rows : Banks) (pair : BufferedPair w rows 1),
    RowCaps pair.free (freeShape w 1) → RowCaps pair.moving (movingShape w 1) →
    ∀ A : FixedPart pair.free (freeShape w 1), ∀ B : FixedPart pair.moving (movingShape w 1),
    ∀ S : Finset (Ideal Ambient), Fits S initialCap →
    (∀ I ∈ S, Active I ∧ Bridge.PairPass pair I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      orderOn I pair.free 6 ∧ orderOn I pair.moving 6) →
    mass S 1 ≤ 47668 ∧ mass S 2 ≤ 264904 ∧ Fits (S.filter dual) reserveFiveCap
def c3 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ 3554 →
    ∀ rows, JetSource M F rows → ∀ f : Equation, f ≠ 0 →
    FullDivisibility M.overhead rows f → f.natDegree ≤ 6
end
section
open Later
open P0 (AnchorModel AnchoredFamily agreement p heightCap)
open P0_10 (JetSource BufferedPair AdjacentChart BankVanishes MarkOn
  TerminalDivisibility band scheduled freeShape movingShape fullShape
  terminalShape reserveCutoff fullCutoff forcedPower)
open K1_14 (Jet Shape Banks L FX Equation jetAt shapeSum sourceDebit triangle)
open K1_14_3 (Surface Parent RowCaps NoMovingCommon MassCap SeedCover OrderAt
  joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open K1_14_3R (OrdinaryGraphs ordinary_graph)
open scoped Classical BigOperators
open Polynomial
def c4 : Prop :=
  ∀ P Q : Jet, P ≠ 0 → Q ≠ 0 → RowCaps P freeZero → RowCaps Q movingZero →
    NoMovingCommon P Q → Nonempty (InitialCover P Q)
def c5 : Prop :=
  ∀ (h : ℕ) (rows : Banks), 3555 ≤ h → h ≤ 32766 →
    (∀ W, ∀ P ∈ rows laterTerminal W, RowCaps P laterTerminal) →
    K1_14_3.LeadingFilter h rows laterTerminal →
    (∀ W < laterTerminal.m * agreement,
      (∀ q ≤ laterTerminal.B, ∀ j ≤ min q laterTerminal.J, q * (131071 - h) ≤ W + 1 + j) →
      triangle laterTerminal.U *
        shapeSum laterTerminal (fun q j => W + 1 + j - q * (131071 - h)) ≤
        sourceDebit h laterTerminal + ∑ t ∈ Finset.range (W + 1), Module.finrank FX (rows laterTerminal t)) →
    ∃ W < laterTerminal.m * agreement, ∃ P ∈ rows laterTerminal W, P ≠ 0 ∧
      P.leadingCoeff.natDegree < 5 * (contactPower h laterTerminal W - P.natDegree)
end
end
end P0_10R
namespace P0_10R.Bridge
noncomputable section
open P0 (AnchorModel AnchoredFamily K lowCutoff highPrefix)
open P0_10 (BufferedPair JetSource freeShape movingShape fullShape)
open K1_14 (Banks Jet Equation jetAt)
open K1_14_2 (Ambient ODE toJet fixedAt)
open K1_14_2_2 (Active FixedPart Fits mass dual fixedOn orderOn RowCaps)
open K1_14_3 (Surface Parent NoMovingCommon)
open scoped Classical
private theorem fixed_group_count {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (hw : M.overhead ≤ 3554) {G : ODE} {B J : ℕ}
    (hc : K1_14_2_2.ODECaps G B J) (hb : 2 ≤ B) (hp : B < P0.p) (hj : J ≤ B) :
    (Γ.filter fun γ => fixedAt G (F.scalar γ) = 0).card ≤ fixedPrice B J := by
  exact fixed_count M F hw _ (Finset.filter_subset _ _) B J hb hp hj
    ⟨G, hc, fun _ hγ => (Finset.mem_filter.mp hγ).2⟩
private theorem card_union_bound {A B : Finset K} {a b : ℕ}
    (ha : A.card ≤ a) (hb : B.card ≤ b) : (A ∪ B).card ≤ a+b :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)
theorem cover (h1 : c1) (h2 : c2) (h3 : c3) :
    ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ 3554 → M.shift ∉ Γ →
    ∀ rows, JetSource M F rows →
    ∀ pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i, P0_10R.PrefixCover M F pairs := by
  classical
  intro u del M Γ F hlo hhi hshift rows src pairs
  let P := pairs 0
  let Q := pairs 1
  have hp₀ := src.shape _ (free_scheduled M.overhead 0) _ _ P.free_mem
  have hq₀ := src.shape _ (moving_scheduled M.overhead 0) _ _ P.moving_mem
  have hp₅ := src.shape _ (free_scheduled M.overhead 1) _ _ Q.free_mem
  have hq₅ := src.shape _ (moving_scheduled M.overhead 1) _ _ Q.moving_mem
  obtain ⟨A₀⟩ := K1_14_2_2_1.proof _ _ P.free_ne hp₀
  obtain ⟨B₀⟩ := K1_14_2_2_1.proof _ _ P.moving_ne hq₀
  obtain ⟨A₅⟩ := K1_14_2_2_1.proof _ _ Q.free_ne hp₅
  obtain ⟨B₅⟩ := K1_14_2_2_1.proof _ _ Q.moving_ne hq₅
  obtain ⟨initial⟩ := h1 u del M Γ F hlo hhi hshift P.free P.moving P.free_ne P.moving_ne
    hp₀ hq₀ P.no_moving A₀ B₀ (buffered_zero src hhi 0 P)
  let A := initial.parents
  let S := A.filter fun I => PairPass Q I ∧ ¬ fixedOn A₅.equation I ∧ ¬ fixedOn B₅.equation I
  let B := S.filter dual
  let C := B.filter (BankPass rows (fullShape M.overhead))
  have hSA : S ⊆ A := Finset.filter_subset _ _
  have hBS : B ⊆ S := Finset.filter_subset _ _
  have hCB : C ⊆ B := Finset.filter_subset _ _
  have hBA : B ⊆ A := hBS.trans hSA
  obtain ⟨hord, hmix, hBm⟩ := h2 M.overhead hlo hhi rows Q hp₅ hq₅ A₅ B₅ S
    (K1_14_2_2.fits_mono hSA initial.masses) (by
      intro I hI
      obtain ⟨hA, hpass, hfree, hmove⟩ := Finset.mem_filter.mp hI
      have hI' := initial.active I hA
      exact ⟨hI', hpass, hfree, hmove,
        buffered_order src hhi (Or.inl rfl) hI' hpass.1 Q.free_mem,
        buffered_order src hhi (Or.inr rfl) hI' hpass.2.1 Q.moving_mem⟩)
  let R := S.filter fun I => ¬ dual I
  have hRS : R ⊆ S := Finset.filter_subset _ _
  obtain ⟨G, hG, hGon⟩ := rank_equation R
    (fun I hI => ⟨initial.active I (hSA (hRS hI)), (Finset.mem_filter.mp hI).2⟩)
    ((K1_14_2_2.mass_mono hRS 1).trans hord) ((K1_14_2_2.mass_mono hRS 2).trans hmix)
  let U := A.filter fun I => ¬ PairPass Q I
  let V := B \ C
  have hU : U ⊆ A \ B := by
    intro I hI
    obtain ⟨ha, hfail⟩ := Finset.mem_filter.mp hI
    exact Finset.mem_sdiff.mpr ⟨ha, fun hb => hfail (Finset.mem_filter.mp (hBS hb)).2.1⟩
  have hV : V ⊆ B := Finset.sdiff_subset
  obtain ⟨C₅, hC₅, hcover₅⟩ := combined_cuts U stageFiveShape (by decide)
    (fun I hI => initial.active I (Finset.mem_filter.mp hI).1)
    (fun I hI => failed_pair src hhi Q (Finset.mem_filter.mp hI).2)
  obtain ⟨Cₜ, hCₜ, hcoverₜ⟩ := combined_cuts V terminalFullShape (by decide)
    (fun I hI => initial.active I (hBA (hV hI))) (by
      intro I hI
      obtain ⟨hb, hnot⟩ := Finset.mem_sdiff.mp hI
      exact failed_terminal src hhi (fun h => hnot (Finset.mem_filter.mpr ⟨hb, h⟩)))
  obtain ⟨hD, hH, hconst⟩ := loss_bounds A B U V hBA hU hV initial.masses hBm
  let curves := C₅.curves ∪ Cₜ.curves
  have massD : K1_14_2_2.curveSeedMass curves ≤ lossSeedCap :=
    (K1_14_2_2.sum_union_le _ _ _).trans ((Nat.add_le_add (hC₅ 0) (hCₜ 0)).trans hD)
  have massH : K1_14_2_2.curveYMass curves ≤ lossYCap :=
    (K1_14_2_2.sum_union_le _ _ _).trans ((Nat.add_le_add (hC₅ 1) (hCₜ 1)).trans hH)
  let lost := Γ.filter fun γ => ∃ I ∈ curves, OnParent F I γ
  have lost_paid : lost.card ≤ curveFee :=
    curve_count root_tariff M F hhi lost (Finset.filter_subset _ _) curves
      (fun I hI => (Finset.mem_union.mp hI).elim (C₅.geometric I) (Cₜ.geometric I))
      massD massH (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  let fixed₀ := Γ.filter fun γ => fixedAt A₀.equation (F.scalar γ) = 0
  let fixed₁ := Γ.filter fun γ => fixedAt B₀.equation (F.scalar γ) = 0
  let fixed₂ := Γ.filter fun γ => fixedAt A₅.equation (F.scalar γ) = 0
  let fixed₃ := Γ.filter fun γ => fixedAt B₅.equation (F.scalar γ) = 0
  let rank := Γ.filter fun γ => fixedAt G (F.scalar γ) = 0
  have shape₀ : freeShape M.overhead 0 = ⟨55,76,17,1036⟩ := by
    rw [freeShape, ite_eq_left hhi]
    rfl
  have shape₁ : movingShape M.overhead 0 = ⟨138,191,39,4990⟩ := by
    rw [movingShape, ite_eq_left hhi]
    rfl
  have shape₂ : freeShape M.overhead 1 = ⟨82,113,25,1601⟩ := by
    rw [freeShape, ite_eq_left hhi]
    rfl
  have shape₃ := moving_five M.overhead hhi
  have fixed₀_paid : fixed₀.card ≤ fixedPrice 76 17 :=
    fixed_group_count hhi (by simpa only [shape₀] using A₀.equation_caps)
      (by decide) (by decide) (by decide)
  have fixed₁_paid : fixed₁.card ≤ fixedPrice 191 39 :=
    fixed_group_count hhi (by simpa only [shape₁] using B₀.equation_caps)
      (by decide) (by decide) (by decide)
  have fixed₂_paid : fixed₂.card ≤ fixedPrice 113 25 :=
    fixed_group_count hhi (by simpa only [shape₂] using A₅.equation_caps)
      (by decide) (by decide) (by decide)
  have fixed₃_paid : fixed₃.card ≤ fixedPrice 282 58 :=
    fixed_group_count hhi (by simpa only [shape₃, stageFiveShape] using B₅.equation_caps)
      (by decide) (by decide) (by decide)
  have rank_paid : rank.card ≤ fixedPrice 264904 47668 :=
    fixed_group_count hhi hG (by decide) (by decide) (by decide)
  let keep := Γ.filter fun γ => ∃ I ∈ C, OnParent F I γ
  let paid := initial.direct ∪ fixed₀ ∪ fixed₁ ∪ fixed₂ ∪ fixed₃ ∪ rank ∪
    (C₅.direct ∪ Cₜ.direct) ∪ lost
  have hpaid : paid.card ≤ highPrefix M.overhead := by
    have hconst' := (Nat.add_le_add (hC₅ 2) (hCₜ 2)).trans hconst
    have hcst : (C₅.direct ∪ Cₜ.direct).card ≤ constantFee :=
      (Finset.card_union_le _ _).trans hconst'
    calc
      _ ≤ initialFee + fixedPrice 76 17 + fixedPrice 191 39 + fixedPrice 113 25 +
          fixedPrice 282 58 + fixedPrice 264904 47668 + constantFee + curveFee := by
        exact card_union_bound
          (card_union_bound
            (card_union_bound
              (card_union_bound
                (card_union_bound
                  (card_union_bound
                    (card_union_bound initial.paid fixed₀_paid) fixed₁_paid)
                  fixed₂_paid)
                fixed₃_paid)
              rank_paid)
            hcst)
          lost_paid
      _ ≤ _ := prefix_ledger _ hhi
  have hremove : Γ \ keep ⊆ paid := by
    intro γ hγ
    obtain ⟨hΓ, hnot⟩ := Finset.mem_sdiff.mp hγ
    have fail_kept (I : Ideal Ambient) (hI : I ∈ C) (hm : OnParent F I γ) : False :=
      hnot (Finset.mem_filter.mpr ⟨hΓ, I, hI, hm⟩)
    have from_five (I : Ideal Ambient) (hI : I ∈ U) (hm : OnParent F I γ) : γ ∈ paid := by
      rcases hcover₅ γ hΓ ⟨I, hI, hm⟩ with hd | ⟨J, hJ, hmark⟩
      · simp only [paid, Finset.mem_union]; tauto
      · have hl : γ ∈ lost :=
          Finset.mem_filter.mpr ⟨hΓ, J, Finset.mem_union_left _ hJ, hmark⟩
        exact Finset.mem_union_right _ hl
    have from_terminal (I : Ideal Ambient) (hI : I ∈ V) (hm : OnParent F I γ) : γ ∈ paid := by
      rcases hcoverₜ γ hΓ ⟨I, hI, hm⟩ with hd | ⟨J, hJ, hmark⟩
      · simp only [paid, Finset.mem_union]; tauto
      · have hl : γ ∈ lost :=
          Finset.mem_filter.mpr ⟨hΓ, J, Finset.mem_union_right _ hJ, hmark⟩
        exact Finset.mem_union_right _ hl
    rcases initial.cover γ hΓ with hd | hf | hg | ⟨I, hI, hm⟩
    · simp only [paid, Finset.mem_union]; tauto
    · have h : γ ∈ fixed₀ := Finset.mem_filter.mpr ⟨hΓ, hf⟩
      simp only [paid, Finset.mem_union]; tauto
    · have h : γ ∈ fixed₁ := Finset.mem_filter.mpr ⟨hΓ, hg⟩
      simp only [paid, Finset.mem_union]; tauto
    · by_cases ht : PairPass Q I
      · by_cases hf : fixedOn A₅.equation I
        · have h : γ ∈ fixed₂ := Finset.mem_filter.mpr ⟨hΓ, fixed_zero hm hf⟩
          simp only [paid, Finset.mem_union]; tauto
        by_cases hg : fixedOn B₅.equation I
        · have h : γ ∈ fixed₃ := Finset.mem_filter.mpr ⟨hΓ, fixed_zero hm hg⟩
          simp only [paid, Finset.mem_union]; tauto
        have hs : I ∈ S := Finset.mem_filter.mpr ⟨hI, ht, hf, hg⟩
        by_cases hj : dual I
        · have hb : I ∈ B := Finset.mem_filter.mpr ⟨hs, hj⟩
          by_cases hc : I ∈ C
          · exact (fail_kept I hc hm).elim
          · exact from_terminal I (Finset.mem_sdiff.mpr ⟨hb, hc⟩) hm
        · have h : γ ∈ rank :=
            Finset.mem_filter.mpr ⟨hΓ, fixed_zero hm (hGon I (Finset.mem_filter.mpr ⟨hs, hj⟩))⟩
          simp only [paid, Finset.mem_union]; tauto
      · exact from_five I (Finset.mem_filter.mpr ⟨hI, ht⟩) hm
  have hprice := (Finset.card_le_card hremove).trans hpaid
  by_cases he : keep = ∅
  · exact Or.inl (by simpa [he] using hprice)
  have hCA : C ⊆ A := hCB.trans hBA
  let toSurface (I : ↥C) := surfaceOf I.1 (initial.active _ (hCA I.2)).prime
  let parents := C.attach.image toSurface
  have hparents : parents.Nonempty := by
    obtain ⟨γ, hg⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨I, hi, _⟩ := (Finset.mem_filter.mp hg).2
    exact ⟨toSurface ⟨I, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _)⟩
  have hgeometry : ∀ q ∈ parents, Parent q := by
    intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    exact parent_of_dual (initial.active _ (hCA I.2)) (initial.height_two _ (hCA I.2))
      (Finset.mem_filter.mp (hCB I.2)).2
  have ht : ∀ q ∈ parents, P0_10.BankVanishes rows (fullShape M.overhead) q := by
    intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp I.2).2
  obtain ⟨f, hf, hfull, hdiv⟩ := terminal_product src hlo hhi parents hparents hgeometry ht
  have hne : f ≠ 0 := by
    rintro rfl
    simpa using hf.positive
  have hdeg := h3 u del M Γ F hlo hhi rows src f hne hfull
  refine Or.inr ⟨{
    kept := keep
    subset := Finset.filter_subset _ _
    paid := hprice
    parents := parents
    geometric := hgeometry
    initial := ?_
    survives := ?_
    terminal := ht
    covers := ?_
    equation := f
    projected := hf
    y_bound := ?_
    divides := hdiv }⟩
  · intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    exact initial.initial _ (hCA I.2)
  · intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    have hpass : PairPass Q I.1 := (Finset.mem_filter.mp (hBS (hCB I.2))).2.1
    exact surface_pass (initial.active _ (hCA I.2)).prime hpass
  · intro γ hγ
    obtain ⟨I, hi, hm⟩ := (Finset.mem_filter.mp hγ).2
    exact ⟨toSurface ⟨I, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), on_surface _ hm⟩
  · simpa only [P0_10.band, ite_eq_left hhi] using hdeg
end
end P0_10R.Bridge
namespace P0_10R.Later
noncomputable section
open P0 (AnchorModel AnchoredFamily agreement p heightCap)
open P0_10 (JetSource BufferedPair AdjacentChart BankVanishes MarkOn
  TerminalDivisibility band scheduled freeShape movingShape fullShape
  terminalShape reserveCutoff fullCutoff forcedPower)
open K1_14 (Jet Shape Banks L FX Equation jetAt shapeSum sourceDebit triangle)
open K1_14_3 (Surface Parent RowCaps NoMovingCommon MassCap SeedCover OrderAt
  joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open K1_14_3R (OrdinaryGraphs ordinary_graph)
open scoped Classical BigOperators
open Polynomial
private theorem paired_mass_of_test {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hl : 3555 ≤ M.overhead)
    (hu : M.overhead ≤ (heightCap : ℤ)) (pair : BufferedPair M.overhead rows 1)
    (S : Finset Surface) (hS : ∀ q ∈ S, Parent q) (hpass : ∀ q ∈ S, SurfacePass pair q) :
    MassCap S (8009 / 36) (60043 / 18) (382555 / 9) := by
  let w := M.overhead
  have hf : freeShape w 1 = freeFive := later_free_five hl
  have hg : movingShape w 1 = movingFive := later_moving_five hl
  have hs : freeShape w 1 ∈ scheduled w := by simp [scheduled]
  have ht : movingShape w 1 ∈ scheduled w := by simp [scheduled]
  have hh : 0 < w.toNat := by dsimp [w]; omega
  have hw : w.toNat ≤ 32766 := by
    change M.overhead ≤ 32766 at hu
    dsimp [w]
    omega
  have hPf : RowCaps pair.free freeFive := by
    simpa only [hf] using src.shape _ hs _ _ pair.free_mem
  have hPg : RowCaps pair.moving movingFive := by
    simpa only [hg] using src.shape _ ht _ _ pair.moving_mem
  apply reserveFive_mass pair.free pair.moving pair.free_ne pair.moving_ne hPf hPg pair.no_moving S
  · intro f hi hd hp hP hQ
    obtain ⟨g, a, ha, hproper, _⟩ := ordinary_graph f hi hd hp
    refine ⟨g, a, ha, hproper, ?_⟩
    intro q hq hf
    exact (hpass q hq).2.2 f hi hd hP hQ hf g a ha
  intro q hq
  have ord (s : Shape) (hm : 0 < s.m) (hs : s ∈ scheduled w)
      (hp : s.m * agreement < p) (hfit : 2 * w.toNat * 5 ≤ fullCutoff s)
      (hv : BankVanishes rows s q) (P : Jet) (hP : P ∈ rows s (reserveCutoff w s 1)) :
      OrderAt q P 6 := by
    rw [← buffered_five_power hh hfit]
    exact order_of_source src hs hh hp (hS q hq) hv _ (buffered_lt 1 hm) _ hP
  have hfree : 2 * w.toNat * 5 ≤ fullCutoff (freeShape w 1) := by
    rw [hf]
    change 2 * w.toNat * 5 ≤ 10452585
    omega
  have hmoving : 2 * w.toNat * 5 ≤ fullCutoff (movingShape w 1) := by
    rw [hg]
    change 2 * w.toNat * 5 ≤ 22346907
    omega
  exact ⟨hS q hq, ord _ (by rw [hf]; decide) hs (by rw [hf]; decide) hfree
    (hpass q hq).1 _ pair.free_mem,
    ord _ (by rw [hg]; decide) ht (by rw [hg]; decide) hmoving
      (hpass q hq).2.1 _ pair.moving_mem⟩
theorem cover (initialCover : c4) (terminalRank : c5) :
    ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    3555 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) →
    ∀ rows, JetSource M F rows →
    ∀ pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i, P0_10R.PrefixCover M F pairs := by
  classical
  intro u del M Γ F hl hu rows src pairs
  let w := M.overhead
  let h := w.toNat
  have hwlo : 3555 ≤ h := by dsimp [h, w]; omega
  have hwhi : h ≤ 32766 := by
    change M.overhead ≤ 32766 at hu
    dsimp [h, w]
    omega
  have hf : freeShape w 0 = freeZero := later_free_zero hl
  have hg : movingShape w 0 = movingZero := later_moving_zero hl
  have hs : freeShape w 0 ∈ scheduled w := by simp [scheduled]
  have ht : movingShape w 0 ∈ scheduled w := by simp [scheduled]
  have hP : RowCaps (pairs 0).free freeZero := by
    simpa only [hf] using src.shape _ hs _ _ (pairs 0).free_mem
  have hQ : RowCaps (pairs 0).moving movingZero := by
    simpa only [hg] using src.shape _ ht _ _ (pairs 0).moving_mem
  obtain ⟨initial⟩ := initialCover _ _ (pairs 0).free_ne (pairs 0).moving_ne hP hQ (pairs 0).no_moving
  have hmarks : ∀ γ ∈ Γ, jetAt (pairs 0).free (M.label γ) (F.scalar γ) = 0 ∧
      jetAt (pairs 0).moving (M.label γ) (F.scalar γ) = 0 := by
    intro γ hγ
    exact ⟨src.necessary _ hs _ (buffered_lt 0 (by rw [hf]; decide)) _ (pairs 0).free_mem γ hγ,
      src.necessary _ ht _ (buffered_lt 0 (by rw [hg]; decide)) _ (pairs 0).moving_mem γ hγ⟩
  let S₀ := initial.parents
  let S₁ := S₀.filter (SurfacePass (pairs 1))
  let S₂ := S₁.filter (BankVanishes rows (fullShape w))
  have s₁ : S₁ ⊆ S₀ := Finset.filter_subset _ _
  have s₂ : S₂ ⊆ S₁ := Finset.filter_subset _ _
  have hg₀ : ∀ q ∈ S₀, Parent q := initial.geometric
  have hg₁ : ∀ q ∈ S₁, Parent q := fun q hq => hg₀ q (s₁ hq)
  have hg₂ : ∀ q ∈ S₂, Parent q := fun q hq => hg₁ q (s₂ hq)
  have hp₁ : ∀ q ∈ S₁, SurfacePass (pairs 1) q := fun q hq => (Finset.mem_filter.mp hq).2
  have hp₂ : ∀ q ∈ S₂, BankVanishes rows (fullShape w) q :=
    fun q hq => (Finset.mem_filter.mp hq).2
  have m₁ := paired_mass_of_test src hl hu (pairs 1) S₁ hg₁ hp₁
  obtain ⟨C₁, d₁, e₁, cov₁⟩ := combine_cut_covers M F movingFive (S₀ \ S₁) (by
    intro q hq
    obtain ⟨hq₀, hfail⟩ := Finset.mem_sdiff.mp hq
    have hbad : ¬ SurfacePass (pairs 1) q := fun hp => hfail (Finset.mem_filter.mpr ⟨hq₀, hp⟩)
    obtain ⟨P, hn, hc, hv⟩ := five_cutter src hl (pairs 1) q hbad
    obtain ⟨C, hd, he, hcov⟩ := cut_cover q P movingFive (hg₀ q hq₀) hc
      (by decide) (by decide) (by decide) hn
    exact ⟨C, hd, he, fun γ hγ hm => hcov _ _ hm (hv γ hγ hm)⟩)
  have hfull : fullShape w = laterTerminal := later_full hl
  have hsfull : fullShape w ∈ scheduled w := by simp [scheduled]
  obtain ⟨C₂, d₂, e₂, cov₂⟩ := combine_cut_covers M F laterTerminal (S₁ \ S₂) (by
    intro q hq
    obtain ⟨hq₁, hfail⟩ := Finset.mem_sdiff.mp hq
    have hbad : ¬ BankVanishes rows (fullShape w) q := fun hp => hfail (Finset.mem_filter.mpr ⟨hq₁, hp⟩)
    obtain ⟨P, hn, hc, hv⟩ := bank_cutter src hsfull (by rw [hfull]; decide) q hbad
    rw [hfull] at hc
    obtain ⟨C, hd, he, hcov⟩ := cut_cover q P laterTerminal (hg₁ q hq₁) hc
      (by decide) (by decide) (by decide) hn
    exact ⟨C, hd, he, fun γ hγ hm => hcov _ _ hm (hv γ hγ)⟩)
  let C : Fin 2 → SeedCover := ![C₁,C₂]
  let lost := joinCovers Finset.univ C
  have hd : (lost.curve.totalDegree : ℚ) ≤ 422701573 / 12 := by
    have hd' : (lost.curve.totalDegree : ℚ) ≤ ∑ i : Fin 2, ((C i).curve.totalDegree : ℚ) := by
      exact_mod_cast joinCovers_degree .univ C
    rw [Fin.sum_univ_two] at hd'
    exact (hd'.trans (add_le_add d₁ d₂)).trans (moving_loss_bound s₁ s₂ initial.masses m₁)
  have he : (lost.points.card : ℚ) ≤ 11914259980 := by
    have he' : (lost.points.card : ℚ) ≤ ∑ i : Fin 2, ((C i).points.card : ℚ) := by
      exact_mod_cast joinCovers_points .univ C
    rw [Fin.sum_univ_two] at he'
    exact (he'.trans (add_le_add e₁ e₂)).trans
      (constant_loss_bound s₁ s₂ initial.masses.mixed initial.jetMass)
  let kept := Γ.filter (fun γ => ∃ q ∈ S₂, MarkOn M F q γ)
  have hcover : ∀ γ ∈ Γ, (∃ q ∈ S₀, MarkOn M F q γ) →
      γ ∈ kept ∨ lost.Covers (M.label γ) := by
    rintro γ hγ ⟨q, hq₀, hm⟩
    by_cases hq₁ : q ∈ S₁
    · by_cases hq₂ : q ∈ S₂
      · exact Or.inl (Finset.mem_filter.mpr ⟨hγ, q, hq₂, hm⟩)
      · exact Or.inr (joinCovers_covers (i := (1 : Fin 2)) (Finset.mem_univ _) (cov₂ γ hγ
          ⟨q, Finset.mem_sdiff.mpr ⟨hq₁, hq₂⟩, hm⟩))
    · exact Or.inr (joinCovers_covers (i := (0 : Fin 2)) (Finset.mem_univ _) (cov₁ γ hγ
        ⟨q, Finset.mem_sdiff.mpr ⟨hq₀, hq₁⟩, hm⟩))
  have hdNat : lost.curve.totalDegree ≤ 35225131 := by
    have ht : (lost.curve.totalDegree : ℚ) < (35225132 : ℕ) := hd.trans_lt (by norm_num)
    have hn : lost.curve.totalDegree < 35225132 := by exact_mod_cast ht
    omega
  have heNat : lost.points.card ≤ 11914259980 := by exact_mod_cast he
  have hprefix := paid_complement hl hu initial lost hmarks hdNat heNat kept hcover
  by_cases hkept : kept.Nonempty
  · have hne : S₂.Nonempty := by
      obtain ⟨γ, hγ⟩ := hkept
      obtain ⟨q, hq, _⟩ := (Finset.mem_filter.mp hγ).2
      exact ⟨q, hq⟩
    obtain ⟨f, hf⟩ := K1_14_3_7.proof S₂ hne hg₂
    have hcontacts (W : ℕ) (hw : W < laterTerminal.m * agreement) (P : Jet)
        (hP : P ∈ rows laterTerminal W) :
        ∀ q ∈ S₂, OrderAt q P (contactPower h laterTerminal W) := by
      intro q hq
      have hw' : W < (fullShape w).m * agreement := by rwa [hfull]
      have hP' : P ∈ rows (fullShape w) W := by rwa [hfull]
      have hp : (fullShape w).m * agreement < p := by rw [hfull]; decide
      simpa only [hfull] using
        order_of_source src hsfull (by omega : 0 < h) hp (hg₂ q hq) (hp₂ q hq) W hw' P hP'
    have hs' : laterTerminal ∈ scheduled w := hfull ▸ hsfull
    obtain ⟨W₀, hw₀, P₀, hp₀, hn₀, hlead⟩ := terminalRank h rows hwlo hwhi
      (src.shape _ hs') (src.leading _ hs') (src.floor_bound _ hs')
    have hfour : f.natDegree ≤ 4 := by
      by_contra! hlarge
      have hdvd := hf.divides_leading P₀ _ hn₀ (hcontacts W₀ hw₀ P₀ hp₀)
      have hdeg := natDegree_le_of_dvd hdvd (leadingCoeff_ne_zero.mpr hn₀)
      rw [natDegree_pow, mul_comm] at hdeg
      exact (not_le_of_gt hlead) ((Nat.mul_le_mul_right _ hlarge).trans hdeg)
    obtain ⟨hm, hb, hj, hU, hy⟩ := terminal_shape_data hl
    have hdiv : TerminalDivisibility w rows f := by
      intro W hW P hP hn
      have ht : terminalShape w ∈ scheduled w := by simp [scheduled]
      have hp : P ∈ rows (fullShape w) W :=
        src.nested _ ht _ hsfull hm hb hj hU W W le_rfl hP
      have hp' : P ∈ rows laterTerminal W := hfull ▸ hp
      have hmult : (band w).multiplicity = laterTerminal.m := hm.trans (congrArg Shape.m hfull)
      have hW' : W < laterTerminal.m * agreement := by rwa [← hmult]
      have hpow : forcedPower w W P.natDegree = contactPower h laterTerminal W - P.natDegree := by
        exact congrArg (fun m => 1 + (m * agreement - 1 - W) / (2 * h) - P.natDegree)
          (show (terminalShape w).m = laterTerminal.m from hmult)
      rw [hpow]
      exact hf.divides_leading P _ hn (hcontacts W hW' P hp')
    right
    exact ⟨{
      kept := kept
      subset := Finset.filter_subset _ _
      paid := hprefix
      parents := S₂
      geometric := hg₂
      initial := fun q hq => initial.initial q (s₁ (s₂ hq))
      survives := fun q hq => hp₁ q (s₂ hq)
      terminal := hp₂
      covers := fun _ hγ => (Finset.mem_filter.mp hγ).2
      equation := f
      projected := hf
      y_bound := hy.symm ▸ hfour
      divides := hdiv }⟩
  · left
    have hk := Finset.not_nonempty_iff_eq_empty.mp hkept
    simpa only [hk, Finset.sdiff_empty] using hprefix
end
end P0_10R.Later
namespace P0_10R
noncomputable section
open P0 Polynomial
open P0_10 (AdjacentChart JetSource BufferedPair adjacent_chart ReducedEquation band
  terminalMass_of_source oversized_seed_loss singular_count simple_count retained_price)
open K1_14 (Banks SeedBound atMark)
example :
    let g₀ : K1_14_3.ClearedEquation := Polynomial.X -
      C (MvPolynomial.X 0 + MvPolynomial.C (Polynomial.X (R := K1_14.L)) * MvPolynomial.X 1)
    ∀ g a, K1_14_3.IsClearing (K1_14_3.liftEquation g₀) g a →
      K1_14.jetAt (K1_14_3R.chainCutter g) (1 : P0.K) (1 + Polynomial.X) = 0 := by
  intro g₀ g a hclear
  apply K1_14_3R.chainCutter_zero hclear
  simp [g₀, K1_14_3.liftEquation, atMark, K1_14.graphEval, K1_14.seedEmbedding,
    K1_14.atX, K1_14.liftPoly]
theorem of_children (h1 : P0_10.c1) (h2 : P0_10.c2) (h5 : P0_10.c5)
    (bridgeInitial : c1) (bridgeMass : c2) (bridgeDegree : c3)
    (laterInitial : c4) (laterRank : c5) : P0.c10 := by
  classical
  intro u del M Γ F hlo hhi
  let regular := Γ.erase M.shift
  have hreg : regular ⊆ Γ := Finset.erase_subset _ _
  have hshift : M.shift ∉ regular := Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar, fun γ hγ => F.mark γ (hreg hγ), F.distinct.mono hreg⟩
  suffices hcard : regular.card ≤ highPrefix M.overhead + highRetained M.overhead by
    have herase : Γ.card - 1 ≤ regular.card := Finset.pred_card_le_card_erase
    omega
  obtain ⟨H, hH⟩ := adjacent_chart M G
  obtain ⟨rows, hrows⟩ := h1 u del M regular G hlo hhi H hH
  obtain ⟨pairs⟩ := h2 u del M regular G hlo hhi rows hrows
  have hcover : PrefixCover M G pairs := by
    by_cases h : M.overhead ≤ 3554
    · exact Bridge.cover bridgeInitial bridgeMass bridgeDegree u del M regular G hlo h hshift rows hrows pairs
    · exact Later.cover laterInitial laterRank u del M regular G (by omega) hhi rows hrows pairs
  obtain hshort | hlong := hcover
  · exact hshort.trans (Nat.le_add_right _ _)
  obtain ⟨cover⟩ := hlong
  have hf : ReducedEquation M.overhead cover.equation :=
    ⟨cover.projected.positive, cover.y_bound, cover.projected.primitive, cover.projected.separable⟩
  have hseed : SeedBound cover.equation (band M.overhead).seedBound := by
    by_contra hbad
    have hm := terminalMass_of_source hrows hlo cover.divides
    exact (h5 _ hlo hhi).not_ge (oversized_seed_loss _ hlo hhi _ hf hm hbad)
  have hroots : ∀ γ ∈ cover.kept, atMark cover.equation (M.label γ) (G.scalar γ) = 0 := by
    intro γ hγ
    obtain ⟨q, hq, hmark⟩ := cover.covers γ hγ
    have hz := RingHom.mem_ker.mp (hmark (cover.projected.vanishes q hq))
    simpa only [coe_eval₂RingHom, eval₂_C, atMark] using hz
  let singular := cover.kept.filter fun γ => atMark cover.equation.derivative (M.label γ) (G.scalar γ) = 0
  have hsubset : singular ⊆ cover.kept := Finset.filter_subset _ _
  have hexception := singular_count M hf hseed singular G.scalar
    (fun γ hγ => hroots γ (hsubset hγ)) (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hsimple := simple_count M G hhi hf hseed (cover.kept \ singular)
    (Finset.sdiff_subset.trans cover.subset) (by
      intro γ hγ
      obtain ⟨hk, hn⟩ := Finset.mem_sdiff.mp hγ
      exact ⟨hroots γ hk, fun hz => hn (Finset.mem_filter.mpr ⟨hk, hz⟩)⟩)
  have hpartition := Finset.card_sdiff_add_card_eq_card hsubset
  have htotal := Finset.card_sdiff_add_card_eq_card cover.subset
  have hpaid := cover.paid
  rw [← retained_price M.overhead]
  omega
end
end P0_10R
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace P0_10R_1
noncomputable section
open P0 (AnchorModel AnchoredFamily K p)
open P0_10R.Bridge (InitialCover OnParent initialCap initialE₀ initialFee)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover seed_count joinCovers joinCovers_degree joinCovers_points
  joinCovers_covers scalar_atX_injective)
open scoped BigOperators Classical
open private K1_14_2_2_2_3.jetEquiv jetEquiv_apply from ProximityPrize.SubmissionLower.Fast051
open private properPair_height from ProximityPrize.SubmissionLower.PortHighBase
private theorem section_bound : K1_14_2_2_2.c4 :=
  K1_14_2_2_2_4.of_children K1_14_2_2_2_4_1.proof K1_14_2_2_2_4_2.proof K1_14_2_2_2_4_3.proof
private theorem seed_projection : K1_14_2_2_2.c6 :=
  K1_14_2_2_2_6.of_children K1_14_2_2_2_6_1.proof K1_14_2_2_2_6_2.proof
private theorem height_le {I : Ideal Ambient} (hI : I.IsPrime)
    (hdim : ringKrullDim (CoordinateRing I) = 2) : I.height ≤ 2 := by
  let x : PrimeSpectrum Ambient := ⟨I, hI⟩
  have hc : Order.coheight x = 2 := by
    rw [ringKrullDim_quotient] at hdim
    change Order.krullDim (Set.Ici x) = 2 at hdim
    rw [← Order.coheight_eq_krullDim_Ici] at hdim
    exact WithBot.coe_injective hdim
  have hd : ringKrullDim Ambient = 4 := by simp [ringKrullDim_eq_zero_of_field]
  have hh : (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ ringKrullDim Ambient := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun y : PrimeSpectrum Ambient =>
      Order.height y + Order.coheight y) x)
  rw [hc, ← x.height_eq_orderHeight, hd] at hh
  have hh' : I.height + 2 ≤ (2 : ℕ∞) + 2 := WithBot.coe_le_coe.mp hh
  exact (ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp hh'
private theorem component_height {P Q : Jet} {I : Ideal Ambient} (hp : ProperPair P Q)
    (hI : I.IsPrime) (hdim : ringKrullDim (CoordinateRing I) = 2)
    (hP : toJet P ∈ I) (hQ : toJet Q ∈ I) : I.height = 2 := by
  let J := I.comap K1_14_2_2_2_3.jetEquiv.toRingHom
  let : J.IsPrime := hI.comap _
  have hP' : P ∈ J := by change K1_14_2_2_2_3.jetEquiv P ∈ I; rwa [jetEquiv_apply]
  have hQ' : Q ∈ J := by change K1_14_2_2_2_3.jetEquiv Q ∈ I; rwa [jetEquiv_apply]
  exact le_antisymm (height_le hI hdim)
    ((K1_14_2_2_2_3.jetEquiv.height_comap I) ▸ properPair_height hp J hP' hQ')
private theorem mem_of_row_dvd {I : Ideal Ambient} {P Q : Jet} (hP : toJet P ∈ I)
    (hd : P ∣ Q) : toJet Q ∈ I :=
  I.mem_of_dvd (map_dvd toJet hd) hP
private theorem ordinary_cover (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) :
    ∃ S : Finset (Ideal Ambient),
      (∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet (C f) ∈ I) ∧
      Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨g, a, hclear, hproper, hfCaps, hgCaps⟩ := K1_14_3_4_2.proof f hi hd hp
  obtain ⟨S, hS, hcover⟩ := K1_14_2_2_2_3.proof _ _ hproper
  obtain ⟨hfinite, hfits⟩ := section_bound _ _ hproper
    ⟨0, f.natDegree, 0, ordinarySeedDegree f⟩ ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩
    (Nat.zero_le _) hd hfCaps hgCaps S hS
  refine ⟨S, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨hprime, hdim, hrow, hcut⟩ := hS I hI
    exact ⟨hprime, hdim, component_height hproper hprime hdim hrow hcut, hfinite I hI, hrow⟩
  · intro k
    have h := hfits k
    fin_cases k <;> simpa [residualBudget, ordinaryBudget, two_mul, Nat.add_mul] using h
  · intro z R hz
    exact hcover z R (by simpa [jetAt, atMark] using hz) (K1_14_3R.chainCutter_zero hclear hz)
private theorem cover_count {u del} (M : AnchorModel u del) (T : Finset K)
    (C : SeedCover) (U E : ℕ) (hU : C.curve.totalDegree ≤ U)
    (hp : U < p) (hE : C.points.card ≤ E) (hcov : ∀ γ ∈ T, C.Covers (M.label γ)) :
    T.card ≤ (p+1)*U + E := by
  have hlabel : Function.Injective M.label := fun _ _ h => sub_left_inj.mp h
  exact (seed_count hlabel.injOn C (hU.trans_lt hp) hcov).trans
    (Nat.add_le_add (Nat.mul_le_mul_left _ hU) hE)
theorem proof : P0_10R.c1 := by
  classical
  intro u del M Γ F _ hw _ P Q hP hQ hPc hQc hnc A B hrows
  have hfshape : P0_10.freeShape M.overhead 0 = freeZero := by
    simp [P0_10.freeShape, hw, freeZero]
  have hmshape : P0_10.movingShape M.overhead 0 = movingZero := by
    simp [P0_10.movingShape, hw, movingZero]
  revert hPc hQc A B
  rw [hfshape, hmshape]
  intro hPc hQc A B
  obtain ⟨prep⟩ := prepare hP hQ hPc hQc hnc A B
  obtain ⟨residual, hresidual, hresCover⟩ := K1_14_2_2_2_3.proof _ _ prep.proper
  obtain ⟨hresFinite, hresCap⟩ := section_bound _ _ prep.proper _ _
    (min_le_right _ _) (min_le_right _ _) prep.free_caps prep.moving_caps residual hresidual
  have ordinary_exists (f : Equation) (hf : f ∈ prep.ordinary) :=
    ordinary_cover f (prep.ordinary_factors f hf).1 (prep.ordinary_factors f hf).2
      (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans prep.ordinary_y).trans_lt
        (prep.gcdY_le.trans_lt (by decide : 76 < p)))
  let ordinary (f : Equation) : Finset (Ideal Ambient) :=
    if hf : f ∈ prep.ordinary then Classical.choose (ordinary_exists f hf) else ∅
  have hord (f : Equation) (hf : f ∈ prep.ordinary) :
      (∀ I ∈ ordinary f, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet (C f) ∈ I) ∧
      Fits (ordinary f) (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ ordinary f, OnJet I z R := by
    simpa only [ordinary, dite_eq_left hf] using Classical.choose_spec (ordinary_exists f hf)
  let S := residual ∪ prep.ordinary.biUnion ordinary
  have hgeom (I : Ideal Ambient) (hi : I ∈ S) :
      I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet P ∈ I ∧ toJet Q ∈ I := by
    rcases Finset.mem_union.mp hi with hr | ho
    · obtain ⟨hprime, hdim, hfree, hmoving⟩ := hresidual I hr
      exact ⟨hprime, hdim, component_height prep.proper hprime hdim hfree hmoving,
        hresFinite I hr, mem_of_row_dvd hfree prep.free_dvd, mem_of_row_dvd hmoving prep.moving_dvd⟩
    · obtain ⟨f, hf, hif⟩ := Finset.mem_biUnion.mp ho
      obtain ⟨hprime, hdim, hheight, hfin, hrow⟩ := (hord f hf).1 I hif
      obtain ⟨hP', hQ'⟩ := prep.ordinary_dvd f hf
      exact ⟨hprime, hdim, hheight, hfin, mem_of_row_dvd hrow hP', mem_of_row_dvd hrow hQ'⟩
  have hfit : Fits S initialCap := by
    intro k
    have hOrdCap : mass (prep.ordinary.biUnion ordinary) k ≤ ordinaryBudget prep.gcdSeed prep.gcdY k := by
      calc
        _ ≤ ∑ f ∈ prep.ordinary, mass (ordinary f) k :=
          sum_biUnion_le prep.ordinary ordinary (fun I => sectionDegree I k)
        _ ≤ ∑ f ∈ prep.ordinary, ordinaryBudget (ordinarySeedDegree f) f.natDegree k :=
          Finset.sum_le_sum fun f hf => (hord f hf).2.1 k
        _ ≤ _ := ordinary_sum _ _ _ prep.ordinary_seed prep.ordinary_y k
    exact (sum_union_le (fun I => sectionDegree I k) _ _).trans
      ((Nat.add_le_add (hresCap k) hOrdCap).trans (ledger _ _ prep.gcdSeed_le prep.gcdY_le k))
  let noSeeds := S.filter (fun I => sectionDegree I 0 = 0)
  let constY := S.filter (fun I => 0 < sectionDegree I 0 ∧
    ¬ Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  let parents := S.filter (fun I => 0 < sectionDegree I 0 ∧
    Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  have hparents (I : Ideal Ambient) (hi : I ∈ parents) : Active I := by
    obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, _, hfinite, _⟩ := hgeom I hI
    have hbudget (k : Fin 4) : initialCap k < p := by fin_cases k <;> decide
    have hsmall (k : Fin 4) : sectionDegree I k < p :=
      (length_le_mass hI k).trans_lt ((hfit k).trans_lt (hbudget k))
    exact ⟨hprime, hdim, hfinite.seeds, hfinite.ordinate, hfinite.mixed, hfinite.jets,
      ⟨ha, hsmall 0⟩, hsmall 2, hsmall 3, hy⟩
  have seed_exists (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      ∃ C : SeedCover, C.curve.totalDegree ≤ sectionDegree I 2 ∧
        C.points.card ≤ sectionDegree I 3 ∧ ∀ z R, OnJet I z R → C.Covers z := by
    obtain ⟨hI, hz⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, _, hfinite, _⟩ := hgeom I hI
    exact seed_projection I hprime hdim hfinite hz
  let seedImage (I : Ideal Ambient) : SeedCover :=
    if hi : I ∈ noSeeds then Classical.choose (seed_exists I hi) else ⟨1, one_ne_zero, ∅⟩
  have hseedImage (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      (seedImage I).curve.totalDegree ≤ sectionDegree I 2 ∧
      (seedImage I).points.card ≤ sectionDegree I 3 ∧
      ∀ z R, OnJet I z R → (seedImage I).Covers z := by
    simpa only [seedImage, dite_eq_left hi] using Classical.choose_spec (seed_exists I hi)
  let imageCover := joinCovers noSeeds seedImage
  let seedExits := Γ.filter (fun γ => imageCover.Covers (M.label γ))
  have hseedExits : seedExits.card ≤ (p+1)*577116 + initialE₀ := by
    apply cover_count M _ _ _ _ _ (by decide) _ (fun γ hγ => (Finset.mem_filter.mp hγ).2)
    · calc
        _ ≤ ∑ I ∈ noSeeds, (seedImage I).curve.totalDegree := joinCovers_degree _ _
        _ ≤ mass noSeeds 2 := Finset.sum_le_sum (fun I hi => (hseedImage I hi).1)
        _ ≤ mass S 2 := mass_mono (Finset.filter_subset _ _) 2
        _ ≤ _ := hfit 2
    · calc
        _ ≤ ∑ I ∈ noSeeds, (seedImage I).points.card := joinCovers_points _ _
        _ ≤ mass noSeeds 3 := Finset.sum_le_sum (fun I hi => (hseedImage I hi).2.1)
        _ ≤ mass S 3 := mass_mono (Finset.filter_subset _ _) 3
        _ ≤ initialCap 3 := hfit 3
        _ ≤ _ := by decide
  let onY (I : Ideal Ambient) := Γ.filter (OnParent F I)
  let yExits := constY.biUnion onY
  have hyExits : yExits.card ≤ 5548 := by
    calc
      _ ≤ ∑ I ∈ constY, (onY I).card := Finset.card_biUnion_le
      _ ≤ mass constY 0 := by
        apply Finset.sum_le_sum
        intro I hi
        obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
        have hcard : (onY I).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro γ hγ δ hδ
          obtain ⟨hg, hgon⟩ := Finset.mem_filter.mp hγ
          obtain ⟨hd, hdon⟩ := Finset.mem_filter.mp hδ
          exact F.distinct hg hd (scalar_atX_injective (ordinate_eq (hgeom I hI).1 hy hgon hdon))
        exact hcard.trans ha
      _ ≤ mass S 0 := mass_mono (Finset.filter_subset _ _) 0
      _ ≤ _ := hfit 0
  let contentCover : SeedCover := ⟨prep.seedContent, prep.seedContent_ne, ∅⟩
  let contentExits := Γ.filter (fun γ => graphEval (M.label γ) prep.seedContent = 0)
  have hcontentExits : contentExits.card ≤ (p+1)*(1036+4990) := by
    have h := cover_count M contentExits contentCover (1036+4990) 0 prep.seedContent_degree
      (by decide) (by simp [contentCover]) (fun γ hγ => Or.inl (Finset.mem_filter.mp hγ).2)
    simpa only [Nat.add_zero] using h
  let direct := (contentExits ∪ seedExits) ∪ yExits
  refine ⟨⟨parents, hparents, fun I hi => (hgeom I (Finset.mem_filter.mp hi).1).2.2.1,
    fun I hi => (hgeom I (Finset.mem_filter.mp hi).1).2.2.2.2,
    fits_mono (Finset.filter_subset _ _) hfit, direct, ?_, ?_⟩⟩
  · calc
      direct.card ≤ (contentExits ∪ seedExits).card + yExits.card := Finset.card_union_le _ _
      _ ≤ contentExits.card + seedExits.card + yExits.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (p+1)*(1036+4990) + ((p+1)*577116 + initialE₀) + 5548 :=
        Nat.add_le_add (Nat.add_le_add hcontentExits hseedExits) hyExits
      _ = initialFee := by unfold initialFee; ac_rfl
  · intro γ hγ
    obtain ⟨hP', hQ'⟩ := hrows γ hγ
    have fromSurface (I : Ideal Ambient) (hi : I ∈ S) (hon : OnParent F I γ) :
        γ ∈ direct ∨ fixedAt A.equation (F.scalar γ) = 0 ∨
          fixedAt B.equation (F.scalar γ) = 0 ∨ ∃ J ∈ parents, OnParent F J γ := by
      by_cases ha : sectionDegree I 0 = 0
      · have hI : I ∈ noSeeds := Finset.mem_filter.mpr ⟨hi, ha⟩
        have hc : imageCover.Covers (M.label γ) := joinCovers_covers hI
          ((hseedImage I hI).2.2 _ _ hon)
        exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hc⟩)))
      · have hpos := Nat.pos_of_ne_zero ha
        by_cases hy : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
        · exact Or.inr (Or.inr (Or.inr ⟨I, Finset.mem_filter.mpr ⟨hi, hpos, hy⟩, hon⟩))
        · have hI : I ∈ constY := Finset.mem_filter.mpr ⟨hi, hpos, hy⟩
          exact Or.inl (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨I, hI, Finset.mem_filter.mpr ⟨hγ, hon⟩⟩))
    rcases prep.cover _ _ hP' hQ' with hg | hh | hc | hr | ⟨f, hf, hz⟩
    · exact Or.inr (Or.inl hg)
    · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hc⟩)))
    · obtain ⟨I, hI, hon⟩ := hresCover _ _ hr.1 hr.2
      exact fromSurface I (Finset.mem_union_left _ hI) hon
    · obtain ⟨I, hI, hon⟩ := (hord f hf).2.2 _ _ hz
      exact fromSurface I (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨f, hf, hI⟩)) hon
end
end P0_10R_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P0_10R_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open private factor_caps natDegree_zero_of_factors dvd_of_dvd_residual
  toJet_equiv ambientToJet from ProximityPrize.SubmissionLower.Fast071
structure SharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t) where
  ordinary : Equation
  left : Jet
  right : Jet
  ordinary_ne : ordinary ≠ 0
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  left_factor : P = fixedIncl A.equation * (C ordinary * left)
  right_factor : Q = fixedIncl B.equation * (C ordinary * right)
  relativelyPrime : IsRelPrime (toJet left) (toJet right)
  seed_le : seedDegree ordinary ≤ s.U
  ordinate_le : ordinary.natDegree ≤ s.B
  left_caps : RowCaps left (residualShape s (seedDegree ordinary) ordinary.natDegree)
  right_caps : RowCaps right (residualShape t (seedDegree ordinary) ordinary.natDegree)
theorem sharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPs : RowCaps P s) (hQs : RowCaps Q t)
    (hno : K1_14_3.NoMovingCommon P Q) : Nonempty (SharedGcd A B) := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D := Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D := Equation)
  let gcdJet : GCDMonoid Jet := UniqueFactorizationMonoid.toGCDMonoid Jet
  let D : Jet := gcdJet.gcd A.residual B.residual
  obtain ⟨L, R, hL, hR, hrel⟩ := @extract_gcd Jet _ gcdJet A.residual B.residual
  change A.residual = D * L at hL
  change B.residual = D * R at hR
  have hF : P = fixedIncl A.equation * (D * L) :=
    A.factorization.trans (congrArg (fixedIncl A.equation * ·) hL)
  have hG : Q = fixedIncl B.equation * (D * R) :=
    B.factorization.trans (congrArg (fixedIncl B.equation * ·) hR)
  have hFL := right_ne_zero_of_mul (hF ▸ hP)
  have hGR := right_ne_zero_of_mul (hG ▸ hQ)
  have hDne := left_ne_zero_of_mul hFL
  have hDdeg : D.natDegree = 0 := by
    apply natDegree_zero_of_factors
    intro F hIrr hfd
    by_contra hpos
    have hleft := hfd.trans (gcdJet.gcd_dvd_left A.residual B.residual)
    have hright := hfd.trans (gcdJet.gcd_dvd_right A.residual B.residual)
    obtain ⟨G, hG⟩ := hno F hIrr (dvd_of_dvd_residual A hleft)
      (dvd_of_dvd_residual B hright) (Nat.pos_of_ne_zero hpos)
    exact A.stripped G (hG ▸ hIrr) (hG ▸ hleft)
  let H := D.coeff 0
  have hD : D = C H := eq_C_of_natDegree_eq_zero hDdeg
  have hH : H ≠ 0 := fun hz => hDne (by rw [hD, hz, map_zero])
  rw [hD] at hF hG
  obtain ⟨hFu, hFb, hLc⟩ := factor_caps hP hH hPs hF
  obtain ⟨_, _, hRc⟩ := factor_caps hQ hH hQs hG
  have hprime : IsRelPrime (toJet L) (toJet R) := by
    have hr := (@gcd_isUnit_iff_isRelPrime Jet _ gcdJet L R).mp hrel
    rw [toJet_equiv]
    intro E hEL hER
    have h1 : ambientToJet E ∣ L := by
      simpa using map_dvd ambientToJet.toRingHom hEL
    have h2 : ambientToJet E ∣ R := by
      simpa using map_dvd ambientToJet.toRingHom hER
    simpa using (hr h1 h2).map ambientToJet.symm.toRingHom
  exact ⟨⟨H, L, R, hH, right_ne_zero_of_mul hFL, right_ne_zero_of_mul hGR,
    hF, hG, hprime, hFu, hFb, hLc, hRc⟩⟩
end
end P0_10R_2
end
