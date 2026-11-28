import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.Low6966Monotone
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleCaps
import ProximityPrize.SubmissionLower.Low49ActiveLattice
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low48BentCycle
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import Mathlib.Algebra.MvPolynomial.Coeff
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.R6960Anchor6966Local
import ProximityPrize.SubmissionLower.Low50Euler2367JetDegree
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.Low6966Retained
import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.Fast063
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Localization.Integer
import ProximityPrize.SubmissionLower.Shared50ShapeRankBase
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive
import ProximityPrize.SubmissionLower.R6966ProofLowTierWeight
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.Gate6966Shape
import ProximityPrize.SubmissionLower.Gate6966CertCF
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import ProximityPrize.SubmissionLower.Gate6966Amb
import ProximityPrize.SubmissionLower.Gate6966Tail

set_option Elab.async false

-- merged module Gate6966Count2
section Merged_Gate6966Count2

set_option autoImplicit false
set_option Elab.async false

namespace Gate6966Count2

open P3 (K)
open K1_13 (Row shape)
open K1_13_6 (GeoJets)





open scoped Polynomial BigOperators


















end Gate6966Count2

end Merged_Gate6966Count2

-- merged module Gate6966Final
section Merged_Gate6966Final

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Gate6966Final

open P3 (K)
open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (VanishesTo)








open scoped Polynomial BigOperators

instance infiniteGenericField : Infinite K1_13_6.GenericField :=
  Infinite.of_injective (algebraMap (Polynomial K1_13.Geom) K1_13_6.GenericField)
    (IsFractionRing.injective (Polynomial K1_13.Geom) K1_13_6.GenericField)























































variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}


































































































































end Gate6966Final

end Merged_Gate6966Final

-- merged module Gate6966Assm
section Merged_Gate6966Assm

set_option autoImplicit false

namespace Gate6966Cell
open Gate6966CertCF (cvOf)

abbrev Lv := List (ℕ × ℕ × ℕ × ℕ)

def dflt : ℕ × ℕ × ℕ × ℕ := (4012, 1650, 550, 0)



def okAt (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (i : ℕ) : Bool :=
  levelOK G (i + 1) (lv.getD i dflt).2.2.2 (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 80
    (fun a => some (cvOf r0 ws (i + 1) a))

def allOK (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (lo n : ℕ) : Bool :=
  (List.range n).all fun d => okAt G r0 ws lv (lo + d)




/-! CUT3: kernel-fast evaluators (explicit `Nat.*`, `cond`/`Nat.ble`, no `ite`/instances) with equalities
to the original `Dq`/`freeD`/`lhsV`/`cell`. -/
section CUT3Fast
open Witness6966Free (ZNp ZNm Dq qCp qCm qAp qAm qBp qBm qUp)

def mxN (x y : ℕ) : ℕ := Nat.add y (Nat.sub x y)
def mnN (x y : ℕ) : ℕ := Nat.sub x (Nat.sub x y)

theorem mxN_eq (x y : ℕ) : mxN x y = Gate6966FreeCard.mx x y := by
  rw [Gate6966FreeCard.mx_eq]; unfold mxN; simp only [Nat.add_eq, Nat.sub_eq]; omega
theorem mnN_eq (x y : ℕ) : mnN x y = Gate6966FreeCard.mn x y := by
  rw [Gate6966FreeCard.mn_eq]; unfold mnN; simp only [Nat.sub_eq]; omega

theorem mnN_eqW (x y : ℕ) : mnN x y = Witness6966Free.mn x y := by
  rw [Witness6966Free.mn_eq]; unfold mnN; simp only [Nat.sub_eq]; omega
theorem natmod' (a b : ℕ) : Nat.mod a b = a % b := rfl
theorem natdiv' (a b : ℕ) : Nat.div a b = a / b := rfl

theorem bif_ble (a b : ℕ) {α : Type} (x y : α) : (bif Nat.ble a b then x else y) = if a ≤ b then x else y := by
  by_cases h : a ≤ b
  · simp [Nat.ble_eq_true_of_le h, h]
  · have : Nat.ble a b = false := by simpa [Bool.eq_false_iff, Nat.ble_eq] using h
    simp [this, h]

def tabCp (i : ℕ) : ℕ × ℕ × ℕ := match i with
  | 0 => (864, 360, 864)
  | 1 => (660, 446, 655)
  | 2 => (672, 424, 608)
  | 3 => (756, 414, 783)
  | 4 => (768, 392, 736)
  | _ => (564, 478, 527)
def tabAp (i : ℕ) : ℕ × ℕ × ℕ := match i with
  | 0 => (936, 288, 864)
  | 1 => (732, 374, 601)
  | 2 => (744, 352, 608)
  | 3 => (828, 342, 729)
  | 4 => (840, 320, 736)
  | 5 => (636, 406, 473)
  | 6 => (936, 288, 810)
  | 7 => (732, 374, 655)
  | 8 => (744, 352, 554)
  | 9 => (828, 342, 783)
  | 10 => (840, 320, 682)
  | _ => (636, 406, 527)
def tabBp (i : ℕ) : ℕ × ℕ × ℕ := match i with
  | 0 => (936, 288, 864)
  | 1 => (840, 320, 682)
  | 2 => (744, 352, 608)
  | 3 => (936, 288, 810)
  | 4 => (840, 320, 736)
  | 5 => (744, 352, 554)
  | 6 => (936, 288, 810)
  | 7 => (840, 320, 736)
  | 8 => (744, 352, 554)
  | 9 => (936, 288, 864)
  | 10 => (840, 320, 682)
  | _ => (744, 352, 608)

def kCp (b j : ℕ) : ℕ := Nat.mul (Nat.mul b j) (Nat.add (Nat.mul (Nat.mul 24 j) j) (Nat.add (Nat.mul 252 j) 792))
def kAp (b j : ℕ) : ℕ :=
  let s := Nat.mul b b
  let u := Nat.mul j j
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mul 18 s) s) (Nat.mul (Nat.mul 108 s) u)) (Nat.mul (Nat.mul 7 u) u))
    (Nat.mul (Nat.mul 216 s) j)) (Nat.mul (Nat.mul 36 b) u)) (Nat.mul 36 s)) (Nat.mul (Nat.mul 720 b) j)
def kBp (b j : ℕ) : ℕ :=
  let s := Nat.mul b b
  let u := Nat.mul j j
  Nat.mul j (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mul 216 s) b) (Nat.mul (Nat.mul 24 b) u)) (Nat.mul 864 s)) (Nat.mul 32 u)) (Nat.mul 1008 b))
def kCm (j : ℕ) : ℕ := Nat.mul (Nat.mul j j) (Nat.add (Nat.add (Nat.mul 11 (Nat.mul j j)) (Nat.mul 94 j)) 132)
def kAm (b j : ℕ) : ℕ :=
  let s := Nat.mul b b
  let u := Nat.mul j j
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mul (Nat.mul 72 s) b) j) (Nat.mul (Nat.mul (Nat.mul 48 b) u) j)) (Nat.mul (Nat.mul (Nat.mul 72 s) b) 1))
    (Nat.mul (Nat.mul (Nat.mul 22 u) j) 1)) (Nat.mul 96 u)
def kBm (b j : ℕ) : ℕ :=
  let s := Nat.mul b b
  let u := Nat.mul j j
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mul 126 s) s) (Nat.mul (Nat.mul 108 s) u)) (Nat.mul (Nat.mul 2 u) u))
    (Nat.mul (Nat.mul 504 s) b)) (Nat.mul (Nat.mul 288 b) u)) (Nat.mul 252 s)) (Nat.mul 168 u)
def kUp (b : ℕ) : ℕ :=
  Nat.mul 36 (Nat.mul (Nat.mul (Nat.add b 1) (Nat.add b 2)) (Nat.mul (Nat.add b 3) (Nat.add b 4)))

def lin (c : ℕ × ℕ × ℕ) (b j : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul c.1 b) (Nat.mul c.2.1 j)) c.2.2

def ZNpF (b j : ℕ) : ℕ :=
  bif Nat.ble j b then Nat.add (kCp b j) (lin (tabCp (Nat.mod j 6)) b j)
  else bif Nat.ble (Nat.mul 3 b) j then kUp b
  else bif Nat.ble j (Nat.mul 2 b) then Nat.add (kAp b j) (lin (tabAp (Nat.add (Nat.mul 6 (Nat.mod b 2)) (Nat.mod j 6))) b j)
  else Nat.add (kBp b j) (lin (tabBp (Nat.add (Nat.mul 6 (Nat.mod b 2)) (Nat.mod j 6))) b j)
def ZNmF (b j : ℕ) : ℕ :=
  bif Nat.ble j b then kCm j
  else bif Nat.ble (Nat.mul 3 b) j then 0
  else bif Nat.ble j (Nat.mul 2 b) then kAm b j
  else kBm b j
def DqF (b j : ℕ) : ℕ := Nat.div (Nat.sub (ZNpF b j) (ZNmF b j)) 864

theorem tabC_eq (r b j : ℕ) (hr : r < 6) : Nat.add (kCp b j) (lin (tabCp r) b j) = qCp r b j := by
  interval_cases r <;> simp only [kCp, lin, tabCp, qCp, Nat.add_eq, Nat.mul_eq] <;> ring
theorem tabA_eq (e r b j : ℕ) (he : e < 2) (hr : r < 6) :
    Nat.add (kAp b j) (lin (tabAp (Nat.add (Nat.mul 6 e) r)) b j) = qAp e r b j := by
  interval_cases e <;> interval_cases r <;> simp only [kAp, lin, tabAp, qAp, Nat.add_eq, Nat.mul_eq] <;> ring
theorem tabB_eq (e r b j : ℕ) (he : e < 2) (hr : r < 6) :
    Nat.add (kBp b j) (lin (tabBp (Nat.add (Nat.mul 6 e) r)) b j) = qBp e r b j := by
  interval_cases e <;> interval_cases r <;> simp only [kBp, lin, tabBp, qBp, Nat.add_eq, Nat.mul_eq] <;> ring

theorem ZNpF_eq (b j : ℕ) : ZNpF b j = ZNp b j := by
  have h2 : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h6 : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  unfold ZNpF ZNp
  simp only [bif_ble, natmod', Nat.mul_eq]
  split_ifs
  · exact tabC_eq _ _ _ h6
  · simp only [kUp, qUp, Nat.add_eq, Nat.mul_eq]; ring
  · exact tabA_eq _ _ _ _ h2 h6
  · exact tabB_eq _ _ _ _ h2 h6

theorem ZNmF_eq (b j : ℕ) : ZNmF b j = ZNm b j := by
  have h2 : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h6 : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  unfold ZNmF ZNm
  simp only [bif_ble, Nat.mul_eq]
  split_ifs
  · generalize j % 6 = r at h6; interval_cases r <;> simp only [kCm, qCm, Nat.add_eq, Nat.mul_eq] <;> ring
  · rfl
  · generalize b % 2 = e at h2; generalize j % 6 = r at h6
    interval_cases e <;> interval_cases r <;> simp only [kAm, qAm, Nat.add_eq, Nat.mul_eq] <;> ring
  · generalize b % 2 = e at h2; generalize j % 6 = r at h6
    interval_cases e <;> interval_cases r <;> simp only [kBm, qBm, Nat.add_eq, Nat.mul_eq] <;> ring

theorem DqF_eq (b j : ℕ) : DqF b j = Dq b j := by
  unfold DqF Dq; rw [ZNpF_eq, ZNmF_eq]; rfl

def freeF (b j t : ℕ) : ℕ :=
  let m := mnN t (mnN b (Nat.div j 3))
  Nat.sub (DqF b j) (cond (Nat.ble (Nat.add m 1) (mnN (Nat.div j 3) b))
    (DqF (Nat.sub (Nat.sub b m) 1) (Nat.sub (Nat.sub j (Nat.mul 3 m)) 3)) 0)

theorem freeF_eq (b j t : ℕ) : freeF b j t = Gate6966FreeU3.freeD b j t := by
  unfold freeF Gate6966FreeU3.freeD Witness6966Free.freeE
  simp only [mnN_eqW, DqF_eq, bif_ble, Nat.sub_eq, Nat.add_eq, Nat.mul_eq, natdiv']

def hBF (l : Bool) (yb yj : ℕ) : ℕ := cond l (mxN (mxN yb yj) (mxN yj 3)) (mxN yb yj)
def hJF (l : Bool) (yj : ℕ) : ℕ := cond l (mxN yj 3) yj
def hTF (l : Bool) (yj yt : ℕ) : ℕ := cond l (mxN (mnN yt (Nat.div yj 3)) 1) (mnN yt (Nat.div yj 3))

theorem hBF_eq (l : Bool) (a b : ℕ) : hBF l a b = hB l a b := by
  cases l <;> simp only [hBF, hB, mxN_eq, Bool.cond_true, Bool.cond_false]
theorem hJF_eq (l : Bool) (a : ℕ) : hJF l a = hJ l a := by
  cases l <;> simp only [hJF, hJ, mxN_eq, Bool.cond_true, Bool.cond_false]
theorem hTF_eq (l : Bool) (a b : ℕ) : hTF l a b = hT l a b := by
  cases l <;> simp only [hTF, hT, mxN_eq, mnN_eq, natdiv', Bool.cond_true, Bool.cond_false]

def lhsF (P : Pr) (yb yj yt hb hj ht : ℕ) : ℕ :=
  let a0 := Nat.sub (hBF P.lift yb yj) (hJF P.lift yj)
  let a1 := Nat.sub (hJF P.lift yj) (Nat.mul 3 (hTF P.lift yj yt))
  let a2 := hTF P.lift yj yt
  let e0 := Nat.sub (hBF P.lift hb hj) (hJF P.lift hj)
  let e1 := Nat.sub (hJF P.lift hj) (Nat.mul 3 (hTF P.lift hj ht))
  let e2 := hTF P.lift hj ht
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
  (Nat.mul a0 (Nat.add (Nat.add (Nat.mul P.m00 a0) (Nat.mul P.m01 a1)) (Nat.mul P.m02 a2)))
  (Nat.mul a1 (Nat.add (Nat.mul P.m11 a1) (Nat.mul P.m12 a2))))
  (Nat.mul (Nat.mul P.m22 a2) a2))
  (Nat.mul e0 (Nat.add (Nat.add (Nat.mul P.q00 a0) (Nat.mul P.q01 a1)) (Nat.mul P.q02 a2))))
  (Nat.mul e1 (Nat.add (Nat.add (Nat.mul P.q10 a0) (Nat.mul P.q11 a1)) (Nat.mul P.q12 a2))))
  (Nat.mul e2 (Nat.add (Nat.add (Nat.mul P.q20 a0) (Nat.mul P.q21 a1)) (Nat.mul P.q22 a2))))
  (Nat.mul P.w0 e0)) (Nat.mul P.w1 e1)) (Nat.mul P.w2 e2)) (Nat.mul P.v0 a0)) (Nat.mul P.v1 a1)) (Nat.mul P.v2 a2)) P.c0

theorem lhsF_eq (P : Pr) (yb yj yt hb hj ht : ℕ) : lhsF P yb yj yt hb hj ht = lhsV P yb yj yt hb hj ht := by
  unfold lhsF lhsV
  simp only [hBF_eq, hJF_eq, hTF_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]

def cellF (P : Pr) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _, _, _ => false
  | f + 1, l0, l1, l2, h0, h1, h2 =>
    bif Nat.blt (mnN h2 (mnN (Nat.div h1 3) h0)) l2 || Nat.blt (Nat.add (Nat.mul 2 h0) (mnN h2 (mnN (Nat.div h1 3) h0))) l1 then true
    else bif Nat.ble (freeF (Nat.sub P.t0 l0) (Nat.sub P.t1 l1) (Nat.sub P.t2 l2)) P.W then true
    else bif Nat.ble (lhsF P (Nat.sub P.t0 l0) (Nat.sub P.t1 l1) (Nat.sub P.t2 l2) h0 h1 h2) P.rhs then true
    else bif Nat.beq l0 h0 && Nat.beq l1 h1 && Nat.beq l2 h2 then false
    else bif Nat.ble (Nat.sub h1 l1) (Nat.sub h0 l0) && Nat.ble (Nat.sub h2 l2) (Nat.sub h0 l0) then
      cellF P f l0 l1 l2 (Nat.div (Nat.add l0 h0) 2) h1 h2 && cellF P f (Nat.add (Nat.div (Nat.add l0 h0) 2) 1) l1 l2 h0 h1 h2
    else bif Nat.ble (Nat.sub h2 l2) (Nat.sub h1 l1) then
      cellF P f l0 l1 l2 h0 (Nat.div (Nat.add l1 h1) 2) h2 && cellF P f l0 (Nat.add (Nat.div (Nat.add l1 h1) 2) 1) l2 h0 h1 h2
    else
      cellF P f l0 l1 l2 h0 h1 (Nat.div (Nat.add l2 h2) 2) && cellF P f l0 l1 (Nat.add (Nat.div (Nat.add l2 h2) 2) 1) h0 h1 h2

theorem cellF_eq (P : Pr) : ∀ (fuel l0 l1 l2 h0 h1 h2 : ℕ), cellF P fuel l0 l1 l2 h0 h1 h2 = cell P fuel l0 l1 l2 h0 h1 h2 := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _; rfl
  | succ f ih =>
    intro l0 l1 l2 h0 h1 h2
    unfold cellF cell
    simp only [mnN_eq, freeF_eq, lhsF_eq, natdiv', Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ih]

def levelOKF (G : Gt) (r W B0 B1 B2 fuel : ℕ) (cv : ℕ → Option (ℕ × ℕ)) : Bool :=
  (List.range (Nat.add (mnN (Nat.div B0 G.lb) (mnN (Nat.div B1 G.lj) (Nat.div B2 G.lt))) 1)).all fun a =>
    bif Nat.ble r a then Nat.ble (freeF (Nat.sub B0 (Nat.mul a G.lb)) (Nat.sub B1 (Nat.mul a G.lj)) (Nat.sub B2 (Nat.mul a G.lt))) W
    else match cv a with
      | none => Nat.ble (freeF (Nat.sub B0 (Nat.mul a G.lb)) (Nat.sub B1 (Nat.mul a G.lj)) (Nat.sub B2 (Nat.mul a G.lt))) W
      | some c => cellF (mkPr G r a c.1 c.2 W B0 B1 B2) fuel 0 0 0 (Nat.sub B0 (Nat.mul a G.lb)) (Nat.sub B1 (Nat.mul a G.lj)) (Nat.sub B2 (Nat.mul a G.lt))

theorem levelOKF_eq (G : Gt) (r W B0 B1 B2 fuel : ℕ) (cv : ℕ → Option (ℕ × ℕ)) :
    levelOKF G r W B0 B1 B2 fuel cv = levelOK G r W B0 B1 B2 fuel cv := by
  unfold levelOKF levelOK
  simp only [mnN_eq, Gate6966FreeCard.mn_eq, freeF_eq, cellF_eq, natdiv', Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  rfl





end CUT3Fast



































/-! PERF (69.62): the `Gate6966Amb.compute` lower bound evaluated in Nat. `cumulative` over ℤ is
slow in the kernel (Int.div/mod, 8 `denominator` calls per count); `denN`/`dg` are the same
quantities with guarded Nat subtraction. -/
def denN (u : ℕ) : ℕ :=
  1 + (u % 6) * (u % 6 + 1) / 2 + (u / 6) * (22 + 7 * (u % 6) + (u % 6) * (u % 6 - 1) / 2) +
    (57 + 6 * (u % 6)) * ((u / 6) * (u / 6 - 1) / 2) + 6 * (u / 6) * (u / 6 - 1) * (u / 6 - 2)

def dg (v c : ℕ) : ℕ := bif Nat.ble c v then denN (v - c) else 0

def cumPV (V d : ℕ) : ℕ := dg V 0 + dg V (2 * d + 3) + dg V (2 * d + 4) + dg V (2 * d + 5)

def cumQV (V d : ℕ) : ℕ := dg V (d + 1) + dg V (d + 2) + dg V (d + 3) + dg V (3 * d + 6)

def cumP (d u : ℕ) : ℕ := cumPV (min u (3 * d)) d

def cumQ (d u : ℕ) : ℕ := cumQV (min u (3 * d)) d

def cappedN (d u c : ℕ) : ℤ :=
  ((cumP d u : ℤ) - cumQ d u) -
    (bif Nat.ble (c + 1) d && Nat.ble (3 * (c + 1)) u then
      (cumP (d - c - 1) (u - 3 * (c + 1)) : ℤ) - cumQ (d - c - 1) (u - 3 * (c + 1)) else 0)





















































































def sumUpTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumUpTo f n + f n

theorem sumUpTo_eq (f : ℕ → ℤ) (n : ℕ) : sumUpTo f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumUpTo]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

def blockN (b j t k : ℕ) : ℤ :=
  ((Gate6966Amb.stop b k - Gate6966Amb.start k : ℕ) : ℤ) * cappedN (Gate6966Amb.padGrade b k) (Gate6966Amb.index j) t

def computeN (b j t : ℕ) : ℤ := sumUpTo (blockN b j t) (Gate6966Amb.chunks b)









def ambLB (b j t : ℕ) : ℤ :=
  bif Nat.ble 4012 b && Nat.ble 1650 j && Nat.ble 550 t then (Low6966Prices.symbolCount : ℤ) else computeN b j t










def lsum (lv : Lv) (i : ℕ) : ℤ :=
  (Low6966Prices.symbolCount : ℤ) - ambLB (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 +
    ((lv.getD i dflt).2.2.2 : ℤ)




end Gate6966Cell

end Merged_Gate6966Assm
