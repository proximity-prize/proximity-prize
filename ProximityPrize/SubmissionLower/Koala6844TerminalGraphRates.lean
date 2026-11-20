import ProximityPrize.SubmissionLower.Koala6844TerminalRates


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped BigOperators
open RCN095 RCN146 RCN327 LocatorHybridCells
open MovingFiberThreeSources6811 MovingFiberArithmeticBase6815
open Koala6844Receipts

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

def graphScope (a b c : ℕ) : Flag := ⟨a+3,a+3+(b+2),a+3+(b+2)+c⟩

theorem graphScope_exists (g : Flag) (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t) :
    ∃ a b c, g = graphScope a b c := by
  refine ⟨g.r-3,g.y-g.r-2,g.t-g.y,?_⟩
  cases g with
  | mk r y t =>
    change 3 ≤ r at hr
    change r+2 ≤ y at hy
    change y ≤ t at ht
    change Koala6844Receipts.Flag.mk r y t = Koala6844Receipts.Flag.mk (r-3+3) (r-3+3+(y-r-2+2)) (r-3+3+(y-r-2+2)+(t-y))
    rw [Koala6844Receipts.Flag.mk.injEq]
    omega

private theorem graphNormal_scope (a b c : ℕ) :
    geometryFlag (graphNormal (graphScope a b c)) = normal a b c := by
  have ha : a+3-3=a := by omega
  have hb : a+3+(b+2)-(a+3)-2=b := by omega
  have hc : a+3+(b+2)+c-(a+3+(b+2))=c := by omega
  simp only [graphScope,graphNormal,geometryFlag,normal,ha,hb,hc]

private theorem graphRaw_scope (a b c : ℕ) :
    geometryFlag (graphRaw (graphScope a b c)) = raw a b c := by
  have ha : a+3-3=a := by omega
  have hb : a+3+(b+2)-(a+3)-2=b := by omega
  have hc : a+3+(b+2)+c-(a+3+(b+2))=c := by omega
  simp only [graphScope,graphRaw,geometryFlag,raw,ha,hb,hc]

private theorem graphFirst_scope (j : Fin 3) (a b c : ℕ) :
    geometryFlag (graphFirstCut (graphScope a b c) j.val) = HFreeDirArith6815.firstDir j a b c := by
  have ha : a+3-3=a := by omega
  have hb : a+3+(b+2)-(a+3)-2=b := by omega
  have hc : a+3+(b+2)+c-(a+3+(b+2))=c := by omega
  cases a with
  | zero =>
    rw [HFreeDirArith6815.firstDir_zero]
    fin_cases j <;> simp [graphFirstCut,graphScope,geometryFlag,HFreeDirArith6815.firstLo,hc]
  | succ a =>
    rw [HFreeDirArith6815.firstDir_succ]
    fin_cases j <;> simp [graphFirstCut,graphScope,geometryFlag,HFreeDirArith6815.firstHi,ha,hc]

private theorem direction_eq (j : Fin 3) : geometryFlag (axisFlag j.val) = direction j := by
  fin_cases j <;> rfl

private theorem weight_eq (f : FlagIncrements) (j : Fin 3) :
    weight (geometryFlag f) j = f.axis j.val := by
  fin_cases j <;> rfl

private theorem move_scale (scale d u v : ℕ) (hd : 0 < d) (hs : 3*d ∣ scale) :
    (524288*u+3*65539*v)*(scale/3)/d =
      524288*u*(scale/(3*d))+65539*v*(scale/d) := by
  obtain ⟨q, rfl⟩ := hs
  have h₁ : (3 * d * q) / 3 = d*q := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < (3 : ℕ))]
  have h₂ : (3 * d * q) / (3*d) = q := Nat.mul_div_cancel_left _ (Nat.mul_pos (by decide) hd)
  have h₃ : (3 * d * q) / d = 3*q := by
    rw [mul_comm 3 d, mul_assoc, Nat.mul_div_cancel_left _ hd]
  rw [h₁,h₂,h₃]
  have he : (524288*u+3*65539*v) * (d*q) = d*((524288*u+3*65539*v)*q) := by ring
  rw [he,Nat.mul_div_cancel_left _ hd]
  ring

def graphMove (g : Flag) (src : SourceShape) (j : Fin 3) : FlagIncrements :=
  let normal := (graphNormal g).axis j.val
  let raw := (graphRaw g).axis j.val
  let weight := (524288 * normal + 3 * 65539 * raw) * (graphScale / 3)
  FlagIncrements.map fun i => weight / (src.k + 1) * mixedRate i (axisFlag j.val) src.graphIncrement

private theorem basis_eq (a b c : ℕ) (left : FlagDegree) :
    dot (increments left) (graphBasis (graphScope a b c)) =
      ∑ j : Fin 3, graphScale/3 * weight (normal a b c) j *
        flagMixed left (HFreeDirArith6815.firstDir j a b c) (direction j) := by
  let g := graphScope a b c
  have h (j : Fin 3) : dot (increments left)
      (FlagIncrements.map (fun i => mixedRate i (graphFirstCut g j.val) (axisFlag j.val))) =
      flagMixed left (HFreeDirArith6815.firstDir j a b c) (direction j) := by
    rw [dot_mixed_eq,geometryFlag_increments,graphFirst_scope,direction_eq]
  rw [Fin.sum_univ_three, ← h 0, ← h 1, ← h 2,
    ← graphNormal_scope a b c]
  simp only [weight_eq]
  simp only [g,graphBasis,dot,increments,FlagIncrements.map,FlagIncrements.axis,Fin.val_zero,
    Fin.val_one,show (2 : Fin 3).val = 2 by decide,Nat.reduceEqDiff,ite_true,ite_false]
  ring

private theorem move_eq (a b c : ℕ) (left : FlagDegree) (src : SourceShape) (j : Fin 3)
    (hdiv : 3*(src.k+1) ∣ graphScale) :
    dot (increments left) (graphMove (graphScope a b c) src j) =
      (524288 * weight (normal a b c) j * (graphScale/(3*(src.k+1))) +
        65539 * weight (raw a b c) j * (graphScale/(src.k+1))) *
      flagMixed left (direction j) (geometryFlag src.graphIncrement) := by
  let g := graphScope a b c
  let n := (graphNormal g).axis j.val
  let r := (graphRaw g).axis j.val
  have hn : n = weight (normal a b c) j := by
    rw [← graphNormal_scope a b c,weight_eq]
  have hr : r = weight (raw a b c) j := by
    rw [← graphRaw_scope a b c,weight_eq]
  rw [← hn, ← hr, ← move_scale graphScale (src.k+1) n r (by omega) hdiv,
    ← direction_eq, ← geometryFlag_increments left, ← dot_mixed_eq]
  simp only [graphMove,n,r,g,dot,FlagIncrements.map,geometryFlag_increments]
  ring

theorem graph_numerator_eq {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (source : Fin 3 → Source F) (shape : Fin 3 → SourceShape) (g : Flag)
    (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t)
    (hd : ∀ j, (source j).d = (shape j).k+1)
    (hf : ∀ j, (source j).flag = geometryFlag (shape j).graphIncrement)
    (hdiv : ∀ j, 3*(shape j).k+3 ∣ graphScale) (left : FlagDegree) :
    HFreeDir6813.numeratorDir source graphScale g.t g.y g.r left =
      dot (increments left) (graphBasis g) + ∑ j : Fin 3, dot (increments left) (graphMove g (shape j) j) := by
  obtain ⟨a,b,c,rfl⟩ := graphScope_exists g hr hy ht
  let cfg : Fin 3 → MovingFiberProfile6815.Params := fun j =>
    ⟨(shape j).m,(source j).B,(source j).s,(source j).U,(source j).T,(source j).k,(source j).n0⟩
  have hbase : HFreeDir6813.numeratorDir source graphScale (graphScope a b c).t (graphScope a b c).y
      (graphScope a b c).r left = HFreeDirArith6815.numberDir cfg graphScale (graphScope a b c).t
        (graphScope a b c).y (graphScope a b c).r left := rfl
  rw [hbase,show (graphScope a b c).t = a+3+(b+2)+c from rfl, show (graphScope a b c).y = a+3+(b+2) from rfl,
    show (graphScope a b c).r = a+3 from rfl,HFreeDirArith6815.numberDir_coordinates,basis_eq]
  simp only [HFreeDirArith6815.graphDir, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hh : 3*((shape j).k+1) ∣ graphScale := by simpa only [Nat.mul_add,Nat.mul_one] using hdiv j
  rw [move_eq a b c left (shape j) j hh]
  change (524288 * weight (normal a b c) j * (graphScale/(3*(source j).d)) +
        65539 * weight (raw a b c) j * (graphScale/(source j).d)) *
       flagMixed left (direction j) (source j).flag = _
  rw [hd j,hf j]

theorem graph_identity_eq (g : Flag) (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t)
    (left : FlagDegree) :
    identityCharge graphScale g.t g.y g.r left = dot (increments left) (graphIdentity g) := by
  obtain ⟨a,b,c,rfl⟩ := graphScope_exists g hr hy ht
  have ha : a+3-3=a := by omega
  have hb : a+3+(b+2)-(a+3)-2=b := by omega
  have hc : a+3+(b+2)+c-(a+3+(b+2))=c := by omega
  have hB : a+3+(b+2)-(a+3)-1=b+1 := by omega
  have hS : a+3-2=a+1 := by omega
  have hg : agreementGap = 49888 := by decide
  have hn : nodes-degree = 131073 := by decide
  have hp : pencilLimit = 81186 := by decide
  unfold identityCharge
  rw [show RCN327.w = Lower80788.HybridIdentityC2.w from rfl,
    Lower80788.HybridIdentityC2.identityDegree_linear]
  simp only [graphScope,graphIdentity,dot,increments,ha,hb,hc,hB,hS,cellA,cellB,cellS,hg,hn,hp]
  ring

end ProximityPrize.SubmissionLower.Koala6844Terminal
