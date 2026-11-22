import ProximityPrize.SubmissionLower.KoalaAffineTriangle
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace KoalaPiecewiseTriangle
open Finset
open scoped BigOperators

structure Line where
  a : ℤ
  d : ℤ

def Line.at (f : Line) (x : ℤ) : ℤ := f.a + f.d*x

def Line.sub (f g : Line) : Line := ⟨f.a-g.a,f.d-g.d⟩

inductive Expr
  | affine (f : Line)
  | lower (f g : Expr)
  | upper (f g : Expr)
  | sub (f g : Expr)

def Expr.at : Expr → ℤ → ℤ
  | .affine f, x => f.at x
  | .lower f g, x => min (f.at x) (g.at x)
  | .upper f g, x => max (f.at x) (g.at x)
  | .sub f g, x => f.at x - g.at x

def Expr.const (a : ℤ) : Expr := .affine ⟨a,0⟩

private def ordered (f g : Line) (lo hi : ℤ) : Prop :=
  f.at lo ≤ g.at lo ∧ f.at hi ≤ g.at hi

private instance (f g : Line) (lo hi : ℤ) : Decidable (ordered f g lo hi) := by
  unfold ordered
  infer_instance

private theorem between {f g : Line} {lo hi x : ℤ}
    (h : ordered f g lo hi) (hl : lo ≤ x) (hu : x ≤ hi) : f.at x ≤ g.at x := by
  unfold ordered Line.at at *
  by_cases hs : f.d ≤ g.d
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hl), h.1]
  · have hs' : g.d ≤ f.d := le_of_not_ge hs
    nlinarith [mul_nonneg (sub_nonneg.mpr hs') (sub_nonneg.mpr hu), h.2]

private def specialize (lo hi : ℤ) : Expr → Option Line
  | .affine f => some f
  | .lower f g => do
      let F ← specialize lo hi f
      let G ← specialize lo hi g
      if ordered F G lo hi then some F
      else if ordered G F lo hi then some G else none
  | .upper f g => do
      let F ← specialize lo hi f
      let G ← specialize lo hi g
      if ordered F G lo hi then some G
      else if ordered G F lo hi then some F else none
  | .sub f g => do
      let F ← specialize lo hi f
      let G ← specialize lo hi g
      some (F.sub G)

private theorem specialize_at {e : Expr} {lo hi x : ℤ} {f : Line}
    (h : specialize lo hi e = some f) (hl : lo ≤ x) (hu : x ≤ hi) : e.at x = f.at x := by
  induction e generalizing f with
  | affine F =>
      have hf : F = f := Option.some.inj h
      subst f
      rfl
  | lower E G ihE ihG =>
      cases hF : specialize lo hi E with
      | none => simp [specialize, hF] at h
      | some F =>
        cases hH : specialize lo hi G with
        | none => simp [specialize, hF, hH] at h
        | some H =>
          simp only [specialize, hF, hH] at h
          change (if ordered F H lo hi then some F
            else if ordered H F lo hi then some H else none) = some f at h
          simp only [Expr.at, ihE hF, ihG hH]
          split at h
          · rename_i ho
            exact (min_eq_left (between ho hl hu)).trans
              (congrArg (fun l : Line => l.at x) (Option.some.inj h))
          · split at h
            · rename_i ho
              exact (min_eq_right (between ho hl hu)).trans
                (congrArg (fun l : Line => l.at x) (Option.some.inj h))
            · cases h
  | upper E G ihE ihG =>
      cases hF : specialize lo hi E with
      | none => simp [specialize, hF] at h
      | some F =>
        cases hH : specialize lo hi G with
        | none => simp [specialize, hF, hH] at h
        | some H =>
          simp only [specialize, hF, hH] at h
          change (if ordered F H lo hi then some H
            else if ordered H F lo hi then some F else none) = some f at h
          simp only [Expr.at, ihE hF, ihG hH]
          split at h
          · rename_i ho
            exact (max_eq_right (between ho hl hu)).trans
              (congrArg (fun l : Line => l.at x) (Option.some.inj h))
          · split at h
            · rename_i ho
              exact (max_eq_left (between ho hl hu)).trans
                (congrArg (fun l : Line => l.at x) (Option.some.inj h))
            · cases h
  | sub E G ihE ihG =>
      cases hF : specialize lo hi E with
      | none => simp [specialize, hF] at h
      | some F =>
        cases hH : specialize lo hi G with
        | none => simp [specialize, hF, hH] at h
        | some H =>
          simp only [specialize, hF, hH] at h
          change some (F.sub H) = some f at h
          rw [← Option.some.inj h]
          simp only [Expr.at, ihE hF, ihG hH, Line.at, Line.sub]
          ring

private def direct (e : Expr) (lo : ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range n, KoalaAffineTriangle.twiceTriangle (e.at (lo+i))

private def run (e : Expr) : ℕ → ℤ → ℕ → ℤ
  | 0, lo, n => direct e lo n
  | k+1, lo, n =>
      if n = 0 then 0 else
        match specialize lo (lo + n - 1) e with
        | some f => KoalaAffineTriangle.sum f.a f.d lo n
        | none =>
            let mid := n/2
            run e k lo mid + run e k (lo+mid) (n-mid)

private theorem run_eq (e : Expr) (fuel : ℕ) (lo : ℤ) (n : ℕ) :
    run e fuel lo n = ∑ i ∈ range n, KoalaAffineTriangle.twiceTriangle (e.at (lo+i)) := by
  induction fuel generalizing lo n with
  | zero => rfl
  | succ k ih =>
      rw [run]
      by_cases hn : n = 0
      · simp [hn]
      rw [ite_eq_right hn]
      cases h : specialize lo (lo+n-1) e with
      | some f =>
          change KoalaAffineTriangle.sum f.a f.d lo n = _
          rw [KoalaAffineTriangle.sum_eq_range]
          apply sum_congr rfl
          intro i hi
          have hlt := mem_range.mp hi
          rw [specialize_at h (by omega) (by omega)]
          rfl
      | none =>
          change run e k lo (n/2) + run e k (lo+(n/2 : ℕ)) (n-n/2) = _
          rw [ih,ih]
          let mid := n/2
          have hm : mid ≤ n := Nat.div_le_self _ _
          conv_rhs => rw [← Nat.add_sub_of_le hm, sum_range_add]
          congr 1
          apply sum_congr rfl
          intro i _
          congr 1
          dsimp [mid]
          push_cast
          ring

/-- Sum the positive twice-triangle of a piecewise affine expression over a finite interval. -/
def sum (e : Expr) (lo : ℤ) (n : ℕ) : ℤ :=
  run e (n.log2+1) lo n

theorem sum_eq (e : Expr) (lo : ℤ) (n : ℕ) :
    sum e lo n = ∑ i ∈ range n, KoalaAffineTriangle.twiceTriangle (e.at (lo+i)) :=
  run_eq ..

#print axioms sum_eq
structure BandCuts where
  l0 : ℤ
  q1 : ℤ
  first : ℤ
  last : ℤ

private def BandCuts.cutAt (b : BandCuts) (l q k : ℤ) : ℤ :=
  let tri := KoalaAffineTriangle.twiceTriangle
  tri (l-k-q) - tri (b.l0-k-q) - (tri (l-k-b.q1)-tri (b.l0-k-b.q1))

def BandCuts.at (b : BandCuts) (l q : ℤ) : ℤ :=
  b.cutAt l q b.first - b.cutAt l q b.last

private def lineCutSum (b : BandCuts) (l q : Line) (k lo : ℤ) (n : ℕ) : ℤ :=
  let sum := KoalaAffineTriangle.sumFast
  sum (l.a-k-q.a) (l.d-q.d) lo n -
    sum (b.l0-k-q.a) (-q.d) lo n -
    (sum (l.a-k-b.q1) l.d lo n -
      (n : ℤ) * KoalaAffineTriangle.twiceTriangle (b.l0-k-b.q1))

private theorem lineCutSum_eq (b : BandCuts) (l q : Line) (k lo : ℤ) (n : ℕ) :
    lineCutSum b l q k lo n =
      ∑ i ∈ range n, b.cutAt (l.at (lo+i)) (q.at (lo+i)) k := by
  unfold lineCutSum
  simp only [KoalaAffineTriangle.sumFast_eq_range]
  have hconst : (n : ℤ) * KoalaAffineTriangle.twiceTriangle (b.l0-k-b.q1) =
      ∑ _ ∈ range n, KoalaAffineTriangle.twiceTriangle (b.l0-k-b.q1) := by
    simp [nsmul_eq_mul]
  rw [hconst]
  simp only [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  simp only [BandCuts.cutAt, Line.at]
  ring_nf

private def lineBandSum (b : BandCuts) (l q : Line) (lo : ℤ) (n : ℕ) : ℤ :=
  lineCutSum b l q b.first lo n - lineCutSum b l q b.last lo n

private theorem lineBandSum_eq (b : BandCuts) (l q : Line) (lo : ℤ) (n : ℕ) :
    lineBandSum b l q lo n =
      ∑ i ∈ range n, b.at (l.at (lo+i)) (q.at (lo+i)) := by
  simp only [lineBandSum, lineCutSum_eq, ← sum_sub_distrib, BandCuts.at]

private def bandRange (b : BandCuts) (l q : Expr) (lo : ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range n, b.at (l.at (lo+i)) (q.at (lo+i))

private theorem bandRange_add (b : BandCuts) (l q : Expr) (lo : ℤ) (n m : ℕ) :
    bandRange b l q lo (n+m) =
      bandRange b l q lo n + bandRange b l q (lo+(n : ℤ)) m := by
  unfold bandRange
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i _
  simp [Nat.cast_add, add_assoc, add_comm, add_left_comm]

private def runBand (b : BandCuts) (l q : Expr) : ℕ → ℤ → ℕ → ℤ
  | 0, lo, n => bandRange b l q lo n
  | fuel+1, lo, n =>
    if n = 0 then 0 else
      match specialize lo (lo+n-1) l, specialize lo (lo+n-1) q with
      | some L, some Q => lineBandSum b L Q lo n
      | _, _ =>
        let j := n/2
        runBand b l q fuel lo j + runBand b l q fuel (lo+(j : ℤ)) (n-j)

private theorem runBand_eq (b : BandCuts) (l q : Expr) (fuel : ℕ) (lo : ℤ) (n : ℕ) :
    runBand b l q fuel lo n = bandRange b l q lo n := by
  induction fuel generalizing lo n with
  | zero => rfl
  | succ fuel ih =>
    rw [runBand]
    by_cases hn : n = 0
    · simp [hn, bandRange]
    rw [ite_eq_right hn]
    have hrest : runBand b l q fuel lo (n/2) +
        runBand b l q fuel (lo+((n/2 : ℕ) : ℤ)) (n-n/2) = bandRange b l q lo n := by
      rw [ih, ih, ← bandRange_add, Nat.add_sub_of_le (Nat.div_le_self _ _)]
    cases hL : specialize lo (lo+n-1) l with
    | none => exact hrest
    | some L =>
      cases hQ : specialize lo (lo+n-1) q with
      | none => exact hrest
      | some Q =>
        change lineBandSum b L Q lo n = _
        rw [lineBandSum_eq, bandRange]
        apply sum_congr rfl
        intro i hi
        have h := mem_range.mp hi
        rw [specialize_at hL (by omega) (by omega), specialize_at hQ (by omega) (by omega)]

/-- Evaluate the two cut fees using the same intervals for both coordinate bounds. -/
def sumBand (b : BandCuts) (l q : Expr) (lo : ℤ) (n : ℕ) : ℤ :=
  runBand b l q (n.log2+1) lo n

theorem sumBand_eq (b : BandCuts) (l q : Expr) (lo : ℤ) (n : ℕ) :
    sumBand b l q lo n = ∑ i ∈ range n, b.at (l.at (lo+i)) (q.at (lo+i)) :=
  runBand_eq ..

theorem band_at (b : BandCuts) (l q : ℤ) :
    b.at l q =
      (KoalaAffineTriangle.twiceTriangle (l-b.first-q) - KoalaAffineTriangle.twiceTriangle (b.l0-b.first-q) -
        (KoalaAffineTriangle.twiceTriangle (l-b.first-b.q1)-KoalaAffineTriangle.twiceTriangle (b.l0-b.first-b.q1))) -
      (KoalaAffineTriangle.twiceTriangle (l-b.last-q) - KoalaAffineTriangle.twiceTriangle (b.l0-b.last-q) -
        (KoalaAffineTriangle.twiceTriangle (l-b.last-b.q1)-KoalaAffineTriangle.twiceTriangle (b.l0-b.last-b.q1))) :=
  rfl

#print axioms sumBand_eq
end KoalaPiecewiseTriangle
