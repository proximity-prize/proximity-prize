import ProximityPrize.SubmissionLower.R6970ExactRankArithmetic
import ProximityPrize.SubmissionLower.R6970PrimaryPointwiseBill

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace Research6970.Height2313.Lower6960.Prefix6969Main.RankBill

open Research6970.ExactRank
open Finset
open P1_7_4 (running weightedBill dotQ)
open P1_7_4_3 (mix)
open scoped BigOperators

def increment (s : Plan) (p : Pricing) (i : ℕ) (k : Fin 4) : ℚ :=
  running (chargedWeight s p) (i+1) k - running (chargedWeight s p) i k

def terms (s : Plan) (p : Pricing) (k : Fin 4) : List Term :=
  (List.range s.count).map fun i => (s.history i k, increment s p i k)

def frame (s : Plan) (p : Pricing) (band : Band) : Frame :=
  ⟨band.lambda, band.mu, s.initialCap 1, s.initialCap 2, terms s p 1, terms s p 2⟩

def commonLoss (s : Plan) (p : Pricing) : ℚ :=
  ∑ i∈range s.count, (increment s p i 0 * s.history i 0 + increment s p i 3 * s.history i 3)

private theorem nonnegativeTerms (s : Plan) (p : Pricing) (k : Fin 4) :
    ∀ t ∈ terms s p k, 0 ≤ t.2 := by
  intro t h
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
  unfold increment
  rw [running]
  exact sub_nonneg.mpr (le_max_left _ _)

private theorem range_sum (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i∈range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem pay_terms (s : Plan) (p : Pricing) (k : Fin 4) (c x : ℚ) :
    pay c x (terms s p k) =
      ∑ i∈range s.count, increment s p i k * min (s.history i k) (c-x) := by
  unfold pay terms
  rw [List.map_map]
  exact range_sum (fun i => increment s p i k * min (s.history i k) (c-x)) s.count

private theorem cuts_eq (s : Plan) (p : Pricing) (band : Band) (j b : ℕ)
    (hj : j ≤ s.initialCap 1) (hb : b ≤ s.initialCap 2) :
    weightedBill s.count (chargedWeight s p) (capsAfter s j b) =
      commonLoss s p + pay (frame s p band).capX j (frame s p band).xs +
        pay (frame s p band).capY b (frame s p band).ys := by
  unfold frame commonLoss weightedBill
  simp only [pay_terms, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change dotQ (increment s p i) (capsAfter s j b i) = _
  simp only [dotQ,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change increment s p i 0 * capsAfter s j b i 0 +
    (increment s p i 1 * capsAfter s j b i 1 +
    (increment s p i 2 * capsAfter s j b i 2 + increment s p i 3 * capsAfter s j b i 3)) = _
  have h01 : (0:Fin 4) ≠ 1 := by decide
  have h02 : (0:Fin 4) ≠ 2 := by decide
  have h21 : (2:Fin 4) ≠ 1 := by decide
  have h31 : (3:Fin 4) ≠ 1 := by decide
  have h32 : (3:Fin 4) ≠ 2 := by decide
  simp only [capsAfter,h01,h02,h21,h31,h32,ite_false,ite_true,Nat.cast_sub hj,Nat.cast_sub hb]
  ring

private theorem fixed_le_rank (band : Band) (j b : ℕ) (h : j ≤ b) :
    (band.fixedFee (b+2) (min (j+1) (b+2)) : ℚ) ≤ rank band.lambda band.mu j b := by
  let B := b+2
  let J := j+1
  have hJB : J ≤ B := by dsimp [J,B]; omega
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hJ : 1 ≤ 2*J := by dsimp [J]; omega
  let top := band.mu + 2*band.lambda*(B-1 : ℕ)
  let edge := band.lambda*(2*J-1 : ℕ)
  let q := mix B J top (min top edge)
  have a := band.lambda_nonneg
  have z := band.mu_nonneg
  have qp : 0 ≤ q := by
    have ht : 0 ≤ top := by unfold top; positivity
    have he : 0 ≤ edge := by unfold edge; positivity
    unfold q mix
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_min ht he)) (mul_nonneg (Nat.cast_nonneg _) ht)
  have qn : 0 ≤ q.ceil := by
    exact_mod_cast (qp.trans (Rat.le_ceil : q ≤ (q.ceil : ℚ)))
  have qc : (q.ceil.toNat : ℚ) = (q.ceil : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg qn
  have upper : (q.ceil : ℚ) ≤ q+1 := (Rat.ceil_lt (x:=q)).le
  have mm : q ≤ mix B J top edge := by
    unfold q mix
    exact add_le_add (mul_le_mul_of_nonneg_left (min_le_right top edge) (Nat.cast_nonneg _)) le_rfl
  have gain : 0 ≤ band.lambda * ((B : ℚ)+(J : ℚ)) := by positivity
  change (band.fixedFee B (min J B) : ℚ) ≤ _
  rw [min_eq_left hJB, Band.fixedFee_eq]
  change ((q.ceil.toNat + B^2 : ℕ) : ℚ) ≤ _
  rw [Nat.cast_add, qc, Nat.cast_pow]
  unfold rank at *
  unfold mix top edge at mm
  simp only [Nat.cast_sub hJB, Nat.cast_sub hB, Nat.cast_sub hJ, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at mm
  simp only [B,J,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at *
  nlinarith only [upper,mm,gain]

private theorem round_le {q : ℚ} {n : ℕ} (h : q ≤ n) : q.ceil.toNat ≤ n := by
  have rounded : q.ceil ≤ (n:ℤ) := Rat.ceil_le_iff.mpr (by exact_mod_cast h)
  simpa only [Int.toNat_natCast] using Int.toNat_le_toNat rounded

theorem exact_of_checked (s : Plan) (p : Pricing) (band : Band)
    (f : Frame) (first : Vertex) (rest : List Vertex) (limit : ℚ) (lossCap : ℕ)
    (fit : frame s p band = f)
    (cert : ExactRank.checked f limit first rest)
    (payLimit : limit + commonLoss s p + s.seedLimit ≤ lossCap) :
    Pointwise s p band lossCap := by
  intro j b hj hb jb
  rw [← fit] at cert
  have h := bound (f:=frame s p band) (x:=(j:ℚ)) (y:=(b:ℚ)) band.lambda_nonneg
    (nonnegativeTerms s p 1) (nonnegativeTerms s p 2)
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hj) (Nat.cast_nonneg _) (Nat.cast_le.mpr hb) cert
  have rank := fixed_le_rank band j b jb
  have cuts := cuts_eq s p band j b hj hb
  unfold cellLoss
  have q : (band.fixedFee (b+2) (min (j+1) (b+2)) : ℚ) +
      weightedBill s.count (chargedWeight s p) (capsAfter s j b) + s.seedLimit ≤ lossCap := by
    rw [cuts]
    change ExactRank.rank band.lambda band.mu (j:ℚ) (b:ℚ) + _ + _ ≤ _ at h
    change (band.fixedFee (b+2) (min (j+1) (b+2)) : ℚ) ≤ ExactRank.rank band.lambda band.mu j b at rank
    exact (by linarith only [payLimit,h,rank])
  exact round_le q

end Research6970.Height2313.Lower6960.Prefix6969Main.RankBill
