import ProximityPrize.SubmissionLower.FadicVar
import ProximityPrize.SubmissionLower.FadicCast

/-!
# Certificates for the variable-depth gate

* `varDepthLow ≤ varDepthDim`, `varPlainLow ≤ varPlainDim` (blocks of `h` grades);
* `varLevelLoss`: the certified loss of one level from its plain box and its literal depth list;
* `rVarLevelLoss_cast`: the kernel-raw evaluator computes it;
* `loss_of_varCert`: from the per-level values to the total loss of `varGateDim`.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2 (cappedCount)
open scoped BigOperators
open Finset

/-! ### Chunked bounds -/

def varMultHigh (h bl jl tl L B J T Θ : ℕ) : ℤ :=
  if bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ then fastHigh (B - bl) (J - jl) (T - tl) (Θ - L) h else 0

def varDepthLow (h bl bh jl jh tl L H a : ℕ) : Entry → ℤ
  | none => 0
  | some (B, J, T) =>
    if BoxOK bh jh H a B J then
      max 0 (fastLow B J T (varΘ H a) h - varMultHigh h bl jl tl L B J T (varΘ H a))
    else 0

theorem varMult_le (h bl jl tl L B J T Θ : ℕ) (hh : 0 < h) :
    varMult bl jl tl L B J T Θ ≤ varMultHigh h bl jl tl L B J T Θ := by
  unfold varMult varMultHigh
  split
  · exact le_fastHigh _ _ _ _ hh
  · exact le_rfl

theorem varDepthLow_le (h bl bh jl jh tl L H a : ℕ) (e : Entry) (hh : 0 < h) :
    varDepthLow h bl bh jl jh tl L H a e ≤ varDepthDim bl bh jl jh tl L H a e := by
  rcases e with _ | ⟨B, J, T⟩
  · exact le_rfl
  · simp only [varDepthLow, varDepthDim]
    split
    · apply max_le_max le_rfl
      have h1 := fastLow_le B J T (varΘ H a) hh
      have h2 := varMult_le h bl jl tl L B J T (varΘ H a) hh
      linarith
    · exact le_rfl

def varPlainLow (h B J T : ℕ) : ℤ := fastLow (min B 4012) (min J 1650) T 131312 h

theorem varPlainLow_le (h B J T : ℕ) (hh : 0 < h) : varPlainLow h B J T ≤ varPlainDim B J T :=
  fastLow_le _ _ _ _ hh

/-- The certified loss of one level. -/
def varLevelLoss (S : ℤ) (h bl bh jl jh tl L H : ℕ) (plain : ℕ × ℕ × ℕ) (es : List Entry) : ℤ :=
  max 0 (S - max (varPlainLow h plain.1 plain.2.1 plain.2.2)
    (∑ a ∈ range es.length, varDepthLow h bl bh jl jh tl L H a (es.getD a none)))

/-- The certified loss of level `i + 1` of a schedule given by tables. -/
def varCertLoss (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) : ℤ :=
  if Rt ≤ i + 1 then 0 else varLevelLoss S h bl bh jl jh tl L H (plain (i + 1)) (table (i + 1))

theorem gateLoss_le_varCertLoss (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) (hh : 0 < h) :
    max 0 (S - varGateDim S bl bh jl jh tl L H Rt plain (fun r => (table r).length)
      (fun r a => (table r).getD a none) (i + 1)) ≤
      varCertLoss S h bl bh jl jh tl L H Rt plain table i := by
  unfold varCertLoss varGateDim
  split
  · simp
  · unfold varLevelLoss
    apply max_le_max le_rfl
    have h1 := varPlainLow_le h (plain (i + 1)).1 (plain (i + 1)).2.1 (plain (i + 1)).2.2 hh
    have h2 : (∑ a ∈ range (table (i + 1)).length,
        varDepthLow h bl bh jl jh tl L H a ((table (i + 1)).getD a none)) ≤
        varFadicDim bl bh jl jh tl L H (table (i + 1)).length (fun a => (table (i + 1)).getD a none) :=
      sum_le_sum fun a _ => varDepthLow_le h bl bh jl jh tl L H a _ hh
    have h3 := max_le_max h1 h2
    linarith

/-- **Certificate.**  The total gate loss is at most the sum of the certified level losses. -/
theorem loss_of_varCert (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (Ltot : ℤ) (hh : 0 < h)
    (hsum : ∑ i ∈ range Rt, varCertLoss S h bl bh jl jh tl L H Rt plain table i = Ltot) (N : ℕ) :
    ∑ i ∈ range N, max 0 (S - varGateDim S bl bh jl jh tl L H Rt plain
      (fun r => (table r).length) (fun r a => (table r).getD a none) (i + 1)) ≤ Ltot := by
  have hzero (i : ℕ) (hi : Rt ≤ i) : varCertLoss S h bl bh jl jh tl L H Rt plain table i = 0 := by
    unfold varCertLoss
    exact if_pos (by omega)
  have hnonneg (i : ℕ) : 0 ≤ varCertLoss S h bl bh jl jh tl L H Rt plain table i := by
    unfold varCertLoss
    split
    · exact le_rfl
    · exact le_max_left _ _
  refine (sum_le_sum fun i _ =>
    gateLoss_le_varCertLoss S h bl bh jl jh tl L H Rt plain table i hh).trans ?_
  rw [← hsum]
  rcases le_total N Rt with hN | hN
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hN) (fun i _ _ => hnonneg i)
  · rw [← sum_range_add_sum_Ico _ hN]
    have : ∑ i ∈ Ico Rt N, varCertLoss S h bl bh jl jh tl L H Rt plain table i = 0 :=
      sum_eq_zero fun i hi => hzero i (mem_Ico.mp hi).1
    rw [this, add_zero]

/-! ### Kernel-raw evaluator -/

def rBoxOK (bh jh H a B J : ℕ) : Bool :=
  Nat.ble (Nat.add B (Nat.mul a bh)) 4012 && Nat.ble (Nat.add J (Nat.mul a jh)) 1650 &&
    Nat.ble (Nat.mul a H) 131312

def rVarMultHigh (h bl jl tl L B J T Θ : ℕ) : ℕ :=
  cond (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ)
    (rFastHigh (Nat.sub B bl) (Nat.sub J jl) (Nat.sub T tl) (Nat.sub Θ L) h) 0

def rVarDepthAux (h bl jl tl L B J T Θ : ℕ) : ℕ :=
  Nat.sub (rFastLow B J T Θ h) (rVarMultHigh h bl jl tl L B J T Θ)

def rVarDepthLow (h bl bh jl jh tl L H a : ℕ) : Entry → ℕ
  | none => 0
  | some (B, J, T) =>
    cond (rBoxOK bh jh H a B J)
      (rVarDepthAux h bl jl tl L B J T (Nat.sub 131312 (Nat.mul a H))) 0

def rVarList (h bl bh jl jh tl L H : ℕ) : ℕ → List Entry → ℕ
  | _, [] => 0
  | k, e :: es => Nat.add (rVarDepthLow h bl bh jl jh tl L H k e) (rVarList h bl bh jl jh tl L H (k + 1) es)

def rVarPlainLow (h B J T : ℕ) : ℕ := rFastLow (rMin B 4012) (rMin J 1650) T 131312 h

def rVarLevelLoss (S h bl bh jl jh tl L H pB pJ pT : ℕ) (es : List Entry) : ℕ :=
  Nat.sub S (rMax (rVarPlainLow h pB pJ pT) (rVarList h bl bh jl jh tl L H 0 es))

/-! ### The raw evaluator computes the certified loss -/

theorem rBoxOK_iff (bh jh H a B J : ℕ) : rBoxOK bh jh H a B J = true ↔ BoxOK bh jh H a B J := by
  unfold rBoxOK BoxOK
  simp only [Bool.and_eq_true, ble_true, Nat.mul_eq, Nat.add_eq]
  tauto

theorem rVarMultHigh_cast (h bl jl tl L B J T Θ : ℕ) :
    ((rVarMultHigh h bl jl tl L B J T Θ : ℕ) : ℤ) = varMultHigh h bl jl tl L B J T Θ := by
  unfold rVarMultHigh varMultHigh
  by_cases hg : bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ
  · have hb : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ) = true := by
      simp only [Bool.and_eq_true, ble_true]
      exact ⟨⟨⟨hg.1, hg.2.1⟩, hg.2.2.1⟩, hg.2.2.2⟩
    rw [hb, if_pos hg]
    exact rFastHigh_cast _ _ _ _ _
  · have hb : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ) = false := by
      cases hc : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ)
      · rfl
      · simp only [Bool.and_eq_true, ble_true] at hc
        exact absurd ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩ hg
    rw [hb, if_neg hg]
    rfl

theorem rVarDepthLow_cast (h bl bh jl jh tl L H a : ℕ) (e : Entry) :
    ((rVarDepthLow h bl bh jl jh tl L H a e : ℕ) : ℤ) = varDepthLow h bl bh jl jh tl L H a e := by
  rcases e with _ | ⟨B, J, T⟩
  · rfl
  · simp only [rVarDepthLow, varDepthLow]
    by_cases hok : BoxOK bh jh H a B J
    · rw [(rBoxOK_iff bh jh H a B J).mpr hok, if_pos hok]
      show ((Nat.sub (rFastLow B J T (Nat.sub 131312 (Nat.mul a H)) h)
        (rVarMultHigh h bl jl tl L B J T (Nat.sub 131312 (Nat.mul a H))) : ℕ) : ℤ) = _
      rw [Nat.sub_eq, natSub_cast, rFastLow_cast, rVarMultHigh_cast]
      rfl
    · have hb : rBoxOK bh jh H a B J = false := by
        cases hc : rBoxOK bh jh H a B J
        · rfl
        · exact absurd ((rBoxOK_iff bh jh H a B J).mp hc) hok
      rw [hb, if_neg hok]
      rfl

theorem rVarList_cast (h bl bh jl jh tl L H : ℕ) (es : List Entry) (k : ℕ) :
    ((rVarList h bl bh jl jh tl L H k es : ℕ) : ℤ) =
      ∑ a ∈ range es.length, varDepthLow h bl bh jl jh tl L H (k + a) (es.getD a none) := by
  induction es generalizing k with
  | nil => simp [rVarList]
  | cons e es ih =>
    rw [rVarList, Nat.add_eq, Nat.cast_add, ih (k + 1), rVarDepthLow_cast, List.length_cons,
      sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    congr 1
    omega

theorem rVarPlainLow_cast (h B J T : ℕ) :
    ((rVarPlainLow h B J T : ℕ) : ℤ) = varPlainLow h B J T := by
  unfold rVarPlainLow varPlainLow
  rw [rMin_eq, rMin_eq, rFastLow_cast]

/-- **The raw level loss is the certified level loss.** -/
theorem rVarLevelLoss_cast (S h bl bh jl jh tl L H pB pJ pT : ℕ) (es : List Entry) :
    ((rVarLevelLoss S h bl bh jl jh tl L H pB pJ pT es : ℕ) : ℤ) =
      varLevelLoss S h bl bh jl jh tl L H (pB, pJ, pT) es := by
  unfold rVarLevelLoss varLevelLoss
  rw [Nat.sub_eq, natSub_cast, rMax_eq, Nat.cast_max, rVarPlainLow_cast, rVarList_cast]
  simp only [zero_add]

/-! ### Row lemmas for generated certificates -/

/-- One level of a generated certificate: the table lookups are closed by `rfl` and the value by
the raw evaluator. -/
theorem varCertLoss_row (S h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i pB pJ pT : ℕ) (es : List Entry) (v : ℕ)
    (hi : ¬ Rt ≤ i + 1) (hp : plain (i + 1) = (pB, pJ, pT)) (ht : table (i + 1) = es)
    (hv : rVarLevelLoss S h bl bh jl jh tl L H pB pJ pT es = v) :
    varCertLoss (S : ℤ) h bl bh jl jh tl L H Rt plain table i = (v : ℤ) := by
  unfold varCertLoss
  rw [if_neg hi, hp, ht, ← rVarLevelLoss_cast, hv]

theorem varCertLoss_terminal (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) (hi : Rt ≤ i + 1) :
    varCertLoss S h bl bh jl jh tl L H Rt plain table i = ((0 : ℕ) : ℤ) := by
  unfold varCertLoss
  rw [if_pos hi]
  rfl

end FadicGate

#print axioms FadicGate.loss_of_varCert
#print axioms FadicGate.rVarLevelLoss_cast
