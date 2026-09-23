import ProximityPrize.SubmissionLower.MovingFiberPackingCheck6811
namespace ProximityPrize.SubmissionLower.MovingFiberPackingCheck6811
set_option Elab.async false
set_option maxHeartbeats 0

theorem shifted_complete (a : Nat) (xs ys : List Nat)
    (h : ∀ i, i < xs.length → i < ys.length →
      a + (xs[i]?).getD 0 ≤ (ys[i]?).getD 0) : shifted a xs ys = true := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [shifted, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · simpa using h 0 (by simp) (by simp)
      · apply ih
        intro i hi hj
        simpa using h (i+1) (by simpa using hi) (by simpa using hj)

theorem convolution_complete (xs ys zs : List Nat)
    (h : ∀ i j, i < xs.length → j < ys.length → i+j < zs.length →
      (xs[i]?).getD 0 + (ys[j]?).getD 0 ≤ (zs[i+j]?).getD 0) :
    convolution xs ys zs = true := by
  induction xs generalizing zs with
  | nil => rfl
  | cons x xs ih =>
    cases zs with
    | nil => rfl
    | cons z zs =>
      simp only [convolution, Bool.and_eq_true]
      constructor
      · apply shifted_complete
        intro j hj hk
        simpa using h 0 j (by simp) hj (by simpa using hk)
      · apply ih
        intro i j hi hj hk
        simpa [Nat.succ_add] using h (i+1) j (by simpa using hi) hj
          (by simpa [Nat.succ_add] using hk)

theorem monotone_getD_of_shifted (ys : List Nat)
    (h : shifted 0 ys ys.tail = true) (i j : Nat)
    (hij : i ≤ j) (hj : j < ys.length) :
    (ys[i]?).getD 0 ≤ (ys[j]?).getD 0 := by
  induction j with
  | zero =>
    have heq : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; rfl
    · have hprev := ih (by omega) (by omega)
      have hs := shifted_sound 0 ys ys.tail h j (by omega)
        (by simp only [List.length_tail]; omega)
      simp only [Nat.zero_add, List.getElem?_tail] at hs
      exact hprev.trans hs

theorem convolution_zero (n : Nat) (ys : List Nat)
    (h : shifted 0 ys ys.tail = true) :
    convolution (List.replicate n 0) ys ys = true := by
  apply convolution_complete
  intro i j hi hj hk
  have hz : ((List.replicate n 0)[i]?).getD 0 = 0 := by simp
  rw [hz, Nat.zero_add]
  exact monotone_getD_of_shifted ys h j (i+j) (by omega) hk


theorem convolution_zero_right (n : Nat) (xs zs : List Nat)
    (h : shifted 0 xs zs = true) (hz : shifted 0 zs zs.tail = true) :
    convolution xs (List.replicate n 0) zs = true := by
  apply convolution_complete
  intro i j hi hj hk
  have hzero : ((List.replicate n 0)[j]?).getD 0 = 0 := by simp
  rw [hzero, Nat.add_zero]
  have hp := shifted_sound 0 xs zs h i hi (by omega)
  simp only [Nat.zero_add] at hp
  exact hp.trans (monotone_getD_of_shifted zs hz i (i+j) (by omega) hk)

end ProximityPrize.SubmissionLower.MovingFiberPackingCheck6811
