import ProximityPrize.SubmissionLower.R6966ProofNearLedgerApply
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineLedger

set_option Elab.async false

namespace Research6966.NearLedger

abbrev gap : ℕ := agreement-wordDegree

theorem upper_of_finite {i : Fin 23} (h : i.val<22) : upper i=some (inCap i) := by
  have hi : i.val+1<23 := by omega
  simp only [inCap,upper,dite_eq_left hi,Option.getD_some]

theorem InBin.le_cap {i : Fin 23} {v : ℕ} (mem : InBin i v) (finite : i.val<22) :
    v ≤ inCap i := mem.2 _ (upper_of_finite finite)

private theorem side_mono {h H : ℕ} (hh : h≤H) : side h≤side H :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _

/-- Weaken an observed surface and its nodal degrees to the checked
quote, then divide out the squared interpolation gap. -/
theorem Quote.surface_of_scaled (q : Quote) (b : Band) (a : ℕ) (i j : Fin 23)
    (selected : q.method=.surface) {marks g v₀ v₁ h₀ h₁ : ℕ}
    (degree : g≤q.degreeCap b a) (x₀ : v₀≤q.axisCap i j 0) (x₁ : v₁≤q.axisCap i j 1)
    (s₀ : h₀≤seedHeight a (inCap i)) (s₁ : h₁≤seedHeight a (inCap j))
    (price : marks*gap^2≤singular a i j*gap^2+
      2*(g*side h₀*side h₁+v₀*side (yHeight a)*side h₁+v₁*side (yHeight a)*side h₀)) :
    marks≤q.wordPrice b a i j := by
  unfold Quote.wordPrice
  simp only [selected]
  apply NativeAffineLedger.floor (by decide : 0<gap^2)
  refine price.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_)) _)
  · exact Nat.mul_le_mul (Nat.mul_le_mul degree (side_mono s₀)) (side_mono s₁)
  · exact Nat.mul_le_mul (Nat.mul_le_mul_right _ x₀) (side_mono s₁)
  · exact Nat.mul_le_mul (Nat.mul_le_mul_right _ x₁) (side_mono s₀)

theorem Quote.affine_of_scaled (q : Quote) (b : Band) (i j : Fin 23)
    (selected : q.method=.affine) {marks : ℕ}
    (price : marks*gap^3≤singular 1 i j*gap^3+6*side 1*side (wordDegree*inCap i)*side (wordDegree*inCap j)) :
    marks≤q.wordPrice b 1 i j := by
  have counted := NativeAffineLedger.three_floor (n:=nodes) (a:=agreement) (d:=wordDegree)
    (c:=6) (by decide) (by decide) price
  simpa only [Quote.wordPrice,selected,seedHeight,ite_eq_left rfl,ite_true] using counted

theorem Quote.single_affine_of_scaled (q : Quote) (b : Band) (i j : Fin 23)
    (selected : q.method=.single) {marks width : ℕ}
    (cap : width≤max (inCap i) (inCap j))
    (price : marks*gap^2≤singular 1 i j*gap^2+2*side 1*side (wordDegree*width)) :
    marks≤q.wordPrice b 1 i j := by
  have counted := NativeAffineLedger.two_floor (n:=nodes) (a:=agreement) (d:=wordDegree)
    (by decide) (by decide) price
  have widths : max 1 (wordDegree*width)≤max (seedHeight 1 (inCap i)) (seedHeight 1 (inCap j)) := by
    by_cases order : inCap i ≤ inCap j
    · rw [max_eq_right order] at cap
      exact (max_le_max le_rfl (Nat.mul_le_mul_left _ cap)).trans
        (le_max_right (seedHeight 1 (inCap i)) (seedHeight 1 (inCap j)))
    · rw [max_eq_left (by omega : inCap j ≤ inCap i)] at cap
      exact (max_le_max le_rfl (Nat.mul_le_mul_left _ cap)).trans
        (le_max_left (seedHeight 1 (inCap i)) (seedHeight 1 (inCap j)))
  unfold Quote.wordPrice
  simp only [selected,yHeight,Nat.sub_self,Nat.mul_zero,Nat.zero_add,Nat.mul_one]
  exact counted.trans (Nat.add_le_add_left (Nat.div_le_div_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 widths))) _)

#print axioms Quote.surface_of_scaled
#print axioms Quote.affine_of_scaled
#print axioms Quote.single_affine_of_scaled
end Research6966.NearLedger
