import ProximityPrize.SubmissionLower.Peer653High53FamilyCover

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
noncomputable section
open Polynomial
open Peer653High53 (Band AnchorModel AnchoredFamily agreement p)
open K1_14 (Banks Jet Equation SeedBound)
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open K1_14_4 (seedDegree seedDegree_le_iff)
theorem tested_spec (b : Band) (x : Test b) :
    Listed b (tested b x) ∧ (tested b x).shape.m = (terminal b).shape.m ∧
    (tested b x).shape.B = (terminal b).shape.B ∧ (tested b x).shape.J = (terminal b).shape.J ∧
    (tested b x).shape.U ≤ (terminal b).shape.U := by
  cases x with
  | none => exact ⟨Or.inl rfl, rfl, rfl, rfl, le_rfl⟩
  | some i => exact ⟨Or.inr (Or.inr ⟨i, rfl⟩), rfl, rfl, rfl, (grade_checked b i).sub⟩
private theorem order_of_full {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead)
    (x : Test b) {q : Surface} (hq : Parent q) (hv : BankPass rows (terminal b).shape q)
    {W} (hW : W < (tested b x).shape.m * agreement) {P : Jet}
    (hP : P ∈ rows (tested b x).shape W) :
    OrderAt q P (contactPower M.overhead.toNat (tested b x).shape W) := by
  let h := M.overhead.toNat
  let t := tested b x
  obtain ⟨ht, hm, hb, hj, hu⟩ := tested_spec b x
  have hchar : t.shape.m * agreement < p := hm ▸ (terminal_guards b).2.2.2.1
  apply K1_14_3R_1.proof _ _ _ hq
  · have hd := Nat.div_le_self (fullCutoff t.shape - W) (2*h)
    change 1 + (fullCutoff t.shape - W)/(2*h) < p
    change W < t.shape.m * agreement at hW
    unfold fullCutoff at *
    omega
  intro a c hac
  change a + c < 1 + (fullCutoff t.shape - W)/(2*h) at hac
  have hh : 0 < h := (terminal_guards b).1.trans_le (window_nat hw).1
  have hc := (Nat.le_div_iff_mul_le (by omega : 0 < 2*h)).mp
    (show a+c ≤ (fullCutoff t.shape - W)/(2*h) by omega)
  rw [Nat.mul_comm (a+c), Nat.mul_add] at hc
  have top : fullCutoff t.shape = fullCutoff (terminal b).shape :=
    congrArg (fun m => m * agreement - 1) hm
  have hwc : W ≤ fullCutoff t.shape := by
    change W < t.shape.m * agreement at hW
    unfold fullCutoff
    omega
  have hw' : W + 2*h*a + 2*h*c ≤ fullCutoff (terminal b).shape := by omega
  have ha := src.shift t ht W P hP 0 a
  have hc' := src.shift t ht _ _ ha 1 c
  exact hv _ (src.nested t ht _ (Or.inl rfl) hm hb hj hu _ _ hw' hc')
theorem trace_of_full {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead)
    {qs : Finset Surface} (hq : ∀ q ∈ qs, Parent q)
    (hp : ∀ q ∈ qs, BankPass rows (terminal b).shape q) {f : Equation}
    (hf : ProjectedProduct qs f) (x : Test b) :
    TerminalTrace M.overhead.toNat (tested b x) rows f := by
  have ht := (tested_spec b x).1
  refine ⟨src.floor_bound _ ht, src.shape _ ht, src.leading _ ht, ?_⟩
  intro W hW P hP hn
  exact hf.divides_leading P _ hn
    (fun q h => order_of_full src hw x (hq q h) (hp q h) hW hP)
theorem grade_of_rejections {b : Band} {f : Equation} (hp : 0 < f.natDegree)
    (reject : ∀ x : Test b, threshold b x ≤ f.natDegree →
      seedThreshold b x ≤ seedDegree f → False) :
    ∃ i : GradeIndex b, f.natDegree = i.val+1 ∧ SeedBound f ((grades b).get i).seedCap := by
  have he : f.natDegree ≤ (grades b).length := by
    by_contra! hlo
    exact reject none hlo (Nat.zero_le _)
  let i : GradeIndex b := ⟨f.natDegree-1, by omega⟩
  have hidx : f.natDegree = i.val+1 := by dsimp [i]; omega
  refine ⟨i, hidx, (seedDegree_le_iff _ _).mp ?_⟩
  by_contra! hlow
  exact reject (some i) hidx.ge hlow
end
end Peer653High53
end
