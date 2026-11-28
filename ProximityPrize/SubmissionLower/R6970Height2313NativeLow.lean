import ProximityPrize.SubmissionLower.Z6969Pack0590

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0688
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Early.NativeLightLow
noncomputable section

open Finset Polynomial
open K1 (K I p)
open K1_14 (Jet jetAt L)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct nodeL)
open Far6969RescueGeometry (Model Family)
open Research6966

open _root_.Lower6960.Prefix6969Early (seed threshold lowFee)

private def votes (i : Fin 56) : ℕ := 179730-(threshold i-1-128659)
private def bad (i : Fin 56) : ℕ := 3*(seed i+p*seed i)
private def upper (i : Fin 56) : ℕ :=
  ((262144-179730)*((2*133482-1)*seed i)+179730)^2/(179730-133482)^2

private theorem receipt (i : Fin 56) :
    0<votes i ∧ bad i≤lowFee ∧ 262144*upper i≤(lowFee-bad i)*votes i := by
  fin_cases i <;> decide +kernel

private theorem per_node {d : ℕ} (hd : d≤133482) (i : Fin 56) :
    ((262144-179730)*((2*d-1)*seed i)+(179730-d))^2/(179730-d)^2≤upper i := by
  have power:(2*d-1)*seed i≤(2*133482-1)*seed i:=Nat.mul_le_mul_right _ (by omega)
  have top:(262144-179730)*((2*d-1)*seed i)+(179730-d)≤
      (262144-179730)*((2*133482-1)*seed i)+179730 :=
    Nat.add_le_add (Nat.mul_le_mul_left _ power) (Nat.sub_le ..)
  have bottom:(179730-133482)^2≤(179730-d)^2:=Nat.pow_le_pow_left (by omega) 2
  exact (Nat.div_le_div_right (Nat.pow_le_pow_left top 2)).trans
    (Nat.div_le_div_left bottom (by decide))

/-- Count all marks of the original quadratic helper in the low physical
weight interval directly on the production word family. -/
theorem count {u del} {M : Model u del} {Γ T : Finset K}
    (F : Family M Γ) (sub : T⊆Γ)
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    (lo : 2308≤M.overhead.toNat) (hi : M.overhead.toNat≤2411)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈T,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (ns : G.natDegree=1) (quad : K1_14_2_2_2_1.jetDegree G=2) (i : Fin 56)
    (cap : K1_14_2_2_2_1.seedDegree G≤seed i)
    (low : RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw<threshold i)
    (root : ∀ γ∈T,jetAt G (M.label γ) (F.scalar γ)=0) :
    T.card≤lowFee := by
  let h := M.overhead.toNat
  let d : ℕ := 131071+h
  let W := RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw
  let v := 179730-(W-(131071-h-1))
  have hp : 0<h := by omega
  have hs : h≤131070 := by omega
  have hd : d≤133482 := by dsimp [d,h]; omega
  have sw : seed i≤56 := by have := i.isLt; dsimp [seed]; omega
  have nodes (j : I) : (poleProduct D).eval (algebraMap K L (K1.node j))≠0 := by
    rw [poleProduct,eval_mul]
    exact mul_ne_zero (noPole 0 j) (noPole 1 j)
  have height : 131071+M.overhead≤(d:ℤ) := by dsimp [d,h]; push_cast; omega
  have cnt := PhysicalHelperTariff.price F sub hp hs phys prime ns quad (seed i) d
    ((K1_14_2_2_2_1.seedDegree_le G (seed i)).mp cap) (by change 3*seed i<2130706433; omega)
    height le_rfl (hd.trans_lt (by decide)) (hd.trans_lt (by decide)) nodes residues root
  rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)] at cnt
  change T.card*v≤bad i*v+262144*
    (((262144-179730)*((2*d-1)*seed i)+(179730-d))^2/(179730-d)^2) at cnt
  have vv : votes i≤v := by
    unfold votes v W
    dsimp [h]
    omega
  obtain ⟨pos,feeFit,paid⟩ := receipt i
  have bill : 262144*(((262144-179730)*((2*d-1)*seed i)+(179730-d))^2/(179730-d)^2)
      ≤(lowFee-bad i)*v :=
    (Nat.mul_le_mul_left _ (per_node hd i)).trans
      (paid.trans (Nat.mul_le_mul_left _ vv))
  apply Nat.le_of_mul_le_mul_right _ (pos.trans_le vv)
  apply cnt.trans
  calc
   _ ≤ bad i*v+(lowFee-bad i)*v := Nat.add_le_add_left bill _
   _ = _ := by rw [←Nat.add_mul,Nat.add_sub_of_le feeFit]

end
end Lower6960.Prefix6969Early.NativeLightLow
end Z6969Source0688


end Research6970.Height2313
