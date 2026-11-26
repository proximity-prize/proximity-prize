import ProximityPrize.SubmissionBinaryLower.B6402RegularLocator

/-! The geometric bound on the number of exceptional order-two sites
comes from the nonzero top ordinate coefficient of the slope coefficient. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402QuarticProfile
open Polynomial B6401ContactKerD B6401QuotInterp B6401FactorBound B6401SmallAlg P64LineOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem quartic_sites (w WF : ℕ) (hw : 0<w) (x : I ↪ K) (F : ContactPoly (Polynomial K))
    (hF : wdeg w F≤WF) (h4 : (F.coeff 1).natDegree=4)
    (bad : Finset I) (zero : ∀ i∈bad,evalXAt (F.coeff 1) (x i)=0) :
    bad.card+5*w≤WF+1 := by
  classical
  let P := (F.coeff 1).coeff 4
  have hf1 : F.coeff 1≠0 := by intro h; simp [h] at h4
  have hp : P≠0 := by
    change (F.coeff 1).coeff 4≠0
    rw [←h4,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hf1
  let xx : I ↪ K[X] := ⟨fun i => C (x i),fun i j h => x.injective (C_injective h)⟩
  have hroot : bad.map xx ⊆ P.roots.toFinset := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
    rw [Multiset.mem_toFinset,mem_roots hp]
    have he := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 4) (zero i hi)
    change P.eval (C (x i))=0
    simpa only [P,evalXAt,coeff_map,coe_evalRingHom,coeff_zero] using he
  have hc : bad.card≤P.natDegree := calc
    _ = (bad.map xx).card := (Finset.card_map _).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hroot
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ _ := card_roots' P
  have upper := wdegBiDom_coeff_le_of_wdeg hF 1 hf1
  have hh : P.natDegree+4*w≤wdegBiDom w (F.coeff 1) :=
    Finset.le_sup (f:=fun j => ((F.coeff 1).coeff j).natDegree+j*w) (mem_support_iff.mpr hp)
  omega

theorem normalized {N w WF n2 nb : ℕ} (hN : N≠0) (hw : w≠0) (sub : nb≤n2)
    (roots : nb+5*w≤WF+1) :
    (nb : ℚ)/N≤(n2 : ℚ)/N ∧
    (N : ℚ)*((nb : ℚ)/N)≤((WF : ℚ)/w-5)*w+1 := by
  have hn : (N:ℚ)≠0 := Nat.cast_ne_zero.mpr hN
  have wne : (w:ℚ)≠0 := Nat.cast_ne_zero.mpr hw
  have hh : (nb:ℚ)+5*w≤WF+1 := by exact_mod_cast roots
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast sub) (Nat.cast_nonneg _)
  · rw [mul_div_cancel₀ _ hn,sub_mul,div_mul_cancel₀ _ wne]; linarith

#print axioms quartic_sites
end ProximityPrize.SubmissionBinaryLower.B6402QuarticProfile
