import ProximityPrize.SubmissionLower.R6966ProofFarFactorPrice
import ProximityPrize.SubmissionLower.R6966ProofFarTerminalReceipts

set_option Elab.async false

namespace Research6966.FarRetained
open Polynomial Finset
open K1 (I K p)
open K1_14 (Equation FX Seeds L atMark atX graphEval liftPoly seedEmbedding)
open KoalaRect (axisDegree axisDegree_le_iff)
open Lower6960
open FarTerminalReceipts (witness)
open RetainedCompression (MarkedFiber integral_project specialize incl)
open CurvatureSquares (zView Ordinate)
open RetainedShortening (Word)
open FarFactorPrice (agreement wordDegree rate)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 1300000
set_option maxRecDepth 9000

abbrev cap : ℕ := 13745945737225694
def axisCap (e : ℕ) : ℕ := (witness e).order 1-1

private theorem budget (i : Fin 40) :
    (rate (max 3 i.val)+(2*i.val-1))*(p+1)*axisCap i.val+(max 3 i.val-1)*i.val≤cap ∧
      (2*i.val-1)*axisCap i.val<p := by
  fin_cases i <;> decide +kernel

private def determinant (f : Equation) : Seeds := f.resultant f.derivative f.natDegree (f.natDegree-1)

private theorem det_axis (f : Equation) (i : Fin 2) :
    (determinant f).degreeOf i≤(2*f.natDegree-1)*axisDegree f i := by
  have coeffs := (axisDegree_le_iff f i _).mp le_rfl
  have der (j : ℕ) : (f.derivative.coeff j).degreeOf i≤axisDegree f i := by
    rw [coeff_derivative]
    have eq : ((j:Seeds)+1)=MvPolynomial.C ((j:FX)+1) := by simp
    rw [eq]
    apply (MvPolynomial.degreeOf_mul_le ..).trans
    rw [MvPolynomial.degreeOf_C,Nat.add_zero]
    exact coeffs (j+1)
  exact (ThirdPole.resultant_axis f f.derivative _ _ _ _ i coeffs der).trans
    (by rw [←Nat.add_mul]; apply Nat.mul_le_mul_right; omega)

private theorem singular (f : Equation) (sep : (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable)
    (T : Finset K) (label : K→K) (inj : Function.Injective label)
    (small : (2*f.natDegree-1)*axisDegree f 0<p) :
    (T.filter (fun γ=>graphEval (label γ) (determinant f)=0)).card≤
      (2*f.natDegree-1)*(axisDegree f 0+p*axisDegree f 1) := by
  classical
  let B:=T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let coord (γ : K) := seedEmbedding (label γ)
  have eq : (B.image coord).card=B.card := card_image_of_injective _ (seedEmbedding.injective.comp inj)
  have nz : determinant f≠0 := resultant_derivative_ne_zero_of_separable_map_fractionField f sep
  have bound := K1_10.frobenius_coefficient_exception_count p _ _ (by decide) _ nz
    (det_axis f 0) small (det_axis f 1) (B.image coord) (by
      intro z hz
      obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp hγ).2)
  rw [eq] at bound
  exact bound.trans_eq (by ring)

/-- Every native retained word is paid by the projected factor tariff or
by the single mixed-axis discriminant charge. -/
theorem count {w : I→K} {s : K→K[X]} {T : Finset K}
    (words : Word agreement wordDegree w s T) (label : K→K) (inj : Function.Injective label)
    (f : Equation) (pos : 0<f.natDegree) (small : f.natDegree<40)
    (sep : (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable)
    (axis : ∀ j : Fin 2, axisDegree f j<(witness f.natDegree).order 1)
    (roots : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤cap := by
  classical
  let e := f.natDegree
  let n := max 3 e
  let v := axisDegree f 0+p*axisDegree f 1
  have axis' (j : Fin 2) : axisDegree f j≤axisCap e := by
    have bound := axis j
    change axisDegree f j < (witness e).order 1 at bound
    change axisDegree f j≤(witness e).order 1-1
    omega
  obtain ⟨price, tame⟩ := budget ⟨e,small⟩
  change (rate n+(2*e-1))*(p+1)*axisCap e+(n-1)*e≤cap at price
  change (2*e-1)*axisCap e<p at tame
  have smallAxis := (Nat.mul_le_mul_left (2*e-1) (axis' 0)).trans_lt tame
  have fn : f≠0 := fun z=>by rw [z,natDegree_zero] at pos; omega
  have ep : 1≤2*e-1 := by dsimp only [e];omega
  have fp : axisDegree f 0<p := by
    have z := Nat.mul_le_mul_right (axisDegree f 0) ep
    rw [Nat.one_mul] at z
    exact z.trans_lt smallAxis
  obtain ⟨D,P,dn,pn,degree,seed,calls⟩ := integral_project f fn fp
  let B := T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let S := T\B
  have bad : B.card≤(2*e-1)*v := singular f sep T label inj smallAxis
  let z (γ : K) := algebraMap K L (label γ)
  have lift_inj : Function.Injective z := (algebraMap K L).injective.comp inj
  have dnon : incl D≠0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) FX)).mpr dn
  have marks (γ : K) (mem : γ∈S) : MarkedFiber P (z γ) (liftPoly (s γ)) := by
    obtain ⟨tg,good⟩:=mem_sdiff.mp mem
    have safe : graphEval (label γ) (determinant f)≠0 :=
      fun eq=>good (mem_filter.mpr ⟨tg,eq⟩)
    have full := natDegree_map_eq_of_resultant_derivative_padded_ne_zero (graphEval (label γ)) f le_rfl safe
    have separable := separable_map_of_resultant_derivative_padded_ne_zero (graphEval (label γ)) f le_rfl pos safe
    have root : (f.map (graphEval (label γ))).eval (atX (s γ))=0 := by rw [eval_map]; exact roots γ tg
    have eq := calls (label γ)
    have smap : ((specialize P (z γ)).map incl).natDegree=(specialize P (z γ)).natDegree :=
      natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) FX) _
    refine ⟨?_,?_,?_⟩
    · rw [← smap,eq,natDegree_C_mul dnon,full,degree]
    · rw [eq]; exact separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr dnon))
    · apply (IsFractionRing.injective (Polynomial L) FX)
      rw [← Polynomial.eval_map_apply,eq,map_zero,eval_mul,eval_C]
      exact mul_eq_zero.mpr (Or.inr root)
  have sub : S⊆T := sdiff_subset
  have wordS : Word agreement wordDegree w s S :=
    ⟨words.distinct.mono sub,fun γ hγ=>words.degree γ (sub hγ),fun γ hγ=>words.hits γ (sub hγ)⟩
  have ord : P.natDegree≤n := degree.trans_le (le_max_right _ _)
  have nsmall : n<48 := max_lt (by decide) (small.trans (by decide))
  have counted := FarFactorPrice.price wordS z lift_inj P pn n v (le_max_left _ _) nsmall ord seed marks
  have eq : S.card+B.card=T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have axisSum : v≤(p+1)*axisCap e := by
    unfold v
    exact (Nat.add_le_add (axis' 0) (Nat.mul_le_mul_left p (axis' 1))).trans_eq (by ring)
  rw [←eq]
  calc
    _ ≤ rate n*v+(n-1)*e+(2*e-1)*v := Nat.add_le_add (by simpa only [degree] using counted) bad
    _ = (rate n+(2*e-1))*v+(n-1)*e := by rw [Nat.add_mul]; ring
    _ ≤ _ := (Nat.add_le_add_right (Nat.mul_le_mul_left _ axisSum) _).trans
      (by simpa only [Nat.mul_assoc] using price)

end
end Research6966.FarRetained
