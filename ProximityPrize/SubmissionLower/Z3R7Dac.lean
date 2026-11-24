import ProximityPrize.SubmissionLower.Ze903db
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace qU3xjYb
noncomputable section
open Polynomial q7kdBxd qrzQ9fc
open P5 (p)

private theorem separable_of_small_root {F E :Type} [Field F] [Field E] [Algebra F E]
    [CharP F p] {x :E} {f :F[X]} (hf :f≠0) (hd:f.natDegree<p)
    (hx :aeval x f=0) :IsSeparable F x := by
  have hi:IsIntegral F x :=IsAlgebraic.isIntegral ⟨f,hf,hx⟩
  let m:=minpoly F x
  have hpos :0< m.natDegree :=minpoly.natDegree_pos hi
  have hlt:m.natDegree<p:=(natDegree_le_of_dvd (minpoly.dvd F x hx) hf).trans_lt hd
  have hcast: (m.natDegree :F)≠0:= fun he =>
    hlt.not_ge (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff F p _).mp he))
  change m.Separable
  apply (separable_iff_derivative_ne_zero (minpoly.irreducible hi)).mpr
  intro hz
  change m.derivative=0 at hz
  have he :=coeff_derivative m (m.natDegree-1)
  rw [hz,coeff_zero,← Nat.cast_succ,show m.natDegree-1+1=m.natDegree by omega,
    show (m.natDegree-1).succ=m.natDegree by omega] at he
  exact (mul_ne_zero (leadingCoeff_ne_zero.mpr (minpoly.ne_zero hi)) hcast) he.symm
private theorem separable_tower {F E :Type} [Field F] [Field E] [Algebra F E]
    (S:IntermediateField F E) (hF:Algebra.IsSeparable F S)
    (hE :Algebra.IsSeparable S E) :Algebra.IsSeparable F E := by
  let:IsScalarTower F S E :=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  exact @Algebra.IsSeparable.trans F S _ _ _ E _ _ _ ‹IsScalarTower F S E› hF hE
end
end qU3xjYb
