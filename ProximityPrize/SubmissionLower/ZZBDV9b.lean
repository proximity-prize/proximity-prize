import ProximityPrize.SubmissionLower.BI
set_option Elab.async false
set_option autoImplicit true
namespace fP
open aR MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
theorem bandSpace_finite (d:ℕ) (lo hi:ℤ) (top:ℕ) :
    Module.Finite ao (GS d lo hi top) :=
  restrictSupport_finite ((Finsupp.finite_of_degree_le d).subset fun _ h=>Nat.le_of_eq h.1)
private def rU (a b c f :ℕ) :Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a,b,c,f]
@[simp] private theorem OZ (a b c f :ℕ) (j:Fin 4) :
    rU a b c f j = ![a,b,c,f] j:= by simp [rU]
end
end fP
