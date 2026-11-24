import ProximityPrize.SubmissionLower.CN
set_option Elab.async false
set_option autoImplicit true
section
set_option maxSynthPendingDepth 8
namespace aBa
noncomputable section
open K1 cu gT Polynomial Finset
def c1 :Prop :=
  ∀ (G P R:Jet) (U e :ℕ),
    Irreducible G→0<G.natDegree→alm G →
    P≠0→G∣P→U<p →
    (∀ j i,((P.coeff j).coeff i).totalDegree≤U) →
    (∀ (i:Fin 2) (r :ℕ),r<e→G∣A5 i r R) →
    G^e∣R
end
end aBa
end
