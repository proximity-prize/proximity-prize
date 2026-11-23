import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
set_option Elab.async false
set_option autoImplicit true
section
set_option maxSynthPendingDepth 8
namespace K1_14_2_1
noncomputable section
open K1 K1_14 K1_14_2 Polynomial Finset
def c1 : Prop :=
  ∀ (G P R : Jet) (U e : ℕ),
    Irreducible G → 0 < G.natDegree → UsesSeed G →
    P ≠ 0 → G ∣ P → U < p →
    (∀ j i, ((P.coeff j).coeff i).totalDegree ≤ U) →
    (∀ (i : Fin 2) (r : ℕ), r < e → G ∣ seedHasse i r R) →
    G ^ e ∣ R
end
end K1_14_2_1
end
