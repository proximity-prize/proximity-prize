import ProximityPrize.SubmissionLower.WholeSpacePowerBox6814
namespace ProximityPrize.SubmissionLower.PacketExactIndex6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts

abbrev Index (C T R U : ℕ) :=
  SecondJetRelaxedGlobalIndex.Index (fun _ => C) 131071 T R (R/2) U

def exponent (C T R U : ℕ) (i : Index C T R U) : Fin 5 →₀ ℕ :=
  SecondJetRelaxedGlobalIndex.exponent i

theorem exponent_injective (C T R U : ℕ) : Function.Injective (exponent C T R U) :=
  SecondJetRelaxedGlobalIndex.exponent_injective _ _ _ _ _ _

theorem card_eq (C T R U : ℕ) (hUT : U≤T) :
    Fintype.card (Index C T R U)=coefficientCount (fun _ => C) 131071 T R (R/2) U :=
  card_index_closed _ _ _ _ _ _ hUT

theorem mem_range_of_bounds (C T R U : ℕ) (e : Fin 5 →₀ ℕ)
    (hc : e 0+131069*e 1+131071*e 2+131070*e 3<C)
    (ht : e 1+e 2+e 3+e 4≤T)
    (hr : 2*e 1+e 3≤R) (hu : e 1+e 2+e 3≤U) :
    e∈Set.range (exponent C T R U) := by
  have hh : e 1<R/2+1 := by omega
  have hrr : e 3<R-2*e 1+1 := by omega
  have hx : e 0<budget (fun _ => C) 131071 (e 1) (e 3)-131071*e 2 := by
    simp only [budget]
    omega
  have hy : e 2<yCount (fun _ => C) 131071 U (e 1) (e 3) := by
    simp only [yCount,budget]
    omega
  have hz : e 4<T+1-e 1-e 3-e 2 := by omega
  refine ⟨⟨⟨e 1,hh⟩,⟨e 3,hrr⟩,⟨e 2,hy⟩,⟨e 0,hx⟩,⟨e 4,hz⟩⟩,?_⟩
  ext i
  fin_cases i <;> simp [exponent,SecondJetRelaxedGlobalIndex.exponent]

variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.PacketExactIndex6815
