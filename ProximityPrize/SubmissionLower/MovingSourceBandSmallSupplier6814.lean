import ProximityPrize.SubmissionLower.MovingSourceBandHighPackets6814

/-! Extract the already proved small interpolation source without
requiring the old high-total Z source at the same time. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandSmallSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open MvPolynomial RCN234 RCN156
open MovingSourceTwoProfiles6814 MovingFiberThreeSources6811 WholeSpaceSourceKernel6814
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]

theorem helper_or_small_source (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I=262144)
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F) (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    (∃ Q, WholeSpaceSourceAlternative6814.ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ S : Source F, Profile S 31 98 995 14 2 3 := by
  obtain ⟨P,hP,hbounds,hcontact⟩ := exists_small_polynomial nodes u0 u1 hI
  have hwide : Bounds P := by
    intro e he
    have hh := hbounds e he
    exact ⟨hh.1,hh.2.1,hh.2.2.1,by omega,hh.2.2.2.2⟩
  rcases WholeSpaceSourceAlternative6814.helper_or_retained nodes u0 u1 P hP hwide hcontact
    F hFi hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  let S : Source F := {
    P := P, B := 31, U := 98, T := 995, s := 14, k := 2, n0 := 3
    hS := fun e he => (hbounds e he).2.1
    hshape := fun e he => ⟨(hbounds e he).1,(hbounds e he).2.2.1,(hbounds e he).2.2.2.1⟩
    hBU := by omega, hUT := by omega, hdn := by omega, hB := by omega
    hn := hret.1, hdiv := hret.2 }
  exact Or.inr ⟨S,by repeat' constructor⟩

#print axioms helper_or_small_source
end
end ProximityPrize.SubmissionLower.MovingSourceBandSmallSupplier6814
