import ProximityPrize.SubmissionLower.PortfolioPacketHelpers6815
import ProximityPrize.SubmissionLower.PortfolioSourceCatalogue6815
namespace ProximityPrize.SubmissionLower.PortfolioUniformBudgets6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN260 RCN294 RCN234 RCN156
open MovingSourceBandLeading6815 MovingSourceBandGeometry6815 PortfolioSource6815

theorem count_mono (t y r b u l capT capY capR capB capU capL : ℕ)
    (ht : t≤capT) (hy : y≤capY) (hr : r≤capR) (hb : b≤capB) (hu : u≤capU) (hl : l≤capL) :
    AsymmetricHelper.leftRegularCountCap (pair t y r b u l)≤
      AsymmetricHelper.leftRegularCountCap (pair capT capY capR capB capU capL) := by
  unfold AsymmetricHelper.leftRegularCountCap
  apply Nat.div_le_div_right
  simp only [AsymmetricHelper.leftRegularNumerator,pair,UnequalParameters.errors,
    UnequalParameters.gap,UnequalParameters.leftAgreement,UnequalParameters.mixedCost,dot]
  gcongr

theorem gates_mono (t y r b u l capT capY capR capB capU capL : ℕ)
    (ht : t≤capT) (hy : y≤capY) (hr : r≤capR) (hb : b≤capB) (hu : u≤capU) (hl : l≤capL)
    (h : Gates capT capY capR capB capU capL) : Gates t y r b u l := by
  rcases h with ⟨hY,hR,hZ⟩
  unfold Gates pair UnequalParameters.mixedCost at *
  constructor
  · apply lt_of_le_of_lt _ hY
    dsimp only
    gcongr
  constructor
  · apply lt_of_le_of_lt _ hR
    dsimp only
    gcongr
  · apply lt_of_le_of_lt _ hZ
    dsimp only
    gcongr

theorem maximum_helper : Gates 4100 59 13 1024 4224 266432 ∧
    AsymmetricHelper.leftRegularCountCap (pair 4100 59 13 1024 4224 266432)<1000000000000000 := by
  unfold Gates
  decide +kernel

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x : I → K} {t y r : ℕ}

theorem helper_parameters (p : Parameters) (P : Packet x t y r)
    (hb : p.B≤256) (hu : p.U≤512) (hl : p.L≤4096) (hs : p.s≤64) :
    p.B+p.s*(r-1)≤1024 ∧ p.U+p.s*(y-1)≤4224 ∧ p.L+p.s*(t-1)≤266432 := by
  have hr := P.rhigh
  have hy := P.yhigh
  have ht := P.thigh
  have hrr : p.s*(r-1)≤64*12 := Nat.mul_le_mul hs (by omega)
  have hyy : p.s*(y-1)≤64*58 := Nat.mul_le_mul hs (by omega)
  have htt : p.s*(t-1)≤64*4099 := Nat.mul_le_mul hs (by omega)
  omega

theorem helper_count (p : Parameters) (nodes : I ↪ K) (P : Packet (nodes : I → K) t y r)
    (hb : p.B≤256) (hu : p.U≤512) (hl : p.L≤4096) (hs : p.s≤64)
    (Q : MvPolynomial (Fin 4) K) (hQ : ProperHelper p P.F Q r y t nodes P.u0 P.u1) :
    P.seeds.card<1000000000000000 := by
  obtain ⟨hr,hy,ht⟩ := helper_parameters p P hb hu hl hs
  have hg := gates_mono t y r _ _ _ 4100 59 13 1024 4224 266432
    P.thigh P.yhigh P.rhigh hr hy ht maximum_helper.1
  exact (PortfolioPacketHelpers6815.helper_count p nodes P Q hQ hg).trans_lt
    ((count_mono t y r _ _ _ 4100 59 13 1024 4224 266432
      P.thigh P.yhigh P.rhigh hr hy ht).trans_lt maximum_helper.2)

end
end ProximityPrize.SubmissionLower.PortfolioUniformBudgets6815
