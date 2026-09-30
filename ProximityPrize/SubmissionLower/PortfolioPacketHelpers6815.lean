import ProximityPrize.SubmissionLower.MovingSourceBandPairCount6815
import ProximityPrize.SubmissionLower.PortfolioAvoidanceSource6815
import ProximityPrize.SubmissionLower.MovingSourcePairEnvelope6814
namespace ProximityPrize.SubmissionLower.PortfolioPacketHelpers6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815
open MovingSourcePairEnvelope6814 MovingSourceCoupledClearing6814
open PortfolioSource6815
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem helper_count {t y r : ℕ} (p : Parameters) (nodes : I ↪ K)
    (P : Packet (nodes : I → K) t y r) (Q : MvPolynomial (Fin 4) K)
    (hh : ProperHelper p P.F Q r y t nodes P.u0 P.u1)
    (hg : Gates t y r (p.B+p.s*(r-1)) (p.U+p.s*(y-1)) (p.L+p.s*(t-1))) :
    P.seeds.card≤AsymmetricHelper.leftRegularCountCap
      (pair t y r (p.B+p.s*(r-1)) (p.U+p.s*(y-1)) (p.L+p.s*(t-1))) := by
  classical
  apply proper_cut_count P Q _ _ _ hh.1 hh.2.1 hg
  intro gamma hgamma
  exact hh.2.2 (P.selected gamma) (P.degree gamma hgamma) gamma
    (P.nodes.filter (fun i => (P.selected gamma).eval (nodes i)=P.u0 i+gamma*P.u1 i))
    (P.agreement gamma hgamma)
    (fun i hi => by simpa only [mul_comm] using (Finset.mem_filter.mp hi).2)
    (P.solution gamma hgamma)

theorem pair_characteristic_gates (p q : FlagDegree)
    (hp : p.zOnly+p.yz+p.all≤8192) (hq : q.zOnly+q.yz+q.all≤8192) :
    flagMixed p q unitZFlag<2130706433 ∧ flagMixed p q unitYZFlag<2130706433 := by
  have hcP : CumulativeLe p ⟨0,0,8192⟩ := by
    change p.all≤8192 ∧ p.yz+p.all≤8192 ∧ p.zOnly+p.yz+p.all≤8192
    omega
  have hcQ : CumulativeLe q ⟨0,0,8192⟩ := by
    change q.all≤8192 ∧ q.yz+q.all≤8192 ∧ q.zOnly+q.yz+q.all≤8192
    omega
  exact ⟨(mixed_mono_pair _ _ _ _ unitZFlag hcP hcQ).trans_lt (by decide),
    (mixed_mono_pair _ _ _ _ unitYZFlag hcP hcQ).trans_lt (by decide)⟩

end
end ProximityPrize.SubmissionLower.PortfolioPacketHelpers6815
