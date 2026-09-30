import ProximityPrize.SubmissionLower.PortfolioCofactorEnvelope6815
import ProximityPrize.SubmissionLower.PortfolioOwners6815
namespace ProximityPrize.SubmissionLower.PortfolioAuxiliaryCount6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
open RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
open PortfolioSource6815 PortfolioAvoidanceSource6815 PortfolioCost6815 PortfolioPriceIntervals6815
open PortfolioCofactorEnvelope6815 MovingSourceCoupledClearing6814 MovingFiberThreeSources6811
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy

def upper (L e hi : ℕ) : ℕ := if e=0 then hi else min hi (L/e)
def active (p : Parameters) (m s b u e : ℕ) : Prop :=
  e*b≤p.B ∧ e*u≤p.U ∧ e*s≤p.s ∧ p.k+1-e*m≤p.s-e*s
def box (p : Parameters) (m s b u lo : ℕ) : PacketPortfolioAvoidance6815.OwnerBox :=
  ⟨(p.k+1+m-1)/m,b,b,s,u,lo⟩

def EndpointChecks (p : Parameters) (z : Degrees) (m s b u lo hi t y r cap : ℕ) : Prop :=
  ∀ e, e<(box p m s b u lo).q → active p m s b u e → lo≤upper p.L e hi →
    totalNumerator z (min m (p.k+1-e*m)) (ownerFlag s b u lo)
      (cofactorFlag p.B p.U p.L p.s e s b u lo) t y r≤
        50174*(3*(z.d*min m (p.k+1-e*m)))*cap ∧
    totalNumerator z (min m (p.k+1-e*m)) (ownerFlag s b u (upper p.L e hi))
      (cofactorFlag p.B p.U p.L p.s e s b u (upper p.L e hi)) t y r≤
        50174*(3*(z.d*min m (p.k+1-e*m)))*cap

theorem cofactor_total_small (p : Parameters) (hp : Shape p)
    (e s b u tau : ℕ) :
    (cofactorFlag p.B p.U p.L p.s e s b u tau).zOnly+
      (cofactorFlag p.B p.U p.L p.s e s b u tau).yz+
      (cofactorFlag p.B p.U p.L p.s e s b u tau).all≤p.L+p.s := by
  have hBU := hp.middle
  have hUL := hp.total
  have hB : p.B-e*b≤Max.max (p.B-e*b) (p.U-e*u) := le_max_left _ _
  have hU : Max.max (p.B-e*b) (p.U-e*u)≤p.L := max_le (by omega) (by omega)
  dsimp only [cofactorFlag]
  omega

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x : I → K} {t y r : ℕ}

theorem packet_count (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (SZ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hZFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (i : Fin 75) (hFT : (PortfolioSourceCatalogue6815.profile i).L<wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J)
    (m s b u tau lo hi cap : ℕ) (hm : 0<m)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J=tau)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne : (asS J).map (carrierMap P.F)≠0)
    (hlo : lo≤tau) (hhi : tau≤hi) (hJF : hi<wt residualTotalWeights P.F)
    (hsize : hi+s≤8192) (hcap : 1000000000000000≤cap)
    (hgood : (PacketPortfolioAvoidance6815.Impossible (caps (PortfolioSourceCatalogue6815.profile i))
        (box (PortfolioSourceCatalogue6815.profile i) m s b u lo) ∧
          0<PortfolioSourceCatalogue6815.kernel i) ∨
      PacketPortfolioAvoidance6815.count (caps (PortfolioSourceCatalogue6815.profile i))
        (box (PortfolioSourceCatalogue6815.profile i) m s b u lo)<PortfolioSourceCatalogue6815.kernel i)
    (hchecks : EndpointChecks (PortfolioSourceCatalogue6815.profile i) z m s b u lo hi t y r cap) :
    P.seeds.card≤Max.max (identityPrice t y r) cap := by
  let p := PortfolioSourceCatalogue6815.profile i
  have hp : Shape p := PortfolioSourceCatalogue6815.shape i
  have small : p.B≤256 ∧ p.U≤512 ∧ p.L≤4096 ∧ p.s≤64 ∧ p.L+p.s≤8192 :=
    PortfolioSourceCatalogue6815.small i
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt
    (by have := P.rhigh; omega)
  have hcovers : PacketPortfolioAvoidance6815.Covers (box p m s b u lo) J := by
    change b≤slope J ∧ slope J≤b ∧ s≤order J ∧ u≤middle J ∧ lo≤total J
    omega
  rcases helper_or_coprime_sources_retained p hp (PortfolioSourceCatalogue6815.kernel i)
    (PortfolioSourceCatalogue6815.dimension i) nodes P.u0 P.u1 hI P.F hFT P.rdegree hchar
    r y t (by have := P.rlow; omega) (by have := P.ylow; have := P.rlow; omega)
    (by have := P.yt; have := P.ylow; have := P.rlow; omega)
    ⟨P.r_weight,P.y_weight,P.total_weight⟩ J hJ hi (by omega) hJF m hm hroot hJne
    (box p m s b u lo) rfl hcovers hgood
      with ⟨Q,hQ⟩ | ⟨e,he,SJ,SQ,hSJ,hcop,hdelta,hSP,hRet,hT,hU,hB,hS⟩
  · exact ((PortfolioUniformBudgets6815.helper_count p nodes P small.1 small.2.1
      small.2.2.1 small.2.2.2.1 Q hQ).le.trans hcap).trans (le_max_right _ _)
  have hT' : e*tau+total SQ.P≤p.L := by simpa only [ht] using hT
  have hU' : e*u+middle SQ.P≤p.U := by simpa only [hu] using hU
  have hB' : e*b+slope SQ.P≤p.B := by simpa only [hb] using hB
  have hS' : e*s+order SQ.P≤p.s := by simpa only [hs] using hS
  have horder : SQ.d≤order SQ.P := by
    have hh := SQ.hdn.trans SQ.hn
    simpa only [Source.d,asS_natDegree,order] using hh
  have hactive : active p m s b u e := by dsimp only [active]; omega
  have hupper : tau≤upper p.L e hi := by
    by_cases hz : e=0
    · simpa only [upper,if_pos hz] using hhi
    · simp only [upper,if_neg hz]
      exact le_min hhi ((Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [Nat.mul_comm] using
        (show e*tau≤p.L by omega)))
  obtain ⟨hloCost,hhiCost⟩ := hchecks e he hactive (hlo.trans hupper)
  have hn := source_nested J
  have hpTot : (ownerFlag s b u tau).zOnly+(ownerFlag s b u tau).yz+(ownerFlag s b u tau).all≤8192 := by
    dsimp only [ownerFlag]
    rw [hu,hs,hb,ht] at hn
    omega
  have hqTot := (cofactor_total_small p hp e s b u tau).trans small.2.2.2.2
  have hpair := PortfolioPacketHelpers6815.pair_characteristic_gates _ _ hpTot hqTot
  have hdc : min m (p.k+1-e*m)≤2130706433 := by
    have h1 := hp.retention
    have h2 := hp.degree
    have h3 := hp.characteristic
    have h4 := min_le_right m (p.k+1-e*m)
    omega
  exact count_of_endpoints P SZ SJ SQ z hZ hZFT hk hg hcop _ hdelta hdc hSP
    ((min_le_right _ _).trans hRet) s b u tau p.B p.U p.L p.s e lo (upper p.L e hi) cap
    (by rwa [hSJ]) (by rwa [hSJ]) (by rwa [hSJ]) (by rwa [hSJ]) hB' hU' hT' hS' hlo hupper
    hpair.1 hpair.2 hloCost hhiCost

end
end ProximityPrize.SubmissionLower.PortfolioAuxiliaryCount6815
