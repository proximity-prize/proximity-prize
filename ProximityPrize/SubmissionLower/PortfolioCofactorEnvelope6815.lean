import ProximityPrize.SubmissionLower.PortfolioPriceIntervals6815
import ProximityPrize.SubmissionLower.PortfolioCatalogueBounds6815
namespace ProximityPrize.SubmissionLower.PortfolioCofactorEnvelope6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingSourceCoupledClearing6814 MovingSourcePairEnvelope6814
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 PortfolioCost6815 PortfolioPriceIntervals6815
variable {K : Type} [Field K]

theorem ordinary_le (Q : Poly (K:=K)) (B U L S : ℕ)
    (hb : slope Q≤B) (hu : middle Q≤U) (ht : total Q≤L) (hs : order Q≤S) :
    CumulativeLe (ordinaryFlag Q)
      ⟨(Max.max (Max.max B U) L)-(Max.max B U),(Max.max B U)+S-B,B⟩ := by
  have h := ordinaryFlag_cumulative Q
  have hBU : B≤Max.max B U := le_max_left _ _
  have hU : U≤Max.max B U := le_max_right _ _
  have hUL : Max.max B U≤Max.max (Max.max B U) L := le_max_left _ _
  have hL : L≤Max.max (Max.max B U) L := le_max_right _ _
  change _≤B ∧ _≤(Max.max B U)+S-B+B ∧
    _≤(Max.max (Max.max B U) L)-(Max.max B U)+((Max.max B U)+S-B)+B
  omega

theorem owner_le (J : Poly (K:=K)) (s b u x : ℕ)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J=x) :
    CumulativeLe (ordinaryFlag J) (ownerFlag s b u x) := by
  have h := ordinaryFlag_cumulative J
  have hn := source_nested J
  change _≤b ∧ _≤u+s-b+b ∧ _≤x-u+(u+s-b)+b
  omega

theorem cofactor_le (Q : Poly (K:=K)) (B U L S e s b u x : ℕ)
    (hb : e*b+slope Q≤B) (hu : e*u+middle Q≤U)
    (ht : e*x+total Q≤L) (hs : e*s+order Q≤S) :
    CumulativeLe (ordinaryFlag Q) (cofactorFlag B U L S e s b u x) := by
  have h := ordinary_le Q (B-e*b) (U-e*u) (L-e*x) (S-e*s)
    (by omega) (by omega) (by omega) (by omega)
  have he : (Max.max (Max.max (B-e*b) (U-e*u)) (L-e*x))-
      Max.max (B-e*b) (U-e*u)=L-(e*x+Max.max (B-e*b) (U-e*u)) := by omega
  simpa only [cofactorFlag,he] using h

variable {I : Type} [CharP K 2130706433] {xmap : I → K} {t y r : ℕ}

theorem count_of_endpoints
    (P : Packet xmap t y r) (SZ SJ SQ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hcop : IsRelPrime SJ.P SQ.P) (delta : ℕ) (hd : 0<delta) (hdchar : delta≤2130706433)
    (hSJ : delta≤SJ.d) (hSQ : delta≤SQ.d)
    (s b u tau B U L S e lo hi cap : ℕ)
    (hs : order SJ.P=s) (hb : slope SJ.P=b) (hu : middle SJ.P=u) (ht : total SJ.P=tau)
    (hB : e*b+slope SQ.P≤B) (hU : e*u+middle SQ.P≤U)
    (hL : e*tau+total SQ.P≤L) (hS : e*s+order SQ.P≤S)
    (hx : lo≤tau) (hx' : tau≤hi)
    (hpairZ : flagMixed (ownerFlag s b u tau) (cofactorFlag B U L S e s b u tau) unitZFlag<2130706433)
    (hpairU : flagMixed (ownerFlag s b u tau) (cofactorFlag B U L S e s b u tau) unitYZFlag<2130706433)
    (hlo : totalNumerator z delta (ownerFlag s b u lo) (cofactorFlag B U L S e s b u lo) t y r≤
      50174*(3*(z.d*delta))*cap)
    (hhi : totalNumerator z delta (ownerFlag s b u hi) (cofactorFlag B U L S e s b u hi) t y r≤
      50174*(3*(z.d*delta))*cap) :
    P.seeds.card≤Max.max (identityPrice t y r) cap := by
  have hc := pair_count_of_bounds P SZ SJ SQ z hZ hFT hk hg hcop delta hd hdchar hSJ hSQ
    _ _ (owner_le SJ.P s b u tau hs hb hu ht) (cofactor_le SQ.P B U L S e s b u tau hB hU hL hS)
    hpairZ hpairU
  exact hc.trans (max_le_max le_rfl
    (cofactor_interval_price lo hi s b u B U L S e z delta t y r cap hd hlo hhi tau hx hx'))

end
end ProximityPrize.SubmissionLower.PortfolioCofactorEnvelope6815
