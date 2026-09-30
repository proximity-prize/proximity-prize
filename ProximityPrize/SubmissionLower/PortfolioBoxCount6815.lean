import ProximityPrize.SubmissionLower.PortfolioBoxes6815
import ProximityPrize.SubmissionLower.PortfolioNativeOwner6815
import ProximityPrize.SubmissionLower.PortfolioDerivativeOwner6815
import ProximityPrize.SubmissionLower.PortfolioAuxiliaryCount6815
namespace ProximityPrize.SubmissionLower.PortfolioBoxCount6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 MovingSourcePairEnvelope6814
open PortfolioCost6815 PortfolioSource6815 PortfolioAvoidanceSource6815 PortfolioBoxes6815

def flag (B U T S : ℕ) : FlagDegree :=
  let M := max B (U+S)
  ⟨max M (T+S)-M,M-B,B⟩
def ownerFlag (a : Box) := flag a.bhi a.uhi a.thi a.shi
def derivativeFlag (a : Box) : FlagDegree :=
  let p := ownerFlag a
  ⟨p.zOnly,p.yz,p.all-2⟩
def ownerZ (a : Box) (m : ℕ) : Degrees :=
  ⟨a.bhi,max a.bhi a.uhi,max (max a.bhi a.uhi) a.thi,m-1,a.slo⟩
def point {K : Type} [Field K] (J : Poly (K:=K)) : Point :=
  ⟨order J,slope J,middle J,total J⟩
def powerBox (p : Parameters) (a : Box) (m : ℕ) : PacketPortfolioAvoidance6815.OwnerBox :=
  ⟨(p.k+1+m-1)/m,a.blo,a.bhi,a.slo,a.ulo,a.tlo⟩
def cofactorFlag (p : Parameters) (a : Box) (e : ℕ) :=
  flag (p.B-e*a.blo) (p.U-e*a.ulo) (p.L-e*a.tlo) (p.s-e*a.slo)
def active (p : Parameters) (a : Box) (m e : ℕ) : Prop :=
  e*a.blo≤p.B ∧ e*a.ulo≤p.U ∧ e*a.tlo≤p.L ∧ e*a.slo≤p.s ∧ p.k+1-e*m≤p.s-e*a.slo
def GoodPower (i : Fin 75) (a : Box) (m : ℕ) : Prop :=
  let p := PortfolioSourceCatalogue6815.profile i
  (PacketPortfolioAvoidance6815.Impossible (caps p) (powerBox p a m) ∧
    0<PortfolioSourceCatalogue6815.kernel i) ∨
  PacketPortfolioAvoidance6815.count (caps p) (powerBox p a m)<PortfolioSourceCatalogue6815.kernel i

variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}

theorem flag_envelope (J : Poly (K:=K)) (B U T S : ℕ)
    (hb : slope J≤B) (hu : middle J≤U) (ht : total J≤T) (hs : order J≤S) :
    CumulativeLe (ordinaryFlag J) (flag B U T S) := by
  have h := ordinaryFlag_cumulative J
  dsimp only [flag]
  change _≤B ∧ _≤max B (U+S)-B+B ∧
    _≤max (max B (U+S)) (T+S)-max B (U+S)+(max B (U+S)-B)+B
  omega

theorem owner_envelope (J : Poly (K:=K)) (a : Box) (h : Contains a (point J)) :
    CumulativeLe (ordinaryFlag J) (ownerFlag a) := by
  exact flag_envelope J a.bhi a.uhi a.thi a.shi h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2 h.2.1

theorem derivative_envelope (J : Poly (K:=K)) (a : Box) (h : Contains a (point J))
    (hs : 2≤order J) : CumulativeLe (ordinaryFlag (pderiv 1 J)) (derivativeFlag a) := by
  have hdB := RamifiedOwnerDerivative6815.pderiv_weight J slopeWeights
  have hdU := RamifiedOwnerDerivative6815.pderiv_weight J middleWeights
  have hdT := RamifiedOwnerDerivative6815.pderiv_weight J totalWeights
  have hdS := RamifiedOwnerDerivative6815.pderiv_order J
  change slope (pderiv 1 J)≤slope J-2 at hdB
  change middle (pderiv 1 J)≤middle J-1 at hdU
  change total (pderiv 1 J)≤total J-1 at hdT
  change order (pderiv 1 J)≤order J-1 at hdS
  have hn := source_nested J
  have hd := ordinaryFlag_cumulative (pderiv 1 J)
  dsimp only [Contains,point] at h
  dsimp only [CumulativeLe,derivativeFlag,ownerFlag,flag]
  omega

theorem owner_source (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (a : Box) (m : ℕ) (hm : 0<m)
    (h : Contains a (point J)) (hms : m≤a.slo) (h2 : 2*a.slo≤a.bhi)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m) :
    ∃ S : Source P.F, Fits S (ownerZ a m) := by
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤a.bhi ∧
      e 1+e 2+e 3≤max a.bhi a.uhi ∧ e 1+e 2+e 3+e 4≤max (max a.bhi a.uhi) a.thi := by
    intro e he
    have h1 := (le_weightedTotalDegree slopeWeights he).trans h.2.2.2.1
    have h2 := (le_weightedTotalDegree middleWeights he).trans h.2.2.2.2.2.1
    have h3 := (le_weightedTotalDegree totalWeights he).trans h.2.2.2.2.2.2.2
    simp [weight_coords,slopeWeights,middleWeights,totalWeights] at h1 h2 h3
    exact ⟨by simpa only [Nat.mul_comm] using h1,h2.trans (le_max_right _ _),h3.trans (le_max_right _ _)⟩
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨S,_,hp⟩ := PortfolioOwners6815.root_source_profile P.F P.rdegree hchar J m a.shi
    a.bhi (max a.bhi a.uhi) (max (max a.bhi a.uhi) a.thi) (m-1) a.slo
    (by omega) (by omega) h.1 h.2.1 h2 (le_max_left _ _) (le_max_left _ _) hshape hroot
  exact ⟨S,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2⟩

theorem derivative_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (SZ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hZFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hFT : 1700<wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (a : Box) (m cap : ℕ)
    (h : Contains a (point J)) (hm : 2≤m) (hms : m≤order J)
    (hsmall : a.thi≤1700) (hsChar : a.shi<2130706433)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hcg : flagMixed (ownerFlag a) (derivativeFlag a) unitZFlag<2130706433 ∧
      flagMixed (ownerFlag a) (derivativeFlag a) unitYZFlag<2130706433)
    (hfit : pairCost z (m-1) (ownerFlag a) (derivativeFlag a) t y r+leading z t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨SJ,SQ,hSJ,hSQ,hcop,hJd,hQd,_⟩ := RamifiedOwnerDerivative6815.source_pair_of_ramified_owner
    P.F hFT P.rdegree hchar J hJ (h.2.2.2.2.2.2.2.trans hsmall)
    (by rw [asS_natDegree]; change 0<order J; omega)
    (by rw [asS_natDegree]; exact h.2.1.trans_lt hsChar) m hm hroot
  have hp := owner_envelope J a h
  have hq := derivative_envelope J a h (by omega)
  rw [←hSJ] at hp
  rw [←hSQ] at hq
  have hms' : m<2130706433 := hms.trans_lt (h.2.1.trans_lt hsChar)
  exact (pair_count_of_bounds P SZ SJ SQ z hZ hZFT hk hg hcop (m-1) (by omega)
    (by omega) (by omega) hQd _ _ hp hq hcg.1 hcg.2).trans (max_le_max le_rfl hfit)

theorem auxiliary_count [Fintype I] (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (SZ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hZFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (i : Fin 75) (hFT : (PortfolioSourceCatalogue6815.profile i).L<wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (a : Box) (m cap : ℕ)
    (h : Contains a (point J)) (hm : 0<m)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne : (asS J).map (carrierMap P.F)≠0)
    (hJF : a.thi<wt residualTotalWeights P.F) (hcap : 1000000000000000≤cap)
    (hgood : GoodPower i a m)
    (hchecks : ∀ e, e<(powerBox (PortfolioSourceCatalogue6815.profile i) a m).q →
      active (PortfolioSourceCatalogue6815.profile i) a m e →
      flagMixed (ownerFlag a) (cofactorFlag (PortfolioSourceCatalogue6815.profile i) a e) unitZFlag<2130706433 ∧
      flagMixed (ownerFlag a) (cofactorFlag (PortfolioSourceCatalogue6815.profile i) a e) unitYZFlag<2130706433 ∧
      pairCost z (min m ((PortfolioSourceCatalogue6815.profile i).k+1-e*m))
        (ownerFlag a) (cofactorFlag (PortfolioSourceCatalogue6815.profile i) a e) t y r+leading z t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  let p := PortfolioSourceCatalogue6815.profile i
  have hp : Shape p := PortfolioSourceCatalogue6815.shape i
  have small : p.B≤256 ∧ p.U≤512 ∧ p.L≤4096 ∧ p.s≤64 ∧ p.L+p.s≤8192 := PortfolioSourceCatalogue6815.small i
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  have hcovers : PacketPortfolioAvoidance6815.Covers (powerBox p a m) J :=
    ⟨h.2.2.1,h.2.2.2.1,h.1,h.2.2.2.2.1,h.2.2.2.2.2.2.1⟩
  rcases helper_or_coprime_sources_retained p hp (PortfolioSourceCatalogue6815.kernel i)
    (PortfolioSourceCatalogue6815.dimension i) nodes P.u0 P.u1 hI P.F hFT P.rdegree hchar
    r y t (by have := P.rlow; omega) (by have := P.ylow; have := P.rlow; omega)
    (by have := P.yt; have := P.ylow; have := P.rlow; omega)
    ⟨P.r_weight,P.y_weight,P.total_weight⟩ J hJ a.thi h.2.2.2.2.2.2.2 hJF m hm hroot hJne
    (powerBox p a m) rfl hcovers hgood
      with ⟨Q,hQ⟩ | ⟨e,he,SJ,SQ,hSJ,hcop,hdelta,hSP,hRet,hT,hU,hB,hS⟩
  · exact ((PortfolioUniformBudgets6815.helper_count p nodes P small.1 small.2.1
      small.2.2.1 small.2.2.2.1 Q hQ).le.trans hcap).trans (le_max_right _ _)
  have hb := Nat.mul_le_mul_left e h.2.2.1
  have hu := Nat.mul_le_mul_left e h.2.2.2.2.1
  have ht := Nat.mul_le_mul_left e h.2.2.2.2.2.2.1
  have hs := Nat.mul_le_mul_left e h.1
  have horder : SQ.d≤order SQ.P := by
    have hh := SQ.hdn.trans SQ.hn
    simpa only [Source.d,asS_natDegree,order] using hh
  have ha : active p a m e := by unfold active; dsimp only [point] at hb hu ht hs; omega
  obtain ⟨hcgZ,hcgU,hfit⟩ := hchecks e he ha
  have hq : CumulativeLe (ordinaryFlag SQ.P) (cofactorFlag p a e) :=
    flag_envelope SQ.P _ _ _ _ (by dsimp only [point] at hb; omega)
      (by dsimp only [point] at hu; omega) (by dsimp only [point] at ht; omega)
      (by dsimp only [point] at hs; omega)
  have hj := owner_envelope J a h
  rw [←hSJ] at hj
  have hdchar : min m (p.k+1-e*m)≤2130706433 := by
    have h1 := hp.retention
    have h2 := hp.degree
    have h3 := hp.characteristic
    have h4 := min_le_right m (p.k+1-e*m)
    omega
  exact (pair_count_of_bounds P SZ SJ SQ z hZ hZFT hk hg hcop _ hdelta hdchar hSP
    ((min_le_right _ _).trans hRet) _ _ hj hq hcgZ hcgU).trans (max_le_max le_rfl hfit)

end
end ProximityPrize.SubmissionLower.PortfolioBoxCount6815
