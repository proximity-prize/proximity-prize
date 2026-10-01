import ProximityPrize.SubmissionLower.MergedInfra6815_45
import ProximityPrize.SubmissionLower.MergedInfra6815_43
import ProximityPrize.SubmissionLower.MergedInfra6815_3
import ProximityPrize.SubmissionLower.MergedInfra6815_44
import ProximityPrize.SubmissionLower.MergedInfra6815_46
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.PortfolioDerivativeOwner6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 MovingSourcePairEnvelope6814
open PortfolioCost6815 PortfolioPriceIntervals6815 PortfolioCofactorEnvelope6815
variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}

def derivativeFlag (s b u hi : ℕ) : FlagDegree := ⟨hi-u,u+s-b,b-2⟩

theorem derivative_envelope (J : Poly (K:=K)) (s b u hi : ℕ) (hs : order J=s)
    (hb : slope J=b) (hu : middle J=u) (ht : total J≤hi) (hs2 : 2≤s) :
    CumulativeLe (ordinaryFlag (pderiv 1 J)) (derivativeFlag s b u hi) := by
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
  change _≤b-2 ∧ _≤u+s-b+(b-2) ∧ _≤hi-u+(u+s-b)+(b-2)
  omega

theorem packet_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (SZ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hZFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hFT : 1700<wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (m s b u hi cap : ℕ)
    (hm : 2≤m) (hms : m≤s) (hs : order J=s) (hb : slope J=b) (hu : middle J=u)
    (ht : total J≤hi) (hh : hi≤1700) (hsChar : s<2130706433) (hsize : hi+s≤8192)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hfit : pairCost z (m-1) (ownerFlag s b u hi) (derivativeFlag s b u hi) t y r+
      leading z t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨SJ,SQ,hSJ,hSQ,hcop,hJd,hQd,_⟩ := RamifiedOwnerDerivative6815.source_pair_of_ramified_owner
    P.F hFT P.rdegree hchar J hJ (ht.trans hh)
    (by rw [asS_natDegree]; change 0<order J; omega)
    (by rw [asS_natDegree]; change order J<2130706433; omega) m hm hroot
  have hn := source_nested J
  have hp : CumulativeLe (ordinaryFlag SJ.P) (ownerFlag s b u hi) := by
    rw [hSJ]
    have h := ordinaryFlag_cumulative J
    change _≤b ∧ _≤u+s-b+b ∧ _≤hi-u+(u+s-b)+b
    omega
  have hq : CumulativeLe (ordinaryFlag SQ.P) (derivativeFlag s b u hi) := by
    rw [hSQ]
    exact derivative_envelope J s b u hi hs hb hu ht (by omega)
  have hpT : (ownerFlag s b u hi).zOnly+(ownerFlag s b u hi).yz+(ownerFlag s b u hi).all≤8192 := by
    dsimp only [ownerFlag]
    omega
  have hqT : (derivativeFlag s b u hi).zOnly+(derivativeFlag s b u hi).yz+
      (derivativeFlag s b u hi).all≤8192 := by
    dsimp only [derivativeFlag]
    omega
  have hcg := PortfolioPacketHelpers6815.pair_characteristic_gates _ _ hpT hqT
  have hc := pair_count_of_bounds P SZ SJ SQ z hZ hZFT hk hg hcop (m-1) (by omega)
    (by omega) (by omega) hQd _ _ hp hq hcg.1 hcg.2
  exact hc.trans (max_le_max le_rfl hfit)

end
end ProximityPrize.SubmissionLower.PortfolioDerivativeOwner6815
end MergedPart0
section MergedPart1
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
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.PortfolioChoice6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 SecondJetCoefficients SecondJetCarrierDichotomy MovingFiberThreeSources6811
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open PortfolioSource6815 PortfolioCost6815 PortfolioNativeOwner6815
open PortfolioPriceIntervals6815 PortfolioReceiptChecks6815

inductive Choice where
  | native
  | derivative (ownerZ : Bool)
  | auxiliary (ownerZ : Bool) (source : Fin 75)
  deriving DecidableEq

def chosenZ (useOwner : Bool) (fixed : Degrees) (m s b u hi : ℕ) : Degrees :=
  if useOwner then ownerDegrees m s b u hi else fixed

def Common (z : Degrees) (low t y r : ℕ) : Prop :=
  z.T<low ∧ z.k<2130706433 ∧ Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0)
instance (z : Degrees) (low t y r : ℕ) : Decidable (Common z low t y r) := by
  unfold Common Gates
  infer_instance

def check (c : Choice) (fixed : Degrees) (low t y r cap m s b u lo hi : ℕ) : Bool :=
  match c with
  | .native => decide (Common (ownerDegrees m s b u hi) low t y r ∧
      nativeScalar (ownerDegrees m s b u hi) t y r/(3*(ownerDegrees m s b u hi).d)+
        leading (ownerDegrees m s b u hi) t y r≤cap)
  | .derivative useOwner =>
      let z := chosenZ useOwner fixed m s b u hi
      decide (2≤m ∧ Common z low t y r ∧
        pairCost z (m-1) (ownerFlag s b u hi) (PortfolioDerivativeOwner6815.derivativeFlag s b u hi) t y r+
          leading z t y r≤cap)
  | .auxiliary useOwner i =>
      let z := chosenZ useOwner fixed m s b u hi
      decide (Common z low t y r ∧ (PortfolioSourceCatalogue6815.profile i).L<low) &&
        checkAux i z m s b u lo hi t y r cap

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x : I → K} {t y r : ℕ}

theorem chosen_source (P : Packet x t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (J : Poly (K:=K)) (m s b u hi : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J≤hi)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (useOwner : Bool) : ∃ S : Source P.F, Fits S (chosenZ useOwner fixed m s b u hi) := by
  cases useOwner
  · exact ⟨fixedS,hFixed⟩
  · obtain ⟨S,_,hS⟩ := exists_owner_source P J m s b u hi hm hms hs hb hu ht hroot
    exact ⟨S,hS⟩

theorem count_of_check (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (c : Choice) (low cap m s b u lo hi tau : ℕ)
    (hloF : low≤wt residualTotalWeights P.F) (hlo : 2985<low) (hcap : 1000000000000000≤cap)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hm : 0<m) (hms : m≤s)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J=tau)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne : (asS J).map (carrierMap P.F)≠0)
    (hsmall : hi≤995) (hsChar : s<2130706433) (hsize : hi+s≤8192)
    (hx : lo≤tau) (hx' : tau≤hi)
    (hc : check c fixed low t y r cap m s b u lo hi=true) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hT : total J≤hi := by omega
  cases c with
  | native =>
    have hh := of_decide_eq_true hc
    exact PortfolioNativeOwner6815.packet_count P J m s b u hi cap hm hms hs hb hu hT hroot
      (hh.1.1.trans_le hloF) hh.1.2.1 hh.1.2.2 hh.2
  | derivative useOwner =>
    have hh := of_decide_eq_true hc
    obtain ⟨SZ,hZ⟩ := chosen_source P fixedS fixed hFixed J m s b u hi hm hms hs hb hu hT hroot useOwner
    exact PortfolioDerivativeOwner6815.packet_count P SZ _ hZ (hh.2.1.1.trans_le hloF)
      hh.2.1.2.1 hh.2.1.2.2 (by omega) J hJ m s b u hi cap hh.1 hms hs hb hu hT
      (by omega) hsChar hsize hroot hh.2.2
  | auxiliary useOwner i =>
    have hh := hc
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hh
    obtain ⟨SZ,hZ⟩ := chosen_source P fixedS fixed hFixed J m s b u hi hm hms hs hb hu hT hroot useOwner
    have hs' := aux_spec i _ m s b u lo hi t y r cap hh.2
    exact PortfolioAuxiliaryCount6815.packet_count nodes hI P SZ _ hZ (hh.1.1.1.trans_le hloF)
      hh.1.1.2.1 hh.1.1.2.2 i (hh.1.2.trans_le hloF) J hJ m s b u tau lo hi cap hm
      hs hb hu ht hroot hJne hx hx' (by omega) hsize hcap hs'.1 hs'.2

end
end ProximityPrize.SubmissionLower.PortfolioChoice6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.PortfolioBoxCheck6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open PortfolioBoxes6815 PortfolioBoxCount6815 PortfolioCost6815 PortfolioSource6815
open PortfolioChoice6815 (Choice Common)
open RCN095 RCN135 RCN136 RCN156 RCN234 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 SecondJetCoefficients SecondJetCarrierDichotomy

def chosenZ (useOwner : Bool) (fixed : Degrees) (a : Box) (m : ℕ) :=
  if useOwner then ownerZ a m else fixed

instance (p : Parameters) (a : Box) (m e : ℕ) : Decidable (active p a m e) := by
  unfold active; infer_instance
instance (i : Fin 75) (a : Box) (m : ℕ) : Decidable (GoodPower i a m) := by
  unfold GoodPower PacketPortfolioAvoidance6815.Impossible; infer_instance

def PairChecks (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r cap : ℕ) : Prop :=
  flagMixed p q unitZFlag<2130706433 ∧ flagMixed p q unitYZFlag<2130706433 ∧
    pairCost z delta p q t y r+leading z t y r≤cap
instance (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r cap : ℕ) :
    Decidable (PairChecks z delta p q t y r cap) := by unfold PairChecks; infer_instance

def checkExit (p : Parameters) (a : Box) (z : Degrees) (m t y r cap e : ℕ) : Bool :=
  if active p a m e then decide (PairChecks z (min m (p.k+1-e*m))
    (ownerFlag a) (cofactorFlag p a e) t y r cap) else true
def checkExits (p : Parameters) (a : Box) (z : Degrees) (m t y r cap : ℕ) : Bool :=
  (List.range (powerBox p a m).q).all (checkExit p a z m t y r cap)

def checkChoice (c : Choice) (fixed : Degrees) (a : Box) (m low t y r cap : ℕ) : Bool :=
  match c with
  | .native => decide (Common (ownerZ a m) low t y r ∧
      nativeScalar (ownerZ a m) t y r/(3*(ownerZ a m).d)+leading (ownerZ a m) t y r≤cap)
  | .derivative useOwner =>
      let z := chosenZ useOwner fixed a m
      decide (2≤m ∧ Common z low t y r ∧ PairChecks z (m-1) (ownerFlag a) (derivativeFlag a) t y r cap)
  | .auxiliary useOwner i =>
      let z := chosenZ useOwner fixed a m
      decide (Common z low t y r ∧ (PortfolioSourceCatalogue6815.profile i).L<low) &&
        decide (GoodPower i a m) && checkExits (PortfolioSourceCatalogue6815.profile i) a z m t y r cap

def check (c : Choice) (fixed : Degrees) (a : Box) (m low t y r cap : ℕ) : Bool :=
  decide (0<m ∧ m≤a.slo ∧ 2*a.slo≤a.bhi ∧ a.thi≤1700 ∧ a.thi<low ∧ a.shi<2130706433) &&
    checkChoice c fixed a m low t y r cap

theorem exits_spec (p : Parameters) (a : Box) (z : Degrees) (m t y r cap : ℕ)
    (hc : checkExits p a z m t y r cap=true) :
    ∀ e, e<(powerBox p a m).q → active p a m e →
      PairChecks z (min m (p.k+1-e*m)) (ownerFlag a) (cofactorFlag p a e) t y r cap := by
  intro e he ha
  have hh := List.all_eq_true.mp hc e (List.mem_range.mpr he)
  simpa only [checkExit,if_pos ha,decide_eq_true_eq] using hh

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r : ℕ}

theorem count_of_check (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (c : Choice) (a : Box) (m low cap : ℕ)
    (hloF : low≤wt residualTotalWeights P.F) (hlo : 1700<low) (hcap : 1000000000000000≤cap)
    (J : Poly (K:=K)) (hJ : Irreducible J) (h : Contains a (point J))
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne : (asS J).map (carrierMap P.F)≠0)
    (hc : check c fixed a m low t y r cap=true) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hm,hms,h2,hsmall,hJF,hsChar⟩ := hc.1
  have hsrc (useOwner : Bool) : ∃ S : Source P.F, Fits S (chosenZ useOwner fixed a m) := by
    cases useOwner
    · exact ⟨fixedS,hFixed⟩
    · exact owner_source P J a m hm h hms h2 hroot
  cases c with
  | native =>
    have hh := of_decide_eq_true hc.2
    obtain ⟨S,hS⟩ := owner_source P J a m hm h hms h2 hroot
    exact (native_count_of_degrees P S _ hS (hh.1.1.trans_le hloF) hh.1.2.1 hh.1.2.2).trans
      (max_le_max le_rfl hh.2)
  | derivative useOwner =>
    have hh := of_decide_eq_true hc.2
    obtain ⟨S,hS⟩ := hsrc useOwner
    exact derivative_count P S _ hS (hh.2.1.1.trans_le hloF) hh.2.1.2.1 hh.2.1.2.2
      (hlo.trans_le hloF) J hJ a m cap h hh.1 (hms.trans h.1) hsmall hsChar hroot
      ⟨hh.2.2.1,hh.2.2.2.1⟩ hh.2.2.2.2
  | auxiliary useOwner i =>
    have hh := hc.2
    simp only [checkChoice,Bool.and_eq_true,decide_eq_true_eq] at hh
    obtain ⟨S,hS⟩ := hsrc useOwner
    exact auxiliary_count nodes hI P S _ hS (hh.1.1.1.1.trans_le hloF)
      hh.1.1.1.2.1 hh.1.1.1.2.2 i (hh.1.1.2.trans_le hloF) J hJ a m cap h hm hroot hJne
      (hJF.trans_le hloF) hcap hh.1.2 (exits_spec _ _ _ _ _ _ _ _ hh.2)

end
end ProximityPrize.SubmissionLower.PortfolioBoxCheck6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.PortfolioBoxCover6815
noncomputable section
set_option autoImplicit false
open PortfolioBoxes6815 PortfolioBoxCount6815 PortfolioCost6815
open RCN095 RCN135 RCN136 RCN156 RCN234 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 SecondJetCoefficients SecondJetCarrierDichotomy

def Valid (fixed : Degrees) (m low t y r cap : ℕ) (a : Box) : Prop :=
  ∃ c, PortfolioBoxCheck6815.check c fixed a m low t y r cap=true

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r : ℕ}
theorem count_of_covered (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (a : Box) (m low cap : ℕ)
    (hloF : low≤wt residualTotalWeights P.F) (hlo : 1700<low) (hcap : 1000000000000000≤cap)
    (J : Poly (K:=K)) (hJ : Irreducible J) (ha : Admissible m (point J)) (h : Contains a (point J))
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne : (asS J).map (carrierMap P.F)≠0)
    (hc : Covered m (Valid fixed m low t y r cap) a) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  obtain ⟨b,⟨c,hc⟩,hb⟩ := hc (point J) ha h
  exact PortfolioBoxCheck6815.count_of_check nodes hI P fixedS fixed hFixed c b m low cap
    hloF hlo hcap J hJ hb hroot hJne hc

end
end ProximityPrize.SubmissionLower.PortfolioBoxCover6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.OwnerTreeCheck6815
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioChoice6815 PortfolioCost6815
set_option autoImplicit false

def choiceOf (j : ℕ) : Choice :=
  if j=0 then .native else if j=1 then .derivative false else if j=2 then .derivative true
  else .auxiliary ((j-3)%2=1) ⟨(j-3)/2%75,Nat.mod_lt _ (by decide)⟩

def axisOf (x : ℕ) : Fin 4 := ⟨x/2%4,Nat.mod_lt _ (by decide)⟩

def run (fixed : Degrees) (m low t y r cap : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0,_,_ => none
  | f+1,code,a =>
    let b := normalize m 8 a
    let x := code%65536
    if x%2=0 then
      (if PortfolioBoxCheck6815.check (choiceOf (x/2)) fixed b m low t y r cap then some (code/65536) else none)
    else
      match run fixed m low t y r cap f (code/65536) (lower b (axisOf x) (x/8)) with
      | none => none
      | some c => run fixed m low t y r cap f c (upper b (axisOf x) (x/8))

theorem run_sound (fixed : Degrees) (m low t y r cap : ℕ) :
    ∀ f code a c, run fixed m low t y r cap f code a=some c → Covered m (Valid fixed m low t y r cap) a := by
  intro f
  induction f with
  | zero => intro code a c h; simp [run] at h
  | succ f ih =>
    intro code a c h
    apply covered_normalize m _ a (normalize m 8 a) rfl
    simp only [run] at h
    split at h
    · split at h
      · exact covered_leaf m _ _ ⟨_,by assumption⟩
      · simp at h
    · split at h
      · simp at h
      · rename_i c1 h1
        exact covered_split m _ _ _ _ (ih _ _ _ h1) (ih _ _ _ h)

theorem covered_of_run (fixed : Degrees) (m low t y r cap f code : ℕ) (a : Box)
    (h : (run fixed m low t y r cap f code a).isSome=true) : Covered m (Valid fixed m low t y r cap) a := by
  cases hc : run fixed m low t y r cap f code a with
  | none => simp [hc] at h
  | some c => exact run_sound fixed m low t y r cap f code a c hc

end ProximityPrize.SubmissionLower.OwnerTreeCheck6815
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.PortfolioRamifiedBoxes6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 MovingSourcePairEnvelope6814 MovingSourceOwnerSplit6814
open PortfolioCost6815
open PortfolioChoice6815 (Common)

structure Point where
  b : ℕ
  u : ℕ
  t : ℕ
  deriving DecidableEq
structure Box where
  blo : ℕ
  bhi : ℕ
  ulo : ℕ
  uhi : ℕ
  tlo : ℕ
  thi : ℕ
  deriving DecidableEq
def Contains (a : Box) (p : Point) := a.blo≤p.b ∧ p.b≤a.bhi ∧ a.ulo≤p.u ∧ p.u≤a.uhi ∧ a.tlo≤p.t ∧ p.t≤a.thi
def Nested (p : Point) := p.b≤p.u ∧ p.u≤p.t
def Empty (a : Box) := a.bhi<a.blo ∨ a.uhi<a.ulo ∨ a.thi<a.tlo
instance (a : Box) : Decidable (Empty a) := by unfold Empty; infer_instance
def step (a : Box) : Box :=
  let bh := min (min a.bhi a.uhi) a.thi
  let ul := max a.ulo a.blo
  let uh := min a.uhi a.thi
  ⟨a.blo,bh,ul,uh,max a.tlo ul,a.thi⟩
def normalize : ℕ → Box → Box
  | 0,a => a
  | n+1,a => normalize n (step a)
theorem step_contains (a : Box) (p : Point) (hn : Nested p) (h : Contains a p) : Contains (step a) p := by
  dsimp only [Nested,Contains,step] at *
  omega
theorem normalize_contains (n : ℕ) (a : Box) (p : Point) (hn : Nested p) (h : Contains a p) :
    Contains (normalize n a) p := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih => exact ih (step a) (step_contains a p hn h)
def lower (a : Box) (axis : Fin 3) (v : ℕ) : Box :=
  match axis.val with
  | 0 => {a with bhi:=v}
  | 1 => {a with uhi:=v}
  | _ => {a with thi:=v}
def upper (a : Box) (axis : Fin 3) (v : ℕ) : Box :=
  match axis.val with
  | 0 => {a with blo:=v+1}
  | 1 => {a with ulo:=v+1}
  | _ => {a with tlo:=v+1}
def Covered (valid : Box → Prop) (a : Box) := ∀ p, Nested p → Contains a p → ∃ b, valid b ∧ Contains b p
theorem covered_leaf (valid : Box → Prop) (a : Box) (h : valid a) : Covered valid a := by
  intro p _ hp; exact ⟨a,h,hp⟩
theorem covered_normalize (valid : Box → Prop) (a b : Box) (he : normalize 4 a=b)
    (h : Covered valid b) : Covered valid a := by
  intro p hn hp; apply h p hn; rw [←he]; exact normalize_contains 4 a p hn hp
theorem covered_split (valid : Box → Prop) (a : Box) (axis : Fin 3) (v : ℕ)
    (hl : Covered valid (lower a axis v)) (hh : Covered valid (upper a axis v)) : Covered valid a := by
  intro p hn hp
  have h : Contains (lower a axis v) p ∨ Contains (upper a axis v) p := by
    fin_cases axis <;> simp [Contains,lower,upper] at * <;> omega
  exact h.elim (hl p hn) (hh p hn)

def cumulativeFlag (B U T : ℕ) : FlagDegree := ⟨T-U,U-B,B⟩
def pFlag (a : Box) := cumulativeFlag a.bhi a.uhi a.thi
def qT (a : Box) := 792-a.tlo
def qU (a : Box) := min (136-a.ulo) (qT a)
def qB (a : Box) := min (38-a.blo) (qU a)
def qFlag (a : Box) := cumulativeFlag (qB a) (qU a) (qT a)
def dFlag (a : Box) := cumulativeFlag (a.bhi-2) (a.uhi-2) (a.thi-2)
def degreeZ (B U T d n : ℕ) : Degrees :=
  ⟨B,max B (U-n),max (max B (U-n)) (T-n),d-1,n⟩
def chosenZ (which : Fin 3) (fixed : Degrees) (a : Box) :=
  match which.val with
  | 0 => fixed
  | 1 => degreeZ a.bhi a.uhi a.thi 2 3
  | _ => degreeZ (qB a) (qU a) (qT a) 1 1
structure Choice where
  which : Fin 3
  derivative : Bool
  deriving DecidableEq
def rhsFlag (c : Choice) (a : Box) := if c.derivative then dFlag a else qFlag a
def check (c : Choice) (fixed : Degrees) (a : Box) (low t y r cap : ℕ) : Bool :=
  decide (6≤a.bhi ∧ a.bhi≤a.uhi ∧ a.uhi≤a.thi ∧ a.thi≤8192 ∧ 2≤qB a ∧
    Common (chosenZ c.which fixed a) low t y r ∧
    PortfolioBoxCheck6815.PairChecks (chosenZ c.which fixed a) 1 (pFlag a) (rhsFlag c a) t y r cap)
def Valid (fixed : Degrees) (low t y r cap : ℕ) (a : Box) := ∃ c, check c fixed a low t y r cap=true

variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}
def point (J : Poly (K:=K)) : Point := ⟨slope J,middle J+order J,total J+order J⟩
def Caps (J : Poly (K:=K)) (B U T : ℕ) := slope J≤B ∧ middle J+order J≤U ∧ total J+order J≤T

theorem envelope (J : Poly (K:=K)) (B U T : ℕ) (h : Caps J B U T) (hBU : B≤U) (hUT : U≤T) :
    CumulativeLe (ordinaryFlag J) (cumulativeFlag B U T) := by
  have hh := ordinaryFlag_cumulative J
  dsimp only [Caps] at h
  dsimp only [CumulativeLe,cumulativeFlag]
  omega

theorem derivative_caps (J : Poly (K:=K)) (B U T : ℕ) (h : Caps J B U T) (hs : 2≤order J) :
    Caps (pderiv 1 J) (B-2) (U-2) (T-2) := by
  have hb := RamifiedOwnerDerivative6815.pderiv_weight J slopeWeights
  have hu := RamifiedOwnerDerivative6815.pderiv_weight J middleWeights
  have ht := RamifiedOwnerDerivative6815.pderiv_weight J totalWeights
  have ho := RamifiedOwnerDerivative6815.pderiv_order J
  change slope (pderiv 1 J)≤slope J-2 at hb
  change middle (pderiv 1 J)≤middle J-1 at hu
  change total (pderiv 1 J)≤total J-1 at ht
  change order (pderiv 1 J)≤order J-1 at ho
  have hn := source_nested J
  unfold Caps at *
  omega

theorem source_from_caps (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (m d n B U T : ℕ) (hd : 0<d) (hm : d≤m) (hn : d≤n)
    (hord : n≤order J) (hB : 2*n≤B) (h : Caps J B U T)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m) :
    ∃ S : Source P.F, Fits S (degreeZ B U T d n) := by
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤max B (U-n) ∧
      e 1+e 2+e 3+e 4≤max (max B (U-n)) (T-n) := by
    intro e he
    have hb := (le_weightedTotalDegree slopeWeights he).trans h.1
    have hu := le_weightedTotalDegree middleWeights he
    have ht := le_weightedTotalDegree totalWeights he
    have hu' : middle J≤U-n := by have := h.2.1; omega
    have ht' : total J≤T-n := by have := h.2.2; omega
    have huc := hu.trans hu'
    have htc := ht.trans ht'
    refine ⟨?_,?_,?_⟩
    · simpa [weight_coords,slopeWeights,Nat.mul_comm] using hb
    · have hh : e 1+e 2+e 3≤U-n := by simpa [weight_coords,middleWeights] using huc
      exact hh.trans (le_max_right _ _)
    · have hh : e 1+e 2+e 3+e 4≤T-n := by simpa [weight_coords,totalWeights] using htc
      exact hh.trans (le_max_right _ _)
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨S,_,hp⟩ := PortfolioOwners6815.root_source_profile P.F P.rdegree hchar J
    m (order J) B (max B (U-n)) (max (max B (U-n)) (T-n)) (d-1) n
    (by omega) (by omega) hord le_rfl hB (le_max_left _ _) (le_max_left _ _) hshape hroot
  exact ⟨S,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2⟩

theorem complement_caps (J D : Poly (K:=K)) (a : Box) (h : Contains a (point J))
    (hb : slope J+slope D≤38) (hu : middle J+order J+(middle D+order D)≤136)
    (ht : total J+order J+(total D+order D)≤792) : Caps D (qB a) (qU a) (qT a) := by
  have hn := source_nested D
  dsimp only [Contains,point] at h
  dsimp only [Caps,qB,qU,qT]
  omega

theorem count_of_check (P : Packet x t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (J D : Poly (K:=K)) (hJ : Irreducible J) (hD : Irreducible D) (hcop : IsRelPrime J D)
    (mJ mD : ℕ) (hmJ : 2≤mJ) (hmD : 0<mD) (hsJ : 3≤order J) (hsD : 1≤order D)
    (hsJmax : order J≤17) (hJL : total J≤775) (hDL : total D≤775)
    (hJmul : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=mJ)
    (hDmul : ((asS D).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=mD)
    (hJroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hDroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) D=0)
    (hb : slope J+slope D≤38) (hu : middle J+order J+(middle D+order D)≤136)
    (ht : total J+order J+(total D+order D)≤792)
    (a : Box) (ha : Contains a (point J)) (c : Choice) (low cap : ℕ)
    (hFT : low≤wt residualTotalWeights P.F) (hlow : 1700<low)
    (hc : check c fixed a low t y r cap=true) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  obtain ⟨h6,hBU,hUT,hTmax,hqb,hcommon,hprice⟩ := of_decide_eq_true hc
  have hp : Caps J a.bhi a.uhi a.thi := ⟨ha.2.1,ha.2.2.2.1,ha.2.2.2.2.2⟩
  have hq := complement_caps J D a ha hb hu ht
  have hsrc : ∃ S : Source P.F, Fits S (chosenZ c.which fixed a) := by
    generalize he : c.which=which
    fin_cases which
    · exact ⟨fixedS,hFixed⟩
    · exact source_from_caps P J mJ 2 3 a.bhi a.uhi a.thi (by decide) hmJ (by decide) hsJ h6 hp hJmul
    · exact source_from_caps P D mD 1 1 (qB a) (qU a) (qT a)
        (by decide) hmD (by decide) hsD hqb hq hDmul
  obtain ⟨SZ,hZ⟩ := hsrc
  have hFchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  have hJenv := envelope J a.bhi a.uhi a.thi hp hBU hUT
  cases he : c.derivative with
  | false =>
    obtain ⟨SJ,hSJ,hJd⟩ := PortfolioSharedCount6815.root_source P J hJ.ne_zero 775 hJL (by omega) hJroot
    obtain ⟨SD,hSD,hDd⟩ := PortfolioSharedCount6815.root_source P D hD.ne_zero 775 hDL (by omega) hDroot
    have hDenv := envelope D (qB a) (qU a) (qT a) hq (min_le_right _ _) (min_le_right _ _)
    have hcop' : IsRelPrime SJ.P SD.P := by rwa [hSJ,hSD]
    rw [←hSJ] at hJenv
    rw [←hSD] at hDenv
    have hprice' : PortfolioBoxCheck6815.PairChecks (chosenZ c.which fixed a) 1 (pFlag a) (qFlag a) t y r cap := by
      simpa only [rhsFlag,he,Bool.false_eq_true,if_false] using hprice
    exact (pair_count_of_bounds P SZ SJ SD _ hZ (hcommon.1.trans_le hFT) hcommon.2.1 hcommon.2.2
      hcop' 1 (by decide) (by decide) hJd hDd _ _ hJenv hDenv hprice'.1 hprice'.2.1).trans
      (max_le_max le_rfl hprice'.2.2)
  | true =>
    obtain ⟨SJ,SQ,hSJ,hSQ,hcop',hJd,hQd,_⟩ := RamifiedOwnerDerivative6815.source_pair_of_ramified_owner
      P.F (hlow.trans_le hFT) P.rdegree hFchar J hJ (by omega)
      (by rw [asS_natDegree]; change 0<order J; omega)
      (by rw [asS_natDegree]; change order J<2130706433; omega) mJ hmJ hJmul
    have hDenv := envelope (pderiv 1 J) (a.bhi-2) (a.uhi-2) (a.thi-2)
      (derivative_caps J a.bhi a.uhi a.thi hp (by omega)) (by omega) (by omega)
    rw [←hSJ] at hJenv
    rw [←hSQ] at hDenv
    have hprice' : PortfolioBoxCheck6815.PairChecks (chosenZ c.which fixed a) 1 (pFlag a) (dFlag a) t y r cap := by
      simpa only [rhsFlag,he,if_true] using hprice
    exact (pair_count_of_bounds P SZ SJ SQ _ hZ (hcommon.1.trans_le hFT) hcommon.2.1 hcommon.2.2
      hcop' 1 (by decide) (by decide) (by omega) (by omega) _ _ hJenv hDenv hprice'.1 hprice'.2.1).trans
      (max_le_max le_rfl hprice'.2.2)

def initialBox : Box := ⟨6,34,6,132,6,788⟩

theorem count_of_covered (P : Packet x t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (J D : Poly (K:=K)) (hJ : Irreducible J) (hD : Irreducible D) (hcop : IsRelPrime J D)
    (mJ mD : ℕ) (hmJ : 2≤mJ) (hmD : 0<mD) (hsJ : 3≤order J) (hsD : 1≤order D)
    (hsJmax : order J≤17) (hJL : total J≤775) (hDL : total D≤775) (hDb : 4≤slope D)
    (hJmul : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=mJ)
    (hDmul : ((asS D).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=mD)
    (hJroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hDroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) D=0)
    (hb : slope J+slope D≤38) (hu : middle J+order J+(middle D+order D)≤136)
    (ht : total J+order J+(total D+order D)≤792)
    (low cap : ℕ) (hFT : low≤wt residualTotalWeights P.F) (hlow : 1700<low)
    (hc : Covered (Valid fixed low t y r cap) initialBox) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hnJ := source_nested J
  have hnD := source_nested D
  have hn : Nested (point J) := by dsimp only [Nested,point]; omega
  have ha : Contains initialBox (point J) := by dsimp only [Contains,initialBox,point]; omega
  obtain ⟨a,⟨c,hc⟩,ha⟩ := hc (point J) hn ha
  exact count_of_check P fixedS fixed hFixed J D hJ hD hcop mJ mD hmJ hmD hsJ hsD hsJmax
    hJL hDL hJmul hDmul hJroot hDroot hb hu ht a ha c low cap hFT hlow hc

end
end ProximityPrize.SubmissionLower.PortfolioRamifiedBoxes6815
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.SharedTreeCheck6815
open PortfolioRamifiedBoxes6815 PortfolioCost6815
set_option autoImplicit false

def choiceOf (j : ℕ) : Choice := ⟨⟨j/2%3,Nat.mod_lt _ (by decide)⟩,j%2=1⟩

def axisOf (x : ℕ) : Fin 3 := ⟨x/2%4%3,Nat.mod_lt _ (by decide)⟩

def run (fixed : Degrees) (low t y r cap : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0,_,_ => none
  | f+1,code,a =>
    let b := normalize 4 a
    let x := code%65536
    if x%2=0 then
      (if check (choiceOf (x/2)) fixed b low t y r cap then some (code/65536) else none)
    else
      match run fixed low t y r cap f (code/65536) (lower b (axisOf x) (x/8)) with
      | none => none
      | some c => run fixed low t y r cap f c (upper b (axisOf x) (x/8))

theorem run_sound (fixed : Degrees) (low t y r cap : ℕ) :
    ∀ f code a c, run fixed low t y r cap f code a=some c → Covered (Valid fixed low t y r cap) a := by
  intro f
  induction f with
  | zero => intro code a c h; simp [run] at h
  | succ f ih =>
    intro code a c h
    apply covered_normalize _ a (normalize 4 a) rfl
    simp only [run] at h
    split at h
    · split at h
      · exact covered_leaf _ _ ⟨_,by assumption⟩
      · simp at h
    · split at h
      · simp at h
      · rename_i c1 h1
        exact covered_split _ _ _ _ (ih _ _ _ h1) (ih _ _ _ h)

theorem covered_of_run (fixed : Degrees) (low t y r cap f code : ℕ) (a : Box)
    (h : (run fixed low t y r cap f code a).isSome=true) : Covered (Valid fixed low t y r cap) a := by
  cases hc : run fixed low t y r cap f code a with
  | none => simp [hc] at h
  | some c => exact run_sound fixed low t y r cap f code a c hc

end ProximityPrize.SubmissionLower.SharedTreeCheck6815
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.PortfolioUniqueCount6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceOwnerSplit6814
open MovingSourceNativeEnvelope6814 PortfolioOwners6815
open PortfolioBoxes6815 PortfolioBoxCount6815 PortfolioBoxCover6815 PortfolioCost6815
open PortfolioLinearRoute6815 PortfolioLinearPacket6815

def rootBox (B U L s m : ℕ) : Box :=
  ⟨max m 2,s/copies3 m,2*max m 2,B/copies3 m,0,U/copies3 m,0,L/copies3 m⟩

def LinearChecks (B U L t y r cap : ℕ) : Prop :=
  Gates t y r (B-2) (U-1) (L-1) ∧
  flagMixed ⟨t-y,y-r,r⟩ (firstFlag (2*B-3) (2*U-2) (2*L-2)) unitZFlag<2130706433 ∧
  linearPrice (firstFlag (2*B-3) (2*U-2) (2*L-2))
    (delayFlag (2*B-3) (2*U-2) (2*L-2)) t y r (B-2) (U-1) (L-1)≤cap
instance (B U L t y r cap : ℕ) : Decidable (LinearChecks B U L t y r cap) := by
  unfold LinearChecks Gates; infer_instance

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r : ℕ}

theorem packet_count (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (B U L s : ℕ) (hS : Profile S B U L s 2 3)
    (z : Degrees) (hZ : Fits SZ z) (low cap : ℕ)
    (hT : L≤995) (hFT : low≤wt residualTotalWeights P.F) (hlow : 2985<low)
    (hB : 14≤B) (hBU : B≤U) (hUL : U≤L) (hcap : 1000000000000000≤cap)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P)
    (hlc : LinearChecks (B/3) (U/3) (L/3) t y r cap)
    (hhigh : Gates t y r (B-14) (U-7) (L-7) ∧
      nativeScalar (PortfolioHighOwner6815.degrees B U L) t y r/21+
        leading (PortfolioHighOwner6815.degrees B U L) t y r≤cap)
    (hc : ∀ m, 0<m → m≤6 → Covered m (Valid z m low t y r cap) (rootBox B U L s m)) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨hm,hms,hb,hu,ht,hs,htriple,hne⟩ := unique_owner_data P.F S B U L s hS hT
    (hlow.trans_le hFT) P.rdegree hchar J hJ hJS hroot hunique
  let m := multiplicity P.F J
  have hm' : 0<m := hm
  have hq := copies3_pos m hm
  have hbd : slope J≤B/copies3 m := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hb)
  have hud : middle J≤U/copies3 m := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hu)
  have htd : total J≤L/copies3 m := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using ht)
  have hsd : order J≤s/copies3 m := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hs)
  have hn := source_nested J
  by_cases hlin : order J=1
  · have hme : m=1 := by omega
    have hqe : copies3 m=3 := by rw [hme]; rfl
    rw [hqe] at hbd hud htd
    have hshape : ∀ e∈J.support, 2*e 1+e 3≤B/3 ∧ e 1+e 2+e 3≤U/3 ∧ e 1+e 2+e 3+e 4≤L/3 := by
      intro e he
      have h1 := (le_weightedTotalDegree slopeWeights he).trans hbd
      have h2 := (le_weightedTotalDegree middleWeights he).trans hud
      have h3 := (le_weightedTotalDegree totalWeights he).trans htd
      refine ⟨?_,?_,?_⟩
      · simpa [weight_coords,slopeWeights,Nat.mul_comm] using h1
      · simpa [weight_coords,middleWeights] using h2
      · simpa [weight_coords,totalWeights] using h3
    exact (PortfolioLinearShape6815.packet_count_of_shape P J hJ.ne_zero hlin (B/3) (U/3) (L/3)
      (by omega) (Nat.div_le_div_right hBU) (Nat.div_le_div_right hUL) hshape
      (by have := Nat.div_le_self L 3; omega) hroot hlc.1 hlc.2.1).trans (max_le_max le_rfl hlc.2.2)
  have hs2 : 2≤order J := by omega
  have hb0 := hbd.trans (Nat.div_le_self B (copies3 m))
  have hu0 := hud.trans (Nat.div_le_self U (copies3 m))
  have ht0 := htd.trans (Nat.div_le_self L (copies3 m))
  have hs0 := hsd.trans (Nat.div_le_self s (copies3 m))
  by_cases hm7 : 7≤m
  · exact PortfolioHighOwner6815.packet_count P J m B U L s cap hm7 hms hs0 hb0 hu0 ht0
      hB hBU hUL (by omega) rfl hhigh.1 hhigh.2
  have ha : Admissible m (point J) := ⟨hms,hs2,htriple,hn.2.2.1,hn.2.1,hn.2.2.2,hn.1⟩
  have hx : Contains (rootBox B U L s m) (point J) := by
    dsimp only [Contains,rootBox,point]
    exact ⟨max_le hms hs2,hsd,by omega,hbd,Nat.zero_le _,hud,Nat.zero_le _,htd⟩
  exact count_of_covered nodes hI P SZ z hZ _ m low cap hFT (by omega) hcap J hJ ha hx rfl hne
    (hc m hm (by omega))

end
end ProximityPrize.SubmissionLower.PortfolioUniqueCount6815
end MergedPart8
