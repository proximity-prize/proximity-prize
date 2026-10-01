import ProximityPrize.SubmissionLower.MergedInfra6815_44
import ProximityPrize.SubmissionLower.MergedInfra6815_3
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.PortfolioPriceIntervals6815
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN095 RCN260
open PortfolioCost6815 PortfolioChord6815 MovingSourceBandLeading6815
open MovingSourcePairRetainedStage6814 MovingSourceBandPairArithmetic6814

theorem mixed_chord {lo hi : ℕ} {f g : ℕ → ℕ}
    (hf : Chord lo hi f) (hg : Chord lo hi g)
    (a b c d : ℕ) (W : FlagDegree) :
    Chord lo hi (fun x => flagMixed ⟨f x,a,b⟩ ⟨g x,c,d⟩ W) := by
  have he : (fun x => flagMixed ⟨f x,a,b⟩ ⟨g x,c,d⟩ W)=
      (fun x => (d*W.all+c*W.all+W.yz*d)*f x+
        (b*W.all+a*W.all+W.yz*b)*g x+flagMixed ⟨0,a,b⟩ ⟨0,c,d⟩ W) := by
    funext x
    simp only [flagMixed]
    ring
  rw [he]
  exact add (add (mul_left hf _) (mul_left hg _)) (constant lo hi _)

def numerator (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r : ℕ) : ℕ :=
  pairNumerator (z.d*delta) (delta*flagMixed (parent t y r) unitZFlag z.flag)
    (z.d*flagMixed p q unitYZFlag) (z.d*flagMixed p q unitAllFlag) t y r (parent t y r)

def leadingNumerator (z : Degrees) (t y r : ℕ) : ℕ :=
  AsymmetricHelper.leftRegularNumerator (pair t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))

def totalNumerator (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r : ℕ) : ℕ :=
  50174*numerator z delta p q t y r+3*(z.d*delta)*leadingNumerator z t y r

theorem price_le_of_total (z : Degrees) (delta : ℕ) (hd : 0<delta)
    (p q : FlagDegree) (t y r cap : ℕ)
    (h : totalNumerator z delta p q t y r≤50174*(3*(z.d*delta))*cap) :
    pairCost z delta p q t y r+leading z t y r≤cap := by
  have hn : pairCost z delta p q t y r*(3*(z.d*delta))≤numerator z delta p q t y r :=
    Nat.div_mul_le_self _ _
  have hl : leading z t y r*50174≤leadingNumerator z t y r := by
    change AsymmetricHelper.leftRegularCountCap (pair t y r _ _ _)*50174≤_
    simpa only [AsymmetricHelper.leftRegularCountCap,pair,UnequalParameters.gap,Nat.reduceSub,
      leadingNumerator] using
      Nat.div_mul_le_self (leadingNumerator z t y r) 50174
  have h1 := Nat.mul_le_mul_left 50174 hn
  have h2 := Nat.mul_le_mul_left (3*(z.d*delta)) hl
  have hdz : 0<z.d := by dsimp [Degrees.d]; omega
  apply Nat.le_of_mul_le_mul_left (c:=50174*(3*(z.d*delta))) ?_
    (by positivity)
  dsimp only [totalNumerator] at h
  nlinarith only [h,h1,h2]

theorem numerator_chord {lo hi : ℕ} {f g : ℕ → ℕ}
    (hf : Chord lo hi f) (hg : Chord lo hi g)
    (a b c d : ℕ) (z : Degrees) (delta t y r : ℕ) :
    Chord lo hi (fun x => numerator z delta ⟨f x,a,b⟩ ⟨g x,c,d⟩ t y r) := by
  simp only [numerator,pairNumerator_eq]
  exact add (add (constant lo hi _) (mul_left (mul_left (mixed_chord hf hg a b c d unitYZFlag) z.d) _))
    (mul_left (mul_left (mixed_chord hf hg a b c d unitAllFlag) z.d) _)

theorem total_chord {lo hi : ℕ} {f g : ℕ → ℕ}
    (hf : Chord lo hi f) (hg : Chord lo hi g)
    (a b c d : ℕ) (z : Degrees) (delta t y r : ℕ) :
    Chord lo hi (fun x => totalNumerator z delta ⟨f x,a,b⟩ ⟨g x,c,d⟩ t y r) :=
  add (mul_left (numerator_chord hf hg a b c d z delta t y r) 50174) (constant lo hi _)

def ownerFlag (s b u x : ℕ) : FlagDegree := ⟨x-u,u+s-b,b⟩
def cofactorFlag (B U L S e s b u x : ℕ) : FlagDegree :=
  let rb := B-e*b
  let ru := Max.max rb (U-e*u)
  ⟨L-(e*x+ru),ru+(S-e*s)-rb,rb⟩

theorem cofactor_total_chord (lo hi s b u B U L S e : ℕ) (z : Degrees) (delta t y r : ℕ) :
    Chord lo hi (fun x => totalNumerator z delta (ownerFlag s b u x)
      (cofactorFlag B U L S e s b u x) t y r) := by
  have hf : Chord lo hi (fun x => x-u) := by
    simpa only [Nat.one_mul,Nat.zero_mul,Nat.add_zero,Nat.zero_add] using sub_affine lo hi 1 0 0 u
  have hg : Chord lo hi (fun x => L-(e*x+Max.max (B-e*b) (U-e*u))) := by
    simpa only [Nat.zero_mul,Nat.zero_add] using sub_affine lo hi 0 L e (Max.max (B-e*b) (U-e*u))
  exact total_chord hf hg _ _ _ _ z delta t y r

theorem cofactor_interval_price (lo hi s b u B U L S e : ℕ) (z : Degrees)
    (delta t y r cap : ℕ) (hd : 0<delta)
    (hlo : totalNumerator z delta (ownerFlag s b u lo) (cofactorFlag B U L S e s b u lo) t y r≤
      50174*(3*(z.d*delta))*cap)
    (hhi : totalNumerator z delta (ownerFlag s b u hi) (cofactorFlag B U L S e s b u hi) t y r≤
      50174*(3*(z.d*delta))*cap)
    (x : ℕ) (hx : lo≤x) (hx' : x≤hi) :
    pairCost z delta (ownerFlag s b u x) (cofactorFlag B U L S e s b u x) t y r+
      leading z t y r≤cap :=
  price_le_of_total z delta hd _ _ t y r cap
    (le_of_endpoints (cofactor_total_chord lo hi s b u B U L S e z delta t y r) _ hlo hhi x hx hx')

end ProximityPrize.SubmissionLower.PortfolioPriceIntervals6815
end MergedPart0
section MergedPart1
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
end MergedPart1
section MergedPart2
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
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.PortfolioReceiptChecks6815
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 50000
open PortfolioSource6815 PortfolioCost6815 PortfolioPriceIntervals6815 PortfolioAuxiliaryCount6815

instance (p : Parameters) (m s b u e : ℕ) : Decidable (active p m s b u e) := by
  unfold active
  infer_instance

def GoodPower (i : Fin 75) (m s b u lo : ℕ) : Prop :=
  let p := PortfolioSourceCatalogue6815.profile i
  (PacketPortfolioAvoidance6815.Impossible (PortfolioAvoidanceSource6815.caps p) (box p m s b u lo) ∧
    0<PortfolioSourceCatalogue6815.kernel i) ∨
  PacketPortfolioAvoidance6815.count (PortfolioAvoidanceSource6815.caps p) (box p m s b u lo)<
    PortfolioSourceCatalogue6815.kernel i

instance (i : Fin 75) (m s b u lo : ℕ) : Decidable (GoodPower i m s b u lo) := by
  unfold GoodPower PacketPortfolioAvoidance6815.Impossible
  infer_instance

def checkExit (p : Parameters) (z : Degrees) (m s b u lo hi t y r cap e : ℕ) : Bool :=
  if active p m s b u e ∧ lo≤upper p.L e hi then
    decide (totalNumerator z (min m (p.k+1-e*m)) (ownerFlag s b u lo)
        (cofactorFlag p.B p.U p.L p.s e s b u lo) t y r≤
          50174*(3*(z.d*min m (p.k+1-e*m)))*cap ∧
      totalNumerator z (min m (p.k+1-e*m)) (ownerFlag s b u (upper p.L e hi))
        (cofactorFlag p.B p.U p.L p.s e s b u (upper p.L e hi)) t y r≤
          50174*(3*(z.d*min m (p.k+1-e*m)))*cap)
  else true

def checkEndpoints (p : Parameters) (z : Degrees) (m s b u lo hi t y r cap : ℕ) : Bool :=
  (List.range (box p m s b u lo).q).all (checkExit p z m s b u lo hi t y r cap)

def checkAux (i : Fin 75) (z : Degrees) (m s b u lo hi t y r cap : ℕ) : Bool :=
  decide (GoodPower i m s b u lo) &&
    checkEndpoints (PortfolioSourceCatalogue6815.profile i) z m s b u lo hi t y r cap

theorem endpoints_spec (p : Parameters) (z : Degrees) (m s b u lo hi t y r cap : ℕ)
    (h : checkEndpoints p z m s b u lo hi t y r cap=true) :
    EndpointChecks p z m s b u lo hi t y r cap := by
  intro e he ha hl
  have hh := List.all_eq_true.mp h e (List.mem_range.mpr he)
  have hcond : active p m s b u e ∧ lo≤upper p.L e hi := ⟨ha,hl⟩
  simpa only [checkExit,if_pos hcond,decide_eq_true_eq] using hh

theorem aux_spec (i : Fin 75) (z : Degrees) (m s b u lo hi t y r cap : ℕ)
    (h : checkAux i z m s b u lo hi t y r cap=true) :
    GoodPower i m s b u lo ∧
      EndpointChecks (PortfolioSourceCatalogue6815.profile i) z m s b u lo hi t y r cap := by
  have hh := h
  simp only [checkAux,Bool.and_eq_true,decide_eq_true_eq] at hh
  exact ⟨hh.1,endpoints_spec _ _ _ _ _ _ _ _ _ _ _ _ hh.2⟩

end ProximityPrize.SubmissionLower.PortfolioReceiptChecks6815
end MergedPart3
