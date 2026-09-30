import ProximityPrize.SubmissionLower.PortfolioBoxCheck6815
import ProximityPrize.SubmissionLower.PortfolioSharedCount6815
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
