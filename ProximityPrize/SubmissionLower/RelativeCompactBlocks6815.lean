import ProximityPrize.SubmissionLower.RelativeFastRecordCover6815
namespace ProximityPrize.SubmissionLower.RelativeCompactBlocks6815
open RelativeCertificate6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 40000

structure Profile where
  alpha : ℕ
  beta : ℕ
  s : ℕ
structure Entry where
  hi : ℕ
  profile : ℕ
  L0 : ℕ
  deltaL : ℕ
  witness : ℕ

structure Layout where
  hiBase : ℕ
  profileBase : ℕ
  lengthBase : ℕ
  deltaBase : ℕ
def decode (l : Layout) (n : ℕ) : Entry :=
  ⟨n%l.hiBase,(n/l.hiBase)%l.profileBase,
    (n/l.hiBase/l.profileBase)%l.lengthBase,
    (n/l.hiBase/l.profileBase/l.lengthBase)%l.deltaBase,
    n/l.hiBase/l.profileBase/l.lengthBase/l.deltaBase⟩

def rectangle (b : Band) (profiles : ℕ → Profile) (lo : ℕ) (e : Entry) : Rectangle :=
  let p := profiles e.profile
  let L1 := if e.deltaL%2=0 then e.L0+e.deltaL/2 else e.L0-e.deltaL/2
  let d : Rectangle := ⟨lo,e.hi,p.alpha,p.beta,p.s,e.L0,L1,0⟩
  {d with U:=(cutoff b d-1)/131071}
def fastWitness (e : Entry) : FastWitness :=
  ⟨e.witness%256,(e.witness/256)%256,e.witness/65536⟩

def checkBlock (b : Band) (profiles : ℕ → Profile) (stop : ℕ) : ℕ → List Entry → Bool
  | start,[] => decide (stop+1=start)
  | start,e::es => decide (FastValid b (rectangle b profiles start e,fastWitness e)) &&
      checkBlock b profiles stop (e.hi+1) es

def Covered (b : Band) (lo hi : ℕ) : Prop :=
  ∀ nu, lo≤nu → nu≤hi → ∃ d : Rectangle, Valid b d ∧ d.lo≤nu ∧ nu≤d.hi

theorem block_sound (b : Band) (profiles : ℕ → Profile) (start stop : ℕ) (es : List Entry)
    (hc : checkBlock b profiles stop start es=true) : Covered b start stop := by
  intro nu hlo hhi
  induction es generalizing start with
  | nil => simp only [checkBlock,decide_eq_true_eq] at hc; omega
  | cons e es ih =>
    simp only [checkBlock,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases he : nu≤e.hi
    · exact ⟨rectangle b profiles start e,fastValid_sound b _ hc.1,hlo,he⟩
    · exact ih (e.hi+1) hc.2 (by omega)

theorem covered_join (b : Band) (lo mid hi : ℕ)
    (h0 : Covered b lo mid) (h1 : Covered b (mid+1) hi) : Covered b lo hi := by
  intro nu hlo hhi
  by_cases h : nu≤mid
  · exact h0 nu hlo h
  · exact h1 nu (by omega) hhi

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K

theorem regular_count (b : Band) (hc : Covered b (minimumWeight b) (tail b))
    (hrange : minimumWeight b≤tail b)
    {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T b.R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : b.R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤b.B)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hnu : minimumWeight b≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤b.count := by
  obtain ⟨d,hd,hlo,hhi⟩ := hc (min nu (tail b)) (le_min hnu hrange) (min_le_right _ _)
  exact regular_count_of_rectangle K I b d hd F hbox hcode htotal hslope hB hT0 hT1
    (hlo.trans (min_le_left _ _)) hhi nodes u0 u1 hcard selected Gamma hdegree hagreement hno

end
end ProximityPrize.SubmissionLower.RelativeCompactBlocks6815
