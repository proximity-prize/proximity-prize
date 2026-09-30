import ProximityPrize.SubmissionLower.RelativeRecordCover6815
import ProximityPrize.SubmissionLower.RelativeWideRectangle6815
namespace ProximityPrize.SubmissionLower.RelativeCertificate6815
open RelativeCertificate6814
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def wideCheckList (b : Band) : List Rectangle → Bool
  | [] => true
  | d::ds => decide (WideValid b d) && wideCheckList b ds

theorem wideCheckList_spec (b : Band) (xs : List Rectangle) (hc : wideCheckList b xs=true) :
    ∀ d∈xs, WideValid b d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [wideCheckList,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro d hd
    rcases List.mem_cons.mp hd with he | he
    · simpa only [he] using hc.1
    · exact ih hc.2 d he

theorem wideCheckList_append (b : Band) (xs ys : List Rectangle) :
    wideCheckList b (xs++ys)=(wideCheckList b xs && wideCheckList b ys) := by
  induction xs with
  | nil => simp [wideCheckList]
  | cons x xs ih => simp only [List.cons_append,wideCheckList,ih,Bool.and_assoc]

theorem wideCheckList_append_of (b : Band) (xs ys : List Rectangle)
    (hx : wideCheckList b xs=true) (hy : wideCheckList b ys=true) :
    wideCheckList b (xs++ys)=true := by
  rw [wideCheckList_append, hx, hy]; rfl

def WideVerifiedCover (b : Band) (start : ℕ) (xs : List Rectangle) : Prop :=
  wideCheckList b xs=true ∧ covers start (tail b) xs=true ∧ start≤tail b

variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance wideCoverDecEqK : DecidableEq K := Classical.decEq K

theorem regular_count_of_wide_cover (b : Band) (start : ℕ) (xs : List Rectangle)
    (hc : WideVerifiedCover b start xs)
    {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T b.R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : b.R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤b.B)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hnu : start≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤b.count := by
  obtain ⟨d,hd,hlo,hhi⟩ := covers_spec xs start (tail b) hc.2.1
    (min nu (tail b)) (le_min hnu hc.2.2) (min_le_right _ _)
  exact regular_count_of_wide_rectangle K I b d (wideCheckList_spec b xs hc.1 d hd) F hbox hcode
    htotal hslope hB hT0 hT1 (hlo.trans (min_le_left _ _)) hhi nodes u0 u1 hcard
    selected Gamma hdegree hagreement hno

end
end ProximityPrize.SubmissionLower.RelativeCertificate6815
