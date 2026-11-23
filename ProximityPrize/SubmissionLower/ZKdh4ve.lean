import ProximityPrize.SubmissionLower.Z877yta
import ProximityPrize.SubmissionLower.Zg9AXud
set_option Elab.async false
namespace qEAs6me
open qfbIfsd (kK Detects)
open qBl3Pad (incidence)
open q2tSkEc (caps orders)
open private detects from ProximityPrize.SubmissionLower.Z877yta
def c1 :Prop :=
  ∀ (s b d:ℕ),2≤d →
    ∃ P:Coeff s b d,P.totalDegree≤kK s (caps b s) (orders d) ∧
      incidence s (caps b s) (orders d) P=0 ∧
      ∀ S:Coeff s b d,incidence s (caps b s) (orders d) S=0→P∣S
def c2 :Prop :=
  ∀ (s b d:ℕ),2≤d →
    ∃ S:Coeff s b d,incidence s (caps b s) (orders d) S=0∧tie S≠0
def c3:Prop :=
  ∀ (s b d:ℕ),2≤d → ∀ R:Coeff s b d,Detects R →
    topRes∣tie R
theorem of_children (raw:c1) (safe :c2) (boundary :c3) :q2tSkEc.c1 := by
  intro s b d hd
  obtain ⟨P,hdeg,hP,hdiv⟩:=raw s b d hd
  obtain ⟨S,hS,hs⟩:=safe s b d hd
  obtain ⟨T,hT⟩:=hdiv S hS
  have htie :tie P≠0:= fun h=>hs (by rw [hT,map_mul,h,zero_mul])
  have hdetect :Detects P:=detects hP
  obtain ⟨Q,hQ⟩:=boundary s b d hd P hdetect
  have hne :Q≠0:= fun h=>htie (by simp [hQ,h])
  refine ⟨Q,hne,?_,detect_quotient hd Q (hQ ▸ detect_tie hdetect)⟩
  have hdegP:=(tie_degree P).trans hdeg
  rw [hQ,MvPolynomial.totalDegree_mul_of_isDomain (topRes_ne s b d) hne] at hdegP
  have htop:=topRes_degree s b d
  omega
end qEAs6me
