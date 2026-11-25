import ProximityPrize.SubmissionLower.High6966PairCertificates
import ProximityPrize.SubmissionLower.High6966Main13200
import ProximityPrize.SubmissionLower.High6966Main15000

set_option Elab.async false

namespace Lower6960.Pair6966
open K1_14 (Jet L)
noncomputable section
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open Wide6966Helper (bankAt helperCutoff)
open PrefixRows (Common)
open Rescue6966 (word Family)
def space {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (cap:ℕ) :=
  evaluated Crt word (bankAt cap).shape (helperCutoff h)
theorem space_mono {h a b:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (le:a≤b) :
    space Crt word a ≤ space Crt word b :=
  K1_14_1.evaluated_mono Crt word (s:=(bankAt a).shape) (s':=(bankAt b).shape)
    (W:=helperCutoff h) (W':=helperCutoff h) rfl rfl rfl le le_rfl
theorem nonzero {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) {cap:ℕ}
    (lo:2330≤h) (hi:h≤2499) (room:4009≤cap) : ∃ P∈space Crt word cap,P≠0 := by
  let bank:=bankAt 4009
  have ck:=Wide6966Helper.checked 4009
  have sup:=HelperSource.crt_supply Crt word bank 179769 10 1 0 97 (by omega) (by omega)
    (by decide) ck.nodes ck.moment.1 ck.moment.2 (Wide6966Helper.helper_width lo (by omega))
    (Wide6966Helper.helper_surplus .seedBoundary lo (by omega))
  obtain ⟨P,mem,ne⟩:=HelperSource.nonzero_of_supply Crt word bank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)
  exact ⟨P,space_mono Crt word room mem,ne⟩
theorem unique {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (i:Fin 12)
    (lo:2330≤h) (hi:h≤2499) {G:Jet} (g:Common (space Crt word 20142) G)
    (M:Research6966.HelperPhysicalModel.Model Crt G) (degree:(row i).degree≤jetDegree G)
    (wt:(row i).wt≤Research6966.RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (seed:(row i).seed≤seedDegree G) :
    ∀ N T, Common (space Crt word (row i).cap) N → Common (space Crt word (row i).cap) T →
      IsRelPrime N T → False := by
  have sub : (row i).cap≤20142 := by fin_cases i <;> decide
  have current : Common (space Crt word (row i).cap) G :=
    ⟨g.1,g.2.1,g.2.2.1,fun P hP=>g.2.2.2 P (space_mono Crt word sub hP)⟩
  apply Research6966.HelperKnownPrime.unique_from_known current
  intro T t cop
  let q:=row i
  let bank:=bankAt q.cap
  have ck:=Wide6966Helper.checked q.cap
  have npos:0<Research6966.HelperWindowIntervals.cutoff bank.shape 179769 h 10 := by
    change 0<294*179769-2*h*10;omega
  have wide:bank.shape.B*(131071-h)≤Research6966.HelperWindowIntervals.cutoff bank.shape 179769 h 10 := by
    change 408*(131071-h)≤294*179769-2*h*10;omega
  have sc:bank.shape.U<K1.p:=sub.trans_lt (by decide)
  exact Research6966.HelperKnownPrime.not_coprime (by omega) (by omega) Crt word bank
    current t cop M (Lother:=128571) (by omega) degree wt seed sc (by decide : 408<K1.p)
    npos wide ck.nodes ck.moment.1 (ready i lo hi)
theorem chosen15000 {u deleted} {anchor : Rescue6966.Model u deleted} {Γ} (F:Family anchor Γ)
    {D:PoleData anchor.overhead.toNat} (Crt:CRTLift D) (i:Fin 12) (cap:(row i).cap=15000)
    (lo:2330≤anchor.overhead.toNat) (hi:anchor.overhead.toNat≤2499)
    (noPole:∀ j k,(D.block j).eval (nodeL k)≠0)
    (residues:∀ γ∈Γ,MarkResidues D (anchor.label γ) (F.scalar γ))
    {G:Jet} (g:Common (space Crt (word anchor) 20142) G) (M:Research6966.HelperPhysicalModel.Model Crt G)
    (degree:(row i).degree≤jetDegree G) (wt:(row i).wt≤Research6966.RawPhysicalDegree.weight
      (131071-anchor.overhead.toNat) (131071-anchor.overhead.toNat-1) M.raw)
    (seed:(row i).seed≤seedDegree G) : Nonempty (High6966Main15000.Rows F Crt) := by
  apply High6966Main15000.rows F Crt lo (by omega) noPole residues (nonzero Crt (word anchor) lo hi (by decide : 4009≤15000))
  have unique0:=unique Crt (word anchor) i lo hi g M degree wt seed
  rw [cap] at unique0
  exact unique0
#print axioms chosen15000
theorem chosen13200 {u deleted} {anchor : Rescue6966.Model u deleted} {Γ} (F:Family anchor Γ)
    {D:PoleData anchor.overhead.toNat} (Crt:CRTLift D) (i:Fin 12) (cap:(row i).cap=13200)
    (lo:2330≤anchor.overhead.toNat) (hi:anchor.overhead.toNat≤2499)
    (noPole:∀ j k,(D.block j).eval (nodeL k)≠0)
    (residues:∀ γ∈Γ,MarkResidues D (anchor.label γ) (F.scalar γ))
    {G:Jet} (g:Common (space Crt (word anchor) 20142) G) (M:Research6966.HelperPhysicalModel.Model Crt G)
    (degree:(row i).degree≤jetDegree G) (wt:(row i).wt≤Research6966.RawPhysicalDegree.weight
      (131071-anchor.overhead.toNat) (131071-anchor.overhead.toNat-1) M.raw)
    (seed:(row i).seed≤seedDegree G) : Nonempty (High6966Main13200.Rows F Crt) := by
  apply High6966Main13200.rows F Crt lo (by omega) noPole residues (nonzero Crt (word anchor) lo hi (by decide : 4009≤13200))
  have unique0:=unique Crt (word anchor) i lo hi g M degree wt seed
  rw [cap] at unique0
  exact unique0
#print axioms chosen13200
end
end Lower6960.Pair6966
