import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

def hasContactProfile (s : SourceShape) : Bool :=
  (List.finRange contactProfiles.size).any (fun i => decide (contactProfiles[i] = s))

theorem contactProfile_of_check (s : SourceShape) (h : hasContactProfile s = true) :
    ∃ i : Fin contactProfiles.size, contactProfiles[i] = s := by
  obtain ⟨i,_,hei⟩ := List.any_eq_true.mp h
  exact ⟨i,of_decide_eq_true hei⟩

def terminalMetadata (e : CertifiedEndpoint) : Bool :=
  match e.receipt with
  | .intrinsic _ _ => true
  | .terminal src _ _ => decide (e.flag.r ≤ 20 ∧ e.flag.y ≤ 86) &&
      hasContactProfile src.z && hasContactProfile src.yz && hasContactProfile src.all

structure TerminalMetadata (f : Flag) (src : Sources) : Prop where
  slope : f.r ≤ 20
  middle : f.y ≤ 86
  z : ∃ i : Fin contactProfiles.size, contactProfiles[i] = src.z
  yz : ∃ i : Fin contactProfiles.size, contactProfiles[i] = src.yz
  all : ∃ i : Fin contactProfiles.size, contactProfiles[i] = src.all

theorem terminalMetadata_of_check
    (f : Flag) (p : Nat) (src : Sources) (bound : terminalPrice f src = some p)
    (fits : p ≤ terminalBudget) (h : terminalMetadata ⟨f,p,.terminal src bound fits⟩ = true) :
    TerminalMetadata f src := by
  have ⟨h₀,hA⟩ := Bool.and_eq_true_iff.mp h
  have ⟨h₁,hM⟩ := Bool.and_eq_true_iff.mp h₀
  have ⟨hCap,hZ⟩ := Bool.and_eq_true_iff.mp h₁
  obtain ⟨hr,hy⟩ := of_decide_eq_true hCap
  exact ⟨hr,hy,contactProfile_of_check src.z hZ,contactProfile_of_check src.yz hM,
    contactProfile_of_check src.all hA⟩

private theorem true_not_of_false (a : Bool) (h : (!a) = false) : a = true := by
  cases a <;> simp_all

theorem terminalPrice_order {f : Flag} {src : Sources} {p : Nat}
    (h : terminalPrice f src = some p) :
    f.r ≤ f.y ∧ f.y ≤ f.t ∧ f.y ≤ src.totalCap ∧ src.totalCap + f.y ≤ f.t := by
  unfold terminalPrice at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hgate
    have hg := Bool.eq_false_iff.mpr hgate
    obtain ⟨hw,hc⟩ := Bool.or_eq_false_iff.mp hg
    have hwo := of_decide_eq_true (true_not_of_false _ hw)
    have hsplit := of_decide_eq_true (true_not_of_false _ hc)
    exact ⟨hwo.2.1,hwo.2.2,hsplit.1,hsplit.2.2⟩

end ProximityPrize.SubmissionLower.Koala6844Receipts
