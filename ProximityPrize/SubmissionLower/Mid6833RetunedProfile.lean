/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Research adaptation of the 68.32 public proof architecture.
Prior authors: Lucieno (PR 618) and BitWonka (PR 581). Apache-2.0.
This file verifies an interpolation or scalar-list statement. -/
import ProximityPrize.SubmissionLower.Mid6833GenericJet

import ProximityPrize.SubmissionLower.Koala6831ResidualInactive
import ProximityPrize.SubmissionLower.Koala6831ResidualLocalTop
import ProximityPrize.SubmissionLower.Koala6831ResidualLowerBlock

namespace ProximityPrize.SubmissionLower.RetunedProfile

structure JetProfile where
  order : ℕ
  secondCap : ℕ
  slopeCap : ℕ
  middleCap : ℕ
  totalCap : ℕ
  derivativeOrder : ℕ
  minimumOrder : ℕ
  deriving DecidableEq

def jetProfile (_ : Fin 1) : JetProfile := ⟨62,25,11,84,411685,0,1⟩

open scoped BigOperators
open SecondJetRelaxedGlobalIndex

def topColumnActive {D : ℕ → ℕ} {w L B s U : ℕ} (m : ℕ)
    (i : Index D w L B s U) : Prop :=
  i.1.val + i.2.1.val + i.2.2.1.val = U ∧ i.2.2.1.val < m

instance {D : ℕ → ℕ} {w L B s U : ℕ} (m : ℕ) (i : Index D w L B s U) :
    Decidable (topColumnActive m i) := by
  unfold topColumnActive
  infer_instance

theorem topColumnActive_iff {D : ℕ → ℕ} {w L B s U : ℕ} (m : ℕ)
    (i : Index D w L B s U) :
    topColumnActive m i ↔
      exponent i 1 + exponent i 2 + exponent i 3 = U ∧ exponent i 2 < m := by
  rcases i with ⟨h,r,y,x,z⟩
  simp [topColumnActive, exponent, add_right_comm]

def liveTopWidth (D : ℕ → ℕ) (w U m h r : ℕ) : ℕ :=
  if U - h - r < m then budget D w h r - w*(U - h - r) else 0

theorem topColumnActive_card_le (D : ℕ → ℕ) (w L B s U m : ℕ) :
    Fintype.card {i : Index D w L B s U // topColumnActive m i} ≤
      (∑ h : Fin (s+1), ∑ r : Fin (B-2*h.val+1),
        liveTopWidth D w U m h.val r.val * (L+1-U)) := by
  let Target := Σ h : Fin (s+1), Σ r : Fin (B-2*h.val+1),
    Fin (liveTopWidth D w U m h.val r.val) × Fin (L+1-U)
  let embedding : {i : Index D w L B s U // topColumnActive m i} → Target := fun i => by
    have hActive := i.property
    unfold topColumnActive at hActive
    have hy : i.val.2.2.1.val = U-i.val.1.val-i.val.2.1.val := by omega
    refine ⟨i.val.1, i.val.2.1, ⟨i.val.2.2.2.1.val, ?_⟩, ⟨i.val.2.2.2.2.val, ?_⟩⟩
    · rw [liveTopWidth, ← hy, if_pos hActive.2]
      exact i.val.2.2.2.1.isLt
    · have hz := i.val.2.2.2.2.isLt
      omega
  have hinj : Function.Injective embedding := by
    rintro ⟨⟨h,r,y,x,z⟩,ha⟩ ⟨⟨h',r',y',x',z'⟩,ha'⟩ he
    have hh : h = h' := congrArg (fun i : Target => i.1) he
    subst h'
    have hr : r = r' := Fin.ext (congrArg (fun i : Target => i.2.1.val) he)
    subst r'
    have hy : y = y' := Fin.ext (by
      change h.val+r.val+y.val = U ∧ y.val < m at ha
      change h.val+r.val+y'.val = U ∧ y'.val < m at ha'
      omega)
    subst y'
    have hx : x = x' := Fin.ext (congrArg (fun i : Target => i.2.2.1.val) he)
    have hz : z = z' := Fin.ext (congrArg (fun i : Target => i.2.2.2.val) he)
    subst x'
    subst z'
    rfl
  simpa [Target] using Fintype.card_le_of_injective embedding hinj

def profileCutoff (p : JetProfile) (h : ℕ) : ℕ :=
  p.order*179740 - SecondJetRelaxedDifferentiation.reserve
    p.derivativeOrder p.minimumOrder h * 48671

abbrev ProfileIndex (j : Fin 1) :=
  let p := jetProfile j
  Index (profileCutoff p) 131071 p.totalCap p.secondCap p.slopeCap p.middleCap

def profileLowerRank (p : JetProfile) : ℕ :=
  SecondJetRelaxedCounts.rankBound p.order p.totalCap p.secondCap p.slopeCap (p.middleCap-1)

def profileTopRankBound (p : JetProfile) : ℕ :=
  ∑ h : Fin (p.slopeCap+1), ∑ r : Fin (p.secondCap-2*h.val+1),
    liveTopWidth (profileCutoff p) 131071 p.middleCap p.order h.val r.val *
      (p.totalCap+1-p.middleCap)

def profileColumnCount (p : JetProfile) : ℕ :=
  SecondJetRelaxedGlobalCounts.coefficientCount (profileCutoff p) 131071
    p.totalCap p.secondCap p.slopeCap p.middleCap

theorem profileMiddleCap_le_cutoff (j : Fin 1) (h : ℕ) :
    let p := jetProfile j
    p.middleCap ≤ (profileCutoff p h+p.secondCap-1)/131071 := by
  let p := jetProfile j
  let cap := max p.derivativeOrder (p.minimumOrder-1)
  have hre : SecondJetRelaxedDifferentiation.reserve p.derivativeOrder p.minimumOrder h ≤ cap := by
    unfold SecondJetRelaxedDifferentiation.reserve cap
    split <;> omega
  have hd : p.order*179740 - cap*48671 ≤ profileCutoff p h := by
    unfold profileCutoff
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_right 48671 hre) _
  have hl : p.middleCap ≤ (p.order*179740-cap*48671+p.secondCap-1)/131071 := by
    fin_cases j <;> decide
  change p.middleCap ≤ (profileCutoff p h + p.secondCap - 1) / 131071
  exact hl.trans (Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right hd _) _))

theorem profileLowerRank_eq_rankBound (j : Fin 1) :
    let p := jetProfile j
    SecondJetRelaxedGlobalMap.rankBound p.order p.totalCap p.secondCap p.slopeCap
      (p.middleCap-1) (fun h => (profileCutoff p h+p.secondCap-1)/131071) =
        profileLowerRank p := by
  apply SecondJetRelaxedCounts.rankBound_eq_closed
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · intro h _
    exact (Nat.sub_le _ _).trans (profileMiddleCap_le_cutoff j h)

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 60000 in
theorem profile_margin (j : Fin 1) :
    let p := jetProfile j
    262144 * profileLowerRank p + profileTopRankBound p < profileColumnCount p := by
  fin_cases j <;> decide +kernel

theorem profileColumnCount_eq_card (j : Fin 1) :
    profileColumnCount (jetProfile j) = Fintype.card (ProfileIndex j) := by
  have hUL : (jetProfile j).middleCap ≤ (jetProfile j).totalCap := by
    fin_cases j <;> decide
  exact (SecondJetRelaxedGlobalCounts.card_index_closed _ _ _ _ _ _ hUL).symm

theorem profile_top_rank_bound (j : Fin 1) :
    Fintype.card {i : ProfileIndex j // topColumnActive (jetProfile j).order i} ≤
      profileTopRankBound (jetProfile j) := by
  exact topColumnActive_card_le _ _ _ _ _ _ _

theorem profile_rank_lt_columns (j : Fin 1) :
    262144 * profileLowerRank (jetProfile j) +
      Fintype.card {i : ProfileIndex j // topColumnActive (jetProfile j).order i} <
      Fintype.card (ProfileIndex j) := by
  rw [← profileColumnCount_eq_card]
  exact (Nat.add_le_add_left (profile_top_rank_bound j) _).trans_lt (profile_margin j)

end ProximityPrize.SubmissionLower.RetunedProfile

#print axioms ProximityPrize.SubmissionLower.RetunedProfile.profile_rank_lt_columns



set_option Elab.async false

namespace ProximityPrize.SubmissionLower.RetunedProfile

open Koala6831Residual
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetSpecialize SecondJetRelaxedDifferentiation

noncomputable section

set_option autoImplicit false

variable {K N : Type*} [Field K] [Fintype N]

def ProfileInterpolant (p : JetProfile) (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K := K)) : Prop :=
  P ≠ 0 ∧
  (∀ e ∈ P.support, 2*e 1+e 3 ≤ p.secondCap ∧ e 1 ≤ p.slopeCap ∧
    e 1+e 2+e 3 ≤ p.middleCap ∧ e 1+e 2+e 3+e 4 ≤ p.totalCap ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < profileCutoff p (e 1)) ∧
  (∀ i, MvPolynomial.X 0^p.order ∣ substitute (K := K)
    (localize (nodes i) (u0 i) (u1 i) P)) ∧
  ∀ d ≤ p.derivativeOrder, ∀ f : Polynomial K, f.natDegree ≤ 131071 →
    ∀ z : K, ∀ S : Finset N, 179740 ≤ S.card →
      (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
        specialize f z ((pderiv 1)^[d] P) = 0

theorem exists_profile_interpolant (j : Fin 1) (hN : Fintype.card N ≤ 262144)
    (nodes : N ↪ K) (u0 u1 : N → K) :
    ∃ P, ProfileInterpolant (jetProfile j) nodes u0 u1 P := by
  classical
  let p := jetProfile j
  have hgate := profile_rank_lt_columns j
  have hid := profileLowerRank_eq_rankBound j
  have hdim : Fintype.card N *
        SecondJetRelaxedGlobalMap.rankBound p.order p.totalCap p.secondCap p.slopeCap (p.middleCap-1)
        (fun h => (profileCutoff p h+p.secondCap-1)/131071) +
      Fintype.card {i : ProfileIndex j // topColumnActive p.order i} <
      Fintype.card (ProfileIndex j) := by
    change SecondJetRelaxedGlobalMap.rankBound p.order p.totalCap p.secondCap p.slopeCap (p.middleCap-1)
        (fun h => (profileCutoff p h+p.secondCap-1)/131071) = profileLowerRank p at hid
    rw [hid]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ hN) _).trans_lt hgate
  exact FrontierGenericJet.exists_jet_of_dimension 179740 131071 p.order p.secondCap p.slopeCap
    p.middleCap p.totalCap p.derivativeOrder p.minimumOrder (by decide) (by decide) (by decide)
    (by norm_num [p,jetProfile]) (by norm_num [p,jetProfile]) (profileCutoff p) (fun _ => rfl)
    nodes u0 u1 hdim
end
end ProximityPrize.SubmissionLower.RetunedProfile
#print axioms ProximityPrize.SubmissionLower.RetunedProfile.exists_profile_interpolant
