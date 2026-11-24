import ProximityPrize.SubmissionLower.R6960HelperSource6960
import ProximityPrize.SubmissionLower.R6960PrefixRows

noncomputable section
set_option Elab.async false
namespace Lower6960.PrefixRows
open Polynomial Finset
open K1_14 (Shape Jet L liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (jetMarkHom toJet)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Lower6960.HelperSource
open Lower6960.DifferentialContact (Native)

/-- These are the four inclusive degree rectangles used to price the rescue banks. -/
def rescueDegrees (G : Jet) : Prop :=
  G.natDegree=1 ∧
    ((jetDegree G=1 ∧ seedDegree G=1) ∨
     (jetDegree G=1 ∧ 2≤seedDegree G ∧ seedDegree G≤6) ∨
     (jetDegree G=1 ∧ 7≤seedDegree G ∧ seedDegree G≤85) ∨
     (2≤jetDegree G ∧ jetDegree G≤7 ∧ 1≤seedDegree G ∧ seedDegree G≤78))

/-- For the actual 69.60 bank a single powered helper works on the whole
prefix, and its possible exception belongs to one of the four rescue classes. -/
theorem prepare_6960 {ι : Type*} [Fintype ι] (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (proper : ∀ i,P i≠0) (caps : ∀ i,K1_14_2_2.RowCaps (P i) (s i))
    {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2339≤h) (hi : h≤33561) :
    let V := evaluated Crt word helperBank.shape (helperCutoff h)
    ∃ out : Prepared P s ks V helperBank.shape, out.exception=1 ∨ rescueDegrees out.exception := by
  obtain ⟨out⟩ := prepare P s ks _ helperBank.shape proper caps
    (helper_nonzero Crt word lo hi) (fun _ inside=>evaluated_shape Crt word inside)
    (fun _ _ g i cop=>helper_not_two Crt word lo hi g.1 i.1 cop g.2.1 i.2.1 g.2.2.1
      i.2.2.1 g.2.2.2 i.2.2.2)
  refine ⟨out,out.kind.imp_right ?_⟩
  intro g
  obtain ⟨slope,b0,b1,u0,u1,mixed⟩ :=
    helper_common_caps Crt word lo hi g.1 g.2.2.1 g.2.1 g.2.2.2
  unfold rescueDegrees
  omega

#print axioms prepare_6960

/-- All derivatives used for the main prefix vanish at every retained mark,
including for a powered helper or a stripped free row outside its source space. -/
theorem native_at_6960 {ι : Type*} {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2339≤h) (hi : h≤33561) {P : ι→Jet} {s : ι→Shape} {ks : ι→ℕ}
    (out : Prepared P s ks (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape)
    (i : ι) (W r : ℕ) (inside : P i∈evaluated Crt word (s i) W)
    (width : W+2*h*r<(s i).m*179827) (power : r+1≤ks i*11)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (z : K1.K) (S : (Polynomial K1.K)) (residues : MarkResidues D z S)
    (degree : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset K1.I) (many : 179827≤hits.card)
    (agree : ∀ i ∈ hits, (liftPoly S).eval (nodeL i) = word i)
    (regular : toJet out.exception∉RingHom.ker (jetMarkHom z S)) :
    Native (RingHom.ker (jetMarkHom z S)) (r+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom z S)) (r+1) (out.helper^(ks i)) := by
  apply out.contacts i _ (RingHom.ker_isPrime _) regular (r+1) 11 power
  · exact contact_of_crt Crt word (s i) _ inside width noPole z S residues degree hits many agree
  · intro H member
    have wh := helper_width lo hi
    unfold WidthGuard cutoffCount at wh
    have fit : helperCutoff h + 2*h*10 < helperBank.shape.m*179827 := by
      unfold helperCutoff cutoffCount
      omega
    exact contact_of_crt Crt word helperBank.shape H member fit noPole z S residues degree hits many agree

#print axioms native_at_6960
end Lower6960.PrefixRows
