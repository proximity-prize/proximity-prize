import ProximityPrize.SubmissionLower.R6960DifferentialContact

noncomputable section
set_option Elab.async false
namespace Lower6960.PrefixRows
open Polynomial Finset
open K1 (I K)
open K1_14 (Shape Jet FX Seeds Equation L liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (Ambient toJet UsesSeed jetMarkHom)
open Lower6960.DifferentialContact (Native native_strip native_power weaken)
open Lower6960.HelperPrefix (one_helper timesShape)
open K1_14_2_2_3 (shiftedWord shift_word)
open K1_14_2_2_2_1 (divisor_caps)
open scoped Classical

/-- Mixed seed contact of a buffered CRT source at an actual marked word. -/
theorem contact_of_crt {h agreement W reserve : ℕ} {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (P : Jet)
    (inside : P ∈ evaluated Crt word s W) (width : W + 2*h*reserve < s.m*agreement)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (z : K) (S : (Polynomial K)) (residues : MarkResidues D z S)
    (degree : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset I) (many : agreement ≤ hits.card)
    (agree : ∀ i ∈ hits, (liftPoly S).eval (nodeL i) = word i) :
    Native (RingHom.ker (jetMarkHom z S)) (reserve+1) P := by
  intro w hw
  have shift : K1_14_3.SeedShift h (evaluated Crt word) s :=
    fun _ _ hin i r => P0_10_1.evaluated_shift Crt word hin i r
  have mem := shift_word shift inside w
  have fit : W+2*h*w.length<s.m*agreement :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : w.length≤reserve)) _) width
  apply RingHom.mem_ker.mpr
  rw [K1_14_2.eval_toJet]
  exact P0_10_1.contact_vanish Crt word noPole z S residues degree hits many agree _ _ fit _ mem

def Common (V : Submodule FX Jet) (G : Jet) : Prop :=
  Irreducible G ∧ 0<G.natDegree ∧ UsesSeed G ∧ ∀ H∈V, G∣H

/-- A prepared family supplies the precise rows, caps and contact consumed
by the prefix. The exception is a unit when no factor is common. -/
structure Prepared {ι : Type*} (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (V : Submodule FX Jet) (hs : Shape) where
  exception : Jet
  kind : exception=1 ∨ Common V exception
  free : ι→Jet
  helper : Jet
  helper_mem : helper∈V
  helper_ne : helper≠0
  free_ne : ∀ i,free i≠0
  stripped : ∀ i,∃ k : ℕ, P i=exception^k*free i
  free_caps : ∀ i,K1_14_2_2.RowCaps (free i) (s i)
  moving_caps : ∀ i,K1_14_2_2.RowCaps (helper^(ks i)) (timesShape (ks i) hs)
  no_moving : ∀ i,K1_14_3.NoMovingCommon (free i) (helper^(ks i))
  contacts : ∀ i (J : Ideal Ambient),J.IsPrime → toJet exception∉J →
    ∀ r a : ℕ, r≤ks i*a → Native J r (P i) → (∀ H∈V,Native J a H) →
      Native J r (free i) ∧ Native J r (helper^(ks i))

theorem power_caps {H : Jet} {hs : Shape} (hn : H≠0)
    (cap : K1_14_2_2.RowCaps H hs) (k : ℕ) :
    K1_14_2_2.RowCaps (H^k) (timesShape k hs) := by
  open K1_14_2_2_2_1 in
    obtain ⟨hb,hj,hu⟩ := (rowCaps_iff H hs).mp cap
    apply (rowCaps_iff ..).mpr
    have b : jetDegree (H^k)=k*jetDegree H := P1_7_4_1.factorDegree_pow hn k 0
    have u : seedDegree (H^k)=k*seedDegree H := P1_7_4_1.factorDegree_pow hn k 2
    rw [b,u,natDegree_pow]
    exact ⟨Nat.mul_le_mul_left k hb,Nat.mul_le_mul_left k hj,Nat.mul_le_mul_left k hu⟩

theorem prepare {ι : Type*} [Fintype ι] (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (V : Submodule FX Jet) (hs : Shape)
    (proper : ∀ i,P i≠0) (caps : ∀ i,K1_14_2_2.RowCaps (P i) (s i))
    (nonzero : ∃ H∈V,H≠0) (vcaps : ∀ H∈V,K1_14_2_2.RowCaps H hs)
    (unique : ∀ G H,Common V G → Common V H → IsRelPrime G H → False) :
    Nonempty (Prepared P s ks V hs) := by
  classical
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D:=Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=Equation)
  have select (G : Jet) (kind : G=1 ∨ Common V G) (F : ι→Jet)
      (fac : ∀ i,∃ n : ℕ,P i=G^n*F i) (none : ∀ i Q,Common V Q → ¬ Q∣F i) :
      Nonempty (Prepared P s ks V hs) := by
    have nf (i) : F i≠0 := by
      obtain ⟨n,e⟩ := fac i
      exact right_ne_zero_of_mul (e ▸ proper i)
    obtain ⟨H,mem,nh,avoid⟩ := one_helper F ks V nonzero nf (by
      intro i Q irr div pos useed
      by_contra! all
      exact none i Q ⟨irr,pos,useed,all⟩ div)
    refine ⟨⟨G,kind,F,H,mem,nh,nf,fac,?_,fun i=>power_caps nh (vcaps H mem) _,avoid,?_⟩⟩
    · intro i
      obtain ⟨n,e⟩ := fac i
      exact divisor_caps (proper i) (caps i) (dvd_trans (dvd_mul_left (F i) (G^n)) (dvd_of_eq e.symm))
    · intro i J prime regular r a fit hp hc
      obtain ⟨n,e⟩ := fac i
      rw [e] at hp
      have unit : toJet (G^n)∉J := by
        rw [map_pow]
        exact fun bad => regular (prime.mem_of_pow_mem _ bad)
      exact ⟨native_strip prime r unit hp,native_power (hc H mem) fit⟩
  by_cases ex : ∃ G,Common V G
  · obtain ⟨G,g⟩ := ex
    choose F eq avoid using fun i => (FiniteMultiplicity.of_prime_left g.1.prime (proper i)).exists_eq_pow_mul_and_not_dvd
    apply select G (Or.inr g) F (fun i=>⟨_,eq i⟩)
    intro i Q q div
    by_cases same : G∣Q
    · exact avoid i (same.trans div)
    · exact unique G Q g q (g.1.isRelPrime_iff_not_dvd.mpr same)
  · apply select 1 (Or.inl rfl) P (fun i=>⟨0,by simp⟩)
    exact fun _ Q q _ => ex ⟨Q,q⟩

#print axioms contact_of_crt
#print axioms prepare
end Lower6960.PrefixRows
