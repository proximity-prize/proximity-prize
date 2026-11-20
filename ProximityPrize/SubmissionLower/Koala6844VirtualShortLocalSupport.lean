import ProximityPrize.SubmissionLower.Koala6844VirtualShortSeedlessRank
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Action.Pointwise.Set
import Mathlib.Tactic.Ring


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open SecondJetBasis SecondJetSupport SecondJetLocal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2600000

variable {K : Type*} [Field K]

structure LocalCaps where
  alphaMinusT : ℤ
  slopeWeight : ℕ
  jet : ℕ
  middle : ℕ
  total : ℕ
  seed : ℕ

def LocalCaps.plus (u v : LocalCaps) : LocalCaps :=
  ⟨u.alphaMinusT+v.alphaMinusT, u.slopeWeight+v.slopeWeight, u.jet+v.jet,
    u.middle+v.middle, u.total+v.total, u.seed+v.seed⟩

def LocalCaps.times (k : ℕ) (u : LocalCaps) : LocalCaps :=
  ⟨(k : ℤ)*u.alphaMinusT, k*u.slopeWeight, k*u.jet, k*u.middle, k*u.total, k*u.seed⟩

def FitsLocal (u : LocalCaps) (P : Poly (K := K)) : Prop :=
  ∀ e ∈ P.support, (e 2 : ℤ)-(e 0 : ℤ) ≤ u.alphaMinusT ∧
    2*e 1+e 3 ≤ u.slopeWeight ∧ e 1 ≤ u.jet ∧ e 1+e 2+e 3 ≤ u.middle ∧
      e 1+e 2+e 3+e 4 ≤ u.total ∧ e 4 ≤ u.seed

theorem FitsLocal.mul {u v : LocalCaps} {P Q : Poly (K := K)}
    (hp : FitsLocal u P) (hq : FitsLocal v Q) : FitsLocal (u.plus v) (P*Q) := by
  intro e he
  obtain ⟨d,hd,f,hf,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  obtain ⟨ht,hB,hs,hU,hL,hZ⟩ := hp d hd
  obtain ⟨ht',hB',hs',hU',hL',hZ'⟩ := hq f hf
  simp only [LocalCaps.plus, Finsupp.add_apply, Nat.cast_add]
  exact ⟨by omega, by omega,by omega,by omega,by omega,by omega⟩

theorem FitsLocal.pow {u : LocalCaps} {P : Poly (K := K)}
    (hP : FitsLocal u P) (k : ℕ) : FitsLocal (LocalCaps.times k u) (P^k) := by
  induction k with
  | zero =>
    intro e he
    simp only [pow_zero, MvPolynomial.support_one, Finset.mem_singleton] at he
    subst e
    simp [LocalCaps.times]
  | succ k ih =>
    simpa only [pow_succ, LocalCaps.times, LocalCaps.plus, Nat.cast_succ, add_mul, one_mul,
      Nat.succ_mul] using ih.mul hP

def noSeedMonomial (t h a r : ℕ) (c : K) : Poly (K := K) :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm ![t,h,a,r,0]) c

theorem fits_noSeedMonomial (t h a r : ℕ) (c : K) :
    FitsLocal ⟨(a : ℤ)-(t : ℤ), 2*h+r, h, h+a+r, h+a+r, 0⟩ (noSeedMonomial t h a r c) := by
  intro e he
  have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
  subst e
  simp

theorem truncate_mem_ordinary_local (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hcap : ∀ h ≤ s, U ≤ caps h) (P : Poly (K := K))
    (hP : FitsLocal ⟨0,B,s,U,L,L⟩ P) :
    truncateOuter (K := K) m (flatEquiv (K := K) P) ∈
      SecondJetRelaxedSpace.source (K := K) m L B s U caps := by
  rw [← flatEquiv_truncFlat, SecondJetRelaxedSpace.mem_source_iff, AlgEquiv.symm_apply_apply]
  intro d hd
  have ht := support_truncFlat m P d hd
  obtain ⟨ha,hB,hs,hU,hL,_⟩ := hP d ht.2
  dsimp only at ha hB hs hU hL
  exact ⟨⟨ht.1,by omega,by omega,hs,hL⟩,hB,hU,hU.trans (hcap _ hs)⟩

theorem ordinary_local_term_mem (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hcap : ∀ h ≤ s, U ≤ caps h) (t h a r j i d : ℕ) (c : K)
    (C A D : Poly (K := K))
    (hC : FitsLocal ⟨1,0,0,1,1,0⟩ C) (hA : FitsLocal ⟨0,0,0,0,1,1⟩ A)
    (hD : FitsLocal ⟨0,0,0,0,0,0⟩ D)
    (hat : a ≤ t) (hB : 2*h+r ≤ B) (hs : h ≤ s)
    (hU : h+a+r+j ≤ U) (hL : h+a+r+d ≤ L) (hij : j ≤ i) (hid : i ≤ d) :
    truncateOuter (K := K) m (flatEquiv (K := K)
      (noSeedMonomial (t+j) h a r c * C^j * A^(i-j) * D)) ∈
        SecondJetRelaxedSpace.source (K := K) m L B s U caps := by
  apply truncate_mem_ordinary_local m L B s U caps hcap
  intro e he
  have hh := (((fits_noSeedMonomial (t+j) h a r c).mul (hC.pow j)).mul
    (hA.pow (i-j))).mul hD e he
  simp only [LocalCaps.plus, LocalCaps.times, mul_one, mul_zero, add_zero,
    Nat.cast_add] at hh
  dsimp only
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

theorem pole_local_term_mem (m B s U : ℕ) (t h a r j i : ℕ) (c : K)
    (C D : Poly (K := K))
    (hC : FitsLocal ⟨1,0,0,1,1,0⟩ C) (hD : FitsLocal ⟨0,0,0,0,0,0⟩ D)
    (hat : a ≤ t) (hB : 2*h+r ≤ B) (hs : h ≤ s)
    (hU : h+a+r+j ≤ U) (hij : i < j) :
    truncateOuter (K := K) (m-(j-i)) (flatEquiv (K := K)
      (noSeedMonomial (t+i) h a r c * C^i * D)) ∈
        seedlessSource (K := K) (m-(j-i)) B s (U-(j-i)) := by
  let P := noSeedMonomial (t+i) h a r c * C^i * D
  have hP : FitsLocal ⟨0,B,s,U-(j-i),U-(j-i),0⟩ P := by
    intro e he
    have hh := ((fits_noSeedMonomial (t+i) h a r c).mul (hC.pow i)).mul hD e he
    simp only [LocalCaps.plus, LocalCaps.times, mul_one, mul_zero, add_zero, Nat.cast_add] at hh
    dsimp only
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
  rw [mem_seedlessSource]
  constructor
  · apply truncate_mem_ordinary_local (caps := fun _ => U-(j-i)) _ _ _ _ _
    · intros; rfl
    · intro e he
      obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hP e he
      dsimp only at h5 ⊢
      exact ⟨h0,h1,h2,h3,h4,by omega⟩
  · rw [← flatEquiv_truncFlat, AlgEquiv.symm_apply_apply]
    intro e he
    exact Nat.eq_zero_of_le_zero (hP e (support_truncFlat _ _ e he).2).2.2.2.2.2

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
