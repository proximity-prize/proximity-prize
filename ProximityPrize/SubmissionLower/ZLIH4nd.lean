import ProximityPrize.SubmissionLower.AS
set_option Elab.async false
set_option autoImplicit true
namespace qK9H6va
open aR fP MvPolynomial
open scoped BigOperators
noncomputable section
open private UD cCH cGq aNJ c07 cFA from ProximityPrize.SubmissionLower.AS
private theorem ahA {n:ℕ} (hn:n≤56) :
    (n.factorial:ao)≠0:= by
  have :CharP ao 2130706433 :=
    charP_of_injective_algebraMap
      (R:=K1.K) (A:=ao) (algebraMap K1.K ao).injective 2130706433
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [Nat.factorial_succ,Nat.cast_mul]
    refine mul_ne_zero ?_ (ih (by omega))
    intro h
    have hd:=(CharP.cast_eq_zero_iff ao 2130706433 (n+1)).mp h
    have :=Nat.le_of_dvd (Nat.succ_pos n) hd
    omega
private theorem bpX (d:Fin 4 →₀ ℕ) (h:d.degree≤56) :
    aNJ d≠0 :=
  Finset.prod_ne_zero_iff.mpr fun j _=>ahA ((Finsupp.le_degree j d).trans h)
private theorem rescale (m e d:Fin 4 →₀ ℕ) (h:d+UD m=e)
    (hd:d.degree=m 0) (hm:m.degree≤56) (he :e.degree≤56) :
    (d.multinomial:ao)*(-1 :ao)^d 2 =
      avQ e*avP m *
        ((e 1).choose (m 1) :ao)*((e 2).choose (m 2) :ao) *
          ((e 3).choose (m 3) :ao) := by
  have coord (j:Fin 4) :d j+UD m j=e j :=
    congrArg (fun u:Fin 4 →₀ ℕ=>u j) h
  have h0:d 0=e 0:= by simpa using coord 0
  have h1 :d 1+m 1=e 1 := by simpa using coord 1
  have h2 :d 2+m 2=e 2 := by simpa using coord 2
  have h3:d 3+m 3=e 3:= by simpa using coord 3
  have fact {x y z :ℕ} (hx :z+y=x) :
      (x.factorial:ao)=(x.choose y :ao)*(y.factorial:ao) *
        (z.factorial:ao) := by
    have hc:=cFA (n:=x) (k :=y) (by omega)
    rw [show x - y=z by omega] at hc
    exact hc.symm
  have hsign: (-1 :ao)^e 2*(-1 :ao)^m 2=(-1 :ao)^d 2 := by
    rw [← pow_add,← h2,add_assoc,← two_mul,pow_add,pow_mul,neg_one_sq,one_pow,mul_one]
  have hmulti:=c07 d
  rw [hd] at hmulti
  change _=(-1 :ao)^e 2/aNJ e *
    ((-1 :ao)^m 2*aNJ m)*_ *_ *_
  simp only [div_mul_eq_mul_div₀]
  apply (eq_div_iff (bpX e he)).mpr
  have hsmall:d.degree≤56:= by
    rw [hd]
    exact (Finsupp.le_degree 0 m).trans hm
  apply mul_right_cancel₀ (bpX d hsmall)
  calc
    _=(-1 :ao)^d 2 *
        ((d.multinomial:ao)*aNJ d)*aNJ e := by ac_rfl
    _=(-1 :ao)^d 2*((m 0).factorial:ao)*aNJ e := by rw [hmulti]
    _ = _:= by
      rw [← hsign]
      simp only [aNJ,Fin.prod_univ_four]
      conv_lhs=>rw [← h0,fact h1,fact h2,fact h3]
      ac_rfl
theorem c3K (m e :Fin 4 →₀ ℕ) (hdegree :m.degree=e.degree) (hm:m.degree≤56) :
    (Jx (monomial m 1)).coeff e =
      avQ e*avP m *
        ((e 1).choose (m 1) :ao)*((e 2).choose (m 2) :ao) *
          ((e 3).choose (m 3) :ao) := by
  classical
  rw [cCH,coeff_mul_monomial']
  by_cases h:UD m≤e
  · rw [ite_eq_left h,mul_one]
    let d:=e-UD m
    have hsum:d+UD m=e :=tsub_add_cancel_of_le h
    have hd:d.degree=m 0:= by
      have ha :d.degree+(UD m).degree=e.degree := by rw [← map_add,hsum]
      rw [← hdegree,cF m,cF (UD m)] at ha
      simp at ha
      omega
    rw [cGq d _ hd]
    exact rescale m e d hsum hd hm (hdegree ▸ hm)
  · rw [ite_eq_right h]
    have hb:e 1< m 1∨e 2< m 2∨e 3< m 3:= by
      by_contra! hn
      apply h
      intro j
      fin_cases j
      · simp
      · simpa using hn.1
      · simpa using hn.2.1
      · simpa using hn.2.2
    rcases hb with h1 | h2 | h3
    · simp [Nat.choose_eq_zero_of_lt h1]
    · simp [Nat.choose_eq_zero_of_lt h2]
    · simp [Nat.choose_eq_zero_of_lt h3]
end
end qK9H6va
