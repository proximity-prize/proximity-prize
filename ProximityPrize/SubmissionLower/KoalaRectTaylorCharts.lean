import ProximityPrize.SubmissionLower.KoalaRectTaylorAxes
import ProximityPrize.SubmissionLower.KoalaRectSectionAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace KoalaRectTaylor
noncomputable section

open K1_14 (FX)
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3 (JetRing ordinate graphIdeal)
open HighCore82258Upper_3_1 (velocity)
open HighCore82258Upper_3_1_2 (finite reciprocal inverseEval seedMap mul_reciprocal clear_overlap)
open private HighCore82258Upper_3_1_2.eval_coefficient HighCore82258Upper_3_1_2.scale_velocity
  from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
open HighCore82258Upper_3_1_2 (eval_coefficient scale_velocity)
open SplitCut.Rect (Box Section space)
open scoped BigOperators

def rectIdeal (Q : Ideal JetRing) : Ideal (SplitCut.Rect.Ring FX) :=
  Q.comap jetToRect.symm.toRingHom

@[simp] theorem jetToRect_mem_rectIdeal {Q : Ideal JetRing} {p : JetRing} :
    jetToRect p ∈ rectIdeal Q ↔ p ∈ Q := by
  change jetToRect.symm (jetToRect p) ∈ Q ↔ _
  rw [AlgEquiv.symm_apply_apply]

theorem rectIdeal_mono {Q P : Ideal JetRing} (h : Q ≤ P) : rectIdeal Q ≤ rectIdeal P :=
  Ideal.comap_mono h

def Represented (Q : Ideal JetRing) (d : Box) (p : JetRing) : Prop :=
  ∃ S : Section (rectIdeal Q) d, S.finite = jetToRect p

theorem jetToRect_mem_box {p : JetRing} {d : Box} (hv : p.natDegree ≤ d.velocity)
    (hy : ∀ j ∈ p.support, (p.coeff j).natDegree + 2*j ≤ d.base+2*d.velocity)
    (h₀ : JetAxis 0 p d.seed₀) (h₁ : JetAxis 1 p d.seed₁) :
    jetToRect p ∈ space FX d := by
  intro m hm
  change m ∈ (jetToRect p).support at hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [coeff_jetToRect] at hc
  have hC : (p.coeff (m 1)).coeff (m 0) ≠ 0 := by
    intro h
    simp [h] at hc
  have hP : p.coeff (m 1) ≠ 0 := by
    intro h
    simp [h] at hC
  have hS := Polynomial.mem_support_iff.mpr hP
  have hV := (Polynomial.le_natDegree_of_mem_supp _ hS).trans hv
  have hY := Polynomial.le_natDegree_of_ne_zero hC
  have hseed := MvPolynomial.mem_support_iff.mpr hc
  refine ⟨hV, (Nat.add_le_add_right hY _).trans (hy _ hS), ?_, ?_⟩
  · exact MvPolynomial.degreeOf_le_iff.mp (h₀ (m 1) (m 0)) _ hseed
  · exact MvPolynomial.degreeOf_le_iff.mp (h₁ (m 1) (m 0)) _ hseed

def ordinateWidth (p : JetRing) : ℕ :=
  p.support.sup fun j => (p.coeff j).natDegree

theorem jetToRect_mem_pad {p : JetRing} {d : Box} {n : ℕ}
    (hn : ordinateWidth p ≤ n) (hv : p.natDegree ≤ d.velocity)
    (h₀ : JetAxis 0 p d.seed₀) (h₁ : JetAxis 1 p d.seed₁) :
    jetToRect p ∈ space FX (d.pad n) := by
  apply jetToRect_mem_box (d := d.pad n) hv _ h₀ h₁
  intro j hj
  have h₁ := (Finset.le_sup (f := fun k => (p.coeff k).natDegree) hj).trans hn
  have h₂ := (Polynomial.le_natDegree_of_mem_supp _ hj).trans hv
  dsimp [Box.pad]
  omega

theorem represented_of_mem {Q : Ideal JetRing} {d : Box} {p : JetRing}
    (hp : jetToRect p ∈ space FX d) : Represented Q d p :=
  ⟨Section.of_mem hp,rfl⟩

theorem represented_of_charts {Q : Ideal JetRing} {d : Box} {p q : JetRing} {n : ℕ}
    (hp : jetToRect p ∈ space FX (d.pad n)) (hq : jetToRect q ∈ space FX (d.pad n))
    (hglue : ordinate^n*p-q ∈ Q) : Represented Q d p := by
  refine ⟨⟨n, jetToRect p, jetToRect q, hp, hq, ?_⟩, rfl⟩
  have h := jetToRect_mem_rectIdeal.mpr hglue
  simpa only [map_sub, map_mul, map_pow, jetToRect_ordinate] using h

namespace Represented

variable {Q : Ideal JetRing} {d k : Box} {p q : JetRing}

theorem restrict {P : Ideal JetRing} (hp : Represented Q d p) (hle : Q ≤ P) :
    Represented P d p := by
  obtain ⟨S,hS⟩ := hp
  exact ⟨S.restrict (rectIdeal_mono hle),hS⟩

theorem widen (hp : Represented Q d p)
    (hv : d.velocity ≤ k.velocity) (hy : d.base+2*d.velocity ≤ k.base+2*k.velocity)
    (h₀ : d.seed₀ ≤ k.seed₀) (h₁ : d.seed₁ ≤ k.seed₁) : Represented Q k p := by
  obtain ⟨S,hS⟩ := hp
  exact ⟨S.widen hv hy h₀ h₁,hS⟩

theorem mul (hp : Represented Q d p) (hq : Represented Q k q) :
    Represented Q (d.add k) (p*q) := by
  obtain ⟨S,hS⟩ := hp
  obtain ⟨T,hT⟩ := hq
  exact ⟨S.mul T, by change S.finite*T.finite = _; rw [hS,hT,map_mul]⟩

theorem add (hp : Represented Q d p) (hq : Represented Q d q) : Represented Q d (p+q) := by
  obtain ⟨S,hS⟩ := hp
  obtain ⟨T,hT⟩ := hq
  exact ⟨S.add T, by change S.finite+T.finite = _; rw [hS,hT,map_add]⟩

theorem smul (hp : Represented Q d p) (c : FX) : Represented Q d (c • p) := by
  obtain ⟨S,hS⟩ := hp
  refine ⟨S.smul c,?_⟩
  change c • S.finite = _
  rw [hS]
  simp only [Algebra.smul_def,map_mul,AlgEquiv.commutes]

theorem sub (hp : Represented Q d p) (hq : Represented Q d q) : Represented Q d (p-q) := by
  simpa [sub_eq_add_neg] using hp.add (hq.smul (-1))

theorem zero : Represented Q d 0 :=
  represented_of_mem (by rw [map_zero]; exact (space FX d).zero_mem)

theorem sum {ι : Type*} (s : Finset ι) (f : ι → JetRing)
    (h : ∀ i ∈ s, Represented Q d (f i)) : Represented Q d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : Represented Q d 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem pow (hp : Represented Q d p) (n : ℕ) :
    Represented Q ⟨n*d.base,n*d.velocity,n*d.seed₀,n*d.seed₁⟩ (p^n) := by
  induction n with
  | zero =>
    apply represented_of_mem
    simpa only [pow_zero,map_one,MvPolynomial.C_1,Nat.zero_mul] using
      SplitCut.Rect.space_C (1 : FX) (⟨0,0,0,0⟩ : Box)
  | succ n ih =>
    rw [pow_succ]
    simpa [Box.add,Nat.succ_mul] using ih.mul hp

end Represented

private def reflected (p : JetRing) (a n : ℕ) : JetRing :=
  ∑ j ∈ p.support, Polynomial.monomial j
    (Polynomial.C (MvPolynomial.C ((-1 : FX)^j)) * (p.coeff j).reflect (a+n-2*j))

private theorem reflected_coeff_in (p : JetRing) (a n j : ℕ) (hj : j ∈ p.support) :
    (reflected p a n).coeff j =
      Polynomial.C (MvPolynomial.C ((-1 : FX)^j)) * (p.coeff j).reflect (a+n-2*j) := by
  classical
  rw [reflected,Polynomial.finsetSum_coeff,Finset.sum_eq_single_of_mem j hj]
  · rw [Polynomial.coeff_monomial_same]
  · intro i _ hi
    exact Polynomial.coeff_monomial_of_ne _ hi.symm

private theorem reflected_coeff_out (p : JetRing) (a n j : ℕ) (hj : j ∉ p.support) :
    (reflected p a n).coeff j = 0 := by
  classical
  rw [reflected,Polynomial.finsetSum_coeff]
  exact Finset.sum_eq_zero fun i hi => Polynomial.coeff_monomial_of_ne _ (fun e => hj (e ▸ hi))

private theorem reflected_bound {p : JetRing} {d : Box} {n : ℕ}
    (hn : 2*d.velocity+ordinateWidth p ≤ n) (hv : p.natDegree ≤ d.velocity)
    (h₀ : JetAxis 0 p d.seed₀) (h₁ : JetAxis 1 p d.seed₁) :
    jetToRect (reflected p (d.base+2*d.velocity) n) ∈ space FX (d.pad n) := by
  let a := d.base+2*d.velocity
  have hsupport (j : ℕ) (hj : j ∈ (reflected p a n).support) : j ∈ p.support := by
    by_contra h
    exact (Polynomial.mem_support_iff.mp hj) (reflected_coeff_out p a n j h)
  have haxes (z : Fin 2) (s : ℕ) (hs : JetAxis z p s) :
      JetAxis z (reflected p a n) s := by
    intro j
    by_cases hj : j ∈ p.support
    · rw [reflected_coeff_in p a n j hj]
      simpa only [Nat.zero_add] using (EquationAxis.scalar ((-1 : FX)^j)).mul
        ((hs j).reflect (a+n-2*j))
    · rw [reflected_coeff_out p a n j hj]
      exact EquationAxis.zero
  apply jetToRect_mem_box (d := d.pad n) _ _ (haxes _ _ h₀) (haxes _ _ h₁)
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    exact fun j hj => reflected_coeff_out p a n j
      (fun he => (not_lt_of_ge ((Polynomial.le_natDegree_of_mem_supp _ he).trans hv)) hj)
  · intro j hj
    have hpj := hsupport j hj
    have hvel := (Polynomial.le_natDegree_of_mem_supp _ hpj).trans hv
    have hw : (p.coeff j).natDegree ≤ ordinateWidth p :=
      Finset.le_sup (f := fun k => (p.coeff k).natDegree) hpj
    have hh : (p.coeff j).natDegree ≤ a+n-2*j := by dsimp [a]; omega
    rw [reflected_coeff_in p a n j hpj]
    have h := Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_C (MvPolynomial.C ((-1 : FX)^j))).le
      (Polynomial.natDegree_reflect_le.trans (max_le le_rfl hh))
    dsimp [Box.pad,a] at *
    omega

private theorem reflected_eval {R : Type} [CommRing R] (φ : JetRing →+* R)
    (z : R) (hz : φ ordinate*z = 1) {p : JetRing} {a b n : ℕ}
    (hv : p.natDegree ≤ b) (hn : 2*b+ordinateWidth p ≤ n) :
    φ (reflected p a n) = (φ ordinate)^(a+n) * inverseEval φ z p := by
  classical
  let y := φ ordinate
  let : Invertible y := ⟨z, by rw [mul_comm]; exact hz, hz⟩
  rw [reflected,map_sum]
  conv_rhs => rw [← p.sum_monomial_eq, Polynomial.sum_def, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hb := (Polynomial.le_natDegree_of_mem_supp _ hj).trans hv
  have hcap : (p.coeff j).natDegree ≤ ordinateWidth p :=
    Finset.le_sup (f := fun k => (p.coeff k).natDegree) hj
  have hN : (p.coeff j).natDegree ≤ a+n-2*j := by omega
  conv_lhs => rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul,map_pow,eval_coefficient,map_neg,map_one]
  change ((-1)^j * ((p.coeff j).reflect (a+n-2*j)).eval₂ (seedMap φ) y) *
    (φ velocity)^j = _
  rw [mul_comm, show inverseEval φ z (Polynomial.monomial j (p.coeff j)) =
      (p.coeff j).eval₂ (seedMap φ) z * (-(φ velocity*z^2))^j by
        simp [inverseEval,Polynomial.eval₂_monomial,Polynomial.coe_eval₂RingHom]]
  rw [scale_velocity y z (φ velocity) _ hz (by omega : 2*j ≤ a+n)]
  have hrev : ((p.coeff j).reflect (a+n-2*j)).natDegree ≤ a+n-2*j :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl hN)
  have h := Polynomial.eval₂_reflect_mul_pow (seedMap φ) y (a+n-2*j)
    ((p.coeff j).reflect (a+n-2*j)) hrev
  simp only [Polynomial.reflect_reflect] at h
  rw [show ⅟y = z from rfl] at h
  rw [h]

private theorem transition_zero {R : Type} [CommRing R] (φ : JetRing →+* R)
    {p q : JetRing} {u : R} {a n : ℕ}
    (hq : φ q = (φ ordinate)^(a+n)*u) (hp : φ p = (φ ordinate)^a*u) :
    φ (ordinate^n*p-q) = 0 := by
  rw [map_sub,map_mul,map_pow,hp,hq,← mul_assoc,← pow_add,Nat.add_comm n a,sub_self]

theorem represented_of_transition (J : Input) (B : ResidueLift J) (D : Factors J B)
    {p inverse : JetRing} {d : Box}
    (hp : p.natDegree ≤ d.velocity) (hi : inverse.natDegree ≤ d.velocity)
    (hp₀ : JetAxis 0 p d.seed₀) (hp₁ : JetAxis 1 p d.seed₁)
    (hi₀ : JetAxis 0 inverse d.seed₀) (hi₁ : JetAxis 1 inverse d.seed₁)
    (h : finite J B D p = (finite J B D ordinate)^(d.base+2*d.velocity) *
      inverseEval (finite J B D) (reciprocal J B D) inverse) :
    Represented (graphIdeal J B D) d p := by
  let n := max (ordinateWidth p) (2*d.velocity+ordinateWidth inverse)
  let q := reflected inverse (d.base+2*d.velocity) n
  have e := reflected_eval (finite J B D) (reciprocal J B D) (mul_reciprocal J B D)
    (a := d.base+2*d.velocity) (n := n) hi (le_max_right _ _ : _ ≤ n)
  have hz : finite J B D (ordinate^n*p-q) = 0 :=
    transition_zero (finite J B D) e h
  obtain ⟨m,hm⟩ := clear_overlap J B D hz
  refine represented_of_charts (d := d) (p := p) (q := ordinate^m*q) (n := n+m)
    (jetToRect_mem_pad (d := d) ((le_max_left _ _).trans (Nat.le_add_right _ _)) hp hp₀ hp₁) ?_ ?_
  · have hq := reflected_bound (d := d) (le_max_right _ _ : _ ≤ n) hi hi₀ hi₁
    simpa only [map_mul,map_pow,jetToRect_ordinate] using SplitCut.Rect.space_shift_ordinate hq m
  · rwa [mul_sub, ← mul_assoc, ← pow_add, Nat.add_comm m n] at hm

end
end KoalaRectTaylor

#print axioms KoalaRectTaylor.represented_of_transition
