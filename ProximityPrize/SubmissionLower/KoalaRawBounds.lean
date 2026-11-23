import ProximityPrize.SubmissionLower.KoalaBoxDegree
import ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
import ArkLib.ToMathlib.MvPolynomial.PDeriv

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.Raw
noncomputable section
open MvPolynomial
open K1_14 (FX Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten partialX separant tangent cleared)
open HighCore82258Upper
open SplitCut.BoxDegree
open private HighCore82258Upper_3_1.seedBiform_box HighCore82258Upper_3_1.liftTaylor_box
  HighCore82258Upper_3_3.residue_degree from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry

theorem fit {f : Biform} {a b c : ℕ} : f ∈ space FX a b c ↔
    f.degreeOf none≤a ∧ f.degreeOf (some 0)≤b ∧ f.degreeOf (some 1)≤ c:=by
  simp only [degreeOf_le_iff]
  constructor
  · exact fun h => ⟨fun m hm => (h hm).1,fun m hm => (h hm).2.1,fun m hm => (h hm).2.2⟩
  · rintro ⟨h,j,k⟩ _ hm
    exact ⟨h _ hm,j _ hm,k _ hm⟩

theorem grow {a b c x y z : ℕ} (ha : a≤x) (hb : b≤y) (hc : c≤z) :
    space FX a b c≤ space FX x y z :=
  restrictSupport_mono FX (fun _ h => ⟨h.1.trans ha,h.2.1.trans hb,h.2.2.trans hc⟩)

theorem root {f : Equation} {e v w : ℕ} (he : f.natDegree≤e)
    (hvw : ∀ i,(f.coeff i).degreeOf 0≤v ∧ (f.coeff i).degreeOf 1≤w) :
    flatten f ∈ space FX e v w:=by
  intro m hm
  change m ∈ (flatten f).support at hm
  have hc : m.some ∈ (f.coeff (m none)).support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    have h:=optionEquivLeft_coeff_coeff FX (flatten f) (m none) m.some
    simp only [AlgEquiv.apply_symm_apply,Finsupp.optionElim_some] at h
    exact h.trans_ne hm
  have hne:f.coeff (m none)≠0:=by intro h; simp [h] at hc
  exact ⟨(Polynomial.le_natDegree_of_ne_zero hne).trans he,
    (monomial_le_degreeOf 0 hc).trans (hvw _).1,(monomial_le_degreeOf 1 hc).trans (hvw _).2⟩

theorem dx {P : Biform} {a b c : ℕ} (h : P ∈ space FX a b c) :
    partialX P ∈ space FX a b c:=by
  intro m hm
  apply h
  contrapose! hm
  change m ∉ P.support at hm
  change m ∉ (partialX P).support
  rw [notMem_support_iff] at hm ⊢
  rw [K1_14_6_1.coeff_partialX,hm,map_zero]

theorem sep {P : Biform} {a b c : ℕ} (h : P ∈ space FX a b c) :
    separant P ∈ space FX (a-1) b c:=by
  rw [fit] at h ⊢
  exact ⟨(degreeOf_pderiv_le_sub_one _ _).trans (Nat.sub_le_sub_right h.1 _),
    (degreeOf_pderiv_le _ _ _).trans h.2.1,(degreeOf_pderiv_le _ _ _).trans h.2.2⟩

theorem tan {f P : Biform} {e b c g u v : ℕ} (he : 0<e)
    (hf:f ∈ space FX e b c) (h:P ∈ space FX g u v) :
    tangent f P ∈ space FX (g+(e-1)) (u+b) (v+c):=by
  apply (space FX _ _ _).sub_mem
  · simpa only [Nat.add_comm] using mul_box (sep hf) (dx h)
  · by_cases hg : g=0
    · rw [pderiv_eq_zero_of_degreeOf_eq_zero (Nat.eq_zero_of_le_zero (hg ▸ (fit.mp h).1)),
        mul_zero]
      exact (space FX _ _ _).zero_mem
    · have hh := mul_box (dx hf) (sep h)
      rwa [show e+(g-1)=g+(e-1) by omega,Nat.add_comm b u,Nat.add_comm c v] at hh

theorem clear {f : Biform} {e b c : ℕ} (he : 0<e) (hf : f ∈ space FX e b c) (n : ℕ) :
    cleared f n ∈ space FX (1+(2*n+1)*(e-1)) ((2*n+1)*b) ((2*n+1)*c):=by
  induction n with
  | zero =>
    simpa only [cleared,Nat.mul_zero,Nat.zero_add,Nat.one_mul,show 1+(e-1)=e by omega]
      using (space FX _ _ _).neg_mem (dx hf)
  | succ n ih =>
    have h₁:=mul_box (sep hf) (tan he hf ih)
    have h₂:=mul_box (tan he hf (sep hf)) ih
    have h₂' := (space FX _ _ _).smul_mem (((2*n+1:ℕ):FX)) h₂
    rw [cleared]
    apply (space FX _ _ _).sub_mem
    · convert h₁ using 2 <;> ring
    · rw [mul_assoc,← MvPolynomial.smul_eq_C_mul]
      convert h₂' using 2 <;> ring

theorem box_pow {P : Biform} {a b c : ℕ} (h : P ∈ space FX a b c) (n : ℕ) :
    P^n ∈ space FX (n*a) (n*b) (n*c):=by
  induction n with
  | zero => simp [fit]
  | succ n ih => simpa only [pow_succ,Nat.succ_mul] using mul_box ih h

theorem of_seed_box {a c : ℕ} {f : Biform} (h : f ∈ K1_14_6_1.box a c) :
    f ∈ space FX a c c:=by
  intro m hm
  have h' := mem_restrictBidegree.mp h m hm
  exact ⟨h'.1,(Finsupp.le_degree 0 m.some).trans h'.2,(Finsupp.le_degree 1 m.some).trans h'.2⟩

theorem ord {f : Equation} {e b c : ℕ} (he : 0<e)
    (hf:flatten f ∈ space FX e b c) {r i:ℕ} (hi:i≤r) :
    ordinateTaylorNum f r i ∈ space FX (1+(2*r-1)*(e-1)) ((2*r-1)*b) ((2*r-1)*c):=by
  cases i with
  | zero =>
    have hY:(MvPolynomial.X (none:Idx):Biform) ∈ space FX 1 0 0:=by simp [fit,MvPolynomial.degreeOf_X]
    simpa only [ordinateTaylorNum, Nat.add_comm _ 1, Nat.add_zero] using
      mul_box (box_pow (sep hf) (2*r-1)) hY
  | succ i =>
    have ht:2*i+1≤2*r-1:=by omega
    have hh:=mul_box (box_pow (sep hf) ((2*r-1)-(2*i+1))) (clear he hf i)
    rw [ordinateTaylorNum, ← MvPolynomial.smul_eq_C_mul]
    apply (space FX _ _ _).smul_mem
    have ha (x : ℕ) : ((2*r-1)-(2*i+1))*x+(2*i+1)*x=(2*r-1)*x := by
      rw [← Nat.add_mul,Nat.sub_add_cancel ht]
    convert hh using 2 <;> first | (rw [← ha (e-1)]; ring) | exact (ha _).symm

theorem num {J : Input} (B : ResidueLift J) {v w : ℕ}
    (hf:flatten J.f ∈ space FX J.e v w) (r:ℕ) :
    quotientNumerator J B r ∈
      space FX (1+(2*r-1)*(J.e-1)) ((2*r-1)*v+2*J.w) ((2*r-1)*w+2*J.w):=by
  unfold quotientNumerator
  apply Submodule.sum_mem
  intro i hi
  rw [← MvPolynomial.smul_eq_C_mul]
  apply (space FX _ _ _).smul_mem
  apply (space FX _ _ _).sub_mem
  · have ho := ord (Nat.lt_of_lt_of_le (by decide : 0<3) J.sheets) hf
      (show i≤r by have:=Finset.mem_range.mp hi; omega)
    simpa only [Nat.zero_add,Nat.add_comm (2*J.w)] using
      mul_box (of_seed_box (HighCore82258Upper_3_1.seedBiform_box B.denominator_degree)) ho
  · have hh := mul_box (box_pow (sep hf) (2*r-1)) (of_seed_box (HighCore82258Upper_3_1.liftTaylor_box J B i))
    exact grow (show (2*r-1)*(J.e-1)≤1+(2*r-1)*(J.e-1) by omega) le_rfl le_rfl (by simpa only [Nat.add_zero] using hh)

theorem den {J : Input} (B : ResidueLift J) {v w : ℕ}
    (hf:flatten J.f ∈ space FX J.e v w) (r:ℕ) :
    quotientDenominator J B r ∈
      space FX ((2*r-1)*(J.e-1)) ((2*r-1)*v+2*J.w) ((2*r-1)*w+2*J.w):=by
  simpa only [quotientDenominator,Nat.zero_add,Nat.add_comm (2*J.w)] using
    mul_box (of_seed_box (HighCore82258Upper_3_1.seedBiform_box B.denominator_degree)) (box_pow (sep hf) (2*r-1))

theorem residue {J : Input} (B : ResidueLift J) {v w : ℕ}
    (hf:flatten J.f ∈ space FX J.e v w) (r:ℕ) (x:P1.I) :
    seedBiform (HighCore82258Upper_3_3.residueAtNode B x)*separant (flatten J.f)^(2*r-1) ∈
      space FX ((2*r-1)*(J.e-1)) ((2*r-1)*v+2*J.w) ((2*r-1)*w+2*J.w):=by
  simpa only [Nat.zero_add,Nat.add_comm (2*J.w)] using
    mul_box (of_seed_box (HighCore82258Upper_3_1.seedBiform_box (HighCore82258Upper_3_3.residue_degree B x))) (box_pow (sep hf) (2*r-1))

theorem padded_num {J : Input} (B : ResidueLift J) {v w r j : ℕ}
    (hf:flatten J.f ∈ space FX J.e v w) (hj:j≤r) :
    separant (flatten J.f)^((2*r-1)-(2*j-1))*quotientNumerator J B j ∈
      space FX (1+(2*r-1)*(J.e-1)) ((2*r-1)*v+2*J.w) ((2*r-1)*w+2*J.w):=by
  have hle:2*j-1≤2*r-1:=by omega
  have hh:=mul_box (box_pow (sep hf) ((2*r-1)-(2*j-1))) (num B hf j)
  have hsum (x : ℕ) : ((2*r-1)-(2*j-1))*x+(2*j-1)*x = (2*r-1)*x := by
    rw [← Nat.add_mul,Nat.sub_add_cancel hle]
  convert hh using 2
  · rw [← hsum (J.e-1)]; ring
  · rw [← hsum v]; ring
  · rw [← hsum w]; ring

end
end SplitCut.Raw
#print axioms SplitCut.Raw.root
#print axioms SplitCut.Raw.num
#print axioms SplitCut.Raw.padded_num
