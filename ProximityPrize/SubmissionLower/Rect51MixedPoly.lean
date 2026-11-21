import ProximityPrize.SubmissionLower.UpperBranch8

/-! Leading-degree control from the public kaankolcu 69.50 note
f9161583-1b70-4048-8a65-bae6ee236fe4. -/
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Rect51MixedPoly
noncomputable section

open MvPolynomial
open scoped BigOperators
abbrev HilbertPoly := MvPolynomial (Fin 4) ℚ

def NonnegativeTop (p : HilbertPoly) : Prop :=
  ∀ m : Fin 4 →₀ ℕ, m.degree=p.totalDegree → 0≤p.coeff m

def difference (p : HilbertPoly) (a : Fin 4 → ℕ) : HilbertPoly :=
  p - MvPolynomial.bind₁ (fun i => MvPolynomial.X i-MvPolynomial.C (a i : ℚ)) p
private abbrev Exp := Fin 4 →₀ ℕ
def Top (n : ℕ) (p : HilbertPoly) : Prop :=
  p.totalDegree ≤ n ∧ ∀ m : Exp, m.degree = n → 0 ≤ p.coeff m
private theorem top_add {n : ℕ} {p q : HilbertPoly} (hp : Top n p) (hq : Top n q) :
    Top n (p + q) :=
  ⟨(totalDegree_add _ _).trans (max_le hp.1 hq.1),
    fun m hm => add_nonneg (hp.2 m hm) (hq.2 m hm)⟩
private theorem top_of_nonnegative {n : ℕ} {p : HilbertPoly}
    (hd : p.totalDegree ≤ n) (hp : NonnegativeTop p) : Top n p := by
  refine ⟨hd, fun m hm => ?_⟩
  rcases lt_or_eq_of_le hd with hlt | heq
  · rw [coeff_eq_zero_of_totalDegree_lt (show p.totalDegree < m.degree by omega)]
  · exact hp m (hm.trans heq.symm)
private theorem cut {n : ℕ} {p q : HilbertPoly} (hd : p.totalDegree ≤ n)
    (hq : NonnegativeTop q) (hgap : NonnegativeTop (p - q)) :
    q.totalDegree ≤ n ∧ Top n (p - q) := by
  have hqn : q.totalDegree ≤ n := by
    by_contra! h
    have hne : q ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨m, hm, hdeg⟩ := Finset.exists_mem_eq_sup q.support (support_nonempty.mpr hne)
      (fun m => m.degree)
    change q.totalDegree = m.degree at hdeg
    have hpzero := coeff_eq_zero_of_totalDegree_lt (f := p)
      (d := m) (show p.totalDegree < m.degree by omega)
    have hdiff : (p - q).totalDegree = q.totalDegree := by
      rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt, totalDegree_neg]
      simpa only [totalDegree_neg] using hd.trans_lt h
    have h1 := hq m hdeg.symm
    have h2 := hgap m (hdeg.symm.trans hdiff.symm)
    rw [coeff_sub, hpzero, zero_sub] at h2
    exact (mem_support_iff.mp hm) (le_antisymm (nonpos_of_neg_nonneg h2) h1)
  exact ⟨hqn, top_of_nonnegative ((totalDegree_sub _ _).trans (max_le hd hqn)) hgap⟩
private def diffAdd (shift : Fin 4 → ℕ) : HilbertPoly →+ HilbertPoly where
  toFun p := difference p shift
  map_zero' := by simp [difference]
  map_add' p q := by simp only [difference, map_add]; abel
private theorem diff_sub (p q : HilbertPoly) (shift : Fin 4 → ℕ) :
    difference (p - q) shift = difference p shift - difference q shift :=
  map_sub (diffAdd shift) p q
private theorem diff_mul_X (p : HilbertPoly) (shift : Fin 4 → ℕ) (i : Fin 4) :
    difference (p * MvPolynomial.X i) shift =
      difference p shift * MvPolynomial.X i + C (shift i : ℚ) * p -
        C (shift i : ℚ) * difference p shift := by
  simp only [difference, map_mul, bind₁_X_right]
  ring
private theorem degree_sub_single {m : Exp} {i : Fin 4} (hi : i ∈ m.support) :
    (m - Finsupp.single i 1).degree + 1 = m.degree := by
  simpa only [map_add, Finsupp.degree_single] using
    congrArg Finsupp.degree (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi))
private theorem diff_monomial (shift : Fin 4 → ℕ) (d : Exp) (r : ℚ) :
    ∀ n : ℕ, (monomial d r).totalDegree ≤ n →
      (∀ m : Exp, n ≤ m.degree → (difference (monomial d r) shift).coeff m = 0) ∧
      ((∀ m : Exp, 0 ≤ (monomial d r).coeff m) →
        ∀ m : Exp, n = m.degree + 1 → 0 ≤ (difference (monomial d r) shift).coeff m) := by
  refine MvPolynomial.induction_on_monomial (motive := fun p =>
    ∀ n : ℕ, p.totalDegree ≤ n →
      (∀ m : Exp, n ≤ m.degree → (difference p shift).coeff m = 0) ∧
      ((∀ m : Exp, 0 ≤ p.coeff m) →
        ∀ m : Exp, n = m.degree + 1 → 0 ≤ (difference p shift).coeff m)) ?_ ?_ d r
  · intro x n _
    simp [difference]
  · intro p i ih n hn
    by_cases hp : p = 0
    · subst p
      simp [difference]
    rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X] at hn
    obtain ⟨hzero, hpos⟩ := ih p.totalDegree le_rfl
    have hcoeff (m : Exp) :
        (difference (p * MvPolynomial.X i) shift).coeff m =
          (difference p shift * MvPolynomial.X i).coeff m + (shift i : ℚ) * p.coeff m -
            (shift i : ℚ) * (difference p shift).coeff m := by
      rw [diff_mul_X, coeff_sub]
      change (difference p shift * MvPolynomial.X i).coeff m +
        (C (shift i : ℚ) * p).coeff m -
        (C (shift i : ℚ) * difference p shift).coeff m = _
      simp only [coeff_C_mul]
    constructor
    · intro m hm
      rw [hcoeff, hzero m (by omega),
        coeff_eq_zero_of_totalDegree_lt (show p.totalDegree < m.degree by omega),
        mul_zero, add_zero, sub_zero, coeff_mul_X']
      split_ifs with hi
      · have hdeg := degree_sub_single hi
        exact hzero _ (by omega)
      · rfl
    · intro h m hm
      have hpcoeff (u : Exp) : 0 ≤ p.coeff u := by
        rw [← MvPolynomial.coeff_mul_X u i p]
        exact h _
      rw [hcoeff, hzero m (by omega), mul_zero, sub_zero]
      refine add_nonneg ?_ (mul_nonneg (Nat.cast_nonneg _) (hpcoeff m))
      rw [coeff_mul_X']
      split_ifs with hi
      · have hdeg := degree_sub_single hi
        rcases lt_or_eq_of_le (show p.totalDegree ≤ (m - Finsupp.single i 1).degree + 1 by
          omega) with hlt | heq
        · rw [hzero _ (by omega)]
        · exact hpos hpcoeff _ heq
      · exact le_rfl
private theorem diff_coeff_sum (p : HilbertPoly) (shift : Fin 4 → ℕ) (m : Exp) :
    (difference p shift).coeff m =
      ∑ d ∈ p.support, (difference (monomial d (p.coeff d)) shift).coeff m := by
  change ((diffAdd shift) p).coeff m = _
  conv_lhs => rw [p.as_sum, map_sum, coeff_sum]
  rfl
private theorem diff_le {n : ℕ} {p : HilbertPoly} (hp : p.totalDegree ≤ n + 1)
    (shift : Fin 4 → ℕ) : (difference p shift).totalDegree ≤ n := by
  rw [totalDegree]
  refine Finset.sup_le fun m hm => ?_
  change m.degree ≤ n
  by_contra! h
  apply mem_support_iff.mp hm
  rw [diff_coeff_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hdeg : d.degree ≤ n + 1 := (le_totalDegree hd).trans hp
  exact (diff_monomial shift d (p.coeff d) (n + 1) ((totalDegree_monomial_le _ _).trans hdeg)).1
    m (by omega)
private theorem diff_top {n : ℕ} {p : HilbertPoly} (hp : Top (n + 1) p)
    (shift : Fin 4 → ℕ) : Top n (difference p shift) := by
  refine ⟨diff_le hp.1 shift, fun m hm => ?_⟩
  rw [diff_coeff_sum]
  refine Finset.sum_nonneg fun d hd => ?_
  have hdeg : d.degree ≤ n + 1 := (le_totalDegree hd).trans hp.1
  have hmono : (monomial d (p.coeff d)).totalDegree ≤ d.degree :=
    totalDegree_monomial_le _ _
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · rw [(diff_monomial shift d (p.coeff d) d.degree hmono).1 m (by omega)]
  · apply (diff_monomial shift d (p.coeff d) d.degree hmono).2 _ m (by omega)
    intro u
    rw [coeff_monomial]
    split_ifs
    · exact hp.2 d heq
    · exact le_rfl
private theorem advance {n : ℕ} {p q r : HilbertPoly}
    (prev : Top (n + 1) (p - q)) (hq : q.totalDegree ≤ n + 1) (shift : Fin 4 → ℕ)
    (hr : NonnegativeTop r) (hgap : NonnegativeTop (difference q shift - r)) :
    r.totalDegree ≤ n ∧ Top n (difference p shift - r) := by
  obtain ⟨hd, h₁⟩ := cut (diff_le hq shift) hr hgap
  have h₂ := diff_top prev shift
  rw [diff_sub] at h₂
  refine ⟨hd, ?_⟩
  convert top_add h₂ h₁ using 1
  ring

theorem three_cut_top (p₀ p₁ p₂ p₃ : HilbertPoly) (f g s : Fin 4 → ℕ)
    (h₀ : p₀.totalDegree≤4) (h₁ : NonnegativeTop p₁) (h₂ : NonnegativeTop p₂)
    (h₃ : NonnegativeTop p₃)
    (hf : NonnegativeTop (difference p₀ f-p₁)) (hg : NonnegativeTop (difference p₁ g-p₂))
    (hs : NonnegativeTop (difference p₂ s-p₃)) :
    p₃.totalDegree≤1 ∧ Top 1 (difference (difference (difference p₀ f) g) s-p₃) := by
  obtain ⟨hq₁, hb₁⟩ := cut (diff_le (n:=3) h₀ f) h₁ hf
  obtain ⟨hq₂, hb₂⟩ := advance (n:=2) hb₁ hq₁ g h₂ hg
  exact advance (n:=1) hb₂ hq₂ s h₃ hs


def ambient : HilbertPoly :=
  (MvPolynomial.X 1+1)*(MvPolynomial.X 0+MvPolynomial.X 1+1)*
    (MvPolynomial.X 2+1)*(MvPolynomial.X 3+1)

theorem ambient_degree : ambient.totalDegree≤4 := by
  have hX (i : Fin 4) : (MvPolynomial.X i : HilbertPoly).totalDegree≤1 := by simp
  have h1 : (1 : HilbertPoly).totalDegree≤1 := by simp
  have hadd {p q : HilbertPoly} (hp : p.totalDegree≤1) (hq : q.totalDegree≤1) :
      (p+q).totalDegree≤1 := (totalDegree_add _ _).trans (max_le hp hq)
  have hmul {p q : HilbertPoly} {a b : ℕ} (hp : p.totalDegree≤a) (hq : q.totalDegree≤b) :
      (p*q).totalDegree≤a+b := (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
  exact hmul (hmul (hmul (hadd (hX 1) h1) (hadd (hadd (hX 0) (hX 1)) h1))
    (hadd (hX 2) h1)) (hadd (hX 3) h1)

private theorem eval_difference (p : HilbertPoly) (a : Fin 4→ℕ) (x : Fin 4→ℚ) :
    eval x (difference p a) = eval x p - eval (fun i=>x i - (a i : ℚ)) p := by
  simp only [difference,map_sub]
  congr 1
  change eval₂Hom (RingHom.id ℚ) _ (bind₁ _ p) = eval₂Hom (RingHom.id ℚ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext i
  simp

private theorem eval_ambient (x : Fin 4→ℚ) :
    eval x ambient = (x 1+1)*(x 0+x 1+1)*(x 2+1)*(x 3+1) := by
  simp [ambient]

theorem constant_le_eval_of_top (p : HilbertPoly) (hp : Top 1 p) {x : Fin 4→ℚ}
    (hx : ∀ i, 0≤x i) : p.coeff 0≤eval x p := by
  have hc (m : Exp) : 0≤(p-C (p.coeff 0)).coeff m := by
    rw [coeff_sub,coeff_C]
    split_ifs with hm
    · subst m
      rw [sub_self]
    · rw [sub_zero]
      by_cases h : m.degree = 1
      · exact hp.2 m h
      · have h0 : m.degree ≠ 0 := fun hz => hm ((Finsupp.degree_eq_zero_iff m).mp hz).symm
        have hh := hp.1
        rw [coeff_eq_zero_of_totalDegree_lt (show p.totalDegree<m.degree by omega)]
  have pnonneg : 0≤eval x (p-C (p.coeff 0)) := by
    rw [MvPolynomial.eval_eq]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (hc m)
      (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)
  rw [map_sub,eval_C] at pnonneg
  exact sub_nonneg.mp pnonneg


def directionalCoeff (e v₀ v₁ b c : ℚ) (a : Fin 4→ℚ) : ℚ :=
  e*(a 2*c+a 3*b)+(a 0+2*e*a 1)*(v₀*c+v₁*b)+
    (3*e-3)*(v₀*a 3+v₁*a 2)+2*v₀*v₁*((e-1)*a 1+a 0)

def rootDirection (e v₀ v₁ : ℕ) : Fin 4→ℕ := ![e,0,v₀,v₁]
def tangentDirection (e v₀ v₁ : ℕ) : Fin 4→ℕ := ![e-2,1,v₀,v₁]
def diagonal (e b c : ℕ) : Fin 4→ℕ := ![e-3,1,b,c]

theorem directional_eq (e v₀ v₁ b c : ℕ) (he : 3≤e) (a : Fin 4→ℕ) (n : ℚ) :
    let p := difference (difference (difference ambient (rootDirection e v₀ v₁))
      (tangentDirection e v₀ v₁)) a
    eval (fun i=>n*(diagonal e b c i:ℚ)) p =
      n*directionalCoeff e v₀ v₁ b c (fun i=>a i) + eval 0 p := by
  have he2 : 2≤e := by omega
  dsimp
  simp only [eval_difference,eval_ambient,rootDirection,tangentDirection,diagonal,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
    Nat.cast_sub he,Nat.cast_sub he2,Nat.cast_zero,Nat.cast_one,Pi.zero_apply,mul_one]
  unfold directionalCoeff
  ring

theorem direction_le (e v₀ v₁ b c : ℕ) (he : 3≤e) (a : Fin 4→ℕ) (k : ℕ)
    (ha : ∀ i, a i≤k*diagonal e b c i) :
    directionalCoeff e v₀ v₁ b c (fun i=>a i) ≤
      k*(2*((e:ℚ)*b*c+(v₀*c+v₁*b)*(3*(e:ℚ)-3)+v₀*v₁*(2*(e:ℚ)-4))) := by
  have heQ : (3:ℚ)≤e := by exact_mod_cast he
  have hQ (i : Fin 4) : (a i:ℚ)≤(k:ℚ)*(diagonal e b c i:ℚ) := by exact_mod_cast ha i
  have h0 := hQ 0
  have h1 := hQ 1
  have h2 := hQ 2
  have h3 := hQ 3
  simp only [diagonal,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,Nat.cast_sub he,Nat.cast_ofNat,Nat.cast_one,mul_one] at h0 h1 h2 h3
  unfold directionalCoeff
  calc
    _ ≤ (e:ℚ)*(k*b*c+k*c*b) + (k*((e:ℚ)-3)+2*e*k)*(v₀*c+v₁*b) +
        (3*e-3)*(v₀*(k*c)+v₁*(k*b)) + 2*v₀*v₁*((e-1)*k+k*(e-3)) := by
      gcongr <;> first | assumption | linarith | positivity
    _ = _ := by ring

#print axioms three_cut_top
#print axioms constant_le_eval_of_top
#print axioms directional_eq
#print axioms direction_le
end
end Rect51MixedPoly
