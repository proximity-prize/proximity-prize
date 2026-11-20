import ProximityPrize.SubmissionLower.Koala6844VirtualShortGermTransport
import ProximityPrize.SubmissionLower.Koala6844Comparison


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial Koala6844BivariateSeeds
open scoped BigOperators Classical Matrix

noncomputable section
set_option autoImplicit false

variable {K E : Type*} [Field K] [Field E]

def affineSeed (a b : E) (i : Fin 2) : MvPolynomial (Fin 2) E :=
  MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X i

private theorem degreeOf_affineSeed (a b : E) (i j : Fin 2) :
    (affineSeed a b j).degreeOf i ≤ if i = j then 1 else 0 := by
  apply (MvPolynomial.degreeOf_add_le _ _ _).trans
  apply max_le
  · simp
  · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])

def mobiusGermNumerator (J : MvPolynomial (Fin 2) E) (a0 a1 c b0 b1 : E) :
    MvPolynomial (Fin 2) E :=
  homogeneousEval seedIntoSecond (packValue J) (packValue J).natDegree
    (affineSeed a0 a1 1 * (MvPolynomial.C c * MvPolynomial.X 0))
    (affineSeed b0 b1 0)

private theorem packed_mobiusGermNumerator (J : MvPolynomial (Fin 2) E)
    (a0 a1 c b0 b1 : E) :
    packValue (mobiusGermNumerator J a0 a1 c b0 b1) =
      homogeneousEval Polynomial.C (packValue J) (packValue J).natDegree
        (Polynomial.C ((MvPolynomial.C a0 + MvPolynomial.C a1 * MvPolynomial.X 0) *
          MvPolynomial.C c) * Polynomial.X)
        (Polynomial.C (MvPolynomial.C b0) + Polynomial.C (MvPolynomial.C b1) * Polynomial.X) := by
  let P := (packValue (R := E)).toRingHom
  have h := map_homogeneousEval seedIntoSecond P (packValue J) (packValue J).natDegree
    (affineSeed a0 a1 1 * (MvPolynomial.C c * MvPolynomial.X 0)) (affineSeed b0 b1 0)
  have hP : P.comp seedIntoSecond = Polynomial.C :=
    RingHom.ext (fun Q => packValue_seedIntoSecond Q)
  have hc (s : E) : P (MvPolynomial.C s) = Polynomial.C (MvPolynomial.C s) := by
    simp [P, packValue, MvPolynomial.finSuccEquiv_apply]
  have hx0 : P (MvPolynomial.X 0) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
  have hx1 : P (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X (0 : Fin 1)) :=
    MvPolynomial.finSuccEquiv_X_succ (j := (0 : Fin 1))
  change P (mobiusGermNumerator J a0 a1 c b0 b1) = _
  rw [mobiusGermNumerator, h, hP]
  simp only [affineSeed, map_add, map_mul, hc, hx0,hx1]
  simp only [← Polynomial.C.map_mul, ← Polynomial.C.map_add]
  rw [← mul_assoc, ← Polynomial.C.map_mul]

theorem mobiusGermNumerator_ne_zero
    (J : MvPolynomial (Fin 2) E) (hJ : J ≠ 0) (a0 a1 c b0 b1 : E)
    (hA : a0 ≠ 0 ∨ a1 ≠ 0) (hc : c ≠ 0) (hb0 : b0 ≠ 0) :
    mobiusGermNumerator J a0 a1 c b0 b1 ≠ 0 := by
  intro hz
  let A : MvPolynomial (Fin 1) E := MvPolynomial.C a0 + MvPolynomial.C a1 * MvPolynomial.X 0
  let ac : MvPolynomial (Fin 1) E := A * MvPolynomial.C c
  have hAn : A ≠ 0 := by
    intro h
    rcases hA with h0 | h1
    · have e := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (0 : E))) h
      exact h0 (by simpa [A] using e)
    · have hh : a0 = 0 := by
        have e := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (0 : E))) h
        simpa [A] using e
      have e := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (1 : E))) h
      exact h1 (by simpa [A, hh] using e)
  have hc' : (MvPolynomial.C c : MvPolynomial (Fin 1) E) ≠ 0 := by simpa using hc
  have hac : ac ≠ 0 := mul_ne_zero hAn hc'
  let Q := packValue J
  have hQ : Q ≠ 0 := fun h =>
    hJ ((packValue (R := E)).injective (h.trans (map_zero (packValue (R := E))).symm))
  have h := packed_mobiusGermNumerator J a0 a1 c b0 b1
  rw [hz, map_zero] at h
  change 0 = homogeneousEval Polynomial.C Q Q.natDegree
    (Polynomial.C ac * Polynomial.X)
    (Polynomial.C (MvPolynomial.C b0) + Polynomial.C (MvPolynomial.C b1) * Polynomial.X) at h
  rcases eq_or_ne b1 0 with rfl | hb1
  · have ne := homogeneousEval_affine_ne_zero (RingHom.id (MvPolynomial (Fin 1) E))
      Function.injective_id Q hQ ac 0 (MvPolynomial.C b0) hac
    exact ne (by simpa only [RingHom.comp_id, map_zero, zero_mul, zero_add, add_zero] using h.symm)
  · let ζ := (-b0)/b1
    have hζ : ζ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb0) hb1
    have hden : b0+b1*ζ = 0 := by dsimp [ζ]; field_simp; ring
    let ev := Polynomial.evalRingHom (MvPolynomial.C ζ : MvPolynomial (Fin 1) E)
    have he := congrArg ev h
    have he0 : ev.comp Polynomial.C = RingHom.id (MvPolynomial (Fin 1) E) :=
      RingHom.ext (fun a => by simp [ev])
    have hl : MvPolynomial.C b0 + (MvPolynomial.C b1 : MvPolynomial (Fin 1) E) * MvPolynomial.C ζ = 0 := by
      rw [← map_mul, ← map_add, hden, map_zero]
    rw [map_zero, map_homogeneousEval, he0] at he
    have eC (p : MvPolynomial (Fin 1) E) : ev (Polynomial.C p) = p := by simp [ev]
    have eX : ev Polynomial.X = MvPolynomial.C ζ := by simp [ev]
    simp only [map_mul, map_add, eC, eX, hl] at he
    rw [homogeneousEval_at_pole _ _ hQ] at he
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ)
      (pow_ne_zero _ (mul_ne_zero hac (by simpa using hζ))) he.symm

theorem mobiusGermNumerator_caps (J : MvPolynomial (Fin 2) E) (a0 a1 c b0 b1 : E) (u v : ℕ)
    (hy : J.degreeOf 0 ≤ u) (ht : J.totalDegree ≤ v) :
    (mobiusGermNumerator J a0 a1 c b0 b1).degreeOf 0 ≤ u ∧
      (mobiusGermNumerator J a0 a1 c b0 b1).degreeOf 1 ≤ v := by
  let N := affineSeed a0 a1 1 * (MvPolynomial.C c * MvPolynomial.X (0 : Fin 2))
  let D := affineSeed b0 b1 0
  have hn (i : Fin 2) : N.degreeOf i ≤ 1 := by
    apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
    have ha := degreeOf_affineSeed a0 a1 i 1
    have hb := MvPolynomial.degreeOf_mul_le i (MvPolynomial.C c) (MvPolynomial.X 0)
    fin_cases i <;> simp [MvPolynomial.degreeOf_X] at ha hb ⊢ <;> omega
  have hd0 : D.degreeOf 0 ≤ 1 := by simpa [D] using degreeOf_affineSeed b0 b1 0 0
  have hd1 : D.degreeOf 1 = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [D] using degreeOf_affineSeed b0 b1 1 0)
  refine ⟨?_,?_⟩
  · apply homogeneousEval_degreeOf_le
    intro j hj
    let s := (packValue J).natDegree
    change (seedIntoSecond ((packValue J).coeff j)).degreeOf 0 + j*N.degreeOf 0 +
      (s-j)*D.degreeOf 0 ≤ u
    have hjs : j ≤ s := Polynomial.le_natDegree_of_mem_supp _ hj
    rw [seedIntoSecond_degree_zero, zero_add]
    exact (Nat.add_le_add (Nat.mul_le_mul_left _ (hn 0)) (Nat.mul_le_mul_left _ hd0)).trans
      (by rw [mul_one, mul_one, Nat.add_sub_of_le hjs]; exact
        (MvPolynomial.natDegree_finSuccEquiv J).trans_le hy)
  · apply homogeneousEval_degreeOf_le
    intro j hj
    change (seedIntoSecond ((packValue J).coeff j)).degreeOf 1 + j*N.degreeOf 1 +
      ((packValue J).natDegree-j)*D.degreeOf 1 ≤ v
    rw [hd1,mul_zero,add_zero]
    have hseed := (MvPolynomial.degreeOf_le_totalDegree (seedIntoSecond ((packValue J).coeff j)) 1).trans
      ((MvPolynomial.totalDegree_rename_le Fin.succ ((packValue J).coeff j)).trans
        (totalDegree_coeff_pack_le J j v ht))
    have hjv := (Polynomial.le_natDegree_of_mem_supp _ hj).trans
      ((MvPolynomial.natDegree_finSuccEquiv J).trans_le ((MvPolynomial.degreeOf_le_totalDegree J 0).trans ht))
    exact (Nat.add_le_add hseed (Nat.mul_le_mul_left _ (hn 1))).trans (by omega)

theorem mobiusGermNumerator_eval_zero (J : MvPolynomial (Fin 2) E)
    (a0 a1 c b0 b1 y g h : E) (hy : MvPolynomial.eval ![y,g] J = 0)
    (he : y * (b0+h*b1) = (a0+g*a1)*c*h) :
    MvPolynomial.eval ![h,g] (mobiusGermNumerator J a0 a1 c b0 b1) = 0 := by
  rw [mobiusGermNumerator, map_homogeneousEval]
  have hmap : (MvPolynomial.eval ![h,g]).comp seedIntoSecond = MvPolynomial.eval (fun _ : Fin 1 => g) := by
    apply MvPolynomial.ringHom_ext
    · simp
    · intro i
      fin_cases i
      simp [seedIntoSecond]
  rw [hmap,homogeneousEval_eq_mul_eval₂ _ _ _ le_rfl _ _ y, eval_packValue, hy, mul_zero]
  simp only [affineSeed, map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination -he

theorem card_le_of_active_germ_equation (embed : K →+* E) (p u v : ℕ)
    (J : MvPolynomial (Fin 2) E) (hJ : J ≠ 0) (hu : J.degreeOf 0 ≤ u)
    (hv : J.totalDegree ≤ v) (hp : v < p) (a0 a1 c b0 b1 : E)
    (ha : a0 ≠ 0 ∨ a1 ≠ 0) (hc : c ≠ 0) (hb : b0 ≠ 0)
    (S : Finset K) (y : K → E) (hy : ∀ g ∈ S, MvPolynomial.eval ![y g,embed g] J = 0)
    (he : ∀ g ∈ S,
      y g*(b0+(embed g)^p*b1) = (a0+embed g*a1)*c*(embed g)^p) :
    S.card ≤ v+p*u := by
  classical
  let F := mobiusGermNumerator J a0 a1 c b0 b1
  let τ := Equiv.swap (0 : Fin 2) 1
  let G := MvPolynomial.rename τ F
  have hn : F ≠ 0 := mobiusGermNumerator_ne_zero J hJ _ _ _ _ _ ha hc hb
  have hG : G ≠ 0 := fun h => hn (MvPolynomial.rename_injective _ τ.injective (h.trans (map_zero _).symm))
  obtain ⟨h0,h1⟩ := mobiusGermNumerator_caps J a0 a1 c b0 b1 u v hu hv
  have ht0 : τ 0 = 1 := by decide
  have ht1 : τ 1 = 0 := by decide
  have hd0 : G.degreeOf 0 ≤ v := by
    rw [← ht1]
    exact (MvPolynomial.degreeOf_rename_of_injective τ.injective 1).trans_le h1
  have hd1 : G.degreeOf 1 ≤ u := by
    rw [← ht0]
    exact (MvPolynomial.degreeOf_rename_of_injective τ.injective 0).trans_le h0
  have hz (g : K) (hg : g ∈ S) :
      MvPolynomial.eval (coordinates (embed g) ((embed g)^p)) G = 0 := by
    have H := mobiusGermNumerator_eval_zero J a0 a1 c b0 b1 (y g) (embed g) ((embed g)^p)
      (hy g hg) (he g hg)
    unfold G
    rw [MvPolynomial.eval_rename]
    have heq : coordinates (embed g) ((embed g)^p) ∘ τ = ![(embed g)^p,embed g] := by
      funext i
      fin_cases i <;> simp [coordinates, ht0,ht1]
    rw [heq]
    exact H
  let em : K ↪ E := ⟨embed,embed.injective⟩
  have H := Koala6844BivariateSeeds.card_le_of_vanishing
    (p := p) (b := v+1) (c := u+1) (by omega) (by omega)
    hG (by omega : G.degreeOf 0 < v+1) (by omega : G.degreeOf 1 < u+1) (S.map em)
    (by
      intro a ha'
      obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp ha'
      exact hz g hg)
  rw [Finset.card_map, Nat.add_sub_cancel, Nat.add_sub_cancel] at H
  exact H

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
