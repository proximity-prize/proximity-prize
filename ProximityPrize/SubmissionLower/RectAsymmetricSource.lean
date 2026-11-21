import ProximityPrize.SubmissionLower.Rect51PoleWindow

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace RectAsymmetric
noncomputable section

open Polynomial
open K1 (I)
open K1_14 (L Shape shapeSum)
open K1_14_1 K1_14_1_7
open Rect51PoleWindow (RectShaped)
open scoped BigOperators Polynomial

/-- Restrict each seed degree by its own cap. -/
def rectangle (u v : ℕ) : Submodule L Source where
  carrier := {P | ∀ j i a e (k : Fin 2), (![u,v] : Fin 2 → ℕ) k < e k → coeffAt P j i a e = 0}
  zero_mem' := by simp [coeffAt]
  add_mem' := by
    intro P Q hP hQ j i a e k hk
    have hp := hP j i a e k hk
    have hq := hQ j i a e k hk
    unfold coeffAt at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro c P hP j i a e k hk
    have hp := hP j i a e k hk
    unfold coeffAt at hp ⊢
    simp [Polynomial.coeff_smul, hp]

theorem mem_rectangle_iff {u v : ℕ} {P : Source} :
    P ∈ rectangle u v ↔
      ∀ j i a e, coeffAt P j i a e ≠ 0 → ∀ k : Fin 2, e k ≤ (![u,v] : Fin 2 → ℕ) k := by
  constructor
  · intro h j i a e hn k
    exact Nat.le_of_not_gt (fun hk => hn (h j i a e k hk))
  · intro h j i a e k hk
    by_contra hn
    exact (Nat.not_le_of_gt hk) (h j i a e hn k)

theorem rectShaped_of_mem {h W u v : ℕ} {s : Shape} {P : Source}
    (hA : P ∈ ambient h s W) (hS : P ∈ rectangle u v) :
    RectShaped s ![u,v] P := by
  refine ⟨?_, mem_rectangle_iff.mp hS⟩
  intro j i a e hn
  have he : trueEligible h s W j i a e := by
    by_contra hbad
    exact hn (hA j i a e hbad)
  exact ⟨he.1, he.2.1, he.2.2.1⟩

private abbrev SeedRectangle (u v : ℕ) := Fin (u+1) × Fin (v+1)
private def exponentRectangle {u v : ℕ} (x : SeedRectangle u v) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![x.1.val,x.2.val]

private theorem exponentRectangle_fits {u v : ℕ} (x : SeedRectangle u v) (k : Fin 2) :
    exponentRectangle x k ≤ (![u,v] : Fin 2 → ℕ) k := by
  fin_cases k
  · exact Nat.le_of_lt_succ x.1.isLt
  · exact Nat.le_of_lt_succ x.2.isLt

private theorem seedWeight_of_rectangle {u v : ℕ} {e : Fin 2 →₀ ℕ}
    (he : ∀ k : Fin 2, e k ≤ (![u,v] : Fin 2 → ℕ) k) :
    seedWeight e ≤ u+v := by
  rw [seedWeight, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  exact Nat.add_le_add (he 0) (he 1)

private theorem exists_exponentRectangle {u v : ℕ} {e : Fin 2 →₀ ℕ}
    (he : ∀ k : Fin 2, e k ≤ (![u,v] : Fin 2 → ℕ) k) :
    ∃ x : SeedRectangle u v, exponentRectangle x = e := by
  refine ⟨(⟨e 0, Nat.lt_succ_of_le (he 0)⟩, ⟨e 1, Nat.lt_succ_of_le (he 1)⟩), ?_⟩
  ext k
  fin_cases k <;> rfl

private theorem exponentRectangle_injective (u v : ℕ) :
    Function.Injective (exponentRectangle (u := u) (v := v)) := by
  intro x y h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  · exact congrArg (fun e : Fin 2 →₀ ℕ => e 1) h

open private trueWidth trueWidth_eq_add lt_trueWidth_iff monomialAt coeffAt_monomialAt
  from ProximityPrize.SubmissionLower.Fast065

private abbrev RectangleIndex (h : ℕ) (s : Shape) (W u v : ℕ) :=
  Σ q : Fin (s.B+1), Σ j : Fin (min q.val s.J + 1),
    Fin (trueWidth h s W q.val j.val) × SeedRectangle u v

private def tags {h : ℕ} {s : Shape} {W u v : ℕ} (x : RectangleIndex h s W u v) :
    ℕ × ℕ × ℕ × (Fin 2 →₀ ℕ) :=
  (x.2.1.val,x.1.val - x.2.1.val,x.2.2.1.val,exponentRectangle x.2.2.2)

private theorem tags_injective (h : ℕ) (s : Shape) (W u v : ℕ) :
    Function.Injective (tags (h := h) (s := s) (W := W) (u := u) (v := v)) := by
  rintro ⟨q,j,a,e⟩ ⟨q',j',a',e'⟩ he
  have hj : j.val = j'.val := congrArg Prod.fst he
  have hi : q.val-j.val = q'.val-j'.val := congrArg (fun p => p.2.1) he
  have hlt := j.isLt
  have hlt' := j'.isLt
  have hmin := Nat.min_le_left q.val s.J
  have hmin' := Nat.min_le_left q'.val s.J
  have hq : q = q' := Fin.ext (by omega)
  subst q'
  have hj' : j = j' := Fin.ext hj
  subst j'
  have ha : a = a' := Fin.ext (congrArg (fun p => p.2.2.1) he)
  subst a'
  have he' : e = e' := exponentRectangle_injective u v (congrArg (fun p => p.2.2.2) he)
  subst e'
  rfl

private def rectMonomial {h : ℕ} {s : Shape} {W u v : ℕ}
    (hUs : u+v ≤ s.U) (x : RectangleIndex h s W u v) : ↥(ambient h s W ⊓ rectangle u v : Submodule L Source) := by
  refine ⟨monomialAt (tags x), ?_, ?_⟩
  · intro j i a e hn
    rw [coeffAt_monomialAt (tags x) (j, i, a, e), ite_eq_right]
    intro he
    apply hn
    have hg : x.2.1.val ≤ x.1.val := (Nat.le_of_lt_succ x.2.1.isLt).trans (min_le_left _ _)
    have hj : x.2.1.val ≤ s.J := (Nat.le_of_lt_succ x.2.1.isLt).trans (min_le_right _ _)
    have he' := (seedWeight_of_rectangle (exponentRectangle_fits x.2.2.2)).trans hUs
    have hw := (lt_trueWidth_iff h s W _ _ _).mp x.2.2.1.isLt
    have hs : trueEligible h s W (tags x).1 (tags x).2.1 (tags x).2.2.1 (tags x).2.2.2 := by
      change trueEligible h s W x.2.1.val (x.1.val-x.2.1.val) x.2.2.1.val
        (exponentRectangle x.2.2.2)
      have hgrade : x.1.val - x.2.1.val + x.2.1.val = x.1.val := by omega
      unfold trueEligible
      rw [hgrade]
      exact ⟨Nat.le_of_lt_succ x.1.isLt,hj,he',hw⟩
    simpa only [he] using hs
  · apply mem_rectangle_iff.mpr
    intro j i a e hn k
    rw [coeffAt_monomialAt (tags x) (j, i, a, e)] at hn
    split_ifs at hn with he
    · have heq : exponentRectangle x.2.2.2 = e := congrArg (fun p => p.2.2.2) he
      rw [← heq]
      exact exponentRectangle_fits x.2.2.2 k
    · exact False.elim (hn rfl)

private def rectCoordinates (h : ℕ) (s : Shape) (W u v : ℕ) :
    (ambient h s W ⊓ rectangle u v : Submodule L Source) →ₗ[L] (RectangleIndex h s W u v → L) :=
  LinearMap.pi fun x => (readCoeff (tags x).1 (tags x).2.1 (tags x).2.2.1 (tags x).2.2.2).comp
    (ambient h s W ⊓ rectangle u v : Submodule L Source).subtype

private def rectEquiv (h : ℕ) (s : Shape) (W u v : ℕ) (hUs : u+v ≤ s.U) :
    (ambient h s W ⊓ rectangle u v : Submodule L Source) ≃ₗ[L] (RectangleIndex h s W u v → L) := by
  classical
  refine LinearEquiv.ofBijective (rectCoordinates h s W u v) ⟨?_, ?_⟩
  · intro P Q hPQ
    apply Subtype.ext
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    apply MvPolynomial.ext
    intro e
    change coeffAt P.val j i a e = coeffAt Q.val j i a e
    by_cases he : trueEligible h s W j i a e
    · by_cases hs : ∀ k : Fin 2, e k ≤ (![u,v] : Fin 2 → ℕ) k
      · obtain ⟨seed, hseed⟩ := exists_exponentRectangle hs
        let q : Fin (s.B+1) := ⟨i+j, Nat.lt_succ_of_le he.1⟩
        let jSlot : Fin (min q.val s.J + 1) := ⟨j, Nat.lt_succ_of_le (le_min (by change j ≤ i+j; omega) he.2.1)⟩
        let x : RectangleIndex h s W u v := ⟨q,jSlot,⟨a,(lt_trueWidth_iff h s W _ _ _).mpr he.2.2.2⟩,seed⟩
        have hx : tags x = (j,i,a,e) := by simp [tags,x,q,jSlot,hseed]
        have hh := congrFun hPQ x
        change coeffAt P.val (tags x).1 (tags x).2.1 (tags x).2.2.1 (tags x).2.2.2 =
          coeffAt Q.val (tags x).1 (tags x).2.1 (tags x).2.2.1 (tags x).2.2.2 at hh
        simpa only [hx] using hh
      · have zero (R : ↥(ambient h s W ⊓ rectangle u v : Submodule L Source)) : coeffAt R.val j i a e = 0 := by
          by_contra hn
          exact hs (mem_rectangle_iff.mp R.property.2 j i a e hn)
        rw [zero P,zero Q]
    · exact (P.property.1 j i a e he).trans (Q.property.1 j i a e he).symm
  · intro f
    refine ⟨∑ x, f x • rectMonomial hUs x, ?_⟩
    funext z
    rw [map_sum]
    have h (x : RectangleIndex h s W u v) :
        rectCoordinates h s W u v (rectMonomial hUs x) z = if x = z then 1 else 0 := by
      change coeffAt (monomialAt (tags x)) (tags z).1 (tags z).2.1 (tags z).2.2.1
        (tags z).2.2.2 = _
      simp only [coeffAt_monomialAt, (tags_injective h s W u v).eq_iff]
    simp [Finset.sum_apply, h, mul_ite]

theorem rectAmbient_finite (h : ℕ) (s : Shape) (W u v : ℕ) (hUs : u+v ≤ s.U) :
    Module.Finite L (ambient h s W ⊓ rectangle u v : Submodule L Source) :=
  Module.Finite.of_injective (rectEquiv h s W u v hUs).toLinearMap
    (rectEquiv h s W u v hUs).injective

/-- The raw rectangular source has this many coefficients before the pole tests. -/
def rectAmbientVolume (h : ℕ) (s : Shape) (W u v : ℕ) : ℕ :=
  ((u+1)*(v+1)) * shapeSum s (fun q j => W+1+j-q*(131071-h))

def rectPoleCredit (h : ℕ) (s : Shape) (u v : ℕ) : ℕ :=
  ((u+1)*(v+1))*(2*h)*shapeSum s (fun q _ => s.B+s.J-q)

theorem rectAmbientBound {h : ℕ} (hhi : h ≤ 131071) (s : Shape) (W u v : ℕ)
    (hw : rawWidthCond h s W) (hUs : u+v ≤ s.U) :
    rectAmbientVolume h s W u v + rectPoleCredit h s u v ≤
      Module.finrank L (ambient h s W ⊓ rectangle u v : Submodule L Source) := by
  rw [(rectEquiv h s W u v hUs).finrank_eq, Module.finrank_pi]
  simp only [RectangleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun q : ℕ => ∑ j : Fin (min q s.J + 1),
    trueWidth h s W q j.val * ((u+1)*(v+1)))]
  unfold rectAmbientVolume rectPoleCredit shapeSum
  simp only [Nat.mul_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q hq => ?_
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => trueWidth h s W q j * ((u+1)*(v+1)))]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [trueWidth_eq_add hhi hw (by simpa using hq) (by simpa using hj)]
  ring_nf
  apply le_rfl

end
end RectAsymmetric
