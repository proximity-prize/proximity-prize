import ProximityPrize.SubmissionLower.Koala6844VirtualHighResolved
import ProximityPrize.SubmissionLower.Koala6844VirtualHighBandPartner


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial RCN132 Koala6844BivariateSeeds
open scoped Classical BigOperators

noncomputable section
set_option autoImplicit false

variable {K Seed : Type} [Field K] [Field Seed]
local notation "R" => MvPolynomial (Fin 4) K
local notation "E" => RationalCoefficients K

def seedPoint (embed : Seed →+* E) (p : ℕ) (value : Seed → E) (g : Seed) : Fin 3 → E :=
  Fin.cases (value g) (coordinates (embed g) ((embed g)^p))

def surfaceSeeds (embed : Seed →+* E) (p : ℕ) (value : Seed → E)
    (A : Finset Seed) (F : R) : Finset Seed :=
  A.filter fun g => MvPolynomial.eval (seedPoint embed p value g) (rationalSurfaceMap K F) = 0

theorem card_seed_only {embed : Seed →+* E} {p : ℕ} {value : Seed → E} (A : Finset Seed)
    (F : R) (hF : F ≠ 0) (hy : F.degreeOf 1 = 0) (hp : 0 < p) (hsmall : F.degreeOf 2 < p) :
    (surfaceSeeds embed p value A F).card ≤ F.degreeOf 2 + p * F.degreeOf 3 := by
  let P := MvPolynomial.finSuccEquiv E 2 (rationalSurfaceMap K F)
  have hdeg : P.natDegree = 0 := by
    change (MvPolynomial.finSuccEquiv E 2 (rationalSurfaceMap K F)).natDegree = 0
    rw [MvPolynomial.natDegree_finSuccEquiv, rationalSurface_degreeOf]
    exact hy
  have hP : P ≠ 0 := by
    intro hzero
    exact RCN136.surfaceMap_ne_zero _ (IsFractionRing.injective _ _) F hF
      ((MvPolynomial.finSuccEquiv E 2).injective (hzero.trans (map_zero _).symm))
  have he := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hc : P.coeff 0 ≠ 0 := by
    intro hz
    exact hP (he.trans (hz ▸ map_zero Polynomial.C))
  let S := surfaceSeeds embed p value A F
  have hl (i : Fin 2) : (P.coeff 0).degreeOf i ≤ F.degreeOf i.succ.succ :=
    (coeff_collectValue_degree_le _ 0 i).trans_eq (rationalSurface_degreeOf F i.succ)
  have hzeros (t : E) (ht : t ∈ S.image embed) :
      MvPolynomial.eval (coordinates t (t^p)) (P.coeff 0) = 0 := by
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ht
    have hz := (Finset.mem_filter.mp hg).2
    change _ at hz
    have hv := (eval₂_collectValue (rationalSurfaceMap K F) (value g)
      (coordinates (embed g) ((embed g)^p))).trans hz
    change P.eval₂ _ _ = 0 at hv
    rw [he,Polynomial.eval₂_C] at hv
    exact hv
  have hbound := card_le_of_vanishing (b := F.degreeOf 2 + 1) (c := F.degreeOf 3 + 1)
    hp (Nat.succ_le_of_lt hsmall) hc (Nat.lt_succ_of_le (hl 0))
    (Nat.lt_succ_of_le (hl 1)) (S.image embed) hzeros
  rw [Finset.card_image_of_injective _ embed.injective] at hbound
  simpa only [Nat.add_sub_cancel] using hbound

private theorem eval_same_of_seed_free (F : MvPolynomial (Fin 3) E)
    (ha : F.degreeOf 1 = 0) (hb : F.degreeOf 2 = 0)
    (v : E) (z : Fin 2 → E) :
    MvPolynomial.eval (Fin.cases v z) F = MvPolynomial.eval (Fin.cases v (0 : Fin 2 → E)) F := by
  rw [MvPolynomial.eval, MvPolynomial.eval]
  apply MvPolynomial.eval₂_congr
  intro i d hi hd
  refine Fin.cases ?_ (fun j => ?_) i hi
  · intro _
    rfl
  · intro hj
    have hh : F.degreeOf j.succ = 0 := by
      fin_cases j
      · exact ha
      · exact hb
    have hd0 := (MvPolynomial.monomial_le_degreeOf j.succ
      (MvPolynomial.mem_support_iff.mpr hd)).trans_eq hh
    exact ((Finsupp.mem_support_iff.mp hj) (Nat.eq_zero_of_le_zero hd0)).elim

theorem card_seed_free {embed : Seed →+* E} {p : ℕ} {value : Seed → E}
    (A : Finset Seed) (hinj : Set.InjOn value (↑A : Set Seed))
    (F : R) (hF : F ≠ 0) (hb : F.degreeOf 2 = 0) (hc : F.degreeOf 3 = 0) :
    (surfaceSeeds embed p value A F).card ≤ F.degreeOf 1 := by
  let H := rationalSurfaceMap K F
  let P := MvPolynomial.finSuccEquiv E 2 H
  let T := P.map (MvPolynomial.eval (0 : Fin 2 → E))
  have hdeg : T.natDegree ≤ F.degreeOf 1 := by
    apply Polynomial.natDegree_map_le.trans
    rw [MvPolynomial.natDegree_finSuccEquiv,rationalSurface_degreeOf]
    exact le_rfl
  have haH : H.degreeOf 1 = 0 := (rationalSurface_degreeOf F 1).trans hb
  have hbH : H.degreeOf 2 = 0 := (rationalSurface_degreeOf F 2).trans hc
  have ht : T ≠ 0 := by
    intro hz
    have hHz : H = 0 := by
      ext d
      have hcoeff := congrArg (fun x : Polynomial E => x.coeff (d 0)) hz
      simp only [Polynomial.coeff_map,Polynomial.coeff_zero,T] at hcoeff
      change H.coeff d = 0
      by_cases hds : d.tail = 0
      · rw [← Finsupp.cons_tail d, hds, ← MvPolynomial.finSuccEquiv_coeff_coeff]
        simpa only [P,MvPolynomial.eval_zero,MvPolynomial.constantCoeff_eq] using hcoeff
      · by_contra hn
        have hd := MvPolynomial.mem_support_iff.mpr hn
        apply hds
        ext i
        have hle := MvPolynomial.monomial_le_degreeOf i.succ hd
        fin_cases i
        · change d 1 ≤ H.degreeOf 1 at hle
          simp [Finsupp.tail_apply, Nat.eq_zero_of_le_zero (hle.trans_eq haH)]
        · change d 2 ≤ H.degreeOf 2 at hle
          simp [Finsupp.tail_apply, Nat.eq_zero_of_le_zero (hle.trans_eq hbH)]
    exact hF (RCN136.surfaceMap_injective _ (IsFractionRing.injective _ _)
      (hHz.trans (map_zero _).symm))
  let S := surfaceSeeds embed p value A F
  have hz : ∀ g ∈ S, T.eval (value g) = 0 := by
    intro g hg
    have hV := (Finset.mem_filter.mp hg).2
    rw [Polynomial.eval_map,eval₂_collectValue]
    exact (eval_same_of_seed_free H haH hbH (value g)
      (coordinates (embed g) ((embed g)^p))).symm.trans hV
  have hsubset : S.image value ⊆ T.roots.toFinset := by
    intro q hq
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hq
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots ht).mpr (hz g hg))
  calc
    S.card = (S.image value).card :=
      (Finset.card_image_of_injOn (fun g hg h hh => hinj (Finset.mem_filter.mp hg).1
        (Finset.mem_filter.mp hh).1)).symm
    _ ≤ T.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ _ := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _ |>.trans hdeg)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

