import ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
import ProximityPrize.SubmissionLower.KoalaRectSections

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unnecessarySeqFocus false

namespace KoalaRectTaylor
noncomputable section

open K1_14 (FX Equation)
open HighCore82258Upper_3 (JetRing ordinate seedVar)
open HighCore82258Upper_3_1 (velocity)
open MvPolynomial

/-- Affine coordinates in the order ordinate, velocity, and the two seeds. -/
def jetAxes : Option (Option (Fin 2)) ≃ Fin 4 where
  toFun
    | none => 1
    | some none => 0
    | some (some i) => i.succ.succ
  invFun := ![some none, none, some (some 0), some (some 1)]
  left_inv := by
    rintro (_ | _ | i)
    · rfl
    · rfl
    · fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private abbrev flatEq := (optionEquivLeft FX (Fin 2)).symm
private abbrev flatJet := (optionEquivLeft FX (Option (Fin 2))).symm

def jetToRect : JetRing ≃ₐ[FX] SplitCut.Rect.Ring FX :=
  ((Polynomial.mapAlgEquiv flatEq).trans flatJet).trans (renameEquiv FX jetAxes)

@[simp] theorem jetToRect_ordinate : jetToRect ordinate = MvPolynomial.X 0 := by
  change rename jetAxes (flatJet ((Polynomial.C Polynomial.X).map flatEq.toRingHom)) = MvPolynomial.X 0
  rw [Polynomial.map_C]
  change rename jetAxes (flatJet (Polynomial.C (flatEq Polynomial.X))) = _
  rw [optionEquivLeft_symm_X, optionEquivLeft_symm_C_X, rename_X] <;> rfl

@[simp] theorem jetToRect_velocity : jetToRect velocity = MvPolynomial.X 1 := by
  change rename jetAxes (flatJet (Polynomial.X.map flatEq.toRingHom)) = MvPolynomial.X 1
  rw [Polynomial.map_X, optionEquivLeft_symm_X, rename_X] <;> rfl

@[simp] theorem jetToRect_seedVar (i : Fin 2) :
    jetToRect (seedVar i) = MvPolynomial.X i.succ.succ := by
  change rename jetAxes (flatJet
    ((Polynomial.C (Polynomial.C (MvPolynomial.X i))).map flatEq.toRingHom)) = _
  rw [Polynomial.map_C]
  change rename jetAxes (flatJet (Polynomial.C (flatEq (Polynomial.C (MvPolynomial.X i))))) = _
  rw [optionEquivLeft_symm_C_X, optionEquivLeft_symm_C_X, rename_X] <;> rfl

@[simp] theorem jetToRect_scalar (a : FX) :
    jetToRect (algebraMap FX JetRing a) = MvPolynomial.C a :=
  jetToRect.commutes a

theorem jetToRect_C (f : Equation) :
    jetToRect (Polynomial.C f) =
      rename (fun i => jetAxes (some i)) (K1_14_6_1.flatten f) := by
  change rename jetAxes (flatJet ((Polynomial.C f).map flatEq.toRingHom)) = _
  rw [Polynomial.map_C]
  change rename jetAxes ((Polynomial.C (flatEq f)).aevalTower (rename some) (MvPolynomial.X none)) = _
  rw [Polynomial.aevalTower_C, rename_rename] <;> rfl

def seedExponent (m : Fin 4 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i.succ.succ)

private theorem coeff_flat {σ : Type} (p : Polynomial (MvPolynomial σ FX)) (m : Option σ →₀ ℕ) :
    ((optionEquivLeft FX σ).symm p).coeff m = (p.coeff (m none)).coeff m.some := by
  have h := optionEquivLeft_coeff_coeff FX ((optionEquivLeft FX σ).symm p) (m none) m.some
  rw [AlgEquiv.apply_symm_apply, Finsupp.optionElim_some] at h
  exact h.symm

theorem coeff_jetToRect (p : JetRing) (m : Fin 4 →₀ ℕ) :
    (jetToRect p).coeff m = ((p.coeff (m 1)).coeff (m 0)).coeff (seedExponent m) := by
  let n := Finsupp.equivMapDomain jetAxes.symm m
  have hm : Finsupp.mapDomain jetAxes n = m := by
    ext i
    simp [n, ← Finsupp.equivMapDomain_eq_mapDomain]
  have hy : n.some none = m 0 := by simp [n, jetAxes, Finsupp.some_apply]
  have hv : n none = m 1 := by simp [n, jetAxes]
  have hz : n.some.some = seedExponent m := by
    ext i
    simp [n, seedExponent, jetAxes, Finsupp.some_apply]
  calc
    _ = (flatJet (p.map flatEq.toRingHom)).coeff n := by
      change (rename jetAxes (flatJet (p.map flatEq.toRingHom))).coeff m = _
      rw [← hm, coeff_rename_mapDomain _ jetAxes.injective]
    _ = (flatEq (p.coeff (n none))).coeff n.some := by
      rw [coeff_flat, Polynomial.coeff_map]
      rfl
    _ = _ := by rw [coeff_flat, hy, hv, hz]

end
end KoalaRectTaylor

#print axioms KoalaRectTaylor.coeff_jetToRect
