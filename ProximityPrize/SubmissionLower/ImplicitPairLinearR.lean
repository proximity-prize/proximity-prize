import ProximityPrize.SubmissionLower.BV
import ProximityPrize.SubmissionLower.W6
import ProximityPrize.SubmissionLower.P5
import ProximityPrize.SubmissionLower.AY

namespace ProximityPrize.SubmissionLower.RCN374

open scoped Classical BigOperators
open ProximityPrize.SubmissionLower

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

variable {K : Type} [Field K]

/-- Put the original `R` coordinate (index 1) first, so a trivariate
polynomial is a polynomial in `R` with bivariate `(Y,Z)` coefficients. -/
def collectR3 :
    MvPolynomial (Fin 3) K ≃ₐ[K]
      Polynomial (MvPolynomial (Fin 2) K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 3) 1)).trans
    (MvPolynomial.finSuccEquiv K 2)

def yzPoint (v : Fin 3 → K) : Fin 2 → K :=
  ![v 0, v 2]

def remainingCoordinate : Fin 2 → Fin 3 :=
  ![0, 2]

@[simp] theorem collectR3_C (c : K) :
    collectR3 (MvPolynomial.C c : MvPolynomial (Fin 3) K) =
      Polynomial.C (MvPolynomial.C c) := by
  simp [collectR3, MvPolynomial.renameEquiv_apply,
    MvPolynomial.finSuccEquiv_apply]

@[simp] theorem collectR3_X_Y :
    collectR3 (K := K) (MvPolynomial.X (0 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 2)) := by
  rw [collectR3, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  rw [Equiv.swap_apply_left]
  simpa only [show (1 : Fin 3) = (0 : Fin 2).succ by decide] using
    (MvPolynomial.finSuccEquiv_X_succ (R := K) (j := (0 : Fin 2)))

@[simp] theorem collectR3_X_R :
    collectR3 (K := K) (MvPolynomial.X (1 : Fin 3)) = Polynomial.X := by
  rw [collectR3, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  rw [Equiv.swap_apply_right]
  exact MvPolynomial.finSuccEquiv_X_zero

@[simp] theorem collectR3_X_Z :
    collectR3 (K := K) (MvPolynomial.X (2 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 2)) := by
  rw [collectR3, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  have hswap : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  rw [hswap]
  simpa only [show (2 : Fin 3) = (1 : Fin 2).succ by decide] using
    (MvPolynomial.finSuccEquiv_X_succ (R := K) (j := (1 : Fin 2)))

theorem eval_collectR3 (F : MvPolynomial (Fin 3) K) (v : Fin 3 → K) :
    Polynomial.eval₂ (MvPolynomial.eval (yzPoint v)) (v 1)
        (collectR3 F) =
      MvPolynomial.eval v F := by
  let lhs : MvPolynomial (Fin 3) K →+* K :=
    (Polynomial.eval₂RingHom (MvPolynomial.eval (yzPoint v)) (v 1)).comp
      (collectR3 (K := K)).toRingHom
  have hhom : lhs = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, collectR3, MvPolynomial.finSuccEquiv_apply]
    · intro i
      fin_cases i <;> simp [lhs, yzPoint]
  exact RingHom.congr_fun hhom F

theorem collectR3_natDegree (F : MvPolynomial (Fin 3) K) :
    (collectR3 F).natDegree = F.degreeOf 1 := by
  rw [collectR3, AlgEquiv.trans_apply, MvPolynomial.natDegree_finSuccEquiv]
  simpa using MvPolynomial.degreeOf_rename_of_injective
    (p := F) (Equiv.swap (0 : Fin 3) 1).injective (1 : Fin 3)

theorem collectR3_coeff_degreeOf_le
    (F : MvPolynomial (Fin 3) K) (n : ℕ) (i : Fin 2) :
    MvPolynomial.degreeOf i ((collectR3 F).coeff n) ≤
      F.degreeOf (remainingCoordinate i) := by
  have hcoeff := MvPolynomial.degreeOf_coeff_finSuccEquiv
    (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) F) i n
  change MvPolynomial.degreeOf i ((collectR3 F).coeff n) ≤
    MvPolynomial.degreeOf i.succ
      (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) F) at hcoeff
  fin_cases i
  · have hrename := MvPolynomial.degreeOf_rename_of_injective
      (p := F) (Equiv.swap (0 : Fin 3) 1).injective (0 : Fin 3)
    exact hcoeff.trans_eq (by simpa [remainingCoordinate] using hrename)
  · have hrename := MvPolynomial.degreeOf_rename_of_injective
      (p := F) (Equiv.swap (0 : Fin 3) 1).injective (2 : Fin 3)
    rw [show (Equiv.swap (0 : Fin 3) 1) 2 = 2 by decide] at hrename
    exact hcoeff.trans_eq (by simpa [remainingCoordinate] using hrename)

theorem degreeOf_det_le_columnCaps
    (N : ℕ) (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin 2) K))
    (i : Fin 2) (columnCap : Fin N → ℕ)
    (hM : ∀ r c, (M r c).degreeOf i ≤ columnCap c) :
    M.det.degreeOf i ≤ ∑ c, columnCap c := by
  classical
  rw [Matrix.det_apply']
  apply (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans
  apply Finset.sup_le_iff.mpr
  intro σ _
  have hprod : (∏ c, M (σ c) c).degreeOf i ≤ ∑ c, columnCap c := by
    calc
      _ ≤ ∑ c : Fin N, (M (σ c) c).degreeOf i :=
        MvPolynomial.degreeOf_prod_le i Finset.univ _
      _ ≤ ∑ c : Fin N, columnCap c :=
        Finset.sum_le_sum fun c _ => hM (σ c) c
  have hsign :
      (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) K)).degreeOf i ≤ 0 := by
    simpa only [map_intCast] using
      (MvPolynomial.degreeOf_C (((Equiv.Perm.sign σ : ℤ) : K)) i).le
  exact (MvPolynomial.degreeOf_mul_le i _ _).trans
    ((Nat.add_le_add hsign hprod).trans_eq (zero_add _))

/-- The fixed-degree resultant eliminating `R`. -/
def eliminateR3 (G B : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 2) K :=
  Polynomial.resultant (collectR3 G) (collectR3 B)
    (G.degreeOf 1) (B.degreeOf 1)

theorem eliminateR3_degreeOf_le
    (G B : MvPolynomial (Fin 3) K) (i : Fin 2) :
    (eliminateR3 G B).degreeOf i ≤
      G.degreeOf 1 * B.degreeOf (remainingCoordinate i) +
        B.degreeOf 1 * G.degreeOf (remainingCoordinate i) := by
  let m := G.degreeOf 1
  let n := B.degreeOf 1
  let M := Polynomial.sylvester (collectR3 G) (collectR3 B) m n
  let columnCap : Fin (m + n) → ℕ := fun c =>
    c.addCases (fun _ => B.degreeOf (remainingCoordinate i))
      (fun _ => G.degreeOf (remainingCoordinate i))
  have hentry : ∀ r c, (M r c).degreeOf i ≤ columnCap c := by
    intro r c
    induction c using Fin.addCases with
    | «left» c =>
        simp only [M, columnCap, Polynomial.sylvester, Matrix.of_apply,
          Fin.addCases_left]
        split_ifs
        · exact collectR3_coeff_degreeOf_le B _ i
        · simp
    | «right» c =>
        simp only [M, columnCap, Polynomial.sylvester, Matrix.of_apply,
          Fin.addCases_right]
        split_ifs
        · exact collectR3_coeff_degreeOf_le G _ i
        · simp
  have hdet := degreeOf_det_le_columnCaps (K := K) (m + n) M i columnCap hentry
  have hsum : (∑ c, columnCap c) =
      m * B.degreeOf (remainingCoordinate i) +
        n * G.degreeOf (remainingCoordinate i) := by
    rw [show (∑ c, columnCap c) =
      (∑ _c : Fin m, B.degreeOf (remainingCoordinate i)) +
        ∑ _c : Fin n, G.degreeOf (remainingCoordinate i) by
          simpa [columnCap] using Fin.sum_univ_add columnCap]
    simp
  change M.det.degreeOf i ≤ _
  rw [hsum] at hdet
  exact hdet

theorem eliminateR3_nonzero
    (G B : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hR : G.degreeOf 1 = 1) (hproper : ¬ G ∣ B) :
    eliminateR3 G B ≠ 0 := by
  have hGi : Irreducible (collectR3 G) :=
    (MulEquiv.irreducible_iff (collectR3 (K := K))).mpr hG
  have hnot : ¬ collectR3 G ∣ collectR3 B := by
    intro hd
    apply hproper
    obtain ⟨U, hU⟩ := hd
    refine ⟨(collectR3 (K := K)).symm U, ?_⟩
    apply (collectR3 (K := K)).injective
    simpa only [map_mul, AlgEquiv.apply_symm_apply] using hU
  unfold eliminateR3
  rw [← collectR3_natDegree G, ← collectR3_natDegree B]
  exact RCN290.irreducible_resultant_nonzero (collectR3 G) (collectR3 B)
    hGi (by rw [collectR3_natDegree, hR]; decide) hnot

theorem eliminateR3_eval_zero_of_common_root
    (G B : MvPolynomial (Fin 3) K) (v : Fin 3 → K)
    (hR : G.degreeOf 1 = 1)
    (hG : MvPolynomial.eval v G = 0)
    (hB : MvPolynomial.eval v B = 0) :
    MvPolynomial.eval (yzPoint v) (eliminateR3 G B) = 0 := by
  rw [eliminateR3, ← Polynomial.resultant_map_map]
  apply resultant_fixed_degree_eq_zero_of_common_root (t := v 1)
  · exact Polynomial.natDegree_map_le.trans_eq (collectR3_natDegree G)
  · exact Polynomial.natDegree_map_le.trans_eq (collectR3_natDegree B)
  · rw [hR]
    omega
  · rw [Polynomial.eval_map]
    rw [eval_collectR3]
    exact hG
  · rw [Polynomial.eval_map]
    rw [eval_collectR3]
    exact hB

/-- The bivariate polynomial obtained from an `R`-free trivariate polynomial. -/
def dropR (A : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 2) K :=
  (collectR3 A).coeff 0

theorem collectR3_eq_C_dropR
    (A : MvPolynomial (Fin 3) K) (hAR : A.degreeOf 1 = 0) :
    collectR3 A = Polynomial.C (dropR A) := by
  exact Polynomial.eq_C_of_natDegree_eq_zero (by rw [collectR3_natDegree, hAR])

theorem dropR_degreeOf_le
    (A : MvPolynomial (Fin 3) K) (i : Fin 2) :
    (dropR A).degreeOf i ≤ A.degreeOf (remainingCoordinate i) :=
  collectR3_coeff_degreeOf_le A 0 i

def zyPair (v : Fin 3 → K) : K × K :=
  (v 2, v 0)

theorem eval_bivariateEquiv
    (F : MvPolynomial (Fin 2) K) (z y : K) :
    ((RCN011.bivariateEquiv K F).map (Polynomial.evalRingHom z)).eval y =
      MvPolynomial.eval ![y, z] F := by
  let lhs : MvPolynomial (Fin 2) K →+* K :=
    (Polynomial.evalRingHom y).comp
      ((Polynomial.mapRingHom (Polynomial.evalRingHom z)).comp
        (RCN011.bivariateEquiv K).toRingEquiv.toRingHom)
  have hhom : lhs = MvPolynomial.eval ![y, z] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs]
    · intro i
      fin_cases i <;> simp [lhs]
  exact RingHom.congr_fun hhom F

theorem dropR_eval
    (A : MvPolynomial (Fin 3) K) (hAR : A.degreeOf 1 = 0)
    (v : Fin 3 → K) :
    MvPolynomial.eval (yzPoint v) (dropR A) = MvPolynomial.eval v A := by
  have h := eval_collectR3 A v
  rw [collectR3_eq_C_dropR A hAR] at h
  simpa using h

/-- Characteristic-free common-point bound after one linear `R` elimination.
The hypotheses `hAproperE` and `hAYpos` are exactly the two obligations that
must be transported from a regular `(G,A)` component. -/
theorem selectedPoint_zyPair_injective
    {k Ω : Type} [Field k] [Field Ω]
    (φ : Polynomial k →+* Ω) (selected : k → Polynomial k) :
    Function.Injective
      (fun γ => zyPair (RCN238.selectedPoint φ selected γ)) := by
  intro γ η h
  apply (φ.comp Polynomial.C).injective
  have hz := congrArg Prod.fst h
  simpa only [zyPair, RCN238.selectedPoint_seed] using hz

/-- Direct specialization to the selected-point fibers used by the IRS proof. -/
theorem collectR3_pderiv_R (P : MvPolynomial (Fin 3) K) :
    collectR3 (MvPolynomial.pderiv 1 P) = (collectR3 P).derivative := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [collectR3, MvPolynomial.renameEquiv_apply,
        MvPolynomial.finSuccEquiv_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i <;>
        simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
          Pi.single_apply, map_add, map_mul, hP,
          Polynomial.derivative_mul] <;> ring

theorem mapped_linear_resultant_ne_zero
    {C L : Type} [CommRing C] [Field L]
    (ψ : C →+* L) (g h : Polynomial C) (r : L)
    (hgdeg : g.natDegree ≤ 1)
    (hlead : ψ (g.coeff 1) ≠ 0)
    (hgroot : (g.map ψ).eval r = 0)
    (hhroot : (h.map ψ).eval r ≠ 0) :
    ψ (Polynomial.resultant g h 1 h.natDegree) ≠ 0 := by
  let lead : L := ψ (g.coeff 1)
  have hmapdeg : (g.map ψ).natDegree ≤ 1 :=
    Polynomial.natDegree_map_le.trans hgdeg
  have hshape := Polynomial.eq_X_add_C_of_natDegree_le_one hmapdeg
  have hzero : lead * r + ψ (g.coeff 0) = 0 := by
    rw [hshape] at hgroot
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.coeff_map, lead] using hgroot
  have hconst : ψ (g.coeff 0) = -lead * r := by
    linear_combination hzero
  have hlinear : g.map ψ = Polynomial.C lead *
      (Polynomial.X - Polynomial.C r) := by
    rw [hshape]
    simp only [Polynomial.coeff_map, lead, hconst]
    simp only [map_neg, map_mul]
    ring
  rw [← Polynomial.resultant_map_map]
  rw [hlinear, Polynomial.resultant_C_mul_left,
    Polynomial.resultant_X_sub_C_left]
  · exact mul_ne_zero (pow_ne_zero _ hlead) hhroot
  · exact Polynomial.natDegree_map_le

/-- Divisibility by an R-free factor is an identity certificate at every
regular point of the R-linear equation. -/
theorem linearR_factor_dvd_resultant_forces_zero
    (f : MvPolynomial (Fin 2) K)
    (G B : MvPolynomial (Fin 3) K) (v : Fin 3 → K)
    (hGR : G.degreeOf 1 = 1)
    (hdiv : f ∣ eliminateR3 G B)
    (hfzero : MvPolynomial.eval (yzPoint v) f = 0)
    (hGzero : MvPolynomial.eval v G = 0)
    (hGreg : MvPolynomial.eval v (MvPolynomial.pderiv 1 G) ≠ 0) :
    MvPolynomial.eval v B = 0 := by
  let ψ : MvPolynomial (Fin 2) K →+* K := MvPolynomial.eval (yzPoint v)
  let r := v 1
  have hgdeg : (collectR3 G).natDegree ≤ 1 := by
    rw [collectR3_natDegree, hGR]
  have hlead : ψ ((collectR3 G).coeff 1) ≠ 0 := by
    intro hz
    apply hGreg
    rw [← eval_collectR3 (MvPolynomial.pderiv 1 G) v]
    rw [collectR3_pderiv_R]
    have hshape := Polynomial.eq_X_add_C_of_natDegree_le_one hgdeg
    rw [hshape]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X, mul_one, zero_mul,
      add_zero, Polynomial.eval₂_C]
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_C, ψ] using hz
  have hgroot : ((collectR3 G).map ψ).eval r = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact (eval_collectR3 G v).trans hGzero
  by_contra hBne
  have hhroot : ((collectR3 B).map ψ).eval r ≠ 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    change Polynomial.eval₂ (MvPolynomial.eval (yzPoint v)) (v 1)
      (collectR3 B) ≠ 0
    rw [eval_collectR3]
    exact hBne
  have hresne := mapped_linear_resultant_ne_zero ψ
    (collectR3 G) (collectR3 B) r hgdeg hlead hgroot hhroot
  obtain ⟨q, hq⟩ := hdiv
  apply hresne
  have hEzero : ψ (eliminateR3 G B) = 0 := by
    rw [hq, map_mul, hfzero, zero_mul]
  simpa only [eliminateR3, hGR, collectR3_natDegree] using hEzero

theorem linearR_bivariate_factor_fiber_card_le
    {Seed : Type} [DecidableEq Seed]
    (seeds : Finset Seed) (v : Seed → Fin 3 → K)
    (hinjective : Function.Injective (fun s => zyPair (v s)))
    (f : MvPolynomial (Fin 2) K) (G B : MvPolynomial (Fin 3) K)
    (hf : Irreducible f) (hfY : 0 < f.degreeOf 0)
    (hGR : G.degreeOf 1 = 1)
    (hproper : ¬ f ∣ eliminateR3 G B)
    (hfroot : ∀ s ∈ seeds, MvPolynomial.eval (yzPoint (v s)) f = 0)
    (hGroot : ∀ s ∈ seeds, MvPolynomial.eval (v s) G = 0)
    (hBroot : ∀ s ∈ seeds, MvPolynomial.eval (v s) B = 0) :
    seeds.card ≤
      f.degreeOf 0 * (B.degreeOf 2 + B.degreeOf 1 * G.degreeOf 2) +
        f.degreeOf 1 * (B.degreeOf 0 + B.degreeOf 1 * G.degreeOf 0) := by
  classical
  let P := RCN011.bivariateEquiv K f
  let Q := RCN011.bivariateEquiv K (eliminateR3 G B)
  let point : Seed → K × K := fun s => zyPair (v s)
  let points := seeds.image point
  have hPirr : Irreducible P :=
    (MulEquiv.irreducible_iff (RCN011.bivariateEquiv K)).mpr hf
  have hPpos : 0 < P.natDegree := by
    change 0 < (RCN011.bivariateEquiv K f).natDegree
    rwa [RCN009.bivariateEquiv_natDegree]
  have hproper' : ¬ P ∣ Q := by
    intro hd
    apply hproper
    obtain ⟨U, hU⟩ := hd
    refine ⟨(RCN011.bivariateEquiv K).symm U, ?_⟩
    apply (RCN011.bivariateEquiv K).injective
    simpa only [map_mul, AlgEquiv.apply_symm_apply, P, Q] using hU
  have hroots : ∀ q ∈ points,
      (P.map (Polynomial.evalRingHom q.1)).eval q.2 = 0 ∧
        (Q.map (Polynomial.evalRingHom q.1)).eval q.2 = 0 := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    constructor
    · change ((RCN011.bivariateEquiv K f).map
        (Polynomial.evalRingHom (point s).1)).eval (point s).2 = 0
      rw [eval_bivariateEquiv]
      exact hfroot s hs
    · change ((RCN011.bivariateEquiv K (eliminateR3 G B)).map
        (Polynomial.evalRingHom (point s).1)).eval (point s).2 = 0
      rw [eval_bivariateEquiv]
      exact eliminateR3_eval_zero_of_common_root G B (v s) hGR
        (hGroot s hs) (hBroot s hs)
  have hcount := RCN362.irreducible_common_points_card_le_bidegree_bound
    P Q points hPirr hPpos hproper' hroots
  have hcard : points.card = seeds.card :=
    Finset.card_image_of_injective _ hinjective
  rw [hcard] at hcount
  have hQY : Q.natDegree ≤
      B.degreeOf 0 + B.degreeOf 1 * G.degreeOf 0 := by
    change (RCN011.bivariateEquiv K (eliminateR3 G B)).natDegree ≤ _
    rw [RCN009.bivariateEquiv_natDegree]
    simpa [remainingCoordinate, hGR] using eliminateR3_degreeOf_le G B 0
  have hQZ : Polynomial.Bivariate.degreeX Q ≤
      B.degreeOf 2 + B.degreeOf 1 * G.degreeOf 2 := by
    exact (RCN009.bivariateEquiv_degreeX_le K (eliminateR3 G B)).trans
      (by simpa [remainingCoordinate, hGR] using
        eliminateR3_degreeOf_le G B 1)
  have hPZ : Polynomial.Bivariate.degreeX P ≤ f.degreeOf 1 :=
    RCN009.bivariateEquiv_degreeX_le K f
  have hbound := Nat.add_le_add
    (Nat.mul_le_mul hQY hPZ)
    (Nat.mul_le_mul (RCN009.bivariateEquiv_natDegree K f).le hQZ)
  exact hcount.trans (hbound.trans_eq (by ring))

/-- Both sharp-incidence branches for one positive-Y factor. -/
theorem linearR_bivariate_factor_seed_incidence
    {k ι : Type} [Field k] [DecidableEq k] [DecidableEq ι]
    (f : MvPolynomial (Fin 2) K) (G : MvPolynomial (Fin 3) K)
    (hf : Irreducible f) (hfY : 0 < f.degreeOf 0)
    (hGR : G.degreeOf 1 = 1)
    (B : ι → MvPolynomial (Fin 3) K) (bY bR bZ : ℕ)
    (v : k → Fin 3 → K)
    (hinjective : Function.Injective (fun γ => zyPair (v γ)))
    (selected : k → Polynomial k) (seeds : Finset k)
    (nodes : Finset ι) (x u₀ u₁ : ι → k)
    (hinj : Set.InjOn x nodes)
    (w a e : ℕ) (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ γ ∈ seeds, (selected γ).natDegree ≤ w)
    (hfroot : ∀ γ ∈ seeds, MvPolynomial.eval (yzPoint (v γ)) f = 0)
    (hGroot : ∀ γ ∈ seeds, MvPolynomial.eval (v γ) G = 0)
    (hGreg : ∀ γ ∈ seeds,
      MvPolynomial.eval (v γ) (MvPolynomial.pderiv 1 G) ≠ 0)
    (hagreement : ∀ γ ∈ seeds,
      a ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hBcaps : ∀ i ∈ nodes,
      (B i).degreeOf 0 ≤ bY ∧ (B i).degreeOf 1 ≤ bR ∧
        (B i).degreeOf 2 ≤ bZ)
    (hBzero : ∀ γ ∈ seeds, ∀ i ∈ nodes,
      MvPolynomial.eval (v γ) (B i) = 0 ↔
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)
    (hnoPencil : RCN238.NoLargeSelectedPencil selected seeds w e) :
    seeds.card * (a - w) ≤
      (nodes.card - w) *
          (f.degreeOf 0 * (bZ + bR * G.degreeOf 2) +
            f.degreeOf 1 * (bY + bR * G.degreeOf 0)) +
        (e + 1) * (a - w) * f.degreeOf 0 := by
  classical
  let relation : k → ι → Prop := fun γ i =>
    (selected γ).eval (x i) = u₀ i + γ * u₁ i
  let identities := nodes.filter fun i => f ∣ eliminateR3 G (B i)
  let cost := f.degreeOf 0 * (bZ + bR * G.degreeOf 2) +
    f.degreeOf 1 * (bY + bR * G.degreeOf 0)
  have hidentities : identities ⊆ nodes := Finset.filter_subset _ _
  by_cases hsmall : identities.card ≤ w
  · have hfiber : ∀ i ∈ nodes \ identities,
        (seeds.filter (fun γ => relation γ i)).card ≤ cost := by
      intro i hi
      obtain ⟨hinodes, hnotIdentity⟩ := Finset.mem_sdiff.mp hi
      have hproper : ¬ f ∣ eliminateR3 G (B i) := by
        intro hdiv
        exact hnotIdentity (Finset.mem_filter.mpr ⟨hinodes, hdiv⟩)
      let fiber := seeds.filter (fun γ => relation γ i)
      have hraw := linearR_bivariate_factor_fiber_card_le
        fiber v hinjective f G (B i) hf hfY hGR hproper
        (by
          intro γ hγ
          exact hfroot γ (Finset.mem_filter.mp hγ).1)
        (by
          intro γ hγ
          exact hGroot γ (Finset.mem_filter.mp hγ).1)
        (by
          intro γ hγ
          obtain ⟨hseed, hrel⟩ := Finset.mem_filter.mp hγ
          exact (hBzero γ hseed i hinodes).mpr hrel)
      exact hraw.trans (by
        dsimp only [cost]
        gcongr
        · exact (hBcaps i hinodes).2.2
        · exact (hBcaps i hinodes).2.1
        · exact (hBcaps i hinodes).1
        · exact (hBcaps i hinodes).2.1)
    have hcount := RCN173.sharp_incidence_bound relation seeds nodes identities
      a w cost hidentities hsmall hwa han hagreement hfiber
    exact hcount.trans (Nat.le_add_right _ _)
  · have hlarge : w < identities.card := Nat.lt_of_not_ge hsmall
    have hvalues : ∀ t : {γ : k // γ ∈ seeds}, ∀ i, i ∈ identities →
        (selected t.1).eval (x i) = u₀ i + t.1 * u₁ i := by
      intro t i hi
      obtain ⟨hinodes, hdiv⟩ := Finset.mem_filter.mp hi
      apply (hBzero t.1 t.2 i hinodes).mp
      exact linearR_factor_dvd_resultant_forces_zero f G (B i) (v t.1)
        hGR hdiv (hfroot t.1 t.2) (hGroot t.1 t.2) (hGreg t.1 t.2)
    obtain ⟨P₀, P₁, hP₀, hP₁, hpencil⟩ :=
      RCN147.exists_affine_pencil_of_identity_nodes identities x u₀ u₁ w
        hlarge (hinj.mono hidentities) (fun t : {γ : k // γ ∈ seeds} => t.1)
        (fun t => selected t.1) (fun t => hdegree t.1 t.2) hvalues
    have hfilter : seeds.filter
        (fun γ => selected γ = P₀ + Polynomial.C γ * P₁) = seeds :=
      Finset.filter_eq_self.mpr fun γ hγ => hpencil ⟨γ, hγ⟩
    have hseedCard : seeds.card ≤ e + 1 := by
      have hp := hnoPencil P₀ P₁ hP₀ hP₁
      have hp' :
          (seeds.filter
            (fun γ => selected γ = P₀ + Polynomial.C γ * P₁)).card ≤ e + 1 := by
        convert hp using 1
        apply congrArg Finset.card
        ext γ
        simp
      calc
        seeds.card =
            (seeds.filter
              (fun γ => selected γ = P₀ + Polynomial.C γ * P₁)).card :=
          congrArg Finset.card hfilter.symm
        _ ≤ e + 1 := hp'
    have hcharge : seeds.card * (a - w) ≤
        (e + 1) * (a - w) * f.degreeOf 0 := by
      calc
        _ ≤ (e + 1) * (a - w) := Nat.mul_le_mul_right _ hseedCard
        _ ≤ (e + 1) * (a - w) * f.degreeOf 0 := by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left ((e + 1) * (a - w))
              (Nat.succ_le_iff.mpr hfY)
    exact hcharge.trans (Nat.le_add_left _ _)

theorem bivariate_factor_pderiv_regular_at_zero
    (i : Fin 2) (ψ : MvPolynomial (Fin 2) K →+* K)
    (A f : MvPolynomial (Fin 2) K)
    (hdiv : f ∣ A) (hfzero : ψ f = 0)
    (hregular : ψ (MvPolynomial.pderiv i A) ≠ 0) :
    ψ (MvPolynomial.pderiv i f) ≠ 0 := by
  intro hz
  obtain ⟨q, rfl⟩ := hdiv
  apply hregular
  rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
    hz, hfzero, zero_mul, zero_mul, zero_add]

theorem factor_pderiv_regular_at_zero_generic
    {σ : Type} (i : σ) (ψ : MvPolynomial σ K →+* K)
    (A f : MvPolynomial σ K)
    (hdiv : f ∣ A) (hfzero : ψ f = 0)
    (hregular : ψ (MvPolynomial.pderiv i A) ≠ 0) :
    ψ (MvPolynomial.pderiv i f) ≠ 0 := by
  intro hz
  obtain ⟨q, rfl⟩ := hdiv
  apply hregular
  rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
    hz, hfzero, zero_mul, zero_mul, zero_add]

/-- End-to-end factor-group replacement for the `hsingle` use of
`proper_cut_seed_bound` in `BW`: normalized positive-Y factors of the R-free
base equation cover the seeds, each factor pays both incidence branches, and
the factor degrees are summed exactly once.  No mixed-R characteristic gate
or component assignment appears. -/
theorem linearR_normalized_factor_seed_incidence
    {k ι : Type} [Field k] [DecidableEq k] [DecidableEq ι]
    (A : MvPolynomial (Fin 2) K) (G : MvPolynomial (Fin 3) K)
    (hA : A ≠ 0) (hGR : G.degreeOf 1 = 1)
    (B : ι → MvPolynomial (Fin 3) K) (bY bR bZ : ℕ)
    (v : k → Fin 3 → K)
    (hinjective : Function.Injective (fun γ => zyPair (v γ)))
    (selected : k → Polynomial k) (seeds : Finset k)
    (nodes : Finset ι) (x u₀ u₁ : ι → k)
    (hinj : Set.InjOn x nodes)
    (w a e : ℕ) (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ γ ∈ seeds, (selected γ).natDegree ≤ w)
    (hAroot : ∀ γ ∈ seeds,
      MvPolynomial.eval (yzPoint (v γ)) A = 0)
    (hAregular : ∀ γ ∈ seeds,
      MvPolynomial.eval (yzPoint (v γ)) (MvPolynomial.pderiv 0 A) ≠ 0)
    (hGroot : ∀ γ ∈ seeds, MvPolynomial.eval (v γ) G = 0)
    (hGreg : ∀ γ ∈ seeds,
      MvPolynomial.eval (v γ) (MvPolynomial.pderiv 1 G) ≠ 0)
    (hagreement : ∀ γ ∈ seeds,
      a ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hBcaps : ∀ i ∈ nodes,
      (B i).degreeOf 0 ≤ bY ∧ (B i).degreeOf 1 ≤ bR ∧
        (B i).degreeOf 2 ≤ bZ)
    (hBzero : ∀ γ ∈ seeds, ∀ i ∈ nodes,
      MvPolynomial.eval (v γ) (B i) = 0 ↔
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)
    (hnoPencil : RCN238.NoLargeSelectedPencil selected seeds w e) :
    seeds.card * (a - w) ≤
      (nodes.card - w) *
          (A.degreeOf 0 * (bZ + bR * G.degreeOf 2) +
            A.degreeOf 1 * (bY + bR * G.degreeOf 0)) +
        (e + 1) * (a - w) * A.degreeOf 0 := by
  classical
  let factors := (RCN137.normalizedFactorSet A).filter
    (fun f => 0 < f.degreeOf 0)
  let factorSeeds := fun f : MvPolynomial (Fin 2) K =>
    seeds.filter (fun γ => MvPolynomial.eval (yzPoint (v γ)) f = 0)
  have hcover : seeds ⊆ factors.biUnion factorSeeds := by
    intro γ hγ
    obtain ⟨f, hf, hfzero⟩ := RCN137.exists_normalizedFactorSet_zero
      (MvPolynomial.eval (yzPoint (v γ))) A hA (hAroot γ hγ)
    have hfreg := bivariate_factor_pderiv_regular_at_zero 0
      (MvPolynomial.eval (yzPoint (v γ))) A f
      (RCN137.normalizedFactorSet_spec A f hf).2 hfzero (hAregular γ hγ)
    have hfY : 0 < f.degreeOf 0 := by
      by_contra hn
      apply hfreg
      rw [RCN267.pderiv_zero_of_degree_zero 0 f
        (Nat.eq_zero_of_not_pos hn), map_zero]
    exact Finset.mem_biUnion.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, hfY⟩,
      Finset.mem_filter.mpr ⟨hγ, hfzero⟩⟩
  have hcard : seeds.card ≤ ∑ f ∈ factors, (factorSeeds f).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hone (f : MvPolynomial (Fin 2) K) (hf : f ∈ factors) :
      (factorSeeds f).card * (a - w) ≤
        (nodes.card - w) *
            (f.degreeOf 0 * (bZ + bR * G.degreeOf 2) +
              f.degreeOf 1 * (bY + bR * G.degreeOf 0)) +
          (e + 1) * (a - w) * f.degreeOf 0 := by
    have hf0 := (Finset.mem_filter.mp hf).1
    have hfY := (Finset.mem_filter.mp hf).2
    have hsub : factorSeeds f ⊆ seeds := Finset.filter_subset _ _
    have hnoSub : RCN238.NoLargeSelectedPencil
        selected (factorSeeds f) w e :=
      RCN243.noLargeSelectedPencil_mono selected seeds (factorSeeds f)
        w e hsub hnoPencil
    apply linearR_bivariate_factor_seed_incidence
      f G (RCN137.normalizedFactorSet_spec A f hf0).1 hfY hGR
      B bY bR bZ v hinjective selected (factorSeeds f)
      nodes x u₀ u₁ hinj w a e hwa han
      (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => hGroot γ (hsub hγ))
      (fun γ hγ => hGreg γ (hsub hγ))
      (fun γ hγ => hagreement γ (hsub hγ)) hBcaps
      (fun γ hγ i hi => hBzero γ (hsub hγ) i hi)
      hnoSub
  have hsumY : (∑ f ∈ factors, f.degreeOf 0) ≤ A.degreeOf 0 :=
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
      (RCN137.normalizedFactorSet_degree_budget A hA 0)
  have hsumZ : (∑ f ∈ factors, f.degreeOf 1) ≤ A.degreeOf 1 :=
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
      (RCN137.normalizedFactorSet_degree_budget A hA 1)
  let eY := bY + bR * G.degreeOf 0
  let eZ := bZ + bR * G.degreeOf 2
  have hsum :
      (∑ f ∈ factors,
        ((nodes.card - w) * (f.degreeOf 0 * eZ + f.degreeOf 1 * eY) +
          (e + 1) * (a - w) * f.degreeOf 0)) =
        (nodes.card - w) *
            ((∑ f ∈ factors, f.degreeOf 0) * eZ +
              (∑ f ∈ factors, f.degreeOf 1) * eY) +
          (e + 1) * (a - w) * (∑ f ∈ factors, f.degreeOf 0) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_mul]
  calc
    seeds.card * (a - w) ≤
        (∑ f ∈ factors, (factorSeeds f).card) * (a - w) :=
      Nat.mul_le_mul_right (a - w) hcard
    _ = ∑ f ∈ factors, (factorSeeds f).card * (a - w) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ f ∈ factors,
        ((nodes.card - w) * (f.degreeOf 0 * eZ + f.degreeOf 1 * eY) +
          (e + 1) * (a - w) * f.degreeOf 0) := by
      apply Finset.sum_le_sum
      intro f hf
      simpa only [eY, eZ] using hone f hf
    _ = (nodes.card - w) *
          ((∑ f ∈ factors, f.degreeOf 0) * eZ +
            (∑ f ∈ factors, f.degreeOf 1) * eY) +
        (e + 1) * (a - w) * (∑ f ∈ factors, f.degreeOf 0) := hsum
    _ ≤ (nodes.card - w) *
          (A.degreeOf 0 * eZ + A.degreeOf 1 * eY) +
        (e + 1) * (a - w) * A.degreeOf 0 := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left (nodes.card - w)
          (Nat.add_le_add (Nat.mul_le_mul_right eZ hsumY)
            (Nat.mul_le_mul_right eY hsumZ)))
        (Nat.mul_le_mul_left ((e + 1) * (a - w)) hsumY)
    _ = (nodes.card - w) *
          (A.degreeOf 0 * (bZ + bR * G.degreeOf 2) +
            A.degreeOf 1 * (bY + bR * G.degreeOf 0)) +
        (e + 1) * (a - w) * A.degreeOf 0 := by rfl

/-- Source-shaped replacement for the `hsingle` call in `BW`.  Relative to
the old call, the mixed-R characteristic gate is absent; `hAregular` is the
new input that makes the positive-Y normalized factors cover every seed. -/
theorem implicit_pair_surface_factor_seed_bound_linearR
    {k Ω ι : Type} [Field k] [Field Ω] [IsAlgClosed Ω]
    [DecidableEq k] [DecidableEq ι]
    (φ : Polynomial k →+* Ω) (hφ : Function.Injective φ)
    (A G : MvPolynomial (Fin 4) k)
    (hAne : A ≠ 0) (hAR : A.degreeOf 2 = 0)
    (g : MvPolynomial (Fin 3) Ω)
    (hgi : Irreducible g) (hdiv : g ∣ RCN136.surfaceMap φ G)
    (hgRle : g.degreeOf 1 ≤ 1)
    (selected : k → Polynomial k) (seeds : Finset k)
    (nodes : Finset ι) (x u₀ u₁ : ι → k)
    (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a)
    (han : a ≤ nodes.card)
    (hdegree : ∀ γ ∈ seeds, (selected γ).natDegree ≤ w)
    (hsolutionG : ∀ γ ∈ seeds,
      RCN319.specialization k (selected γ) γ G = 0)
    (hregularG : ∀ γ ∈ seeds,
      MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
        (RCN231.polynomialPoint (φ.comp Polynomial.C)
          (selected γ) γ (φ Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0)
    (hgpoint : ∀ γ ∈ seeds,
      MvPolynomial.eval (RCN238.selectedPoint φ selected γ) g = 0)
    (hApoint : ∀ γ ∈ seeds,
      MvPolynomial.eval (RCN238.selectedPoint φ selected γ)
        (RCN136.surfaceMap φ A) = 0)
    (hAregular : ∀ γ ∈ seeds,
      MvPolynomial.eval
        (yzPoint (RCN238.selectedPoint φ selected γ))
        (MvPolynomial.pderiv 0 (dropR (RCN136.surfaceMap φ A))) ≠ 0)
    (hagreement : ∀ γ ∈ seeds,
      a ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : RCN238.NoLargeSelectedPencil selected seeds w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (RCN238.agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)).degreeOf j ≤
        cap j) :
    seeds.card * (a - w) ≤
      (nodes.card - w) *
          (∑ j : Fin 3, cap j *
            RCN068.capAt (RCN170.geometricPairCost A g) j) +
        (e + 1) * (a - w) *
          RCN068.capAt (RCN170.geometricPairCost A g) 2 := by
  classical
  let A3 := RCN136.surfaceMap φ A
  let A2 := dropR A3
  let point := RCN238.selectedPoint φ selected
  let agreement := fun i : ι =>
    RCN238.agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)
  have hA3R : A3.degreeOf 1 = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (RCN136.surfaceMap_degreeOf_le φ A 1).trans_eq hAR
  have hA3ne : A3 ≠ 0 :=
    RCN136.surfaceMap_ne_zero φ hφ A hAne
  have hA2ne : A2 ≠ 0 := by
    intro hz
    apply hA3ne
    apply (collectR3 (K := Ω)).injective
    change dropR A3 = 0 at hz
    rw [collectR3_eq_C_dropR A3 hA3R, hz, map_zero]
    simp
  have hglobalDerivative : ∀ γ ∈ seeds,
      MvPolynomial.eval (point γ)
        (MvPolynomial.pderiv 1 (RCN136.surfaceMap φ G)) ≠ 0 := by
    intro γ hγ
    rw [RCN267.surfaceMap_pderiv_R]
    rw [RCN243.selectedPoint_evaluation]
    exact hregularG γ hγ
  have hgRegular : ∀ γ ∈ seeds,
      MvPolynomial.eval (point γ) (MvPolynomial.pderiv 1 g) ≠ 0 := by
    intro γ hγ
    exact factor_pderiv_regular_at_zero_generic
      (K := Ω) 1 (MvPolynomial.eval (point γ))
      (RCN136.surfaceMap φ G) g hdiv (hgpoint γ hγ)
      (hglobalDerivative γ hγ)
  by_cases hempty : seeds = ∅
  · simp [hempty]
  have hnonempty : seeds.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨γ₀, hγ₀⟩ := hnonempty
  have hgRpos : 0 < g.degreeOf 1 := by
    by_contra hn
    apply hgRegular γ₀ hγ₀
    rw [RCN267.pderiv_zero_of_degree_zero 1 g
      (Nat.eq_zero_of_not_pos hn), map_zero]
  have hgR : g.degreeOf 1 = 1 := Nat.le_antisymm hgRle hgRpos
  have hA2root : ∀ γ ∈ seeds,
      MvPolynomial.eval (yzPoint (point γ)) A2 = 0 := by
    intro γ hγ
    rw [dropR_eval A3 hA3R]
    exact hApoint γ hγ
  have hBzero : ∀ γ ∈ seeds, ∀ i ∈ nodes,
      MvPolynomial.eval (point γ) (agreement i) = 0 ↔
        (selected γ).eval (x i) = u₀ i + γ * u₁ i := by
    intro γ hγ i hi
    exact RCN238.selected_agreement_zero_iff φ G selected p w hchar γ
      (hdegree γ hγ) (hsolutionG γ hγ) (hregularG γ hγ)
      (x i) (u₀ i) (u₁ i)
  have hraw := linearR_normalized_factor_seed_incidence
    A2 g hA2ne hgR agreement (cap 0) (cap 1) (cap 2)
    point (selectedPoint_zyPair_injective φ selected)
    selected seeds nodes x u₀ u₁ hinj w a e hwa han hdegree
    hA2root hAregular hgpoint hgRegular hagreement
    (fun i hi => ⟨hcap i hi 0, hcap i hi 1, hcap i hi 2⟩)
    hBzero hnoPencil
  have hA2Y : A2.degreeOf 0 ≤ A.degreeOf 1 :=
    (dropR_degreeOf_le A3 0).trans (RCN136.surfaceMap_degreeOf_le φ A 0)
  have hA2Z : A2.degreeOf 1 ≤ A.degreeOf 3 :=
    (dropR_degreeOf_le A3 1).trans (RCN136.surfaceMap_degreeOf_le φ A 2)
  have hcost :
      A2.degreeOf 0 * (cap 2 + cap 1 * g.degreeOf 2) +
          A2.degreeOf 1 * (cap 0 + cap 1 * g.degreeOf 0) ≤
        ∑ j : Fin 3, cap j *
          RCN068.capAt (RCN170.geometricPairCost A g) j := by
    have h := Nat.add_le_add
      (Nat.mul_le_mul_right (cap 2 + cap 1 * g.degreeOf 2) hA2Y)
      (Nat.mul_le_mul_right (cap 0 + cap 1 * g.degreeOf 0) hA2Z)
    exact h.trans_eq (by
      simp [Fin.sum_univ_three, RCN068.capAt,
        RCN170.geometricPairCost, hgR]
      ring)
  have hcharge : A2.degreeOf 0 ≤
      RCN068.capAt (RCN170.geometricPairCost A g) 2 := by
    simpa [RCN068.capAt, RCN170.geometricPairCost, hgR] using hA2Y
  exact hraw.trans (Nat.add_le_add
    (Nat.mul_le_mul_left (nodes.card - w) hcost)
    (Nat.mul_le_mul_left ((e + 1) * (a - w)) hcharge))

def dropRHom : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
  Polynomial.constantCoeff.comp (collectR3 (K := K)).toRingHom

theorem dropRHom_apply (Q : MvPolynomial (Fin 3) K) :
    dropRHom Q = dropR Q := by rfl

@[simp] theorem dropRHom_X_Y :
    dropRHom (K := K) (MvPolynomial.X (0 : Fin 3)) =
      MvPolynomial.X (0 : Fin 2) := by
  simp [dropRHom]

@[simp] theorem dropRHom_X_R :
    dropRHom (K := K) (MvPolynomial.X (1 : Fin 3)) = 0 := by
  simp [dropRHom]

@[simp] theorem dropRHom_X_Z :
    dropRHom (K := K) (MvPolynomial.X (2 : Fin 3)) =
      MvPolynomial.X (1 : Fin 2) := by
  simp [dropRHom]

theorem dropRHom_pderiv_Y (Q : MvPolynomial (Fin 3) K) :
    dropRHom (MvPolynomial.pderiv 0 Q) =
      MvPolynomial.pderiv 0 (dropRHom Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [dropRHom, dropR, collectR3_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i <;>
        simp [MvPolynomial.pderiv_X, map_add, map_mul, hP] <;> ring

theorem dropR_pderiv_Y (Q : MvPolynomial (Fin 3) K) :
    MvPolynomial.pderiv 0 (dropR Q) = dropR (MvPolynomial.pderiv 0 Q) := by
  rw [← dropRHom_apply, ← dropRHom_apply, dropRHom_pderiv_Y]

theorem pderiv_other_degree_le
    {σ : Type} [DecidableEq σ]
    (i j : σ) (Q : MvPolynomial σ K) :
    (MvPolynomial.pderiv i Q).degreeOf j ≤ Q.degreeOf j := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hbefore : d + Finsupp.single i 1 ∈ Q.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hne := MvPolynomial.mem_support_iff.mp hd
    apply hne
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have hle := MvPolynomial.monomial_le_degreeOf j hbefore
  simpa only [Finsupp.add_apply] using
    (Nat.le_trans (Nat.le_add_right (d j) ((Finsupp.single i 1) j)) hle)

/-- Bridge requested by the outer BW theorem. -/
theorem selected_dropR_surface_Y_regular_of_specialization
    {k : Type} [Field k]
    (A : MvPolynomial (Fin 4) k) (hAR : A.degreeOf 2 = 0)
    (selected : k → Polynomial k) (γ : k)
    (hregularA : RCN319.specialization k (selected γ) γ
      (MvPolynomial.pderiv (1 : Fin 4) A) ≠ 0) :
    MvPolynomial.eval
      (yzPoint (RCN238.selectedPoint (RCN135.polynomialEmbedding k) selected γ))
      (MvPolynomial.pderiv 0
        (dropR (RCN136.surfaceMap (RCN135.polynomialEmbedding k) A))) ≠ 0 := by
  let φ := RCN135.polynomialEmbedding k
  let A3 := RCN136.surfaceMap φ A
  let point := RCN238.selectedPoint φ selected γ
  have hA3R : A3.degreeOf 1 = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (RCN136.surfaceMap_degreeOf_le φ A 1).trans_eq hAR
  have hderR : (MvPolynomial.pderiv 0 A3).degreeOf 1 = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (pderiv_other_degree_le 0 1 A3).trans_eq hA3R
  rw [dropR_pderiv_Y]
  rw [dropR_eval (MvPolynomial.pderiv 0 A3) hderR point]
  change MvPolynomial.eval point
    (MvPolynomial.pderiv 0 (RCN136.surfaceMap φ A)) ≠ 0
  rw [RCN267.surfaceMap_pderiv]
  rw [RCN170.canonical_selectedPoint_surface_evaluation]
  exact (map_ne_zero_iff (RCN135.polynomialEmbedding k)
    (RCN135.polynomialEmbedding_injective k)).mpr hregularA

/-- Complete characteristic-free replacement for `BW.implicit_pair_seed_bound`.
The conclusion is byte-for-byte the same arithmetic expression; the mixed-R
gate is gone. -/
theorem implicit_pair_seed_bound_linearR
    {k ι : Type} [Field k] [DecidableEq k] [DecidableEq ι]
    (A G : MvPolynomial (Fin 4) k)
    (hA : Irreducible A) (hG : Irreducible G)
    (hGR : G.degreeOf 2 = 1) (hproper : ¬ G ∣ A)
    (implicitD w jY jZ p n a e : ℕ)
    (hAbox : A ∈ RCN174.globalCoefficientBox k implicitD w jZ 0)
    (hGbox : G ∈ RCN174.globalCoefficientBox k implicitD w jZ 1)
    (hjY : (implicitD - 1) / w = jY)
    (selected : k → Polynomial k) (Γ : Finset k)
    (nodes : Finset ι) (x u₀ u₁ : ι → k) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n) [CharP k p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a) (han : a ≤ n)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolutionA : ∀ γ ∈ Γ, RCN319.specialization k (selected γ) γ A = 0)
    (hregularA : ∀ γ ∈ Γ,
      RCN319.specialization k (selected γ) γ
        (MvPolynomial.pderiv (1 : Fin 4) A) ≠ 0)
    (hsolutionG : ∀ γ ∈ Γ, RCN319.specialization k (selected γ) γ G = 0)
    (hregularG : ∀ γ ∈ Γ,
      RCN319.specialization k (selected γ) γ
        (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : RCN238.NoLargeSelectedPencil selected Γ w e) :
    Γ.card * (a - w) ≤
      (n - w) *
        ((1 + 2 * w * jY) * RCN169.pairYCost ⟨A, G⟩ +
          w * RCN169.pairRCost ⟨A, G⟩ +
          (2 * w * jZ + 1) * RCN169.pairZCost ⟨A, G⟩) +
        (e + 1) * (a - w) * RCN169.pairZCost ⟨A, G⟩ := by
  classical
  let φ := RCN135.polynomialEmbedding k
  let factors := RCN137.surfaceFactors φ G
  let seedsFor := fun g : MvPolynomial (Fin 3) (RCN135.GenericField k) =>
    Γ.filter (fun γ =>
      MvPolynomial.eval (RCN238.selectedPoint φ selected γ) g = 0)
  let agreementCap : RCN051.DegreeVector :=
    ⟨1 + 2 * w * jY, w, 2 * w * jZ + 1⟩
  have hsub (g) : seedsFor g ⊆ Γ := Finset.filter_subset _ _
  have hAGcaps := RCN081.degree_bounds_of_mem_box A implicitD w jZ 0 hw hAbox
  have hGGcaps := RCN081.degree_bounds_of_mem_box G implicitD w jZ 1 hw hGbox
  have hAY : A.degreeOf 1 ≤ jY := hAGcaps.1.trans_eq hjY
  have hGY : G.degreeOf 1 ≤ jY := hGGcaps.1.trans_eq hjY
  have hAR : A.degreeOf 2 = 0 := Nat.eq_zero_of_le_zero hAGcaps.2.1
  have hGzero : ∀ γ ∈ Γ,
      MvPolynomial.eval (RCN238.selectedPoint φ selected γ)
        (RCN136.surfaceMap φ G) = 0 := by
    intro γ hγ
    rw [RCN170.canonical_selectedPoint_surface_evaluation,
      hsolutionG γ hγ, map_zero]
  have hAzero : ∀ γ ∈ Γ,
      MvPolynomial.eval (RCN238.selectedPoint φ selected γ)
        (RCN136.surfaceMap φ A) = 0 := by
    intro γ hγ
    rw [RCN170.canonical_selectedPoint_surface_evaluation,
      hsolutionA γ hγ, map_zero]
  have hcover : Γ ⊆ factors.biUnion seedsFor := by
    intro γ hγ
    obtain ⟨g, hg, hz⟩ := RCN137.exists_surfaceFactor_zero φ
      (RCN135.polynomialEmbedding_injective k) G hG.ne_zero
      (RCN238.selectedPoint φ selected γ) (hGzero γ hγ)
    exact Finset.mem_biUnion.mpr
      ⟨g, hg, Finset.mem_filter.mpr ⟨hγ, hz⟩⟩
  have hcard : Γ.card ≤ ∑ g ∈ factors, (seedsFor g).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsingle
      (g : MvPolynomial (Fin 3) (RCN135.GenericField k)) (hg : g ∈ factors) :
      (seedsFor g).card * (a - w) ≤
        (n - w) * (∑ i : Fin 3,
          RCN068.capAt agreementCap i *
            RCN068.capAt (RCN170.geometricPairCost A g) i) +
          (e + 1) * (a - w) *
            RCN068.capAt (RCN170.geometricPairCost A g) 2 := by
    obtain ⟨hgi, hdiv⟩ := RCN137.surfaceFactors_spec φ G g hg
    have hfacdegree (i : Fin 3) : g.degreeOf i ≤ G.degreeOf i.succ :=
      (RCN137.coordinate_degree_le_of_dvd i g (RCN136.surfaceMap φ G) hdiv
        (RCN136.surfaceMap_ne_zero φ
          (RCN135.polynomialEmbedding_injective k) G hG.ne_zero)).trans
        (RCN136.surfaceMap_degreeOf_le φ G i)
    have hgRle : g.degreeOf 1 ≤ 1 := (hfacdegree 1).trans_eq hGR
    have hregularG' : ∀ γ ∈ seedsFor g,
        MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
          (RCN231.polynomialPoint (φ.comp Polynomial.C)
            (selected γ) γ (φ Polynomial.X))
          (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0 := by
      intro γ hγ
      exact (RCN135.initialPoint_regular_iff k G (selected γ) γ).mpr
        (hregularG γ (hsub g hγ))
    have hAregular' : ∀ γ ∈ seedsFor g,
        MvPolynomial.eval
          (yzPoint (RCN238.selectedPoint φ selected γ))
          (MvPolynomial.pderiv 0
            (dropR (RCN136.surfaceMap φ A))) ≠ 0 := by
      intro γ hγ
      exact selected_dropR_surface_Y_regular_of_specialization
        A hAR selected γ (hregularA γ (hsub g hγ))
    have hcap' (i : ι) : ∀ j,
        (RCN238.agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)).degreeOf j ≤
          RCN068.capAt agreementCap j := by
      have hc := RCN068.surface_agreement_caps φ G jY 1 jZ (by decide)
        hGY hGGcaps.2.1 hGGcaps.2.2 w
        (fun j => (j.factorial : k)⁻¹) (x i) (u₀ i) (u₁ i)
      simpa [RCN068.HasCaps, RCN238.agreementPolynomial, RCN068.agreementCaps,
        agreementCap] using hc
    have hcount := implicit_pair_surface_factor_seed_bound_linearR
      φ (RCN135.polynomialEmbedding_injective k) A G hA.ne_zero hAR
      g hgi hdiv hgRle selected (seedsFor g) nodes x u₀ u₁ hinj
      p w a e hw hchar hwa (by simpa [hnodes] using han)
      (fun γ hγ => hdegree γ (hsub g hγ))
      (fun γ hγ => hsolutionG γ (hsub g hγ)) hregularG'
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => hAzero γ (hsub g hγ)) hAregular'
      (fun γ hγ => hagreement γ (hsub g hγ))
      (RCN243.noLargeSelectedPencil_mono selected Γ (seedsFor g)
        w e (hsub g) hnoPencil)
      (RCN068.capAt agreementCap) (fun i _ => hcap' i)
    rwa [hnodes] at hcount
  have hbudget (i : Fin 3) :
      (∑ g ∈ factors,
        RCN068.capAt (RCN170.geometricPairCost A g) i) ≤
          RCN068.capAt (RCN170.pairCost A G) i :=
    RCN170.sum_geometricPairCost_le φ
      (RCN135.polynomialEmbedding_injective k) A G hG.ne_zero i
  have hfubini :
      (∑ g ∈ factors, ∑ i : Fin 3,
        RCN068.capAt agreementCap i *
          RCN068.capAt (RCN170.geometricPairCost A g) i) =
        ∑ i : Fin 3, RCN068.capAt agreementCap i *
          (∑ g ∈ factors,
            RCN068.capAt (RCN170.geometricPairCost A g) i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    Γ.card * (a - w) ≤ (∑ g ∈ factors, (seedsFor g).card) * (a - w) :=
      Nat.mul_le_mul_right (a - w) hcard
    _ = ∑ g ∈ factors, (seedsFor g).card * (a - w) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g ∈ factors,
        ((n - w) * (∑ i : Fin 3,
          RCN068.capAt agreementCap i *
            RCN068.capAt (RCN170.geometricPairCost A g) i) +
          (e + 1) * (a - w) *
            RCN068.capAt (RCN170.geometricPairCost A g) 2) :=
      Finset.sum_le_sum (fun g hg => hsingle g hg)
    _ = (n - w) * (∑ i : Fin 3, RCN068.capAt agreementCap i *
          (∑ g ∈ factors,
            RCN068.capAt (RCN170.geometricPairCost A g) i)) +
        (e + 1) * (a - w) *
          (∑ g ∈ factors,
            RCN068.capAt (RCN170.geometricPairCost A g) 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hfubini]
    _ ≤ (n - w) * (∑ i : Fin 3, RCN068.capAt agreementCap i *
          RCN068.capAt (RCN170.pairCost A G) i) +
        (e + 1) * (a - w) * RCN068.capAt (RCN170.pairCost A G) 2 :=
      Nat.add_le_add
        (Nat.mul_le_mul_left (n - w) (Finset.sum_le_sum
          (fun i _ => Nat.mul_le_mul_left
            (RCN068.capAt agreementCap i) (hbudget i))))
        (Nat.mul_le_mul_left ((e + 1) * (a - w)) (hbudget 2))
    _ = (n - w) *
        ((1 + 2 * w * jY) * RCN169.pairYCost ⟨A, G⟩ +
          w * RCN169.pairRCost ⟨A, G⟩ +
          (2 * w * jZ + 1) * RCN169.pairZCost ⟨A, G⟩) +
        (e + 1) * (a - w) * RCN169.pairZCost ⟨A, G⟩ := by
      simp [Fin.sum_univ_three, RCN068.capAt, agreementCap,
        RCN170.pairCost]

end

end ProximityPrize.SubmissionLower.RCN374

