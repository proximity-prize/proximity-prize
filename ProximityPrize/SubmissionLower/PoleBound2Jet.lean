import ProximityPrize.SubmissionLower.PoleMoment2Jet

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1600000

/-!
# Global 2-Jet Pole Rank Bound (`PoleBound2Jet`)

Completes Piece 1 by connecting `PoleMoment2Jet.simple_rank_le_2jet` to
`PortHighBase.regular_deformation` and `Fast065.specialization_rank_le`, delivering:
- `Source2`, `ambient2`, `physical2`, `poleSpace2`, `contacted2`, `complete2`
- `matrix_of_columns_2jet` (`K1_14_1_7_4` 2-jet analog)
- `pole_bound_2jet`:
    `Module.finrank L (contacted2 h word s W) ≤`
      `poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s +`
        `Module.finrank L (complete2 Crt word s W)`
-/

namespace PoleBound2Jet
noncomputable section

open Polynomial Matrix Finset
open K1 (I)
open K1_14 (L triangle)
open K1_14_1 (SeedPoly SeedField seedWeight PoleData CRTLift poleProduct rawBlock crtPolynomial nodeL)
open K1_14_1_7 (Seed SeedFrac Exponent Parameter GenericField specialPoint genericPoint liftAt
  RegularDeformation specialization_rank_le)
open PoleMoment2Jet
open scoped BigOperators Matrix Polynomial

open P0_10_1_1 (regular_deformation)

abbrev Source2 := TrueSource2 L
abbrev RawSource2 := JetPolys2 SeedField

def coeffAt2 (P : Source2) (e₂ e₁ e₀ a : ℕ) (e : Fin 2 →₀ ℕ) : L :=
  sourceCoeff2 P e₂ e₁ e₀ a e

def trueEligible2 (h : ℕ) (s : Shape2) (W e₂ e₁ e₀ a : ℕ) (e : Fin 2 →₀ ℕ) : Prop :=
  e₀ + e₁ + e₂ ≤ s.B ∧ jetIdx e₁ e₂ ≤ s.J ∧ e₂ ≤ s.C ∧ seedWeight e ≤ s.U ∧
    a + (e₀ + e₁ + e₂) * (131071 + h) ≤ W + (s.B + s.J) * (2 * h) + jetIdx e₁ e₂

def ambient2 (h : ℕ) (s : Shape2) (W : ℕ) : Submodule L Source2 where
  carrier := {P | ∀ e₂ e₁ e₀ a e, ¬ trueEligible2 h s W e₂ e₁ e₀ a e → coeffAt2 P e₂ e₁ e₀ a e = 0}
  zero_mem' := by simp [coeffAt2, sourceCoeff2]
  add_mem' := by
    intro P Q hP hQ e₂ e₁ e₀ a e he
    have hp := hP e₂ e₁ e₀ a e he
    have hq := hQ e₂ e₁ e₀ a e he
    unfold coeffAt2 sourceCoeff2 at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro b P hP e₂ e₁ e₀ a e he
    have hp := hP e₂ e₁ e₀ a e he
    unfold coeffAt2 sourceCoeff2 at hp ⊢
    simp [Polynomial.coeff_smul, hp]

private def substituteJets2L {R S A : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring A] [Algebra R S] [Algebra R A]
    (base : S →ₐ[R] A) (y0 y1 y2 : A) : Polynomial (Polynomial (Polynomial S)) →ₐ[R] A :=
  eval₂AlgHom (eval₂AlgHom (eval₂AlgHom base y0 (fun _ => Commute.all _ _))
    y1 (fun _ => Commute.all _ _)) y2 (fun _ => Commute.all _ _)

/-- 2-Jet physical Hasse contact evaluation at node `(x, r)`:
    `X ↦ X + x`, `Y₀ ↦ r + X * Y₁ + X² * Y₂ + η`, `Y₁ ↦ Y₁`, `Y₂ ↦ Y₂`. -/
def atPhysical2 (x r : L) : Source2 →ₐ[L] Source2 :=
  let c : SeedPoly[X] →+* Source2 := jetConstant2
  let base : SeedPoly[X] →ₐ[L] SeedPoly[X] :=
    eval₂AlgHom (IsScalarTower.toAlgHom L SeedPoly SeedPoly[X])
      (Polynomial.X (R := SeedPoly) + (@Polynomial.C SeedPoly _) (MvPolynomial.C x))
      (fun _ => Commute.all _ _)
  let y0 : Source2 := C (C (Polynomial.X (R := SeedPoly[X])))
  let y1 : Source2 := C (Polynomial.X (R := SeedPoly[X][X]))
  let y2 : Source2 := Polynomial.X
  substituteJets2L (R := L) (S := SeedPoly[X]) (A := Source2)
    ((IsScalarTower.toAlgHom L SeedPoly[X] Source2).comp base)
    (c ((@Polynomial.C SeedPoly _) (MvPolynomial.C r)) +
      c (Polynomial.X (R := SeedPoly)) * y1 -
      c ((Polynomial.X (R := SeedPoly)) ^ 2) * y2 + y0)
    y1 y2

theorem atPhysical2_as_substitute (x r : L) :
    (atPhysical2 x r).toRingHom =
      PoleMoment2Jet.substitute2
        (jetConstant2.comp (eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C (MvPolynomial.C x))))
        (jetConstant2 (Polynomial.C (MvPolynomial.C r)) +
          jetConstant2 Polynomial.X * C Polynomial.X -
          jetConstant2 (Polynomial.X ^ 2) * Polynomial.X +
          C (C Polynomial.X))
        (C Polynomial.X) Polynomial.X := by
  rfl

def physical2 (word : I → L) (s : Shape2) : Submodule L Source2 where
  carrier := {P | ∀ i a b e₁ e₂ e, a + 3 * b < s.m →
    coeffAt2 (atPhysical2 (nodeL i) (word i) P) e₂ e₁ b a e = 0}
  zero_mem' := by simp [coeffAt2, sourceCoeff2]
  add_mem' := by
    intro P Q hP hQ i a b e₁ e₂ e he
    have hp := hP i a b e₁ e₂ e he
    have hq := hQ i a b e₁ e₂ e he
    unfold coeffAt2 sourceCoeff2 at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro c P hP i a b e₁ e₂ e he
    have hp := hP i a b e₁ e₂ e he
    unfold coeffAt2 sourceCoeff2 at hp ⊢
    simp [Polynomial.coeff_smul, hp]

def poleSpace2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (s : Shape2) : Submodule L Source2 where
  carrier := {P | PoleTest2 s (poleProduct D) (crtPolynomial Crt) P}
  zero_mem' := by simp [PoleTest2]
  add_mem' := by
    intro P Q hP hQ
    change _ ∣ forward2 _ _ (P + Q)
    rw [map_add]
    exact dvd_add hP hQ
  smul_mem' := by
    intro b P hP
    change _ ∣ forward2 _ _ (b • P)
    rw [map_smul, Algebra.smul_def]
    exact dvd_mul_of_dvd_right hP _

def contacted2 (h : ℕ) (word : I → L) (s : Shape2) (W : ℕ) : Submodule L Source2 :=
  ambient2 h s W ⊓ physical2 word s

def complete2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) : Submodule L Source2 :=
  contacted2 h word s W ⊓ poleSpace2 Crt s

theorem contacted2_shaped {h : ℕ} {word : I → L} {s : Shape2} {W : ℕ}
    {P : Source2} (hP : P ∈ contacted2 h word s W) : Shaped2 s P := by
  intro e₂ e₁ e₀ a e hn
  have he : trueEligible2 h s W e₂ e₁ e₀ a e := by
    by_contra hf
    exact hn (hP.1 e₂ e₁ e₀ a e hf)
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1⟩

private abbrev CoeffBox2 (B M U : ℕ) :=
  Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin (M + 1) × (Fin 2 → Fin (U + 1))

theorem contacted2_finite (h : ℕ) (word : I → L) (s : Shape2) (W : ℕ) :
    Module.Finite L (contacted2 h word s W) := by
  let M := W + (s.B + s.J) * (2 * h) + s.J
  let f : contacted2 h word s W →ₗ[L] (CoeffBox2 s.B M s.U → L) :=
    LinearMap.pi fun u =>
      { toFun := fun P =>
          coeffAt2 P.1 u.1.val u.2.1.val u.2.2.1.val u.2.2.2.1.val
            (Finsupp.equivFunOnFinite.symm (fun k => (u.2.2.2.2 k).val))
        map_add' := fun P Q => by simp [coeffAt2, sourceCoeff2]
        map_smul' := fun c P => by simp [coeffAt2, sourceCoeff2] }
  have hzero : ∀ Q : contacted2 h word s W, f Q = 0 → Q = 0 := by
    intro Q hQ
    apply Subtype.ext
    change Q.1 = 0
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    apply MvPolynomial.ext; intro e
    simp only [Polynomial.coeff_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    change coeffAt2 Q.1 e₂ e₁ e₀ a e = 0
    by_cases he : trueEligible2 h s W e₂ e₁ e₀ a e
    · obtain ⟨hB, hJ, _, hU, hW⟩ := he
      have hM : a ≤ M := by dsimp [M]; omega
      have hU' (k : Fin 2) : e k ≤ s.U := by
        apply le_trans _ hU
        rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      let u : CoeffBox2 s.B M s.U :=
        (⟨e₂, by omega⟩, ⟨e₁, by omega⟩, ⟨e₀, by omega⟩, ⟨a, by omega⟩,
          fun k => ⟨e k, Nat.lt_succ_of_le (hU' k)⟩)
      have hz := congrFun hQ u
      change coeffAt2 Q.1 e₂ e₁ e₀ a (Finsupp.equivFunOnFinite.symm (fun k => e k)) = 0 at hz
      exact (Finsupp.equivFunOnFinite.symm_apply_apply e) ▸ hz
    · exact Q.2.1 e₂ e₁ e₀ a e he
  apply Module.Finite.of_injective f
  intro P Q hPQ
  apply sub_eq_zero.mp
  exact hzero (P - Q) (by rw [map_sub, hPQ, sub_self])

/-! ## Parameter Specialization & `matrix_of_columns_2jet` -/

def jetMap2 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    JetPolys2 R →+* JetPolys2 S :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom f)))

def mapSource2 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    TrueSource2 R →+* TrueSource2 S :=
  jetMap2 (MvPolynomial.map f)

theorem shaped2_map {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {s : Shape2} {P : TrueSource2 R} (hP : Shaped2 s P) : Shaped2 s (mapSource2 f P) := by
  intro e₂ e₁ e₀ a e hne
  apply hP e₂ e₁ e₀ a e
  intro hz
  apply hne
  unfold sourceCoeff2 at hz ⊢
  unfold mapSource2 jetMap2
  simp only [coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.coeff_map, hz, map_zero]

private def seedAt {F : Type} [Field F] (point : Parameter →+* F) :
    Seed Parameter →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (MvPolynomial.map point)

private def scalarJet2 {R : Type} [CommSemiring R] (d : R) : JetPolys2 R :=
  jetConstant2 (Polynomial.C d)

private def rawY0 {R : Type} [CommSemiring R] : JetPolys2 R := C (C (Polynomial.X (R := R[X])))
private def rawY1 {R : Type} [CommSemiring R] : JetPolys2 R := C (Polynomial.X (R := R[X][X]))
private def rawY2 {R : Type} [CommSemiring R] : JetPolys2 R := Polynomial.X

private def clearedY0 {R : Type} [CommSemiring R] (H N : R[X]) (d : R) : JetPolys2 R :=
  scalarJet2 d * (jetConstant2 H * rawY0) + jetConstant2 N

private def clearedY1 {R : Type} [CommSemiring R] (H N : R[X]) (d : R) : JetPolys2 R :=
  scalarJet2 d * (jetConstant2 H * rawY1 + jetConstant2 H.derivative * rawY0) +
    jetConstant2 N.derivative

private def clearedY2 {R : Type} [CommSemiring R] (H N : R[X]) (d : R) : JetPolys2 R :=
  scalarJet2 d * (jetConstant2 H * rawY2 + jetConstant2 H.derivative * rawY1 +
      jetConstant2 (hasseDeriv 2 H) * rawY0) +
    jetConstant2 (hasseDeriv 2 N)

private def cleared2 (s : Shape2) (H : Parameter[X]) (N : (Seed Parameter)[X])
    (d : Seed Parameter) (P : Source2) : TrueSource2 Parameter :=
  let h := H.map (MvPolynomial.C (σ := Fin 2))
  let y0 := clearedY0 h N d
  let y1 := clearedY1 h N d
  let y2 := clearedY2 h N d
  ∑ e₂ ∈ P.support, ∑ e₁ ∈ (P.coeff e₂).support, ∑ e₀ ∈ ((P.coeff e₂).coeff e₁).support,
    scalarJet2 d ^ (s.B - (e₀ + e₁ + e₂)) *
      (jetConstant2 ((((P.coeff e₂).coeff e₁).coeff e₀).map (MvPolynomial.map (Polynomial.C (R := L)))) *
        y0 ^ e₀ * y1 ^ e₁ * y2 ^ e₂)

private theorem eval_expansion2 {A T : Type} [CommSemiring A] [CommSemiring T]
    (f : JetPolys2 A →+* T) (P : JetPolys2 A) :
    f P = ∑ e₂ ∈ P.support, ∑ e₁ ∈ (P.coeff e₂).support, ∑ e₀ ∈ ((P.coeff e₂).coeff e₁).support,
      f (jetConstant2 (((P.coeff e₂).coeff e₁).coeff e₀)) *
        f rawY0 ^ e₀ * f rawY1 ^ e₁ * f rawY2 ^ e₂ := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow]
  apply Finset.sum_congr rfl; intro e₂ _
  conv_lhs => rw [(P.coeff e₂).as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro e₁ _
  conv_lhs => rw [((P.coeff e₂).coeff e₁).as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul, jetConstant2, RingHom.comp_apply,
    rawY0, rawY1, rawY2]

private theorem degree_of_shaped2 {s : Shape2} {P : Source2} (hP : Shaped2 s P)
    {e₂ e₁ e₀ : ℕ} (h0 : e₀ ∈ ((P.coeff e₂).coeff e₁).support) : e₀ + e₁ + e₂ ≤ s.B := by
  have hn : ((P.coeff e₂).coeff e₁).coeff e₀ ≠ 0 := Polynomial.mem_support_iff.mp h0
  by_contra hb
  apply hn
  apply Polynomial.ext; intro a
  apply MvPolynomial.ext; intro e
  simp only [Polynomial.coeff_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra he
  exact hb (hP e₂ e₁ e₀ a e he).1

private theorem map_abscissa {F : Type} [Field F] (point : Parameter →+* F) (H : Parameter[X]) :
    (H.map (MvPolynomial.C (σ := Fin 2))).map (seedAt point) =
      (H.map point).map (algebraMap F (SeedFrac F)) := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  apply RingHom.ext; intro a
  simp [seedAt, IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F)]

private theorem jetMap2_const {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : R[X]) : jetMap2 f (jetConstant2 p) = jetConstant2 (p.map f) := by
  simp [jetMap2, jetConstant2]

private theorem jetMap2_scalar {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (a : R) : jetMap2 f (scalarJet2 a) = scalarJet2 (f a) := by
  simp [scalarJet2, jetMap2_const]

private theorem jetMap2_rawY0 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    jetMap2 f rawY0 = rawY0 := by simp [jetMap2, rawY0]

private theorem jetMap2_rawY1 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    jetMap2 f rawY1 = rawY1 := by simp [jetMap2, rawY1]

private theorem jetMap2_rawY2 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    jetMap2 f rawY2 = rawY2 := by simp [jetMap2, rawY2]

private theorem cleared2_specializes {F : Type} [Field F] (point : Parameter →+* F)
    (s : Shape2) (H : Parameter[X]) (N : (Seed Parameter)[X]) (d : Seed Parameter)
    (hd : MvPolynomial.map point d ≠ 0) (P : Source2) (hP : Shaped2 s P) :
    jetMap2 (seedAt point) (cleared2 s H N d P) =
      scalarJet2 (seedAt point d) ^ s.B *
        forward2 (H.map point) (liftAt point N d)
          (mapSource2 (point.comp (Polynomial.C (R := L))) P) := by
  let sd := seedAt point d
  have hsd : sd ≠ 0 := by
    intro hz
    exact hd (IsFractionRing.injective (Seed F) (SeedFrac F) (hz.trans (map_zero _).symm))
  let hp := (H.map point).map (algebraMap F (SeedFrac F))
  let lp := liftAt point N d
  have hlift_mul : C sd * lp = N.map (seedAt point) := by
    unfold lp liftAt
    rw [Polynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    change C (sd * sd⁻¹) * N.map (seedAt point) = N.map (seedAt point)
    rw [mul_inv_cancel₀ hsd, map_one, one_mul]
  have hlift_der : C sd * lp.derivative = (N.derivative).map (seedAt point) := by
    rw [← Polynomial.derivative_C_mul, hlift_mul, Polynomial.derivative_map]
  have hlift_h2 : C sd * hasseDeriv 2 lp = (hasseDeriv 2 N).map (seedAt point) := by
    have hmul : hasseDeriv 2 (C sd * lp) = C sd * hasseDeriv 2 lp := by
      rw [← Polynomial.smul_eq_C_mul, map_smul, Polynomial.smul_eq_C_mul]
    rw [← hmul, hlift_mul, Polynomial.hasseDeriv_map]
  have hmapH : (H.map (MvPolynomial.C (σ := Fin 2))).map (seedAt point) = hp :=
    map_abscissa point H
  have hy0 : jetMap2 (seedAt point) (clearedY0 (H.map (MvPolynomial.C (σ := Fin 2))) N d) =
      scalarJet2 sd * (jetConstant2 hp * rawY0 + jetConstant2 lp) := by
    rw [clearedY0, map_add, map_mul, map_mul, jetMap2_scalar, jetMap2_const, jetMap2_const,
      jetMap2_rawY0, hmapH, ← hlift_mul, map_mul]
    exact (mul_add _ _ _).symm
  have hy1 : jetMap2 (seedAt point) (clearedY1 (H.map (MvPolynomial.C (σ := Fin 2))) N d) =
      scalarJet2 sd * (jetConstant2 hp * rawY1 + jetConstant2 hp.derivative * rawY0 +
        jetConstant2 lp.derivative) := by
    rw [clearedY1, map_add, map_mul, map_add, map_mul, map_mul, jetMap2_scalar, jetMap2_const,
      jetMap2_const, jetMap2_const, jetMap2_rawY0, jetMap2_rawY1, ← Polynomial.derivative_map,
      hmapH, ← hlift_der, map_mul]
    exact (mul_add _ _ _).symm
  have hy2 : jetMap2 (seedAt point) (clearedY2 (H.map (MvPolynomial.C (σ := Fin 2))) N d) =
      scalarJet2 sd * (jetConstant2 hp * rawY2 + jetConstant2 hp.derivative * rawY1 +
        jetConstant2 (hasseDeriv 2 hp) * rawY0 + jetConstant2 (hasseDeriv 2 lp)) := by
    rw [clearedY2, map_add, map_mul, map_add, map_add, map_mul, map_mul, map_mul, jetMap2_scalar,
      jetMap2_const, jetMap2_const, jetMap2_const, jetMap2_const, jetMap2_rawY0, jetMap2_rawY1,
      jetMap2_rawY2, ← Polynomial.derivative_map, ← Polynomial.hasseDeriv_map, hmapH, ← hlift_h2,
      map_mul]
    exact (mul_add _ _ _).symm
  let Fhom := (forward2 (H.map point) lp).toRingHom.comp
    (mapSource2 (point.comp (Polynomial.C (R := L))))
  have hFbase (q : SeedPoly[X]) :
      Fhom (jetConstant2 q) =
        jetConstant2 ((q.map (MvPolynomial.map (Polynomial.C (R := L)))).map (seedAt point)) := by
    change (forward2 (H.map point) lp).toRingHom (mapSource2 _ (jetConstant2 q)) = _
    rw [forward2_as_substitute, mapSource2, jetMap2_const, substitute2_base]
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_map]
    congr 2
    apply MvPolynomial.ringHom_ext
    · intro a; simp [seedAt]
    · intro j; simp [seedAt]
  have hFy0 : Fhom rawY0 = jetConstant2 hp * rawY0 + jetConstant2 lp := by
    change (forward2 (H.map point) lp).toRingHom (mapSource2 _ rawY0) = _
    rw [forward2_as_substitute]
    simp [mapSource2, jetMap2, rawY0, hp, lp]
  have hFy1 : Fhom rawY1 = jetConstant2 hp * rawY1 + jetConstant2 hp.derivative * rawY0 +
      jetConstant2 lp.derivative := by
    change (forward2 (H.map point) lp).toRingHom (mapSource2 _ rawY1) = _
    rw [forward2_as_substitute]
    simp [mapSource2, jetMap2, rawY0, rawY1, hp, lp]
  have hFy2 : Fhom rawY2 = jetConstant2 hp * rawY2 + jetConstant2 hp.derivative * rawY1 +
      jetConstant2 (hasseDeriv 2 hp) * rawY0 + jetConstant2 (hasseDeriv 2 lp) := by
    change (forward2 (H.map point) lp).toRingHom (mapSource2 _ rawY2) = _
    rw [forward2_as_substitute]
    simp [mapSource2, jetMap2, rawY0, rawY1, rawY2, hp, lp]
  change _ = scalarJet2 sd ^ s.B * Fhom P
  rw [eval_expansion2 Fhom P, Finset.mul_sum]
  unfold cleared2
  simp only [map_sum, map_mul, map_pow, hy0, hy1, hy2]
  apply Finset.sum_congr rfl; intro e₂ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e₀ h0
  have hB : e₀ + e₁ + e₂ ≤ s.B := degree_of_shaped2 hP h0
  have hpow : scalarJet2 sd ^ (s.B - (e₀ + e₁ + e₂)) *
      (scalarJet2 sd ^ e₀ * scalarJet2 sd ^ e₁ * scalarJet2 sd ^ e₂) =
      scalarJet2 sd ^ s.B := by
    rw [← pow_add, ← pow_add, ← pow_add, Nat.sub_add_cancel hB]
  have hc : jetMap2 (seedAt point) (scalarJet2 d) = scalarJet2 sd := by
    simp [jetMap2, scalarJet2, jetConstant2, sd]
  have hb : jetMap2 (seedAt point)
      (jetConstant2 ((((P.coeff e₂).coeff e₁).coeff e₀).map (MvPolynomial.map (Polynomial.C (R := L))))) =
      Fhom (jetConstant2 (((P.coeff e₂).coeff e₁).coeff e₀)) := by
    rw [hFbase]
    simp [jetMap2, jetConstant2]
  rw [hc, hb, ← hFy0, ← hFy1, ← hFy2]
  simp only [mul_pow]
  calc
    scalarJet2 sd ^ (s.B - (e₀ + e₁ + e₂)) *
        (Fhom (jetConstant2 (((P.coeff e₂).coeff e₁).coeff e₀)) *
          (scalarJet2 sd ^ e₀ * Fhom rawY0 ^ e₀) *
          (scalarJet2 sd ^ e₁ * Fhom rawY1 ^ e₁) *
          (scalarJet2 sd ^ e₂ * Fhom rawY2 ^ e₂)) =
      (scalarJet2 sd ^ (s.B - (e₀ + e₁ + e₂)) *
        (scalarJet2 sd ^ e₀ * scalarJet2 sd ^ e₁ * scalarJet2 sd ^ e₂)) *
        (Fhom (jetConstant2 (((P.coeff e₂).coeff e₁).coeff e₀)) *
          Fhom rawY0 ^ e₀ * Fhom rawY1 ^ e₁ * Fhom rawY2 ^ e₂) := by ring
    _ = _ := by rw [hpow]

private abbrev Row2 := ℕ × ℕ × ℕ × ℕ × Exponent

private def readRow2 {R : Type} [CommRing R] (Q : TrueSource2 R) (G : (Seed R)[X]) (r : Row2) : R :=
  (((((Q.coeff r.1).coeff r.2.1).coeff r.2.2.1) %ₘ G).coeff r.2.2.2.1).coeff r.2.2.2.2

private def rowsOfColumn2 (Q : TrueSource2 Parameter) (G : (Seed Parameter)[X]) : Finset Row2 :=
  Q.support.biUnion fun e₂ => (Q.coeff e₂).support.biUnion fun e₁ =>
    ((Q.coeff e₂).coeff e₁).support.biUnion fun e₀ =>
      let p := (((Q.coeff e₂).coeff e₁).coeff e₀) %ₘ G
      p.support.biUnion fun a => (p.coeff a).support.image fun e => (e₂, e₁, e₀, a, e)

private theorem mem_rowsOfColumn2 (Q : TrueSource2 Parameter) (G : (Seed Parameter)[X])
    (r : Row2) (hr : readRow2 Q G r ≠ 0) : r ∈ rowsOfColumn2 Q G := by
  obtain ⟨e₂, e₁, e₀, a, e⟩ := r
  refine Finset.mem_biUnion.mpr ⟨e₂, Polynomial.mem_support_iff.mpr (fun h => hr (by simp [readRow2, h])), ?_⟩
  refine Finset.mem_biUnion.mpr ⟨e₁, Polynomial.mem_support_iff.mpr (fun h => hr (by simp [readRow2, h])), ?_⟩
  refine Finset.mem_biUnion.mpr ⟨e₀, Polynomial.mem_support_iff.mpr (fun h => hr (by simp [readRow2, h])), ?_⟩
  refine Finset.mem_biUnion.mpr ⟨a, Polynomial.mem_support_iff.mpr (fun h => hr (by simp [readRow2, h])), ?_⟩
  exact Finset.mem_image.mpr ⟨e, MvPolynomial.mem_support_iff.mpr hr, rfl⟩

private theorem readRow2_map {F : Type} [Field F] (point : Parameter →+* F)
    (Q : TrueSource2 Parameter) {G : (Seed Parameter)[X]} (hG : G.Monic) (r : Row2) :
    readRow2 (mapSource2 point Q) (G.map (MvPolynomial.map point)) r = point (readRow2 Q G r) := by
  simp only [readRow2, mapSource2, jetMap2, coe_mapRingHom, Polynomial.coeff_map,
    ← map_modByMonic (MvPolynomial.map point) hG, MvPolynomial.coeff_map]

private def readRow2Linear {F : Type} [Field F] (G : (Seed F)[X]) (r : Row2) :
    TrueSource2 F →ₗ[F] F :=
  (MvPolynomial.lcoeff F r.2.2.2.2).comp <|
    ((Polynomial.lcoeff (Seed F) r.2.2.2.1).restrictScalars F).comp <|
    ((Polynomial.modByMonicHom G).restrictScalars F).comp <|
    ((Polynomial.lcoeff (Seed F)[X] r.2.2.1).restrictScalars F).comp <|
    ((Polynomial.lcoeff (Seed F)[X][X] r.2.1).restrictScalars F).comp <|
    (Polynomial.lcoeff (Seed F)[X][X][X] r.1).restrictScalars F

private theorem readRow2_sum {F ι : Type} [Field F] [Fintype ι]
    (Q : ι → TrueSource2 F) (v : ι → F) (G : (Seed F)[X]) (r : Row2) :
    readRow2 (∑ k, v k • Q k) G r = ∑ k, v k * readRow2 (Q k) G r := by
  change readRow2Linear G r (∑ k, v k • Q k) = ∑ k, v k • readRow2Linear G r (Q k)
  simp only [map_sum, map_smul]

private theorem dvd_iff_read2 {F : Type} [Field F] (Q : TrueSource2 F)
    {G : (Seed F)[X]} (hG : G.Monic) :
    (jetConstant2 (G.map (algebraMap (Seed F) (SeedFrac F))) : JetPolys2 (SeedFrac F)) ∣
      jetMap2 (algebraMap (Seed F) (SeedFrac F)) Q ↔
      ∀ r, readRow2 Q G r = 0 := by
  let f := algebraMap (Seed F) (SeedFrac F)
  have h : (jetConstant2 (G.map f) : JetPolys2 (SeedFrac F)) ∣ jetMap2 f Q ↔
      ∀ e₂ e₁ e₀, (((Q.coeff e₂).coeff e₁).coeff e₀) %ₘ G = 0 := by
    simp only [jetConstant2, RingHom.comp_apply, C_dvd_iff_dvd_coeff,
      jetMap2, coe_mapRingHom, Polynomial.coeff_map]
    apply forall_congr'; intro e₂
    apply forall_congr'; intro e₁
    apply forall_congr'; intro e₀
    rw [← modByMonic_eq_zero_iff_dvd (hG.map f), ← map_modByMonic f hG,
      Polynomial.map_eq_zero_iff (IsFractionRing.injective (Seed F) (SeedFrac F))]
  rw [h]
  constructor
  · intro hz r; simp [readRow2, hz]
  · intro hz e₂ e₁ e₀
    apply Polynomial.ext; intro a
    rw [Polynomial.coeff_zero]
    apply MvPolynomial.ext; intro e
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact hz (e₂, e₁, e₀, a, e)

private theorem matrix_of_columns_2jet {ι : Type} [Fintype ι]
    (Q : ι → TrueSource2 Parameter) (G : (Seed Parameter)[X]) (hG : G.Monic) :
    ∃ n : ℕ, ∃ M : Matrix (Fin n) ι Parameter,
      ∀ (F : Type) [Field F] (point : Parameter →+* F) (v : ι → F),
        (M.map point).mulVec v = 0 ↔
          (jetConstant2 (G.map (seedAt point)) : JetPolys2 (SeedFrac F)) ∣
            ∑ k, v k • jetMap2 (seedAt point) (Q k) := by
  classical
  let rows := Finset.univ.biUnion fun k => rowsOfColumn2 (Q k) G
  let e : Fin rows.card ≃ ↥rows := (Fintype.equivFinOfCardEq (Fintype.card_coe rows)).symm
  let M : Matrix (Fin rows.card) ι Parameter := fun r k => readRow2 (Q k) G (e r).val
  refine ⟨rows.card, M, ?_⟩
  intro F _ point v
  let inc := algebraMap (Seed F) (SeedFrac F)
  let incAlg : TrueSource2 F →ₐ[F] JetPolys2 (SeedFrac F) :=
    mapAlgHom (mapAlgHom (mapAlgHom (mapAlgHom (IsScalarTower.toAlgHom F (Seed F) (SeedFrac F)))))
  let G' := G.map (MvPolynomial.map point)
  let Q' : ι → TrueSource2 F := fun k => mapSource2 point (Q k)
  let q := ∑ k, v k • Q' k
  have hcomp (k : ι) : incAlg (Q' k) = jetMap2 (seedAt point) (Q k) := by
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    simp only [incAlg, Q', mapSource2, jetMap2, coe_mapRingHom, Polynomial.coeff_map,
      Polynomial.coeff_mapAlgHom_apply, seedAt, RingHom.comp_apply]
    rfl
  have hq : jetMap2 inc q = ∑ k, v k • jetMap2 (seedAt point) (Q k) := by
    change incAlg (∑ k, v k • Q' k) = _
    simp only [map_sum, map_smul, hcomp]
  have hGmap : G.map (seedAt point) = G'.map inc := by
    dsimp only [G', seedAt, inc]
    exact (Polynomial.map_map (MvPolynomial.map point) (algebraMap (Seed F) (SeedFrac F)) G).symm
  rw [← hq, hGmap, dvd_iff_read2 q (hG.map _)]
  have hread (r : Row2) : readRow2 q G' r = ∑ k, v k * point (readRow2 (Q k) G r) := by
    rw [readRow2_sum]
    simp only [Q', G', readRow2_map point _ hG]
  have heval (r : Fin rows.card) : ((M.map point).mulVec v) r = readRow2 q G' (e r).val := by
    rw [hread]
    change ∑ k, point (readRow2 (Q k) G (e r).val) * v k = _
    simp only [mul_comm]
  change (M.map point).mulVec v = 0 ↔ ∀ r, readRow2 q G' r = 0
  constructor
  · intro hv r
    by_cases hr : r ∈ rows
    · have he := congrFun hv (e.symm ⟨r, hr⟩)
      rw [heval] at he
      simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using he
    · rw [hread]
      apply Finset.sum_eq_zero; intro k _
      have hz : readRow2 (Q k) G r = 0 := by
        by_contra hn
        exact hr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, mem_rowsOfColumn2 _ _ _ hn⟩)
      rw [hz, map_zero, mul_zero]
  · intro hv
    funext r
    exact (heval r).trans (hv (e r).val)

private theorem deformation_matrix_2jet {h : ℕ} {D : PoleData h} {Crt : CRTLift D}
    (E : RegularDeformation D Crt) (s : Shape2) {ι : Type} [Fintype ι]
    (P : ι → Source2) (hP : ∀ k, Shaped2 s (P k)) :
    ∃ n : ℕ, ∃ M : Matrix (Fin n) ι Parameter,
      (∀ v : ι → L, (M.map specialPoint).mulVec v = 0 ↔
        PoleTest2 s (poleProduct D) (crtPolynomial Crt) (Fintype.linearCombination L P v)) ∧
      ∀ v : ι → GenericField, (M.map genericPoint).mulVec v = 0 ↔
        PoleTest2 s (E.H.map genericPoint) (liftAt genericPoint E.num E.den)
          (Fintype.linearCombination GenericField
            (fun k => mapSource2 (genericPoint.comp (Polynomial.C (R := L))) (P k)) v) := by
  classical
  let G := (E.H.map (MvPolynomial.C (σ := Fin 2))) ^ (s.B + s.J)
  obtain ⟨n, M, hM⟩ := matrix_of_columns_2jet (fun k => cleared2 s E.H E.num E.den (P k)) G
    ((E.monic.map _).pow _)
  have fibre {F : Type} [Field F] (point : Parameter →+* F)
      (hd : MvPolynomial.map point E.den ≠ 0) (v : ι → F) :
      (M.map point).mulVec v = 0 ↔
        PoleTest2 s (E.H.map point) (liftAt point E.num E.den)
          (Fintype.linearCombination F
            (fun k => mapSource2 (point.comp (Polynomial.C (R := L))) (P k)) v) := by
    let f := forward2 (E.H.map point) (liftAt point E.num E.den)
    let d := scalarJet2 (seedAt point E.den)
    have hu : IsUnit d := by
      have hn : seedAt point E.den ≠ 0 := by
        intro hzero
        exact hd (IsFractionRing.injective (Seed F) (SeedFrac F) (hzero.trans (map_zero _).symm))
      exact (isUnit_iff_ne_zero.mpr hn).map (jetConstant2.comp Polynomial.C)
    rw [hM F point v]
    simp only [cleared2_specializes point s E.H E.num E.den hd _ (hP _)]
    have hsum : (∑ k, v k • (d ^ s.B * f (mapSource2 (point.comp (Polynomial.C (R := L))) (P k)))) =
        d ^ s.B * f (Fintype.linearCombination F
          (fun k => mapSource2 (point.comp (Polynomial.C (R := L))) (P k)) v) := by
      simp only [Fintype.linearCombination_apply, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
    have hG : G.map (seedAt point) =
        ((E.H.map point).map (algebraMap F (SeedFrac F))) ^ (s.B + s.J) := by
      simp only [G, Polynomial.map_pow, map_abscissa]
    rw [hsum, (hu.pow s.B).dvd_mul_left, hG]
    rfl
  refine ⟨n, M, ?_, fibre genericPoint E.genericDen⟩
  intro v
  have hpoint : specialPoint.comp (Polynomial.C (R := L)) = RingHom.id L := by
    ext a; simp [specialPoint]
  have hmap (Q : Source2) : mapSource2 (RingHom.id L) Q = Q := by
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    simp only [mapSource2, jetMap2, coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.map_id]
  simpa only [E.specialH, E.specialLift, hpoint, hmap] using fibre specialPoint E.specialDen v

/-- Main Global 2-Jet Pole Rank Bound (`pole_bound_2jet`):
    exact 2-jet analog of `UpperBranch1.P1_7_1.pole_bound` — without `s.B < K1.p`! -/
theorem pole_bound_2jet {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape2) (W : ℕ) :
    Module.finrank L (contacted2 h word s W) ≤
      poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s +
        Module.finrank L (complete2 Crt word s W) := by
  classical
  obtain ⟨E⟩ := regular_deformation hpos hchar D Crt
  let A := contacted2 h word s W
  let _ : Module.Finite L A := contacted2_finite h word s W
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source2 := fun k => basis k
  have hP (k : Fin d) : Shaped2 s (P k) := contacted2_shaped (basis k).property
  obtain ⟨n, M, hspecial, hg⟩ := deformation_matrix_2jet E s P hP
  let embed := genericPoint.comp (Polynomial.C (R := L))
  have hgen := simple_rank_le_2jet E.genericPoles s _
    (fun k => shaped2_map embed (hP k)) _ hg
  have hrank := (specialization_rank_le M).trans hgen
  let f := (M.map specialPoint).mulVecLin
  have hf : ∀ v : Fin d → L,
      Fintype.linearCombination L P v = ((basis.equivFun.symm v : A) : Source2) := by
    intro v
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul, Submodule.subtype_apply, P] using
      map_sum A.subtype (fun k => v k • basis k) Finset.univ
  have hk (v : LinearMap.ker f) :
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source2) ∈ complete2 Crt word s W := by
    have hv := (hspecial v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property, hv⟩
  let g : LinearMap.ker f →ₗ[L] complete2 Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  let _ : Module.Finite L (complete2 Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : complete2 Crt word s W => (x : Source2)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ _
  omega

#print axioms pole_bound_2jet

end
end PoleBound2Jet
