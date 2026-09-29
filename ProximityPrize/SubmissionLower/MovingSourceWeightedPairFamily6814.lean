import ProximityPrize.SubmissionLower.MovingSourceWeightedProjection6814

/-! One pole-exact projection family carries both the ordinary zero
budget and the proved multiplicity-weighted pair budget. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWeightedPairFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 700000
open scoped BigOperators Classical
open RCN002 RCN022 RCN032 RCN037 RCN042 RCN046 RCN093 RCN095 RCN116 RCN264 RCN338 RCN341 RCN344
open MovingSourceProjectionFamily6814 MovingSourcePoleBudget6814 MovingSourceAutomaticProjection6814
open MovingSourceWeightedProjection6814
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
local instance : DecidableEq Ω := Classical.decEq Ω
variable {G H A M B C : MvPolynomial (Fin 3) Ω}

def weighted_pair_certificate
    (base : ∀ V : RegularComponent Ω G M (H*A), SeparableLiteralCoordinate V.1)
    (hY : ∀ V : RegularComponent Ω G M (H*A), LiteralProjectionGate V 0)
    (hZ : ∀ V : RegularComponent Ω G M (H*A), LiteralProjectionGate V 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (D : AdaptiveNestedProjectionData base hY hZ hderiv)
    (hG : G≠0) (hB : B≠0) (hC : C≠0) (hcop : IsRelPrime B C)
    (d : ℕ) (hd : 0<d) (thick : HasThickness G H A M B C d)
    (p q : FlagDegree) (hp : RCN095.PolynomialInFlag p B) (hq : RCN095.PolynomialInFlag q C) :
    let unit := projectionFamily_of_coprime_pair base hY hZ hderiv D B C hB hC hcop
      (fun V => (thick.mem_regular hd V).1) (fun V => (thick.mem_regular hd V).2) p q hp hq
    RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d) := by
  let x (axis : Axis) (V : RegularComponent Ω G M (H*A)) :=
    flagEvaluation Ω V.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0))
  have gate (axis : Axis) (V : RegularComponent Ω G M (H*A)) (ht : Transcendental Ω (x axis V)) :
      (letI := (elementEmbedding Ω (CoordinateField Ω V.1) (x axis V) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω V.1)) ∧
      (letI := (elementEmbedding Ω (CoordinateField Ω V.1) (x axis V) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω V.1)) := by
    cases axis with
    | z =>
      have hz : Transcendental Ω (coordinate Ω V.1 2) := by simpa [x,Axis.order,RCN125.zOrder] using ht
      have he := elementEmbedding_congr ht hz (by simp [x,Axis.order,RCN125.zOrder])
      rw [he]
      exact hZ V hz
    | u =>
      have hu : Transcendental Ω (affineU Ω V.1 D.lam) := by simpa [x,Axis.order,RCN125.uOrder] using ht
      have he := elementEmbedding_congr ht hu (by simp [x,Axis.order,RCN125.uOrder])
      rw [he]
      exact D.uGate V hu
    | v =>
      have he := elementEmbedding_congr ht (D.allAffineTranscendental V) (by simp [x,Axis.order,RCN125.vOrder])
      rw [he]
      exact ⟨D.allFinite V,D.allSeparable V⟩
  have hsum (axis : Axis) :
      (∑ V : RegularComponent Ω G M (H*A), d*coordinateDegree Ω (CoordinateField Ω V.1)
        (coordinateOfGate (x axis V) (gate axis V)))≤flagMixed p q axis.flag := by
    rw [sum_mul_coordinateOfGate_eq_active
      (fun V : RegularComponent Ω G M (H*A) => CoordinateField Ω V.1)
      (x axis) (gate axis) (fun _ => d)]
    have hh := weighted_directional_degree G H A M B C hG hB hC hcop d hd thick
      (fun V : {V : RegularComponent Ω G M (H*A) // Transcendental Ω (x axis V)} => V.1)
      Subtype.val_injective axis D.lam D.mu (D.mu*D.lam) (fun V => V.2)
      (fun V => gate axis V.1) p q hp hq
    simpa only [Finset.mul_sum] using hh
  exact { z := hsum .z, yz := hsum .u, all := hsum .v }

theorem exists_weighted_pair_family
    (G H A M B C : MvPolynomial (Fin 3) Ω)
    (hG : G≠0) (hB : B≠0) (hC : C≠0) (hcop : IsRelPrime B C)
    (d : ℕ) (hd : 0<d) (thick : HasThickness G H A M B C d)
    (p q : FlagDegree) (hp : RCN095.PolynomialInFlag p B) (hq : RCN095.PolynomialInFlag q C)
    (c : ℕ) [CharP Ω c]
    (hZsmall : flagMixed p q unitZFlag<c) (hYsmall : flagMixed p q unitYZFlag<c)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0) :
    ∃ base : ∀ V : RegularComponent Ω G M (H*A), SeparableLiteralCoordinate V.1,
      ∃ unit : AdaptiveUnitProjectionFamily base p q,
        Nonempty (RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d)) := by
  have mems (V : RegularComponent Ω G M (H*A)) := thick.mem_regular hd V
  have hY (V : RegularComponent Ω G M (H*A)) : LiteralProjectionGate V 0 := by
    intro ht
    have ht' : Transcendental Ω (flagEvaluation Ω V.1 0 0 0 (MvPolynomial.X (Axis.u.order 0))) := by
      simpa [Axis.order,RCN125.uOrder,affineU] using ht
    have he := elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.uOrder,affineU])
    have hh := prime_projection_gate V.1 .u 0 0 0 ht' B C hB hC hcop
      (mems V).1 (mems V).2 p q hp hq c hYsmall
    rw [he] at hh
    exact hh
  have hZ (V : RegularComponent Ω G M (H*A)) : LiteralProjectionGate V 2 := by
    intro ht
    have ht' : Transcendental Ω (flagEvaluation Ω V.1 0 0 0 (MvPolynomial.X (Axis.z.order 0))) := by
      simpa [Axis.order,RCN125.zOrder] using ht
    have he := elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.zOrder])
    have hh := prime_projection_gate V.1 .z 0 0 0 ht' B C hB hC hcop
      (mems V).1 (mems V).2 p q hp hq c hZsmall
    rw [he] at hh
    exact hh
  let base (V : RegularComponent Ω G M (H*A)) : SeparableLiteralCoordinate V.1 :=
    Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates V.1
      (regularComponent_ne_point Ω G M (H*A) V) (hY V) (hZ V))
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hY hZ hderiv
  let unit := projectionFamily_of_coprime_pair base hY hZ hderiv D B C hB hC hcop
    (fun V => (mems V).1) (fun V => (mems V).2) p q hp hq
  exact ⟨base,unit,⟨weighted_pair_certificate base hY hZ hderiv D hG hB hC hcop d hd thick p q hp hq⟩⟩

#print axioms weighted_pair_certificate
#print axioms exists_weighted_pair_family
end
end ProximityPrize.SubmissionLower.MovingSourceWeightedPairFamily6814
