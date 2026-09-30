import ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814
namespace ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN093 RCN095 RCN135 RCN136 RCN238 RCN243 RCN264
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
open MovingSourceProperSeedCount6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814

theorem constant_parameter_seeds_le_one
    {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
    (phi : Polynomial K →+* Ω) (selected : K → Polynomial K) (seeds : Finset K)
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (hconstant : IsAlgebraic Ω (coordinate Ω P 2))
    (hon : ∀ gamma∈seeds, P≤RingHom.ker (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom) :
    seeds.card≤1 := by
  obtain ⟨c,hc⟩ := RCN370.eq_algebraMap_of_isAlgebraic Ω (CoordinateField Ω P) _ hconstant
  have hmem : MvPolynomial.X (2 : Fin 3)-MvPolynomial.C c∈P := by
    rw [←coordinateEvaluation_ker Ω P]
    change coordinateEvaluation Ω P (MvPolynomial.X 2-MvPolynomial.C c)=0
    rw [coordinateEvaluation_eq_aeval]
    simpa using sub_eq_zero.mpr hc.symm
  have hvalue (gamma : K) (hgamma : gamma∈seeds) : (phi.comp Polynomial.C) gamma=c := by
    have hh := hon gamma hgamma hmem
    change MvPolynomial.aeval (selectedPoint phi selected gamma)
      (MvPolynomial.X (2 : Fin 3)-MvPolynomial.C c)=0 at hh
    simpa only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
      Algebra.algebraMap_self,RingHom.id_apply,selectedPoint_seed,sub_eq_zero] using hh
  apply Finset.card_le_one.mpr
  intro gamma hgamma eta heta
  exact (phi.comp Polynomial.C).injective ((hvalue gamma hgamma).trans (hvalue eta heta).symm)

theorem card_primes_le_direction
    {Ω : Type} [Field Ω] {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (hinj : Function.Injective P) (axis : Axis)
    (ht : ∀ a, Transcendental Ω
      (flagEvaluation Ω (P a) 0 0 0 (MvPolynomial.X (axis.order 0))))
    (F N : MvPolynomial (Fin 3) Ω) (hF : F≠0) (hN : N≠0) (hrel : IsRelPrime F N)
    (hFmem : ∀ a,F∈P a) (hNmem : ∀ a,N∈P a)
    (p q : FlagDegree) (hp : PolynomialInFlag p F) (hq : PolynomialInFlag q N) :
    Fintype.card A≤flagMixed p q axis.flag := by
  letI : ∀ a, Algebra (RatFunc Ω) (CoordinateField Ω (P a)) := fun a =>
    (elementEmbedding Ω (CoordinateField Ω (P a))
      (flagEvaluation Ω (P a) 0 0 0 (MvPolynomial.X (axis.order 0))) (ht a)).toRingHom.toAlgebra
  have hb := finite_sum_prime_fields Ω axis 0 0 0 P hinj ht F N hF hN hrel hFmem hNmem p q hp hq
  calc
    Fintype.card A=∑ _ : A, 1 := by simp
    _≤∑ a : A, Module.finrank (RatFunc Ω) (CoordinateField Ω (P a)) := by
      apply Finset.sum_le_sum
      intro a _
      letI := hb.1 a
      exact Module.finrank_pos
    _≤_ := hb.2

theorem constant_prime_family_card_le
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (hinj : Function.Injective P)
    (hnonpoint : ∀ a, ∀ v : Fin 3 → Ω, P a≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hconstant : ∀ a, IsAlgebraic Ω (coordinate Ω (P a) 2))
    (F N : MvPolynomial (Fin 3) Ω) (hF : F≠0) (hN : N≠0) (hrel : IsRelPrime F N)
    (hFmem : ∀ a,F∈P a) (hNmem : ∀ a,N∈P a)
    (p q : FlagDegree) (hp : PolynomialInFlag p F) (hq : PolynomialInFlag q N) :
    Fintype.card A≤flagMixed p q unitYZFlag+flagMixed p q unitAllFlag := by
  let activeY (a : A) := Transcendental Ω (coordinate Ω (P a) 0)
  have hr (a : A) (ha : ¬activeY a) : Transcendental Ω (coordinate Ω (P a) 1) := by
    obtain ⟨i,hi⟩ := exists_transcendental_coordinate_of_ne_point_kernel Ω (P a) (hnonpoint a)
    fin_cases i
    · exact False.elim (ha hi)
    · exact hi
    · exact False.elim (hi (hconstant a))
  have hycap : Fintype.card {a : A // activeY a}≤flagMixed p q unitYZFlag :=
    card_primes_le_direction (fun a : {a : A // activeY a} => P a.1)
      (fun a b h => Subtype.ext (hinj h)) .u
      (fun a => by simpa [Axis.order,RCN125.uOrder,affineU] using a.2)
      F N hF hN hrel (fun a => hFmem a.1) (fun a => hNmem a.1) p q hp hq
  have hrcap : Fintype.card {a : A // ¬activeY a}≤flagMixed p q unitAllFlag :=
    card_primes_le_direction (fun a : {a : A // ¬activeY a} => P a.1)
      (fun a b h => Subtype.ext (hinj h)) .v
      (fun a => by simpa [Axis.order,RCN125.vOrder,affineV] using hr a.1 a.2)
      F N hF hN hrel (fun a => hFmem a.1) (fun a => hNmem a.1) p q hp hq
  have hcomp := Fintype.card_subtype_compl activeY
  have hle : Fintype.card {a : A // activeY a}≤Fintype.card A :=
    Fintype.card_le_of_injective (fun a : {a : A // activeY a} => a.1) Subtype.val_injective
  omega

open RCN074 RCN086 RCN244
variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev ConstantComponent (S : Stage K I Gamma x p flag errorCap stageSupport) :=
  {C : FirstTailComponent S // IsAlgebraic (GenericField K) (coordinate (GenericField K) C.1 2)}

end
end ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814
