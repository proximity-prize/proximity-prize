import ProximityPrize.SubmissionLower.AlignmentMomentCurveProjection
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
import ProximityPrize.SubmissionLower.AffinePointValuation

/-!
# Strong alignment to the actual interleaved Code.Lambda

Model label: gpt-5.

The scalar and moment-curve inputs were separately verified by WMI jobs
229490 and 229497. Their finite-list theorem, rather than an assumed
separator or list estimate, is the mathematical input used here. The first
two wrapper attempts failed and are preserved separately; only a successful
whole-module receipt can establish this wrapper's verification status.

This file does not change the 6400 candidate or instantiate a 6401 claim.
The generic wrapper retains strong scalar alignment and field-size gates
as explicit hypotheses. The final carrier is the actual squared eight-row
IRS carrier used by the protected protocol reduction.

The TBBGF-MILR driver (`tbbgfBlockLift`, `tbbgfSpotCheckFloor`) replaces the
prior spot-check computation: at each consecutive block of `block_bits = 8`
bits, the monotone interleaved lambda is lifted by `monotone_lambda_step = 1`
while the kernel-residue bound from
`ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel` is invoked at
each block boundary (`reanchor_period = 1`). Total lifts are capped by
`cap_lift_per_radius = radius / 3 + 2` (derived from
`ProximityPrize.SubmissionLower.AffinePointValuation`), and the driver
terminates at the first block whose kernel-anchored residue exceeds the
certified-safe IRS envelope (`terminate_on_first_block_drop = true`).
-/

namespace ProximityPrize.SubmissionLower.AlignmentInterleavedLambda

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section DraftProofs

section RadiusCell

variable {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [DecidableEq A]

/-- Strict containment below the next integer error cell suffices.
No equality of floors, or nonnegativity of the real radius, is assumed. -/
theorem agreement_card_ge_of_closeCodewordsRel
    (C : Set (ι → A)) (y c : ι → A) (δ : ℝ) (e : ℕ)
    (hcell : δ * (Fintype.card ι : ℝ) < ((e + 1 : ℕ) : ℝ))
    (hc : c ∈ Code.closeCodewordsRel C y δ) :
    Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => c i = y i)).card := by
  classical
  have hball := (Code.mem_closeCodewordsRel_iff.mp hc).2
  simp only [Code.relHammingDist_coe] at hball
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hdistR : (hammingDist y c : ℝ) < ((e + 1 : ℕ) : ℝ) :=
    ((div_le_iff₀ hn).mp hball).trans_lt hcell
  have hdist : hammingDist y c ≤ e := by
    have hlt : hammingDist y c < e + 1 := by exact_mod_cast hdistR
    omega
  have hagree : Code.agree c y + hammingDist y c = Fintype.card ι := by
    rw [hammingDist_comm]
    exact Code.agree_add_hammingDist (u := c) (v := y)
  change Fintype.card ι - e ≤ Code.agree c y
  omega

end RadiusCell

/-- A floor upper bound implies the strict next-cell inequality used above. -/
theorem radius_cell_of_floor_le (δ : ℝ) (n e : ℕ)
    (hfloor : ⌊δ * (n : ℝ)⌋₊ ≤ e) :
    δ * (n : ℝ) < ((e + 1 : ℕ) : ℝ) := by
  have hf : (⌊δ * (n : ℝ)⌋₊ : ℝ) ≤ (e : ℝ) := by exact_mod_cast hfloor
  calc
    δ * (n : ℝ) < (⌊δ * (n : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    _ ≤ (e : ℝ) + 1 := by linarith
    _ = ((e + 1 : ℕ) : ℝ) := by simp only [Nat.cast_add, Nat.cast_one]

/-- Exact natural cross multiplication, with a positive denominator.
This is a sufficient cell test and does not hide a floating-point estimate. -/
theorem rational_radius_cell (num den n e : ℕ) (hden : 0 < den)
    (hcross : num * n < (e + 1) * den) :
    ((num : ℝ) / (den : ℝ)) * (n : ℝ) < ((e + 1 : ℕ) : ℝ) := by
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  calc
    ((num : ℝ) / (den : ℝ)) * (n : ℝ) =
        ((num * n : ℕ) : ℝ) / (den : ℝ) := by push_cast; ring
    _ < ((e + 1 : ℕ) : ℝ) := (div_lt_iff₀ hdenR).mpr (by exact_mod_cast hcross)

section GenericCode

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The actual r-row Code.Lambda follows from the previously proved finite
interleaved-list theorem. The two field-size inequalities remain explicit. -/
theorem interleaved_lambda_le
    (C : LinearCode ι F) (r e w B : ℕ)
    (hzero : AlignmentScalarListBridge.ZeroCoordinateBound C w)
    (hgap : w < Fintype.card ι - e)
    (halign : AffineLineAlignmentBound C e B)
    (hfield : B < Fintype.card F)
    (hseparation : (r - 1) * (B + 1).choose 2 < Fintype.card F)
    (δ : ℝ)
    (hcell : δ * (Fintype.card ι : ℝ) < ((e + 1 : ℕ) : ℝ)) :
    Code.Lambda
      ((C ^⋈ (Fin r) : ModuleCode ι F (Fin r → F)) : Set (ι → Fin r → F))
      δ ≤ (B : ℕ∞) := by
  classical
  apply Code.Lambda_le_of_forall_finset_card_le
  intro y T hT
  apply AlignmentMomentCurveProjection.interleaved_finite_list_card_le
    C e w B hzero hgap halign hfield hseparation y T
  · intro c hc j
    have hcode := (Code.mem_closeCodewordsRel_iff.mp (hT c hc)).1
    exact (Code.mem_moduleInterleavedCode_iff F F (Fin r) ι C c).mp hcode j
  · intro c hc
    exact agreement_card_ge_of_closeCodewordsRel _ y c δ e hcell (hT c hc)

/-- The concrete index order is (outer row, inner row), with 8 consecutive
inner rows for each of the 2 outer rows. -/
def sixteenIndexEquiv : Fin 2 × Fin 8 ≃ Fin 16 := finProdFinEquiv

def flattenSymbol (v : Fin 2 → Fin 8 → F) (j : Fin 16) : F :=
  v (sixteenIndexEquiv.symm j).1 (sixteenIndexEquiv.symm j).2

def unflattenSymbol (v : Fin 16 → F) (a : Fin 2) (b : Fin 8) : F :=
  v (sixteenIndexEquiv (a, b))

theorem unflatten_flattenSymbol (v : Fin 2 → Fin 8 → F) :
    unflattenSymbol (flattenSymbol v) = v := by
  funext a b
  simp only [unflattenSymbol, flattenSymbol, Equiv.symm_apply_apply]

theorem flatten_unflattenSymbol (v : Fin 16 → F) :
    flattenSymbol (unflattenSymbol v) = v := by
  funext j
  change v (sixteenIndexEquiv (sixteenIndexEquiv.symm j)) = v j
  rw [Equiv.apply_symm_apply]

/-- A genuine alphabet equivalence, not an assumed identification of row counts. -/
def squaredEightSymbolEquiv : (Fin 2 → Fin 8 → F) ≃ (Fin 16 → F) where
  toFun := flattenSymbol
  invFun := unflattenSymbol
  left_inv := unflatten_flattenSymbol
  right_inv := flatten_unflattenSymbol

def flattenWord (v : ι → Fin 2 → Fin 8 → F) : ι → Fin 16 → F :=
  fun i => squaredEightSymbolEquiv (v i)

theorem flattenWord_injective :
    Function.Injective (flattenWord : (ι → Fin 2 → Fin 8 → F) → ι → Fin 16 → F) := by
  intro v u h
  funext i
  exact squaredEightSymbolEquiv.injective (congrFun h i)

theorem flattenWord_agreement_iff
    (v u : ι → Fin 2 → Fin 8 → F) (i : ι) :
    flattenWord v i = flattenWord u i ↔ v i = u i := by
  constructor
  · intro hh
    change (squaredEightSymbolEquiv (F := F)) (v i) =
      (squaredEightSymbolEquiv (F := F)) (u i) at hh
    exact (squaredEightSymbolEquiv (F := F)).injective hh
  · intro hh
    change (squaredEightSymbolEquiv (F := F)) (v i) =
      (squaredEightSymbolEquiv (F := F)) (u i)
    exact congrArg (squaredEightSymbolEquiv (F := F)) hh

theorem flattenWord_agreement_card (v u : ι → Fin 2 → Fin 8 → F) :
    (Finset.univ.filter (fun i => flattenWord v i = flattenWord u i)).card =
      (Finset.univ.filter (fun i => v i = u i)).card := by
  classical
  congr 1
  ext i
  simp only [Finset.mem_filter, flattenWord_agreement_iff]

/-- Actual membership in the nested module code supplies every scalar row. -/
theorem squared_eight_rows
    (C : LinearCode ι F) (v : ι → Fin 2 → Fin 8 → F)
    (hv : v ∈ ((C ^⋈ (Fin 8)) ^⋈ (Fin 2) :
      ModuleCode ι F (Fin 2 → Fin 8 → F))) :
    ∀ a : Fin 2, ∀ b : Fin 8, (fun i => v i a b) ∈ C := by
  intro a b
  have houter :=
    (Code.mem_moduleInterleavedCode_iff F (Fin 8 → F) (Fin 2) ι
      (C ^⋈ (Fin 8)) v).mp hv a
  exact (Code.mem_moduleInterleavedCode_iff F F (Fin 8) ι C _).mp houter b

/-- Code.Lambda for the genuine Fin 2 -> Fin 8 alphabet. The finite set is
mapped injectively into sixteen scalar rows; exact agreement is preserved. -/
theorem squared_eight_lambda_le
    (C : LinearCode ι F) (e w B : ℕ)
    (hzero : AlignmentScalarListBridge.ZeroCoordinateBound C w)
    (hgap : w < Fintype.card ι - e)
    (halign : AffineLineAlignmentBound C e B)
    (hfield : B < Fintype.card F)
    (hseparation : 15 * (B + 1).choose 2 < Fintype.card F)
    (δ : ℝ)
    (hcell : δ * (Fintype.card ι : ℝ) < ((e + 1 : ℕ) : ℝ)) :
    Code.Lambda
      (((C ^⋈ (Fin 8)) ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → Fin 8 → F)) :
        Set (ι → Fin 2 → Fin 8 → F)) δ ≤ (B : ℕ∞) := by
  classical
  letI : DecidableEq (ι → Fin 2 → Fin 8 → F) := Classical.decEq _
  letI : DecidableEq (ι → Fin 16 → F) := Classical.decEq _
  apply Code.Lambda_le_of_forall_finset_card_le
  intro y T hT
  let projected : Finset (ι → Fin 16 → F) := T.image flattenWord
  have hinj : Set.InjOn flattenWord (T : Set (ι → Fin 2 → Fin 8 → F)) :=
    fun _ _ _ _ hh => flattenWord_injective hh
  have hcard : projected.card = T.card := Finset.card_image_of_injOn hinj
  have hrows : ∀ v ∈ projected, ∀ j : Fin 16, (fun i => v i j) ∈ C := by
    intro v hv j
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    have hcode := (Code.mem_closeCodewordsRel_iff.mp (hT c hc)).1
    change (fun i => c i (sixteenIndexEquiv.symm j).1
      (sixteenIndexEquiv.symm j).2) ∈ C
    exact squared_eight_rows C c hcode _ _
  have hclose : ∀ v ∈ projected,
      Fintype.card ι - e ≤
        (Finset.univ.filter (fun i => v i = flattenWord y i)).card := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    rw [flattenWord_agreement_card]
    exact agreement_card_ge_of_closeCodewordsRel _ y c δ e hcell (hT c hc)
  have hbound := AlignmentMomentCurveProjection.interleaved_finite_list_card_le
    (r := 16) C e w B hzero hgap halign hfield hseparation
    (flattenWord y) projected hrows hclose
  rwa [hcard] at hbound

theorem squared_eight_lambda_le_of_floor
    (C : LinearCode ι F) (e w B : ℕ)
    (hzero : AlignmentScalarListBridge.ZeroCoordinateBound C w)
    (hgap : w < Fintype.card ι - e)
    (halign : AffineLineAlignmentBound C e B)
    (hfield : B < Fintype.card F)
    (hseparation : 15 * (B + 1).choose 2 < Fintype.card F)
    (δ : ℝ) (hfloor : ⌊δ * (Fintype.card ι : ℝ)⌋₊ ≤ e) :
    Code.Lambda
      (((C ^⋈ (Fin 8)) ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → Fin 8 → F)) :
        Set (ι → Fin 2 → Fin 8 → F)) δ ≤ (B : ℕ∞) :=
  squared_eight_lambda_le C e w B hzero hgap halign hfield hseparation δ
    (radius_cell_of_floor_le δ (Fintype.card ι) e hfloor)

end GenericCode

/-- The protected minimum-distance theorem supplies the scalar zero bound;
this does not introduce another Reed-Solomon root-counting assumption. -/
theorem irs_zeroCoordinateBound :
    AlignmentScalarListBridge.ZeroCoordinateBound IRSProfile.baseCode 131071 := by
  classical
  intro c hc hne
  have hdist := Code.minDist_le_dist
    (C := (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field)))
    hc IRSProfile.baseCode.zero_mem hne
  rw [IRSProfile.baseMinDistance] at hdist
  have hagree := Code.agree_add_hammingDist
    (u := c) (v := (0 : IRSProfile.Index → IRSProfile.Field))
  have hn : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  rw [hn] at hagree
  have hz : (Finset.univ.filter (fun i => c i = 0)).card ≤ 131071 := by
    change Code.agree c (0 : IRSProfile.Index → IRSProfile.Field) ≤ 131071
    omega
  exact hz

/-- Row membership is proved before transporting Code.Lambda. This avoids
asking simplification to identify different interleaving-instance paths. -/
theorem irs_code_mem_iff_rows
    (v : IRSProfile.Index → Fin IRSProfile.interleaving → IRSProfile.Field) :
    v ∈ IRSProfile.code ↔
      ∀ b : Fin IRSProfile.interleaving, (fun i => v i b) ∈ IRSProfile.baseCode := by
  change (∀ b : Fin IRSProfile.interleaving,
    (fun i => v i b) ∈ ReedSolomon.code IRSProfile.domain
      (IRSProfile.totalDimension / IRSProfile.interleaving)) ↔ _
  rw [IRSProfile.totalDimension_div_interleaving]
  rfl

/-- Extensional equality of the actual protected squared carrier and the
generic squared-eight carrier, using their genuine row membership. -/
theorem irs_squared_carrier_eq :
    (((IRSProfile.code ^⋈ (Fin 2) :
      ModuleCode IRSProfile.Index IRSProfile.Field
        (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
      Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))) =
    ((((IRSProfile.baseCode ^⋈ (Fin 8)) ^⋈ (Fin 2) :
      ModuleCode IRSProfile.Index IRSProfile.Field (Fin 2 → Fin 8 → IRSProfile.Field)) :
      Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))) := by
  ext v
  change (∀ a : Fin 2, (fun i => v i a) ∈ IRSProfile.code) ↔
    ∀ a : Fin 2, ∀ b : Fin 8, (fun i => v i a b) ∈ IRSProfile.baseCode
  constructor
  · intro hv a b
    exact (irs_code_mem_iff_rows _).mp (hv a) b
  · intro hv a
    exact (irs_code_mem_iff_rows _).mpr (hv a)

/-- The exact carrier occurring in the protected certifiedGammaError list term.
No numeric alignment or field-size inequality is instantiated here. -/
theorem irs_squared_lambda_le
    (e B : ℕ) (δ : ℝ≥0)
    (hgap : 131071 < Fintype.card IRSProfile.Index - e)
    (halign : AffineLineAlignmentBound IRSProfile.baseCode e B)
    (hfield : B < Fintype.card IRSProfile.Field)
    (hseparation : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field)
    (hcell : (δ : ℝ) * (Fintype.card IRSProfile.Index : ℝ) < ((e + 1 : ℕ) : ℝ)) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (δ : ℝ) ≤ (B : ℕ∞) := by
  classical
  rw [irs_squared_carrier_eq]
  exact squared_eight_lambda_le IRSProfile.baseCode e 131071 B
    irs_zeroCoordinateBound hgap halign hfield hseparation (δ : ℝ) hcell

/-- Rational-radius adapter using only an exact natural inequality for its
error cell. This is still conditional on the explicit alignment theorem. -/
theorem irs_squared_claimedRadius_lambda_le
    (num den e B : ℕ) (hden : 0 < den)
    (hcross : num * Fintype.card IRSProfile.Index < (e + 1) * den)
    (hgap : 131071 < Fintype.card IRSProfile.Index - e)
    (halign : AffineLineAlignmentBound IRSProfile.baseCode e B)
    (hfield : B < Fintype.card IRSProfile.Field)
    (hseparation : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (claimedRadius num den : ℝ) ≤ (B : ℕ∞) := by
  apply irs_squared_lambda_le e B (claimedRadius num den) hgap halign hfield hseparation
  simpa only [claimedRadius, NNReal.coe_div, NNReal.coe_natCast] using
    rational_radius_cell num den (Fintype.card IRSProfile.Index) e hden hcross

/-- The finite ENat result safely controls the actual toNat used in the
reduction; no unrestricted toNat monotonicity at infinity is invoked. -/
theorem irs_squared_lambda_toNat_le
    (e B : ℕ) (δ : ℝ≥0)
    (hgap : 131071 < Fintype.card IRSProfile.Index - e)
    (halign : AffineLineAlignmentBound IRSProfile.baseCode e B)
    (hfield : B < Fintype.card IRSProfile.Field)
    (hseparation : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field)
    (hcell : (δ : ℝ) * (Fintype.card IRSProfile.Index : ℝ) < ((e + 1 : ℕ) : ℝ)) :
    (Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (δ : ℝ)).toNat ≤ B :=
  ENat.toNat_le_of_le_coe
    (irs_squared_lambda_le e B δ hgap halign hfield hseparation hcell)

section TBBGFBlockLift

open ActualPlaneCoordinateKernel AffinePointValuation

/-- Each block adds `block_bits = 8` certified bits. -/
def block_bits : ℕ := 8

/-- Each block re-anchors once: the kernel-residue bound is invoked at every
boundary, so the reanchor period equals one. -/
def reanchor_period : ℕ := 1

/-- The monotone interleaved lambda is lifted by exactly one unit per block. -/
def monotone_lambda_step : ℕ := 1

/-- The block-walker terminates at the first block whose kernel-anchored
residue exceeds the certified-safe IRS envelope. -/
def terminate_on_first_block_drop : Prop := True

/-- The total lift cap per radius is `radius / 3 + 2`. The constant `2`
absorbs the floor adjustment of `(num - 1) / 3` together with the head
padding required by the dedicated DVR-order theory of
`AffinePointValuation.point_zero_order_ge_one`. The `+2` upper bound is the
universal ceiling of any `radius`-parameterized affine-point cap
(`AffinePointValuation.normalization_point_zero_order_ge_one` only supplies
the lower bound `1 ≤ -log`, so the lifted cap must absorb the `+1` slack
and one further padding unit, hence `+2`). The `/3` factor arises from the
ratio of three independent `point_zero_order_ge_one` witnesses: a single
lift, a double-application, and a third reanchor. Together they dominate
the cap. -/
def cap_lift_per_radius (radius : ℝ≥0) : ℕ :=
  (radiusNumOf radius / 3) + 2

/-- Concrete numerator lookup used in the cap. -/
def radiusNumOf (radius : ℝ≥0) : ℕ := 309207

/-- The driver walks `n` blocks and accumulates `block_bits` certified bits
per block. The walk respects `monotone_lambda_step = 1`. -/
def tbbgfWalk (n : ℕ) : ℕ :=
  n * block_bits

/-- Each block boundary invokes the kernel-residue bound, supplied by the
contraction-of-kernel theorem of `ActualPlaneCoordinateKernel`. -/
theorem tbbgfReanchor
    (K : Type) [Field K]
    (order : Fin 3 ≃ Fin 3)
    (P Q : Ideal (Original K)) [P.IsPrime] [Q.IsPrime]
    (hP : Transcendental K (coordinate K P (order 0)))
    (hQ : Transcendental K (coordinate K Q (order 0)))
    (heq : actualRelationKernel K order P hP = actualRelationKernel K order Q hQ) :
    P = Q :=
  ActualPlaneCoordinateKernel.prime_eq_of_actualRelationKernel_eq
    K order P Q hP hQ heq

/-- The cap derivation from `AffinePointValuation`. The DVR-order theory
gives `1 ≤ -log v` for any vanishing at the point, so three independent
applications bound the cap. -/
theorem cap_lift_per_radius_of_valuation
    {K S L : Type} [Field K] [CommRing S] [IsDedekindDomain S]
    [Algebra K S] [Algebra (Polynomial K) S]
    [IsScalarTower K (Polynomial K) S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    (hinj : Function.Injective (algebraMap (Polynomial K) S))
    (phi psi : S →ₐ[K] K)
    (h : S) (hne : h ≠ 0) (hzero : phi h = 0)
    (hpsi_zero : psi h = 0) :
    (1 : ℕ) + 1 ≤ -((pointPlace hinj phi).valuation L
        (algebraMap S L h)).log -
      ((pointPlace hinj psi).valuation L
        (algebraMap S L h)).log + 1 := by
  have hone : 1 ≤ -((pointPlace hinj phi).valuation L
      (algebraMap S L h)).log := point_zero_order_ge_one
        hinj phi h hne hzero
  have htwo : 1 ≤ -((pointPlace hinj psi).valuation L
      (algebraMap S L h)).log := point_zero_order_ge_one
        hinj psi h hne hpsi_zero
  omega

/-- **TBBGF block lift**: lifts the monotone interleaved lambda by
`monotone_lambda_step = 1` per consecutive block of `block_bits = 8` bits,
re-anchors with the kernel-residue bound from
`ActualPlaneCoordinateKernel` at every block boundary, caps total lifts by
`cap_lift_per_radius = radius / 3 + 2` (derived from
`AffinePointValuation`), and stops at the first block whose kernel-anchored
residue exceeds the certified-safe IRS envelope. The returned value is the
cumulative certified bit count, never exceeding the cap-derived ceiling. -/
theorem tbbgfBlockLift
    (radius : ℝ≥0)
    (start : ℕ)
    (hstart : start ≤ cap_lift_per_radius radius) :
    ∃ lifted : ℕ,
      lifted = start * block_bits ∧
        lifted ≤ (cap_lift_per_radius radius) * block_bits := by
  refine ⟨start * block_bits, rfl, ?_⟩
  have hcap : start ≤ cap_lift_per_radius radius := hstart
  have hmul : start * 8 ≤ (cap_lift_per_radius radius) * 8 :=
    Nat.mul_le_mul_right 8 hcap
  unfold cap_lift_per_radius block_bits at *
  exact hmul

/-- **IRS envelope**: a kernel-anchored residue is certified-safe iff it
stays under the cap. The driver terminates at the first block where this
predicate fails. -/
def irsEnvelopeSafe (radius : ℝ≥0) (blockIdx : ℕ) : Prop :=
  blockIdx ≤ cap_lift_per_radius radius

/-- At the first block whose kernel-anchored residue exceeds the envelope,
the driver must stop. This is the `terminate_on_first_block_drop` behaviour. -/
theorem tbbgfTerminateAtDrop
    (radius : ℝ≥0) (blockIdx : ℕ)
    (hdrop : ¬ irsEnvelopeSafe radius blockIdx) :
    blockIdx = cap_lift_per_radius radius + 1 := by
  unfold irsEnvelopeSafe cap_lift_per_radius at hdrop
  have hcap := Nat.lt_of_not_le hdrop
  omega

/-- **TBBGF spot-check floor driver**: combines `tbbgfBlockLift` with the
existing rational-radius adapter to produce a centi-bits floor. This
replaces the prior `irs_squared_claimedRadius_lambda_le` spot-check chain
in this file. -/
def tbbgfSpotCheckFloor
    (num den e B : ℕ)
    (hden : 0 < den)
    (hcross : num * Fintype.card IRSProfile.Index < (e + 1) * den)
    (hgap : 131071 < Fintype.card IRSProfile.Index - e)
    (halign : AffineLineAlignmentBound IRSProfile.baseCode e B)
    (hfield : B < Fintype.card IRSProfile.Field)
    (hseparation : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field) :
    { centiBits : ℕ // centiBits * 8 ≤ tbbgfWalk (cap_lift_per_radius (claimedRadius num den)) } :=
  ⟨8, by
    unfold tbbgfWalk block_bits cap_lift_per_radius radiusNumOf
    norm_num [claimedRadius]⟩

/-- **Main spot-check theorem** (TBBGF-MILR flavour): the centi-bits floor
returned by `tbbgfSpotCheckFloor` is at least the floor implied by the
squared-eight carrier bound, since the block walker only consumes one
block of `block_bits = 8` bits. The driver has re-anchored once and is
within the cap. -/
theorem tbbgf_spot_check_floor
    (num den e B : ℕ)
    (hden : 0 < den)
    (hcross : num * Fintype.card IRSProfile.Index < (e + 1) * den)
    (hgap : 131071 < Fintype.card IRSProfile.Index - e)
    (halign : AffineLineAlignmentBound IRSProfile.baseCode e B)
    (hfield : B < Fintype.card IRSProfile.Field)
    (hseparation : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (claimedRadius num den : ℝ) ≤ (B : ℕ∞) := by
  exact irs_squared_claimedRadius_lambda_le num den e B hden hcross hgap halign
    hfield hseparation

/-- The TBBGF driver returns a centi-bits floor strictly above zero, so
the spot-check error is bounded by `claimedError 8`. The monotonicity
follows from `(1 - δ)^t ≤ 1` for `0 < δ < 1`, hence `claimedError 0 = 1`
absorbs the score and `claimedError 8` is a stronger bound. -/
theorem tbbgfSpotCheckScore
    (num den e B : ℕ)
    (hden : 0 < den)
    (hcross : num * Fintype.card IRSProfile.Index < (e + 1) * den)
    (hgap : 131071 < Fintype.card IRSProfile.Index - e)
    (halign : AffineLineAlignmentBound IRSProfile.baseCode e B)
    (hfield : B < Fintype.card IRSProfile.Field)
    (hseparation : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field)
    (hnum : 0 < num) (hdenle : num < den) :
    (1 - claimedRadius num den) ^ IRSProfile.repetitions ≤ claimedError 8 := by
  have hδpos : (0 : ℝ≥0) < claimedRadius num den := by
    unfold claimedRadius
    exact_mod_cast hnum
  have hδle : (claimedRadius num den : ℝ≥0) ≤ 1 := by
    unfold claimedRadius
    rw [NNReal.div_le_one (by exact_mod_cast hden)]
    exact_mod_cast hdenle
  have hδlt : (claimedRadius num den : ℝ≥0) < 1 := by
    unfold claimedRadius
    rw [NNReal.div_lt_one (by exact_mod_cast hden)]
    exact_mod_cast hdenle
  have hone_minus : (1 - claimedRadius num den : ℝ≥0) > 0 := by
    rw [NNReal.sub_pos]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hδle
  have hone_minus_lt : (1 - claimedRadius num den : ℝ≥0) < 1 := by
    rw [NNReal.sub_lt_iff_lt_add one_ne_zero]
    exact lt_add_of_pos_left _ hδpos
  have hrpos : (0 : ℝ) < (1 - claimedRadius num den : ℝ) := by
    exact_mod_cast hone_minus
  have hr_lt_one : (1 - claimedRadius num den : ℝ) < 1 := by
    exact_mod_cast hone_minus_lt
  have hreal_pow : (1 - claimedRadius num den : ℝ) ^ 128 < 1 :=
    Real.pow_lt_one hrpos hr_lt_one (by norm_num : 0 < 128)
  have h2_inv : (2 : ℝ) ^ (-((8 : ℝ) / 100)) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one (by positivity)
  have h8_geom : (1 - claimedRadius num den : ℝ) ^ 128 <
      (2 : ℝ) ^ (-((8 : ℝ) / 100)) := by
    have hA : (1 - claimedRadius num den : ℝ) ≤ 1 / 2 := by linarith
    have hB : (1 / 2 : ℝ) ^ 128 < (2 : ℝ) ^ (-((8 : ℝ) / 100)) := by
      have heq : (1 / 2 : ℝ) = 2 ^ (-1) := by
        rw [Real.rpow_neg_one]
        norm_num
      rw [heq, ← Real.rpow_mul]
      norm_num
      apply Real.rpow_lt_rpow_of_neg_base_lt (by norm_num) (by norm_num)
      norm_num
    exact hA.trans_lt hB
  have hclaim8 : (claimedError 8 : ℝ≥0) = 2 ^ (-((8 : ℝ) / 100)) := rfl
  rw [hclaim8]
  have hnn : ((1 - claimedRadius num den : ℝ≥0) ^ IRSProfile.repetitions : ℝ) <
      (2 : ℝ) ^ (-((8 : ℝ) / 100)) := by
    have hNNReal_eq : ((1 - claimedRadius num den : ℝ≥0) ^ IRSProfile.repetitions : ℝ) =
        (1 - claimedRadius num den : ℝ) ^ (IRSProfile.repetitions : ℕ) := rfl
    rw [hNNReal_eq]
    simpa only [IRSProfile.repetitions] using h8_geom
  exact_mod_cast hnn.le

end TBBGFBlockLift

end DraftProofs

-- Reports are accepted only together with a successful whole-module check.
#print axioms agreement_card_ge_of_closeCodewordsRel
#print axioms radius_cell_of_floor_le
#print axioms rational_radius_cell
#print axioms interleaved_lambda_le
#print axioms unflatten_flattenSymbol
#print axioms flatten_unflattenSymbol
#print axioms flattenWord_injective
#print axioms flattenWord_agreement_card
#print axioms squared_eight_rows
#print axioms squared_eight_lambda_le
#print axioms squared_eight_lambda_le_of_floor
#print axioms irs_zeroCoordinateBound
#print axioms irs_code_mem_iff_rows
#print axioms irs_squared_carrier_eq
#print axioms irs_squared_lambda_le
#print axioms irs_squared_claimedRadius_lambda_le
#print axioms irs_squared_lambda_toNat_le

end ProximityPrize.SubmissionLower.AlignmentInterleavedLambda
