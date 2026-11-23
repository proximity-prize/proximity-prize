import ProximityPrize.SubmissionLower.FadicSpace

/-!
# The gate space of one level, and its kernel certificate

At level `r` the gate space is the whole source when `r • σ` covers it, and otherwise the larger
of the plain tapered box `r • σ` and the f-adic space of `FadicSpace`.

* `exists_gateSpace`: the space, the bound `gateDim ≤ finrank`, and the two forms of a nonzero
  row: supported in the box `r • σ`, or `f ^ a * (c + f * h)` with `c` in the box `(r - a) • σ`.
* `fastGateDim_eq`: the same number in a form the kernel evaluates (prefix sums, the constant
  range of each count collapsed).
* `loss_of_rows`: from the per-level values to `∑ i < N, max 0 (S - gateDim (i+1)) ≤ L` for
  every `N`.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents jetColumns)
open MvPolynomial
open scoped BigOperators
open Finset

/-- The level covers the whole source. -/
def IsFull (σb σj σt r:ℕ):Prop:=4012≤r*σb ∧ 1650≤r*σj ∧ 550≤r*σt

instance (σb σj σt r:ℕ):Decidable (IsFull σb σj σt r):=by unfold IsFull; infer_instance

/-- Dimension of the plain tapered box of level `r`. -/
def plainDim (σb σj σt r : ℕ) : ℤ :=
  boxCount (min (r*σb) 4012) (min (r*σj) 1650) (r*σt) 131312

/-- Lower bound for the dimension of the gate space of level `r`; `S` is the source dimension. -/
def gateDim (S : ℤ) (σb σj σt bl bh jl jh r : ℕ) : ℤ :=
  if IsFull σb σj σt r then S
  else max (plainDim σb σj σt r) (fadicDim σb σj σt bl bh jl jh r)

/-- Exponents in the box `(B, J, T)`, no taper. -/
def slopeBox (B J T : ℕ) : Set JetExp :=
  {e | Finsupp.weight gradeWeight e≤B ∧ Finsupp.weight oldWeight e≤J ∧ e 3≤T}

theorem taperBox_subset_slopeBox (B J T Θ : ℕ) : taperBox B J T Θ ⊆ slopeBox B J T :=
  fun _ h => ⟨h.1,h.2.1,h.2.2.1⟩

theorem taperBox_subset_source {B J T : ℕ} (hB : B ≤ 4012) (hJ : J ≤ 1650) :
    taperBox B J T 131312 ⊆ jetExponents:=by
  intro e he
  obtain ⟨h1,h2,_,h4⟩:=he
  have hg:=w_grade e
  have ho:=w_old e
  refine ⟨h1.trans hB,h2.trans hJ, ?_⟩
  unfold TaperBudget.cap
  split
  · omega
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).mpr
    omega

theorem source_subset_slopeBox {σb σj σt r : ℕ} (h : IsFull σb σj σt r) :
    jetExponents ⊆ slopeBox (r*σb) (r*σj) (r*σt):=by
  intro e he
  obtain ⟨h1,h2,_⟩:=he
  obtain ⟨hb,hj,ht⟩:=h
  have ho:=w_old e
  exact ⟨h1.trans hb,h2.trans hj,by omega⟩

section Field

variable {𝕜:Type*} [Field 𝕜]

/-- **The gate space of level `r`.** -/
theorem exists_gateSpace (f : MvPolynomial (Fin 4) 𝕜) (hf : f ≠ 0) (bl bh jl jh : ℕ)
    (hbl:bl≤f.weightedTotalDegree gradeWeight) (hbh:f.weightedTotalDegree gradeWeight≤bh)
    (hjl:jl≤f.weightedTotalDegree oldWeight) (hjh:f.weightedTotalDegree oldWeight≤jh)
    (σb σj σt r:ℕ) :
    ∃ U : Submodule 𝕜 (MvPolynomial (Fin 4) 𝕜),
      U≤restrictSupport 𝕜 jetExponents ∧
      gateDim (jetColumns.card:ℤ) σb σj σt bl bh jl jh r≤(Module.finrank 𝕜 U:ℤ) ∧
      ∀ v ∈ U, v ≠ 0 →
        v ∈ restrictSupport 𝕜 (slopeBox (r*σb) (r*σj) (r*σt)) ∨
        ∃ (a : ℕ) (c h : MvPolynomial (Fin 4) 𝕜),
          3*a≤r ∧ a < r ∧ v=f ^ a*(c+f*h) ∧ c≠0 ∧ ¬ f ∣ c ∧
          c ∈ restrictSupport 𝕜 (slopeBox ((r - a)*σb) ((r - a)*σj) ((r - a)*σt)):=by
  classical
  by_cases hfull:IsFull σb σj σt r
  · refine ⟨restrictSupport 𝕜 jetExponents, le_rfl, ?_, ?_⟩
    · have h := finrank_restrictSupport_finset (K := 𝕜) jetColumns
      have hset:(jetColumns:Set JetExp)=jetExponents:=Set.Finite.coe_toFinset _
      rw [hset] at h
      unfold gateDim
      simp only [hfull, ↓reduceIte]
      rw [h]
    · intro v hv _
      exact Or.inl (restrictSupport_mono 𝕜 (source_subset_slopeBox hfull) hv)
  · by_cases hcmp : fadicDim σb σj σt bl bh jl jh r ≤ plainDim σb σj σt r
    · set B := min (r * σb) 4012
      set J:=min (r*σj) 1650
      have hfin:=taperBox_finite B J (r*σt) 131312
      refine ⟨restrictSupport 𝕜 (taperBox B J (r * σt) 131312),
        restrictSupport_mono 𝕜 (taperBox_subset_source (min_le_right _ _) (min_le_right _ _)),
        ?_, ?_⟩
      · have h := finrank_restrictSupport_finset (K := 𝕜) hfin.toFinset
        rw [Set.Finite.coe_toFinset] at h
        unfold gateDim
        simp only [hfull, ↓reduceIte]
        rw [max_eq_left hcmp,h]
        exact (taperBox_card B J (r*σt) 131312).ge
      · intro v hv _
        refine Or.inl (restrictSupport_mono 𝕜 ?_ hv)
        exact (taperBox_subset_slopeBox _ _ _ _).trans
          (fun e he => ⟨he.1.trans (min_le_left _ _),he.2.1.trans (min_le_left _ _),he.2.2⟩)
    · obtain ⟨U, hU, hdim, hrow⟩ := exists_fadicSpace f hf bl bh jl jh hbl hbh hjl hjh σb σj σt r
      refine ⟨U,hU, ?_, ?_⟩
      · unfold gateDim
        simp only [hfull, ↓reduceIte]
        rw [max_eq_right (le_of_not_ge hcmp)]
        exact hdim
      · intro v hv hne
        obtain ⟨a,c,h,h1,h2,h3,h4,h5,h6⟩:=hrow v hv hne
        exact Or.inr ⟨a, c, h, h1, h2, h3, h4, h5,
          restrictSupport_mono 𝕜 (taperBox_subset_slopeBox _ _ _ _) h6⟩

end Field

/-! ### Kernel form -/

def fastMult (σb σj σt bl bh jl jh r a : ℕ) : ℤ :=
  if bl ≤ depthB σb bh r a ∧ jl ≤ depthJ σj jh r a ∧ 26 * bl ≤ depthΘ bh jh a then
    fastCount (depthB σb bh r a - bl) (depthJ σj jh r a - jl) ((r - a) * σt)
      (depthΘ bh jh a - 26*bl)
  else 0

def fastDepthDim (σb σj σt bl bh jl jh r a : ℕ) : ℤ :=
  if DepthOK bh jh r a then
    max 0 (fastCount (depthB σb bh r a) (depthJ σj jh r a) ((r - a) * σt) (depthΘ bh jh a) -
      fastMult σb σj σt bl bh jl jh r a)
  else 0

def fastGateDim (S : ℤ) (σb σj σt bl bh jl jh r : ℕ) : ℤ :=
  if IsFull σb σj σt r then S
  else max (fastCount (min (r * σb) 4012) (min (r * σj) 1650) (r * σt) 131312)
    (intPrefix (fastDepthDim σb σj σt bl bh jl jh r) (r / 3+1))

theorem fastGateDim_eq (S : ℤ) (σb σj σt bl bh jl jh r : ℕ) :
    fastGateDim S σb σj σt bl bh jl jh r=gateDim S σb σj σt bl bh jl jh r:=by
  have hdepth : fastDepthDim σb σj σt bl bh jl jh r = depthDim σb σj σt bl bh jl jh r := by
    funext a
    unfold fastDepthDim depthDim fastMult multCount
    simp only [fastCount_eq]
  unfold fastGateDim gateDim plainDim fadicDim
  rw [hdepth,intPrefix_eq,fastCount_eq]

/-- The loss of level `i + 1`. -/
def rowLoss (S : ℤ) (σb σj σt bl bh jl jh i : ℕ) : ℤ :=
  max 0 (S - fastGateDim S σb σj σt bl bh jl jh (i+1))

theorem isFull_mono {σb σj σt r r' : ℕ} (h : IsFull σb σj σt r) (hr : r ≤ r') :
    IsFull σb σj σt r' :=
  ⟨h.1.trans (Nat.mul_le_mul_right _ hr), h.2.1.trans (Nat.mul_le_mul_right _ hr),
    h.2.2.trans (Nat.mul_le_mul_right _ hr)⟩

/-- **Certificate.**  If level `R0 + 1` is full and the first `R0` level losses add up to `L`,
the total loss over any number of levels is at most `L`. -/
theorem loss_of_rows (S : ℤ) (σb σj σt bl bh jl jh R0 : ℕ) (L : ℤ)
    (hfull:IsFull σb σj σt (R0+1))
    (hsum:intPrefix (rowLoss S σb σj σt bl bh jl jh) R0=L) (N:ℕ) :
    ∑ i ∈ range N,max 0 (S - gateDim S σb σj σt bl bh jl jh (i+1))≤L:=by
  have hrow (i : ℕ) : max 0 (S - gateDim S σb σj σt bl bh jl jh (i + 1)) =
      rowLoss S σb σj σt bl bh jl jh i:=by
    unfold rowLoss
    rw [fastGateDim_eq]
  have hzero (i : ℕ) (hi : R0 ≤ i) : rowLoss S σb σj σt bl bh jl jh i = 0 := by
    unfold rowLoss fastGateDim
    have hf:IsFull σb σj σt (i+1):=isFull_mono hfull (by omega)
    simp only [hf, ↓reduceIte,sub_self,max_self]
  have hnonneg (i:ℕ):0≤rowLoss S σb σj σt bl bh jl jh i:=le_max_left _ _
  simp only [hrow]
  rw [← hsum,intPrefix_eq]
  rcases le_total N R0 with h | h
  · exact Finset.sum_le_sum_of_subset_of_nonneg (range_mono h) (fun i _ _ => hnonneg i)
  · rw [← Finset.sum_range_add_sum_Ico _ h]
    have : ∑ i ∈ Finset.Ico R0 N, rowLoss S σb σj σt bl bh jl jh i = 0 :=
      Finset.sum_eq_zero fun i hi => hzero i (Finset.mem_Ico.mp hi).1
    rw [this,add_zero]

end FadicGate

#print axioms FadicGate.exists_gateSpace
#print axioms FadicGate.fastGateDim_eq
#print axioms FadicGate.loss_of_rows
