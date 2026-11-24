import ProximityPrize.SubmissionLower.FadicGateDim

set_option Elab.async false

/-!
# Variable-depth f-adic gate

Each depth `a` of a level may choose its own box `(B, J, T)`, or be skipped.  The anchor factor
is described by bounds on four weighted degrees: grade in `[bl, bh]`, index in `[jl, jh]`, top at
least `tl`, and taper (`26·grade + 25·nonY0` per monomial) in `[L, H]`.  The box of depth `a`
needs `B + a·bh ≤ 4012`, `J + a·jh ≤ 1650`, `a·H ≤ 131312`, and uses the taper bound
`131312 - a·H`; multiples of `f` inside it are debited with the lower bounds.

* `exists_varFadicSpace`: the direct sum over the depths `a < n`, its dimension bound, and the row
  form `v = f ^ a * (c + f * h)` with `c` in the box of depth `a`.
* `exists_varGateSpace`: a level with a plain box, an f-adic schedule, and a terminal level from
  which the whole source is used.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents jetColumns)
open MvPolynomial
open scoped BigOperators
open Finset

/-- A depth entry: skipped, or a box `(B, J, T)`. -/
abbrev Entry := Option (ℕ × ℕ × ℕ)

def varΘ (H a : ℕ) : ℕ := 131312 - a * H

def BoxOK (bh jh H a B J : ℕ) : Prop := B + a * bh ≤ 4012 ∧ J + a * jh ≤ 1650 ∧ a * H ≤ 131312

instance (bh jh H a B J : ℕ) : Decidable (BoxOK bh jh H a B J) := by unfold BoxOK; infer_instance

/-- Upper bound for the multiples of `f` in the box, debited with the lower weight bounds. -/
def varMult (bl jl tl L B J T Θ : ℕ) : ℤ :=
  if bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ then boxCount (B - bl) (J - jl) (T - tl) (Θ - L) else 0

def varDepthDim (bl bh jl jh tl L H a : ℕ) : Entry → ℤ
  | none => 0
  | some (B, J, T) =>
    if BoxOK bh jh H a B J then
      max 0 (boxCount B J T (varΘ H a) - varMult bl jl tl L B J T (varΘ H a))
    else 0

def varFadicDim (bl bh jl jh tl L H n : ℕ) (box : ℕ → Entry) : ℤ :=
  ∑ a ∈ range n, varDepthDim bl bh jl jh tl L H a (box a)

section Field

variable {𝕜 : Type*} [Field 𝕜]

local notation "R" => MvPolynomial (Fin 4) 𝕜

theorem w_taper' (m : JetExp) :
    Finsupp.weight taperWeight m = 26 * Finsupp.weight gradeWeight m + 25 * (m 1 + m 2 + m 3) := by
  rw [w_taper, w_grade]
  ring

/-- `f ^ a` times a row of the depth box stays in the accepted source. -/
theorem pow_mul_mem_source_var (f : R) (hf : f ≠ 0) (bh jh H : ℕ)
    (hbh : f.weightedTotalDegree gradeWeight ≤ bh) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (hH : f.weightedTotalDegree taperWeight ≤ H)
    {B J T a : ℕ} (hB : B + a * bh ≤ 4012) (hJ : J + a * jh ≤ 1650) (hΘ : a * H ≤ 131312)
    {c : R} (hc : c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a))) :
    f ^ a * c ∈ restrictSupport 𝕜 jetExponents := by
  classical
  rw [mem_restrictSupport_iff] at hc ⊢
  intro m hm
  obtain ⟨μ, hμ, e, he, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  obtain ⟨heB, heJ, _, heΘ⟩ := hc he
  have hμg : Finsupp.weight gradeWeight μ ≤ a * bh := by
    refine (le_weightedTotalDegree gradeWeight hμ).trans ?_
    rw [wdeg_pow gradeWeight hf a]
    exact Nat.mul_le_mul_left a hbh
  have hμo : Finsupp.weight oldWeight μ ≤ a * jh := by
    refine (le_weightedTotalDegree oldWeight hμ).trans ?_
    rw [wdeg_pow oldWeight hf a]
    exact Nat.mul_le_mul_left a hjh
  have hμτ : Finsupp.weight taperWeight μ ≤ a * H := by
    refine (le_weightedTotalDegree taperWeight hμ).trans ?_
    rw [wdeg_pow taperWeight hf a]
    exact Nat.mul_le_mul_left a hH
  have hτ := w_taper' μ
  have ho := w_old μ
  have hoe := w_old e
  have hsumg : Finsupp.weight gradeWeight (μ + e) =
      Finsupp.weight gradeWeight μ + Finsupp.weight gradeWeight e := map_add _ _ _
  have hsumo : Finsupp.weight oldWeight (μ + e) =
      Finsupp.weight oldWeight μ + Finsupp.weight oldWeight e := map_add _ _ _
  unfold varΘ at heΘ
  change Finsupp.weight gradeWeight (μ + e) ≤ 4012 ∧ Finsupp.weight oldWeight (μ + e) ≤ 1650 ∧
    (μ + e) 1 + (μ + e) 2 + (μ + e) 3 ≤ TaperBudget.cap (Finsupp.weight gradeWeight (μ + e))
  rw [hsumg, hsumo]
  simp only [Finsupp.add_apply]
  refine ⟨by omega, by omega, ?_⟩
  unfold TaperBudget.cap
  split
  · omega
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).mpr
    omega

/-- A nonzero cofactor of a multiple of `f` in a tapered box lies in the box shrunk by the lower
weight bounds. -/
theorem cofactor_mem_var (f : R) (hf : f ≠ 0) (bl jl tl L : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hjl : jl ≤ f.weightedTotalDegree oldWeight)
    (htl : tl ≤ f.weightedTotalDegree topWeight) (hL : L ≤ f.weightedTotalDegree taperWeight)
    {B J T Θ : ℕ} {g : R} (hg : g ≠ 0)
    (hfg : f * g ∈ restrictSupport 𝕜 (taperBox B J T Θ)) :
    (bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ) ∧
      g ∈ restrictSupport 𝕜 (taperBox (B - bl) (J - jl) (T - tl) (Θ - L)) := by
  classical
  rw [mem_restrictSupport_iff] at hfg
  have hmul (w : Fin 4 → ℕ) : (f * g).weightedTotalDegree w =
      f.weightedTotalDegree w + g.weightedTotalDegree w := weightedTotalDegree_mul _ _ _ hf hg
  have hgB : (f * g).weightedTotalDegree gradeWeight ≤ B :=
    wdeg_le_of_support _ _ _ fun m hm => (hfg hm).1
  have hgJ : (f * g).weightedTotalDegree oldWeight ≤ J :=
    wdeg_le_of_support _ _ _ fun m hm => (hfg hm).2.1
  have hgT : (f * g).weightedTotalDegree topWeight ≤ T :=
    wdeg_le_of_support _ _ _ fun m hm => by rw [w_top]; exact (hfg hm).2.2.1
  have hgΘ : (f * g).weightedTotalDegree taperWeight ≤ Θ :=
    wdeg_le_of_support _ _ _ fun m hm => by
      have h := (hfg hm).2.2.2
      rw [w_taper']
      exact h
  rw [hmul] at hgB hgJ hgT hgΘ
  refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
  rw [mem_restrictSupport_iff]
  intro e he
  have h1 := le_weightedTotalDegree gradeWeight he
  have h2 := le_weightedTotalDegree oldWeight he
  have h3 := le_weightedTotalDegree topWeight he
  have h4 := le_weightedTotalDegree taperWeight he
  rw [w_top] at h3
  rw [w_taper'] at h4
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **One depth.** -/
theorem exists_varDepthSpace (f : R) (hf : f ≠ 0) (bl bh jl jh tl L H : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hbh : f.weightedTotalDegree gradeWeight ≤ bh)
    (hjl : jl ≤ f.weightedTotalDegree oldWeight) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (htl : tl ≤ f.weightedTotalDegree topWeight)
    (hL : L ≤ f.weightedTotalDegree taperWeight) (hH : f.weightedTotalDegree taperWeight ≤ H)
    (a : ℕ) (e : Entry) :
    ∃ C : Submodule 𝕜 R, FiniteDimensional 𝕜 C ∧
      varDepthDim bl bh jl jh tl L H a e ≤ (Module.finrank 𝕜 C : ℤ) ∧
      (∀ c ∈ C, f ∣ c → c = 0) ∧
      (∀ c ∈ C, f ^ a * c ∈ restrictSupport 𝕜 jetExponents) ∧
      (∀ c ∈ C, c ≠ 0 → ∃ B J T : ℕ, e = some (B, J, T) ∧ BoxOK bh jh H a B J ∧
        c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a))) := by
  classical
  have bot_case : ∃ C : Submodule 𝕜 R, FiniteDimensional 𝕜 C ∧ (0 : ℤ) ≤ (Module.finrank 𝕜 C : ℤ) ∧
      (∀ c ∈ C, f ∣ c → c = 0) ∧ (∀ c ∈ C, f ^ a * c ∈ restrictSupport 𝕜 jetExponents) ∧
      (∀ c ∈ C, c ≠ 0 → ∃ B J T : ℕ, e = some (B, J, T) ∧ BoxOK bh jh H a B J ∧
        c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a))) := by
    refine ⟨⊥, inferInstance, by positivity, ?_, ?_, ?_⟩
    · intro c hc _; exact (Submodule.mem_bot 𝕜).mp hc
    · intro c hc
      rw [(Submodule.mem_bot 𝕜).mp hc, mul_zero]
      exact Submodule.zero_mem _
    · intro c hc hne; exact absurd ((Submodule.mem_bot 𝕜).mp hc) hne
  rcases e with _ | ⟨B, J, T⟩
  · simpa [varDepthDim] using bot_case
  by_cases hok : BoxOK bh jh H a B J
  swap
  · simpa [varDepthDim, hok] using bot_case
  obtain ⟨hB, hJ, hΘa⟩ := hok
  set Θ := varΘ H a with hΘdef
  have hI := taperBox_finite B J T Θ
  let M : Submodule 𝕜 R := restrictSupport 𝕜 (taperBox B J T Θ)
  have : Module.Finite 𝕜 M := restrictSupport_finite hI
  have hMdim : (Module.finrank 𝕜 M : ℤ) = boxCount B J T Θ := by
    have h := finrank_restrictSupport_finset (K := 𝕜) hI.toFinset
    rw [Set.Finite.coe_toFinset] at h
    change (Module.finrank 𝕜 (restrictSupport 𝕜 (taperBox B J T Θ)) : ℤ) = _
    rw [h]
    exact taperBox_card B J T Θ
  let mulf : R →ₗ[𝕜] R := LinearMap.mulLeft 𝕜 f
  let G : Submodule 𝕜 R := M.comap mulf
  have hGdim : ∃ _ : Module.Finite 𝕜 G,
      (Module.finrank 𝕜 G : ℤ) ≤ varMult bl jl tl L B J T Θ := by
    by_cases hguard : bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ
    · let Nset := taperBox (B - bl) (J - jl) (T - tl) (Θ - L)
      have hN := taperBox_finite (B - bl) (J - jl) (T - tl) (Θ - L)
      have : Module.Finite 𝕜 (restrictSupport 𝕜 Nset) := restrictSupport_finite hN
      have hle : G ≤ restrictSupport 𝕜 Nset := by
        intro g hg
        by_cases hg0 : g = 0
        · rw [hg0]; exact Submodule.zero_mem _
        · exact (cofactor_mem_var f hf bl jl tl L hbl hjl htl hL hg0 hg).2
      have : Module.Finite 𝕜 G := Submodule.finiteDimensional_of_le hle
      refine ⟨inferInstance, ?_⟩
      have h1 := Submodule.finrank_mono hle
      have h2 := finrank_restrictSupport_finset (K := 𝕜) hN.toFinset
      rw [Set.Finite.coe_toFinset] at h2
      have h3 := taperBox_card (B - bl) (J - jl) (T - tl) (Θ - L)
      have h4 : varMult bl jl tl L B J T Θ = boxCount (B - bl) (J - jl) (T - tl) (Θ - L) := by
        unfold varMult
        rw [if_pos hguard]
      rw [h4, ← h3]
      change Module.finrank 𝕜 G ≤ Module.finrank 𝕜 (restrictSupport 𝕜 Nset) at h1
      rw [h2] at h1
      exact_mod_cast h1
    · have hbot : G = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        by_contra hg0
        exact hguard (cofactor_mem_var f hf bl jl tl L hbl hjl htl hL hg0 hg).1
      rw [hbot]
      refine ⟨inferInstance, ?_⟩
      have h4 : varMult bl jl tl L B J T Θ = 0 := by
        unfold varMult
        rw [if_neg hguard]
      rw [h4, finrank_bot]
      rfl
  obtain ⟨hGfin, hGle⟩ := hGdim
  have := hGfin
  let Mf : Submodule 𝕜 R := G.map mulf
  have hMfle : Module.finrank 𝕜 Mf ≤ Module.finrank 𝕜 G := Submodule.finrank_map_le mulf G
  let p : Submodule 𝕜 M := Mf.comap M.subtype
  obtain ⟨q, hq⟩ := p.exists_isCompl
  have hpq := Submodule.finrank_add_eq_of_isCompl hq
  have hp_le : Module.finrank 𝕜 p ≤ Module.finrank 𝕜 Mf := by
    have h1 : p.map M.subtype ≤ Mf := Submodule.map_comap_le _ _
    have h2 := Submodule.finrank_mono h1
    rwa [Submodule.finrank_map_subtype_eq] at h2
  let C : Submodule 𝕜 R := q.map M.subtype
  have hCdim : Module.finrank 𝕜 C = Module.finrank 𝕜 q := Submodule.finrank_map_subtype_eq M q
  have hCM : C ≤ M := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  refine ⟨C, Submodule.finiteDimensional_of_le hCM, ?_, ?_, ?_, ?_⟩
  · have hd : varDepthDim bl bh jl jh tl L H a (some (B, J, T)) =
        max 0 (boxCount B J T Θ - varMult bl jl tl L B J T Θ) := by
      simp only [varDepthDim]
      rw [if_pos ⟨hB, hJ, hΘa⟩]
    rw [hd, hCdim]
    apply max_le (by positivity)
    have : (Module.finrank 𝕜 M : ℤ) = Module.finrank 𝕜 p + Module.finrank 𝕜 q := by
      exact_mod_cast hpq.symm
    have h5 : (Module.finrank 𝕜 p : ℤ) ≤ Module.finrank 𝕜 G := by exact_mod_cast hp_le.trans hMfle
    linarith
  · rintro _ ⟨y, hy, rfl⟩ ⟨g, hg⟩
    have hyM : (y : R) ∈ M := y.2
    have hgG : g ∈ G := by
      change f * g ∈ M
      rw [← hg]
      exact hyM
    have hyp : y ∈ p := by
      change (y : R) ∈ Mf
      exact ⟨g, hgG, hg.symm⟩
    have hy0 : y = 0 := by
      have := hq.disjoint.le_bot ⟨hyp, hy⟩
      exact (Submodule.mem_bot 𝕜).mp this
    rw [hy0]
    rfl
  · intro c hc
    exact pow_mul_mem_source_var f hf bh jh H hbh hjh hH hB hJ hΘa (hCM hc)
  · intro c hc _
    exact ⟨B, J, T, rfl, ⟨hB, hJ, hΘa⟩, hCM hc⟩

/-- **The variable-depth f-adic space.** -/
theorem exists_varFadicSpace (f : R) (hf : f ≠ 0) (bl bh jl jh tl L H : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hbh : f.weightedTotalDegree gradeWeight ≤ bh)
    (hjl : jl ≤ f.weightedTotalDegree oldWeight) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (htl : tl ≤ f.weightedTotalDegree topWeight)
    (hL : L ≤ f.weightedTotalDegree taperWeight) (hH : f.weightedTotalDegree taperWeight ≤ H)
    (n : ℕ) (box : ℕ → Entry) :
    ∃ U : Submodule 𝕜 R,
      U ≤ restrictSupport 𝕜 jetExponents ∧
      varFadicDim bl bh jl jh tl L H n box ≤ (Module.finrank 𝕜 U : ℤ) ∧
      ∀ v ∈ U, v ≠ 0 → ∃ (a B J T : ℕ) (c h : R),
        a < n ∧ box a = some (B, J, T) ∧ BoxOK bh jh H a B J ∧
        v = f ^ a * (c + f * h) ∧ c ≠ 0 ∧ ¬ f ∣ c ∧
        c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a)) := by
  classical
  choose C hCfin hCdim hCdvd hCsrc hCbox using
    fun a => exists_varDepthSpace f hf bl bh jl jh tl L H hbl hbh hjl hjh htl hL hH a (box a)
  have : ∀ i : Fin n, FiniteDimensional 𝕜 (C i) := fun i => hCfin i
  let Φ : (∀ i : Fin n, C i) →ₗ[𝕜] R :=
    ∑ i : Fin n, (LinearMap.mulLeft 𝕜 (f ^ (i : ℕ))).comp ((C i).subtype.comp (LinearMap.proj i))
  have hΦ (w : ∀ i : Fin n, C i) : Φ w = ∑ i : Fin n, f ^ (i : ℕ) * (w i : R) := by
    simp [Φ, LinearMap.sum_apply]
  let seq (w : ∀ i : Fin n, C i) : ℕ → R := fun i => if h : i < n then (w ⟨i, h⟩ : R) else 0
  have hseq (w : ∀ i : Fin n, C i) : Φ w = ∑ i ∈ range n, f ^ i * seq w i := by
    rw [hΦ, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [seq, i.isLt]
  have hseqC (w : ∀ i : Fin n, C i) (i : ℕ) (hi : i < n) : seq w i = (w ⟨i, hi⟩ : R) := by
    simp [seq, hi]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [hseq] at hw
    have hall := fadic_zero f hf n (seq w) (fun i hi hdiv => by
      rw [hseqC w i hi] at hdiv ⊢
      exact hCdvd i _ (w ⟨i, hi⟩).2 hdiv) hw
    funext i
    have := hall i i.isLt
    rw [hseqC w i i.isLt] at this
    exact Subtype.ext this
  refine ⟨LinearMap.range Φ, ?_, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [hΦ]
    exact Submodule.sum_mem _ fun i _ => hCsrc i _ (w i).2
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    unfold varFadicDim
    rw [← Fin.sum_univ_eq_sum_range (fun a => varDepthDim bl bh jl jh tl L H a (box a)) n,
      Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hCdim i
  · rintro _ ⟨w, rfl⟩ hv
    have hex : ∃ i, i < n ∧ seq w i ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hv
      rw [hseq]
      exact Finset.sum_eq_zero fun i hi => by
        rw [hnone i (Finset.mem_range.mp hi), mul_zero]
    let a := Nat.find hex
    obtain ⟨han, hane⟩ := Nat.find_spec hex
    have hlow : ∀ i < a, seq w i = 0 := by
      intro i hi
      by_contra hne
      exact Nat.find_min hex hi ⟨hi.trans han, hne⟩
    obtain ⟨h, hh⟩ := fadic_shape f a n (seq w) han hlow
    have hcC : seq w a ∈ C a := by
      rw [hseqC w a han]
      exact (w ⟨a, han⟩).2
    obtain ⟨B, J, T, hbox, hok, hmem⟩ := hCbox a _ hcC hane
    refine ⟨a, B, J, T, seq w a, h, han, hbox, hok, ?_, hane, ?_, hmem⟩
    · rw [← hh, ← hseq]
    · intro hdvd
      exact hane (hCdvd a _ hcC hdvd)

/-! ### A level of the variable gate -/

/-- Dimension of the plain box `(B, J, T)` of a level, cut to the source. -/
def varPlainDim (B J T : ℕ) : ℤ := boxCount (min B 4012) (min J 1650) T 131312

/-- Lower bound for the gate dimension of a level: the whole source from the terminal level on,
otherwise the larger of the plain box and the f-adic schedule. -/
def varGateDim (S : ℤ) (bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ) (n : ℕ → ℕ)
    (box : ℕ → ℕ → Entry) (r : ℕ) : ℤ :=
  if Rt ≤ r then S
  else max (varPlainDim (plain r).1 (plain r).2.1 (plain r).2.2)
    (varFadicDim bl bh jl jh tl L H (n r) (box r))

/-- **One level of the variable gate.**  `Rt` is the terminal level. -/
theorem exists_varGateSpace (f : R) (hf : f ≠ 0) (bl bh jl jh tl L H : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hbh : f.weightedTotalDegree gradeWeight ≤ bh)
    (hjl : jl ≤ f.weightedTotalDegree oldWeight) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (htl : tl ≤ f.weightedTotalDegree topWeight)
    (hL : L ≤ f.weightedTotalDegree taperWeight) (hH : f.weightedTotalDegree taperWeight ≤ H)
    (Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ) (n : ℕ → ℕ) (box : ℕ → ℕ → Entry) (r : ℕ) :
    ∃ U : Submodule 𝕜 R,
      U ≤ restrictSupport 𝕜 jetExponents ∧
      varGateDim (jetColumns.card : ℤ) bl bh jl jh tl L H Rt plain n box r ≤
        (Module.finrank 𝕜 U : ℤ) ∧
      ∀ v ∈ U, v ≠ 0 →
        Rt ≤ r ∨
        v ∈ restrictSupport 𝕜
          (taperBox (min (plain r).1 4012) (min (plain r).2.1 1650) (plain r).2.2 131312) ∨
        ∃ (a B J T : ℕ) (c h : R),
          a < n r ∧ box r a = some (B, J, T) ∧ BoxOK bh jh H a B J ∧
          v = f ^ a * (c + f * h) ∧ c ≠ 0 ∧ ¬ f ∣ c ∧
          c ∈ restrictSupport 𝕜 (taperBox B J T (varΘ H a)) := by
  classical
  by_cases hterm : Rt ≤ r
  · refine ⟨restrictSupport 𝕜 jetExponents, le_rfl, ?_, fun _ _ _ => Or.inl hterm⟩
    have h := finrank_restrictSupport_finset (K := 𝕜) jetColumns
    have hset : (jetColumns : Set JetExp) = jetExponents := Set.Finite.coe_toFinset _
    rw [hset] at h
    unfold varGateDim
    rw [if_pos hterm, h]
  · by_cases hcmp : varFadicDim bl bh jl jh tl L H (n r) (box r) ≤
        varPlainDim (plain r).1 (plain r).2.1 (plain r).2.2
    · set B := min (plain r).1 4012
      set J := min (plain r).2.1 1650
      have hfin := taperBox_finite B J (plain r).2.2 131312
      refine ⟨restrictSupport 𝕜 (taperBox B J (plain r).2.2 131312),
        restrictSupport_mono 𝕜 (taperBox_subset_source (min_le_right _ _) (min_le_right _ _)),
        ?_, fun v hv _ => Or.inr (Or.inl hv)⟩
      have h := finrank_restrictSupport_finset (K := 𝕜) hfin.toFinset
      rw [Set.Finite.coe_toFinset] at h
      unfold varGateDim
      rw [if_neg hterm, max_eq_left hcmp, h]
      exact (taperBox_card B J (plain r).2.2 131312).ge
    · obtain ⟨U, hU, hdim, hrow⟩ :=
        exists_varFadicSpace f hf bl bh jl jh tl L H hbl hbh hjl hjh htl hL hH (n r) (box r)
      refine ⟨U, hU, ?_, fun v hv hne => Or.inr (Or.inr (hrow v hv hne))⟩
      unfold varGateDim
      rw [if_neg hterm, max_eq_right (le_of_not_ge hcmp)]
      exact hdim

end Field

end FadicGate

#print axioms FadicGate.pow_mul_mem_source_var
#print axioms FadicGate.cofactor_mem_var
#print axioms FadicGate.exists_varFadicSpace
#print axioms FadicGate.exists_varGateSpace
