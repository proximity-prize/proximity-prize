import ProximityPrize.SubmissionLower.FadicCount

/-!
# The f-adic gate space

For a nonzero polynomial `f` in four jet variables over a field, with weighted degrees in
`[bl, bh]` (grade) and `[jl, jh]` (index), and a slope `(σb, σj, σt)`, the space of level `r` is

    U = ∑_{3a ≤ r} f ^ a • C a,

where `C a` is a complement of the multiples of `f` inside the monomial space of the tapered
box of depth `a`.  `exists_fadicSpace` gives

* `U ≤ restrictSupport 𝕜 TaperColumns.jetExponents` (the accepted `Shared50ShapeRank.ambient`);
* `fadicDim σb σj σt bl bh jl jh r ≤ finrank U`, an explicit sum of accepted `cappedCount`s,
  uniform over the rectangle of weights;
* every nonzero `v ∈ U` is `f ^ a * (c + f * h)` with `3 a ≤ r`, `a < r`, `c ≠ 0`, `¬ f ∣ c`
  and `c` supported in the box `(r - a) • σ`.

Nothing here depends on the geometry modules; the only project imports are
`PrimaryTaperColumns` (the source) and, through it, `Fast068` (the column counts).
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents)
open MvPolynomial
open scoped BigOperators
open Finset

/-! ### Weights of jet exponents -/

def topWeight : Fin 4 → ℕ := fun i => if i = 3 then 1 else 0
def taperWeight : Fin 4 → ℕ := fun i => if i = 0 then 26 else 51

theorem weight_four (w : Fin 4 → ℕ) (m : JetExp) :
    Finsupp.weight w m = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp [Fin.sum_univ_four]

theorem w_grade (m : JetExp) : Finsupp.weight gradeWeight m = m 0 + m 1 + m 2 + m 3 := by
  rw [weight_four]; simp [gradeWeight]

theorem w_old (m : JetExp) : Finsupp.weight oldWeight m = m 1 + 2 * m 2 + 3 * m 3 := by
  rw [weight_four]; simp [oldWeight]; omega

theorem w_top (m : JetExp) : Finsupp.weight topWeight m = m 3 := by
  rw [weight_four]; simp [topWeight]

theorem w_taper (m : JetExp) :
    Finsupp.weight taperWeight m = 26 * m 0 + 51 * (m 1 + m 2 + m 3) := by
  rw [weight_four]; simp [taperWeight]; omega

section Field

variable {𝕜 : Type*} [Field 𝕜]

local notation "R" => MvPolynomial (Fin 4) 𝕜

theorem wdeg_le_of_support (w : Fin 4 → ℕ) (p : R) (b : ℕ)
    (h : ∀ m ∈ p.support, Finsupp.weight w m ≤ b) : p.weightedTotalDegree w ≤ b := by
  unfold MvPolynomial.weightedTotalDegree
  exact Finset.sup_le h

theorem wdeg_pow (w : Fin 4 → ℕ) {p : R} (hp : p ≠ 0) (a : ℕ) :
    (p ^ a).weightedTotalDegree w = a * p.weightedTotalDegree w := by
  induction a with
  | zero => rw [pow_zero, zero_mul, ← MvPolynomial.C_1, weightedTotalDegree_C]
  | succ a ih =>
    rw [pow_succ, weightedTotalDegree_mul _ _ _ (pow_ne_zero _ hp) hp, ih, Nat.succ_mul]

/-! ### The boxes of one depth -/

def depthB (σb xb r a : ℕ) : ℕ := min ((r - a) * σb) (4012 - a * xb)
def depthJ (σj xj r a : ℕ) : ℕ := min ((r - a) * σj) (1650 - a * xj)
def depthΘ (xb xj a : ℕ) : ℕ := 131312 - a * (26 * xb + 25 * xj)

/-- The depths used at level `r`. -/
def DepthOK (xb xj r a : ℕ) : Prop :=
  3 * a ≤ r ∧ a < r ∧ a * xb ≤ 4012 ∧ a * xj ≤ 1650 ∧ a * (26 * xb + 25 * xj) ≤ 131312

instance (xb xj r a : ℕ) : Decidable (DepthOK xb xj r a) := by unfold DepthOK; infer_instance

/-- Upper bound for the multiples of `f` inside the depth-`a` box, for every factor whose
weighted degrees are at least `(bl, jl)`. -/
def multCount (σb σj σt bl bh jl jh r a : ℕ) : ℤ :=
  if bl ≤ depthB σb bh r a ∧ jl ≤ depthJ σj jh r a ∧ 26 * bl ≤ depthΘ bh jh a then
    boxCount (depthB σb bh r a - bl) (depthJ σj jh r a - jl) ((r - a) * σt)
      (depthΘ bh jh a - 26 * bl)
  else 0

/-- Dimension contributed by depth `a`, uniformly for weighted degrees in
`[bl, bh] × [jl, jh]`: the box is placed with the upper weights, the multiples are debited with
the lower ones. -/
def depthDim (σb σj σt bl bh jl jh r a : ℕ) : ℤ :=
  if DepthOK bh jh r a then
    max 0 (boxCount (depthB σb bh r a) (depthJ σj jh r a) ((r - a) * σt) (depthΘ bh jh a) -
      multCount σb σj σt bl bh jl jh r a)
  else 0

/-- Lower bound for the dimension of the f-adic space of level `r`. -/
def fadicDim (σb σj σt bl bh jl jh r : ℕ) : ℤ :=
  ∑ a ∈ range (r / 3 + 1), depthDim σb σj σt bl bh jl jh r a

/-- A power of `f` times a row of the depth-`a` box stays in the accepted source. -/
theorem pow_mul_mem_source (f : R) (hf : f ≠ 0) (xb xj : ℕ)
    (hb : f.weightedTotalDegree gradeWeight ≤ xb) (hj : f.weightedTotalDegree oldWeight ≤ xj)
    {B J T a : ℕ} (hB : B + a * xb ≤ 4012) (hJ : J + a * xj ≤ 1650)
    (hΘ : a * (26 * xb + 25 * xj) ≤ 131312) {c : R}
    (hc : c ∈ restrictSupport 𝕜 (taperBox B J T (depthΘ xb xj a))) :
    f ^ a * c ∈ restrictSupport 𝕜 jetExponents := by
  classical
  rw [mem_restrictSupport_iff] at hc ⊢
  intro m hm
  obtain ⟨μ, hμ, e, he, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  obtain ⟨heB, heJ, _, heΘ⟩ := hc he
  have hμg : Finsupp.weight gradeWeight μ ≤ a * xb := by
    refine (le_weightedTotalDegree gradeWeight hμ).trans ?_
    rw [wdeg_pow gradeWeight hf a]
    exact Nat.mul_le_mul_left a hb
  have hμo : Finsupp.weight oldWeight μ ≤ a * xj := by
    refine (le_weightedTotalDegree oldWeight hμ).trans ?_
    rw [wdeg_pow oldWeight hf a]
    exact Nat.mul_le_mul_left a hj
  have hg := w_grade μ
  have ho := w_old μ
  have hge := w_grade e
  have hoe := w_old e
  have hsumg : Finsupp.weight gradeWeight (μ + e) =
      Finsupp.weight gradeWeight μ + Finsupp.weight gradeWeight e := map_add _ _ _
  have hsumo : Finsupp.weight oldWeight (μ + e) =
      Finsupp.weight oldWeight μ + Finsupp.weight oldWeight e := map_add _ _ _
  unfold depthΘ at heΘ
  have hdist : a * (26 * xb + 25 * xj) = 26 * (a * xb) + 25 * (a * xj) := by ring
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

/-- A nonzero cofactor of a multiple of `f` inside a tapered box lies in the smaller box. -/
theorem cofactor_mem (f : R) (hf : f ≠ 0) (xb xj : ℕ)
    (hb : f.weightedTotalDegree gradeWeight = xb) (hj : f.weightedTotalDegree oldWeight = xj)
    {B J T Θ : ℕ} {g : R} (hg : g ≠ 0)
    (hfg : f * g ∈ restrictSupport 𝕜 (taperBox B J T Θ)) :
    (xb ≤ B ∧ xj ≤ J ∧ 26 * xb ≤ Θ) ∧
      g ∈ restrictSupport 𝕜 (taperBox (B - xb) (J - xj) T (Θ - 26 * xb)) := by
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
      rw [w_taper]
      rw [w_grade] at h
      omega
  -- the taper weight of `f` is at least `26 * xb`
  have hfτ : 26 * xb ≤ f.weightedTotalDegree taperWeight := by
    have hne : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup f.support hne
      (fun s => Finsupp.weight gradeWeight s)
    have hxb : xb = Finsupp.weight gradeWeight m := by
      rw [← hb]
      exact hmax
    have h1 := le_weightedTotalDegree taperWeight hm
    rw [w_taper] at h1
    rw [hxb, w_grade]
    omega
  rw [hmul] at hgB hgJ hgT hgΘ
  rw [hb] at hgB
  rw [hj] at hgJ
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  rw [mem_restrictSupport_iff]
  intro e he
  have h1 := le_weightedTotalDegree gradeWeight he
  have h2 := le_weightedTotalDegree oldWeight he
  have h3 := le_weightedTotalDegree topWeight he
  have h4 := le_weightedTotalDegree taperWeight he
  rw [w_top] at h3
  rw [w_taper] at h4
  have hge := w_grade e
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hge]
  omega

/-! ### One depth -/

theorem exists_depthSpace (f : R) (hf : f ≠ 0) (bl bh jl jh : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hbh : f.weightedTotalDegree gradeWeight ≤ bh)
    (hjl : jl ≤ f.weightedTotalDegree oldWeight) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (σb σj σt r a : ℕ) :
    ∃ C : Submodule 𝕜 R, FiniteDimensional 𝕜 C ∧
      depthDim σb σj σt bl bh jl jh r a ≤ (Module.finrank 𝕜 C : ℤ) ∧
      (∀ c ∈ C, f ∣ c → c = 0) ∧
      (∀ c ∈ C, f ^ a * c ∈ restrictSupport 𝕜 jetExponents) ∧
      (∀ c ∈ C, c ≠ 0 → DepthOK bh jh r a ∧
        c ∈ restrictSupport 𝕜 (taperBox ((r - a) * σb) ((r - a) * σj) ((r - a) * σt) 131312)) := by
  classical
  by_cases hok : DepthOK bh jh r a
  swap
  · refine ⟨⊥, inferInstance, ?_, ?_, ?_, ?_⟩
    · simp [depthDim, hok]
    · intro c hc _; exact (Submodule.mem_bot 𝕜).mp hc
    · intro c hc
      rw [(Submodule.mem_bot 𝕜).mp hc, mul_zero]
      exact Submodule.zero_mem _
    · intro c hc hne; exact absurd ((Submodule.mem_bot 𝕜).mp hc) hne
  obtain ⟨h3a, har, hab, haj, haΘ⟩ := hok
  set B := depthB σb bh r a with hBdef
  set J := depthJ σj jh r a with hJdef
  set Θ := depthΘ bh jh a with hΘdef
  let T := (r - a) * σt
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
  -- the cofactors form a small space
  have hGdim : ∃ _ : Module.Finite 𝕜 G,
      (Module.finrank 𝕜 G : ℤ) ≤ multCount σb σj σt bl bh jl jh r a := by
    by_cases hguard : bl ≤ B ∧ jl ≤ J ∧ 26 * bl ≤ Θ
    · let Nset := taperBox (B - bl) (J - jl) T (Θ - 26 * bl)
      have hN := taperBox_finite (B - bl) (J - jl) T (Θ - 26 * bl)
      have : Module.Finite 𝕜 (restrictSupport 𝕜 Nset) := restrictSupport_finite hN
      have hle : G ≤ restrictSupport 𝕜 Nset := by
        intro g hg
        by_cases hg0 : g = 0
        · rw [hg0]; exact Submodule.zero_mem _
        · refine restrictSupport_mono 𝕜 (taperBox_mono ?_ ?_ le_rfl ?_)
            (cofactor_mem f hf _ _ rfl rfl hg0 hg).2
          · exact Nat.sub_le_sub_left hbl B
          · exact Nat.sub_le_sub_left hjl J
          · exact Nat.sub_le_sub_left (Nat.mul_le_mul_left 26 hbl) Θ
      have : Module.Finite 𝕜 G := Submodule.finiteDimensional_of_le hle
      refine ⟨inferInstance, ?_⟩
      have h1 := Submodule.finrank_mono hle
      have h2 := finrank_restrictSupport_finset (K := 𝕜) hN.toFinset
      rw [Set.Finite.coe_toFinset] at h2
      have h3 := taperBox_card (B - bl) (J - jl) T (Θ - 26 * bl)
      have h4 : multCount σb σj σt bl bh jl jh r a =
          boxCount (B - bl) (J - jl) T (Θ - 26 * bl) := by
        unfold multCount
        simp only [B, J, Θ, T] at hguard ⊢
        simp only [hguard, and_self, ↓reduceIte]
      rw [h4, ← h3]
      change Module.finrank 𝕜 G ≤ Module.finrank 𝕜 (restrictSupport 𝕜 Nset) at h1
      rw [h2] at h1
      exact_mod_cast h1
    · have hbot : G = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        by_contra hg0
        obtain ⟨h1, h2, h3⟩ := (cofactor_mem f hf _ _ rfl rfl hg0 hg).1
        exact hguard ⟨hbl.trans h1, hjl.trans h2, (Nat.mul_le_mul_left 26 hbl).trans h3⟩
      rw [hbot]
      refine ⟨inferInstance, ?_⟩
      have h4 : multCount σb σj σt bl bh jl jh r a = 0 := by
        unfold multCount
        simp only [B, J, Θ] at hguard
        simp only [hguard, ↓reduceIte]
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
  · have hd : depthDim σb σj σt bl bh jl jh r a =
        max 0 (boxCount B J T Θ - multCount σb σj σt bl bh jl jh r a) := by
      unfold depthDim
      have hok' : DepthOK bh jh r a := ⟨h3a, har, hab, haj, haΘ⟩
      simp only [hok', ↓reduceIte]
      rfl
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
    have hcM := hCM hc
    refine pow_mul_mem_source f hf bh jh hbh hjh ?_ ?_ haΘ hcM
    · have : B ≤ 4012 - a * bh := min_le_right _ _
      omega
    · have : J ≤ 1650 - a * jh := min_le_right _ _
      omega
  · intro c hc _
    refine ⟨⟨h3a, har, hab, haj, haΘ⟩, ?_⟩
    exact restrictSupport_mono 𝕜 (taperBox_mono (min_le_left _ _) (min_le_left _ _) le_rfl
      (Nat.sub_le _ _)) (hCM hc)

/-! ### The direct sum over the depths -/

private theorem shift_sum (f : R) (n : ℕ) (u : ℕ → R) :
    (∑ i ∈ range n, f ^ (i + 1) * u (i + 1)) = f * ∑ i ∈ range n, f ^ i * u (i + 1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem fadic_zero (f : R) (hf : f ≠ 0) :
    ∀ (n : ℕ) (u : ℕ → R), (∀ i < n, f ∣ u i → u i = 0) →
      (∑ i ∈ range n, f ^ i * u i) = 0 → ∀ i < n, u i = 0 := by
  intro n
  induction n with
  | zero => intro u _ _ i hi; omega
  | succ n ih =>
    intro u hu h
    rw [Finset.sum_range_succ', shift_sum, pow_zero, one_mul] at h
    have h0 : u 0 = 0 :=
      hu 0 (Nat.succ_pos n) ⟨-(∑ i ∈ range n, f ^ i * u (i + 1)), by linear_combination h⟩
    rw [h0, add_zero] at h
    have hT : (∑ i ∈ range n, f ^ i * u (i + 1)) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hf
      · exact h1
    have hshift := ih (fun i => u (i + 1))
      (fun i hi hdiv => hu (i + 1) (Nat.succ_lt_succ hi) hdiv) hT
    intro i hi
    cases i with
    | zero => exact h0
    | succ i => exact hshift i (Nat.lt_of_succ_lt_succ hi)

theorem fadic_shape (f : R) :
    ∀ (a n : ℕ) (u : ℕ → R), a < n → (∀ i < a, u i = 0) →
      ∃ h : R, (∑ i ∈ range n, f ^ i * u i) = f ^ a * (u a + f * h) := by
  intro a
  induction a with
  | zero =>
    intro n u hn _
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨∑ i ∈ range m, f ^ i * u (i + 1), ?_⟩
    rw [Finset.sum_range_succ', shift_sum]
    ring
  | succ a ih =>
    intro n u hn hlow
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨h, hh⟩ := ih m (fun i => u (i + 1)) (by omega)
      (fun i hi => hlow (i + 1) (by omega))
    refine ⟨h, ?_⟩
    rw [Finset.sum_range_succ', shift_sum, hlow 0 (Nat.succ_pos a), hh]
    ring

/-- **The f-adic gate space of level `r`.** -/
theorem exists_fadicSpace (f : R) (hf : f ≠ 0) (bl bh jl jh : ℕ)
    (hbl : bl ≤ f.weightedTotalDegree gradeWeight) (hbh : f.weightedTotalDegree gradeWeight ≤ bh)
    (hjl : jl ≤ f.weightedTotalDegree oldWeight) (hjh : f.weightedTotalDegree oldWeight ≤ jh)
    (σb σj σt r : ℕ) :
    ∃ U : Submodule 𝕜 R,
      U ≤ restrictSupport 𝕜 jetExponents ∧
      fadicDim σb σj σt bl bh jl jh r ≤ (Module.finrank 𝕜 U : ℤ) ∧
      ∀ v ∈ U, v ≠ 0 → ∃ (a : ℕ) (c h : R),
        3 * a ≤ r ∧ a < r ∧ v = f ^ a * (c + f * h) ∧ c ≠ 0 ∧ ¬ f ∣ c ∧
        c ∈ restrictSupport 𝕜
          (taperBox ((r - a) * σb) ((r - a) * σj) ((r - a) * σt) 131312) := by
  classical
  choose C hCfin hCdim hCdvd hCsrc hCbox using
    fun a => exists_depthSpace f hf bl bh jl jh hbl hbh hjl hjh σb σj σt r a
  let n := r / 3 + 1
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
    unfold fadicDim
    rw [← Fin.sum_univ_eq_sum_range (fun a => depthDim σb σj σt bl bh jl jh r a) n, Nat.cast_sum]
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
    obtain ⟨hok, hbox⟩ := hCbox a _ hcC hane
    refine ⟨a, seq w a, h, hok.1, hok.2.1, ?_, hane, ?_, hbox⟩
    · rw [← hh, ← hseq]
    · intro hdvd
      exact hane (hCdvd a _ hcC hdvd)

end Field

end FadicGate

#print axioms FadicGate.pow_mul_mem_source
#print axioms FadicGate.cofactor_mem
#print axioms FadicGate.exists_depthSpace
#print axioms FadicGate.exists_fadicSpace
