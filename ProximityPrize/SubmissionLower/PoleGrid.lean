import ProximityPrize.SubmissionLower.PoleFamily

namespace PoleGrid

open PoleBlocks PoleFamily
open scoped BigOperators

def rowBound {U B J : ℕ} (v : Label U B J) : ℕ :=
  ∑ s : Fin (min v.2.1.val B+1),
    min (slotCount (offset v) J s.val) (((B+J : ℕ) : ℤ)-offset v-s.val).toNat

def colBound {U B J : ℕ} (v : Label U B J) : ℕ :=
  ∑ q : ColumnGrade v.2.1.val B (U-v.1.val), slotCount (offset v) J q.val.val

def saving {U B J : ℕ} (v : Label U B J) : ℕ :=
  rowBound v - blockBound v

def rowSum (B J g : ℕ) : ℕ :=
  ∑ s : Fin (B+1), min (min J s.val+1) (B+J-g-s.val)

def colSum (B J ell : ℕ) : ℕ :=
  ∑ q ∈ Finset.Icc ell B, (min J q+1)

theorem rowSum_anti (B J : ℕ) : Antitone (rowSum B J) := by
  intro g g' hg
  exact Finset.sum_le_sum fun s _ ↦ min_le_min le_rfl (by omega)

theorem colSum_anti (B J : ℕ) : Antitone (colSum B J) := by
  intro ell ell' he
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rw [Finset.mem_Icc] at hq ⊢
    exact ⟨he.trans hq.1,hq.2⟩
  · intro q _ _
    exact Nat.zero_le _

def sample (U B J d ell g : ℕ)
    (hd : d ≤ U) (hell : ell ≤ B) (hg : g < B+J) : Label U B J :=
  ⟨⟨U-d, by omega⟩, ⟨d+ell, by dsimp; omega⟩, ⟨g+J, by omega⟩⟩

@[simp] theorem sample_offset (U B J d ell g : ℕ)
    (hd : d ≤ U) (hell : ell ≤ B) (hg : g < B+J) :
    offset (sample U B J d ell g hd hell hg) = g := by
  simp [sample, offset]

private theorem rowBound_eq (U B J d ell g : ℕ)
    (hB : B ≤ d) (hd : d ≤ U) (hell : ell ≤ B) (hg : g < B+J) :
    rowBound (sample U B J d ell g hd hell hg) = rowSum B J g := by
  unfold rowBound rowSum
  rw [sample_offset]
  change (∑ s : Fin (min (d+ell) B+1),
    min (slotCount (g : ℤ) J s.val) (((B+J : ℕ) : ℤ)-(g : ℤ)-s.val).toNat) = _
  have hmin : min (d+ell) B = B := min_eq_right (by omega)
  rw [hmin]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have he : (((B+J : ℕ) : ℤ)-(g : ℤ)-s.val).toNat = B+J-g-s.val := by omega
  rw [he]
  simp [slotCount]

private theorem colBound_eq (U B J d ell g : ℕ)
    (hB : B ≤ d) (hd : d ≤ U) (hell : ell ≤ B) (hg : g < B+J) :
    colBound (sample U B J d ell g hd hell hg) = colSum B J ell := by
  classical
  unfold colBound colSum
  rw [sample_offset]
  change (∑ q : ColumnGrade (d+ell) B (U-(U-d)), slotCount (g : ℤ) J q.val.val) = _
  rw [Nat.sub_sub_self hd]
  have hmin : min (d+ell) B = B := min_eq_right (by omega)
  have hdiff : d+ell-d=ell := by omega
  unfold ColumnGrade
  rw [hmin, hdiff]
  let e : {q : Fin (B+1) // ell ≤ q.val} ≃ ↥(Finset.Icc ell B) :=
    { toFun := fun q ↦ ⟨q.val.val, Finset.mem_Icc.mpr ⟨q.property, Nat.le_of_lt_succ q.val.isLt⟩⟩
      invFun := fun q ↦ ⟨⟨q.val, Nat.lt_succ_of_le (Finset.mem_Icc.mp q.property).2⟩,
        (Finset.mem_Icc.mp q.property).1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    _ = ∑ q : ↥(Finset.Icc ell B), (min J q.val+1) := by
      apply Fintype.sum_equiv e
      intro q
      simp [e,slotCount]
    _ = _ := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach _ (fun q : ℕ ↦ min J q+1)

/-- Endpoints certify every label in a rectangle: the top offset minimizes
row capacity and the lowest input grade maximizes column capacity. -/
theorem sample_lower_saving (U B J d ell g lLo gHi : ℕ)
    (hB : B ≤ d) (hd : d ≤ U) (hell : ell ≤ B) (hg : g < B+J)
    (hlLo : lLo ≤ ell) (hgHi : g ≤ gHi) :
    rowSum B J gHi - colSum B J lLo ≤ saving (sample U B J d ell g hd hell hg) := by
  unfold saving
  change _ ≤ rowBound _ - min (colBound _) (rowBound _)
  rw [rowBound_eq U B J d ell g hB hd hell hg, colBound_eq U B J d ell g hB hd hell hg]
  have hr := rowSum_anti B J hgHi
  have hc := colSum_anti B J hlLo
  exact by omega

/-- Any injective collection of witnesses gives a certified lower saving. -/
theorem saving_of_witnesses {U B J : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Label U B J) (he : Function.Injective e) (w : ι → ℕ)
    (hw : ∀ i, w i ≤ saving (e i)) :
    (∑ i, w i) ≤ (∑ v : Label U B J, rowBound v) - (∑ v : Label U B J, blockBound v) := by
  classical
  have hadd : (∑ v : Label U B J, saving v) + (∑ v : Label U B J, blockBound v) =
      ∑ v : Label U B J, rowBound v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    unfold saving
    exact Nat.sub_add_cancel (min_le_right _ _)
  calc
    (∑ i, w i) ≤ ∑ i, saving (e i) := Finset.sum_le_sum fun i _ ↦ hw i
    _ = ∑ v ∈ Finset.univ.image e, saving v := by
      rw [Finset.sum_image]
      exact fun a _ b _ hab ↦ he hab
    _ ≤ ∑ v : Label U B J, saving v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun v _ _ ↦ Nat.zero_le _)
    _ = _ := by omega

structure Rectangle (B J : ℕ) where
  gradeLo : ℕ
  gradeHi : ℕ
  offsetLo : ℕ
  offsetHi : ℕ
  gradeOrder : gradeLo ≤ gradeHi
  gradeBound : gradeHi ≤ B
  offsetOrder : offsetLo ≤ offsetHi
  offsetBound : offsetHi < B+J

abbrev RectPoint (U B J : ℕ) (r : Rectangle B J) :=
  Fin (U-B+1) × Fin (r.offsetHi-r.offsetLo+1) × Fin (r.gradeHi-r.gradeLo+1)

def rectSample {U B J : ℕ} (hU : B ≤ U) (r : Rectangle B J)
    (p : RectPoint U B J r) : Label U B J :=
  sample U B J (B+p.1.val) (r.gradeLo+p.2.2.val) (r.offsetLo+p.2.1.val)
    (by have := p.1.isLt; omega)
    (by have := p.2.2.isLt; have := r.gradeOrder; have := r.gradeBound; omega)
    (by have := p.2.1.isLt; have := r.offsetOrder; have := r.offsetBound; omega)

theorem rectSample_injective {U B J : ℕ} (hU : B ≤ U) (r : Rectangle B J) :
    Function.Injective (rectSample hU r) := by
  intro p q hpq
  have hu := congrArg (fun v : Label U B J ↦ v.1.val) hpq
  have hn := congrArg (fun v : Label U B J ↦ v.2.1.val) hpq
  have hg := congrArg (fun v : Label U B J ↦ v.2.2.val) hpq
  simp [rectSample,sample] at hu hn hg
  have hp := p.1.isLt
  have hq := q.1.isLt
  exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))

def rectBenefit {B J : ℕ} (r : Rectangle B J) : ℕ :=
  rowSum B J r.offsetHi - colSum B J r.gradeLo

theorem rect_sample_saving {U B J : ℕ} (hU : B ≤ U) (r : Rectangle B J)
    (p : RectPoint U B J r) :
    rectBenefit r ≤ saving (rectSample hU r p) := by
  apply sample_lower_saving
  · omega
  · omega
  · have := p.2.1.isLt
    have := r.offsetOrder
    omega

/-- Separation in either interval axis prevents repeated witnesses. -/
def Separated {B J : ℕ} (r r' : Rectangle B J) : Prop :=
  r.gradeHi < r'.gradeLo ∨ r'.gradeHi < r.gradeLo ∨
    r.offsetHi < r'.offsetLo ∨ r'.offsetHi < r.offsetLo

theorem rectSamples_injective_of_separated {U B J : ℕ} (hU : B ≤ U) {ι : Type*}
    (rects : ι → Rectangle B J) (hsep : Pairwise (fun i j ↦ Separated (rects i) (rects j))) :
    Function.Injective (fun p : Sigma (fun i ↦ RectPoint U B J (rects i)) ↦
      rectSample hU (rects p.1) p.2) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ h
  by_cases he : i = j
  · subst j
    have hpq := rectSample_injective hU (rects i) h
    change p = q at hpq
    exact congrArg (Sigma.mk i) hpq
  · exfalso
    have hs := hsep he
    have hd := congrArg (fun v : Label U B J ↦ v.1.val) h
    have hn := congrArg (fun v : Label U B J ↦ v.2.1.val) h
    have hg := congrArg (fun v : Label U B J ↦ v.2.2.val) h
    simp [rectSample,sample] at hd hn hg
    have hpa := p.1.isLt
    have hqa := q.1.isLt
    have hpb := p.2.1.isLt
    have hqb := q.2.1.isLt
    have hpc := p.2.2.isLt
    have hqc := q.2.2.isLt
    have hgi := (rects i).gradeOrder
    have hgj := (rects j).gradeOrder
    have hoi := (rects i).offsetOrder
    have hoj := (rects j).offsetOrder
    unfold Separated at hs
    rcases hs with hlt | hlt | hlt | hlt <;> omega

/-- A union of rectangular samples is valid whenever the label assignment is
injective. This exposes the disjointness condition directly to certificates. -/
theorem rectangles_saving {U B J : ℕ} (hU : B ≤ U) {ι : Type*} [Fintype ι]
    (rects : ι → Rectangle B J)
    (hdisj : Function.Injective (fun p : Sigma (fun i ↦ RectPoint U B J (rects i)) ↦
      rectSample hU (rects p.1) p.2)) :
    (∑ i, (U-B+1)*( (rects i).offsetHi-(rects i).offsetLo+1) *
        ((rects i).gradeHi-(rects i).gradeLo+1) * rectBenefit (rects i)) ≤
        (∑ v : Label U B J, rowBound v) - (∑ v : Label U B J, blockBound v) := by
  classical
  have h := saving_of_witnesses _ hdisj (fun p ↦ rectBenefit (rects p.1))
    (fun p ↦ rect_sample_saving hU _ p.2)
  rw [Fintype.sum_sigma] at h
  simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using h

theorem rectangle_saving {U B J : ℕ} (hU : B ≤ U) (r : Rectangle B J) :
    (U-B+1)*(r.offsetHi-r.offsetLo+1)*(r.gradeHi-r.gradeLo+1) * rectBenefit r ≤
      (∑ v : Label U B J, rowBound v) - (∑ v : Label U B J, blockBound v) := by
  have h := saving_of_witnesses _ (rectSample_injective hU r)
    (fun _ ↦ rectBenefit r) (rect_sample_saving hU r)
  simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using h

end PoleGrid
