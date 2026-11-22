import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast066

set_option Elab.async false
set_option autoImplicit false

namespace CurveListCoupledCap
noncomputable section
open MeasureTheory Set
open scoped Pointwise
open private split_cap oldCap volume_oldCap from ProximityPrize.SubmissionLower.Fast048

abbrev Space := Fin 4 → ℝ
private abbrev snoc (v : Fin 3 → ℝ) (z : ℝ) : Space := Fin.snoc (α := fun _ => ℝ) v z

/-- A cap in which the final jet contributes to every weight. -/
def body (b j c h : ℝ) : Set Space :=
  {x | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 ≤ b ∧
    x 1 + 2 * x 2 + 3 * x 3 ≤ j ∧ x 2 + 2 * x 3 ≤ c ∧ x 3 ≤ h}

/-- The chamber constraints must hold at the ends of the height interval. -/
def Chamber (b j c h : ℝ) : Prop :=
  0 ≤ h ∧ 2 * h ≤ c ∧ 2 * c ≤ j ∧ j ≤ b

theorem chamber_at {b j c h z : ℝ} (hp : Chamber b j c h) (hz : z ∈ Icc 0 h) :
    0 ≤ c - 2 * z ∧ 2 * (c - 2 * z) ≤ j - 3 * z ∧ j - 3 * z ≤ b - z := by
  obtain ⟨_, hc, hj, hb⟩ := hp
  exact ⟨by linarith [hz.2], by linarith [hz.1], by linarith [hz.1]⟩

/-- At a fixed height the remaining three coordinates obey the original cap. -/
theorem mem_slice (b j c h z : ℝ) (v : Fin 3 → ℝ) :
    snoc v z ∈ body b j c h ↔
      z ∈ Icc 0 h ∧ v ∈ oldCap (b-z) (j-3*z) (c-2*z) := by
  change ((∀ i, 0 ≤ snoc v z i) ∧
    snoc v z 0 + snoc v z 1 + snoc v z 2 + snoc v z 3 ≤ b ∧
    snoc v z 1 + 2 * snoc v z 2 + 3 * snoc v z 3 ≤ j ∧
    snoc v z 2 + 2 * snoc v z 3 ≤ c ∧ snoc v z 3 ≤ h) ↔ _
  have hs0 : snoc v z 0 = v 0 := Fin.snoc_apply_zero _ _
  have hs1 : snoc v z 1 = v 1 := by
    change snoc v z (Fin.castSucc (1 : Fin 3)) = v 1
    simp only [snoc, Fin.snoc_castSucc]
  have hs2 : snoc v z 2 = v 2 := by
    change snoc v z (Fin.castSucc (2 : Fin 3)) = v 2
    simp only [snoc, Fin.snoc_castSucc]
  have hs3 : snoc v z 3 = z := by
    change snoc v z (Fin.last 3) = z
    simp only [snoc, Fin.snoc_last]
  rw [hs0, hs1, hs2, hs3]
  constructor
  · rintro ⟨hn, hb, hj, hc, hh⟩
    exact ⟨⟨by simpa only [hs3] using hn 3, hh⟩,
      fun i => by simpa only [Fin.snoc_castSucc] using hn i.castSucc,
      by linarith, by linarith, by linarith⟩
  · rintro ⟨⟨hz, hh⟩, hn, hb, hj, hc⟩
    refine ⟨?_, by linarith, by linarith, by linarith, hh⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [snoc,Fin.snoc_last] using hz
    | cast i => simpa only [snoc,Fin.snoc_castSucc] using hn i

/-- Common height charges are preserved under Minkowski addition. -/
theorem body_add {b j c h B J C H : ℝ} (hp : Chamber b j c h) (hq : Chamber B J C H) :
    body (b+B) (j+J) (c+C) (h+H) = body b j c h + body B J C H := by
  ext x
  constructor
  · rintro ⟨hx, hb, hj, hc, hh⟩
    obtain ⟨w, hw₀, hw₁, hw₂, hw₃⟩ := split_cap (hx 3) hp.1 hq.1 hh
    obtain ⟨pc, pj, pb⟩ := chamber_at hp ⟨hw₀, hw₁⟩
    obtain ⟨qc, qj, qb⟩ := chamber_at hq ⟨hw₂, hw₃⟩
    obtain ⟨u, hu₀, hu₁, hu₂, hu₃⟩ := split_cap (hx 2) pc qc (by linarith)
    obtain ⟨v, hv₀, hv₁, hv₂, hv₃⟩ := split_cap (hx 1)
      (show 0 ≤ j - 3*w - 2*u by linarith)
      (show 0 ≤ J - 3*(x 3-w) - 2*(x 2-u) by linarith) (by linarith)
    obtain ⟨a, ha₀, ha₁, ha₂, ha₃⟩ := split_cap (hx 0)
      (show 0 ≤ b - w - v - u by linarith)
      (show 0 ≤ B - (x 3-w) - (x 1-v) - (x 2-u) by linarith) (by linarith)
    let y : Space := ![a,v,u,w]
    have hy : y ∈ body b j c h := by
      refine ⟨?_, ?_, ?_, ?_, hw₁⟩
      · intro i; fin_cases i <;> assumption
      · change a+v+u+w ≤ b
        linarith
      · change v+2*u+3*w ≤ j
        linarith
      · change u+2*w ≤ c
        linarith
    have hy' : x-y ∈ body B J C H := by
      refine ⟨?_, ?_, ?_, ?_, hw₃⟩
      · intro i; fin_cases i <;> assumption
      · change (x 0-a)+(x 1-v)+(x 2-u)+(x 3-w) ≤ B
        linarith
      · change (x 1-v)+2*(x 2-u)+3*(x 3-w) ≤ J
        linarith
      · change (x 2-u)+2*(x 3-w) ≤ C
        linarith
    exact Set.mem_add.mpr ⟨y, hy, x-y, hy', by abel⟩
  · intro hx
    obtain ⟨y, ⟨hy, hyb, hyj, hyc, hyh⟩, z, ⟨hz, hzb, hzj, hzc, hzh⟩, rfl⟩ := Set.mem_add.mp hx
    refine ⟨fun i => add_nonneg (hy i) (hz i), ?_, ?_, ?_, ?_⟩ <;>
      simp only [Pi.add_apply] <;> linarith

def density (b j c z : ℝ) : ℝ := (c-2*z) * (j-c-z) * (b-j/2+z/2)

theorem volume_body {b j c h : ℝ} (hp : Chamber b j c h) :
    volume (body b j c h) = ENNReal.ofReal (∫ z in (0 : ℝ)..h, density b j c z) := by
  have hm : MeasurableSet (body b j c h) := by
    unfold body
    measurability
  refine K1_13_7_5_3_4.volume_by_last hm hp.1 (by unfold density; fun_prop) ?_
    (fun z => oldCap (b-z) (j-3*z) (c-2*z)) (mem_slice b j c h) ?_
  · intro z hz
    obtain ⟨h₀,h₁,h₂⟩ := chamber_at hp hz
    exact mul_nonneg (mul_nonneg h₀ (by linarith)) (by linarith)
  · intro z hz
    obtain ⟨h₀,h₁,h₂⟩ := chamber_at hp hz
    rw [volume_oldCap h₀ h₂ h₁]
    congr 1
    unfold density
    ring

open K1_13_5_4_2_4 (Exponent exponentVector latticeBody capSupport mem_capSupport)
open private exists_scale from ProximityPrize.SubmissionLower.Fast048

def exponents (b j c h : ℕ) : Finset Exponent :=
  (capSupport ⟨b,j,c⟩ h).filter fun a =>
    a 0 + a 1 + a 2 + a 3 ≤ b ∧ a 1 + 2*a 2 + 3*a 3 ≤ j ∧ a 2 + 2*a 3 ≤ c

theorem mem_exponents_nat {b j c h : ℕ} {a : Exponent} :
    a ∈ exponents b j c h ↔ a 0 + a 1 + a 2 + a 3 ≤ b ∧
      a 1 + 2*a 2 + 3*a 3 ≤ j ∧ a 2 + 2*a 3 ≤ c ∧ a 3 ≤ h := by
  classical
  rw [exponents,Finset.mem_filter,mem_capSupport]
  change (a 0 + a 1 + a 2 ≤ b ∧ a 1 + 2*a 2 ≤ j ∧ a 2 ≤ c ∧ a 3 ≤ h) ∧ _ ↔ _
  constructor
  · rintro ⟨⟨_,_,_,hh⟩,hb,hj,hc⟩
    exact ⟨hb,hj,hc,hh⟩
  · rintro ⟨hb,hj,hc,hh⟩
    exact ⟨⟨by omega,by omega,by omega,hh⟩,hb,hj,hc⟩

theorem mem_exponents {b j c h : ℕ} {a : Exponent} :
    a ∈ exponents b j c h ↔ exponentVector a ∈ body b j c h := by
  rw [mem_exponents_nat]
  have h₁ : (a 0 : ℝ) + a 1 + a 2 + a 3 ≤ b ↔ a 0 + a 1 + a 2 + a 3 ≤ b := by norm_cast
  have h₂ : (a 1 : ℝ) + 2*(a 2 : ℝ) + 3*(a 3 : ℝ) ≤ j ↔ a 1 + 2*a 2 + 3*a 3 ≤ j := by norm_cast
  have h₃ : (a 2 : ℝ) + 2*(a 3 : ℝ) ≤ c ↔ a 2 + 2*a 3 ≤ c := by norm_cast
  have h₄ : (a 3 : ℝ) ≤ h ↔ a 3 ≤ h := Nat.cast_le
  change _ ↔ (∀ i, 0 ≤ (a i : ℝ)) ∧ (a 0 : ℝ) + a 1 + a 2 + a 3 ≤ b ∧
    (a 1 : ℝ) + 2*(a 2 : ℝ) + 3*(a 3 : ℝ) ≤ j ∧ (a 2 : ℝ) + 2*(a 3 : ℝ) ≤ c ∧ (a 3 : ℝ) ≤ h
  rw [h₁,h₂,h₃,h₄]
  exact ⟨fun h => ⟨fun _ => Nat.cast_nonneg _,h⟩,And.right⟩

open K1_13 (Shape)
open K1_13_5_4 (GeoRow)
open MvPolynomial (weightedTotalDegree le_weightedTotalDegree)

abbrev Fits (p : GeoRow 4) (s : Shape) (h : ℕ) : Prop :=
  ∀ a ∈ p.support, a ∈ exponents s.b s.j s.t h

abbrev totalWeight : Fin 4 → ℕ := ![1,1,1,1]
abbrev indexWeight : Fin 4 → ℕ := ![0,1,2,3]
abbrev topWeight : Fin 4 → ℕ := ![0,0,1,2]
abbrev heightWeight : Fin 4 → ℕ := Pi.single 3 1

theorem fits_weights {p : GeoRow 4} {b j c h : ℕ}
    (hb : weightedTotalDegree totalWeight p ≤ b) (hj : weightedTotalDegree indexWeight p ≤ j)
    (hc : weightedTotalDegree topWeight p ≤ c) (hh : weightedTotalDegree heightWeight p ≤ h) :
    Fits p ⟨b,j,c⟩ h := by
  intro a ha
  have hb' := (le_weightedTotalDegree totalWeight ha).trans hb
  have hj' := (le_weightedTotalDegree indexWeight ha).trans hj
  have hc' := (le_weightedTotalDegree topWeight ha).trans hc
  have hh' := (le_weightedTotalDegree heightWeight ha).trans hh
  rw [Finsupp.weight_single_one_apply] at hh'
  simp [Finsupp.weight_eq_sum,smul_eq_mul,Fin.sum_univ_four] at hb' hj' hc'
  rw [Nat.mul_comm (a 2) 2,Nat.mul_comm (a 3) 3] at hj'
  rw [Nat.mul_comm (a 3) 2] at hc'
  exact mem_exponents_nat.mpr ⟨hb',hj',hc',hh'⟩

theorem fits_mono {p : GeoRow 4} {s q : Shape} {h k : ℕ}
    (hb : s.b ≤ q.b) (hj : s.j ≤ q.j) (hc : s.t ≤ q.t) (hh : h ≤ k) (hp : Fits p s h) :
    Fits p q k := by
  intro a ha
  obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_exponents_nat.mp (hp a ha)
  exact mem_exponents_nat.mpr ⟨h₁.trans hb,h₂.trans hj,h₃.trans hc,h₄.trans hh⟩

theorem zero_mem_exponents (b j c h : ℕ) : (0 : Exponent) ∈ exponents b j c h := by
  simp [mem_exponents_nat]

theorem single_mem_exponents {b j c h : ℕ} (hb : 1 ≤ b) (hj : 3 ≤ j) (hc : 2 ≤ c)
    (hh : 1 ≤ h) (i : Fin 4) : Finsupp.single i 1 ∈ exponents b j c h := by
  apply mem_exponents_nat.mpr
  fin_cases i <;> simp [Finsupp.single_apply] <;> omega

theorem exponents_downward (b j c h : ℕ) : K1_13_5_4_2_4.Downward (exponents b j c h) := by
  intro a d ha hd
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  have h₃ := hd 3
  obtain ⟨hb,hj,hc,hh⟩ := mem_exponents_nat.mp ha
  exact mem_exponents_nat.mpr ⟨by omega,by omega,by omega,by omega⟩

theorem convex_body (b j c h : ℝ) : Convex ℝ (body b j c h) := by
  intro x hx y hy a d ha hd had
  obtain ⟨hx,hxb,hxj,hxc,hxh⟩ := hx
  obtain ⟨hy,hyb,hyj,hyc,hyh⟩ := hy
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hd (hy i)),?_,?_,?_,?_⟩ <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · nlinarith [mul_le_mul_of_nonneg_left hxb ha, mul_le_mul_of_nonneg_left hyb hd,
      congrArg (fun t : ℝ => t*b) had]
  · nlinarith [mul_le_mul_of_nonneg_left hxj ha, mul_le_mul_of_nonneg_left hyj hd,
      congrArg (fun t : ℝ => t*j) had]
  · nlinarith [mul_le_mul_of_nonneg_left hxc ha, mul_le_mul_of_nonneg_left hyc hd,
      congrArg (fun t : ℝ => t*c) had]
  · nlinarith [mul_le_mul_of_nonneg_left hxh ha, mul_le_mul_of_nonneg_left hyh hd,
      congrArg (fun t : ℝ => t*h) had]

private def parameter (b j c h : ℝ) (u : Space) : Space :=
  let t := u 3*h
  let z := u 2*(c-2*t)
  let y := u 1*(j-3*t-2*z)
  ![u 0*(b-t-y-z),y,z,t]

theorem parameter_update (b j c h : ℝ) (u : Space) (i : Fin 4) :
    parameter b j c h u = (1-u i) • parameter b j c h (Function.update u i 0) +
      u i • parameter b j c h (Function.update u i 1) := by
  funext j'
  fin_cases i <;> fin_cases j' <;>
    simp [parameter, Pi.add_apply, smul_eq_mul, Function.update] <;> ring

theorem parameter_corner (b j c h : ℕ) (hc : 2*h ≤ c) (hj : 2*c ≤ j) (hb : j ≤ b)
    (u : Space) (hu : ∀ i, u i = 0 ∨ u i = 1) :
    parameter b j c h u ∈ latticeBody (exponents b j c h) := by
  classical
  have hbinary (i : Fin 4) : ∃ v : ℕ, (v : ℝ) = u i ∧ v ≤ 1 := by
    rcases hu i with hi | hi
    · exact ⟨0, by simpa using hi.symm, Nat.zero_le 1⟩
    · exact ⟨1, by simpa using hi.symm, le_rfl⟩
  choose v hv using hbinary
  let t := v 3*h
  let z := v 2*(c-2*t)
  let y := v 1*(j-3*t-2*z)
  let a := v 0*(b-t-y-z)
  have ht : t ≤ h := by simpa [t] using Nat.mul_le_mul_right h (hv 3).2
  have hz : z ≤ c-2*t := by simpa [z] using Nat.mul_le_mul_right (c-2*t) (hv 2).2
  have hy : y ≤ j-3*t-2*z := by simpa [y] using Nat.mul_le_mul_right (j-3*t-2*z) (hv 1).2
  have ha : a ≤ b-t-y-z := by simpa [a] using Nat.mul_le_mul_right (b-t-y-z) (hv 0).2
  let w : Fin 4 → ℕ := ![a,y,z,t]
  let e : Exponent := Finsupp.equivFunOnFinite.symm w
  have he (i : Fin 4) : e i = w i := congrFun (Finsupp.equivFunOnFinite.apply_symm_apply w) i
  have hem : e ∈ exponents b j c h := by
    apply mem_exponents.mpr
    change (∀ i, 0 ≤ (e i : ℝ)) ∧ (e 0 : ℝ) + e 1 + e 2 + e 3 ≤ b ∧
      (e 1 : ℝ) + 2*(e 2 : ℝ) + 3*(e 3 : ℝ) ≤ j ∧ (e 2 : ℝ) + 2*(e 3 : ℝ) ≤ c ∧ (e 3 : ℝ) ≤ h
    rw [he 0,he 1,he 2,he 3]
    exact ⟨fun _ => Nat.cast_nonneg _,by change (a : ℝ)+y+z+t ≤ b; exact_mod_cast (show a+y+z+t ≤ b by omega),
      by change (y : ℝ)+2*(z : ℝ)+3*(t : ℝ) ≤ j; exact_mod_cast (show y+2*z+3*t ≤ j by omega),
      by change (z : ℝ)+2*(t : ℝ) ≤ c; exact_mod_cast (show z+2*t ≤ c by omega),
      by exact_mod_cast ht⟩
  apply subset_convexHull ℝ _
  refine ⟨e,hem,?_⟩
  have ht' : (t : ℝ) = u 3*h := by simp only [t,Nat.cast_mul,(hv 3).1]
  have hz' : (z : ℝ) = u 2*((c : ℝ)-2*(t : ℝ)) := by
    simp only [z,Nat.cast_mul,Nat.cast_sub (show 2*t ≤ c by omega),Nat.cast_ofNat,(hv 2).1]
  have hy' : (y : ℝ) = u 1*((j : ℝ)-3*(t : ℝ)-2*(z : ℝ)) := by
    simp only [y,Nat.cast_mul,Nat.cast_sub (show 2*z ≤ j-3*t by omega),
      Nat.cast_sub (show 3*t ≤ j by omega),Nat.cast_ofNat,(hv 1).1]
  have ha' : (a : ℝ) = u 0*((b : ℝ)-(t : ℝ)-(y : ℝ)-(z : ℝ)) := by
    simp only [a,Nat.cast_mul,Nat.cast_sub (show z ≤ b-t-y by omega),
      Nat.cast_sub (show y ≤ b-t by omega),Nat.cast_sub (show t ≤ b by omega),(hv 0).1]
  funext i
  change (e i : ℝ) = parameter b j c h u i
  rw [he i]
  fin_cases i
  · change (a : ℝ) = _
    rw [ha',hy',hz',ht']; rfl
  · change (y : ℝ) = _
    rw [hy',hz',ht']; rfl
  · change (z : ℝ) = _
    rw [hz',ht']; rfl
  · exact ht'

theorem parameter_cube (b j c h : ℕ) (hc : 2*h ≤ c) (hj : 2*c ≤ j) (hb : j ≤ b)
    (S : Finset (Fin 4)) (u : Space) (hu : ∀ i ∈ S, 0 ≤ u i ∧ u i ≤ 1)
    (hu' : ∀ i ∉ S, u i = 0 ∨ u i = 1) :
    parameter b j c h u ∈ latticeBody (exponents b j c h) := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty => exact parameter_corner b j c h hc hj hb u (fun i => hu' i (by simp))
  | insert i S hi ih =>
      have upd (q : ℝ) (hq : q = 0 ∨ q = 1) :
          parameter b j c h (Function.update u i q) ∈ latticeBody (exponents b j c h) := by
        apply ih
        · intro k hk
          have hn : k ≠ i := fun he => hi (he ▸ hk)
          simpa [Function.update_of_ne hn] using hu k (Finset.mem_insert_of_mem hk)
        · intro k hk
          by_cases he : k = i
          · subst k; simpa using hq
          · rw [Function.update_of_ne he]
            exact hu' k (by simp [he,hk])
      have h := hu i (Finset.mem_insert_self i S)
      rw [parameter_update]
      exact convex_convexHull ℝ _ (upd 0 (Or.inl rfl)) (upd 1 (Or.inr rfl))
        (sub_nonneg.mpr h.2) h.1 (sub_add_cancel 1 (u i))

theorem lattice_exponents (b j c h : ℕ) (hc : 2*h ≤ c) (hj : 2*c ≤ j) (hb : j ≤ b) :
    latticeBody (exponents b j c h) = body b j c h := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_body _ _ _ _)
    rintro _ ⟨a,ha,rfl⟩
    exact mem_exponents.mp ha
  · intro x hx
    obtain ⟨hn,hb',hj',hc',hh⟩ := hx
    obtain ⟨u₃,hl₃,hr₃,he₃⟩ := exists_scale (hn 3) hh
    obtain ⟨u₂,hl₂,hr₂,he₂⟩ := exists_scale (hn 2) (show x 2 ≤ c-2*x 3 by linarith)
    obtain ⟨u₁,hl₁,hr₁,he₁⟩ := exists_scale (hn 1) (show x 1 ≤ j-3*x 3-2*x 2 by linarith)
    obtain ⟨u₀,hl₀,hr₀,he₀⟩ := exists_scale (hn 0) (show x 0 ≤ b-x 3-x 1-x 2 by linarith)
    let u : Space := ![u₀,u₁,u₂,u₃]
    have he : parameter b j c h u = x := by
      funext i
      fin_cases i <;> simp only [parameter,u,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,he₃,he₂,he₁,he₀] <;> rfl
    rw [← he]
    apply parameter_cube b j c h hc hj hb Finset.univ
    · intro i _; fin_cases i <;> exact ⟨by assumption,by assumption⟩
    · simp

end
end CurveListCoupledCap
