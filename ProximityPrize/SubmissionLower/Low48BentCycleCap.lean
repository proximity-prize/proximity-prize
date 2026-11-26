import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup50
import ProximityPrize.SubmissionLower.Fat6966Bank24000
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.R6960Front6960Rank4

section Merged6967_Low48BentCycleCap
set_option Elab.async false




set_option Elab.async false

-- merged module Low48Price
section Merged_Low48Price

set_option Elab.async false
namespace Low48Price
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev physicalDegree : ℕ := 133437
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev primaryBox : Shape := ⟨4012, 1650, 550⟩



abbrev BentCap := Shape × ℕ



def bentIntegral (B J T H : ℤ) : ℤ :=
  -576 * H ^ 5 + 160 * T ^ 2 * H ^ 3 - 480 * T ^ 3 * H ^ 2 + 540 * T ^ 4 * H
  + 960 * J * H ^ 4 - 320 * J * T * H ^ 3 + 960 * J * T ^ 2 * H ^ 2 - 1200 * J * T ^ 3 * H
  - 480 * J ^ 2 * H ^ 3 - 480 * J ^ 2 * T * H ^ 2 + 840 * J ^ 2 * T ^ 2 * H
  + 240 * J ^ 3 * H ^ 2 - 240 * J ^ 3 * T * H - 960 * B * H ^ 4 + 640 * B * T * H ^ 3
  - 1440 * B * T ^ 2 * H ^ 2 + 1440 * B * T ^ 3 * H + 640 * B * J * H ^ 3
  + 960 * B * J * T * H ^ 2 - 1440 * B * J * T ^ 2 * H - 480 * B * J ^ 2 * H ^ 2
  + 480 * B * J ^ 2 * T * H

def addBent (p q : BentCap) : BentCap := (p.1.plus q.1, p.2 + q.2)

def ambientMix (caps : List BentCap) : ℕ :=
  (caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) *
      bentIntegral s.1.b s.1.j s.1.t s.2) 0).toNat






end
end Low48Price

end Merged_Low48Price

-- merged module Low48BentCycleCap
section Merged_Low48BentCycleCap

set_option autoImplicit false
set_option Elab.async false

namespace Low48BentCycle

noncomputable section

open Low48BentLattice
open K1_13 (Shape InBox Row shape)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5)
open Low48Price (primaryBox taylorLength)
open Low48BentSupport (graph lifted)
open K1_13_6_2_4 (Exponent oldEmbedding old_section_box box5_iff)
open K1_13_6_2_4_1 (Grade unitGrade positiveDiagonal)
open MvPolynomial
open scoped Pointwise

def rawFamily (caps : Fin 5 → Cap) : Family := fun i => {m | Allowed (caps i) m}

def capFamily (caps : Fin 5 → Cap) : Family := fun i => latticePoints (caps i)

instance (caps : Fin 5 → Cap) (i : Fin 5) : Finite (capFamily caps i) :=
  inferInstanceAs (Finite (latticePoints (caps i)))


open Low48BentCycle (generator_mem_diagonal)

theorem diagonal_unit (B : Family) (h0 : ∀ i, 0 ∈ B i) (i : Fin 5) :
    diagonalExponents B (unitGrade i) = B i := by
  ext m
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hi : unitGrade i i = 1 := by simp [unitGrade]
    let j : Fin (unitGrade i i) := ⟨0, by omega⟩
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · exact hu i j
    · intro k _ hk
      exfalso
      apply hk
      exact Fin.ext (by omega : k.val = j.val)
    · simp
    · intro k _ hk
      have hkill : unitGrade i k = 0 := by simp [unitGrade, hk]
      have : IsEmpty (Fin (unitGrade i k)) := by rw [hkill]; infer_instance
      simp
    · simp
  · intro hm
    exact generator_mem_diagonal h0 (⟨i, ⟨m, hm⟩⟩ : Generator B)

theorem grade_sum (t : Grade) : (∑ i : Fin 5, t i • unitGrade i) = t := by
  ext i
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp [unitGrade]
  · intro j _ hj
    simp [unitGrade, Ne.symm hj]
  · simp

theorem diagonal_sum (B : Family) (s : Finset (Fin 5)) (t : Fin 5 → Grade) :
    diagonalExponents B (∑ i ∈ s, t i) = ∑ i ∈ s, diagonalExponents B (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (diagonal_nsmul B 0 0).trans (zero_smul _ _)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, diagonal_add, ih]

def capSum (caps : Fin 5 → Cap) (t : Grade) : Cap :=
  Sum Finset.univ (fun i => Scale (t i) (caps i))

theorem chamber_capSum (caps : Fin 5 → Cap) (h : ∀ i, Chamber (caps i)) (t : Grade) :
    Chamber (capSum caps t) :=
  chamber_sum _ _ (fun i _ => chamber_scale (h i) (t i))

theorem diagonal_cap (caps : Fin 5 → Cap) (h : ∀ i, Chamber (caps i)) (t : Grade) :
    diagonalExponents (capFamily caps) t = latticePoints (capSum caps t) := by
  have h0 (i : Fin 5) : 0 ∈ capFamily caps i := zero_mem (caps i)
  calc
    diagonalExponents (capFamily caps) t =
        ∑ i : Fin 5, diagonalExponents (capFamily caps) (t i • unitGrade i) := by
      conv_lhs => rw [← grade_sum t]
      exact diagonal_sum _ _ _
    _ = ∑ i : Fin 5, latticePoints (Scale (t i) (caps i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_nsmul, diagonal_unit _ h0]
      exact lattice_scale _ (h i) _
    _ = _ := lattice_sum _ _ (fun i _ => chamber_scale (h i) (t i))

theorem coeff_congr (S T : Set Exponent) [Finite S] [Finite T] (h : S = T) :
    (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField S) ⊥)).coeff 5 =
      (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField T) ⊥)).coeff 5 := by
  subst T
  rfl

theorem ambient_cap (caps : Fin 5 → Cap) (h : ∀ i, Chamber (caps i)) (v : Cap → ℚ)
    (hv : ∀ a, Chamber a →
      (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField (latticePoints a)) ⊥)).coeff 5 =
        v a) :
    32 * mixedDegree (capFamily caps) ⊥ Finset.univ =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        v (capSum caps (positiveDiagonal J)) := by
  unfold mixedDegree
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℚ) ^ 5 = 32 by norm_num, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [coeff_congr _ _ (diagonal_cap caps h _), hv _ (chamber_capSum caps h _)]

def caps (p : Shape) : Fin 5 → Cap :=
  ![(p, 0), (primaryBox, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]

theorem caps_chamber {p : Shape} (hb : p.j ≤ p.b) (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j) :
    ∀ i, Chamber (caps p i) := by
  intro i
  fin_cases i
  · change Chamber (p, 0)
    exact ⟨hb, show 3 * p.t ≤ p.j by omega, Nat.zero_le _⟩
  · change 1650 ≤ 4012 ∧ 3 * 550 ≤ 1650 ∧ 2 * 0 ≤ (550 : ℕ)
    decide
  · exact Low48BentSupport.graph_chamber ht hj
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 4)
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 3)


theorem old_section {q : Shape} {F : Row 4} (h : InBox (shape F) q) :
    Low48BentSupport.Box (q, 0) (oldEmbedding (toGeneric F)) := by
  intro m hm
  have hb := (box5_iff (a := (q, 0))).mp (old_section_box h) m hm
  simp only [K1_13_6_2_4.Allowed, Fin.sum_univ_four] at hb
  have h0 : m 4 = 0 := Nat.eq_zero_of_le_zero hb.2.2.2
  change m 0 + m 1 + m 2 + m 3 ≤ q.b ∧
    0 * m 0 + 1 * m 1 + 2 * m 2 + 3 * m 3 ≤ q.j ∧ m 3 ≤ q.t ∧ m 4 ≤ 0 at hb
  simpa [Allowed, h0] using hb

end

end Low48BentCycle

end Merged_Low48BentCycleCap

end Merged6967_Low48BentCycleCap

section Merged6967_Low49ActiveSplit
set_option Elab.async false

set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Low49ActiveSplit

private theorem distribute {n al ah bl bh : ℕ} (ha : al ≤ ah) (hb : bl ≤ bh)
    (hl : al + bl ≤ n) (hh : n ≤ ah + bh) :
    ∃ a b, a+b=n ∧ al≤a ∧ a≤ah ∧ bl≤b ∧ b≤bh := by
  let a := max al (n-bh)
  exact ⟨a,n-a,by dsimp [a]; omega⟩

private theorem distribute_under {n a b : ℕ} (h : n ≤ a+b)
    (hp : a%2=0 ∨ b%2=0) :
    ∃ x y, x+y=n ∧ x≤a ∧ y≤b ∧ (x%2=0 ∨ y%2=0) := by
  rcases hp with ha|hb
  · let x := min n a
    exact ⟨x,n-x,by dsimp [x]; omega⟩
  · let y := min n b
    exact ⟨n-y,y,by dsimp [y]; omega⟩

private theorem distribute_over {n al ah bl bh : ℕ} (ha : al≤ah) (hb : bl≤bh)
    (hl : al+bl≤n) (hh : n≤ah+bh) (he : ah%2=0 ∧ bh%2=0)
    (hp : al%2=0 ∨ bl%2=0) :
    ∃ x y, x+y=n ∧ al≤x ∧ x≤ah ∧ bl≤y ∧ y≤bh ∧ (x%2=0 ∨ y%2=0) := by
  by_cases hn : n%2=0
  · rcases hp with hA|hB
    · let x := min ah (n-bl)
      let w := x - x%2
      exact ⟨w,n-w,by dsimp [w,x]; omega⟩
    · let y := min bh (n-al)
      let w := y-y%2
      exact ⟨n-w,w,by dsimp [w,y]; omega⟩
  · obtain ⟨x,y,hx,ha,hxa,hb,hyb⟩ := distribute ha hb hl hh
    exact ⟨x,y,hx,ha,hxa,hb,hyb,by omega⟩

private theorem split_secondary {y z ja jb ta tb ca cb : ℕ}
    (hja : 3*ta≤ja ∧ 2*ca≤ja ∧ ca≤2*ta)
    (hjb : 3*tb≤jb ∧ 2*cb≤jb ∧ cb≤2*tb)
    (hev : ja%2=0 ∧ jb%2=0 ∧ ta%2=0 ∧ tb%2=0 ∧ ca%2=0 ∧ cb%2=0)
    (hp : (ca/2)%2=0 ∨ (cb/2)%2=0)
    (h : z≤ta+tb ∧ 2*y+3*z≤ja+jb) :
    ∃ ya yb za zb,
      ya+yb=y ∧ za+zb=z ∧ za≤ta ∧ zb≤tb ∧ 2*ya+3*za≤ja ∧ 2*yb+3*zb≤jb ∧
      (if y+2*z≤ca+cb then ya+2*za≤ca ∧ yb+2*zb≤cb
       else ca≤ya+2*za ∧ cb≤yb+2*zb) := by
  by_cases hc : y+2*z≤ca+cb
  · obtain ⟨za,zb,hz,_,hza,_,hzb⟩ := distribute (n:=z) (al:=0) (bl:=0)
      (ah:=ca/2) (bh:=cb/2) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨ya,yb,hy,_,hya,_,hyb⟩ := distribute (n:=y) (al:=0) (bl:=0)
      (ah:=ca-2*za) (bh:=cb-2*zb) (by omega) (by omega) (by omega) (by omega)
    exact ⟨ya,yb,za,zb,hy,hz,by omega,by omega,by omega,by omega,by simp only [hc,ite_true]; omega⟩
  · have hs : ∃ za zb, za+zb=z ∧ za≤ta ∧ zb≤tb ∧
        (ca-2*za)+(cb-2*zb) = ca+cb-2*z ∧ (za%2=0 ∨ zb%2=0) := by
      by_cases hz : 2*z≤ca+cb
      · obtain ⟨za,zb,hz',hza,hzb,hep⟩ :=
          distribute_under (n:=z) (a:=ca/2) (b:=cb/2) (by omega) hp
        exact ⟨za,zb,hz',by omega,by omega,by omega,hep⟩
      · obtain ⟨za,zb,hz',hza,hza',hzb,hzb',hep⟩ := distribute_over
          (al:=ca/2) (bl:=cb/2) (ah:=ta) (bh:=tb)
          (by omega) (by omega) (by omega) h.1 ⟨hev.2.2.1,hev.2.2.2.1⟩ hp
        exact ⟨za,zb,hz',hza',hzb',by omega,hep⟩
    obtain ⟨za,zb,hz,hza,hzb,hsmall,hParity⟩ := hs
    have hhalves : (ja-3*za+ (jb-3*zb))/2 = (ja-3*za)/2+(jb-3*zb)/2 := by omega
    obtain ⟨ya,yb,hy,hya,hya',hyb,hyb'⟩ := distribute (n:=y)
      (al:=ca-2*za) (bl:=cb-2*zb) (ah:=(ja-3*za)/2) (bh:=(jb-3*zb)/2)
      (by omega) (by omega) (by omega) (by omega)
    exact ⟨ya,yb,za,zb,hy,hz,hza,hzb,by omega,by omega,by simp only [hc,ite_false]; omega⟩

theorem split {x y z ja jb ta tb ca cb : ℕ}
    (hja : 3*ta≤ja ∧ 2*ca≤ja ∧ ca≤2*ta)
    (hjb : 3*tb≤jb ∧ 2*cb≤jb ∧ cb≤2*tb)
    (hev : ja%2=0 ∧ jb%2=0 ∧ ta%2=0 ∧ tb%2=0 ∧ ca%2=0 ∧ cb%2=0)
    (hp : (ca/2)%2=0 ∨ (cb/2)%2=0)
    (h : z≤ta+tb ∧ x+2*y+3*z≤ja+jb) :
    ∃ xa xb ya yb za zb,
      xa+xb=x ∧ ya+yb=y ∧ za+zb=z ∧ za≤ta ∧ zb≤tb ∧
      xa+2*ya+3*za≤ja ∧ xb+2*yb+3*zb≤jb ∧
      (xa+ya+za-(ja-ca))+(xb+yb+zb-(jb-cb)) = x+y+z-(ja+jb-(ca+cb)) := by
  obtain ⟨ya,yb,za,zb,hy,hz,hza,hzb,hya,hyb,hr⟩ :=
    split_secondary (y:=y) (z:=z) hja hjb hev hp (by omega)
  let aa := ja-ca-(ya+za)
  let ab := jb-cb-(yb+zb)
  let ma := ja-(2*ya+3*za)
  let mb := jb-(2*yb+3*zb)
  by_cases hc : y+2*z≤ca+cb
  · simp only [hc,ite_true] at hr
    by_cases hl : x+y+z≤ja+jb-(ca+cb)
    · obtain ⟨xa,xb,hx,_,hxa,_,hxb⟩ := distribute (n:=x) (al:=0) (bl:=0)
        (ah:=aa) (bh:=ab) (by omega) (by omega) (by omega) (by dsimp [aa,ab]; omega)
      exact ⟨xa,xb,ya,yb,za,zb,hx,hy,hz,hza,hzb,by dsimp [aa] at hxa; omega,
        by dsimp [ab] at hxb; omega,by dsimp [aa,ab] at *; omega⟩
    · obtain ⟨xa,xb,hx,hxa,hxa',hxb,hxb'⟩ := distribute (n:=x) (al:=aa) (bl:=ab)
        (ah:=ma) (bh:=mb) (by dsimp [aa,ma]; omega) (by dsimp [ab,mb]; omega)
        (by dsimp [aa,ab]; omega) (by dsimp [ma,mb]; omega)
      exact ⟨xa,xb,ya,yb,za,zb,hx,hy,hz,hza,hzb,by dsimp [ma] at hxa'; omega,
        by dsimp [mb] at hxb'; omega,by dsimp [aa,ab] at *; omega⟩
  · simp only [hc,ite_false] at hr
    obtain ⟨xa,xb,hx,_,hxa,_,hxb⟩ := distribute (n:=x) (al:=0) (bl:=0)
      (ah:=ma) (bh:=mb) (by omega) (by omega) (by omega) (by dsimp [ma,mb]; omega)
    exact ⟨xa,xb,ya,yb,za,zb,hx,hy,hz,hza,hzb,by dsimp [ma] at hxa; omega,
      by dsimp [mb] at hxb; omega,by dsimp [ma,mb] at *; omega⟩

end Low49ActiveSplit

end Merged6967_Low49ActiveSplit

section Merged6967_Low6966AllocWeight
set_option Elab.async false


set_option Elab.async false

/-! Low-side copy of `KoalaAllocationWeight` for the 69.61 box (142, 58, 15): full charge from index 56, denominator 374. -/
namespace Low6966AllocWeight
open K1_13 (Shape)
open scoped BigOperators

def fullCharge (j t : ℕ) : Prop := 56 ≤ j ∨ 15 ≤ t

instance (j t : ℕ) : Decidable (fullCharge j t) := by unfold fullCharge; infer_instance

def weight (b j t : ℕ) : ℕ := if fullCharge j t then 374 else min (b+4*j) 374

theorem mono {b j t B J T : ℕ} (hb : b ≤ B) (hj : j ≤ J) (ht : t ≤ T) :
    weight b j t ≤ weight B J T := by
  by_cases h : fullCharge j t
  · have h' : fullCharge J T := h.imp (fun k => k.trans hj) (fun k => k.trans ht)
    simp [weight, h, h']
  · by_cases h' : fullCharge J T
    · simpa [weight, h, h'] using (min_le_right (b+4*j) 374)
    · simpa [weight, h, h'] using
        (min_le_min (Nat.add_le_add hb (Nat.mul_le_mul_left 4 hj)) (le_refl 374))

theorem sum_le {top n : ℕ} (htop : top ≤ 15) (a : Fin n → Shape) (hfits : LowProfile6966.Fits top a)
    (s : Finset (Fin n)) : (∑ i ∈ s, weight (a i).b (a i).j (a i).t) ≤ 374 := by
  classical
  have part (f : Fin n → ℕ) : ∑ i ∈ s, f i ≤ ∑ i, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  by_cases hall : ∃ i ∈ s, fullCharge (a i).j (a i).t
  · obtain ⟨i, hi, hc⟩ := hall
    have only (j : Fin n) (hji : j ≠ i) : False := by
      have pair (f : Fin n → ℕ) : f i+f j ≤ ∑ k, f k := by
        rw [← Finset.sum_pair (Ne.symm hji)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      obtain ⟨ht,hj,_⟩ := hfits.1 j
      have hJ := (pair fun k => (a k).j).trans hfits.2.2.1
      have hT := (pair fun k => (a k).t).trans hfits.2.2.2
      rcases hc with h | h <;> omega
    have he : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j _ => by
      by_contra hne
      exact only j hne⟩
    rw [he, Finset.sum_singleton]
    simp [weight, hc]
  · have hw : ∀ i ∈ s, weight (a i).b (a i).j (a i).t ≤ (a i).b+4*(a i).j := by
      intro i hi
      simp [weight, show ¬ fullCharge (a i).j (a i).t from fun h => hall ⟨i,hi,h⟩]
    refine (Finset.sum_le_sum hw).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add ((part _).trans hfits.2.1)
      (Nat.mul_le_mul_left 4 ((part _).trans hfits.2.2.1))

#print axioms sum_le
end Low6966AllocWeight

end Merged6967_Low6966AllocWeight

section Merged6967_Low6966SurfaceLinearFour
set_option Elab.async false






set_option Elab.async false

-- merged module Low6966Monotone
section Merged_Low6966Monotone



-- merged module R6960Low6966RetainedFees
section Merged_R6960Low6966RetainedFees
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace LowProfile6966
open Finset
open K1_13 (Shape chart ceilDiv mixed32 shape)
open K1_13_8 (Valid)
open Low6966Fat (commonBox resultantBox)
open K1_13_8_4 (TotalLE)
open scoped BigOperators Classical
abbrev errors : ℕ := 262144-agreement
abbrev incidenceGap : ℕ := agreement-physicalDegree
abbrev taylorLength : ℕ := physicalDegree+1
abbrev fatOrder : ℕ := 21923
abbrev divisorOrder : ℕ := 20000
abbrev isolatedOrder : ℕ := 220
def lowDegreeCap : ℕ → ℕ
  | 3 => 27
  | 4 => 25
  | 5 => 22
  | 6 => 19
  | 7 => 14
  | 8 => 6
  | _ => 0
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (errors * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (errors * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated
def retainedTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 2158343791299739, 2158343791299739, 2158343791299739, 2502144872790737, 2853169289624949, 3213531186026336, 3585344706218855, 3970723994426466, 4371783194873127, 4790636451782796, 5229397909379435, 5690181711886999, 6175102003529451, 6686272928530745, 7225808631114844, 7795823255505704, 8398430945927286, 9035745846603546, 9709882101758445, 10422953855615941, 11177075252399994, 11974360436334560, 12816923551643602, 13706878742551074, 14646340153280940, 15637421928057153, 16682238211103677]
  | 4,1 => [0, 0, 5084581920206611, 5084581920206611, 5084581920206611, 5939082899406459, 6802921358173483, 7678211440731636, 8567067291304884, 9471603054117181, 10393932873392487, 11336170893354761, 12300431258227963, 13288828112236049, 14303475599602981, 15346487864552715, 16419979051309211, 17526063304096428, 18666854767138326, 19844467584658860, 21061015900881993, 22318613860031681, 23619375606331885, 24965415284006560, 26358847037279670, 27801785010375170]
  | 5,1 => [0, 0, 10839217099761532, 10839217099761532, 10839217099761532, 10839217099761532, 12430409652199293, 14033053828428185, 15649263772672170, 17281153629155205, 18930837542101250, 20600429655734262, 22292044114278202, 24007795061957024, 25749796642994694, 27520163001615166, 29321008282042400, 31154446628500355, 33022592185212991, 34927559096404263, 36871461506298134, 38856413559118558, 40884529399089500]
  | 6,1 => [0, 0, 18805928703070084, 18805928703070084, 18805928703070084, 18805928703070084, 18805928703070084, 21080209774346668, 23368056613638343, 25671583365169068, 27992904173162802, 30334133181843506, 32697384535435135, 35084772378161650, 37498410854247010, 39940414107915173, 42412896283390097, 44917971524895743, 47457753976656067, 50034357782895031]
  | 7,1 => [0, 0, 0, 29118013708689678, 29118013708689678, 29118013708689678, 29118013708689678, 29118013708689678, 32077497443029043, 35052661089607461, 38045618792648885, 41058484696377279, 44093372945016599, 47152397682790804, 50237673053923854]
  | 8,1 => [0, 0, 0, 41777586260844276, 41777586260844276, 41777586260844276, 41777586260844276]
  | 6,2 => [0, 0, 61289770173836758, 61289770173836768, 61289770173836782, 61289770173836799, 61289770173836821, 69920260416388496, 78604664577623767, 87351439741583314, 96169042992307818, 105065931413837957, 114050562090214412, 123131392105477863, 132316878543668989, 141615478488828472, 151035649024996992, 160585847236215226, 170274530206523857, 180110155019963563]
  | 7,2 => [0, 0, 0, 110707568104725432, 110707568104725446, 110707568104725464, 110707568104725486, 110707568104725511, 123787931603989937, 136930666105978638, 150144228694732294, 163437076454291587, 176817666468697195, 190294455821989800, 203875901598210081]
  | 8,2 => [0, 0, 0, 176274052417450246, 176274052417450259, 176274052417450277, 176274052417450299]
  | _,_ => []
def retainedTariff (b j t : ℕ) : ℕ := (retainedTariffs j t).getD b 0
def singleTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 2158343791299739, 2158343791299739, 2158343791299739, 2502144872790737, 2853169289624949, 3213531186026336, 3585344706218855, 3970723994426466, 4371783194873127, 4790636451782796, 5229397909379435, 5690181711886999, 6175102003529451, 6686272928530745, 7225808631114844, 7795823255505704, 8398430945927286, 9035745846603546, 9709882101758445, 10422953855615941, 11177075252399994, 11974360436334560, 12816923551643602, 13706878742551074, 14646340153280940, 15637421928057153, 16682238211103677]
  | 4,1 => [0, 0, 5084581920206611, 5084581920206611, 5084581920206611, 5939082899406459, 6802921358173483, 7678211440731636, 8567067291304884, 9471603054117181, 10393932873392487, 11336170893354761, 12300431258227963, 13288828112236049, 14303475599602981, 15346487864552715, 16419979051309211, 17526063304096428, 18666854767138326, 19844467584658860, 21061015900881993, 22318613860031681, 23619375606331885, 24965415284006560, 26358847037279670, 27801785010375170]
  | 5,1 => [0, 0, 10839217099761532, 10839217099761532, 10839217099761532, 10839217099761532, 12430409652199293, 14033053828428185, 15649263772672170, 17281153629155205, 18930837542101250, 20600429655734262, 22292044114278202, 24007795061957024, 25749796642994694, 27520163001615166, 29321008282042400, 31154446628500355, 33022592185212991, 34927559096404263, 36871461506298134, 38856413559118558, 40884529399089500]
  | 6,1 => [0, 0, 18805928703070084, 18805928703070084, 18805928703070084, 18805928703070084, 18805928703070084, 21080209774346668, 23368056613638343, 25671583365169068, 27992904173162802, 30334133181843506, 32697384535435135, 35084772378161650, 37498410854247010, 39940414107915173, 42412896283390097, 44917971524895743, 47457753976656067, 50034357782895031]
  | 7,1 => [0, 0, 0, 29118013708689678, 29118013708689678, 29118013708689678, 29118013708689678, 29118013708689678, 32077497443029043, 35052661089607461, 38045618792648885, 41058484696377279, 44093372945016599, 47152397682790804, 50237673053923854]
  | 8,1 => [0, 0, 0, 41777586260844276, 41777586260844276, 41777586260844276, 41777586260844276]
  | 6,2 => [0, 0, 61289770173836758, 61289770173836768, 61289770173836782, 61289770173836799, 61289770173836821, 69920260416388496, 78604664577623767, 87351439741583314, 96169042992307818, 105065931413837957, 114050562090214412, 123131392105477863, 132316878543668989, 141615478488828472, 151035649024996992, 160585847236215226, 170274530206523857, 180110155019963563]
  | 7,2 => [0, 0, 0, 110707568104725432, 110707568104725446, 110707568104725464, 110707568104725486, 110707568104725511, 123787931603989937, 136930666105978638, 150144228694732294, 163437076454291587, 176817666468697195, 190294455821989800, 203875901598210081]
  | 8,2 => [0, 0, 0, 176274052417450246, 176274052417450259, 176274052417450277, 176274052417450299]
  | _,_ => []
def singleTariff (b j t : ℕ) : ℕ := (singleTariffs j t).getD b 0
private theorem cell_1_3_1 : fatPrice ⟨1,3,1⟩ ≤ singleTariff 1 3 1 := by decide +kernel
private theorem cell_2_3_1 : fatPrice ⟨2,3,1⟩ ≤ singleTariff 2 3 1 := by decide +kernel
private theorem cell_3_3_1 : fatPrice ⟨3,3,1⟩ ≤ singleTariff 3 3 1 := by decide +kernel
private theorem cell_4_3_1 : fatPrice ⟨4,3,1⟩ ≤ singleTariff 4 3 1 := by decide +kernel
private theorem cell_5_3_1 : fatPrice ⟨5,3,1⟩ ≤ singleTariff 5 3 1 := by decide +kernel
private theorem cell_6_3_1 : fatPrice ⟨6,3,1⟩ ≤ singleTariff 6 3 1 := by decide +kernel
private theorem cell_7_3_1 : fatPrice ⟨7,3,1⟩ ≤ singleTariff 7 3 1 := by decide +kernel
private theorem cell_8_3_1 : fatPrice ⟨8,3,1⟩ ≤ singleTariff 8 3 1 := by decide +kernel
private theorem cell_9_3_1 : fatPrice ⟨9,3,1⟩ ≤ singleTariff 9 3 1 := by decide +kernel
private theorem cell_10_3_1 : fatPrice ⟨10,3,1⟩ ≤ singleTariff 10 3 1 := by decide +kernel
private theorem cell_11_3_1 : fatPrice ⟨11,3,1⟩ ≤ singleTariff 11 3 1 := by decide +kernel
private theorem cell_12_3_1 : fatPrice ⟨12,3,1⟩ ≤ singleTariff 12 3 1 := by decide +kernel
private theorem cell_13_3_1 : fatPrice ⟨13,3,1⟩ ≤ singleTariff 13 3 1 := by decide +kernel
private theorem cell_14_3_1 : fatPrice ⟨14,3,1⟩ ≤ singleTariff 14 3 1 := by decide +kernel
private theorem cell_15_3_1 : fatPrice ⟨15,3,1⟩ ≤ singleTariff 15 3 1 := by decide +kernel
private theorem cell_16_3_1 : fatPrice ⟨16,3,1⟩ ≤ singleTariff 16 3 1 := by decide +kernel
private theorem cell_17_3_1 : fatPrice ⟨17,3,1⟩ ≤ singleTariff 17 3 1 := by decide +kernel
private theorem cell_18_3_1 : fatPrice ⟨18,3,1⟩ ≤ singleTariff 18 3 1 := by decide +kernel
private theorem cell_19_3_1 : fatPrice ⟨19,3,1⟩ ≤ singleTariff 19 3 1 := by decide +kernel
private theorem cell_20_3_1 : fatPrice ⟨20,3,1⟩ ≤ singleTariff 20 3 1 := by decide +kernel
private theorem cell_21_3_1 : fatPrice ⟨21,3,1⟩ ≤ singleTariff 21 3 1 := by decide +kernel
private theorem cell_22_3_1 : fatPrice ⟨22,3,1⟩ ≤ singleTariff 22 3 1 := by decide +kernel
private theorem cell_23_3_1 : fatPrice ⟨23,3,1⟩ ≤ singleTariff 23 3 1 := by decide +kernel
private theorem cell_24_3_1 : fatPrice ⟨24,3,1⟩ ≤ singleTariff 24 3 1 := by decide +kernel
private theorem cell_25_3_1 : fatPrice ⟨25,3,1⟩ ≤ singleTariff 25 3 1 := by decide +kernel
private theorem cell_26_3_1 : fatPrice ⟨26,3,1⟩ ≤ singleTariff 26 3 1 := by decide +kernel
private theorem cell_27_3_1 : fatPrice ⟨27,3,1⟩ ≤ singleTariff 27 3 1 := by decide +kernel
private theorem cell_2_4_1 : fatPrice ⟨2,4,1⟩ ≤ singleTariff 2 4 1 := by decide +kernel
private theorem cell_3_4_1 : fatPrice ⟨3,4,1⟩ ≤ singleTariff 3 4 1 := by decide +kernel
private theorem cell_4_4_1 : fatPrice ⟨4,4,1⟩ ≤ singleTariff 4 4 1 := by decide +kernel
private theorem cell_5_4_1 : fatPrice ⟨5,4,1⟩ ≤ singleTariff 5 4 1 := by decide +kernel
private theorem cell_6_4_1 : fatPrice ⟨6,4,1⟩ ≤ singleTariff 6 4 1 := by decide +kernel
private theorem cell_7_4_1 : fatPrice ⟨7,4,1⟩ ≤ singleTariff 7 4 1 := by decide +kernel
private theorem cell_8_4_1 : fatPrice ⟨8,4,1⟩ ≤ singleTariff 8 4 1 := by decide +kernel
private theorem cell_9_4_1 : fatPrice ⟨9,4,1⟩ ≤ singleTariff 9 4 1 := by decide +kernel
private theorem cell_10_4_1 : fatPrice ⟨10,4,1⟩ ≤ singleTariff 10 4 1 := by decide +kernel
private theorem cell_11_4_1 : fatPrice ⟨11,4,1⟩ ≤ singleTariff 11 4 1 := by decide +kernel
private theorem cell_12_4_1 : fatPrice ⟨12,4,1⟩ ≤ singleTariff 12 4 1 := by decide +kernel
private theorem cell_13_4_1 : fatPrice ⟨13,4,1⟩ ≤ singleTariff 13 4 1 := by decide +kernel
private theorem cell_14_4_1 : fatPrice ⟨14,4,1⟩ ≤ singleTariff 14 4 1 := by decide +kernel
private theorem cell_15_4_1 : fatPrice ⟨15,4,1⟩ ≤ singleTariff 15 4 1 := by decide +kernel
private theorem cell_16_4_1 : fatPrice ⟨16,4,1⟩ ≤ singleTariff 16 4 1 := by decide +kernel
private theorem cell_17_4_1 : fatPrice ⟨17,4,1⟩ ≤ singleTariff 17 4 1 := by decide +kernel
private theorem cell_18_4_1 : fatPrice ⟨18,4,1⟩ ≤ singleTariff 18 4 1 := by decide +kernel
private theorem cell_19_4_1 : fatPrice ⟨19,4,1⟩ ≤ singleTariff 19 4 1 := by decide +kernel
private theorem cell_20_4_1 : fatPrice ⟨20,4,1⟩ ≤ singleTariff 20 4 1 := by decide +kernel
private theorem cell_21_4_1 : fatPrice ⟨21,4,1⟩ ≤ singleTariff 21 4 1 := by decide +kernel
private theorem cell_22_4_1 : fatPrice ⟨22,4,1⟩ ≤ singleTariff 22 4 1 := by decide +kernel
private theorem cell_23_4_1 : fatPrice ⟨23,4,1⟩ ≤ singleTariff 23 4 1 := by decide +kernel
private theorem cell_24_4_1 : fatPrice ⟨24,4,1⟩ ≤ singleTariff 24 4 1 := by decide +kernel
private theorem cell_25_4_1 : fatPrice ⟨25,4,1⟩ ≤ singleTariff 25 4 1 := by decide +kernel
private theorem cell_2_5_1 : fatPrice ⟨2,5,1⟩ ≤ singleTariff 2 5 1 := by decide +kernel
private theorem cell_3_5_1 : fatPrice ⟨3,5,1⟩ ≤ singleTariff 3 5 1 := by decide +kernel
private theorem cell_4_5_1 : fatPrice ⟨4,5,1⟩ ≤ singleTariff 4 5 1 := by decide +kernel
private theorem cell_5_5_1 : fatPrice ⟨5,5,1⟩ ≤ singleTariff 5 5 1 := by decide +kernel
private theorem cell_6_5_1 : fatPrice ⟨6,5,1⟩ ≤ singleTariff 6 5 1 := by decide +kernel
private theorem cell_7_5_1 : fatPrice ⟨7,5,1⟩ ≤ singleTariff 7 5 1 := by decide +kernel
private theorem cell_8_5_1 : fatPrice ⟨8,5,1⟩ ≤ singleTariff 8 5 1 := by decide +kernel
private theorem cell_9_5_1 : fatPrice ⟨9,5,1⟩ ≤ singleTariff 9 5 1 := by decide +kernel
private theorem cell_10_5_1 : fatPrice ⟨10,5,1⟩ ≤ singleTariff 10 5 1 := by decide +kernel
private theorem cell_11_5_1 : fatPrice ⟨11,5,1⟩ ≤ singleTariff 11 5 1 := by decide +kernel
private theorem cell_12_5_1 : fatPrice ⟨12,5,1⟩ ≤ singleTariff 12 5 1 := by decide +kernel
private theorem cell_13_5_1 : fatPrice ⟨13,5,1⟩ ≤ singleTariff 13 5 1 := by decide +kernel
private theorem cell_14_5_1 : fatPrice ⟨14,5,1⟩ ≤ singleTariff 14 5 1 := by decide +kernel
private theorem cell_15_5_1 : fatPrice ⟨15,5,1⟩ ≤ singleTariff 15 5 1 := by decide +kernel
private theorem cell_16_5_1 : fatPrice ⟨16,5,1⟩ ≤ singleTariff 16 5 1 := by decide +kernel
private theorem cell_17_5_1 : fatPrice ⟨17,5,1⟩ ≤ singleTariff 17 5 1 := by decide +kernel
private theorem cell_18_5_1 : fatPrice ⟨18,5,1⟩ ≤ singleTariff 18 5 1 := by decide +kernel
private theorem cell_19_5_1 : fatPrice ⟨19,5,1⟩ ≤ singleTariff 19 5 1 := by decide +kernel
private theorem cell_20_5_1 : fatPrice ⟨20,5,1⟩ ≤ singleTariff 20 5 1 := by decide +kernel
private theorem cell_21_5_1 : fatPrice ⟨21,5,1⟩ ≤ singleTariff 21 5 1 := by decide +kernel
private theorem cell_22_5_1 : fatPrice ⟨22,5,1⟩ ≤ singleTariff 22 5 1 := by decide +kernel
private theorem cell_2_6_1 : fatPrice ⟨2,6,1⟩ ≤ singleTariff 2 6 1 := by decide +kernel
private theorem cell_3_6_1 : fatPrice ⟨3,6,1⟩ ≤ singleTariff 3 6 1 := by decide +kernel
private theorem cell_4_6_1 : fatPrice ⟨4,6,1⟩ ≤ singleTariff 4 6 1 := by decide +kernel
private theorem cell_5_6_1 : fatPrice ⟨5,6,1⟩ ≤ singleTariff 5 6 1 := by decide +kernel
private theorem cell_6_6_1 : fatPrice ⟨6,6,1⟩ ≤ singleTariff 6 6 1 := by decide +kernel
private theorem cell_7_6_1 : fatPrice ⟨7,6,1⟩ ≤ singleTariff 7 6 1 := by decide +kernel
private theorem cell_8_6_1 : fatPrice ⟨8,6,1⟩ ≤ singleTariff 8 6 1 := by decide +kernel
private theorem cell_9_6_1 : fatPrice ⟨9,6,1⟩ ≤ singleTariff 9 6 1 := by decide +kernel
private theorem cell_10_6_1 : fatPrice ⟨10,6,1⟩ ≤ singleTariff 10 6 1 := by decide +kernel
private theorem cell_11_6_1 : fatPrice ⟨11,6,1⟩ ≤ singleTariff 11 6 1 := by decide +kernel
private theorem cell_12_6_1 : fatPrice ⟨12,6,1⟩ ≤ singleTariff 12 6 1 := by decide +kernel
private theorem cell_13_6_1 : fatPrice ⟨13,6,1⟩ ≤ singleTariff 13 6 1 := by decide +kernel
private theorem cell_14_6_1 : fatPrice ⟨14,6,1⟩ ≤ singleTariff 14 6 1 := by decide +kernel
private theorem cell_15_6_1 : fatPrice ⟨15,6,1⟩ ≤ singleTariff 15 6 1 := by decide +kernel
private theorem cell_16_6_1 : fatPrice ⟨16,6,1⟩ ≤ singleTariff 16 6 1 := by decide +kernel
private theorem cell_17_6_1 : fatPrice ⟨17,6,1⟩ ≤ singleTariff 17 6 1 := by decide +kernel
private theorem cell_18_6_1 : fatPrice ⟨18,6,1⟩ ≤ singleTariff 18 6 1 := by decide +kernel
private theorem cell_19_6_1 : fatPrice ⟨19,6,1⟩ ≤ singleTariff 19 6 1 := by decide +kernel
private theorem cell_3_7_1 : fatPrice ⟨3,7,1⟩ ≤ singleTariff 3 7 1 := by decide +kernel
private theorem cell_4_7_1 : fatPrice ⟨4,7,1⟩ ≤ singleTariff 4 7 1 := by decide +kernel
private theorem cell_5_7_1 : fatPrice ⟨5,7,1⟩ ≤ singleTariff 5 7 1 := by decide +kernel
private theorem cell_6_7_1 : fatPrice ⟨6,7,1⟩ ≤ singleTariff 6 7 1 := by decide +kernel
private theorem cell_7_7_1 : fatPrice ⟨7,7,1⟩ ≤ singleTariff 7 7 1 := by decide +kernel
private theorem cell_8_7_1 : fatPrice ⟨8,7,1⟩ ≤ singleTariff 8 7 1 := by decide +kernel
private theorem cell_9_7_1 : fatPrice ⟨9,7,1⟩ ≤ singleTariff 9 7 1 := by decide +kernel
private theorem cell_10_7_1 : fatPrice ⟨10,7,1⟩ ≤ singleTariff 10 7 1 := by decide +kernel
private theorem cell_11_7_1 : fatPrice ⟨11,7,1⟩ ≤ singleTariff 11 7 1 := by decide +kernel
private theorem cell_12_7_1 : fatPrice ⟨12,7,1⟩ ≤ singleTariff 12 7 1 := by decide +kernel
private theorem cell_13_7_1 : fatPrice ⟨13,7,1⟩ ≤ singleTariff 13 7 1 := by decide +kernel
private theorem cell_14_7_1 : fatPrice ⟨14,7,1⟩ ≤ singleTariff 14 7 1 := by decide +kernel
private theorem cell_3_8_1 : fatPrice ⟨3,8,1⟩ ≤ singleTariff 3 8 1 := by decide +kernel
private theorem cell_4_8_1 : fatPrice ⟨4,8,1⟩ ≤ singleTariff 4 8 1 := by decide +kernel
private theorem cell_5_8_1 : fatPrice ⟨5,8,1⟩ ≤ singleTariff 5 8 1 := by decide +kernel
private theorem cell_6_8_1 : fatPrice ⟨6,8,1⟩ ≤ singleTariff 6 8 1 := by decide +kernel
private theorem cell_2_6_2 : fatPrice ⟨2,6,2⟩ ≤ singleTariff 2 6 2 := by decide +kernel
private theorem cell_3_6_2 : fatPrice ⟨3,6,2⟩ ≤ singleTariff 3 6 2 := by decide +kernel
private theorem cell_4_6_2 : fatPrice ⟨4,6,2⟩ ≤ singleTariff 4 6 2 := by decide +kernel
private theorem cell_5_6_2 : fatPrice ⟨5,6,2⟩ ≤ singleTariff 5 6 2 := by decide +kernel
private theorem cell_6_6_2 : fatPrice ⟨6,6,2⟩ ≤ singleTariff 6 6 2 := by decide +kernel
private theorem cell_7_6_2 : fatPrice ⟨7,6,2⟩ ≤ singleTariff 7 6 2 := by decide +kernel
private theorem cell_8_6_2 : fatPrice ⟨8,6,2⟩ ≤ singleTariff 8 6 2 := by decide +kernel
private theorem cell_9_6_2 : fatPrice ⟨9,6,2⟩ ≤ singleTariff 9 6 2 := by decide +kernel
private theorem cell_10_6_2 : fatPrice ⟨10,6,2⟩ ≤ singleTariff 10 6 2 := by decide +kernel
private theorem cell_11_6_2 : fatPrice ⟨11,6,2⟩ ≤ singleTariff 11 6 2 := by decide +kernel
private theorem cell_12_6_2 : fatPrice ⟨12,6,2⟩ ≤ singleTariff 12 6 2 := by decide +kernel
private theorem cell_13_6_2 : fatPrice ⟨13,6,2⟩ ≤ singleTariff 13 6 2 := by decide +kernel
private theorem cell_14_6_2 : fatPrice ⟨14,6,2⟩ ≤ singleTariff 14 6 2 := by decide +kernel
private theorem cell_15_6_2 : fatPrice ⟨15,6,2⟩ ≤ singleTariff 15 6 2 := by decide +kernel
private theorem cell_16_6_2 : fatPrice ⟨16,6,2⟩ ≤ singleTariff 16 6 2 := by decide +kernel
private theorem cell_17_6_2 : fatPrice ⟨17,6,2⟩ ≤ singleTariff 17 6 2 := by decide +kernel
private theorem cell_18_6_2 : fatPrice ⟨18,6,2⟩ ≤ singleTariff 18 6 2 := by decide +kernel
private theorem cell_19_6_2 : fatPrice ⟨19,6,2⟩ ≤ singleTariff 19 6 2 := by decide +kernel
private theorem cell_3_7_2 : fatPrice ⟨3,7,2⟩ ≤ singleTariff 3 7 2 := by decide +kernel
private theorem cell_4_7_2 : fatPrice ⟨4,7,2⟩ ≤ singleTariff 4 7 2 := by decide +kernel
private theorem cell_5_7_2 : fatPrice ⟨5,7,2⟩ ≤ singleTariff 5 7 2 := by decide +kernel
private theorem cell_6_7_2 : fatPrice ⟨6,7,2⟩ ≤ singleTariff 6 7 2 := by decide +kernel
private theorem cell_7_7_2 : fatPrice ⟨7,7,2⟩ ≤ singleTariff 7 7 2 := by decide +kernel
private theorem cell_8_7_2 : fatPrice ⟨8,7,2⟩ ≤ singleTariff 8 7 2 := by decide +kernel
private theorem cell_9_7_2 : fatPrice ⟨9,7,2⟩ ≤ singleTariff 9 7 2 := by decide +kernel
private theorem cell_10_7_2 : fatPrice ⟨10,7,2⟩ ≤ singleTariff 10 7 2 := by decide +kernel
private theorem cell_11_7_2 : fatPrice ⟨11,7,2⟩ ≤ singleTariff 11 7 2 := by decide +kernel
private theorem cell_12_7_2 : fatPrice ⟨12,7,2⟩ ≤ singleTariff 12 7 2 := by decide +kernel
private theorem cell_13_7_2 : fatPrice ⟨13,7,2⟩ ≤ singleTariff 13 7 2 := by decide +kernel
private theorem cell_14_7_2 : fatPrice ⟨14,7,2⟩ ≤ singleTariff 14 7 2 := by decide +kernel
private theorem cell_3_8_2 : fatPrice ⟨3,8,2⟩ ≤ singleTariff 3 8 2 := by decide +kernel
private theorem cell_4_8_2 : fatPrice ⟨4,8,2⟩ ≤ singleTariff 4 8 2 := by decide +kernel
private theorem cell_5_8_2 : fatPrice ⟨5,8,2⟩ ≤ singleTariff 5 8 2 := by decide +kernel
private theorem cell_6_8_2 : fatPrice ⟨6,8,2⟩ ≤ singleTariff 6 8 2 := by decide +kernel
private theorem price_3_1 (b : ℕ) (lo : 1≤b) (hi : b≤27) :
    fatPrice ⟨b,3,1⟩ ≤ singleTariff b 3 1 := by
  interval_cases b
  · exact cell_1_3_1
  · exact cell_2_3_1
  · exact cell_3_3_1
  · exact cell_4_3_1
  · exact cell_5_3_1
  · exact cell_6_3_1
  · exact cell_7_3_1
  · exact cell_8_3_1
  · exact cell_9_3_1
  · exact cell_10_3_1
  · exact cell_11_3_1
  · exact cell_12_3_1
  · exact cell_13_3_1
  · exact cell_14_3_1
  · exact cell_15_3_1
  · exact cell_16_3_1
  · exact cell_17_3_1
  · exact cell_18_3_1
  · exact cell_19_3_1
  · exact cell_20_3_1
  · exact cell_21_3_1
  · exact cell_22_3_1
  · exact cell_23_3_1
  · exact cell_24_3_1
  · exact cell_25_3_1
  · exact cell_26_3_1
  · exact cell_27_3_1
private theorem price_4_1 (b : ℕ) (lo : 2≤b) (hi : b≤25) :
    fatPrice ⟨b,4,1⟩ ≤ singleTariff b 4 1 := by
  interval_cases b
  · exact cell_2_4_1
  · exact cell_3_4_1
  · exact cell_4_4_1
  · exact cell_5_4_1
  · exact cell_6_4_1
  · exact cell_7_4_1
  · exact cell_8_4_1
  · exact cell_9_4_1
  · exact cell_10_4_1
  · exact cell_11_4_1
  · exact cell_12_4_1
  · exact cell_13_4_1
  · exact cell_14_4_1
  · exact cell_15_4_1
  · exact cell_16_4_1
  · exact cell_17_4_1
  · exact cell_18_4_1
  · exact cell_19_4_1
  · exact cell_20_4_1
  · exact cell_21_4_1
  · exact cell_22_4_1
  · exact cell_23_4_1
  · exact cell_24_4_1
  · exact cell_25_4_1
private theorem price_5_1 (b : ℕ) (lo : 2≤b) (hi : b≤22) :
    fatPrice ⟨b,5,1⟩ ≤ singleTariff b 5 1 := by
  interval_cases b
  · exact cell_2_5_1
  · exact cell_3_5_1
  · exact cell_4_5_1
  · exact cell_5_5_1
  · exact cell_6_5_1
  · exact cell_7_5_1
  · exact cell_8_5_1
  · exact cell_9_5_1
  · exact cell_10_5_1
  · exact cell_11_5_1
  · exact cell_12_5_1
  · exact cell_13_5_1
  · exact cell_14_5_1
  · exact cell_15_5_1
  · exact cell_16_5_1
  · exact cell_17_5_1
  · exact cell_18_5_1
  · exact cell_19_5_1
  · exact cell_20_5_1
  · exact cell_21_5_1
  · exact cell_22_5_1
private theorem price_6_1 (b : ℕ) (lo : 2≤b) (hi : b≤19) :
    fatPrice ⟨b,6,1⟩ ≤ singleTariff b 6 1 := by
  interval_cases b
  · exact cell_2_6_1
  · exact cell_3_6_1
  · exact cell_4_6_1
  · exact cell_5_6_1
  · exact cell_6_6_1
  · exact cell_7_6_1
  · exact cell_8_6_1
  · exact cell_9_6_1
  · exact cell_10_6_1
  · exact cell_11_6_1
  · exact cell_12_6_1
  · exact cell_13_6_1
  · exact cell_14_6_1
  · exact cell_15_6_1
  · exact cell_16_6_1
  · exact cell_17_6_1
  · exact cell_18_6_1
  · exact cell_19_6_1
private theorem price_7_1 (b : ℕ) (lo : 3≤b) (hi : b≤14) :
    fatPrice ⟨b,7,1⟩ ≤ singleTariff b 7 1 := by
  interval_cases b
  · exact cell_3_7_1
  · exact cell_4_7_1
  · exact cell_5_7_1
  · exact cell_6_7_1
  · exact cell_7_7_1
  · exact cell_8_7_1
  · exact cell_9_7_1
  · exact cell_10_7_1
  · exact cell_11_7_1
  · exact cell_12_7_1
  · exact cell_13_7_1
  · exact cell_14_7_1
private theorem price_8_1 (b : ℕ) (lo : 3≤b) (hi : b≤6) :
    fatPrice ⟨b,8,1⟩ ≤ singleTariff b 8 1 := by
  interval_cases b
  · exact cell_3_8_1
  · exact cell_4_8_1
  · exact cell_5_8_1
  · exact cell_6_8_1
private theorem price_6_2 (b : ℕ) (lo : 2≤b) (hi : b≤19) :
    fatPrice ⟨b,6,2⟩ ≤ singleTariff b 6 2 := by
  interval_cases b
  · exact cell_2_6_2
  · exact cell_3_6_2
  · exact cell_4_6_2
  · exact cell_5_6_2
  · exact cell_6_6_2
  · exact cell_7_6_2
  · exact cell_8_6_2
  · exact cell_9_6_2
  · exact cell_10_6_2
  · exact cell_11_6_2
  · exact cell_12_6_2
  · exact cell_13_6_2
  · exact cell_14_6_2
  · exact cell_15_6_2
  · exact cell_16_6_2
  · exact cell_17_6_2
  · exact cell_18_6_2
  · exact cell_19_6_2
private theorem price_7_2 (b : ℕ) (lo : 3≤b) (hi : b≤14) :
    fatPrice ⟨b,7,2⟩ ≤ singleTariff b 7 2 := by
  interval_cases b
  · exact cell_3_7_2
  · exact cell_4_7_2
  · exact cell_5_7_2
  · exact cell_6_7_2
  · exact cell_7_7_2
  · exact cell_8_7_2
  · exact cell_9_7_2
  · exact cell_10_7_2
  · exact cell_11_7_2
  · exact cell_12_7_2
  · exact cell_13_7_2
  · exact cell_14_7_2
private theorem price_8_2 (b : ℕ) (lo : 3≤b) (hi : b≤6) :
    fatPrice ⟨b,8,2⟩ ≤ singleTariff b 8 2 := by
  interval_cases b
  · exact cell_3_8_2
  · exact cell_4_8_2
  · exact cell_5_8_2
  · exact cell_6_8_2
private theorem single_price {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤8) (hv : j≤3*b) (hb : b≤lowDegreeCap j) :
    fatPrice ⟨b,j,t⟩≤singleTariff b j t := by
  have ht2 : t≤2 := by omega
  interval_cases t
  · have jl : 3≤j := by omega
    interval_cases j
    · exact price_3_1 b (by omega) hb
    · exact price_4_1 b (by omega) hb
    · exact price_5_1 b (by omega) hb
    · exact price_6_1 b (by omega) hb
    · exact price_7_1 b (by omega) hb
    · exact price_8_1 b (by omega) hb
  · have jl : 6≤j := by omega
    interval_cases j
    · exact price_6_2 b (by omega) hb
    · exact price_7_2 b (by omega) hb
    · exact price_8_2 b (by omega) hb
private def splitPrices (b j : ℕ) : List ℕ :=
  (List.range (b+1)).flatMap (fun c=>(List.range (j+1)).map (fun k=>
    if 3≤k ∧ k≤3*c ∧ 3≤j-k ∧ j-k≤3*(b-c) then
      singleTariff c k 1+singleTariff (b-c) (j-k) 1 else 0))
private def widthCharge (b j t : ℕ) : ℕ :=
  if t=0 then 0 else
    max (singleTariff b j t) (if t=2 then (splitPrices b j).foldr max 0 else 0)
private theorem le_fold_max {v : ℕ} {L : List ℕ} (mem : v∈L) : v≤L.foldr max 0 := by
  induction L with
  | nil => simp at mem
  | cons a tail ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | m
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih m).trans (le_max_right _ _)
private theorem width_single (b j t : ℕ) (hp : 0<t) : singleTariff b j t≤widthCharge b j t := by
  unfold widthCharge
  rw [ite_eq_right (Nat.ne_of_gt hp)]
  exact le_max_left _ _
private theorem width_pair (b c j k : ℕ) (hj : 3≤j) (hk : 3≤k) (hb : j≤3*b) (hc : k≤3*c) :
    singleTariff b j 1+singleTariff c k 1≤widthCharge (b+c) (j+k) 2 := by
  unfold widthCharge
  rw [ite_eq_right (by decide : ¬(2 : ℕ)=0), ite_eq_left rfl]
  apply le_trans _ (le_max_right _ _)
  apply le_fold_max
  unfold splitPrices
  refine List.mem_flatMap.mpr ⟨b,List.mem_range.mpr (by omega),?_⟩
  refine List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),?_⟩
  rw [show b+c-b=c by omega,show j+k-j=k by omega]
  rw [ite_eq_left ⟨hj,hb,hk,hc⟩]
private theorem checked_row (j : Fin 9) (t : Fin 3) :
    (List.range (lowDegreeCap j.val+1)).all (fun b=>decide
      (1≤t.val → 3*t.val≤j.val → j.val≤3*b → widthCharge b j.val t.val≤retainedTariff b j.val t.val)) = true := by
  fin_cases j <;> fin_cases t <;> decide +kernel
private theorem width_checked {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤8) (hv : j≤3*b) (hb : b≤lowDegreeCap j) :
    widthCharge b j t≤retainedTariff b j t := by
  have inj : t<3 := by omega
  have h := List.all_eq_true.mp (checked_row ⟨j,by omega⟩ ⟨t,inj⟩)
    b (List.mem_range.mpr (Nat.lt_succ_of_le hb))
  exact of_decide_eq_true h ht hj hv
theorem retained_family_fee (n : ℕ) (a : Fin n→Shape) (hv : ∀ i,Valid (a i))
    (hj : (∑ i,(a i).j)≤8) (hb : (∑ i,(a i).b) ≤ lowDegreeCap (∑ i,(a i).j)) :
    (∑ i,fatPrice (a i)) ≤ retainedTariff (∑ i,(a i).b) (∑ i,(a i).j) (∑ i,(a i).t) := by
  have hsum : 3*(∑ i,(a i).t)≤∑ i,(a i).j := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun i _=>(hv i).2.1
  have hn' : n≤∑ i,(a i).t := calc
    n = ∑ _ : Fin n,1 := by simp
    _ ≤ ∑ i,(a i).t := sum_le_sum fun i _=>(hv i).1
  have hn : n≤2 := by omega
  interval_cases n
  · simp
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    have one := hv 0
    have eq : a 0=⟨(a 0).b,(a 0).j,(a 0).t⟩ := by cases a 0; rfl
    conv_lhs => rw [eq]
    exact (single_price one.1 one.2.1 hj one.2.2 hb).trans
      ((width_single _ _ _ one.1).trans (width_checked one.1 one.2.1 hj one.2.2 hb))
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0 : (a 0).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have ht1 : (a 1).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have he (i : Fin 2) : a i=⟨(a i).b,(a i).j,(a i).t⟩ := by cases a i; rfl
    have shape0 : a 0=⟨(a 0).b,(a 0).j,1⟩ :=
      (he 0).trans (congrArg (fun t=>(⟨(a 0).b,(a 0).j,t⟩ : Shape)) ht0)
    have shape1 : a 1=⟨(a 1).b,(a 1).j,1⟩ :=
      (he 1).trans (congrArg (fun t=>(⟨(a 1).b,(a 1).j,t⟩ : Shape)) ht1)
    have hj0 : 3≤(a 0).j := by simpa only [ht0,Nat.mul_one] using (hv 0).2.1
    have hj1 : 3≤(a 1).j := by simpa only [ht1,Nat.mul_one] using (hv 1).2.1
    have j0hi : (a 0).j≤5 := by omega
    have j1hi : (a 1).j≤5 := by omega
    have totalB : (a 0).b+(a 1).b≤19 := by
      apply hb.trans
      have eq : (a 0).j+(a 1).j=6 ∨ (a 0).j+(a 1).j=7 ∨ (a 0).j+(a 1).j=8 := by omega
      rcases eq with eq | eq | eq <;> rw [eq] <;> decide
    have below (j : ℕ) (lo : 3≤j) (hi : j≤5) : 19≤lowDegreeCap j := by
      interval_cases j <;> decide
    have p0 := single_price (b:=(a 0).b) (t:=1) (by decide) (by simpa using hj0) (by omega)
      (hv 0).2.2 ((by omega : (a 0).b≤19).trans (below _ hj0 j0hi))
    have p1 := single_price (b:=(a 1).b) (t:=1) (by decide) (by simpa using hj1) (by omega)
      (hv 1).2.2 ((by omega : (a 1).b≤19).trans (below _ hj1 j1hi))
    rw [←shape0] at p0
    rw [←shape1] at p1
    have h := width_pair (a 0).b (a 1).b (a 0).j (a 1).j hj0 hj1 (hv 0).2.2 (hv 1).2.2
    rw [ht0,ht1]
    exact (Nat.add_le_add p0 p1).trans (h.trans (width_checked (by decide) (by omega) hj (by
      have := (hv 0).2.2; have := (hv 1).2.2; omega) hb))
#print axioms retained_family_fee
end LowProfile6966

end
end Merged_R6960Low6966RetainedFees

-- merged module R6960Low6966Width
section Merged_R6960Low6966Width

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace LowProfile6966
open Finset Polynomial
open P3 (K)
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Low6966Retained (Box combined)
open LowProfile6966 (lowDegreeCap)
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty)
open scoped Classical BigOperators

theorem degree_bound {r : Shape} (hr : Valid r) (hx : Box r) :
    r.b ≤ lowDegreeCap r.j := by
  have hjl : 3≤r.j := (Nat.mul_le_mul_left 3 hr.1).trans hr.2.1
  have hju := hx.2.1
  have hj : r.j=3 ∨ r.j=4 ∨ r.j=5 ∨ r.j=6 ∨ r.j=7 ∨ r.j=8 := by omega
  rcases hj with hj | hj | hj | hj | hj | hj <;> rw [hj] <;> simp only [lowDegreeCap]
  · exact hx.1
  · exact hx.2.2.1 (by omega)
  · exact hx.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.2 (by omega)

/-- The retained factors selected by the actual primary bank spend the
finite charge for their exact total width, before the positive-order allocation. -/
theorem Inventory.retained_charge {Γ : Finset K} {s : K→(Polynomial K)} (d : Inventory Γ s) :
    let r := combined (fun i=>shape (d.factor i)) d.zeros
    (∑ i∈d.zeros,fatPrice (shape (d.factor i))) ≤ retainedTariff r.b r.j r.t := by
  let q i := shape (d.factor i)
  let r := combined q d.zeros
  change (∑ i∈d.zeros,fatPrice (q i)) ≤ retainedTariff r.b r.j r.t
  by_cases empty : d.zeros=∅
  · simp [empty,r,combined,P3_6_8.shapeSum_empty,zeroShape,retainedTariff,retainedTariffs]
  · have box := (d.retained.resolve_left empty).1
    have hv : Valid r := (P3_6_8.shapeSum_valid_or_empty d.fits.1 d.zeros).resolve_left empty
    let e := d.zeros.equivFin.symm
    let ar : Fin d.zeros.card→Shape := fun i=>q (e i).val
    have sums (g : Shape→ℕ) : (∑ i,g (ar i)) = ∑ i∈d.zeros,g (q i) := by
      rw [←sum_attach d.zeros (fun i=>g (q i))]
      exact Fintype.sum_equiv e _ _ (fun _=>rfl)
    have hj : (∑ i,(ar i).j)≤8 := by rw [sums]; exact box.2.1
    have hb : (∑ i,(ar i).b)≤lowDegreeCap (∑ i,(ar i).j) := by
      rw [sums,sums]
      exact degree_bound hv box
    have h := retained_family_fee d.zeros.card ar (fun i=>d.fits.1 (e i).val) hj hb
    rw [sums,sums,sums,sums] at h
    exact h

#print axioms Inventory.retained_charge
end LowProfile6966

end
end Merged_R6960Low6966Width

-- merged module R6960Low6966Prices
section Merged_R6960Low6966Prices

set_option Elab.async false
namespace Low6966Prices
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement := LowProfile6966.agreement
abbrev physicalDegree := LowProfile6966.physicalDegree
abbrev errors := LowProfile6966.errors
abbrev incidenceGap := LowProfile6966.incidenceGap
abbrev taylorLength := LowProfile6966.taylorLength
abbrev anchorCutoff := LowProfile6966.anchorCutoff
abbrev primaryCutoff := LowProfile6966.primaryCutoff
def primaryBox : Shape := ⟨4012,1650,550⟩
abbrev layerWidth := LowProfile6966.layerWidth
abbrev layerNeed := LowProfile6966.need
abbrev symbolCount := Final50Price.symbolCount
abbrev TrueWeightLE := @LowProfile6966.TrueWeightLE
abbrev LayerBudget := @LowProfile6966.LayerBudget
abbrev remaining := Final50Price.remaining
abbrev Messages := LowProfile6966.Messages
abbrev SmallFactor := LowProfile6966.SmallFactor
abbrev LowerRow := LowProfile6966.LowerRow
abbrev ProperCut := LowProfile6966.ProperCut
abbrev ActiveFits := Final50Price.ActiveFits
abbrev Fits := @LowProfile6966.Fits
abbrev fullCap := LowProfile6966.fullCap
def lowerWidth (top : ℕ) : ℕ := 142-top
def lowerIndex (top : ℕ) : ℕ := 58-3*top
def lowerTop (top : ℕ) : ℕ := lowerIndex top/2
abbrev fatPrice := LowProfile6966.fatPrice
abbrev FatEquations := Low6966Fat.FatEquations
abbrev Holds := Low6966Fat.Holds
abbrev fatOrder := LowProfile6966.fatOrder
abbrev divisorOrder := LowProfile6966.divisorOrder
abbrev isolatedOrder := LowProfile6966.isolatedOrder
abbrev commonBox := Low6966Fat.commonBox
abbrev resultantBox := Low6966Fat.resultantBox
abbrev linearChart := LowProfile6966.linearChart

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  LowProfile6966.Messages.mono h hΔ

def lowerCap : ℕ → ℕ
  | 0 => 31464968217693405
  | 1 => 28477373315269876
  | 2 => 25626056352459652
  | 3 => 22912565863762966
  | 4 => 20339598887668053
  | 5 => 17908828818584971
  | 6 => 15622833931959120
  | 7 => 13483398957529752
  | 8 => 11492997137025786
  | 9 => 9653510601443595
  | 10 => 7967321697613410
  | 11 => 6436395614225206
  | 12 => 5063038351519769
  | 13 => 3849283402825717
  | 14 => 2797375379595067
  | 15 => 1909400917248679
  | _ => 0

def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPriceOld (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
abbrev BentCap := Shape × ℕ

def bentGraph (p : Shape) : BentCap := (⟨max p.b (p.j + 1), p.j + 1, p.t + 1⟩, 1)

def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))

def bentIntegral (B J T H : ℤ) : ℤ :=
  -576 * H ^ 5 + 160 * T ^ 2 * H ^ 3 - 480 * T ^ 3 * H ^ 2 + 540 * T ^ 4 * H
  + 960 * J * H ^ 4 - 320 * J * T * H ^ 3 + 960 * J * T ^ 2 * H ^ 2 - 1200 * J * T ^ 3 * H
  - 480 * J ^ 2 * H ^ 3 - 480 * J ^ 2 * T * H ^ 2 + 840 * J ^ 2 * T ^ 2 * H
  + 240 * J ^ 3 * H ^ 2 - 240 * J ^ 3 * T * H - 960 * B * H ^ 4 + 640 * B * T * H ^ 3
  - 1440 * B * T ^ 2 * H ^ 2 + 1440 * B * T ^ 3 * H + 640 * B * J * H ^ 3
  + 960 * B * J * T * H ^ 2 - 1440 * B * J * T ^ 2 * H - 480 * B * J ^ 2 * H ^ 2
  + 480 * B * J ^ 2 * T * H

def addBent (p q : BentCap) : BentCap := (p.1.plus q.1, p.2 + q.2)

def ambientMix (caps : List BentCap) : ℕ :=
  (caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) *
      bentIntegral s.1.b s.1.j s.1.t s.2) 0).toNat

def tiltedSurface (p q : Shape) : ℕ :=
  ambientMix [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]

def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]

def activeLoss (cs : List (ℕ × ℕ)) : ℕ :=
  480 * ((cs.map Prod.snd).prod - (cs.map (fun x => x.2 - 2*x.1)).prod)

def tiltedSurfaceActive (p q : Shape) (K : ℕ) : ℕ :=
  tiltedSurface p q - activeLoss (activeClips p K)

def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))

def physicalPriceWith (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceTilted (x : Shape) (l : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurface x.chamber primaryBox)

def physicalPriceActive (x : Shape) (l K : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurfaceActive x.chamber primaryBox K)

def physicalPrice (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOld x l) (physicalPriceTilted x l)
    if activeFitsPrice x K then min base (physicalPriceActive x l K) else base
  else physicalPriceOld x l

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l K
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, Holds E (extend (s γ))) → Γ.card ≤ fatPrice (shape f)

end
end Low6966Prices

end Merged_R6960Low6966Prices

-- merged module R6960Low6966Monotone
section Merged_R6960Low6966Monotone
set_option Elab.async false
section
namespace Low6966Monotone
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩
theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩
theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩
theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩
theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩
theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩
theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩
private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega
theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (chart L x) (chart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [chart] <;> gcongr
private theorem lifted_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (liftedChart L x) (liftedChart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [liftedChart] <;> gcongr
private def graphShape (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
private theorem graph_chamber (x : Shape) : Chamber (graphShape x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem graph_mono {x y : Shape} (h : InBox x y) :
    InBox (graphShape x) (graphShape y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [graphShape] <;> gcongr
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    Low6966Prices.surfaceNumerator32 p q ≤ Low6966Prices.surfaceNumerator32 p' q := by
  let L := Low6966Prices.taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (box_refl q) (chart_mono _ hp) (chart_mono _ hp) hp' hq
      (chart_chamber _ _) hq (chart_chamber _ _) (chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (box_refl q) (lifted_mono _ hp) (lifted_mono _ hp) hp' hq
      (lifted_chamber _ _) hq (lifted_chamber _ _) (lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (graphShape p) (liftedChart M p) ≤ mixed32 p' q (graphShape p') (liftedChart M p') :=
    mixed_mono hp (box_refl q) (graph_mono hp) (lifted_mono _ hp) hp' hq
      (graph_chamber _) hq (graph_chamber _) (lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : Low6966Prices.physicalPriceOld x l ≤ Low6966Prices.physicalPriceOld y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6966Prices.primaryBox
  let L := Low6966Prices.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, le_rfl⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Low6966Prices.errors + 2*Low6966Prices.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (Low6966Prices.errors + 2*Low6966Prices.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6966Prices.errors hc) (Nat.mul_le_mul_left (2*Low6966Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6966Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)
end Low6966Monotone
end

namespace Low6966Monotone
open K1_13 (Shape)
open Low6966Prices (physicalPrice physicalPriceOld physicalPriceTilted physicalPriceActive physicalPriceWith)

theorem physicalPrice_le_old (x : Shape) (l K : ℕ) : physicalPrice x l K ≤ physicalPriceOld x l := by
  unfold physicalPrice
  split
  · split
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact min_le_left _ _
  · exact le_rfl

private theorem with_anti (a : Shape) (s : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPriceWith a u s ≤ physicalPriceWith a l s := by
  unfold physicalPriceWith
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _

theorem physicalPrice_anti (a : Shape) (K : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPrice a u K ≤ physicalPrice a l K := by
  have hold : physicalPriceOld a u ≤ physicalPriceOld a l := by
    unfold physicalPriceOld
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _
  have hnew : physicalPriceTilted a u ≤ physicalPriceTilted a l := with_anti a _ hl h
  have hactive : physicalPriceActive a u K ≤ physicalPriceActive a l K := with_anti a _ hl h
  unfold physicalPrice
  split
  · split
    · exact min_le_min (min_le_min hold hnew) hactive
    · exact min_le_min hold hnew
  · exact hold
end Low6966Monotone

end Merged_R6960Low6966Monotone

end Merged_Low6966Monotone

-- merged module Low6966SurfaceLinearFour
section Merged_Low6966SurfaceLinearFour

-- merged module R6960Low6966SharedPrice
section Merged_R6960Low6966SharedPrice
set_option Elab.async false
set_option autoImplicit false
namespace Low6966SharedPrice
open K1_13 (Shape chart ceilDiv mixed32 shape OnFactor extend)
open Low6966Prices (Messages SmallFactor ActiveFits ProperCut taylorLength primaryBox
  physicalPrice physicalDegree errors incidenceGap tiltedFits tiltedSurface)
open scoped Polynomial
abbrev slope : Shape := ⟨62,28,7⟩
abbrev slopeLoss : ℕ := 19729276669472
inductive Surface where
  | ordinary
  | tilted
  deriving DecidableEq
def surfaceScale : Surface → ℕ
  | .ordinary => 32
  | .tilted => 1920
def surface (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltedSurface f.chamber q
def weights (kind : Surface) (f : Shape) : Shape :=
  let b := surface kind f ⟨1,0,0⟩
  let j := surface kind f ⟨1,1,0⟩ - b
  let t := surface kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
def coord (p : Shape) (i : Fin 3) : ℕ := (![p.b,p.j,p.t] : Fin 3 → ℕ) i
def expression (w q : Shape) (useIndex topIndex : Bool) : ℕ :=
  3*w.b*(if useIndex then q.j else q.b) + 3*w.j*q.j +
    w.t*(if topIndex then q.j else 3*q.t)
def deficit (r a : ℕ) (f : Shape) : Shape :=
  ⟨r*slope.b-a*f.b,r*slope.j-a*f.j,r*slope.t-a*f.t⟩
structure Rate where
  kind : Surface
  pivot : Fin 3
  split : ℕ
  topIndex : Bool
  amount : ℕ
def RateFits (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weights u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))
instance (f : Shape) (u : Rate) : Decidable (RateFits f u) := by
  unfold RateFits
  infer_instance
private theorem expression_line (w f : Shape) (r a : ℕ) (u t : Bool)
    (hb : a*f.b ≤ r*slope.b) (hj : a*f.j ≤ r*slope.j) (ht : a*f.t ≤ r*slope.t) :
    expression w (deficit r a f) u t + a*expression w f u t = r*expression w slope u t := by
  have b := Nat.sub_add_cancel hb
  have j := Nat.sub_add_cancel hj
  have h := Nat.sub_add_cancel ht
  cases u <;> cases t <;> simp only [expression, deficit, Bool.false_eq_true, ↓reduceIte, ite_true]
  all_goals
    rw [mul_add, mul_add]
    simp only [mul_assoc, ← mul_add, ← add_assoc] <;> ring_nf at b j h ⊢
    <;> nlinarith only [congrArg (fun z => w.b*z) b, congrArg (fun z => w.b*z) j,
      congrArg (fun z => w.j*z) j, congrArg (fun z => w.t*z) j, congrArg (fun z => w.t*z) h]
private theorem affine_of_endpoints (p q s x y W r a : ℕ)
    (hp : 0 < p) (hb : a*q ≤ r*p)
    (h₀ : x ≤ W) (h₁ : (q : ℤ)*x-p*y ≤ (q-(s:ℤ)*p)*W) :
    (r : ℤ)*x-a*y ≤ (r-(s:ℤ)*a)*W := by
  have hq : (0 : ℤ) < p := by exact_mod_cast hp
  have hr : (a : ℤ)*q ≤ (r : ℤ)*p := by exact_mod_cast hb
  have hzero : (0 : ℤ) ≤ (W : ℤ)-x := sub_nonneg.mpr (by exact_mod_cast h₀)
  have hA := mul_nonneg (sub_nonneg.mpr hr) hzero
  have hB := mul_nonneg (Int.natCast_nonneg a)
    (show 0 ≤ (p : ℤ)*((y:ℤ)-s*W)-q*((x:ℤ)-W) by linarith)
  apply sub_nonneg.mp
  refine nonneg_of_mul_nonneg_left ?_ hq
  have ident : (p : ℤ)*(((r:ℤ)-s*a)*W-((r:ℤ)*x-a*y)) =
      ((r:ℤ)*p-a*q)*((W:ℤ)-x)+a*(p*((y:ℤ)-s*W)-q*((x:ℤ)-W)) := by ring
  rw [mul_comm, ident]
  exact add_nonneg hA hB
private theorem pivot_pos (i : Fin 3) : 0 < coord slope i := by fin_cases i <;> decide
theorem rate_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (chooseWidth : Bool) :
    expression (weights u.kind f) (deficit r a f) chooseWidth u.topIndex ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let W := 3*surfaceScale u.kind*u.amount
  let w := weights u.kind f
  obtain ⟨_,hs,hpos,hcoord,h₀,h₁⟩ := hu
  have hp : 0 < p := pivot_pos u.pivot
  have hfitPivot : a*q ≤ r*p := hfit u.pivot
  have har : u.split*a ≤ r := by
    by_contra! hbad
    have hleft := Nat.mul_lt_mul_of_pos_right hbad hp
    have hright := Nat.mul_le_mul_left a (Nat.le_of_lt hpos)
    exact (not_lt_of_ge (hfitPivot.trans' (by
      simpa only [mul_left_comm, mul_assoc, mul_comm] using hright : u.split*a*p ≤ a*q))) hleft
  have f0 := expression_line w f q p chooseWidth u.topIndex
    (hcoord 0) (hcoord 1) (hcoord 2)
  have f1 := expression_line w f r a chooseWidth u.topIndex
    (hfit 0) (hfit 1) (hfit 2)
  have hend : ((q : ℤ)*expression w slope chooseWidth u.topIndex -
      p*expression w f chooseWidth u.topIndex) ≤ (q-(u.split:ℤ)*p)*W := by
    have hnum : expression w (deficit q p f) chooseWidth u.topIndex ≤ W*(q-u.split*p) := h₁ chooseWidth
    have hnum' : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤
        (W:ℤ)*(q-(u.split:ℤ)*p) := by
      have hh : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤ (W:ℤ) * ((q-u.split*p : ℕ) : ℤ) := by exact_mod_cast hnum
      change u.split*p < q at hpos
      rwa [Int.ofNat_sub (Nat.le_of_lt hpos)] at hh
    have hline : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) +
        p*expression w f chooseWidth u.topIndex = q*expression w slope chooseWidth u.topIndex := by
      exact_mod_cast f0
    nlinarith
  have haff := affine_of_endpoints p q u.split _ _ W r a hp hfitPivot (h₀ chooseWidth) hend
  have hline : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) +
      a*expression w f chooseWidth u.topIndex = r*expression w slope chooseWidth u.topIndex := by
    exact_mod_cast f1
  have hgoal : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) ≤
      (W:ℤ)*(r-(u.split:ℤ)*a) := by nlinarith
  rw [← Nat.cast_mul, ← Nat.cast_sub har, ← Nat.cast_mul] at hgoal
  exact_mod_cast hgoal
theorem remainder_pos {f : Shape} {u : Rate} (hu : RateFits f u) {r a : ℕ}
    (hr : 0 < r) (hfit : ∀ i, a*coord f i ≤ r*coord slope i) : 0 < r-u.split*a := by
  obtain ⟨_,_,hs,_,_,_⟩ := hu
  have hp := pivot_pos u.pivot
  have hmark := hfit u.pivot
  by_cases ha : a = 0
  · simpa [ha] using hr
  have hm := Nat.mul_lt_mul_of_pos_left hs (Nat.pos_of_ne_zero ha)
  have h : u.split*a * coord slope u.pivot < r * coord slope u.pivot := by
    simpa only [mul_left_comm,mul_assoc,mul_comm] using hm.trans_le hmark
  exact Nat.sub_pos_of_lt (Nat.lt_of_mul_lt_mul_right h)
theorem chamber_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (g : Shape)
    (hg : K1_13.InBox g (deficit r a f)) (hgt : 3*g.t ≤ g.j) :
    3*((weights u.kind f).b*g.chamber.b + (weights u.kind f).j*g.j + (weights u.kind f).t*g.t) ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let w := weights u.kind f
  let d := deficit r a f
  have hgB : g.b ≤ d.b := hg.1
  have hgJ : g.j ≤ d.j := hg.2.1
  have hgT : g.t ≤ d.t := hg.2.2
  have hTop : 3*g.t ≤ (if u.topIndex then d.j else 3*d.t) := by
    split
    · exact hgt.trans hgJ
    · exact Nat.mul_le_mul_left _ hgT
  have component (i : Bool)
      (hB : max g.b g.j ≤ (if i then d.j else d.b)) :
      3*(w.b*g.chamber.b + w.j*g.j + w.t*g.t) ≤ expression w d i u.topIndex := by
    change 3*(w.b*max g.b g.j + w.j*g.j + w.t*g.t) ≤ _
    unfold expression
    calc
      _ = 3*w.b*max g.b g.j + 3*w.j*g.j + w.t*(3*g.t) := by ring
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left _ hB) (Nat.mul_le_mul_left _ hgJ)) (Nat.mul_le_mul_left _ hTop)
  rcases le_total d.b d.j with h | h
  · exact (component true (max_le (hgB.trans h) hgJ)).trans (rate_bound hu r a hfit true)
  · exact (component false (max_le hgB (hgJ.trans h))).trans (rate_bound hu r a hfit false)
def additiveBase (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixed32 p q z h + 2*x.t*mixed32 p p p h
  let pt := mixed32 p q z p + 2*x.t*mixed32 p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)
def nonsharedFee (x : Shape) (l : ℕ) : ℕ :=
  ceilDiv (2*x.b*primaryBox.b^2*(chart (taylorLength+2) x.chamber).b) l
def price (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPrice x l K + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l
def cShared : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → ∀ u, RateFits (shape f) u →
      Γ.card ≤ price (shape f) l K u
end Low6966SharedPrice

end Merged_R6960Low6966SharedPrice

-- merged module R6960Low6966SurfaceLinearFour
section Merged_R6960Low6966SurfaceLinearFour
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Low6966SharedPrice
open K1_13 (Shape chart difference volume32)
open K1_13_8 (Valid)
open Low6966Prices (taylorLength)
open K1_13_8_2 (signedMixed signed_rotate signed_nonneg)
theorem surface_eq_weights_of_signed (kind : Surface) (f : Shape) (b j t : ℤ)
    (hb : 0 ≤ b) (hj : 0 ≤ j) (ht : 0 ≤ t)
    (h : ∀ q : Shape, (surface kind f q : ℤ) = b*q.b + j*q.j + t*q.t) (q : Shape) :
    surface kind f q = (weights kind f).b*q.b + (weights kind f).j*q.j +
      (weights kind f).t*q.t := by
  have hn (u : Shape) : surface kind f u = b.toNat*u.b + j.toNat*u.j + t.toNat*u.t := by
    apply Int.ofNat.inj
    change (surface kind f u : ℤ) = ((b.toNat*u.b + j.toNat*u.j + t.toNat*u.t : ℕ) : ℤ)
    rw [h u]
    push_cast
    rw [Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hj, Int.toNat_of_nonneg ht]
  have hw : weights kind f = ⟨b.toNat,j.toNat,t.toNat⟩ := by
    unfold weights
    simp only [hn ⟨1,0,0⟩, hn ⟨1,1,0⟩, hn ⟨3,3,1⟩, Nat.mul_one, Nat.mul_zero,
      Nat.add_zero, Nat.add_sub_cancel_left]
    congr 1
    omega
  rw [hw]
  exact hn q
private theorem signed_four_linear (q p r s : Shape) :
    signedMixed q p r s = signedMixed ⟨1,0,0⟩ p r s*q.b +
      signedMixed ⟨0,1,0⟩ p r s*q.j + signedMixed ⟨0,0,1⟩ p r s*q.t := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero,
    Nat.cast_one]
  ring
theorem surface_ordinary_eq_weights {f : Shape} (hf : Valid f) (q : Shape) :
    surface .ordinary f q = (weights .ordinary f).b*q.b + (weights .ordinary f).j*q.j +
      (weights .ordinary f).t*q.t := by
  let p := f.chamber
  let r := chart (taylorLength+1) p
  let s := chart (taylorLength+2) p
  have hp : K1_13_8_2.Chamber p := ⟨le_max_right _ _,hf.2.1⟩
  have hr : K1_13_8_2.Chamber r := K1_13_7_1.chart_chamber _ _
  have hs : K1_13_8_2.Chamber s := K1_13_7_1.chart_chamber _ _
  have hnonneg (u : Shape) : 0 ≤ signedMixed u r s p := signed_nonneg u r s p hr hs hp
  refine surface_eq_weights_of_signed .ordinary f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedMixed p u r s).toNat : ℤ) = _
  rw [signed_rotate, Int.toNat_of_nonneg (hnonneg u)]
  exact signed_four_linear u r s p
#print axioms surface_ordinary_eq_weights
end Low6966SharedPrice

end Merged_R6960Low6966SurfaceLinearFour

end Merged_Low6966SurfaceLinearFour

end Merged6967_Low6966SurfaceLinearFour
