import ProximityPrize.SubmissionLower.KoalaTwoSectionPrice
import ProximityPrize.SubmissionLower.HighCore82258Family

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000

namespace H2429ReducibleCharge

open KoalaTwoSectionPrice
open P1_7 (ceilRatio degreeAt quotientOrder singularDegree singularFee)

private theorem ceil_le {n d c : ℕ} (hd : 0 < d) (h : n ≤ d*c) :
    ceilRatio n d ≤ c := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hd).mpr
  change n + (d-1) < (c+1)*d
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm c d]
  omega

private theorem ceil_lift_le {x k : ℕ} (hx : 0 < x) (h : 4858 ≤ x*k) :
    ceilRatio 4858 x ≤ k :=
  ceil_le hx h

theorem lift_le (a b : ℕ) : liftIndex 2429 a b ≤ 4858 := by
  unfold liftIndex
  apply max_le (by decide)
  apply max_le <;> apply ceil_lift_le
  · exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left ..)
  · simpa using Nat.mul_le_mul_right 4858 (le_max_left 1 a)
  · exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left ..)
  · simpa using Nat.mul_le_mul_right 4858 (le_max_left 1 b)

theorem lift_le_of_wide {a b : ℕ} (ha : 30 ≤ a) (hb : 30 ≤ b) :
    liftIndex 2429 a b ≤ 162 := by
  have ha' : 30 ≤ max 1 a := ha.trans (le_max_right ..)
  have hb' : 30 ≤ max 1 b := hb.trans (le_max_right ..)
  unfold liftIndex
  apply max_le (by decide)
  apply max_le <;> apply ceil_lift_le
  · omega
  · exact (by decide : 4858 ≤ 30*162).trans (Nat.mul_le_mul_right _ ha')
  · omega
  · exact (by decide : 4858 ≤ 30*162).trans (Nat.mul_le_mul_right _ hb')

private theorem small_axis {a b : ℕ} (ha : a ≤ 30) :
    max 1 a * max 1 b ≤ 30*(a+b)+1 := by
  by_cases hb : b = 0
  · subst b
    simp only [max_eq_left (show 0 ≤ 1 by decide), Nat.mul_one, Nat.add_zero]
    exact max_le (by omega) (by omega)
  · rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hb)]
    apply (Nat.mul_le_mul_right b (max_le (by decide : 1 ≤ 30) ha)).trans
    omega

private theorem axes_product {a b V : ℕ} (hV : a+b ≤ V) :
    4*(a*b) ≤ V*(a+b) := by
  have hab : 4*(a*b) ≤ (a+b)*(a+b) := by
    exact_mod_cast (show 4*((a:ℤ)*b) ≤ ((a:ℤ)+b)*((a:ℤ)+b) by
      nlinarith [sq_nonneg ((a:ℤ)-b)])
  exact hab.trans (Nat.mul_le_mul_right _ hV)

theorem graph_le {d a b : ℕ} (hd : 2 ≤ d) :
    graphDegree d a b ≤ 2*(9*d-10)*(max 1 a * max 1 b) := by
  let P := max 1 a * max 1 b
  have ha : a * max 1 b ≤ P := Nat.mul_le_mul_right _ (le_max_right ..)
  have hb : b * max 1 a ≤ P := by
    rw [Nat.mul_comm b]
    exact Nat.mul_le_mul_left _ (le_max_right ..)
  have hab : a*b ≤ P := Nat.mul_le_mul (le_max_right ..) (le_max_right ..)
  unfold graphDegree
  dsimp only
  rw [Nat.mul_assoc d (max 1 a) (max 1 b)]
  change 2*(d*P+(a*max 1 b+b*max 1 a)*(2*d-2+(d-1))+a*b*(2*(d-1)-2)) ≤ _
  apply (Nat.mul_le_mul_left 2 (Nat.add_le_add
    (Nat.add_le_add le_rfl (Nat.mul_le_mul_right _ (Nat.add_le_add ha hb)))
    (Nat.mul_le_mul_right _ hab))).trans
  change 2*(d*P+(P+P)*(2*d-2+(d-1))+P*(2*(d-1)-2)) ≤ 2*(9*d-10)*P
  rw [show 9*d-10 = d+2*(2*d-2+(d-1))+(2*(d-1)-2) by omega]
  exact le_of_eq (by ring)

theorem surface_le {d a b : ℕ} (hd : 1 ≤ d) :
    surfaceDegree d a b ≤ 2*(3*d-2)*(max 1 a * max 1 b) := by
  let P := max 1 a * max 1 b
  have ha : a * max 1 b ≤ P := Nat.mul_le_mul_right _ (le_max_right ..)
  have hb : b * max 1 a ≤ P := by
    rw [Nat.mul_comm b]
    exact Nat.mul_le_mul_left _ (le_max_right ..)
  unfold surfaceDegree
  dsimp only
  rw [Nat.mul_assoc d (max 1 a) (max 1 b)]
  change 2*(d*P+a*(d-1)*max 1 b+b*(d-1)*max 1 a) ≤ _
  rw [show a*(d-1)*max 1 b = (a*max 1 b)*(d-1) by ring,
    show b*(d-1)*max 1 a = (b*max 1 a)*(d-1) by ring]
  apply (Nat.mul_le_mul_left 2 (Nat.add_le_add
    (Nat.add_le_add le_rfl (Nat.mul_le_mul_right _ ha))
    (Nat.mul_le_mul_right _ hb))).trans
  change 2*(d*P+P*(d-1)+P*(d-1)) ≤ 2*(3*d-2)*P
  rw [show 3*d-2 = d+(d-1)+(d-1) by omega]
  exact le_of_eq (by ring)

private theorem graph_factor_le {d D : ℕ} (hd : d ≤ D) :
    2*(9*d-10) ≤ 2*(9*D-10) :=
  Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hd) _)

private theorem lengths_le {k K : ℕ} (h : k ≤ K) :
    (128642+1+k)*(128642+2+k) ≤ (128642+1+K)*(128642+2+K) :=
  Nat.mul_le_mul (Nat.add_le_add_left h _) (Nat.add_le_add_left h _)

private theorem second_main {d a b V C : ℕ} (hd : 7 ≤ d) (hd' : d ≤ 16)
    (hsum : a+b ≤ V) (hC : 150000000000000 ≤ C)
    (hwide : 2*(9*d-10)*V*16590856830 ≤ 4*C) :
    graphDegree d a b * (128642+1+liftIndex 2429 a b) *
      (128642+2+liftIndex 2429 a b) ≤ C*(a+b)+5000000000000 := by
  let k := liftIndex 2429 a b
  by_cases hw : 30 ≤ a ∧ 30 ≤ b
  · have hL : (128642+1+k)*(128642+2+k) ≤ 16590856830 :=
      (lengths_le (lift_le_of_wide hw.1 hw.2)).trans (by decide)
    have hG := graph_le (a := a) (b := b) (show 2 ≤ d by omega)
    rw [max_eq_right (show 1 ≤ a by omega),max_eq_right (show 1 ≤ b by omega)] at hG
    have hprod : graphDegree d a b * (128642+1+k) * (128642+2+k) ≤
        2*(9*d-10)*(a*b)*16590856830 := by
      rw [Nat.mul_assoc (graphDegree d a b)]
      exact Nat.mul_le_mul hG hL
    have h4 : 4 * (graphDegree d a b * (128642+1+k) * (128642+2+k)) ≤
        4 * (C*(a+b)) := calc
      _ ≤ 4*(2*(9*d-10)*(a*b)*16590856830) := Nat.mul_le_mul_left _ hprod
      _ = (4*(a*b))*(2*(9*d-10)*16590856830) := by ring
      _ ≤ (V*(a+b))*(2*(9*d-10)*16590856830) :=
        Nat.mul_le_mul_right _ (axes_product hsum)
      _ = (2*(9*d-10)*V*16590856830)*(a+b) := by ring
      _ ≤ (4*C)*(a+b) := Nat.mul_le_mul_right _ hwide
      _ = _ := by ring
    change graphDegree d a b * (128642+1+k) * (128642+2+k) ≤ _
    omega
  · have hsmall : max 1 a * max 1 b ≤ 30*(a+b)+1 := by
      by_cases ha : a ≤ 30
      · exact small_axis ha
      · have hb : b ≤ 30 := by omega
        simpa only [mul_comm b a, Nat.add_comm b a, Nat.mul_comm (max 1 b)] using
          (small_axis (a := b) (b := a) hb)
    have hL : (128642+1+k)*(128642+2+k) ≤ 17822650502 :=
      (lengths_le (lift_le a b)).trans (by decide)
    have hG := (graph_le (a := a) (b := b) (show 2 ≤ d by omega)).trans
      (Nat.mul_le_mul (graph_factor_le hd') hsmall)
    change graphDegree d a b * (128642+1+k) * (128642+2+k) ≤ _
    rw [Nat.mul_assoc (graphDegree d a b)]
    calc
      _ ≤ 2*(9*16-10)*(30*(a+b)+1)*17822650502 := Nat.mul_le_mul hG hL
      _ = 143294110036080*(a+b)+4776470334536 := by ring
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ (hC.trans' (by decide))) (by decide)

private theorem padded_product {a b : ℕ} (hsum : a+b ≤ 386) :
    4*(max 1 a * max 1 b) ≤ 390*(a+b)+4 := by
  by_cases ha : a = 0
  · subst a
    simp only [max_eq_left (show 0 ≤ 1 by decide),one_mul,zero_add]
    have h : max 1 b ≤ b+1 := max_le (by omega) (by omega)
    omega
  · by_cases hb : b = 0
    · subst b
      simp only [max_eq_left (show 0 ≤ 1 by decide),mul_one,add_zero]
      have h : max 1 a ≤ a+1 := max_le (by omega) (by omega)
      omega
    · rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr ha),
        max_eq_right (Nat.one_le_iff_ne_zero.mpr hb)]
      have h := axes_product hsum
      omega

theorem single_le {d a b : ℕ} (hd : 1 ≤ d) (hd' : d ≤ 6) (hsum : a+b ≤ 386) :
    properCharge 179876 2429 2429 d a b ≤
      330000000000000*(a+b)+4000000000000 := by
  rw [properCharge, if_pos (show singleCut d from Or.inl hd')]
  change ceilRatio (properBudget 179876 2429 2429 d a b) 8341929376 ≤ _
  apply ceil_le (by decide)
  let k := liftIndex 2429 a b
  let P := max 1 a * max 1 b
  have hk : k ≤ 4858 := lift_le a b
  have hp : 4*P ≤ 390*(a+b)+4 := padded_product hsum
  have hD : 2*(3*d-2) ≤ 32 :=
    (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 hd') 2)).trans (by decide)
  have hs : surfaceDegree d a b ≤ 32*P :=
    (surface_le hd).trans (Nat.mul_le_mul_right P hD)
  have hK : (2*128642+1+k)*
      (2*262144*(179876-133500)*128642+179876*(262144-133500)*k) ≤
        849412650073959476064 := calc
    _ ≤ (2*128642+1+4858)*
        (2*262144*(179876-133500)*128642+179876*(262144-133500)*4858) :=
      Nat.mul_le_mul (Nat.add_le_add_left hk _)
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _)
    _ ≤ _ := by decide
  change surfaceDegree d a b * (2*128642+1+k) *
    (2*262144*(179876-133500)*128642+179876*(262144-133500)*k) ≤ _
  rw [Nat.mul_assoc (surfaceDegree d a b)]
  calc
    _ ≤ (32*P)*849412650073959476064 := Nat.mul_le_mul hs hK
    _ ≤ (32*P)*(8341929376*101824483497) :=
      Nat.mul_le_mul_left _ (by decide)
    _ = 8341929376*(32*P*101824483497) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

private theorem rest_le {d v : ℕ} (hd : d ≤ 16) :
    ceilRatio (175288956912312*v) 46376 + singularFee d v + d ≤
      100000000000*v+20 := by
  have hf : ceilRatio (175288956912312*v) 46376 ≤ 3780000000*v := by
    apply ceil_le (by decide)
    have h : 175288956912312*v ≤ (46376*3780000000)*v :=
      Nat.mul_le_mul_right _ (by decide)
    exact h.trans_eq (Nat.mul_assoc ..)
  have hs : singularFee d v ≤ 66051899454*v := by
    change 2130706434*((2*d-1)*v) ≤ _
    calc
      _ ≤ 2130706434*((2*16-1)*v) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
          (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hd) 1))
      _ ≤ _ := by rw [← Nat.mul_assoc] <;> exact le_rfl
  omega

private theorem charge_le_aux {d a b V C : ℕ} (hd : 1 ≤ d) (hd' : d ≤ 16)
    (hV : V ≤ 386) (hsum : a+b ≤ V) (hC : 331000000000000 ≤ C)
    (hwide : 2*(9*d-10)*V*16590856830 ≤ 4*(C-1000000000000)) :
    charge 179876 2429 2429 d a b ≤ C*(a+b)+50000000000000 := by
  have hrest := rest_le (v := a+b) hd'
  unfold charge
  change properCharge 179876 2429 2429 d a b +
    ceilRatio (175288956912312*(a+b)) 46376 + singularFee d (a+b) + d ≤ _
  by_cases h : d ≤ 6
  · have hsingle := single_le hd h (hsum.trans hV)
    have hmono : 331000000000000*(a+b) ≤ C*(a+b) := Nat.mul_le_mul_right _ hC
    omega
  · have hmain := second_main (a := a) (b := b) (by omega : 7 ≤ d) hd'
      hsum (C := C-1000000000000) (by omega) hwide
    have ha : a ≤ 2130706434*a := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right a (show 1 ≤ 2130706434 by decide)
    have hb : 2130706433*b ≤ 2130706434*b := Nat.mul_le_mul_right b (by decide)
    have hcomp : a+128+2130706433*(b+128) ≤ 2130706434*(a+b)+272730423552 := calc
      _ = a+2130706433*b+272730423552 := by ring
      _ ≤ 2130706434*a+2130706434*b+272730423552 :=
        Nat.add_le_add_right (Nat.add_le_add ha hb) _
      _ = _ := by ring
    have hC₀ : 1000000000000 ≤ C := (show 1000000000000 ≤ 331000000000000 by decide).trans hC
    have hcancel : (C-1000000000000)*(a+b)+1000000000000*(a+b) = C*(a+b) := by
      rw [← Nat.add_mul,Nat.sub_add_cancel hC₀]
    rw [properCharge,if_neg (show ¬ singleCut d by unfold singleCut; omega)]
    unfold secondCut
    change graphDegree d a b * (128642+1+liftIndex 2429 a b) *
      (128642+2+liftIndex 2429 a b) + (a+128+2130706433*(b+128)) +
      ceilRatio (175288956912312*(a+b)) 46376 + singularFee d (a+b) + d ≤ _
    omega

/-- Any positive proper ordinate part at total grade sixteen. -/
theorem charge_le_grade16 {d a b : ℕ} (hd : 1 ≤ d) (hd' : d < 16) (hsum : a+b ≤ 386) :
    charge 179876 2429 2429 d a b ≤ 416000000000000*(a+b)+50000000000000 := by
  apply charge_le_aux hd (by omega : d ≤ 16) le_rfl hsum (by decide)
  exact (Nat.mul_le_mul_right 16590856830 (Nat.mul_le_mul_right 386
    (graph_factor_le (show d ≤ 15 by omega)))).trans (by decide)

/-- Any positive proper ordinate part at total grade seventeen. -/
theorem charge_le_grade17 {d a b : ℕ} (hd : 1 ≤ d) (hd' : d < 17) (hsum : a+b ≤ 375) :
    charge 179876 2429 2429 d a b ≤ 430000000000000*(a+b)+50000000000000 := by
  apply charge_le_aux hd (by omega : d ≤ 16) (by decide) hsum (by decide)
  exact (Nat.mul_le_mul_right 16590856830 (Nat.mul_le_mul_right 375
    (graph_factor_le (show d ≤ 16 by omega)))).trans (by decide)

/-- The small-ordinate route uses the persistent count, which has a
different numerator. The bound also includes one additional part fee d. -/
theorem small_ordinate_le {d v : ℕ} (hd : d ≤ 2) (hv : v ≤ 386) :
    singularFee d v + HighCore82258.persistentFee 2429 2429 d v + d ≤
      220000000000000*v+50000000000000 := by
  let b := 112413965243552+3127850509008896*v
  let a := 23139968144+3127850509008896*(d-1)
  have hB : b ≤ 1207462710442677408 := by dsimp [b]; omega
  have hA : a ≤ 3127873648977040 := by dsimp [a]; omega
  have hN : d*b^2+2*v*a*b ≤
      2*(1207462710442677408*b)+2*v*3127873648977040*1207462710442677408 := by
    rw [pow_two]
    exact Nat.add_le_add
      (Nat.mul_le_mul hd (Nat.mul_le_mul_right _ hB))
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ hA) hB)
  have hceil :
      ceilRatio (d*b^2+2*v*a*b) 69587785714171749376 ≤
        218000000000000*v+4000000000000 := by
    apply ceil_le (by decide)
    refine hN.trans ?_
    dsimp [b]
    omega
  have hsing : singularFee d v ≤ 6392119302*v := by
    change 2130706434*((2*d-1)*v) ≤ _
    calc
      _ ≤ 2130706434*((2*2-1)*v) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
          (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hd) 1))
      _ ≤ _ := by rw [← Nat.mul_assoc] <;> exact le_rfl
  change singularFee d v + (ceilRatio (d*b^2+2*v*a*b) 69587785714171749376+d) + d ≤ _
  omega

/-- Price for either terminal route, given actual axis caps of one part. -/
def partCharge (d a b : ℕ) : ℕ :=
  if d ≤ 2 then singularFee d (a+b) + HighCore82258.persistentFee 2429 2429 d (a+b) + d
  else charge 179876 2429 2429 d a b

theorem part_le_grade16 {d a b : ℕ} (hd : 1 ≤ d) (hd' : d < 16) (hsum : a+b ≤ 386) :
    partCharge d a b ≤ 416000000000000*(a+b)+50000000000000 := by
  by_cases h : d ≤ 2
  · rw [partCharge,if_pos h]
    have hs := small_ordinate_le h hsum
    omega
  · rw [partCharge,if_neg h]
    exact charge_le_grade16 hd hd' hsum

theorem part_le_grade17 {d a b : ℕ} (hd : 1 ≤ d) (hd' : d < 17) (hsum : a+b ≤ 375) :
    partCharge d a b ≤ 430000000000000*(a+b)+50000000000000 := by
  by_cases h : d ≤ 2
  · rw [partCharge,if_pos h]
    have hs := small_ordinate_le h (hsum.trans (by decide))
    omega
  · rw [partCharge,if_neg h]
    exact charge_le_grade17 hd hd' hsum

theorem split_grade16 {d₁ d₂ a₁ b₁ a₂ b₂ : ℕ}
    (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) (hd : d₁+d₂ = 16)
    (haxes : a₁+b₁+a₂+b₂ ≤ 386) :
    partCharge d₁ a₁ b₁ + partCharge d₂ a₂ b₂ ≤ 160676000000000000 := by
  have hleft := part_le_grade16 h₁ (by omega : d₁ < 16) (by omega : a₁+b₁ ≤ 386)
  have hright := part_le_grade16 h₂ (by omega : d₂ < 16) (by omega : a₂+b₂ ≤ 386)
  omega

theorem split_grade17 {d₁ d₂ a₁ b₁ a₂ b₂ : ℕ}
    (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) (hd : d₁+d₂ = 17)
    (haxes : a₁+b₁+a₂+b₂ ≤ 375) :
    partCharge d₁ a₁ b₁ + partCharge d₂ a₂ b₂ ≤ 161350000000000000 := by
  have hleft := part_le_grade17 h₁ (by omega : d₁ < 17) (by omega : a₁+b₁ ≤ 375)
  have hright := part_le_grade17 h₂ (by omega : d₂ < 17) (by omega : a₂+b₂ ≤ 375)
  omega

#print axioms charge_le_grade16
#print axioms charge_le_grade17
#print axioms small_ordinate_le
end H2429ReducibleCharge
