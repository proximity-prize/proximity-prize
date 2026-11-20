import ProximityPrize.SubmissionLower.PortBase
set_option Elab.async false

section PackSource_P0_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace P0_1
noncomputable section

open Polynomial Finset FrobeniusLocator P0
open K1_2 (JointOn goodSet errorSet mixedChoices padding cutoff deletionSize planePrice)

abbrev prefixCap : ℕ := 181262114320041249

/-- Full ordinary rank and two active generators in the middle prefix. -/
def MiddleGuard (u : Words) : Prop :=
  7 ≤ nullity u ∧ nullity u ≤ frontLimit ∧ firstRank u = L ∧
    ¬ TypeAtMostOne u ∧ ¬ HomogeneousPrincipal u ∧ ¬ ConstantKernel u

def BadOn (D : Finset I) (v w : I → K) (γ : K) : Prop :=
  ∃ S : Finset I, S ⊆ D ∧ agreement ≤ S.card ∧
    ExtendsOn node (fun i => v i + γ * w i) k S ∧
    ¬ (ExtendsOn node v k S ∧ ExtendsOn node w k S)

/-- The mark and failure of joint extension are on the same surviving support. -/
def ShortenedCap (N cap : ℕ) : Prop :=
  ∀ (D : Finset I), D.card ≤ N → ∀ (v w : I → K) (Γ : Finset K),
    (∀ γ ∈ Γ, BadOn D v w γ) → Γ.card ≤ cap

def reducedHeight (r g : ℕ) : ℕ := t + 1 - L - r - g
def childRows (r : ℕ) : ℕ := L - padding r
def childErrors (r g : ℕ) : ℕ := childRows r + reducedHeight r g

def rankReserve (r : ℕ) : ℕ := L + p * (t + 1 - L - r)

def extraReserve (r g : ℕ) : ℕ :=
  let H := reducedHeight r g
  2 * H * ((p * L + H) / (L - H)) + (L / (L - H)) * (p + 1)

def incidenceDenominator (r g : ℕ) : ℕ :=
  (t - g).choose (r - 1 + padding r) * (agreement - 1).choose (padding r)

def incidenceRatio (r g : ℕ) : ℚ :=
  ((blockLength - g).choose (deletionSize r) : ℚ) / incidenceDenominator r g

def nativePlanePrice (r g : ℕ) : ℚ :=
  planePrice (k + childRows r) (childRows r) (reducedHeight r g) (cutoff r)

/-- Exact hit and error sets of the chosen decoder after removing the fixed gcd. -/
structure PaddedFamily (u : Words) (D : Finset I) (Γ : Finset K) (r g : ℕ) where
  decoder : K → K[X]
  slack : K → ℕ
  domain_card : D.card = blockLength - g
  degree : ∀ γ ∈ Γ, (decoder γ).degree < k
  witness : ∀ γ ∈ Γ,
    slack γ ≤ r - 1 ∧
    (goodSet u D γ (decoder γ)).card = agreement + slack γ ∧
    (errorSet u D γ (decoder γ)).card = t - g - slack γ ∧
    ¬ JointOn u (goodSet u D γ (decoder γ))

/-- One family for each shared deletion union, using the given decoder. -/
def childSlopes {u : Words} {D : Finset I} {Γ : Finset K} {r g : ℕ}
    (F : PaddedFamily u D Γ r g) (J : Finset I) : Finset K := by
  classical
  exact Γ.filter fun γ =>
    J ∈ mixedChoices u (r - 1 - F.slack γ + padding r) (F.slack γ + padding r)
      (errorSet u D γ (F.decoder γ)) (goodSet u D γ (F.decoder γ))

end
end P0_1
end PackSource_P0_1Defs

section PackSource_P0_1Arithmetic
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0_1

open P0
open K1_2 (padding cutoff fixedLimit deletionSize padding_le_eight fixedLimit_le
  curveBeta ordinaryCore planeThreshold oldPlanePrice newPlanePrice planePrice planePrice_nonneg)
open private K1_2.new_price_mono from ProximityPrize.SubmissionLower.Fast076

private def newNativePrice (r g : ℕ) : ℚ :=
  let a := childRows r
  let A := k + a
  newPlanePrice (curveBeta A a (cutoff r)) A a (reducedHeight r g)

private theorem new_native_mono (r lo g : ℕ) (hl : lo ≤ g) :
    newNativePrice r g ≤ newNativePrice r lo := by
  have hj := padding_le_eight r
  dsimp only [newNativePrice]
  apply K1_2.new_price_mono
  · unfold curveBeta
    positivity
  · have hL : L = 49145 := by decide
    unfold childRows
    omega
  · unfold reducedHeight
    omega

private def gap (a C : ℕ) : ℕ := a - C + 1

private def newNumerator (A a x C : ℕ) : ℕ :=
  2 * (gap a C + A) * x^2 * (A + a + x)

private def newDenominator (a x C : ℕ) : ℕ :=
  gap a C * (a + x)

private theorem gap_pos (a C : ℕ) : 0 < gap a C := Nat.succ_pos _

private theorem beta_double (A a C : ℕ) :
    2 * curveBeta A a C = ((2 * (gap a C + A) : ℕ) : ℚ) / gap a C := by
  have hd : (0 : ℚ) < gap a C := by exact_mod_cast gap_pos a C
  change 2 * (1 + (A : ℚ) / gap a C) = _
  push_cast only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

private theorem new_price_fraction (A a x C : ℕ) (ha : 0 < a) :
    newPlanePrice (curveBeta A a C) A a x =
      (newNumerator A a x C : ℚ) / newDenominator a x C := by
  have hgap : (0 : ℚ) < gap a C := by exact_mod_cast gap_pos a C
  have hax : (0 : ℚ) < a + x := by exact_mod_cast Nat.add_pos_left ha x
  unfold newPlanePrice
  rw [beta_double]
  unfold newNumerator newDenominator
  push_cast only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- Check the two adjacent integers for the ceiling and compare prices by
clearing positive denominators. All row inputs are natural numbers. -/
private theorem threshold_row (A a C x q : ℕ) (ha : 0 < a) (hq : q < x)
    (hlo : q * (2 * (gap a C + A)) < ordinaryCore A a C * gap a C)
    (hhi : ordinaryCore A a C * gap a C ≤ (q + 1) * (2 * (gap a C + A)))
    (hcompare : (A + a + q)^2 * q * newDenominator a x C ≤
      newNumerator A a x C * (a + q)) :
    let z := planeThreshold A a C
    z < x ∧ oldPlanePrice A a z ≤ newPlanePrice (curveBeta A a C) A a x := by
  have hgap := gap_pos a C
  let n := 2 * (gap a C + A)
  have hn : (0 : ℚ) < n := by
    exact_mod_cast (show 0 < n from Nat.mul_pos (by decide) (Nat.add_pos_left hgap _))
  let y := (ordinaryCore A a C : ℚ) / (2 * curveBeta A a C)
  have hy : y = ((ordinaryCore A a C : ℚ) * gap a C) / n := by
    dsimp only [y]
    rw [beta_double, div_div_eq_mul_div]
  have hyceil : ⌈y⌉ = (q : ℤ) + 1 := by
    apply Int.ceil_eq_iff.mpr
    rw [hy, Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_cancel_right]
    exact ⟨(lt_div_iff₀ hn).mpr (by exact_mod_cast hlo),
      (div_le_iff₀ hn).mpr (by exact_mod_cast hhi)⟩
  have he : planeThreshold A a C = q := by
    change (⌈y⌉ : ℤ).toNat - 1 = q
    rw [hyceil]
    omega
  dsimp only
  rw [he, new_price_fraction _ _ _ _ ha]
  refine ⟨hq, ?_⟩
  unfold oldPlanePrice
  have hqden : (0 : ℚ) < a + q := by exact_mod_cast Nat.add_pos_left ha q
  have hxden : (0 : ℚ) < newDenominator a x C := by
    exact_mod_cast Nat.mul_pos hgap (Nat.add_pos_left ha x)
  apply (div_le_div_iff₀ hqden hxden).mpr
  exact_mod_cast hcompare

private theorem threshold_check (r : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16) :
    let a := childRows r
    let A := k + a
    let q := planeThreshold A a (cutoff r)
    q < reducedHeight r (fixedLimit r) ∧
      oldPlanePrice A a q ≤ newNativePrice r (fixedLimit r) := by
  interval_cases r
  · exact threshold_row _ _ _ _ 5630 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 5629 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 5629 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 5629 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 5629 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 5629 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 5629 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 5629 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 5629 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact threshold_row _ _ _ _ 11405 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem plane_le_new (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) : nativePlanePrice r g ≤ newNativePrice r g := by
  have h := threshold_check r hr hr16
  dsimp only at h
  have hH : reducedHeight r (fixedLimit r) ≤ reducedHeight r g := by
    unfold reducedHeight
    omega
  have hq := h.1.trans_le hH
  dsimp only [nativePlanePrice, planePrice]
  rw [ite_eq_right (not_le.mpr hq)]
  change min _ (max _ (newNativePrice r g)) ≤ newNativePrice r g
  apply min_le_of_right_le
  exact max_le (h.2.trans (new_native_mono r g _ hg)) le_rfl

private theorem reserve_le (r lo g : ℕ) (hr : 7 ≤ r) (hl : lo ≤ g) :
    extraReserve r g ≤ extraReserve r lo := by
  have hH : reducedHeight r g ≤ reducedHeight r lo := by unfold reducedHeight; omega
  have hd : L - reducedHeight r lo ≤ L - reducedHeight r g := by omega
  have hdpos : 0 < L - reducedHeight r lo := by
    have hL : L = 49145 := by decide
    have ht : t = 81927 := by decide
    unfold reducedHeight
    omega
  have hz :
      (p * L + reducedHeight r g) / (L - reducedHeight r g) ≤
      (p * L + reducedHeight r lo) / (L - reducedHeight r lo) :=
    (Nat.div_le_div_right (Nat.add_le_add_left hH _)).trans (Nat.div_le_div_left hd hdpos)
  have hn : L / (L - reducedHeight r g) ≤ L / (L - reducedHeight r lo) :=
    Nat.div_le_div_left hd hdpos
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hH) hz)
    (Nat.mul_le_mul_right (p + 1) hn)

-- The descending factorial evaluates using recursion on the small
-- lower argument of the binomial coefficient.
private def fastChoose (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

private theorem fastChoose_eq (n k : ℕ) : fastChoose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

private def intervalDenominator (r hi : ℕ) : ℕ :=
  fastChoose (t - hi) (r - 1 + padding r) * fastChoose (agreement - 1) (padding r)

private def intervalRatio (r lo hi : ℕ) : ℚ :=
  (fastChoose (blockLength - lo) (deletionSize r) : ℚ) /
    intervalDenominator r hi

private theorem ratio_le_interval (r g lo hi : ℕ) (hr16 : r ≤ 16)
    (hl : lo ≤ g) (hh : g ≤ hi) (hhi : hi ≤ fixedLimit r) :
    incidenceRatio r g ≤ intervalRatio r lo hi := by
  have hj := padding_le_eight r
  have ht : t = 81927 := by decide
  have hA : agreement = 180217 := by decide
  have hhi' := hhi.trans (fixedLimit_le r)
  have htop := Nat.choose_le_choose (deletionSize r) (show blockLength - g ≤ blockLength - lo by omega)
  have hbot : incidenceDenominator r hi ≤ incidenceDenominator r g := by
    unfold incidenceDenominator
    exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (by omega))
  have hpos : 0 < incidenceDenominator r hi := by
    unfold incidenceDenominator
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hpos' : (0 : ℚ) < incidenceDenominator r hi := by exact_mod_cast hpos
  simp only [intervalRatio, intervalDenominator, fastChoose_eq, incidenceRatio]
  change ((blockLength - g).choose (deletionSize r) : ℚ) / incidenceDenominator r g ≤
    ((blockLength - lo).choose (deletionSize r) : ℚ) / incidenceDenominator r hi
  exact div_le_div₀ (by positivity) (by exact_mod_cast htop) hpos' (by exact_mod_cast hbot)

private def intervalBound (r lo hi : ℕ) : ℚ :=
  ((rankReserve r + extraReserve r lo : ℕ) : ℚ) +
    intervalRatio r lo hi * newNativePrice r lo

private theorem native_le_interval (r g lo hi : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hl : lo ≤ g) (hh : g ≤ hi) (hhi : hi ≤ fixedLimit r) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g ≤ intervalBound r lo hi := by
  unfold intervalBound
  apply add_le_add
  · exact_mod_cast Nat.add_le_add_left (reserve_le r lo g hr hl) (rankReserve r)
  · exact mul_le_mul (ratio_le_interval r g lo hi hr16 hl hh hhi)
      ((plane_le_new r g hr hr16 (hh.trans hhi)).trans (new_native_mono r lo g hl))
      (planePrice_nonneg _ _ _ _) (by unfold intervalRatio; positivity)

private theorem fee_fraction_lt (fee n d pn pd cap : ℕ) (hd : 0 < d) (hpd : 0 < pd)
    (hc : fee * (d * pd) + n * pn < (cap + 1) * (d * pd)) :
    (fee : ℚ) + (n : ℚ) / d * ((pn : ℚ) / pd) < (cap : ℚ) + 1 := by
  have hpos : (0 : ℚ) < (d : ℚ) * pd := by exact_mod_cast Nat.mul_pos hd hpd
  rw [div_mul_div_comm]
  apply (mul_lt_mul_iff_of_pos_right hpos).mp
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  exact_mod_cast hc

private theorem interval_row (r lo hi n d : ℕ)
    (hn : fastChoose (blockLength - lo) (deletionSize r) = n)
    (hd : intervalDenominator r hi = d)
    (hpos : 0 < d) (ha : 0 < childRows r)
    (hc :
      let a := childRows r
      let x := reducedHeight r lo
      let pd := newDenominator a x (cutoff r)
      (rankReserve r + extraReserve r lo) * (d * pd) +
        n * newNumerator (k + a) a x (cutoff r) < (prefixCap + 1) * (d * pd)) :
    intervalBound r lo hi < (prefixCap : ℚ) + 1 := by
  unfold intervalBound intervalRatio newNativePrice
  dsimp only
  rw [hn, hd, new_price_fraction _ _ _ _ ha]
  exact fee_fraction_lt _ _ _ _ _ _ hpos
    (Nat.mul_pos (gap_pos _ _) (Nat.add_pos_left ha _)) hc

/-- The intervals form a consecutive cover. Each bound is checked separately. -/
private inductive Covered (r : ℕ) : ℕ → Prop where
  | last (lo : ℕ) (h : fixedLimit r < lo) : Covered r lo
  | step (lo hi : ℕ) (hhi : hi ≤ fixedLimit r)
      (hrow : intervalBound r lo hi < (prefixCap : ℚ) + 1)
      (tail : Covered r (hi + 1)) : Covered r lo

private theorem covered_bound (r g lo : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hlo : lo ≤ g) (hg : g ≤ fixedLimit r) (h : Covered r lo) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g < (prefixCap : ℚ) + 1 := by
  induction h with
  | last lo he => omega
  | step lo hi hhi hrow tail ih =>
    by_cases hh : g ≤ hi
    · exact (native_le_interval r g lo hi hr hr16 hlo hh hhi).trans_lt hrow
    · exact ih (by omega)

private theorem interval_7_0 : intervalBound 7 0 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 7 0 14678
    422242198515215421625824190019449329526518448128
    168399027036883270630019521440191099696571720
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_7 : Covered 7 0 := by
  refine .step 0 14678 (by decide) interval_7_0 ?_
  exact .last 14679 (by decide)

private theorem interval_8_0 : intervalBound 8 0 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 8 0 14678
    4432098913149497004569630004492530100439776589795650188869632
    508190109464535481702389350592153251510887997664958263360
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_8 : Covered 8 0 := by
  refine .step 0 14678 (by decide) interval_8_0 ?_
  exact .last 14679 (by decide)

private theorem interval_9_0 : intervalBound 9 0 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 9 0 14678
    82985037157342199950345834479116529125598505518551684261327536128
    3106381342753263750380632504042344770758236188635829879096640
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_9 : Covered 9 0 := by
  refine .step 0 14678 (by decide) interval_9_0 ?_
  exact .last 14679 (by decide)

private theorem interval_10_0 : intervalBound 10 0 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 10 0 14678
    366340422393039911676501100216249756356263641368320230725462436506470766084096
    4055826891544388810783443260159944811749032065440229185603098867125571080
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_10 : Covered 10 0 := by
  refine .step 0 14678 (by decide) interval_10_0 ?_
  exact .last 14679 (by decide)

private theorem interval_11_0 : intervalBound 11 0 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 11 0 14678
    964626172130375279386958657294852412209504272917867488730613906297312662237442545357619200
    3146814158903462701269366345932430150516183848313260695446078822979106101608892684992
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_11 : Covered 11 0 := by
  refine .step 0 14678 (by decide) interval_11_0 ?_
  exact .last 14679 (by decide)

private theorem interval_12_0 : intervalBound 12 0 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 12 0 14678
    12040555749690594749239388146893137795143052287348718934096354265441751632206066179015265484800
    13223306447482213203571536056401313046237819053593360599851353974011076227223268173922008
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_12 : Covered 12 0 := by
  refine .step 0 14678 (by decide) interval_12_0 ?_
  exact .last 14679 (by decide)

private theorem interval_13_0 : intervalBound 13 0 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 13 0 14678
    17856452928583865090450316453749447941588394573582706677021977989385637691517914207944319101249881293619200
    5866879975417724557072608567297339020644621148484363834808312267264901043180261597170369326728896448
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_13 : Covered 13 0 := by
  refine .step 0 14678 (by decide) interval_13_0 ?_
  exact .last 14679 (by decide)

private theorem interval_14_0 : intervalBound 14 0 7339 < (prefixCap : ℚ) + 1 :=
  interval_row 14 0 7339
    187221337665616108700353477954272211777965999425099962967240034823110534068027026887454596912784755387338588160
    148597446997697727205114281276576236387502787761197708731457953807955610392094106764529078334376878005200
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_14_7340 : intervalBound 14 7340 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 14 7340 14678
    92044747896110849327033358223936236772647661558404894168568609579830187037212356340707518295787534070190684192
    20759800401437317878765712978314073668260974970197487630420928528446661159686956181019005273963707215552
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_14 : Covered 14 0 := by
  refine .step 0 7339 (by decide) interval_14_0 ?_
  refine .step 7340 14678 (by decide) interval_14_7340 ?_
  exact .last 14679 (by decide)

private theorem interval_15_0 : intervalBound 15 0 7339 < (prefixCap : ℚ) + 1 :=
  interval_row 15 0 7339
    171534206195691160296526030629964564663184055914115996232495083058396804951877630029712601976027828458458319724994905047040
    50646999142108954884715693815050917418777551464323267387790134192707110359291576366799430752638985635793347714385600
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_15_7340 : intervalBound 15 7340 11009 < (prefixCap : ℚ) + 1 :=
  interval_row 15 7340 11009
    77444332581852857006132284488019431567928038219486535694241924607933140514115668733263417190552014974451960799199166709368
    17552067886670069241453243458870835940776821475027967769740525323087309635598035061095955514363047515158509342662400
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_15_11010 : intervalBound 15 11010 14678 < (prefixCap : ℚ) + 1 :=
  interval_row 15 11010 14678
    51589326570067944228167733394890678230704005881981861068396256584559359458325162162979277741735502645190445678336599457805
    5751412175712708016803184859394959785714981100368676535404799827938516512658634010121138338928893377073066873178560
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_15 : Covered 15 0 := by
  refine .step 0 7339 (by decide) interval_15_0 ?_
  refine .step 7340 11009 (by decide) interval_15_7340 ?_
  refine .step 11010 14678 (by decide) interval_15_11010 ?_
  exact .last 14679 (by decide)

private theorem interval_16_0 : intervalBound 16 0 3606 < (prefixCap : ℚ) + 1 :=
  interval_row 16 0 3606
    114536897603298755427924249236563228755012280617414493634602231713678464853595959917232410968988852330397180303934995787822463098552320
    38553202102487059409318106312829172219719781963832850635883376914848830885624951121979197552560671954169155000994469221497434000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_3607 : intervalBound 16 3607 7213 < (prefixCap : ℚ) + 1 :=
  interval_row 16 3607 7213
    74541983187379651954712123743732210550523214249172090659624517472592539202625988468170621460051238856982553375132400965199490231405744
    13032846776440280686643984105054873021124941419980447637890694594418881253274919443366638150980193976750801485432266594778501400
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_7214 : intervalBound 16 7214 9017 < (prefixCap : ℚ) + 1 :=
  interval_row 16 7214 9017
    48220905196960206195495788160501663483073895102015594179765543645975713457722365130042511023188510136114995010540382318413764483092800
    7427803880546460005929557835966321946702655382790135989265867369566647595236474815133225546333504935060013750827911324891356000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_9018 : intervalBound 16 9018 10820 < (prefixCap : ℚ) + 1 :=
  interval_row 16 9018 10820
    38691880001128206058435761014891818970148660954052138000619994607335522803035592514084312627050202355587610133320841980153506916440000
    4175448589302656883349595117542704570666665968702513481962344845037273673436634982844680680547619864448762979638690279825114000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_10821 : intervalBound 16 10821 11722 < (prefixCap : ℚ) + 1 :=
  interval_row 16 10821 11722
    31000875124084765756377851382307460199370567626158226740223146266159942045387237486511509082093315612332202521726050164158558393124104
    3112892306820363256286756168387834213141734073529247078785848647355215126686790990597586612376789630698889612017612354212855500
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_11723 : intervalBound 16 11723 12624 < (prefixCap : ℚ) + 1 :=
  interval_row 16 11723 12624
    27730958340957013797384068016888192426731405387202726193385248322316009141449621999364934511018448999276182663031026399233261435885904
    2311934459270806334628274207816207273374122675247234916595603360359108241344239600650664528205058238766724968436514284552531325
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_12625 : intervalBound 16 12625 13075 < (prefixCap : ℚ) + 1 :=
  interval_row 16 12625 13075
    24795970520081577682234621680454644175028628072427854984938458020872282021436528480013967309182959768630341085061241808427768134125010
    1989524132850373652512468309550547062547948751711025626244864709665788860015273149194026863936777572246405669461463563914124000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_13076 : intervalBound 16 13076 13526 < (prefixCap : ℚ) + 1 :=
  interval_row 16 13076 13526
    23443547140207014422960258398539284760099835135387697044868000823583197367007293770951456767392172361548613490020744366462312389079648
    1710386178657784599707122065603588013345892496728734595148107500095618090604773129882225554894317153584098319942896818190382000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_13527 : intervalBound 16 13527 13752 < (prefixCap : ℚ) + 1 :=
  interval_row 16 13527 13752
    22162634647472740889101507812348992439869078312097931235415936627034710496230952769053379648771364386694529871820230405398965983560464
    1585005782962949150886033389622640078004878481733226711336183894650433421884123342750049456110633249451345651530803342196534500
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_13753 : intervalBound 16 13753 13977 < (prefixCap : ℚ) + 1 :=
  interval_row 16 13753 13977
    21546498868889441876519549385487094426631114465336228062127465747015044964067770073029763528048776919966450814258642713482203269066680
    1468942329192548733830922334558898403047700280251347247202146274230940922271235461384691046668682092044664719650927998705998000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_13978 : intervalBound 16 13978 14090 < (prefixCap : ℚ) + 1 :=
  interval_row 16 13978 14090
    20949571380752745421437366754083214794294224524655857190834404063996460238338273997711322177265574489101583303446462271424429647467808
    1413764328059244704264758422574493499094781255261247241694417315980421410491546205842040038677410695143370459736889940715645500
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14091 : intervalBound 16 14091 14202 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14091 14202
    20655849891283092416433850279928641942914941881613781211997529444339770551048824724625867082751836411720080834115408076063666607434480
    1361034340118208689772324960704105551841490996998232587210791194741715543023462677967509358685481548844551541315952422814324000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14203 : intervalBound 16 14203 14259 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14203 14259
    20368662148536049001019551190660440430846546085240730694728240546771545700494426609885885451825471177490097340133354561219042408472896
    1334926134282054441794683265244742588203160404256404929168065909122877696765499965328013974652764093071842481869361077765758400
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14260 : intervalBound 16 14260 14315 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14260 14315
    20223991637618591504349491855103562695372458439836124879311841828203724407447070956884761579359848639001707493682729330322545729274560
    1309742921355526442991630548822797226617912679110227155950038420188117867539727934582592588842474912501386243312434004379939000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14316 : intervalBound 16 14316 14343 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14316 14343
    20082827841238661044450331391990903830823434733979179177265201141174175987516226504069237919108732421517558436627774907095561362442240
    1297322356922731544365139664266587427185927397894220095728587133941465095731801558382228265310511536164757510200896535163545600
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14344 : intervalBound 16 14344 14371 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14344 14371
    20012603991812411523396888910240418896978474942377031273737642511777214982128376810082954263802111516695804626148136513228335841351200
    1285014504630840004096508651953470069100010113827399521749361043365373085494713013016877652342874483954154342162055888068844000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14372 : intervalBound 16 14372 14385 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14372 14385
    19942617800674434836283801620146312871812559944291691028240377398267869245096648089722099158916222143988959034369732850108728343174080
    1278902539992811092108428803756429002933609550909170502983147564081918642208042415091744572174494465643857876020983525225496000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14386 : intervalBound 16 14386 14399 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14386 14399
    19907713583872644857322724563738717842100862870315168395435723504559713445819832650149367627064622547626463762187603314828556685382080
    1272818387746530620302098589183958040162126688136961340747996134906568506193036919926779602051144582329364069326844665923813600
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14400 : intervalBound 16 14400 14406 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14400 14406
    19872868490241205518957387831555743247260219536534110650648630181012082957886110752692907300994994818637540527330652705400463421790528
    1269786703490707091457743568458563946973953174662572860061993638868116668613252429183239792889488478226515720889427087179900000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14407 : intervalBound 16 14407 14413 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14407 14413
    19855468084353965835586437858620548913458616261864435956150494926579166779554210666387218507230172442632782453776710391093775644067376
    1266761927059895971756950109074948604742411034936687788193301996123688206397623365117163135404775316088802373000712565085985000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14414 : intervalBound 16 14414 14417 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14414 14417
    19838082422965975147726559402223895245160381189777259830608514327483876458735392330627692140912518490921908070529672153285349038464800
    1265036579073757556377876580160594677919705308407140574988161333548783057458080537338657594497061920848463382540693168590700000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14418 : intervalBound 16 14418 14420 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14418 14420
    19828154374646519271541193183343409333979870545029736361616956702839507818016111435932222673114868892198742279712262074007353309249760
    1263744043428204253473118807109848212783146302859056759479432361070660034585237240265996390797808074680701695498830617799325000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14421 : intervalBound 16 14421 14422 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14421 14422
    19820711493999381898589322963078425683636048444899547463538068843335124854483929759171236323632314173588487872422535071638589427701336
    1262883054887165393578059118855296735620297405542254886731862690962953983211444198634584298620235812522578756967492513692950000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14423 : intervalBound 16 14423 14424 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14423 14424
    19815751075703351904318595469308256468369247088046583729379894460340924514061375386226727819947049468779208641298199091618380861831632
    1262022627450083495331698512559884316195221294382991755586777227330627492993095449351826731973501666557455191995896842489601250
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14425 : intervalBound 16 14425 14425 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14425 14425
    19810791858787406502493258381107439032456718288692740395837670472041619334662822265671612264957131976738051373486543658888816953889076
    1261592624036437406707598412330429664709028234966805677777220676122109287397213174559075416997346672878199137162542685972450000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14426 : intervalBound 16 14426 14426 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14426 14426
    19808312700759066287969635683575903984236734523753638126927046063802310722084156327692548002707511757492539807588981974668286621837152
    1261162760767899614340642251572472865172891414585124593800614411484753231078731708780063554614144116309857479431590440383025000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem interval_16_14427 : intervalBound 16 14427 14427 < (prefixCap : ℚ) + 1 :=
  interval_row 16 14427 14427
    19805833842970276086793592526816238344180253610900166183903387151539262127987705489052810603777745116132274228446427705534777079190768
    1260733037600870063798726801848970000387199698869276563909836287731562177252643045955780337154312035086244100044219489135950000
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem covered_16 : Covered 16 0 := by
  refine .step 0 3606 (by decide) interval_16_0 ?_
  refine .step 3607 7213 (by decide) interval_16_3607 ?_
  refine .step 7214 9017 (by decide) interval_16_7214 ?_
  refine .step 9018 10820 (by decide) interval_16_9018 ?_
  refine .step 10821 11722 (by decide) interval_16_10821 ?_
  refine .step 11723 12624 (by decide) interval_16_11723 ?_
  refine .step 12625 13075 (by decide) interval_16_12625 ?_
  refine .step 13076 13526 (by decide) interval_16_13076 ?_
  refine .step 13527 13752 (by decide) interval_16_13527 ?_
  refine .step 13753 13977 (by decide) interval_16_13753 ?_
  refine .step 13978 14090 (by decide) interval_16_13978 ?_
  refine .step 14091 14202 (by decide) interval_16_14091 ?_
  refine .step 14203 14259 (by decide) interval_16_14203 ?_
  refine .step 14260 14315 (by decide) interval_16_14260 ?_
  refine .step 14316 14343 (by decide) interval_16_14316 ?_
  refine .step 14344 14371 (by decide) interval_16_14344 ?_
  refine .step 14372 14385 (by decide) interval_16_14372 ?_
  refine .step 14386 14399 (by decide) interval_16_14386 ?_
  refine .step 14400 14406 (by decide) interval_16_14400 ?_
  refine .step 14407 14413 (by decide) interval_16_14407 ?_
  refine .step 14414 14417 (by decide) interval_16_14414 ?_
  refine .step 14418 14420 (by decide) interval_16_14418 ?_
  refine .step 14421 14422 (by decide) interval_16_14421 ?_
  refine .step 14423 14424 (by decide) interval_16_14423 ?_
  refine .step 14425 14425 (by decide) interval_16_14425 ?_
  refine .step 14426 14426 (by decide) interval_16_14426 ?_
  refine .step 14427 14427 (by decide) interval_16_14427 ?_
  exact .last 14428 (by decide)

theorem arithmetic_bound (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16) (hg : g ≤ fixedLimit r) :
    ((rankReserve r + extraReserve r g : ℕ) : ℚ) +
      incidenceRatio r g * nativePlanePrice r g < (prefixCap : ℚ) + 1 := by
  apply covered_bound r g 0 hr hr16 (Nat.zero_le g) hg
  interval_cases r
  · exact covered_7
  · exact covered_8
  · exact covered_9
  · exact covered_10
  · exact covered_11
  · exact covered_12
  · exact covered_13
  · exact covered_14
  · exact covered_15
  · exact covered_16

end P0_1
end PackSource_P0_1Arithmetic

section PackSource_P0_1Counting
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0_1
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator ProximityPrize.Benchmark P0
open K1_2 (padding fixedLimit deletionSize padding_le_eight fixedLimit_le planePrice_nonneg
  goodSet errorSet mixedChoices JointOn)

theorem rank_book (u : Words) (hfirst : firstRank u = L) (Γ : Finset K) :
    (abnormalSlopes u Γ).card ≤ rankReserve (nullity u) := by
  classical
  have hb := Strata.two_block_rank_exception_count p node (u 0) (u 1) L t
    (nullity u) (actual_stackRank u) hfirst (abnormalSlopes u Γ) (by
      intro γ hγ
      rw [← actual_stackRank u]
      exact (Finset.mem_filter.mp hγ).2)
  have he : t + 1 - nullity u - L = t + 1 - L - nullity u := by omega
  rw [he] at hb
  exact hb

/-- Apply one child count per deletion union and keep the rational child
price through the finite incidence inequality. -/
theorem padded_count {u : Words} {D : Finset I} {Γ : Finset K} {r g : ℕ}
    (F : PaddedFamily u D Γ r g) (hr : 7 ≤ r) (hr16 : r ≤ 16) (hg : g ≤ fixedLimit r)
    (hchild : ∀ J ∈ D.powersetCard (deletionSize r),
      ((childSlopes F J).card : ℚ) ≤ nativePlanePrice r g) :
    (Γ.card : ℚ) ≤ incidenceRatio r g * nativePlanePrice r g := by
  classical
  have hg' := hg.trans (fixedLimit_le r)
  have hj := padding_le_eight r
  have ht : t = 81927 := by decide
  have hA : agreement = 180217 := by decide
  have hk : k = 131072 := by decide
  let q := nativePlanePrice r g
  let n := q.num.toNat
  let d := q.den
  have hd : (0 : ℚ) < d := by exact_mod_cast Rat.den_pos q
  have hn : (n : ℚ) = (q.num : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg]
    exact Rat.num_nonneg.mpr (planePrice_nonneg _ _ _ _)
  have hq : (n : ℚ) / d = q := by rw [hn, Rat.num_div_den]
  have hfit : r - 1 + padding r ≤ t - g := by omega
  have hden : 0 < (incidenceDenominator r g : ℚ) := by
    unfold incidenceDenominator
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hfit)
      (Nat.choose_pos (by omega : padding r ≤ agreement - 1))
  have hcount := K1_2.Mixed.shared_mixed_rational_count node (u 0) (u 1)
    IRSProfile.domain.injective D Γ k agreement (t - g) (r - 1) (padding r) n d
    (fun γ => goodSet u D γ (F.decoder γ)) (fun γ => errorSet u D γ (F.decoder γ)) F.slack
    (by omega) hfit (by omega)
    (by
      intro γ hγ
      rcases F.witness γ hγ with ⟨hs, hS, hE, hbad⟩
      have hsub : goodSet u D γ (F.decoder γ) ⊆ D := by
        intro i hi
        exact (mem_filter.mp hi).1
      exact ⟨hs, hS, hE, Finset.sdiff_disjoint, union_subset sdiff_subset hsub, hbad⟩)
    (by
      intro J hJ
      have hh := hchild J hJ
      change ((childSlopes F J).card : ℚ) ≤ q at hh
      rw [← hq] at hh
      have hmul := (le_div_iff₀ hd).mp hh
      have hc : (childSlopes F J).card * d ≤ n := by exact_mod_cast hmul
      have hsame : childSlopes F J = Γ.filter (fun γ =>
          J ∈ K1_2.Mixed.mixedDeletions node (u 0) (u 1) k
            (r - 1 - F.slack γ + padding r) (F.slack γ + padding r)
            (errorSet u D γ (F.decoder γ)) (goodSet u D γ (F.decoder γ))) := by
        ext γ
        simp only [childSlopes, mem_filter]
        unfold mixedChoices K1_2.Mixed.mixedDeletions K1_2.Mixed.goodDeletions JointOn K1_2.Mixed.JointOn
        rfl
      rw [hsame, mul_comm] at hc
      exact hc)
  change d * incidenceDenominator r g * Γ.card ≤ D.card.choose (deletionSize r) * n at hcount
  rw [F.domain_card] at hcount
  have hcountQ : (d : ℚ) * incidenceDenominator r g * Γ.card ≤
      ((blockLength - g).choose (deletionSize r) : ℚ) * n := by exact_mod_cast hcount
  change (Γ.card : ℚ) ≤ incidenceRatio r g * q
  rw [← hq, incidenceRatio, div_mul_div_comm]
  apply (le_div_iff₀ (mul_pos hden hd)).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hcountQ

end
end P0_1
end PackSource_P0_1Counting

section PackSource_P0_1Moving
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace P0_1
noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark P0
open K1_6 (shifts pairCoordinates)
open private shifted_pair_height from ProximityPrize.SubmissionLower.Fast076
open private certificate_shifts_annihilate_generic from ProximityPrize.SubmissionLower.Fast050
open private lift_common_divisor specialize_factor root_outside_of_dvd_locator
  common_node_count eval_atSlope from ProximityPrize.SubmissionLower.Fast051

/-- Complementary minors bound the unreduced primitive pair in the middle band. -/
private theorem coefficients_le {u : Words} (guard : MiddleGuard u)
    (T : TwoActive u) (R : Relation T) :
    ∀ i, (R.coefficients i).natDegree ≤ 6397065653 := by
  let P (b : Fin 2) : Bivar := Principal.assemble (fun j => R.coefficients (b, j))
  have hL : L = 49145 := by decide
  have ht : t + 1 = 81928 := by decide
  have hBalance := relation_height_balance T
  rw [hL, ht] at hBalance
  have hr := guard.1
  have hH : T.height ≤ 32776 := by omega
  have hLt : T.height < L := by omega
  have hSum : T.height + (L - T.height) = L := by omega
  have hRank : L + T.height ≤ GenericLayer.genericRank (twoBlock u) := by
    change _ ≤ stackRank u
    rw [P0.actual_stackRank, ht, hL]
    omega
  have hsize : k + (49144 + 1) + t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  have hshift : (shifts P L (L - T.height)).transpose * twoBlock u = 0 :=
    certificate_shifts_annihilate_generic p node (u 0) (u 1) node.injective
      Native.native_domain_fixed (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
      k T.height 49144 t _ hSum hsize R _ (fun _ => rfl)
  have hCoordinates : pairCoordinates P T.height = R.coefficients := by
    funext i
    exact Principal.assemble_coeff (fun j => R.coefficients (i.1, j)) i.2
  have hPrim : PrimitiveVector.IsPrimitive (pairCoordinates P T.height) := by
    rw [hCoordinates]
    exact R.primitive
  have hBound := shifted_pair_height K L T.height (t + 1) p P (twoBlock u)
    (by decide) hLt R.x_degree hPrim hRank hshift
    (stacked_entry_natDegree p node (u 0) (u 1) L t)
  have hCap : (p * L + T.height) / (L - T.height) ≤ 6397065653 := by
    have hd : 16369 ≤ L - T.height := by omega
    exact (Nat.div_le_div_right (Nat.add_le_add_left hH _)).trans
      ((Nat.div_le_div_left hd (by decide)).trans (by decide))
  intro i
  rw [← hCoordinates]
  exact (hBound i.1 i.2.val).trans hCap

/-- Saturation preserves the common divisor degree and splits that many distinct
domain roots. More roots than fixed nodes gives a new common zero. -/
theorem moving_has_new_node {u : Words} {T : TwoActive u} (R : Relation T)
    (hMoving : MovingGCD R) {γ : K} {M : BadMark u γ} (hSat : SaturatedAt R M) :
    ∃ i ∉ fixedNodes R,
      (atSlope (leftU R) γ).eval (node i) = 0 ∧ (atSlope (leftV R) γ).eval (node i) = 0 := by
  classical
  obtain ⟨G, hG, hGU, hGV, hg⟩ := hMoving.2
  obtain ⟨D, hD, hd, hDU, hDV⟩ := lift_common_divisor hG hGU hGV
  obtain ⟨A, hA⟩ := hDU
  obtain ⟨B, hB⟩ := hDV
  obtain ⟨hAU, hAUdeg⟩ := specialize_factor hD hA hSat.U_ne
  obtain ⟨hBV, hBVdeg⟩ := specialize_factor hD hB hSat.V_ne
  change atSlope (leftU R) γ = atSlope D γ * atSlope A γ at hAU
  change atSlope (leftV R) γ = atSlope D γ * atSlope B γ at hBV
  change (atSlope (leftU R) γ).natDegree + D.natDegree ≤
    (leftU R).natDegree + (atSlope D γ).natDegree at hAUdeg
  change (atSlope (leftV R) γ).natDegree + D.natDegree ≤
    (leftV R).natDegree + (atSlope D γ).natDegree at hBVdeg
  have hdeg : D.natDegree ≤ (atSlope D γ).natDegree := by
    have hU := R.x_degree 0
    have hV := R.x_degree 1
    change (leftU R).natDegree ≤ T.height at hU
    change (leftV R).natDegree ≤ T.height at hV
    have hMax := hSat.degree_eq
    rcases le_total (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree with h | h
    · rw [max_eq_right h] at hMax
      omega
    · rw [max_eq_left h] at hMax
      omega
  obtain ⟨errors, _, hGCD⟩ := hSat.gcd_errors
  have hDvd := hGCD.2.2.2 (atSlope D γ) ⟨atSlope A γ, hAU⟩ ⟨atSlope B γ, hBV⟩
  have hCard : (fixedNodes R).card < (atSlope D γ).natDegree := by omega
  obtain ⟨i, hiFixed, hi⟩ := root_outside_of_dvd_locator (F := K) (ι := I)
    node IRSProfile.domain.injective errors (fixedNodes R) (atSlope D γ) hDvd hCard
  exact ⟨i, hiFixed, by rw [hAU, eval_mul, hi, zero_mul], by rw [hBV, eval_mul, hi, zero_mul]⟩

/-- Keep the domain cardinality symbolic while composing the covering bound. -/
private theorem common_node_count_at {F ι : Type} [Field F] [Fintype ι]
    (U V : ι → F[X]) (N H : ℕ) (hcard : Fintype.card ι = N) (Γ : Finset F)
    (hU : ∀ i, (U i).natDegree ≤ H) (hV : ∀ i, (V i).natDegree ≤ H)
    (hNew : ∀ γ ∈ Γ, ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0) :
    Γ.card ≤ N * H :=
  (common_node_count U V H Γ hU hV hNew).trans_eq (congrArg (fun n : ℕ => n * H) hcard)

/-- Cover the marked slopes by one nonzero seed polynomial per nonfixed node. -/
theorem normal_growth_count {u : Words} (guard : MiddleGuard u)
    {T : TwoActive u} (R : Relation T)
    (hMoving : MovingGCD R) (hSat : NormalSaturation R) (Γ : Finset K)
    (hBad : BadFamily u Γ) (hNormal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ 1676952378540032 := by
  classical
  have hHeight := coefficients_le guard T R
  let U (i : I) := (leftU R).eval (C (node i))
  let V (i : I) := (leftV R).eval (C (node i))
  have hU (i) : (U i).natDegree ≤ 6397065653 := by
    dsimp only [U, leftU]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (0, j)) _
  have hV (i) : (V i).natDegree ≤ 6397065653 := by
    dsimp only [V, leftV]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (1, j)) _
  have hNew (γ : K) (hγ : γ ∈ Γ) :
      ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0 := by
    refine (P0.bad_mark u Γ hBad γ hγ).elim (fun M => ?_)
    obtain ⟨i, hi, hu, hv⟩ := moving_has_new_node R hMoving (hSat γ (hNormal γ hγ) M)
    have hNZ : ¬ (U i = 0 ∧ V i = 0) := by
      simpa only [fixedNodes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact ⟨i, hNZ, (eval_atSlope _ γ _).symm.trans hu, (eval_atSlope _ γ _).symm.trans hv⟩
  have hcount := common_node_count_at U V 262144 6397065653 IRSProfile.card_index Γ hU hV hNew
  exact hcount.trans (by decide)

end
end P0_1
end PackSource_P0_1Moving

section PackSource_P0_1Pruning
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0_1
noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark P0
open K1_2.Pruning (bound)

private def pruneFactor : ℚ := 247218 / 67001

/-- Once the first multiplication dominates the terminal charge, every
subsequent step is bounded by another power of the same factor. -/
private theorem pruning_power (δ r : ℕ)
    (hbase : ((δ : ℚ) + 87041886477376) ≤ pruneFactor * δ) :
    bound δ 87041886477376 pruneFactor r ≤ pruneFactor ^ r * δ := by
  have hfactor : 1 ≤ pruneFactor := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 67001)).mpr
    rw [one_mul]
    exact_mod_cast (show (67001 : ℕ) ≤ 247218 by decide)
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : (1 : ℚ) ≤ pruneFactor ^ r := one_le_pow₀ hfactor
    have hδ : (δ : ℚ) ≤ pruneFactor ^ r * δ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg δ)
    rw [K1_2.Pruning.bound_succ, pow_succ']
    apply max_le
    · exact hbase.trans ((mul_le_mul_of_nonneg_left hδ (zero_le_one.trans hfactor)).trans_eq
        (mul_assoc _ _ _).symm)
    · exact (mul_le_mul_of_nonneg_left ih (zero_le_one.trans hfactor)).trans_eq
        (mul_assoc _ _ _).symm

private theorem pruning_row (δ cap r : ℕ)
    (hbase : (δ + 87041886477376) * 67001 ≤ 247218 * δ)
    (hprice : 247218 ^ r * δ < (cap + 1) * 67001 ^ r) :
    bound δ 87041886477376 pruneFactor r < (cap : ℚ) + 1 := by
  have hpos : (0 : ℚ) < 67001 := by positivity
  have hbase' : ((δ : ℚ) + 87041886477376) * 67001 ≤ 247218 * δ := by
    exact_mod_cast hbase
  have hstart : (δ : ℚ) + 87041886477376 ≤ pruneFactor * δ := by
    rw [show pruneFactor * δ = (247218 * (δ : ℚ)) / 67001 by unfold pruneFactor; ring]
    exact (le_div_iff₀ hpos).mpr hbase'
  have hprice' : (247218 : ℚ) ^ r * δ < ((cap : ℚ) + 1) * (67001 : ℚ) ^ r := by
    exact_mod_cast hprice
  refine (pruning_power δ r hstart).trans_lt ?_
  rw [pruneFactor, div_pow, div_mul_eq_mul_div]
  exact (div_lt_iff₀ (pow_pos hpos _)).mpr hprice'

private theorem pruning_bound_lt (r : ℕ) (hr : r ≤ 6) :
    bound (rankReserve r) 87041886477376 pruneFactor r < (176232354070904438 : ℚ) + 1 := by
  interval_cases r
  all_goals
    exact pruning_row _ 176232354070904438 _ (by decide) (by decide)

/-- Use one exact same-support witness for each label in the old pruning induction. -/
theorem count_le_six (core : ShortenedCap 247217 87041886477376)
    (u : Words) (hfirst : firstRank u = L) (hr : nullity u ≤ 6)
    (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 176232354070904438 := by
  let : NeZero k := ⟨by decide⟩
  obtain ⟨W⟩ := K1_2.Pruning.witnessFamily_of_MCA node u k agreement (by decide)
    radius (fun _ hT => agreement_of_threshold hT) Γ hΓ
  have hpunct : K1_2.Pruning.PuncturedCap node k agreement 67000 87041886477376 := core
  let φ := algebraMap K[X] Frac
  have hp := K1_2.Pruning.stacked_pruning_count_of_card p φ (IsFractionRing.injective K[X] Frac)
    node node.injective Native.native_domain_fixed (u 0) (u 1)
    blockLength k agreement L 67000 87041886477376 IRSProfile.card_index
    (by decide) (by decide) hfirst hpunct Γ W
  change (Γ.card : ℚ) ≤ bound (L + p * (stackRank u - L))
    87041886477376 (1 + (agreement : ℚ) / ((67000 : ℚ) + 1)) (t + 1 - stackRank u) at hp
  rw [actual_stackRank] at hp
  have hdepth : t + 1 - (t + 1 - nullity u) = nullity u := by
    change 81928 - (81928 - nullity u) = nullity u
    omega
  have hfactor : 1 + (agreement : ℚ) / (67000 + 1) = pruneFactor := by
    change 1 + (180217 : ℚ) / (67000 + 1) = 247218 / 67001
    ring
  have hδ : t + 1 - nullity u - L = t + 1 - L - nullity u := by omega
  rw [hdepth, hfactor, hδ] at hp
  have hh := hp.trans_lt (pruning_bound_lt (nullity u) hr)
  have hn : Γ.card < 176232354070904438 + 1 := by exact_mod_cast hh
  omega

end
end P0_1
end PackSource_P0_1Pruning

section PackSource_P0_1Saturation
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace P0_1
noncomputable section

open Polynomial Matrix FrobeniusLocator P0
open ProximityPrize.Benchmark

private theorem eval_atSlope (P : Bivar) (a γ : K) :
    (atSlope P γ).eval a = (P.eval (C a)).eval γ := by
  simpa only [atSlope, Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (C a) (p := P))

private theorem atSlope_constant (G : K[X]) (γ : K) :
    atSlope (G.map C) γ = G := by
  rw [atSlope, Polynomial.map_map]
  have h : (Polynomial.evalRingHom γ).comp C = RingHom.id K := by
    ext a
    simp
  rw [h, Polynomial.map_id]

private theorem twoBlock_atSlope (u : Words) (γ : K) :
    ((twoBlock u).map (evalRingHom γ)) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        node (fun i => u 0 i + γ * u 1 i) L t := by
  rw [twoBlock, Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]

private theorem rank_at_normal {u : Words} (T : TwoActive u) {γ : K} (hγ : Normal u γ) :
    ((twoBlock u).map (evalRingHom γ)).rank = L + T.height := by
  change _ = stackRank u at hγ
  rw [hγ, actual_stackRank]
  have h := relation_height_balance T
  omega

/-- The original stack has the same rank as its two evaluated error blocks. -/
private theorem error_rank {u : Words} {γ : K} (M : BadMark u γ)
    (E : Finset I) (hE : E.card ≤ t)
    (hEagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    ((twoBlock u).map (evalRingHom γ)).rank =
      (Strata.errorTwoMatrix (frobenius K p) (fun i : E => node i.val)
        (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) L).rank := by
  have hfix : ∀ b i, Strata.twoConjugations (frobenius K p) b (node i) = node i := by
    intro b i
    fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]
  have h := Strata.conjugateHankel_error_rank
    (Strata.twoConjugations (frobenius K p)) node (fun i => u 0 i + γ * u 1 i)
    IRSProfile.domain.injective hfix M.decoder k L t M.degree
    (by rw [IRSProfile.card_index]; decide) E (hE.trans (Nat.le_succ _)) hEagree
  rw [Strata.conjugateErrors_two] at h
  rw [twoBlock_atSlope]
  exact h

/-- When the distinct common error roots exhaust the gcd degree, their
monic locator has the same divisors as the gcd. -/
private theorem commonGCD_of_roots (U V : K[X]) (hV : V ≠ 0) (S : Finset I)
    (hroots : ∀ i ∈ S, (GCDMonoid.gcd U V).eval (node i) = 0)
    (hcard : S.card = (GCDMonoid.gcd U V).natDegree) :
    IsCommonGCD (locator node S) U V := by
  have hG : GCDMonoid.gcd U V ≠ 0 := gcd_ne_zero_of_right hV
  have hdiv := Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _ hroots
  have hassoc := Polynomial.associated_of_dvd_of_natDegree_le hdiv hG
    (by rw [locator_natDegree, hcard])
  exact ⟨(locator_monic node S).ne_zero, hdiv.trans (gcd_dvd_left U V),
    hdiv.trans (gcd_dvd_right U V), fun H hHU hHV => (dvd_gcd hHU hHV).trans hassoc.dvd'⟩

private theorem lift_dvd_atSlope {P : Bivar} {G : K[X]} (γ : K) (h : G.map C ∣ P) :
    G ∣ atSlope P γ := by
  have h' := map_dvd (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) h
  change atSlope (G.map C) γ ∣ atSlope P γ at h'
  rwa [atSlope_constant] at h'

private theorem valid_of_saturation {u : Words} {T : TwoActive u} (R : Relation T)
    (γ : K) (S : Finset I)
    (hdegree : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree = T.height)
    (hG : IsCommonGCD (locator node S) (atSlope (leftU R) γ) (atSlope (leftV R) γ)) :
    ¬ InvalidLeft R := by
  intro hinvalid
  rcases hinvalid with hlow | ⟨G, _, hGU, hGV, hbad⟩
  · have hle : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree ≤
        max (leftU R).natDegree (leftV R).natDegree :=
      max_le_max Polynomial.natDegree_map_le Polynomial.natDegree_map_le
    omega
  · have hS : locator node S ∣ locator node Finset.univ :=
      ⟨locator node (Finset.univ \ S),
        (Principal.locator_mul_sdiff node S Finset.univ (Finset.subset_univ S)).symm⟩
    exact hbad ((hG.2.2.2 G (lift_dvd_atSlope γ hGU) (lift_dvd_atSlope γ hGV)).trans hS)

/-- Normal saturation depends on the height being strictly below the
ordinary row count. The same argument covers the middle prefix. -/
theorem saturation_of_height (u : Words) (T : TwoActive u) (R : Relation T)
    (hH : T.height < L) : NormalSaturation R := by
  classical
  intro γ hγ M
  let U := atSlope (leftU R) γ
  let V := atSlope (leftV R) γ
  let E : Finset I := Finset.univ.filter (fun i => M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i)
  let e : E → K := fun i => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)
  let x : E → K := fun i => node i.val
  have hEagree (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm h⟩)
  have hEcard : E.card ≤ t := by
    have hsub : E ⊆ Finset.univ \ M.support := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => ?_⟩
      exact (Finset.mem_filter.mp hi).2 (M.hits i hs)
    have h := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      IRSProfile.card_index] at h
    have hmark := M.agreement
    change 180217 ≤ M.support.card at hmark
    change E.card ≤ 81927
    omega
  have hfit : k + T.height ≤ M.support.card := by
    have hmark := M.agreement
    change 180217 ≤ M.support.card at hmark
    change T.height < 49145 at hH
    change 131072 + T.height ≤ M.support.card
    omega
  have hfix (i : I) : frobenius K p (node i) = node i := Native.native_domain_fixed i
  obtain ⟨hpair, hrel⟩ :=
    Strata.certificate_specializes p node (u 0) (u 1) k T.height R γ
  have hUle : U.natDegree ≤ T.height := hrel.degree_U
  have hVle : V.natDegree ≤ T.height := hrel.degree_V
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have he (i : E) : e i ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp i.property).2)
  have herror (i : E) : U.eval (x i) * e i + V.eval (x i) * frobenius K p (e i) = 0 :=
    Strata.certificate_error_identity p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed k T.height R γ M.support hfit M.decoder M.degree M.hits i.val
  have hrank : (Strata.errorTwoMatrix (frobenius K p) x e L).rank = L + T.height :=
    (error_rank M E hEcard hEagree).symm.trans (rank_at_normal T hγ)
  obtain ⟨hU, hV⟩ := Strata.saturated_coefficients_nonzero (frobenius K p) x e hx U V
    T.height L hUle hVle hpair hH he herror hrank
  let G := GCDMonoid.gcd U V
  let C₀ := (Finset.univ : Finset E).filter (fun i => G.eval (x i) = 0)
  let S := C₀.image (fun i : E => i.val)
  obtain ⟨hC, hsum, _⟩ := Strata.normal_error_three_rank (frobenius K p) x e hx
    (fun i => hfix i.val) U V T.height L hUle hVle hpair hH he herror hrank
  have hmax : max U.natDegree V.natDegree = T.height := by
    obtain ⟨hle, hred⟩ := Strata.gcd_reduction_degrees U V hU hV
    change max (U / G).natDegree (V / G).natDegree + G.natDegree = T.height at hsum
    change G.natDegree ≤ max U.natDegree V.natDegree at hle
    change max (U / G).natDegree (V / G).natDegree =
      max U.natDegree V.natDegree - G.natDegree at hred
    omega
  have hS_card : S.card = G.natDegree :=
    (Finset.card_image_of_injective C₀ Subtype.val_injective).trans hC
  have hS_error (i : I) (hi : i ∈ S) : M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp j.property).2
  have hG : IsCommonGCD (locator node S) U V := by
    apply commonGCD_of_roots U V hV S _ hS_card
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hj).2
  refine ⟨hU, hV, hmax, ⟨S, hS_error, hG⟩, ?_, valid_of_saturation R γ S hmax hG⟩
  intro i hi
  have hzero := (Finset.mem_filter.mp hi).2
  have hu0 : U.eval (node i) = 0 := by
    change (atSlope (leftU R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.1, eval_zero]
  have hv0 : V.eval (node i) = 0 := by
    change (atSlope (leftV R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.2, eval_zero]
  have hdiv : (Polynomial.X : K[X]) - C (node i) ∣ locator node S :=
    hG.2.2.2 _ (dvd_iff_isRoot.mpr hu0) (dvd_iff_isRoot.mpr hv0)
  have hroot : (locator node S).eval (node i) = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero hdiv (by rw [eval_sub, eval_X, eval_C, sub_self])
  exact hS_error i ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective S i).mp hroot)

end
end P0_1
end PackSource_P0_1Saturation

section PackSource_P0_1Shortened
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0_1
noncomputable section

open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark P0
open ReedSolomon.HiddenDerivative
open scoped BigOperators

/-- Apply the library's exact correlated-pair theorem to the actual puncture.
The same witness support supplies the agreement lower bound and the
contradiction to joint extension. -/
private theorem shortened_from_weighted (N cap m B H : ℕ)
    (hB : B ≤ 2 * 131071 + 1)
    (hcert : ∀ n ≤ N, IsJohnsonWeightedCertificate n 131071 agreement m B
      (johnsonWeightedHeight n 131071 agreement m B))
    (hheight : ∀ n ≤ N, johnsonWeightedHeight n 131071 agreement m B ≤ H)
    (hprice : johnsonWeightedRefinedExceptionCount N 131071 agreement B H < (cap : ℚ) + 1) :
    ShortenedCap N cap := by
  classical
  let : DecidableEq K := Classical.decEq K
  intro D hD u v Γ hΓ
  by_cases hA : agreement ≤ D.card
  swap
  · have hzero : Γ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨S, hSD, hAS, _, _⟩ := hΓ γ hγ
      exact hA (hAS.trans (card_le_card hSD))
    simp [hzero]
  let e : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (α := D) (by simp)).symm
  let x : Fin D.card ↪ K :=
    ⟨fun j => node (e j).val, fun i j h => e.injective (Subtype.ext (IRSProfile.domain.injective h))⟩
  let u' (j : Fin D.card) := u (e j).val
  let v' (j : Fin D.card) := v (e j).val
  obtain ⟨exceptions, hcard, hexact⟩ := ReedSolomon.exists_weightedJohnson_line_exactCorrelatedPair
    x u' v' (hcert D.card hD) (by decide) (by decide) hA hB
  have hsub : Γ ⊆ exceptions := by
    intro γ hγ
    by_contra hnormal
    obtain ⟨S, hSD, hAS, ⟨P, hP, hval⟩, hnonjoint⟩ := hΓ γ hγ
    let f : S ↪ Fin D.card :=
      ⟨fun i => e.symm ⟨i.val, hSD i.property⟩,
        fun i j hh => Subtype.ext (congrArg (fun z : D => z.val) (e.symm.injective hh))⟩
    have hf (i : S) : (e (f i)).val = i.val := by simp [f]
    let hits := ReedSolomon.polynomialAgreementSet x (fun j => u' j + γ * v' j) P
    have hhits (i : S) : f i ∈ hits := by
      have h := hval i.val i.property
      simpa only [hits, ReedSolomon.polynomialAgreementSet, mem_filter, mem_univ, true_and,
        x, Function.Embedding.coeFn_mk, u', v', hf] using h
    have hinj : S.attach.map f ⊆ hits := by
      intro j hj
      obtain ⟨i, _, rfl⟩ := mem_map.mp hj
      exact hhits i
    have hA' : agreement ≤ hits.card := hAS.trans (by simpa using card_le_card hinj)
    obtain ⟨pair, h0, h1, _, hsets⟩ := hexact γ hnormal P hP (by simpa only [hits] using hA')
    change hits = ReedSolomon.commonPolynomialAgreementSet x u' v' pair.1 pair.2 at hsets
    have hboth (i : S) : pair.1.eval (node i.val) = u i.val ∧
        pair.2.eval (node i.val) = v i.val := by
      have hi := hhits i
      rw [hsets] at hi
      simpa only [ReedSolomon.commonPolynomialAgreementSet, mem_filter, mem_univ, true_and,
        x, Function.Embedding.coeFn_mk, u', v', hf] using hi
    exact hnonjoint ⟨⟨pair.1, h0, fun i hi => (hboth ⟨i, hi⟩).1⟩,
      ⟨pair.2, h1, fun i hi => (hboth ⟨i, hi⟩).2⟩⟩
  have hmono : johnsonWeightedRefinedExceptionCount D.card 131071 agreement B
      (johnsonWeightedHeight D.card 131071 agreement m B) ≤
      johnsonWeightedRefinedExceptionCount N 131071 agreement B H := by
    let h := johnsonWeightedHeight D.card 131071 agreement m B
    have hh : h ≤ H := hheight D.card hD
    have hN : D.card - 131071 ≤ N - 131071 := Nat.sub_le_sub_right hD _
    have hN' : D.card - 131071 - 1 ≤ N - 131071 - 1 := Nat.sub_le_sub_right hN _
    have hslots : h + B + (2 * 131071 - 1) * h * (2 * B - 1) ≤
        H + B + (2 * 131071 - 1) * H * (2 * B - 1) :=
      Nat.add_le_add (Nat.add_le_add_right hh B)
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hh))
    unfold johnsonWeightedRefinedExceptionCount
    change (((2 * B - 1) * h : ℕ) : ℚ) + _ + _ ≤ (((2 * B - 1) * H : ℕ) : ℚ) + _ + _
    apply add_le_add
    · apply add_le_add
      · exact_mod_cast Nat.mul_le_mul_left (2 * B - 1) hh
      · apply mul_le_mul
        · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hN) (Nat.cast_nonneg _)
        · exact Nat.cast_le.mpr hslots
        · exact Nat.cast_nonneg _
        · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact_mod_cast Nat.mul_le_mul_right B hN'
  have hΓq : (Γ.card : ℚ) ≤
      johnsonWeightedRefinedExceptionCount N 131071 agreement B H :=
    (show (Γ.card : ℚ) ≤ exceptions.card by exact_mod_cast card_le_card hsub).trans
      (hcard.trans hmono)
  exact Nat.le_of_lt_succ (by exact_mod_cast (hΓq.trans_lt hprice))

/-- The quadratic moment of the grades up to and including (b). -/
private theorem sum_range_squares (b : ℕ) :
    6 * (∑ i ∈ Finset.range (b + 1), i^2) = b * (b + 1) * (2 * b + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- Check the two moments of the positive widths by polynomial identities. -/
private theorem range_moments (a d b : ℕ) (hcut : d * b ≤ a) :
    2 * (∑ j ∈ Finset.range (b + 1), (a - d*j)) + d * (b * (b + 1)) =
        2 * ((b + 1) * a) ∧
    6 * (∑ j ∈ Finset.range (b + 1), j * (a - d*j)) + d * (b * (b + 1) * (2*b + 1)) =
        3 * a * (b * (b + 1)) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (b + 1)) : a - d*j + d*j = a := by
    exact Nat.sub_add_cancel ((Nat.mul_le_mul_left d (by simpa using hj)).trans hcut)
  have h0 : (∑ j ∈ Finset.range (b + 1), (a - d*j)) +
      d * (∑ j ∈ Finset.range (b + 1), j) = (b + 1) * a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _j ∈ Finset.range (b + 1), a := Finset.sum_congr rfl hterm
      _ = _ := by simp
  have h1 : (∑ j ∈ Finset.range (b + 1), j * (a - d*j)) +
      d * (∑ j ∈ Finset.range (b + 1), j^2) = a * (∑ j ∈ Finset.range (b + 1), j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      _ = j * ((a - d*j) + d*j) := by ring
      _ = a*j := by rw [hterm j hj, Nat.mul_comm]
  have htri : 2 * (∑ j ∈ Finset.range (b + 1), j) = b * (b + 1) := by
    rw [Nat.mul_comm 2, Finset.sum_range_id_mul_two]
    simp [Nat.mul_comm]
  constructor
  · calc
      _ = 2 * ((∑ j ∈ Finset.range (b + 1), (a - d*j)) +
          d * (∑ j ∈ Finset.range (b + 1), j)) := by rw [← htri]; ring
      _ = _ := by rw [h0]
  · calc
      _ = 6 * ((∑ j ∈ Finset.range (b + 1), j * (a - d*j)) +
          d * (∑ j ∈ Finset.range (b + 1), j^2)) := by rw [← sum_range_squares]; ring
      _ = 3*a*(2*(∑ j ∈ Finset.range (b + 1), j)) := by rw [h1]; ring
      _ = _ := by rw [htri]

private theorem moment_values (a d b N W : ℕ) (hcut : d * b ≤ a)
    (hN : 2*N + d * (b * (b + 1)) = 2 * ((b + 1) * a))
    (hW : 6*W + d * (b * (b + 1) * (2*b + 1)) = 3 * a * (b * (b + 1))) :
    (∑ j ∈ Finset.range (b + 1), (a - d*j)) = N ∧
      (∑ j ∈ Finset.range (b + 1), j * (a - d*j)) = W := by
  obtain ⟨h0, h1⟩ := range_moments a d b hcut
  constructor <;> omega

private theorem small_moments :
    johnsonWeightedN 131071 agreement 512 703 = 32524551840 ∧
    johnsonWeightedW 131071 agreement 512 703 = 7621349090080 ∧
    johnsonWeightedR 512 703 = 131328 ∧ johnsonWeightedT 512 703 = 22369536 := by
  have ⟨hN, hW⟩ := moment_values (512 * agreement) 131071 703 32524551840 7621349090080
    (by decide) (by decide) (by decide)
  have ⟨hR, hT⟩ := moment_values 512 1 511 131328 22369536 (by decide) (by decide) (by decide)
  have hu : johnsonWeightedU 512 703 = 511 := by decide
  refine ⟨hN, hW, ?_, ?_⟩
  · simpa only [johnsonWeightedR, hu, one_mul] using hR
  · simpa only [johnsonWeightedT, hu, one_mul] using hT

private theorem large_moments :
    johnsonWeightedN 131071 agreement 2048 2815 = 519839185536 ∧
    johnsonWeightedW 131071 agreement 2048 2815 = 487767215844480 ∧
    johnsonWeightedR 2048 2815 = 2098176 ∧ johnsonWeightedT 2048 2815 = 1431655424 := by
  have ⟨hN, hW⟩ := moment_values (2048 * agreement) 131071 2815 519839185536 487767215844480
    (by decide) (by decide) (by decide)
  have ⟨hR, hT⟩ := moment_values 2048 1 2047 2098176 1431655424 (by decide) (by decide) (by decide)
  have hu : johnsonWeightedU 2048 2815 = 2047 := by decide
  refine ⟨hN, hW, ?_, ?_⟩
  · simpa only [johnsonWeightedR, hu, one_mul] using hR
  · simpa only [johnsonWeightedT, hu, one_mul] using hT

/-- Clear the single positive denominator before checking the two bank prices. -/
private theorem weighted_price_lt (N D A B H cap : ℕ) (hDA : D < A)
    (hcheck : ((2*B-1)*H)*(A-D) + (N-D)*(H+B+(2*D-1)*H*(2*B-1)) +
      ((N-D-1)*B)*(A-D) < (cap+1)*(A-D)) :
    johnsonWeightedRefinedExceptionCount N D A B H < (cap : ℚ) + 1 := by
  let gap := A - D
  have hg : (0 : ℚ) < gap := by exact_mod_cast Nat.sub_pos_of_lt hDA
  apply (mul_lt_mul_iff_of_pos_right hg).mp
  unfold johnsonWeightedRefinedExceptionCount
  rw [add_mul, add_mul, mul_right_comm (((N - D : ℕ) : ℚ) / gap), div_mul_cancel₀ _ hg.ne']
  exact_mod_cast hcheck

/-- The library computes a sufficient height of at most 36032 for the written small bank. -/
private theorem shortened_small_tight : ShortenedCap 247217 31362997178808 := by
  apply shortened_from_weighted 247217 31362997178808 512 703 36032 (by decide)
  · intro n hn
    refine ⟨by decide, by decide, by decide, ?_, rfl⟩
    rw [small_moments.1, small_moments.2.2.1]
    omega
  · intro n hn
    unfold johnsonWeightedHeight johnsonWeightedHeightInt johnsonWeightedMoment johnsonWeightedSlope
    rw [small_moments.1, small_moments.2.1, small_moments.2.2.1, small_moments.2.2.2]
    change (max (703 : ℤ) ((7621349090080 - (n : ℤ) * 22369536) /
      (32524551840 - (n : ℤ) * 131328))).toNat ≤ 36032
    have hn' : (n : ℤ) ≤ 247217 := by exact_mod_cast hn
    have hden : 0 < (32524551840 - (n : ℤ) * 131328) := by omega
    have hquot : (7621349090080 - (n : ℤ) * 22369536) /
        (32524551840 - (n : ℤ) * 131328) < 36033 :=
      (Int.ediv_lt_iff_lt_mul hden).mpr (by omega)
    omega
  · exact weighted_price_lt _ _ _ _ _ _ (by decide) (by decide)

/-- The library computes a sufficient height of at most 1522809 for the written large bank. -/
private theorem shortened_large_tight : ShortenedCap 247716 5333229977383096 := by
  apply shortened_from_weighted 247716 5333229977383096 2048 2815 1522809 (by decide)
  · intro n hn
    refine ⟨by decide, by decide, by decide, ?_, rfl⟩
    rw [large_moments.1, large_moments.2.2.1]
    omega
  · intro n hn
    unfold johnsonWeightedHeight johnsonWeightedHeightInt johnsonWeightedMoment johnsonWeightedSlope
    rw [large_moments.1, large_moments.2.1, large_moments.2.2.1, large_moments.2.2.2]
    change (max (2815 : ℤ) ((487767215844480 - (n : ℤ) * 1431655424) /
      (519839185536 - (n : ℤ) * 2098176))).toNat ≤ 1522809
    have hn' : (n : ℤ) ≤ 247716 := by exact_mod_cast hn
    have hden : 0 < (519839185536 - (n : ℤ) * 2098176) := by omega
    have hquot : (487767215844480 - (n : ℤ) * 1431655424) /
        (519839185536 - (n : ℤ) * 2098176) < 1522810 :=
      (Int.ediv_lt_iff_lt_mul hden).mpr (by omega)
    omega
  · exact weighted_price_lt _ _ _ _ _ _ (by decide) (by decide)

theorem shortened_small : ShortenedCap 247217 87041886477376 := by
  intro D hD u v Γ hΓ
  exact (shortened_small_tight D hD u v Γ hΓ).trans (by decide)

theorem shortened_large : ShortenedCap 247716 7004463192991142 := by
  intro D hD u v Γ hΓ
  exact (shortened_large_tight D hD u v Γ hΓ).trans (by decide)

end
end P0_1
end PackSource_P0_1Shortened

section PackSource_P0_1Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0_1
noncomputable section

open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark P0
open K1_1 (level_profile sliceDim level_of_profile)
open K1_2 (padding cutoff fixedLimit deletionSize padding_le_eight fixedLimit_le
  RegularPlane ReducedRelation RegularAt planePrice_nonneg)
open private nativeMoments independent_nativeMoments locator_nullity principal_of_one_active from ProximityPrize.SubmissionLower.PortBase

/-- Prepare the original normal labels on a small fixed puncture by paying
for reduced-resultant zeros and graph normalization. -/
def c1 : Prop :=
  ∀ (u : Words), MiddleGuard u → ∀ (T : TwoActive u) (R : Relation T),
    ¬ MovingGCD R → ¬ InvalidLeft R → NormalSaturation R →
    ∀ Γ : Finset K, Γ.Nonempty → BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
      let r := nullity u
      let g := (fixedNodes R).card
      let D := Finset.univ \ fixedNodes R
      g ≤ fixedLimit r →
        ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ extraReserve r g ∧
          ∃ _ : PaddedFamily u D (Γ \ book) r g,
          ∃ Q : ReducedRelation u D (reducedHeight r g),
            ∀ γ ∈ Γ \ book, RegularAt Q γ

/-- All retained labels sharing one deletion union lie in a single child
plane, with the same marked decoders and their exact remaining supports. -/
def c2 : Prop :=
  ∀ (u : Words) (D : Finset I) (Γ : Finset K) (r g : ℕ),
    7 ≤ r → r ≤ 16 → g ≤ fixedLimit r →
    ∀ (F : PaddedFamily u D Γ r g) (Q : ReducedRelation u D (reducedHeight r g)),
      (∀ γ ∈ Γ, RegularAt Q γ) →
      ∀ J ∈ D.powersetCard (deletionSize r), (childSlopes F J).Nonempty →
        RegularPlane u (D \ J) (childRows r) (childErrors r g)
          (childSlopes F J) F.decoder

/- The plane proof only uses the dimension k and symbolic child sizes. -/
private theorem plane_count : K1_2.c4 :=
  K1_2_4.of_children
    (K1_2_4_1.of_children K1_2_4_1_1.proof K1_2_4_1_2.proof)
    K1_2_4_2.proof K1_2_4_3.proof

private theorem main_height_guards (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) :
    1 ≤ reducedHeight r g ∧ reducedHeight r g ≤ childRows r ∧
      1 ≤ cutoff r ∧ cutoff r ≤ childRows r := by
  have hpad := padding_le_eight r
  have hsmall := hg.trans (fixedLimit_le r)
  have hL : L = 49145 := by decide
  have ht : t = 81927 := by decide
  unfold reducedHeight childRows cutoff
  split_ifs <;> omega

/-- The same apolar level argument as the suffix, at positive nullity. -/
private theorem two_active_middle (u : Words) (hm : MiddleGuard u) : Nonempty (TwoActive u) := by
  obtain ⟨a, b, c, hab, hbc, hc, hsum, hdim⟩ := level_profile
    (nativeMoments u) k (independent_nativeMoments u hm.2.2.2.1)
  have hloc := hdim (t + 1) (by decide)
  rw [locator_nullity] at hloc
  have hpos := hm.1
  have hthree : 3 * t < 2 * k + 2 := by decide
  have hinactive : t < c := by omega
  have hb : b ≤ t := by
    by_contra hb
    have hsmall := hdim (a + 1) (by omega)
    exact hm.2.2.2.2.1 (principal_of_one_active u a (by omega) (by omega) (by omega))
  exact ⟨⟨a, b, c, hab, hb, hinactive, hc, hsum, by omega,
    level_of_profile _ _ _ _ _ hdim⟩⟩

private def middle_relation {u : Words} (hm : MiddleGuard u) (T : TwoActive u) :
    Relation T := by
  have hline := Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
  have hH : T.height ≤ 32776 := by
    have h := relation_height_balance T
    have hr := hm.1
    have hL : L = 49145 := by decide
    have ht : t = 81927 := by decide
    omega
  apply Strata.polynomialRelationCertificate_of_nullity_one p (by decide)
    node (u 0) (u 1) node.injective Native.native_domain_fixed
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [Sol1.C64.native_field_card]
  exact (Nat.mul_le_mul_right p (show 2 * T.height + 2 ≤ 2 * 32776 + 2 by omega)).trans_lt
    (by decide)

private theorem normal_count_large_g
    (u : Words) (T : TwoActive u) (R : Relation T) (hsat : NormalSaturation R)
    (Γ : Finset K) (hΓ : BadFamily u Γ) (hn : ∀ γ ∈ Γ, Normal u γ)
    (hg : fixedLimit (nullity u) < (fixedNodes R).card) : Γ.card ≤ 7004463192991142 := by
  classical
  refine shortened_large (Finset.univ \ fixedNodes R) ?_ (u 0) (u 1) Γ ?_
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index]
    unfold fixedLimit at hg
    split_ifs at hg <;> omega
  · intro γ hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
    have sat := hsat γ (hn γ hγ) M
    refine ⟨M.support, ?_, M.agreement, ⟨M.decoder, M.degree, M.hits⟩, M.nonjoint⟩
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hf => sat.fixed_errors i hf (M.hits i hi)⟩

private theorem add_rank_book (u : Words) (Γ : Finset K) (hfirst : firstRank u = L)
    (b : ℕ) (hb : (normalSlopes u Γ).card ≤ b) :
    Γ.card ≤ rankReserve (nullity u) + b := by
  classical
  have hr := rank_book u hfirst Γ
  have hs := Finset.card_filter_add_card_filter_not (s := Γ) (p := Normal u)
  change (normalSlopes u Γ).card + (abnormalSlopes u Γ).card = Γ.card at hs
  omega

private theorem middle_count (hprepare : c1) (hplane : c2)
    (u : Words) (hm : MiddleGuard u) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ prefixCap := by
  classical
  let r := nullity u
  have hr : 7 ≤ r := hm.1
  have hr16 : r ≤ 16 := hm.2.1
  have hfirst := hm.2.2.1
  have hL : L = 49145 := by decide
  have ht : t = 81927 := by decide
  have hrank : rankReserve r ≤ 69836034097153 := by
    have hs : t + 1 - L - r ≤ 32776 := by omega
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left p hs) L).trans (by decide)
  obtain ⟨T⟩ := two_active_middle u hm
  let R := middle_relation hm T
  have hH : T.height < L := by
    have hb := relation_height_balance T
    omega
  have hsat := saturation_of_height u T R hH
  let N := normalSlopes u Γ
  have hN : BadFamily u N := normal_badFamily hΓ
  have hn : ∀ γ ∈ N, Normal u γ := normal_on_normalSlopes
  by_cases hnon : N.Nonempty
  swap
  · have hzero := Finset.not_nonempty_iff_eq_empty.mp hnon
    have hh := add_rank_book u Γ hfirst 0 (by change N.card ≤ 0; rw [hzero]; decide)
    exact hh.trans (hrank.trans (by decide))
  by_cases hmov : MovingGCD R
  · have hc := normal_growth_count hm R hmov hsat N hN hn
    have hh := add_rank_book u Γ hfirst _ hc
    exact hh.trans ((Nat.add_le_add_right hrank _).trans (by decide))
  have hinv : ¬ InvalidLeft R := by
    obtain ⟨γ, hγ⟩ := hnon
    obtain ⟨M⟩ := bad_mark u N hN γ hγ
    exact (hsat γ (hn γ hγ) M).valid
  let g := (fixedNodes R).card
  by_cases hg : g ≤ fixedLimit r
  · obtain ⟨book, hbook, hfee, F, Q, hreg⟩ :=
      hprepare u hm T R hmov hinv hsat N hnon hN hn hg
    obtain ⟨hb, hba, hc, hca⟩ := main_height_guards r g hr hr16 hg
    have hp := padded_count F hr hr16 hg (by
      intro J hJ
      by_cases hJE : (childSlopes F J).Nonempty
      · have h := hplane u _ _ r g hr hr16 hg F Q hreg J hJ hJE
        exact plane_count u _ _ F.decoder (childRows r) (reducedHeight r g) (cutoff r)
          hb hba hc hca h
      · rw [Finset.not_nonempty_iff_eq_empty.mp hJE, Finset.card_empty, Nat.cast_zero]
        exact planePrice_nonneg _ _ _ _)
    have hsplit : Γ.card ≤ rankReserve r + ((N \ book).card + book.card) := by
      rw [Finset.card_sdiff_add_card_eq_card hbook]
      exact add_rank_book u Γ hfirst _ le_rfl
    have hsplit' : (Γ.card : ℚ) ≤ (rankReserve r : ℚ) + ((N \ book).card : ℚ) + book.card := by
      exact_mod_cast (by simpa only [Nat.add_assoc] using hsplit)
    have hfee' : (book.card : ℚ) ≤ extraReserve r g := by exact_mod_cast hfee
    change ((N \ book).card : ℚ) ≤ incidenceRatio r g * nativePlanePrice r g at hp
    have hmiddle : (Γ.card : ℚ) ≤
        (rankReserve r : ℚ) + incidenceRatio r g * nativePlanePrice r g + extraReserve r g :=
      hsplit'.trans (add_le_add (add_le_add le_rfl hp) hfee')
    have hprice := arithmetic_bound r g hr hr16 hg
    push_cast at hprice
    rw [add_right_comm] at hprice
    exact Nat.le_of_lt_succ (by exact_mod_cast (hmiddle.trans_lt hprice))
  · have hc := normal_count_large_g u T R hsat N hN hn (Nat.lt_of_not_ge hg)
    have hh := add_rank_book u Γ hfirst _ hc
    exact hh.trans ((Nat.add_le_add_right hrank _).trans (by decide))

theorem of_children (hprepare : c1) (hplane : c2) : P0.c1 := by
  intro u Γ hu hΓ
  by_cases hd : firstRank u < L
  · exact (deficient_count u Γ hd hΓ).trans (by decide)
  have hfirst := Nat.le_antisymm (firstRank_le u) (Nat.le_of_not_gt hd)
  by_cases hlow : nullity u ≤ 6
  · exact (count_le_six shortened_small u hfirst hlow Γ hΓ).trans (by decide)
  by_cases ht : TypeAtMostOne u
  · exact (type_one_count u ht Γ hΓ).trans (by decide)
  by_cases hp : HomogeneousPrincipal u
  · exact (principal_count u Γ hp hΓ).trans (by decide)
  by_cases hk : ConstantKernel u
  · exact (constant_count u Γ hk hΓ).trans (by decide)
  exact middle_count hprepare hplane u ⟨by omega, hu, hfirst, ht, hp, hk⟩ Γ hΓ

end
end P0_1
end PackSource_P0_1Split

section PackSource_P0_1_1Rank
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace P0_1_1
noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark P0
open K1_2 (JointOn goodSet errorSet)
open K1_2_2 (domain_card)
open private stacked_at_slope node_fixed rank_le_punctured_rank_add_deleted from ProximityPrize.SubmissionLower.Fast076

/-- Keep the original row size and subtract the fixed errors from the column cutoff. -/
def shortenedStack (u : Words) (S : Finset I) :
    Matrix (Fin 2 × Fin L) (Fin (t - S.card + 1)) K[X] :=
  let D := Finset.univ \ S
  stacked p (fun i : D => node i.val) (fun i => u 0 i.val) (fun i => u 1 i.val)
    L (t - S.card)

private theorem evaluated_error_rank {ι : Type} [Fintype ι] [DecidableEq ι]
    (x a b : ι → K) (hx : Function.Injective x)
    (hfix : ∀ c i, Strata.twoConjugations (frobenius K p) c (x i) = x i)
    (γ : K) (P : K[X]) (d : ℕ) (hP : P.degree < k)
    (hsize : k + L + d ≤ Fintype.card ι) (E : Finset ι) (hE : E.card ≤ d)
    (hagree : ∀ i ∉ E, a i + γ * b i = P.eval (x i)) :
    ((stacked p x a b L d).map (evalRingHom γ)).rank =
      (Strata.conjugateErrors (Strata.twoConjugations (frobenius K p))
        (fun i : E => x i.val) (fun i : E => a i.val + γ * b i.val - P.eval (x i.val)) L).rank := by
  rw [stacked_at_slope]
  exact Strata.conjugateHankel_error_rank _ x _ hx hfix P k L d hP hsize E
    (hE.trans (Nat.le_succ _)) hagree

private theorem full_error_rank {u : Words} {γ : K} (M : BadMark u γ)
    (E : Finset I) (hE : E.card ≤ t)
    (hagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    ((twoBlock u).map (evalRingHom γ)).rank =
      (Strata.conjugateErrors (Strata.twoConjugations (frobenius K p))
        (fun i : E => node i.val)
        (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) L).rank :=
  evaluated_error_rank node (u 0) (u 1) node.injective node_fixed γ M.decoder t M.degree
    (by rw [IRSProfile.card_index]; decide) E hE hagree

/-- The normal evaluated rank drops by at most the number of removed error columns. -/
theorem shortened_rank {u : Words} {T : TwoActive u} {R : Relation T}
    (A : Reduction u T R) {γ : K} (M : BadMark u γ) (hn : Normal u γ) :
    L + A.height ≤ GenericLayer.genericRank (shortenedStack u (fixedNodes R)) := by
  classical
  let S := fixedNodes R
  let D := Finset.univ \ S
  let w (i : I) := u 0 i + γ * u 1 i
  let G := goodSet u Finset.univ γ M.decoder
  let E := Finset.univ \ G
  let E' : Finset D := E.subtype (fun i : I => i ∈ D)
  have hE (i : I) : i ∈ E ↔ w i ≠ M.decoder.eval (node i) := by
    simp [E, G, goodSet, w, eq_comm]
  have hS : S ⊆ E := fun i hi => (hE i).2 (A.deleted_error γ hn M i hi).symm
  have hG : agreement ≤ G.card := M.agreement.trans (Finset.card_le_card (by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, M.hits i hi⟩))
  have hEcard : E.card ≤ t := by
    have hc : E.card = blockLength - G.card := domain_card G
    have ht : t = blockLength - agreement := rfl
    omega
  have hDcard : Fintype.card D = blockLength - S.card :=
    (Fintype.card_coe D).trans (domain_card S)
  have hDsize : k + L + (t - S.card) ≤ Fintype.card D := by
    have hs := (Finset.card_le_card hS).trans hEcard
    have hsum : k + L + t = blockLength := by decide
    omega
  have hE'card : E'.card ≤ t - S.card := by
    have hfilter : E.filter (fun i : I => i ∈ D) = E \ S := by
      ext i
      simp [D]
    change (E.subtype (fun i : I => i ∈ D)).card ≤ _
    rw [Finset.card_subtype, hfilter, Finset.card_sdiff_of_subset hS]
    exact Nat.sub_le_sub_right hEcard _
  have hagree (i : I) (hi : i ∉ E) : w i = M.decoder.eval (node i) :=
    not_not.mp (fun hne => hi ((hE i).2 hne))
  have hagree' (i : D) (hi : i ∉ E') : w i.val = M.decoder.eval (node i.val) :=
    hagree i.val (fun he => hi (Finset.mem_subtype.mpr he))
  let σ := Strata.twoConjugations (frobenius K p)
  let x (i : D) := node i.val
  let B := Strata.conjugateErrors σ (fun i : E => node i.val)
    (fun i : E => w i.val - M.decoder.eval (node i.val)) L
  let B' := Strata.conjugateErrors σ (fun i : E' => x i.val)
    (fun i : E' => w i.val.val - M.decoder.eval (x i.val)) L
  have hfull : ((twoBlock u).map (evalRingHom γ)).rank = B.rank :=
    full_error_rank M E hEcard hagree
  have hshort : ((shortenedStack u S).map (evalRingHom γ)).rank = B'.rank :=
    evaluated_error_rank x (fun i : D => u 0 i.val) (fun i : D => u 1 i.val)
      (node.injective.comp Subtype.val_injective) (fun b i => node_fixed b i.val)
      γ M.decoder (t - S.card) M.degree hDsize E' hE'card hagree'
  have hD (i : I) : i ∈ D ↔ i ∉ S := by simp [D]
  have hrank : B.rank ≤ B'.rank + S.card :=
    rank_le_punctured_rank_add_deleted D E S hD hS B
  have hnormal : ((twoBlock u).map (evalRingHom γ)).rank = L + T.height := by
    rw [show ((twoBlock u).map (evalRingHom γ)).rank = stackRank u from hn, actual_stackRank]
    have hbal := relation_height_balance T
    omega
  have hspecial := K1_2_3.rank_ge_specialization (shortenedStack u S)
    (evalRingHom γ) (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
  change ((shortenedStack u S).map (evalRingHom γ)).rank ≤
    GenericLayer.genericRank (shortenedStack u S) at hspecial
  rw [hshort] at hspecial
  rw [← hfull, hnormal] at hrank
  have hheight : A.height + S.card = T.height := A.height_eq
  change L + A.height ≤ GenericLayer.genericRank (shortenedStack u S)
  omega

private theorem mark_counts {u : Words} {γ : K} (M : BadMark u γ)
    (hγ : Normal u γ) {S : Finset I}
    (hfixed : ∀ i ∈ S, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i) :
    let D := Finset.univ \ S
    let G := goodSet u D γ M.decoder
    let s := G.card - agreement
    s ≤ nullity u - 1 ∧ G.card = agreement + s ∧
      (errorSet u D γ M.decoder).card = t - S.card - s ∧ ¬ JointOn u G := by
  classical
  dsimp only
  let D := Finset.univ \ S
  let G := goodSet u D γ M.decoder
  let E := Finset.univ \ G
  have hsupport : M.support ⊆ G := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => hfixed i hs (M.hits i hi)⟩, M.hits i hi⟩
  have hlow := M.agreement.trans (Finset.card_le_card hsupport)
  have hGD : G ⊆ D := Finset.filter_subset _ _
  have hGle := Finset.card_le_card hGD
  have hD : D.card = blockLength - S.card := domain_card S
  have hE : E.card = blockLength - G.card := domain_card G
  have ht : t = blockLength - agreement := rfl
  have hEt : E.card ≤ t := by omega
  have hEg : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    intro i hi
    by_contra hne
    apply hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hG =>
      hne (Finset.mem_filter.mp hG).2.symm⟩
  have hrank : stackRank u ≤ E.card := by
    rw [← (show ((twoBlock u).map (evalRingHom γ)).rank = stackRank u from hγ),
      full_error_rank M E hEt hEg, ← Fintype.card_coe E]
    exact Matrix.rank_le_card_width _
  have hrankBound : stackRank u + nullity u = t + 1 := by
    simpa only [stackRank, nullity, Fintype.card_fin] using GenericLayer.rank_add_nullity (twoBlock u)
  have herror : (errorSet u D γ M.decoder).card = D.card - G.card :=
    Finset.card_sdiff_of_subset hGD
  change G.card - agreement ≤ nullity u - 1 ∧ G.card = agreement + (G.card - agreement) ∧
    (errorSet u D γ M.decoder).card = t - S.card - (G.card - agreement) ∧ ¬ JointOn u G
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro hjoint
  apply M.nonjoint
  obtain ⟨⟨P, hP, hPval⟩, ⟨Q, hQ, hQval⟩⟩ := hjoint
  exact ⟨⟨P, hP, fun i hi => hPval i (hsupport hi)⟩,
    ⟨Q, hQ, fun i hi => hQval i (hsupport hi)⟩⟩

/-- Choose genuine decoders and retain their full hit sets on the puncture. -/
theorem paddedFamily {u : Words} {T : TwoActive u} {R : Relation T}
    (hsat : NormalSaturation R) (Γ : Finset K) (hbad : BadFamily u Γ)
    (hn : ∀ γ ∈ Γ, Normal u γ) :
    Nonempty (P0_1.PaddedFamily u (Finset.univ \ fixedNodes R) Γ
      (nullity u) (fixedNodes R).card) := by
  classical
  let D := Finset.univ \ fixedNodes R
  let M (γ : K) (hγ : γ ∈ Γ) : BadMark u γ :=
    Classical.choice (bad_mark u Γ hbad γ hγ)
  let P (γ : K) : K[X] := if hγ : γ ∈ Γ then (M γ hγ).decoder else 0
  refine ⟨⟨P, fun γ => (goodSet u D γ (P γ)).card - agreement, domain_card _, ?_, ?_⟩⟩
  · intro γ hγ
    simpa only [P, dite_eq_left hγ] using (M γ hγ).degree
  · intro γ hγ
    have h := mark_counts (M γ hγ) (hn γ hγ) (hsat γ (hn γ hγ) (M γ hγ)).fixed_errors
    simpa only [P, dite_eq_left hγ, D] using h

end
end P0_1_1
end PackSource_P0_1_1Rank

section PackSource_P0_4Reduction
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

namespace P0_4

noncomputable section

open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark

open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective
  lift_locator_dvd coprime_after_factor)
open private certificate_output_zero from ProximityPrize.SubmissionLower.Fast068

private theorem eval_liftX (f : K[X]) (x : K) : (liftX f).eval (C x) = C (f.eval x) :=
  K1_8.eval_liftX f x

private theorem mem_fixed_iff {u : Words} {T : TwoActive u} (R : Relation T) (i : I) :
    i ∈ fixedNodes R ↔ (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0 := by
  classical
  simp [fixedNodes]

private def constantsInFrac : K →+* Frac :=
  K1_8.seedInclusion.comp Polynomial.C

private theorem extend_liftX (G : K[X]) :
    extendSeed (liftX G) = G.map constantsInFrac :=
  Polynomial.map_map Polynomial.C seedInclusion G

private theorem fixed_case_maximal {u : Words} {T : TwoActive u} (R : Relation T)
    (hi : ¬ InvalidLeft R) (hf : FixedLeftGCD R) :
    ∀ H : Frac[X], H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
      H ∣ extendSeed (liftX (locator node (fixedNodes R))) := by
  classical
  obtain ⟨g, hg, hgu, hgv, hgmax⟩ := hf
  change g.map constantsInFrac ≠ 0 at hg
  change g.map constantsInFrac ∣ _ at hgu hgv
  change ∀ H : Frac[X], H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
    H ∣ g.map constantsInFrac at hgmax
  have hg0 : g ≠ 0 := by
    intro hz
    exact hg (by rw [hz, Polynomial.map_zero])
  let g₀ := g * C g.leadingCoeff⁻¹
  have hm : g₀.Monic := monic_mul_leadingCoeff_inv hg0
  have hnorm (P : Frac[X]) (hd : g.map constantsInFrac ∣ P) :
      g₀.map constantsInFrac ∣ P := by
    apply ((Polynomial.map_dvd_map' constantsInFrac).mpr ?_).trans hd
    exact (dvd_mul_leadingCoeff_inv hg0).mp dvd_rfl
  have hlift (P : Bivar) (hd : g.map constantsInFrac ∣ extendSeed P) :
      liftX g₀ ∣ P := by
    apply (Polynomial.map_dvd_map seedInclusion seedInclusion_injective (hm.map Polynomial.C)).mp
    change extendSeed (liftX g₀) ∣ extendSeed P
    rw [extend_liftX]
    exact hnorm _ hd
  have hu := hlift _ hgu
  have hv := hlift _ hgv
  have hdom : g₀ ∣ locator node Finset.univ := by
    by_contra h
    exact hi (Or.inr ⟨g₀, hm.ne_zero, hu, hv, h⟩)
  obtain ⟨S, _, _, t, ht, hS⟩ :=
    Strata.split_divisor_locator_factor node IRSProfile.domain.injective Finset.univ g₀ hm.ne_zero hdom
  have hsub : S ⊆ fixedNodes R := by
    intro i his
    have hz : g₀.eval (node i) = 0 := by
      rw [hS, eval_smul, locator_eval_zero node S i his, smul_zero]
    have hlzero : (liftX g₀).eval (C (node i)) = 0 := by
      rw [eval_liftX, hz, C_0]
    obtain ⟨U, hU⟩ := hu
    obtain ⟨V, hV⟩ := hv
    exact (mem_fixed_iff R i).mpr ⟨by rw [hU, eval_mul, hlzero, zero_mul],
      by rw [hV, eval_mul, hlzero, zero_mul]⟩
  have hg₀dvd : g₀ ∣ locator node (fixedNodes R) := by
    rw [hS, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ht)).mul_left_dvd]
    exact Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _
      (fun i his => locator_eval_zero node _ i (hsub his))
  intro H hU hV
  rw [extend_liftX]
  exact (hgmax H hU hV).trans
    ((Polynomial.map_dvd_map' constantsInFrac).mpr
      ((dvd_mul_right g (C g.leadingCoeff⁻¹)).trans hg₀dvd))

theorem fixed_gcd {u : Words} {T : TwoActive u} (R : Relation T)
    (hu : leftU R ≠ 0) (hm : ¬ MovingGCD R) (hi : ¬ InvalidLeft R) :
    IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R)) := by
  classical
  let S := fixedNodes R
  let Δ := liftX (locator node S)
  let A := extendSeed (leftU R)
  let B := extendSeed (leftV R)
  have hΔ : Δ.Monic := (locator_monic node S).map Polynomial.C
  have hΔ0 : extendSeed Δ ≠ 0 := (hΔ.map seedInclusion).ne_zero
  have hA0 : A ≠ 0 :=
    fun h => hu (extendSeed_injective (h.trans (Polynomial.map_zero _).symm))
  have hΔA : extendSeed Δ ∣ A := by
    exact _root_.map_dvd (Polynomial.mapRingHom seedInclusion)
      (lift_locator_dvd S (leftU R) (fun i h => ((mem_fixed_iff R i).mp h).1))
  have hΔB : extendSeed Δ ∣ B := by
    exact _root_.map_dvd (Polynomial.mapRingHom seedInclusion)
      (lift_locator_dvd S (leftV R) (fun i h => ((mem_fixed_iff R i).mp h).2))
  refine ⟨hΔ0, hΔA, hΔB, ?_⟩
  by_cases hf : FixedLeftGCD R
  · exact fixed_case_maximal R hi hf
  let G := EuclideanDomain.gcd A B
  have hGA : G ∣ A := EuclideanDomain.gcd_dvd_left _ _
  have hGB : G ∣ B := EuclideanDomain.gcd_dvd_right _ _
  have hG : G ≠ 0 := fun hz => hA0 (zero_dvd_iff.mp (hz ▸ hGA))
  have hGd : G.natDegree ≤ S.card := by
    apply Nat.le_of_not_gt
    exact fun h => hm ⟨hf, G, hG, hGA, hGB, h⟩
  have hΔd : (extendSeed Δ).natDegree = S.card := by
    rw [extend_liftX, natDegree_map_eq_of_injective constantsInFrac.injective, locator_natDegree]
  obtain ⟨q, hq⟩ := EuclideanDomain.dvd_gcd hΔA hΔB
  change G = extendSeed Δ * q at hq
  have hq0 : q ≠ 0 := by intro h; exact hG (by rw [hq, h, mul_zero])
  have hd := congrArg Polynomial.natDegree hq
  rw [natDegree_mul hΔ0 hq0, hΔd] at hd
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have hqU : IsUnit q := by
    rw [hqC, isUnit_C, isUnit_iff_ne_zero]
    intro hz
    exact hq0 (by rwa [hz, C_0] at hqC)
  intro H hHA hHB
  have hHG : H ∣ G := EuclideanDomain.dvd_gcd hHA hHB
  rwa [hq, hqU.dvd_mul_right] at hHG

theorem puncture {u : Words} {T : TwoActive u} (R : Relation T)
    (hs : NormalSaturation R) (hw : ∃ γ, Normal u γ ∧ Nonempty (BadMark u γ))
    (hgcd : IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R))) : Nonempty (Reduction u T R) := by
  classical
  obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
  have h := hs γ hγ M
  let B := fixedNodes R
  let G := liftX (locator node B)
  have hG : G.Monic := (locator_monic node B).map Polynomial.C
  have hGd : G.natDegree = B.card := by
    change ((locator node B).map Polynomial.C).natDegree = _
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, locator_natDegree]
  obtain ⟨U, hU⟩ := lift_locator_dvd B (leftU R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).1)
  obtain ⟨V, hV⟩ := lift_locator_dvd B (leftV R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).2)
  obtain ⟨W, hW⟩ := lift_locator_dvd B R.output (fun i hi => by
    have hroot := (mem_fixed_iff R i).mp hi
    exact certificate_output_zero R i hroot.1 hroot.2)
  have hu : U ≠ 0 := by
    intro hz
    apply h.U_ne
    rw [hU, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hv : V ≠ 0 := by
    intro hz
    apply h.V_ne
    rw [hV, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hdeg : max (leftU R).natDegree (leftV R).natDegree = T.height := by
    apply le_antisymm (max_le (R.x_degree 0) (R.x_degree 1))
    exact Nat.le_of_not_gt fun hlt => h.valid (Or.inl hlt)
  have hdu := congrArg Polynomial.natDegree hU
  have hdv := congrArg Polynomial.natDegree hV
  change (leftU R).natDegree = (G * U).natDegree at hdu
  change (leftV R).natDegree = (G * V).natDegree at hdv
  rw [natDegree_mul hG.ne_zero hu, hGd] at hdu
  rw [natDegree_mul hG.ne_zero hv, hGd] at hdv
  let H := max U.natDegree V.natDegree
  have hH : H + B.card = T.height := by
    dsimp [H]
    omega
  have hout : W.degree < (k + H : ℕ) := by
    by_cases hzero : W = 0
    · rw [hzero, degree_zero]
      exact WithBot.bot_lt_coe _
    have hRout : R.output ≠ 0 := by rw [hW]; exact mul_ne_zero hG.ne_zero hzero
    have hd := (natDegree_lt_iff_degree_lt hRout).mpr R.output_degree
    rw [hW] at hd
    change (G * W).natDegree < _ at hd
    rw [natDegree_mul hG.ne_zero hzero, hGd] at hd
    exact (natDegree_lt_iff_degree_lt hzero).mp (by omega)
  have hcop : IsCoprime (extendSeed U) (extendSeed V) := by
    apply coprime_after_factor (extendSeed G) _ _ hgcd.1
      (fun hz => hu (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm)))
    intro Q hqu hqv
    apply hgcd.2.2.2 Q
    · rw [hU, extendSeed, Polynomial.map_mul]
      exact hqu
    · rw [hV, extendSeed, Polynomial.map_mul]
      exact hqv
  exact ⟨⟨U, V, W, H, hH, rfl, hu, hv, hcop, hU, hV, hW, hout,
    fun γ hn M => (hs γ hn M).fixed_errors⟩⟩

end
end P0_4
end PackSource_P0_4Reduction

section PackSource_P0_4Exponent
set_option autoImplicit true
set_option maxRecDepth 12000

namespace P0_4

noncomputable section

open Polynomial P0

private theorem threeUAt_eq (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    threeUAt q a β = K1_8.threeUAt q a β := by
  delta threeUAt K1_8.threeUAt P0.liftX K1.liftX P0.seed K1.seed P0.twist K1.twist P0.p K1.p
    P0.Bivar K1.Bivar P0.K K1.K
  rfl

private theorem relationOnAt_eq (q : ℕ) (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOnAt q u S U V W = K1_8.relationOnAt q u S U V W := by
  delta relationOnAt K1_8.relationOnAt P0.node K1.node P0.Words K1.Words P0.I K1.I
    P0.Bivar K1.Bivar P0.K K1.K
  rfl

private theorem columnRankAt_eq (q : ℕ) (U V : Bivar) :
    columnRankAt q U V = K1_8.columnRankAt q U V := by
  delta columnRankAt K1_8.columnRankAt P0.seed K1.seed P0.extendSeed K1.extendSeed
    P0.Bivar K1.Bivar P0.Frac K1.Frac P0.K K1.K
  rfl

open private K1_8.threeUAt_native from ProximityPrize.SubmissionLower.Fast068

private theorem native_threeU :
    threeUAt P0.p = (P0.threeU : K[X] → (Fin 2 → K[X]) → Bivar) := by
  unfold threeUAt P0.threeU
  rfl

theorem threeU_eq (a : K[X]) (β : Fin 2 → K[X]) :
    P0.threeU a β = K1.threeU a β := by
  calc
    P0.threeU a β = threeUAt P0.p a β := congrFun (congrFun native_threeU.symm a) β
    _ = K1_8.threeUAt P0.p a β := threeUAt_eq P0.p a β
    _ = K1_8.threeUAt K1.p a β := congrArg (fun q => K1_8.threeUAt q a β) (show P0.p = K1.p from rfl)
    _ = K1.threeU a β := congrFun (congrFun K1_8.threeUAt_native a) β

theorem relationOn_eq (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOn u S U V W = K1_8.relationOnAt K1.p u S U V W := by
  calc
    _ = relationOnAt P0.p u S U V W := by delta P0.relationOn relationOnAt; rfl
    _ = K1_8.relationOnAt P0.p u S U V W := relationOnAt_eq P0.p u S U V W
    _ = K1_8.relationOnAt K1.p u S U V W :=
      congrArg (fun q => K1_8.relationOnAt q u S U V W) (show P0.p = K1.p from rfl)

theorem columnRank_eq (U V : Bivar) : columnRank U V = K1.columnRank U V := by
  calc
    _ = columnRankAt P0.p U V := by delta P0.columnRank columnRankAt; rfl
    _ = K1_8.columnRankAt P0.p U V := columnRankAt_eq P0.p U V
    _ = K1_8.columnRankAt K1.p U V := congrArg (fun q => K1_8.columnRankAt q U V) (show P0.p = K1.p from rfl)
    _ = _ := by delta K1_8.columnRankAt K1.columnRank; rfl

end
end P0_4
end PackSource_P0_4Exponent

section PackSource_P0_4RankThree
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace P0_4

noncomputable section

open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark

open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective extendSeedHom AmplitudeDirection)
open private transfer_at from ProximityPrize.SubmissionLower.Fast068
open private threeU_height threeV_height common_multiplier multiplier_degree_zero
  seed_scalar_coeff descend_scalar proportional_amplitudes rescale_threeU from ProximityPrize.SubmissionLower.Fast068

private theorem sameDirection_eq (U V P Q : Bivar) :
    sameDirection U V P Q = K1.sameDirection U V P Q := by
  delta P0.sameDirection K1.sameDirection
  rfl

private theorem threeV_eq (b : K[X]) (α : Fin 2 → K[X]) :
    threeV b α = K1.threeV b α := by
  delta P0.threeV K1.threeV P0.liftX K1.liftX P0.seed K1.seed
  rfl

private theorem reduced_scaled_relation {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (e : K[X]) :
    relationOn u (fixedNodes R) (C e * D.U) (C e * D.V) (C e * D.output) := by
  let G := liftX (locator node (fixedNodes R))
  have hG : ∀ i ∉ fixedNodes R, G.eval (C (node i)) ≠ 0 := by
    intro i hi
    change (K1.liftX (locator node (fixedNodes R))).eval (C (node i)) ≠ 0
    rw [K1_8.eval_liftX, C_ne_zero]
    exact fun hz => hi ((Principal.locator_eval_zero_iff node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  rw [relationOn_eq]
  exact @transfer_at u K1.p k T.height R (fixedNodes R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e

/-- A bounded canonical direction differs from the reduced relation by a
polynomial in the seed alone. The Bezout identity comes from the original
seed-primitive certificate, before the fixed locator was removed. -/
private theorem seed_multiplier {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ e : K[X], P = C e * D.U ∧ Q = C e * D.V := by
  have hext (F : Bivar) : (extendSeedHom F).natDegree = F.natDegree :=
    natDegree_map_eq_of_injective seedInclusion_injective F
  have hne (F : Bivar) (hF : F ≠ 0) : extendSeedHom F ≠ 0 :=
    fun hz => hF (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm))
  have hxy : extendSeedHom D.U * extendSeedHom Q = extendSeedHom D.V * extendSeedHom P := by
    have h := congrArg extendSeedHom hcross
    simpa only [map_mul] using h
  have hcop : IsCoprime (extendSeedHom D.U) (extendSeedHom D.V) := D.coprime
  obtain ⟨E, heP, heQ⟩ := common_multiplier hcop hxy
  have hEd := multiplier_degree_zero (hne _ D.U_ne) (hne _ D.V_ne) heP heQ
    (by simpa only [hext] using D.max_degree)
    (by simpa only [hext] using hp) (by simpa only [hext] using hq)
  let s := E.coeff 0
  have hE : E = C s := eq_C_of_natDegree_eq_zero hEd
  rw [hE] at heP heQ
  let G := liftX (locator node (fixedNodes R))
  have hLeftU : extendSeedHom (G * P) = C s * extendSeedHom (leftU R) := by
    rw [D.U_factor]
    change extendSeedHom (G * P) = C s * extendSeedHom (G * D.U)
    rw [map_mul, map_mul, heP]
    ac_rfl
  have hLeftV : extendSeedHom (G * Q) = C s * extendSeedHom (leftV R) := by
    rw [D.V_factor]
    change extendSeedHom (G * Q) = C s * extendSeedHom (G * D.V)
    rw [map_mul, map_mul, heQ]
    ac_rfl
  let F : Fin 2 → Bivar := ![G * P, G * Q]
  let A : Fin 2 × Fin (T.height + 1) → K[X] :=
    fun j => (F j.1).coeff j.2.val
  have hA : ∀ j, seedInclusion (A j) = s * seedInclusion (R.coefficients j) := by
    rintro ⟨i, j⟩
    fin_cases i
    · have hc := seed_scalar_coeff j.val hLeftU
      rw [leftU, Principal.assemble_coeff] at hc
      exact hc
    · have hc := seed_scalar_coeff j.val hLeftV
      rw [leftV, Principal.assemble_coeff] at hc
      exact hc
  obtain ⟨e, he⟩ := descend_scalar R.coefficients A R.primitive s hA
  have hmapC : extendSeedHom (C e) = C s := by
    change (C e).map seedInclusion = C s
    rw [Polynomial.map_C, he]
  refine ⟨e, extendSeed_injective ?_, extendSeed_injective ?_⟩
  · change extendSeedHom P = extendSeedHom (C e * D.U)
    rw [map_mul, hmapC, heP]
  · change extendSeedHom Q = extendSeedHom (C e * D.V)
    rw [map_mul, hmapC, heQ]

private theorem canonical_output {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ W : Bivar, W.degree < (k + D.height : ℕ) ∧ relationOn u (fixedNodes R) P Q W := by
  obtain ⟨e, rfl, rfl⟩ := seed_multiplier D P Q hcross hp hq
  refine ⟨C e * D.output, ?_, ?_⟩
  · have hdeg : (C e * D.output).degree ≤ D.output.degree := by
      simpa only [smul_eq_C_mul] using degree_smul_le e D.output
    exact hdeg.trans_lt D.output_degree
  · exact reduced_scaled_relation D e

theorem rank_three_branch {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (hr : columnRank D.U D.V = 3) (S : AmplitudeDirection D.U D.V)
    (ha : S.a.natDegree + amplitudeDegree (S.β 0) (S.β 1) ≤ D.height)
    (hb : S.b.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height) :
    ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B := by
  have hdir : sameDirection D.U D.V (threeU S.a S.β) (threeV S.b S.α) := by
    rw [threeU_eq, threeV_eq, sameDirection_eq]
    exact S.direction
  have hUdeg : (threeU S.a S.β).natDegree ≤ D.height := by
    rw [threeU_eq]
    exact (threeU_height _ _).trans ha
  have hVdeg : (threeV S.b S.α).natDegree ≤ D.height := by
    rw [threeV_eq]
    exact (threeV_height _ _).trans hb
  obtain ⟨W, hW, hnodes⟩ := canonical_output D _ _ hdir hUdeg hVdeg
  by_cases hd : S.α 0 * S.β 1 - S.α 1 * S.β 0 = 0
  · obtain ⟨t, ht, htβ⟩ := proportional_amplitudes S.α_primitive S.β_primitive (sub_eq_zero.mp hd)
    have htσ : twist t ≠ 0 := fun hz => ht (twist.injective (hz.trans (map_zero twist).symm))
    let a := S.a * C (twist t)
    have heq (i : Fin 2) : (S.β i).map twist = C (twist t) * (S.α i).map twist := by
      rw [htβ i, Polynomial.map_mul, Polynomial.map_C]
    have hU : threeU a S.α = threeU S.a S.β :=
      (threeU_eq _ _).trans ((rescale_threeU S.a S.α S.β (twist t) heq).trans (threeU_eq _ _).symm)
    have hdeg (i : Fin 2) : (S.β i).natDegree = (S.α i).natDegree := by
      rw [htβ i, natDegree_C_mul ht]
    have ha' : a.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height := by
      simpa only [a, natDegree_mul_C htσ, amplitudeDegree, hdeg] using ha
    have hdir' : sameDirection D.U D.V (threeU a S.α) (threeV S.b S.α) := by
      rw [hU]
      exact hdir
    have hn : relationOn u (fixedNodes R) (threeU a S.α) (threeV S.b S.α) W := by
      rw [hU]
      exact hnodes
    exact ⟨⟨hr, S.α, S.α, a, S.b, mul_ne_zero S.a_ne (C_ne_zero.mpr htσ), S.b_ne,
      S.α_primitive, S.α_primitive, ha', hb, hdir', W, hW, hn⟩, Or.inr rfl⟩
  · exact ⟨⟨hr, S.α, S.β, S.a, S.b, S.a_ne, S.b_ne,
      S.α_primitive, S.β_primitive, ha, hb, hdir, W, hW, hnodes⟩, Or.inl hd⟩

end
end P0_4
end PackSource_P0_4RankThree

section PackSource_P0_1_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace P0_1_1
noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark P0 P0_1
open K1_2 (ReducedRelation fixedLimit_le)
open K1_2_2 (domain_card resultant_book)
open K1_6 (shifts pairCoordinates)
open private shifts_annihilate restricted_nodes native_relation from ProximityPrize.SubmissionLower.Fast076
open private shifted_pair_height from ProximityPrize.SubmissionLower.Fast076
open P0_4 (reduced_scaled_relation)

private def pair {u : Words} {T : TwoActive u} {R : Relation T} (A : Reduction u T R) :
    Fin 2 → Bivar :=
  Fin.cases A.U (fun _ => A.V)

private theorem pair_degree {u : Words} {T : TwoActive u} {R : Relation T}
    (A : Reduction u T R) (b : Fin 2) : (pair A b).natDegree ≤ A.height := by
  fin_cases b
  · exact (le_max_left _ _).trans_eq A.max_degree
  · exact (le_max_right _ _).trans_eq A.max_degree

/-- Multiplication by the fixed locator puts all original coefficients in
the ideal generated by the divided pair. The original certificate is primitive. -/
private theorem pair_primitive {u : Words} {T : TwoActive u} {R : Relation T}
    (A : Reduction u T R) : PrimitiveVector.IsPrimitive (pairCoordinates (pair A) A.height) := by
  let J : Ideal K[X] := Ideal.span (Set.range (pairCoordinates (pair A) A.height))
  let φ := Ideal.Quotient.mk J
  have hzero (b : Fin 2) : (pair A b).map φ = 0 := by
    ext i
    rw [coeff_map, coeff_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    by_cases hi : i < A.height + 1
    · exact Ideal.subset_span (Set.mem_range_self ((b, ⟨i, hi⟩) : Fin 2 × Fin (A.height + 1)))
    · rw [coeff_eq_zero_of_natDegree_lt ((pair_degree A b).trans_lt (by omega))]
      exact J.zero_mem
  have hfactor (b : Fin 2) :
      Principal.assemble (fun j => R.coefficients (b, j)) =
        liftX (locator node (fixedNodes R)) * pair A b := by
    fin_cases b
    · exact A.U_factor
    · exact A.V_factor
  have horig (i : Fin 2 × Fin (T.height + 1)) : R.coefficients i ∈ J := by
    have h := congrArg (Polynomial.map φ) (hfactor i.1)
    rw [Polynomial.map_mul, hzero, mul_zero] at h
    have hc := congrArg (fun P : (K[X] ⧸ J)[X] => P.coeff i.2.val) h
    rw [coeff_map, Principal.assemble_coeff, coeff_zero] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mp hc
  change J = ⊤
  apply top_unique
  rw [← R.primitive]
  exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact horig i)

/-- The reduced all-node identity yields its full complement of left shifts
using the dual weights of the shortened domain. -/
private theorem shortened_shifts {u : Words} {T : TwoActive u} {R : Relation T}
    (A : Reduction u T R) (hH : A.height < L) (hg : (fixedNodes R).card ≤ t) :
    (shifts (pair A) L (L - A.height)).transpose * shortenedStack u (fixedNodes R) = 0 := by
  classical
  let D := Finset.univ \ fixedNodes R
  have hL : A.height + (L - A.height) = L := Nat.add_sub_of_le hH.le
  have hsize : k + (49144 + 1) + (t - (fixedNodes R).card) ≤ Fintype.card D := by
    have hd : Fintype.card D = blockLength - (fixedNodes R).card :=
      (Fintype.card_coe D).trans (domain_card _)
    have hsum : k + (49144 + 1) + t = blockLength := by decide
    omega
  refine shifts_annihilate (F := K) (E := Frac) (ι := D) p
    (fun i => node i.val) (fun i => u 0 i.val) (fun i => u 1 i.val)
    (node.injective.comp Subtype.val_injective)
    (fun i => Native.native_domain_fixed i.val)
    (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
    k A.height 49144 _ _ hL hsize (pair A) A.output (pair_degree A) A.output_degree ?_
  apply restricted_nodes p (u := u) (S := fixedNodes R) A.U A.V A.output
  rw [← P0_4.relationOn_eq]
  exact reduced_scaled_relation A 1

theorem proof : P0_1.c1 := by
  classical
  intro u hm T R hmov hinv hsat Γ hnon hbad hn
  dsimp only
  intro hg
  obtain ⟨γ, hγ⟩ := hnon
  obtain ⟨M⟩ := bad_mark u Γ hbad γ hγ
  have hSat := hsat γ (hn γ hγ) M
  have hU : leftU R ≠ 0 := by
    intro hz
    exact hSat.U_ne (by rw [atSlope, hz, Polynomial.map_zero])
  obtain ⟨A⟩ := P0_4.puncture R hsat ⟨γ, hn γ hγ, ⟨M⟩⟩
    (P0_4.fixed_gcd R hU hmov hinv)
  let D := Finset.univ \ fixedNodes R
  let H := reducedHeight (nullity u) (fixedNodes R).card
  have hL : L = 49145 := by decide
  have ht : t = 81927 := by decide
  have hbal := relation_height_balance T
  have hheight : A.height = H := by
    have h := A.height_eq
    dsimp only [H, reducedHeight]
    omega
  have hg' := hg.trans (fixedLimit_le (nullity u))
  have hpos : 0 < H := by
    have hr : nullity u ≤ 16 := hm.2.1
    dsimp only [H, reducedHeight]
    omega
  have hlt : A.height < L := by
    have hr := hm.1
    rw [hheight]
    dsimp only [H, reducedHeight]
    omega
  have hdeleted : Finset.univ \ D = fixedNodes R := by
    ext i
    simp [D]
  have hnodes : K1.relationOn u (Finset.univ \ D) A.U A.V A.output := by
    rw [hdeleted, native_relation, ← P0_4.relationOn_eq]
    have hscaled := reduced_scaled_relation A (1 : K[X])
    rwa [Polynomial.C_1, one_mul, one_mul, one_mul] at hscaled
  let Q : ReducedRelation u D H :=
    ⟨A.U, A.V, A.output, Or.inl A.U_ne, A.max_degree.trans hheight,
      hheight ▸ A.output_degree, hnodes⟩
  have hrank := shortened_rank A M (hn γ hγ)
  have hshift := shortened_shifts A hlt (hg'.trans (by decide))
  have hentry (i : Fin 2 × Fin L) (j : Fin (t - (fixedNodes R).card + 1)) :
      (shortenedStack u (fixedNodes R) i j).natDegree ≤ if i.1 = 0 then 1 else p :=
    stacked_entry_natDegree p (fun i : D => node i.val) (fun i => u 0 i.val)
      (fun i => u 1 i.val) L (t - (fixedNodes R).card) i j
  have hp : 1 ≤ p := by decide
  have hz := shifted_pair_height K L A.height _ p (pair A) (shortenedStack u (fixedNodes R))
    hp hlt (pair_degree A) (pair_primitive A) hrank hshift hentry
  rw [hheight] at hz
  let ζ := (p * L + H) / (L - H)
  have hζU (i : ℕ) : (Q.U.coeff i).natDegree ≤ ζ := hz 0 i
  have hζV (i : ℕ) : (Q.V.coeff i).natDegree ≤ ζ := hz 1 i
  obtain ⟨book, hbsub, hbcard, hreg⟩ :=
    resultant_book Q hpos A.U_ne A.V_ne A.coprime hζU hζV Γ
  obtain ⟨F⟩ := paddedFamily hsat (Γ \ book)
    (fun z hz => hbad z (Finset.mem_sdiff.mp hz).1)
    (fun z hz => hn z (Finset.mem_sdiff.mp hz).1)
  refine ⟨book, hbsub, ?_, F, Q, hreg⟩
  exact hbcard.trans (Nat.le_add_right _ _)

end
end P0_1_1
end PackSource_P0_1_1Proof

section PackSource_P0_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace P0_1_2

open Polynomial Finset Matrix FrobeniusLocator
open P0 (Words I K k p t L blockLength Bivar)
open P0_1 (PaddedFamily childSlopes childRows childErrors reducedHeight)
open K1_2 (padding fixedLimit deletionSize padding_le_eight fixedLimit_le
  goodSet errorSet JointOn mixedChoices planeMatrix onGraph)
open K1_2_3 (evaluated_rank formal_graph_rank_le plane_rank_le rank_ge_specialization)

private theorem child_parameters (r g : ℕ) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) :
    reducedHeight r g ≤ childRows r ∧
      0 < childErrors r g ∧ childErrors r g + 1 < p ∧
      blockLength - g - deletionSize r = k + childRows r + childErrors r g := by
  have hpad := padding_le_eight r
  have hfixed := hg.trans (fixedLimit_le r)
  have hL : L = 49145 := by decide
  have ht : t = 81927 := by decide
  change _ ∧ _ ∧ childErrors r g + 1 < 2130706433 ∧
    262144 - g - deletionSize r = 131072 + childRows r + childErrors r g
  simp only [childErrors, childRows, reducedHeight, deletionSize, hL, ht]
  omega

private theorem child_mark {u : Words} {D : Finset I} {Γ : Finset K} {r g : ℕ}
    (F : PaddedFamily u D Γ r g) (hr : 7 ≤ r) (hr16 : r ≤ 16)
    (hg : g ≤ fixedLimit r) {J : Finset I} {γ : K} (hγ : γ ∈ childSlopes F J) :
    γ ∈ Γ ∧ (F.decoder γ).degree < k ∧
      (errorSet u (D \ J) γ (F.decoder γ)).card = childErrors r g ∧
      ¬ JointOn u (goodSet u (D \ J) γ (F.decoder γ)) := by
  classical
  obtain ⟨hΓ, hJ⟩ := Finset.mem_filter.mp hγ
  obtain ⟨hslack, _, herrors, _⟩ := F.witness γ hΓ
  let S := goodSet u D γ (F.decoder γ)
  let E := errorSet u D γ (F.decoder γ)
  change J ∈ mixedChoices u (r - 1 - F.slack γ + padding r) (F.slack γ + padding r) E S at hJ
  obtain ⟨⟨B, C⟩, hmem, rfl⟩ := Finset.mem_image.mp hJ
  obtain ⟨hB, hC⟩ := Finset.mem_product.mp hmem
  obtain ⟨hBE, hBc⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨hCS, _⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1
  have hbad := (Finset.mem_filter.mp hC).2
  have hgood : goodSet u (D \ (B ∪ C)) γ (F.decoder γ) = S \ C := by
    ext i
    have hBnot (h : i ∈ B) : i ∉ S := (Finset.mem_sdiff.mp (hBE h)).2
    simp only [S, goodSet, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union] at hBnot ⊢
    tauto
  have herr : errorSet u (D \ (B ∪ C)) γ (F.decoder γ) = E \ B := by
    ext i
    have hCs (h : i ∈ C) : i ∈ S := hCS h
    simp only [E, errorSet, S, goodSet, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_union] at hCs ⊢
    tauto
  refine ⟨hΓ, F.degree γ hΓ, ?_, hgood.symm ▸ hbad⟩
  rw [herr, Finset.card_sdiff_of_subset hBE]
  change E.card = _ at herrors
  rw [herrors, hBc]
  have hpad := padding_le_eight r
  have hfixed := hg.trans (fixedLimit_le r)
  have hL : L = 49145 := by decide
  have ht : t = 81927 := by decide
  simp only [childErrors, childRows, reducedHeight, hL, ht]
  omega

/-- One regular plane on the common puncture, with the original decoders. -/
theorem proof : P0_1.c2 := by
  intro u D Γ r g hr hr16 hg F Q hreg J hJ hnon
  obtain ⟨hH, hR, hRp, hsize⟩ := child_parameters r g hr hr16 hg
  obtain ⟨hsub, hJc⟩ := Finset.mem_powersetCard.mp hJ
  have hD : (D \ J).card = k + childRows r + childErrors r g := by
    rw [Finset.card_sdiff_of_subset hsub, F.domain_card, hJc, hsize]
  have hmark := fun γ hγ => child_mark F hr hr16 hg (γ := γ) (J := J) hγ
  have hrank (γ : K) (hγ : γ ∈ childSlopes F J) :=
    evaluated_rank Q (Finset.sdiff_subset : D \ J ⊆ D) hH hR hD γ
      (hreg γ (hmark γ hγ).1) (F.decoder γ) (hmark γ hγ).2.1 (hmark γ hγ).2.2.1
  refine ⟨hD, le_antisymm ?_ ?_, ?_⟩
  · exact plane_rank_le u (D \ J) (childRows r) (childErrors r g) hRp
      (formal_graph_rank_le Q Finset.sdiff_subset hH hD)
  · obtain ⟨γ, hγ⟩ := hnon
    exact (hrank γ hγ).ge.trans
      (rank_ge_specialization _ (onGraph γ) _ (IsFractionRing.injective Bivar (FractionRing Bivar)))
  · intro γ hγ
    obtain ⟨_, hdegree, hE, hbad⟩ := hmark γ hγ
    exact ⟨hdegree, hE, hbad, hrank γ hγ⟩

end P0_1_2
end PackSource_P0_1_2Proof

section PackSource_P0_2Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace P0_2

open P0 Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open private certificate_shifts_annihilate_generic from ProximityPrize.SubmissionLower.Fast050
open private lift_common_divisor specialize_factor eval_atSlope root_outside_of_dvd_locator
  common_node_count from ProximityPrize.SubmissionLower.Fast051

/-- Each shift of the generic relation lies in the left kernel of the stacked matrix. -/
private theorem certificate_shifts_annihilate {u : Words} {T : TwoActive u} (R : Relation T)
    (s : ℕ) (hL : T.height + s = L) :
    (K1_6.shifts (fun b => Principal.assemble (fun j => R.coefficients (b, j))) L s).transpose *
      twoBlock u = 0 := by
  have hsize : k + (49144 + 1) + t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  exact certificate_shifts_annihilate_generic p node (u 0) (u 1) IRSProfile.domain.injective
    Native.native_domain_fixed (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
    k T.height 49144 t s hL hsize R _ (fun _ => rfl)

/-- On a saturated label the common divisor retains its degree and has a nonfixed node. -/
private theorem moving_has_new_node {u : Words} {T : TwoActive u} (R : Relation T)
    (hMoving : MovingGCD R) {γ : K} {M : BadMark u γ} (hSat : SaturatedAt R M) :
    ∃ i ∉ fixedNodes R,
      (atSlope (leftU R) γ).eval (node i) = 0 ∧ (atSlope (leftV R) γ).eval (node i) = 0 := by
  classical
  obtain ⟨G, hG, hGU, hGV, hg⟩ := hMoving.2
  obtain ⟨D, hD, hd, hDU, hDV⟩ := lift_common_divisor hG hGU hGV
  obtain ⟨A, hA⟩ := hDU
  obtain ⟨B, hB⟩ := hDV
  obtain ⟨hAU, hAUdeg⟩ := specialize_factor hD hA hSat.U_ne
  obtain ⟨hBV, hBVdeg⟩ := specialize_factor hD hB hSat.V_ne
  change atSlope (leftU R) γ = atSlope D γ * atSlope A γ at hAU
  change atSlope (leftV R) γ = atSlope D γ * atSlope B γ at hBV
  change (atSlope (leftU R) γ).natDegree + D.natDegree ≤
    (leftU R).natDegree + (atSlope D γ).natDegree at hAUdeg
  change (atSlope (leftV R) γ).natDegree + D.natDegree ≤
    (leftV R).natDegree + (atSlope D γ).natDegree at hBVdeg
  have hdeg : D.natDegree ≤ (atSlope D γ).natDegree := by
    have hU := R.x_degree 0
    have hV := R.x_degree 1
    change (leftU R).natDegree ≤ T.height at hU
    change (leftV R).natDegree ≤ T.height at hV
    have hMax := hSat.degree_eq
    rcases le_total (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree with h | h
    · rw [max_eq_right h] at hMax
      omega
    · rw [max_eq_left h] at hMax
      omega
  obtain ⟨errors, _, hGCD⟩ := hSat.gcd_errors
  have hDvd := hGCD.2.2.2 (atSlope D γ) ⟨atSlope A γ, hAU⟩ ⟨atSlope B γ, hBV⟩
  have hCard : (fixedNodes R).card < (atSlope D γ).natDegree := by omega
  obtain ⟨i, hiFixed, hi⟩ := root_outside_of_dvd_locator (F := K) (ι := I)
    node IRSProfile.domain.injective errors (fixedNodes R) (atSlope D γ) hDvd hCard
  exact ⟨i, hiFixed, by rw [hAU, eval_mul, hi, zero_mul], by rw [hBV, eval_mul, hi, zero_mul]⟩

-- Transport the count with symbolic factors so the index type stays unevaluated.
private theorem count_bound {c n n' H b : ℕ}
    (hn : n = n') (hc : c ≤ n * H) (hb : n' * H = b) : c ≤ b :=
  hb ▸ hn ▸ hc

/-- Cover the marked slopes by one nonzero seed polynomial per nonfixed node. -/
private theorem normal_growth_count {u : Words} {T : TwoActive u} (R : Relation T)
    (hHeight : ∀ i, (R.coefficients i).natDegree ≤ 6393160002)
    (hMoving : MovingGCD R) (hSat : NormalSaturation R) (Γ : Finset K)
    (hBad : BadFamily u Γ) (hNormal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ 1675928535564288 := by
  classical
  let U (i : I) := (leftU R).eval (C (node i))
  let V (i : I) := (leftV R).eval (C (node i))
  have hU (i) : (U i).natDegree ≤ 6393160002 := by
    dsimp only [U, leftU]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (0, j)) _
  have hV (i) : (V i).natDegree ≤ 6393160002 := by
    dsimp only [V, leftV]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (1, j)) _
  have hNew (γ : K) (hγ : γ ∈ Γ) :
      ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0 := by
    refine (P0.bad_mark u Γ hBad γ hγ).elim (fun M => ?_)
    obtain ⟨i, hi, hu, hv⟩ := moving_has_new_node R hMoving (hSat γ (hNormal γ hγ) M)
    have hNZ : ¬ (U i = 0 ∧ V i = 0) := by
      simpa only [fixedNodes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact ⟨i, hNZ, (eval_atSlope (leftU R) γ (node i)).symm.trans hu,
      (eval_atSlope (leftV R) γ (node i)).symm.trans hv⟩
  exact count_bound (c := Γ.card) (n := Fintype.card I) (n' := 262144)
    (H := 6393160002) (b := 1675928535564288) IRSProfile.card_index
    (common_node_count U V 6393160002 Γ hU hV hNew) rfl

theorem proof : P0.c2 := by
  intro u front T R moving saturated Γ bad normal
  let P (b : Fin 2) : Bivar := Principal.assemble (fun j => R.coefficients (b, j))
  let s := L - T.height
  have hP : ∀ b, (P b).natDegree ≤ T.height := R.x_degree
  have hBalance := relation_height_balance T
  have hHeight := relation_height_le front T
  change T.height ≤ 32766 at hHeight
  have hsDef : s = 49145 - T.height := rfl
  have hSum : T.height + s = L := by change T.height + s = 49145; omega
  have hs : 16379 ≤ s := by omega
  have hRank : GenericLayer.genericRank (twoBlock u) + s = 2 * L := by
    change stackRank u + s = _
    rw [actual_stackRank u]
    change 49145 + T.height + nullity u = 81928 at hBalance
    change 81928 - nullity u + s = 98290
    omega
  have hCoordinates : K1_6.pairCoordinates P T.height = R.coefficients := by
    funext i
    exact Principal.assemble_coeff (fun j => R.coefficients (i.1, j)) i.2
  have hPrim : PrimitiveVector.IsPrimitive (K1_6.pairCoordinates P T.height) := by
    rw [hCoordinates]
    exact R.primitive
  have hKernel := certificate_shifts_annihilate R s hSum
  obtain ⟨hMinors, H, hH, rows, hRows⟩ :=
    K1_6_1.proof K T.height L s P hSum (by omega) hP hPrim
  have hBound := K1_6_2.proof K L (t + 1) s p (twoBlock u) (K1_6.shifts P L s)
    (by decide) hRank hKernel (stacked_entry_natDegree p node (u 0) (u 1) L t) hMinors rows
  rw [hRows] at hBound
  have hProduct : 16379 * H ≤ s * H := Nat.mul_le_mul_right H hs
  have hCeiling : L * (p + 1) = 104713567698930 := rfl
  rw [hCeiling] at hBound
  have hCap : H ≤ 6393160002 := by omega
  apply normal_growth_count R _ moving saturated Γ bad normal
  intro i
  rw [← hCoordinates]
  exact (hH i.1 i.2.val).trans hCap

end P0_2
end PackSource_P0_2Proof

section PackSource_P0_3Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace P0_3
noncomputable section

open Polynomial Matrix FrobeniusLocator P0
open ProximityPrize.Benchmark

private theorem eval_atSlope (P : Bivar) (a γ : K) :
    (atSlope P γ).eval a = (P.eval (C a)).eval γ := by
  simpa only [atSlope, Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (C a) (p := P))

private theorem atSlope_constant (G : K[X]) (γ : K) :
    atSlope (G.map C) γ = G := by
  rw [atSlope, Polynomial.map_map]
  have h : (Polynomial.evalRingHom γ).comp C = RingHom.id K := by
    ext a
    simp
  rw [h, Polynomial.map_id]

private theorem twoBlock_atSlope (u : Words) (γ : K) :
    ((twoBlock u).map (evalRingHom γ)) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        node (fun i => u 0 i + γ * u 1 i) L t := by
  rw [twoBlock, Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]

private theorem rank_at_normal {u : Words} (T : TwoActive u) {γ : K} (hγ : Normal u γ) :
    ((twoBlock u).map (evalRingHom γ)).rank = L + T.height := by
  change _ = stackRank u at hγ
  rw [hγ, actual_stackRank]
  have h := relation_height_balance T
  omega

/-- The original stack has the same rank as its two evaluated error blocks. -/
private theorem error_rank {u : Words} {γ : K} (M : BadMark u γ)
    (E : Finset I) (hE : E.card ≤ t)
    (hEagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    ((twoBlock u).map (evalRingHom γ)).rank =
      (Strata.errorTwoMatrix (frobenius K p) (fun i : E => node i.val)
        (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) L).rank := by
  have hfix : ∀ b i, Strata.twoConjugations (frobenius K p) b (node i) = node i := by
    intro b i
    fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]
  have h := Strata.conjugateHankel_error_rank
    (Strata.twoConjugations (frobenius K p)) node (fun i => u 0 i + γ * u 1 i)
    IRSProfile.domain.injective hfix M.decoder k L t M.degree
    (by rw [IRSProfile.card_index]; decide) E (hE.trans (Nat.le_succ t)) hEagree
  rw [Strata.conjugateErrors_two] at h
  rw [twoBlock_atSlope]
  exact h

/-- When the distinct common error roots exhaust the gcd degree, their
monic locator has the same divisors as the gcd. -/
private theorem commonGCD_of_roots (U V : K[X]) (hV : V ≠ 0) (S : Finset I)
    (hroots : ∀ i ∈ S, (GCDMonoid.gcd U V).eval (node i) = 0)
    (hcard : S.card = (GCDMonoid.gcd U V).natDegree) :
    IsCommonGCD (locator node S) U V := by
  have hG : GCDMonoid.gcd U V ≠ 0 := gcd_ne_zero_of_right hV
  have hdiv := Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _ hroots
  have hassoc := Polynomial.associated_of_dvd_of_natDegree_le hdiv hG
    (by rw [locator_natDegree, hcard])
  exact ⟨(locator_monic node S).ne_zero, hdiv.trans (gcd_dvd_left U V),
    hdiv.trans (gcd_dvd_right U V), fun H hHU hHV => (dvd_gcd hHU hHV).trans hassoc.dvd'⟩

private theorem lift_dvd_atSlope {P : Bivar} {G : K[X]} (γ : K) (h : G.map C ∣ P) :
    G ∣ atSlope P γ := by
  have h' := map_dvd (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) h
  change atSlope (G.map C) γ ∣ atSlope P γ at h'
  rwa [atSlope_constant] at h'

private theorem valid_of_saturation {u : Words} {T : TwoActive u} (R : Relation T)
    (γ : K) (S : Finset I)
    (hdegree : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree = T.height)
    (hG : IsCommonGCD (locator node S) (atSlope (leftU R) γ) (atSlope (leftV R) γ)) :
    ¬ InvalidLeft R := by
  intro hinvalid
  rcases hinvalid with hlow | ⟨G, _, hGU, hGV, hbad⟩
  · have hle : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree ≤
        max (leftU R).natDegree (leftV R).natDegree :=
      max_le_max Polynomial.natDegree_map_le Polynomial.natDegree_map_le
    omega
  · have hS : locator node S ∣ locator node Finset.univ :=
      ⟨locator node (Finset.univ \ S),
        (Principal.locator_mul_sdiff node S Finset.univ (Finset.subset_univ S)).symm⟩
    exact hbad ((hG.2.2.2 G (lift_dvd_atSlope γ hGU) (lift_dvd_atSlope γ hGV)).trans hS)

theorem proof : P0.c3 := by
  classical
  intro u hfront T R γ hγ M
  let U := atSlope (leftU R) γ
  let V := atSlope (leftV R) γ
  let E : Finset I := Finset.univ.filter (fun i => M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i)
  let e : E → K := fun i => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)
  let x : E → K := fun i => node i.val
  have hEagree (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm h⟩)
  have hEcard : E.card ≤ t := by
    have hsub : E ⊆ Finset.univ \ M.support := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => ?_⟩
      exact (Finset.mem_filter.mp hi).2 (M.hits i hs)
    have h := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      IRSProfile.card_index] at h
    exact h.trans (Nat.sub_le_sub_left M.agreement blockLength)
  have hheight : T.height ≤ heightCap := relation_height_le hfront T
  have hH : T.height < L := hheight.trans_lt (by decide)
  have hfit : k + T.height ≤ M.support.card :=
    ((Nat.add_le_add_left hheight k).trans (by decide : k + heightCap ≤ agreement)).trans
      M.agreement
  have hfix (i : I) : frobenius K p (node i) = node i := Native.native_domain_fixed i
  obtain ⟨hpair, hrel⟩ :=
    Strata.certificate_specializes p node (u 0) (u 1) k T.height R γ
  have hUle : U.natDegree ≤ T.height := hrel.degree_U
  have hVle : V.natDegree ≤ T.height := hrel.degree_V
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have he (i : E) : e i ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp i.property).2)
  have herror (i : E) : U.eval (x i) * e i + V.eval (x i) * frobenius K p (e i) = 0 :=
    Strata.certificate_error_identity p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed k T.height R γ M.support hfit M.decoder M.degree M.hits i.val
  have hrank : (Strata.errorTwoMatrix (frobenius K p) x e L).rank = L + T.height :=
    (error_rank M E hEcard hEagree).symm.trans (rank_at_normal T hγ)
  obtain ⟨hU, hV⟩ := Strata.saturated_coefficients_nonzero (frobenius K p) x e hx U V
    T.height L hUle hVle hpair hH he herror hrank
  let G := GCDMonoid.gcd U V
  let C₀ := (Finset.univ : Finset E).filter (fun i => G.eval (x i) = 0)
  let S := C₀.image (fun i : E => i.val)
  obtain ⟨hC, hsum, _⟩ := Strata.normal_error_three_rank (frobenius K p) x e hx
    (fun i => hfix i.val) U V T.height L hUle hVle hpair hH he herror hrank
  have hmax : max U.natDegree V.natDegree = T.height := by
    obtain ⟨hle, hred⟩ := Strata.gcd_reduction_degrees U V hU hV
    change max (U / G).natDegree (V / G).natDegree + G.natDegree = T.height at hsum
    change G.natDegree ≤ max U.natDegree V.natDegree at hle
    change max (U / G).natDegree (V / G).natDegree =
      max U.natDegree V.natDegree - G.natDegree at hred
    omega
  have hS_card : S.card = G.natDegree :=
    (Finset.card_image_of_injective C₀ Subtype.val_injective).trans hC
  have hS_error (i : I) (hi : i ∈ S) : M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp j.property).2
  have hG : IsCommonGCD (locator node S) U V := by
    apply commonGCD_of_roots U V hV S _ hS_card
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hj).2
  refine ⟨hU, hV, hmax, ⟨S, hS_error, hG⟩, ?_, valid_of_saturation R γ S hmax hG⟩
  intro i hi
  have hzero := (Finset.mem_filter.mp hi).2
  have hu0 : U.eval (node i) = 0 := by
    change (atSlope (leftU R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.1, eval_zero]
  have hv0 : V.eval (node i) = 0 := by
    change (atSlope (leftV R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.2, eval_zero]
  have hdiv : (Polynomial.X : K[X]) - C (node i) ∣ locator node S :=
    hG.2.2.2 _ (dvd_iff_isRoot.mpr hu0) (dvd_iff_isRoot.mpr hv0)
  have hroot : (locator node S).eval (node i) = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero hdiv (by rw [eval_sub, eval_X, eval_C, sub_self])
  exact hS_error i ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective S i).mp hroot)

end
end P0_3
end PackSource_P0_3Proof

section PackSource_P0_4Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 850000

namespace P0_4

noncomputable section

open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark

theorem proof : P0.c4 := by
  intro u hfront T R hmove hinvalid hsat hw
  have hu : leftU R ≠ 0 := by
    obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
    intro hz
    exact (hsat γ hγ M).U_ne (by rw [atSlope, hz, Polynomial.map_zero])
  obtain ⟨D⟩ := puncture R hsat hw (fixed_gcd R hu hmove hinvalid)
  refine ⟨D, ?_⟩
  rcases K1_8.rank_cases D.U D.V D.U_ne D.V_ne with hfour | hthree
  · exact Or.inl ((columnRank_eq _ _).trans hfour)
  · obtain ⟨S⟩ := K1_8_1.proof D.U D.V D.U_ne D.V_ne hthree
    have hsmall : D.height < p - 1 := by
      have hle : D.height ≤ T.height := by
        rw [← D.height_eq]
        exact Nat.le_add_right _ _
      exact (hle.trans (relation_height_le hfront T)).trans_lt (by decide)
    obtain ⟨ha, hb⟩ := K1_8_2.proof D.U D.V D.height D.U_ne D.V_ne D.coprime D.max_degree hsmall S
    exact Or.inr (rank_three_branch D ((columnRank_eq _ _).trans hthree) S ha hb)

end
end P0_4
end PackSource_P0_4Proof

section PackSource_P0_5Polar
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace P0_5

noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k amplitudeDegree)
open K1_9 (K I node twist pencil fold pencil_degree
  seedCoeff crossValue CoefficientIdentities sixNorm_mul sixNorm_ne_zero)

open private seedCoeff_degree from ProximityPrize.SubmissionLower.Fast068

/-- Height bound using only the active-degree hypotheses in this contract. -/
abbrev heightBound : ℕ := 32781

/-- Four seed coefficients after restoring the fixed locator, evaluated bilinearly. -/
structure PolarData (u : Words) where
  a : K[X]
  b : K[X]
  A : Fin 2 → K[X]
  Q : K → K → K[X]
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  b_bound : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  Q_degree : ∀ r s, (Q r s).degree < (k + heightBound : ℕ)
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)

abbrev PolarData.amp {u : Words} (D : PolarData u) := pencil (D.A 0) (D.A 1)

private theorem pow_eq_twist (z : K) : z ^ P0.p = twist z :=
  (frobenius_def P0.p z).symm

private theorem threeUAt_native : threeUAt P0.p = P0.threeU := by
  unfold threeUAt P0.threeU
  rfl

private theorem relationOnAt_native : relationOnAt P0.p = P0.relationOn := by
  unfold relationOnAt P0.relationOn
  rfl

private theorem coefficientsAt (q : ℕ) (hq : 1 < q) (hσ : ∀ z : K, z ^ q = twist z)
    (u : Words) (deleted : Finset I) (a b : K[X]) (A B : Fin 2 → K[X])
    (output : P0.Bivar) (hp : A = B)
    (hn : relationOnAt q u deleted (threeUAt q a B) (P0.threeV b A) output)
    (i : I) (hi : i ∉ deleted) :
    (seedCoeff output 0).eval (node i) = crossValue u a b A i 0 0 ∧
    (seedCoeff output 1).eval (node i) = crossValue u a b A i 0 1 ∧
    (seedCoeff output q).eval (node i) = crossValue u a b A i 1 0 ∧
    (seedCoeff output (q + 1)).eval (node i) = crossValue u a b A i 1 1 := by
  subst B
  exact K1_9.coefficients_at_node u a b A i q hq hσ output (threeUAt q a A)
    (K1_9.eval_first a A i q) (hn i hi).symm

private theorem coefficients {u : Words} {T : P0.TwoActive u} {R : P0.Relation T}
    {D : P0.Reduction u T R} (B : P0.RankThree u T R D) (hp : P0.Parallel B)
    (i : I) (hi : i ∉ P0.fixedNodes R) :
    CoefficientIdentities u B.a B.b B.α B.output i := by
  have hnodes : relationOnAt P0.p u (P0.fixedNodes R) (threeUAt P0.p B.a B.β)
      (P0.threeV B.b B.α) B.output := by
    rw [threeUAt_native, relationOnAt_native]
    exact B.nodes
  exact coefficientsAt P0.p (by decide) pow_eq_twist u (P0.fixedNodes R)
    B.a B.b B.α B.β B.output hp hnodes i hi

-- The node set stays abstract while checking the locator and degree calculations.
private theorem polarData_of_set {u : Words} (S : Finset I) (height : ℕ)
    (a b : K[X]) (A : Fin 2 → K[X]) (output : P0.Bivar)
    (hh : height + S.card ≤ heightBound)
    (hout : output.degree < (k + height : ℕ))
    (hfirst : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hsecond : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hane : a ≠ 0) (hn : K1.sixNorm a ≠ K1.sixNorm b) (hA : IsCoprime (A 0) (A 1))
    (hc : ∀ i ∉ S, CoefficientIdentities u a b A output i) : Nonempty (PolarData u) := by
  classical
  let g := locator node S
  let v (j : ℕ) := g * seedCoeff output j
  have hg : g.natDegree = S.card := locator_natDegree _ _
  have hd (j : ℕ) : (v j).degree < (k + heightBound : ℕ) := by
    have h := Strata.degree_mul_lt_add g (seedCoeff output j) g.natDegree
      (k + height) le_rfl (seedCoeff_degree _ _ _ hout)
    exact h.trans_le (by exact_mod_cast (show k + height + g.natDegree ≤ k + heightBound by omega))
  have ha : (g * a).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := a)
    omega
  have hb : (g * b).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := b)
    omega
  have hgn : g ≠ 0 := (locator_monic node S).ne_zero
  refine ⟨⟨g * a, g * b, A,
    fun r s => pencil (pencil (v 0) (v 1) s) (pencil (v K1.p) (v (K1.p + 1)) s) (twist r),
    mul_ne_zero hgn hane, ?_, hA, ha, hb, ?_, ?_⟩⟩
  · intro h
    rw [sixNorm_mul, sixNorm_mul] at h
    exact hn (mul_left_cancel₀ (sixNorm_ne_zero hgn) h)
  · intro r s
    exact pencil_degree (pencil_degree (hd 0) (hd 1) s)
      (pencil_degree (hd K1.p) (hd (K1.p + 1)) s) _
  · intro r s i
    by_cases hi : i ∈ S
    · have hz : g.eval (node i) = 0 := locator_eval_zero node _ i hi
      simp only [pencil, v, eval_mul, eval_add, eval_C, hz, zero_mul, mul_zero, add_zero, sub_zero]
    obtain ⟨h0, h1, h2, h3⟩ := hc i hi
    simp only [pencil, fold, v, eval_add, eval_mul, eval_C, h0, h1, h2, h3,
      crossValue, map_add, map_mul]
    ring

theorem polarData_of_parallel {u : Words} {T : P0.TwoActive u} {R : P0.Relation T}
    {D : P0.Reduction u T R} (B : P0.RankThree u T R D)
    (hp : P0.Parallel B) (hn : ¬ P0.UnitNorm B) : Nonempty (PolarData u) := by
  have hh : D.height + (P0.fixedNodes R).card ≤ heightBound := by
    rw [D.height_eq, P0.TwoActive.height]
    have h₁ := T.ab
    have h₂ := T.active
    have h₃ := T.degreeSum
    dsimp only [P0.t, P0.blockLength, P0.agreement, k, heightBound] at h₂ h₃ ⊢
    omega
  have hfirst := (congrArg (fun A : Fin 2 → K[X] =>
    B.a.natDegree + amplitudeDegree (A 0) (A 1) ≤ D.height) hp).mpr B.first_degree
  exact polarData_of_set (P0.fixedNodes R) D.height B.a B.b B.α B.output hh
    B.output_degree hfirst B.second_degree B.a_ne hn B.α_primitive (coefficients B hp)

end
end P0_5
end PackSource_P0_5Polar

section PackSource_P0_5Pencil
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace P0_5
noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark

open P0 (Words k agreement amplitudeDegree)
open K1_9 (K I node twist pencil fold map_eval_node pencil_natDegree pencil_degree
  degree_sub_lt eq_on_nodes sixNorm_mul sixNorm_twist sixNorm_ne_zero)

open private all_card affine_zero residual fold_residual from ProximityPrize.SubmissionLower.Fast068

private theorem amp_natDegree_le {u : Words} (D : PolarData u) (z : K) :
    (D.amp z).natDegree ≤ amplitudeDegree (D.A 0) (D.A 1) :=
  pencil_natDegree ..

private theorem PolarData.amp_nonzero_at {u} (D : PolarData u) {r s : K}
    (hrs : r ≠ s) (i : I) : (D.amp r).eval (node i) ≠ 0 ∨ (D.amp s).eval (node i) ≠ 0 := by
  by_contra! hz
  obtain ⟨hr, hs⟩ := hz
  simp only [PolarData.amp, pencil, eval_add, eval_mul, eval_C] at hr hs
  have hb : (r-s) * (D.A 1).eval (node i) = 0 := by linear_combination hr - hs
  have h1 := (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hrs)
  have h0 : (D.A 0).eval (node i) = 0 := by simpa [h1] using hr
  obtain ⟨P, Q, hPQ⟩ := D.primitive
  have h := congrArg (Polynomial.eval (node i)) hPQ
  simp only [eval_add, eval_mul, h0, h1, mul_zero, add_zero, eval_one, zero_ne_one] at h

private def PolarData.cross {u} (D : PolarData u) (r s : K) (P Q : K[X]) : K[X] :=
  D.a * (D.amp r).map twist * Q - D.b * D.amp s * P.map twist

private theorem PolarData.cross_degree {u} (D : PolarData u) (r s : K)
    {P Q : K[X]} (hP : P.degree < k) (hQ : Q.degree < k) :
    (D.cross r s P Q).degree < (k + heightBound : ℕ) := by
  have hl : (D.a * (D.amp r).map twist).natDegree ≤ heightBound :=
    natDegree_mul_le.trans <|
      (Nat.add_le_add_left (natDegree_map_le.trans (amp_natDegree_le D r)) _).trans D.a_bound
  have hr : (D.b * D.amp s).natDegree ≤ heightBound :=
    natDegree_mul_le.trans <|
      (Nat.add_le_add_left (amp_natDegree_le D s) _).trans D.b_bound
  exact degree_sub_lt
    (Strata.degree_mul_lt_add _ _ heightBound k hl hQ)
    (Strata.degree_mul_lt_add _ _ heightBound k hr (degree_map_le.trans_lt hP))

private theorem PolarData.decoder_identity {u} (D : PolarData u) (z : K)
    (S : Finset I) (P : K[X]) (hS : agreement ≤ S.card) (hP : P.degree < k)
    (hits : ∀ i ∈ S, P.eval (node i) = fold u z i) : D.cross z z P P = D.Q z z := by
  have hcard := (show k + heightBound ≤ agreement by decide).trans hS
  have hb : ((k + heightBound : ℕ) : WithBot ℕ) ≤ S.card := by exact_mod_cast hcard
  apply eq_on_nodes S _ _ ((D.cross_degree z z hP hP).trans_le hb) ((D.Q_degree z z).trans_le hb)
  intro i hi
  simp only [PolarData.cross, eval_sub, eval_mul, map_eval_node, hits i hi, D.nodes]

private def PolarData.subtract {u} (D : PolarData u) (P Q : K[X])
    (hP : P.degree < k) (hQ : Q.degree < k) : PolarData (residual u P Q) where
  a := D.a
  b := D.b
  A := D.A
  Q r s := D.Q r s - D.cross r s (pencil P Q r) (pencil P Q s)
  a_ne := D.a_ne
  norms_ne := D.norms_ne
  primitive := D.primitive
  a_bound := D.a_bound
  b_bound := D.b_bound
  Q_degree r s := degree_sub_lt (D.Q_degree r s)
    (D.cross_degree r s (pencil_degree hP hQ r) (pencil_degree hP hQ s))
  nodes r s i := by
    simp only [eval_sub, D.nodes, PolarData.cross, eval_mul, map_eval_node, fold_residual, map_sub]
    ring

/-- Two zero diagonal entries force an off-diagonal entry to vanish by the cyclic norm. -/
private theorem PolarData.offdiag_zero {u} (D : PolarData u) {r s : K}
    (hr : D.amp r ≠ 0) (hs : D.amp s ≠ 0) (hrr : D.Q r r = 0) (hss : D.Q s s = 0) :
    D.Q r s = 0 := by
  let E := D.amp s * (D.amp r).map twist
  -- Each scalar shares its height budget with one of the two amplitudes in E.
  let d := amplitudeDegree (D.A 0) (D.A 1)
  have hd : d ≤ heightBound := (Nat.le_add_left _ _).trans D.a_bound
  have hE : E.natDegree ≤ d + d := natDegree_mul_le.trans
    (Nat.add_le_add (amp_natDegree_le D s) (natDegree_map_le.trans (amp_natDegree_le D r)))
  have hl : (D.b * E).natDegree ≤ heightBound + heightBound := by
    have hb : D.b.natDegree + d ≤ heightBound := D.b_bound
    exact natDegree_mul_le.trans (by omega)
  have ht : (D.a.map twist * E.map twist).natDegree ≤ heightBound + heightBound := by
    have ha : D.a.natDegree + d ≤ heightBound := D.a_bound
    exact natDegree_mul_le.trans
      ((Nat.add_le_add natDegree_map_le natDegree_map_le).trans (by omega))
  have hcut : ((k + heightBound + (heightBound + heightBound) : ℕ) : WithBot ℕ) ≤
      (Finset.univ : Finset I).card := by
    rw [all_card]
    exact_mod_cast (show k + heightBound + (heightBound + heightBound) ≤ 262144 by decide)
  have heq : D.b * E * (D.Q r s).map twist = D.a.map twist * E.map twist * D.Q r s := by
    apply eq_on_nodes Finset.univ _ _
      ((Strata.degree_mul_lt_add _ _ _ _ hl (degree_map_le.trans_lt (D.Q_degree r s))).trans_le hcut)
      ((Strata.degree_mul_lt_add _ _ _ _ ht (D.Q_degree r s)).trans_le hcut)
    intro i _
    have h₁ := (D.nodes r r i).symm
    have h₂ := (D.nodes s s i).symm
    rw [hrr, eval_zero] at h₁
    rw [hss, eval_zero] at h₂
    have hσ := congrArg (fun x => twist x) h₁
    simp only [map_sub, map_mul, map_zero] at hσ
    simp only [E, eval_mul, map_eval_node, D.nodes, map_sub, map_mul]
    linear_combination
      -(twist (D.a.eval (node i))) * twist (twist ((D.amp r).eval (node i))) *
        twist ((D.amp r).eval (node i)) * h₂ +
      D.b.eval (node i) * (D.amp s).eval (node i) * twist ((D.amp s).eval (node i)) * hσ
  by_contra hne
  have hn : E ≠ 0 := mul_ne_zero hs ((Polynomial.map_ne_zero_iff twist.injective).mpr hr)
  have hN := congrArg K1.sixNorm heq
  simp only [sixNorm_mul, sixNorm_twist] at hN
  exact D.norms_ne (mul_right_cancel₀ (sixNorm_ne_zero hn)
    (mul_right_cancel₀ (sixNorm_ne_zero hne) hN.symm))

private theorem PolarData.zero_of_diagonal_zeros {u} (D : PolarData u) {r s : K}
    (hrs : r ≠ s) (hr : D.amp r ≠ 0) (hs : D.amp s ≠ 0)
    (hrr : D.Q r r = 0) (hss : D.Q s s = 0) (y z : K) : D.Q y z = 0 := by
  have hrs' := D.offdiag_zero hr hs hrr hss
  have hsr' := D.offdiag_zero hs hr hss hrr
  apply eq_on_nodes Finset.univ _ _ (by rw [all_card]; exact (D.Q_degree y z).trans_le (by exact_mod_cast (show k + heightBound ≤ 262144 by decide)))
    (by rw [all_card, degree_zero]; exact WithBot.bot_lt_coe 262144)
  intro i _
  let f (r s : K) := (D.Q r s).eval (node i)
  have right (x γ : K) : f x γ = f x 0 + id γ * (f x 1 - f x 0) := by
    simp only [f, D.nodes, pencil, fold, eval_add, eval_mul, eval_C, id_eq]
    ring
  have left (x γ : K) : f γ x = f 0 x + twist γ * (f 1 x - f 0 x) := by
    simp only [f, D.nodes, pencil, fold, eval_add, eval_mul, eval_C, map_add, map_mul,
      map_zero, map_one]
    ring
  have h₁ : f r z = 0 := affine_zero (f r) id Function.injective_id hrs (right r)
    (by simp [f, hrr]) (by simp [f, hrs']) z
  have h₂ : f s z = 0 := affine_zero (f s) id Function.injective_id hrs (right s)
    (by simp [f, hsr']) (by simp [f, hss]) z
  simpa only [eval_zero] using affine_zero (fun γ => f γ z) twist twist.injective hrs (left z) h₁ h₂ y

/-- A vanishing polarized relation forces every close decoder to be zero, including
the zero-amplitude case, where enough agreeing nodes survive the zeros of the left scalar. -/
private theorem PolarData.decoder_zero {u} (D : PolarData u) (hQ : ∀ r s, D.Q r s = 0) (z : K)
    (S : Finset I) (P : K[X]) (hS : agreement ≤ S.card) (hP : P.degree < k)
    (hits : ∀ i ∈ S, P.eval (node i) = fold u z i) : P = 0 := by
  classical
  by_cases hz : D.amp z = 0
  · let S' := S.filter (fun i => D.a.eval (node i) ≠ 0)
    let roots := S.filter (fun i => D.a.eval (node i) = 0)
    have hroots : roots.card ≤ D.a.natDegree := by
      rw [← Finset.card_image_of_injective roots node.injective]
      apply Polynomial.card_le_degree_of_subset_roots
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Polynomial.mem_roots D.a_ne).mpr (Finset.mem_filter.mp hi).2
    have hsum : roots.card + S'.card = S.card := Finset.card_filter_add_card_filter_not ..
    have ha : D.a.natDegree ≤ heightBound := (Nat.le_add_right _ _).trans D.a_bound
    have hmargin : k + heightBound ≤ agreement := by decide
    have hcard : k ≤ S'.card := by omega
    apply eq_on_nodes S' _ _ (hP.trans_le (by exact_mod_cast hcard))
      (by rw [degree_zero]; exact WithBot.bot_lt_coe _)
    intro i hi
    have hi' : i ∈ S ∧ D.a.eval (node i) ≠ 0 := Finset.mem_filter.mp hi
    obtain ⟨hiS, hia⟩ := hi'
    rw [hits i hiS, eval_zero]
    obtain ⟨r, hr⟩ : ∃ r, (D.amp r).eval (node i) ≠ 0 := by
      rcases D.amp_nonzero_at zero_ne_one i with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have he := (D.nodes r z i).symm
    simp only [hQ, hz, eval_zero, mul_zero, zero_mul, sub_zero] at he
    have ht : twist ((D.amp r).eval (node i)) ≠ 0 := by
      intro h
      exact hr (twist.injective (h.trans (map_zero twist).symm))
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hia ht)
  · have he := D.decoder_identity z S P hS hP hits
    rw [hQ, PolarData.cross] at he
    by_contra hne
    have hN := congrArg K1.sixNorm (sub_eq_zero.mp he)
    simp only [sixNorm_mul, sixNorm_twist] at hN
    exact D.norms_ne (mul_right_cancel₀ (sixNorm_ne_zero hz)
      (mul_right_cancel₀ (sixNorm_ne_zero hne) hN))

/-- Two nonzero-amplitude decoders determine a polynomial pencil for all marked labels. -/
theorem pencil_of_marks {u : Words} (D : PolarData u) (Γ : Finset K)
    (M : ∀ z ∈ Γ, P0.BadMark u z) :
    Γ.card ≤ 2 ∨ ∃ P Q : K[X], P.degree < k ∧ Q.degree < k ∧
      ∀ z (hz : z ∈ Γ), (M z hz).decoder = pencil P Q z := by
  classical
  let G := Γ.filter (fun z => D.amp z ≠ 0)
  by_cases hsmall : G.card ≤ 1
  · let zeros := Γ.filter (fun z => D.amp z = 0)
    have hZ : zeros.card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro r s hr hs
      by_contra hrs
      have hr' := (Finset.mem_filter.mp hr).2
      have hs' := (Finset.mem_filter.mp hs).2
      simpa [hr', hs'] using D.amp_nonzero_at hrs (0 : I)
    have hsum : zeros.card + G.card = Γ.card := Finset.card_filter_add_card_filter_not ..
    exact Or.inl (by omega)
  right
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp (by omega : 1 < G.card)
  obtain ⟨hrΓ, hrA⟩ := Finset.mem_filter.mp hr
  obtain ⟨hsΓ, hsA⟩ := Finset.mem_filter.mp hs
  let Wr := (M r hrΓ).decoder
  let Ws := (M s hsΓ).decoder
  let Q := C ((s-r)⁻¹) * (Ws-Wr)
  let P := Wr - C r * Q
  have hWr : Wr.degree < k := (M r hrΓ).degree
  have hWs : Ws.degree < k := (M s hsΓ).degree
  have scale (c : K) (V : K[X]) (hV : V.degree < k) : (C c * V).degree < k := by
    by_cases hc : c = 0
    · rw [hc, map_zero, zero_mul, degree_zero]
      exact WithBot.bot_lt_coe k
    · simpa only [degree_C_mul hc] using hV
  have hQ : Q.degree < k := scale _ _ (degree_sub_lt hWs hWr)
  have hP : P.degree < k := degree_sub_lt hWr (scale _ _ hQ)
  have hpr : pencil P Q r = Wr := by simp [pencil, P]
  have hps : pencil P Q s = Ws := by
    have hc : (C s - C r : K[X]) * C ((s-r)⁻¹) = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hrs.symm), map_one]
    calc
      pencil P Q s = Wr + ((C s - C r) * C ((s-r)⁻¹)) * (Ws-Wr) := by
        simp only [pencil, P, Q]
        ring
      _ = Ws := by rw [hc, one_mul, add_comm, sub_add_cancel]
  let D' := D.subtract P Q hP hQ
  have hd (z : K) (hz : z ∈ Γ) (h : pencil P Q z = (M z hz).decoder) : D'.Q z z = 0 := by
    change D.Q z z - D.cross z z (pencil P Q z) (pencil P Q z) = 0
    rw [h, D.decoder_identity z _ _ (M z hz).agreement (M z hz).degree (M z hz).hits, sub_self]
  have hzero := D'.zero_of_diagonal_zeros hrs hrA hsA (hd r hrΓ hpr) (hd s hsΓ hps)
  refine ⟨P, Q, hP, hQ, fun z hz => sub_eq_zero.mp ?_⟩
  let W := M z hz
  change W.decoder - pencil P Q z = 0
  apply D'.decoder_zero hzero z W.support _ W.agreement (degree_sub_lt W.degree (pencil_degree hP hQ z))
  intro i hi
  rw [fold_residual, eval_sub, W.hits i hi]
  rfl

end
end P0_5
end PackSource_P0_5Pencil

section PackSource_P0_5Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace P0_5
noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k agreement t)
open K1_9 (K I node pencil)

/-- Fixing one support leaves at most one other label per node outside that support. -/
private theorem pencil_count {u : Words} (Γ : Finset K)
    (M : ∀ z ∈ Γ, P0.BadMark u z) {P Q : K[X]} (hP : P.degree < k)
    (hQ : Q.degree < k) (h : ∀ z (hz : z ∈ Γ), (M z hz).decoder = pencil P Q z) :
    Γ.card ≤ t + 1 := by
  classical
  by_cases hΓ : Γ.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]
  obtain ⟨r, hr⟩ := hΓ
  let S := (M r hr).support
  let nonjoint (i : I) := P.eval (node i) ≠ u 0 i ∨ Q.eval (node i) ≠ u 1 i
  have hits {z : K} (hz : z ∈ Γ) {i : I} (hi : i ∈ (M z hz).support) :
      P.eval (node i) + z * Q.eval (node i) = u 0 i + z * u 1 i := by
    simpa only [h z hz, pencil, eval_add, eval_mul, eval_C] using (M z hz).hits i hi
  have unique {z t : K} (hz : z ∈ Γ) (ht : t ∈ Γ) {i : I}
      (hi : i ∈ (M z hz).support) (hj : i ∈ (M t ht).support) (hn : nonjoint i) : z = t := by
    by_contra hne
    have h₁ := hits hz hi
    have h₂ := hits ht hj
    have hw : (z-t) * (Q.eval (node i) - u 1 i) = 0 := by linear_combination h₁ - h₂
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hne))
    rw [he, add_right_cancel_iff] at h₁
    exact hn.elim (fun hbad => hbad h₁) (fun hbad => hbad he)
  have witness (z : ↥(Γ.erase r)) :
      ∃ i ∈ (M z.val (Finset.mem_erase.mp z.property).2).support, nonjoint i := by
    let W := M z.val (Finset.mem_erase.mp z.property).2
    by_contra hw
    apply W.nonjoint
    refine ⟨⟨P, hP, ?_⟩, ⟨Q, hQ, ?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inr hn⟩
  choose f hf hn using witness
  let g : ↥(Γ.erase r) → ↥((Finset.univ : Finset I) \ S) := fun z =>
    ⟨f z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
      (Finset.mem_erase.mp z.property).1 (unique (Finset.mem_erase.mp z.property).2 hr (hf z) hi (hn z))⟩⟩
  have hg : Function.Injective g := by
    intro z t hzt
    have he : f z = f t := congrArg Subtype.val hzt
    apply Subtype.ext
    have ht := hf t
    rw [← he] at ht
    exact unique (Finset.mem_erase.mp z.property).2 (Finset.mem_erase.mp t.property).2 (hf z) ht (hn z)
  have hcard := Finset.card_le_card_of_injective hg
  have he := Finset.card_erase_add_one hr
  have hS : agreement ≤ S.card := (M r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index] at hcard
  dsimp only [t, P0.blockLength, agreement] at hS ⊢
  omega

theorem proof : P0.c5 := by
  intro u T R D B hp hn Γ hΓ
  classical
  obtain ⟨data⟩ := polarData_of_parallel B hp hn
  let M (z : K) (hz : z ∈ Γ) := Classical.choice (P0.bad_mark u Γ hΓ z hz)
  rcases pencil_of_marks data Γ M with hsmall | ⟨P, Q, hP, hQ, h⟩
  · exact hsmall.trans (by decide)
  · exact pencil_count Γ M hP hQ h

end
end P0_5
end PackSource_P0_5Proof

section PackSource_P0_7Defs
set_option autoImplicit true
set_option autoImplicit false

namespace P0_7
noncomputable section
open P0 MvPolynomial

/-- The complementary-minor bounds at the original, unpunctured height. -/
def WedgeBounds (h : ℕ) (U V : MvPolynomial (Fin 5) K) : Prop :=
  (L - h) * U.degreeOf 3 ≤ h ∧ (L - h) * U.degreeOf 4 ≤ L ∧
    (L - h) * V.degreeOf 3 ≤ L ∧ (L - h) * V.degreeOf 4 ≤ h

/-- Independent parameter lift. Only a scalar seed content is permitted
by the graph specialization. -/
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  bounds : WedgeBounds T.height U V
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : K1_11_2.graph p U = Polynomial.C content * leftU R
  graphV : K1_11_2.graph p V = Polynomial.C content * leftV R

/-- Primitive reduced plane pair. Divisibility transports the wedge bounds
from the original height without a new rank hypothesis on the punctured matrix. -/
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ A.U
  V_dvd : V ∣ A.V
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  graphU : K1_11_2.graph p U = Polynomial.C A.content * D.U
  graphV : K1_11_2.graph p V = Polynomial.C A.content * D.V

abbrev Puncture := K1_11.Puncture
open K1_11 (sourceWeights scalarWeightY scalarWeightYS scalarWeightT
  contactLift contactWeight contactShift polynomialView scalarImages)

structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted

inductive Bank
  | w22 | w12 | w21 | w13 | w23 | w31 | w32 | w33

def Bank.dS : Bank → ℕ
  | .w22 | .w21 | .w23 => 2
  | .w12 | .w13 => 1
  | .w31 | .w32 | .w33 => 3

def Bank.dT : Bank → ℕ
  | .w22 | .w12 | .w32 => 2
  | .w21 | .w31 => 1
  | .w13 | .w23 | .w33 => 3

def Bank.s : Bank → ℕ
  | .w22 => 10
  | .w12 => 14
  | .w21 => 9
  | _ => 8

def Bank.t : Bank → ℕ
  | .w22 => 10
  | .w12 => 9
  | .w21 => 14
  | _ => 8

def Bank.heightFloor : Bank → ℕ
  | .w22 | .w12 | .w21 => 24573
  | _ => 32764

def Bank.a (b : Bank) : ℕ := b.s + 5 * b.dS
def Bank.b (b : Bank) : ℕ := b.t + 5 * (b.dT - 1)
def Bank.E (b : Bank) : ℕ := b.a + b.b
def Bank.M (b : Bank) : ℕ := (2 * 131071 - 1) * (b.E - 1) + 1
def Bank.zeroFee (b : Bank) : ℕ := b.a + p * b.b
def Bank.chartRate (b : Bank) : ℚ := (43691 / 16382 : ℚ) * b.M
def Bank.chartFee (b : Bank) : ℚ := b.E * b.chartRate ^ 2

abbrev weightedCutoff : ℕ := 4 * agreement - 1
abbrev nodeCut := K1_11.nodeCut

def Bank.relationBounds (b : Bank) (H : ℕ) : Fin 4 → ℕ := ![131071 + H, 1, b.dS, b.dT]

/-- Source data for the actual punctured words, including local order
over the independent parameters and the primitive equation in Y₁. -/
structure ContactInput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (b : Bank) (H : ℕ) where
  L : MvPolynomial (Fin 5) K
  L_ne : L ≠ 0
  degrees : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j
  order_one : ∀ i : Fin P.N,
    (contactLift contactWeight
      (contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) L)).natTrailingDegree = 1
  numerator : MvPolynomial (Fin 4) K
  denominator : MvPolynomial (Fin 4) K
  denominator_ne : denominator ≠ 0
  linear : polynomialView L =
    Polynomial.C denominator * Polynomial.X - Polynomial.C numerator
  primitive : (Polynomial.C denominator * Polynomial.X - Polynomial.C numerator).IsPrimitive
  numerator_Y : numerator.weightedTotalDegree scalarWeightY ≤ 1
  denominator_Y : denominator.weightedTotalDegree scalarWeightY ≤ 0
  numerator_S : numerator.weightedTotalDegree scalarWeightYS ≤ b.dS
  denominator_S : denominator.weightedTotalDegree scalarWeightYS ≤ b.dS
  numerator_T : numerator.weightedTotalDegree scalarWeightT ≤ b.dT
  denominator_T : denominator.weightedTotalDegree scalarWeightT ≤ b.dT - 1

abbrev scalarWeightTotal := K1_11.scalarWeightTotal

/-- The chosen actual decoder of each original slope is a root, including
at labels where the denominator used in the construction specializes to zero. -/
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0

/-- One simple-root chart. The same cleared polynomial describes the
selected decoder at every marked point and determines all its node cuts. -/
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)


end
end P0_7
end PackSource_P0_7Defs

section PackSource_P0_7Plane
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

namespace P0_7
noncomputable section
open P0 MvPolynomial
open K1_11 (sourceWeights sourceBounds filtered mem_filtered)
open K1_11_2 (OmitsMessages sWeight tWeight graph PlaneOutput equation equation_degrees
  nodeWordMap decoder_bounds decoderNumerator decoderDenominator decoderDenominator_ne equation_linear
  equation_primitive linear_relation_contact_order_one)
open K1_11_2_2 (interpolant parameterNode nodeValue parameterNode_interpolant
  parameterNode_nodeValue degreeOf_interpolant_le degreeOf_nodeValue_le seedEval
  seedEval_nodeValue eval_graph nodeWord_combination nodeWord_omits)
open private degreeOf_le_of_dvd from ProximityPrize.SubmissionLower.Fast072
open private no_pair_one_one_of_graph native_column_rank from ProximityPrize.SubmissionLower.Fast070
open private transfer_at from ProximityPrize.SubmissionLower.Fast068

private theorem reduced_bounds {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A) :
    WedgeBounds T.height B.U B.V := by
  have loc_ne : liftX (FrobeniusLocator.locator node (fixedNodes R)) ≠ 0 :=
    fun hz => (FrobeniusLocator.locator_monic node (fixedNodes R)).ne_zero
      ((Polynomial.map_injective _ Polynomial.C_injective) (hz.trans (Polynomial.map_zero _).symm))
  have hU : A.U ≠ 0 := by
    intro h
    have hg := A.graphU
    rw [h, map_zero, D.U_factor] at hg
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr A.content_ne) (mul_ne_zero loc_ne D.U_ne) hg.symm
  have hV : A.V ≠ 0 := by
    intro h
    have hg := A.graphV
    rw [h, map_zero, D.V_factor] at hg
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr A.content_ne) (mul_ne_zero loc_ne D.V_ne) hg.symm
  exact ⟨(Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hU B.U_dvd 3)).trans A.bounds.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hU B.U_dvd 4)).trans A.bounds.2.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hV B.V_dvd 3)).trans A.bounds.2.2.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hV B.V_dvd 4)).trans A.bounds.2.2.2⟩

private theorem degree_lt_of_product (s d m b : ℕ) (hd : s * d ≤ b) (hm : b < s * m) :
    d < m := by
  by_contra! h
  exact (not_lt_of_ge ((Nat.mul_le_mul_left s h).trans hd)) hm

private theorem reduced_boxes {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hH : T.height ≤ heightCap) :
    B.U.degreeOf 3 ≤ 2 ∧ B.U.degreeOf 4 ≤ 3 ∧
      B.V.degreeOf 3 ≤ 3 ∧ B.V.degreeOf 4 ≤ 2 := by
  obtain ⟨hUS, hUT, hVS, hVT⟩ := reduced_bounds B
  have hh : T.height ≤ 32766 := hH
  exact ⟨Nat.le_of_lt_succ (degree_lt_of_product _ _ 3 _ hUS (by change _ < (49145 - _) * 3; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 4 _ hUT (by change 49145 < (49145 - _) * 4; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 4 _ hVS (by change 49145 < (49145 - _) * 4; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 3 _ hVT (by change _ < (49145 - _) * 3; omega))⟩

private theorem no_pair_one_one {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hs : sWeight B.U B.V = 1) (ht : tWeight B.U B.V = 1) :
    False := by
  let f : Polynomial K →ₐ[K] Frac := IsScalarTower.toAlgHom K (Polynomial K) Frac
  have hf : Function.Injective f := IsFractionRing.injective (Polynomial K) Frac
  have hold : K1.columnRank D.U D.V = 4 := (P0_4.columnRank_eq D.U D.V).symm.trans hr
  have hr' : K1_8.columnRankAt K1.p D.U D.V = 4 := hold
  rw [native_column_rank] at hr'
  exact no_pair_one_one_of_graph p f hf A.content B.U B.V D.U D.V A.content_ne D.U_ne
    B.U_omits B.V_omits B.graphU B.graphV hr' hs ht

private theorem actual_bank {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hH : T.height ≤ heightCap) :
    ∃ bank : Bank, sWeight B.U B.V = bank.dS ∧ tWeight B.U B.V = bank.dT ∧
      bank.heightFloor ≤ T.height := by
  obtain ⟨pUS, pUT, pVS, pVT⟩ := reduced_bounds B
  obtain ⟨bUS, bUT, bVS, bVT⟩ := reduced_boxes B hH
  have hlo : 24573 ≤ T.height := by
    by_contra! h
    have hs₁ : B.U.degreeOf 3 < 1 :=
      degree_lt_of_product _ _ 1 _ pUS (by change _ < (49145 - _) * 1; omega)
    have hs₂ : B.V.degreeOf 3 < 2 :=
      degree_lt_of_product _ _ 2 _ pVS (by change 49145 < (49145 - _) * 2; omega)
    have ht₁ : B.U.degreeOf 4 < 2 :=
      degree_lt_of_product _ _ 2 _ pUT (by change 49145 < (49145 - _) * 2; omega)
    have ht₂ : B.V.degreeOf 4 < 1 :=
      degree_lt_of_product _ _ 1 _ pVT (by change _ < (49145 - _) * 1; omega)
    exact no_pair_one_one B hr (by unfold sWeight; omega) (by unfold tWeight; omega)
  have hhi (hw : sWeight B.U B.V = 3 ∨ tWeight B.U B.V = 3) : 32764 ≤ T.height := by
    by_contra! h
    have hs₁ : B.U.degreeOf 3 < 2 :=
      degree_lt_of_product _ _ 2 _ pUS (by change _ < (49145 - _) * 2; omega)
    have hs₂ : B.V.degreeOf 3 < 3 :=
      degree_lt_of_product _ _ 3 _ pVS (by change 49145 < (49145 - _) * 3; omega)
    have ht₁ : B.U.degreeOf 4 < 3 :=
      degree_lt_of_product _ _ 3 _ pUT (by change 49145 < (49145 - _) * 3; omega)
    have ht₂ : B.V.degreeOf 4 < 2 :=
      degree_lt_of_product _ _ 2 _ pVT (by change _ < (49145 - _) * 2; omega)
    unfold sWeight tWeight at hw
    omega
  have hs : sWeight B.U B.V = 1 ∨ sWeight B.U B.V = 2 ∨ sWeight B.U B.V = 3 := by
    unfold sWeight
    omega
  have ht : tWeight B.U B.V = 1 ∨ tWeight B.U B.V = 2 ∨ tWeight B.U B.V = 3 := by
    unfold tWeight
    omega
  rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht
  · exact (no_pair_one_one B hr hs ht).elim
  · exact ⟨.w12, hs, ht, hlo⟩
  · exact ⟨.w13, hs, ht, hhi (Or.inr ht)⟩
  · exact ⟨.w21, hs, ht, hlo⟩
  · exact ⟨.w22, hs, ht, hlo⟩
  · exact ⟨.w23, hs, ht, hhi (Or.inr ht)⟩
  · exact ⟨.w31, hs, ht, hhi (Or.inl hs)⟩
  · exact ⟨.w32, hs, ht, hhi (Or.inl hs)⟩
  · exact ⟨.w33, hs, ht, hhi (Or.inl hs)⟩

private theorem reduced_scaled_relation {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (e : Polynomial K) :
    K1_8.relationOnAt p u (fixedNodes R) (Polynomial.C e * D.U)
      (Polynomial.C e * D.V) (Polynomial.C e * D.output) := by
  let G := liftX (FrobeniusLocator.locator node (fixedNodes R))
  have hG : ∀ i ∉ fixedNodes R, G.eval (Polynomial.C (node i)) ≠ 0 := by
    intro i hi
    rw [show G = K1.liftX _ from rfl, K1_8.eval_liftX, Polynomial.C_ne_zero]
    exact fun hz => hi ((FrobeniusLocator.Principal.locator_eval_zero_iff node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  exact @transfer_at u p 131072 T.height R (fixedNodes R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e

private theorem nodeValue_of_relation (q : ℕ) {u : Words} {deleted : Finset I}
    {P : Puncture deleted} {U V : MvPolynomial (Fin 5) K} {G : Bivar}
    (hrel : K1_8.relationOnAt q u deleted (graph q U) (graph q V) G) (i : Fin P.N) :
    seedEval q (nodeValue (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
      (u 0 (P.index i) ^ q) (u 1 (P.index i) ^ q) U V) = G.eval (Polynomial.C (P.nodes i)) := by
  have hkeep : P.index i ∉ deleted := (P.retained _).mp ⟨i, rfl⟩
  rw [seedEval_nodeValue]
  exact hrel (P.index i) hkeep

private theorem plane_output {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hH : T.height ≤ heightCap) (P : Puncture (fixedNodes R)) :
    Nonempty (PlaneOutput u P D.height B.U B.V) := by
  let x : Fin P.N → K := P.nodes
  let a (i : Fin P.N) : K := u 0 (P.index i)
  let b (i : Fin P.N) : K := u 1 (P.index i)
  let v (i : Fin P.N) := nodeValue (x i) (a i) (b i) (a i ^ p) (b i ^ p) B.U B.V
  let W := interpolant x v
  have hx : Function.Injective x :=
    ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective
  have hnodes (i : Fin P.N) : parameterNode (x i) W = v i :=
    parameterNode_interpolant x hx v (fun _ => parameterNode_nodeValue ..) i
  have hdeg (j : Fin 5) : W.degreeOf j ≤
      (P.N - 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 5) K).degreeOf j +
      (if j = 3 then sWeight B.U B.V else if j = 4 then tWeight B.U B.V else 0) :=
    degreeOf_interpolant_le x hx v j _ (fun i => degreeOf_nodeValue_le j
      (x i) (a i) (b i) (a i ^ p) (b i ^ p) B.U B.V)
  have hm : OmitsMessages W := ⟨Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 1),
    Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 2)⟩
  have hs : W.degreeOf 3 ≤ sWeight B.U B.V := by simpa [degreeOf_X] using hdeg 3
  have ht : W.degreeOf 4 ≤ tWeight B.U B.V := by simpa [degreeOf_X] using hdeg 4
  have hbound : 131072 + D.height ≤ P.N := by
    have hh : T.height ≤ 32766 := hH
    have hD := D.height_eq
    have hP := P.size
    omega
  have hsmall : W.degreeOf 3 < p := by
    obtain ⟨huS, _, hvS, _⟩ := reduced_boxes B hH
    unfold sWeight at hs
    change W.degreeOf 3 < 2130706433
    omega
  have hdegree := K1_11_2_1.graph_natDegree p (by decide) W hm hsmall
  have hWdeg : (graph p W).natDegree < P.N := by
    rw [hdegree]
    have hh : W.degreeOf 0 ≤ P.N - 1 := by simpa [degreeOf_X] using hdeg 0
    omega
  let G := Polynomial.C A.content * D.output
  have hDdeg : D.output.natDegree ≤ 131071 + D.height := by
    by_cases hz : D.output = 0
    · simp [hz]
    have hd := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr D.output_degree
    change D.output.natDegree < 131072 + D.height at hd
    omega
  have hGdeg : G.natDegree ≤ 131071 + D.height :=
    (Polynomial.natDegree_C_mul_le A.content D.output).trans hDdeg
  have hrel : K1_8.relationOnAt p u (fixedNodes R) (graph p B.U) (graph p B.V) G := by
    rw [B.graphU, B.graphV]
    exact reduced_scaled_relation D A.content
  have heval (i : Fin P.N) : (graph p W).eval (Polynomial.C (x i)) = G.eval (Polynomial.C (x i)) := by
    rw [eval_graph, hnodes]
    exact nodeValue_of_relation p (P := P) hrel i
  have hgraph : graph p W = G := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Polynomial.C_injective.comp hx) heval
    rw [Fintype.card_fin]
    exact max_lt hWdeg (by omega)
  have hheight : W.degreeOf 0 ≤ 131071 + D.height := by
    rw [← hdegree, hgraph]
    exact hGdeg
  refine ⟨⟨W, hm, hheight, hs, ht, ?_⟩⟩
  intro i
  change nodeWordMap (x i) (a i) (b i) (a i ^ p) (b i ^ p) (B.U * MvPolynomial.X 1 + B.V * MvPolynomial.X 2 - W) = 0
  rw [map_sub, nodeWord_combination _ _ _ _ _ _ _ B.U_omits B.V_omits,
    nodeWord_omits _ _ _ _ _ W hm, hnodes]
  exact sub_self _


theorem contact_input {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hH : T.height ≤ heightCap) (P : Puncture (fixedNodes R)) :
    ∃ b : Bank, b.heightFloor ≤ T.height ∧ Nonempty (ContactInput u P b D.height) := by
  obtain ⟨W⟩ := plane_output B hH P
  obtain ⟨bank, hs, ht, hfloor⟩ := actual_bank B hr hH
  let L := equation B.U B.V W.W
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) =
      sourceBounds (131071 + D.height) 1 bank.dS bank.dT j := by
    simpa only [L, equation, hs, ht] using equation_degrees 131071 D.height B.U B.V W.W
      B.U_ne B.V_ne B.U_omits B.V_omits W.omits B.height W.height W.degreeS W.degreeT
  have hL : L ≠ 0 := by
    intro hz
    have he := hdeg 1
    simp [hz, sourceBounds, weightedTotalDegree] at he
  have hf : L ∈ filtered (sourceWeights 131071)
      (sourceBounds (131071 + D.height) 1 bank.dS bank.dT) :=
    (mem_filtered _ _ _).mpr fun j => (hdeg j).le
  obtain ⟨hy, hdy, hns, hds, hnt, hdt⟩ := decoder_bounds 131071 D.height bank.dS bank.dT
    B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne hf
  refine ⟨bank, hfloor, ⟨{
    L := L
    L_ne := hL
    degrees := hdeg
    order_one := ?_
    numerator := decoderNumerator B.U W.W
    denominator := decoderDenominator B.V
    denominator_ne := decoderDenominator_ne B.V B.V_omits B.V_ne
    linear := equation_linear B.U B.V W.W B.U_omits B.V_omits W.omits
    primitive := equation_primitive B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne B.relPrime
    numerator_Y := hy
    denominator_Y := hdy
    numerator_S := hns
    denominator_S := hds
    numerator_T := hnt
    denominator_T := hdt
  }⟩⟩
  intro i
  exact linear_relation_contact_order_one _ _ _ _ _ B.U B.V W.W B.relPrime
    B.U_omits B.V_omits W.omits (W.node i)


end
end P0_7
end PackSource_P0_7Plane

section PackSource_P0_7Charts
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace P0_7
noncomputable section

open P0 MvPolynomial
open K1_11_3 (SimpleRoot derivativeChart exists_simple_derivative_at_root)
open private exceptions specializeY yView_degree specializeY_eval specializeY_iterate
  specializeY_derivative from ProximityPrize.SubmissionLower.Fast070
open private centerPoint atCenter atCenter_degree K1_11_3.numerator numerator_degree K1_11_3.denominator
  eval_atCenter pderiv_atCenter numerator_eval_degree denominator_degree reconstruct
  natDegree_le_of_degree_lt_succ derivativeChart_degree from ProximityPrize.SubmissionLower.Fast072

/-- Cover the surviving slopes by derivatives that are simple at the actual decoders. -/
theorem assign {u : Words} {deleted : Finset I} {Γ : Finset K}
    {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, ∃ hsub : charts j ⊆ Γ, ∀ γ (hγ : γ ∈ charts j),
        SimpleRoot (derivativeChart A.Q j) (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
  classical
  obtain ⟨exceptional, hfee, hex⟩ := exceptions A.Q A.nonzero p b.a b.b (by decide)
    (by cases b <;> decide) A.degreeS A.degreeT Γ
  have hassign (γ : K) (hγ : γ ∈ Γ) (hn : γ ∉ exceptional) :
      ∃ j : Fin 5, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p) := by
    let f := specializeY A.Q γ (γ ^ p)
    have hdeg : f.natDegree ≤ 5 :=
      (Polynomial.natDegree_map_le).trans ((yView_degree A.Q).le.trans A.degreeY)
    have hroot : f.IsRoot (F.mark γ hγ).decoder :=
      (specializeY_eval A.Q _ γ (γ ^ p)).trans (A.vanishes γ hγ)
    obtain ⟨j, hj, hz, hnz⟩ := exists_simple_derivative_at_root p 5 f
      (hex γ hγ hn) hdeg (by decide) _ hroot
    refine ⟨⟨j,hj⟩, ?_, ?_⟩
    · rw [← specializeY_eval, specializeY_iterate]
      exact hz
    · rw [← specializeY_eval, specializeY_derivative, specializeY_iterate]
      exact hnz
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p)
  refine ⟨exceptional, charts, hfee, ?_, ?_⟩
  · intro γ hγ
    by_cases he : γ ∈ exceptional
    · exact Or.inl he
    · obtain ⟨j,hj⟩ := hassign γ hγ he
      exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  · intro j
    refine ⟨fun _ hγ => (Finset.mem_filter.mp hγ).1, ?_⟩
    intro γ hγ
    obtain ⟨_, h⟩ := (Finset.mem_filter.mp hγ).2
    exact h


private theorem build_chart
    {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank)
    (Λ : Finset K) (hsub : Λ ⊆ Γ) (hne : Λ.Nonempty)
    (G : MvPolynomial (Fin 4) K) (hG : G.weightedTotalDegree scalarWeightTotal ≤ b.E)
    (hroot : ∀ γ (hγ : γ ∈ Λ),
      SimpleRoot G (F.mark γ (hsub hγ)).decoder γ (γ ^ p)) :
    Nonempty (TaylorChart u P F b Λ) := by
  classical
  let point (γ : K) : Fin 3 → Frac := if h : γ ∈ Λ then
    centerPoint (F.mark γ (hsub h)).decoder γ (γ ^ p) else fun _ => 0
  have hpnt (γ : K) (hγ : γ ∈ Λ) :
      point γ = centerPoint (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
    simp [point, hγ]
  refine ⟨{
    subset := hsub
    equation := atCenter G
    equation_ne := ?_
    equation_degree := (atCenter_degree G).trans hG
    numerator := K1_11_3.numerator G 131071
    numerator_degree := numerator_degree _ _
    denominator := K1_11_3.denominator G 131071
    cut_degree := ?_
    point := point
    slope := fun γ hγ => by rw [hpnt γ hγ]; rfl
    on_equation := fun γ hγ => by rw [hpnt γ hγ, eval_atCenter, (hroot γ hγ).1, map_zero]
    regular := ?_
    reconstruction := ?_ }⟩
  · obtain ⟨γ, hγ⟩ := hne
    have hn := (hroot γ hγ).2
    intro hz
    apply hn
    apply (IsFractionRing.injective (Polynomial K) Frac)
    rw [map_zero, ← eval_atCenter, ← pderiv_atCenter, hz, map_zero, map_zero]
  · intro i
    unfold nodeCut
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact numerator_eval_degree K1_11_3_1.proof G 131071 b.E (by cases b <;> decide) hG _
    · apply (totalDegree_mul _ _).trans
      have ha : (C (σ := Fin 3) (algebraMap K Frac (u 0 (P.index i))) +
          MvPolynomial.X 1 * C (algebraMap K Frac (u 1 (P.index i)))).totalDegree ≤ 1 := by
        exact (totalDegree_add _ _).trans (max_le (by simp)
          ((totalDegree_mul _ _).trans (by simp)))
      exact Nat.add_le_add (denominator_degree G 131071 b.E hG) ha
  · intro γ hγ
    rw [hpnt γ hγ, K1_11_3.denominator, map_pow, eval_atCenter]
    exact pow_ne_zero _ (fun h => (hroot γ hγ).2
      ((IsFractionRing.injective (Polynomial K) Frac) (h.trans (map_zero _).symm)))
  · intro γ hγ
    rw [hpnt γ hγ]
    apply reconstruct K1_11_3_2.proof
    · exact natDegree_le_of_degree_lt_succ (F.mark γ (hsub hγ)).degree
    · exact (hroot γ hγ).1
    · intro n hn
      have pp := CharP.char_is_prime_of_two_le K p (by decide)
      intro hz
      have hn' := pp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K p _).mp hz)
      exact (not_lt_of_ge (hn'.trans hn)) (by decide)

theorem chart_cover {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, charts j = ∅ ∨ Nonempty (TaylorChart u P F b (charts j)) := by
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ := assign A
  refine ⟨exceptional, charts, hfee, hcover, fun j => ?_⟩
  rcases (charts j).eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  · obtain ⟨hsub, hroot⟩ := hcharts j
    exact Or.inr (build_chart P F b (charts j) hsub hn (derivativeChart A.Q j)
      ((derivativeChart_degree A.Q j).trans A.degreeTotal) hroot)


end
end P0_7
end PackSource_P0_7Charts

section PackSource_P0_7Arithmetic
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000

namespace P0_7
open P0 Finset
open K1_11 (V J)

private def countRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (s + 1 - i) * (t + 1 - j)

private def gradeRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (i + j) * ((s + 1 - i) * (t + 1 - j))

private def count (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), countRow B s t i
private def grade (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), gradeRow B s t i

private def contactRow (m s t i : ℕ) : ℕ :=
  ∑ j ∈ range (m - i), (m - i - j) * (s + 1 - i) * (t + 1 - j)

private theorem V_affine (D w B s t : ℕ) (hB : w * B ≤ D + 1) :
    V D w B s t + w * grade B s t = (D + 1) * count B s t := by
  unfold V count grade countRow gradeRow
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hij : i + j ≤ B := by
    simp only [mem_range] at hi hj
    omega
  have hw := (Nat.mul_le_mul_left w hij).trans hB
  calc
    _ = ((D + 1 - w * (i + j)) + w * (i + j)) * ((s + 1 - i) * (t + 1 - j)) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hw]

/-- Compare the punctured source with its unpunctured value at the bank floor.
The multiplier coefficient count is no larger than the per-node jet cost. -/
private theorem surplus_of_stats (h H e N lo s t ds dt c g c' g' j : ℕ)
    (hlo : lo ≤ h) (hmax : h ≤ 32766) (hH : H + e = h) (hN : N + e = 262144)
    (hc : count 5 s t = c) (hg : grade 5 s t = g)
    (hc' : count 4 (s-ds) (t-dt) = c') (hg' : grade 4 (s-ds) (t-dt) = g')
    (hj : J 4 s t - J 3 (s-ds) (t-dt) = j) (hgain : c' ≤ j)
    (hmargin : 262144 * j + (589797 - lo) * c' + 131071 * g <
      720868 * c + 131071 * g') :
    N * (J 4 s t - J 3 (s-ds) (t-dt)) + V (720867 - 131071 - H) 131071 4 (s-ds) (t-dt)
      < V 720867 131071 5 s t := by
  have hv := V_affine 720867 131071 5 s t (by decide)
  have hv' := V_affine (720867 - 131071 - H) 131071 4 (s-ds) (t-dt) (by omega)
  rw [hc, hg] at hv
  rw [hc', hg'] at hv'
  have hw : 720867 - 131071 - H + 1 ≤ (589797 - lo) + e := by omega
  have hm : N * j + (720867 - 131071 - H + 1) * c' ≤
      262144 * j + (589797 - lo) * c' := by
    calc
      _ ≤ N * j + ((589797 - lo) + e) * c' :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hw) _
      _ = N * j + e * c' + (589797 - lo) * c' := by ring
      _ ≤ N * j + e * j + (589797 - lo) * c' :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hgain) _) _
      _ = _ := by rw [← Nat.add_mul, hN]
  rw [hj]
  omega

private theorem dims_5_10_10 : count 5 10 10 = 1806 ∧ grade 5 10 10 = 5544 := by
  constructor
  · have r0 : countRow 5 10 10 0 = 561 := by decide
    have r1 : countRow 5 10 10 1 = 450 := by decide
    have r2 : countRow 5 10 10 2 = 342 := by decide
    have r3 : countRow 5 10 10 3 = 240 := by decide
    have r4 : countRow 5 10 10 4 = 147 := by decide
    have r5 : countRow 5 10 10 5 = 66 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · have r0 : gradeRow 5 10 10 0 = 1210 := by decide
    have r1 : gradeRow 5 10 10 1 = 1250 := by decide
    have r2 : gradeRow 5 10 10 2 = 1152 := by decide
    have r3 : gradeRow 5 10 10 3 = 944 := by decide
    have r4 : gradeRow 5 10 10 4 = 658 := by decide
    have r5 : gradeRow 5 10 10 5 = 330 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]

private theorem dims_4_8_8 : count 4 8 8 = 870 ∧ grade 4 8 8 = 2124 := by
  constructor
  · have r0 : countRow 4 8 8 0 = 315 := by decide
    have r1 : countRow 4 8 8 1 = 240 := by decide
    have r2 : countRow 4 8 8 2 = 168 := by decide
    have r3 : countRow 4 8 8 3 = 102 := by decide
    have r4 : countRow 4 8 8 4 = 45 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 8 8 0 = 540 := by decide
    have r1 : gradeRow 4 8 8 1 = 560 := by decide
    have r2 : gradeRow 4 8 8 2 = 490 := by decide
    have r3 : gradeRow 4 8 8 3 = 354 := by decide
    have r4 : gradeRow 4 8 8 4 = 180 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]

private theorem dims_5_14_9 : count 5 14 9 = 2310 ∧ grade 5 14 9 = 7154 := by
  constructor
  · have r0 : countRow 5 14 9 0 = 675 := by decide
    have r1 : countRow 5 14 9 1 = 560 := by decide
    have r2 : countRow 5 14 9 2 = 442 := by decide
    have r3 : countRow 5 14 9 3 = 324 := by decide
    have r4 : countRow 5 14 9 4 = 209 := by decide
    have r5 : countRow 5 14 9 5 = 100 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · have r0 : gradeRow 5 14 9 0 = 1425 := by decide
    have r1 : gradeRow 5 14 9 1 = 1540 := by decide
    have r2 : gradeRow 5 14 9 2 = 1482 := by decide
    have r3 : gradeRow 5 14 9 3 = 1272 := by decide
    have r4 : gradeRow 5 14 9 4 = 935 := by decide
    have r5 : gradeRow 5 14 9 5 = 500 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]

private theorem dims_4_13_7 : count 4 13 7 = 1255 ∧ grade 4 13 7 = 3104 := by
  constructor
  · have r0 : countRow 4 13 7 0 = 420 := by decide
    have r1 : countRow 4 13 7 1 = 338 := by decide
    have r2 : countRow 4 13 7 2 = 252 := by decide
    have r3 : countRow 4 13 7 3 = 165 := by decide
    have r4 : countRow 4 13 7 4 = 80 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 13 7 0 = 700 := by decide
    have r1 : gradeRow 4 13 7 1 = 780 := by decide
    have r2 : gradeRow 4 13 7 2 = 732 := by decide
    have r3 : gradeRow 4 13 7 3 = 572 := by decide
    have r4 : gradeRow 4 13 7 4 = 320 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]

private theorem dims_5_9_14 : count 5 9 14 = 2310 ∧ grade 5 9 14 = 7154 := by
  constructor
  · have r0 : countRow 5 9 14 0 = 750 := by decide
    have r1 : countRow 5 9 14 1 = 585 := by decide
    have r2 : countRow 5 9 14 2 = 432 := by decide
    have r3 : countRow 5 9 14 3 = 294 := by decide
    have r4 : countRow 5 9 14 4 = 174 := by decide
    have r5 : countRow 5 9 14 5 = 75 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · have r0 : gradeRow 5 9 14 0 = 1700 := by decide
    have r1 : gradeRow 5 9 14 1 = 1665 := by decide
    have r2 : gradeRow 5 9 14 2 = 1472 := by decide
    have r3 : gradeRow 5 9 14 3 = 1162 := by decide
    have r4 : gradeRow 5 9 14 4 = 780 := by decide
    have r5 : gradeRow 5 9 14 5 = 375 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]

private theorem dims_4_7_13 : count 4 7 13 = 1255 ∧ grade 4 7 13 = 3104 := by
  constructor
  · have r0 : countRow 4 7 13 0 = 480 := by decide
    have r1 : countRow 4 7 13 1 = 350 := by decide
    have r2 : countRow 4 7 13 2 = 234 := by decide
    have r3 : countRow 4 7 13 3 = 135 := by decide
    have r4 : countRow 4 7 13 4 = 56 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 7 13 0 = 880 := by decide
    have r1 : gradeRow 4 7 13 1 = 840 := by decide
    have r2 : gradeRow 4 7 13 2 = 690 := by decide
    have r3 : gradeRow 4 7 13 3 = 470 := by decide
    have r4 : gradeRow 4 7 13 4 = 224 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]

private theorem dims_5_8_8 : count 5 8 8 = 1106 ∧ grade 5 8 8 = 3304 := by
  constructor
  · have r0 : countRow 5 8 8 0 = 351 := by decide
    have r1 : countRow 5 8 8 1 = 280 := by decide
    have r2 : countRow 5 8 8 2 = 210 := by decide
    have r3 : countRow 5 8 8 3 = 144 := by decide
    have r4 : countRow 5 8 8 4 = 85 := by decide
    have r5 : countRow 5 8 8 5 = 36 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · have r0 : gradeRow 5 8 8 0 = 720 := by decide
    have r1 : gradeRow 5 8 8 1 = 760 := by decide
    have r2 : gradeRow 5 8 8 2 = 700 := by decide
    have r3 : gradeRow 5 8 8 3 = 564 := by decide
    have r4 : gradeRow 5 8 8 4 = 380 := by decide
    have r5 : gradeRow 5 8 8 5 = 180 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]

private theorem dims_4_7_5 : count 4 7 5 = 455 ∧ grade 4 7 5 = 1064 := by
  constructor
  · have r0 : countRow 4 7 5 0 = 160 := by decide
    have r1 : countRow 4 7 5 1 = 126 := by decide
    have r2 : countRow 4 7 5 2 = 90 := by decide
    have r3 : countRow 4 7 5 3 = 55 := by decide
    have r4 : countRow 4 7 5 4 = 24 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 7 5 0 = 240 := by decide
    have r1 : gradeRow 4 7 5 1 = 280 := by decide
    have r2 : gradeRow 4 7 5 2 = 258 := by decide
    have r3 : gradeRow 4 7 5 3 = 190 := by decide
    have r4 : gradeRow 4 7 5 4 = 96 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]

private theorem dims_4_6_5 : count 4 6 5 = 385 ∧ grade 4 6 5 = 889 := by
  constructor
  · have r0 : countRow 4 6 5 0 = 140 := by decide
    have r1 : countRow 4 6 5 1 = 108 := by decide
    have r2 : countRow 4 6 5 2 = 75 := by decide
    have r3 : countRow 4 6 5 3 = 44 := by decide
    have r4 : countRow 4 6 5 4 = 18 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 6 5 0 = 210 := by decide
    have r1 : gradeRow 4 6 5 1 = 240 := by decide
    have r2 : gradeRow 4 6 5 2 = 215 := by decide
    have r3 : gradeRow 4 6 5 3 = 152 := by decide
    have r4 : gradeRow 4 6 5 4 = 72 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]

private theorem dims_4_5_7 : count 4 5 7 = 455 ∧ grade 4 5 7 = 1064 := by
  constructor
  · have r0 : countRow 4 5 7 0 = 180 := by decide
    have r1 : countRow 4 5 7 1 = 130 := by decide
    have r2 : countRow 4 5 7 2 = 84 := by decide
    have r3 : countRow 4 5 7 3 = 45 := by decide
    have r4 : countRow 4 5 7 4 = 16 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 5 7 0 = 300 := by decide
    have r1 : gradeRow 4 5 7 1 = 300 := by decide
    have r2 : gradeRow 4 5 7 2 = 244 := by decide
    have r3 : gradeRow 4 5 7 3 = 156 := by decide
    have r4 : gradeRow 4 5 7 4 = 64 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]

private theorem dims_4_5_6 : count 4 5 6 = 385 ∧ grade 4 5 6 = 889 := by
  constructor
  · have r0 : countRow 4 5 6 0 = 150 := by decide
    have r1 : countRow 4 5 6 1 = 110 := by decide
    have r2 : countRow 4 5 6 2 = 72 := by decide
    have r3 : countRow 4 5 6 3 = 39 := by decide
    have r4 : countRow 4 5 6 4 = 14 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 5 6 0 = 240 := by decide
    have r1 : gradeRow 4 5 6 1 = 250 := by decide
    have r2 : gradeRow 4 5 6 2 = 208 := by decide
    have r3 : gradeRow 4 5 6 3 = 135 := by decide
    have r4 : gradeRow 4 5 6 4 = 56 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]

private theorem dims_4_5_5 : count 4 5 5 = 315 ∧ grade 4 5 5 = 714 := by
  constructor
  · have r0 : countRow 4 5 5 0 = 120 := by decide
    have r1 : countRow 4 5 5 1 = 90 := by decide
    have r2 : countRow 4 5 5 2 = 60 := by decide
    have r3 : countRow 4 5 5 3 = 33 := by decide
    have r4 : countRow 4 5 5 4 = 12 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 5 5 0 = 180 := by decide
    have r1 : gradeRow 4 5 5 1 = 200 := by decide
    have r2 : gradeRow 4 5 5 2 = 172 := by decide
    have r3 : gradeRow 4 5 5 3 = 114 := by decide
    have r4 : gradeRow 4 5 5 4 = 48 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]

private theorem jets_4_10_10 : J 4 10 10 = 2096 := by
  change (∑ i ∈ range 4, contactRow 4 10 10 i) = 2096
  have r0 : contactRow 4 10 10 0 = 1100 := by decide
  have r1 : contactRow 4 10 10 1 = 620 := by decide
  have r2 : contactRow 4 10 10 2 = 288 := by decide
  have r3 : contactRow 4 10 10 3 = 88 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]

private theorem jets_3_8_8 : J 3 8 8 = 721 := by
  change (∑ i ∈ range 3, contactRow 3 8 8 i) = 721
  have r0 : contactRow 3 8 8 0 = 450 := by decide
  have r1 : contactRow 3 8 8 1 = 208 := by decide
  have r2 : contactRow 3 8 8 2 = 63 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]

private theorem jets_4_14_9 : J 4 14 9 = 2631 := by
  change (∑ i ∈ range 4, contactRow 4 14 9 i) = 2631
  have r0 : contactRow 4 14 9 0 = 1350 := by decide
  have r1 : contactRow 4 14 9 1 = 784 := by decide
  have r2 : contactRow 4 14 9 2 = 377 := by decide
  have r3 : contactRow 4 14 9 3 = 120 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]

private theorem jets_3_13_7 : J 3 13 7 = 1011 := by
  change (∑ i ∈ range 3, contactRow 3 13 7 i) = 1011
  have r0 : contactRow 3 13 7 0 = 616 := by decide
  have r1 : contactRow 3 13 7 1 = 299 := by decide
  have r2 : contactRow 3 13 7 2 = 96 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]

private theorem jets_4_9_14 : J 4 9 14 = 2631 := by
  change (∑ i ∈ range 4, contactRow 4 9 14 i) = 2631
  have r0 : contactRow 4 9 14 0 = 1400 := by decide
  have r1 : contactRow 4 9 14 1 = 774 := by decide
  have r2 : contactRow 4 9 14 2 = 352 := by decide
  have r3 : contactRow 4 9 14 3 = 105 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]

private theorem jets_3_7_13 : J 3 7 13 = 1011 := by
  change (∑ i ∈ range 3, contactRow 3 7 13 i) = 1011
  have r0 : contactRow 3 7 13 0 = 640 := by decide
  have r1 : contactRow 3 7 13 1 = 287 := by decide
  have r2 : contactRow 3 7 13 2 = 84 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]

private theorem jets_4_8_8 : J 4 8 8 = 1356 := by
  change (∑ i ∈ range 4, contactRow 4 8 8 i) = 1356
  have r0 : contactRow 4 8 8 0 = 720 := by decide
  have r1 : contactRow 4 8 8 1 = 400 := by decide
  have r2 : contactRow 4 8 8 2 = 182 := by decide
  have r3 : contactRow 4 8 8 3 = 54 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]

private theorem jets_3_7_5 : J 3 7 5 = 411 := by
  change (∑ i ∈ range 3, contactRow 3 7 5 i) = 411
  have r0 : contactRow 3 7 5 0 = 256 := by decide
  have r1 : contactRow 3 7 5 1 = 119 := by decide
  have r2 : contactRow 3 7 5 2 = 36 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]

private theorem jets_3_6_5 : J 3 6 5 = 356 := by
  change (∑ i ∈ range 3, contactRow 3 6 5 i) = 356
  have r0 : contactRow 3 6 5 0 = 224 := by decide
  have r1 : contactRow 3 6 5 1 = 102 := by decide
  have r2 : contactRow 3 6 5 2 = 30 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]

private theorem jets_3_5_7 : J 3 5 7 = 411 := by
  change (∑ i ∈ range 3, contactRow 3 5 7 i) = 411
  have r0 : contactRow 3 5 7 0 = 264 := by decide
  have r1 : contactRow 3 5 7 1 = 115 := by decide
  have r2 : contactRow 3 5 7 2 = 32 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]

private theorem jets_3_5_6 : J 3 5 6 = 356 := by
  change (∑ i ∈ range 3, contactRow 3 5 6 i) = 356
  have r0 : contactRow 3 5 6 0 = 228 := by decide
  have r1 : contactRow 3 5 6 1 = 100 := by decide
  have r2 : contactRow 3 5 6 2 = 28 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]

private theorem jets_3_5_5 : J 3 5 5 = 301 := by
  change (∑ i ∈ range 3, contactRow 3 5 5 i) = 301
  have r0 : contactRow 3 5 5 0 = 192 := by decide
  have r1 : contactRow 3 5 5 1 = 85 := by decide
  have r2 : contactRow 3 5 5 2 = 24 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]

theorem bank_surplus (b : Bank) (h H e N : ℕ) (hlo : b.heightFloor ≤ h)
    (hmax : h ≤ heightCap) (hH : H + e = h) (hN : N + e = blockLength) :
    N * (J 4 b.s b.t - J 3 (b.s - b.dS) (b.t - b.dT)) +
      V (weightedCutoff - 131071 - H) 131071 4 (b.s - b.dS) (b.t - b.dT) <
      V weightedCutoff 131071 5 b.s b.t := by
  cases b with
  | w22 =>
    exact surplus_of_stats h H e N 24573 10 10 2 2 1806 5544 870 2124 1375
      hlo hmax hH hN dims_5_10_10.1 dims_5_10_10.2 dims_4_8_8.1 dims_4_8_8.2
      (by rw [jets_4_10_10, jets_3_8_8]) (by decide) (by decide)
  | w12 =>
    exact surplus_of_stats h H e N 24573 14 9 1 2 2310 7154 1255 3104 1620
      hlo hmax hH hN dims_5_14_9.1 dims_5_14_9.2 dims_4_13_7.1 dims_4_13_7.2
      (by rw [jets_4_14_9, jets_3_13_7]) (by decide) (by decide)
  | w21 =>
    exact surplus_of_stats h H e N 24573 9 14 2 1 2310 7154 1255 3104 1620
      hlo hmax hH hN dims_5_9_14.1 dims_5_9_14.2 dims_4_7_13.1 dims_4_7_13.2
      (by rw [jets_4_9_14, jets_3_7_13]) (by decide) (by decide)
  | w13 =>
    exact surplus_of_stats h H e N 32764 8 8 1 3 1106 3304 455 1064 945
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_7_5.1 dims_4_7_5.2
      (by rw [jets_4_8_8, jets_3_7_5]) (by decide) (by decide)
  | w23 =>
    exact surplus_of_stats h H e N 32764 8 8 2 3 1106 3304 385 889 1000
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_6_5.1 dims_4_6_5.2
      (by rw [jets_4_8_8, jets_3_6_5]) (by decide) (by decide)
  | w31 =>
    exact surplus_of_stats h H e N 32764 8 8 3 1 1106 3304 455 1064 945
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_5_7.1 dims_4_5_7.2
      (by rw [jets_4_8_8, jets_3_5_7]) (by decide) (by decide)
  | w32 =>
    exact surplus_of_stats h H e N 32764 8 8 3 2 1106 3304 385 889 1000
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_5_6.1 dims_4_5_6.2
      (by rw [jets_4_8_8, jets_3_5_6]) (by decide) (by decide)
  | w33 =>
    exact surplus_of_stats h H e N 32764 8 8 3 3 1106 3304 315 714 1055
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_5_5.1 dims_4_5_5.2
      (by rw [jets_4_8_8, jets_3_5_5]) (by decide) (by decide)

private theorem rational_fee (E M exceptionFee limit a b : ℕ) (hb : 0 < b)
    (h : exceptionFee * b^2 + 5 * E * (a*M)^2 ≤ limit * b^2) :
    (exceptionFee : ℚ) + 5 * ((E : ℚ) * (((a : ℚ) / b) * M)^2) ≤ limit := by
  have hb' : 0 < (b : ℚ) := by exact_mod_cast hb
  have h' : (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 ≤
      (limit : ℚ) * (b : ℚ)^2 := by exact_mod_cast h
  refine le_of_mul_le_mul_right ?_ (pow_pos hb' 2)
  calc
    _ = (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 := by
      field_simp
    _ ≤ _ := h'

def Bank.regularCap : Bank → ℕ
  | .w22 => 98881751603308737
  | .w12 => 82585573997687680
  | .w21 => 82585573997687680
  | .w13 => 68185902430167102
  | .w23 => 107777690559483786
  | .w31 => 68185881123102782
  | .w32 => 107777679905951626
  | .w33 => 160322346563912056

theorem bank_fee (b : Bank) : (b.zeroFee : ℚ) + 5 * b.chartFee ≤ b.regularCap := by
  cases b with
  | w22 => exact rational_fee 35 8912795 31960596515 98881751603308737 43691 16382 (by decide) (by decide)
  | w12 => exact rational_fee 33 8388513 29829890081 82585573997687680 43691 16382 (by decide) (by decide)
  | w21 => exact rational_fee 33 8388513 29829890081 82585573997687680 43691 16382 (by decide) (by decide)
  | w13 => exact rational_fee 31 7864231 38352715807 68185902430167102 43691 16382 (by decide) (by decide)
  | w23 => exact rational_fee 36 9174936 38352715812 107777690559483786 43691 16382 (by decide) (by decide)
  | w31 => exact rational_fee 31 7864231 17045651487 68185881123102782 43691 16382 (by decide) (by decide)
  | w32 => exact rational_fee 36 9174936 27699183652 107777679905951626 43691 16382 (by decide) (by decide)
  | w33 => exact rational_fee 41 10485641 38352715817 160322346563912056 43691 16382 (by decide) (by decide)

theorem bank_cap (b : Bank) : b.regularCap ≤ 160322346563912056 := by
  cases b <;> decide

theorem bank_rate_ge (b : Bank) : (262144 : ℚ) ≤ b.chartRate := by
  have hm : (262144 : ℕ) ≤ b.M := by cases b <;> decide
  have hr : (1 : ℚ) ≤ 43691 / 16382 := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 16382)).mpr
    rw [one_mul]
    exact_mod_cast (show (16382 : ℕ) ≤ 43691 by decide)
  exact (by exact_mod_cast hm : (262144 : ℚ) ≤ b.M).trans
    (by simpa only [one_mul, Bank.chartRate] using
      mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℚ) ≤ b.M))

end P0_7
end PackSource_P0_7Arithmetic

section PackSource_P0_7Quotient
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace P0_7
noncomputable section

open MvPolynomial

open P0 (heightCap)
open K1_11 (V J filtered filteredMul filteredMul_injective mem_filteredMul_range_iff
  sourceWeights sourceBounds source_filtered_finrank JetSpace jetSpace_finrank sourceToJet
  contactShift contactLift contactWeight contactShift_parameter_weights
  truncated_mul_mem_jet contact_product_not_high_order
  jetSpace_support_bound)
open private exists_kernel_outside from ProximityPrize.SubmissionLower.Fast065

abbrev Source (F : Type*) [Field F] (b : Bank) :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds weightedCutoff 5 b.s b.t)

abbrev Multipliers (F : Type*) [Field F] (b : Bank) := JetSpace F 2 (b.s - b.dS) (b.t - b.dT)

variable {F : Type*} [Field F]

structure ContactData (N : ℕ) (L : MvPolynomial (Fin 5) F) (b : Bank) where
  x : Fin N → F
  first : Fin N → F
  firstSlope : Fin N → F
  second : Fin N → F
  secondSlope : Fin N → F
  nonzero : L ≠ 0
  degreeS : L.weightedTotalDegree (sourceWeights 1 2) ≤ b.dS
  degreeT : L.weightedTotalDegree (sourceWeights 1 3) ≤ b.dT
  order_one : ∀ i, (contactLift contactWeight
    (contactShift (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree = 1

variable {N : ℕ} {L : MvPolynomial (Fin 5) F} {b : Bank} {H : ℕ} (D : ContactData N L b)

def ContactData.shifted (i : Fin N) (Q : MvPolynomial (Fin 5) F) :=
  contactShift (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q

private theorem shifted_S (i : Fin N) :
    (D.shifted i L).weightedTotalDegree (sourceWeights 1 2) ≤ b.dS := by
  apply (contactShift_parameter_weights _ _ _ _ _ L).1.trans
  exact D.degreeS

private theorem shifted_T (i : Fin N) :
    (D.shifted i L).weightedTotalDegree (sourceWeights 1 3) ≤ b.dT := by
  apply (contactShift_parameter_weights _ _ _ _ _ L).2.trans
  exact D.degreeT

private theorem shifted_ne (i : Fin N) : D.shifted i L ≠ 0 := by
  intro hz
  have hh := D.order_one i
  change (contactLift contactWeight (D.shifted i L)).natTrailingDegree = 1 at hh
  simp [hz] at hh

private theorem bank_s (b : Bank) : b.s - b.dS + b.dS = b.s := by cases b <;> rfl
private theorem bank_t (b : Bank) : b.t - b.dT + b.dT = b.t := by cases b <;> rfl

private def localMultiply (i : Fin N) : Multipliers F b →ₗ[F] JetSpace F 3 b.s b.t where
  toFun Q := ⟨weightedTruncation contactWeight 4 (D.shifted i L * Q.val), by
    simpa only [bank_s, bank_t] using
      truncated_mul_mem_jet 2 (b.s-b.dS) (b.t-b.dT) b.dS b.dT (D.shifted i L)
        (shifted_S D i) (shifted_T D i) Q⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp

private theorem localMultiply_injective (i : Fin N) :
    Function.Injective (localMultiply D i) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro Q hQ
  by_contra hn
  have hprod : weightedTruncation contactWeight 4 (D.shifted i L * Q.val) = 0 :=
    congrArg (fun x : JetSpace F 3 b.s b.t => x.val) hQ
  have hhigh := (weightedTruncation_eq_zero_iff _ _ _).mp hprod
  have hQn : Q.val ≠ 0 := fun hz => hn (Subtype.ext hz)
  exact contact_product_not_high_order contactWeight 4 (D.shifted i L) Q.val
    (D.order_one i) (shifted_ne D i) hQn (jetSpace_support_bound _ _ _ Q) hhigh

private abbrev LocalSpace (i : Fin N) :=
  (JetSpace F 3 b.s b.t) ⧸ LinearMap.range (localMultiply D i)

private theorem local_finrank (i : Fin N) :
    Module.finrank F (LocalSpace D i) = J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT) := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (localMultiply D i))
  rw [LinearMap.finrank_range_of_inj (localMultiply_injective D i), jetSpace_finrank,
    jetSpace_finrank] at hq
  change Module.finrank F (LocalSpace D i) + J 3 (b.s-b.dS) (b.t-b.dT) = J 4 b.s b.t at hq
  omega

private def nodeMap (i : Fin N) : Source F b →ₗ[F] LocalSpace D i :=
  (LinearMap.range (localMultiply D i)).mkQ.comp
    (sourceToJet weightedCutoff 131071 5 b.s b.t 3 (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i))

private theorem localContact (Q : Source F b) (i : Fin N) (hi : nodeMap D i Q = 0) :
    ∃ R : Multipliers F b, D.shifted i Q.val - D.shifted i L * R.val ∈
      restrictWeightedOrder contactWeight 4 := by
  have hmem : sourceToJet weightedCutoff 131071 5 b.s b.t 3 (D.x i)
      (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q ∈
      LinearMap.range (localMultiply D i) :=
    (Submodule.Quotient.mk_eq_zero _).mp hi
  obtain ⟨R, hR⟩ := hmem
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm

theorem exists_quotient_source (h e : ℕ) (hmin : b.heightFloor ≤ h) (hmax : h ≤ heightCap)
    (hH : H + e = h) (hN : N + e = 262144)
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j) :
    ∃ Q : Source F b, ¬ L ∣ Q.val ∧ ∀ i, ∃ R : Multipliers F b,
      D.shifted i Q.val - D.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hupper : H ≤ 32766 := by
    have hh : h ≤ 32766 := hmax
    omega
  have hD : weightedCutoff = 720867 := rfl
  have hfit : ∀ i, b.relationBounds H i ≤ sourceBounds weightedCutoff 5 b.s b.t i := by
    intro i
    cases b <;> fin_cases i <;>
      simp [Bank.relationBounds, Bank.s, Bank.t, Bank.dS, Bank.dT, sourceBounds, hD] <;> omega
  have hshift : (fun i => sourceBounds weightedCutoff 5 b.s b.t i - b.relationBounds H i) =
      sourceBounds (weightedCutoff - 131071 - H) 4 (b.s-b.dS) (b.t-b.dT) := by
    funext i
    fin_cases i <;> simp [sourceBounds, Bank.relationBounds, hD] <;> omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds weightedCutoff 5 b.s b.t)
    (b.relationBounds H) L D.nonzero hdeg hfit
  have hdimMult : Module.finrank F (LinearMap.range mult) =
      V (weightedCutoff - 131071 - H) 131071 4 (b.s-b.dS) (b.t-b.dT) := by
    rw [LinearMap.finrank_range_of_inj
      (filteredMul_injective _ _ _ L D.nonzero hdeg hfit), hshift, source_filtered_finrank]
  have hdimLocal : Module.finrank F (∀ i : Fin N, LocalSpace D i) =
      N * (J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT)) := by
    letI (i : Fin N) : Module.Free F (LocalSpace D i) := Module.Free.of_divisionRing F _
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank D, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace D i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F b) := by
    rw [hdimLocal, hdimMult, source_filtered_finrank]
    exact bank_surplus b h H e N hmin hmax hH hN
  letI : Module F (∀ i : Fin N, LocalSpace D i) := Pi.module _ _ _
  obtain ⟨Q, hQ, hnot⟩ := exists_kernel_outside (G := ∀ i : Fin N, LocalSpace D i)
    (LinearMap.pi (nodeMap D)) (LinearMap.range mult) hdim
  exact ⟨Q, (mem_filteredMul_range_iff _ _ _ L D.nonzero hdeg hfit Q).not.mp hnot,
    fun i => localContact D Q i (congrFun hQ i)⟩

end
end P0_7
end PackSource_P0_7Quotient

section PackSource_P0_7Annihilator
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace P0_7
noncomputable section

open P0 FrobeniusLocator MvPolynomial
open K1_11 (V J contactLift contactWeight contactShift
  contactLift_X_pow_dvd_iff
  contactDecoderImages_vanish decoder_contact_composition decoder_eval_degree
  eq_zero_of_many_contacts decoder_contact_multiplicity decoderImages contactDecoderImages
  sourceWeights mem_filtered correctOn nodes_injective indexedSupport indexedSupport_card
  mem_indexedSupport scalarWeightY scalarWeightYS scalarWeightT scalarEliminant
  scalarEliminant_ne_zero polynomialView_source_coefficients clearedEval_weight_bound
  polynomialView scalarEliminant_annihilates)
open private scalar_total_weight_le from ProximityPrize.SubmissionLower.Fast071

variable {u : Words} {deleted : Finset I} {P : Puncture deleted} {b : Bank} {H : ℕ}
    (D : ContactInput u P b H)

def ContactInput.shifted (_D : ContactInput u P b H) (i : Fin P.N) (Q : MvPolynomial (Fin 5) K) :=
  contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
    (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) Q

private def asContactData : ContactData P.N D.L b where
  x := P.nodes
  first := fun i => u 0 (P.index i)
  firstSlope := fun i => u 1 (P.index i)
  second := fun i => u 0 (P.index i) ^ p
  secondSlope := fun i => u 1 (P.index i) ^ p
  nonzero := D.L_ne
  degreeS := le_of_eq (D.degrees 2)
  degreeT := le_of_eq (D.degrees 3)
  order_one := D.order_one

private theorem contact_order_one_mem {σ : Type*} (v : σ → ℕ) (L : MvPolynomial σ K)
    (hL : (contactLift v L).natTrailingDegree = 1) : L ∈ restrictWeightedOrder v 1 := by
  apply (contactLift_X_pow_dvd_iff v 1 L).mp
  apply Polynomial.X_pow_dvd_iff.mpr
  intro d hd
  apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
  omega

theorem relation_annihilates (hH : H ≤ 32766) (Q Q' : Polynomial K)
    (hQ : Q.natDegree ≤ 131071) (hQ' : Q'.natDegree ≤ 131071)
    (s t : K) (S : Finset (Fin P.N)) (hS : 180217 ≤ S.card) (hc : correctOn u P Q Q' s t S) :
    aeval (decoderImages Q Q' s t) D.L = 0 := by
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 1
  · intro i hi
    have ho := contact_order_one_mem contactWeight (D.shifted i D.L) (D.order_one i)
    have hd := pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder Polynomial.C ho
      (contactDecoderImages_vanish _ _ _ _ _ s t Q Q' (hc i hi).1 (hc i hi).2)
    change (Polynomial.X-Polynomial.C (P.nodes i))^1 ∣
      aeval (contactDecoderImages (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i)^p) (u 1 (P.index i)^p) s t Q Q') (D.shifted i D.L) at hd
    rwa [ContactInput.shifted, decoder_contact_composition] at hd
  · have hdeg : D.L.weightedTotalDegree (sourceWeights 131071 0) ≤ 131071+H :=
      le_of_eq (D.degrees 0)
    have hd := decoder_eval_degree 131071 (131071+H) D.L hdeg Q Q' hQ hQ' s t
    omega

theorem exists_two_decoder_source (h : ℕ) (hmin : b.heightFloor ≤ h) (hmax : h ≤ heightCap)
    (hH : H + deleted.card = h) :
    ∃ G : Source K b, ¬ D.L ∣ G.val ∧
      ∀ (Q Q' : Polynomial K), Q.natDegree ≤ 131071 → Q'.natDegree ≤ 131071 →
        ∀ (s t : K) (S : Finset (Fin P.N)), 180217 ≤ S.card → correctOn u P Q Q' s t S →
          aeval (decoderImages Q Q' s t) G.val = 0 := by
  obtain ⟨G, hnot, hnode⟩ := exists_quotient_source (asContactData D) h deleted.card hmin hmax hH P.size D.degrees
  refine ⟨G, hnot, ?_⟩
  intro Q Q' hQ hQ' s t S hS hc
  have hmax' : h ≤ 32766 := hmax
  have hrel := relation_annihilates D (by omega) Q Q' hQ hQ' s t S hS hc
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hnode i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ s t Q Q' G.val D.L R.val
      (hc i hi).1 (hc i hi).2 hrel hR
  · have hd := decoder_eval_degree 131071 weightedCutoff G.val
      ((mem_filtered _ _ _).mp G.property 0) Q Q' hQ hQ' s t
    change _ ≤ 720867 at hd
    omega

def selectMarks {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {Γ : Finset K} (hΓ : BadFamily u Γ) (hn : ∀ γ ∈ Γ, Normal u γ) :
    Marks u (fixedNodes R) Γ where
  mark γ hγ := Classical.choice (P0.bad_mark u Γ hΓ γ hγ)
  survives γ hγ i hi hid :=
    (D.deleted_error γ (hn γ hγ) _ i hid)
      ((Classical.choice (P0.bad_mark u Γ hΓ γ hγ)).hits i hi)

theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree < (131072 : ℕ) from M.degree)

theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [Strata.eval_coefficient_map twist M.decoder _ (Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, P0.twist, frobenius_def]


private theorem bank_cancel (b : Bank) : 1 + (b.dT - 1) = b.dT := by cases b <;> rfl

theorem exists_annihilator {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {b : Bank} {H : ℕ} (C : ContactInput u P b H) (h : ℕ)
    (hmin : b.heightFloor ≤ h) (hmax : h ≤ heightCap) (hH : H + deleted.card = h)
    {Γ : Finset K} (F : Marks u deleted Γ) : Nonempty (Annihilator F b) := by
  obtain ⟨G, hG, hgAnn⟩ := exists_two_decoder_source C h hmin hmax hH
  let Q := scalarEliminant 5 G.val C.numerator C.denominator
  have hne : Q ≠ 0 := scalarEliminant_ne_zero weightedCutoff 131071 5 b.s b.t
    G.val C.L G.property hG C.numerator C.denominator C.denominator_ne C.linear C.primitive
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients weightedCutoff 131071 5 b.s b.t G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 := by
    simpa [Q, scalarEliminant] using
      clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val)
        C.numerator C.denominator (by simpa using hY) C.numerator_Y C.denominator_Y (by omega)
  have hs : Q.weightedTotalDegree scalarWeightYS ≤ b.a := by
    simpa [Q, scalarEliminant, Bank.a] using
      clearedEval_weight_bound scalarWeightYS 5 b.s 0 b.dS b.dS (polynomialView G.val)
        C.numerator C.denominator (by simpa using hS) C.numerator_S C.denominator_S (by omega)
  have ht : Q.weightedTotalDegree scalarWeightT ≤ b.b := by
    simpa [Q, scalarEliminant, Bank.b] using
      clearedEval_weight_bound scalarWeightT 5 b.t 1 b.dT (b.dT-1) (polynomialView G.val)
        C.numerator C.denominator (by simpa using hT) C.numerator_T C.denominator_T (bank_cancel b).ge
  refine ⟨⟨Q, hne, hy, hs, ht, scalar_total_weight_le Q b.a b.b hs ht, ?_⟩⟩
  intro γ hγ
  let M := F.mark γ hγ
  let S := indexedSupport P M.support
  have hS : 180217 ≤ S.card := by
    rw [indexedSupport_card P M.support (F.survives γ hγ)]
    exact M.agreement
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 :=
    Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hmax' : h ≤ 32766 := hmax
  have hrel := relation_annihilates C (by omega) _ _ hd hd' γ (γ ^ p) S hS hcorrect
  exact scalarEliminant_annihilates weightedCutoff 131071 5 b.s b.t G.val C.L G.property
    C.numerator C.denominator C.linear _ _ γ (γ^p) hrel
    (hgAnn _ _ hd hd' γ (γ^p) S hS hcorrect)


end
end P0_7
end PackSource_P0_7Annihilator

section PackSource_P0_7Incidence
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace P0_7
noncomputable section

open P0 MvPolynomial
open scoped BigOperators
open K1_11 (indexedSupport mem_indexedSupport indexedSupport_card nodes_injective)
open private ncard_inter_filter surface_count_with_terminal from ProximityPrize.SubmissionLower.Fast070
open private seed_eq_of_mismatch from ProximityPrize.SubmissionLower.Fast065

variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}

private theorem pencil_bad_count (hsub : Λ ⊆ Γ) (P₀ P₁ : Polynomial K)
    (h₀ : P₀.degree < (131072 : ℕ)) (h₁ : P₁.degree < (131072 : ℕ))
    (pencil : ∀ γ (hγ : γ ∈ Λ),
      (F.mark γ (hsub hγ)).decoder = P₀ + Polynomial.C γ * P₁) :
    Λ.card ≤ P.N := by
  classical
  have mismatch (γ : Λ) :
      ∃ i : Fin P.N,
        (P₀.eval (P.nodes i) ≠ u 0 (P.index i) ∨ P₁.eval (P.nodes i) ≠ u 1 (P.index i)) ∧
        P₀.eval (P.nodes i) + (γ : K) * P₁.eval (P.nodes i) =
          u 0 (P.index i) + (γ : K) * u 1 (P.index i) := by
    let M := F.mark γ (hsub γ.property)
    obtain ⟨idx, hi, hm⟩ :
        ∃ idx ∈ M.support, P₀.eval (node idx) ≠ u 0 idx ∨ P₁.eval (node idx) ≠ u 1 idx := by
      by_contra hn
      push Not at hn
      exact M.nonjoint ⟨⟨P₀, h₀, fun j hj => (hn j hj).1⟩, ⟨P₁, h₁, fun j hj => (hn j hj).2⟩⟩
    obtain ⟨i, rfl⟩ := (P.retained idx).mpr (F.survives γ (hsub γ.property) idx hi)
    refine ⟨i, hm, ?_⟩
    have hh := M.hits (P.index i) hi
    change (F.mark (γ : K) (hsub γ.property)).decoder.eval (P.nodes i) = _ at hh
    simpa only [pencil _ γ.property, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C] using hh
  let f : Λ → Fin P.N := fun γ => Classical.choose (mismatch γ)
  have hf : Function.Injective f := by
    intro γ δ he
    apply Subtype.ext
    obtain ⟨hm, hγ⟩ := Classical.choose_spec (mismatch γ)
    have hδ := (Classical.choose_spec (mismatch δ)).2
    change f γ = f δ at he
    change
      (P₀.eval (P.nodes (f γ)) ≠ u 0 (P.index (f γ)) ∨
        P₁.eval (P.nodes (f γ)) ≠ u 1 (P.index (f γ))) at hm
    change P₀.eval (P.nodes (f γ)) + (γ : K) * P₁.eval (P.nodes (f γ)) =
      u 0 (P.index (f γ)) + (γ : K) * u 1 (P.index (f γ)) at hγ
    change P₀.eval (P.nodes (f δ)) + (δ : K) * P₁.eval (P.nodes (f δ)) =
      u 0 (P.index (f δ)) + (δ : K) * u 1 (P.index (f δ)) at hδ
    rw [← he] at hδ
    exact seed_eq_of_mismatch (F := K) hγ hδ hm
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

variable (chart : TaylorChart u P F b Λ)

theorem chart_cut_iff (γ : K) (hγ : γ ∈ Λ) (i : Fin P.N) :
    MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 ↔
      (F.mark γ (chart.subset hγ)).decoder.eval (P.nodes i) =
        u 0 (P.index i) + γ * u 1 (P.index i) := by
  let val := MvPolynomial.eval (chart.point γ)
  let x := algebraMap K Frac (P.nodes i)
  change val (nodeCut u P chart.numerator chart.denominator i) = 0 ↔ _
  have heval := Polynomial.eval_map_apply val (C x) (p := chart.numerator)
  unfold nodeCut
  change val (chart.numerator.eval (C x) - _) = 0 ↔ _
  rw [map_sub, ← heval]
  change (chart.numerator.map val).eval (val (C x)) - _ = 0 ↔ _
  rw [show val (C x) = x by simp [val], show chart.numerator.map val = _ from chart.reconstruction γ hγ]
  rw [Polynomial.eval_mul, Polynomial.eval_C, show x = algebraMap K Frac (P.nodes i) from rfl,
    Polynomial.eval_map_apply, map_mul, map_add, map_mul]
  simp only [val, eval_C, eval_X, chart.slope γ hγ]
  rw [← map_mul, ← map_add, sub_eq_zero]
  constructor
  · intro h
    exact (algebraMap K Frac).injective (mul_left_cancel₀ (chart.regular γ hγ) h)
  · intro h
    rw [h]

theorem chart_agreements (γ : K) (hγ : γ ∈ Λ) :
    180217 ≤ {i | MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0}.ncard := by
  let M := F.mark γ (chart.subset hγ)
  have hsub : (indexedSupport P M.support : Set (Fin P.N)) ⊆
      {i | MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0} := by
    intro i hi
    exact (chart_cut_iff chart γ hγ i).mpr (M.hits _ ((mem_indexedSupport P M.support i).mp hi))
  have h := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, indexedSupport_card P M.support (F.survives γ (chart.subset hγ))] at h
  exact M.agreement.trans h

theorem chart_persistent (J : Ideal (MvPolynomial (Fin 3) Frac)) (W : Finset K) (hW : W ⊆ Λ)
    (hzero : ∀ γ ∈ W, chart.point γ ∈ zeroLocus Frac J)
    (hpersist : 131072 ≤ {i | nodeCut u P chart.numerator chart.denominator i ∈ J}.ncard) :
    W.card ≤ P.N := by
  classical
  let keep := Finset.univ.filter fun i => nodeCut u P chart.numerator chart.denominator i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersist.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P₀ := Lagrange.interpolate S P.nodes (fun i => u 0 (P.index i))
  let P₁ := Lagrange.interpolate S P.nodes (fun i => u 1 (P.index i))
  have hinj : Set.InjOn P.nodes (S : Set (Fin P.N)) := nodes_injective.injOn
  have hd₀ : P₀.degree < (131072 : ℕ) := by
    simpa only [P₀, hcard] using Lagrange.degree_interpolate_lt (fun i => u 0 (P.index i)) hinj
  have hd₁ : P₁.degree < (131072 : ℕ) := by
    simpa only [P₁, hcard] using Lagrange.degree_interpolate_lt (fun i => u 1 (P.index i)) hinj
  apply pencil_bad_count (P := P) (F := F) (fun _ hg => chart.subset (hW hg)) P₀ P₁ hd₀ hd₁
  intro γ hγ
  let M := F.mark γ (chart.subset (hW hγ))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (mark_degree M)))
  · rw [hcard]
    have hm : (Polynomial.C γ * P₁).degree ≤ P₁.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) P₁.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hd₀ (hm.trans_lt hd₁))
  · intro i hi
    have hcut : nodeCut u P chart.numerator chart.denominator i ∈ J := (Finset.mem_filter.mp (hS hi)).2
    have hz : MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 :=
      hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (chart_cut_iff chart γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])


theorem chart_count {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
    (chart : TaylorChart u P F b Λ) : (Λ.card : ℚ) ≤ b.chartFee := by
  classical
  let S := Λ.image chart.point
  let R : ℚ := b.chartRate
  have hRbig : (262144 : ℚ) ≤ R := bank_rate_ge b
  have hone : (1 : ℚ) ≤ 262144 := by
    exact_mod_cast (show (1 : ℕ) ≤ 262144 by decide)
  have hR : 1 ≤ R := hone.trans hRbig
  have hN : P.N ≤ 262144 := by have := P.size; omega
  have hinj : Set.InjOn chart.point (Λ : Set K) := by
    intro γ hγ δ hδ he
    apply (algebraMap K Frac).injective
    exact (chart.slope γ hγ).symm.trans ((congrFun he 1).trans (chart.slope δ hδ))
  have hcard : S.card = Λ.card := Finset.card_image_of_injOn hinj
  let cuts := nodeCut u P chart.numerator chart.denominator
  have hratio (m : ℕ) (hm : m < 131072) :
      (((Fintype.card (Fin P.N) - m) * b.M : ℕ) : ℚ) ≤ R * ((180217 - m : ℕ) : ℚ) := by
    have hnat : (P.N - m) * 16382 ≤ 43691 * (180217 - m) := by omega
    have hrat : ((P.N - m : ℕ) : ℚ) * 16382 ≤ 43691 * ((180217 - m : ℕ) : ℚ) := by
      exact_mod_cast hnat
    have hh : ((P.N - m : ℕ) : ℚ) ≤ (43691/16382 : ℚ) * ((180217 - m : ℕ) : ℚ) := by
      linarith
    rw [Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (b.M : ℚ))).trans_eq (by dsimp [R, Bank.chartRate]; ring)
  rw [← hcard]
  refine surface_count_with_terminal chart.equation chart.denominator chart.equation_ne cuts
    (L := 131072) (A := 180217) (by decide) chart.equation_degree chart.cut_degree hR hratio S
    (fun x hx => ?_) (fun x hx => ?_) (fun J hJ => ?_)
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨chart.on_equation γ hγ, chart.regular γ hγ⟩
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact chart_agreements chart γ hγ
  · let W := Λ.filter fun γ => chart.point γ ∈ zeroLocus Frac J
    have hW : W ⊆ Λ := Finset.filter_subset _ _
    have hWimage : W.image chart.point = S.filter (· ∈ zeroLocus Frac J) := by
      ext x
      simp only [W, S, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨γ, ⟨hγ, hJγ⟩, rfl⟩
        exact ⟨⟨γ, hγ, rfl⟩, hJγ⟩
      · rintro ⟨⟨γ, hγ, rfl⟩, hJγ⟩
        exact ⟨γ, ⟨hγ, hJγ⟩, rfl⟩
    have hbound := chart_persistent chart J W hW (fun γ hγ => (Finset.mem_filter.mp hγ).2) hJ
    rw [ncard_inter_filter, ← hWimage, Finset.card_image_of_injOn (hinj.mono hW)]
    exact (by exact_mod_cast hbound.trans hN : (W.card : ℚ) ≤ 262144).trans hRbig


end
end P0_7
end PackSource_P0_7Incidence

section PackSource_P0_7Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace P0_7
open P0

/-- Lift the primitive relation to the independent parameter plane and
bound its degrees by the unpunctured shift wedge. -/
def c1 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    Nonempty (IndependentLift R)

/-- Remove the common fixed X-locator while retaining plane coprimality,
the exact reduced X-height, and the common graph content. -/
def c2 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    T.height ≤ heightCap → ∀ (A : IndependentLift R),
      Nonempty (ReducedPair D A)

private theorem card_from_cover (b : Bank) (Γ exceptional : Finset K)
    (charts : Fin 5 → Finset K) (hfee : exceptional.card ≤ b.zeroFee)
    (hcover : ∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j)
    (hcharts : ∀ j, ((charts j).card : ℚ) ≤ b.chartFee) :
    Γ.card ≤ 160322346563912056 := by
  classical
  have hsub : Γ ⊆ exceptional ∪ Finset.univ.biUnion charts := by
    intro γ hγ
    exact Finset.mem_union.mpr ((hcover γ hγ).imp id (fun ⟨j, hj⟩ =>
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩))
  have hcount := (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hbound : (Γ.card : ℚ) ≤ b.zeroFee + 5 * b.chartFee := by
    calc
      (Γ.card : ℚ) ≤ (exceptional.card : ℚ) + ∑ j : Fin 5, ((charts j).card : ℚ) := by
        exact_mod_cast hcount
      _ ≤ (b.zeroFee : ℚ) + ∑ _j : Fin 5, b.chartFee := by
        exact add_le_add (by exact_mod_cast hfee) (Finset.sum_le_sum fun j _ => hcharts j)
      _ = _ := by simp
  have hcap := hbound.trans (bank_fee b)
  exact (by exact_mod_cast hcap : Γ.card ≤ b.regularCap).trans (bank_cap b)

theorem of_children (h1 : c1) (h2 : c2) : P0.c7 := by
  intro u hu T R D _ hr Γ hΓ hn
  classical
  have hmax := relation_height_le hu T
  obtain ⟨A⟩ := h1 u hu T R
  obtain ⟨B⟩ := h2 u T R D hmax A
  let P := K1_11.nativePuncture (fixedNodes R)
  let F := selectMarks D hΓ hn
  obtain ⟨b, hfloor, ⟨C⟩⟩ := contact_input B hr hmax P
  obtain ⟨Q⟩ := exists_annihilator C T.height hfloor hmax D.height_eq F
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ := chart_cover P Q
  refine card_from_cover b Γ exceptional charts hfee hcover fun j => ?_
  rcases hcharts j with he | chart
  · simp only [he, Finset.card_empty, Nat.cast_zero]
    unfold Bank.chartFee
    positivity
  · exact chart_count (Classical.choice chart)

end P0_7
end PackSource_P0_7Split

section PackSource_P0_7_1Aux1
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace P0_7_1

noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark P0
open K1_11_1 (Seeds PlaneField planeSlice planeStack graph rank_graph mulVec_map)
open private syndrome_degree graph_slice_map graph_stack_map certificate_kernel
  from ProximityPrize.SubmissionLower.Fast065

private theorem first_slice_nullity (u : Words) (T : TwoActive u) :
    GenericLayer.genericNullity
      (Strata.parameterRelation p node (u 0) (u 1) k T.height) = 1 :=
  Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level

theorem plane_first_slice_nullity (u : Words) (T : TwoActive u)
    (hh : T.height ≤ heightCap) :
    Module.finrank (PlaneField K) (LinearMap.ker
      ((planeSlice p node (u 0) (u 1) k T.height).map
        (algebraMap (Seeds K) (PlaneField K))).mulVecLin) = 1 := by
  let A := planeSlice p node (u 0) (u 1) k T.height
  have hdeg (j : Fin (k - T.height)) (b : Fin 2 × Fin (T.height + 1)) :
      (A j b).degreeOf 0 ≤ if b.1 = 0 then 1 else 0 :=
    syndrome_degree p node (u 0) (u 1) b.1 0 _
  have hsize : T.height + 1 < p :=
    (Nat.add_le_add_right hh 1).trans_lt (by decide)
  have he := rank_graph p (by decide) hsize A hdeg
  change (A.map (algebraMap (Seeds K) (PlaneField K))).rank =
    ((planeSlice p node (u 0) (u 1) k T.height).map _).rank at he
  rw [graph_slice_map] at he
  have hn := GenericLayer.rank_add_nullity
    (Strata.parameterRelation p node (u 0) (u 1) k T.height)
  rw [first_slice_nullity u T] at hn
  apply GenericRank.nullity_one_of_rank
  change (A.map (algebraMap (Seeds K) (PlaneField K))).rank + 1 = _
  rw [he]
  exact hn

theorem plane_stack_degree (u : Words) (b : Fin 2 × Fin L) (j : Fin (t + 1))
    (i : Fin 2) :
    (planeStack p node (u 0) (u 1) L t b j).degreeOf i ≤
      if b.1 = i then 1 else 0 :=
  syndrome_degree p node (u 0) (u 1) b.1 i _

theorem plane_stack_rank (u : Words) :
    ((planeStack p node (u 0) (u 1) L t).map
      (algebraMap (Seeds K) (PlaneField K))).rank = stackRank u := by
  let A := planeStack p node (u 0) (u 1) L t
  have hdeg (j : Fin (t + 1)) (b : Fin 2 × Fin L) :
      (A.transpose j b).degreeOf 0 ≤ if b.1 = 0 then 1 else 0 :=
    plane_stack_degree u b j 0
  have he := rank_graph p (by decide) (by decide) A.transpose hdeg
  rw [Matrix.transpose_map, Matrix.transpose_map, Matrix.rank_transpose, Matrix.rank_transpose] at he
  change ((planeStack p node (u 0) (u 1) L t).map _).rank =
    ((planeStack p node (u 0) (u 1) L t).map _).rank at he
  rw [graph_stack_map] at he
  exact he

/-- The graph image of the plane generator is a polynomial multiple of the
supplied primitive relation, with a single multiplier for both blocks. -/
theorem graph_content (u : Words) (T : TwoActive u) (R : Relation T)
    (Q : Fin 2 × Fin (T.height + 1) → Seeds K)
    (hQ : (planeSlice p node (u 0) (u 1) k T.height).mulVec Q = 0)
    (hgraph : (fun j => graph p (Q j)) ≠ 0) :
    ∃ c : K[X], c ≠ 0 ∧ ∀ j, graph p (Q j) = c * R.coefficients j := by
  classical
  let f := algebraMap K[X] Frac
  let M := (Strata.parameterRelation p node (u 0) (u 1) k T.height).map f
  let E := fun j => f (R.coefficients j)
  let V := fun j => f (graph p (Q j))
  obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout R.coefficients).mp R.primitive
  have hinj := IsFractionRing.injective K[X] Frac
  have hE : E ≠ 0 := by
    intro he
    have hzero (j : Fin 2 × Fin (T.height + 1)) : R.coefficients j = 0 :=
      hinj ((congrFun he j).trans (map_zero f).symm)
    simp only [hzero, mul_zero, Finset.sum_const_zero, zero_ne_one] at ha
  have hME : M.mulVec E = 0 :=
    certificate_kernel p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed k k T.height
      (by rw [IRSProfile.card_index]; decide) R
  have hMV : M.mulVec V = 0 := by
    change ((Strata.parameterRelation p node (u 0) (u 1) k T.height).map f).mulVec V = 0
    rw [← graph_slice_map]
    change ((planeSlice p node (u 0) (u 1) k T.height).map
      (f.comp (graph p).toRingHom)).mulVec
      (fun j => (f.comp (graph p).toRingHom) (Q j)) = 0
    rw [mulVec_map, hQ]
    funext j
    rw [Pi.zero_apply, map_zero, Pi.zero_apply]
  obtain ⟨b, hb⟩ := GenericRank.kernel_line_of_finrank M
    (first_slice_nullity u T) E hE hME V hMV
  let c := ∑ j, a j * graph p (Q j)
  have hc : f c = b := by
    have hbe := congrArg f ha
    simp only [map_sum, map_mul, map_one] at hbe
    simp only [c, map_sum, map_mul]
    have he (j : Fin 2 × Fin (T.height + 1)) : f (graph p (Q j)) = b * f (R.coefficients j) :=
      congrFun hb j
    simp_rw [he, mul_left_comm (f (a _)) b, ← Finset.mul_sum, hbe, mul_one]
  have he (j : Fin 2 × Fin (T.height + 1)) : graph p (Q j) = c * R.coefficients j := by
    apply hinj
    rw [map_mul, hc]
    exact congrFun hb j
  refine ⟨c, ?_, he⟩
  intro hzero
  apply hgraph
  funext j
  rw [he, hzero, zero_mul, Pi.zero_apply]

end

end P0_7_1
end PackSource_P0_7_1Aux1

section PackSource_P0_7_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace P0_7_1

noncomputable section

open Polynomial Matrix FrobeniusLocator P0
open K1_11_1 (Seeds PlaneField planePair planeStack plane_generator shifts_annihilate
  blockDegree degreeOf_coordinate graph graph_ne_zero seedPositions intoFive intoFive_omitted
  intoFive_height intoFive_seed_degree intoFive_primitive graph_intoFive)

-- K1_11_1.graph_pair is phrased for the old native certificate.
-- Its coefficient proof is independent of the agreement.
private theorem graph_pair {F : Type} [Field F] {h : ℕ} (q : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (a : Fin 2 × Fin (h + 1) → F[X])
    (c : F[X]) (hQ : ∀ j, graph q (Q j) = c * a j) (b : Fin 2) :
    (planePair Q b).map (graph q).toRingHom =
      Polynomial.C c * Principal.assemble (fun j => a (b, j)) := by
  rw [planePair, Principal.map_assemble]
  change Principal.assemble (fun j => graph q (Q (b, j))) = _
  simp only [hQ, Principal.assemble, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.C_mul_monomial]

theorem proof : P0_7.c1 := by
  intro u front T R
  classical
  let h := T.height
  let s := L - h
  have hbal : L + h + nullity u = t + 1 := relation_height_balance T
  have hhi : h ≤ heightCap := relation_height_le front T
  have hL : h < L := hhi.trans_lt (by decide)
  have hsum : h + s = L := by omega
  have hs : 0 < s := by omega
  have hsL : s ≤ L := Nat.sub_le _ _
  have hSlice := plane_first_slice_nullity u T hhi
  obtain ⟨Q, hQne, hQ, hPrim⟩ := plane_generator _ (by rw [hSlice]; decide)
  let M := planeStack p node (u 0) (u 1) L t
  let W := K1_6.shifts (planePair Q) L s
  have hRank : (M.map (algebraMap (Seeds K) (PlaneField K))).rank + s = 2 * L := by
    rw [plane_stack_rank u, actual_stackRank u]
    omega
  have hker : W.transpose * M = 0 :=
    shifts_annihilate p node (u 0) (u 1) h L s t hsum Q hQ
  obtain ⟨hMP, hattain⟩ := K1_11_1_1.proof K h L s Q hsum hs hQne hPrim
  have hprod (b i : Fin 2) : s * blockDegree Q b i ≤ if b = i then h else L := by
    by_cases hd : blockDegree Q b i = 0
    · simp only [hd, Nat.mul_zero, Nat.zero_le]
    obtain ⟨rows, hdet⟩ := hattain b i (Nat.pos_of_ne_zero hd)
    have hb := K1_11_1_2.proof K L (t + 1) s M W hs hsL hRank hker
      (plane_stack_degree u) hMP b i rows
    rw [hdet] at hb
    simpa only [show L - s = h by omega] using hb
  have hgraph : (fun j => graph p (Q j)) ≠ 0 := by
    intro hz
    apply hQne
    funext j
    change Q j = 0
    by_contra hne
    obtain ⟨b, i⟩ := j
    have hbound : s * blockDegree Q b 0 ≤ L := by
      apply (hprod b 0).trans
      split_ifs
      · exact hL.le
      · exact le_rfl
    have hone : 1 ≤ s := hs
    have hdeg : (Q (b, i)).degreeOf 0 ≤ L :=
      (degreeOf_coordinate Q b 0 i).trans
        ((by simpa only [one_mul] using Nat.mul_le_mul_right (blockDegree Q b 0) hone :
          blockDegree Q b 0 ≤ s * blockDegree Q b 0).trans hbound)
    exact graph_ne_zero p (by decide) _ hne (hdeg.trans_lt (by decide)) (congrFun hz (b, i))
  obtain ⟨c, hc, hgraphQ⟩ := graph_content u T R Q hQ hgraph
  have hdegree (b i : Fin 2) :
      s * (intoFive (planePair Q b)).degreeOf (seedPositions i) ≤
        if b = i then h else L :=
    (Nat.mul_le_mul_left s (intoFive_seed_degree Q b i)).trans (hprod b i)
  refine ⟨{
    U := intoFive (planePair Q 0)
    V := intoFive (planePair Q 1)
    U_omits := ⟨intoFive_omitted Q 0 1 (Or.inl rfl), intoFive_omitted Q 0 2 (Or.inr rfl)⟩
    V_omits := ⟨intoFive_omitted Q 1 1 (Or.inl rfl), intoFive_omitted Q 1 2 (Or.inr rfl)⟩
    heights := ⟨intoFive_height Q 0, intoFive_height Q 1⟩
    bounds := ?_
    primitive := intoFive_primitive Q hPrim
    content := c
    content_ne := hc
    graphU := (graph_intoFive p (planePair Q 0)).trans (graph_pair p Q R.coefficients c hgraphQ 0)
    graphV := (graph_intoFive p (planePair Q 1)).trans (graph_pair p Q R.coefficients c hgraphQ 1)
  }⟩
  have hseedS : seedPositions 0 = 3 := rfl
  have hseedT : seedPositions 1 = 4 := rfl
  exact ⟨by simpa only [hseedS, ite_true] using hdegree 0 0,
    by simpa only [hseedT, ite_eq_right (show (0 : Fin 2) ≠ 1 by decide)] using hdegree 0 1,
    by simpa only [hseedS, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] using hdegree 1 0,
    by simpa only [hseedT, ite_true] using hdegree 1 1⟩

end

end P0_7_1
end PackSource_P0_7_1Proof

section PackSource_P0_7_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace P0_7_2
noncomputable section

open P0 MvPolynomial
open FrobeniusLocator (locator locator_monic)
open K1_11_2 (graph OmitsMessages)
open K1_11_2_1 (graph_natDegree)
open private divide_plane planeLocator degreeOf_le_of_dvd omits_of_dvd native_p_pos
  seedRelPrime parameter_only from ProximityPrize.SubmissionLower.Fast072
open P0_7 (degree_lt_of_product)

private theorem seed_degree_lt {h d : ℕ} (hmax : h ≤ heightCap)
    (hd : (L - h) * d ≤ L) : d < p := by
  have hh : h ≤ 32766 := hmax
  have hd' : d < 4 := degree_lt_of_product _ _ 4 _ hd (by
    change 49145 < (49145 - h) * 4
    omega)
  exact hd'.trans_le (by decide : 4 ≤ p)

/-- A common plane divisor has X-degree zero after graph specialization and
therefore before specialization. The original lift's primitivity removes it. -/
private theorem reduced_relPrime {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : P0_7.IndependentLift R)
    {U V : MvPolynomial (Fin 5) K} (hU : U ≠ 0) (hUo : OmitsMessages U)
    (hS : U.degreeOf 3 < p) (hAdU : U ∣ A.U) (hAdV : V ∣ A.V)
    (hgU : graph p U = Polynomial.C A.content * D.U)
    (hgV : graph p V = Polynomial.C A.content * D.V) :
    IsRelPrime U V := by
  intro d hdU hdV
  let f := (Polynomial.mapRingHom K1_8.seedInclusion).comp (graph (F := K) p).toRingHom
  have hfdU : f d ∣ extendSeed (Polynomial.C A.content * D.U) := by
    rw [← hgU]
    exact _root_.map_dvd f hdU
  have hfdV : f d ∣ extendSeed (Polynomial.C A.content * D.V) := by
    rw [← hgV]
    exact _root_.map_dvd f hdV
  have hu := seedRelPrime D.coprime A.content_ne hfdU hfdV
  have hx := Polynomial.natDegree_eq_zero_of_isUnit hu
  change ((graph p d).map K1_8.seedInclusion).natDegree = 0 at hx
  have hdo := omits_of_dvd hU hUo hdU
  rw [Polynomial.natDegree_map_eq_of_injective K1_8.seedInclusion_injective,
    graph_natDegree p native_p_pos d hdo
      ((degreeOf_le_of_dvd hU hdU 3).trans_lt hS)] at hx
  obtain ⟨q, rfl⟩ := parameter_only hdo hx
  exact (A.primitive q (hdU.trans hAdU) (hdV.trans hAdV)).map
    (rename (![3, 4] : Fin 2 → Fin 5))

theorem proof : P0_7.c2 := by
  intro u T R D hmax A
  have hhcap : T.height ≤ 32766 := hmax
  have hh : T.height ≤ L := hhcap.trans (by decide : 32766 ≤ 49145)
  have hASU := seed_degree_lt hmax (A.bounds.1.trans hh)
  have hASV := seed_degree_lt hmax A.bounds.2.2.1
  obtain ⟨U, hfU, hU, hgU⟩ := divide_plane (fixedNodes R) A.U D.U A.content D.U_ne
    A.content_ne A.U_omits hASU (A.graphU.trans (by simp only [D.U_factor, P0.liftX, K1.liftX]))
  obtain ⟨V, hfV, hV, hgV⟩ := divide_plane (fixedNodes R) A.V D.V A.content D.V_ne
    A.content_ne A.V_omits hASV (A.graphV.trans (by simp only [D.V_factor, P0.liftX, K1.liftX]))
  have hAdU : U ∣ A.U := hfU.symm ▸ dvd_mul_left U (planeLocator (fixedNodes R))
  have hAdV : V ∣ A.V := hfV.symm ▸ dvd_mul_left V (planeLocator (fixedNodes R))
  have hl : planeLocator (fixedNodes R) ≠ 0 := by
    simpa only [planeLocator, EmbeddingLike.map_ne_zero_iff] using
      ((locator_monic node (fixedNodes R)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K)).ne_zero
  have hAu : A.U ≠ 0 := hfU.symm ▸ mul_ne_zero hl hU
  have hAv : A.V ≠ 0 := hfV.symm ▸ mul_ne_zero hl hV
  have hUo := omits_of_dvd hAu A.U_omits hAdU
  have hVo := omits_of_dvd hAv A.V_omits hAdV
  have hUS := (degreeOf_le_of_dvd hAu hAdU 3).trans_lt hASU
  have hVS := (degreeOf_le_of_dvd hAv hAdV 3).trans_lt hASV
  refine ⟨⟨U, V, hUo, hVo, hU, hV, hAdU, hAdV,
    reduced_relPrime D A hU hUo hUS hAdU hAdV hgU hgV, ?_, hgU, hgV⟩⟩
  rw [← graph_natDegree p native_p_pos U hUo hUS,
    ← graph_natDegree p native_p_pos V hVo hVS, hgU, hgV,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr A.content_ne) D.U_ne,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr A.content_ne) D.V_ne,
    Polynomial.natDegree_C, zero_add, zero_add, D.max_degree]

end
end P0_7_2
end PackSource_P0_7_2Proof

section PackSource_P0_11Source
set_option autoImplicit true
namespace P0_11

open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42 (Jet e0 e1 e2 jet_total blockUpper)
open scoped BigOperators

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

private def width (j : Jet) : ℕ :=
  48 * 180217 - 131072 * j.1.val + e1 j + 2 * e2 j

private abbrev SourceIndex := (j : Jet) × Fin (width j)

private theorem width_add (j : Jet) : width j + 2304 = Sol1.C42.width j := by
  have hs := j.1.isLt
  unfold width Sol1.C42.width
  omega

/-- The jet triples are unchanged. Only the X ranges become shorter. -/
private def oldIndex (i : SourceIndex) : Sol1.C42.SourceIndex :=
  ⟨i.1, Fin.castLE (by rw [← width_add i.1]; omega) i.2⟩

private theorem oldIndex_injective : Function.Injective oldIndex := by
  rintro ⟨j, x⟩ ⟨j', x'⟩ h
  have hj : j = j' := congrArg Sigma.fst h
  subst j'
  have hx : x.val = x'.val := congrArg (fun i : Sol1.C42.SourceIndex => i.2.val) h
  rw [Fin.ext hx]

private def columns (i : SourceIndex) : SourceColumn 2 :=
  Sol1.C42.columns (oldIndex i)

private theorem columns_weight_lt (i : SourceIndex) :
    Finsupp.weight (differentialWeight 131072) (columns i).exponent < 48 * 180217 := by
  have hw : i.2.val + 131072 * e0 i.1 + 131071 * e1 i.1 + 131070 * e2 i.1 <
      48 * 180217 := by
    have ht := jet_total i.1
    have hx := i.2.isLt
    unfold width at hx
    omega
  simpa [SourceColumn.weight_exponent, columns, oldIndex, Sol1.C42.columns,
    differentialWeight, Fin.sum_univ_two, Nat.add_assoc, Nat.mul_comm] using hw

private theorem sum_width_add {J : Type*} [Fintype J] (f g : J → ℕ) (d : ℕ)
    (h : ∀ j, f j + d = g j) :
    (∑ j, f j) + Fintype.card J * d = ∑ j, g j := by
  calc
    _ = (∑ j, f j) + ∑ _j : J, d := by simp
    _ = ∑ j, (f j + d) := Finset.sum_add_distrib.symm
    _ = ∑ j, g j := Finset.sum_congr rfl (fun j _ => h j)

private theorem source_card : Fintype.card SourceIndex = 27296569168 := by
  have h := sum_width_add width Sol1.C42.width 2304 width_add
  change (∑ j : Jet, width j) + Fintype.card Jet * 2304 = Sol1.C42.sourceTotal at h
  rw [Sol1.C42.jet_count, Sol1.C42.source_total] at h
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hc : (27296569168 : ℕ) + 7194 * 2304 = 27313144144 := by decide
  exact Nat.add_right_cancel (h.trans hc.symm)

private theorem strict_source_surplus : 262144 * blockUpper < Fintype.card SourceIndex := by
  rw [Sol1.C42.global_rank_allowance, source_card]
  decide

universe u
variable {F : Type u} [Field F]

private theorem global_rank_le
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    ((localConstraintMatrix 48 (fun i => Polynomial.C (domain i))
      (fun i => Polynomial.C (received i)) columns).map
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).rank ≤
      262144 * blockUpper := by
  classical
  let phi := algebraMap (Polynomial F) (FractionRing (Polynomial F))
  let M := (localConstraintMatrix 48 (fun i => Polynomial.C (domain i))
    (fun i => Polynomial.C (received i)) Sol1.C42.columns).map phi
  have hOld := Sol1.C42.global_block_rank_of_origin domain received
    (Sol1.C52.origin_rank (F := FractionRing (Polynomial F)))
  change ((supportedLocalConstraintMatrix 48 (fun i => Polynomial.C (domain i))
    (fun i => Polynomial.C (received i)) Sol1.C42.columns).map phi).rank ≤
    262144 * blockUpper at hOld
  rw [rank_map_supportedLocalConstraintMatrix] at hOld
  change (M.submatrix id oldIndex).rank ≤ 262144 * blockUpper
  exact (Matrix.rank_submatrix_le M id oldIndex).trans hOld

open Classical in
/-- The C42 source at the shortened X widths and the retuned agreement. -/
theorem weighted_uniform_annihilator
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    ∃ Q : DifferentialPolynomial F 2, Q ≠ 0 ∧ jetTotalDegree Q ≤ 64 ∧
      Q.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148 ∧
      ∀ P ∈ ReedSolomon.closePolynomialSet domain received 131073 180217,
        differentialSpecialization Q P = 0 := by
  classical
  let K := FractionRing (Polynomial F)
  let phi : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hphi : Function.Injective phi := IsFractionRing.injective (Polynomial F) K
  have hcolumns : Function.Injective columns := Sol1.C42.columns_injective.comp oldIndex_injective
  obtain ⟨v, _, _, hspan, _, hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le.{u,0,0,u,u} 48 0 64 (fun i => domain i)
      (fun i => Polynomial.C (received i)) (by intro i; simp) columns
      hcolumns (fun i => Sol1.C42.columns_y0_le (oldIndex i)) phi hphi
      (global_rank_le domain received) strict_source_surplus
  let Qs : DifferentialPolynomial (Polynomial F) 2 := SourceColumn.interpolant columns v
  let psi : Polynomial F →+* F := Polynomial.evalRingHom 0
  let Q : DifferentialPolynomial F 2 := MvPolynomial.map psi Qs
  have hQ0 : Q ≠ 0 :=
    SourceColumn.map_interpolant_ne_zero hcolumns psi
      (Ideal.comp_ne_zero_of_span_range_eq_top hspan psi)
  have hjet : jetTotalDegree Q ≤ 64 :=
    SourceColumn.map_interpolant_jetTotalDegree_le psi columns
      (fun i => Sol1.C42.columns_total_le (oldIndex i)) v
  have hwt : Q.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148 :=
    Astra7.generic_source_weight_le psi columns v (Astra7.jetWeight 1 4 3) 148
      (fun i => Astra7.columns_weight148 (oldIndex i))
  refine ⟨Q, hQ0, hjet, hwt, ?_⟩
  intro P hP
  have hPdegree : P.natDegree ≤ 131072 := by
    by_cases hz : P = 0
    · simp [hz]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP.1
      omega
  have hQweight : differentialWeightedDegree 131072 Q < 48 * 180217 :=
    Astra7.generic_source_weight_lt psi columns v (differentialWeight 131072) (48 * 180217)
      (by decide) columns_weight_lt
  have hlocal : ∀ i, SatisfiesLocalConstraints 48 (domain i) (received i) Q := by
    intro i
    have hh := SatisfiesLocalConstraints.map psi 48 (Polynomial.C (domain i))
      (Polynomial.C (received i)) Qs (hconstraints i)
    simpa [psi, Q] using hh
  let indices := ReedSolomon.polynomialAgreementSet domain received P
  apply differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    domain received indices hQweight (fun i _ => hlocal i) P hPdegree
    domain.injective.injOn hP.2
  intro i hi
  exact (Finset.mem_filter.mp hi).2

end
end P0_11
end PackSource_P0_11Source

section PackSource_P0_11Consumer
set_option autoImplicit true
namespace P0_11

open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private abbrev eta : ℚ := (131072 : ℚ) / 49145

abbrev regularCharge : ℚ :=
  (148 : ℚ) / 45 * ((((131072 * 36962583 : ℕ) : ℚ) / 49145) ^ 2)

abbrev firstOrderCharge (h : ℕ) : ℚ :=
  eta * h * Sol1.C42.b h + ((h * (h - 1) : ℕ) : ℚ)

abbrev fullCharge : ℚ := regularCharge + firstOrderCharge 4032

variable {F : Type*} [Field F] [CharP F 2130706433]

private theorem regular_scale {x z : ℚ} (h : x * 45 ≤ 148 * z) :
    x ≤ 148 / 45 * z := by
  rw [div_mul_eq_mul_div₀]
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 45)).2 h

/-- The unchanged weighted chart geometry with the new agreement in the incidence ratio. -/
private theorem regular64_card
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2) (hQ : Q.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148)
    (S : Finset F[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 2)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180217) :
    (S.card : ℚ) ≤ regularCharge := by
  classical
  have hchar : ∀ j : Fin 3, ((1 + 4 * j.val : ℕ) : F) ≠ 0 := by
    intro j
    have hj := j.isLt
    have hpos : 0 < 1 + 4 * j.val := by omega
    have hbound : 1 + 4 * j.val ≤ 9 := by omega
    intro hz
    have hdvd := (CharP.cast_eq_zero_iff F 2130706433 (1 + 4 * j.val)).mp hz
    exact (Nat.not_dvd_of_pos_of_lt hpos (hbound.trans_lt (by decide))) hdvd
  have hh := Astra7.weighted_regular_polynomial_card
    (r := 2) (n := 262144) (k := 131073) (A := 180217)
    1 4 148 (by decide) (by decide) hchar Q hQ
    (by decide) (by decide) domain received Astra7.native_choose_two S
    (fun P hP => (hS P hP).2.1) (fun P hP => (hS P hP).1) hsep
    (fun P hP => by
      simpa [ReedSolomon.closePolynomialSet, ReedSolomon.polynomialAgreementSet] using
        (hS P hP).2.2)
  have hprod : (∏ j : Fin 3, (1 + 4 * j.val)) = 45 := by
    norm_num [Fin.prod_univ_succ]
  have hchart : Astra7.chartBound 2 1 4 148 131073 (2 * 131073) = 36962583 := by decide
  rw [hprod, hchart, Nat.cast_mul] at hh
  exact regular_scale hh

private theorem incidence_one {n A k a d : ℕ} (hn : n - k + 1 = a)
    (hA : A - k + 1 = d) :
    dimensionSensitiveIncidenceProduct n A k 1 1 = (a : ℚ) / d := by
  simp [dimensionSensitiveIncidenceProduct, hn, hA]

private theorem retuned_incidence_one :
    dimensionSensitiveIncidenceProduct 262144 180217 131073 1 1 = eta :=
  incidence_one (by decide) (by decide)

private theorem first_order_charge_ge (h : ℕ) : (h : ℚ) ≤ firstOrderCharge h := by
  have hi : (1 : ℚ) ≤ eta := by
    apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 49145)).2
    rw [one_mul]
    exact_mod_cast (by decide : (49145 : ℕ) ≤ 131072)
  have hb : (1 : ℚ) ≤ (Sol1.C42.b h : ℚ) := by
    exact_mod_cast (by unfold Sol1.C42.b; omega : 1 ≤ Sol1.C42.b h)
  have h1 : (h : ℚ) ≤ eta * h := le_mul_of_one_le_left (Nat.cast_nonneg h) hi
  have h2 : eta * h ≤ eta * h * Sol1.C42.b h :=
    le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hi) (Nat.cast_nonneg h)) hb
  exact (h1.trans h2).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))

private theorem regular_order_one_card_le
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 1) (h : ℕ) (htop : 0 < jetDegree Q (Fin.last 1))
    (hwt : jetTotalDegree Q ≤ h) (S : Finset F[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 1)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180217) :
    (S.card : ℚ) ≤ eta * h * Sol1.C42.b h := by
  have hactual := finite_actualStage_regularSolutions_card_le_dimensionSensitive (A := 180217)
    Q (Fin.last 1)
    (Sol1.C57.highestActiveJet_last_of_pos Q htop) 131073 131073 (by decide) le_rfl
    domain received (by decide) (by decide)
    (fun r hr => Sol1.C40Primitives.native_binomial_guard r (by omega)) S hsep hS
  have hcharge := directJetStageCharge_le_weight_order (Q, Fin.last 1)
    262144 180217 131073 131073 h 1 (by decide) hwt (by simp)
  simpa only [retuned_incidence_one, pow_one, Sol1.C42.b] using hactual.trans hcharge

open Sol1.C57 in
/-- First-order charge, including singular and lower-order roots. -/
private theorem first_order_card_le
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) (h : ℕ) (hbound : h ≤ 4096)
    (hweight : jetTotalDegree Q ≤ h) (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180217) :
    (S.card : ℚ) ≤ firstOrderCharge h := by
  classical
  let G := regularPart 0 Q
  have hsplit := split_weight 0 Q
  have hGweight : jetTotalDegree G ≤ h := by dsimp [G]; omega
  by_cases hb : jetDegree G (Fin.last 1) = 0
  · have hGone : G = 1 := regular_eq_one_of_degree_zero 0 Q hb
    have hlow : ∀ P ∈ S, differentialSpecialization (lowerPart 0 Q) P = 0 := by
      intro P hP
      rcases root_split 0 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P = 0 at hr
        rw [hGone] at hr
        have hz : (1 : F[X]) = 0 := by
          simpa only [differentialSpecialization, map_one] using hr
        exact (one_ne_zero hz).elim
    have hc := order_zero_card_le (lowerPart 0 Q) (lower_ne_zero 0 Q) S hlow
    have hch : S.card ≤ h := by omega
    exact (by exact_mod_cast hch : (S.card : ℚ) ≤ h).trans (first_order_charge_ge h)
  · have hbpos : 0 < jetDegree G (Fin.last 1) := by omega
    have hchar : ringChar F = 0 ∨ jetDegree Q (Fin.last 1) < ringChar F := by
      right
      rw [ringChar.eq F 2130706433]
      have hh := jetDegree_le_total Q (Fin.last 1)
      omega
    let good : F[X] → Prop := fun P => differentialSpecialization G P = 0 ∧
      differentialSpecialization (separant G (Fin.last 1)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P => ¬good P
    have hreg : (regular.card : ℚ) ≤ eta * h * Sol1.C42.b h := by
      apply regular_order_one_card_le domain received G h hbpos hGweight regular
      · intro P hP
        exact ((Finset.mem_filter.mp hP).2).2
      · intro P hP
        have hp := Finset.mem_filter.mp hP
        exact ⟨hp.2.1, (hS P hp.1).2⟩
    let R := exceptionalEquation 0 Q
    have hR : R ≠ 0 := exceptional_ne_zero 0 Q hchar
    have hRweight : jetTotalDegree R ≤ h * (h - 1) :=
      exceptional_weight_sharp 0 Q h hweight (hbpos.trans_le (jetDegree_le_total G (Fin.last 1)))
    have hexc : exceptional.card ≤ h * (h - 1) := by
      apply (order_zero_card_le R hR exceptional ?_).trans hRweight
      intro P hP
      have hp := Finset.mem_filter.mp hP
      rcases root_regular_or_exceptional 0 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hcard : regular.card + exceptional.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ) = (regular.card : ℚ) + exceptional.card := by exact_mod_cast hcard.symm
      _ ≤ firstOrderCharge h := add_le_add hreg (by exact_mod_cast hexc)

open Sol1.C57 in
/-- Retuned order-two consumer with the entire exceptional list charged at order one. -/
theorem weighted_second_order_card
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2) (hQ : Q ≠ 0) (hjet : jetTotalDegree Q ≤ 64)
    (hwt : Q.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180217) :
    (S.card : ℚ) ≤ fullCharge := by
  classical
  let G := regularPart 1 Q
  have hsplit := split_weight 1 Q
  have hGwt : G.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148 :=
    (weightedTotalDegree_le_of_dvd (Astra7.jetWeight 1 4 3) (Astra7.regularPart_dvd 1 Q) hQ).trans hwt
  have hcost : 0 ≤ regularCharge := by unfold regularCharge; positivity
  by_cases hb : jetDegree G (Fin.last 2) = 0
  · have hGone : G = 1 := regular_eq_one_of_degree_zero 1 Q hb
    have hlow : ∀ P ∈ S, P ∈ directJetAgreementSolutions (lowerPart 1 Q)
        domain received 131073 180217 := by
      intro P hP
      refine ⟨?_, (hS P hP).2⟩
      rcases root_split 1 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P = 0 at hr
        rw [hGone] at hr
        have hz : (1 : F[X]) = 0 := by
          simpa only [differentialSpecialization, map_one] using hr
        exact (one_ne_zero hz).elim
    have hlowjet : jetTotalDegree (lowerPart 1 Q) ≤ 4032 := by omega
    have hc := first_order_card_le domain received (lowerPart 1 Q) (lower_ne_zero 1 Q)
      4032 (by decide) hlowjet S hlow
    exact hc.trans (le_add_of_nonneg_left hcost)
  · have hbpos : 0 < jetDegree G (Fin.last 2) := by omega
    have hchar : ringChar F = 0 ∨ jetDegree Q (Fin.last 2) < ringChar F := by
      right
      rw [ringChar.eq F 2130706433]
      have hh := jetDegree_le_total Q (Fin.last 2)
      omega
    let good : F[X] → Prop := fun P => differentialSpecialization G P = 0 ∧
      differentialSpecialization (separant G (Fin.last 2)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P => ¬good P
    have hr : (regular.card : ℚ) ≤ regularCharge := by
      apply regular64_card domain received G hGwt regular
      · intro P hP
        exact ((Finset.mem_filter.mp hP).2).2
      · intro P hP
        have hp := Finset.mem_filter.mp hP
        exact ⟨hp.2.1, (hS P hp.1).2⟩
    let R := exceptionalEquation 1 Q
    have hR : R ≠ 0 := exceptional_ne_zero 1 Q hchar
    have hRjet : jetTotalDegree R ≤ 4032 :=
      exceptional_weight_sharp 1 Q 64 hjet (hbpos.trans_le (jetDegree_le_total G (Fin.last 2)))
    have he : (exceptional.card : ℚ) ≤ firstOrderCharge 4032 := by
      apply first_order_card_le domain received R hR 4032 (by decide) hRjet exceptional
      intro P hP
      have hp := Finset.mem_filter.mp hP
      refine ⟨?_, (hS P hp.1).2⟩
      rcases root_regular_or_exceptional 1 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hc : regular.card + exceptional.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ) = (regular.card : ℚ) + exceptional.card := by exact_mod_cast hc.symm
      _ ≤ fullCharge := add_le_add hr he

end
end P0_11
end PackSource_P0_11Consumer

section PackSource_P0_11Proof
set_option autoImplicit true
namespace P0_11

open Polynomial ReedSolomon.HiddenDerivative

set_option maxRecDepth 10000

noncomputable section

private theorem combine_charges (w t n d c h b e : ℕ) (ht : t ≠ 0) (hd : d ≠ 0) :
    (w : ℚ) / t * ((((n * c : ℕ) : ℚ) / d) ^ 2) + ((n : ℚ) / d * h * b + e) =
      ((w * (n * c)^2 + t * d * n * h * b + t * d^2 * e : ℕ) : ℚ) /
        ((t * d^2 : ℕ) : ℚ) := by
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring

private theorem fraction_eq {n d n' d' : ℕ} (hd : d ≠ 0) (hd' : d' ≠ 0)
    (h : n * d' = n' * d) : (n : ℚ) / d = (n' : ℚ) / d' := by
  apply (div_eq_div_iff (by exact_mod_cast hd) (by exact_mod_cast hd')).2
  exact_mod_cast h

private theorem budget_exact : fullCharge = (386116232609617758524030272 : ℚ) / 12076155125 := by
  have h := combine_charges 148 45 131072 49145 36962583 4032 1056710527 16252992
    (by decide) (by decide)
  change fullCharge = _ at h
  rw [h]
  change ((3475046093486559826716272448 : ℕ) : ℚ) / (108685396125 : ℕ) =
    ((386116232609617758524030272 : ℕ) : ℚ) / (12076155125 : ℕ)
  exact fraction_eq (by decide) (by decide) (by decide)

private theorem fraction_le_nat {n d cap : ℕ} (hd : 0 < d) (h : n ≤ cap * d) :
    (n : ℚ) / d ≤ cap := by
  apply (div_le_iff₀ (by exact_mod_cast hd)).2
  exact_mod_cast h

private theorem budget_le_cap : fullCharge ≤ (P0.listCap : ℚ) := by
  rw [budget_exact]
  exact fraction_le_nat (n := 386116232609617758524030272) (d := 12076155125)
    (by decide) (by decide)

open Classical in
private theorem weighted_complete_list {F : Type*} [Field F] [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    let L := ReedSolomon.closePolynomialSet domain received 131073 180217
    L.Finite ∧ L.ncard ≤ P0.listCap := by
  classical
  let L := ReedSolomon.closePolynomialSet domain received 131073 180217
  change L.Finite ∧ L.ncard ≤ P0.listCap
  obtain ⟨Q, hQ, hjet, hwt, hsound⟩ := weighted_uniform_annihilator domain received
  have hf : ∀ S : Finset F[X], (S : Set F[X]) ⊆ L → S.card ≤ P0.listCap := by
    intro S hS
    have hc := weighted_second_order_card domain received Q hQ hjet hwt S
      (fun P hP => ⟨hsound P (hS hP), hS hP⟩)
    exact Nat.cast_le.mp (hc.trans budget_le_cap)
  have hfin : L.Finite := by
    by_contra hi
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hi (P0.listCap + 1)
    have hh := hf S hS
    rw [hcard] at hh
    exact Nat.not_succ_le_self P0.listCap hh
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hf hfin.toFinset (fun P hP => hfin.mem_toFinset.mp hP)

private theorem closePolynomialSet_decEq {F : Type*} [Field F] {n : ℕ}
    (dec dec' : DecidableEq F) (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) :
    @ReedSolomon.closePolynomialSet F _ dec n domain received k A =
      @ReedSolomon.closePolynomialSet F _ dec' n domain received k A := by
  rw [Subsingleton.elim dec dec']

/-- Every augmented-degree scalar list at agreement 180217 has the retuned weighted cap. -/
theorem proof : P0.c11 := by
  classical
  intro received
  let := Sol1.C42.native_charP
  let L := ReedSolomon.closePolynomialSet P0.node received 131073 180217
  let L' := @ReedSolomon.closePolynomialSet P0.K _ (Classical.decEq P0.K) 262144
    P0.node received 131073 180217
  change L.Finite ∧ L.ncard ≤ P0.listCap
  have he : L = L' := closePolynomialSet_decEq _ _ P0.node received 131073 180217
  rw [he]
  exact weighted_complete_list P0.node received

end
end P0_11
end PackSource_P0_11Proof
