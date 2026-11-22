import ProximityPrize.SubmissionLower.Final50PriceCaps

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Final50PriceMass
open Final50PriceCaps (Band start thresholds order)
open Final50Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (zeroShape)
open Final50PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.sumBelow_add
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]

private def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
  | [] => decide (length = 0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v) &&
        check f (offset + min length 12) (length - 12) vs

private theorem check_sum (f : ℕ → ℕ) (offset length : ℕ) (values : List ℕ)
    (h : check f offset length values = true) :
    P3_6_8_1.sumBelow f (offset + length) = P3_6_8_1.sumBelow f offset + values.sum := by
  induction values generalizing offset length with
  | nil =>
    have hz : length = 0 := of_decide_eq_true h
    simp [hz]
  | cons v vs ih =>
    have hv : P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hr := (Bool.and_eq_true_iff.mp h).2
    have hs : min length 12 + (length - 12) = length := by omega
    calc
      _ = P3_6_8_1.sumBelow f (offset + min length 12 + (length - 12)) := by rw [Nat.add_assoc, hs]
      _ = P3_6_8_1.sumBelow f (offset + min length 12) + vs.sum := ih _ _ hr
      _ = _ := by rw [P3_6_8_1.sumBelow_add, hv, List.sum_cons, Nat.add_assoc]



-- Prefixes depend only on the retained shape, so their checked chunks can be shared.
private def prefixTerm (b j i : ℕ) : ℕ :=
  if j = 0 then Final50Price.symbolCount else
    K1_13_8.fastRemaining ((i+1)*b) ((i+1)*j)

private theorem prefix_eq (r y : Shape) (L : ℕ) :
    P3_6_8_1.sumBelow (fastLayer r y L) L =
      P3_6_8_1.sumBelow (prefixTerm r.b r.j) L := by
  rw [P3_6_8_1.sumBelow_eq, P3_6_8_1.sumBelow_eq]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  simp [fastLayer, prefixTerm, hi', show i+1-L = 0 by omega]

private theorem prefix_add (b j m n p : ℕ) (vs : List ℕ)
    (hp : P3_6_8_1.sumBelow (prefixTerm b j) m = p)
    (hv : check (prefixTerm b j) m n vs = true) :
    P3_6_8_1.sumBelow (prefixTerm b j) (m+n) = p + vs.sum := by
  rw [check_sum _ _ _ _ hv, hp]

private theorem mass_of_split (r y : Shape) (L n p : ℕ) (vs : List ℕ)
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j+y.j)
    (hn : n ≤ 1650 / (r.j+y.j))
    (hcut : 4012 < (L+n+1)*r.b + (n+1)*y.b ∨
             1650 < (L+n+1)*r.j + (n+1)*y.j)
    (hp : P3_6_8_1.sumBelow (prefixTerm r.b r.j) L = p)
    (hv : check (fastLayer r y L) L n vs = true)
    (hneed : p + vs.sum < layerNeed) : availableMass r y L < layerNeed := by
  have hz (i : ℕ) (hi : L+n ≤ i) : fastLayer r y L i = 0 := by
    have h₁ : L+n+1 ≤ i+1 := by omega
    have h₂ : n+1 ≤ i+1-L := by omega
    have hpre : ¬ (r.j = 0 ∧ i < L) := by omega
    rw [fastLayer, if_neg hpre]
    rcases hcut with hb | hidx
    · have h := hb.trans_le (Nat.add_le_add (Nat.mul_le_mul_right r.b h₁)
          (Nat.mul_le_mul_right y.b h₂))
      simp [K1_13_8.fastRemaining, show ¬ _ ≤ 4012 from not_le.mpr h]
    · have h := hidx.trans_le (Nat.add_le_add (Nat.mul_le_mul_right r.j h₁)
          (Nat.mul_le_mul_right y.j h₂))
      exact K1_13_8.fastRemaining_zero h
  rw [mass_eq r y L hr hj, P3_6_8_1.sumBelow_eq,
    K1_13_8.sum_range_truncate (m := L+n) hz (Nat.add_le_add_left hn L),
    ← P3_6_8_1.sumBelow_eq, check_sum _ _ _ _ hv, prefix_eq, hp]
  exact hneed

private theorem prefix_0_0_1 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 1 = 406807694511 :=
  prefix_add 0 0 0 1 0 [406807694511] (rfl) (by decide +kernel)

private theorem prefix_0_0_2 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 2 = 813615389022 :=
  prefix_add 0 0 1 1 406807694511 [406807694511] (prefix_0_0_1) (by decide +kernel)

private theorem prefix_0_0_4 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 4 = 1627230778044 :=
  prefix_add 0 0 2 2 813615389022 [813615389022] (prefix_0_0_2) (by decide +kernel)

private theorem prefix_0_0_5 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 5 = 2034038472555 :=
  prefix_add 0 0 4 1 1627230778044 [406807694511] (prefix_0_0_4) (by decide +kernel)

private theorem prefix_0_0_8 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 8 = 3254461556088 :=
  prefix_add 0 0 5 3 2034038472555 [1220423083533] (prefix_0_0_5) (by decide +kernel)

private theorem prefix_0_0_13 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 13 = 5288500028643 :=
  prefix_add 0 0 8 5 3254461556088 [2034038472555] (prefix_0_0_8) (by decide +kernel)

private theorem prefix_0_0_15 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 15 = 6102115417665 :=
  prefix_add 0 0 13 2 5288500028643 [813615389022] (prefix_0_0_13) (by decide +kernel)

private theorem prefix_0_0_16 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 16 = 6508923112176 :=
  prefix_add 0 0 15 1 6102115417665 [406807694511] (prefix_0_0_15) (by decide +kernel)

private theorem prefix_0_0_18 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 18 = 7322538501198 :=
  prefix_add 0 0 16 2 6508923112176 [813615389022] (prefix_0_0_16) (by decide +kernel)

private theorem prefix_0_0_20 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 20 = 8136153890220 :=
  prefix_add 0 0 18 2 7322538501198 [813615389022] (prefix_0_0_18) (by decide +kernel)

private theorem prefix_0_0_22 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 22 = 8949769279242 :=
  prefix_add 0 0 20 2 8136153890220 [813615389022] (prefix_0_0_20) (by decide +kernel)

private theorem prefix_0_0_23 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 23 = 9356576973753 :=
  prefix_add 0 0 22 1 8949769279242 [406807694511] (prefix_0_0_22) (by decide +kernel)

private theorem prefix_0_0_24 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 24 = 9763384668264 :=
  prefix_add 0 0 23 1 9356576973753 [406807694511] (prefix_0_0_23) (by decide +kernel)

private theorem prefix_0_0_25 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 25 = 10170192362775 :=
  prefix_add 0 0 24 1 9763384668264 [406807694511] (prefix_0_0_24) (by decide +kernel)

private theorem prefix_0_0_27 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 27 = 10983807751797 :=
  prefix_add 0 0 25 2 10170192362775 [813615389022] (prefix_0_0_25) (by decide +kernel)

private theorem prefix_0_0_29 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 29 = 11797423140819 :=
  prefix_add 0 0 27 2 10983807751797 [813615389022] (prefix_0_0_27) (by decide +kernel)

private theorem prefix_0_0_31 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 31 = 12611038529841 :=
  prefix_add 0 0 29 2 11797423140819 [813615389022] (prefix_0_0_29) (by decide +kernel)

private theorem prefix_0_0_33 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 33 = 13424653918863 :=
  prefix_add 0 0 31 2 12611038529841 [813615389022] (prefix_0_0_31) (by decide +kernel)

private theorem prefix_0_0_34 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 34 = 13831461613374 :=
  prefix_add 0 0 33 1 13424653918863 [406807694511] (prefix_0_0_33) (by decide +kernel)

private theorem prefix_0_0_35 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 35 = 14238269307885 :=
  prefix_add 0 0 34 1 13831461613374 [406807694511] (prefix_0_0_34) (by decide +kernel)

private theorem prefix_0_0_36 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 36 = 14645077002396 :=
  prefix_add 0 0 35 1 14238269307885 [406807694511] (prefix_0_0_35) (by decide +kernel)

private theorem prefix_0_0_37 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 37 = 15051884696907 :=
  prefix_add 0 0 36 1 14645077002396 [406807694511] (prefix_0_0_36) (by decide +kernel)

private theorem prefix_0_0_38 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 38 = 15458692391418 :=
  prefix_add 0 0 37 1 15051884696907 [406807694511] (prefix_0_0_37) (by decide +kernel)

private theorem prefix_0_0_39 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 39 = 15865500085929 :=
  prefix_add 0 0 38 1 15458692391418 [406807694511] (prefix_0_0_38) (by decide +kernel)

private theorem prefix_0_0_40 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 40 = 16272307780440 :=
  prefix_add 0 0 39 1 15865500085929 [406807694511] (prefix_0_0_39) (by decide +kernel)

private theorem prefix_0_0_41 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 41 = 16679115474951 :=
  prefix_add 0 0 40 1 16272307780440 [406807694511] (prefix_0_0_40) (by decide +kernel)

private theorem prefix_0_0_42 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 42 = 17085923169462 :=
  prefix_add 0 0 41 1 16679115474951 [406807694511] (prefix_0_0_41) (by decide +kernel)

private theorem prefix_0_0_43 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 43 = 17492730863973 :=
  prefix_add 0 0 42 1 17085923169462 [406807694511] (prefix_0_0_42) (by decide +kernel)

private theorem prefix_0_0_44 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 44 = 17899538558484 :=
  prefix_add 0 0 43 1 17492730863973 [406807694511] (prefix_0_0_43) (by decide +kernel)

private theorem prefix_0_0_45 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 45 = 18306346252995 :=
  prefix_add 0 0 44 1 17899538558484 [406807694511] (prefix_0_0_44) (by decide +kernel)

private theorem prefix_0_0_46 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 46 = 18713153947506 :=
  prefix_add 0 0 45 1 18306346252995 [406807694511] (prefix_0_0_45) (by decide +kernel)

private theorem prefix_0_0_47 :
    P3_6_8_1.sumBelow (prefixTerm 0 0) 47 = 19119961642017 :=
  prefix_add 0 0 46 1 18713153947506 [406807694511] (prefix_0_0_46) (by decide +kernel)

private theorem prefix_1_3_1 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 1 = 406784167900 :=
  prefix_add 1 3 0 1 0 [406784167900] (rfl) (by decide +kernel)

private theorem prefix_1_3_7 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 7 = 2802234295898 :=
  prefix_add 1 3 1 6 406784167900 [2395450127998] (prefix_1_3_1) (by decide +kernel)

private theorem prefix_1_3_10 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 10 = 3971204672684 :=
  prefix_add 1 3 7 3 2802234295898 [1168970376786] (prefix_1_3_7) (by decide +kernel)

private theorem prefix_1_3_12 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 12 = 4740005313959 :=
  prefix_add 1 3 10 2 3971204672684 [768800641275] (prefix_1_3_10) (by decide +kernel)

private theorem prefix_1_3_14 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 14 = 5500464954418 :=
  prefix_add 1 3 12 2 4740005313959 [760459640459] (prefix_1_3_12) (by decide +kernel)

private theorem prefix_1_3_18 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 18 = 6996597965292 :=
  prefix_add 1 3 14 4 5500464954418 [1496133010874] (prefix_1_3_14) (by decide +kernel)

private theorem prefix_1_3_21 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 21 = 8097241733583 :=
  prefix_add 1 3 18 3 6996597965292 [1100643768291] (prefix_1_3_18) (by decide +kernel)

private theorem prefix_1_3_25 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 25 = 9536534840342 :=
  prefix_add 1 3 21 4 8097241733583 [1439293106759] (prefix_1_3_21) (by decide +kernel)

private theorem prefix_1_3_27 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 27 = 10244213165881 :=
  prefix_add 1 3 25 2 9536534840342 [707678325539] (prefix_1_3_25) (by decide +kernel)

private theorem prefix_1_3_28 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 28 = 10595085671051 :=
  prefix_add 1 3 27 1 10244213165881 [350872505170] (prefix_1_3_27) (by decide +kernel)

private theorem prefix_1_3_29 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 29 = 10943990047709 :=
  prefix_add 1 3 28 1 10595085671051 [348904376658] (prefix_1_3_28) (by decide +kernel)

private theorem prefix_1_3_42 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 42 = 15303914876236 :=
  prefix_add 1 3 29 13 10943990047709 [4035953699957, 323971128570] (prefix_1_3_29) (by decide +kernel)

private theorem prefix_1_3_43 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 43 = 15626017824485 :=
  prefix_add 1 3 42 1 15303914876236 [322102948249] (prefix_1_3_42) (by decide +kernel)

private theorem prefix_1_3_45 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 45 = 16264647362425 :=
  prefix_add 1 3 43 2 15626017824485 [638629537940] (prefix_1_3_43) (by decide +kernel)

private theorem prefix_1_3_47 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 47 = 16895888601464 :=
  prefix_add 1 3 45 2 16264647362425 [631241239039] (prefix_1_3_45) (by decide +kernel)

private theorem prefix_1_3_48 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 48 = 17208756130844 :=
  prefix_add 1 3 47 1 16895888601464 [312867529380] (prefix_1_3_47) (by decide +kernel)

private theorem prefix_1_3_51 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 51 = 18136430168795 :=
  prefix_add 1 3 48 3 17208756130844 [927674037951] (prefix_1_3_48) (by decide +kernel)

private theorem prefix_1_3_52 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 52 = 18442035208545 :=
  prefix_add 1 3 51 1 18136430168795 [305605039750] (prefix_1_3_51) (by decide +kernel)

private theorem prefix_1_3_53 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 53 = 18745842002439 :=
  prefix_add 1 3 52 1 18442035208545 [303806793894] (prefix_1_3_52) (by decide +kernel)

private theorem prefix_1_3_54 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 54 = 19047857477634 :=
  prefix_add 1 3 53 1 18745842002439 [302015475195] (prefix_1_3_53) (by decide +kernel)

private theorem prefix_1_3_55 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 55 = 19348088547454 :=
  prefix_add 1 3 54 1 19047857477634 [300231069820] (prefix_1_3_54) (by decide +kernel)

private theorem prefix_1_3_56 :
    P3_6_8_1.sumBelow (prefixTerm 1 3) 56 = 19646542114598 :=
  prefix_add 1 3 55 1 19348088547454 [298453567144] (prefix_1_3_55) (by decide +kernel)

private theorem prefix_2_3_5 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 5 = 2010474425715 :=
  prefix_add 2 3 0 5 0 [2010474425715] (rfl) (by decide +kernel)

private theorem prefix_2_3_7 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 7 = 2798812868156 :=
  prefix_add 2 3 5 2 2010474425715 [788338442441] (prefix_2_3_5) (by decide +kernel)

private theorem prefix_2_3_8 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 8 = 3189620679212 :=
  prefix_add 2 3 7 1 2798812868156 [390807811056] (prefix_2_3_7) (by decide +kernel)

private theorem prefix_2_3_11 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 11 = 4348703743830 :=
  prefix_add 2 3 8 3 3189620679212 [1159083064618] (prefix_2_3_8) (by decide +kernel)

private theorem prefix_2_3_13 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 13 = 5110396157981 :=
  prefix_add 2 3 11 2 4348703743830 [761692414151] (prefix_2_3_11) (by decide +kernel)

private theorem prefix_2_3_15 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 15 = 5863346032020 :=
  prefix_add 2 3 13 2 5110396157981 [752949874039] (prefix_2_3_13) (by decide +kernel)

private theorem prefix_2_3_19 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 19 = 7343294748062 :=
  prefix_add 2 3 15 4 5863346032020 [1479948716042] (prefix_2_3_15) (by decide +kernel)

private theorem prefix_2_3_23 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 23 = 8789100009756 :=
  prefix_add 2 3 19 4 7343294748062 [1445805261694] (prefix_2_3_19) (by decide +kernel)

private theorem prefix_2_3_27 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 27 = 10201307048886 :=
  prefix_add 2 3 23 4 8789100009756 [1412207039130] (prefix_2_3_23) (by decide +kernel)

private theorem prefix_2_3_29 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 29 = 10894980286737 :=
  prefix_add 2 3 27 2 10201307048886 [693673237851] (prefix_2_3_27) (by decide +kernel)

private theorem prefix_2_3_30 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 30 = 11238738736500 :=
  prefix_add 2 3 29 1 10894980286737 [343758449763] (prefix_2_3_29) (by decide +kernel)

private theorem prefix_2_3_37 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 37 = 13588366553051 :=
  prefix_add 2 3 30 7 11238738736500 [2349627816551] (prefix_2_3_30) (by decide +kernel)

private theorem prefix_2_3_38 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 38 = 13916029718972 :=
  prefix_add 2 3 37 1 13588366553051 [327663165921] (prefix_2_3_37) (by decide +kernel)

private theorem prefix_2_3_40 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 40 = 14565439885500 :=
  prefix_add 2 3 38 2 13916029718972 [649410166528] (prefix_2_3_38) (by decide +kernel)

private theorem prefix_2_3_42 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 42 = 15207016320090 :=
  prefix_add 2 3 40 2 14565439885500 [641576434590] (prefix_2_3_40) (by decide +kernel)

private theorem prefix_2_3_44 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 44 = 15840824144420 :=
  prefix_add 2 3 42 2 15207016320090 [633807824330] (prefix_2_3_42) (by decide +kernel)

private theorem prefix_2_3_46 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 46 = 16466928178932 :=
  prefix_add 2 3 44 2 15840824144420 [626104034512] (prefix_2_3_44) (by decide +kernel)

private theorem prefix_2_3_47 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 47 = 16777111448916 :=
  prefix_add 2 3 46 1 16466928178932 [310183269984] (prefix_2_3_46) (by decide +kernel)

private theorem prefix_2_3_49 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 49 = 17391780678962 :=
  prefix_add 2 3 47 2 16777111448916 [614669230046] (prefix_2_3_47) (by decide +kernel)

private theorem prefix_2_3_50 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 50 = 17696282656250 :=
  prefix_add 2 3 49 1 17391780678962 [304501977288] (prefix_2_3_49) (by decide +kernel)

private theorem prefix_2_3_51 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 51 = 17998906854750 :=
  prefix_add 2 3 50 1 17696282656250 [302624198500] (prefix_2_3_50) (by decide +kernel)

private theorem prefix_2_3_52 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 52 = 18299661237000 :=
  prefix_add 2 3 51 1 17998906854750 [300754382250] (prefix_2_3_51) (by decide +kernel)

private theorem prefix_2_3_53 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 53 = 18598553745231 :=
  prefix_add 2 3 52 1 18299661237000 [298892508231] (prefix_2_3_52) (by decide +kernel)

private theorem prefix_2_3_54 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 54 = 18895592304540 :=
  prefix_add 2 3 53 1 18598553745231 [297038559309] (prefix_2_3_53) (by decide +kernel)

private theorem prefix_2_3_55 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 55 = 19190784819740 :=
  prefix_add 2 3 54 1 18895592304540 [295192515200] (prefix_2_3_54) (by decide +kernel)

private theorem prefix_2_3_56 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 56 = 19484139178532 :=
  prefix_add 2 3 55 1 19190784819740 [293354358792] (prefix_2_3_55) (by decide +kernel)

private theorem prefix_2_3_57 :
    P3_6_8_1.sumBelow (prefixTerm 2 3) 57 = 19775663248356 :=
  prefix_add 2 3 56 1 19484139178532 [291524069824] (prefix_2_3_56) (by decide +kernel)

private theorem prefix_2_4_1 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 1 = 405977702900 :=
  prefix_add 2 4 0 1 0 [405977702900] (rfl) (by decide +kernel)

private theorem prefix_2_4_7 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 7 = 2780047658398 :=
  prefix_add 2 4 1 6 405977702900 [2374069955498] (prefix_2_4_1) (by decide +kernel)

private theorem prefix_2_4_11 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 11 = 4304968480160 :=
  prefix_add 2 4 7 4 2780047658398 [1524920821762] (prefix_2_4_7) (by decide +kernel)

private theorem prefix_2_4_15 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 15 = 5784725383338 :=
  prefix_add 2 4 11 4 4304968480160 [1479756903178] (prefix_2_4_11) (by decide +kernel)

private theorem prefix_2_4_20 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 20 = 7572289975476 :=
  prefix_add 2 4 15 5 5784725383338 [1787564592138] (prefix_2_4_15) (by decide +kernel)

private theorem prefix_2_4_24 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 24 = 8953728392296 :=
  prefix_add 2 4 20 4 7572289975476 [1381438416820] (prefix_2_4_20) (by decide +kernel)

private theorem prefix_2_4_28 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 28 = 10292914821374 :=
  prefix_add 2 4 24 4 8953728392296 [1339186429078] (prefix_2_4_24) (by decide +kernel)

private theorem prefix_2_4_31 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 31 = 11270104078806 :=
  prefix_add 2 4 28 3 10292914821374 [977189257432] (prefix_2_4_28) (by decide +kernel)

private theorem prefix_2_4_32 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 32 = 11590725229536 :=
  prefix_add 2 4 31 1 11270104078806 [320621150730] (prefix_2_4_31) (by decide +kernel)

private theorem prefix_2_4_33 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 33 = 11908814585228 :=
  prefix_add 2 4 32 1 11590725229536 [318089355692] (prefix_2_4_32) (by decide +kernel)

private theorem prefix_2_4_45 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 45 = 15533265224864 :=
  prefix_add 2 4 33 12 11908814585228 [3624450639636] (prefix_2_4_33) (by decide +kernel)

private theorem prefix_2_4_46 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 46 = 15819651672484 :=
  prefix_add 2 4 45 1 15533265224864 [286386447620] (prefix_2_4_45) (by decide +kernel)

private theorem prefix_2_4_49 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 49 = 16664781571364 :=
  prefix_add 2 4 46 3 15819651672484 [845129898880] (prefix_2_4_46) (by decide +kernel)

private theorem prefix_2_4_51 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 51 = 17216639192470 :=
  prefix_add 2 4 49 2 16664781571364 [551857621106] (prefix_2_4_49) (by decide +kernel)

private theorem prefix_2_4_53 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 53 = 17759366579862 :=
  prefix_add 2 4 51 2 17216639192470 [542727387392] (prefix_2_4_51) (by decide +kernel)

private theorem prefix_2_4_55 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 55 = 18293065604750 :=
  prefix_add 2 4 53 2 17759366579862 [533699024888] (prefix_2_4_53) (by decide +kernel)

private theorem prefix_2_4_56 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 56 = 18556561155544 :=
  prefix_add 2 4 55 1 18293065604750 [263495550794] (prefix_2_4_55) (by decide +kernel)

private theorem prefix_2_4_57 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 57 = 18817837552212 :=
  prefix_add 2 4 56 1 18556561155544 [261276396668] (prefix_2_4_56) (by decide +kernel)

private theorem prefix_2_4_58 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 58 = 19076907362880 :=
  prefix_add 2 4 57 1 18817837552212 [259069810668] (prefix_2_4_57) (by decide +kernel)

private theorem prefix_2_4_59 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 59 = 19333783121424 :=
  prefix_add 2 4 58 1 19076907362880 [256875758544] (prefix_2_4_58) (by decide +kernel)

private theorem prefix_2_4_60 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 60 = 19588477324052 :=
  prefix_add 2 4 59 1 19333783121424 [254694202628] (prefix_2_4_59) (by decide +kernel)

private theorem prefix_2_4_61 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 61 = 19841002429312 :=
  prefix_add 2 4 60 1 19588477324052 [252525105260] (prefix_2_4_60) (by decide +kernel)

private theorem prefix_2_4_62 :
    P3_6_8_1.sumBelow (prefixTerm 2 4) 62 = 20091370861522 :=
  prefix_add 2 4 61 1 19841002429312 [250368432210] (prefix_2_4_61) (by decide +kernel)

private theorem prefix_2_5_1 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 1 = 405296820225 :=
  prefix_add 2 5 0 1 0 [405296820225] (rfl) (by decide +kernel)

private theorem prefix_2_5_3 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 3 = 1204989913167 :=
  prefix_add 2 5 1 2 405296820225 [799693092942] (prefix_2_5_1) (by decide +kernel)

private theorem prefix_2_5_16 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 16 = 6059871817121 :=
  prefix_add 2 5 3 13 1204989913167 [4501951139360, 352930764594] (prefix_2_5_3) (by decide +kernel)

private theorem prefix_2_5_21 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 21 = 7775101417274 :=
  prefix_add 2 5 16 5 6059871817121 [1715229600153] (prefix_2_5_16) (by decide +kernel)

private theorem prefix_2_5_32 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 32 = 11268842645056 :=
  prefix_add 2 5 21 11 7775101417274 [3493741227782] (prefix_2_5_21) (by decide +kernel)

private theorem prefix_2_5_33 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 33 = 11568066003952 :=
  prefix_add 2 5 32 1 11268842645056 [299223358896] (prefix_2_5_32) (by decide +kernel)

private theorem prefix_2_5_43 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 43 = 14399689006468 :=
  prefix_add 2 5 33 10 11568066003952 [2831623002516] (prefix_2_5_33) (by decide +kernel)

private theorem prefix_2_5_49 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 49 = 15963742028049 :=
  prefix_add 2 5 43 6 14399689006468 [1564053021581] (prefix_2_5_43) (by decide +kernel)

private theorem prefix_2_5_57 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 57 = 17900206960224 :=
  prefix_add 2 5 49 8 15963742028049 [1936464932175] (prefix_2_5_49) (by decide +kernel)

private theorem prefix_2_5_59 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 59 = 18358713237292 :=
  prefix_add 2 5 57 2 17900206960224 [458506277068] (prefix_2_5_57) (by decide +kernel)

private theorem prefix_2_5_60 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 60 = 18584225120910 :=
  prefix_add 2 5 59 1 18358713237292 [225511883618] (prefix_2_5_59) (by decide +kernel)

private theorem prefix_2_5_62 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 62 = 19027856472931 :=
  prefix_add 2 5 60 2 18584225120910 [443631352021] (prefix_2_5_60) (by decide +kernel)

private theorem prefix_2_5_65 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 65 = 19675090861219 :=
  prefix_add 2 5 62 3 19027856472931 [647234388288] (prefix_2_5_62) (by decide +kernel)

private theorem prefix_2_5_66 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 66 = 19886050082250 :=
  prefix_add 2 5 65 1 19675090861219 [210959221031] (prefix_2_5_65) (by decide +kernel)

private theorem prefix_2_5_67 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 67 = 20094645966560 :=
  prefix_add 2 5 66 1 19886050082250 [208595884310] (prefix_2_5_66) (by decide +kernel)

private theorem prefix_2_5_68 :
    P3_6_8_1.sumBelow (prefixTerm 2 5) 68 = 20300896090970 :=
  prefix_add 2 5 67 1 20094645966560 [206250124410] (prefix_2_5_67) (by decide +kernel)

private theorem prefix_2_6_11 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 11 = 4218526636379 :=
  prefix_add 2 6 0 11 0 [4218526636379] (rfl) (by decide +kernel)

private theorem prefix_2_6_21 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 21 = 7630748804483 :=
  prefix_add 2 6 11 10 4218526636379 [3412222168104] (prefix_2_6_11) (by decide +kernel)

private theorem prefix_2_6_24 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 24 = 8580398800522 :=
  prefix_add 2 6 21 3 7630748804483 [949649996039] (prefix_2_6_21) (by decide +kernel)

private theorem prefix_2_6_37 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 37 = 12326006266759 :=
  prefix_add 2 6 24 13 8580398800522 [3477982715867, 267624750370] (prefix_2_6_24) (by decide +kernel)

private theorem prefix_2_6_41 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 41 = 13363863064666 :=
  prefix_add 2 6 37 4 12326006266759 [1037856797907] (prefix_2_6_37) (by decide +kernel)

private theorem prefix_2_6_43 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 43 = 13863575745395 :=
  prefix_add 2 6 41 2 13363863064666 [499712680729] (prefix_2_6_41) (by decide +kernel)

private theorem prefix_2_6_46 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 46 = 14589713536243 :=
  prefix_add 2 6 43 3 13863575745395 [726137790848] (prefix_2_6_43) (by decide +kernel)

private theorem prefix_2_6_50 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 50 = 15515243736970 :=
  prefix_add 2 6 46 4 14589713536243 [925530200727] (prefix_2_6_46) (by decide +kernel)

private theorem prefix_2_6_54 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 54 = 16393523228469 :=
  prefix_add 2 6 50 4 15515243736970 [878279491499] (prefix_2_6_50) (by decide +kernel)

private theorem prefix_2_6_56 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 56 = 16815447493922 :=
  prefix_add 2 6 54 2 16393523228469 [421924265453] (prefix_2_6_54) (by decide +kernel)

private theorem prefix_2_6_59 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 59 = 17427373656031 :=
  prefix_add 2 6 56 3 16815447493922 [611926162109] (prefix_2_6_56) (by decide +kernel)

private theorem prefix_2_6_61 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 61 = 17821637610149 :=
  prefix_add 2 6 59 2 17427373656031 [394263954118] (prefix_2_6_59) (by decide +kernel)

private theorem prefix_2_6_62 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 62 = 18014736648519 :=
  prefix_add 2 6 61 1 17821637610149 [193099038370] (prefix_2_6_61) (by decide +kernel)

private theorem prefix_2_6_63 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 63 = 18205179316548 :=
  prefix_add 2 6 62 1 18014736648519 [190442668029] (prefix_2_6_62) (by decide +kernel)

private theorem prefix_2_6_64 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 64 = 18392989678768 :=
  prefix_add 2 6 63 1 18205179316548 [187810362220] (prefix_2_6_63) (by decide +kernel)

private theorem prefix_2_6_65 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 65 = 18578191697936 :=
  prefix_add 2 6 64 1 18392989678768 [185202019168] (prefix_2_6_64) (by decide +kernel)

private theorem prefix_2_6_67 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 67 = 18940866048621 :=
  prefix_add 2 6 65 2 18578191697936 [362674350685] (prefix_2_6_65) (by decide +kernel)

private theorem prefix_2_6_69 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 69 = 19293392031055 :=
  prefix_add 2 6 67 2 18940866048621 [352525982434] (prefix_2_6_67) (by decide +kernel)

private theorem prefix_2_6_70 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 70 = 19465908206633 :=
  prefix_add 2 6 69 1 19293392031055 [172516175578] (prefix_2_6_69) (by decide +kernel)

private theorem prefix_2_6_71 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 71 = 19635957672378 :=
  prefix_add 2 6 70 1 19465908206633 [170049465745] (prefix_2_6_70) (by decide +kernel)

private theorem prefix_2_6_72 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 72 = 19803563675598 :=
  prefix_add 2 6 71 1 19635957672378 [167606003220] (prefix_2_6_71) (by decide +kernel)

private theorem prefix_2_6_73 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 73 = 19968749360962 :=
  prefix_add 2 6 72 1 19803563675598 [165185685364] (prefix_2_6_72) (by decide +kernel)

private theorem prefix_2_6_75 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 75 = 20291951842955 :=
  prefix_add 2 6 73 2 19968749360962 [323202481993] (prefix_2_6_73) (by decide +kernel)

private theorem prefix_2_6_76 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 76 = 20450014414755 :=
  prefix_add 2 6 75 1 20291951842955 [158062571800] (prefix_2_6_75) (by decide +kernel)

private theorem prefix_2_6_77 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 77 = 20605748218825 :=
  prefix_add 2 6 76 1 20450014414755 [155733804070] (prefix_2_6_76) (by decide +kernel)

private theorem prefix_2_6_78 :
    P3_6_8_1.sumBelow (prefixTerm 2 6) 78 = 20759175885019 :=
  prefix_add 2 6 77 1 20605748218825 [153427666194] (prefix_2_6_77) (by decide +kernel)

private theorem prefix_3_7_20 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 20 = 7154800101692 :=
  prefix_add 3 7 0 20 0 [4518321774336, 2636478327356] (rfl) (by decide +kernel)

private theorem prefix_3_7_38 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 38 = 12106716429931 :=
  prefix_add 3 7 20 18 7154800101692 [3442789566068, 1509126762171] (prefix_3_7_20) (by decide +kernel)

private theorem prefix_3_7_39 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 39 = 12345309926026 :=
  prefix_add 3 7 38 1 12106716429931 [238593496095] (prefix_3_7_38) (by decide +kernel)

private theorem prefix_3_7_41 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 41 = 12811744803230 :=
  prefix_add 3 7 39 2 12345309926026 [466434877204] (prefix_3_7_39) (by decide +kernel)

private theorem prefix_3_7_59 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 59 = 16409022839062 :=
  prefix_add 3 7 41 18 12811744803230 [2512493764084, 1084784271748] (prefix_3_7_41) (by decide +kernel)

private theorem prefix_3_7_63 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 63 = 17073628995194 :=
  prefix_add 3 7 59 4 16409022839062 [664606156132] (prefix_3_7_59) (by decide +kernel)

private theorem prefix_3_7_65 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 65 = 17389136388274 :=
  prefix_add 3 7 63 2 17073628995194 [315507393080] (prefix_3_7_63) (by decide +kernel)

private theorem prefix_3_7_72 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 72 = 18409550143796 :=
  prefix_add 3 7 65 7 17389136388274 [1020413755522] (prefix_3_7_65) (by decide +kernel)

private theorem prefix_3_7_79 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 79 = 19307536852454 :=
  prefix_add 3 7 72 7 18409550143796 [897986708658] (prefix_3_7_72) (by decide +kernel)

private theorem prefix_3_7_83 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 83 = 19769638791534 :=
  prefix_add 3 7 79 4 19307536852454 [462101939080] (prefix_3_7_79) (by decide +kernel)

private theorem prefix_3_7_86 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 86 = 20093272080751 :=
  prefix_add 3 7 83 3 19769638791534 [323633289217] (prefix_3_7_83) (by decide +kernel)

private theorem prefix_3_7_88 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 88 = 20298524140798 :=
  prefix_add 3 7 86 2 20093272080751 [205252060047] (prefix_3_7_86) (by decide +kernel)

private theorem prefix_3_7_90 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 90 = 20495631246850 :=
  prefix_add 3 7 88 2 20298524140798 [197107106052] (prefix_3_7_88) (by decide +kernel)

private theorem prefix_3_7_92 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 92 = 20684811110080 :=
  prefix_add 3 7 90 2 20495631246850 [189179863230] (prefix_3_7_90) (by decide +kernel)

private theorem prefix_3_7_94 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 94 = 20866278531239 :=
  prefix_add 3 7 92 2 20684811110080 [181467421159] (prefix_3_7_92) (by decide +kernel)

private theorem prefix_3_7_95 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 95 = 20954186403764 :=
  prefix_add 3 7 94 1 20866278531239 [87907872525] (prefix_3_7_94) (by decide +kernel)

private theorem prefix_3_7_96 :
    P3_6_8_1.sumBelow (prefixTerm 3 7) 96 = 21040245395728 :=
  prefix_add 3 7 95 1 20954186403764 [86058991964] (prefix_3_7_95) (by decide +kernel)

private theorem prefix_4_6_16 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 16 = 5942786444100 :=
  prefix_add 4 6 0 16 0 [4559471596449, 1383314847651] (rfl) (by decide +kernel)

private theorem prefix_4_6_25 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 25 = 8822079847350 :=
  prefix_add 4 6 16 9 5942786444100 [2879293403250] (prefix_4_6_16) (by decide +kernel)

private theorem prefix_4_6_35 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 35 = 11666174980215 :=
  prefix_add 4 6 25 10 8822079847350 [2844095132865] (prefix_4_6_25) (by decide +kernel)

private theorem prefix_4_6_38 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 38 = 12450989984631 :=
  prefix_add 4 6 35 3 11666174980215 [784815004416] (prefix_4_6_35) (by decide +kernel)

private theorem prefix_4_6_44 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 44 = 13931072174217 :=
  prefix_add 4 6 38 6 12450989984631 [1480082189586] (prefix_4_6_38) (by decide +kernel)

private theorem prefix_4_6_49 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 49 = 15077040813912 :=
  prefix_add 4 6 44 5 13931072174217 [1145968639695] (prefix_4_6_44) (by decide +kernel)

private theorem prefix_4_6_57 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 57 = 16754679603054 :=
  prefix_add 4 6 49 8 15077040813912 [1677638789142] (prefix_4_6_49) (by decide +kernel)

private theorem prefix_4_6_59 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 59 = 17145497957877 :=
  prefix_add 4 6 57 2 16754679603054 [390818354823] (prefix_4_6_57) (by decide +kernel)

private theorem prefix_4_6_62 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 62 = 17711165342649 :=
  prefix_add 4 6 59 3 17145497957877 [565667384772] (prefix_4_6_59) (by decide +kernel)

private theorem prefix_4_6_70 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 70 = 19104030740655 :=
  prefix_add 4 6 62 8 17711165342649 [1392865398006] (prefix_4_6_62) (by decide +kernel)

private theorem prefix_4_6_72 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 72 = 19427100609114 :=
  prefix_add 4 6 70 2 19104030740655 [323069868459] (prefix_4_6_70) (by decide +kernel)

private theorem prefix_4_6_74 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 74 = 19740517599012 :=
  prefix_add 4 6 72 2 19427100609114 [313416989898] (prefix_4_6_72) (by decide +kernel)

private theorem prefix_4_6_75 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 75 = 19893668506425 :=
  prefix_add 4 6 74 1 19740517599012 [153150907413] (prefix_4_6_74) (by decide +kernel)

private theorem prefix_4_6_76 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 76 = 20044480602225 :=
  prefix_add 4 6 75 1 19893668506425 [150812095800] (prefix_4_6_75) (by decide +kernel)

private theorem prefix_4_6_77 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 77 = 20192978395359 :=
  prefix_add 4 6 76 1 20044480602225 [148497793134] (prefix_4_6_76) (by decide +kernel)

private theorem prefix_4_6_78 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 78 = 20339186254101 :=
  prefix_add 4 6 77 1 20192978395359 [146207858742] (prefix_4_6_77) (by decide +kernel)

private theorem prefix_4_6_79 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 79 = 20483128406232 :=
  prefix_add 4 6 78 1 20339186254101 [143942152131] (prefix_4_6_78) (by decide +kernel)

private theorem prefix_4_6_80 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 80 = 20624828939220 :=
  prefix_add 4 6 79 1 20483128406232 [141700532988] (prefix_4_6_79) (by decide +kernel)

private theorem prefix_4_6_81 :
    P3_6_8_1.sumBelow (prefixTerm 4 6) 81 = 20764311800400 :=
  prefix_add 4 6 80 1 20624828939220 [139482861180] (prefix_4_6_80) (by decide +kernel)

private theorem prefix_7_7_76 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 76 = 18207992744206 :=
  prefix_add 7 7 0 76 0 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 479441848130] (rfl) (by decide +kernel)

private theorem prefix_7_7_82 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 82 = 18858483630234 :=
  prefix_add 7 7 76 6 18207992744206 [650490886028] (prefix_7_7_76) (by decide +kernel)

private theorem prefix_7_7_94 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 94 = 19937008185735 :=
  prefix_add 7 7 82 12 18858483630234 [1078524555501] (prefix_7_7_82) (by decide +kernel)

private theorem prefix_7_7_100 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 100 = 20377744337378 :=
  prefix_add 7 7 94 6 19937008185735 [440736151643] (prefix_7_7_94) (by decide +kernel)

private theorem prefix_7_7_105 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 105 = 20700650876832 :=
  prefix_add 7 7 100 5 20377744337378 [322906539454] (prefix_7_7_100) (by decide +kernel)

private theorem prefix_7_7_107 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 107 = 20819304825666 :=
  prefix_add 7 7 105 2 20700650876832 [118653948834] (prefix_7_7_105) (by decide +kernel)

private theorem prefix_7_7_108 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 108 = 20876480145516 :=
  prefix_add 7 7 107 1 20819304825666 [57175319850] (prefix_7_7_107) (by decide +kernel)

private theorem prefix_7_7_109 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 109 = 20932253685332 :=
  prefix_add 7 7 108 1 20876480145516 [55773539816] (prefix_7_7_108) (by decide +kernel)

private theorem prefix_7_7_110 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 110 = 20986649632805 :=
  prefix_add 7 7 109 1 20932253685332 [54395947473] (prefix_7_7_109) (by decide +kernel)

private theorem prefix_7_7_111 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 111 = 21039691928402 :=
  prefix_add 7 7 110 1 20986649632805 [53042295597] (prefix_7_7_110) (by decide +kernel)

private theorem prefix_7_7_112 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 112 = 21091404269042 :=
  prefix_add 7 7 111 1 21039691928402 [51712340640] (prefix_7_7_111) (by decide +kernel)

private theorem prefix_7_7_113 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 113 = 21141810109106 :=
  prefix_add 7 7 112 1 21091404269042 [50405840064] (prefix_7_7_112) (by decide +kernel)

private theorem prefix_7_7_114 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 114 = 21190932661156 :=
  prefix_add 7 7 113 1 21141810109106 [49122552050] (prefix_7_7_113) (by decide +kernel)

private theorem prefix_7_7_115 :
    P3_6_8_1.sumBelow (prefixTerm 7 7) 115 = 21238794894016 :=
  prefix_add 7 7 114 1 21190932661156 [47862232860] (prefix_7_7_114) (by decide +kernel)

private theorem prefix_12_6_42 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 42 = 12792309617276 :=
  prefix_add 12 6 0 42 0 [4487981692249, 3778312455973, 3156060990097, 1369954478957] (rfl) (by decide +kernel)

private theorem prefix_12_6_65 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 65 = 16951228551556 :=
  prefix_add 12 6 42 23 12792309617276 [2370357086383, 1788561847897] (prefix_12_6_42) (by decide +kernel)

private theorem prefix_12_6_67 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 67 = 17240966535111 :=
  prefix_add 12 6 65 2 16951228551556 [289737983555] (prefix_12_6_65) (by decide +kernel)

private theorem prefix_12_6_87 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 87 = 19620080935754 :=
  prefix_add 12 6 67 20 17240966535111 [1533395736433, 845718664210] (prefix_12_6_67) (by decide +kernel)

private theorem prefix_12_6_89 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 89 = 19811655837798 :=
  prefix_add 12 6 87 2 19620080935754 [191574902044] (prefix_12_6_87) (by decide +kernel)

private theorem prefix_12_6_92 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 92 = 20085050849821 :=
  prefix_add 12 6 89 3 19811655837798 [273395012023] (prefix_12_6_89) (by decide +kernel)

private theorem prefix_12_6_97 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 97 = 20505275715388 :=
  prefix_add 12 6 92 5 20085050849821 [420224865567] (prefix_12_6_92) (by decide +kernel)

private theorem prefix_12_6_98 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 98 = 20584243740942 :=
  prefix_add 12 6 97 1 20505275715388 [78968025554] (prefix_12_6_97) (by decide +kernel)

private theorem prefix_12_6_99 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 99 = 20661579626127 :=
  prefix_add 12 6 98 1 20584243740942 [77335885185] (prefix_12_6_98) (by decide +kernel)

private theorem prefix_12_6_100 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 100 = 20737308635615 :=
  prefix_add 12 6 99 1 20661579626127 [75729009488] (prefix_12_6_99) (by decide +kernel)

private theorem prefix_12_6_101 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 101 = 20811455774065 :=
  prefix_add 12 6 100 1 20737308635615 [74147138450] (prefix_12_6_100) (by decide +kernel)

private theorem prefix_12_6_102 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 102 = 20884045787455 :=
  prefix_add 12 6 101 1 20811455774065 [72590013390] (prefix_12_6_101) (by decide +kernel)

private theorem prefix_12_6_104 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 104 = 21024652137554 :=
  prefix_add 12 6 102 2 20884045787455 [140606350099] (prefix_12_6_102) (by decide +kernel)

private theorem prefix_12_6_105 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 105 = 21092716684802 :=
  prefix_add 12 6 104 1 21024652137554 [68064547248] (prefix_12_6_104) (by decide +kernel)

private theorem prefix_12_6_106 :
    P3_6_8_1.sumBelow (prefixTerm 12 6) 106 = 21159320530732 :=
  prefix_add 12 6 105 1 21092716684802 [66603845930] (prefix_12_6_105) (by decide +kernel)

private theorem prefix_14_6_72 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 72 = 17544785276694 :=
  prefix_add 14 6 0 72 0 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499] (rfl) (by decide +kernel)

private theorem prefix_14_6_78 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 78 = 18239238099511 :=
  prefix_add 14 6 72 6 17544785276694 [694452822817] (prefix_14_6_72) (by decide +kernel)

private theorem prefix_14_6_90 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 90 = 19399841570580 :=
  prefix_add 14 6 78 12 18239238099511 [1160603471069] (prefix_14_6_78) (by decide +kernel)

private theorem prefix_14_6_93 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 93 = 19647296159201 :=
  prefix_add 14 6 90 3 19399841570580 [247454588621] (prefix_14_6_90) (by decide +kernel)

private theorem prefix_14_6_96 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 96 = 19879239635560 :=
  prefix_add 14 6 93 3 19647296159201 [231943476359] (prefix_14_6_93) (by decide +kernel)

private theorem prefix_14_6_101 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 101 = 20233343814275 :=
  prefix_add 14 6 96 5 19879239635560 [354104178715] (prefix_14_6_96) (by decide +kernel)

private theorem prefix_14_6_104 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 104 = 20427480521422 :=
  prefix_add 14 6 101 3 20233343814275 [194136707147] (prefix_14_6_101) (by decide +kernel)

private theorem prefix_14_6_105 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 105 = 20489290767610 :=
  prefix_add 14 6 104 1 20427480521422 [61810246188] (prefix_14_6_104) (by decide +kernel)

private theorem prefix_14_6_111 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 111 = 20831383824680 :=
  prefix_add 14 6 105 6 20489290767610 [342093057070] (prefix_14_6_105) (by decide +kernel)

private theorem prefix_14_6_112 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 112 = 20883824443524 :=
  prefix_add 14 6 111 1 20831383824680 [52440618844] (prefix_14_6_111) (by decide +kernel)

private theorem prefix_14_6_113 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 113 = 20935019115796 :=
  prefix_add 14 6 112 1 20883824443524 [51194672272] (prefix_14_6_112) (by decide +kernel)

private theorem prefix_14_6_115 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 115 = 21033759657005 :=
  prefix_add 14 6 113 2 20935019115796 [98740541209] (prefix_14_6_113) (by decide +kernel)

private theorem prefix_14_6_116 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 116 = 21081349375245 :=
  prefix_add 14 6 115 1 21033759657005 [47589718240] (prefix_14_6_115) (by decide +kernel)

private theorem prefix_14_6_117 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 117 = 21127780848759 :=
  prefix_add 14 6 116 1 21081349375245 [46431473514] (prefix_14_6_116) (by decide +kernel)

private theorem prefix_14_6_118 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 118 = 21173075340601 :=
  prefix_add 14 6 117 1 21127780848759 [45294491842] (prefix_14_6_117) (by decide +kernel)

private theorem prefix_14_6_119 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 119 = 21217253852102 :=
  prefix_add 14 6 118 1 21173075340601 [44178511501] (prefix_14_6_118) (by decide +kernel)

private theorem prefix_14_6_120 :
    P3_6_8_1.sumBelow (prefixTerm 14 6) 120 = 21260337124490 :=
  prefix_add 14 6 119 1 21217253852102 [43083272388] (prefix_14_6_119) (by decide +kernel)

private theorem m0_0 : availableMass (start .empty) ⟨3,9,0⟩ 5 < layerNeed :=
  mass_of_split _ _ 5 183 2034038472555 [4419454632432, 3596534841372, 2880841206984, 2265453291444, 1743314608032, 1307232621132, 949878746232, 663788349924, 441360749904, 274859214972, 156410965032, 78007171092, 31502955264, 8617390764, 933501912, 1782176]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_5 (by decide +kernel) (by decide +kernel)

private theorem m0_1 : availableMass (start .empty) ⟨4,12,0⟩ 13 < layerNeed :=
  mass_of_split _ _ 13 137 5288500028643 [4266263794484, 3219125201588, 2356295261492, 1661150503604, 1116637475636, 705272743604, 409142891828, 209904522932, 88784257844, 26578735796, 3654614324, 31891402]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_13 (by decide +kernel) (by decide +kernel)

private theorem m0_2 : availableMass (start .empty) ⟨5,8,0⟩ 1 < layerNeed :=
  mass_of_split _ _ 1 206 406807694511 [4451345034738, 3680112320386, 3005541912594, 2420639567778, 1918524288562, 1492428323778, 1135697168466, 841789563874, 604277497458, 416846202882, 273294160018, 167533094946, 93587979954, 45597033538, 17811720402, 4596751458, 430083826, 211811]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_1 (by decide +kernel) (by decide +kernel)

private theorem m0_3 : availableMass (start .empty) ⟨5,15,0⟩ 22 < layerNeed :=
  mass_of_split _ _ 22 110 8949769279242 [4117697930408, 2869789950068, 1899885801128, 1175089115588, 661453765448, 323983862708, 126633759368, 32308047428, 2861558888, 605683]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_22 (by decide +kernel) (by decide +kernel)

private theorem m0_4 : availableMass (start .empty) ⟨7,21,0⟩ 23 < layerNeed :=
  mass_of_split _ _ 23 78 9356576973753 [3834144619499, 2251141782419, 1173262567979, 507886900211, 158361945131, 24002110739, 331564582]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_23 (by decide +kernel) (by decide +kernel)

private theorem m0_5 : availableMass (start .empty) ⟨8,23,0⟩ 24 < layerNeed :=
  mass_of_split _ _ 24 71 9763384668264 [3741298433403, 2063764405211, 978279460427, 360480794379, 80875605851, 4841097083]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_24 (by decide +kernel) (by decide +kernel)

private theorem m0_6 : availableMass (start .empty) ⟨9,26,0⟩ 25 < layerNeed :=
  mass_of_split _ _ 25 63 10170192362775 [3609164415976, 1808807630352, 733082848824, 200611721824, 21511927944, 36478031]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_25 (by decide +kernel) (by decide +kernel)

private theorem m0_7 : availableMass (start .empty) ⟨10,30,0⟩ 39 < layerNeed :=
  mass_of_split _ _ 39 55 15865500085929 [3441637966211, 1507170548951, 478533281291, 75409139231, 1223255306]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_39 (by decide +kernel) (by decide +kernel)

private theorem m0_8 : availableMass (start .empty) ⟨12,7,0⟩ 1 < layerNeed :=
  mass_of_split _ _ 1 235 406807694511 [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 465502291911, 325201152215, 218658542807, 140152245255, 84460283303, 46860922871, 23132672055, 9554281127, 2904742535, 463290903, 10294505]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_1 (by decide +kernel) (by decide +kernel)

private theorem m0_9 : availableMass (start .empty) ⟨12,36,0⟩ 40 < layerNeed :=
  mass_of_split _ _ 40 45 16272307780440 [3200966280684, 1121101879788, 222424009452, 8738823834]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_40 (by decide +kernel) (by decide +kernel)

private theorem m0_10 : availableMass (start .empty) ⟨13,39,0⟩ 42 < layerNeed :=
  mass_of_split _ _ 42 42 17085923169462 [3086700799382, 957692339882, 141519686534, 1689522376]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_42 (by decide +kernel) (by decide +kernel)

private theorem m0_11 : availableMass (start .empty) ⟨15,45,0⟩ 43 < layerNeed :=
  mass_of_split _ _ 43 36 17492730863973 [2869924035453, 684426537933, 48318716013]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_43 (by decide +kernel) (by decide +kernel)

private theorem m0_12 : availableMass (start .empty) ⟨18,7,0⟩ 2 < layerNeed :=
  mass_of_split _ _ 2 222 813615389022 [4386339368001, 3525063270425, 2797305764657, 2188499287113, 1684917913889, 1273677360761, 942734983185, 680889776297, 477782374913, 323895053529, 210551726321, 129917947145, 75000909537, 39649446713, 18554031569, 7246776681, 2101434305, 333397417, 6441458]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_2 (by decide +kernel) (by decide +kernel)

private theorem m0_13 : availableMass (start .empty) ⟨18,10,0⟩ 8 < layerNeed :=
  mass_of_split _ _ 8 165 3254461556088 [4244728475447, 3184423781283, 2334958710959, 1666621514075, 1151926104231, 765612059027, 484644620063, 288214692939, 157738847255, 76859316611, 31443998607, 9586454843, 1605910919, 47903971]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_8 (by decide +kernel) (by decide +kernel)

private theorem m0_14 : availableMass (start .empty) ⟨18,52,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 31 18306346252995 [2633375067300, 444006253316, 9352003630]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_15 : availableMass (start .empty) ⟨19,6,0⟩ 2 < layerNeed :=
  mass_of_split _ _ 2 211 813615389022 [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 115193179578, 64853223906, 31846335114, 11906544751, 1997023009, 15381961]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_2 (by decide +kernel) (by decide +kernel)

private theorem m0_16 : availableMass (start .empty) ⟨20,9,0⟩ 15 < layerNeed :=
  mass_of_split _ _ 15 183 6102115417665 [4274464818351, 3255423702519, 2430388418007, 1773029304399, 1258936502367, 865619953671, 572509401159, 360954388767, 214224261519, 117508165527, 57915047991, 24473657199, 8132542527, 1760054439, 144344487, 195549]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_15 (by decide +kernel) (by decide +kernel)

private theorem m0_17 : availableMass (start .empty) ⟨23,51,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 32 17899538558484 [2643105791921, 461055981785, 11753673134]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_18 : availableMass (start .empty) ⟨24,24,0⟩ 33 < layerNeed :=
  mass_of_split _ _ 33 68 13424653918863 [3591803480008, 1809378196744, 767284294216, 242428954504, 41531423944, 1159191408]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_33 (by decide +kernel) (by decide +kernel)

private theorem m0_19 : availableMass (start .empty) ⟨25,27,0⟩ 35 < layerNeed :=
  mass_of_split _ _ 35 61 14238269307885 [3466207577373, 1584358027125, 570833077029, 130482205485, 9377706381, 17406]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_35 (by decide +kernel) (by decide +kernel)

private theorem m0_20 : availableMass (start .empty) ⟨27,6,0⟩ 5 < layerNeed :=
  mass_of_split _ _ 5 148 2034038472555 [4353938121874, 3441199047898, 2673178401442, 2034252892138, 1509668150962, 1085538730234, 748848103618, 487448666122, 290061734098, 146304944588, 49162019215, 4783246784, 5416761]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_5 (by decide +kernel) (by decide +kernel)

private theorem m0_21 : availableMass (start .empty) ⟨30,3,0⟩ 1 < layerNeed :=
  mass_of_split _ _ 1 133 406807694511 [4468617313888, 3712507961116, 3030865923784, 2419232490148, 1873277159152, 1388797640428, 961719854296, 588231389580, 273127186090, 63203787060, 2813351970, 14950]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_1 (by decide +kernel) (by decide +kernel)

private theorem m0_22 : availableMass (start .empty) ⟨34,3,0⟩ 4 < layerNeed :=
  mass_of_split _ _ 4 118 1627230778044 [4431184486292, 3612204340544, 2876212486460, 2218169625032, 1633182583844, 1116504317072, 663687177500, 283028310656, 49166727792, 887398072]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_4 (by decide +kernel) (by decide +kernel)

private theorem m0_23 : availableMass (start .empty) ⟨34,17,0⟩ 29 < layerNeed :=
  mass_of_split _ _ 29 97 11797423140819 [3808364803757, 2240407179413, 1214083332549, 587859244733, 241560892157, 76374245637, 14845270613, 879927149, 1429]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_29 (by decide +kernel) (by decide +kernel)

private theorem m0_24 : availableMass (start .empty) ⟨35,6,0⟩ 16 < layerNeed :=
  mass_of_split _ _ 16 114 6508923112176 [4282448217674, 3261405230258, 2415641020826, 1725180227330, 1171203063530, 736045318994, 403199112629, 159602797287, 22913014457, 112081650]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_16 (by decide +kernel) (by decide +kernel)

private theorem m0_25 : availableMass (start .empty) ⟨35,19,0⟩ 31 < layerNeed :=
  mass_of_split _ _ 31 86 12611038529841 [3718205168441, 2063742870641, 1031895362961, 443828120345, 150621954185, 33273012321, 2692779041, 1818657]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_31 (by decide +kernel) (by decide +kernel)

private theorem m0_26 : availableMass (start .empty) ⟨36,9,0⟩ 22 < layerNeed :=
  mass_of_split _ _ 22 111 8949769279242 [4138003816863, 2934377924775, 2006432851911, 1309571434239, 803051226447, 449984501943, 217338252855, 76067647847, 8814714280, 3166290]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_22 (by decide +kernel) (by decide +kernel)

private theorem m0_27 : availableMass (start .empty) ⟨36,21,0⟩ 34 < layerNeed :=
  mass_of_split _ _ 34 78 13831461613374 [3630011256202, 1897202362918, 869542854826, 326125685398, 86563424362, 10988257702, 125927264]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_34 (by decide +kernel) (by decide +kernel)

private theorem m0_28 : availableMass (start .empty) ⟨37,12,0⟩ 23 < layerNeed :=
  mass_of_split _ _ 23 108 9356576973753 [3997787099426, 2630350866626, 1645865478242, 965554953218, 519672926114, 247502647106, 97356981986, 26578461016, 2277270412]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_23 (by decide +kernel) (by decide +kernel)

private theorem m0_29 : availableMass (start .empty) ⟨37,15,0⟩ 27 < layerNeed :=
  mass_of_split _ _ 27 108 10983807751797 [3869489952456, 2364336414996, 1348375576776, 701856260196, 321893431656, 122468201556, 34427824296, 5485698276, 221366932]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_27 (by decide +kernel) (by decide +kernel)

private theorem m0_30 : availableMass (start .empty) ⟨37,23,0⟩ 35 < layerNeed :=
  mass_of_split _ _ 35 71 14238269307885 [3543757293266, 1740463583382, 725823177890, 231978712694, 44475246738, 2260262006]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_35 (by decide +kernel) (by decide +kernel)

private theorem m0_31 : availableMass (start .empty) ⟨37,26,0⟩ 36 < layerNeed :=
  mass_of_split _ _ 36 63 14645077002396 [3427679880044, 1537562043908, 552249258012, 132549079988, 12403225292, 18279599]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_36 (by decide +kernel) (by decide +kernel)

private theorem m0_32 : availableMass (start .empty) ⟨38,28,0⟩ 37 < layerNeed :=
  mass_of_split _ _ 37 58 15051884696907 [3345843745316, 1402581422468, 448007681508, 83912138564, 3731570832]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_37 (by decide +kernel) (by decide +kernel)

private theorem m0_33 : availableMass (start .empty) ⟨40,31,0⟩ 40 < layerNeed :=
  mass_of_split _ _ 40 53 16272307780440 [3223586211145, 1212674706545, 317062140169, 36770994769, 219611212]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_40 (by decide +kernel) (by decide +kernel)

private theorem m0_34 : availableMass (start .empty) ⟨41,30,0⟩ 40 < layerNeed :=
  mass_of_split _ _ 40 55 16272307780440 [3253743777768, 1260455260344, 350222201160, 47906117016, 674162412]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_40 (by decide +kernel) (by decide +kernel)

private theorem m0_35 : availableMass (start .empty) ⟨42,33,0⟩ 41 < layerNeed :=
  mass_of_split _ _ 41 50 16679115474951 [3140687143795, 1092576572635, 244973686027, 18779577475, 2614793]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_41 (by decide +kernel) (by decide +kernel)

private theorem m0_36 : availableMass (start .empty) ⟨42,48,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 34 17899538558484 [2652039668632, 499184213080, 20401046300]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_37 : availableMass (start .empty) ⟨42,51,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 32 18306346252995 [2563326126424, 417419422804, 9968041924]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_38 : availableMass (start .empty) ⟨49,50,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 33 18306346252995 [2562644607908, 426239328636, 11961244636]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_39 : availableMass (start .empty) ⟨51,3,0⟩ 15 < layerNeed :=
  mass_of_split _ _ 15 78 6102115417665 [4272094969009, 3185913953113, 2218935377833, 1363652448289, 616851659871, 100434322389, 511798266]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_15 (by decide +kernel) (by decide +kernel)

private theorem m0_40 : availableMass (start .empty) ⟨56,47,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 35 17899538558484 [2619107381961, 486933253761, 21840880423]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_41 : availableMass (start .empty) ⟨56,48,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 34 18306346252995 [2589999615648, 459837179424, 17623138944]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_42 : availableMass (start .empty) ⟨57,43,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 38 17899538558484 [2733838453065, 603250477841, 46712079089, 13090983]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_43 : availableMass (start .empty) ⟨64,42,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 39 17899538558484 [2729935948509, 607390250913, 50793045957, 52152219]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_44 : availableMass (start .empty) ⟨67,3,0⟩ 18 < layerNeed :=
  mass_of_split _ _ 18 59 7322538501198 [4122363658625, 2784699470825, 1600321628537, 574051659577, 31710172504]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_18 (by decide +kernel) (by decide +kernel)

private theorem m0_45 : availableMass (start .empty) ⟨67,17,0⟩ 35 < layerNeed :=
  mass_of_split _ _ 35 59 14238269307885 [3560489644478, 1761045972770, 728229872358, 211921074576, 18509695225]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_35 (by decide +kernel) (by decide +kernel)

private theorem m0_46 : availableMass (start .empty) ⟨68,6,0⟩ 20 < layerNeed :=
  mass_of_split _ _ 20 59 8136153890220 [3987552362849, 2519755732493, 1353299325785, 457758080493, 22298776518]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_20 (by decide +kernel) (by decide +kernel)

private theorem m0_47 : availableMass (start .empty) ⟨68,9,0⟩ 23 < layerNeed :=
  mass_of_split _ _ 23 59 9356576973753 [3865081813887, 2292286369287, 1158521719719, 384847990475, 21360045788]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_23 (by decide +kernel) (by decide +kernel)

private theorem m0_48 : availableMass (start .empty) ⟨68,19,0⟩ 36 < layerNeed :=
  mass_of_split _ _ 36 59 14645077002396 [3478220714732, 1623853466192, 620255458164, 161022805784, 11793569440]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_36 (by decide +kernel) (by decide +kernel)

private theorem m0_49 : availableMass (start .empty) ⟨69,12,0⟩ 25 < layerNeed :=
  mass_of_split _ _ 25 58 10170192362775 [3737446061794, 2059418178178, 956963870242, 291806931536, 14325293352]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_25 (by decide +kernel) (by decide +kernel)

private theorem m0_50 : availableMass (start .empty) ⟨69,15,0⟩ 29 < layerNeed :=
  mass_of_split _ _ 29 58 11797423140819 [3621281974504, 1858882879924, 796865352424, 228708406632, 12685028190]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_29 (by decide +kernel) (by decide +kernel)

private theorem m0_51 : availableMass (start .empty) ⟨69,41,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 40 17899538558484 [2735162463970, 617951487430, 55843884506, 137344300]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_52 : availableMass (start .empty) ⟨70,39,0⟩ 43 < layerNeed :=
  mass_of_split _ _ 43 42 17492730863973 [2790623121671, 678616567679, 74997919127, 633590308]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_43 (by decide +kernel) (by decide +kernel)

private theorem m0_53 : availableMass (start .empty) ⟨71,32,0⟩ 41 < layerNeed :=
  mass_of_split _ _ 41 51 16679115474951 [3006087541194, 935940264794, 182210945258, 12363537018, 10586725]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_41 (by decide +kernel) (by decide +kernel)

private theorem m0_54 : availableMass (start .empty) ⟨71,35,0⟩ 43 < layerNeed :=
  mass_of_split _ _ 43 47 17492730863973 [2909676731073, 816447716569, 127597725945, 4466440381]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_43 (by decide +kernel) (by decide +kernel)

private theorem m0_55 : availableMass (start .empty) ⟨71,46,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 35 18306346252995 [2579642579744, 467185011992, 22167130512]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_56 : availableMass (start .empty) ⟨77,45,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 36 18306346252995 [2580095508471, 473012110431, 24612977511]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_57 : availableMass (start .empty) ⟨79,53,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 31 18713153947506 [2355965047955, 294961823675, 3787925008]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_58 : availableMass (start .empty) ⟨80,52,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 31 18713153947506 [2377701723108, 311135835940, 4929481320]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_59 : availableMass (start .empty) ⟨82,44,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 37 18306346252995 [2584601805452, 480873345452, 27251057100, 443720]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_60 : availableMass (start .empty) ⟨85,23,0⟩ 37 < layerNeed :=
  mass_of_split _ _ 37 47 15051884696907 [3216792647522, 1205344981734, 307964503346, 24335498117]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_37 (by decide +kernel) (by decide +kernel)

private theorem m0_61 : availableMass (start .empty) ⟨85,26,0⟩ 39 < layerNeed :=
  mass_of_split _ _ 39 47 15865500085929 [3116563532732, 1072569610004, 242248816620, 17260453007]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_39 (by decide +kernel) (by decide +kernel)

private theorem m0_62 : availableMass (start .empty) ⟨86,28,0⟩ 40 < layerNeed :=
  mass_of_split _ _ 40 46 16272307780440 [3044952863588, 980537268164, 198012391716, 11565218665]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_40 (by decide +kernel) (by decide +kernel)

private theorem m0_63 : availableMass (start .empty) ⟨86,37,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 44 17899538558484 [2766275774174, 660480216194, 74053652478, 975492479]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_64 : availableMass (start .empty) ⟨87,51,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 32 18713153947506 [2374374287089, 314069677849, 5738915374]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_65 : availableMass (start .empty) ⟨94,42,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 39 18306346252995 [2582069941779, 484313912943, 30135299307, 15657549]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_66 : availableMass (start .empty) ⟨94,50,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 33 18713153947506 [2370258064643, 315588516111, 6468960931]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_67 : availableMass (start .empty) ⟨100,17,0⟩ 38 < layerNeed :=
  mass_of_split _ _ 38 40 15458692391418 [3312614485199, 1281684766127, 248971405452, 502987830]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_38 (by decide +kernel) (by decide +kernel)

private theorem m0_68 : availableMass (start .empty) ⟨100,49,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 33 18713153947506 [2369682352291, 318152027171, 7186394893]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_69 : availableMass (start .empty) ⟨101,15,0⟩ 31 < layerNeed :=
  mass_of_split _ _ 31 39 12611038529841 [3373073996552, 1353429344852, 258847641217, 288859726]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_31 (by decide +kernel) (by decide +kernel)

private theorem m0_70 : availableMass (start .empty) ⟨101,19,0⟩ 39 < layerNeed :=
  mass_of_split _ _ 39 39 15865500085929 [3238236261023, 1183964061743, 213645988596, 288859726]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_39 (by decide +kernel) (by decide +kernel)

private theorem m0_71 : availableMass (start .empty) ⟨101,26,0⟩ 42 < layerNeed :=
  mass_of_split _ _ 42 39 17085923169462 [3012858083628, 917572132036, 139321807584, 287945338]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_42 (by decide +kernel) (by decide +kernel)

private theorem m0_72 : availableMass (start .empty) ⟨101,34,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 39 17899538558484 [2771627454348, 661165387732, 69849430225, 209342761]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_73 : availableMass (start .empty) ⟨101,41,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 39 18306346252995 [2574647440386, 478576646246, 29397281018, 18618678]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_74 : availableMass (start .empty) ⟨102,28,0⟩ 43 < layerNeed :=
  mass_of_split _ _ 43 39 17492730863973 [2944655903012, 839855883396, 114926430560, 154522506]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_43 (by decide +kernel) (by decide +kernel)

private theorem m0_75 : availableMass (start .empty) ⟨106,48,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 34 18713153947506 [2368427997848, 319312059224, 7702041244]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_76 : availableMass (start .empty) ⟨107,40,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 37 18306346252995 [2571363213010, 474602807874, 27984230503, 395010]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_77 : availableMass (start .empty) ⟨110,39,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 36 18306346252995 [2582849312751, 482773920519, 28347253578]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_78 : availableMass (start .empty) ⟨112,47,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 35 18713153947506 [2366474489393, 318909774025, 7893202735]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_79 : availableMass (start .empty) ⟨117,21,0⟩ 40 < layerNeed :=
  mass_of_split _ _ 40 34 16272307780440 [3059845655269, 908612949829, 70771166140]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_40 (by decide +kernel) (by decide +kernel)

private theorem m0_80 : availableMass (start .empty) ⟨117,23,0⟩ 41 < layerNeed :=
  mass_of_split _ _ 41 34 16679115474951 [2998816217026, 848599247302, 64961135002]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_41 (by decide +kernel) (by decide +kernel)

private theorem m0_81 : availableMass (start .empty) ⟨117,46,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 34 18713153947506 [2368393465214, 319979156238, 7914852964]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_82 : availableMass (start .empty) ⟨118,33,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 34 17899538558484 [2702912703111, 574529235327, 33616363399]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_44 (by decide +kernel) (by decide +kernel)

private theorem m0_83 : availableMass (start .empty) ⟨122,45,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 32 18713153947506 [2369736093726, 319566154986, 7435610214]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_84 : availableMass (start .empty) ⟨126,36,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 31 18306346252995 [2577231027504, 460114454448, 15170940093]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_45 (by decide +kernel) (by decide +kernel)

private theorem m0_85 : availableMass (start .empty) ⟨127,44,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 31 18713153947506 [2370484759172, 317521030292, 6411014237]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m0_86 : availableMass (start .empty) ⟨129,55,0⟩ 47 < layerNeed :=
  mass_of_split _ _ 47 30 19119961642017 [2109822486014, 174223385298, 646129493]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_47 (by decide +kernel) (by decide +kernel)

private theorem m0_87 : availableMass (start .empty) ⟨132,43,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 30 18713153947506 [2370621631890, 313687851566, 4939582795]
    (Or.inl rfl) (by decide) (by decide) (by decide)
    prefix_0_0_46 (by decide +kernel) (by decide +kernel)

private theorem m1_0 : availableMass (start .one3) ⟨2,6,0⟩ 7 < layerNeed :=
  mass_of_split _ _ 7 181 2802234295898 [4250723020941, 3449188341741, 2753544833589, 2156845604709, 1652007714429, 1231812173181, 888903942501, 615791935029, 404849014509, 248311995789, 138281644821, 66722678661, 25463765469, 6197524509, 480526149, 3463]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_7 (by decide +kernel) (by decide +kernel)

private theorem m1_1 : availableMass (start .one3) ⟨3,9,0⟩ 12 < layerNeed :=
  mass_of_split _ _ 12 134 4740005313959 [3986307280316, 2986780786364, 2167447388348, 1511576120252, 1002006034364, 621146201276, 350975709884, 173043667388, 68469199292, 17941449404, 1719579836, 1027850]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_12 (by decide +kernel) (by decide +kernel)

private theorem m1_2 : availableMass (start .one3) ⟨4,12,0⟩ 27 < layerNeed :=
  mass_of_split _ _ 27 104 10244213165881 [3519675841970, 2400873392270, 1545401316170, 919890853670, 489923484770, 220030929470, 73695147770, 13348339670, 387059280]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_27 (by decide +kernel) (by decide +kernel)

private theorem m1_3 : availableMass (start .one3) ⟨6,18,0⟩ 43 < layerNeed :=
  mass_of_split _ _ 43 72 15626017824485 [2955109160492, 1642002552224, 787110717644, 295749192752, 69200755532, 4715425952]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_43 (by decide +kernel) (by decide +kernel)

private theorem m1_4 : availableMass (start .one3) ⟨10,30,0⟩ 47 < layerNeed :=
  mass_of_split _ _ 47 45 16895888601464 [2459207103287, 857515933967, 168728350703, 6462856495]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_47 (by decide +kernel) (by decide +kernel)

private theorem m1_5 : availableMass (start .one3) ⟨12,36,0⟩ 52 < layerNeed :=
  mass_of_split _ _ 52 38 18442035208545 [2193723787754, 570305888534, 52234475402, 15876318]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_52 (by decide +kernel) (by decide +kernel)

private theorem m1_6 : availableMass (start .one3) ⟨18,3,0⟩ 1 < layerNeed :=
  mass_of_split _ _ 1 211 406784167900 [4401341418546, 3600375833754, 2913222739842, 2328628834026, 1835923080402, 1425016709946, 1086403220514, 811158376842, 590940210546, 417989020122, 285127370946, 185760095274, 113874292242, 64039327866, 31406835042, 11727517728, 1962943874, 14790636]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_1 (by decide +kernel) (by decide +kernel)

private theorem m1_7 : availableMass (start .one3) ⟨19,6,0⟩ 14 < layerNeed :=
  mass_of_split _ _ 14 178 5500464954418 [3952525177356, 2992913071584, 2219513604396, 1606543830384, 1130140605228, 768360585696, 501180229644, 310495796016, 180123344844, 95798737248, 45177635436, 17835502704, 5267603436, 889003104, 34574738]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_14 (by decide +kernel) (by decide +kernel)

private theorem m1_8 : availableMass (start .one3) ⟨26,3,0⟩ 7 < layerNeed :=
  mass_of_split _ _ 7 148 2802234295898 [4189895943712, 3305743392328, 2563043021872, 1946359658968, 1441127051584, 1033647869032, 711093701968, 461505062392, 273791383648, 137748781540, 46177966618, 4403963999, 3908086]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_7 (by decide +kernel) (by decide +kernel)

private theorem m1_9 : availableMass (start .one3) ⟨34,3,0⟩ 10 < layerNeed :=
  mass_of_split _ _ 10 114 3971204672684 [4053291171794, 3079285989578, 2274683547266, 1619866800890, 1096374282290, 686900099114, 375294134668, 148375981107, 21042876467, 88336745]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_10 (by decide +kernel) (by decide +kernel)

private theorem m1_10 : availableMass (start .one3) ⟨35,6,0⟩ 28 < layerNeed :=
  mass_of_split _ _ 28 110 10595085671051 [3531008172531, 2475111640179, 1669956708747, 1073168346171, 646226239107, 354464792931, 167073131739, 57131192519, 6371370545, 655851]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_28 (by decide +kernel) (by decide +kernel)

private theorem m1_11 : availableMass (start .one3) ⟨51,3,0⟩ 14 < layerNeed :=
  mass_of_split _ _ 14 76 5500464954418 [3823623586413, 2656700941977, 1718181322533, 979609358097, 415144639734, 61102363296, 99880866]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_14 (by decide +kernel) (by decide +kernel)

private theorem m1_12 : availableMass (start .one3) ⟨67,3,0⟩ 18 < layerNeed :=
  mass_of_split _ _ 18 58 6996597965292 [3609731199779, 2272152894911, 1216416944699, 411532966491, 19547160155]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_18 (by decide +kernel) (by decide +kernel)

private theorem m1_13 : availableMass (start .one3) ⟨67,6,0⟩ 42 < layerNeed :=
  mass_of_split _ _ 42 58 15303914876236 [3037992922524, 1772334668424, 880695969132, 289534313044, 15365675622]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_42 (by decide +kernel) (by decide +kernel)

private theorem m1_14 : availableMass (start .one3) ⟨67,28,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 48 16264647362425 [2305053254791, 683448548991, 119772302319, 5883295447]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_45 (by decide +kernel) (by decide +kernel)

private theorem m1_15 : availableMass (start .one3) ⟨68,43,0⟩ 53 < layerNeed :=
  mass_of_split _ _ 53 32 18745842002439 [1816046826070, 262342283318, 5530520339]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_53 (by decide +kernel) (by decide +kernel)

private theorem m1_16 : availableMass (start .one3) ⟨69,34,0⟩ 48 < layerNeed :=
  mass_of_split _ _ 48 40 17208756130844 [2094319166750, 476263977826, 44464559614, 150492578]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_48 (by decide +kernel) (by decide +kernel)

private theorem m1_17 : availableMass (start .one3) ⟨69,44,0⟩ 54 < layerNeed :=
  mass_of_split _ _ 54 31 19047857477634 [1778113580417, 240841440169, 3945780115]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_54 (by decide +kernel) (by decide +kernel)

private theorem m1_18 : availableMass (start .one3) ⟨70,24,0⟩ 47 < layerNeed :=
  mass_of_split _ _ 47 55 16895888601464 [2372318168631, 797461380159, 179984039847, 17778801327, 147480882]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_47 (by decide +kernel) (by decide +kernel)

private theorem m1_19 : availableMass (start .one3) ⟨70,39,0⟩ 54 < layerNeed :=
  mass_of_split _ _ 54 35 19047857477634 [1887383473646, 330404763614, 14267864897]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_54 (by decide +kernel) (by decide +kernel)

private theorem m1_20 : availableMass (start .one3) ⟨71,30,0⟩ 52 < layerNeed :=
  mass_of_split _ _ 52 45 18442035208545 [2131457495425, 560706858169, 76206727177, 1691225148]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_52 (by decide +kernel) (by decide +kernel)

private theorem m1_21 : availableMass (start .one3) ⟨84,3,0⟩ 21 < layerNeed :=
  mass_of_split _ _ 21 46 8097241733583 [3414413872320, 1895437836960, 715991688254, 48032922933]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_21 (by decide +kernel) (by decide +kernel)

private theorem m1_22 : availableMass (start .one3) ⟨87,27,0⟩ 52 < layerNeed :=
  mass_of_split _ _ 52 45 18442035208545 [2141834794115, 573926135135, 82135416155, 2232168242]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_52 (by decide +kernel) (by decide +kernel)

private theorem m1_23 : availableMass (start .one3) ⟨100,3,0⟩ 25 < layerNeed :=
  mass_of_split _ _ 25 39 9536534840342 [3213914713976, 1541849191544, 312806055066, 191581076]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_25 (by decide +kernel) (by decide +kernel)

private theorem m1_24 : availableMass (start .one3) ⟨100,9,0⟩ 47 < layerNeed :=
  mass_of_split _ _ 47 39 16895888601464 [2645619581016, 1106074356264, 214512564438, 129356155]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_47 (by decide +kernel) (by decide +kernel)

private theorem m1_25 : availableMass (start .one3) ⟨100,23,0⟩ 52 < layerNeed :=
  mass_of_split _ _ 52 39 18442035208545 [2185659440032, 611992136120, 82246920134, 116841587]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_52 (by decide +kernel) (by decide +kernel)

private theorem m1_26 : availableMass (start .one3) ⟨100,33,0⟩ 54 < layerNeed :=
  mass_of_split _ _ 54 39 19047857477634 [1918592717478, 368211073542, 24407316582, 20405492]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_54 (by decide +kernel) (by decide +kernel)

private theorem m1_27 : availableMass (start .one3) ⟨100,48,0⟩ 55 < layerNeed :=
  mass_of_split _ _ 55 29 19348088547454 [1594924098293, 145333716869, 563634441]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_55 (by decide +kernel) (by decide +kernel)

private theorem m1_28 : availableMass (start .one3) ⟨101,29,0⟩ 53 < layerNeed :=
  mass_of_split _ _ 53 38 18745842002439 [2020503507600, 452616269520, 41548375111, 44567370]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_53 (by decide +kernel) (by decide +kernel)

private theorem m1_29 : availableMass (start .one3) ⟨101,39,0⟩ 55 < layerNeed :=
  mass_of_split _ _ 55 35 19348088547454 [1771526470201, 257276859469, 7830457371]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_55 (by decide +kernel) (by decide +kernel)

private theorem m1_30 : availableMass (start .one3) ⟨101,49,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 28 19646542114598 [1562025691532, 132685875052, 335239382]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_56 (by decide +kernel) (by decide +kernel)

private theorem m1_31 : availableMass (start .one3) ⟨110,48,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 29 19646542114598 [1556021788321, 132374209081, 430937047]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_56 (by decide +kernel) (by decide +kernel)

private theorem m1_32 : availableMass (start .one3) ⟨111,46,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 30 19646542114598 [1590172966607, 150161316495, 898655384]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_56 (by decide +kernel) (by decide +kernel)

private theorem m1_33 : availableMass (start .one3) ⟨116,3,0⟩ 29 < layerNeed :=
  mass_of_split _ _ 29 34 10943990047709 [3020329484608, 1204100612985, 91293987293]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_29 (by decide +kernel) (by decide +kernel)

private theorem m1_34 : availableMass (start .one3) ⟨116,16,0⟩ 51 < layerNeed :=
  mass_of_split _ _ 51 33 18136430168795 [2300147262797, 682080075885, 51744263289]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_51 (by decide +kernel) (by decide +kernel)

private theorem m1_35 : availableMass (start .one3) ⟨116,20,0⟩ 52 < layerNeed :=
  mass_of_split _ _ 52 33 18442035208545 [2185019131366, 579041120386, 41570230102]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_52 (by decide +kernel) (by decide +kernel)

private theorem m1_36 : availableMass (start .one3) ⟨117,32,0⟩ 54 < layerNeed :=
  mass_of_split _ _ 54 33 19047857477634 [1876302319256, 326488577108, 13850916779]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_54 (by decide +kernel) (by decide +kernel)

private theorem m1_37 : availableMass (start .one3) ⟨117,38,0⟩ 55 < layerNeed :=
  mass_of_split _ _ 55 33 19348088547454 [1738599100027, 234468578747, 5654694121]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_55 (by decide +kernel) (by decide +kernel)

private theorem m1_38 : availableMass (start .one3) ⟨117,45,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 30 19646542114598 [1591467840464, 151906014032, 1046385592]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_56 (by decide +kernel) (by decide +kernel)

private theorem m1_39 : availableMass (start .one3) ⟨125,44,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 31 19646542114598 [1586325705195, 149735781499, 1030428322]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_56 (by decide +kernel) (by decide +kernel)

private theorem m1_40 : availableMass (start .one3) ⟨129,43,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 30 19646542114598 [1592568074151, 152647548443, 1078159801]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_1_3_56 (by decide +kernel) (by decide +kernel)

private theorem m2_0 : availableMass (start .one3wide) ⟨2,6,0⟩ 8 < layerNeed :=
  mass_of_split _ _ 8 180 3189620679212 [4208470093431, 3400998776559, 2703885998463, 2109079680039, 1608512625639, 1194102523071, 857751943599, 591348341943, 386764056279, 235856308239, 130467202911, 62423728839, 23537758023, 5606045919, 410231439]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_8 (by decide +kernel) (by decide +kernel)

private theorem m2_1 : availableMass (start .one3wide) ⟨3,9,0⟩ 13 < layerNeed :=
  mass_of_split _ _ 13 134 5110396157981 [3940243619046, 2939781547878, 2124086402022, 1474670710374, 972903674598, 600011169126, 337075741158, 165036610662, 64689670374, 16687485798, 1539295206, 600025]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_13 (by decide +kernel) (by decide +kernel)

private theorem m2_2 : availableMass (start .one3wide) ⟨4,12,0⟩ 29 < layerNeed :=
  mass_of_split _ _ 29 104 10894980286737 [3440529737116, 2334520356064, 1494026014732, 883469957920, 466785542428, 207416237056, 68315622604, 11947391872, 306022308]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_29 (by decide +kernel) (by decide +kernel)

private theorem m2_3 : availableMass (start .one3wide) ⟨7,21,0⟩ 42 < layerNeed :=
  mass_of_split _ _ 42 63 15207016320090 [2818562727304, 1408996587016, 569910078856, 155848954888, 16772495752, 29893822]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_42 (by decide +kernel) (by decide +kernel)

private theorem m2_4 : availableMass (start .one3wide) ⟨10,28,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 48 15840824144420 [2534246983549, 963406781765, 231456474397, 17126534725]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_44 (by decide +kernel) (by decide +kernel)

private theorem m2_5 : availableMass (start .one3wide) ⟨10,30,0⟩ 49 < layerNeed :=
  mass_of_split _ _ 49 45 17391780678962 [2386141258003, 824562572731, 159621018739, 5821408730]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_49 (by decide +kernel) (by decide +kernel)

private theorem m2_6 : availableMass (start .one3wide) ⟨13,39,0⟩ 50 < layerNeed :=
  mass_of_split _ _ 50 35 17696282656250 [2101166327518, 471613066414, 27877937956]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_50 (by decide +kernel) (by decide +kernel)

private theorem m2_7 : availableMass (start .one3wide) ⟨18,3,0⟩ 5 < layerNeed :=
  mass_of_split _ _ 5 200 2010474425715 [4290337982255, 3490905666515, 2807572478999, 2228622102779, 1742956319615, 1340095009955, 1010176152935, 743955826379, 532808206799, 368725569395, 244318288055, 152814835355, 88061782559, 44523799619, 17315639435, 3146034322, 36163100]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_5 (by decide +kernel) (by decide +kernel)

private theorem m2_8 : availableMass (start .one3wide) ⟨19,6,0⟩ 15 < layerNeed :=
  mass_of_split _ _ 15 178 5863346032020 [3903693587601, 2941404455553, 2169054350889, 1559833243017, 1088971834785, 733741562481, 473454595833, 289463838009, 165162925617, 85986228705, 39408850761, 14946628713, 4156132929, 634667217, 20277425]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_15 (by decide +kernel) (by decide +kernel)

private theorem m2_9 : availableMass (start .one3wide) ⟨26,3,0⟩ 7 < layerNeed :=
  mass_of_split _ _ 7 142 2798812868156 [4171860044439, 3275953506267, 2525101609983, 1903338236931, 1395602021607, 987736351659, 666489367887, 419513964243, 235367787911, 103855274703, 23192689868, 610941997]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_7 (by decide +kernel) (by decide +kernel)

private theorem m2_10 : availableMass (start .one3wide) ⟨34,3,0⟩ 11 < layerNeed :=
  mass_of_split _ _ 11 110 4348703743830 [4007918294569, 3027768530941, 2219919472945, 1564266428101, 1041896111545, 635086646029, 327323090521, 108623947825, 8481374010, 963271]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_11 (by decide +kernel) (by decide +kernel)

private theorem m2_11 : availableMass (start .one3wide) ⟨35,6,0⟩ 29 < layerNeed :=
  mass_of_split _ _ 29 106 10894980286737 [3470092819824, 2416340939124, 1616004862032, 1025793325956, 606390719376, 322457081844, 142628103984, 39952099148, 1825528865]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_29 (by decide +kernel) (by decide +kernel)

private theorem m2_12 : availableMass (start .one3wide) ⟨38,18,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 72 16466928178932 [2685422589329, 1297513375481, 530356380041, 165435863105, 30900856097, 1565161769]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_46 (by decide +kernel) (by decide +kernel)

private theorem m2_13 : availableMass (start .one3wide) ⟨50,3,0⟩ 15 < layerNeed :=
  mass_of_split _ _ 15 76 5863346032020 [3782947846107, 2624439326943, 1693268220099, 961045220487, 402146541459, 56368295189, 69235186]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_15 (by decide +kernel) (by decide +kernel)

private theorem m2_14 : availableMass (start .one3wide) ⟨66,3,0⟩ 19 < layerNeed :=
  mass_of_split _ _ 19 58 7343294748062 [3565512832325, 2238105162425, 1191183059597, 394675154453, 17019368351]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_19 (by decide +kernel) (by decide +kernel)

private theorem m2_15 : availableMass (start .one3wide) ⟨66,16,0⟩ 40 < layerNeed :=
  mass_of_split _ _ 40 57 14565439885500 [2703539359332, 1204751157512, 430004287724, 100117846224, 5822390919]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_40 (by decide +kernel) (by decide +kernel)

private theorem m2_16 : availableMass (start .one3wide) ⟨66,28,0⟩ 47 < layerNeed :=
  mass_of_split _ _ 47 48 16777111448916 [2238817082741, 657675556325, 113230544397, 5318388461]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_47 (by decide +kernel) (by decide +kernel)

private theorem m2_17 : availableMass (start .one3wide) ⟨66,41,0⟩ 51 < layerNeed :=
  mass_of_split _ _ 51 34 17998906854750 [1858937376780, 301562399596, 9801583374]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_51 (by decide +kernel) (by decide +kernel)

private theorem m2_18 : availableMass (start .one3wide) ⟨67,6,0⟩ 37 < layerNeed :=
  mass_of_split _ _ 37 57 13588366553051 [3082512047376, 1781679614916, 865476557904, 260150212884, 8523937842]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_37 (by decide +kernel) (by decide +kernel)

private theorem m2_19 : availableMass (start .one3wide) ⟨67,42,0⟩ 55 < layerNeed :=
  mass_of_split _ _ 55 33 19190784819740 [1779615932142, 267377883402, 6643644194]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_55 (by decide +kernel) (by decide +kernel)

private theorem m2_20 : availableMass (start .one3wide) ⟨68,12,0⟩ 38 < layerNeed :=
  mass_of_split _ _ 38 56 13916029718972 [2855507173407, 1408521790647, 569135163087, 145193561855, 4758372012]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_38 (by decide +kernel) (by decide +kernel)

private theorem m2_21 : availableMass (start .one3wide) ⟨68,34,0⟩ 51 < layerNeed :=
  mass_of_split _ _ 51 40 17998906854750 [2016912367274, 451989322150, 40790427922, 114405001]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_51 (by decide +kernel) (by decide +kernel)

private theorem m2_22 : availableMass (start .one3wide) ⟨69,45,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 30 19484139178532 [1696445324976, 213057270192, 2565175704]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_56 (by decide +kernel) (by decide +kernel)

private theorem m2_23 : availableMass (start .one3wide) ⟨70,24,0⟩ 50 < layerNeed :=
  mass_of_split _ _ 50 54 17696282656250 [2282106107160, 753913347804, 164730488544, 15065345124, 88639005]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_50 (by decide +kernel) (by decide +kernel)

private theorem m2_24 : availableMass (start .one3wide) ⟨71,33,0⟩ 52 < layerNeed :=
  mass_of_split _ _ 52 41 18299661237000 [2015535284376, 462503015304, 45249749880, 236193666]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_52 (by decide +kernel) (by decide +kernel)

private theorem m2_25 : availableMass (start .one3wide) ⟨72,36,0⟩ 53 < layerNeed :=
  mass_of_split _ _ 53 38 18598553745231 [1925976863430, 382923385218, 25360970022, 4403417]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_53 (by decide +kernel) (by decide +kernel)

private theorem m2_26 : availableMass (start .one3wide) ⟨83,3,0⟩ 23 < layerNeed :=
  mass_of_split _ _ 23 46 8789100009756 [3347628619752, 1848789592632, 686799197301, 42329940579]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_23 (by decide +kernel) (by decide +kernel)

private theorem m2_27 : availableMass (start .one3wide) ⟨83,6,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 46 15840824144420 [2844216750150, 1455286716522, 507598123811, 30895251162]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_44 (by decide +kernel) (by decide +kernel)

private theorem m2_28 : availableMass (start .one3wide) ⟨84,43,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 32 19484139178532 [1693191627163, 219244822175, 3778196040]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_56 (by decide +kernel) (by decide +kernel)

private theorem m2_29 : availableMass (start .one3wide) ⟨99,3,0⟩ 27 < layerNeed :=
  mass_of_split _ _ 27 39 10201307048886 [3144989772452, 1495751602484, 291642378932, 113352706]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_27 (by decide +kernel) (by decide +kernel)

private theorem m2_30 : availableMass (start .one3wide) ⟨99,9,0⟩ 49 < layerNeed :=
  mass_of_split _ _ 49 38 17391780678962 [2565730853076, 1056661657284, 191690255651, 44834245]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_49 (by decide +kernel) (by decide +kernel)

private theorem m2_31 : availableMass (start .one3wide) ⟨100,12,0⟩ 50 < layerNeed :=
  mass_of_split _ _ 50 38 17696282656250 [2458867347991, 930645229231, 154930633872, 16325895]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_50 (by decide +kernel) (by decide +kernel)

private theorem m2_32 : availableMass (start .one3wide) ⟨100,37,0⟩ 54 < layerNeed :=
  mass_of_split _ _ 54 37 18895592304540 [1791717451696, 283946480656, 11341894256, 5217]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_54 (by decide +kernel) (by decide +kernel)

private theorem m2_33 : availableMass (start .one3wide) ⟨101,42,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 32 19484139178532 [1661168475165, 203793058893, 3497587022]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_56 (by decide +kernel) (by decide +kernel)

private theorem m2_34 : availableMass (start .one3wide) ⟨101,50,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 27 19775663248356 [1499583750173, 117596972381, 177371631]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_57 (by decide +kernel) (by decide +kernel)

private theorem m2_35 : availableMass (start .one3wide) ⟨102,39,0⟩ 55 < layerNeed :=
  mass_of_split _ _ 55 35 19190784819740 [1730575078871, 245374543139, 7034617359]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_55 (by decide +kernel) (by decide +kernel)

private theorem m2_36 : availableMass (start .one3wide) ⟨104,49,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 28 19775663248356 [1509470899734, 123248165766, 277878413]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_57 (by decide +kernel) (by decide +kernel)

private theorem m2_37 : availableMass (start .one3wide) ⟨114,48,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 29 19775663248356 [1500212275757, 121259291597, 337500150]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_57 (by decide +kernel) (by decide +kernel)

private theorem m2_38 : availableMass (start .one3wide) ⟨115,3,0⟩ 30 < layerNeed :=
  mass_of_split _ _ 30 33 11238738736500 [2967605114044, 1166478315909, 81631562102]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_30 (by decide +kernel) (by decide +kernel)

private theorem m2_39 : availableMass (start .one3wide) ⟨115,31,0⟩ 51 < layerNeed :=
  mass_of_split _ _ 51 33 17998906854750 [1904180571636, 345278560364, 15417085404]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_51 (by decide +kernel) (by decide +kernel)

private theorem m2_40 : availableMass (start .one3wide) ⟨115,36,0⟩ 55 < layerNeed :=
  mass_of_split _ _ 55 33 19190784819740 [1747123321405, 255731234701, 7514248753]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_55 (by decide +kernel) (by decide +kernel)

private theorem m2_41 : availableMass (start .one3wide) ⟨116,25,0⟩ 54 < layerNeed :=
  mass_of_split _ _ 54 33 18895592304540 [1992120847838, 437877181774, 23562497001]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_54 (by decide +kernel) (by decide +kernel)

private theorem m2_42 : availableMass (start .one3wide) ⟨116,41,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 33 19484139178532 [1633580778308, 188187939556, 2772001996]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_56 (by decide +kernel) (by decide +kernel)

private theorem m2_43 : availableMass (start .one3wide) ⟨118,47,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 29 19775663248356 [1506703614139, 124973492119, 441770653]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_57 (by decide +kernel) (by decide +kernel)

private theorem m2_44 : availableMass (start .one3wide) ⟨124,39,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 30 19484139178532 [1645611069127, 193858225411, 2699992879]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_56 (by decide +kernel) (by decide +kernel)

private theorem m2_45 : availableMass (start .one3wide) ⟨126,46,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 30 19775663248356 [1501618279693, 123203855589, 449165360]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_3_57 (by decide +kernel) (by decide +kernel)

private theorem m3_0 : availableMass (start .one4) ⟨2,6,0⟩ 15 < layerNeed :=
  mass_of_split _ _ 15 159 5784725383338 [3883855162579, 3046390793687, 2338022992315, 1748271611263, 1266559735331, 882213681319, 584462998027, 362440466255, 205182098803, 101627140471, 40618068059, 10900590367, 1123648195, 1425325]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_15 (by decide +kernel) (by decide +kernel)

private theorem m3_1 : availableMass (start .one4) ⟨3,9,0⟩ 33 < layerNeed :=
  mass_of_split _ _ 33 116 11908814585228 [3231049642509, 2298653378797, 1564136335533, 1004654893581, 597016163533, 317677985709, 142748930157, 47988296653, 8806114701, 270184956]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_33 (by decide +kernel) (by decide +kernel)

private theorem m3_2 : availableMass (start .one4) ⟨6,18,0⟩ 45 < layerNeed :=
  mass_of_split _ _ 45 66 15533265224864 [2585589988735, 1348984179531, 585658273335, 183936696643, 28463927151, 434289236]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_45 (by decide +kernel) (by decide +kernel)

private theorem m3_3 : availableMass (start .one4) ⟨9,27,0⟩ 53 < layerNeed :=
  mass_of_split _ _ 53 46 17759366579862 [2121953667914, 752901044502, 154785992858, 6939440070]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_53 (by decide +kernel) (by decide +kernel)

private theorem m3_4 : availableMass (start .one4) ⟨10,3,0⟩ 1 < layerNeed :=
  mass_of_split _ _ 1 235 405977702900 [4405876948635, 3626084417739, 2953667248363, 2378419105851, 1890633897723, 1481105773675, 1141129125579, 862498587483, 637509035611, 458955588363, 320133606315, 214838692219, 137366691003, 82513689771, 45576017803, 22350246555, 9133189659, 2721902923, 413684331, 7557760]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_1 (by decide +kernel) (by decide +kernel)

private theorem m3_5 : availableMass (start .one4) ⟨12,36,0⟩ 55 < layerNeed :=
  mass_of_split _ _ 55 35 18293065604750 [1834932535256, 412941306584, 24602563816]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_55 (by decide +kernel) (by decide +kernel)

private theorem m3_6 : availableMass (start .one4) ⟨18,3,0⟩ 7 < layerNeed :=
  mass_of_split _ _ 7 199 2780047658398 [4143100716739, 3292206981619, 2579363678291, 1988795764003, 1505683634851, 1116163125779, 807325510579, 567217501891, 384841251203, 250154348851, 154069824019, 88456144739, 46137217891, 20892389203, 7456443251, 1530304975, 30426360]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_7 (by decide +kernel) (by decide +kernel)

private theorem m3_7 : availableMass (start .one4) ⟨34,3,0⟩ 11 < layerNeed :=
  mass_of_split _ _ 11 110 4304968480160 [3888292733075, 2869878139459, 2051808090019, 1407220703219, 911119929715, 540375552355, 273723357194, 93536108425, 8223444834, 963271]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_11 (by decide +kernel) (by decide +kernel)

private theorem m3_8 : availableMass (start .one4) ⟨35,6,0⟩ 31 < layerNeed :=
  mass_of_split _ _ 31 106 11270104078806 [3197277710776, 2159541119984, 1393920888232, 848753156320, 477751601048, 240007435216, 99989407624, 27574471278, 1529968637]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_31 (by decide +kernel) (by decide +kernel)

private theorem m3_9 : availableMass (start .one4) ⟨37,15,0⟩ 49 < layerNeed :=
  mass_of_split _ _ 49 76 16664781571364 [2444476090365, 1233428297213, 538536328517, 187918207317, 44158596269, 4308797645, 14894045]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_49 (by decide +kernel) (by decide +kernel)

private theorem m3_10 : availableMass (start .one4) ⟨50,3,0⟩ 15 < layerNeed :=
  mass_of_split _ _ 15 76 5784725383338 [3643983252655, 2470231491807, 1556230916415, 864292918543, 359870094883, 53278206475, 69235186]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_15 (by decide +kernel) (by decide +kernel)

private theorem m3_11 : availableMass (start .one4) ⟨66,3,0⟩ 20 < layerNeed :=
  mass_of_split _ _ 20 58 7572289975476 [3383107729283, 2075157176707, 1081896125299, 358843118371, 16507179292]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_20 (by decide +kernel) (by decide +kernel)

private theorem m3_12 : availableMass (start .one4) ⟨67,6,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 56 15819651672484 [2633677782404, 1469174551740, 688206512756, 204007945488, 7064093079]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_46 (by decide +kernel) (by decide +kernel)

private theorem m3_13 : availableMass (start .one4) ⟨68,42,0⟩ 58 < layerNeed :=
  mass_of_split _ _ 58 30 19076907362880 [1497982720243, 187774858103, 2225225433]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_58 (by decide +kernel) (by decide +kernel)

private theorem m3_14 : availableMass (start .one4) ⟨70,27,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 45 18817837552212 [1827597169489, 485900695337, 67948068529, 1708334276]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_57 (by decide +kernel) (by decide +kernel)

private theorem m3_15 : availableMass (start .one4) ⟨70,38,0⟩ 59 < layerNeed :=
  mass_of_split _ _ 59 33 19333783121424 [1555926576527, 240637762019, 6947175588]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_59 (by decide +kernel) (by decide +kernel)

private theorem m3_16 : availableMass (start .one4) ⟨72,39,0⟩ 60 < layerNeed :=
  mass_of_split _ _ 60 32 19588477324052 [1515067025892, 217932393192, 4911805965]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_60 (by decide +kernel) (by decide +kernel)

private theorem m3_17 : availableMass (start .one4) ⟨72,44,0⟩ 61 < layerNeed :=
  mass_of_split _ _ 61 29 19841002429312 [1405566491148, 149284304172, 807788266]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_61 (by decide +kernel) (by decide +kernel)

private theorem m3_18 : availableMass (start .one4) ⟨83,3,0⟩ 24 < layerNeed :=
  mass_of_split _ _ 24 46 8953728392296 [3153178885006, 1703811206562, 627161599998, 40516014597]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_24 (by decide +kernel) (by decide +kernel)

private theorem m3_19 : availableMass (start .one4) ⟨99,3,0⟩ 28 < layerNeed :=
  mass_of_split _ _ 28 39 10292914821374 [2940430812574, 1371392600594, 269796461919, 109080280]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_28 (by decide +kernel) (by decide +kernel)

private theorem m3_20 : availableMass (start .one4) ⟨99,9,0⟩ 51 < layerNeed :=
  mass_of_split _ _ 51 38 17216639192470 [2264623519185, 902786121121, 163706487520, 40807075]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_51 (by decide +kernel) (by decide +kernel)

private theorem m3_21 : availableMass (start .one4) ⟨99,18,0⟩ 55 < layerNeed :=
  mass_of_split _ _ 55 38 18293065604750 [1962664811198, 598899444638, 86757547915, 33609511]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_55 (by decide +kernel) (by decide +kernel)

private theorem m3_22 : availableMass (start .one4) ⟨99,29,0⟩ 59 < layerNeed :=
  mass_of_split _ _ 59 38 19333783121424 [1651395007366, 330096934330, 23836805566, 15159877]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_59 (by decide +kernel) (by decide +kernel)

private theorem m3_23 : availableMass (start .one4) ⟨100,22,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 38 18556561155544 [1848465244915, 486954729231, 57089761721, 11379355]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_56 (by decide +kernel) (by decide +kernel)

private theorem m3_24 : availableMass (start .one4) ⟨102,36,0⟩ 60 < layerNeed :=
  mass_of_split _ _ 60 35 19588477324052 [1490061116544, 209552494912, 5860668556]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_60 (by decide +kernel) (by decide +kernel)

private theorem m3_25 : availableMass (start .one4) ⟨109,49,0⟩ 62 < layerNeed :=
  mass_of_split _ _ 62 26 20091370861522 [1226079810735, 76364826375, 16190729]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_62 (by decide +kernel) (by decide +kernel)

private theorem m3_26 : availableMass (start .one4) ⟨110,39,0⟩ 61 < layerNeed :=
  mass_of_split _ _ 61 32 19841002429312 [1399813777630, 158022360986, 2136018834]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_61 (by decide +kernel) (by decide +kernel)

private theorem m3_27 : availableMass (start .one4) ⟨115,3,0⟩ 32 < layerNeed :=
  mass_of_split _ _ 32 33 11590725229536 [2737061215054, 1058881308806, 76395906608]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_32 (by decide +kernel) (by decide +kernel)

private theorem m3_28 : availableMass (start .one4) ⟨115,16,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 33 18817837552212 [1904316972370, 525840601426, 35422025841]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_57 (by decide +kernel) (by decide +kernel)

private theorem m3_29 : availableMass (start .one4) ⟨115,20,0⟩ 58 < layerNeed :=
  mass_of_split _ _ 58 33 19076907362880 [1798963554928, 438088966384, 27303339060]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_58 (by decide +kernel) (by decide +kernel)

private theorem m3_30 : availableMass (start .one4) ⟨117,48,0⟩ 62 < layerNeed :=
  mass_of_split _ _ 62 26 20091370861522 [1224238724356, 77161614164, 31554477]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_62 (by decide +kernel) (by decide +kernel)

private theorem m3_31 : availableMass (start .one4) ⟨124,47,0⟩ 62 < layerNeed :=
  mass_of_split _ _ 62 27 20091370861522 [1224035591762, 78061399886, 50380534]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_62 (by decide +kernel) (by decide +kernel)

private theorem m3_32 : availableMass (start .one4) ⟨128,46,0⟩ 62 < layerNeed :=
  mass_of_split _ _ 62 28 20091370861522 [1230066006395, 80761156535, 76198507]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_4_62 (by decide +kernel) (by decide +kernel)

private theorem m4_0 : availableMass (start .one5) ⟨1,3,0⟩ 1 < layerNeed :=
  mass_of_split _ _ 1 205 405296820225 [4427367235406, 3685201041630, 3029988414830, 2456579933438, 1959769552782, 1534294605086, 1174835799470, 876017221950, 632406335438, 438513979742, 288794371566, 177645104510, 99407149070, 48364852638, 18745939502, 4721510846, 406044750, 54298]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_1 (by decide +kernel) (by decide +kernel)

private theorem m4_1 : availableMass (start .one5) ⟨2,6,0⟩ 16 < layerNeed :=
  mass_of_split _ _ 16 142 6059871817121 [3698083488102, 2818064601570, 2088444090814, 1495806800058, 1026507576726, 666671271442, 402192738030, 218736833514, 101738418118, 36402355266, 7703511582, 386862640]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_16 (by decide +kernel) (by decide +kernel)

private theorem m4_2 : availableMass (start .one5) ⟨3,9,0⟩ 33 < layerNeed :=
  mass_of_split _ _ 33 106 11568066003952 [2990174381894, 2048891486742, 1327400847014, 797696126198, 431126125830, 198394785494, 69561182822, 14039533494, 600493944]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_33 (by decide +kernel) (by decide +kernel)

private theorem m4_3 : availableMass (start .one5) ⟨5,15,0⟩ 49 < layerNeed :=
  mass_of_split _ _ 49 70 15963742028049 [2307501047728, 1251946216608, 578687998608, 204077139328, 41588992368, 1826624038]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_49 (by decide +kernel) (by decide +kernel)

private theorem m4_4 : availableMass (start .one5) ⟨8,24,0⟩ 59 < layerNeed :=
  mass_of_split _ _ 59 46 18358713237292 [1796308656870, 644079947658, 135546515038, 6565222196]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_59 (by decide +kernel) (by decide +kernel)

private theorem m4_5 : availableMass (start .one5) ⟨10,3,0⟩ 3 < layerNeed :=
  mass_of_split _ _ 3 204 1204989913167 [4269739528020, 3430645891188, 2719553159572, 2123082060468, 1628561109972, 1224026612980, 898222663188, 640601143092, 441321723988, 291251865972, 181966817940, 105749617588, 55591091412, 25189854708, 8952311572, 1992654900, 132866388]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_3 (by decide +kernel) (by decide +kernel)

private theorem m4_6 : availableMass (start .one5) ⟨18,3,0⟩ 21 < layerNeed :=
  mass_of_split _ _ 21 193 7775101417274 [3533464245868, 2717080417644, 2051106048108, 1515817422700, 1092878092908, 765338876268, 517637856364, 335600382828, 206439071340, 118753803628, 62531727468, 29147256684, 11362071148, 3325116780, 572605548, 28015468, 221]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_21 (by decide +kernel) (by decide +kernel)

private theorem m4_7 : availableMass (start .one5) ⟨34,3,0⟩ 32 < layerNeed :=
  mass_of_split _ _ 32 109 11268842645056 [3060811079912, 2174448209768, 1489455505896, 973617961064, 597466788584, 334279422312, 160079516648, 53766864962, 4869532922, 20475]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_32 (by decide +kernel) (by decide +kernel)

private theorem m4_8 : availableMass (start .one5) ⟨50,3,0⟩ 43 < layerNeed :=
  mass_of_split _ _ 43 75 14399689006468 [2637400513660, 1711463600668, 1027989790652, 543440635228, 218396344956, 32376655205, 14617216]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_43 (by decide +kernel) (by decide +kernel)

private theorem m4_9 : availableMass (start .one5) ⟨67,6,0⟩ 49 < layerNeed :=
  mass_of_split _ _ 49 56 15963742028049 [2295123710680, 1233419359092, 555351915840, 161876663412, 6280549143]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_49 (by decide +kernel) (by decide +kernel)

private theorem m4_10 : availableMass (start .one5) ⟨68,42,0⟩ 60 < layerNeed :=
  mass_of_split _ _ 60 28 18584225120910 [1247221390579, 126934282787, 488763188]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_60 (by decide +kernel) (by decide +kernel)

private theorem m4_11 : availableMass (start .one5) ⟨69,21,0⟩ 62 < layerNeed :=
  mass_of_split _ _ 62 51 19027856472931 [1613815164476, 495465819100, 94060862716, 6049451420, 4307544]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_62 (by decide +kernel) (by decide +kernel)

private theorem m4_12 : availableMass (start .one5) ⟨71,41,0⟩ 66 < layerNeed :=
  mass_of_split _ _ 66 28 19886050082250 [1159452460162, 115783273490, 428212392]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_66 (by decide +kernel) (by decide +kernel)

private theorem m4_13 : availableMass (start .one5) ⟨72,36,0⟩ 66 < layerNeed :=
  mass_of_split _ _ 66 32 19886050082250 [1240494713552, 169991931740, 3192545266]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_66 (by decide +kernel) (by decide +kernel)

private theorem m4_14 : availableMass (start .one5) ⟨99,6,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 38 17900206960224 [1953066885096, 809148460612, 151911781409, 30408141]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_57 (by decide +kernel) (by decide +kernel)

private theorem m4_15 : availableMass (start .one5) ⟨99,15,0⟩ 60 < layerNeed :=
  mass_of_split _ _ 60 38 18584225120910 [1682902574794, 528127060746, 79285254253, 26061271]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_60 (by decide +kernel) (by decide +kernel)

private theorem m4_16 : availableMass (start .one5) ⟨99,39,0⟩ 67 < layerNeed :=
  mass_of_split _ _ 67 29 20094645966560 [1120546285192, 108314448312, 624758246]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_67 (by decide +kernel) (by decide +kernel)

private theorem m4_17 : availableMass (start .one5) ⟨101,27,0⟩ 65 < layerNeed :=
  mass_of_split _ _ 65 37 19675090861219 [1346272576782, 251851871934, 15419608174, 1138386]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_65 (by decide +kernel) (by decide +kernel)

private theorem m4_18 : availableMass (start .one5) ⟨101,45,0⟩ 68 < layerNeed :=
  mass_of_split _ _ 68 26 20300896090970 [1015942145010, 63904067266, 9135902]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_68 (by decide +kernel) (by decide +kernel)

private theorem m4_19 : availableMass (start .one5) ⟨116,38,0⟩ 67 < layerNeed :=
  mass_of_split _ _ 67 30 20094645966560 [1101418924087, 100749627135, 583619486]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_67 (by decide +kernel) (by decide +kernel)

private theorem m4_20 : availableMass (start .one5) ⟨116,42,0⟩ 68 < layerNeed :=
  mass_of_split _ _ 68 27 20300896090970 [1030570422735, 72463672959, 81814153]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_68 (by decide +kernel) (by decide +kernel)

private theorem m4_21 : availableMass (start .one5) ⟨124,41,0⟩ 68 < layerNeed :=
  mass_of_split _ _ 68 28 20300896090970 [1029430641405, 72780246417, 108711287]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_5_68 (by decide +kernel) (by decide +kernel)

private theorem m5_0 : availableMass (start .one6) ⟨1,3,0⟩ 21 < layerNeed :=
  mass_of_split _ _ 21 169 7630748804483 [3469991518644, 2771499764184, 2172147095292, 1664854350432, 1242406319172, 897451742184, 622503311244, 409937669232, 251995410132, 140781079032, 68263172124, 26274136704, 6510371172, 532225032, 24238]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_21 (by decide +kernel) (by decide +kernel)

private theorem m5_1 : availableMass (start .one6) ⟨2,6,0⟩ 41 < layerNeed :=
  mass_of_split _ _ 41 117 13363863064666 [2589884838146, 1847574376274, 1260913984418, 812545639922, 484681338434, 259103093906, 117162938594, 39782923058, 7455116162, 245775939]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_41 (by decide +kernel) (by decide +kernel)

private theorem m5_2 : availableMass (start .one6) ⟨4,12,0⟩ 54 < layerNeed :=
  mass_of_split _ _ 54 73 16393523228469 [1982603373057, 1113640202493, 543280058649, 210672133461, 52788836529, 4425795117, 353064]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_54 (by decide +kernel) (by decide +kernel)

private theorem m5_3 : availableMass (start .one6) ⟨7,21,0⟩ 63 < layerNeed :=
  mass_of_split _ _ 63 47 18205179316548 [1506018936984, 546380457468, 118016503512, 6220063827]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_63 (by decide +kernel) (by decide +kernel)

private theorem m5_4 : availableMass (start .one6) ⟨9,27,0⟩ 69 < layerNeed :=
  mass_of_split _ _ 69 37 19293392031055 [1239861093830, 307742191874, 24762599198, 602220]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_69 (by decide +kernel) (by decide +kernel)

private theorem m5_5 : availableMass (start .one6) ⟨34,3,0⟩ 43 < layerNeed :=
  mass_of_split _ _ 43 109 13863575745395 [2465158486452, 1678572483288, 1094646343668, 675608023176, 387540196116, 200380255512, 87920313108, 27807473294, 2835780359, 15]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_43 (by decide +kernel) (by decide +kernel)

private theorem m5_6 : availableMass (start .one6) ⟨66,3,0⟩ 56 < layerNeed :=
  mass_of_split _ _ 56 57 16815447493922 [1932455174559, 1087440376839, 519569509767, 165738374148, 8229232757]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_56 (by decide +kernel) (by decide +kernel)

private theorem m5_7 : availableMass (start .one6) ⟨69,18,0⟩ 65 < layerNeed :=
  mass_of_split _ _ 65 52 18578191697936 [1363378214708, 426694015124, 84140086004, 5985162836, 9404636]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_65 (by decide +kernel) (by decide +kernel)

private theorem m5_8 : availableMass (start .one6) ⟨69,34,0⟩ 75 < layerNeed :=
  mass_of_split _ _ 75 30 20291951842955 [907722374188, 103963796460, 835899182]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_75 (by decide +kernel) (by decide +kernel)

private theorem m5_9 : availableMass (start .one6) ⟨99,6,0⟩ 59 < layerNeed :=
  mass_of_split _ _ 59 38 17427373656031 [1654240991358, 658434586782, 123038045327, 27451915]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_59 (by decide +kernel) (by decide +kernel)

private theorem m5_10 : availableMass (start .one6) ⟨99,15,0⟩ 61 < layerNeed :=
  mass_of_split _ _ 61 38 17821637610149 [1423404768639, 416567742375, 58084328779, 24726625]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_61 (by decide +kernel) (by decide +kernel)

private theorem m5_11 : availableMass (start .one6) ⟨99,27,0⟩ 70 < layerNeed :=
  mass_of_split _ _ 70 37 19465908206633 [1041954714764, 165947448968, 6723086228, 6985]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_70 (by decide +kernel) (by decide +kernel)

private theorem m5_12 : availableMass (start .one6) ⟨100,21,0⟩ 73 < layerNeed :=
  mass_of_split _ _ 73 37 19968749360962 [1079178428760, 227506441596, 18149819092, 3275441]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_73 (by decide +kernel) (by decide +kernel)

private theorem m5_13 : availableMass (start .one6) ⟨101,27,0⟩ 75 < layerNeed :=
  mass_of_split _ _ 75 36 20291951842955 [953326953546, 142677750822, 4837445826]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_75 (by decide +kernel) (by decide +kernel)

private theorem m5_14 : availableMass (start .one6) ⟨115,39,0⟩ 77 < layerNeed :=
  mass_of_split _ _ 77 26 20605748218825 [751818589833, 44287792329, 7608380]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_77 (by decide +kernel) (by decide +kernel)

private theorem m6_0 : availableMass (start .one7) ⟨1,3,0⟩ 20 < layerNeed :=
  mass_of_split _ _ 20 151 7154800101692 [3312716334011, 2562012748159, 1933506238627, 1416645234215, 1000781395723, 675169615951, 428968019699, 251237963767, 130944036955, 56954060063, 18039085891, 2873399239, 50533574]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_20 (by decide +kernel) (by decide +kernel)

private theorem m6_1 : availableMass (start .one7) ⟨2,6,0⟩ 38 < layerNeed :=
  mass_of_split _ _ 38 106 12106716429931 [2420256528369, 1658378428097, 1074976160945, 646879226625, 350567854577, 162173003969, 57476363697, 11910352385, 558536022]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_38 (by decide +kernel) (by decide +kernel)

private theorem m6_2 : availableMass (start .one7) ⟨3,9,0⟩ 59 < layerNeed :=
  mass_of_split _ _ 59 77 16409022839062 [1614805815124, 934289432500, 477532873748, 200802163828, 59457358036, 7952542004, 60084460]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_59 (by decide +kernel) (by decide +kernel)

private theorem m6_3 : availableMass (start .one7) ⟨6,18,0⟩ 65 < layerNeed :=
  mass_of_split _ _ 65 47 17389136388274 [1242563589224, 458411521468, 103136333512, 6230505356]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_65 (by decide +kernel) (by decide +kernel)

private theorem m6_4 : availableMass (start .one7) ⟨7,21,0⟩ 79 < layerNeed :=
  mass_of_split _ _ 79 39 19307536852454 [877622609618, 236861246626, 24445991026, 29763571]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_79 (by decide +kernel) (by decide +kernel)

private theorem m6_5 : availableMass (start .one7) ⟨11,33,0⟩ 94 < layerNeed :=
  mass_of_split _ _ 94 24 20866278531239 [483442409440, 34852042112]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_94 (by decide +kernel) (by decide +kernel)

private theorem m6_6 : availableMass (start .one7) ⟨34,3,0⟩ 41 < layerNeed :=
  mass_of_split _ _ 41 105 12811744803230 [2255927713816, 1474540994512, 914848757768, 530618133184, 280993786360, 130497918896, 49030268392, 11868581670, 534796335]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_41 (by decide +kernel) (by decide +kernel)

private theorem m6_7 : availableMass (start .one7) ⟨34,6,0⟩ 79 < layerNeed :=
  mass_of_split _ _ 79 84 19307536852454 [1084959853722, 580436883606, 276248524954, 110783423910, 33743546298, 6144177622, 313923066]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_79 (by decide +kernel) (by decide +kernel)

private theorem m6_8 : availableMass (start .one7) ⟨37,18,0⟩ 90 < layerNeed :=
  mass_of_split _ _ 90 40 20495631246850 [683551256658, 175881905598, 19543497538, 90645326]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_90 (by decide +kernel) (by decide +kernel)

private theorem m6_9 : availableMass (start .one7) ⟨66,3,0⟩ 63 < layerNeed :=
  mass_of_split _ _ 63 55 17073628995194 [1449971968628, 762071773404, 332861925380, 91943569546, 2605192655]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_63 (by decide +kernel) (by decide +kernel)

private theorem m6_10 : availableMass (start .one7) ⟨68,15,0⟩ 86 < layerNeed :=
  mass_of_split _ _ 86 47 20093272080751 [747824426972, 206316872372, 31488180300, 1093419361]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_86 (by decide +kernel) (by decide +kernel)

private theorem m6_11 : availableMass (start .one7) ⟨68,32,0⟩ 94 < layerNeed :=
  mass_of_split _ _ 94 25 20866278531239 [452385553713, 29234465385, 461703]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_94 (by decide +kernel) (by decide +kernel)

private theorem m6_12 : availableMass (start .one7) ⟨98,3,0⟩ 86 < layerNeed :=
  mass_of_split _ _ 86 37 20093272080751 [861651644546, 333483028826, 56557182515, 5985]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_86 (by decide +kernel) (by decide +kernel)

private theorem m7_0 : availableMass (start .two6thin) ⟨1,3,0⟩ 11 < layerNeed :=
  mass_of_split _ _ 11 176 4218526636379 [3903441583584, 3146863739844, 2493299062632, 1935743973132, 1467058843632, 1079967997524, 767059709304, 520786204572, 333463660032, 197272203492, 104255913864, 46322821164, 15244906512, 2658102132, 67127756]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_11 (by decide +kernel) (by decide +kernel)

private theorem m7_1 : availableMass (start .two6thin) ⟨2,6,0⟩ 46 < layerNeed :=
  mass_of_split _ _ 46 114 14589713536243 [2421560994236, 1713087887804, 1156684055228, 734901894332, 429863821244, 223262270396, 96359694524, 29988564668, 4551370172, 64081822]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_46 (by decide +kernel) (by decide +kernel)

private theorem m7_2 : availableMass (start .two6thin) ⟨4,12,0⟩ 62 < layerNeed :=
  mass_of_split _ _ 62 71 18014736648519 [1760656387161, 963196679829, 451005714417, 162748953453, 34915077129, 1816270907]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_62 (by decide +kernel) (by decide +kernel)

private theorem m7_3 : availableMass (start .two6thin) ⟨8,24,0⟩ 64 < layerNeed :=
  mass_of_split _ _ 64 42 18392989678768 [1413424338755, 435394714775, 63593217995, 728541205]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_64 (by decide +kernel) (by decide +kernel)

private theorem m7_4 : availableMass (start .two6thin) ⟨10,30,0⟩ 72 < layerNeed :=
  mass_of_split _ _ 72 33 19803563675598 [1121101879788, 222424009452, 8738823834]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_72 (by decide +kernel) (by decide +kernel)

private theorem m7_5 : availableMass (start .two6thin) ⟨18,3,0⟩ 24 < layerNeed :=
  mass_of_split _ _ 24 167 8580398800522 [3237556875087, 2413857022455, 1758005034807, 1245545703183, 853943619711, 562583177607, 352768571175, 207723795807, 112592647983, 54438725271, 22245426327, 6915950895, 1273299807, 60274983]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_24 (by decide +kernel) (by decide +kernel)

private theorem m7_6 : availableMass (start .two6thin) ⟨34,3,0⟩ 37 < layerNeed :=
  mass_of_split _ _ 37 109 12326006266759 [2665413929148, 1827044235240, 1200886381068, 748215979944, 434163363900, 227713583688, 101706408780, 32837534798, 3419531864, 3060]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_37 (by decide +kernel) (by decide +kernel)

private theorem m7_7 : availableMass (start .two6thin) ⟨50,3,0⟩ 50 < layerNeed :=
  mass_of_split _ _ 50 75 15515243736970 [2171748417075, 1352665782531, 775837825515, 390367142379, 151145968512, 23756604296, 9030775]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_50 (by decide +kernel) (by decide +kernel)

private theorem m7_8 : availableMass (start .two6thin) ⟨69,21,0⟩ 71 < layerNeed :=
  mass_of_split _ _ 71 45 19635957672378 [1184369438736, 310364881524, 41965925472, 931979857]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_71 (by decide +kernel) (by decide +kernel)

private theorem m7_9 : availableMass (start .two6thin) ⟨70,39,0⟩ 76 < layerNeed :=
  mass_of_split _ _ 76 26 20450014414755 [824233149024, 63184657812, 22602955]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_76 (by decide +kernel) (by decide +kernel)

private theorem m7_10 : availableMass (start .two6thin) ⟨99,6,0⟩ 67 < layerNeed :=
  mass_of_split _ _ 67 38 18940866048621 [1471189264566, 577376723094, 106613281067, 17801971]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_67 (by decide +kernel) (by decide +kernel)

private theorem m7_11 : availableMass (start .two6thin) ⟨99,15,0⟩ 69 < layerNeed :=
  mass_of_split _ _ 69 38 19293392031055 [1257816985215, 356245511847, 47363007003, 15868585]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_69 (by decide +kernel) (by decide +kernel)

private theorem m7_12 : availableMass (start .two6thin) ⟨101,27,0⟩ 75 < layerNeed :=
  mass_of_split _ _ 75 36 20291951842955 [953326953546, 142677750822, 4837445826]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_75 (by decide +kernel) (by decide +kernel)

private theorem m7_13 : availableMass (start .two6thin) ⟨101,44,0⟩ 77 < layerNeed :=
  mass_of_split _ _ 77 23 20605748218825 [714672494452, 30348904490]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_77 (by decide +kernel) (by decide +kernel)

private theorem m7_14 : availableMass (start .two6thin) ⟨116,40,0⟩ 77 < layerNeed :=
  mass_of_split _ _ 77 25 20605748218825 [739670608413, 40038963953, 1766030]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_77 (by decide +kernel) (by decide +kernel)

private theorem m7_15 : availableMass (start .two6thin) ⟨128,48,0⟩ 78 < layerNeed :=
  mass_of_split _ _ 78 21 20759175885019 [634517754705, 15612105213]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_2_6_78 (by decide +kernel) (by decide +kernel)

private theorem m8_0 : availableMass (start .two6thinwide) ⟨1,3,0⟩ 16 < layerNeed :=
  mass_of_split _ _ 16 172 5942786444100 [3632443254414, 2893701587058, 2263862876166, 1733844178314, 1294668365886, 937464127074, 653465965878, 434014202106, 270554971374, 154640225106, 77927730534, 32181070698, 9269644446, 1168666434, 6544254]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_16 (by decide +kernel) (by decide +kernel)

private theorem m8_1 : availableMass (start .two6thinwide) ⟨2,6,0⟩ 25 < layerNeed :=
  mass_of_split _ _ 25 125 8822079847350 [3119204983282, 2263347101410, 1581271359442, 1052886066370, 658242858418, 377536699042, 191105878930, 79432016002, 23140055410, 2998269538, 19541681]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_25 (by decide +kernel) (by decide +kernel)

private theorem m8_2 : availableMass (start .two6thinwide) ⟨3,9,0⟩ 57 < layerNeed :=
  mass_of_split _ _ 57 87 16754679603054 [1909667310219, 1181818671075, 667832877171, 330315922107, 131943783483, 35462422899, 3687785955, 5168503]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_57 (by decide +kernel) (by decide +kernel)

private theorem m8_3 : availableMass (start .two6thinwide) ⟨10,28,0⟩ 59 < layerNeed :=
  mass_of_split _ _ 59 38 17145497957877 [1381938872601, 352130557557, 31115617969, 6457054]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_59 (by decide +kernel) (by decide +kernel)

private theorem m8_4 : availableMass (start .two6thinwide) ⟨10,30,0⟩ 76 < layerNeed :=
  mass_of_split _ _ 76 33 20044480602225 [993766446216, 186566493384, 6127904232]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_76 (by decide +kernel) (by decide +kernel)

private theorem m8_5 : availableMass (start .two6thinwide) ⟨17,3,0⟩ 35 < layerNeed :=
  mass_of_split _ _ 35 160 11666174980215 [2755757002278, 2020041299730, 1442319815406, 998207464314, 665359894902, 423473489058, 254285362110, 141573362826, 71156073414, 30892809522, 10683620238, 2469288090, 231329046, 620746]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_35 (by decide +kernel) (by decide +kernel)

private theorem m8_6 : availableMass (start .two6thinwide) ⟨34,6,0⟩ 49 < layerNeed :=
  mass_of_split _ _ 49 100 15077040813912 [2107606268082, 1283782039842, 728828335506, 376717086210, 170736493170, 63491027682, 16901431122, 2204754172, 12750446]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_49 (by decide +kernel) (by decide +kernel)

private theorem m8_7 : availableMass (start .two6thinwide) ⟨38,21,0⟩ 72 < layerNeed :=
  mass_of_split _ _ 72 45 19427100609114 [1172058036018, 349956108438, 56941187370, 1610925827]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_72 (by decide +kernel) (by decide +kernel)

private theorem m8_8 : availableMass (start .two6thinwide) ⟨39,39,0⟩ 77 < layerNeed :=
  mass_of_split _ _ 77 26 20192978395359 [805468000539, 67868124483, 21936112]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_77 (by decide +kernel) (by decide +kernel)

private theorem m8_9 : availableMass (start .two6thinwide) ⟨65,15,0⟩ 62 < layerNeed :=
  mass_of_split _ _ 62 54 17711165342649 [1433980289761, 515563771345, 130876575937, 16500809329, 254232569]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_62 (by decide +kernel) (by decide +kernel)

private theorem m8_10 : availableMass (start .two6thinwide) ⟨66,6,0⟩ 62 < layerNeed :=
  mass_of_split _ _ 62 53 17711165342649 [1622715024908, 801267250988, 319612132172, 73372499261, 794067256]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_62 (by decide +kernel) (by decide +kernel)

private theorem m8_11 : availableMass (start .two6thinwide) ⟨66,9,0⟩ 70 < layerNeed :=
  mass_of_split _ _ 70 53 19104030740655 [1371131779833, 598328295993, 203142535353, 39132084717, 445510828]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_70 (by decide +kernel) (by decide +kernel)

private theorem m8_12 : availableMass (start .two6thinwide) ⟨66,17,0⟩ 74 < layerNeed :=
  mass_of_split _ _ 74 52 19740517599012 [1139677507197, 351844802645, 67613679437, 4522006053, 5208114]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_74 (by decide +kernel) (by decide +kernel)

private theorem m8_13 : availableMass (start .two6thinwide) ⟨66,39,0⟩ 79 < layerNeed :=
  mass_of_split _ _ 79 26 20483128406232 [741868793787, 53620233627, 8681657]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_79 (by decide +kernel) (by decide +kernel)

private theorem m8_14 : availableMass (start .two6thinwide) ⟨66,40,0⟩ 80 < layerNeed :=
  mass_of_split _ _ 80 25 20624828939220 [716314949159, 46676068491, 692278]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_80 (by decide +kernel) (by decide +kernel)

private theorem m8_15 : availableMass (start .two6thinwide) ⟨67,24,0⟩ 75 < layerNeed :=
  mass_of_split _ _ 75 40 19893668506425 [1005309435978, 214620737634, 17557244730, 31694958]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_75 (by decide +kernel) (by decide +kernel)

private theorem m8_16 : availableMass (start .two6thinwide) ⟨70,30,0⟩ 77 < layerNeed :=
  mass_of_split _ _ 77 33 20192978395359 [879457930518, 125472626598, 2902324995]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_77 (by decide +kernel) (by decide +kernel)

private theorem m8_17 : availableMass (start .two6thinwide) ⟨82,39,0⟩ 80 < layerNeed :=
  mass_of_split _ _ 80 26 20624828939220 [708430538802, 46338383982, 4817937]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_80 (by decide +kernel) (by decide +kernel)

private theorem m8_18 : availableMass (start .two6thinwide) ⟨84,38,0⟩ 78 < layerNeed :=
  mass_of_split _ _ 78 26 20339186254101 [745100484788, 54260488436, 28157360]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_78 (by decide +kernel) (by decide +kernel)

private theorem m8_19 : availableMass (start .two6thinwide) ⟨88,48,0⟩ 81 < layerNeed :=
  mass_of_split _ _ 81 21 20764311800400 [600085143099, 16470564732]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_81 (by decide +kernel) (by decide +kernel)

private theorem m8_20 : availableMass (start .two6thinwide) ⟨90,47,0⟩ 81 < layerNeed :=
  mass_of_split _ _ 81 21 20764311800400 [607262662943, 18214018551]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_81 (by decide +kernel) (by decide +kernel)

private theorem m8_21 : availableMass (start .two6thinwide) ⟨92,46,0⟩ 81 < layerNeed :=
  mass_of_split _ _ 81 22 20764311800400 [614500166106, 20085501593]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_81 (by decide +kernel) (by decide +kernel)

private theorem m8_22 : availableMass (start .two6thinwide) ⟨93,45,0⟩ 81 < layerNeed :=
  mass_of_split _ _ 81 22 20764311800400 [622793717898, 22245616624]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_81 (by decide +kernel) (by decide +kernel)

private theorem m8_23 : availableMass (start .two6thinwide) ⟨97,3,0⟩ 38 < layerNeed :=
  mass_of_split _ _ 38 38 12450989984631 [2219227587510, 960763240986, 170885985145, 10349575]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_38 (by decide +kernel) (by decide +kernel)

private theorem m8_24 : availableMass (start .two6thinwide) ⟨98,12,0⟩ 74 < layerNeed :=
  mass_of_split _ _ 74 36 19740517599012 [1145260619037, 341255345337, 40983516512]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_74 (by decide +kernel) (by decide +kernel)

private theorem m8_25 : availableMass (start .two6thinwide) ⟨98,28,0⟩ 77 < layerNeed :=
  mass_of_split _ _ 77 34 20192978395359 [859811169115, 116114127719, 2884098331]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_77 (by decide +kernel) (by decide +kernel)

private theorem m8_26 : availableMass (start .two6thinwide) ⟨98,33,0⟩ 78 < layerNeed :=
  mass_of_split _ _ 78 30 20339186254101 [783453061855, 75690656119, 488633972]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_78 (by decide +kernel) (by decide +kernel)

private theorem m8_27 : availableMass (start .two6thinwide) ⟨98,38,0⟩ 79 < layerNeed :=
  mass_of_split _ _ 79 26 20483128406232 [713358471726, 46939260958, 16788659]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_79 (by decide +kernel) (by decide +kernel)

private theorem m8_28 : availableMass (start .two6thinwide) ⟨99,31,0⟩ 79 < layerNeed :=
  mass_of_split _ _ 79 31 20483128406232 [790787690225, 85626577937, 950019483]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_79 (by decide +kernel) (by decide +kernel)

private theorem m8_29 : availableMass (start .two6thinwide) ⟨99,36,0⟩ 80 < layerNeed :=
  mass_of_split _ _ 80 27 20624828939220 [719800346160, 53905313952, 71846208]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_80 (by decide +kernel) (by decide +kernel)

private theorem m8_30 : availableMass (start .two6thinwide) ⟨103,44,0⟩ 81 < layerNeed :=
  mass_of_split _ _ 81 23 20764311800400 [621968183388, 22996922820]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_81 (by decide +kernel) (by decide +kernel)

private theorem m8_31 : availableMass (start .two6thinwide) ⟨112,43,0⟩ 81 < layerNeed :=
  mass_of_split _ _ 81 23 20764311800400 [621806937802, 23734343884]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_81 (by decide +kernel) (by decide +kernel)

private theorem m8_32 : availableMass (start .two6thinwide) ⟨113,3,0⟩ 44 < layerNeed :=
  mass_of_split _ _ 44 32 13931072174217 [1964392119678, 698376659463, 42132013059]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_44 (by decide +kernel) (by decide +kernel)

private theorem m8_33 : availableMass (start .two6thinwide) ⟨113,27,0⟩ 79 < layerNeed :=
  mass_of_split _ _ 79 31 20483128406232 [816441530608, 100863650260, 1721756432]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_79 (by decide +kernel) (by decide +kernel)

private theorem m8_34 : availableMass (start .two6thinwide) ⟨114,25,0⟩ 77 < layerNeed :=
  mass_of_split _ _ 77 31 20192978395359 [869992821761, 121259831897, 2681807514]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_77 (by decide +kernel) (by decide +kernel)

private theorem m8_35 : availableMass (start .two6thinwide) ⟨118,33,0⟩ 80 < layerNeed :=
  mass_of_split _ _ 80 30 20624828939220 [726501530715, 58358847651, 191585370]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_80 (by decide +kernel) (by decide +kernel)

private theorem m8_36 : availableMass (start .two6thinwide) ⟨121,42,0⟩ 81 < layerNeed :=
  mass_of_split _ _ 81 24 20764311800400 [621294505260, 24252178380]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_4_6_81 (by decide +kernel) (by decide +kernel)

private theorem m9_0 : availableMass (start .two6wide) ⟨1,3,0⟩ 42 < layerNeed :=
  mass_of_split _ _ 42 155 12792309617276 [2274614346942, 1702444569282, 1243396145142, 881988473754, 603814228974, 395539359282, 244903087782, 140717912202, 72869604894, 32317212834, 11093057622, 2302735482, 125117262]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_42 (by decide +kernel) (by decide +kernel)

private theorem m9_1 : availableMass (start .two6wide) ⟨3,9,0⟩ 67 < layerNeed :=
  mass_of_split _ _ 67 83 17240966535111 [1333668352363, 773747274283, 404633192803, 181135883923, 62614083643, 12975487963, 676784153]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_67 (by decide +kernel) (by decide +kernel)

private theorem m9_2 : availableMass (start .two6wide) ⟨6,18,0⟩ 87 < layerNeed :=
  mass_of_split _ _ 87 47 19620080935754 [762631121692, 263466936028, 54038238364, 2677570357]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_87 (by decide +kernel) (by decide +kernel)

private theorem m9_3 : availableMass (start .two6wide) ⟨9,27,0⟩ 92 < layerNeed :=
  mass_of_split _ _ 92 33 20085050849821 [579805745968, 105840147484, 3468871949]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_92 (by decide +kernel) (by decide +kernel)

private theorem m9_4 : availableMass (start .two6wide) ⟨10,28,0⟩ 99 < layerNeed :=
  mass_of_split _ _ 99 31 20661579626127 [480221251641, 72779279733, 1155826025]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_99 (by decide +kernel) (by decide +kernel)

private theorem m9_5 : availableMass (start .two6wide) ⟨11,31,0⟩ 101 < layerNeed :=
  mass_of_split _ _ 101 28 20811455774065 [431788006325, 48713379765, 155342663]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_101 (by decide +kernel) (by decide +kernel)

private theorem m9_6 : availableMass (start .two6wide) ⟨31,3,0⟩ 65 < layerNeed :=
  mass_of_split _ _ 65 75 16951228551556 [1410179203062, 859089271122, 479394965934, 232754433354, 85527567418, 12168869137, 3781421]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_65 (by decide +kernel) (by decide +kernel)

private theorem m9_7 : availableMass (start .two6wide) ⟨34,15,0⟩ 98 < layerNeed :=
  mass_of_split _ _ 98 50 20584243740942 [583100739116, 183639266216, 36190996604, 2419832744, 819000]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_98 (by decide +kernel) (by decide +kernel)

private theorem m9_8 : availableMass (start .two6wide) ⟨46,3,0⟩ 89 < layerNeed :=
  mass_of_split _ _ 89 50 19811655837798 [838026348894, 421072439202, 163697114862, 26426443652, 5162270]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_89 (by decide +kernel) (by decide +kernel)

private theorem m9_9 : availableMass (start .two6wide) ⟨61,27,0⟩ 100 < layerNeed :=
  mass_of_split _ _ 100 31 20737308635615 [422443037916, 48432360312, 620301820]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_100 (by decide +kernel) (by decide +kernel)

private theorem m9_10 : availableMass (start .two6wide) ⟨62,28,0⟩ 101 < layerNeed :=
  mass_of_split _ _ 101 30 20811455774065 [404081890327, 41834301939, 347919332]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_101 (by decide +kernel) (by decide +kernel)

private theorem m9_11 : availableMass (start .two6wide) ⟨63,31,0⟩ 104 < layerNeed :=
  mass_of_split _ _ 104 27 21024652137554 [354775825875, 26876284091, 34008893]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_104 (by decide +kernel) (by decide +kernel)

private theorem m9_12 : availableMass (start .two6wide) ⟨79,43,0⟩ 105 < layerNeed :=
  mass_of_split _ _ 105 20 21092716684802 [272583145108, 5265647476]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_105 (by decide +kernel) (by decide +kernel)

private theorem m9_13 : availableMass (start .two6wide) ⟨80,30,0⟩ 104 < layerNeed :=
  mass_of_split _ _ 104 28 21024652137554 [345653247852, 23992623468, 33484068]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_104 (by decide +kernel) (by decide +kernel)

private theorem m9_14 : availableMass (start .two6wide) ⟨92,9,0⟩ 97 < layerNeed :=
  mass_of_split _ _ 97 27 20505275715388 [553264293983, 106508558091, 183365135]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_97 (by decide +kernel) (by decide +kernel)

private theorem m9_15 : availableMass (start .two6wide) ⟨92,12,0⟩ 99 < layerNeed :=
  mass_of_split _ _ 99 27 20661579626127 [504141492387, 85486803685, 118988681]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_99 (by decide +kernel) (by decide +kernel)

private theorem m9_16 : availableMass (start .two6wide) ⟨92,20,0⟩ 101 < layerNeed :=
  mass_of_split _ _ 101 26 20811455774065 [423940141905, 49623414242, 69479356]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_101 (by decide +kernel) (by decide +kernel)

private theorem m9_17 : availableMass (start .two6wide) ⟨92,24,0⟩ 102 < layerNeed :=
  mass_of_split _ _ 102 26 20884045787455 [388083109767, 35898994054, 43644330]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_102 (by decide +kernel) (by decide +kernel)

private theorem m9_18 : availableMass (start .two6wide) ⟨92,42,0⟩ 105 < layerNeed :=
  mass_of_split _ _ 105 21 21092716684802 [269136294600, 5147265132]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_105 (by decide +kernel) (by decide +kernel)

private theorem m9_19 : availableMass (start .two6wide) ⟨92,46,0⟩ 106 < layerNeed :=
  mass_of_split _ _ 106 19 21159320530732 [245858076396, 2791745242]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_106 (by decide +kernel) (by decide +kernel)

private theorem m9_20 : availableMass (start .two6wide) ⟨100,41,0⟩ 105 < layerNeed :=
  mass_of_split _ _ 105 21 21092716684802 [268422753893, 5224435494]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_105 (by decide +kernel) (by decide +kernel)

private theorem m9_21 : availableMass (start .two6wide) ⟨100,45,0⟩ 106 < layerNeed :=
  mass_of_split _ _ 106 19 21159320530732 [245431770786, 2906660032]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_106 (by decide +kernel) (by decide +kernel)

private theorem m9_22 : availableMass (start .two6wide) ⟨104,44,0⟩ 106 < layerNeed :=
  mass_of_split _ _ 106 20 21159320530732 [247041150851, 3149419220]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_106 (by decide +kernel) (by decide +kernel)

private theorem m9_23 : availableMass (start .two6wide) ⟨107,28,0⟩ 104 < layerNeed :=
  mass_of_split _ _ 104 23 21024652137554 [331617240730, 17428782011]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_104 (by decide +kernel) (by decide +kernel)

private theorem m9_24 : availableMass (start .two6wide) ⟨107,33,0⟩ 105 < layerNeed :=
  mass_of_split _ _ 105 23 21092716684802 [298849959849, 10873185922]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_105 (by decide +kernel) (by decide +kernel)

private theorem m9_25 : availableMass (start .two6wide) ⟨111,43,0⟩ 106 < layerNeed :=
  mass_of_split _ _ 106 20 21159320530732 [246859998494, 3216888634]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_106 (by decide +kernel) (by decide +kernel)

private theorem m9_26 : availableMass (start .two6wide) ⟨117,42,0⟩ 106 < layerNeed :=
  mass_of_split _ _ 106 21 21159320530732 [247091846614, 3271454931]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_12_6_106 (by decide +kernel) (by decide +kernel)

private theorem m10_0 : availableMass (start .two6wider) ⟨1,3,0⟩ 72 < layerNeed :=
  mass_of_split _ _ 72 135 17544785276694 [1250066140980, 882485958192, 601706767308, 393093654216, 243326844132, 140401701600, 73628730492, 33633574008, 12357014676, 3054974352, 298514220, 513884]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_72 (by decide +kernel) (by decide +kernel)

private theorem m10_1 : availableMass (start .two6wider) ⟨4,12,0⟩ 90 < layerNeed :=
  mass_of_split _ _ 90 61 19399841570580 [729787001841, 334579779261, 121643730729, 28535772213, 2245543137, 168240]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_90 (by decide +kernel) (by decide +kernel)

private theorem m10_2 : availableMass (start .two6wider) ⟨12,36,0⟩ 118 < layerNeed :=
  mass_of_split _ _ 118 22 21173075340601 [219350135717, 9418212322]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_118 (by decide +kernel) (by decide +kernel)

private theorem m10_3 : availableMass (start .two6wider) ⟨31,15,0⟩ 93 < layerNeed :=
  mass_of_split _ _ 93 52 19647296159201 [600385622539, 193520757091, 40091622331, 3117804115, 5212385]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_93 (by decide +kernel) (by decide +kernel)

private theorem m10_4 : availableMass (start .two6wider) ⟨32,6,0⟩ 96 < layerNeed :=
  mass_of_split _ _ 96 58 19879239635560 [645913433600, 304247303360, 117111644288, 30058081553, 1791493835]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_96 (by decide +kernel) (by decide +kernel)

private theorem m10_5 : availableMass (start .two6wider) ⟨35,27,0⟩ 101 < layerNeed :=
  mass_of_split _ _ 101 31 20233343814275 [395998542354, 52668518574, 843286502]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_101 (by decide +kernel) (by decide +kernel)

private theorem m10_6 : availableMass (start .two6wider) ⟨36,28,0⟩ 104 < layerNeed :=
  mass_of_split _ _ 104 30 20427480521422 [358159930103, 41397820851, 360505220]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_104 (by decide +kernel) (by decide +kernel)

private theorem m10_7 : availableMass (start .two6wider) ⟨36,30,0⟩ 105 < layerNeed :=
  mass_of_split _ _ 105 28 20489290767610 [336456348954, 32174840778, 91710030]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_105 (by decide +kernel) (by decide +kernel)

private theorem m10_8 : availableMass (start .two6wider) ⟨37,31,0⟩ 111 < layerNeed :=
  mass_of_split _ _ 111 26 20831383824680 [278533313495, 21114211407, 8351962]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_111 (by decide +kernel) (by decide +kernel)

private theorem m10_9 : availableMass (start .two6wider) ⟨37,42,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 19 21217253852102 [179030361022, 2879283995]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_10 : availableMass (start .two6wider) ⟨38,30,0⟩ 112 < layerNeed :=
  mass_of_split _ _ 112 27 20883824443524 [274888030908, 22210424508, 19497648]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_112 (by decide +kernel) (by decide +kernel)

private theorem m10_11 : availableMass (start .two6wider) ⟨61,9,0⟩ 112 < layerNeed :=
  mass_of_split _ _ 112 32 20883824443524 [371016429454, 93082891474, 4734141557]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_112 (by decide +kernel) (by decide +kernel)

private theorem m10_12 : availableMass (start .two6wider) ⟨61,20,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 32 21033759657005 [281960177652, 37535920484, 791244345]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_115 (by decide +kernel) (by decide +kernel)

private theorem m10_13 : availableMass (start .two6wider) ⟨62,15,0⟩ 113 < layerNeed :=
  mass_of_split _ _ 113 31 20935019115796 [324511574339, 59179724219, 2085367842]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_113 (by decide +kernel) (by decide +kernel)

private theorem m10_14 : availableMass (start .two6wider) ⟨62,24,0⟩ 116 < layerNeed :=
  mass_of_split _ _ 116 31 21081349375245 [254340088445, 24589467065, 186586610]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_116 (by decide +kernel) (by decide +kernel)

private theorem m10_15 : availableMass (start .two6wider) ⟨63,21,0⟩ 116 < layerNeed :=
  mass_of_split _ _ 116 31 21081349375245 [267366465081, 31689635985, 449991934]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_116 (by decide +kernel) (by decide +kernel)

private theorem m10_16 : availableMass (start .two6wider) ⟨63,36,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 22 21217253852102 [187044601412, 5246232741]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_17 : availableMass (start .two6wider) ⟨69,49,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 16 21260337124490 [142692660140, 509046174]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_18 : availableMass (start .two6wider) ⟨70,47,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 17 21260337124490 [147202784380, 759742489]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_19 : availableMass (start .two6wider) ⟨74,46,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 17 21260337124490 [148296912900, 874803434]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_20 : availableMass (start .two6wider) ⟨77,31,0⟩ 117 < layerNeed :=
  mass_of_split _ _ 117 25 21127780848759 [208558834487, 8749657087, 45932]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_117 (by decide +kernel) (by decide +kernel)

private theorem m10_21 : availableMass (start .two6wider) ⟨77,34,0⟩ 118 < layerNeed :=
  mass_of_split _ _ 118 23 21173075340601 [192133286396, 5838291810]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_118 (by decide +kernel) (by decide +kernel)

private theorem m10_22 : availableMass (start .two6wider) ⟨80,45,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 18 21260337124490 [148627306188, 966476178]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_23 : availableMass (start .two6wider) ⟨83,35,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 22 21217253852102 [179982896176, 4345718164]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_24 : availableMass (start .two6wider) ⟨84,33,0⟩ 118 < layerNeed :=
  mass_of_split _ _ 118 24 21173075340601 [191457845115, 5757704547]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_118 (by decide +kernel) (by decide +kernel)

private theorem m10_25 : availableMass (start .two6wider) ⟨85,34,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 23 21217253852102 [181981217080, 4711087123]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_26 : availableMass (start .two6wider) ⟨87,44,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 18 21260337124490 [148490547024, 1031452379]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_27 : availableMass (start .two6wider) ⟨90,3,0⟩ 78 < layerNeed :=
  mass_of_split _ _ 78 28 18239238099511 [840931998375, 202173672757, 552837532]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_78 (by decide +kernel) (by decide +kernel)

private theorem m10_28 : availableMass (start .two6wider) ⟨90,31,0⟩ 118 < layerNeed :=
  mass_of_split _ _ 118 22 21173075340601 [194369822744, 6236704284]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_118 (by decide +kernel) (by decide +kernel)

private theorem m10_29 : availableMass (start .two6wider) ⟨91,26,0⟩ 117 < layerNeed :=
  mass_of_split _ _ 117 22 21127780848759 [216960976666, 10153018728]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_117 (by decide +kernel) (by decide +kernel)

private theorem m10_30 : availableMass (start .two6wider) ⟨91,29,0⟩ 118 < layerNeed :=
  mass_of_split _ _ 118 22 21173075340601 [200286505695, 7370078286]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_118 (by decide +kernel) (by decide +kernel)

private theorem m10_31 : availableMass (start .two6wider) ⟨93,43,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 18 21260337124490 [148616301550, 1094026558]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_32 : availableMass (start .two6wider) ⟨98,33,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 20 21217253852102 [177843054053, 3863480291]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_33 : availableMass (start .two6wider) ⟨99,30,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 20 21217253852102 [186116250066, 5001071517]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_34 : availableMass (start .two6wider) ⟨100,42,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 19 21260337124490 [148233752680, 1107388156]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_35 : availableMass (start .two6wider) ⟨105,3,0⟩ 90 < layerNeed :=
  mass_of_split _ _ 90 23 19399841570580 [601368776544, 76498924476]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_90 (by decide +kernel) (by decide +kernel)

private theorem m10_36 : availableMass (start .two6wider) ⟨105,20,0⟩ 117 < layerNeed :=
  mass_of_split _ _ 117 19 21127780848759 [227052258012, 9195383649]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_117 (by decide +kernel) (by decide +kernel)

private theorem m10_37 : availableMass (start .two6wider) ⟨105,25,0⟩ 118 < layerNeed :=
  mass_of_split _ _ 118 19 21173075340601 [203645562982, 6360971756]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_118 (by decide +kernel) (by decide +kernel)

private theorem m10_38 : availableMass (start .two6wider) ⟨105,29,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 19 21217253852102 [185352033742, 4430604475]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_39 : availableMass (start .two6wider) ⟨105,41,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 19 21260337124490 [148537409022, 1135811848]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_40 : availableMass (start .two6wider) ⟨107,28,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 19 21217253852102 [187008421570, 4431916191]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_41 : availableMass (start .two6wider) ⟨111,40,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 18 21260337124490 [148316927414, 1093865608]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m10_42 : availableMass (start .two6wider) ⟨114,26,0⟩ 119 < layerNeed :=
  mass_of_split _ _ 119 18 21217253852102 [188100724420, 3720172790]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_119 (by decide +kernel) (by decide +kernel)

private theorem m10_43 : availableMass (start .two6wider) ⟨116,39,0⟩ 120 < layerNeed :=
  mass_of_split _ _ 120 17 21260337124490 [148407919878, 1037783030]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_14_6_120 (by decide +kernel) (by decide +kernel)

private theorem m11_0 : availableMass (start .two7) ⟨1,3,0⟩ 39 < layerNeed :=
  mass_of_split _ _ 39 137 12345309926026 [2485320501073, 1870140147997, 1365325568201, 960231072085, 644114202049, 406135732493, 235359669817, 120753252421, 51186950705, 15434467069, 2172735913, 21614173]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_39 (by decide +kernel) (by decide +kernel)

private theorem m11_1 : availableMass (start .two7) ⟨2,6,0⟩ 72 < layerNeed :=
  mass_of_split _ _ 72 88 18409550143796 [1326693567523, 829433432811, 474696370323, 238858451419, 97946477187, 27637978443, 3261215731, 11690115]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_72 (by decide +kernel) (by decide +kernel)

private theorem m11_2 : availableMass (start .two7) ⟨5,15,0⟩ 83 < layerNeed :=
  mass_of_split _ _ 83 48 19769638791534 [897161533893, 337911924233, 79640636525, 5567562225]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_83 (by decide +kernel) (by decide +kernel)

private theorem m11_3 : availableMass (start .two7) ⟨9,26,0⟩ 86 < layerNeed :=
  mass_of_split _ _ 86 31 20093272080751 [678927140096, 114089066780, 2439374769]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_86 (by decide +kernel) (by decide +kernel)

private theorem m11_4 : availableMass (start .two7) ⟨10,29,0⟩ 90 < layerNeed :=
  mass_of_split _ _ 90 28 20495631246850 [580271173284, 69105793908, 251644188]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_90 (by decide +kernel) (by decide +kernel)

private theorem m11_5 : availableMass (start .two7) ⟨34,3,0⟩ 59 < layerNeed :=
  mass_of_split _ _ 59 103 16409022839062 [1665453717604, 1053919605676, 628206843188, 346304409340, 171578819332, 72774124364, 24011911636, 4791304348, 158332261]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_59 (by decide +kernel) (by decide +kernel)

private theorem m11_6 : availableMass (start .two7) ⟨66,6,0⟩ 79 < layerNeed :=
  mass_of_split _ _ 79 54 19307536852454 [1016942820826, 457569515990, 163815230170, 36174537485, 1039700399]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_79 (by decide +kernel) (by decide +kernel)

private theorem m11_7 : availableMass (start .two7) ⟨66,26,0⟩ 90 < layerNeed :=
  mass_of_split _ _ 90 30 20495631246850 [561012151882, 69496815334, 836638220]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_90 (by decide +kernel) (by decide +kernel)

private theorem m11_8 : availableMass (start .two7) ⟨68,32,0⟩ 92 < layerNeed :=
  mass_of_split _ _ 92 25 20684811110080 [476601444144, 32540949540, 2214528]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_92 (by decide +kernel) (by decide +kernel)

private theorem m11_9 : availableMass (start .two7) ⟨69,21,0⟩ 88 < layerNeed :=
  mass_of_split _ _ 88 36 20298524140798 [640905543324, 117917953500, 6323303452]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_88 (by decide +kernel) (by decide +kernel)

private theorem m11_10 : availableMass (start .two7) ⟨70,30,0⟩ 94 < layerNeed :=
  mass_of_split _ _ 94 26 20866278531239 [467927380699, 36445319555, 20131842]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_94 (by decide +kernel) (by decide +kernel)

private theorem m11_11 : availableMass (start .two7) ⟨85,27,0⟩ 94 < layerNeed :=
  mass_of_split _ _ 94 29 20866278531239 [482237172643, 45735265831, 198980923]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_94 (by decide +kernel) (by decide +kernel)

private theorem m11_12 : availableMass (start .two7) ⟨85,42,0⟩ 95 < layerNeed :=
  mass_of_split _ _ 95 20 20954186403764 [358237334949, 6612004189]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_95 (by decide +kernel) (by decide +kernel)

private theorem m11_13 : availableMass (start .two7) ⟨86,45,0⟩ 96 < layerNeed :=
  mass_of_split _ _ 96 18 21040245395728 [330068875284, 3784998704]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_96 (by decide +kernel) (by decide +kernel)

private theorem m11_14 : availableMass (start .two7) ⟨98,15,0⟩ 88 < layerNeed :=
  mass_of_split _ _ 88 37 20298524140798 [673330119542, 148441842934, 12588574023, 1365]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_88 (by decide +kernel) (by decide +kernel)

private theorem m11_15 : availableMass (start .two7) ⟨98,17,0⟩ 92 < layerNeed :=
  mass_of_split _ _ 92 36 20684811110080 [592280901556, 111688313236, 6879110675]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_92 (by decide +kernel) (by decide +kernel)

private theorem m11_16 : availableMass (start .two7) ⟨98,39,0⟩ 96 < layerNeed :=
  mass_of_split _ _ 96 21 21040245395728 [360692163150, 8740066093]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_96 (by decide +kernel) (by decide +kernel)

private theorem m11_17 : availableMass (start .two7) ⟨99,9,0⟩ 88 < layerNeed :=
  mass_of_split _ _ 88 36 20298524140798 [744515846372, 220462113220, 28143400555]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_88 (by decide +kernel) (by decide +kernel)

private theorem m11_18 : availableMass (start .two7) ⟨99,12,0⟩ 90 < layerNeed :=
  mass_of_split _ _ 90 36 20495631246850 [676061135420, 170810249400, 17702405870]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_90 (by decide +kernel) (by decide +kernel)

private theorem m11_19 : availableMass (start .two7) ⟨107,38,0⟩ 95 < layerNeed :=
  mass_of_split _ _ 95 21 20954186403764 [372106180128, 10044518065]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_95 (by decide +kernel) (by decide +kernel)

private theorem m11_20 : availableMass (start .two7) ⟨115,31,0⟩ 95 < layerNeed :=
  mass_of_split _ _ 95 25 20954186403764 [415381680121, 22113922805, 1204500]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_95 (by decide +kernel) (by decide +kernel)

private theorem m11_21 : availableMass (start .two7) ⟨123,37,0⟩ 96 < layerNeed :=
  mass_of_split _ _ 96 22 21040245395728 [359445617868, 9488419484]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_3_7_96 (by decide +kernel) (by decide +kernel)

private theorem m12_0 : availableMass (start .two7wide) ⟨1,3,0⟩ 76 < layerNeed :=
  mass_of_split _ _ 76 111 18207992744206 [1162297228923, 799002038063, 522766159043, 320514910263, 179740394123, 88501497023, 35423889363, 9700025543, 1089143963, 3062147]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_76 (by decide +kernel) (by decide +kernel)

private theorem m12_1 : availableMass (start .two7wide) ⟨4,12,0⟩ 94 < layerNeed :=
  mass_of_split _ _ 94 52 19937008185735 [648927864978, 262564576862, 73074606386, 8493799182, 29499156]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_94 (by decide +kernel) (by decide +kernel)

private theorem m12_2 : availableMass (start .two7wide) ⟨12,34,0⟩ 113 < layerNeed :=
  mass_of_split _ _ 113 20 21141810109106 [233273353630, 7131267064]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_113 (by decide +kernel) (by decide +kernel)

private theorem m12_3 : availableMass (start .two7wide) ⟨33,6,0⟩ 100 < layerNeed :=
  mass_of_split _ _ 100 73 20377744337378 [589666734050, 277486259342, 109648048674, 32760280862, 5837822210, 302226510, 785]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_100 (by decide +kernel) (by decide +kernel)

private theorem m12_4 : availableMass (start .two7wide) ⟨37,26,0⟩ 107 < layerNeed :=
  mass_of_split _ _ 107 27 20819304825666 [320972885797, 29531902909, 35692446]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_107 (by decide +kernel) (by decide +kernel)

private theorem m12_5 : availableMass (start .two7wide) ⟨37,28,0⟩ 108 < layerNeed :=
  mass_of_split _ _ 108 25 20876480145516 [298622528952, 21467220652, 674534]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_108 (by decide +kernel) (by decide +kernel)

private theorem m12_6 : availableMass (start .two7wide) ⟨38,29,0⟩ 109 < layerNeed :=
  mass_of_split _ _ 109 24 20932253685332 [283030422954, 17493599850]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_109 (by decide +kernel) (by decide +kernel)

private theorem m12_7 : availableMass (start .two7wide) ⟨38,37,0⟩ 114 < layerNeed :=
  mass_of_split _ _ 114 19 21190932661156 [203344110690, 3371811590]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_114 (by decide +kernel) (by decide +kernel)

private theorem m12_8 : availableMass (start .two7wide) ⟨39,32,0⟩ 113 < layerNeed :=
  mass_of_split _ _ 113 22 21141810109106 [233354248993, 8481122290]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_113 (by decide +kernel) (by decide +kernel)

private theorem m12_9 : availableMass (start .two7wide) ⟨64,34,0⟩ 114 < layerNeed :=
  mass_of_split _ _ 114 20 21190932661156 [207733248992, 4847690462]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_114 (by decide +kernel) (by decide +kernel)

private theorem m12_10 : availableMass (start .two7wide) ⟨65,9,0⟩ 105 < layerNeed :=
  mass_of_split _ _ 105 45 20700650876832 [453414232352, 141607922208, 27038860064, 1381871376]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_105 (by decide +kernel) (by decide +kernel)

private theorem m12_11 : availableMass (start .two7wide) ⟨65,31,0⟩ 111 < layerNeed :=
  mass_of_split _ _ 111 22 21039691928402 [243215233099, 9628710358]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_111 (by decide +kernel) (by decide +kernel)

private theorem m12_12 : availableMass (start .two7wide) ⟨65,47,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 15 21238794894016 [154769264793, 243453015]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_115 (by decide +kernel) (by decide +kernel)

private theorem m12_13 : availableMass (start .two7wide) ⟨67,46,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 15 21238794894016 [157312888394, 325133208]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_115 (by decide +kernel) (by decide +kernel)

private theorem m12_14 : availableMass (start .two7wide) ⟨70,44,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 16 21238794894016 [162792440927, 550788901]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_115 (by decide +kernel) (by decide +kernel)

private theorem m12_15 : availableMass (start .two7wide) ⟨72,42,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 17 21238794894016 [168769169931, 884405513]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_115 (by decide +kernel) (by decide +kernel)

private theorem m12_16 : availableMass (start .two7wide) ⟨80,23,0⟩ 107 < layerNeed :=
  mass_of_split _ _ 107 30 20819304825666 [314143613102, 30258047846, 182410552]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_107 (by decide +kernel) (by decide +kernel)

private theorem m12_17 : availableMass (start .two7wide) ⟨80,26,0⟩ 113 < layerNeed :=
  mass_of_split _ _ 113 26 21141810109106 [246079853180, 14906454416, 1508675]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_113 (by decide +kernel) (by decide +kernel)

private theorem m12_18 : availableMass (start .two7wide) ⟨80,41,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 17 21238794894016 [170071179148, 1048836170]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_115 (by decide +kernel) (by decide +kernel)

private theorem m12_19 : availableMass (start .two7wide) ⟨81,24,0⟩ 111 < layerNeed :=
  mass_of_split _ _ 111 28 21039691928402 [272356427426, 21427322758, 39147572]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_111 (by decide +kernel) (by decide +kernel)

private theorem m12_20 : availableMass (start .two7wide) ⟨82,21,0⟩ 112 < layerNeed :=
  mass_of_split _ _ 112 30 21091404269042 [280287104604, 28551326156, 239799096]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_112 (by decide +kernel) (by decide +kernel)

private theorem m12_21 : availableMass (start .two7wide) ⟨84,33,0⟩ 114 < layerNeed :=
  mass_of_split _ _ 114 21 21190932661156 [204946506610, 4917257689]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_114 (by decide +kernel) (by decide +kernel)

private theorem m12_22 : availableMass (start .two7wide) ⟨88,32,0⟩ 114 < layerNeed :=
  mass_of_split _ _ 114 21 21190932661156 [207662657193, 5561025633]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_114 (by decide +kernel) (by decide +kernel)

private theorem m12_23 : availableMass (start .two7wide) ⟨89,31,0⟩ 114 < layerNeed :=
  mass_of_split _ _ 114 22 21190932661156 [211523731439, 6413140309]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_114 (by decide +kernel) (by decide +kernel)

private theorem m12_24 : availableMass (start .two7wide) ⟨93,40,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 17 21238794894016 [169983075510, 1179664472]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_115 (by decide +kernel) (by decide +kernel)

private theorem m12_25 : availableMass (start .two7wide) ⟨95,3,0⟩ 82 < layerNeed :=
  mass_of_split _ _ 82 33 18858483630234 [819609368475, 283326734103, 25156346443]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_82 (by decide +kernel) (by decide +kernel)

private theorem m12_26 : availableMass (start .two7wide) ⟨95,15,0⟩ 109 < layerNeed :=
  mass_of_split _ _ 109 31 20932253685332 [335909272543, 51962469035, 1533258710]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_109 (by decide +kernel) (by decide +kernel)

private theorem m12_27 : availableMass (start .two7wide) ⟨96,19,0⟩ 110 < layerNeed :=
  mass_of_split _ _ 110 31 20986649632805 [300744527800, 33544352600, 424701318]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_110 (by decide +kernel) (by decide +kernel)

private theorem m12_28 : availableMass (start .two7wide) ⟨101,30,0⟩ 114 < layerNeed :=
  mass_of_split _ _ 114 23 21190932661156 [211079297117, 6644233185]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_114 (by decide +kernel) (by decide +kernel)

private theorem m12_29 : availableMass (start .two7wide) ⟨106,39,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 18 21238794894016 [169727535416, 1297503006]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_115 (by decide +kernel) (by decide +kernel)

private theorem m12_30 : availableMass (start .two7wide) ⟨109,29,0⟩ 114 < layerNeed :=
  mass_of_split _ _ 114 23 21190932661156 [212036617806, 7034435716]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_114 (by decide +kernel) (by decide +kernel)

private theorem m12_31 : availableMass (start .two7wide) ⟨111,3,0⟩ 94 < layerNeed :=
  mass_of_split _ _ 94 28 19937008185735 [594990563097, 152064816978, 1344568999]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_94 (by decide +kernel) (by decide +kernel)

private theorem m12_32 : availableMass (start .two7wide) ⟨111,22,0⟩ 113 < layerNeed :=
  mass_of_split _ _ 113 27 21141810109106 [250342162050, 17262920862, 19027272]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_113 (by decide +kernel) (by decide +kernel)

private theorem m12_33 : availableMass (start .two7wide) ⟨118,38,0⟩ 115 < layerNeed :=
  mass_of_split _ _ 115 18 21238794894016 [169576969338, 1405947969]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_115 (by decide +kernel) (by decide +kernel)

private theorem m12_34 : availableMass (start .two7wide) ⟨119,20,0⟩ 111 < layerNeed :=
  mass_of_split _ _ 111 25 21039691928402 [271733409561, 20892112285, 2409681]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_111 (by decide +kernel) (by decide +kernel)

private theorem m12_35 : availableMass (start .two7wide) ⟨119,21,0⟩ 113 < layerNeed :=
  mass_of_split _ _ 113 25 21141810109106 [250809304916, 17066572980, 1189350]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_113 (by decide +kernel) (by decide +kernel)

private theorem m12_36 : availableMass (start .two7wide) ⟨120,28,0⟩ 114 < layerNeed :=
  mass_of_split _ _ 114 24 21190932661156 [211564935050, 7061303454]
    (Or.inr (by decide)) (by decide) (by decide) (by decide)
    prefix_7_7_114 (by decide +kernel) (by decide +kernel)

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m0_0⟩
    · exact ⟨by decide, m0_1⟩
    · exact ⟨by decide, m0_2⟩
    · exact ⟨by decide, m0_3⟩
    · exact ⟨by decide, m0_4⟩
    · exact ⟨by decide, m0_5⟩
    · exact ⟨by decide, m0_6⟩
    · exact ⟨by decide, m0_7⟩
    · exact ⟨by decide, m0_8⟩
    · exact ⟨by decide, m0_9⟩
    · exact ⟨by decide, m0_10⟩
    · exact ⟨by decide, m0_11⟩
    · exact ⟨by decide, m0_12⟩
    · exact ⟨by decide, m0_13⟩
    · exact ⟨by decide, m0_14⟩
    · exact ⟨by decide, m0_15⟩
    · exact ⟨by decide, m0_16⟩
    · exact ⟨by decide, m0_17⟩
    · exact ⟨by decide, m0_18⟩
    · exact ⟨by decide, m0_19⟩
    · exact ⟨by decide, m0_20⟩
    · exact ⟨by decide, m0_21⟩
    · exact ⟨by decide, m0_22⟩
    · exact ⟨by decide, m0_23⟩
    · exact ⟨by decide, m0_24⟩
    · exact ⟨by decide, m0_25⟩
    · exact ⟨by decide, m0_26⟩
    · exact ⟨by decide, m0_27⟩
    · exact ⟨by decide, m0_28⟩
    · exact ⟨by decide, m0_29⟩
    · exact ⟨by decide, m0_30⟩
    · exact ⟨by decide, m0_31⟩
    · exact ⟨by decide, m0_32⟩
    · exact ⟨by decide, m0_33⟩
    · exact ⟨by decide, m0_34⟩
    · exact ⟨by decide, m0_35⟩
    · exact ⟨by decide, m0_36⟩
    · exact ⟨by decide, m0_37⟩
    · exact ⟨by decide, m0_38⟩
    · exact ⟨by decide, m0_39⟩
    · exact ⟨by decide, m0_40⟩
    · exact ⟨by decide, m0_41⟩
    · exact ⟨by decide, m0_42⟩
    · exact ⟨by decide, m0_43⟩
    · exact ⟨by decide, m0_44⟩
    · exact ⟨by decide, m0_45⟩
    · exact ⟨by decide, m0_46⟩
    · exact ⟨by decide, m0_47⟩
    · exact ⟨by decide, m0_48⟩
    · exact ⟨by decide, m0_49⟩
    · exact ⟨by decide, m0_50⟩
    · exact ⟨by decide, m0_51⟩
    · exact ⟨by decide, m0_52⟩
    · exact ⟨by decide, m0_53⟩
    · exact ⟨by decide, m0_54⟩
    · exact ⟨by decide, m0_55⟩
    · exact ⟨by decide, m0_56⟩
    · exact ⟨by decide, m0_57⟩
    · exact ⟨by decide, m0_58⟩
    · exact ⟨by decide, m0_59⟩
    · exact ⟨by decide, m0_60⟩
    · exact ⟨by decide, m0_61⟩
    · exact ⟨by decide, m0_62⟩
    · exact ⟨by decide, m0_63⟩
    · exact ⟨by decide, m0_64⟩
    · exact ⟨by decide, m0_65⟩
    · exact ⟨by decide, m0_66⟩
    · exact ⟨by decide, m0_67⟩
    · exact ⟨by decide, m0_68⟩
    · exact ⟨by decide, m0_69⟩
    · exact ⟨by decide, m0_70⟩
    · exact ⟨by decide, m0_71⟩
    · exact ⟨by decide, m0_72⟩
    · exact ⟨by decide, m0_73⟩
    · exact ⟨by decide, m0_74⟩
    · exact ⟨by decide, m0_75⟩
    · exact ⟨by decide, m0_76⟩
    · exact ⟨by decide, m0_77⟩
    · exact ⟨by decide, m0_78⟩
    · exact ⟨by decide, m0_79⟩
    · exact ⟨by decide, m0_80⟩
    · exact ⟨by decide, m0_81⟩
    · exact ⟨by decide, m0_82⟩
    · exact ⟨by decide, m0_83⟩
    · exact ⟨by decide, m0_84⟩
    · exact ⟨by decide, m0_85⟩
    · exact ⟨by decide, m0_86⟩
    · exact ⟨by decide, m0_87⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m1_0⟩
    · exact ⟨by decide, m1_1⟩
    · exact ⟨by decide, m1_2⟩
    · exact ⟨by decide, m1_3⟩
    · exact ⟨by decide, m1_4⟩
    · exact ⟨by decide, m1_5⟩
    · exact ⟨by decide, m1_6⟩
    · exact ⟨by decide, m1_7⟩
    · exact ⟨by decide, m1_8⟩
    · exact ⟨by decide, m1_9⟩
    · exact ⟨by decide, m1_10⟩
    · exact ⟨by decide, m1_11⟩
    · exact ⟨by decide, m1_12⟩
    · exact ⟨by decide, m1_13⟩
    · exact ⟨by decide, m1_14⟩
    · exact ⟨by decide, m1_15⟩
    · exact ⟨by decide, m1_16⟩
    · exact ⟨by decide, m1_17⟩
    · exact ⟨by decide, m1_18⟩
    · exact ⟨by decide, m1_19⟩
    · exact ⟨by decide, m1_20⟩
    · exact ⟨by decide, m1_21⟩
    · exact ⟨by decide, m1_22⟩
    · exact ⟨by decide, m1_23⟩
    · exact ⟨by decide, m1_24⟩
    · exact ⟨by decide, m1_25⟩
    · exact ⟨by decide, m1_26⟩
    · exact ⟨by decide, m1_27⟩
    · exact ⟨by decide, m1_28⟩
    · exact ⟨by decide, m1_29⟩
    · exact ⟨by decide, m1_30⟩
    · exact ⟨by decide, m1_31⟩
    · exact ⟨by decide, m1_32⟩
    · exact ⟨by decide, m1_33⟩
    · exact ⟨by decide, m1_34⟩
    · exact ⟨by decide, m1_35⟩
    · exact ⟨by decide, m1_36⟩
    · exact ⟨by decide, m1_37⟩
    · exact ⟨by decide, m1_38⟩
    · exact ⟨by decide, m1_39⟩
    · exact ⟨by decide, m1_40⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m2_0⟩
    · exact ⟨by decide, m2_1⟩
    · exact ⟨by decide, m2_2⟩
    · exact ⟨by decide, m2_3⟩
    · exact ⟨by decide, m2_4⟩
    · exact ⟨by decide, m2_5⟩
    · exact ⟨by decide, m2_6⟩
    · exact ⟨by decide, m2_7⟩
    · exact ⟨by decide, m2_8⟩
    · exact ⟨by decide, m2_9⟩
    · exact ⟨by decide, m2_10⟩
    · exact ⟨by decide, m2_11⟩
    · exact ⟨by decide, m2_12⟩
    · exact ⟨by decide, m2_13⟩
    · exact ⟨by decide, m2_14⟩
    · exact ⟨by decide, m2_15⟩
    · exact ⟨by decide, m2_16⟩
    · exact ⟨by decide, m2_17⟩
    · exact ⟨by decide, m2_18⟩
    · exact ⟨by decide, m2_19⟩
    · exact ⟨by decide, m2_20⟩
    · exact ⟨by decide, m2_21⟩
    · exact ⟨by decide, m2_22⟩
    · exact ⟨by decide, m2_23⟩
    · exact ⟨by decide, m2_24⟩
    · exact ⟨by decide, m2_25⟩
    · exact ⟨by decide, m2_26⟩
    · exact ⟨by decide, m2_27⟩
    · exact ⟨by decide, m2_28⟩
    · exact ⟨by decide, m2_29⟩
    · exact ⟨by decide, m2_30⟩
    · exact ⟨by decide, m2_31⟩
    · exact ⟨by decide, m2_32⟩
    · exact ⟨by decide, m2_33⟩
    · exact ⟨by decide, m2_34⟩
    · exact ⟨by decide, m2_35⟩
    · exact ⟨by decide, m2_36⟩
    · exact ⟨by decide, m2_37⟩
    · exact ⟨by decide, m2_38⟩
    · exact ⟨by decide, m2_39⟩
    · exact ⟨by decide, m2_40⟩
    · exact ⟨by decide, m2_41⟩
    · exact ⟨by decide, m2_42⟩
    · exact ⟨by decide, m2_43⟩
    · exact ⟨by decide, m2_44⟩
    · exact ⟨by decide, m2_45⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m3_0⟩
    · exact ⟨by decide, m3_1⟩
    · exact ⟨by decide, m3_2⟩
    · exact ⟨by decide, m3_3⟩
    · exact ⟨by decide, m3_4⟩
    · exact ⟨by decide, m3_5⟩
    · exact ⟨by decide, m3_6⟩
    · exact ⟨by decide, m3_7⟩
    · exact ⟨by decide, m3_8⟩
    · exact ⟨by decide, m3_9⟩
    · exact ⟨by decide, m3_10⟩
    · exact ⟨by decide, m3_11⟩
    · exact ⟨by decide, m3_12⟩
    · exact ⟨by decide, m3_13⟩
    · exact ⟨by decide, m3_14⟩
    · exact ⟨by decide, m3_15⟩
    · exact ⟨by decide, m3_16⟩
    · exact ⟨by decide, m3_17⟩
    · exact ⟨by decide, m3_18⟩
    · exact ⟨by decide, m3_19⟩
    · exact ⟨by decide, m3_20⟩
    · exact ⟨by decide, m3_21⟩
    · exact ⟨by decide, m3_22⟩
    · exact ⟨by decide, m3_23⟩
    · exact ⟨by decide, m3_24⟩
    · exact ⟨by decide, m3_25⟩
    · exact ⟨by decide, m3_26⟩
    · exact ⟨by decide, m3_27⟩
    · exact ⟨by decide, m3_28⟩
    · exact ⟨by decide, m3_29⟩
    · exact ⟨by decide, m3_30⟩
    · exact ⟨by decide, m3_31⟩
    · exact ⟨by decide, m3_32⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m4_0⟩
    · exact ⟨by decide, m4_1⟩
    · exact ⟨by decide, m4_2⟩
    · exact ⟨by decide, m4_3⟩
    · exact ⟨by decide, m4_4⟩
    · exact ⟨by decide, m4_5⟩
    · exact ⟨by decide, m4_6⟩
    · exact ⟨by decide, m4_7⟩
    · exact ⟨by decide, m4_8⟩
    · exact ⟨by decide, m4_9⟩
    · exact ⟨by decide, m4_10⟩
    · exact ⟨by decide, m4_11⟩
    · exact ⟨by decide, m4_12⟩
    · exact ⟨by decide, m4_13⟩
    · exact ⟨by decide, m4_14⟩
    · exact ⟨by decide, m4_15⟩
    · exact ⟨by decide, m4_16⟩
    · exact ⟨by decide, m4_17⟩
    · exact ⟨by decide, m4_18⟩
    · exact ⟨by decide, m4_19⟩
    · exact ⟨by decide, m4_20⟩
    · exact ⟨by decide, m4_21⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m5_0⟩
    · exact ⟨by decide, m5_1⟩
    · exact ⟨by decide, m5_2⟩
    · exact ⟨by decide, m5_3⟩
    · exact ⟨by decide, m5_4⟩
    · exact ⟨by decide, m5_5⟩
    · exact ⟨by decide, m5_6⟩
    · exact ⟨by decide, m5_7⟩
    · exact ⟨by decide, m5_8⟩
    · exact ⟨by decide, m5_9⟩
    · exact ⟨by decide, m5_10⟩
    · exact ⟨by decide, m5_11⟩
    · exact ⟨by decide, m5_12⟩
    · exact ⟨by decide, m5_13⟩
    · exact ⟨by decide, m5_14⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m6_0⟩
    · exact ⟨by decide, m6_1⟩
    · exact ⟨by decide, m6_2⟩
    · exact ⟨by decide, m6_3⟩
    · exact ⟨by decide, m6_4⟩
    · exact ⟨by decide, m6_5⟩
    · exact ⟨by decide, m6_6⟩
    · exact ⟨by decide, m6_7⟩
    · exact ⟨by decide, m6_8⟩
    · exact ⟨by decide, m6_9⟩
    · exact ⟨by decide, m6_10⟩
    · exact ⟨by decide, m6_11⟩
    · exact ⟨by decide, m6_12⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m7_0⟩
    · exact ⟨by decide, m7_1⟩
    · exact ⟨by decide, m7_2⟩
    · exact ⟨by decide, m7_3⟩
    · exact ⟨by decide, m7_4⟩
    · exact ⟨by decide, m7_5⟩
    · exact ⟨by decide, m7_6⟩
    · exact ⟨by decide, m7_7⟩
    · exact ⟨by decide, m7_8⟩
    · exact ⟨by decide, m7_9⟩
    · exact ⟨by decide, m7_10⟩
    · exact ⟨by decide, m7_11⟩
    · exact ⟨by decide, m7_12⟩
    · exact ⟨by decide, m7_13⟩
    · exact ⟨by decide, m7_14⟩
    · exact ⟨by decide, m7_15⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m8_0⟩
    · exact ⟨by decide, m8_1⟩
    · exact ⟨by decide, m8_2⟩
    · exact ⟨by decide, m8_3⟩
    · exact ⟨by decide, m8_4⟩
    · exact ⟨by decide, m8_5⟩
    · exact ⟨by decide, m8_6⟩
    · exact ⟨by decide, m8_7⟩
    · exact ⟨by decide, m8_8⟩
    · exact ⟨by decide, m8_9⟩
    · exact ⟨by decide, m8_10⟩
    · exact ⟨by decide, m8_11⟩
    · exact ⟨by decide, m8_12⟩
    · exact ⟨by decide, m8_13⟩
    · exact ⟨by decide, m8_14⟩
    · exact ⟨by decide, m8_15⟩
    · exact ⟨by decide, m8_16⟩
    · exact ⟨by decide, m8_17⟩
    · exact ⟨by decide, m8_18⟩
    · exact ⟨by decide, m8_19⟩
    · exact ⟨by decide, m8_20⟩
    · exact ⟨by decide, m8_21⟩
    · exact ⟨by decide, m8_22⟩
    · exact ⟨by decide, m8_23⟩
    · exact ⟨by decide, m8_24⟩
    · exact ⟨by decide, m8_25⟩
    · exact ⟨by decide, m8_26⟩
    · exact ⟨by decide, m8_27⟩
    · exact ⟨by decide, m8_28⟩
    · exact ⟨by decide, m8_29⟩
    · exact ⟨by decide, m8_30⟩
    · exact ⟨by decide, m8_31⟩
    · exact ⟨by decide, m8_32⟩
    · exact ⟨by decide, m8_33⟩
    · exact ⟨by decide, m8_34⟩
    · exact ⟨by decide, m8_35⟩
    · exact ⟨by decide, m8_36⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m9_0⟩
    · exact ⟨by decide, m9_1⟩
    · exact ⟨by decide, m9_2⟩
    · exact ⟨by decide, m9_3⟩
    · exact ⟨by decide, m9_4⟩
    · exact ⟨by decide, m9_5⟩
    · exact ⟨by decide, m9_6⟩
    · exact ⟨by decide, m9_7⟩
    · exact ⟨by decide, m9_8⟩
    · exact ⟨by decide, m9_9⟩
    · exact ⟨by decide, m9_10⟩
    · exact ⟨by decide, m9_11⟩
    · exact ⟨by decide, m9_12⟩
    · exact ⟨by decide, m9_13⟩
    · exact ⟨by decide, m9_14⟩
    · exact ⟨by decide, m9_15⟩
    · exact ⟨by decide, m9_16⟩
    · exact ⟨by decide, m9_17⟩
    · exact ⟨by decide, m9_18⟩
    · exact ⟨by decide, m9_19⟩
    · exact ⟨by decide, m9_20⟩
    · exact ⟨by decide, m9_21⟩
    · exact ⟨by decide, m9_22⟩
    · exact ⟨by decide, m9_23⟩
    · exact ⟨by decide, m9_24⟩
    · exact ⟨by decide, m9_25⟩
    · exact ⟨by decide, m9_26⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m10_0⟩
    · exact ⟨by decide, m10_1⟩
    · exact ⟨by decide, m10_2⟩
    · exact ⟨by decide, m10_3⟩
    · exact ⟨by decide, m10_4⟩
    · exact ⟨by decide, m10_5⟩
    · exact ⟨by decide, m10_6⟩
    · exact ⟨by decide, m10_7⟩
    · exact ⟨by decide, m10_8⟩
    · exact ⟨by decide, m10_9⟩
    · exact ⟨by decide, m10_10⟩
    · exact ⟨by decide, m10_11⟩
    · exact ⟨by decide, m10_12⟩
    · exact ⟨by decide, m10_13⟩
    · exact ⟨by decide, m10_14⟩
    · exact ⟨by decide, m10_15⟩
    · exact ⟨by decide, m10_16⟩
    · exact ⟨by decide, m10_17⟩
    · exact ⟨by decide, m10_18⟩
    · exact ⟨by decide, m10_19⟩
    · exact ⟨by decide, m10_20⟩
    · exact ⟨by decide, m10_21⟩
    · exact ⟨by decide, m10_22⟩
    · exact ⟨by decide, m10_23⟩
    · exact ⟨by decide, m10_24⟩
    · exact ⟨by decide, m10_25⟩
    · exact ⟨by decide, m10_26⟩
    · exact ⟨by decide, m10_27⟩
    · exact ⟨by decide, m10_28⟩
    · exact ⟨by decide, m10_29⟩
    · exact ⟨by decide, m10_30⟩
    · exact ⟨by decide, m10_31⟩
    · exact ⟨by decide, m10_32⟩
    · exact ⟨by decide, m10_33⟩
    · exact ⟨by decide, m10_34⟩
    · exact ⟨by decide, m10_35⟩
    · exact ⟨by decide, m10_36⟩
    · exact ⟨by decide, m10_37⟩
    · exact ⟨by decide, m10_38⟩
    · exact ⟨by decide, m10_39⟩
    · exact ⟨by decide, m10_40⟩
    · exact ⟨by decide, m10_41⟩
    · exact ⟨by decide, m10_42⟩
    · exact ⟨by decide, m10_43⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m11_0⟩
    · exact ⟨by decide, m11_1⟩
    · exact ⟨by decide, m11_2⟩
    · exact ⟨by decide, m11_3⟩
    · exact ⟨by decide, m11_4⟩
    · exact ⟨by decide, m11_5⟩
    · exact ⟨by decide, m11_6⟩
    · exact ⟨by decide, m11_7⟩
    · exact ⟨by decide, m11_8⟩
    · exact ⟨by decide, m11_9⟩
    · exact ⟨by decide, m11_10⟩
    · exact ⟨by decide, m11_11⟩
    · exact ⟨by decide, m11_12⟩
    · exact ⟨by decide, m11_13⟩
    · exact ⟨by decide, m11_14⟩
    · exact ⟨by decide, m11_15⟩
    · exact ⟨by decide, m11_16⟩
    · exact ⟨by decide, m11_17⟩
    · exact ⟨by decide, m11_18⟩
    · exact ⟨by decide, m11_19⟩
    · exact ⟨by decide, m11_20⟩
    · exact ⟨by decide, m11_21⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m12_0⟩
    · exact ⟨by decide, m12_1⟩
    · exact ⟨by decide, m12_2⟩
    · exact ⟨by decide, m12_3⟩
    · exact ⟨by decide, m12_4⟩
    · exact ⟨by decide, m12_5⟩
    · exact ⟨by decide, m12_6⟩
    · exact ⟨by decide, m12_7⟩
    · exact ⟨by decide, m12_8⟩
    · exact ⟨by decide, m12_9⟩
    · exact ⟨by decide, m12_10⟩
    · exact ⟨by decide, m12_11⟩
    · exact ⟨by decide, m12_12⟩
    · exact ⟨by decide, m12_13⟩
    · exact ⟨by decide, m12_14⟩
    · exact ⟨by decide, m12_15⟩
    · exact ⟨by decide, m12_16⟩
    · exact ⟨by decide, m12_17⟩
    · exact ⟨by decide, m12_18⟩
    · exact ⟨by decide, m12_19⟩
    · exact ⟨by decide, m12_20⟩
    · exact ⟨by decide, m12_21⟩
    · exact ⟨by decide, m12_22⟩
    · exact ⟨by decide, m12_23⟩
    · exact ⟨by decide, m12_24⟩
    · exact ⟨by decide, m12_25⟩
    · exact ⟨by decide, m12_26⟩
    · exact ⟨by decide, m12_27⟩
    · exact ⟨by decide, m12_28⟩
    · exact ⟨by decide, m12_29⟩
    · exact ⟨by decide, m12_30⟩
    · exact ⟨by decide, m12_31⟩
    · exact ⟨by decide, m12_32⟩
    · exact ⟨by decide, m12_33⟩
    · exact ⟨by decide, m12_34⟩
    · exact ⟨by decide, m12_35⟩
    · exact ⟨by decide, m12_36⟩

theorem order_valid (k : Band) (x : Shape) : order k x = 1 ∨
    availableMass (start k) x (order k x - 1) < layerNeed := by
  rcases (P0_9_8.orderFor_select x.b x.j (thresholds k)).2 with h | ⟨q,hq,hb,hj,he⟩
  · exact Or.inl h
  · right
    change order k x = q.l at he
    rw [he]
    obtain ⟨hpos, hsmall⟩ := thresholds_valid k q hq
    have hr : start k = zeroShape ∨ 0 < (start k).j := by cases k <;> decide
    have hi : 0 < (start k).j + q.j := by omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y := ⟨q.b,q.j,0⟩) hr hi hb hj).trans_lt hsmall
#print axioms order_valid
end Final50PriceMass
