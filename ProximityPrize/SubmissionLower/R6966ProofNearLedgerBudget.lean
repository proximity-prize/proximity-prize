import Mathlib.Tactic

set_option Elab.async false

-- merged module R6966ProofNearLedgerCore
section Merged_R6966ProofNearLedgerCore

namespace Research6966.NearLedger

abbrev core : ℕ := 274790602290452470
abbrev credit : ℕ := 1828374077815
abbrev prime : ℕ := 2130706433
abbrev nodes : ℕ := 262144
abbrev agreement : ℕ := 179769
abbrev wordDegree : ℕ := 133570
abbrev massCap : ℕ := 12000
abbrev graphCap : ℕ := 374

def rate (e : ℕ) : ℕ :=
  let n := max 3 e
  (9*n+2)*(n-1)+2*n-1+2*e-1

def density (e : ℕ) : ℕ := rate e*prime

theorem rate_mono : Monotone rate := by
  intro e f h
  have n : max 3 e ≤ max 3 f := max_le_max le_rfl h
  unfold rate
  dsimp only
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.sub_le_sub_right (Nat.add_le_add
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 n) 2)
        (Nat.sub_le_sub_right n 1)) (Nat.mul_le_mul_left 2 n)) 1)
    (Nat.mul_le_mul_left 2 h)) 1

structure Book where
  fee : ℕ
  credit : ℕ
  mass : ℕ
  grade : ℕ

structure Branch where
  extra : ℕ
  primary : Book
  rescue : Book

def Branch.base (b : Branch) : ℕ := b.extra+b.primary.fee+b.rescue.fee

def Book.debit (b : Book) (r : ℕ) : ℕ := b.fee+(r-b.credit)*b.mass

def Branch.debit (b : Branch) (r : ℕ) : ℕ :=
  b.extra+b.primary.debit r+b.rescue.debit r

/-- The two actual prefix invoices and their retained integer masses.
Use zero paid and zero mass when there is no rescue. -/
structure Invoice (b : Branch) where
  extraPaid : ℕ
  primaryPaid : ℕ
  rescuePaid : ℕ
  primaryMass : ℕ
  rescueMass : ℕ
  extra_le : extraPaid≤b.extra
  primary_bill : primaryPaid+b.primary.credit*primaryMass≤b.primary.fee
  rescue_bill : rescuePaid+b.rescue.credit*rescueMass≤b.rescue.fee
  primary_cap : primaryMass≤b.primary.mass
  rescue_cap : rescueMass≤b.rescue.mass

def Invoice.paid {b : Branch} (I : Invoice b) : ℕ := I.extraPaid+I.primaryPaid+I.rescuePaid
def Invoice.mass {b : Branch} (I : Invoice b) : ℕ := I.primaryMass+I.rescueMass

private theorem book_debit (b : Book) {paid m r : ℕ}
    (cap : m≤b.mass) (bill : paid+b.credit*m≤b.fee) :
    paid+r*m≤b.debit r := by
  unfold Book.debit
  by_cases bound : r≤b.credit
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_right m bound) paid).trans
      (bill.trans (Nat.le_add_right _ _))
  · have eq : r=b.credit+(r-b.credit) := by omega
    calc
      paid+r*m = paid+b.credit*m+(r-b.credit)*m := by
        conv_lhs => rw [eq, Nat.add_mul]
        omega
      _ ≤ _ := Nat.add_le_add bill (Nat.mul_le_mul_left (r-b.credit) cap)

theorem Invoice.debit_le {b : Branch} (I : Invoice b) (r : ℕ) :
    I.paid+r*I.mass≤b.debit r := by
  unfold Invoice.paid Invoice.mass Branch.debit
  rw [Nat.mul_add]
  have main := book_debit b.primary I.primary_cap I.primary_bill (r:=r)
  have rescue := book_debit b.rescue I.rescue_cap I.rescue_bill (r:=r)
  have other := I.extra_le
  omega

theorem Invoice.credit_le {b : Branch} (I : Invoice b)
    (main : credit≤b.primary.credit) (rescue : credit≤b.rescue.credit) :
    I.paid+credit*I.mass≤b.base := by
  unfold Invoice.paid Invoice.mass Branch.base
  rw [Nat.mul_add]
  have hm := (Nat.add_le_add_left (Nat.mul_le_mul_right I.primaryMass main) _).trans I.primary_bill
  have hr := (Nat.add_le_add_left (Nat.mul_le_mul_right I.rescueMass rescue) _).trans I.rescue_bill
  have other := I.extra_le
  omega

structure Band where
  low : ℕ
  high : ℕ
  content : ℕ
  maxGraph : ℕ

def band : Fin 4 → Band :=
  ![⟨19,20,7,5⟩,⟨21,24,7,4⟩,⟨25,33,6,3⟩,⟨34,374,6,2⟩]

def bandFor (e : ℕ) : Fin 4 := if e≤20 then 0 else if e≤24 then 1 else if e≤33 then 2 else 3

theorem bandFor_bounds {e : ℕ} (lo : 19≤e) (hi : e≤graphCap) :
    (band (bandFor e)).low≤e ∧ e≤(band (bandFor e)).high := by
  change e ≤ 374 at hi
  unfold bandFor
  split <;> try split <;> try split
  all_goals
    simp [band]
    omega

def Band.off (b : Band) (a : ℕ) : ℕ := b.content-a
def Band.additive (b : Band) : ℕ := 2*b.high^2

def levels : Fin 23 → ℕ := ![0,1,2,3,4,5,6,7,8,10,12,15,19,24,32,48,64,96,160,256,512,1024,4096]
def upper (i : Fin 23) : Option ℕ :=
  if h : i.val+1<23 then some (levels ⟨i.val+1,h⟩-1) else none

def InBin (i : Fin 23) (v : ℕ) : Prop :=
  levels i≤v ∧ ∀ u, upper i = some u → v≤u

private def binsAt (v : ℕ) : Finset (Fin 23) :=
  Finset.univ.filter (fun i => levels i≤v)

private theorem bins_nonempty (v : ℕ) : (binsAt v).Nonempty :=
  ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ 0, Nat.zero_le v⟩⟩

def seedBin (v : ℕ) : Fin 23 := (binsAt v).max' (bins_nonempty v)

theorem seedBin_valid (v : ℕ) : InBin (seedBin v) v := by
  have chosen : seedBin v ∈ binsAt v := Finset.max'_mem _ (bins_nonempty v)
  refine ⟨(Finset.mem_filter.mp chosen).2, ?_⟩
  intro u eq
  unfold upper at eq
  split at eq
  · rename_i within
    let next : Fin 23 := ⟨(seedBin v).val+1,within⟩
    have value : levels next-1=u := Option.some.inj eq
    by_contra! tooBig
    have live : next ∈ binsAt v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have impossible : next≤seedBin v := Finset.le_max' _ _ live
    change (seedBin v).val+1≤(seedBin v).val at impossible
    omega
  · cases eq

end Research6966.NearLedger

end Merged_R6966ProofNearLedgerCore

-- merged module R6966ProofNearLedgerBudget
section Merged_R6966ProofNearLedgerBudget

namespace Research6966.NearLedger
set_option maxRecDepth 12000
set_option maxHeartbeats 0

def branch : Fin 58 → Branch :=
  ![⟨0, ⟨240122305198674767, 1828374077815, 7736, 220⟩, ⟨0, 1828374077815, 0, 0⟩⟩,
    ⟨416533811611925, ⟨240122305198674767, 1828374077815, 7736, 220⟩, ⟨0, 1828374077815, 0, 0⟩⟩,
    ⟨10632898488527429, ⟨185233047747540462, 1838347228855, 6160, 220⟩, ⟨0, 1828374077815, 0, 0⟩⟩,
    ⟨12000000000000000, ⟨185233047747540462, 1838347228855, 6160, 220⟩, ⟨0, 1828374077815, 0, 0⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨55793924646092275, 2203492493860, 5896, 154⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨52966495969959153, 2359182270245, 5715, 131⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨49288464967547301, 2376099868615, 5415, 132⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨38810346942555605, 2475696935960, 4427, 132⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨28105265459992834, 2554050539555, 2666, 145⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨13206613370585709, 3176395990275, 1619, 113⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5933515518403897, 3234294189700, 826, 55⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5235984048072161, 2882821816310, 820, 40⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨4561869216803883, 2712702142845, 762, 32⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨27875885778979703, 2558545636200, 3276, 133⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨27281212382701115, 2577523319005, 3200, 132⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨25923318675865290, 2590340332650, 3055, 133⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨21737866497188014, 2763866044610, 2588, 124⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨16642479830436074, 2891191446610, 1931, 124⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨9940541874649818, 3234294189700, 1222, 87⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5744268724374942, 3414264917535, 751, 58⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5327907282339369, 3056948333700, 762, 48⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨4722732019234886, 2882821816310, 738, 38⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨12971243220374339, 3234294189700, 1517, 98⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨12752171936355248, 3234294189700, 1434, 99⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨12637645649694967, 3234294189700, 1446, 98⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨11670208228550418, 3414264917535, 1309, 99⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨9840921658962126, 3414264917535, 1108, 89⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨7878171165247421, 3414264917535, 955, 77⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5828038718101279, 3596403450385, 718, 67⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5365702251384505, 3234294189700, 748, 51⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨4877651877782013, 3056948333700, 738, 42⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨7837859755555625, 3780354068890, 846, 87⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨7712204582539976, 3596403450385, 869, 79⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨7933252180329457, 3780354068890, 865, 85⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨7765540692437988, 3780354068890, 840, 86⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨7415482185496329, 3780354068890, 803, 85⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨6578449850475856, 3596403450385, 782, 71⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5373350808195588, 3596403450385, 643, 63⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5501308014295807, 3414264917535, 722, 58⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5183184408781634, 3234294189700, 724, 50⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5611203065645877, 4152616915935, 559, 75⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5705330680314931, 4152616915935, 575, 75⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5962380426836631, 4152616915935, 618, 76⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5930963484758957, 3965833672700, 622, 75⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨6034727864104571, 3965833672700, 651, 76⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5854587034500465, 3780354068890, 673, 69⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5205644515912856, 3780354068890, 613, 63⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5193076709205624, 3414264917535, 658, 56⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5115030531490045, 3234294189700, 702, 51⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨4817022442938847, 4719101025785, 442, 78⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨4777699928008097, 4529388060400, 456, 72⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨4917739195484850, 4340518392025, 493, 68⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5048245675359167, 4340518392025, 497, 72⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5137483949503584, 4152616915935, 529, 69⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5374518812809944, 3965833672700, 591, 69⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨4968408715399305, 3780354068890, 568, 62⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5294229975626841, 3596403450385, 647, 61⟩⟩,
    ⟨0, ⟨167997887646643864, 1849635312035, 5608, 220⟩, ⟨5223746972126276, 3414264917535, 690, 56⟩⟩]

def rescueBranch (i : Fin 54) : Fin 58 := ⟨i.val+4, by have := i.isLt; omega⟩
def free : ℕ := 34251763280165778

private def debitTable : Fin 48 → ℕ :=
  ![240538839010286692, 240538839010286692, 240538839010286692, 240538839010286692, 240538839010286692, 240538839010286692, 240538839010286692, 240538839010286692, 240538839010286692, 240538839010286692, 240668940684595660, 243734805648213628, 247097367221213980, 250756625403596716, 254712580195361836, 258965231596509340, 263514579607039228, 268360624226951500, 273503365456246156, 278942803294923196, 287100448822345651, 296071711553060563, 305484183926269651, 315337865941972915, 325632757600170355, 336368858900861971, 347546169844047763, 359164690429727731, 371224420657901875, 383725360528570195, 396667510041732691, 410050869197389363, 423875437995540211, 438141216436185235, 452848204519324435, 467996402244957811, 483585809613085363, 499616426623707091, 516088253276822995, 533001289572433075, 550355535510537331, 568150991091135763, 586387656314228371, 605065531179815155, 624184615687896115, 643744909838471251, 663746413631540563, 684189127067104051]

def nativeCap (n : ℕ) : ℕ := if h : n<48 then debitTable ⟨n,h⟩ else core+1

theorem branch_base (i : Fin 58) : (branch i).base+free≤core ∧
    credit≤(branch i).primary.credit ∧ credit≤(branch i).rescue.credit ∧
    (branch i).primary.mass+(branch i).rescue.mass≤massCap ∧
    (branch i).primary.grade+(branch i).rescue.grade≤graphCap := by
  fin_cases i <;> decide +kernel

private theorem cap0 : ∀ r : Fin 58, (branch r).debit (density 0)≤nativeCap 0 := by
  decide +kernel

private theorem cap1 : ∀ r : Fin 58, (branch r).debit (density 1)≤nativeCap 1 := by
  decide +kernel

private theorem cap2 : ∀ r : Fin 58, (branch r).debit (density 2)≤nativeCap 2 := by
  decide +kernel

private theorem cap3 : ∀ r : Fin 58, (branch r).debit (density 3)≤nativeCap 3 := by
  decide +kernel

private theorem cap4 : ∀ r : Fin 58, (branch r).debit (density 4)≤nativeCap 4 := by
  decide +kernel

private theorem cap5 : ∀ r : Fin 58, (branch r).debit (density 5)≤nativeCap 5 := by
  decide +kernel

private theorem cap6 : ∀ r : Fin 58, (branch r).debit (density 6)≤nativeCap 6 := by
  decide +kernel

private theorem cap7 : ∀ r : Fin 58, (branch r).debit (density 7)≤nativeCap 7 := by
  decide +kernel

private theorem cap8 : ∀ r : Fin 58, (branch r).debit (density 8)≤nativeCap 8 := by
  decide +kernel

private theorem cap9 : ∀ r : Fin 58, (branch r).debit (density 9)≤nativeCap 9 := by
  decide +kernel

private theorem cap10 : ∀ r : Fin 58, (branch r).debit (density 10)≤nativeCap 10 := by
  decide +kernel

private theorem cap11 : ∀ r : Fin 58, (branch r).debit (density 11)≤nativeCap 11 := by
  decide +kernel

private theorem cap12 : ∀ r : Fin 58, (branch r).debit (density 12)≤nativeCap 12 := by
  decide +kernel

private theorem cap13 : ∀ r : Fin 58, (branch r).debit (density 13)≤nativeCap 13 := by
  decide +kernel

private theorem cap14 : ∀ r : Fin 58, (branch r).debit (density 14)≤nativeCap 14 := by
  decide +kernel

private theorem cap15 : ∀ r : Fin 58, (branch r).debit (density 15)≤nativeCap 15 := by
  decide +kernel

private theorem cap16 : ∀ r : Fin 58, (branch r).debit (density 16)≤nativeCap 16 := by
  decide +kernel

private theorem cap17 : ∀ r : Fin 58, (branch r).debit (density 17)≤nativeCap 17 := by
  decide +kernel

private theorem cap18 : ∀ r : Fin 58, (branch r).debit (density 18)≤nativeCap 18 := by
  decide +kernel

private theorem cap19 : ∀ r : Fin 58, (branch r).debit (density 19)≤nativeCap 19 := by
  decide +kernel

private theorem cap20 : ∀ r : Fin 58, (branch r).debit (density 20)≤nativeCap 20 := by
  decide +kernel

private theorem cap21 : ∀ r : Fin 58, (branch r).debit (density 21)≤nativeCap 21 := by
  decide +kernel

private theorem cap22 : ∀ r : Fin 58, (branch r).debit (density 22)≤nativeCap 22 := by
  decide +kernel

private theorem cap23 : ∀ r : Fin 58, (branch r).debit (density 23)≤nativeCap 23 := by
  decide +kernel

private theorem cap24 : ∀ r : Fin 58, (branch r).debit (density 24)≤nativeCap 24 := by
  decide +kernel

private theorem cap25 : ∀ r : Fin 58, (branch r).debit (density 25)≤nativeCap 25 := by
  decide +kernel

private theorem cap26 : ∀ r : Fin 58, (branch r).debit (density 26)≤nativeCap 26 := by
  decide +kernel

private theorem cap27 : ∀ r : Fin 58, (branch r).debit (density 27)≤nativeCap 27 := by
  decide +kernel

private theorem cap28 : ∀ r : Fin 58, (branch r).debit (density 28)≤nativeCap 28 := by
  decide +kernel

private theorem cap29 : ∀ r : Fin 58, (branch r).debit (density 29)≤nativeCap 29 := by
  decide +kernel

private theorem cap30 : ∀ r : Fin 58, (branch r).debit (density 30)≤nativeCap 30 := by
  decide +kernel

private theorem cap31 : ∀ r : Fin 58, (branch r).debit (density 31)≤nativeCap 31 := by
  decide +kernel

private theorem cap32 : ∀ r : Fin 58, (branch r).debit (density 32)≤nativeCap 32 := by
  decide +kernel

private theorem cap33 : ∀ r : Fin 58, (branch r).debit (density 33)≤nativeCap 33 := by
  decide +kernel

private theorem cap34 : ∀ r : Fin 58, (branch r).debit (density 34)≤nativeCap 34 := by
  decide +kernel

private theorem cap35 : ∀ r : Fin 58, (branch r).debit (density 35)≤nativeCap 35 := by
  decide +kernel

private theorem cap36 : ∀ r : Fin 58, (branch r).debit (density 36)≤nativeCap 36 := by
  decide +kernel

private theorem cap37 : ∀ r : Fin 58, (branch r).debit (density 37)≤nativeCap 37 := by
  decide +kernel

private theorem cap38 : ∀ r : Fin 58, (branch r).debit (density 38)≤nativeCap 38 := by
  decide +kernel

private theorem cap39 : ∀ r : Fin 58, (branch r).debit (density 39)≤nativeCap 39 := by
  decide +kernel

private theorem cap40 : ∀ r : Fin 58, (branch r).debit (density 40)≤nativeCap 40 := by
  decide +kernel

private theorem cap41 : ∀ r : Fin 58, (branch r).debit (density 41)≤nativeCap 41 := by
  decide +kernel

private theorem cap42 : ∀ r : Fin 58, (branch r).debit (density 42)≤nativeCap 42 := by
  decide +kernel

private theorem cap43 : ∀ r : Fin 58, (branch r).debit (density 43)≤nativeCap 43 := by
  decide +kernel

private theorem cap44 : ∀ r : Fin 58, (branch r).debit (density 44)≤nativeCap 44 := by
  decide +kernel

private theorem cap45 : ∀ r : Fin 58, (branch r).debit (density 45)≤nativeCap 45 := by
  decide +kernel

private theorem cap46 : ∀ r : Fin 58, (branch r).debit (density 46)≤nativeCap 46 := by
  decide +kernel

private theorem cap47 : ∀ r : Fin 58, (branch r).debit (density 47)≤nativeCap 47 := by
  decide +kernel

private theorem cap_fin (g : Fin 48) (r : Fin 58) :
    (branch r).debit (density g.val)≤nativeCap g.val := by
  fin_cases g
  · exact cap0 r
  · exact cap1 r
  · exact cap2 r
  · exact cap3 r
  · exact cap4 r
  · exact cap5 r
  · exact cap6 r
  · exact cap7 r
  · exact cap8 r
  · exact cap9 r
  · exact cap10 r
  · exact cap11 r
  · exact cap12 r
  · exact cap13 r
  · exact cap14 r
  · exact cap15 r
  · exact cap16 r
  · exact cap17 r
  · exact cap18 r
  · exact cap19 r
  · exact cap20 r
  · exact cap21 r
  · exact cap22 r
  · exact cap23 r
  · exact cap24 r
  · exact cap25 r
  · exact cap26 r
  · exact cap27 r
  · exact cap28 r
  · exact cap29 r
  · exact cap30 r
  · exact cap31 r
  · exact cap32 r
  · exact cap33 r
  · exact cap34 r
  · exact cap35 r
  · exact cap36 r
  · exact cap37 r
  · exact cap38 r
  · exact cap39 r
  · exact cap40 r
  · exact cap41 r
  · exact cap42 r
  · exact cap43 r
  · exact cap44 r
  · exact cap45 r
  · exact cap46 r
  · exact cap47 r

theorem branch_native (r : Fin 58) {g : ℕ} (small : g<48) :
    (branch r).debit (density g)≤nativeCap g := cap_fin ⟨g,small⟩ r

theorem small_cap : nativeCap 18+17*18≤core := by decide +kernel
#print axioms branch_base
#print axioms branch_native
end Research6966.NearLedger

end Merged_R6966ProofNearLedgerBudget
