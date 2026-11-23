import ProximityPrize.SubmissionLower.Z6Xnfpd
import ProximityPrize.SubmissionLower.Z1G66Gc
import ProximityPrize.SubmissionLower.ZnaG81a
import ProximityPrize.SubmissionLower.Z2oJVua
set_option Elab.async false
open _root_ renaming Nat.cast_nonneg→cy,P5_7.FarBand→c9,P5_7_5.sheetCut→aU,add_le_add→lV,mul_le_mul_of_nonneg_left→lI
section
set_option autoImplicit true
namespace qH0Nw9c
noncomputable section
open Polynomial

open P5_7_1
open cu (FX Jet)

open DP (Source complete U4)


abbrev last :=introductions.length
abbrev Intro:=Fin last
abbrev shape (i:Intro) :=(introductions.get i).2
abbrev dI (i:Intro) :=(introductions.get i).1
abbrev anchorRow {x :Input} {P:Poles x} (pick :Picks x.h P.rows) :=
 (pick.main ⟨0,by decide⟩).free
structure Reference (x :Input) (P:Poles x) where
 raw:Source
 mem:raw∈complete P.crt x.word anchor.free (cutoff anchor.free)
 nonzero :U4 raw≠0
abbrev LineRow :=MvPolynomial (Fin 3) FX
def LineCaps (f :Jet) (g:LineRow) :Prop :=
 ∀ e∈g.support,e 1+e 2≤wD f 0∧e 2≤wD f 1∧e 0≤wD f 2
end
end qH0Nw9c
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qd4jtSc
open qMHqmcc (GG receipt appendGrades)
private theorem vQn0 :GG b2 32 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn1 :GG b2 33 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn2 :GG b2 34 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn3 :GG b2 35 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn4 :GG b2 36 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn5 :GG b2 37 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn6 :GG b2 38 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn7 :GG b2 39 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem r1 :GG b2 32 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQn0 vQn1) vQn2) vQn3) vQn4) vQn5) vQn6) vQn7
private theorem vQn8 :GG b2 40 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn9 :GG b2 41 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn10 :GG b2 42 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn11 :GG b2 43 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn12 :GG b2 44 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn13 :GG b2 45 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn14 :GG b2 46 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQn15 :GG b2 47 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem r2 :GG b2 40 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQn8 vQn9) vQn10) vQn11) vQn12) vQn13) vQn14) vQn15
theorem p2_2 :GG b2 32 16:=appendGrades r1 r2
end qd4jtSc
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
namespace qeA2Kad
open P5 (p)

open P5_7_5
private def base (b:c9) :ℕ :=
 pointFee b+lowSeedFee b+lowJetFee b+a4f b+contentBudget b
private def uq (b:c9) (D H :ℚ) :ℚ :=
 let q:=aU b
 let Q:ℚ:=(p+1 :ℕ)
 if q=0 then Q*D else max D (Q/(q+1 :ℕ))*D + alO b.row.hi q*H+D
private theorem curve_nonneg (b:c9) (hb:aU b≠0) :
  0≤alO b.row.hi (aU b) := by
 cases b <;> first | exact (hb rfl).elim | exact of_decide_eq_true (by with_unfolding_all rfl)
private theorem tariff_mono {b:c9} {D H :ℚ} (hD:0≤D)
   (hs :ash b≤D) (hh:heightLimit b≤H) :
   uq b (ash b) (heightLimit b)≤uq b D H := by
 by_cases hb:aU b=0
 · simp only [uq,ite_eq_left hb]
   exact lI hs (cy _)
 · simp only [uq,ite_eq_right hb]
   have hQ:0≤((p+1 :ℕ) :ℚ)/((aU b+1 :ℕ) :ℚ) :=
     div_nonneg (cy _) (cy _)
   have hm:=mul_le_mul hs (max_le_max_right _ hs) (hQ.trans (le_max_right _ _)) hD
   rw [mul_comm (ash b),mul_comm D] at hm
   exact lV (lV hm (lI hh (curve_nonneg b hb))) hs
private theorem ceil_nat {x :ℚ} {n:ℕ} (h:x≤n) :x.ceil.toNat≤n:= by
 have hz :x.ceil≤(n:ℤ) := by
  rw [Rat.ceil_eq_neg_floor_neg]
  change -⌊-x⌋ ≤ _
  rw [Int.floor_neg,neg_neg]
  exact Int.ceil_le.mpr (by exact_mod_cast h)
 simpa using Int.toNat_le_toNat hz
private abbrev gu (b:c9) :Prop :=
 pointFee b+lossFee b+lowSeedFee b+lowJetFee b+a4f b+contentBudget b ≤
  b.row.prefixFee
private theorem checked {b:c9} {xs :cL} {d e L:ℕ}
  (rows :aLW b xs d e (Fo b+1))
  (small: (total xs af.seed (Fo b+1) :ℚ)/d<p)
  (loss :uq b ((total xs af.seed (Fo b+1) :ℚ)/d)
    ((total xs af.height (Fo b+1) :ℚ)/e)≤L)
  (gH :base b+L≤b.row.prefixFee) :
  ash b<p∧gu b:= by
 have hs :=acI rows
 have hh:=height_le rows
 have hD:0≤(total xs af.seed (Fo b+1) :ℚ)/d :=
  div_nonneg (cy _) (cy _)
 have hL:lossFee b≤L:=ceil_nat ((tariff_mono hD hs hh).trans loss)
 refine ⟨hs.trans_lt small,?_⟩
 calc
  _=base b+lossFee b:= by unfold base; ac_rfl
  _≤base b+L:=Nat.add_le_add_left hL _
  _≤_:=gH
set_option quotPrecheck false in
local notation "az" => atY.mk (by decide) (by decide) (by decide) (by decide)
 (by with_unfolding_all rfl) (by with_unfolding_all rfl)
private def baseNumber :c9→ℕ
 | .dbl=>0x78b90c7bfbc54
 | .lZ=>0x2bd161666deb2
 | .om=>0x114a553ba0caa
 | .wS=>0x29043eb5bc5a
 | .vX=>0x228127d2c973
 | .vg=>0x368297b3d23
 | .wI=>0x191f1cfcb20
 | .vW=>0x1742a574d77
 | .wO=>0x14ad8f2779f
 | .wQ=>0x9f897c8cd7
private theorem base_eq (b:c9) :base b=baseNumber b:= by
 unfold base pointFee lowSeedFee lowJetFee
 rw [cb1,← b08,(rank_eq b).1,(rank_eq b).2]
 simp only [cVa,au9]
 cases b <;> with_unfolding_all rfl
set_option quotPrecheck false in
local notation "checked!" kA:arg sd:arg hd:arg loss:arg receipt:arg =>
 checked (b:=kA) (xs :=receipt) (d:=sd) (e :=hd) (L:=loss)
  (by intro i; fin_cases i <;> exact az)
  (of_decide_eq_true (by with_unfolding_all rfl))
  (of_decide_eq_true (by with_unfolding_all rfl))
  (by rw [base_eq]; exact Nat.le_of_ble_eq_true rfl)
set_option maxHeartbeats 1800000 in
private theorem eN2 : ∀ b,ash b<p∧gu b
 | .dbl=>checked! .dbl 0x1d42dcf00 0xa7f937c480 0x351a3e421d6823
   [⟨0,0x15faf3283cc6d00,0x1eee3c27e0934c380⟩,⟨266305,0x1731e260cf3b00,0x3eb0de45550d1d40⟩,⟨262209,
     0x2931d1e0e8e600,0x3c67e75fba40ec00⟩,⟨532545,0x79fdf4c8faa80,0xeb2779bb6cac170⟩,⟨524353,
     0x642fc6dc77880,0x1278f476d0ad1580⟩,⟨12353,0x1ff680c36d9200,0x4106fec899301800⟩,⟨802881,
     0x1d7959128aeb78,0x3cb154b519f1e800⟩,⟨1335426,0x3be7e35ec483b29,0x10522c2168a6aa476d⟩,⟨3,
     0x2491138310ad50,0x1e1eedc229177800⟩,⟨2404608,0x6e93f056c716c0,0x5ec6a61b323b9180⟩]
 | .lZ=>checked! .lZ 0x35c063c4 0x38157ccc 0x6b798458d2054
   [⟨0,0x128f4814a044e0,0x42d99a0fd802c8⟩,⟨262145,0x2ab745ac6f47c,0x88cbbfa5b2444⟩,⟨8257,0x2c33bdabf0154,
     0x86e82a89de080⟩,⟨532545,0x4541e3a532a8,0x200d783fb5e60⟩,⟨524353,0x5cac04abae20,0x1f8e749b155dc⟩,
     ⟨12353,0x1c270ee12a408,0x6f890fd876d50⟩,⟨1065025,0x25bd8fc76f9d4,0xaca5c241bc8b7⟩,⟨1601666,
     0x3720d4decbf15,0xf8f3442a98d0e⟩,⟨2932996,0x23fe7aee00cb6,0xedc700a56c5cf⟩]
 | .om=>checked! .om 0x581eb8d0 0xd04b7c1354 0x206a1924537822
   [⟨0,0xd3799c64555c0,0xa748ef78a1d13400⟩,⟨532545,0x1ea548a8a5a50,0x138c9eaf9f8e1f1a⟩,⟨798785,
     0x1792c0adfb3bb,0x1200ecd26593082d⟩,⟨1069186,0x22e81d8a9bf0c,0x135b62d952355710⟩,⟨1863872,
     0x2d1ed159e8fd0,0x18e7328299115aa0⟩,⟨3199301,0xe22b1275a470,0x8880628ba62aa79⟩]
 | .wS=>checked! .wS 29400 784 0x2e01206e87de7
   [⟨0,0x1774f5ba0,0x378e4000⟩,⟨532545,0x6b57bb54,0xaa80aa0⟩,⟨798785,0x7eac0363,0xd331073⟩,⟨1331330,
     0x384a4d00,63684864⟩]
 | .vX=>checked! .vX 5880 336 0x2847bd1d1ae6c
   [⟨0,0x3ee47738,0x10c82550⟩,⟨532545,0x13abbbe4,64475488⟩,⟨798785,0x17805225,81692583⟩,⟨1331330,
     0xa7e90e0,23781888⟩]
 | .vg=>checked! .vg 1 1 0x29221600a5d4
   [⟨0,21226,70773⟩]
 | .wI=>checked! .wI 1 1 0x113b44004578
   [⟨0,8892,16335⟩]
 | .vW=>checked! .vW 1 1 0x102f60004140
   [⟨0,8352,14205⟩]
 | .wO=>checked! .wO 1 1 0xec736003b94
   [⟨0,7626,11493⟩]
 | .wQ=>checked! .wQ 1 1 0x253cf000962
   [⟨0,1201, 2415⟩]
theorem proof :P5_7_5.c3:= by
 intro b
 obtain ⟨hs,hp⟩:=eN2 b
 exact schedule b hs hp
end qeA2Kad
end
