import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZjobcJd
import ProximityPrize.SubmissionLower.ZcErkXc
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qK3TPae
noncomputable section
open Finset Polynomial



open q9NbxKa (nativeSlope)






open scoped Classical BigOperators
private theorem slope {e :ℕ} (he :0<e) (d:ℕ) :
  nativeSlope d e*((e :ℚ)*d)=(d:ℚ)^2/3+(4*(e :ℚ)^2+8*e)*d:= by
 have heq : (e :ℚ)≠0:=Nat.cast_ne_zero.mpr he.ne'
 unfold nativeSlope
 field_simp
 ring
end
end qK3TPae
end
section
set_option autoImplicit true
namespace qa5nZzb
noncomputable section
open Polynomial Finset
open P5 (K)
open P5_7_2 (fO row)
open q7F2qKe (wX)
open qxRSHvb (gap quadraticRate)
open qWdRihc (UJ asT exceptional_count)
open qrsE1ie (CoverIncidence NodeAllowance)


open private band_degrees from ProximityPrize.SubmissionLower.ZRqikKa


open scoped Classical
def c3:Prop :=qrsE1ie.c3
private theorem ng (M:UJ) {U B} (h:NodeAllowance U M.scalar M.word B) :
  asT M U B:= by
 intro i
 let native (γ:K) :Decidable (M.hit γ i) :=inferInstance
 let shared (γ:K) :Decidable (M.hit γ i) :=
  Classical.propDecidable (P5_7_7.hit M.word M.scalar γ i)
 have hhit := @filter_congr_decidable K U (fun γ=>M.hit γ i) shared native
 have hmiss := @filter_congr_decidable K U (fun γ => ¬M.hit γ i)
  (fun γ => @instDecidableNot (M.hit γ i) (shared γ))
  (fun γ => @instDecidableNot (M.hit γ i) (native γ))
 rw [← hhit,← hmiss]
 exact h i
private theorem dQt (M:UJ) {H :ℕ}
  (C:CoverIncidence M.CF M.scalar M.word H) :M.CF.card≤29*H+2 := by
 have hl:=exceptional_count M C.left C.left_sub _ (ng M C.left_nodes)
 have hr :=exceptional_count M C.right C.right_sub _ (ng M C.right_nodes)
 have hc:M.CF.card≤5*H+(C.left.card+C.right.card) := by
  rw [← card_sdiff_add_card_eq_card (union_subset C.left_sub C.right_sub)]
  exact Nat.add_le_add C.zJ (card_union_le _ _)
 calc
  _≤5*H+(6*(2*C.leftDegree*H)+1+(6*(2*C.rightDegree*H)+1)) :=
    hc.trans (Nat.add_le_add_left (Nat.add_le_add hl hr) _)
  _=5*H+12*H*(C.leftDegree+C.rightDegree)+2 := by ring
  _≤5*H+12*H*2+2 := by
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ C.boS) _) _
  _ = _:= by ring
private theorem rate_ge (b:fO) : (29:ℚ)≤quadraticRate b:= by
 have hgap:gap b≤48669:= by
  unfold gap wX
  change 179740-(131071+(row b).declaredHi)≤48669
  omega
 have hq: (gap b:ℚ)≤48669:= by exact_mod_cast hgap
 have hp: (0:ℚ)<(gap b:ℚ) := by
  apply Nat.cast_pos.mpr
  have h:=(band_degrees b).2
  unfold gap wX
  change 0<179740-(131071+(row b).declaredHi)
  omega
 have h: (16:ℚ)≤8*262144/(gap b:ℚ) := by
  apply (le_div_iff₀ hp).mpr
  linarith only [hq]
 show (29:ℚ)≤13+8*262144/(gap b:ℚ)
 linarith only [h]
end
end qa5nZzb
end
section
set_option autoImplicit true
namespace qYdH9sc
abbrev polarDegree (D g W:ℕ) :=(2*g-1)*W-g*g*D
abbrev poleFee (D g W:ℕ) :=(6*g-2)*W-3*g*g*D
def FilterOK (D g extra c W M:ℕ) :Prop :=
  let r :=(extra+1)*c
  let j:=r/(c+1)
  let e :=g+extra
  0<D ∧0<c∧g*D ≤W∧M=W+1+j*D ∧e*D <M ∧
    (c+1)*(D*(e*(e+1)+j*(j+1))/2)< r*M
end qYdH9sc
end
