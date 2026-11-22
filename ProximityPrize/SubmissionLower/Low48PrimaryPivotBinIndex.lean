import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinParity
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinWeight

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

namespace Low48PrimaryPivot
open Finset K1_13_2_3
open scoped BigOperators

def indexFiber (j : ℕ) : Finset Column :=
  univ.filter (fun col => (columnPoint col).index = j)

attribute [local irreducible] Finset.univ

private theorem mem_indexFiber {j : ℕ} {col : Column} :
    col ∈ indexFiber j ↔ (columnPoint col).index = j := by
  simp only [indexFiber,mem_filter,mem_univ,true_and]

private def fRange (j : ℕ) : Finset ℤ := Ico 0 ((j : ℤ)/3+1)

private def cRange (j : ℕ) (f : ℤ) : Finset ℤ := Ico 0 (sectionWidth j f.toNat)

private def fromBin (j : ℕ) (f c : ℤ) : Triple :=
  ⟨j-2*c.toNat-3*f.toNat,c.toNat,f.toNat⟩

private theorem fromBin_index {j : ℕ} {f c : ℤ} (_hf : f ∈ fRange j) (hc : c ∈ cRange j f) :
    (fromBin j f c).index = j := by
  rw [cRange,mem_Ico] at hc
  simp only [sectionWidth] at hc
  have hco : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc.1
  simp only [fromBin,Triple.index]
  omega

private theorem indexFiber_sum (j : ℕ) (hj : j ≤ 1650) (term : Triple → ℤ) :
    (∑ col ∈ indexFiber j, term (columnPoint col)) =
      ∑ f ∈ fRange j, ∑ c ∈ cRange j f, term (fromBin j f c) := by
  rw [sum_sigma']
  let position (col : Column) : Sigma (fun _ : ℤ => ℤ) := ⟨col.1.val,col.2.1.val⟩
  refine sum_bij (fun col _ => position col) ?_ ?_ ?_ ?_
  · intro col hcol
    have hkey := mem_indexFiber.mp hcol
    simp only [columnPoint,Triple.index] at hkey
    simp only [position,mem_sigma,fRange,cRange,mem_Ico,sectionWidth,Int.toNat_natCast]
    omega
  · intro col hcol other hother hpos
    have hf := congrArg Sigma.fst hpos
    have hc := congrArg (fun p : Sigma (fun _ : ℤ => ℤ) => p.snd) hpos
    simp only [position,Int.natCast_inj] at hf hc
    have hb := mem_indexFiber.mp hcol
    have hb' := mem_indexFiber.mp hother
    simp only [columnPoint,Triple.index] at hb hb'
    exact Prod.ext (Fin.ext hf) (Prod.ext (Fin.ext hc) (Fin.ext (by omega)))
  · rintro ⟨f,c⟩ hx
    obtain ⟨hf,hc⟩ := mem_sigma.mp hx
    change f ∈ fRange j at hf
    change c ∈ cRange j f at hc
    have hidx := fromBin_index hf hc
    have hf' := mem_Ico.mp hf
    have hc' := mem_Ico.mp hc
    let col : Column := (⟨f.toNat, by unfold fRange at hf; rw [mem_Ico] at hf; omega⟩,
      ⟨c.toNat, by
        have ho := hc'.2
        change c < sectionWidth j f.toNat at ho
        simp only [sectionWidth] at ho
        omega⟩,
      ⟨(fromBin j f c).b, by simp [fromBin]; omega⟩)
    refine ⟨col,mem_indexFiber.mpr ?_,?_⟩
    · exact hidx
    · change (⟨(f.toNat : ℤ),(c.toNat : ℤ)⟩ : Sigma (fun _ : ℤ => ℤ)) = ⟨f,c⟩
      rw [Int.toNat_of_nonneg hf'.1, Int.toNat_of_nonneg hc'.1]
  · intro col hcol
    have hb := mem_indexFiber.mp hcol
    simp only [columnPoint,Triple.index] at hb
    apply congrArg term
    simp only [columnPoint,fromBin,position,Int.toNat_natCast]
    congr 1
    omega

theorem indexFiber_card (j : ℕ) (hj : j ≤ 1650) :
    ((indexFiber j).card : ℤ) = totalAtIndex j := by
  have he := indexFiber_sum j hj (fun _ => 1)
  simp only [sum_const,nsmul_eq_mul,mul_one] at he
  rw [he,totalAtIndex_eq]
  apply sum_congr rfl
  intro f hf
  have hF := (mem_Ico.mp hf)
  change 0 ≤ f ∧ f < (j:ℤ)/3+1 at hF
  simp only [cRange,Int.card_Ico,sub_zero,sectionWidth,Int.toNat_of_nonneg hF.1]
  omega

theorem uncharged_card (j : ℕ) (q : ℤ) (hj : j ≤ 1650) :
    (((indexFiber j).filter fun col => q ≤ ((columnPoint col).contact : ℤ)).card : ℤ) =
      uncharged j q := by
  rw [natCast_card_filter]
  have he := indexFiber_sum j hj (fun p => if q ≤ (p.contact : ℤ) then 1 else 0)
  rw [he,uncharged_eq]
  let cost (f : ℤ) := max 0 ((j-3*f)/2+1 -
    max 0 (max (3*q-9900+5*j-3*f) (max (q-4950+3*j-2*f) (2*q-4950+2*j-f))))
  have sectionEq (f : ℤ) (hf : f ∈ fRange j) :
      (∑ c ∈ cRange j f, if q ≤ ((fromBin j f c).contact : ℤ) then (1 : ℤ) else 0) =
        if f ≤ 1650-q then cost f else 0 := by
    have hf0 := (mem_Ico.mp hf).1
    by_cases hF : f ≤ 1650-q
    · rw [ite_eq_left hF,← natCast_card_filter]
      have hfn : (f.toNat : ℤ) = f := Int.toNat_of_nonneg hf0
      have hsum : 3*f.toNat ≤ j := by
        unfold fRange at hf
        rw [mem_Ico] at hf
        omega
      have hrow := section_count j f.toNat q (by rwa [hfn]) hj hsum
      simpa only [cRange,fromBin,sectionWidth,sectionFloor,hfn,cost] using hrow
    · rw [ite_eq_right hF]
      apply sum_eq_zero
      intro c hc
      have hkey := fromBin_index hf hc
      have hb : (fromBin j f c).index ≤ 1650 := hkey.trans_le hj
      have hF' : ¬q ≤ ((fromBin j f c).contact : ℤ) := by
        intro hd
        have hlo := ((contact_ge_iff _ _ hb).mp hd).1
        apply hF
        simpa [fromBin,Int.toNat_of_nonneg hf0] using hlo
      rw [ite_eq_right hF']
  calc
    _ = ∑ f ∈ fRange j, if f ≤ 1650-q then cost f else 0 :=
      sum_congr rfl sectionEq
    _ = ∑ f ∈ (fRange j).filter (fun f => f ≤ 1650-q), cost f := (sum_filter ..).symm
    _ = _ := by
      have hs : (fRange j).filter (fun f => f ≤ 1650-q) =
          Ico 0 (min ((j : ℤ)/3) (1650-q)+1) := by
        ext f
        simp only [fRange,mem_filter,mem_Ico]
        omega
      rw [hs]

#print axioms indexFiber_card
#print axioms uncharged_card
end Low48PrimaryPivot
