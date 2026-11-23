import ProximityPrize.SubmissionLower.ZzQsYjc
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZaQt7ib
set_option Elab.async false
set_option autoImplicit true
namespace P4_6_6_1
noncomputable section
open Polynomial





open aR (af Shape aO shape iH)
open dN (GeoJets separant bC)
open BO (m6 asR)
open GJ (vE Ux)


open lB (amo abr)
open private bPY agr from ProximityPrize.SubmissionLower.B5


open scoped BigOperators
private theorem derivative_sum {f :af 4} (hf :Irreducible f)
    (hp:vE (m6 f)) {h:Shape} (hh:vE h)
    (uG:Finset (Ideal GeoJets)) (r w:Ideal GeoJets→ℕ)
    (hr : ∀ aI∈uG,r aI<(shape f).t)
    (hw : ∀ aI∈uG,w aI=0∨asR f aI (r aI) (w aI)) :
    32*(∑ aI∈uG,w aI *
      Ux aI ((m6 f).scale 6) (h.scale 6)) ≤
      36*((shape f).t*iH (m6 f) (m6 f) (m6 f) h) := by
  classical
  let p:=m6 f
  let value := fun aI=>w aI*Ux aI (p.scale 6) (h.scale 6)
  let gH :=uG.filter fun aI=>w aI≠0
  let orders :=Finset.range (shape f).t
  have hmaps : ∀ aI∈gH,r aI∈orders := by
    intro aI hs
    exact Finset.mem_range.mpr (hr aI (Finset.mem_filter.mp hs).1)
  have hpaid : (∑ aI∈gH,value aI) = ∑ aI∈uG,value aI:= by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro aI _
    by_cases hv :w aI=0 <;> simp [value,hv]
  have group (j:ℕ) :
      32*(∑ aI∈gH.filter (fun aI=>r aI=j),value aI) ≤
        36*iH p p p h:= by
    let RS:=gH.filter fun aI=>r aI=j
    by_cases he :RS.Nonempty
    · have data (aI:Ideal GeoJets) (hs :aI∈RS) :
          asR f aI j (w aI) := by
        obtain ⟨hpaid,htag⟩:=Finset.mem_filter.mp hs
        obtain ⟨hs,hpos⟩:=Finset.mem_filter.mp hpaid
        rw [← htag]
        exact (hw aI hs).resolve_left hpos
      obtain ⟨aI,hs⟩:=he
      let g:=(separant^[j]) f
      have hgproper : ¬ f∣g:=(data aI hs).1
      have hgfit :aO (shape g) p:=(data aI hs).2.1
      have hf0:=agr hf.ne_zero
      have hg0:bC g≠0:=agr fun hg =>
        hgproper (hg.symm ▸ dvd_zero f)
      exact bPY _ _ p p p h hf0 hg0 (amo f g hf hgproper)
        hp hp hp hh (abr ⟨le_max_left _ _,le_rfl,le_rfl⟩) (abr hgfit)
        RS w (fun t ht=>(data t ht).2.2.2)
    · rw [show gH.filter (fun aI=>r aI=j) = ∅ from
        Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty,mul_zero]
      exact Nat.zero_le _
  change 32*(∑ aI∈uG,value aI)≤36*((shape f).t*iH p p p h)
  calc
    _ = ∑ j∈orders,32*(∑ aI∈gH.filter (fun aI=>r aI=j),value aI) := by
      rw [← hpaid,← Finset.sum_fiberwise_of_maps_to hmaps value]
      simp only [Finset.mul_sum]
    _ ≤ ∑ _j∈orders,36*iH p p p h:=Finset.sum_le_sum fun j _=>group j
    _ = _:= by simp [orders,Nat.mul_left_comm]
end
end P4_6_6_1
