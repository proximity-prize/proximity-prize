import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.Z9HmSkb
import ProximityPrize.SubmissionLower.ZRlaVZc
import ProximityPrize.SubmissionLower.ZYswgKc
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
namespace qzTRNDe
noncomputable section
open Polynomial Finset K1 aR wH Tx XU lB
open P6_6 (mV)
open P6_6_6 (ahv)
open scoped BigOperators
open private bOF cVW cFs b1T dlX from ProximityPrize.SubmissionLower.J
open private cFB from ProximityPrize.SubmissionLower.CU
private theorem fat_chart_chamber (p:Shape) :
    bF (P6_6_6.rH p)∧1≤(P6_6_6.rH p).t:= by
  unfold P6_6_6.rH
  split
  · let j:=3+P6_6.bf*(p.iU.j - 2)
    refine ⟨⟨le_max_right _ _,?_⟩,?_⟩
    · exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (Nat.mul_div_le _ _)
    · change 1≤ min (P6_6.bf+1) (j/3)
      exact le_min (by omega) (by omega)
  · have h:=Dr.aGY (P6_6.bf+4) p.iU (Nat.zero_lt_succ _)
    exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩
private theorem dLj {w Γ s} (hm:P6_6.Messages w Γ s) {H :Shape} (C:a1h H)
    (hC : ∀ γ∈Γ,C.ar5 (s γ)) {r :PrimeSpectrum gQ}
    (hr : ∀ γ∈Γ,r.asIdeal≤Ol (zq (extend (s γ)))) :
    ∃ (F:gQ) (Ig:Finset oe),Supported H F∧bTw r F Ig ∧
      mV*Γ.card≤P6.t* Ig.card+mV:= by
  classical
  let proper :=(univ :Finset I).filter (fun i => ∃ γ∈Γ,(s γ).eval (node i)≠w i)
  let lg (i:I) :=Γ.filter (fun γ=>(s γ).eval (node i)=w i)
  by_cases h:proper.Nonempty
  · obtain ⟨i,hi,hmax⟩:=proper.exists_max_image (fun i=>(lg i).card) h
    let F:gQ:=C.numerator i-MvPolynomial.C (constantCoeff (w i))*C.denominator
    let toPoint (γ:K) :=zq (extend (s γ))
    let Ig:=(lg i).image toPoint
    have hcard:Ig.card=(lg i).card:=Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact hm.distinct (filter_subset _ _ ha) (filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective (cVW hab)))
    refine ⟨F,Ig,cFs C i (w i),⟨?_,?_⟩,?_⟩
    · intro hF
      obtain ⟨γ,hγ,hne⟩:=(mem_filter.mp hi).2
      exact hne ((b1T (hC γ hγ) i (w i)).mp (RingHom.mem_ker.mp (hr γ hγ hF)))
    · intro y hy
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hy
      exact ⟨hr γ (mem_filter.mp hγ).1,
        (b1T (hC γ (mem_filter.mp hγ).1) i (w i)).mpr (mem_filter.mp hγ).2⟩
    · rw [hcard]
      exact P6_6_5.bv5 hm _ (fun j hj=>hmax j (mem_filter.mpr ⟨mem_univ _,hj⟩))
  · refine ⟨1,∅,?_,⟨r.isPrime.one_notMem,by simp⟩,?_⟩
    · simpa only [map_one] using bOF H (1 :cH)
    · apply P6_6_5.bv5 hm 0
      intro i hi
      exact (h ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩).elim
theorem proof :P6_6_6.c3:= by
  classical
  intro w Γ s hm f hf _hEligible hOn P Q _hpq hbP hbQ hHigh
  let H :=P6_6_6.rH (shape f)
  have hlift (γ:K) (hγ:γ∈Γ) :=
    ewb f P Q (extend (s γ)) (hOn γ hγ).1 (hHigh γ hγ)
  choose lift hLift hPoint using hlift
  let R:=Γ.attach.image (fun γ : {a // a∈Γ} => lift γ.val γ.property)
  let dO (r :PrimeSpectrum gQ) :=Γ.filter (fun γ =>
    r.asIdeal≤Ol (zq (extend (s γ))))
  have hR (r :PrimeSpectrum gQ) (hr :r∈R) :
      bQ6 f P Q r ∧ ∃ γ∈Γ,r.asIdeal<Ol (zq (extend (s γ))) := by
    obtain ⟨γ,_,rfl⟩:=mem_image.mp hr
    exact ⟨hLift γ.val γ.property,γ.val,γ.property,hPoint γ.val γ.property⟩
  have hcover :Γ.card ≤ ∑ r∈R,(dO r).card:= by
    refine (card_le_card (t:=R.biUnion dO) ?_).trans card_biUnion_le
    intro γ hγ
    exact mem_biUnion.mpr ⟨lift γ hγ,mem_image.mpr ⟨Subtype.mk γ hγ,mem_attach _ _,rfl⟩,
      mem_filter.mpr ⟨hγ,(hPoint γ hγ).le⟩⟩
  obtain ⟨C,hC⟩:=gKX f hf.2.1
  have hsections (r :PrimeSpectrum gQ) :
      ∃ (F:gQ) (Ig:Finset oe),Supported H F∧bTw r F Ig ∧
        mV*(dO r).card≤P6.t* Ig.card+mV :=
    dLj (hm.mono (filter_subset _ _)) C
      (fun γ hγ=>hC (s γ) (hm.degree γ (mem_filter.mp hγ).1)
        (hOn γ (mem_filter.mp hγ).1).1 (hOn γ (mem_filter.mp hγ).1).2)
      (fun _ hγ=>(mem_filter.mp hγ).2)
  choose cut Ig hCut hSection hFee using hsections
  have hDegree :=de0 f P Q hbP hbQ R (fun r hr=>(hR r hr).1)
    H (fat_chart_chamber (shape f)) cut Ig (fun r _=>⟨hCut r,hSection r⟩)
  have hlinear (r :PrimeSpectrum gQ) : ∃ (F:gQ) (singlePoint:Finset oe),
      (r∈R→Supported (shape f).iU F∧bTw r F singlePoint) ∧
      (r∈R→singlePoint.card = 1) := by
    by_cases hr :r∈R
    · obtain ⟨γ,_,hpoint⟩:=(hR r hr).2
      obtain ⟨F,hF,hproper,hmem,hzero⟩:=cFB hf.2.1 hpoint
      exact ⟨F,{zq (extend (s γ))},fun _=>⟨hF,hproper,by simpa using And.intro hmem hzero⟩,fun _=> by simp⟩
    · exact ⟨0,∅,fun h=>(hr h).elim,fun h=>(hr h).elim⟩
  choose linear singlePoint hLinear hOne using hlinear
  have hCount:=de0 f P Q hbP hbQ R (fun r hr=>(hR r hr).1)
    (shape f).iU ⟨Tn f,hf.2.1⟩ linear singlePoint hLinear
  rw [sum_congr rfl hOne,sum_const,smul_eq_mul,Nat.mul_one] at hCount
  have hsum:mV*Γ.card≤P6.t*(∑ r∈R,(Ig r).card)+mV*R.card:= calc
    _≤ mV*(∑ r∈R,(dO r).card) :=Nat.mul_le_mul_left _ hcover
    _ = ∑ r∈R,mV*(dO r).card:=mul_sum ..
    _ ≤ ∑ r∈R,(P6.t*(Ig r).card+mV) :=sum_le_sum fun r _=>hFee r
    _ = _:= by rw [sum_add_distrib,← mul_sum,sum_const,smul_eq_mul,Nat.mul_comm R.card]
  unfold P6_6_6.bHH
  dsimp only
  rw [P6_6_6.dRW,Nat.mul_right_comm 32 mV ahv]
  have hweight:0<32*ahv :=Nat.mul_pos (by decide) (by decide)
  have hgap:0< mV:= by
    change 0<46402
    decide
  exact dlX (32*ahv) P6.t mV (Nat.mul_pos hweight hgap)
    hsum hDegree hCount
end
end qzTRNDe
