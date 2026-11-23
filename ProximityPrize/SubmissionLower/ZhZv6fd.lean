import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.ZskDvCd
set_option Elab.async false
section
set_option autoImplicit true
namespace P6_6_8
open aR (Shape aO)
open P6_6
open scoped BigOperators
open private aQC eiI fH dLQ from ProximityPrize.SubmissionLower.E6
private def cuts :List (ℕ×ℕ) :=
  [(3307,1710),(3335,1700),(3407,1650),(3470,1600),(3537,1550),
   (3585,1500),(3630,1450),(3678,1400),(3733,1350),(3781,1300),
   (3830,1250),(3878,1200),(3927,1150),(3975,1100),(4020,1050),
   (4025,1000),(4026,850)]
private theorem min_grade (r u:ℕ) :
    min r (Dj (r+u))=min r (fH (min (r+u) 4025) cuts) := by
  by_cases h:r+u≤4025
  · rw [min_eq_left h]
    have last :r+u<4026:= by omega
    simp only [Dj,cuts,fH,ite_eq_left last]
    by_cases h3307:r+u<3307
    · simp only [ite_eq_left h3307,← min_assoc,min_eq_left (Nat.le_add_right r u)]
    simp only [ite_eq_right h3307]
    by_cases h3335:r+u<3335
    · simp only [ite_eq_left h3335]; rfl
    simp only [ite_eq_right h3335]
    by_cases h3407:r+u<3407
    · simp only [ite_eq_left h3407]; rfl
    simp only [ite_eq_right h3407]
    by_cases h3470:r+u<3470
    · simp only [ite_eq_left h3470]; rfl
    simp only [ite_eq_right h3470]
    by_cases h3537:r+u<3537
    · simp only [ite_eq_left h3537]; rfl
    simp only [ite_eq_right h3537]
    by_cases h3585:r+u<3585
    · simp only [ite_eq_left h3585]; rfl
    simp only [ite_eq_right h3585]
    by_cases h3630:r+u<3630
    · simp only [ite_eq_left h3630]; rfl
    simp only [ite_eq_right h3630]
    by_cases h3678:r+u<3678
    · simp only [ite_eq_left h3678]; rfl
    simp only [ite_eq_right h3678]
    by_cases h3733:r+u<3733
    · simp only [ite_eq_left h3733]; rfl
    simp only [ite_eq_right h3733]
    by_cases h3781 :r+u<3781
    · simp only [ite_eq_left h3781]; rfl
    simp only [ite_eq_right h3781]
    by_cases h3830:r+u<3830
    · simp only [ite_eq_left h3830]; rfl
    simp only [ite_eq_right h3830]
    by_cases h3878:r+u<3878
    · simp only [ite_eq_left h3878]; rfl
    simp only [ite_eq_right h3878]
    by_cases h3927:r+u<3927
    · simp only [ite_eq_left h3927]; rfl
    simp only [ite_eq_right h3927]
    by_cases dk2 :r+u<3975
    · simp only [ite_eq_left dk2]; rfl
    simp only [ite_eq_right dk2]
    by_cases h4020:r+u<4020
    · simp only [ite_eq_left h4020]; rfl
    simp only [ite_eq_right h4020]
    by_cases doW:r+u<4025
    · simp only [ite_eq_left doW]; rfl
    simp only [ite_eq_right doW]
    rfl
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    change min r (Dj (r+u))=min r 850
    simp (disch:=omega) only [Dj,ite_eq_right]
private theorem eiJ {r x y :ℕ} (h:x≤y) :
    min r (Dj (r+y))≤ min r (Dj (r + x)) := by
  rw [min_grade r y,min_grade r x]
  exact min_le_min_left _ (dLQ cuts (min_le_min_right _ (Nat.add_le_add_left h r)))
theorem dNb {x y :Shape} (h:aO x y) :Gq y≤Gq x := by
  by_cases hy :y.b≤Wk.b∧y.j≤Wk.j∧y.t≤Wk.t
  · have hx :x.b≤Wk.b∧x.j≤Wk.j∧x.t≤Wk.t :=
      ⟨h.1.trans hy.1,h.2.1.trans hy.2.1,h.2.2.trans hy.2.2⟩
    simp only [Gq,ite_eq_left hy,ite_eq_left hx]
    apply aQC (Nat.succ_le_succ (Nat.sub_le_sub_left h.1 _))
    intro r
    exact eiI (eiJ h.1) (Nat.sub_le_sub_left h.2.1 _)
      (Nat.sub_le_sub_left h.2.2 _)
  · simp only [Gq,ite_eq_right hy,Nat.zero_le]
theorem Q5 {x y :Shape} (h:aO x y) (d:ℕ) :aO (x.scale d) (y.scale d) :=
  ⟨Nat.mul_le_mul_left d h.1,Nat.mul_le_mul_left d h.2.1,Nat.mul_le_mul_left d h.2.2⟩
theorem admissible_down {x y :Shape} (h:aO x y) :AdmissibleEarly y→AdmissibleEarly x := by
  intro hy
  exact hy.trans (Finset.sum_le_sum fun d _=>dNb (Q5 h (d+1)))
theorem not_companion_down {v x y :Shape} {ell:ℕ} (h:aO x y) :
    ¬ CompanionTest v y ell → ¬ CompanionTest v x ell:= by
  intro hy hx
  apply hy
  refine lt_of_le_of_lt (Finset.sum_le_sum fun d _=>dNb ?_) hx
  obtain ⟨hb,hj,ht⟩:= Q5 h (d+2 - ell)
  exact ⟨Nat.add_le_add_left hb _,Nat.add_le_add_left hj _,Nat.add_le_add_left ht _⟩
end P6_6_8
end
section
set_option autoImplicit true
namespace P6_6_8
open aR (Shape ceilDiv)
open P6_6
open private cEr from ProximityPrize.SubmissionLower.E6
private abbrev eB:Shape :=⟨1,0,0⟩
private abbrev eJ:Shape :=⟨0,1,0⟩
private abbrev eT:Shape :=⟨0,0,1⟩
private def Linear (f :Shape→ℤ) :Prop :=
  ∀ r,f r=(r.b:ℤ)*f eB+(r.j:ℤ)*f eJ+(r.t:ℤ)*f eT
private theorem lin_add {f g:Shape→ℤ} (hf :Linear f) (hg:Linear g) :
    Linear (fun r=>f r+g r) := by
  intro r
  dsimp only
  rw [hf r,hg r]
  ring
private theorem lin_sub {f g:Shape→ℤ} (hf :Linear f) (hg:Linear g) :
    Linear (fun r=>f r - g r) := by
  intro r
  dsimp only
  rw [hf r,hg r]
  ring
private theorem lin_mul_l {f :Shape→ℤ} {c:ℤ} (hf :Linear f) :
    Linear (fun r=>c*f r) := by
  intro r
  dsimp only
  rw [hf r]
  ring
private theorem lin_mul_r {f :Shape→ℤ} {c:ℤ} (hf :Linear f) :
    Linear (fun r=>f r*c) := by
  simpa only [mul_comm (f _) c] using lin_mul_l (c:=c) hf
private theorem lin_ite {p:Prop} [Decidable p] {f g:Shape→ℤ} (hf :Linear f) (hg:Linear g) :
    Linear (fun r=>if p then f r else g r) := by
  by_cases h:p
  · simpa only [ite_eq_left h] using hf
  · simpa only [ite_eq_right h] using hg
private theorem lin_b:Linear (fun r=>(r.b:ℤ)) := by
  intro r
  change (r.b:ℤ)=(r.b:ℤ)*1+(r.j:ℤ)*0+(r.t:ℤ)*0
  ring
private theorem lin_mixed (q a b:Shape) :Linear (fun r=>wP r q a b) := by
  intro r
  simp only [Ds.wP,aR.gI,aR.Dn,Shape.plus,
    FI.oL,Nat.cast_add]
  ring
private theorem lin_pair (dR:Bool) (p q:Shape) :Linear (fun r=>pair32 dR p r q) := by
  dsimp only [pair32]
  repeat' first
    | with_reducible exact lin_mixed _ _ _
    | with_reducible apply lin_ite
    | with_reducible apply lin_add
    | with_reducible apply lin_sub
    | with_reducible apply lin_mul_l
private theorem lin_curve (p q w:Shape) :Linear (fun r=>curve32 p r q w) :=
  lin_add (lin_mul_l (lin_mixed _ _ _)) (lin_mul_l (lin_mixed _ _ _))
private theorem lin_numerator (dR:Bool) (p q both:Shape) (ell boundT:ℕ) :
    Linear (fun r=>pairNumerator dR p r q both ell boundT) := by
  dsimp only [pairNumerator]
  repeat' first
    | with_reducible exact lin_pair _ _ _
    | with_reducible exact lin_curve _ _ _
    | with_reducible exact lin_mixed _ _ _
    | with_reducible exact lin_b
    | with_reducible apply lin_ite
    | with_reducible apply lin_add
    | with_reducible apply lin_sub
    | with_reducible apply lin_mul_l
    | with_reducible apply lin_mul_r
private theorem bvc (n:ℤ) {d:ℕ} (hd:0<d) :n≤(d:ℤ)*(ceilDiv n.toNat d:ℤ) := by
  have hn:n.toNat≤d*ceilDiv n.toNat d:= by
    unfold ceilDiv
    have hm:=Nat.mod_lt (n.toNat+d - 1) hd
    have he :=Nat.mod_add_div (n.toNat+d - 1) d
    omega
  exact (show n≤(n.toNat :ℤ) by omega).trans (by exact_mod_cast hn)
theorem large_majorized (v r :Shape) (he :0<sharedOrder v) :
    largeFee v r (Cj v) (sharedOrder v) (liftChoice v)≤dot (Lw v) r := by
  let d:=quoteDen (sharedOrder v)
  have hd:0<d:=Nat.mul_pos (Nat.mul_pos (by decide) he) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  change ceilDiv (quoteNum v r).toNat d≤dot (Lw v) r
  apply cEr
  have hlin:Linear (quoteNum v) :=lin_numerator _ _ _ _ _ _
  have h:quoteNum v r≤(d:ℤ)*(dot (Lw v) r :ℤ) := by
    rw [hlin r]
    calc
      _≤(r.b:ℤ)*((d:ℤ)*(ceilDiv (quoteNum v eB).toNat d:ℤ)) +
          (r.j:ℤ)*((d:ℤ)*(ceilDiv (quoteNum v eJ).toNat d:ℤ)) +
          (r.t:ℤ)*((d:ℤ)*(ceilDiv (quoteNum v eT).toNat d:ℤ)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (bvc _ hd) (Int.natCast_nonneg _))
          (mul_le_mul_of_nonneg_left (bvc _ hd) (Int.natCast_nonneg _)))
          (mul_le_mul_of_nonneg_left (bvc _ hd) (Int.natCast_nonneg _))
      _ = _:= by
        simp only [dot,Lw,Nat.cast_add,Nat.cast_mul,eB,eJ,eT,d]
        ring
  simpa only [← Nat.cast_mul,Int.toNat_natCast] using Int.toNat_le_toNat h
end P6_6_8
end
