import ProximityPrize.SubmissionLower.ZxMkGTa
set_option Elab.async false
open _root_ renaming MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom → zOD
set_option autoImplicit true
section
namespace qBl3Pad
noncomputable section
open scoped Classical
open cu (L)
open P5_7_1_7_4_3_4 (pairDegree)
open qfbIfsd (Slot Vars form)
abbrev jo (s :ℕ) (b e :Fin 3→ℕ) :=z3y (Vars s b e) L
def ng (s :ℕ) (b e :Fin 3→ℕ) :Fin 3→ℕ :=
  ![pairDegree s (b 1) (e 1) (b 2) (e 2),pairDegree s (b 0) (e 0) (b 2) (e 2),
    pairDegree s (b 0) (e 0) (b 1) (e 1)]
def blockWeight {s :ℕ} {b e :Fin 3→ℕ} (k :Fin 3) (v :Vars s b e) :ℕ :=
 if v.1=k then 1 else 0
abbrev OtherVars (s :ℕ) (b e :Fin 3→ℕ) (k :Fin 3) := {v :Vars s b e // v.1≠k}
abbrev PairCoeffs (s :ℕ) (b e :Fin 3→ℕ) (k :Fin 3) :=
 z3y (OtherVars s b e k) L
abbrev MY (s :ℕ) (b e :Fin 3→ℕ) (k :Fin 3) :=
 FractionRing (PairCoeffs s b e k)
abbrev lK (s :ℕ) (b e :Fin 3→ℕ) (k :Fin 3) :=
 z3y (Fin 2) (MY s b e k)
def pairCoeff {s :ℕ} {b e :Fin 3→ℕ} (k :Fin 3) (v :Vars s b e) :MY s b e k :=
  if h:v.1≠k then
    algebraMap (PairCoeffs s b e k) (MY s b e k) (z9v ⟨v,h⟩)
  else 0
def pairForm (s :ℕ) (b e :Fin 3→ℕ) (k t:Fin 3) :lK s b e k :=
 form (fun v=>znf (pairCoeff k v)) t (z9v 0) (z9v 1)
def Ib (s :ℕ) (b e :Fin 3→ℕ) (k :Fin 3) :Ideal (lK s b e k) :=
 Ideal.span (pairForm s b e k '' {t | t≠k})
abbrev PairAlgebra (s :ℕ) (b e :Fin 3→ℕ) (k :Fin 3) :=
 lK s b e k ⧸ Ib s b e k
abbrev Chart (s :ℕ) (b e :Fin 3→ℕ) :=z3y (Fin 2 ⊕ Vars s b e) L
def zeroSlot (s b e :ℕ) :Slot s b e :=
 ⟨⟨0,Nat.zero_lt_succ _⟩,⟨0,Nat.zero_lt_succ _⟩⟩
def rest {M:Type} [CommSemiring M] {s :ℕ} {b e :Fin 3→ℕ}
    (a :Vars s b e→M) (t:Fin 3) (x y :M) :M :=
  ∑ i∈Finset.univ.erase (zeroSlot s (b t) (e t)),a ⟨t,i⟩*x^i.2.val*y ^i.1.val
def bcm {s :ℕ} {b e :Fin 3→ℕ} (v :Vars s b e) :Chart s b e :=
 z9v (.inr v)
def incidenceArg {s :ℕ} {b e :Fin 3→ℕ} (v :Vars s b e) :Chart s b e :=
  if v.2=zeroSlot s (b v.1) (e v.1) then
    -rest bcm v.1 (z9v (.inl 0)) (z9v (.inl 1))
  else bcm v
def incidence (s :ℕ) (b e :Fin 3→ℕ) :jo s b e →+* Chart s b e :=
 zOD znf incidenceArg
theorem form_eq {M:Type} [CommSemiring M] {s :ℕ} {b e :Fin 3→ℕ}
  (a :Vars s b e→M) (t:Fin 3) (x y :M) :
  form a t x y=a ⟨t,zeroSlot s (b t) (e t)⟩+rest a t x y := by
 unfold form rest
 rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (zeroSlot s (b t) (e t)))]
 simp [zeroSlot,add_comm]
theorem map_rest {M N :Type} [CommSemiring M] [CommSemiring N] (f :M →+* N)
  {s :ℕ} {b e :Fin 3→ℕ} (a :Vars s b e→M) (t:Fin 3) (x y :M) :
  f (rest a t x y)=rest (f ∘ a) t (f x) (f y) := by
 simp [rest,map_sum]
end
end qBl3Pad
end
section
namespace qBl3Pad
noncomputable section
open scoped Classical
open cu (L)
open qfbIfsd (Vars form kK Detects)
def c1 :Prop :=
  ∀ (s :ℕ) (b e :Fin 3→ℕ),(∀ t,0<e t)→0<b 1 →
    ∀ k :Fin 3,Module.Finite (MY s b e k) (PairAlgebra s b e k) ∧
      Module.finrank (MY s b e k) (PairAlgebra s b e k)≤ng s b e k
def c2 :Prop :=
  ∀ (s :ℕ) (b e :Fin 3→ℕ),(∀ t,0<e t)→0<b 1 →
    (∃ Q:jo s b e,Q≠0∧incidence s b e Q=0) →
    ∃ R:jo s b e,R≠0∧incidence s b e R=0 ∧
      ∀ Q:jo s b e,incidence s b e Q=0→R∣Q
def c3:Prop :=
  ∀ (s :ℕ) (b e :Fin 3→ℕ),(∀ t,0<e t)→0<b 1 →
    ∀ k :Fin 3,Module.Finite (MY s b e k) (PairAlgebra s b e k) →
      ∃ Q:jo s b e,Q≠0∧incidence s b e Q=0 ∧
        Q.weightedTotalDegree (blockWeight k)≤Module.finrank (MY s b e k) (PairAlgebra s b e k)
private theorem detects {s :ℕ} {b e :Fin 3→ℕ} {R:jo s b e}
   (hR:incidence s b e R=0) :Detects R:= by
 intro M _ m a x y hz
 let g:Fin 2 ⊕ Vars s b e→M:=Sum.elim ![x,y] a
 let f :=zOD m g
 have q0 (v :Vars s b e) :f (bcm v)=a v := by simp [f,g,bcm]
 have harg (v :Vars s b e) :f (incidenceArg v)=a v := by
   by_cases hv :v.2=zeroSlot s (b v.1) (e v.1)
   · have hv' : v=⟨v.1,zeroSlot s (b v.1) (e v.1)⟩:=Sigma.ext rfl (heq_of_eq hv)
     rw [incidenceArg,ite_eq_left hv,map_neg,map_rest]
     have hx :f (z9v (.inl 0))=x := by simp [f,g]
     have hy :f (z9v (.inl 1))=y := by simp [f,g]
     rw [hx,hy,show f ∘ bcm=a from funext q0]
     have h:=(form_eq a v.1 x y).symm.trans (hz v.1)
     exact (neg_eq_of_add_eq_zero_left h).trans (congrArg a hv').symm
   · rw [incidenceArg,ite_eq_right hv,q0]
 have hf :f.comp znf=m:= by ext l; simp [f]
 have h:=congrArg f hR
 change f (zOD znf incidenceArg R)=f 0 at h
 rw [MvPolynomial.map_eval₂Hom,hf,map_zero] at h
 simpa only [harg,MvPolynomial.coe_eval₂Hom] using h
private theorem ags {s :ℕ} {b e :Fin 3→ℕ} (R:jo s b e)
   (h : ∀ k,R.weightedTotalDegree (blockWeight k)≤ng s b e k) :
   R.totalDegree≤ kK s b e := by
 rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
 intro m hm
 have hs : (∑ k :Fin 3,Finsupp.weight (blockWeight k) m)=m.sum (fun _ n=>n) := by
   simp only [Finsupp.weight_apply,Finsupp.sum]
   rw [Finset.sum_comm]
   simp [blockWeight]
 have ha : (∑ k :Fin 3,ng s b e k)=kK s b e := by
   simp only [Fin.sum_univ_three,ng,Matrix.cons_val_zero,Matrix.cons_val_one,
     Matrix.cons_val_two,kK]
   ac_rfl
 rw [← hs,← ha]
 exact Finset.sum_le_sum fun k _=>(MvPolynomial.le_weightedTotalDegree _ hm).trans (h k)
end
end qBl3Pad
end
