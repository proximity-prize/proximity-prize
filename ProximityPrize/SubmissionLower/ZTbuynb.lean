import ProximityPrize.SubmissionLower.Z6Xnfpd
import ProximityPrize.SubmissionLower.ZRSUmIe
set_option Elab.async false
private theorem bothR {p q:Bool} {C:Prop} (h:(p && q)=true) (f:p=true → q=true → C) :C:= by
 simp only [Bool.and_eq_true] at h; exact f h.1 h.2
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qd4jtSc
open qMHqmcc (GG receipt appendGrades)
private theorem vQk0 :GG b2 16 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk1 :GG b2 17 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk2 :GG b2 18 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk3 :GG b2 19 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk4 :GG b2 20 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk5 :GG b2 21 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk6 :GG b2 22 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk7 :GG b2 23 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem r1 :GG b2 16 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQk0 vQk1) vQk2) vQk3) vQk4) vQk5) vQk6) vQk7
private theorem vQk8 :GG b2 24 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk9 :GG b2 25 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk10 :GG b2 26 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk11 :GG b2 27 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk12 :GG b2 28 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk13 :GG b2 29 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk14 :GG b2 30 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem vQk15 :GG b2 31 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | exact bothR (by decide +kernel) (receipt 2535 rfl)
private theorem r2 :GG b2 24 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQk8 vQk9) vQk10) vQk11) vQk12) vQk13) vQk14) vQk15
theorem p2_1 :GG b2 16 16:=appendGrades r1 r2
end qd4jtSc
end
section
set_option autoImplicit true
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace q20JTGa
noncomputable section
open Polynomial Finset P5_7_7
open P5 (I K)
open cu (L)
open scoped Classical
section Interpolation
variable {ι F:Type*} [Field F] {x y :ι→F}
structure InterpolationRow (x y :ι→F) where
 a :F[X]
 b:F[X]
 Ju : ∀ i,a.eval (x i)*y i+b.eval (x i)=0
def det (r s :InterpolationRow x y) :F[X] :=r.a*s.b-s.a*r.b
private abbrev bound (D:ℕ) (a b:F[X]) (d:ℕ) :Prop :=
 (a=0∨a.natDegree+D ≤d)∧b.natDegree≤d
structure InterpolationRows [Fintype ι] (D:ℕ) (x y :ι→F) where
 r :InterpolationRow x y
 s :InterpolationRow x y
 d₀:ℕ
 d₁:ℕ
 order :d₀≤d₁
 width :d₀+d₁=Fintype.card ι+D
 bound₀:bound D r.a r.b d₀
 bound₁:bound D s.a s.b d₁
 determinant : ∃ c:F,c≠0∧det r s=C c*Lagrange.nodal univ x
private def reduce (r s :InterpolationRow x y) (m:F[X]) :InterpolationRow x y :=
 ⟨s.a-m*r.a,s.b-m*r.b,fun i=> by
   simp only [eval_sub,eval_mul]
   calc
     _=s.a.eval (x i)*y i+s.b.eval (x i) -
         m.eval (x i)*(r.a.eval (x i)*y i+r.b.eval (x i)) := by ring
     _=0:= by rw [s.Ju,r.Ju,mul_zero,sub_zero]⟩
private def aug (D:ℕ) (r :InterpolationRow x y) :F[X] :=
 r.a*(Polynomial.X:F[X])^D
private def cap (D:ℕ) (r :InterpolationRow x y) :ℕ :=
 max (aug D r).natDegree r.b.natDegree
private def bit (D:ℕ) (r :InterpolationRow x y) :ℕ :=
 if r.b.coeff (cap D r)=0 then 0 else 1
private def weight (D:ℕ) (r :InterpolationRow x y) :ℕ :=
 2*cap D r+bit D r
private theorem weight_lt {D:ℕ} {r s :InterpolationRow x y} (h:cap D r<cap D s) :
  weight D r<weight D s := by
 unfold weight bit
 split <;> split <;> omega
private theorem shifted_cap (D:ℕ) (r :InterpolationRow x y) :
   bound D r.a r.b (cap D r) := by
 refine ⟨?_,le_max_right _ _⟩
 by_cases ha :r.a=0
 · exact Or.inl ha
 · apply Or.inr
   rw [cap,aug,natDegree_mul ha (pow_ne_zero _ X_ne_zero),natDegree_X_pow]
   exact le_max_left _ _
private theorem cap_drop {a b:F[X]} {n:ℕ} (ha :a.natDegree≤n) (hb:b.natDegree≤n)
   (hza :a.coeff n=0) (hzb:b.coeff n=0) (hne :a≠0∨b≠0) :
   max a.natDegree b.natDegree<n:= by
 have cut (f :F[X]) (h:f.natDegree≤n) (hz :f.coeff n=0) (hn:f≠0) :
     f.natDegree<n:= by
   rcases h.lt_or_eq with h | h
   · exact h
   · rw [← h,coeff_natDegree,leadingCoeff_eq_zero] at hz
     exact (hn hz).elim
 have hn:0<n:= by
   rcases hne with h | h
   · exact (Nat.zero_le _).trans_lt (cut a ha hza h)
   · exact (Nat.zero_le _).trans_lt (cut b hb hzb h)
 apply max_lt
 · by_cases h:a=0
   · simpa [h] using hn
   · exact cut a ha hza h
 · by_cases h:b=0
   · simpa [h] using hn
   · exact cut b hb hzb h
private theorem aPZ {D:ℕ} {r s :InterpolationRow x y} (hd:det r s≠0) :
   aug D r≠0∨r.b≠0:= by
 by_cases ha :r.a=0
 · exact Or.inr fun hb=>hd (by simp [det,ha,hb])
 · unfold aug
   exact Or.inl (mul_ne_zero ha (pow_ne_zero _ X_ne_zero))
private theorem col_sub {a b:F[X]} {d e :ℕ} (h:d≤e)
   (ha :a.natDegree≤d) (hb:b.natDegree≤e) (v :F) :
   let f :=b-monomial (e-d) v*a
   f.natDegree≤e∧f.coeff e=b.coeff e - v*a.coeff d:= by
 let m:F[X] :=monomial (e-d) v
 have hm:m.natDegree≤e-d:=natDegree_monomial_le _
 have he :e-d+d=e :=Nat.sub_add_cancel h
 refine ⟨(natDegree_sub_le _ _).trans (max_le hb (natDegree_mul_le.trans ?_)),?_⟩
 · exact (Nat.add_le_add hm ha).trans_eq he
 · change (b-m*a).coeff e= _
   have hc:=coeff_mul_add_eq_of_natDegree_le hm ha
   rw [he] at hc
   rw [coeff_sub,hc]
   simp [m]
private theorem det_swap (r s :InterpolationRow x y) :det s r = -det r s := by
 unfold det
 ring
private theorem det_reduce (r s :InterpolationRow x y) (m:F[X]) :
  det r (reduce r s m)=det r s := by
 simp only [det,reduce]
 ring
private theorem leading_det {D:ℕ} (r s :InterpolationRow x y)
    (hne :det r s≠0) (h:cap D r≤ cap D s)
    (minimal : ∀ m,weight D s≤weight D (reduce r s m)) :
    (det r s*(Polynomial.X:F[X])^D).natDegree=cap D r+cap D s := by
  let d:=cap D r
  let e :=cap D s
  have ar : (aug D r).natDegree≤d:=le_max_left _ _
  have br :r.b.natDegree≤d:=le_max_right _ _
  have as' : (aug D s).natDegree≤e :=le_max_left _ _
  have bs :s.b.natDegree≤e :=le_max_right _ _
  have det_eq :det r s*(Polynomial.X:F[X])^D =aug D r*s.b - r.b*aug D s := by
    unfold det aug
    ring
  have top {t:InterpolationRow x y} (ht:aug D t≠0∨t.b≠0)
      (hb:t.b.coeff (cap D t)=0) : (aug D t).coeff (cap D t)≠0:= by
    intro ha
    exact (lt_irrefl (cap D t)) (cap_drop (le_max_left _ _) (le_max_right _ _) ha hb ht)
  have nr :aug D r≠0∨r.b≠0:=aPZ hne
  have ns :aug D s≠0∨s.b≠0:=aPZ (by rw [det_swap]; exact neg_ne_zero.mpr hne)
  have subrow (v :F) :
      let t:=reduce r s (monomial (e-d) v)
      cap D t≤e∧(aug D t).coeff e=(aug D s).coeff e - v*(aug D r).coeff d ∧
        t.b.coeff e=s.b.coeff e - v*r.b.coeff d:= by
    have ha :=col_sub h ar as' v
    have hb:=col_sub h br bs v
    have heq :aug D (reduce r s (monomial (e-d) v)) =
        aug D s-monomial (e-d) v*aug D r := by
      simp only [aug,reduce]
      ring
    refine ⟨max_le ?_ hb.1,?_,hb.2⟩
    · rw [heq]
      exact ha.1
    · rw [heq]
      exact ha.2
  have different: (r.b.coeff d=0)≠(s.b.coeff e=0) := by
    intro heq
    by_cases hr :r.b.coeff d=0
    · have hs :=Eq.mp heq hr
      let v :=(aug D s).coeff e/(aug D r).coeff d
      let t:=reduce r s (monomial (e-d) v)
      obtain ⟨hle,ha,hb⟩:=subrow v
      have ha₀: (aug D t).coeff e=0:= by
        rw [ha,div_mul_cancel₀ _ (top nr hr),sub_self]
      have hb₀:t.b.coeff e=0:= by rw [hb,hr,hs,mul_zero,sub_zero]
      have nt:aug D t≠0∨t.b≠0:=aPZ (by rw [det_swap,det_reduce]; exact neg_ne_zero.mpr hne)
      have hlt:=cap_drop ((le_max_left _ _).trans hle) ((le_max_right _ _).trans hle) ha₀ hb₀ nt
      exact (not_lt_of_ge (minimal _)) (weight_lt hlt)
    · have hs :s.b.coeff e≠0:= fun hz=>hr (Eq.mpr heq hz)
      let v :=s.b.coeff e/r.b.coeff d
      let t:=reduce r s (monomial (e-d) v)
      obtain ⟨hle,_,hb⟩:=subrow v
      have hb₀:t.b.coeff e=0:= by rw [hb,div_mul_cancel₀ _ hr,sub_self]
      apply not_lt_of_ge (minimal _) (show weight D t<weight D s from ?_)
      rcases hle.lt_or_eq with hl | hl
      · exact weight_lt hl
      · have hb' : t.b.coeff (cap D t)=0:=hl.symm ▸ hb₀
        have hl' : cap D t=cap D s :=hl
        have h₀:bit D t=0:=ite_eq_left hb'
        have h₁:bit D s=1 :=ite_eq_right hs
        simp only [weight,h₀,h₁,hl',add_zero,Nat.lt_add_one]
  rw [det_eq]
  refine natDegree_eq_of_le_of_coeff_ne_zero
    ((natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le.trans (Nat.add_le_add ar bs))
      (natDegree_mul_le.trans (Nat.add_le_add br as')))) ?_
  rw [coeff_sub,coeff_mul_add_eq_of_natDegree_le ar bs,coeff_mul_add_eq_of_natDegree_le br as']
  by_cases hr :r.b.coeff d=0
  · have hs :s.b.coeff e≠0:= fun hs=>different (propext ⟨fun _=>hs,fun _=>hr⟩)
    rw [hr,zero_mul,sub_zero]
    exact mul_ne_zero (top nr hr) hs
  · have hs :s.b.coeff e=0:= by
      by_contra hn
      exact different (propext ⟨fun h=>(hr h).elim,fun h=>(hn h).elim⟩)
    rw [hs,mul_zero,zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hr (top ns hs))
private theorem interpolationRows [Fintype ι] (D:ℕ) (hx :Function.Injective x) :
   Nonempty (InterpolationRows D x y) := by
 let H :=Lagrange.nodal univ x
 let R:=Lagrange.interpolate univ x y
 let good (r s :InterpolationRow x y) := ∃ c:F,c≠0∧det r s=C c*H
 have flip {r s :InterpolationRow x y} (h:good r s) :good s r := by
   obtain ⟨c,hc,hd⟩:=h
   exact ⟨-c,neg_ne_zero.mpr hc,by rw [det_swap,hd,map_neg,neg_mul]⟩
 let A:InterpolationRow x y :=⟨1,-R,fun i=> by
   have hR:R.eval (x i)=y i :=
     Lagrange.eval_interpolate_at_node y hx.injOn (mem_univ i)
   rw [eval_one,eval_neg,hR,one_mul,add_neg_cancel]⟩
 let B:InterpolationRow x y :=⟨0,H,fun i=> by
   have hH :H.eval (x i)=0:=Lagrange.eval_nodal_at_node (mem_univ i)
   rw [eval_zero,zero_mul,zero_add,hH]⟩
 have hex : ∃ n,∃ r s :InterpolationRow x y,good r s∧weight D r+weight D s=n :=
   ⟨_,A,B,⟨1,one_ne_zero,by simp only [det,A,B,one_mul,zero_mul,sub_zero,map_one]⟩,rfl⟩
 obtain ⟨r,s,hg,hw⟩:=Nat.find_spec hex
 have smallest (r' s' : InterpolationRow x y) (hh:good r' s') :
     Nat.find hex≤weight D r'+weight D s' := Nat.find_min' hex ⟨r',s',hh,rfl⟩
 have finish (r' s' : InterpolationRow x y) (hh:good r' s') (ho:cap D r' ≤ cap D s')
     (hw' : weight D r'+weight D s' = Nat.find hex) :Nonempty (InterpolationRows D x y) := by
   obtain ⟨c,hc,hd⟩:=hh
   have hn:det r' s' ≠ 0:=hd ▸ mul_ne_zero (C_ne_zero.mpr hc) Lagrange.nodal_ne_zero
   have hdeg:=leading_det r' s' hn ho (fun m=> by
     have hm:=smallest r' (reduce r' s' m) ⟨c,hc,(det_reduce _ _ _).trans hd⟩
     omega)
   rw [natDegree_mul hn (pow_ne_zero _ X_ne_zero),natDegree_X_pow,hd,natDegree_C_mul hc] at hdeg
   change (Lagrange.nodal univ x).natDegree+D = _ at hdeg
   rw [Lagrange.natDegree_nodal,card_univ] at hdeg
   exact ⟨⟨r',s',_,_,ho,hdeg.symm,shifted_cap D r',shifted_cap D s',⟨c,hc,hd⟩⟩⟩
 by_cases h:cap D r≤ cap D s
 · exact finish r s hg h hw
 · exact finish s r (flip hg) (le_of_not_ge h) ((Nat.add_comm _ _).trans hw)
private theorem interpolation_target [Fintype ι] {D:ℕ}
   (J:InterpolationRows D x y) (hx :Function.Injective x) (i:ι) :
   J.r.a.eval (x i)≠0∨J.s.a.eval (x i)≠0:= by
 let H :=Lagrange.nodal univ x
 let R:=Lagrange.interpolate univ x y
 have aiq (r :InterpolationRow x y) :H∣r.a*R+r.b:=nodal_dvd hx (fun j hj=> by
   have hR:R.eval (x j)=y j:=Lagrange.eval_interpolate_at_node y hx.injOn hj
   rw [eval_add,eval_mul,hR,r.Ju])
 obtain ⟨q,hq⟩:=aiq J.r
 obtain ⟨t,ht⟩:=aiq J.s
 obtain ⟨c,hc,hd⟩:=J.determinant
 have he :J.r.a*t-J.s.a*q=C c:= by
   apply mul_left_cancel₀ (show H≠0 from Lagrange.nodal_ne_zero)
   calc
     _=J.r.a*(H*t)-J.s.a*(H*q) := by ring
     _=det J.r J.s := by rw [← ht,← hq]; unfold det; ring
     _ = _:=hd.trans (mul_comm _ _)
 by_contra hn
 obtain ⟨ha,hb⟩:=not_or.mp hn
 have ez :=congrArg (eval (x i)) he
 simp only [eval_sub,eval_mul,eval_C,not_not.mp ha,not_not.mp hb,zero_mul,sub_self] at ez
 exact hc ez.symm
end Interpolation
abbrev WordRow (w:I→K) :=
 InterpolationRow base (fun i=>algebraMap K L (w i))
abbrev WordRows (D:ℕ) (w:I→K) :=
 InterpolationRows D base (fun i=>algebraMap K L (w i))
theorem wordRows (D:ℕ) (w:I→K) :Nonempty (WordRows D w) :=
 interpolationRows D base_injective
theorem wordRows_target {D:ℕ} {w:I→K} (J:WordRows D w) (i:I) :
  J.r.a.eval (base i)≠0∨J.s.a.eval (base i)≠0 :=
 interpolation_target J base_injective i
end
end q20JTGa
end
