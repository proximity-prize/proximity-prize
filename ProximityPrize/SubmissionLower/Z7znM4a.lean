import ProximityPrize.SubmissionLower.ZFO2WXb
import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZLt6kU
set_option Elab.async false
set_option maxHeartbeats 6000000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qlc9qed
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open P5 (K)

open aR (ao af embed extend cK jet)
open jA Rk




open private values from ProximityPrize.SubmissionLower.ZFO2WXb
open scoped BigOperators
private theorem eval_rename_top (F:jK) (z :K) (S:K[X]) :
    MvPolynomial.eval (values z S) (toTop F) =
      cK (JX (C (embed z)) F) (extend S) := by
  rw [toTop,MvPolynomial.eval_rename]
  let v :=values z S ∘ aD
  have hv :MvPolynomial.eval v=(MvPolynomial.eval (jet (extend S))).comp
      (JX (C (embed z))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [JX]
    · intro i
      cases i with
      | none=>simp [JX,v,values,aD]
      | some j =>
        simp only [MvPolynomial.eval_X,RingHom.comp_apply,JX,MvPolynomial.eval₂Hom_X',
          Option.elim_some]
        fin_cases j
        · change cu.j9 S=hasseDeriv 0 (extend S)
          rw [hasseDeriv_zero]
          rfl
        · change cu.j9 S.derivative=hasseDeriv 1 (extend S)
          rw [hasseDeriv_one,derivative_map]
          rfl
        · change cu.j9 (hasseDeriv 2 S)=hasseDeriv 2 (extend S)
          exact (hasseDeriv_map embed 2 S).symm
  exact DFunLike.congr_fun hv F
private theorem raw_eval_degree {T:ao[X]} {t:ℕ} {Q:af 3}
   (hT:T.natDegree≤131071) (hQ:a04 t Q) : (cK Q T).natDegree≤t:= by
 classical
 rw [cK,MvPolynomial.eval_eq]
 apply natDegree_sum_le_of_forall_le
 intro a ha
 apply natDegree_mul_le.trans
 refine (Nat.add_le_add_left ((natDegree_prod_le _ _).trans ?_) _).trans (hQ a ha)
 apply Finset.sum_le_sum
 intro j _
 calc
   _≤a j*(jet T j).natDegree :=natDegree_pow_le
   _≤a j*(131071 - j.val) :=Nat.mul_le_mul_left _
     ((natDegree_hasseDeriv_le T j.val).trans (Nat.sub_le_sub_right hT j.val))
   _ = _:=Nat.mul_comm _ _
end
end qlc9qed
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qlc9qed
noncomputable section

open aR (ao)
open jA
open NR (TT)



def c2 :Prop :=
  ∀ (b:Bank) (a v :ao) (V:Submodule ao jK),Module.Finite ao V →
    (∀ F∈V,Jn b.box F∧gY F≤b.U) →
    TT V (ays b.m a v)≤(b.U+1)*b.contactRank
private theorem exists_row (V:Submodule ao jK) (hV:0<Module.finrank ao V) :
  ∃ F∈V,F≠0:= by
 let:Nontrivial V:=Module.nontrivial_of_finrank_pos hV
 obtain ⟨F,hF⟩:=exists_ne (0:V)
 exact ⟨F.val,F.property,fun h=>hF (Subtype.ext h)⟩
private theorem degree_dvd {F G:ko} (i:mA) (hF:F≠0) (hd:G∣F) :
  G.degreeOf i≤F.degreeOf i:= by
 obtain ⟨Q,e⟩:=hd
 rw [e] at hF
 have hn:=mul_ne_zero_iff.mp hF
 rw [e,MvPolynomial.degreeOf_mul_eq hn.1 hn.2]
 exact Nat.le_add_right _ _
end
end qlc9qed
end
section
set_option autoImplicit true
namespace q5oHm3d
open cu (Shape)
open P5_7_2 (Ls)
open TD (GM)
private theorem tent_mix (cap rise base cU l t r :ℚ) (hl:l≤t) (hr :t≤ r) :
    (r-t)*tent cap rise base cU l+(t-l)*tent cap rise base cU r ≤
      (r-l)*tent cap rise base cU t:= by
  have hmono:Monotone (fun x :ℚ=>(r-l)*x) :=
    fun _ _ h=>mul_le_mul_of_nonneg_left h (sub_nonneg.mpr (hl.trans hr))
  conv_rhs=>unfold tent; rw [hmono.map_min,hmono.map_min]
  have bound (a b:ℚ) (h₁:tent cap rise base cU l≤a+b*l)
      (h₂:tent cap rise base cU r≤a+b*r) :
      (r-t)*tent cap rise base cU l+(t-l)*tent cap rise base cU r ≤
        (r-l)*(a+b*t) := by
    calc
      _≤(r-t)*(a+b*l)+(t-l)*(a+b*r) :=add_le_add
        (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hr))
        (mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hl))
      _ = _:= by ring
  refine le_min ?_ (le_min ?_ ?_)
  · simpa only [zero_mul,add_zero] using bound cap 0
      (by rw [zero_mul,add_zero]; exact min_le_left _ _)
      (by rw [zero_mul,add_zero]; exact min_le_left _ _)
  · simpa only [zero_add] using bound 0 rise
      (by rw [zero_add]; exact (min_le_right _ _).trans (min_le_left _ _))
      (by rw [zero_add]; exact (min_le_right _ _).trans (min_le_left _ _))
  · simpa only [neg_mul,← sub_eq_add_neg] using bound base (-cU)
      (by simpa [tent,sub_eq_add_neg] using
        (min_le_right cap _).trans (min_le_right (rise*l) (base-cU*l)))
      (by simpa [tent,sub_eq_add_neg] using
        (min_le_right cap _).trans (min_le_right (rise*r) (base-cU*r)))
private theorem cell_mix (s :Ls) (d:Shape) (c:GM) (n e :ℕ)
    (l t r :ℚ) (hl:l≤t) (hr :t≤ r) :
    (r-t)*PN s d c n e l+(t-l)*PN s d c n e r≤(r-l)*PN s d c n e t:= by
  simp only [PN]
  apply le_of_sub_nonneg
  have h₁:=mul_nonneg (Nat.cast_nonneg (α:=ℚ) (d.B-d.J))
    (sub_nonneg.mpr (tent_mix (c 1) 1 (proper (shrink s.free n e 0) (shrink s.moving n e 0)
      (s.dI+1-n) 1)
      ((n*((shrink s.free n e 0).J+(shrink s.moving n e 0).J) :ℕ) /
        ((s.dI+1-n)^2 :ℕ)) l t r hl hr))
  have h₂:=mul_nonneg (Nat.cast_nonneg (α:=ℚ) d.J)
    (sub_nonneg.mpr (tent_mix (c 2) (2*(e :ℚ))
      (proper (shrink s.free n e 0) (shrink s.moving n e 0) (s.dI+1-n) 2)
      ((n*((shrink s.free n e 0).B+(shrink s.moving n e 0).B) :ℕ) /
        ((s.dI+1-n)^2 :ℕ)) l t r hl hr))
  linear_combination h₁+h₂
private theorem cbw {f :ℕ→ℚ} (mix : ∀ l t r :ℕ,l≤t→t≤ r →
   ((r :ℚ)-t)*f l+((t:ℚ)-l)*f r≤((r :ℚ)-l)*f t)
   {hi t v :ℕ} (h:Peak f hi t) (hv :v≤hi) :f v≤f t:= by
 rcases lt_trichotomy v t with hlt | rfl | hgt
 · have ht:0<t:= by omega
   have hm:=mix v (t-1) t (by omega) (by omega)
   have hh:=mul_le_mul_of_nonneg_left (h.2.1 ht)
     (sub_nonneg.mpr (show (v :ℚ)≤t from Nat.cast_le.mpr hlt.le))
   rw [Nat.cast_sub (show 1≤t by omega),Nat.cast_one] at hm
   linarith only [hm,hh]
 · exact le_rfl
 · have ht:t<hi:=hgt.trans_le hv
   have hm:=mix t (t+1) v (by omega) (by omega)
   have hh:=mul_le_mul_of_nonneg_left (h.2.2 ht)
     (sub_nonneg.mpr (show (t:ℚ)≤v from Nat.cast_le.mpr hgt.le))
   rw [Nat.cast_add,Nat.cast_one] at hm
   linarith only [hm,hh]
theorem cell_le_peak {s :Ls} {d:Shape} {c:GM} {n e hi t v :ℕ}
  (h:Peak (fun v=>PN s d c n e v) hi t) (hv :v≤hi) :
  PN s d c n e v≤PN s d c n e t :=
 cbw (fun l t r hl hr=>cell_mix s d c n e l t r (Nat.cast_le.mpr hl) (Nat.cast_le.mpr hr))
  h hv
theorem peak_of_bound {f :ℕ→ℚ} {hi:ℕ} {dm:ℚ}
  (h : ∀ v≤hi,f v≤dm) : ∃ t,Peak f hi t∧f t≤dm:= by
 obtain ⟨t,ht,hmax⟩:=Finset.exists_max_image (Finset.range (hi+1)) f
  ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
 have ht' := Finset.mem_range.mp ht
 exact ⟨t,⟨by omega,fun _=>hmax _ (Finset.mem_range.mpr (by omega)),
  fun _=>hmax _ (Finset.mem_range.mpr (by omega))⟩,h t (by omega)⟩
end q5oHm3d
end
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
private def d0_0:=s2! 7521 1571 1571 42 8 0x94cc82db401e1ed7c944b5a8fd82ad00fd047f6b4027ea478ad00552d3ceb40082436ead0004d3fa6b40
private def d0_1 :=s2! 7521 1571 3619 43 8 0x84695b6da010510f05b401fc7a53b6803d15d8d6d0073afce6da00d755d65b40188741fb6802b831256d00
private def d0_2 :=s2! 7521 1571 5667 43 8 0x5c4173aceaccd27245b401bdc6bbb6803b6365d6d007c92e86da0101ac0a5b4020e4087b68042609f56d00
private def d0_3:=s2! 7521 1571 7715 42 8 0x1b4626eaa00a5dd800a803a218b70c9932cd940d7f60d2f0c338dd8853b331a8c2be2ca8f289e0fd3617
private def d0_4 :=s2! 7521 1571 9763 38 4 0x1609a7c708121e8a80750babaa03f3fbf4a80
private def r0:=j2! 7521 1571 0x4d9c456593b2 [d0_0,d0_1,d0_2,d0_3,d0_4]
private def d1_0:=s2! 8774 1832 1832 42 8 0xbbeb98a3d0a4c136962406d2588c89012edd5ce2402f7a45a890064b95062400993828890005a743e240
private def d1_1 :=s2! 8774 1832 3880 43 8 0xc84c288d801828a569b002e1cfb8360056ec3866c00a172b38d80126856c9b0020d21e4360038c1fde6c00
private def d1_2 :=s2! 8774 1832 5928 43 8 0xc013128d8018ebc2a9b003337b603600684aad66c00d2819d8d801a547409b00343ed8c360066c472e6c00
private def d1_3:=s2! 8774 1832 7976 43 8 0x5520fafc0f2c7c3ec6b94dcbe07b3f07c1129013808912736dbcd73ee9149b002b0793436005b7ee7e6c00
private def d1_4 :=s2! 8774 1832 10024 42 8 0x7e7123df80467ee087e01ef12805f80be7d87a7e0436e65cdf8168787aef34730e399274a37813d7b0c
private def d1_5:=s2! 8774 1832 12072 36 2 0x3c0d82ea80cd967e0
private def r1 :=j2! 8774 1832 0x8fae93773c8c [d1_0,d1_1,d1_2,d1_3,d1_4,d1_5]
def dataJ:Array aqm := #[
 r0,r1
]
end qpECY2d
end
