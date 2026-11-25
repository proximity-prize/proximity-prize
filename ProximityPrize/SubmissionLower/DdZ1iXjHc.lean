import ProximityPrize.SubmissionLower.DdZQtCuFa
import ProximityPrize.SubmissionLower.DdZkuTDfa
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Ideal.Quotient.mkₐ→ oj,Ideal.subset_span→nq,Int.card_Icc_of_le→n5,LinearMap.range→c9,Module.finrank→cy,Nat.add_sub_of_le→lV,Nat.cast_add→lz,Nat.cast_sub→lJ,Nat.mul_le_mul_left→lI,Nat.mul_left_comm→nX,Nat.succ_eq_add_one→nI,Nat.succ_le_of_lt→ oq,P5_8_5.jetCaps→aU,mul_left_cancel₀→mD
section
set_option autoImplicit true
namespace qxVnKgd
open Finset P5_8_2
theorem sum_Icc_shift (f :ℤ→ℤ) (a b:ℤ) :
  (∑ x∈Icc a b,f x) = ∑ i∈range (b+1-a).toNat,f (a+i) := by
 rw [Int.Icc_eq_finset_map,sum_map]
 rfl
theorem sum_poly_value (f :ℕ→ℤ) (a b c d value :ℤ) (n:ℕ)
  (h : ∀ x∈range n,f x=poly a b c d x) (hv :sumFormula a b c d n = 12*value) :
  (∑ x∈range n,f x)=value := by
 rw [sum_congr rfl h]
 have ht:=(gvl a b c d n).trans hv
 omega
theorem H_even {x :ℤ} (hx :0≤x) :H (2*x)=x*(x+1) := by
 unfold H
 rw [show (2*x+1)/2=x by omega,show 2*x/2=x by omega]
 apply mD (by decide : (2:ℤ)≠0)
 linear_combination 2*twice_T hx
theorem H_odd {x :ℤ} (hx :0≤x) :H (2*x+1)=(x+1)^2 := by
 unfold H
 rw [show (2*x+1+1)/2=x+1 by omega,show (2*x+1)/2=x by omega]
 apply mD (by decide : (2:ℤ)≠0)
 linear_combination twice_T (by omega :0≤x+1)+twice_T hx
theorem sum_pairs (f :ℕ→ℤ) (n:ℕ) :
   (∑ i∈range (2*n),f i) = ∑ i∈range n,(f (2*i)+f (2*i+1)) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [show 2*(n+1)=(2*n+1)+1 by omega,sum_range_succ,sum_range_succ,ih,
     sum_range_succ,add_assoc]
theorem total_left: (∑ x∈region 2,score 2 x)=0x22d583b73ba := by
 change (∑ x∈(Icc (1:ℤ) 1959).sigma (fun o=>Icc (o-2641) 0),
   (961380-H x.1))= _
 rw [sum_sigma]
 simp only [sum_const,nsmul_eq_mul]
 have hh (o:ℤ) (ho:o∈Icc (1:ℤ) 1959) : (#(Icc (o-2641) 0) :ℤ)=2642-o:= by
   have :=(mem_Icc.mp ho).2
   rw [n5 _ _ (by omega)]
   omega
 rw [sum_congr rfl (fun o ho=> by rw [hh o ho]),sum_Icc_shift]
 let f (i:ℕ) :ℤ:=(2642-(1+(i:ℤ)))*(961380-H (1+(i:ℤ)))
 change (∑ i∈range (2*979+1),f i)= _
 rw [sum_range_succ,sum_pairs]
 have hp:=sum_poly_value (fun i=>f (2*i)+f (2*i+1)) 0x12e9d7af3 (-3858716) (-5271) 4
   0x22d58313d1e 979 ?_ (by decide)
 · rw [hp]
   have ht:f (2*979)=0xa369c:= by decide
   rw [ht]
   decide
 · intro i hi
   simp only [f,lz ,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
   rw [show (1+2*(i:ℤ))=2*(i:ℤ)+1 by ring,H_odd (by omega),
     show (1+(2*(i:ℤ)+1))=2*((i:ℤ)+1) by ring,H_even (by omega)]
   unfold poly
   ring
theorem total_both: (∑ x∈region 6,score 6 x)=0xa9555ac4 := by
 change (∑ x∈(Icc (2614:ℤ) 2939).sigma (fun s=>Icc (3920-s) (2*s-3920)),
  (2939-x.1)*(2940-x.1))= _
 rw [sum_sigma]
 simp only [sum_const,nsmul_eq_mul]
 have hh (s :ℤ) (hs :s∈Icc (2614:ℤ) 2939) : (#(Icc (3920-s) (2*s-3920)) :ℤ)=3*s-7839:= by
  have :=(mem_Icc.mp hs).1
  rw [n5 _ _ (by omega)]
  omega
 rw [sum_congr rfl (fun s hs=> by rw [hh s hs]),sum_Icc_shift]
 apply sum_poly_value _ 317850 315897 (-1950) 3 _ 326 _ (by decide)
 intro i _
 unfold poly
 ring
end qxVnKgd
end
section
namespace qTS2oyd
noncomputable section
open i4 P5_8 P5_8_5 MvPolynomial Filter
open aFz (GS aIz bJy anJ)
private abbrev kA (s :Jn) :=GS s.B s.J s.C
private def scale (u:Jn) (m:ℕ) :Jn:=⟨m*u.B,m*u.J,m*u.C⟩
def addCaps (a b:Jn) :Jn:=⟨a.B+b.B,a.J+b.J,a.C+b.C⟩
private def dM (a s :Jn) :Prop :=a.B≤ s.B∧a.J≤ s.J∧a.C≤ s.C
private def bF (s :Jn) :Prop :=s.J≤ s.B∧2*s.C≤ s.J
theorem jetCaps_mul {p q:BL 2} (hp:p≠0) (hq:q≠0) :
  aU (p*q)=addCaps (aU p) (aU q) := by
 simp only [aU,addCaps,totalDegree_mul_of_isDomain hp hq,
  weightedTotalDegree_mul _ _ _ hp hq,degreeOf_mul_eq hp hq]
private def mulBand (p:BL 2) (s :Jn) (h:dM (aU p) s) :
    kA (s.wD (aU p)) →ₗ[nU] kA s :=
  ((LinearMap.mulLeft nU p).domRestrict (kA (s.wD (aU p)))).codRestrict (kA s)
    (by
      intro z
      obtain ⟨hB,hJ,hC⟩:=h
      have hp:p∈kA (aU p) :=aIz.mpr ⟨le_rfl,le_rfl,le_rfl⟩
      change p*z.val∈kA s
      simpa only [Jn.wD,lV hB,lV hJ,lV hC]
        using bJy hp z.property)
private theorem mem_mulBand_range {p:BL 2} (hp:p≠0) {s :Jn}
    (h:dM (aU p) s) (x :kA s) :
    x∈c9 (mulBand p s h)↔p∣x.val := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.val,(congrArg Subtype.val hz).symm⟩
  · rintro ⟨z,hz⟩
    have hmem:z∈kA (s.wD (aU p)) := by
      by_cases hzero :z=0
      · rw [hzero]
        exact Submodule.zero_mem _
      have hx :=aIz.mp x.property
      rw [hz,totalDegree_mul_of_isDomain hp hzero,weightedTotalDegree_mul _ _ _ hp hzero,
        degreeOf_mul_eq hp hzero] at hx
      obtain ⟨hB,hJ,hC⟩:=hx
      apply aIz.mpr
      exact ⟨by change _≤ s.B - p.totalDegree; omega,
        by change _≤ s.J - p.weightedTotalDegree Fin.val; omega,
        by change _≤ s.C - p.degreeOf (Fin.last 2); omega⟩
    exact ⟨⟨z,hmem⟩,Subtype.ext hz.symm⟩
private theorem rank_mulBand {p:BL 2} (hp:p≠0) {s :Jn}
  (h:dM (aU p) s) :
  cy nU (c9 (mulBand p s h)) =
    cy nU (kA (s.wD (aU p))) := by
 apply LinearMap.finrank_range_of_inj
 intro y z hyz
 exact Subtype.ext (mD hp (congrArg Subtype.val hyz))
private theorem quotient_dim {L R:BL 2} (hL:L≠0) (hR:R≠0)
    (hc:IsRelPrime L R) (s :Jn) (hLs :dM (aU L) s) (hRs :dM (aU R) s)
    (hLRs :dM (aU (L*R)) s) :
    cy nU ((kA s).map (oj nU (ke L R)).toLinearMap) +
        cy nU (kA (s.wD (aU L))) +
        cy nU (kA (s.wD (aU R))) ≤
      cy nU (kA s)+Module.finrank nU (kA (s.wD (aU (L*R)))) := by
  let U:=c9 (mulBand L s hLs)
  let V:=c9 (mulBand R s hRs)
  let W:=c9 (mulBand (L*R) s hLRs)
  let q:=(oj nU (ke L R)).toLinearMap.domRestrict (kA s)
  have hLR:=mul_ne_zero hL hR
  have hInf :U ⊓ V=W:= by
    ext x
    change (x∈U∧x∈V)↔x∈W
    rw [mem_mulBand_range hL,mem_mulBand_range hR,mem_mulBand_range hLR]
    exact ⟨fun ⟨h₁,h₂⟩=>hc.mul_dvd h₁ h₂,
      fun h=>⟨(show L∣L*R from ⟨R,rfl⟩).trans h,
        (show R∣L*R from ⟨L,mul_comm _ _⟩).trans h⟩⟩
  have hker {p:BL 2} (hp:p≠0) (hs :dM (aU p) s)
      (hi:p∈ke L R) :c9 (mulBand p s hs)≤LinearMap.ker q:= by
    intro x hx
    obtain ⟨z,hz⟩:=(mem_mulBand_range hp hs x).mp hx
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (ke L R) x.val=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hz,mul_comm]
    exact (ke L R).mul_mem_left z hi
  have hSup:U ⊔ V≤LinearMap.ker q:=sup_le
    (hker hL hLs (nq (by simp))) (hker hR hRs (nq (by simp)))
  have hdim:=Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hInf,rank_mulBand hL,rank_mulBand hR,rank_mulBand hLR] at hdim
  have hle :=Submodule.finrank_mono hSup
  have hq:=q.finrank_range_add_finrank_ker
  rw [show c9 q=(kA s).map _ from LinearMap.range_domRestrict _ _] at hq
  omega
private theorem shifted_chamber (u a :Jn) (hC:0< u.C) (hCJ:2*u.C< u.J)
  (hJB:u.J< u.B) :
  ∀ᶠ m:ℕ in atTop,dM a (scale u m)∧bF ((scale u m).wD a) := by
 filter_upwards [eventually_ge_atTop (a.B+a.J+a.C)] with m hm
 have h₁:=lI m (oq hJB)
 have h₂:=lI m (oq hCJ)
 rw [nI,Nat.mul_add,Nat.mul_one] at h₁
 rw [nI,Nat.mul_add,Nat.mul_one,nX m 2] at h₂
 have h₃:m≤ m*u.C:=Nat.le_mul_of_pos_right _ hC
 simp only [dM,bF,scale,Jn.wD]
 omega
private theorem spent_count {s a :Jn} (ha :dM a s) (h:bF (s.wD a)) :
  (cy nU (kA (s.wD a)) :ℚ) =
    anJ ((s.B:ℚ)-a.B) ((s.J:ℚ)-a.J) ((s.C:ℚ)-a.C) := by
 obtain ⟨hB,hJ,hC⟩:=ha
 simpa only [Jn.wD,lJ hB,lJ hJ,lJ hC] using
  cxd.proof (s.wD a).B (s.wD a).J (s.wD a).C h.1 h.2
theorem proof :P5_8_5.c2 := by
 intro L R hL hR hc u hC hCJ hJB
 let a :=aU L
 let b:=aU R
 have hLR:=jetCaps_mul hL hR
 filter_upwards [shifted_chamber u a hC hCJ hJB,shifted_chamber u b hC hCJ hJB,
   shifted_chamber u (addCaps a b) hC hCJ hJB] with m ha hb hab
 let s :=scale u m
 have h₀:bF s := by
   refine ⟨lI m hJB.le,?_⟩
   simpa only [s,scale,nX m 2] using lI m hCJ.le
 have hnat :=quotient_dim hL hR hc s ha.1 hb.1 (hLR.symm ▸ hab.1)
 have hq:=(Nat.cast_le (α:=ℚ)).mpr hnat
 change ((cy nU (aEl (ke L R) u m) +
     cy nU (kA (s.wD a))+Module.finrank nU (kA (s.wD b)) :ℕ) :ℚ) ≤
   ((cy nU (kA s)+Module.finrank nU (kA (s.wD (aU (L*R)))) :ℕ) :ℚ) at hq
 rw [lz ,lz ,lz ,spent_count ha.1 ha.2,spent_count hb.1 hb.2,
   cxd.proof s.B s.J s.C h₀.1 h₀.2,hLR,spent_count hab.1 hab.2] at hq
 simp only [s,scale,addCaps,Nat.cast_mul,lz ,← sub_sub] at hq
 change (cy nU (aEl (ke L R) u m) :ℚ)≤boxDifference u a b m
 unfold boxDifference
 linarith only [hq]
end
end qTS2oyd
end
