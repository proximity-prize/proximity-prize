import ProximityPrize.SubmissionLower.B7
set_option Elab.async false
set_option autoImplicit true
section
namespace anm
noncomputable section
open aR (Shape)
open aiI (Symbol acO)
def akp (P:Symbol) :Shape :=⟨P.totalDegree,acO P,P.degreeOf 3⟩
end
end anm
end
section
namespace anm
noncomputable section
open Polynomial
open MvPolynomial (weightedTotalDegree weightedTotalDegree_mul weightedTotalDegree_one weightedTotalDegree_piSingle weightedTotalDegree_C)

open aR (ao af Shape aO shape wU cK jet)
open aiI (LY)




open private IM from ProximityPrize.SubmissionLower.AB
open scoped BigOperators
private theorem aJZ {R:Type*} [CommRing R] [IsDomain R]
   (w:Fin 4→ℕ) (P:MvPolynomial (Fin 4) R) (hP:P≠0) (a :ℕ) :
   weightedTotalDegree w (P^a)=a*weightedTotalDegree w P:= by
 induction a with
 | zero=>rw [pow_zero,zero_mul,← MvPolynomial.C_1,weightedTotalDegree_C]
 | succ a ih =>
   rw [pow_succ,weightedTotalDegree_mul w _ _ (pow_ne_zero _ hP) hP,ih,Nat.succ_mul]
theorem aXI (P:af 4) (hP:P≠0) (a :ℕ) :
  shape (P^a)=(shape P).scale a := by
 have hb:=aJZ (1 :Fin 4→ℕ) P hP a
 have hj:=aJZ Fin.val P hP a
 have ht:=aJZ (Pi.single (3:Fin 4) 1) P hP a
 simp only [weightedTotalDegree_one] at hb
 simp only [← Ex.C6] at hj
 simp only [weightedTotalDegree_piSingle] at ht
 simp only [shape,Shape.scale]
 rw [hb,hj,ht]
theorem bhd {P Q:af 4} (hP:P≠0) (hQ:Q≠0) :
  shape (P*Q)=(shape P).plus (shape Q) := by
 have hb:=weightedTotalDegree_mul (1 :Fin 4→ℕ) P Q hP hQ
 have hj:=weightedTotalDegree_mul Fin.val P Q hP hQ
 have ht:=weightedTotalDegree_mul (Pi.single (3:Fin 4) 1) P Q hP hQ
 simp only [weightedTotalDegree_one] at hb
 simp only [← Ex.C6] at hj
 simp only [weightedTotalDegree_piSingle] at ht
 simp only [shape,Shape.plus]
 rw [hb,hj,ht]
theorem bNR {P Q:af 4} (hP:P≠0) (h:Q∣P) :
  aO (shape Q) (shape P) := by
 obtain ⟨H,hH⟩:=h
 have hn:Q*H≠0:=hH ▸ hP
 rw [hH,bhd (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn)]
 exact ⟨Nat.le_add_right _ _,Nat.le_add_right _ _,Nat.le_add_right _ _⟩
theorem bxm {x :ao} {P:af 4} (hP:P≠0)
  (hsup: (LY x P).support=P.support) :LY x P≠0:= by
 intro h
 apply hP
 apply MvPolynomial.support_eq_empty.mp
 rw [← hsup,h,MvPolynomial.support_zero]
theorem dgu (x :ao) (P:af 4) :
  aO (akp (LY x P)) (shape P) := by
 have h: (LY x P).support⊆P.support :=MvPolynomial.support_map_subset _ _
 exact ⟨Finset.sup_mono h,Finset.sup_mono h,by
  simp only [akp,shape,MvPolynomial.degreeOf_eq_sup]
  exact Finset.sup_mono h⟩
private theorem cpo (S:ao[X]) (F:af 4) :
  MvPolynomial.constantCoeff (IM S F)=cK F S:= by
 have h:MvPolynomial.constantCoeff.comp (IM S)=MvPolynomial.eval (jet S) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [IM]
  · intro i
    simp [IM]
 exact RingHom.congr_fun h F
theorem c2E {F G:af 4} {S:ao[X]} {d:ℕ}
    (hF:cK F S≠0) (h:wU (F*G) S d) :wU G S d:= by
  classical
  let A:=IM S F
  let B:=IM S G
  let deg (m:Fin 4 →₀ ℕ) :=m.sum (fun _ a=>a)
  have hA:A.coeff 0≠0:= by
    rw [← MvPolynomial.constantCoeff_eq,cpo]
    exact hF
  have hAB (m:Fin 4 →₀ ℕ) (hm:deg m<d) : (A*B).coeff m=0:= by
    by_contra hn
    apply (not_le_of_gt hm)
    apply h m
    change m∈(IM S (F*G)).support
    rw [map_mul]
    exact MvPolynomial.mem_support_iff.mpr hn
  have vanish (k :ℕ) : ∀ m,deg m=k→k<d→B.coeff m=0:= by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m hmk hk
      have heq : (A*B).coeff m=A.coeff 0*B.coeff m:= by
        rw [MvPolynomial.coeff_mul]
        apply Finset.sum_eq_single (0,m)
        · intro uv huv hne
          have hs :=Finset.HasAntidiagonal.mem_antidiagonal.mp huv
          have hu:uv.1≠0:= by
            intro hz
            apply hne
            rw [hz,zero_add] at hs
            exact Prod.ext hz hs
          have hpos :0<deg uv.1 := by
            obtain ⟨i,hi⟩:=Finsupp.support_nonempty_iff.mpr hu
            exact (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)).trans_le
              (Finset.single_le_sum (fun _ _=>Nat.zero_le _) hi)
          have hsum:deg uv.1+deg uv.2=k := by
            rw [← hmk,← hs]
            exact (Finsupp.sum_add_index' (fun _=>rfl) (fun _ _ _=>rfl)).symm
          rw [ih (deg uv.2) (by omega) _ rfl (by omega),mul_zero]
        · simp
      exact (mul_eq_zero.mp (heq ▸ hAB m (hmk ▸ hk))).resolve_left hA
  intro m hm
  by_contra! hk
  exact (MvPolynomial.mem_support_iff.mp hm) (vanish (deg m) m rfl hk)
end
end anm
end
section
namespace anm
noncomputable section
open aR (ceilDiv)
open scoped BigOperators
private theorem ceil_le_iff {M a n:ℕ} (ha :0<a) :
  ceilDiv M a≤n↔M≤a*n:= by
 rw [ceilDiv,← Nat.lt_succ_iff,Nat.div_lt_iff_lt_mul ha,Nat.succ_mul,Nat.mul_comm n a]
 omega
end
end anm
end
section
namespace cz6
noncomputable section




open MvPolynomial


open scoped BigOperators
private abbrev Exp:=Fin 4 →₀ ℕ
private abbrev index (m:Exp) :=m.sum (fun i a=>i.val*a)
end
end cz6
end
