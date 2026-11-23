import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import ProximityPrize.SubmissionLower.R
set_option Elab.async false
open _root_ renaming Finsupp.weight_apply→cy,MvPolynomial.aeval_X→lJ,MvPolynomial.optionEquivRight→mD,MvPolynomial.ringHom_ext→lV,RingHom.congr_fun→lI,finSuccEquivLast→aU,finSuccEquivLast_last→lz,smul_eq_mul→c9
set_option autoImplicit true
section
namespace Ex
noncomputable section
section Evaluation
open K1 aR PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative
open scoped BigOperators
private theorem bcz {n:ℕ} (P:af n) (m:Fin n →₀ ℕ) (i:ℕ) :
   ((mD ao (Fin n)).symm P).coeff (m.optionElim i) =
     (P.coeff m).coeff i:= by
 rw [← MvPolynomial.optionEquivRight_coeff_coeff,AlgEquiv.apply_symm_apply]
private theorem cBu (Q:DifferentialPolynomial ao 3) (S:ao[X]) :
   cK (mD ao (Fin 4) Q) S =
     differentialSpecialization Q S:= by
 let x :Option (Fin 4)→ao[X] := fun
   | none=>Polynomial.X
   | some i=>jet S i
 have h:=MvPolynomial.aeval_map_optionEquivRight (R:=ao) x Q
 have hx :x none=Polynomial.X:=rfl
 have hj: (fun j=>x (some j))=jet S:=rfl
 rw [hx,hj,Polynomial.aeval_X_left] at h
 rw [show (AlgHom.id ao ao[X]).toRingHom=RingHom.id (ao[X]) from rfl,
   MvPolynomial.map_id] at h
 rw [MvPolynomial.aeval_eq_eval] at h
 unfold cK differentialSpecialization
 refine h.trans (AlgHom.congr_fun ?_ Q)
 apply MvPolynomial.algHom_ext
 intro v
 rw [differentialSpecializationHom,lJ,lJ]
 cases v <;> rfl
end Evaluation
section LeadingCoefficient
open aR MvPolynomial
open scoped Polynomial
def YN :af 4 ≃ₐ[ao[X]] Polynomial (af 3) :=
 (renameEquiv ao[X] aU).trans (optionEquivLeft ao[X] (Fin 3))
def X7 (P:af 4) :af 3:=(YN P).leadingCoeff
theorem aQU (P:af 4) : (YN P).natDegree=(shape P).t:= by
 change (optionEquivLeft _ _ (rename aU P)).natDegree=P.degreeOf 3
 rw [natDegree_optionEquivLeft]
 exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 3)
theorem bUb {P:af 4} (hP:P≠0) :X7 P≠0 :=
 Polynomial.leadingCoeff_ne_zero.mpr (fun h=>hP (YN.injective (h.trans (map_zero _).symm)))
theorem bA3 (P Q:af 4) :X7 (P*Q)=X7 P*X7 Q:= by
 rw [ X7,map_mul,Polynomial.leadingCoeff_mul]
 rfl
private def partialEval (S:ao[X]) :af 4 →+* ao[X][X] :=
 eval₂Hom Polynomial.C fun i:Fin 4 =>
  if i=3 then Polynomial.X else Polynomial.C (jet S i)
private theorem bKk (P:af 4) (S:ao[X]) :
    partialEval S P=(YN P).map (eval (jet S)) := by
  have hlast :aU (3:Fin 4)=none :=lz
  have h:partialEval S=(Polynomial.mapRingHom (eval (jet S))).comp YN.toRingHom:= by
    apply lV
    · intro p
      simp [partialEval,YN,optionEquivLeft_C]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [partialEval,YN,hlast,optionEquivLeft_X_none,show Fin.last 3=(3:Fin 4) by rfl]
      · have hj:j.castSucc≠(3:Fin 4) :=Fin.castSucc_ne_last j
        simp [partialEval,YN,optionEquivLeft_X_some,hj,jet]
  exact lI h P
theorem a3E (P:af 4) (S:ao[X]) :
  cK (X7 P) S=bhZ P S:= by
 change eval (jet S) (YN P).leadingCoeff =
  (partialEval S P).coeff (shape P).t
 rw [bKk,Polynomial.coeff_map,← aQU,Polynomial.leadingCoeff]
theorem bUq (P:af 4) (S:ao[X]) (ht: (shape P).t=0) :
    cK P S=cK (X7 P) S:= by
  have he :cK P S=(partialEval S P).eval (jet S (3:Fin 4)) := by
    have h:eval (jet S) =
        (Polynomial.evalRingHom (jet S (3:Fin 4))).comp (partialEval S) := by
      apply lV
      · intro p
        simp [partialEval]
      · intro i
        by_cases hi:i=3
        · subst i
          simp [partialEval]
        · simp [partialEval,hi]
    exact lI h P
  have hd: (partialEval S P).natDegree≤0:= by
    rw [bKk]
    exact Polynomial.natDegree_map_le.trans (by rw [aQU,ht])
  rw [he,a3E]
  change (partialEval S P).eval _=(partialEval S P).coeff (shape P).t
  rw [ht,Polynomial.eq_C_of_natDegree_le_zero hd,Polynomial.eval_C,Polynomial.coeff_C_zero]
theorem C6 {n:ℕ} (P:af n) :
  qE P=P.weightedTotalDegree (fun i=>i.val) := by
 simp only [qE,weightedTotalDegree,cy ,c9,Nat.mul_comm]
private theorem cBi (P:af 4) (m:Fin 3 →₀ ℕ) (hm:m∈(X7 P).support) :
   ∃ u∈P.support,P.coeff u=(X7 P).coeff m ∧
     ∀ w:Fin 4→ℕ,m.weight (fun i=>w i.castSucc)≤u.weight w:= by
 classical
 let k :=(YN P).natDegree
 let c:=rename aU P
 have hc:c.coeff (m.optionElim k)=(X7 P).coeff m:= by
   exact (optionEquivLeft_coeff_coeff _ _ _ _).symm
 have hs :m.optionElim k∈c.support :=
   mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
 rw [show c=rename aU P from rfl,
   support_rename_of_injective finSuccEquivLast.injective] at hs
 obtain ⟨u,hu,he⟩:=Finset.mem_image.mp hs
 refine ⟨u,hu,?_,fun w => ?_⟩
 · rw [← hc,← he,coeff_rename_mapDomain _ finSuccEquivLast.injective]
 · let w' : Option (Fin 3)→ℕ:= fun v=>v.elim (w 3) (fun i=>w i.castSucc)
   have hlast :aU (3:Fin 4)=none :=lz
   have hw : ∀ i:Fin 4,w' (aU i)=w i:= by
     intro i
     refine Fin.lastCases ?_ (fun j => ?_) i
     · simp [w',hlast,show Fin.last 3=(3:Fin 4) by rfl]
     · simp [w']
   have hweight: (m.optionElim k).weight w' = u.weight w:= by
     rw [← he]
     simp only [cy ,c9]
     rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
     simp only [hw]
   rw [Finsupp.weight_optionElim] at hweight
   exact hweight ▸ Nat.le_add_left _ _
end LeadingCoefficient
section FactorCover
open K1 aR MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
private theorem aDq (P:af 4) :
    3*(shape P).t≤(shape P).j∧(shape P).j≤3*(shape P).b:= by
  classical
  change 3*P.degreeOf 3≤qE P∧qE P≤3*P.totalDegree
  rw [C6]
  constructor
  · rw [MvPolynomial.degreeOf_eq_sup]
    have h:P.support.sup (fun m=>m (3:Fin 4)) ≤
        P.weightedTotalDegree (fun i=>i.val)/3:= by
      apply Finset.sup_le
      intro m hm
      have hterm :=Finsupp.apply_smul_le_weight (fun i:Fin 4=>i.val) m (3:Fin 4)
      have hthree : (3:Fin 4).val=3:=rfl
      have hle :=le_weightedTotalDegree (fun i:Fin 4=>i.val) hm
      have hmul :3*m (3:Fin 4)≤P.weightedTotalDegree (fun i=>i.val) :=
        (by simpa only [smul_eq_mul,Nat.mul_comm,hthree] using hterm :
          3*m (3:Fin 4)≤ m.weight (fun i=>i.val)).trans hle
      omega
    omega
  · rw [weightedTotalDegree,Finset.sup_le_iff]
    intro m hm
    have hle :=Finsupp.weight_le_weight
      (w:= fun i:Fin 4=>i.val) (w' := fun _=>3) (fun i=>Nat.le_of_lt_succ i.isLt) m
    have he :m.weight (fun _=>3)=3*m.degree := by
      simp only [cy ,Finsupp.degree_apply,Finsupp.sum,c9,
        Finset.mul_sum,Nat.mul_comm]
    have hdeg:m.degree≤P.totalDegree :=le_totalDegree hm
    exact hle.trans (he.trans_le (Nat.mul_le_mul_left 3 hdeg))
end FactorCover
section Composition
open aR
end Composition
end
end Ex
end
section
namespace fP
open aR Ex MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def lP:Fin 4→ℕ:=Fin.val
def m9:Fin 4→ℕ := ![3,0,1, 2]
def Ew (d:ℕ) (lo hi:ℤ) (f :ℕ) (m:Fin 4 →₀ ℕ) :Prop :=
 m.degree=d∧lo≤(m.weight lP:ℤ)∧(m.weight lP:ℤ)≤hi∧m 3≤f
def aOb (lo hi:ℤ) :ℕ:=(hi+1-lo).toNat
def qI (n:ℕ) (f :ℕ→ℕ) :ℕ :=
 Nat.rec 0 (fun i a=>a+f i) n
theorem aAs (n:ℕ) (f :ℕ→ℕ) :
   qI n f = ∑ i∈Finset.range n,f i:= by
 induction n with
 | zero=>simp [qI]
 | succ n ih =>
   rw [Finset.sum_range_succ,← ih]
   rfl
def anJ (d:ℕ) (lo hi:ℤ) (top:ℕ) :ℕ :=
  qI (min d top+1) fun f =>
    qI (min (d - f) ((hi-3*f)/2).toNat+1) fun c =>
     aOb (max 0 (lo - 2*c-3*f))
      (min ((d:ℤ) - f - c) (hi - 2*c-3*f))
noncomputable section
abbrev Form:=MvPolynomial (Fin 4) ao
def GS (d:ℕ) (lo hi:ℤ) (f :ℕ) :Submodule ao Form :=
 restrictSupport ao {m | Ew d lo hi f m}
def L4 :Form:=MvPolynomial.X 0+MvPolynomial.X 1-MvPolynomial.X 2+MvPolynomial.X 3
def Jx :Form →ₐ[ao] Form :=
 bind₁ fun j=>if j=0 then L4 else MvPolynomial.X j
def avQ (e :Fin 4 →₀ ℕ) :ao :=
 (-1 :ao)^(e 2) / ∏ j:Fin 4,((e j).factorial:ao)
def avP (m:Fin 4 →₀ ℕ) :ao :=
 (-1 :ao)^(m 2) * ∏ j:Fin 4,((m j).factorial:ao)
end
end fP
end
