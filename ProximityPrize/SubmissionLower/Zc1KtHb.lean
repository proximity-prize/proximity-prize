import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZyrUiId
set_option Elab.async false
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q54LkTb
noncomputable section
open Finset
open P5_7_1 (Input OriginCover wD)
open qehP9ee
open cu (Jet Shape)



open akZ (aHP)
open scoped Classical




variable {x :Input} {anchorRow :Jet} (O:OriginCover x anchorRow)
theorem tD {a b:Fin 3→ℕ} (h : ∀ j,a j≤b j) (s :Shape) (k :Fin 4) :
  kK a s k≤kK b s k :=
 sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h j)) (Nat.cast_nonneg _)
private theorem tariff_cast (s :Shape) (k :Fin 4) (f :Jet) :
  (aHP s k f :ℚ)=kK (wD f) s k := by
 simp only [kK,aHP,TD.arC,mixedCols,wD,akZ.yE,
  Nat.cast_sum,Nat.cast_mul,mul_comm]
private theorem cast_fold (j:Fin 3) (L:List (Fin 3→ℕ)) (a :ℕ) :
   (↑(L.foldl (fun n w=>max n (w j)) a) :ℚ) =
     (L.map (fun w l=>(w l:ℚ))).foldl (fun n w=>max n (w j)) (a :ℚ) := by
 induction L generalizing a with
 | nil=>rfl
 | cons w L ih =>
   simp only [List.foldl_cons,List.map_cons,ih,Nat.cast_max]
end
end q54LkTb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q54LkTb
noncomputable section
open Finset

open P5_7_1 (Input Poles Picks Ls OriginCover)
open qehP9ee





open TD (GM bf7)
open scoped Classical


theorem le_folds (v :ℚ) (L:List α) (w:α→ℚ) (a :ℚ)
   (ha :v≤a) (hw : ∀ b∈L,v≤w b) :
   v≤L.foldl (fun c b=>min c (w b)) a := by
 induction L generalizing a with
 | nil=>exact ha
 | cons b L ih =>
   exact ih _ (le_min ha (hw b (List.mem_cons_self ..)))
     (fun c hc=>hw c (List.mem_cons_of_mem _ hc))
private theorem mass_fold (A:GM) (L:List Ls) (k :Fin 4) :
   L.foldl (fun a v=>TD.bCb a (bf7 v.free v.moving v.dI true)) A k =
   L.foldl (fun a v=>min a (bf7 v.free v.moving v.dI true k)) (A k) := by
 induction L generalizing A with
 | nil=>rfl
 | cons s L ih =>
   exact ih (TD.bCb A (bf7 s.free s.moving s.dI true))
variable {x :Input} (P:Poles x) (pick :Picks x.h P.rows)
 (R:bQX pick) (O:OriginCover x (pick.main ⟨0,by decide⟩).free)
end
end q54LkTb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q54LkTb
noncomputable section
open Finset Polynomial
open P5 (p)
open P5_7_1 (Input Poles Picks Ls OriginCover bgK wD)
open qehP9ee
open cu (Jet Shape)

open gT (Ambient iJ)
open pI (xN dual O9 aaS NO oU pN)
open XY (ag6)
open TD (J2)
open akZ (caQ)
open scoped Classical


def c1 :Prop :=
  ∀ (P F G:Jet) (s t:Shape) (S:Finset (Ideal Ambient)) (n:ℕ),
    0<n→P≠0→ag6 F G→s.J≤ s.B→t.J≤t.B →
    oU P s→ oU F t→ oU G t →
    (∀ I∈S,xN I∧dual I∧iJ F∈I∧iJ G∈I∧O9 I P n) →
    ∀ k,J2 S k≤kK (bgK s) t k/(n:ℚ)
def c2 :Prop :=
  ∀ (s :Ls) (P Q:Jet) (A:NO P s.free) (B:NO Q s.moving)
    (I:Ideal Ambient),
    s.free.B<p→s.free.U<p→P≠0→Q≠0 →
    oU P s.free→ oU Q s.moving→qQ.aeH P Q →
    xN I→dual I→aFX.aTw P Q I →
    ¬ aaS A.equation I → ¬ aaS B.equation I →
    O9 I P (s.dI+1)→O9 I Q (s.dI+1) →
    MovingBox s (pN I)
private theorem b9i (a :Fin 3→ℕ) (s :Shape) (k :Fin 4) :0≤kK a s k :=
 sum_nonneg fun _ _=>mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
variable {x :Input} (P:Poles x) (pick :Picks x.h P.rows) (R:bQX pick)
 (O:OriginCover x (pick.main ⟨0,by decide⟩).free)
private theorem positive_spend {f :Jet} (hf :Irreducible f) :
  1 ≤ ∑ j:Fin 3,wD f j:= by
 rw [Fin.sum_univ_three]
 by_contra! h
 have h0:wD f 0=0:= by omega
 have h2 :wD f 2=0:= by omega
 have h1 :f.natDegree=0:=Nat.eq_zero_of_le_zero ((caQ hf.ne_zero).trans_eq h0)
 have hF:=eq_C_of_natDegree_eq_zero h1
 have hQ: (f.coeff 0).natDegree=0:= by
  have h:=h0
  change atc.jetDegree f=0 at h
  rw [hF,atc.bri] at h
  exact h
 have hr :=eq_C_of_natDegree_eq_zero hQ
 have ht: ((f.coeff 0).coeff 0).totalDegree=0:= by
  have h:=h2
  change atc.gY f=0 at h
  rw [hF,hr,atc.bNz] at h
  exact h
 let a :=((f.coeff 0).coeff 0).coeff 0
 have ha :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp ht
 have hfa :f=C (C (MvPolynomial.C a)) :=hF.trans (congrArg C (hr.trans (congrArg C ha)))
 have hne :a≠0:= fun hz=>hf.ne_zero (by simp [hfa,hz])
 exact hf.not_isUnit (hfa ▸ (((isUnit_iff_ne_zero.mpr hne).map MvPolynomial.C).map C).map C)
end
end q54LkTb
end
