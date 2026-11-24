import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.ZZZuA2c
import ProximityPrize.SubmissionLower.ZZBDV9b
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
section
set_option autoImplicit true
namespace P4_6_5_1
noncomputable section
open aR (af)

open we (cH)
open bJ (gZ)

open Polynomial
open scoped BigOperators
export we (GD Bk aap afs JC)


structure acU (f :af 3) (Q:Bk) :Prop where
  solution :we.acU f Q
  short : ∀ a∈MvPolynomial.zeroLocus cH Q,
    (JC a).natDegree≤gZ
end
end P4_6_5_1
end
section
section
set_option autoImplicit true
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
private abbrev kA:fO:=⟨6,by decide⟩
set_option quotPrecheck false in
local notation "kU" => receipt 2539 rfl (by decide +kernel) (by decide +kernel)
private theorem r84 :GG kA 84 3:=⟨kU,kU,kU,True.intro⟩
private theorem r87:GG kA 87 3:=⟨kU,kU,kU,True.intro⟩
private theorem r90:GG kA 90 3:=⟨kU,kU,kU,True.intro⟩
theorem h:GG kA 84 9 :=
  appendGrades (appendGrades r84 r87) r90
end qyV6B3d
end
section
set_option autoImplicit true
namespace qwtjEYd
open P5_7_2 (fO)
open qMHqmcc (GG appendGrades receipt test)
private abbrev b:fO:=⟨12,by decide⟩
set_option quotPrecheck false in
local notation "az" n:arg=>receipt (b:=b) (x :=test b n) 2581 rfl
  (by decide +kernel) (by decide +kernel)
private theorem Ku:GG b 39 4 :=⟨az 42,az 41,az 40,az 39,True.intro⟩
private theorem Vr :GG b 43 4 :=⟨az 46,az 45,az 44,az 43,True.intro⟩
private theorem Cx :GG b 47 4 :=⟨az 50,az 49,az 48,az 47,True.intro⟩
theorem earlyD:GG (⟨12,by decide⟩:fO) 39 12 :=
  appendGrades (appendGrades Ku Vr) Cx
end qwtjEYd
end
end
section
set_option autoImplicit true
namespace P1_6_1_3
noncomputable section
open ac5
open fP (lP m9 Ew)
abbrev Source (q:ℕ) := {m:Fin 4 →₀ ℕ // Ew q 0 49 14 m}
abbrev Target (q:ℕ) := {e :Fin 4 →₀ ℕ // e.degree=q}
instance sourceFinite (q:ℕ) :Finite (Source q) :=
  ((Finsupp.finite_of_degree_le _).subset fun _ (h:Ew _ _ _ _ _) =>
    h.1.le).to_subtype
instance targetFinite (q:ℕ) :Finite (Target q) :=
  ((Finsupp.finite_of_degree_le _).subset fun _ (h:_ = _)=>h.le).to_subtype
noncomputable instance (q:ℕ) :Fintype (Source q) :=Fintype.ofFinite _
noncomputable instance (q:ℕ) :Fintype (Target q) :=Fintype.ofFinite _
def Ig (r :Fin 139) {q:ℕ} (m:Source q) :Prop :=
  49≤ r.val+m.val.weight lP
instance (r :Fin 139) {q:ℕ} (m:Source q) :Decidable (Ig r m) :=
  inferInstanceAs (Decidable (49≤ r.val+m.val.weight lP))
def cutoff (q:ℕ) (r :Fin 139) :ℕ:=139 - q - r.val
def DV (r :Fin 139) {q:ℕ} (e :Target q) :Prop :=
  e.val.weight m9<cutoff q r
instance (r :Fin 139) {q:ℕ} (e :Target q) :Decidable (DV r e) :=
  inferInstanceAs (Decidable (e.val.weight m9<cutoff q r))
def redundant (r :Fin 139) {q:ℕ} (e :Target q) :Prop :=
  15≤e.val 3∧e.val.weight m9+15<cutoff q r
instance (r :Fin 139) {q:ℕ} (e :Target q) :Decidable (redundant r e) := by
  unfold redundant
  infer_instance
def Bp (r :Fin 139) {q:ℕ} (e :Target q) :Prop :=
  DV r e ∧ ¬ redundant r e
instance (r :Fin 139) {q:ℕ} (e :Target q) :Decidable (Bp r e) := by
  unfold Bp
  infer_instance
def adjacentAdmissible {q:ℕ} (e :Target q) :Prop :=
  e.val 0≤14∧e.val.weight m9<49
instance {q:ℕ} (e :Target q) :Decidable (adjacentAdmissible e) := by
  unfold adjacentAdmissible
  infer_instance
def adjacentProduct (e :Fin 4 →₀ ℕ) :MvPolynomial (Fin 4) (ZMod P1.p) :=
  (MvPolynomial.X 0+MvPolynomial.X 1)^e 1 *
    (MvPolynomial.X 2 - MvPolynomial.X 1)^e 2 *
    (MvPolynomial.X 3-MvPolynomial.X 2)^e 3*(-MvPolynomial.X 3)^e 0
end
end P1_6_1_3
end
