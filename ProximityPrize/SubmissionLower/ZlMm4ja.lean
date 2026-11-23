import ProximityPrize.SubmissionLower.AG
set_option Elab.async false
open _root_ renaming CommRing → za6, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, Polynomial → zM1, Polynomial.X → z7y, Polynomial.ringHom_ext' → z3l
section
set_option autoImplicit true
namespace K1_14_3_4_5
noncomputable section
open cu qQ Polynomial
def Lz {F R:Type*} [za6 F] [za6 R] (a :F →+* R)
    (t:Fin 2→R) (y v :R) :zM1 (zM1 (z3y (Fin 2) F)) →+* R :=
  eval₂RingHom (eval₂RingHom (MvPolynomial.eval₂Hom a t) y) v
abbrev MatrixQuot {F:Type*} [Field F] {n:ℕ}
    (M:Matrix (Fin n) (Fin n) (zM1 F)) :=
  (Fin n→zM1 F) ⧸ LinearMap.range M.toLin'
end
end K1_14_3_4_5
end
section
set_option autoImplicit true
namespace K1_14_3_4_5
noncomputable section
open cu qQ bjG Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
local instance sectionRing:za6 aSE :=Polynomial.commRing
@[simp] theorem evalRow_const {F R:Type*} [za6 F] [za6 R]
    (a :F →+* R) (t:Fin 2→R) (y v :R) (c:F) :
    Lz a t y v (C (C (znf c)))=a c:= by
  simp [Lz]
@[simp] theorem evalRow_seed {F R:Type*} [za6 F] [za6 R]
    (a :F →+* R) (t:Fin 2→R) (y v :R) (i:Fin 2) :
    Lz a t y v (C (C (z9v i)))=t i:= by
  simp [Lz]
@[simp] theorem evalRow_y {F R:Type*} [za6 F] [za6 R]
    (a :F →+* R) (t:Fin 2→R) (y v :R) :
    Lz a t y v (C (R:=zM1 (z3y (Fin 2) F)) (z7y (R:=z3y (Fin 2) F)))=y := by
  simp [Lz]
@[simp] theorem evalRow_v {F R:Type*} [za6 F] [za6 R]
    (a :F →+* R) (t:Fin 2→R) (y v :R) :
    Lz a t y v (z7y (R:=zM1 (z3y (Fin 2) F)))=v := by
  simp [Lz]
theorem rowHom_ext {F R:Type*} [za6 F] [za6 R]
    {f g:zM1 (zM1 (z3y (Fin 2) F)) →+* R}
    (hc : ∀ c:F,f (C (C (znf c)))=g (C (C (znf c))))
    (ht : ∀ i,f (C (C (z9v i)))=g (C (C (z9v i))))
    (hy :f (C (R:=zM1 (z3y (Fin 2) F)) (z7y (R:=z3y (Fin 2) F))) =
      g (C (R:=zM1 (z3y (Fin 2) F)) (z7y (R:=z3y (Fin 2) F))))
    (hv :f (z7y (R:=zM1 (z3y (Fin 2) F))) =
      g (z7y (R:=zM1 (z3y (Fin 2) F)))) :f=g:= by
  apply z3l
  · apply z3l
    · apply MvPolynomial.ringHom_ext <;> assumption
    · exact hy
  · exact hv
end
end K1_14_3_4_5
end
