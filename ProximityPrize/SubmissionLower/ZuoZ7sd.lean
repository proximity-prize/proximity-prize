import ProximityPrize.SubmissionLower.ZPMTD6c
set_option Elab.async false
set_option maxHeartbeats 800000
namespace qkLbbMe
noncomputable section
open Polynomial Finset PolynomialDifferential
open P5 (p K twist)


open cu (L j9)
open scoped Classical
local instance :CharP L p :=
 charP_of_injective_ringHom (algebraMap K L).injective p
local notation "D" => P5_7_1.degree
private abbrev Eqn:=DifferentialPolynomial L 1
private def dX:Finset L :=
 letI:=Subfield.fintypeBot L p
 (univ :Finset (⊥ : Subfield L)).map ⟨Subtype.val,Subtype.val_injective⟩
private theorem card_grid :dX.card=p:= by
 let:=Subfield.fintypeBot L p
 rw [dX,card_map,card_univ,← Nat.card_eq_fintype_card,Subfield.card_bot L p]
private theorem mem_grid (a :L) :a∈dX↔a^p=a := by
 let:=Subfield.fintypeBot L p
 rw [← Subfield.mem_bot_iff_pow_eq_self L p]
 change (a∈dX)↔a∈(⊥ : Subfield L)
 constructor
 · intro ha
   obtain ⟨b,_,rfl⟩:=mem_map.mp ha
   exact b.property
 · intro ha
   exact mem_map.mpr ⟨⟨a,ha⟩,mem_univ _,rfl⟩
private theorem jet_mem_grid (S:K[X]) (hs :S.map twist=S) {a :L}
   (ha :a∈dX) (i:Fin 2) :polynomialJet (d:=1) a (j9 S) i∈dX:= by
 let f :=frobenius L p
 have hm: (j9 S).map f=j9 S:= by
   have hcomp:f.comp (algebraMap K L)=(algebraMap K L).comp twist:= by
     ext b
     change (algebraMap K L b)^p=algebraMap K L (b^p)
     exact (map_pow (algebraMap K L) b p).symm
   unfold j9
   rw [Polynomial.map_map,hcomp,← Polynomial.map_map,hs]
 have ha' : f a=a :=(mem_grid a).mp ha
 rw [mem_grid]
 change f ((hasseDeriv i.val (j9 S)).eval a)= _
 rw [← Polynomial.eval_map_apply,← hasseDeriv_map,hm,ha']
 rfl
private theorem cast_ne_zero {n:ℕ} (hn:0<n) (hp:n<p) : (n:L)≠0:= by
 intro h
 exact (not_le_of_gt hp) (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff L p n).mp h))
private inductive Good:Eqn→ L[X]→L→Prop where
 | regular {Q S a i} (active :highestActiveJet Q=some i)
    (solves :differentialSpecialization Q S=0)
    (sep:jetEvaluation (separant Q i) a (polynomialJet a S)≠0) :Good Q S a
 | singular {Q S a i} (active :highestActiveJet Q=some i)
    (solves :differentialSpecialization Q S=0)
    (next:Good (separant Q i) S a) :Good Q S a
private theorem Good.eval_zero {Q S a} (h:Good Q S a) :
  jetEvaluation Q a (polynomialJet a S)=0:= by
 have hz :differentialSpecialization Q S=0:= by cases h <;> assumption
 rw [← eval_differentialSpecialization,hz,Polynomial.eval_zero]
private theorem Good.initial_ne {Q S a} (h:Good Q S a) :initialJetEquation a Q≠0:= by
 induction h with
 | regular _ _ hreg =>
    intro hz
    apply hreg
    rw [← aeval_initialJetEquation,← pderiv_initialJetEquation,hz,map_zero,map_zero]
 | singular _ _ _ ih =>
    intro hz
    apply ih
    rw [← pderiv_initialJetEquation,hz,map_zero]
end
end qkLbbMe
