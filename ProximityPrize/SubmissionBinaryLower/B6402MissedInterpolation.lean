import ProximityPrize.SubmissionBinaryLower.B6402CombinedInterpolation
import ProximityPrize.SubmissionBinaryLower.B6402JointMissSystem
import ProximityPrize.SubmissionBinaryLower.B6402LocalInput
import ProximityPrize.SubmissionBinaryLower.B6402MissWitness

/-! A single nonmultiple meets all primary and all missed-site equations.
All output width counts are cardinalities of the actual coefficient spaces. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402MissedInterpolation
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd
open B6402SeedCoordinates B6402QuotientSpace B6402MixedDegree B6402PrimarySystem
open B6402CombinedInterpolation B6402ExceptionalSystem B6402ExceptionalSupport
open B6402ExceptionalInterpolation B6402ExceptionalFibres B6402LocalInput B6402JointMissSystem
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000
variable {K I R B : Type*} [Field K] [CharP K 2] [Fintype I] [Fintype R] [Fintype B]
variable {w W WF s q T H : ℕ}

theorem exists_interpolant (hw : 1<w) (hs : 1≤s) (hH : H≤T)
    (m k : I → ℕ) (x : I → K) (y : I → K[X]) (hy : ∀ i, (y i).natDegree≤q)
    (reg : R → I) (bad : B → I)
    (fc : KerDIdx w WF 1 → K[X]) (F : ContactPoly (Polynomial K))
    (heq : F=∑ e,cC (fc e)*kerDBasisPoly e.1) (height : mixed q F≤H)
    (ordeg : ∀ j, (F.coeff j).natDegree≤5) (hirr : Irreducible F)
    (slope : F.natDegree=1) (dF : contactDeriv F=0) (hirrK : Irreducible (liftCRat F))
    (ord : ∀ i, twOrdGE (localized (x i) (y i) fc) (k i))
    (exactOrd : ∀ i, ∃ a b, a+b=k i ∧ twCoeff (localized (x i) (y i) fc) a b≠0)
    (m2 b J : ℕ) (hJ : W/(w-1)≤J) (a L : B → Fibre K) (d : B → ℕ)
    (hd : ∀ i,d i≤J) (hLne : ∀ i,L i≠0)
    (ha : ∀ i, Bounds (a i) 0 5 0) (hL : ∀ i, Bounds (L i) 0 (d i) H)
    (surplus : (∑ i,Fintype.card (Seeds (m i) s q T))+
      Fintype.card (Targets R B s m2 b J T H)+Fintype.card (Slots w (W-wdeg w F) (s-1) q (T-mixed q F)) <
      Fintype.card (Slots w W s q T)+(∑ i,Fintype.card (Seeds (m i-k i) (s-1) q (T-H)))+
      Fintype.card (Columns B s J T H b d)) :
    ∃ (u : Global K w W s q T) (v : B6402PrimarySystem.Aux K m k s 1 q T H),
      resultant F (source q T u) 1 s≠0 ∧
      (∀ i, twOrdGE (localized (x i) (y i) (decode (width q T) u)-
        localized (x i) (y i) fc*multiplier (decode (localWidth q (T-H)) (v i))) (m i)) ∧
      (∀ r : R, ∀ i<b, ∀ j, 2*m2+3*s≤2*i+j → j≤J+4*s →
        ((B6402RegularSystem.phi F (x (reg r)) (y (reg r)) u).coeff j).coeff (2*i)=0) ∧
      (∀ r : B, remainderConditions (localized (x (bad r)) (y (bad r)) fc) (a r) (L r) b
        (localSource (x (bad r)) (y (bad r)) u)) ∧
      contactDeriv (source q T u)=0 ∧ (source q T u).natDegree≤s ∧ wdeg w (source q T u)≤W ∧ mixed q (source q T u)≤T := by
  classical
  let rx := x ∘ reg
  let ry := y ∘ reg
  let bx := x ∘ bad
  let byv := y ∘ bad
  let bf (r : B) := localized (bx r) (byv r) fc
  let extra := joint (V:=B6402PrimarySystem.Aux K m k s 1 q T H) (w:=w) (W:=W) (s:=s) (q:=q) (T:=T)
    F rx ry bx byv bf a L m2 b J H d
  have hf r j : Bounds ((bf r).coeff (j+1)) (3*(j+1)) 5 H :=
    shifted_factor (by omega) _ _ (hy (bad r)) fc F heq height ordeg j
  have unique : ∀ z,extra ((0,0),z)=0 → z=0 := fun z hz =>
    no_extra_kernel F rx ry bx byv bf a L m2 b J H d z hz hH hd hLne hf ha hL
  have hs' : 0<F.natDegree := by omega
  obtain ⟨u,v,z,hz,hres,primary,bounds⟩ := interpolate (by omega : 0<w) hs hH m k x y hy fc F heq height
    hirr hs' dF hirrK ord exactOrd extra unique (by simpa only [slope] using surplus)
  refine ⟨u,v,slope ▸ hres,primary,?_,?_,bounds⟩
  · intro r i hi j hl hh
    exact B6402RegularSystem.tests_zero F (rx r) (ry r) m2 b J H (by omega) (hy (reg r)) height u
      (all_regular F rx ry bx byv bf a L m2 b J H d ((u,v),z) hz r) i j hi hl hh
  · intro r
    let zr : ACols K s J T H (d r) b := fun j t => z ⟨r,j,t⟩
    have hgr j : Bounds ((localSource (bx r) (byv r) u).coeff j) (s+3*j) J T :=
      (shifted_source hw (bx r) (byv r) (hy (bad r)) u j).mono le_rfl hJ le_rfl
    exact detects (bf r) (a r) (L r) (localSource (bx r) (byv r)) (u,zr)
      hH (hd r) (hf r) (ha r) (hL r) hgr
      (all_exceptional F rx ry bx byv bf a L m2 b J H d ((u,v),z) hz r)

#print axioms exists_interpolant
end ProximityPrize.SubmissionBinaryLower.B6402MissedInterpolation
