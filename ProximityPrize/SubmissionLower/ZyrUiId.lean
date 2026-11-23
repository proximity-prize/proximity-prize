import ProximityPrize.SubmissionLower.Z6Xnfpd
import ProximityPrize.SubmissionLower.ZDyoNob
set_option Elab.async false
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qd4jtSc
open qMHqmcc (GG receipt appendGrades)
private theorem vQm0 :GG b3 0 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm1 :GG b3 1 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm2 :GG b3 2 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm3 :GG b3 3 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm4 :GG b3 4 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm5 :GG b3 5 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm6 :GG b3 6 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm7 :GG b3 7 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem r1 :GG b3 0 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQm0 vQm1) vQm2) vQm3) vQm4) vQm5) vQm6) vQm7
private theorem vQm8 :GG b3 8 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm9 :GG b3 9 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm10 :GG b3 10 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm11 :GG b3 11 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm12 :GG b3 12 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm13 :GG b3 13 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm14 :GG b3 14 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem vQm15 :GG b3 15 1:= by
  repeat' apply And.intro
  all_goals first | exact True.intro | apply receipt 2536 rfl <;> with_unfolding_all rfl
private theorem r2 :GG b3 8 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQm8 vQm9) vQm10) vQm11) vQm12) vQm13) vQm14) vQm15
theorem p3_0:GG b3 0 16:=appendGrades r1 r2
end qd4jtSc
end
section
open _root_ renaming Fin.cases→ oj,Finset→lz,Ideal→cy,P5_7.midAgreement→ oy,P5_7_1.OriginCover→nX,P5_7_1.Picks→lJ,gT.Ambient→aU
section
set_option autoImplicit true
namespace qehP9ee
noncomputable section
open P5 (p)

open P5_7_1 (Ls afa movingOrder stages cutoff terminal degree bgK)
open cu (vP Jet Shape)
open gT (iJ)
open pI (NO dual aaS)

open scoped Classical BigOperators
abbrev Trial:=Fin 12
abbrev bAL:=Fin 13
abbrev stage (i:afa) :Ls :=stages.get i
def movingStage (i:Fin movingOrder.length) :afa :=
 ⟨movingOrder.get i,by fin_cases i <;> decide⟩
inductive TrialKind
 | free (i:afa)
 | moving (i:afa)
 | terminal
def trialKind (t:Trial) :TrialKind :=
  ([1,2,3,4,5,6,7].map (fun i:Fin 8=>TrialKind.free i) ++
    List.ofFn (fun i=>TrialKind.moving (movingStage i)) ++ [TrialKind.terminal]).get t
def a3D (s :Ls) :Shape :=
 let j:=max s.free.J s.moving.J
 ⟨0,max (s.free.B-s.free.J) (s.moving.B-s.moving.J)+j,j,max s.free.U s.moving.U⟩
def inBank (rows :vP) (s :Shape) (I:cy aU) :Prop :=
 ∀ G∈rows s (cutoff s),iJ G∈I
def passes {h rows} (pick :lJ h rows) (t:Trial) (I:cy aU) :Prop :=
  match trialKind t with
  | .free i=>inBank rows (stage i).free I
  | .moving i=>inBank rows (stage i).free I∧inBank rows (stage i).moving I ∧
    aFX.aTw (pick.main i).free (pick.main i).moving I
  | .terminal=>inBank rows terminal I
structure bQX {h rows} (pick :lJ h rows) where
 free : ∀ i,NO (pick.main i).free (stage i).free
 moving : ∀ i,NO (pick.main i).moving (stage i).moving
def clean {h rows} {pick :lJ h rows} (R:bQX pick) (I:cy aU) :Prop :=
  ∀ j:Fin movingOrder.length,
    ¬ aaS (R.free (movingStage j)).equation I ∧
    ¬ aaS (R.moving (movingStage j)).equation I
def QV {x rows} {pick :lJ x.h rows} (R:bQX pick)
    {anchorRow :Jet} (O:nX x anchorRow) (f :Jet) (s :bAL) :
    lz (cy aU) :=
  (O.parents f).filter fun I=>clean R I∧(0<s.val→dual I) ∧
    ∀ t:Trial,t.val+1<s.val→passes pick t I
def stopped {x rows} {pick :lJ x.h rows} (R:bQX pick)
    {anchorRow :Jet} (O:nX x anchorRow) (f :Jet) :bAL→lz (cy aU) :=
  oj ((QV R O f 0).filter fun I => ¬ dual I)
    (fun t=>(QV R O f t.succ).filter fun I => ¬ passes pick t I)
def final {x rows} {pick :lJ x.h rows} (R:bQX pick)
    {anchorRow :Jet} (O:nX x anchorRow) (f :Jet) :lz (cy aU) :=
  (O.parents f).filter fun I=>clean R I∧dual I ∧ ∀ t,passes pick t I
def asShape (v :Fin 3→ℕ) :Shape :=⟨0,v 0,v 1,v 2⟩
def mixedCols (s :Shape) :Fin 4→Fin 3→ℕ :=
 ![![s.J,s.B-s.J,0],![0,s.U,s.J],![s.U,0,s.B],![0,0,s.U]]
def kK (a :Fin 3→ℕ) (s :Shape) (k :Fin 4) :ℚ :=
 ∑ j,((a j:ℕ) :ℚ)*mixedCols s k j
def ordinaryBox (e u:ℕ) :Fin 4→ℕ := ![e,u,2*e*u,u*u]
def aea (s :Shape) (ν e u:ℕ) :Shape :=
 ⟨0,s.B-ν*e,min s.J (s.B-ν*e),s.U-ν*u⟩
def MovingBox (s :Ls) (v :Fin 4→ℕ) :Prop :=
  let m:=s.dI+1
  let residual (ν e u:ℕ) := ∀ k,
    ((v k :ℕ) :ℚ)≤kK (bgK (aea s.free ν e u))
      (aea s.moving ν e u) k/((m-ν:ℕ) :ℚ)^2
  residual 0 0 0 ∨ ∃ ν e u:ℕ,0<ν∧ν≤ m∧0<e ∧
    ν*e≤ min s.free.B s.moving.B∧ν*u≤ min s.free.U s.moving.U ∧
    (∀ k,v k≤ordinaryBox e u k)∧(ν< m→ residual ν e u)
abbrev graphRate (g:ℕ) :ℚ:=((p+1 :ℕ) :ℚ)/g
abbrev gap:ℕ:=oy-degree
end
end qehP9ee
end
end
