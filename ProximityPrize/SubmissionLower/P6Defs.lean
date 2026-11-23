import ProximityPrize.SubmissionLower.AA
set_option Elab.async false
set_option maxRecDepth 12000
section
open _root_ renaming Finset.range→aU
set_option autoImplicit true
section
namespace bzq
open xE GI Finset
open scoped BigOperators
private def jO (t:ℕ) :ℕ:=(t+1649)/4+1
private def aJN (t u:ℕ) :ℤ :=
 let d:=1650 - jO t
 gd 1650 (u:ℤ) - gd (d:ℤ) ((u:ℤ)-(3*jO t:ℕ)) +
  gd (d:ℤ) ((u:ℤ) - t)
private def bna (t k :ℕ) :ℤ :=
 let d:=1650 - jO t
 aTX 1650 k+24*((1650+t - k :ℕ) :ℤ)*gd 1650 1650 -
  aTX 1650 1650+aTX d (k - t)-aTX d (k-3*jO t)
private def bdW (t:ℕ) :ℕ→ℕ→ℕ→ℕ
 | 0,lo,_=>lo
 | fuel+1,lo,hi =>
   let mid :=(lo+hi)/2
   if aJN t mid<gd 1650 1650 then bdW t fuel (mid+1) hi
   else bdW t fuel lo mid
private def cutoff (t:ℕ) :ℕ:=min 1650 (bdW t 11 0 1650)
private def nw (t:ℕ) :ℤ:=bna t (cutoff t)
private def m8 (f :ℕ→ℤ) :ℕ→ℤ
 | 0=>0
 | n+1=>m8 f n+f n
private theorem aNC (f :ℕ→ℤ) (n:ℕ) :m8 f n = ∑ j∈aU n,f j:= by
 induction n with
 | zero=>simp [m8]
 | succ n ih=>rw [m8,sum_range_succ,ih]
private theorem es1 (f :ℕ→ℤ) (a b:ℕ) :
  m8 f (a+b)=m8 f a+m8 (fun j=>f (a+j)) b:= by
 simpa only [aNC] using sum_range_add f a b


private def block (s n:Nat) :Int :=
 m8 (fun j=>nw (1350-(s+j))) n
private theorem add {s a b:Nat} {x y :Int}
  (ha :block s a=x) (hb:block (s+a) b=y) :block s (a+b)=x+y := by
 unfold block at *
 rw [es1,ha]
 simpa only [Nat.add_assoc] using congrArg (fun z :ℤ=>x+z) hb
end bzq
end
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I e9 node p blockLength k kB nC aB8 ayo
 sZ aiE vn seed jH twist uO Ox Xb
 JO J9 Z4 ake)
abbrev a08:=P1.a08
abbrev target :a08:=⟨179876,0x1415c51a,0x40000000,2325,0x3b633efb605881a,0x22a0a042c6b0⟩
abbrev dw:=target.dw
abbrev t:ℕ:=blockLength - dw
abbrev L:ℕ:=dw - k
abbrev DY:ℕ:=t+1 - L - 2
abbrev budget:ℕ:=0x3d0ed83eb28710f
abbrev a9J:=P1.a9J
abbrev B5:=a9J dw
def iy (u:e9) := QO node (u 0) (u 1) L t
def So (u:e9) :=AI p node (u 0) (u 1) L t
def R5 (u:e9) :=Bx.ay6 (So u)
structure qo (u:e9) where
 a :ℕ
 b:ℕ
 c:ℕ
 ab:a≤b
 active :b≤t
 inactive :t<c
 top:c≤k
 degreeSum:a+b+c=2*k+2
 nullitySum:R5 u+a+b=2*(t+1)
 level :kL.aKl
   (fun s j=>algebraMap K[X] kB (Principal.P8 p node (u 0) (u 1) s j))
   k a b c
def qo.height {u:e9} (T:qo u) :=(k+1) - T.c
abbrev FJ:=P1.FJ
abbrev FJ.iF := @P1.FJ.iF
abbrev FJ.label := @P1.FJ.label
abbrev FJ.wK := @P1.FJ.wK
abbrev FJ.decoder := @P1.FJ.decoder
abbrev jG:=FJ DY
abbrev jG.iF {u deleted} (M:jG u deleted) :=FJ.iF M
abbrev jG.label {u deleted} (M:jG u deleted) :=FJ.label M
abbrev jG.wK {u deleted} (M:jG u deleted) :=FJ.wK M
abbrev jG.decoder {u deleted} (M:jG u deleted) {γ:K} (B:B5 u γ) :=
 FJ.decoder M B
inductive gJ where
 | transport
 | middle
 | far
def gJ.lo:gJ→ℕ
 | .transport=>2326
 | .middle=>2533
 | .far=>3600
def gJ.hi:gJ→ℕ
 | .transport=>2532
 | .middle=>3599
 | .far=>33463
def gJ.regular :gJ→ℕ
 | .transport=>0x33f9ed514e4b01f
 | .middle=>0x39efe5516db7297
 | .far=>0x3cd53f7b0bf176
end
end P5
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I e9 node p blockLength k kB nC aB8 ayo
  sZ aiE vn seed jH twist uO Ox Xb
  JO J9 Z4 ake)
abbrev a08:=P1.a08
abbrev target :a08:=⟨179827,0x1418d040,0x40000000,2354,0x3ca348fd72293ee,0x2571805851eb⟩
abbrev dw:=target.dw
abbrev radiusNumerator :=target.numerator
abbrev radiusDenominator :=target.denominator
abbrev ajO:ℤ:=target.aou
abbrev NG:=target.mcaBound
abbrev LM:=target.listBound
abbrev t:ℕ:=blockLength - dw
abbrev L:ℕ:=dw - k
abbrev DY:ℕ:=t+1 - L - 2
abbrev aEu:ℕ:=0x41096701418c
abbrev aCe :ℕ:=0x41096705894d
abbrev structuralCap:ℕ:=0x26f1c2be4b348bc
abbrev budget:ℕ:=0x3d0ed83eb28710f
def Xt:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
def radius :ℝ:=Xt
def Tt (u:e9) (Γ:Finset K) :Prop :=
  ∀ γ∈Γ,IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius
abbrev a9J:=P1.a9J
abbrev B5:=a9J dw
def iy (u:e9) := QO node (u 0) (u 1) L t
def So (u:e9) :=AI p node (u 0) (u 1) L t
def aDf (u:e9) :=Bx.adJ (iy u)
def Vv (u:e9) :=Bx.adJ (So u)
def R5 (u:e9) :=Bx.ay6 (So u)
def Normal (u:e9) (γ:K) :Prop :=
  ((So u).map (evalRingHom γ)).rank=Vv u
def aOW (u:e9) (Γ:Finset K) :Finset K:= by
  classical exact Γ.filter (Normal u)
def bAR (u:e9) (Γ:Finset K) :Finset K:= by
  classical exact Γ.filter (fun γ => ¬ Normal u γ)
def aKm (u:e9) :Prop :=
  ∃ (a :ℕ) (g:kB[X]),g≠0∧g.natDegree≤a∧a≤t ∧
    ∀ P:kB[X],P.natDegree≤t →
      (((So u).map (algebraMap K[X] kB)).mulVec (fun i=>P.coeff i.val)=0 ↔
        ∃ Q:kB[X],Q.natDegree≤t - a∧P=g*Q)
abbrev bcD (u:e9) :=ayo p node (u 0) (u 1) L t
def aYx (u:e9) :Prop :=
  Vv u=(bcD u).rank
def abC (u:e9) :Prop :=
  2≤R5 u∧aDf u=L ∧ ¬ aB8 u ∧
    ¬ aKm u ∧ ¬ aYx u
structure qo (u:e9) where
  a :ℕ
  b:ℕ
  c:ℕ
  ab:a≤b
  active :b≤t
  inactive :t<c
  top:c≤k
  degreeSum:a+b+c=2*k+2
  nullitySum:R5 u+a+b=2*(t+1)
  level :kL.aKl
    (fun s j=>algebraMap K[X] kB (Principal.P8 p node (u 0) (u 1) s j))
    k a b c
def qo.height {u:e9} (T:qo u) :=(k+1) - T.c
abbrev Relation {u:e9} (T:qo u) :=
  kL.axT p node (u 0) (u 1) k T.height
def y1 {u:e9} {T:qo u} (R:Relation T) :nC :=
  Principal.assemble (fun j=>R.coefficients (0,j))
def zv {u:e9} {T:qo u} (R:Relation T) :nC :=
  Principal.assemble (fun j=>R.coefficients (1,j))
def pJ {u:e9} {T:qo u} (R:Relation T) :Finset I:= by
  classical
  exact Finset.univ.filter fun i =>
    (y1 R).eval (C (node i))=0∧(zv R).eval (C (node i))=0
def aYI {u:e9} {T:qo u} (R:Relation T) :Prop :=
  ∃ G:K[X],aiE (G.map (algebraMap K kB))
    (sZ (y1 R)) (sZ (zv R))
def aSe {u:e9} {T:qo u} (R:Relation T) :Prop :=
  ¬ aYI R ∧ ∃ G:kB[X],G≠0∧G∣sZ (y1 R) ∧
    G∣sZ (zv R)∧(pJ R).card<G.natDegree
def as1 {u:e9} {T:qo u} (R:Relation T) :Prop :=
  max (y1 R).natDegree (zv R).natDegree<T.height ∨
    ∃ G:K[X],G≠0∧G.map Polynomial.C∣y1 R∧G.map Polynomial.C∣zv R ∧
      ¬ G∣mL node Finset.univ
structure aSC {u:e9} {T:qo u} (R:Relation T)
    {γ:K} (M:B5 u γ) :Prop where
  U_ne :vn (y1 R) γ≠0
  V_ne :vn (zv R) γ≠0
  degree_eq :max (vn (y1 R) γ).natDegree (vn (zv R) γ).natDegree =
    T.height
  gcd_errors : ∃ errors :Finset I,
    (∀ i∈errors,M.decoder.eval (node i)≠u 0 i+γ*u 1 i) ∧
    aiE (mL node errors) (vn (y1 R) γ) (vn (zv R) γ)
  fixed_errors : ∀ i∈pJ R,M.decoder.eval (node i)≠u 0 i+γ*u 1 i
  valid : ¬ as1 R
def axB {u:e9} {T:qo u} (R:Relation T) :Prop :=
  ∀ γ,Normal u γ → ∀ M:B5 u γ,aSC R M
structure Reduction (u:e9) (T:qo u) (R:Relation T) where
  U:nC
  V:nC
  output :nC
  height:ℕ
  height_eq :height+(pJ R).card=T.height
  max_degree :max U.natDegree V.natDegree=height
  U_ne :U≠0
  V_ne :V≠0
  coprime :IsCoprime (sZ U) (sZ V)
  U_factor :y1 R=jH (mL node (pJ R))*U
  V_factor :zv R=jH (mL node (pJ R))*V
  output_factor :R.output=jH (mL node (pJ R))*output
  output_degree :output.degree<(k+height:ℕ)
  deleted_error : ∀ γ,Normal u γ → ∀ M:B5 u γ,∀ i∈pJ R,
    M.decoder.eval (node i)≠u 0 i+γ*u 1 i
structure KJ (u:e9) (T:qo u) (R:Relation T)
    (D:Reduction u T R) where
  rank_eq :Xb D.U D.V=3
  α:Fin 2→K[X]
  β:Fin 2→K[X]
  a :K[X]
  b:K[X]
  a_ne :a≠0
  b_ne :b≠0
  α_primitive :IsCoprime (α 0) (α 1)
  β_primitive :IsCoprime (β 0) (β 1)
  first_degree :a.natDegree+uO (β 0) (β 1)≤D.height
  second_degree :b.natDegree+uO (α 0) (α 1)≤D.height
  same_direction :Z4 D.U D.V (JO a β) (J9 b α)
  output :nC
  output_degree :output.degree<(k+D.height:ℕ)
  nodes :ake u (pJ R) (JO a β) (J9 b α) output
def Parallel {u T R D} (B:KJ u T R D) :Prop :=
  B.α=B.β
def baQ {u T R D} (B:KJ u T R D) :Prop :=
  B.α 0*B.β 1 - B.α 1*B.β 0≠0
def aSM {u T R D} (B:KJ u T R D) :Prop :=
  Ox B.a=Ox B.b
abbrev FJ:=P1.FJ
abbrev bjQ := @P1.bjQ
abbrev bje := @P1.bje
abbrev FJ.iF := @P1.FJ.iF
abbrev FJ.label := @P1.FJ.label
abbrev FJ.wK := @P1.FJ.wK
abbrev FJ.decoder := @P1.FJ.decoder
abbrev jG:=FJ DY
abbrev awT {u deleted} (M:jG u deleted) :=bjQ (A:=dw) M
abbrev mJ {u deleted} (M:jG u deleted) :=bje dw M
abbrev jG.iF {u deleted} (M:jG u deleted) :=FJ.iF M
abbrev jG.label {u deleted} (M:jG u deleted) :=FJ.label M
abbrev jG.wK {u deleted} (M:jG u deleted) :=FJ.wK M
abbrev jG.decoder {u deleted} (M:jG u deleted) {γ:K} (B:B5 u γ) :=
  FJ.decoder M B
abbrev lowRegular :ℕ:=0x3c9b27d091bc914
inductive gJ where
  | rectTight
  | rectPruned
  | rectTailOne
  | rectTailTwo
  | rectTailThree
  | graph
  | near
  | middle
  | far
def gJ.lo:gJ→ℕ
  | .rectTight=>2355
  | .rectPruned=>2360
  | .rectTailOne=>2368
  | .rectTailTwo=>2375
  | .rectTailThree=>2382
  | .graph=>2407
  | .near=>2535
  | .middle=>2704
  | .far=>3600
def gJ.hi:gJ→ℕ
  | .rectTight=>2359
  | .rectPruned=>2367
  | .rectTailOne=>2374
  | .rectTailTwo=>2381
  | .rectTailThree=>2406
  | .graph=>2534
  | .near=>2703
  | .middle=>3599
  | .far=>33561
def gJ.regular :gJ→ℕ
  | .rectTight=>0x3c2e4b7183555ec
  | .rectPruned=>0x38a700758b82f53
  | .rectTailOne=>0x33a89ec159a1149
  | .rectTailTwo=>0x2d3858bd2a52a0e
  | .rectTailThree=>0x239fb466c5455fe
  | .graph=>0x3280d59995ddc5c
  | .near=>0x39a9bf4e9dda3ed
  | .middle=>0x25ed9d49dbd1c57
  | .far=>0x3cd53f7b0bf176
end
end P6
end
