import ProximityPrize.SubmissionLower.Z3gZttb
import ProximityPrize.SubmissionLower.ZXTI5ee
set_option Elab.async false
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem r1 :total 2760 12=0x1cfe99173ac0 :=
  r! 0x26fe64579a0,r! 0x26eecdfb900,r! 0x26df318f840,r! 0x26cfa02f910,
  r! 0x26c00a7f3e0,r! 0x26b07ffc1c0,r! 0x26a0f0abd80,r! 0x26916eef830,
  r! 0x2681e41baf0,r! 0x267268cb5d0,r! 0x2662e679c80,r! 0x26536fe9e40,
  rfl
private theorem r2 :total 2772 12=0x1c7368d253f0 :=
  r! 0x2643f453d50,r! 0x26348449d70,r! 0x26250f6f3c0,r! 0x2615a8c74b0,
  r! 0x260637d6f50,r! 0x25f6d798ca0,r! 0x25e76f0ae20,r! 0x25d813aed30,
  r! 0x25c8b239230,r! 0x25b95f84580,r! 0x25aa0257400,r! 0x259ab612dd0,
  rfl
private theorem r3:total 2784 11=0x199b60f8b0e0 :=
  r! 0x258b5fbf8d0,r! 0x257c1aa4330,r! 0x256ccc07610,r! 0x255d8bc2d40,
  r! 0x254e43e7cd0,r! 0x253f0cb3f90,r! 0x252fc99e880,r! 0x25209852300,
  r! 0x25115c19180,r! 0x2502313b360,r! 0x24f2fd7c4d0,rfl
theorem apk :total 2760 35=0x530d62e23f90 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
section
set_option autoImplicit true
namespace q6nKpZc
noncomputable section
open Polynomial Finset
open scoped BigOperators Classical
open P6 (K p jG)
open P6_7_4 (wordLift)
open P5_7_2 (A fO Window Ls stages movingOrder Donors NodeUnits terminal row topDonors)
open q7F2qKe (agA au1 nV origins isLast originBudget lineFee
  fibreShape kK BC earlyFee afterFree stops lossTail globalCap originFreeCap
  Individual SS projectionCap pointFee weakAgreement)
open cu (L Jet j9)
open DP (jF zG aKF VY)
open gT (Ambient tK IZ iJ FW)
open pI (xN dual oU abM NO acW pN)
open TD (J2 FP aBh)
structure Input (b:fO) {u del} (M:jG u del) {Γ} (F:P1.bje A M Γ) where
  vo:Window b M.iF
  regular :M.shift∉Γ
  H :L[X]
  bY:P6_7.YQ M F H
  D:jF M.iF.toNat
  first:D.block 0=H
  second:D.block 1=H.map (frobenius L p)
  units :NodeUnits D
  residues : ∀ γ∈Γ,aKF D (M.label γ) (F.scalar γ)
  crt:zG D
  donors :Donors b crt (wordLift M)
abbrev Input.banks {b u del M Γ F} (x : @Input b u del M Γ F) :=VY x.crt (wordLift M)
def I0 {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (I:Ideal Ambient) (γ:K) :Prop :=IZ I (M.label γ) (F.scalar γ)
def aHl {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (C:acW) :Finset K:=Γ.filter fun γ => ∃ Q∈C.qv,I0 F Q γ
structure TopPair {u del} (M:jG u del) {Γ} (F:P1.bje A M Γ) (b:fO) where
  raw:Fin 2→Bool→jA.jK
  nonzero : ∀ i e,raw i e≠0
  conjugate : ∀ e,raw 1 e=MvPolynomial.map (Polynomial.mapRingHom (frobenius L p)) (raw 0 e)
  caps : ∀ i e,
    let t:=if e then (topDonors b).2 else (topDonors b).1
    jA.vC (raw i e)≤t.shape.B∧jA.lP (raw i e)≤t.shape.J ∧
      (raw i e).degreeOf (some 2)≤t.YM∧jA.gY (raw i e)≤t.shape.U ∧
      jA.ahb (row b).declaredHi
        (t.shape.m*weakAgreement-1+(t.shape.B+t.shape.J)*(row b).declaredHi) (raw i e)
  zero : ∀ i e γ,γ∈Γ →
    MvPolynomial.eval (jA.ED (cu.jz (M.label γ)^(p^i.val))
      (jA.jW (j9 (F.scalar γ)))) (jA.bC (raw i e))=0
  no_moving_top : ∀ i (f :jA.ko),Irreducible f→0<f.degreeOf (some 2) →
    f∣jA.bC (raw i false)→f∣jA.bC (raw i true) →
    jA.gY f=0
def FixedTariff {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ) (b:fO) :Prop :=
  ∀ B J,aBh B J → ∀ G:tK,abM G B J → ∀ T⊆Γ,
    (∀ γ∈T,FW G (F.scalar γ)=0)→T.card≤au1 b B J
structure FixedPartPair {b u del M Γ F} (x : @Input b u del M Γ F)
    (s :Ls) (hs :s∈stages b) where
  free :NO (x.donors.staged s hs).free.jet s.free
  moving:NO (x.donors.staged s hs).moving.jet s.moving
structure aAT {u del} {M:jG u del} {Γ}
    (F:P1.bje A M Γ) (b:fO) (x :Input b M F) where
  factors :ℕ→Finset Jet
  parents :ℕ→Jet→Finset (Ideal Ambient)
  cut:ℕ→Jet→Jet
  rescue :ℕ→Jet→Bool
  line :ℕ→Jet→Finset K
  zo:Finset K
  fixed : ∀ s (hs :s∈stages b),(FixedPartPair x s hs)
  firstFactor : ∀ o∈origins b,∀ f∈factors o,
    Irreducible f∧gT.alm f ∧
      ∃ hs :nV b 0∈stages b,f∣(x.donors.staged _ hs).free.jet
  tail : ∀ i∈origins b,∀ k,
    ∑ o∈(origins b).filter (i ≤ ·),∑ f∈factors o,akZ.yE f k≤originBudget b i k
  rescue_last : ∀ o∈origins b,∀ f∈factors o,rescue o f=true →
    isLast b o ∧ ∀ k,0<akZ.yE f k
  line_price : ∀ o∈origins b,∀ f∈factors o,
    (line o f).card≤ if rescue o f then lineFee b (akZ.yE f) else 0
  proper : ∀ o∈origins b,∀ f∈factors o,
    oU (cut o f) (fibreShape b o (rescue o f)) ∧ ¬ f∣cut o f
  nonlast_common : ∀ o∈origins b,¬ isLast b o → ∀ f∈factors o,∀ g∈factors o,cut o f=cut o g
  DN : ∀ o∈origins b,∀ f∈factors o,∀ I∈parents o f,
    xN I∧I.height=2∧iJ f∈I∧iJ (cut o f)∈I ∧
      ∀ s (hs :s∈stages b),¬ pI.aaS (fixed s hs).free.equation I ∧
        ¬ pI.aaS (fixed s hs).moving.equation I
  parent_unique : ∀ o∈origins b,∀ f∈factors o,∀ o' ∈ origins b,∀ f' ∈ factors o',
    ∀ I∈parents o f,I∈parents o' f' → o=o' ∧ f=f'
  factor_cap : ∀ o∈origins b,∀ f∈factors o,∀ k,
    J2 (parents o f) k≤kK (akZ.yE f) (fibreShape b o (rescue o f)) k
  mass_cap : ∀ k,∑ o∈origins b,∑ f∈factors o,J2 (parents o f) k≤BC b k
  early_price :zo.card≤earlyFee b
  Eh : ∀ γ∈Γ,γ∈zo ∨ ∃ o∈origins b,∃ f∈factors o,
    γ∈line o f ∨ ∃ I∈parents o f,I0 F I γ
def Pass {b u del M Γ F} (x : @Input b u del M Γ F) (j:ℕ) (I:Ideal Ambient) :Prop :=
  if j=0 then dual I else
  if j<afterFree b then agA x.banks (nV b j).free I else
  match (movingOrder b)[j-afterFree b]? with
  | none=>agA x.banks (terminal b).shape I
  | some n =>
    let s :=nV b n
    ∃ hs :s∈stages b,agA x.banks s.free I∧agA x.banks s.moving I ∧
      aFX.aTw (x.donors.staged s hs).free.jet (x.donors.staged s hs).moving.jet I
structure Timeline {b u del M Γ F} {x : @Input b u del M Γ F} (C:aAT F b x) where
  stopped :ℕ→Jet→ℕ→Finset (Ideal Ambient)
  Bp:ℕ→Jet→Finset (Ideal Ambient)
  cuts :ℕ→Jet→ℕ→ Ideal Ambient→acW
  stopped_at : ∀ o∈origins b,∀ f∈C.factors o,∀ j∈stops b,∀ I∈stopped o f j,
    I∈C.parents o f ∧ ¬ Pass x j I ∧ ∀ i<j,Pass x i I
  kept_at : ∀ o∈origins b,∀ f∈C.factors o,∀ I∈Bp o f,
    I∈C.parents o f∧dual I∧agA x.banks (terminal b).shape I
  exhaust : ∀ o∈origins b,∀ f∈C.factors o,∀ I∈C.parents o f,
    I∈Bp o f ∨ ∃ j∈stops b,I∈stopped o f j
  aNI : ∀ o∈origins b,∀ f∈C.factors o,∀ k,
    ∑ j∈stops b,J2 (stopped o f j) k ≤
      kK (akZ.yE f) (fibreShape b o (C.rescue o f)) k
  global_bound : ∀ i∈stops b,∀ k,
    ∑ o∈origins b,lossTail b C.factors stopped o i k≤globalCap b i k
  free_bound : ∀ o∈origins b,∀ k,
    lossTail b C.factors stopped o (afterFree b) k≤originFreeCap b o k
  individual : ∀ o∈origins b,∀ f∈C.factors o,∀ j∈stops b,∀ I∈stopped o f j,
    Individual b o j (fun k=>pN I k)
  cut_cost : ∀ o∈origins b,∀ f∈C.factors o,∀ j∈stops b,0<j →
    ∀ I∈stopped o f j,∀ i,
      ((cuts o f j I).cost i:ℚ)≤FP (SS b j i) fun k=>pN I k
  cut_cover : ∀ o∈origins b,∀ f∈C.factors o,∀ j∈stops b,0<j →
    ∀ I∈stopped o f j,∀ γ∈Γ,I0 F I γ →
      γ∈(cuts o f j I).direct ∨ ∃ Q∈(cuts o f j I).qv,I0 F Q γ
  total_projection :
    (∑ o∈origins b,∑ f∈C.factors o,∑ j∈(stops b).filter (0 < ·),
      ∑ I∈stopped o f j,((cuts o f j I).cost 0:ℚ))≤projectionCap b
  total_points :
    (∑ o∈origins b,∑ f∈C.factors o,∑ j∈(stops b).filter (0 < ·),
      ∑ I∈stopped o f j,(cuts o f j I).direct.card)≤pointFee b
end
end q6nKpZc
end
