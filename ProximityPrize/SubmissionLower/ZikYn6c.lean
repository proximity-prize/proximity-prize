import ProximityPrize.SubmissionLower.ZITfVad
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZDusXie
import ProximityPrize.SubmissionLower.ZXrG2Fd
import ProximityPrize.SubmissionLower.Zeg869c
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.mem_filter → zO0, Finset.mem_insert → z4p, Finsupp.add_apply → zSs, Finsupp.weight_single → zTy, Int.toNat_of_nonneg → zi4, LinearMap.ker → z83, LinearMap.range → zWl, Matrix.rank_transpose → zZo, Matrix.transpose_map → znz, Module.finrank → zsE, Polynomial.C → z1z, Polynomial.natDegree_mul → zNh, Set.mem_ofPred_eq → zsi, Submodule.finrank_mono → zFM
set_option maxRecDepth 12000
section
set_option autoImplicit true
namespace qxuyiwe
open qK9H6va (offset Vm iO Gy)
noncomputable section
abbrev Pivot (hist:List ℕ) :=Σ i:Fin hist.length,Fin hist[i.val]
abbrev PivotIndex (hist:List ℕ) :=Pivot hist→Fin 57
abbrev FF {hist:List ℕ} (ix :PivotIndex hist) (g w:ℤ) :=
  {j:Pivot hist // (j.1.val :ℤ)+(ix j).val<w ∧ -g≤(ix j).val}
instance {hist:List ℕ} (ix :PivotIndex hist) (g w:ℤ) :
    Fintype (FF ix g w) :=Fintype.ofFinite _
def profileCutoff (q d:ℕ) (g:ℤ) :ℤ:=Vm q g+d
def Profile (d:ℕ) (hist:List ℕ) :Prop :=
  ∃ ix :PivotIndex hist,∀ q,iO q=d → ∀ r :Fin 155,
    (Gy q (offset r)).rank ≤
      Fintype.card (FF ix (offset r) (profileCutoff q d (offset r)))
def charge (n:ℕ) :List ℕ→ℕ
  | []=>0
  | c :: cs=>c*n+charge (n - 1) cs
theorem charge_append (n:ℕ) (xs ys :List ℕ) :
    charge n (xs ++ ys)=charge n xs+charge (n - xs.length) ys := by
  induction xs generalizing n with
  | nil=>simp [charge]
  | cons x xs ih =>
    simp only [List.cons_append,charge,ih,List.length_cons,Nat.sub_sub,Nat.add_assoc]
    rw [Nat.add_comm 1 xs.length]
private def r510 :List ℕ:=[12,4,4,5,17,10,10,12,24,18,18,21,33,28,28,32,44]
private def r511 :List ℕ:=[40,40,45, 57,54,54,60,70,68,65,71,80,75,73,75,85,79]
private def r512 :List ℕ:=[77,78,90,81,82,80,95,82,86,82,96,85,86,84,97,85,88]
private def r513:List ℕ:=[83,98,85,87,84,96,85,85,84,94,81,85,84,85,81,81,83]
private def r514 :List ℕ:=[75,81,76,77,72,77,70,74,67,70,62,64,56,56,49,49,42]
private def r515:List ℕ:=[42,36,36,30,30,25,25,20,20,16,16,12,12,9]
def h51 :List ℕ:=r510 ++ r511 ++ r512 ++ r513 ++ r514 ++ r515
theorem charge51 :charge (99+51 - 51) h51 =
    qK9H6va.Ni 51 := by
  simp only [h51,charge_append]
  change charge 99 r510+charge 82 r511+charge 65 r512+charge 48 r513+charge 31 r514+charge 14 r515=278819
  rw [show charge 99 r510=28290 by rfl,
    show charge 82 r511=79668 by rfl,
    show charge 65 r512=82651 by rfl,
    show charge 48 r513=58625 by rfl,
    show charge 31 r514=26569 by rfl,
    show charge 14 r515=3016 by rfl]
private def r520:List ℕ:=[9,3,4,4,14,8,10,10,21,15,18,18,30,24, 28,28,41]
private def r521 :List ℕ:=[35,40,40,54,48,54,54,69,61,68,65,80,71,75,73,84,76]
private def r522 :List ℕ:=[79,77,87,81,81,82,89,86,82,86,91,87,85,86,93,88,85]
private def r523:List ℕ:=[88,92,89,85,87,93,87,85,86,91,86,82,87,86,82,83,83]
private def r524 :List ℕ:=[80,78,82,74,78,75,75,71,75,67,70,62,64,56,56,49,49]
private def r525:List ℕ:=[42,42,36,36,30,30,25,25,20,20,16,16,12,12]
def h52 :List ℕ:=r520 ++ r521 ++ r522 ++ r523 ++ r524 ++ r525
theorem charge52 :charge (99+52 - 52) h52 =
    qK9H6va.Ni 52 := by
  simp only [h52,charge_append]
  change charge 99 r520+charge 82 r521+charge 65 r522+charge 48 r523+charge 31 r524+charge 14 r525=273470
  rw [show charge 99 r520=25145 by rfl,
    show charge 82 r521=76348 by rfl,
    show charge 65 r522=82144 by rfl,
    show charge 48 r523=59049 by rfl,
    show charge 31 r524=27509 by rfl,
    show charge 14 r525=3275 by rfl]
theorem charge114 :charge (99+52 - 114) h52 =
    qK9H6va.Ni 114 := by
  simp only [h52,charge_append]
  change charge 37 r520+charge 20 r521+charge 3 r522+charge 0 r523+charge 0 r524+charge 0 r525=19387
  rw [show charge 37 r520=7475 by rfl,
    show charge 20 r521=11434 by rfl,
    show charge 3 r522=478 by rfl,
    show charge 0 r523=0 by rfl,
    show charge 0 r524=0 by rfl,
    show charge 0 r525=0 by rfl]
theorem charge115:charge (99+52 - 115) h52 =
    qK9H6va.Ni 115:= by
  simp only [h52,charge_append]
  change charge 36 r520+charge 19 r521+charge 2 r522+charge 0 r523+charge 0 r524+charge 0 r525=17812
  rw [show charge 36 r520=7190 by rfl,
    show charge 19 r521=10387 by rfl,
    show charge 2 r522=235 by rfl,
    show charge 0 r523=0 by rfl,
    show charge 0 r524=0 by rfl,
    show charge 0 r525=0 by rfl]
private def r530:List ℕ:=[6,3, 3,4,10,8,8,10,16,15,15,18,24, 24, 24, 28,34]
private def r531 :List ℕ:=[35, 35,40,46,48,48,54,60,63,61,68,71,74,71,75,79,78]
private def r532 :List ℕ:=[76,79,83,81,81,81,88,83,86,82,92,85,87,85,92,87,88]
private def r533:List ℕ:=[85,94,86,89,85,93,87,87,85,92,85,86,84,89,82,84,85]
private def r534 :List ℕ:=[80,82,80,79,76,80,73,76,72,75,67,70,62,64,56,56,49]
private def r535:List ℕ:=[49,42,42,36,36,30,30,25,25,20,20,16,16,12]
def h53:List ℕ:=r530 ++ r531 ++ r532 ++ r533 ++ r534 ++ r535
theorem charge53:charge (99+53 - 53) h53 =
    qK9H6va.Ni 53:= by
  simp only [h53,charge_append]
  change charge 99 r530+charge 82 r531+charge 65 r532+charge 48 r533+charge 31 r534+charge 14 r535=267974
  rw [show charge 99 r530=22020 by rfl,
    show charge 82 r531=73255 by rfl,
    show charge 65 r532=81583 by rfl,
    show charge 48 r533=59238 by rfl,
    show charge 31 r534=28279 by rfl,
    show charge 14 r535=3599 by rfl]
private def r540:List ℕ:=[4, 2,3, 3,8,6,8,8,14,12,15,15,22,20,24, 24,32]
private def r541 :List ℕ:=[30,35, 35,44,42,48,48,58,56,63,61,72,67,74,71,79,75]
private def r542 :List ℕ:=[78,76,83,79,81,81,85,84,83,86,86,88,85,87,89,88,87]
private def r543:List ℕ:=[88,89,90,86,89,89,89,87,87,89,88,85,87,86,86,83,86]
private def r544 :List ℕ:=[82,81,84,78,80,78,78,74,77,72,75,67,70,62,64,56,56]
private def r545:List ℕ:=[49,49,42,42,36,36,30,30,25,25,20,20,16,16]
def h54 :List ℕ:=r540 ++ r541 ++ r542 ++ r543 ++ r544 ++ r545
theorem charge54 :charge (99+54 - 54) h54 =
    qK9H6va.Ni 54 := by
  simp only [h54,charge_append]
  change charge 99 r540+charge 82 r541+charge 65 r542+charge 48 r543+charge 31 r544+charge 14 r545=262388
  rw [show charge 99 r540=19330 by rfl,
    show charge 82 r541=69655 by rfl,
    show charge 65 r542=81009 by rfl,
    show charge 48 r543=59462 by rfl,
    show charge 31 r544=29046 by rfl,
    show charge 14 r545=3886 by rfl]
theorem charge112 :charge (99+54 - 112) h54 =
    qK9H6va.Ni 112 := by
  simp only [h54,charge_append]
  change charge 41 r540+charge 24 r541+charge 7 r542+charge 0 r543+charge 0 r544+charge 0 r545=22884
  rw [show charge 41 r540=6570 by rfl,
    show charge 24 r541=14091 by rfl,
    show charge 7 r542=2223 by rfl,
    show charge 0 r543=0 by rfl,
    show charge 0 r544=0 by rfl,
    show charge 0 r545=0 by rfl]
theorem charge113:charge (99+54 - 113) h54 =
    qK9H6va.Ni 113:= by
  simp only [h54,charge_append]
  change charge 40 r540+charge 23 r541+charge 6 r542+charge 0 r543+charge 0 r544+charge 0 r545=21143
  rw [show charge 40 r540=6350 by rfl,
    show charge 23 r541=13133 by rfl,
    show charge 6 r542=1660 by rfl,
    show charge 0 r543=0 by rfl,
    show charge 0 r544=0 by rfl,
    show charge 0 r545=0 by rfl]
private def r550:List ℕ:=[2,2,2,3,5,6,6,8,10,12,12,15,17,20,20,24, 26]
private def r551 :List ℕ:=[30,30,35, 37,42,42,48,50,56,56,63,63,70,67,74,73,77]
private def r552 :List ℕ:=[75,78,78,81,79,81,83,83,84,83,88,84,88,85,89,87,88]
private def r553:List ℕ:=[87,90,87,90,86,91,87,89,87,89,87,88,85,89,84,86,85]
private def r554 :List ℕ:=[84,82,83,82,78,82,77,78,75,77,72,75,67,70,62,64,56]
private def r555:List ℕ:=[56,49,49,42,42,36,36,30,30,25,25,20,20,16]
def h55:List ℕ:=r550 ++ r551 ++ r552 ++ r553 ++ r554 ++ r555
theorem charge55:charge (99+55 - 55) h55 =
    qK9H6va.Ni 55:= by
  simp only [h55,charge_append]
  change charge 99 r550+charge 82 r551+charge 65 r552+charge 48 r553+charge 31 r554+charge 14 r555=256718
  rw [show charge 99 r550=16660 by rfl,
    show charge 82 r551=66290 by rfl,
    show charge 65 r552=80290 by rfl,
    show charge 48 r553=59560 by rfl,
    show charge 31 r554=29684 by rfl,
    show charge 14 r555=4234 by rfl]
end
end qxuyiwe
end
section
set_option autoImplicit true
namespace qnnEPee
noncomputable section
open xE (Flag gd denominator)
open akL (Jp adw bob azA
  BU Oq)
private def boxed (s :zJe (Fin 4)) (cap:Fin 4→ℕ) (d u:ℤ) :zJe Jp :=
  (adw d u).filter (fun e => ∀ i∈s,e i<cap i)
private theorem mem_boxed {s :zJe (Fin 4)} {cap:Fin 4→ℕ} {d u:ℤ} {e :Jp} :
    e∈boxed s cap d u↔(e.weight BU:ℤ)=d ∧
      (e.weight Oq:ℤ)≤u ∧ ∀ i∈s,e i<cap i:= by
  simp only [boxed,zO0,azA,bob,
    zsi,and_assoc]
private theorem boxed_insert {i:Fin 4} {s :zJe (Fin 4)} (hi:i∉s)
    (cap:Fin 4→ℕ) (d u:ℤ) :
    ((boxed (insert i s) cap d u).card:ℤ)=((boxed s cap d u).card:ℤ) -
      ((boxed s cap (d - cap i) (u-(cap i:ℤ)*(Oq i:ℤ))).card:ℤ) := by
  classical
  let b:=boxed s cap d u
  let t:=b.filter fun e=>cap i≤e i
  let m:=Finsupp.single i (cap i)
  have hshift (e :Jp) :
      e∈boxed s cap (d - cap i) (u-(cap i:ℤ)*(Oq i:ℤ)) ↔
        e+m∈t:= by
    have he : (∀ j∈s,(e+m) j<cap j) ↔ ∀ j∈s,e j<cap j:= by
      have he' (j:Fin 4) (hj:j∈s) :m j=0 :=
        Finsupp.single_eq_of_ne (fun h=>hi (h ▸ hj))
      constructor <;> intro h j hj <;> simpa [zSs,he' j hj] using h j hj
    have hg: ((e+m).weight BU:ℤ)=(e.weight BU:ℤ)+cap i:= by
      simp only [m,map_add,zTy,BU,smul_eq_mul,mul_one,Nat.cast_add]
    have hw: ((e+m).weight Oq:ℤ) =
        (e.weight Oq:ℤ)+(cap i:ℤ)*(Oq i:ℤ) := by
      simp only [m,map_add,zTy,smul_eq_mul,Nat.cast_add,Nat.cast_mul]
    have hi' : (e+m) i=e i+cap i:= by simp [m,zSs]
    simp only [t,b,zO0,mem_boxed,hg,hw,hi',he]
    constructor
    · rintro ⟨hg',hw',hs⟩
      exact ⟨⟨by omega,by omega,hs⟩,by omega⟩
    · rintro ⟨⟨hg',hw',hs⟩,_⟩
      exact ⟨by omega,by omega,hs⟩
  have hcard: (boxed s cap (d - cap i) (u-(cap i:ℤ)*(Oq i:ℤ))).card=t.card:= by
    apply Finset.card_bij (fun e _=>e+m)
    · exact fun e h=>(hshift e).mp h
    · exact fun _ _ _ _ h=>add_right_cancel h
    · intro e he
      have hm:m≤e :=Finsupp.single_le_iff.mpr (Finset.mem_filter.mp he).2
      have heq :e - m+m=e :=tsub_add_cancel_of_le hm
      exact ⟨_,(hshift _).mpr (by rwa [heq]),heq⟩
  have hdiff :b \ t=boxed (insert i s) cap d u:= by
    ext e
    simp only [b,t,Finset.mem_sdiff,zO0,mem_boxed,z4p,forall_eq_or_imp]
    constructor
    · rintro ⟨⟨hd,hu,hs⟩,hn⟩
      exact ⟨hd,hu,(lt_of_not_ge fun hk=>hn ⟨⟨hd,hu,hs⟩,hk⟩),hs⟩
    · rintro ⟨hd,hu,hk,hs⟩
      exact ⟨⟨hd,hu,hs⟩,fun h=>(not_le_of_gt hk) h.2⟩
  have hc:=Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ b :
    t⊆b)
  rw [hdiff,← hcard] at hc
  change _+_=(boxed s cap d u).card at hc
  omega
private theorem boxed_empty (cap:Fin 4→ℕ) (d u:ℤ) :
    ((boxed ∅ cap d u).card:ℤ)=gd d u:= by
  simpa [boxed] using aw7.proof d u
private theorem cIK {d u:ℤ} (h:u≤d) :
    gd d u=denominator u:= by
  by_cases hu:u<0
  · simp [gd,denominator,hu]
  · have hd : ¬ d<0:= by omega
    have hz (v :ℤ) (hv :v<0) :denominator v=0:= by simp [denominator,hv]
    simp (disch:=omega) [gd,hu,hd,hz]
theorem reduced_card (F:Flag) :
    ((reducedColumns F).card:ℤ)=P6_6_2.latticeAllowance F:= by
  let cap:Fin 4→ℕ := ![0,(boxU F).toNat,(boxV F).toNat,(boxW F).toNat]
  have hu:0≤boxU F:=le_max_left _ _
  have hv :0≤boxV F:=le_max_left _ _
  have hw:0≤boxW F:=le_max_left _ _
  have h1 : (cap 1 :ℤ)=boxU F:=zi4 hu
  have h2 : (cap 2 :ℤ)=boxV F:=zi4 hv
  have h3: (cap 3:ℤ)=boxW F:=zi4 hw
  have he :reducedColumns F=boxed {1, 2,3} cap (F.lower - 1) (F.lower - 1) := by
    ext e
    simp only [reducedColumns,momentColumns,zO0,azA,
      bob,zsi,mem_boxed,z4p,Finset.mem_singleton,
      forall_eq_or_imp,forall_eq,and_assoc]
    rw [← h1,← h2,← h3]
    norm_cast
  have hsingle (d u:ℤ) :
      ((boxed {3} cap d u).card:ℤ)=gd d u -
        gd (d - cap 3) (u-(cap 3:ℤ)*(Oq 3:ℤ)) := by
    simpa only [Finset.insert_empty,boxed_empty] using
      boxed_insert (i:=3) (s := ∅) (by simp) cap d u
  simp only [he,
    boxed_insert (by decide : (1 :Fin 4)∉({2,3} : zJe (Fin 4))),
    boxed_insert (by decide : (2 :Fin 4)∉({3} : zJe (Fin 4))),
    hsingle,
    show (Oq 1 :ℤ)=1 by rfl,show (Oq 2 :ℤ)=2 by rfl,
    show (Oq 3:ℤ)=3 by rfl,h1,h2,h3,mul_one]
  simp (disch:=omega) only [cIK]
  let u:=F.lower - 1
  let x :=boxU F
  let y :=2*boxV F
  let z :=3*boxW F
  change _=denominator u - denominator (u - x) - denominator (u - y) -
    denominator (u - z)+denominator (u - x - y)+denominator (u - x - z) +
    denominator (u - y - z) - denominator (u - x - y - z)
  dsimp only [u,x,y,z]
  simp only [mul_comm (boxV F) 2,mul_comm (boxW F) 3]
  ring
end
end qnnEPee
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P6_4_1
noncomputable section
open Polynomial Matrix gR ProximityPrize.Benchmark P6
open aiG (aZ CS aPj aoI graph ceq b9w)
open private cr6 b5J cUi cEJ from ProximityPrize.SubmissionLower.Z
private theorem cSo (u:e9) (T:qo u) :
    Bx.ay6
      (kL.af7 p node (u 0) (u 1) k T.height)=1 :=
  kL.b4H p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1≤t by decide).trans_lt T.inactive) T.level
theorem eLQ (u:e9) (T:qo u)
    (hh:T.height≤DY) :
    zsE (CS K) (z83
      ((aPj p node (u 0) (u 1) k T.height).map
        (algebraMap (aZ K) (CS K))).mulVecLin)=1 := by
  let A:=aPj p node (u 0) (u 1) k T.height
  have hdeg (j:Fin (k - T.height)) (b:Fin 2×Fin (T.height+1)) :
      (A j b).degreeOf 0≤ if b.1=0 then 1 else 0 :=
    cr6 p node (u 0) (u 1) b.1 0 _
  have hsize :T.height+1<p :=
    (Nat.add_le_add_right hh 1).trans_lt (by decide)
  have he :=ceq p (by decide) hsize A hdeg
  change (A.map (algebraMap (aZ K) (CS K))).rank =
    ((aPj p node (u 0) (u 1) k T.height).map _).rank at he
  rw [b5J] at he
  have hn:=Bx.cep
    (kL.af7 p node (u 0) (u 1) k T.height)
  rw [cSo u T] at hn
  apply aRz.eFB
  change (A.map (algebraMap (aZ K) (CS K))).rank+1= _
  rw [he]
  exact hn
theorem c4h (u:e9) (b:Fin 2×Fin L) (j:Fin (t+1))
    (i:Fin 2) :
    (aoI p node (u 0) (u 1) L t b j).degreeOf i ≤
      if b.1=i then 1 else 0 :=
  cr6 p node (u 0) (u 1) b.1 i _
theorem eL2 (u:e9) :
    ((aoI p node (u 0) (u 1) L t).map
      (algebraMap (aZ K) (CS K))).rank=Vv u:= by
  let A:=aoI p node (u 0) (u 1) L t
  have hdeg (j:Fin (t+1)) (b:Fin 2×Fin L) :
      (A.transpose j b).degreeOf 0≤ if b.1=0 then 1 else 0 :=
    c4h u b j 0
  have he :=ceq p (by decide) (by decide) A.transpose hdeg
  rw [znz,znz,zZo,zZo] at he
  change ((aoI p node (u 0) (u 1) L t).map _).rank =
    ((aoI p node (u 0) (u 1) L t).map _).rank at he
  rw [cUi] at he
  exact he
theorem ekq (u:e9) (T:qo u) (R:Relation T)
    (Q:Fin 2×Fin (T.height+1)→aZ K)
    (hQ: (aPj p node (u 0) (u 1) k T.height).mulVec Q=0)
    (hgraph: (fun j=>graph p (Q j))≠0) :
    ∃ c:K[X],c≠0 ∧ ∀ j,graph p (Q j)=c*R.coefficients j:= by
  classical
  let f :=algebraMap K[X] kB
  let M:=(kL.af7 p node (u 0) (u 1) k T.height).map f
  let E := fun j=>f (R.coefficients j)
  let V:= fun j=>f (graph p (Q j))
  obtain ⟨a,ha⟩:=(M4.a6R R.coefficients).mp R.primitive
  have hinj:=IsFractionRing.injective K[X] kB
  have hE :E≠0:= by
    intro he
    have hzero (j:Fin 2×Fin (T.height+1)) :R.coefficients j=0 :=
      hinj ((congrFun he j).trans (map_zero f).symm)
    simp only [hzero,mul_zero,Finset.sum_const_zero,zero_ne_one] at ha
  have hME :M.mulVec E=0 :=
    cEJ p node (u 0) (u 1) IRSProfile.domain.injective
      Native.ahU k k T.height
      (by rw [IRSProfile.card_index]; decide) R
  have hMV:M.mulVec V=0:= by
    change ((kL.af7 p node (u 0) (u 1) k T.height).map f).mulVec V=0
    rw [← b5J]
    change ((aPj p node (u 0) (u 1) k T.height).map
      (f.comp (graph p).toRingHom)).mulVec
      (fun j=>(f.comp (graph p).toRingHom) (Q j))=0
    rw [b9w,hQ]
    funext j
    rw [Pi.zero_apply,map_zero,Pi.zero_apply]
  obtain ⟨b,hb⟩:=aRz.cWG M
    (cSo u T) E hE hME V hMV
  let c := ∑ j,a j*graph p (Q j)
  have hc:f c=b:= by
    have hbe :=congrArg f ha
    simp only [map_sum,map_mul,map_one] at hbe
    simp only [c,map_sum,map_mul]
    have he (j:Fin 2×Fin (T.height+1)) :f (graph p (Q j))=b*f (R.coefficients j) :=
      congrFun hb j
    simp_rw [he,mul_left_comm (f (a _)) b,← Finset.mul_sum,hbe,mul_one]
  have he (j:Fin 2×Fin (T.height+1)) :graph p (Q j)=c*R.coefficients j:= by
    apply hinj
    rw [map_mul,hc]
    exact congrFun hb j
  refine ⟨c,?_,he⟩
  intro hzero
  apply hgraph
  funext j
  rw [he,hzero,zero_mul,Pi.zero_apply]
end
noncomputable section
open Polynomial Matrix gR P6
open aiG (aZ CS Gz aoI c4f dd5
  Kn bD0 graph b5H acH ZL brc
  b6p cVx cVw b5G)
private theorem cUh {F:Type} [Field F] {h:ℕ} (q:ℕ)
    (Q:Fin 2×Fin (h+1)→aZ F) (a :Fin 2×Fin (h+1)→F[X])
    (c:F[X]) (hQ : ∀ j,graph q (Q j)=c*a j) (b:Fin 2) :
    (Gz Q b).map (graph q).toRingHom =
      z1z c*Principal.assemble (fun j=>a (b,j)) := by
  rw [Gz,Principal.cZi]
  change Principal.assemble (fun j=>graph q (Q (b,j)))= _
  simp only [hQ,Principal.assemble,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.C_mul_monomial]
theorem proof :P6_4.c1 := by
  intro u front T R
  classical
  let h:=T.height
  let s :=L - h
  have hbal:L+h+R5 u=t+1 :=a7J T
  have hhi:h≤DY:=aEz front T
  have hL:h<L:=hhi.trans_lt (by decide)
  have hsum:h+s=L:= by omega
  have hs :0<s := by omega
  have hsL:s≤L:=Nat.sub_le _ _
  have hSlice :=eLQ u T hhi
  obtain ⟨Q,hQne,hQ,hPrim⟩:=c4f _ (by rw [hSlice]; decide)
  let M:=aoI p node (u 0) (u 1) L t
  let W:=Mc.Sm (Gz Q) L s
  have hRank : (M.map (algebraMap (aZ K) (CS K))).rank+s=2*L:= by
    rw [eL2 u,aSO u]
    omega
  have hker :W.transpose*M=0 :=
    dd5 p node (u 0) (u 1) h L s t hsum Q hQ
  obtain ⟨hMP,hattain⟩:=cxJ.proof K h L s Q hsum hs hQne hPrim
  have hprod (b i:Fin 2) :s*Kn Q b i≤ if b=i then h else L:= by
    by_cases hd:Kn Q b i=0
    · simp only [hd,Nat.mul_zero,Nat.zero_le]
    obtain ⟨rows,hdet⟩:=hattain b i (Nat.pos_of_ne_zero hd)
    have hb:=cxK.proof K L (t+1) s M W hs hsL hRank hker
      (c4h u) hMP b i rows
    rw [hdet] at hb
    simpa only [show L - s=h by omega] using hb
  have hgraph: (fun j=>graph p (Q j))≠0:= by
    intro hz
    apply hQne
    funext j
    change Q j=0
    by_contra hne
    obtain ⟨b,i⟩:=j
    have hbound:s*Kn Q b 0≤L:= by
      apply (hprod b 0).trans
      split_ifs
      · exact hL.le
      · exact le_rfl
    have hone :1≤ s :=hs
    have hdeg: (Q (b,i)).degreeOf 0≤L :=
      (bD0 Q b 0 i).trans
        ((by simpa only [one_mul] using Nat.mul_le_mul_right (Kn Q b 0) hone :
          Kn Q b 0≤ s*Kn Q b 0).trans hbound)
    exact b5H p (by decide) _ hne (hdeg.trans_lt (by decide)) (congrFun hz (b,i))
  obtain ⟨c,hc,hgraphQ⟩:=ekq u T R Q hQ hgraph
  have hdegree (b i:Fin 2) :
      s*(ZL (Gz Q b)).degreeOf (acH i) ≤
        if b=i then h else L :=
    (Nat.mul_le_mul_left s (cVx Q b i)).trans (hprod b i)
  refine ⟨{
    U:=ZL (Gz Q 0)
    V:=ZL (Gz Q 1)
    U_omits :=⟨brc Q 0 1 (Or.inl rfl),brc Q 0 2 (Or.inr rfl)⟩
    V_omits :=⟨brc Q 1 1 (Or.inl rfl),brc Q 1 2 (Or.inr rfl)⟩
    heights :=⟨b6p Q 0,b6p Q 1⟩
    Ca := ?_
    primitive :=cVw Q hPrim
    content:=c
    content_ne :=hc
    graphU:=(b5G p (Gz Q 0)).trans (cUh p Q R.coefficients c hgraphQ 0)
    graphV:=(b5G p (Gz Q 1)).trans (cUh p Q R.coefficients c hgraphQ 1)
  }⟩
  have hseedS:acH 0=3:=rfl
  have hseedT:acH 1=4 :=rfl
  exact ⟨by simpa only [hseedS,ite_true] using hdegree 0 0,
    by simpa only [hseedT,ite_eq_right (show (0:Fin 2)≠1 by decide)] using hdegree 0 1,
    by simpa only [hseedS,ite_eq_right (show (1 :Fin 2)≠0 by decide)] using hdegree 1 0,
    by simpa only [hseedT,ite_true] using hdegree 1 1⟩
end
end P6_4_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6_4_2
noncomputable section
open P6 MvPolynomial
open gR (S8)
open Qo (graph yV)
open bRc (bqM)
open private b02 aI0 aCW bJU bsT dcS c3C from ProximityPrize.SubmissionLower.A1
open private an2 from ProximityPrize.SubmissionLower.B7
private theorem ddd {h d:ℕ} (hmax :h≤DY)
    (hd: (L - h)*d≤L) :d<p:= by
  have hh:h≤33561 :=hmax
  have hd' : d<4 :=an2 _ _ 4 _ hd (by
    change 48755<(48755 - h)*4
    omega)
  exact hd'.trans_le (by change 4≤0x7f000001; decide)
private theorem fVi {u:e9} {T:qo u} {R:Relation T}
    (D:Reduction u T R) (A:P6_4.ap3 R)
    {U V:MvPolynomial (Fin 5) K} (hU:U≠0) (hUo:yV U)
    (hS:U.degreeOf 3<p) (hAdU:U∣A.U) (hAdV:V∣A.V)
    (hgU:graph p U=z1z A.content*D.U)
    (hgV:graph p V=z1z A.content*D.V) :
    IsRelPrime U V:= by
  intro d hdU hdV
  let f :=(Polynomial.mapRingHom Aj.GC).comp (graph (F:=K) p).toRingHom
  have hfdU:f d∣sZ (z1z A.content*D.U) := by
    rw [← hgU]
    exact _root_.map_dvd f hdU
  have hfdV:f d∣sZ (z1z A.content*D.V) := by
    rw [← hgV]
    exact _root_.map_dvd f hdV
  have hu:=dcS D.coprime A.content_ne hfdU hfdV
  have hx :=Polynomial.natDegree_eq_zero_of_isUnit hu
  change ((graph p d).map Aj.GC).natDegree=0 at hx
  have hdo:=bJU hU hUo hdU
  rw [Polynomial.natDegree_map_eq_of_injective Aj.aAg,
    bqM p bsT d hdo
      ((aCW hU hdU 3).trans_lt hS)] at hx
  obtain ⟨q,rfl⟩:=c3C hdo hx
  exact (A.primitive q (hdU.trans hAdU) (hdV.trans hAdV)).map
    (rename (![3,4] :Fin 2→Fin 5))
theorem proof :P6_4.c2 := by
  intro u T R D hmax A
  have hhcap:T.height≤33561 :=hmax
  have hh:T.height≤L:=hhcap.trans (by decide :33561≤48755)
  have hASU:=ddd hmax (A.Ca.1.trans hh)
  have hASV:=ddd hmax A.Ca.2.2.1
  obtain ⟨U,hfU,hU,hgU⟩:=b02 (pJ R) A.U D.U A.content D.U_ne
    A.content_ne A.U_omits hASU (A.graphU.trans (by simp only [D.U_factor,P0.jH,K1.jH]))
  obtain ⟨V,hfV,hV,hgV⟩:=b02 (pJ R) A.V D.V A.content D.V_ne
    A.content_ne A.V_omits hASV (A.graphV.trans (by simp only [D.V_factor,P0.jH,K1.jH]))
  have hAdU:U∣A.U:=hfU.symm ▸ dvd_mul_left U (aI0 (pJ R))
  have hAdV:V∣A.V:=hfV.symm ▸ dvd_mul_left V (aI0 (pJ R))
  have hl:aI0 (pJ R)≠0:= by
    simpa only [aI0,EmbeddingLike.map_ne_zero_iff] using
      ((S8 node (pJ R)).map
        (MvPolynomial.C:K →+* MvPolynomial (Fin 4) K)).ne_zero
  have hAu:A.U≠0:=hfU.symm ▸ mul_ne_zero hl hU
  have hAv :A.V≠0:=hfV.symm ▸ mul_ne_zero hl hV
  have hUo:=bJU hAu A.U_omits hAdU
  have hVo:=bJU hAv A.V_omits hAdV
  have hUS:=(aCW hAu hAdU 3).trans_lt hASU
  have hVS:=(aCW hAv hAdV 3).trans_lt hASV
  refine ⟨⟨U,V,hUo,hVo,hU,hV,hAdU,hAdV,
    fVi D A hU hUo hUS hAdU hAdV hgU hgV,?_,hgU,hgV⟩⟩
  rw [← bqM p bsT U hUo hUS,
    ← bqM p bsT V hVo hVS,hgU,hgV,
    zNh (Polynomial.C_ne_zero.mpr A.content_ne) D.U_ne,
    zNh (Polynomial.C_ne_zero.mpr A.content_ne) D.V_ne,
    Polynomial.natDegree_C,zero_add,zero_add,D.max_degree]
end
end P6_4_2
end
section
set_option autoImplicit true
namespace P6_6_2
noncomputable section
open aR (ao af embed)
open xE (Local Ky oldCount m5 BH)
open akL (KP aDd)
open P6 (I K node)
open P6_6 (Pq aJ5 aWx Wk x5)
open private cZu dgs from ProximityPrize.SubmissionLower.AR
open private aOG fTs from ProximityPrize.SubmissionLower.AR
open scoped BigOperators
def c1 :Prop :=0x5678fbe532882ec9d≤ columns.card
def c2 :Prop :=
  ∀ (q:Fin (Wk.b+1)) (r :Offset),
    zsE ao (zWl (KP (pT q.val r))) ≤
      oppositeBound (pT q.val r)
def c3:Prop :=
  ∃ p:kJ,rankBand p 0 (Wk.b+1)≤ rankCap
private theorem drV (q:ℕ) (r :Offset) :
    zWl (KP (alp q r)) ≤
      zWl (KP (pT q r)) := by
  rintro _ ⟨p,rfl⟩
  refine ⟨⟨p.1,?_⟩,rfl⟩
  intro e he
  obtain ⟨hd,hl,hu,hc⟩:=p.2 he
  exact ⟨hd,hl,hu.trans (min_le_left _ _),hc⟩
private theorem prescribed_rank (q:ℕ) (r :Offset) (power :Fin 11→ℕ) :
    zsE ao (zWl (KP (alp q r))) ≤
      prescribedBound q r power := by
  let F:=pT q r
  let A:=alp q r
  change _≤(if F.order≤0 then 0 else
    (min (oldCount A)
      (oldCount F - max 0 (max (m5 F) (m5 (BH F power))))).toNat)
  by_cases ho:F.order≤0
  · rw [ite_eq_left ho]
    exact le_of_eq (fTs A ho)
  rw [ite_eq_right ho]
  have hCols :=bjv.proof aw7.proof
  have hRows :=aYY.proof aw7.proof
  let R:=BH F power
  have hKernel0:=aOG F (hCols F) (hRows F)
  have hKernel1 :=aOG R (hCols R) (hRows R)
  obtain ⟨f,hf⟩:=bjw.proof F power
  have hInj:=LinearMap.finrank_le_finrank_of_injective (f :=f) hf
  change zsE ao (z83 (KP R)) ≤
    zsE ao (z83 (KP F)) at hInj
  have hMax :max 0 (max (m5 F) (m5 R)) ≤
      (zsE ao (z83 (KP F)) :ℤ) :=
    max_le (Int.natCast_nonneg _) (max_le hKernel0 (by omega))
  have hActive :=(KP A).finrank_range_le
  have hNullity :=(KP F).finrank_range_add_finrank_ker
  rw [aDd] at hActive hNullity
  have hFullCols :=hCols F
  have hActiveCols :=hCols A
  have hRank :zsE ao (zWl (KP A)) ≤
      zsE ao (zWl (KP F)) :=
    zFM (drV q r)
  have hbound: (zsE ao (zWl (KP A)) :ℤ) ≤
      min (oldCount A) (oldCount F - max 0 (max (m5 F) (m5 R))) := by
    exact le_min (by omega) (by omega)
  change zsE ao (zWl (KP A)) ≤
    (min (oldCount A) (oldCount F - max 0 (max (m5 F) (m5 R)))).toNat
  omega
private theorem dme (w:I→K) {bound:ℕ}
    (h:zsE ao (zWl (nodeMap 0 0))≤bound) :
    zsE ao (zWl (asI w))≤262144*bound:= by
  let nmap (i:I) :=nodeMap (embed (node i)) (embed (w i))
  let B (i:I) :=zWl (nmap i)
  let f :W2 →ₗ[ao] (∀ i,B i) :=LinearMap.pi fun i=>(nmap i).rangeRestrict
  let g: (∀ i,B i) →ₗ[ao] (I→Local) :=
    LinearMap.pi fun i=>(B i).subtype.comp (LinearMap.proj i)
  have hw:asI w=g.comp f :=rfl
  rw [hw]
  calc
    zsE ao (zWl (g.comp f)) ≤
        zsE ao (zWl g) :=
      zFM (LinearMap.range_comp_le_range f g)
    _≤zsE ao (∀ i,B i) :=g.finrank_range_le
    _ = ∑ i,zsE ao (B i) :=Module.finrank_pi_fintype ao
    _ ≤ ∑ _:I,bound:=Finset.sum_le_sum fun i _ =>
      (zFM (eE5 (embed (node i)) (embed (w i)))).trans h
    _=262144*bound:= by
      simp [I,gR.Native.I,ProximityPrize.Benchmark.IRSProfile.Index]
private theorem d6l (w:I→K)
    (hker :x5≤zsE ao (z83 (asI w))) :aJ5 w:= by
  let vY:z83 (asI w) →ₗ[ao] af 4 :=
    Ky.toLinearMap.comp ((W2).subtype.comp (z83 (asI w)).subtype)
  have hinj:Function.Injective vY:= by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact Ky.injective hab
  refine cZu (V:=z83 (asI w)) (W:=af 4)
    vY hinj (Pq w aWx) ?_ hker
  intro Q
  obtain ⟨hbox,hprofile,hwt⟩:=bLI Q.1
  have hk :asI w Q.1=0:=(LinearMap.mem_ker (f :=asI w)).mp Q.2
  exact ⟨hbox,hprofile,hwt,dPo w Q.1 hk⟩
private theorem origin_rank (h2 :c2) (h3:c3) :
    zsE ao (zWl (nodeMap 0 0))≤ rankCap:= by
  obtain ⟨p,hp⟩:=h3
  have h:=eIb (fun q r=>xR q r (p q r)) (fun i =>
    le_min (prescribed_rank i.1.val i.2 (p i.1.val i.2))
      ((zFM (drV i.1.val i.2)).trans (h2 i.1 i.2)))
  unfold rankBand at hp
  rw [Nat.Ico_zero_eq_range] at hp
  exact h.trans hp
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_6.c2 := by
  intro w _
  have hr :=dme w (origin_rank h2 h3)
  have hc:262144*rankCap + x5≤ columns.card:=h1
  rw [← ebi] at hc
  exact d6l w (dgs hr hc (asI w).finrank_range_add_finrank_ker)
end
end P6_6_2
end
