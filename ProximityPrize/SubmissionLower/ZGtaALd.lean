import ProximityPrize.SubmissionLower.ZzP7Fpd
set_option Elab.async false
section
set_option autoImplicit true
namespace qkgz7gb
open P5 (p)
open P5_7_3 (fO cV aKj)
open Dt (jJ)
def wX (b:fO) :ℕ:=131071+b.pricedHi
private def ordinateMultiplier (e :ℕ) :ℕ→ℕ
 | 0=>0
 | 1=>e-1
 | 2=>e
 | 3=>2*e
 | 4=>3*e
 | 5=>5*e
 | 6=>8*e
 | 7=>12*e
 | 8=>20*e
 | _=>32*e
private def ratio (i:ℕ) :ℕ :=
 [2,4,8,12,16,24,32,48,64,96,128,256,512,1024][i]?.getD 0
private def decode (D e u n:ℕ) :Witness :=
 let g:=ordinateMultiplier e (n%16)
 let E :=e+g
 let asym:=n/1024%2=1
 let i:=n/16%4
 let k :=n/64%16
 let scale :=if asym then [100,130,175,250][i]?.getD 0 else [100,125,150,200][i]?.getD 0
 let s :=if asym then Stock.asymmetric ((p-1-E*u)/e-u) (ratio k*u)
   else Stock.symmetric (4*2^k*u)
 ⟨g,E*D*scale/100+1,n/2048,s⟩
def Ready (D e u cap:ℕ) :Prop :=
  ∃ w:Witness,FilterOK D e u w∧CurveOK D e w.weight w.stock ∧
    0<smoothRate D e u w.weight w.stock∧2*smoothRate D e u w.weight w.stock<p ∧
    (highStock e u w).b5A+planeFee (smoothRate D e u w.weight w.stock)≤ cap
private instance (D e u:ℕ) (w:Witness) :Decidable (FilterOK D e u w) := by
 unfold FilterOK
 infer_instance
private instance (D e W:ℕ) (s :Stock) :Decidable (CurveOK D e W s) := by
 cases s <;> unfold CurveOK <;> infer_instance
private theorem checked {D e u cap:ℕ} (n:ℕ)
    (h₁:FilterOK D e u (decode D e u n))
    (h₂:CurveOK D e (decode D e u n).weight (decode D e u n).stock)
    (h₃:0<smoothRate D e u (decode D e u n).weight (decode D e u n).stock)
    (h₄:2*smoothRate D e u (decode D e u n).weight (decode D e u n).stock<p)
    (h₅: (highStock e u (decode D e u n)).b5A +
        planeFee (smoothRate D e u (decode D e u n).weight (decode D e u n).stock)≤ cap) :
    Ready D e u cap :=
  ⟨decode D e u n,h₁,h₂,h₃,h₄,h₅⟩
private def E5 (D cap:ℕ) :ℕ→List jJ→Prop
 | _,[]=>True
 | e,g :: gs=>Ready D e g.seedCap cap∧E5 D cap (e+1) gs
private theorem Gx {D cap} (gs :List jJ) (e :ℕ)
   (hall:E5 D cap e gs) (i:Fin gs.length) :Ready D (i.val+e) (gs.get i).seedCap cap:= by
 induction gs generalizing e with
 | nil=>exact Fin.elim0 i
 | cons g gs ih =>
   rcases i with ⟨_ | j,hj⟩
   · change Ready D (0+e) g.seedCap cap
     simpa only [Nat.zero_add] using hall.1
   · have h:=ih (e+1) hall.2 ⟨j,by simpa using hj⟩
     simpa only [List.get_cons_succ,Nat.succ_add,Nat.add_succ] using h
local notation "r!" n=>checked n (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem each (b:fO) :E5 (wX b) b.schedule.retainedFee 1 b.schedule.gw:= by
 cases b
 · exact ⟨r! 0x1c15a030,r! 0x4c16a031,r! 0x7c179031,r! 0xac187831,r! 0xa1ee7061,r! 0xc2a7f062,
  r! 0xba1e4093,r! 0xd5799093,r! 0xd05258c4,r! 0xe7c530c4,r! 0xff40c0c4,r! 0xfc7d1104,
  r! 0x110a85105,r! 0x125b95905,r! 0x123673145,r! 0x136ee6145,r! 0x14a7be945,r! 0x15e072945,
  r! 0x15eb05186,r! 0x1712ba686,r! 0x183ad1686,r! 0x1962e0686,r! 0x1a8aea686,r! 0x1bb31ae86,
  r! 0x1cdbf1186,r! 0x1e0421186,r! 0x1f2c4a186,r! 0x221674945,trivial⟩
 · exact ⟨r! 0x1c160030,r! 0x4c179031,r! 0x7c192031,r! 0xac1aa031,r! 0xa1f09061,r! 0xc2aa8062,
  r! 0xba20b093,r! 0xd57c6093,r! 0xd05520c4,r! 0xe7c848c4,r! 0xff4420c4,r! 0xfc807104,
  r! 0x110abf905,r! 0x125bd4905,r! 0x1236b1945,r! 0x136f28945,r! 0x14a805145,r! 0x15e0bd945,
  r! 0x171958145,r! 0x171306e86,r! 0x183b22686,r! 0x196337686,r! 0x1a8b47e86,r! 0x1ab9846c7,
  r! 0x1bd7016c7,r! 0x1cf4796c7,r! 0x1f2cb7186,r! 0x2054df186,r! 0x217cff986,r! 0x2771ee105,trivial⟩
 · exact ⟨r! 0x1c168030,r! 0x4c18e831,r! 0x7c1b5031,r! 0xac1da831,r! 0xa1f38861,r! 0xc2ae1862,
  r! 0xba243893,r! 0xd5806893,r! 0xd05918c4,r! 0xe7ccb0c4,r! 0xff4900c4,r! 0xfc854904,
  r! 0x110b13105,r! 0x125c2e105,r! 0x12370a945,r! 0x136f88145,r! 0x14a86a145,r! 0x15e128945,
  r! 0x1719c9145,r! 0x171373686,r! 0x183b94686,r! 0x1963ade86,r! 0x1a8bc2e86,r! 0x1bb3fee86,
  r! 0x1cdc30e86,r! 0x1e051b986,r! 0x1f2d4e986,r! 0x20557a986,r! 0x23501b145,trivial⟩
 · exact ⟨r! 0x1c17c830,r! 0x4c1c6831,r! 0x7c20f831,r! 0xac258031,r! 0xa1fb2061,r! 0xc2b74062,
  r! 0xba2d0893,r! 0xd58a8893,r! 0xd06308c4,r! 0xe7d7c0c4,r! 0xff5528c4,r! 0xfc915904,
  r! 0x110be3105,r! 0x125d0e905,r! 0x1237e9945,r! 0x137075945,r! 0x14a967145,r! 0x15e234945,
  r! 0x15ec52686,r! 0x171488686,r! 0x183cb5e86,r! 0x1964dc686,r! 0x1a8cfe686,r! 0x1bb546e86,
  r! 0x1cde42186,r! 0x1e0689986,r! 0x20e076945,r! 0x22190e945,trivial⟩
 · exact ⟨r! 0x1c192030,r! 0x4c200031,r! 0x7c26e031,r! 0xac2da831,r! 0xa202d861,r! 0xc2c08062,
  r! 0xba35f093,r! 0xd594b893,r! 0xd06d00c4,r! 0xe7e2d0c4,r! 0xff6160c4,r! 0xfc9d6904,
  r! 0x110cb4105,r! 0x125def905,r! 0x1238c8945,r! 0x137163945,r! 0x14aa64145,r! 0x15e340945,
  r! 0x15ed5de86,r! 0x1715a1686,r! 0x183ddce86,r! 0x196611e86,r! 0x1a8e41686,r! 0x1bb697e86,
  r! 0x1cdfa3986,r! 0x1e07f9186,r! 0x20e205945,r! 0x24d2c9905,trivial⟩
 · exact ⟨r! 0x1c1a0030,r! 0x4c224031,r! 0x7c2a6831,r! 0xac327831,r! 0xa2092861,r! 0xc2c84062,
  r! 0xe55c5062,r! 0xd59e2093,r! 0xf1012893,r! 0xe7ed88c4,r! 0xff6d28c4,r! 0x116dba0c4,
  r! 0x111f33104,r! 0x125ecd105,r! 0x13b0dc905,r! 0x1502a2105,r! 0x14ab60145,r! 0x15e44b145,
  r! 0x171d18145,r! 0x1855cc145,r! 0x198e78945,r! 0x19673b686,r! 0x1a8f7d686,r! 0x1bb7e7686,
  r! 0x1ce049686,r! 0x1e08a2e86,r! 0x1f30f5e86,r! 0x205941e86,r! 0x218274986,r! 0x22aac3186,
  r! 0x23d31f986,r! 0x26ff8b145,trivial⟩
 · exact ⟨r! 0x1c1f3830,r! 0x4c305031,r! 0x7c415831,r! 0xac524031,r! 0xd7b72022,r! 0xc2ecf862,
  r! 0xe5877862,r! 0xd5c6b093,r! 0xf12ee893,r! 0xe819c0c4,r! 0xff9dd8c4,r! 0x11710c8c4,
  r! 0x112278104,r! 0x127738104,r! 0x13b49e905,r! 0x1506a3105,r! 0x16585f905,r! 0x15e6c6e05,
  r! 0x172180945,r! 0x185a6e145,r! 0x1b9ff9905,r! 0x1cf1f4905,trivial⟩
 · exact ⟨r! 0x1c1f9030,r! 0x4c310831,r! 0x7c425831,r! 0xac537831,r! 0xd7ae7822,r! 0xc2f1b862,
  r! 0xe58c9862,r! 0xd5cd3893,r! 0xf1365093,r! 0x10caea893,r! 0xffa678c4,r! 0x1171a18c4,
  r! 0x12ea628c4,r! 0x1461ad0c4,r! 0x13cda7104,r! 0x15075b905,r! 0x153b07dc5,r! 0x17ab1f905,
  r! 0x18fd3f905,r! 0x1a4f0b905,r! 0x1ea8000c4,trivial⟩
 · exact ⟨r! 0x1c20e830,r! 0x4c34a031,r! 0x7c482831,r! 0xac5b8031,r! 0xd7b6b022,r! 0xc52f9861,
  r! 0xe597d862,r! 0xd5d80893,r! 0xf1428093,r! 0x10cbc3893,r! 0xffb380c4,r! 0x1172858c4,
  r! 0x12eb5a0c4,r! 0x1462b80c4,r! 0x13ceac104,r! 0x150871105,r! 0x153c20dc5,r! 0x17ac5a905,
  r! 0x18fe8f905,r! 0x1a507b905,r! 0x1ba228905,r! 0x2021128c4,trivial⟩
 · exact ⟨r! 0x1c20f030,r! 0x4c349831,r! 0x7c481831,r! 0xac5b6031,r! 0xd7b35822,r! 0xc5305061,
  r! 0xe598a862,r! 0xd5d94893,r! 0xf143e893,r! 0x10cbdc893,r! 0xffb540c4,r! 0x1172a30c4,
  r! 0x12eb790c4,r! 0x1462d88c4,r! 0x15db8b0c4,r! 0x151fc3d84,r! 0x1678c9104,r! 0x17ac7a105,
  r! 0x18fea3105,r! 0x1d32f38c4,r! 0x239282893,trivial⟩
 · exact ⟨r! 0x1c228030,r! 0x4c38e031,r! 0x7c4f1031,r! 0xac651031,r! 0xd7bf0822,r! 0xc53b8061,
  r! 0xe5a5a862,r! 0xd5e58093,r! 0xf151b093,r! 0x10ccd1093,r! 0xffc3e0c4,r! 0x1173a20c4,
  r! 0x12ec8d8c4,r! 0x1464020c4,r! 0x15dcca0c4,r! 0x1520f8584,r! 0x167a11904,r! 0x17add2105,
  r! 0x19255c104,r! 0x1d34560c4,r! 0x2af44a062,trivial⟩
 · exact ⟨r! 0x1c236030,r! 0x4c3b1831,r! 0x7c52a031,r! 0xac69e831,r! 0xd7c1c022,r! 0xc5422861,
  r! 0xe5ad5862,r! 0x10885b062,r! 0xf15a6893,r! 0x10cd6c093,r! 0x12851e093,r! 0x1174470c4,
  r! 0x12ed3e8c4,r! 0x1464be0c4,r! 0x147788544,r! 0x1755758c4,r! 0x18cdaa8c4,r! 0x1a45a50c4,
  r! 0x1bbc190c4,trivial⟩
 · exact ⟨r! 0x1c25f030,r! 0x4c41f831,r! 0x7c5dd831,r! 0xac797031,r! 0xd7d2f022,r! 0xc5548061,
  r! 0xe5c29062,r! 0x1089e3062,r! 0xf1712893,r! 0x10cf00893,r! 0x1286dc093,r! 0x1175ee8c4,
  r! 0x12ef0a0c4,r! 0x1466ad0c4,r! 0x147979d44,r! 0x1757aa8c4,r! 0x18d0048c4,r! 0x1a48270c4,
  r! 0x1bbf098c4,trivial⟩
 · exact ⟨r! 0x1c283830,r! 0x4c481831,r! 0x7c67a831,r! 0xac870031,r! 0xdca5e831,r! 0xc565c861,
  r! 0xe5d69862,r! 0x108b51062,r! 0xf1874893,r! 0x10d089893,r! 0x128887893,r! 0x11778c8c4,
  r! 0x12e2d6504,r! 0x1468828c4,r! 0x15e1870c4,r! 0x1759868c4,r! 0x18d14f0c4,r! 0x25770f062,trivial⟩
 · exact ⟨r! 0x1c2d3830,r! 0x4c557831,r! 0x7c7d6831,r! 0xaca4e031,r! 0xdccbe831,r! 0xc589e061,
  r! 0xe6006862,r! 0x108e52062,r! 0xf1b47093,r! 0x10d3a9093,r! 0x128bf1893,r! 0x14441f093,
  r! 0x12e64c504,r! 0x146c360c4,r! 0x15e53d0c4,r! 0x1b1e66893,trivial⟩
 · exact ⟨r! 0x1c373030,r! 0x4c702831,r! 0x7ca8a831,r! 0xace0b031,r! 0xdd183031,r! 0x108f2a022,
  r! 0xe6540062,r! 0x109451862,r! 0x12c354862,r! 0x10d9ec093,r! 0x1292d7893,r! 0x144ba4893,
  r! 0x1414204c4,r! 0x1473e50c4,r! 0x19747c093,r! 0x1b2a19093,trivial⟩
 · exact ⟨r! 0x1c3e0830,r! 0x4c822831,r! 0x7cc57831,r! 0xad07e031,r! 0xdd495031,r! 0x109052022,
  r! 0xe91a1061,r! 0x10988b062,r! 0x12c808062,r! 0x10de89093,r! 0x12bec6493,r! 0x1450da093,
  r! 0x160975893,r! 0x17c0bb893,r! 0x1fb0b1862,trivial⟩
 · exact ⟨r! 0x1c549830,r! 0x4cbeb031,r! 0x7d27e831,r! 0xad8f9031,r! 0xddf5b031,r! 0x10e591031,
  r! 0xe9d6d061,r! 0x10a5c9062,r! 0x12d6a9062,r! 0x14f314452,r! 0x1735b4862,r! 0x195e80062,trivial⟩
theorem ready (b:fO) (i:aKj b) :
  Ready (wX b) (i.val+1) (cV b i).seedCap b.schedule.retainedFee :=
 Gx _ _ (each b) i
end qkgz7gb
end
section
set_option autoImplicit true
namespace qkgz7gb
noncomputable section
open Polynomial
open P5 (K p)
open cu (aZ Equation vm kr qD yq jz
 bqt)
open Y3 (ek)
open private fXn from ProximityPrize.SubmissionLower.BJ
open scoped BigOperators
private theorem coordinate_resultant {f g:Equation} (i:Fin 2) {u v :ℕ}
   (hf : ∀ j,(f.coeff j).degreeOf i≤u) (hg : ∀ j,(g.coeff j).degreeOf i≤v) :
   (f.resultant g).degreeOf i≤f.natDegree*v+g.natDegree*u:= by
 classical
 let m:=f.natDegree
 let n:=g.natDegree
 let A:=sylvester f g m n
 let cap:Fin (m+n)→ℕ:= fun j=>j.addCases (fun _=>v) (fun _=>u)
 have entry (a j:Fin (m+n)) : (A a j).degreeOf i≤ cap j:= by
   refine Fin.addCases ?_ ?_ j
   · intro b
     simp only [A,cap,sylvester,Matrix.of_apply,Fin.addCases_left]
     split
     · apply hg
     · simp
   · intro b
     simp only [A,cap,sylvester,Matrix.of_apply,Fin.addCases_right]
     split
     · apply hf
     · simp
 change A.det.degreeOf i≤ m*v+n*u
 rw [Matrix.det_apply]
 refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun π _ => ?_)
 have term : (∏ j,A (π j) j).degreeOf i≤ m*v+n*u :=
   (MvPolynomial.degreeOf_prod_le _ _ _).trans <| calc
     _ ≤ ∑ j,cap j:=Finset.sum_le_sum fun j _=>entry (π j) j
     _ = _:= by rw [Fin.sum_univ_add]; simp [cap]
 rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simpa [h] using term
theorem no_constant_root {f :Equation} (hf :f.IsPrimitive) (hd:f.natDegree=0) (z :K)
  (S:K[X]) :yq f z S≠0:= by
 have h:=eq_C_of_natDegree_eq_zero hd
 have hu:IsUnit (f.coeff 0) :=(isPrimitive_iff_isUnit_of_C_dvd.mp hf) _ (h ▸ dvd_rfl)
 exact (((h.symm ▸ hu.map C:IsUnit f)).map (eval₂RingHom (qD z) (kr S))).ne_zero
theorem ePy {f g:Equation} {e E u:ℕ} (s :Stock)
    (hf :f.IsPrimitive) (hfe :f.natDegree≤e) (hge :g.natDegree≤E)
    (hfv :vm f u) (hgv :s.fits g)
    (hcop:IsCoprime (ek f) (ek g)) (hp: (s.resultantShift e E u).first<p)
    (T:Finset K) (z :K→K) (S:K→K[X]) (hz :Set.InjOn z (T:Set K))
    (hfr : ∀ γ∈T,yq f (z γ) (S γ)=0)
    (hgr : ∀ γ∈T,yq g (z γ) (S γ)=0) :
    T.card≤(s.resultantShift e E u).b5A:= by
  classical
  by_cases hd:f.natDegree=0
  · have he :T = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun γ hγ =>
      no_constant_root hf hd _ _ (hfr γ hγ)
    simp [he]
  let R:=f.resultant g
  have hcop' : IsCoprime (f.map (algebraMap aZ (FractionRing aZ)))
      (g.map (algebraMap aZ (FractionRing aZ))) :=hcop
  have hn:=resultant_ne_zero _ _ hcop'
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective aZ (FractionRing aZ)),
    natDegree_map_eq_of_injective (IsFractionRing.injective aZ (FractionRing aZ)),
    resultant_map_map] at hn
  have hR:R≠0:= fun h=>hn (by rw [show f.resultant g=0 from h,map_zero])
  have hzero (γ:K) (hγ:γ∈T) :qD (z γ) R=0:= by
    obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl hd)
    have ev :=congrArg (eval₂RingHom (qD (z γ)) (kr (S γ))) hab
    have h₁:=hfr γ hγ
    have h₂:=hgr γ hγ
    change f.eval₂ _ _=0 at h₁
    change g.eval₂ _ _=0 at h₂
    simpa [R,eval₂_add,eval₂_mul,h₁,h₂] using ev.symm
  have hcap (v :ℕ) :f.natDegree*v+g.natDegree*u≤e*v+E*u :=
    Nat.add_le_add (Nat.mul_le_mul_right _ hfe) (Nat.mul_le_mul_right _ hge)
  cases s with
  | symmetric v =>
    have hbound:R.totalDegree≤e*v+E*u:=(fXn hfv hgv).trans (hcap v)
    let C:qQ.VN :=⟨R,hR,∅⟩
    have hc:=qQ.aJr hz C (hbound.trans_lt hp) (fun γ hγ=>Or.inl (hzero γ hγ))
    have hcard:T.card≤(p+1)*R.totalDegree := by
      simpa only [C,Finset.card_empty,Nat.add_zero] using hc
    exact hcard.trans (Nat.mul_le_mul_left _ hbound)
  | asymmetric vz vt =>
    have ha :R.degreeOf 0≤e*vz+E*u :=
      (coordinate_resultant 0 (fun _=>(MvPolynomial.degreeOf_le_totalDegree _ _).trans (hfv _))
        (fun j=>(hgv j).1)).trans (hcap vz)
    have hb:R.degreeOf 1≤e*vt+E*u :=
      (coordinate_resultant 1 (fun _=>(MvPolynomial.degreeOf_le_totalDegree _ _).trans (hfv _))
        (fun j=>(hgv j).2)).trans (hcap vt)
    let V:=T.image fun γ=>jz (z γ)
    have hi:V.card=T.card:=Finset.card_image_of_injOn
      (fun _ ha _ hb h=>hz ha hb (jz.injective h))
    have hc:=bqt p _ _ (by decide) R hR ha hp hb V (by
      intro x hx
      obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
      exact hzero γ hγ)
    exact hi ▸ hc
end
end qkgz7gb
end
section
set_option autoImplicit true
namespace quj0Mle
noncomputable section
open qkgz7gb (PlaneCurve)
open cu (L triangle)
open MvPolynomial
abbrev aax :=Fin 2→L
abbrev Space (n:ℕ) :=restrictTotalDegree (Fin 2) L n
abbrev Ib (q r :PlaneCurve) :=Ideal.span ({q,r} : Set PlaneCurve)
theorem XK (n:ℕ) :2*(n*(n+1)/2)=n*(n+1) := by
 obtain ⟨a,ha⟩:=Nat.even_mul_succ_self n
 omega
theorem bye (n:ℕ) :2*triangle n=(n+1)*(n+2) :=
 XK (n+1)
private theorem cFD (n:ℕ) : (n+Nat.card (Fin 2)).choose (Nat.card (Fin 2)) =
  triangle n:= by
 simp [Nat.choose_two_right,triangle,Nat.mul_comm (n+2)]
private theorem space_rank (n:ℕ) :Module.finrank L (Space n)=triangle n:= by
 rw [show Space n=restrictSupport L {m:Fin 2 →₀ ℕ | m.degree≤n} from rfl,
  Module.finrank_eq_nat_card_basis (basisRestrictSupport L _),Nat.card_coe_set_eq,
  Finsupp.ncard_setOf_degree_le,cFD]
theorem interpolate (S:Finset aax) (n:ℕ) (h:S.card<triangle n) :
  ∃ r :PlaneCurve,r≠0∧r.totalDegree≤n ∧ ∀ x∈S,r.eval x=0:= by
 let E :Space n →ₗ[L] (S→L) :=LinearMap.pi fun x =>
  (aeval x.val).toLinearMap.comp (Space n).subtype
 have hr :Module.finrank L (S→L)<Module.finrank L (Space n) := by
  rw [space_rank,Module.finrank_fintype_fun_eq_card,Fintype.card_coe]
  exact h
 obtain ⟨r,hker,hn⟩:=Submodule.exists_mem_ne_zero_of_ne_bot
  (E.ker_ne_bot_of_finrank_lt hr)
 refine ⟨r,fun h0=>hn (Subtype.ext h0),(mem_restrictTotalDegree _ _ _).mp r.2,?_⟩
 intro x hx
 exact congrFun (LinearMap.mem_ker.mp hker) ⟨x,hx⟩
theorem pair_rank {q r :PlaneCurve} (hq:Irreducible q) (hr :r≠0)
   (hd:r.totalDegree<q.totalDegree) (n:ℕ)
   (hn:q.totalDegree+r.totalDegree≤n) :
   affineHilbertFunction (Ib q r) n≤q.totalDegree*r.totalDegree := by
 let d:=q.totalDegree
 let e :=r.totalDegree
 let I:Ideal PlaneCurve :=Ideal.span {q}
 have hprime :I.IsPrime :=(Ideal.span_singleton_prime hq.ne_zero).2 hq.prime
 have hni:r∉I:= fun h =>
   hd.not_ge (totalDegree_le_of_dvd_of_isDomain (Ideal.mem_span_singleton.mp h) hr)
 have hcut:=principalCut_affineHilbertFunction_add_le_of_isPrime
   hprime hni (b:=e) (N :=n) le_rfl (by omega :e≤n)
 have heq :I ⊔ Ideal.span {r} = Ib q r := by
   change Ideal.span ({q} : Set PlaneCurve) ⊔ Ideal.span {r} = Ideal.span {q,r}
   rw [← Ideal.span_union]
   congr 1
 rw [heq] at hcut
 have h₁:=affineHilbertFunction_span_singleton hq.ne_zero (N :=n) (by omega)
 have h₂:=affineHilbertFunction_span_singleton hq.ne_zero (N :=n-e) (by omega)
 rw [cFD,cFD] at h₁ h₂
 have hcast: (affineHilbertFunction (Ib q r) n:ℚ) +
     (affineHilbertFunction I (n-e) :ℚ)≤(affineHilbertFunction I n:ℚ) := by
   exact_mod_cast hcut
 change (affineHilbertFunction I n:ℚ)=(triangle n:ℚ)-(triangle (n-d) :ℚ) at h₁
 change (affineHilbertFunction I (n-e) :ℚ) =
   (triangle (n-e) :ℚ)-(triangle (n-e-d) :ℚ) at h₂
 rw [h₁,h₂] at hcast
 have balance :triangle n+triangle (n-e-d) =
     d*e+triangle (n-d)+triangle (n-e) := by
   obtain ⟨t,rfl⟩ : ∃ t,n=t+d+e :=⟨n-d-e,by omega⟩
   rw [show t+d+e-e-d=t by omega,show t+d+e-d=t+e by omega,
     show t+d+e-e=t+d by omega]
   apply Nat.eq_of_mul_eq_mul_left (n:=2) (by decide)
   simp only [Nat.mul_add,bye]
   ring
 have hb: (triangle n:ℚ)+(triangle (n-e-d) :ℚ) =
     (d:ℚ)*e+(triangle (n-d) :ℚ)+(triangle (n-e) :ℚ) := by exact_mod_cast balance
 have hc: (affineHilbertFunction (Ib q r) n:ℚ)≤(d:ℚ)*e := by linarith
 exact_mod_cast hc
end
end quj0Mle
end
