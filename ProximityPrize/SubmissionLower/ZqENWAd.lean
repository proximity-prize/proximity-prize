import ProximityPrize.SubmissionLower.ZoYisee
import ProximityPrize.SubmissionLower.ZzDXtqd
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Function.Surjective → zpX, Ideal → znc, Ideal.span → zye, MvPolynomial → z3y, Nat.cast_nonneg → zqJ, Nat.cast_sub → zjK, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
namespace qXuDJRd
noncomputable section
open aR (Shape aO)
open oR (Wc amU)
open yz (aCt)
open Finset
open scoped BigOperators
open private bw6 from ProximityPrize.SubmissionLower.BI
private def akm (p:Shape) :=
  Σ z :Fin (p.t+1),Σ y :Fin (p.j - 2*z.val+1),Fin (p.b - z.val - y.val+1)
private def grS (p:Shape) (hp:bF p) :aCt p 0 ≃ akm p where
  toFun e := by
    have hb:=e.property.1
    have hj:=e.property.2.1
    have ht:=e.property.2.2.1
    let z :Fin (p.t+1) :=⟨e.val 2,by omega⟩
    let y :Fin (p.j - 2*z.val+1) :=⟨e.val 1,by dsimp [z]; omega⟩
    exact ⟨z,y,⟨e.val 0,by dsimp [z,y]; omega⟩⟩
  invFun a := by
    obtain ⟨z,y,x⟩:=a
    have hz :=z.isLt
    have hy :=y.isLt
    have hx :=x.isLt
    have hb:=hp.1
    have hj:=hp.2
    refine ⟨Finsupp.equivFunOnFinite.symm ![x.val,y.val,z.val,0],?_⟩
    change x.val+y.val+z.val≤p.b∧y.val+2*z.val≤p.j∧z.val≤p.t∧0≤0
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact (Nat.eq_zero_of_le_zero e.property.2.2.2).symm
  right_inv a := by
    rcases a with ⟨⟨z,hz⟩,⟨y,hy⟩,⟨x,hx⟩⟩
    rfl
private abbrev U (p:Shape) :ℚ:=p.t
private abbrev V (p:Shape) :ℚ:=(p.j:ℚ) - p.t
private abbrev W (p:Shape) :ℚ:=2*(p.b:ℚ) - p.j
private def count (p:Shape) :ℚ:=(U p+1)*(V p+1)*(W p+2)/2
private theorem lattice_formula (p:Shape) (hp:bF p) : (lattice p:ℚ)=count p:= by
  classical
  let:Fintype (akm p) := by unfold akm; infer_instance
  change ((aCt p 0).ncard:ℚ)= _
  rw [← Nat.card_coe_set_eq,Nat.card_congr (grS p hp),Nat.card_eq_fintype_card]
  change (Fintype.card (Σ z :Fin (p.t+1),Σ y :Fin (p.j - 2*z.val+1),
    Fin (p.b - z.val - y.val+1)) :ℚ)= _
  simp only [Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  rw [zdx (fun z => ∑ y :Fin (p.j - 2*z+1),
    ((p.b - z - y.val+1 :ℕ) :ℚ))]
  have hSlices :
      (∑ z∈range (p.t+1),∑ y :Fin (p.j - 2*z+1),((p.b - z - y.val+1 :ℕ) :ℚ)) =
        ∑ z∈range (p.t+1),(((p.j:ℚ)+1+(-2)*(z :ℚ))*(W p+2)/2) := by
    apply sum_congr rfl
    intro z hz
    have hz' := mem_range.mp hz
    have hj:=hp.2
    have hJ:2*z≤p.j:= by omega
    have hb:z≤p.b:= by have :=hp.1; omega
    rw [zdx (fun y=>((p.b - z - y+1 :ℕ) :ℚ))]
    calc
      _ = ∑ y∈range (p.j - 2*z+1),((p.b:ℚ) - z+1+(-1)*(y :ℚ)) := by
        apply sum_congr rfl
        intro y hy
        have hy' := mem_range.mp hy
        have hby :y≤p.b - z := by have :=hp.1; omega
        push_cast [zjK hby,zjK hb]
        ring
      _ = _:= by
        rw [bw6]
        push_cast [zjK hJ]
        ring
  rw [hSlices]
  simp_rw [mul_div_assoc]
  rw [← sum_mul,bw6]
  unfold count
  push_cast
  ring
private def polar (q r a :Shape) :ℚ :=
  (U q*(V r*W a+V a*W r)+V q*(U r*W a+U a*W r) +
    W q*(U r*V a+U a*V r))/2
private theorem btK (q r a :Shape) :polar q r a=polar r q a := by unfold polar; ring
private theorem polar_total {q r a :Shape} {b:ℕ}
    (hb:q.b≤b) (hr :r.t≤ r.j) (ha :a.t≤a.j) :
    polar q r a≤polar ⟨b,q.j,q.t⟩ r a := by
  have h:0≤((b:ℚ) - q.b)*(U r*V a+U a*V r) :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hb)) (add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast ha)))
      (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hr))))
  have he :polar ⟨b,q.j,q.t⟩ r a - polar q r a =
      ((b:ℚ) - q.b)*(U r*V a+U a*V r) := by unfold polar; ring
  linarith only [h,he]
private theorem polar_mono {p q r a :Shape} (h:aO q p) (hr :bF r) (ha :bF a) :
    polar q r a≤polar p r a := by
  let B:=2*(U r*V a+U a*V r)
  let J:=U r*(2*((a.b:ℚ)-a.j)+U a)+U a*(2*((r.b:ℚ) - r.j)+U r)
  let T:=((r.j:ℚ) - 2*U r)*W a+((a.j:ℚ) - 2*U a)*W r
  have hrb: (r.j:ℚ)≤ r.b:= by exact_mod_cast hr.1
  have hab: (a.j:ℚ)≤a.b:= by exact_mod_cast ha.1
  have hrt:2*U r≤(r.j:ℚ) := by exact_mod_cast hr.2
  have hat :2*U a≤(a.j:ℚ) := by exact_mod_cast ha.2
  have hvR:0≤V r := by linarith [zqJ (α:=ℚ) r.t]
  have hvA:0≤V a := by linarith [zqJ (α:=ℚ) a.t]
  have hwR:0≤W r := by linarith [zqJ (α:=ℚ) r.b]
  have hwA:0≤W a := by linarith [zqJ (α:=ℚ) a.b]
  have hB:0≤B:= by dsimp only [B]; positivity
  have hJ:0≤J:= by
    dsimp only [J]
    exact add_nonneg
      (mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hab)) (by positivity)))
      (mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hrb)) (by positivity)))
  have hT:0≤T:=add_nonneg (mul_nonneg (sub_nonneg.mpr hrt) hwA) (mul_nonneg (sub_nonneg.mpr hat) hwR)
  have he :2*(polar p r a - polar q r a) =
      ((p.b:ℚ) - q.b)*B+((p.j:ℚ) - q.j)*J+(U p-U q)*T:= by
    unfold polar B J T
    ring
  have h₁:=mul_nonneg (sub_nonneg.mpr (by exact_mod_cast h.1 : (q.b:ℚ)≤p.b)) hB
  have h₂:=mul_nonneg (sub_nonneg.mpr (by exact_mod_cast h.2.1 : (q.j:ℚ)≤p.j)) hJ
  have h₃:=mul_nonneg (sub_nonneg.mpr (by exact_mod_cast h.2.2 :U q≤U p)) hT
  linarith only [he,h₁,h₂,h₃]
private theorem polar_diag {p a :Shape} (hp:bF p) (ha :bF a) :
    (Wc p p a :ℚ)=polar p p a := by
  have hb (u:Shape) (hu:bF u) :u.j≤2*u.b:= by have :=hu.1; omega
  have ht (u:Shape) (hu:bF u) :u.t≤u.j:= by have :=hu.2; omega
  unfold Wc
  have he :amU p p a+amU p a p+amU p p a +
      amU p a p+amU a p p+amU a p p =
        (amU p p a+amU p a p+amU a p p)*2 := by omega
  rw [he,Nat.mul_div_cancel _ (by decide :0<2)]
  unfold polar amU
  push_cast [zjK (hb p hp),zjK (hb a ha),zjK (ht p hp),zjK (ht a ha)]
  ring
theorem cIp (p a q r :Shape) (hp:bF p) (ha :bF a)
    (hq:aO q p) (hr :aO r p) (hqj:2*q.t≤q.j) (hrj:2*r.t≤ r.j) :
    ∃ (d:Shape) (c:ℚ),∀ n:ℕ,
      let x :=(a.scale (2*n)).plus d
      (lattice ((x.plus q).plus r) :ℚ)+lattice x ≤
        (lattice (x.plus q) :ℚ)+lattice (x.plus r)+2*(Wc p p a :ℚ)*n+c:= by
  let d:Shape :=⟨2*p.j,0,0⟩
  let r' : Shape :=⟨p.b,r.j,r.t⟩
  have hr' : bF r' := ⟨hr.2.1.trans hp.1,hrj⟩
  have hm:polar q r a≤(Wc p p a :ℚ) := calc
    _=polar r q a :=btK _ _ _
    _≤polar r' q a :=polar_total hr.1 (by omega) (by have :=ha.2; omega)
    _=polar q r' a :=btK _ _ _
    _≤polar p r' a :=polar_mono hq hr' ha
    _=polar r' p a :=btK _ _ _
    _≤polar p p a :=polar_mono ⟨le_rfl,hr.2⟩ hp ha
    _ = _:=(polar_diag hp ha).symm
  let c:=count ((d.plus q).plus r)+count d - count (d.plus q) - count (d.plus r)
  refine ⟨d,c,?_⟩
  intro n x
  have hb:=zBI (2*n) ha.1
  have ht:=zBI (2*n) ha.2
  have ht' : 2*(2*n*a.t)≤2*n*a.j:= by simpa only [Nat.mul_left_comm] using ht
  have hq' := hq.2.1
  have hrle :=hr.2.1
  have hx :bF x := by
    change (2*n*a.j+0≤2*n*a.b+2*p.j) ∧
      2*(2*n*a.t+0)≤2*n*a.j+0
    omega
  have hxq:bF (x.plus q) := by
    change (2*n*a.j+0+q.j≤2*n*a.b+2*p.j+q.b) ∧
      2*(2*n*a.t+0+q.t)≤2*n*a.j+0+q.j
    omega
  have hxr :bF (x.plus r) := by
    change (2*n*a.j+0+r.j≤2*n*a.b+2*p.j+r.b) ∧
      2*(2*n*a.t+0+r.t)≤2*n*a.j+0+r.j
    omega
  have hxqr :bF ((x.plus q).plus r) := by
    change (2*n*a.j+0+q.j+r.j≤2*n*a.b+2*p.j+q.b+r.b) ∧
      2*(2*n*a.t+0+q.t+r.t)≤2*n*a.j+0+q.j+r.j
    omega
  have he :count ((x.plus q).plus r)+count x - count (x.plus q) - count (x.plus r) =
      2*polar q r a*n+c:= by
    dsimp [x,c,count,polar,U,V,W,Shape.plus,Shape.scale,d]
    push_cast
    ring
  rw [lattice_formula _ hxqr,lattice_formula _ hx,lattice_formula _ hxq,lattice_formula _ hxr]
  have hMul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℚ)≤2))
    (Nat.cast_nonneg (α:=ℚ) n)
  linarith only [he,hMul]
end
end qXuDJRd
end
section
set_option autoImplicit true
namespace qXuDJRd
noncomputable section
open dN (GeoField GeoJets)
open Dr (dimension AN)
open WI (b2k aIs)
open bar (a4G)
open MvPolynomial Finset
open private gMd from ProximityPrize.SubmissionLower.J
variable {σ:Type} [Finite σ]
private abbrev coeff (φ:z3y σ GeoField →ₐ[GeoField] GeoJets) (I:znc GeoJets) :=
  (affineHilbertPolynomial (I.comap φ.toRingHom)).coeff 2
private theorem cGf (φ:z3y σ GeoField →ₐ[GeoField] GeoJets)
    (hφ:zpX φ) (I:znc GeoJets) (hd:dimension I≤2) :
    0≤ coeff φ I :=
  Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
    ((natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ I).trans_le hd)
    (eventually_eval_affineHilbertPolynomial_nonneg _)
private theorem coeff_step (φ:z3y σ GeoField →ₐ[GeoField] GeoJets)
    (hφ:zpX φ) (I:znc GeoJets) (hd:dimension I≤2) (g:GeoJets) :
    coeff φ I=coeff φ (I ⊔ zye {g})+coeff φ (I.colon {g}) := by
  obtain ⟨G,rfl⟩:=hφ g
  have hcut: (I ⊔ zye {φ G}).comap φ.toRingHom =
      I.comap φ.toRingHom ⊔ zye {G} := by
    let ψ:=φ.toRingHom
    have hm: (I.comap ψ ⊔ zye {G}).map ψ=I ⊔ zye {φ G} := by
      rw [Ideal.map_sup,Ideal.map_comap_of_surjective ψ hφ,Ideal.map_span,Set.image_singleton]
      rfl
    change (I ⊔ zye {φ G}).comap ψ= _
    rw [← hm,Ideal.comap_map_of_surjective ψ hφ]
    exact sup_eq_left.mpr ((Ideal.comap_mono (f :=ψ) bot_le :
      (⊥ : znc GeoJets).comap ψ≤I.comap ψ).trans le_sup_left)
  have hann (x :z3y σ GeoField) :
      x*G∈I.comap φ.toRingHom↔x∈(I.colon {φ G}).comap φ.toRingHom:= by
    change φ (x*G)∈I↔φ x∈I.colon {φ G}
    rw [map_mul,Submodule.mem_colon_singleton,smul_eq_mul]
  unfold coeff
  rw [hcut]
  exact a4G hann
    ((natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ I).trans_le hd)
theorem cycle_le (φ:z3y σ GeoField →ₐ[GeoField] GeoJets)
    (hφ:zpX φ) (J:znc GeoJets) (hd:dimension J≤2)
    (S:Finset (znc GeoJets)) (hS : ∀ P∈S,J.IsMinimalPrime P) :
    ∑ P∈S,(AN J P:ℚ)*coeff φ P≤ coeff φ J:= by
  classical
  suffices h : ∀ I:znc GeoJets,J≤I →
      ∑ P∈S,(AN I P:ℚ)*coeff φ P≤ coeff φ I from h J le_rfl
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α:=znc GeoJets)) with
  | h I ih =>
    intro hJI
    by_cases hI:I = ⊤
    · subst I
      refine le_of_eq ?_
      simp only [coeff,Ideal.comap_top,affineHilbertPolynomial_top,Polynomial.coeff_zero]
      exact sum_eq_zero fun P hP=> by
        have hp:=(hS P hP).isPrime
        have hz :=aIs (I := ⊤) hp (by simpa using hp.ne_top)
        simp [AN,hp,hz]
    obtain ⟨g,hg,hprime⟩:=b2k I hI
    let A:=I.colon {g}
    let B:=I ⊔ zye {g}
    have hIB:I<B:=lt_of_le_not_ge le_sup_left
      fun h=>hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)))
    have hdim:=(natDegree_affineHilbertPolynomial_le_of_le hJI).trans hd
    rw [coeff_step φ hφ I hdim g]
    calc
      _=(∑ P∈S,(AN B P:ℚ)*coeff φ P)+(if A∈S then coeff φ A else 0) := by
        rw [← sum_ite_eq' S A (fun P=>coeff φ P),← sum_add_distrib]
        refine sum_congr rfl fun P hP => ?_
        rw [gMd hJI (hS P hP) g hprime,add_mul,ite_mul,one_mul,zero_mul]
      _≤_:=add_le_add (ih B hIB (hJI.trans hIB.le)) (by
        split_ifs
        · rfl
        · exact cGf φ hφ A
            ((natDegree_affineHilbertPolynomial_le_of_le Ideal.le_colon).trans hdim))
end
end qXuDJRd
end
section
set_option autoImplicit true
namespace qbVMAwc
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
local notation "q!" p "," n "," s "," a "," m "," zs "," hs =>
  reject (cut:=p) (len:=n) (Fy :=s) (adj:=a)
    (value :=m) zs hs rfl rfl rfl (by decide)
local notation "r!" h "," t=>transfer (by decide) t (by decide) (by decide) h
local notation "e" => rfl
local notation "z" => True.intro
private theorem r1 :Cut 2 4 21 53:=q! 0,112,70,3,0x160b89,[
    0xe9898,0x68d45,0xe5ac],⟨e,e,e,z⟩
private theorem r2 :Cut 5 4 21 56:=q! 0,114,70,3,0x161454,[
    0xdbcf0,0x77731,0xe033],⟨e,e,e,z⟩
private theorem r3:Cut 8 4 16 56:=q! 8,129,0,1,0x1614dc,[
    0x25f92,0x24356,0x7ea22,0x62b22,0x2bffd,0x9522,
    0x791],⟨e,e,e,e,e,e,e,z⟩
private theorem r4 :Cut 9 4 16 58:=q! 64,131,48,1,0x161742,[
    0x25ee8,0x23e43,0x21eeb,0x200d9,0x1e403,0x1c863,
    0x1adef,0x194a0,0x17c6e,0x15b0c,0x11191,0x21ce3,
    0x654f,33],⟨e,e,e,e,e,e,e,e,e,e,e,e,e,e,z⟩
private theorem r5:Cut 10 4 16 59:=q! 8,131,0,1,0x1615e5,[
    0x25e3e,0x23fe0,0x7ca81,0x60bfd,0x2ee3f,0xa864,
    0xaa6],⟨e,e,e,e,e,e,e,z⟩
private theorem r6:Cut 11 4 16 60:=q! 0,132,96,2,0x1617f8,[
    0x8bed7,0x99eb2,0x2f653,0xc41c],⟨e,e,e,e,z⟩
private theorem r7:Cut 12 4 16 61 :=q! 0,133,96,3,0x1615c0,[
    0x10b9f5,0x48360,0xd86b],⟨e,e,e,z⟩
private theorem r8:Cut 13 4 16 64 :=q! 0,135,48,1,0x160e04,[
    0x8ad75,0x6a299,0x4bafe,0x1b781,0x4b77],⟨e,e,e,e,e,z⟩
private theorem r9:Cut 15 4 16 68:=q! 0,139,102,2,0x161109,[
    0x89c13,0x8dce0,0x3c553,0xd2c3],⟨e,e,e,e,z⟩
private theorem dz :Cut 17 4 16 71 :=q! 0,141,170,2,0x1609ce,[
    0x11117f,0x4f84f],⟨e,e,z⟩
private theorem dD:Cut 18 4 16 77:=q! 0,146,108,2,0x1611a0,[
    0x881ff,0x84546,0x47fc5,0xca96],⟨e,e,e,e,z⟩
private theorem dK:Cut 20 4 16 88:=q! 0,155,76,2,0x1617d4,[
    0x8709d,0x60b3f,0x42889,0x2d121,0x9cb7,0x597],⟨e,e,e,e,e,e,z⟩
private theorem e8:Cut 22 4 7 99:=q! 48,179,44,1,0x16160f,[
    0x2564a,0x227c4,0x1fbbe,0x1d223,0x1aadc,0x185d5,
    0x162fa,0x14236,0x3ed04,0x27178,0x12ef5,0x596c,
    0xd62],⟨e,e,e,e,e,e,e,e,e,e,e,e,e,z⟩
theorem lane4 (b t:ℕ) (hlo:2≤b) (hhi:b≤22) (ht:1≤t) :
    Test ⟨b,4,t⟩:= by
  interval_cases b
  · exact r! r1,ht
  · exact r! r1,ht
  · exact r! r1,ht
  · exact r! r2,ht
  · exact r! r2,ht
  · exact r! r2,ht
  · exact r! r3,ht
  · exact r! r4,ht
  · exact r! r5,ht
  · exact r! r6,ht
  · exact r! r7,ht
  · exact r! r8,ht
  · exact r! r8,ht
  · exact r! r9,ht
  · exact r! r9,ht
  · exact r! dz,ht
  · exact r! dD,ht
  · exact r! dD,ht
  · exact r! dK,ht
  · exact r! dK,ht
  · exact r! e8,ht
end qbVMAwc
end
