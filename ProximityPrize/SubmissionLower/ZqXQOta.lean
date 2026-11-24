import ProximityPrize.SubmissionLower.Z3gZttb
import ProximityPrize.SubmissionLower.Z3vxfLe
set_option Elab.async false
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem xL6ff0:total 2585 4=0xc94eeeda660:=r! 0x326e7907870,r! 0x325c9fb3390,r! 0x324ad48ae70,r! 0x32390194bf0,rfl
private theorem xL6ff1:total 2589 4=0xc8324c9e2c0:=r! 0x32273e1aa20,r! 0x32157025c80,r! 0x3203b2f4350,r! 0x31f1eb698d0,rfl
private theorem xL6ff2:total 2593 4=0xc7165f5fb70:=r! 0x31e02a00d50,r! 0x31ce742ba50,r! 0x31bcb860b30,r! 0x31ab08d28a0,rfl
private theorem r1:total 2585 12=0x258979ad8490:=total_append xL6ff0 (total_append xL6ff1 xL6ff2)
private theorem xL6ff3:total 2597 4=0xc5fb52d42f0:=r! 0x319953b4f90,r! 0x3187aa32910,r! 0x3175fb80040,r! 0x3164596ca10,rfl
private theorem xL6ff4:total 2601 4=0xc4e1116a470:=r! 0x3152b0095c0,r! 0x3141143d840,r! 0x312f7153830,r! 0x311ddbcfe40,rfl
private theorem xL6ff5:total 2605 4=0xc3c79d557e0:=r! 0x310c3fe1d40,r! 0x30fab025140,r! 0x30e91aa9c10,r! 0x30d792a4d50,rfl
private theorem r2:total 2597 12=0x24ea40193f40:=total_append xL6ff3 (total_append xL6ff4 xL6ff5)
private theorem xL6ff6:total 2609 4=0xc2aef46c270:=r! 0x30c60239ac0,r! 0x30b4807d350,r! 0x30a2f6943b0,r! 0x30917b210b0,rfl
private theorem xL6ff7:total 2613 4=0xc197109fc30:=r! 0x307ff87ed50,r! 0x306e8291200,r! 0x305d0665c40,r! 0x304b8f2a0a0,rfl
private theorem xL6ff8:total 2617 3=0x907a1a225e0:=r! 0x303a211d150,r! 0x3028b05e020,r! 0x301748a7470,rfl
private theorem r3:total 2609 11=0x214c01f2e480:=total_append xL6ff6 (total_append xL6ff7 xL6ff8)
theorem aec:total 2585 35=0x6bbfbbb9a850 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
section
set_option autoImplicit true
namespace q90NBie
noncomputable section
open P6_6 P6_6_7 Finset
open P6 (K)
open aR (af Shape extend)
open dN (GeoJets Ch)
open BO (aYz)
def c1 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (A:SurfaceAssignment C R G) (F:Cuts A ell) (h:Shape),
      h=chartBody C R cs∨h=weightedChart bf (chartBody C R cs) →
      32*(mass F (fun _ D =>sectionCost h D) :ℤ) ≤
        6*wP (firstSlot C R cs) (cutterBody C ell) (commonBody C R ell cs) h
def c2 :Prop :=
  ∀ (C:Context) R ell cs,CaseGuard C R ell cs →
    ∀ (D:Ideal GeoJets),aYz R D →
      ∀ L:Finset K,L⊆C.Δ→(∀ γ∈L,D ≤Ch (extend (C.s γ))) →
        let p:=chartBody C R cs
        6*mV*L.card ≤
          P6.t*sectionCost (weightedChart bf p) D + 2*mV*sectionCost p D
def c3:Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs→3≤ell →
    ∀ (A:SurfaceAssignment C R G) (F:Cuts A ell),SecondCuts F →
      let b:=commonBody C R ell cs
      32*(mass F (fun z D =>remainingOrder F z D *(aHl F z D).card) :ℤ) ≤
        wP (firstSlot C R cs) (cutterBody C ell) b b
variable {C:Context} {R G:af 4} {ell:ℕ} {cs :ChartCase C.n}
variable {A:SurfaceAssignment C R G} {z D:Ideal GeoJets}
private theorem sum_allocated (F:Cuts A ell) :
    lowGeneric C R G ell A = ∑ z∈uG A ell,∑ D∈qv F z,
      genericOrder R z*(aHl F z D).card:= by
  classical
  calc
    _ = ∑ γ∈lowMarks C R G ell A,genericOrder R (A.aI γ) := by
      rw [lowGeneric,lowMarks,sum_filter]
      apply sum_congr rfl
      intro γ _
      by_cases ho:0<ord C R γ <;> by_cases hj:genericOrder G (A.aI γ)<ell <;>
        simp [surfaceOrder,ho,hj]
    _ = ∑ z∈uG A ell,∑ γ∈surfaceMarks A ell z,genericOrder R (A.aI γ) :=
      (sum_fiberwise_of_maps_to (fun γ hγ=>mem_image_of_mem A.aI hγ) _).symm
    _ = _:= by
      apply sum_congr rfl
      intro z _
      calc
        _ = ∑ γ∈surfaceMarks A ell z,genericOrder R z :=
          sum_congr rfl (fun γ hγ=> by rw [(mem_filter.mp hγ).2])
        _ = ∑ D∈qv F z,∑ γ∈aHl F z D,genericOrder R z :=
          (sum_fiberwise_of_maps_to (fun γ hγ=>mem_image_of_mem F.curve hγ) _).symm
        _ = _:= by simp [Nat.mul_comm]
private theorem add_le_product {a b:ℕ} (ha :0<a) (hb:0<b) :a+b≤a*b+1 := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  nlinarith only [Nat.zero_le (a*b)]
private theorem discount {j e ell:ℕ} (hj:0<j) (he :0<e) (hl:j<ell) :
    if ell - j≤e then max 1 (ell - 2)≤j*e
    else max 1 (ell - 2)≤j*e*(ell - j-e) := by
  have hje :=Nat.mul_pos hj he
  split_ifs with hk
  · have :=add_le_product hj he
    omega
  · let m:=ell - j-e
    have hm:0< m:= by dsimp [m]; omega
    have h₁:=add_le_product he hm
    have h₂:=add_le_product hj (Nat.mul_pos he hm)
    have hp:=Nat.mul_pos hje hm
    rw [Nat.mul_assoc] at hp ⊢
    change max 1 (ell - 2)≤j*(e*m)
    have heq :e+m=ell - j:= by dsimp [m]; omega
    omega
private abbrev pointMass (F:Cuts A ell) :ℕ :=
  mass F (fun z D =>remainingOrder F z D *(aHl F z D).card)
private theorem account (hinc:c2) (h:PairInput C R G ell cs) (F:Cuts A ell) :
    let p:=chartBody C R cs
    6*mV*max 1 (ell - 2)*lowGeneric C R G ell A ≤
      P6.t*mass F (fun _ D =>sectionCost (weightedChart bf p) D) +
        2*mV*mass F (fun _ D =>sectionCost p D)+6*mV*pointMass F:= by
  classical
  intro p
  rw [sum_allocated F]
  simp only [mass,mul_sum,← sum_add_distrib]
  refine sum_le_sum (fun z hZ=>sum_le_sum (fun D hD => ?_))
  let i:=genericOrder R z
  let j:=genericOrder G z
  let e :=curveOrder F z D
  let m:=remainingOrder F z D
  let n:=(aHl F z D).card
  let a :=sectionCost (weightedChart bf p) D
  let b:=sectionCost p D
  let k :=max 1 (ell - 2)
  let d:=6*mV
  have ⟨hj,he⟩:=orders_pos h hZ hD
  have hd:=discount hj he (surface_spec hZ).2
  change d*k*(i*n)≤P6.t*(i*j*e*a)+2*mV*(i*j*e*b)+d*(i*j*e*(m*n))
  calc
    _=i*(k*(d*n)) := by ring
    _≤ i*((j*e)*(P6.t*a+2*mV*b+d*(m*n))) := by
      apply Nat.mul_le_mul_left
      by_cases hb:ell - j≤e
      · rw [ite_eq_left hb] at hd
        have hc:d*n≤P6.t*a+2*mV*b:= by
          apply hinc C R ell cs h.guard D (curve_on h hZ hD) (aHl F z D)
          · exact fun γ hγ=>(low_mark (curve_mark hγ).1).1
          · intro γ hγ
            obtain ⟨hl,_,heq⟩:=curve_mark hγ
            simpa only [heq] using (F.valid γ hl).2
        exact (Nat.mul_le_mul hd hc).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
      · rw [ite_eq_right hb] at hd
        calc
          k*(d*n)≤(j*e*m)*(d*n) :=Nat.mul_le_mul_right _ hd
          _=(j*e)*(d*(m*n)) := by ring
          _≤_:=Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
    _ = _:= by ring
private theorem no_points (h:PairInput C R G ell cs) (F:Cuts A ell) (hl:ell<3) :
    pointMass F=0:= by
  unfold pointMass mass
  refine sum_eq_zero (fun z hZ=>sum_eq_zero (fun D hD => ?_))
  have ⟨hj,he⟩:=orders_pos h hZ hD
  have hm:remainingOrder F z D =0:= by
    change ell - genericOrder G z - curveOrder F z D =0
    omega
  simp only [hm,zero_mul,mul_zero]
private theorem finish {x u y z c pt:ℤ} {t d:ℕ}
    (h:6*x≤(t:ℤ)*u+2*(d:ℤ)*y+6*(d:ℤ)*z)
    (hu:u≤6*c) (hy :y≤6*pt) :
    x≤(t:ℤ)*c+2*(d:ℤ)*pt+(d:ℤ)*z := by
  have h₁:=mul_le_mul_of_nonneg_left hu (show 0≤(t:ℤ) by positivity)
  have h₂:=mul_le_mul_of_nonneg_left hy (show 0≤2*(d:ℤ) by positivity)
  linarith only [h,h₁,h₂]
theorem of_children (h₁:c1) (h₂:c2) (h₃:c3) :P6_6_7.c2 := by
  intro C R G ell cs h A
  dsimp only
  obtain ⟨F⟩:=make_cuts h A
  let p:=chartBody C R cs
  let r :=firstSlot C R cs
  let q:=cutterBody C ell
  let b:=commonBody C R ell cs
  let H :=weightedChart bf p
  let k :=max 1 (ell - 2)
  let n:=lowGeneric C R G ell A
  let u:=mass F (fun _ D =>sectionCost H D)
  let v :=mass F (fun _ D =>sectionCost p D)
  let z :=pointMass F
  have hu:=h₁ C R G ell cs h A F H (Or.inr rfl)
  have hv :=h₁ C R G ell cs h A F p (Or.inl rfl)
  have hnat :6*mV*k*n≤P6.t*u+2*mV*v+6*mV*z :=
    account h₂ h F
  have ha :6*((feeScale :ℤ)*(k :ℤ)*n) ≤
      (P6.t:ℤ)*(32*(u:ℤ))+2*(mV:ℤ)*(32*(v :ℤ)) +
        6*(mV:ℤ)*(32*(z :ℤ)) := by
    have hm: (6:ℤ)*mV*(k :ℤ)*n ≤
        (P6.t:ℤ)*u+2*(mV:ℤ)*v+6*(mV:ℤ)*z := by
      exact_mod_cast hnat
    push_cast [feeScale]
    linarith only [hm]
  have hs : (feeScale :ℤ)*(k :ℤ)*n≤ curve32 p r q b+(mV:ℤ)*(32*(z :ℤ)) :=
    finish ha hu hv
  constructor
  · intro hl
    have hk :k=ell - 2 :=max_eq_right (by omega)
    have hb:=h₃ C R G ell cs h hl A F (second_cuts F)
    have hpt:=mul_le_mul_of_nonneg_left hb (show 0≤(mV:ℤ) by positivity)
    rw [hk,Nat.cast_sub (show 2≤ell by omega)] at hs
    exact hs.trans (add_le_add (le_refl _) hpt)
  · intro hl
    have hk :k=1 :=max_eq_left (by omega)
    have hz :z=0:=no_points h F hl
    simpa only [hk,hz,Nat.cast_one,Nat.cast_zero,mul_zero,mul_one,add_zero] using hs
end
end q90NBie
end
section
set_option autoImplicit true
namespace qduj6fa
noncomputable section
open Polynomial
open aR (ao af wU)
open dN (GeoJets bC Ch)
open agL (afc BV bft a4A)
open vS (JV)
open Dr (AN oF a9B)
theorem cut_order_le {J P:Ideal GeoJets} {f :GeoJets} {n:ℕ}
    (hJ:J.IsPrime) (hf :f∉J) (hP: (J ⊔ Ideal.span {f}).IsMinimalPrime P)
    (hn:letI:=hP.isPrime; afc P f n) :
    n≤AN (J ⊔ Ideal.span {f}) P:= by
  let:=hP.isPrime
  apply ENat.natCast_le_natCast.mp
  rw [a9B hP]
  let L:=Localization.AtPrime P
  let φ:=algebraMap GeoJets L
  let m:=IsLocalRing.maximalIdeal L
  let A:=J.map φ
  have hJP:J≤P:=le_sup_left.trans hP.le
  have hm:φ f∈m :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mpr
      (hP.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
  have hno (i:ℕ) : ¬ m^i≤A:= by
    intro h
    have hmem:φ (f^i)∈A:= by
      rw [map_pow]
      exact h (Ideal.pow_mem_pow hm i)
    change algebraMap GeoJets L (f^i)∈J.map (algebraMap GeoJets L) at hmem
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl L] at hmem
    obtain ⟨u,hu,huf⟩:=hmem
    exact hf (hJ.mem_of_pow_mem i
      ((hJ.mem_or_mem huf).resolve_left (fun huJ=>hu (hJP huJ))))
  let I (i:ℕ) :Ideal L:=A ⊔ m^i
  have hstep (i:ℕ) :I (i+1)<I i:= by
    refine lt_of_le_of_ne (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ i)) _) ?_
    intro he
    apply hno i
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I:=m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · change m^i≤A ⊔ m•m^i
      rw [smul_eq_mul,← pow_succ']
      change m^i≤I (i+1)
      rw [he]
      exact le_sup_right
  have hcoheight (i:ℕ) : (i:ℕ∞)≤Order.coheight (I i:Submodule L L) := by
    induction i with
    | zero=>simp
    | succ i ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans
          (Order.coheight_add_one_le (show (I (i+1) :Submodule L L)<I i from hstep i))
  change (n:ℕ∞)≤Module.length L (L ⧸ (J ⊔ Ideal.span {f}).map φ)
  rw [Ideal.map_sup,Ideal.map_span,Set.image_singleton,Module.length_quotient]
  apply (hcoheight n).trans
  apply Order.coheight_anti
  exact sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_right hn))
theorem mark_vanishesTo {V:af 4} {S:ao[X]} {d:ℕ}
    (h:wU V S d) :
    letI:=Dr.c4m (JV S)
    afc (oF (JV S)) (bC V) d:= by
  let:=Dr.c4m (JV S)
  apply bRn.gK5
  intro a ha
  change BV a (MvPolynomial.map dN.j8 V)∈Ch S
  rw [← bft]
  exact BO.Ue.mpr (a4A ha h)
end
end qduj6fa
end
