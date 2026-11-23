import ProximityPrize.SubmissionLower.Zlhpfyd
import ProximityPrize.SubmissionLower.ZqXQOta
import ProximityPrize.SubmissionLower.ZV6zyia
set_option Elab.async false
set_option autoImplicit true
namespace qduj6fa
noncomputable section
open P6_6 P6_6_7 q90NBie
open Finset
open aR (af Shape shape aO extend)
open dN (GeoJets bC Ch kC AX)
open BO (bfW Ue)
open agL (aD7)
open vS (JV bTT)
open Dr (dimension tW AN oF bge btI
  aPQ aCR aQG a9B aIT aIc bEk)
open lB (bF amo)
open private eMr from ProximityPrize.SubmissionLower.Zlhpfyd
def c1 :Prop :=
  ∀ (J:Ideal GeoJets) (V:af 4) (p:Shape) (boxes :List Shape),
    IsLeftRegular (Ideal.Quotient.mk J (bC V)) →
    aO (shape V) p→bF p →
    boxes.length≤2→(∀ s∈boxes,bF s)→dimension J≤boxes.length+1 →
    ∀ S:Finset (Ideal GeoJets),(∀ D∈S,(AX J V).IsMinimalPrime D) →
      (∑ D∈S,(AN (AX J V) D:ℚ)*tW D boxes) ≤
        tW J (p :: boxes)
def c2 :Prop :=
  ∀ (R:af 4) (r q b:Shape),
    R≠0→aO (shape R) r→bF q→bF b →
    32*tW (Ideal.span {bC R}) [q,b,b] ≤
      (wP r q b b:ℚ)
private theorem btG (h1 :c1) (C:Context) {D:Ideal GeoJets} {b:Shape}
    (hD:D.IsPrime) (hdim:dimension D =1) (hb:bF b) {V:af 4}
    (hV:bC V∉D) (hbox :aO (shape V) b) {d:ℕ} (hd:0<d)
    (L:Finset P6.K) (hL:L⊆C.Δ)
    (hmark : ∀ γ∈L,D ≤Ch (extend (C.s γ))∧aR.wU V (extend (C.s γ)) d) :
    (d:ℚ)*L.card≤tW D [b] := by
  classical
  let x (γ:P6.K) :=JV (extend (C.s γ))
  let J:=AX D V
  have hreg:=aPQ hD hV
  have hJ:dimension J=0:= by
    have hh:=aCR hreg
    change dimension J≤dimension D - 1 at hh
    omega
  have hmin (γ) (hγ:γ∈L) :J.IsMinimalPrime (oF (x γ)) := by
    obtain ⟨hDγ,hVγ⟩:=hmark γ hγ
    apply eMr hJ
    exact sup_le hDγ ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ue.mpr (bfW hd hVγ)))
  have hinj:Set.InjOn (fun γ=>oF (x γ)) (L:Set P6.K) := by
    intro γ hγ δ hδ heq
    exact C.messages.distinct (hL hγ) (hL hδ)
      (Polynomial.map_injective aR.embed aR.embed.injective
        (bTT (btI heq)))
  calc
    _ = ∑ _γ∈L,(d:ℚ) := by simp [mul_comm]
    _ ≤ ∑ γ∈L,(AN J (oF (x γ)) :ℚ)*tW (oF (x γ)) [] := by
      refine sum_le_sum fun γ hγ => ?_
      rw [bge,mul_one]
      exact_mod_cast cut_order_le hD hV (hmin γ hγ) (mark_vanishesTo (hmark γ hγ).2)
    _ = ∑ P∈L.image (fun γ=>oF (x γ)),(AN J P:ℚ)*tW P [] :=
      (sum_image (f := fun P=>(AN J P:ℚ)*tW P []) hinj).symm
    _≤_:=h1 D V b [] hreg hbox hb (by simp) (by simp) (by simpa using hdim.le) _ (by
      intro P hP
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hP
      exact hmin γ hγ)
private theorem surface_bound (h1 :c1) {C:Context} {R G:af 4} {ell:ℕ}
    {A:SurfaceAssignment C R G} (F:Cuts A ell) (hF:SecondCuts F)
    {z :Ideal GeoJets} (hz :z∈uG A ell) (hdim:dimension z=2)
    {b:Shape} (hb:bF b) (hqb:aO (cutterBody C ell) b) :
    (∑ D∈qv F z,
      ((curveOrder F z D *(remainingOrder F z D *(aHl F z D).card) :ℕ) :ℚ)) ≤
      tW z [b,b] := by
  classical
  let W (D:Ideal GeoJets) :=curveOrder F z D *(remainingOrder F z D *(aHl F z D).card)
  let J:=AX z (F.first z)
  let S:=(qv F z).filter (fun D =>0< remainingOrder F z D)
  have hzP:=(surface_spec hz).1.isPrime
  have hcut:=F.proper z hz
  have hbox {V:af 4} (hV:aO (shape V) (cutterBody C ell)) :aO (shape V) b :=
    ⟨hV.1.trans hqb.1,hV.2.1.trans hqb.2.1,hV.2.2.trans hqb.2.2⟩
  have hfilter : ∑ D∈S,(W D:ℚ) = ∑ D∈qv F z,(W D:ℚ) := by
    unfold S
    rw [sum_filter]
    refine sum_congr rfl fun D _ => ?_
    by_cases hm:0< remainingOrder F z D
    · exact ite_eq_left hm
    · simp [W,Nat.eq_zero_of_not_pos hm]
  calc
    _ = ∑ D∈S,(W D:ℚ) :=hfilter.symm
    _ ≤ ∑ D∈S,(AN J D:ℚ)*tW D [b] := by
      refine sum_le_sum fun D hD => ?_
      obtain ⟨hD,hm⟩:=mem_filter.mp hD
      have hDmin:=curve_spec hD
      let:=hDmin.isPrime
      have hd:=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hcut hDmin
      change dimension D + 1=dimension z at hd
      have hd' : dimension D =1 := by omega
      obtain ⟨V,hV,hVbox,hVorder⟩:=hF z hz D hD hm
      have hs :=btG h1 C hDmin.isPrime hd' hb hV (hbox hVbox) hm (aHl F z D)
        (fun _ hγ=>(low_mark (curve_mark hγ).1).1) (fun γ hγ=> by
          obtain ⟨hγ',_,heq⟩:=curve_mark hγ
          exact ⟨heq ▸ (F.valid γ hγ').2,hVorder γ hγ⟩)
      have he :=cut_order_le hzP hcut hDmin (generic_vanishesTo (F.first z) D)
      simp only [W,Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast he) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hs (by positivity))
    _≤_:=h1 z (F.first z) b [b] (aPQ hzP hcut) (hbox (F.fits z hz)) hb (by simp)
      (by simpa using hb) (by simpa using hdim.le) S (fun _ hD =>curve_spec (mem_filter.mp hD).1)
private theorem physical_chamber (v :Shape) (ell:ℕ) :bF (physicalBody v ell) := by
  let y :=rawResidual Wk (v.scale ell)
  let j:=min y.j (3*y.b)
  change j≤ max y.b j∧3*min y.t (min y.b (j/3))≤j
  have h:=(min_le_right y.t _).trans (min_le_right y.b (j/3))
  exact ⟨le_max_right _ _,by omega⟩
private theorem join_chamber {p q:Shape} (hp:bF p) (hq:bF q) :
    bF (joinBody p q) := by
  refine ⟨max_le_max hp.1 hq.1,?_⟩
  obtain h | h:=le_total p.t q.t
  · exact (show 3*max p.t q.t≤q.j by rw [max_eq_right h]; exact hq.2).trans (le_max_right _ _)
  · exact (show 3*max p.t q.t≤p.j by rw [max_eq_left h]; exact hp.2).trans (le_max_left _ _)
theorem of_children (h1 :c1) (h2 :c2) :q90NBie.c3:= by
  classical
  intro C R G ell cs hp _ A F hF
  let r :=firstSlot C R cs
  let q:=cutterBody C ell
  let b:=commonBody C R ell cs
  let J:=kC R G
  let H :Ideal GeoJets :=Ideal.span {bC R}
  have hr :aO (shape R) r := by
    cases cs
    · exact ⟨le_rfl,le_rfl,le_rfl⟩
    · exact ⟨le_max_left _ _,le_rfl,le_rfl⟩
  have hq:bF q:=physical_chamber C.v ell
  have hb:bF b:= by
    apply join_chamber _ hq
    cases cs
    · exact physical_chamber _ _
    · exact lB.Tn R
  have hqb:aO q b:=⟨le_max_right _ _,le_max_right _ _,le_max_right _ _⟩
  have hrel :=amo R G hp.factor.1 hp.proper
  have hR:bC R≠0:= fun h =>
    hp.factor.1.ne_zero (lB.aFf (h.trans (map_zero _).symm))
  have hmass : (mass F (fun z D =>remainingOrder F z D *(aHl F z D).card) :ℚ) ≤
      ∑ z∈uG A ell,(AN J z :ℚ)*tW z [b,b] := by
    unfold mass
    simp only [Nat.cast_sum]
    refine sum_le_sum fun z hz => ?_
    have hzmin:=(surface_spec hz).1
    let:=hzmin.isPrime
    have hprod:=OO.bsc (aD7 hR hrel hzmin)
      (generic_vanishesTo R z) (generic_vanishesTo G z)
    rw [← a9B hzmin] at hprod
    have hw:genericOrder R z*genericOrder G z≤AN J z :=
      ENat.natCast_le_natCast.mp hprod
    let v := ∑ D∈qv F z,((curveOrder F z D *
      (remainingOrder F z D *(aHl F z D).card) :ℕ) :ℚ)
    have hv :0≤v :=sum_nonneg fun _ _=>Nat.cast_nonneg _
    have hbound:v≤tW z [b,b] :=
      surface_bound h1 F hF hz (aQG hR hrel hzmin) hb hqb
    calc
      _=((genericOrder R z*genericOrder G z :ℕ) :ℚ)*v := by
        simp only [v,mul_sum,Nat.cast_mul,mul_assoc]
      _≤(AN J z :ℚ)*v :=mul_le_mul_of_nonneg_right (by exact_mod_cast hw) hv
      _≤_:=mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
  have hH :dimension H≤3:= by
    have hh:=aCR (aPQ (J:=(⊥ : Ideal GeoJets)) (D:=bC R)
      (by infer_instance) (by simpa using hR))
    simpa [H,bEk] using hh
  have hpair : (∑ z∈uG A ell,(AN J z :ℚ)*tW z [b,b]) ≤
      tW H [q,b,b] := by
    rw [show J=AX H G from aIc R G]
    exact h1 H G q [b,b] (aIT R G hrel) hp.H6 hq (by simp) (by simpa using hb)
      (by simpa using hH) _ (fun z hz=> by
        change (Ideal.span {bC R} ⊔ Ideal.span {bC G}).IsMinimalPrime z
        rw [← aIc]
        exact (surface_spec hz).1)
  have hfinal:=(mul_le_mul_of_nonneg_left (hmass.trans hpair) (by norm_num : (0:ℚ)≤32)).trans
    (h2 R r q b hp.factor.1.ne_zero hr hq hb)
  exact_mod_cast hfinal
end
end qduj6fa
