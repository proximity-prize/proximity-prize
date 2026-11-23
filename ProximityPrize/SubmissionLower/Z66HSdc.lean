import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.ZIrsLvc
import ProximityPrize.SubmissionLower.ZLECmAc
set_option Elab.async false
set_option autoImplicit true
namespace qbRvrcc
noncomputable section
open Polynomial Finset P6_6 P6_6_7 P6_6_7_3
open aR (Shape af aO shape extend embed Dd)
open dN (GeoJets An Ch bC separant)
open BO (pN Ue)
open aKp (bDo rV cZO)
open wH (qg)
open lB (bF yy abr Tn)
private theorem bYY:aKp.c2 :=
  as4.of_children bRo.proof bjz.proof
private theorem bYX {D:Ideal GeoJets} (hD:D.IsPrime)
    (hdim:ringKrullDim (GeoJets ⧸ D)=1) {p:Shape} (hp:aO ⟨1,3,1⟩ p)
    {U:GeoJets} (hU:yy U p) (hproper :U∉D)
    {s :P6.K→P6.K[X]} {Γ:Finset P6.K} (hinj:Set.InjOn s (Γ:Set P6.K))
    (hmarks : ∀ γ∈Γ,D ≤Ch (extend (s γ))∧An (extend (s γ)) U=0) :
    6*Γ.card≤pN D (p.scale 6) := by
  classical
  let point (γ:P6.K) :=rV (extend (s γ))
  have hinj' : Set.InjOn point (Γ:Set P6.K) := by
    intro γ hγ η hη he
    exact hinj hγ hη (Polynomial.map_injective embed embed.injective (cZO he))
  have hc:=bYY D p hD hdim hp U hU hproper (Γ.image point) (by
    intro x hx
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
    exact hmarks γ hγ)
  rwa [Finset.card_image_of_injOn hinj'] at hc
private theorem iU {C:Context} {R:af 4} {cs :ChartCase C.n} :
    bF (chartBody C R cs) := by
  cases cs with
  | own _=>exact Tn R
  | union _ =>
    refine ⟨le_max_right _ _,?_⟩
    let q:=rawResidual m6 C.v
    let j:=min q.j (3*q.b)
    change 3*min q.t (min q.b (j/3))≤j
    exact (Nat.mul_le_mul_left 3 ((min_le_right _ _).trans (min_le_right _ _))).trans
      (Nat.mul_div_le _ _)
private theorem taylor_simplex {L:ℕ} (h4 :4≤L) (p:Shape) :
    aO ⟨1,3,1⟩ (weightedChart L p) := by
  unfold weightedChart
  split
  · refine ⟨(Nat.le_add_right _ _).trans (le_max_left _ _),Nat.le_add_right _ _,?_⟩
    change 1≤ min _ _
    exact le_min (by omega) (by omega)
  · refine ⟨(Nat.le_add_right _ _).trans (le_max_left _ _),Nat.le_add_left _ _,?_⟩
    change 1≤ min _ _
    exact le_min (by omega) (by omega)
private theorem uq {gap err regular bad d c b:ℕ}
    (hr :gap*regular≤err*d+gap) (hd:6*d≤ c) (hf :6*bad≤b) (hb:6≤b) :
    6*gap*(regular+bad)≤err*c+2*gap*b:= by
  calc
    _=6*(gap*regular)+gap*(6*bad) := by ring
    _≤6*(err*d+gap)+gap*b :=
      Nat.add_le_add (Nat.mul_le_mul_left 6 hr) (Nat.mul_le_mul_left gap hf)
    _=err*(6*d)+(gap*6+gap*b) := by ring
    _≤err*c+(gap*b+gap*b) :=
      Nat.add_le_add (Nat.mul_le_mul_left err hd) (Nat.add_le_add_right (Nat.mul_le_mul_left gap hb) _)
    _ = _:= by ring
theorem proof :P6_6_7_3.c4 := by
  classical
  intro C R G ell cs h Γ D hΓ hm hD hdim
  by_cases hne :Γ.Nonempty
  swap
  · have he :=Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]
  obtain ⟨γ₀,h₀⟩:=hne
  let p:=chartBody C R cs
  have hp:bF p:=iU
  have hp0:0<p.t:= by
    have hs : (chartIndices C cs).Nonempty := by
      cases cs with
      | union _ =>
        obtain ⟨k,hk,_⟩:=C.marks.Eh γ₀ (hΓ h₀)
        exact ⟨k,hk⟩
      | own k=>exact ⟨k,Finset.mem_singleton_self _⟩
    obtain ⟨k,hk⟩:=hs
    exact (C.marks.factors k (charter h hk)).2.1.trans_le ((bW2 h).2 k hk).2.2
  have hu:aO ⟨1,3,1⟩ p:= by
    obtain ⟨hb,hj⟩:=hp
    change 1≤p.b∧3≤p.j∧1≤p.t
    omega
  have hmsg :=C.messages.mono hΓ
  by_cases hprod:bC (GW C cs)∈D
  swap
  · have hc:=bYX hD hdim hu (abr (bW2 h).1) hprod hmsg.distinct
        (fun γ hγ=>⟨(hm γ hγ).2,
          Ue.mpr (chart_product_vanishes h (hΓ hγ) (hm γ hγ).1)⟩)
    calc
      _=mV*(6*Γ.card) := by ring
      _≤ mV*pN D (p.scale 6) :=Nat.mul_le_mul_left _ hc
      _≤ curveCharge p D:=(Nat.mul_le_mul_right _ (by omega)).trans (Nat.le_add_left _ _)
  change MvPolynomial.map dN.j8 (∏ i∈chartIndices C cs,C.f i)∈D at hprod
  rw [map_prod] at hprod
  let:=hD
  obtain ⟨k,hk,hfk⟩:=Ideal.IsPrime.prod_mem_iff.mp hprod
  have hf :=C.marks.factors k (charter h hk)
  have honor :Dd (C.f k) (extend (C.s γ₀)) :=
    ⟨Ue.mp ((hm γ₀ h₀).2 hfk),C.marks.leading γ₀ (hΓ h₀) k (charter h hk)⟩
  obtain ⟨r,hr,hsep⟩:=bAm.bmF
    (hf.2.2.1.2.2.trans_lt (by decide :16<K1.p)) honor hfk (hm γ₀ h₀).2
  let g:=(separant^[r]) (C.f k)
  have hfbox :=(bW2 h).2 k hk
  have hanchor :aO (shape (C.f k)).iU p :=
    ⟨max_le hfbox.1 (hfbox.2.1.trans hp.1),hfbox.2⟩
  have hg:aO (shape g) p :=
    cDD (akM.bc7 (C.f k) r) hanchor
  let A:=Γ.filter fun γ=>qg g (extend (C.s γ))
  let B:=Γ.filter fun γ => ¬ qg g (extend (C.s γ))
  have hA:A⊆Γ:=filter_subset _ _
  have hB:B⊆Γ:=filter_subset _ _
  have hs :Γ.card=A.card+B.card:=(card_filter_add_card_filter_not _).symm
  have hb:=bYX hD hdim hu (abr (cDD hsep hanchor)) hr.2.2
    (hmsg.distinct.mono hB) (fun γ hγ=>⟨(hm γ (hB hγ)).2,
      Ue.mpr (not_ne_iff.mp (mem_filter.mp hγ).2)⟩)
  obtain ⟨x,U,hx,hU,hproper,hval⟩:=bDo hD hdim
  have he :6≤pN D (p.scale 6) := by
    have hfit :yy U p :=
      ⟨hU.1.trans hu.1,hU.2.1.trans hu.2.1,hU.2.2.trans hu.2.2⟩
    simpa using bYY D p hD hdim hu U hfit hproper {x} (by
      intro y hy
      rw [Finset.mem_singleton.mp hy]
      exact ⟨hx,hval⟩)
  let L:=bf
  have h4 :4≤L:= by decide
  have hL:L≤K1.p:= by decide
  let degree :=pN D ((weightedChart L p).scale 6)
  have ha :mV*A.card≤P6.t*(degree/6)+mV:= by
    apply P6_6_5.bv5 (hmsg.mono hA)
    intro i hmiss
    obtain ⟨V,hV,hvalue⟩:=d40 h4 hL hg hp hp0 (P6.node i) (C.w i)
    have on (γ:P6.K) (hγ:γ∈A) :
        An (extend (C.s γ)) V=0↔(C.s γ).eval (P6.node i)=C.w i :=
      hvalue _ (Nat.lt_succ_of_le (hmsg.degree γ (hA hγ)))
        (Ue.mp ((hm γ (hA hγ)).2 (hr.2.1 r le_rfl))) (mem_filter.mp hγ).2
    have hproperV:V∉D:= by
      obtain ⟨γ,hγ,hmiss⟩:=hmiss
      exact fun hv=>hmiss ((on γ hγ).mp ((hm γ (hA hγ)).2 hv))
    let F:=A.filter fun γ=>(C.s γ).eval (P6.node i)=C.w i
    have hF:F⊆Γ:=(filter_subset _ _).trans hA
    have hc:=bYX hD hdim (taylor_simplex h4 p) hV hproperV
      (hmsg.distinct.mono hF) (fun γ hγ=>⟨(hm γ (hF hγ)).2,
        (on γ (mem_filter.mp hγ).1).mpr (mem_filter.mp hγ).2⟩)
    exact (Nat.le_div_iff_mul_le (by decide :0<6)).mpr (by simpa only [Nat.mul_comm] using hc)
  rw [hs]
  exact uq ha (Nat.mul_div_le _ _) hb he
end
end qbRvrcc
