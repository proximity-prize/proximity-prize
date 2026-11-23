import ProximityPrize.SubmissionLower.Z3e8uLd
import ProximityPrize.SubmissionLower.Z1G66Gc
set_option Elab.async false
open _root_ renaming Finset.filter_subset→lI,Finset.mem_union_left→n5,Finset.mem_union_right→ oj,Finset.sum_const_zero→ ov,Ideal→lz,List.mem_cons_of_mem→ oy,List.mem_cons_self→ ox,Nat.add_le_add→lJ,akZ.weightedDegree→lV,gT.Ambient→c9
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1400000
namespace qIVBNpc
noncomputable section

open P5_7 (FarBand farAgreement)
open P5_7_5 (nV aqE azi aIe arC auN)
open akZ (aB5 aRJ yE ajz cN5 aHP weightedDegree cs5 c2L cfi collect bt8 caQ bKa bLw)
open cu gT pI YX XY Polynomial
open qQ (aeH)

open scoped BigOperators Classical




open private b6z dg6 from ProximityPrize.SubmissionLower.D7


private theorem eo1 {b:FarBand} (sched:aqE b)
    {P Q:Jet} (hQ:Q≠0) (hnc:aeH P Q)
    (hQc:oU Q (nV b 0).moving.shape) (T8:ℕ→Jet)
    (rows : ∀ i∈b.row.RU,T8 i≠0∧oU (T8 i) (nV b i).free.shape) :
    ∀ (is :List ℕ),(∀ i∈is,i∈b.row.RU) →
    ∀ (D:Finset Jet) (cap:Fin 3→ℕ),aRJ P D→(∀ j,ajz D j≤ cap j) →
    ∃ S:Finset (lz c9),aB5 S ∧
      (∀ k old,mass S k≤azi b k is cap old+weightedDegree old D) ∧
      ∀ z R,(∀ i∈is,∀ j a,a≤(nV b i).dI →
        rD (A5 j a (T8 i)) z R=0) →
        rD Q z R=0→(∃ f∈D,rD f z R=0) → ∃ I∈S,IZ I z R:= by
  classical
  intro is
  induction is with
  | nil =>
    intro _ D cap hD hcap
    let t:=(nV b 0).moving.shape
    have gt:=(sched.aE7 0 sched.aXU).2
    obtain ⟨S,hG,hS,hC⟩:=collect D
      (fun f k=>aHP t k f+af1 (yE f 2) (yE f 0) k)
      (fun f z R=>rD f z R=0∧rD Q z R=0)
      (dg6 hD hnc hQc gt.ode.jb gt.ode.small hQ)
    refine ⟨S,hG,?_,?_⟩
    · intro k old
      have hord: (![cap 0,cap 2,2*cap 0*cap 2,cap 2*cap 2] :Fin 4→ℕ) k =
          af1 (cap 2) (cap 0) k := by
        fin_cases k <;> try rfl
        change 2*cap 0*cap 2=2*cap 2*cap 0
        ring
      have hstep:=cs5 (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty,lV,ajz,Finset.sum_empty,
        mul_zero,ov,Nat.add_zero] at hstep
      refine (hS k).trans ?_
      simp only [Finset.sum_add_distrib,azi,hord]
      calc
        _≤_:=lJ hstep (c2L D cap hcap k)
        _ = _:= by
          simp only [lV,ajz,t]
          ac_rfl
    · intro z R _ hq ⟨f,hf,hz⟩
      exact hC f hf z R ⟨hz,hq⟩
  | cons i is ih =>
    intro his D cap hD hcap
    have hi:=his i (ox ..)
    have hrest : ∀ l∈is,l∈b.row.RU:= fun l hl=>his l (oy _ hl)
    let s :=(nV b i).free.shape
    let r :=(nV b i).dI
    let T:=D.filter fun f => ∀ j a,a≤ r→f∣A5 j a (T8 i)
    have hT:T⊆D:=lI _ _
    have gt:=(sched.aE7 i (sched.brd i hi).2).1
    obtain ⟨hrow,hc⟩:=rows i hi
    have hTcap (j:Fin 3) :
        ajz T j≤ min (cap j) (auN s j/(r+1)) :=
      le_min ((cN5 hT j).trans (hcap j))
        (bLw (hD.mono hT) hrow hc gt.seed_small r
          (fun f hf=>(Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover,hLaterGeom,hLaterCap,hLater⟩ :=
      ih hrest T _ (hD.mono hT) hTcap
    obtain ⟨discard,hDiscardGeom,hDiscardCap,hDiscard⟩ :=
      collect (D \ T) (fun f k=>aHP s k f)
        (fun f z R=>rD f z R=0 ∧
          ∀ j a,a≤ r→ rD (A5 j a (T8 i)) z R=0) (by
        intro f hf
        obtain ⟨hfD,hfT⟩:=Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a,a≤ r→f∣A5 j a (T8 i) :=
          fun hall=>hfT (Finset.mem_filter.mpr ⟨hfD,hall⟩)
        push Not at hn
        obtain ⟨j,a,ha,hd⟩:=hn
        have hirr :=(hD.factors f hfD).1
        obtain ⟨S,hG,hF,hC⟩:=bt8 (b6z hirr hd)
          (caQ hirr.ne_zero) gt.ode.jb (bKa f) (czY.proof s (T8 i) hc j a)
        exact ⟨S,hG,fun k=>(hF k).trans_eq (cfi f s gt.ode.jb k),
          fun z R hr=>hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard∪laterCover,?_,?_,?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w:= fun j=>max (old j) (arC s k j)
      let newCap:= fun j=>min (cap j) (auN s j/(r+1))
      have hstep:=cs5 hT cap old s k hcap
      calc
        _≤ mass discard k+mass laterCover k :=bOC (fun I=>pN I k) _ _
        _≤(∑ f∈D \ T,aHP s k f) +
            (azi b k is newCap w+weightedDegree w T) :=
          lJ (hDiscardCap k) (hLaterCap k w)
        _=azi b k is newCap w +
            ((∑ f∈D \ T,aHP s k f)+weightedDegree w T) := by ac_rfl
        _≤azi b k is newCap w+(lV old D + aIe cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _:= by
          change _=(aIe cap old s k+azi b k is newCap w)+weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f,hf,hz⟩
      by_cases h:f∈T
      · obtain ⟨I,hI,hMark⟩:=hLater z R
          (fun l hl=>hder l (oy _ hl)) hq ⟨f,h,hz⟩
        exact ⟨I,oj _ hI,hMark⟩
      · obtain ⟨I,hI,hMark⟩:=hDiscard f (Finset.mem_sdiff.mpr ⟨hf,h⟩) z R
          ⟨hz,hder i (ox ..)⟩
        exact ⟨I,n5 _ hI,hMark⟩
end
end qIVBNpc
