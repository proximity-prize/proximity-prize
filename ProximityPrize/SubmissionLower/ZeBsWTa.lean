import ProximityPrize.SubmissionLower.ZN1KL1c
import ProximityPrize.SubmissionLower.ZGAUtmc
set_option Elab.async false
set_option autoImplicit true
namespace qYyXDQd
open qHde8fc qKVdmob qDoysbd
open qhonTAe (Ae abJ)
open GN (ord)
open fP (cF)
open private aV aaH W6 line_sound start value prep from ProximityPrize.SubmissionLower.ZN1KL1c
private theorem core {w f a cut n code :ℕ} (hpos :0<cut) (hw:w≤112)
    (hf :dM (112-w) cut n code) (hh:Head (112-w) a f n code)
    (hl : ∀ t≤112-w,lK (112-w) a f n code t)
    (e :aY) (he :cP (aD e.val)=w) (hef :e.val 3=f) (hea :e.val 0=a) :
    cE cut (aD e.val)∈qokB5pc.jZ e cut:= by
  let q:=112-w
  let vs :=unpack q n code
  have hwt:w=56+ord e.val :=he.symm.trans (qhonTAe.nG e)
  have hq:56-ord e.val=q:= by dsimp only [q]; omega
  refine Ae e cut hpos (aV vs) (aaH vs ?_) ⟨?_,?_⟩
  · exact fun v hv=>of_decide_eq_true (List.all_eq_true.mp hf v hv)
  · rw [W6 e (by omega),hq,hea,hef]
    intro hz
    have hm:=Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    change value f (prep q a vs) % (P1.p:ℤ)=1 at hh
    omega
  · intro v hLive hkey
    obtain ⟨hv,hva⟩:=(abJ _).mp hLive
    let t:=56-ord v.val
    let u:=v.val 0
    let k :=v.val 3
    have hc:=qhonTAe.nG v
    change cP (aD v.val)=56+ord v.val at hc
    unfold dZ at hkey
    rw [he,hc,hef] at hkey
    have hd:=v.property
    have hd' := e.property
    rw [cF] at hd hd'
    have ho' : w-56≤ord v.val := by omega
    have ht:t≤q:= by dsimp only [t,q]; omega
    have hnum :3*u+2*k≤56-t:= by
      have h0:ord v.val=3*u+v.val 2+2*k :=rfl
      dsimp only [t]
      omega
    have hk :start q a f t u≤k := by
      unfold start
      split
      · exact Nat.zero_le _
      · rename_i h
        have hsame :ord v.val=ord e.val := by dsimp only [t,q] at h; omega
        have h0:ord v.val=3*u+v.val 2+2*k :=rfl
        have h1 :ord e.val=3*a+e.val 2+2*f := by rw [← hea,← hef]; rfl
        dsimp only [u,k] at *
        split <;> omega
    have hp:lK q a f n code t:=hl t ht
    have hu:u∈List.range (min 16 ((56-t)/3)+1) :=List.mem_range.mpr (by
      change u≤16 at hva
      omega)
    have hline :aT q a f n code t u:=List.all_eq_true.mp hp u hu
    have hm:=line_sound hline hk (by omega)
    rw [W6 v hv]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero hm)
end qYyXDQd
