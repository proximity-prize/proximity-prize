import ProximityPrize.SubmissionLower.ZjZ6ihd
set_option Elab.async false
set_option autoImplicit true
namespace qckEfrc
noncomputable section
open Polynomial Finset MvPolynomial
open P5 (K)


variable {ι:Type*} [Finite ι]
structure LinearData (T:Finset K) (s :K→K[X]) where
  pt:K→ι→cu.FX
  inj:Set.InjOn pt (T:Set K)
  cut:K→K→MvPolynomial ι cu.FX
  deg : ∀ x a,(cut x a).totalDegree≤1
  hit : ∀ γ∈T,∀ x a,aeval (pt γ) (cut x a)=0↔(s γ).eval x=a
variable {T:Finset K} {s :K→K[X]} (C:LinearData (ι:=ι) T s)
private theorem zero_count {U:Finset K} (hU:U⊆T) (P:Ideal (MvPolynomial ι cu.FX))
    (hd: (affineHilbertPolynomial P).natDegree=0)
    (hz : ∀ γ∈U,C.pt γ∈zeroLocus _ P) : (U.card:ℚ)≤affineDegree P:= by
  classical
  obtain ⟨hf,hc⟩:=finite_zeroLocus_and_ncard_le_affineDegree (K:=cu.FX) P hd
  have h: (↑(U.image C.pt) :Set (ι→cu.FX))⊆zeroLocus _ P:= by
    intro x hx
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hx
    exact hz γ hγ
  have hn:=Set.ncard_le_ncard h hf
  rw [Set.ncard_coe_finset,card_image_of_injOn (C.inj.mono hU)] at hn
  exact (Nat.cast_le.mpr hn).trans hc
omit [Finite ι] in
private theorem cut_data {U:Finset K} (hU:U⊆T) {P:Ideal (MvPolynomial ι cu.FX)}
    (hz : ∀ γ∈U,C.pt γ∈zeroLocus _ P) {x a :K}
    (hmiss : ∃ γ∈U,(s γ).eval x≠a) :C.cut x a∉P:= by
  obtain ⟨γ,hγ,hmiss⟩:=hmiss
  exact fun h=>hmiss ((C.hit γ (hU hγ) x a).mp (hz γ hγ _ h))
end
end qckEfrc
