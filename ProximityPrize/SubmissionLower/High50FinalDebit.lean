import ProximityPrize.SubmissionLower.High50NonlinearBase

set_option Elab.async false

namespace High50Nonlinear

open Finset
open K1_14_2 (Ambient)
open P1_7_4 (Mass dotQ massQ massQ_split running weightedBill)

private theorem sum_steps (w : ℕ → Mass) (z : Mass) (n : ℕ) :
    (∑ i ∈ range n, dotQ (fun k => running w (i+1) k - running w i k) z) = dotQ (running w n) z := by
  induction n with
  | zero => simp [dotQ, running]
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold dotQ
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring

private theorem subtract_bill (w H : ℕ → Mass) (z : Mass) (n : ℕ) :
    weightedBill n w (fun i k => H i k - z k) + dotQ (running w n) z = weightedBill n w H := by
  rw [← sum_steps]
  unfold weightedBill
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  unfold dotQ
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  ring

/-- Reserve the mass of the terminal survivors before charging the proper cuts. -/
theorem bill_after_exit_and_final (n stop : ℕ) (w H : ℕ → Mass) (entry : Mass)
    (live lost : ℕ → Finset (Ideal Ambient)) (E S T : Finset (Ideal Ambient))
    (next : ∀ i < n, live (i+1) ⊆ live i)
    (fail : ∀ i < n, lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k, massQ (live i) k ≤ H i k)
    (early : ∀ i < stop, S ⊆ live i)
    (late : ∀ i ≥ stop, i < n → live i ⊆ E \ S)
    (disjoint : ∀ i < n, Disjoint (lost i) S)
    (subset : S ⊆ E) (entry_cap : ∀ k, massQ E k ≤ entry k)
    (final_entry : T ⊆ E) (final_live : T ⊆ live n) (final_disjoint : Disjoint S T) :
    (∑ i ∈ range n, dotQ (w i) (massQ (lost i))) + dotQ (running w n) (massQ T) ≤
      weightedBill n w (remainder stop H entry (massQ S)) := by
  let live' := fun i => live i \ T
  let E' := E \ T
  have hlive : ∀ i, i ≤ n → T ⊆ live i := by
    intro i hi
    have reach (j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : live j ⊆ live i := by
      induction hij with
      | refl => exact Subset.refl _
      | @step k _ ih => exact (next k (by omega)).trans (ih (by omega))
    exact final_live.trans (reach n hi le_rfl)
  have hdisj (i : ℕ) (hi : i < n) (I : Ideal Ambient) (hI : I ∈ lost i) : I ∉ T := by
    intro ht
    exact (mem_sdiff.mp (fail i hi hI)).2 (hlive (i+1) (by omega) ht)
  have hsubset : S ⊆ E' := fun I hI => mem_sdiff.mpr ⟨subset hI, disjoint_left.mp final_disjoint hI⟩
  have hcap (i : ℕ) (hi : i < n) (k : Fin 4) : massQ (live' i) k ≤ H i k - massQ T k := by
    have hp := massQ_split (hlive i (by omega)) k
    change massQ (live i \ T) k ≤ _
    linarith only [hp,cap i hi k]
  have hentry (k : Fin 4) : massQ E' k ≤ entry k - massQ T k := by
    have he := massQ_split final_entry k
    change massQ (E \ T) k ≤ _
    linarith only [he,entry_cap k]
  have hearly (i : ℕ) (hi : i < stop) : S ⊆ live' i :=
    fun I hI => mem_sdiff.mpr ⟨early i hi hI,disjoint_left.mp final_disjoint hI⟩
  have hlate (i : ℕ) (hi : i ≥ stop) (hi' : i < n) : live' i ⊆ E' \ S := by
    intro I hI
    obtain ⟨hL,hT⟩ := mem_sdiff.mp hI
    obtain ⟨hE,hS⟩ := mem_sdiff.mp (late i hi hi' hL)
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hE,hT⟩,hS⟩
  have next' (i : ℕ) (hi : i < n) : live' (i+1) ⊆ live' i :=
    fun I hI => mem_sdiff.mpr ⟨next i hi (mem_sdiff.mp hI).1,(mem_sdiff.mp hI).2⟩
  have fail' (i : ℕ) (hi : i < n) : lost i ⊆ live' i \ live' (i+1) := by
    intro I hI
    obtain ⟨hm,hn⟩ := mem_sdiff.mp (fail i hi hI)
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hm,hdisj i hi I hI⟩,fun h => hn (mem_sdiff.mp h).1⟩
  have hb := bill_after_exit n stop w (fun i k => H i k-massQ T k) (fun k => entry k-massQ T k)
    live' lost E' S next' fail' hcap hearly hlate disjoint hsubset hentry
  have same : remainder stop (fun i k => H i k-massQ T k) (fun k => entry k-massQ T k) (massQ S) =
      fun i k => remainder stop H entry (massQ S) i k - massQ T k := by
    funext i k
    unfold remainder
    by_cases hi : i < stop
    · rw [ite_eq_left hi,ite_eq_left hi]
      ring
    · rw [ite_eq_right hi,ite_eq_right hi]
      have heq : entry k - massQ T k - massQ S k = (entry k - massQ S k) - massQ T k := by ring
      rw [heq, min_sub_sub_right]
  rw [same] at hb
  exact (add_le_add hb (le_refl (dotQ (running w n) (massQ T)))).trans_eq
    (subtract_bill w (remainder stop H entry (massQ S)) (massQ T) n)

#print axioms bill_after_exit_and_final
end High50Nonlinear
