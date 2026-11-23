import ProximityPrize.SubmissionLower.Z7znM4a
set_option Elab.async false
set_option autoImplicit true
namespace q5oHm3d
open P5_7_2 (fO Ls)
open q7F2qKe
open TD (GM FP a3x auN)
open cu (Shape)
open pI (weight)
private theorem dot_project (d:Shape) (x :GM) :
  FP (fun k=>(weight d 0 k :ℚ)) x=project d x := by
 rw [FP,Fin.sum_univ_four]
 change d.U*x 0+(d.B-d.J:ℕ)*x 1+d.J*x 2+0*x 3= _
 simp only [zero_mul,add_zero,project]
private theorem project_mono (d:Shape) {x y :GM} (h : ∀ k,x k≤y k) :
  project d x≤project d y := by
 rw [← dot_project,← dot_project]
 exact a3x (fun _=>Nat.cast_nonneg _) h
private theorem mixed_zero (f g:Shape) :
  kK (auN f) g 0=g.J*f.B+(g.B-g.J)*f.J:= by
 rw [kK,Fin.sum_univ_three]
 change g.J*f.B+(g.B-g.J)*f.J+0*f.U= _
 simp
private theorem mixed_one (f g:Shape) :
  kK (auN f) g 1=g.U*f.J+g.J*f.U:= by
 rw [kK,Fin.sum_univ_three]
 change 0*f.B+g.U*f.J+g.J*f.U= _
 simp
private theorem mixed_two (f g:Shape) :
  kK (auN f) g 2=g.U*f.B+g.B*f.U:= by
 rw [kK,Fin.sum_univ_three]
 change g.U*f.B+0*f.J+g.B*f.U= _
 simp
private theorem proper_seed_zero (f g:Shape) (r n e v :ℕ) :
  proper (shrink f n e v) (shrink g n e v) r 0 =
   proper (shrink f n e 0) (shrink g n e 0) r 0:= by
 simp only [proper,mixed_zero,shrink]
private theorem proper_seed_one (f g:Shape) (r n e v :ℕ)
    (hf :n*v≤f.U) (hg:n*v≤g.U) :
    proper (shrink f n e v) (shrink g n e v) r 1 =
      proper (shrink f n e 0) (shrink g n e 0) r 1 -
        (n*((shrink f n e 0).J+(shrink g n e 0).J) :ℕ)/((r^2 :ℕ) :ℚ)*v := by
  simp only [proper,mixed_one,shrink,Nat.mul_zero,Nat.sub_zero,
    Nat.cast_add,Nat.cast_mul,Nat.cast_sub hf,Nat.cast_sub hg]
  ring
private theorem proper_seed_two (f g:Shape) (r n e v :ℕ)
    (hf :n*v≤f.U) (hg:n*v≤g.U) :
    proper (shrink f n e v) (shrink g n e v) r 2 =
      proper (shrink f n e 0) (shrink g n e 0) r 2 -
        (n*((shrink f n e 0).B+(shrink g n e 0).B) :ℕ)/((r^2 :ℕ) :ℚ)*v := by
  simp only [proper,mixed_two,shrink,Nat.mul_zero,Nat.sub_zero,
    Nat.cast_add,Nat.cast_mul,Nat.cast_sub hf,Nat.cast_sub hg]
  ring
private theorem adM {e v E V:ℕ} (he :e≤E) (hv :v≤V) (k :Fin 4) :
   graph e v k≤graph E V k := by
 apply Nat.cast_le.mpr
 fin_cases k
 · exact he
 · exact hv
 · exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 he) hv
 · exact Nat.mul_le_mul hv hv
private theorem le_cell (s :Ls) (d:Shape) {c x :GM} (n e v :ℕ)
   (hclip : ∀ k,x k≤ c k) (hgraph : ∀ k,x k≤graph e v k)
   (hproper : ∀ k,x k≤proper (shrink s.free n e v) (shrink s.moving n e v)
     (s.dI+1-n) k)
   (hf :n*v≤ s.free.U) (hg:n*v≤ s.moving.U) :
   project d x≤PN s d c n e v := by
 have h₀:=hproper 0
 have h₁:=hproper 1
 have h₂:=hproper 2
 rw [proper_seed_zero] at h₀
 rw [proper_seed_one _ _ _ _ _ _ hf hg] at h₁
 rw [proper_seed_two _ _ _ _ _ _ hf hg] at h₂
 have g₁ :x 1≤1*(v :ℚ) := by
   simpa only [one_mul] using (show x 1≤(v :ℚ) from hgraph 1)
 have g₂ :x 2≤2*(e :ℚ)*v := by
   have h:=hgraph 2
   change x 2≤((2*e*v :ℕ) :ℚ) at h
   push_cast at h
   exact h
 exact add_le_add (add_le_add
   (mul_le_mul_of_nonneg_left (le_min (hclip 0) (le_min (hgraph 0) h₀)) (Nat.cast_nonneg _))
   (mul_le_mul_of_nonneg_left (le_min (hclip 1) (le_min g₁ h₁)) (Nat.cast_nonneg _)))
   (mul_le_mul_of_nonneg_left (le_min (hclip 2) (le_min g₂ h₂)) (Nat.cast_nonneg _))
private theorem stage_le {s :Ls} {d:Shape} {c x :GM} {dm:ℚ}
    (h:StageCheck s d c dm) (hpos :0<x 0) (hclip : ∀ k,x k≤ c k)
    (hfit :MovingFit s x) :
    project d x≤dm:= by
  rcases hfit with hproper | ⟨n,e,v,hn,hnm,he,hne,hnv,hgraph,hproper⟩
  · exact (project_mono d (fun k=>le_min (hclip k) (hproper k))).trans h.1
  · have he' : e≤jU s n:=(Nat.le_div_iff_mul_le hn).2 (by rwa [Nat.mul_comm])
    have hv' : v≤ seed s n:=(Nat.le_div_iff_mul_le hn).2 (by rwa [Nat.mul_comm])
    rcases hnm.eq_or_lt with rfl | hlt
    · exact (project_mono d (fun k =>
        le_min (hclip k) ((hgraph k).trans (adM he' hv' k)))).trans h.2.1
    · have h₀:=hproper hlt 0
      change x 0≤proper (shrink s.free n e v) (shrink s.moving n e v) (s.dI+1-n) 0 at h₀
      rw [proper_seed_zero] at h₀
      have hcap:0<ordinateCap s n e :=hpos.trans_le (le_min (hgraph 0) h₀)
      obtain ⟨t,ht,hdm⟩:=h.2.2 n hn hlt e he he' hcap
      have hvf :=hnv.trans (min_le_left _ _)
      have hvg:=hnv.trans (min_le_right _ _)
      exact (le_cell s d n e v hclip hgraph (hproper hlt) hvf hvg).trans
        ((cell_le_peak ht hv').trans hdm)
theorem projection_paid {b:fO} {o j:ℕ} {dm:ℚ}
   (h:ProjectionCheck b o j dm) {x :GM} (hx :Individual b o j x) :
   min (projectionCap b) (FP (SS b j 0) x)≤dm:= by
 have hclip : ∀ k,x k≤ clip b o j k := fun k=>(hx.2.1 k).2
 refine (min_le_right _ _).trans ?_
 rw [show FP (SS b j 0) x=project (aHp b j) x from dot_project _ _]
 rcases h with hbox | ⟨i,hi,hstage⟩
 · exact (project_mono _ hclip).trans hbox
 · exact stage_le hstage hx.1 hclip (hx.2.2 i hi)
end q5oHm3d
