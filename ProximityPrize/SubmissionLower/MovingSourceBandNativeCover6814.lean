import ProximityPrize.SubmissionLower.MovingSourceBandNativeForms6814
import ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
import ProximityPrize.SubmissionLower.WholeSpaceTrimmedReceipts6814

/-! Generated bounded covers. Every small dimension receipt is kernel checked;
coverage of the infinite degree variable is proved by linear arithmetic. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandNativeCover6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open WholeSpacePowerBox6814 MovingSourceBandNativeForms6814

def Admissible (a : Box) : Prop :=
  WholeSpacePowerCover6814.Good a ∨ WholeSpaceTrimmedReceipts6814.Good a
def HasBox (q b u t : ℕ) : Prop := ∃ a : Box, a.q=q ∧ a.Covers b u t ∧ Admissible a

private theorem cover1_b4 (u t : ℕ) (hbu : 4≤u) (hu : u≤32)
    (hut : u≤t) (ht : t≤331)
    (hf : ∃ i, Failure i 1 2 4 u t) : HasBox 3 4 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover1_b5 (u t : ℕ) (hbu : 5≤u) (hu : u≤32)
    (hut : u≤t) (ht : t≤331)
    (hf : ∃ i, Failure i 1 2 5 u t) : HasBox 3 5 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover1_b6 (u t : ℕ) (hbu : 6≤u) (hu : u≤32)
    (hut : u≤t) (ht : t≤331)
    (hf : ∃ i, Failure i 1 2 6 u t) : HasBox 3 6 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

def box0 : Box := ⟨3,7,7,32,294⟩
theorem box0_good : Admissible box0 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover1_b7 (u t : ℕ) (hbu : 7≤u) (hu : u≤32)
    (hut : u≤t) (ht : t≤331)
    (hf : ∃ i, Failure i 1 2 7 u t) : HasBox 3 7 u t := by
  have hc : box0.Covers 7 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box0] at hi ⊢ <;> omega
  exact ⟨box0,rfl,hc,box0_good⟩

def box1 : Box := ⟨3,8,8,28,52⟩
theorem box1_good : Admissible box1 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover1_b8 (u t : ℕ) (hbu : 8≤u) (hu : u≤32)
    (hut : u≤t) (ht : t≤331)
    (hf : ∃ i, Failure i 1 2 8 u t) : HasBox 3 8 u t := by
  have hc : box1.Covers 8 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box1] at hi ⊢ <;> omega
  exact ⟨box1,rfl,hc,box1_good⟩

def box2 : Box := ⟨3,9,9,25,29⟩
theorem box2_good : Admissible box2 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover1_b9 (u t : ℕ) (hbu : 9≤u) (hu : u≤32)
    (hut : u≤t) (ht : t≤331)
    (hf : ∃ i, Failure i 1 2 9 u t) : HasBox 3 9 u t := by
  have hc : box2.Covers 9 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box2] at hi ⊢ <;> omega
  exact ⟨box2,rfl,hc,box2_good⟩

def box3 : Box := ⟨3,10,10,21,25⟩
theorem box3_good : Admissible box3 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover1_b10 (u t : ℕ) (hbu : 10≤u) (hu : u≤32)
    (hut : u≤t) (ht : t≤331)
    (hf : ∃ i, Failure i 1 2 10 u t) : HasBox 3 10 u t := by
  have hc : box3.Covers 10 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box3] at hi ⊢ <;> omega
  exact ⟨box3,rfl,hc,box3_good⟩

theorem cover1 (b u t : ℕ) (hblo : 4≤b) (hbhi : b≤10)
    (hbu : b≤u) (hu : u≤32) (hut : u≤t) (ht : t≤331)
    (hf : ∃ i, Failure i 1 2 b u t) : HasBox 3 b u t := by
  interval_cases b
  · exact cover1_b4 u t hbu hu hut ht hf
  · exact cover1_b5 u t hbu hu hut ht hf
  · exact cover1_b6 u t hbu hu hut ht hf
  · exact cover1_b7 u t hbu hu hut ht hf
  · exact cover1_b8 u t hbu hu hut ht hf
  · exact cover1_b9 u t hbu hu hut ht hf
  · exact cover1_b10 u t hbu hu hut ht hf

private theorem cover2_b4 (u t : ℕ) (hbu : 4≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 4 u t) : HasBox 2 4 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b5 (u t : ℕ) (hbu : 5≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 5 u t) : HasBox 2 5 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b6 (u t : ℕ) (hbu : 6≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 6 u t) : HasBox 2 6 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b7 (u t : ℕ) (hbu : 7≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 7 u t) : HasBox 2 7 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b8 (u t : ℕ) (hbu : 8≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 8 u t) : HasBox 2 8 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b9 (u t : ℕ) (hbu : 9≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 9 u t) : HasBox 2 9 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b10 (u t : ℕ) (hbu : 10≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 10 u t) : HasBox 2 10 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b11 (u t : ℕ) (hbu : 11≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 11 u t) : HasBox 2 11 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b12 (u t : ℕ) (hbu : 12≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 12 u t) : HasBox 2 12 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover2_b13 (u t : ℕ) (hbu : 13≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 13 u t) : HasBox 2 13 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

def box4 : Box := ⟨2,14,14,49,469⟩
theorem box4_good : Admissible box4 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover2_b14 (u t : ℕ) (hbu : 14≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 14 u t) : HasBox 2 14 u t := by
  have hc : box4.Covers 14 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box4] at hi ⊢ <;> omega
  exact ⟨box4,rfl,hc,box4_good⟩

def box5 : Box := ⟨2,15,15,45,201⟩
theorem box5_good : Admissible box5 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover2_b15 (u t : ℕ) (hbu : 15≤u) (hu : u≤49)
    (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 15 u t) : HasBox 2 15 u t := by
  have hc : box5.Covers 15 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box5] at hi ⊢ <;> omega
  exact ⟨box5,rfl,hc,box5_good⟩

theorem cover2 (b u t : ℕ) (hblo : 4≤b) (hbhi : b≤15)
    (hbu : b≤u) (hu : u≤49) (hut : u≤t) (ht : t≤497)
    (hf : ∃ i, Failure i 2 2 b u t) : HasBox 2 b u t := by
  interval_cases b
  · exact cover2_b4 u t hbu hu hut ht hf
  · exact cover2_b5 u t hbu hu hut ht hf
  · exact cover2_b6 u t hbu hu hut ht hf
  · exact cover2_b7 u t hbu hu hut ht hf
  · exact cover2_b8 u t hbu hu hut ht hf
  · exact cover2_b9 u t hbu hu hut ht hf
  · exact cover2_b10 u t hbu hu hut ht hf
  · exact cover2_b11 u t hbu hu hut ht hf
  · exact cover2_b12 u t hbu hu hut ht hf
  · exact cover2_b13 u t hbu hu hut ht hf
  · exact cover2_b14 u t hbu hu hut ht hf
  · exact cover2_b15 u t hbu hu hut ht hf

private theorem cover3_b10 (u t : ℕ) (hbu : 10≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 10 u t) : HasBox 1 10 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover3_b11 (u t : ℕ) (hbu : 11≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 11 u t) : HasBox 1 11 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover3_b12 (u t : ℕ) (hbu : 12≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 12 u t) : HasBox 1 12 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover3_b13 (u t : ℕ) (hbu : 13≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 13 u t) : HasBox 1 13 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover3_b14 (u t : ℕ) (hbu : 14≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 14 u t) : HasBox 1 14 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover3_b15 (u t : ℕ) (hbu : 15≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 15 u t) : HasBox 1 15 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover3_b16 (u t : ℕ) (hbu : 16≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 16 u t) : HasBox 1 16 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

private theorem cover3_b17 (u t : ℕ) (hbu : 17≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 17 u t) : HasBox 1 17 u t := by
  obtain ⟨i,hi⟩ := hf
  fin_cases i <;> norm_num [Failure,form] at hi <;> omega

def box6 : Box := ⟨1,18,18,97,891⟩
theorem box6_good : Admissible box6 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b18 (u t : ℕ) (hbu : 18≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 18 u t) : HasBox 1 18 u t := by
  have hc : box6.Covers 18 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box6] at hi ⊢ <;> omega
  exact ⟨box6,rfl,hc,box6_good⟩

def box7 : Box := ⟨1,19,19,94,650⟩
theorem box7_good : Admissible box7 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b19 (u t : ℕ) (hbu : 19≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 19 u t) : HasBox 1 19 u t := by
  have hc : box7.Covers 19 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box7] at hi ⊢ <;> omega
  exact ⟨box7,rfl,hc,box7_good⟩

def box8 : Box := ⟨1,20,20,91,409⟩
theorem box8_good : Admissible box8 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b20 (u t : ℕ) (hbu : 20≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 20 u t) : HasBox 1 20 u t := by
  have hc : box8.Covers 20 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box8] at hi ⊢ <;> omega
  exact ⟨box8,rfl,hc,box8_good⟩

def box9 : Box := ⟨1,21,21,87,168⟩
theorem box9_good : Admissible box9 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b21 (u t : ℕ) (hbu : 21≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 21 u t) : HasBox 1 21 u t := by
  have hc : box9.Covers 21 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box9] at hi ⊢ <;> omega
  exact ⟨box9,rfl,hc,box9_good⟩

def box10 : Box := ⟨1,22,22,83,503⟩
theorem box10_good : Admissible box10 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box11 : Box := ⟨1,22,22,91,96⟩
theorem box11_good : Admissible box11 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b22 (u t : ℕ) (hbu : 22≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 22 u t) : HasBox 1 22 u t := by
  have hc : box10.Covers 22 u t ∨ box11.Covers 22 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box10,box11] at hi ⊢ <;> omega
  rcases hc with h0 | h1
  · exact ⟨box10,rfl,h0,box10_good⟩
  · exact ⟨box11,rfl,h1,box11_good⟩

def box12 : Box := ⟨1,23,23,80,721⟩
theorem box12_good : Admissible box12 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box13 : Box := ⟨1,23,23,84,93⟩
theorem box13_good : Admissible box13 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

private theorem cover3_b23 (u t : ℕ) (hbu : 23≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 23 u t) : HasBox 1 23 u t := by
  have hc : box12.Covers 23 u t ∨ box13.Covers 23 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box12,box13] at hi ⊢ <;> omega
  rcases hc with h0 | h1
  · exact ⟨box12,rfl,h0,box12_good⟩
  · exact ⟨box13,rfl,h1,box13_good⟩

def box14 : Box := ⟨1,24,24,76,869⟩
theorem box14_good : Admissible box14 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box15 : Box := ⟨1,24,24,78,661⟩
theorem box15_good : Admissible box15 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box16 : Box := ⟨1,24,24,81,244⟩
theorem box16_good : Admissible box16 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box17 : Box := ⟨1,24,24,87,89⟩
theorem box17_good : Admissible box17 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b24 (u t : ℕ) (hbu : 24≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 24 u t) : HasBox 1 24 u t := by
  have hc : box14.Covers 24 u t ∨ box15.Covers 24 u t ∨ box16.Covers 24 u t ∨ box17.Covers 24 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box14,box15,box16,box17] at hi ⊢ <;> omega
  rcases hc with h0 | h1 | h2 | h3
  · exact ⟨box14,rfl,h0,box14_good⟩
  · exact ⟨box15,rfl,h1,box15_good⟩
  · exact ⟨box16,rfl,h2,box16_good⟩
  · exact ⟨box17,rfl,h3,box17_good⟩

def box18 : Box := ⟨1,25,25,72,949⟩
theorem box18_good : Admissible box18 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

def box19 : Box := ⟨1,25,25,73,879⟩
theorem box19_good : Admissible box19 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box20 : Box := ⟨1,25,25,74,810⟩
theorem box20_good : Admissible box20 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box21 : Box := ⟨1,25,25,75,740⟩
theorem box21_good : Admissible box21 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box22 : Box := ⟨1,25,25,76,601⟩
theorem box22_good : Admissible box22 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box23 : Box := ⟨1,25,25,78,393⟩
theorem box23_good : Admissible box23 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box24 : Box := ⟨1,25,25,81,85⟩
theorem box24_good : Admissible box24 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b25 (u t : ℕ) (hbu : 25≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 25 u t) : HasBox 1 25 u t := by
  have hc : box18.Covers 25 u t ∨ box19.Covers 25 u t ∨ box20.Covers 25 u t ∨ box21.Covers 25 u t ∨ box22.Covers 25 u t ∨ box23.Covers 25 u t ∨ box24.Covers 25 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box18,box19,box20,box21,box22,box23,box24] at hi ⊢ <;> omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · exact ⟨box18,rfl,h0,box18_good⟩
  · exact ⟨box19,rfl,h1,box19_good⟩
  · exact ⟨box20,rfl,h2,box20_good⟩
  · exact ⟨box21,rfl,h3,box21_good⟩
  · exact ⟨box22,rfl,h4,box22_good⟩
  · exact ⟨box23,rfl,h5,box23_good⟩
  · exact ⟨box24,rfl,h6,box24_good⟩

def box25 : Box := ⟨1,26,26,68,889⟩
theorem box25_good : Admissible box25 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box26 : Box := ⟨1,26,26,70,819⟩
theorem box26_good : Admissible box26 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

def box27 : Box := ⟨1,26,26,71,750⟩
theorem box27_good : Admissible box27 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box28 : Box := ⟨1,26,26,72,680⟩
theorem box28_good : Admissible box28 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box29 : Box := ⟨1,26,26,73,541⟩
theorem box29_good : Admissible box29 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box30 : Box := ⟨1,26,26,75,402⟩
theorem box30_good : Admissible box30 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box31 : Box := ⟨1,26,26,77,81⟩
theorem box31_good : Admissible box31 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

private theorem cover3_b26 (u t : ℕ) (hbu : 26≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 26 u t) : HasBox 1 26 u t := by
  have hc : box25.Covers 26 u t ∨ box26.Covers 26 u t ∨ box27.Covers 26 u t ∨ box28.Covers 26 u t ∨ box29.Covers 26 u t ∨ box30.Covers 26 u t ∨ box31.Covers 26 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box25,box26,box27,box28,box29,box30,box31] at hi ⊢ <;> omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · exact ⟨box25,rfl,h0,box25_good⟩
  · exact ⟨box26,rfl,h1,box26_good⟩
  · exact ⟨box27,rfl,h2,box27_good⟩
  · exact ⟨box28,rfl,h3,box28_good⟩
  · exact ⟨box29,rfl,h4,box29_good⟩
  · exact ⟨box30,rfl,h5,box30_good⟩
  · exact ⟨box31,rfl,h6,box31_good⟩

def box32 : Box := ⟨1,27,27,64,898⟩
theorem box32_good : Admissible box32 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

def box33 : Box := ⟨1,27,27,66,759⟩
theorem box33_good : Admissible box33 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box34 : Box := ⟨1,27,27,68,621⟩
theorem box34_good : Admissible box34 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box35 : Box := ⟨1,27,27,70,482⟩
theorem box35_good : Admissible box35 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box36 : Box := ⟨1,27,27,72,273⟩
theorem box36_good : Admissible box36 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box37 : Box := ⟨1,27,27,75,77⟩
theorem box37_good : Admissible box37 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b27 (u t : ℕ) (hbu : 27≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 27 u t) : HasBox 1 27 u t := by
  have hc : box32.Covers 27 u t ∨ box33.Covers 27 u t ∨ box34.Covers 27 u t ∨ box35.Covers 27 u t ∨ box36.Covers 27 u t ∨ box37.Covers 27 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box32,box33,box34,box35,box36,box37] at hi ⊢ <;> omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5
  · exact ⟨box32,rfl,h0,box32_good⟩
  · exact ⟨box33,rfl,h1,box33_good⟩
  · exact ⟨box34,rfl,h2,box34_good⟩
  · exact ⟨box35,rfl,h3,box35_good⟩
  · exact ⟨box36,rfl,h4,box36_good⟩
  · exact ⟨box37,rfl,h5,box37_good⟩

def box38 : Box := ⟨1,28,28,60,700⟩
theorem box38_good : Admissible box38 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box39 : Box := ⟨1,28,28,65,352⟩
theorem box39_good : Admissible box39 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box40 : Box := ⟨1,28,28,70,74⟩
theorem box40_good : Admissible box40 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b28 (u t : ℕ) (hbu : 28≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 28 u t) : HasBox 1 28 u t := by
  have hc : box38.Covers 28 u t ∨ box39.Covers 28 u t ∨ box40.Covers 28 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box38,box39,box40] at hi ⊢ <;> omega
  rcases hc with h0 | h1 | h2
  · exact ⟨box38,rfl,h0,box38_good⟩
  · exact ⟨box39,rfl,h1,box39_good⟩
  · exact ⟨box40,rfl,h2,box40_good⟩

def box41 : Box := ⟨1,29,29,56,432⟩
theorem box41_good : Admissible box41 := by
  apply Or.inr
  unfold WholeSpaceTrimmedReceipts6814.Good
  decide +kernel

def box42 : Box := ⟨1,29,29,65,70⟩
theorem box42_good : Admissible box42 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b29 (u t : ℕ) (hbu : 29≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 29 u t) : HasBox 1 29 u t := by
  have hc : box41.Covers 29 u t ∨ box42.Covers 29 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box41,box42] at hi ⊢ <;> omega
  rcases hc with h0 | h1
  · exact ⟨box41,rfl,h0,box41_good⟩
  · exact ⟨box42,rfl,h1,box42_good⟩

def box43 : Box := ⟨1,30,30,53,66⟩
theorem box43_good : Admissible box43 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b30 (u t : ℕ) (hbu : 30≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 30 u t) : HasBox 1 30 u t := by
  have hc : box43.Covers 30 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box43] at hi ⊢ <;> omega
  exact ⟨box43,rfl,hc,box43_good⟩

def box44 : Box := ⟨1,31,31,49,62⟩
theorem box44_good : Admissible box44 := by
  apply Or.inl
  unfold WholeSpacePowerCover6814.Good
  decide +kernel

private theorem cover3_b31 (u t : ℕ) (hbu : 31≤u) (hu : u≤98)
    (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 31 u t) : HasBox 1 31 u t := by
  have hc : box44.Covers 31 u t := by
    obtain ⟨i,hi⟩ := hf
    fin_cases i <;> norm_num [Failure,form,Box.Covers,box44] at hi ⊢ <;> omega
  exact ⟨box44,rfl,hc,box44_good⟩

theorem cover3 (b u t : ℕ) (hblo : 10≤b) (hbhi : b≤31)
    (hbu : b≤u) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hf : ∃ i, Failure i 3 5 b u t) : HasBox 1 b u t := by
  interval_cases b
  · exact cover3_b10 u t hbu hu hut ht hf
  · exact cover3_b11 u t hbu hu hut ht hf
  · exact cover3_b12 u t hbu hu hut ht hf
  · exact cover3_b13 u t hbu hu hut ht hf
  · exact cover3_b14 u t hbu hu hut ht hf
  · exact cover3_b15 u t hbu hu hut ht hf
  · exact cover3_b16 u t hbu hu hut ht hf
  · exact cover3_b17 u t hbu hu hut ht hf
  · exact cover3_b18 u t hbu hu hut ht hf
  · exact cover3_b19 u t hbu hu hut ht hf
  · exact cover3_b20 u t hbu hu hut ht hf
  · exact cover3_b21 u t hbu hu hut ht hf
  · exact cover3_b22 u t hbu hu hut ht hf
  · exact cover3_b23 u t hbu hu hut ht hf
  · exact cover3_b24 u t hbu hu hut ht hf
  · exact cover3_b25 u t hbu hu hut ht hf
  · exact cover3_b26 u t hbu hu hut ht hf
  · exact cover3_b27 u t hbu hu hut ht hf
  · exact cover3_b28 u t hbu hu hut ht hf
  · exact cover3_b29 u t hbu hu hut ht hf
  · exact cover3_b30 u t hbu hu hut ht hf
  · exact cover3_b31 u t hbu hu hut ht hf

theorem failure_has_box (i : Fin 11) (m s b u t : ℕ)
    (hm : 0<m) (hs : 2≤s) (hms : m≤s) (hsb : 2*s≤b) (hbu : b≤u) (hut : u≤t)
    (hB : MovingSourceNativeEnvelope6814.copies3 m*b≤31)
    (hU : MovingSourceNativeEnvelope6814.copies3 m*u≤98)
    (hT : MovingSourceNativeEnvelope6814.copies3 m*t≤995)
    (hex : 3≤m → 5≤s) (hf : Failure i m s b u t) :
    HasBox (MovingSourceNativeEnvelope6814.copies3 m) b u t := by
  by_cases hm1 : m=1
  · subst m
    norm_num [MovingSourceNativeEnvelope6814.copies3] at hB hU hT ⊢
    exact cover1 b u t (by omega) (by omega) hbu (by omega) hut (by omega)
      ⟨i,failure_of_larger i 1 s 1 2 b u t le_rfl hs hf⟩
  by_cases hm2 : m=2
  · subst m
    norm_num [MovingSourceNativeEnvelope6814.copies3] at hB hU hT ⊢
    exact cover2 b u t (by omega) (by omega) hbu (by omega) hut (by omega)
      ⟨i,failure_of_larger i 2 s 2 2 b u t le_rfl hs hf⟩
  have hm3 : 3≤m := by omega
  have hs5 := hex hm3
  have hq : MovingSourceNativeEnvelope6814.copies3 m=1 := by
    unfold MovingSourceNativeEnvelope6814.copies3
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hq] at hB hU hT ⊢
  exact cover3 b u t (by omega) (by omega) hbu (by omega) hut (by omega)
    ⟨i,failure_of_larger i m s 3 5 b u t hm3 hs5 hf⟩

#print axioms failure_has_box
end
end ProximityPrize.SubmissionLower.MovingSourceBandNativeCover6814
