module

public import Erdos272.Resources.FullBandGeometry209
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.FullBandCredit209
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 CrossBandMenu208 FullBandGeometry209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def MiddlePiece (s : System) (d : ℕ) (b : Band) : Finset (Finset ℤ) :=
  (s.Piece d b).filter fun S=>Code d (s.B d b) (s.start S)∈Middle s d b
def EffectiveLight (s : System) (d : ℕ) (b : Band) : ℝ := if s.E d b≤1 then 0 else s.Light d b
def MiddleFee (s : System) (d : ℕ) (b : Band) : ℕ :=
  if s.E d b≤1 then 0 else
    if s.T d b-s.E d b≤s.N/d then Period s d b*(SizeV s d b-s.T d b) else 0

theorem heavy_union (s : System) (d : ℕ) (b : Band) : s.Heavy d b=Full s d b∪Middle s d b := by
  ext q
  constructor
  · intro hq
    by_cases hf : q∈Full s d b
    · exact Finset.mem_union_left _ hf
    · obtain ⟨hI,hh⟩:=Finset.mem_filter.mp hq
      have hn : (BandSystem208.Fiber (s.Piece d b) d (s.B d b) s.start q).card≤SizeV s d b := by
        by_contra h
        exact hf (Finset.mem_filter.mpr ⟨hI,Nat.lt_of_not_ge h⟩)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hI,hh,hn⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hf | hm
    · exact full_subset s d b hf
    · exact middle_subset s d b hm

theorem full_middle_disjoint (s : System) (d : ℕ) (b : Band) : Disjoint (Full s d b) (Middle s d b) := by
  apply Finset.disjoint_left.mpr
  intro q hf hm
  have hh:=(Finset.mem_filter.mp hf).2
  have hl:=(Finset.mem_filter.mp hm).2.2
  omega

theorem heavy_card (s : System) (d : ℕ) (b : Band) :
    (s.Heavy d b).card=(Full s d b).card+(Middle s d b).card := by
  rw [heavy_union,Finset.card_union_of_disjoint (full_middle_disjoint s d b)]

theorem heavy_piece_card (s : System) (d : ℕ) (b : Band) :
    (s.HeavyPiece d b).card=(FullPiece s d b).card+(MiddlePiece s d b).card := by
  have he : s.HeavyPiece d b=FullPiece s d b∪MiddlePiece s d b := by
    ext S
    simp only [System.HeavyPiece,FullPiece,MiddlePiece,Finset.mem_filter,heavy_union,Finset.mem_union]
    tauto
  have hd : Disjoint (FullPiece s d b) (MiddlePiece s d b) := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    exact Finset.disjoint_left.mp (full_middle_disjoint s d b)
      (Finset.mem_filter.mp hS).2 (Finset.mem_filter.mp hT).2
  rw [he,Finset.card_union_of_disjoint hd]

theorem middle_piece_card (s : System) (d : ℕ) (b : Band) :
    (MiddlePiece s d b).card≤(SizeV s d b)*(Middle s d b).card := by
  let label : Finset ℤ→ℕ×ℕ := fun S=>Code d (s.B d b) (s.start S)
  have hmap : ∀S∈MiddlePiece s d b,label S∈Middle s d b := fun S hS=>(Finset.mem_filter.mp hS).2
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _≤∑_q∈Middle s d b,SizeV s d b := by
      apply Finset.sum_le_sum
      intro q hq
      have he : (MiddlePiece s d b).filter (fun S=>label S=q)=BandSystem208.Fiber (s.Piece d b) d (s.B d b) s.start q := by
        ext S
        simp only [MiddlePiece,BandSystem208.Fiber,Finset.mem_filter]
        constructor
        · intro h;exact ⟨h.1.1,h.2⟩
        · intro h
          refine ⟨⟨h.1,?_⟩,h.2⟩
          simpa only [label,h.2] using hq
      rw [he]
      exact (Finset.mem_filter.mp hq).2.2
    _=_ := by simp [Nat.mul_comm]

theorem piece_extinction (s : System) (v : Valid s) {d : ℕ} (hd : d∈Finset.Icc 1 s.D) (b : Band)
    (hA : s.N/d<s.T d b-s.E d b) : s.Piece d b=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hI : Code d (s.B d b) (s.start S)∈Codes s d b := Finset.mem_image.mpr ⟨S,hS,rfl⟩
  have hh:=(source_traits s v hd b _ hI).2.1
  omega

/-- Original truncated light price, full-heavy credit, and only the right
middle correction. The support cutoff is the actual per-band A=T-E. -/
theorem actual_full_credit (s : System) (v : Valid s) {d : ℕ} (hd : d∈Finset.Icc 1 s.D) (b : Band) :
    ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(Full s d b).card≤
      EffectiveLight s d b+(FullPiece s d b).card+(MiddleFee s d b : ℝ) := by
  by_cases hE1 : s.E d b≤1
  · have hp:=ActualBandEval208.actual_piece_empty v hd b hE1
    have hf : Full s d b=∅ := by simp only [Full,FullHeavySplit209.Full,Codes,hp,Finset.image_empty,Finset.filter_empty]
    have hfp : FullPiece s d b=∅ := by simp only [FullPiece,hp,Finset.filter_empty]
    simp only [hp,hf,hfp,Finset.card_empty,Nat.cast_zero,mul_zero,zero_add,EffectiveLight,MiddleFee,if_pos hE1]
    positivity
  · by_cases hA : s.T d b-s.E d b≤s.N/d
    · have hc:=v.piece_credit hd b
      have hh : ((s.Heavy d b).card : ℝ)=(Full s d b).card+(Middle s d b).card := by exact_mod_cast heavy_card s d b
      have hp : ((s.HeavyPiece d b).card : ℝ)=(FullPiece s d b).card+(MiddlePiece s d b).card := by exact_mod_cast heavy_piece_card s d b
      have hm : ((MiddlePiece s d b).card : ℝ)≤(SizeV s d b : ℝ)*(Middle s d b).card := by exact_mod_cast middle_piece_card s d b
      have hB:=v.B_two d hd b
      have hTU:=v.TU d hd b
      have hTV : s.T d b≤SizeV s d b := by dsimp only [SizeV];omega
      have hclean : ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(Full s d b).card≤
          s.Light d b+(FullPiece s d b).card+((SizeV s d b-s.T d b : ℕ) : ℝ)*(Middle s d b).card := by
        rw [hh,hp] at hc
        rw [Nat.cast_sub hTV]
        nlinarith only [hc,hm]
      have hdR : ((SizeV s d b-s.T d b : ℕ) : ℝ)*(Middle s d b).card≤
          ((Period s d b*(SizeV s d b-s.T d b) : ℕ) : ℝ) := by
        have hdN:=Nat.mul_le_mul_right (SizeV s d b-s.T d b) (actual_middle_bounds s v hd b).1
        have hdN' : (SizeV s d b-s.T d b)*(Middle s d b).card≤Period s d b*(SizeV s d b-s.T d b) := by
          simpa only [Nat.mul_comm] using hdN
        exact_mod_cast hdN'
      simp only [EffectiveLight,if_neg hE1,MiddleFee,if_pos hA]
      linarith only [hclean,hdR]
    · have hp:=piece_extinction s v hd b (by omega)
      have hf : Full s d b=∅ := by simp only [Full,FullHeavySplit209.Full,Codes,hp,Finset.image_empty,Finset.filter_empty]
      have hfp : FullPiece s d b=∅ := by simp only [FullPiece,hp,Finset.filter_empty]
      simp only [hp,hf,hfp,Finset.card_empty,Nat.cast_zero,mul_zero,zero_add,EffectiveLight,if_neg hE1,MiddleFee,if_neg hA,add_zero]
      exact Nat.cast_nonneg _

#print axioms heavy_card
#print axioms heavy_piece_card
#print axioms middle_piece_card
#print axioms actual_full_credit
end
end JSP233.FullBandCredit209
