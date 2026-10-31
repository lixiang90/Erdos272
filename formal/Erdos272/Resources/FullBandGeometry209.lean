import Erdos272.Resources.FullHeavySplit209
import Erdos272.Resources.ActualBandEval208

namespace JSP233.FullBandGeometry209
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 CrossBandMenu208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 200000

def Codes (s : System) (d : ℕ) (b : Band) : Finset (ℕ×ℕ) :=
  (s.Piece d b).image fun S=>Code d (s.B d b) (s.start S)
def Cap (s : System) (d : ℕ) (b : Band) (q : ℕ×ℕ) : ℕ :=
  min (SizeV s d b) (s.N/d-q.2*s.B d b+s.E d b)
def Full (s : System) (d : ℕ) (b : Band) : Finset (ℕ×ℕ) :=
  FullHeavySplit209.Full (s.Piece d b) (fun S=>Code d (s.B d b) (s.start S)) (Codes s d b) (SizeV s d b)
def Middle (s : System) (d : ℕ) (b : Band) : Finset (ℕ×ℕ) :=
  FullHeavySplit209.Middle (s.Piece d b) (fun S=>Code d (s.B d b) (s.start S))
    (Codes s d b) (SizeV s d b) (Cap s d b)
def FullPiece (s : System) (d : ℕ) (b : Band) : Finset (Finset ℤ) :=
  (s.Piece d b).filter fun S=>Code d (s.B d b) (s.start S)∈Full s d b
def FullFamily (s : System) : Finset (Finset ℤ) :=
  s.F.filter fun S=>Code (s.step S) (s.B (s.step S) (s.band S)) (s.start S)∈Full s (s.step S) (s.band S)
def Span (s : System) (d : ℕ) (b : Band) : ℕ :=
  SizeV s d b+(SizeV s d b-1)/s.B d b*s.B d b
def Period (s : System) (d : ℕ) (b : Band) : ℕ :=
  LightClosed208.Count (SizeV s d b-s.E d b-1) (s.T d b-s.E d b) (s.B d b)

theorem full_subset (s : System) (d : ℕ) (b : Band) : Full s d b⊆s.Heavy d b := by
  intro q hq
  obtain ⟨hI,hfull⟩:=Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨hI,?_⟩
  exact (min_le_left _ _).trans_lt hfull

theorem middle_subset (s : System) (d : ℕ) (b : Band) : Middle s d b⊆s.Heavy d b := by
  intro q hq
  obtain ⟨hI,hmid⟩:=Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hI,hmid.1⟩

theorem source_traits (s : System) (v : Valid s) {d : ℕ} (hd : d∈Finset.Icc 1 s.D) (b : Band) :
    ∀q∈Codes s d b,q.1<d ∧ s.T d b-s.E d b+q.2*s.B d b≤s.N/d ∧ s.T d b≤Cap s d b q := by
  have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
  have hM:=v.M_le d hd b
  have heM:=v.eM
  have he2:=v.e_two
  have hB:=v.B_two d hd b
  have hb:=BandGeometry208.actual_band_windows (s.piece_legal v.legal d b) hd0
    (by omega : 2≤s.T d b) (v.ET d hd b).le hB s.start
    (fun S hS=>v.crooked S (s.piece_subset d b hS)) (v.low d hd b) (v.high d hd b)
    (v.small d hd b) (fun S hS=>v.piece_sub hS)
  intro q hq
  obtain ⟨S,hS,heq⟩:=Finset.mem_image.mp hq
  have hs:=hb S hS
  have hl:=v.low d hd b S hS
  refine ⟨?_,?_,?_⟩
  · simpa only [heq] using hs.2.2.1
  · simpa only [heq] using hs.2.2.2
  · have hh:=hl.trans hs.2.1
    simpa only [Cap,SizeV,heq] using hh

theorem original_properties (s : System) (v : Valid s) {d : ℕ} (hd : d∈Finset.Icc 1 s.D)
    (b : Band) (hE : 1≤s.E d b) :
    BandSystem208.Properties s.N d (s.T d b-s.E d b) (s.B d b) (SizeV s d b) (s.E d b) (s.Heavy d b) := by
  have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
  have hM:=v.M_le d hd b
  have heM:=v.eM
  have he2:=v.e_two
  exact BandSystem208.actual_properties (s.piece_legal v.legal d b) hd0 (by omega : 2≤s.T d b)
    (v.ET d hd b).le hE (v.TU d hd b) (v.B_two d hd b) (v.BA d hd b) s.start
    (fun S hS=>v.crooked S (s.piece_subset d b hS)) (v.low d hd b) (v.high d hd b)
    (v.small d hd b) (fun S hS=>v.piece_sub hS) (v.gate d hd b)

theorem actual_middle_bounds (s : System) (v : Valid s) {d : ℕ} (hd : d∈Finset.Icc 1 s.D) (b : Band) :
    (Middle s d b).card≤Period s d b ∧
      (∑q∈Middle s d b,(SizeV s d b-Cap s d b q))≤Period s d b*(SizeV s d b-s.T d b) := by
  by_cases hE1 : s.E d b≤1
  · have hp:=ActualBandEval208.actual_piece_empty v hd b hE1
    have hm : Middle s d b=∅ := by simp only [Middle,FullHeavySplit209.Middle,Codes,hp,Finset.image_empty,Finset.filter_empty]
    simp only [hm,Finset.card_empty,Finset.sum_empty,Nat.zero_le,and_self]
  · have hB:=v.B_two d hd b
    have hET:=v.ET d hd b
    have hTU:=v.TU d hd b
    have hEV : s.E d b<SizeV s d b := by dsimp only [SizeV];omega
    have hp:=original_properties s v hd b (by omega : 1≤s.E d b)
    have hr : ∀q∈Middle s d b,¬SizeV s d b-s.E d b+q.2*s.B d b≤s.N/d := by
      intro q hq ho
      obtain ⟨hI,hmid⟩:=Finset.mem_filter.mp hq
      have hs:=(source_traits s v hd b q hI).2.1
      have hw : Cap s d b q=SizeV s d b := min_eq_left (by omega)
      rw [hw] at hmid
      omega
    have hc:=FullHeavySplit209.right_middle_count hp (by omega : 0<s.B d b) hEV (middle_subset s d b) hr
    refine ⟨hc,?_⟩
    have he:=FullHeavySplit209.middle_extra (Middle s d b) (Cap s d b)
      (T := s.T d b) (V := SizeV s d b) (fun q hq=>(source_traits s v hd b q (Finset.mem_filter.mp hq).1).2.2)
    exact he.trans (Nat.mul_le_mul_right _ hc)

theorem actual_full_geometry (s : System) (v : Valid s) {d : ℕ} (hd : d∈Finset.Icc 1 s.D) (b : Band) :
    (Full s d b).card≤(SizeV s d b-1)/s.B d b+1 ∧
      ((Full s d b).biUnion (ClippedWindows208.Window s.N d (s.B d b) (SizeV s d b))).card≤
        min (Span s d b) (s.N/d+1) := by
  have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
  have hM:=v.M_le d hd b
  have heM:=v.eM
  have he2:=v.e_two
  have hB:=v.B_two d hd b
  have hTU:=v.TU d hd b
  have hV : 0<SizeV s d b := by dsimp only [SizeV];omega
  have hband:=BandGeometry208.actual_band_windows (s.piece_legal v.legal d b) hd0
    (by omega : 2≤s.T d b) (v.ET d hd b).le hB s.start
    (fun S hS=>v.crooked S (s.piece_subset d b hS)) (v.low d hd b) (v.high d hd b)
    (v.small d hd b) (fun S hS=>v.piece_sub hS)
  have hdis:=BandGeometry208.actual_band_disjoint (s.piece_legal v.legal d b) hd0
    (by omega : 2≤s.T d b) (v.ET d hd b).le (by omega : 0<s.B d b) (v.BA d hd b) s.start
    (fun S hS=>v.crooked S (s.piece_subset d b hS)) (v.low d hd b) (v.high d hd b)
    (v.small d hd b) (fun S hS=>v.piece_sub hS) (v.gate d hd b)
  apply FullHeavySplit209.actual_full_geometry hd0 (by omega : 0<s.B d b) hV
    (BandSystem208.Fiber (s.Piece d b) d (s.B d b) s.start)
    (fun S=>Grid (s.start S) d (MaxAPSize S))
  · intro q hq
    exact (source_traits s v hd b q (Finset.mem_filter.mp hq).1).1
  · intro q hq S hS
    obtain ⟨hSF,heq⟩:=Finset.mem_filter.mp hS
    simpa only [heq,SizeV] using (hband S hSF).1
  · intro q hq S hS T hT hST
    obtain ⟨hSF,hSq⟩:=Finset.mem_filter.mp hS
    obtain ⟨hTF,hTq⟩:=Finset.mem_filter.mp hT
    exact hdis S hSF T hTF hST (hSq.trans hTq.symm)
  · intro q hq t ht S hS T hT
    have hSF:=(Finset.mem_filter.mp hS).1
    have hTF:=(Finset.mem_filter.mp hT).1
    by_cases he : S=T
    · subst T
      have hn : S.Nonempty := Finset.card_pos.mp (by have hh:=v.low d hd b S hSF;omega)
      simpa only [Finset.inter_self] using hn
    · exact isAP_nonempty ((s.piece_legal v.legal d b).2 S hSF T hTF he)
  · intro q hq S hS
    have hh:=v.high d hd b S (Finset.mem_filter.mp hS).1
    dsimp only [SizeV]
    omega
  · intro q hq
    exact (Finset.mem_filter.mp hq).2

#print axioms full_subset
#print axioms source_traits
#print axioms actual_middle_bounds
#print axioms actual_full_geometry
end
end JSP233.FullBandGeometry209
