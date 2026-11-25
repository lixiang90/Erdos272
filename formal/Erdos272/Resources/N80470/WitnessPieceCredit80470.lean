module

public import Erdos272.Geometry.N80470.WitnessPieceGeometry80470

@[expose] public section

namespace JSP233.WitnessPieceCredit80470
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208 BandLabels208
open CrossBandCredit208 CrossBandCleanup208 PhaseSystem82427
open WitnessPieceGeometry80470
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Labels (s : System) (d : ℕ) (b : Band) : Finset (ℕ × ℕ) :=
  (s.Piece d b).image (fun S => Code d (s.B d b) (s.start S))

def Threshold (s : System) (d : ℕ) (b : Band) (q : ℕ × ℕ) : ℕ :=
  if Refined s d b then
    PhaseDefs82427.Cap s.N d (s.E d b) (s.B d b) (s.U d b+s.B d b-3) (Swap q)
  else min (s.U d b+s.B d b-3) (s.N/d-q.2*s.B d b+s.E d b)

def CostSum (s : System) (d : ℕ) (b : Band) (A₀ : Finset ℤ) (W : ℕ) : ℕ :=
  ∑ q ∈ Labels s d b,
    WitnessCredit80470.Cost (Threshold s d b q) W (Hits s d b A₀ q)

def Light (s : System) (d : ℕ) (b : Band) (A₀ : Finset ℤ) (W : ℕ) : ℝ :=
  if s.E d b ≤ 1 then 0 else CostSum s d b A₀ W

theorem heavy_mem (s : System) (d : ℕ) (b : Band) (q : ℕ × ℕ) :
    q ∈ PhaseSystem82427.Heavy s d b ↔
      q ∈ Labels s d b ∧ Threshold s d b q < (Fiber s d b q).card := by
  by_cases hr : Refined s d b
  · simp only [PhaseSystem82427.Heavy,Threshold,if_pos hr,
      PhaseDefs82427.Heavy,CrossBandCredit208.System.Heavy,BandSystem208.Heavy,
      Labels,Fiber,Finset.mem_filter]
  · simp only [PhaseSystem82427.Heavy,Threshold,if_neg hr,
      PhaseDefs82427.Heavy,CrossBandCredit208.System.Heavy,BandSystem208.Heavy,
      Labels,Fiber,Finset.mem_filter]

theorem actual_threshold {s : System} (v : Valid s) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band) {S : Finset ℤ}
    (hS : S ∈ s.Piece d b) :
    s.T d b ≤ Threshold s d b (Code d (s.B d b) (s.start S)) := by
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  have hB := v.B_two d hd b
  have hs := v.low d hd b S hS
  have he := v.small d hd b S hS
  have hm := maxAPSize_le_card S
  have hcard : S.card=MaxAPSize S+Defect S := by unfold Defect; omega
  have hm0 : 0 < MaxAPSize S := by have := v.ET d hd b; omega
  have hhi := v.high d hd b S hS
  have hupper : S.card ≤ s.U d b+s.B d b-3 := by omega
  have hground := v.legal.1 S (s.piece_subset d b hS)
  by_cases hr : Refined s d b
  · have hc := (PhaseGeometry82427.actual_source_cap hd0 (by omega : 0 < s.B d b)
      hm0 he hcard (v.piece_sub hS) hground).2
    simpa only [Threshold,if_pos hr,PhaseDefs82427.Cap,Swap] using
      hs.trans (le_min hupper hc)
  · have hc := PotentialPhases208.actual_source_cap hd0 (by omega : 0 < s.B d b)
      hm0 he hcard (v.piece_sub hS) hground
    simpa only [Threshold,if_neg hr] using hs.trans (le_min hupper hc)

theorem actual_piece_credit {s : System} (v : Valid s) {d W : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band)
    {F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlegal : Legal (Ground s.N) F) (hsub : s.F ⊆ F)
    (hA : A₀ ∈ F) (hW : A₀.card ≤ W) :
    ((s.Piece d b).card : ℝ) + (s.T d b : ℝ)*(PhaseSystem82427.Heavy s d b).card ≤
      Light s d b A₀ W + (PhaseSystem82427.HeavyPiece s d b).card := by
  by_cases he : s.E d b ≤ 1
  · have hp := ActualBandEval208.actual_piece_empty v hd b he
    have hh : PhaseSystem82427.Heavy s d b=∅ := by
      unfold PhaseSystem82427.Heavy
      split_ifs <;> simp only [PhaseDefs82427.Heavy,System.Heavy,BandSystem208.Heavy,
        hp,Finset.image_empty,Finset.filter_empty]
    simp only [Light,if_pos he,PhaseSystem82427.HeavyPiece,hp,hh,
      Finset.filter_empty,Finset.card_empty,Nat.cast_zero,mul_zero,zero_add,le_refl]
  · have hmap : ∀ S ∈ s.Piece d b,
        Code d (s.B d b) (s.start S) ∈ Labels s d b :=
      fun S hS => Finset.mem_image.mpr ⟨S,hS,rfl⟩
    have hc := WitnessCredit80470.actual_light_credit
      (fun S => Code d (s.B d b) (s.start S)) (Labels s d b)
      (PhaseSystem82427.Heavy s d b) (Threshold s d b) (fun _ => s.T d b) W
      (Hits s d b A₀) hmap (by
        intro q hq hn
        have hn' : ¬Threshold s d b q < (Fiber s d b q).card :=
          fun h => hn ((heavy_mem s d b q).mpr ⟨hq,h⟩)
        change (Fiber s d b q).card ≤ _
        omega) (by
        intro q _hq hH
        exact ((heavy_mem s d b q).mp hH).2) (by
        intro q hq _hH
        obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hq
        exact actual_threshold v hd b hS) (by
        intro q _hq hmiss
        exact WitnessPieceGeometry80470.actual_fiber_cap v hd b hlegal hsub hA hW q hmiss)
    have hfilter : (Labels s d b).filter
        (fun q => q ∈ PhaseSystem82427.Heavy s d b)=PhaseSystem82427.Heavy s d b := by
      ext q
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨((heavy_mem s d b q).mp h).1,h⟩⟩
    have hcredit : (∑ q ∈ Labels s d b,
        if q ∈ PhaseSystem82427.Heavy s d b then s.T d b else 0)=
        s.T d b*(PhaseSystem82427.Heavy s d b).card := by
      rw [←Finset.sum_filter,hfilter]
      simp [Nat.mul_comm]
    rw [hcredit] at hc
    simpa only [Light,if_neg he,CostSum,PhaseSystem82427.HeavyPiece]
      using (show ((s.Piece d b).card : ℝ)+
        (s.T d b : ℝ)*(PhaseSystem82427.Heavy s d b).card ≤
        (CostSum s d b A₀ W : ℝ)+(PhaseSystem82427.HeavyPiece s d b).card by
          exact_mod_cast hc)

#print axioms heavy_mem
#print axioms actual_threshold
#print axioms actual_piece_credit
end
end JSP233.WitnessPieceCredit80470
