module

public import Erdos272.Counting.N65968.FullSurplus65968
public import Erdos272.Counting.N80470.WitnessPieceBound80470

@[expose] public section

-- Connect the finite surplus sum to the original actual set family.
namespace JSP233.FullSurplusActual65968
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208 BandLabels208
open CrossBandCredit208 CrossBandCleanup208
open WitnessPieceGeometry80470 WitnessPieceCredit80470 WitnessPieceBound80470
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def OldSurplus (high d T E B U W : ℕ) : ℕ :=
  Overlap high d T E B U*(min (U+B-3) (high/d+E)-W)

def Candidate (high d T E B U W : ℕ) : ℕ :=
  Base high d T E B U W+
    W*min (OldSurplus high d T E B U W)
      (FullSurplus65968.Surplus (high/d) T E B (U+B-3) W)

def Bound (high d T E B U W : ℕ) : ℕ :=
  if E≤1 then 0 else min (Base high d T E B U (U+B-3))
    (Candidate high d T E B U W)

theorem threshold_point_upper {s : System} {d high : ℕ} (hN : s.N≤high)
    (b : Band) (q : ℕ×ℕ) :
    Threshold s d b q≤min (s.U d b+s.B d b-3)
      (high/d-q.2*s.B d b+s.E d b) := by
  have hn : s.N/d≤high/d := Nat.div_le_div_right hN
  have hp : (s.N-(q.1+1))/d≤high/d :=
    (Nat.div_le_div_right (Nat.sub_le s.N (q.1+1))).trans hn
  unfold Threshold PhaseDefs82427.Cap Swap
  split_ifs
  · exact min_le_min_left _
      (Nat.add_le_add_right (Nat.sub_le_sub_right hp (q.2*s.B d b)) _)
  · exact min_le_min_left _
      (Nat.add_le_add_right (Nat.sub_le_sub_right hn (q.2*s.B d b)) _)

theorem actual_full_surplus {s : System} (v : Valid s) {d high W : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (b : Band) (hN : s.N≤high)
    {A₀ : Finset ℤ} (hW : A₀.card≤W) :
    CostSum s d b A₀ W≤Base high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W+
      W*FullSurplus65968.Surplus (high/d) (s.T d b) (s.E d b)
        (s.B d b) (s.U d b+s.B d b-3) W := by
  have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1; omega
  have heM := v.eM
  have he2 := v.e_two
  have hM := v.M_le d hd b
  have hET := v.ET d hd b
  have hTU := v.TU d hd b
  have hB := v.B_two d hd b
  have hw := BandGeometry208.actual_band_windows (s.piece_legal v.legal d b)
    hd0 (by omega : 2≤s.T d b) hET.le hB s.start
    (fun S hS => v.crooked S (s.piece_subset d b hS))
    (v.low d hd b) (v.high d hd b) (v.small d hd b)
    (fun S hS => v.piece_sub hS)
  have hres : ∀ q∈Labels s d b, q.1<d := by
    intro q hq
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hq
    exact (hw S hS).2.2.1
  have hfeasible : ∀ q∈Labels s d b,
      s.T d b-s.E d b+q.2*s.B d b≤high/d := by
    intro q hq
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hq
    exact ((hw S hS).2.2.2).trans (Nat.div_le_div_right hN)
  have hs := FullSurplus65968.cost_sum_surplus (N:=s.N) (Threshold s d b) hd0
    (by omega : 0<s.B d b) hW hres hfeasible
    (fun q _hq => threshold_point_upper hN b q)
  have hs' : CostSum s d b A₀ W≤
      (∑ q∈Labels s d b, min (Threshold s d b q) W)+
        W*FullSurplus65968.Surplus (high/d) (s.T d b) (s.E d b)
          (s.B d b) (s.U d b+s.B d b-3) W := by
    simpa only [CostSum,Hits,Window] using hs
  exact hs'.trans (Nat.add_le_add_right (actual_base_bound v hd b hN) _)

theorem actual_cost_bound {s : System} (v : Valid s) {d high W : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (b : Band) (hN : s.N≤high)
    {A₀ : Finset ℤ} (hW : A₀.card≤W) :
    CostSum s d b A₀ W≤
      min (Base high d (s.T d b) (s.E d b) (s.B d b) (s.U d b)
        (s.U d b+s.B d b-3))
      (Candidate high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W) := by
  have old := WitnessPieceBound80470.actual_cost_bound v hd b hN hW
  apply le_min (old.trans (min_le_left _ _))
  have ho := old.trans (min_le_right _ _)
  have hall := actual_full_surplus v hd b hN hW
  unfold Candidate
  by_cases h : OldSurplus high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W≤
      FullSurplus65968.Surplus (high/d) (s.T d b) (s.E d b)
        (s.B d b) (s.U d b+s.B d b-3) W
  · rw [min_eq_left h]
    simpa only [WitnessPieceBound80470.Candidate,OldSurplus,Nat.mul_assoc] using ho
  · rw [min_eq_right (by omega)]
    exact hall

theorem actual_piece_bound {s : System} (v : Valid s) {d high W : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (b : Band) (hN : s.N≤high)
    {F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlegal : Legal (Ground s.N) F) (hsub : s.F⊆F)
    (hA : A₀∈F) (hW : A₀.card≤W) :
    ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(PhaseSystem82427.Heavy s d b).card≤
      (Bound high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W : ℝ)+
        (PhaseSystem82427.HeavyPiece s d b).card := by
  have hc := WitnessPieceCredit80470.actual_piece_credit v hd b hlegal hsub hA hW
  have hb : WitnessPieceCredit80470.Light s d b A₀ W≤
      (Bound high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W : ℝ) := by
    by_cases he : s.E d b≤1
    · simp only [WitnessPieceCredit80470.Light,Bound,if_pos he,Nat.cast_zero,le_refl]
    · simp only [WitnessPieceCredit80470.Light,Bound,if_neg he]
      exact_mod_cast actual_cost_bound v hd b hN hW
  linarith only [hc,hb]

#print axioms threshold_point_upper
#print axioms actual_full_surplus
#print axioms actual_cost_bound
#print axioms actual_piece_bound
end
end JSP233.FullSurplusActual65968
