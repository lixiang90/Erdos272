module

public import Erdos272.Resources.N80470.WitnessPieceCredit80470
public import Erdos272.Counting.N80470.WitnessWindows80470
public import Erdos272.Counting.N80470.WitnessLegacy80470

@[expose] public section

namespace JSP233.WitnessPieceBound80470
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208 BandLabels208
open CrossBandCredit208 CrossBandCleanup208
open WitnessPieceGeometry80470 WitnessPieceCredit80470
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Refined (E B : ℕ) : Prop := 2 ≤ E ∧ 3 ≤ B

instance (E B : ℕ) : Decidable (Refined E B) :=
  inferInstanceAs (Decidable (2 ≤ E ∧ 3 ≤ B))

def Weight (high d E B V W : ℕ) (i : ℕ × ℕ) : ℕ :=
  if Refined E B then min (min V W) ((high-i.2)/d-i.1*B+E)
  else min (min V W) (high/d-i.1*B+E)

def Base (high d T E B U W : ℕ) : ℕ :=
  let V := U+B-3
  if Refined E B then WitnessClosed80470.CappedClosed high d T E B (min V W)
  else WitnessLegacy80470.LegacyClosed high d T E B (min V W)

def Overlap (high d T E B U : ℕ) : ℕ :=
  min ((U+B-3-1)/B+1) (WitnessWindows80470.FeasibleCount (high/d) (T-E) B)

def Candidate (high d T E B U W : ℕ) : ℕ :=
  Base high d T E B U W+
    W*Overlap high d T E B U*(min (U+B-3) (high/d+E)-W)

def Bound (high d T E B U W : ℕ) : ℕ :=
  if E ≤ 1 then 0 else min (Base high d T E B U (U+B-3))
    (Candidate high d T E B U W)

theorem indices_mono {N high d A B : ℕ} (hN : N ≤ high) :
    LightPhases208.Indices N d A B ⊆ LightPhases208.Indices high d A B := by
  intro i hi
  obtain ⟨hi,hs⟩ := Finset.mem_filter.mp hi
  obtain ⟨hr,hx⟩ := Finset.mem_product.mp hi
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hr).trans_le (by omega)),hx⟩,hs.trans hN⟩

theorem weight_sum {high d T E B U W : ℕ} (hd : 0 < d) (hB : 0 < B)
    (hET : E < T) :
    (∑ i ∈ LightPhases208.Indices high d (T-E) B,
      Weight high d E B (U+B-3) W i)=Base high d T E B U W := by
  by_cases hr : Refined E B
  · simp only [Weight,Base,if_pos hr]
    exact WitnessClosed80470.capped_price_closed hd hB hET
  · have hs := LightPhases208.index_sum high d T E B (min (U+B-3) W)
    rw [WitnessLegacy80470.legacy_price_closed hd hB hET.le] at hs
    simpa only [Weight,Base,if_neg hr,LightPhases208.Cap] using hs

theorem threshold_cap (s : System) (d : ℕ) (b : Band) (q : ℕ × ℕ) :
    Threshold s d b q ≤ s.U d b+s.B d b-3 := by
  unfold Threshold
  split_ifs <;> exact min_le_left _ _

theorem threshold_upper {s : System} {d high : ℕ} (hN : s.N ≤ high)
    (b : Band) (q : ℕ × ℕ) :
    Threshold s d b q ≤ min (s.U d b+s.B d b-3) (high/d+s.E d b) := by
  have hn : s.N/d ≤ high/d := Nat.div_le_div_right hN
  have hp : (s.N-(q.1+1))/d ≤ s.N/d := Nat.div_le_div_right (Nat.sub_le s.N (q.1+1))
  have hphase : (s.N-(q.1+1))/d-q.2*s.B d b ≤ high/d :=
    (Nat.sub_le _ _).trans (hp.trans hn)
  have hlegacy : s.N/d-q.2*s.B d b ≤ high/d := (Nat.sub_le _ _).trans hn
  unfold Threshold PhaseDefs82427.Cap Swap
  split_ifs
  · exact min_le_min_left _ (Nat.add_le_add_right hphase _)
  · exact min_le_min_left _ (Nat.add_le_add_right hlegacy _)

theorem capped_threshold {s : System} {d high W : ℕ} (hN : s.N ≤ high)
    (b : Band) (q : ℕ × ℕ) :
    min (Threshold s d b q) W ≤
      Weight high d (s.E d b) (s.B d b) (s.U d b+s.B d b-3) W (Swap q) := by
  have hn : s.N/d ≤ high/d := Nat.div_le_div_right hN
  have hp : (s.N-(q.1+1))/d ≤ (high-(q.1+1))/d :=
    Nat.div_le_div_right (Nat.sub_le_sub_right hN (q.1+1))
  by_cases hr : PhaseSystem82427.Refined s d b
  · have hr' : Refined (s.E d b) (s.B d b) := hr
    simp only [Threshold,Weight,if_pos hr,if_pos hr',PhaseDefs82427.Cap,Swap]
    have hz := Nat.add_le_add_right (Nat.sub_le_sub_right hp (q.2*s.B d b)) (s.E d b)
    omega
  · have hr' : ¬Refined (s.E d b) (s.B d b) := hr
    simp only [Threshold,Weight,if_neg hr,if_neg hr',Swap]
    have hz := Nat.add_le_add_right (Nat.sub_le_sub_right hn (q.2*s.B d b)) (s.E d b)
    omega

theorem actual_base_bound {s : System} (v : Valid s) {d high W : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band) (hN : s.N ≤ high) :
    (∑ q ∈ Labels s d b, min (Threshold s d b q) W) ≤
      Base high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W := by
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  have hB := v.B_two d hd b
  have hET := v.ET d hd b
  have hm : ∀ S ∈ s.Piece d b, S.card=MaxAPSize S+Defect S := by
    intro S hS
    have := maxAPSize_le_card S
    unfold Defect
    omega
  have hl := LightPhases208.actual_label s.start MaxAPSize Defect hd0
    (by omega : 0 < s.B d b) (v.low d hd b) hET (v.small d hd b) hm
    (fun S hS => v.piece_sub hS)
    (fun S hS => v.legal.1 S (s.piece_subset d b hS))
  have hI : (Labels s d b).image Swap ⊆
      LightPhases208.Indices high d (s.T d b-s.E d b) (s.B d b) := by
    intro i hi
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hq
    exact indices_mono hN (hl S hS)
  calc
    _ ≤ ∑ q ∈ Labels s d b,
        Weight high d (s.E d b) (s.B d b) (s.U d b+s.B d b-3) W (Swap q) :=
      Finset.sum_le_sum (fun q hq => capped_threshold hN b q)
    _ = ∑ i ∈ (Labels s d b).image Swap,
        Weight high d (s.E d b) (s.B d b) (s.U d b+s.B d b-3) W i :=
      (Finset.sum_image (fun q hq t ht he => swap_injective he)).symm
    _ ≤ ∑ i ∈ LightPhases208.Indices high d (s.T d b-s.E d b) (s.B d b),
        Weight high d (s.E d b) (s.B d b) (s.U d b+s.B d b-3) W i :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (by intros; exact Nat.zero_le _)
    _ = _ := weight_sum hd0 (by omega) hET

theorem actual_hit_bound {s : System} (v : Valid s) {d high W : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band) (hN : s.N ≤ high)
    {A₀ : Finset ℤ} (hW : A₀.card ≤ W) :
    ((Labels s d b).filter (Hits s d b A₀)).card ≤
      W*Overlap high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) := by
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  have heM := v.eM
  have he2 := v.e_two
  have hM := v.M_le d hd b
  have hET := v.ET d hd b
  have hTU := v.TU d hd b
  have hB := v.B_two d hd b
  have hw := BandGeometry208.actual_band_windows (s.piece_legal v.legal d b)
    hd0 (by omega : 2 ≤ s.T d b) hET.le hB s.start
    (fun S hS => v.crooked S (s.piece_subset d b hS))
    (v.low d hd b) (v.high d hd b) (v.small d hd b)
    (fun S hS => v.piece_sub hS)
  have hres : ∀ q ∈ Labels s d b, q.1 < d := by
    intro q hq
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hq
    exact (hw S hS).2.2.1
  have hfeasible : ∀ q ∈ Labels s d b,
      s.T d b-s.E d b+q.2*s.B d b ≤ high/d := by
    intro q hq
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hq
    exact ((hw S hS).2.2.2).trans (Nat.div_le_div_right hN)
  have hh := WitnessWindows80470.actual_witness_window_count
    (N:=s.N) (d:=d) (B:=s.B d b) (V:=s.U d b+s.B d b-3)
    (Q:=high/d) (A:=s.T d b-s.E d b) (I:=Labels s d b)
    hd0 (by omega) (by omega) hres hfeasible hW
  have labels : (Labels s d b).filter (Hits s d b A₀) =
      (Labels s d b).filter (fun q =>
        (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3) q∩A₀).Nonempty) := by
    ext q
    simp only [Finset.mem_filter,Hits,Window]
  rw [labels]
  exact hh

theorem actual_cost_bound {s : System} (v : Valid s) {d high W : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band) (hN : s.N ≤ high)
    {A₀ : Finset ℤ} (hW : A₀.card ≤ W) :
    CostSum s d b A₀ W ≤
      min (Base high d (s.T d b) (s.E d b) (s.B d b) (s.U d b)
        (s.U d b+s.B d b-3))
      (Candidate high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W) := by
  apply le_min
  · have hb := actual_base_bound (W:=s.U d b+s.B d b-3) v hd b hN
    apply le_trans (b:=∑ q ∈ Labels s d b,
      min (Threshold s d b q) (s.U d b+s.B d b-3)) ?_ hb
    apply Finset.sum_le_sum
    intro q hq
    rw [min_eq_left (threshold_cap s d b q)]
    exact WitnessCredit80470.cost_le_threshold _ _ _
  · have hc := WitnessCredit80470.cost_sum_upper (Labels s d b)
      (Threshold s d b) W (min (s.U d b+s.B d b-3) (high/d+s.E d b))
      (Overlap high d (s.T d b) (s.E d b) (s.B d b) (s.U d b))
      (Hits s d b A₀) (fun q hq => threshold_upper hN b q)
      (actual_hit_bound v hd b hN hW)
    exact hc.trans (Nat.add_le_add_right (actual_base_bound v hd b hN) _)

theorem actual_piece_bound {s : System} (v : Valid s) {d high W : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band) (hN : s.N ≤ high)
    {F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlegal : Legal (Ground s.N) F) (hsub : s.F ⊆ F)
    (hA : A₀ ∈ F) (hW : A₀.card ≤ W) :
    ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(PhaseSystem82427.Heavy s d b).card ≤
      (Bound high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W : ℝ)+
        (PhaseSystem82427.HeavyPiece s d b).card := by
  have hc := WitnessPieceCredit80470.actual_piece_credit v hd b hlegal hsub hA hW
  have hb : WitnessPieceCredit80470.Light s d b A₀ W ≤
      (Bound high d (s.T d b) (s.E d b) (s.B d b) (s.U d b) W : ℝ) := by
    by_cases he : s.E d b ≤ 1
    · simp only [WitnessPieceCredit80470.Light,Bound,if_pos he,Nat.cast_zero,le_refl]
    · simp only [WitnessPieceCredit80470.Light,Bound,if_neg he]
      exact_mod_cast actual_cost_bound v hd b hN hW
  linarith only [hc,hb]

#print axioms indices_mono
#print axioms weight_sum
#print axioms threshold_cap
#print axioms threshold_upper
#print axioms capped_threshold
#print axioms actual_base_bound
#print axioms actual_hit_bound
#print axioms actual_cost_bound
#print axioms actual_piece_bound
end
end JSP233.WitnessPieceBound80470
