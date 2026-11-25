module

public import Erdos272.Geometry.N82427.PhaseSystem82427
public import Erdos272.Geometry.N82427.PhaseCredit82427
public import Erdos272.Resources.ActualCleanupEval208

@[expose] public section

namespace JSP233.PhaseCleanup82427
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208
open CrossBandCredit208 CrossBandCleanup208 PhaseSystem82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem piece_credit {s : System} (v : Valid s) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band) :
    ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(Heavy s d b).card ≤
      Light s d b+(HeavyPiece s d b).card := by
  by_cases he : s.E d b ≤ 1
  · have hp := ActualBandEval208.actual_piece_empty v hd b he
    have hh : Heavy s d b=∅ := by
      unfold Heavy
      split_ifs <;> simp only [PhaseDefs82427.Heavy, System.Heavy, BandSystem208.Heavy,
        hp, Finset.image_empty, Finset.filter_empty]
    simp only [Light, if_pos he, HeavyPiece, hp, hh, Finset.filter_empty, Finset.card_empty,
      Nat.cast_zero, mul_zero, zero_add, le_refl]
  · by_cases hr : Refined s d b
    · have hd0 := (Finset.mem_Icc.mp hd).1
      have hET := v.ET d hd b
      have hB := hr.2
      have h := PhaseCredit82427.actual_light_credit (U := s.U d b) s.start MaxAPSize Defect hd0
        (by omega : 0 < s.B d b) (v.low d hd b) hET (v.small d hd b)
        (by intro S hS; have hh := maxAPSize_le_card S; unfold Defect; omega)
        (fun S hS => v.piece_sub hS)
        (fun S hS => v.legal.1 S (s.piece_subset d b hS))
        (by intro S hS; have hh := v.high d hd b S hS; omega)
      dsimp only [HeavyPiece, Heavy, Light]
      simp only [if_pos hr, if_neg he]
      exact_mod_cast h
    · simpa only [HeavyPiece, Heavy, Light, if_neg he, if_neg hr, System.HeavyPiece] using
        CrossBandCleanup208.Valid.piece_credit v hd b

theorem core_in_windows {s : System} (v : Valid s) {S : Finset ℤ} (hS : S ∈ G s) :
    s.Core S ⊆ Windows s (s.step S) := by
  have hSF := g_subset s hS
  have hd := v.step_range S hSF
  let d := s.step S
  let b := s.band S
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; dsimp only [d]; omega
  have heM := v.eM
  have he2 := v.e_two
  have hM := v.M_le d hd b
  have hET := v.ET d hd b
  have hw := BandGeometry208.actual_band_windows (s.piece_legal v.legal d b) hd0
    (by omega : 2 ≤ s.T d b) hET.le (v.B_two d hd b) s.start
    (fun R hR => v.crooked R (s.piece_subset d b hR))
    (v.low d hd b) (v.high d hd b) (v.small d hd b) (fun R hR => v.piece_sub hR)
    S (v.self_piece hSF)
  have hH := (Finset.mem_filter.mp hS).2
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_biUnion.mpr
    ⟨Code d (s.B d b) (s.start S), hH, hw.1 hx⟩⟩

theorem equal_label_disjoint {s : System} (v : Valid s) {S T : Finset ℤ}
    (hS : S ∈ G s) (hT : T ∈ G s) (hST : S ≠ T) (hstep : s.step S=s.step T)
    (hlabel : s.Label S=s.Label T) : Disjoint (S\s.Core S) (T\s.Core T) := by
  have hSF := g_subset s hS
  have hTF := g_subset s hT
  have hd := v.step_range S hSF
  let d := s.step S
  let b := s.band S
  have hb : s.band S=s.band T := congrArg Prod.fst hlabel
  have hc := congrArg Prod.snd hlabel
  have hcode : Code d (s.B d b) (s.start S)=Code d (s.B d b) (s.start T) := by
    simpa only [System.Label, ←hstep, ←hb] using hc
  have hSP : S ∈ s.Piece d b := v.self_piece hSF
  have hTP : T ∈ s.Piece d b := Finset.mem_filter.mpr ⟨hTF, hstep.symm, hb.symm⟩
  have heM := v.eM
  have he2 := v.e_two
  have hM := v.M_le d hd b
  have hET := v.ET d hd b
  have hB := v.B_two d hd b
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; dsimp only [d]; omega
  have hh := BandGeometry208.actual_band_disjoint (s.piece_legal v.legal d b) hd0
    (by omega : 2 ≤ s.T d b) hET.le (by omega : 0 < s.B d b) (v.BA d hd b) s.start
    (fun R hR => v.crooked R (s.piece_subset d b hR)) (v.low d hd b) (v.high d hd b)
    (v.small d hd b) (fun R hR => v.piece_sub hR) (v.gate d hd b) S hSP T hTP hST hcode
  simpa only [System.Core, ←hstep] using hh

theorem actual_heavy_cleanup (s : System) (v : Valid s) (Z : ℕ → Band → ℕ)
    (hZ : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : Band, ((Heavy s d b).biUnion
      (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3))).card ≤ Z d b) :
    ((G s).card : ℝ) ≤ (s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
      (253/35 : ℝ)*s.N+
      ((∑ d ∈ Finset.Icc 1 s.D, (∑ b : Band, (Heavy s d b).card)*
        (min s.N (∑ b : Band, Z d b)+(s.e-1)) : ℕ) : ℝ) := by
  have hG : Legal (Ground s.N) (G s) :=
    ⟨fun S hS => v.legal.1 S (g_subset s hS),
      fun S hS T hT hST => v.legal.2 S (g_subset s hS) T (g_subset s hT) hST⟩
  have hstep : ∀ S ∈ G s, s.step S ∈ Finset.Icc 1 s.D := fun S hS => v.step_range S (g_subset s hS)
  have heM := v.eM
  have he2 := v.e_two
  have hAP : ∀ S ∈ G s, ∃ a : ℤ, APAt (s.step S : ℤ) a (s.Core S) := by
    intro S hS
    exact ⟨s.start S, grid_APAt _ _ _ (by have := (Finset.mem_Icc.mp (hstep S hS)).1; omega)⟩
  have hne : ∀ S ∈ G s, (s.Core S).Nonempty := by
    intro S hS
    apply Finset.card_pos.mp
    rw [v.core_card (g_subset s hS)]
    have hs := v.size (g_subset s hS)
    have hm := two_le_maxAPSize (show 2 ≤ S.card by omega)
    omega
  have hmax : ∀ S ∈ G s, ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ (s.Core S).card := by
    intro S hS R hR hRS
    rw [v.core_card (g_subset s hS)]
    exact AP_card_le_max hR hRS
  have hsmall : ∀ S ∈ G s, (S\s.Core S).card < s.e := by
    intro S hS
    have hSF := g_subset s hS
    rw [v.remainder hSF]
    exact (v.small _ (v.step_range S hSF) _ S (v.self_piece hSF)).trans_le
      (v.E_le _ (v.step_range S hSF) _)
  have hp := NearResidual208.actual_near_payment hG v.e_two v.eM s.Core s.step hstep
    (fun S hS => v.sub S (g_subset s hS)) hAP hne hmax
    (fun S hS => v.size (g_subset s hS)) (fun S hS => v.crooked S (g_subset s hS)) hsmall
    (Windows s) (fun S hS => core_in_windows v hS) s.Label (Labels s)
    (fun S hS => label_mem s hS)
    (fun S hS T hT hST hstep hlabel => equal_label_disjoint v hS hT hST hstep hlabel)
  have hb : (∑ d ∈ Finset.Icc 1 s.D, (Labels s d).card*((Windows s d).card+(s.e-1))) ≤
      ∑ d ∈ Finset.Icc 1 s.D, (∑ b : Band, (Heavy s d b).card)*
        (min s.N (∑ b : Band, Z d b)+(s.e-1)) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [labels_card]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (windows_card s d (Z d) (hZ d hd)) (s.e-1))
  have hbR := (show ((∑ d ∈ Finset.Icc 1 s.D, (Labels s d).card*((Windows s d).card+(s.e-1)) : ℕ) : ℝ) ≤
      ((∑ d ∈ Finset.Icc 1 s.D, (∑ b : Band, (Heavy s d b).card)*
        (min s.N (∑ b : Band, Z d b)+(s.e-1)) : ℕ) : ℝ) by exact_mod_cast hb)
  linarith only [hp, hbR]

#print axioms piece_credit
#print axioms core_in_windows
#print axioms equal_label_disjoint
#print axioms actual_heavy_cleanup
end
end JSP233.PhaseCleanup82427
