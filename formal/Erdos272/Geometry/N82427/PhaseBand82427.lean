module

public import Erdos272.Geometry.N82427.PhaseProperties82427
public import Erdos272.Geometry.N82427.PhaseSystem82427
public import Erdos272.Resources.ActualBandEval208

@[expose] public section

namespace JSP233.PhaseBand82427
open StarCompletion APGeometry NearAP36 SourceBridge208
open CrossBandCredit208 CrossBandCleanup208 CrossBandMenu208 PhaseSystem82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def RawWindows (s : System) (d : ℕ) (b : Band) : ℕ :=
  ((Heavy s d b).biUnion
    (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3))).card

theorem actual_properties {s : System} (v : Valid s) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band) (he : 2 ≤ s.E d b) :
    BandSystem208.Properties s.N d (s.T d b-s.E d b) (s.B d b)
      (s.U d b+s.B d b-3) (s.E d b) (Heavy s d b) := by
  have hd0 := (Finset.mem_Icc.mp hd).1
  have hM := v.M_le d hd b
  have heM := v.eM
  have he2 := v.e_two
  have hET := v.ET d hd b
  dsimp only [Heavy]
  split_ifs with hr
  · exact PhaseProperties82427.actual_properties (s.piece_legal v.legal d b) hd0
      (by omega : 2 ≤ s.T d b) hET.le hr.1 (v.TU d hd b) hr.2 (v.BA d hd b)
      s.start (fun S hS => v.crooked S (s.piece_subset d b hS))
      (v.low d hd b) (v.high d hd b) (v.small d hd b) (fun S hS => v.piece_sub hS)
      (v.gate d hd b)
  · exact BandSystem208.actual_properties (s.piece_legal v.legal d b) hd0
      (by omega : 2 ≤ s.T d b) hET.le (by omega : 1 ≤ s.E d b)
      (v.TU d hd b) (v.B_two d hd b) (v.BA d hd b) s.start
      (fun S hS => v.crooked S (s.piece_subset d b hS))
      (v.low d hd b) (v.high d hd b) (v.small d hd b) (fun S hS => v.piece_sub hS)
      (v.gate d hd b)

theorem actual_band_value {s : System} (v : Valid s) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band) (r : CleanupEval208.Row) (q : CleanupEval208.Band)
    (hT : q.T=s.T d b) (hE : q.E=s.E d b) (hU : q.U=s.U d b)
    (hB : CleanupEval208.block q d=s.B d b)
    (hgood : CleanupEval208.BandGood r d q (CleanupEval208.bandValue r d q))
    (hgrid : 0 < r.grid) (hlow : 0 < r.low) (hlN : r.low ≤ s.N) (hNh : s.N ≤ r.high) :
    (Heavy s d b).card ≤ (CleanupEval208.bandValue r d q).count ∧
      (RawWindows s d b : ℝ)/s.N ≤ ((CleanupEval208.bandValue r d q).windows : ℝ)/r.grid := by
  by_cases he : s.E d b ≤ 1
  · have hp := ActualBandEval208.actual_piece_empty v hd b he
    have hh : Heavy s d b=∅ := by
      unfold Heavy
      split_ifs <;> simp only [PhaseDefs82427.Heavy, System.Heavy, BandSystem208.Heavy,
        hp, Finset.image_empty, Finset.filter_empty]
    have hq : q.E ≤ 1 := by simpa only [hE] using he
    simp only [hh, Finset.card_empty, Nat.zero_le, RawWindows, Finset.biUnion_empty,
      Nat.cast_zero, zero_div, CleanupEval208.bandValue, if_pos hq,
      CleanupEval208.bandZero, le_refl, and_self]
  · have he2 : 2 ≤ s.E d b := by omega
    have hq : ¬q.E ≤ 1 := by simpa only [hE] using he
    have hET := v.ET d hd b
    have hB2 := v.B_two d hd b
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hp := actual_properties v hd b he2
    have hTV : s.T d b < SizeV s d b := by
      have hh := hgood.2.2.2.2.2.2.1
      simpa only [hT, hU, hB, SizeV] using hh
    have hV0 : 0 < SizeV s d b := by omega
    have hEV : s.E d b < SizeV s d b := by omega
    have hAJ : s.T d b-s.E d b ≤ SizeV s d b-s.E d b-1 := by omega
    have hc := CleanupWindowBounds208.actual_window_bounds hp hd0 (by omega : 0 < s.B d b)
      hV0 hEV hAJ (Nat.div_le_div_right (c := d) hlN) (Nat.div_le_div_right (c := d) hNh)
    have hz := BandWindowRatio208.actual_window_ratio hp hd0 (by omega : 0 < s.B d b)
      hV0 hEV hAJ hgrid hlow hlN hNh
    simp only [CleanupEval208.bandValue, if_neg hq]
    refine ⟨?_, ?_⟩
    · simpa only [hT, hE, hU, hB, SizeV] using hc.1
    · simpa only [hT, hE, hU, hB, RawWindows, SizeV,
        BandWindowRatio208.OrdinaryGrid, BandWindowRatio208.RightGrid] using hz

#print axioms actual_properties
#print axioms actual_band_value
end
end JSP233.PhaseBand82427
