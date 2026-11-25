module

public import Erdos272.Resources.N86412.CorrelatedSource86412

@[expose] public section

namespace JSP233.SourceDynamicData86412
open CorrelatedSource86412
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def queries : List Plan := [
  ⟨89, 2, 4392, 12⟩,
  ⟨89, 3, 6465, 15⟩,
  ⟨89, 4, 8368, 17⟩,
  ⟨89, 5, 10450, 20⟩,
  ⟨89, 7, 13657, 23⟩,
  ⟨89, 9, 16857, 25⟩,
  ⟨89, 11, 19591, 27⟩,
  ⟨89, 13, 21762, 29⟩,
  ⟨89, 15, 24045, 31⟩,
  ⟨89, 17, 25823, 32⟩,
  ⟨89, 19, 27113, 33⟩,
  ⟨89, 21, 28094, 34⟩,
  ⟨89, 23, 29112, 34⟩,
  ⟨89, 26, 29652, 34⟩,
  ⟨155, 5, 32658, 26⟩,
  ⟨133, 8, 35822, 30⟩,
  ⟨155, 7, 43164, 31⟩,
  ⟨155, 7, 44088, 32⟩,
  ⟨155, 8, 49320, 33⟩,
  ⟨155, 9, 54464, 35⟩,
  ⟨155, 9, 56094, 35⟩,
  ⟨133, 15, 60564, 41⟩,
  ⟨90, 4, 8620, 18⟩,
  ⟨90, 10, 18730, 27⟩,
  ⟨90, 16, 25648, 32⟩,
  ⟨90, 24, 30325, 35⟩,
  ⟨157, 7, 44770, 31⟩,
  ⟨157, 9, 57032, 36⟩,
  ⟨130, 4, 18736, 22⟩,
  ⟨130, 19, 68381, 44⟩,
  ⟨130, 34, 91188, 52⟩]

def query (i : ℕ) : Plan := (queries[i]?).getD ⟨0,0,0,0⟩

theorem checked0 : (List.range 16).all (fun j => decide (Conditions (query (0+j)))) = true := by decide +kernel
#print axioms checked0

theorem piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 16) : Conditions (query i) := by
  have hm : i-0 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked0 (i-0) hm)
  have he : 0+(i-0) = i := by omega
  simpa only [he] using hc
#print axioms piece0

theorem checked1 : (List.range 15).all (fun j => decide (Conditions (query (16+j)))) = true := by decide +kernel
#print axioms checked1

theorem piece1 {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 31) : Conditions (query i) := by
  have hm : i-16 ∈ List.range 15 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked1 (i-16) hm)
  have he : 16+(i-16) = i := by omega
  simpa only [he] using hc
#print axioms piece1

theorem conditions {i : ℕ} (hi : i < 31) : Conditions (query i) := by
  by_cases h0 : i < 16
  · exact piece0 (by omega) h0
  exact piece1 (by omega) hi
#print axioms conditions
end
end JSP233.SourceDynamicData86412
