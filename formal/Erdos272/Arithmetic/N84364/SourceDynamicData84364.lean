module

public import Erdos272.Resources.N86412.CorrelatedSource86412

@[expose] public section

namespace JSP233.SourceDynamicData84364
open CorrelatedSource86412
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def queries : List Plan := [
  ⟨88, 2, 4310, 12⟩,
  ⟨88, 4, 8360, 17⟩,
  ⟨88, 6, 11706, 21⟩,
  ⟨88, 8, 14984, 24⟩,
  ⟨88, 10, 17810, 26⟩,
  ⟨88, 14, 22442, 30⟩,
  ⟨88, 16, 24304, 31⟩,
  ⟨88, 19, 26106, 33⟩,
  ⟨88, 22, 27899, 34⟩,
  ⟨88, 25, 28545, 34⟩,
  ⟨132, 9, 39616, 32⟩,
  ⟨132, 10, 42260, 33⟩,
  ⟨132, 11, 46400, 35⟩,
  ⟨132, 12, 48766, 36⟩,
  ⟨132, 12, 50088, 37⟩,
  ⟨132, 13, 52556, 38⟩,
  ⟨132, 14, 54720, 39⟩,
  ⟨132, 14, 56546, 39⟩,
  ⟨132, 15, 57994, 40⟩,
  ⟨132, 15, 59288, 40⟩,
  ⟨89, 8, 15176, 24⟩,
  ⟨133, 9, 39050, 32⟩,
  ⟨133, 10, 44088, 34⟩,
  ⟨133, 11, 47172, 36⟩,
  ⟨133, 13, 53672, 38⟩,
  ⟨133, 14, 57574, 40⟩]

def query (i : ℕ) : Plan := (queries[i]?).getD ⟨0,0,0,0⟩

theorem checked0 : (List.range 16).all (fun j => decide (Conditions (query (0+j)))) = true := by decide +kernel
#print axioms checked0

theorem piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 16) : Conditions (query i) := by
  have hm : i-0 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked0 (i-0) hm)
  have he : 0+(i-0) = i := by omega
  simpa only [he] using hc
#print axioms piece0

theorem checked1 : (List.range 10).all (fun j => decide (Conditions (query (16+j)))) = true := by decide +kernel
#print axioms checked1

theorem piece1 {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 26) : Conditions (query i) := by
  have hm : i-16 ∈ List.range 10 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked1 (i-16) hm)
  have he : 16+(i-16) = i := by omega
  simpa only [he] using hc
#print axioms piece1

theorem conditions {i : ℕ} (hi : i < 26) : Conditions (query i) := by
  by_cases h0 : i < 16
  · exact piece0 (by omega) h0
  exact piece1 (by omega) hi
#print axioms conditions
end
end JSP233.SourceDynamicData84364
