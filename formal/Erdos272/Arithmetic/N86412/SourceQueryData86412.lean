module

public import Erdos272.Resources.N109474.CorrelatedSource109474

@[expose] public section

namespace JSP233.SourceQueryData86412
open CorrelatedSource109474
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def queries : List Plan := [
  ⟨178, 2, 16857, 18⟩,
  ⟨178, 3, 19591, 20⟩,
  ⟨178, 3, 21762, 21⟩,
  ⟨178, 3, 24045, 22⟩,
  ⟨178, 3, 25823, 23⟩,
  ⟨178, 4, 27113, 23⟩,
  ⟨178, 4, 28094, 24⟩,
  ⟨178, 4, 29112, 25⟩,
  ⟨178, 4, 29652, 25⟩,
  ⟨155, 5, 31074, 28⟩,
  ⟨133, 8, 33842, 32⟩,
  ⟨155, 6, 37130, 30⟩,
  ⟨155, 7, 39050, 31⟩,
  ⟨155, 7, 40362, 31⟩,
  ⟨155, 7, 41660, 32⟩,
  ⟨155, 8, 45100, 34⟩,
  ⟨155, 8, 47172, 34⟩,
  ⟨155, 8, 48308, 35⟩,
  ⟨155, 9, 51138, 36⟩,
  ⟨155, 9, 51908, 36⟩,
  ⟨155, 9, 53672, 37⟩,
  ⟨155, 10, 57574, 38⟩,
  ⟨155, 10, 58758, 39⟩,
  ⟨180, 4, 30325, 25⟩,
  ⟨157, 10, 60062, 39⟩,
  ⟨260, 4, 68381, 31⟩]

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
end JSP233.SourceQueryData86412
