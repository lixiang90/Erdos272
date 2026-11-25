module

public import Erdos272.Resources.N118533.CorrelatedSource118533

@[expose] public section

namespace JSP233.SourceQueryData118533
open CorrelatedSource118533
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def queries : List Plan := [
  ⟨104, 1, 2979, 10⟩,
  ⟨104, 4, 11156, 21⟩,
  ⟨198, 1, 11156, 14⟩,
  ⟨104, 10, 24354, 31⟩,
  ⟨208, 2, 24354, 20⟩,
  ⟨298, 1, 24354, 17⟩,
  ⟨104, 18, 36469, 39⟩,
  ⟨362, 1, 36469, 19⟩,
  ⟨104, 28, 44219, 44⟩,
  ⟨208, 4, 44219, 28⟩,
  ⟨397, 1, 44219, 20⟩,
  ⟨182, 6, 52652, 33⟩,
  ⟨433, 1, 52652, 21⟩,
  ⟨182, 7, 60444, 35⟩,
  ⟨462, 1, 60444, 21⟩,
  ⟨182, 8, 68380, 38⟩,
  ⟨491, 1, 68380, 22⟩,
  ⟨182, 9, 75936, 40⟩,
  ⟨517, 1, 75936, 23⟩,
  ⟨182, 10, 83468, 43⟩,
  ⟨520, 2, 83468, 24⟩,
  ⟨542, 1, 83468, 23⟩,
  ⟨156, 17, 90874, 49⟩,
  ⟨312, 4, 90874, 32⟩,
  ⟨565, 1, 90874, 24⟩,
  ⟨156, 19, 97010, 51⟩,
  ⟨312, 4, 97010, 33⟩,
  ⟨583, 1, 97010, 24⟩,
  ⟨156, 20, 102866, 53⟩,
  ⟨312, 4, 102866, 34⟩,
  ⟨600, 1, 102866, 24⟩,
  ⟨107, 1, 3169, 10⟩,
  ⟨107, 14, 33391, 36⟩,
  ⟨214, 3, 33391, 24⟩,
  ⟨347, 1, 33391, 18⟩,
  ⟨107, 28, 47710, 46⟩,
  ⟨214, 4, 47710, 29⟩,
  ⟨412, 1, 47710, 20⟩,
  ⟨187, 8, 69152, 38⟩,
  ⟨494, 1, 69152, 22⟩,
  ⟨535, 1, 81328, 23⟩,
  ⟨160, 18, 97138, 51⟩,
  ⟨321, 4, 97138, 33⟩,
  ⟨583, 1, 97138, 24⟩,
  ⟨160, 20, 107942, 53⟩,
  ⟨321, 4, 107942, 35⟩,
  ⟨614, 1, 107942, 25⟩,
  ⟨130, 14, 52457, 41⟩,
  ⟨260, 3, 52457, 27⟩,
  ⟨432, 1, 52457, 21⟩,
  ⟨130, 32, 84586, 55⟩,
  ⟨260, 5, 84586, 34⟩,
  ⟨545, 1, 84586, 23⟩,
  ⟨227, 9, 120996, 45⟩,
  ⟨650, 1, 120996, 25⟩]

def query (i : ℕ) : Plan := (queries[i]?).getD ⟨0,0,0,0⟩

theorem checked0 : (List.range 16).all (fun j => decide (Conditions (query (0+j)))) = true := by decide +kernel
#print axioms checked0

theorem piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 16) : Conditions (query i) := by
  have hm : i-0 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked0 (i-0) hm)
  have he : 0+(i-0) = i := by omega
  simpa only [he] using hc
#print axioms piece0

theorem checked1 : (List.range 16).all (fun j => decide (Conditions (query (16+j)))) = true := by decide +kernel
#print axioms checked1

theorem piece1 {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 32) : Conditions (query i) := by
  have hm : i-16 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked1 (i-16) hm)
  have he : 16+(i-16) = i := by omega
  simpa only [he] using hc
#print axioms piece1

theorem checked2 : (List.range 16).all (fun j => decide (Conditions (query (32+j)))) = true := by decide +kernel
#print axioms checked2

theorem piece2 {i : ℕ} (hlo : 32 ≤ i) (hhi : i < 48) : Conditions (query i) := by
  have hm : i-32 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked2 (i-32) hm)
  have he : 32+(i-32) = i := by omega
  simpa only [he] using hc
#print axioms piece2

theorem checked3 : (List.range 7).all (fun j => decide (Conditions (query (48+j)))) = true := by decide +kernel
#print axioms checked3

theorem piece3 {i : ℕ} (hlo : 48 ≤ i) (hhi : i < 55) : Conditions (query i) := by
  have hm : i-48 ∈ List.range 7 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked3 (i-48) hm)
  have he : 48+(i-48) = i := by omega
  simpa only [he] using hc
#print axioms piece3

theorem conditions {i : ℕ} (hi : i < 55) : Conditions (query i) := by
  by_cases h0 : i < 16
  · exact piece0 (by omega) h0
  by_cases h1 : i < 32
  · exact piece1 (by omega) h1
  by_cases h2 : i < 48
  · exact piece2 (by omega) h2
  exact piece3 (by omega) hi
#print axioms conditions
end
end JSP233.SourceQueryData118533
