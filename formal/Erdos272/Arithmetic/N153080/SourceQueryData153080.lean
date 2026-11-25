module

public import Erdos272.Resources.N158375.CorrelatedSource158375

@[expose] public section

namespace JSP233.SourceQueryData153080
open CorrelatedSource158375
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def queries : List Plan := [
  ⟨118, 1, 3811, 11⟩,
  ⟨118, 4, 14320, 21⟩,
  ⟨165, 2, 14320, 18⟩,
  ⟨225, 1, 14320, 15⟩,
  ⟨354, 1, 14320, 12⟩,
  ⟨590, 1, 14320, 9⟩,
  ⟨1180, 1, 14320, 7⟩,
  ⟨3776, 1, 14320, 4⟩,
  ⟨118, 11, 34349, 35⟩,
  ⟨165, 5, 34349, 28⟩,
  ⟨236, 3, 34349, 23⟩,
  ⟨353, 1, 34349, 18⟩,
  ⟨590, 1, 34349, 14⟩,
  ⟨1180, 1, 34349, 10⟩,
  ⟨3776, 1, 34349, 6⟩,
  ⟨118, 21, 53388, 45⟩,
  ⟨165, 8, 53388, 35⟩,
  ⟨236, 4, 53388, 29⟩,
  ⟨354, 2, 53388, 23⟩,
  ⟨438, 1, 53388, 21⟩,
  ⟨1180, 1, 53388, 13⟩,
  ⟨3776, 1, 53388, 7⟩,
  ⟨118, 31, 63368, 49⟩,
  ⟨165, 10, 63368, 39⟩,
  ⟨236, 5, 63368, 31⟩,
  ⟨354, 2, 63368, 25⟩,
  ⟨476, 1, 63368, 21⟩,
  ⟨1180, 1, 63368, 14⟩,
  ⟨3776, 1, 63368, 8⟩,
  ⟨118, 57, 80402, 57⟩,
  ⟨165, 13, 80402, 44⟩,
  ⟨236, 6, 80402, 35⟩,
  ⟨354, 3, 80402, 28⟩,
  ⟨535, 1, 80402, 23⟩,
  ⟨1180, 1, 80402, 15⟩,
  ⟨3776, 1, 80402, 9⟩,
  ⟨118, 63, 93624, 63⟩,
  ⟨165, 16, 93624, 48⟩,
  ⟨236, 7, 93624, 39⟩,
  ⟨354, 3, 93624, 31⟩,
  ⟨576, 1, 93624, 24⟩,
  ⟨1180, 1, 93624, 17⟩,
  ⟨3776, 1, 93624, 10⟩,
  ⟨118, 69, 108994, 69⟩,
  ⟨165, 19, 108994, 53⟩,
  ⟨236, 8, 108994, 42⟩,
  ⟨354, 4, 108994, 33⟩,
  ⟨590, 2, 108994, 25⟩,
  ⟨621, 1, 108994, 25⟩,
  ⟨3776, 1, 108994, 10⟩,
  ⟨118, 73, 119416, 73⟩,
  ⟨165, 21, 119416, 56⟩,
  ⟨236, 9, 119416, 44⟩,
  ⟨354, 4, 119416, 35⟩,
  ⟨590, 2, 119416, 26⟩,
  ⟨649, 1, 119416, 25⟩,
  ⟨3776, 1, 119416, 11⟩,
  ⟨118, 77, 131594, 77⟩,
  ⟨165, 25, 131594, 59⟩,
  ⟨236, 10, 131594, 46⟩,
  ⟨354, 4, 131594, 37⟩,
  ⟨590, 2, 131594, 28⟩,
  ⟨681, 1, 131594, 26⟩,
  ⟨3776, 1, 131594, 11⟩]

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

theorem checked3 : (List.range 16).all (fun j => decide (Conditions (query (48+j)))) = true := by decide +kernel
#print axioms checked3

theorem piece3 {i : ℕ} (hlo : 48 ≤ i) (hhi : i < 64) : Conditions (query i) := by
  have hm : i-48 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked3 (i-48) hm)
  have he : 48+(i-48) = i := by omega
  simpa only [he] using hc
#print axioms piece3

theorem conditions {i : ℕ} (hi : i < 64) : Conditions (query i) := by
  by_cases h0 : i < 16
  · exact piece0 (by omega) h0
  by_cases h1 : i < 32
  · exact piece1 (by omega) h1
  by_cases h2 : i < 48
  · exact piece2 (by omega) h2
  exact piece3 (by omega) hi
#print axioms conditions
end
end JSP233.SourceQueryData153080
