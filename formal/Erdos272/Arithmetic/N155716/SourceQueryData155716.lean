module

public import Erdos272.Resources.N158375.CorrelatedSource158375

@[expose] public section

namespace JSP233.SourceQueryData155716
open CorrelatedSource158375
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def queries : List Plan := [
  ⟨119, 1, 3873, 11⟩,
  ⟨119, 4, 14563, 22⟩,
  ⟨166, 2, 14563, 18⟩,
  ⟨228, 1, 14563, 15⟩,
  ⟨357, 1, 14563, 12⟩,
  ⟨595, 1, 14563, 9⟩,
  ⟨1190, 1, 14563, 7⟩,
  ⟨3808, 1, 14563, 4⟩,
  ⟨119, 11, 34977, 35⟩,
  ⟨166, 5, 34977, 28⟩,
  ⟨238, 3, 34977, 23⟩,
  ⟨357, 1, 34977, 18⟩,
  ⟨595, 1, 34977, 14⟩,
  ⟨1190, 1, 34977, 10⟩,
  ⟨3808, 1, 34977, 6⟩,
  ⟨119, 21, 54472, 45⟩,
  ⟨166, 8, 54472, 36⟩,
  ⟨238, 4, 54472, 29⟩,
  ⟨357, 2, 54472, 23⟩,
  ⟨442, 1, 54472, 21⟩,
  ⟨1190, 1, 54472, 13⟩,
  ⟨3808, 1, 54472, 7⟩,
  ⟨119, 32, 65437, 50⟩,
  ⟨166, 10, 65437, 39⟩,
  ⟨238, 5, 65437, 32⟩,
  ⟨357, 2, 65437, 25⟩,
  ⟨483, 1, 65437, 22⟩,
  ⟨1190, 1, 65437, 14⟩,
  ⟨3808, 1, 65437, 8⟩,
  ⟨119, 58, 83594, 58⟩,
  ⟨166, 13, 83594, 45⟩,
  ⟨238, 6, 83594, 36⟩,
  ⟨357, 3, 83594, 29⟩,
  ⟨545, 1, 83594, 23⟩,
  ⟨1190, 1, 83594, 16⟩,
  ⟨3808, 1, 83594, 9⟩,
  ⟨119, 64, 97168, 64⟩,
  ⟨166, 16, 97168, 49⟩,
  ⟨238, 7, 97168, 39⟩,
  ⟨357, 3, 97168, 31⟩,
  ⟨587, 1, 97168, 24⟩,
  ⟨1190, 1, 97168, 17⟩,
  ⟨3808, 1, 97168, 10⟩,
  ⟨119, 68, 107332, 68⟩,
  ⟨166, 18, 107332, 52⟩,
  ⟨238, 8, 107332, 41⟩,
  ⟨357, 4, 107332, 32⟩,
  ⟨595, 2, 107332, 25⟩,
  ⟨616, 1, 107332, 25⟩,
  ⟨3808, 1, 107332, 10⟩,
  ⟨119, 72, 118466, 72⟩,
  ⟨166, 21, 118466, 55⟩,
  ⟨238, 8, 118466, 43⟩,
  ⟨357, 4, 118466, 34⟩,
  ⟨595, 2, 118466, 26⟩,
  ⟨647, 1, 118466, 25⟩,
  ⟨3808, 1, 118466, 11⟩,
  ⟨119, 76, 129944, 76⟩,
  ⟨166, 24, 129944, 58⟩,
  ⟨238, 9, 129944, 46⟩,
  ⟨357, 4, 129944, 36⟩,
  ⟨595, 2, 129944, 28⟩,
  ⟨677, 1, 129944, 26⟩,
  ⟨3808, 1, 129944, 11⟩]

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
end JSP233.SourceQueryData155716
