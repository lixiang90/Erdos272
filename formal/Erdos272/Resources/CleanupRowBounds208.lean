module

public import Erdos272.Resources.CleanupChecked208
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.CleanupRowBounds208
open CleanupEval208
open scoped BigOperators
set_option maxHeartbeats 0

theorem range_sum_Icc {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    (∑ k∈Finset.range n,f (1+k))=∑ d∈Finset.Icc 1 n,f d := by
  have hh := Finset.sum_Ico_add f 0 n 1
  simpa only [Nat.Ico_zero_eq_range,Nat.zero_add,Finset.Ico_add_one_right_eq_Icc] using hh

theorem good_Icc {r : Row} {n : ℕ} {out : Totals} (h : ChunkFacts r 1 n out)
    {d : ℕ} (hd : d∈Finset.Icc 1 n) : (step r d).good=true := by
  obtain ⟨h1,hn⟩ := Finset.mem_Icc.mp hd
  have hh := h.good (d-1) (by omega)
  have he : 1+(d-1)=d := by omega
  simpa only [he] using hh

theorem net_eq_Icc {r : Row} {n : ℕ} {out : Totals} (h : ChunkFacts r 1 n out) :
    out.net=∑ d∈Finset.Icc 1 n,(step r d).totals.net :=
  h.net_eq.trans (range_sum_Icc (fun d=>(step r d).totals.net) n)

theorem light_eq_Icc {r : Row} {n : ℕ} {out : Totals} (h : ChunkFacts r 1 n out) :
    out.light=∑ d∈Finset.Icc 1 n,(step r d).totals.light :=
  h.light_eq.trans (range_sum_Icc (fun d=>(step r d).totals.light) n)

theorem normalized_row_bound {r : Row} {n : ℕ} {out : Totals} (h : ChunkFacts r 1 n out)
    (fee : ℕ → ℝ)
    (hfee : ∀ d∈Finset.Icc 1 n,fee d≤((step r d).totals.net : ℝ)/r.grid) :
    (∑ d∈Finset.Icc 1 n,fee d)≤(out.net : ℝ)/r.grid := by
  have hh := Finset.sum_le_sum hfee
  have he : (((∑ d∈Finset.Icc 1 n,(step r d).totals.net) : ℕ) : ℝ)/r.grid=
      ∑ d∈Finset.Icc 1 n,((step r d).totals.net : ℝ)/r.grid := by
    rw [Nat.cast_sum,Finset.sum_div]
  rw [←he,←net_eq_Icc h] at hh
  exact hh

#print axioms good_Icc
#print axioms normalized_row_bound
end JSP233.CleanupRowBounds208
