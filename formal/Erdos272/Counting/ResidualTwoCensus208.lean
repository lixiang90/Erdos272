import Erdos272.Counting.ResidualCensus208
import Erdos272.Resources.ResidualPrice208

namespace JSP233.ResidualTwoCensus208
open StepClass208 StepCensus208 ResidualSpan208 ResidualCensus208 ResidualPrice208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def H (M b : ℕ) : ℝ := ∑ p ∈ Classes,
  Rho p*(1/((M-b : ℕ) : ℝ)+1/(Span (M-b) b p : ℝ))

theorem integer_gate_upper (N d k : ℕ) :
    (if (d : ℤ)*(k : ℤ) ≤ (N : ℤ)-1 then 1 else 0 : ℕ) ≤
      (if d*k ≤ N then 1 else 0) := by
  by_cases hz : (d : ℤ)*(k : ℤ) ≤ (N : ℤ)-1
  · have hZ : ((d*k : ℕ) : ℤ) ≤ (N : ℤ) := by push_cast; omega
    have hnat : d*k ≤ N := by exact_mod_cast hZ
    rw [if_pos hz,if_pos hnat]
  · rw [if_neg hz]
    exact Nat.zero_le _

theorem occupancy_census (N D M b : ℕ) (hb : b < M) :
    ((∑ d ∈ Finset.Icc 1 D, Occupancy N M d b : ℕ) : ℝ) ≤
      (N : ℝ)*H M b+253/35 := by
  let a := M-b
  have ha : 0 < a := by dsimp [a]; omega
  have hspan : ∀ p ∈ Classes, 0 < Span a b p := by
    intro p hp
    exact lt_of_lt_of_le ha (span_ge a b p)
  have hpoint : ∀ d ∈ Finset.Icc 1 D, Occupancy N M d b ≤
      (if d*a ≤ N then 1 else 0)+(if d*Span a b (PrimeGate d) ≤ N then 1 else 0) := by
    intro d hd
    exact Nat.add_le_add (integer_gate_upper N d a)
      (integer_gate_upper N d (Span a b (PrimeGate d)))
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hs
  have hsR : ((∑ d ∈ Finset.Icc 1 D, Occupancy N M d b : ℕ) : ℝ) ≤
      ((∑ d ∈ Finset.Icc 1 D, if d*a ≤ N then 1 else 0 : ℕ) : ℝ)+
      ((∑ d ∈ Finset.Icc 1 D, if d*Span a b (PrimeGate d) ≤ N then 1 else 0 : ℕ) : ℝ) := by
    exact_mod_cast hs
  have hfirst := gate_cut_real_upper N D (fun _ => a) (fun p hp => ha)
  have hsecond := gate_cut_real_upper N D (fun p => Span a b p) hspan
  have he : (∑ p ∈ Classes, Rho p/a)+(∑ p ∈ Classes, Rho p/(Span a b p : ℝ))=H M b := by
    rw [← Finset.sum_add_distrib]
    unfold H
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [a]
    ring
  have hc : 2*(∑ p ∈ Classes, Error p)=(253/35 : ℝ) := period_error_sum
  have hN : (N : ℝ)*(∑ p ∈ Classes, Rho p/a)+
      (N : ℝ)*(∑ p ∈ Classes, Rho p/(Span a b p : ℝ))=(N : ℝ)*H M b := by
    rw [← mul_add,he]
  linarith only [hsR,hfirst,hsecond,hN,hc]

#print axioms integer_gate_upper
#print axioms occupancy_census
end
end JSP233.ResidualTwoCensus208
