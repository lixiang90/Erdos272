module

public import Erdos272.Counting.N65968.IntegerFee65968
public import Erdos272.Arithmetic.N67702.CleanupRows67702
public import Erdos272.Arithmetic.N67702.WitnessHighNumeric67702
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace JSP233.IntegerFeePilot65968
open scoped BigOperators
open CleanupRows67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Delta (i : ℕ) : ℤ := (data (64+i)).potential-
  (if i=0 then (1886 : ℤ) else (data (63+i)).potential)
def Residual (i : ℕ) : ℤ := (data (64+i)).residualUnits
def Net (i : ℕ) : ℤ := (data (64+i)).total.net
def Cap (i : ℕ) : ℤ := (WitnessHighNumeric67702.data (64+i)).cap
def AccR : ℤ := ∑ i ∈ Finset.range 32, Delta i*Residual i
def AccNet : ℤ := ∑ i ∈ Finset.range 32, Delta i*Net i
def AccCap : ℤ := ∑ i ∈ Finset.range 32, Delta i*Cap i
def AccMass : ℤ := ∑ i ∈ Finset.range 32, Delta i

theorem accumulated_r : AccR=915525610173755 := by decide +kernel
theorem accumulated_net : AccNet=4035347643425160246 := by decide +kernel
theorem accumulated_cap : AccCap=12791826120393 := by decide +kernel
theorem accumulated_mass : AccMass=45203 := by decide +kernel

def Weighted (N : ℕ) : ℝ := (1/47089 : ℝ)*
  ∑ i ∈ Finset.range 32, (Delta i : ℝ)*
    IntegerFee65968.Upper N 1000000000000 (253/35) (Residual i) (Net i) (Cap i)

theorem fee (N : ℕ) : Weighted N=
    (3736839225199/192200000000000 : ℝ)*(N : ℝ)^2+
    (15267352651988060861/164811500000000000 : ℝ)*N+
    (12791826120393/47089 : ℝ) := by
  unfold Weighted
  rw [IntegerFee65968.integer_coefficients]
  change (1/47089 : ℝ)*((AccR : ℝ)/1000000000000*(N : ℝ)^2+
    ((253/35 : ℝ)*(AccMass : ℝ)+(AccNet : ℝ)/1000000000000)*N+
    (AccCap : ℝ))=_
  rw [accumulated_r,accumulated_net,accumulated_cap,accumulated_mass]
  norm_num
  ring

#print axioms accumulated_r
#print axioms accumulated_net
#print axioms accumulated_cap
#print axioms accumulated_mass
#print axioms fee
end
end JSP233.IntegerFeePilot65968
