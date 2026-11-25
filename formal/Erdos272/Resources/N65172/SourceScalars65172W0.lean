module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Erdos272.Counting.N65172.ScalarUpper65172

@[expose] public section

namespace JSP233.SourceScalars65172W0
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

open CleanupRows65172

def Witness : ℕ := 77
def potential (n : ℕ) : ℕ :=
  if n=0 then 0 else if n=1 then 1778 else (data (0+min (n-2) 23)).potential
def Psi (n : ℕ) : ℝ := potential n
def G : ℝ := 1/263214
def CoeffA : ℝ := 876327387706013/43869000000000000
def CoeffB : ℝ := 2039969097408552053/21934500000000000
def CoeffC : ℝ := 10266038555830/43869
def SourceUpper (N : ℕ) : ℝ := CoeffA*(N : ℝ)^2+CoeffB*N+CoeffC

def Cost (N i : ℕ) : ℝ := if i=0 then 0 else ScalarUpper65172.Upper N (0+(i-1))
def Weighted (N : ℕ) : ℝ := 6*G*(∑ i∈Finset.range 25, (Psi (i+1)-Psi i)*Cost N i)

def Delta (i : ℕ) : ℤ := (potential (i+2) : ℤ)-(potential (i+1) : ℤ)
def Residual (i : ℕ) : ℤ := (data (0+i)).residualUnits
def Net (i : ℕ) : ℤ := (data (0+i)).total.net
def Cap (i : ℕ) : ℤ := (WitnessNumeric65172.data (0+i)).cap
def AccR : ℤ := ∑ i∈Finset.range 24, Delta i*Residual i
def AccNet : ℤ := ∑ i∈Finset.range 24, Delta i*Net i
def AccCap : ℤ := ∑ i∈Finset.range 24, Delta i*Cap i
def AccMass : ℤ := ∑ i∈Finset.range 24, Delta i

theorem accumulated_residual : AccR=876327387706013 := by decide +kernel
#print axioms accumulated_residual

theorem accumulated_net : AccNet=3775680394817104106 := by decide +kernel
#print axioms accumulated_net

theorem accumulated_cap : AccCap=10266038555830 := by decide +kernel
#print axioms accumulated_cap

theorem accumulated_mass : AccMass=42091 := by decide +kernel
#print axioms accumulated_mass

theorem fee (N : ℕ) : Weighted N=SourceUpper N := by
  change 6*G*(∑ i∈Finset.range (24+1), ((potential (i+1) : ℝ)-potential i)*
    (if i=0 then 0 else ScalarUpper65172.Upper N (0+(i-1))))=_
  rw [IntegerFeeNat65968.zero_head potential (fun i => ScalarUpper65172.Upper N (0+i)) 24]
  simp only [ScalarUpper65172.Upper,IntegerFeeNat65968.upper_cast]
  change 6*G*(∑ i∈Finset.range 24, (Delta i : ℝ)*
    IntegerFee65968.Upper N 1000000000000 (253/35) (Residual i) (Net i) (Cap i))=_
  rw [IntegerFee65968.integer_coefficients]
  change 6*G*((AccR : ℝ)/1000000000000*(N : ℝ)^2+
    ((253/35 : ℝ)*(AccMass : ℝ)+(AccNet : ℝ)/1000000000000)*N+(AccCap : ℝ))=_
  rw [accumulated_residual,accumulated_net,accumulated_cap,accumulated_mass]
  norm_num [G,SourceUpper,CoeffA,CoeffB,CoeffC]
  ring
#print axioms fee

theorem links {i : ℕ} (hi : i<24) :
    (data (0+i)).row.low=65172 ∧ (data (0+i)).row.high=66834 ∧
    (data (0+i)).memberFloor=78 ∧ potential (i+2)=(data (0+i)).potential := by
  interval_cases i <;> decide +kernel
#print axioms links

theorem psi_mono : Monotone Psi := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n<25
  · have hh : potential n≤potential (n+1) := by interval_cases n <;> decide +kernel
    dsimp only [Psi]
    exact_mod_cast hh
  · have h0 : n≠0 := by omega
    have h1 : n≠1 := by omega
    have h2 : n+1≠0 := by omega
    have h3 : n+1≠1 := by omega
    have hm0 : min (n-2) 23=23 := by omega
    have hm1 : min (n+1-2) 23=23 := by omega
    simp only [Psi,potential,if_neg h0,if_neg h1,if_neg h2,if_neg h3,hm0,hm1,le_refl]
#print axioms psi_mono

theorem psi_zero : Psi 0=0 := by simp [Psi,potential]
#print axioms psi_zero
theorem reciprocal : 6*G*Psi 25=1 := by norm_num [G,Psi,potential,data,data23]
#print axioms reciprocal
theorem g_positive : 0<G := by norm_num [G]
#print axioms g_positive

theorem upper_mono {N H : ℕ} (h : N≤H) : SourceUpper N≤SourceUpper H := by
  have hn : (N : ℝ)≤H := by exact_mod_cast h
  have hs:=pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) N) hn 2
  have ha:=mul_le_mul_of_nonneg_left hs (by norm_num [CoeffA] : 0≤CoeffA)
  have hb:=mul_le_mul_of_nonneg_left hn (by norm_num [CoeffB] : 0≤CoeffB)
  unfold SourceUpper
  exact add_le_add (add_le_add ha hb) (le_refl CoeffC)
#print axioms upper_mono
end
end JSP233.SourceScalars65172W0
