module

public import Erdos272.Arithmetic.N233811.RowGeometry233811
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section

namespace JSP233.SourceData233811W0
open CleanupRows233811
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def potential (n : ℕ) : ℕ :=
  if n=0 then 0 else (data (0+min (n-1) 6)).potential

def Psi (n : ℕ) : ℝ := potential n
def G : ℝ := 1/(6*215106)

def CoeffA : ℝ := 234516172396681/21510600000000000

def CoeffB : ℝ := 253164819780471484037/250957000000000000

def CoeffC : ℝ := 132259449602195/35851

def SourceUpper (N : ℕ) : ℝ := CoeffA*(N : ℝ)^2+CoeffB*N+CoeffC

theorem links {i : ℕ} (hi : i < 7) :
    (data (0+i)).row.low = 236005 ∧ (data (0+i)).row.high = 241005 ∧
    (data (0+i)).memberFloor = 145 ∧ potential (i+1) = (data (0+i)).potential := by
  interval_cases i <;> decide +kernel

theorem psi_mono : Monotone Psi := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 7
  · have hh : potential n ≤ potential (n+1) := by
      interval_cases n <;> decide +kernel
    dsimp only [Psi]
    exact_mod_cast hh
  · have h0 : n ≠ 0 := by omega
    have h1 : n+1 ≠ 0 := by omega
    have hm0 : min (n-1) 6 = 6 := by omega
    have hm1 : min (n+1-1) 6 = 6 := by omega
    simp only [Psi, potential, if_neg h0, if_neg h1, hm0, hm1, le_refl]

theorem psi_zero : Psi 0 = 0 := by simp [Psi, potential]

theorem reciprocal : 6*G*Psi 7 = 1 := by
  norm_num [G, Psi, potential, data, data06]

theorem g_positive : 0 < G := by norm_num [G]

#print axioms links
#print axioms psi_mono
#print axioms psi_zero
#print axioms reciprocal
#print axioms g_positive
end
end JSP233.SourceData233811W0
