module

public import Erdos272.Arithmetic.N243614.RowGeometry243614
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section

namespace JSP233.SourceWindowData243614
open CleanupRows243614
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def potential (n : ℕ) : ℕ :=
  if n=0 then 0 else (data (min (n-1) 4)).potential

def Psi (n : ℕ) : ℝ := potential n
def G : ℝ := 1/(6*225160)

def CoeffA : ℝ := 1202143985852703/112580000000000000

def CoeffB : ℝ := 308326448855792247/303100000000000

def CoeffC : ℝ := 227972464492319/56290

def SourceUpper (N : ℕ) : ℝ := CoeffA*(N : ℝ)^2+CoeffB*N+CoeffC

theorem links {i : ℕ} (hi : i < 5) :
    (data i).row.low = 246007 ∧ (data i).row.high = 251007 ∧
    (data i).memberFloor = 148 ∧ potential (i+1) = (data i).potential := by
  interval_cases i <;> decide +kernel

theorem psi_mono : Monotone Psi := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 5
  · have hh : potential n ≤ potential (n+1) := by
      interval_cases n <;> decide +kernel
    dsimp only [Psi]
    exact_mod_cast hh
  · have h0 : n ≠ 0 := by omega
    have h1 : n+1 ≠ 0 := by omega
    have hm0 : min (n-1) 4 = 4 := by omega
    have hm1 : min (n+1-1) 4 = 4 := by omega
    simp only [Psi, potential, if_neg h0, if_neg h1, hm0, hm1, le_refl]

theorem psi_zero : Psi 0 = 0 := by simp [Psi, potential]

theorem reciprocal : 6*G*Psi 5 = 1 := by
  norm_num [G, Psi, potential, data, data04]

theorem g_positive : 0 < G := by norm_num [G]

#print axioms links
#print axioms psi_mono
#print axioms psi_zero
#print axioms reciprocal
#print axioms g_positive
end
end JSP233.SourceWindowData243614
