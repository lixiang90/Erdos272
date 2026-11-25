module

public import Erdos272.Arithmetic.N80470.RowGeometry80470
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section

namespace JSP233.SourceData80470W1
open CleanupRows80470
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Witness : ℕ := 86

def potential (n : ℕ) : ℕ :=
  if n=0 then 0 else if n=1 then 2186 else (data (4+min (n-2) 3)).potential
def Psi (n : ℕ) : ℝ := potential n
def G : ℝ := 1/327132
def CoeffA : ℝ := 98809351767779/5452200000000000
def CoeffB : ℝ := 2466549628005013319/23853375000000000
def CoeffC : ℝ := 3260659215121/9087
def SourceUpper (N : ℕ) : ℝ := CoeffA*(N : ℝ)^2+CoeffB*N+CoeffC

theorem links {i : ℕ} (hi : i < 4) :
    (data (4+i)).row.low = 80470 ∧ (data (4+i)).row.high = 82425 ∧
    (data (4+i)).memberFloor = 86 ∧ potential (i+2) = (data (4+i)).potential := by
  interval_cases i <;> decide +kernel

theorem psi_mono : Monotone Psi := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 5
  · have hh : potential n ≤ potential (n+1) := by interval_cases n <;> decide +kernel
    dsimp only [Psi]
    exact_mod_cast hh
  · have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    have h2 : n+1 ≠ 0 := by omega
    have h3 : n+1 ≠ 1 := by omega
    have hm0 : min (n-2) 3 = 3 := by omega
    have hm1 : min (n+1-2) 3 = 3 := by omega
    simp only [Psi, potential, if_neg h0, if_neg h1, if_neg h2, if_neg h3, hm0, hm1, le_refl]

theorem psi_zero : Psi 0 = 0 := by simp [Psi, potential]
theorem reciprocal : 6*G*Psi 5 = 1 := by norm_num [G, Psi, potential, data, data07]
theorem g_positive : 0 < G := by norm_num [G]

theorem upper_mono {N H : ℕ} (h : N ≤ H) : SourceUpper N ≤ SourceUpper H := by
  have hn : (N : ℝ) ≤ H := by exact_mod_cast h
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) N) hn 2
  have ha := mul_le_mul_of_nonneg_left hs (by norm_num [CoeffA] : 0 ≤ CoeffA)
  have hb := mul_le_mul_of_nonneg_left hn (by norm_num [CoeffB] : 0 ≤ CoeffB)
  unfold SourceUpper
  linarith only [ha, hb]

#print axioms links
#print axioms psi_mono
#print axioms psi_zero
#print axioms reciprocal
#print axioms g_positive
#print axioms upper_mono
end
end JSP233.SourceData80470W1
