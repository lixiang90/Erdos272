module

public import Erdos272.Arithmetic.N200000.RowGeometry200000
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section

namespace JSP233.SourceData200000W2
open CleanupRows200000
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def potential (n : ℕ) : ℕ :=
  if n=0 then 0 else if n=1 then 3700 else (data (14+min (n-2) 6)).potential
def Psi (n : ℕ) : ℝ := potential n
def G : ℝ := 1/1160784
def CoeffA : ℝ := 119022611535357/10748000000000000
def CoeffB : ℝ := 17792881050090068777/56427000000000000
def CoeffC : ℝ := 24053732593498/8061
def SourceUpper (N : ℕ) : ℝ := CoeffA*(N : ℝ)^2+CoeffB*N+CoeffC

theorem links {i : ℕ} (hi : i < 7) :
    (data (14+i)).row.low = 220001 ∧ (data (14+i)).row.high = 233810 ∧
    (data (14+i)).memberFloor = 140 ∧ potential (i+2) = (data (14+i)).potential := by
  interval_cases i <;> decide +kernel

theorem psi_mono : Monotone Psi := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 8
  · have hh : potential n ≤ potential (n+1) := by interval_cases n <;> decide +kernel
    dsimp only [Psi]
    exact_mod_cast hh
  · have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    have h2 : n+1 ≠ 0 := by omega
    have h3 : n+1 ≠ 1 := by omega
    have hm0 : min (n-2) 6 = 6 := by omega
    have hm1 : min (n+1-2) 6 = 6 := by omega
    simp only [Psi, potential, if_neg h0, if_neg h1, if_neg h2, if_neg h3, hm0, hm1, le_refl]

theorem psi_zero : Psi 0 = 0 := by simp [Psi, potential]
theorem reciprocal : 6*G*Psi 8 = 1 := by norm_num [G, Psi, potential, data, data20]
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
end JSP233.SourceData200000W2
