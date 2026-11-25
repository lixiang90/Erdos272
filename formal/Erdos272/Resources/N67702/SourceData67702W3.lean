module

public import Erdos272.Arithmetic.N67702.RowGeometry67702
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section

namespace JSP233.SourceData67702W3
open CleanupRows67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Witness : ℕ := 82

def potential (n : ℕ) : ℕ :=
  if n=0 then 0 else if n=1 then 1886 else (data (64+min (n-2) 31)).potential
def Psi (n : ℕ) : ℝ := potential n
def G : ℝ := 1/282534
def CoeffA : ℝ := 3736839225199/192200000000000
def CoeffB : ℝ := 15267352651988060861/164811500000000000
def CoeffC : ℝ := 12791826120393/47089
def SourceUpper (N : ℕ) : ℝ := CoeffA*(N : ℝ)^2+CoeffB*N+CoeffC

theorem links {i : ℕ} (hi : i < 32) :
    (data (64+i)).row.low = 69458 ∧ (data (64+i)).row.high = 71236 ∧
    (data (64+i)).memberFloor = 80 ∧ potential (i+2) = (data (64+i)).potential := by
  interval_cases i <;> decide +kernel

theorem psi_mono : Monotone Psi := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 33
  · have hh : potential n ≤ potential (n+1) := by interval_cases n <;> decide +kernel
    dsimp only [Psi]
    exact_mod_cast hh
  · have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    have h2 : n+1 ≠ 0 := by omega
    have h3 : n+1 ≠ 1 := by omega
    have hm0 : min (n-2) 31 = 31 := by omega
    have hm1 : min (n+1-2) 31 = 31 := by omega
    simp only [Psi, potential, if_neg h0, if_neg h1, if_neg h2, if_neg h3, hm0, hm1, le_refl]

theorem psi_zero : Psi 0 = 0 := by simp [Psi, potential]
theorem reciprocal : 6*G*Psi 33 = 1 := by norm_num [G, Psi, potential, data, data95]
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
end JSP233.SourceData67702W3
