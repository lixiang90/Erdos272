module

public import Erdos272.Arithmetic.SevenPrices208

@[expose] public section

namespace JSP233.HybridPrices209
open SevenPrices208 ReciprocalPrice208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def K (j : ℕ) : ℕ := 242*2^j/3
def Levels (j : ℕ) : ℕ := 12-j

def RootTwo (n : ℝ) : ℝ :=
  Price (APCoupling208.Kappa*G242) U242 (Eta242+968+Loss) (-Light242) n

def High (j : ℕ) (n : ℝ) : ℝ :=
  Price (2/((K j : ℝ)*((5*K j/3 : ℕ) : ℝ)^2))
    (2303/(200*(K j : ℝ))+(if j≤6 then 0 else Beta))
    ((7/2 : ℝ)*(Levels j : ℝ)*(141/10)+Loss+(if j≤6 then 2*(2^j : ℕ)*242 else 0)) 0 n

theorem root_two_window {n : ℝ} (hl : 659912≤n) (hu : n≤705097) : RootTwo n≤Budget := by
  unfold RootTwo
  apply window (by norm_num) hl hu
  all_goals norm_num [Price,Budget,Loss,APCoupling208.Kappa,G242,U242,Eta242,Light242]

theorem high_window {n : ℝ} (j : ℕ) (hj : 2≤j) (hjhi : j≤8)
    (hl : 659912≤n) (hu : n≤705097) : High j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hu
  all_goals norm_num [Price,K,Levels,Budget,Loss,Beta]

theorem level_cutoff (j : ℕ) (hj : 2≤j) (hjhi : j≤8) :
    705097<3*K j*2^(Levels j) := by
  interval_cases j <;> norm_num [K,Levels]

theorem minimum_size (j : ℕ) (hj : 2≤j) (hjhi : j≤8) :
    0<K j ∧ 3*K j≤242*2^j ∧ 1≤5*K j/3 := by
  interval_cases j <;> norm_num [K]

#print axioms root_two_window
#print axioms high_window
#print axioms level_cutoff
#print axioms minimum_size
end
end JSP233.HybridPrices209
