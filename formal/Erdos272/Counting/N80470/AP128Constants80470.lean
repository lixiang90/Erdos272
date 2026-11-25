module

public import Erdos272.Counting.N80470.AP128Family80470

@[expose] public section

namespace JSP233.AP128Constants80470
open HarmonicAbel29 AP128Family80470
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option Elab.async false

def Coefficient (k : ℕ) : ℝ :=
  1/(4*((k : ℝ)+1))+1/(2*((k : ℝ)+1)^2)+
    ((k%2 : ℕ) : ℝ)/(4*(k : ℝ)*((k : ℝ)+1))

def Fee (k : ℕ) : ℝ := (3*(k : ℝ)+1)/4+1+((k%2 : ℕ) : ℝ)/4

def NuExact : ℝ := 1/4+∑ k∈Finset.Icc 1 128, Coefficient k

theorem square_coefficient :
    ((∑ j∈(Finset.Icc 1 64 : Finset ℕ), (1 : ℝ)/(j : ℝ)^2)+2/129-1)/4<Kappa := by
  norm_num [Kappa, Finset.sum_Icc_succ_top]

theorem nu_coefficient : Nu<NuExact := by
  norm_num [Nu, NuExact, Coefficient, Finset.sum_Icc_succ_top]

#print axioms square_coefficient
#print axioms nu_coefficient
end
end JSP233.AP128Constants80470
