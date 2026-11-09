module

public import Erdos272.Resources.TotientRows208
public import Mathlib.NumberTheory.Divisors
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.TotientCovariance212
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- The finite convolution is exact, including c=0. No analytic totient
estimate or common global frontier height is assumed. -/
theorem mass_convolution (c : ℕ) :
    (∑d∈Finset.Icc 1 c,TotientRows208.TotientMass (c/d)/(d : ℝ))=(c : ℝ) := by
  have h := TotientFloor29.divisor_sum_prefix c
    (fun d k => (Nat.totient k : ℝ)/((d : ℝ)*(k : ℝ)))
  have hl : (∑n∈Finset.Icc 1 c,∑d∈n.divisors,
      (Nat.totient (n/d) : ℝ)/((d : ℝ)*(n/d : ℕ)))=(c : ℝ) := by
    have hr : ∀n∈Finset.Icc 1 c,(∑d∈n.divisors,
        (Nat.totient (n/d) : ℝ)/((d : ℝ)*(n/d : ℕ)))=1 := by
      intro n hn
      have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by have hh:=Finset.mem_Icc.mp hn;omega)
      have he : ∀d∈n.divisors,(d : ℝ)*(n/d : ℕ)=(n : ℝ) := by
        intro d hd
        exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hsum : (∑d∈n.divisors,
          (Nat.totient (n/d) : ℝ)/((d : ℝ)*(n/d : ℕ)))=
          ∑d∈n.divisors,(Nat.totient (n/d) : ℝ)/(n : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [he d hd]
      have hs' : (∑d∈n.divisors,(Nat.totient (n/d) : ℝ))=
          ∑d∈n.divisors,(Nat.totient d : ℝ) :=
        Nat.sum_div_divisors n (fun j : ℕ=>(Nat.totient j : ℝ))
      rw [hsum,←Finset.sum_div,hs']
      have hs : (∑d∈n.divisors,(Nat.totient d : ℝ))=(n : ℝ) := by
        exact_mod_cast Nat.sum_totient n
      rw [hs,div_self hn0]
    rw [Finset.sum_congr rfl hr]
    simp
  have hr : (∑d∈Finset.Icc 1 c,∑k∈Finset.Icc 1 (c/d),
      (Nat.totient k : ℝ)/((d : ℝ)*(k : ℝ)))=
      ∑d∈Finset.Icc 1 c,TotientRows208.TotientMass (c/d)/(d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [TotientRows208.TotientMass,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [div_div,mul_comm]
  exact hr.symm.trans (h.symm.trans hl)

/-- Each frontier height is independent: a single row is completed to a
square before any summation, retaining its actual C and totient mass. -/
theorem row_unconstrained {rho C A e f err P U : ℝ} (hrho : 0<rho)
    (hP : e*f-err≤P) (hU : rho*e^2/2-(61/200 : ℝ)*e≤U) :
    C*e-C*A-P-U≤-C*A+(C-f+61/200)^2/(2*rho)+err := by
  have he : C*e-C*A-(e*f-err)-(rho*e^2/2-(61/200 : ℝ)*e)=
      -C*A+(C-f+61/200)^2/(2*rho)+err-
        rho/2*(e-(C-f+61/200)/rho)^2 := by
    field_simp
    ring
  have hs : 0≤rho/2*(e-(C-f+61/200)/rho)^2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith only [hP,hU,he,hs]

#print axioms mass_convolution
#print axioms row_unconstrained
end
end JSP233.TotientCovariance212
