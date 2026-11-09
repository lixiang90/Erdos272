module

public import Erdos272.Arithmetic.StepClass208
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.StepCensus208
open StepClass208
open scoped BigOperators
set_option maxHeartbeats 0
set_option Elab.async false

def Count (p n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if PrimeGate (i+1)=p then 1 else 0

def PeriodMass (p : ℕ) : ℕ := match p with
  | 2 => 105 | 3 => 35 | 5 => 14 | 7 => 8 | 11 => 48 | _ => 0

def PeriodError (p : ℕ) : ℕ := match p with
  | 2 => 0 | 3 => 105 | 5 => 140 | 7 => 196 | 11 => 318 | _ => 0

noncomputable def Rho (p : ℕ) : ℝ := (PeriodMass p : ℝ)/210
noncomputable def Error (p : ℕ) : ℝ := (PeriodError p : ℝ)/210

theorem gate_period (n : ℕ) : PrimeGate (n+1)=PrimeGate (n%210+1) := by
  unfold PrimeGate
  split_ifs <;> omega

theorem count_zero (p : ℕ) : Count p 0=0 := rfl

theorem count_succ (p n : ℕ) :
    Count p (n+1)=Count p n+(if PrimeGate (n+1)=p then 1 else 0) :=
  Finset.sum_range_succ _ _

theorem count_periodic (p n : ℕ) : Count p n=n/210*Count p 210+Count p (n%210) := by
  induction n with
  | zero => simp only [count_zero,Nat.zero_div,Nat.zero_mul,Nat.zero_mod,Nat.add_zero]
  | succ n ih =>
    rw [count_succ,ih,gate_period n]
    have hr : n%210 < 210 := Nat.mod_lt _ (by decide)
    by_cases htop : n%210=209
    · have hq : (n+1)/210=n/210+1 := by omega
      have hm : (n+1)%210=0 := by omega
      have hc := count_succ p 209
      rw [hq,hm,count_zero,htop]
      norm_num only [Nat.reduceAdd] at hc
      nlinarith only [hc]
    · have hq : (n+1)/210=n/210 := by omega
      have hm : (n+1)%210=n%210+1 := by omega
      rw [hq,hm,count_succ p (n%210)]
      omega

private def countFast (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => countFast p n+(if PrimeGate (n+1)=p then 1 else 0)

private theorem countFast_eq (p n : ℕ) : countFast p n=Count p n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [countFast, ih, count_succ]

private theorem fast_period_checks : ∀ p ∈ ({2,3,5,7,11} : Finset ℕ),
    countFast p 210=PeriodMass p ∧
      ∀ r ∈ Finset.range 210, 210*countFast p r ≤ PeriodMass p*r+PeriodError p := by
  decide +kernel

theorem period_checks : ∀ p ∈ ({2,3,5,7,11} : Finset ℕ),
    Count p 210=PeriodMass p ∧
      ∀ r ∈ Finset.range 210, 210*Count p r ≤ PeriodMass p*r+PeriodError p := by
  simpa only [countFast_eq] using fast_period_checks

theorem count_upper (p n : ℕ) (hp : p ∈ ({2,3,5,7,11} : Finset ℕ)) :
    (Count p n : ℝ) ≤ Rho p*n+Error p := by
  obtain ⟨hc,hprefix⟩ := period_checks p hp
  have hr := hprefix (n%210) (Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hdecomp := count_periodic p n
  rw [hc] at hdecomp
  have hdiv := Nat.mod_add_div n 210
  have hnat : 210*Count p n ≤ PeriodMass p*n+PeriodError p := by
    nlinarith only [hr,hdecomp,hdiv]
  have hR : 210*(Count p n : ℝ) ≤ (PeriodMass p : ℝ)*n+PeriodError p := by exact_mod_cast hnat
  unfold Rho Error
  linarith only [hR]

theorem shifted_sum (f : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f (i+1))=∑ d ∈ Finset.Icc 1 n, f d := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]

theorem count_eq_card (p n : ℕ) :
    Count p n=((Finset.Icc 1 n).filter (fun d => PrimeGate d=p)).card := by
  unfold Count
  rw [shifted_sum (fun d => if PrimeGate d=p then 1 else 0) n,← Finset.sum_filter]
  simp

theorem real_count_upper (p : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hp : p ∈ ({2,3,5,7,11} : Finset ℕ)) :
    (Count p ⌊y⌋₊ : ℝ) ≤ Rho p*y+Error p := by
  have hn := count_upper p ⌊y⌋₊ hp
  have hf := Nat.floor_le hy
  have hmul := mul_le_mul_of_nonneg_left hf
    (show 0 ≤ Rho p by unfold Rho; positivity)
  linarith only [hn,hmul]

theorem period_error_sum :
    2*(∑ p ∈ ({2,3,5,7,11} : Finset ℕ), Error p) = (253/35 : ℝ) := by
  norm_num [Error,PeriodError]

#print axioms gate_period
#print axioms count_periodic
#print axioms period_checks
#print axioms count_upper
#print axioms real_count_upper
#print axioms period_error_sum
end JSP233.StepCensus208
