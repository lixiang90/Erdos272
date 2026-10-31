import Erdos272.Arithmetic.StepCensus208
import Erdos272.Arithmetic.PrefixAbel208

/-! Periodic owner masks and exact integer prefix-discrepancy certificates. -/
namespace JSP233.LightOwners209
open StepClass208
open scoped BigOperators
set_option maxHeartbeats 0

def FromPrime (mask p : ℕ) : Bool :=
  if p=2 then mask.testBit 0 else if p=3 then mask.testBit 1 else
    if p=5 then mask.testBit 2 else if p=7 then mask.testBit 3 else mask.testBit 4

def Selected (mask d : ℕ) : Bool := FromPrime mask (PrimeGate d)

def Count (mask n : ℕ) : ℕ :=
  ∑i∈Finset.range n,if Selected mask (i+1) then 1 else 0

noncomputable def Weight (mask i : ℕ) : ℝ := if Selected mask (i+1) then 1 else 0
noncomputable def Rho (mask : ℕ) : ℝ := (Count mask 210:ℝ)/210

def Checks (mask : ℕ) (lo hi : ℤ) : Prop :=
  ∀r∈Finset.range 210,
    lo≤210*(Count mask r:ℤ)-(Count mask 210:ℤ)*r ∧
      210*(Count mask r:ℤ)-(Count mask 210:ℤ)*r≤hi

instance (mask : ℕ) (lo hi : ℤ) : Decidable (Checks mask lo hi) :=
  inferInstanceAs (Decidable (∀r∈Finset.range 210,
    lo≤210*(Count mask r:ℤ)-(Count mask 210:ℤ)*r ∧
      210*(Count mask r:ℤ)-(Count mask 210:ℤ)*r≤hi))

theorem selected_period (mask n : ℕ) :
    Selected mask (n+1)=Selected mask (n%210+1) := by
  unfold Selected
  rw [StepCensus208.gate_period]

theorem count_zero (mask : ℕ) : Count mask 0=0 := rfl

theorem count_succ (mask n : ℕ) :
    Count mask (n+1)=Count mask n+(if Selected mask (n+1) then 1 else 0) :=
  Finset.sum_range_succ _ _

theorem count_periodic (mask n : ℕ) :
    Count mask n=n/210*Count mask 210+Count mask (n%210) := by
  induction n with
  | zero => simp only [count_zero,Nat.zero_div,Nat.zero_mul,Nat.zero_mod,Nat.add_zero]
  | succ n ih =>
    rw [count_succ,ih,selected_period mask n]
    have hr : n%210<210 := Nat.mod_lt _ (by decide)
    by_cases htop : n%210=209
    · have hq : (n+1)/210=n/210+1 := by omega
      have hm : (n+1)%210=0 := by omega
      have hc := count_succ mask 209
      rw [hq,hm,count_zero,htop]
      norm_num only [Nat.reduceAdd] at hc
      nlinarith only [hc]
    · have hq : (n+1)/210=n/210 := by omega
      have hm : (n+1)%210=n%210+1 := by omega
      rw [hq,hm,count_succ mask (n%210)]
      omega

theorem prefix_eq_count (mask n : ℕ) :
    PrefixAbel208.Prefix (Weight mask) n=(Count mask n:ℝ) := by
  unfold PrefixAbel208.Prefix Weight Count
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> norm_num

theorem weight_nonneg (mask i : ℕ) : 0≤Weight mask i := by
  unfold Weight
  split_ifs <;> norm_num

theorem rho_nonneg (mask : ℕ) : 0≤Rho mask := by unfold Rho; positivity

theorem checks_sign {mask : ℕ} {lo hi : ℤ} (h : Checks mask lo hi) :
    lo≤0 ∧ 0≤hi := by
  simpa only [count_zero,Int.natCast_zero,mul_zero,zero_sub,neg_zero] using h 0 (by simp)

theorem integer_bounds {mask : ℕ} {lo hi : ℤ} (h : Checks mask lo hi) (n : ℕ) :
    lo≤210*(Count mask n:ℤ)-(Count mask 210:ℤ)*n ∧
      210*(Count mask n:ℤ)-(Count mask 210:ℤ)*n≤hi := by
  have hr := h (n%210) (Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hc : (Count mask n:ℤ)=(n/210:ℕ)*(Count mask 210:ℤ)+(Count mask (n%210):ℤ) := by
    exact_mod_cast count_periodic mask n
  have hd : (n%210:ℕ)+210*(n/210:ℕ)=(n:ℤ) := by exact_mod_cast Nat.mod_add_div n 210
  constructor <;> nlinarith only [hr.1,hr.2,hc,hd]

theorem real_bounds {mask : ℕ} {lo hi : ℤ} (h : Checks mask lo hi) (n : ℕ) :
    Rho mask*n+(lo:ℝ)/210≤PrefixAbel208.Prefix (Weight mask) n ∧
      PrefixAbel208.Prefix (Weight mask) n≤Rho mask*n+(hi:ℝ)/210 := by
  rw [prefix_eq_count]
  have hb := integer_bounds h n
  have hl : (lo:ℝ)≤210*(Count mask n:ℝ)-(Count mask 210:ℝ)*n := by exact_mod_cast hb.1
  have hu : 210*(Count mask n:ℝ)-(Count mask 210:ℝ)*n≤(hi:ℝ) := by exact_mod_cast hb.2
  unfold Rho
  constructor <;> linarith only [hl,hu]

#print axioms count_periodic
#print axioms real_bounds
end JSP233.LightOwners209
