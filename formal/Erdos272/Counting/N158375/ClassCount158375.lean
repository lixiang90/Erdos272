module

public import Erdos272.Arithmetic.StepCensus208
public import Erdos272.Foundation.ProofTactics

@[expose] public section

namespace JSP233.ClassCount158375
open StepClass208
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def WindowCount (p a n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if PrimeGate (a+j+1)=p then 1 else 0

def Certificate (p n b : ℕ) : Prop :=
  ∀ r ∈ Finset.range 210, b ≤ WindowCount p r n

instance (p n b : ℕ) : Decidable (Certificate p n b) :=
  inferInstanceAs (Decidable (∀ r ∈ Finset.range 210, b ≤ WindowCount p r n))

def Steps (N q p : ℕ) : Finset ℕ :=
  (Finset.Icc (N/(q+1)+1) (N/q)).filter (fun d => PrimeGate d=p)

theorem window_count_period (p a n : ℕ) :
    WindowCount p a n = WindowCount p (a%210) n := by
  unfold WindowCount
  apply Finset.sum_congr rfl
  intro j hj
  have hmod : (a+j)%210 = (a%210+j)%210 := by omega
  have hg : PrimeGate (a+j+1) = PrimeGate (a%210+j+1) := by
    calc
      _ = PrimeGate ((a+j)%210+1) := StepCensus208.gate_period (a+j)
      _ = PrimeGate ((a%210+j)%210+1) := by rw [hmod]
      _ = _ := (StepCensus208.gate_period (a%210+j)).symm
  rw [hg]

theorem certificate_lower {p n b : ℕ} (h : Certificate p n b) (a : ℕ) :
    b ≤ WindowCount p a n := by
  rw [window_count_period]
  exact h (a%210) (Finset.mem_range.mpr (Nat.mod_lt a (by decide)))

theorem window_count_mono (p a : ℕ) : Monotone (WindowCount p a) := by
  intro n m hnm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
    (fun _ _ _ => Nat.zero_le _)

theorem certificate_mono {p n m b c : ℕ} (hnm : n ≤ m) (hcb : c ≤ b)
    (h : Certificate p n b) : Certificate p m c := by
  intro r hr
  exact hcb.trans ((h r hr).trans (window_count_mono p r hnm))

theorem shifted_sum (f : ℕ → ℕ) (a n : ℕ) :
    (∑ j ∈ Finset.range n, f (a+j+1)) = ∑ d ∈ Finset.Icc (a+1) (a+n), f d := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, show a+(n+1) = a+n+1 by omega,
        Finset.sum_Icc_succ_top (by omega), ih]

theorem window_count_eq_card (p a n : ℕ) :
    WindowCount p a n =
      ((Finset.Icc (a+1) (a+n)).filter (fun d => PrimeGate d=p)).card := by
  unfold WindowCount
  rw [shifted_sum (fun d => if PrimeGate d=p then 1 else 0) a n,
    ← Finset.sum_filter]
  simp

theorem physical_interval_length {N low q : ℕ} (hq : 0 < q) (hlo : low ≤ N) :
    N/(q+1)+low/(q*(q+1)) ≤ N/q := by
  have hfirst := Nat.div_mul_le_self low (q*(q+1))
  have hnq : low/(q*(q+1))*q ≤ N/(q+1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < q+1)).mpr
    nlinarith only [hfirst, hlo]
  have hsecond := Nat.div_mul_le_self N (q+1)
  apply (Nat.le_div_iff_mul_le hq).mpr
  nlinarith only [hnq, hsecond]

theorem physical_interval_count {N low q p b : ℕ} (hq : 0 < q) (hlo : low ≤ N)
    (h : Certificate p (low/(q*(q+1))) b) : b ≤ (Steps N q p).card := by
  have hb := certificate_lower h (N/(q+1))
  rw [window_count_eq_card] at hb
  have hlength := physical_interval_length hq hlo
  apply hb.trans (Finset.card_le_card ?_)
  intro d hd
  obtain ⟨hd, hgate⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans hlength⟩, hgate⟩

theorem mem_steps {N q p d : ℕ} (hq : 0 < q) (hd : d ∈ Steps N q p) :
    0 < d ∧ N/d=q ∧ PrimeGate d=p := by
  obtain ⟨hd, hgate⟩ := Finset.mem_filter.mp hd
  obtain ⟨hleft, hright⟩ := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := (Nat.succ_pos _).trans_le hleft
  have hmul : d*q ≤ N := (Nat.le_div_iff_mul_le hq).mp hright
  have htop : N < d*(q+1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < q+1)).mp (by omega)
  refine ⟨hdpos, ?_, hgate⟩
  apply Nat.le_antisymm
  · have h : N/d < q+1 :=
      (Nat.div_lt_iff_lt_mul hdpos).mpr (by nlinarith only [htop])
    omega
  · exact (Nat.le_div_iff_mul_le hdpos).mpr (by nlinarith only [hmul])

#print axioms window_count_period
#print axioms certificate_lower
#print axioms window_count_mono
#print axioms certificate_mono
#print axioms shifted_sum
#print axioms window_count_eq_card
#print axioms physical_interval_length
#print axioms physical_interval_count
#print axioms mem_steps
end JSP233.ClassCount158375
