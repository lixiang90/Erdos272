module

public import Erdos272.Arithmetic.N82427.ClassFastNumeric82427
public import Erdos272.Counting.N158375.ClassCountConcat158375

@[expose] public section

namespace JSP233.ClassFastCore82427
open ClassFastNumeric82427 ClassCount158375
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem gate_eq (d : ℕ) : Gate d=StepClass208.PrimeGate d := by
  simp only [Gate, StepClass208.PrimeGate, Nat.dvd_iff_mod_eq_zero]

theorem prefix_correct {p : ℕ} (hf : PrefixFacts p) {t : ℕ} (ht : t≤210) :
    Prefix p t=StepCensus208.Count p t := by
  induction t with
  | zero => simpa only [StepCensus208.count_zero] using hf.1
  | succ t ih =>
      have hsmall : t<210 := by omega
      have hs := List.all_eq_true.mp hf.2 t (List.mem_range.mpr hsmall)
      have hstep : Prefix p (t+1)=Prefix p t+(if Gate (t+1)=p then 1 else 0) :=
        of_decide_eq_true hs
      rw [hstep, ih (by omega), gate_eq, StepCensus208.count_succ]

theorem count_eq_window (p t : ℕ) :
    StepCensus208.Count p t=WindowCount p 0 t := by
  simp only [StepCensus208.Count, WindowCount, Nat.zero_add]

theorem window_difference (p a n : ℕ) :
    WindowCount p a n=StepCensus208.Count p (a+n)-StepCensus208.Count p a := by
  have hh := ClassCountConcat158375.window_count_add p 0 a n
  rw [←count_eq_window, ←count_eq_window] at hh
  simp only [Nat.zero_add] at hh
  omega

theorem eval_correct {p r n : ℕ} (hf : PrefixFacts p) (hr : r<210) :
    eval p r n=WindowCount p r n := by
  unfold eval
  rw [prefix_correct hf (by omega : 210≤210),
    prefix_correct hf (Nat.le_of_lt (Nat.mod_lt (r+n) (by decide))),
    prefix_correct hf hr.le, ←StepCensus208.count_periodic, window_difference]

theorem sound {p n b : ℕ} (hf : PrefixFacts p) (hc : check p n b=true) :
    Certificate p n b := by
  intro r hr
  have hsmall := Finset.mem_range.mp hr
  have hh := of_decide_eq_true (List.all_eq_true.mp hc r (List.mem_range.mpr hsmall))
  rw [eval_correct hf hsmall] at hh
  exact hh

#print axioms gate_eq
#print axioms prefix_correct
#print axioms count_eq_window
#print axioms window_difference
#print axioms eval_correct
#print axioms sound
end JSP233.ClassFastCore82427
