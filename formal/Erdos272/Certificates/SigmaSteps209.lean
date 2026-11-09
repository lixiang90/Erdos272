module

public import Erdos272.Arithmetic.ComputedSigma209
public import Erdos272.Arithmetic.FastFullLookup209

@[expose] public section

namespace JSP233.SigmaSteps209
set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked_of_steps {a factor : Nat → Nat} {lo len : Nat}
    (h : ∀ n, lo ≤ n → n < lo+len → SigmaSieve209.Step a factor n) :
    ComputedSigma209.checkSteps a factor lo len = true := by
  revert h
  induction len with
  | zero =>
    intro _
    rfl
  | succ len ih =>
    intro h
    have hs := h (lo+len) (by omega) (by omega)
    have ht := ih (fun n hnlo hnhi => h n hnlo (by omega))
    simpa only [ComputedSigma209.checkSteps, ForcedCheck209.withNat_eq,
      Bool.and_eq_true_iff, decide_eq_true_eq] using And.intro hs ht

theorem checked_append {a factor : Nat → Nat} {lo k l : Nat}
    (hk : ComputedSigma209.checkSteps a factor lo k = true)
    (hl : ComputedSigma209.checkSteps a factor (lo+k) l = true) :
    ComputedSigma209.checkSteps a factor lo (k+l) = true := by
  apply checked_of_steps
  intro n hnlo hnhi
  by_cases hn : n < lo+k
  · exact ComputedSigma209.checkSteps_sound hk hnlo hn
  · exact ComputedSigma209.checkSteps_sound hl (by omega) (by omega)

theorem fast_factor_checked {a : Nat → Nat} {lo len : Nat}
    (h : ComputedSigma209.checkSteps a FastFullLookup209.factor lo len = true) :
    ComputedSigma209.checkSteps a FactorFullData209.factor lo len = true := by
  have he : FastFullLookup209.factor = FactorFullData209.factor :=
    funext (fun n => FastFullLookup209.factor_eq n)
  simpa only [he] using h

#print axioms checked_append
#print axioms fast_factor_checked
end JSP233.SigmaSteps209
