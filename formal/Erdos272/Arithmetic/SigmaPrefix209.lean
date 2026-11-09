module

public import Erdos272.Arithmetic.SigmaSieve209
public import Erdos272.Arithmetic.ForcedCheck209
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace JSP233.SigmaPrefix209
set_option maxHeartbeats 0
open Finset

/-- Inclusive divisor-sum prefix. -/
def mass (a : Nat→Nat) : Nat→Nat
  | 0 => a 0
  | n+1 => mass a n+a (n+1)

/-- First discrete integral; all terms are finite natural counts. -/
def weighted (a : Nat→Nat) : Nat→Nat
  | 0 => 0
  | n+1 => weighted a n+mass a n

theorem mass_eq_sum (a : Nat→Nat) (n : Nat) : mass a n=∑ m∈range (n+1),a m := by
  induction n with
  | zero => simp [mass]
  | succ n ih => rw [mass,ih,Finset.sum_range_succ a (n+1)]

theorem weighted_eq_sum (a : Nat→Nat) (n : Nat) :
    weighted a n=∑ m∈range n,(n-m)*a m := by
  induction n with
  | zero => simp [weighted]
  | succ n ih =>
    rw [weighted,ih,mass_eq_sum,Finset.sum_range_succ,Finset.sum_range_succ]
    have heq : (∑ m∈range n,(n+1-m)*a m) =
        (∑ m∈range n,(n-m)*a m)+(∑ m∈range n,a m) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      have hm' := Finset.mem_range.mp hm
      rw [show n+1-m=(n-m)+1 by omega]
      ring
    rw [heq]
    simp [Nat.add_assoc]

/-- Cleared denominator form of the cubic envelope. -/
def Good (s w : Nat) : Prop :=
  6000000000*w+1500000000*s^2≤1644934067*s^3+16800000000*s
instance (s w : Nat) : Decidable (Good s w) := by unfold Good;infer_instance

/-- Independent block states certify every row and both endpoint accumulators. -/
def checkFrom (a : Nat→Nat) : Nat→Nat→Nat→Nat→Nat→Nat→Bool
  | _,0,d,w,dEnd,wEnd => decide (d=dEnd ∧ w=wEnd)
  | n,k+1,d,w,dEnd,wEnd =>
    ForcedCheck209.withNat (n+1) (fun t =>
    ForcedCheck209.withNat (a t) (fun aval =>
    ForcedCheck209.withNat (d+aval) (fun d' =>
    ForcedCheck209.withNat (w+d) (fun w' =>
      decide (31≤t → Good t w') && checkFrom a t k d' w' dEnd wEnd))))

theorem checkFrom_sound (a : Nat→Nat) (k n d w dEnd wEnd : Nat)
    (hd : d=mass a n) (hw : w=weighted a n)
    (hc : checkFrom a n k d w dEnd wEnd=true) :
    (dEnd=mass a (n+k) ∧ wEnd=weighted a (n+k)) ∧
    ∀ t, n<t → t≤n+k → 31≤t → Good t (weighted a t) := by
  induction k generalizing n d w with
  | zero =>
    have he : d=dEnd ∧ w=wEnd := of_decide_eq_true hc
    constructor
    · simpa only [Nat.add_zero] using ⟨he.1.symm.trans hd,he.2.symm.trans hw⟩
    · intro t ht ht';omega
  | succ k ih =>
    have hp : (31≤n+1 → Good (n+1) (w+d)) ∧
        checkFrom a (n+1) k (d+a (n+1)) (w+d) dEnd wEnd=true := by
      simpa only [checkFrom,ForcedCheck209.withNat_eq,Bool.and_eq_true_iff,decide_eq_true_eq] using hc
    have hd' : d+a (n+1)=mass a (n+1) := by rw [hd];rfl
    have hw' : w+d=weighted a (n+1) := by rw [hw,hd];rfl
    have hh := ih (n+1) _ _ hd' hw' hp.2
    constructor
    · simpa only [show n+1+k=n+(k+1) by omega] using hh.1
    · intro t hnt hthi ht31
      by_cases ht : t=n+1
      · subst t;simpa only [hw'] using hp.1 ht31
      · exact hh.2 t (by omega) (by omega) ht31

theorem weighted_congr {a b : Nat→Nat} {s : Nat}
    (ha : ∀ n, n≤s → a n=b n) : weighted a s=weighted b s := by
  rw [weighted_eq_sum,weighted_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ha n (by have h:=Finset.mem_range.mp hn;omega)]

def W (s : Nat) : Nat := weighted SigmaSieve209.sigmaOne s

theorem W_eq_sum (s : Nat) :
    W s=∑ n∈range s,(s-n)*SigmaSieve209.sigmaOne n := weighted_eq_sum _ _

theorem actual_bound {a : Nat→Nat} {s : Nat}
    (ha : ∀ n,n≤s → a n=SigmaSieve209.sigmaOne n)
    (hg : Good s (weighted a s)) :
    (W s : Real)≤(1644934067/1000000000 : Real)*(s:Real)^3/6-
      (s:Real)^2/4+(14/5:Real)*s := by
  rw [weighted_congr ha] at hg
  have hh : (6000000000:Real)*W s+1500000000*(s:Real)^2≤
      1644934067*(s:Real)^3+16800000000*s := by exact_mod_cast hg
  nlinarith only [hh]

#print axioms weighted_eq_sum
#print axioms checkFrom_sound
#print axioms actual_bound
end JSP233.SigmaPrefix209



