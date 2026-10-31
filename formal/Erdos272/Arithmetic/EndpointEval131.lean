import Erdos272.Arithmetic.Hyperbola131
import Erdos272.Arithmetic.PrefixSuper127
namespace JSP233.EndpointEval131
open SimplexMoment57 Hyperbola131
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def quotSum (N:ℕ) : ℕ→ℕ
  | 0=>0
  | m+1=>quotSum N m+N/(m+1)

def d1Eval (N:ℕ) : ℕ := 2*quotSum N (Nat.sqrt N)-(Nat.sqrt N)^2

def tauEval (N:ℕ) : ℕ := d1Eval N-d1Eval (N-1)

def zEval (N:ℕ) : ℕ→ℕ
  | 0=>0
  | m+1=>zEval N m+tauEval (m+1)*d1Eval (N/(m+1))

def d3Eval (N:ℕ) : ℕ := 2*zEval N (Nat.sqrt N)-(d1Eval (Nat.sqrt N))^2

noncomputable section
open scoped Classical

theorem quotSum_eq (N m:ℕ) : quotSum N m=∑a∈Finset.Icc 1 m,N/a := by
  induction m with
  | zero => simp [quotSum]
  | succ m ih =>
    rw [quotSum,Finset.sum_Icc_succ_top (by omega : 1≤m+1),ih]

theorem d1Eval_sound (N:ℕ) : d1Eval N=DivCount 1 N := by
  have h := actual_hyperbola_nat (Nat.sqrt_le' N) (Nat.lt_succ_sqrt' N)
  dsimp only [d1Eval]
  rw [quotSum_eq]
  omega

theorem first_moment_eq (N:ℕ) : (∑a∈Finset.Icc 1 N,a.divisors.card)=DivCount 1 N := by
  simpa only [DivCount] using PrefixSuper127.actual_first_moment_common N N le_rfl

theorem d1_successor (n:ℕ) : DivCount 1 (n+1)=DivCount 1 n+(n+1).divisors.card := by
  rw [←first_moment_eq,Finset.sum_Icc_succ_top (by omega : 1≤n+1),first_moment_eq]

theorem tauEval_sound (N:ℕ) : tauEval N=N.divisors.card := by
  cases N with
  | zero => norm_num [tauEval,d1Eval,quotSum]
  | succ n =>
    have h := d1_successor n
    dsimp only [tauEval]
    rw [d1Eval_sound,d1Eval_sound]
    simp only [Nat.add_sub_cancel] at *
    omega

theorem zEval_eq (N m:ℕ) : zEval N m=∑a∈Finset.Icc 1 m,a.divisors.card*DivCount 1 (N/a) := by
  induction m with
  | zero => simp [zEval]
  | succ m ih =>
    rw [zEval,Finset.sum_Icc_succ_top (by omega : 1≤m+1),ih,tauEval_sound,d1Eval_sound]

#print axioms quotSum_eq
#print axioms d1Eval_sound
#print axioms first_moment_eq
#print axioms d1_successor
#print axioms tauEval_sound
#print axioms zEval_eq
end
end JSP233.EndpointEval131
